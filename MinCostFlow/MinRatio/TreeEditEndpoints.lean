module

public import MinCostFlow.MinRatio.TreeEditLayout
public import MinCostFlow.MinRatio.GraphRead
public import MinCostFlow.MinRatio.PathTreeContract

/-!
# Resolving endpoints of a tree-change record

The tree changes of Lemma 5.11 (page 20) identify edges by name.
Resolve their endpoints through the shared dynamic graph's slot and
inverse-name tables before applying the link-cut updates.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM DynSpanner.Program

/-- The graph words needed to resolve one live edge, with the slot
and name bounds supplied by the shared dynamic graph layout. -/
structure TreeEditEndpointAt (mem : ℕ → ℕ) (base vc ec : ℕ) (G : MGraph) (e : ℕ) : Prop where
  edgeBound : e < ec
  tailSlotBound : mem (dgETailSlotBase base vc ec + e) < vc
  headSlotBound : mem (dgEHeadSlotBase base vc ec + e) < vc
  tailNameBound : G.tail e < vc
  headNameBound : G.head e < vc
  tailName : mem (dgIntToExtBase base vc + mem (dgETailSlotBase base vc ec + e)) = G.tail e
  headName : mem (dgIntToExtBase base vc + mem (dgEHeadSlotBase base vc ec + e)) = G.head e

/-- The full graph layout supplies the endpoint lookup for every live edge. -/
theorem TreeEditEndpointAt.of_graph {mem : ℕ → ℕ} {base vc ec e : ℕ} {G : MGraph}
    (hG : DynGraphAt mem base vc ec G) (he : e ∈ G.E) :
    TreeEditEndpointAt mem base vc ec G e := by
  have hend := readNamedGraph_endpoints hG he
  obtain ⟨hvalid, hv, hedge, _, _, _, _, _, _, hind, _, hpres, _, hslots, _⟩ := hG
  have hb : mem (dgEPresBase base vc + e) = 1 := by simp [hpres e (hedge e he), he]
  simp only [readNamedGraph, hb, hedge e he, and_self, ite_true] at hend
  exact ⟨hedge e he, by rw [(hslots e he).1]; exact hv _ (hind _ (hvalid e he).1).1,
    by rw [(hslots e he).2]; exact hv _ (hind _ (hvalid e he).2).1,
    hv _ (hvalid e he).1, hv _ (hvalid e he).2, hend.1, hend.2⟩

/-- Agreement on the two slot words and their inverse-table entries
preserves the endpoint lookup. -/
theorem TreeEditEndpointAt.congr {mem mem' : ℕ → ℕ} {base vc ec e : ℕ} {G : MGraph}
    (he : TreeEditEndpointAt mem base vc ec G e)
    (ht : mem' (dgETailSlotBase base vc ec + e) = mem (dgETailSlotBase base vc ec + e))
    (hh : mem' (dgEHeadSlotBase base vc ec + e) = mem (dgEHeadSlotBase base vc ec + e))
    (hi : ∀ v < vc, mem' (dgIntToExtBase base vc + v) = mem (dgIntToExtBase base vc + v)) :
    TreeEditEndpointAt mem' base vc ec G e := by
  refine ⟨he.edgeBound, ht.symm ▸ he.tailSlotBound, hh.symm ▸ he.headSlotBound,
    he.tailNameBound, he.headNameBound, ?_, ?_⟩
  · rw [ht, hi _ he.tailSlotBound]
    exact he.tailName
  · rw [hh, hi _ he.headSlotBound]
    exact he.headName

/-- A frame for the graph allocation preserves the endpoint lookup. -/
theorem TreeEditEndpointAt.congr_region {mem mem' : ℕ → ℕ} {base vc ec e : ℕ} {G : MGraph}
    (he : TreeEditEndpointAt mem base vc ec G e)
    (hframe : ∀ a, base ≤ a → a < base + dynGraphSize vc ec → mem' a = mem a) :
    TreeEditEndpointAt mem' base vc ec G e := by
  have hcap := he.edgeBound
  apply he.congr
  · apply hframe <;> simp only [dgETailSlotBase, dynGraphSize] <;> omega
  · apply hframe <;> simp only [dgEHeadSlotBase, dynGraphSize] <;> omega
  · intro v hv
    apply hframe <;> simp only [dgIntToExtBase, dynGraphSize] <;> omega

/-- Registers 9 and 10 are the two endpoint-slot table bases and
register 11 is the inverse vertex-name base. Register 8 holds the edge. -/
@[expose] def treeEditEndpoints : Stmt :=
  .assign 1 (.load (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 8))))) ;;
  .assign 2 (.load (.bin .add (.reg 11) (.load (.bin .add (.reg 10) (.reg 8)))))

/-- Resolve both endpoint names in 17 steps from either the old graph
for a deletion or the new graph for an insertion. -/
theorem treeEditEndpoints_runs {w base vc ec e : ℕ} {G : MGraph}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (he : TreeEditEndpointAt st.mem base vc ec G e)
    (hroom : base + dynGraphSize vc ec ≤ 2 ^ w)
    (h8 : st.regs 8 = e) (h9 : st.regs 9 = dgETailSlotBase base vc ec)
    (h10 : st.regs 10 = dgEHeadSlotBase base vc ec)
    (h11 : st.regs 11 = dgIntToExtBase base vc) :
    ∃ out, Runs w p ω treeEditEndpoints st .normal out 17 ∧
      out.regs 1 = G.tail e ∧ out.regs 2 = G.head e ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 1 → r ≠ 2 → out.regs r = st.regs r) := by
  obtain ⟨hcap, hvTail, hvHead, _, _, htail, hhead⟩ := he
  have ht : dgETailSlotBase base vc ec + e < 2 ^ w := by
    unfold dgETailSlotBase dynGraphSize at *
    omega
  have hh : dgEHeadSlotBase base vc ec + e < 2 ^ w := by
    unfold dgEHeadSlotBase dynGraphSize at *
    omega
  have ht' : dgIntToExtBase base vc + st.mem (dgETailSlotBase base vc ec + e) < 2 ^ w := by
    unfold dgIntToExtBase dynGraphSize at *
    omega
  have hh' : dgIntToExtBase base vc + st.mem (dgEHeadSlotBase base vc ec + e) < 2 ^ w := by
    unfold dgIntToExtBase dynGraphSize at *
    omega
  let mid := { st with regs := Function.update st.regs 1 (G.tail e) }
  let out := { mid with regs := Function.update mid.regs 2 (G.head e) }
  have hr₁ : Runs w p ω
      (.assign 1 (.load (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 8))))))
        st .normal mid 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, h8, h9, h11, ht, ht', htail], rfl, rfl, rfl⟩
  have hr₂ : Runs w p ω
      (.assign 2 (.load (.bin .add (.reg 11) (.load (.bin .add (.reg 10) (.reg 8))))))
        mid .normal out 8 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid, Function.update_of_ne, h8, h10, h11,
      hh, hh', hhead], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 8, 8, hr₁, hr₂, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], rfl, ?_⟩
  intro r h1 h2
  simp [out, mid, Function.update_of_ne, h1, h2]

/-- The tree reserves vertex `v + 1` for graph name `v`. Registers
1 and 2 are converted in place before the tree call. -/
@[expose] def treeEditVertexIndices : Stmt :=
  .assign 1 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 2 (.bin .add (.reg 2) (.const 1))

/-- Both converted names are legal link-cut vertices, and the
conversion costs nine steps. -/
theorem treeEditVertexIndices_runs {w u v n : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (h1 : st.regs 1 = u) (h2 : st.regs 2 = v)
    (hu : u < n) (hv : v < n) (hn : n < 2 ^ w) :
    ∃ out, Runs w p ω treeEditVertexIndices st .normal out 9 ∧
      out.regs 1 = u + 1 ∧ out.regs 2 = v + 1 ∧
      LinkCut.isVertex n (out.regs 1) ∧ LinkCut.isVertex n (out.regs 2) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 1 → r ≠ 2 → out.regs r = st.regs r) := by
  let mid := { st with regs := Function.update st.regs 1 (u + 1) }
  let out := { mid with regs := Function.update mid.regs 2 (v + 1) }
  have hw : 1 < 2 ^ w := by omega
  have hU : u + 1 < 2 ^ w := by omega
  have hV : v + 1 < 2 ^ w := by omega
  have hfirst : Runs w p ω (.assign 1 (.bin .add (.reg 1) (.const 1))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, h1, hw, hU], rfl, rfl, rfl⟩
  have hsecond : Runs w p ω (.assign 2 (.bin .add (.reg 2) (.const 1))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, mid, Function.update_of_ne, h2, hw, hV], rfl, rfl, rfl⟩
  have hu' : out.regs 1 = u + 1 := by simp [out, mid, Function.update_of_ne]
  have hv' : out.regs 2 = v + 1 := by simp [out]
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 4, hfirst, hsecond, rfl⟩),
    hu', hv', ?_, ?_, rfl, ?_⟩
  · rw [hu']
    exact ⟨by omega, by omega⟩
  · rw [hv']
    exact ⟨by omega, by omega⟩
  · intro r hr1 hr2
    simp [out, mid, Function.update_of_ne, hr1, hr2]

/-- The graph capacity bounds both endpoint names, so the endpoint
lookup and conversion together prepare the two legal tree vertices. -/
theorem treeEditResolve_runs {w base vc ec e n : ℕ} {G : MGraph}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (he : TreeEditEndpointAt st.mem base vc ec G e)
    (hroom : base + dynGraphSize vc ec ≤ 2 ^ w)
    (hvc : vc ≤ n) (hn : n < 2 ^ w)
    (h8 : st.regs 8 = e) (h9 : st.regs 9 = dgETailSlotBase base vc ec)
    (h10 : st.regs 10 = dgEHeadSlotBase base vc ec)
    (h11 : st.regs 11 = dgIntToExtBase base vc) :
    ∃ out, Runs w p ω (treeEditEndpoints ;; treeEditVertexIndices) st .normal out 27 ∧
      out.regs 1 = G.tail e + 1 ∧ out.regs 2 = G.head e + 1 ∧
      LinkCut.isVertex n (out.regs 1) ∧ LinkCut.isVertex n (out.regs 2) ∧ out.mem = st.mem ∧
      (∀ r, r ≠ 1 → r ≠ 2 → out.regs r = st.regs r) := by
  obtain ⟨mid, hr, hu, hv, hmem, hregs⟩ :=
    treeEditEndpoints_runs (p := p) (ω := ω) he hroom h8 h9 h10 h11
  have hU := he.tailNameBound.trans_le hvc
  have hV := he.headNameBound.trans_le hvc
  obtain ⟨out, hs, hu', hv', huBound, hvBound, hm, hsave⟩ :=
    treeEditVertexIndices_runs (p := p) (ω := ω) hu hv hU hV hn
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 17, 9, hr, hs, rfl⟩),
    hu', hv', huBound, hvBound, hm.trans hmem,
    fun r h1 h2 => (hsave r h1 h2).trans (hregs r h1 h2)⟩

end MinCostFlow.MinRatio
