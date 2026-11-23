module

public import MinCostFlow.LastLevelProgram.RepresentativeScan

/-!
# Parallel-class scan invariant

For Definition 5.8 (pages 19–20), the scan keeps a class key and a
shortest edge encountered in that class. It saves winners of completed
non-loop classes in encounter order.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM SparseCore Num DynSpanner.Program

/-- The state represented by the active key, incumbent and output array. -/
structure RepresentativeGroupState where
  anchor : ℕ
  winner : ℕ
  completed : List ℕ

/-- The initial edge is both the class anchor and its first winner. -/
def RepresentativeGroupState.seed (e : ℕ) : RepresentativeGroupState :=
  ⟨e,e,[]⟩

/-- Emit the active winner when its endpoints differ. -/
def RepresentativeGroupState.finish (G : MGraph) (s : RepresentativeGroupState) : List ℕ :=
  if (edgePairKey G s.anchor).1 = (edgePairKey G s.anchor).2 then s.completed
  else s.completed ++ [s.winner]

/-- Advance the mathematical scan using the encoded lengths. -/
def RepresentativeGroupState.step (G : MGraph) (length : ℕ → ℕ)
    (s : RepresentativeGroupState) (e : ℕ) : RepresentativeGroupState :=
  if edgePairKey G s.anchor = edgePairKey G e then
    {s with winner := if length e < length s.winner then e else s.winner}
  else ⟨e,e,s.finish G⟩

/-- The output array needs at most one slot per edge. -/
theorem RepresentativeGroupState.finish_length_le (G : MGraph) (s : RepresentativeGroupState) :
    (s.finish G).length ≤ s.completed.length + 1 := by
  unfold finish
  split <;> simp

/-- A scan iteration adds at most one completed representative. -/
theorem RepresentativeGroupState.step_length_le (G : MGraph) (length : ℕ → ℕ)
    (s : RepresentativeGroupState) (e : ℕ) :
    (s.step G length e).completed.length ≤ s.completed.length + 1 := by
  unfold step
  split
  · exact Nat.le_succ _
  · exact s.finish_length_le G

/-- After seeding, the number of completed representatives is bounded by
the number of subsequent edges processed. -/
theorem RepresentativeGroupState.fold_length_le (G : MGraph) (length : ℕ → ℕ)
    (s : RepresentativeGroupState) (edges : List ℕ) :
    (edges.foldl (step G length) s).completed.length ≤ s.completed.length + edges.length := by
  induction edges generalizing s with
  | nil => simp
  | cons e rest ih =>
    simp only [List.foldl_cons,List.length_cons]
    exact (ih (s.step G length e)).trans
      (by simpa [Nat.add_right_comm, ← Nat.add_assoc] using Nat.add_le_add_right (s.step_length_le G length e) rest.length)

/-- Every edge stored by the scan belongs to the allowed input set. -/
def RepresentativeGroupState.EdgesIn (s : RepresentativeGroupState) (E : Finset ℕ) : Prop :=
  s.anchor ∈ E ∧ s.winner ∈ E ∧ ∀ e ∈ s.completed, e ∈ E

/-- Seeding the scan stores only the first input edge. -/
theorem RepresentativeGroupState.seed_edgesIn {E : Finset ℕ} {e : ℕ} (he : e ∈ E) :
    (seed e).EdgesIn E := by
  simp [seed, EdgesIn, he]

/-- The output of a finished class consists of input edges. -/
theorem RepresentativeGroupState.finish_edgesIn {G : MGraph} {s : RepresentativeGroupState}
    {E : Finset ℕ} (hs : s.EdgesIn E) : ∀ e ∈ s.finish G, e ∈ E := by
  intro e he
  unfold finish at he
  split at he
  · exact hs.2.2 e he
  · rcases List.mem_append.mp he with hc | hw
    · exact hs.2.2 e hc
    · simpa [(List.mem_singleton.mp hw)] using hs.2.1

/-- Updating a class preserves membership in the input edge set. -/
theorem RepresentativeGroupState.step_edgesIn {G : MGraph} {length : ℕ → ℕ}
    {s : RepresentativeGroupState} {e : ℕ} {E : Finset ℕ} (hs : s.EdgesIn E) (he : e ∈ E) :
    (s.step G length e).EdgesIn E := by
  unfold step
  split
  · refine ⟨hs.1, ?_, hs.2.2⟩
    split <;> first | exact he | exact hs.2.1
  · exact ⟨he, he, finish_edgesIn hs⟩

/-- The reachable scan state stores only input edges throughout the fold. -/
theorem RepresentativeGroupState.fold_edgesIn {G : MGraph} {length : ℕ → ℕ}
    {E : Finset ℕ} (s : RepresentativeGroupState) (edges : List ℕ)
    (hs : s.EdgesIn E) (he : ∀ e ∈ edges, e ∈ E) :
    (edges.foldl (step G length) s).EdgesIn E := by
  induction edges generalizing s with
  | nil => exact hs
  | cons e rest ih =>
    exact ih (s.step G length e) (step_edgesIn hs (he e (List.mem_cons_self ..)))
      (fun f hf => he f (List.mem_cons_of_mem _ hf))

/-- The active key, winner register and completed array represent the scan state. -/
def RepresentativeGroupState.At (s : RepresentativeGroupState) (st : State)
    (G : MGraph) (vCap eCap dst : ℕ) : Prop :=
  st.regs 18 = representativeSortKey G vCap eCap s.anchor ∧
  st.regs 12 = s.winner ∧
  st.regs 17 = s.completed.length ∧
  ListAt st.mem dst s.completed

/-- Finishing a class realizes the logical output list in memory. -/
theorem RepresentativeGroupState.finish_at {G : MGraph} {s : RepresentativeGroupState}
    {st out : State} {dst : ℕ}
    (hlist : ListAt st.mem dst s.completed)
    (hm : out.mem = if (edgePairKey G s.anchor).1 = (edgePairKey G s.anchor).2 then st.mem
      else Function.update st.mem (dst+s.completed.length) s.winner) :
    ListAt out.mem dst (s.finish G) := by
  rw [hm]
  unfold finish
  split
  · exact hlist
  · exact hlist.snoc s.winner

/-- The register and memory updates of a group step realize the logical step. -/
theorem RepresentativeGroupState.step_at {G : MGraph} {s : RepresentativeGroupState}
    {st out : State} {vCap eCap dst e : ℕ} {length : ℕ → ℕ}
    (hlist : ListAt st.mem dst s.completed)
    (hm : out.mem = if edgePairKey G s.anchor ≠ edgePairKey G e ∧
          (edgePairKey G s.anchor).1 ≠ (edgePairKey G s.anchor).2 then
        Function.update st.mem (dst+s.completed.length) s.winner else st.mem)
    (hn : out.regs 17 = if edgePairKey G s.anchor ≠ edgePairKey G e ∧
        (edgePairKey G s.anchor).1 ≠ (edgePairKey G s.anchor).2 then
        s.completed.length+1 else s.completed.length)
    (hk : out.regs 18 = representativeSortKey G vCap eCap
        (if edgePairKey G s.anchor = edgePairKey G e then s.anchor else e))
    (hw : out.regs 12 = if edgePairKey G s.anchor = edgePairKey G e then
        if length e < length s.winner then e else s.winner else e) :
    (s.step G length e).At out G vCap eCap dst := by
  by_cases hsame : edgePairKey G s.anchor = edgePairKey G e
  · simp [hsame] at hm hn hk hw
    exact ⟨by simpa [step,hsame] using hk,by simpa [step,hsame] using hw,
      by simpa [step,hsame] using hn,by simpa [step,hsame,hm] using hlist⟩
  · simp [hsame] at hm hn hk hw
    have hfinished : ListAt out.mem dst (s.finish G) := finish_at hlist (by
      split <;> rename_i h <;> simpa [h] using hm)
    have hcount : out.regs 17 = (s.finish G).length := by
      unfold finish
      split <;> rename_i h <;> simpa [h] using hn
    simpa [step,At,hsame] using And.intro hk (And.intro hw (And.intro hcount hfinished))

/-- A live edge has valid endpoint digits and a key that fits in one word. -/
theorem representativeLiveKey_bounds {w g vCap eCap e : ℕ} {G : MGraph}
    {mem : ℕ → ℕ} (hG : DynGraphAt mem g vCap eCap G) (he : e ∈ G.E)
    (hcap : vCap*vCap*eCap ≤ 2^w) :
    e < eCap ∧ (edgePairKey G e).2 < vCap ∧ representativeSortKey G vCap eCap e < 2^w := by
  have hends := hG.1 e he
  have ht := hG.2.1 _ hends.1
  have hh := hG.2.1 _ hends.2
  have he' := hG.2.2.1 _ he
  exact ⟨he',max_lt ht hh,(representativeSortKey_lt G vCap eCap e ht hh he').trans_le hcap⟩

/-- The machine step implements the list-fold update and preserves
memory outside the cell where it may append a winner. -/
theorem representativeGroupStep_at_runs {w entry g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} {st : State}
    (s : RepresentativeGroupState) (e src i dst lengths L : ℕ)
    (hcmp : MeetsContract w p entry (unsignedLessContract w 4))
    (hG : DynGraphAt st.mem g vCap eCap G) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hin : s.EdgesIn G.E) (he : e ∈ G.E) (hat : s.At st G vCap eCap dst)
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap) (h6 : st.regs 6 = src)
    (h8 : st.regs 8 = i) (h13 : st.regs 13 = lengths) (h14 : st.regs 14 = L)
    (h16 : st.regs 16 = dst)
    (hread : st.mem (src+i) = representativeSortKey G vCap eCap e)
    (hs : src+i < 2^w) (hd : dst+s.completed.length < 2^w)
    (hc : s.completed.length+1 < 2^w)
    (hlen : ∀ f ∈ G.E, lengths+f*L+L < 2^w ∧ Valid st.mem (lengths+f*L) 4 L) :
    let len := fun f => unsignedVal st.mem (lengths+f*L) 4 L
    ∃ out cost, Runs w p ω (representativeGroupStep entry) st .normal out cost ∧
      (s.step G len e).At out G vCap eCap dst ∧
      (∀ a, a ≠ dst+s.completed.length → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 11 → r ≠ 12 → r ≠ 15 → r ≠ 17 → r ≠ 18 → r ≠ 19 →
        out.regs r = st.regs r) ∧ cost ≤ 41*L+48 := by
  obtain ⟨ha,hav,hab⟩ := representativeLiveKey_bounds hG hin.1 hcap
  obtain ⟨he',hev,heb⟩ := representativeLiveKey_bounds hG he hcap
  obtain ⟨hel,hevalid⟩ := hlen e he
  obtain ⟨hwl,hwvalid⟩ := hlen s.winner hin.2.1
  obtain ⟨out,c,hrun,hm,hn,hkey,hw,hregs,hcost⟩ :=
    representativeGroupStep_runs st G s.anchor e src i dst s.completed.length s.winner lengths L
      hcmp h4 h5 h6 h8 hat.2.1 h13 h14 h16 hat.2.2.1 hat.1 hread ha he' hav hev hab heb
      hs hd hc hel hwl hevalid hwvalid
  refine ⟨out,c,hrun,RepresentativeGroupState.step_at hat.2.2.2 hm hn hkey hw,?_,hregs,hcost⟩
  intro a hne
  rw [hm]
  split
  · exact Function.update_of_ne hne ..
  · rfl

/-- Advancing a processed prefix applies exactly one logical group update. -/
theorem RepresentativeGroupState.fold_take_succ {G : MGraph} {length : ℕ → ℕ}
    (s : RepresentativeGroupState) {edges : List ℕ} {i : ℕ} (hi : i < edges.length) :
    ((edges.take (i+1)).foldl (step G length) s) =
      ((edges.take i).foldl (step G length) s).step G length edges[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  rfl

/-- An initially empty output occupies fewer cells than the number
of processed edges, since the active winner still occupies a register. -/
theorem RepresentativeGroupState.seed_fold_take_length_le (G : MGraph) (length : ℕ → ℕ)
    (e : ℕ) (edges : List ℕ) (i : ℕ) :
    ((edges.take i).foldl (step G length) (seed e)).completed.length ≤ i := by
  exact (fold_length_le G length (seed e) (edges.take i)).trans (by
    simp [seed,List.length_take])

/-- Every prefix of the tail keeps the initial edge and all stored
winners inside the input graph. -/
theorem RepresentativeGroupState.seed_fold_take_edgesIn {G : MGraph} {length : ℕ → ℕ}
    {e : ℕ} {edges : List ℕ} (he : e ∈ G.E) (ht : ∀ f ∈ edges, f ∈ G.E) (i : ℕ) :
    ((edges.take i).foldl (step G length) (seed e)).EdgesIn G.E :=
  fold_edgesIn (seed e) (edges.take i) (seed_edgesIn he)
    (fun f hf => ht f (List.mem_of_mem_take hf))

/-- Registers preserved by the representative class scan. -/
def representativeGroupPreserves (r : ℕ) : Prop :=
  r < 8 ∨ r = 13 ∨ r = 14 ∨ r = 16 ∨ 20 ≤ r

/-- Starting with the first edge in registers, scan the rest of the
sorted keys and leave the final class ready to flush. -/
theorem representativeGroupTail_triple {w entry g vCap eCap : ℕ}
    {p : Program} {G : MGraph} (initial : State) (first src dst lengths L : ℕ)
    (edges : List ℕ) (hcmp : MeetsContract w p entry (unsignedLessContract w 4))
    (hG : DynGraphAt initial.mem g vCap eCap G)
    (hfirst : first ∈ G.E) (hedges : ∀ e ∈ edges, e ∈ G.E)
    (hseed : (RepresentativeGroupState.seed first).At initial G vCap eCap dst)
    (h4 : initial.regs 4 = vCap) (h5 : initial.regs 5 = eCap) (h6 : initial.regs 6 = src)
    (h7 : initial.regs 7 = edges.length+1) (h13 : initial.regs 13 = lengths)
    (h14 : initial.regs 14 = L) (h16 : initial.regs 16 = dst)
    (hread : ∀ j (hj : j < edges.length),
      initial.mem (src+(j+1)) = representativeSortKey G vCap eCap edges[j])
    (hw : 1 < 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hs : src+(edges.length+1) < 2^w) (hd : dst+(edges.length+1) < 2^w)
    (hsg : src+(edges.length+1) ≤ dst ∨ dst+(edges.length+1) ≤ src)
    (hdg : g+dynGraphSize vCap eCap ≤ dst ∨ dst+(edges.length+1) ≤ g)
    (hlen : ∀ f ∈ G.E, lengths+f*L+L < 2^w ∧ Valid initial.mem (lengths+f*L) 4 L ∧
      (lengths+f*L+L ≤ dst ∨ dst+(edges.length+1) ≤ lengths+f*L)) :
    let len := fun f => unsignedVal initial.mem (lengths+f*L) 4 L
    Triple w p (fun st => st = initial)
      (forRange 8 (.const 1) (.reg 7) (representativeGroupStep entry))
      (normalPost fun st =>
        (edges.foldl (RepresentativeGroupState.step G len) (.seed first)).At st G vCap eCap dst ∧
        (∀ a, a < dst ∨ dst+(edges.length+1) ≤ a → st.mem a = initial.mem a) ∧
        ∀ r, representativeGroupPreserves r → st.regs r = initial.regs r)
      (fun _ => edges.length*(41*L+57)+7) := by
  let len := fun f => unsignedVal initial.mem (lengths+f*L) 4 L
  let model := fun i => (edges.take (i-1)).foldl (RepresentativeGroupState.step G len) (.seed first)
  let frame := fun (st : State) =>
    ∀ a, a < dst ∨ dst+(edges.length+1) ≤ a → st.mem a = initial.mem a
  let keep := fun (st : State) => ∀ r, representativeGroupPreserves r → st.regs r = initial.regs r
  let Inv := fun i (st : State) => st.regs 8 = i ∧ (model i).At st G vCap eCap dst ∧ frame st ∧ keep st
  have loop := Triple.forRange_const (p := p) (r := 8) (lo := .const 1) (hi := .reg 7)
    (body := representativeGroupStep entry) (P := fun st => st = initial) (Inv := Inv)
    (41*L+48) 1 (edges.length+1) (by omega) hw (fun _ => by omega)
    (fun st hst => by
      subst st
      refine ⟨by simp [Expr.eval,hw],by simp,?_,fun _ _ => rfl,?_⟩
      · simpa [model,RepresentativeGroupState.At] using hseed
      · intro r hr
        have hne : r ≠ 8 := by
          unfold representativeGroupPreserves at hr
          omega
        exact Function.update_of_ne hne ..)
    (fun _ _ _ _ h => h.1)
    (fun _ st _ _ h => by simp [Expr.eval,(h.2.2.2 7 (by unfold representativeGroupPreserves; omega)).trans h7])
    (fun i hi hupper => by
      intro st ω ⟨hindex,hat,hframe,hkeep⟩
      have hj : i-1 < edges.length := by omega
      let e := edges[i-1]
      have he : e ∈ G.E := hedges _ (List.getElem_mem hj)
      have hstate := RepresentativeGroupState.seed_fold_take_edgesIn (length := len)
        hfirst hedges (i-1)
      have hcount := RepresentativeGroupState.seed_fold_take_length_le G len first edges (i-1)
      change (model i).completed.length ≤ i-1 at hcount
      have hgraph := representativeGraph_frame hG (fun a ha hb => hframe a (by omega))
      have hcell f (hf : f ∈ G.E) j (hj' : j < L) :
          st.mem (lengths+f*L+j) = initial.mem (lengths+f*L+j) :=
        hframe _ (by have hsep := (hlen f hf).2.2; omega)
      have hlen' f (hf : f ∈ G.E) :
          lengths+f*L+L < 2^w ∧ Valid st.mem (lengths+f*L) 4 L := by
        refine ⟨(hlen f hf).1,fun j hj' => ?_⟩
        rw [hcell f hf j hj']
        exact (hlen f hf).2.1 j hj'
      have hread' : st.mem (src+i) = representativeSortKey G vCap eCap e := by
        rw [hframe _ (by omega),show i = i-1+1 by omega]
        exact hread (i-1) hj
      obtain ⟨out,c,hrun,hout,hm,hregs,hcost⟩ :=
        representativeGroupStep_at_runs (ω := ω) (model i) e src i dst lengths L hcmp hgraph hcap
          hstate he hat ((hkeep 4 (by unfold representativeGroupPreserves; omega)).trans h4) ((hkeep 5 (by unfold representativeGroupPreserves; omega)).trans h5)
          ((hkeep 6 (by unfold representativeGroupPreserves; omega)).trans h6) hindex ((hkeep 13 (by unfold representativeGroupPreserves; omega)).trans h13)
          ((hkeep 14 (by unfold representativeGroupPreserves; omega)).trans h14) ((hkeep 16 (by unfold representativeGroupPreserves; omega)).trans h16)
          hread' (by omega) (by omega) (by omega) hlen'
      have hmodel : model (i+1) = (model i).step G len e := by
        change ((edges.take (i+1-1)).foldl _ _) = _
        rw [show i+1-1 = i-1+1 by omega]
        exact RepresentativeGroupState.fold_take_succ (.seed first) hj
      have hvalue f (hf : f ∈ G.E) : unsignedVal st.mem (lengths+f*L) 4 L = len f :=
        unsignedVal_congr (hcell f hf)
      have hstep : (model i).step G (fun f => unsignedVal st.mem (lengths+f*L) 4 L) e =
          (model i).step G len e := by
        unfold RepresentativeGroupState.step
        simp only [hvalue e he,hvalue (model i).winner hstate.2.1]
      rw [hstep,← hmodel] at hout
      refine ⟨.normal,out,c,hrun,⟨⟨by simp,?_,?_,?_⟩,?_⟩,hcost⟩
      · simpa only [RepresentativeGroupState.At,Function.update_of_ne (by decide : (18 : ℕ) ≠ 8),
          Function.update_of_ne (by decide : (12 : ℕ) ≠ 8),
          Function.update_of_ne (by decide : (17 : ℕ) ≠ 8)] using hout
      · intro a ha
        exact (hm a (by omega)).trans (hframe a ha)
      · intro r hr
        have hne : r ≠ 8 ∧ r ≠ 11 ∧ r ≠ 12 ∧ r ≠ 15 ∧ r ≠ 17 ∧ r ≠ 18 ∧ r ≠ 19 := by
          unfold representativeGroupPreserves at hr
          omega
        exact (Function.update_of_ne hne.1 ..).trans
          ((hregs r hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2.1
            hne.2.2.2.2.2.2).trans (hkeep r hr))
      · exact (hregs 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hindex)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned _ => exact h
    | normal => simpa [model,keep,frame] using h.2
  · intro _ _
    simp [Expr.size_const,Expr.size_reg,Nat.add_assoc]

/-- Finish the final class and expose the resulting output array and count.
The write, when needed, is within the reserved representative array. -/
theorem representativeGroupFinish_runs {w g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} {st : State}
    (s : RepresentativeGroupState) (dst countCap : ℕ)
    (hG : DynGraphAt st.mem g vCap eCap G) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hin : s.EdgesIn G.E) (hat : s.At st G vCap eCap dst)
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap) (h16 : st.regs 16 = dst)
    (hcount : s.completed.length < countCap) (hdst : dst+countCap < 2^w) :
    ∃ out cost, Runs w p ω representativeFlush st .normal out cost ∧
      ListAt out.mem dst (s.finish G) ∧ out.regs 17 = (s.finish G).length ∧
      (∀ a, a < dst ∨ dst+countCap ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 17 → out.regs r = st.regs r) ∧ cost ≤ 23 := by
  obtain ⟨he,hv,hkey⟩ := representativeLiveKey_bounds hG hin.1 hcap
  obtain ⟨out,c,hrun,hm,hn,hregs,hcost⟩ :=
    representativeFlush_runs st G s.anchor dst s.completed.length s.winner
      h4 h5 hat.2.1 h16 hat.2.2.1 hat.1 he hv hkey (by omega) (by omega)
  refine ⟨out,c,hrun,RepresentativeGroupState.finish_at hat.2.2.2 hm,?_,?_,hregs,hcost⟩
  · unfold RepresentativeGroupState.finish
    split <;> rename_i h <;> simpa [h] using hn
  · intro a ha
    rw [hm]
    split
    · rfl
    · exact Function.update_of_ne (by omega) ..

/-- The nonempty scan writes the completed group fold with linear
cost in the number of keys and the length block width. -/
theorem representativeGroupScan_cons_runs {w entry g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} (st : State)
    (first src dst lengths L : ℕ) (edges : List ℕ)
    (hcmp : MeetsContract w p entry (unsignedLessContract w 4))
    (hG : DynGraphAt st.mem g vCap eCap G)
    (hfirst : first ∈ G.E) (hedges : ∀ e ∈ edges, e ∈ G.E)
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap) (h6 : st.regs 6 = src)
    (h7 : st.regs 7 = edges.length+1) (h13 : st.regs 13 = lengths)
    (h14 : st.regs 14 = L) (h16 : st.regs 16 = dst)
    (hkeys : ListAt st.mem src ((first :: edges).map (representativeSortKey G vCap eCap)))
    (hw : 1 < 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hs : src+(edges.length+1) < 2^w) (hd : dst+(edges.length+1) < 2^w)
    (hsg : src+(edges.length+1) ≤ dst ∨ dst+(edges.length+1) ≤ src)
    (hdg : g+dynGraphSize vCap eCap ≤ dst ∨ dst+(edges.length+1) ≤ g)
    (hlen : ∀ f ∈ G.E, lengths+f*L+L < 2^w ∧ Valid st.mem (lengths+f*L) 4 L ∧
      (lengths+f*L+L ≤ dst ∨ dst+(edges.length+1) ≤ lengths+f*L)) :
    let len := fun f => unsignedVal st.mem (lengths+f*L) 4 L
    let winners := (edges.foldl (RepresentativeGroupState.step G len) (.seed first)).finish G
    ∃ out cost, Runs w p ω (representativeGroupScan entry) st .normal out cost ∧
      ListAt out.mem dst winners ∧ out.regs 17 = winners.length ∧
      (∀ a, a < dst ∨ dst+(edges.length+1) ≤ a → out.mem a = st.mem a) ∧
      (∀ r, representativeGroupPreserves r → out.regs r = st.regs r) ∧
      cost ≤ edges.length*(41*L+57)+58 := by
  have hread : st.mem src = representativeSortKey G vCap eCap first := by
    simpa using hkeys 0 (by simp)
  obtain ⟨he,hv,hk⟩ := representativeLiveKey_bounds hG hfirst hcap
  obtain ⟨seed,hinit,hmem,hcount,hkey,hwin,hkeep⟩ :=
    representativeGroupInit_runs (ω := ω) st G src first h5 h6 hread (by omega) he hv hk
  have hseed : (RepresentativeGroupState.seed first).At seed G vCap eCap dst :=
    ⟨hkey,hwin,hcount,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  have htail := representativeGroupTail_triple seed first src dst lengths L edges hcmp
    (by rwa [hmem]) hfirst hedges hseed
    ((hkeep 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h4)
    ((hkeep 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h5)
    ((hkeep 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h6)
    ((hkeep 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h7)
    ((hkeep 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13)
    ((hkeep 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14)
    ((hkeep 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16)
    (fun j hj => by
      rw [hmem]
      simpa only [List.map_cons,List.getElem_map,List.getElem_cons_succ] using hkeys (j+1) (by simpa using hj))
    hw hcap hs hd hsg hdg (by rwa [hmem])
  obtain ⟨o,mid,c,hloop,hpost,hcost⟩ := htail.runs ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rw [hmem] at hpost
    obtain ⟨hat,hframe,hregs⟩ := hpost
    let len := fun f => unsignedVal st.mem (lengths+f*L) 4 L
    let model := edges.foldl (RepresentativeGroupState.step G len) (.seed first)
    have hin : model.EdgesIn G.E := RepresentativeGroupState.fold_edgesIn _ _
      (RepresentativeGroupState.seed_edgesIn hfirst) hedges
    have hn : model.completed.length < edges.length+1 := by
      apply Nat.lt_succ_of_le
      simpa [model, RepresentativeGroupState.seed] using (RepresentativeGroupState.fold_length_le G len (.seed first) edges)
    have hgraph := representativeGraph_frame hG (fun a ha hb => hframe a (by omega))
    obtain ⟨out,d,hflush,hlist,hnum,houtside,houtreg,hdcost⟩ :=
      representativeGroupFinish_runs (ω := ω) model dst (edges.length+1) hgraph hcap hin hat
        ((hregs 4 (by unfold representativeGroupPreserves; omega)).trans ((hkeep 4 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans h4))
        ((hregs 5 (by unfold representativeGroupPreserves; omega)).trans ((hkeep 5 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans h5))
        ((hregs 16 (by unfold representativeGroupPreserves; omega)).trans ((hkeep 16 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)).trans h16)) hn hd
    have hseq : Runs w p ω (.seq (forRange 8 (.const 1) (.reg 7) (representativeGroupStep entry))
        representativeFlush) seed .normal out (c+d+1) :=
      runs_seq_iff.mpr (Or.inr ⟨mid,c,d,hloop,hflush,rfl⟩)
    have hbody : Runs w p ω (.seq representativeGroupInit
        (.seq (forRange 8 (.const 1) (.reg 7) (representativeGroupStep entry)) representativeFlush))
        st .normal out (22+(c+d+1)+1) :=
      runs_seq_iff.mpr (Or.inr ⟨seed,22,c+d+1,hinit,hseq,rfl⟩)
    have hz : 0 < 2^w := by omega
    have hrun : Runs w p ω (representativeGroupScan entry) st .normal out (c+d+28) :=
      runs_cond_iff.mpr ⟨0,22+(c+d+1)+1,by simp [Expr.eval,BinOp.eval,h7,hz],
        by simpa using hbody,by change c+d+28 = 3+(22+(c+d+1)+1)+1; omega⟩
    refine ⟨out,c+d+28,hrun,hlist,hnum,fun a ha => (houtside a ha).trans (hframe a ha),?_,by omega⟩
    intro r hr'
    have hp := hr'
    unfold representativeGroupPreserves at hp
    exact (houtreg r (by omega)).trans ((hregs r hr').trans
      (hkeep r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))

/-- Within one class, a fold keeps the shortest edge and chooses the
smallest name among equal lengths when names arrive in increasing order. -/
theorem RepresentativeGroupState.fold_sameClass (G : MGraph) (len : ℕ → ℕ)
    (s : RepresentativeGroupState) (edges : List ℕ)
    (hp : ∀ e ∈ edges, edgePairKey G s.anchor = edgePairKey G e)
    (hs : edges.Pairwise (· ≤ ·)) (hw : ∀ e ∈ edges, s.winner ≤ e) :
    let out := edges.foldl (step G len) s
    out.anchor = s.anchor ∧ out.completed = s.completed ∧
      out.winner ∈ s.winner :: edges ∧
      ∀ e ∈ s.winner :: edges, len out.winner ≤ len e ∧
        (len out.winner = len e → out.winner ≤ e) := by
  induction edges generalizing s with
  | nil => simp
  | cons e rest ih =>
    have hpair := hp e (by simp)
    have htail f (hf : f ∈ rest) := hp f (List.mem_cons_of_mem _ hf)
    have hnames := List.pairwise_cons.mp hs
    have hwe := hw e (by simp)
    let next := s.step G len e
    have hnext : next = {s with winner := if len e < len s.winner then e else s.winner} := by
      simp [next,step,hpair]
    have hsmall : ∀ f ∈ rest, next.winner ≤ f := by
      intro f hf
      rw [hnext]
      split
      · exact hnames.1 f hf
      · exact hwe.trans (hnames.1 f hf)
    obtain ⟨ha,hc,hm,hle⟩ := ih next (by simpa [hnext] using htail) hnames.2 hsmall
    change (rest.foldl (step G len) next).anchor = s.anchor ∧ _
    have ha' : next.anchor = s.anchor := by rw [hnext]
    have hc' : next.completed = s.completed := by rw [hnext]
    have hmem : next.winner ∈ s.winner :: e :: rest := by
      rw [hnext]
      simp only
      split <;> simp
    refine ⟨ha.trans ha',hc.trans hc',?_,?_⟩
    · rcases List.mem_cons.mp hm with h | h
      · exact h ▸ hmem
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
    · intro f hf
      by_cases hrest : f ∈ rest
      · exact hle f (List.mem_cons_of_mem _ hrest)
      have hmid : len next.winner ≤ len f ∧
          (len next.winner = len f → next.winner ≤ f) := by
        rcases List.mem_cons.mp hf with rfl | hf
        · rw [hnext]
          simp only
          split <;> rename_i h <;> omega
        · rcases List.mem_cons.mp hf with rfl | hf
          · rw [hnext]
            simp only
            split <;> rename_i h <;> omega
          · exact False.elim (hrest hf)
      have hmin := hle next.winner (by simp)
      change len (rest.foldl (step G len) next).winner ≤ len f ∧
        (len (rest.foldl (step G len) next).winner = len f → _)
      exact ⟨hmin.1.trans hmid.1,fun h =>
        (hmin.2 (by omega)).trans (hmid.2 (by omega))⟩

/-- At a class boundary, the fold emits the completed class and can
continue on the remaining edges from the new class seed. -/
theorem RepresentativeGroupState.fold_after_boundary (G : MGraph) (len : ℕ → ℕ)
    (s : RepresentativeGroupState) (done rest : List ℕ) (e : ℕ)
    (h : edgePairKey G (done.foldl (step G len) s).anchor ≠ edgePairKey G e) :
    (done ++ e :: rest).foldl (step G len) s =
      rest.foldl (step G len) {seed e with completed := (done.foldl (step G len) s).finish G} := by
  rw [List.foldl_append, List.foldl_cons]
  simp only [step, ite_eq_right h, seed]

/-- A non-loop leading class emits its canonical winner when its
sorted prefix enumerates the full class. -/
theorem representativeLeadingClass_finish {G : MGraph} {vCap eCap first : ℕ}
    (len : ℕ → ℕ) (ℓ : ℕ → ℝ) (edges completed : List ℕ)
    (hfirst : first ∈ nonLoopEdges G)
    (he : first < eCap) (hv : (edgePairKey G first).2 < vCap)
    (hvalid : ∀ e ∈ edges, e < eCap ∧ (edgePairKey G e).2 < vCap)
    (hs : (first :: edges).Pairwise (fun e f => representativeSortKey G vCap eCap e ≤
      representativeSortKey G vCap eCap f))
    (hmem : ∀ e ∈ edges, e ∈ G.E)
    (hcover : ∀ e ∈ nonLoopEdges G, edgePairKey G e = edgePairKey G first →
      e ∈ first :: edges)
    (horder : ∀ e ∈ G.E, ∀ f ∈ G.E, len e ≤ len f ↔ ℓ e ≤ ℓ f) :
    let group := edges.takeWhile (fun e => decide (edgePairKey G e = edgePairKey G first))
    let out := group.foldl (RepresentativeGroupState.step G len)
      { RepresentativeGroupState.seed first with completed := completed }
    out.anchor = first ∧ out.finish G = completed ++ [shortestEdge G ℓ (edgePairKey G first)] := by
  let group := edges.takeWhile (fun e => decide (edgePairKey G e = edgePairKey G first))
  have hgroup : group = edges.filter (fun e => decide (edgePairKey G e = edgePairKey G first)) :=
    representativeClass_takeWhile_eq_filter edges he hv hvalid hs
  have hpair : ∀ e ∈ group, edgePairKey G first = edgePairKey G e := by
    intro e hm
    rw [hgroup] at hm
    exact (of_decide_eq_true (List.mem_filter.mp hm).2).symm
  have hnames : (first :: group).Pairwise (· ≤ ·) := by
    have hh := representativeClass_pairwise (edgePairKey G first) hs
    simpa [hgroup] using hh
  obtain ⟨ha,hc,hw,hmin⟩ := RepresentativeGroupState.fold_sameClass G len
    { RepresentativeGroupState.seed first with completed := completed } group hpair
    (List.pairwise_cons.mp hnames).2 (List.pairwise_cons.mp hnames).1
  let out := group.foldl (RepresentativeGroupState.step G len)
    { RepresentativeGroupState.seed first with completed := completed }
  have hk (e : ℕ) (hm : e ∈ first :: group) : edgePairKey G e = edgePairKey G first := by
    rcases List.mem_cons.mp hm with rfl | hg
    · rfl
    · exact (hpair e hg).symm
  have hgmem (e : ℕ) (hm : e ∈ first :: group) : e ∈ G.E := by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact (Finset.mem_filter.mp hfirst).1
    · rw [hgroup] at hm
      exact hmem e (List.mem_filter.mp hm).1
  have hloop : (edgePairKey G first).1 ≠ (edgePairKey G first).2 := by
    have hn := (Finset.mem_filter.mp hfirst).2
    by_cases h : G.tail first ≤ G.head first
    · simpa [edgePairKey,min_eq_left h,max_eq_right h] using hn
    · have h' := (le_of_not_ge h)
      simpa [edgePairKey,min_eq_right h',max_eq_left h',eq_comm] using hn
  have hout : out.winner ∈ nonLoopEdges G := by
    refine Finset.mem_filter.mpr ⟨hgmem _ hw,?_⟩
    intro heq
    have heq' : (edgePairKey G out.winner).1 = (edgePairKey G out.winner).2 := by
      simp [edgePairKey,heq]
    rw [hk _ hw] at heq'
    exact hloop heq'
  have hwin := eq_shortestEdge_of_minimal hout (ℓ := ℓ) (by
    intro e he' hkey
    have hkey' := hkey.trans (hk _ hw)
    have hem : e ∈ first :: group := by
      rcases List.mem_cons.mp (hcover e he' hkey') with rfl | ht
      · simp
      · rw [hgroup]
        exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨ht,decide_eq_true hkey'⟩)
    obtain ⟨hmin',htie⟩ := hmin e hem
    have hord := horder _ (hgmem _ hw) _ (hgmem _ hem)
    have hrev := horder _ (hgmem _ hem) _ (hgmem _ hw)
    exact ⟨hord.mp hmin',fun h => htie (le_antisymm hmin' (hrev.mpr h.ge))⟩)
  have hname : out.winner = shortestEdge G ℓ (edgePairKey G first) :=
    hwin.trans (congrArg (shortestEdge G ℓ) (hk _ hw))
  refine ⟨ha,?_⟩
  change out.finish G = _
  have ha' : out.anchor = first := ha
  have hc' : out.completed = completed := hc
  simp [RepresentativeGroupState.finish,ha',hc',hname,hloop]

/-- A leading self-loop class keeps the existing output and retains its anchor
until the next class begins. -/
theorem representativeLeadingLoop_finish {G : MGraph} {first : ℕ}
    (len : ℕ → ℕ) (edges completed : List ℕ)
    (hloop : G.tail first = G.head first) :
    let group := edges.takeWhile (fun e => decide (edgePairKey G e = edgePairKey G first))
    let out := group.foldl (RepresentativeGroupState.step G len)
      { RepresentativeGroupState.seed first with completed := completed }
    out.anchor = first ∧ out.finish G = completed := by
  let p := fun e => decide (edgePairKey G e = edgePairKey G first)
  have hfold (group : List ℕ) (s : RepresentativeGroupState) (ha : s.anchor = first)
      (hc : s.completed = completed) (hg : ∀ e ∈ group, p e = true) :
      (group.foldl (RepresentativeGroupState.step G len) s).anchor = first ∧
        (group.foldl (RepresentativeGroupState.step G len) s).completed = completed := by
    induction group generalizing s with
    | nil => exact ⟨ha,hc⟩
    | cons e rest ih =>
      have hpair : edgePairKey G s.anchor = edgePairKey G e := by
        rw [ha]
        exact (of_decide_eq_true (hg e (by simp))).symm
      apply ih (s.step G len e)
      · simpa [RepresentativeGroupState.step,hpair] using ha
      · simpa [RepresentativeGroupState.step,hpair] using hc
      · exact fun f hf => hg f (List.mem_cons_of_mem _ hf)
  obtain ⟨ha,hc⟩ := hfold (edges.takeWhile p)
    { RepresentativeGroupState.seed first with completed := completed } rfl rfl
    (fun e he => List.all_eq_true.mp List.all_takeWhile e he)
  refine ⟨ha,?_⟩
  rw [RepresentativeGroupState.finish, ha, hc]
  simp [edgePairKey,hloop]

/-- Completing the leading class reduces the fold to the remaining classes.
The saved prefix advances by one edge exactly for a non-loop class. -/
theorem representativeLeadingClass_split {G : MGraph} {vCap eCap first : ℕ}
    (len : ℕ → ℕ) (ℓ : ℕ → ℝ) (edges completed : List ℕ)
    (hfirst : first ∈ G.E)
    (he : first < eCap) (hv : (edgePairKey G first).2 < vCap)
    (hvalid : ∀ e ∈ edges, e < eCap ∧ (edgePairKey G e).2 < vCap)
    (hs : (first :: edges).Pairwise (fun e f => representativeSortKey G vCap eCap e ≤
      representativeSortKey G vCap eCap f))
    (hmem : ∀ e ∈ edges, e ∈ G.E)
    (hcover : ∀ e ∈ nonLoopEdges G, edgePairKey G e = edgePairKey G first →
      e ∈ first :: edges)
    (horder : ∀ e ∈ G.E, ∀ f ∈ G.E, len e ≤ len f ↔ ℓ e ≤ ℓ f) :
    let p := fun e => decide (edgePairKey G e = edgePairKey G first)
    let saved := if G.tail first = G.head first then completed
      else completed ++ [shortestEdge G ℓ (edgePairKey G first)]
    let seed := fun e => { RepresentativeGroupState.seed e with completed := saved }
    (edges.foldl (RepresentativeGroupState.step G len)
      { RepresentativeGroupState.seed first with completed := completed }).finish G =
      match edges.dropWhile p with
      | [] => saved
      | e :: rest => (rest.foldl (RepresentativeGroupState.step G len) (seed e)).finish G := by
  let p := fun e => decide (edgePairKey G e = edgePairKey G first)
  let done := edges.takeWhile p
  let start := { RepresentativeGroupState.seed first with completed := completed }
  let mid := done.foldl (RepresentativeGroupState.step G len) start
  have hmid : mid.anchor = first ∧ mid.finish G =
      (if G.tail first = G.head first then completed
        else completed ++ [shortestEdge G ℓ (edgePairKey G first)]) := by
    by_cases h : G.tail first = G.head first
    · simpa only [ite_eq_left h] using representativeLeadingLoop_finish len edges completed h
    · simpa only [ite_eq_right h] using
        representativeLeadingClass_finish len ℓ edges completed (Finset.mem_filter.mpr ⟨hfirst,h⟩)
          he hv hvalid hs hmem hcover horder
  have hsplit : done ++ edges.dropWhile p = edges := List.takeWhile_append_dropWhile
  dsimp only
  change (edges.foldl (RepresentativeGroupState.step G len) start).finish G =
    match edges.dropWhile p with
    | [] => _
    | e :: rest => _
  cases hrest : edges.dropWhile p with
  | nil =>
    rw [hrest,List.append_nil] at hsplit
    rw [← hsplit]
    exact hmid.2
  | cons e rest =>
    have hnext : edgePairKey G mid.anchor ≠ edgePairKey G e := by
      have hh := List.head?_dropWhile_not p edges
      rw [hrest] at hh
      have hn : ¬ edgePairKey G e = edgePairKey G first := by
        simpa [p] using hh
      exact fun h => hn (h.symm.trans (congrArg (edgePairKey G) hmid.1))
    rw [hrest] at hsplit
    rw [← hsplit,RepresentativeGroupState.fold_after_boundary G len start done rest e hnext]
    change (rest.foldl (RepresentativeGroupState.step G len)
      { RepresentativeGroupState.seed e with completed := mid.finish G }).finish G = _
    rw [hmid.2]

/-- A sorted list containing whole parallel classes emits exactly their
canonical shortest non-loop edges, after the previously saved prefix. -/
theorem representativeFold_mem {G : MGraph} {vCap eCap : ℕ}
    (len : ℕ → ℕ) (ℓ : ℕ → ℝ)
    (horder : ∀ e ∈ G.E, ∀ f ∈ G.E, len e ≤ len f ↔ ℓ e ≤ ℓ f)
    (input completed : List ℕ) (winner : ℕ)
    (hvalid : ∀ e ∈ input, e ∈ G.E ∧ e < eCap ∧ (edgePairKey G e).2 < vCap)
    (hs : input.Pairwise (fun e f => representativeSortKey G vCap eCap e ≤
      representativeSortKey G vCap eCap f))
    (hcover : ∀ a ∈ input, ∀ b ∈ nonLoopEdges G, edgePairKey G b = edgePairKey G a → b ∈ input) :
    winner ∈ (match input with
      | [] => completed
      | first :: edges => (edges.foldl (RepresentativeGroupState.step G len)
          { RepresentativeGroupState.seed first with completed := completed }).finish G) ↔
      winner ∈ completed ∨ ∃ e ∈ input, e ∈ nonLoopEdges G ∧
        winner = shortestEdge G ℓ (edgePairKey G e) := by
  cases input with
  | nil => simp
  | cons first edges =>
    let p := fun e => decide (edgePairKey G e = edgePairKey G first)
    let saved := if G.tail first = G.head first then completed
      else completed ++ [shortestEdge G ℓ (edgePairKey G first)]
    have hf := hvalid first (by simp)
    have ht (e : ℕ) (he : e ∈ edges) := hvalid e (List.mem_cons_of_mem _ he)
    have hd (e : ℕ) := representativeClass_mem_dropWhile edges hf.2.1 hf.2.2
      (fun e he => (ht e he).2) hs e
    have hsplit := representativeLeadingClass_split len ℓ edges completed hf.1 hf.2.1 hf.2.2
      (fun e he => (ht e he).2) hs (fun e he => (ht e he).1)
      (hcover first (by simp)) horder
    have hsorted := (List.pairwise_cons.mp hs).2.sublist (List.dropWhile_sublist p)
    have htail e (he : e ∈ edges.dropWhile p) := ht e ((hd e).mp he).1
    have hwhole a (ha : a ∈ edges.dropWhile p) b (hb : b ∈ nonLoopEdges G)
        (hk : edgePairKey G b = edgePairKey G a) : b ∈ edges.dropWhile p := by
      have hne : edgePairKey G b ≠ edgePairKey G first :=
        fun h => ((hd a).mp ha).2 (hk.symm.trans h)
      rcases List.mem_cons.mp (hcover a (List.mem_cons_of_mem _ ((hd a).mp ha).1) b hb hk) with h | h
      · exact False.elim (hne (congrArg (edgePairKey G) h))
      · exact (hd b).mpr ⟨h,hne⟩
    have hshort : (edges.dropWhile p).length < (first :: edges).length :=
      Nat.lt_succ_of_le (List.dropWhile_sublist p).length_le
    have hr := representativeFold_mem len ℓ horder (edges.dropWhile p) saved winner htail hsorted hwhole
    change winner ∈ (edges.foldl (RepresentativeGroupState.step G len)
      { RepresentativeGroupState.seed first with completed := completed }).finish G ↔ _
    rw [hsplit]
    change (winner ∈ (match edges.dropWhile p with
      | [] => saved
      | e :: rest => (rest.foldl (RepresentativeGroupState.step G len)
          { RepresentativeGroupState.seed e with completed := saved }).finish G)) ↔ _
    rw [hr]
    have hsave : winner ∈ saved ↔ winner ∈ completed ∨
        first ∈ nonLoopEdges G ∧ winner = shortestEdge G ℓ (edgePairKey G first) := by
      by_cases h : G.tail first = G.head first
      · simp [saved,h,nonLoopEdges]
      · simp [saved,h,nonLoopEdges,hf.1]
    rw [hsave]
    constructor
    · rintro ((hc | ⟨hn,hw⟩) | ⟨e,he,hn,hw⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨first,by simp,hn,hw⟩
      · exact Or.inr ⟨e,List.mem_cons_of_mem _ ((hd e).mp he).1,hn,hw⟩
    · rintro (hc | ⟨e,he,hn,hw⟩)
      · exact Or.inl (Or.inl hc)
      · by_cases hk : edgePairKey G e = edgePairKey G first
        · have hfnon : first ∈ nonLoopEdges G := by
            refine Finset.mem_filter.mpr ⟨hf.1,?_⟩
            intro hloop
            have hends : (edgePairKey G e).1 = (edgePairKey G e).2 := by
              rw [hk]
              simp [edgePairKey,hloop]
            apply (Finset.mem_filter.mp hn).2
            rcases le_total (G.tail e) (G.head e) with h | h
            · simpa [edgePairKey,min_eq_left h,max_eq_right h] using hends
            · exact (show G.head e = G.tail e by
                simpa [edgePairKey,min_eq_right h,max_eq_left h] using hends).symm
          exact Or.inl (Or.inr ⟨hfnon,by simpa only [hk] using hw⟩)
        · rcases List.mem_cons.mp he with rfl | he
          · exact False.elim (hk rfl)
          · exact Or.inr ⟨e,(hd e).mpr ⟨he,hk⟩,hn,hw⟩
termination_by input.length

/-- The fold appends a representative only once, since later classes have distinct keys. -/
theorem representativeFold_nodup {G : MGraph} {vCap eCap : ℕ}
    (len : ℕ → ℕ) (ℓ : ℕ → ℝ)
    (horder : ∀ e ∈ G.E, ∀ f ∈ G.E, len e ≤ len f ↔ ℓ e ≤ ℓ f)
    (input completed : List ℕ) (hc : completed.Nodup)
    (hdis : ∀ e ∈ input, e ∈ nonLoopEdges G →
      shortestEdge G ℓ (edgePairKey G e) ∉ completed)
    (hvalid : ∀ e ∈ input, e ∈ G.E ∧ e < eCap ∧ (edgePairKey G e).2 < vCap)
    (hs : input.Pairwise (fun e f => representativeSortKey G vCap eCap e ≤
      representativeSortKey G vCap eCap f))
    (hcover : ∀ a ∈ input, ∀ b ∈ nonLoopEdges G, edgePairKey G b = edgePairKey G a → b ∈ input) :
    (match input with
      | [] => completed
      | first :: edges => (edges.foldl (RepresentativeGroupState.step G len)
          { RepresentativeGroupState.seed first with completed := completed }).finish G).Nodup := by
  cases input with
  | nil => exact hc
  | cons first edges =>
    let p := fun e => decide (edgePairKey G e = edgePairKey G first)
    let saved := if G.tail first = G.head first then completed
      else completed ++ [shortestEdge G ℓ (edgePairKey G first)]
    have hf := hvalid first (by simp)
    have ht e (he : e ∈ edges) := hvalid e (List.mem_cons_of_mem _ he)
    have hd e := representativeClass_mem_dropWhile edges hf.2.1 hf.2.2
      (fun e he => (ht e he).2) hs e
    have hsplit := representativeLeadingClass_split len ℓ edges completed hf.1 hf.2.1 hf.2.2
      (fun e he => (ht e he).2) hs (fun e he => (ht e he).1)
      (hcover first (by simp)) horder
    have hsaved : saved.Nodup := by
      by_cases h : G.tail first = G.head first
      · simpa [saved,h] using hc
      · have hn : first ∈ nonLoopEdges G := Finset.mem_filter.mpr ⟨hf.1,h⟩
        simp only [saved,ite_eq_right h,List.nodup_append,hc,List.nodup_singleton,true_and]
        intro a ha b hb hab
        exact hdis first (by simp) hn ((hab.trans (List.mem_singleton.mp hb)) ▸ ha)
    have hds e (he : e ∈ edges.dropWhile p) (hn : e ∈ nonLoopEdges G) :
        shortestEdge G ℓ (edgePairKey G e) ∉ saved := by
      have hold := hdis e (List.mem_cons_of_mem _ ((hd e).mp he).1) hn
      by_cases h : G.tail first = G.head first
      · simpa [saved,h] using hold
      · have hn' : first ∈ nonLoopEdges G := Finset.mem_filter.mpr ⟨hf.1,h⟩
        have hne : shortestEdge G ℓ (edgePairKey G e) ≠
            shortestEdge G ℓ (edgePairKey G first) := by
          intro hkey
          exact ((hd e).mp he).2 ((shortestEdge_spec (ℓ := ℓ) hn).2.1.symm.trans
            ((congrArg (edgePairKey G) hkey).trans (shortestEdge_spec (ℓ := ℓ) hn').2.1))
        simp [saved,h,hold,hne]
    have hwhole a (ha : a ∈ edges.dropWhile p) b (hb : b ∈ nonLoopEdges G)
        (hk : edgePairKey G b = edgePairKey G a) : b ∈ edges.dropWhile p := by
      have hne : edgePairKey G b ≠ edgePairKey G first :=
        fun h => ((hd a).mp ha).2 (hk.symm.trans h)
      rcases List.mem_cons.mp (hcover a (List.mem_cons_of_mem _ ((hd a).mp ha).1) b hb hk) with h | h
      · exact False.elim (hne (congrArg (edgePairKey G) h))
      · exact (hd b).mpr ⟨h,hne⟩
    have hshort : (edges.dropWhile p).length < (first :: edges).length :=
      Nat.lt_succ_of_le (List.dropWhile_sublist p).length_le
    change ((edges.foldl (RepresentativeGroupState.step G len)
      { RepresentativeGroupState.seed first with completed := completed }).finish G).Nodup
    rw [hsplit]
    exact representativeFold_nodup len ℓ horder (edges.dropWhile p) saved hsaved hds
      (fun e he => ht e ((hd e).mp he).1)
      ((List.pairwise_cons.mp hs).2.sublist (List.dropWhile_sublist p)) hwhole
termination_by input.length

/-- On a sorted enumeration of the input graph, the group fold enumerates
all edges of the representative graph exactly once. -/
theorem representativeFold_enumerates {G : MGraph} {vCap eCap : ℕ}
    (len : ℕ → ℕ) (ℓ : ℕ → ℝ) (input : List ℕ)
    (horder : ∀ e ∈ G.E, ∀ f ∈ G.E, len e ≤ len f ↔ ℓ e ≤ ℓ f)
    (hmem : ∀ e, e ∈ input ↔ e ∈ G.E)
    (hvalid : ∀ e ∈ G.E, e < eCap ∧ (edgePairKey G e).2 < vCap)
    (hs : input.Pairwise (fun e f => representativeSortKey G vCap eCap e ≤
      representativeSortKey G vCap eCap f)) :
    let output := match input with
      | [] => []
      | first :: edges => (edges.foldl (RepresentativeGroupState.step G len)
          (.seed first)).finish G
    output.Nodup ∧ ∀ e, e ∈ output ↔ e ∈ (representativeGraph G ℓ).E := by
  have hv e (he : e ∈ input) := And.intro ((hmem e).mp he) (hvalid e ((hmem e).mp he))
  have hcover : ∀ a ∈ input, ∀ b ∈ nonLoopEdges G, edgePairKey G b = edgePairKey G a → b ∈ input :=
    fun _ _ b hb _ => (hmem b).mpr (Finset.mem_filter.mp hb).1
  have hn := representativeFold_nodup len ℓ horder input [] List.nodup_nil
    (fun _ _ _ => List.not_mem_nil) hv hs hcover
  have hm e := representativeFold_mem len ℓ horder input [] e hv hs hcover
  refine ⟨?_,?_⟩
  · cases input <;> exact hn
  · intro e
    have he : e ∈ (representativeGraph G ℓ).E ↔
        ∃ f ∈ input, f ∈ nonLoopEdges G ∧ e = shortestEdge G ℓ (edgePairKey G f) := by
      constructor
      · intro he
        obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp he
        obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hk
        exact ⟨f,(hmem f).mpr (Finset.mem_filter.mp hf).1,hf,rfl⟩
      · rintro ⟨f,_,hf,rfl⟩
        exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hf)
    rw [he]
    cases input <;> simpa only [List.not_mem_nil,false_or,RepresentativeGroupState.seed] using hm e

/-- The shared word sorter returns a sorted enumeration of the edge names
when its input consists of the encoded live edges. -/
theorem representativeSortedKeys_decode {G : MGraph} {vCap eCap : ℕ}
    (edges sorted : List ℕ) (hperm : sorted.Perm (edges.map (representativeSortKey G vCap eCap)))
    (hs : sorted.Pairwise (· ≤ ·))
    (hvalid : ∀ e ∈ edges, e < eCap ∧ (edgePairKey G e).2 < vCap) :
    ∃ names : List ℕ, names.Perm edges ∧
      names.map (representativeSortKey G vCap eCap) = sorted ∧
      names.Pairwise (fun e f => representativeSortKey G vCap eCap e ≤
        representativeSortKey G vCap eCap f) := by
  let key := representativeSortKey G vCap eCap
  let decode := fun k => k % eCap
  have hdecode e (he : e ∈ edges) : decode (key e) = e :=
    (representativeSortKey_decode G vCap eCap e (hvalid e he).1 (hvalid e he).2).1
  have hback : (edges.map key).map decode = edges := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id edges]
    exact List.map_congr_left hdecode
  have hnames := hperm.map decode
  change (sorted.map decode).Perm ((edges.map key).map decode) at hnames
  rw [hback] at hnames
  have hround : (sorted.map decode).map key = sorted := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id sorted]
    apply List.map_congr_left
    intro k hk
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp (hperm.mem_iff.mp hk)
    change key (decode (key e)) = key e
    rw [hdecode e he]
  refine ⟨sorted.map decode,hnames,hround,?_⟩
  apply List.pairwise_map.mp
  rwa [hround]

/-- Scanning the sorted live-edge keys writes a duplicate-free enumeration
of the representative graph and returns its edge count in register 17. -/
theorem representativeGroupScan_enumerates {w entry g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} (st : State) (ℓ : ℕ → ℝ)
    (src dst lengths L : ℕ) (input : List ℕ)
    (hcmp : MeetsContract w p entry (unsignedLessContract w 4))
    (hG : DynGraphAt st.mem g vCap eCap G)
    (hmem : ∀ e, e ∈ input ↔ e ∈ G.E)
    (hsorted : input.Pairwise (fun e f => representativeSortKey G vCap eCap e ≤
      representativeSortKey G vCap eCap f))
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap) (h6 : st.regs 6 = src)
    (h7 : st.regs 7 = input.length) (h13 : st.regs 13 = lengths)
    (h14 : st.regs 14 = L) (h16 : st.regs 16 = dst)
    (hkeys : ListAt st.mem src (input.map (representativeSortKey G vCap eCap)))
    (hw : 1 < 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hs : src+input.length < 2^w) (hd : dst+input.length < 2^w)
    (hsg : src+input.length ≤ dst ∨ dst+input.length ≤ src)
    (hdg : g+dynGraphSize vCap eCap ≤ dst ∨ dst+input.length ≤ g)
    (hlen : ∀ f ∈ G.E, lengths+f*L+L < 2^w ∧ Valid st.mem (lengths+f*L) 4 L ∧
      (lengths+f*L+L ≤ dst ∨ dst+input.length ≤ lengths+f*L))
    (horder : ∀ e ∈ G.E, ∀ f ∈ G.E,
      unsignedVal st.mem (lengths+e*L) 4 L ≤ unsignedVal st.mem (lengths+f*L) 4 L ↔ ℓ e ≤ ℓ f) :
    ∃ out cost names, Runs w p ω (representativeGroupScan entry) st .normal out cost ∧
      ListAt out.mem dst names ∧ names.Nodup ∧
      (∀ e, e ∈ names ↔ e ∈ (representativeGraph G ℓ).E) ∧
      out.regs 17 = names.length ∧
      (∀ a, a < dst ∨ dst+input.length ≤ a → out.mem a = st.mem a) ∧
      (∀ r, representativeGroupPreserves r → out.regs r = st.regs r) ∧
      cost ≤ input.length*(41*L+57)+58 := by
  have hvalid e (he : e ∈ G.E) :
      e < eCap ∧ (edgePairKey G e).2 < vCap :=
    let h := representativeLiveKey_bounds hG he hcap
    ⟨h.1,h.2.1⟩
  have henum := representativeFold_enumerates _ ℓ input horder hmem hvalid hsorted
  cases input with
  | nil =>
    obtain ⟨out,hr,hm,hcount,hkeep⟩ := representativeGroupScan_empty_runs
      (p := p) (ω := ω) (entry := entry) st h7 hw
    exact ⟨out,6,[],hr,fun _ h => False.elim (Nat.not_lt_zero _ h),henum.1,henum.2,
      hcount,fun a _ => congrFun hm a,
      fun r hr' => hkeep r (by unfold representativeGroupPreserves at hr'; omega),by simp⟩
  | cons first edges =>
    obtain ⟨out,c,hr,hlist,hcount,hframe,hkeep,hcost⟩ :=
      representativeGroupScan_cons_runs (ω := ω) st first src dst lengths L edges hcmp hG
        ((hmem first).mp (by simp))
        (fun e he => (hmem e).mp (List.mem_cons_of_mem _ he))
        h4 h5 h6 h7 h13 h14 h16 hkeys hw hcap hs hd hsg hdg hlen
    refine ⟨out,c,_,hr,hlist,henum.1,henum.2,hcount,hframe,hkeep,?_⟩
    simp only [List.length_cons]
    exact hcost.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.le_succ _)) _)

/-- For positive lengths in a common fixed-point format, the scan's
unsigned comparison agrees with the comparison of decoded lengths. -/
theorem representativeLength_order {mem : ℕ → ℕ} {a b L P : ℕ}
    (ha : Valid mem a 4 L) (hb : Valid mem b 4 L)
    (hpa : 0 < fixVal mem a 4 L P) (hpb : 0 < fixVal mem b 4 L P) :
    unsignedVal mem a 4 L ≤ unsignedVal mem b 4 L ↔
      fixVal mem a 4 L P ≤ fixVal mem b 4 L P := by
  have hp : (0 : ℝ) < 2^P := pow_pos (by norm_num) _
  have decode (x : ℕ) (hv : Valid mem x 4 L) (hx : 0 < fixVal mem x 4 L P) :
      intVal mem x 4 L = (unsignedVal mem x 4 L : ℤ) := by
    have hpos : (0 : ℤ) < intVal mem x 4 L := by
      have hreal : (0 : ℝ) < (intVal mem x 4 L : ℝ) :=
        (div_pos_iff_of_pos_right hp).mp hx
      exact_mod_cast hreal
    have hu := unsignedVal_lt hv
    unfold intVal signedVal at hpos ⊢
    by_cases h : capacity 4 L ≤ 2 * unsignedVal mem x 4 L
    · rw [ite_eq_left h] at hpos
      omega
    · simp [h]
  rw [fixVal,fixVal,div_le_div_iff_of_pos_right hp,decode a ha hpa,decode b hb hpb]
  exact_mod_cast (Iff.rfl : unsignedVal mem a 4 L ≤ unsignedVal mem b 4 L ↔ _)

end MinCostFlow.LastLevelProgram
