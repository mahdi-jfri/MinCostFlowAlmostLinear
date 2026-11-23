module

public import MinCostFlow.LastLevelProgram.BranchStretch
public import MinCostFlow.LastLevelProgram.RepresentativeScan
import WordRAM.Tactic

/-!
# Finding the representative stretch index

The scan for Definition 5.8 (pages 19–20) compares endpoint classes in
the compact representative edge order. It keeps the unit-block index
when no representative matches.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Compare the next representative key with the source key, recording
the compact position when the endpoint classes agree. -/
@[expose] def stretchIndexScanStep : Stmt :=
  .cond (representativeSameClass
      (.load (.bin .add (.reg 6) (.reg 8))) (.reg 9))
    (.assign 10 (.reg 8)) .nop

/-- A scan step changes only the result register, and only on a match. -/
theorem stretchIndexScanStep_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (keys i candidate source cap : ℕ)
    (hkeys : st.regs 6 = keys) (hi : st.regs 8 = i)
    (hsource : st.regs 9 = source) (hcap : st.regs 5 = cap)
    (hread : st.mem (keys+i) = candidate)
    (hfit : keys+i < 2^w) (hw : 1 < 2^w)
    (hcandidate : candidate < 2^w) (hsourceWord : source < 2^w) :
    ∃ out cost, Runs w p ω stretchIndexScanStep st .normal out cost ∧
      out.mem = st.mem ∧
      out.regs 10 = (if candidate/cap = source/cap then i else st.regs 10) ∧
      (∀ r, r ≠ 10 → out.regs r = st.regs r) ∧ cost ≤ 17 := by
  have hdiv₁ := (Nat.div_le_self candidate cap).trans_lt hcandidate
  have hdiv₂ := (Nat.div_le_self source cap).trans_lt hsourceWord
  have hz : 0 < 2^w := by omega
  by_cases he : candidate/cap = source/cap
  · let out := {st with regs := Function.update st.regs 10 i}
    have ht : (representativeSameClass
        (.load (.bin .add (.reg 6) (.reg 8))) (.reg 9)).eval w st = some 1 := by
      simp [representativeSameClass,representativeClassExpr,Expr.eval,BinOp.eval,
        hkeys,hi,hsource,hcap,hread,hfit,hw,hdiv₂,he]
    have ha : Runs w p ω (.assign 10 (.reg 8)) st .normal out 2 :=
      runs_assign_iff.mpr ⟨i,by simp [Expr.eval,hi],rfl,rfl,rfl⟩
    exact ⟨out,13,runs_cond_iff.mpr ⟨1,2,ht,by simpa using ha,rfl⟩,rfl,
      by simp [out,he],fun r hr => Function.update_of_ne hr ..,by decide⟩
  · have ht : (representativeSameClass
        (.load (.bin .add (.reg 6) (.reg 8))) (.reg 9)).eval w st = some 0 := by
      simp [representativeSameClass,representativeClassExpr,Expr.eval,BinOp.eval,
        hkeys,hi,hsource,hcap,hread,hfit,hz,hdiv₁,hdiv₂,he]
    exact ⟨st,12,runs_cond_iff.mpr ⟨0,1,ht,by simp [runs_nop_iff],rfl⟩,rfl,
      by simp [he],fun _ _ => rfl,by decide⟩

/-- Scan the representative key table once. Register ten starts at
the sentinel, which is the table length. -/
@[expose] def stretchIndexScan : Stmt :=
  forRange 8 (.const 0) (.reg 7) stretchIndexScanStep

/-- The scan returns the unique matching position, or the sentinel
when the source class has no representative. -/
theorem stretchIndexScan_triple {w : ℕ} {p : Program} (st : State)
    (keys m cap source target : ℕ)
    (hkeys : st.regs 6 = keys) (hm : st.regs 7 = m)
    (hcap : st.regs 5 = cap) (hsource : st.regs 9 = source) (hinit : st.regs 10 = m)
    (hw : 1 < 2^w) (hfit : keys+m < 2^w) (hword : source < 2^w)
    (htarget : target ≤ m)
    (hread : ∀ i < m, st.mem (keys+i) < 2^w ∧
      (st.mem (keys+i)/cap = source/cap ↔ target = i)) :
    Triple w p (fun s => s = st) stretchIndexScan
      (normalPost fun out => out.mem = st.mem ∧ out.regs 10 = target ∧
        ∀ r, r ≠ 8 → r ≠ 10 → out.regs r = st.regs r)
      (fun _ => 26*m+7) := by
  let Inv := fun i (s : State) =>
    (∀ r, r ≠ 8 → r ≠ 10 → s.regs r = st.regs r) ∧ s.regs 8 = i ∧ s.mem = st.mem ∧
    s.regs 10 = (if target < i then target else m)
  have loop := Triple.forRange_const (p := p) (r := 8) (lo := .const 0) (hi := .reg 7)
    (body := stretchIndexScanStep) (P := fun s => s = st)
    (Inv := Inv) 17 0 m (Nat.zero_le _) hw (fun _ => by omega)
    (fun s hs => by
      subst s
      refine ⟨by simp [Expr.eval,show 0 < 2^w by omega],?_⟩
      exact ⟨fun _ hr _ => Function.update_of_ne hr ..,by simp,rfl,by
        simpa only [Nat.not_lt_zero,ite_false] using
          (Function.update_of_ne (show (10 : ℕ) ≠ 8 by decide) 0 st.regs).trans hinit⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval,(h.1 7 (by decide) (by decide)).trans hm])
    (fun i _ hi => by
      intro mid ω ⟨hregs,hindex,hmem,hres⟩
      obtain ⟨hkey,hmatch⟩ := hread i hi
      obtain ⟨out,c,hr,hmem',hres',hkeep,hcost⟩ :=
        stretchIndexScanStep_runs mid keys i (st.mem (keys+i)) source cap
          ((hregs 6 (by decide) (by decide)).trans hkeys) hindex
          ((hregs 9 (by decide) (by decide)).trans hsource)
          ((hregs 5 (by decide) (by decide)).trans hcap) (congrFun hmem _)
          (by omega) hw hkey hword
      refine ⟨.normal,out,c,hr,⟨⟨?_,by simp,hmem'.trans hmem,?_⟩,
        (hkeep 8 (by decide)).trans hindex⟩,hcost⟩
      · intro r hr8 hr10
        exact (Function.update_of_ne hr8 ..).trans ((hkeep r hr10).trans (hregs r hr8 hr10))
      · change Function.update out.regs 8 (i+1) 10 = _
        simp only [Function.update_of_ne (show (10 : ℕ) ≠ 8 by decide),hres',hmatch,hres]
        by_cases he : target = i
        · subst target
          simp
        · have hlt : target < i+1 ↔ target < i := by omega
          simp [he,hlt])
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o out h
    cases o with
    | normal =>
      refine ⟨h.2.2.1,?_,h.1⟩
      by_cases ht : target < m
      · simpa [ht] using h.2.2.2
      · simpa [ht,show m = target by omega] using h.2.2.2
    | returned _ => exact False.elim h
  · intro _ _
    simp [Expr.size_reg,Expr.size_const,Nat.mul_comm]

/-- For the representative key table, the scan returns the model's
source index for each live edge, including the loop sentinel. -/
theorem stretchIndexScan_graph_triple {w : ℕ} {p : Program} (st : State)
    (G : MGraph) (ℓ : ℕ → ℝ) (keys vCap eCap e : ℕ)
    (hG : G.IsValid) (he : e ∈ G.E)
    (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ f ∈ G.E, f < eCap)
    (hkeys : st.regs 6 = keys) (hcap : st.regs 5 = eCap)
    (hsource : st.regs 9 = representativeSortKey G vCap eCap e)
    (hw : 1 < 2^w) (hcapFit : vCap*vCap*eCap ≤ 2^w) :
    let H := representativeGraph G ℓ
    st.regs 7 = H.m → st.regs 10 = H.m → keys+H.m < 2^w →
    (∀ i < H.m, st.mem (keys+i) = representativeSortKey G vCap eCap (edgeName H i)) →
    Triple w p (fun s => s = st) stretchIndexScan
      (normalPost fun out => out.mem = st.mem ∧ out.regs 10 = branchStretchIndex G ℓ e ∧
        ∀ r, r ≠ 8 → r ≠ 10 → out.regs r = st.regs r)
      (fun _ => 26*H.m+7) := by
  intro H hm hinit hfit hread
  have hword (f : ℕ) (hf : f ∈ G.E) : representativeSortKey G vCap eCap f < 2^w := by
    obtain ⟨ht,hh⟩ := hG f hf
    exact (representativeSortKey_lt G vCap eCap f (hV _ ht)
      (hV _ hh) (hE f hf)).trans_le hcapFit
  refine stretchIndexScan_triple st keys H.m eCap _ _ hkeys hm hcap hsource hinit
    hw hfit (hword e he) (branchStretchIndex_le G ℓ e) ?_
  intro i hi
  have hf := (representativeGraph_subgraph hG ℓ).2.1 (edgeName_mem hi)
  rw [hread i hi]
  exact ⟨hword _ hf,branchStretchIndex_key_iff ℓ he hi hG hV hE⟩

/-- Move the four scan arguments into the loop registers and seed
the answer with the sentinel. -/
@[expose] def stretchIndexScanSetup : Stmt :=
  .assign 5 (.reg 0) ;;
  .assign 6 (.reg 1) ;;
  .assign 7 (.reg 2) ;;
  .assign 9 (.reg 3) ;;
  .assign 10 (.reg 2)

/-- The setup only reads argument registers. -/
theorem stretchIndexScanSetup_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (cap keys m source pos : ℕ) (mem : ℕ → ℕ) :
    ∃ out cost, Runs w p ω stretchIndexScanSetup
      (startState [cap,keys,m,source] mem pos) .normal out cost ∧
      out.mem = mem ∧ out.regs 5 = cap ∧ out.regs 6 = keys ∧ out.regs 7 = m ∧
      out.regs 9 = source ∧ out.regs 10 = m ∧ cost ≤ 14 := by
  have run : ∃ o out cost, Runs w p ω stretchIndexScanSetup
      (startState [cap,keys,m,source] mem pos) o out cost ∧
      (o = .normal ∧ out.mem = mem ∧ out.regs 5 = cap ∧ out.regs 6 = keys ∧
        out.regs 7 = m ∧ out.regs 9 = source ∧ out.regs 10 = m) ∧ cost ≤ 14 := by
    apply runs_start_le
    unfold stretchIndexScanSetup
    wram_run
    · simp [startState]
    · wram_cost
  obtain ⟨_,out,cost,hr,⟨rfl,hout⟩,hc⟩ := run
  exact ⟨out,cost,hr,hout.1,hout.2.1,hout.2.2.1,hout.2.2.2.1,
    hout.2.2.2.2.1,hout.2.2.2.2.2,hc⟩

/-- Find one source index and return it without writing memory. -/
@[expose] def stretchIndexScanBody : Stmt :=
  .seq stretchIndexScanSetup (.seq stretchIndexScan (.ret (.reg 10)))

/-- The installed scan accepts the compact key table and one source key.
Its result is suitable for the original-edge index table. -/
theorem stretchIndexScan_meetsContract {w entry vCap eCap : ℕ} {p : Program}
    (G : MGraph) (ℓ : ℕ → ℝ) (e keys : ℕ)
    (hp : p.procs[entry]? = some stretchIndexScanBody)
    (hG : G.IsValid) (he : e ∈ G.E)
    (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ f ∈ G.E, f < eCap)
    (hw : 1 < 2^w) (hcap : vCap*vCap*eCap ≤ 2^w) :
    let H := representativeGraph G ℓ
    MeetsContract w p entry
      { pre := fun args mem =>
          args = [eCap,keys,H.m,representativeSortKey G vCap eCap e] ∧
          keys+H.m < 2^w ∧
          ∀ i < H.m, mem (keys+i) = representativeSortKey G vCap eCap (edgeName H i)
        post := fun _ mem ret out => ret = branchStretchIndex G ℓ e ∧ out = mem
        cost := fun _ _ => 26*H.m+25 } := by
  intro H
  apply meetsContract_of_runs hp
  intro args mem pos ω _ ⟨hargs,hfit,hkeys⟩
  change args = _ at hargs
  subst args
  obtain ⟨ready,c,hs,hmem,h5,h6,h7,h9,h10,hcost⟩ :=
    stretchIndexScanSetup_runs (p := p) (w := w) (ω := ω)
      eCap keys H.m (representativeSortKey G vCap eCap e) pos mem
  have ht := stretchIndexScan_graph_triple (p := p) ready G ℓ keys vCap eCap e
    hG he hV hE h6 h5 h9 hw hcap h7 h10 hfit (hmem.symm ▸ hkeys)
  obtain ⟨o,out,k,hr,ho,hk⟩ := ht.runs ω rfl
  change k ≤ 26*H.m+7 at hk
  cases o with
  | returned _ => exact False.elim ho
  | normal =>
    obtain ⟨hmem',hres,_⟩ := ho
    have hret : Runs w p ω (.ret (.reg 10)) out (.returned (branchStretchIndex G ℓ e)) out 2 :=
      runs_ret_iff.mpr ⟨_,by simp [Expr.eval,hres],rfl,rfl,rfl⟩
    have htail := runs_seq_iff.mpr (Or.inr ⟨out,k,2,hr,hret,rfl⟩)
    exact ⟨_,out,c+(k+2+1)+1,runs_seq_iff.mpr (Or.inr ⟨ready,c,_,hs,htail,rfl⟩),
      ⟨rfl,hmem'.trans hmem⟩,by change _ ≤ 26*H.m+25; omega⟩

/-- Look up one original edge's class and write its compact index. -/
@[expose] def writeStretchIndexStep (entry : ℕ) : Stmt :=
  .seq (.call 140 entry [.reg 114,.reg 138,.reg 73,.load (.bin .add (.reg 136) (.reg 139))])
    (.store (.bin .add (.reg 131) (.reg 139)) (.reg 140))

/-- One iteration writes the model index in the original edge order. -/
theorem writeStretchIndexStep_runs {w entry vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (ℓ : ℕ → ℝ)
    (keys source dst i : ℕ) (hi : i < G.m)
    (hp : p.procs[entry]? = some stretchIndexScanBody) (hG : G.IsValid)
    (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hw : 1 < 2^w) (hcap : vCap*vCap*eCap ≤ 2^w) (heCap : eCap < 2^w)
    (h114 : st.regs 114 = eCap) (h138 : st.regs 138 = keys)
    (h136 : st.regs 136 = source) (h131 : st.regs 131 = dst) (h139 : st.regs 139 = i)
    (hsource : source+i < 2^w) (hdst : dst+i < 2^w)
    (hread : st.mem (source+i) = representativeSortKey G vCap eCap (edgeName G i)) :
    let H := representativeGraph G ℓ
    st.regs 73 = H.m → keys+H.m < 2^w →
    (∀ j < H.m, st.mem (keys+j) = representativeSortKey G vCap eCap (edgeName H j)) →
    ∃ out cost, Runs w p ω (writeStretchIndexStep entry) st .normal out cost ∧
      out.mem = Function.update st.mem (dst+i) (branchStretchIndex G ℓ (edgeName G i)) ∧
      (∀ r, r ≠ 140 → out.regs r = st.regs r) ∧ cost ≤ 26*H.m+39 := by
  intro H h73 hfit hkeys
  let e := edgeName G i
  let key := representativeSortKey G vCap eCap e
  have he : e ∈ G.E := edgeName_mem hi
  obtain ⟨ht,hh⟩ := hG e he
  have hk : key < 2^w :=
    (representativeSortKey_lt G vCap eCap e (hV _ ht) (hV _ hh) (hE _ he)).trans_le hcap
  have ha : evalArgs w st [.reg 114,.reg 138,.reg 73,.load (.bin .add (.reg 136) (.reg 139))] =
      some [eCap,keys,H.m,key] := by
    simp [evalArgs,Expr.eval,BinOp.eval,h114,h138,h73,h136,h139,hsource,hread,key,e]
  have hwords : ∀ a ∈ [eCap,keys,H.m,key], a < 2^w := by
    intro a ha'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha'
    rcases ha' with rfl | rfl | rfl | rfl
    · exact heCap
    · omega
    · omega
    · exact hk
  obtain ⟨mid,c,ret,hr,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 140)
      (stretchIndexScan_meetsContract G ℓ e keys hp hG he hV hE hw hcap)
      ha hwords ⟨rfl,hfit,hkeys⟩ ω
  obtain ⟨hvalue,hmem⟩ := hpost
  let out := {mid with mem := Function.update mid.mem (dst+i) ret}
  have hs : Runs w p ω (.store (.bin .add (.reg 131) (.reg 139)) (.reg 140))
      mid .normal out 5 :=
    runs_store_iff.mpr ⟨dst+i,ret,by
      simp [Expr.eval,BinOp.eval,(hregs 131 (by decide)).trans h131,
        (hregs 139 (by decide)).trans h139,hdst],by simp [Expr.eval,hret],rfl,rfl,rfl⟩
  change c ≤ 7+(26*H.m+25)+1 at hcost
  exact ⟨out,c+6,runs_seq_iff.mpr (Or.inr ⟨mid,c,5,hr,hs,by omega⟩),
    by simp only [out,hmem,hvalue,e],hregs,by omega⟩

/-- Materialize the original edge-to-stretch index table. -/
@[expose] def writeStretchIndices (entry : ℕ) : Stmt :=
  forRange 139 (.const 0) (.reg 133) (writeStretchIndexStep entry)

/-- The original edge loop fills the index table and preserves both key
arrays. Its cost is linear in the product of the two live edge counts. -/
theorem writeStretchIndices_triple {w entry vCap eCap : ℕ}
    {p : Program} (st : State) (G : MGraph) (ℓ : ℕ → ℝ) (keys source dst : ℕ)
    (hp : p.procs[entry]? = some stretchIndexScanBody) (hG : G.IsValid)
    (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hw : 1 < 2^w) (hcap : vCap*vCap*eCap ≤ 2^w) (heCap : eCap < 2^w)
    (h114 : st.regs 114 = eCap) (h138 : st.regs 138 = keys)
    (h136 : st.regs 136 = source) (h131 : st.regs 131 = dst)
    (h133 : st.regs 133 = G.m)
    (hsrc : source+G.m < 2^w) (hdst : dst+G.m < 2^w)
    (hsrcSep : source+G.m ≤ dst ∨ dst+G.m ≤ source)
    (hread : ∀ i < G.m, st.mem (source+i) = representativeSortKey G vCap eCap (edgeName G i)) :
    let H := representativeGraph G ℓ
    st.regs 73 = H.m → keys+H.m < 2^w →
    (keys+H.m ≤ dst ∨ dst+G.m ≤ keys) →
    (∀ j < H.m, st.mem (keys+j) = representativeSortKey G vCap eCap (edgeName H j)) →
    Triple w p (fun s => s = st) (writeStretchIndices entry)
      (normalPost fun out =>
        (∀ i < G.m, out.mem (dst+i) = branchStretchIndex G ℓ (edgeName G i)) ∧
        (∀ a, a < dst ∨ dst+G.m ≤ a → out.mem a = st.mem a) ∧
        ∀ r, r ≠ 139 → r ≠ 140 → out.regs r = st.regs r)
      (fun _ => (26*H.m+48)*G.m+7) := by
  intro H h73 hfit hsep hkeys
  let Inv := fun i (s : State) =>
    (∀ r, r ≠ 139 → r ≠ 140 → s.regs r = st.regs r) ∧ s.regs 139 = i ∧
    (∀ j < i, s.mem (dst+j) = branchStretchIndex G ℓ (edgeName G j)) ∧
    ∀ a, a < dst ∨ dst+G.m ≤ a → s.mem a = st.mem a
  have loop := Triple.forRange_const (p := p) (r := 139) (lo := .const 0) (hi := .reg 133)
    (body := writeStretchIndexStep entry) (P := fun s => s = st)
    (Inv := Inv) (26*H.m+39) 0 G.m (Nat.zero_le _) hw (fun _ => by omega)
    (fun s hs => by
      subst s
      refine ⟨by simp [Expr.eval,show 0 < 2^w by omega],?_⟩
      exact ⟨fun _ hr _ => Function.update_of_ne hr ..,by simp,
        fun _ hj => False.elim (Nat.not_lt_zero _ hj),fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ s _ _ h => by simp [Expr.eval,(h.1 133 (by decide) (by decide)).trans h133])
    (fun i _ hi => by
      intro mid ω ⟨hregs,hindex,hprefix,hframe⟩
      have hk r (hr₁ : r ≠ 139) (hr₂ : r ≠ 140) := hregs r hr₁ hr₂
      obtain ⟨out,c,hr,hm,hkeep,hcost⟩ :=
        writeStretchIndexStep_runs mid G ℓ keys source dst i hi hp hG hV hE hw hcap heCap
          ((hk 114 (by decide) (by decide)).trans h114) ((hk 138 (by decide) (by decide)).trans h138)
          ((hk 136 (by decide) (by decide)).trans h136) ((hk 131 (by decide) (by decide)).trans h131)
          hindex (by omega) (by omega) ((hframe _ (by omega)).trans (hread i hi))
          ((hk 73 (by decide) (by decide)).trans h73) hfit
          (fun j hj => (hframe _ (by change j < H.m at hj; omega)).trans (hkeys j hj))
      refine ⟨.normal,out,c,hr,⟨⟨?_,by simp,?_,?_⟩,(hkeep 139 (by decide)).trans hindex⟩,hcost⟩
      · intro r hr₁ hr₂
        exact (Function.update_of_ne hr₁ ..).trans ((hkeep r hr₂).trans (hk r hr₁ hr₂))
      · intro j hj
        change out.mem (dst+j) = _
        by_cases he : j = i
        · subst j
          rw [hm,Function.update_self]
        · rw [hm,Function.update_of_ne (show dst+j ≠ dst+i by omega)]
          exact hprefix j (by omega)
      · intro a ha
        change out.mem a = _
        rw [hm,Function.update_of_ne (show a ≠ dst+i by omega)]
        exact hframe a ha)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o out h
    cases o with
    | normal => exact ⟨h.2.2.1,h.2.2.2,h.1⟩
    | returned _ => exact False.elim h
  · intro _ _
    simp [Expr.size_reg,Expr.size_const,Nat.mul_comm]

/-- Encode a canonical edge-name table using the original graph's
endpoints. This supplies the keys for either of the two scan inputs. -/
theorem stretchIndexKeyTable_triple {w entry g vCap eCap : ℕ}
    {p : Program} (st : State) (G H : MGraph) (src dst : ℕ)
    (hp : p.procs[entry]? = some representativeKeyBody)
    (hg : DynSpanner.Program.DynGraphAt st.mem g vCap eCap G)
    (hsub : H.E ⊆ G.E)
    (h0 : st.regs 0 = DynSpanner.Program.dgIntToExtBase g vCap)
    (h1 : st.regs 1 = DynSpanner.Program.dgETailSlotBase g vCap eCap)
    (h2 : st.regs 2 = DynSpanner.Program.dgEHeadSlotBase g vCap eCap)
    (h3 : st.regs 3 = src) (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap)
    (h6 : st.regs 6 = dst) (h7 : st.regs 7 = H.m)
    (hnames : ∀ i < H.m, st.mem (src+i) = edgeName H i)
    (hw : 1 < 2^w) (hgEnd : g+DynSpanner.Program.dynGraphSize vCap eCap < 2^w)
    (hcap : vCap*vCap*eCap ≤ 2^w)
    (hs : src+H.m < 2^w) (hd : dst+H.m < 2^w)
    (hsep : src+H.m ≤ dst ∨ dst+H.m ≤ src)
    (hgraphSep : g+DynSpanner.Program.dynGraphSize vCap eCap ≤ dst) :
    Triple w p (fun s => s = st) (representativeKeyScan entry)
      (normalPost fun out =>
        (∀ i < H.m, out.mem (dst+i) = representativeSortKey G vCap eCap (edgeName H i)) ∧
        (∀ a, a < dst ∨ dst+H.m ≤ a → out.mem a = st.mem a) ∧
        ∀ r, r ≠ 8 → r ≠ 9 → out.regs r = st.regs r)
      (fun _ => 57*H.m+7) := by
  let edges := List.ofFn fun i : Fin H.m => edgeName H i
  have hlen : edges.length = H.m := List.length_ofFn
  have hedges (i : ℕ) (hi : i < edges.length) :
      edges[i] ∈ G.E ∧ st.mem (src+i) = edges[i] := by
    have hi' : i < H.m := hlen ▸ hi
    simpa only [edges,List.getElem_ofFn] using
      And.intro (hsub (edgeName_mem hi')) (hnames i hi')
  have hwords e (he : e ∈ G.E) : ∀ a ∈
      [DynSpanner.Program.dgIntToExtBase g vCap,DynSpanner.Program.dgETailSlotBase g vCap eCap,
        DynSpanner.Program.dgEHeadSlotBase g vCap eCap,e,vCap,eCap], a < 2^w := by
    have hef := hg.2.2.1 e he
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    simp only [DynSpanner.Program.dynGraphSize] at hgEnd
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;>
      try simp only [DynSpanner.Program.dgIntToExtBase,DynSpanner.Program.dgETailSlotBase,
        DynSpanner.Program.dgEHeadSlotBase]
    all_goals omega
  have ht := representativeKeyScan_triple st G edges src dst (representativeKey_meetsContract G hp)
    (fun mem hframe => representativeGraph_frame hg (fun a _ ha => hframe a (Or.inl (ha.trans_le hgraphSep))))
    h0 h1 h2 h3 h4 h5 h6 (h7.trans hlen.symm) hedges hw hgEnd hcap
    (by rwa [hlen]) (by rwa [hlen]) (by rwa [hlen]) hwords
  refine ht.conseq (fun _ h => h) ?_ (fun _ _ => by rw [hlen])
  intro o out hout
  cases o with
  | returned _ => exact False.elim hout
  | normal =>
    obtain ⟨hdata,hframe,hregs⟩ := hout
    refine ⟨?_,by simpa only [hlen] using hframe,hregs⟩
    intro i hi
    simpa only [edges,List.getElem_ofFn] using hdata i (hlen.symm ▸ hi)

/-- Run the key scan as a procedure so the controller's graph and
allocation registers are retained across both calls. -/
@[expose] def stretchIndexKeyTableBody (key : ℕ) : Stmt :=
  .seq (representativeKeyScan key) (.ret (.const 0))

/-- The key table procedure preserves the prefix and suffix of its
destination array. Its source may be either canonical edge-name table. -/
theorem stretchIndexKeyTable_meetsContract {w entry key g vCap eCap : ℕ}
    {p : Program} (G H : MGraph) (src dst : ℕ)
    (hp : p.procs[entry]? = some (stretchIndexKeyTableBody key))
    (hk : p.procs[key]? = some representativeKeyBody)
    (hsub : H.E ⊆ G.E)
    (hw : 1 < 2^w) (hgEnd : g+DynSpanner.Program.dynGraphSize vCap eCap < 2^w)
    (hcap : vCap*vCap*eCap ≤ 2^w)
    (hs : src+H.m < 2^w) (hd : dst+H.m < 2^w)
    (hsep : src+H.m ≤ dst ∨ dst+H.m ≤ src)
    (hgraphSep : g+DynSpanner.Program.dynGraphSize vCap eCap ≤ dst) :
    MeetsContract w p entry
      { pre := fun args mem =>
          args = [DynSpanner.Program.dgIntToExtBase g vCap,
            DynSpanner.Program.dgETailSlotBase g vCap eCap,
            DynSpanner.Program.dgEHeadSlotBase g vCap eCap,src,vCap,eCap,dst,H.m] ∧
          DynSpanner.Program.DynGraphAt mem g vCap eCap G ∧
          ∀ i < H.m, mem (src+i) = edgeName H i
        post := fun _ mem ret out => ret = 0 ∧
          (∀ i < H.m, out (dst+i) = representativeSortKey G vCap eCap (edgeName H i)) ∧
          (∀ a, a < dst ∨ dst+H.m ≤ a → out a = mem a)
        cost := fun _ _ => 57*H.m+10 } := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ ⟨hargs,hg,hnames⟩
  change args = _ at hargs
  subst args
  have ht := stretchIndexKeyTable_triple (p := p)
    (startState [DynSpanner.Program.dgIntToExtBase g vCap,
      DynSpanner.Program.dgETailSlotBase g vCap eCap,
      DynSpanner.Program.dgEHeadSlotBase g vCap eCap,src,vCap,eCap,dst,H.m] mem pos)
    G H src dst hk hg hsub rfl rfl rfl rfl rfl rfl rfl rfl
    hnames hw hgEnd hcap hs hd hsep hgraphSep
  obtain ⟨o,out,c,hr,hpost,hcost⟩ := ht.runs ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    obtain ⟨hdata,hframe,_⟩ := hpost
    have hret : Runs w p ω (.ret (.const 0)) out (.returned 0) out 2 :=
      runs_ret_iff.mpr ⟨0,by simp [Expr.eval,show 0 < 2^w by omega],rfl,rfl,rfl⟩
    refine ⟨_,out,c+2+1,runs_seq_iff.mpr (Or.inr ⟨out,c,2,hr,hret,rfl⟩),
      ⟨rfl,hdata,hframe⟩,?_⟩
    change c ≤ 57*H.m+7 at hcost
    change _ ≤ 57*H.m+10
    omega

/-- Build one key table using the stable controller graph registers. -/
@[expose] def stretchIndexKeyArgs (src dst count : ℕ) : List Expr :=
  let base := Expr.bin .add (.reg 112) (.const 4)
  let slots n := Expr.bin .add base (.bin .mul (.const n) (.reg 113))
  let edges n := Expr.bin .add (slots 7) (.bin .mul (.const n) (.reg 114))
  [slots 4,edges 3,edges 4,.reg src,.reg 113,.reg 114,.reg dst,.reg count]

open DynSpanner.Program in
/-- The three endpoint-table expressions agree with the dynamic graph
layout whenever the graph block fits in a word. -/
theorem stretchIndexKeyArgs_eval {w : ℕ} (st : State)
    (src dst count g vCap eCap source target m : ℕ)
    (hg : st.regs 112 = g) (hv : st.regs 113 = vCap) (he : st.regs 114 = eCap)
    (hs : st.regs src = source) (hd : st.regs dst = target) (hm : st.regs count = m)
    (hw : 16 ≤ 2^w) (hfit : g+dynGraphSize vCap eCap < 2^w) :
    evalArgs w st (stretchIndexKeyArgs src dst count) =
      some [dgIntToExtBase g vCap,dgETailSlotBase g vCap eCap,
        dgEHeadSlotBase g vCap eCap,source,vCap,eCap,target,m] := by
  unfold dynGraphSize at hfit
  have h4 : 4 < 2^w := by omega
  have h3 : 3 < 2^w := by omega
  have h7 : 7 < 2^w := by omega
  have hb0 : g+4 < 2^w := by omega
  have hb1 : 4*vCap < 2^w := by omega
  have hb2 : 7*vCap < 2^w := by omega
  have hb3 : 3*eCap < 2^w := by omega
  have hb4 : 4*eCap < 2^w := by omega
  have hb5 : g+4+4*vCap < 2^w := by omega
  have hb6 : g+4+7*vCap < 2^w := by omega
  have hb7 : g+4+7*vCap+3*eCap < 2^w := by omega
  have hb8 : g+4+7*vCap+4*eCap < 2^w := by omega
  simp [stretchIndexKeyArgs,evalArgs,Expr.eval,BinOp.eval,hg,hv,he,hs,hd,hm,
    h4,h3,h7,hb0,hb1,hb2,hb3,hb4,hb5,hb6,hb7,hb8,
    dgIntToExtBase,dgETailSlotBase,dgEHeadSlotBase]

open DynSpanner.Program in
/-- Calling the key scan from setup retains every controller register
except its unused return register. -/
theorem stretchIndexKeyCall_runs {w entry key g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G H : MGraph)
    (src dst count source target : ℕ)
    (hp : p.procs[entry]? = some (stretchIndexKeyTableBody key))
    (hk : p.procs[key]? = some representativeKeyBody)
    (hsub : H.E ⊆ G.E) (hgraph : DynGraphAt st.mem g vCap eCap G)
    (hg : st.regs 112 = g) (hv : st.regs 113 = vCap) (he : st.regs 114 = eCap)
    (hs : st.regs src = source) (hd : st.regs dst = target) (hm : st.regs count = H.m)
    (hw : 16 ≤ 2^w) (hgraphFit : g+dynGraphSize vCap eCap < 2^w)
    (hcap : vCap*vCap*eCap ≤ 2^w)
    (hsrc : source+H.m < 2^w) (hdst : target+H.m < 2^w)
    (hsep : source+H.m ≤ target ∨ target+H.m ≤ source)
    (hgraphSep : g+dynGraphSize vCap eCap ≤ target)
    (hnames : ∀ i < H.m, st.mem (source+i) = edgeName H i) :
    ∃ out cost, Runs w p ω (.call 135 entry (stretchIndexKeyArgs src dst count))
      st .normal out cost ∧
      (∀ i < H.m, out.mem (target+i) = representativeSortKey G vCap eCap (edgeName H i)) ∧
      (∀ a, a < target ∨ target+H.m ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 135 → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stretchIndexKeyArgs src dst count)+57*H.m+11 := by
  have ha := stretchIndexKeyArgs_eval st src dst count g vCap eCap source target H.m
    hg hv he hs hd hm hw hgraphFit
  have hwords : ∀ a ∈ [dgIntToExtBase g vCap,dgETailSlotBase g vCap eCap,
      dgEHeadSlotBase g vCap eCap,source,vCap,eCap,target,H.m], a < 2^w := by
    intro a ha'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha'
    unfold dynGraphSize at hgraphFit
    rcases ha' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try simp only [dgIntToExtBase,dgETailSlotBase,dgEHeadSlotBase]
    all_goals omega
  obtain ⟨out,c,ret,hr,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 135)
      (stretchIndexKeyTable_meetsContract G H source target hp hk hsub (by omega)
        hgraphFit hcap hsrc hdst hsep hgraphSep) ha hwords ⟨rfl,hgraph,hnames⟩ ω
  obtain ⟨_,hkeys,hframe⟩ := hpost
  change c ≤ argsSize (stretchIndexKeyArgs src dst count)+(57*H.m+10)+1 at hcost
  exact ⟨out,c,hr,hkeys,hframe,hregs,by omega⟩

/-- Generate both class-key arrays and write the stretch index table. -/
@[expose] def prepareStretchIndices (keys scan : ℕ) : Stmt :=
  .seq (.call 135 keys (stretchIndexKeyArgs 134 136 133))
    (.seq (.call 135 keys (stretchIndexKeyArgs 100 138 73)) (writeStretchIndices scan))

open DynSpanner.Program in
/-- The first five edge-sized work arrays suffice for the canonical names,
keys, and the completed original-edge index table. -/
theorem prepareStretchIndices_runs {w entry key scan g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (ℓ : ℕ → ℝ) (heap : ℕ)
    (hp : p.procs[entry]? = some (stretchIndexKeyTableBody key))
    (hk : p.procs[key]? = some representativeKeyBody)
    (hscan : p.procs[scan]? = some stretchIndexScanBody)
    (hg : DynGraphAt st.mem g vCap eCap G)
    (h112 : st.regs 112 = g) (h113 : st.regs 113 = vCap) (h114 : st.regs 114 = eCap)
    (h134 : st.regs 134 = heap) (h136 : st.regs 136 = heap+G.m)
    (h100 : st.regs 100 = heap+2*G.m) (h138 : st.regs 138 = heap+3*G.m)
    (h131 : st.regs 131 = heap+4*G.m) (h133 : st.regs 133 = G.m)
    (hw : 16 ≤ 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hgraph : g+dynGraphSize vCap eCap ≤ heap) (hfit : heap+5*G.m < 2^w)
    (hnames : ∀ i < G.m, st.mem (heap+i) = edgeName G i) :
    let H := representativeGraph G ℓ
    st.regs 73 = H.m →
    (∀ i < H.m, st.mem (heap+2*G.m+i) = edgeName H i) →
    ∃ out cost, Runs w p ω (prepareStretchIndices entry scan) st .normal out cost ∧
      (∀ i < G.m, out.mem (heap+4*G.m+i) = branchStretchIndex G ℓ (edgeName G i)) ∧
      (∀ a, a < heap+G.m ∨ (heap+2*G.m ≤ a ∧ a < heap+3*G.m) ∨
        heap+5*G.m ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 135 → r ≠ 139 → r ≠ 140 → out.regs r = st.regs r) ∧
      cost ≤ argsSize (stretchIndexKeyArgs 134 136 133)+argsSize (stretchIndexKeyArgs 100 138 73)+
        57*(G.m+H.m)+(26*H.m+48)*G.m+31 := by
  intro H h73 hreps
  have hsub := (representativeGraph_subgraph hg.1 ℓ).2.1
  have hm : H.m ≤ G.m := Finset.card_le_card hsub
  have hgFit : g+dynGraphSize vCap eCap < 2^w := by omega
  have heFit : eCap < 2^w := by unfold dynGraphSize at hgFit; omega
  obtain ⟨mid,c,hr,hsrc,hframe,hregs,hc⟩ :=
    stretchIndexKeyCall_runs (ω := ω) st G G 134 136 133 heap (heap+G.m)
      hp hk (fun _ he => he) hg h112 h113 h114 h134 h136 h133 hw hgFit hcap
      (by omega) (by omega) (Or.inl le_rfl) (by omega) hnames
  have hg' := representativeGraph_frame hg fun a _ ha => hframe a (Or.inl (by omega))
  have hk₁ r (hn : r ≠ 135) := hregs r hn
  obtain ⟨ready,d,hs,hkeys,hframe',hkeep,hd⟩ :=
    stretchIndexKeyCall_runs (ω := ω) mid G H 100 138 73 (heap+2*G.m) (heap+3*G.m)
      hp hk hsub hg' ((hk₁ 112 (by decide)).trans h112) ((hk₁ 113 (by decide)).trans h113)
      ((hk₁ 114 (by decide)).trans h114) ((hk₁ 100 (by decide)).trans h100)
      ((hk₁ 138 (by decide)).trans h138) ((hk₁ 73 (by decide)).trans h73) hw hgFit hcap
      (by omega) (by omega) (Or.inl (by omega)) (by omega)
      (fun i hi => (hframe _ (Or.inr (by omega))).trans (hreps i hi))
  have hk₂ r (hn : r ≠ 135) := (hkeep r hn).trans (hregs r hn)
  have ht := writeStretchIndices_triple (p := p) ready G ℓ (heap+3*G.m) (heap+G.m)
    (heap+4*G.m) hscan hg.1 hg.2.1 hg.2.2.1 (by omega) hcap heFit
    ((hk₂ 114 (by decide)).trans h114) ((hk₂ 138 (by decide)).trans h138)
    ((hk₂ 136 (by decide)).trans h136) ((hk₂ 131 (by decide)).trans h131)
    ((hk₂ 133 (by decide)).trans h133) (by omega) (by omega) (Or.inl (by omega))
    (fun i hi => (hframe' _ (Or.inl (by omega))).trans (hsrc i hi))
    ((hk₂ 73 (by decide)).trans h73) (by change heap+3*G.m+H.m < _; omega)
    (Or.inl (by change heap+3*G.m+H.m ≤ _; omega)) hkeys
  obtain ⟨o,out,k,hwrites,hpost,hcost⟩ := ht.runs ω rfl
  change k ≤ (26*H.m+48)*G.m+7 at hcost
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    obtain ⟨hindex,hout,hregs'⟩ := hpost
    have htail := runs_seq_iff.mpr (Or.inr ⟨ready,d,k,hs,hwrites,rfl⟩)
    refine ⟨out,c+(d+k+1)+1,runs_seq_iff.mpr (Or.inr ⟨mid,c,_,hr,htail,rfl⟩),
      hindex,?_,fun r hr₁ hr₂ hr₃ => (hregs' r hr₂ hr₃).trans (hk₂ r hr₁),by omega⟩
    intro a ha
    exact (hout a (by omega)).trans ((hframe' a (by omega)).trans (hframe a (by omega)))

end MinCostFlow.LastLevelProgram
