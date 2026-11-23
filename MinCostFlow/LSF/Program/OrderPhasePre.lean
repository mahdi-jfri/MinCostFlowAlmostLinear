module

public import MinCostFlow.LSF.Program.OrderPhaseIn

/-!
# The pre of the order phase

`orderPhase_seqPre` shows that `OrderPhaseIn` gives the pre of the whole call sequence of the order
phase, with the budget `orderPhaseCost`. Call by call, the pre of the next call comes from the
posts of the earlier ones and from `OrderPhaseIn`, through the frames of the posts.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- `T0IndexArrays` depends only on the entries below `tM`. -/
lemma T0IndexArrays.congr {T₀ : MGraph} {vList : List ℕ} {tM : ℕ} {fid tl hd fid' tl' hd' : ℕ → ℕ}
    (hA : T0IndexArrays T₀ vList tM fid tl hd) (hf : ∀ i < tM, fid i = fid' i)
    (htl : ∀ i < tM, tl i = tl' i) (hhd : ∀ i < tM, hd i = hd' i) :
    T0IndexArrays T₀ vList tM fid' tl' hd' where
  fid_mem i hi := hf i hi ▸ hA.fid_mem i hi
  fid_cover f hf' := by
    obtain ⟨i, hi, rfl⟩ := hA.fid_cover f hf'
    exact ⟨i, hi, (hf i hi).symm⟩
  fid_inj i hi j hj h := hA.fid_inj i hi j hj (by rw [hf i hi, hf j hj]; exact h)
  tl_lt i hi := htl i hi ▸ hA.tl_lt i hi
  hd_lt i hi := hhd i hi ▸ hA.hd_lt i hi
  tail_eq i hi := by rw [← hf i hi, ← htl i hi]; exact hA.tail_eq i hi
  head_eq i hi := by rw [← hf i hi, ← hhd i hi]; exact hA.head_eq i hi

/-- The cost of the order phase, from its arguments. -/
def orderPhaseCost (a : List ℕ) (_ : ℕ → ℕ) : ℕ :=
  (400 * a.getD 0 0 + 400 * a.getD 1 0 + 60 * a.getD 0 0 * a.getD 8 0 + 40 * a.getD 8 0 + 411) +
  14 +
  (50 * a.getD 9 0 + a.getD 9 0 * (100 * a.getD 8 0 + 300 * a.getD 20 0 + 420) +
    (90 * a.getD 20 0 + 180) * a.getD 0 0 * (Nat.clog 2 (a.getD 0 0) + 1) +
    80 * a.getD 0 0 * a.getD 20 0 + 200 * a.getD 0 0 + 400 + 100 * a.getD 0 0 * a.getD 8 0 +
    40 * a.getD 8 0 + 227) +
  (100 * a.getD 1 0 + 150 * a.getD 0 0 + 1000 * a.getD 35 0 + 414) +
  (a.getD 0 0 * (bstLoopCost (a.getD 0 0) + 500) + 20 * a.getD 0 0 + 609) + 2

/-- Every argument of the phase is a word. -/
lemma OrderPhaseIn.args_lt {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {mem : ℕ → ℕ} (I : OrderPhaseIn w h G₀ T₀ vList eList X mem) :
    ∀ j, X.args.getD j 0 < 2 ^ w := by
  have hall : ∀ x ∈ X.args, x < 2 ^ w := by
    have l1 := I.l1; have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l5 := I.l5
    have l6 := I.l6; have l7 := I.l7; have l8 := I.l8; have l9 := I.l9; have l10 := I.l10
    have l11 := I.l11; have l12 := I.l12; have l13 := I.l13; have l14 := I.l14
    have l15 := I.l15; have l16 := I.l16; have l17 := I.l17; have l18 := I.l18
    have l19 := I.l19; have hmin := I.hmin; have hn := I.hn2; have hnO := I.hnO
    have hKq := I.hKq
    have hnK : X.K ≤ X.n * X.K := Nat.le_mul_of_pos_left _ (by omega)
    have hnL : X.logCap ≤ X.n * X.logCap := Nat.le_mul_of_pos_left _ (by omega)
    simp only [OrderLayout.args, OrderLayout.qOrd, List.forall_mem_cons,
      and_true, dgEListBase, dgETailSlotBase, dgEHeadSlotBase, dgIntToExtBase, tPiBase,
      tOrigIdBase, tDgTPtr, tBlockSize, dynGraphSize] at l1 l2 ⊢
    and_intros
    all_goals first | omega | simp
  intro j
  rcases lt_or_ge j X.args.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj]; exact hall _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ hj]; exact Nat.two_pow_pos w

/-- The layout facts of `OrderPhaseIn`, unfolded for `omega`. -/
lemma OrderPhaseIn.tPi_le {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {mem : ℕ → ℕ} (I : OrderPhaseIn w h G₀ T₀ vList eList X mem) :
    tDgTPtr X.tPtr + dynGraphSize X.vCap (2 * X.tM + 1) ≤ tPiBase X.tPtr X.vCap X.tM ∧
    tPiBase X.tPtr X.vCap X.tM + X.tM ≤ X.vIdx := by
  have := I.l2
  simp only [tPiBase, tOrigIdBase, tDgTPtr, tBlockSize] at this ⊢
  omega

/-- The pre of the `T` stage, from a memory that agrees with the start memory on what it reads. -/
lemma orderPhase_tPre {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {mem mem₃ : ℕ → ℕ} (I : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (hfr : ∀ a, (a < tPiBase X.tPtr X.vCap X.tM ∨
      (tPiBase X.tPtr X.vCap X.tM + X.tM ≤ a ∧ a < X.auxPar) ∨
      (X.minPtr + X.n * X.logCap ≤ a ∧ a < X.rtOut)) → mem₃ a = mem a) :
    (tStageContract w G₀ T₀ vList).pre [X.tPtr, X.vCap, X.eCap, X.tM, X.vListPtr, X.tOrigSrc,
      X.tTail, X.tHead, X.n, X.nOrig, tOrigIdBase X.tPtr X.vCap X.tM, tDgTPtr X.tPtr] mem₃ := by
  have l2 := I.l2; have l3 := I.l3; have l4 := I.l4; have l5 := I.l5; have l6 := I.l6
  have l7 := I.l7; have l8 := I.l8; have l9 := I.l9; have l10 := I.l10; have l11 := I.l11
  have l12 := I.l12; have l13 := I.l13; have l14 := I.l14; have l15 := I.l15
  have l16 := I.l16; have l17 := I.l17; have l18 := I.l18; have l19 := I.l19
  have hmin := I.hmin
  obtain ⟨ht1, ht2⟩ := I.tPi_le
  refine ⟨X.tPtr, X.vCap, X.eCap, X.tM, X.vListPtr, X.tOrigSrc, X.tTail, X.tHead, X.n, X.nOrig,
    rfl, I.hw16, ?_, I.hvlen, ?_, I.hvCap, I.hGV, I.hnO, ?_, I.hTG, ?_, ?_, by omega, by omega,
    by omega, by omega, by omega⟩
  · exact I.hA.congr (fun i hi => (hfr _ (Or.inr (Or.inr ⟨by omega, by omega⟩))).symm)
      (fun i hi => (hfr _ (Or.inr (Or.inr ⟨by omega, by omega⟩))).symm)
      (fun i hi => (hfr _ (Or.inr (Or.inr ⟨by omega, by omega⟩))).symm)
  · exact I.hvLA.congr fun k hk1 hk2 => hfr k (Or.inr (Or.inl ⟨by omega, by
      rw [I.hvlen] at hk2; omega⟩))
  · intro i hi
    rw [hfr _ (Or.inr (Or.inr ⟨by omega, by omega⟩))]
    exact I.hO i hi
  · intro i hi
    rw [hfr _ (Or.inl (by omega))]
    exact I.hzT i hi
  · intro e he
    have h1 : tPiBase X.tPtr X.vCap X.tM + X.tM ≤ tIdxOfEdgeBase X.tPtr X.vCap X.tM + e := by
      simp only [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase]; omega
    have h2 : tIdxOfEdgeBase X.tPtr X.vCap X.tM + e < X.auxPar := by
      simp only [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr,
        tBlockSize] at l2 ⊢
      omega
    rw [hfr _ (Or.inr (Or.inl ⟨h1, h2⟩))]
    exact I.hzIdx e he

/-- A register file that changed only at `R` or above still holds words below `R`. -/
lemma upd_words {w R i v : ℕ} {regs : ℕ → ℕ} (h : ∀ j < R, regs j < 2 ^ w) (hi : R ≤ i) :
    ∀ j < R, Function.update regs i v j < 2 ^ w := fun j hj => by
  rw [Function.update_of_ne (by omega)]; exact h j hj

/-- `OrderPhaseIn` gives the pre of the whole order phase. -/
theorem orderPhase_seqPre {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {mem : ℕ → ℕ} (I : OrderPhaseIn w h G₀ T₀ vList eList X mem) (bRoot bStore bOrder bT bTH : ℕ) :
    SeqPre w 41 0 (orderPhaseItems w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH)
      (fun j => X.args.getD j 0) mem (orderPhaseCost X.args mem) := by
  have hgd := I.args_lt
  have hn := I.hn2; have hmin := I.hmin
  have l5 := I.l5; have l6 := I.l6; have l7 := I.l7; have l8 := I.l8; have l9 := I.l9
  have l10 := I.l10; have l11 := I.l11; have l12 := I.l12; have l13 := I.l13; have l14 := I.l14
  have l15 := I.l15; have l16 := I.l16; have l17 := I.l17; have l18 := I.l18; have l19 := I.l19
  have l4 := I.l4; have l3 := I.l3; have l2 := I.l2
  obtain ⟨ht1, ht2⟩ := I.tPi_le
  have hl := (show 1 ≤ X.logCap by rw [I.hlog]; unfold auxLogCap; omega)
  set c1 := 400 * X.n + 400 * X.tM + 60 * X.n * X.logCap + 40 * X.logCap + 411 with hc1
  set c3 := 50 * X.m0 + X.m0 * (100 * X.logCap + 300 * X.K + 420) +
    (90 * X.K + 180) * X.n * (Nat.clog 2 X.n + 1) + 80 * X.n * X.K + 200 * X.n + 400 +
    100 * X.n * X.logCap + 40 * X.logCap + 227 with hc3
  set c4 := 100 * X.tM + 150 * X.n + 1000 * X.nOrig + 414 with hc4
  set c5 := X.n * (bstLoopCost X.n + 500) + 20 * X.n + 609 with hc5
  have hB : orderPhaseCost X.args mem = c1 + 14 + c3 + c4 + c5 + 2 := rfl
  have hw0 : ∀ j < 41, (fun j => X.args.getD j 0) j < 2 ^ w := fun j _ => hgd j
  -- 1. the rooting
  refine SeqPre.cons [X.n, X.tM, X.tTail, X.tHead, 0, X.rtOut, X.sPtr, X.auxPar, X.logCap] c1 rfl
    (words_of_map fun j hj => hw0 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega)) (orderPhase_rootPre I)
    (by simp [rootStageContract]; omega) (by omega) ?_
  intro v₁ mem₁ hpost₁
  have hw1 := upd_words (v := v₁) hw0 (i := 41 + 0) (by omega)
  -- 2. the parent edge of the root
  refine SeqPre.cons [X.auxPar + X.n, 0] 14 rfl
    (words_of_map fun j hj => hw1 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega)) ⟨_, _, rfl⟩
    (by simp [storeWordContract]) (by omega) ?_
  intro v₂ mem₂ hpost₂
  obtain ⟨a₂, b₂, heq₂, -, hmem₂⟩ := hpost₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl⟩ := heq₂
  subst hmem₂
  have hw2 := upd_words (v := v₂) hw1 (i := 41 + 1) (by omega)
  -- what the rooting left
  have hpost₁' := hpost₁
  obtain ⟨n', m', tailArr', headArr', r', outPtr', sPtr', auxPar', logCap', tl, hd, heq, -, hends,
    hR, ⟨Q, hQ, hQat⟩, -, hfr⟩ := hpost₁'
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
  have hF2 : ∀ a, (a < X.auxPar ∨ (X.minPtr ≤ a ∧ a < X.rtOut) ∨
      X.sPtr + 4 * X.n + 2 * X.tM ≤ a) →
      Function.update mem₁ (X.auxPar + X.n) 0 a = mem a := orderPhase_frame₂ I hfr
  have hpe : ∀ y < X.n, y ≠ 0 →
      Function.update mem₁ (X.auxPar + X.n) 0 (X.auxPar + X.n + y) < X.tM := by
    intro y hy hy0
    rw [Function.update_of_ne (by omega)]
    exact (hR.step y hy hy0).1
  -- 3. the order
  refine SeqPre.cons [X.n, 0, X.m0, dgEListBase X.gPtr X.vCap X.eCap,
    dgETailSlotBase X.gPtr X.vCap X.eCap, dgEHeadSlotBase X.gPtr X.vCap X.eCap,
    dgIntToExtBase X.gPtr X.vCap, X.vIdx, X.eu, X.ev, X.qPtr, X.Kq, X.dPtr, X.K, X.tmpPtr,
    X.logCap, X.auxPar + 3 * X.n, X.auxPar + X.n + X.n, X.auxPar, X.qOrd, X.auxPar + X.n,
    X.arrPtr, X.scratchPtr, tPiBase X.tPtr X.vCap X.tM, X.minPtr] c3 rfl (words_of_map fun j hj => hw2 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega))
    (orderPhase_orderPre I hpost₁) (by simp [orderStageContract]; omega) (by omega) ?_
  intro v₃ mem₃ hpost₃
  have hw3 := upd_words (v := v₃) hw2 (i := 41 + 2) (by omega)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₃, -, -, -,
    -, -, hfr₃⟩ := hpost₃
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, -, -, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  have hF3 : ∀ a, (a < tPiBase X.tPtr X.vCap X.tM ∨ tPiBase X.tPtr X.vCap X.tM + X.tM ≤ a) →
      (a < X.eu ∨ X.ev + X.m0 ≤ a) → (a < X.dPtr ∨ X.scratchPtr + X.n ≤ a) →
      (a < X.minPtr ∨ X.minPtr + X.n * X.logCap ≤ a) →
      mem₃ a = Function.update mem₁ (X.auxPar + X.n) 0 a :=
    fun a h1 h2 h3 h4 => hfr₃ a h2 h3 h4 fun y hy hy0 => by have := hpe y hy hy0; omega
  -- 4. the `T` block
  refine SeqPre.cons [X.tPtr, X.vCap, X.eCap, X.tM, X.vListPtr, X.tOrigSrc, X.tTail, X.tHead,
    X.n, X.nOrig, tOrigIdBase X.tPtr X.vCap X.tM, tDgTPtr X.tPtr] c4 rfl (words_of_map fun j hj => hw3 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega))
    (orderPhase_tPre I fun a ha => by
      rw [hF3 a (by omega) (by omega) (by omega) (by omega)]
      exact hF2 a (by omega))
    (by simp [tStageContract]; omega) (by omega) ?_
  intro v₄ mem₄ hpost₄
  have hw4 := upd_words (v := v₄) hw3 (i := 41 + 3) (by omega)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₄, -, -, -, hfr₄⟩ := hpost₄
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -⟩ := heq₄
  -- the memory after the `T` block, above it
  have hF4 : ∀ a, X.auxPar ≤ a → (a < X.eu ∨ X.ev + X.m0 ≤ a) →
      (a < X.dPtr ∨ X.scratchPtr + X.n ≤ a) → (a < X.minPtr ∨ X.minPtr + X.n * X.logCap ≤ a) →
      mem₄ a = Function.update mem₁ (X.auxPar + X.n) 0 a := fun a h0 h2 h3 h4 => by
    rw [hfr₄ a (Or.inr (by omega))]
    exact hF3 a (Or.inr (by omega)) h2 h3 h4
  -- 5. the parents of `T_H`
  refine SeqPre.cons [X.n, X.qOrd, X.auxPar, X.auxPar + X.n + X.n, X.thBase, 0, X.thDst] c5 rfl
    (words_of_map fun j hj => hw4 j (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega)) ?_
    (by simp [thStageContract]; omega) (by omega) ?_
  · have hqo : X.qOrd = X.sPtr + X.n + 2 * X.tM + X.n := rfl
    have hA3 : ∀ x < 3 * X.n, mem₄ (X.auxPar + x) = mem₁ (X.auxPar + x) ∨ x = X.n := by
      intro x hx
      rcases eq_or_ne x X.n with hx' | hx'
      · exact Or.inr hx'
      · left
        rw [hF4 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
          Function.update_of_ne (by omega)]
    have hpar : ∀ x < X.n, mem₁ (X.auxPar + x) = mem₄ (X.auxPar + x) := fun x hx =>
      ((hA3 x (by omega)).resolve_right (by omega)).symm
    have hdep : ∀ x < X.n, mem₁ (X.auxPar + X.n + X.n + x) = mem₄ (X.auxPar + X.n + X.n + x) :=
      fun x hx => by
        have := hA3 (X.n + X.n + x) (by omega)
        rw [show X.auxPar + X.n + X.n + x = X.auxPar + (X.n + X.n + x) by omega]
        exact (this.resolve_right (by omega)).symm
    have hR₄ : RootedArrays X.n X.tM 0 (X.tl mem) (X.hd mem) (fun x => mem₄ (X.auxPar + x))
        (fun x => mem₁ (X.auxPar + X.n + x)) (fun x => mem₄ (X.auxPar + X.n + X.n + x)) :=
      (hR.congr (by omega) hpar (fun _ _ => rfl) hdep).congr_ends
        (fun f hf => ((hends f hf).1).symm) (fun f hf => ((hends f hf).2).symm)
    refine ⟨X.n, X.qOrd, X.auxPar, X.auxPar + X.n + X.n, X.thBase, 0, X.thDst, X.tM, Q,
      fun i => mem (X.tOrigSrc + i), X.tl mem, X.hd mem, fun x => mem₁ (X.auxPar + X.n + x), rfl,
      by omega, I.hvlen, hQ.congr hpar, ?_, ⟨I.hT, I.hA, I.hnd, I.hV, I.hvlen ▸ hR₄,
        by rw [I.hvlen]; omega⟩, fun x hx => hR₄.dep_lt hx, by omega, by omega, by omega,
      by omega, I.l19, I.l20, ?_⟩
    · refine hQat.congr fun k hk1 hk2 => ?_
      rw [hQ.len] at hk2
      rw [hF4 k (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)),
        Function.update_of_ne (by omega)]
    · intro a ha1 ha2
      rw [hF4 a (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)),
        hF2 a (Or.inr (Or.inr (by omega)))]
      exact I.hzTH a ha1 ha2
  intro v₅ mem₅ _
  show 2 ≤ _
  omega

/-- The contract of the order phase. -/
def orderPhaseContract (w h : ℕ) (G₀ T₀ : MGraph) (vList eList : List ℕ)
    (bRoot bStore bOrder bT bTH : ℕ) : Contract :=
  callSeqContract w 41 4 (orderPhaseItems w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH)
    orderPhaseCost

/-- The body of the order phase. -/
def orderPhaseProc (w h : ℕ) (G₀ T₀ : MGraph) (vList eList : List ℕ)
    (bRoot bStore bOrder bT bTH : ℕ) : Stmt :=
  callSeqStmt 41 4 0 (orderPhaseItems w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH)

theorem orderPhase_meetsContract {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {p : Program}
    {b bRoot bStore bOrder bT bTH : ℕ}
    (hp : p.procs[b]? = some (orderPhaseProc w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH))
    (hRoot : MeetsContract w p bRoot (rootStageContract w))
    (hStore : MeetsContract w p bStore storeWordContract)
    (hOrder : MeetsContract w p bOrder (orderStageContract w h G₀ vList eList))
    (hT : MeetsContract w p bT (tStageContract w G₀ T₀ vList))
    (hTH : MeetsContract w p bTH (thStageContract w T₀ vList)) :
    MeetsContract w p b (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH) := by
  refine callSeq_meetsContract hp ?_
  intro it hit
  simp only [orderPhaseItems, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl | rfl
  exacts [hRoot, hStore, hOrder, hT, hTH]

/-- The post of the order phase, call by call, with the arguments written out. -/
theorem orderPhase_post {w h : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {bRoot bStore bOrder bT bTH : ℕ} {mem mem₅ : ℕ → ℕ} {ret : ℕ}
    (hpost : (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH).post X.args mem
      ret mem₅) :
    ∃ v₁ mem₁ v₃ mem₃ v₄ mem₄ v₅,
      (rootStageContract w).post
        [X.n, X.tM, X.tTail, X.tHead, 0, X.rtOut, X.sPtr, X.auxPar, X.logCap] mem v₁ mem₁ ∧
      (orderStageContract w h G₀ vList eList).post
        [X.n, 0, X.m0, dgEListBase X.gPtr X.vCap X.eCap, dgETailSlotBase X.gPtr X.vCap X.eCap,
          dgEHeadSlotBase X.gPtr X.vCap X.eCap, dgIntToExtBase X.gPtr X.vCap, X.vIdx, X.eu, X.ev,
          X.qPtr, X.Kq, X.dPtr, X.K, X.tmpPtr, X.logCap, X.auxPar + 3 * X.n,
          X.auxPar + X.n + X.n, X.auxPar, X.qOrd, X.auxPar + X.n, X.arrPtr, X.scratchPtr,
          tPiBase X.tPtr X.vCap X.tM, X.minPtr]
        (Function.update mem₁ (X.auxPar + X.n) 0) v₃ mem₃ ∧
      (tStageContract w G₀ T₀ vList).post [X.tPtr, X.vCap, X.eCap, X.tM, X.vListPtr, X.tOrigSrc,
        X.tTail, X.tHead, X.n, X.nOrig, tOrigIdBase X.tPtr X.vCap X.tM, tDgTPtr X.tPtr]
        mem₃ v₄ mem₄ ∧
      (thStageContract w T₀ vList).post
        [X.n, X.qOrd, X.auxPar, X.auxPar + X.n + X.n, X.thBase, 0, X.thDst] mem₄ v₅ mem₅ := by
  obtain ⟨v₁, mem₁, h₁, v₂, mem₂, h₂, v₃, mem₃, h₃, v₄, mem₄, h₄, v₅, mem₅', h₅, h₆, -⟩ := hpost
  obtain ⟨a, b, heq, -, rfl⟩ := h₂
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl⟩ := heq
  subst h₆
  exact ⟨v₁, mem₁, v₃, mem₃, v₄, mem₄, v₅, h₁, h₃, h₄, h₅⟩

end

end MinCostFlow.LSF.Program
