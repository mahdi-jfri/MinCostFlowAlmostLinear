module

public import MinCostFlow.LSF.Program.DecompPhaseIn
public import MinCostFlow.LSF.Program.OrderPhasePre

/-!
# The pre of the decomposition phase

`decompPhase_seqPre` shows that `DecompPhaseIn` gives the pre of the whole call sequence of the
decomposition phase, with the budget `decompPhaseCost`. Two facts about outputs are needed on
the way: the boundary flags of `decompWTProc` are `0` or `1` (`decompWTOut_bnd_le`), and so are
the flags of the stretch pass (`wstrEdgeOut_ret_le`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- The boundary flags of `decompWTProc` are `0` or `1`. -/
lemma decompWTOut_bnd_le {mem mem' : ℕ → ℕ} {n m0 euPtr evPtr qPtr parPtr r θ base : ℕ}
    {Q : List ℕ} (hO : DecompWTOut mem mem' n m0 euPtr evPtr qPtr parPtr r θ base)
    (hQ : TopDownOrder n r (fun x => mem (parPtr + x)) Q) (hQat : ListAt mem qPtr Q) (hn : 0 < n) :
    ∀ y < n, mem' (base + 11 * n + y) ≤ 1 := by
  obtain ⟨-, hGC, -, -, -, hroot, -⟩ := hO
  obtain ⟨-, -, hcl⟩ := hGC Q hQ hQat
  have hle : ∀ s c, closureIn s c ≤ 1 := fun s c => by unfold closureIn; split_ifs <;> omega
  intro y hy
  by_cases hyr : y = r
  · subst hyr; rw [hroot]; exact hle _ _
  · have hyQ := hQ.cover y hy
    have hQne : 0 < Q.length := by rw [hQ.len]; exact hn
    have h0 := hQ.head_eq hn
    have hyD : y ∈ Q.drop 1 := by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hyQ
      have hi0 : i ≠ 0 := by rintro rfl; exact hyr h0
      rw [List.mem_iff_getElem]
      exact ⟨i - 1, by rw [List.length_drop]; omega, by
        rw [List.getElem_drop]; congr 1; omega⟩
    have := (hcl y hyD).2
    simp only at this
    rw [this]
    exact hle _ _

/-- The flag of an edge of the stretch pass is `0` or `1`. -/
lemma wstrEdgeOut_ret_le {h LB Lw : ℕ} {mem mem' : ℕ → ℕ} {numOut denOut acc le th k2 ret : ℕ}
    (hO : WstrEdgeOut h LB Lw mem mem' numOut denOut acc le th k2 ret) : ret ≤ 1 := by
  obtain ⟨-, -, h1, h2⟩ := hO
  by_cases hc : wstrNumVal (capacity h LB) (unsignedVal mem acc h LB) (unsignedVal mem k2 h LB)
      (unsignedVal mem le h LB) < unsignedVal mem th h LB * unsignedVal mem le h LB % capacity h LB
  · rw [(h1 hc).1]; omega
  · rw [(h2 hc).1]

/-- A register file that changed at one place with a word still holds words below `R`. -/
lemma upd_words_val {w R i v : ℕ} {regs : ℕ → ℕ} (h : ∀ j < R, regs j < 2 ^ w) (hv : v < 2 ^ w) :
    ∀ j < R, Function.update regs i v j < 2 ^ w := fun j hj => by
  rw [Function.update_apply]; split_ifs
  · exact hv
  · exact h j hj

/-- The cost of the decomposition phase, from its arguments. -/
def decompPhaseCost (a : List ℕ) (_ : ℕ → ℕ) : ℕ :=
  (60 * a.getD 1 0 + 400 * a.getD 0 0 + 611) +
  (20 * Nat.log 2 (a.getD 0 0 + 1) + 20 * Nat.log 2 (a.getD 9 0 + 2) + 105) +
  (wstrCost (a.getD 0 0) (a.getD 11 0) (a.getD 1 0) (wstrLB (a.getD 0 0) (a.getD 9 0) (a.getD 10 0))
    (a.getD 15 0) + 227) +
  (20 * a.getD 1 0 + 17) +
  (40 * a.getD 0 0 + 40 * a.getD 28 0 + 60 * a.getD 1 0 + 112) +
  (a.getD 9 0 * (70 * a.getD 0 0 + 80) + 30 * a.getD 11 0 + 400 * a.getD 0 0 + 416) +
  (2 * wstrCopyEdgesCost (a.getD 1 0) (a.getD 10 0) + 4)

lemma wstrStageArgs_eq (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
    x21 x22 x23 x24 : ℕ) :
    wstrStageArgs [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17,
      x18, x19, x20, x21, x22, x23, x24] =
    [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20,
      x21, x22, x23, x24, wsPt x24 x0 x1 x2 x4 1, wsPt x24 x0 x1 x2 x4 2, wsPt x24 x0 x1 x2 x4 3,
      wsPt x24 x0 x1 x2 x4 4, wsPt x24 x0 x1 x2 x4 5, wsPt x24 x0 x1 x2 x4 6,
      wsPt x24 x0 x1 x2 x4 7, wsPt x24 x0 x1 x2 x4 8, wsPt x24 x0 x1 x2 x4 9,
      wsPt x24 x0 x1 x2 x4 10, wsPt x24 x0 x1 x2 x4 11, wsPt x24 x0 x1 x2 x4 12,
      wsPt x24 x0 x1 x2 x4 13, wsPt x24 x0 x1 x2 x4 14, wsPt x24 x0 x1 x2 x4 15,
      wsPt x24 x0 x1 x2 x4 16, wsPt x24 x0 x1 x2 x4 17, wsPt x24 x0 x1 x2 x4 18] := rfl

lemma wstrStage_cost_eq {w h C : ℕ} (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
    x18 x19 x20 x21 x22 x23 x24 : ℕ) (mem : ℕ → ℕ) :
    (wstrStageContract w h C).cost [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13,
      x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24] mem = wstrCost x0 x1 x2 x4 x9 + 200 := by
  simp only [wstrStageContract, wstrContract, wstrStageArgs_eq]
  rfl

/-- Every argument of the phase is a word. -/
lemma DecompPhaseIn.args_lt {w h C : ℕ} {T₀ : MGraph} {vList : List ℕ} {X : DecompLayout}
    {mem : ℕ → ℕ} (I : DecompPhaseIn w h C T₀ vList X mem) : ∀ j, X.args.getD j 0 < 2 ^ w := by
  have hall : ∀ x ∈ X.args, x < 2 ^ w := by
    have L1 := I.L1; have L2 := I.L2; have L3 := I.L3; have L4 := I.L4; have L5 := I.L5
    have L6 := I.L6; have L7 := I.L7; have L8 := I.L8; have L9 := I.L9; have L10 := I.L10
    have L11 := I.L11; have L12 := I.L12; have L13 := I.L13; have L14 := I.L14
    have L15 := I.L15; have L16 := I.L16; have L17 := I.L17; have L18 := I.L18
    have L19 := I.L19; have hn := I.hn; have hθ := I.hθw; have hD := I.hDw; have hk := I.hk
    have hLB := I.hLB; have hLw := lw_le_wstrLB X.n X.D X.Lw; have hLin := I.hLinw
    have hnO := I.hnO
    have hp := wsPt_mono X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) (Nat.zero_le 18)
    have hp0 : wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 0 = X.idPtr := rfl
    have hnL : X.logCap ≤ X.n * X.logCap := Nat.le_mul_of_pos_left _ hn
    simp only [DecompLayout.args, DecompLayout.denS, List.forall_mem_cons, and_true] at hp0 ⊢
    and_intros
    all_goals first | omega | simp
  intro j
  rcases lt_or_ge j X.args.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj]; exact hall _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ hj]; exact Nat.two_pow_pos w

/-- `DecompPhaseIn` gives the pre of the whole decomposition phase. -/
theorem decompPhase_seqPre {w h C : ℕ} {T₀ : MGraph} {vList : List ℕ} {X : DecompLayout}
    {mem : ℕ → ℕ} (I : DecompPhaseIn w h C T₀ vList X mem) (bWT bLB bW bCopy bFlag bRoots : ℕ) :
    SeqPreCont w 40 (decompCopyPre w) 0 (decompPhaseItems w h C bWT bLB bW bCopy bFlag bRoots)
      (fun j => X.args.getD j 0) mem (decompPhaseCost X.args mem) := by
  have hgd := I.args_lt
  have hn := I.hn
  have L1 := I.L1; have L2 := I.L2; have L3 := I.L3; have L4 := I.L4; have L4s := I.L4s
  have L5 := I.L5; have L6 := I.L6; have L7 := I.L7; have L8 := I.L8; have L9 := I.L9
  have L10 := I.L10; have L11 := I.L11; have L12 := I.L12; have L13 := I.L13; have L14 := I.L14
  have L15 := I.L15; have L16 := I.L16; have L17 := I.L17; have L18 := I.L18
  have L19 := I.L19; have hLBw := I.hLB; have hDw := I.hDw
  have hden : X.denS = X.numS + X.eCap * X.Lw := rfl
  set LB := wstrLB X.n X.D X.Lw with hLBdef
  have hp18 := wsPt_mono X.idPtr X.n X.tM X.m0 LB (Nat.zero_le 18)
  have hp0 : wsPt X.idPtr X.n X.tM X.m0 LB 0 = X.idPtr := rfl
  rw [hp0] at hp18
  set c1 := 60 * X.m0 + 400 * X.n + 611 with hc1
  set c2 := 20 * Nat.log 2 (X.n + 1) + 20 * Nat.log 2 (X.D + 2) + 105 with hc2
  set c3 := wstrCost X.n X.tM X.m0 LB X.logCap + 227 with hc3
  set c4 := 20 * X.m0 + 17 with hc4
  set c5 := 40 * X.n + 40 * X.cnt + 60 * X.m0 + 112 with hc5
  set c6 := X.D * (70 * X.n + 80) + 30 * X.tM + 400 * X.n + 416 with hc6
  set cTail := 2 * wstrCopyEdgesCost X.m0 X.Lw + 4 with hcTail
  have hB : decompPhaseCost X.args mem = c1 + c2 + c3 + c4 + c5 + c6 + cTail := rfl
  have hw0 : ∀ j < 43, (fun j => X.args.getD j 0) j < 2 ^ w := fun j _ => hgd j
  have hmono := decompCopyPre_mono w
  obtain ⟨Q, tl, hd, dep, hQ, hQat, hRA, hLT, -⟩ := I.htree
  -- 1. the decomposition `W_T`
  refine SeqPreCont.cons hmono [X.n, X.m0, X.eu, X.ev, X.qOrd, X.auxPar, 0, X.θ, X.dBase] c1 rfl
    (words_of_map fun j hj => hw0 j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega))
    ⟨X.n, X.m0, X.eu, X.ev, X.qOrd, X.auxPar, 0, X.θ, X.dBase, Q, rfl, I.hw16, hn, I.hθ, I.hθw,
      I.hm0w, hQ, hQat, by omega, by omega, by omega, by omega, by omega, I.heuv, I.hzD⟩
    (by simp [decompWTContract]; omega) (by omega) ?_
  intro v₁ m₁ hp₁
  obtain ⟨_, _, _, _, _, _, _, _, _, heq₁, hv₁, hfr₁, hOut⟩ := hp₁
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  have hw1 := upd_words_val (i := 40 + 0) hw0 (show v₁ < 2 ^ w by rw [hv₁]; exact Nat.two_pow_pos w)
  -- 2. the block width
  refine SeqPreCont.cons hmono [X.n, X.D, X.Lw] c2 rfl
    (words_of_map fun j hj => hw1 j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega))
    ⟨X.n, X.D, X.Lw, rfl, I.hw16, by omega, by omega, hLBw⟩
    (by simp [wstrLBContract]; omega) (by omega) ?_
  intro v₂ m₂ hp₂
  obtain ⟨_, _, _, heq₂, hv₂, hm₂⟩ := hp₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  subst hv₂
  subst m₂
  have hw2 := upd_words_val (i := 40 + 1) hw1 hLBw
  -- 3. the stretch pass
  refine SeqPreCont.cons hmono [X.n, X.tM, X.m0, X.k, LB, X.Lw, X.Lin, X.nOrig, 0, X.logCap, X.lenArr,
      tOrigIdBase X.tPtr X.vCap X.tM, X.qOrd, X.auxPar, X.auxPar + X.n,
      tPiBase X.tPtr X.vCap X.tM, X.thBase + 7 * X.n, X.eu, X.ev, X.auxPar + 3 * X.n,
      X.auxPar + X.n + X.n, dgEListBase X.gPtr X.vCap X.eCap, X.numS, X.denS, X.idPtr] c3 rfl
    (words_of_map fun j hj => hw2 j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega))
    (decompPhase_wstrPre I fun a ha => hfr₁ a (Or.inl ha))
    (by rw [wstrStage_cost_eq]; simp only [List.length_cons, List.length_nil]; omega) (by omega) ?_
  intro v₃ m₃ hp₃
  obtain ⟨hv₃, hW⟩ := hp₃
  change v₃ = wsPt X.idPtr X.n X.tM X.m0 LB 18 at hv₃
  subst hv₃
  rw [wstrStageArgs_eq] at hW
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, heqW, -, hWP⟩ := hW
  simp only [List.cons.injEq, and_true] at heqW
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := heqW
  obtain ⟨_, -, -, -, -, -, -, hfrW, -, hedge⟩ := hWP
  have hm₃ : ∀ a < X.numS, m₃ a = m₁ a := fun a ha =>
    hfrW a (by omega) fun t _ => ⟨Or.inl (by omega), Or.inl (by omega)⟩
  have hflag : ∀ t < X.m0, m₃ (wsPt X.idPtr X.n X.tM X.m0 LB 18 + t) ≤ 1 := fun t ht =>
    wstrEdgeOut_ret_le (hedge t ht)
  have hw3 := upd_words_val (i := 40 + 2) hw2 (show wsPt X.idPtr X.n X.tM X.m0 LB 18 < 2 ^ w by
    omega)
  -- 4. copy the flags down
  refine SeqPreCont.cons hmono [X.hiCopy, wsPt X.idPtr X.n X.tM X.m0 LB 18, X.m0] c4 rfl
    (words_of_map fun j hj => hw3 j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega))
    ⟨_, _, _, rfl, by omega, by omega, Or.inl (by omega)⟩
    (by simp [memCopyContract]; omega) (by omega) ?_
  intro v₄ m₄ hp₄
  obtain ⟨_, _, _, heq₄, -, hcp, hfr₄⟩ := hp₄
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl⟩ := heq₄
  have hw4 := upd_words (i := 40 + 3) (v := v₄) hw3 (by omega)
  have hlow : ∀ a < X.dBase, m₄ a = mem a := fun a ha => by
    rw [hfr₄ a (Or.inl (by omega)), hm₃ a (by omega), hfr₁ a (Or.inl ha)]
  have hbnd : ∀ y < X.n, m₄ (X.dBase + 11 * X.n + y) = m₁ (X.dBase + 11 * X.n + y) :=
    fun y hy => by rw [hfr₄ _ (Or.inl (by omega)), hm₃ _ (by omega)]
  -- 5. the merged flags
  refine SeqPreCont.cons hmono [X.n, X.cnt, X.m0, X.dBase + 11 * X.n, X.repPtr, X.vIdx, X.hiCopy, X.eu,
      X.ev, X.inR] c5 rfl
    (words_of_map fun j hj => hw4 j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega))
    ⟨X.n, X.cnt, X.m0, X.dBase + 11 * X.n, X.repPtr, X.vIdx, X.hiCopy, X.eu, X.ev, X.inR, rfl,
      I.hw16, by omega, by omega, by omega, by omega, by omega, by omega,
      fun y hy => by rw [hbnd y hy]; exact decompWTOut_bnd_le hOut hQ hQat hn y hy,
      fun j hj => by
        have hr := I.hrep j hj
        unfold repIdx at hr ⊢
        rw [hlow (X.repPtr + j) (by omega), hlow _ (by omega)]
        exact ⟨by omega, hr.2⟩,
      fun t ht => ⟨by rw [hcp t ht]; exact hflag t ht,
        by rw [hlow _ (by omega)]; exact (I.heuv t ht).1,
        by rw [hlow _ (by omega)]; exact (I.heuv t ht).2⟩⟩
    (by simp [flagMergeContract]; omega) (by omega) ?_
  intro v₅ m₅ hp₅
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₅, -, hfr₅, hval₅⟩ := hp₅
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  have hw5 := upd_words (i := 40 + 4) (v := v₅) hw4 (by omega)
  have hlow₅ : ∀ a < X.dBase, m₅ a = mem a := fun a ha => by
    rw [hfr₅ a (Or.inl (by omega)), hlow a ha]
  obtain ⟨hPD, hDle, -⟩ := thArrays_parDep (dep := fun x => mem (X.thBase + 7 * X.n + x))
    (par := fun x => mem (X.thDst + x)) I.hT I.hnd I.hV I.hvlen hn I.hthPar I.hthDep
  -- 6. the closure of the roots and the arrays of `F`
  refine SeqPreCont.cons hmono [X.n, X.tM, 0, X.qOrd, X.auxPar, X.auxPar + X.n, tPiBase X.tPtr X.vCap X.tM,
      X.thDst, X.thBase + 7 * X.n, X.D, X.inR, X.inR + X.n, X.inR + X.n + X.n,
      X.inR + X.n + X.n + X.tM] c6 rfl
    (words_of_map fun j hj => hw5 j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega))
    ⟨X.n, X.tM, 0, X.qOrd, X.auxPar, X.auxPar + X.n, tPiBase X.tPtr X.vCap X.tM, X.thDst,
      X.thBase + 7 * X.n, X.D, X.inR, X.inR + X.n, X.inR + X.n + X.n, X.inR + X.n + X.n + X.tM, Q,
      rfl, I.hw16, hn, hQ.congr fun x hx => (hlow₅ _ (by omega)).symm,
      hQat.congr fun k hk1 hk2 => hlow₅ k (by rw [hQ.len] at hk2; omega),
      fun x hx hx0 => by rw [hlow₅ _ (by omega)]; exact (hRA.step x hx hx0).1,
      hPD.congr (fun x hx => hlow₅ _ (by omega)) (fun x hx => hlow₅ _ (by omega)),
      fun x hx => by rw [hlow₅ _ (by omega), I.hD]; exact hDle x hx,
      fun x hx => by rw [hval₅ x hx]; split_ifs <;> omega,
      by
        rw [hval₅ 0 hn]
        split_ifs with hc
        · rfl
        exfalso; apply hc
        obtain ⟨j, hj, hj0⟩ := I.hroot
        refine Or.inr (Or.inl ⟨j, hj, ?_⟩)
        have hr := I.hrep j hj
        unfold repIdx at hj0 ⊢
        rw [hlow (X.repPtr + j) (by omega), hlow _ (by omega)]
        exact hj0,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
    (by simp [rootsStageContract]; omega) (by omega) ?_
  intro v₆ m₆ hp₆
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₆, -, hfr₆, -⟩ := hp₆
  simp only [List.cons.injEq, and_true] at heq₆
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₆
  have hlow₆ : ∀ a < X.dBase, m₆ a = mem a := fun a ha => by
    rw [hfr₆ a (Or.inl (by omega)) (Or.inl (by omega)), hlow₅ a ha]
  have hEt₆ : ∀ t < X.m0, (m₆ (dgEListBase X.gPtr X.vCap X.eCap + t) + 1) * X.Lw ≤ X.eCap * X.Lw := by
    intro t ht
    rw [hlow₆ _ (by omega)]
    exact Nat.mul_le_mul_right X.Lw (I.heLt t ht)
  have hLw1 : 1 ≤ X.Lw := le_trans I.hLin1 I.hLinw
  have hLwW : X.Lw < 2 ^ w := hgd 10
  show decompCopyPre w _ m₆ _
  rw [hB]
  dsimp only [decompCopyPre]
  simp (disch := omega) only [Function.update_of_ne]
  simp only [DecompLayout.args, List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨⟨I.hw16, hLw1, hLwW, L4s, by omega, by omega, hEt₆⟩,
    ⟨I.hw16, hLw1, hLwW, by omega, by omega, by omega, hEt₆⟩,
    L13, by omega, by omega, by omega⟩

/-- The post of the decomposition phase, call by call, with the arguments written out. -/
theorem decompPhase_post {w h C : ℕ} {X : DecompLayout} {bWT bLB bW bCopy bFlag bRoots : ℕ}
    {K : List ℕ → (ℕ → ℕ) → ℕ} {mem mem₈ : ℕ → ℕ} {ret : ℕ}
    (hpost : (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots K).post X.args mem ret mem₈) :
    ∃ (v₁ : ℕ) (m₁ m₃ : ℕ → ℕ) (v₄ : ℕ) (m₄ : ℕ → ℕ) (v₅ : ℕ) (m₅ : ℕ → ℕ) (v₆ : ℕ)
      (m₆ : ℕ → ℕ) (_v₇ : ℕ) (m₇ : ℕ → ℕ) (_v₈ : ℕ),
      (decompWTContract w).post [X.n, X.m0, X.eu, X.ev, X.qOrd, X.auxPar, 0, X.θ, X.dBase] mem
        v₁ m₁ ∧
      (wstrStageContract w h C).post [X.n, X.tM, X.m0, X.k, wstrLB X.n X.D X.Lw, X.Lw, X.Lin,
        X.nOrig, 0, X.logCap, X.lenArr, tOrigIdBase X.tPtr X.vCap X.tM, X.qOrd, X.auxPar,
        X.auxPar + X.n, tPiBase X.tPtr X.vCap X.tM, X.thBase + 7 * X.n, X.eu, X.ev,
        X.auxPar + 3 * X.n, X.auxPar + X.n + X.n, dgEListBase X.gPtr X.vCap X.eCap, X.numS,
        X.denS, X.idPtr] m₁ (wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18) m₃ ∧
      (memCopyContract w).post [X.hiCopy, wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18,
        X.m0] m₃ v₄ m₄ ∧
      (flagMergeContract w).post [X.n, X.cnt, X.m0, X.dBase + 11 * X.n, X.repPtr, X.vIdx,
        X.hiCopy, X.eu, X.ev, X.inR] m₄ v₅ m₅ ∧
      (rootsStageContract w).post [X.n, X.tM, 0, X.qOrd, X.auxPar, X.auxPar + X.n,
        tPiBase X.tPtr X.vCap X.tM, X.thDst, X.thBase + 7 * X.n, X.D, X.inR, X.inR + X.n,
        X.inR + X.n + X.n, X.inR + X.n + X.n + X.tM] m₅ v₆ m₆ ∧
      wstrCopyEdgesPost X.numSt X.numS (dgEListBase X.gPtr X.vCap X.eCap) X.m0 X.Lw (X.eCap * X.Lw)
        m₆ m₇ ∧
      wstrCopyEdgesPost X.denSt X.denS (dgEListBase X.gPtr X.vCap X.eCap) X.m0 X.Lw (X.eCap * X.Lw)
        m₇ mem₈ := by
  obtain ⟨v₁, m₁, h₁, v₂, m₂, h₂, v₃, m₃, h₃, v₄, m₄, h₄, v₅, m₅, h₅, v₆, m₆, h₆,
    m₇, h₇, h₈, -⟩ := hpost
  obtain ⟨_, _, _, heq, hv₂, hm₂⟩ := h₂
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  subst hv₂
  subst m₂
  have hv₃ : v₃ = wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18 := h₃.1
  subst hv₃
  simp (disch := omega) only [Function.update_of_ne] at h₇ h₈
  simp only [DecompLayout.args, List.getD_cons_zero, List.getD_cons_succ] at h₇ h₈
  exact ⟨v₁, m₁, m₃, v₄, m₄, v₅, m₅, v₆, m₆, 0, m₇, 0, h₁, h₃, h₄, h₅, h₆, h₇, h₈⟩

end

end MinCostFlow.LSF.Program
