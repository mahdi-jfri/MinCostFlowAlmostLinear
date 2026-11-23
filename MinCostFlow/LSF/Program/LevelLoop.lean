module

public import MinCostFlow.LSF.Program.LevelStep

/-!
# All levels of the stretch sum

`levelsProc` runs `levelStepProc` for the levels `i = 0, …, K - 1`. Its post gives, for each
level, roots `rts i` with `LevelRt` for the flags of that level, lowest common ancestors
`lxs i x` of `x` and `rts i x`, and the accumulators as the fold `accFold` of `accLevelVal` over
the levels. The cost is `O(K (n + tM + m0 LB))`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

@[expose] public section

/-- `LevelRt` depends only on the arrays at the indices it reads. -/
lemma levelRt_congr {n tM r : ℕ} {par pe piv inR rt par' pe' piv' inR' : ℕ → ℕ}
    (h : LevelRt n tM r par pe piv inR rt) (hpar_lt : ∀ x < n, par x < n)
    (hpe_lt : ∀ x < n, x ≠ r → pe x < tM) (hinr : inR r = 1)
    (hpar : ∀ x < n, par' x = par x) (hpe : ∀ x < n, pe' x = pe x)
    (hpiv : ∀ j < tM, piv' j = piv j) (hin : ∀ x < n, inR' x = inR x) :
    LevelRt n tM r par' pe' piv' inR' rt := by
  obtain ⟨mp, own, hmp, hown, hrt_r, hrt⟩ := h
  refine ⟨mp, own, fun x hx hxr => ⟨(hmp x hx hxr).1, ?_⟩, ownState_congr hin (fun _ _ => rfl) hown,
    hrt_r, fun x hx hxr => ?_⟩
  · have hm := (hmp x hx hxr).2
    have hpx := hpar_lt x hx
    unfold MpRule at hm ⊢
    rw [hpar x hx, hpe x hx, hin _ hpx]
    by_cases h1 : inR (par x) = 1
    · rw [if_pos h1] at hm ⊢; exact hm
    · have hpr : par x ≠ r := fun h' => h1 (h' ▸ hinr)
      rw [if_neg h1] at hm ⊢
      rw [hpiv _ (hpe_lt x hx hxr), hpiv _ (hmp _ hpx hpr).1]
      exact hm
  · have hr := hrt x hx hxr
    unfold RtRule at hr ⊢
    rw [hin x hx, hpar x hx, hpe x hx]; exact hr

/-- The accumulator of edge position `t` after the levels below `k`. -/
def accFold (h LB : ℕ) (mem : ℕ → ℕ) (euPtr evPtr ldBase duvBase accBase : ℕ)
    (rts lxs : ℕ → ℕ → ℕ) (t : ℕ) : ℕ → ℕ
  | 0 => unsignedVal mem (accBase + t * LB) h LB
  | k + 1 =>
    let u := mem (euPtr + t)
    let v := mem (evPtr + t)
    accLevelVal (capacity h LB)
      (accFold h LB mem euPtr evPtr ldBase duvBase accBase rts lxs t k)
      (unsignedVal mem (duvBase + t * LB) h LB) (dRVal h LB mem ldBase (rts k) (lxs k) u)
      (dRVal h LB mem ldBase (rts k) (lxs k) v) (rts k u) (rts k v)

lemma accFold_congr {h LB : ℕ} {mem : ℕ → ℕ} {euPtr evPtr ldBase duvBase accBase t : ℕ}
    {rts lxs rts' lxs' : ℕ → ℕ → ℕ} : ∀ K, (∀ k < K, rts' k = rts k ∧ lxs' k = lxs k) →
      accFold h LB mem euPtr evPtr ldBase duvBase accBase rts' lxs' t K =
        accFold h LB mem euPtr evPtr ldBase duvBase accBase rts lxs t K
  | 0, _ => rfl
  | K + 1, hk => by
    simp only [accFold]
    rw [accFold_congr K (fun k hk' => hk k (by omega)), (hk K (by omega)).1, (hk K (by omega)).2]

/-- Args: `[K, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr, rtPtr, tM, r, m0,
euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap, upPtr, depPtr]`. Register
`25` is the level `i`. -/
def levelsProc (bStep : ℕ) : Stmt :=
  forRange 25 (.const 0) (.reg 0)
    (.call 26 bStep [.reg 25, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8,
      .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .reg 16, .reg 17, .reg 18,
      .reg 19, .reg 20, .reg 21, .reg 22, .reg 23, .reg 24]) ;;
  .ret (.const 0)

lemma levelsProc_noRand (bStep : ℕ) : (levelsProc bStep).NoRand := by
  simp [levelsProc, forRange, forUp, Stmt.NoRand]

/-- The contract of `levelsProc`. -/
def levelsContract (w h : ℕ) : Contract where
  pre args mem := ∃ (K n qPtr parPtr pePtr piPtr thDepPtr inRPtr mpPtr ownPtr rtPtr tM r m0
      euPtr evPtr ldBase duvBase accBase LB idPtr dRBase logCap upPtr depPtr : ℕ),
    args = [K, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr, rtPtr, tM, r,
      m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap, upPtr, depPtr] ∧
    K + 1 < 2 ^ w ∧
    LevelStepPre w h mem 0 n qPtr parPtr pePtr piPtr thDepPtr inRPtr mpPtr ownPtr rtPtr tM r m0
      euPtr evPtr ldBase duvBase accBase LB idPtr dRBase logCap upPtr depPtr
  post args mem ret mem' := ∃ (K n qPtr parPtr pePtr piPtr thDepPtr inRPtr mpPtr ownPtr rtPtr
      tM r m0 euPtr evPtr ldBase duvBase accBase LB idPtr dRBase logCap upPtr depPtr : ℕ),
    args = [K, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr, rtPtr, tM, r,
      m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap, upPtr, depPtr] ∧
    ret = 0 ∧ (∀ a, a < inRPtr ∨ accBase + m0 * LB ≤ a → mem' a = mem a) ∧
    ∃ rts lxs : ℕ → ℕ → ℕ,
      (∀ k < K, LevelRt n tM r (fun x => mem (parPtr + x)) (fun x => mem (pePtr + x))
        (fun j => mem (piPtr + j)) (levelFlag mem thDepPtr k) (rts k)) ∧
      (∀ (tl hd dep : ℕ → ℕ),
        RootedArrays n tM r tl hd (fun x => mem (parPtr + x)) (fun x => mem (pePtr + x)) dep →
        LcaTables w n logCap upPtr depPtr parPtr (fun x => mem (parPtr + x)) dep mem →
        ∀ k < K, ∀ x < n,
          lxs k x < n ∧ IsLcaOf (fun y => mem (parPtr + y)) dep (lxs k x) x (rts k x)) ∧
      ∀ t < m0, Valid mem' (accBase + t * LB) h LB ∧
        unsignedVal mem' (accBase + t * LB) h LB =
          accFold h LB mem euPtr evPtr ldBase duvBase accBase rts lxs t K
  cost args _ := args.getD 0 0 * (400 * args.getD 1 0 + 30 * args.getD 11 0 +
    args.getD 1 0 * (100 * args.getD 22 0 + 400 * args.getD 19 0 + 400) +
    args.getD 13 0 * (150 * args.getD 19 0 + 160) + 600) + 20

theorem levels_meetsContract {w h : ℕ} {p : Program} {b bStep : ℕ}
    (hStep : MeetsContract w p bStep (levelStepContract w h))
    (hp : p.procs[b]? = some (levelsProc bStep)) :
    MeetsContract w p b (levelsContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨K, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr, rtPtr, tM, r, m0,
    euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap, upPtr, depPtr, rfl, hK,
    hpre0⟩ := hpre
  obtain ⟨h16, hn, ⟨Q, tl, hd, dep, hQ, hQat, hRA, hLT⟩, hid, hida, hupa, hdepa, hth, -, hend, hld,
    hblk, hqa, hpa, hpea, hpia, hta, heua, heva, hlda, hduva, hia, hma, hoa, hra, hdRa,
    hacw⟩ := hpre0
  set args := [K, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr, rtPtr, tM, r,
    m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap, upPtr, depPtr]
    with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hKw : K < 2 ^ w := by omega
  have hrn : r < n := hQ.lt r (by rw [← hQ.head_eq hn]; exact List.getElem_mem _)
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set pe : ℕ → ℕ := fun x => mem (pePtr + x) with hpe
  set piv : ℕ → ℕ := fun j => mem (piPtr + j) with hpiv
  set F : (ℕ → ℕ → ℕ) → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ :=
    fun rts lxs t k => accFold h LB mem euPtr evPtr ldBase duvBase accBase rts lxs t k with hF
  set C : ℕ := 400 * n + 30 * tM + n * (100 * logCap + 400 * LB + 400) +
    m0 * (150 * LB + 160) + 500 with hC
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ k < 25, st.regs k = args.getD k 0) ∧ st.regs 25 = i ∧
    (∀ a, a < inRPtr ∨ accBase + m0 * LB ≤ a → st.mem a = mem a) ∧
    ∃ rts lxs : ℕ → ℕ → ℕ,
      (∀ k < i, LevelRt n tM r par pe piv (levelFlag mem thDepPtr k) (rts k)) ∧
      (∀ (tl hd dep : ℕ → ℕ), RootedArrays n tM r tl hd par pe dep →
        LcaTables w n logCap upPtr depPtr parPtr par dep mem →
        ∀ k < i, ∀ x < n, lxs k x < n ∧ IsLcaOf par dep (lxs k x) x (rts k x)) ∧
      ∀ t < m0, Valid st.mem (accBase + t * LB) h LB ∧
        unsignedVal st.mem (accBase + t * LB) h LB = F rts lxs t i
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 25 (.const 0) (.reg 0)
        (.call 26 bStep [.reg 25, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8,
          .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .reg 16, .reg 17, .reg 18,
          .reg 19, .reg 20, .reg 21, .reg 22, .reg 23, .reg 24]))
      (normalPost (Inv K))
      (fun _ => (K - 0) * ((C + 90) + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const (C + 90) 0 K (by omega) hw1 (fun _ => hKw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun k hk => ?_, by simp, fun a _ => rfl,
        fun _ _ => 0, fun _ _ => 0, fun k hk => absurd hk (by omega),
        fun _ _ _ _ _ k hk => absurd hk (by omega), fun t ht => ⟨(hblk t ht).2, rfl⟩⟩
      simp only [Function.update_of_ne (show k ≠ 25 by omega)]
      interval_cases k <;> simp [startState, hargs]
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = K := hI.1 0 (by omega)
      eval_expr
    · intro i _ hiK st ω' hI
      obtain ⟨hR, h25, hfr, rts, lxs, hrts, hlxs, hacc⟩ := hI
      have hlow : ∀ a, a < inRPtr → st.mem a = mem a := fun a ha => hfr a (Or.inl ha)
      have hQs : TopDownOrder n r (fun x => st.mem (parPtr + x)) Q :=
        hQ.congr fun x hx => (hlow _ (by omega)).symm
      have hQats : ListAt st.mem qPtr Q :=
        hQat.congr fun k hk1 hk2 => hlow k (by rw [hQ.len] at hk2; omega)
      have hRAs : RootedArrays n tM r tl hd (fun x => st.mem (parPtr + x))
          (fun x => st.mem (pePtr + x)) dep :=
        hRA.congr hrn (fun x hx => (hlow _ (by omega)).symm) (fun x hx => (hlow _ (by omega)).symm)
          (fun _ _ => rfl)
      have hLTs : LcaTables w n logCap upPtr depPtr parPtr (fun x => st.mem (parPtr + x)) dep
          st.mem :=
        (hLT.of_agree (B := inRPtr) hlow hupa hdepa (by omega)).congr hRA
          (fun x hx => (hlow _ (by omega)).symm) (fun _ _ => rfl)
      have hblkL : ∀ x < n, ∀ j < LB, st.mem (ldBase + x * LB + j) = mem (ldBase + x * LB + j) :=
        fun x hx j hj => hlow _ (by have := blk_end LB hx; omega)
      have hblkD : ∀ t < m0, ∀ j < LB,
          st.mem (duvBase + t * LB + j) = mem (duvBase + t * LB + j) :=
        fun t ht j hj => hlow _ (by have := blk_end LB ht; omega)
      have hargsw : ∀ v ∈ [i, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr,
          rtPtr, tM, r, m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap,
          upPtr, depPtr], v < 2 ^ w := by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · omega
        · exact hwords v (List.mem_cons_of_mem _ hv)
      have hev : evalArgs w st [.reg 25, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
          .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .reg 16, .reg 17,
          .reg 18, .reg 19, .reg 20, .reg 21, .reg 22, .reg 23, .reg 24] =
          some [i, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr, ownPtr, rtPtr, tM, r,
            m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase, logCap, upPtr,
            depPtr] := by
        have e : ∀ k < 25, st.regs k = args.getD k 0 := hR
        simp only [evalArgs, Expr.eval, h25, e 1 (by omega), e 2 (by omega), e 3 (by omega),
          e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega),
          e 9 (by omega), e 10 (by omega), e 11 (by omega), e 12 (by omega), e 13 (by omega),
          e 14 (by omega), e 15 (by omega), e 16 (by omega), e 17 (by omega), e 18 (by omega),
          e 19 (by omega), e 20 (by omega), e 21 (by omega), e 22 (by omega), e 23 (by omega),
          e 24 (by omega), hargs, List.getD_cons_zero, List.getD_cons_succ]
      refine runs_start_le ?_
      refine runs_call_le (vs := [i, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr, mpPtr,
          ownPtr, rtPtr, tM, r, m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase,
          logCap, upPtr, depPtr]) hStep hev hargsw
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, h16, hn,
          ⟨Q, tl, hd, dep, hQs, hQats, hRAs, hLTs⟩,
          fun x hx => by rw [hlow _ (by omega)]; exact hid x hx, hida, hupa, hdepa,
          by rw [hlow _ (by omega)]; exact hth, by omega,
          fun t ht => by rw [hlow _ (by omega), hlow _ (by omega)]; exact hend t ht,
          fun x hx j hj => by rw [hblkL x hx j hj]; exact hld x hx j hj,
          fun t ht => ⟨fun j hj => by rw [hblkD t ht j hj]; exact (hblk t ht).1 j hj,
            (hacc t ht).1⟩,
          hqa, hpa, hpea, hpia, hta, heua, heva, hlda, hduva, hia, hma, hoa, hra, hdRa, hacw⟩ ?_
      rintro v₁ mem₁ pos₁ ⟨i₁, n₁, a₁, b₁, c₁, d₁, e₁, f₁, g₁, j₁, k₁, l₁, m₁, o₁, q₁, s₁, u₁,
        x₁, y₁, z₁, a₂, b₂, c₂, d₂, e₂, heq₁, -, hfr₁, rt, lx, hLR, hlx, hacc₁⟩
      simp only [List.cons.injEq, and_true] at heq₁
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
      have hLR' : LevelRt n tM r par pe piv (levelFlag mem thDepPtr i) rt := by
        refine levelRt_congr hLR (fun x hx => hRAs.par_lt x hx)
          (fun x hx hxr => (hRAs.step x hx hxr).1) ?_ (fun x hx => (hlow _ (by omega)).symm)
          (fun x hx => (hlow _ (by omega)).symm) (fun j hj => (hlow _ (by omega)).symm)
          (fun x hx => by simp only [levelFlag]; rw [hlow _ (by omega)])
        simp only [levelFlag]; rw [hlow _ (by omega), hth]; simp
      have hrt_lt := levelRt_lt hRA hrn hLR'
      have hlx_lt : ∀ x < n, lx x < n := fun x hx => (hlx tl hd dep hRAs hLTs x hx).1
      set rts' : ℕ → ℕ → ℕ := fun k => if k < i then rts k else rt with hrts'
      set lxs' : ℕ → ℕ → ℕ := fun k => if k < i then lxs k else lx with hlxs'
      refine ⟨⟨⟨fun k hk => ?_, ?_, fun a ha => ?_, rts', lxs', fun k hk => ?_,
        fun tl' hd' dep' hRA' hLT' k hk x hx => ?_, fun t ht => ?_⟩, ?_⟩, ?_⟩
      · dsimp only
        rw [Function.update_of_ne (show k ≠ 25 by omega), Function.update_of_ne (show k ≠ 26 by omega)]
        exact hR k hk
      · simp
      · dsimp only
        rw [hfr₁ a ha]; exact hfr a ha
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · simp only [hrts', if_pos hk]; exact hrts k hk
        · simp only [hrts', lt_irrefl, if_false]; exact hLR'
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · simp only [hrts', hlxs', if_pos hk]; exact hlxs tl' hd' dep' hRA' hLT' k hk x hx
        · simp only [hrts', hlxs', lt_irrefl, if_false]
          have hdd := rootedArrays_dep_eq hRAs (hRA'.congr hrn
            (fun y hy => (hlow _ (by omega)).symm) (fun y hy => (hlow _ (by omega)).symm)
            (fun _ _ => rfl))
          obtain ⟨h1, h2⟩ := hlx tl hd dep hRAs hLTs x hx
          exact ⟨h1, (isLcaOf_congr (n := n) (fun y hy => hlow _ (by omega)) hdd
            (fun y hy => hRAs.par_lt y hy) hx (hrt_lt x hx) h1).mp h2⟩
      · refine ⟨(hacc₁ t ht).1, ?_⟩
        dsimp only
        rw [(hacc₁ t ht).2]
        obtain ⟨hut, hvt⟩ := hend t ht
        have hacc' : unsignedVal st.mem (accBase + t * LB) h LB =
            accFold h LB mem euPtr evPtr ldBase duvBase accBase rts lxs t i := (hacc t ht).2
        have hdRV : ∀ z < n, dRVal h LB st.mem ldBase rt lx z = dRVal h LB mem ldBase rt lx z :=
          fun z hz => by
            simp only [dRVal]
            rw [unsignedVal_congr (hblkL z hz), unsignedVal_congr (hblkL _ (hrt_lt z hz)),
              unsignedVal_congr (hblkL _ (hlx_lt z hz))]
        simp only [accStepVal, hF, accFold]
        rw [accFold_congr (rts := rts) (lxs := lxs) (rts' := rts') (lxs' := lxs') i
          (fun k hk => by simp only [hrts', hlxs', if_pos hk, and_self]), hacc']
        simp only [hrts', hlxs', lt_irrefl, if_false]
        rw [hlow (euPtr + t) (by omega), hlow (evPtr + t) (by omega),
          unsignedVal_congr (hblkD t ht), hdRV _ hut, hdRV _ hvt]
      · show Function.update st.regs 26 v₁ 25 = i
        rw [Function.update_of_ne (show (25 : ℕ) ≠ 26 by omega)]; exact h25
      · simp only [levelStepContract, List.getD_cons_zero, List.getD_cons_succ, argsSize,
          Expr.size_reg]
        omega
  refine runs_start_le ?_
  unfold levelsProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, hfr, rts, lxs, hrts, hlxs, hacc⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨K, n, qPtr, parPtr, pePtr, piPtr, thDepPtr, inRPtr,
    mpPtr, ownPtr, rtPtr, tM, r, m0, euPtr, evPtr, ldBase, duvBase, accBase, LB, idPtr, dRBase,
    logCap, upPtr, depPtr, rfl, rfl, hfr, rts, lxs, hrts, hlxs, hacc⟩ ?_
  simp only [levelsContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
    Expr.size_reg]
  have h1 : (K - 0) * (C + 90 + 1 + 8) ≤ K * (400 * n + 30 * tM +
      n * (100 * logCap + 400 * LB + 400) + m0 * (150 * LB + 160) + 600) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega
end

end MinCostFlow.LSF.Program
