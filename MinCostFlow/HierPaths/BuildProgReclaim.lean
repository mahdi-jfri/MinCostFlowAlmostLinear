module

public import MinCostFlow.HierPaths.BuildProgReclaimHoles
import MinCostFlow.HierPaths.InitLayout

/-!
# Reclaiming scratch memory while skipping sorted zero holes

Proves `buildReclaimHolesProc_meetsContract`: copies `sec0 ++ sec1` down to `h + 4` and zeroes all
reclaimed scratch while skipping the sorted `G.n`-word zero holes collected by
`buildCollectHolesProc`, keeping the running time independent of `G.n`.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

private theorem holesValid_ge_mul {gn lo hi : ℕ} {holes : List ℕ} {mem : ℕ → ℕ}
    (hV : HolesValid gn lo hi holes mem) :
    ∀ i (hi' : i < holes.length), lo + i * gn ≤ holes[i]'hi' := by
  intro i
  induction i with
  | zero => intro hi'; simpa using (hV.1 0 hi').1
  | succ i ih =>
    intro hi'
    have h1 := ih (by omega)
    have h2 := hV.2 i hi'
    rw [Nat.succ_mul]
    omega

private theorem holesValid_mono {gn lo hi : ℕ} {holes : List ℕ} {mem : ℕ → ℕ}
    (hV : HolesValid gn lo hi holes mem) :
    ∀ i j (hi' : i < holes.length) (hj' : j < holes.length), i < j →
      holes[i]'hi' + gn ≤ holes[j]'hj' := by
  intro i j hi' hj' hlt
  have hgen : ∀ d (hd : i + 1 + d < holes.length),
      holes[i]'hi' + gn ≤ holes[i + 1 + d]'hd := by
    intro d
    induction d with
    | zero => intro hd; exact hV.2 i hd
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := hV.2 (i + 1 + d) (by omega)
      have hidx : holes[i + 1 + (d + 1)]'hd = holes[(i + 1 + d) + 1]'(by omega) := by
        congr 1
      rw [hidx]; omega
  simpa [show i + 1 + (j - (i + 1)) = j by omega] using hgen (j - (i + 1)) (by omega)

private theorem reclaimCur_mono (holes : List ℕ) (gn start0 : ℕ) (i : ℕ) :
    start0 ≤ reclaimCur holes gn start0 i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih => exact ih.trans (le_max_left _ _)

private theorem reclaimCur_le_hi {gn lo hi start0 : ℕ} {holes : List ℕ} {mem : ℕ → ℕ}
    (hV : HolesValid gn lo hi holes mem) (hStart : start0 ≤ hi) :
    ∀ i ≤ holes.length, reclaimCur holes gn start0 i ≤ hi := by
  intro i
  induction i with
  | zero => intro _; exact hStart
  | succ i ih =>
    intro hi'
    dsimp [reclaimCur]
    have h1 := ih (Nat.le_of_succ_le hi')
    have h2 : holes.getD i 0 + gn ≤ hi := by
      rw [List.getD_eq_getElem _ _ hi']; exact (hV.1 i hi').2.1
    exact max_le h1 h2

private theorem reclaim_gap_sum_le {gn h hi start0 : ℕ} {holes : List ℕ} {mem : ℕ → ℕ}
    (hV : HolesValid gn h hi holes mem) (hLo : h ≤ start0) (hHi : start0 ≤ hi) :
    rangeCost (reclaimGap holes gn start0) 0 holes.length +
      (hi - reclaimCur holes gn start0 holes.length) + holes.length * gn ≤ hi - h := by
  have hgen : ∀ n ≤ holes.length,
      rangeCost (reclaimGap holes gn start0) 0 n + n * gn ≤
        reclaimCur holes gn start0 n - h ∧
      (rangeCost (reclaimGap holes gn start0) 0 n = 0 ∨
        ∀ j (hj : j < holes.length), n ≤ j → reclaimCur holes gn start0 n ≤ holes[j]'hj) := by
    intro n
    induction n with
    | zero =>
      intro _
      simp [rangeCost, reclaimCur]
    | succ n ih =>
      intro hn
      obtain ⟨hSum, hDisj⟩ := ih (Nat.le_of_succ_le hn)
      have hRc : rangeCost (reclaimGap holes gn start0) 0 (n + 1) =
          rangeCost (reclaimGap holes gn start0) 0 n + reclaimGap holes gn start0 n := by
        rw [rangeCost_zero_eq_range, rangeCost_zero_eq_range, List.range_succ, List.map_append,
          List.sum_append, List.map_singleton, List.sum_singleton]
      have hpEq : holes.getD n 0 = holes[n]'hn := List.getD_eq_getElem _ _ hn
      have hpGe : h + n * gn ≤ holes[n]'hn := holesValid_ge_mul hV n hn
      have hCurGe : h ≤ reclaimCur holes gn start0 n := hLo.trans (reclaimCur_mono holes gn start0 n)
      rw [hRc, reclaimGap, hpEq, reclaimCur, hpEq]
      by_cases hlt : reclaimCur holes gn start0 n < holes[n]'hn
      · have hmax : max (reclaimCur holes gn start0 n) (holes[n]'hn + gn) = holes[n]'hn + gn :=
          max_eq_right (by omega)
        rw [hmax, Nat.succ_mul]
        refine ⟨by omega, Or.inr fun j hj hnj => ?_⟩
        exact holesValid_mono hV n j hn hj (by omega)
      · have hsub0 : holes[n]'hn - reclaimCur holes gn start0 n = 0 := by omega
        rw [hsub0, Nat.add_zero]
        rcases hDisj with hZ0 | hLeAll
        · rw [hZ0, Nat.zero_add]
          have h1 : h + (n + 1) * gn ≤ holes[n]'hn + gn := by rw [Nat.succ_mul]; omega
          have h2 : holes[n]'hn + gn ≤ max (reclaimCur holes gn start0 n) (holes[n]'hn + gn) :=
            le_max_right _ _
          exact ⟨by omega, Or.inl rfl⟩
        · have hLeN : reclaimCur holes gn start0 n ≤ holes[n]'hn := hLeAll n hn le_rfl
          have hEqCur : reclaimCur holes gn start0 n = holes[n]'hn := by omega
          have hmax : max (reclaimCur holes gn start0 n) (holes[n]'hn + gn) = holes[n]'hn + gn :=
            max_eq_right (by omega)
          rw [hmax, Nat.succ_mul]
          refine ⟨by omega, Or.inr fun j hj hnj => ?_⟩
          exact holesValid_mono hV n j hn hj (by omega)
  have h1 := (hgen holes.length le_rfl).1
  have h2 := reclaimCur_le_hi hV hHi holes.length le_rfl
  have h3 := hLo.trans (reclaimCur_mono holes gn start0 holes.length)
  omega

private theorem rangeCost_linear (f : ℕ → ℕ) (a b n : ℕ) :
    rangeCost (fun i => a * f i + b) 0 n = a * rangeCost f 0 n + n * b := by
  rw [rangeCost_zero_eq_range, rangeCost_zero_eq_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ih,
      Nat.mul_add, Nat.succ_mul]
    omega


private theorem reclaim_loop_triple {w fZero gn h outStart end1 dst total01 start0 : ℕ}
    {holes : List ℕ} {p : Program} {mem m1 : ℕ → ℕ}
    (hfZ : p.procs[fZero]? = some zeroProc)
    (hStartLe : start0 ≤ end1) (hOutLe : outStart ≤ end1)
    (hHolesAt : ListAt mem end1 holes) (hHolesV : HolesValid gn h outStart holes mem)
    (hM1Above : ∀ a, start0 ≤ a → m1 a = mem a)
    (htop : end1 + holes.length < 2 ^ w) (hw4 : 4 < 2 ^ w) :
    Triple w p
      (fun st =>
        st.regs 2 = end1 ∧ st.regs 3 = end1 ∧ st.regs 4 = holes.length ∧ st.regs 5 = gn ∧
        st.regs 6 = dst ∧ st.regs 7 = total01 ∧ st.regs 9 = start0 ∧ st.mem = m1)
      (forRange 10 (.const 0) (.reg 4)
        (.assign 11 (.load (.bin .add (.reg 3) (.reg 10))) ;;
         .cond (.bin .lt (.reg 9) (.reg 11))
           (.call 8 fZero [.reg 9, .bin .sub (.reg 11) (.reg 9)] ;;
            .assign 9 (.reg 11))
           .nop ;;
         .assign 12 (.bin .add (.reg 11) (.reg 5)) ;;
         .cond (.bin .lt (.reg 9) (.reg 12))
           (.assign 9 (.reg 12))
           .nop))
      (normalPost fun st =>
        st.regs 2 = end1 ∧ st.regs 3 = end1 ∧ st.regs 4 = holes.length ∧ st.regs 5 = gn ∧
        st.regs 6 = dst ∧ st.regs 7 = total01 ∧
        st.regs 9 = reclaimCur holes gn start0 holes.length ∧ st.regs 10 = holes.length ∧
        (∀ a < start0, st.mem a = m1 a) ∧
        (∀ a, start0 ≤ a → a < reclaimCur holes gn start0 holes.length → st.mem a = 0) ∧
        (∀ a, reclaimCur holes gn start0 holes.length ≤ a → st.mem a = m1 a))
      (fun _ => rangeCost (fun i => 15 * reclaimGap holes gn start0 i + 95) 0 holes.length +
        (holes.length - 0) * ((Expr.reg 4).size + 8) + ((Expr.const 0).size + (Expr.reg 4).size + 5)) := by
  have hZeroSpec := zeroProc_meetsContract (w := w) hfZ
  have hHolesEnd : HolesValid gn h end1 holes mem :=
    ⟨fun j hj => ⟨(hHolesV.1 j hj).1, (hHolesV.1 j hj).2.1.trans hOutLe, (hHolesV.1 j hj).2.2⟩,
     hHolesV.2⟩
  refine Triple.forRange_le (w := w) (p := p) (r := 10) (lo := .const 0) (hi := .reg 4)
    (Inv := fun i st =>
      st.regs 2 = end1 ∧ st.regs 3 = end1 ∧ st.regs 4 = holes.length ∧ st.regs 5 = gn ∧
      st.regs 6 = dst ∧ st.regs 7 = total01 ∧
      st.regs 9 = reclaimCur holes gn start0 i ∧ st.regs 10 = i ∧
      (∀ a < start0, st.mem a = m1 a) ∧
      (∀ a, start0 ≤ a → a < reclaimCur holes gn start0 i → st.mem a = 0) ∧
      (∀ a, reclaimCur holes gn start0 i ≤ a → st.mem a = m1 a))
    (fun i => 15 * reclaimGap holes gn start0 i + 95) 0 holes.length (Nat.zero_le _)
    (by omega) (fun _ => by omega)
    (fun st ⟨q2, q3, q4, q5, q6, q7, q9, qm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      refine ⟨by simpa using q2, by simpa using q3, by simpa using q4, by simpa using q5,
        by simpa using q6, by simpa using q7, by simpa [reclaimCur] using q9, by simp,
        fun _ _ => qm ▸ rfl, fun _ h1 h2 => by simp [reclaimCur] at h2; omega,
        fun _ _ => qm ▸ rfl⟩)
    (fun _ st _ _ hi' => hi'.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi' => by simp [Expr.eval, hi'.2.2.1])
    (fun i _ hi => by
      intro st ω' ⟨q2, q3, q4, q5, q6, q7, q9, q10, qBelow, qZero, qAbove⟩
      set cur := reclaimCur holes gn start0 i
      set pVal := holes[i]'hi
      have hpEq : holes.getD i 0 = pVal := List.getD_eq_getElem _ _ hi
      have hCurGe : start0 ≤ cur := reclaimCur_mono holes gn start0 i
      have hCurLe : cur ≤ end1 := reclaimCur_le_hi hHolesEnd hStartLe i (Nat.le_of_lt hi)
      have hpEnd : pVal + gn ≤ outStart := (hHolesV.1 i hi).2.1
      have hMp : st.mem (end1 + i) = pVal := by
        rw [qAbove _ (by omega), hM1Above _ (by omega)]
        exact hHolesAt i hi
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := pVal)
        (by rw [← hMp]; exact Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq q3)
              (Expr.eval_reg_of_eq q10) (by omega))) ?_
      have hFinish : ∀ (st2 : State) (cur1 k1 : ℕ),
          st2.regs 2 = end1 → st2.regs 3 = end1 → st2.regs 4 = holes.length → st2.regs 5 = gn →
          st2.regs 6 = dst → st2.regs 7 = total01 → st2.regs 9 = cur1 → st2.regs 10 = i →
          st2.regs 11 = pVal → cur1 = max cur pVal →
          (∀ a < start0, st2.mem a = m1 a) →
          (∀ a, start0 ≤ a → a < cur1 → st2.mem a = 0) →
          (∀ a, cur1 ≤ a → st2.mem a = m1 a) →
          k1 ≤ 15 * reclaimGap holes gn start0 i + 65 →
          ∃ o st' c, Runs w p ω'
            (.assign 12 (.bin .add (.reg 11) (.reg 5)) ;;
             .cond (.bin .lt (.reg 9) (.reg 12)) (.assign 9 (.reg 12)) .nop) st2 o st' c ∧
            normalPost (fun st₁ =>
              (st₁.regs 2 = end1 ∧ st₁.regs 3 = end1 ∧ st₁.regs 4 = holes.length ∧
               st₁.regs 5 = gn ∧ st₁.regs 6 = dst ∧ st₁.regs 7 = total01 ∧
               st₁.regs 9 = reclaimCur holes gn start0 (i + 1) ∧
               Function.update st₁.regs 10 (i + 1) 10 = i + 1 ∧
               (∀ a < start0, st₁.mem a = m1 a) ∧
               (∀ a, start0 ≤ a → a < reclaimCur holes gn start0 (i + 1) → st₁.mem a = 0) ∧
               (∀ a, reclaimCur holes gn start0 (i + 1) ≤ a → st₁.mem a = m1 a)) ∧
              st₁.regs 10 = i) o st' ∧
            k1 + c ≤ 15 * reclaimGap holes gn start0 i + 95 := by
        intro st2 cur1 k1 r2 r3 r4 r5 r6 r7 r9 r10 r11 hcur1 hb2 hz2 hAbove2 hk1
        have hNextCur : max cur1 (pVal + gn) = reclaimCur holes gn start0 (i + 1) := by
          rw [hcur1, reclaimCur, hpEq]; omega
        refine runs_seq_assign_le (v := pVal + gn)
          (Expr.eval_add (Expr.eval_reg_of_eq r11) (Expr.eval_reg_of_eq r5) (by omega)) ?_
        refine runs_cond_le (v := if cur1 < pVal + gn then 1 else 0)
          (Expr.eval_lt_op (Expr.eval_reg_of_eq (by simpa using r9))
            (Expr.eval_reg_of_eq (v := pVal + gn) (by simp)) (by omega)) ?_ ?_
        · intro hlt1
          have hlt2 : cur1 < pVal + gn := by split_ifs at hlt1 with h' <;> simp_all
          have hmaxEq : reclaimCur holes gn start0 (i + 1) = pVal + gn := by
            rw [← hNextCur]; exact max_eq_right (Nat.le_of_lt hlt2)
          refine runs_assign_le (v := pVal + gn) (Expr.eval_reg_of_eq (v := pVal + gn) (by simp)) ?_
            (by simp [Expr.size]; omega)
          refine ⟨⟨by simpa using r2, by simpa using r3, by simpa using r4, by simpa using r5,
            by simpa using r6, by simpa using r7, by simp [hmaxEq], by simp, hb2, ?_, ?_⟩,
            by simpa using r10⟩
          · intro a ha1 ha2
            rw [hmaxEq] at ha2
            by_cases hltA : a < cur1
            · exact hz2 a ha1 hltA
            · rw [hAbove2 a (by omega), hM1Above a ha1]
              have hEqA : pVal + (a - pVal) = a := by omega
              rw [← hEqA]
              exact (hHolesV.1 i hi).2.2 (a - pVal) (by omega)
          · intro a ha; rw [hmaxEq] at ha; exact hAbove2 a (by omega)
        · intro hge1
          have hge2 : pVal + gn ≤ cur1 :=
            Nat.le_of_not_lt fun hlt => by simp [hlt] at hge1
          have hmaxEq : reclaimCur holes gn start0 (i + 1) = cur1 := by
            rw [← hNextCur]; exact max_eq_left hge2
          refine runs_nop_le ?_ (by simp [Expr.size]; omega)
          exact ⟨⟨by simpa using r2, by simpa using r3, by simpa using r4, by simpa using r5,
            by simpa using r6, by simpa using r7, by simpa [hmaxEq] using r9, by simp,
            hb2, by simpa [hmaxEq] using hz2, by simpa [hmaxEq] using hAbove2⟩, by simpa using r10⟩
      refine runs_seq_cond_le (v := if cur < pVal then 1 else 0)
        (Expr.eval_lt_op (Expr.eval_reg_of_eq (by simpa using q9))
          (Expr.eval_reg_of_eq (v := pVal) (by simp)) (by omega)) ?_ ?_
      · intro hlt1
        have hlt2 : cur < pVal := by split_ifs at hlt1 with h' <;> simp_all
        have hGapEq : pVal - cur = reclaimGap holes gn start0 i := by rw [reclaimGap, hpEq]
        refine runs_seq_assoc_le ?_
        have hZeroPre : (zeroContract w).pre [cur, pVal - cur] st.mem :=
          ⟨cur, pVal - cur, rfl, by omega, by omega⟩
        refine runs_seq_call_le hZeroSpec (vs := [cur, pVal - cur])
          (by unfold evalArgs
              rw [Expr.eval_reg_of_eq (v := cur) (by simpa using q9)]
              unfold evalArgs
              rw [Expr.eval_sub (Expr.eval_reg_of_eq (v := pVal) (by simp))
                    (Expr.eval_reg_of_eq (v := cur) (by simpa using q9)) (by omega)]
              rfl)
          (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl <;> omega)
          hZeroPre ?_
        intro _ mNext _ hPostZ
        obtain ⟨_, _, heqZ, hZed, hFrZ⟩ := hPostZ
        simp only [List.cons.injEq, and_true] at heqZ
        obtain ⟨rfl, rfl⟩ := heqZ
        refine runs_seq_assign_le (v := pVal) (Expr.eval_reg_of_eq (v := pVal) (by simp)) ?_
        apply hFinish _ pVal _ (by simpa using q2) (by simpa using q3) (by simpa using q4)
          (by simpa using q5) (by simpa using q6) (by simpa using q7) (by simp)
          (by simpa using q10) (by simp) (max_eq_right (Nat.le_of_lt hlt2)).symm
          (fun a ha => (hFrZ a (Or.inl (by omega))).trans (qBelow a ha))
          (fun a ha1 ha2 => by
            by_cases hltC : a < cur
            · exact (hFrZ a (Or.inl hltC)).trans (qZero a ha1 hltC)
            · have hEqA : cur + (a - cur) = a := by omega
              rw [← hEqA]; exact hZed (a - cur) (by omega))
          (fun a ha => (hFrZ a (Or.inr (by omega))).trans (qAbove a (by omega)))
        simp only [zeroContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size, argsSize]
        omega
      · intro hge1
        have hge2 : pVal ≤ cur :=
          Nat.le_of_not_lt fun hlt => by simp [hlt] at hge1
        refine runs_seq_nop_le ?_
        refine hFinish _ cur _ (by simpa using q2) (by simpa using q3) (by simpa using q4)
          (by simpa using q5) (by simpa using q6) (by simpa using q7) (by simpa using q9)
          (by simpa using q10) (by simp) (max_eq_left hge2).symm qBelow qZero qAbove ?_
        simp only [Expr.size]; omega)

/-- `buildReclaimHolesProc` meets `buildReclaimHolesContract`. -/
theorem buildReclaimHolesProc_meetsContract {w f fCopy fZero gn : ℕ}
    {payload holes : List ℕ} {p : Program}
    (hf : p.procs[f]? = some (buildReclaimHolesProc fCopy fZero))
    (hfC : p.procs[fCopy]? = some buildCopyProc)
    (hfZ : p.procs[fZero]? = some zeroProc) :
    MeetsContract w p f (buildReclaimHolesContract w gn payload holes) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨h, outStart, end1, rfl, hOutGe, hEndEq, hPayAt, hHolesAt, hHolesV, hZF, htop, hw4⟩ := hPre
  set total01 := payload.length
  set dst := h + 4
  set start0 := dst + total01
  have hStartLe : start0 ≤ end1 := by dsimp [start0, dst, total01]; omega
  refine runs_start_le ?_
  unfold buildReclaimHolesProc
  refine runs_seq_assign_le (v := dst)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const hw4) (by omega)) ?_
  refine runs_seq_assign_le (v := total01)
    (by have hsub : end1 - outStart = total01 := by omega
        rw [← hsub]
        exact Expr.eval_sub (Expr.eval_reg_of_eq (by simp [startState]))
          (Expr.eval_reg_of_eq (by simp [startState])) (by omega)) ?_
  have hCopySpec := buildCopyProc_meetsDownContract (w := w) hfC
  have hCopyPre : (buildCopyDownContract w).pre [outStart, total01, dst] mem :=
    ⟨outStart, total01, dst, rfl, hOutGe, by omega, by omega⟩
  refine runs_seq_call_le hCopySpec (vs := [outStart, total01, dst])
    (by simp [evalArgs, Expr.eval, startState])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> omega)
    hCopyPre ?_
  intro _ m1 _ hPostC
  obtain ⟨_, _, _, heqC, hCopied, hFrCopy⟩ := hPostC
  simp only [List.cons.injEq, and_true] at heqC
  obtain ⟨rfl, rfl, rfl⟩ := heqC
  have hPayM1 : ListAt m1 dst payload := fun j hj => by rw [hCopied j hj]; exact hPayAt j hj
  have hM1Below : ∀ a < dst, m1 a = mem a := fun a ha => hFrCopy a (Or.inl ha)
  have hM1Above : ∀ a, start0 ≤ a → m1 a = mem a := fun a ha => hFrCopy a (Or.inr ha)
  refine runs_seq_assign_le (v := start0)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) (by omega)) ?_
  have hloop := reclaim_loop_triple (h := h) (outStart := outStart) (end1 := end1)
    (dst := dst) (total01 := total01) (start0 := start0) (holes := holes) (mem := mem) (m1 := m1)
    hfZ hStartLe (by omega) hHolesAt hHolesV hM1Above htop hw4
  refine runs_seq_triple_le hloop
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
     by simp [startState], by simp [startState], by simp, rfl⟩ ?_
  intro st2 ⟨q2, q3, q4, _, q6, q7, q9, _, qBelow, qZero, qAbove⟩
  set curEnd := reclaimCur holes gn start0 holes.length
  have hCurEndGe : start0 ≤ curEnd := reclaimCur_mono holes gn start0 holes.length
  have hCurEndLe : curEnd ≤ end1 := reclaimCur_le_hi (hi := end1)
    ⟨fun j hj => ⟨(hHolesV.1 j hj).1, (hHolesV.1 j hj).2.1.trans (by omega), (hHolesV.1 j hj).2.2⟩,
     hHolesV.2⟩ hStartLe holes.length le_rfl
  have hZeroSpec := zeroProc_meetsContract (w := w) hfZ
  have hCostEq : (buildReclaimHolesContract w gn payload holes).cost
      [h, outStart, end1, end1, holes.length, gn] mem =
      17 * (end1 - outStart) + 15 * (end1 - h - holes.length * gn) + 125 * holes.length + 200 := by
    simp [buildReclaimHolesContract]
  rw [hCostEq]
  have hTail : ∀ (st3 : State) (k3 : ℕ),
      st3.regs 3 = end1 → st3.regs 4 = holes.length → st3.regs 6 = dst → st3.regs 7 = total01 →
      (∀ a < start0, st3.mem a = m1 a) →
      (∀ a, start0 ≤ a → a < end1 → st3.mem a = 0) →
      (∀ a, end1 ≤ a → st3.mem a = m1 a) →
      k3 + 15 * holes.length + 30 ≤
        17 * (end1 - outStart) + 15 * (end1 - h - holes.length * gn) + 125 * holes.length + 200 →
      ∃ o st' c, Runs w p ω
        (.call 8 fZero [.reg 3, .reg 4] ;; .ret (.bin .add (.reg 6) (.reg 7))) st3 o st' c ∧
        (buildReclaimHolesContract w gn payload holes).post
          [h, outStart, end1, end1, holes.length, gn] mem o.value st'.mem ∧
        k3 + c ≤ 17 * (end1 - outStart) + 15 * (end1 - h - holes.length * gn) + 125 * holes.length + 200 := by
    intro st3 k3 r3 r4 r6 r7 hb3 hz3 ha3 hk3
    have hZPre : (zeroContract w).pre [end1, holes.length] st3.mem :=
      ⟨end1, holes.length, rfl, by omega, by omega⟩
    refine runs_seq_call_le hZeroSpec (vs := [end1, holes.length])
      (by simp [evalArgs, Expr.eval, r3, r4])
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl <;> omega)
      hZPre ?_
    intro _ mFinal _ hPostZF
    obtain ⟨_, _, heqZF, hZedF, hFrZF⟩ := hPostZF
    simp only [List.cons.injEq, and_true] at heqZF
    obtain ⟨rfl, rfl⟩ := heqZF
    refine runs_ret_le (v := start0)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r6))
        (Expr.eval_reg_of_eq (by simpa using r7)) (by omega)) ?_ ?_
    · refine ⟨h, outStart, end1, rfl, rfl, ?_, ?_, ?_⟩
      · exact WordRAM.ListAt.congr hPayM1 fun a _ hb =>
          (hFrZF a (Or.inl (by dsimp [start0] at *; omega))).trans
            (hb3 a (by dsimp [start0] at *; omega))
      · intro a ha
        exact (hFrZF a (Or.inl (by dsimp [start0, dst] at *; omega))).trans
          ((hb3 a (by dsimp [start0, dst] at *; omega)).trans (hM1Below a (by dsimp [dst]; omega)))
      · intro a ha
        by_cases h1 : a < end1
        · exact (hFrZF a (Or.inl h1)).trans (hz3 a ha h1)
        · by_cases h2 : a < end1 + holes.length
          · have hEqA : end1 + (a - end1) = a := by omega
            rw [← hEqA]; exact hZedF (a - end1) (by omega)
          · exact (hFrZF a (Or.inr (by omega))).trans
              ((ha3 a (by omega)).trans ((hM1Above a (by omega)).trans (hZF a (by omega))))
    · simp only [zeroContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size, argsSize]
      omega
  have hGapSum := reclaim_gap_sum_le
    (hi := end1)
    ⟨fun j hj => ⟨(hHolesV.1 j hj).1, (hHolesV.1 j hj).2.1.trans (by omega), (hHolesV.1 j hj).2.2⟩,
     hHolesV.2⟩ (by dsimp [start0, dst]; omega) hStartLe
  have h15 : 15 * rangeCost (reclaimGap holes gn start0) 0 holes.length + 15 * (end1 - curEnd) ≤
      15 * (end1 - h - holes.length * gn) := by
    have hmul := Nat.mul_le_mul_left 15 hGapSum
    have hmul2 : 15 * (rangeCost (reclaimGap holes gn start0) 0 holes.length +
        (end1 - curEnd) + holes.length * gn) =
        15 * rangeCost (reclaimGap holes gn start0) 0 holes.length + 15 * (end1 - curEnd) +
          15 * (holes.length * gn) := by ring
    have hmul3 : 15 * (end1 - h) = 15 * (end1 - h - holes.length * gn) + 15 * (holes.length * gn) := by
      have : holes.length * gn ≤ end1 - h := by omega
      omega
    omega
  have hLin := rangeCost_linear (reclaimGap holes gn start0) 15 95 holes.length
  refine runs_seq_cond_le (v := if curEnd < end1 then 1 else 0)
    (Expr.eval_lt_op (Expr.eval_reg_of_eq q9) (Expr.eval_reg_of_eq q2) (by omega)) ?_ ?_
  · intro hlt1
    have hlt2 : curEnd < end1 := by split_ifs at hlt1 with h' <;> simp_all
    have hZPre : (zeroContract w).pre [curEnd, end1 - curEnd] st2.mem :=
      ⟨curEnd, end1 - curEnd, rfl, by omega, by omega⟩
    refine runs_seq_call_le hZeroSpec (vs := [curEnd, end1 - curEnd])
      (by unfold evalArgs
          rw [Expr.eval_reg_of_eq q9]
          unfold evalArgs
          rw [Expr.eval_sub (Expr.eval_reg_of_eq q2) (Expr.eval_reg_of_eq q9) (by omega)]
          rfl)
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl <;> omega)
      hZPre ?_
    intro _ mNext _ hPostZ
    obtain ⟨_, _, heqZ, hZed, hFrZ⟩ := hPostZ
    simp only [List.cons.injEq, and_true] at heqZ
    obtain ⟨rfl, rfl⟩ := heqZ
    refine hTail _ _ (by simpa using q3) (by simpa using q4) (by simpa using q6) (by simpa using q7)
      (fun a ha => (hFrZ a (Or.inl (by omega))).trans (qBelow a ha))
      (fun a ha1 ha2 => by
        by_cases hltC : a < curEnd
        · exact (hFrZ a (Or.inl hltC)).trans (qZero a ha1 hltC)
        · have hEqA : curEnd + (a - curEnd) = a := by omega
          rw [← hEqA]; exact hZed (a - curEnd) (by omega))
      (fun a ha => (hFrZ a (Or.inr (by omega))).trans (qAbove a (by omega))) ?_
    simp only [buildCopyDownContract, buildCopyContract, zeroContract,
      List.getD_cons_succ, List.getD_cons_zero, Expr.size, argsSize, Nat.sub_zero]
    rw [hLin]
    have h9 : 1 + 8 = 9 := rfl
    rw [h9]
    omega
  · intro hge1
    have hge2 : end1 ≤ curEnd :=
      Nat.le_of_not_lt fun hlt => by simp [hlt] at hge1
    have hEqEnd : curEnd = end1 := by omega
    refine runs_seq_nop_le ?_
    refine hTail _ _ q3 q4 q6 q7 qBelow (by rwa [← hEqEnd]) (by rwa [← hEqEnd]) ?_
    simp only [buildCopyDownContract, buildCopyContract,
      List.getD_cons_succ, List.getD_cons_zero, Expr.size, argsSize, Nat.sub_zero]
    rw [hLin]
    have h9 : 1 + 8 = 9 := rfl
    rw [h9]
    omega

end MinCostFlow.HierPaths
