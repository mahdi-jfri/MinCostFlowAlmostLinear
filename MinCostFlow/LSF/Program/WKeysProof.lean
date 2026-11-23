module

public import MinCostFlow.LSF.Program.WKeys

/-!
# The proof of `wKeysProc`

`wKeys_meetsContract`: the key pass meets `wKeysContract`. After `x` steps, the first `x` key
blocks are written and the kept indices below `x` are listed.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Block `y` ends before block `x` when `y < x`. -/
lemma kblock_lt {keysPtr L y x : ℕ} (h : y < x) :
    keysPtr + y * (3 * L) + 3 * L ≤ keysPtr + x * (3 * L) := by
  have : (y + 1) * (3 * L) ≤ x * (3 * L) := Nat.mul_le_mul_right _ h
  rw [Nat.succ_mul] at this
  omega

set_option maxHeartbeats 4000000 in
theorem wKeys_meetsContract {w h : ℕ} {p : Program} {b bLoad : ℕ}
    (hp : p.procs[b]? = some (wKeysProc bLoad))
    (hLoad : MeetsContract w p bLoad (uLoadWordContract w h)) :
    MeetsContract w p b (wKeysContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, keysPtr, arrPtr, tM, rfl, hw2, hL,
    h3L, hnC, hkw, haw, hKA, hPe, hOw, hY, hB, hR, hpe, hval⟩ := hpre
  set args := [n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, keysPtr, arrPtr] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := hwords _ (by simp [hargs])
  have hLw : L < 2 ^ w := hwords _ (by simp [hargs])
  obtain ⟨pe, hpe'⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (pePtr + y) := ⟨_, rfl⟩
  obtain ⟨own, hown⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (ownPtr + y) := ⟨_, rfl⟩
  obtain ⟨lY, hlY⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (labYPtr + y) := ⟨_, rfl⟩
  obtain ⟨lB, hlB⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (labBPtr + y) := ⟨_, rfl⟩
  obtain ⟨rtf, hrtf⟩ : ∃ f : ℕ → ℕ, f = fun y => mem (rtPtr + y) := ⟨_, rfl⟩
  have hpex : ∀ y, mem (pePtr + y) = pe y := fun y => by rw [hpe']
  have hownx : ∀ y, mem (ownPtr + y) = own y := fun y => by rw [hown]
  have hlYx : ∀ y, mem (labYPtr + y) = lY y := fun y => by rw [hlY]
  have hlBx : ∀ y, mem (labBPtr + y) = lB y := fun y => by rw [hlB]
  have hrtx : ∀ y, mem (rtPtr + y) = rtf y := fun y => by rw [hrtf]
  simp only [hpex, hlYx, hlBx, hrtx] at hpe hval
  have hYw := hY.2.2
  have hBw := hB.2.2
  have hRw := hR.2.2
  have hPew := hPe.2.2
  have hOww := hOw.2.2
  set C := capacity h L with hC
  set kL := n * (3 * L) with hkL
  let Fr : (ℕ → ℕ) → Prop := fun m =>
    ∀ a, (a < keysPtr ∨ keysPtr + kL ≤ a) → (a < arrPtr ∨ arrPtr + n ≤ a) → m a = mem a
  have hRd : ∀ {a len : ℕ}, KAway w keysPtr kL arrPtr n a len →
      ∀ m, Fr m → ∀ i < len, m (a + i) = mem (a + i) := fun hD m hm i hi => by
    obtain ⟨hD1, hD2, -⟩ := hD
    exact hm _ (by rcases hD1 with h | h <;> [left; right] <;> omega)
      (by rcases hD2 with h | h <;> [left; right] <;> omega)
  have hblk : ∀ x < n, keysPtr + x * (3 * L) + 3 * L ≤ keysPtr + kL := fun x hx => by
    have := kblock_lt (keysPtr := keysPtr) (L := L) hx
    rw [hkL]; exact this
  let KeyOK : (ℕ → ℕ) → ℕ → Prop := fun m y =>
    Valid m (keysPtr + y * (3 * L)) h (3 * L) ∧
      unsignedVal m (keysPtr + y * (3 * L)) h (3 * L) = key3 C (lY y) (lB y) (rtf y)
  let Inv : ℕ → State → Prop := fun x st =>
    (∀ i < 10, st.regs i = args.getD i 0) ∧ st.regs 10 = (keptList r own pe x).length ∧
    st.regs 11 = 3 * L ∧ st.regs 14 = x ∧ Fr st.mem ∧
    ListAt st.mem arrPtr (keptList r own pe x) ∧ ∀ y < x, KeyOK st.mem y
  have hbody : ∀ x, 0 ≤ x → x < n → Triple w p (Inv x) (wKeysBody bLoad)
      (normalPost fun st₁ => Inv (x + 1) { st₁ with regs := Function.update st₁.regs 14 (x + 1) } ∧
        st₁.regs 14 = x) (fun _ => 90 * L + 200) := by
    intro x _ hx st ω' hI
    obtain ⟨hRg, r10, r11, r14, hfr, hLA, hK⟩ := hI
    have r1 : st.regs 1 = r := hRg 1 (by omega)
    have r2 : st.regs 2 = pePtr := hRg 2 (by omega)
    have r3 : st.regs 3 = ownPtr := hRg 3 (by omega)
    have r4 : st.regs 4 = labYPtr := hRg 4 (by omega)
    have r5 : st.regs 5 = labBPtr := hRg 5 (by omega)
    have r6 : st.regs 6 = rtPtr := hRg 6 (by omega)
    have r7 : st.regs 7 = L := hRg 7 (by omega)
    have r8 : st.regs 8 = keysPtr := hRg 8 (by omega)
    have r9 : st.regs 9 = arrPtr := hRg 9 (by omega)
    obtain ⟨hYx, hBx, hRx⟩ := hval x hx
    have hbx := hblk x hx
    set kb := keysPtr + x * (3 * L) with hkb
    have hmulw : x * (3 * L) < 2 ^ w := by omega
    have m_y : st.mem (labYPtr + x) = lY x := (hRd hY _ hfr x hx).trans (hlYx x)
    have m_b : st.mem (labBPtr + x) = lB x := (hRd hB _ hfr x hx).trans (hlBx x)
    have m_r : st.mem (rtPtr + x) = rtf x := (hRd hR _ hfr x hx).trans (hrtx x)
    have hlen := keptList_length_le r own pe x
    refine runs_start_le ?_
    unfold wKeysBody
    refine runs_seq_assign_le (v := kb) (by eval_expr <;> omega) ?_
    -- the three loads
    refine runs_seq_call_le (vs := [kb, L, lY x]) hLoad
      (evalArgs_cons (by eval_expr <;> omega) (evalArgs_cons (by eval_expr <;> omega)
        (evalArgs_cons (by rw [← m_y]; eval_expr <;> omega) (evalArgs_nil _ _))))
      (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega)
      ⟨kb, L, lY x, rfl, by omega⟩ ?_
    rintro v1 m1 pos1 ⟨d1, L1, x1, heq1, -, hfr1, hval1, hu1⟩
    simp only [List.cons.injEq, and_true] at heq1
    obtain ⟨rfl, rfl, rfl⟩ := heq1
    dsimp only at hfr1 hval1 hu1
    have m_b1 : m1 (labBPtr + x) = lB x := by
      rw [hfr1 _ (by rcases hB.1 with h | h <;> [left; right] <;> omega)]; exact m_b
    have m_r1 : m1 (rtPtr + x) = rtf x := by
      rw [hfr1 _ (by rcases hR.1 with h | h <;> [left; right] <;> omega)]; exact m_r
    refine runs_seq_call_le (vs := [kb + L, L, lB x]) hLoad
      (evalArgs_cons (by eval_expr <;> omega) (evalArgs_cons (by eval_expr <;> omega)
        (evalArgs_cons (by rw [← m_b1]; eval_expr <;> omega) (evalArgs_nil _ _))))
      (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega)
      ⟨kb + L, L, lB x, rfl, by omega⟩ ?_
    rintro v2 m2 pos2 ⟨d2, L2, x2, heq2, -, hfr2, hval2, hu2⟩
    simp only [List.cons.injEq, and_true] at heq2
    obtain ⟨rfl, rfl, rfl⟩ := heq2
    dsimp only at hfr2 hval2 hu2
    have m_r2 : m2 (rtPtr + x) = rtf x := by
      rw [hfr2 _ (by rcases hR.1 with h | h <;> [left; right] <;> omega)]; exact m_r1
    refine runs_seq_call_le (vs := [kb + (L + L), L, rtf x]) hLoad
      (evalArgs_cons (by eval_expr <;> omega) (evalArgs_cons (by eval_expr <;> omega)
        (evalArgs_cons (by rw [← m_r2]; eval_expr <;> omega) (evalArgs_nil _ _))))
      (by
        intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> omega)
      ⟨kb + (L + L), L, rtf x, rfl, by omega⟩ ?_
    rintro v3 m3 pos3 ⟨d3, L3, x3, heq3, -, hfr3, hval3, hu3⟩
    simp only [List.cons.injEq, and_true] at heq3
    obtain ⟨rfl, rfl, rfl⟩ := heq3
    dsimp only at hfr3 hval3 hu3
    -- the memory after the three loads
    have hm3 : ∀ a, (a < kb ∨ kb + 3 * L ≤ a) → m3 a = st.mem a := fun a ha => by
      rw [hfr3 a (by omega), hfr2 a (by omega), hfr1 a (by omega)]
    have hfr3' : Fr m3 := fun a ha1 ha2 => by
      rw [hm3 a (by rcases ha1 with h | h <;> [left; right] <;> omega)]; exact hfr a ha1 ha2
    have hKx : KeyOK m3 x := by
      have v0 : Valid m3 kb h L ∧ unsignedVal m3 kb h L = lY x := by
        refine key_congr (m := m1) ⟨hval1, by rw [hu1, Nat.mod_eq_of_lt (by omega)]⟩ ?_
        intro i hi; rw [hfr3 _ (by omega), hfr2 _ (by omega)]
      have v1 : Valid m3 (kb + L) h L ∧ unsignedVal m3 (kb + L) h L = lB x := by
        refine key_congr (m := m2) ⟨hval2, by rw [hu2, Nat.mod_eq_of_lt (by omega)]⟩ ?_
        intro i hi; rw [hfr3 _ (by omega)]
      have v2 : Valid m3 (kb + 2 * L) h L ∧ unsignedVal m3 (kb + 2 * L) h L = rtf x := by
        rw [show kb + 2 * L = kb + (L + L) by omega]
        exact ⟨hval3, by rw [hu3, Nat.mod_eq_of_lt (by omega)]⟩
      obtain ⟨hv, hu⟩ := key3_block v0.1 v1.1 v2.1
      exact ⟨hv, by rw [hu, v0.2, v1.2, v2.2]⟩
    have hKy : ∀ y < x, KeyOK m3 y := fun y hy =>
      key_congr (hK y hy) fun i hi => hm3 _ (Or.inl (by
        have := kblock_lt (keysPtr := keysPtr) (L := L) hy; omega))
    have hLA3 : ListAt m3 arrPtr (keptList r own pe x) := fun i hi => by
      rw [hm3 _ (by rcases hKA with h | h <;> [left; right] <;> omega)]; exact hLA i hi
    have hKall : ∀ y < x + 1, KeyOK m3 y := fun y hy => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | rfl
      · exact hKy y hy
      · exact hKx
    -- the kept test
    refine WordRAM.runs_cond_le (v := if x = r then 1 else 0) (by eval_expr <;> omega)
      (fun hb => ?_) (fun hb => ?_)
    · have hxr : x = r := by by_contra hc; simp [hc] at hb
      have hk : keptList r own pe (x + 1) = keptList r own pe x := by
        rw [keptList_succ, if_neg (fun h => h.1 hxr)]
      refine runs_nop_le ⟨⟨fun i hi => ?_, by simpa [hk] using r10, by simpa using r11, by simp,
        hfr3', by rw [hk]; exact hLA3, hKall⟩, by simpa using r14⟩ ?_
      · simp only [Function.update_apply]
        split_ifs <;> first | omega | exact hRg i hi
      · simp only [Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const, argsSize,
          uLoadWordContract, List.getD_cons_succ, List.getD_cons_zero]
        omega
    · have hxr : x ≠ r := by intro hc; simp [hc] at hb
      have hpx := hpe x hx hxr
      have m_pe : m3 (pePtr + x) = pe x := (hRd hPe _ hfr3' x hx).trans (hpex x)
      have m_own : m3 (ownPtr + pe x) = own (pe x) := (hRd hOw _ hfr3' _ hpx).trans (hownx _)
      refine WordRAM.runs_cond_le (v := if own (pe x) = 0 then 1 else 0)
        (by rw [← m_own, ← m_pe]; eval_expr <;> omega) (fun hb' => ?_) (fun hb' => ?_)
      · have ho : own (pe x) = 0 := by by_contra hc; simp [hc] at hb'
        have hk : keptList r own pe (x + 1) = keptList r own pe x ++ [x] := by
          rw [keptList_succ, if_pos ⟨hxr, ho⟩]
        refine runs_seq_store_le (x := arrPtr + (keptList r own pe x).length) (v := x)
          (by eval_expr <;> omega) (by eval_expr <;> omega) ?_
        refine runs_assign_le (v := (keptList r own pe x).length + 1) (by eval_expr <;> omega)
          ⟨⟨fun i hi => ?_, by simp [hk], by simpa using r11, by simp, fun a ha1 ha2 => ?_, ?_,
            fun y hy => ?_⟩, by simpa using r14⟩ ?_
        · simp only [Function.update_apply]
          split_ifs <;> first | omega | exact hRg i hi
        · dsimp only
          rw [Function.update_of_ne (by omega)]; exact hfr3' a ha1 ha2
        · dsimp only
          rw [hk]
          intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
          · rw [Function.update_of_ne (by omega), List.getElem_append_left hi]; exact hLA3 i hi
          · rw [Function.update_self]; simp
        · dsimp only
          refine key_congr (hKall y hy) fun i hi => Function.update_of_ne ?_ _ _
          have := hblk y (by omega)
          rcases hKA with h | h <;> omega
        · simp only [Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const, argsSize,
            uLoadWordContract, List.getD_cons_succ, List.getD_cons_zero]
          omega
      · have ho : own (pe x) ≠ 0 := by intro hc; simp [hc] at hb'
        have hk : keptList r own pe (x + 1) = keptList r own pe x := by
          rw [keptList_succ, if_neg (fun h => ho h.2)]
        refine runs_nop_le ⟨⟨fun i hi => ?_, by simpa [hk] using r10, by simpa using r11,
          by simp, hfr3', by rw [hk]; exact hLA3, hKall⟩, by simpa using r14⟩ ?_
        · simp only [Function.update_apply]
          split_ifs <;> first | omega | exact hRg i hi
        · simp only [Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const, argsSize,
            uLoadWordContract, List.getD_cons_succ, List.getD_cons_zero]
          omega
  have hloop : Triple w p (Inv 0) (forRange 14 (.const 0) (.reg 0) (wKeysBody bLoad))
      (normalPost (Inv n))
      (fun _ => (n - 0) * (90 * L + 200 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const (90 * L + 200) 0 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ hbody
    · intro st hI
      refine ⟨by eval_expr, ?_⟩
      have h14 : Function.update st.regs 14 0 = st.regs :=
        Function.update_eq_self_iff.mpr hI.2.2.2.1.symm
      rw [h14]
      exact hI
    · intro i st _ _ hI; exact hI.2.2.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
  have hst : ∀ i < 10, (startState args mem pos).regs i = args.getD i 0 := fun i _ => rfl
  have s7 := hst 7 (by omega)
  simp only [hargs, List.getD_cons_zero, List.getD_cons_succ] at s7
  refine runs_start_le ?_
  unfold wKeysProc
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 3 * L) (by eval_expr) ?_
  refine runs_seq_triple_le hloop ⟨fun i hi => ?_, by simp [keptList], by simp, by simp [startState, hargs],
    fun a _ _ => rfl, by simp [keptList, ListAt], fun y hy => absurd hy (Nat.not_lt_zero _)⟩ ?_
  · simp only [Function.update_apply]
    split_ifs <;> first | omega | exact hst i hi
  rintro st ⟨hRg, r10, -, -, hfr, hLA, hK⟩
  subst hpe' hown hlY hlB hrtf
  refine runs_ret_le (v := (keptList r (fun i => mem (ownPtr + i)) (fun x => mem (pePtr + x)) n).length)
    (by eval_expr) ⟨n, r, pePtr, ownPtr, labYPtr, labBPtr, rtPtr, L, keysPtr, arrPtr, rfl,
      hfr, rfl, hLA, hK⟩ ?_
  simp only [wKeysContract, hargs, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
    Expr.size_reg, Expr.size_bin, Nat.sub_zero]
  nlinarith
