module

public import MinCostFlow.LSF.Program.CongScatterTail
import Mathlib.Tactic.Linarith

/-!
# Spreading the edge values over their endpoints: the proof

This file proves `congScatter_meetsContract`. The definitions and the contract are in
`CongScatterBase`. Each step of the loop looks up the endpoints and their lowest common
ancestor, fills the scratch block with `q t`, and then runs the four block updates of
`congScatter_tail`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow.Num

@[expose] public section

set_option maxHeartbeats 1600000 in
theorem congScatter_meetsContract {w h : ℕ} {p : Program} {b bLca bFill bCopy bAdd bSub : ℕ}
    (hp : p.procs[b]? = some (congScatterProc bLca bFill bCopy bAdd bSub))
    (hLca : MeetsContract w p bLca (lcaContract w))
    (hFill : MeetsContract w p bFill (memFillContract w))
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hAdd : MeetsContract w p bAdd (addToContract w h))
    (hSub : MeetsContract w p bSub (subFromContract w h)) :
    MeetsContract w p b (congScatterContract w h) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨m0, euPtr, evPtr, qPtr, Kq, dPtr, K, tmpPtr, L, upPtr, depPtr, parPtr, n, tM, r, tl, hd,
    pe, rfl, hh, hw2, hw16, hKq, hR, hT, hends, hqv, heu, hev, hqd, hud, hdd, hpd, hdt, htw,
    hval⟩ := hpre
  set args := [m0, euPtr, evPtr, qPtr, Kq, dPtr, K, tmpPtr, L, upPtr, depPtr, parPtr, n] with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set dep : ℕ → ℕ := fun x => mem (depPtr + x) with hdep
  set eu : ℕ → ℕ := fun t => mem (euPtr + t) with heu_def
  set ev : ℕ → ℕ := fun t => mem (evPtr + t) with hev_def
  set lc : ℕ → ℕ := fun t => lcaChoice par dep (eu t) (ev t) with hlc
  set q : ℕ → ℕ := fun t => unsignedVal mem (qPtr + t * Kq) h Kq with hq
  set cap : ℤ := (capacity h K : ℤ) with hcap
  have hw1 : 1 < 2 ^ w := by omega
  have hm0w : m0 < 2 ^ w := hwords m0 (by simp [hargs])
  -- the loop invariant
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 12, st.regs i = args.getD i 0) ∧ st.regs 12 = j ∧
    (∀ a, a < dPtr ∨ tmpPtr + K ≤ a → st.mem a = mem a) ∧
    (∀ t < j, IsLcaOf par dep (lc t) (eu t) (ev t) ∧ lc t < n) ∧
    ∀ y < n, Valid st.mem (dPtr + y * K) h K ∧
      (unsignedVal st.mem (dPtr + y * K) h K : ℤ) % cap =
        ((unsignedVal mem (dPtr + y * K) h K : ℤ) +
          ∑ t ∈ Finset.range j, (q t : ℤ) * scatterWeight eu ev lc t y) % cap
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 12 (.const 0) (.reg 0) (congScatterBody bLca bFill bCopy bAdd bSub))
      (normalPost (Inv m0))
      (fun _ => (m0 - 0) * ((100 * L + 300 * K + 400) + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const (100 * L + 300 * K + 400) 0 m0 (Nat.zero_le _) hw1
      (fun _ => hm0w) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, fun i hi => ?_, by simp, fun a _ => rfl, fun t ht => absurd ht (by omega),
        fun y hy => ⟨hval y hy, ?_⟩⟩
      · simp only [Function.update_of_ne (show i ≠ 12 by omega)]
        interval_cases i <;> simp [startState, hargs]
      · simp [startState]
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = m0 := hI.1 0 (by omega)
      eval_expr
    · intro i _ hi st ω' hI
      obtain ⟨hregs, h12, hfr, hlcs, hD⟩ := hI
      have hr12 : ∀ k < 12, st.regs k = args.getD k 0 := hregs
      have r1 : st.regs 1 = euPtr := hr12 1 (by omega)
      have r2 : st.regs 2 = evPtr := hr12 2 (by omega)
      have r3 : st.regs 3 = qPtr := hr12 3 (by omega)
      have r4 : st.regs 4 = Kq := hr12 4 (by omega)
      have r5 : st.regs 5 = dPtr := hr12 5 (by omega)
      have r6 : st.regs 6 = K := hr12 6 (by omega)
      have r7 : st.regs 7 = tmpPtr := hr12 7 (by omega)
      have r8 : st.regs 8 = L := hr12 8 (by omega)
      have r9 : st.regs 9 = upPtr := hr12 9 (by omega)
      have r10 : st.regs 10 = depPtr := hr12 10 (by omega)
      have r11 : st.regs 11 = parPtr := hr12 11 (by omega)
      obtain ⟨hun, hvn⟩ := hends i hi
      change eu i < n at hun
      change ev i < n at hvn
      have hmu : st.mem (euPtr + i) = eu i := hfr _ (Or.inl (by omega))
      have hmv : st.mem (evPtr + i) = ev i := hfr _ (Or.inl (by omega))
      have hbu : eu i * K + K ≤ n * K := by
        exact block_end_le K (show eu i < n by omega)
      have hbv : ev i * K + K ≤ n * K := by
        exact block_end_le K (show ev i < n by omega)
      have hbq : i * Kq + Kq ≤ m0 * Kq := by
        exact block_end_le Kq (show i < m0 by omega)
      have hLw : L < 2 ^ w := hwords L (by simp [hargs])
      have hKqw : Kq < 2 ^ w := hwords Kq (by simp [hargs])
      have hKw : K < 2 ^ w := hwords K (by simp [hargs])
      refine runs_start_le ?_
      unfold congScatterBody
      refine runs_seq_assign_le (v := eu i) (by rw [← hmu]; eval_expr) ?_
      refine runs_seq_assign_le (v := ev i) (by rw [← hmv]; eval_expr) ?_
      -- the lowest common ancestor
      have hT' : LcaTables w n L upPtr depPtr parPtr par dep st.mem :=
        hT.of_agree (B := dPtr) (fun a ha => hfr a (Or.inl ha)) hud hdd hpd
      refine runs_seq_call_le (vs := [eu i, ev i, L, upPtr, depPtr, parPtr]) hLca
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons
            (by eval_expr) (evalArgs_nil _ _)))))))
        (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          have := hT.hupW; have := hT.hdW; have := hT.hpW
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        ⟨eu i, ev i, L, upPtr, depPtr, parPtr, n, tM, r, tl, hd, par, pe, dep, rfl, hw16, hR,
          hun, hvn, hT'⟩ ?_
      rintro l mem₁ pos₁ ⟨hm₁, hlpost⟩
      obtain ⟨hln, hlca⟩ := hlpost _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl hR hun hvn hT'
      have hll : lc i = l := lcaChoice_eq hR hun hlca
      subst hm₁
      have hbl : l * K + K ≤ n * K := by
        exact block_end_le K (show l < n by omega)
      -- the scratch block: zero it, then copy `q i`
      refine runs_seq_call_le (vs := [tmpPtr, K, 0]) hFill
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_nil _ _))))
        (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> omega)
        ⟨tmpPtr, K, 0, rfl, htw⟩ ?_
      rintro v₂ mem₂ pos₂ ⟨d₂, l₂, x₂, heq₂, -, hz₂, hfr₂⟩
      simp only [List.cons.injEq, and_true] at heq₂
      obtain ⟨rfl, rfl, rfl⟩ := heq₂
      dsimp only at hz₂ hfr₂
      refine runs_seq_call_le (vs := [tmpPtr, qPtr + i * Kq, Kq]) hCopy
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
          (evalArgs_nil _ _))))
        (by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl <;> omega)
        ⟨tmpPtr, qPtr + i * Kq, Kq, rfl, by omega, by omega, Or.inr (by omega)⟩ ?_
      rintro v₃ mem₃ pos₃ ⟨d₃, s₃, l₃, heq₃, -, hc₃, hfr₃⟩
      simp only [List.cons.injEq, and_true] at heq₃
      obtain ⟨rfl, rfl, rfl⟩ := heq₃
      dsimp only at hc₃ hfr₃
      have hq₃ : ∀ i' < Kq, mem₃ (tmpPtr + i') = mem (qPtr + i * Kq + i') := fun i' hi' => by
        rw [hc₃ i' hi', hfr₂ _ (Or.inl (by omega)), hfr _ (Or.inl (by omega))]
      have hM₃ : ScatterMid mem mem₃ dPtr n K tmpPtr h (q i) (fun y =>
          (unsignedVal mem (dPtr + y * K) h K : ℤ) +
            ∑ t ∈ Finset.range i, (q t : ℤ) * scatterWeight eu ev lc t y) := by
        have hz₃ : ∀ i', Kq ≤ i' → i' < K → mem₃ (tmpPtr + i') = 0 := fun i' h1 h2 => by
          rw [hfr₃ _ (Or.inr (by omega)), hz₂ i' h2]
        refine ⟨fun a ha => ?_, fun i' hi' => ?_, ?_, fun y hy => ?_⟩
        · rw [hfr₃ a (by rcases ha with ha | ha <;> [left; right] <;> omega),
            hfr₂ a (by rcases ha with ha | ha <;> [left; right] <;> omega)]
          exact hfr a ha
        · by_cases hlt : i' < Kq
          · rw [hq₃ i' hlt]; exact hqv i hi i' hlt
          · rw [hz₃ i' (by omega) hi']; exact base_pos h
        · rw [unsignedVal_extend_zero hKq hz₃]
          exact unsignedVal_congr hq₃
        · have hag : ∀ i' < K, mem₃ (dPtr + y * K + i') = st.mem (dPtr + y * K + i') :=
            fun i' hi' => by
              have := block_end_le K hy
              rw [hfr₃ _ (Or.inl (by omega)), hfr₂ _ (Or.inl (by omega))]
          refine ⟨fun i' hi' => by rw [hag i' hi']; exact (hD y hy).1 i' hi', ?_⟩
          rw [unsignedVal_congr (mem' := st.mem) (a' := dPtr + y * K) hag]
          exact (hD y hy).2
      -- the four updates of the array
      refine congScatter_tail hAdd hSub hh hw2 hdt htw (by simp [Function.update_apply, r5])
        (by simp [Function.update_apply, r6]) (by simp [Function.update_apply, r7])
        (by simp [Function.update_apply]) (by simp [Function.update_apply])
        (by simp [Function.update_apply]) hun hvn hln hM₃ (fun st' hMf hreg => ?_) ?_
      · refine ⟨⟨fun k hk => ?_, by simp, hMf.1, fun t ht => ?_,
          fun y hy => ⟨(hMf.2.2.2 y hy).1, ?_⟩⟩, ?_⟩
        · simp only [Function.update_of_ne (show k ≠ 12 by omega), hreg k (show k ≠ 16 by omega),
            Function.update_of_ne (show k ≠ 16 by omega), Function.update_of_ne (show k ≠ 15 by omega),
            Function.update_of_ne (show k ≠ 14 by omega), Function.update_of_ne (show k ≠ 13 by omega)]
          exact hr12 k hk
        · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
          · exact hlcs t ht
          · rw [hll]; exact ⟨hlca, hln⟩
        · rw [(hMf.2.2.2 y hy).2, Finset.sum_range_succ]
          congr 1
          simp only [scatterWeight]
          rw [hll]
          ring
        · simp only [hreg 12 (show (12 : ℕ) ≠ 16 by omega),
            Function.update_of_ne (show (12 : ℕ) ≠ 16 by omega),
            Function.update_of_ne (show (12 : ℕ) ≠ 15 by omega),
            Function.update_of_ne (show (12 : ℕ) ≠ 14 by omega),
            Function.update_of_ne (show (12 : ℕ) ≠ 13 by omega)]
          exact h12
      · simp [argsSize, Expr.size, lcaContract, memFillContract, memCopyContract]
        omega
  refine runs_start_le ?_
  unfold congScatterProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, hfr, hlcs, hD⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨m0, euPtr, evPtr, qPtr, Kq, dPtr, K, tmpPtr, L, upPtr,
    depPtr, parPtr, n, lc, rfl, rfl, hfr, hlcs, hD⟩ ?_
  · simp only [congScatterContract, hargs, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size_const, Expr.size_reg, Nat.sub_zero]
    have : m0 * (100 * L + 300 * K + 400 + 1 + 8) ≤ m0 * (100 * L + 300 * K + 420) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

end

end MinCostFlow.LSF.Program
