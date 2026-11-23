module

public import MinCostFlow.LSF.Program.THSizeMath
public import MinCostFlow.LSF.Program.DecompGreedy

/-!
# The size pass

`thSizeProc` walks the top-down order `Q` from the back, over the positions `n - 1, …, 1`. At
`x = Q[k]` with parent `p` it stores `sz x = acc x + 1` and adds `sz x` to `acc p`. After the loop
it stores `sz r = acc r + 1` for the root `r = Q[0]`. The result is `SizeState … 1`
(`THSizeMath.lean`), at cost `O(n)`. The array `acc` starts at `0`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- One step (register `5` is `k`). Registers: `10 = x`, `11 = p`. -/
def thSizeBody : Stmt :=
  .assign 10 (.load (.bin .add (.reg 1) (.reg 5))) ;;
  .assign 11 (.load (.bin .add (.reg 2) (.reg 10))) ;;
  .store (.bin .add (.reg 4) (.reg 10)) (.bin .add (.load (.bin .add (.reg 3) (.reg 10))) (.const 1)) ;;
  .store (.bin .add (.reg 3) (.reg 11))
    (.bin .add (.load (.bin .add (.reg 3) (.reg 11))) (.load (.bin .add (.reg 4) (.reg 10)))) ;;
  .assign 5 (.bin .sub (.reg 5) (.const 1))

/-- Args: `[n, qPtr, parPtr, accPtr, szPtr]`. The two statements after the loop are the root
step. -/
def thSizeProc : Stmt :=
  .assign 5 (.bin .sub (.reg 0) (.const 1)) ;;
  .loop (.reg 5) thSizeBody ;;
  .assign 10 (.load (.reg 1)) ;;
  .store (.bin .add (.reg 4) (.reg 10)) (.bin .add (.load (.bin .add (.reg 3) (.reg 10))) (.const 1)) ;;
  .ret (.const 0)

lemma thSizeProc_noRand : thSizeProc.NoRand := by
  simp [thSizeProc, thSizeBody, Stmt.NoRand]

/-- The contract of `thSizeProc`. -/
def thSizeContract (w : ℕ) : Contract where
  pre args mem := ∃ (n qPtr parPtr accPtr szPtr r : ℕ) (Q : List ℕ),
    args = [n, qPtr, parPtr, accPtr, szPtr] ∧ 0 < n ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    qPtr + n ≤ accPtr ∧ parPtr + n ≤ accPtr ∧ accPtr + n ≤ szPtr ∧ szPtr + n < 2 ^ w ∧
    (∀ u < n, mem (accPtr + u) = 0)
  post args mem ret mem' := ∃ (n qPtr parPtr accPtr szPtr : ℕ),
    args = [n, qPtr, parPtr, accPtr, szPtr] ∧ ret = 0 ∧
    (∀ a, a < accPtr ∨ szPtr + n ≤ a → mem' a = mem a) ∧
    (∀ Q r, TopDownOrder n r (fun x => mem (parPtr + x)) Q → ListAt mem qPtr Q →
      SizeState Q (fun x => mem (parPtr + x)) n (fun u => mem' (accPtr + u))
        (fun x => mem' (szPtr + x)) 1 ∧
      mem' (szPtr + r) = mem' (accPtr + r) + 1)
  cost args _ := 60 * args.getD 0 0 + 40

theorem thSize_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some thSizeProc) :
    MeetsContract w p b (thSizeContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qPtr, parPtr, accPtr, szPtr, r, Q, rfl, hn, hQ, hQat, hq, hpa, hal, hsl, hzero⟩ :=
    hpre
  set args := [n, qPtr, parPtr, accPtr, szPtr] with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun k st =>
    (∀ i < 5, st.regs i = args.getD i 0) ∧ st.regs 5 = k ∧ k < n ∧
    (∀ a, a < accPtr ∨ szPtr + n ≤ a → st.mem a = mem a) ∧
    SizeState Q par n (fun u => st.mem (accPtr + u)) (fun x => st.mem (szPtr + x)) (k + 1)
  have hloop : ∀ k₀, Triple w p (Inv k₀) (.loop (.reg 5) thSizeBody)
      (normalPost (Inv 0)) (fun _ => 60 * k₀ + 3) := by
    intro k₀
    refine Triple.loop_inv (Inv := Inv) (condVal := fun st => st.regs 5) (fun k => k)
      (fun k => 60 * k + 3) ?_ ?_ ?_ k₀
    · intro k st _; eval_expr
    · rintro k st hI h0
      rw [hI.2.1] at h0; subst h0
      exact ⟨hI, by simp⟩
    · rintro k st ⟨hregs, h5, hkn, hfr, hS⟩ hne
      rw [h5] at hne
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      refine ⟨58, ?_⟩
      intro s ω' hs; subst s
      have r1 : st.regs 1 = qPtr := hregs 1 (by omega)
      have r2 : st.regs 2 = parPtr := hregs 2 (by omega)
      have r3 : st.regs 3 = accPtr := hregs 3 (by omega)
      have r4 : st.regs 4 = szPtr := hregs 4 (by omega)
      have hkQ : k' + 1 < Q.length := by rw [hQ.len]; exact hkn
      set x := Q[k' + 1] with hx
      have hxn : x < n := hQ.lt x (List.getElem_mem _)
      have hxr : x ≠ r := by
        intro h
        have h0 := hQ.head_eq hn
        rw [← h0, hx] at h
        have := (hQ.nodup.getElem_inj_iff).mp h
        omega
      have hpQ := hQ.after (k' + 1) hkQ hxr
      have hpn : par x < n := hQ.lt _ (List.mem_of_mem_take hpQ)
      set pp := par x with hpp
      have hmx : st.mem (qPtr + (k' + 1)) = x := by
        rw [hfr _ (Or.inl (by omega))]; exact hQat _ hkQ
      have hmp : st.mem (parPtr + x) = pp := hfr _ (Or.inl (by omega))
      set ax := st.mem (accPtr + x) with hax
      set ap := st.mem (accPtr + pp) with hap
      have hstep := sizeState_step hQ (j := k' + 1 + 1) (by omega) (by omega) hS
      simp only [show k' + 1 + 1 - 1 = k' + 1 by omega] at hstep
      have hxtake : x ∈ Q.take (k' + 1 + 1) := by
        rw [hx]; exact List.mem_take_iff_getElem.mpr ⟨k' + 1, by simp; omega, rfl⟩
      have hax_le := sizeState_acc_le hQ hS hxtake
      have hap_le := sizeState_acc_le hQ hstep hpQ
      rw [Function.update_self] at hap_le
      change ap + (ax + 1) + (k' + 1) ≤ n at hap_le
      change ax + (k' + 1 + 1) ≤ n at hax_le
      have hm1a : Function.update st.mem (szPtr + x) (ax + 1) (accPtr + pp) = ap := by
        rw [Function.update_of_ne (by omega)]
      have hm1s : Function.update st.mem (szPtr + x) (ax + 1) (szPtr + x) = ax + 1 := by
        rw [Function.update_self]
      refine runs_start_le ?_
      unfold thSizeBody
      refine runs_seq_assign_le (v := x) (by rw [← hmx]; eval_expr) ?_
      refine runs_seq_assign_le (v := pp) (by rw [← hmp]; eval_expr) ?_
      refine runs_seq_store_le (x := szPtr + x) (v := ax + 1) (by eval_expr) (by
        have : ax + 1 < 2 ^ w := by omega
        eval_expr) ?_
      refine runs_seq_store_le (x := accPtr + pp) (v := ap + (ax + 1)) (by eval_expr) (by
        have : ap + (ax + 1) < 2 ^ w := by omega
        eval_expr) ?_
      set m2 := Function.update (Function.update st.mem (szPtr + x) (ax + 1)) (accPtr + pp)
        (ap + (ax + 1)) with hm2
      refine runs_assign_le (v := k') (by show _ = some (k' + 1 - 1); eval_expr) ⟨k', ⟨?_, by simp,
        by omega, ?_, ?_⟩, by omega, ?_⟩ ?_
      · intro i hi
        simp only [Function.update_of_ne (show i ≠ 5 by omega),
          Function.update_of_ne (show i ≠ 11 by omega), Function.update_of_ne (show i ≠ 10 by omega)]
        exact hregs i hi
      · intro a ha
        show m2 a = mem a
        rw [hm2, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr a ha
      · refine sizeState_congr hQ (by omega) (fun u hu => ?_) (fun u hu => ?_) hstep
        · dsimp only
          by_cases hu' : u = pp
          · rw [hu', Function.update_self, hm2, Function.update_self]
          · rw [Function.update_of_ne hu', hm2, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
        · dsimp only
          by_cases hu' : u = x
          · rw [hu', Function.update_self, hm2, Function.update_of_ne (by omega),
              Function.update_self]
          · rw [Function.update_of_ne hu', hm2, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
      · simp only [Expr.size_reg]; omega
      · simp only [Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load]
        omega
  -- the whole procedure
  have hR0 : ∀ i < 5, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  refine runs_start_le ?_
  unfold thSizeProc
  refine runs_seq_assign_le (v := n - 1) (by
    have := hR0 0 (by omega); eval_expr) ?_
  refine runs_seq_triple_le (hloop (n - 1)) ⟨fun i hi => ?_, by simp, by omega,
    fun a _ => rfl, ?_⟩ ?_
  · simp only [Function.update_of_ne (show i ≠ 5 by omega)]; exact hR0 i hi
  · rw [show n - 1 + 1 = n by omega]
    exact sizeState_congr hQ le_rfl (acc := fun _ => 0) (fun u hu => (hzero u hu).symm)
      (fun _ _ => rfl) (sizeState_init hQ _)
  rintro st ⟨hregs, -, -, hfr, hS⟩
  have r1 : st.regs 1 = qPtr := hregs 1 (by omega)
  have r3 : st.regs 3 = accPtr := hregs 3 (by omega)
  have r4 : st.regs 4 = szPtr := hregs 4 (by omega)
  have hlen : 0 < Q.length := by rw [hQ.len]; exact hn
  have hmr : st.mem qPtr = r := by
    rw [hfr _ (Or.inl (by omega)), ← hQ.head_eq hn]
    simpa using hQat 0 hlen
  have hrn : r < n := hQ.lt r (hQ.head_eq hn ▸ List.getElem_mem hlen)
  have hrtake : r ∈ Q.take (0 + 1) := by
    rw [← hQ.head_eq hn]; exact List.mem_take_iff_getElem.mpr ⟨0, by simp; omega, rfl⟩
  set ar := st.mem (accPtr + r) with har
  have har_le := sizeState_acc_le hQ hS hrtake
  refine runs_seq_assign_le (v := r) (by rw [← hmr]; eval_expr) ?_
  refine runs_seq_store_le (x := szPtr + r) (v := ar + 1) (by eval_expr) (by
    have : ar + 1 < 2 ^ w := by omega
    eval_expr) ?_
  have hfr' : ∀ a, a < accPtr ∨ szPtr + n ≤ a → Function.update st.mem (szPtr + r) (ar + 1) a =
      mem a := by
    intro a ha
    rw [Function.update_of_ne (by omega)]; exact hfr a ha
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qPtr, parPtr, accPtr, szPtr, rfl,
    rfl, hfr', fun Q' r' hQ' hQat' => ?_⟩ ?_
  · have hQQ := topDownOrder_eq_of_listAt hQ hQ' hQat hQat'
    subst Q'
    have hr' : r' = r := by rw [← hQ'.head_eq hn, hQ.head_eq hn]
    subst hr'
    have hrQ : r' ∉ Q.drop 1 := fun h => ((hQ.mem_drop_one hn).mp h).2 rfl
    refine ⟨⟨fun u hu => ?_, fun x hx => ?_, ?_⟩, ?_⟩
    · have h1 := hS.1 u hu
      dsimp only at h1 ⊢
      rw [Function.update_of_ne (by omega), h1]
      congr 1
      refine List.map_congr_left (fun c hc => ?_)
      have hcr : c ≠ r' := fun h => hrQ (h ▸ (List.mem_filter.mp hc).1)
      rw [Function.update_of_ne (by omega)]
    · have hxr : x ≠ r' := fun h => hrQ (h ▸ hx)
      have hxn := hQ.lt x (List.mem_of_mem_drop hx)
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hS.2.1 x hx
    · rw [← hS.2.2]
      congr 2
      refine List.map_congr_left (fun c hc => ?_)
      have := hQ.lt c (List.mem_of_mem_take hc)
      dsimp only
      rw [Function.update_of_ne (by omega)]
    · dsimp only
      rw [Function.update_self, Function.update_of_ne (by omega)]
  · simp only [thSizeContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg,
      Expr.size_bin, Expr.size_load]
    omega

end

end MinCostFlow.LSF.Program
