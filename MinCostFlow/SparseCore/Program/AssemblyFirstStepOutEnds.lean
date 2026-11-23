module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutSel
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourFacts

import WordRAM.Tactic

/-!
# Phase 4 entering-edge endpoint-root queries (`AssemblyFirstStepOutEnds`)

Implements and verifies `asmFirstQueryInsEndsStmt fEndRoot` (`[tourH, insSupPtr, insSupLen,
selInsPtr, eCap, h]`):
* Allocates `[h, h + 2 * eCap)` for `tlPtr = h` and `hdPtr = h + eCap`, setting `hp := h + 2 * eCap`.
* Iterates over the duplicate-free candidate list `insSup[0..insSupLen)`. Whenever
  `mem[selInsPtr + e] ≠ 0` (i.e. `e ∈ outInsS`), queries `fEndRoot [tourH, 2 * e, hp]` for the
  tail end `(e, true)` and `fEndRoot [tourH, 2 * e + 1, hp]` for the head end `(e, false)`, writing
  their new roots into `tlPtr + e` and `hdPtr + e`.
* Delivers `OutInsEndsAt st'.mem h (h + eCap) eCap tl' hd'` agreeing with
  `a.rf.root (ordSrc a.ord (e, true))` / `a.rf.root (ordSrc a.ord (e, false))` on `outInsS` (and `0`
  outside), preserves `TR.rep` + footprint growth inside `[h + 2 * eCap, o.value)` + `ZeroFrom` +
  frame below `h`, and pays `2 * |outInsS| * (H.mul * ordStoreLog eCap + 40) + 35 * insSup.length + 50`
  amortized against `TR.phi`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Loop body of `asmFirstQueryInsEndsStmt`:
regs `0 = tourH`, `1 = insSupPtr`, `2 = insSupLen`, `3 = selInsPtr`, `4 = eCap`,
`5 = tlPtr (= h)`, `6 = hdPtr (= h + eCap)`, `7 = hp`, `8 = i`, `9..12` scratch. -/
def asmFirstQueryInsEndsBody (fEndRoot : ℕ) : Stmt :=
  .assign 9 (.load (.bin .add (.reg 1) (.reg 8))) ;;
  .assign 10 (.load (.bin .add (.reg 3) (.reg 9))) ;;
  .cond (.reg 10)
    (.assign 11 (.reg 7) ;;
     .call 7 fEndRoot [.reg 0, .bin .mul (.const 2) (.reg 9), .reg 7] ;;
     .store (.bin .add (.reg 5) (.reg 9)) (.load (.reg 11)) ;;
     .assign 11 (.reg 7) ;;
     .call 7 fEndRoot [.reg 0, .bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1), .reg 7] ;;
     .store (.bin .add (.reg 6) (.reg 9)) (.load (.reg 11)))
    .nop

/-- **Entering-edge endpoint-root table builder**, `[tourH, insSupPtr, insSupLen, selInsPtr, eCap, h]`.
Allocates `tlPtr = h`, `hdPtr = h + eCap`, runs `fEndRoot` on `2 * e` and `2 * e + 1` for each
selected edge in `insSup`, and returns the final heap pointer `hp`. -/
def asmFirstQueryInsEndsStmt (fEndRoot : ℕ) : Stmt :=
  .assign 6 (.bin .add (.reg 5) (.reg 4)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 4)) ;;
  forRange 8 (.const 0) (.reg 2) (asmFirstQueryInsEndsBody fEndRoot) ;;
  .ret (.reg 7)

end

public section

theorem asmFirstQueryInsEndsStmt_noRand (fEndRoot : ℕ) :
    (asmFirstQueryInsEndsStmt fEndRoot).NoRand := by
  simp [asmFirstQueryInsEndsStmt, asmFirstQueryInsEndsBody, forRange, forUp, Stmt.NoRand]

private lemma endOfKey_two_mul' (e : ℕ) : endOfKey (2 * e) = (e, true) := by
  simp [endOfKey]

private lemma endOfKey_two_mul_add_one' (e : ℕ) : endOfKey (2 * e + 1) = (e, false) := by
  simp [endOfKey, Nat.mul_add_div (by decide : 0 < 2)]

private lemma count_mem_finset_le_card {L : List ℕ} {S : Finset ℕ} (hnd : L.Nodup) :
    (L.filter fun e => decide (e ∈ S)).length ≤ S.card := by
  have hnd' : (L.filter fun e => decide (e ∈ S)).Nodup := hnd.filter _
  rw [← List.toFinset_card_of_nodup hnd']
  refine Finset.card_le_card fun x hx => ?_
  have := (List.mem_filter.mp (List.mem_toFinset.mp hx)).2
  simpa using this

set_option maxHeartbeats 400000 in
/-- **Verification of `asmFirstQueryInsEndsStmt`**. -/
theorem asmFirstQueryInsEnds_runs {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w fEndRoot vCap eCap tourH insSupPtr selInsPtr h pos : ℕ} {p : Program}
    (H : AsmFirstTourEndRootAt TR w p fEndRoot)
    (hTR_loc : ∀ v e, (TR v e).Local)
    {a : AsmTourAbs} {tx₀ : (TR vCap eCap).τ}
    {insSup : List ℕ} {outInsS : Finset ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (htour_w : tourH < 2 ^ w)
    (hrep : (TR vCap eCap).rep tourH a tx₀ mem₀)
    (hfoot : ∀ x, (TR vCap eCap).foot tourH tx₀ x → x < h)
    (hIS : ListAt mem₀ insSupPtr insSup) (hIS_le : insSupPtr + insSup.length ≤ h)
    (hIS_disj : ∀ x, insSupPtr ≤ x → x < insSupPtr + insSup.length → ¬ (TR vCap eCap).foot tourH tx₀ x)
    (hIS_nd : insSup.Nodup) (hIS_cap : ∀ e ∈ insSup, e < eCap)
    (hIS_cov : ∀ e ∈ outInsS, e ∈ insSup)
    (hSel : OutSelFlagsAt mem₀ selInsPtr eCap outInsS) (hSel_le : selInsPtr + eCap ≤ h)
    (hSel_disj : ∀ x, selInsPtr ≤ x → x < selInsPtr + eCap → ¬ (TR vCap eCap).foot tourH tx₀ x)
    (hAct : ∀ e ∈ outInsS, (∃ u, (e, true) ∈ a.ord u) ∧ (∃ u, (e, false) ∈ a.ord u))
    (hz : ZeroFrom mem₀ h)
    (hsp : h + 2 * eCap + 2 * outInsS.card + H.querySpace < 2 ^ w) :
    let tl : ℕ → ℕ := fun e => if e ∈ outInsS then a.rf.root (ordSrc a.ord (e, true)) else 0
    let hd : ℕ → ℕ := fun e => if e ∈ outInsS then a.rf.root (ordSrc a.ord (e, false)) else 0
    ∃ hEnd st' cost tx',
      Runs w p ω (asmFirstQueryInsEndsStmt fEndRoot)
        (startState [tourH, insSupPtr, insSup.length, selInsPtr, eCap, h] mem₀ pos)
        (.returned hEnd) st' cost ∧
      (TR vCap eCap).rep tourH a tx' st'.mem ∧
      OutInsEndsAt st'.mem h (h + eCap) eCap tl hd ∧
      h + 2 * eCap ≤ hEnd ∧
      hEnd ≤ h + 2 * eCap + 2 * outInsS.card ∧
      ZeroFrom st'.mem hEnd ∧
      (∀ x < h, ¬ (TR vCap eCap).foot tourH tx₀ x → st'.mem x = mem₀ x) ∧
      (∀ x, (TR vCap eCap).foot tourH tx' x →
        (TR vCap eCap).foot tourH tx₀ x ∨ (h + 2 * eCap ≤ x ∧ x < hEnd)) ∧
      cost + (TR vCap eCap).phi tourH tx' st'.mem ≤
        2 * outInsS.card * (H.mul * ordStoreLog eCap + 45) + 35 * insSup.length + 50 +
          (TR vCap eCap).phi tourH tx₀ mem₀ := by
  classical
  intro tl hd
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have hq1 : 1 ≤ H.querySpace := H.querySpace_ge
  set s0 := startState [tourH, insSupPtr, insSup.length, selInsPtr, eCap, h] mem₀ pos
  set r1 := Function.update s0.regs 6 (h + eCap)
  set r2 := Function.update r1 7 (h + 2 * eCap)
  set r3 := Function.update r2 8 0
  have ha6 : Runs w p ω (.assign 6 (.bin .add (.reg 5) (.reg 4))) s0 .normal ⟨mem₀, r1, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨h + eCap, Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]))
      (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega), rfl, rfl, rfl⟩
  have ha7 : Runs w p ω (.assign 7 (.bin .add (.reg 6) (.reg 4))) ⟨mem₀, r1, pos⟩ .normal ⟨mem₀, r2, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨h + 2 * eCap, by
      have h6r : r1 6 = h + eCap := by simp [r1]
      have h4r : r1 4 = eCap := by simp [r1, s0, startState]
      have he : (Expr.bin .add (.reg 6) (.reg 4)).eval w ⟨mem₀, r1, pos⟩ = some (h + eCap + eCap) :=
        Expr.eval_add (Expr.eval_reg_of_eq h6r) (Expr.eval_reg_of_eq h4r) (by omega)
      simpa [show h + eCap + eCap = h + 2 * eCap by omega] using he, rfl, rfl, rfl⟩
  have ha8 : Runs w p ω (.assign 8 (.const 0)) ⟨mem₀, r2, pos⟩ .normal ⟨mem₀, r3, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  let cnt : ℕ → ℕ := fun i => ((insSup.take i).filter fun e => decide (e ∈ outInsS)).length
  have hcnt_le : ∀ i, cnt i ≤ outInsS.card := fun i =>
    count_mem_finset_le_card (hIS_nd.sublist (List.take_sublist i insSup))
  have hloop : ∀ (k : ℕ) (hk : k ≤ insSup.length) (stK : State) (txK : (TR vCap eCap).τ),
      stK.regs 0 = tourH → stK.regs 1 = insSupPtr → stK.regs 2 = insSup.length →
      stK.regs 3 = selInsPtr → stK.regs 5 = h → stK.regs 6 = h + eCap →
      stK.regs 7 = h + 2 * eCap + 2 * cnt k → stK.regs 8 = k →
      (TR vCap eCap).rep tourH a txK stK.mem →
      (∀ e < eCap, stK.mem (h + e) = if e ∈ insSup.take k then tl e else 0) →
      (∀ e < eCap, stK.mem (h + eCap + e) = if e ∈ insSup.take k then hd e else 0) →
      ZeroFrom stK.mem (stK.regs 7) →
      (∀ x < h, ¬ (TR vCap eCap).foot tourH tx₀ x → stK.mem x = mem₀ x) →
      (∀ x, (TR vCap eCap).foot tourH txK x →
        (TR vCap eCap).foot tourH tx₀ x ∨ (h + 2 * eCap ≤ x ∧ x < stK.regs 7)) →
      ∃ st1 c1 tx1,
        Runs w p ω (forUp 8 (.reg 2) (asmFirstQueryInsEndsBody fEndRoot)) stK .normal st1 c1 ∧
        st1.regs 7 = h + 2 * eCap + 2 * cnt insSup.length ∧
        (TR vCap eCap).rep tourH a tx1 st1.mem ∧
        (∀ e < eCap, st1.mem (h + e) = if e ∈ insSup then tl e else 0) ∧
        (∀ e < eCap, st1.mem (h + eCap + e) = if e ∈ insSup then hd e else 0) ∧
        ZeroFrom st1.mem (st1.regs 7) ∧
        (∀ x < h, ¬ (TR vCap eCap).foot tourH tx₀ x → st1.mem x = mem₀ x) ∧
        (∀ x, (TR vCap eCap).foot tourH tx1 x →
          (TR vCap eCap).foot tourH tx₀ x ∨ (h + 2 * eCap ≤ x ∧ x < st1.regs 7)) ∧
        c1 + (TR vCap eCap).phi tourH tx1 st1.mem ≤
          2 * (cnt insSup.length - cnt k) * (H.mul * ordStoreLog eCap + 45) +
            35 * (insSup.length - k) + 6 + (TR vCap eCap).phi tourH txK stK.mem := by
    intro k
    induction hrem : insSup.length - k generalizing k with
    | zero =>
      intro hk stK txK _ _ r2k _ _ _ r7k r8k hrepK htlK hhdK hzK hfrK hftK
      have hkEq : k = insSup.length := by omega
      subst hkEq; rw [List.take_length] at htlK hhdK
      have hcond : (Expr.bin .lt (.reg 8) (.reg 2)).eval w stK = some 0 := by
        simp [Expr.eval, r2k, r8k, BinOp.eval, h0w]
      exact ⟨stK, 4, txK, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        r7k, hrepK, htlK, hhdK, hzK, hfrK, hftK, by omega⟩
    | succ d ih =>
      intro hk stK txK r0k r1k r2k r3k r5k r6k r7k r8k hrepK htlK hhdK hzK hfrK hftK
      have hklt : k < insSup.length := by omega
      set e := insSup[k]'hklt
      have he_mem : e ∈ insSup := List.getElem_mem hklt
      have heCap : e < eCap := hIS_cap e he_mem
      have htk_succ : insSup.take (k + 1) = insSup.take k ++ [e] :=
        List.take_succ_eq_append_getElem hklt
      have hcnt_succ : cnt (k + 1) = cnt k + if e ∈ outInsS then 1 else 0 := by
        simp only [cnt, htk_succ, List.filter_append, List.length_append]
        by_cases heS : e ∈ outInsS <;> simp [heS]
      have hcnt_mono : cnt (k + 1) ≤ cnt insSup.length := by
        obtain ⟨rest, hrest⟩ := List.take_prefix (k + 1) insSup
        have hlen : (insSup.filter fun e => decide (e ∈ outInsS)).length =
            ((insSup.take (k + 1)).filter fun e => decide (e ∈ outInsS)).length +
              (rest.filter fun e => decide (e ∈ outInsS)).length := by
          conv_lhs => rw [← hrest]
          rw [List.filter_append, List.length_append]
        dsimp only [cnt]; rw [List.take_length]; omega
      have hcnt_k_le : cnt k ≤ outInsS.card := hcnt_le k
      have hcnt_s_le : cnt (k + 1) ≤ outInsS.card := hcnt_le (k + 1)
      have hme : stK.mem (insSupPtr + k) = e :=
        (hfrK _ (by omega) (hIS_disj _ (by omega) (by omega))).trans (hIS k hklt)
      have hmsel : stK.mem (selInsPtr + e) = if e ∈ outInsS then 1 else 0 :=
        (hfrK _ (by omega) (hSel_disj _ (by omega) (by omega))).trans (hSel e heCap)
      set rA := Function.update stK.regs 9 e
      set rB := Function.update rA 10 (if e ∈ outInsS then 1 else 0)
      have h9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 1) (.reg 8)))) stK .normal ⟨stK.mem, rA, stK.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq r1k) (Expr.eval_reg_of_eq r8k) (by omega)) hme, rfl, rfl, rfl⟩
      have h10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 3) (.reg 9))))
          ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r3k])) (Expr.eval_reg_of_eq (by simp [rA])) (by omega))
          hmsel, rfl, rfl, rfl⟩
      have hfootK_lt : ∀ x, (TR vCap eCap).foot tourH txK x → x < stK.regs 7 := fun x hx => by
        rcases hftK x hx with hf | ⟨_, hlt⟩
        · have := hfoot x hf; omega
        · exact hlt
      have hbody : ∃ stA cA txA,
          Runs w p ω (asmFirstQueryInsEndsBody fEndRoot) stK .normal stA cA ∧
          stA.regs 0 = tourH ∧ stA.regs 1 = insSupPtr ∧ stA.regs 2 = insSup.length ∧
          stA.regs 3 = selInsPtr ∧ stA.regs 5 = h ∧ stA.regs 6 = h + eCap ∧
          stA.regs 7 = h + 2 * eCap + 2 * cnt (k + 1) ∧ stA.regs 8 = k ∧
          (TR vCap eCap).rep tourH a txA stA.mem ∧
          (∀ e' < eCap, stA.mem (h + e') = if e' ∈ insSup.take (k + 1) then tl e' else 0) ∧
          (∀ e' < eCap, stA.mem (h + eCap + e') = if e' ∈ insSup.take (k + 1) then hd e' else 0) ∧
          ZeroFrom stA.mem (stA.regs 7) ∧
          (∀ x < h, ¬ (TR vCap eCap).foot tourH tx₀ x → stA.mem x = mem₀ x) ∧
          (∀ x, (TR vCap eCap).foot tourH txA x →
            (TR vCap eCap).foot tourH tx₀ x ∨ (h + 2 * eCap ≤ x ∧ x < stA.regs 7)) ∧
          cA + (TR vCap eCap).phi tourH txA stA.mem ≤
            (if e ∈ outInsS then 2 * (H.mul * ordStoreLog eCap + 45) else 0) + 25 +
              (TR vCap eCap).phi tourH txK stK.mem := by
        by_cases heS : e ∈ outInsS
        · have hcnt1 : cnt (k + 1) = cnt k + 1 := by simp [hcnt_succ, heS]
          set hp0 := stK.regs 7
          set rC := Function.update rB 11 hp0
          have ha11_1 : Runs w p ω (.assign 11 (.reg 7)) ⟨stK.mem, rB, stK.pos⟩ .normal ⟨stK.mem, rC, stK.pos⟩ 2 :=
            runs_assign_iff.mpr ⟨hp0, Expr.eval_reg_of_eq (by simp [rB, rA, hp0]), rfl, rfl, rfl⟩
          -- Query 1: tail end `2 * e`
          obtain ⟨body1, hbody1, o1, st1, c1, tx1, hr1, hrep1, hans1, hval1, hresp1, hcost1⟩ :=
            H.runs vCap eCap tourH (2 * e) hp0 a txK stK.mem stK.pos ω
              htour_w (by omega) (by omega) (by omega)
              (by rw [endOfKey_two_mul']; exact (hAct e heS).1)
              hrepK hfootK_lt hzK (by omega)
          rw [endOfKey_two_mul'] at hans1
          have htl_e : tl e = a.rf.root (ordSrc a.ord (e, true)) := by simp [tl, heS]
          have heA1 : evalArgs w ⟨stK.mem, rC, stK.pos⟩ [.reg 0, .bin .mul (.const 2) (.reg 9), .reg 7] =
              some [tourH, 2 * e, hp0] :=
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, r0k])) <|
            evalArgs_cons (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq (by simp [rC, rB, rA])) (by omega)) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hp0])) <| evalArgs_nil _ _
          set rD := Function.update rC 7 (hp0 + 1)
          have hcall1 : Runs w p ω (.call 7 fEndRoot [.reg 0, .bin .mul (.const 2) (.reg 9), .reg 7])
              ⟨stK.mem, rC, stK.pos⟩ .normal ⟨st1.mem, rD, st1.pos⟩
              (argsSize [.reg 0, .bin .mul (.const 2) (.reg 9), .reg 7] + c1 + 1) := by
            have h0 : Runs w p ω (.call 7 fEndRoot [.reg 0, .bin .mul (.const 2) (.reg 9), .reg 7])
                ⟨stK.mem, rC, stK.pos⟩ .normal ⟨st1.mem, Function.update rC 7 o1.value, st1.pos⟩
                (argsSize [.reg 0, .bin .mul (.const 2) (.reg 9), .reg 7] + c1 + 1) :=
              runs_call_iff.mpr ⟨_, body1, o1, st1, c1, heA1, hbody1, hr1, rfl, rfl, rfl⟩
            rwa [hval1] at h0
          set m1 := Function.update st1.mem (h + e) (tl e)
          have hst1 : Runs w p ω (.store (.bin .add (.reg 5) (.reg 9)) (.load (.reg 11)))
              ⟨st1.mem, rD, st1.pos⟩ .normal ⟨m1, rD, st1.pos⟩ 6 :=
            runs_store_iff.mpr ⟨h + e, tl e,
              Expr.eval_add (Expr.eval_reg_of_eq (by simp [rD, rC, rB, rA, r5k]))
                (Expr.eval_reg_of_eq (by simp [rD, rC, rB, rA])) (by omega),
              Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [rD, rC])) (htl_e ▸ hans1), rfl, rfl, rfl⟩
          -- Preserve `TR.rep` and `TR.phi` across storing into `h + e` (outside `foot tx1`!)
          have hft1 : ∀ x, (TR vCap eCap).foot tourH tx1 x →
              (TR vCap eCap).foot tourH tx₀ x ∨ (h + 2 * eCap ≤ x ∧ x < hp0 + 1) := fun x hx => by
            rcases hresp1.2.2.2.2 x hx with h0 | ⟨hlo, hhi⟩
            · rcases hftK x h0 with ha0 | ⟨h1, h2⟩
              · exact Or.inl ha0
              · exact Or.inr ⟨h1, by omega⟩
            · exact Or.inr ⟨by omega, by rw [hval1] at hhi; exact hhi⟩
          have hnotft1_he : ¬ (TR vCap eCap).foot tourH tx1 (h + e) := fun hx => by
            rcases hft1 _ hx with h0 | ⟨h1, _⟩
            · have := hfoot _ h0; omega
            · omega
          have hloc1 := hTR_loc vCap eCap tourH a tx1 st1.mem m1 fun x hx => by
            have hne : x ≠ h + e := fun heq => hnotft1_he (heq ▸ hx)
            simp [m1, hne]
          have hrep1_m1 : (TR vCap eCap).rep tourH a tx1 m1 := hloc1.1 hrep1
          have hphi1_m1 : (TR vCap eCap).phi tourH tx1 m1 = (TR vCap eCap).phi tourH tx1 st1.mem := hloc1.2.symm
          have hz1_m1 : ZeroFrom m1 (hp0 + 1) := fun x hx => by
            dsimp only [m1]; rw [Function.update_of_ne (by omega)]; exact hresp1.2.2.1 x (by rw [hval1]; exact hx)
          have hfoot1_lt : ∀ x, (TR vCap eCap).foot tourH tx1 x → x < hp0 + 1 := fun x hx => by
            rcases hft1 x hx with h0 | ⟨_, h2⟩
            · have := hfoot x h0; omega
            · exact h2
          set rE := Function.update rD 11 (hp0 + 1)
          have ha11_2 : Runs w p ω (.assign 11 (.reg 7)) ⟨m1, rD, st1.pos⟩ .normal ⟨m1, rE, st1.pos⟩ 2 :=
            runs_assign_iff.mpr ⟨hp0 + 1, Expr.eval_reg_of_eq (by simp [rD]), rfl, rfl, rfl⟩
          -- Query 2: head end `2 * e + 1`
          obtain ⟨body2, hbody2, o2, st2, c2, tx2, hr2, hrep2, hans2, hval2, hresp2, hcost2⟩ :=
            H.runs vCap eCap tourH (2 * e + 1) (hp0 + 1) a tx1 m1 st1.pos ω
              htour_w (by omega) (by omega) (by omega)
              (by rw [endOfKey_two_mul_add_one']; exact (hAct e heS).2)
              hrep1_m1 hfoot1_lt hz1_m1 (by omega)
          rw [endOfKey_two_mul_add_one'] at hans2
          have hhd_e : hd e = a.rf.root (ordSrc a.ord (e, false)) := by simp [hd, heS]
          have heA2 : evalArgs w ⟨m1, rE, st1.pos⟩
              [.reg 0, .bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1), .reg 7] =
              some [tourH, 2 * e + 1, hp0 + 1] :=
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rE, rD, rC, rB, rA, r0k])) <|
            evalArgs_cons (Expr.eval_add (Expr.eval_mul (Expr.eval_const h2w)
              (Expr.eval_reg_of_eq (by simp [rE, rD, rC, rB, rA])) (by omega)) (Expr.eval_const h1w) (by omega)) <|
            evalArgs_cons (Expr.eval_reg_of_eq (by simp [rE, rD])) <| evalArgs_nil _ _
          set rF := Function.update rE 7 (hp0 + 2)
          have hcall2 : Runs w p ω
              (.call 7 fEndRoot [.reg 0, .bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1), .reg 7])
              ⟨m1, rE, st1.pos⟩ .normal ⟨st2.mem, rF, st2.pos⟩
              (argsSize [.reg 0, .bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1), .reg 7] + c2 + 1) := by
            have h0 : Runs w p ω
                (.call 7 fEndRoot [.reg 0, .bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1), .reg 7])
                ⟨m1, rE, st1.pos⟩ .normal ⟨st2.mem, Function.update rE 7 o2.value, st2.pos⟩
                (argsSize [.reg 0, .bin .add (.bin .mul (.const 2) (.reg 9)) (.const 1), .reg 7] + c2 + 1) :=
              runs_call_iff.mpr ⟨_, body2, o2, st2, c2, heA2, hbody2, hr2, rfl, rfl, rfl⟩
            rwa [show o2.value = hp0 + 2 by omega] at h0
          set m2 := Function.update st2.mem (h + eCap + e) (hd e)
          have hst2 : Runs w p ω (.store (.bin .add (.reg 6) (.reg 9)) (.load (.reg 11)))
              ⟨st2.mem, rF, st2.pos⟩ .normal ⟨m2, rF, st2.pos⟩ 6 :=
            runs_store_iff.mpr ⟨h + eCap + e, hd e,
              Expr.eval_add (Expr.eval_reg_of_eq (by simp [rF, rE, rD, rC, rB, rA, r6k]))
                (Expr.eval_reg_of_eq (by simp [rF, rE, rD, rC, rB, rA])) (by omega),
              Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [rF, rE])) (hhd_e ▸ hans2), rfl, rfl, rfl⟩
          have hft2 : ∀ x, (TR vCap eCap).foot tourH tx2 x →
              (TR vCap eCap).foot tourH tx₀ x ∨ (h + 2 * eCap ≤ x ∧ x < hp0 + 2) := fun x hx => by
            rcases hresp2.2.2.2.2 x hx with h1 | ⟨hlo, hhi⟩
            · rcases hft1 x h1 with h0 | ⟨ha, hb⟩
              · exact Or.inl h0
              · exact Or.inr ⟨ha, by omega⟩
            · exact Or.inr ⟨by omega, by rw [hval2] at hhi; omega⟩
          have hnotft2_hce : ¬ (TR vCap eCap).foot tourH tx2 (h + eCap + e) := fun hx => by
            rcases hft2 _ hx with h0 | ⟨h1, _⟩
            · have := hfoot _ h0; omega
            · omega
          have hloc2 := hTR_loc vCap eCap tourH a tx2 st2.mem m2 fun x hx => by
            have hne : x ≠ h + eCap + e := fun heq => hnotft2_hce (heq ▸ hx)
            simp [m2, hne]
          have hrep2_m2 : (TR vCap eCap).rep tourH a tx2 m2 := hloc2.1 hrep2
          have hphi2_m2 : (TR vCap eCap).phi tourH tx2 m2 = (TR vCap eCap).phi tourH tx2 st2.mem := hloc2.2.symm
          have hfr_m2 : ∀ x < h + 2 * eCap, ¬ (TR vCap eCap).foot tourH tx₀ x →
              x ≠ h + e → x ≠ h + eCap + e → m2 x = stK.mem x := fun x hx hnf hne1 hne2 => by
            have hnf1 : ¬ (TR vCap eCap).foot tourH tx1 x := fun hf => by
              rcases hft1 x hf with h0 | ⟨h1, _⟩
              · exact hnf h0
              · omega
            have hnfK : ¬ (TR vCap eCap).foot tourH txK x := fun hf => by
              rcases hftK x hf with h0 | ⟨h1, _⟩
              · exact hnf h0
              · omega
            dsimp only [m2]; rw [Function.update_of_ne hne2]
            rw [hresp2.2.2.2.1 x (by omega) hnf1]
            dsimp only [m1]; rw [Function.update_of_ne hne1]
            exact hresp1.2.2.2.1 x (by omega) hnfK
          refine ⟨⟨m2, rF, st2.pos⟩, _, tx2,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10,
                runs_cond_iff.mpr ⟨1, _, Expr.eval_reg_of_eq (by simp [rB, heS]), by
                  simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha11_1,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall1,
                      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst1,
                        runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha11_2,
                          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall2, hst2, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩,
                rfl⟩), rfl⟩),
            by simp [rF, rE, rD, rC, rB, rA, r0k], by simp [rF, rE, rD, rC, rB, rA, r1k],
            by simp [rF, rE, rD, rC, rB, rA, r2k], by simp [rF, rE, rD, rC, rB, rA, r3k],
            by simp [rF, rE, rD, rC, rB, rA, r5k], by simp [rF, rE, rD, rC, rB, rA, r6k],
            by simp only [rF, Function.update_self, hp0, r7k, hcnt1]; omega,
            by simp [rF, rE, rD, rC, rB, rA, r8k], hrep2_m2, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro e' he'
            change m2 (h + e') = if e' ∈ insSup.take (k + 1) then tl e' else 0
            have htk : e' ∈ insSup.take (k + 1) ↔ e' ∈ insSup.take k ∨ e' = e := by
              rw [htk_succ, List.mem_append, List.mem_singleton]
            by_cases hee : e' = e
            · subst hee
              have hnf1 : ¬ (TR vCap eCap).foot tourH tx1 (h + e) := hnotft1_he
              dsimp only [m2]; rw [Function.update_of_ne (by omega : h + e ≠ h + eCap + e)]
              rw [hresp2.2.2.2.1 (h + e) (by omega) hnf1]; simp [m1, htk]
            · simp only [htk, hee, or_false]
              have hnf0 : ¬ (TR vCap eCap).foot tourH tx₀ (h + e') := fun hf => by have := hfoot _ hf; omega
              rw [hfr_m2 (h + e') (by omega) hnf0 (by omega) (by omega)]; exact htlK e' he'
          · intro e' he'
            change m2 (h + eCap + e') = if e' ∈ insSup.take (k + 1) then hd e' else 0
            have htk : e' ∈ insSup.take (k + 1) ↔ e' ∈ insSup.take k ∨ e' = e := by
              rw [htk_succ, List.mem_append, List.mem_singleton]
            by_cases hee : e' = e
            · subst hee; simp [m2, htk]
            · simp only [htk, hee, or_false]
              have hnf0 : ¬ (TR vCap eCap).foot tourH tx₀ (h + eCap + e') := fun hf => by have := hfoot _ hf; omega
              rw [hfr_m2 (h + eCap + e') (by omega) hnf0 (by omega) (by omega)]; exact hhdK e' he'
          · intro x hx
            change m2 x = 0
            have hx2 : hp0 + 2 ≤ x := by simpa [rF] using hx
            dsimp only [m2]; rw [Function.update_of_ne (by omega)]
            exact hresp2.2.2.1 x (by rw [hval2]; omega)
          · intro x hx hnf
            change m2 x = mem₀ x
            rw [hfr_m2 x (by omega) hnf (by omega) (by omega)]; exact hfrK x hx hnf
          · intro x hx
            simpa [rF] using hft2 x hx
          · simp only [heS, ↓reduceIte, Expr.size]
            rw [hphi2_m2]; rw [hphi1_m1] at hcost2; omega
        · have hcnt0 : cnt (k + 1) = cnt k := by simp [hcnt_succ, heS]
          have htl_0 : tl e = 0 := by simp [tl, heS]
          have hhd_0 : hd e = 0 := by simp [hd, heS]
          refine ⟨⟨stK.mem, rB, stK.pos⟩, _, txK,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10,
                runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (by simp [rB, heS]),
                  by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, rfl⟩), rfl⟩),
            by simp [rB, rA, r0k], by simp [rB, rA, r1k], by simp [rB, rA, r2k],
            by simp [rB, rA, r3k], by simp [rB, rA, r5k], by simp [rB, rA, r6k],
            by simp [rB, rA, r7k, hcnt0], by simp [rB, rA, r8k], hrepK, ?_, ?_,
            by simpa [rB, rA] using hzK, hfrK, by simpa [rB, rA] using hftK,
            by simp only [heS, ↓reduceIte, Expr.size]; omega⟩
          · intro e' he'
            have htk : e' ∈ insSup.take (k + 1) ↔ e' ∈ insSup.take k ∨ e' = e := by
              rw [htk_succ, List.mem_append, List.mem_singleton]
            by_cases hee : e' = e
            · subst hee; rw [htlK e heCap]; by_cases hm : e ∈ insSup.take k <;> simp [hm, htk, htl_0]
            · simp only [htk, hee, or_false]; exact htlK e' he'
          · intro e' he'
            have htk : e' ∈ insSup.take (k + 1) ↔ e' ∈ insSup.take k ∨ e' = e := by
              rw [htk_succ, List.mem_append, List.mem_singleton]
            by_cases hee : e' = e
            · subst hee; rw [hhdK e heCap]; by_cases hm : e ∈ insSup.take k <;> simp [hm, htk, hhd_0]
            · simp only [htk, hee, or_false]; exact hhdK e' he'
      obtain ⟨stA, cA, txA, hrA, r0A, r1A, r2A, r3A, r5A, r6A, r7A, r8A, hrepA, htlA, hhdA, hzA, hfrA, hftA, hcA⟩ := hbody
      set stB : State := ⟨stA.mem, Function.update stA.regs 8 (k + 1), stA.pos⟩
      have ha8s : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.const 1))) stA .normal stB 4 :=
        runs_assign_iff.mpr ⟨k + 1, Expr.eval_add (Expr.eval_reg_of_eq r8A) (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
      obtain ⟨st1, c1, tx1, hr1, r7f, hrepf, htlf, hhdf, hzf, hfrf, hftf, hc1⟩ :=
        ih (k + 1) (by omega) (by omega) stB txA
          (by simp [stB, r0A]) (by simp [stB, r1A]) (by simp [stB, r2A]) (by simp [stB, r3A])
          (by simp [stB, r5A]) (by simp [stB, r6A]) (by simp [stB, r7A]) (by simp [stB])
          hrepA htlA hhdA (by simpa [stB] using hzA) hfrA (by simpa [stB] using hftA)
      have hcond : (Expr.bin .lt (.reg 8) (.reg 2)).eval w stK = some 1 := by
        simp [Expr.eval, r2k, r8k, BinOp.eval, hklt, h1w]
      refine ⟨st1, _, tx1, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stB, _, c1, hcond, by decide,
        runs_seq_iff.mpr (Or.inr ⟨stA, cA, 4, hrA, ha8s, rfl⟩), hr1, rfl⟩)),
        r7f, hrepf, htlf, hhdf, hzf, hfrf, hftf, ?_⟩
      simp only [Expr.size]
      change c1 + (TR vCap eCap).phi tourH tx1 st1.mem ≤
        2 * (cnt insSup.length - cnt (k + 1)) * (H.mul * ordStoreLog eCap + 45) +
          35 * d + 6 + (TR vCap eCap).phi tourH txA stA.mem at hc1
      by_cases heS : e ∈ outInsS
      · simp only [heS, ↓reduceIte] at hcA hcnt_succ
        have hdiff : cnt insSup.length - cnt k = (cnt insSup.length - cnt (k + 1)) + 1 := by omega
        rw [hdiff]; nlinarith
      · simp only [heS, ↓reduceIte] at hcA hcnt_succ
        have hdiff : cnt insSup.length - cnt k = cnt insSup.length - cnt (k + 1) := by omega
        rw [hdiff]; omega
  obtain ⟨st1, c1, tx1, hrB, r7f, hrepf, htlf, hhdf, hzf, hfrf, hftf, hc1⟩ :=
    hloop 0 (Nat.zero_le _) ⟨mem₀, r3, pos⟩ tx₀
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1, s0, startState])
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1, s0, startState])
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1])
      (by simp [r3, r2, cnt]) (by simp [r3])
      hrep (fun e he => by simp [hz (h + e) (by omega)])
      (fun e he => by simp [hz (h + eCap + e) (by omega)])
      (by simp only [r3, r2, Function.update_of_ne (by decide : (7 : ℕ) ≠ 8), Function.update_self]
          exact fun x hx => hz x (by omega))
      (fun _ _ _ => rfl) (fun x hx => Or.inl hx)
  set hEnd := h + 2 * eCap + 2 * cnt insSup.length
  have hret : Runs w p ω (.ret (.reg 7)) st1 (.returned hEnd) st1 2 :=
    runs_ret_iff.mpr ⟨hEnd, Expr.eval_reg_of_eq r7f, rfl, rfl, rfl⟩
  have hseqLoop : Runs w p ω (forRange 8 (.const 0) (.reg 2) (asmFirstQueryInsEndsBody fEndRoot))
      ⟨mem₀, r2, pos⟩ .normal st1 (2 + c1 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha8, hrB, rfl⟩)
  have hcnt_all : cnt insSup.length ≤ outInsS.card := hcnt_le insSup.length
  have hcnt0 : cnt 0 = 0 := by simp [cnt]
  refine ⟨hEnd, st1, _, tx1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha6,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha7,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hseqLoop, hret, rfl⟩), rfl⟩), rfl⟩),
    hrepf, fun e he => ?_, by omega, by omega, by rwa [← r7f], hfrf, by rwa [← r7f], ?_⟩
  · constructor
    · rw [htlf e he]; by_cases h1 : e ∈ outInsS
      · simp [hIS_cov e h1]
      · by_cases h2 : e ∈ insSup <;> simp [h1, h2, tl]
    · rw [hhdf e he]; by_cases h1 : e ∈ outInsS
      · simp [hIS_cov e h1]
      · by_cases h2 : e ∈ insSup <;> simp [h1, h2, hd]
  · rw [hcnt0, Nat.sub_zero, Nat.sub_zero] at hc1
    change c1 + (TR vCap eCap).phi tourH tx1 st1.mem ≤
      2 * cnt insSup.length * (H.mul * ordStoreLog eCap + 45) + 35 * insSup.length + 6 +
        (TR vCap eCap).phi tourH tx₀ mem₀ at hc1
    have hmul : 2 * cnt insSup.length * (H.mul * ordStoreLog eCap + 45) ≤
        2 * outInsS.card * (H.mul * ordStoreLog eCap + 45) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hcnt_all)
    omega

end

end MinCostFlow.SparseCore.Program
