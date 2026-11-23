module

public import MinCostFlow.Spanner.PathDSContract
public import MinCostFlow.HierPaths.HierParams
public import MinCostFlow.HierPaths.BoundsProgFront
public import MinCostFlow.HierPaths.BoundsProgTail

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The evaluator of `[Γ, Γ, 1]` (`boundsProcs`)

`gammaBoundsProc a` is a deterministic Word-RAM procedure that, called with `[d, M, h]`, writes
`[Γ, Γ, 1]` at `h, h + 1, h + 2` and returns `h + 3`, where `Γ = gammaHP a d M`. It runs
`gammaFront` (the integers `X`, `j`, `⌈X^{2/3}⌉`, `⌈log₂(X + 2)⌉`, found by halving and by
comparing cubes) and then `gammaTail a` (the product, with one shift for each power of two). The
only constant in its body besides small numerals is the constant `a` of the construction.

`gammaBoundsProc_meetsContract` proves `pathDSBoundsContract` for any `PathDSParams` with
`phiOutDen = gExp = Γ`, `gDel = 1`, word constant `cw ≥ 3`, `K_bounds ≥ 1000` and at least three
cells of space. The cost is at most `1000 (log₂(d + M + 2) + 1)`: the loops take `O(X)` rounds
and `X ≤ log₂(d + M + 2) + 4`. The words suffice since every value is at most `Γ`, `8M + 8` or `X^3`,
and `X ≤ Γ`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Expander

/-- The evaluator of `[Γ, Γ, 1]`. -/
def gammaBoundsProc (a : ℕ) : Stmt := gammaFront ;; gammaTail a

/-- The `boundsProcs` list: the evaluator alone. -/
def gammaBoundsProcs (a : ℕ) : List Stmt := [gammaBoundsProc a]

lemma gammaBoundsProcs_nonempty (a : ℕ) : 0 < (gammaBoundsProcs a).length := by
  simp [gammaBoundsProcs]

lemma gammaBoundsProcs_noRand (a : ℕ) : ∀ s ∈ gammaBoundsProcs a, s.NoRand := by
  intro s hs
  simp only [gammaBoundsProcs, List.mem_singleton] at hs
  subst hs
  simp [gammaBoundsProc, gammaFront_noRand, gammaTail_noRand, Stmt.NoRand]

/-- `X ≤ Γ`, since `X ≤ j^3 ≤ (j + 2)^4` and `(j + 2)^4` is a factor of `Γ`. -/
lemma bigX_le_gammaHP (a d M : ℕ) : bigX M ≤ gammaHP a d M := by
  have h1 : bigX M ≤ bigJ M ^ 3 := le_ceilRoot_pow 2 (bigX M)
  have h2 : bigJ M ^ 3 ≤ (bigJ M + 2) ^ 4 :=
    le_trans (Nat.pow_le_pow_left (by omega) 3) (Nat.pow_le_pow_right (by omega) (by norm_num))
  have h3 : (bigJ M + 2) ^ 4 ≤ gammaHP a d M := by
    unfold gammaHP
    have hB : 1 ≤ 4 ^ (bigJ M + 1) := Nat.one_le_pow _ _ (by omega)
    have hC : 1 ≤ (bigKB M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hD : 1 ≤ (1 + (2 + d) ^ 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hE : 1 ≤ bigUX a M ^ (2 * bigJ M + 2) := Nat.one_le_pow _ _ (one_le_bigUX a M)
    calc (bigJ M + 2) ^ 4 = 1 * (bigJ M + 2) ^ 4 * 1 * 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr; norm_num
  omega

/-- `boundsProcs` meets `pathDSBoundsContract` for parameters with `phiOutDen = gExp = Γ` and
`gDel = 1`. -/
theorem gammaBoundsProc_meetsContract {a w bB : ℕ} {p : Program} (P : PathDSParams)
    (hphi : P.phiOutDen = gammaHP a) (hexp : P.gExp = gammaHP a) (hdel : P.gDel = fun _ _ => 1)
    (hcw : 3 ≤ P.cw) (hK : 1000 ≤ P.K_bounds) (hspace : ∀ d M, 3 ≤ P.boundsSpace d M)
    (hproc : p.procs[bB]? = some (gammaBoundsProc a)) :
    MeetsContract w p bB (pathDSBoundsContract P w) := by
  refine meetsContract_of_triple hproc fun args mem pos hwords hpre => ?_
  rcases hpre with ⟨⟨d, M, h, rfl, hd, hcwd⟩, hzero, hsp⟩
  rw [hexp, hdel] at hcwd
  set G := gammaHP a d M
  have hsp' : h + 3 < 2 ^ w := by
    have := hspace d M
    simp only [heapArg, List.getLastD_cons, List.getLastD_nil, List.getD_cons_zero,
      List.getD_cons_succ] at hsp
    omega
  -- word bounds
  set Y := d + M + G + 1 + 2
  have hY : Y ^ 3 < 2 ^ w := by
    have hlt : Y < 2 ^ (Nat.log 2 Y + 1) := Nat.lt_pow_succ_log_self (by decide) Y
    have h3 : 3 * (Nat.log 2 Y + 1) ≤ w := le_trans (Nat.mul_le_mul_right _ hcw) hcwd
    calc Y ^ 3 < (2 ^ (Nat.log 2 Y + 1)) ^ 3 := Nat.pow_lt_pow_left hlt (by decide)
      _ = 2 ^ (3 * (Nat.log 2 Y + 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) h3
  have hG1 : 4096 ≤ G := by
    have := max_two_le_gammaHP a d M
    unfold G gammaHP
    have hA : 1 ≤ (bigJ M + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hB : 1 ≤ 4 ^ (bigJ M + 1) := Nat.one_le_pow _ _ (by omega)
    have hC : 1 ≤ (bigKB M + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hD : 1 ≤ (1 + (2 + d) ^ 4) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hE : 1 ≤ bigUX a M ^ (2 * bigJ M + 2) := Nat.one_le_pow _ _ (one_le_bigUX a M)
    calc 4096 = 2 ^ 12 * 1 * 1 * 1 * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr
  have hYY : Y ≤ Y ^ 3 := Nat.le_self_pow (by decide) _
  have hYw : Y < 2 ^ w := lt_of_le_of_lt hYY hY
  have h4 : 4 ≤ 2 ^ w := by omega
  have hY2 : 8 * Y ≤ Y ^ 3 := by
    rw [show Y ^ 3 = Y * Y * Y by ring]
    have hY8 : 8 ≤ Y := by omega
    have : 8 ≤ Y * Y := le_trans hY8 (Nat.le_mul_of_pos_left Y (by omega))
    exact Nat.mul_le_mul_right Y this
  have h8M : 8 * M + 8 < 2 ^ w := by omega
  have hXG := bigX_le_gammaHP a d M
  have hX3 : bigX M ^ 3 < 2 ^ w :=
    lt_of_le_of_lt (Nat.pow_le_pow_left (show bigX M ≤ Y by omega) 3) hY
  have hGw : G < 2 ^ w := by omega
  have hGt : tailVal a d (bigJ M) (ceilRoot 2 (bigX M ^ 2)) (Nat.clog 2 (bigX M + 2)) = G :=
    (gammaHP_eq_tailVal a d M).symm
  -- run
  intro st ω hst; subst hst
  refine runs_start_le ?_
  refine runs_seq_triple_le (gammaFront_triple (d := d) (M := M) (h := h) h8M hX3 h4 _ rfl rfl rfl)
    rfl ?_
  intro st1 ⟨h1_0, h1_2, h1_9, h1_10, h1_11, hm1, hp1⟩
  have hv1 : 1 ≤ Nat.clog 2 (bigX M + 2) := by
    have := (Nat.lt_clog_iff_pow_lt (b := 2) (by decide) (x := bigX M + 2) (y := 0)).mpr
      (by norm_num)
    omega
  obtain ⟨o, st', c, hrun, ⟨ho, hmem⟩, hc⟩ := gammaTail_runs (a := a) (p := p) ω st1
    (by have := two_le_bigJ M; omega) hv1 (by rw [hGt]; exact hGw) hsp' h1_0 h1_2 h1_9 h1_10 h1_11
  subst ho
  rw [hGt, hm1] at hmem
  refine ⟨_, st', c, hrun, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [Outcome.value, heapArg, List.getLastD_cons, List.getLastD_nil]; omega
  · simp only [Outcome.value, heapArg, List.getLastD_cons, List.getLastD_nil, List.getD_cons_zero,
      List.getD_cons_succ]
    have := hspace d M
    omega
  · intro x hx
    simp only [heapArg, List.getLastD_cons, List.getLastD_nil] at hx
    rw [hmem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    rfl
  · intro x hx
    simp only [Outcome.value] at hx
    rw [hmem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hzero x (by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]; omega)
  · refine ⟨d, M, h, rfl, ?_⟩
    rw [hphi, hexp, hdel]
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    rw [hmem]
    interval_cases i <;> simp [G]
  · simp only [Outcome.value, heapArg, List.getLastD_cons, List.getLastD_nil]; omega
  · -- cost
    have hXlog : bigX M ≤ Nat.log 2 (d + M + 2) + 4 := by
      have h1 : bigX M = Nat.log 2 (8 * M + 7) + 1 := clog_eq_log_pred (by omega)
      have h2 : Nat.log 2 (8 * M + 7) ≤ Nat.log 2 (d + M + 2) + 3 := by
        have h3 : 8 * M + 7 ≤ (d + M + 2) * 2 * 2 * 2 := by omega
        have h4 := Nat.log_mono_right (b := 2) h3
        rw [Nat.log_mul_base (by decide) (by omega), Nat.log_mul_base (by decide) (by omega),
          Nat.log_mul_base (by decide) (by omega)] at h4
        exact h4
      omega
    have hl8 : Nat.log 2 (8 * M + 7) + 1 = bigX M := (clog_eq_log_pred (n := 8 * M + 8) (by omega)).symm
    have hlX : Nat.log 2 (bigX M + 1) ≤ bigX M := Nat.lt_succ_iff.mp (Nat.log_lt_self 2 (by omega))
    have hjX : bigJ M ≤ bigX M := ceilRoot_le_self 2 (bigX M)
    have hRX : ceilRoot 2 (bigX M ^ 2) ≤ bigX M := ceilRoot_sq_le_self _ (by
      have := three_le_xOf M; rw [bigX_eq_xOf]; omega)
    have hKl : 1000 * (Nat.log 2 (d + M + 2) + 1) ≤
        P.K_bounds * (Nat.log 2 (d + M + 2) + 1) := Nat.mul_le_mul_right _ hK
    simp only [pathDSBoundsContract, heapContract, List.getD_cons_zero, List.getD_cons_succ]
    omega

/-- `boundsProcs` for `hierParams`, with the constants that the contract needs. -/
theorem hierParams_boundsSpec (a : ℕ) {K_init K_del K_query : ℝ} {hK_init : 0 ≤ K_init}
    {hK_del : 0 ≤ K_del} {hK_query : 0 ≤ K_query} {K_bounds cw : ℕ} {hcw_pos : 1 ≤ cw}
    {boundsSpace : ℕ → ℕ → ℕ} {initSpace delSpace querySpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {C_space c_space : ℕ} {hC_space : 1 ≤ C_space} {hb hi hd hq}
    (hcw : 3 ≤ cw) (hK : 1000 ≤ K_bounds) (hspace : ∀ d M, 3 ≤ boundsSpace d M)
    (w : ℕ) (p : Program) (bB : ℕ) (hp : p.HasAt bB (gammaBoundsProcs a)) :
    MeetsContract w p bB (pathDSBoundsContract
      (hierParams a K_init K_del K_query hK_init hK_del hK_query K_bounds cw hcw_pos boundsSpace
        initSpace delSpace querySpace C_space c_space hC_space hb hi hd hq) w) := by
  have hproc : p.procs[bB]? = some (gammaBoundsProc a) := by
    have := hp 0 (by simp [gammaBoundsProcs])
    simpa [gammaBoundsProcs] using this
  exact gammaBoundsProc_meetsContract _ rfl rfl rfl hcw hK hspace hproc

end MinCostFlow.HierPaths
