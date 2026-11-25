module

public import WordRAM.Module
public import WordRAM.Sep.Tactic
public import WordRAM.Syntax
public import MinCostFlow.NarrowProg.Stage0Defs
public import MinCostFlow.NarrowProg.Stage0Entry
public import MinCostFlow.NarrowProg.Stage0Read
public import MinCostFlow.NarrowProg.Stage0Check
public import MinCostFlow.NarrowProg.Stage0Shift
public import MinCostFlow.NarrowProg.Stage3Answer
public import MinCostFlow.NarrowTop.Program
public import MinCostFlow.NarrowTop.MainMath
public import MinCostFlow.NarrowTop.MainCalls
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Top-level outer narrow-word procedure (`narrowMain`) and `NarrowMainPkg` instance

Implements `narrowMain` (procedure `0`), which runs the six narrow-word outer stages in order:
1. `stage0Read` (parse `narrowEncode I` into edge and demand record arrays),
2. `stage0Check` (check `lower ≤ upper`, build active vertex labels, check isolated demands,
   and compute limb width `L`; write `[0]` at address `0` and return `1` on infeasibility),
3. `stage0Shift` (compute shifted capacities and active shifted demands),
4. `stage0Feas` (pruned feasibility circulation via `stage1Circ`, saturation test, scatter;
   write `[0]` at address `0` and return `1` on infeasibility),
5. `stage0Res` (pruned residual circulation via `stage1Circ`, forward/reverse scatter),
6. `stage3Answer` (restore `lower + f + hFwd - hRev`, encode into `intWords`, copy to address `0`).

Proves `narrowMain_meets` with explicit `w`-independent cost constants and builds
`narrowMainPkg : NarrowMainPkg`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std
open MinCostFlow.Scaling MinCostFlow.Narrow MinCostFlow.NarrowProg MinCostFlow.NarrowProg.Stage1

namespace MinCostFlow.NarrowTop

/-! ### `narrowMain` procedure -/

/-- Top-level narrow-word minimum-cost flow procedure (entry procedure `0`). Takes `h0 = (narrowEncode I).length`,
runs the six outer stages in sequence, writes the narrow-word answer at address `0`, and returns
its length. -/
wram_def narrowMain (sRead sCheck sShift sFeas sRes sAnswer : ℕ) (h0) {
  k := mem[0]
  n := mem[1]
  m := mem[2]
  pOut := h0
  h1 := h0 + 5
  h2 := sRead(h1)
  pEdges := h1 + 4
  pDems := pEdges + 11 * m
  h3 := sCheck(pEdges, pDems, m, n, pOut, h2)
  ok := mem[pOut]
  if ok == 0 {
    mem[0] := 0
    return 1
  }
  cnt := mem[pOut + 1]
  L := mem[pOut + 2]
  pLabels := h2
  pActive := h2 + n
  h4 := sShift(pEdges, pDems, pLabels, pActive, m, cnt, L, k, pOut, h3)
  pShCapBuf := mem[pOut]
  pShCapLen := mem[pOut + 1]
  pShDemBuf := mem[pOut + 2]
  pShDemSign := mem[pOut + 3]
  pShDemLen := mem[pOut + 4]
  h5 := sFeas(pEdges, pLabels, n, m, pShCapBuf, pShCapLen, pShDemBuf, pShDemSign, pShDemLen,
    L, k, pOut, h4)
  feasOk := mem[pOut]
  if feasOk == 0 {
    mem[0] := 0
    return 1
  }
  pFeasFlow := mem[pOut + 1]
  h6 := sRes(pEdges, pShCapBuf, pFeasFlow, n, m, L, k, pOut, h5)
  pHFwd := mem[pOut]
  pHRev := mem[pOut + 1]
  outLen := sAnswer(pEdges, pFeasFlow, pHFwd, pHRev, m, L, k, h6)
  return outLen
}

/-! ### Separation-logic layout helpers -/

private theorem list_narrowEncode_head3 (I : Instance) :
    Assn.list 0 (narrowEncode I) =
      (0 ↦ narrowLimbWidth I) * (1 ↦ I.n) * (2 ↦ I.m) *
      Assn.list 3 (I.edges.flatMap (narrowEdgeWords (narrowLimbWidth I)) ++
        I.demand.flatMap (intWords (narrowLimbWidth I))) := by
  unfold narrowEncode
  simp only [Assn.list_cons, zero_add, mul_assoc]

private theorem list_narrowEncode_head1 (I : Instance) :
    Assn.list 0 (narrowEncode I) =
      (0 ↦ narrowLimbWidth I) *
      Assn.list 1 (I.n :: I.m ::
        (I.edges.flatMap (narrowEdgeWords (narrowLimbWidth I)) ++
         I.demand.flatMap (intWords (narrowLimbWidth I)))) := by
  unfold narrowEncode
  simp only [Assn.list_cons, zero_add]

private theorem split_free_five {h w : ℕ} (hfit : h + 5 ≤ 2 ^ w) :
    Assn.free h (2 ^ w - h) =
      Assn.list h (List.replicate 3 0) * Assn.list (h + 3) (List.replicate 2 0) *
      Assn.free (h + 5) (2 ^ w - (h + 5)) := by
  have h1 : 2 ^ w - h = 3 + (2 + (2 ^ w - (h + 5))) := by omega
  rw [h1, Assn.free_add', Assn.free_add']
  simp only [Assn.free, mul_assoc, show h + 3 + 2 = h + 5 by omega]

private theorem list_split_three' (p a0 a1 a2 : ℕ) :
    Assn.list p [a0, a1, a2] = (p ↦ a0) * (p + 1 ↦ a1) * (p + 2 ↦ a2) := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one, mul_assoc, show p + 1 + 1 = p + 2 by omega]

private theorem list_join_five_of_three_two (p a0 a1 a2 b0 b1 : ℕ) :
    (p ↦ a0) * (p + 1 ↦ a1) * (p + 2 ↦ a2) * Assn.list (p + 3) [b0, b1] =
      Assn.list p [a0, a1, a2, b0, b1] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one, mul_assoc,
    show p + 1 + 1 = p + 2 by omega,
    show p + 2 + 1 = p + 3 by omega,
    show p + 3 + 1 = p + 4 by omega]

private theorem list_split_five' (p a0 a1 a2 a3 a4 : ℕ) :
    Assn.list p [a0, a1, a2, a3, a4] =
      (p ↦ a0) * (p + 1 ↦ a1) * (p + 2 ↦ a2) * (p + 3 ↦ a3) * (p + 4 ↦ a4) := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one, mul_assoc,
    show p + 1 + 1 = p + 2 by omega,
    show p + 2 + 1 = p + 3 by omega,
    show p + 3 + 1 = p + 4 by omega]

private theorem list_join_two (p a0 a1 : ℕ) :
    (p ↦ a0) * (p + 1 ↦ a1) = Assn.list p [a0, a1] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one]

private theorem list_split_two (p a0 a1 : ℕ) :
    Assn.list p [a0, a1] = (p ↦ a0) * (p + 1 ↦ a1) := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one]

private theorem list_zero_singleton (v : ℕ) : (0 ↦ v) = Assn.list 0 [v] := by
  simp only [Assn.list_cons, Assn.list_nil, mul_one]

private theorem noDebt_free (a n : ℕ) : Assn.NoDebt (Assn.free a n) := by
  unfold Assn.free; exact Assn.noDebt_list _ _

/-! ### Correctness and explicit `w`-independent cost of `narrowMain` -/

/-- Explicit `w`-independent non-`stage1Circ` cost constant of `narrowMain`. -/
def narrowMainConst (aFeas aRes : ℕ) : ℕ :=
  4500 + 2 * aFeas + 2 * aRes

private theorem cost_branch1 (aFeas aRes n m L_U L_C : ℕ) :
    400 * m + 150 * n + 155 + ((40 * L_U + 570) * m + 60 * n + 340) + 300 ≤
      narrowMainConst aFeas aRes * (n + m * (L_U + L_C + 1) + 1) := by
  have h1 : 4500 * (n + m * (L_U + L_C + 1) + 1) ≤
      narrowMainConst aFeas aRes * (n + m * (L_U + L_C + 1) + 1) :=
    Nat.mul_le_mul_right _ (by unfold narrowMainConst; omega)
  nlinarith

private theorem cost_branch4 (aFeas aRes n m L_U L_C L_dem : ℕ) (hL : L_dem ≤ L_U + 1) :
    400 * m + 150 * n + 155 + ((40 * L_U + 570) * m + 60 * n + 340) +
      (980 * m * L_dem + 1500 * m + 450) + aFeas * (n + m * (L_dem + 1) + 1) +
      aRes * (m * (L_dem + L_C + 1) + 1) + (400 * m * L_dem + 590 * m + 160) + 300 ≤
      narrowMainConst aFeas aRes * (n + m * (L_U + L_C + 1) + 1) := by
  unfold narrowMainConst
  have h1 : m * L_dem ≤ m * (L_U + 1) := Nat.mul_le_mul_left m hL
  have h1' : 980 * m * L_dem ≤ 980 * (m * (L_U + 1)) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 980 h1
  have h1'' : 400 * m * L_dem ≤ 400 * (m * (L_U + 1)) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 400 h1
  have h2 : aFeas * (n + m * (L_dem + 1) + 1) ≤
      2 * aFeas * (n + m * (L_U + L_C + 1) + 1) := by
    rw [show 2 * aFeas * (n + m * (L_U + L_C + 1) + 1) =
      aFeas * (2 * (n + m * (L_U + L_C + 1) + 1)) by ring]
    exact Nat.mul_le_mul_left aFeas (by nlinarith)
  have h3 : aRes * (m * (L_dem + L_C + 1) + 1) ≤
      2 * aRes * (n + m * (L_U + L_C + 1) + 1) := by
    rw [show 2 * aRes * (n + m * (L_U + L_C + 1) + 1) =
      aRes * (2 * (n + m * (L_U + L_C + 1) + 1)) by ring]
    exact Nat.mul_le_mul_left aRes (by nlinarith)
  have hexp : (4500 + 2 * aFeas + 2 * aRes) * (n + m * (L_U + L_C + 1) + 1) =
      4500 * (n + m * (L_U + L_C + 1) + 1) +
      2 * aFeas * (n + m * (L_U + L_C + 1) + 1) +
      2 * aRes * (n + m * (L_U + L_C + 1) + 1) := by ring
  rw [hexp]
  nlinarith

private theorem cost_branch3 (aFeas aRes n m L_U L_C L_dem : ℕ) (hL : L_dem ≤ L_U + 1) :
    400 * m + 150 * n + 155 + ((40 * L_U + 570) * m + 60 * n + 340) +
      (980 * m * L_dem + 1500 * m + 450) + aFeas * (n + m * (L_dem + 1) + 1) + 300 ≤
      narrowMainConst aFeas aRes * (n + m * (L_U + L_C + 1) + 1) :=
  le_trans (by omega) (cost_branch4 aFeas aRes n m L_U L_C L_dem hL)

theorem narrowMain_meets {w : ℕ} {p : Program}
    {fn sRead sCheck sShift sFeas sRes sAnswer : ℕ}
    {S : ℕ → ℕ → ℕ} {B : ℕ → ℕ → ℕ → ℕ → ℕ} {aFeas aRes : ℕ}
    (hS : ∀ n n' m m', n ≤ n' → m ≤ m' → S n m ≤ S n' m')
    (hp : p.procs[fn]? = some (narrowMain sRead sCheck sShift sFeas sRes sAnswer))
    (hRead : Meets w p sRead ((stage0ReadSpec w).withCost fun d _ =>
      400 * d.1.m + 150 * d.1.n + 155))
    (hCheck : Meets w p sCheck ((stage0CheckSpec w).withCost fun x _ =>
      (40 * narrowMaxCapLimbs x.1.1 + 570) * x.1.1.m + 60 * x.1.1.n + 340))
    (hShift : Meets w p sShift ((stage0ShiftSpec w).withCost fun d _ =>
      980 * d.I.m * d.L + 1500 * d.I.m + 450))
    (hFeas : Meets w p sFeas ((stage0FeasSpec w S).withCost fun d _ =>
      aFeas * (d.I.n + d.I.m * (d.L + 1) + 1) +
      B (d.I.n + 1) (3 * d.I.m) (FlowReduction.scalingCapacityBudget d.I d.I.maxCapacity) 1))
    (hRes : Meets w p sRes ((stage0ResSpec w S).withCost fun d _ =>
      aRes * (d.I.m * (d.L + narrowMaxCostLimbs d.I + 1) + 1) +
      B d.I.n (2 * d.I.m) (2 * d.I.maxCapacity) d.I.maxCost))
    (hAns : Meets w p sAnswer ((stage3AnswerSpec w).withCost fun d _ =>
      400 * d.I.m * d.L + 590 * d.I.m + 160)) :
    Meets w p fn
      (narrowEntrySpec w (NarrowMainFits w S)
        (fun I _ =>
          narrowMainConst aFeas aRes *
            (I.n + I.m * (narrowMaxCapLimbs I + narrowMaxCostLimbs I + 1) + 1) +
          B (I.n + 1) (3 * I.m) (FlowReduction.scalingCapacityBudget I I.maxCapacity) 1 +
          B I.n (2 * I.m) (2 * I.maxCapacity) I.maxCost)
        (fun I _ out => narrowIsCorrectAnswer I out)) := by
  sep_enter ⟨I, hv⟩ with hfits
  obtain ⟨h2k1, hclip, hmem_fit⟩ := hfits
  set h0 := (narrowEncode I).length
  set k := narrowLimbWidth I
  set L_U := narrowMaxCapLimbs I
  set L_C := narrowMaxCostLimbs I
  have hk3 : 3 ≤ k := three_le_narrowLimbWidth I
  have hw7 : 7 ≤ w := by omega
  have hw128 : 128 ≤ 2 ^ w := le_trans (by decide : 128 ≤ 2 ^ 7) (Nat.pow_le_pow_right (by decide) hw7)
  have hw10 : 10 < 2 ^ w := by omega
  have hmain_ge : 4 * I.n + 65 * I.m + 13 * I.m * (L_U + 1) + 2 * I.m * L_C + 7 * (L_U + 1) + 60 ≤
      narrowMainSpace I S := by
    unfold narrowMainSpace; dsimp only [L_U, L_C]; omega
  have hh0_5 : h0 + 5 ≤ 2 ^ w := by omega
  -- Read k, n, m from address 0..2 and split pOut (5 words) from free heap
  sep_apply list_narrowEncode_head3 I
  sep_apply split_free_five hh0_5
  sep_step; sep_step; sep_step
  sep_apply (list_narrowEncode_head3 I).symm
  sep_step; sep_step
  -- Step 1: stage0Read(h0 + 5)
  have hread_fit : h0 + 5 + stage0ReadSpace I < 2 ^ w := by
    unfold stage0ReadSpace; omega
  generalize hF1 : (Assn.list h0 (List.replicate 3 0) * Assn.list (h0 + 3) (List.replicate 2 0)) = F1
  sep_apply hF1
  sep_step from (⟨I, hv⟩ : { J : Instance // J.IsValid })
  subst F1; sep_norm
  sep_step; sep_step
  subst pEdges pDems
  have h11m_lt : 11 * I.m < 2 ^ w := by omega
  have hpE_fit : h0 + 5 + 4 + 11 * I.m ≤ 2 ^ w := by omega
  have h3n_lt : 3 * I.n < 2 ^ w := by omega
  have hpD_fit : h0 + 5 + 4 + 11 * I.m + 3 * I.n ≤ 2 ^ w := by omega
  have hLU_lt : L_U + 1 < 2 ^ w := by omega
  have hchk_fit : h2 + stage0CheckSpace I < 2 ^ w := by
    unfold stage0ReadSpace stage0CheckSpace at *; omega
  -- Step 2: stage0Check
  generalize hF2 : Assn.list (h0 + 3) (List.replicate 2 0) = F2
  sep_step from ((⟨I, hv⟩, List.replicate 3 0) : { J : Instance // J.IsValid } × List ℕ) with hchk_res
  subst F2
  sep_apply list_split_three' h0 ok cnt L_dem
  sep_step
  sep_step
  · -- Branch 1: stage0Check reported infeasibility (ok = 0)
    rcases hchk_res with ⟨hok0, hinf⟩ | ⟨h1, _⟩
    · subst hok0
      simp only [zero_ne_one, ↓reduceIte]
      have hgood0 : narrowIsCorrectAnswer I [0] := Or.inl ⟨rfl, hinf⟩
      sep_apply list_narrowEncode_head1 I
      sep_step; sep_step
      sep_apply list_zero_singleton 0
      sep_step
      apply Assn.NoDebt.le_gc
      apply Assn.NoDebt.mul
      · apply Assn.noDebt_credits
        have hcost_nat := cost_branch1 aFeas aRes I.n I.m L_U L_C
        dsimp only [L_U, L_C] at hcost_nat ⊢
        omega
      · repeat (first | apply Assn.NoDebt.mul | apply Assn.noDebt_list | apply noDebt_free |
          apply Assn.noDebt_pointsTo | apply Assn.noDebt_gc |
          (apply Assn.noDebt_prod; intro _ _; apply Assn.noDebt_list))
    · omega
  · -- Branch 2: stage0Check succeeded (ok = 1)
    rcases hchk_res with ⟨h0', _⟩ | ⟨hok1, hcaps, hiso, hcnt_eq, hcnt_le, hact_inv, hact_len,
        hL1, hLle, hedge_lt, hdem_lt⟩
    · omega
    subst hok1 hcnt_eq
    simp only [↓reduceIte]
    have hL_eq : L_dem = L_U + 1 :=
      stage0Check_L_eq I hv hiso hact_inv hL1 hLle hedge_lt hdem_lt
    have hLge : narrowMaxCapLimbs I + 1 ≤ L_dem := by dsimp only [L_U] at hL_eq; omega
    have hL_lt_pow : L_dem < 2 ^ k := by
      dsimp only [k, L_U] at hL_eq ⊢; rw [hL_eq]; exact narrowMaxCapLimbs_lt_pow_k I hv
    have hpAct_lt : h2 + I.n < 2 ^ w := by unfold stage0CheckSpace at hchk_fit; omega
    sep_step; sep_step; sep_step; sep_step; sep_step
    have hrep2 : List.replicate 2 0 = [0, 0] := rfl
    rw [hrep2]
    sep_apply list_join_five_of_three_two h0 1
      (FlowReduction.shiftedGraph I hv).endpointLabels.count L_dem 0 0
    -- Step 3: stage0Shift
    have hel_le : (FlowReduction.shiftedGraph I hv).endpointLabels.count ≤ 2 * I.m :=
      Circulation.endpointLabels_count_le _
    have hshift_fit : h3 + stage0ShiftSpace I.m (FlowReduction.shiftedGraph I hv).endpointLabels.count L_dem < 2 ^ w := by
      have htot := narrowMain_totalSpace_le I hv hiso (fun _ => 0)
        (fun e => ⟨le_rfl, Nat.cast_nonneg _⟩) S hS hel_le hLle
      rw [hh3, hh2]; omega
    sep_step from (⟨I, hv, act, actTail, L_dem,
      [1, (FlowReduction.shiftedGraph I hv).endpointLabels.count, L_dem, 0, 0]⟩ : Stage0ShiftData)
    set c_el := (FlowReduction.shiftedGraph I hv).endpointLabels.count
    set shCapBuf := h3
    set shCapLen := h3 + I.m * L_dem
    set shDemBuf := h3 + I.m * L_dem + I.m + c_el * L_dem + c_el * L_dem
    set shDemSign := shDemBuf + c_el * L_dem
    set shDemLen := shDemSign + c_el
    sep_apply list_split_five' h0 shCapBuf shCapLen shDemBuf shDemSign shDemLen
    sep_step; sep_step; sep_step; sep_step; sep_step
    sep_apply list_join_two h0 shCapBuf shCapLen
    -- Step 4: stage0Feas
    have hfeas_fit : h4 + stage0FeasSpace I.m L_dem +
        stage1CircSpace (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
          (narrowLimbWidth I) S < 2 ^ w := by
      have htot := narrowMain_totalSpace_le I hv hiso (fun _ => 0)
        (fun e => ⟨le_rfl, Nat.cast_nonneg _⟩) S hS hel_le hLle
      have hh4' : h4 = h0 + 5 + stage0ReadSpace I + stage0CheckSpace I +
          stage0ShiftSpace I.m c_el L_dem := by
        dsimp only [c_el]; rw [hh4, hh3, hh2]
      unfold stage0FeasSpace
      clear * - hh4' htot hmem_fit
      omega
    have hmL_lt : I.m * L_dem < 2 ^ w := by
      have h1 : I.m * L_dem ≤ I.m * (L_U + 1) := Nat.mul_le_mul_left I.m hLle
      have h2 : I.m * (L_U + 1) ≤ 13 * I.m * (L_U + 1) :=
        Nat.mul_le_mul_right (L_U + 1) (by omega)
      clear * - h1 h2 hmain_ge hmem_fit
      omega
    have hcelL_lt : c_el * L_dem < 2 ^ w := by
      have h1 : c_el * L_dem ≤ 2 * I.m * (L_U + 1) := Nat.mul_le_mul hel_le hLle
      have h2 : 2 * I.m * (L_U + 1) ≤ 13 * I.m * (L_U + 1) :=
        Nat.mul_le_mul_right (L_U + 1) (by omega)
      clear * - h1 h2 hmain_ge hmem_fit
      omega
    have hpLab_fit : h2 + I.n ≤ 2 ^ w := by
      unfold stage0CheckSpace at hchk_fit; clear * - hchk_fit; omega
    have h3mul : 3 * c_el * L_dem = 3 * (c_el * L_dem) := Nat.mul_assoc 3 c_el L_dem
    have hpShCap_fit : shCapBuf + I.m * L_dem ≤ 2 ^ w := by
      dsimp only [shCapBuf]; unfold stage0ShiftSpace at hshift_fit; clear * - hshift_fit; omega
    have hpShCapLen_fit : shCapLen + I.m ≤ 2 ^ w := by
      dsimp only [shCapLen]; unfold stage0ShiftSpace at hshift_fit; clear * - hshift_fit; omega
    have hpShDemBuf_fit : shDemBuf + c_el * L_dem ≤ 2 ^ w := by
      dsimp only [shDemBuf]; unfold stage0ShiftSpace at hshift_fit; clear * - hshift_fit h3mul; omega
    have hpShDemSign_fit : shDemSign + c_el ≤ 2 ^ w := by
      dsimp only [shDemSign, shDemBuf]; unfold stage0ShiftSpace at hshift_fit; clear * - hshift_fit h3mul; omega
    have hpShDemLen_fit : shDemLen + c_el ≤ 2 ^ w := by
      dsimp only [shDemLen, shDemSign, shDemBuf]; unfold stage0ShiftSpace at hshift_fit; clear * - hshift_fit h3mul; omega
    have hn2_lt : I.n + 2 < 2 ^ w := by
      clear * - hmain_ge hmem_fit; omega
    generalize hF4 :
      (Assn.list 0 (narrowEncode I) *
       (∏ v ∈ Finset.range I.n,
          Assn.list (h0 + 5 + 4 + 11 * I.m + v * 3) (if hlt : v < I.n then demRec I ⟨v, hlt⟩ else [])) *
       Assn.list (h2 + I.n) (act ++ actTail) *
       (h0 + 2 ↦ shDemBuf) * (h0 + 3 ↦ shDemSign) * (h0 + 4 ↦ shDemLen)) = F4
    sep_apply hF4
    sep_step from (⟨I, hv, hiso, act, L_dem, hLge, [shCapBuf, shCapLen]⟩ : Stage0FeasData)
      with hh5_ge hh5_le hpFeas_fit hfok_le hfeas_ok1 hfeas_ok0
    subst F4; sep_norm
    sep_apply list_split_two h0 ok pFeasFlow
    sep_step
    sep_step
    · -- Branch 3: stage0Feas reported infeasibility (ok = 0)
      have hinf := hfeas_ok0 (by omega)
      have hgood0 : narrowIsCorrectAnswer I [0] := Or.inl ⟨rfl, hinf⟩
      simp only [show ok = 0 by omega, zero_ne_one, ↓reduceIte]
      sep_apply list_narrowEncode_head1 I
      sep_step; sep_step
      sep_apply list_zero_singleton 0
      sep_step
      apply Assn.NoDebt.le_gc
      apply Assn.NoDebt.mul
      · apply Assn.noDebt_credits
        have hcost_nat := cost_branch3 aFeas aRes I.n I.m L_U L_C L_dem hLle
        dsimp only [L_U, L_C] at hcost_nat ⊢
        omega
      · repeat (first | apply Assn.NoDebt.mul | apply Assn.noDebt_list | apply noDebt_free |
          apply Assn.noDebt_pointsTo | apply Assn.noDebt_gc |
          (apply Assn.noDebt_prod; intro _ _; apply Assn.noDebt_list))
    · -- Branch 4: stage0Feas succeeded (ok = 1)
      have hfok1 : ok = 1 := by omega
      obtain ⟨hf_bnds, hf_feas⟩ := hfeas_ok1 hfok1
      subst hfok1
      simp only [↓reduceIte]
      sep_step; sep_step
      sep_apply list_join_two h0 1 pFeasFlow
      have htot_f := narrowMain_totalSpace_le I hv hiso f hf_bnds S hS hel_le hLle
      have htotCost := totCostLimbs_le I
      have h4mL : 4 * I.m * L_dem = 4 * (I.m * L_dem) := Nat.mul_assoc 4 I.m L_dem
      have h2mL : 2 * I.m * L_dem = 2 * (I.m * L_dem) := Nat.mul_assoc 2 I.m L_dem
      have h2mC : 2 * I.m * narrowMaxCostLimbs I = 2 * (I.m * narrowMaxCostLimbs I) :=
        Nat.mul_assoc 2 I.m _
      have hh5_le' : h5 ≤ h0 + 5 + stage0ReadSpace I + stage0CheckSpace I +
          stage0ShiftSpace I.m c_el L_dem +
          stage0FeasSpace I.m L_dem +
          stage1CircSpace (FlowReduction.buildFeasibilityInstance I hv).withoutZeroEdges
            (narrowLimbWidth I) S := by
        dsimp only [c_el]; rw [hh4, hh3, hh2] at hh5_le; exact hh5_le
      have hres_fit : h5 + stage0ResSpace I.m L_dem (totCostLimbs I) +
          stage1CircSpace ((FlowReduction.shiftedGraph I hv).residual f).withoutZeroEdges
            (narrowLimbWidth I) S < 2 ^ w := by
        unfold stage0FeasSpace at hh5_le'
        unfold stage0ResSpace
        clear * - hh5_le' htot_f htotCost hmem_fit h4mL h2mL h2mC
        omega
      -- Step 5: stage0Res
      generalize hF5 :
        ((∏ v ∈ Finset.range I.n,
            Assn.list (h0 + 5 + 4 + 11 * I.m + v * 3) (if hlt : v < I.n then demRec I ⟨v, hlt⟩ else [])) *
         Assn.list (h2 + I.n) (act ++ actTail) *
         Assn.list h2 (List.ofFn (FlowReduction.shiftedGraph I hv).endpointLabels.table) *
         Assn.list shCapLen (List.ofFn fun e : Fin I.m =>
           (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph I hv).capacity e)).length) *
         (∏ c ∈ Finset.range c_el,
           Assn.list (shDemBuf + c * L_dem)
             (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand I act c).natAbs) L_dem)) *
         Assn.list shDemSign (List.ofFn fun c : Fin c_el =>
           if activeShiftedDemand I act c.val < 0 then 1 else 0) *
         Assn.list shDemLen (List.ofFn fun c : Fin c_el =>
           (Nat.digits (2 ^ k) (activeShiftedDemand I act c.val).natAbs).length) *
         (h0 + 2 ↦ shDemBuf) * (h0 + 3 ↦ shDemSign) * (h0 + 4 ↦ shDemLen)) = F5
      sep_apply hF5
      sep_step from (⟨I, hv, f, hf_bnds, L_dem, hLge, [1, pFeasFlow]⟩ : Stage0ResData)
        with hh6_ge hh6_le hpFwd_fit hpRev_fit hg_opt hg_nonneg hrev_le hsum_le
      subst F5; sep_norm
      sep_apply list_split_two h0 pHFwd pHRev
      sep_step; sep_step
      -- Step 6: stage3Answer
      obtain ⟨hdigs, hans_good⟩ :=
        narrowMain_stage3_correct I hv L_dem hcaps hedge_lt f hf_bnds hf_feas g hg_opt
          hg_nonneg hrev_le hsum_le
      have hans_fit : h6 + stage3AnswerSpace I.m L_dem < 2 ^ w := by
        unfold stage0FeasSpace at hh5_le'
        unfold stage0ResSpace at hh6_le
        clear * - hh5_le' hh6_le htot_f htotCost hmem_fit h4mL h2mL h2mC
        omega
      generalize hF6 :
        ((h0 ↦ pHFwd) * (h0 + 1 ↦ pHRev) * (h0 + 2 ↦ shDemBuf) * (h0 + 3 ↦ shDemSign) *
         (h0 + 4 ↦ shDemLen) *
         (∏ i ∈ Finset.range I.m,
           Assn.list (shCapBuf + i * L_dem)
             (if hlt : i < I.m then
               padLimbs (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph I hv).capacity ⟨i, hlt⟩)) L_dem
             else [])) *
         (∏ v ∈ Finset.range I.n,
            Assn.list (h0 + 5 + 4 + 11 * I.m + v * 3) (if hlt : v < I.n then demRec I ⟨v, hlt⟩ else [])) *
         Assn.list (h2 + I.n) (act ++ actTail) *
         Assn.list h2 (List.ofFn (FlowReduction.shiftedGraph I hv).endpointLabels.table) *
         Assn.list shCapLen (List.ofFn fun e : Fin I.m =>
           (Nat.digits (2 ^ k) ((FlowReduction.shiftedGraph I hv).capacity e)).length) *
         (∏ c ∈ Finset.range c_el,
           Assn.list (shDemBuf + c * L_dem)
             (padLimbs (Nat.digits (2 ^ k) (activeShiftedDemand I act c).natAbs) L_dem)) *
         Assn.list shDemSign (List.ofFn fun c : Fin c_el =>
           if activeShiftedDemand I act c.val < 0 then 1 else 0) *
         Assn.list shDemLen (List.ofFn fun c : Fin c_el =>
           (Nat.digits (2 ^ k) (activeShiftedDemand I act c.val).natAbs).length)) = F6
      sep_apply hF6
      sep_step from (⟨I, hv, L_dem, fun e => (f e).toNat,
        fun e => (g (Fin.castAdd I.m e)).toNat,
        fun e => (g (Fin.natAdd I.m e)).toNat⟩ : Stage3Data)
      subst F6; sep_norm
      sep_step
      apply Assn.NoDebt.le_gc
      apply Assn.NoDebt.mul
      · apply Assn.noDebt_credits
        have hcost_nat := cost_branch4 aFeas aRes I.n I.m L_U L_C L_dem hLle
        dsimp only [L_U, L_C] at hcost_nat ⊢
        omega
      · repeat (first | apply Assn.NoDebt.mul | apply Assn.noDebt_list | apply noDebt_free |
          apply Assn.noDebt_pointsTo | apply Assn.noDebt_gc |
          (apply Assn.noDebt_prod; intro _ _; apply Assn.noDebt_list))

/-! ### Module assembly and `NarrowMainPkg` instance -/

/-- Procedure names for `stage0ReadMod` inside `narrowMainMod` (`.mainAux 1..5`). -/
def mainReadNames : Stage0ReadNames NarrowTopName where
  readInt := .mainAux 1
  readOneEdge := .mainAux 2
  readEdges := .mainAux 3
  readDems := .mainAux 4
  stage0Read := .mainAux 5

/-- Procedure names for `stage0CheckMod` inside `narrowMainMod` (`.mainAux 10..18`). -/
def mainCheckNames : Stage0CheckNames NarrowTopName where
  limbsCmp := .mainAux 10
  signedLimbsLe := .mainAux 11
  checkOneCap := .mainAux 12
  checkCaps := .mainAux 13
  scanEnd := .mainAux 14
  labels := .mainAux 15
  isoCheck := .mainAux 16
  maxLen := .mainAux 17
  stage0Check := .mainAux 18

/-- Procedure names for `stage0ShiftMod` inside `narrowMainMod` (`.mainAux 20..35`). -/
def mainShiftNames : Stage0ShiftNames NarrowTopName where
  padCopy := .mainAux 20
  limbsAdd := .mainAux 21
  limbsSub := .mainAux 22
  limbsCmp := .mainAux 23
  canonLen := .mainAux 24
  accAddLimbs := .mainAux 25
  accNormalize := .mainAux 26
  shiftOneCap := .mainAux 27
  shiftOneDem := .mainAux 28
  shiftCaps := .mainAux 29
  shiftDemInit := .mainAux 30
  shiftDemEdges := .mainAux 31
  shiftDemFin := .mainAux 32
  shiftDem := .mainAux 33
  shiftWork := .mainAux 34
  stage0Shift := .mainAux 35

/-- Procedure names for `stage3AnswerMod` inside `narrowMainMod` (`.mainAux 40..50`). -/
def mainAnswerNames : Stage3AnswerNames NarrowTopName where
  padCopy := .mainAux 40
  limbsAdd := .mainAux 41
  limbsSub := .mainAux 42
  limbsCmp := .mainAux 43
  canonLen := .mainAux 44
  copy := .mainAux 45
  netFlow := .mainAux 46
  addLower := .mainAux 47
  oneEdge := .mainAux 48
  fill := .mainAux 49
  stage3Answer := .mainAux 50

/-- Core procedures of `narrowMainMod` (entry `narrowMain` at `.mainAux 0` plus Read/Check/Shift/Answer). -/
def narrowMainCoreMod (calls : Stage0CallsPkg) : Module NarrowTopName :=
  ⟨(.mainAux 0, fun idx =>
      narrowMain (idx mainReadNames.stage0Read) (idx mainCheckNames.stage0Check)
        (idx mainShiftNames.stage0Shift) (idx (.mainAux calls.feasEntry))
        (idx (.mainAux calls.resEntry)) (idx mainAnswerNames.stage3Answer)) ::
    ((stage0ReadMod mainReadNames).procs ++
     (stage0CheckMod mainCheckNames).procs ++
     (stage0ShiftMod mainShiftNames).procs ++
     (stage3AnswerMod mainAnswerNames).procs)⟩

/-- Complete outer `narrowMain` module combining `narrowMainCoreMod`, `calls.feasMod`, and `calls.resMod`. -/
def narrowMainMod (calls : Stage0CallsPkg) : Module NarrowTopName :=
  ⟨(narrowMainCoreMod calls).procs ++ calls.feasMod.procs ++ calls.resMod.procs⟩

theorem narrowMainMod_nonempty (calls : Stage0CallsPkg) : (narrowMainMod calls).procs ≠ [] := by
  simp [narrowMainMod, narrowMainCoreMod]

private theorem coreNames_eq (calls : Stage0CallsPkg) :
    (narrowMainCoreMod calls).names =
      .mainAux 0 ::
        ((stage0ReadMod mainReadNames).names ++
         (stage0CheckMod mainCheckNames).names ++
         (stage0ShiftMod mainShiftNames).names ++
         (stage3AnswerMod mainAnswerNames).names) := by
  simp [narrowMainCoreMod, Module.names, List.map_append]

private theorem coreNames_lt100 (calls : Stage0CallsPkg) :
    ∀ n ∈ (narrowMainCoreMod calls).names, ∃ i, n = .mainAux i ∧ i < 100 := by
  rw [coreNames_eq]
  intro n hn
  have hdec : ∀ x ∈ (.mainAux 0 ::
      ((stage0ReadMod mainReadNames).names ++
       (stage0CheckMod mainCheckNames).names ++
       (stage0ShiftMod mainShiftNames).names ++
       (stage3AnswerMod mainAnswerNames).names)),
      (match x with | .mainAux i => decide (i < 100) | _ => false) = true := by decide
  have hx := hdec n hn
  cases n with
  | mainAux i => exact ⟨i, rfl, of_decide_eq_true hx⟩
  | _ => cases hx

private theorem coreNames_nodup (calls : Stage0CallsPkg) :
    (narrowMainCoreMod calls).names.Nodup := by
  rw [coreNames_eq]
  decide

theorem narrowMainMod_names_main (calls : Stage0CallsPkg) :
    ∀ n ∈ (narrowMainMod calls).names, ∃ i, n = .mainAux i := by
  intro n hn
  simp only [narrowMainMod, Module.names, List.map_append, List.mem_append] at hn
  rcases hn with (hn | hn) | hn
  · obtain ⟨i, hi, _⟩ := coreNames_lt100 calls n hn; exact ⟨i, hi⟩
  · obtain ⟨i, hi, _⟩ := calls.feas_names n hn; exact ⟨i, hi⟩
  · obtain ⟨i, hi, _⟩ := calls.res_names n hn; exact ⟨i, hi⟩

theorem narrowMainMod_names_nodup (calls : Stage0CallsPkg) :
    (narrowMainMod calls).names.Nodup := by
  simp only [narrowMainMod, Module.names, List.map_append]
  have hcf : ((narrowMainCoreMod calls).names ++ calls.feasMod.names).Nodup := by
    refine List.nodup_append.mpr ⟨coreNames_nodup calls, calls.feas_nodup, ?_⟩
    intro x hx y hy hxy
    obtain ⟨i, rfl, hi⟩ := coreNames_lt100 calls x hx
    obtain ⟨j, rfl, hj1, _⟩ := calls.feas_names y hy
    cases hxy; omega
  refine List.nodup_append.mpr ⟨hcf, calls.res_nodup, ?_⟩
  intro x hx y hy hxy
  obtain ⟨j, rfl, hj⟩ := calls.res_names y hy
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨i, rfl, hi⟩ := coreNames_lt100 calls x hx; cases hxy; omega
  · obtain ⟨i, rfl, _, hi⟩ := calls.feas_names x hx; cases hxy; omega

theorem narrowMainMod_noRand (calls : Stage0CallsPkg) : (narrowMainMod calls).NoRand := by
  intro q hq idx
  simp only [narrowMainMod, narrowMainCoreMod, List.mem_append, List.mem_cons] at hq
  rcases hq with (((rfl | hq) | hq) | hq)
  · wram_no_rand
  · rcases hq with ((hq | hq) | hq) | hq
    · exact stage0ReadMod_noRand mainReadNames q hq idx
    · exact stage0CheckMod_noRand mainCheckNames q hq idx
    · exact stage0ShiftMod_noRand mainShiftNames q hq idx
    · exact stage3AnswerMod_noRand mainAnswerNames q hq idx
  · exact calls.feas_noRand q hq idx
  · exact calls.res_noRand q hq idx

private theorem placed_of_sub {ι : Type} {m₁ m₂ : Module ι} {p : Program} {idx : ι → ℕ}
    (hp : m₂.Placed p idx) (hsub : ∀ q ∈ m₁.procs, q ∈ m₂.procs) : m₁.Placed p idx :=
  fun n b hmem => hp n b (hsub (n, b) hmem)

/-- Concrete `NarrowMainPkg` built from `narrowMainMod calls`. -/
def narrowMainPkg (calls : Stage0CallsPkg) : NarrowMainPkg where
  mainMod := narrowMainMod calls
  mainMod_nonempty := narrowMainMod_nonempty calls
  mainMod_names_main := narrowMainMod_names_main calls
  mainMod_names_nodup := narrowMainMod_names_nodup calls
  mainMod_noRand := narrowMainMod_noRand calls
  a0 := narrowMainConst calls.aFeas calls.aRes
  mainMod_meets := by
    intro w p idx S B hS hB hp hhead hstage1
    have hhead0 : idx (.mainAux 0) = 0 := by
      simpa [narrowMainMod, narrowMainCoreMod] using hhead
    have hp_main : p.procs[0]? = some (narrowMain (idx mainReadNames.stage0Read)
        (idx mainCheckNames.stage0Check) (idx mainShiftNames.stage0Shift)
        (idx (.mainAux calls.feasEntry)) (idx (.mainAux calls.resEntry))
        (idx mainAnswerNames.stage3Answer)) := by
      rw [← hhead0]
      exact hp.get (n := .mainAux 0)
        (b := fun i => narrowMain (i mainReadNames.stage0Read) (i mainCheckNames.stage0Check)
          (i mainShiftNames.stage0Shift) (i (.mainAux calls.feasEntry))
          (i (.mainAux calls.resEntry)) (i mainAnswerNames.stage3Answer))
        (by simp [narrowMainMod, narrowMainCoreMod])
    by_cases hw : 2 < 2 ^ w
    · have hp_read : (stage0ReadMod mainReadNames).Placed p idx :=
        placed_of_sub hp fun q hq => by simp [narrowMainMod, narrowMainCoreMod, hq]
      have hp_check : (stage0CheckMod mainCheckNames).Placed p idx :=
        placed_of_sub hp fun q hq => by simp [narrowMainMod, narrowMainCoreMod, hq]
      have hp_shift : (stage0ShiftMod mainShiftNames).Placed p idx :=
        placed_of_sub hp fun q hq => by simp [narrowMainMod, narrowMainCoreMod, hq]
      have hp_ans : (stage3AnswerMod mainAnswerNames).Placed p idx :=
        placed_of_sub hp fun q hq => by simp [narrowMainMod, narrowMainCoreMod, hq]
      have hp_feas : calls.feasMod.Placed p idx :=
        placed_of_sub hp fun q hq => by simp [narrowMainMod, hq]
      have hp_res : calls.resMod.Placed p idx :=
        placed_of_sub hp fun q hq => by simp [narrowMainMod, hq]
      have hRead := stage0Read_meets_direct (w := w)
        (hp_read.get (n := mainReadNames.stage0Read) (b := fun i => stage0Read (i mainReadNames.readEdges) (i mainReadNames.readDems)) (by simp [stage0ReadMod]))
        (hp_read.get (n := mainReadNames.readInt) (b := fun _ => readInt) (by simp [stage0ReadMod]))
        (hp_read.get (n := mainReadNames.readOneEdge) (b := fun i => stage0ReadOneEdge (i mainReadNames.readInt)) (by simp [stage0ReadMod]))
        (hp_read.get (n := mainReadNames.readEdges) (b := fun i => stage0ReadEdges (i mainReadNames.readOneEdge)) (by simp [stage0ReadMod]))
        (hp_read.get (n := mainReadNames.readDems) (b := fun i => stage0ReadDems (i mainReadNames.readInt)) (by simp [stage0ReadMod]))
      have hCheck := stage0Check_meets_direct (w := w) hw
        (hp_check.get (n := mainCheckNames.stage0Check) (b := fun i => stage0Check (i mainCheckNames.checkCaps) (i mainCheckNames.labels) (i mainCheckNames.isoCheck) (i mainCheckNames.maxLen)) (by simp [stage0CheckMod]))
        (hp_check.get (n := mainCheckNames.limbsCmp) (b := fun _ => limbsCmp) (by simp [stage0CheckMod]))
        (hp_check.get (n := mainCheckNames.signedLimbsLe) (b := fun i => signedLimbsLe (i mainCheckNames.limbsCmp)) (by simp [stage0CheckMod]))
        (hp_check.get (n := mainCheckNames.checkOneCap) (b := fun i => stage0CheckOneCap (i mainCheckNames.signedLimbsLe)) (by simp [stage0CheckMod]))
        (hp_check.get (n := mainCheckNames.checkCaps) (b := fun i => stage0CheckCaps (i mainCheckNames.checkOneCap)) (by simp [stage0CheckMod]))
        (hp_check.get (n := mainCheckNames.scanEnd) (b := fun _ => stage0ScanEnd) (by simp [stage0CheckMod]))
        (hp_check.get (n := mainCheckNames.labels) (b := fun i => stage0Labels (i mainCheckNames.scanEnd)) (by simp [stage0CheckMod]))
        (hp_check.get (n := mainCheckNames.isoCheck) (b := fun _ => stage0IsoCheck) (by simp [stage0CheckMod]))
        (hp_check.get (n := mainCheckNames.maxLen) (b := fun _ => stage0MaxLen) (by simp [stage0CheckMod]))
      have hShift := stage0Shift_meets_direct (w := w) hw
        (hp_shift.get (n := mainShiftNames.stage0Shift) (b := fun i => stage0Shift (i mainShiftNames.shiftWork)) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.padCopy) (b := fun _ => padCopy) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.limbsAdd) (b := fun _ => limbsAdd) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.limbsSub) (b := fun _ => limbsSub) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.limbsCmp) (b := fun _ => limbsCmp) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.canonLen) (b := fun _ => canonLen) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.accAddLimbs) (b := fun _ => accAddLimbs) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.accNormalize) (b := fun _ => accNormalize) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.shiftOneCap) (b := fun i => stage0ShiftOneCap (i mainShiftNames.padCopy) (i mainShiftNames.limbsAdd) (i mainShiftNames.limbsSub) (i mainShiftNames.canonLen)) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.shiftOneDem) (b := fun i => stage0ShiftOneDem (i mainShiftNames.accNormalize) (i mainShiftNames.limbsCmp) (i mainShiftNames.limbsSub) (i mainShiftNames.canonLen)) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.shiftCaps) (b := fun i => stage0ShiftCaps (i mainShiftNames.shiftOneCap)) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.shiftDemInit) (b := fun i => stage0ShiftDemInit (i mainShiftNames.accAddLimbs)) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.shiftDemEdges) (b := fun i => stage0ShiftDemEdges (i mainShiftNames.accAddLimbs)) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.shiftDemFin) (b := fun i => stage0ShiftDemFin (i mainShiftNames.shiftOneDem)) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.shiftDem) (b := fun i => stage0ShiftDem (i mainShiftNames.shiftDemInit) (i mainShiftNames.shiftDemEdges) (i mainShiftNames.shiftDemFin)) (by simp [stage0ShiftMod]))
        (hp_shift.get (n := mainShiftNames.shiftWork) (b := fun i => stage0ShiftWork (i mainShiftNames.shiftCaps) (i mainShiftNames.shiftDem)) (by simp [stage0ShiftMod]))
      have hAns := stage3Answer_meets_direct (w := w) hw
        (hp_ans.get (n := mainAnswerNames.stage3Answer) (b := fun i => stage3Answer (i mainAnswerNames.fill) (i mainAnswerNames.copy)) (by simp [stage3AnswerMod]))
        (hp_ans.get (n := mainAnswerNames.padCopy) (b := fun _ => padCopy) (by simp [stage3AnswerMod]))
        (hp_ans.get (n := mainAnswerNames.limbsAdd) (b := fun _ => limbsAdd) (by simp [stage3AnswerMod]))
        (hp_ans.get (n := mainAnswerNames.limbsSub) (b := fun _ => limbsSub) (by simp [stage3AnswerMod]))
        (hp_ans.get (n := mainAnswerNames.limbsCmp) (b := fun _ => limbsCmp) (by simp [stage3AnswerMod]))
        (hp_ans.get (n := mainAnswerNames.canonLen) (b := fun _ => canonLen) (by simp [stage3AnswerMod]))
        (hp_ans.get (n := mainAnswerNames.copy) (b := fun _ => copy) (by simp [stage3AnswerMod]))
        (hp_ans.get (n := mainAnswerNames.netFlow) (b := fun i => stage3NetFlow (i mainAnswerNames.limbsSub) (i mainAnswerNames.limbsAdd)) (by simp [stage3AnswerMod]))
        (hp_ans.get (n := mainAnswerNames.addLower) (b := fun i => stage3AddLower (i mainAnswerNames.padCopy) (i mainAnswerNames.limbsAdd) (i mainAnswerNames.limbsSub) (i mainAnswerNames.limbsCmp)) (by simp [stage3AnswerMod]))
        (hp_ans.get (n := mainAnswerNames.oneEdge) (b := fun i => stage3OneEdge (i mainAnswerNames.netFlow) (i mainAnswerNames.addLower) (i mainAnswerNames.canonLen) (i mainAnswerNames.copy)) (by simp [stage3AnswerMod]))
        (hp_ans.get (n := mainAnswerNames.fill) (b := fun i => stage3Fill (i mainAnswerNames.oneEdge)) (by simp [stage3AnswerMod]))
      have hFeas := calls.feas_meets w p idx S B hS hB hp_feas hstage1
      have hRes := calls.res_meets w p idx S B hS hB hp_res hstage1
      exact narrowMain_meets hS hp_main hRead hCheck hShift hFeas hRes hAns
    · -- Vacuous when `¬ (2 < 2 ^ w)`: `NarrowMainFits` implies `7 ≤ w` hence `128 ≤ 2 ^ w`.
      refine ⟨_, hp_main, fun ⟨I, hv⟩ args => ?_⟩
      intro st ω h₁ h₂ c hpre
      obtain ⟨_, hpre'⟩ := Assn.pure_mul_apply.mp hpre
      obtain ⟨⟨_, hfits⟩, _⟩ := Assn.pure_credits_apply.mp hpre'
      have hk3 : 3 ≤ narrowLimbWidth I := three_le_narrowLimbWidth I
      have h2k1 : 2 * narrowLimbWidth I + 1 ≤ w := hfits.1
      have h2pow : 2 ^ 7 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
      exact False.elim (hw (by omega))

end MinCostFlow.NarrowTop
