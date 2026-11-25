module

public import WordRAM.Module
public import WordRAM.Std.Limbs
public import MinCostFlow.NarrowProg.LimbBit
public import MinCostFlow.NarrowProg.AccAdd
public import MinCostFlow.NarrowProg.PhaseWrite
public import MinCostFlow.NarrowProg.PhaseState
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Stage 2 phase update (`phaseUpdate`)

Updates the capped residual array `ρ̃`, capped flow array `g̃`, and lazy base-`2 ^ k`
accumulators `posAcc` / `negAcc` after one circulation-solver call in Stage 2 (Gabow bit scaling).
Zero-capacity dummy loops introduced by `Circulation.positiveInstance` are erased on the fly
using the current `ρ̃`, incoming capacity bit `b`, and `g̃`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Narrow

namespace MinCostFlow.NarrowProg

/-! ### Partial-update helpers for the loop invariant -/

private def partialUpdate (m : ℕ) (oldVal newVal : Fin m → ℕ) (i : ℕ) : List ℕ :=
  List.ofFn fun e : Fin m => if e.val < i then newVal e else oldVal e

private theorem partialUpdate_zero (m : ℕ) (oldVal newVal : Fin m → ℕ) :
    partialUpdate m oldVal newVal 0 = List.ofFn oldVal := by
  simp [partialUpdate]

private theorem partialUpdate_all (m : ℕ) (oldVal newVal : Fin m → ℕ) :
    partialUpdate m oldVal newVal m = List.ofFn newVal := by
  unfold partialUpdate; congr 1; funext e; simp [e.isLt]

@[local sep_len]
private theorem length_partialUpdate (m : ℕ) (oldVal newVal : Fin m → ℕ) (i : ℕ) :
    (partialUpdate m oldVal newVal i).length = m := by
  simp [partialUpdate]

private theorem getElem_partialUpdate {m i : ℕ} (oldVal newVal : Fin m → ℕ) (hi : i < m) :
    (partialUpdate m oldVal newVal i)[i]'(by rw [length_partialUpdate]; exact hi) = oldVal ⟨i, hi⟩ := by
  simp [partialUpdate]

private theorem set_partialUpdate {m i : ℕ} (oldVal newVal : Fin m → ℕ) (hi : i < m) :
    (partialUpdate m oldVal newVal i).set i (newVal ⟨i, hi⟩) =
      partialUpdate m oldVal newVal (i + 1) := by
  apply List.ext_getElem (by simp [partialUpdate])
  intro j hj1 hj2
  simp only [partialUpdate, List.length_ofFn] at hj2
  by_cases hji : j = i
  · subst hji; simp [partialUpdate]
  · rw [List.getElem_set_ne (by omega)]
    simp only [partialUpdate, List.getElem_ofFn]
    split_ifs <;> first | rfl | omega

private theorem list_split_one {pBase : ℕ} {xs : List ℕ} {i : ℕ} (hi : i < xs.length) :
    Assn.list pBase xs =
    Assn.list pBase (xs.take i) * (pBase + i ↦ xs[i]) *
      Assn.list (pBase + (i + 1)) (xs.drop (i + 1)) := by
  have hxs : xs = xs.take i ++ (xs[i] :: xs.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  conv_lhs => rw [hxs]
  rw [Assn.list_append, List.length_take_of_le (le_of_lt hi), Assn.list_cons, mul_assoc,
    Nat.add_assoc]

private theorem list_join_one {pBase : ℕ} {xs : List ℕ} {i : ℕ} (hi : i < xs.length) (v : ℕ) :
    Assn.list pBase (xs.take i) * (pBase + i ↦ v) *
      Assn.list (pBase + (i + 1)) (xs.drop (i + 1)) =
    Assn.list pBase (xs.set i v) := by
  have hxs : xs.set i v = xs.take i ++ (v :: xs.drop (i + 1)) := by
    apply List.ext_getElem
    · simp [List.length_take_of_le (le_of_lt hi)]; omega
    · intro j hj1 hj2
      rw [List.length_set] at hj1
      by_cases hlt : j < i
      · rw [List.getElem_set_ne (by omega), List.getElem_append_left (by simp [List.length_take_of_le (le_of_lt hi)]; omega),
          List.getElem_take]
      · by_cases heq : j = i
        · subst heq
          rw [List.getElem_set_self (by rw [List.length_set]; exact hi),
            List.getElem_append_right (by simp [List.length_take_of_le (le_of_lt hi)])]
          simp [List.length_take_of_le (le_of_lt hi)]
        · rw [List.getElem_set_ne (by omega),
            List.getElem_append_right (by simp [List.length_take_of_le (le_of_lt hi)]; omega)]
          have hsub : j - (xs.take i).length = (j - (i + 1)) + 1 := by
            rw [List.length_take_of_le (le_of_lt hi)]; omega
          simp only [hsub, List.getElem_cons_succ, List.getElem_drop]
          congr 1; omega
  rw [hxs, Assn.list_append, List.length_take_of_le (le_of_lt hi), Assn.list_cons, mul_assoc,
    Nat.add_assoc]

private theorem list_split_partialUpdate {pBase m i : ℕ} (oldVal newVal : Fin m → ℕ) (hi : i < m) :
    Assn.list pBase (partialUpdate m oldVal newVal i) =
    Assn.list pBase ((partialUpdate m oldVal newVal i).take i) * (pBase + i ↦ oldVal ⟨i, hi⟩) *
      Assn.list (pBase + (i + 1)) ((partialUpdate m oldVal newVal i).drop (i + 1)) := by
  have hlen : i < (partialUpdate m oldVal newVal i).length := by
    rw [length_partialUpdate]; exact hi
  rw [list_split_one hlen, getElem_partialUpdate oldVal newVal hi]

private theorem list_join_partialUpdate {pBase m i : ℕ} (oldVal newVal : Fin m → ℕ) (hi : i < m) :
    Assn.list pBase ((partialUpdate m oldVal newVal i).take i) * (pBase + i ↦ newVal ⟨i, hi⟩) *
      Assn.list (pBase + (i + 1)) ((partialUpdate m oldVal newVal i).drop (i + 1)) =
    Assn.list pBase (partialUpdate m oldVal newVal (i + 1)) := by
  have hlen : i < (partialUpdate m oldVal newVal i).length := by
    rw [length_partialUpdate]; exact hi
  rw [list_join_one hlen (newVal ⟨i, hi⟩), set_partialUpdate oldVal newVal hi]

private theorem list_partialUpdate_all {pBase m : ℕ} (oldVal newVal : Fin m → ℕ) :
    Assn.list pBase (partialUpdate m oldVal newVal m) = Assn.list pBase (List.ofFn newVal) := by
  rw [partialUpdate_all]

private def partialAcc (m : ℕ) (oldAcc newAcc : Fin m → List ℕ) (i : ℕ) (j : ℕ) : List ℕ :=
  if h : j < m then (if j < i then newAcc ⟨j, h⟩ else oldAcc ⟨j, h⟩) else []

private theorem partialAcc_zero (m : ℕ) (oldAcc newAcc : Fin m → List ℕ) (j : ℕ) :
    partialAcc m oldAcc newAcc 0 j = if h : j < m then oldAcc ⟨j, h⟩ else [] := by
  unfold partialAcc; simp

private theorem partialAcc_all (m : ℕ) (oldAcc newAcc : Fin m → List ℕ) {j : ℕ} (hj : j < m) :
    partialAcc m oldAcc newAcc m j = newAcc ⟨j, hj⟩ := by
  unfold partialAcc; simp [hj]

private theorem list_partialAcc_self {pBase L m i : ℕ} (oldAcc newAcc : Fin m → List ℕ)
    (hi : i < m) :
    Assn.list (pBase + i * L) (partialAcc m oldAcc newAcc i i) =
    Assn.list (pBase + i * L) (oldAcc ⟨i, hi⟩) := by
  congr 1; unfold partialAcc; simp [hi]

private theorem list_partialAcc_succ {pBase L m i : ℕ} (oldAcc newAcc : Fin m → List ℕ)
    {xs : List ℕ} (hi : i < m) (hxs : xs = newAcc ⟨i, hi⟩) :
    Assn.list (pBase + i * L) xs =
    Assn.list (pBase + i * L) (partialAcc m oldAcc newAcc (i + 1) i) := by
  congr 1; rw [hxs]; unfold partialAcc; simp [hi]

private theorem partialAcc_prod_erase_eq {pBase L m i : ℕ}
    (oldAcc newAcc : Fin m → List ℕ) :
    (∏ j ∈ (Finset.range m).erase i,
      Assn.list (pBase + j * L) (partialAcc m oldAcc newAcc i j)) =
    (∏ j ∈ (Finset.range m).erase i,
      Assn.list (pBase + j * L) (partialAcc m oldAcc newAcc (i + 1) j)) := by
  refine Finset.prod_congr rfl fun j hj => ?_
  have hne : j ≠ i := (Finset.mem_erase.mp hj).1
  congr 1; unfold partialAcc
  split_ifs <;> first | rfl | omega

/-! ### Branchless-loop helpers (`nzLoad`, `clamp`, and `phaseUpdateEdge`) -/

/-- Return `mem[p + idx]` when `0 < cond`, else `0`. -/
wram_def nzLoad (p, idx, cond) {
  v := 0
  if 0 < cond {
    v := mem[p + idx]
  }
  return v
}

/-- Specification of `nzLoad`: conditionally reads `xs[idx]` when `0 < cond`. -/
def nzLoadSpec (w : ℕ) : Spec (List ℕ × ℕ × ℕ) where
  pre := fun (xs, idx, cond) args => ⨆ p : ℕ,
    ⌜args = [p, idx, cond] ∧ idx < xs.length ∧ 1 < 2 ^ w⌝ * Assn.list p xs
  post := fun (xs, idx, cond) args v => ⨆ p : ℕ,
    ⌜args = [p, idx, cond] ∧ v = if 0 < cond then xs.getD idx 0 else 0⌝ * Assn.list p xs

theorem nzLoad_meets {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some nzLoad) :
    Meets w p f ((nzLoadSpec w).withCost fun _ _ => 25) := by
  sep_enter ⟨xs, idx, cond⟩ with hidx hw
  sep_run

/-- Return `min x M`. -/
wram_def clamp (x, M) {
  if M < x {
    x := M
  }
  return x
}

/-- Specification of `clamp`: returns `min x M`. -/
def clampSpec (w : ℕ) : Spec (ℕ × ℕ) where
  pre := fun (x, M) args => ⌜args = [x, M] ∧ 1 < 2 ^ w⌝
  post := fun (x, M) args v => ⌜args = [x, M] ∧ v = min x M⌝

theorem clamp_meets {w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some clamp) :
    Meets w p f ((clampSpec w).withCost fun _ _ => 20) := by
  sep_enter ⟨x, M⟩ with hw
  sep_run

/-- Named value for `phaseUpdateEdgeSpec`. -/
structure PhaseUpdateEdgeData where
  I : Circulation
  k : ℕ
  capLimb : List ℕ
  T : ℕ
  t : ℕ
  g : Fin I.m → ℤ
  flow : List ℕ
  posAcc : List ℕ
  negAcc : List ℕ
  e : Fin I.m

/-- Update a single edge `e` (`ρ̃ e`, `g̃ e`, `posAcc e`, `negAcc e`) in `O(1)` steps. -/
wram_def phaseUpdateEdge (lb acc nzl clmp : ℕ)
    (pCap, capLen, pRhoI, pGCapI, pSolFlow, pPosI, pNegI, m, i, k, shift) {
  rho := mem[pRhoI]
  gcap := mem[pGCapI]
  b := lb(pCap, capLen, shift, k)
  twoRhoB := 2 * rho + b
  df := nzl(pSolFlow, i, twoRhoB)
  dr := nzl(pSolFlow, m + i, gcap)
  M := m + 1
  nRho := clmp(twoRhoB + dr - df, M)
  mem[pRhoI] := nRho
  nGCap := clmp(2 * gcap + df - dr, M)
  mem[pGCapI] := nGCap
  r := acc(pPosI, df, shift, k)
  r := acc(pNegI, dr, shift, k)
  return 0
}

/-- Specification of `phaseUpdateEdge`: updates one edge's capped residual, capped flow, and
positive/negative accumulators. -/
def phaseUpdateEdgeSpec (w : ℕ) : Spec PhaseUpdateEdgeData where
  pre d args := ⨆ (pCap : ℕ) (pRhoI : ℕ) (pGCapI : ℕ) (pSolFlow : ℕ) (pPosI : ℕ) (pNegI : ℕ)
      (shift : ℕ),
    let L := d.T / d.k + 2
    ⌜args = [pCap, d.capLimb.length, pRhoI, pGCapI, pSolFlow, pPosI, pNegI, d.I.m, d.e.val, d.k,
        shift] ∧
      shift = d.T - 1 - d.t ∧ d.t < d.T ∧
      Limbs d.k d.capLimb ∧ Nat.ofDigits (2 ^ d.k) d.capLimb = d.I.capacity d.e ∧
      1 ≤ d.k ∧ 2 * d.k ≤ w ∧ d.k + Nat.log 2 (2 * d.k) + 2 ≤ w ∧
      d.I.m + 1 < 2 ^ d.k ∧ 3 * d.I.m + 5 < 2 ^ w ∧
      d.flow.length = 2 * d.I.m ∧
      (truncInstance d.I (d.T - d.t)).Optimal (fun e => (d.g e : ℝ)) ∧
      (bitScalePhaseInstance d.I d.T d.t d.g).positiveInstance.Optimal
        (fun a => ((d.flow.getD a.val 0 : ℕ) : ℝ)) ∧
      d.posAcc.length = L ∧ d.negAcc.length = L ∧
      (∀ j < L,
        d.posAcc.getD j 0 ≤ accTouches d.k d.T d.t j * (2 ^ d.k - 1) ∧
        d.negAcc.getD j 0 ≤ accTouches d.k d.T d.t j * (2 ^ d.k - 1))⌝ *
    Assn.list pCap d.capLimb *
    (pRhoI ↦ cappedResidual d.I d.T d.t d.g (d.I.m + 1) d.e) *
    (pGCapI ↦ cappedFlow d.g (d.I.m + 1) d.e) *
    Assn.list pSolFlow d.flow *
    Assn.list pPosI d.posAcc *
    Assn.list pNegI d.negAcc
  post d args v := ⨆ (pCap : ℕ) (pRhoI : ℕ) (pGCapI : ℕ) (pSolFlow : ℕ) (pPosI : ℕ) (pNegI : ℕ)
      (shift : ℕ),
    let g' := nextGhostFlow d.I d.T d.t d.g d.flow
    ⌜args = [pCap, d.capLimb.length, pRhoI, pGCapI, pSolFlow, pPosI, pNegI, d.I.m, d.e.val, d.k,
        shift] ∧ v = 0⌝ *
    Assn.list pCap d.capLimb *
    (pRhoI ↦ cappedResidual d.I d.T (d.t + 1) g' (d.I.m + 1) d.e) *
    (pGCapI ↦ cappedFlow g' (d.I.m + 1) d.e) *
    Assn.list pSolFlow d.flow *
    Assn.list pPosI (accAddResult d.k d.posAcc
      (erasedDelta d.I d.T d.t d.g d.flow (Fin.castAdd d.I.m d.e)).toNat (d.T - 1 - d.t)) *
    Assn.list pNegI (accAddResult d.k d.negAcc
      (erasedDelta d.I d.T d.t d.g d.flow (Fin.natAdd d.I.m d.e)).toNat (d.T - 1 - d.t))

theorem phaseUpdateEdge_meets {w : ℕ} {p : Program} {f lb acc nzl clmp Tlb Tacc Tnzl Tclmp : ℕ}
    (hp : p.procs[f]? = some (phaseUpdateEdge lb acc nzl clmp))
    (hlb : Meets w p lb ((limbBitSpec w).withCost fun _ _ => Tlb))
    (hacc : Meets w p acc ((accAddSpec w).withCost fun _ _ => Tacc))
    (hnzl : Meets w p nzl ((nzLoadSpec w).withCost fun _ _ => Tnzl))
    (hclmp : Meets w p clmp ((clampSpec w).withCost fun _ _ => Tclmp)) :
    Meets w p f ((phaseUpdateEdgeSpec w).withCost fun _ _ =>
      Tlb + 2 * Tacc + 2 * Tnzl + 2 * Tclmp + 110) := by
  sep_enter ⟨I, k, capLimb, T, t, g, flow, posAcc, negAcc, e⟩ with
    hshift ht hL hV hk h2kw hkw hm_lt hw hflow_len hg hsol hpos_len hneg_len hacc_bd
  have hrho_le : cappedResidual I T t g (I.m + 1) e ≤ I.m + 1 := Nat.min_le_right _ _
  have hgcap_le : cappedFlow g (I.m + 1) e ≤ I.m + 1 := Nat.min_le_right _ _
  sep_step
  sep_step
  sep_step from (k, capLimb, shift)
  have hbi : b = capBit I (T - 1 - t) e := by rw [hb, hV, hshift]; rfl
  have hb_le : b ≤ 1 := by rw [hbi]; unfold capBit; omega
  sep_step
  have htwo_eq : twoRhoB = 2 * cappedResidual I T t g (I.m + 1) e + capBit I (T - 1 - t) e := by
    rw [htwoRhoB, hrho, hbi]
  sep_step from (flow, e.val, twoRhoB)
  sep_step from (flow, I.m + e.val, gcap)
  sep_step
  subst M
  have hdf_eq : df = (erasedDelta I T t g flow (Fin.castAdd I.m e)).toNat := by
    rw [hdf, htwo_eq]; exact (erasedDelta_fwd_toNat hg.1 e).symm
  have hdr_eq : dr = (erasedDelta I T t g flow (Fin.natAdd I.m e)).toNat := by
    rw [hdr, hgcap]; exact (erasedDelta_rev_toNat hg.1 e).symm
  have ⟨hdf_bd, hdr_bd⟩ := erasedDelta_bounds hg.1 hsol e
  have hdf_le_two : df ≤ twoRhoB := by
    rw [hdf_eq, htwo_eq]; exact le_trans hdf_bd (Nat.min_le_left _ _)
  have hdf_le_M : df ≤ I.m + 1 := by
    rw [hdf_eq]; exact le_trans hdf_bd (Nat.min_le_right _ _)
  have hdr_le_two : dr ≤ 2 * gcap := by
    rw [hdr_eq, hgcap]; exact le_trans hdr_bd (Nat.min_le_left _ _)
  have hdr_le_M : dr ≤ I.m + 1 := by
    rw [hdr_eq]; exact le_trans hdr_bd (Nat.min_le_right _ _)
  have htwo_le : twoRhoB ≤ 2 * (I.m + 1) + 1 := by omega
  sep_step from (twoRhoB + dr - df, I.m + 1)
  have hnRho_eq : nRho = cappedResidual I T (t + 1) (nextGhostFlow I T t g flow) (I.m + 1) e := by
    rw [hnRho, htwo_eq, hdf_eq, hdr_eq]; exact (nextCappedResidual_eq ht hg.1 hsol e).symm
  sep_step
  sep_step from (2 * gcap + df - dr, I.m + 1)
  have hnGCap_eq : nGCap = cappedFlow (nextGhostFlow I T t g flow) (I.m + 1) e := by
    rw [hnGCap, hgcap, hdf_eq, hdr_eq]; exact (nextCappedFlow_eq hg.1 hsol e).symm
  sep_step
  have hdf_lt_pow : df < 2 ^ k := by omega
  have hdr_lt_pow : dr < 2 ^ k := by omega
  have hfitPos : (T - 1 - t) / k + 1 < posAcc.length := by
    rw [hpos_len]
    have hdiv : (T - 1 - t) / k ≤ T / k := Nat.div_le_div_right (by omega)
    omega
  have hfitNeg : (T - 1 - t) / k + 1 < negAcc.length := by
    rw [hneg_len]
    have hdiv : (T - 1 - t) / k ≤ T / k := Nat.div_le_div_right (by omega)
    omega
  obtain ⟨hpos_lo, hpos_hi⟩ := accAdd_limbs_lt_word hk hkw ht hdf_lt_pow hfitPos
    (fun j hj => (hacc_bd j (by rwa [hpos_len] at hj)).1)
  obtain ⟨hneg_lo, hneg_hi⟩ := accAdd_limbs_lt_word hk hkw ht hdr_lt_pow hfitNeg
    (fun j hj => (hacc_bd j (by rwa [hneg_len] at hj)).2)
  rw [← hshift] at hfitPos hfitNeg hpos_lo hpos_hi hneg_lo hneg_hi
  sep_step from (k, posAcc, df, shift)
  sep_step from (k, negAcc, dr, shift)
  sep_run

/-! ### The `phaseUpdate` procedure -/

/-- Named value for `phaseUpdateSpec`. -/
structure PhaseUpdateData where
  I : Circulation
  k : ℕ
  capPtrs : List ℕ
  capLimbs : List (List ℕ)
  ptrs : BitScalePtrs
  pRho : ℕ
  pGCap : ℕ
  pPosAcc : ℕ
  pNegAcc : ℕ
  T : ℕ
  t : ℕ
  g : Fin I.m → ℤ
  flow : List ℕ
  posAcc : Fin I.m → List ℕ
  negAcc : Fin I.m → List ℕ

/-- Update `ρ̃`, `g̃`, `posAcc`, and `negAcc` across all `m` edges after one phase solver call. -/
wram_def phaseUpdate (edge : ℕ) (pIn, pState, pSolFlow, shift) {
  m := mem[pIn + 1]
  k := mem[pIn + 2]
  pCapPtrs := mem[pIn + 7]
  pCapLens := mem[pIn + 8]
  pRho := mem[pState]
  pGCap := mem[pState + 1]
  pPosAcc := mem[pState + 2]
  pNegAcc := mem[pState + 3]
  L := mem[pState + 4]
  off := 0
  for i in 0 .. m {
    r := edge(mem[pCapPtrs + i], mem[pCapLens + i], pRho + i, pGCap + i,
              pSolFlow, pPosAcc + off, pNegAcc + off, m, i, k, shift)
    off := off + L
  }
  return 0
}

/-- Specification of `phaseUpdate`: advances all Stage 2 phase invariants from `t` to `t + 1`. -/
def phaseUpdateSpec (w : ℕ) : Spec PhaseUpdateData where
  pre d args := ⨆ (pIn : ℕ) (pState : ℕ) (pSolFlow : ℕ) (shift : ℕ),
    let L := d.T / d.k + 2
    ⌜args = [pIn, pState, pSolFlow, shift] ∧
      shift = d.T - 1 - d.t ∧ d.t < d.T ∧
      d.capPtrs.length = d.I.m ∧ d.capLimbs.length = d.I.m ∧
      (∀ j (hj : j < d.I.m), Limbs d.k (d.capLimbs.getD j []) ∧
        Nat.ofDigits (2 ^ d.k) (d.capLimbs.getD j []) = d.I.capacity ⟨j, hj⟩) ∧
      1 ≤ d.k ∧ 2 * d.k ≤ w ∧ d.k + Nat.log 2 (2 * d.k) + 2 ≤ w ∧
      d.I.m + 1 < 2 ^ d.k ∧ 3 * d.I.m + 5 < 2 ^ w ∧ d.I.m * L < 2 ^ w ∧
      d.pPosAcc + d.I.m * L ≤ 2 ^ w ∧ d.pNegAcc + d.I.m * L ≤ 2 ^ w ∧
      d.flow.length = 2 * d.I.m ∧
      (truncInstance d.I (d.T - d.t)).Optimal (fun e => (d.g e : ℝ)) ∧
      (bitScalePhaseInstance d.I d.T d.t d.g).positiveInstance.Optimal
        (fun a => ((d.flow.getD a.val 0 : ℕ) : ℝ)) ∧
      (∀ e : Fin d.I.m, (d.posAcc e).length = L ∧ (d.negAcc e).length = L) ∧
      (∀ e : Fin d.I.m, ∀ j < L,
        (d.posAcc e).getD j 0 ≤ accTouches d.k d.T d.t j * (2 ^ d.k - 1) ∧
        (d.negAcc e).getD j 0 ≤ accTouches d.k d.T d.t j * (2 ^ d.k - 1)) ∧
      (∀ e : Fin d.I.m,
        ((Nat.ofDigits (2 ^ d.k) (d.posAcc e) : ℕ) : ℤ) -
          ((Nat.ofDigits (2 ^ d.k) (d.negAcc e) : ℕ) : ℤ) =
            d.g e * (2 : ℤ) ^ (d.T - d.t)) ∧
      (∀ e : Fin d.I.m,
        Nat.ofDigits (2 ^ d.k) (d.posAcc e) ≤ (d.I.m + 1) * (2 ^ d.T - 2 ^ (d.T - d.t)) ∧
        Nat.ofDigits (2 ^ d.k) (d.negAcc e) ≤ (d.I.m + 1) * (2 ^ d.T - 2 ^ (d.T - d.t)))⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pState [d.pRho, d.pGCap, d.pPosAcc, d.pNegAcc, L] *
    Assn.list pSolFlow d.flow *
    Assn.list d.pRho (List.ofFn fun e => cappedResidual d.I d.T d.t d.g (d.I.m + 1) e) *
    Assn.list d.pGCap (List.ofFn fun e => cappedFlow d.g (d.I.m + 1) e) *
    (∏ j ∈ Finset.range d.I.m,
      Assn.list (d.pPosAcc + j * L) (if h : j < d.I.m then d.posAcc ⟨j, h⟩ else [])) *
    (∏ j ∈ Finset.range d.I.m,
      Assn.list (d.pNegAcc + j * L) (if h : j < d.I.m then d.negAcc ⟨j, h⟩ else []))
  post d args v := ⨆ (pIn : ℕ) (pState : ℕ) (pSolFlow : ℕ) (shift : ℕ),
    let L := d.T / d.k + 2
    let g' := nextGhostFlow d.I d.T d.t d.g d.flow
    let pos' := nextPosAcc d.I d.k d.T d.t d.g d.flow d.posAcc
    let neg' := nextNegAcc d.I d.k d.T d.t d.g d.flow d.negAcc
    ⌜args = [pIn, pState, pSolFlow, shift] ∧ v = 0 ∧
      (truncInstance d.I (d.T - (d.t + 1))).Optimal (fun e => (g' e : ℝ)) ∧
      (∀ e : Fin d.I.m, (pos' e).length = L ∧ (neg' e).length = L) ∧
      (∀ e : Fin d.I.m, ∀ j < L,
        (pos' e).getD j 0 ≤ accTouches d.k d.T (d.t + 1) j * (2 ^ d.k - 1) ∧
        (neg' e).getD j 0 ≤ accTouches d.k d.T (d.t + 1) j * (2 ^ d.k - 1)) ∧
      (∀ e : Fin d.I.m,
        ((Nat.ofDigits (2 ^ d.k) (pos' e) : ℕ) : ℤ) -
          ((Nat.ofDigits (2 ^ d.k) (neg' e) : ℕ) : ℤ) =
            g' e * (2 : ℤ) ^ (d.T - (d.t + 1))) ∧
      (∀ e : Fin d.I.m,
        Nat.ofDigits (2 ^ d.k) (pos' e) ≤ (d.I.m + 1) * (2 ^ d.T - 2 ^ (d.T - (d.t + 1))) ∧
        Nat.ofDigits (2 ^ d.k) (neg' e) ≤ (d.I.m + 1) * (2 ^ d.T - 2 ^ (d.T - (d.t + 1))))⌝ *
    bitScaleInput d.I d.k d.capPtrs d.capLimbs pIn d.ptrs.pTail d.ptrs.pHead d.ptrs.pCSign
      d.ptrs.pCMag d.ptrs.pCapPtrs d.ptrs.pCapLens *
    Assn.list pState [d.pRho, d.pGCap, d.pPosAcc, d.pNegAcc, L] *
    Assn.list pSolFlow d.flow *
    Assn.list d.pRho (List.ofFn fun e => cappedResidual d.I d.T (d.t + 1) g' (d.I.m + 1) e) *
    Assn.list d.pGCap (List.ofFn fun e => cappedFlow g' (d.I.m + 1) e) *
    (∏ j ∈ Finset.range d.I.m,
      Assn.list (d.pPosAcc + j * L) (if h : j < d.I.m then pos' ⟨j, h⟩ else [])) *
    (∏ j ∈ Finset.range d.I.m,
      Assn.list (d.pNegAcc + j * L) (if h : j < d.I.m then neg' ⟨j, h⟩ else []))

/-- `phaseUpdate` updates all `m` edges in `(Tedge + 60) * m + 120` steps. -/
theorem phaseUpdate_meets {w : ℕ} {p : Program} {f edge Tedge : ℕ}
    (hp : p.procs[f]? = some (phaseUpdate edge))
    (hedge : Meets w p edge ((phaseUpdateEdgeSpec w).withCost fun _ _ => Tedge)) :
    Meets w p f ((phaseUpdateSpec w).withCost fun d _ => (Tedge + 60) * d.I.m + 120) := by
  sep_enter ⟨I, k, capPtrs, capLimbs, ⟨pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens⟩,
    pRho, pGCap, pPosAcc, pNegAcc, T, t, g, flow, posAcc, negAcc⟩ with
    hshift ht hptrs hlimbs hcaps hk h2kw hkw hm_lt hw hmL hpPos_fit hpNeg_fit hflow_len hg hsol
    hacc_len hacc_bd hacc_diff hacc_val
  set L := T / k + 2
  generalize hg'_def : nextGhostFlow I T t g flow = g'
  generalize hpos'_def : nextPosAcc I k T t g flow posAcc = pos'
  generalize hneg'_def : nextNegAcc I k T t g flow negAcc = neg'
  generalize holdRho_def : (fun e => cappedResidual I T t g (I.m + 1) e) = oldRho
  generalize hnewRho_def : (fun e => cappedResidual I T (t + 1) g' (I.m + 1) e) = newRho
  generalize holdGCap_def : (fun e => cappedFlow g (I.m + 1) e) = oldGCap
  generalize hnewGCap_def : (fun e => cappedFlow g' (I.m + 1) e) = newGCap
  sep_apply bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens
  sep_step; sep_step; sep_step; sep_step
  sep_step; sep_step; sep_step; sep_step; sep_step
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hm hk_1 hpCapPtrs_1 hpCapLens_1 hpRho_1 hpGCap_1 hpPosAcc_1 hpNegAcc_1 hL_1
  subst m k_1 pCapPtrs_1 pCapLens_1 pRho_1 pGCap_1 pPosAcc_1 pNegAcc_1 L_1
  sep_step
  generalize hF_def :
    (Assn.list pIn [I.n, I.m, k, pTail, pHead, pCSign, pCMag, pCapPtrs, pCapLens] *
     Assn.list pTail (List.ofFn fun e : Fin I.m => (I.tail e).val) *
     Assn.list pHead (List.ofFn fun e : Fin I.m => (I.head e).val) *
     Assn.list pCSign (List.ofFn fun e : Fin I.m => if I.cost e < 0 then 1 else 0) *
     Assn.list pCMag (List.ofFn fun e : Fin I.m => (I.cost e).natAbs) *
     Assn.list pState [pRho, pGCap, pPosAcc, pNegAcc, L]) = F
  sep_apply hF_def
  have hrho0 : Assn.list pRho (List.ofFn oldRho) =
      Assn.list pRho (partialUpdate I.m oldRho newRho 0) := by rw [partialUpdate_zero]
  have hgcap0 : Assn.list pGCap (List.ofFn oldGCap) =
      Assn.list pGCap (partialUpdate I.m oldGCap newGCap 0) := by rw [partialUpdate_zero]
  have hpos0 : (∏ j ∈ Finset.range I.m,
        Assn.list (pPosAcc + j * L) (if h : j < I.m then posAcc ⟨j, h⟩ else [])) =
      (∏ j ∈ Finset.range I.m, Assn.list (pPosAcc + j * L) (partialAcc I.m posAcc pos' 0 j)) := by
    refine Finset.prod_congr rfl fun j _ => by rw [partialAcc_zero]
  have hneg0 : (∏ j ∈ Finset.range I.m,
        Assn.list (pNegAcc + j * L) (if h : j < I.m then negAcc ⟨j, h⟩ else [])) =
      (∏ j ∈ Finset.range I.m, Assn.list (pNegAcc + j * L) (partialAcc I.m negAcc neg' 0 j)) := by
    refine Finset.prod_congr rfl fun j _ => by rw [partialAcc_zero]
  sep_apply hrho0
  sep_apply hgcap0
  sep_apply hpos0
  sep_apply hneg0
  sep_for (fun i (r0 : ℕ) =>
    ⟨[pIn, pState, pSolFlow, shift, I.m, k, pCapPtrs, pCapLens, pRho, pGCap, pPosAcc, pNegAcc, L,
      i * L, i, r0],
      i ≤ I.m, (Tedge + 40) * (I.m - i) + 10,
      [F,
       Assn.list pCapPtrs capPtrs,
       Assn.list pCapLens (capLimbs.map List.length),
       ∏ j ∈ Finset.range I.m, Assn.list (capPtrs.getD j 0) (capLimbs.getD j []),
       Assn.list pSolFlow flow,
       Assn.list pRho (partialUpdate I.m oldRho newRho i),
       Assn.list pGCap (partialUpdate I.m oldGCap newGCap i),
       ∏ j ∈ Finset.range I.m, Assn.list (pPosAcc + j * L) (partialAcc I.m posAcc pos' i j),
       ∏ j ∈ Finset.range I.m, Assn.list (pNegAcc + j * L) (partialAcc I.m negAcc neg' i j)]⟩)
    with r0
  · set e : Fin I.m := ⟨i, hhi⟩
    have hmem : i ∈ Finset.range I.m := Finset.mem_range.mpr hhi
    have hxi : capLimbs.getD i [] = capLimbs[i]'(by omega) :=
      List.getD_eq_getElem capLimbs [] (by omega)
    have hpi : capPtrs.getD i 0 = capPtrs[i]'(by omega) :=
      List.getD_eq_getElem capPtrs 0 (by omega)
    have hLi : Limbs k (capLimbs.getD i []) := (hcaps i hhi).1
    have hVi : Nat.ofDigits (2 ^ k) (capLimbs.getD i []) = I.capacity e := (hcaps i hhi).2
    have hL_pos : 0 < L := Nat.succ_pos _
    have hiL_lt : i * L < I.m * L := Nat.mul_lt_mul_of_pos_right hhi hL_pos
    have hpPos_lt : pPosAcc + i * L < 2 ^ w := by omega
    have hpNeg_lt : pNegAcc + i * L < 2 ^ w := by omega
    have hpos_len_e : (posAcc e).length = L := (hacc_len e).1
    have hneg_len_e : (negAcc e).length = L := (hacc_len e).2
    have hbd_e : ∀ j < L,
        (posAcc e).getD j 0 ≤ accTouches k T t j * (2 ^ k - 1) ∧
        (negAcc e).getD j 0 ≤ accTouches k T t j * (2 ^ k - 1) := hacc_bd e
    -- Split out the single edge's cells and accumulators
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (capPtrs.getD j 0) (capLimbs.getD j []))
    sep_apply list_split_partialUpdate (pBase := pRho) oldRho newRho hhi
    sep_apply list_split_partialUpdate (pBase := pGCap) oldGCap newGCap hhi
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pPosAcc + j * L) (partialAcc I.m posAcc pos' i j))
    sep_apply list_partialAcc_self (pBase := pPosAcc) (L := L) posAcc pos' hhi
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pNegAcc + j * L) (partialAcc I.m negAcc neg' i j))
    sep_apply list_partialAcc_self (pBase := pNegAcc) (L := L) negAcc neg' hhi
    have holdRho_e : (pRho + i ↦ oldRho e) =
        (pRho + i ↦ cappedResidual I T t g (I.m + 1) e) := by rw [← holdRho_def]
    have holdGCap_e : (pGCap + i ↦ oldGCap e) = (pGCap + i ↦ cappedFlow g (I.m + 1) e) := by
      rw [← holdGCap_def]
    sep_apply holdRho_e
    sep_apply holdGCap_e
    -- Call `phaseUpdateEdge`
    let dEdge : PhaseUpdateEdgeData :=
      { I := I, k := k, capLimb := capLimbs.getD i [], T := T, t := t, g := g,
        flow := flow, posAcc := posAcc e, negAcc := negAcc e, e := e }
    sep_step from dEdge
    -- Re-join updated cells and accumulators
    have hnewRho_e : (pRho + i ↦ cappedResidual I T (t + 1) (nextGhostFlow I T t g flow) (I.m + 1) e) =
        (pRho + i ↦ newRho e) := by rw [← hnewRho_def, ← hg'_def]
    have hnewGCap_e : (pGCap + i ↦ cappedFlow (nextGhostFlow I T t g flow) (I.m + 1) e) =
        (pGCap + i ↦ newGCap e) := by rw [← hnewGCap_def, ← hg'_def]
    sep_apply hnewRho_e
    sep_apply hnewGCap_e
    sep_apply list_join_partialUpdate (pBase := pRho) oldRho newRho hhi
    sep_apply list_join_partialUpdate (pBase := pGCap) oldGCap newGCap hhi
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (capPtrs.getD j 0) (capLimbs.getD j []))).symm
    have hpos_res : accAddResult k (posAcc e)
        (erasedDelta I T t g flow (Fin.castAdd I.m e)).toNat (T - 1 - t) = pos' e := by
      rw [← hpos'_def]; rfl
    have hneg_res : accAddResult k (negAcc e)
        (erasedDelta I T t g flow (Fin.natAdd I.m e)).toNat (T - 1 - t) = neg' e := by
      rw [← hneg'_def]; rfl
    sep_apply list_partialAcc_succ (pBase := pPosAcc) (L := L) posAcc pos' hhi hpos_res
    sep_apply partialAcc_prod_erase_eq (pBase := pPosAcc) (L := L) (i := i) posAcc pos'
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pPosAcc + j * L) (partialAcc I.m posAcc pos' (i + 1) j))).symm
    sep_apply list_partialAcc_succ (pBase := pNegAcc) (L := L) negAcc neg' hhi hneg_res
    sep_apply partialAcc_prod_erase_eq (pBase := pNegAcc) (L := L) (i := i) negAcc neg'
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pNegAcc + j * L) (partialAcc I.m negAcc neg' (i + 1) j))).symm
    have hoff_next : i * L + L = (i + 1) * L := by ring
    have hoff_lt : i * L + L < 2 ^ w := by
      rw [hoff_next]
      exact lt_of_le_of_lt (Nat.mul_le_mul_right L (by omega : i + 1 ≤ I.m)) hmL
    sep_run
    dsimp only [dEdge]; rw [List.getElem_map, hxi]
  · -- Post-loop: rewrite partial arrays to final arrays and discharge invariants
    subst F
    sep_norm
    sep_apply list_partialUpdate_all (pBase := pRho) oldRho newRho
    sep_apply list_partialUpdate_all (pBase := pGCap) oldGCap newGCap
    have hpos_all : (∏ j ∈ Finset.range I.m,
          Assn.list (pPosAcc + j * L) (partialAcc I.m posAcc pos' I.m j)) =
        (∏ j ∈ Finset.range I.m,
          Assn.list (pPosAcc + j * L) (if h : j < I.m then pos' ⟨j, h⟩ else [])) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' : j < I.m := Finset.mem_range.mp hj
      simp only [partialAcc_all I.m posAcc pos' hj', hj', ↓reduceDIte]
    have hneg_all : (∏ j ∈ Finset.range I.m,
          Assn.list (pNegAcc + j * L) (partialAcc I.m negAcc neg' I.m j)) =
        (∏ j ∈ Finset.range I.m,
          Assn.list (pNegAcc + j * L) (if h : j < I.m then neg' ⟨j, h⟩ else [])) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' : j < I.m := Finset.mem_range.mp hj
      simp only [partialAcc_all I.m negAcc neg' hj', hj', ↓reduceDIte]
    sep_apply hpos_all
    sep_apply hneg_all
    sep_apply (bitScaleInput_eq I k capPtrs capLimbs pIn pTail pHead pCSign pCMag pCapPtrs pCapLens).symm
    subst hg'_def hpos'_def hneg'_def hnewRho_def hnewGCap_def
    have hopt' : (truncInstance I (T - (t + 1))).Optimal (fun e => (nextGhostFlow I T t g flow e : ℝ)) :=
      nextGhostFlow_optimal ht hg hsol
    have hlen' : ∀ e : Fin I.m,
        (nextPosAcc I k T t g flow posAcc e).length = L ∧
        (nextNegAcc I k T t g flow negAcc e).length = L := fun e =>
      ⟨by rw [nextPosAcc, length_accAddResult, (hacc_len e).1],
       by rw [nextNegAcc, length_accAddResult, (hacc_len e).2]⟩
    have hfit_all : ∀ e : Fin I.m, (T - 1 - t) / k + 1 < L := fun _ => by
      have hdiv : (T - 1 - t) / k ≤ T / k := Nat.div_le_div_right (by omega)
      omega
    have hbd' : ∀ e : Fin I.m, ∀ j < L,
        (nextPosAcc I k T t g flow posAcc e).getD j 0 ≤ accTouches k T (t + 1) j * (2 ^ k - 1) ∧
        (nextNegAcc I k T t g flow negAcc e).getD j 0 ≤ accTouches k T (t + 1) j * (2 ^ k - 1) := by
      intro e j hj
      have ⟨hdf_bd, hdr_bd⟩ := erasedDelta_bounds hg.1 hsol e
      have hdf_lt : (erasedDelta I T t g flow (Fin.castAdd I.m e)).toNat < 2 ^ k :=
        lt_of_le_of_lt (le_trans hdf_bd (Nat.min_le_right _ _)) hm_lt
      have hdr_lt : (erasedDelta I T t g flow (Fin.natAdd I.m e)).toNat < 2 ^ k :=
        lt_of_le_of_lt (le_trans hdr_bd (Nat.min_le_right _ _)) hm_lt
      refine ⟨accAddResult_limb_bound hk ht hdf_lt (by rw [(hacc_len e).1]; exact hfit_all e)
          (fun j' hj' => (hacc_bd e j' (by rwa [(hacc_len e).1] at hj')).1) j
          (by rw [length_accAddResult, (hacc_len e).1]; exact hj),
        accAddResult_limb_bound hk ht hdr_lt (by rw [(hacc_len e).2]; exact hfit_all e)
          (fun j' hj' => (hacc_bd e j' (by rwa [(hacc_len e).2] at hj')).2) j
          (by rw [length_accAddResult, (hacc_len e).2]; exact hj)⟩
    have hdiff' : ∀ e : Fin I.m,
        ((Nat.ofDigits (2 ^ k) (nextPosAcc I k T t g flow posAcc e) : ℕ) : ℤ) -
          ((Nat.ofDigits (2 ^ k) (nextNegAcc I k T t g flow negAcc e) : ℕ) : ℤ) =
            nextGhostFlow I T t g flow e * (2 : ℤ) ^ (T - (t + 1)) := fun e =>
      nextAcc_diff_eq ht (by rw [(hacc_len e).1]; exact hfit_all e)
        (by rw [(hacc_len e).2]; exact hfit_all e) (hacc_diff e)
    have hval' : ∀ e : Fin I.m,
        Nat.ofDigits (2 ^ k) (nextPosAcc I k T t g flow posAcc e) ≤
          (I.m + 1) * (2 ^ T - 2 ^ (T - (t + 1))) ∧
        Nat.ofDigits (2 ^ k) (nextNegAcc I k T t g flow negAcc e) ≤
          (I.m + 1) * (2 ^ T - 2 ^ (T - (t + 1))) := by
      intro e
      have ⟨hdf_bd, hdr_bd⟩ := erasedDelta_bounds hg.1 hsol e
      exact ⟨nextAcc_val_le ht (by rw [(hacc_len e).1]; exact hfit_all e)
          (le_trans hdf_bd (Nat.min_le_right _ _)) (hacc_val e).1,
        nextAcc_val_le ht (by rw [(hacc_len e).2]; exact hfit_all e)
          (le_trans hdr_bd (Nat.min_le_right _ _)) (hacc_val e).2⟩
    sep_run

/-- Concrete-cost corollary when `edge`, `nzl`, and `clmp` are `phaseUpdateEdge`, `nzLoad`, and
`clamp`. -/
theorem phaseUpdate_meets_direct {w : ℕ} {p : Program} {f edge lb acc nzl clmp Tlb Tacc : ℕ}
    (hp : p.procs[f]? = some (phaseUpdate edge))
    (hedge : p.procs[edge]? = some (phaseUpdateEdge lb acc nzl clmp))
    (hlb : Meets w p lb ((limbBitSpec w).withCost fun _ _ => Tlb))
    (hacc : Meets w p acc ((accAddSpec w).withCost fun _ _ => Tacc))
    (hnzl : p.procs[nzl]? = some nzLoad)
    (hclmp : p.procs[clmp]? = some clamp) :
    Meets w p f ((phaseUpdateSpec w).withCost fun d _ => (Tlb + 2 * Tacc + 260) * d.I.m + 120) :=
  phaseUpdate_meets (w := w) (Tedge := Tlb + 2 * Tacc + 200) hp
    (phaseUpdateEdge_meets (w := w) (Tlb := Tlb) (Tacc := Tacc) (Tnzl := 25) (Tclmp := 20)
      hedge hlb hacc (nzLoad_meets hnzl) (clamp_meets hclmp))

/-- `phaseUpdate` runs in `O(m + 1)` steps when `lb` is `O(1)` and `acc` is `O(1)`. -/
theorem phaseUpdate_meetsO {w : ℕ} {p : Program} {f edge lb acc nzl clmp : ℕ}
    (hp : p.procs[f]? = some (phaseUpdate edge))
    (hedge : p.procs[edge]? = some (phaseUpdateEdge lb acc nzl clmp))
    (hlb : MeetsO w p lb (limbBitSpec w) fun _ _ => 1)
    (hacc : MeetsO w p acc (accAddSpec w) fun _ _ => 1)
    (hnzl : p.procs[nzl]? = some nzLoad)
    (hclmp : p.procs[clmp]? = some clamp) :
    MeetsO w p f (phaseUpdateSpec w) fun d _ => d.I.m + 1 := by
  obtain ⟨Klb, hKlb⟩ := hlb
  obtain ⟨Kacc, hKacc⟩ := hacc
  have hKlb' : Meets w p lb ((limbBitSpec w).withCost fun _ _ => Klb) := by
    simpa only [Nat.mul_one] using hKlb
  have hKacc' : Meets w p acc ((accAddSpec w).withCost fun _ _ => Kacc) := by
    simpa only [Nat.mul_one] using hKacc
  refine MeetsO.of_meets (phaseUpdate_meets_direct hp hedge hKlb' hKacc' hnzl hclmp)
    ⟨Klb + 2 * Kacc + 260, fun _ => by dsimp only; nlinarith⟩

/-! ### Module -/

/-- Module for `phaseUpdate` together with its helpers `nzLoad`, `clamp`, and `phaseUpdateEdge`,
polymorphic over the procedure-name type `ι`. -/
def phaseUpdateMod {ι : Type} (name edgeName lbName accName nzlName clmpName : ι) : Module ι :=
  ⟨[(nzlName, fun _ => nzLoad),
    (clmpName, fun _ => clamp),
    (edgeName, fun idx => phaseUpdateEdge (idx lbName) (idx accName) (idx nzlName) (idx clmpName)),
    (name, fun idx => phaseUpdate (idx edgeName))]⟩

theorem phaseUpdateMod_noRand {ι : Type} (name edgeName lbName accName nzlName clmpName : ι) :
    (phaseUpdateMod name edgeName lbName accName nzlName clmpName).NoRand := by
  wram_no_rand

/-- In any program placing `phaseUpdateMod` alongside `O(1)` `limbBit` and `accAdd`,
`phaseUpdate` runs in `O(m + 1)` steps. -/
theorem phaseUpdateMod_meets {ι : Type} {w : ℕ} {p : Program} {idx : ι → ℕ}
    {name edgeName lbName accName nzlName clmpName : ι}
    (hp : (phaseUpdateMod name edgeName lbName accName nzlName clmpName).Placed p idx)
    (hlb : MeetsO w p (idx lbName) (limbBitSpec w) fun _ _ => 1)
    (hacc : MeetsO w p (idx accName) (accAddSpec w) fun _ _ => 1) :
    MeetsO w p (idx name) (phaseUpdateSpec w) (fun d _ => d.I.m + 1) :=
  phaseUpdate_meetsO
    (hp.get (n := name) (b := fun idx => phaseUpdate (idx edgeName))
      (by simp [phaseUpdateMod]))
    (hp.get (n := edgeName) (b := fun idx =>
      phaseUpdateEdge (idx lbName) (idx accName) (idx nzlName) (idx clmpName))
      (by simp [phaseUpdateMod]))
    hlb hacc
    (hp.get (n := nzlName) (b := fun _ => nzLoad) (by simp [phaseUpdateMod]))
    (hp.get (n := clmpName) (b := fun _ => clamp) (by simp [phaseUpdateMod]))

end MinCostFlow.NarrowProg
