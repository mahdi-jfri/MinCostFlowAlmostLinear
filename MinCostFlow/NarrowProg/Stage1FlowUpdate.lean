module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Limbs
public import WordRAM.Std.Array
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1StartHelpers
public import MinCostFlow.NarrowProg.Stage1CostBit
import WordRAM.Std.LimbsBits
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Stage 1 round update: flow augmentation and `(frozen, halfCost)` update (Part 4b)

This file implements the end-of-round state update of Stage 1:
- `stage1CopyPad`: copies an `L`-limb unsigned number into a `K_cap`-limb scratch buffer and
  zero-pads the remaining `K_cap - L` limbs (`O(K_cap + 1)`).
- `stage1FlowUpdate`: augments each edge's `K_cap`-limb flow `flow[e]` by
  `delta_fwd[e] - delta_rev[e]` using `stage1CopyPad`, `limbsAdd` (carry `0`), and `limbsSub`
  (borrow `0`), computing `intAugment m flow delta` (`O(m * (K_cap + 1) + 1)`).
- `stage1StateUpdate`: reads one cost bit per active edge via `stage1CostBit` and updates
  `(pFrozen, pHSign, pHMag)` using an overflow-free unsigned `(pos, neg)` split matching
  `stepHalfCost` (`O(m + 1)`).
- `stage1UpdateMod`: polymorphic `Module ι` bundling all update procedures.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Scaling.Machine
  MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate

private def updMix (a b : List ℕ) (e : ℕ) : List ℕ := a.take e ++ b.drop e

private theorem updMix_zero (a b : List ℕ) : updMix a b 0 = b := by simp [updMix]

private theorem updMix_full {a b : List ℕ} {m : ℕ} (ha : a.length = m) (hb : b.length = m) :
    updMix a b m = a := by
  simp [updMix, List.take_of_length_le (by omega : a.length ≤ m),
    List.drop_of_length_le (by omega : b.length ≤ m)]

private theorem updMix_len {a b : List ℕ} {e m : ℕ} (ha : a.length = m) (hb : b.length = m)
    (he : e ≤ m) : (updMix a b e).length = m := by
  simp [updMix, ha, hb]; omega

private theorem updMix_set {a b : List ℕ} {e m v : ℕ} (ha : a.length = m) (hb : b.length = m)
    (he : e < m) (hv : a[e]'(by omega) = v) :
    (updMix a b e).set e v = updMix a b (e + 1) := by
  unfold updMix
  exact set_take_append_drop (by omega) (by omega) hv

/-! ### 1. Copy and zero-pad an `L`-limb integer into a `K_cap`-limb buffer (`stage1CopyPad`) -/

/-- Copy `L` limbs from `src` to `dst` and zero-fill `dst[L .. K_cap)`. -/
wram_def stage1CopyPad (copyIdx : ℕ) (src, L, dst, K_cap) {
  r := copyIdx(src, dst, L)
  rem := K_cap - L
  p := dst + L
  for i in 0 .. rem {
    mem[p + i] := 0
  }
  return 0
}

def stage1CopyPadSpec (w : ℕ) : Spec (ℕ × List ℕ × List ℕ) where
  pre := fun (K_cap, xs, old) args => ⨆ (src : ℕ) (dst : ℕ),
    ⌜args = [src, xs.length, dst, K_cap] ∧ xs.length ≤ K_cap ∧ old.length = K_cap ∧
      dst + K_cap < 2 ^ w ∧ 1 < 2 ^ w⌝ *
    Assn.list src xs * Assn.list dst old
  post := fun (K_cap, xs, _) args v => ⨆ (src : ℕ) (dst : ℕ),
    ⌜args = [src, xs.length, dst, K_cap] ∧ v = 0⌝ *
    Assn.list src xs * Assn.list dst (padLimbs K_cap xs)

theorem stage1CopyPad_meets {w : ℕ} {p : Program} {f copyIdx : ℕ}
    (hp : p.procs[f]? = some (stage1CopyPad copyIdx))
    (hcopy : Meets w p copyIdx ((copySpec w).withCost fun x _ => 17 * x.1.length + 10)) :
    Meets w p f ((stage1CopyPadSpec w).withCost fun x _ => 40 * x.1 + 40) := by
  sep_enter ⟨K_cap, xs, old⟩ with hle hold hdst hw
  obtain ⟨old1, old2, h1, h2, hEq⟩ :
      ∃ a b, a.length = xs.length ∧ b.length = K_cap - xs.length ∧ old = a ++ b :=
    ⟨old.take xs.length, old.drop xs.length, by simp [hold]; omega, by simp [hold],
      (List.take_append_drop xs.length old).symm⟩
  have hsplit : Assn.list dst old = Assn.list dst old1 * Assn.list (dst + xs.length) old2 := by
    rw [hEq, Assn.list_append, h1]
  sep_apply hsplit
  sep_step from (xs, old1)
  sep_step; sep_step
  subst hrem
  have hzero_len : (List.replicate (K_cap - xs.length) 0).length = K_cap - xs.length :=
    List.length_replicate
  have hzero_init : Assn.list (dst + xs.length) old2 =
      Assn.list (dst + xs.length) (updMix (List.replicate (K_cap - xs.length) 0) old2 0) := by
    rw [updMix_zero]
  sep_apply hzero_init
  sep_for (fun i =>
    ⟨[src, xs.length, dst, K_cap, 0, K_cap - xs.length, dst + xs.length, i],
      i ≤ K_cap - xs.length, 20 * (K_cap - xs.length - i) + 5,
      [Assn.list src xs, Assn.list dst xs,
       Assn.list (dst + xs.length) (updMix (List.replicate (K_cap - xs.length) 0) old2 i)]⟩)
  · have hlen := updMix_len hzero_len h2 (Nat.le_of_lt hhi)
    sep_run
    exact updMix_set hzero_len h2 hhi (List.getElem_replicate ..)
  · rw [updMix_full hzero_len h2]
    have hmerge : Assn.list dst xs * Assn.list (dst + xs.length) (List.replicate (K_cap - xs.length) 0) =
        Assn.list dst (padLimbs K_cap xs) := by
      rw [← Assn.list_append]; rfl
    sep_apply hmerge
    sep_run

theorem stage1CopyPad_meetsO {w : ℕ} {p : Program} {f copyIdx : ℕ}
    (hp : p.procs[f]? = some (stage1CopyPad copyIdx))
    (hcopy : Meets w p copyIdx ((copySpec w).withCost fun x _ => 17 * x.1.length + 10)) :
    MeetsO w p f (stage1CopyPadSpec w) fun x _ => x.1 + 1 :=
  MeetsO.of_meets (stage1CopyPad_meets hp hcopy) ⟨40, fun _ => by dsimp only; omega⟩

/-! ### 2. Long-number flow augmentation (`stage1FlowUpdate`) -/

/-- Update all `m` edge flows in place: `flow[e] ← flow[e] + delta_fwd[e] - delta_rev[e]`. -/
wram_def stage1FlowUpdate (copyPadIdx addIdx subIdx : ℕ)
    (m, k, K_cap, L_round, pFlow, pDelta, pTmp1, pTmp2) {
  pf := pFlow
  dfwd := pDelta
  drev := pDelta + m * L_round
  for e in 0 .. m {
    r := copyPadIdx(dfwd, L_round, pTmp1, K_cap)
    r := addIdx(pf, pTmp1, pTmp2, K_cap, k)
    r := copyPadIdx(drev, L_round, pTmp1, K_cap)
    r := subIdx(pTmp2, pTmp1, pf, K_cap, k)
    pf := pf + K_cap
    dfwd := dfwd + L_round
    drev := drev + L_round
  }
  return 0
}

/-- Ghost input bundle for `stage1FlowUpdateSpec`. -/
structure Stage1FlowUpdIn where
  m : ℕ
  k : ℕ
  K_cap : ℕ
  L_round : ℕ
  flow : Fin m → ℤ
  flowLimbs : Fin m → List ℕ
  delta : Fin (m + m) → ℤ
  deltaLimbs : Fin (m + m) → List ℕ
  tmp1 : List ℕ
  tmp2 : List ℕ

/-- One-edge updated `K_cap`-limb flow list. -/
def updFlowLimb (k K_cap : ℕ) (fL dfL drL : List ℕ) : List ℕ :=
  subLimbs k (addLimbs k fL (padLimbs K_cap dfL)) (padLimbs K_cap drL)

private theorem padLimbs_len' {K_cap : ℕ} {xs : List ℕ} (hle : xs.length ≤ K_cap) :
    (padLimbs K_cap xs).length = K_cap := by
  unfold padLimbs; simp; omega

private theorem updFlowLimb_spec {k K_cap : ℕ} (hk : 1 ≤ k)
    {fL dfL drL : List ℕ} {f df dr : ℕ}
    (hfL : Limbs k fL) (hdfL : Limbs k dfL) (hdrL : Limbs k drL)
    (hflen : fL.length = K_cap) (hdflen : dfL.length ≤ K_cap) (hdrlen : drL.length ≤ K_cap)
    (hfv : Nat.ofDigits (2 ^ k) fL = f)
    (hdfv : Nat.ofDigits (2 ^ k) dfL = df)
    (hdrv : Nat.ofDigits (2 ^ k) drL = dr)
    (hsum_lt : f + df < (2 ^ k) ^ K_cap) (hsub_le : dr ≤ f + df) :
    Limbs k (updFlowLimb k K_cap fL dfL drL) ∧
      (updFlowLimb k K_cap fL dfL drL).length = K_cap ∧
      Nat.ofDigits (2 ^ k) (updFlowLimb k K_cap fL dfL drL) = f + df - dr := by
  have hpdfL : Limbs k (padLimbs K_cap dfL) := padLimbs_limbs hdfL
  have hpdrL : Limbs k (padLimbs K_cap drL) := padLimbs_limbs hdrL
  have hpdflen : (padLimbs K_cap dfL).length = K_cap := padLimbs_len' hdflen
  have hpdrlen : (padLimbs K_cap drL).length = K_cap := padLimbs_len' hdrlen
  have hpdfv : Nat.ofDigits (2 ^ k) (padLimbs K_cap dfL) = df := by
    unfold padLimbs; rw [ofDigits_append_replicate_zero, hdfv]
  have hpdrv : Nat.ofDigits (2 ^ k) (padLimbs K_cap drL) = dr := by
    unfold padLimbs; rw [ofDigits_append_replicate_zero, hdrv]
  obtain ⟨hadd_eq, hcarry_le, hadd_L⟩ := addRun_spec hk hfL hpdfL (by omega) fL.length le_rfl
  rw [List.take_length, List.take_of_length_le (by omega), hfv, hpdfv] at hadd_eq
  have hcarry0 : (carryRun (addStep k fL (padLimbs K_cap dfL)) fL.length).2 = 0 := by
    by_contra hne
    have hge1 : 1 ≤ (carryRun (addStep k fL (padLimbs K_cap dfL)) fL.length).2 := by omega
    have hpow : (2 ^ k) ^ fL.length = (2 ^ k) ^ K_cap := by rw [hflen]
    have hmul : (2 ^ k) ^ fL.length ≤
        (carryRun (addStep k fL (padLimbs K_cap dfL)) fL.length).2 * (2 ^ k) ^ fL.length := by
      simpa using Nat.mul_le_mul_right ((2 ^ k) ^ fL.length) hge1
    omega
  have hadd_val : Nat.ofDigits (2 ^ k) (addLimbs k fL (padLimbs K_cap dfL)) = f + df := by
    unfold addLimbs
    rw [hcarry0, Nat.zero_mul, Nat.add_zero] at hadd_eq
    exact hadd_eq
  have hadd_len : (addLimbs k fL (padLimbs K_cap dfL)).length = K_cap := by
    unfold addLimbs; rw [length_carryRun, hflen]
  set sL := addLimbs k fL (padLimbs K_cap dfL) with hsL_def
  have hsL_L : Limbs k sL := hadd_L
  obtain ⟨hsub_eq, hbor_le, hsub_L⟩ := subRun_spec hk hsL_L hpdrL (by omega) sL.length le_rfl
  rw [List.take_length, List.take_of_length_le (by omega), hadd_val, hpdrv] at hsub_eq
  have hbor0 : (carryRun (subStep k sL (padLimbs K_cap drL)) sL.length).2 = 0 := by
    by_contra hne
    have hge1 : 1 ≤ (carryRun (subStep k sL (padLimbs K_cap drL)) sL.length).2 := by omega
    have hlt : Nat.ofDigits (2 ^ k) (carryRun (subStep k sL (padLimbs K_cap drL)) sL.length).1 <
        (2 ^ k) ^ K_cap := by
      have h1 := ofDigits_lt_pow hsub_L
      rw [length_carryRun, hadd_len, pow_mul] at h1
      rwa [hadd_len]
    have hpow : (2 ^ k) ^ sL.length = (2 ^ k) ^ K_cap := by rw [hadd_len]
    have hmul : (2 ^ k) ^ sL.length ≤
        (carryRun (subStep k sL (padLimbs K_cap drL)) sL.length).2 * (2 ^ k) ^ sL.length := by
      simpa using Nat.mul_le_mul_right ((2 ^ k) ^ sL.length) hge1
    omega
  refine ⟨hsub_L, ?_, ?_⟩
  · unfold updFlowLimb subLimbs; rw [← hsL_def, length_carryRun, hadd_len]
  · unfold updFlowLimb subLimbs; rw [← hsL_def]
    rw [hbor0, Nat.zero_mul, Nat.add_zero] at hsub_eq
    omega

/-- Specification of `stage1FlowUpdate`. -/
def stage1FlowUpdateSpec (w : ℕ) : Spec Stage1FlowUpdIn where
  pre := fun inp args => ⨆ (pFlow : ℕ) (pDelta : ℕ) (pTmp1 : ℕ) (pTmp2 : ℕ),
    ⌜args = [inp.m, inp.k, inp.K_cap, inp.L_round, pFlow, pDelta, pTmp1, pTmp2] ∧
      1 ≤ inp.k ∧ 2 * inp.k ≤ w ∧ inp.L_round ≤ inp.K_cap ∧
      inp.tmp1.length = inp.K_cap ∧ inp.tmp2.length = inp.K_cap ∧
      pTmp1 + inp.K_cap < 2 ^ w ∧
      pFlow + inp.m * inp.K_cap < 2 ^ w ∧
      pDelta + 2 * inp.m * inp.L_round < 2 ^ w ∧
      (∀ e : Fin inp.m, 0 ≤ inp.flow e ∧ Limbs inp.k (inp.flowLimbs e) ∧
        (inp.flowLimbs e).length = inp.K_cap ∧
        ((Nat.ofDigits (2 ^ inp.k) (inp.flowLimbs e) : ℕ) : ℤ) = inp.flow e) ∧
      (∀ a : Fin (inp.m + inp.m), 0 ≤ inp.delta a ∧ Limbs inp.k (inp.deltaLimbs a) ∧
        (inp.deltaLimbs a).length = inp.L_round ∧
        ((Nat.ofDigits (2 ^ inp.k) (inp.deltaLimbs a) : ℕ) : ℤ) = inp.delta a) ∧
      (∀ e : Fin inp.m,
        (inp.flow e).toNat + (inp.delta (Fin.castAdd inp.m e)).toNat < (2 ^ inp.k) ^ inp.K_cap ∧
        (inp.delta (Fin.natAdd inp.m e)).toNat ≤
          (inp.flow e).toNat + (inp.delta (Fin.castAdd inp.m e)).toNat)⌝ *
    (∏ e ∈ Finset.range inp.m, Assn.list (pFlow + e * inp.K_cap)
      (if h : e < inp.m then inp.flowLimbs ⟨e, h⟩ else [])) *
    (∏ a ∈ Finset.range (inp.m + inp.m), Assn.list (pDelta + a * inp.L_round)
      (if h : a < inp.m + inp.m then inp.deltaLimbs ⟨a, h⟩ else [])) *
    Assn.list pTmp1 inp.tmp1 *
    Assn.list pTmp2 inp.tmp2
  post := fun inp args v => ⨆ (pFlow : ℕ) (pDelta : ℕ) (pTmp1 : ℕ) (pTmp2 : ℕ)
      (tmp1' : List ℕ) (tmp2' : List ℕ),
    let newLimbs : Fin inp.m → List ℕ := fun e =>
      updFlowLimb inp.k inp.K_cap (inp.flowLimbs e)
        (inp.deltaLimbs (Fin.castAdd inp.m e)) (inp.deltaLimbs (Fin.natAdd inp.m e))
    ⌜args = [inp.m, inp.k, inp.K_cap, inp.L_round, pFlow, pDelta, pTmp1, pTmp2] ∧ v = 0 ∧
      tmp1'.length = inp.K_cap ∧ tmp2'.length = inp.K_cap ∧
      (∀ e : Fin inp.m, Limbs inp.k (newLimbs e) ∧ (newLimbs e).length = inp.K_cap ∧
        ((Nat.ofDigits (2 ^ inp.k) (newLimbs e) : ℕ) : ℤ) =
          intAugment inp.m inp.flow inp.delta e)⌝ *
    (∏ e ∈ Finset.range inp.m, Assn.list (pFlow + e * inp.K_cap)
      (if h : e < inp.m then newLimbs ⟨e, h⟩ else [])) *
    (∏ a ∈ Finset.range (inp.m + inp.m), Assn.list (pDelta + a * inp.L_round)
      (if h : a < inp.m + inp.m then inp.deltaLimbs ⟨a, h⟩ else [])) *
    Assn.list pTmp1 tmp1' *
    Assn.list pTmp2 tmp2'

theorem stage1FlowUpdate_meets {w : ℕ} {p : Program} {f copyPadIdx addIdx subIdx : ℕ}
    (hp : p.procs[f]? = some (stage1FlowUpdate copyPadIdx addIdx subIdx))
    (hcp : Meets w p copyPadIdx ((stage1CopyPadSpec w).withCost fun x _ => 40 * x.1 + 40))
    (hadd : Meets w p addIdx ((limbsAddSpec w).withCost fun x _ => 50 * x.2.1.length + 30))
    (hsub : Meets w p subIdx ((limbsSubSpec w).withCost fun x _ => 60 * x.2.1.length + 30)) :
    Meets w p f ((stage1FlowUpdateSpec w).withCost fun inp _ =>
      (190 * inp.K_cap + 225) * inp.m + 50) := by
  sep_enter inp with hk h2k hLle htmp1 htmp2 hpT1_fit hpF_fit hpD_fit hflowSpec hdeltaSpec hbounds
  obtain ⟨m, k, K_cap, L_round, flow, flowLimbs, delta, deltaLimbs, tmp1, tmp2⟩ := inp
  dsimp only at hk h2k hLle htmp1 htmp2 hpT1_fit hpF_fit hpD_fit hflowSpec hdeltaSpec hbounds ⊢
  set newLimbs : Fin m → List ℕ := fun e =>
    updFlowLimb k K_cap (flowLimbs e)
      (deltaLimbs (Fin.castAdd m e)) (deltaLimbs (Fin.natAdd m e)) with hnew_def
  have h1w : 1 < 2 ^ w := by
    have h2 : 2 ≤ 2 ^ k := two_le_pow hk
    have h2w : 2 ^ k + 2 ^ k ≤ 2 ^ w := pow_lt_pow_w hk h2k
    omega
  have hmL_lt : pDelta + m * L_round < 2 ^ w := by
    have : 2 * m * L_round = 2 * (m * L_round) := Nat.mul_assoc 2 m L_round
    omega
  have h2mL : 2 * m * L_round = 2 * (m * L_round) := Nat.mul_assoc 2 m L_round
  sep_step; sep_step; sep_step
  sep_for (fun e (t : List ℕ × List ℕ × ℕ) =>
    ⟨[m, k, K_cap, L_round, pFlow, pDelta, pTmp1, pTmp2,
      pFlow + e * K_cap, pDelta + e * L_round, pDelta + (m + e) * L_round, e, t.2.2],
      e ≤ m ∧ t.1.length = K_cap ∧ t.2.1.length = K_cap,
      (190 * K_cap + 205) * (m - e) + 5,
      [∏ j ∈ Finset.range m, Assn.list (pFlow + j * K_cap)
          (if h : j < m then (if j < e then newLimbs ⟨j, h⟩ else flowLimbs ⟨j, h⟩) else []),
       ∏ a ∈ Finset.range (m + m), Assn.list (pDelta + a * L_round)
          (if h : a < m + m then deltaLimbs ⟨a, h⟩ else []),
       Assn.list pTmp1 t.1, Assn.list pTmp2 t.2.1]⟩)
    with ⟨t1, t2, r⟩
  · have hmemF : e ∈ Finset.range m := Finset.mem_range.mpr hhi
    have hmemD1 : e ∈ Finset.range (m + m) := Finset.mem_range.mpr (by omega)
    have hmemD2 : m + e ∈ (Finset.range (m + m)).erase e :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
    have hf_e := hflowSpec ⟨e, hhi⟩
    have hdf_e := hdeltaSpec (Fin.castAdd m ⟨e, hhi⟩)
    have hdr_e := hdeltaSpec (Fin.natAdd m ⟨e, hhi⟩)
    have hb_e := hbounds ⟨e, hhi⟩
    have hpf_next : pFlow + e * K_cap + K_cap = pFlow + (e + 1) * K_cap := by
      rw [Nat.succ_mul]; omega
    have hpf_lt : pFlow + (e + 1) * K_cap < 2 ^ w := by
      have : (e + 1) * K_cap ≤ m * K_cap := Nat.mul_le_mul_right K_cap (by omega); omega
    have hdf_next : pDelta + e * L_round + L_round = pDelta + (e + 1) * L_round := by
      rw [Nat.succ_mul]; omega
    have hdr_next : pDelta + (m + e) * L_round + L_round = pDelta + (m + (e + 1)) * L_round := by
      rw [show m + (e + 1) = (m + e) + 1 by omega, Nat.succ_mul]; omega
    have hdr_lt : pDelta + (m + (e + 1)) * L_round < 2 ^ w := by
      have hle1 : (m + (e + 1)) * L_round ≤ (2 * m) * L_round :=
        Nat.mul_le_mul_right L_round (by omega)
      omega
    have hdf_lt : pDelta + (e + 1) * L_round < 2 ^ w := by
      have hle1 : (e + 1) * L_round ≤ (m + (e + 1)) * L_round :=
        Nat.mul_le_mul_right L_round (by omega)
      omega
    -- Pull edge `e` out of `pFlow`, and `e` & `m + e` out of `pDelta`
    sep_apply Assn.prod_eq_mul_erase hmemF
      (fun j => Assn.list (pFlow + j * K_cap)
        (if h : j < m then (if j < e then newLimbs ⟨j, h⟩ else flowLimbs ⟨j, h⟩) else []))
    have hflow_at : (if h : e < m then (if e < e then newLimbs ⟨e, h⟩ else flowLimbs ⟨e, h⟩) else []) =
        flowLimbs ⟨e, hhi⟩ := by simp [hhi]
    rw [hflow_at]
    sep_apply Assn.prod_eq_mul_erase hmemD1
      (fun a => Assn.list (pDelta + a * L_round)
        (if h : a < m + m then deltaLimbs ⟨a, h⟩ else []))
    have hdf_at : (if h : e < m + m then deltaLimbs ⟨e, h⟩ else []) =
        deltaLimbs (Fin.castAdd m ⟨e, hhi⟩) := by
      simp only [show e < m + m by omega, ↓reduceDIte]; rfl
    rw [hdf_at]
    sep_apply Assn.prod_eq_mul_erase hmemD2
      (fun a => Assn.list (pDelta + a * L_round)
        (if h : a < m + m then deltaLimbs ⟨a, h⟩ else []))
    have hdr_at : (if h : m + e < m + m then deltaLimbs ⟨m + e, h⟩ else []) =
        deltaLimbs (Fin.natAdd m ⟨e, hhi⟩) := by
      simp only [show m + e < m + m by omega, ↓reduceDIte]; rfl
    rw [hdr_at]
    -- Call 1: copyPad delta_fwd -> pTmp1
    sep_step from (K_cap, deltaLimbs (Fin.castAdd m ⟨e, hhi⟩), t1)
    have hpdf_len : (padLimbs K_cap (deltaLimbs (Fin.castAdd m ⟨e, hhi⟩))).length = K_cap :=
      padLimbs_len' (by omega)
    have hpdf_L : Limbs k (padLimbs K_cap (deltaLimbs (Fin.castAdd m ⟨e, hhi⟩))) :=
      padLimbs_limbs hdf_e.2.1
    -- Call 2: limbsAdd(pf, pTmp1, pTmp2)
    have hfl_L : Limbs k (flowLimbs ⟨e, hhi⟩) := hf_e.2.1
    sep_step from (k, flowLimbs ⟨e, hhi⟩, padLimbs K_cap (deltaLimbs (Fin.castAdd m ⟨e, hhi⟩)), t2)
    have hadd_len : (addLimbs k (flowLimbs ⟨e, hhi⟩)
        (padLimbs K_cap (deltaLimbs (Fin.castAdd m ⟨e, hhi⟩)))).length = K_cap := by
      unfold addLimbs; rw [length_carryRun, hf_e.2.2.1]
    -- Call 3: copyPad delta_rev -> pTmp1
    sep_step from (K_cap, deltaLimbs (Fin.natAdd m ⟨e, hhi⟩),
      padLimbs K_cap (deltaLimbs (Fin.castAdd m ⟨e, hhi⟩)))
    have hpdr_len : (padLimbs K_cap (deltaLimbs (Fin.natAdd m ⟨e, hhi⟩))).length = K_cap :=
      padLimbs_len' (by omega)
    have hpdr_L : Limbs k (padLimbs K_cap (deltaLimbs (Fin.natAdd m ⟨e, hhi⟩))) :=
      padLimbs_limbs hdr_e.2.1
    -- Call 4: limbsSub(pTmp2, pTmp1, pf)
    sep_step from (k, addLimbs k (flowLimbs ⟨e, hhi⟩)
        (padLimbs K_cap (deltaLimbs (Fin.castAdd m ⟨e, hhi⟩))),
      padLimbs K_cap (deltaLimbs (Fin.natAdd m ⟨e, hhi⟩)), flowLimbs ⟨e, hhi⟩)
    -- Put atoms back into products
    have hsub_eq : subLimbs k (addLimbs k (flowLimbs ⟨e, hhi⟩)
        (padLimbs K_cap (deltaLimbs (Fin.castAdd m ⟨e, hhi⟩))))
        (padLimbs K_cap (deltaLimbs (Fin.natAdd m ⟨e, hhi⟩))) = newLimbs ⟨e, hhi⟩ := rfl
    rw [hsub_eq]
    have hprodF_upd :
        Assn.list (pFlow + e * K_cap) (newLimbs ⟨e, hhi⟩) *
        (∏ j ∈ (Finset.range m).erase e, Assn.list (pFlow + j * K_cap)
          (if h : j < m then (if j < e then newLimbs ⟨j, h⟩ else flowLimbs ⟨j, h⟩) else [])) =
        ∏ j ∈ Finset.range m, Assn.list (pFlow + j * K_cap)
          (if h : j < m then (if j < e + 1 then newLimbs ⟨j, h⟩ else flowLimbs ⟨j, h⟩) else []) := by
      rw [Assn.prod_eq_mul_erase hmemF]
      simp only [hhi, ↓reduceDIte, Nat.lt_succ_self, ↓reduceIte]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      have hne : j ≠ e := (Finset.mem_erase.mp hj).1
      have hiff : (j < e) ↔ (j < e + 1) := by omega
      simp only [hiff]
    sep_apply hprodF_upd
    rw [← hdr_at]
    sep_apply (Assn.prod_eq_mul_erase hmemD2
      (fun a => Assn.list (pDelta + a * L_round)
        (if h : a < m + m then deltaLimbs ⟨a, h⟩ else []))).symm
    rw [← hdf_at]
    sep_apply (Assn.prod_eq_mul_erase hmemD1
      (fun a => Assn.list (pDelta + a * L_round)
        (if h : a < m + m then deltaLimbs ⟨a, h⟩ else []))).symm
    have hmul_sub_z : (190 * (K_cap : ℤ) + 205) * ((m : ℤ) - (e : ℤ)) =
        (190 * (K_cap : ℤ) + 205) + (190 * (K_cap : ℤ) + 205) * ((m : ℤ) - ((e + 1 : ℕ) : ℤ)) := by
      push_cast; ring
    sep_run
    · rw [hdf_at, hadd_len, hf_e.2.2.1]; omega
    · rw [hdr_at]; exact hpdr_len
    · rw [hdf_at]; exact hadd_len
  · have hprodF_end :
        (∏ j ∈ Finset.range m, Assn.list (pFlow + j * K_cap)
          (if h : j < m then (if j < m then newLimbs ⟨j, h⟩ else flowLimbs ⟨j, h⟩) else [])) =
        ∏ j ∈ Finset.range m, Assn.list (pFlow + j * K_cap)
          (if h : j < m then newLimbs ⟨j, h⟩ else []) :=
      Finset.prod_congr rfl fun j hj => by
        have hlt := Finset.mem_range.mp hj
        simp [hlt]
    rw [hprodF_end]
    have hnew_spec : ∀ e : Fin m, Limbs k (newLimbs e) ∧ (newLimbs e).length = K_cap ∧
        ((Nat.ofDigits (2 ^ k) (newLimbs e) : ℕ) : ℤ) = intAugment m flow delta e := by
      intro e
      obtain ⟨hf0, hfL, hflen, hfv⟩ := hflowSpec e
      obtain ⟨hdf0, hdfL, hdflen, hdfv⟩ := hdeltaSpec (Fin.castAdd m e)
      obtain ⟨hdr0, hdrL, hdrlen, hdrv⟩ := hdeltaSpec (Fin.natAdd m e)
      obtain ⟨hsum, hsub⟩ := hbounds e
      have hfv' : Nat.ofDigits (2 ^ k) (flowLimbs e) = (flow e).toNat := by omega
      have hdfv' : Nat.ofDigits (2 ^ k) (deltaLimbs (Fin.castAdd m e)) =
          (delta (Fin.castAdd m e)).toNat := by omega
      have hdrv' : Nat.ofDigits (2 ^ k) (deltaLimbs (Fin.natAdd m e)) =
          (delta (Fin.natAdd m e)).toNat := by omega
      obtain ⟨hL', hlen', hval'⟩ := updFlowLimb_spec hk hfL hdfL hdrL hflen (by omega) (by omega)
        hfv' hdfv' hdrv' hsum hsub
      refine ⟨hL', hlen', ?_⟩
      change ((Nat.ofDigits (2 ^ k) (updFlowLimb k K_cap (flowLimbs e)
        (deltaLimbs (Fin.castAdd m e)) (deltaLimbs (Fin.natAdd m e))) : ℕ) : ℤ) = _
      rw [hval']; unfold intAugment intProject; omega
    sep_run

theorem stage1FlowUpdate_meetsO {w : ℕ} {p : Program} {f copyPadIdx addIdx subIdx : ℕ}
    (hp : p.procs[f]? = some (stage1FlowUpdate copyPadIdx addIdx subIdx))
    (hcp : Meets w p copyPadIdx ((stage1CopyPadSpec w).withCost fun x _ => 40 * x.1 + 40))
    (hadd : Meets w p addIdx ((limbsAddSpec w).withCost fun x _ => 50 * x.2.1.length + 30))
    (hsub : Meets w p subIdx ((limbsSubSpec w).withCost fun x _ => 60 * x.2.1.length + 30)) :
    MeetsO w p f (stage1FlowUpdateSpec w) fun inp _ => inp.m * (inp.K_cap + 1) + 1 :=
  MeetsO.of_meets (stage1FlowUpdate_meets hp hcp hadd hsub) ⟨225, fun inp => by
    dsimp only; rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm inp.1.K_cap inp.1.m]
    simp only [Nat.mul_add, Nat.mul_one]; omega⟩


/-- Polymorphic module for `stage1CopyPad` and `stage1FlowUpdate`. -/
def stage1FlowUpdateMod {ι : Type} (copyPadName flowUpdName copyName addName subName : ι) : Module ι :=
  ⟨[(copyPadName, fun idx => stage1CopyPad (idx copyName)),
    (flowUpdName, fun idx => stage1FlowUpdate (idx copyPadName) (idx addName) (idx subName))]⟩

theorem stage1FlowUpdateMod_noRand {ι : Type} (copyPadName flowUpdName copyName addName subName : ι) :
    (stage1FlowUpdateMod copyPadName flowUpdName copyName addName subName).NoRand := by
  wram_no_rand

end MinCostFlow.NarrowProg.Stage1
