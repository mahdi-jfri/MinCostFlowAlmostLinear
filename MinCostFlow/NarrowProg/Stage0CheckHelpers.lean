module

public import WordRAM.Module
public import WordRAM.Std.Limbs
public import MinCostFlow.NarrowProg.Stage0Read
public import MinCostFlow.Scaling.FlowReduction
public import MinCostFlow.Scaling.VertexCompression
import WordRAM.Sep.Tactic
import WordRAM.Syntax
import Mathlib.Tactic.Ring

/-!
# Stage 0, item 2 helpers: signed comparison, capacity check, and endpoint labeling

Implements and verifies:
- `signedLimbsLe`: compares two canonical signed base-`2 ^ k` integers using `WordRAM.Std.limbsCmp`
  when their limb lengths agree;
- `stage0CheckCaps`: scans all `m` edges to check `lower ≤ upper` (returning `0` on failure, which
  certifies infeasibility via `FlowReduction.infeasible_of_upper_lt_lower`);
- `stage0ScanEnd` and `stage0Labels`: scan tails and heads in the exact order of
  `Circulation.endpoints` to populate `pLabel` (`(shiftedGraph I hv).endpointLabels.table`) and
  `pActive` (the inverse list of active vertex IDs of length `cnt ≤ 2 * m`).
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling

namespace MinCostFlow.NarrowProg

/-! ### Canonical limb comparison lemmas -/

theorem ofDigits_ge_pow_pred {k : ℕ} (hk : 1 ≤ k) {xs : List ℕ} (hcan : CanonicalLimbs k xs)
    (hne : xs ≠ []) : (2 ^ k) ^ (xs.length - 1) ≤ Nat.ofDigits (2 ^ k) xs := by
  have hb : 1 < 2 ^ k := by have := two_le_pow hk; omega
  have hlast : 1 ≤ xs.getLast hne := Nat.pos_of_ne_zero (hcan.2 hne)
  have hsplit : xs = xs.dropLast ++ [xs.getLast hne] := (List.dropLast_append_getLast hne).symm
  have hlen : xs.dropLast.length = xs.length - 1 := List.length_dropLast
  conv_rhs => rw [hsplit]
  rw [Nat.ofDigits_append]
  simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero, hlen]
  have hmul : (2 ^ k) ^ (xs.length - 1) * 1 ≤ (2 ^ k) ^ (xs.length - 1) * xs.getLast hne :=
    Nat.mul_le_mul_left _ hlast
  omega

theorem ofDigits_lt_pow_length {k : ℕ} (_hk : 1 ≤ k) {xs : List ℕ} (hL : Limbs k xs) :
    Nat.ofDigits (2 ^ k) xs < (2 ^ k) ^ xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha : a < 2 ^ k := hL a List.mem_cons_self
    have hxs : Limbs k xs := fun x hx => hL x (List.mem_cons_of_mem a hx)
    have hih := ih hxs
    simp only [Nat.ofDigits_cons, List.length_cons, Nat.pow_succ]
    have h1 : 2 ^ k * Nat.ofDigits (2 ^ k) xs + 2 ^ k ≤ 2 ^ k * (2 ^ k) ^ xs.length := by
      have : Nat.ofDigits (2 ^ k) xs + 1 ≤ (2 ^ k) ^ xs.length := hih
      have hm := Nat.mul_le_mul_left (2 ^ k) this
      linarith
    have hcomm : (2 ^ k) ^ xs.length * 2 ^ k = 2 ^ k * (2 ^ k) ^ xs.length := Nat.mul_comm _ _
    omega

theorem canonical_lt_of_length_lt {k : ℕ} (hk : 1 ≤ k) {xs ys : List ℕ}
    (hx : CanonicalLimbs k xs) (hy : CanonicalLimbs k ys) (hlt : xs.length < ys.length) :
    Nat.ofDigits (2 ^ k) xs < Nat.ofDigits (2 ^ k) ys := by
  have hyne : ys ≠ [] := by intro h; subst h; simp at hlt
  have h1 := ofDigits_lt_pow_length hk hx.1
  have h2 := ofDigits_ge_pow_pred hk hy hyne
  have h3 : (2 ^ k) ^ xs.length ≤ (2 ^ k) ^ (ys.length - 1) :=
    Nat.pow_le_pow_right (by have := two_le_pow hk; omega) (by omega)
  omega

/-! ### `signedLimbsLe` -/

/-- Compare two canonical signed integers `(sA, lenA, pA)` and `(sB, lenB, pB)`: returns `1` iff
`a ≤ b`, and `0` otherwise. -/
wram_def signedLimbsLe (cmp : ℕ) (sA, lenA, pA, sB, lenB, pB) {
  if sA == 1 {
    if sB == 0 {
      return 1
    } else {
      if lenA < lenB {
        return 0
      } else {
        if lenB < lenA {
          return 1
        } else {
          c := cmp(pA, pB, lenA)
          if c == 0 {
            return 0
          } else {
            return 1
          }
        }
      }
    }
  } else {
    if sB == 1 {
      return 0
    } else {
      if lenA < lenB {
        return 1
      } else {
        if lenB < lenA {
          return 0
        } else {
          c := cmp(pA, pB, lenA)
          if c == 2 {
            return 0
          } else {
            return 1
          }
        }
      }
    }
  }
}

/-- Specification of `signedLimbsLe` on canonical base-`2 ^ k` signed integers `a, b : ℤ`. -/
def signedLimbsLeSpec : Spec (ℕ × ℤ × ℤ) where
  pre := fun (k, a, b) args => ⨆ (pA : ℕ) (pB : ℕ),
    let sA := if a < 0 then 1 else 0
    let sB := if b < 0 then 1 else 0
    let xs := Nat.digits (2 ^ k) a.natAbs
    let ys := Nat.digits (2 ^ k) b.natAbs
    ⌜args = [sA, xs.length, pA, sB, ys.length, pB] ∧ 1 ≤ k⌝ *
    Assn.list pA xs * Assn.list pB ys
  post := fun (k, a, b) args v => ⨆ (pA : ℕ) (pB : ℕ),
    let sA := if a < 0 then 1 else 0
    let sB := if b < 0 then 1 else 0
    let xs := Nat.digits (2 ^ k) a.natAbs
    let ys := Nat.digits (2 ^ k) b.natAbs
    ⌜args = [sA, xs.length, pA, sB, ys.length, pB] ∧ v = if a ≤ b then 1 else 0⌝ *
    Assn.list pA xs * Assn.list pB ys

/-- Limb count of the first operand `a` in `signedLimbsLeSpec` (wrapped as a named function to avoid
bound-variable powers inside `withCost` lambdas). -/
def signedCmpDigitsLen (x : ℕ × ℤ × ℤ) : ℕ :=
  (Nat.digits (2 ^ x.1) x.2.1.natAbs).length

theorem signedLimbsLe_meets {w : ℕ} {p : Program} {f cmp : ℕ} {Tcmp : ℕ → ℕ}
    (hw : 2 < 2 ^ w)
    (hp : p.procs[f]? = some (signedLimbsLe cmp))
    (hcmp : Meets w p cmp (limbsCmpSpec.withCost fun x _ => Tcmp x.2.1.length)) :
    Meets w p f (signedLimbsLeSpec.withCost fun x _ =>
      Tcmp (signedCmpDigitsLen x) + 50) := by
  sep_enter ⟨k, a, b⟩ with hk
  have hcx := digits_canonical hk a.natAbs
  have hcy := digits_canonical hk b.natAbs
  have hLx : Limbs k (Nat.digits (2 ^ k) a.natAbs) := hcx.1
  have hLy : Limbs k (Nat.digits (2 ^ k) b.natAbs) := hcy.1
  have hvalx : Nat.ofDigits (2 ^ k) (Nat.digits (2 ^ k) a.natAbs) = a.natAbs :=
    Nat.ofDigits_digits (2 ^ k) a.natAbs
  have hvaly : Nat.ofDigits (2 ^ k) (Nat.digits (2 ^ k) b.natAbs) = b.natAbs :=
    Nat.ofDigits_digits (2 ^ k) b.natAbs
  sep_step
  · have ha_neg : a < 0 := by by_contra h; simp [h] at hcond
    sep_step
    · have hb_nonneg : 0 ≤ b := by by_contra h; push Not at h; simp [h] at hcond_1
      have hle : a ≤ b := by omega
      sep_run
    · have hb_neg : b < 0 := by by_contra h; simp [h] at hcond_1
      sep_step
      · have hlt := canonical_lt_of_length_lt hk hcx hcy hcond_2
        rw [hvalx, hvaly] at hlt
        have hgt : ¬ a ≤ b := by omega
        sep_run
      · sep_step
        · have hlt := canonical_lt_of_length_lt hk hcy hcx hcond_3
          rw [hvalx, hvaly] at hlt
          have hle : a ≤ b := by omega
          sep_run
        · have hlen_eq : (Nat.digits (2 ^ k) b.natAbs).length =
              (Nat.digits (2 ^ k) a.natAbs).length := by omega
          sep_step from (k, Nat.digits (2 ^ k) a.natAbs, Nat.digits (2 ^ k) b.natAbs)
          rw [hvalx, hvaly] at hc
          sep_step
          · have hlt : a.natAbs < b.natAbs := by
              unfold cmpCode at hc; split_ifs at hc <;> omega
            have hgt : ¬ a ≤ b := by omega
            sep_run; dsimp only [signedCmpDigitsLen]; omega
          · have hge : b.natAbs ≤ a.natAbs := by
              unfold cmpCode at hc; split_ifs at hc <;> omega
            have hle : a ≤ b := by omega
            sep_run; dsimp only [signedCmpDigitsLen]; omega
  · have ha_nonneg : 0 ≤ a := by by_contra h; push Not at h; simp [h] at hcond
    sep_step
    · have hb_neg : b < 0 := by by_contra h; simp [h] at hcond_1
      have hgt : ¬ a ≤ b := by omega
      sep_run
    · have hb_nonneg : 0 ≤ b := by by_contra h; push Not at h; simp [h] at hcond_1
      sep_step
      · have hlt := canonical_lt_of_length_lt hk hcx hcy hcond_2
        rw [hvalx, hvaly] at hlt
        have hle : a ≤ b := by omega
        sep_run
      · sep_step
        · have hlt := canonical_lt_of_length_lt hk hcy hcx hcond_3
          rw [hvalx, hvaly] at hlt
          have hgt : ¬ a ≤ b := by omega
          sep_run
        · have hlen_eq : (Nat.digits (2 ^ k) b.natAbs).length =
              (Nat.digits (2 ^ k) a.natAbs).length := by omega
          sep_step from (k, Nat.digits (2 ^ k) a.natAbs, Nat.digits (2 ^ k) b.natAbs)
          rw [hvalx, hvaly] at hc
          sep_step
          · have hgt : b.natAbs < a.natAbs := by
              unfold cmpCode at hc; split_ifs at hc <;> omega
            have hnle : ¬ a ≤ b := by omega
            sep_run; dsimp only [signedCmpDigitsLen]; omega
          · have hle_nat : a.natAbs ≤ b.natAbs := by
              unfold cmpCode at hc; split_ifs at hc <;> omega
            have hle : a ≤ b := by omega
            sep_run; dsimp only [signedCmpDigitsLen]; omega

/-! ### `stage0CheckOneCap` and `stage0CheckCaps` -/

/-- Check `lower ≤ upper` for a single edge whose 11-word record sits at `pE`. -/
wram_def stage0CheckOneCap (sle : ℕ) (pE) {
  sLo := mem[pE + 2]
  lenLo := mem[pE + 3]
  pLo := mem[pE + 4]
  sHi := mem[pE + 5]
  lenHi := mem[pE + 6]
  pHi := mem[pE + 7]
  ok := sle(sLo, lenLo, pLo, sHi, lenHi, pHi)
  return ok
}

/-- Specification of `stage0CheckOneCap`. -/
def stage0CheckOneCapSpec (w : ℕ) : Spec ((I : Instance) × Fin I.m) where
  pre := fun ⟨I, e⟩ args => ⨆ (pE : ℕ),
    ⌜args = [pE] ∧ pE + 11 ≤ 2 ^ w ∧ 10 < 2 ^ w⌝ *
    Assn.list (edgeStartPos I e.val) (narrowEdgeWords (narrowLimbWidth I) (I.edge e)) *
    Assn.list pE (edgeRec I e)
  post := fun ⟨I, e⟩ args v => ⨆ (pE : ℕ),
    ⌜args = [pE] ∧ v = if (I.edge e).lower ≤ (I.edge e).upper then 1 else 0⌝ *
    Assn.list (edgeStartPos I e.val) (narrowEdgeWords (narrowLimbWidth I) (I.edge e)) *
    Assn.list pE (edgeRec I e)

/-- Limb count of the lower capacity of edge `e` (wrapped as a named function). -/
def edgeLowerDigitsLen (x : (I : Instance) × Fin I.m) : ℕ :=
  (Nat.digits (2 ^ narrowLimbWidth x.1) (x.1.edge x.2).lower.natAbs).length

theorem stage0CheckOneCap_meets {w : ℕ} {p : Program} {f sle : ℕ} {Tsle : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0CheckOneCap sle))
    (hsle : Meets w p sle (signedLimbsLeSpec.withCost fun x _ => Tsle (signedCmpDigitsLen x))) :
    Meets w p f ((stage0CheckOneCapSpec w).withCost fun x _ =>
      Tsle (edgeLowerDigitsLen x) + 60) := by
  sep_enter ⟨I, e⟩ with hpE_fit hw10
  have hk : 1 ≤ narrowLimbWidth I := one_le_narrowLimbWidth I
  have hrec_len : (edgeRec I e).length = 11 := rfl
  sep_apply list_narrowEdgeWords I e
  sep_apply list_intWords (edgeStartPos I e.val + 2) (narrowLimbWidth I) (I.edge e).lower
  sep_apply list_intWords (edgeHiPos I e) (narrowLimbWidth I) (I.edge e).upper
  have hloPtr_eq : edgeStartPos I e.val + 2 + 2 = edgeLoPtr I e := by unfold edgeLoPtr; omega
  have hhiPtr_eq : edgeHiPos I e + 2 = edgeHiPtr I e := rfl
  rw [hloPtr_eq, hhiPtr_eq]
  sep_step; sep_step; sep_step; sep_step; sep_step; sep_step
  simp only [edgeRec, List.getElem_cons_zero, List.getElem_cons_succ]
    at hsLo hlenLo hpLo hsHi hlenHi hpHi
  subst sLo lenLo pLo sHi lenHi pHi
  generalize hF1 :
    (Assn.list pE (edgeRec I e) *
     (edgeStartPos I e.val ↦ (I.edge e).tail) *
     (edgeStartPos I e.val + 1 ↦ (I.edge e).head) *
     (edgeStartPos I e.val + 2 ↦ if (I.edge e).lower < 0 then 1 else 0) *
     (edgeStartPos I e.val + 2 + 1 ↦
       (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).lower.natAbs).length) *
     (edgeHiPos I e ↦ if (I.edge e).upper < 0 then 1 else 0) *
     (edgeHiPos I e + 1 ↦
       (Nat.digits (2 ^ narrowLimbWidth I) (I.edge e).upper.natAbs).length) *
     Assn.list (edgeCostPos I e) (intWords (narrowLimbWidth I) (I.edge e).cost)) = F1
  sep_apply hF1
  sep_step from (narrowLimbWidth I, (I.edge e).lower, (I.edge e).upper)
  subst F1
  sep_norm
  rw [← hloPtr_eq, ← hhiPtr_eq]
  sep_apply (list_intWords (edgeStartPos I e.val + 2) (narrowLimbWidth I) (I.edge e).lower).symm
  sep_apply (list_intWords (edgeHiPos I e) (narrowLimbWidth I) (I.edge e).upper).symm
  sep_apply (list_narrowEdgeWords I e).symm
  have hlen_eq : signedCmpDigitsLen (narrowLimbWidth I, (I.edge e).lower, (I.edge e).upper) =
      edgeLowerDigitsLen ⟨I, e⟩ := rfl
  rw [hlen_eq]
  sep_step

/-- Check `lower ≤ upper` on every edge `e < m`. Returns `1` if all hold, `0` otherwise. -/
wram_def stage0CheckCaps (oneCap : ℕ) (pEdges, m) {
  off := 0
  for i in 0 .. m {
    ok := oneCap(pEdges + off)
    if ok == 0 {
      return 0
    }
    off := off + 11
  }
  return 1
}

/-- Specification of `stage0CheckCaps`. -/
def stage0CheckCapsSpec (w : ℕ) : Spec { I : Instance // I.IsValid } where
  pre := fun ⟨I, _⟩ args => ⨆ (pEdges : ℕ),
    ⌜args = [pEdges, I.m] ∧ pEdges + 11 * I.m ≤ 2 ^ w ∧ 11 * I.m < 2 ^ w ∧ 10 < 2 ^ w⌝ *
    Assn.list 0 (narrowEncode I) *
    (∏ i ∈ Finset.range I.m,
      Assn.list (pEdges + i * 11) (if h : i < I.m then edgeRec I ⟨i, h⟩ else []))
  post := fun ⟨I, _⟩ args v => ⨆ (pEdges : ℕ),
    ⌜args = [pEdges, I.m] ∧
      (v = 1 ∧ (∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper) ∨
       v = 0 ∧ (∀ f, ¬ I.IsFeasible f))⌝ *
    Assn.list 0 (narrowEncode I) *
    (∏ i ∈ Finset.range I.m,
      Assn.list (pEdges + i * 11) (if h : i < I.m then edgeRec I ⟨i, h⟩ else []))

theorem stage0CheckCaps_meets {w : ℕ} {p : Program} {f oneCap : ℕ} {T1 : ℕ → ℕ}
    (hmono : ∀ a b, a ≤ b → T1 a ≤ T1 b)
    (hp : p.procs[f]? = some (stage0CheckCaps oneCap))
    (h1 : Meets w p oneCap ((stage0CheckOneCapSpec w).withCost fun x _ =>
      T1 (edgeLowerDigitsLen x))) :
    Meets w p f ((stage0CheckCapsSpec w).withCost fun d _ =>
      (T1 (narrowMaxCapLimbs d.1) + 55) * d.1.m + 40) := by
  sep_enter ⟨I, hv⟩ with hpE_fit h11m hw10
  sep_apply list_narrowEncode_split I hv
  generalize hF0 :
    ((0 ↦ narrowLimbWidth I) * (1 ↦ I.n) * (2 ↦ I.m) *
     ∏ v ∈ Finset.range I.n,
       Assn.list (demStartPos I v)
         (if _ : v < I.n then intWords (narrowLimbWidth I) (I.d v) else [])) = F0
  sep_apply hF0
  sep_step
  sep_for (fun i (ok : ℕ) =>
    ⟨[pEdges, I.m, i * 11, i, ok],
      i ≤ I.m ∧ ∀ (j : ℕ) (hj : j < I.m), j < i → (I.edge ⟨j, hj⟩).lower ≤ (I.edge ⟨j, hj⟩).upper,
      (T1 (narrowMaxCapLimbs I) + 40) * (I.m - i) + 15,
      [F0,
       ∏ j ∈ Finset.range I.m,
         Assn.list (edgeStartPos I j)
           (if h : j < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨j, h⟩) else []),
       ∏ j ∈ Finset.range I.m,
         Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else [])]⟩)
    with ok
  · have hmem : i ∈ Finset.range I.m := Finset.mem_range.mpr hhi
    let e : Fin I.m := ⟨i, hhi⟩
    have hdig_le : edgeLowerDigitsLen ⟨I, e⟩ ≤ narrowMaxCapLimbs I := by
      unfold edgeLowerDigitsLen narrowMaxCapLimbs
      dsimp only
      exact digits_length_mono (by have := two_le_pow (one_le_narrowLimbWidth I); omega)
        (lower_natAbs_le_maxCapacity' I e)
    have hT_le : T1 (edgeLowerDigitsLen ⟨I, e⟩) ≤ T1 (narrowMaxCapLimbs I) := hmono _ _ hdig_le
    have hpEi_fit : pEdges + i * 11 + 11 ≤ 2 ^ w := by
      have : (i + 1) * 11 ≤ I.m * 11 := Nat.mul_le_mul_right 11 (by omega)
      omega
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (edgeStartPos I j)
        (if h : j < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨j, h⟩) else []))
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else []))
    have hcur_in : Assn.list (edgeStartPos I i)
          (if h : i < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨i, h⟩) else []) =
        Assn.list (edgeStartPos I e.val) (narrowEdgeWords (narrowLimbWidth I) (I.edge e)) := by
      simp [e, hhi]
    have hcur_rec : Assn.list (pEdges + i * 11)
          (if h : i < I.m then edgeRec I ⟨i, h⟩ else []) =
        Assn.list (pEdges + i * 11) (edgeRec I e) := by simp [e, hhi]
    sep_apply hcur_in
    sep_apply hcur_rec
    sep_step from (⟨I, e⟩ : (J : Instance) × Fin J.m)
    subst ok_1
    sep_apply hcur_in.symm
    sep_apply hcur_rec.symm
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (edgeStartPos I j)
        (if h : j < I.m then narrowEdgeWords (narrowLimbWidth I) (I.edge ⟨j, h⟩) else []))).symm
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else []))).symm
    sep_step
    · have hlt : (I.edge e).upper < (I.edge e).lower := by
        by_contra hle; push Not at hle; simp [hle] at hcond
      have hinf : ∀ f, ¬ I.IsFeasible f := FlowReduction.infeasible_of_upper_lt_lower I e hlt
      subst F0
      sep_norm
      sep_apply (list_narrowEncode_split I hv).symm
      sep_step
      exact Or.inr ⟨rfl, hinf⟩
    · have hle : (I.edge e).lower ≤ (I.edge e).upper := by
        by_contra hgt; simp [hgt] at hcond
      have hall_next : ∀ (j : ℕ) (hj : j < I.m), j < i + 1 →
          (I.edge ⟨j, hj⟩).lower ≤ (I.edge ⟨j, hj⟩).upper := by
        intro j hj hji
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hji) with hlt | rfl
        · exact hinv_1 j hj hlt
        · exact hle
      have hoff_eq : i * 11 + 11 = (i + 1) * 11 := by ring
      have hoff_lt : i * 11 + 11 < 2 ^ w := by omega
      sep_step; sep_step
  · subst F0
    sep_norm
    sep_apply (list_narrowEncode_split I hv).symm
    have hall : ∀ e : Fin I.m, (I.edge e).lower ≤ (I.edge e).upper :=
      fun e => hinv_1 e.val e.isLt e.isLt
    sep_step
    exact Or.inl ⟨rfl, hall⟩

/-! ### `stage0ScanEnd` and `stage0Labels` -/

theorem vertexLabels_scan_append {n : ℕ} (s : VertexLabels n) (vs₁ vs₂ : List (Fin n)) :
    s.scan (vs₁ ++ vs₂) = (s.scan vs₁).scan vs₂ := by
  induction vs₁ generalizing s with
  | nil => rfl
  | cons v vs₁ ih => exact ih (s.encounter v)

/-- Active-vertex inverse list built alongside `VertexLabels.scan`. -/
def activeScan {n : ℕ} : VertexLabels n → List ℕ → List (Fin n) → List ℕ
  | _, act, [] => act
  | s, act, v :: vs =>
    if s.table v = 0 then
      activeScan (s.encounter v) (act ++ [v.val]) vs
    else
      activeScan (s.encounter v) act vs

theorem activeScan_append {n : ℕ} (s : VertexLabels n) (act : List ℕ)
    (vs₁ vs₂ : List (Fin n)) :
    activeScan s act (vs₁ ++ vs₂) = activeScan (s.scan vs₁) (activeScan s act vs₁) vs₂ := by
  induction vs₁ generalizing s act with
  | nil => rfl
  | cons v vs₁ ih =>
    simp only [List.cons_append, activeScan, VertexLabels.scan]
    split_ifs <;> exact ih _ _

/-- Invariant relating `activeScan` to `VertexLabels`: `act` has length `s.count`, each entry is
a vertex `< n`, and `s.table (act[c]) = c + 1`. -/
def ActiveInv {n : ℕ} (s : VertexLabels n) (act : List ℕ) : Prop :=
  act.length = s.count ∧
  ∀ (c : ℕ) (hc : c < act.length),
    ∃ hv : act[c]'hc < n, s.table ⟨act[c]'hc, hv⟩ = c + 1

theorem activeInv_empty (n : ℕ) : ActiveInv (VertexLabels.empty n) [] :=
  ⟨rfl, fun _ hc => False.elim (Nat.not_lt_zero _ hc)⟩

theorem activeInv_encounter {n : ℕ} {s : VertexLabels n} {act : List ℕ}
    (_hs : s.Valid) (hinv : ActiveInv s act) (v : Fin n) :
    ActiveInv (s.encounter v) (if s.table v = 0 then act ++ [v.val] else act) := by
  by_cases h0 : s.table v = 0
  · simp only [h0, ↓reduceIte, VertexLabels.encounter]
    refine ⟨by simp [hinv.1], fun c hc => ?_⟩
    have hc' : c < act.length + 1 := by simpa using hc
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hc') with hlt | rfl
    · have hget : (act ++ [v.val])[c]'hc = act[c]'hlt :=
        List.getElem_append_left hlt
      obtain ⟨hv, htab⟩ := hinv.2 c hlt
      refine ⟨by simpa [hget] using hv, ?_⟩
      have hne : (⟨act[c]'hlt, hv⟩ : Fin n) ≠ v := by
        intro heq; rw [heq, h0] at htab; omega
      simp [hget, Function.update_of_ne hne, htab]
    · have hget : (act ++ [v.val])[act.length]'hc = v.val := by
        rw [List.getElem_append_right le_rfl]; simp
      refine ⟨by simp [hget], ?_⟩
      simp [hinv.1]
  · simp only [h0, ↓reduceIte, VertexLabels.encounter]
    exact hinv

/-- Scan one endpoint column (`fieldOff = 0` for tails, `fieldOff = 1` for heads) across all `m`
edges, updating `pLabel` and `pActive` and returning the updated active count `cnt`. -/
wram_def stage0ScanEnd (pEdges, pLabel, pActive, m, fieldOff, cnt) {
  off := 0
  for i in 0 .. m {
    u := mem[pEdges + off + fieldOff]
    if mem[pLabel + u] == 0 {
      mem[pActive + cnt] := u
      cnt := cnt + 1
      mem[pLabel + u] := cnt
    }
    off := off + 11
  }
  return cnt
}

/-- Named value for `stage0ScanEndSpec`. -/
structure Stage0ScanEndData where
  I : Instance
  hv : I.IsValid
  fieldOff : ℕ
  s0 : VertexLabels I.n
  act0 : List ℕ
  actTail : List ℕ

/-- The endpoint list scanned by `stage0ScanEnd`: tails if `fieldOff = 0`, heads otherwise. -/
def scanEndList (I : Instance) (hv : I.IsValid) (fieldOff : ℕ) : List (Fin I.n) :=
  if fieldOff = 0 then List.ofFn (FlowReduction.shiftedGraph I hv).tail
  else List.ofFn (FlowReduction.shiftedGraph I hv).head

/-- Specification of `stage0ScanEnd`. -/
def stage0ScanEndSpec (w : ℕ) : Spec Stage0ScanEndData where
  pre d args := ⨆ (pEdges : ℕ) (pLabel : ℕ) (pActive : ℕ),
    ⌜args = [pEdges, pLabel, pActive, d.I.m, d.fieldOff, d.s0.count] ∧
      (d.fieldOff = 0 ∨ d.fieldOff = 1) ∧
      d.s0.Valid ∧ ActiveInv d.s0 d.act0 ∧
      d.s0.count + d.I.m ≤ d.act0.length + d.actTail.length ∧
      d.s0.count + d.I.m < 2 ^ w ∧
      pEdges + 11 * d.I.m ≤ 2 ^ w ∧ 11 * d.I.m < 2 ^ w ∧ 10 < 2 ^ w⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else [])) *
    Assn.list pLabel (List.ofFn d.s0.table) *
    Assn.list pActive (d.act0 ++ d.actTail)
  post d args cnt' := ⨆ (pEdges : ℕ) (pLabel : ℕ) (pActive : ℕ) (actTail' : List ℕ),
    let vs := scanEndList d.I d.hv d.fieldOff
    let s1 := d.s0.scan vs
    let act1 := activeScan d.s0 d.act0 vs
    ⌜args = [pEdges, pLabel, pActive, d.I.m, d.fieldOff, d.s0.count] ∧
      cnt' = s1.count ∧ s1.Valid ∧ ActiveInv s1 act1 ∧
      act1.length + actTail'.length = d.act0.length + d.actTail.length⌝ *
    (∏ i ∈ Finset.range d.I.m,
      Assn.list (pEdges + i * 11) (if h : i < d.I.m then edgeRec d.I ⟨i, h⟩ else [])) *
    Assn.list pLabel (List.ofFn s1.table) *
    Assn.list pActive (act1 ++ actTail')

theorem stage0ScanEnd_meets {w : ℕ} {p : Program} {f : ℕ}
    (hp : p.procs[f]? = some stage0ScanEnd) :
    Meets w p f ((stage0ScanEndSpec w).withCost fun d _ => 80 * d.I.m + 40) := by
  sep_enter ⟨I, hv, fieldOff, s0, act0, actTail⟩ with
    hfo hs0 hact0 hcap hcnt_lt hpE_fit h11m hw10
  set vs := scanEndList I hv fieldOff
  have hvs_len : vs.length = I.m := by
    dsimp only [vs, scanEndList]; split_ifs <;> simp
  sep_step
  have hact_init : act0 ++ actTail =
      activeScan s0 act0 (vs.take 0) ++ actTail.drop ((s0.scan (vs.take 0)).count - s0.count) := by
    simp [activeScan, VertexLabels.scan]
  have hact_init_list : Assn.list pActive (act0 ++ actTail) =
      Assn.list pActive (activeScan s0 act0 (vs.take 0) ++
        actTail.drop ((s0.scan (vs.take 0)).count - s0.count)) := by rw [hact_init]
  sep_apply hact_init_list
  sep_for (fun i (u : ℕ) =>
    let si := s0.scan (vs.take i)
    let acti := activeScan s0 act0 (vs.take i)
    ⟨[pEdges, pLabel, pActive, I.m, fieldOff, si.count, i * 11, i, u],
      i ≤ I.m ∧ si.Valid ∧ ActiveInv si acti ∧
        s0.count ≤ si.count ∧ si.count ≤ s0.count + i,
      70 * (I.m - i) + 10,
      [∏ j ∈ Finset.range I.m,
         Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else []),
       Assn.list pLabel (List.ofFn si.table),
       Assn.list pActive (acti ++ actTail.drop (si.count - s0.count))]⟩) with u
  · have hmem : i ∈ Finset.range I.m := Finset.mem_range.mpr hhi
    let e : Fin I.m := ⟨i, hhi⟩
    set si := s0.scan (vs.take i)
    set acti := activeScan s0 act0 (vs.take i)
    have hrec_len : (edgeRec I e).length = 11 := rfl
    have hvi : i < vs.length := by omega
    have htake : vs.take (i + 1) = vs.take i ++ [vs[i]'hvi] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hvi]; rfl
    have hsi_next : s0.scan (vs.take (i + 1)) = si.encounter (vs[i]'hvi) := by
      rw [htake, vertexLabels_scan_append]; rfl
    have hacti_next : activeScan s0 act0 (vs.take (i + 1)) =
        (if si.table (vs[i]'hvi) = 0 then acti ++ [(vs[i]'hvi).val] else acti) := by
      rw [htake, activeScan_append]; rfl
    have hrec_val : (edgeRec I e)[fieldOff]'(by rcases hfo with rfl | rfl <;> simp [edgeRec]) =
        (vs[i]'hvi).val := by
      rcases hfo with rfl | rfl <;>
        simp [vs, scanEndList, edgeRec, FlowReduction.shiftedGraph, e]
    have hpEi_fit : pEdges + i * 11 + 11 ≤ 2 ^ w := by
      have : (i + 1) * 11 ≤ I.m * 11 := Nat.mul_le_mul_right 11 (by omega)
      omega
    sep_apply Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else []))
    have hcur_rec : Assn.list (pEdges + i * 11)
          (if h : i < I.m then edgeRec I ⟨i, h⟩ else []) =
        Assn.list (pEdges + i * 11) (edgeRec I e) := by simp [e, hhi]
    sep_apply hcur_rec
    sep_step
    rw [hrec_val] at hu_1; subst u_1
    sep_apply hcur_rec.symm
    sep_apply (Assn.prod_eq_mul_erase hmem
      (fun j => Assn.list (pEdges + j * 11) (if h : j < I.m then edgeRec I ⟨j, h⟩ else []))).symm
    have htab_len : (vs[i]'hvi).val < (List.ofFn si.table).length := by simp
    have htab_get : (List.ofFn si.table)[(vs[i]'hvi).val]'htab_len = si.table (vs[i]'hvi) := by
      simp
    have hsi_valid' := VertexLabels.encounter_valid si hinv_1 (vs[i]'hvi)
    have hacti_inv' := activeInv_encounter hinv_1 hinv_2 (vs[i]'hvi)
    have hoff_eq : i * 11 + 11 = (i + 1) * 11 := by ring
    have hoff_lt : i * 11 + 11 < 2 ^ w := by omega
    sep_step
    · rw [htab_get] at hcond
      have hdrop_lt : si.count - s0.count < actTail.length := by
        have := hact0.1; omega
      have hdrop_eq : actTail.drop (si.count - s0.count) =
          actTail[si.count - s0.count]'hdrop_lt :: actTail.drop (si.count + 1 - s0.count) := by
        have : si.count + 1 - s0.count = (si.count - s0.count) + 1 := by omega
        rw [this, List.drop_eq_getElem_cons hdrop_lt]
      have hcnt_next_lt : si.count + 1 < 2 ^ w := by omega
      have hact_len_lt : si.count < (acti ++ actTail.drop (si.count - s0.count)).length := by
        simp only [List.length_append, List.length_drop]
        have := hact0.1; have := hinv_2.1; omega
      have hact_set : (acti ++ actTail.drop (si.count - s0.count)).set si.count (vs[i]'hvi).val =
          (acti ++ [(vs[i]'hvi).val]) ++ actTail.drop (si.count + 1 - s0.count) := by
        rw [hdrop_eq]
        have hlen_a : acti.length = si.count := hinv_2.1
        rw [List.set_append_right _ _ (by omega)]
        simp [hlen_a]
      have htab_set : (List.ofFn si.table).set (vs[i]'hvi).val (si.count + 1) =
          List.ofFn (si.encounter (vs[i]'hvi)).table := by
        refine List.ext_getElem (by simp) fun j hj _ => ?_
        by_cases hje : j = (vs[i]'hvi).val
        · subst hje
          simp [VertexLabels.encounter, hcond]
        · have hjne : (⟨j, by simp at hj; exact hj⟩ : Fin I.n) ≠ vs[i]'hvi :=
            fun heq => hje (congrArg Fin.val heq)
          simp [List.getElem_set_ne (Ne.symm hje), VertexLabels.encounter, hcond,
            Function.update_of_ne hjne]
      have hsi_c : (s0.scan (vs.take (i + 1))).count = si.count + 1 := by
        rw [hsi_next]; simp [VertexLabels.encounter, hcond]
      have hvalid_next : (s0.scan (vs.take (i + 1))).Valid := by rw [hsi_next]; exact hsi_valid'
      have hactinv_next : ActiveInv (s0.scan (vs.take (i + 1))) (activeScan s0 act0 (vs.take (i + 1))) := by
        rw [hsi_next, hacti_next]; exact hacti_inv'
      have hcnt_ge : s0.count ≤ (s0.scan (vs.take (i + 1))).count := by omega
      have hcnt_le : (s0.scan (vs.take (i + 1))).count ≤ s0.count + (i + 1) := by omega
      have hact_set' : Assn.list pActive ((acti ++ actTail.drop (si.count - s0.count)).set si.count (vs[i]'hvi).val) =
          Assn.list pActive (activeScan s0 act0 (vs.take (i + 1)) ++
            actTail.drop ((s0.scan (vs.take (i + 1))).count - s0.count)) := by
        rw [hact_set]; simp [hsi_c, hacti_next, hcond]
      have htab_set' : Assn.list pLabel ((List.ofFn si.table).set (vs[i]'hvi).val (si.count + 1)) =
          Assn.list pLabel (List.ofFn (s0.scan (vs.take (i + 1))).table) := by
        rw [htab_set, hsi_next]
      sep_step; sep_step; sep_step; sep_step
      subst cnt
      sep_step
      sep_apply hact_set'
      sep_apply htab_set'
      sep_step
    · rw [htab_get] at hcond
      have hsi_eq : s0.scan (vs.take (i + 1)) = si := by
        rw [hsi_next]; simp [VertexLabels.encounter, hcond]
      have hacti_eq : activeScan s0 act0 (vs.take (i + 1)) = acti := by
        rw [hacti_next]; simp [hcond]
      have hvalid_next : (s0.scan (vs.take (i + 1))).Valid := by rw [hsi_eq]; exact hinv_1
      have hactinv_next : ActiveInv (s0.scan (vs.take (i + 1))) (activeScan s0 act0 (vs.take (i + 1))) := by
        rw [hsi_eq, hacti_eq]; exact hinv_2
      have hcnt_ge : s0.count ≤ (s0.scan (vs.take (i + 1))).count := by rw [hsi_eq]; exact hinv_3
      have hcnt_le : (s0.scan (vs.take (i + 1))).count ≤ s0.count + (i + 1) := by rw [hsi_eq]; omega
      have hact_eq' : Assn.list pActive (acti ++ actTail.drop (si.count - s0.count)) =
          Assn.list pActive (activeScan s0 act0 (vs.take (i + 1)) ++
            actTail.drop ((s0.scan (vs.take (i + 1))).count - s0.count)) := by
        rw [hsi_eq, hacti_eq]
      have htab_eq' : Assn.list pLabel (List.ofFn si.table) =
          Assn.list pLabel (List.ofFn (s0.scan (vs.take (i + 1))).table) := by rw [hsi_eq]
      sep_apply hact_eq'
      sep_apply htab_eq'
      have hcnt_eq : si.count = (s0.scan (vs.take (i + 1))).count := by rw [hsi_eq]
      sep_step; sep_step
  · have htake_all : vs.take I.m = vs := by rw [← hvs_len, List.take_length]
    simp only [htake_all] at hinv_1 hinv_2 hinv_3 hinv_4 ⊢
    have hlen_end : (activeScan s0 act0 vs).length +
        (actTail.drop ((s0.scan vs).count - s0.count)).length = act0.length + actTail.length := by
      simp only [List.length_drop]
      have := hact0.1; have := hinv_2.1; omega
    sep_step

/-- Build `(shiftedGraph I hv).endpointLabels` in `pLabel` (`n` words) and active-vertex list in
`pActive` (`2 * m` words), returning `cnt = endpointLabels.count ≤ 2 * m`. -/
wram_def stage0Labels (scanEnd : ℕ) (pEdges, pLabel, pActive, m) {
  cnt := scanEnd(pEdges, pLabel, pActive, m, 0, 0)
  cnt := scanEnd(pEdges, pLabel, pActive, m, 1, cnt)
  return cnt
}

/-- Specification of `stage0Labels`. -/
def stage0LabelsSpec (w : ℕ) : Spec { I : Instance // I.IsValid } where
  pre := fun ⟨I, _⟩ args => ⨆ (pEdges : ℕ) (pLabel : ℕ) (pActive : ℕ),
    ⌜args = [pEdges, pLabel, pActive, I.m] ∧
      pEdges + 11 * I.m ≤ 2 ^ w ∧ 11 * I.m < 2 ^ w ∧ 10 < 2 ^ w⌝ *
    (∏ i ∈ Finset.range I.m,
      Assn.list (pEdges + i * 11) (if h : i < I.m then edgeRec I ⟨i, h⟩ else [])) *
    Assn.list pLabel (List.replicate I.n 0) *
    Assn.list pActive (List.replicate (2 * I.m) 0)
  post := fun ⟨I, hv⟩ args cnt => ⨆ (pEdges : ℕ) (pLabel : ℕ) (pActive : ℕ)
      (act : List ℕ) (actTail : List ℕ),
    let el := (FlowReduction.shiftedGraph I hv).endpointLabels
    ⌜args = [pEdges, pLabel, pActive, I.m] ∧
      cnt = el.count ∧ cnt ≤ 2 * I.m ∧ ActiveInv el act ∧
      act.length + actTail.length = 2 * I.m⌝ *
    (∏ i ∈ Finset.range I.m,
      Assn.list (pEdges + i * 11) (if h : i < I.m then edgeRec I ⟨i, h⟩ else [])) *
    Assn.list pLabel (List.ofFn el.table) *
    Assn.list pActive (act ++ actTail)

theorem stage0Labels_meets {w : ℕ} {p : Program} {f scanEnd : ℕ} {Tse : ℕ → ℕ}
    (hp : p.procs[f]? = some (stage0Labels scanEnd))
    (hse : Meets w p scanEnd ((stage0ScanEndSpec w).withCost fun d _ => Tse d.I.m)) :
    Meets w p f ((stage0LabelsSpec w).withCost fun d _ => 2 * Tse d.1.m + 40) := by
  sep_enter ⟨I, hv⟩ with hpE_fit h11m hw10
  have hrep_lab : List.replicate I.n 0 = List.ofFn (VertexLabels.empty I.n).table := by
    refine List.ext_getElem (by simp) fun i _ _ => by simp [VertexLabels.empty]
  have hrep_act : List.replicate (2 * I.m) 0 = [] ++ List.replicate (2 * I.m) 0 := rfl
  rw [hrep_lab, hrep_act]
  have hval0 := VertexLabels.empty_valid I.n
  have hinv0 := activeInv_empty I.n
  have hcap0 : (VertexLabels.empty I.n).count + I.m ≤
      ([] : List ℕ).length + (List.replicate (2 * I.m) 0).length := by
    simp [VertexLabels.empty]; omega
  have hcnt0_lt : (VertexLabels.empty I.n).count + I.m < 2 ^ w := by
    simp [VertexLabels.empty]; omega
  sep_step from (⟨I, hv, 0, VertexLabels.empty I.n, [], List.replicate (2 * I.m) 0⟩ :
    Stage0ScanEndData) with _ hval1 hinv1 hlen1
  have hlen1' : (activeScan (VertexLabels.empty I.n) [] (scanEndList I hv 0)).length +
      actTail'.length = 2 * I.m := by simpa using hlen1
  have hcnt1_le : ((VertexLabels.empty I.n).scan (scanEndList I hv 0)).count ≤ I.m := by
    have h := VertexLabels.scan_count_le (VertexLabels.empty I.n) (scanEndList I hv 0)
    simp only [VertexLabels.empty, zero_add, scanEndList, ↓reduceIte, List.length_ofFn] at h
    exact h
  have hcap2 : ((VertexLabels.empty I.n).scan (scanEndList I hv 0)).count + I.m ≤
      (activeScan (VertexLabels.empty I.n) [] (scanEndList I hv 0)).length + actTail'.length := by
    have := hinv1.1; omega
  have hcnt2_lt : ((VertexLabels.empty I.n).scan (scanEndList I hv 0)).count + I.m < 2 ^ w := by
    omega
  sep_step from (⟨I, hv, 1,
    (VertexLabels.empty I.n).scan (scanEndList I hv 0),
    activeScan (VertexLabels.empty I.n) [] (scanEndList I hv 0), actTail'⟩ :
    Stage0ScanEndData) with _ hval2 hinv2 hlen2
  have hlen2' : (activeScan ((VertexLabels.empty I.n).scan (scanEndList I hv 0))
      (activeScan (VertexLabels.empty I.n) [] (scanEndList I hv 0))
      (scanEndList I hv 1)).length + actTail'_1.length = 2 * I.m := by omega
  have hel_eq : ((VertexLabels.empty I.n).scan (scanEndList I hv 0)).scan (scanEndList I hv 1) =
      (FlowReduction.shiftedGraph I hv).endpointLabels := by
    rw [← vertexLabels_scan_append]
    rfl
  have hcnt_le : (FlowReduction.shiftedGraph I hv).endpointLabels.count ≤ 2 * I.m :=
    (FlowReduction.shiftedGraph I hv).endpointLabels_count_le
  rw [hel_eq] at hinv2 hcnt_1 ⊢
  sep_step

end MinCostFlow.NarrowProg
