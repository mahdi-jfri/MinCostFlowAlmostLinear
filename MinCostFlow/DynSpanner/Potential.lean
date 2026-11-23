module

public import MinCostFlow.DynSpanner.Walks
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Degree-entropy potential for vertex-split encoding bounds (Lemma 2.1)

This file formalizes the degree-entropy potential `Φ(H) = ∑_{v ∈ H.V} deg_H(v) log₂ deg_H(v)`
from Lemma 2.1 (`prelims.tex`, page 6) for graphs `H` undergoing edge insertions, edge deletions,
and vertex splits. It proves that every edge insertion increases `Φ` by at most `O(log(m + 2))`,
deletions do not increase `Φ`, and each vertex split decreases `Φ` by at least
`min(deg(v₁), deg(v₂)) = Enc(u) - 1`.
-/

namespace MinCostFlow.DynSpanner

@[expose] public section

/-- Auxiliary function `d ↦ d * log₂ d` (with `0 ↦ 0`) used in the Lemma 2.1 split potential. -/
noncomputable def degPotFun (d : ℕ) : ℝ :=
  if d = 0 then 0 else (d : ℝ) * Real.logb 2 (d : ℝ)

/-- Degree-entropy potential `Φ(H) = ∑_{v ∈ H.V} deg_H(v) log₂ deg_H(v)` (Lemma 2.1, page 6). -/
noncomputable def degPot (H : MGraph) : ℝ :=
  ∑ v ∈ H.V, degPotFun (H.deg v)

/-- Number of edge insertions in a batch `U`. -/
def batchInsertCount (U : List Update) : ℕ :=
  U.countP fun u => match u with | .insert _ _ _ => true | _ => false

theorem degPotFun_nonneg (d : ℕ) : 0 ≤ degPotFun d := by
  unfold degPotFun
  split_ifs with hd
  · exact le_rfl
  · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    have hlog : 0 ≤ Real.logb 2 (d : ℝ) := Real.logb_nonneg (by norm_num) hd1
    positivity

theorem degPotFun_mono {a b : ℕ} (hab : a ≤ b) : degPotFun a ≤ degPotFun b := by
  unfold degPotFun
  split_ifs with ha hb
  · exact le_rfl
  · have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hb
    have hlog : 0 ≤ Real.logb 2 (b : ℝ) := Real.logb_nonneg (by norm_num) hb1
    positivity
  · omega
  · have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ha
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hlog : Real.logb 2 (a : ℝ) ≤ Real.logb 2 (b : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) ha_pos habR
    exact mul_le_mul habR hlog
      (Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero ha))
      (by positivity)

theorem degPot_nonneg (H : MGraph) : 0 ≤ degPot H :=
  Finset.sum_nonneg fun v _ => degPotFun_nonneg (H.deg v)

theorem deg_le_two_mul_m {H : MGraph} (_hV : H.IsValid) (v : ℕ) : H.deg v ≤ 2 * H.m := by
  unfold MGraph.deg MGraph.m
  have h1 : (H.E.filter fun e => H.tail e = v).card ≤ H.E.card :=
    Finset.card_filter_le _ _
  have h2 : (H.E.filter fun e => H.head e = v).card ≤ H.E.card :=
    Finset.card_filter_le _ _
  omega

private theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have h1 : (1 / 2 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
    have h := Real.add_one_lt_exp (by norm_num : (-(1 / 2 : ℝ)) ≠ 0)
    linarith
  have h2 : Real.exp (1 / 2 : ℝ) < 2 := by
    rw [Real.exp_neg] at h1
    calc Real.exp (1 / 2 : ℝ)
        = ((Real.exp (1 / 2 : ℝ))⁻¹)⁻¹ := (inv_inv _).symm
      _ < (1 / 2 : ℝ)⁻¹ := inv_strictAnti₀ (by positivity) h1
      _ = 2 := by norm_num
  have h3 := Real.log_lt_log (Real.exp_pos _) h2
  rwa [Real.log_exp] at h3

theorem logb_two_le_two_mul_log {x : ℝ} (hx : 1 ≤ x) : Real.logb 2 x ≤ 2 * Real.log x := by
  rw [Real.logb]
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := half_lt_log_two
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem degPot_le {H : MGraph} (hV : H.IsValid) :
    degPot H ≤ 2 * (H.m : ℝ) * (2 * Real.log (2 * (H.m : ℝ) + 2)) := by
  have hterm : ∀ v ∈ H.V, degPotFun (H.deg v) ≤
      (H.deg v : ℝ) * (2 * Real.log (2 * (H.m : ℝ) + 2)) := by
    intro v _
    have hdeg_le : (H.deg v : ℝ) ≤ 2 * (H.m : ℝ) + 2 := by
      have := deg_le_two_mul_m hV v
      exact_mod_cast (by omega : H.deg v ≤ 2 * H.m + 2)
    unfold degPotFun
    split_ifs with hd
    · have hlog : 0 ≤ Real.log (2 * (H.m : ℝ) + 2) := Real.log_nonneg (by linarith)
      exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    · have hd1 : (1 : ℝ) ≤ (H.deg v : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
      have hlog : Real.logb 2 (H.deg v : ℝ) ≤ 2 * Real.log (2 * (H.m : ℝ) + 2) := by
        calc Real.logb 2 (H.deg v : ℝ)
            ≤ Real.logb 2 (2 * (H.m : ℝ) + 2) :=
              Real.logb_le_logb_of_le (by norm_num) (by linarith) hdeg_le
          _ ≤ 2 * Real.log (2 * (H.m : ℝ) + 2) := logb_two_le_two_mul_log (by linarith)
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
  calc degPot H
      ≤ ∑ v ∈ H.V, (H.deg v : ℝ) * (2 * Real.log (2 * (H.m : ℝ) + 2)) :=
        Finset.sum_le_sum hterm
    _ = (∑ v ∈ H.V, (H.deg v : ℝ)) * (2 * Real.log (2 * (H.m : ℝ) + 2)) := by
        rw [Finset.sum_mul]
    _ = 2 * (H.m : ℝ) * (2 * Real.log (2 * (H.m : ℝ) + 2)) := by
        have hs : (∑ v ∈ H.V, (H.deg v : ℝ)) = 2 * (H.m : ℝ) := by
          exact_mod_cast sum_deg_eq_two_mul_m hV
        rw [hs]

private theorem degPotFun_add_sub_aux (a b : ℕ) (hab : a ≤ b) :
    (a : ℝ) + degPotFun a + degPotFun b ≤ degPotFun (a + b) := by
  by_cases ha : a = 0
  · subst ha; simp [degPotFun]
  · have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
    have hb_pos : 0 < b := lt_of_lt_of_le ha_pos hab
    have hab_pos : a + b ≠ 0 := by omega
    unfold degPotFun
    simp only [ha, Nat.ne_of_gt hb_pos, hab_pos, ↓reduceIte]
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha_pos
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb_pos
    have h2a : (2 : ℝ) * (a : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * a ≤ a + b)
    have hb_le : (b : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega : b ≤ a + b)
    have hlog_a : 1 + Real.logb 2 (a : ℝ) ≤ Real.logb 2 ((a + b : ℕ) : ℝ) := by
      have hmul : Real.logb 2 (2 * (a : ℝ)) = 1 + Real.logb 2 (a : ℝ) := by
        rw [Real.logb_mul (by norm_num) (ne_of_gt haR), Real.logb_self_eq_one (by norm_num)]
      rw [← hmul]
      exact Real.logb_le_logb_of_le (by norm_num) (by positivity) h2a
    have hlog_b : Real.logb 2 (b : ℝ) ≤ Real.logb 2 ((a + b : ℕ) : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) hbR hb_le
    push_cast at hlog_a hlog_b ⊢
    nlinarith

theorem degPotFun_add_sub (a b : ℕ) :
    ((min a b : ℕ) : ℝ) + degPotFun a + degPotFun b ≤ degPotFun (a + b) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact degPotFun_add_sub_aux a b hab
  · rw [min_eq_right hba, add_comm a b, add_assoc (b : ℝ), add_comm (degPotFun a) (degPotFun b),
      ← add_assoc]
    exact degPotFun_add_sub_aux b a hba

theorem degPotFun_succ_sub {d m : ℕ} (hm : d ≤ 2 * m + 1) :
    degPotFun (d + 1) - degPotFun d ≤ 2 * Real.log (2 * (m : ℝ) + 2) + 2 := by
  by_cases hd : d = 0
  · subst hd
    simp only [degPotFun, Nat.zero_add, one_ne_zero, ↓reduceIte, Nat.cast_one, Real.logb_one,
      mul_zero, sub_self]
    have hlog : 0 ≤ Real.log (2 * (m : ℝ) + 2) := Real.log_nonneg (by linarith)
    linarith
  · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
    unfold degPotFun
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, hd, ↓reduceIte]
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := half_lt_log_two
    have hd_step : (d : ℝ) * (Real.logb 2 ((d + 1 : ℕ) : ℝ) - Real.logb 2 (d : ℝ)) ≤ 2 := by
      have hsub : Real.logb 2 ((d + 1 : ℕ) : ℝ) - Real.logb 2 (d : ℝ) =
          Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ)) / Real.log 2 := by
        rw [Real.logb, Real.logb, ← sub_div, ← Real.log_div (by positivity) (ne_of_gt hdR)]
      rw [hsub]
      have hlog_le : Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ)) ≤ ((d + 1 : ℕ) : ℝ) / (d : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hstep : ((d + 1 : ℕ) : ℝ) / (d : ℝ) - 1 = 1 / (d : ℝ) := by
        push_cast; field_simp; ring
      have hmul_d : (d : ℝ) * (Real.log (((d + 1 : ℕ) : ℝ) / (d : ℝ)) / Real.log 2) ≤
          (d : ℝ) * ((1 / (d : ℝ)) / Real.log 2) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hlog_le.trans_eq hstep)
          (by linarith)) (by positivity)
      have hcancel : (d : ℝ) * ((1 / (d : ℝ)) / Real.log 2) = 1 / Real.log 2 := by
        field_simp
      have hinv : 1 / Real.log 2 ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      linarith
    have hlog_d1 : Real.logb 2 ((d + 1 : ℕ) : ℝ) ≤ 2 * Real.log (2 * (m : ℝ) + 2) := by
      have hd1_le : ((d + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) + 2 := by
        exact_mod_cast (by omega : d + 1 ≤ 2 * m + 2)
      calc Real.logb 2 ((d + 1 : ℕ) : ℝ)
          ≤ Real.logb 2 (2 * (m : ℝ) + 2) :=
            Real.logb_le_logb_of_le (by norm_num) (by positivity) hd1_le
        _ ≤ 2 * Real.log (2 * (m : ℝ) + 2) := logb_two_le_two_mul_log (by linarith)
    push_cast at hd_step hlog_d1 ⊢
    nlinarith

theorem degPot_delete_le {H : MGraph} (e : ℕ) :
    degPot (H.applyUpdate (.delete e)) ≤ degPot H := by
  refine Finset.sum_le_sum fun v _ => degPotFun_mono ?_
  unfold MGraph.deg MGraph.applyUpdate
  exact add_le_add
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _)))
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _)))

theorem degPot_split_le {H : MGraph} (hV : H.IsValid) {v v' : ℕ} {St Sh : Finset ℕ}
    (hu : H.UpdateIsValid (.split v v' St Sh)) :
    (H.updateEnc (.split v v' St Sh) : ℝ) + degPot (H.applyUpdate (.split v v' St Sh)) ≤ 1 + degPot H := by
  set H' := H.applyUpdate (.split v v' St Sh)
  obtain ⟨hsum, hother⟩ := split_deg_add hV hu
  have hv_mem : v ∈ H.V := hu.1
  have hv'_not : v' ∉ H.V := hu.2.1
  have hV' : H'.V = insert v' H.V := rfl
  have hPot' : degPot H' = degPotFun (H'.deg v') + degPotFun (H'.deg v) +
      ∑ w ∈ H.V.erase v, degPotFun (H.deg w) := by
    unfold degPot
    rw [hV', Finset.sum_insert hv'_not]
    have hsplit_v : ∑ w ∈ H.V, degPotFun (H'.deg w) =
        degPotFun (H'.deg v) + ∑ w ∈ H.V.erase v, degPotFun (H'.deg w) :=
      (Finset.add_sum_erase H.V (fun w => degPotFun (H'.deg w)) hv_mem).symm
    rw [hsplit_v]
    have hcongr : ∑ w ∈ H.V.erase v, degPotFun (H'.deg w) =
        ∑ w ∈ H.V.erase v, degPotFun (H.deg w) := by
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [hother w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)]
    rw [hcongr]
    ring
  have hPot : degPot H = degPotFun (H.deg v) + ∑ w ∈ H.V.erase v, degPotFun (H.deg w) := by
    unfold degPot
    exact (Finset.add_sum_erase H.V (fun w => degPotFun (H.deg w)) hv_mem).symm
  have hadd := degPotFun_add_sub (H'.deg v) (H'.deg v')
  rw [hsum] at hadd
  simp only [MGraph.updateEnc, Nat.cast_add, Nat.cast_one]
  change ((min (H'.deg v) (H'.deg v') : ℕ) : ℝ) + 1 + degPot H' ≤ 1 + degPot H
  rw [hPot', hPot]
  linarith

private theorem filter_card_insert_update {E : Finset ℕ} {f : ℕ → ℕ} {e val w : ℕ} (he : e ∉ E) :
    (Finset.filter (fun x => Function.update f e val x = w) (insert e E)).card =
      (Finset.filter (fun x => f x = w) E).card + (if val = w then 1 else 0) := by
  have hcongr : (Finset.filter (fun x => Function.update f e val x = w) E) =
      (Finset.filter (fun x => f x = w) E) := by
    ext x
    simp only [Finset.mem_filter]
    refine and_congr_right fun hx => ?_
    have hne : x ≠ e := fun h => he (h ▸ hx)
    rw [Function.update_of_ne hne]
  have he_flt : e ∉ Finset.filter (fun x => Function.update f e val x = w) E := by
    intro h; exact he (Finset.mem_filter.mp h).1
  by_cases hval : val = w
  · subst hval
    have hmem : Function.update f e val e = val := Function.update_self e val f
    rw [Finset.filter_insert]
    rw [hcongr] at he_flt
    simp only [hmem, ↓reduceIte, hcongr, Finset.card_insert_of_notMem he_flt]
  · have hnot : Function.update f e val e ≠ w := by simp [hval]
    rw [Finset.filter_insert]
    simp only [eq_false hval, eq_false hnot, ↓reduceIte, hcongr, Nat.add_zero]

private theorem deg_applyUpdate_insert_eq {H : MGraph} {e u v w : ℕ} (he : e ∉ H.E) :
    (H.applyUpdate (.insert e u v)).deg w =
      H.deg w + (if u = w then 1 else 0) + (if v = w then 1 else 0) := by
  unfold MGraph.deg MGraph.applyUpdate
  dsimp only
  rw [filter_card_insert_update he, filter_card_insert_update he]
  omega

theorem degPot_insert_le {H : MGraph} (hV : H.IsValid) {e u v : ℕ}
    (hins : H.UpdateIsValid (.insert e u v)) {mBound : ℕ} (hm : H.m ≤ mBound) :
    degPot (H.applyUpdate (.insert e u v)) ≤
      degPot H + 4 * Real.log (2 * (mBound : ℝ) + 2) + 4 := by
  obtain ⟨he, hu, hv⟩ := hins
  set H' := H.applyUpdate (.insert e u v)
  have hV' : H'.V = H.V := rfl
  have hdeg_le : ∀ w, H.deg w ≤ 2 * mBound := fun w => le_trans (deg_le_two_mul_m hV w) (by omega)
  by_cases huv : u = v
  · subst huv
    have hsub : degPot H' - degPot H = degPotFun (H.deg u + 2) - degPotFun (H.deg u) := by
      unfold degPot
      rw [hV', ← Finset.add_sum_erase H.V (fun w => degPotFun (H'.deg w)) hu,
        ← Finset.add_sum_erase H.V (fun w => degPotFun (H.deg w)) hu]
      have hcongr : ∑ w ∈ H.V.erase u, degPotFun (H'.deg w) =
          ∑ w ∈ H.V.erase u, degPotFun (H.deg w) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have hne : u ≠ w := (Finset.ne_of_mem_erase hw).symm
        dsimp only [H']
        simp only [deg_applyUpdate_insert_eq he, eq_false hne, ↓reduceIte, Nat.add_zero]
      dsimp only [H']
      rw [hcongr, deg_applyUpdate_insert_eq he]
      simp only [↓reduceIte]
      ring
    have h1 := degPotFun_succ_sub (d := H.deg u) (m := mBound) (by have := hdeg_le u; omega)
    have h2 := degPotFun_succ_sub (d := H.deg u + 1) (m := mBound) (by have := hdeg_le u; omega)
    linarith
  · have hu_mem : u ∈ H.V.erase v := Finset.mem_erase.mpr ⟨huv, hu⟩
    have hsub : degPot H' - degPot H =
        (degPotFun (H.deg v + 1) - degPotFun (H.deg v)) +
        (degPotFun (H.deg u + 1) - degPotFun (H.deg u)) := by
      unfold degPot
      rw [hV', ← Finset.add_sum_erase H.V (fun w => degPotFun (H'.deg w)) hv,
        ← Finset.add_sum_erase H.V (fun w => degPotFun (H.deg w)) hv,
        ← Finset.add_sum_erase (H.V.erase v) (fun w => degPotFun (H'.deg w)) hu_mem,
        ← Finset.add_sum_erase (H.V.erase v) (fun w => degPotFun (H.deg w)) hu_mem]
      have hcongr : ∑ w ∈ (H.V.erase v).erase u, degPotFun (H'.deg w) =
          ∑ w ∈ (H.V.erase v).erase u, degPotFun (H.deg w) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have hne1 : u ≠ w := (Finset.ne_of_mem_erase hw).symm
        have hne2 : v ≠ w := (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hw)).symm
        dsimp only [H']
        simp only [deg_applyUpdate_insert_eq he, eq_false hne1, eq_false hne2, ↓reduceIte,
          Nat.add_zero]
      dsimp only [H']
      rw [hcongr, deg_applyUpdate_insert_eq he, deg_applyUpdate_insert_eq he]
      simp only [eq_false huv, eq_false (Ne.symm huv), ↓reduceIte, Nat.add_zero]
      ring
    have h1 := degPotFun_succ_sub (d := H.deg v) (m := mBound) (by have := hdeg_le v; omega)
    have h2 := degPotFun_succ_sub (d := H.deg u) (m := mBound) (by have := hdeg_le u; omega)
    linarith

/-- Degree-entropy bound on `batchEnc` along any valid sequence of insertions, deletions, and
splits whose intermediate graphs all have at most `mBound` edges (Lemma 2.1, page 6). -/
theorem batchEnc_le_degPot :
    ∀ (U : List Update) (H : MGraph) (mBound : ℕ),
      H.IsValid → H.BatchIsValid U →
      (∀ pfx sfx, U = pfx ++ sfx → (H.applyBatch pfx).m ≤ mBound) →
      (H.batchEnc U : ℝ) + degPot (H.applyBatch U) ≤
        (U.length : ℝ) + degPot H +
          (batchInsertCount U : ℝ) * (4 * Real.log (2 * (mBound : ℝ) + 2) + 4)
  | [], H, _, _, _, _ => by
    simp [MGraph.batchEnc, MGraph.applyBatch, batchInsertCount]
  | u :: U, H, mBound, hV, hBV, hm => by
    obtain ⟨hu, hBV'⟩ := hBV
    have hV1 : (H.applyUpdate u).IsValid := isValid_applyUpdate_any hV hu
    have hm0 : H.m ≤ mBound := hm [] (u :: U) rfl
    have hm' : ∀ pfx sfx, U = pfx ++ sfx → ((H.applyUpdate u).applyBatch pfx).m ≤ mBound := by
      intro pfx sfx heq
      have := hm (u :: pfx) sfx (by simp [heq])
      simpa [MGraph.applyBatch] using this
    have ih := batchEnc_le_degPot U (H.applyUpdate u) mBound hV1 hBV' hm'
    simp only [MGraph.batchEnc, MGraph.applyBatch, List.foldl_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one] at ih ⊢
    cases u with
    | delete e =>
      have hpot := degPot_delete_le (H := H) e
      have hcnt : batchInsertCount (.delete e :: U) = batchInsertCount U := by
        simp [batchInsertCount]
      have henc : H.updateEnc (.delete e) = 1 := rfl
      rw [hcnt, henc]
      push_cast
      linarith
    | split v v' St Sh =>
      have hpot := degPot_split_le hV hu
      have hcnt : batchInsertCount (.split v v' St Sh :: U) = batchInsertCount U := by
        simp [batchInsertCount]
      rw [hcnt]
      linarith
    | insert e a b =>
      have hpot := degPot_insert_le hV hu hm0
      have hcnt : batchInsertCount (.insert e a b :: U) = batchInsertCount U + 1 := by
        simp [batchInsertCount]
      have henc : H.updateEnc (.insert e a b) = 1 := rfl
      rw [hcnt, henc]
      push_cast
      linarith

end

end MinCostFlow.DynSpanner
