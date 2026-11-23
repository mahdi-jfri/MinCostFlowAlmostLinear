module

public import MinCostFlow.SparseCore.CanonCoreSpec
public import MinCostFlow.SparseCore.BundleTreeCore
import MinCostFlow.DynSpanner.ComplexitySum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Split-only Lemma 2.1 and rotation-free `canonCoreBatch` helpers

Reusable graph, rotation, and encoding helpers for the single-step bounds on `stepBundleTree`:
1. **Split-only Lemma 2.1 (`batchEnc_splits_le_real`)**: a valid split-only batch `U_sp` on a valid
   graph `S` never increases `S.m`, so its encoding size satisfies
   `(S.batchEnc U_sp : ℝ) ≤ 4 * S.m * log(2 * S.m + 2) + U_sp.length`.
2. **Rotation-free `canonCoreBatch` validity (`canonCoreBatch_props_of_valid`)**: any valid batch
   `U` on a valid graph `G` is a `RotationBatch β` between `sortedRotation G` and
   `sortedRotation (G.applyBatch U)` for `β := max 2 (2 * (G.m + U.length))`, so
   `orderedCore_canonCoreBatch` supplies validity, `batchSplitCount = (cs'.RF.R \ cs.RF.R).card`,
   and `batchDeletes ⊆ batchDeletes U` without requiring a `RotationBatch 2` on `U`.
3. **Batch encoding and graph-size helpers**: `batchEnc_map_delete`, `batchEnc_map_insert`,
   `applyBatch_map_delete_props`, `applyBatch_delOrSplit_E_sub`, `m_applyBatch_le_add_len`,
   and logarithmic comparisons against `bundleLogFactor M N`.
-/

public section

namespace MinCostFlow.Final.DryRun

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.Bundle

/-! ## 1. Split-only Lemma 2.1 and delete/insert batch encoding -/

private noncomputable def phiTermUS (d : ℕ) : ℝ :=
  (d : ℝ) * Real.log (d : ℝ)

private noncomputable def degPotentialUS (G : MGraph) : ℝ :=
  ∑ v ∈ G.V, phiTermUS (G.deg v)

private lemma log_two_gt_half_us : (1 / 2 : ℝ) < Real.log 2 := by
  have h1 : (1 / 2 : ℝ) < Real.exp (-(1 / 2 : ℝ)) := by
    have := Real.add_one_lt_exp (show -(1 / 2 : ℝ) ≠ 0 by norm_num)
    linarith
  have h2 : Real.exp (1 / 2 : ℝ) < 2 := by
    rw [Real.exp_neg] at h1
    have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    rw [lt_inv_comm₀ (by norm_num) hpos] at h1
    linarith
  rw [← Real.log_exp (1 / 2 : ℝ)]
  exact Real.log_lt_log (Real.exp_pos _) h2

private lemma log_two_lt_one_us : Real.log 2 < 1 := by
  have h : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
    linarith
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (by norm_num) h

private lemma phiTermUS_nonneg (d : ℕ) : 0 ≤ phiTermUS d := by
  cases d with
  | zero => simp [phiTermUS]
  | succ n =>
    exact mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by exact_mod_cast Nat.succ_pos n))

private lemma degPotentialUS_nonneg (G : MGraph) : 0 ≤ degPotentialUS G :=
  Finset.sum_nonneg fun v _ => phiTermUS_nonneg (G.deg v)

private lemma phiTermUS_split_drop_of_le {a b : ℕ} (hab : a ≤ b) :
    Real.log 2 * (a : ℝ) ≤ phiTermUS (a + b) - phiTermUS a - phiTermUS b := by
  cases a with
  | zero => simp [phiTermUS]
  | succ m =>
    have ha_pos : (0 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast lt_of_lt_of_le (Nat.succ_pos m) hab
    have hab_pos : (0 : ℝ) < ((m + 1 + b : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + 1 + b)
    have hlog2 : Real.log 2 ≤ Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ) := by
      rw [← Real.log_div hab_pos.ne' ha_pos.ne']
      refine Real.log_le_log (by norm_num) ?_
      rw [le_div_iff₀ ha_pos]
      have hle : (2 * ((m + 1 : ℕ) : ℝ)) ≤ ((m + 1 + b : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 * (m + 1) ≤ m + 1 + b)
      linarith
    have hlogb : 0 ≤ Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log (b : ℝ) :=
      sub_nonneg.mpr (Real.log_le_log hb_pos (by exact_mod_cast (by omega : b ≤ m + 1 + b)))
    have h1 : Real.log 2 * ((m + 1 : ℕ) : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) * (Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ)) := by
      calc Real.log 2 * ((m + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * Real.log 2 := mul_comm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog2 ha_pos.le
    have h2 : 0 ≤ (b : ℝ) * (Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log (b : ℝ)) :=
      mul_nonneg hb_pos.le hlogb
    have hcalc : phiTermUS (m + 1 + b) - phiTermUS (m + 1) - phiTermUS b =
        ((m + 1 : ℕ) : ℝ) * (Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log ((m + 1 : ℕ) : ℝ)) +
        (b : ℝ) * (Real.log ((m + 1 + b : ℕ) : ℝ) - Real.log (b : ℝ)) := by
      simp only [phiTermUS, Nat.cast_add]; ring
    linarith

private lemma phiTermUS_split_drop (a b : ℕ) :
    Real.log 2 * ((min a b : ℕ) : ℝ) ≤ phiTermUS (a + b) - phiTermUS a - phiTermUS b := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab]; exact phiTermUS_split_drop_of_le hab
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    rw [min_eq_right hba, add_comm a b]
    linarith [phiTermUS_split_drop_of_le hba]

private lemma sum_deg_eq_two_mul_m_us {G : MGraph} (hG : G.IsValid) :
    ∑ v ∈ G.V, G.deg v = 2 * G.m := by
  simp only [MGraph.deg, Finset.sum_add_distrib, MGraph.m]
  have hpart : ∀ (f : ℕ → ℕ), (∀ e ∈ G.E, f e ∈ G.V) →
      ∑ v ∈ G.V, (G.E.filter (fun e => f e = v)).card = G.E.card := by
    intro f hf
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun e he => ?_).trans (Finset.card_eq_sum_ones G.E).symm
    rw [Finset.sum_eq_single (f e)]
    · simp
    · intro v _ hne; simp [Ne.symm hne]
    · intro hnot; exact absurd (hf e he) hnot
  rw [hpart G.tail (fun e he => (hG e he).1), hpart G.head (fun e he => (hG e he).2)]
  omega

private lemma deg_le_two_mul_m_us (G : MGraph) (v : ℕ) : G.deg v ≤ 2 * G.m := by
  simp only [MGraph.deg, MGraph.m]
  have h1 := Finset.card_filter_le G.E (fun e => G.tail e = v)
  have h2 := Finset.card_filter_le G.E (fun e => G.head e = v)
  omega

private lemma degPotentialUS_le {G : MGraph} (hG : G.IsValid) :
    degPotentialUS G ≤ 2 * (G.m : ℝ) * Real.log (2 * (G.m : ℝ) + 2) := by
  unfold degPotentialUS
  have hterm : ∀ v ∈ G.V, phiTermUS (G.deg v) ≤ (G.deg v : ℝ) * Real.log (2 * (G.m : ℝ) + 2) := by
    intro v _
    unfold phiTermUS
    cases hd : G.deg v with
    | zero => simp
    | succ d =>
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine Real.log_le_log (by exact_mod_cast Nat.succ_pos d) ?_
      have hle : d + 1 ≤ 2 * G.m := hd ▸ deg_le_two_mul_m_us G v
      have hleR : ((d + 1 : ℕ) : ℝ) ≤ 2 * (G.m : ℝ) := by exact_mod_cast hle
      linarith
  calc ∑ v ∈ G.V, phiTermUS (G.deg v)
      ≤ ∑ v ∈ G.V, (G.deg v : ℝ) * Real.log (2 * (G.m : ℝ) + 2) := Finset.sum_le_sum hterm
    _ = (∑ v ∈ G.V, (G.deg v : ℝ)) * Real.log (2 * (G.m : ℝ) + 2) := (Finset.sum_mul _ _ _).symm
    _ = 2 * (G.m : ℝ) * Real.log (2 * (G.m : ℝ) + 2) := by
        have hsum : (∑ v ∈ G.V, (G.deg v : ℝ)) = 2 * (G.m : ℝ) := by
          exact_mod_cast sum_deg_eq_two_mul_m_us hG
        rw [hsum]

private lemma deg_split_eq_of_mem_ne_us {G : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    (hv' : v' ∉ G.V) {w : ℕ} (hw : w ∈ G.V) (hwv : w ≠ v) :
    (G.applyUpdate (.split v v' St Sh)).deg w = G.deg w := by
  have hwv' : w ≠ v' := fun h => hv' (h ▸ hw)
  let G' := G.applyUpdate (.split v v' St Sh)
  change G'.deg w = G.deg w
  simp only [MGraph.deg]
  have hpart : ∀ (S : Finset ℕ) (f f' : ℕ → ℕ),
      (∀ e, f' e = if e ∈ S ∧ f e = v then v' else f e) →
      (G'.E.filter (fun e => f' e = w)).card = (G.E.filter (fun e => f e = w)).card := by
    intro S f f' hf'
    refine congrArg Finset.card (Finset.ext fun e => ?_)
    have hGE : G'.E = G.E := rfl
    simp only [Finset.mem_filter, hGE, hf']
    constructor
    · rintro ⟨he, ht⟩; split_ifs at ht
      · exact absurd ht.symm hwv'
      · exact ⟨he, ht⟩
    · rintro ⟨he, ht⟩; refine ⟨he, ?_⟩; split_ifs with hc
      · exact absurd (ht.symm.trans hc.2) hwv
      · exact ht
  rw [hpart St G.tail G'.tail (fun _ => rfl), hpart Sh G.head G'.head (fun _ => rfl)]

private lemma deg_split_add_us {G : MGraph} (hG : G.IsValid) {v v' : ℕ} {St Sh : Finset ℕ}
    (hv : v ∈ G.V) (hv' : v' ∉ G.V) :
    (G.applyUpdate (.split v v' St Sh)).deg v + (G.applyUpdate (.split v v' St Sh)).deg v' =
      G.deg v := by
  have hne : v ≠ v' := fun h => hv' (h ▸ hv)
  let G' := G.applyUpdate (.split v v' St Sh)
  have hpart : ∀ (S : Finset ℕ) (f f' : ℕ → ℕ),
      (∀ e, f' e = if e ∈ S ∧ f e = v then v' else f e) →
      (∀ e ∈ G.E, f e ∈ G.V) →
      (G.E.filter (fun e => f' e = v)).card + (G.E.filter (fun e => f' e = v')).card =
        (G.E.filter (fun e => f e = v)).card := by
    intro S f f' hf' hfV
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext e; simp only [Finset.mem_union, Finset.mem_filter]; rw [hf' e]
      constructor
      · rintro (⟨he, h⟩ | ⟨he, h⟩)
        · split_ifs at h
          · exact absurd h hne.symm
          · exact ⟨he, h⟩
        · split_ifs at h with hc
          · exact ⟨he, hc.2⟩
          · exact absurd (h ▸ hfV e he) hv'
      · rintro ⟨he, h⟩; by_cases heS : e ∈ S
        · exact Or.inr ⟨he, by simp [heS, h]⟩
        · exact Or.inl ⟨he, by simp [heS, h]⟩
    · rw [Finset.disjoint_left]; intro e h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have ht := hpart St G.tail G'.tail (fun _ => rfl) (fun e he => (hG e he).1)
  have hh := hpart Sh G.head G'.head (fun _ => rfl) (fun e he => (hG e he).2)
  change (G'.E.filter (fun e => G'.tail e = v)).card +
      (G'.E.filter (fun e => G'.head e = v)).card +
      ((G'.E.filter (fun e => G'.tail e = v')).card +
        (G'.E.filter (fun e => G'.head e = v')).card) =
      (G.E.filter (fun e => G.tail e = v)).card + (G.E.filter (fun e => G.head e = v)).card
  have hGE : G'.E = G.E := rfl
  rw [hGE]; omega

private lemma split_potential_step {G : MGraph} (hG : G.IsValid) {v v' : ℕ} {St Sh : Finset ℕ}
    (hu : G.UpdateIsValid (.split v v' St Sh)) :
    Real.log 2 * ((G.updateEnc (.split v v' St Sh) : ℝ) - 1) ≤
      degPotentialUS G - degPotentialUS (G.applyUpdate (.split v v' St Sh)) := by
  rcases hu with ⟨hv, hv', _, _⟩
  let G' := G.applyUpdate (.split v v' St Sh)
  have hdrop : Real.log 2 * ((min (G'.deg v) (G'.deg v') : ℕ) : ℝ) ≤
      phiTermUS (G.deg v) - phiTermUS (G'.deg v) - phiTermUS (G'.deg v') := by
    rw [← deg_split_add_us (St := St) (Sh := Sh) hG hv hv']
    exact phiTermUS_split_drop (G'.deg v) (G'.deg v')
  have hpot_eq : degPotentialUS G - degPotentialUS G' =
      phiTermUS (G.deg v) - phiTermUS (G'.deg v) - phiTermUS (G'.deg v') := by
    unfold degPotentialUS
    have hG'V : G'.V = insert v' G.V := rfl
    rw [hG'V, Finset.sum_insert hv', ← Finset.add_sum_erase G.V _ hv,
      ← Finset.add_sum_erase G.V (fun w => phiTermUS (G'.deg w)) hv]
    have hrest : ∑ w ∈ G.V.erase v, phiTermUS (G'.deg w) = ∑ w ∈ G.V.erase v, phiTermUS (G.deg w) :=
      Finset.sum_congr rfl fun w hw => by
        obtain ⟨hwv, hwV⟩ := Finset.mem_erase.mp hw
        rw [deg_split_eq_of_mem_ne_us hv' hwV hwv]
    rw [hrest]; ring
  have henc : (G.updateEnc (.split v v' St Sh) : ℝ) - 1 =
      ((min (G'.deg v) (G'.deg v') : ℕ) : ℝ) := by
    simp only [MGraph.updateEnc, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]; rfl
  rw [henc, hpot_eq]
  exact hdrop

/-- Split-only Lemma 2.1: a valid batch of splits on a valid graph `S` never increases `S.m`,
so its encoding size is bounded without any `log |U|` factor. -/
theorem batchEnc_splits_le_real {S : MGraph} (hS : S.IsValid) {U : List Update}
    (hU : S.BatchIsValid U) (hsp : ∀ u ∈ U, isSplit u = true) :
    (S.batchEnc U : ℝ) ≤ 4 * (S.m : ℝ) * Real.log (2 * (S.m : ℝ) + 2) + (U.length : ℝ) := by
  have htele : ∀ (xs : List Update) (G : MGraph),
      G.IsValid → G.BatchIsValid xs → (∀ u ∈ xs, isSplit u = true) →
      Real.log 2 * ((G.batchEnc xs : ℝ) - (xs.length : ℝ)) ≤
        degPotentialUS G - degPotentialUS (G.applyBatch xs) := by
    intro xs
    induction xs with
    | nil => intro G _ _ _; simp [MGraph.batchEnc, MGraph.applyBatch]
    | cons u rest ih =>
      intro G hG ⟨hu, hrest⟩ hsp'
      have hu_sp := hsp' u List.mem_cons_self
      cases u with
      | insert _ _ _ => simp [isSplit] at hu_sp
      | delete _ => simp [isSplit] at hu_sp
      | split v v' St Sh =>
        have hstep := split_potential_step hG hu
        have hG1 : (G.applyUpdate (.split v v' St Sh)).IsValid := applyUpdate_isValid hG hu
        have hih := ih (G.applyUpdate (.split v v' St Sh)) hG1 hrest
          (fun op hop => hsp' op (List.mem_cons_of_mem _ hop))
        have hcast : ((G.batchEnc (.split v v' St Sh :: rest) : ℝ) -
            ((.split v v' St Sh :: rest).length : ℝ)) =
            ((G.updateEnc (.split v v' St Sh) : ℝ) - 1) +
            (((G.applyUpdate (.split v v' St Sh)).batchEnc rest : ℝ) - (rest.length : ℝ)) := by
          simp only [MGraph.batchEnc, List.length_cons, Nat.cast_add, Nat.cast_one]; ring
        rw [hcast, mul_add]
        have hEq : G.applyBatch (.split v v' St Sh :: rest) =
            (G.applyUpdate (.split v v' St Sh)).applyBatch rest := rfl
        rw [hEq]
        linarith
  have h1 := htele U S hS hU hsp
  have h2 := degPotentialUS_nonneg (S.applyBatch U)
  have h3 := degPotentialUS_le hS
  have hlog2 := log_two_gt_half_us
  have hge0 : 0 ≤ (S.batchEnc U : ℝ) - (U.length : ℝ) := by
    have hlen_le : ∀ (xs : List Update) (G : MGraph), xs.length ≤ G.batchEnc xs := by
      intro xs
      induction xs with
      | nil => intro _; simp [MGraph.batchEnc]
      | cons u rest ih =>
        intro G
        simp only [MGraph.batchEnc, List.length_cons]
        have hpos : 1 ≤ G.updateEnc u := by cases u <;> simp [MGraph.updateEnc]
        have := ih (G.applyUpdate u)
        omega
    have : (U.length : ℝ) ≤ (S.batchEnc U : ℝ) := by exact_mod_cast hlen_le U S
    linarith
  have hhalf : (1 / 2 : ℝ) * ((S.batchEnc U : ℝ) - (U.length : ℝ)) ≤
      Real.log 2 * ((S.batchEnc U : ℝ) - (U.length : ℝ)) :=
    mul_le_mul_of_nonneg_right hlog2.le hge0
  linarith

/-- Encoding size of a list of deletions equals its length. -/
theorem batchEnc_map_delete (G : MGraph) (xs : List ℕ) :
    G.batchEnc (xs.map Update.delete) = xs.length := by
  induction xs generalizing G with
  | nil => simp [MGraph.batchEnc]
  | cons x xs ih =>
    simp only [List.map_cons, MGraph.batchEnc, MGraph.updateEnc, List.length_cons,
      ih (G.applyUpdate (.delete x))]
    omega

/-- Encoding size of a list of insertions equals its length. -/
theorem batchEnc_map_insert (G : MGraph) (xs : List ℕ) (t h : ℕ → ℕ) :
    G.batchEnc (xs.map fun e => Update.insert e (t e) (h e)) = xs.length := by
  induction xs generalizing G with
  | nil => simp [MGraph.batchEnc]
  | cons x xs ih =>
    simp only [List.map_cons, MGraph.batchEnc, MGraph.updateEnc, List.length_cons,
      ih (G.applyUpdate (.insert x (t x) (h x)))]
    omega

/-! ## 2. Rotation-free `canonCoreBatch` validity via `sortedRotation` -/

private lemma pathBdry_le_length {α : Type*} (p : α → Bool) (a b : α) (xs : List α) :
    pathBdry p a xs b ≤ xs.length + 1 := by
  induction xs generalizing a with
  | nil => simp only [pathBdry, List.length_nil]; split_ifs <;> omega
  | cons x xs ih =>
    simp only [pathBdry, List.length_cons]
    have := ih x
    split_ifs <;> omega

private lemma cycBdry_le_length {α : Type*} (p : α → Bool) (xs : List α) :
    cycBdry p xs ≤ xs.length := by
  cases xs with
  | nil => simp [cycBdry]
  | cons x xs =>
    simpa [cycBdry] using pathBdry_le_length p x x xs

private lemma sortedEnds_length_le (G : MGraph) (v : ℕ) :
    (sortedEnds G v).length ≤ 2 * G.m := by
  unfold sortedEnds
  rw [Finset.length_sort]
  have h1 : ((G.E ×ˢ ({true, false} : Finset Bool)).filter fun x => G.src x = v).card ≤
      (G.E ×ˢ ({true, false} : Finset Bool)).card := Finset.card_filter_le _ _
  rw [Finset.card_product] at h1
  have h2 : ({true, false} : Finset Bool).card = 2 := by decide
  rw [h2, Nat.mul_comm] at h1
  exact h1

private lemma sortedEnds_eq_of_mem {xs ys : List End} (hx : xs.Nodup) (hy : ys.Nodup)
    (hsx : xs.Pairwise endLE) (hsy : ys.Pairwise endLE)
    (hm : ∀ x, x ∈ xs ↔ x ∈ ys) : xs = ys :=
  ((List.perm_ext_iff_of_nodup hx hy).mpr hm).eq_of_pairwise' hsx hsy

private lemma sortedRotation_step_any {G : MGraph} (hG : G.IsValid) {u : Update}
    (hu : G.UpdateIsValid u) {β : ℕ} (hβ : 2 * G.m ≤ β) :
    RotationStep β u (sortedRotation G) (sortedRotation (G.applyUpdate u)) := by
  cases u with
  | insert e a b =>
    intro v
    change ((sortedEnds (G.applyUpdate (.insert e a b)) v).filter
      (fun x => x.1 != e)).IsRotated (sortedEnds G v)
    suffices h : (sortedEnds (G.applyUpdate (.insert e a b)) v).filter (fun x => x.1 != e) =
        sortedEnds G v by rw [h]
    refine sortedEnds_eq_of_mem
      ((sortedRotation _).nodup v |>.filter _) ((sortedRotation G).nodup v)
      ((Finset.pairwise_sort _ _).filter _) (Finset.pairwise_sort _ _) fun x => ?_
    have he' := hu.1
    by_cases h : x.1 = e
    · simp [List.mem_filter, mem_sortedEnds, h, he']
    · rcases x with ⟨i, side⟩
      cases side <;>
        simp [List.mem_filter, mem_sortedEnds, MGraph.applyUpdate, MGraph.src, h,
          Function.update_of_ne]
  | delete e =>
    intro v
    change (sortedEnds (G.applyUpdate (.delete e)) v).IsRotated
      ((sortedEnds G v).filter (fun x => x.1 != e))
    suffices h : sortedEnds (G.applyUpdate (.delete e)) v =
        (sortedEnds G v).filter (fun x => x.1 != e) by rw [h]
    refine sortedEnds_eq_of_mem
      ((sortedRotation _).nodup v) ((sortedRotation G).nodup v |>.filter _)
      (Finset.pairwise_sort _ _) ((Finset.pairwise_sort _ _).filter _) fun x => ?_
    simp only [List.mem_filter, mem_sortedEnds, MGraph.applyUpdate, MGraph.src,
      Finset.mem_erase, bne_iff_ne]
    exact ⟨fun ⟨⟨hn, he⟩, hs⟩ => ⟨⟨he, hs⟩, hn⟩, fun ⟨⟨he, hs⟩, hn⟩ => ⟨⟨hn, he⟩, hs⟩⟩
  | split v v' St Sh =>
    rcases hu with ⟨hv, hv', _, _⟩
    have hvv' : v ≠ v' := fun h => hv' (h ▸ hv)
    have hsrc_ne_v' : ∀ x : End, x.1 ∈ G.E → G.src x ≠ v' := by
      intro x hx hEq
      have hV : G.src x ∈ G.V := by
        rcases x with ⟨e, side⟩
        cases side
        · exact (hG e hx).2
        · exact (hG e hx).1
      exact hv' (hEq ▸ hV)
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (sortedEnds (G.applyUpdate (.split v v' St Sh)) v).IsRotated
        ((sortedEnds G v).filter fun x => !(splitEnds St Sh x))
      suffices h : sortedEnds (G.applyUpdate (.split v v' St Sh)) v =
          (sortedEnds G v).filter fun x => !(splitEnds St Sh x) by rw [h]
      refine sortedEnds_eq_of_mem
        ((sortedRotation _).nodup v) ((sortedRotation G).nodup v |>.filter _)
        (Finset.pairwise_sort _ _) ((Finset.pairwise_sort _ _).filter _) fun x => ?_
      simp only [List.mem_filter, mem_sortedEnds, src_applySplit]
      change x.1 ∈ G.E ∧ (if G.src x = v ∧ splitEnds St Sh x = true then v' else G.src x) = v ↔ _
      constructor
      · rintro ⟨hx, hsrc⟩
        split_ifs at hsrc with hc
        · exact absurd hsrc.symm hvv'
        · refine ⟨⟨hx, hsrc⟩, ?_⟩
          cases hsp : splitEnds St Sh x with
          | false => rfl
          | true => exact absurd ⟨hsrc, hsp⟩ hc
      · rintro ⟨⟨hx, hsrc⟩, hnot⟩
        have hfalse : splitEnds St Sh x = false := by
          cases hsp : splitEnds St Sh x <;> simp [hsp] at hnot ⊢
        exact ⟨hx, by simp [hsrc, hfalse]⟩
    · change (sortedEnds (G.applyUpdate (.split v v' St Sh)) v').IsRotated
        ((sortedEnds G v).filter (splitEnds St Sh))
      suffices h : sortedEnds (G.applyUpdate (.split v v' St Sh)) v' =
          (sortedEnds G v).filter (splitEnds St Sh) by rw [h]
      refine sortedEnds_eq_of_mem
        ((sortedRotation _).nodup v') ((sortedRotation G).nodup v |>.filter _)
        (Finset.pairwise_sort _ _) ((Finset.pairwise_sort _ _).filter _) fun x => ?_
      simp only [List.mem_filter, mem_sortedEnds, src_applySplit]
      change x.1 ∈ G.E ∧ (if G.src x = v ∧ splitEnds St Sh x = true then v' else G.src x) = v' ↔ _
      constructor
      · rintro ⟨hx, hsrc⟩
        split_ifs at hsrc with hc
        · exact ⟨⟨hx, hc.1⟩, hc.2⟩
        · exact absurd hsrc (hsrc_ne_v' x hx)
      · rintro ⟨⟨hx, hsrc⟩, hmov⟩
        exact ⟨hx, by simp [hsrc, hmov]⟩
    · exact (cycBdry_le_length _ _).trans ((sortedEnds_length_le G v).trans hβ)
    · intro w hwv hwv'
      change (sortedEnds (G.applyUpdate (.split v v' St Sh)) w).IsRotated (sortedEnds G w)
      suffices h : sortedEnds (G.applyUpdate (.split v v' St Sh)) w = sortedEnds G w by rw [h]
      refine sortedEnds_eq_of_mem
        ((sortedRotation _).nodup w) ((sortedRotation G).nodup w)
        (Finset.pairwise_sort _ _) (Finset.pairwise_sort _ _) fun x => ?_
      simp only [mem_sortedEnds, src_applySplit]
      change x.1 ∈ G.E ∧ (if G.src x = v ∧ splitEnds St Sh x = true then v' else G.src x) = w ↔ _
      constructor
      · rintro ⟨hx, hsrc⟩
        split_ifs at hsrc with hc
        · exact absurd hsrc.symm hwv'
        · exact ⟨hx, hsrc⟩
      · rintro ⟨hx, hsrc⟩
        refine ⟨hx, ?_⟩
        split_ifs with hc
        · exact absurd (hsrc.symm.trans hc.1) hwv
        · exact hsrc

/-- One update increases the edge count by at most `1`. -/
theorem m_applyUpdate_le_succ (G : MGraph) (u : Update) :
    (G.applyUpdate u).m ≤ G.m + 1 := by
  cases u with
  | insert e a b => exact Finset.card_insert_le _ _
  | delete e => exact Nat.le_trans Finset.card_erase_le (Nat.le_succ _)
  | split _ _ _ _ => simp [MGraph.applyUpdate, MGraph.m]

/-- Applying a batch `U` increases the edge count by at most `U.length`. -/
theorem m_applyBatch_le_add_len (G : MGraph) (U : List Update) :
    (G.applyBatch U).m ≤ G.m + U.length := by
  induction U generalizing G with
  | nil => simp [MGraph.applyBatch]
  | cons u rest ih =>
    have h1 := m_applyUpdate_le_succ G u
    have h2 := ih (G.applyUpdate u)
    change ((G.applyUpdate u).applyBatch rest).m ≤ G.m + (rest.length + 1)
    omega

/-- Any valid batch on a valid graph `G` is a `RotationBatch β` between `sortedRotation G` and
`sortedRotation (G.applyBatch U)` for `β := max 2 (2 * (G.m + U.length))`. -/
theorem exists_rotationBatch_of_valid {G : MGraph} (hG : G.IsValid) {U : List Update}
    (hU : G.BatchIsValid U) :
    ∃ β ≥ 2, ∃ (ρ : Rotation G) (σ : Rotation (G.applyBatch U)), RotationBatch β U ρ σ := by
  have haux : ∀ (xs : List Update) (H : MGraph) (β : ℕ),
      H.IsValid → H.BatchIsValid xs → 2 * (H.m + xs.length) ≤ β →
      RotationBatch β xs (sortedRotation H) (sortedRotation (H.applyBatch xs)) := by
    intro xs
    induction xs with
    | nil => intro H _ _ _ _; exact .refl _
    | cons u rest ih =>
      intro H β hH ⟨hu, hrest⟩ hβ
      have hH1 : (H.applyUpdate u).IsValid := applyUpdate_isValid hH hu
      have hm1 : (H.applyUpdate u).m ≤ H.m + 1 := m_applyUpdate_le_succ H u
      have hstep := sortedRotation_step_any hH hu (β := β) (by simp at hβ; omega)
      have htail := ih (H.applyUpdate u) β hH1 hrest (by simp at hβ; omega)
      exact .cons hstep htail
  refine ⟨max 2 (2 * (G.m + U.length)), le_max_left _ _,
    sortedRotation G, sortedRotation (G.applyBatch U),
    haux U G _ hG hU (le_max_right _ _)⟩

/-- Rotation-free specification of `canonCoreBatch`: validity on the core graph, exact split count
`(cs'.RF.R \ cs.RF.R).card`, and deletions contained in `batchDeletes U`. -/
theorem canonCoreBatch_props_of_valid {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    (coreGraph cs.G cs.lsf).BatchIsValid (canonCoreBatch cs U) ∧
    batchSplitCount (canonCoreBatch cs U) = ((compLSFBatch cs U).RF.R \ cs.RF.R).card ∧
    batchDeletes (canonCoreBatch cs U) ⊆ batchDeletes U := by
  obtain ⟨β, hβ, ρ, σ, hrot⟩ := exists_rotationBatch_of_valid hI.hG_val hU
  obtain ⟨_, _, hOCB, hsp, _, hdelSub⟩ :=
    orderedCore_canonCoreBatch (C_lsst := C_lsst) (ℓ₀ := ℓ₀) hrot hβ hU cs rfl hI
  exact ⟨hOCB.1, hsp, hdelSub⟩

/-! ## 3. Batch deletion, `delOrSplit`, and log-factor helpers -/

/-- A batch of deletions and splits never adds edges. -/
theorem applyBatch_delOrSplit_E_sub {G : MGraph} {us : List Update}
    (hds : ∀ u ∈ us, isDelOrSplit u) :
    (G.applyBatch us).E ⊆ G.E := by
  induction us generalizing G with
  | nil => exact Finset.Subset.rfl
  | cons u rest ih =>
    have hu := hds u List.mem_cons_self
    have hrest := fun op hop => hds op (List.mem_cons_of_mem _ hop)
    have h1 : (G.applyUpdate u).E ⊆ G.E := by
      cases u with
      | insert _ _ _ => exact hu.elim
      | delete _ => exact Finset.erase_subset _ _
      | split _ _ _ _ => exact Finset.Subset.rfl
    exact (ih hrest).trans h1

/-- Deleting a list of edges from a valid graph `S` keeps it valid, keeps `S.V`, removes `xs`,
and produces a subgraph of `S`. -/
theorem applyBatch_map_delete_props {S : MGraph} (hS : S.IsValid) (xs : List ℕ) :
    let S' := S.applyBatch (xs.map Update.delete)
    S'.IsValid ∧ S'.V = S.V ∧ S'.E = S.E \ xs.toFinset ∧ S.IsSubgraph S' := by
  induction xs generalizing S with
  | nil =>
    exact ⟨hS, rfl, by simp [MGraph.applyBatch],
      ⟨Finset.Subset.rfl, Finset.Subset.rfl, fun _ _ => ⟨rfl, rfl⟩⟩⟩
  | cons x rest ih =>
    let S1 := S.applyUpdate (.delete x)
    have hS1 : S1.IsValid := fun e he => hS e (Finset.erase_subset _ _ he)
    have hSub1 : S.IsSubgraph S1 :=
      ⟨Finset.Subset.rfl, Finset.erase_subset _ _, fun _ _ => ⟨rfl, rfl⟩⟩
    obtain ⟨hV, hVEq, hEEq, hSub2⟩ := ih hS1
    refine ⟨hV, hVEq, ?_,
      ⟨hSub2.1.trans hSub1.1, hSub2.2.1.trans hSub1.2.1, fun e he => hSub2.2.2 e he⟩⟩
    change (S1.applyBatch (rest.map Update.delete)).E = _
    rw [hEEq]
    ext e
    simp only [S1, MGraph.applyUpdate, Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons,
      Finset.mem_insert]
    tauto

/-- `log(x + 2) ≤ Nat.log 2 (M + N + 2) + 1` whenever `x ≤ M + N`. -/
theorem log_add_two_le_natLog (x M N : ℕ) (hx : x ≤ M + N) :
    Real.log ((x : ℝ) + 2) ≤ ((Nat.log 2 (M + N + 2) + 1 : ℕ) : ℝ) := by
  have hlt : M + N + 2 < 2 ^ (Nat.log 2 (M + N + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (M + N + 2)
  have hle : (x : ℝ) + 2 ≤ (2 : ℝ) ^ (Nat.log 2 (M + N + 2) + 1) := by
    have : x + 2 ≤ 2 ^ (Nat.log 2 (M + N + 2) + 1) := by omega
    exact_mod_cast this
  calc Real.log ((x : ℝ) + 2)
      ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 (M + N + 2) + 1)) :=
        Real.log_le_log (by positivity) hle
    _ = ((Nat.log 2 (M + N + 2) + 1 : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
    _ ≤ ((Nat.log 2 (M + N + 2) + 1 : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left log_two_lt_one_us.le (Nat.cast_nonneg _)
    _ = ((Nat.log 2 (M + N + 2) + 1 : ℕ) : ℝ) := mul_one _

/-- `log(2 m + 2) ≤ 2 * bundleLogFactor M N` whenever `m ≤ M`. -/
theorem log_two_mul_add_two_le_two_mul_bundleLog (m M N : ℕ) (hm : m ≤ M) :
    Real.log (2 * (m : ℝ) + 2) ≤ 2 * (bundleLogFactor M N : ℝ) := by
  have hlt : M + N + 2 < 2 ^ (Nat.log 2 (M + N + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) (M + N + 2)
  have hle : 2 * (m : ℝ) + 2 ≤ (2 : ℝ) ^ (Nat.log 2 (M + N + 2) + 2) := by
    have hpow : 2 ^ (Nat.log 2 (M + N + 2) + 2) = 2 * 2 ^ (Nat.log 2 (M + N + 2) + 1) := by
      rw [pow_succ]; ring
    have : 2 * m + 2 ≤ 2 ^ (Nat.log 2 (M + N + 2) + 2) := by omega
    exact_mod_cast this
  have hlog : Real.log (2 * (m : ℝ) + 2) ≤ ((Nat.log 2 (M + N + 2) + 2 : ℕ) : ℝ) := by
    calc Real.log (2 * (m : ℝ) + 2)
        ≤ Real.log ((2 : ℝ) ^ (Nat.log 2 (M + N + 2) + 2)) :=
          Real.log_le_log (by positivity) hle
      _ = ((Nat.log 2 (M + N + 2) + 2 : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ ((Nat.log 2 (M + N + 2) + 2 : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left log_two_lt_one_us.le (Nat.cast_nonneg _)
      _ = ((Nat.log 2 (M + N + 2) + 2 : ℕ) : ℝ) := mul_one _
  have hnat : Nat.log 2 (M + N + 2) + 2 ≤ 2 * bundleLogFactor M N := by
    unfold bundleLogFactor
    have hpos : 1 ≤ Nat.log 2 (M + N + 2) + 1 := Nat.succ_pos _
    nlinarith
  exact hlog.trans (by exact_mod_cast hnat)

end MinCostFlow.Final.DryRun
