module

public import MinCostFlow.DynSpanner.Walks
public import MinCostFlow.SparseCore.CoreModel
public import MinCostFlow.SparseCore.MWU

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Power-of-two length bucketing, circulation transfer, and vertex-split quotient graphs

This file provides the structural ingredients of `[chen2022maximum]` Algorithm 5 (`algo:dynasparsecore`)
used to prove Lemma 5.17 (`MinCostFlow/SparseCore/SplitSpanner.lean`, `Lemma517.lean`):

1. Power-of-two length buckets `bucketOf` (`Int.floor (Real.log x / Real.log 2)`) and proof that
   matching buckets imply `Chain.approx2`.
2. Quotient graph projection `projGraph`, walk projection `isWalk_projGraph`, `econg_le_vcong`, and
   exact circulation / valid-pair preservation (`isCirculation_passCoreC`,
   `isCirculation_passSparseCoreC`, `isValidPair_passCore`, `isValidPair_passSparseCore`).
3. Initial vertex-split core graph `tildeC0Base` (splitting each `v ∈ S₀.R` to even vertex `2 * v`
   and each `v ∈ W \ S₀.R` to odd vertex `2 * Nat.pair (S₀.RF.root v) (pieceMap S₀ v) + 1`),
   proving `tildeV0_rootPieceInv`, `tildeC0Base_V_card_le`, and `tildeC0Base_maxDeg_le`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 1. Power-of-two length bucketing -/

/-- Power-of-two length bucket index `⌊log₂ x⌋`. -/
noncomputable def bucketOf (x : ℝ) : ℤ :=
  Int.floor (Real.log x / Real.log 2)

lemma approx2_of_bucketOf_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hEq : bucketOf a = bucketOf b) : approx2 a b := by
  refine ⟨ha, hb, ?_, ?_⟩
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have ha1 : (bucketOf a : ℝ) ≤ Real.log a / Real.log 2 := Int.floor_le _
    have hb2 : Real.log b / Real.log 2 < (bucketOf a : ℝ) + 1 := by
      rw [hEq]; exact Int.lt_floor_add_one _
    have hdiff1 : Real.log b / Real.log 2 - 1 < Real.log a / Real.log 2 := by linarith
    have hmul1 : Real.log b - Real.log 2 < Real.log a := by
      have h := (mul_lt_mul_iff_of_pos_right hlog2).mpr hdiff1
      simp only [sub_mul, div_mul_cancel₀ _ hlog2.ne', one_mul] at h
      exact h
    have hexp1 : Real.exp (Real.log b - Real.log 2) ≤ Real.exp (Real.log a) :=
      (Real.exp_lt_exp.mpr hmul1).le
    rw [Real.exp_sub, Real.exp_log ha, Real.exp_log hb, Real.exp_log (by norm_num)] at hexp1
    linarith
  · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have ha2 : Real.log a / Real.log 2 < (bucketOf a : ℝ) + 1 := Int.lt_floor_add_one _
    have hb1 : (bucketOf a : ℝ) ≤ Real.log b / Real.log 2 := by
      rw [hEq]; exact Int.floor_le _
    have hdiff2 : Real.log a / Real.log 2 < Real.log b / Real.log 2 + 1 := by linarith
    have hmul2 : Real.log a < Real.log b + Real.log 2 := by
      have h := (mul_lt_mul_iff_of_pos_right hlog2).mpr hdiff2
      simp only [add_mul, div_mul_cancel₀ _ hlog2.ne', one_mul] at h
      exact h
    have hexp2 : Real.exp (Real.log a) ≤ Real.exp (Real.log b + Real.log 2) :=
      (Real.exp_lt_exp.mpr hmul2).le
    rw [Real.exp_add, Real.exp_log ha, Real.exp_log hb, Real.exp_log (by norm_num)] at hexp2
    linarith

/-! ## 2. Graph projection, congestion, and circulation transfer -/

/-- Project a multigraph onto vertex set `V_R` via vertex map `proj`. -/
def projGraph (V_R : Finset ℕ) (proj : ℕ → ℕ) (H : MGraph) : MGraph where
  V := V_R
  E := H.E
  tail e := proj (H.tail e)
  head e := proj (H.head e)

lemma projGraph_isWalk {V_R : Finset ℕ} {proj : ℕ → ℕ} {H : MGraph}
    {u v : ℕ} {P : List (ℕ × Bool)} (hW : H.IsWalk u v P) :
    (projGraph V_R proj H).IsWalk (proj u) (proj v) P := by
  induction hW with
  | nil u => exact .nil (proj u)
  | cons he hsrc _ ih =>
    rename_i u' v' x P' _
    refine .cons he ?_ ?_
    · cases xb : x.2 <;>
        simp only [MGraph.src, projGraph, xb, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢ <;>
        exact congrArg proj hsrc
    · have hdst : (projGraph V_R proj H).dst x = proj (H.dst x) := by
        cases xb : x.2 <;> simp [MGraph.dst, projGraph, xb]
      rw [hdst]
      exact ih

lemma mem_walkEdges_tail_mem_walkVertices {H : MGraph} {u v e' : ℕ} {P : List (ℕ × Bool)}
    (hW : H.IsWalk u v P) (he' : e' ∈ walkEdges P) :
    H.tail e' ∈ H.walkVertices u P := by
  induction hW with
  | nil _ => simp [walkEdges] at he'
  | cons he hsrc _ ih =>
    rename_i u' v' x P' _
    simp only [walkEdges, List.map_cons, List.toFinset_cons, Finset.mem_insert] at he'
    simp only [MGraph.walkVertices, List.map_cons, List.mem_cons]
    rcases he' with rfl | he'
    · rcases x with ⟨e₀, b₀⟩
      cases b₀
      · right; left; simp [MGraph.dst]
      · left
        simp only [MGraph.src, ↓reduceIte] at hsrc
        exact hsrc
    · have hih := ih he'
      simp only [MGraph.walkVertices, List.mem_cons] at hih
      rcases hih with hdst | hmem
      · right; left; exact hdst
      · right; right; exact hmem

lemma econg_le_vcong {C H : MGraph} {emb : Embedding}
    (hH : H.IsValid) (hEmb : emb.IsEmbedding C H) :
    emb.econg C H (fun _ => 1) (fun _ => 1) ≤ emb.vcong C H (fun _ => 1) := by
  unfold Embedding.econg Embedding.vcong
  by_cases hE : H.E.Nonempty <;> by_cases hV : H.V.Nonempty <;>
    simp only [hE, hV, ↓reduceDIte]
  · rw [Finset.sup'_le_iff]
    intro e' he'
    have htailH : H.tail e' ∈ H.V := (hH e' he').1
    have hsub :
        (C.E.filter fun e => e' ∈ walkEdges (emb e)) ⊆
          (C.E.filter fun e => H.tail e' ∈ H.walkVertices (C.tail e) (emb e)) := by
      intro e he
      rw [Finset.mem_filter] at he ⊢
      exact ⟨he.1, mem_walkEdges_tail_mem_walkVertices (hEmb.2 e he.1) he.2⟩
    have hcard :
        (∑ e ∈ C.E with e' ∈ walkEdges (emb e), (1 : ℝ)) ≤
          emb.vcongAt C H (fun _ => 1) (H.tail e') := by
      dsimp only [Embedding.vcongAt]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast Finset.card_le_card hsub
    have hec : emb.econgAt C (fun _ => 1) (fun _ => 1) e' =
        (∑ e ∈ C.E with e' ∈ walkEdges (emb e), (1 : ℝ)) := by
      simp [Embedding.econgAt]
    rw [hec]
    exact le_trans hcard (Finset.le_sup' (emb.vcongAt C H (fun _ => 1)) htailH)
  · exfalso
    obtain ⟨e', he'⟩ := hE
    exact hV ⟨H.tail e', (hH e' he').1⟩
  · obtain ⟨v0, hv0⟩ := hV
    refine le_trans ?_ (Finset.le_sup' (emb.vcongAt C H (fun _ => 1)) hv0)
    dsimp only [Embedding.vcongAt]
    exact Finset.sum_nonneg fun _ _ => zero_le_one
  · exact le_rfl

lemma rootedForest_root_spec {RF : RootedForest} {G : MGraph}
    (hRF : RF.IsRootedSpanningForestOf G) {v : ℕ} (hv : v ∈ G.V) :
    RF.root v ∈ RF.R ∧ RF.F.Connected v (RF.root v) := by
  have hex := (hRF.2.2.2.1 v hv).exists
  simpa [RootedForest.root, hex] using Classical.choose_spec hex

lemma rootedForest_root_eq_of_mem_R {RF : RootedForest} {G : MGraph}
    (hRF : RF.IsRootedSpanningForestOf G) {r : ℕ} (hr : r ∈ RF.R) :
    RF.root r = r := by
  have hrV : r ∈ G.V := hRF.2.2.1 hr
  obtain ⟨r', _, huniq⟩ := hRF.2.2.2.1 r hrV
  have hr_spec := rootedForest_root_spec hRF hrV
  have hr_nil : r ∈ RF.R ∧ RF.F.Connected r r := ⟨hr, ⟨[], .nil r⟩⟩
  rw [huniq _ hr_spec, huniq _ hr_nil]

lemma rootedForest_root_eq_of_connected {RF : RootedForest} {G : MGraph}
    (hRF : RF.IsRootedSpanningForestOf G) {u v : ℕ} (hu : u ∈ G.V) (hv : v ∈ G.V)
    (hconn : RF.F.Connected u v) : RF.root u = RF.root v := by
  have hu_spec := rootedForest_root_spec hRF hu
  have hv_spec := rootedForest_root_spec hRF hv
  obtain ⟨P, hP⟩ := hconn
  obtain ⟨Q, hQ⟩ := hv_spec.2
  exact (hRF.2.2.2.1 u hu).unique hu_spec ⟨hv_spec.1, ⟨P ++ Q, IsWalk.append hP hQ⟩⟩

lemma rootedForest_root_eq_of_edge_F {RF : RootedForest} {G : MGraph}
    (hG : G.IsValid) (hRF : RF.IsRootedSpanningForestOf G) {e : ℕ} (he : e ∈ RF.F.E) :
    RF.root (G.tail e) = RF.root (G.head e) := by
  have hSub := hRF.2.2.2.2
  have heG : e ∈ G.E := hSub.2.1 he
  have hth := hSub.2.2 e he
  have hconn : RF.F.Connected (G.tail e) (G.head e) :=
    ⟨[(e, true)], .cons he (by simp [MGraph.src, hth.1]) (by
      simpa [MGraph.dst, hth.2] using .nil (G.head e))⟩
  exact rootedForest_root_eq_of_connected hRF (hG e heG).1 (hG e heG).2 hconn

lemma isCirculation_passCoreC {G : MGraph} {L : LSF} {c : ℕ → ℝ}
    (hG : G.IsValid) (hRF : L.F.IsRootedSpanningForestOf G) (hc : G.IsCirculation c) :
    (coreGraph G L).IsCirculation (passCoreC c) := by
  intro r _hr
  dsimp only [MGraph.demand, coreGraph, passCoreC] at hc ⊢
  have hr_fib : ∀ e ∈ G.E,
      (if r = L.F.root (G.tail e) then (1 : ℝ) else 0) -
        (if r = L.F.root (G.head e) then (1 : ℝ) else 0) =
      ∑ v ∈ G.V with L.F.root v = r, G.b e v := by
    intro e he
    have htV : G.tail e ∈ G.V := (hG e he).1
    have hhV : G.head e ∈ G.V := (hG e he).2
    dsimp only [MGraph.b]
    rw [Finset.sum_sub_distrib]
    have hs1 : (∑ v ∈ G.V with L.F.root v = r, if v = G.tail e then (1 : ℝ) else 0) =
        if r = L.F.root (G.tail e) then 1 else 0 := by
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_filter, htV, true_and, eq_comm]
    have hs2 : (∑ v ∈ G.V with L.F.root v = r, if v = G.head e then (1 : ℝ) else 0) =
        if r = L.F.root (G.head e) then 1 else 0 := by
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_filter, hhV, true_and, eq_comm]
    rw [hs1, hs2]
  have hsum_zero : ∑ v ∈ G.V with L.F.root v = r, G.demand c v = 0 :=
    Finset.sum_eq_zero fun v hv => hc v (Finset.mem_filter.mp hv).1
  simp only [MGraph.demand] at hsum_zero
  rw [Finset.sum_comm] at hsum_zero
  have hrew :
      (∑ e ∈ G.E, ∑ v ∈ G.V with L.F.root v = r, G.b e v * c e) =
        (∑ e ∈ G.E,
          ((if r = L.F.root (G.tail e) then (1 : ℝ) else 0) -
            (if r = L.F.root (G.head e) then (1 : ℝ) else 0)) * c e) := by
    refine Finset.sum_congr rfl fun e he => ?_
    rw [← Finset.sum_mul, ← hr_fib e he]
  rw [hrew] at hsum_zero
  have hsplit := Finset.sum_sdiff (hRF.2.2.2.2.2.1) (f := fun e =>
    ((if r = L.F.root (G.tail e) then (1 : ℝ) else 0) -
      (if r = L.F.root (G.head e) then (1 : ℝ) else 0)) * c e)
  have hF_zero :
      (∑ e ∈ L.F.F.E,
        ((if r = L.F.root (G.tail e) then (1 : ℝ) else 0) -
          (if r = L.F.root (G.head e) then (1 : ℝ) else 0)) * c e) = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rw [rootedForest_root_eq_of_edge_F hG hRF he, sub_self, zero_mul]
  rw [hF_zero, add_zero] at hsplit
  simpa [MGraph.b] using hsplit.trans hsum_zero

lemma isValidPair_passCore {G : MGraph} {L : LSF} {ℓ c w : ℕ → ℝ}
    (hG : G.IsValid) (hRF : L.F.IsRootedSpanningForestOf G)
    (hVP : IsValidPair G ℓ c w) (hwstr : ∀ e ∈ G.E, 0 ≤ L.wstr e) :
    IsValidPair (coreGraph G L) (coreLen L ℓ) (passCoreC c) (passCoreW L w) := by
  refine ⟨isCirculation_passCoreC hG hRF hVP.1, fun e he => ?_⟩
  have heG : e ∈ G.E := (Finset.mem_sdiff.mp he).1
  dsimp only [coreLen, passCoreC, passCoreW]
  rw [mul_assoc, abs_mul, abs_of_nonneg (hwstr e heG)]
  exact mul_le_mul_of_nonneg_left (hVP.2 e heG) (hwstr e heG)

lemma sum_b_mul_walkFlow_of_isWalk {S : MGraph} {u v r : ℕ} {P : List (ℕ × Bool)}
    (hW : S.IsWalk u v P) :
    ∑ e' ∈ S.E, S.b e' r * walkFlow P e' =
      (if r = u then (1 : ℝ) else 0) - (if r = v then (1 : ℝ) else 0) := by
  induction hW with
  | nil u => simp [walkFlow]
  | cons he hsrc _ ih =>
    rename_i u' v' x P' _
    have hstep : ∑ e' ∈ S.E, S.b e' r *
        (if x.1 = e' then (if x.2 = true then (1 : ℝ) else -1) else 0) =
        (if r = u' then (1 : ℝ) else 0) - (if r = S.dst x then (1 : ℝ) else 0) := by
      have hsrc' : u' = S.src x := hsrc.symm
      have hcongr : ∑ e' ∈ S.E, S.b e' r *
          (if x.1 = e' then (if x.2 = true then (1 : ℝ) else -1) else 0) =
          ∑ e' ∈ S.E, if e' = x.1 then S.b e' r * (if x.2 = true then (1 : ℝ) else -1) else 0 := by
        refine Finset.sum_congr rfl fun e' _ => ?_
        by_cases h1 : x.1 = e'
        · subst h1; simp
        · simp [h1, Ne.symm h1]
      rw [hcongr, Finset.sum_ite_eq' S.E x.1]
      simp only [he, ↓reduceIte, hsrc']
      rcases x with ⟨e₀, b₀⟩
      cases b₀ <;> simp [MGraph.b, MGraph.src, MGraph.dst]
    have hwf : ∀ e', walkFlow (x :: P') e' =
        (if x.1 = e' then (if x.2 = true then (1 : ℝ) else -1) else 0) + walkFlow P' e' := by
      intro e'
      simp [walkFlow]
    calc ∑ e' ∈ S.E, S.b e' r * walkFlow (x :: P') e'
        = ∑ e' ∈ S.E, (S.b e' r * (if x.1 = e' then (if x.2 = true then 1 else -1) else 0) +
            S.b e' r * walkFlow P' e') := by
          refine Finset.sum_congr rfl fun e' _ => ?_
          rw [hwf e', mul_add]
      _ = (∑ e' ∈ S.E, S.b e' r * (if x.1 = e' then (if x.2 = true then 1 else -1) else 0)) +
            (∑ e' ∈ S.E, S.b e' r * walkFlow P' e') := Finset.sum_add_distrib
      _ = ((if r = u' then (1 : ℝ) else 0) - (if r = S.dst x then (1 : ℝ) else 0)) +
            ((if r = S.dst x then (1 : ℝ) else 0) - (if r = v' then (1 : ℝ) else 0)) := by
          rw [hstep, ih]
      _ = (if r = u' then (1 : ℝ) else 0) - (if r = v' then (1 : ℝ) else 0) := by ring

lemma isCirculation_passSparseCoreC {C S : MGraph} {emb : Embedding} {cC : ℕ → ℝ}
    (hC : C.IsValid) (hEmb : emb.IsEmbedding C S) (hcC : C.IsCirculation cC) :
    S.IsCirculation (passSparseCoreC C emb cC) := by
  intro r _hr
  dsimp only [MGraph.demand, passSparseCoreC]
  calc ∑ e' ∈ S.E, S.b e' r * ∑ e ∈ C.E, cC e * walkFlow (emb e) e'
      = ∑ e' ∈ S.E, ∑ e ∈ C.E, cC e * (S.b e' r * walkFlow (emb e) e') := by
        refine Finset.sum_congr rfl fun e' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => by ring
    _ = ∑ e ∈ C.E, cC e * ∑ e' ∈ S.E, S.b e' r * walkFlow (emb e) e' := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ e ∈ C.E, C.b e r * cC e := by
        refine Finset.sum_congr rfl fun e he => ?_
        rw [sum_b_mul_walkFlow_of_isWalk (hEmb.2 e he)]
        simp [MGraph.b, mul_comm]
    _ = 0 := by
        by_cases hrC : r ∈ C.V
        · exact hcC r hrC
        · refine Finset.sum_eq_zero fun e he => ?_
          have hth := hC e he
          have ht : r ≠ C.tail e := fun h => hrC (h ▸ hth.1)
          have hh : r ≠ C.head e := fun h => hrC (h ▸ hth.2)
          simp [MGraph.b, ht, hh]

lemma walkFlow_eq_zero_of_not_mem_walkEdges {P : List (ℕ × Bool)} {e' : ℕ}
    (hne : e' ∉ walkEdges P) : walkFlow P e' = 0 := by
  induction P with
  | nil => simp [walkFlow]
  | cons x xs ih =>
    simp only [walkEdges, List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at hne
    have hneq : x.1 ≠ e' := Ne.symm hne.1
    simp only [walkFlow, List.map_cons, List.sum_cons, hneq, ↓reduceIte, zero_add]
    exact ih hne.2

lemma isValidPair_passSparseCore {C S : MGraph} {emb : Embedding} {lenC lenS cC wC : ℕ → ℝ}
    (hC : C.IsValid) (hEmb : emb.IsEmbedding C S) (hVP : IsValidPair C lenC cC wC)
    (hApprox : ∀ e ∈ C.E, ∀ e' ∈ walkEdges (emb e), 0 ≤ lenS e' ∧ lenS e' ≤ 2 * lenC e)
    (hlenS : ∀ e' ∈ S.E, 0 ≤ lenS e') :
    IsValidPair S lenS (passSparseCoreC C emb cC) (passSparseCoreW C emb wC) := by
  refine ⟨isCirculation_passSparseCoreC hC hEmb hVP.1, fun e' he' => ?_⟩
  dsimp only [passSparseCoreC, passSparseCoreW]
  rw [abs_mul, abs_of_nonneg (hlenS e' he')]
  calc lenS e' * |∑ e ∈ C.E, cC e * walkFlow (emb e) e'|
      ≤ lenS e' * ∑ e ∈ C.E, |cC e * walkFlow (emb e) e'| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (hlenS e' he')
    _ = ∑ e ∈ C.E, lenS e' * |cC e| * |walkFlow (emb e) e'| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [abs_mul, mul_assoc]
    _ ≤ ∑ e ∈ C.E, 2 * (wC e * walkCount (emb e) e') := by
        refine Finset.sum_le_sum fun e he => ?_
        by_cases hw : e' ∈ walkEdges (emb e)
        · have hA := (hApprox e he e' hw).2
          have h1 : lenS e' * |cC e| ≤ 2 * (lenC e * |cC e|) := by
            calc lenS e' * |cC e| ≤ (2 * lenC e) * |cC e| :=
                  mul_le_mul_of_nonneg_right hA (abs_nonneg _)
              _ = 2 * (lenC e * |cC e|) := by ring
          have h2 : lenC e * |cC e| ≤ wC e := by
            have hle := hVP.2 e he
            rw [abs_mul] at hle
            exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)) hle
          calc lenS e' * |cC e| * |walkFlow (emb e) e'|
              ≤ (2 * wC e) * |walkFlow (emb e) e'| :=
                mul_le_mul_of_nonneg_right (le_trans h1 (by linarith)) (abs_nonneg _)
            _ ≤ (2 * wC e) * walkCount (emb e) e' := by
                have hw0 : 0 ≤ 2 * wC e := by
                  linarith [le_trans (abs_nonneg _) (hVP.2 e he)]
                exact mul_le_mul_of_nonneg_left (abs_walkFlow_le_walkCount (emb e) e') hw0
            _ = 2 * (wC e * walkCount (emb e) e') := by ring
        · simp [walkFlow_eq_zero_of_not_mem_walkEdges hw, walkCount_eq_zero_of_not_mem hw]
    _ = 2 * ∑ e ∈ C.E, wC e * walkCount (emb e) e' := (Finset.mul_sum _ _ _).symm

/-! ## 3. Initial vertex-split core graph `tildeC0Base` -/

lemma unique_piece_of_not_R {𝒲 : Finset (Finset ℕ)} {R : Finset ℕ}
    (hb : boundary 𝒲 ⊆ R) {x : ℕ} (hxR : x ∉ R)
    {W₁ W₂ : Finset ℕ} (h1 : W₁ ∈ 𝒲) (h2 : W₂ ∈ 𝒲) (hx1 : x ∈ W₁) (hx2 : x ∈ W₂) :
    W₁ = W₂ := by
  by_contra hne
  apply hxR
  apply hb
  simp only [boundary, Finset.mem_filter, Finset.mem_biUnion, id_eq]
  exact ⟨⟨W₁, h1, hx1⟩, W₁, h1, W₂, h2, hne, hx1, hx2⟩

lemma mem_piece_of_mem_V_not_R {S₀ : LSFState}
    (hRF : S₀.RF.IsRootedSpanningForestOf S₀.G)
    (hBiU : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    {x : ℕ} (hxV : x ∈ S₀.G.V) (hxR : x ∉ S₀.R) :
    ∃ W ∈ S₀.W_init, x ∈ W := by
  obtain ⟨hrR, P, hW⟩ := rootedForest_root_spec hRF hxV
  generalize hrx : S₀.RF.root x = r₀ at hrR hW
  cases hW with
  | nil => exact absurd hrR hxR
  | @cons _ _ x₀ _ he hsrc _ =>
    have heF : x₀.1 ∈ S₀.RF.F.E := he
    rw [← hBiU, Finset.mem_biUnion] at heF
    obtain ⟨W, hW_mem, heW⟩ := heF
    rw [inducedEdges, Finset.mem_filter] at heW
    refine ⟨W, hW_mem, ?_⟩
    rcases x₀ with ⟨e₀, b₀⟩
    cases b₀
    · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsrc
      rw [← hsrc]; exact heW.2.2
    · simp only [MGraph.src, ↓reduceIte] at hsrc
      rw [← hsrc]; exact heW.2.1

lemma root_mem_piece_of_walk_RF {S₀ : LSFState}
    (hRF : S₀.RF.IsRootedSpanningForestOf S₀.G)
    (hBiU : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hb : boundary S₀.W_init ⊆ S₀.R) :
    ∀ {y r : ℕ} {P : List (ℕ × Bool)},
      S₀.RF.F.IsWalk y r P → r ∈ S₀.R →
        (∀ W ∈ S₀.W_init, y ∈ W → y ∉ S₀.R → r ∈ W) := by
  intro y r P hW
  induction hW with
  | nil u =>
    intro hu _ _ _ hu_not
    exact absurd hu hu_not
  | cons he hsrc hrest ih =>
    rename_i u v x P'
    intro hvR W hW_mem huW hu_notR
    have heF : x.1 ∈ S₀.RF.F.E := he
    rw [← hBiU, Finset.mem_biUnion] at heF
    obtain ⟨W', hW'_mem, heW'⟩ := heF
    rw [inducedEdges, Finset.mem_filter] at heW'
    have huW' : u ∈ W' := by
      rcases x with ⟨e₀, b₀⟩
      cases b₀ <;> simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsrc
      · rw [← hsrc]; exact heW'.2.2
      · rw [← hsrc]; exact heW'.2.1
    have hdW' : S₀.RF.F.dst x ∈ W' := by
      rcases x with ⟨e₀, b₀⟩
      cases b₀ <;> simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte]
      · exact heW'.2.1
      · exact heW'.2.2
    have hWeq : W' = W := unique_piece_of_not_R hb hu_notR hW'_mem hW_mem huW' huW
    have hdW : S₀.RF.F.dst x ∈ W := hWeq ▸ hdW'
    by_cases hdR : S₀.RF.F.dst x ∈ S₀.R
    · have hdV : S₀.RF.F.dst x ∈ S₀.G.V := hRF.2.2.1 hdR
      obtain ⟨r', _, huniq⟩ := hRF.2.2.2.1 _ hdV
      have h1 : S₀.RF.F.dst x ∈ S₀.RF.R ∧ S₀.RF.F.Connected (S₀.RF.F.dst x) (S₀.RF.F.dst x) :=
        ⟨hdR, ⟨[], .nil _⟩⟩
      have h2 : v ∈ S₀.RF.R ∧ S₀.RF.F.Connected (S₀.RF.F.dst x) v := ⟨hvR, ⟨P', hrest⟩⟩
      have heq : S₀.RF.F.dst x = v :=
        (huniq (S₀.RF.F.dst x) h1).trans (huniq v h2).symm
      rwa [← heq]
    · exact ih hvR W hW_mem hdW hdR

/-- Canonical piece representative `Finset ℕ` containing `v ∈ S₀.G.V \ S₀.R`. -/
noncomputable def pieceSet (S₀ : LSFState) (v : ℕ) : Finset ℕ :=
  open Classical in
  if h : ∃ W ∈ S₀.W_init, v ∈ W then Classical.choose h else ∅

/-- Canonical injective index in `ℕ` for a piece `W ∈ S₀.W_init`. -/
noncomputable def pieceIdx (S₀ : LSFState) (W : Finset ℕ) : ℕ :=
  open Classical in
  if hW : W ∈ S₀.W_init then ((S₀.W_init.equivFin) ⟨W, hW⟩).1 else 0

/-- Canonical injective piece index in `ℕ` for `v ∈ S₀.G.V \ S₀.R`. -/
noncomputable def pieceMap (S₀ : LSFState) (v : ℕ) : ℕ :=
  pieceIdx S₀ (pieceSet S₀ v)

lemma pieceSet_spec {S₀ : LSFState} {v : ℕ} (hW : ∃ W ∈ S₀.W_init, v ∈ W) :
    pieceSet S₀ v ∈ S₀.W_init ∧ v ∈ pieceSet S₀ v := by
  classical
  simp only [pieceSet, hW, ↓reduceDIte]
  exact Classical.choose_spec hW

lemma pieceMap_eq_iff {S₀ : LSFState} (hb : boundary S₀.W_init ⊆ S₀.R)
    {x y : ℕ} (hxR : x ∉ S₀.R) (hyR : y ∉ S₀.R)
    (hxW : ∃ W ∈ S₀.W_init, x ∈ W) (hyW : ∃ W ∈ S₀.W_init, y ∈ W) :
    pieceMap S₀ x = pieceMap S₀ y ↔ ∃ W ∈ S₀.W_init, x ∈ W ∧ y ∈ W := by
  classical
  have hxs := pieceSet_spec hxW
  have hys := pieceSet_spec hyW
  simp only [pieceMap, pieceIdx, hxs.1, hys.1, ↓reduceDIte]
  constructor
  · intro h
    have heq : pieceSet S₀ x = pieceSet S₀ y :=
      congrArg Subtype.val ((S₀.W_init.equivFin).injective (Fin.ext h))
    exact ⟨pieceSet S₀ x, hxs.1, hxs.2, heq ▸ hys.2⟩
  · rintro ⟨W, hW, hx, hy⟩
    have hx_eq : pieceSet S₀ x = W := unique_piece_of_not_R hb hxR hxs.1 hW hxs.2 hx
    have hy_eq : pieceSet S₀ y = W := unique_piece_of_not_R hb hyR hys.1 hW hys.2 hy
    congr 2
    exact Subtype.ext (hx_eq.trans hy_eq.symm)

/-- Initial vertex-split map `G₀.V → ℕ` for `algo:dynasparsecore`. -/
noncomputable def tildeV0 (S₀ : LSFState) (v : ℕ) : ℕ :=
  if v ∈ S₀.R then 2 * v else 2 * Nat.pair (S₀.RF.root v) (pieceMap S₀ v) + 1

/-- Dynamic root-piece equivalence invariant for quotient vertex map `m`. -/
def RootPieceInv (S₀ S : LSFState) (m : ℕ → ℕ) : Prop :=
  ∀ x ∈ S.G.V, ∀ y ∈ S.G.V,
    m x = m y ↔
      x = y ∨
        (x ∈ S₀.G.V ∧ y ∈ S₀.G.V ∧ S.RF.root x = S.RF.root y ∧
          (x ∈ S₀.R ↔ y ∈ S₀.R) ∧
          (x ∉ S₀.R → ∃ W ∈ S₀.W_init, x ∈ W ∧ y ∈ W))

lemma tildeV0_rootPieceInv {S₀ : LSFState}
    (hRF : S₀.RF.IsRootedSpanningForestOf S₀.G)
    (hBiU : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hb : boundary S₀.W_init ⊆ S₀.R) :
    RootPieceInv S₀ S₀ (tildeV0 S₀) := by
  intro x hx y hy
  by_cases hxR : x ∈ S₀.R <;> by_cases hyR : y ∈ S₀.R
  · have htx : tildeV0 S₀ x = 2 * x := by simp [tildeV0, hxR]
    have hty : tildeV0 S₀ y = 2 * y := by simp [tildeV0, hyR]
    rw [htx, hty]
    constructor
    · intro h; left; omega
    · rintro (rfl | ⟨_, _, hrt, _, _⟩)
      · rfl
      · rw [rootedForest_root_eq_of_mem_R hRF hxR, rootedForest_root_eq_of_mem_R hRF hyR] at hrt
        rw [hrt]
  · have htx : tildeV0 S₀ x = 2 * x := by simp [tildeV0, hxR]
    have hty : tildeV0 S₀ y = 2 * Nat.pair (S₀.RF.root y) (pieceMap S₀ y) + 1 := by simp [tildeV0, hyR]
    rw [htx, hty]
    constructor
    · intro h; omega
    · rintro (rfl | ⟨_, _, _, hiff, _⟩)
      · exact absurd hxR hyR
      · exact absurd (hiff.mp hxR) hyR
  · have htx : tildeV0 S₀ x = 2 * Nat.pair (S₀.RF.root x) (pieceMap S₀ x) + 1 := by simp [tildeV0, hxR]
    have hty : tildeV0 S₀ y = 2 * y := by simp [tildeV0, hyR]
    rw [htx, hty]
    constructor
    · intro h; omega
    · rintro (rfl | ⟨_, _, _, hiff, _⟩)
      · exact absurd hyR hxR
      · exact absurd (hiff.mpr hyR) hxR
  · have htx : tildeV0 S₀ x = 2 * Nat.pair (S₀.RF.root x) (pieceMap S₀ x) + 1 := by simp [tildeV0, hxR]
    have hty : tildeV0 S₀ y = 2 * Nat.pair (S₀.RF.root y) (pieceMap S₀ y) + 1 := by simp [tildeV0, hyR]
    rw [htx, hty]
    have hxW := mem_piece_of_mem_V_not_R hRF hBiU hx hxR
    have hyW := mem_piece_of_mem_V_not_R hRF hBiU hy hyR
    constructor
    · intro h
      have hpair : Nat.pair (S₀.RF.root x) (pieceMap S₀ x) =
          Nat.pair (S₀.RF.root y) (pieceMap S₀ y) := by omega
      have hpr := Nat.pair_eq_pair.mp hpair
      right
      refine ⟨hx, hy, hpr.1, by simp [hxR, hyR], fun _ =>
        (pieceMap_eq_iff hb hxR hyR hxW hyW).mp hpr.2⟩
    · rintro (rfl | ⟨_, _, hrt, _, hW⟩)
      · rfl
      · have hpm := (pieceMap_eq_iff hb hxR hyR hxW hyW).mpr (hW hxR)
        rw [hrt, hpm]

/-- Initial vertex-split core graph `\tilde{C}₀` (including all off-forest core edges
`S₀.G.E \ S₀.RF.F.E`, since `Update.split` handles self-loops directly). -/
noncomputable def tildeC0Base (S₀ : LSFState) : MGraph where
  V := S₀.G.V.image (tildeV0 S₀)
  E := S₀.G.E \ S₀.RF.F.E
  tail e := tildeV0 S₀ (S₀.G.tail e)
  head e := tildeV0 S₀ (S₀.G.head e)

lemma tildeC0Base_isValid {S₀ : LSFState} (hG : S₀.G.IsValid) :
    (tildeC0Base S₀).IsValid := by
  intro e he
  rw [tildeC0Base, Finset.mem_sdiff] at he
  have hth := hG e he.1
  exact ⟨Finset.mem_image_of_mem _ hth.1, Finset.mem_image_of_mem _ hth.2⟩

lemma tildeC0Base_V_card_le {S₀ : LSFState}
    (hRF : S₀.RF.IsRootedSpanningForestOf S₀.G)
    (hBiU : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hb : boundary S₀.W_init ⊆ S₀.R)
    (hWPB : ∀ W ∈ S₀.W_init, (pieceBoundary S₀.W_init W).card ≤ 1) :
    (tildeC0Base S₀).V.card ≤ 2 * S₀.R.card + S₀.W_init.card := by
  classical
  set oddVs := (S₀.G.V.filter fun v => v ∉ S₀.R).image (tildeV0 S₀)
  have hpart : (tildeC0Base S₀).V ⊆ (S₀.R.image fun r => 2 * r) ∪ oddVs := by
    intro u hu
    rw [tildeC0Base, Finset.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [Finset.mem_union]
    by_cases hvR : v ∈ S₀.R
    · left
      rw [Finset.mem_image]
      exact ⟨v, hvR, by simp [tildeV0, hvR]⟩
    · right
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hv, hvR⟩)
  set pairs := (S₀.G.V.filter fun v => v ∉ S₀.R).image fun v => (S₀.RF.root v, pieceSet S₀ v)
  let pairToOdd : ℕ × Finset ℕ → ℕ := fun p => 2 * Nat.pair p.1 (pieceIdx S₀ p.2) + 1
  have hodd_sub : oddVs ⊆ pairs.image pairToOdd := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    have hv_f := Finset.mem_filter.mp hv
    rw [Finset.mem_image]
    exact ⟨(S₀.RF.root v, pieceSet S₀ v), Finset.mem_image_of_mem _ hv,
      by simp [pairToOdd, tildeV0, hv_f.2, pieceMap]⟩
  have hodd_le : oddVs.card ≤ pairs.card :=
    le_trans (Finset.card_le_card hodd_sub) Finset.card_image_le
  have hpairs_prop : ∀ p ∈ pairs, p.1 ∈ S₀.R ∧ p.2 ∈ S₀.W_init ∧ p.1 ∈ p.2 := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨v, hv, rfl⟩ := hp
    have hv_f := Finset.mem_filter.mp hv
    have hW := mem_piece_of_mem_V_not_R hRF hBiU hv_f.1 hv_f.2
    have hps := pieceSet_spec hW
    have hr_sp := rootedForest_root_spec hRF hv_f.1
    obtain ⟨P, hP⟩ := hr_sp.2
    exact ⟨hr_sp.1, hps.1, root_mem_piece_of_walk_RF hRF hBiU hb hP hr_sp.1 _ hps.1 hps.2 hv_f.2⟩
  set pairsB := pairs.filter fun p => p.1 ∈ boundary S₀.W_init
  set pairsI := pairs.filter fun p => p.1 ∉ boundary S₀.W_init
  have hpairs_split : pairs.card ≤ pairsB.card + pairsI.card := by
    calc pairs.card ≤ (pairsB ∪ pairsI).card := Finset.card_le_card fun p hp => by
          rw [Finset.mem_union]
          by_cases hpb : p.1 ∈ boundary S₀.W_init
          · left; exact Finset.mem_filter.mpr ⟨hp, hpb⟩
          · right; exact Finset.mem_filter.mpr ⟨hp, hpb⟩
      _ ≤ pairsB.card + pairsI.card := Finset.card_union_le _ _
  have hpairsB_le : pairsB.card ≤ S₀.W_init.card := by
    refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
    · intro p hp
      exact (hpairs_prop p (Finset.mem_filter.mp hp).1).2.1
    · intro p₁ hp₁ p₂ hp₂ heq
      have h1 := Finset.mem_filter.mp hp₁
      have h2 := Finset.mem_filter.mp hp₂
      have hprop1 := hpairs_prop p₁ h1.1
      have hprop2 := hpairs_prop p₂ h2.1
      have hpb1 : p₁.1 ∈ pieceBoundary S₀.W_init p₁.2 := Finset.mem_inter.mpr ⟨hprop1.2.2, h1.2⟩
      have hpb2 : p₂.1 ∈ pieceBoundary S₀.W_init p₁.2 :=
        Finset.mem_inter.mpr ⟨heq ▸ hprop2.2.2, h2.2⟩
      have hc1 : (pieceBoundary S₀.W_init p₁.2).card ≤ 1 := hWPB p₁.2 hprop1.2.1
      exact Prod.ext (Finset.card_le_one.mp hc1 p₁.1 hpb1 p₂.1 hpb2) heq
  have hpairsI_le : pairsI.card ≤ S₀.R.card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro p hp
      exact (hpairs_prop p (Finset.mem_filter.mp hp).1).1
    · intro p₁ hp₁ p₂ hp₂ heq
      have h1 := Finset.mem_filter.mp hp₁
      have h2 := Finset.mem_filter.mp hp₂
      have hprop1 := hpairs_prop p₁ h1.1
      have hprop2 := hpairs_prop p₂ h2.1
      have hsnd : p₁.2 = p₂.2 := by
        by_contra hne
        apply h1.2
        simp only [boundary, Finset.mem_filter, Finset.mem_biUnion, id_eq]
        refine ⟨⟨p₁.2, hprop1.2.1, hprop1.2.2⟩, p₁.2, hprop1.2.1, p₂.2, hprop2.2.1,
          hne, hprop1.2.2, heq.symm ▸ hprop2.2.2⟩
      exact Prod.ext heq hsnd
  have heven_le : (S₀.R.image fun r => 2 * r).card ≤ S₀.R.card := Finset.card_image_le
  calc (tildeC0Base S₀).V.card
      ≤ ((S₀.R.image fun r => 2 * r) ∪ oddVs).card := Finset.card_le_card hpart
    _ ≤ (S₀.R.image fun r => 2 * r).card + oddVs.card := Finset.card_union_le _ _
    _ ≤ S₀.R.card + pairs.card := Nat.add_le_add heven_le hodd_le
    _ ≤ S₀.R.card + (pairsB.card + pairsI.card) := Nat.add_le_add_left hpairs_split _
    _ ≤ S₀.R.card + (S₀.W_init.card + S₀.R.card) := Nat.add_le_add_left (Nat.add_le_add hpairsB_le hpairsI_le) _
    _ = 2 * S₀.R.card + S₀.W_init.card := by omega

lemma tildeC0Base_maxDeg_le {S₀ : LSFState}
    (hG : S₀.G.IsValid) (hRF : S₀.RF.IsRootedSpanningForestOf S₀.G)
    (hBiU : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E)
    (hb : boundary S₀.W_init ⊆ S₀.R)
    {k : ℝ}
    (hVol : ∀ W ∈ S₀.W_init, (S₀.G.vol (W \ S₀.R) : ℝ) ≤ 2240 * k * Real.log ((S₀.G.n : ℝ) + 2) ^ 2) :
    ((tildeC0Base S₀).maxDeg : ℝ) ≤
      max (S₀.G.maxDeg : ℝ) (2240 * k * Real.log ((S₀.G.n : ℝ) + 2) ^ 2) := by
  set M := max (S₀.G.maxDeg : ℝ) (2240 * k * Real.log ((S₀.G.n : ℝ) + 2) ^ 2)
  have hM_nn : 0 ≤ M := le_max_of_le_left (Nat.cast_nonneg _)
  have hpoint : ∀ vT ∈ (tildeC0Base S₀).V, ((tildeC0Base S₀).deg vT : ℝ) ≤ M := by
    intro vT hvT
    rw [tildeC0Base, Finset.mem_image] at hvT
    obtain ⟨x₀, hx₀, rfl⟩ := hvT
    by_cases hx₀R : x₀ ∈ S₀.R
    · have ht_sub : ((tildeC0Base S₀).E.filter fun e => (tildeC0Base S₀).tail e = tildeV0 S₀ x₀) ⊆
          (S₀.G.E.filter fun e => S₀.G.tail e = x₀) := by
        intro e he
        rw [Finset.mem_filter] at he ⊢
        have heG : e ∈ S₀.G.E := (Finset.mem_sdiff.mp he.1).1
        have hinv := (tildeV0_rootPieceInv hRF hBiU hb (S₀.G.tail e) (hG e heG).1 x₀ hx₀).mp he.2
        refine ⟨heG, ?_⟩
        rcases hinv with h | ⟨_, _, hrt, hiff, _⟩
        · exact h
        · have htr : S₀.G.tail e ∈ S₀.R := hiff.mpr hx₀R
          rw [rootedForest_root_eq_of_mem_R hRF htr, rootedForest_root_eq_of_mem_R hRF hx₀R] at hrt
          exact hrt
      have hh_sub : ((tildeC0Base S₀).E.filter fun e => (tildeC0Base S₀).head e = tildeV0 S₀ x₀) ⊆
          (S₀.G.E.filter fun e => S₀.G.head e = x₀) := by
        intro e he
        rw [Finset.mem_filter] at he ⊢
        have heG : e ∈ S₀.G.E := (Finset.mem_sdiff.mp he.1).1
        have hinv := (tildeV0_rootPieceInv hRF hBiU hb (S₀.G.head e) (hG e heG).2 x₀ hx₀).mp he.2
        refine ⟨heG, ?_⟩
        rcases hinv with h | ⟨_, _, hrt, hiff, _⟩
        · exact h
        · have hhr : S₀.G.head e ∈ S₀.R := hiff.mpr hx₀R
          rw [rootedForest_root_eq_of_mem_R hRF hhr, rootedForest_root_eq_of_mem_R hRF hx₀R] at hrt
          exact hrt
      have hdeg_le : (tildeC0Base S₀).deg (tildeV0 S₀ x₀) ≤ S₀.G.deg x₀ :=
        Nat.add_le_add (Finset.card_le_card ht_sub) (Finset.card_le_card hh_sub)
      have hmax_le : S₀.G.deg x₀ ≤ S₀.G.maxDeg := Finset.le_sup (f := S₀.G.deg) hx₀
      exact le_trans (Nat.cast_le.mpr (le_trans hdeg_le hmax_le)) (le_max_left _ _)
    · obtain ⟨W, hW_mem, hx₀W⟩ := mem_piece_of_mem_V_not_R hRF hBiU hx₀ hx₀R
      have hmem_W_notR : ∀ y ∈ S₀.G.V, tildeV0 S₀ y = tildeV0 S₀ x₀ → y ∈ W \ S₀.R := by
        intro y hy heq
        have hinv := (tildeV0_rootPieceInv hRF hBiU hb y hy x₀ hx₀).mp heq
        rcases hinv with rfl | ⟨_, _, _, hiff, hWp⟩
        · exact Finset.mem_sdiff.mpr ⟨hx₀W, hx₀R⟩
        · have hy_notR : y ∉ S₀.R := fun hyR => hx₀R (hiff.mp hyR)
          obtain ⟨W', hW'_mem, hyW', hx₀W'⟩ := hWp hy_notR
          have hWeq : W' = W := unique_piece_of_not_R hb hx₀R hW'_mem hW_mem hx₀W' hx₀W
          exact Finset.mem_sdiff.mpr ⟨hWeq ▸ hyW', hy_notR⟩
      have ht_sub : ((tildeC0Base S₀).E.filter fun e => (tildeC0Base S₀).tail e = tildeV0 S₀ x₀) ⊆
          (W \ S₀.R).biUnion (fun y => S₀.G.E.filter fun e => S₀.G.tail e = y) := by
        intro e he
        rw [Finset.mem_filter] at he
        have heG : e ∈ S₀.G.E := (Finset.mem_sdiff.mp he.1).1
        rw [Finset.mem_biUnion]
        exact ⟨S₀.G.tail e, hmem_W_notR _ (hG e heG).1 he.2, Finset.mem_filter.mpr ⟨heG, rfl⟩⟩
      have hh_sub : ((tildeC0Base S₀).E.filter fun e => (tildeC0Base S₀).head e = tildeV0 S₀ x₀) ⊆
          (W \ S₀.R).biUnion (fun y => S₀.G.E.filter fun e => S₀.G.head e = y) := by
        intro e he
        rw [Finset.mem_filter] at he
        have heG : e ∈ S₀.G.E := (Finset.mem_sdiff.mp he.1).1
        rw [Finset.mem_biUnion]
        exact ⟨S₀.G.head e, hmem_W_notR _ (hG e heG).2 he.2, Finset.mem_filter.mpr ⟨heG, rfl⟩⟩
      have hcard_t :
          ((tildeC0Base S₀).E.filter fun e => (tildeC0Base S₀).tail e = tildeV0 S₀ x₀).card ≤
            ∑ y ∈ W \ S₀.R, (S₀.G.E.filter fun e => S₀.G.tail e = y).card :=
        le_trans (Finset.card_le_card ht_sub) Finset.card_biUnion_le
      have hcard_h :
          ((tildeC0Base S₀).E.filter fun e => (tildeC0Base S₀).head e = tildeV0 S₀ x₀).card ≤
            ∑ y ∈ W \ S₀.R, (S₀.G.E.filter fun e => S₀.G.head e = y).card :=
        le_trans (Finset.card_le_card hh_sub) Finset.card_biUnion_le
      have hdeg_le : (tildeC0Base S₀).deg (tildeV0 S₀ x₀) ≤ S₀.G.vol (W \ S₀.R) := by
        dsimp only [MGraph.deg, MGraph.vol]
        calc _ ≤ (∑ y ∈ W \ S₀.R, (S₀.G.E.filter fun e => S₀.G.tail e = y).card) +
              (∑ y ∈ W \ S₀.R, (S₀.G.E.filter fun e => S₀.G.head e = y).card) :=
            Nat.add_le_add hcard_t hcard_h
          _ = ∑ y ∈ W \ S₀.R, ((S₀.G.E.filter fun e => S₀.G.tail e = y).card +
              (S₀.G.E.filter fun e => S₀.G.head e = y).card) := by
            rw [← Finset.sum_add_distrib]
      exact le_trans (le_trans (Nat.cast_le.mpr hdeg_le) (hVol W hW_mem)) (le_max_right _ _)
  have hsup_nat : (tildeC0Base S₀).maxDeg ≤ Nat.floor M := by
    dsimp only [MGraph.maxDeg]
    exact Finset.sup_le fun vT hvT => (Nat.le_floor_iff hM_nn).mpr (hpoint vT hvT)
  exact le_trans (Nat.cast_le.mpr hsup_nat) (Nat.floor_le hM_nn)

end

end MinCostFlow.SparseCore
