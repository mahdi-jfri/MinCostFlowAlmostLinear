module

public import MinCostFlow.Expander.DecomposeLevelProg
public import MinCostFlow.Expander.DecomposeProgBounds

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Base Bounds & Multi-Level Invariants for `DecomposeImpl`

Pure analytical, word-size, arena-length, cost, address-layout, and multi-level
graph-decomposition lemmas supporting `DecomposeProgHelpers` and `DecomposeProg`.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner WordRAM

public section


/-! ## 4. Multi-Level Decomposition Record & `DecomposeProp` Assembly -/

structure DecompLevelRec where
  lvl : ℕ
  rawComps : List (ℕ × List ℕ)
  validRs : List (Finset ℕ)
  Gi : Cited.Graph
  keptIdx : List ℕ

lemma pairwise_lt_eq_of_mem_iff :
    ∀ {xs ys : List ℕ}, xs.Pairwise (· < ·) → ys.Pairwise (· < ·) → (∀ a, a ∈ xs ↔ a ∈ ys) → xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, h => by
    have := (h y).mpr (by simp)
    simp at this
  | x :: xs, [], _, _, h => by
    have := (h x).mp (by simp)
    simp at this
  | x :: xs, y :: ys, hpx, hpy, h => by
    rw [List.pairwise_cons] at hpx hpy
    have hxy : x = y := by
      have hx_in : x ∈ y :: ys := (h x).mp (by simp)
      have hy_in : y ∈ x :: xs := (h y).mpr (by simp)
      rcases List.mem_cons.mp hx_in with hxy | hx_ys
      · exact hxy
      · rcases List.mem_cons.mp hy_in with hyx | hy_xs
        · exact hyx.symm
        · exfalso
          have h1 := hpy.1 x hx_ys
          have h2 := hpx.1 y hy_xs
          omega
    subst y
    congr 1
    apply pairwise_lt_eq_of_mem_iff hpx.2 hpy.2
    intro a
    constructor <;> intro ha
    · have : a ∈ x :: ys := (h a).mp (by simp [ha])
      rcases List.mem_cons.mp this with rfl | ha'
      · exfalso; have := hpx.1 _ ha; omega
      · exact ha'
    · have : a ∈ x :: xs := (h a).mpr (by simp [ha])
      rcases List.mem_cons.mp this with rfl | ha'
      · exfalso; have := hpy.1 _ ha; omega
      · exact ha'

lemma graphAt_eq_of_edges_eq {G : Cited.Graph} {d : DecomposeOutput} {i : ℕ}
    {idxs : List ℕ} (hidxs : DecomposeOutput.edgesAt G d i = idxs)
    {Gi : Cited.Graph} (hn : Gi.n = G.n)
    (he : Gi.edges = idxs.map fun j => G.edges.getD j (0, 0)) :
    DecomposeOutput.graphAt G d i = Gi := by
  cases Gi
  simp only [DecomposeOutput.graphAt, hidxs, ← he]
  congr 1
  exact hn.symm

lemma pairwise_le_flatten_of_blocks :
    ∀ (blocks : List (ℕ × List (ℕ × List ℕ))),
      blocks.Pairwise (fun a b => a.1 ≤ b.1) →
      (∀ b ∈ blocks, ∀ c ∈ b.2, c.1 = b.1) →
      (blocks.map (·.2)).flatten.Pairwise (fun a b => a.1 ≤ b.1)
  | [], _, _ => List.Pairwise.nil
  | b :: bs, hpb, hb_eq => by
    rw [List.pairwise_cons] at hpb
    simp only [List.map_cons, List.flatten_cons]
    refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · refine List.pairwise_of_forall_mem_list fun x hx y hy => ?_
      rw [hb_eq b (by simp) x hx, hb_eq b (by simp) y hy]
    · exact pairwise_le_flatten_of_blocks bs hpb.2 fun b' hb' => hb_eq b' (by simp [hb'])
    · intro x hx y hy
      rw [List.mem_flatten] at hy
      rcases hy with ⟨l, hl, hy_l⟩
      rw [List.mem_map] at hl
      rcases hl with ⟨b', hb', rfl⟩
      rw [hb_eq b (by simp) x hx, hb_eq b' (by simp [hb']) y hy_l]
      exact hpb.1 b' hb'

lemma filter_eq_of_blocks (blocks : List (ℕ × List (ℕ × List ℕ)))
    (hkeys : (blocks.map (·.1)).Nodup)
    (hb_eq : ∀ b ∈ blocks, ∀ c ∈ b.2, c.1 = b.1) :
    ∀ b ∈ blocks, (blocks.map (·.2)).flatten.filter (fun c => decide (c.1 = b.1)) = b.2 := by
  induction blocks with
  | nil => intro b hb; simp at hb
  | cons b₀ bs ih =>
    intro b hb
    simp only [List.map_cons, List.flatten_cons, List.filter_append]
    simp only [List.map_cons, List.nodup_cons] at hkeys
    rcases List.mem_cons.mp hb with rfl | hb_bs
    · have h1 : b.2.filter (fun c => decide (c.1 = b.1)) = b.2 := by
        apply List.filter_eq_self.mpr
        intro c hc; simp [hb_eq b (by simp) c hc]
      have h2 : (bs.map (·.2)).flatten.filter (fun c => decide (c.1 = b.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c hc
        rw [List.mem_flatten] at hc
        rcases hc with ⟨l, hl, hcl⟩
        rw [List.mem_map] at hl
        rcases hl with ⟨b', hb', rfl⟩
        rw [hb_eq b' (by simp [hb']) c hcl]
        have hne : b'.1 ≠ b.1 := fun h => hkeys.1 (h ▸ List.mem_map_of_mem hb')
        simp [hne]
      simp [h1, h2]
    · have ih' := ih hkeys.2 (fun b' hb' => hb_eq b' (by simp [hb'])) b hb_bs
      have h1 : b₀.2.filter (fun c => decide (c.1 = b.1)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro c hc
        rw [hb_eq b₀ (by simp) c hc]
        have hne : b₀.1 ≠ b.1 := fun h => hkeys.1 (h ▸ List.mem_map_of_mem hb_bs)
        simp [hne]
      simp [h1, ih']

lemma decompProp_of_multiLevel {G : Cited.Graph} (h1n : 1 ≤ G.n) (hnm : G.n < G.m)
    {φ : ℝ} (recs : List DecompLevelRec) (remG_0 : Cited.Graph) (remIdx_0 level : List ℕ)
    (ℓ : ℕ) (hℓ : ℓ = Nat.log 2 (G.m / G.n) + 1)
    (hlen : recs.length = ℓ)
    (hrem0_n : remG_0.n = G.n) (hrem0_m : remG_0.m ≤ G.n)
    (hrem0_edges : remG_0.edges = remIdx_0.map fun j => G.edges.getD j (0, 0))
    (hrem0_pw : remIdx_0.Pairwise (· < ·)) (hrem0_lt : ∀ a ∈ remIdx_0, a < G.m)
    (_hlvl_len : level.length = G.m)
    (hrecs : ∀ (t : ℕ) (ht : t < recs.length),
      recs[t].lvl = t + 1 ∧
      (∀ comp ∈ recs[t].rawComps, comp.1 = t + 1 ∧ comp.2.Pairwise (· < ·) ∧ 2 ≤ comp.2.length) ∧
      recs[t].rawComps.map (fun c => c.2.toFinset) = recs[t].validRs ∧
      recs[t].keptIdx.Pairwise (· < ·) ∧
      (∀ a ∈ recs[t].keptIdx, a < G.m) ∧
      recs[t].Gi.n = G.n ∧
      recs[t].Gi.edges = (recs[t].keptIdx.map fun j => G.edges.getD j (0, 0)) ∧
      recs[t].Gi.m ≤ 2 ^ (t + 1) * G.n ∧
      recs[t].validRs.Pairwise Disjoint ∧
      (∀ R ∈ recs[t].validRs,
        R ⊆ G.verts ∧ 2 ≤ R.card ∧ recs[t].Gi.IsConductanceExpanderOn R φ ∧
          (∀ x ∈ R, φ * 2 ^ (t + 1) ≤ (recs[t].Gi.degIn R x : ℝ)) ∧
          ∀ e ∈ recs[t].Gi.edges, e.1 ∈ R ↔ e.2 ∈ R) ∧
      (∀ e ∈ recs[t].Gi.edges, ∃ R ∈ recs[t].validRs, e.1 ∈ R ∧ e.2 ∈ R))
    (hlvl_spec : ∀ a < G.m,
      (level.getD a 0 = 0 ↔ a ∈ remIdx_0) ∧
      (∀ (t : ℕ) (ht : t < recs.length), level.getD a 0 = t + 1 ↔ a ∈ recs[t].keptIdx) ∧
      (level.getD a 0 = 0 ∨ ∃ (t : ℕ) (_ : t < recs.length), level.getD a 0 = t + 1)) :
    let rawComps := (recs.map (·.rawComps)).flatten
    rawComps.Pairwise (fun a b => a.1 ≤ b.1) ∧
    (∀ c ∈ rawComps, 1 ≤ c.1 ∧ c.1 ≤ ℓ ∧ c.2.Pairwise (· < ·) ∧ 2 ≤ c.2.length) ∧
    DecomposeProp 1 G (mkDecomposeOutput ℓ level rawComps) φ := by
  have hℓ_bds := decompose_ell_bounds h1n hnm
  let blocks : List (ℕ × List (ℕ × List ℕ)) := recs.map fun r => (r.lvl, r.rawComps)
  have hblocks_eq : (recs.map (·.rawComps)).flatten = (blocks.map (·.2)).flatten := by
    simp [blocks, List.map_map, Function.comp_def]
  have hblocks_pw : blocks.Pairwise (fun a b => a.1 ≤ b.1) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [blocks, List.length_map] at hi hj
    simp only [blocks, List.getElem_map]
    rw [(hrecs i hi).1, (hrecs j hj).1]
    omega
  have hblocks_mem : ∀ b ∈ blocks, ∀ c ∈ b.2, c.1 = b.1 := by
    intro b hb c hc
    rw [List.mem_map] at hb
    rcases hb with ⟨r, hr, rfl⟩
    rw [List.mem_iff_getElem] at hr
    rcases hr with ⟨t, ht, rfl⟩
    rw [(hrecs t ht).1]
    exact ((hrecs t ht).2.1 c hc).1
  have hkeys : (blocks.map (·.1)).Nodup := by
    rw [List.nodup_iff_getElem?_ne_getElem?]
    intro i j hij hj
    simp only [blocks, List.map_map, List.length_map, Function.comp_def] at hj ⊢
    intro heq
    have hi : i < recs.length := by omega
    rw [List.getElem?_eq_getElem (by simp; exact hi),
      List.getElem?_eq_getElem (by simp; exact hj)] at heq
    simp only [List.getElem_map] at heq
    have heq' := Option.some.inj heq
    rw [(hrecs i hi).1, (hrecs j hj).1] at heq'
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hblocks_eq]
    exact pairwise_le_flatten_of_blocks blocks hblocks_pw hblocks_mem
  · intro c hc
    rw [List.mem_flatten] at hc
    rcases hc with ⟨rc, hrc, hcrc⟩
    rw [List.mem_map] at hrc
    rcases hrc with ⟨r, hr, rfl⟩
    rw [List.mem_iff_getElem] at hr
    rcases hr with ⟨t, ht, rfl⟩
    have hc_spec := (hrecs t ht).2.1 c hcrc
    refine ⟨by omega, by omega, hc_spec.2.1, hc_spec.2.2⟩
  · dsimp only [DecomposeProp]
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [mkDecomposeOutput]
      have h1 : (ℓ : ℝ) ≤ (Nat.log 2 (G.m + 2) + 1 : ℕ) := by
        exact_mod_cast (by rw [hℓ]; exact hℓ_bds.2.1 : ℓ ≤ Nat.log 2 (G.m + 2) + 1)
      push_cast at h1
      linarith
    · intro j hj
      dsimp only [mkDecomposeOutput]
      rcases (hlvl_spec j hj).2.2 with h0 | ⟨t, ht, ht_eq⟩
      · rw [h0]; omega
      · rw [ht_eq]; omega
    · intro i hi
      dsimp only [mkDecomposeOutput] at hi
      by_cases hi0 : i = 0
      · subst i
        have hed0 : DecomposeOutput.edgesAt G (mkDecomposeOutput ℓ level (recs.map (·.rawComps)).flatten) 0 =
            remIdx_0 := by
          apply pairwise_lt_eq_of_mem_iff
          · exact List.Pairwise.filter _ List.pairwise_lt_range
          · exact hrem0_pw
          · intro a
            simp only [DecomposeOutput.edgesAt, mkDecomposeOutput, List.mem_filter, List.mem_range]
            constructor
            · rintro ⟨ha, ha0⟩; exact (hlvl_spec a ha).1.mp (by simpa using ha0)
            · intro ha; exact ⟨hrem0_lt a ha, (by simpa using (hlvl_spec a (hrem0_lt a ha)).1.mpr ha)⟩
        have hg0 := graphAt_eq_of_edges_eq hed0 hrem0_n hrem0_edges
        rw [hg0]
        simpa using hrem0_m
      · have ht_len : i - 1 < recs.length := by omega
        have hrec := hrecs (i - 1) ht_len
        have hedi : DecomposeOutput.edgesAt G (mkDecomposeOutput ℓ level (recs.map (·.rawComps)).flatten) i =
            recs[i - 1].keptIdx := by
          apply pairwise_lt_eq_of_mem_iff
          · exact List.Pairwise.filter _ List.pairwise_lt_range
          · exact hrec.2.2.2.1
          · intro a
            simp only [DecomposeOutput.edgesAt, mkDecomposeOutput, List.mem_filter, List.mem_range]
            have hii : i - 1 + 1 = i := by omega
            constructor
            · rintro ⟨ha, hai⟩
              have hmem : level.getD a 0 = i := by simpa using hai
              exact ((hlvl_spec a ha).2.1 (i - 1) ht_len).mp (hmem.trans hii.symm)
            · intro ha
              refine ⟨hrec.2.2.2.2.1 a ha, ?_⟩
              have hmem : level.getD a 0 = i :=
                (((hlvl_spec a (hrec.2.2.2.2.1 a ha)).2.1 (i - 1) ht_len).mpr ha).trans hii
              simpa [hmem]
        have hgi := graphAt_eq_of_edges_eq hedi hrec.2.2.2.2.2.1 hrec.2.2.2.2.2.2.1
        rw [hgi]
        simpa [show i - 1 + 1 = i by omega] using hrec.2.2.2.2.2.2.2.1
    · intro i hi0 hiℓ
      dsimp only [mkDecomposeOutput] at hiℓ
      have ht_len : i - 1 < recs.length := by omega
      have hrec := hrecs (i - 1) ht_len
      have hedi : DecomposeOutput.edgesAt G (mkDecomposeOutput ℓ level (recs.map (·.rawComps)).flatten) i =
          recs[i - 1].keptIdx := by
        apply pairwise_lt_eq_of_mem_iff
        · exact List.Pairwise.filter _ List.pairwise_lt_range
        · exact hrec.2.2.2.1
        · intro a
          simp only [DecomposeOutput.edgesAt, mkDecomposeOutput, List.mem_filter, List.mem_range]
          have hii : i - 1 + 1 = i := by omega
          constructor
          · rintro ⟨ha, hai⟩
            have hmem : level.getD a 0 = i := by simpa using hai
            exact ((hlvl_spec a ha).2.1 (i - 1) ht_len).mp (hmem.trans hii.symm)
          · intro ha
            refine ⟨hrec.2.2.2.2.1 a ha, ?_⟩
            have hmem : level.getD a 0 = i :=
              (((hlvl_spec a (hrec.2.2.2.2.1 a ha)).2.1 (i - 1) ht_len).mpr ha).trans hii
            simpa [hmem]
      have hgi := graphAt_eq_of_edges_eq hedi hrec.2.2.2.2.2.1 hrec.2.2.2.2.2.2.1
      have hcomps_eq : (mkDecomposeOutput ℓ level (recs.map (·.rawComps)).flatten).comps i =
          recs[i - 1].validRs := by
        dsimp only [mkDecomposeOutput]
        rw [hblocks_eq]
        have hmem_b : (recs[i - 1].lvl, recs[i - 1].rawComps) ∈ blocks := by
          simp only [blocks, List.mem_map]
          exact ⟨recs[i - 1], List.getElem_mem ht_len, rfl⟩
        have hblk := filter_eq_of_blocks blocks hkeys hblocks_mem (recs[i - 1].lvl, recs[i - 1].rawComps) hmem_b
        have hlvl_i : recs[i - 1].lvl = i := by rw [hrec.1]; omega
        rw [hlvl_i] at hblk
        rw [hblk, hrec.2.2.1]
      rw [hcomps_eq, hgi]
      have hii : i - 1 + 1 = i := by omega
      have hR' := hrec.2.2.2.2.2.2.2.2.2.1
      have hE' := hrec.2.2.2.2.2.2.2.2.2.2
      refine ⟨hrec.2.2.2.2.2.2.2.2.1, fun R hR => ?_, hE'⟩
      have hRR := hR' R hR
      rw [hii] at hRR
      exact hRR

/-! ## 5. Total Level Cost Bound & Polynomial Space Allocation -/

private lemma natLog2_four_mul_add_two_le {m : ℕ} (h1m : 1 ≤ m) :
    (Nat.log 2 (4 * m + 2) : ℝ) ≤ 8 * Real.log ((m : ℝ) + 2) := by
  have h2 : (2 ^ Nat.log 2 (4 * m + 2) : ℝ) ≤ (4 * m + 2 : ℕ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h3 : (Nat.log 2 (4 * m + 2) : ℝ) * Real.log 2 ≤ Real.log ((4 * m + 2 : ℕ) : ℝ) := by
    have := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at this
  have h4 := real_log_add_two_le_four_mul h1m (by omega : 4 * m ≤ 4 * m)
  have hmul : (Nat.log 2 (4 * m + 2) : ℝ) * (1 / 2 : ℝ) ≤
      (Nat.log 2 (4 * m + 2) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left half_lt_real_log_two.le (Nat.cast_nonneg _)
  push_cast at h3 h4
  linarith

lemma levelCost_le_subpoly {C₀_p C₁_p C₀_c C_c : ℝ}
    (hC0p : 0 ≤ C₀_p) (_hC1p : 1 ≤ C₁_p) (_hC0c : 0 ≤ C₀_c) (_hCc : 1 ≤ C_c)
    {n m curM D D_phi c_cited_ub scaleP c_ws c_cited : ℕ}
    (h1m : 1 ≤ m) (hnm : n < m) (hcurM : curM ≤ m) (hDn : D * n ≤ 2 * m)
    (hDphi : (D_phi : ℝ) ≤ C₁_p * subpolyB1 C₀_p m)
    (hc_ub : (c_cited_ub : ℝ) ≤ C_c * (m : ℝ) * subpolyB1 C₀_c m)
    (hc_ws : c_ws ≤ 5 * c_cited * (Nat.log 2 (n + m + 206) + 1)) :
    (levelCost n curM D D_phi c_cited_ub scaleP c_ws : ℝ) ≤
      (2000 * (100 + (scaleP : ℝ) * (C_c + (c_cited : ℝ) + 10) +
        (144 * 36 * (64 * C₁_p + 36) ^ 2))) *
        (m : ℝ) * subpolyB1 (max C₀_c (2 * C₀_p + 4)) m := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h1m
  let C_sb := max C₀_c (2 * C₀_p + 4)
  have hCsb_nn : 0 ≤ C_sb := le_trans (by positivity) (le_max_right _ _)
  have hC4 : 4 ≤ C_sb := le_trans (by linarith) (le_max_right _ _)
  have hC2p4 : 2 * C₀_p + 4 ≤ C_sb := le_max_right _ _
  have hC0c_le : C₀_c ≤ C_sb := le_max_left _ _
  have hsb1 : (1 : ℝ) ≤ subpolyB1 C_sb m := one_le_subpolyB1 hCsb_nn m
  have hsb_4 : subpolyB1 4 m ≤ subpolyB1 C_sb m := subpolyB1_mono_C hC4 m
  have hsb_c : subpolyB1 C₀_c m ≤ subpolyB1 C_sb m := subpolyB1_mono_C hC0c_le m
  have hsb_p2 : subpolyB1 C₀_p m ^ 2 * subpolyB1 4 m ≤ subpolyB1 C_sb m := by
    rw [subpolyB1_sq, subpolyB1_mul]
    exact subpolyB1_mono_C hC2p4 m
  have hm_r : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt hnm
  have hcurM_r : (curM : ℝ) ≤ (m : ℝ) := by exact_mod_cast hcurM
  have hDn_r : (D : ℝ) * (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hDn
  have hmtw_r : (curM : ℝ) + (D : ℝ) * (n : ℝ) ≤ 3 * (m : ℝ) := by linarith
  have hlogm_half : (1 / 2 : ℝ) ≤ Real.log ((m : ℝ) + 2) := by
    have h := Real.log_le_log (by norm_num) (show (2 : ℝ) ≤ (m : ℝ) + 2 by exact_mod_cast (by omega : 2 ≤ m + 2))
    exact le_trans half_lt_real_log_two.le h
  have hnatLog4m := natLog2_four_mul_add_two_le h1m
  have hlog2m_le : (Nat.log 2 (2 * curM + 1) + 1 : ℝ) ≤ 12 * Real.log ((m : ℝ) + 2) := by
    have h1 : (Nat.log 2 (2 * curM + 1) : ℝ) ≤ Nat.log 2 (4 * m + 2) := by
      exact_mod_cast Nat.log_mono_right (by omega : 2 * curM + 1 ≤ 4 * m + 2)
    linarith
  have hlog3m_le : (Nat.log 2 (curM + D * n + 1) + 2 : ℝ) ≤ 12 * Real.log ((m : ℝ) + 2) := by
    have h1 : (Nat.log 2 (curM + D * n + 1) : ℝ) ≤ Nat.log 2 (4 * m + 2) := by
      exact_mod_cast Nat.log_mono_right (by omega : curM + D * n + 1 ≤ 4 * m + 2)
    linarith
  have hlogn_le : (Nat.log 2 (n + 2) : ℝ) ≤ 12 * Real.log ((m : ℝ) + 2) := by
    have h1 : (Nat.log 2 (n + 2) : ℝ) ≤ Nat.log 2 (4 * m + 2) := by
      exact_mod_cast Nat.log_mono_right (by omega : n + 2 ≤ 4 * m + 2)
    linarith
  have hlog_ws : (Nat.log 2 (n + m + 206) + 1 : ℝ) ≤ 40 * Real.log ((m : ℝ) + 2) := by
    have harg : ((n + m + 206 : ℕ) : ℝ) ≤ 208 * ((m : ℝ) + 2) := by push_cast; linarith
    have hpow2 : (2 ^ Nat.log 2 (n + m + 206) : ℝ) ≤ (n + m + 206 : ℕ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlog_nat : (Nat.log 2 (n + m + 206) : ℝ) * Real.log 2 ≤ Real.log ((n + m + 206 : ℕ) : ℝ) := by
      have := Real.log_le_log (by positivity) hpow2
      rwa [Real.log_pow] at this
    have hlog208 : Real.log ((n + m + 206 : ℕ) : ℝ) ≤ Real.log 208 + Real.log ((m : ℝ) + 2) := by
      have h := Real.log_le_log (by positivity) harg
      rwa [Real.log_mul (by norm_num) (by positivity)] at h
    have hl208 : Real.log 208 ≤ 8 := by
      have h256 : (208 : ℝ) ≤ 2 ^ (8 : ℕ) := by norm_num
      have h := Real.log_le_log (by norm_num) h256
      rw [Real.log_pow] at h
      push_cast at h
      have := real_log_two_lt_one; linarith
    have hmul : (Nat.log 2 (n + m + 206) : ℝ) * (1 / 2 : ℝ) ≤
        (Nat.log 2 (n + m + 206) : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left half_lt_real_log_two.le (Nat.cast_nonneg _)
    linarith
  have hsb_log : Real.log ((m : ℝ) + 2) ≤ 6 * subpolyB1 C_sb m := by
    have h2 : subpolyB1 2 m ≤ subpolyB1 C_sb m := subpolyB1_mono_C (by linarith) m
    linarith [real_log_add_two_le_sb m]
  have hprune_sq : (4 * (4 * (4 * (D_phi : ℝ) + 2) * (Nat.log 2 (2 * curM + 1) + 1 : ℝ) + 2) + 14) ^ 2 ≤
      (64 * C₁_p + 36) ^ 2 * 144 * 36 * subpolyB1 C_sb m := by
    have hsb_p : 1 ≤ subpolyB1 C₀_p m := one_le_subpolyB1 hC0p m
    have hinner : 4 * (4 * (4 * (D_phi : ℝ) + 2) * (Nat.log 2 (2 * curM + 1) + 1 : ℝ) + 2) + 14 ≤
        (64 * C₁_p + 36) * subpolyB1 C₀_p m * (12 * Real.log ((m : ℝ) + 2)) := by
      have hlog_nn : 0 ≤ (Nat.log 2 (2 * curM + 1) + 1 : ℝ) := by positivity
      have hD_le : 4 * (D_phi : ℝ) + 2 ≤ (4 * C₁_p + 2) * subpolyB1 C₀_p m := by linarith
      have h1 : 16 * (4 * (D_phi : ℝ) + 2) * (Nat.log 2 (2 * curM + 1) + 1 : ℝ) ≤
          16 * ((4 * C₁_p + 2) * subpolyB1 C₀_p m) * (12 * Real.log ((m : ℝ) + 2)) := by
        gcongr
      have h2 : (22 : ℝ) ≤ 4 * subpolyB1 C₀_p m * (12 * Real.log ((m : ℝ) + 2)) := by
        have h412 : 4 * 1 * (12 * (1 / 2 : ℝ)) ≤ 4 * subpolyB1 C₀_p m * (12 * Real.log ((m : ℝ) + 2)) := by
          gcongr
        linarith
      have hsum_eq : 16 * ((4 * C₁_p + 2) * subpolyB1 C₀_p m) * (12 * Real.log ((m : ℝ) + 2)) +
          4 * subpolyB1 C₀_p m * (12 * Real.log ((m : ℝ) + 2)) =
          (64 * C₁_p + 36) * subpolyB1 C₀_p m * (12 * Real.log ((m : ℝ) + 2)) := by ring
      have hlin_eq : 4 * (4 * (4 * (D_phi : ℝ) + 2) * (Nat.log 2 (2 * curM + 1) + 1 : ℝ) + 2) + 14 =
          16 * (4 * (D_phi : ℝ) + 2) * (Nat.log 2 (2 * curM + 1) + 1 : ℝ) + 22 := by ring
      linarith
    have hsq := pow_le_pow_left₀ (by positivity) hinner 2
    have hlog2 := log_add_two_sq_le_sb m
    have hrhs : ((64 * C₁_p + 36) * subpolyB1 C₀_p m * (12 * Real.log ((m : ℝ) + 2))) ^ 2 =
        (64 * C₁_p + 36) ^ 2 * 144 * (subpolyB1 C₀_p m ^ 2 * Real.log ((m : ℝ) + 2) ^ 2) := by ring
    rw [hrhs] at hsq
    have hsp2 : subpolyB1 C₀_p m ^ 2 * Real.log ((m : ℝ) + 2) ^ 2 ≤ 36 * subpolyB1 C_sb m := by
      have hA : subpolyB1 C₀_p m ^ 2 * Real.log ((m : ℝ) + 2) ^ 2 ≤
          subpolyB1 C₀_p m ^ 2 * (36 * subpolyB1 4 m) := by gcongr
      linarith [hsb_p2]
    have hmul_eq := mul_le_mul_of_nonneg_left hsp2
      (by positivity : 0 ≤ (64 * C₁_p + 36) ^ 2 * 144)
    linarith
  have hcw_r : (c_ws : ℝ) ≤ 200 * (c_cited : ℝ) * Real.log ((m : ℝ) + 2) := by
    have hc : (c_ws : ℝ) ≤ 5 * (c_cited : ℝ) * (Nat.log 2 (n + m + 206) + 1 : ℝ) := by
      exact_mod_cast hc_ws
    have hmul : 5 * (c_cited : ℝ) * (Nat.log 2 (n + m + 206) + 1 : ℝ) ≤
        5 * (c_cited : ℝ) * (40 * Real.log ((m : ℝ) + 2)) := by gcongr
    linarith
  have hc_ws_sb : (c_ws : ℝ) ≤ 1200 * (c_cited : ℝ) * (m : ℝ) * subpolyB1 C_sb m := by
    have h1 : 200 * (c_cited : ℝ) * Real.log ((m : ℝ) + 2) ≤
        200 * (c_cited : ℝ) * (6 * subpolyB1 C_sb m) := by gcongr
    have h2 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1m
    have h3 : (1200 * (c_cited : ℝ) * subpolyB1 C_sb m) * 1 ≤
        (1200 * (c_cited : ℝ) * subpolyB1 C_sb m) * (m : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  unfold levelCost
  push_cast
  have hm_sb : (m : ℝ) ≤ (m : ℝ) * subpolyB1 C_sb m := by
    calc (m : ℝ) = (m : ℝ) * 1 := by ring
      _ ≤ (m : ℝ) * subpolyB1 C_sb m := mul_le_mul_of_nonneg_left hsb1 hm_pos.le
  have hm1_sb : (1 : ℝ) ≤ (m : ℝ) * subpolyB1 C_sb m := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1m
    linarith
  have hcurM_sb : (curM : ℝ) ≤ (m : ℝ) * subpolyB1 C_sb m := le_trans hcurM_r hm_sb
  have hn_sb : (n : ℝ) ≤ (m : ℝ) * subpolyB1 C_sb m := le_trans hm_r hm_sb
  have hsp_cited : (c_cited_ub : ℝ) ≤ C_c * (m : ℝ) * subpolyB1 C_sb m := by
    have h1 : C_c * (m : ℝ) * subpolyB1 C₀_c m ≤ C_c * (m : ℝ) * subpolyB1 C_sb m :=
      mul_le_mul_of_nonneg_left hsb_c (by positivity)
    linarith
  have hlog3m_sb : (Nat.log 2 (curM + D * n + 1) + 2 : ℝ) ≤ 72 * (m : ℝ) * subpolyB1 C_sb m := by
    have h1 : (Nat.log 2 (curM + D * n + 1) + 2 : ℝ) ≤ 72 * subpolyB1 C_sb m := by linarith
    have h2 : (72 * subpolyB1 C_sb m) * 1 ≤ (72 * subpolyB1 C_sb m) * (m : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast h1m) (by positivity)
    linarith
  have hn_logn : (n : ℝ) * (2 * (Nat.log 2 (n + 2) : ℝ) + 1) ≤
      150 * (m : ℝ) * subpolyB1 C_sb m := by
    have h1 : 2 * (Nat.log 2 (n + 2) : ℝ) + 1 ≤ 150 * subpolyB1 C_sb m := by linarith
    have h2 : (n : ℝ) * (2 * (Nat.log 2 (n + 2) : ℝ) + 1) ≤ (m : ℝ) * (150 * subpolyB1 C_sb m) :=
      mul_le_mul hm_r h1 (by positivity) hm_pos.le
    linarith
  have hcurM_prune : (590 + 720 * (4 * (4 * (4 * (D_phi : ℝ) + 2) * (Nat.log 2 (2 * curM + 1) + 1 : ℝ) + 2) + 14) ^ 2) *
      (curM : ℝ) ≤ (590 + 720 * (64 * C₁_p + 36) ^ 2 * 144 * 36) * (m : ℝ) * subpolyB1 C_sb m := by
    have h1 : 590 + 720 * (4 * (4 * (4 * (D_phi : ℝ) + 2) *
        (Nat.log 2 (2 * curM + 1) + 1 : ℝ) + 2) + 14) ^ 2 ≤
        (590 + 720 * (64 * C₁_p + 36) ^ 2 * 144 * 36) * subpolyB1 C_sb m := by
      have h590 : (590 : ℝ) ≤ 590 * subpolyB1 C_sb m := by linarith
      have h720 : 720 * (4 * (4 * (4 * (D_phi : ℝ) + 2) *
          (Nat.log 2 (2 * curM + 1) + 1 : ℝ) + 2) + 14) ^ 2 ≤
          720 * ((64 * C₁_p + 36) ^ 2 * 144 * 36 * subpolyB1 C_sb m) :=
        mul_le_mul_of_nonneg_left hprune_sq (by norm_num)
      linarith
    have h2 := mul_le_mul hcurM_r h1 (by positivity) hm_pos.le
    linarith
  have hn_prune : (n : ℝ) * (1100 + 400 * (4 * (4 * (4 * (D_phi : ℝ) + 2) *
      (Nat.log 2 (2 * curM + 1) + 1 : ℝ) + 2) + 14) ^ 2) ≤
      (1100 + 400 * (64 * C₁_p + 36) ^ 2 * 144 * 36) * (m : ℝ) * subpolyB1 C_sb m := by
    have h1 : 1100 + 400 * (4 * (4 * (4 * (D_phi : ℝ) + 2) *
        (Nat.log 2 (2 * curM + 1) + 1 : ℝ) + 2) + 14) ^ 2 ≤
        (1100 + 400 * (64 * C₁_p + 36) ^ 2 * 144 * 36) * subpolyB1 C_sb m := by
      have h11 : (1100 : ℝ) ≤ 1100 * subpolyB1 C_sb m := by linarith
      have h400 : 400 * (4 * (4 * (4 * (D_phi : ℝ) + 2) *
          (Nat.log 2 (2 * curM + 1) + 1 : ℝ) + 2) + 14) ^ 2 ≤
          400 * ((64 * C₁_p + 36) ^ 2 * 144 * 36 * subpolyB1 C_sb m) :=
        mul_le_mul_of_nonneg_left hprune_sq (by norm_num)
      linarith
    have h2 := mul_le_mul hm_r h1 (by positivity) hm_pos.le
    linarith
  have hscale : (scaleP : ℝ) * (2 * (c_cited_ub : ℝ) + (5 + 2 * ((curM : ℝ) + (D : ℝ) * (n : ℝ))) + (c_ws : ℝ) + 1) ≤
      (scaleP : ℝ) * (2 * C_c + 12 + 1200 * (c_cited : ℝ)) * (m : ℝ) * subpolyB1 C_sb m := by
    have hinner : 2 * (c_cited_ub : ℝ) + (5 + 2 * ((curM : ℝ) + (D : ℝ) * (n : ℝ))) + (c_ws : ℝ) + 1 ≤
        (2 * C_c + 12 + 1200 * (c_cited : ℝ)) * (m : ℝ) * subpolyB1 C_sb m := by
      have h6m : (5 + 2 * ((curM : ℝ) + (D : ℝ) * (n : ℝ)) + 1 : ℝ) ≤
          12 * (m : ℝ) * subpolyB1 C_sb m := by linarith
      linarith
    have hmul := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ (scaleP : ℝ))
    linarith
  have hscale2 : (scaleP : ℝ) * (2 * C_c + 12 + 1200 * (c_cited : ℝ)) ≤
      2000 * ((scaleP : ℝ) * (C_c + (c_cited : ℝ) + 10)) := by
    have hsp_nn : 0 ≤ (scaleP : ℝ) := Nat.cast_nonneg _
    have h1 : 2 * C_c + 12 + 1200 * (c_cited : ℝ) ≤ 2000 * (C_c + (c_cited : ℝ) + 10) := by
      have hcc_nn : 0 ≤ (c_cited : ℝ) := Nat.cast_nonneg _
      linarith
    calc (scaleP : ℝ) * (2 * C_c + 12 + 1200 * (c_cited : ℝ))
        ≤ (scaleP : ℝ) * (2000 * (C_c + (c_cited : ℝ) + 10)) :=
          mul_le_mul_of_nonneg_left h1 hsp_nn
      _ = 2000 * ((scaleP : ℝ) * (C_c + (c_cited : ℝ) + 10)) := by ring
  have hscale_full : (scaleP : ℝ) * (2 * (c_cited_ub : ℝ) + (5 + 2 * ((curM : ℝ) + (D : ℝ) * (n : ℝ))) +
      (c_ws : ℝ) + 1) ≤
      2000 * ((scaleP : ℝ) * (C_c + (c_cited : ℝ) + 10)) * (m : ℝ) * subpolyB1 C_sb m := by
    have hmsb_nn : 0 ≤ (m : ℝ) * subpolyB1 C_sb m := by positivity
    have h1 := mul_le_mul_of_nonneg_right hscale2 hmsb_nn
    linarith
  have hrest : 120 * ((curM : ℝ) + (D : ℝ) * (n : ℝ) + 1) +
      45 * (Nat.log 2 (curM + D * n + 1) + 2 : ℝ) +
      400 * (2 * (n : ℝ) + ((curM : ℝ) + (D : ℝ) * (n : ℝ)) + 2) +
      1000 * ((n : ℝ) * (2 * (Nat.log 2 (n + 2) : ℝ) + 1) + 1) +
      42 * (n : ℝ) + 200 * ((n : ℝ) + (curM : ℝ) + 1) +
      620 * (n : ℝ) + 125 * (curM : ℝ) + 260 ≤
      (2000 * 100 - 2000) * (m : ℝ) * subpolyB1 C_sb m := by
    have hmtw_sb : (curM : ℝ) + (D : ℝ) * (n : ℝ) ≤ 3 * (m : ℝ) * subpolyB1 C_sb m := by linarith
    linarith
  have hprune_const : (590 + 1100 + 1120 * (64 * C₁_p + 36) ^ 2 * 144 * 36) * (m : ℝ) * subpolyB1 C_sb m ≤
      (2000 + 2000 * (144 * 36 * (64 * C₁_p + 36) ^ 2)) * (m : ℝ) * subpolyB1 C_sb m := by
    have h1 : 590 + 1100 + 1120 * (64 * C₁_p + 36) ^ 2 * 144 * 36 ≤
        2000 + 2000 * (144 * 36 * (64 * C₁_p + 36) ^ 2) := by
      have hnn : 0 ≤ (64 * C₁_p + 36) ^ 2 := sq_nonneg _
      linarith
    have hmsb_nn : 0 ≤ (m : ℝ) * subpolyB1 C_sb m := by positivity
    have hmul := mul_le_mul_of_nonneg_right h1 hmsb_nn
    simpa only [mul_assoc] using hmul
  dsimp only [C_sb] at hscale_full hrest hprune_const hcurM_prune hn_prune
  linarith

/-! ## 6. Layout & Space Bounds -/

structure DecompLayout where
  statePtr : ℕ
  boundsAddr : ℕ
  lvlArrAddr : ℕ
  g0Addr : ℕ
  idx0Addr : ℕ
  g1Addr : ℕ
  idx1Addr : ℕ
  twAddr : ℕ
  bufAddr : ℕ
  workAddr : ℕ
  keptVertAddr : ℕ
  arena₀ : ℕ
  zeroCursor₀ : ℕ

@[expose] def mkDecompLayout (h n m D_phi : ℕ) : DecompLayout :=
  let statePtr := h + 4 + 5 * m
  let boundsAddr := statePtr + 3
  let lvlArrAddr := boundsAddr + 2 * m + 6
  let g0Addr := lvlArrAddr + m
  let idx0Addr := g0Addr + 2 + 2 * m
  let g1Addr := idx0Addr + m
  let idx1Addr := g1Addr + 2 + 2 * m
  let twAddr := idx1Addr + m
  let bufAddr := twAddr + 6 + 8 * n + 18 * m
  let workAddr := bufAddr + groupBufSize n m
  let H_cap := 4 * (4 * D_phi + 2) * (Nat.log 2 (2 * m + 1) + 1) + 2
  let keptVertAddr := workAddr + partWorkSize n m H_cap
  let arena₀ := keptVertAddr + n
  let zeroCursor₀ := arena₀ + 4 * m
  { statePtr, boundsAddr, lvlArrAddr, g0Addr, idx0Addr, g1Addr, idx1Addr,
    twAddr, bufAddr, workAddr, keptVertAddr, arena₀, zeroCursor₀ }

@[expose] def decompSpace (C_phi c_cited n m : ℕ) : ℕ :=
  (100 + 64 * C_phi) * (n + m + 2) ^ 2 + (m + 3) * (1 + 2 * (416 * (n + m + 2)) ^ c_cited) + 2 * n + 10

lemma decompSpace_le_poly (C_phi c_cited n m : ℕ) :
    decompSpace C_phi c_cited n m ≤
      (100 + 64 * C_phi + 12 + 4 * 416 ^ c_cited) * (n + m + 2) ^ max 2 (c_cited + 1) := by
  unfold decompSpace
  set N := n + m + 2
  have hN2 : 2 ≤ N := by omega
  set e := max 2 (c_cited + 1)
  have hsq : N ^ 2 ≤ N ^ e := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have hcc : N ^ (c_cited + 1) ≤ N ^ e := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have hm3 : m + 3 ≤ 2 * N := by omega
  have h416 : (416 * N) ^ c_cited = 416 ^ c_cited * N ^ c_cited := Nat.mul_pow 416 N c_cited
  have hterm1 : (100 + 64 * C_phi) * N ^ 2 ≤ (100 + 64 * C_phi) * N ^ e :=
    Nat.mul_le_mul_left _ hsq
  have hterm2 : (m + 3) * (1 + 2 * (416 * N) ^ c_cited) ≤
      (2 + 4 * 416 ^ c_cited) * N ^ e := by
    have h1 : 1 + 2 * (416 * N) ^ c_cited ≤ (1 + 2 * 416 ^ c_cited) * N ^ c_cited := by
      have hNpow : 1 ≤ N ^ c_cited := Nat.one_le_pow _ _ (by omega)
      rw [h416]
      calc 1 + 2 * (416 ^ c_cited * N ^ c_cited)
          ≤ N ^ c_cited + 2 * 416 ^ c_cited * N ^ c_cited := by rw [← Nat.mul_assoc]; omega
        _ = (1 + 2 * 416 ^ c_cited) * N ^ c_cited := by ring
    calc (m + 3) * (1 + 2 * (416 * N) ^ c_cited)
        ≤ (2 * N) * ((1 + 2 * 416 ^ c_cited) * N ^ c_cited) := Nat.mul_le_mul hm3 h1
      _ = (2 + 4 * 416 ^ c_cited) * N ^ (c_cited + 1) := by rw [pow_succ']; ring
      _ ≤ (2 + 4 * 416 ^ c_cited) * N ^ e := Nat.mul_le_mul_left _ hcc
  have hterm3 : 2 * n + 10 ≤ 10 * N ^ e := by
    have hN1 : N ^ 1 ≤ N ^ e := Nat.pow_le_pow_right (by omega) (le_trans (by omega : 1 ≤ 2) (le_max_left _ _))
    simp only [pow_one] at hN1
    omega
  linarith [hterm1, hterm2, hterm3]

lemma layout_zeroCursor_le {h n m D_phi C_phi : ℕ}
    (hDphi : D_phi ≤ C_phi * (m + 2)) :
    (mkDecompLayout h n m D_phi).zeroCursor₀ - h ≤
      (100 + 64 * C_phi) * (n + m + 2) ^ 2 := by
  have heq : (mkDecompLayout h n m D_phi).zeroCursor₀ =
      h + (38 * n + 45 * m + 34 + 32 * (D_phi * (Nat.log 2 (2 * m + 1) + 1)) +
        16 * (Nat.log 2 (2 * m + 1) + 1)) := by
    simp only [mkDecompLayout, groupBufSize, partWorkSize, pruneWorkSpace]; ring
  rw [heq, Nat.add_sub_cancel_left]
  have hlog : Nat.log 2 (2 * m + 1) + 1 ≤ 2 * m + 1 := natLog2_add_one_le_self' (by omega)
  have h1 : D_phi * (Nat.log 2 (2 * m + 1) + 1) ≤ C_phi * ((m + 2) * (2 * m + 1)) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul hDphi hlog
  have h2 : (m + 2) * (2 * m + 1) ≤ 2 * (n + m + 2) ^ 2 := by nlinarith
  have h3 : 32 * (D_phi * (Nat.log 2 (2 * m + 1) + 1)) ≤ 64 * C_phi * (n + m + 2) ^ 2 :=
    calc 32 * (D_phi * (Nat.log 2 (2 * m + 1) + 1))
        ≤ 32 * (C_phi * (2 * (n + m + 2) ^ 2)) :=
          Nat.mul_le_mul_left 32 (le_trans h1 (Nat.mul_le_mul_left C_phi h2))
      _ = 64 * C_phi * (n + m + 2) ^ 2 := by ring
  have h4 : 38 * n + 45 * m + 34 + 16 * (Nat.log 2 (2 * m + 1) + 1) ≤ 100 * (n + m + 2) ^ 2 := by
    nlinarith
  linarith

lemma layout_splitDisjoint_g0 {h n m D_phi curM : ℕ} (hcurM : curM ≤ m) :
    let L := mkDecompLayout h n m D_phi
    SplitDisjoint L.g0Addr L.idx0Addr L.g1Addr L.idx1Addr L.lvlArrAddr L.bufAddr L.keptVertAddr n curM m := by
  dsimp only [mkDecompLayout, SplitDisjoint, groupBufSize]
  omega

lemma layout_splitDisjoint_g1 {h n m D_phi curM : ℕ} (hcurM : curM ≤ m) :
    let L := mkDecompLayout h n m D_phi
    SplitDisjoint L.g1Addr L.idx1Addr L.g0Addr L.idx0Addr L.lvlArrAddr L.bufAddr L.keptVertAddr n curM m := by
  dsimp only [mkDecompLayout, SplitDisjoint, groupBufSize]
  omega

end

end MinCostFlow.Expander
