module

public import MinCostFlow.HierPaths.InitModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The `Init` model: the cost after the static construction

After the static construction, `Init` flattens every connector walk to the root host
(`flatSteps`), projects it to the input graph (one step per root edge), and builds the arrays
(`initIndexSteps`). `initRestSteps` adds these. The main result, `initRestSteps_le_gamma`: with the
numbers of `HierPaths/Params.lean` this is at most `63 · m · Γ`.

The count: there are `N ≤ h · B · P` connectors (`card_connRecs_le`), flattening one takes at most
`2 h λ` steps (`flatSteps_le` and `lemma_5_length`), its projection and its share of the arrays take
`O(λ)` steps, and the keys of the arrays number `O(m)`. Then
`h · B · λ · (2h + 12) ≤ 12 · (h + 1)(B + 1)² H U^{h+1}` because `h + 1 ≤ U`, and the right side is
`12` times the factor `initFactor`, which is at most `Γ` (`initFactor_le_gamma`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The connectors with their local data: depth, group, children and the matched pair with its
local walk, in the order of `connRecs`. -/
def connLocal (H : HierData) (x b : ℕ) : List (ℕ × ℕ × ℕ × ℕ × (ℕ × ℕ × List ℕ)) :=
  (List.range (leafDepth x b)).flatMap fun t => (List.range (numGroups x b t)).flatMap fun g =>
    (childList x b t g).flatMap fun c => (childList x b t g).flatMap fun c' =>
      if c < c' then (H.conn t c c').map fun q => (t, g, c, c', q) else []

/-- The steps of flattening all connectors. -/
def flattenSteps (H : HierData) (x b : ℕ) : ℕ :=
  ((connLocal H x b).map fun p => flatSteps H x b p.1 p.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2).sum

/-- The steps of projecting all flattened connectors: one per root edge. -/
def projSteps (H : HierData) (x b : ℕ) : ℕ :=
  ((connRecs H x b).map fun r => r.hwalk.length).sum

/-- The steps of `Init` after the static construction, for an input graph with `n` vertices and
`m` edges. -/
def initRestSteps (H : HierData) (x b : ℕ) (owner : ℕ → ℕ) (label : ℕ → Option ℕ) (n m : ℕ) :
    ℕ :=
  flattenSteps H x b + projSteps H x b + initIndexSteps H x b owner label n m

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner HierData

variable {x b : ℕ} {H : HierData}

theorem connRecs_eq_map : connRecs H x b = (connLocal H x b).map fun p =>
    (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1,
      flatWalk H x b p.1 p.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2⟩ : ConnRec) := by
  simp only [connRecs, connLocal, List.map_flatMap]
  congr 1; funext t; congr 1; funext g; congr 1; funext c; congr 1; funext c'
  unfold pairRecs
  split_ifs <;> simp

theorem length_connLocal : (connLocal H x b).length = (connRecs H x b).length := by
  rw [connRecs_eq_map, List.length_map]

theorem mem_connLocal {p : ℕ × ℕ × ℕ × ℕ × (ℕ × ℕ × List ℕ)} (hp : p ∈ connLocal H x b) :
    p.1 < leafDepth x b ∧ p.2.1 < numGroups x b p.1 ∧ p.2.2.1 ∈ childGroups x b p.1 p.2.1 ∧
      p.2.2.2.1 ∈ childGroups x b p.1 p.2.1 ∧ p.2.2.1 < p.2.2.2.1 ∧
        p.2.2.2.2 ∈ H.conn p.1 p.2.2.1 p.2.2.2.1 := by
  simp only [connLocal, List.mem_flatMap, List.mem_range, mem_childList] at hp
  obtain ⟨t, ht, g, hg, c, hc, c', hc', hp⟩ := hp
  split_ifs at hp with hcc
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ⟨ht, hg, hc, hc', hcc, hq⟩
  · simp at hp

/-- Flattening all connectors takes at most `N · 2 h · Hc U^h` steps. -/
theorem flattenSteps_le (hb : 0 < b) (hH : H.IsValid x b) {Hc U h : ℕ} (hHc : 1 ≤ Hc)
    (hU : 1 ≤ U) (hB : H.Bounds x b (lvlBound Hc U) (lvlBound Hc U) (lvlBound Hc U))
    (hh : leafDepth x b ≤ h) :
    flattenSteps H x b ≤ (connRecs H x b).length * (2 * h * (Hc * U ^ h)) := by
  unfold flattenSteps
  rw [← length_connLocal]
  refine sum_map_le_length_mul' fun p hp => ?_
  obtain ⟨ht, hg, hc, hc', hcc, hq⟩ := mem_connLocal hp
  have hs := one_lt_groupSize_of_lt_leafDepth hb ht
  have hW := hH.conn_walk _ _ hs hg _ hc _ hc' hcc _ hq
  refine (flatSteps_le hH hB (one_le_lvlBound hHc hU) hs hg hW).trans ?_
  have hlen := hB.conn_length _ _ hs hg _ hc _ hc' hcc _ hq
  have h1 : p.2.2.2.2.2.2.length * ∏ k ∈ Finset.range p.1, lvlBound Hc U k ≤ Hc * U ^ h := by
    calc _ ≤ lvlBound Hc U p.1 * ∏ k ∈ Finset.range p.1, lvlBound Hc U k :=
          Nat.mul_le_mul_right _ hlen
      _ = Hc * U ^ (p.1 + 1) := lvlBound_mul_prod Hc U p.1
      _ ≤ Hc * U ^ h := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hU (by omega))
  calc p.1 * (2 * (p.2.2.2.2.2.2.length * ∏ k ∈ Finset.range p.1, lvlBound Hc U k))
      ≤ h * (2 * (Hc * U ^ h)) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ h1)
    _ = 2 * h * (Hc * U ^ h) := by ring

/-- Each stored root walk has at most `Hc U^h` edges. -/
theorem hwalk_length_le (hb : 0 < b) (hH : H.IsValid x b) {Hc U h : ℕ} (hU : 1 ≤ U)
    (hB : H.Bounds x b (lvlBound Hc U) (lvlBound Hc U) (lvlBound Hc U))
    (hh : leafDepth x b ≤ h) {r : ConnRec} (hr : r ∈ connRecs H x b) :
    r.hwalk.length ≤ Hc * U ^ h := by
  obtain ⟨t, ht, g, hg, c, hc, c', hc', hcc, q, hq, rfl⟩ := mem_connRecs.mp hr
  exact lemma_5_length hH hU hB (by omega) (one_lt_groupSize_of_lt_leafDepth hb ht) hg hc hc'
    hcc hq

/-- The arithmetic of the final bound. -/
private theorem arith_bound {N h B P lam Hc U m n : ℕ} (hN : N ≤ h * B * P) (hP : P ≤ 4 * m)
    (hn : n ≤ 2 * m) (hU : h + 1 ≤ U) (hlam : lam = Hc * U ^ h) :
    N * lam * (2 * h + 12) + 3 * P + m + n ≤
      48 * m * ((h + 1) * (B + 1) ^ 2 * Hc * U ^ (h + 1)) + 15 * m := by
  have hB : B ≤ (B + 1) ^ 2 := by nlinarith
  have hh : h * (2 * h + 12) ≤ 12 * (h + 1) * U := by nlinarith
  have key : h * B * (2 * h + 12) ≤ 12 * (h + 1) * (B + 1) ^ 2 * U := by
    calc h * B * (2 * h + 12) = (h * (2 * h + 12)) * B := by ring
      _ ≤ (12 * (h + 1) * U) * (B + 1) ^ 2 := Nat.mul_le_mul hh hB
      _ = 12 * (h + 1) * (B + 1) ^ 2 * U := by ring
  have h1 : N * lam * (2 * h + 12) ≤ 4 * m * (12 * (h + 1) * (B + 1) ^ 2 * U) * lam := by
    calc N * lam * (2 * h + 12) ≤ h * B * P * lam * (2 * h + 12) := by gcongr
      _ = P * (h * B * (2 * h + 12)) * lam := by ring
      _ ≤ 4 * m * (12 * (h + 1) * (B + 1) ^ 2 * U) * lam := by gcongr
  have h2 : 4 * m * (12 * (h + 1) * (B + 1) ^ 2 * U) * lam =
      48 * m * ((h + 1) * (B + 1) ^ 2 * Hc * U ^ (h + 1)) := by
    rw [hlam, pow_succ]; ring
  omega

/-- The depth is below the local bound: `h + 1 ≤ U` for `a ≥ 1`. -/
theorem succ_depthOf_le_uOf {a : ℕ} (ha : 1 ≤ a) (m : ℕ) : depthOf m + 1 ≤ uOf a m := by
  have hv : 1 ≤ vxOf m := Nat.clog_pos (by norm_num) (by omega)
  have h1 : depthOf m ≤ a * depthOf m * vxOf m := by
    calc depthOf m = 1 * depthOf m * 1 := by ring
      _ ≤ a * depthOf m * vxOf m := by gcongr
  unfold uOf
  calc depthOf m + 1 ≤ 2 ^ depthOf m := Nat.lt_two_pow_self
    _ ≤ 2 ^ (a * depthOf m * vxOf m) := Nat.pow_le_pow_right (by norm_num) h1

theorem one_le_hOf' (d : ℕ) : 1 ≤ hOf d := by
  unfold hOf; exact Nat.one_le_pow _ _ (by omega)

/-- **The cost of `Init` after the static construction.** With the local bounds
(`uOf a m`, and `hOf d · uOf a m` at the root), at most `63 · m · Γ` steps, when the terminals
number at most `4m`, the vertices at most `2m`, and `m ≤ M`. -/
theorem initRestSteps_le_gamma (hb : 0 < b) (hH : H.IsValid x b) {a dd M : ℕ} (ha : 1 ≤ a)
    {G : Graph}
    (hB : H.Bounds x b (lvlBound (hOf dd) (uOf a G.m)) (lvlBound (hOf dd) (uOf a G.m))
      (lvlBound (hOf dd) (uOf a G.m)))
    (hh : leafDepth x b ≤ depthOf G.m) (hBb : 2 ^ b ≤ branchOf G.m) (hP : 2 ^ x ≤ 4 * G.m)
    (hn : G.n ≤ 2 * G.m) (hmM : G.m ≤ M) {owner : ℕ → ℕ} {label : ℕ → Option ℕ}
    (hproj : IsProjection G (H.host 0 0).edges owner label)
    (hown : ∀ p < 2 ^ x, owner p < G.n) :
    initRestSteps H x b owner label G.n G.m ≤ 63 * G.m * gammaHP a dd M := by
  set N := (connRecs H x b).length
  set lam := hOf dd * uOf a G.m ^ depthOf G.m
  have hU := one_le_uOf a G.m
  have hlam1 : 1 ≤ lam := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := one_le_hOf' dd; omega) (by positivity))
  have hrec : ∀ r ∈ connRecs H x b, r.hwalk.length ≤ lam :=
    fun r hr => hwalk_length_le hb hH hU hB hh hr
  -- the four parts
  have hflat := flattenSteps_le hb hH (one_le_hOf' dd) hU hB hh
  have hproj' : projSteps H x b ≤ N * lam := sum_map_le_length_mul' hrec
  have hocc : (occRecs H x b owner label).length ≤ N * lam := by
    rw [length_occRecs]
    exact sum_map_le_length_mul' fun r hr =>
      (length_projectWalk_le _ _ _ _ _).trans (hrec r hr)
  have hfit := connSystem_fitsGraph hb hH hproj hown
  have hverts : ∑ k ∈ Finset.range N, ((connSystem H x b owner label).walk k).verts.length ≤
      N * (lam + 1) := by
    have : ∀ k ∈ Finset.range N,
        ((connSystem H x b owner label).walk k).verts.length ≤ lam + 1 := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      obtain ⟨_, _, hW⟩ := hfit.2 k hk'
      have hlen : ((connSystem H x b owner label).walk k).edges.length ≤ lam :=
        (length_projectWalk_le _ _ _ _ _).trans (hrec _ (getD_mem_connRecs hk'))
      rcases hW.2.2 with ⟨hv, _, _⟩ | ⟨_, hv, _⟩
      · rw [hv]; exact Nat.zero_le _
      · omega
    calc _ ≤ ∑ _k ∈ Finset.range N, (lam + 1) := Finset.sum_le_sum this
      _ = N * (lam + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hNle : N ≤ depthOf G.m * branchOf G.m * 2 ^ x := by
    calc N ≤ leafDepth x b * (2 ^ b * 2 ^ x) := card_connRecs_le hb hH
      _ ≤ depthOf G.m * (branchOf G.m * 2 ^ x) :=
          Nat.mul_le_mul hh (Nat.mul_le_mul_right _ hBb)
      _ = _ := by ring
  have htotal : initRestSteps H x b owner label G.n G.m ≤
      N * lam * (2 * depthOf G.m + 12) + 3 * 2 ^ x + G.m + G.n := by
    unfold initRestSteps initIndexSteps bucketSteps
    have e1 : N * (2 * depthOf G.m * lam) = N * lam * (2 * depthOf G.m) := by ring
    have e2 : N * lam * (2 * depthOf G.m + 12) = N * lam * (2 * depthOf G.m) + 12 * (N * lam) := by
      ring
    have e3 : N * (lam + 1) = N * lam + N := by ring
    have e4 : N ≤ N * lam := Nat.le_mul_of_pos_right _ hlam1
    rw [e1] at hflat
    rw [e3] at hverts
    rw [e2, show (connRecs H x b).length = N from rfl]
    omega
  have harith := arith_bound (Hc := hOf dd) hNle hP hn (succ_depthOf_le_uOf ha G.m) rfl
  have hinit := initFactor_le_gamma a dd hmM
  unfold initFactor at hinit
  have hΓ : 1 ≤ gammaHP a dd M := le_trans (by omega) (max_two_le_gammaHP a dd M)
  calc initRestSteps H x b owner label G.n G.m
      ≤ 48 * G.m * ((depthOf G.m + 1) * (branchOf G.m + 1) ^ 2 * hOf dd *
          uOf a G.m ^ (depthOf G.m + 1)) + 15 * G.m := htotal.trans harith
    _ ≤ 48 * G.m * gammaHP a dd M + 15 * G.m * gammaHP a dd M := by
        refine Nat.add_le_add (Nat.mul_le_mul_left _ hinit) ?_
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hΓ)
    _ = 63 * G.m * gammaHP a dd M := by ring

end MinCostFlow.HierPaths
