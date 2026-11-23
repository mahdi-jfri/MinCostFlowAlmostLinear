module

public import MinCostFlow.HierPaths.BuildCostAll
public import MinCostFlow.HierPaths.PortsHost

/-!
# The root of the construction is the host of `lemma_2`

`buildHyp_root`: the root host `hostGraph` of `lemma_2` meets the conditions `BuildHyp` of the
construction, with the expansion `rootβ`: `min(φ, 1)/50` at the root and `1/(2 P_r)` below. The lemma `lemma_2` gives the size `2^x`, validity,
no loops, degree at most `11` and expansion `min(φ, 1)/50`. The other conditions are on the
numbers alone.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

namespace BuildParams

/-- The expansion asked at each depth: `min(φ, 1)/50` at the root, which `lemma_2` gives, and
`1/(2 P_r)` below, which `lemma_3` gives. -/
@[expose] noncomputable def rootβ (B : BuildParams) (cfg : ParamConfig) (φ : ℝ) : ℕ → ℝ
  | 0 => min φ 1 / 50
  | _ + 1 => 1 / (2 * PParam cfg B.M B.r : ℝ)

theorem buildHyp_root {B : BuildParams} {cfg : ParamConfig} {G : Graph} (hG : G.IsValid)
    (hm : 1 ≤ G.m) {φ : ℝ} (hφ : 0 < φ) (hcond : G.IsConductanceExpanderOn G.verts φ)
    (hx : hostSize G = 2 ^ B.x) {bh : ℕ → ℕ}
    (hbh : ∀ j, max 2 (2 / B.rootβ cfg φ j) ≤ (bh j : ℝ))
    (hdeg : 49 * B.L' + 2 ≤ B.Δ) (hL : 1 ≤ B.L) (hxL : B.x < B.L) (hxL' : B.x < B.L')
    (hsize : 2 ^ B.x ≤ (NOf B.M B.r) ^ B.r) (hcore : 49 * B.L' ≤ deltaParam B.M) :
    B.BuildHyp cfg (hostGraph ExplicitExpander.explicitGraph G) (B.rootβ cfg φ) bh := by
  obtain ⟨⟨hn, _, _, _⟩, hv, hl, hd, _, hexp, _⟩ := lemma_2 hG hm hφ hcond
  have hP : (0 : ℝ) < PParam cfg B.M B.r := by exact_mod_cast one_le_PParam cfg B.M B.r
  have hn' : (hostGraph ExplicitExpander.explicitGraph G).n = 2 ^ B.x := by rw [hn, hx]
  refine ⟨hn', hv, hl, fun v => (hd v).trans (by omega), ?_, ?_, fun _ => le_rfl, hbh, hdeg, hL,
    hxL, hxL', hsize, hcore⟩
  · have hverts : (hostGraph ExplicitExpander.explicitGraph G).verts = Finset.range (2 ^ B.x) := by
      rw [Graph.verts, hn']
    rw [← hverts]
    exact hexp
  · intro j
    cases j with
    | zero =>
      have : 0 < min φ 1 := lt_min hφ one_pos
      simp only [rootβ]
      positivity
    | succ j =>
      simp only [rootβ]
      positivity

end BuildParams

end MinCostFlow.HierPaths
