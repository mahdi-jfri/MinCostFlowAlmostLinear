module

public import MinCostFlow.LowStretch.ProgClusterWalk3

/-!
# The highway of a cluster, split into light walks and steps

The special petal grows along the highway `c.hw` of the cluster. The record stores only its pairs
that are not light (`Cl.hwE`). Here we split the highway at these pairs: the steps `hwSt t hw`
are the pairs that are not light, each with its two ends, and the highway is a `HwDec` with these
steps (`IsHighway.hwDec`). The stored highway is the list of these steps with their flags
(`hwE_eq_hwSt`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

variable (G) in
/-- The steps of the walk `hw` from `t` whose pairs are not light: the pair and its two ends. -/
def hwSt (θ : ℕ) : ℕ → List ℕ → List (ℕ × ℕ × ℕ)
  | _, [] => []
  | t, p :: hw => (if θ ≤ G.pω p then [(p, t, G.other p t)] else []) ++ hwSt θ (G.other p t) hw

/-- The stored highway lists the steps with their flags. -/
theorem hwE_eq_hwSt (t : ℕ) (hw : List ℕ) (θ : ℕ) (half : Finset ℕ) :
    hwE G t hw θ half = (hwSt G θ t hw).map (stE half) := by
  induction hw generalizing t with
  | nil => simp [hwE_nil, hwSt]
  | cons p hw ih =>
    rw [hwE_cons, ih, hwSt, List.map_append]
    congr 1
    split_ifs <;> simp_all [stE]

/-- A light pair in front of a split highway. -/
theorem HwDec.light_cons {a b p : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ}
    (h : c.HwDec G b st hw) (hj : G.Joins p a b) (ha : a ∈ c.X) (hl : G.pω p < c.θ) :
    c.HwDec G a st (p :: hw) := by
  cases h with
  | nil hw0 => exact .nil (.cons ha hl hj hw0)
  | cons hw0 hj' hb hd hst => exact .cons (l := p :: _) (.cons ha hl hj hw0) hj' hb hd hst

/-- **A highway splits at its pairs that are not light.** -/
theorem IsHighway.hwDec {t : ℕ} {hw : List ℕ} (h : c.IsHighway G t hw) :
    c.HwDec G t (hwSt G c.θ t hw) hw := by
  induction hw generalizing t with
  | nil =>
    obtain ⟨hw0, -⟩ := h
    cases hw0 with
    | nil ha => exact .nil (.nil ha)
  | cons p hw ih =>
    obtain ⟨hw0, hd⟩ := h
    cases hw0 with
    | @cons _ b _ _ _ ha _ hj rest =>
      have hob : G.other p t = b := hj.other_eq
      have hrest : c.IsHighway G b hw := by
        refine ⟨rest, fun i hi => ?_⟩
        have := hd (i + 1) (by simp; omega)
        simp only [hv, PG.vtx, List.getD_cons_succ, hob] at this
        simpa [hv] using this
      have h0 := hd 0 (by simp)
      simp only [hv, PG.vtx, List.getD_cons_zero, List.getD_cons_succ, hob,
        PG.vtx_getD_zero] at h0
      have ih' := ih hrest
      rw [hwSt, hob]
      split_ifs with hθ
      · exact .cons (l := []) (.nil ha) hj rest.start_mem h0 ih'
      · exact HwDec.light_cons ih' hj ha (by omega)

/-- The steps of a highway have positive length. -/
theorem hwSt_pos (hG : G.Ok) {t : ℕ} {hw : List ℕ} (h : c.IsHighway G t hw) :
    ∀ s ∈ hwSt G c.θ t hw, 0 < c.len G s.1 := by
  induction hw generalizing t with
  | nil => simp [hwSt]
  | cons p hw ih =>
    obtain ⟨hw0, hd⟩ := h
    cases hw0 with
    | @cons _ b _ _ _ ha _ hj rest =>
      have hob : G.other p t = b := hj.other_eq
      have hrest : c.IsHighway G b hw := by
        refine ⟨rest, fun i hi => ?_⟩
        have := hd (i + 1) (by simp; omega)
        simp only [hv, PG.vtx, List.getD_cons_succ, hob] at this
        simpa [hv] using this
      intro s hs
      rw [hwSt, hob] at hs
      rcases List.mem_append.mp hs with hs | hs
      · split_ifs at hs with h1
        · simp only [List.mem_singleton] at hs
          subst hs
          obtain ⟨-, -, -, h2, h3⟩ := hG p hj.1
          have := half_le_len (c := c) (G := G) h1
          obtain ⟨k, hk⟩ := h2
          show 0 < c.len G p
          omega
        · simp at hs
      · exact ih hrest s hs

end Cl

end MinCostFlow.LowStretch
