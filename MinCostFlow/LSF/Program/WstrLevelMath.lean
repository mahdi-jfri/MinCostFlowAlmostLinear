module

public import MinCostFlow.LSF.Program.WstrMath
public import MinCostFlow.LSF.Program.LevelLoop
public import MinCostFlow.LSF.PathRoot
public import MinCostFlow.LSF.Components

/-!
# From the level loop to the stretches

This file links the output of `levelsProc` (`LevelLoop.lean`) to the stretches of the forests
`F_T(B_i, π)` of the model, where `B_i = levelRoots T₀ r₀ i`.

* `levelDist`: the distance that level `i` adds for an edge, so that the stretch is
  `1 + levelDist / ℓ e` (`stretch_eq_levelDist`).
* `rootSetIdx_level`: the flags of `levelFlagProc` describe `B_i`, when the depth array holds the
  depths in `T_H`.
* `levelRt_root`: the roots that `levelRt` describes are the roots of `F_T(B_i, π)`.
* `dRVal_bridge`: the block `dR x` holds `S` times the tree distance from `x` to its root.
* `accFold_bridge`: the accumulator of an edge after `K` levels holds `S` times the sum of the
  level distances, when the weighted depths are at most `M` and `4 M (K + 1)` fits in a block.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.Num

variable {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ}

/-- The distance that a forest with roots `R` adds for the pair `a, b`: the tree distance when
both have the same root, and otherwise the sum of the distances to the two roots. -/
noncomputable def levelDist (T : MGraph) (r : ℕ) (R : Finset ℕ) (π : ℕ → ℕ) (ℓ : ℕ → ℝ)
    (a b : ℕ) : ℝ :=
  let RF := rootedForestGivenRoots T r R π
  if RF.root a = RF.root b then walkLength ℓ (T.forestPath a b)
  else walkLength ℓ (T.forestPath a (RF.root a)) + walkLength ℓ (T.forestPath b (RF.root b))

lemma stretch_eq_levelDist {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) {R : Finset ℕ}
    (hR : IsBranchFree T r R) (hrR : r ∈ R) (π : ℕ → ℕ) (G : MGraph) (ℓ : ℕ → ℝ) {e : ℕ}
    (hu : G.tail e ∈ T.V) (hv : G.head e ∈ T.V) :
    (rootedForestGivenRoots T r R π).stretch G ℓ e =
      1 + levelDist T r R π ℓ (G.tail e) (G.head e) / ℓ e := by
  have hRS := forestGivenRoots_isRootedSpanningForest hT hR ⟨r, hrR⟩ π
  rw [forestGivenRoots_stretch hT hR hrR π (rt := (rootedForestGivenRoots T r R π).root)
    (fun x hx => MinCostFlow.LSF.rootedForest_root_spec hRS hx) G ℓ hu hv]
  unfold levelDist
  dsimp only
  split_ifs <;> rfl

/-- The flags of level `i` are those of `B_i`. -/
lemma levelFlag_iff (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {mem : ℕ → ℕ}
    {thDepPtr i : ℕ}
    (hthd : ∀ x < vList.length, mem (thDepPtr + x) =
      depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0))
    {x : ℕ} (hx : x < vList.length) :
    levelFlag mem thDepPtr i x = 1 ↔ vList.getD x 0 ∈ levelRoots T₀ (vList.getD r 0) i := by
  classical
  unfold levelFlag levelRoots
  rw [Finset.mem_filter, hthd x hx]
  constructor
  · intro h
    split_ifs at h with h1
    exact ⟨hI.getD_mem hx, by omega⟩
  · rintro ⟨-, h⟩
    rw [if_pos (by omega)]

/-- The root set and order facts for level `i`. -/
lemma rootSetIdx_level (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {mem : ℕ → ℕ}
    {thDepPtr i : ℕ} {π piv : ℕ → ℕ}
    (hthd : ∀ x < vList.length, mem (thDepPtr + x) =
      depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0))
    (hπ : IsEdgeOrder T₀ π) (hpiv : ∀ j < tM, π (fid j) = piv j) :
    RootSetIdx T₀ vList tM r fid (levelRoots T₀ (vList.getD r 0) i) π
      (levelFlag mem thDepPtr i) piv :=
  ⟨upClosure_levelRoots hI.hT ▸ upClosure_isBranchFree hI.hT levelRoots_subset,
    root_mem_levelRoots hI.hT, fun x hx => levelFlag_iff hI hthd hx, hπ, hpiv⟩

/-- The roots of `LevelRt` are the roots of the forest. -/
theorem levelRt_root (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {R : Finset ℕ}
    {π inR piv rt : ℕ → ℕ} (hS : RootSetIdx T₀ vList tM r fid R π inR piv)
    (h : LevelRt vList.length tM r par pe piv inR rt) :
    ∀ x < vList.length, rt x < vList.length ∧
      vList.getD (rt x) 0 = (rootedForestGivenRoots T₀ (vList.getD r 0) R π).root
        (vList.getD x 0) := by
  obtain ⟨mp, own, hmp, hown, hrt_r, hrule⟩ := h
  have hb := rt_bridge hI hS (fun x hx hxr => (hmp x hx hxr).2) hown hrt_r hrule
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hb x hx
  exact ⟨h1, (forestGivenRoots_root_eq_of_connected hI.hT hS.hR ⟨_, hS.hrR⟩ π
    (hI.getD_mem hx) h2 h3).symm⟩

/-- The block `dR x` holds `S` times the tree distance from `x` to its root. -/
theorem dRVal_bridge (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {h LB S ldBase : ℕ}
    {mem : ℕ → ℕ} {ℓ : ℕ → ℝ} {rt lx : ℕ → ℕ} (hℓ : ∀ f ∈ T₀.E, 0 ≤ ℓ f)
    (hLd : ∀ z < vList.length, (unsignedVal mem (ldBase + z * LB) h LB : ℝ) =
      S * wDepth T₀ (vList.getD r 0) ℓ (vList.getD z 0))
    {x : ℕ} (hx : x < vList.length) (hrt : rt x < vList.length) (hl : lx x < vList.length)
    (hlca : IsLcaOf par dep (lx x) x (rt x))
    (hfit : unsignedVal mem (ldBase + x * LB) h LB + unsignedVal mem (ldBase + rt x * LB) h LB <
      capacity h LB) :
    (dRVal h LB mem ldBase rt lx x : ℝ) =
      S * walkLength ℓ (T₀.forestPath (vList.getD x 0) (vList.getD (rt x) 0)) :=
  treeDist_bridge hI (Ld := fun z => unsignedVal mem (ldBase + z * LB) h LB) hℓ hLd hl hx hrt
    hlca hfit

/-- A tree distance is at most the sum of the two weighted depths. -/
lemma walkLength_le_wDepth_add (hT : IsRootedTree T₀ r) {ℓ : ℕ → ℝ} (hℓ : ∀ f ∈ T₀.E, 0 ≤ ℓ f)
    {a b : ℕ} (ha : a ∈ T₀.V) (hb : b ∈ T₀.V) :
    walkLength ℓ (T₀.forestPath a b) ≤ wDepth T₀ r ℓ a + wDepth T₀ r ℓ b := by
  rw [walkLength_forestPath_lca hT ℓ ha hb]
  have hl := lca_mem hT ha hb
  have h0 : 0 ≤ wDepth T₀ r ℓ (lca T₀ r a b) :=
    walkLength_nonneg_of_nonneg ℓ fun f hf =>
      hℓ f (walkEdges_forestPath_subset hT hl hT.2 hf)
  linarith

/-- The accumulator of an edge after `K` levels. -/
theorem accFold_bridge (hI : TreeIdx T₀ vList tM r fid tl hd par pe dep) {h LB S ldBase : ℕ}
    {mem : ℕ → ℕ} {euPtr evPtr duvBase accBase thDepPtr M K t : ℕ} {ℓ : ℕ → ℝ}
    {π piv : ℕ → ℕ} {rts lxs : ℕ → ℕ → ℕ} (hℓ : ∀ f ∈ T₀.E, 0 ≤ ℓ f)
    (hthd : ∀ x < vList.length, mem (thDepPtr + x) =
      depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0))
    (hπ : IsEdgeOrder T₀ π) (hpiv : ∀ j < tM, π (fid j) = piv j)
    (hLd : ∀ z < vList.length, (unsignedVal mem (ldBase + z * LB) h LB : ℝ) =
      S * wDepth T₀ (vList.getD r 0) ℓ (vList.getD z 0))
    (hM : ∀ z < vList.length, unsignedVal mem (ldBase + z * LB) h LB ≤ M)
    (hrts : ∀ k < K, LevelRt vList.length tM r par pe piv (levelFlag mem thDepPtr k) (rts k))
    (hlxs : ∀ k < K, ∀ x < vList.length, lxs k x < vList.length ∧
      IsLcaOf par dep (lxs k x) x (rts k x))
    (hu : mem (euPtr + t) < vList.length) (hv : mem (evPtr + t) < vList.length)
    (hduv : (unsignedVal mem (duvBase + t * LB) h LB : ℝ) = S * walkLength ℓ
      (T₀.forestPath (vList.getD (mem (euPtr + t)) 0) (vList.getD (mem (evPtr + t)) 0)))
    (hduvM : unsignedVal mem (duvBase + t * LB) h LB ≤ 2 * M)
    (hX0 : unsignedVal mem (accBase + t * LB) h LB = 0)
    (hcap : 4 * M * (K + 1) < capacity h LB) :
    ∀ k ≤ K, accFold h LB mem euPtr evPtr ldBase duvBase accBase rts lxs t k ≤ 4 * M * k ∧
      (accFold h LB mem euPtr evPtr ldBase duvBase accBase rts lxs t k : ℝ) =
        S * ∑ j ∈ Finset.range k, levelDist T₀ (vList.getD r 0)
          (levelRoots T₀ (vList.getD r 0) j) π ℓ (vList.getD (mem (euPtr + t)) 0)
          (vList.getD (mem (evPtr + t)) 0) := by
  set u := mem (euPtr + t) with hudef
  set v := mem (evPtr + t) with hvdef
  set g : ℕ → ℕ := fun x => vList.getD x 0 with hg
  have hSnn : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  intro k
  induction k with
  | zero =>
    intro _
    simp [accFold, hX0]
  | succ k ih =>
    intro hk
    obtain ⟨ihle, iheq⟩ := ih (by omega)
    have hS := rootSetIdx_level (i := k) hI hthd hπ hpiv
    have hroot := levelRt_root hI hS (hrts k (by omega))
    obtain ⟨hru, hgru⟩ := hroot u hu
    obtain ⟨hrv, hgrv⟩ := hroot v hv
    set RF := rootedForestGivenRoots T₀ (g r) (levelRoots T₀ (g r) k) π with hRF
    -- the distances to the roots
    have hdR : ∀ x < vList.length,
        dRVal h LB mem ldBase (rts k) (lxs k) x ≤ 2 * M ∧
        (dRVal h LB mem ldBase (rts k) (lxs k) x : ℝ) =
          S * walkLength ℓ (T₀.forestPath (g x) (g (rts k x))) := by
      intro x hx
      obtain ⟨hrx, -⟩ := hroot x hx
      obtain ⟨hlx, hlca⟩ := hlxs k (by omega) x hx
      have hMx := hM x hx
      have hMr := hM _ hrx
      have hfit : unsignedVal mem (ldBase + x * LB) h LB +
          unsignedVal mem (ldBase + rts k x * LB) h LB < capacity h LB := by
        have : 4 * M ≤ 4 * M * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      have heq := dRVal_bridge hI hℓ hLd hx hrx hlx hlca hfit
      refine ⟨?_, heq⟩
      have hle := walkLength_le_wDepth_add hI.hT hℓ (hI.getD_mem hx) (hI.getD_mem hrx)
      have h1 : (dRVal h LB mem ldBase (rts k) (lxs k) x : ℝ) ≤ 2 * M := by
        rw [heq]
        calc (S : ℝ) * walkLength ℓ (T₀.forestPath (g x) (g (rts k x)))
            ≤ S * (wDepth T₀ (g r) ℓ (g x) + wDepth T₀ (g r) ℓ (g (rts k x))) :=
              mul_le_mul_of_nonneg_left hle hSnn
          _ = unsignedVal mem (ldBase + x * LB) h LB +
              unsignedVal mem (ldBase + rts k x * LB) h LB := by
              rw [hLd x hx, hLd _ hrx]; ring
          _ ≤ 2 * M := by exact_mod_cast (by omega)
      exact_mod_cast h1
    obtain ⟨hdu, hdue⟩ := hdR u hu
    obtain ⟨hdv, hdve⟩ := hdR v hv
    have hk4 : 4 * M * k + 4 * M < capacity h LB := by
      have : 4 * M * (k + 1) ≤ 4 * M * (K + 1) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this; omega
    simp only [accFold]
    rw [← hudef, ← hvdef, Finset.sum_range_succ, mul_add (S : ℝ), ← iheq]
    by_cases hsame : rts k u = rts k v
    · have hroots : RF.root (g u) = RF.root (g v) := by rw [← hgru, ← hgrv, hsame]
      rw [accLevelVal_same hsame (by omega)]
      refine ⟨by rw [Nat.mul_succ]; omega, ?_⟩
      push_cast
      rw [hduv]
      unfold levelDist
      rw [← hRF, if_pos hroots]
    · have hroots : RF.root (g u) ≠ RF.root (g v) := by
        rw [← hgru, ← hgrv]
        exact fun h' => hsame (hI.getD_inj hru hrv h')
      rw [accLevelVal_ne hsame (by omega)]
      refine ⟨by rw [Nat.mul_succ]; omega, ?_⟩
      push_cast
      rw [hdue, hdve]
      unfold levelDist
      rw [← hRF, if_neg hroots, ← hgru, ← hgrv]
      ring

end MinCostFlow.LSF.Program
