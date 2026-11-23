module

public import MinCostFlow.MinRatio.UpdateAssemblyBase
import MinCostFlow.MinRatio.PathApplyAccounting
import MinCostFlow.MinRatio.PathFlowBookkeeping
import MinCostFlow.LinkCut.PathTree.Ready
import MinCostFlow.MinRatio.PathNormalizationRange
import MinCostFlow.MinRatio.PathCycleCoefficients
import MinCostFlow.MinRatio.PathIncrementRange
import MinCostFlow.MinRatio.PathFlowNormalization
import MinCostFlow.MinRatio.CycleDetectorAccounting
import MinCostFlow.MinRatio.ExplicitEdgeRouteUpdate
import MinCostFlow.LSF.Congestion

/-!
# Unconditional discharge of `GoodCycleNumericBridge`

Connects an accepted `CycleDescriptorAt` from `updateCycleLoopBody` directly to the numeric,
connectivity, off-tree record, and post-apply accounting requirements of `updateGoodApplyBody_runs`
and `MinRatioStateFits`, with zero additional assumptions beyond the hypotheses already available
in `solverUpdateGoodBranch_runs`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

private theorem pathEdgeAt_unique {mem : ℕ → ℕ} {a h L : ℕ} {v₁ v₂ : PathEdgeValue}
    (h₁ : PathEdgeAt mem a h L (some v₁)) (h₂ : PathEdgeAt mem a h L (some v₂)) :
    v₁ = v₂ := by
  obtain ⟨_, hf1, hg1, hl1, hfl1, hd1⟩ := h₁
  obtain ⟨_, hf2, hg2, hl2, hfl2, hd2⟩ := h₂
  have hfwd : v₁.forward = v₂.forward := by
    have h := hf1.symm.trans hf2
    cases hv1 : v₁.forward <;> cases hv2 : v₂.forward <;> simp [hv1, hv2] at h ⊢
  cases v₁; cases v₂
  simp only [PathEdgeValue.mk.injEq]
  exact ⟨hfwd, hg1.2.symm.trans hg2.2, hl1.2.symm.trans hl2.2,
    hfl1.2.symm.trans hfl2.2, hd1.2.symm.trans hd2.2⟩

private theorem abs_walkFlow_singleton_le_one (x : ℕ × Bool) (e : ℕ) :
    |walkFlow [x] e| ≤ 1 := by
  obtain ⟨e', b⟩ := x
  by_cases h : e' = e
  · cases b <;> simp [walkFlow, h]
  · simp [walkFlow, h]

private theorem walkFlow_nodup_abs_le_one {F : MGraph} :
    ∀ {u v : ℕ} {walk : List (ℕ × Bool)}, F.IsPath u v walk → ∀ e, |walkFlow walk e| ≤ 1 := by
  intro u v walk hp e
  have h1 : ∀ {a b : ℕ} {w : List (ℕ × Bool)}, F.IsPath a b w →
      (∀ x ∈ w, x.1 ≠ e → walkFlow w e = walkFlow w e) → |walkFlow w e| ≤ 1 := by
    intro a b w
    induction w generalizing a with
    | nil => intro _ _; simp [walkFlow_nil]
    | cons x rest ih =>
      intro hpath _
      obtain ⟨hw, hnd⟩ := hpath
      cases hw with
      | cons hxe hsrc hrest =>
        simp only [MGraph.walkVertices, List.nodup_cons] at hnd
        have hpathR : F.IsPath (F.dst x) b rest := ⟨hrest, hnd.2⟩
        by_cases hxeq : x.1 = e
        · have hnot : e ∉ walkEdges rest := by
            intro hm
            rw [walkEdges, List.mem_toFinset, List.mem_map] at hm
            obtain ⟨y, hy, hye⟩ := hm
            have hyV : F.src y ∈ F.walkVertices (F.dst x) rest ∧ F.dst y ∈ F.walkVertices (F.dst x) rest := by
              have hsub : ∀ {s t : ℕ} {l : List (ℕ × Bool)}, F.IsWalk s t l →
                  ∀ z ∈ l, F.src z ∈ F.walkVertices s l ∧ F.dst z ∈ F.walkVertices s l := by
                intro s t l hl
                induction hl with
                | nil _ => intro _ h; cases h
                | cons _ hsz hl' ihl =>
                  intro z hz
                  rcases List.mem_cons.mp hz with rfl | hzr
                  · refine ⟨by simp [MGraph.walkVertices, hsz], ?_⟩
                    simp only [MGraph.walkVertices, List.mem_cons, List.mem_map]
                    exact Or.inr ⟨z, Or.inl rfl, rfl⟩
                  · obtain ⟨h1, h2⟩ := ihl z hzr
                    simp only [MGraph.walkVertices, List.mem_cons, List.mem_map] at h1 h2 ⊢
                    refine ⟨Or.inr ?_, Or.inr ?_⟩
                    · rcases h1 with h1 | ⟨w', hw', h1⟩
                      · exact ⟨_, Or.inl rfl, h1.symm⟩
                      · exact ⟨w', Or.inr hw', h1⟩
                    · rcases h2 with h2 | ⟨w', hw', h2⟩
                      · exact ⟨_, Or.inl rfl, h2.symm⟩
                      · exact ⟨w', Or.inr hw', h2⟩
              exact hsub hrest y hy
            have haIn : a ∈ F.walkVertices (F.dst x) rest := by
              have hxe' : y.1 = x.1 := hye.trans hxeq.symm
              rcases x with ⟨ex, bx⟩; rcases y with ⟨ey, by_⟩
              dsimp only at hxe' hsrc; subst hxe'
              cases bx <;> cases by_ <;> simp [MGraph.src, MGraph.dst] at hsrc hyV ⊢
              · exact hsrc ▸ hyV.1
              · exact hsrc ▸ hyV.2
              · exact hsrc ▸ hyV.2
              · exact hsrc ▸ hyV.1
            exact hnd.1 haIn
          rw [walkFlow_cons, walkFlow_eq_zero_of_not_mem hnot, add_zero]
          cases x.2 <;> simp [hxeq]
        · rw [walkFlow_cons, ite_eq_right hxeq, zero_add]
          exact ih hpathR (fun _ _ _ => rfl)
  exact h1 hp (fun _ _ _ => rfl)

private theorem abs_list_sum_le_length {α : Type*} (xs : List α) (f : α → ℝ)
    (hf : ∀ x ∈ xs, |f x| ≤ 1) : |(xs.map f).sum| ≤ (xs.length : ℝ) := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h1 := hf x List.mem_cons_self
    have h2 := ih (fun y hy => hf y (List.mem_cons_of_mem _ hy))
    linarith [abs_add_le (f x) (rest.map f).sum]

private theorem route_coord_abs_le {cfg : Alg2Config} {model : Alg2State cfg}
    {edges : List (ℕ × Bool)} {paths : List (ℕ × ℕ)}
    (hroute : CycleRouteAt model edges paths) {e : ℕ} (he : e ∈ model.extG.E) :
    |liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1 e| ≤
      (edges.length : ℝ) + (paths.length : ℝ) := by
  unfold liftEdgeFn
  rw [ite_eq_left he]
  rw [(hroute.2.2 e he).1]
  have h1 := abs_list_sum_le_length edges (fun x => walkFlow [x] (model.extToInt e))
    (fun x _ => abs_walkFlow_singleton_le_one x _)
  have h2 := abs_list_sum_le_length paths
    (fun p => walkFlow (model.chain.toTreeChain.chainTree.forestPath p.1 p.2) (model.extToInt e))
    (fun p hp => walkFlow_nodup_abs_le_one (MGraph.isPath_forestPath (hroute.2.1 p hp).2.2) _)
  linarith [abs_add_le
    (edges.map (fun x => walkFlow [x] (model.extToInt e))).sum
    (paths.map (fun p => walkFlow (model.chain.toTreeChain.chainTree.forestPath p.1 p.2) (model.extToInt e))).sum]

private theorem goodCycle_inner_abs_le {cfg : Alg2Config} {model : Alg2State cfg}
    {m E maxEdges maxPaths : ℕ} {edges : List (ℕ × Bool)} {paths : List (ℕ × ℕ)}
    (hextM : ∀ e ∈ model.extG.E, e < m)
    (hgB : ∀ e ∈ model.extG.E, |model.extg e| ≤ (2 : ℝ) ^ E)
    (hroute : CycleRouteAt model edges paths)
    (hmaxE : edges.length ≤ maxEdges) (hmaxP : paths.length ≤ maxPaths)
    (hmaxEP : maxEdges + maxPaths < 2 ^ (3 * E + 20)) :
    let Δ := liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1
    |-model.extG.inner model.extg Δ| ≤ (2 : ℝ) ^ (4 * E + Nat.size m + 20) := by
  dsimp only
  rw [abs_neg]
  let Δ := liftEdgeFn model.extG model.extToInt (algorithm1_findCycle model.chain).1
  have hcard : model.extG.E.card ≤ m := by
    have hsub : model.extG.E ⊆ Finset.range m := fun e he => Finset.mem_range.mpr (hextM e he)
    exact (Finset.card_le_card hsub).trans (by simp)
  have hmSize : (m : ℝ) ≤ (2 : ℝ) ^ Nat.size m := by
    exact_mod_cast (Nat.lt_size_self m).le
  have hep : (edges.length : ℝ) + (paths.length : ℝ) ≤ (2 : ℝ) ^ (3 * E + 20) := by
    have hnat : edges.length + paths.length ≤ 2 ^ (3 * E + 20) := by omega
    exact_mod_cast hnat
  have hterm : ∀ e ∈ model.extG.E, |model.extg e * Δ e| ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ (3 * E + 20) := by
    intro e he
    rw [abs_mul]
    exact mul_le_mul (hgB e he) ((route_coord_abs_le hroute he).trans hep) (abs_nonneg _) (by positivity)
  calc
    |model.extG.inner model.extg Δ|
      ≤ ∑ e ∈ model.extG.E, |model.extg e * Δ e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ model.extG.E, ((2 : ℝ) ^ E * (2 : ℝ) ^ (3 * E + 20)) := Finset.sum_le_sum hterm
    _ = (model.extG.E.card : ℝ) * ((2 : ℝ) ^ E * (2 : ℝ) ^ (3 * E + 20)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ Nat.size m * ((2 : ℝ) ^ E * (2 : ℝ) ^ (3 * E + 20)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_trans (by exact_mod_cast hcard) hmSize
    _ = (2 : ℝ) ^ (4 * E + Nat.size m + 20) := by
          rw [← pow_add, ← pow_add]
          congr 1; omega

private theorem goodCycle_numeric_pack {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (m k : ℕ) (modelLoop : Alg2State cfg)
    (request inner : ℤ) (edges : List (ℕ × Bool)) (paths : List (ℕ × ℕ))
    (maxEdges maxPaths : ℕ)
    (hfmt4 : F.fmt.limbBits = 4)
    (hGeq : modelLoop.extG = G)
    (hfits : MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G 4 F.limbs F.fmt.precision modelLoop)
    (hflowB : ∀ e ∈ G.E, |modelLoop.flow e| ≤ (2 : ℝ) ^ F.rangeExponent)
    (hκα : (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ (1 / (2 : ℝ) ^ k) * cfg.α)
    (hprec : 5 * F.rangeExponent + Nat.size m + 30 ≤ F.fmt.precision)
    (hglB : ∀ e ∈ G.E, |modelLoop.extg e| ≤ (2 : ℝ) ^ F.rangeExponent ∧
      (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ modelLoop.extℓ e ∧
      modelLoop.extℓ e ≤ (2 : ℝ) ^ F.rangeExponent)
    (hextM : ∀ e ∈ modelLoop.extG.E, e < m)
    (hinnerEq : modelLoop.extG.inner modelLoop.extg
        (liftEdgeFn modelLoop.extG modelLoop.extToInt (algorithm1_findCycle modelLoop.chain).1) =
        (inner : ℝ) / (2 : ℝ) ^ F.fmt.precision)
    (hroute : CycleRouteAt modelLoop edges paths)
    (hmaxE : edges.length ≤ maxEdges) (hmaxP : paths.length ≤ maxPaths)
    (hgood : modelLoop.extG.inner modelLoop.extg
        (liftEdgeFn modelLoop.extG modelLoop.extToInt (algorithm1_findCycle modelLoop.chain).1) /
      modelLoop.extG.lnorm modelLoop.extℓ
        (liftEdgeFn modelLoop.extG modelLoop.extToInt (algorithm1_findCycle modelLoop.chain).1) ≤
      -((1 / (2 : ℝ) ^ k) * cfg.α))
    (hreqLo : (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ (request : ℝ) / (2 : ℝ) ^ F.fmt.precision)
    (hreqHi : (request : ℝ) / (2 : ℝ) ^ F.fmt.precision ≤ (2 : ℝ) ^ F.rangeExponent)
    (hsizeM : Nat.size m ≤ F.rangeExponent + 8)
    (hmaxEP : maxEdges + maxPaths < 2 ^ (3 * F.rangeExponent + 20)) :
    let L := F.limbs
    let P := F.fmt.precision
    let E := F.rangeExponent
    let Δ := liftEdgeFn modelLoop.extG modelLoop.extToInt (algorithm1_findCycle modelLoop.chain).1
    let mult := pathMultiplier P request (-inner)
    let actual := -(((mult : ℝ) / (2 : ℝ) ^ P) * ((inner : ℝ) / (2 : ℝ) ^ P))
    let inc : ℕ → ℝ := fun e =>
      if e ∈ modelLoop.extG.E then -(actual / modelLoop.extG.inner modelLoop.extg Δ) * Δ e else 0
    (∃ e0 ∈ G.E, Δ e0 ≠ 0) ∧
    0 < -inner ∧
    Num.Fits 4 L (-inner) ∧
    (2 : ℝ) * (((-inner : ℤ) : ℝ) / (2 : ℝ) ^ P) ≤ (request : ℝ) ∧
    0 ≤ mult ∧
    (mult : ℤ) ≤ (2 : ℤ) ^ (3 * E + P) ∧
    Num.Fits 4 L mult ∧
    Num.Fits 4 L |mult| ∧
    NormalizationWithin ((request : ℝ) / (2 : ℝ) ^ P) actual ∧
    (∀ e ∈ G.E, |inc e| ≤ (2 : ℝ) ^ (3 * E + 1)) ∧
    MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G 4 L P
      { modelLoop with
        flow := fun e => modelLoop.flow e + inc e
        detectAccum := fun e => modelLoop.detectAccum e + |inc e| } := by
  dsimp only
  let L := F.limbs
  let P := F.fmt.precision
  let E := F.rangeExponent
  let Δ := liftEdgeFn modelLoop.extG modelLoop.extToInt (algorithm1_findCycle modelLoop.chain).1
  let mult := pathMultiplier P request (-inner)
  let actual := -(((mult : ℝ) / (2 : ℝ) ^ P) * ((inner : ℝ) / (2 : ℝ) ^ P))
  let inc : ℕ → ℝ := fun e =>
    if e ∈ modelLoop.extG.E then -(actual / modelLoop.extG.inner modelLoop.extg Δ) * Δ e else 0
  have hPpos : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have hr : 1 / (2 : ℝ) ^ E ≤ (1 / (2 : ℝ) ^ k) * cfg.α := by
    simpa [one_div, zpow_neg, zpow_natCast] using hκα
  have hl : ∀ e ∈ modelLoop.extG.E, 1 / (2 : ℝ) ^ E ≤ modelLoop.extℓ e := fun e he => by
    have := (hglB e (hGeq ▸ he)).2.1
    simpa [one_div, zpow_neg, zpow_natCast] using this
  have hnonzero : ∃ e0 ∈ G.E, Δ e0 ≠ 0 := by
    by_contra! hn
    have hz : modelLoop.extG.lnorm modelLoop.extℓ Δ = 0 := by
      unfold MGraph.lnorm
      exact Finset.sum_eq_zero fun e he => by rw [hn e (hGeq ▸ he), abs_zero, mul_zero]
    rw [hz, div_zero] at hgood
    have hrPos : (0 : ℝ) < (1 / (2 : ℝ) ^ k) * cfg.α := lt_of_lt_of_le (by positivity) hr
    linarith
  have hmagLo : 1 / (2 : ℝ) ^ (2 * E) ≤ -modelLoop.extG.inner modelLoop.extg Δ :=
    findCycle_lift_inner_lower modelLoop.chain modelLoop.extG modelLoop.extToInt modelLoop.extg
      modelLoop.extℓ E hr hl hgood
  have hmagEq : ((-inner : ℤ) : ℝ) / (2 : ℝ) ^ P = -modelLoop.extG.inner modelLoop.extg Δ := by
    rw [hinnerEq, Int.cast_neg, neg_div]
  have hmagLo' : 1 / (2 : ℝ) ^ (2 * E) ≤ ((-inner : ℤ) : ℝ) / (2 : ℝ) ^ P := hmagEq.symm ▸ hmagLo
  have hmagPos : 0 < -inner := by
    have hpos : (0 : ℝ) < ((-inner : ℤ) : ℝ) / (2 : ℝ) ^ P := lt_of_lt_of_le (by positivity) hmagLo'
    have : (0 : ℝ) < ((-inner : ℤ) : ℝ) := (div_pos_iff_of_pos_right hPpos).mp hpos
    exact_mod_cast this
  have hmagAbs := goodCycle_inner_abs_le hextM (fun e he => (hglB e (hGeq ▸ he)).1) hroute hmaxE hmaxP hmaxEP
  have hmagHi : |((-inner : ℤ) : ℝ) / (2 : ℝ) ^ P| ≤ (2 : ℝ) ^ (5 * E + 28) := by
    rw [hmagEq]
    exact hmagAbs.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hwidth := F.width
  rw [hfmt4] at hwidth
  have hfitMag : Num.Fits 4 L (-inner) :=
    Num.IPM.fits_of_scaled_bound (P := P) (E := 5 * E + 28) (by omega) hmagHi
  have hstep : (2 : ℝ) * (((-inner : ℤ) : ℝ) / (2 : ℝ) ^ P) ≤ (request : ℝ) := by
    have h1 : 2 * (-modelLoop.extG.inner modelLoop.extg Δ) ≤ ((request : ℝ) / (2 : ℝ) ^ P) * (2 : ℝ) ^ P :=
      pathFlow_precision_step hreqLo (le_trans (le_abs_self _) hmagAbs) (by omega)
    rw [div_mul_cancel₀ _ hPpos.ne', ← hmagEq] at h1
    exact h1
  have hreqPos : (0 : ℝ) ≤ (request : ℝ) / (2 : ℝ) ^ P := le_trans (by positivity) hreqLo
  have hreqAbs : |(request : ℝ) / (2 : ℝ) ^ P| ≤ (2 : ℝ) ^ E := by
    rw [abs_of_nonneg hreqPos]; exact hreqHi
  have hfitMult : Num.Fits 4 L mult := by
    have h := pathMultiplier_fits F request (-inner) hreqAbs hmagLo'
    rwa [hfmt4] at h
  have hreqNonneg : 0 ≤ request := by
    have : (0 : ℝ) ≤ (request : ℝ) := (div_nonneg_iff.mp hreqPos).resolve_right (by intro h; linarith) |>.1
    exact_mod_cast this
  have hmultNonneg : 0 ≤ mult := by
    unfold mult pathMultiplier
    rw [Num.floorDiv_eq_floor]
    exact Int.floor_nonneg.mpr (div_nonneg (by positivity) (by exact_mod_cast hmagPos.le))
  have hfitAbs : Num.Fits 4 L |mult| := by rwa [abs_of_nonneg hmultNonneg]
  have hmultLe : mult ≤ (2 : ℤ) ^ (3 * E + P) := by
    have hfloor : (mult : ℝ) ≤ ((request : ℝ) * (2 : ℝ) ^ P) / ((-inner : ℤ) : ℝ) := by
      unfold mult pathMultiplier
      rw [Num.floorDiv_eq_floor]
      have h := Int.floor_le (((request * (2 : ℤ) ^ P : ℤ) : ℝ) / ((-inner : ℤ) : ℝ))
      simpa [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] using h
    have hquot : ((request : ℝ) * (2 : ℝ) ^ P) / ((-inner : ℤ) : ℝ) ≤ (2 : ℝ) ^ (3 * E + P) := by
      have hnum : (request : ℝ) ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ P := (div_le_iff₀ hPpos).mp hreqHi
      have hden : (2 : ℝ) ^ P / (2 : ℝ) ^ (2 * E) ≤ ((-inner : ℤ) : ℝ) := by
        have h := (le_div_iff₀ hPpos).mp hmagLo'
        simpa [one_div, inv_mul_eq_div] using h
      have hdenPos : (0 : ℝ) < (2 : ℝ) ^ P / (2 : ℝ) ^ (2 * E) := by positivity
      calc
        ((request : ℝ) * (2 : ℝ) ^ P) / ((-inner : ℤ) : ℝ)
          ≤ ((2 : ℝ) ^ E * (2 : ℝ) ^ P * (2 : ℝ) ^ P) / ((2 : ℝ) ^ P / (2 : ℝ) ^ (2 * E)) := by
            apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hnum hPpos.le) hdenPos hden
        _ = (2 : ℝ) ^ (3 * E + P) := by
            have h2E : (2 : ℝ) ^ (2 * E) ≠ 0 := by positivity
            field_simp [hPpos.ne', h2E]
            rw [← pow_add, ← pow_add]; congr 1; omega
    exact_mod_cast hfloor.trans hquot
  have hnormWithin : NormalizationWithin ((request : ℝ) / (2 : ℝ) ^ P) actual := by
    have hinnerNeg : (inner : ℝ) / (2 : ℝ) ^ P < 0 := by
      have : -((inner : ℝ) / (2 : ℝ) ^ P) = ((-inner : ℤ) : ℝ) / (2 : ℝ) ^ P := by simp [Int.cast_neg, neg_div]
      linarith [lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (2 : ℝ) ^ (2 * E)) hmagLo']
    have hstep' : 2 * (-((inner : ℝ) / (2 : ℝ) ^ P)) ≤ ((request : ℝ) / (2 : ℝ) ^ P) * (2 : ℝ) ^ P := by
      rw [div_mul_cancel₀ _ hPpos.ne']
      simpa [Int.cast_neg, neg_div] using hstep
    have h := pathFlow_floor_normalization hinnerNeg P hstep'
    dsimp only at h
    rw [pathFlow_floor_normalization_dyadic] at h
    exact h
  have hincLe : ∀ e ∈ G.E, |inc e| ≤ (2 : ℝ) ^ (3 * E + 1) := by
    intro e he
    have he' : e ∈ modelLoop.extG.E := hGeq.symm ▸ he
    dsimp only [inc]
    rw [ite_eq_left he']
    exact pathIncrement_dyadic_le modelLoop.extG modelLoop.extg modelLoop.extℓ Δ E hr hl hreqPos
      hreqHi hnormWithin (fun f _ => findCycle_lift_integral modelLoop.chain modelLoop.extG modelLoop.extToInt f)
      hgood he'
  have hFitsEnd : MinRatioStateFits (Chain.Ordered.algorithm2_dsWithFailureWith cfg (1 / (2 : ℝ) ^ k)) G 4 L P
      { modelLoop with
        flow := fun e => modelLoop.flow e + inc e
        detectAccum := fun e => modelLoop.detectAccum e + |inc e| } := by
    intro e he
    have he' : e ∈ modelLoop.extG.E := hGeq.symm ▸ he
    obtain ⟨oldFl, _, holdEq⟩ := hfits e he
    obtain ⟨coeff, hcoeff⟩ := findCycle_lift_integral modelLoop.chain modelLoop.extG modelLoop.extToInt e
    have hinnerNe : modelLoop.extG.inner modelLoop.extg Δ ≠ 0 := by
      have : 0 < -modelLoop.extG.inner modelLoop.extg Δ := lt_of_lt_of_le (by positivity) hmagLo
      linarith
    have hincEq : inc e = ((mult * coeff : ℤ) : ℝ) / (2 : ℝ) ^ P := by
      dsimp only [inc]
      change Δ e = (coeff : ℝ) at hcoeff
      rw [ite_eq_left he', hcoeff]
      have hactEq : actual = -(((mult : ℝ) / (2 : ℝ) ^ P) * modelLoop.extG.inner modelLoop.extg Δ) := by
        dsimp only [actual]; rw [hinnerEq]
      rw [hactEq, pathFlow_normalization hinnerNe, Int.cast_mul, div_mul_eq_mul_div]
    change modelLoop.flow e = (oldFl : ℝ) / (2 : ℝ) ^ P at holdEq
    refine ⟨oldFl + mult * coeff, ?_, ?_⟩
    · have h1 := pathIncrement_flow_fits F oldFl (mult * coeff)
        (by rw [← holdEq]; exact hflowB e he)
        (by rw [← hincEq]; exact hincLe e he)
      rwa [hfmt4] at h1
    · change modelLoop.flow e + inc e = _
      rw [holdEq, hincEq, Int.cast_add, add_div]
  exact ⟨hnonzero, hmagPos, hfitMag, hstep, hmultNonneg, hmultLe, hfitMult, hfitAbs,
    hnormWithin, hincLe, hFitsEnd⟩

private theorem sum_abs_mul_div_pow (paths : List (ℕ × ℕ)) (f : ℕ × ℕ → ℝ) (mult : ℤ) (P : ℕ) :
    (paths.map (fun p => |(mult : ℝ) * f p|)).sum / (2 : ℝ) ^ P =
      (paths.map (fun p => |((mult : ℝ) / (2 : ℝ) ^ P) * f p|)).sum := by
  have hPpos : (0 : ℝ) < (2 : ℝ) ^ P := pow_pos zero_lt_two P
  induction paths with
  | nil => simp
  | cons p rest ih =>
    simp only [List.map_cons, List.sum_cons, add_div, ih]
    congr 1
    rw [div_mul_eq_mul_div, abs_div, abs_of_pos hPpos]

private theorem forestPairs_snd_unique {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} (hnd : (trees.flatMap AuxTree.toList).Nodup)
    {a : ℕ} {b₁ b₂ : Option PathEdgeValue}
    (h1 : (a, b₁) ∈ forestPairs pathPayload s trees)
    (h2 : (a, b₂) ∈ forestPairs pathPayload s trees) : b₁ = b₂ := by
  have hperm : ((forestPairs pathPayload s trees).map Prod.fst).Perm (trees.flatMap AuxTree.toList) := by
    have hev : ∀ (t : AuxTree) (b : Bool),
        (AuxTree.evalInorder (fun id => (s.nodes id).rev) t b).Perm t.toList := by
      intro t
      induction t with
      | leaf => intro _; simp [AuxTree.evalInorder, AuxTree.toList]
      | node x l r ihl ihr =>
        intro b
        cases b
        · simp only [AuxTree.evalInorder, AuxTree.toList, List.append_assoc, List.singleton_append]
          exact (ihl _).append (List.Perm.cons x (ihr _))
        · simp only [AuxTree.evalInorder, AuxTree.toList, List.append_assoc, List.singleton_append]
          have h1 := (ihr (!(s.nodes x).rev)).append (List.Perm.cons x (ihl (!(s.nodes x).rev)))
          exact h1.trans (List.perm_middle.trans
            ((List.Perm.cons x List.perm_append_comm).trans List.perm_middle.symm))
    have hloop : ∀ ts : List AuxTree,
        ((forestPairs pathPayload s ts).map Prod.fst).Perm (ts.flatMap AuxTree.toList) := by
      intro ts
      induction ts with
      | nil => simp [forestPairs]
      | cons t rest ih =>
        simp only [forestPairs, List.flatMap_cons, List.map_append]
        have ht : ((SplayState.evalPairs pathPayload s t false pathPayload.idTag).map Prod.fst).Perm t.toList := by
          rw [SplayState.evalPairs_map_fst]
          exact hev t false
        exact ht.append ih
    exact hloop trees
  have hndP : ((forestPairs pathPayload s trees).map Prod.fst).Nodup := hperm.nodup_iff.mpr hnd
  have hmem : ∀ {l : List (ℕ × Option PathEdgeValue)}, (l.map Prod.fst).Nodup →
      ∀ {x : ℕ} {y₁ y₂ : Option PathEdgeValue}, (x, y₁) ∈ l → (x, y₂) ∈ l → y₁ = y₂ := by
    intro l
    induction l with
    | nil => intro _ _ _ _ h; cases h
    | cons p rest ih =>
      intro hnd' x y₁ y₂ hp1 hp2
      rw [List.map_cons, List.nodup_cons] at hnd'
      rcases List.mem_cons.mp hp1 with h1a | h1b <;> rcases List.mem_cons.mp hp2 with h2a | h2b
      · exact congrArg Prod.snd (h1a.trans h2a.symm)
      · rcases p with ⟨px, py⟩
        simp only [Prod.mk.injEq] at h1a
        obtain ⟨rfl, rfl⟩ := h1a
        exact False.elim (hnd'.1 (List.mem_map.mpr ⟨(x, y₂), h2b, rfl⟩))
      · rcases p with ⟨px, py⟩
        simp only [Prod.mk.injEq] at h2a
        obtain ⟨rfl, rfl⟩ := h2a
        exact False.elim (hnd'.1 (List.mem_map.mpr ⟨(x, y₁), h1b, rfl⟩))
      · exact ih hnd'.2 h1b h2b
  exact hmem hndP h1 h2

/-- Unconditional wiring of `GoodCycleNumericBridge`. -/
theorem goodCycleNumericBridge_wired {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (m V psi k epsExp drainUnit : ℕ) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T))
    (maxEdges maxPaths : ℕ) (B_bound R_bound : ℤ) :
    GoodCycleNumericBridge F cfg G m V psi k epsExp drainUnit Rcore
      maxEdges maxPaths B_bound R_bound := by
  classical
  intro root eta outHeap curDesc nextHeap mem modelLoop tok B R request inner norm edges paths
    Δ mult actual inc hfmt4 hGeq hfits hflowB hκα hprec hglB hrep hnum hOff hB hR hdesc
    hmaxE hmaxP htag18 hfootRng hgood hreqAt hreqLo hreqHi h2nW hlogW hsizeM hmaxEP hcapP hcapB
  let L := F.limbs
  let P := F.fmt.precision
  let E := F.rangeExponent
  let FT := modelLoop.chain.toTreeChain.chainTree
  obtain ⟨_, _, _, _, hfreshInv, _, hextM, _, _, _, htn, hlct, _, hedgeAcc, _, _, _, _, hwire, htags⟩ := hrep
  obtain ⟨_, hdg0, ⟨hFTforest, hFTvalid⟩, hns, horient⟩ := hwire
  obtain ⟨hOwn, _, _, _, _, _, _, _, _, t9, t10, t11, t12, t13, _, t15, _, t1718, _, _, _⟩ := htags
  obtain ⟨_, _, _, _, _, hedBaseLo, _, _, _, _, _, _, _, _, hinnerEq, _, _, _, hroute⟩ := hdesc
  obtain ⟨⟨e0, he0G, _⟩, hmagPos, hfitMag, hstep, hmultNonneg, hmultLe, hfitMult, hfitAbs,
      _, hincLe, hFitsEnd⟩ :=
    goodCycle_numeric_pack F cfg G m k modelLoop request inner edges paths maxEdges maxPaths
      hfmt4 hGeq hfits hflowB hκα hprec hglB hextM hinnerEq hroute hmaxE hmaxP hgood
      hreqLo hreqHi hsizeM hmaxEP
  have hcapPos : 0 < tok.intCap := by
    have := (hedgeAcc.1 e0 (hGeq.symm ▸ he0G)).1; omega
  have htnG : tok.tree.n = G.n := htn.trans (by rw [hGeq])
  have h2nWT : 2 * tok.tree.n + 1 < 2 ^ w := htnG.symm ▸ h2nW
  have hlogWT : Nat.log 2 (2 * tok.tree.n + 1) ≤ 4 * L := htnG.symm ▸ hlogW
  have hconnTree : ∀ q ∈ paths, q.1 < tok.tree.n ∧ q.2 < tok.tree.n ∧
      pathTreeConnected tok.tree (q.1 + 1) (q.2 + 1) := by
    intro q hq
    obtain ⟨hq1, hq2, hqc⟩ := hroute.2.1 q hq
    refine ⟨htn.symm ▸ hq1, htn.symm ▸ hq2,
      treeEditNamedSlots_connected hlct hns
        (fun e he => ⟨htn.symm ▸ (hFTvalid e he).2.1, htn.symm ▸ (hFTvalid e he).2.2.1⟩)
        (htn.symm ▸ hq1) (htn.symm ▸ hq2) hqc⟩
  have htagMagLe : pathTagMagnitude (PathTag.ofFlow mult) ≤ (2 : ℤ) ^ (3 * E + 2 + P) := by
    simp only [pathTagMagnitude, PathTag.ofFlow, abs_abs]
    have hpow : (2 : ℤ) * (2 : ℤ) ^ (3 * E + P) ≤ (2 : ℤ) ^ (3 * E + 2 + P) := by
      have : (2 : ℤ) ^ (3 * E + 2 + P) = 4 * (2 : ℤ) ^ (3 * E + P) := by
        rw [show 3 * E + 2 + P = (3 * E + P) + 2 by omega, pow_add]; ring
      have hpos : (0 : ℤ) ≤ (2 : ℤ) ^ (3 * E + P) := pow_nonneg (by decide) _
      omega
    have h1 : |mult| = mult := abs_of_nonneg hmultNonneg
    dsimp only [E, P, mult] at hmultLe hpow h1 ⊢
    rw [h1]
    omega
  have hm1 : (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult) ≤
      (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P) :=
    mul_le_mul (Int.ofNat_le.mpr hmaxP) htagMagLe (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (Int.natCast_nonneg maxPaths)
  have hBend : B + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult) ≤
      B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P) := by omega
  have hRend : R + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult) ≤
      R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P) := by omega
  have hcapTree : 2 * ((2 * tok.tree.n + 1 : ℕ) : ℤ) *
      ((B + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult)) +
        (R + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult))) <
      (Num.capacity 4 L : ℤ) := by
    rw [htnG]
    have hsum : (B + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult)) +
        (R + (paths.length : ℤ) * pathTagMagnitude (PathTag.ofFlow mult)) ≤
        (B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P)) +
        (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P)) := by omega
    have hmul := mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (by decide : (0 : ℤ) ≤ 2) (Int.natCast_nonneg (2 * G.n + 1)))
    exact lt_of_le_of_lt hmul hcapP
  -- Helper: map internal edge in `(G 0).E` back to its external edge
  have hinvExt (ei : ℕ) (hei : ei ∈ (modelLoop.chain.G 0).E) :
      modelLoop.intToExt ei ∈ modelLoop.extG.E ∧ modelLoop.extToInt (modelLoop.intToExt ei) = ei :=
    ⟨(hfreshInv.hRight ei hei).2, (hfreshInv.hRight ei hei).1⟩
  let address : ℕ → ℕ := fun ei => mem (tok.edgeRecords + ei)
  let old : ℕ → PathEdgeValue := fun ei =>
    if h : ∃ val : PathEdgeValue, PathEdgeAt mem (address ei) 4 L (some val) then
      Classical.choose h
    else
      { forward := true, gradient := 0, length := 0, flow := 0, detector := 0 }
  have hold_of_off (e : ℕ) (he : e ∈ modelLoop.extG.E) (hnFT : modelLoop.extToInt e ∉ FT.E) :
      PathEdgeAt mem (address (modelLoop.extToInt e)) 4 L (some (old (modelLoop.extToInt e))) := by
    have hacc := (hedgeAcc.1 e he).2.2
    rw [ite_eq_right hnFT] at hacc
    obtain ⟨_, val, _, hpa, _⟩ := hacc
    have hex : ∃ val : PathEdgeValue, PathEdgeAt mem (address (modelLoop.extToInt e)) 4 L (some val) :=
      ⟨val, hpa⟩
    simp only [old]
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex
  have haddr : ∀ ei ∈ edges.map Prod.fst, ei < tok.intCap ∧
      mem (tok.edgeRecords + ei) = address ei ∧
      PathEdgeAt mem (address ei) 4 L (some (old ei)) ∧
      (∀ x < 2 + 4 * L, tok.tag (address ei + x) = 18) ∧
      address ei + 2 + 4 * L ≤ mem (curDesc + 2) := by
    intro ei hei
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hei
    obtain ⟨heiG0, heiNotFT⟩ := Finset.mem_sdiff.mp (hroute.1 row hrow)
    obtain ⟨heExt, he2i⟩ := hinvExt row.1 heiG0
    have hacc := hedgeAcc.1 (modelLoop.intToExt row.1) heExt
    have ht18e := (t1718 (modelLoop.intToExt row.1) heExt).2 (he2i.symm ▸ heiNotFT)
    rw [he2i] at hacc ht18e
    have hlast18 : address row.1 + (2 + 4 * L - 1) < curDesc :=
      htag18 _ (ht18e (2 + 4 * L - 1) (by omega))
    refine ⟨hacc.1, rfl, he2i ▸ hold_of_off _ heExt (he2i.symm ▸ heiNotFT), ht18e, by omega⟩
  have hdisj : ∀ e ∈ edges.map Prod.fst, ∀ f ∈ edges.map Prod.fst, e ≠ f →
      address e + 2 + 4 * L ≤ address f ∨ address f + 2 + 4 * L ≤ address e := by
    intro e1 he1 e2 he2 hne
    obtain ⟨r1, hr1, rfl⟩ := List.mem_map.mp he1
    obtain ⟨r2, hr2, rfl⟩ := List.mem_map.mp he2
    obtain ⟨h1G0, h1nFT⟩ := Finset.mem_sdiff.mp (hroute.1 r1 hr1)
    obtain ⟨h2G0, h2nFT⟩ := Finset.mem_sdiff.mp (hroute.1 r2 hr2)
    obtain ⟨he1Ext, h1eq⟩ := hinvExt r1.1 h1G0
    obtain ⟨he2Ext, h2eq⟩ := hinvExt r2.1 h2G0
    have hneExt : modelLoop.intToExt r1.1 ≠ modelLoop.intToExt r2.1 := fun h =>
      hne (h1eq.symm.trans ((congrArg modelLoop.extToInt h).trans h2eq))
    simpa [address, L, h1eq, h2eq, Nat.add_assoc] using
      hOff.2 _ he1Ext _ he2Ext hneExt (h1eq.symm ▸ h1nFT) (h2eq.symm ▸ h2nFT)
  have hinnerNe : modelLoop.extG.inner modelLoop.extg Δ ≠ 0 := by
    have : (0 : ℝ) < ((-inner : ℤ) : ℝ) / (2 : ℝ) ^ P := div_pos (by exact_mod_cast hmagPos) (by positivity)
    rw [Int.cast_neg, neg_div, ← hinnerEq] at this
    linarith
  have hfitOff : ∀ ei ∈ edges.map Prod.fst,
      let n := (edges.count (ei, true) : ℤ) - (edges.count (ei, false) : ℤ)
      Num.Fits 4 L n ∧ Num.Fits 4 L (mult * n) ∧ Num.Fits 4 L |mult * n| ∧
        Num.Fits 4 L ((old ei).flow + mult * n) ∧ Num.Fits 4 L ((old ei).detector + |mult * n|) := by
    intro ei hei
    dsimp only
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hei
    obtain ⟨heiG0, heiNotFT⟩ := Finset.mem_sdiff.mp (hroute.1 row hrow)
    obtain ⟨heExt, he2i⟩ := hinvExt row.1 heiG0
    let e := modelLoop.intToExt row.1
    let n : ℤ := (edges.count (row.1, true) : ℤ) - (edges.count (row.1, false) : ℤ)
    have hwidth := F.width
    rw [hfmt4] at hwidth
    have hcap4L : (2 : ℤ) ^ (4 * L) = (Num.capacity 4 L : ℤ) := by
      rw [Num.capacity_eq_two_pow]; push_cast; rfl
    have hnFit : Num.Fits 4 L n := by
      apply explicitEdge_signed_count_fits edges row.1
      have hlt : 2 * (edges.length : ℤ) < (2 : ℤ) ^ (3 * E + 21) := by
        have : 2 * edges.length < 2 ^ (3 * E + 21) := by
          rw [pow_succ]; dsimp only [E]; omega
        exact_mod_cast this
      have hpow : (2 : ℤ) ^ (3 * E + 21) ≤ (Num.capacity 4 L : ℤ) := by
        rw [← hcap4L]; exact pow_le_pow_right₀ (by decide) (by omega)
      exact lt_of_lt_of_le hlt hpow
    have hCeq := offTree_cycle_increment_of_signed_count heiNotFT edges paths
      (fun p hp => (hroute.2.1 p hp).2.2) (algorithm1_findCycle modelLoop.chain).1
      (by have h := (hroute.2.2 e heExt).1; dsimp only [e] at h; rw [he2i] at h; exact h)
      ((mult : ℝ) / (2 : ℝ) ^ P)
    have hinc_eq : inc e = ((mult * n : ℤ) : ℝ) / (2 : ℝ) ^ P := by
      dsimp only [inc]
      rw [ite_eq_left heExt]
      have hactEq : actual = -(((mult : ℝ) / (2 : ℝ) ^ P) * modelLoop.extG.inner modelLoop.extg Δ) := by
        dsimp only [actual]; rw [hinnerEq]
      rw [hactEq, pathFlow_normalization hinnerNe]
      have hΔe : Δ e = (algorithm1_findCycle modelLoop.chain).1 row.1 := by
        dsimp only [Δ, liftEdgeFn]; rw [ite_eq_left heExt, he2i]
      rw [hΔe, hCeq.1, Int.cast_mul, div_mul_eq_mul_div]
    have hchgBound : |((mult * n : ℤ) : ℝ) / (2 : ℝ) ^ P| ≤ (2 : ℝ) ^ (3 * E + 1) := by
      rw [← hinc_eq]; exact hincLe e (hGeq ▸ heExt)
    have hpaOld : PathEdgeAt mem (address row.1) 4 L (some (old row.1)) := (haddr row.1 hei).2.2.1
    have horE := horient e heExt
    dsimp only [e] at horE
    rw [he2i, ite_eq_right heiNotFT] at horE
    have hfwdOld : (old row.1).forward = true := (horE (old row.1) hpaOld).1
    have haccE := (hedgeAcc.1 e heExt).2.2
    dsimp only [e] at haccE
    rw [he2i, ite_eq_right heiNotFT] at haccE
    obtain ⟨_, val0, _, hpa0, hfl0, _, _, _⟩ := haccE
    have hvalEq : old row.1 = val0 := pathEdgeAt_unique hpaOld hpa0
    have hflOld : |((old row.1).flow : ℝ) / (2 : ℝ) ^ P| ≤ (2 : ℝ) ^ E := by
      have hof : (old row.1).flow = val0.originalFlow := by
        rw [← hvalEq]; simp [PathEdgeValue.originalFlow, hfwdOld]
      rw [hof, hfl0]; exact hflowB e (hGeq ▸ heExt)
    have hdetOld : |(old row.1).detector| ≤ B :=
      hOff.1 e heExt (by dsimp only [e]; rw [he2i]; exact heiNotFT) (old row.1)
        (by dsimp only [e]; rw [he2i]; exact hpaOld)
    have hmnFit : Num.Fits 4 L (mult * n) :=
      Num.IPM.fits_of_scaled_bound (P := P) (E := 3 * E + 1) (by omega) hchgBound
    have hmnAbsFit : Num.Fits 4 L |mult * n| := by
      apply Num.IPM.fits_of_scaled_bound (P := P) (E := 3 * E + 1) (by omega)
      simpa [Int.cast_abs, abs_div, abs_of_pos (pow_pos (zero_lt_two : (0 : ℝ) < 2) P)] using hchgBound
    have hflNewFit : Num.Fits 4 L ((old row.1).flow + mult * n) := by
      have h := pathIncrement_flow_fits F (old row.1).flow (mult * n) hflOld hchgBound
      rwa [hfmt4] at h
    have hdetNewFit : Num.Fits 4 L ((old row.1).detector + |mult * n|) := by
      have hmnAbsLe : |mult * n| ≤ (2 : ℤ) ^ (3 * E + 1 + P) := by
        have hPpos : (0 : ℝ) < (2 : ℝ) ^ P := pow_pos zero_lt_two P
        rw [abs_div, abs_of_pos hPpos, div_le_iff₀ hPpos, ← pow_add] at hchgBound
        exact_mod_cast hchgBound
      have hGnPos : 1 ≤ G.n := by
        have htV := (hdg0.1 row.1 heiG0).1
        have htLt := hdg0.2.1 _ htV
        rw [hGeq] at htLt; omega
      have hB6 : 6 * B_bound < (Num.capacity 4 L : ℤ) := by
        have h0B : 0 ≤ B_bound := le_trans hnum.1 hB
        have h0R : 0 ≤ R_bound := le_trans hnum.2.1 hR
        have h3 : (3 : ℤ) ≤ ((2 * G.n + 1 : ℕ) : ℤ) := by omega
        have hmp : (0 : ℤ) ≤ (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P) :=
          mul_nonneg (Int.natCast_nonneg _) (pow_nonneg (by decide) _)
        have h1 : 6 * B_bound ≤ 2 * ((2 * G.n + 1 : ℕ) : ℤ) *
            ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P)) +
              (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P))) := by
          calc 6 * B_bound = (2 * 3) * B_bound := by ring
            _ ≤ (2 * ((2 * G.n + 1 : ℕ) : ℤ)) * B_bound :=
                  mul_le_mul_of_nonneg_right (by omega) h0B
            _ ≤ (2 * ((2 * G.n + 1 : ℕ) : ℤ)) *
                  ((B_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P)) +
                    (R_bound + (maxPaths : ℤ) * (2 : ℤ) ^ (3 * E + 2 + P))) :=
                  mul_le_mul_of_nonneg_left (by omega) (by omega)
        exact lt_of_le_of_lt h1 hcapP
      have h2PowSmall : 4 * (2 * (2 : ℤ) ^ (3 * E + 1 + P)) < (Num.capacity 4 L : ℤ) := by
        rw [← hcap4L]
        have h1 : 4 * (2 * (2 : ℤ) ^ (3 * E + 1 + P)) = (2 : ℤ) ^ (3 * E + 4 + P) := by
          rw [show 3 * E + 4 + P = (3 * E + 1 + P) + 3 by omega, pow_add]; ring
        rw [h1]
        exact pow_lt_pow_right₀ (by decide) (by dsimp only [E, P, L] at hwidth ⊢; omega)
      have hdAbs := abs_le.mp hdetOld
      have h0B : 0 ≤ B_bound := le_trans hnum.1 hB
      have hv0 : 0 ≤ |mult * n| := abs_nonneg _
      unfold Num.Fits
      dsimp only [E, P, L] at hB6 h2PowSmall hmnAbsLe hdAbs h0B hB hv0 ⊢
      omega
    exact ⟨hnFit, hmnFit, hmnAbsFit, hflNewFit, hdetNewFit⟩
  refine ⟨hcapPos, h2nWT, hlogWT, hmagPos, hfitMag, hstep, hfitMult, hfitAbs,
    hconnTree, hcapTree, hBend, hRend, hFitsEnd, address, old, haddr, hdisj, hfitOff, ?_⟩
  -- Post-apply accounts, `TreeEditNamedSlots`, and `SolverEdgeOrientInv`
  intro mem' trees' depth' s' hlct' hupdOff hfr hioMono hioPres
  have hkeep {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (hv14 : v ≠ 14)
      (hv15 : v ≠ 15) (hv16 : v ≠ 16) (hv18 : v ≠ 18) : mem' a = mem a := by
    have hRng := hfootRng a (Or.inl (hOwn a (ht ▸ hv0)))
    exact hfr a hRng.1 hRng.2
      (fun ei hei => by
        by_contra h; push Not at h
        have h18 := (haddr ei hei).2.2.2.1 (a - address ei) (by omega)
        rw [show address ei + (a - address ei) = a by omega] at h18
        exact hv18 (ht.symm.trans h18))
      (ht ▸ hv1) (ht ▸ hv14) (ht ▸ hv15) (ht ▸ hv16)
  have hslotEq (ei : ℕ) (hei : ei < tok.intCap) : mem' (tok.slots + ei) = mem (tok.slots + ei) :=
    hkeep (t9 ei hei) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hnameEq (sl : ℕ) (hsl : sl < 2 * tok.tree.n) : mem' (tok.names + sl) = mem (tok.names + sl) :=
    hkeep (t10 sl hsl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hslThrEq (sl : ℕ) (hsl : sl < 2 * tok.tree.n) :
      mem' (tok.slotThresholds + sl) = mem (tok.slotThresholds + sl) :=
    hkeep (t11 sl hsl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have heThrEq (ei : ℕ) (hei : ei < tok.intCap) :
      mem' (tok.edgeThresholds + ei) = mem (tok.edgeThresholds + ei) :=
    hkeep (t12 ei hei) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have heRecEq (ei : ℕ) (hei : ei < tok.intCap) :
      mem' (tok.edgeRecords + ei) = mem (tok.edgeRecords + ei) :=
    hkeep (t13 ei hei) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hns', hfoldAcc⟩ := applyPathsFold_account hFTforest paths hlct hns
    (fun ei hei => ⟨htn.symm ▸ (hFTvalid ei hei).2.1, htn.symm ▸ (hFTvalid ei hei).2.2.1, (hFTvalid ei hei).2.2.2⟩)
    (fun p hp => ⟨htn.symm ▸ (hroute.2.1 p hp).1, htn.symm ▸ (hroute.2.1 p hp).2.1, (hroute.2.1 p hp).2.2⟩)
    hlct'
  have hs'n : s'.n = tok.tree.n := by
    have : ∀ (ps : List (ℕ × ℕ)) (st : PathTreeState), (applyPathsFold st (PathTag.ofFlow mult) ps).n = st.n := by
      intro ps; induction ps with
      | nil => intro _; rfl
      | cons p rest ih => intro st; exact ih _
    exact this paths tok.tree
  have hns'Mem : TreeEditNamedSlots s' trees' FT
      (fun f => mem' (tok.slots + f)) (fun k => mem' (tok.names + k)) := by
    refine ⟨fun ei hei => ?_, fun sl hsl hls => ?_, fun ei hei => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hns'.forward ei hei
      have hslLt : mem (tok.slots + ei) < 2 * tok.tree.n := by
        unfold isEdgeSlot at h2; rw [hs'n] at h2; omega
      rw [hslotEq ei (hFTvalid ei hei).1, hnameEq _ hslLt]
      exact ⟨h1, h2, h3⟩
    · have hslLt : sl < 2 * tok.tree.n := by
        unfold isEdgeSlot at hls; rw [hs'n] at hls; omega
      obtain ⟨h1, h2⟩ := hns'.inverse sl hsl hls
      rw [hnameEq sl hslLt, hslotEq _ (hFTvalid _ h1).1]
      exact ⟨h1, h2⟩
    · have he := hns'.endpoints ei hei
      dsimp only at he ⊢
      rw [hslotEq ei (hFTvalid ei hei).1]
      exact he
  have hactPerm : (trees'.flatMap AuxTree.toList).Perm (tok.trees.flatMap AuxTree.toList) := by
    have hnd1 := hlct'.activeNodup
    have hnd2 := hlct.activeNodup
    refine (List.perm_ext_iff_of_nodup hnd1 hnd2).mpr fun x => ?_
    constructor <;> intro hx
    · exact lct_active_mem_of_same_freeList hlct hlct' hs'n hx
    · exact lct_active_mem_of_same_freeList hlct' hlct hs'n.symm hx
  have hPpos : (0 : ℝ) < (2 : ℝ) ^ P := pow_pos zero_lt_two P
  have hactEq : actual = -(((mult : ℝ) / (2 : ℝ) ^ P) * modelLoop.extG.inner modelLoop.extg Δ) := by
    dsimp only [actual]; rw [hinnerEq]
  have hincMul (e : ℕ) (he : e ∈ modelLoop.extG.E) :
      inc e = ((mult : ℝ) / (2 : ℝ) ^ P) * (algorithm1_findCycle modelLoop.chain).1 (modelLoop.extToInt e) := by
    dsimp only [inc]
    rw [ite_eq_left he, hactEq, pathFlow_normalization hinnerNe]
    dsimp only [Δ, liftEdgeFn]
    rw [ite_eq_left he]
  refine ⟨⟨?_, ?_⟩, hns'Mem, ?_⟩
  · -- `SolverEdgeAccountsAt` part 1: every `e ∈ modelLoop.extG.E`
    intro e he
    let ei := modelLoop.extToInt e
    obtain ⟨heiCap, hthrAt, hbranch⟩ := hedgeAcc.1 e he
    have hthrAt' : PathIntAt mem' (mem' (tok.edgeThresholds + ei)) 4 L
        (detectorThreshold P cfg.ε (modelLoop.extℓ e)) := by
      rw [heThrEq ei heiCap]
      exact hthrAt.congr fun i hi =>
        hkeep ((t1718 e he).1 i hi) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    refine ⟨heiCap, hthrAt', ?_⟩
    by_cases hFT : ei ∈ FT.E
    · rw [ite_eq_left hFT] at hbranch ⊢
      obtain ⟨hslNZ, hslEdge, hnm, hslThr, val, acc, hpOld, hflOld, haccOld, hdetOld⟩ := hbranch
      have horE := horient e he
      rw [ite_eq_left hFT] at horE
      obtain ⟨_, _, hftOld, hffOld⟩ := horE val hpOld
      obtain ⟨val', hp', hfl', hdet', _, _, _, _⟩ := hfoldAcc ei hFT val hpOld ⟨hftOld, hffOld⟩
      have hslLt : mem (tok.slots + ei) < 2 * tok.tree.n := hslEdge.2
      have hzeroEdges : (edges.map (fun x => walkFlow [x] ei)).sum = 0 := by
        apply List.sum_eq_zero; intro z hz
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
        apply walkFlow_eq_zero_of_not_mem
        have hne : x.1 ≠ ei := fun h => (Finset.mem_sdiff.mp (hroute.1 x hx)).2 (h.symm ▸ hFT)
        simp [walkEdges, Ne.symm hne]
      have hC_tree : (algorithm1_findCycle modelLoop.chain).1 ei =
          (paths.map (fun p => walkFlow (FT.forestPath p.1 p.2) ei)).sum := by
        have h := (hroute.2.2 e he).1; rw [hzeroEdges, zero_add] at h; exact h
      have habs_tree : |((mult : ℝ) / (2 : ℝ) ^ P) * (algorithm1_findCycle modelLoop.chain).1 ei| =
          (paths.map (fun p => |((mult : ℝ) / (2 : ℝ) ^ P) * walkFlow (FT.forestPath p.1 p.2) ei|)).sum := by
        have h := (hroute.2.2 e he).2 ((mult : ℝ) / (2 : ℝ) ^ P)
        rw [hzeroEdges, mul_zero, abs_zero, zero_add] at h; exact h
      have hdetSum : ((val'.detector : ℝ) - (val.detector : ℝ)) / (2 : ℝ) ^ P = |inc e| := by
        rw [hincMul e he, habs_tree, hdet', add_sub_cancel_left]
        exact sum_abs_mul_div_pow paths (fun p => walkFlow (FT.forestPath p.1 p.2) ei) mult P
      refine ⟨by rw [hslotEq ei heiCap]; exact hslNZ,
        by rw [hslotEq ei heiCap, hs'n]; exact hslEdge,
        by rw [hslotEq ei heiCap, hnameEq _ hslLt]; exact hnm,
        by rw [hslotEq ei heiCap, hslThrEq _ hslLt, heThrEq ei heiCap]; exact hslThr,
        val', acc + (val'.detector - val.detector),
        by rw [hslotEq ei heiCap]; exact hp', ?_, ?_, by dsimp only [P] at hdetOld ⊢; omega⟩
      · change (val'.originalFlow : ℝ) / (2 : ℝ) ^ P = modelLoop.flow e + inc e
        rw [hfl', add_div, hflOld, hincMul e he, hC_tree, div_mul_eq_mul_div]
      · change ((acc + (val'.detector - val.detector) : ℤ) : ℝ) / (2 : ℝ) ^ P =
          modelLoop.detectAccum e + |inc e|
        rw [Int.cast_add, Int.cast_sub, add_div, haccOld, hdetSum]
    · rw [ite_eq_right hFT] at hbranch ⊢
      obtain ⟨hsl0, val, acc, hpaOld, hflOld, haccOld, hdetOld, hioOld⟩ := hbranch
      have horE := horient e he
      rw [ite_eq_right hFT] at horE
      have hfwdOld : val.forward = true := (horE val hpaOld).1
      refine ⟨(hslotEq ei heiCap).trans hsl0, ?_⟩
      by_cases heiIn : ei ∈ edges.map Prod.fst
      · have hvalEq : old ei = val := pathEdgeAt_unique (haddr ei heiIn).2.2.1 hpaOld
        let net : ℤ := (edges.count (ei, true) : ℤ) - (edges.count (ei, false) : ℤ)
        let val' := updatedOffTreeVal edges old mult ei
        obtain ⟨hpa', hio'⟩ := hupdOff ei heiIn
        have hCeq := offTree_cycle_increment_of_signed_count hFT edges paths
          (fun p hp => (hroute.2.1 p hp).2.2) (algorithm1_findCycle modelLoop.chain).1
          (hroute.2.2 e he).1 ((mult : ℝ) / (2 : ℝ) ^ P)
        have hincOff : inc e = ((mult * net : ℤ) : ℝ) / (2 : ℝ) ^ P := by
          rw [hincMul e he, hCeq.1, Int.cast_mul, div_mul_eq_mul_div]
        have habsOff : |inc e| = ((|mult * net| : ℤ) : ℝ) / (2 : ℝ) ^ P := by
          rw [hincOff, abs_div, abs_of_pos hPpos, Int.cast_abs]
        refine ⟨val', acc + |mult * net|, by rw [heRecEq ei heiCap]; exact hpa', ?_, ?_, ?_, hio'⟩
        · change (val'.originalFlow : ℝ) / (2 : ℝ) ^ P = modelLoop.flow e + inc e
          have hsh : val'.originalFlow = val.originalFlow + mult * net := by
            dsimp only [val', updatedOffTreeVal]
            rw [hvalEq, PathEdgeValue.originalFlow_shift, ite_eq_left hfwdOld]; rfl
          rw [hsh, Int.cast_add, add_div, hflOld, hincOff]
        · change ((acc + |mult * net| : ℤ) : ℝ) / (2 : ℝ) ^ P = modelLoop.detectAccum e + |inc e|
          rw [Int.cast_add, add_div, haccOld, habsOff]
        · dsimp only [val', updatedOffTreeVal, PathEdgeValue.shift, PathTag.ofFlow]
          rw [hvalEq, hdetOld]; ring
      · -- Off-tree edge not in `edges`: `inc e = 0`, block untouched
        obtain ⟨ht0, hf0⟩ := (explicitEdge_counts_zero_iff edges ei).2 heiIn
        have hCeq := offTree_cycle_increment_of_signed_count hFT edges paths
          (fun p hp => (hroute.2.1 p hp).2.2) (algorithm1_findCycle modelLoop.chain).1
          (hroute.2.2 e he).1 ((mult : ℝ) / (2 : ℝ) ^ P)
        have hinc0 : inc e = 0 := by rw [hincMul e he, hCeq.1]; simp [ht0, hf0]
        have hpa' : PathEdgeAt mem' (mem' (tok.edgeRecords + ei)) 4 L (some val) := by
          rw [heRecEq ei heiCap]
          refine hpaOld.congr fun a ha1 ha2 => ?_
          have ht18a : tok.tag a = 18 := by
            rw [show a = mem (tok.edgeRecords + ei) + (a - mem (tok.edgeRecords + ei)) by
              dsimp only [ei] at ha1 ⊢; omega]
            exact (t1718 e he).2 hFT _ (by dsimp only [ei, L] at ha1 ha2 ⊢; omega)
          have hRng := hfootRng a (Or.inl (hOwn a (by rw [ht18a]; decide)))
          exact hfr a hRng.1 hRng.2 (fun f hf => by
            obtain ⟨rf, hrf, rfl⟩ := List.mem_map.mp hf
            obtain ⟨hfG0, hfnFT⟩ := Finset.mem_sdiff.mp (hroute.1 rf hrf)
            obtain ⟨hefExt, hfeq⟩ := hinvExt rf.1 hfG0
            have hneExt : e ≠ modelLoop.intToExt rf.1 := fun h => heiIn (by
              have : ei = rf.1 := (congrArg modelLoop.extToInt h).trans hfeq
              rw [this]; exact List.mem_map.mpr ⟨rf, hrf, rfl⟩)
            have hd := hOff.2 e he _ hefExt hneExt hFT (hfeq.symm ▸ hfnFT)
            rw [hfeq] at hd
            rcases hd with hd | hd <;> [exact Or.inl (by dsimp only [address, ei, L] at ha1 ha2 hd ⊢; omega);
              exact Or.inr (by dsimp only [address, ei, L] at ha1 ha2 hd ⊢; omega)])
            (by rw [ht18a]; decide) (by rw [ht18a]; decide) (by rw [ht18a]; decide) (by rw [ht18a]; decide)
        refine ⟨val, acc, hpa', ?_, ?_, hdetOld, fun hd => hioMono ei heiCap (hioOld hd)⟩
        · change (val.originalFlow : ℝ) / (2 : ℝ) ^ P = modelLoop.flow e + inc e
          rw [hinc0, add_zero]; exact hflOld
        · change (acc : ℝ) / (2 : ℝ) ^ P = modelLoop.detectAccum e + |inc e|
          rw [hinc0, abs_zero, add_zero]; exact haccOld
  · -- `SolverEdgeAccountsAt` part 2: every active edge slot in `s'`
    intro sl val hslEdge hfp
    have hslEdge0 : isEdgeSlot tok.tree.n sl := hs'n ▸ hslEdge
    have hslLt : sl < 2 * tok.tree.n := by unfold isEdgeSlot at hslEdge0; omega
    obtain ⟨val0, hfp0⟩ := applyPathsFold_some_back paths hlct hns
      (fun ei hei => ⟨htn.symm ▸ (hFTvalid ei hei).2.1, htn.symm ▸ (hFTvalid ei hei).2.2.1⟩)
      (fun p hp => ⟨htn.symm ▸ (hroute.2.1 p hp).1, htn.symm ▸ (hroute.2.1 p hp).2.1, (hroute.2.1 p hp).2.2⟩)
      hlct' sl val hfp
    obtain ⟨heiCap, eiFT, hslotEi, heExt, he2i⟩ := hedgeAcc.2 sl val0 hslEdge0 hfp0
    dsimp only
    rw [hnameEq sl hslLt, hslotEq _ heiCap]
    exact ⟨heiCap, eiFT, hslotEi, heExt, he2i⟩
  · -- `SolverEdgeOrientInv`
    intro e he
    let ei := modelLoop.extToInt e
    have heiCap := (hedgeAcc.1 e he).1
    have horE := horient e he
    by_cases hFT : ei ∈ FT.E
    · rw [ite_eq_left hFT] at horE ⊢
      intro val' hp'
      have hacc := (hedgeAcc.1 e he).2.2
      rw [ite_eq_left hFT] at hacc
      obtain ⟨_, _, _, _, val, _, hpOld, _, _, _⟩ := hacc
      obtain ⟨hgrOld, hlenOld, hftOld, hffOld⟩ := horE val hpOld
      obtain ⟨val1, hp1, _, _, hgr1, hlen1, hft1, hff1⟩ := hfoldAcc ei hFT val hpOld ⟨hftOld, hffOld⟩
      rw [hslotEq ei heiCap] at hp' ⊢
      have hvalEq : val' = val1 := Option.some.inj (forestPairs_snd_unique hlct'.activeNodup hp' hp1)
      subst hvalEq
      exact ⟨hgr1.symm ▸ hgrOld, hlen1.symm ▸ hlenOld, hft1, hff1⟩
    · rw [ite_eq_right hFT] at horE ⊢
      intro val' hpa'
      rw [heRecEq ei heiCap] at hpa'
      by_cases heiIn : ei ∈ edges.map Prod.fst
      · obtain ⟨hpaU, _⟩ := hupdOff ei heiIn
        have hvalEq : val' = updatedOffTreeVal edges old mult ei := pathEdgeAt_unique hpa' hpaU
        have hpaOld : PathEdgeAt mem (address ei) 4 L (some (old ei)) := (haddr ei heiIn).2.2.1
        obtain ⟨hfwdO, hgrO, hlenO⟩ := horE (old ei) hpaOld
        subst hvalEq
        refine ⟨hfwdO, ?_, hlenO⟩
        dsimp only [updatedOffTreeVal, PathEdgeValue.originalGradient, PathEdgeValue.shift]
        simpa [PathEdgeValue.originalGradient, hfwdO] using hgrO
      · have hpaOld : PathEdgeAt mem (mem (tok.edgeRecords + ei)) 4 L (some val') := by
          refine hpa'.congr fun a ha1 ha2 => ?_
          have ht18a : tok.tag a = 18 := by
            rw [show a = mem (tok.edgeRecords + ei) + (a - mem (tok.edgeRecords + ei)) by
              dsimp only [ei] at ha1 ⊢; omega]
            exact (t1718 e he).2 hFT _ (by dsimp only [ei, L] at ha1 ha2 ⊢; omega)
          have hRng := hfootRng a (Or.inl (hOwn a (by rw [ht18a]; decide)))
          exact (hfr a hRng.1 hRng.2 (fun f hf => by
            obtain ⟨rf, hrf, rfl⟩ := List.mem_map.mp hf
            obtain ⟨hfG0, hfnFT⟩ := Finset.mem_sdiff.mp (hroute.1 rf hrf)
            obtain ⟨hefExt, hfeq⟩ := hinvExt rf.1 hfG0
            have hneExt : e ≠ modelLoop.intToExt rf.1 := fun h => heiIn (by
              have : ei = rf.1 := (congrArg modelLoop.extToInt h).trans hfeq
              rw [this]; exact List.mem_map.mpr ⟨rf, hrf, rfl⟩)
            have hd := hOff.2 e he _ hefExt hneExt hFT (hfeq.symm ▸ hfnFT)
            rw [hfeq] at hd
            rcases hd with hd | hd <;> [exact Or.inl (by dsimp only [address, ei, L] at ha1 ha2 hd ⊢; omega);
              exact Or.inr (by dsimp only [address, ei, L] at ha1 ha2 hd ⊢; omega)])
            (by rw [ht18a]; decide) (by rw [ht18a]; decide) (by rw [ht18a]; decide) (by rw [ht18a]; decide)).symm
        exact horE val' hpaOld

end MinCostFlow.MinRatio
