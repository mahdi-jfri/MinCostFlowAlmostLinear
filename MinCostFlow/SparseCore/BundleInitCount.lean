module

public import MinCostFlow.SparseCore.BundleStageBase

/-!
# The size of the initial bundle graphs

At the start of a run each pair of a component `C` and a bucket `b` cuts the restricted tours of
the core rotation into chunks of at most `k` ends. A vertex gets
`⌈d / k⌉` chunks when `d` admitted ends lie at it, and only roots of `C` carry ends of the edges of
`C`. So `k` times the number of bundles of `(C, b)` is at most `k` times the number of roots of
`C` plus twice the number of edges of `(C, b)`. Summed over the active
buckets this gives `initBundleTree_vertex_sum_le`.

A component that is not large has one root and fewer than `k / 4` edges, so each of its buckets
has at most one bundle.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.DynSpanner MinCostFlow.Bundle

private theorem ceil_capacity_le' (n k : ℕ) (hk : 0 < k) : k * (n ⌈/⌉ k) ≤ k + n := by
  have hmod := Nat.mod_lt n hk
  have hdiv := Nat.mod_add_div n k
  have h₁ : n ≤ k * (n / k + 1) := by
    rw [Nat.mul_succ]
    omega
  have h₂ : n ⌈/⌉ k ≤ n / k + 1 := (ceilDiv_le_iff_le_mul hk).2 h₁
  apply (Nat.mul_le_mul_left k h₂).trans
  rw [Nat.mul_succ]
  omega

private theorem chunk_count_le {α : Type*} (f : ℕ → List α) (k : ℕ) (hk : 0 < k) :
    ∀ vs : List ℕ, k * (vs.map fun v => (f v).length ⌈/⌉ k).sum ≤
      k * (vs.filter fun v => f v ≠ []).length + (vs.flatMap f).length
  | [] => by simp
  | v :: vs => by
    have ih := chunk_count_le f k hk vs
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, Nat.mul_add]
    by_cases hv : f v = []
    · have hfil : ((v :: vs).filter fun v => f v ≠ []) = vs.filter fun v => f v ≠ [] := by
        simp [hv]
      rw [hfil, hv]
      have h00 : (0 : ℕ) ⌈/⌉ k = 0 := Nat.le_zero.mp ((ceilDiv_le_iff_le_mul hk).2 (by simp))
      simp only [List.length_nil, h00, Nat.mul_zero, Nat.zero_add]
      exact ih
    · have hfil : ((v :: vs).filter fun v => f v ≠ []).length =
          (vs.filter fun v => f v ≠ []).length + 1 := by
        simp [hv]
      rw [hfil]
      have h := ceil_capacity_le' (f v).length k hk
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- The number of initial bundles counted against a set `S` that holds the sources of all
admitted ends: `k` times the bundles is at most `k |S| + 2 |E|`. -/
theorem initBundleState_vertex_bound_at {C : MGraph} (ρ : Rotation C) {E : Finset ℕ}
    (hE : E ⊆ C.E) {k : ℕ} (hk : 0 < k) (S : Finset ℕ)
    (hS : ∀ x : End, x.1 ∈ E → C.src x ∈ S) :
    k * (initBundleState ρ E k).vertices.card ≤ k * S.card + 2 * E.card := by
  classical
  let vs := C.V.sort (· ≤ ·)
  have hvs : vs.Nodup := Finset.sort_nodup _ _
  have hcard : (initBundleState ρ E k).vertices.card =
      (vs.map fun v => (restrictedEnds ρ E v).length ⌈/⌉ k).sum := by
    simp [initBundleState, initialSlots, vs, List.length_flatMap, initialChunks_length]
  have hA := chunk_count_le (restrictedEnds ρ E) k hk vs
  have hB : (vs.filter fun v => restrictedEnds ρ E v ≠ []).length ≤ S.card := by
    rw [← List.toFinset_card_of_nodup (hvs.filter _)]
    apply Finset.card_le_card
    intro v hv
    have hv' := (List.mem_filter.mp (List.mem_toFinset.mp hv)).2
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (of_decide_eq_true hv')
    obtain ⟨hxE, hxv⟩ := (mem_restrictedEnds ρ hE v x).mp hx
    exact hxv ▸ hS x hxE
  have hC : (vs.flatMap (restrictedEnds ρ E)).length ≤ 2 * E.card := by
    have hnd : (vs.flatMap (restrictedEnds ρ E)).Nodup := by
      refine List.nodup_flatMap.mpr ⟨fun v _ => (ρ.nodup v).filter _, ?_⟩
      refine hvs.imp fun {v w} hne => ?_
      refine List.disjoint_left.mpr fun {x} hx hx' => hne ?_
      exact ((mem_restrictedEnds ρ hE v x).mp hx).2.symm.trans
        ((mem_restrictedEnds ρ hE w x).mp hx').2
    rw [← List.toFinset_card_of_nodup hnd, ← card_edgeEnds]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨v, -, hxv⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hx)
    exact (mem_edgeEnds E x).mpr ((mem_restrictedEnds ρ hE v x).mp hxv).1
  rw [hcard]
  have := Nat.mul_le_mul_left k hB
  omega

/-- The initial bundle state of a component and bucket is `initBundleState` for some rotation, or
it is empty. -/
theorem initBundleFor_cases (cs : CompLSFState) (ord : ℕ → List End) (E : Finset ℕ) (k : ℕ) :
    (∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (hI : CompLSFInv C_lsst ℓ₀ cs) (ρ : Rotation cs.G),
      initBundleFor cs ord E k =
        initBundleState (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) E k) ∨
    initBundleFor cs ord E k = ⟨∅, ∅, fun _ => 0, fun _ => 0⟩ := by
  classical
  by_cases h : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ cs) (ρ : Rotation cs.G),
      ρ.order = ord
  · obtain ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩ := h
    exact Or.inl ⟨C_lsst, ℓ₀, hI, ρ, initBundleFor_eq hI hρ E k⟩
  · right
    unfold initBundleFor
    rw [dite_eq_right h]

/-- The vertex and edge counts of the initial bundle graphs for an arbitrary `lsfInit`. -/
theorem initBundleTreeWith_vertex_sum_le
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (hk : 1 ≤ k) (G₀ : MGraph) (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (ℓ₀ : ℕ → ℝ) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (ord : ℕ → List End) (j : ℕ)
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (B_bound : ℕ)
    (hB : ∀ C ∈ components G₀,
      ((initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).activeBuckets C).card ≤
        B_bound) :
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j
    k * ((components G₀).sum fun C => (st₀.activeBuckets C).sum fun b =>
      (st₀.bun (C, b)).vertices.card) ≤ k * B_bound * st₀.cs.RF.R.card + 2 * G₀.m ∧
    (∀ C ∈ components G₀, C ∉ largeComps k G₀ → ∀ b : ℤ, (st₀.bun (C, b)).vertices.card ≤ 11) ∧
    ((components G₀).sum fun C => (st₀.activeBuckets C).sum fun b =>
      (st₀.bun (C, b)).edges.card) ≤ G₀.m := by
  classical
  intro st₀
  set cs₀ := st₀.cs with hcs₀
  have hk0 : 0 < k := hk
  have hI₀ : CompLSFInv C_lsst ℓ₀ cs₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  set C₀ := coreGraph G₀ cs₀.lsf
  set origB := st₀.origBucket
  let E : Finset ℕ → ℤ → Finset ℕ := fun C b => bucketCoreEdges C₀ origB C b
  have hbun : ∀ C b, st₀.bun (C, b) = initBundleFor cs₀ ord (E C b) k := fun _ _ => rfl
  have hGC : ∀ C ∈ components G₀, (cs₀.compSt C).G = compGraph G₀ C := fun C hC =>
    (initCompLSFWith_compSt_basic hInit hG₀ hℓ₀ hk hC).2.1
  -- The edges of a bucket are edges of its component.
  have hEC : ∀ C ∈ components G₀, ∀ b, E C b ⊆ (cs₀.compSt C).G.E := by
    intro C hC b e he
    obtain ⟨heC, htC, -⟩ := Finset.mem_filter.mp he
    have heG : e ∈ cs₀.G.E := (Finset.mem_sdiff.mp heC).1
    have hroot : cs₀.RF.root (cs₀.G.tail e) ∈ (cs₀.compSt C).G.V := by
      rw [hGC C hC]
      exact htC
    have ht := compLSF_mem_V_of_root hI₀ hC (hI₀.hG_val e heG).1 hroot
    rw [hGC C hC] at ht ⊢
    exact Finset.mem_filter.mpr ⟨heG, ht⟩
  -- One bucket: the bundle count, and the edge count.
  have hone : ∀ C ∈ components G₀, ∀ b,
      k * (st₀.bun (C, b)).vertices.card ≤ k * (cs₀.compSt C).R.card + 2 * (E C b).card ∧
      (st₀.bun (C, b)).edges.card ≤ (E C b).card := by
    intro C hC b
    rw [hbun]
    rcases initBundleFor_cases cs₀ ord (E C b) k with ⟨C', ℓ', hI', ρ, hρ⟩ | h0
    · rw [hρ]
      refine ⟨initBundleState_vertex_bound_at _ (Finset.filter_subset _ _) hk0 _ ?_, le_rfl⟩
      intro x hx
      obtain ⟨e, side⟩ := x
      have heC := hEC C hC b hx
      have hends := hI₀.hNonCross_ends C hC e heC (Finset.notMem_empty e)
      have hval := (hI₀.hCompLSF C hC).1.hG_val e heC
      rw [coreGraph_src]
      apply compLSF_root_mem_R hI₀ hC
      cases side
      · change cs₀.G.head e ∈ _
        rw [← hends.2]
        exact hval.2
      · change cs₀.G.tail e ∈ _
        rw [← hends.1]
        exact hval.1
    · rw [h0]
      simp
  -- The edge sets of distinct components, and of distinct buckets, are disjoint.
  have htail : ∀ C b, ∀ e ∈ E C b, C₀.tail e ∈ C ∧ origB e = b := fun C b e he =>
    (Finset.mem_filter.mp he).2
  have hcompDisj : ∀ C ∈ components G₀, ∀ C' ∈ components G₀, C ≠ C' → Disjoint C C' := by
    intro C hC C' hC' hne
    have hd := hI₀.hV_disj C hC C' hC' hne
    rwa [hGC C hC, hGC C' hC'] at hd
  have hsumE : ((components G₀).sum fun C => (st₀.activeBuckets C).sum fun b =>
      (E C b).card) ≤ G₀.m := by
    have hinner : ∀ C ∈ components G₀, ((st₀.activeBuckets C).sum fun b => (E C b).card) =
        ((st₀.activeBuckets C).biUnion fun b => E C b).card := by
      intro C _
      refine (Finset.card_biUnion fun b _ b' _ hne => ?_).symm
      exact Finset.disjoint_left.mpr fun e he he' =>
        hne ((htail C b e he).2.symm.trans (htail C b' e he').2)
    rw [Finset.sum_congr rfl hinner, ← Finset.card_biUnion]
    · refine (Finset.card_le_card ?_).trans (Finset.card_le_card (Finset.sdiff_subset (t :=
        cs₀.RF.F.E)))
      intro e he
      obtain ⟨C, -, hC⟩ := Finset.mem_biUnion.mp he
      obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.mp hC
      exact (Finset.mem_filter.mp hb).1
    · intro C hC C' hC' hne
      refine Finset.disjoint_left.mpr fun e he he' => ?_
      obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.mp he
      obtain ⟨b', -, hb'⟩ := Finset.mem_biUnion.mp he'
      exact Finset.disjoint_left.mp (hcompDisj C hC C' hC' hne) (htail C b e hb).1
        (htail C' b' e hb').1
  -- The roots split over the components.
  have hsumR : ((components G₀).sum fun C => (cs₀.compSt C).R.card) = cs₀.RF.R.card := by
    have hR : cs₀.RF.R = (components G₀).biUnion fun C => (cs₀.compSt C).R := rfl
    rw [hR, Finset.card_biUnion]
    intro C hC C' hC' hne
    exact Finset.disjoint_of_subset_left (lsfInv_R_sub_V (hI₀.hCompLSF C hC).1)
      (Finset.disjoint_of_subset_right (lsfInv_R_sub_V (hI₀.hCompLSF C' hC').1)
        (hI₀.hV_disj C hC C' hC' hne))
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.mul_sum]
    calc ((components G₀).sum fun C => k * ((st₀.activeBuckets C).sum fun b =>
          (st₀.bun (C, b)).vertices.card))
        ≤ (components G₀).sum fun C => (st₀.activeBuckets C).sum fun b =>
          (k * (cs₀.compSt C).R.card + 2 * (E C b).card) := by
          refine Finset.sum_le_sum fun C hC => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun b _ => (hone C hC b).1
      _ = ((components G₀).sum fun C => (st₀.activeBuckets C).card * (k * (cs₀.compSt C).R.card))
          + 2 * ((components G₀).sum fun C => (st₀.activeBuckets C).sum fun b => (E C b).card) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun C _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.mul_sum]
      _ ≤ ((components G₀).sum fun C => B_bound * (k * (cs₀.compSt C).R.card)) + 2 * G₀.m :=
          Nat.add_le_add (Finset.sum_le_sum fun C hC => Nat.mul_le_mul_right _ (hB C hC))
            (Nat.mul_le_mul_left 2 hsumE)
      _ = k * B_bound * cs₀.RF.R.card + 2 * G₀.m := by
          rw [← hsumR, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun C _ => ?_
          ring
  · intro C hC hNL b
    have hlt : 4 * (compGraph G₀ C).m < k := by
      by_contra hge
      push Not at hge
      have hm1 : 1 ≤ (compGraph G₀ C).m := by
        have : 0 < 4 * (compGraph G₀ C).m := lt_of_lt_of_le hk hge
        omega
      exact hNL (Finset.mem_filter.mpr ⟨hC, hm1, hge⟩)
    have hℓs : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
      rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he
    have hR1 : (cs₀.compSt C).R.card = 1 := (initLSF_small_props_with hInit hG₀ hℓs hk hC hlt).1
    have hEm : (E C b).card ≤ (compGraph G₀ C).m := by
      have h := Finset.card_le_card (hEC C hC b)
      rwa [hGC C hC] at h
    have h := (hone C hC b).1
    rw [hR1] at h
    have hm : (compGraph G₀ C).m = (compGraph G₀ C).E.card := rfl
    have hV1 : (st₀.bun (C, b)).vertices.card ≤ 1 := by
      by_contra hgt
      push Not at hgt
      have : k * 2 ≤ k * (st₀.bun (C, b)).vertices.card := Nat.mul_le_mul_left k hgt
      omega
    omega
  · exact (Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b _ => (hone C hC b).2).trans hsumE

/-- The vertex and edge counts of the initial bundle graphs. -/
theorem initBundleTree_vertex_sum_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N : ℕ) (hk : 1 ≤ k) (G₀ : MGraph) (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (ℓ₀ : ℕ → ℝ) (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (ord : ℕ → List End) (j : ℕ) (B_bound : ℕ)
    (hB : ∀ C ∈ components G₀,
      ((initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).activeBuckets C).card ≤
        B_bound) :
    let st₀ := initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j
    k * ((components G₀).sum fun C => (st₀.activeBuckets C).sum fun b =>
      (st₀.bun (C, b)).vertices.card) ≤ k * B_bound * st₀.cs.RF.R.card + 2 * G₀.m ∧
    (∀ C ∈ components G₀, C ∉ largeComps k G₀ → ∀ b : ℤ, (st₀.bun (C, b)).vertices.card ≤ 11) ∧
    ((components G₀).sum fun C => (st₀.activeBuckets C).sum fun b =>
      (st₀.bun (C, b)).edges.card) ≤ G₀.m :=
  initBundleTreeWith_vertex_sum_le (initLSFOnline oracle C_lsst) C_lsst L sparsify k M N hk G₀ hG₀
    hV₀ ℓ₀ hℓ₀ ord j (initLSFOnline_isValidLSFInitFor hLSST k j) B_bound hB

/-- `initBundleTree_vertex_sum_le` in the form that `BundleRunInvBase.lean` takes as a
hypothesis. -/
theorem initBundleTree_vertex_sum_le_stmt : InitBundleTreeVertexSumLeStmt :=
  fun oracle C_lsst L sparsify hLSST k M N hk G₀ hG₀ hV₀ ℓ₀ hℓ₀ ord j B_bound hB =>
    initBundleTree_vertex_sum_le oracle C_lsst L sparsify hLSST k M N hk G₀ hG₀ hV₀ ℓ₀ hℓ₀ ord j
      B_bound hB

end MinCostFlow.SparseCore
