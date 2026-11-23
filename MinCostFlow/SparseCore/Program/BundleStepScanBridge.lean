module

public import MinCostFlow.SparseCore.Program.BundleStepScanAmort

/-!
# Bridge lemmas connecting Phase 2 Pass C scanned-end lists to Phase 3 (`BundleStepScanBridge`)

Defines `ScanValidForSlot` (the exact per-slot contract passed from Phase 2 Pass C into Phase 3)
and proves:
1. `addScanEndsForGroups_sum_le`: total scanned ends across all slots is at most
   `totalNonMaxLen cord' gs maxIdxs`, so `tourPot` pays for all Phase 3 scanned-end work.
2. `scanValidForSlot_of_scan`: under `hgs_nd`, `hgs_disj`, `hcord_nd`, `hmax_lt`, `hsrc_iff`,
   and `hbundle_in_group`, Phase 2 Pass C produces a `ScanValidForSlot` list for every active slot,
   with every candidate bundle having at least one scanned end (`(candSet j).card ≤ (scanEnds j).length`).
3. `scanValidForSlot_len_le_two_eCap`, `scanValidForSlot_len_le_candEndsSum`, and
   `nat_log_two_mul_le_ordStoreLog`: cardinality and logarithmic bounds used to absorb Phase 3
   sorting costs into `bundleScanPotMul TS eCap * totalNonMaxLen`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

open Classical

/-- Per-slot contract between Phase 2 Pass C and Phase 3:
1. No end key appears twice in `scan_j`.
2. Every entry `(b, v, k) ∈ scan_j` belongs to a candidate bundle `b ∈ candSet_j` with
   `endOfKey k ∈ B.ends b` and `src' (endOfKey k) = v`.
3. For every `b ∈ candSet_j`, there is a single remainder root `w_rem` such that no scanned entry
   of `b` has root `w_rem`, while every unscanned end of `b` has `src' x = w_rem`. -/
def ScanValidForSlot (B : BundleState) (src' : End → ℕ) (candSet_j : Finset ℕ)
    (scan_j : List (ℕ × ℕ × ℕ)) : Prop :=
  (scan_j.map fun t => t.2.2).Nodup ∧
  (∀ t ∈ scan_j, t.1 ∈ candSet_j ∧ endOfKey t.2.2 ∈ B.ends t.1 ∧ src' (endOfKey t.2.2) = t.2.1) ∧
  (∀ b ∈ candSet_j, ∃ w_rem : ℕ,
    (∀ t ∈ scan_j, t.1 = b → t.2.1 ≠ w_rem) ∧
    (∀ x ∈ B.ends b, endKey x ∉ scan_j.map (fun t => t.2.2) → src' x = w_rem))

end

public section

open Classical

/-! ## 1. Monotonicity of candidate sets -/

lemma addCandsForList_subset {slotCap : ℕ} (S : BundleTableState slotCap) (xs : List End)
    (cand₀ : Fin slotCap → Finset ℕ) (j : Fin slotCap) :
    cand₀ j ⊆ addCandsForList S xs cand₀ j := by
  unfold addCandsForList passBCands
  cases S j <;> simp

lemma addCandsForGroupPrefix_mono {slotCap : ℕ} (S : BundleTableState slotCap)
    (cord' : ℕ → List End) (G : List ℕ) (maxIdx : ℕ) (cand₀ : Fin slotCap → Finset ℕ)
    (j : Fin slotCap) {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) :
    addCandsForGroupPrefix S cord' G maxIdx cand₀ k₁ j ⊆
      addCandsForGroupPrefix S cord' G maxIdx cand₀ k₂ j := by
  induction hle with
  | refl => exact Finset.Subset.refl _
  | @step m _ ih =>
    refine Finset.Subset.trans ih ?_
    simp only [addCandsForGroupPrefix]
    split_ifs
    · exact Finset.Subset.refl _
    · exact addCandsForList_subset _ _ _ _
    · exact Finset.Subset.refl _

lemma addCandsForGroups_mono {slotCap : ℕ} (S : BundleTableState slotCap)
    (cord' : ℕ → List End) (gs : List (List ℕ)) (maxIdxs : List ℕ)
    (cand₀ : Fin slotCap → Finset ℕ) (j : Fin slotCap) {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) :
    addCandsForGroups S cord' gs maxIdxs cand₀ k₁ j ⊆
      addCandsForGroups S cord' gs maxIdxs cand₀ k₂ j := by
  induction hle with
  | refl => exact Finset.Subset.refl _
  | @step m _ ih =>
    refine Finset.Subset.trans ih ?_
    simp only [addCandsForGroups]
    exact addCandsForGroupPrefix_mono S cord' _ _ _ j (Nat.zero_le _)

/-! ## 2. Total scanned ends bounded by `totalNonMaxLen` -/

lemma addScanEndsForGroupPrefix_sum_le {slotCap : ℕ} {S : BundleTableState slotCap}
    (hdisj : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S j₁ = some B₁ → S j₂ = some B₂ → Disjoint B₁.edges B₂.edges)
    (cord' : ℕ → List End) (G : List ℕ) (maxIdx : ℕ)
    (cand₀ : Fin slotCap → Finset ℕ) (scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)) (k : ℕ) :
    (∑ j : Fin slotCap, (addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ k j).length) ≤
      (∑ j : Fin slotCap, (scan₀ j).length) + nonMaxLenPrefix cord' G maxIdx k := by
  induction k with
  | zero => simp [addScanEndsForGroupPrefix, nonMaxLenPrefix]
  | succ k ih =>
    simp only [addScanEndsForGroupPrefix, nonMaxLenPrefix]
    split_ifs with hlt hkm
    · omega
    · exact (addScanEndsForList_sum_le hdisj _ _ _ _).trans (by omega)
    · omega

theorem addScanEndsForGroups_sum_le {slotCap : ℕ} {S₀ : BundleTableState slotCap} {D : Finset ℕ}
    (hdisj₀ : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S₀ j₁ = some B₁ → S₀ j₂ = some B₂ → Disjoint B₁.edges B₂.edges)
    (cord' : ℕ → List End) (gs : List (List ℕ)) (maxIdxs : List ℕ)
    (cand₀ : Fin slotCap → Finset ℕ) :
    let S := tableDelEdges S₀ D
    (∑ j : Fin slotCap, (addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) gs.length j).length) ≤
      totalNonMaxLen cord' gs maxIdxs := by
  intro S
  have hdisj : ∀ j₁ j₂ : Fin slotCap, j₁ ≠ j₂ → ∀ B₁ B₂,
      S j₁ = some B₁ → S j₂ = some B₂ → Disjoint B₁.edges B₂.edges := by
    intro j₁ j₂ hne B₁ B₂ h1 h2
    simp only [S, tableDelEdges] at h1 h2
    cases hS1 : S₀ j₁ with
    | none => simp [hS1] at h1
    | some A₁ =>
      cases hS2 : S₀ j₂ with
      | none => simp [hS2] at h2
      | some A₂ =>
        simp only [hS1, hS2, Option.map_some, Option.some.injEq] at h1 h2
        subst h1; subst h2
        exact (hdisj₀ j₁ j₂ hne A₁ A₂ hS1 hS2).mono Finset.sdiff_subset Finset.sdiff_subset
  have hgo : ∀ k ≤ gs.length,
      (∑ j : Fin slotCap, (addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) k j).length) ≤
        ∑ gi ∈ Finset.range k,
          ∑ t ∈ (Finset.range (gs.getD gi []).length).erase (maxIdxs.getD gi 0),
            (cord' ((gs.getD gi []).getD t 0)).length := by
    intro k
    induction k with
    | zero => intro _; simp [addScanEndsForGroups]
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ]
      simp only [addScanEndsForGroups]
      have h1 := addScanEndsForGroupPrefix_sum_le hdisj cord' (gs.getD k []) (maxIdxs.getD k 0)
        (addCandsForGroups S cord' gs maxIdxs cand₀ k)
        (addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) k) (gs.getD k []).length
      rw [nonMaxLenPrefix_eq_finset_sum] at h1
      have h2 := ih (by omega)
      omega
  exact hgo gs.length (le_refl _)

/-! ## 3. Exact membership and `Nodup` of scanned-end lists -/

lemma addScanEndsForGroupPrefix_mem_iff {slotCap : ℕ} {S : BundleTableState slotCap}
    {cord' : ℕ → List End} {G : List ℕ} {maxIdx : ℕ}
    {cand₀ : Fin slotCap → Finset ℕ} {scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)}
    {j : Fin slotCap} {b w k : ℕ} :
    ∀ n ≤ G.length,
      (b, w, k) ∈ addScanEndsForGroupPrefix S cord' G maxIdx cand₀ scan₀ n j ↔
        (b, w, k) ∈ scan₀ j ∨
          ∃ B, S j = some B ∧ ∃ t, ∃ (_htn : t < n) (htG : t < G.length), t ≠ maxIdx ∧
            w = G[t]'htG ∧ ∃ x ∈ cord' w, x ∈ B.ends b ∧
              b ∈ addCandsForGroupPrefix S cord' G maxIdx cand₀ (t + 1) j ∧ endKey x = k := by
  intro n
  induction n with
  | zero => intro _; simp [addScanEndsForGroupPrefix]
  | succ n ih =>
    intro hn
    have hnG : n < G.length := by omega
    have ih' := ih (by omega)
    simp only [addScanEndsForGroupPrefix, hnG, ↓reduceDIte]
    split_ifs with hnm
    · rw [ih']
      constructor
      · rintro (h0 | ⟨B, hSj, t, htn, htG, hne, hw, hx⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨B, hSj, t, by omega, htG, hne, hw, hx⟩
      · rintro (h0 | ⟨B, hSj, t, htn, htG, hne, hw, hx⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨B, hSj, t, by omega, htG, hne, hw, hx⟩
    · rw [addScanEndsForList_mem_iff, ih']
      constructor
      · rintro ((h0 | ⟨B, hSj, t, htn, htG, hne, hw, hx⟩) | ⟨B, hSj, rfl, x, hx, hxB, hbc, rfl⟩)
        · exact Or.inl h0
        · exact Or.inr ⟨B, hSj, t, by omega, htG, hne, hw, hx⟩
        · exact Or.inr ⟨B, hSj, n, by omega, hnG, hnm, rfl, x, hx, hxB, hbc, rfl⟩
      · rintro (h0 | ⟨B, hSj, t, htn, htG, hne, rfl, x, hx, hxB, hbc, rfl⟩)
        · exact Or.inl (Or.inl h0)
        · by_cases ht : t = n
          · subst ht; exact Or.inr ⟨B, hSj, rfl, x, hx, hxB, hbc, rfl⟩
          · exact Or.inl (Or.inr ⟨B, hSj, t, by omega, htG, hne, rfl, x, hx, hxB, hbc, rfl⟩)

lemma addScanEndsForGroups_mem_iff {slotCap : ℕ} {S : BundleTableState slotCap}
    {cord' : ℕ → List End} {gs : List (List ℕ)} {maxIdxs : List ℕ}
    {cand₀ : Fin slotCap → Finset ℕ} {j : Fin slotCap} {b w k : ℕ} :
    ∀ n ≤ gs.length,
      (b, w, k) ∈ addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) n j ↔
        ∃ B, S j = some B ∧ ∃ gi, ∃ (_hgin : gi < n) (hgi : gi < gs.length),
          ∃ t, ∃ (ht : t < gs[gi].length), t ≠ maxIdxs.getD gi 0 ∧
            w = gs[gi][t] ∧ ∃ x ∈ cord' w, x ∈ B.ends b ∧
              b ∈ addCandsForGroupPrefix S cord' gs[gi] (maxIdxs.getD gi 0)
                (addCandsForGroups S cord' gs maxIdxs cand₀ gi) (t + 1) j ∧
              endKey x = k := by
  intro n
  induction n with
  | zero => intro _; simp [addScanEndsForGroups]
  | succ n ih =>
    intro hn
    have hnG : n < gs.length := by omega
    have hget : gs.getD n [] = gs[n] := List.getD_eq_getElem gs [] hnG
    have ih' := ih (by omega)
    simp only [addScanEndsForGroups, hget]
    rw [addScanEndsForGroupPrefix_mem_iff _ (le_refl _), ih']
    constructor
    · rintro (⟨B, hSj, gi, hgin, hgi, t, ht, hne, hw, hx⟩ | ⟨B, hSj, t, ht, _, hne, hw, hx⟩)
      · exact ⟨B, hSj, gi, by omega, hgi, t, ht, hne, hw, hx⟩
      · exact ⟨B, hSj, n, by omega, hnG, t, ht, hne, hw, hx⟩
    · rintro ⟨B, hSj, gi, hgin, hgi, t, ht, hne, hw, hx⟩
      by_cases hgn : gi = n
      · subst hgn; exact Or.inr ⟨B, hSj, t, ht, ht, hne, hw, hx⟩
      · exact Or.inl ⟨B, hSj, gi, by omega, hgi, t, ht, hne, hw, hx⟩

lemma addScanEndsForList_nodup_keys {slotCap : ℕ} {S : BundleTableState slotCap}
    {candSet : Fin slotCap → Finset ℕ} {v : ℕ} {xs : List End}
    {scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)} {j : Fin slotCap}
    (hnd₀ : ((scan₀ j).map fun t => t.2.2).Nodup)
    (hxs_nd : xs.Nodup)
    (hdisj : ∀ t ∈ scan₀ j, endOfKey t.2.2 ∉ xs) :
    ((addScanEndsForList S candSet v xs scan₀ j).map fun t => t.2.2).Nodup := by
  induction xs generalizing scan₀ with
  | nil => exact hnd₀
  | cons x rest ih =>
    simp only [addScanEndsForList, List.foldl_cons]
    obtain ⟨hx_not, hrest_nd⟩ := List.nodup_cons.mp hxs_nd
    set scan1 : Fin slotCap → List (ℕ × ℕ × ℕ) := fun j' =>
      match S j' with
      | none => scan₀ j'
      | some B =>
        if x.1 ∈ B.edges ∧ B.bundleOf x ∈ candSet j' then
          (B.bundleOf x, v, endKey x) :: scan₀ j'
        else scan₀ j'
    refine ih (scan₀ := scan1) ?_ hrest_nd ?_
    · dsimp only [scan1]
      cases hSj : S j with
      | none => exact hnd₀
      | some B =>
        dsimp only
        split_ifs
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨fun hm => ?_, hnd₀⟩
          obtain ⟨t, ht, htk⟩ := List.mem_map.mp hm
          have htx : endOfKey t.2.2 = x := by rw [htk, bundle_endOfKey_endKey]
          exact hdisj t ht (htx ▸ List.mem_cons_self)
        · exact hnd₀
    · intro t ht hmem
      dsimp only [scan1] at ht
      cases hSj : S j with
      | none => rw [hSj] at ht; exact hdisj t ht (List.mem_cons_of_mem _ hmem)
      | some B =>
        rw [hSj] at ht
        dsimp only at ht
        split_ifs at ht
        · rcases List.mem_cons.mp ht with rfl | ht'
          · simp only [bundle_endOfKey_endKey] at hmem; exact hx_not hmem
          · exact hdisj t ht' (List.mem_cons_of_mem _ hmem)
        · exact hdisj t ht (List.mem_cons_of_mem _ hmem)

lemma addScanEndsForGroups_nodup_keys {slotCap : ℕ} {S₀ : BundleTableState slotCap} {D : Finset ℕ}
    {j : Fin slotCap} {B₀ : BundleState} {cord' : ℕ → List End} {src' : End → ℕ}
    {gs : List (List ℕ)} {maxIdxs : List ℕ} {cand₀ : Fin slotCap → Finset ℕ}
    (hS₀j : S₀ j = some B₀)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_disj : ∀ i (hi : i < gs.length) j' (hj' : j' < gs.length), i ≠ j' →
      Disjoint gs[i].toFinset gs[j'].toFinset)
    (hcord_nd : ∀ G ∈ gs, ∀ w ∈ G, (cord' w).Nodup)
    (hsrc_iff : ∀ x ∈ edgeEnds (B₀.edges \ D), ∀ w, x ∈ cord' w ↔ src' x = w) :
    let S := tableDelEdges S₀ D
    ((addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) gs.length j).map
      fun t => t.2.2).Nodup := by
  intro S
  set B : BundleState := { B₀ with edges := B₀.edges \ D }
  have hSj : S j = some B := by simp [S, tableDelEdges, hS₀j, B]
  have hgo_grp : ∀ n ≤ gs.length,
      ((addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) n j).map fun t => t.2.2).Nodup := by
    intro n
    induction n with
    | zero => intro _; simp [addScanEndsForGroups]
    | succ n ih =>
      intro hn
      have hnG : n < gs.length := by omega
      have hget : gs.getD n [] = gs[n] := List.getD_eq_getElem gs [] hnG
      simp only [addScanEndsForGroups, hget]
      have hgo_pref : ∀ k ≤ gs[n].length,
          ((addScanEndsForGroupPrefix S cord' gs[n] (maxIdxs.getD n 0)
            (addCandsForGroups S cord' gs maxIdxs cand₀ n)
            (addScanEndsForGroups S cord' gs maxIdxs cand₀ (fun _ => []) n) k j).map
            fun t => t.2.2).Nodup := by
        intro k
        induction k with
        | zero => intro _; exact ih (by omega)
        | succ k ihk =>
          intro hk
          have hkG : k < gs[n].length := by omega
          simp only [addScanEndsForGroupPrefix, hkG, ↓reduceDIte]
          split_ifs with hkm
          · exact ihk (by omega)
          · refine addScanEndsForList_nodup_keys (ihk (by omega))
              (hcord_nd _ (List.getElem_mem hnG) _ (List.getElem_mem hkG)) ?_
            intro ⟨b, w, key⟩ ht hmem
            have ht' := (addScanEndsForGroupPrefix_mem_iff k (by omega)).mp ht
            rcases ht' with hprev | ⟨B', hSj', t, htk, htG, _, hw, x, hxw, hxB', _, rfl⟩
            · obtain ⟨B', hSj', gi, hgin, hgi, t, htG, _, hw, x, hxw, hxB', _, rfl⟩ :=
                (addScanEndsForGroups_mem_iff n (by omega)).mp hprev
              rw [hSj] at hSj'; cases hSj'
              have hxE : x ∈ edgeEnds (B₀.edges \ D) :=
                (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp hxB').1
              rw [bundle_endOfKey_endKey] at hmem
              have hsrc1 : src' x = gs[gi][t] := by rw [← hw]; exact (hsrc_iff x hxE w).mp hxw
              have hsrc2 : src' x = gs[n][k] := (hsrc_iff x hxE _).mp hmem
              have hdisj_gn := hgs_disj gi hgi n hnG (by omega)
              exact Finset.disjoint_left.mp hdisj_gn
                (List.mem_toFinset.mpr (List.getElem_mem htG))
                (List.mem_toFinset.mpr (by rw [← hsrc1, hsrc2]; exact List.getElem_mem hkG))
            · rw [hSj] at hSj'; cases hSj'
              have hxE : x ∈ edgeEnds (B₀.edges \ D) :=
                (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp hxB').1
              rw [bundle_endOfKey_endKey] at hmem
              have hsrc1 : src' x = gs[n][t] := by rw [← hw]; exact (hsrc_iff x hxE w).mp hxw
              have hsrc2 : src' x = gs[n][k] := (hsrc_iff x hxE _).mp hmem
              have hndn := hgs_nd gs[n] (List.getElem_mem hnG)
              have heq := hndn.getElem_inj_iff.mp (hsrc1.symm.trans hsrc2)
              omega
      exact hgo_pref gs[n].length (le_refl _)
  exact hgo_grp gs.length (le_refl _)

/-! ## 4. Full Phase 2 → Phase 3 contract (`scanValidForSlot_of_scan`) -/

theorem scanValidForSlot_of_scan {slotCap : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {j : Fin slotCap} {B₀ : BundleState}
    {cord' : ℕ → List End} {src' : End → ℕ} {gs : List (List ℕ)} {maxIdxs : List ℕ}
    (hS₀j : S₀ j = some B₀)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_disj : ∀ i (hi : i < gs.length) j' (hj' : j' < gs.length), i ≠ j' →
      Disjoint gs[i].toFinset gs[j'].toFinset)
    (hcord_nd : ∀ G ∈ gs, ∀ w ∈ G, (cord' w).Nodup)
    (hmax_lt : ∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length)
    (hsrc_iff : ∀ x ∈ edgeEnds (B₀.edges \ D), ∀ w, x ∈ cord' w ↔ src' x = w)
    (hbundle_in_group : ∀ b ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ D) src' b).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ D) b, src' x ∈ gs[gi].toFinset) :
    let S := tableDelEdges S₀ D
    let B : BundleState := { B₀ with edges := B₀.edges \ D }
    let candSet := addCandsForGroups S cord' gs maxIdxs (fun _ => ∅) gs.length
    let scanEnds := addScanEndsForGroups S cord' gs maxIdxs (fun _ => ∅) (fun _ => []) gs.length
    ScanValidForSlot B src' (candSet j) (scanEnds j) ∧
    (∀ b ∈ candSet j, ∃ t ∈ scanEnds j, t.1 = b) ∧
    (candSet j).card ≤ (scanEnds j).length := by
  intro S B candSet scanEnds
  have hSj : S j = some B := by simp [S, tableDelEdges, hS₀j, B]
  have hends_eq : ∀ b, B.ends b = survivingEnds B₀ (B₀.edges \ D) b := fun b => by
    ext x; simp only [survivingEnds, BundleState.mem_ends, Finset.mem_filter, Finset.mem_sdiff, B]; tauto
  have hcand_eq : candSet j = (exactSplitCands B₀ (B₀.edges \ D) src').toFinset :=
    scanCands_eq_exactSplitCands hS₀j hgs_nd hcord_nd hmax_lt hsrc_iff hbundle_in_group
  have hnd_keys : ((scanEnds j).map fun t => t.2.2).Nodup :=
    addScanEndsForGroups_nodup_keys hS₀j hgs_nd hgs_disj hcord_nd hsrc_iff
  have hmem_props : ∀ t ∈ scanEnds j,
      t.1 ∈ candSet j ∧ endOfKey t.2.2 ∈ B.ends t.1 ∧ src' (endOfKey t.2.2) = t.2.1 ∧
      ∃ gi, ∃ (hgi : gi < gs.length) (t' : ℕ) (ht' : t' < gs[gi].length),
        t' ≠ maxIdxs.getD gi 0 ∧ t.2.1 = gs[gi][t'] := by
    intro ⟨b, w, key⟩ ht
    obtain ⟨B', hSj', gi, _, hgi, t', ht', hne, hw, x, hxw, hxB', hbc, rfl⟩ :=
      (addScanEndsForGroups_mem_iff gs.length (le_refl _)).mp ht
    rw [hSj] at hSj'; cases hSj'
    have hbc_full : b ∈ candSet j := by
      have hsub1 := addCandsForGroupPrefix_mono S cord' gs[gi] (maxIdxs.getD gi 0)
        (addCandsForGroups S cord' gs maxIdxs (fun _ => ∅) gi) j (show t' + 1 ≤ gs[gi].length by omega)
      have hstep : addCandsForGroups S cord' gs maxIdxs (fun _ => ∅) (gi + 1) j =
          addCandsForGroupPrefix S cord' gs[gi] (maxIdxs.getD gi 0)
            (addCandsForGroups S cord' gs maxIdxs (fun _ => ∅) gi) gs[gi].length j := by
        simp only [addCandsForGroups, List.getD_eq_getElem gs [] hgi]
      have hsub2 := addCandsForGroups_mono S cord' gs maxIdxs (fun _ => ∅) j (show gi + 1 ≤ gs.length by omega)
      exact hsub2 (hstep ▸ hsub1 hbc)
    have hxE : x ∈ edgeEnds (B₀.edges \ D) :=
      (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp hxB').1
    rw [bundle_endOfKey_endKey]
    exact ⟨hbc_full, hxB', (hsrc_iff x hxE w).mp hxw, gi, hgi, t', ht', hne, hw⟩
  have hrem_spec : ∀ b ∈ candSet j, ∃ w_rem : ℕ,
      (∀ t ∈ scanEnds j, t.1 = b → t.2.1 ≠ w_rem) ∧
      (∀ x ∈ B.ends b, endKey x ∉ (scanEnds j).map (fun t => t.2.2) → src' x = w_rem) := by
    intro b hb
    have hb_ex : b ∈ B₀.vertices ∧ 2 ≤ (finalRootsOf B₀ (B₀.edges \ D) src' b).card := by
      rw [hcand_eq] at hb
      simpa [exactSplitCands] using hb
    obtain ⟨gi, hgi, hG⟩ := hbundle_in_group b hb_ex.1 hb_ex.2
    have hmlt := hmax_lt gi hgi
    set w_rem := gs[gi][maxIdxs.getD gi 0]'hmlt
    refine ⟨w_rem, ?_, ?_⟩
    · intro t ht htb
      obtain ⟨_, htB, htsrc, gi', hgi', t', ht', hne, htw⟩ := hmem_props t ht
      have htin : t.2.1 ∈ gs[gi].toFinset := by
        rw [← htsrc]
        exact hG (endOfKey t.2.2) (hends_eq b ▸ htb ▸ htB)
      have hgi_eq : gi' = gi := by
        by_contra hne_g
        exact Finset.disjoint_left.mp (hgs_disj gi' hgi' gi hgi hne_g)
          (List.mem_toFinset.mpr (htw ▸ List.getElem_mem ht')) htin
      subst hgi_eq
      rw [htw]
      intro heq
      exact hne ((hgs_nd gs[gi'] (List.getElem_mem hgi')).getElem_inj_iff.mp heq)
    · intro x hxB hxnot
      have hxs : src' x ∈ gs[gi].toFinset := hG x (hends_eq b ▸ hxB)
      obtain ⟨t, ht, htx⟩ := List.getElem_of_mem (List.mem_toFinset.mp hxs)
      by_cases htm : t = maxIdxs.getD gi 0
      · rw [← htx]; simp [w_rem, htm]
      · exfalso
        have hxE : x ∈ edgeEnds (B₀.edges \ D) :=
          (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp hxB).1
        have hxc : x ∈ cord' gs[gi][t] := (hsrc_iff x hxE _).mpr htx.symm
        have hpos : 0 < ((B.ends b).filter fun y => y ∈ cord' gs[gi][t]).card :=
          Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxB, hxc⟩⟩
        have hlt_card : ((B.ends b).filter fun y => y ∈ cord' gs[gi][t]).card < (B.ends b).card := by
          obtain ⟨w₁, hw₁, w₂, hw₂, hwne⟩ := Finset.one_lt_card.mp hb_ex.2
          have hex_ne : ∃ y ∈ B.ends b, src' y ≠ gs[gi][t] := by
            by_cases h1 : w₁ = gs[gi][t]
            · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw₂
              exact ⟨y, (hends_eq b).symm ▸ hy, by omega⟩
            · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw₁
              exact ⟨y, (hends_eq b).symm ▸ hy, h1⟩
          obtain ⟨y, hyB, hysrc⟩ := hex_ne
          have hyE : y ∈ edgeEnds (B₀.edges \ D) :=
            (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b y).mp hyB).1
          have hynot : y ∉ cord' gs[gi][t] := fun hm => hysrc ((hsrc_iff y hyE _).mp hm)
          exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨Finset.filter_subset _ _, fun heq => by
              have := Finset.mem_filter.mp (heq.symm ▸ hyB)
              exact hynot this.2⟩)
        have hbc_step : b ∈ addCandsForGroupPrefix S cord' gs[gi] (maxIdxs.getD gi 0)
            (addCandsForGroups S cord' gs maxIdxs (fun _ => ∅) gi) (t + 1) j := by
          rw [mem_addCandsForGroupPrefix_iff hSj (hcord_nd _ (List.getElem_mem hgi)) (t + 1) (by omega)]
          exact Or.inr ⟨hb_ex.1, t, by omega, ht, htm, hpos, hlt_card⟩
        have hin : (b, gs[gi][t], endKey x) ∈ scanEnds j :=
          (addScanEndsForGroups_mem_iff gs.length (le_refl _)).mpr
            ⟨B, hSj, gi, hgi, hgi, t, ht, htm, rfl, x, hxc, hxB, hbc_step, rfl⟩
        exact hxnot (List.mem_map.mpr ⟨(b, gs[gi][t], endKey x), hin, rfl⟩)
  have hvalid : ScanValidForSlot B src' (candSet j) (scanEnds j) :=
    ⟨hnd_keys, fun t ht => let h := hmem_props t ht; ⟨h.1, h.2.1, h.2.2.1⟩, hrem_spec⟩
  have hnonemp : ∀ b ∈ candSet j, ∃ t ∈ scanEnds j, t.1 = b := by
    intro b hb
    obtain ⟨w_rem, _, hrem⟩ := hrem_spec b hb
    have hb2 : 2 ≤ (finalRootsOf B₀ (B₀.edges \ D) src' b).card := by
      rw [hcand_eq] at hb; exact (by simpa [exactSplitCands] using hb : _ ∧ _).2
    obtain ⟨w₁, hw₁, w₂, hw₂, hwne⟩ := Finset.one_lt_card.mp hb2
    have hex : ∃ x ∈ B.ends b, src' x ≠ w_rem := by
      by_cases h1 : w₁ = w_rem
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw₂
        exact ⟨x, (hends_eq b).symm ▸ hx, by omega⟩
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw₁
        exact ⟨x, (hends_eq b).symm ▸ hx, h1⟩
    obtain ⟨x, hxB, hxs⟩ := hex
    have hxin : endKey x ∈ (scanEnds j).map (fun t => t.2.2) := by
      by_contra hnot; exact hxs (hrem x hxB hnot)
    obtain ⟨t, ht, htk⟩ := List.mem_map.mp hxin
    have htB := (hmem_props t ht).2.1
    rw [htk, bundle_endOfKey_endKey] at htB
    have htb : t.1 = b :=
      ((BundleState.mem_ends B t.1 x).mp htB).2.symm.trans ((BundleState.mem_ends B b x).mp hxB).2
    exact ⟨t, ht, htb⟩
  have hcard_le : (candSet j).card ≤ (scanEnds j).length := by
    have hsub : candSet j ⊆ ((scanEnds j).map Prod.fst).toFinset := by
      intro b hb
      obtain ⟨t, ht, rfl⟩ := hnonemp b hb
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩)
    calc (candSet j).card
        ≤ ((scanEnds j).map Prod.fst).toFinset.card := Finset.card_le_card hsub
      _ ≤ ((scanEnds j).map Prod.fst).length := List.toFinset_card_le _
      _ = (scanEnds j).length := List.length_map _
  exact ⟨hvalid, hnonemp, hcard_le⟩

/-! ## 5. Cardinality and logarithmic bounds -/

lemma scanValidForSlot_len_le_two_eCap {eCap : ℕ} {B : BundleState} {src' : End → ℕ}
    {candSet_j : Finset ℕ} {scan_j : List (ℕ × ℕ × ℕ)}
    (hval : ScanValidForSlot B src' candSet_j scan_j)
    (hE_lt : ∀ e ∈ B.edges, e < eCap) :
    scan_j.length ≤ 2 * eCap := by
  have hsub : (scan_j.map fun t => t.2.2).toFinset ⊆ Finset.range (2 * eCap) := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    have hE := ((BundleState.mem_ends B t.1 (endOfKey t.2.2)).mp (hval.2.1 t ht).2.1).1
    have hlt := hE_lt _ hE
    rw [Finset.mem_range]
    unfold endOfKey at hlt
    omega
  calc scan_j.length
      = (scan_j.map fun t => t.2.2).length := (List.length_map _).symm
    _ = (scan_j.map fun t => t.2.2).toFinset.card := (List.toFinset_card_of_nodup hval.1).symm
    _ ≤ (Finset.range (2 * eCap)).card := Finset.card_le_card hsub
    _ = 2 * eCap := Finset.card_range _

lemma scanValidForSlot_filter_len_le {B : BundleState} {src' : End → ℕ}
    {candSet_j : Finset ℕ} {scan_j : List (ℕ × ℕ × ℕ)}
    (hval : ScanValidForSlot B src' candSet_j scan_j) (b : ℕ) :
    (scan_j.filter fun t => t.1 == b).length ≤ (B.ends b).card := by
  set L := scan_j.filter fun t => t.1 == b
  have hnd : (L.map fun t => t.2.2).Nodup := by
    have hsub : L.Sublist scan_j := List.filter_sublist
    exact hval.1.sublist (hsub.map _)
  have hsub : (L.map fun t => t.2.2).toFinset ⊆ (B.ends b).image endKey := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    obtain ⟨ht_in, htb⟩ := List.mem_filter.mp ht
    have htb' : t.1 = b := by simpa using htb
    refine Finset.mem_image.mpr ⟨endOfKey t.2.2, ?_, bundle_endKey_endOfKey t.2.2⟩
    rw [← htb']; exact (hval.2.1 t ht_in).2.1
  calc L.length
      = (L.map fun t => t.2.2).length := (List.length_map _).symm
    _ = (L.map fun t => t.2.2).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ ((B.ends b).image endKey).card := Finset.card_le_card hsub
    _ ≤ (B.ends b).card := Finset.card_image_le

lemma scanValidForSlot_len_eq_sum_filters {B : BundleState} {src' : End → ℕ}
    {candSet_j : Finset ℕ} {scan_j : List (ℕ × ℕ × ℕ)}
    (hval : ScanValidForSlot B src' candSet_j scan_j) :
    scan_j.length = (((candSet_j.sort (· ≤ ·)).map fun b =>
      (scan_j.filter fun t => t.1 == b).length).sum) := by
  have hgo : ∀ (L : List (ℕ × ℕ × ℕ)), (∀ t ∈ L, t.1 ∈ candSet_j) →
      L.length = (((candSet_j.sort (· ≤ ·)).map fun b =>
        (L.filter fun t => t.1 == b).length).sum) := by
    intro L
    induction L with
    | nil =>
      intro _; simp
    | cons a tl ih =>
      intro ha
      have h1 := ha a List.mem_cons_self
      have h2 := ih fun t ht => ha t (List.mem_cons_of_mem _ ht)
      simp only [List.length_cons, List.filter_cons]
      have hsplit : ∀ (cs : List ℕ), cs.Nodup →
          (cs.map fun b => (if (a.1 == b) = true then a :: tl.filter (fun t => t.1 == b)
            else tl.filter (fun t => t.1 == b)).length).sum =
          (if a.1 ∈ cs then 1 else 0) +
            (cs.map fun b => (tl.filter fun t => t.1 == b).length).sum := by
        intro cs
        induction cs with
        | nil => intro _; simp
        | cons c rest ihr =>
          intro hnd
          obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
          simp only [List.map_cons, List.sum_cons, List.mem_cons]
          rw [ihr hnd']
          by_cases hac : a.1 = c
          · subst hac; simp [hnot]; omega
          · simp [hac]; omega
      rw [hsplit (candSet_j.sort (· ≤ ·)) (Finset.sort_nodup _ _),
        ite_eq_left ((Finset.mem_sort (· ≤ ·)).mpr h1)]
      omega
  exact hgo scan_j fun t ht => (hval.2.1 t ht).1

lemma scanValidForSlot_len_le_candEndsSum {B : BundleState} {src' : End → ℕ}
    {candSet_j : Finset ℕ} {scan_j : List (ℕ × ℕ × ℕ)}
    (hval : ScanValidForSlot B src' candSet_j scan_j) :
    scan_j.length ≤ (((candSet_j.sort (· ≤ ·)).map fun b => (B.ends b).card).sum) := by
  rw [scanValidForSlot_len_eq_sum_filters hval]
  have hsum_le : ∀ (cs : List ℕ),
      (cs.map fun b => (scan_j.filter fun t => t.1 == b).length).sum ≤
        (cs.map fun b => (B.ends b).card).sum := by
    intro cs
    induction cs with
    | nil => simp
    | cons b rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have h1 := scanValidForSlot_filter_len_le hval b
      omega
  exact hsum_le _

lemma nat_log_two_mul_le_ordStoreLog {eCap m : ℕ} (hm : m ≤ 2 * eCap) :
    Nat.log 2 (2 * m + 1) + 1 ≤ ordStoreLog eCap + 2 := by
  unfold ordStoreLog
  have h1 : 2 * m + 1 ≤ (eCap + 2) * 2 * 2 := by omega
  have h2 : Nat.log 2 (2 * m + 1) ≤ Nat.log 2 ((eCap + 2) * 2 * 2) := Nat.log_mono_right h1
  have h3 : Nat.log 2 ((eCap + 2) * 2 * 2) = Nat.log 2 (eCap + 2) + 2 := by
    rw [Nat.log_mul_base (by decide) (by omega), Nat.log_mul_base (by decide) (by omega)]
  omega

lemma nat_log_le_ordStoreLog {eCap m : ℕ} (hm : m ≤ 2 * eCap) :
    Nat.log 2 (m + 1) + 1 ≤ ordStoreLog eCap + 2 := by
  have h1 : Nat.log 2 (m + 1) ≤ Nat.log 2 (2 * m + 1) := Nat.log_mono_right (by omega)
  have h2 := nat_log_two_mul_le_ordStoreLog hm
  omega

end

end MinCostFlow.SparseCore.Program
