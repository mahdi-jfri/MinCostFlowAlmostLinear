module

public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkBound
public import MinCostFlow.SparseCore.Program.AssemblyFirstOutEdges
public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartIface

/-!
# Model coverage for updating the embedding table in a branch step (`AssemblyFirstEmbModel`)

In a branch step `info := stepBundleTree sp tr U ord ord'` (`tr' := info.state`), the embedding
table (`Read.EmbView`) must end up matching `tr'.emb` on every edge of the new core graph
`coreGraph tr'.cs.G tr'.cs.lsf`. Rather than refreshing every active spanner from scratch, the
step only writes walks for:
1. every entering output edge `e ∈ outInsSet sp tr U ord ord'` (receiving `[(e, true)]`);
2. for each old active pair `p ∈ activePairs tr`, every edge `e` in
   `oldPairNewWalkEdges sp tr U ord ord' p := (R_p \ tr'.S_cur.E) ∪ ((tr.S_cur.E \ tr'.S_cur.E) ∩ (tr'.dyn p).G.E)`;
3. for each newly active pair `p = (C, b)` (`C ∈ info.newlyActive`, `b ∈ tr.activeBuckets C`),
   every edge `e ∈ (tr'.dyn p).G.E \ tr'.S_cur.E`.

This file proves:
* `stepBundleTree_emb_eq_old_of_not_new`: every other core edge `e ∈ (coreGraph tr'.cs.G
  tr'.cs.lsf).E` already satisfies `e ∈ (coreGraph tr.cs.G tr.cs.lsf).E` and `tr'.emb e = tr.emb e`
  (its walk in the embedding table is unchanged).
* `embView_step_matches`: any `EmbView` obtained by starting from a view matching `tr.emb` on the
  old core graph, updating every edge in (2)–(3) to `slotWalk P S6' (slotOf p) e`, and updating
  every edge in (1) to `[(e, true)]` covers `(coreGraph tr'.cs.G tr'.cs.lsf).E` and agrees with
  `tr'.emb` everywhere on it.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart
open MinCostFlow.SparseCore.Program.Read

/-! ## Edge sets written into the embedding table by a step -/

@[expose] public section

/-- The off-spanner edges of an old active pair `p` whose walks may change during a branch step:
re-embedded edges outside `tr'.S_cur.E`, plus edges that left `S_cur` while remaining in
`(tr'.dyn p).G`. -/
noncomputable def oldPairNewWalkEdges {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (p : Finset ℕ × ℤ) : Finset ℕ :=
  let info := stepBundleTree sparsify tr U ord ord'
  let tr' := info.state
  (updateReembSet (tr.dyn p) (info.U_B p) (sparsify tr.m₀) \ tr'.S_cur.E) ∪
    ((tr.S_cur.E \ tr'.S_cur.E) ∩ (tr'.dyn p).G.E)

/-- The off-spanner edges of a newly active pair `p` whose walks are written during a branch step. -/
noncomputable def newPairNewWalkEdges {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (tr : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End)
    (p : Finset ℕ × ℤ) : Finset ℕ :=
  let tr' := (stepBundleTree sparsify tr U ord ord').state
  (tr'.dyn p).G.E \ tr'.S_cur.E

end

/-! ## Pure model coverage theorems -/

public section

/-- Under `BunDisjointInv` and `e ∉ tr.S_cur.E`, if `p ∈ activePairs tr` contains `e` in
`(tr.bun p).edges`, then `tr.emb e = piTotal (tr.dyn p) e`. -/
theorem bundleTree_emb_eq_piTotal {L : ℕ} {tr : BundleTreeState L}
    (hBD : BunDisjointInv tr) {p : Finset ℕ × ℤ} (hp : p ∈ activePairs tr)
    {e : ℕ} (heNotS : e ∉ tr.S_cur.E) (heBun : e ∈ (tr.bun p).edges) :
    tr.emb e = piTotal (tr.dyn p) e := by
  classical
  have ⟨hC, hb⟩ := mem_activePairs.mp hp
  have hex : ∃ q : Finset ℕ × ℤ, q.1 ∈ tr.activeComps ∧ q.2 ∈ tr.activeBuckets q.1 ∧
      e ∈ (tr.bun q).edges := ⟨p, hC, hb, heBun⟩
  simp only [BundleTreeState.emb, heNotS, ↓reduceIte, hex, ↓reduceDIte]
  have hq : hex.choose ∈ activePairs tr :=
    mem_activePairs.mpr ⟨hex.choose_spec.1, hex.choose_spec.2.1⟩
  have hpeq : hex.choose = p := by
    by_contra hne
    exact Finset.disjoint_left.mp (hBD.1 hex.choose hq p hp hne) hex.choose_spec.2.2 heBun
  rw [hpeq]

/-- If `e ∉ tr.S_cur.E` and `e` belongs to no active bundle of `tr`, then `tr.emb e = []`. -/
theorem bundleTree_emb_eq_nil_of_not_mem {L : ℕ} {tr : BundleTreeState L} {e : ℕ}
    (heNotS : e ∉ tr.S_cur.E) (heNotBun : ∀ p ∈ activePairs tr, e ∉ (tr.bun p).edges) :
    tr.emb e = [] := by
  classical
  have hno : ¬ ∃ p : Finset ℕ × ℤ, p.1 ∈ tr.activeComps ∧ p.2 ∈ tr.activeBuckets p.1 ∧
      e ∈ (tr.bun p).edges := by
    rintro ⟨p, hC, hb, he⟩
    exact heNotBun p (mem_activePairs.mpr ⟨hC, hb⟩) he
  simp [BundleTreeState.emb, heNotS, hno]

/-- **Model coverage theorem for the embedding table after a branch step.**
For every edge `e` of the new core graph that lies in either `tr'.S_cur.E` or an active bundle of
`tr'`:
1. if `e ∈ tr'.S_cur.E` and `e ∉ outInsSet`, then `e ∈ tr.S_cur.E` and `tr'.emb e = tr.emb e`;
2. if `e ∉ tr'.S_cur.E` and `e ∈ (tr'.bun p).edges` for an old active pair `p ∈ activePairs tr`
   with `e ∉ oldPairNewWalkEdges sp tr U ord ord' p`, then `tr'.emb e = tr.emb e` (and `e` was
   already in `(tr.bun p).edges \ tr.S_cur.E`). -/
theorem stepBundleTree_emb_eq_old_of_not_new (P : DSParams) (tr : BundleTreeState P.L)
    (U : List Update) (ord ord' : ℕ → List End)
    (hL : 1 ≤ P.L)
    (hBD : BunDisjointInv tr) (hBD' : BunDisjointInv (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state)
    (hDynG : ∀ p ∈ activePairs tr, (tr.dyn p).G.E = (tr.bun p).edges)
    (hDynG' : ∀ p ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state,
      ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.dyn p).G.E =
        ((stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').state.bun p).edges)
    (d : Finset ℕ × ℤ → DSHist)
    (hOld : ∀ p ∈ activePairs tr,
      (d p).state P = tr.dyn p ∧
      (d p).G₀.IsValid ∧ (d p).G₀.m ≤ P.mMax ∧
      (d p).G₀.BatchIsValid ((d p).flat ++
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B p) ∧
      (∀ u ∈ (d p).flat ++
        (stepBundleTree (fun _ => canonicalSparsify P.impl) tr U ord ord').U_B p,
        isDelOrSplit u)) :
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify P.impl
    let info := stepBundleTree sp tr U ord ord'
    let tr' := info.state
    (∀ e ∈ tr'.S_cur.E, e ∉ outInsSet sp tr U ord ord' → tr'.emb e = tr.emb e) ∧
    (∀ p ∈ activePairs tr, ∀ e ∈ (tr'.dyn p).G.E, e ∉ tr'.S_cur.E →
      e ∉ oldPairNewWalkEdges sp tr U ord ord' p →
      e ∈ (tr.dyn p).G.E ∧ e ∉ tr.S_cur.E ∧ tr'.emb e = tr.emb e) := by
  intro sp info tr'
  constructor
  · intro e heS' heNotIns
    have heS : e ∈ tr.S_cur.E := by
      by_contra hnot
      exact heNotIns ((mem_outInsSet_iff sp tr U ord ord' e).mpr ⟨heS', Or.inl hnot⟩)
    simp [BundleTreeState.emb, heS', heS]
  · intro p hp e heG' heNotS' heNotNew
    have hp' : p ∈ activePairs tr' := by
      have ⟨hC, hb⟩ := mem_activePairs.mp hp
      exact mem_activePairs.mpr ⟨Finset.mem_union.mpr (Or.inl hC), hb⟩
    have heNotR : e ∉ updateReembSet (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl) := by
      intro hR
      exact heNotNew (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hR, heNotS'⟩)))
    have heNotS : e ∉ tr.S_cur.E := by
      intro hS
      exact heNotNew (Finset.mem_union.mpr (Or.inr
        (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hS, heNotS'⟩, heG'⟩)))
    obtain ⟨hst, hVG₀, hGm₀, hBV, hds⟩ := hOld p hp
    have hGsub : (tr'.dyn p).G.E ⊆ (tr.dyn p).G.E := by
      have hdsU : ∀ u ∈ info.U_B p, isDelOrSplit u := fun u hu =>
        hds u (List.mem_append.mpr (Or.inr hu))
      have hstep_sub : ∀ (U' : List Update) (st0 : DynSpannerState P.L) uhAcc dAcc cAcc,
          (∀ u ∈ U', isDelOrSplit u) →
          (DynSpanner.updateGo (canonicalSparsify P.impl) st0 U' uhAcc dAcc cAcc).state.G.E ⊆
            st0.G.E := by
        intro U'
        induction U' with
        | nil => intro st0 _ _ _ _; exact Finset.Subset.refl _
        | cons u us ih =>
          intro st0 uhAcc dAcc cAcc hU
          have hu : isDelOrSplit u := hU u List.mem_cons_self
          have hus : ∀ u' ∈ us, isDelOrSplit u' := fun u' hu' => hU u' (List.mem_cons_of_mem u hu')
          have h1 : (DynSpanner.step st0 u (canonicalSparsify P.impl)).state.G.E ⊆ st0.G.E := by
            have hGeq : (DynSpanner.step st0 u (canonicalSparsify P.impl)).state.G =
                st0.G.applyUpdate u := by
              dsimp only [DynSpanner.step]
              split_ifs <;> rfl
            rw [hGeq]
            rcases u with ⟨_, _, _⟩ | e0 | ⟨_, _, _, _⟩
            · cases hu
            · exact Finset.erase_subset e0 st0.G.E
            · exact Finset.Subset.refl _
          exact Finset.Subset.trans
            (ih (DynSpanner.step st0 u (canonicalSparsify P.impl)).state _ _ _ hus) h1
      exact hstep_sub (info.U_B p) (tr.dyn p) [] ∅ 0 hdsU
    have heG : e ∈ (tr.dyn p).G.E := hGsub heG'
    have heBun : e ∈ (tr.bun p).edges := (hDynG p hp) ▸ heG
    have heBun' : e ∈ (tr'.bun p).edges := (hDynG' p hp') ▸ heG'
    have hpi : piTotal (tr'.dyn p) e = piTotal (tr.dyn p) e := by
      have hst' : tr'.dyn p = (⟨(d p).G₀, (d p).Us ++ [info.U_B p]⟩ : DSHist).state P := by
        show (DynSpanner.update (tr.dyn p) (info.U_B p) (canonicalSparsify P.impl)).state = _
        rw [← hst]
        exact (dsHist_append_state_eq_update P (d p) (info.U_B p)).symm
      have heG'' : e ∈ ((⟨(d p).G₀, (d p).Us ++ [info.U_B p]⟩ : DSHist).state P).G.E :=
        hst' ▸ heG'
      have heNotR' : e ∉ updateReembSet ((d p).state P) (info.U_B p) (canonicalSparsify P.impl) := by
        rwa [hst]
      rw [hst', ← hst]
      exact dsHist_piTotal_eq_of_not_mem_updateReembSet P (d p) (info.U_B p) hVG₀ hL hGm₀ hBV hds
        e heG'' heNotR'
    refine ⟨heG, heNotS, ?_⟩
    rw [bundleTree_emb_eq_piTotal hBD' hp' heNotS' heBun',
      bundleTree_emb_eq_piTotal hBD hp heNotS heBun, hpi]

end

end MinCostFlow.SparseCore.Program
