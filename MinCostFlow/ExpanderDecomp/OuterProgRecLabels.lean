module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OuterDecomp
public import MinCostFlow.ExpanderDecomp.OuterCost
public import MinCostFlow.ExpanderDecomp.OuterProgGame
public import MinCostFlow.ExpanderDecomp.OuterProgPortOps
public import MinCostFlow.ExpanderDecomp.ProgPortGraph
public import MinCostFlow.ExpanderDecomp.ProgRemoveFake
public import MinCostFlow.ExpanderDecomp.ProgCompLabels
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Shared Building Blocks for the Recursive Outer Decomposition Procedure (`OuterProgRecBase`)

Provides the subprocedure index table, label-matching invariant, pure `OuterRecSpec` combination
lemmas (parameterized by an arbitrary `RemoveFake` output `R` satisfying `removeFakeContract`),
`portGraph` / `portOwnersList` bridge lemmas, and verified helper statements (`writeCompLabelsStmt`,
`writeConstLabelStmt`, `rfWorkBound`) used by `OuterProgRec.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 1. Subprocedure Indices and Label-Matching Invariant -/

/-- Procedure index table for `outerDecompRecProc`. -/
structure OuterRecIndices where
  /-- Index of `outerDecompRecProc` itself (for recursive calls). -/
  bSelf : ℕ
  /-- Index of `compLabelsInEntry` (`ProgCompLabels.lean`). -/
  bComp : ℕ
  /-- Index of `portGraphEntry` (`ProgPortGraph.lean`). -/
  bPort : ℕ
  /-- Index of `outerGameProc` (`OuterProgGame.lean`). -/
  bGame : ℕ
  /-- Index of `outerRoundPortCutProc` (`OuterProgPortOps.lean`). -/
  bRound : ℕ
  /-- Index of `restrictProc` (`OuterProgSubgraphOps.lean`). -/
  bRestrict : ℕ
  /-- Index of `stripIsolatedProc` (`OuterProgSubgraphOps.lean`). -/
  bStripIso : ℕ
  /-- Index of `outerContractEdgesProc` (`OuterProgPortOps.lean`). -/
  bContract : ℕ
  /-- Index of `removeFakeEntry` (`ProgRemoveFake.lean`). -/
  bRF : ℕ
  /-- Index of `setDiffProc` (`OuterProgSubgraphOps.lean`). -/
  bSetDiff : ℕ

/-- The label array at `labelsAddr` encodes the finalized partition `parts` of `X` using label
values strictly inside `[nlLo, nlHi)`:
* every `v ∈ X` receives a label in `[nlLo, nlHi)`;
* every part `P ∈ parts` is nonempty, contained in `X`, and monochromatic in `[nlLo, nlHi)`;
* any two vertices `u, v ∈ X` with the same label belong to a common part `P ∈ parts`. -/
def LabelsMatchParts (mem : ℕ → ℕ) (labelsAddr : ℕ) (X : Finset ℕ)
    (parts : List (Finset ℕ)) (nlLo nlHi : ℕ) : Prop :=
  nlLo ≤ nlHi ∧
  (∀ v ∈ X, nlLo ≤ mem (labelsAddr + v) ∧ mem (labelsAddr + v) < nlHi) ∧
  (∀ P ∈ parts, P.Nonempty ∧ P ⊆ X ∧
    ∃ lbl, nlLo ≤ lbl ∧ lbl < nlHi ∧ ∀ v ∈ P, mem (labelsAddr + v) = lbl) ∧
  (∀ u ∈ X, ∀ v ∈ X, mem (labelsAddr + u) = mem (labelsAddr + v) →
    ∃ P ∈ parts, u ∈ P ∧ v ∈ P)

/-! ## 2. Computable Workspace Upper Bound for `RemoveFake` -/

/-- Simple computable upper bound on `removeFakeWorkSpace k e mF (rfHParam e mF 1 Λ)` valid
whenever `e ≤ M`, `mF ≤ e`, and `2 * M < 2 ^ LParam M`. -/
def rfWorkBound (k e mF Λ L : ℕ) : ℕ :=
  16 * k + 7 * e + 30 * mF + 224 * Λ * L + 20

/-- Per-node zero-heap space envelope (words) for `outerDecompRecProc` parameterized by `cfg`. -/
def outerRecNodeSpace (cfg : ParamConfig) (C_sp M r k e gameLoopCost : ℕ) : ℕ :=
  10 * k + 80 * e + portGraphHeapSpace e +
    outerGameSpace C_sp M r e gameLoopCost +
    224 * Lambda cfg M r * LParam M + 200

/-! ## 3. Small Helper Statements for `outerDecompRecProc` -/

/-- Copy `k` local component labels from `tmpLblAddr` (`r10`) shifted by `nl = mem[nextLblAddr]`
into `labelsAddr[verts[i]]` and advance `mem[nextLblAddr]` by `k`.
Reads `r0=k, r1=vertsAddr, r6=labelsAddr, r7=nextLblAddr, r10=tmpLblAddr`; uses scratch
`r12, r13, r14, r15`. -/
def writeCompLabelsStmt : Stmt :=
  .assign 12 (.load (.reg 7)) ;;
  forRange 13 (.const 0) (.reg 0)
    (.assign 14 (.load (.bin .add (.reg 1) (.reg 13))) ;;
     .assign 15 (.load (.bin .add (.reg 10) (.reg 13))) ;;
     .store (.bin .add (.reg 6) (.reg 14)) (.bin .add (.reg 12) (.reg 15))) ;;
  .store (.reg 7) (.bin .add (.reg 12) (.reg 0))

/-- Paint all `kR` vertices in `rAddr` (`r24`) with the single fresh label `nl = mem[nextLblAddr]`
in `labelsAddr` (`r6`), and increment `mem[nextLblAddr]` by `1`.
Reads `r6=labelsAddr, r7=nextLblAddr, r24=rAddr, r28=kR`; uses scratch `r30, r31, r32`. -/
def writeConstLabelStmt : Stmt :=
  .assign 30 (.load (.reg 7)) ;;
  forRange 31 (.const 0) (.reg 28)
    (.assign 32 (.load (.bin .add (.reg 24) (.reg 31))) ;;
     .store (.bin .add (.reg 6) (.reg 32)) (.reg 30)) ;;
  .store (.reg 7) (.bin .add (.reg 30) (.const 1))

/-- Compute `rfWorkBound k e mF Λ L` into register `r31` from
`r0=k, r2=e, r27=mF, r22=Λ, r23=L`, using scratch `r32`. -/
def computeRfWorkBoundStmt : Stmt :=
  .assign 31 (.bin .mul (.const 16) (.reg 0)) ;;
  .assign 31 (.bin .add (.reg 31) (.bin .mul (.const 7) (.reg 2))) ;;
  .assign 31 (.bin .add (.reg 31) (.bin .mul (.const 30) (.reg 27))) ;;
  .assign 32 (.bin .mul (.const 224) (.reg 22)) ;;
  .assign 32 (.bin .mul (.reg 32) (.reg 23)) ;;
  .assign 31 (.bin .add (.reg 31) (.bin .add (.reg 32) (.const 20)))

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander MinCostFlow.ExplicitExpander

/-! ## 4. `NoRand` Proofs -/

lemma writeCompLabelsStmt_noRand : writeCompLabelsStmt.NoRand := by
  simp [writeCompLabelsStmt, forRange, forUp, Stmt.NoRand]

lemma writeConstLabelStmt_noRand : writeConstLabelStmt.NoRand := by
  simp [writeConstLabelStmt, forRange, forUp, Stmt.NoRand]

lemma computeRfWorkBoundStmt_noRand : computeRfWorkBoundStmt.NoRand := by
  simp [computeRfWorkBoundStmt, Stmt.NoRand]

/-! ## 5. Cloud Expander and Port-Owner Bridge Lemmas -/

/-- `1 / (ParamConfig.default.a₀ : ℝ) ≤ cloudAlpha` (`1 / 12 ≤ 1 / 12`). -/
lemma inv_default_a0_le_cloudAlpha :
    (1 : ℝ) / (ParamConfig.default.a₀ : ℝ) ≤ cloudAlpha := by
  unfold ParamConfig.default cloudAlpha alpha0
  norm_num

/-- `portGraph cloud G X = portGraph explicitGraph G X`. -/
lemma portGraph_cloud_eq_explicitGraph (G : Graph) (X : Finset ℕ) :
    portGraph cloud G X = portGraph explicitGraph G X := by
  unfold portGraph
  congr 1; congr 1
  unfold allCloudEdges
  apply List.flatMap_congr
  intro v _
  unfold cloudEdgesFor
  dsimp only
  split_ifs with h
  · rw [cloud_eq_explicitGraph h]
  · rfl

/-- Entry `p` of `portOwnersList (G.inside X)` equals `portOwner G X p` for all `p < 2 * e`. -/
lemma portOwnersList_getElem_eq_portOwner (G : Graph) (X : Finset ℕ)
    {p : ℕ} (hp : p < (portOwnersList (G.inside X)).length) :
    (portOwnersList (G.inside X))[p] = portOwner G X p := by
  have hlen := portOwnersList_length (G.inside X)
  have hgen : ∀ (es : List (ℕ × ℕ)) (p : ℕ) (hp : p < (portOwnersList es).length),
      (portOwnersList es)[p] =
        let ed := es.getD (p / 2) (0, 0)
        if p % 2 = 0 then ed.1 else ed.2 := by
    intro es
    induction es with
    | nil => intro p hp; simp [portOwnersList] at hp
    | cons hd tl ih =>
      intro p hp
      rcases p with _ | _ | p'
      · simp [portOwnersList]
      · simp [portOwnersList]
      · have hlen' : p' < (portOwnersList tl).length := by
          simp only [portOwnersList, List.flatMap_cons, List.length_append, List.length_cons,
            List.length_nil] at hp ⊢
          omega
        have hstep : (portOwnersList (hd :: tl))[p' + 2] = (portOwnersList tl)[p'] := by
          simp [portOwnersList]
        rw [hstep, ih p' hlen']
        have hdiv : (p' + 2) / 2 = p' / 2 + 1 := by omega
        have hmod : (p' + 2) % 2 = p' % 2 := by omega
        simp [hdiv, hmod]
  exact hgen (G.inside X) p hp

/-- If `∀ p < 2 * e, mem (ownerAddr + p) = portOwner G X p`, then
`ListAt mem ownerAddr (portOwnersList (G.inside X))`. -/
lemma listAt_portOwnersList_of_portOwner {mem : ℕ → ℕ} {ownerAddr : ℕ} {G : Graph} {X : Finset ℕ}
    (h : ∀ p < 2 * (G.inside X).length, mem (ownerAddr + p) = portOwner G X p) :
    ListAt mem ownerAddr (portOwnersList (G.inside X)) := by
  intro i hi
  have hi2 : i < 2 * (G.inside X).length := by rw [← portOwnersList_length]; exact hi
  rw [portOwnersList_getElem_eq_portOwner G X hi]
  exact h i hi2

/-- Every vertex in `portOwnersList (G.inside X)` belongs to `X`. -/
lemma mem_portOwnersList_inside {G : Graph} {X : Finset ℕ} {v : ℕ}
    (hv : v ∈ portOwnersList (G.inside X)) : v ∈ X := by
  rcases List.mem_flatMap.mp hv with ⟨ed, hed, hv_ed⟩
  have h12 := (mem_inside_iff.mp hed).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_ed
  rcases hv_ed with rfl | rfl
  · exact h12.1
  · exact h12.2

/-- Strict sortedness (`verts.Pairwise (· < ·)`) is preserved by `List.filter`. -/
lemma pairwise_lt_filter {l : List ℕ} (h : l.Pairwise (· < ·)) (p : ℕ → Bool) :
    (l.filter p).Pairwise (· < ·) :=
  h.filter p

/-- `List.range n` is strictly increasing. -/
lemma pairwise_lt_range (n : ℕ) : (List.range n).Pairwise (· < ·) :=
  List.pairwise_lt_range

/-! ## 6. `LabelsMatchParts` Composition and `IsExpanderDecomposition` Bridge -/

lemma labelsMatchParts_congr {mem₁ mem₂ : ℕ → ℕ} {labelsAddr : ℕ} {X : Finset ℕ}
    {parts : List (Finset ℕ)} {nlLo nlHi : ℕ}
    (h : LabelsMatchParts mem₁ labelsAddr X parts nlLo nlHi)
    (heq : ∀ v ∈ X, mem₂ (labelsAddr + v) = mem₁ (labelsAddr + v)) :
    LabelsMatchParts mem₂ labelsAddr X parts nlLo nlHi := by
  rcases h with ⟨hle, hrange, hmono, hsame⟩
  refine ⟨hle,
    fun v hv => by rw [heq v hv]; exact hrange v hv,
    fun P hP => by
      rcases hmono P hP with ⟨hne, hsub, lbl, hlo, hhi, hconst⟩
      exact ⟨hne, hsub, lbl, hlo, hhi, fun v hv => by rw [heq v (hsub hv)]; exact hconst v hv⟩,
    fun u hu v hv huv => by
      rw [heq u hu, heq v hv] at huv; exact hsame u hu v hv huv⟩

lemma labelsMatchParts_empty (mem : ℕ → ℕ) (labelsAddr nl : ℕ) :
    LabelsMatchParts mem labelsAddr ∅ [] nl nl :=
  ⟨le_rfl, fun _ hv => by simp at hv, fun _ hP => by simp at hP, fun _ hu => by simp at hu⟩

lemma labelsMatchParts_singleton_list {mem : ℕ → ℕ} {labelsAddr nl₀ : ℕ} {iso : List ℕ}
    (hmem : ∀ u ∈ iso, mem (labelsAddr + u) = nl₀ + iso.idxOf u) :
    LabelsMatchParts mem labelsAddr iso.toFinset (iso.map fun v => ({v} : Finset ℕ))
      nl₀ (nl₀ + iso.length) := by
  refine ⟨Nat.le_add_right _ _, ?_, ?_, ?_⟩
  · intro v hv
    have hvL : v ∈ iso := List.mem_toFinset.mp hv
    rw [hmem v hvL]
    have hlt := List.idxOf_lt_length_of_mem hvL
    omega
  · intro P hP
    rcases List.mem_map.mp hP with ⟨v, hvL, rfl⟩
    refine ⟨Finset.singleton_nonempty v, Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hvL),
      nl₀ + iso.idxOf v, Nat.le_add_right _ _,
      by have := List.idxOf_lt_length_of_mem hvL; omega,
      fun u hu => by rw [Finset.mem_singleton.mp hu]; exact hmem v hvL⟩
  · intro u hu v hv huv
    have huL : u ∈ iso := List.mem_toFinset.mp hu
    have hvL : v ∈ iso := List.mem_toFinset.mp hv
    rw [hmem u huL, hmem v hvL] at huv
    have hidx : iso.idxOf u = iso.idxOf v := by omega
    have hu_eq : u = v := by
      have h1 : iso[iso.idxOf u]'(List.idxOf_lt_length_of_mem huL) = u :=
        List.getElem_idxOf (List.idxOf_lt_length_of_mem huL)
      have h2 : iso[iso.idxOf v]'(List.idxOf_lt_length_of_mem hvL) = v :=
        List.getElem_idxOf (List.idxOf_lt_length_of_mem hvL)
      rw [← h1, ← h2]; simp [hidx]
    subst hu_eq
    exact ⟨{u}, List.mem_map.mpr ⟨u, huL, rfl⟩, Finset.mem_singleton_self u, Finset.mem_singleton_self u⟩

lemma labelsMatchParts_const {mem : ℕ → ℕ} {labelsAddr nl : ℕ} {R : Finset ℕ}
    (hRne : R.Nonempty) (hmem : ∀ u ∈ R, mem (labelsAddr + u) = nl) :
    LabelsMatchParts mem labelsAddr R [R] nl (nl + 1) := by
  refine ⟨by omega,
    fun v hv => by rw [hmem v hv]; omega,
    fun P hP => by
      rw [List.mem_singleton.mp hP]
      exact ⟨hRne, Finset.Subset.refl R, nl, le_rfl, by omega, hmem⟩,
    fun u hu v hv _ => ⟨R, List.mem_singleton_self R, hu, hv⟩⟩

lemma labelsMatchParts_union {mem : ℕ → ℕ} {labelsAddr : ℕ} {X₁ X₂ : Finset ℕ}
    {p₁ p₂ : List (Finset ℕ)} {nl₀ nl₁ nl₂ : ℕ}
    (_hdisj : Disjoint X₁ X₂)
    (h₁ : LabelsMatchParts mem labelsAddr X₁ p₁ nl₀ nl₁)
    (h₂ : LabelsMatchParts mem labelsAddr X₂ p₂ nl₁ nl₂) :
    LabelsMatchParts mem labelsAddr (X₁ ∪ X₂) (p₁ ++ p₂) nl₀ nl₂ := by
  rcases h₁ with ⟨h01, hr1, hm1, hs1⟩
  rcases h₂ with ⟨h12, hr2, hm2, hs2⟩
  refine ⟨le_trans h01 h12, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv1 | hv2
    · have := hr1 v hv1; omega
    · have := hr2 v hv2; omega
  · intro P hP
    rcases List.mem_append.mp hP with hP1 | hP2
    · rcases hm1 P hP1 with ⟨hne, hsub, lbl, hlo, hhi, hconst⟩
      exact ⟨hne, hsub.trans Finset.subset_union_left, lbl, hlo, by omega, hconst⟩
    · rcases hm2 P hP2 with ⟨hne, hsub, lbl, hlo, hhi, hconst⟩
      exact ⟨hne, hsub.trans Finset.subset_union_right, lbl, by omega, hhi, hconst⟩
  · intro u hu v hv huv
    rcases Finset.mem_union.mp hu with hu1 | hu2 <;> rcases Finset.mem_union.mp hv with hv1 | hv2
    · rcases hs1 u hu1 v hv1 huv with ⟨P, hP, huP, hvP⟩
      exact ⟨P, List.mem_append_left p₂ hP, huP, hvP⟩
    · have h1 := hr1 u hu1; have h2 := hr2 v hv2; omega
    · have h1 := hr2 u hu2; have h2 := hr1 v hv1; omega
    · rcases hs2 u hu2 v hv2 huv with ⟨P, hP, huP, hvP⟩
      exact ⟨P, List.mem_append_right p₁ hP, huP, hvP⟩

/-- From `compLabelsInContract`'s `Cited.partsOf` equality + shifted labels in `labelsAddr`,
`LabelsMatchParts` holds for `H.componentsOf` on `[nl₀, nl₀ + H.verts.length)`. -/
lemma labelsMatchParts_componentsOf {mem : ℕ → ℕ} {labelsAddr nl₀ : ℕ}
    {G : Graph} {H : CompactSubgraph} {localLbl : List ℕ}
    (hRep : H.Represents G H.vertSet)
    (hlen : localLbl.length = H.verts.length)
    (hparts : Cited.partsOf (relabelGraph H.verts ((Graph.mk 0 H.edges).inside H.vertSet)) localLbl =
      Cited.partsOf (relabelGraph H.verts ((Graph.mk 0 H.edges).inside H.vertSet))
        (compLabels (relabelGraph H.verts ((Graph.mk 0 H.edges).inside H.vertSet))))
    (hval : ∀ i (hi : i < H.verts.length),
      mem (labelsAddr + H.verts[i]) = nl₀ + localLbl[i]'(hlen ▸ hi))
    (hlt : ∀ i (hi : i < H.verts.length), localLbl[i]'(hlen ▸ hi) < H.verts.length) :
    LabelsMatchParts mem labelsAddr H.vertSet H.componentsOf nl₀ (nl₀ + H.verts.length) := by
  have hnd : H.verts.Nodup := hRep.1
  have hins_eq : (Graph.mk 0 H.edges).inside H.vertSet = H.edges := by
    unfold Graph.inside
    exact List.filter_eq_self.mpr fun ed hed => by
      rw [hRep.2.2] at hed
      have h12 := (mem_inside_iff.mp hed).2
      simp [h12.1, h12.2]
  have hG_eq : relabelGraph H.verts ((Graph.mk 0 H.edges).inside H.vertSet) = H.localGraph := by
    rw [hins_eq]; rfl
  rw [hG_eq] at hparts
  have hgetD_loc : ∀ i (hi : i < H.verts.length), localLbl.getD i 0 = localLbl[i]'(hlen ▸ hi) := by
    intro i hi; simp [List.getD_eq_getElem?_getD, hlen ▸ hi]
  have hiff : ∀ i (hi : i < H.verts.length), ∀ j (hj : j < H.verts.length),
      mem (labelsAddr + H.verts[i]) = mem (labelsAddr + H.verts[j]) ↔
        (compLabels H.localGraph).getD i 0 = (compLabels H.localGraph).getD j 0 := by
    intro i hi j hj
    rw [hval i hi, hval j hj, Nat.add_left_cancel_iff, ← hgetD_loc i hi, ← hgetD_loc j hj]
    exact label_eq_iff_of_partsOf_eq hparts hi hj
  set cl := compLabels H.localGraph
  have hcl_len : cl.length = H.verts.length := compLabels_length H.localGraph
  refine ⟨Nat.le_add_right _ _, ?_, ?_, ?_⟩
  · intro v hv
    have hvL : v ∈ H.verts := List.mem_toFinset.mp hv
    have hi : H.verts.idxOf v < H.verts.length := List.idxOf_lt_length_of_mem hvL
    have hgv : H.verts[H.verts.idxOf v] = v := List.getElem_idxOf hi
    rw [← hgv, hval _ hi]
    have := hlt _ hi; omega
  · intro P hP
    unfold CompactSubgraph.componentsOf at hP
    rcases List.mem_map.mp hP with ⟨c, hc_dedup, rfl⟩
    have hc_mem : c ∈ cl := List.mem_dedup.mp hc_dedup
    rcases List.getElem_of_mem hc_mem with ⟨i₀, hi₀_cl, rfl⟩
    have hi₀ : i₀ < H.verts.length := hcl_len ▸ hi₀_cl
    have hi₀_getD : cl.getD i₀ 0 = cl[i₀] := by simp [List.getD_eq_getElem?_getD, hi₀_cl]
    have hmem_i₀ : H.verts.getD i₀ 0 ∈
        ((Finset.range H.verts.length).filter fun i => cl.getD i 0 = cl[i₀]).image fun i => H.verts.getD i 0 :=
      Finset.mem_image.mpr ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi₀, hi₀_getD⟩, rfl⟩
    have hsub : (((Finset.range H.verts.length).filter fun i => cl.getD i 0 = cl[i₀]).image fun i =>
        H.verts.getD i 0) ⊆ H.vertSet := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨i, hi_f, rfl⟩
      have hi : i < H.verts.length := Finset.mem_range.mp (Finset.mem_filter.mp hi_f).1
      rw [show H.verts.getD i 0 = H.verts[i] by simp [List.getD_eq_getElem?_getD, hi]]
      exact List.mem_toFinset.mpr (List.getElem_mem hi)
    refine ⟨⟨_, hmem_i₀⟩, hsub, mem (labelsAddr + H.verts[i₀]),
      by rw [hval i₀ hi₀]; omega, by rw [hval i₀ hi₀]; have := hlt i₀ hi₀; omega, ?_⟩
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi_f, rfl⟩
    rcases Finset.mem_filter.mp hi_f with ⟨hi_r, hi_eq⟩
    have hi : i < H.verts.length := Finset.mem_range.mp hi_r
    rw [show H.verts.getD i 0 = H.verts[i] by simp [List.getD_eq_getElem?_getD, hi]]
    exact (hiff i hi i₀ hi₀).mpr (hi_eq.trans hi₀_getD.symm)
  · intro u hu v hv huv
    have huL : u ∈ H.verts := List.mem_toFinset.mp hu
    have hvL : v ∈ H.verts := List.mem_toFinset.mp hv
    set i := H.verts.idxOf u
    set j := H.verts.idxOf v
    have hi : i < H.verts.length := List.idxOf_lt_length_of_mem huL
    have hj : j < H.verts.length := List.idxOf_lt_length_of_mem hvL
    have hgu : H.verts[i] = u := List.getElem_idxOf hi
    have hgv : H.verts[j] = v := List.getElem_idxOf hj
    have hguD : H.verts.getD i 0 = u := by simp [List.getD_eq_getElem?_getD, hi, hgu]
    have hgvD : H.verts.getD j 0 = v := by simp [List.getD_eq_getElem?_getD, hj, hgv]
    rw [← hgu, ← hgv] at huv
    have hcl_eq : cl.getD i 0 = cl.getD j 0 := (hiff i hi j hj).mp huv
    set c := cl.getD i 0
    have hc_mem : c ∈ cl := by
      have hi_cl : i < cl.length := hcl_len.symm ▸ hi
      have : c = cl[i] := by simp [c, List.getD_eq_getElem?_getD, hi_cl]
      rw [this]; exact List.getElem_mem hi_cl
    refine ⟨((Finset.range H.verts.length).filter fun t => cl.getD t 0 = c).image fun t => H.verts.getD t 0,
      List.mem_map.mpr ⟨c, List.mem_dedup.mpr hc_mem, rfl⟩,
      Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, rfl⟩, hguD⟩,
      Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hcl_eq.symm⟩, hgvD⟩⟩

/-- If `LabelsMatchParts mem labelsAddr G.verts parts 0 nlHi` holds with `parts.Pairwise Disjoint`
and `parts.toFinset.biUnion id = G.verts`, then `Cited.partsOf G (readList mem labelsAddr G.n)`
equals `parts.toFinset`. -/
lemma partsOf_readList_eq_of_labelsMatchParts {mem : ℕ → ℕ} {labelsAddr nlHi : ℕ}
    {G : Graph} {parts : List (Finset ℕ)}
    (hpw : parts.Pairwise Disjoint)
    (hunion : parts.toFinset.biUnion id = G.verts)
    (hL : LabelsMatchParts mem labelsAddr G.verts parts 0 nlHi) :
    Cited.partsOf G (readList mem labelsAddr G.n) = parts.toFinset := by
  set out := readList mem labelsAddr G.n
  have hout_getD : ∀ u ∈ G.verts, out.getD u 0 = mem (labelsAddr + u) := fun u hu => by
    have hu' : u < G.n := Finset.mem_range.mp hu
    simp [out, readList, List.getD_eq_getElem?_getD, hu']
  rcases hL with ⟨_, _, hmono, hsame⟩
  have hdisj_ne : ∀ {A B : Finset ℕ}, A ∈ parts → B ∈ parts → A ≠ B → Disjoint A B := by
    intro A B hA hB hne
    clear hmono hsame hunion out hout_getD
    induction parts with
    | nil => simp at hA
    | cons hd tl ih =>
      rw [List.pairwise_cons] at hpw
      simp only [List.mem_cons] at hA hB
      rcases hA with rfl | hA <;> rcases hB with rfl | hB
      · exact (hne rfl).elim
      · exact hpw.1 B hB
      · exact (hpw.1 A hA).symm
      · exact ih hpw.2 hA hB
  have hfiber : ∀ P ∈ parts, ∀ v ∈ P,
      G.verts.filter (fun u => out.getD u 0 = out.getD v 0) = P := by
    intro P hP v hv
    rcases hmono P hP with ⟨_, hsub, lbl, _, _, hconst⟩
    ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨huV, heq⟩
      rw [hout_getD u huV, hout_getD v (hsub hv)] at heq
      rcases hsame u huV v (hsub hv) heq with ⟨Q, hQ, huQ, hvQ⟩
      have hQP : Q = P := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj_ne hQ hP hne) hvQ hv
      exact hQP ▸ huQ
    · intro huP
      refine ⟨hsub huP, ?_⟩
      rw [hout_getD u (hsub huP), hout_getD v (hsub hv), hconst u huP, hconst v hv]
  ext S
  simp only [Cited.partsOf, Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨v, hvV, rfl⟩
    have hvU : v ∈ parts.toFinset.biUnion id := hunion.symm ▸ hvV
    rcases Finset.mem_biUnion.mp hvU with ⟨P, hPf, hvP⟩
    have hP : P ∈ parts := List.mem_toFinset.mp hPf
    rw [hfiber P hP v hvP]; exact hP
  · intro hS
    rcases (hmono S hS).1 with ⟨v, hvS⟩
    exact ⟨v, (hmono S hS).2.1 hvS, hfiber S hS v hvS⟩

/-- Top-level correctness bridge: if root `iso₀` + `act₀` satisfy `OuterRecSpec` and
`LabelsMatchParts` on `labelsAddr`, then `out := readList mem labelsAddr G.n` is an
`IsExpanderDecomposition G (1 / cfg.E) (phiOut cfg G.m r) out`! -/
theorem isExpanderDecomposition_of_outerRecSpec {cfg : ParamConfig} {r nlHi : ℕ}
    {mem : ℕ → ℕ} {labelsAddr : ℕ} {G : Graph} (hv : G.IsValid)
    {o : OuterRecOut}
    (ho : OuterRecSpec cfg G.m r G (CompactSubgraph.ofGraph G).stripIsolated.2 o)
    (hL : LabelsMatchParts mem labelsAddr G.verts
      (((CompactSubgraph.ofGraph G).stripIsolated.1.map fun v => ({v} : Finset ℕ)) ++ o.parts)
      0 nlHi) :
    let out := readList mem labelsAddr G.n
    out.length = G.n ∧
    IsExpanderDecomposition G (1 / (cfg.E : ℝ)) (phiOut cfg G.m r) out ∧
    o.depth ≤ HDepth cfg G.m r ∧
    o.edgeSum ≤ HDepth cfg G.m r * G.m ∧
    15 * o.witnessEdgeSum ≤ 16 * G.m := by
  have hrep0 := CompactSubgraph.ofGraph_represents hv
  have hst0 := CompactSubgraph.stripIsolated_spec hrep0
  set iso₀ := (CompactSubgraph.ofGraph G).stripIsolated.1
  set act₀ := (CompactSubgraph.ofGraph G).stripIsolated.2
  have he0_eq : act₀.edges.length = G.m := by
    have h1 : act₀.edges = (CompactSubgraph.ofGraph G).edges := hst0.2.2.2.2.2.1
    rw [h1]; rfl
  obtain ⟨hp_ne, hp_pw, hp_u, hp_exp, hd_pow, hes, cCut, cWit, wRet, hcr, hpot, hwRet, hw15, hw16⟩ := ho
  obtain ⟨hi_ne, hi_pw, hi_u, hi_exp⟩ :=
    singleton_parts_spec G (1 / (QOut cfg G.m r : ℝ)) hst0.1
  set lIso := iso₀.map fun v => ({v} : Finset ℕ)
  set parts := lIso ++ o.parts
  have hi_u' : lIso.toFinset.biUnion id = iso₀.toFinset := hi_u
  have hpw_all : parts.Pairwise Disjoint :=
    pairwise_disjoint_append hi_pw hp_pw (by rw [hi_u', hp_u]; exact hst0.2.1)
  have hunion_all : parts.toFinset.biUnion id = G.verts := by
    rw [biUnion_append, hi_u', hp_u]; exact hst0.2.2.1
  have hexp_all : ∀ P ∈ parts, G.IsConductanceExpanderOn P (phiOut cfg G.m r) := by
    intro P hP; unfold phiOut
    rcases List.mem_append.mp hP with h | h
    · exact hi_exp P h
    · exact hp_exp P h
  set out := readList mem labelsAddr G.n
  have hlen_out : out.length = G.n := by simp [out, readList]
  have hpartsOf : Cited.partsOf G out = parts.toFinset :=
    partsOf_readList_eq_of_labelsMatchParts hpw_all hunion_all hL
  have hK2 : 2 ≤ 16 * DOut cfg G.m r := by have := one_le_DOut cfg G.m r; omega
  have hdepth_le : o.depth ≤ HDepth cfg G.m r := by
    have h1 := depth_le_of_pow hK2 (by omega : act₀.edges.length ≤ G.m) hd_pow
    unfold HDepth; omega
  have hesum_le : o.edgeSum ≤ HDepth cfg G.m r * G.m :=
    le_trans hes (Nat.mul_le_mul hdepth_le (by omega))
  have hwsum_le : 15 * o.witnessEdgeSum ≤ 16 * G.m := by omega
  have hcut_36 : 8 * cfg.E * cCut ≤ G.m := by
    have h1 : bOut cfg G.m * cCut ≤ 2 * cfg.kappa * (G.m * (ell G.m + 1)) := by
      calc bOut cfg G.m * cCut ≤ 2 * cfg.kappa * cutPotential act₀.edges.length := hpot
        _ = 2 * cfg.kappa * cutPotential G.m := by rw [he0_eq]
        _ ≤ 2 * cfg.kappa * (G.m * (ell G.m + 1)) :=
            Nat.mul_le_mul_left _ (cutPotential_le_mul_ell G.m)
    have hden := cut_budget_denom cfg G.m
    have hmul : bOut cfg G.m * (8 * cfg.E * cCut) ≤ bOut cfg G.m * G.m := by
      calc bOut cfg G.m * (8 * cfg.E * cCut)
          = 8 * cfg.E * (bOut cfg G.m * cCut) := by ring
        _ ≤ 8 * cfg.E * (2 * cfg.kappa * (G.m * (ell G.m + 1))) := Nat.mul_le_mul_left _ h1
        _ = (16 * cfg.kappa * (ell G.m + 1) * cfg.E) * G.m := by ring
        _ ≤ bOut cfg G.m * G.m := Nat.mul_le_mul_right G.m hden
    exact Nat.le_of_mul_le_mul_left hmul (one_le_bOut cfg G.m)
  have hcut_37 : 15 * bOut cfg G.m * cWit ≤ G.m := by
    have h16 : 16 * (15 * bOut cfg G.m * cWit) ≤ 16 * G.m := by
      calc 16 * (15 * bOut cfg G.m * cWit)
          = 15 * (16 * bOut cfg G.m * cWit) := by ring
        _ ≤ 15 * o.witnessEdgeSum := Nat.mul_le_mul_left 15 hw16
        _ ≤ 16 * G.m := hwsum_le
    exact Nat.le_of_mul_le_mul_left h16 (by decide)
  have hcomb : cfg.E * (cCut + cWit) ≤ G.m :=
    combined_cut_budget (E_le_bOut cfg G.m) hcut_36 hcut_37
  have hcross_lbl :
      (G.edges.filter fun ed => decide (out.getD ed.1 0 ≠ out.getD ed.2 0)).length ≤ cCut + cWit := by
    have hins_act : G.inside act₀.vertSet = G.edges :=
      hst0.2.2.2.2.1.2.2.symm.trans hst0.2.2.2.2.2.1
    have hle : (G.edges.filter fun ed => decide (out.getD ed.1 0 ≠ out.getD ed.2 0)).length ≤
        crossingCount G act₀.vertSet o.parts := by
      unfold crossingCount
      rw [hins_act]
      apply length_filter_le_of_imp
      intro ed hed hne_lbl
      rw [decide_eq_true_iff] at hne_lbl ⊢
      have hv_e := hv ed hed
      intro P hP ⟨h1P, h2P⟩
      have hPparts : P ∈ parts := List.mem_append_right lIso hP
      rcases hL.2.2.1 P hPparts with ⟨_, _, lbl, _, _, hconst⟩
      have h1 : out.getD ed.1 0 = lbl := by
        have : out.getD ed.1 0 = mem (labelsAddr + ed.1) := by
          simp [out, readList, List.getD_eq_getElem?_getD, hv_e.1]
        rw [this]; exact hconst ed.1 h1P
      have h2 : out.getD ed.2 0 = lbl := by
        have : out.getD ed.2 0 = mem (labelsAddr + ed.2) := by
          simp [out, readList, List.getD_eq_getElem?_getD, hv_e.2]
        rw [this]; exact hconst ed.2 h2P
      exact hne_lbl (h1.trans h2.symm)
    exact le_trans hle hcr
  have hsum_cut_nat : cfg.E * ∑ X ∈ Cited.partsOf G out, G.cut X ≤ G.vol G.verts := by
    rw [sum_cut_partsOf hv, vol_verts_of_isValid hv]
    have hmul : cfg.E * (2 * (G.edges.filter fun ed =>
        decide (out.getD ed.1 0 ≠ out.getD ed.2 0)).length) ≤ 2 * (cfg.E * (cCut + cWit)) := by
      calc cfg.E * (2 * (G.edges.filter fun ed =>
            decide (out.getD ed.1 0 ≠ out.getD ed.2 0)).length)
          = 2 * (cfg.E * (G.edges.filter fun ed =>
            decide (out.getD ed.1 0 ≠ out.getD ed.2 0)).length) := by ring
        _ ≤ 2 * (cfg.E * (cCut + cWit)) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left cfg.E hcross_lbl)
    omega
  have hsum_cut_real : (∑ X ∈ Cited.partsOf G out, (G.cut X : ℝ)) ≤
      1 / (cfg.E : ℝ) * (G.vol G.verts : ℝ) := by
    have hEpos : (0 : ℝ) < (cfg.E : ℝ) := by exact_mod_cast cfg.hE
    have hnat_r : (cfg.E : ℝ) * (∑ X ∈ Cited.partsOf G out, (G.cut X : ℝ)) ≤
        (G.vol G.verts : ℝ) := by
      have : ((cfg.E * ∑ X ∈ Cited.partsOf G out, G.cut X : ℕ) : ℝ) ≤
          (G.vol G.verts : ℝ) := by exact_mod_cast hsum_cut_nat
      simpa [Nat.cast_sum] using this
    rw [one_div_mul_eq_div, le_div_iff₀ hEpos]
    linarith
  refine ⟨hlen_out, ⟨hlen_out, ?_, hsum_cut_real⟩, hdepth_le, hesum_le, hwsum_le⟩
  intro X hX
  rw [hpartsOf, List.mem_toFinset] at hX
  exact hexp_all X hX


end MinCostFlow.ExpanderDecomp
