module

public import MinCostFlow.SparseCore.Program.CompLayout
public import MinCostFlow.SparseCore.Program.CompCutLogBase
public import MinCostFlow.SparseCore.Program.ReadSpec
import Mathlib.Tactic.Linarith

/-!
# Data-Structure Specification for Per-Component Dynamic LSF (`CompContract`)

Defines the `WordRAM.DataStructure (CompLSFFamily k)` specification `compLSFDS W w k` for the
per-component dynamic LSF manager (P4), exposing:

* `init`: `[g0Ptr, lenArr, L_in, P_fp, k, L_w, vCap, eCap, heap]` — discovers components of `G₀`
  in `O(n₀ + m₀ + 1)`, skips isolated components (`m_C = 0`, no window and no init call), and
  initializes edgeful components (`1 ≤ m_C`) via `W.initOff`, creating
  `compLSFInitFamily W.lsfInit G₀ ℓ₀ k`.
* `op 0` (batch update): `[b, batchPtr, heap]` — splits batch `U` into the parts of
  `touchedCompsBatch`, updates each touched edgeful component across all `k` branches via
  `lsfModule`'s exact `lsfApplyBatch`, writes `[numTouched, c_0, ...]` at `heap`, and leaves
  `compLSFBatchFamily S U`. Cost is at most a constant (free of the input) times
  `k * ∑_{touched edgeful C} lsfBatchCost_C + |U| + 1`.
* `op 1` (vertex component): `[b, v, heap]` — writes `[c, isEdgeful, n_C, m_C]` at `heap`.
* `op 2` (window handle): `[b, c, j, heap]` — writes the `LSFRep W.h` handle for edgeful
  component `c` and branch `j` at `heap`.
* `op 3` (forest root): `[b, j, v, heap]` — writes `(S j).RF.root v` at `heap`.
* `op 4` (edge info & `wstrGlobal`): `[b, j, e, heap]` — writes
  `[isCross, isIns, wstrNumPtr, wstrDenPtr]` at `heap` representing `crossEdges`,
  `insertedGlobal`, and exact rational `(S j).wstrGlobal e`.
* `op 5` (global header info): `[b, heap]` — writes `[numComps, numEdgeful, k, vCap, eCap, L_w]`
  at `heap`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-! ## 1. Edgeful components and projected batch word counts -/

/-- Edgeful connected components of `G₀` (`1 ≤ (compGraph G₀ C).m`). -/
noncomputable def edgefulComps (G₀ : MGraph) : Finset (Finset ℕ) :=
  open Classical in (components G₀).filter fun C => 1 ≤ (compGraph G₀ C).m

/-- Projected word length of one encoded update at `uPtr` (in `mem`) onto component `C` of `cs`.
* Same-component `.insert`: `4` words.
* Cross-component `.insert`: `6` words on each endpoint component (`[.insert e a a, .delete e]`,
  word lengths `4 + 2 = 6`).
* `.delete`: `2` words if `e ∈ G_C.E` (never holds for cross-edges, since cross-inserts are projected to
  insert-then-delete self-loops), else `0`.
* `.split` (Tag 2 or Tag 3): `dgUpdateMemLen mem uPtr` if `v ∈ G_C.V`, else `0` (upper bound on the
  cross-edge-filtered projected split encoding). -/
noncomputable def projUpdWords (mem : ℕ → ℕ) (cs : CompLSFState) (C : Finset ℕ)
    (uPtr : ℕ) (u : Update) : ℕ :=
  open Classical in
  match u with
  | .insert _ a b =>
    if a ∈ (cs.compSt C).G.V ∧ b ∈ (cs.compSt C).G.V then 4
    else if a ∈ (cs.compSt C).G.V ∨ b ∈ (cs.compSt C).G.V then 6
    else 0
  | .delete e =>
    if e ∈ (cs.compSt C).G.E then 2 else 0
  | .split v _ _ _ =>
    if v ∈ (cs.compSt C).G.V then dgUpdateMemLen mem uPtr else 0

/-- Total body words of the projected batch onto component `C` for a list of encoded updates
starting at `ptr` in `mem`. -/
noncomputable def projBatchBodyWords (mem : ℕ → ℕ) (C : Finset ℕ) :
    CompLSFState → ℕ → List Update → ℕ
  | _, _, [] => 0
  | cs, ptr, u :: us =>
    projUpdWords mem cs C ptr u +
      projBatchBodyWords mem C (compLSFStepSingle cs u) (ptr + dgUpdateMemLen mem ptr) us

/-- Exact `lsfBatchCost` of component `C`'s projected batch (`1 + projBodyWords` words at limb
width `L_w`). -/
noncomputable def compProjLsfBatchCost (mem : ℕ → ℕ) (cs : CompLSFState) (C : Finset ℕ)
    (batchPtr L_w : ℕ) (U : List Update) : ℕ :=
  lsfBatchCostFactor * ((1 + projBatchBodyWords mem C cs (batchPtr + 1) U) * L_w + 1)

/-- Sum of `compProjLsfBatchCost` over all touched edgeful components of `cs` on batch `U`. -/
noncomputable def sumTouchedLsfBatchCost (mem : ℕ → ℕ) (cs : CompLSFState) (batchPtr L_w : ℕ)
    (U : List Update) : ℕ :=
  open Classical in
  ((touchedCompsBatch cs U).filter fun C => 1 ≤ (compGraph cs.G₀ C).m).sum fun C =>
    compProjLsfBatchCost mem cs C batchPtr L_w U

/-! ## 2. Explicit input-free constants for `compLSFDS` -/

/-- Constant multiplier on `k * ∑_{touched edgeful C} lsfBatchCost_C` in `op 0`. -/
def compBatchLsfMul : ℕ := 5

/-- Constant multiplier on `U.length + 1` in `op 0`. -/
def compBatchUpdMul : ℕ := 800

/-- Constant multiplier on `G₀.n + G₀.m + 1` in `init`. -/
def compInitLinMul : ℕ := 800

/-- Constant multiplier on each edgeful component's `(n_C + m_C + 1)` setup work in `init`. -/
def compInitCompMul : ℕ := 800

/-! ## 3. Initialization and operation predicates, costs, and spaces -/

/-- Zero-extended length function read from `lenArr` on `G₀.E`. -/
noncomputable def compReadLen (mem : ℕ → ℕ) (lenArr h L_in P_fp : ℕ) (G₀ : MGraph) : ℕ → ℝ :=
  open Classical in fun e => if e ∈ G₀.E then fixVal mem (lenArr + e * L_in) h L_in P_fp else 0

/-- Initialization precondition for `compLSFDS W w k G₀`:
`args = [g0Ptr, lenArr, W.L_in, W.P_fp, k, L_w, vCap, eCap, heap]`. -/
def CompInitPre (W : LSFWindowImpl) (w k : ℕ) (G₀ : MGraph) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ (g0Ptr vCap0 eCap0 lenArr L_w vCap eCap heap : ℕ),
    args = [g0Ptr, lenArr, W.L_in, W.P_fp, k, L_w, vCap, eCap, heap] ∧
    1 ≤ k ∧ 1 ≤ L_w ∧ 2 ≤ W.h * L_w ∧ W.h < 2 ^ w ∧ 1 ≤ eCap ∧ 16 ≤ 2 ^ w ∧
    G₀.IsValid ∧ G₀.V.Nonempty ∧
    DynGraphAt mem g0Ptr vCap0 eCap0 G₀ ∧
    vCap0 ≤ vCap ∧ eCap0 ≤ eCap ∧
    g0Ptr + dynGraphSize vCap0 eCap0 ≤ heap ∧
    lenArr + eCap * W.L_in ≤ heap ∧
    (∀ e ∈ G₀.E, Valid mem (lenArr + e * W.L_in) W.h W.L_in ∧
      0 < fixVal mem (lenArr + e * W.L_in) W.h W.L_in W.P_fp) ∧
    (∀ C ∈ edgefulComps G₀, W.winPre w k L_w vCap eCap (compGraph G₀ C))

/-- Initialization postcondition: builds `compLSFInitFamily W.lsfInit G₀ ℓ₀ k` for `G₀` and the
lengths read from `lenArr`. -/
def CompInitPost (W : LSFWindowImpl) (k : ℕ) (G₀ : MGraph) (args : List ℕ) (mem : ℕ → ℕ)
    (S' : CompLSFFamily k) (_mem' : ℕ → ℕ) : Prop :=
  S' = compLSFInitFamily W.lsfInit G₀
    (compReadLen mem (args.getD 1 0) W.h W.L_in W.P_fp G₀) k

/-- Initialization heap space above `heap` for `compLSFDS W w k G₀`. -/
noncomputable def compInitSpace (W : LSFWindowImpl) (k : ℕ) (G₀ : MGraph) (args : List ℕ) : ℕ :=
  let L_w := args.getD 5 0
  let vCap := args.getD 6 0
  let eCap := args.getD 7 0
  compStaticSize vCap eCap L_w + G₀.m * k + vCap + G₀.n + 3 * G₀.m +
    (edgefulComps G₀).sum fun C =>
      dynGraphSize vCap eCap +
        W.winSpace k L_w vCap eCap (compGraph G₀ C).n (compGraph G₀ C).m

/-- Initialization amortized cost bound (including initial `compPhi`) for `compLSFDS W w k G₀`.
Charges `0` window init cost to isolated components (`m_C = 0`). -/
noncomputable def compInitCost (W : LSFWindowImpl) (k : ℕ) (G₀ : MGraph) (args : List ℕ) : ℕ :=
  let L_w := args.getD 5 0
  compInitLinMul * (G₀.n + G₀.m + 1) +
    (edgefulComps G₀).sum fun C =>
      let nC := (compGraph G₀ C).n
      let mC := (compGraph G₀ C).m
      W.winCost k L_w nC mC +
        k * (3000 * (nC + 1) * (Nat.log 2 (nC + 2) + 1)) +
        compInitCompMul * (nC + mC + 1)

/-- Precondition of `op 0` (batch update `[b, batchPtr, heap]`). -/
def CompBatchPre (w k : ℕ) (S : CompLSFFamily k) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ (hk : 1 ≤ k) (b batchPtr heap totalWords : ℕ) (U : List Update),
    args = [b, batchPtr, heap] ∧
    16 ≤ 2 ^ w ∧
    let cs0 := S ⟨0, hk⟩
    BatchAt mem batchPtr cs0.G U totalWords ∧
    cs0.G.BatchIsValid U ∧
    BatchWithinCaps (mem (b + compOffVCap)) (mem (b + compOffECap)) U ∧
    (∀ i < totalWords, mem (batchPtr + i) < 2 ^ w) ∧
    batchPtr + totalWords ≤ heap ∧
    (∀ i < totalWords, batchPtr + i < b ∨ mem (b + compOffEndAddr) ≤ batchPtr + i)

/-- Heap space above `heap` needed by `op 0` (touched list, per-branch `LSFChangeAt` table and
records, scratch cut/split buffers, and temporary 1-update buffer). Polynomial in fixed sizes
`vCap`, `eCap`, `k`, and batch words; independent of `heap`. -/
def compBatchSpace (k : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  let b := args.getD 0 0
  let batchPtr := args.getD 1 0
  let vCap := mem (b + compOffVCap)
  let eCap := mem (b + compOffECap)
  7 + 3 * mem batchPtr + batchMemLen mem batchPtr + 2 * eCap + k * (4 + 4 * vCap)

/-- Postcondition of `op 0`: every branch advances by `compLSFBatch`, `[heap, heap + 1 + r)` holds
the touched component list (`r ≤ 2 * U.length`), and `[heap + 1 + r, heap + 1 + r + k)` holds
pointers `chgPtr_j` to per-branch change records giving BOTH:
* `Read.LSFChangeAt mem' chgPtr_j (chg j)` with `(chg j).Exact (S j).lsf (S' j).lsf` (P10),
* the ordered forest-cut sequence `cuts = List.zip (chg j).fDel (chg j).roots` satisfying
  `CompForestCutsValid` and removing every edge in `(S j).RF.F.E \ (S' j).RF.F.E` with zero links
  (P2, P9). -/
def CompBatchPost (k : ℕ) (S : CompLSFFamily k) (args : List ℕ) (mem : ℕ → ℕ)
    (S' : CompLSFFamily k) (mem' : ℕ → ℕ) : Prop :=
  ∃ (hk : 1 ≤ k) (b batchPtr heap totalWords : ℕ) (U : List Update),
    args = [b, batchPtr, heap] ∧
    BatchAt mem batchPtr (S ⟨0, hk⟩).G U totalWords ∧
    S' = compLSFBatchFamily S U ∧
    mem' heap ≤ 2 * U.length ∧
    ∃ chg : Fin k → Read.LSFChange, ∀ j : Fin k,
      let chgPtr := mem' (heap + 1 + mem' heap + j.1)
      let cuts := List.zip (chg j).fDel (chg j).roots
      Read.LSFChangeAt mem' chgPtr (chg j) ∧
      (chg j).Exact (S j).lsf (S' j).lsf ∧
      (chg j).fDel.length ≤ (chg j).roots.length ∧
      CompForestCutsValid (mem (b + compOffVCap)) (S j).RF cuts ∧
      (cuts.foldl compApplyForestCut (S j).RF).F.E = (S' j).RF.F.E ∧
      heap + 1 + mem' heap + k ≤ chgPtr ∧
      chgPtr + (chg j).words ≤ heap + compBatchSpace k args mem

private lemma applyLSFBatch_G_eq (S : LSFState) : ∀ U, (applyLSFBatch S U).G = S.G.applyBatch U
  | [] => rfl
  | u :: us => by
    change (applyLSFBatch (applyLSFUpdate S u) us).G = (S.G.applyUpdate u).applyBatch us
    rw [applyLSFBatch_G_eq]; cases u <;> rfl

private def GraphEq (G₁ G₂ : MGraph) : Prop :=
  G₁.V = G₂.V ∧ G₁.E = G₂.E ∧ ∀ e ∈ G₁.E, G₁.tail e = G₂.tail e ∧ G₁.head e = G₂.head e

private lemma graphEq_refl (G : MGraph) : GraphEq G G := ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩

private lemma updateAt_of_graphEq {mem : ℕ → ℕ} {a : ℕ} {G₁ G₂ : MGraph} {u : Update} {l : ℕ}
    (hG : GraphEq G₁ G₂) (h : UpdateAt mem a G₁ u l) : UpdateAt mem a G₂ u l := by
  cases u with
  | insert _ _ _ => exact h
  | delete _ => exact h
  | split v v' St Sh =>
    rcases h with ⟨Lt, Lh, hnd1, hnd2, hLt, hLh, hlen, hLA⟩ | ⟨Lt, Lh, hnd1, hnd2, hLt, hLh, hlen, hLA⟩
    · left; refine ⟨Lt, Lh, hnd1, hnd2, fun e => ?_, fun e => ?_, hlen, hLA⟩
      · rw [hLt]; exact ⟨fun ⟨he, ht, hs⟩ => ⟨hG.2.1 ▸ he, (hG.2.2 e he).1 ▸ ht, hs⟩,
          fun ⟨he, ht, hs⟩ => ⟨hG.2.1.symm ▸ he, (hG.2.2 e (hG.2.1.symm ▸ he)).1.symm ▸ ht, hs⟩⟩
      · rw [hLh]; exact ⟨fun ⟨he, hh, hs⟩ => ⟨hG.2.1 ▸ he, (hG.2.2 e he).2 ▸ hh, hs⟩,
          fun ⟨he, hh, hs⟩ => ⟨hG.2.1.symm ▸ he, (hG.2.2 e (hG.2.1.symm ▸ he)).2.symm ▸ hh, hs⟩⟩
    · right; refine ⟨Lt, Lh, hnd1, hnd2, fun e => ?_, fun e => ?_, hlen, hLA⟩
      · rw [hLt]; exact ⟨fun ⟨he, ht, hs⟩ => ⟨hG.2.1 ▸ he, (hG.2.2 e he).1 ▸ ht, hs⟩,
          fun ⟨he, ht, hs⟩ => ⟨hG.2.1.symm ▸ he, (hG.2.2 e (hG.2.1.symm ▸ he)).1.symm ▸ ht, hs⟩⟩
      · rw [hLh]; exact ⟨fun ⟨he, hh, hs⟩ => ⟨hG.2.1 ▸ he, (hG.2.2 e he).2 ▸ hh, hs⟩,
          fun ⟨he, hh, hs⟩ => ⟨hG.2.1.symm ▸ he, (hG.2.2 e (hG.2.1.symm ▸ he)).2.symm ▸ hh, hs⟩⟩

private lemma touchedCompsBatch_cons_uncond (cs : CompLSFState) (u : Update) (us : List Update) :
    touchedCompsBatch cs (u :: us) =
      touchedComps cs u ∪ touchedCompsBatch (compLSFStepSingle cs u) us := by
  classical
  ext C
  simp only [touchedCompsBatch, touchedComps, Finset.mem_union, Finset.mem_filter]
  have hG0 : (compLSFStepSingle cs u).G₀ = cs.G₀ := rfl
  rw [hG0]
  have hstep : projCompBatchG cs.G (cs.compSt C).G (u :: us) =
      projCompUpdateG cs.G (cs.compSt C).G u ++
        projCompBatchG (compLSFStepSingle cs u).G ((compLSFStepSingle cs u).compSt C).G us := by
    simp [projCompBatchG, compLSFStepSingle, applyLSFBatch_G_eq]
  rw [hstep, ne_eq, List.append_eq_nil_iff, not_and_or]
  tauto

/-- Two updates with the same `UpdateAt` encoding on `GraphEq` graphs have identical word length,
`GraphEq` global graph effect, projected word length, and touched-component sets. -/
private lemma updateAt_same_effect {mem : ℕ → ℕ} {a : ℕ} {G₁ G₂ : MGraph} {u₁ u₂ : Update} {l₁ l₂ : ℕ}
    (hG : GraphEq G₁ G₂) (h1 : UpdateAt mem a G₁ u₁ l₁) (h2 : UpdateAt mem a G₂ u₂ l₂) :
    l₁ = l₂ ∧ GraphEq (G₁.applyUpdate u₁) (G₂.applyUpdate u₂) ∧
    ∀ (cs₁ cs₂ : CompLSFState), cs₁.G₀ = cs₂.G₀ → cs₁.G = G₁ → cs₂.G = G₂ →
      (∀ C ∈ components cs₁.G₀, (cs₁.compSt C).G.E ⊆ G₁.E) →
      (∀ C ∈ components cs₁.G₀, GraphEq (cs₁.compSt C).G (cs₂.compSt C).G) →
      (∀ C ∈ components cs₁.G₀, projUpdWords mem cs₁ C a u₁ = projUpdWords mem cs₂ C a u₂) ∧
      touchedComps cs₁ u₁ = touchedComps cs₂ u₂ ∧
      (∀ C ∈ components cs₁.G₀, ((compLSFStepSingle cs₁ u₁).compSt C).G.E ⊆ (G₁.applyUpdate u₁).E) ∧
      (∀ C ∈ components cs₁.G₀,
        GraphEq ((compLSFStepSingle cs₁ u₁).compSt C).G ((compLSFStepSingle cs₂ u₂).compSt C).G) := by
  have h2' : UpdateAt mem a G₁ u₂ l₂ := updateAt_of_graphEq ⟨hG.1.symm, hG.2.1.symm, fun e he =>
    let p := hG.2.2 e (hG.2.1.symm ▸ he); ⟨p.1.symm, p.2.symm⟩⟩ h2
  have hE_pres : ∀ (cs : CompLSFState) (u : Update), cs.G = G₁ →
      (∀ C ∈ components cs.G₀, (cs.compSt C).G.E ⊆ G₁.E) →
      ∀ C ∈ components cs.G₀, ((compLSFStepSingle cs u).compSt C).G.E ⊆ (G₁.applyUpdate u).E := by
    intro cs u hGc hsub C hC
    cases u with
    | insert e x y =>
      simp only [compLSFStepSingle, applyLSFBatch_G_eq, projCompUpdateG, hGc]
      split_ifs <;> simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate]
      · exact Finset.insert_subset_insert e (hsub C hC)
      · exact (Finset.erase_subset e _).trans (Finset.insert_subset_insert e (hsub C hC))
      · exact (Finset.erase_subset e _).trans (Finset.insert_subset_insert e (hsub C hC))
      · exact (hsub C hC).trans (Finset.subset_insert _ _)
    | delete e =>
      simp only [compLSFStepSingle, applyLSFBatch_G_eq, projCompUpdateG, hGc]
      split_ifs with he <;> simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate]
      · exact Finset.erase_subset_erase e (hsub C hC)
      · intro z hz; exact Finset.mem_erase.mpr ⟨fun hze => he (hze ▸ hz), hsub C hC hz⟩
    | split v v' St Sh =>
      simp only [compLSFStepSingle, applyLSFBatch_G_eq, projCompUpdateG, hGc]
      split_ifs <;> simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate]
      · exact hsub C hC
      · exact hsub C hC
  have hApplyG_eq : ∀ {H₁ H₂ : MGraph} (u : Update), GraphEq H₁ H₂ →
      GraphEq (H₁.applyUpdate u) (H₂.applyUpdate u) := by
    intro H₁ H₂ u hH
    cases u with
    | insert e x y =>
      refine ⟨hH.1, by simp [MGraph.applyUpdate, hH.2.1], fun f hf => ?_⟩
      simp only [MGraph.applyUpdate, Finset.mem_insert] at hf ⊢
      rcases hf with rfl | hf'
      · simp
      · by_cases hfe : f = e
        · subst hfe; simp
        · simp [hfe, hH.2.2 f hf']
    | delete e =>
      refine ⟨hH.1, by simp [MGraph.applyUpdate, hH.2.1], fun f hf => ?_⟩
      exact hH.2.2 f (Finset.mem_of_mem_erase hf)
    | split v v' St Sh =>
      refine ⟨by simp [MGraph.applyUpdate, hH.1], hH.2.1, fun f hf => ?_⟩
      have ⟨ht, hh⟩ := hH.2.2 f hf
      simp [MGraph.applyUpdate, ht, hh]
  have hsame_u : ∀ (cs₁ cs₂ : CompLSFState) (u : Update), cs₁.G₀ = cs₂.G₀ → cs₁.G = G₁ → cs₂.G = G₂ →
      (∀ C ∈ components cs₁.G₀, (cs₁.compSt C).G.E ⊆ G₁.E) →
      (∀ C ∈ components cs₁.G₀, GraphEq (cs₁.compSt C).G (cs₂.compSt C).G) →
      (∀ C ∈ components cs₁.G₀, projUpdWords mem cs₁ C a u = projUpdWords mem cs₂ C a u) ∧
      touchedComps cs₁ u = touchedComps cs₂ u ∧
      (∀ C ∈ components cs₁.G₀, ((compLSFStepSingle cs₁ u).compSt C).G.E ⊆ (G₁.applyUpdate u).E) ∧
      (∀ C ∈ components cs₁.G₀,
        GraphEq ((compLSFStepSingle cs₁ u).compSt C).G ((compLSFStepSingle cs₂ u).compSt C).G) := by
    intro cs₁ cs₂ u hG0 hG1 hG2 hsub hCG
    refine ⟨fun C hC => ?_, ?_, hE_pres cs₁ u hG1 hsub, fun C hC => ?_⟩
    · have hCeq := hCG C hC
      cases u with
      | insert e x y => simp [projUpdWords, hCeq.1]
      | delete e => simp [projUpdWords, hCeq.2.1]
      | split v v' St Sh =>
        simp only [projUpdWords, hCeq.1]
    · ext C; simp only [touchedComps, hG0, Finset.mem_filter]
      constructor <;> rintro ⟨hC, hP⟩ <;> refine ⟨hC, ?_⟩
      · have hCeq := hCG C (hG0.symm ▸ hC)
        cases u with
        | insert _ _ _ => simp only [projCompUpdateG, hCeq.1] at hP ⊢; split_ifs at hP ⊢ <;> simp at hP ⊢
        | delete _ => simp only [projCompUpdateG, hCeq.2.1] at hP ⊢; split_ifs at hP ⊢ <;> simp at hP ⊢
        | split _ _ _ _ => simp only [projCompUpdateG, hCeq.1] at hP ⊢; split_ifs at hP ⊢ <;> simp at hP ⊢
      · have hCeq := hCG C (hG0.symm ▸ hC)
        cases u with
        | insert _ _ _ => simp only [projCompUpdateG, hCeq.1] at hP ⊢; split_ifs at hP ⊢ <;> simp at hP ⊢
        | delete _ => simp only [projCompUpdateG, hCeq.2.1] at hP ⊢; split_ifs at hP ⊢ <;> simp at hP ⊢
        | split _ _ _ _ => simp only [projCompUpdateG, hCeq.1] at hP ⊢; split_ifs at hP ⊢ <;> simp at hP ⊢
    · have hCeq := hCG C hC
      cases u with
      | insert e x y =>
        simp only [compLSFStepSingle, applyLSFBatch_G_eq, projCompUpdateG, hCeq.1]
        split_ifs
        · simpa [MGraph.applyBatch] using hApplyG_eq _ hCeq
        · simpa [MGraph.applyBatch] using hApplyG_eq (.delete e) (hApplyG_eq (.insert e x x) hCeq)
        · simpa [MGraph.applyBatch] using hApplyG_eq (.delete e) (hApplyG_eq (.insert e y y) hCeq)
        · simpa [MGraph.applyBatch] using hCeq
      | delete e =>
        simp only [compLSFStepSingle, applyLSFBatch_G_eq, projCompUpdateG, hCeq.2.1]
        split_ifs
        · simpa [MGraph.applyBatch] using hApplyG_eq _ hCeq
        · simpa [MGraph.applyBatch] using hCeq
      | split v v' St Sh =>
        simp only [compLSFStepSingle, applyLSFBatch_G_eq, projCompUpdateG, hCeq.1, hG1, hG2]
        split_ifs with hv
        · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil]
          have hSt_eq : ((cs₁.compSt C).G.E.filter fun e =>
              e ∈ St ∧ (cs₁.compSt C).G.tail e = v ∧ G₁.tail e = v) =
              ((cs₂.compSt C).G.E.filter fun e =>
                e ∈ St ∧ (cs₂.compSt C).G.tail e = v ∧ G₂.tail e = v) := by
            ext e; simp only [Finset.mem_filter]
            exact ⟨fun ⟨he, hs, h1, h2⟩ => ⟨hCeq.2.1 ▸ he, hs, (hCeq.2.2 e he).1 ▸ h1,
                (hG.2.2 e (hsub C hC he)).1 ▸ h2⟩,
              fun ⟨he, hs, h1, h2⟩ => let he1 := hCeq.2.1.symm ▸ he;
                ⟨he1, hs, (hCeq.2.2 e he1).1.symm ▸ h1, (hG.2.2 e (hsub C hC he1)).1.symm ▸ h2⟩⟩
          have hSh_eq : ((cs₁.compSt C).G.E.filter fun e =>
              e ∈ Sh ∧ (cs₁.compSt C).G.head e = v ∧ G₁.head e = v) =
              ((cs₂.compSt C).G.E.filter fun e =>
                e ∈ Sh ∧ (cs₂.compSt C).G.head e = v ∧ G₂.head e = v) := by
            ext e; simp only [Finset.mem_filter]
            exact ⟨fun ⟨he, hs, h1, h2⟩ => ⟨hCeq.2.1 ▸ he, hs, (hCeq.2.2 e he).2 ▸ h1,
                (hG.2.2 e (hsub C hC he)).2 ▸ h2⟩,
              fun ⟨he, hs, h1, h2⟩ => let he1 := hCeq.2.1.symm ▸ he;
                ⟨he1, hs, (hCeq.2.2 e he1).2.symm ▸ h1, (hG.2.2 e (hsub C hC he1)).2.symm ▸ h2⟩⟩
          rw [hSt_eq, hSh_eq]; exact hApplyG_eq _ hCeq
        · simpa [MGraph.applyBatch] using hCeq
  have hlist_ext : ∀ {Lt1 Lh1 Lt2 Lh2 : List ℕ} {t v1 v1' v2 v2' : ℕ},
      ListAt mem a ([t, v1, v1', Lt1.length, Lh1.length] ++ Lt1 ++ Lh1) →
      ListAt mem a ([t, v2, v2', Lt2.length, Lh2.length] ++ Lt2 ++ Lh2) →
      v1 = v2 ∧ v1' = v2' ∧ Lt1 = Lt2 ∧ Lh1 = Lh2 := by
    intro Lt1 Lh1 Lt2 Lh2 t v1 v1' v2 v2' hL1 hL2
    have hv : v1 = v2 := by have := hL1 1 (by simp); have := hL2 1 (by simp); simp at *; omega
    have hv' : v1' = v2' := by have := hL1 2 (by simp); have := hL2 2 (by simp); simp at *; omega
    have hkt : Lt1.length = Lt2.length := by have := hL1 3 (by simp); have := hL2 3 (by simp); simp at *; omega
    have hkh : Lh1.length = Lh2.length := by have := hL1 4 (by simp); have := hL2 4 (by simp); simp at *; omega
    have hLt_eq : Lt1 = Lt2 := List.ext_getElem hkt fun i h1' h2' => by
      have m1 := hL1 (5 + i) (by simp; omega)
      have m2 := hL2 (5 + i) (by simp; omega)
      simp only [List.append_assoc] at m1 m2
      rw [List.getElem_append_right (by simp), List.getElem_append_left (by simp; omega)] at m1 m2
      simp at m1 m2; omega
    have hLh_eq : Lh1 = Lh2 := List.ext_getElem hkh fun i h1' h2' => by
      have m1 := hL1 (5 + Lt1.length + i) (by simp; omega)
      have m2 := hL2 (5 + Lt2.length + i) (by simp; omega)
      rw [List.getElem_append_right (by simp; omega)] at m1 m2
      have m1' : mem (a + (5 + Lt1.length + i)) = Lh1[i] := by
        rw [m1]; congr 1; simp; omega
      have m2' : mem (a + (5 + Lt2.length + i)) = Lh2[i] := by
        rw [m2]; congr 1; simp; omega
      rw [hkt] at m1'; omega
    exact ⟨hv, hv', hLt_eq, hLh_eq⟩
  cases u₁ with
  | insert e1 a1 b1 =>
    rcases h1 with ⟨rfl, hL1⟩
    have hm0 : mem a = 0 := by simpa using hL1 0 (by simp)
    cases u₂ with
    | insert e2 a2 b2 =>
      rcases h2' with ⟨rfl, hL2⟩
      have he : e1 = e2 := by have := hL1 1 (by simp); have := hL2 1 (by simp); simp at *; omega
      have ha : a1 = a2 := by have := hL1 2 (by simp); have := hL2 2 (by simp); simp at *; omega
      have hb : b1 = b2 := by have := hL1 3 (by simp); have := hL2 3 (by simp); simp at *; omega
      subst he ha hb
      exact ⟨rfl, hApplyG_eq _ hG, fun cs₁ cs₂ hG0 hG1 hG2 hsub hCG => hsame_u cs₁ cs₂ _ hG0 hG1 hG2 hsub hCG⟩
    | delete _ => rcases h2' with ⟨_, hL2⟩; have := hL2 0 (by simp); simp at this; omega
    | split _ _ _ _ =>
      rcases h2' with ⟨_, _, _, _, _, _, _, hL2⟩ | ⟨_, _, _, _, _, _, _, hL2⟩ <;>
        (have := hL2 0 (by simp); simp at this; omega)
  | delete e1 =>
    rcases h1 with ⟨rfl, hL1⟩
    have hm0 : mem a = 1 := by simpa using hL1 0 (by simp)
    cases u₂ with
    | insert _ _ _ => rcases h2' with ⟨_, hL2⟩; have := hL2 0 (by simp); simp at this; omega
    | delete e2 =>
      rcases h2' with ⟨rfl, hL2⟩
      have he : e1 = e2 := by have := hL1 1 (by simp); have := hL2 1 (by simp); simp at *; omega
      subst he
      exact ⟨rfl, hApplyG_eq _ hG, fun cs₁ cs₂ hG0 hG1 hG2 hsub hCG => hsame_u cs₁ cs₂ _ hG0 hG1 hG2 hsub hCG⟩
    | split _ _ _ _ =>
      rcases h2' with ⟨_, _, _, _, _, _, _, hL2⟩ | ⟨_, _, _, _, _, _, _, hL2⟩ <;>
        (have := hL2 0 (by simp); simp at this; omega)
  | split v1 v1' St1 Sh1 =>
    cases u₂ with
    | insert _ _ _ =>
      rcases h2' with ⟨_, hL2⟩; have m2 := hL2 0 (by simp)
      rcases h1 with ⟨_, _, _, _, _, _, _, hL1⟩ | ⟨_, _, _, _, _, _, _, hL1⟩ <;>
        (have m1 := hL1 0 (by simp); simp at m1 m2; omega)
    | delete _ =>
      rcases h2' with ⟨_, hL2⟩; have m2 := hL2 0 (by simp)
      rcases h1 with ⟨_, _, _, _, _, _, _, hL1⟩ | ⟨_, _, _, _, _, _, _, hL1⟩ <;>
        (have m1 := hL1 0 (by simp); simp at m1 m2; omega)
    | split v2 v2' St2 Sh2 =>
      have hsame_v : v1 = v2 ∧ v1' = v2' ∧ l₁ = l₂ ∧
          (∀ e ∈ G₁.E, G₁.tail e = v1 → (e ∈ St1 ↔ e ∈ St2)) ∧
          (∀ e ∈ G₁.E, G₁.head e = v1 → (e ∈ Sh1 ↔ e ∈ Sh2)) := by
        rcases h1 with ⟨Lt1, Lh1, _, _, hLt1, hLh1, rfl, hL1⟩ | ⟨Lt1, Lh1, _, _, hLt1, hLh1, rfl, hL1⟩ <;>
        rcases h2' with ⟨Lt2, Lh2, _, _, hLt2, hLh2, rfl, hL2⟩ | ⟨Lt2, Lh2, _, _, hLt2, hLh2, rfl, hL2⟩
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := hlist_ext hL1 hL2
          exact ⟨rfl, rfl, rfl, fun e he ht => by simpa [he, ht] using (hLt1 e).symm.trans (hLt2 e),
            fun e he hh => by simpa [he, hh] using (hLh1 e).symm.trans (hLh2 e)⟩
        · have m1 := hL1 0 (by simp); have m2 := hL2 0 (by simp); simp at m1 m2; omega
        · have m1 := hL1 0 (by simp); have m2 := hL2 0 (by simp); simp at m1 m2; omega
        · obtain ⟨rfl, rfl, rfl, rfl⟩ := hlist_ext hL1 hL2
          refine ⟨rfl, rfl, rfl, fun e he ht => ?_, fun e he hh => ?_⟩
          · have := (hLt1 e).symm.trans (hLt2 e); simp [he, ht] at this; exact not_iff_not.mp this
          · have := (hLh1 e).symm.trans (hLh2 e); simp [he, hh] at this; exact not_iff_not.mp this
      rcases hsame_v with ⟨rfl, rfl, rfl, hSt, hSh⟩
      refine ⟨rfl, ?_, fun cs₁ cs₂ hG0 hG1 hG2 hsub hCG => ⟨fun C hC => ?_, ?_,
        hE_pres cs₁ _ hG1 hsub, fun C hC => ?_⟩⟩
      · refine ⟨by simp [MGraph.applyUpdate, hG.1], hG.2.1, fun e he => ?_⟩
        have ⟨ht, hh⟩ := hG.2.2 e he
        simp only [MGraph.applyUpdate, ht, hh]
        refine ⟨?_, ?_⟩
        · by_cases hte : G₂.tail e = v1
          · simp [hte, hSt e he (ht.trans hte)]
          · simp [hte]
        · by_cases hhe : G₂.head e = v1
          · simp [hhe, hSh e he (hh.trans hhe)]
          · simp [hhe]
      · have hCeq := hCG C hC
        simp only [projUpdWords, hCeq.1]
      · ext C; simp only [touchedComps, hG0, Finset.mem_filter]
        constructor <;> rintro ⟨hC, hP⟩ <;> refine ⟨hC, ?_⟩
        · have hCeq := hCG C (hG0.symm ▸ hC)
          simp only [projCompUpdateG, hCeq.1] at hP ⊢
          split_ifs at hP ⊢ <;> simp at hP ⊢
        · have hCeq := hCG C (hG0.symm ▸ hC)
          simp only [projCompUpdateG, hCeq.1] at hP ⊢
          split_ifs at hP ⊢ <;> simp at hP ⊢
      · have hCeq := hCG C hC
        simp only [compLSFStepSingle, applyLSFBatch_G_eq, projCompUpdateG, hCeq.1, hG1, hG2]
        split_ifs with hv
        · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil]
          have hSt_eq : ((cs₁.compSt C).G.E.filter fun e =>
              e ∈ St1 ∧ (cs₁.compSt C).G.tail e = v1 ∧ G₁.tail e = v1) =
              ((cs₂.compSt C).G.E.filter fun e =>
                e ∈ St2 ∧ (cs₂.compSt C).G.tail e = v1 ∧ G₂.tail e = v1) := by
            ext e; simp only [Finset.mem_filter]
            exact ⟨fun ⟨he, hs, h1, h2⟩ => ⟨hCeq.2.1 ▸ he, (hSt e (hsub C hC he) h2).mp hs,
                (hCeq.2.2 e he).1 ▸ h1, (hG.2.2 e (hsub C hC he)).1 ▸ h2⟩,
              fun ⟨he, hs, h1, h2⟩ => let he1 := hCeq.2.1.symm ▸ he;
                let ht1 := (hG.2.2 e (hsub C hC he1)).1.symm ▸ h2;
                ⟨he1, (hSt e (hsub C hC he1) ht1).mpr hs, (hCeq.2.2 e he1).1.symm ▸ h1, ht1⟩⟩
          have hSh_eq : ((cs₁.compSt C).G.E.filter fun e =>
              e ∈ Sh1 ∧ (cs₁.compSt C).G.head e = v1 ∧ G₁.head e = v1) =
              ((cs₂.compSt C).G.E.filter fun e =>
                e ∈ Sh2 ∧ (cs₂.compSt C).G.head e = v1 ∧ G₂.head e = v1) := by
            ext e; simp only [Finset.mem_filter]
            exact ⟨fun ⟨he, hs, h1, h2⟩ => ⟨hCeq.2.1 ▸ he, (hSh e (hsub C hC he) h2).mp hs,
                (hCeq.2.2 e he).2 ▸ h1, (hG.2.2 e (hsub C hC he)).2 ▸ h2⟩,
              fun ⟨he, hs, h1, h2⟩ => let he1 := hCeq.2.1.symm ▸ he;
                let hh1 := (hG.2.2 e (hsub C hC he1)).2.symm ▸ h2;
                ⟨he1, (hSh e (hsub C hC he1) hh1).mpr hs, (hCeq.2.2 e he1).2.symm ▸ h1, hh1⟩⟩
          rw [hSt_eq, hSh_eq]; exact hApplyG_eq _ hCeq
        · simpa [MGraph.applyBatch] using hCeq

private lemma batchBodyAt_same_cost {mem : ℕ → ℕ} :
    ∀ {U₁ U₂ : List Update} {a tw₁ tw₂ : ℕ} {cs₁ cs₂ : CompLSFState},
      U₁.length = U₂.length → cs₁.G₀ = cs₂.G₀ → GraphEq cs₁.G cs₂.G →
      (∀ C ∈ components cs₁.G₀, (cs₁.compSt C).G.E ⊆ cs₁.G.E) →
      (∀ C ∈ components cs₁.G₀, GraphEq (cs₁.compSt C).G (cs₂.compSt C).G) →
      BatchBodyAt mem a cs₁.G U₁ tw₁ → BatchBodyAt mem a cs₂.G U₂ tw₂ →
      (∀ C ∈ components cs₁.G₀, projBatchBodyWords mem C cs₁ a U₁ = projBatchBodyWords mem C cs₂ a U₂) ∧
      touchedCompsBatch cs₁ U₁ = touchedCompsBatch cs₂ U₂
  | [], [], _, _, _, _, _, _, _, _, _, _, _, _ => ⟨fun _ _ => rfl, by simp [touchedCompsBatch, projCompBatchG]⟩
  | u₁ :: us₁, u₂ :: us₂, a, tw₁, tw₂, cs₁, cs₂, hlen, hG0, hG, hsub, hCG, h1, h2 => by
    rcases h1 with ⟨l₁, _, hu1, hr1⟩
    rcases h2 with ⟨l₂, _, hu2, hr2⟩
    have ⟨hl, hG', hrest⟩ := updateAt_same_effect hG hu1 hu2
    subst hl
    obtain ⟨hpw, htc, hsub', hCG'⟩ := hrest cs₁ cs₂ hG0 rfl rfl hsub hCG
    obtain ⟨hbw_rec, htc_rec⟩ := batchBodyAt_same_cost (U₁ := us₁) (U₂ := us₂)
      (cs₁ := compLSFStepSingle cs₁ u₁) (cs₂ := compLSFStepSingle cs₂ u₂)
      (by simp at hlen; exact hlen) hG0 hG' hsub' hCG' hr1 hr2
    have hlen1 : dgUpdateMemLen mem a = l₁ := dgUpdateMemLen_eq hu1
    refine ⟨fun C hC => ?_, ?_⟩
    · simp only [projBatchBodyWords, hpw C hC, hlen1, hbw_rec C hC]
    · rw [touchedCompsBatch_cons_uncond, touchedCompsBatch_cons_uncond, htc, htc_rec]
  | [], _ :: _, _, _, _, _, _, hlen, _, _, _, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, _, hlen, _, _, _, _, _, _ => by simp at hlen

/-- Amortized cost bound of `op 0`: at most `compBatchLsfMul * k * ∑_{touched edgeful} lsfBatchCost`
plus `compBatchUpdMul * k * (|U| + 1)`. -/
noncomputable def compBatchCost (k : ℕ) (S : CompLSFFamily k) (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  open Classical in
  if hk : 1 ≤ k then
    let b := args.getD 0 0
    let batchPtr := args.getD 1 0
    let L_w := mem (b + compOffLW)
    let cs0 := S ⟨0, hk⟩
    if h : ∃ U tw, BatchAt mem batchPtr cs0.G U tw then
      let U := h.choose
      compBatchLsfMul * k * sumTouchedLsfBatchCost mem cs0 batchPtr L_w U +
        compBatchUpdMul * k * (U.length + 1)
    else 0
  else 0

/-- Precondition of `op 1` (vertex component info `[b, v, heap]`). -/
def CompVertPre (w k : ℕ) (S : CompLSFFamily k) (args : List ℕ) : Prop :=
  ∃ (hk : 1 ≤ k) (b v heap : ℕ), args = [b, v, heap] ∧ 16 ≤ 2 ^ w ∧ v ∈ (S ⟨0, hk⟩).G.V

/-- Precondition of `op 2` (edgeful window handle readout `[b, c, j, heap]`). -/
def CompWinHandlePre (w k : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ b c j heap, args = [b, c, j, heap] ∧ 16 ≤ 2 ^ w ∧
    c < mem (b + compOffNumComps) ∧ mem (mem (b + compOffEdgefulPtr) + c) = 1 ∧ j < k

/-- Precondition of `op 3` (forest root readout `[b, j, v, heap]`). -/
def CompRootPre (w k : ℕ) (S : CompLSFFamily k) (args : List ℕ) : Prop :=
  ∃ (hk : 1 ≤ k) (b j v heap : ℕ), args = [b, j, v, heap] ∧ 16 ≤ 2 ^ w ∧ j < k ∧
    v ∈ (S ⟨0, hk⟩).G.V

/-- Precondition of `op 4` (edge flags & `wstrGlobal` readout `[b, j, e, heap]`). -/
def CompEdgePre (w k : ℕ) (S : CompLSFFamily k) (args : List ℕ) : Prop :=
  ∃ (hk : 1 ≤ k) (b j e heap : ℕ), args = [b, j, e, heap] ∧ 16 ≤ 2 ^ w ∧ j < k ∧
    e ∈ (S ⟨0, hk⟩).G.E

/-- Precondition of `op 5` (global header readout `[b, heap]`). -/
def CompInfoPre (w k : ℕ) (args : List ℕ) : Prop :=
  ∃ b heap, args = [b, heap] ∧ 16 ≤ 2 ^ w ∧ k < 2 ^ w

/-- **The per-component dynamic LSF data-structure specification** (`DataStructure (CompLSFFamily k)`). -/
noncomputable def compLSFDS (W : LSFWindowImpl) (w k : ℕ) (G₀ : MGraph) :
    DataStructure (CompLSFFamily k) where
  initPre := CompInitPre W w k G₀
  initPost := CompInitPost W k G₀
  initCost args _ := compInitCost W k G₀ args
  initSpace args _ := compInitSpace W k G₀ args
  pre i S args mem := match i with
    | 0 => CompBatchPre w k S args mem
    | 1 => CompVertPre w k S args
    | 2 => CompWinHandlePre w k args mem
    | 3 => CompRootPre w k S args
    | 4 => CompEdgePre w k S args
    | 5 => CompInfoPre w k args
    | _ => False
  post i S args mem S' mem' := match i with
    | 0 => CompBatchPost k S args mem S' mem'
    | 1 => S' = S ∧ ∃ (hk : 1 ≤ k),
        let b := args.getD 0 0
        let v := args.getD 1 0
        let h := heapArg args
        let cs0 := S ⟨0, hk⟩
        ∃ C ∈ components cs0.G₀, v ∈ (cs0.compSt C).G.V ∧
          mem' h < mem (b + compOffNumComps) ∧
          mem' (h + 1) = (if 1 ≤ (compGraph cs0.G₀ C).m then 1 else 0) ∧
          mem' (h + 2) = (compGraph cs0.G₀ C).n ∧
          mem' (h + 3) = (compGraph cs0.G₀ C).m
    | 2 => S' = S ∧ ∃ (hj : args.getD 2 0 < k),
        let h := heapArg args
        let hWin := mem' h
        ∃ C ∈ edgefulComps (S ⟨args.getD 2 0, hj⟩).G₀, ∃ xWin,
          (LSFRep W.h).rep hWin ((S ⟨args.getD 2 0, hj⟩).compSt C) xWin mem'
    | 3 => S' = S ∧ ∃ (hj : args.getD 1 0 < k),
        mem' (heapArg args) = (S ⟨args.getD 1 0, hj⟩).RF.root (args.getD 2 0)
    | 4 => S' = S ∧ ∃ (hj : args.getD 1 0 < k),
        let b := args.getD 0 0
        let e := args.getD 2 0
        let h := heapArg args
        let L_w := mem (b + compOffLW)
        let cs := S ⟨args.getD 1 0, hj⟩
        mem' h = (if e ∈ cs.crossEdges then 1 else 0) ∧
        mem' (h + 1) = (if e ∈ cs.insertedGlobal then 1 else 0) ∧
        Valid mem' (mem' (h + 2)) W.h L_w ∧
        Valid mem' (mem' (h + 3)) W.h L_w ∧
        1 ≤ intVal mem' (mem' (h + 2)) W.h L_w ∧
        1 ≤ intVal mem' (mem' (h + 3)) W.h L_w ∧
        (intVal mem' (mem' (h + 2)) W.h L_w : ℝ) /
          (intVal mem' (mem' (h + 3)) W.h L_w : ℝ) = cs.wstrGlobal e
    | 5 => S' = S ∧
        let b := args.getD 0 0
        let h := heapArg args
        mem' h = mem (b + compOffNumComps) ∧
        mem' (h + 1) = mem (b + compOffNumEdgeful) ∧
        mem' (h + 2) = k ∧
        mem' (h + 3) = mem (b + compOffVCap) ∧
        mem' (h + 4) = mem (b + compOffECap) ∧
        mem' (h + 5) = mem (b + compOffLW)
    | _ => False
  cost i S args mem := match i with
    | 0 => compBatchCost k S args mem
    | 1 => 120
    | 2 => 80
    | 3 => 150
    | 4 => 180
    | 5 => 120
    | _ => 0
  space i _ args mem := match i with
    | 0 => compBatchSpace k args mem
    | 1 => 4
    | 2 => 1
    | 3 => 1
    | 4 => 4
    | 5 => 6
    | _ => 0

/-! ## 4. Cost-shape corollaries -/

/-- Exact cost-shape corollary for `op 0` (batch update): for any batch `U` stored via `BatchAt`,
the amortized cost bound is `compBatchLsfMul * k * ∑_{touched edgeful C} compProjLsfBatchCost +
compBatchUpdMul * k * (U.length + 1)`, with constants `5` and `800` independent of all inputs. -/
theorem compLSFDS_batchCost_eq (W : LSFWindowImpl) {w k b batchPtr heap totalWords : ℕ}
    {G₀ : MGraph} (hk : 1 ≤ k) {S : CompLSFFamily k} {mem : ℕ → ℕ} {U : List Update}
    (hsub : ∀ C ∈ components (S ⟨0, hk⟩).G₀, ((S ⟨0, hk⟩).compSt C).G.E ⊆ (S ⟨0, hk⟩).G.E)
    (hB : BatchAt mem batchPtr (S ⟨0, hk⟩).G U totalWords) :
    (compLSFDS W w k G₀).cost 0 S [b, batchPtr, heap] mem =
      compBatchLsfMul * k *
          sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr (mem (b + compOffLW)) U +
        compBatchUpdMul * k * (U.length + 1) := by
  have hex : ∃ U' tw', BatchAt mem batchPtr (S ⟨0, hk⟩).G U' tw' := ⟨U, totalWords, hB⟩
  simp only [compLSFDS, compBatchCost, hk, ↓reduceDIte, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, hex]
  obtain ⟨tw', hB'⟩ := hex.choose_spec
  have hlen : hex.choose.length = U.length := hB'.2.1.symm.trans hB.2.1
  obtain ⟨hbw, htc⟩ := batchBodyAt_same_cost hlen rfl (graphEq_refl _) hsub
    (fun _ _ => graphEq_refl _) hB'.2.2 hB.2.2
  rw [hlen]
  congr 2
  unfold sumTouchedLsfBatchCost compProjLsfBatchCost
  rw [htc]
  refine Finset.sum_congr rfl fun C hC => ?_
  have hCm : C ∈ components (S ⟨0, hk⟩).G₀ :=
    Finset.filter_subset _ _ (Finset.mem_filter.mp hC).1
  rw [hbw C hCm]

/-- Exact cost-shape corollary for `init`: isolated components (`m_C = 0`) incur zero window init
cost, and every edgeful component `C` pays only `W.winCost + k * O(n_C log n_C) + O(n_C + m_C)`. -/
theorem compLSFDS_initCost_eq (W : LSFWindowImpl) {w k g0Ptr lenArr L_w vCap eCap heap : ℕ}
    (mem : ℕ → ℕ) (G₀ : MGraph) :
    (compLSFDS W w k G₀).initCost [g0Ptr, lenArr, W.L_in, W.P_fp, k, L_w, vCap, eCap, heap] mem =
      compInitLinMul * (G₀.n + G₀.m + 1) +
        (edgefulComps G₀).sum fun C =>
          let nC := (compGraph G₀ C).n
          let mC := (compGraph G₀ C).m
          W.winCost k L_w nC mC +
            k * (3000 * (nC + 1) * (Nat.log 2 (nC + 2) + 1)) +
            compInitCompMul * (nC + mC + 1) := by
  simp only [compLSFDS, compInitCost, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

end

end MinCostFlow.SparseCore.Program
