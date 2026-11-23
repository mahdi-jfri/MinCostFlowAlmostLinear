module

public import MinCostFlow.SparseCore.Program.AssemblyModel
public import MinCostFlow.SparseCore.Program.AssemblyStatement
public import WordRAM.Logic

/-!
# Empty-graph dispatch for the sparse-core program (`AssemblyEmpty`)

When the initial graph `G₀` has no vertices (`G₀.V = ∅`, equivalently `G₀.n = 0`), the bundle tool
sets `st.isNonempty = false` and never updates its state (`asm_updateOrd_of_empty`), never restarts
(`restart st j = st`), and returns `emptyLSF`, `emptyGraph`, `fun _ => []`, and `fun _ => []` for
readouts `2`, `3`, `4`, and `5`.

This file handles the empty-graph case completely (Decision 7):
* `asmEmpty_inv`: along any `SparseCoreOrdInput` whose state has `isNonempty = false`, the current
  graph `G` has `G.V = ∅` and `G.E = ∅`, and `ord = fun _ => []`.
* Layout lemmas (`dynGraphAt_emptyGraph`, `lsfAt_emptyLSF`, `embReadoutAt_empty`,
  `smallBatchAt_empty`, `ordEditsAt_empty`, `ordListAt_empty`): a 4-word all-zero block represents
  `emptyGraph` at capacities `(0, 0)`, and a single zero word represents the empty batch, empty
  edits, and empty order list.
* `asmEmptyUpdateBody`: deterministic Word-RAM procedure (`[k, heap]`) that writes `BranchOutAt`
  with `k` empty entries (sharing one zero word at `heap + 1 + 4 * k`) and returns
  `heap + 2 + 4 * k` in at most `35 * k + 30` steps and `4 * k + 2` cells (`asmEmptyUpdateBody_runs`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

/-! ## Model invariants on an empty state -/

/-- A valid graph with `V = ∅` has `E = ∅`. -/
theorem empty_E_of_empty_V {G : MGraph} (hV : G.V = ∅) (hval : G.IsValid) : G.E = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  have hv := (hval e he).1
  rw [hV] at hv
  exact Finset.notMem_empty _ hv

/-- Any valid batch on an empty graph (`V = ∅`, `E = ∅`) must be `[]`, leaving `V = ∅` and `E = ∅`. -/
theorem applyBatch_empty_of_valid {G : MGraph} {U : List Update}
    (hV : G.V = ∅) (hE : G.E = ∅) (hU : G.BatchIsValid U) :
    U = [] ∧ (G.applyBatch U).V = ∅ ∧ (G.applyBatch U).E = ∅ := by
  cases U with
  | nil => exact ⟨rfl, hV, hE⟩
  | cons u us =>
    have hu := hU.1
    cases u with
    | insert e a b =>
      have ha := hu.2.1
      rw [hV] at ha
      exact absurd ha (Finset.notMem_empty _)
    | delete e =>
      unfold MGraph.UpdateIsValid at hu
      rw [hE] at hu
      exact absurd hu (Finset.notMem_empty _)
    | split v v' St Sh =>
      have hv := hu.1
      rw [hV] at hv
      exact absurd hv (Finset.notMem_empty _)

/-- Along any contract history `SparseCoreOrdInput`, if `st.isNonempty = false` then the current
input graph has `V = ∅` and `E = ∅`. -/
theorem asmEmpty_inv {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {params : ℕ → SparsifyParams} {spanConst : ℕ} {k M N : ℕ}
    {s : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (h : SparseCoreOrdInput (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N s G ord n)
    (hem : SparseCoreBundleState.isNonempty (L := L) s = false) :
    G.V = ∅ ∧ G.E = ∅ := by
  induction h with
  | init G₀ ℓ g ord hval _ _ _ _ =>
    have hnot : ¬ G₀.V.Nonempty := by
      have hdec : decide G₀.V.Nonempty = false := hem
      exact of_decide_eq_false hdec
    have hV : G₀.V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    exact ⟨hV, empty_E_of_empty_V hV hval⟩
  | @update s₀ G₀ ord₀ n₀ h_in U ℓ g ord' hU _ _ _ ih =>
    have hem₀ : SparseCoreBundleState.isNonempty (L := L) s₀ = false := by
      by_cases hne : SparseCoreBundleState.isNonempty (L := L) s₀ = true
      · rw [asm_updateOrd_of_nonempty lsfInit C_lsst L sparsify params spanConst s₀ hne] at hem
        simp only [hne] at hem
        exact Bool.noConfusion hem
      · exact Bool.eq_false_iff.mpr hne
    obtain ⟨hV, hE⟩ := ih hem₀
    obtain ⟨_, hV', hE'⟩ := applyBatch_empty_of_valid hV hE hU
    exact ⟨hV', hE'⟩
  | @restart s₀ G₀ ord₀ n₀ h_in j _ ih =>
    have hR := sparseCoreBundleRestartTool_restart_eq lsfInit C_lsst L sparsify s₀ j
    have hem₀ : SparseCoreBundleState.isNonempty (L := L) s₀ = false := by
      change (if SparseCoreBundleState.isNonempty (L := L) s₀ = true then _ else s₀).isNonempty =
        false at hem
      by_cases hne : SparseCoreBundleState.isNonempty (L := L) s₀ = true
      · simp only [hne, ↓reduceIte] at hem; exact Bool.noConfusion hem
      · exact Bool.eq_false_iff.mpr hne
    exact ih hem₀

/-! ## Empty-structure layout lemmas -/

/-- Four zero words at address `a` represent `emptyGraph` with capacities `vCap = 0`, `eCap = 0`. -/
theorem dynGraphAt_emptyGraph {mem : ℕ → ℕ} {a : ℕ}
    (h0 : mem a = 0) (h1 : mem (a + 1) = 0) (h2 : mem (a + 2) = 0) (h3 : mem (a + 3) = 0) :
    DynGraphAt mem a 0 0 emptyGraph := by
  refine ⟨fun _ h => by simp [emptyGraph] at h,
    fun _ h => by simp [emptyGraph] at h,
    fun _ h => by simp [emptyGraph] at h,
    h0, h1, h2, h3,
    fun _ hv => absurd hv (Nat.not_lt_zero _),
    ⟨[], rfl, List.nodup_nil, fun _ => by simp [emptyGraph], listAt_nil _ _, fun _ hi => by simp at hi⟩,
    fun _ hv => by simp [emptyGraph] at hv,
    fun _ hv => by simp [emptyGraph] at hv,
    fun _ he => absurd he (Nat.not_lt_zero _),
    ⟨[], rfl, List.nodup_nil, fun _ => by simp [emptyGraph], listAt_nil _ _, fun _ hi => by simp at hi⟩,
    fun _ he => by simp [emptyGraph] at he,
    ⟨fun _ => [], fun _ hv => absurd hv (Nat.not_lt_zero _)⟩⟩

/-- `[vCap, eCap]` followed by zeros across `[a + 2, a + dynGraphSize vCap eCap)` represents
`emptyGraph` with exact capacities `(vCap, eCap)`. -/
theorem dynGraphAt_emptyGraph_cap {mem : ℕ → ℕ} {a vCap eCap : ℕ}
    (h0 : mem a = vCap) (h1 : mem (a + 1) = eCap)
    (hz : ∀ k, 2 ≤ k → k < dynGraphSize vCap eCap → mem (a + k) = 0) :
    DynGraphAt mem a vCap eCap emptyGraph := by
  have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  refine ⟨fun _ h => by simp [emptyGraph] at h,
    fun _ h => by simp [emptyGraph] at h,
    fun _ h => by simp [emptyGraph] at h,
    h0, h1, hz 2 (by omega) (by omega), hz 3 (by omega) (by omega),
    fun v hv => by
      simp only [emptyGraph, Finset.notMem_empty, ↓reduceIte, dgVPresBase]
      simpa [Nat.add_assoc] using hz (4 + v) (by omega) (by omega),
    ⟨[], rfl, List.nodup_nil, fun _ => by simp [emptyGraph], listAt_nil _ _, fun _ hi => by simp at hi⟩,
    fun _ hv => by simp [emptyGraph] at hv,
    fun _ hv => by simp [emptyGraph] at hv,
    fun e he => by
      simp only [emptyGraph, Finset.notMem_empty, ↓reduceIte, dgEPresBase]
      simpa [Nat.add_assoc] using hz (4 + 7 * vCap + e) (by omega) (by omega),
    ⟨[], rfl, List.nodup_nil, fun _ => by simp [emptyGraph], listAt_nil _ _, fun _ hi => by simp at hi⟩,
    fun _ he => by simp [emptyGraph] at he,
    ⟨fun _ => [], fun s hs => ⟨⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim,
      by simp only [dgIncHeadBase]; simpa [Nat.add_assoc] using hz (4 + 6 * vCap + s) (by omega) (by omega),
      fun _ hi => by simp at hi⟩,
      by simp only [dgSlotDegBase, List.length_nil]
         simpa [Nat.add_assoc] using hz (4 + 5 * vCap + s) (by omega) (by omega),
      fun h => by simp [emptyGraph]⟩⟩⟩

/-- When `mem a = mem (a + 1) = mem (a + 2) = mem (a + 3) = 0` and `mem h = a`, `mem (h + 1) = a`,
`LSFAt` holds for `emptyLSF` on `E = ∅` at any limb width `L` and precision `P`. -/
theorem lsfAt_emptyLSF {mem : ℕ → ℕ} {h a hBits L P : ℕ}
    (hg : DynGraphAt mem a 0 0 emptyGraph)
    (h0 : mem h = a) (h1 : mem (h + 1) = a) :
    LSFAt mem h 0 0 hBits L P ∅ emptyLSF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0]; exact hg
  · rw [h1]; exact hg
  · exact ⟨fun _ hv => absurd hv (Finset.notMem_empty _), fun _ hv => absurd hv (Nat.not_lt_zero _)⟩
  · intro e he; exact absurd he (Finset.notMem_empty _)

/-- `EmbeddingReadoutAt` holds trivially on any graph `G` with `G.E = ∅`. -/
theorem embReadoutAt_empty {mem : ℕ → ℕ} {h : ℕ} {G : MGraph} (hE : G.E = ∅) :
    EmbeddingReadoutAt mem h 0 G emptyLSF (fun _ => []) := by
  intro e he
  have hsub : e ∈ G.E := (Finset.mem_sdiff.mp he).1
  rw [hE] at hsub
  exact absurd hsub (Finset.notMem_empty _)

/-- A single zero word at `a` represents the empty batch `[]` on any graph in `1` word. -/
theorem smallBatchAt_empty {mem : ℕ → ℕ} {a : ℕ} (G : MGraph) (h0 : mem a = 0) :
    SmallBatchAt mem a G [] 1 :=
  ⟨⟨le_rfl, h0, rfl⟩, by simp [MGraph.batchEnc]⟩

/-- A single zero word at `a` represents the empty edit list `[]` in `1` word. -/
theorem ordEditsAt_empty {mem : ℕ → ℕ} {a : ℕ} (h0 : mem a = 0) :
    OrdEditsAt mem a [] 1 :=
  ⟨by simp [readOrdEdits, h0, decodeOrdEdits],
   by simp [h0, decodeOrdEdits],
   by simp [ordEditsEnc]⟩

/-- A single zero word at `a` represents the empty order `fun _ => []` in `1` word. -/
theorem ordListAt_empty {mem : ℕ → ℕ} {a : ℕ} (h0 : mem a = 0) :
    OrdListAt mem a (fun _ => []) 1 :=
  ⟨by simp [readOrdRecordsAt, h0, readOrdRecords],
   by funext u; simp [readOrd, readOrdRecordsAt, h0, readOrdRecords, ordOfRecords],
   by simp [readOrdRecordsAt, h0, readOrdRecords, ordRecordsWords]⟩

/-! ## Empty-graph `op 0` output writer -/

/-- Procedure body for empty-graph `op 0`, called as `[k, heap]`:
* writes `mem[heap] = k`;
* sets `fChgPtr = heap + 2 + 6 * k`, writes `mem[heap + 1 + 6 * k] = fChgPtr`, sets
  `ePtr = fChgPtr + k = heap + 2 + 7 * k` (where `mem[ePtr] = mem[ePtr + 1] = 0` by `ZeroFrom`),
  and sets `rSlotBase = heap + 1 + 4 * k`;
* for `j = 0 .. k - 1`, writes `[ePtr, 1, ePtr, 1]` at `heap + 1 + 4 * j .. heap + 4 + 4 * j`,
  writes `mem[fChgPtr + j] = ePtr` (pointing to the 2-word empty `LSFChangeAt` record), and writes
  `mem[rSlotBase + 2 * j] = ePtr` (leaving length word `mem[rSlotBase + 2 * j + 1] = 0`, so every
  empty re-embedding list `[ePtr, 0]` lies inside `[heap, heap + 7 * k + 4)`);
* returns `ePtr + 2 = heap + 4 + 7 * k`. -/
def asmEmptyUpdateBody : Stmt :=
  .store (.reg 1) (.reg 0) ;;
  .assign 5 (.bin .add (.bin .add (.reg 1) (.const 2)) (.bin .mul (.const 6) (.reg 0))) ;;
  .store (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 6) (.reg 0))) (.reg 5) ;;
  .assign 2 (.bin .add (.reg 5) (.reg 0)) ;;
  .assign 6 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 4) (.reg 0))) ;;
  forRange 3 (.const 0) (.reg 0)
    (.assign 4 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 4) (.reg 3))) ;;
     .store (.reg 4) (.reg 2) ;;
     .store (.bin .add (.reg 4) (.const 1)) (.const 1) ;;
     .store (.bin .add (.reg 4) (.const 2)) (.reg 2) ;;
     .store (.bin .add (.reg 4) (.const 3)) (.const 1) ;;
     .store (.bin .add (.reg 5) (.reg 3)) (.reg 2) ;;
     .store (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 3))) (.reg 2)) ;;
  .ret (.bin .add (.reg 2) (.const 2))

theorem asmEmptyUpdateBody_noRand : asmEmptyUpdateBody.NoRand := by
  simp [asmEmptyUpdateBody, forRange, forUp, Stmt.NoRand]

private def emptyMem6 (mem : ℕ → ℕ) (base fChg rSlot ePtr : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update mem base ePtr) (base + 1) 1) (base + 2) ePtr) (base + 3) 1)
    fChg ePtr) rSlot ePtr

private theorem empty_mem6_other {mem : ℕ → ℕ} {base fChg rSlot ePtr a : ℕ}
    (ha : a < base ∨ base + 4 ≤ a) (hneF : a ≠ fChg) (hneR : a ≠ rSlot) :
    emptyMem6 mem base fChg rSlot ePtr a = mem a := by
  unfold emptyMem6
  rw [Function.update_of_ne hneR, Function.update_of_ne hneF, Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega)]

private theorem empty_mem6_self {mem : ℕ → ℕ} {base fChg rSlot ePtr : ℕ}
    (hbr : base + 4 ≤ rSlot) (hrf : rSlot < fChg) :
    let m := emptyMem6 mem base fChg rSlot ePtr
    m base = ePtr ∧ m (base + 1) = 1 ∧ m (base + 2) = ePtr ∧ m (base + 3) = 1 ∧
      m fChg = ePtr ∧ m rSlot = ePtr := by
  unfold emptyMem6
  refine ⟨?_, ?_, ?_, ?_, ?_, Function.update_self _ _ _⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_self]

private theorem empty_mem6_prev {mem : ℕ → ℕ} {heap k i j ePtr : ℕ}
    (hlt : j < i) (hi : i < k)
    (hpj : mem (heap + 1 + 4 * j) = ePtr ∧ mem (heap + 2 + 4 * j) = 1 ∧
      mem (heap + 3 + 4 * j) = ePtr ∧ mem (heap + 4 + 4 * j) = 1 ∧
      mem (heap + 2 + 6 * k + j) = ePtr ∧ mem (heap + 1 + 4 * k + 2 * j) = ePtr) :
    let base := heap + 1 + 4 * i
    let fChg := heap + 2 + 6 * k + i
    let rSlot := heap + 1 + 4 * k + 2 * i
    let m := emptyMem6 mem base fChg rSlot ePtr
    m (heap + 1 + 4 * j) = ePtr ∧ m (heap + 2 + 4 * j) = 1 ∧
      m (heap + 3 + 4 * j) = ePtr ∧ m (heap + 4 + 4 * j) = 1 ∧
      m (heap + 2 + 6 * k + j) = ePtr ∧ m (heap + 1 + 4 * k + 2 * j) = ePtr := by
  intro base fChg rSlot m
  have h1 : heap + 1 + 4 * j < base := by omega
  have h2 : heap + 2 + 4 * j < base := by omega
  have h3 : heap + 3 + 4 * j < base := by omega
  have h4 : heap + 4 + 4 * j < base := by omega
  have h5 : base + 4 ≤ heap + 2 + 6 * k + j := by omega
  have h6 : base + 4 ≤ heap + 1 + 4 * k + 2 * j := by omega
  exact ⟨(empty_mem6_other (Or.inl h1) (by omega) (by omega)).trans hpj.1,
    (empty_mem6_other (Or.inl h2) (by omega) (by omega)).trans hpj.2.1,
    (empty_mem6_other (Or.inl h3) (by omega) (by omega)).trans hpj.2.2.1,
    (empty_mem6_other (Or.inl h4) (by omega) (by omega)).trans hpj.2.2.2.1,
    (empty_mem6_other (Or.inr h5) (by omega) (by omega)).trans hpj.2.2.2.2.1,
    (empty_mem6_other (Or.inr h6) (by omega) (by omega)).trans hpj.2.2.2.2.2⟩

private theorem asmEmptyUpdateLoop_body {w k heap i : ℕ} {p : Program} {st : State} {ω : ℕ → Bool}
    (hw : 6 < 2 ^ w) (hsp : heap + (7 * k + 4) < 2 ^ w) (hilt : i < k)
    (h1 : st.regs 1 = heap) (h2 : st.regs 2 = heap + 2 + 7 * k) (h3 : st.regs 3 = i)
    (h5 : st.regs 5 = heap + 2 + 6 * k) (h6 : st.regs 6 = heap + 1 + 4 * k) :
    let base := heap + 1 + 4 * i
    let fChgPtr := heap + 2 + 6 * k
    let ePtr := heap + 2 + 7 * k
    let rSlot := heap + 1 + 4 * k + 2 * i
    ∃ c, Runs w p ω
        (.assign 4 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 4) (.reg 3))) ;;
          .store (.reg 4) (.reg 2) ;;
          .store (.bin .add (.reg 4) (.const 1)) (.const 1) ;;
          .store (.bin .add (.reg 4) (.const 2)) (.reg 2) ;;
          .store (.bin .add (.reg 4) (.const 3)) (.const 1) ;;
          .store (.bin .add (.reg 5) (.reg 3)) (.reg 2) ;;
          .store (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 3))) (.reg 2))
        st .normal ⟨emptyMem6 st.mem base (fChgPtr + i) rSlot ePtr, Function.update st.regs 4 base,
          st.pos⟩ c ∧ c ≤ 50 := by
  intro base fChgPtr ePtr rSlot
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have ha4 : (Expr.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 4) (.reg 3))).eval w st =
      some base :=
    Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h1) (Expr.eval_const h1w) (by omega))
      (Expr.eval_mul (Expr.eval_const h4w) (Expr.eval_reg_of_eq h3) (by omega)) (by omega)
  let regs1 := Function.update st.regs 4 base
  have hr4 : regs1 4 = base := Function.update_self 4 base st.regs
  have hr2 : regs1 2 = ePtr := (Function.update_of_ne (by decide) base st.regs).trans h2
  have hr3 : regs1 3 = i := (Function.update_of_ne (by decide) base st.regs).trans h3
  have hr5 : regs1 5 = fChgPtr := (Function.update_of_ne (by decide) base st.regs).trans h5
  have hr6 : regs1 6 = heap + 1 + 4 * k := (Function.update_of_ne (by decide) base st.regs).trans h6
  let m1 := Function.update st.mem base ePtr
  let m2 := Function.update m1 (base + 1) 1
  let m3 := Function.update m2 (base + 2) ePtr
  let m4 := Function.update m3 (base + 3) 1
  let m5 := Function.update m4 (fChgPtr + i) ePtr
  let s1 : State := ⟨st.mem, regs1, st.pos⟩
  let s2 : State := ⟨m1, regs1, st.pos⟩
  let s3 : State := ⟨m2, regs1, st.pos⟩
  let s4 : State := ⟨m3, regs1, st.pos⟩
  let s5 : State := ⟨m4, regs1, st.pos⟩
  let s6 : State := ⟨m5, regs1, st.pos⟩
  have r1 : Runs w p ω (.assign 4 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 4) (.reg 3))))
      st .normal s1 _ := runs_assign_iff.mpr ⟨base, ha4, rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.store (.reg 4) (.reg 2)) s1 .normal s2 _ :=
    runs_store_iff.mpr ⟨base, ePtr, Expr.eval_reg_of_eq hr4, Expr.eval_reg_of_eq hr2, rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.store (.bin .add (.reg 4) (.const 1)) (.const 1)) s2 .normal s3 _ :=
    runs_store_iff.mpr ⟨base + 1, 1, Expr.eval_add (Expr.eval_reg_of_eq hr4) (Expr.eval_const h1w) (by omega),
      Expr.eval_const h1w, rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.store (.bin .add (.reg 4) (.const 2)) (.reg 2)) s3 .normal s4 _ :=
    runs_store_iff.mpr ⟨base + 2, ePtr, Expr.eval_add (Expr.eval_reg_of_eq hr4) (Expr.eval_const h2w) (by omega),
      Expr.eval_reg_of_eq hr2, rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.store (.bin .add (.reg 4) (.const 3)) (.const 1)) s4 .normal s5 _ :=
    runs_store_iff.mpr ⟨base + 3, 1, Expr.eval_add (Expr.eval_reg_of_eq hr4) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_const h1w, rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.store (.bin .add (.reg 5) (.reg 3)) (.reg 2)) s5 .normal s6 _ :=
    runs_store_iff.mpr ⟨fChgPtr + i, ePtr, Expr.eval_add (Expr.eval_reg_of_eq hr5) (Expr.eval_reg_of_eq hr3) (by omega),
      Expr.eval_reg_of_eq hr2, rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.store (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 3))) (.reg 2))
      s6 .normal ⟨emptyMem6 st.mem base (fChgPtr + i) rSlot ePtr, regs1, st.pos⟩ _ :=
    runs_store_iff.mpr ⟨rSlot, ePtr,
      Expr.eval_add (Expr.eval_reg_of_eq hr6) (Expr.eval_mul (Expr.eval_const h2w) (Expr.eval_reg_of_eq hr3) (by omega)) (by omega),
      Expr.eval_reg_of_eq hr2, rfl, rfl, rfl⟩
  refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨s1, _, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, _, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, _, _, r3,
        runs_seq_iff.mpr (Or.inr ⟨s4, _, _, r4,
          runs_seq_iff.mpr (Or.inr ⟨s5, _, _, r5,
            runs_seq_iff.mpr (Or.inr ⟨s6, _, _, r6, r7, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by simp [Expr.size]⟩

private theorem asmEmptyUpdateLoop_triple {w k heap : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 6 < 2 ^ w) (hsp : heap + (7 * k + 4) < 2 ^ w) :
    let fChgPtr := heap + 2 + 6 * k
    let ePtr := heap + 2 + 7 * k
    let rSlotBase := heap + 1 + 4 * k
    Triple w p
      (fun st => st.regs 0 = k ∧ st.regs 1 = heap ∧ st.regs 2 = ePtr ∧ st.regs 5 = fChgPtr ∧
        st.regs 6 = rSlotBase ∧ st.mem heap = k ∧ st.mem (heap + 1 + 6 * k) = fChgPtr ∧
        (∀ a < heap, st.mem a = mem₀ a) ∧
        (∀ a, heap + 1 ≤ a → a ≠ heap + 1 + 6 * k → st.mem a = 0))
      (forRange 3 (.const 0) (.reg 0)
        (.assign 4 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 4) (.reg 3))) ;;
         .store (.reg 4) (.reg 2) ;;
         .store (.bin .add (.reg 4) (.const 1)) (.const 1) ;;
         .store (.bin .add (.reg 4) (.const 2)) (.reg 2) ;;
         .store (.bin .add (.reg 4) (.const 3)) (.const 1) ;;
         .store (.bin .add (.reg 5) (.reg 3)) (.reg 2) ;;
         .store (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 3))) (.reg 2)))
      (normalPost fun st' =>
        st'.regs 0 = k ∧ st'.regs 1 = heap ∧ st'.regs 2 = ePtr ∧ st'.regs 5 = fChgPtr ∧
        st'.regs 6 = rSlotBase ∧ st'.mem heap = k ∧ st'.mem (heap + 1 + 6 * k) = fChgPtr ∧
        (∀ j < k, st'.mem (heap + 1 + 4 * j) = ePtr ∧
          st'.mem (heap + 2 + 4 * j) = 1 ∧
          st'.mem (heap + 3 + 4 * j) = ePtr ∧
          st'.mem (heap + 4 + 4 * j) = 1 ∧
          st'.mem (fChgPtr + j) = ePtr ∧
          st'.mem (rSlotBase + 2 * j) = ePtr) ∧
        (∀ a < heap, st'.mem a = mem₀ a) ∧
        (∀ j < k, st'.mem (heap + 2 + 4 * k + 2 * j) = 0) ∧
        ZeroFrom st'.mem ePtr)
      (fun _ => 60 * k + 20) := by
  intro fChgPtr ePtr rSlotBase
  have hfChg_w : fChgPtr < 2 ^ w := by omega
  have hePtr_w : ePtr < 2 ^ w := by omega
  have hrBase_w : rSlotBase < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 3) (lo := .const 0) (hi := .reg 0)
    (body := .assign 4 (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 4) (.reg 3))) ;;
      .store (.reg 4) (.reg 2) ;;
      .store (.bin .add (.reg 4) (.const 1)) (.const 1) ;;
      .store (.bin .add (.reg 4) (.const 2)) (.reg 2) ;;
      .store (.bin .add (.reg 4) (.const 3)) (.const 1) ;;
      .store (.bin .add (.reg 5) (.reg 3)) (.reg 2) ;;
      .store (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 3))) (.reg 2))
    (P := fun st => st.regs 0 = k ∧ st.regs 1 = heap ∧ st.regs 2 = ePtr ∧ st.regs 5 = fChgPtr ∧
      st.regs 6 = rSlotBase ∧ st.mem heap = k ∧ st.mem (heap + 1 + 6 * k) = fChgPtr ∧
      (∀ a < heap, st.mem a = mem₀ a) ∧
      (∀ a, heap + 1 ≤ a → a ≠ heap + 1 + 6 * k → st.mem a = 0))
    (Inv := fun i st => st.regs 0 = k ∧ st.regs 1 = heap ∧ st.regs 2 = ePtr ∧ st.regs 3 = i ∧
      st.regs 5 = fChgPtr ∧ st.regs 6 = rSlotBase ∧
      st.mem heap = k ∧ st.mem (heap + 1 + 6 * k) = fChgPtr ∧
      (∀ j < i, st.mem (heap + 1 + 4 * j) = ePtr ∧
        st.mem (heap + 2 + 4 * j) = 1 ∧
        st.mem (heap + 3 + 4 * j) = ePtr ∧
        st.mem (heap + 4 + 4 * j) = 1 ∧
        st.mem (fChgPtr + j) = ePtr ∧
        st.mem (rSlotBase + 2 * j) = ePtr) ∧
      (∀ a < heap, st.mem a = mem₀ a) ∧
      (∀ j < k, st.mem (heap + 2 + 4 * k + 2 * j) = 0) ∧
      ZeroFrom st.mem ePtr)
    50 0 k (Nat.zero_le k) h1w (fun _ => by omega)
    (fun st hst => by
      rcases hst with ⟨h0, h1, h2, h5, h6, hmk, hmf, hlt, hz1⟩
      refine ⟨Expr.eval_const (by omega), ?_, ?_, ?_, ?_, ?_, ?_, hmk, hmf,
        fun j hj => absurd hj (Nat.not_lt_zero _), hlt,
        fun j hj => hz1 _ (by omega) (by omega),
        fun a ha => hz1 a (by omega) (by omega)⟩
      · simp [h0]
      · simp [h1]
      · simp [h2]
      · simp
      · simp [h5]
      · simp [h6])
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => Expr.eval_reg_of_eq hi.1)
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h2, h3, h5, h6, hmk, hmf, hprev, hlt, hzr, hze⟩
      set base := heap + 1 + 4 * i
      set rSlot := rSlotBase + 2 * i
      let regs1 := Function.update st.regs 4 base
      have hr2 : regs1 2 = ePtr := (Function.update_of_ne (by decide) base st.regs).trans h2
      have hr3 : regs1 3 = i := (Function.update_of_ne (by decide) base st.regs).trans h3
      have hr5 : regs1 5 = fChgPtr := (Function.update_of_ne (by decide) base st.regs).trans h5
      have hr6 : regs1 6 = rSlotBase := (Function.update_of_ne (by decide) base st.regs).trans h6
      obtain ⟨cBody, rAll, hcBody⟩ := asmEmptyUpdateLoop_body (ω := ω) hw hsp hilt h1 h2 h3 h5 h6
      have hreg_out : Function.update regs1 3 (i + 1) 0 = k ∧
          Function.update regs1 3 (i + 1) 1 = heap ∧
          Function.update regs1 3 (i + 1) 2 = ePtr ∧
          Function.update regs1 3 (i + 1) 3 = i + 1 ∧
          Function.update regs1 3 (i + 1) 5 = fChgPtr ∧
          Function.update regs1 3 (i + 1) 6 = rSlotBase := by
        refine ⟨?_, ?_, ?_, Function.update_self _ _ _, ?_, ?_⟩
        · rw [Function.update_of_ne (by decide)]; dsimp only [regs1]; rw [Function.update_of_ne (by decide)]; exact h0
        · rw [Function.update_of_ne (by decide)]; dsimp only [regs1]; rw [Function.update_of_ne (by decide)]; exact h1
        · rw [Function.update_of_ne (by decide)]; exact hr2
        · rw [Function.update_of_ne (by decide)]; exact hr5
        · rw [Function.update_of_ne (by decide)]; exact hr6
      refine ⟨.normal, ⟨emptyMem6 st.mem base (fChgPtr + i) rSlot ePtr, regs1, st.pos⟩, cBody, rAll,
        ⟨⟨hreg_out.1, hreg_out.2.1, hreg_out.2.2.1, hreg_out.2.2.2.1, hreg_out.2.2.2.2.1,
          hreg_out.2.2.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩, hr3⟩, hcBody⟩
      · dsimp only; rw [empty_mem6_other (Or.inl (by omega)) (by omega) (by omega)]; exact hmk
      · dsimp only; rw [empty_mem6_other (Or.inr (by omega)) (by omega) (by omega)]; exact hmf
      · intro j hj
        by_cases hji : j = i
        · subst hji
          have hb0 : heap + 1 + 4 * j = base := rfl
          have hb1 : heap + 2 + 4 * j = base + 1 := by omega
          have hb2 : heap + 3 + 4 * j = base + 2 := by omega
          have hb3 : heap + 4 + 4 * j = base + 3 := by omega
          dsimp only; rw [hb0, hb1, hb2, hb3]
          exact empty_mem6_self (by omega) (by omega)
        · exact empty_mem6_prev (by omega) hilt (hprev j (by omega))
      · intro a ha
        dsimp only; rw [empty_mem6_other (Or.inl (by omega)) (by omega) (by omega)]; exact hlt a ha
      · intro j hj
        dsimp only; rw [empty_mem6_other (Or.inr (by omega)) (by omega) (by omega)]; exact hzr j hj
      · intro a ha
        dsimp only; rw [empty_mem6_other (Or.inr (by omega)) (by omega) (by omega)]; exact hze a ha )
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' h
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨h0, h1, h2, _, h5, h6, hmk, hmf, hbr, hlt, hzr, hze⟩
      exact ⟨h0, h1, h2, h5, h6, hmk, hmf, hbr, hlt, hzr, hze⟩
  · intro _ _
    simp [Expr.size]; omega

/-- Execution of `asmEmptyUpdateBody` on `[k, heap]`: writes `BranchOutAt` with `k` empty
branches (empty batch `[]`, empty edits `[]`, empty graphs, empty rotations), `reembList` slots
`[heap + 2 + 7 * k, 0]` at `heap + 1 + 4 * k .. heap + 6 * k` (inside `[heap, heap + 7 * k + 4)`),
and the `fChgPtr` table at `heap + 1 + 6 * k` pointing to `k` copies of the 2-word empty
`LSFChangeAt` record at `heap + 2 + 7 * k`; leaves memory below `heap` unchanged and memory from
`heap + 7 * k + 4` zero, and costs at most `60 * k + 75`. -/
theorem asmEmptyUpdateBody_runs {w k heap pos : ℕ} {p : Program} (ω : ℕ → Bool) {mem : ℕ → ℕ}
    (hw : 6 < 2 ^ w) (hsp : heap + (7 * k + 4) < 2 ^ w) (hz : ZeroFrom mem heap) :
    ∃ o st' c,
      Runs w p ω asmEmptyUpdateBody (startState [k, heap] mem pos) o st' c ∧
      o.value = heap + 7 * k + 4 ∧
      BranchOutAt st'.mem heap k (fun _ => emptyGraph) (fun _ => []) (fun _ _ => []) (fun _ _ => []) ∧
      st'.mem (heap + 1 + 6 * k) = heap + 2 + 6 * k ∧
      (∀ j < k, st'.mem (heap + 2 + 6 * k + j) = heap + 2 + 7 * k) ∧
      (∀ j < k, st'.mem (heap + 1 + 4 * j) = heap + 2 + 7 * k ∧
        st'.mem (heap + 2 + 4 * j) = 1 ∧
        st'.mem (heap + 3 + 4 * j) = heap + 2 + 7 * k ∧
        st'.mem (heap + 4 + 4 * j) = 1) ∧
      (∀ j < k, st'.mem (heap + 1 + 4 * k + 2 * j) = heap + 2 + 7 * k ∧
        st'.mem (heap + 2 + 4 * k + 2 * j) = 0) ∧
      (∀ j < k, readOrdEdits st'.mem (st'.mem (heap + 3 + 4 * j)) = []) ∧
      (∀ j < k, readList st'.mem (st'.mem (heap + 1 + 4 * k + 2 * j))
        (st'.mem (heap + 2 + 4 * k + 2 * j)) = []) ∧
      (∀ a < heap, st'.mem a = mem a) ∧
      ZeroFrom st'.mem (heap + 2 + 7 * k) ∧
      ZeroFrom st'.mem (heap + 7 * k + 4) ∧
      c ≤ 60 * k + 75 := by
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  set fChgPtr := heap + 2 + 6 * k
  set ePtr := heap + 2 + 7 * k
  set rSlotBase := heap + 1 + 4 * k
  have hk_w : k < 2 ^ w := by omega
  have hheap_w : heap < 2 ^ w := by omega
  have hfChg_w : fChgPtr < 2 ^ w := by omega
  have hePtr_w : ePtr < 2 ^ w := by omega
  have hrBase_w : rSlotBase < 2 ^ w := by omega
  have hmain : ∃ o st' c,
      Runs w p ω asmEmptyUpdateBody (startState [k, heap] mem pos) o st' c ∧
      (o.value = heap + 7 * k + 4 ∧
        BranchOutAt st'.mem heap k (fun _ => emptyGraph) (fun _ => []) (fun _ _ => []) (fun _ _ => []) ∧
        st'.mem (heap + 1 + 6 * k) = fChgPtr ∧
        (∀ j < k, st'.mem (fChgPtr + j) = ePtr) ∧
        (∀ j < k, st'.mem (heap + 1 + 4 * j) = ePtr ∧
          st'.mem (heap + 2 + 4 * j) = 1 ∧
          st'.mem (heap + 3 + 4 * j) = ePtr ∧
          st'.mem (heap + 4 + 4 * j) = 1) ∧
        (∀ j < k, st'.mem (rSlotBase + 2 * j) = ePtr ∧
          st'.mem (heap + 2 + 4 * k + 2 * j) = 0) ∧
        (∀ j < k, readOrdEdits st'.mem (st'.mem (heap + 3 + 4 * j)) = []) ∧
        (∀ j < k, readList st'.mem (st'.mem (heap + 1 + 4 * k + 2 * j))
          (st'.mem (heap + 2 + 4 * k + 2 * j)) = []) ∧
        (∀ a < heap, st'.mem a = mem a) ∧
        ZeroFrom st'.mem ePtr ∧
        ZeroFrom st'.mem (heap + 7 * k + 4)) ∧
      c ≤ 60 * k + 75 := by
    refine runs_start_le ?_
    unfold asmEmptyUpdateBody
    refine runs_seq_store_le
      (Expr.eval_reg_of_eq (v := heap) (by simp [startState]))
      (Expr.eval_reg_of_eq (v := k) (by simp [startState])) ?_
    set st1 : State := { startState [k, heap] mem pos with mem := Function.update mem heap k }
    have ha5 : (Expr.bin .add (.bin .add (.reg 1) (.const 2)) (.bin .mul (.const 6) (.reg 0))).eval w st1 =
        some fChgPtr := by
      have h6k : (Expr.bin .mul (.const 6) (.reg 0)).eval w st1 = some (6 * k) :=
        Expr.eval_mul (Expr.eval_const hw) (Expr.eval_reg_of_eq (by simp [st1, startState])) (by omega)
      have h12 : (Expr.bin .add (.reg 1) (.const 2)).eval w st1 = some (heap + 2) :=
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [st1, startState])) (Expr.eval_const h2w) (by omega)
      exact Expr.eval_add h12 h6k (by omega)
    refine runs_seq_assign_le ha5 ?_
    set st2 : State := { st1 with regs := Function.update st1.regs 5 fChgPtr }
    have hsf : (Expr.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 6) (.reg 0))).eval w st2 =
        some (heap + 1 + 6 * k) := by
      have h6k : (Expr.bin .mul (.const 6) (.reg 0)).eval w st2 = some (6 * k) :=
        Expr.eval_mul (Expr.eval_const hw) (Expr.eval_reg_of_eq (by simp [st2, st1, startState])) (by omega)
      have h11 : (Expr.bin .add (.reg 1) (.const 1)).eval w st2 = some (heap + 1) :=
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, st1, startState])) (Expr.eval_const h1w) (by omega)
      exact Expr.eval_add h11 h6k (by omega)
    refine runs_seq_store_le hsf (Expr.eval_reg_of_eq (v := fChgPtr) (Function.update_self 5 fChgPtr st1.regs)) ?_
    set st3 : State := { st2 with mem := Function.update st2.mem (heap + 1 + 6 * k) fChgPtr }
    have ha2 : (Expr.bin .add (.reg 5) (.reg 0)).eval w st3 = some ePtr := by
      have hval : fChgPtr + k = ePtr := by omega
      rw [← hval]
      exact Expr.eval_add (Expr.eval_reg_of_eq (v := fChgPtr) (by simp [st3, st2]))
        (Expr.eval_reg_of_eq (v := k) (by simp [st3, st2, st1, startState])) (by omega)
    refine runs_seq_assign_le ha2 ?_
    set st4 : State := { st3 with regs := Function.update st3.regs 2 ePtr }
    have ha6 : (Expr.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 4) (.reg 0))).eval w st4 =
        some rSlotBase := by
      have h4k : (Expr.bin .mul (.const 4) (.reg 0)).eval w st4 = some (4 * k) :=
        Expr.eval_mul (Expr.eval_const h4w) (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, startState])) (by omega)
      have h11 : (Expr.bin .add (.reg 1) (.const 1)).eval w st4 = some (heap + 1) :=
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, startState])) (Expr.eval_const h1w) (by omega)
      exact Expr.eval_add h11 h4k (by omega)
    refine runs_seq_assign_le ha6 ?_
    set st4b : State := { st4 with regs := Function.update st4.regs 6 rSlotBase }
    have hpreL : st4b.regs 0 = k ∧ st4b.regs 1 = heap ∧ st4b.regs 2 = ePtr ∧ st4b.regs 5 = fChgPtr ∧
        st4b.regs 6 = rSlotBase ∧ st4b.mem heap = k ∧ st4b.mem (heap + 1 + 6 * k) = fChgPtr ∧
        (∀ a < heap, st4b.mem a = mem a) ∧
        (∀ a, heap + 1 ≤ a → a ≠ heap + 1 + 6 * k → st4b.mem a = 0) := by
      refine ⟨by simp [st4b, st4, st3, st2, st1, startState], by simp [st4b, st4, st3, st2, st1, startState],
        by simp [st4b, st4], by simp [st4b, st4, st3, st2], by simp [st4b],
        by dsimp only [st4b, st4, st3, st2, st1]; rw [Function.update_of_ne (by omega), Function.update_self],
        by dsimp only [st4b, st4, st3]; rw [Function.update_self],
        fun a ha => by dsimp only [st4b, st4, st3, st2, st1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
        fun a ha hne => by
          dsimp only [st4b, st4, st3, st2, st1]
          rw [Function.update_of_ne hne, Function.update_of_ne (by omega)]
          exact hz a (by omega)⟩
    refine runs_seq_triple_le (asmEmptyUpdateLoop_triple p mem hw hsp) hpreL ?_
    intro st5 ⟨_, _, hr2, _, _, hmk, hmf, hbr, hlt, hzr, hze⟩
    refine runs_ret_le (Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_const h2w) (by omega)) ?_ ?_
    · have hval : (Outcome.returned (ePtr + 2)).value = heap + 7 * k + 4 := by
        dsimp only [Outcome.value, ePtr]; omega
      have hze0 : st5.mem ePtr = 0 := hze ePtr le_rfl
      refine ⟨hval, ⟨hmk, fun j hj => ?_⟩, hmf, fun j hj => (hbr j hj).2.2.2.2.1,
        fun j hj => ⟨(hbr j hj).1, (hbr j hj).2.1, (hbr j hj).2.2.1, (hbr j hj).2.2.2.1⟩,
        fun j hj => ⟨(hbr j hj).2.2.2.2.2, hzr j hj⟩,
        fun j hj => ?_, fun j hj => ?_, hlt, hze, fun a ha => hze a (by omega)⟩
      · obtain ⟨hb0, hb1, hb2, hb3, -⟩ := hbr j hj
        refine ⟨?_, ⟨[], ?_, rfl⟩⟩
        · rw [hb0, hb1]; exact smallBatchAt_empty emptyGraph hze0
        · rw [hb2, hb3]; exact ordEditsAt_empty hze0
      · obtain ⟨-, -, hb2, -, -⟩ := hbr j hj
        rw [hb2]; exact (ordEditsAt_empty hze0).1
      · rw [hzr j hj]; rfl
    · simp [Expr.size]; omega
  obtain ⟨o, st', c, hrun, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hc⟩ := hmain
  exact ⟨o, st', c, hrun, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hc⟩

end MinCostFlow.SparseCore.Program
