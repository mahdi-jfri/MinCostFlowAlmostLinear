module

public import MinCostFlow.Machine.WideWord.LSSTGraphBuildCSR
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# WordRAM `O(n + m)` BFS bridges and unified `graphModule`

This file defines and verifies the `O(n + m + 1)` BFS component-discovery procedures and assembles
the 6-procedure graph-preprocessing module `graphModule`:

* Indices `0..2`: `csrAuxModule` (`scanNonloops`, `starPairs`, `buildVertIdx`) from
  `LSSTGraphCSR.lean`.
* Index `3`: `buildCSR` from `LSSTGraphBuildCSR.lean`.
* Index `4`: `bfsVisit` (queue-based BFS from a single unvisited vertex `s`).
* Index `5`: `bfsBridges b` (multi-source BFS over active vertices producing `B` satisfying
  `IsBridgeVerts` for Theorem 2.2).
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM
open MinCostFlow
open MinCostFlow.LSF

/-! ### Module indices and procedures -/

def idxBuildCSR : ℕ := 3
def idxBfsVisit : ℕ := 4
def idxBfsBridges : ℕ := 5

/-- Inner adjacency scan of `bfsVisit`. -/
def bfsVisitInner : Stmt :=
  WordRAM.forRange 11 (.reg 9) (.reg 10) (
    .assign 12 (.load (.bin .add (.reg 2) (.reg 11))) ;;
    .cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 12))) (.const 0))
      (.store (.bin .add (.reg 4) (.reg 12)) (.const 1) ;;
       .store (.bin .add (.reg 5) (.reg 7)) (.reg 12) ;;
       .assign 7 (.bin .add (.reg 7) (.const 1)))
      .nop
  )

/-- BFS visit of one connected component from unvisited vertex `s`.
Args: `[n, offPtr, adjPtr, s, visPtr, queuePtr]`. Returns `0`. -/
def bfsVisit : Stmt :=
  .store (.bin .add (.reg 4) (.reg 3)) (.const 1) ;;
  .store (.reg 5) (.reg 3) ;;
  .assign 6 (.const 0) ;;
  .assign 7 (.const 1) ;;
  .loop (.bin .lt (.reg 6) (.reg 7)) (
    .assign 8 (.load (.bin .add (.reg 5) (.reg 6))) ;;
    .assign 6 (.bin .add (.reg 6) (.const 1)) ;;
    .assign 9 (.load (.bin .add (.reg 1) (.reg 8))) ;;
    .assign 10 (.load (.bin .add (.reg 1) (.bin .add (.reg 8) (.const 1)))) ;;
    bfsVisitInner
  ) ;;
  .ret (.const 0)

/-- Conditional step inside `bfsBridges`: if vertex `reg 7` is unvisited in `reg 6`,
record it in `outBPtr` (`reg 5`) and mark its component via `bfsVisit`. -/
def bfsBridgesCond (b : ℕ) : Stmt :=
  .cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 7))) (.const 0))
    (.store (.bin .add (.reg 5) (.reg 9)) (.reg 7) ;;
     .assign 9 (.bin .add (.reg 9) (.const 1)) ;;
     .call 11 (b + idxBfsVisit) [.reg 0, .reg 1, .reg 2, .reg 7, .reg 6, .reg 8])
    .nop

/-- Compute bridging vertex list `B` across components of active vertices in CSR adjacency.
Args: `[n, offPtr, adjPtr, vLen, vListPtr, outBPtr, heap]`. Returns `bLen`. -/
def bfsBridges (b : ℕ) : Stmt :=
  .assign 7 (.load (.reg 4)) ;;
  .assign 8 (.bin .add (.reg 6) (.reg 0)) ;;
  .call 11 (b + idxBfsVisit) [.reg 0, .reg 1, .reg 2, .reg 7, .reg 6, .reg 8] ;;
  .assign 9 (.const 0) ;;
  .assign 10 (.const 1) ;;
  .loop (.bin .lt (.reg 10) (.reg 3)) (
    .assign 7 (.load (.bin .add (.reg 4) (.reg 10))) ;;
    bfsBridgesCond b ;;
    .assign 10 (.bin .add (.reg 10) (.const 1))
  ) ;;
  .ret (.reg 9)

/-- Unified 6-procedure graph-preprocessing module placed at base `b`. -/
def graphModule (b : ℕ) : List Stmt :=
  csrAuxModule ++ [buildCSR, bfsVisit, bfsBridges b]

theorem graphModule_length (b : ℕ) : (graphModule b).length = 6 := rfl

theorem graphModule_noRand (b : ℕ) : ∀ s ∈ graphModule b, s.NoRand := by
  intro s hs
  simp only [graphModule, csrAuxModule, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact csrAuxModule_noRand _ (by simp [csrAuxModule])
  · exact csrAuxModule_noRand _ (by simp [csrAuxModule])
  · exact csrAuxModule_noRand _ (by simp [csrAuxModule])
  · exact buildCSR_noRand
  · simp [bfsVisit, bfsVisitInner, Stmt.NoRand, WordRAM.forRange, WordRAM.forUp]
  · simp [bfsBridges, bfsBridgesCond, Stmt.NoRand]

theorem hasAt_csrAuxModule {p : Program} {b b0 : ℕ}
    (hp : p.HasAt b (graphModule b0)) : p.HasAt b csrAuxModule := fun i hi => by
  have hi3 : i < 3 := by simpa [csrAuxModule] using hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
    exact hp _ (by simp [graphModule, csrAuxModule])

theorem hasAt_buildCSR {p : Program} {b b0 : ℕ}
    (hp : p.HasAt b (graphModule b0)) : p.HasAt (b + idxBuildCSR) [buildCSR] := fun i hi => by
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  simpa [graphModule, csrAuxModule, idxBuildCSR] using hp 3 (by simp [graphModule, csrAuxModule])

theorem hasAt_bfsVisit {p : Program} {b b0 : ℕ}
    (hp : p.HasAt b (graphModule b0)) : p.HasAt (b + idxBfsVisit) [bfsVisit] := fun i hi => by
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  simpa [graphModule, csrAuxModule, idxBfsVisit] using hp 4 (by simp [graphModule, csrAuxModule])

/-! ### Potential accounting and walk-closure helpers -/

def visZeroCount (n visPtr : ℕ) (mem : ℕ → ℕ) : ℕ :=
  ((Finset.range n).filter (fun u => mem (visPtr + u) = 0)).card

def visZeroDegSum (n visPtr offPtr : ℕ) (m0 mem : ℕ → ℕ) : ℕ :=
  ∑ u ∈ (Finset.range n).filter (fun u => mem (visPtr + u) = 0),
    (m0 (offPtr + (u + 1)) - m0 (offPtr + u))

lemma visZero_flip {n visPtr offPtr u : ℕ} {m0 mem : ℕ → ℕ}
    (hun : u < n) (hz : mem (visPtr + u) = 0) :
    let mem' := Function.update mem (visPtr + u) 1
    visZeroCount n visPtr mem' + 1 = visZeroCount n visPtr mem ∧
    visZeroDegSum n visPtr offPtr m0 mem' + (m0 (offPtr + (u + 1)) - m0 (offPtr + u)) =
      visZeroDegSum n visPtr offPtr m0 mem := by
  let S := (Finset.range n).filter (fun x => mem (visPtr + x) = 0)
  let S' := (Finset.range n).filter (fun x => (Function.update mem (visPtr + u) 1) (visPtr + x) = 0)
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hun, hz⟩
  have hS_eq : S' = S.erase u := by
    ext x
    simp only [S', S, Finset.mem_filter, Finset.mem_erase, Finset.mem_range, ne_eq]
    by_cases hxu : x = u
    · subst hxu; simp
    · simp [hxu]
  constructor
  · change S'.card + 1 = S.card
    rw [hS_eq, Finset.card_erase_add_one huS]
  · change ∑ x ∈ S', (m0 (offPtr + (x + 1)) - m0 (offPtr + x)) +
        (m0 (offPtr + (u + 1)) - m0 (offPtr + u)) =
        ∑ x ∈ S, (m0 (offPtr + (x + 1)) - m0 (offPtr + x))
    rw [hS_eq, Finset.sum_erase_add _ _ huS]

lemma visZero_congr {n visPtr offPtr : ℕ} {m0 mem₁ mem₂ : ℕ → ℕ}
    (h : ∀ u < n, mem₁ (visPtr + u) = 0 ↔ mem₂ (visPtr + u) = 0) :
    visZeroCount n visPtr mem₁ = visZeroCount n visPtr mem₂ ∧
    visZeroDegSum n visPtr offPtr m0 mem₁ = visZeroDegSum n visPtr offPtr m0 mem₂ := by
  have hflt : (Finset.range n).filter (fun u => mem₁ (visPtr + u) = 0) =
      (Finset.range n).filter (fun u => mem₂ (visPtr + u) = 0) :=
    Finset.filter_congr fun u hu => h u (Finset.mem_range.mp hu)
  exact ⟨congrArg Finset.card hflt, congrArg (Finset.sum · _) hflt⟩

lemma visZero_le_total {n visPtr offPtr : ℕ} {m0 mem : ℕ → ℕ}
    (hmono : ∀ u < n, m0 (offPtr + u) ≤ m0 (offPtr + (u + 1))) :
    visZeroCount n visPtr mem ≤ n ∧
    visZeroDegSum n visPtr offPtr m0 mem ≤ m0 (offPtr + n) - m0 offPtr := by
  constructor
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  · have hsub : ∑ u ∈ (Finset.range n).filter (fun u => mem (visPtr + u) = 0),
        (m0 (offPtr + (u + 1)) - m0 (offPtr + u)) ≤
        ∑ u ∈ Finset.range n, (m0 (offPtr + (u + 1)) - m0 (offPtr + u)) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have h0_le : ∀ j ≤ n, m0 offPtr ≤ m0 (offPtr + j) := fun j => by
      induction j with
      | zero => intro _; exact le_refl _
      | succ j ih => intro hj; exact (ih (by omega)).trans (hmono j (by omega))
    have htele : ∀ k ≤ n, ∑ u ∈ Finset.range k, (m0 (offPtr + (u + 1)) - m0 (offPtr + u)) =
        m0 (offPtr + k) - m0 offPtr := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 := h0_le k (by omega)
        have h2 := hmono k (by omega)
        rw [Finset.sum_range_succ, ih (by omega)]; omega
    exact hsub.trans_eq (htele n (le_refl _))

section ClassicalAccounting
open Classical

noncomputable def reachUnvisSet (G : IndexedGraph) (visPtr s : ℕ) (mem : ℕ → ℕ) : Finset ℕ :=
  (Finset.range G.n).filter fun u =>
    mem (visPtr + u) = 0 ∧ ({ G.toMGraph with E := (nonloopEdges G).toFinset } : MGraph).Connected s u

noncomputable def unreachUnvisSet (G : IndexedGraph) (visPtr s : ℕ) (mem : ℕ → ℕ) : Finset ℕ :=
  (Finset.range G.n).filter fun u =>
    mem (visPtr + u) = 0 ∧ ¬ ({ G.toMGraph with E := (nonloopEdges G).toFinset } : MGraph).Connected s u

lemma visZero_partition (G : IndexedGraph) (visPtr offPtr s : ℕ) (m0 mem : ℕ → ℕ) :
    (reachUnvisSet G visPtr s mem).card + (unreachUnvisSet G visPtr s mem).card =
      visZeroCount G.n visPtr mem ∧
    (∑ u ∈ reachUnvisSet G visPtr s mem, (m0 (offPtr + (u + 1)) - m0 (offPtr + u))) +
      (∑ u ∈ unreachUnvisSet G visPtr s mem, (m0 (offPtr + (u + 1)) - m0 (offPtr + u))) =
      visZeroDegSum G.n visPtr offPtr m0 mem := by
  let Z := (Finset.range G.n).filter (fun u => mem (visPtr + u) = 0)
  let G_nl : MGraph := { G.toMGraph with E := (nonloopEdges G).toFinset }
  have hR : reachUnvisSet G visPtr s mem = Z.filter (fun u => G_nl.Connected s u) := by
    ext u; simp [reachUnvisSet, Z, G_nl, and_assoc]
  have hU : unreachUnvisSet G visPtr s mem = Z.filter (fun u => ¬ G_nl.Connected s u) := by
    ext u; simp [unreachUnvisSet, Z, G_nl, and_assoc]
  rw [hR, hU]
  exact ⟨Finset.card_filter_add_card_filter_not (s := Z) (p := fun u => G_nl.Connected s u),
    Finset.sum_filter_add_sum_filter_not Z (fun u => G_nl.Connected s u) _⟩

noncomputable def bfsVisitExactCost (G : IndexedGraph) (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  match args with
  | [_, offPtr, _, s, visPtr, _] =>
    let R := reachUnvisSet G visPtr s mem
    120 * R.card + 120 * (∑ u ∈ R, (mem (offPtr + (u + 1)) - mem (offPtr + u))) + 60
  | _ => 0

end ClassicalAccounting

lemma vis_walk_invariant {G : IndexedGraph} {mem : ℕ → ℕ} {visPtr : ℕ}
    (hclosed : ∀ e ∈ nonloopEdges G, mem (visPtr + G.tail e) = 1 ↔ mem (visPtr + G.head e) = 1) :
    ∀ {x y : ℕ} {P : List (ℕ × Bool)},
      ({ G.toMGraph with E := (nonloopEdges G).toFinset } : MGraph).IsWalk x y P →
      mem (visPtr + x) = 1 → mem (visPtr + y) = 1
  | _, _, [], .nil _, hx => hx
  | _, _, (e, dir) :: _, .cons heE hsrc hrest, hx => by
    have he : e ∈ nonloopEdges G := List.mem_toFinset.mp heE
    have hstep : mem (visPtr + ({ G.toMGraph with E := (nonloopEdges G).toFinset } : MGraph).dst (e, dir)) = 1 := by
      cases dir
      · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsrc
        simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte]
        rw [← hsrc] at hx
        exact (hclosed e he).mpr hx
      · simp only [MGraph.src, ↓reduceIte] at hsrc
        simp only [MGraph.dst, ↓reduceIte]
        rw [← hsrc] at hx
        exact (hclosed e he).mp hx
    exact vis_walk_invariant hclosed hrest hstep

/-! ### `bfsVisit` contracts and verification -/

def bfsVisitContract (G : IndexedGraph) (w : ℕ) : Contract where
  pre args mem := ∃ offPtr adjPtr s visPtr queuePtr,
    args = [G.n, offPtr, adjPtr, s, visPtr, queuePtr] ∧
    G.Valid ∧ 16 ≤ 2 ^ w ∧
    s < G.n ∧ mem (visPtr + s) = 0 ∧
    offPtr + (G.n + 1) ≤ visPtr ∧ adjPtr + 2 * (nonloopEdges G).length ≤ visPtr ∧
    visPtr + G.n = queuePtr ∧ queuePtr + G.n < 2 ^ w ∧
    CSRAdjacencySpec G mem offPtr adjPtr ∧
    (∀ u < G.n, mem (visPtr + u) = 0 ∨ mem (visPtr + u) = 1) ∧
    (∀ e ∈ nonloopEdges G, mem (visPtr + G.tail e) = 1 ↔ mem (visPtr + G.head e) = 1)
  post args mem _ mem' := ∃ offPtr adjPtr s visPtr queuePtr,
    args = [G.n, offPtr, adjPtr, s, visPtr, queuePtr] ∧
    mem' (visPtr + s) = 1 ∧
    (∀ u < G.n, mem (visPtr + u) = 1 → mem' (visPtr + u) = 1) ∧
    (∀ u < G.n, mem' (visPtr + u) = 0 ∨ mem' (visPtr + u) = 1) ∧
    (∀ u < G.n, mem (visPtr + u) = 0 → mem' (visPtr + u) = 1 →
      ({ G.toMGraph with E := (nonloopEdges G).toFinset } : MGraph).Connected s u) ∧
    (∀ e ∈ nonloopEdges G, mem' (visPtr + G.tail e) = 1 ↔ mem' (visPtr + G.head e) = 1) ∧
    (∀ a, a < visPtr ∨ visPtr + 2 * G.n ≤ a → mem' a = mem a) ∧
    visZeroCount G.n visPtr mem' + 1 ≤ visZeroCount G.n visPtr mem
  cost args mem := match args with
    | [_, offPtr, _, _, visPtr, _] =>
      120 * visZeroCount G.n visPtr mem + 120 * visZeroDegSum G.n visPtr offPtr mem mem + 60
    | _ => 0

noncomputable def bfsVisitExactContract (G : IndexedGraph) (w : ℕ) : Contract where
  pre := (bfsVisitContract G w).pre
  post args mem ret mem' := (bfsVisitContract G w).post args mem ret mem' ∧
    ∃ offPtr adjPtr s visPtr queuePtr,
      args = [G.n, offPtr, adjPtr, s, visPtr, queuePtr] ∧
      visZeroCount G.n visPtr mem' + (reachUnvisSet G visPtr s mem).card =
        visZeroCount G.n visPtr mem ∧
      visZeroDegSum G.n visPtr offPtr mem mem' +
        (∑ u ∈ reachUnvisSet G visPtr s mem, (mem (offPtr + (u + 1)) - mem (offPtr + u))) =
        visZeroDegSum G.n visPtr offPtr mem mem
  cost args mem := bfsVisitExactCost G args mem

def qDegSum (offPtr queuePtr : ℕ) (m0 : ℕ → ℕ) (st : State) : ℕ :=
  ∑ j ∈ Finset.Ico (st.regs 6) (st.regs 7),
    (m0 (offPtr + (st.mem (queuePtr + j) + 1)) - m0 (offPtr + st.mem (queuePtr + j)))

def bfsRemTotal (G : IndexedGraph) (offPtr visPtr queuePtr : ℕ) (m0 : ℕ → ℕ) (st : State) : ℕ :=
  50 * (st.regs 7 - st.regs 6) +
  120 * visZeroCount G.n visPtr st.mem +
  120 * visZeroDegSum G.n visPtr offPtr m0 st.mem +
  120 * qDegSum offPtr queuePtr m0 st + 15

def bfsVisitLoopInv (G : IndexedGraph) (offPtr adjPtr s visPtr queuePtr : ℕ)
    (mem : ℕ → ℕ) (st : State) : Prop :=
  let G_nl : MGraph := { G.toMGraph with E := (nonloopEdges G).toFinset }
  st.regs 0 = G.n ∧ st.regs 1 = offPtr ∧ st.regs 2 = adjPtr ∧
  st.regs 4 = visPtr ∧ st.regs 5 = queuePtr ∧
  st.regs 6 ≤ st.regs 7 ∧ st.regs 7 ≤ G.n ∧
  st.mem (visPtr + s) = 1 ∧
  (∀ u < G.n, mem (visPtr + u) = 1 → st.mem (visPtr + u) = 1) ∧
  (∀ u < G.n, st.mem (visPtr + u) = 0 ∨ st.mem (visPtr + u) = 1) ∧
  (∀ u < G.n, mem (visPtr + u) = 0 → st.mem (visPtr + u) = 1 → G_nl.Connected s u) ∧
  (∀ u < G.n, mem (visPtr + u) = 0 → st.mem (visPtr + u) = 1 →
    ∃ j < st.regs 7, st.mem (queuePtr + j) = u) ∧
  (∀ j < st.regs 7,
    st.mem (queuePtr + j) < G.n ∧ st.mem (visPtr + st.mem (queuePtr + j)) = 1 ∧
    G_nl.Connected s (st.mem (queuePtr + j))) ∧
  ((List.range (st.regs 7)).map fun j => st.mem (queuePtr + j)).Nodup ∧
  (∀ j < st.regs 6, ∀ p,
    mem (offPtr + st.mem (queuePtr + j)) ≤ p → p < mem (offPtr + (st.mem (queuePtr + j) + 1)) →
    st.mem (visPtr + st.mem (adjPtr + p)) = 1) ∧
  (∀ a, a < visPtr ∨ visPtr + 2 * G.n ≤ a → st.mem a = mem a)

def bfsVisitInnerInv (G : IndexedGraph) (offPtr adjPtr s visPtr queuePtr qhead q pSt pEn : ℕ)
    (mem st_mem : ℕ → ℕ) (rem0 : ℕ) (pIdx : ℕ) (s₁ : State) : Prop :=
  let G_nl : MGraph := { G.toMGraph with E := (nonloopEdges G).toFinset }
  s₁.regs 0 = G.n ∧ s₁.regs 1 = offPtr ∧ s₁.regs 2 = adjPtr ∧ s₁.regs 4 = visPtr ∧
  s₁.regs 5 = queuePtr ∧ s₁.regs 6 = qhead + 1 ∧ s₁.regs 8 = q ∧
  s₁.regs 9 = pSt ∧ s₁.regs 10 = pEn ∧ s₁.regs 11 = pIdx ∧
  qhead + 1 ≤ s₁.regs 7 ∧ s₁.regs 7 ≤ G.n ∧
  s₁.mem (visPtr + s) = 1 ∧
  (∀ u < G.n, mem (visPtr + u) = 1 → s₁.mem (visPtr + u) = 1) ∧
  (∀ u < G.n, st_mem (visPtr + u) = 1 → s₁.mem (visPtr + u) = 1) ∧
  (∀ u < G.n, s₁.mem (visPtr + u) = 0 ∨ s₁.mem (visPtr + u) = 1) ∧
  (∀ u < G.n, mem (visPtr + u) = 0 → s₁.mem (visPtr + u) = 1 → G_nl.Connected s u) ∧
  (∀ u < G.n, mem (visPtr + u) = 0 → s₁.mem (visPtr + u) = 1 →
    ∃ j < s₁.regs 7, s₁.mem (queuePtr + j) = u) ∧
  (∀ j < s₁.regs 7,
    s₁.mem (queuePtr + j) < G.n ∧ s₁.mem (visPtr + s₁.mem (queuePtr + j)) = 1 ∧
    G_nl.Connected s (s₁.mem (queuePtr + j))) ∧
  ((List.range (s₁.regs 7)).map fun j => s₁.mem (queuePtr + j)).Nodup ∧
  (∀ j < qhead, ∀ p, mem (offPtr + s₁.mem (queuePtr + j)) ≤ p →
    p < mem (offPtr + (s₁.mem (queuePtr + j) + 1)) → s₁.mem (visPtr + s₁.mem (adjPtr + p)) = 1) ∧
  (∀ p, pSt ≤ p → p < pIdx → s₁.mem (visPtr + s₁.mem (adjPtr + p)) = 1) ∧
  (∀ j < qhead + 1, j < s₁.regs 7 → s₁.mem (queuePtr + j) = st_mem (queuePtr + j)) ∧
  (∀ a, a < visPtr ∨ visPtr + 2 * G.n ≤ a → s₁.mem a = mem a) ∧
  bfsRemTotal G offPtr visPtr queuePtr mem s₁ ≤ rem0

lemma csr_off_le_2nl {G : IndexedGraph} {mem : ℕ → ℕ} {offPtr adjPtr u : ℕ}
    (hcsr : CSRAdjacencySpec G mem offPtr adjPtr) (hu : u ≤ G.n) :
    mem (offPtr + u) ≤ 2 * (nonloopEdges G).length := by
  suffices ∀ d, u + d ≤ G.n → mem (offPtr + u) ≤ mem (offPtr + (u + d)) by
    have h := this (G.n - u) (by omega)
    rw [show u + (G.n - u) = G.n by omega, hcsr.2.2.1] at h
    exact h
  intro d
  induction d with
  | zero => intro _; exact le_refl _
  | succ d ih => intro hd; exact (ih (by omega)).trans (hcsr.2.1 _ (by omega))

lemma csr_adj_frame {G : IndexedGraph} {m0 m1 : ℕ → ℕ} {offPtr adjPtr : ℕ}
    (hG : G.Valid) (hcsr : CSRAdjacencySpec G m0 offPtr adjPtr)
    (hoff : ∀ u ≤ G.n, m1 (offPtr + u) = m0 (offPtr + u))
    (hadj : ∀ q < 2 * (nonloopEdges G).length, m1 (adjPtr + q) = m0 (adjPtr + q)) :
    CSRAdjacencySpec G m1 offPtr adjPtr := by
  refine ⟨by simpa using (hoff 0 (Nat.zero_le _)).trans hcsr.1,
    fun u hu => by rw [hoff u (by omega), hoff (u + 1) hu]; exact hcsr.2.1 u hu,
    by rw [hoff G.n (le_refl _), hcsr.2.2.1],
    fun u hu q hq1 hq2 => ?_,
    fun e he => ?_⟩
  · rw [hoff u (by omega)] at hq1
    rw [hoff (u + 1) hu] at hq2
    obtain ⟨e, he, hth⟩ := hcsr.2.2.2.1 u hu q hq1 hq2
    have hq_lt : q < 2 * (nonloopEdges G).length := lt_of_lt_of_le hq2 (csr_off_le_2nl hcsr hu)
    exact ⟨e, he, by rwa [hadj q hq_lt]⟩
  · have het := (hG.2 e (mem_nonloopEdges_iff.mp he).1).1
    have heh := (hG.2 e (mem_nonloopEdges_iff.mp he).1).2
    obtain ⟨⟨p1, h1a, h1b, h1c⟩, ⟨p2, h2a, h2b, h2c⟩⟩ := hcsr.2.2.2.2 e he
    have h1_lt : p1 < 2 * (nonloopEdges G).length := lt_of_lt_of_le h1b (csr_off_le_2nl hcsr (by omega))
    have h2_lt : p2 < 2 * (nonloopEdges G).length := lt_of_lt_of_le h2b (csr_off_le_2nl hcsr (by omega))
    exact ⟨⟨p1, by rwa [hoff _ (by omega)], by rwa [hoff _ (by omega)], by rwa [hadj p1 h1_lt]⟩,
      ⟨p2, by rwa [hoff _ (by omega)], by rwa [hoff _ (by omega)], by rwa [hadj p2 h2_lt]⟩⟩


end MinCostFlow.WideWord
