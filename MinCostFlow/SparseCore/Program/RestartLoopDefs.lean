module

public import MinCostFlow.SparseCore.Program.RestartExport

/-!
# The loop of the restart: definitions and arithmetic (`RestartLoopDefs`)

The loop of `restartBranchStmt` calls operation `0` of the bucket spanners once per listed slot.
After round `i` the table is `spanAfter S6 g (slots.take i)`: the first `i` slots hold a fresh
spanner on their graph `g s`. This file defines that table and the potential `specPhi`, which the
representation of `bucketSpannerDS` fixes from the abstract state (`bucketPhi_eq_specPhi`). The
cost of the loop is a sum of `a i + p i - p (i + 1)` over the rounds, where `a i` is the bound of
round `i` and `p i` the potential after `i` rounds; `sum_tele` turns it into the amortized form.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

/-- The potential of a bucket spanner table: the sum of the banks of its active slots. -/
@[expose] noncomputable def specPhi (P : DSParams) {cap : ℕ} (S : BucketSpannerState cap) : ℕ :=
  ∑ j, match S j with
    | some s => s.bank P
    | none => 0

/-- The potential of the representation of `bucketSpannerDS` is that of its abstract state. -/
theorem bucketPhi_eq_specPhi {P : DSParams} {cap tbl : ℕ} {S : BucketSpannerState cap}
    {x : (bucketSpannerRep P cap).τ} {mem : ℕ → ℕ}
    (h : (bucketSpannerRep P cap).rep tbl S x mem) :
    (bucketSpannerRep P cap).phi tbl x mem = specPhi P S := by
  show bucketPhi P x = _
  unfold bucketPhi specPhi
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := h.1 j
  rcases hS : S j with _ | s <;> rcases hx : x.slots j with _ | ⟨b, m⟩ <;>
    simp only [hS, hx] at hj ⊢ <;>
    first
      | rfl
      | exact hj.elim
      | (obtain ⟨-, hr, -⟩ := hj; simp only [bucketSlotBank]; rw [hr.1])

/-- The table after the slots of `l` got a fresh spanner on their graphs `g s`. -/
@[expose] def spanAfter {cap : ℕ} (S6 : BucketSpannerState cap) (g : ℕ → MGraph) (l : List ℕ) :
    BucketSpannerState cap :=
  fun j => if j.1 ∈ l then some ⟨g j.1, []⟩ else S6 j

theorem restartSpanState_eq_spanAfter {slotCap cap : ℕ} (S6 : BucketSpannerState cap)
    (S : Fin slotCap → Option BundleState) (cs : CompLSFState) (ord : ℕ → List End) (k : ℕ)
    (slots : List ℕ) :
    restartSpanState S6 S cs ord k slots = spanAfter S6 (restartSlotGraph S cs ord k) slots :=
  rfl

theorem spanAfter_nil {cap : ℕ} (S6 : BucketSpannerState cap) (g : ℕ → MGraph) :
    spanAfter S6 g [] = S6 := by
  funext j; simp [spanAfter]

theorem spanAfter_take_succ {cap : ℕ} (S6 : BucketSpannerState cap) (g : ℕ → MGraph)
    {slots : List ℕ} {i : ℕ} (hi : i < slots.length) (hs : slots[i] < cap) :
    spanAfter S6 g (slots.take (i + 1)) =
      (spanAfter S6 g (slots.take i)).set ⟨slots[i], hs⟩ (some ⟨g slots[i], []⟩) := by
  have hmem : ∀ a, a ∈ slots.take (i + 1) ↔ a ∈ slots.take i ∨ a = slots[i] := by
    intro a
    rw [List.take_add_one, List.getElem?_eq_getElem hi, List.mem_append]
    simp only [Option.toList_some, List.mem_singleton]
  funext j
  by_cases hj : j = ⟨slots[i], hs⟩
  · subst hj
    simp [spanAfter, BucketSpannerState.set, hmem]
  · have hj' : j.1 ≠ slots[i] := fun h => hj (Fin.ext h)
    simp only [spanAfter, BucketSpannerState.set, Function.update_of_ne hj, hmem, hj', or_false]

/-- The amortized sum: if no round raises the potential by more than its bound, the sum of the
rounds' bounds minus the potential changes, plus the last potential, is at most the sum of the
bounds plus the first potential. -/
theorem sum_tele (a p : ℕ → ℕ) (n : ℕ) (h : ∀ j < n, p (j + 1) ≤ a j + p j) :
    ((List.range n).map fun j => a j + p j - p (j + 1)).sum + p n ≤
      ((List.range n).map a).sum + p 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih fun j hj => h j (by omega)
    have hn := h n (by omega)
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega

/-- A sum over the first `i + 1` rounds. -/
theorem sum_range_succ' (f : ℕ → ℕ) (i : ℕ) :
    ((List.range (i + 1)).map f).sum = ((List.range i).map f).sum + f i := by
  simp [List.range_succ, List.sum_append]

/-- Sums over a prefix of the rounds grow with the prefix. -/
theorem sum_range_mono (f : ℕ → ℕ) {i n : ℕ} (h : i ≤ n) :
    ((List.range i).map f).sum ≤ ((List.range n).map f).sum := by
  induction n with
  | zero => simp [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · rw [sum_range_succ']; exact le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · rw [show i = n + 1 by omega]

/-- A sum over the rounds of a function of the slots is the sum over the slots. -/
theorem sum_range_getD (f : ℕ → ℕ) (slots : List ℕ) :
    ((List.range slots.length).map fun j => f (slots.getD j 0)).sum = (slots.map f).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  simp at h₁
  simp [List.getElem?_eq_getElem h₁]

/-- `ExportAt` reads only the cells from `d` to `hEnd`. -/
theorem exportAt_congr {mem mem' : ℕ → ℕ} {d hEnd : ℕ} {G : MGraph}
    (heq : ∀ a, d ≤ a → a < hEnd → mem' a = mem a) (hx : ExportAt mem d hEnd G) :
    ExportAt mem' d hEnd G := by
  obtain ⟨hn, hm, hnd, hV, hnd2, hT, hcov, hd4, hV1, hE1, hVend, hEend⟩ := hx
  have h0 : mem' d = mem d := heq d (le_refl _) (by omega)
  have h1 : mem' (d + 1) = mem (d + 1) := heq _ (by omega) (by omega)
  have h2 : mem' (d + 2) = mem (d + 2) := heq _ (by omega) (by omega)
  have h3 : mem' (d + 3) = mem (d + 3) := heq _ (by omega) (by omega)
  have hvL : readList mem' (mem' (d + 1)) (mem' d) = readList mem (mem (d + 1)) (mem d) := by
    rw [h0, h1]
    unfold readList
    refine List.map_congr_left fun i hi => heq _ (by omega) ?_
    have := List.mem_range.mp hi; omega
  have heT : readTriples mem' (mem' (d + 3)) (mem' (d + 2)) =
      readTriples mem (mem (d + 3)) (mem (d + 2)) := by
    rw [h2, h3]
    unfold readTriples
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    rw [heq _ (by omega) (by omega), heq _ (by omega) (by omega), heq _ (by omega) (by omega)]
  unfold ExportAt
  rw [hvL, heT, h0, h1, h2, h3]
  exact ⟨hn, hm, hnd, hV, hnd2, hT, hcov, hd4, hV1, hE1, hVend, hEend⟩

end

end MinCostFlow.SparseCore.Program.Restart
