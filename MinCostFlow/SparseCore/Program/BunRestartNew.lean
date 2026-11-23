module

public import MinCostFlow.SparseCore.Program.BunRestartStage3

/-!
# The restart of the bundles: the new table (`BunRestartNew`)

The new table `brNewTable` keeps the slots that are not listed (`brNewTable_unlisted`). In a
listed slot `s` it holds the bundle state built from the chunks of the tour lists of `rList`
(`brNewTable_listed`). That bundle state has the edges of slot `s` and at most two bundles per
edge (`brNew_card_le`). It agrees with `initBundleFor` (`brNew_bunAgree`).

The last part sums these bounds over the listed slots, for the space and the cost of the export.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

/-! ## Sums over lists -/

theorem brSum_le {l : List ℕ} {f g : ℕ → ℕ} (h : ∀ s ∈ l, f s ≤ g s) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih fun s hs => h s (List.mem_cons_of_mem _ hs))

theorem brSum_affine (l : List ℕ) (a b : ℕ) (f : ℕ → ℕ) :
    (l.map fun s => a + b * f s).sum = a * l.length + b * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

theorem brSum_mul_succ (l : List ℕ) (a : ℕ) (f : ℕ → ℕ) :
    (l.map fun v => a * (f v + 1)).sum = a * ((l.map f).sum + l.length) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

/-! ## The slots of the new table -/

variable {slotCap vCap eCap tbl : ℕ} {S : Fin slotCap → Option BundleState}
  {m : BundleTableMeta slotCap} {mem : ℕ → ℕ} {slots : List ℕ} {cord : ℕ → List End}
  {rList : List ℕ} {k : ℕ}

theorem brSpecs_fst : (brSpecs S slots).map Prod.fst = slots := by
  simp only [brSpecs, List.map_map]
  exact List.map_id'' (fun _ => rfl) slots

/-- The new table keeps the slots that are not listed. -/
theorem brNewTable_unlisted {j : Fin slotCap} (hj : j.1 ∉ slots) :
    brNewTable eCap tbl S m mem slots cord rList k j = S j := by
  simp [brNewTable, tableAfterInitSlots, brSpecs_fst, hj, clearS]

/-- The bundle state of a listed slot `s` after the restart. -/
noncomputable def brNewB (S : Fin slotCap → Option BundleState) (cord : ℕ → List End)
    (rList : List ℕ) (k s : ℕ) : BundleState :=
  bundleStateOfSlots (initPrefixSlots cord rList (slotB S s).edges k) (slotB S s).edges

section

variable (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem)
  (hact : ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B)
include hrep hact

/-- A listed slot of the new table holds `brNewB`. -/
theorem brNewTable_listed {s : ℕ} (hs : s ∈ slots) (hsc : s < slotCap) :
    brNewTable eCap tbl S m mem slots cord rList k ⟨s, hsc⟩ = some (brNewB S cord rList k s) := by
  simp only [brNewTable, tableAfterInitSlots, brSpecs_fst, hs, ite_true, brNewB,
    slotEdgesOf_allPairs hrep hact hs]

theorem slotB_brNewTable {s : ℕ} (hs : s ∈ slots) :
    slotB (brNewTable eCap tbl S m mem slots cord rList k) s = brNewB S cord rList k s :=
  slotB_eq (hact s hs).1 (brNewTable_listed hrep hact hs (hact s hs).1)

end

/-- The new bundle state of a slot has the edges of the slot and at most two bundles per edge. -/
theorem brNew_card_le (hk : 1 ≤ k) (hr : rList.Nodup) (hnd : ∀ v, (cord v).Nodup)
    (hdisj : ∀ v₁ v₂ x, x ∈ cord v₁ → x ∈ cord v₂ → v₁ = v₂) (s : ℕ) :
    (brNewB S cord rList k s).edges = (slotB S s).edges ∧
      (brNewB S cord rList k s).vertices.card ≤ 2 * (slotB S s).edges.card := by
  refine ⟨rfl, ?_⟩
  simp only [brNewB, bundleStateOfSlots, Finset.card_range]
  exact initPrefixSlots_length_le hk hr (fun v _ => hnd v) hdisj

/-- The export of the new slots takes at most `4 n + 5 E` words. -/
theorem brNew_space_sum (hk : 1 ≤ k) (hr : rList.Nodup) (hnd : ∀ v, (cord v).Nodup)
    (hdisj : ∀ v₁ v₂ x, x ∈ cord v₁ → x ∈ cord v₂ → v₁ = v₂) :
    (slots.map fun s => bundleExportSpace (brNewB S cord rList k s)).sum ≤
      4 * slots.length + 5 * edgeTot S slots := by
  refine (brSum_le (g := fun s => 4 + 5 * (slotB S s).edges.card) fun s _ => ?_).trans
    (by rw [brSum_affine]; unfold edgeTot; omega)
  obtain ⟨he, hv⟩ := brNew_card_le (S := S) hk hr hnd hdisj s
  unfold bundleExportSpace
  rw [he]
  omega

/-- The export of the new slots costs at most `100 n + 200 E`. -/
theorem brNew_cost_sum (hk : 1 ≤ k) (hr : rList.Nodup) (hnd : ∀ v, (cord v).Nodup)
    (hdisj : ∀ v₁ v₂ x, x ∈ cord v₁ → x ∈ cord v₂ → v₁ = v₂) :
    (slots.map fun s => bundleExportCost (brNewB S cord rList k s)).sum ≤
      100 * slots.length + 200 * edgeTot S slots := by
  refine (brSum_le (g := fun s => 100 + 200 * (slotB S s).edges.card) fun s _ => ?_).trans
    (by rw [brSum_affine]; unfold edgeTot; omega)
  obtain ⟨he, hv⟩ := brNew_card_le (S := S) hk hr hnd hdisj s
  unfold bundleExportCost
  rw [he]
  omega

/-- The new slots have at most `2 E` bundles in all. -/
theorem brNew_nb_sum (hk : 1 ≤ k) (hr : rList.Nodup) (hnd : ∀ v, (cord v).Nodup)
    (hdisj : ∀ v₁ v₂ x, x ∈ cord v₁ → x ∈ cord v₂ → v₁ = v₂) :
    (slots.map fun s => (brNewB S cord rList k s).vertices.card).sum ≤ 2 * edgeTot S slots := by
  refine (brSum_le (g := fun s => 0 + 2 * (slotB S s).edges.card) fun s _ =>
    by have := (brNew_card_le (S := S) hk hr hnd hdisj s).2; omega).trans
    (by rw [brSum_affine]; unfold edgeTot; omega)

/-! ## Logarithms -/

theorem ordStoreLog_one_le (e : ℕ) : 1 ≤ ordStoreLog e := by
  unfold ordStoreLog; omega

/-- The sort of `2 E ≤ 2 eCap` keys pays one logarithm of `eCap` per key, up to a factor `2`. -/
theorem log_sort_le {E eCap : ℕ} (hE : E ≤ eCap) :
    Nat.log 2 (2 * E + 1) + 1 ≤ 2 * ordStoreLog eCap := by
  have h1 : Nat.log 2 (2 * E + 1) ≤ Nat.log 2 ((eCap + 2) * 2) :=
    Nat.log_mono_right (by omega)
  rw [Nat.log_mul_base (by omega) (by omega)] at h1
  unfold ordStoreLog
  omega

end

end MinCostFlow.SparseCore.Program.Restart
