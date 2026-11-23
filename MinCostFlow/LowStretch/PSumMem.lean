module

public import MinCostFlow.LowStretch.ProgPSum

/-!
# What `psum` adds, entry by entry

`psum` adds, for each arc of the settled node `u`, a value that depends on the head of the arc
and on its entry. When the arcs of `u` are the two directions of the entries at `u` (the sum
fact of `pgP`), what it adds is the sum of `EAdd` over the entries at `u` (`psum_sm`). With
`esum_snoc` this says that after the settle the cells hold the sums `ESum` of the longer settled
list.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Classical

/-- What `psum` adds for an arc with head `y` and entry `e`. -/
noncomputable def PS.gve (F : PS) (mem : ℕ → ℕ) (y e : ℕ) : Fin 5 → ℕ :=
  let okc := mem (F.OK + y) = F.os
  let stc := mem (F.TS + 2 * F.NN + y) = F.rs
  let wt := 1 <<< (F.Es - mem (F.EXP + mem (F.AS + 2 * e)))
  fun t => match t with
    | 0 => if okc ∧ stc then 1 else 0
    | 1 => if okc ∧ ¬ stc then wt else 0
    | 2 => if okc ∧ stc then wt else 0
    | 3 => if okc ∧ ¬ stc then wt * F.k else 0
    | 4 => if okc ∧ stc then wt * mem (F.TS + F.NN + y) else 0

theorem PS.gv_eq (F : PS) (mem : ℕ → ℕ) (k : ℕ) (t : Fin 5) :
    F.gv mem k t = F.gve mem (mem (F.HD + k)) (mem (F.ORD + k) / 2) t := by
  have e : mem (F.ORD + k) >>> 1 = mem (F.ORD + k) / 2 := by
    rw [Nat.shiftRight_eq_div_pow]
  by_cases h1 : mem (F.OK + mem (F.HD + k)) = F.os <;>
    by_cases h2 : mem (F.TS + 2 * F.NN + mem (F.HD + k)) = F.rs <;>
    fin_cases t <;> simp [PS.gv, PS.gve, PS.okc, PS.stc, PS.wt, PS.pa, PS.y, PS.ty, e, h1, h2]

/-- **What `psum` adds.** -/
theorem psum_sm (F : PS) (mem : ℕ → ℕ) {ea eb wtE : ℕ → ℕ} {ok : ℕ → Prop} {δ : ℕ → ℕ}
    {ℓ' : List ℕ} {u nA : ℕ}
    (hsum : ∀ Fs : ℕ → ℕ → ℕ,
      ∑ k ∈ Finset.Ico F.lo F.hi, Fs (mem (F.HD + k)) (mem (F.ORD + k) / 2) =
        ∑ j ∈ (Finset.range nA).filter (ea · = u), Fs (eb j) j +
        ∑ j ∈ (Finset.range nA).filter (eb · = u), Fs (ea j) j)
    (hok : ∀ y < F.NN, (mem (F.OK + y) = F.os ↔ ok y))
    (hends : ∀ j < nA, ea j < F.NN ∧ eb j < F.NN)
    (hst : ∀ y, ok y → (mem (F.TS + 2 * F.NN + y) = F.rs ↔ y ∈ ℓ'))
    (hty : ∀ y, ok y → y ∈ ℓ' → mem (F.TS + F.NN + y) = δ y)
    (hk : F.k = δ u)
    (hwt : ∀ j < nA, 1 <<< (F.Es - mem (F.EXP + mem (F.AS + 2 * j))) = wtE j) (t : Fin 5) :
    F.sm mem t F.hi =
      ∑ j ∈ (Finset.range nA).filter (ea · = u), EAdd ok δ ℓ' u (eb j) (wtE j) t +
      ∑ j ∈ (Finset.range nA).filter (eb · = u), EAdd ok δ ℓ' u (ea j) (wtE j) t := by
  unfold PS.sm
  rw [Finset.sum_congr rfl fun k _ => F.gv_eq mem k t, hsum (fun y e => F.gve mem y e t)]
  have key : ∀ y j, j < nA → y < F.NN → F.gve mem y j t = EAdd ok δ ℓ' u y (wtE j) t := by
    intro y j hj hyN
    have hw := hwt j hj
    by_cases hy : ok y
    · have hs := hst y hy
      have ho : mem (F.OK + y) = F.os := (hok y hyN).mpr hy
      by_cases hm : y ∈ ℓ'
      · have ht := hty y hy hm
        fin_cases t <;> simp [PS.gve, EAdd, ho, hs.mpr hm, hy, hm, hw, ht, hk]
      · have hs' : ¬ mem (F.TS + 2 * F.NN + y) = F.rs := fun h => hm (hs.mp h)
        fin_cases t <;> simp [PS.gve, EAdd, ho, hs', hy, hm, hw, hk]
    · have ho : ¬ mem (F.OK + y) = F.os := fun h => hy ((hok y hyN).mp h)
      fin_cases t <;> simp [PS.gve, EAdd, ho, hy]
  congr 1
  · exact Finset.sum_congr rfl fun j hj =>
      key _ j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
        (hends j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)).2
  · exact Finset.sum_congr rfl fun j hj =>
      key _ j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
        (hends j (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)).1

end MinCostFlow.LowStretch
