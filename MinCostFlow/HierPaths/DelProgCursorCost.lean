module

public import MinCostFlow.HierPaths.DelProgState

/-!
# Charging moves of a cursor to the cursor sum

One visit costs a fixed amount plus a cost per entry skipped. A cursor write increases the
sum of positions by exactly the number of entries skipped. The increase telescopes even
when the same cursor is visited more than once.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The change in the sum of a cursor table after updating one in-range cursor. -/
theorem delCursorSum_update (f : ℕ → ℕ) {n q v : ℕ} (hq : q < n) (hv : f q ≤ v) :
    (∑ i ∈ Finset.range n, Function.update f q v i) =
      (∑ i ∈ Finset.range n, f i) + (v - f q) := by
  have hq' := Finset.mem_range.mpr hq
  have h₀ := Finset.sum_erase_add (s := Finset.range n) f hq'
  have h₁ := Finset.sum_erase_add (s := Finset.range n) (Function.update f q v) hq'
  have he : (∑ i ∈ (Finset.range n).erase q, Function.update f q v i) =
      (∑ i ∈ (Finset.range n).erase q, f i) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    exact Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _
  rw [Function.update_self, he] at h₁
  omega

/-- Range costs telescope when each step charges the increase of a nondecreasing count. -/
theorem delRangeCost_le_of_delta (cost count : ℕ → ℕ) (start len fixed unit : ℕ)
    (h : ∀ i, start ≤ i → i < start + len →
      cost i + unit * count i ≤ fixed + unit * count (i + 1)) :
    rangeCost cost start (start + len) + unit * count start ≤
      fixed * len + unit * count (start + len) := by
  induction len with
  | zero => simp
  | succ len ih =>
    have hlast : start + len < start + (len + 1) := by omega
    have he : rangeCost cost start (start + (len + 1)) =
        rangeCost cost start (start + len) + cost (start + len) := by
      simp only [rangeCost, Nat.add_sub_cancel_left, List.range'_concat, List.map_append,
        List.map_singleton, List.sum_append, List.sum_singleton, Nat.one_mul]
    rw [he, Nat.mul_succ]
    have hp := ih (fun i hs hi => h i hs (hi.trans hlast))
    have hq := h (start + len) (Nat.le_add_right ..) hlast
    rw [← Nat.add_assoc start len 1]
    omega

/-- Pair-loop costs are bounded by constant work per listed connector plus the cursor moves. -/
theorem delPairPass_rangeCost (x : HierConcrete) (cs : List ℕ)
    (hq : ∀ c ∈ cs, x.H.A.pairOf c < x.H.A.numPairs) :
    rangeCost (delPairPassStepCost x cs) 0 cs.length +
        90 * (∑ q ∈ Finset.range x.H.A.numPairs, x.ms.st.pairCur q) ≤
      261 * cs.length +
        90 * (∑ q ∈ Finset.range x.H.A.numPairs, (x.refreshPairs cs).ms.st.pairCur q) := by
  let count := fun i => ∑ q ∈ Finset.range x.H.A.numPairs,
    (x.refreshPairs (cs.take i)).ms.st.pairCur q
  have H := delRangeCost_le_of_delta (delPairPassStepCost x cs) count 0 cs.length 261 90
    (fun i _ hi => by
      rw [Nat.zero_add] at hi
      let q := x.H.A.pairOf cs[i]
      let y := x.refreshPairs (cs.take i)
      let n := (x.H.A.pairConns q).length
      let old := y.ms.st.pairCur q
      let valid := x.H.A.pairValid (x.H.A.surv x.ms.st) q
      let next := advance valid n old
      obtain ⟨hH, hLoss, _⟩ := x.refreshPairs_data (cs.take i)
      have hs : y.H.A.surv y.ms.st = x.H.A.surv x.ms.st := by
        simp only [StaticArrays.surv, y, hH, hLoss]
      have hnext : (x.refreshPairs (cs.take (i + 1))).ms.st.pairCur =
          Function.update y.ms.st.pairCur q next := by
        rw [List.take_succ_eq_append_getElem hi, x.refreshPairs_append_one]
        change Function.update y.ms.st.pairCur q
          (advance (y.H.A.pairValid (y.H.A.surv y.ms.st) q) (y.H.A.pairConns q).length old) = _
        rw [hs, show y.H = x.H from hH]
      have he : count (i + 1) = count i + (next - old) := by
        unfold count
        rw [hnext]
        exact delCursorSum_update _ (hq _ (List.getElem_mem hi)) (le_advance valid n old)
      unfold delPairPassStepCost
      rw [List.getD_eq_getElem _ 0 hi, he]
      change 171 + (next - old + 1) * 90 + 90 * count i ≤ 261 + 90 * (count i + (next - old))
      omega)
  simpa only [Nat.zero_add, count, List.take_zero, List.take_length, HierConcrete.refreshPairs,
    List.foldl_nil] using H

/-- Owner-loop costs are bounded by constant work per listed terminal plus the cursor moves. -/
theorem delOwnerPass_rangeCost (x : HierConcrete) (cs : List ℕ)
    (hq : ∀ c ∈ cs, x.H.A.C.owner c < x.n) :
    rangeCost (delOwnerPassStepCost x cs) 0 cs.length +
        280 * (∑ q ∈ Finset.range x.n, x.ms.st.supCur q) ≤
      451 * cs.length +
        280 * (∑ q ∈ Finset.range x.n, (x.refreshOwners cs).ms.st.supCur q) := by
  let count := fun i => ∑ q ∈ Finset.range x.n,
    (x.refreshOwners (cs.take i)).ms.st.supCur q
  have H := delRangeCost_le_of_delta (delOwnerPassStepCost x cs) count 0 cs.length 451 280
    (fun i _ hi => by
      rw [Nat.zero_add] at hi
      let q := x.H.A.C.owner cs[i]
      let y := x.refreshOwners (cs.take i)
      let n := (x.H.A.C.supportArray q).length
      let old := y.ms.st.supCur q
      let valid := x.H.A.supValid (x.H.A.surv x.ms.st) q
      let next := advance valid n old
      obtain ⟨hH, hLoss, _⟩ := x.refreshOwners_data (cs.take i)
      have hs : y.H.A.surv y.ms.st = x.H.A.surv x.ms.st := by
        simp only [StaticArrays.surv, y, hH, hLoss]
      have hnext : (x.refreshOwners (cs.take (i + 1))).ms.st.supCur =
          Function.update y.ms.st.supCur q next := by
        rw [List.take_succ_eq_append_getElem hi, x.refreshOwners_append_one]
        change Function.update y.ms.st.supCur q
          (advance (y.H.A.supValid (y.H.A.surv y.ms.st) q) (y.H.A.C.supportArray q).length old) = _
        rw [hs, show y.H = x.H from hH]
      have he : count (i + 1) = count i + (next - old) := by
        unfold count
        rw [hnext]
        exact delCursorSum_update _ (hq _ (List.getElem_mem hi)) (le_advance valid n old)
      unfold delOwnerPassStepCost
      rw [List.getD_eq_getElem _ 0 hi, he]
      change 171 + (next - old + 1) * 280 + 280 * count i ≤ 451 + 280 * (count i + (next - old))
      omega)
  simpa only [Nat.zero_add, count, List.take_zero, List.take_length, HierConcrete.refreshOwners,
    List.foldl_nil] using H

/-- A walk scan pays for its vertex visits and the increase of the support cursor sum. -/
theorem delWalkVerts_rangeCost (x : HierConcrete) (lo : ℕ) (vs : List ℕ)
    (hv : ∀ v ∈ vs, v < x.n) :
    rangeCost (delWalkVertsStepCost x lo vs) lo (lo + vs.length) +
        280 * (∑ v ∈ Finset.range x.n, x.ms.st.supCur v) ≤
      445 * vs.length +
        280 * (∑ v ∈ Finset.range x.n, (x.refreshWalkVerts vs).ms.st.supCur v) := by
  let count := fun i => ∑ v ∈ Finset.range x.n,
    (x.refreshWalkVerts (vs.take (i - lo))).ms.st.supCur v
  have H := delRangeCost_le_of_delta (delWalkVertsStepCost x lo vs) count lo vs.length 445 280
    (fun i hlo hi => by
      have hk : i - lo < vs.length := by omega
      have hsub : i + 1 - lo = i - lo + 1 := by omega
      let v := vs[i - lo]
      let y := x.refreshWalkVerts (vs.take (i - lo))
      let n := (x.H.A.C.supportArray v).length
      let old := y.ms.st.supCur v
      let valid := x.H.A.supValid (x.H.A.surv x.ms.st) v
      let next := advance valid n old
      obtain ⟨hH, hLoss, _⟩ := x.refreshWalkVerts_data (vs.take (i - lo))
      have hs : y.H.A.surv y.ms.st = x.H.A.surv x.ms.st := by
        simp only [StaticArrays.surv, y, hH, hLoss]
      have hnext : (x.refreshWalkVerts (vs.take (i + 1 - lo))).ms.st.supCur =
          Function.update y.ms.st.supCur v next := by
        rw [hsub, List.take_succ_eq_append_getElem hk, x.refreshWalkVerts_append_one]
        change Function.update y.ms.st.supCur v
          (advance (y.H.A.supValid (y.H.A.surv y.ms.st) v) (y.H.A.C.supportArray v).length old) = _
        rw [hs, show y.H = x.H from hH]
      have he : count (i + 1) = count i + (next - old) := by
        unfold count
        rw [hnext]
        exact delCursorSum_update _ (hv _ (List.getElem_mem hk)) (le_advance valid n old)
      unfold delWalkVertsStepCost
      rw [List.getD_eq_getElem _ 0 hk, he]
      change 165 + (next - old + 1) * 280 + 280 * count i ≤ 445 + 280 * (count i + (next - old))
      omega)
  simpa only [count, Nat.sub_self, Nat.add_sub_cancel_left, List.take_zero, List.take_length,
    HierConcrete.refreshWalkVerts, List.foldl_nil] using H

/-- The nested walk pass charges its walk lengths once and its support cursor moves once. -/
theorem delWalkPass_rangeCost (x : HierConcrete) (cs : List ℕ)
    (hv : ∀ c ∈ cs, ∀ v ∈ (x.H.A.C.walk c).verts, v < x.n) :
    rangeCost (delWalkPassStepCost x cs) 0 cs.length +
        280 * (∑ v ∈ Finset.range x.n, x.ms.st.supCur v) ≤
      96 * cs.length + (454 * (x.walkPassVerts cs).length +
        280 * (∑ v ∈ Finset.range x.n, (x.refreshWalkVerts (x.walkPassVerts cs)).ms.st.supCur v)) := by
  let count := fun i =>
    let vs := x.walkPassVerts (cs.take i)
    454 * vs.length +
      280 * (∑ v ∈ Finset.range x.n, (x.refreshWalkVerts vs).ms.st.supCur v)
  have H := delRangeCost_le_of_delta (delWalkPassStepCost x cs) count 0 cs.length 96 1
    (fun i _ hi => by
      rw [Nat.zero_add] at hi
      let c := cs[i]
      let seen := x.walkPassVerts (cs.take i)
      let y := x.refreshWalkVerts seen
      let vs := (y.H.A.C.walk c).verts
      let lo := y.walkVertStart c
      have hH : y.H = x.H := (x.refreshWalkVerts_data seen).1
      have hN : y.n = x.n := x.refreshWalkVerts_n seen
      have hv' : ∀ v ∈ vs, v < y.n := by
        unfold vs
        rw [hH, hN]
        exact hv c (List.getElem_mem hi)
      have hcost := delWalkVerts_rangeCost y lo vs hv'
      rw [hN] at hcost
      have hvs : x.walkPassVerts (cs.take (i + 1)) = seen ++ vs := by
        simp only [HierConcrete.walkPassVerts, List.take_succ_eq_append_getElem hi,
          List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, vs, hH]
        rfl
      have hc : count (i + 1) = 454 * (seen.length + vs.length) +
          280 * (∑ v ∈ Finset.range x.n, (y.refreshWalkVerts vs).ms.st.supCur v) := by
        simp only [count, hvs, List.length_append, x.refreshWalkVerts_append]
        rfl
      unfold delWalkPassStepCost
      rw [List.getD_eq_getElem _ 0 hi, hc, Nat.one_mul, Nat.one_mul]
      change rangeCost (delWalkVertsStepCost y lo vs) lo (lo + vs.length) + vs.length * 9 + 96 +
          (454 * seen.length + 280 * (∑ v ∈ Finset.range x.n, y.ms.st.supCur v)) ≤ _
      omega)
  simpa only [Nat.zero_add, Nat.one_mul, count, List.take_zero, List.take_length,
    HierConcrete.walkPassVerts, List.flatMap_nil, List.length_nil, Nat.mul_zero,
    HierConcrete.refreshWalkVerts, List.foldl_nil] using H

private theorem delFailureCost_charge (x b u : ℕ) (L : LossState) :
    delFailureCost x b u L + (700 * L.updates + 130 * L.enumerated) ≤
      408 + (700 * (failStep x b u L).1.updates + 130 * (failStep x b u L).1.enumerated) := by
  let E := (enumerate (failSt1 x b u L) [u]).1
  let Lf := (failStep x b u L).1
  have hLf : Lf = (climb x b u (leafDepth x b) 1 E).1 := by
    unfold Lf
    rw [failStep_eq]
  obtain ⟨hu, he⟩ := climb_counts_mono x b u (leafDepth x b) 1 E
  rw [← hLf] at hu he
  have hU : L.updates ≤ E.updates := by simp [E, enumerate, failSt1]
  have hE : L.enumerated ≤ E.enumerated := by simp [E, enumerate, failSt1]
  have hcost := delFailureCost_events_le x b u L
  change delFailureCost x b u L ≤ delClimbCost L Lf + 400 at hcost
  change delFailureCost x b u L + _ ≤ 408 + (700 * Lf.updates + 130 * Lf.enumerated)
  unfold delClimbCost at hcost
  omega

/-- The reverse scan pays for entries and for actual increases of the loss event counters. -/
theorem delScan_rangeCost (x : HierConcrete) (lo : ℕ) (l : List ℕ) :
    let L := x.ms.st.loss
    let Lf := (scan x.H.A.x x.H.A.b L l).1
    rangeCost (delScanStepCost x l lo) lo (lo + l.length) +
      (700 * L.updates + 130 * L.enumerated) ≤
      1408 * l.length + (700 * Lf.updates + 130 * Lf.enumerated) := by
  dsimp only
  let count := fun i =>
    let L := (scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (i - lo))).1
    700 * L.updates + 130 * L.enumerated
  have H := delRangeCost_le_of_delta (delScanStepCost x l lo) count lo l.length 1408 1
    (fun i hlo hi => by
      have hk : i - lo < l.length := by omega
      have hsub : i + 1 - lo = i - lo + 1 := by omega
      let L := (scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (i - lo))).1
      let t := l[i - lo]
      unfold delScanStepCost
      simp only [List.getD_eq_getElem _ _ hk, Nat.one_mul]
      have hn : scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (i + 1 - lo)) =
          scanStep x.H.A.x x.H.A.b (scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (i - lo))) t := by
        rw [hsub, scan_take_succ _ _ _ hk]
      change 1000 + (if t ∈ L.failed then 0 else delFailureCost x.H.A.x x.H.A.b t L) +
        (700 * L.updates + 130 * L.enumerated) ≤ 1408 + count (i + 1)
      unfold count
      rw [hn]
      by_cases ht : t ∈ L.failed
      · simp only [ite_eq_left ht, Nat.add_zero, scanStep, show
          t ∈ (scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (i - lo))).1.failed from ht]
        change 1000 + (700 * L.updates + 130 * L.enumerated) ≤
          1408 + (700 * L.updates + 130 * L.enumerated)
        omega
      · simp only [ite_eq_right ht, scanStep, show
          t ∉ (scan x.H.A.x x.H.A.b x.ms.st.loss (l.take (i - lo))).1.failed from ht]
        change 1000 + delFailureCost x.H.A.x x.H.A.b t L +
          (700 * L.updates + 130 * L.enumerated) ≤
          1408 + (700 * (failStep x.H.A.x x.H.A.b t L).1.updates +
            130 * (failStep x.H.A.x x.H.A.b t L).1.enumerated)
        have H := delFailureCost_charge x.H.A.x x.H.A.b t L
        omega)
  have hnil : scan x.H.A.x x.H.A.b x.ms.st.loss [] = (x.ms.st.loss, []) := rfl
  simpa only [Nat.one_mul, hnil, count, Nat.sub_self, Nat.add_sub_cancel_left, List.take_zero,
    List.take_length] using H

end MinCostFlow.HierPaths

end
