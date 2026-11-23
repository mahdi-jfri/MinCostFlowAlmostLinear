module

public import MinCostFlow.SparseCore.Program.ContractOrder
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
import WordRAM.Tactic

/-!
# Level-0 `sortedEnds` whole-order builder (`OrdSortedEnds`)

Constructs the `OrdListAt` memory layout for `Bundle.sortedEnds G` directly from
`DynGraphAt mem graph vCap eCap G` in `O(vCap + eCap)` deterministic Word-RAM steps:
1. Pass 1 (`buildSortedEndsPass1`) scans `e = 0 .. eCap - 1` to count the incidence degree
   `(sortedEnds G v).length` of every vertex `v < vCap`.
2. Pass 2 (`buildSortedEndsPass2`) writes the record headers `[v, deg]` at `[out + 1, ...)`
   and initializes each vertex's payload cursor `cur[v]`.
3. Pass 3 (`buildSortedEndsPass3`) scans `e = 0 .. eCap - 1` in strictly increasing edge-ID
   order, appending `2 * e` at `cur[G.tail e]` and `2 * e + 1` at `cur[G.head e]`. Because edge
   IDs increase strictly and `2 * e < 2 * e + 1`, every vertex's list is automatically sorted by
   `endKey` without sorting.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- Pass 1 of `buildSortedEndsBody`: count incidence degrees into `cntBase[0..vCap)`. -/
@[expose] def buildSortedEndsPass1 : Stmt :=
  forRange 10 (.const 0) (.reg 3)
    (.cond (.load (.bin .add (.reg 5) (.reg 10)))
      (.assign 11 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 10))))) ;;
       .assign 12 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 7) (.reg 10))))) ;;
       .store (.bin .add (.reg 8) (.reg 11))
         (.bin .add (.load (.bin .add (.reg 8) (.reg 11))) (.const 1)) ;;
       .store (.bin .add (.reg 8) (.reg 12))
         (.bin .add (.load (.bin .add (.reg 8) (.reg 12))) (.const 1)))
      .nop)

/-- Pass 2 of `buildSortedEndsBody`: write vertex headers `[v, deg]` and initial cursors. -/
@[expose] def buildSortedEndsPass2 : Stmt :=
  forRange 10 (.const 0) (.reg 2)
    (.assign 12 (.load (.bin .add (.reg 8) (.reg 10))) ;;
     .store (.reg 11) (.reg 10) ;;
     .store (.bin .add (.reg 11) (.const 1)) (.reg 12) ;;
     .store (.bin .add (.reg 9) (.reg 10)) (.bin .add (.reg 11) (.const 2)) ;;
     .assign 11 (.bin .add (.bin .add (.reg 11) (.const 2)) (.reg 12)))

/-- Pass 3 of `buildSortedEndsBody`: scatter half-edge keys `2 * e` and `2 * e + 1` in order. -/
@[expose] def buildSortedEndsPass3 : Stmt :=
  forRange 10 (.const 0) (.reg 3)
    (.cond (.load (.bin .add (.reg 5) (.reg 10)))
      (.assign 11 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 10))))) ;;
       .assign 12 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 7) (.reg 10))))) ;;
       .assign 13 (.load (.bin .add (.reg 9) (.reg 11))) ;;
       .store (.reg 13) (.bin .mul (.const 2) (.reg 10)) ;;
       .store (.bin .add (.reg 9) (.reg 11)) (.bin .add (.reg 13) (.const 1)) ;;
       .assign 14 (.load (.bin .add (.reg 9) (.reg 12))) ;;
       .store (.reg 14) (.bin .add (.bin .mul (.const 2) (.reg 10)) (.const 1)) ;;
       .store (.bin .add (.reg 9) (.reg 12)) (.bin .add (.reg 14) (.const 1)))
      .nop)

/-- Deterministic Word-RAM procedure `[graph, out]` (`reg 0..1`) constructing `OrdListAt` for
`Bundle.sortedEnds G` at `out` using scratch `[out + 1 + 2*vCap + 2*eCap, out + 1 + 4*vCap + 2*eCap)`.
Returns `nextHeap = out + 1 + 4*vCap + 2*eCap`. -/
@[expose] def buildSortedEndsBody : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 2))) ;;
  .assign 5 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 2))) ;;
  .assign 6 (.bin .add (.reg 5) (.bin .mul (.const 3) (.reg 3))) ;;
  .assign 7 (.bin .add (.reg 5) (.bin .mul (.const 4) (.reg 3))) ;;
  .assign 8 (.bin .add (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 2) (.reg 2)))
    (.bin .mul (.const 2) (.reg 3))) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 2)) ;;
  buildSortedEndsPass1 ;;
  .store (.reg 1) (.reg 2) ;;
  .assign 11 (.bin .add (.reg 1) (.const 1)) ;;
  buildSortedEndsPass2 ;;
  buildSortedEndsPass3 ;;
  .ret (.bin .add (.reg 9) (.reg 2))

theorem buildSortedEndsBody_noRand : buildSortedEndsBody.NoRand := by
  simp [buildSortedEndsBody, buildSortedEndsPass1, buildSortedEndsPass2, buildSortedEndsPass3,
    forRange, forUp, Stmt.NoRand]

/-- Prefix of `sortedEnds G v` containing only edges with ID `< k`. -/
@[expose] def sortedEndsBelow (G : MGraph) (k v : ℕ) : List End :=
  (sortedEnds G v).filter fun x => decide (x.1 < k)

private theorem sortedEndsBelow_zero (G : MGraph) (v : ℕ) :
    sortedEndsBelow G 0 v = [] := by simp [sortedEndsBelow]

private theorem sortedEndsBelow_all {G : MGraph} {eCap : ℕ}
    (hE : ∀ e ∈ G.E, e < eCap) (v : ℕ) :
    sortedEndsBelow G eCap v = sortedEnds G v := by
  unfold sortedEndsBelow
  rw [List.filter_eq_self]
  intro x hx
  simp [hE x.1 ((mem_sortedEnds G v x).mp hx).1]

private theorem sortedEnds_eq_of_list {xs ys : List End} (hx : xs.Nodup) (hy : ys.Nodup)
    (hsx : xs.Pairwise endLE) (hsy : ys.Pairwise endLE)
    (hm : ∀ x, x ∈ xs ↔ x ∈ ys) : xs = ys :=
  (List.perm_ext_iff_of_nodup hx hy |>.mpr hm).eq_of_pairwise' hsx hsy

private theorem sortedEndsBelow_step_not_mem {G : MGraph} {k : ℕ} (hk : k ∉ G.E) (v : ℕ) :
    sortedEndsBelow G (k + 1) v = sortedEndsBelow G k v := by
  unfold sortedEndsBelow
  apply List.filter_congr
  intro x hx
  have hne : x.1 ≠ k := fun h => hk (h ▸ ((mem_sortedEnds G v x).mp hx).1)
  simp only [decide_eq_decide]; omega

private theorem sortedEndsBelow_step_mem {G : MGraph} {k : ℕ} (hk : k ∈ G.E) (v : ℕ) :
    sortedEndsBelow G (k + 1) v =
      sortedEndsBelow G k v ++
        (if G.tail k = v then [(k, true)] else []) ++
        (if G.head k = v then [(k, false)] else []) := by
  have hndS : (sortedEnds G v).Nodup := (sortedRotation G).nodup v
  have hpwS : (sortedEnds G v).Pairwise endLE := Finset.pairwise_sort _ _
  have hndB : (sortedEndsBelow G k v).Nodup := hndS.filter _
  have hpwB : (sortedEndsBelow G k v).Pairwise endLE := hpwS.filter _
  have hltB : ∀ z ∈ sortedEndsBelow G k v, z.1 < k := fun z hz => by
    have := (List.mem_filter.mp hz).2; simpa using this
  have hnotB : ∀ b : Bool, (k, b) ∉ sortedEndsBelow G k v := fun b hm =>
    Nat.lt_irrefl k (hltB (k, b) hm)
  refine sortedEnds_eq_of_list (hndS.filter _) ?_ (hpwS.filter _) ?_ ?_
  · rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨hndB, by split_ifs <;> simp, fun a ha b hb => by
      split_ifs at hb with ht
      · rw [List.mem_singleton.mp hb]; intro heq; exact hnotB true (heq ▸ ha)
      · simp at hb⟩,
      by split_ifs <;> simp, fun a ha b hb => by
      split_ifs at hb with hh
      · rw [List.mem_singleton.mp hb]; intro heq; subst heq
        rcases List.mem_append.mp ha with hm | hm
        · exact hnotB false hm
        · split_ifs at hm <;> simp at hm
      · simp at hb⟩
  · rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨hpwB, by split_ifs <;> simp, fun a ha b hb => by
      split_ifs at hb with ht
      · rw [List.mem_singleton.mp hb]
        have hlt := hltB a ha
        cases a with | mk f b' => cases b' <;> simp [endLE, endKey] <;> omega
      · simp at hb⟩,
      by split_ifs <;> simp, fun a ha b hb => by
      split_ifs at hb with hh
      · rw [List.mem_singleton.mp hb]
        rcases List.mem_append.mp ha with hm | hm
        · have hlt := hltB a hm
          cases a with | mk f b' => cases b' <;> simp [endLE, endKey] <;> omega
        · split_ifs at hm with ht
          · rw [List.mem_singleton.mp hm]; simp [endLE, endKey]
          · simp at hm
      · simp at hb⟩
  · intro z
    simp only [sortedEndsBelow, List.mem_filter, mem_sortedEnds, decide_eq_true_eq, List.mem_append]
    cases z with
    | mk f b =>
      by_cases hfk : f < k
      · constructor
        · intro ⟨⟨hfE, hfS⟩, _⟩; exact Or.inl (Or.inl ⟨⟨hfE, hfS⟩, hfk⟩)
        · intro h; refine ⟨?_, by omega⟩
          rcases h with (⟨h1, _⟩ | h2) | h3
          · exact h1
          · split_ifs at h2 <;> simp at h2; omega
          · split_ifs at h3 <;> simp at h3; omega
      · by_cases hfeq : f = k
        · subst hfeq
          cases b
          · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte, hk, true_and,
              Nat.lt_succ_self, and_true, Nat.lt_irrefl, and_false, false_or]
            by_cases ht : G.tail f = v <;> by_cases hh : G.head f = v <;> simp [ht, hh]
          · simp only [MGraph.src, ↓reduceIte, hk, true_and,
              Nat.lt_succ_self, and_true, Nat.lt_irrefl, and_false, false_or]
            by_cases ht : G.tail f = v <;> by_cases hh : G.head f = v <;> simp [ht, hh]
        · constructor
          · intro ⟨_, hlt⟩; omega
          · intro h
            rcases h with (⟨_, hlt⟩ | h2) | h3
            · omega
            · split_ifs at h2 <;> simp at h2; exact absurd h2.1 hfeq
            · split_ifs at h3 <;> simp at h3; exact absurd h3.1 hfeq

/-- Sum of `sortedEnds` lengths over `[0, vCap)` equals `2 * G.m`. -/
theorem sum_sortedEnds_length {G : MGraph} {vCap eCap : ℕ}
    (hVal : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap) :
    (Finset.range vCap).sum (fun v => (sortedEnds G v).length) = 2 * G.m := by
  have hbelow : ∀ k : ℕ,
      (Finset.range vCap).sum (fun v => (sortedEndsBelow G k v).length) =
        2 * (G.E.filter fun e => e < k).card := by
    intro k
    induction k with
    | zero => simp [sortedEndsBelow_zero]
    | succ k ih =>
      by_cases hk : k ∈ G.E
      · have hcard : (G.E.filter fun e => e < k + 1).card = (G.E.filter fun e => e < k).card + 1 := by
          have heq : G.E.filter (fun e => e < k + 1) = insert k (G.E.filter fun e => e < k) := by
            ext e; simp only [Finset.mem_filter, Finset.mem_insert]; constructor
            · intro ⟨he, hlt⟩; by_cases h : e = k
              · left; exact h
              · right; exact ⟨he, by omega⟩
            · rintro (rfl | ⟨he, hlt⟩)
              · exact ⟨hk, Nat.lt_succ_self _⟩
              · exact ⟨he, by omega⟩
          rw [heq, Finset.card_insert_of_notMem (by simp)]
        have htLt : G.tail k < vCap := hV _ (hVal k hk).1
        have hhLt : G.head k < vCap := hV _ (hVal k hk).2
        have hstepSum :
            (Finset.range vCap).sum (fun v => (sortedEndsBelow G (k + 1) v).length) =
              (Finset.range vCap).sum (fun v => (sortedEndsBelow G k v).length) +
              (Finset.range vCap).sum (fun v => if G.tail k = v then 1 else 0) +
              (Finset.range vCap).sum (fun v => if G.head k = v then 1 else 0) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v _
          rw [sortedEndsBelow_step_mem hk v, List.length_append, List.length_append]
          split_ifs <;> simp
        rw [hstepSum, ih, hcard]
        have hs1 : (Finset.range vCap).sum (fun v => if G.tail k = v then 1 else 0) = 1 := by
          simp [Finset.mem_range.mpr htLt]
        have hs2 : (Finset.range vCap).sum (fun v => if G.head k = v then 1 else 0) = 1 := by
          simp [Finset.mem_range.mpr hhLt]
        rw [hs1, hs2]; omega
      · have hfilt : G.E.filter (fun e => e < k + 1) = G.E.filter (fun e => e < k) := by
          ext e; simp only [Finset.mem_filter]; constructor
          · intro ⟨he, hlt⟩; exact ⟨he, by have : e ≠ k := fun h => hk (h ▸ he); omega⟩
          · intro ⟨he, hlt⟩; exact ⟨he, by omega⟩
        rw [hfilt, ← ih]
        apply Finset.sum_congr rfl
        intro v _
        rw [sortedEndsBelow_step_not_mem hk v]
  have h1 := hbelow eCap
  have hfiltAll : G.E.filter (fun e => e < eCap) = G.E := by
    ext e; simp only [Finset.mem_filter, and_iff_left_iff_imp]; exact hE e
  rw [hfiltAll] at h1
  have hsumEq : (Finset.range vCap).sum (fun v => (sortedEnds G v).length) =
      (Finset.range vCap).sum (fun v => (sortedEndsBelow G eCap v).length) :=
    Finset.sum_congr rfl (fun v _ => by rw [sortedEndsBelow_all hE v])
  rw [hsumEq, h1]; rfl

/-- Record start offset for vertex `v` in the `OrdListAt` written by `buildSortedEndsBody`. -/
@[expose] def sortedOrdOffset (G : MGraph) (out v : ℕ) : ℕ :=
  out + 1 + (Finset.range v).sum (fun u => 2 + (sortedEnds G u).length)

private theorem sortedOrdOffset_zero (G : MGraph) (out : ℕ) :
    sortedOrdOffset G out 0 = out + 1 := by simp [sortedOrdOffset]

private theorem sortedOrdOffset_succ (G : MGraph) (out v : ℕ) :
    sortedOrdOffset G out (v + 1) = sortedOrdOffset G out v + 2 + (sortedEnds G v).length := by
  simp only [sortedOrdOffset, Finset.sum_range_succ]; omega

private theorem sortedOrdOffset_mono (G : MGraph) (out : ℕ) {u v : ℕ} (h : u ≤ v) :
    sortedOrdOffset G out u ≤ sortedOrdOffset G out v := by
  unfold sortedOrdOffset
  have hle := Finset.sum_le_sum_of_subset (Finset.range_mono h) (f := fun w => 2 + (sortedEnds G w).length)
  omega

private theorem sortedOrdOffset_lt_of_lt (G : MGraph) (out : ℕ) {u v : ℕ} (h : u < v) :
    sortedOrdOffset G out u + 2 + (sortedEnds G u).length ≤ sortedOrdOffset G out v := by
  rw [← sortedOrdOffset_succ]; exact sortedOrdOffset_mono G out (Nat.succ_le_of_lt h)

private theorem endOfKey_endKey (x : End) : endOfKey (endKey x) = x := by
  obtain ⟨e, b⟩ := x
  cases b
  · unfold endKey endOfKey
    have h1 : (2 * e + 1) / 2 = e := by omega
    have h2 : (2 * e + 1) % 2 = 1 := by omega
    simp [h1, h2]
  · unfold endKey endOfKey
    simp [Nat.mul_mod_right]

private theorem readList_map_endOfKey (mem : ℕ → ℕ) :
    ∀ (xs : List End) (b : ℕ),
      (∀ j (hj : j < xs.length), mem (b + j) = endKey xs[j]) →
      (readList mem b xs.length).map endOfKey = xs := by
  intro xs b hb
  apply List.ext_getElem (by simp [readList])
  intro j hj1 hj2
  simp only [readList, List.getElem_map, List.getElem_range]
  rw [hb j hj2, endOfKey_endKey]

private theorem readOrdRecords_of_range {G : MGraph} {mem : ℕ → ℕ} {out vCap : ℕ}
    (hrec : ∀ v < vCap,
      mem (sortedOrdOffset G out v) = v ∧
      mem (sortedOrdOffset G out v + 1) = (sortedEnds G v).length ∧
      ∀ j (hj : j < (sortedEnds G v).length),
        mem (sortedOrdOffset G out v + 2 + j) = endKey (sortedEnds G v)[j]) :
    ∀ k ≤ vCap, ∀ start, start + k = vCap →
      readOrdRecords mem k (sortedOrdOffset G out start) =
        (List.range k).map fun j => (start + j, sortedEnds G (start + j)) := by
  intro k
  induction k with
  | zero => intro _ _ _; rfl
  | succ k ih =>
    intro hk start hsum
    have hsLt : start < vCap := by omega
    obtain ⟨hv, hlen, hkeys⟩ := hrec start hsLt
    dsimp only [readOrdRecords]
    rw [hv, hlen, ← sortedOrdOffset_succ, ih (by omega) (start + 1) (by omega),
      readList_map_endOfKey mem (sortedEnds G start) (sortedOrdOffset G out start + 2) hkeys,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.add_zero, Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

/-- Pass 1 helper: counts incidence degrees into `cntBase[0..vCap)`. -/
private theorem buildSortedEndsPass1_runs
    {w graph out vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool} {st0 : State} {G : MGraph}
    (hVal : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hEPres : ∀ e < eCap, st0.mem (dgEPresBase graph vCap + e) = if e ∈ G.E then 1 else 0)
    (hTail : ∀ e ∈ G.E, st0.mem (dgIntToExtBase graph vCap + st0.mem (dgETailSlotBase graph vCap eCap + e)) = G.tail e ∧
      st0.mem (dgETailSlotBase graph vCap eCap + e) < vCap)
    (hHead : ∀ e ∈ G.E, st0.mem (dgIntToExtBase graph vCap + st0.mem (dgEHeadSlotBase graph vCap eCap + e)) = G.head e ∧
      st0.mem (dgEHeadSlotBase graph vCap eCap + e) < vCap)
    (hbelow : graph + dynGraphSize vCap eCap ≤ out)
    (hzeroCnt : ∀ v < vCap, st0.mem (out + 1 + 2 * vCap + 2 * eCap + v) = 0)
    (hroom : out + 1 + 4 * vCap + 2 * eCap < 2 ^ w)
    (hr3 : st0.regs 3 = eCap) (hr4 : st0.regs 4 = dgIntToExtBase graph vCap)
    (hr5 : st0.regs 5 = dgEPresBase graph vCap) (hr6 : st0.regs 6 = dgETailSlotBase graph vCap eCap)
    (hr7 : st0.regs 7 = dgEHeadSlotBase graph vCap eCap)
    (hr8 : st0.regs 8 = out + 1 + 2 * vCap + 2 * eCap) :
    let cntBase := out + 1 + 2 * vCap + 2 * eCap
    ∃ st1 c1, Runs w p ω buildSortedEndsPass1 st0 .normal st1 c1 ∧
      c1 ≤ 64 * eCap + 10 ∧
      (∀ r ≤ 9, st1.regs r = st0.regs r) ∧ st1.pos = st0.pos ∧
      (∀ v < vCap, st1.mem (cntBase + v) = (sortedEnds G v).length) ∧
      (∀ a, (a < cntBase ∨ cntBase + vCap ≤ a) → st1.mem a = st0.mem a) := by
  dsimp only
  let cntBase := out + 1 + 2 * vCap + 2 * eCap
  have hw1 : 1 < 2 ^ w := by omega
  have hGmLe : G.m ≤ eCap :=
    (Finset.card_le_card (fun e he => Finset.mem_range.mpr (hE e he))).trans (by simp)
  have hdegBound (v : ℕ) (hv : v < vCap) : (sortedEnds G v).length ≤ 2 * G.m := by
    have hsum := sum_sortedEnds_length hVal hV hE
    have hle := Finset.single_le_sum (f := fun u => (sortedEnds G u).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hv)
    omega
  have hdgSz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  let Inv (k : ℕ) (st : State) : Prop :=
    k ≤ eCap ∧ (∀ r ≤ 9, st.regs r = st0.regs r) ∧ st.regs 10 = k ∧ st.pos = st0.pos ∧
    (∀ v < vCap, st.mem (cntBase + v) = (sortedEndsBelow G k v).length) ∧
    (∀ a, (a < cntBase ∨ cntBase + vCap ≤ a) → st.mem a = st0.mem a)
  have hstep : ∀ k, 0 ≤ k → k < eCap →
      Triple w p (Inv k)
        (.cond (.load (.bin .add (.reg 5) (.reg 10)))
          (.assign 11 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 10))))) ;;
           .assign 12 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 7) (.reg 10))))) ;;
           .store (.bin .add (.reg 8) (.reg 11))
             (.bin .add (.load (.bin .add (.reg 8) (.reg 11))) (.const 1)) ;;
           .store (.bin .add (.reg 8) (.reg 12))
             (.bin .add (.load (.bin .add (.reg 8) (.reg 12))) (.const 1)))
          .nop)
        (normalPost fun st' => Inv (k + 1) { st' with regs := Function.update st'.regs 10 (k + 1) } ∧ st'.regs 10 = k)
        (fun _ => 55) := by
    intro k _ hk st bits hInv
    obtain ⟨_, hregs, hr10, hpos, hcnt, hfr⟩ := hInv
    have hs4 : st.regs 4 = dgIntToExtBase graph vCap := (hregs 4 (by decide)).trans hr4
    have hs5 : st.regs 5 = dgEPresBase graph vCap := (hregs 5 (by decide)).trans hr5
    have hs6 : st.regs 6 = dgETailSlotBase graph vCap eCap := (hregs 6 (by decide)).trans hr6
    have hs7 : st.regs 7 = dgEHeadSlotBase graph vCap eCap := (hregs 7 (by decide)).trans hr7
    have hs8 : st.regs 8 = cntBase := (hregs 8 (by decide)).trans hr8
    have hpres : st.mem (dgEPresBase graph vCap + k) = if k ∈ G.E then 1 else 0 :=
      (hfr _ (Or.inl (by dsimp [dgEPresBase, cntBase]; omega))).trans (hEPres k hk)
    by_cases hkE : k ∈ G.E
    · have hcond : (Expr.load (.bin .add (.reg 5) (.reg 10))).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, hs5, hr10, show dgEPresBase graph vCap + k < 2 ^ w by dsimp [dgEPresBase]; omega, hpres, hkE]
      obtain ⟨htEq, htSlot⟩ := hTail k hkE
      obtain ⟨hhEq, hhSlot⟩ := hHead k hkE
      have huLt : G.tail k < vCap := hV _ (hVal k hkE).1
      have hvLt : G.head k < vCap := hV _ (hVal k hkE).2
      have htSlotEq : st.mem (dgETailSlotBase graph vCap eCap + k) = st0.mem (dgETailSlotBase graph vCap eCap + k) :=
        hfr _ (Or.inl (by dsimp [dgETailSlotBase, cntBase]; omega))
      have hhSlotEq : st.mem (dgEHeadSlotBase graph vCap eCap + k) = st0.mem (dgEHeadSlotBase graph vCap eCap + k) :=
        hfr _ (Or.inl (by dsimp [dgEHeadSlotBase, cntBase]; omega))
      have hTailMem : st.mem (dgIntToExtBase graph vCap + st.mem (dgETailSlotBase graph vCap eCap + k)) = G.tail k := by
        rw [htSlotEq]; exact (hfr _ (Or.inl (by dsimp [dgIntToExtBase, cntBase]; omega))).trans htEq
      have hHeadMem : st.mem (dgIntToExtBase graph vCap + st.mem (dgEHeadSlotBase graph vCap eCap + k)) = G.head k := by
        rw [hhSlotEq]; exact (hfr _ (Or.inl (by dsimp [dgIntToExtBase, cntBase]; omega))).trans hhEq
      let c1 := (sortedEndsBelow G k (G.tail k)).length
      have hc1Le : c1 ≤ 2 * G.m := (List.length_filter_le _ _).trans (hdegBound _ huLt)
      let m1 := Function.update st.mem (cntBase + G.tail k) (c1 + 1)
      let c2 := m1 (cntBase + G.head k)
      have hc2Le : c2 ≤ 2 * G.m + 1 := by
        by_cases huv : G.head k = G.tail k
        · dsimp only [c2, m1]; rw [huv, Function.update_self]; omega
        · dsimp only [c2, m1]; rw [Function.update_of_ne (by omega), hcnt _ hvLt]
          exact le_trans ((List.length_filter_le _ _).trans (hdegBound _ hvLt)) (Nat.le_succ _)
      let m2 := Function.update m1 (cntBase + G.head k) (c2 + 1)
      let st1 : State := { st with regs := Function.update st.regs 11 (G.tail k) }
      let st2 : State := { st1 with regs := Function.update st1.regs 12 (G.head k) }
      let st3 : State := { st2 with mem := m1 }
      let st4 : State := { st3 with mem := m2 }
      have p1 : Runs w p bits (.assign 11 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 10)))))) st .normal st1 8 :=
        runs_assign_iff.mpr ⟨G.tail k, by
          simp [Expr.eval, BinOp.eval, hs4, hs6, hr10,
            show dgETailSlotBase graph vCap eCap + k < 2 ^ w by dsimp [dgETailSlotBase]; omega,
            show dgIntToExtBase graph vCap + st.mem (dgETailSlotBase graph vCap eCap + k) < 2 ^ w by
              rw [htSlotEq]; dsimp [dgIntToExtBase]; omega, hTailMem], rfl, rfl, rfl⟩
      have p2 : Runs w p bits (.assign 12 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 7) (.reg 10)))))) st1 .normal st2 8 :=
        runs_assign_iff.mpr ⟨G.head k, by
          simp [Expr.eval, BinOp.eval, st1, hs4, hs7, hr10,
            show dgEHeadSlotBase graph vCap eCap + k < 2 ^ w by dsimp [dgEHeadSlotBase]; omega,
            show dgIntToExtBase graph vCap + st.mem (dgEHeadSlotBase graph vCap eCap + k) < 2 ^ w by
              rw [hhSlotEq]; dsimp [dgIntToExtBase]; omega, hHeadMem], rfl, rfl, rfl⟩
      have p3 : Runs w p bits (.store (.bin .add (.reg 8) (.reg 11)) (.bin .add (.load (.bin .add (.reg 8) (.reg 11))) (.const 1))) st2 .normal st3 10 :=
        runs_store_iff.mpr ⟨cntBase + G.tail k, c1 + 1,
          by simp [Expr.eval, BinOp.eval, st2, st1, hs8, show cntBase + G.tail k < 2 ^ w by omega],
          by simp [Expr.eval, BinOp.eval, st2, st1, hs8, hw1, show cntBase + G.tail k < 2 ^ w by omega,
            hcnt _ huLt, show c1 + 1 < 2 ^ w by omega, c1], rfl, rfl, rfl⟩
      have p4 : Runs w p bits (.store (.bin .add (.reg 8) (.reg 12)) (.bin .add (.load (.bin .add (.reg 8) (.reg 12))) (.const 1))) st3 .normal st4 10 :=
        runs_store_iff.mpr ⟨cntBase + G.head k, c2 + 1,
          by simp [Expr.eval, BinOp.eval, st3, st2, st1, hs8, show cntBase + G.head k < 2 ^ w by omega],
          by simp [Expr.eval, BinOp.eval, st3, st2, st1, hs8, hw1, show cntBase + G.head k < 2 ^ w by omega,
            show c2 + 1 < 2 ^ w by omega, c2], rfl, rfl, rfl⟩
      refine ⟨.normal, st4, 44,
        runs_cond_iff.mpr ⟨1, 39, hcond, by
          simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
          exact runs_seq_iff.mpr (Or.inr ⟨st1, 8, 30, p1,
            runs_seq_iff.mpr (Or.inr ⟨st2, 8, 21, p2,
              runs_seq_iff.mpr (Or.inr ⟨st3, 10, 10, p3, p4, rfl⟩), rfl⟩), rfl⟩),
          by simp [Expr.size]⟩,
        ⟨⟨hk, fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 10), st4, st3, st2, st1,
            Function.update_of_ne (by omega : r ≠ 12), Function.update_of_ne (by omega : r ≠ 11), hregs r hr],
          by simp, hpos, fun v hv => ?_, fun a ha => ?_⟩,
         by simp [st4, st3, st2, st1, hr10]⟩, by dsimp; omega⟩
      · change m2 (cntBase + v) = (sortedEndsBelow G (k + 1) v).length
        rw [sortedEndsBelow_step_mem hkE v, List.length_append, List.length_append]
        by_cases hvh : v = G.head k <;> by_cases hvt : v = G.tail k
        · subst hvh; dsimp only [m2, c2, m1]; rw [Function.update_self, ← hvt, Function.update_self]; simp [hvt, c1]
        · subst hvh; dsimp only [m2, c2, m1]; rw [Function.update_self, Function.update_of_ne (by omega), hcnt _ hv]
          simp [show G.tail k ≠ G.head k by omega]
        · subst hvt; dsimp only [m2, m1]; rw [Function.update_of_ne (by omega), Function.update_self]
          simp [show G.head k ≠ G.tail k by omega, c1]
        · dsimp only [m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hcnt _ hv]
          simp [show G.tail k ≠ v by omega, show G.head k ≠ v by omega]
      · change m2 a = st0.mem a; dsimp only [m2, m1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hfr a ha
    · have hcond : (Expr.load (.bin .add (.reg 5) (.reg 10))).eval w st = some 0 := by
        simp [Expr.eval, BinOp.eval, hs5, hr10, show dgEPresBase graph vCap + k < 2 ^ w by dsimp [dgEPresBase]; omega, hpres, hkE]
      refine ⟨.normal, st, 6,
        runs_cond_iff.mpr ⟨0, 1, hcond, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
          by simp [Expr.size]⟩,
        ⟨⟨hk, fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 10), hregs r hr],
          by simp, hpos, fun v hv => by rw [sortedEndsBelow_step_not_mem hkE v]; exact hcnt v hv, hfr⟩,
         hr10⟩, by dsimp; omega⟩
  have hloop := Triple.forRange_const (p := p) (P := fun st => st = st0) (Inv := Inv)
    (r := 10) (lo := .const 0) (hi := .reg 3) 55 0 eCap (Nat.zero_le _) hw1 (fun _ => by omega)
    (by
      intro st hst; subst hst
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _,
        fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 10)], by simp, rfl,
        fun v hv => by simp [sortedEndsBelow_zero]; exact hzeroCnt v hv, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.1)
    (fun _ st _ _ h => by simp [Expr.eval, (h.2.1 3 (by decide)).trans hr3])
    hstep
  obtain ⟨o, st1, c1, rLoop, hInv1, hc1⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv1
  | normal =>
    obtain ⟨_, hregs1, _, hpos1, hcnt1, hfr1⟩ := hInv1
    refine ⟨st1, c1, rLoop, by simp only [Expr.size] at hc1; omega, hregs1, hpos1,
      fun v hv => by rw [hcnt1 v hv, sortedEndsBelow_all hE v], hfr1⟩

/-- Pass 2 helper: writes headers `[v, deg]` and initializes `curBase[v] := offset[v] + 2`. -/
private theorem buildSortedEndsPass2_runs
    {w out vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool} {st0 : State} {G : MGraph}
    (hVal : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hroom : out + 1 + 4 * vCap + 2 * eCap < 2 ^ w)
    (hw2 : 2 < 2 ^ w)
    (hr2 : st0.regs 2 = vCap)
    (hr8 : st0.regs 8 = out + 1 + 2 * vCap + 2 * eCap)
    (hr9 : st0.regs 9 = out + 1 + 3 * vCap + 2 * eCap)
    (hr11 : st0.regs 11 = out + 1)
    (hout0 : st0.mem out = vCap)
    (hcnt0 : ∀ v < vCap, st0.mem (out + 1 + 2 * vCap + 2 * eCap + v) = (sortedEnds G v).length) :
    let cntBase := out + 1 + 2 * vCap + 2 * eCap
    let curBase := cntBase + vCap
    ∃ st1 c2, Runs w p ω buildSortedEndsPass2 st0 .normal st1 c2 ∧
      c2 ≤ 54 * vCap + 10 ∧
      (∀ r ≤ 9, st1.regs r = st0.regs r) ∧ st1.pos = st0.pos ∧
      st1.mem out = vCap ∧
      (∀ v < vCap,
        st1.mem (sortedOrdOffset G out v) = v ∧
        st1.mem (sortedOrdOffset G out v + 1) = (sortedEnds G v).length ∧
        st1.mem (curBase + v) = sortedOrdOffset G out v + 2) ∧
      (∀ a, (a < out ∨ curBase + vCap ≤ a) → st1.mem a = st0.mem a) := by
  dsimp only
  let cntBase := out + 1 + 2 * vCap + 2 * eCap
  let curBase := cntBase + vCap
  have hw1 : 1 < 2 ^ w := by omega
  have hGmLe : G.m ≤ eCap :=
    (Finset.card_le_card (fun e he => Finset.mem_range.mpr (hE e he))).trans (by simp)
  have hEndOff : sortedOrdOffset G out vCap = out + 1 + 2 * vCap + 2 * G.m := by
    unfold sortedOrdOffset
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      sum_sortedEnds_length hVal hV hE]
    omega
  let Inv (k : ℕ) (st : State) : Prop :=
    k ≤ vCap ∧ (∀ r ≤ 9, st.regs r = st0.regs r) ∧ st.regs 10 = k ∧
    st.regs 11 = sortedOrdOffset G out k ∧ st.pos = st0.pos ∧
    st.mem out = vCap ∧
    (∀ v < vCap, st.mem (cntBase + v) = (sortedEnds G v).length) ∧
    (∀ v < k,
      st.mem (sortedOrdOffset G out v) = v ∧
      st.mem (sortedOrdOffset G out v + 1) = (sortedEnds G v).length ∧
      st.mem (curBase + v) = sortedOrdOffset G out v + 2) ∧
    (∀ a, (a < out ∨ curBase + vCap ≤ a) → st.mem a = st0.mem a)
  have hstep : ∀ k, 0 ≤ k → k < vCap →
      Triple w p (Inv k)
        (.assign 12 (.load (.bin .add (.reg 8) (.reg 10))) ;;
         .store (.reg 11) (.reg 10) ;;
         .store (.bin .add (.reg 11) (.const 1)) (.reg 12) ;;
         .store (.bin .add (.reg 9) (.reg 10)) (.bin .add (.reg 11) (.const 2)) ;;
         .assign 11 (.bin .add (.bin .add (.reg 11) (.const 2)) (.reg 12)))
        (normalPost fun st' => Inv (k + 1) { st' with regs := Function.update st'.regs 10 (k + 1) } ∧ st'.regs 10 = k)
        (fun _ => 45) := by
    intro k _ hk st bits hInv
    obtain ⟨_, hregs, hr10, hr11, hpos, houtM, hcnt, hhdr, hfr⟩ := hInv
    have hs8 : st.regs 8 = cntBase := (hregs 8 (by decide)).trans hr8
    have hs9 : st.regs 9 = curBase := (hregs 9 (by decide)).trans (by dsimp [curBase, cntBase]; omega)
    let off := sortedOrdOffset G out k
    let deg := (sortedEnds G k).length
    have hr11_off : st.regs 11 = off := hr11
    have hoffEnd : off + 2 + deg ≤ cntBase := by
      have h1 : sortedOrdOffset G out (k + 1) ≤ sortedOrdOffset G out vCap := sortedOrdOffset_mono G out hk
      rw [sortedOrdOffset_succ, hEndOff] at h1; dsimp only [off, deg, cntBase]; omega
    have hoffGe : out + 1 ≤ off := sortedOrdOffset_mono G out (Nat.zero_le k)
    let st1 : State := { st with regs := Function.update st.regs 12 deg }
    let m1 := Function.update st.mem off k
    let m2 := Function.update m1 (off + 1) deg
    let m3 := Function.update m2 (curBase + k) (off + 2)
    let st2 : State := { st1 with mem := m1 }
    let st3 : State := { st2 with mem := m2 }
    let st4 : State := { st3 with mem := m3 }
    let st5 : State := { st4 with regs := Function.update st4.regs 11 (off + 2 + deg) }
    have p1 : Runs w p bits (.assign 12 (.load (.bin .add (.reg 8) (.reg 10)))) st .normal st1 5 :=
      runs_assign_iff.mpr ⟨deg, by simp [Expr.eval, BinOp.eval, hs8, hr10, show cntBase + k < 2 ^ w by omega, hcnt k hk, deg], rfl, rfl, rfl⟩
    have p2 : Runs w p bits (.store (.reg 11) (.reg 10)) st1 .normal st2 3 :=
      runs_store_iff.mpr ⟨off, k, by simp [Expr.eval, st1, hr11_off], by simp [Expr.eval, st1, hr10], rfl, rfl, rfl⟩
    have p3 : Runs w p bits (.store (.bin .add (.reg 11) (.const 1)) (.reg 12)) st2 .normal st3 5 :=
      runs_store_iff.mpr ⟨off + 1, deg, by simp [Expr.eval, BinOp.eval, st2, st1, hr11_off, hw1, show off + 1 < 2 ^ w by omega],
        by simp [Expr.eval, st2, st1], rfl, rfl, rfl⟩
    have p4 : Runs w p bits (.store (.bin .add (.reg 9) (.reg 10)) (.bin .add (.reg 11) (.const 2))) st3 .normal st4 7 :=
      runs_store_iff.mpr ⟨curBase + k, off + 2,
        by simp [Expr.eval, BinOp.eval, st3, st2, st1, hs9, hr10, show curBase + k < 2 ^ w by omega],
        by simp [Expr.eval, BinOp.eval, st3, st2, st1, hr11_off, hw2, show off + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have p5 : Runs w p bits (.assign 11 (.bin .add (.bin .add (.reg 11) (.const 2)) (.reg 12))) st4 .normal st5 6 :=
      runs_assign_iff.mpr ⟨off + 2 + deg,
        by simp [Expr.eval, BinOp.eval, st4, st3, st2, st1, hr11_off, hw2, show off + 2 < 2 ^ w by omega,
          show off + 2 + deg < 2 ^ w by omega], rfl, rfl, rfl⟩
    refine ⟨.normal, st5, 30,
      runs_seq_iff.mpr (Or.inr ⟨st1, 5, 24, p1,
      runs_seq_iff.mpr (Or.inr ⟨st2, 3, 20, p2,
      runs_seq_iff.mpr (Or.inr ⟨st3, 5, 14, p3,
      runs_seq_iff.mpr (Or.inr ⟨st4, 7, 6, p4, p5, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      ⟨⟨hk, fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 10), st5, st4, st3, st2, st1,
          Function.update_of_ne (by omega : r ≠ 11), Function.update_of_ne (by omega : r ≠ 12), hregs r hr],
        by simp, by simp [st5, sortedOrdOffset_succ, off, deg], hpos,
        by change m3 out = vCap; dsimp only [m3, m2, m1]
           rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), houtM],
        fun v hv => by
          change m3 (cntBase + v) = _; dsimp only [m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hcnt v hv,
        fun v hv => ?_,
        fun a ha => by
          change m3 a = st0.mem a; dsimp only [m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr a ha⟩,
       by simp [st5, st4, st3, st2, st1, hr10]⟩, by dsimp; omega⟩
    · by_cases hvk : v = k
      · subst hvk
        refine ⟨?_, ?_, ?_⟩
        · change m3 off = v; dsimp only [m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
        · change m3 (off + 1) = deg; dsimp only [m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_self]
        · change m3 (curBase + v) = off + 2; dsimp only [m3]; rw [Function.update_self]
      · have hvlt : v < k := by omega
        have hsep := sortedOrdOffset_lt_of_lt G out hvlt
        obtain ⟨h1, h2, h3⟩ := hhdr v hvlt
        refine ⟨?_, ?_, ?_⟩
        · change m3 (sortedOrdOffset G out v) = v; dsimp only [m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), h1]
        · change m3 (sortedOrdOffset G out v + 1) = _; dsimp only [m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), h2]
        · change m3 (curBase + v) = _; dsimp only [m3, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), h3]
  have hloop := Triple.forRange_const (p := p) (P := fun st => st = st0) (Inv := Inv)
    (r := 10) (lo := .const 0) (hi := .reg 2) 45 0 vCap (Nat.zero_le _) hw1 (fun _ => by omega)
    (by
      intro st hst; subst hst
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _,
        fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 10)], by simp,
        by simp [hr11, sortedOrdOffset_zero], rfl, hout0, hcnt0, fun v hv => by omega, fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.1)
    (fun _ st _ _ h => by simp [Expr.eval, (h.2.1 2 (by decide)).trans hr2])
    hstep
  obtain ⟨o, st1, c2, rLoop, hInv2, hc2⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv2
  | normal =>
    obtain ⟨_, hregs2, _, _, hpos2, hout2, _, hhdr2, hfr2⟩ := hInv2
    exact ⟨st1, c2, rLoop, by simp only [Expr.size] at hc2; omega, hregs2, hpos2, hout2, hhdr2, hfr2⟩

/-- Pass 3 helper: scatters half-edge keys `2 * e` and `2 * e + 1` in strictly increasing `e` order. -/
private theorem buildSortedEndsPass3_runs
    {w graph out vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool} {st0 : State} {G : MGraph}
    (hVal : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hEPres : ∀ e < eCap, st0.mem (dgEPresBase graph vCap + e) = if e ∈ G.E then 1 else 0)
    (hTail : ∀ e ∈ G.E, st0.mem (dgIntToExtBase graph vCap + st0.mem (dgETailSlotBase graph vCap eCap + e)) = G.tail e ∧
      st0.mem (dgETailSlotBase graph vCap eCap + e) < vCap)
    (hHead : ∀ e ∈ G.E, st0.mem (dgIntToExtBase graph vCap + st0.mem (dgEHeadSlotBase graph vCap eCap + e)) = G.head e ∧
      st0.mem (dgEHeadSlotBase graph vCap eCap + e) < vCap)
    (hbelow : graph + dynGraphSize vCap eCap ≤ out)
    (hroom : out + 1 + 4 * vCap + 2 * eCap < 2 ^ w)
    (hw2 : 2 < 2 ^ w)
    (hr3 : st0.regs 3 = eCap) (hr4 : st0.regs 4 = dgIntToExtBase graph vCap)
    (hr5 : st0.regs 5 = dgEPresBase graph vCap) (hr6 : st0.regs 6 = dgETailSlotBase graph vCap eCap)
    (hr7 : st0.regs 7 = dgEHeadSlotBase graph vCap eCap)
    (hr9 : st0.regs 9 = out + 1 + 3 * vCap + 2 * eCap)
    (hout0 : st0.mem out = vCap)
    (hhdr0 : ∀ v < vCap,
      st0.mem (sortedOrdOffset G out v) = v ∧
      st0.mem (sortedOrdOffset G out v + 1) = (sortedEnds G v).length ∧
      st0.mem (out + 1 + 3 * vCap + 2 * eCap + v) = sortedOrdOffset G out v + 2) :
    let curBase := out + 1 + 3 * vCap + 2 * eCap
    ∃ st1 c3, Runs w p ω buildSortedEndsPass3 st0 .normal st1 c3 ∧
      c3 ≤ 79 * eCap + 10 ∧
      (∀ r ≤ 9, st1.regs r = st0.regs r) ∧ st1.pos = st0.pos ∧
      st1.mem out = vCap ∧
      (∀ v < vCap,
        st1.mem (sortedOrdOffset G out v) = v ∧
        st1.mem (sortedOrdOffset G out v + 1) = (sortedEnds G v).length ∧
        ∀ j (hj : j < (sortedEnds G v).length),
          st1.mem (sortedOrdOffset G out v + 2 + j) = endKey (sortedEnds G v)[j]) ∧
      (∀ a, (a < out ∨ curBase + vCap ≤ a) → st1.mem a = st0.mem a) := by
  dsimp only
  let cntBase := out + 1 + 2 * vCap + 2 * eCap
  let curBase := out + 1 + 3 * vCap + 2 * eCap
  have hw1 : 1 < 2 ^ w := by omega
  have hdgSz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hGmLe : G.m ≤ eCap :=
    (Finset.card_le_card (fun e he => Finset.mem_range.mpr (hE e he))).trans (by simp)
  have hEndOff : sortedOrdOffset G out vCap = out + 1 + 2 * vCap + 2 * G.m := by
    unfold sortedOrdOffset
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      sum_sortedEnds_length hVal hV hE]
    omega
  let Inv (k : ℕ) (st : State) : Prop :=
    k ≤ eCap ∧ (∀ r ≤ 9, st.regs r = st0.regs r) ∧ st.regs 10 = k ∧ st.pos = st0.pos ∧
    st.mem out = vCap ∧
    (∀ v < vCap,
      st.mem (sortedOrdOffset G out v) = v ∧
      st.mem (sortedOrdOffset G out v + 1) = (sortedEnds G v).length ∧
      st.mem (curBase + v) = sortedOrdOffset G out v + 2 + (sortedEndsBelow G k v).length ∧
      ∀ j (hj : j < (sortedEndsBelow G k v).length),
        st.mem (sortedOrdOffset G out v + 2 + j) = endKey (sortedEndsBelow G k v)[j]) ∧
    (∀ a, (a < out ∨ curBase + vCap ≤ a) → st.mem a = st0.mem a)
  have hstep : ∀ k, 0 ≤ k → k < eCap →
      Triple w p (Inv k)
        (.cond (.load (.bin .add (.reg 5) (.reg 10)))
          (.assign 11 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 10))))) ;;
           .assign 12 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 7) (.reg 10))))) ;;
           .assign 13 (.load (.bin .add (.reg 9) (.reg 11))) ;;
           .store (.reg 13) (.bin .mul (.const 2) (.reg 10)) ;;
           .store (.bin .add (.reg 9) (.reg 11)) (.bin .add (.reg 13) (.const 1)) ;;
           .assign 14 (.load (.bin .add (.reg 9) (.reg 12))) ;;
           .store (.reg 14) (.bin .add (.bin .mul (.const 2) (.reg 10)) (.const 1)) ;;
           .store (.bin .add (.reg 9) (.reg 12)) (.bin .add (.reg 14) (.const 1)))
          .nop)
        (normalPost fun st' => Inv (k + 1) { st' with regs := Function.update st'.regs 10 (k + 1) } ∧ st'.regs 10 = k)
        (fun _ => 70) := by
    intro k _ hk st bits hInv
    obtain ⟨_, hregs, hr10, hpos, houtM, hrec, hfr⟩ := hInv
    have hs4 : st.regs 4 = dgIntToExtBase graph vCap := (hregs 4 (by decide)).trans hr4
    have hs5 : st.regs 5 = dgEPresBase graph vCap := (hregs 5 (by decide)).trans hr5
    have hs6 : st.regs 6 = dgETailSlotBase graph vCap eCap := (hregs 6 (by decide)).trans hr6
    have hs7 : st.regs 7 = dgEHeadSlotBase graph vCap eCap := (hregs 7 (by decide)).trans hr7
    have hs9 : st.regs 9 = curBase := (hregs 9 (by decide)).trans hr9
    have hpres : st.mem (dgEPresBase graph vCap + k) = if k ∈ G.E then 1 else 0 :=
      (hfr _ (Or.inl (by dsimp [dgEPresBase]; omega))).trans (hEPres k hk)
    by_cases hkE : k ∈ G.E
    · have hcond : (Expr.load (.bin .add (.reg 5) (.reg 10))).eval w st = some 1 := by
        simp [Expr.eval, BinOp.eval, hs5, hr10, show dgEPresBase graph vCap + k < 2 ^ w by dsimp [dgEPresBase]; omega, hpres, hkE]
      obtain ⟨htEq, htSlot⟩ := hTail k hkE
      obtain ⟨hhEq, hhSlot⟩ := hHead k hkE
      have huLt : G.tail k < vCap := hV _ (hVal k hkE).1
      have hvLt : G.head k < vCap := hV _ (hVal k hkE).2
      have htSlotEq : st.mem (dgETailSlotBase graph vCap eCap + k) = st0.mem (dgETailSlotBase graph vCap eCap + k) :=
        hfr _ (Or.inl (by dsimp [dgETailSlotBase]; omega))
      have hhSlotEq : st.mem (dgEHeadSlotBase graph vCap eCap + k) = st0.mem (dgEHeadSlotBase graph vCap eCap + k) :=
        hfr _ (Or.inl (by dsimp [dgEHeadSlotBase]; omega))
      have hTailMem : st.mem (dgIntToExtBase graph vCap + st.mem (dgETailSlotBase graph vCap eCap + k)) = G.tail k := by
        rw [htSlotEq]; exact (hfr _ (Or.inl (by dsimp [dgIntToExtBase]; omega))).trans htEq
      have hHeadMem : st.mem (dgIntToExtBase graph vCap + st.mem (dgEHeadSlotBase graph vCap eCap + k)) = G.head k := by
        rw [hhSlotEq]; exact (hfr _ (Or.inl (by dsimp [dgIntToExtBase]; omega))).trans hhEq
      let u := G.tail k
      let v := G.head k
      let pu := sortedOrdOffset G out u + 2 + (sortedEndsBelow G k u).length
      have hpuLt : pu < sortedOrdOffset G out (u + 1) := by
        have hstep := sortedEndsBelow_step_mem hkE u
        have hlenLe : (sortedEndsBelow G (k + 1) u).length ≤ (sortedEnds G u).length := List.length_filter_le _ _
        rw [hstep, List.length_append, List.length_append, ite_eq_left rfl, List.length_singleton] at hlenLe
        rw [sortedOrdOffset_succ]; dsimp only [pu]; omega
      have hpuEnd : pu + 1 ≤ cntBase := by
        have := sortedOrdOffset_mono G out (show u + 1 ≤ vCap by omega)
        rw [hEndOff] at this; dsimp only [cntBase]; omega
      let m1 := Function.update st.mem pu (2 * k)
      let m2 := Function.update m1 (curBase + u) (pu + 1)
      let pv := m2 (curBase + v)
      have hpvEq : pv = sortedOrdOffset G out v + 2 + (sortedEndsBelow G k v).length +
          (if v = u then 1 else 0) := by
        by_cases hvu : v = u
        · dsimp only [pv, m2]; rw [hvu, Function.update_self]; simp [pu]
        · dsimp only [pv, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), (hrec v hvLt).2.2.1]
          simp [hvu]
      have hpvLt : pv < sortedOrdOffset G out (v + 1) := by
        have hstep := sortedEndsBelow_step_mem hkE v
        have hlenLe : (sortedEndsBelow G (k + 1) v).length ≤ (sortedEnds G v).length := List.length_filter_le _ _
        rw [hstep, List.length_append, List.length_append, ite_eq_left rfl, List.length_singleton] at hlenLe
        rw [sortedOrdOffset_succ, hpvEq]
        by_cases hvu : v = u
        · have htu : G.tail k = v := hvu.symm
          simp only [hvu, htu, ↓reduceIte, List.length_singleton] at hlenLe ⊢; omega
        · have hne : G.tail k ≠ v := fun h => hvu h.symm
          simp only [hne, hvu, ↓reduceIte, List.length_nil] at hlenLe ⊢; omega
      have hpvEnd : pv + 1 ≤ cntBase := by
        have := sortedOrdOffset_mono G out (show v + 1 ≤ vCap by omega)
        rw [hEndOff] at this; dsimp only [cntBase]; omega
      have hpvNePu : pv ≠ pu := by
        by_cases hvu : v = u
        · rw [hpvEq, ite_eq_left hvu, hvu]; dsimp only [pu]; omega
        · by_cases hlt : v < u
          · have := sortedOrdOffset_lt_of_lt G out hlt; rw [← sortedOrdOffset_succ] at this
            dsimp only [pu]; omega
          · have hlt' : u < v := by omega
            have := sortedOrdOffset_lt_of_lt G out hlt'; rw [← sortedOrdOffset_succ] at this
            rw [hpvEq]; omega
      let m3 := Function.update m2 pv (2 * k + 1)
      let m4 := Function.update m3 (curBase + v) (pv + 1)
      let st1 : State := { st with regs := Function.update st.regs 11 u }
      let st2 : State := { st1 with regs := Function.update st1.regs 12 v }
      let st3 : State := { st2 with regs := Function.update st2.regs 13 pu }
      let st4 : State := { st3 with mem := m1 }
      let st5 : State := { st4 with mem := m2 }
      let st6 : State := { st5 with regs := Function.update st5.regs 14 pv }
      let st7 : State := { st6 with mem := m3 }
      let st8 : State := { st7 with mem := m4 }
      have p1 : Runs w p bits (.assign 11 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 6) (.reg 10)))))) st .normal st1 8 :=
        runs_assign_iff.mpr ⟨u, by
          simp [Expr.eval, BinOp.eval, hs4, hs6, hr10,
            show dgETailSlotBase graph vCap eCap + k < 2 ^ w by dsimp [dgETailSlotBase]; omega,
            show dgIntToExtBase graph vCap + st.mem (dgETailSlotBase graph vCap eCap + k) < 2 ^ w by
              rw [htSlotEq]; dsimp [dgIntToExtBase]; omega, hTailMem, u], rfl, rfl, rfl⟩
      have p2 : Runs w p bits (.assign 12 (.load (.bin .add (.reg 4) (.load (.bin .add (.reg 7) (.reg 10)))))) st1 .normal st2 8 :=
        runs_assign_iff.mpr ⟨v, by
          simp [Expr.eval, BinOp.eval, st1, hs4, hs7, hr10,
            show dgEHeadSlotBase graph vCap eCap + k < 2 ^ w by dsimp [dgEHeadSlotBase]; omega,
            show dgIntToExtBase graph vCap + st.mem (dgEHeadSlotBase graph vCap eCap + k) < 2 ^ w by
              rw [hhSlotEq]; dsimp [dgIntToExtBase]; omega, hHeadMem, v], rfl, rfl, rfl⟩
      have p3 : Runs w p bits (.assign 13 (.load (.bin .add (.reg 9) (.reg 11)))) st2 .normal st3 5 :=
        runs_assign_iff.mpr ⟨pu, by
          simp [Expr.eval, BinOp.eval, st2, st1, hs9, show curBase + u < 2 ^ w by omega, (hrec u huLt).2.2.1, pu],
          rfl, rfl, rfl⟩
      have p4 : Runs w p bits (.store (.reg 13) (.bin .mul (.const 2) (.reg 10))) st3 .normal st4 5 :=
        runs_store_iff.mpr ⟨pu, 2 * k, by simp [Expr.eval, st3],
          by simp [Expr.eval, BinOp.eval, st3, st2, st1, hr10, hw2, show 2 * k < 2 ^ w by omega], rfl, rfl, rfl⟩
      have p5 : Runs w p bits (.store (.bin .add (.reg 9) (.reg 11)) (.bin .add (.reg 13) (.const 1))) st4 .normal st5 7 :=
        runs_store_iff.mpr ⟨curBase + u, pu + 1,
          by simp [Expr.eval, BinOp.eval, st4, st3, st2, st1, hs9, show curBase + u < 2 ^ w by omega],
          by simp [Expr.eval, BinOp.eval, st4, st3, hw1, show pu + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have p6 : Runs w p bits (.assign 14 (.load (.bin .add (.reg 9) (.reg 12)))) st5 .normal st6 5 :=
        runs_assign_iff.mpr ⟨pv, by
          simp [Expr.eval, BinOp.eval, st5, st4, st3, st2, st1, hs9, show curBase + v < 2 ^ w by omega, pv],
          rfl, rfl, rfl⟩
      have p7 : Runs w p bits (.store (.reg 14) (.bin .add (.bin .mul (.const 2) (.reg 10)) (.const 1))) st6 .normal st7 7 :=
        runs_store_iff.mpr ⟨pv, 2 * k + 1, by simp [Expr.eval, st6],
          by simp [Expr.eval, BinOp.eval, st6, st5, st4, st3, st2, st1, hr10, hw1, hw2,
            show 2 * k < 2 ^ w by omega, show 2 * k + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have p8 : Runs w p bits (.store (.bin .add (.reg 9) (.reg 12)) (.bin .add (.reg 14) (.const 1))) st7 .normal st8 7 :=
        runs_store_iff.mpr ⟨curBase + v, pv + 1,
          by simp [Expr.eval, BinOp.eval, st7, st6, st5, st4, st3, st2, st1, hs9, show curBase + v < 2 ^ w by omega],
          by simp [Expr.eval, BinOp.eval, st7, st6, hw1, show pv + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hpuGe : out + 1 ≤ pu := le_trans (sortedOrdOffset_mono G out (Nat.zero_le u)) (by dsimp [pu]; omega)
      have hpvGe : out + 1 ≤ pv := le_trans (sortedOrdOffset_mono G out (Nat.zero_le v)) (by rw [hpvEq]; omega)
      have hm4_ne (a : ℕ) (h1 : a ≠ pu) (h2 : a ≠ pv) (h3 : a ≠ curBase + u) (h4 : a ≠ curBase + v) :
          m4 a = st.mem a := by
        dsimp only [m4, m3, m2, m1]
        rw [Function.update_of_ne h4, Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h1]
      have hpu_not_hdr (x : ℕ) (hx : x < vCap) : sortedOrdOffset G out x ≠ pu ∧ sortedOrdOffset G out x + 1 ≠ pu := by
        by_cases hxu : x = u
        · subst hxu; dsimp only [pu]; omega
        · by_cases hlt : x < u
          · have := sortedOrdOffset_lt_of_lt G out hlt; dsimp only [pu]; omega
          · have := sortedOrdOffset_lt_of_lt G out (show u < x by omega); rw [← sortedOrdOffset_succ] at this; omega
      have hpv_not_hdr (x : ℕ) (hx : x < vCap) : sortedOrdOffset G out x ≠ pv ∧ sortedOrdOffset G out x + 1 ≠ pv := by
        by_cases hxv : x = v
        · subst hxv; rw [hpvEq]; omega
        · by_cases hlt : x < v
          · have := sortedOrdOffset_lt_of_lt G out hlt; rw [hpvEq]; omega
          · have := sortedOrdOffset_lt_of_lt G out (show v < x by omega); rw [← sortedOrdOffset_succ] at this; omega
      refine ⟨.normal, st8, 64,
        runs_cond_iff.mpr ⟨1, 59, hcond, by
          simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
          exact runs_seq_iff.mpr (Or.inr ⟨st1, 8, 50, p1,
            runs_seq_iff.mpr (Or.inr ⟨st2, 8, 41, p2,
              runs_seq_iff.mpr (Or.inr ⟨st3, 5, 35, p3,
                runs_seq_iff.mpr (Or.inr ⟨st4, 5, 29, p4,
                  runs_seq_iff.mpr (Or.inr ⟨st5, 7, 21, p5,
                    runs_seq_iff.mpr (Or.inr ⟨st6, 5, 15, p6,
                      runs_seq_iff.mpr (Or.inr ⟨st7, 7, 7, p7, p8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
          by simp [Expr.size]⟩,
        ⟨⟨hk, fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 10), st8, st7, st6, st5, st4, st3, st2, st1,
            Function.update_of_ne (by omega : r ≠ 14), Function.update_of_ne (by omega : r ≠ 13),
            Function.update_of_ne (by omega : r ≠ 12), Function.update_of_ne (by omega : r ≠ 11), hregs r hr],
          by simp, hpos,
          by change m4 out = vCap; rw [hm4_ne out (by omega) (by omega) (by omega) (by omega), houtM],
          fun x hx => ?_,
          fun a ha => by
            change m4 a = st0.mem a
            rw [hm4_ne a (by omega) (by omega) (by omega) (by omega)]; exact hfr a ha⟩,
         by simp [st8, st7, st6, st5, st4, st3, st2, st1, hr10]⟩, by dsimp; omega⟩
      · have hxOff : sortedOrdOffset G out x + 1 < cntBase := by
          have h1 := sortedOrdOffset_mono G out (show x + 1 ≤ vCap by omega)
          rw [sortedOrdOffset_succ, hEndOff] at h1; dsimp only [cntBase]; omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · change m4 (sortedOrdOffset G out x) = x
          rw [hm4_ne _ (hpu_not_hdr x hx).1 (hpv_not_hdr x hx).1 (by omega) (by omega), (hrec x hx).1]
        · change m4 (sortedOrdOffset G out x + 1) = (sortedEnds G x).length
          rw [hm4_ne _ (hpu_not_hdr x hx).2 (hpv_not_hdr x hx).2 (by omega) (by omega), (hrec x hx).2.1]
        · change m4 (curBase + x) = _
          rw [sortedEndsBelow_step_mem hkE x, List.length_append, List.length_append]
          by_cases hxv : x = v <;> by_cases hxu : x = u
          · rw [hxv]; dsimp only [m4]; rw [Function.update_self, hpvEq]
            have hvu : v = u := hxv.symm.trans hxu
            have htu : G.tail k = v := hvu.symm
            simp [hvu, htu, v]; omega
          · rw [hxv]; dsimp only [m4]; rw [Function.update_self, hpvEq]
            have hvu : v ≠ u := fun h => hxu (hxv.trans h)
            have hne : G.tail k ≠ v := fun h => hvu h.symm
            simp [hvu, hne, v]; omega
          · rw [hxu]; dsimp only [m4, m3, m2]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
            have hne : G.head k ≠ u := fun h => hxv (hxu.trans h.symm)
            simp [hne, pu, u]; omega
          · rw [hm4_ne (curBase + x) (by omega) (by omega) (by omega) (by omega), (hrec x hx).2.2.1]
            have hne1 : G.tail k ≠ x := fun h => hxu h.symm
            have hne2 : G.head k ≠ x := fun h => hxv h.symm
            simp [hne1, hne2]
        · intro j hj
          change m4 (sortedOrdOffset G out x + 2 + j) = endKey (sortedEndsBelow G (k + 1) x)[j]
          have hstep := sortedEndsBelow_step_mem hkE x
          by_cases hjOld : j < (sortedEndsBelow G k x).length
          · have hnePu : sortedOrdOffset G out x + 2 + j ≠ pu := by
              by_cases hxu : x = u
              · rw [hxu] at hjOld ⊢; dsimp only [pu]; omega
              · by_cases hlt : x < u
                · have h1 := sortedOrdOffset_lt_of_lt G out hlt
                  have h2 : (sortedEndsBelow G k x).length ≤ (sortedEnds G x).length := List.length_filter_le _ _
                  dsimp only [pu]; omega
                · have h1 := sortedOrdOffset_lt_of_lt G out (show u < x by omega); rw [← sortedOrdOffset_succ] at h1; omega
            have hnePv : sortedOrdOffset G out x + 2 + j ≠ pv := by
              by_cases hxv : x = v
              · rw [hxv] at hjOld ⊢; rw [hpvEq]; omega
              · by_cases hlt : x < v
                · have h1 := sortedOrdOffset_lt_of_lt G out hlt
                  have h2 : (sortedEndsBelow G k x).length ≤ (sortedEnds G x).length := List.length_filter_le _ _
                  rw [hpvEq]; omega
                · have h1 := sortedOrdOffset_lt_of_lt G out (show v < x by omega); rw [← sortedOrdOffset_succ] at h1; omega
            have hltCnt : sortedOrdOffset G out x + 2 + j < cntBase := by
              have h1 := sortedOrdOffset_mono G out (show x + 1 ≤ vCap by omega)
              have h2 : (sortedEndsBelow G k x).length ≤ (sortedEnds G x).length := List.length_filter_le _ _
              rw [sortedOrdOffset_succ, hEndOff] at h1; dsimp only [cntBase]; omega
            rw [hm4_ne _ hnePu hnePv (by omega) (by omega), (hrec x hx).2.2.2 j hjOld]
            congr 1
            have hget : (sortedEndsBelow G (k + 1) x)[j] = (sortedEndsBelow G k x)[j] := by
              simp only [hstep, List.append_assoc]; exact List.getElem_append_left hjOld
            exact hget.symm
          · have hj' := hj; rw [hstep, List.length_append, List.length_append] at hj'
            by_cases hxu : x = u <;> by_cases hxv : x = v
            · have htx : G.tail k = x := hxu.symm
              have hhx : G.head k = x := hxv.symm
              have hvu : v = u := hxv.symm.trans hxu
              simp only [htx, hhx, ↓reduceIte, List.length_singleton] at hj'
              by_cases hjEq : j = (sortedEndsBelow G k x).length
              · have haddr : sortedOrdOffset G out x + 2 + j = pu := by rw [hxu] at hjEq ⊢; dsimp only [pu]; omega
                rw [haddr]; dsimp only [m4, m3, m2, m1]
                rw [Function.update_of_ne (by omega), Function.update_of_ne hpvNePu.symm,
                  Function.update_of_ne (by omega), Function.update_self]
                have hget : (sortedEndsBelow G (k + 1) x)[j] = (k, true) := by
                  simp only [hstep, htx, hhx, ↓reduceIte, List.append_assoc]
                  rw [List.getElem_append_right (by omega)]; simp [hjEq]
                rw [hget]; simp [endKey]
              · have hjEq2 : j = (sortedEndsBelow G k x).length + 1 := by omega
                have haddr : sortedOrdOffset G out x + 2 + j = pv := by
                  rw [hxv] at hjEq2 ⊢; rw [hpvEq, ite_eq_left hvu]; omega
                rw [haddr]; dsimp only [m4, m3]
                rw [Function.update_of_ne (by omega), Function.update_self]
                have hget : (sortedEndsBelow G (k + 1) x)[j] = (k, false) := by
                  simp only [hstep, htx, hhx, ↓reduceIte, List.append_assoc]
                  rw [List.getElem_append_right (by omega)]; simp [hjEq2]
                rw [hget]; simp [endKey]
            · have htx : G.tail k = x := hxu.symm
              have hne : G.head k ≠ x := fun h => hxv h.symm
              simp only [htx, hne, ↓reduceIte, List.length_singleton, List.length_nil] at hj'
              have hjEq : j = (sortedEndsBelow G k x).length := by omega
              have haddr : sortedOrdOffset G out x + 2 + j = pu := by rw [hxu] at hjEq ⊢; dsimp only [pu]; omega
              rw [haddr]; dsimp only [m4, m3, m2, m1]
              rw [Function.update_of_ne (by omega), Function.update_of_ne hpvNePu.symm,
                Function.update_of_ne (by omega), Function.update_self]
              have hget : (sortedEndsBelow G (k + 1) x)[j] = (k, true) := by
                simp only [hstep, htx, hne, ↓reduceIte, List.append_nil]
                rw [List.getElem_append_right (by omega)]; simp [hjEq]
              rw [hget]; simp [endKey]
            · have hhx : G.head k = x := hxv.symm
              have hne : G.tail k ≠ x := fun h => hxu h.symm
              have hvu : v ≠ u := fun h => hxu (hxv.trans h)
              simp only [hhx, hne, ↓reduceIte, List.length_singleton, List.length_nil] at hj'
              have hjEq : j = (sortedEndsBelow G k x).length := by omega
              have haddr : sortedOrdOffset G out x + 2 + j = pv := by
                rw [hxv] at hjEq ⊢; rw [hpvEq, ite_eq_right hvu]; omega
              rw [haddr]; dsimp only [m4, m3]
              rw [Function.update_of_ne (by omega), Function.update_self]
              have hget : (sortedEndsBelow G (k + 1) x)[j] = (k, false) := by
                simp only [hstep, hhx, hne, ↓reduceIte, List.append_nil]
                rw [List.getElem_append_right (by omega)]; simp [hjEq]
              rw [hget]; simp [endKey]
            · have hne1 : G.tail k ≠ x := fun h => hxu h.symm
              have hne2 : G.head k ≠ x := fun h => hxv h.symm
              simp only [hne1, hne2, ↓reduceIte, List.length_nil] at hj'; omega
    · have hcond : (Expr.load (.bin .add (.reg 5) (.reg 10))).eval w st = some 0 := by
        simp [Expr.eval, BinOp.eval, hs5, hr10, show dgEPresBase graph vCap + k < 2 ^ w by dsimp [dgEPresBase]; omega, hpres, hkE]
      refine ⟨.normal, st, 6,
        runs_cond_iff.mpr ⟨0, 1, hcond, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
          by simp [Expr.size]⟩,
        ⟨⟨hk, fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 10), hregs r hr],
          by simp, hpos, houtM, fun x hx => by
            have hstep := sortedEndsBelow_step_not_mem hkE x
            refine ⟨(hrec x hx).1, (hrec x hx).2.1, ?_, ?_⟩
            · rw [hstep]; exact (hrec x hx).2.2.1
            · intro j hj
              have hj' : j < (sortedEndsBelow G k x).length := by rwa [hstep] at hj
              have hget : (sortedEndsBelow G (k + 1) x)[j] = (sortedEndsBelow G k x)[j] := by simp [hstep]
              rw [hget]; exact (hrec x hx).2.2.2 j hj',
          hfr⟩, hr10⟩, by dsimp; omega⟩
  have hloop := Triple.forRange_const (p := p) (P := fun st => st = st0) (Inv := Inv)
    (r := 10) (lo := .const 0) (hi := .reg 3) 70 0 eCap (Nat.zero_le _) hw1 (fun _ => by omega)
    (by
      intro st hst; subst hst
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], Nat.zero_le _,
        fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 10)], by simp, rfl, hout0,
        fun v hv => ⟨(hhdr0 v hv).1, (hhdr0 v hv).2.1,
          by simp [sortedEndsBelow_zero]; exact (hhdr0 v hv).2.2,
          fun j hj => by simp [sortedEndsBelow_zero] at hj⟩,
        fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.1)
    (fun _ st _ _ h => by simp [Expr.eval, (h.2.1 3 (by decide)).trans hr3])
    hstep
  obtain ⟨o, st1, c3, rLoop, hInv3, hc3⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hInv3
  | normal =>
    obtain ⟨_, hregs3, _, hpos3, hout3, hrec3, hfr3⟩ := hInv3
    refine ⟨st1, c3, rLoop, by simp only [Expr.size] at hc3; omega, hregs3, hpos3, hout3,
      fun v hv => ⟨(hrec3 v hv).1, (hrec3 v hv).2.1, fun j hj => by
        have h := (hrec3 v hv).2.2.2 j (by rwa [sortedEndsBelow_all hE v])
        simpa [sortedEndsBelow_all hE v] using h⟩, hfr3⟩

private theorem find?_map_range_pair (f : ℕ → List End) :
    ∀ n v, ((List.range n).map fun u => (u, f u)).find? (fun p => p.1 == v) =
      if v < n then some (v, f v) else none := by
  intro n
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [List.range_succ, List.map_append, List.map_singleton, List.find?_append, ih v]
    by_cases hlt : v < n
    · have hlt' : v < n + 1 := by omega
      simp [hlt, hlt']
    · simp only [hlt, ↓reduceIte, Option.none_or, List.find?_singleton]
      by_cases heq : n = v
      · subst heq; simp
      · have hlt' : ¬ v < n + 1 := by omega
        simp [heq, hlt']

private theorem ordListAt_of_sortedEnds_records {G : MGraph} {mem : ℕ → ℕ} {out vCap eCap : ℕ}
    (hVal : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hout : mem out = vCap)
    (hrec : ∀ v < vCap,
      mem (sortedOrdOffset G out v) = v ∧
      mem (sortedOrdOffset G out v + 1) = (sortedEnds G v).length ∧
      ∀ j (hj : j < (sortedEnds G v).length),
        mem (sortedOrdOffset G out v + 2 + j) = endKey (sortedEnds G v)[j]) :
    OrdListAt mem out (sortedEnds G) (1 + 2 * vCap + 2 * G.m) := by
  have hrecs : readOrdRecordsAt mem out = (List.range vCap).map fun v => (v, sortedEnds G v) := by
    unfold readOrdRecordsAt
    rw [hout, ← sortedOrdOffset_zero G out]
    simpa using readOrdRecords_of_range (G := G) (mem := mem) (out := out) (vCap := vCap)
      hrec vCap le_rfl 0 (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [hrecs, List.map_map]
    have : (Prod.fst ∘ fun v => (v, sortedEnds G v)) = id := rfl
    rw [this, List.map_id]; exact List.nodup_range
  · funext v
    unfold readOrd ordOfRecords
    rw [hrecs, find?_map_range_pair]
    by_cases hv : v < vCap
    · simp [hv]
    · simp only [hv, ↓reduceIte]; symm
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have hxE := ((mem_sortedEnds G v x).mp hx).1
      have hxS := ((mem_sortedEnds G v x).mp hx).2
      have hvIn : v ∈ G.V := by
        cases hx2 : x.2
        · simp only [MGraph.src, hx2, Bool.false_eq_true, ↓reduceIte] at hxS
          rw [← hxS]; exact (hVal x.1 hxE).2
        · simp only [MGraph.src, hx2, ↓reduceIte] at hxS
          rw [← hxS]; exact (hVal x.1 hxE).1
      exact hv (hV v hvIn)
  · unfold ordRecordsWords
    rw [hrecs, List.map_map]
    have hsum : ((List.range vCap).map (fun v => 2 + (sortedEnds G v).length)).sum =
        (Finset.range vCap).sum (fun v => 2 + (sortedEnds G v).length) := by
      rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
    rw [show ((List.range vCap).map ((fun p : ℕ × List End => 2 + p.2.length) ∘
      fun v => (v, sortedEnds G v))).sum =
        ((List.range vCap).map (fun v => 2 + (sortedEnds G v).length)).sum from rfl,
      hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      sum_sortedEnds_length hVal hV hE]
    omega

private theorem sortedEnds_wordsBound {w : ℕ} {G : MGraph} {mem : ℕ → ℕ} {out vCap eCap : ℕ}
    (hVal : G.IsValid) (hV : ∀ v ∈ G.V, v < vCap) (hE : ∀ e ∈ G.E, e < eCap)
    (hroom : out + 1 + 4 * vCap + 2 * eCap < 2 ^ w)
    (hout : mem out = vCap)
    (hrec : ∀ v < vCap,
      mem (sortedOrdOffset G out v) = v ∧
      mem (sortedOrdOffset G out v + 1) = (sortedEnds G v).length ∧
      ∀ j (hj : j < (sortedEnds G v).length),
        mem (sortedOrdOffset G out v + 2 + j) = endKey (sortedEnds G v)[j]) :
    ∀ j < 1 + 2 * vCap + 2 * G.m, mem (out + j) < 2 ^ w := by
  have hGmLe : G.m ≤ eCap :=
    (Finset.card_le_card (fun e he => Finset.mem_range.mpr (hE e he))).trans (by simp)
  have hEndOff : sortedOrdOffset G out vCap = out + 1 + 2 * vCap + 2 * G.m := by
    unfold sortedOrdOffset
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      sum_sortedEnds_length hVal hV hE]
    omega
  intro j hj
  by_cases hj0 : j = 0
  · subst hj0; simp only [Nat.add_zero, hout]; omega
  · have hgt : sortedOrdOffset G out 0 ≤ out + j := by rw [sortedOrdOffset_zero]; omega
    have hlt : out + j < sortedOrdOffset G out vCap := by rw [hEndOff]; omega
    have hex : ∃ v < vCap, sortedOrdOffset G out v ≤ out + j ∧ out + j < sortedOrdOffset G out (v + 1) := by
      suffices ∀ k ≤ vCap, out + j < sortedOrdOffset G out k →
          ∃ v < k, sortedOrdOffset G out v ≤ out + j ∧ out + j < sortedOrdOffset G out (v + 1) from
        this vCap le_rfl hlt
      intro k
      induction k with
      | zero => intro _ h0; omega
      | succ k ih =>
        intro hk hlt'
        by_cases hge : sortedOrdOffset G out k ≤ out + j
        · exact ⟨k, Nat.lt_succ_self k, hge, hlt'⟩
        · obtain ⟨v, hv, h1, h2⟩ := ih (by omega) (by omega)
          exact ⟨v, Nat.lt_succ_of_lt hv, h1, h2⟩
    obtain ⟨v, hv, h1, h2⟩ := hex
    have hOffMono := sortedOrdOffset_mono G out (show v + 1 ≤ vCap by omega)
    rw [sortedOrdOffset_succ] at h2 hOffMono
    rw [hEndOff] at hOffMono
    by_cases h0' : out + j = sortedOrdOffset G out v
    · rw [h0', (hrec v hv).1]; omega
    · by_cases h1' : out + j = sortedOrdOffset G out v + 1
      · rw [h1', (hrec v hv).2.1]; omega
      · let idx := out + j - (sortedOrdOffset G out v + 2)
        have hidx : idx < (sortedEnds G v).length := by dsimp [idx]; omega
        have haddr : out + j = sortedOrdOffset G out v + 2 + idx := by dsimp [idx]; omega
        rw [haddr, (hrec v hv).2.2 idx hidx]
        have hmem := List.getElem_mem hidx
        have heLt : (sortedEnds G v)[idx].1 < eCap := hE _ ((mem_sortedEnds G v _).mp hmem).1
        cases hb : (sortedEnds G v)[idx].2 <;> simp [endKey, hb] <;> omega

/-- Execution of `buildSortedEndsBody [graph, out]`: constructs `OrdListAt` for `sortedEnds G`
at `out` in `O(vCap + eCap)` deterministic steps and `1 + 4 * vCap + 2 * eCap` words. -/
theorem buildSortedEndsBody_runs {w graph out vCap eCap pos : ℕ} {p : Program}
    {ω : ℕ → Bool} {mem : ℕ → ℕ} {G : MGraph}
    (hg : DynGraphAt mem graph vCap eCap G)
    (hbelow : graph + dynGraphSize vCap eCap ≤ out)
    (hz : ZeroFrom mem out)
    (hroom : out + 1 + 4 * vCap + 2 * eCap < 2 ^ w)
    (hw7 : 7 < 2 ^ w) :
    let words := 1 + 2 * vCap + 2 * G.m
    let nextHeap := out + 1 + 4 * vCap + 2 * eCap
    ∃ cost outSt,
      Runs w p ω buildSortedEndsBody (startState [graph, out] mem pos)
        (.returned nextHeap) outSt cost ∧
      cost ≤ 150 * eCap + 60 * vCap + 120 ∧
      words ≤ 1 + 2 * vCap + 2 * eCap ∧
      OrdListAt outSt.mem out (sortedEnds G) words ∧
      IsRotationOrder G (sortedEnds G) ∧
      (∀ j < words, outSt.mem (out + j) < 2 ^ w) ∧
      ZeroFrom outSt.mem nextHeap ∧
      (∀ a < out, outSt.mem a = mem a) := by
  dsimp only
  obtain ⟨hVal, hV, hE, hVCapEq0, hECapEq0, _, _, _, _, hExtInt, _, hEPresMem0, _, hEnds, _⟩ := hg
  have hGmLe : G.m ≤ eCap :=
    (Finset.card_le_card (fun e he => Finset.mem_range.mpr (hE e he))).trans (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hdgSz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hdegBound (v : ℕ) (hv : v < vCap) : (sortedEnds G v).length ≤ 2 * G.m := by
    have hsum := sum_sortedEnds_length hVal hV hE
    have hle := Finset.single_le_sum (f := fun u => (sortedEnds G u).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hv)
    omega
  have hEndOff : sortedOrdOffset G out vCap = out + 1 + 2 * vCap + 2 * G.m := by
    unfold sortedOrdOffset
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      sum_sortedEnds_length hVal hV hE]
    omega
  let intToExt := dgIntToExtBase graph vCap
  let ePres := dgEPresBase graph vCap
  let eTail := dgETailSlotBase graph vCap eCap
  let eHead := dgEHeadSlotBase graph vCap eCap
  let cntBase := out + 1 + 2 * vCap + 2 * eCap
  let curBase := cntBase + vCap
  have hTailExt (e : ℕ) (he : e ∈ G.E) :
      mem (intToExt + mem (eTail + e)) = G.tail e ∧ mem (eTail + e) < vCap := by
    have h1 := (hEnds e he).1
    have h2 := hExtInt (G.tail e) (hVal e he).1
    exact ⟨by dsimp [intToExt, eTail]; rw [h1]; exact h2.2, hV _ (h1 ▸ h2.1)⟩
  have hHeadExt (e : ℕ) (he : e ∈ G.E) :
      mem (intToExt + mem (eHead + e)) = G.head e ∧ mem (eHead + e) < vCap := by
    have h1 := (hEnds e he).2
    have h2 := hExtInt (G.head e) (hVal e he).2
    exact ⟨by dsimp [intToExt, eHead]; rw [h1]; exact h2.2, hV _ (h1 ▸ h2.1)⟩
  have hVCapEq : mem graph = vCap := by simpa [dgVCapOff] using hVCapEq0
  have hECapEq : mem (graph + 1) = eCap := by simpa [dgECapOff] using hECapEq0
  let s0 := startState [graph, out] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 2 vCap }
  let s2 : State := { s1 with regs := Function.update s1.regs 3 eCap }
  let s3 : State := { s2 with regs := Function.update s2.regs 4 intToExt }
  let s4 : State := { s3 with regs := Function.update s3.regs 5 ePres }
  let s5 : State := { s4 with regs := Function.update s4.regs 6 eTail }
  let s6 : State := { s5 with regs := Function.update s5.regs 7 eHead }
  let s7 : State := { s6 with regs := Function.update s6.regs 8 cntBase }
  let s8 : State := { s7 with regs := Function.update s7.regs 9 curBase }
  have r1 : Runs w p ω (.assign 2 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨vCap, by simp [Expr.eval, s0, startState, hVCapEq], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const 1)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨eCap, by simp [Expr.eval, BinOp.eval, s1, s0, startState, hw1, show graph + 1 < 2 ^ w by omega, hECapEq], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 4 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 2)))) s2 .normal s3 8 :=
    runs_assign_iff.mpr ⟨intToExt, by simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, intToExt, dgIntToExtBase, hw4,
      show graph + 4 < 2 ^ w by omega, show 4 * vCap < 2 ^ w by omega, show graph + 4 + 4 * vCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 5 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 2)))) s3 .normal s4 8 :=
    runs_assign_iff.mpr ⟨ePres, by simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, ePres, dgEPresBase, hw4, hw7,
      show graph + 4 < 2 ^ w by omega, show 7 * vCap < 2 ^ w by omega, show graph + 4 + 7 * vCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 6 (.bin .add (.reg 5) (.bin .mul (.const 3) (.reg 3)))) s4 .normal s5 6 :=
    runs_assign_iff.mpr ⟨eTail, by simp [Expr.eval, BinOp.eval, s4, s3, s2, eTail, ePres, dgETailSlotBase, dgEPresBase, hw3,
      show 3 * eCap < 2 ^ w by omega, show graph + 4 + 7 * vCap + 3 * eCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 7 (.bin .add (.reg 5) (.bin .mul (.const 4) (.reg 3)))) s5 .normal s6 6 :=
    runs_assign_iff.mpr ⟨eHead, by simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, eHead, ePres, dgEHeadSlotBase, dgEPresBase, hw4,
      show 4 * eCap < 2 ^ w by omega, show graph + 4 + 7 * vCap + 4 * eCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 8 (.bin .add (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 2) (.reg 2))) (.bin .mul (.const 2) (.reg 3)))) s6 .normal s7 12 :=
    runs_assign_iff.mpr ⟨cntBase, by simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0, startState, cntBase, hw1, hw2,
      show out + 1 < 2 ^ w by omega, show 2 * vCap < 2 ^ w by omega, show out + 1 + 2 * vCap < 2 ^ w by omega,
      show 2 * eCap < 2 ^ w by omega, show out + 1 + 2 * vCap + 2 * eCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.reg 2))) s7 .normal s8 4 :=
    runs_assign_iff.mpr ⟨curBase, by simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, s1, curBase, cntBase,
      show out + 1 + 2 * vCap + 2 * eCap + vCap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hs8_1 : s8.regs 1 = out := by simp [s8, s7, s6, s5, s4, s3, s2, s1, s0, startState]
  have hs8_2 : s8.regs 2 = vCap := by simp [s8, s7, s6, s5, s4, s3, s2, s1]
  have hs8_3 : s8.regs 3 = eCap := by simp [s8, s7, s6, s5, s4, s3, s2]
  have hs8_4 : s8.regs 4 = intToExt := by simp [s8, s7, s6, s5, s4, s3]
  have hs8_5 : s8.regs 5 = ePres := by simp [s8, s7, s6, s5, s4]
  have hs8_6 : s8.regs 6 = eTail := by simp [s8, s7, s6, s5]
  have hs8_7 : s8.regs 7 = eHead := by simp [s8, s7, s6]
  have hs8_8 : s8.regs 8 = cntBase := by simp [s8, s7]
  have hs8_9 : s8.regs 9 = curBase := by simp [s8]
  -- Pass 1
  obtain ⟨s9, c1, rLoop1, hc1, hregs9, _, hcnt9, hfr9⟩ :=
    buildSortedEndsPass1_runs (w := w) (p := p) (ω := ω) (st0 := s8)
      hVal hV hE hEPresMem0 hTailExt hHeadExt hbelow
      (fun v hv => hz _ (by omega)) hroom hs8_3 hs8_4 hs8_5 hs8_6 hs8_7 hs8_8
  -- Header store & wPtr init
  let s10 : State := { s9 with mem := Function.update s9.mem out vCap }
  let s11 : State := { s10 with regs := Function.update s10.regs 11 (out + 1) }
  have rStoreOut : Runs w p ω (.store (.reg 1) (.reg 2)) s9 .normal s10 3 :=
    runs_store_iff.mpr ⟨out, vCap,
      by simp [Expr.eval, (hregs9 1 (by decide)).trans hs8_1],
      by simp [Expr.eval, (hregs9 2 (by decide)).trans hs8_2], rfl, rfl, rfl⟩
  have rSetW : Runs w p ω (.assign 11 (.bin .add (.reg 1) (.const 1))) s10 .normal s11 4 :=
    runs_assign_iff.mpr ⟨out + 1,
      by simp [Expr.eval, BinOp.eval, s10, (hregs9 1 (by decide)).trans hs8_1, hw1, show out + 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  -- Pass 2
  obtain ⟨s12, c2, rLoop2, hc2, hregs12, _, hout12, hhdr12, hfr12⟩ :=
    buildSortedEndsPass2_runs (w := w) (p := p) (ω := ω) (st0 := s11)
      hVal hV hE hroom hw2
      (by simp [s11, s10, (hregs9 2 (by decide)).trans hs8_2])
      (by simp [s11, s10, (hregs9 8 (by decide)).trans hs8_8, cntBase])
      (by simp [s11, s10, (hregs9 9 (by decide)).trans hs8_9, curBase, cntBase]; omega)
      (by simp [s11]) (by simp [s11, s10])
      (fun v hv => by
        change Function.update s9.mem out vCap (cntBase + v) = _
        rw [Function.update_of_ne (by omega)]; exact hcnt9 v hv)
  have hs12Below (a : ℕ) (ha : a < out) : s12.mem a = mem a := by
    rw [hfr12 a (Or.inl ha)]
    change Function.update s9.mem out vCap a = mem a
    rw [Function.update_of_ne (by omega)]
    exact hfr9 a (Or.inl (by omega))
  -- Pass 3
  obtain ⟨s13, c3, rLoop3, hc3, hregs13, _, hout13, hrec13, hfr13⟩ :=
    buildSortedEndsPass3_runs (w := w) (p := p) (ω := ω) (st0 := s12)
      hVal hV hE
      (fun e he => (hs12Below _ (by dsimp [dgEPresBase]; omega)).trans (hEPresMem0 e he))
      (fun e he => by
        have h1 := hTailExt e he
        have heLt : e < eCap := hE e he
        have heq1 : s12.mem (dgETailSlotBase graph vCap eCap + e) = mem (eTail + e) :=
          hs12Below _ (by dsimp [dgETailSlotBase]; omega)
        rw [heq1]
        exact ⟨(hs12Below _ (by dsimp [dgIntToExtBase]; omega)).trans h1.1, h1.2⟩)
      (fun e he => by
        have h1 := hHeadExt e he
        have heLt : e < eCap := hE e he
        have heq1 : s12.mem (dgEHeadSlotBase graph vCap eCap + e) = mem (eHead + e) :=
          hs12Below _ (by dsimp [dgEHeadSlotBase]; omega)
        rw [heq1]
        exact ⟨(hs12Below _ (by dsimp [dgIntToExtBase]; omega)).trans h1.1, h1.2⟩)
      hbelow hroom hw2
      (by simp [hregs12 3 (by decide), s11, s10, (hregs9 3 (by decide)).trans hs8_3])
      (by simp [hregs12 4 (by decide), s11, s10, (hregs9 4 (by decide)).trans hs8_4, intToExt])
      (by simp [hregs12 5 (by decide), s11, s10, (hregs9 5 (by decide)).trans hs8_5, ePres])
      (by simp [hregs12 6 (by decide), s11, s10, (hregs9 6 (by decide)).trans hs8_6, eTail])
      (by simp [hregs12 7 (by decide), s11, s10, (hregs9 7 (by decide)).trans hs8_7, eHead])
      (by simp [hregs12 9 (by decide), s11, s10, (hregs9 9 (by decide)).trans hs8_9, curBase, cntBase]; omega)
      hout12
      (fun v hv => by
        have h := hhdr12 v hv
        refine ⟨h.1, h.2.1, ?_⟩
        convert h.2.2 using 2; omega)
  have hr9_13 : s13.regs 9 = out + 1 + 3 * vCap + 2 * eCap := by
    rw [hregs13 9 (by decide), hregs12 9 (by decide)]
    simp only [s11, s10, Function.update_of_ne (by decide : (9 : ℕ) ≠ 11)]
    rw [hregs9 9 (by decide), hs8_9]; dsimp [curBase, cntBase]; omega
  have hr2_13 : s13.regs 2 = vCap := by
    rw [hregs13 2 (by decide), hregs12 2 (by decide)]
    simp only [s11, s10, Function.update_of_ne (by decide : (2 : ℕ) ≠ 11)]
    rw [hregs9 2 (by decide), hs8_2]
  have rRet : Runs w p ω (.ret (.bin .add (.reg 9) (.reg 2))) s13
      (.returned (out + 1 + 4 * vCap + 2 * eCap)) s13 4 :=
    runs_ret_iff.mpr ⟨out + 1 + 4 * vCap + 2 * eCap, by
      simp only [Expr.eval, BinOp.eval, hr9_13, hr2_13,
        show out + 1 + 3 * vCap + 2 * eCap + vCap = out + 1 + 4 * vCap + 2 * eCap by omega,
        hroom, ↓reduceIte], rfl, rfl, rfl⟩
  have hOrdAt : OrdListAt s13.mem out (sortedEnds G) (1 + 2 * vCap + 2 * G.m) :=
    ordListAt_of_sortedEnds_records hVal hV hE hout13 hrec13
  have hWordsBound : ∀ j < 1 + 2 * vCap + 2 * G.m, s13.mem (out + j) < 2 ^ w :=
    sortedEnds_wordsBound hVal hV hE hroom hout13 hrec13
  have hZeroNext : ZeroFrom s13.mem (out + 1 + 4 * vCap + 2 * eCap) := by
    intro a ha
    rw [hfr13 a (Or.inr (by omega)), hfr12 a (Or.inr (by omega))]
    change Function.update s9.mem out vCap a = 0
    rw [Function.update_of_ne (show a ≠ out by omega), hfr9 a (Or.inr (by omega))]
    exact hz a (by omega)
  have hFrameBelow : ∀ a < out, s13.mem a = mem a := fun a ha =>
    (hfr13 a (Or.inl ha)).trans (hs12Below a ha)
  have rFull : Runs w p ω buildSortedEndsBody (startState [graph, out] mem pos)
      (.returned (out + 1 + 4 * vCap + 2 * eCap)) s13
      (3 + (5 + (8 + (8 + (6 + (6 + (12 + (4 + (c1 + (3 + (4 + (c2 + (c3 + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 8, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 8, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 6, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 6, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 12, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 4, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, c1, _, rLoop1,
    runs_seq_iff.mpr (Or.inr ⟨s10, 3, _, rStoreOut,
    runs_seq_iff.mpr (Or.inr ⟨s11, 4, _, rSetW,
    runs_seq_iff.mpr (Or.inr ⟨s12, c2, _, rLoop2,
    runs_seq_iff.mpr (Or.inr ⟨s13, c3, 4, rLoop3, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  exact ⟨_, s13, rFull, by omega, by omega, hOrdAt, ⟨sortedRotation G, rfl⟩, hWordsBound,
    hZeroNext, hFrameBelow⟩

end MinCostFlow.MinRatio
