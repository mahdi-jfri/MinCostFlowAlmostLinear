module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.ExpanderDecomp.RouteProgLayout
public import MinCostFlow.ExpanderDecomp.RouteGraph

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Local Terminal-Pairs Layout, Statements, and Helper Stages

Defines the compact local terminal-pair layout (`LocalBPairsAt`, `LocalAPairsAt`, `LocalPairsAt`),
workspace offsets (`localPairsSpace`), deterministic Word-RAM statements (`pairsScanStmt`,
`pairsBucketStmt`, `buildLocalPairsProc`), contract `buildLocalPairsContract`, combinatorial
helpers, and verifies `markSetLoop_triple` and Stage 2 (`pairsBucket_triple`). Stage 1
(`pairsScan_triple`) and `buildLocalPairs_meetsContract` live in `RouteProgPairs.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Compact Local Terminal-Pairs Layout -/

/-- Local membership table for target sets `B_i`: `pairB[v] = i + 1` iff `origOf X v ∈ B_i`,
and `0` otherwise. -/
def LocalBPairsAt (mem : ℕ → ℕ) (pairBAddr : ℕ) (X : Finset ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) : Prop :=
  ∀ v < X.card,
    mem (pairBAddr + v) ≤ pairs.length ∧
    ∀ i (hi : i < pairs.length),
      mem (pairBAddr + v) = i + 1 ↔ origOf X v ∈ (pairs[i]'hi).2

/-- Compact local arrays for source sets `A_i`: fixed slice offsets `aOff`, mutable lengths
`aLen`, and strictly increasing local-ID slices `aData[aOff[i] .. aOff[i] + aLen[i] - 1]`. -/
def LocalAPairsAt (mem : ℕ → ℕ) (aOffAddr aLenAddr aDataAddr : ℕ)
    (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (cap : ℕ) : Prop :=
  mem (aOffAddr + pairs.length) ≤ cap ∧
  ∀ i (hi : i < pairs.length),
    let off := mem (aOffAddr + i)
    let len := mem (aLenAddr + i)
    off + len ≤ mem (aOffAddr + i + 1) ∧
    len = (pairs[i]'hi).1.card ∧
    ListAt mem (aDataAddr + off) (((pairs[i]'hi).1.sort (· ≤ ·)).map (locOf X))

/-- Combined compact local representation of terminal pairs `(A_i, B_i)`. -/
def LocalPairsAt (mem : ℕ → ℕ) (pairBAddr aOffAddr aLenAddr aDataAddr : ℕ)
    (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (cap : ℕ) : Prop :=
  LocalBPairsAt mem pairBAddr X pairs ∧
  LocalAPairsAt mem aOffAddr aLenAddr aDataAddr X pairs cap

/-- Total heap words reserved by `buildLocalPairsProc`:
`pairB` (`nX`), `aOff` (`k + 1`), `aLen` (`k`), `aData` (`nX`), scratch `aTag` (`nX`),
and scratch `aWCur` (`k`). -/
def localPairsSpace (nX k : ℕ) : ℕ :=
  3 * nX + 3 * k + 1

def pairsBAddr (workAddr : ℕ) : ℕ := workAddr
def pairsAOffAddr (workAddr nX : ℕ) : ℕ := workAddr + nX
def pairsALenAddr (workAddr nX k : ℕ) : ℕ := workAddr + nX + k + 1
def pairsADataAddr (workAddr nX k : ℕ) : ℕ := workAddr + nX + 2 * k + 1
def pairsATagAddr (workAddr nX k : ℕ) : ℕ := workAddr + 2 * nX + 2 * k + 1
def pairsAWCurAddr (workAddr nX k : ℕ) : ℕ := workAddr + 3 * nX + 2 * k + 1

/-- Prefix sum of `|A_t|` over `t < i`. -/
def pairAOff (pairs : List (Finset ℕ × Finset ℕ)) (i : ℕ) : ℕ :=
  ((pairs.take i).map fun p => p.1.card).sum

/-- Remaining total sizes `∑_{t ≥ i} (|A_t| + |B_t|)` for Stage 1 cost accounting. -/
def pairRemSize (pairs : List (Finset ℕ × Finset ℕ)) (i : ℕ) : ℕ :=
  ((pairs.drop i).map fun p => p.1.card + p.2.card).sum

/-- Prefix of the sorted local-ID list of `A` consisting of entries `< v`. -/
def localPrefix (X A : Finset ℕ) (v : ℕ) : List ℕ :=
  ((A.sort (· ≤ ·)).map (locOf X)).filter (· < v)

/-- Explicit step bound for `buildLocalPairsProc`. -/
def buildLocalPairsCost (nX k : ℕ) : ℕ :=
  200 * (nX + k + 1)

/-! ## 2. Procedure Statements -/

/-- Stage 1: scan `pairs[0 .. k-1]`, fill `aOff`, `aWCur`, `aLen`, `aTag`, and `pairB`, leaving
`totalDemand pairs` in register `11`. -/
def pairsScanStmt : Stmt :=
  seqStmts
    [ .assign 11 (.const 0)
    , .assign 12 (.const 0)
    , .loop (.bin .lt (.reg 12) (.reg 4))
        (seqStmts
          [ .store (.bin .add (.reg 6) (.reg 12)) (.reg 11)
          , .store (.bin .add (.reg 10) (.reg 12)) (.reg 11)
          , .assign 13 (.load (.bin .add (.bin .add (.reg 0) (.const 1))
              (.bin .mul (.const 2) (.reg 12))))
          , .assign 14 (.load (.reg 13))
          , .store (.bin .add (.reg 7) (.reg 12)) (.reg 14)
          , .assign 11 (.bin .add (.reg 11) (.reg 14))
          , .assign 15 (.const 0)
          , .loop (.bin .lt (.reg 15) (.reg 14))
              (seqStmts
                [ .assign 16 (.load (.bin .add (.bin .add (.reg 13) (.const 1)) (.reg 15)))
                , .assign 17 (.bin .sub (.load (.bin .add (.reg 2) (.reg 16))) (.const 1))
                , .store (.bin .add (.reg 9) (.reg 17)) (.bin .add (.reg 12) (.const 1))
                , .assign 15 (.bin .add (.reg 15) (.const 1)) ])
          , .assign 13 (.load (.bin .add (.bin .add (.reg 0) (.const 2))
              (.bin .mul (.const 2) (.reg 12))))
          , .assign 14 (.load (.reg 13))
          , .assign 15 (.const 0)
          , .loop (.bin .lt (.reg 15) (.reg 14))
              (seqStmts
                [ .assign 16 (.load (.bin .add (.bin .add (.reg 13) (.const 1)) (.reg 15)))
                , .assign 17 (.bin .sub (.load (.bin .add (.reg 2) (.reg 16))) (.const 1))
                , .store (.bin .add (.reg 5) (.reg 17)) (.bin .add (.reg 12) (.const 1))
                , .assign 15 (.bin .add (.reg 15) (.const 1)) ])
          , .assign 12 (.bin .add (.reg 12) (.const 1)) ])
    , .store (.bin .add (.reg 6) (.reg 4)) (.reg 11) ]

/-- Stage 2: bucket-sort all `A_i` into strictly increasing local-ID slices of `aData` by
sweeping `v = 0 .. nX - 1` over `aTag`. -/
def pairsBucketStmt : Stmt :=
  seqStmts
    [ .assign 12 (.const 0)
    , .loop (.bin .lt (.reg 12) (.reg 1))
        (seqStmts
          [ .assign 13 (.load (.bin .add (.reg 9) (.reg 12)))
          , .cond (.reg 13)
              (seqStmts
                [ .assign 14 (.bin .sub (.reg 13) (.const 1))
                , .assign 15 (.load (.bin .add (.reg 10) (.reg 14)))
                , .store (.bin .add (.reg 8) (.reg 15)) (.reg 12)
                , .store (.bin .add (.reg 10) (.reg 14)) (.bin .add (.reg 15) (.const 1)) ])
              .nop
          , .assign 12 (.bin .add (.reg 12) (.const 1)) ]) ]

/-- Build compact local terminal-pair arrays from `PairsAt` using `locId`.
Arguments: `[pAddr, nX, locIdAddr, workAddr, n]`. Returns `totalDemand pairs`. -/
def buildLocalPairsProc : Stmt :=
  seqStmts
    [ .assign 4 (.load (.reg 0))
    , .assign 5 (.reg 3)
    , .assign 6 (.bin .add (.reg 5) (.reg 1))
    , .assign 7 (.bin .add (.bin .add (.reg 6) (.reg 4)) (.const 1))
    , .assign 8 (.bin .add (.reg 7) (.reg 4))
    , .assign 9 (.bin .add (.reg 8) (.reg 1))
    , .assign 10 (.bin .add (.reg 9) (.reg 1))
    , pairsScanStmt
    , pairsBucketStmt
    , .ret (.reg 11) ]

theorem buildLocalPairsProc_noRand : Stmt.NoRand buildLocalPairsProc := by
  unfold buildLocalPairsProc pairsScanStmt pairsBucketStmt
  repeat (first | apply seqStmts_noRand | constructor | simp)

/-! ## 3. Contract -/

/-- Contract for `buildLocalPairsProc` `[pAddr, nX, locIdAddr, workAddr, n]`. -/
def buildLocalPairsContract (w : ℕ) : Contract where
  pre args mem :=
    args.length = 5 ∧
    ∃ (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)),
      let pAddr := args.getD 0 0
      let nX := args.getD 1 0
      let locIdAddr := args.getD 2 0
      let workAddr := args.getD 3 0
      let n := args.getD 4 0
      nX = X.card ∧
      X ⊆ Finset.range n ∧
      PairsAt mem pAddr pairs ∧
      PairsBounded mem pAddr pairs workAddr ∧
      RouteTerminalPairs X pairs ∧
      locIdAddr + n ≤ workAddr ∧
      (∀ u < n, mem (locIdAddr + u) = if u ∈ X then locOf X u + 1 else 0) ∧
      ZeroFrom mem workAddr ∧
      workAddr + localPairsSpace X.card pairs.length + 4 < 2 ^ w ∧
      4 ≤ 2 ^ w
  post args mem v mem' :=
    ∀ (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)),
      let pAddr := args.getD 0 0
      let nX := args.getD 1 0
      let locIdAddr := args.getD 2 0
      let workAddr := args.getD 3 0
      let n := args.getD 4 0
      nX = X.card →
      X ⊆ Finset.range n →
      PairsAt mem pAddr pairs →
      PairsBounded mem pAddr pairs workAddr →
      RouteTerminalPairs X pairs →
      locIdAddr + n ≤ workAddr →
      (∀ u < n, mem (locIdAddr + u) = if u ∈ X then locOf X u + 1 else 0) →
      v = totalDemand pairs ∧
      LocalPairsAt mem' (pairsBAddr workAddr) (pairsAOffAddr workAddr X.card)
        (pairsALenAddr workAddr X.card pairs.length)
        (pairsADataAddr workAddr X.card pairs.length) X pairs X.card ∧
      (∀ a < workAddr, mem' a = mem a) ∧
      ZeroFrom mem' (workAddr + localPairsSpace X.card pairs.length)
  cost args mem :=
    buildLocalPairsCost (args.getD 1 0) (mem (args.getD 0 0))

/-! ## 4. Combinatorial Helpers -/

lemma routeTerminalPairs_sum_card_le {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hp : RouteTerminalPairs X pairs) :
    (pairs.map fun p => p.1.card + p.2.card).sum ≤ X.card := by
  induction pairs generalizing X with
  | nil => simp
  | cons pq rest ih =>
    rcases hp with ⟨hmem, hpw⟩
    rw [List.pairwise_cons] at hpw
    have hpq := hmem pq List.mem_cons_self
    have hrest_tp : RouteTerminalPairs (X \ (pq.1 ∪ pq.2)) rest := by
      refine ⟨fun q hq => ?_, hpw.2⟩
      have hq' := hmem q (List.mem_cons_of_mem _ hq)
      have hdisj := hpw.1 q hq
      refine ⟨Finset.subset_sdiff.mpr ⟨hq'.1, (hdisj.mono_right Finset.subset_union_left).symm⟩,
        Finset.subset_sdiff.mpr ⟨hq'.2.1, (hdisj.mono_right Finset.subset_union_right).symm⟩,
        hq'.2.2.1, hq'.2.2.2⟩
    have hsub := ih hrest_tp
    have hunion_sub : pq.1 ∪ pq.2 ⊆ X := Finset.union_subset hpq.1 hpq.2.1
    have hcard_u : (pq.1 ∪ pq.2).card = pq.1.card + pq.2.card :=
      Finset.card_union_of_disjoint hpq.2.2.2
    have hcard_sdiff : (X \ (pq.1 ∪ pq.2)).card = X.card - (pq.1 ∪ pq.2).card :=
      Finset.card_sdiff_of_subset hunion_sub
    have hle_u : (pq.1 ∪ pq.2).card ≤ X.card := Finset.card_le_card hunion_sub
    simp only [List.map_cons, List.sum_cons]
    omega

lemma routeTerminalPairs_totalDemand_le {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hp : RouteTerminalPairs X pairs) :
    totalDemand pairs ≤ X.card := by
  have h1 : totalDemand pairs ≤ (pairs.map fun p => p.1.card + p.2.card).sum := by
    clear hp
    unfold totalDemand
    induction pairs with
    | nil => simp
    | cons pq rest ih =>
      simp only [List.map_cons, List.sum_cons]
      omega
  exact le_trans h1 (routeTerminalPairs_sum_card_le hp)

lemma routeTerminalPairs_disj_fst {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hp : RouteTerminalPairs X pairs) {i j : ℕ} (hi : i < pairs.length) (hj : j < pairs.length)
    (hne : i ≠ j) :
    Disjoint (pairs[i]'hi).1 (pairs[j]'hj).1 := by
  have hpw := List.pairwise_iff_getElem.mp hp.2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hpw i j hi hj hlt).mono Finset.subset_union_left Finset.subset_union_left
  · exact ((hpw j i hj hi hgt).mono Finset.subset_union_left Finset.subset_union_left).symm

lemma routeTerminalPairs_disj_snd {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hp : RouteTerminalPairs X pairs) {i j : ℕ} (hi : i < pairs.length) (hj : j < pairs.length)
    (hne : i ≠ j) :
    Disjoint (pairs[i]'hi).2 (pairs[j]'hj).2 := by
  have hpw := List.pairwise_iff_getElem.mp hp.2
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hpw i j hi hj hlt).mono Finset.subset_union_right Finset.subset_union_right
  · exact ((hpw j i hj hi hgt).mono Finset.subset_union_right Finset.subset_union_right).symm

lemma pairAOff_zero (pairs : List (Finset ℕ × Finset ℕ)) : pairAOff pairs 0 = 0 := by
  simp [pairAOff]

lemma pairAOff_length (pairs : List (Finset ℕ × Finset ℕ)) :
    pairAOff pairs pairs.length = totalDemand pairs := by
  simp [pairAOff, totalDemand]

lemma pairAOff_succ (pairs : List (Finset ℕ × Finset ℕ)) {i : ℕ} (hi : i < pairs.length) :
    pairAOff pairs (i + 1) = pairAOff pairs i + (pairs[i]'hi).1.card := by
  unfold pairAOff
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]

lemma pairAOff_mono (pairs : List (Finset ℕ × Finset ℕ)) {i j : ℕ} (hij : i ≤ j) :
    pairAOff pairs i ≤ pairAOff pairs j := by
  induction hij with
  | refl => exact le_rfl
  | @step m _ ih =>
    by_cases hm : m < pairs.length
    · rw [pairAOff_succ pairs hm]; omega
    · have h1 : pairs.take (m + 1) = pairs.take m := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp only [pairAOff, h1]; exact ih

lemma pairAOff_le_totalDemand (pairs : List (Finset ℕ × Finset ℕ)) (i : ℕ) :
    pairAOff pairs i ≤ totalDemand pairs := by
  by_cases hi : i ≤ pairs.length
  · simpa [pairAOff_length] using pairAOff_mono pairs hi
  · unfold pairAOff totalDemand
    rw [List.take_of_length_le (by omega)]

lemma pairRemSize_zero (pairs : List (Finset ℕ × Finset ℕ)) :
    pairRemSize pairs 0 = (pairs.map fun p => p.1.card + p.2.card).sum := by
  simp [pairRemSize]

lemma pairRemSize_eq_succ (pairs : List (Finset ℕ × Finset ℕ)) {i : ℕ} (hi : i < pairs.length) :
    pairRemSize pairs i = (pairs[i]'hi).1.card + (pairs[i]'hi).2.card + pairRemSize pairs (i + 1) := by
  unfold pairRemSize
  rw [List.drop_eq_getElem_cons hi, List.map_cons, List.sum_cons]

lemma pairwise_lt_map_locOf {X A : Finset ℕ} (hA : A ⊆ X) :
    ((A.sort (· ≤ ·)).map (locOf X)).Pairwise (· < ·) := by
  have hle : (A.sort (· ≤ ·)).Pairwise (· ≤ ·) := A.pairwise_sort (· ≤ ·)
  have hnd : (A.sort (· ≤ ·)).Nodup := A.sort_nodup (· ≤ ·)
  have hlt : (A.sort (· ≤ ·)).Pairwise (· < ·) :=
    (hle.and (List.nodup_iff_pairwise_ne.mp hnd)).imp fun h => Nat.lt_of_le_of_ne h.1 h.2
  rw [List.pairwise_map]
  refine hlt.imp_of_mem fun {a b} ha hb hab => ?_
  rw [Finset.mem_sort] at ha hb
  exact (locOf_lt_iff (hA ha) (hA hb)).mpr hab

lemma mem_map_locOf_iff {X A : Finset ℕ} (hA : A ⊆ X) {v : ℕ} (hv : v < X.card) :
    v ∈ (A.sort (· ≤ ·)).map (locOf X) ↔ origOf X v ∈ A := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨u, hu, hloc⟩
    rw [Finset.mem_sort] at hu
    have : origOf X v = u := by rw [← hloc, origOf_locOf (hA hu)]
    rwa [this]
  · intro h
    exact List.mem_map.mpr ⟨origOf X v, (Finset.mem_sort (· ≤ ·)).mpr h, locOf_origOf hv⟩

lemma filter_lt_succ_of_pairwise_lt {l : List ℕ} (hlt : l.Pairwise (· < ·)) (v : ℕ) :
    l.filter (· < v + 1) = l.filter (· < v) ++ if v ∈ l then [v] else [] := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.pairwise_cons] at hlt
    have ih' := ih hlt.2
    by_cases hav : a < v
    · have hne : v ≠ a := Nat.ne_of_gt hav
      have hav1 : a < v + 1 := Nat.lt_succ_of_lt hav
      rw [List.filter_cons, List.filter_cons, decide_eq_true hav1, decide_eq_true hav]
      simp only [↓reduceIte, List.mem_cons, hne, false_or, ih', List.cons_append]
    · by_cases heq : a = v
      · subst heq
        have hflt_v : t.filter (· < a) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx; simp [Nat.not_lt.mpr (Nat.le_of_lt (hlt.1 x hx))]
        have hflt_v1 : t.filter (· < a + 1) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx; have := hlt.1 x hx; simp; omega
        rw [List.filter_cons, List.filter_cons,
          decide_eq_true (Nat.lt_succ_self a), decide_eq_false (Nat.lt_irrefl a)]
        simp only [↓reduceIte, Bool.false_eq_true, hflt_v, hflt_v1, List.mem_cons, true_or,
          List.nil_append]
      · have hgt : v < a := by omega
        have hnot_t : v ∉ t := fun hm => by have := hlt.1 v hm; omega
        have hflt_v : t.filter (· < v) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx; have := hlt.1 x hx; simp; omega
        have hflt_v1 : t.filter (· < v + 1) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx; have := hlt.1 x hx; simp; omega
        have hne : v ≠ a := Nat.ne_of_lt hgt
        rw [List.filter_cons, List.filter_cons,
          decide_eq_false (by omega : ¬ a < v + 1), decide_eq_false (by omega : ¬ a < v)]
        simp only [Bool.false_eq_true, ↓reduceIte, hflt_v, hflt_v1, List.mem_cons, hne, hnot_t,
          or_self, List.append_nil]

lemma localPrefix_zero (X A : Finset ℕ) : localPrefix X A 0 = [] := by
  simp [localPrefix]

lemma localPrefix_card {X A : Finset ℕ} (hA : A ⊆ X) :
    localPrefix X A X.card = (A.sort (· ≤ ·)).map (locOf X) := by
  unfold localPrefix
  rw [List.filter_eq_self]
  intro x hx
  rcases List.mem_map.mp hx with ⟨u, hu, rfl⟩
  rw [Finset.mem_sort] at hu
  exact decide_eq_true (locOf_lt (hA hu))

lemma localPrefix_succ {X A : Finset ℕ} (hA : A ⊆ X) {v : ℕ} (hv : v < X.card) :
    localPrefix X A (v + 1) =
      localPrefix X A v ++ if origOf X v ∈ A then [v] else [] := by
  unfold localPrefix
  rw [filter_lt_succ_of_pairwise_lt (pairwise_lt_map_locOf hA) v]
  simp only [mem_map_locOf_iff hA hv]

lemma localPrefix_length_le (X A : Finset ℕ) (v : ℕ) :
    (localPrefix X A v).length ≤ A.card := by
  calc (localPrefix X A v).length
      ≤ ((A.sort (· ≤ ·)).map (locOf X)).length := List.length_filter_le _ _
    _ = A.card := by simp [Finset.length_sort]

/-! ## 5. Inner Tag-Marking Loop Helper -/

/-- Helper triple for marking `arr[locOf X u] := tag` for every `u ∈ S` stored at `VertSetAt ptr`. -/
lemma markSetLoop_triple {w : ℕ} {p : Program}
    {X S : Finset ℕ} {n ptr locIdAddr arrAddr tag workAddr rArr : ℕ}
    {mem0 : ℕ → ℕ} {st0 : State}
    (hS : S ⊆ X) (hX : X ⊆ Finset.range n)
    (hseq : VertSetAt mem0 ptr S)
    (hptr_lt : ptr + 1 + S.card ≤ workAddr)
    (hloc_lt : locIdAddr + n ≤ workAddr)
    (harr_ge : workAddr ≤ arrAddr)
    (hloc : ∀ u < n, mem0 (locIdAddr + u) = if u ∈ X then locOf X u + 1 else 0)
    (htag_lt : tag < 2 ^ w)
    (hw : arrAddr + X.card + 4 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hreg_loc : st0.regs 2 = locIdAddr)
    (hreg_arr : st0.regs rArr = arrAddr)
    (hreg_tag : st0.regs 12 + 1 = tag)
    (hreg_ptr : st0.regs 13 = ptr)
    (hreg_len : st0.regs 14 = S.card)
    (hreg_j : st0.regs 15 = 0)
    (hrArr_ne : rArr ≠ 15 ∧ rArr ≠ 16 ∧ rArr ≠ 17 ∧ rArr ≤ 10)
    (hmem0 : st0.mem = mem0) :
    Triple w p (fun st => st = st0)
      (.loop (.bin .lt (.reg 15) (.reg 14))
        (seqStmts
          [ .assign 16 (.load (.bin .add (.bin .add (.reg 13) (.const 1)) (.reg 15)))
          , .assign 17 (.bin .sub (.load (.bin .add (.reg 2) (.reg 16))) (.const 1))
          , .store (.bin .add (.reg rArr) (.reg 17)) (.bin .add (.reg 12) (.const 1))
          , .assign 15 (.bin .add (.reg 15) (.const 1)) ]))
      (normalPost fun st' =>
        (∀ r ≤ 14, st'.regs r = st0.regs r) ∧
        (∀ v < X.card, st'.mem (arrAddr + v) =
          if origOf X v ∈ S then tag else mem0 (arrAddr + v)) ∧
        (∀ a, (a < arrAddr ∨ arrAddr + X.card ≤ a) → st'.mem a = mem0 a))
      (fun _ => 35 * S.card + 5) := by
  rcases hseq with ⟨xs, hxs_nd, hxs_fin, hxs_seq⟩
  have hxs_len : xs.length = S.card := by
    rw [← hxs_fin, List.toFinset_card_of_nodup hxs_nd]
  let I : State → Prop := fun st =>
    (∀ r ≤ 14, st.regs r = st0.regs r) ∧
    st.regs 15 ≤ S.card ∧
    (∀ v < X.card, st.mem (arrAddr + v) =
      if origOf X v ∈ xs.take (st.regs 15) then tag else mem0 (arrAddr + v)) ∧
    (∀ a, (a < arrAddr ∨ arrAddr + X.card ≤ a) → st.mem a = mem0 a)
  have hloop :
      Triple w p I
        (.loop (.bin .lt (.reg 15) (.reg 14))
          (seqStmts
            [ .assign 16 (.load (.bin .add (.bin .add (.reg 13) (.const 1)) (.reg 15)))
            , .assign 17 (.bin .sub (.load (.bin .add (.reg 2) (.reg 16))) (.const 1))
            , .store (.bin .add (.reg rArr) (.reg 17)) (.bin .add (.reg 12) (.const 1))
            , .assign 15 (.bin .add (.reg 15) (.const 1)) ]))
        (normalPost fun st' =>
          (∀ r ≤ 14, st'.regs r = st0.regs r) ∧
          (∀ v < X.card, st'.mem (arrAddr + v) =
            if origOf X v ∈ S then tag else mem0 (arrAddr + v)) ∧
          (∀ a, (a < arrAddr ∨ arrAddr + X.card ≤ a) → st'.mem a = mem0 a))
        (fun st => ((Expr.bin .lt (.reg 15) (.reg 14)).size + 30 + 1) * (S.card - st.regs 15) +
          (Expr.bin .lt (.reg 15) (.reg 14)).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => S.card - st.regs 15)
      (condVal := fun st => if st.regs 15 < S.card then 1 else 0)
      (bodyBound := 30) ?_ ?_ ?_
    · intro stL ⟨hregs, _, _, _⟩
      have hr14 : stL.regs 14 = S.card := (hregs 14 (by decide)).trans hreg_len
      eval_expr
    · intro stL ⟨hregs, hj_le, hmem_arr, hframe⟩ hv
      have hj_eq : stL.regs 15 = S.card := by split_ifs at hv; omega
      refine ⟨hregs, ?_, hframe⟩
      intro v hv'
      have h := hmem_arr v hv'
      simp only [hj_eq, ← hxs_len, List.take_length, ← List.mem_toFinset, hxs_fin] at h
      exact h
    · intro stL ⟨hregs, hj_le, hmem_arr, hframe⟩ hv
      have hr2 : stL.regs 2 = locIdAddr := (hregs 2 (by decide)).trans hreg_loc
      have hrA : stL.regs rArr = arrAddr := (hregs rArr (by omega)).trans hreg_arr
      have hr12 : stL.regs 12 + 1 = tag := by rw [hregs 12 (by decide)]; exact hreg_tag
      have hr13 : stL.regs 13 = ptr := (hregs 13 (by decide)).trans hreg_ptr
      have hr14 : stL.regs 14 = S.card := (hregs 14 (by decide)).trans hreg_len
      have hj_lt : stL.regs 15 < S.card := by split_ifs at hv <;> omega
      set j := stL.regs 15
      have hj_xs : j < xs.length := by omega
      set u := xs[j]'hj_xs
      have hu_S : u ∈ S := by rw [← hxs_fin]; exact List.mem_toFinset.mpr (List.getElem_mem hj_xs)
      have hu_X : u ∈ X := hS hu_S
      have hu_n : u < n := Finset.mem_range.mp (hX hu_X)
      have hloc_u_lt : locOf X u < X.card := locOf_lt hu_X
      have hu_mem : stL.mem (ptr + 1 + j) = u := by
        rw [hframe _ (Or.inl (by omega))]; exact hxs_seq.2 j hj_xs
      have hloc_mem : stL.mem (locIdAddr + u) = locOf X u + 1 := by
        rw [hframe _ (Or.inl (by omega)), hloc u hu_n]
        simp only [hu_X, ↓reduceIte]
      wram_enter
      subst st
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := u) (by rw [← hu_mem]; eval_expr) ?_
      refine runs_seq_assign_le (v := locOf X u)
        (by
          have hsub : (locOf X u + 1) - 1 = locOf X u := Nat.add_sub_cancel _ 1
          conv_rhs => rw [← hsub, ← hloc_mem]
          eval_expr) ?_
      refine runs_seq_store_le (x := arrAddr + locOf X u) (v := tag)
        (by
          have hrr : Function.update (Function.update stL.regs 16 u) 17 (locOf X u) rArr = arrAddr := by
            rw [Function.update_of_ne hrArr_ne.2.2.1, Function.update_of_ne hrArr_ne.2.1, hrA]
          simp only [Expr.eval, hrr, Function.update_self, BinOp.eval,
            show arrAddr + locOf X u < 2 ^ w by omega, ↓reduceIte])
        (by
          have h12 : stL.regs 12 + 1 = tag := hr12
          rw [← h12]; eval_expr) ?_
      refine runs_assign_le (v := j + 1) (by eval_expr) ?_ ?_
      · dsimp only [normalPost]
        refine ⟨⟨?_, by simp; omega, ?_, ?_⟩, by simp; omega⟩
        · intro r hr
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
          exact hregs r hr
        · intro v hv'
          dsimp only
          simp only [Function.update_self]
          by_cases hvu : v = locOf X u
          · subst hvu
            have horig : origOf X (locOf X u) = u := origOf_locOf hu_X
            have hmem_take : u ∈ xs.take (j + 1) := by
              rw [List.take_succ_eq_append_getElem hj_xs]
              exact List.mem_append_right _ (List.mem_singleton_self _)
            rw [Function.update_self, horig]
            simp only [hmem_take, ↓reduceIte]
          · have hne_orig : origOf X v ≠ u := fun h => hvu (by rw [← h, locOf_origOf hv'])
            have hiff : origOf X v ∈ xs.take (j + 1) ↔ origOf X v ∈ xs.take j := by
              rw [List.take_succ_eq_append_getElem hj_xs, List.mem_append, List.mem_singleton]
              exact ⟨fun h => h.resolve_right hne_orig, Or.inl⟩
            rw [Function.update_of_ne (by omega), hmem_arr v hv']
            simp only [hiff]
        · intro a ha
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe a ha
      · wram_cost
  intro st ω hst
  subst st
  have hinit : I st0 := by
    refine ⟨fun _ _ => rfl, by omega, ?_, fun _ _ => by rw [hmem0]⟩
    intro v _; simp [hreg_j, hmem0]
  obtain ⟨o, st', c, hrun, hpost, hcost⟩ := hloop st0 ω hinit
  refine ⟨o, st', c, hrun, hpost, ?_⟩
  simp only [hreg_j, Nat.sub_zero] at hcost
  have hsz : (Expr.bin .lt (.reg 15) (.reg 14)).size = 3 := rfl
  rw [hsz] at hcost
  dsimp only
  omega

/-! ## 6. Stage 2 Verification (`pairsBucketStmt`) -/

lemma pairsBucket_triple {w : ℕ} {p : Program}
    {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {workAddr : ℕ} {st0 : State}
    (htp : RouteTerminalPairs X pairs)
    (hwcur0 : ∀ i < pairs.length,
      st0.mem (pairsAWCurAddr workAddr X.card pairs.length + i) = pairAOff pairs i)
    (htag0 : ∀ v < X.card,
      st0.mem (pairsATagAddr workAddr X.card pairs.length + v) ≤ pairs.length ∧
      ∀ i (hi : i < pairs.length),
        st0.mem (pairsATagAddr workAddr X.card pairs.length + v) = i + 1 ↔
          origOf X v ∈ (pairs[i]'hi).1)
    (hw : workAddr + localPairsSpace X.card pairs.length + 4 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hregs0 : ∀ r ≤ 11, st0.regs r =
      match r with
      | 1 => X.card
      | 8 => pairsADataAddr workAddr X.card pairs.length
      | 9 => pairsATagAddr workAddr X.card pairs.length
      | 10 => pairsAWCurAddr workAddr X.card pairs.length
      | r => st0.regs r) :
    Triple w p (fun st => st = st0) pairsBucketStmt
      (normalPost fun st' =>
        (∀ r ≤ 11, st'.regs r = st0.regs r) ∧
        (∀ i (hi : i < pairs.length),
          ListAt st'.mem (pairsADataAddr workAddr X.card pairs.length + pairAOff pairs i)
            (((pairs[i]'hi).1.sort (· ≤ ·)).map (locOf X))) ∧
        (∀ a, (a < pairsADataAddr workAddr X.card pairs.length ∨
               (pairsATagAddr workAddr X.card pairs.length ≤ a ∧
                a < pairsAWCurAddr workAddr X.card pairs.length) ∨
               workAddr + localPairsSpace X.card pairs.length ≤ a) →
          st'.mem a = st0.mem a))
      (fun _ => 50 * X.card + 15) := by
  set k := pairs.length
  set nX := X.card
  set aDataAddr := pairsADataAddr workAddr nX k
  set aTagAddr := pairsATagAddr workAddr nX k
  set aWCurAddr := pairsAWCurAddr workAddr nX k
  have hsp : localPairsSpace nX k = 3 * nX + 3 * k + 1 := rfl
  have htd_le : totalDemand pairs ≤ nX := routeTerminalPairs_totalDemand_le htp
  let I : State → Prop := fun st =>
    (∀ r ≤ 11, st.regs r = st0.regs r) ∧
    st.regs 12 ≤ nX ∧
    (∀ i (hi : i < k),
      st.mem (aWCurAddr + i) = pairAOff pairs i + (localPrefix X (pairs[i]'hi).1 (st.regs 12)).length) ∧
    (∀ i (hi : i < k),
      ListAt st.mem (aDataAddr + pairAOff pairs i) (localPrefix X (pairs[i]'hi).1 (st.regs 12))) ∧
    (∀ a, (a < aDataAddr ∨ (aTagAddr ≤ a ∧ a < aWCurAddr) ∨
           workAddr + localPairsSpace nX k ≤ a) → st.mem a = st0.mem a)
  have hloop :
      Triple w p I
        (.loop (.bin .lt (.reg 12) (.reg 1))
          (seqStmts
            [ .assign 13 (.load (.bin .add (.reg 9) (.reg 12)))
            , .cond (.reg 13)
                (seqStmts
                  [ .assign 14 (.bin .sub (.reg 13) (.const 1))
                  , .assign 15 (.load (.bin .add (.reg 10) (.reg 14)))
                  , .store (.bin .add (.reg 8) (.reg 15)) (.reg 12)
                  , .store (.bin .add (.reg 10) (.reg 14)) (.bin .add (.reg 15) (.const 1)) ])
                .nop
            , .assign 12 (.bin .add (.reg 12) (.const 1)) ]))
        (normalPost fun st' =>
          (∀ r ≤ 11, st'.regs r = st0.regs r) ∧
          (∀ i (hi : i < k),
            ListAt st'.mem (aDataAddr + pairAOff pairs i)
              (((pairs[i]'hi).1.sort (· ≤ ·)).map (locOf X))) ∧
          (∀ a, (a < aDataAddr ∨ (aTagAddr ≤ a ∧ a < aWCurAddr) ∨
                 workAddr + localPairsSpace nX k ≤ a) → st'.mem a = st0.mem a))
        (fun st => ((Expr.bin .lt (.reg 12) (.reg 1)).size + 42 + 1) * (nX - st.regs 12) +
          (Expr.bin .lt (.reg 12) (.reg 1)).size + 1) := by
    refine Triple.loop_const_normal
      (m := fun st => nX - st.regs 12)
      (condVal := fun st => if st.regs 12 < nX then 1 else 0)
      (bodyBound := 42) ?_ ?_ ?_
    · intro stL ⟨hregs, _, _, _, _⟩
      have hr1 : stL.regs 1 = nX := (hregs 1 (by decide)).trans (hregs0 1 (by decide))
      eval_expr
    · intro stL ⟨hregs, hv_le, _, hdata, hframe⟩ hv
      have hv_eq : stL.regs 12 = nX := by split_ifs at hv; omega
      refine ⟨hregs, ?_, hframe⟩
      intro i hi
      have hAi_sub : (pairs[i]'hi).1 ⊆ X := (htp.1 _ (List.getElem_mem hi)).1
      have h := hdata i hi
      rwa [hv_eq, localPrefix_card hAi_sub] at h
    · intro stL ⟨hregs, hv_le, hwcur, hdata, hframe⟩ hv
      have hr1 : stL.regs 1 = nX := (hregs 1 (by decide)).trans (hregs0 1 (by decide))
      have hr8 : stL.regs 8 = aDataAddr := (hregs 8 (by decide)).trans (hregs0 8 (by decide))
      have hr9 : stL.regs 9 = aTagAddr := (hregs 9 (by decide)).trans (hregs0 9 (by decide))
      have hr10 : stL.regs 10 = aWCurAddr := (hregs 10 (by decide)).trans (hregs0 10 (by decide))
      have hv_lt : stL.regs 12 < nX := by split_ifs at hv <;> omega
      set v := stL.regs 12
      set tag := st0.mem (aTagAddr + v)
      have htag_le : tag ≤ k := (htag0 v hv_lt).1
      have htag_mem : stL.mem (aTagAddr + v) = tag :=
        hframe _ (Or.inr (Or.inl ⟨by omega,
          by dsimp only [aTagAddr, pairsATagAddr, aWCurAddr, pairsAWCurAddr]; omega⟩))
      wram_enter
      subst st
      dsimp only [seqStmts]
      have haTag_v_lt : aTagAddr + v < 2 ^ w := by dsimp only [aTagAddr, pairsATagAddr]; omega
      refine runs_seq_assign_le (v := tag) (by rw [← htag_mem]; eval_expr) ?_
      refine runs_seq_cond_le (v := tag) (by eval_expr) (fun htag_ne => ?_) (fun htag_zero => ?_)
      · set i0 := tag - 1
        have hi0_lt : i0 < k := by omega
        have htag_eq : tag = i0 + 1 := by omega
        have hv_in_i0 : origOf X v ∈ (pairs[i0]'hi0_lt).1 :=
          ((htag0 v hv_lt).2 i0 hi0_lt).mp htag_eq
        have hA0_sub : (pairs[i0]'hi0_lt).1 ⊆ X := (htp.1 _ (List.getElem_mem hi0_lt)).1
        have hpref_succ0 := localPrefix_succ hA0_sub hv_lt
        simp only [hv_in_i0, ↓reduceIte] at hpref_succ0
        set pos0 := pairAOff pairs i0 + (localPrefix X (pairs[i0]'hi0_lt).1 v).length
        have hlen_lt_card : (localPrefix X (pairs[i0]'hi0_lt).1 v).length < (pairs[i0]'hi0_lt).1.card := by
          have h1 := localPrefix_length_le X (pairs[i0]'hi0_lt).1 (v + 1)
          rw [hpref_succ0, List.length_append, List.length_singleton] at h1
          omega
        have hpos0_lt_nX : pos0 < nX := by
          have h1 : pairAOff pairs i0 + (pairs[i0]'hi0_lt).1.card = pairAOff pairs (i0 + 1) :=
            (pairAOff_succ pairs hi0_lt).symm
          have h2 := pairAOff_le_totalDemand pairs (i0 + 1)
          omega
        have hpos0_mem : stL.mem (aWCurAddr + i0) = pos0 := hwcur i0 hi0_lt
        have haWCur_i0_lt : aWCurAddr + i0 < 2 ^ w := by dsimp only [aWCurAddr, pairsAWCurAddr]; omega
        have haData_pos0_lt : aDataAddr + pos0 < 2 ^ w := by dsimp only [aDataAddr, pairsADataAddr]; omega
        have htag_lt_w : tag < 2 ^ w := by dsimp only [localPairsSpace] at hw; omega
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_le (v := i0)
          (by
            have hi0_eq : tag - 1 = i0 := rfl
            rw [← hi0_eq]; eval_expr) ?_
        refine runs_seq_assoc_le ?_
        refine runs_seq_assign_le (v := pos0) (by rw [← hpos0_mem]; eval_expr) ?_
        refine runs_seq_assoc_le ?_
        refine runs_seq_store_le (x := aDataAddr + pos0) (v := v) (by eval_expr) (by eval_expr) ?_
        refine runs_seq_store_le (x := aWCurAddr + i0) (v := pos0 + 1) (by eval_expr) (by eval_expr) ?_
        refine runs_assign_le (v := v + 1) (by eval_expr) ?_ ?_
        · dsimp only [normalPost]
          refine ⟨⟨?_, by simp; omega, ?_, ?_, ?_⟩, by simp; omega⟩
          · intro r hr
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hregs r hr
          · intro i hi
            dsimp only
            simp only [Function.update_self]
            have hAi_sub : (pairs[i]'hi).1 ⊆ X := (htp.1 _ (List.getElem_mem hi)).1
            by_cases hii : i = i0
            · subst hii
              rw [Function.update_self, hpref_succ0, List.length_append, List.length_singleton]
              dsimp only [pos0]; omega
            · have hnot_in : origOf X v ∉ (pairs[i]'hi).1 := by
                have hdisj := routeTerminalPairs_disj_fst htp hi0_lt hi (Ne.symm hii)
                exact Finset.disjoint_left.mp hdisj hv_in_i0
              have hpref_eq := localPrefix_succ hAi_sub hv_lt
              simp only [hnot_in, ↓reduceIte, List.append_nil] at hpref_eq
              rw [hpref_eq, Function.update_of_ne (by omega),
                Function.update_of_ne (by dsimp only [aDataAddr, pairsADataAddr, aWCurAddr, pairsAWCurAddr]; omega)]
              exact hwcur i hi
          · intro i hi j hj
            dsimp only at hj ⊢
            simp only [Function.update_self] at hj ⊢
            have hAi_sub : (pairs[i]'hi).1 ⊆ X := (htp.1 _ (List.getElem_mem hi)).1
            by_cases hii : i = i0
            · subst hii
              have hj_len : j < (localPrefix X (pairs[i0]'hi0_lt).1 v).length + 1 := by
                rw [hpref_succ0, List.length_append, List.length_singleton] at hj; exact hj
              by_cases hj_old : j < (localPrefix X (pairs[i0]'hi0_lt).1 v).length
              · have hget_eq : (localPrefix X (pairs[i0]'hi0_lt).1 (v + 1))[j]'hj =
                    (localPrefix X (pairs[i0]'hi0_lt).1 v)[j]'hj_old := by
                  have hopt : (localPrefix X (pairs[i0]'hi0_lt).1 (v + 1))[j]? =
                      (localPrefix X (pairs[i0]'hi0_lt).1 v)[j]? := by
                    rw [hpref_succ0, List.getElem?_append_left hj_old]
                  rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj_old] at hopt
                  exact Option.some.inj hopt
                rw [hget_eq,
                  Function.update_of_ne (by dsimp only [aDataAddr, pairsADataAddr, aWCurAddr, pairsAWCurAddr]; omega),
                  Function.update_of_ne (by dsimp only [pos0]; omega)]
                exact hdata i0 hi0_lt j hj_old
              · have hget_last : (localPrefix X (pairs[i0]'hi0_lt).1 (v + 1))[j]'hj = v := by
                  have hopt : (localPrefix X (pairs[i0]'hi0_lt).1 (v + 1))[j]? = some v := by
                    rw [hpref_succ0, List.getElem?_append_right (by omega),
                      show j - (localPrefix X (pairs[i0]'hi0_lt).1 v).length = 0 by omega]
                    rfl
                  rw [List.getElem?_eq_getElem hj] at hopt
                  exact Option.some.inj hopt
                rw [hget_last,
                  Function.update_of_ne (by dsimp only [aDataAddr, pairsADataAddr, aWCurAddr, pairsAWCurAddr]; omega),
                  show aDataAddr + pairAOff pairs i0 + j = aDataAddr + pos0 by dsimp only [pos0]; omega,
                  Function.update_self]
            · have hnot_in : origOf X v ∉ (pairs[i]'hi).1 := by
                have hdisj := routeTerminalPairs_disj_fst htp hi0_lt hi (Ne.symm hii)
                exact Finset.disjoint_left.mp hdisj hv_in_i0
              have hpref_eq := localPrefix_succ hAi_sub hv_lt
              simp only [hnot_in, ↓reduceIte, List.append_nil] at hpref_eq
              have hj' : j < (localPrefix X (pairs[i]'hi).1 v).length := by
                rw [← hpref_eq]; exact hj
              have hget_eq : (localPrefix X (pairs[i]'hi).1 (v + 1))[j]'hj =
                  (localPrefix X (pairs[i]'hi).1 v)[j]'hj' := by
                have hopt : (localPrefix X (pairs[i]'hi).1 (v + 1))[j]? =
                    (localPrefix X (pairs[i]'hi).1 v)[j]? := by rw [hpref_eq]
                rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj'] at hopt
                exact Option.some.inj hopt
              have hj_card : j < (pairs[i]'hi).1.card :=
                lt_of_lt_of_le hj' (localPrefix_length_le X (pairs[i]'hi).1 v)
              have hpos_i_lt_nX : pairAOff pairs i + j < nX := by
                have h1 : pairAOff pairs i + (pairs[i]'hi).1.card = pairAOff pairs (i + 1) :=
                  (pairAOff_succ pairs hi).symm
                have h2 := pairAOff_le_totalDemand pairs (i + 1)
                omega
              have hne_pos : pairAOff pairs i + j ≠ pos0 := by
                rcases lt_or_gt_of_ne hii with hlt | hgt
                · have h1 : pairAOff pairs i + (pairs[i]'hi).1.card = pairAOff pairs (i + 1) :=
                    (pairAOff_succ pairs hi).symm
                  have h2 := pairAOff_mono pairs (by omega : i + 1 ≤ i0)
                  dsimp only [pos0]; omega
                · have h1 : pairAOff pairs i0 + (pairs[i0]'hi0_lt).1.card = pairAOff pairs (i0 + 1) :=
                    (pairAOff_succ pairs hi0_lt).symm
                  have h2 := pairAOff_mono pairs (by omega : i0 + 1 ≤ i)
                  dsimp only [pos0]; omega
              rw [hget_eq,
                Function.update_of_ne (by dsimp only [aDataAddr, pairsADataAddr, aWCurAddr, pairsAWCurAddr]; omega),
                Function.update_of_ne (by omega)]
              exact hdata i hi j hj'
          · intro a ha
            dsimp only
            rw [Function.update_of_ne (by
                  rcases ha with h1 | ⟨h1, h2⟩ | h1 <;>
                    dsimp only [aDataAddr, pairsADataAddr, aTagAddr, pairsATagAddr, aWCurAddr,
                      pairsAWCurAddr, localPairsSpace] at * <;> omega),
                Function.update_of_ne (by
                  rcases ha with h1 | ⟨h1, h2⟩ | h1 <;>
                    dsimp only [aDataAddr, pairsADataAddr, aTagAddr, pairsATagAddr, aWCurAddr,
                      pairsAWCurAddr, localPairsSpace] at * <;> omega)]
            exact hframe a ha
        · wram_cost
      · refine runs_seq_nop_le ?_
        refine runs_assign_le (v := v + 1) (by eval_expr) ?_ ?_
        · dsimp only [normalPost]
          refine ⟨⟨?_, by simp; omega, ?_, ?_, hframe⟩, by simp; omega⟩
          · intro r hr
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hregs r hr
          · intro i hi
            dsimp only
            simp only [Function.update_self]
            have hAi_sub : (pairs[i]'hi).1 ⊆ X := (htp.1 _ (List.getElem_mem hi)).1
            have hnot_in : origOf X v ∉ (pairs[i]'hi).1 := fun hmem => by
              have := ((htag0 v hv_lt).2 i hi).mpr hmem; omega
            have hpref_eq := localPrefix_succ hAi_sub hv_lt
            simp only [hnot_in, ↓reduceIte, List.append_nil] at hpref_eq
            rw [hpref_eq]; exact hwcur i hi
          · intro i hi j hj
            dsimp only at hj ⊢
            simp only [Function.update_self] at hj ⊢
            have hAi_sub : (pairs[i]'hi).1 ⊆ X := (htp.1 _ (List.getElem_mem hi)).1
            have hnot_in : origOf X v ∉ (pairs[i]'hi).1 := fun hmem => by
              have := ((htag0 v hv_lt).2 i hi).mpr hmem; omega
            have hpref_eq := localPrefix_succ hAi_sub hv_lt
            simp only [hnot_in, ↓reduceIte, List.append_nil] at hpref_eq
            have hj' : j < (localPrefix X (pairs[i]'hi).1 v).length := by
              rw [← hpref_eq]; exact hj
            have hget_eq : (localPrefix X (pairs[i]'hi).1 (v + 1))[j]'hj =
                (localPrefix X (pairs[i]'hi).1 v)[j]'hj' := by
              have hopt : (localPrefix X (pairs[i]'hi).1 (v + 1))[j]? =
                  (localPrefix X (pairs[i]'hi).1 v)[j]? := by rw [hpref_eq]
              rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hj'] at hopt
              exact Option.some.inj hopt
            rw [hget_eq]; exact hdata i hi j hj'
        · wram_cost
  wram_enter
  subst st
  unfold pairsBucketStmt
  dsimp only [seqStmts]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  have hinit : I { st0 with regs := Function.update st0.regs 12 0 } := by
    refine ⟨fun r hr => Function.update_of_ne (by omega) _ _, by simp, ?_, ?_, fun _ _ => rfl⟩
    · intro i hi; simp [localPrefix_zero, hwcur0 i hi]
    · intro i hi j hj; simp [localPrefix_zero] at hj
  refine runs_triple_le hloop hinit (fun _ _ h => h) ?_
  have hsz : (Expr.bin .lt (.reg 12) (.reg 1)).size = 3 := rfl
  simp only [Function.update_self, Nat.sub_zero, hsz]
  wram_cost

end MinCostFlow.ExpanderDecomp
