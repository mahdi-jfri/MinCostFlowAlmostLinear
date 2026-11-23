module

public import MinCostFlow.HierPaths.InitProg

/-!
# The length of the block of `Init`

The block of a concrete state is the `layoutList` of its 24 sections. This file gives the
lengths of `csrList` and `layoutList` and writes the length of the block of `initConcrete` as a
sum of a few counts of the static model (`length_encode_initConcrete`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- A sum over `List.range` is a sum over `Finset.range`. -/
theorem sum_map_range (k : ℕ) (g : ℕ → ℕ) :
    ((List.range k).map g).sum = ∑ i ∈ Finset.range k, g i := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.range_succ, Finset.sum_range_succ, ih]

/-- The length of a `csrList`: the `k + 1` offsets and the lists. -/
theorem length_csrList (k : ℕ) (f : ℕ → List ℕ) :
    (csrList k f).length = k + 1 + ∑ i ∈ Finset.range k, (f i).length := by
  simp [csrList, csrData, List.length_flatMap, sum_map_range]

/-- The length of a `layoutList`: the offsets and the sections. -/
theorem length_layoutList (bs : List (List ℕ)) :
    (layoutList bs).length = bs.length + 1 + (bs.map List.length).sum := by
  rw [layoutList, length_csrList]
  congr 1
  rw [← sum_map_range]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem?_eq_getElem (by simpa using h2 : i < bs.length)]

/-- The length of the block of a concrete state, section by section. -/
theorem length_encode (x : HierConcrete) : x.encode.length = 25 + (x.sections.map List.length).sum := by
  rw [HierConcrete.encode, length_layoutList, HierConcrete.length_sections]

/-! ### Counting lemmas -/

theorem sum_ite_eq_le_one (P a : ℕ) :
    ∑ p ∈ Finset.range P, (if a = p then 1 else 0) ≤ 1 := by
  rw [Finset.sum_ite_eq]; split_ifs <;> omega

/-- The classes of a function on `0, …, N − 1` have at most `N` elements together. -/
theorem sum_length_filter_eq_le (N P : ℕ) (g : ℕ → ℕ) :
    ∑ p ∈ Finset.range P, ((List.range N).filter fun k => g k = p).length ≤ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [List.range_succ, List.filter_append, List.length_append, Finset.sum_add_distrib]
    have h1 : ∑ p ∈ Finset.range P, ([N].filter fun k => g k = p).length ≤ 1 := by
      have := sum_ite_eq_le_one P (g N)
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) this
      by_cases hg : g N = p <;> simp [hg]
    omega

/-- The same for the union of the classes of two functions. -/
theorem sum_length_filter_eq_or_le (N P : ℕ) (g h : ℕ → ℕ) :
    ∑ p ∈ Finset.range P, ((List.range N).filter fun k => g k = p ∨ h k = p).length ≤ 2 * N := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [List.range_succ, List.filter_append, List.length_append, Finset.sum_add_distrib]
    have h1 : ∑ p ∈ Finset.range P, ([N].filter fun k => g k = p ∨ h k = p).length ≤ 2 := by
      have e1 := sum_ite_eq_le_one P (g N)
      have e2 := sum_ite_eq_le_one P (h N)
      have : ∀ p, ([N].filter fun k => g k = p ∨ h k = p).length ≤
          (if g N = p then 1 else 0) + (if h N = p then 1 else 0) := by
        intro p
        by_cases hg : g N = p <;> by_cases hh : h N = p <;> simp [hg, hh]
      calc _ ≤ ∑ p ∈ Finset.range P, ((if g N = p then 1 else 0) + (if h N = p then 1 else 0)) :=
            Finset.sum_le_sum fun p _ => this p
        _ ≤ 2 := by rw [Finset.sum_add_distrib]; omega
    omega

/-- The counts of `0, …, m − 1` in a list add up to at most its length. -/
theorem sum_count_le (m : ℕ) (l : List ℕ) : ∑ e ∈ Finset.range m, l.count e ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib]
    have := sum_ite_eq_le_one m a
    have h2 : ∑ e ∈ Finset.range m, (if (a == e) = true then 1 else 0) ≤ 1 := by
      simpa [beq_iff_eq] using this
    omega

/-- A sum over a list is a sum over its indices. -/
theorem sum_map_eq_sum_getD {α : Type*} [Inhabited α] (l : List α) (f : α → ℕ) :
    (l.map f).sum = ∑ k ∈ Finset.range l.length, f (l.getD k default) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.map_append, List.sum_append, ih, List.length_append, List.length_singleton,
      Finset.sum_range_succ]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]
    · simp [List.getD_eq_getElem?_getD]

theorem sum_map_entryWords (l : List SupportEntry) :
    (l.map fun e => (entryWords e).length).sum = 3 * l.length := by
  induction l with
  | nil => simp
  | cons e l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons]
    cases e <;> simp [entryWords] <;> ring

theorem length_pairIdxTable (x : HierConcrete) (j : ℕ) :
    (x.pairIdxTable j).length =
      numGroups x.H.A.x x.H.A.b (j + 1) * branching x.H.A.x x.H.A.b j := by
  simp [HierConcrete.pairIdxTable]

/-- **The length of a block**, with the sums of the lists of its sections. -/
theorem length_encode_eq (x : HierConcrete) :
    x.encode.length = 25 + 15 + x.H.A.C.numTerm + 4 * x.H.A.C.numConn +
      (x.m + 1 + ∑ e ∈ Finset.range x.m, (x.H.A.revList e).length) +
      (x.H.A.C.numTerm + 1 + ∑ t ∈ Finset.range x.H.A.C.numTerm, (x.H.A.termConns t).length) +
      (x.H.A.numPairs + 1 + ∑ q ∈ Finset.range x.H.A.numPairs, (x.H.A.pairConns q).length) +
      (x.n + 1 + 3 * ∑ w ∈ Finset.range x.n, (x.H.A.C.supportArray w).length) +
      (x.H.A.C.numConn + 1 + ∑ c ∈ Finset.range x.H.A.C.numConn, (x.H.A.C.walk c).verts.length) +
      (x.H.A.C.numConn + 1 + ∑ c ∈ Finset.range x.H.A.C.numConn, (x.H.A.C.walk c).edges.length) +
      (x.depth + 1 + ∑ j ∈ Finset.range x.depth,
        numGroups x.H.A.x x.H.A.b (j + 1) * branching x.H.A.x x.H.A.b j) +
      2 * x.H.A.C.numTerm + x.H.A.C.numConn + x.m + x.n +
      2 * (x.depth + 1 + 1 + ∑ j ∈ Finset.range (x.depth + 1), numGroups x.H.A.x x.H.A.b j) +
      x.n + x.H.A.numPairs + x.n + (x.depth + 2) * stackWords := by
  rw [length_encode]
  simp only [HierConcrete.sections, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    length_csrList, length_tabList, length_bitsList, List.length_replicate, HierConcrete.header,
    List.length_cons, List.length_nil, List.length_flatMap, sum_map_entryWords,
    length_pairIdxTable, Finset.mul_sum]
  ring

/-! ### The sections of the initial block -/

section Sections

variable {H : HierData} {x b : ℕ} {owner : ℕ → ℕ} {label : ℕ → Option ℕ}

theorem sum_list_map_sum {α : Type*} (l : List α) (s : Finset ℕ) (f : α → ℕ → ℕ) :
    ∑ e ∈ s, (l.map fun r => f r e).sum = (l.map fun r => ∑ e ∈ s, f r e).sum := by
  induction l with
  | nil => simp
  | cons r l ih => simp [Finset.sum_add_distrib, ih]

theorem sum_revIdx_le (m : ℕ) :
    ∑ e ∈ Finset.range m, (revIdx H x b owner label e).length ≤
      (occRecs H x b owner label).length := by
  simp only [revIdx, List.length_flatMap, List.length_replicate]
  rw [sum_list_map_sum, length_occRecs]
  exact List.sum_le_sum fun r _ => sum_count_le m _

theorem sum_termConns_le (P : ℕ) :
    ∑ t ∈ Finset.range P, (termConns H x b t).length ≤ 2 * (connRecs H x b).length :=
  sum_length_filter_eq_or_le _ P _ _

theorem sum_pairConns_le (P : ℕ) :
    ∑ q ∈ Finset.range P, ((staticArrays H x b owner label).pairConns q).length ≤
      (connRecs H x b).length :=
  sum_length_filter_eq_le _ P _

theorem sum_edges_eq :
    ∑ c ∈ Finset.range (connRecs H x b).length,
      ((connSystem H x b owner label).walk c).edges.length =
      (occRecs H x b owner label).length := by
  rw [length_occRecs, sum_map_eq_sum_getD]
  rfl

theorem sum_supportArray_le (n : ℕ) :
    ∑ w ∈ Finset.range n, ((connSystem H x b owner label).supportArray w).length ≤
      2 ^ x + ∑ c ∈ Finset.range (connRecs H x b).length,
        ((connSystem H x b owner label).walk c).verts.length := by
  set C := connSystem H x b owner label
  have h1 : ∀ w, (C.supportArray w).length =
      ((List.range (2 ^ x)).filter fun t => owner t = w).length +
        ∑ c ∈ Finset.range (connRecs H x b).length, (C.positionsOn w c).length := by
    intro w
    simp only [ConnectorSystem.supportArray, List.length_append, List.length_map,
      List.length_flatMap]
    rw [sum_map_range]
    rfl
  simp only [h1, Finset.sum_add_distrib]
  refine Nat.add_le_add (sum_length_filter_eq_le _ n owner) ?_
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun c _ => sum_length_filter_eq_le _ n _

theorem branching_le_pow (j : ℕ) : branching x b j ≤ 2 ^ b := by
  unfold branching groupSize
  apply Nat.div_le_of_le_mul
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  have : min x (j * b) + b ≥ min x ((j + 1) * b) := by
    rw [Nat.add_mul, one_mul]; omega
  omega

end Sections

/-- `depthOf m · branchOf m ≤ Γ` for `m ≤ M`. -/
theorem depthOf_mul_branchOf_le_gammaHP (a d : ℕ) {m M : ℕ} (h : m ≤ M) :
    depthOf m * branchOf m ≤ gammaHP a d M := by
  have hJ := depthOf_le_bigJ h
  have hK := branchOf_le_bigKB h
  have e : gammaHP a d M = ((bigJ M + 2) ^ 4 * (bigKB M + 1) ^ 4) *
      (2 ^ 12 * 4 ^ (bigJ M + 1) * (1 + (2 + d) ^ 4) ^ 2 * bigUX a M ^ (2 * bigJ M + 2)) := by
    unfold gammaHP; ring
  have h1 : depthOf m * branchOf m ≤ (bigJ M + 2) ^ 4 * (bigKB M + 1) ^ 4 := by
    apply Nat.mul_le_mul
    · calc depthOf m ≤ bigJ M + 2 := by omega
        _ ≤ (bigJ M + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
    · calc branchOf m ≤ bigKB M + 1 := by omega
        _ ≤ (bigKB M + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have h2 : 1 ≤ 2 ^ 12 * 4 ^ (bigJ M + 1) * (1 + (2 + d) ^ 4) ^ 2 * bigUX a M ^ (2 * bigJ M + 2) := by
    have := one_le_bigUX a M
    have : 0 < 2 ^ 12 * 4 ^ (bigJ M + 1) * (1 + (2 + d) ^ 4) ^ 2 * bigUX a M ^ (2 * bigJ M + 2) := by
      positivity
    omega
  rw [e]
  exact h1.trans (Nat.le_mul_of_pos_right _ h2)

/-- **The block of `Init` has length at most `2000 · m · Γ`**, when the static output is
`Good`. -/
theorem length_initBlock_le (S : StaticData) {a d M : ℕ} (ha : 1 ≤ a) (G : Graph)
    (phiNum phiDen : ℕ) (hS : S.Good a d M G) :
    (initBlock S a G phiNum phiDen M).length ≤ 2000 * G.m * gammaHP a d M := by
  rw [initBlock, length_encode_eq]
  have hA : (initConcrete S a (initAbs phiNum phiDen M G)).H.A =
      staticArrays S.H S.x S.b S.owner S.label := rfl
  have hC : (staticArrays S.H S.x S.b S.owner S.label).C = connSystem S.H S.x S.b S.owner S.label :=
    rfl
  have hnt : (connSystem S.H S.x S.b S.owner S.label).numTerm = 2 ^ S.x := rfl
  have hnc : (connSystem S.H S.x S.b S.owner S.label).numConn = (connRecs S.H S.x S.b).length :=
    rfl
  have hrl : (staticArrays S.H S.x S.b S.owner S.label).revList =
      revIdx S.H S.x S.b S.owner S.label := rfl
  have htc : (staticArrays S.H S.x S.b S.owner S.label).termConns = termConns S.H S.x S.b := rfl
  have hnp : (staticArrays S.H S.x S.b S.owner S.label).numPairs = numPairsOf S.x S.b := rfl
  have hax : (staticArrays S.H S.x S.b S.owner S.label).x = S.x := rfl
  have hab : (staticArrays S.H S.x S.b S.owner S.label).b = S.b := rfl
  have hn : (initConcrete S a (initAbs phiNum phiDen M G)).n = G.n := rfl
  have hm : (initConcrete S a (initAbs phiNum phiDen M G)).m = G.m := rfl
  have hd : (initConcrete S a (initAbs phiNum phiDen M G)).depth = leafDepth S.x S.b := rfl
  simp only [hA, hC, hnt, hnc, hrl, htc, hnp, hax, hab, hn, hm, hd]
  set T := 2 ^ S.x
  set N := (connRecs S.H S.x S.b).length
  set D := leafDepth S.x S.b
  set Γ := gammaHP a d M
  have hR := sum_revIdx_le (H := S.H) (x := S.x) (b := S.b) (owner := S.owner)
    (label := S.label) G.m
  have hTC := sum_termConns_le (H := S.H) (x := S.x) (b := S.b) T
  have hPC := sum_pairConns_le (H := S.H) (x := S.x) (b := S.b) (owner := S.owner)
    (label := S.label) (numPairsOf S.x S.b)
  have hE := sum_edges_eq (H := S.H) (x := S.x) (b := S.b) (owner := S.owner) (label := S.label)
  have hSA := sum_supportArray_le (H := S.H) (x := S.x) (b := S.b) (owner := S.owner)
    (label := S.label) G.n
  have hPI : ∑ j ∈ Finset.range D, numGroups S.x S.b (j + 1) * branching S.x S.b j ≤
      D * (T * 2 ^ S.b) := by
    have := Finset.sum_le_card_nsmul (Finset.range D)
      (fun j => numGroups S.x S.b (j + 1) * branching S.x S.b j) (T * 2 ^ S.b)
      (fun j _ => Nat.mul_le_mul (numGroups_le_pow _) (branching_le_pow _))
    simpa using this
  have hNG : ∑ j ∈ Finset.range (D + 1), numGroups S.x S.b j ≤ (D + 1) * T := by
    have := Finset.sum_le_card_nsmul (Finset.range (D + 1)) (fun j => numGroups S.x S.b j) T
      (fun j _ => numGroups_le_pow _)
    simpa using this
  have hN : N ≤ D * (2 ^ S.b * T) := card_connRecs_le hS.b_pos hS.valid
  have hI : initIndexSteps S.H S.x S.b S.owner S.label G.n G.m ≤
      initRestSteps S.H S.x S.b S.owner S.label G.n G.m := by
    unfold initRestSteps; omega
  have hrest := initRestSteps_le_gamma hS.b_pos hS.valid ha hS.bounds hS.depth hS.branch
    hS.terms hS.verts hS.mM hS.proj hS.owner_lt
  have hIdx := hI
  unfold initIndexSteps bucketSteps at hIdx
  have hT1 : 1 ≤ T := Nat.one_le_two_pow
  have hb1 : 1 ≤ 2 ^ S.b := Nat.one_le_two_pow
  have hm1 : 1 ≤ G.m := by have := hS.terms; omega
  have hΓ1 : 1 ≤ Γ := one_le_gammaHP a d M
  have hDB : depthOf G.m * branchOf G.m ≤ Γ := depthOf_mul_branchOf_le_gammaHP a d hS.mM
  have hQ : D * (T * 2 ^ S.b) ≤ 4 * (G.m * Γ) := by
    calc D * (T * 2 ^ S.b) ≤ depthOf G.m * (4 * G.m * branchOf G.m) :=
          Nat.mul_le_mul hS.depth (Nat.mul_le_mul hS.terms hS.branch)
      _ = 4 * G.m * (depthOf G.m * branchOf G.m) := by ring
      _ ≤ 4 * G.m * Γ := Nat.mul_le_mul_left _ hDB
      _ = 4 * (G.m * Γ) := by ring
  have hDT : D * T ≤ D * (T * 2 ^ S.b) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hb1)
  have hD : D ≤ G.m * Γ := by
    have h1 : D ≤ depthOf G.m * branchOf G.m :=
      hS.depth.trans (Nat.le_mul_of_pos_right _ (one_le_branchOf _))
    exact (h1.trans hDB).trans (Nat.le_mul_of_pos_left _ hm1)
  have hmX : G.m ≤ G.m * Γ := Nat.le_mul_of_pos_right _ hΓ1
  have hP : numPairsOf S.x S.b = D * (T * 2 ^ S.b) := by unfold numPairsOf; ring
  have hN' : D * (2 ^ S.b * T) = D * (T * 2 ^ S.b) := by ring
  have hNG' : (D + 1) * T = D * T + T := by ring
  have e1 : 2000 * G.m * Γ = 2000 * (G.m * Γ) := by ring
  have e2 : 63 * G.m * Γ = 63 * (G.m * Γ) := by ring
  rw [e1]
  rw [e2] at hrest
  rw [hN'] at hN
  rw [hNG'] at hNG
  rw [hP] at hPC ⊢
  have hverts := hS.verts
  have hterms := hS.terms
  simp only [stackWords]
  simp only [T, N, D] at *
  generalize G.m * Γ = X at *
  generalize leafDepth S.x S.b * (2 ^ S.x * 2 ^ S.b) = Q at *
  generalize leafDepth S.x S.b * 2 ^ S.x = DT at *
  omega

end MinCostFlow.HierPaths
