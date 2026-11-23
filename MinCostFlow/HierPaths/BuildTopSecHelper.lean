module

public import MinCostFlow.HierPaths.BuildTopNext
public import MinCostFlow.HierPaths.BuildTopRows
public import MinCostFlow.HierPaths.BuildTopNumbers
public import MinCostFlow.HierPaths.BuildTopPack

/-!
# Shared helpers for assembling sections 3, 4, and 5

Provides `buildTopReplySpan` (writing a `(src, len)` pair for a single row of a
`BuildLevelData` reply block in `O(1)` time), a linear cost bound for
`buildTopGather`, and the pure encoding-size bound `S.encode.length ≤ m * Γ`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp
open scoped BigOperators

/-- Read row `i` of section `sec` (with `k` rows) from reply block `rAddr` and
store `(src, len)` at `[dst, dst + 1]`. Args: `[rAddr, sec, k, i, dst]`. -/
def buildTopReplySpan (read : ℕ) : Stmt :=
  .call 5 read [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .call 6 read [.reg 0, .reg 1, .reg 2, .bin .add (.reg 3) (.const 1)] ;;
  .store (.reg 4) (.reg 5) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.bin .sub (.reg 6) (.reg 5)) ;;
  .ret (.const 0)

theorem buildTopReplySpan_noRand (read : ℕ) : (buildTopReplySpan read).NoRand := by
  simp [buildTopReplySpan, Stmt.NoRand]

/-- Starting address of row `i` in section `sec` of a 3-section reply block at `rAddr`. -/
def buildTopReplyRowAddr (rAddr sec k i : ℕ) (rows : ℕ → List ℕ)
    (sections : List (List ℕ)) : ℕ :=
  initCSRAddr (initCSRAddr rAddr 3 (sections.getD · []) sec) k rows i

/-- A row of a 3-section reply block lies inside the block's memory span. -/
theorem buildTopReplyRowAddr_facts {rAddr sec k i : ℕ} {rows : ℕ → List ℕ}
    {sections : List (List ℕ)} {mem : ℕ → ℕ}
    (hlen : sections.length = 3) (hsec : sec < 3) (hi : i < k)
    (hget : sections.getD sec [] = csrList k rows)
    (hAt : ListAt mem rAddr (layoutList sections)) :
    let src := buildTopReplyRowAddr rAddr sec k i rows sections
    ListAt mem src (rows i) ∧
    src + (rows i).length ≤ rAddr + (layoutList sections).length := by
  dsimp only [buildTopReplyRowAddr]
  let F := (sections.getD · [])
  have hcsr : layoutList sections = csrList 3 F := by rw [layoutList, hlen]
  rw [hcsr] at hAt ⊢
  have hSecAt : ListAt mem (initCSRAddr rAddr 3 F sec) (csrList k rows) := by
    have h := initCSRAddr_listAt hAt hsec
    change ListAt mem (initCSRAddr rAddr 3 F sec) (sections.getD sec []) at h
    rwa [hget] at h
  have hRowAt : ListAt mem (initCSRAddr (initCSRAddr rAddr 3 F sec) k rows i) (rows i) :=
    initCSRAddr_listAt hSecAt hi
  have hRowEnd : initCSRAddr (initCSRAddr rAddr 3 F sec) k rows i + (rows i).length ≤
      initCSRAddr rAddr 3 F sec + (csrList k rows).length := by
    have h := initCSRAddr_le_end (addr := initCSRAddr rAddr 3 F sec) (k := k) (f := rows)
      (i := i + 1) (Nat.succ_le_of_lt hi)
    rwa [initCSRAddr_succ] at h
  have hSecEnd : initCSRAddr rAddr 3 F sec + (csrList k rows).length ≤
      rAddr + (csrList 3 F).length := by
    have h := initCSRAddr_le_end (addr := rAddr) (k := 3) (f := F)
      (i := sec + 1) (Nat.succ_le_of_lt hsec)
    rw [initCSRAddr_succ] at h
    change initCSRAddr rAddr 3 F sec + (sections.getD sec []).length ≤ _ at h
    rwa [hget] at h
  exact ⟨hRowAt, hRowEnd.trans hSecEnd⟩

/-- Contract for `buildTopReplySpan`. -/
def buildTopReplySpanContract (w sec k i : ℕ) (rows : ℕ → List ℕ)
    (sections : List (List ℕ)) : Contract where
  pre args mem := ∃ rAddr dst, args = [rAddr, sec, k, i, dst] ∧
    sections.length = 3 ∧ sec < 3 ∧ i < k ∧
    sections.getD sec [] = csrList k rows ∧
    ListAt mem rAddr (layoutList sections) ∧
    rAddr + (layoutList sections).length < 2 ^ w ∧ dst + 1 < 2 ^ w ∧ 1 < 2 ^ w
  post args mem _ mem' := ∃ rAddr dst, args = [rAddr, sec, k, i, dst] ∧
    mem' dst = buildTopReplyRowAddr rAddr sec k i rows sections ∧
    mem' (dst + 1) = (rows i).length ∧
    ∀ y, y ≠ dst → y ≠ dst + 1 → mem' y = mem y
  cost _ _ := 115

theorem buildTopReplySpan_meetsContract {w f read seek sec k i : ℕ}
    {rows : ℕ → List ℕ} {sections : List (List ℕ)} {p : Program}
    (hp : p.procs[f]? = some (buildTopReplySpan read))
    (hr : p.procs[read]? = some (buildTopReplyRead seek))
    (hs : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p f (buildTopReplySpanContract w sec k i rows sections) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨rAddr, dst, rfl, hlen, hsec, hi, hget, hAt, hroom, hdst, h1⟩ := hpre
  obtain ⟨_, hEnd⟩ := buildTopReplyRowAddr_facts hlen hsec hi hget hAt
  let src := buildTopReplyRowAddr rAddr sec k i rows sections
  have hNext : buildTopReplyRowAddr rAddr sec k (i + 1) rows sections = src + (rows i).length := by
    change initCSRAddr (initCSRAddr rAddr 3 (sections.getD · []) sec) k rows (i + 1) =
      initCSRAddr (initCSRAddr rAddr 3 (sections.getD · []) sec) k rows i + (rows i).length
    rw [initCSRAddr_succ]
  have hSrcW : src < 2 ^ w := by omega
  have hNextW : src + (rows i).length < 2 ^ w := by omega
  have hi1W : i + 1 < 2 ^ w := by
    have hkW : k < 2 ^ w := hw k (by simp)
    omega
  refine runs_start_le ?_
  unfold buildTopReplySpan
  refine runs_seq_call_le (buildTopReplyRead_meetsContract (w := w) (sec := sec) (k := k)
    (i := i) (rows := rows) (sections := sections) hr hs) (vs := [rAddr, sec, k, i])
    rfl (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> exact hw _ (by simp))
    ⟨rAddr, rfl, hlen, hsec, hi.le, hget, hAt, hroom⟩ ?_
  intro v1 mem1 pos1 hpost1
  obtain ⟨hv1, hm1⟩ := hpost1
  change v1 = src at hv1
  change mem1 = mem at hm1
  subst v1 mem1
  refine runs_seq_call_le (buildTopReplyRead_meetsContract (w := w) (sec := sec) (k := k)
    (i := i + 1) (rows := rows) (sections := sections) hr hs) (vs := [rAddr, sec, k, i + 1])
    ?_ ?_ ⟨rAddr, rfl, hlen, hsec, Nat.succ_le_of_lt hi, hget, hAt, hroom⟩ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, h1, hi1W]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hw _ (by simp)
    · exact hw _ (by simp)
    · exact hi1W
  intro v2 mem2 pos2 hpost2
  obtain ⟨hv2, hm2⟩ := hpost2
  change v2 = buildTopReplyRowAddr rAddr sec k (i + 1) rows sections at hv2
  rw [hNext] at hv2
  change mem2 = mem at hm2
  subst v2 mem2
  refine runs_seq_store_le
    (Expr.eval_reg_of_eq (v := dst) rfl) (Expr.eval_reg_of_eq (v := src) rfl) ?_
  refine runs_seq_store_le
    (Expr.eval_add (Expr.eval_reg_of_eq (v := dst) rfl) (Expr.eval_const h1) hdst)
    (Expr.eval_eq_of_eq (Expr.eval_sub (Expr.eval_reg_of_eq (v := src + (rows i).length) rfl)
      (Expr.eval_reg_of_eq (v := src) rfl) hNextW)
      (Nat.add_sub_cancel_left src _)) ?_
  refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _))
    ⟨rAddr, dst, rfl, ?_, ?_, ?_⟩ ?_
  · dsimp only
    rw [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self dst)), Function.update_self]
  · dsimp only
    rw [Function.update_self]
  · intro y hy0 hy1
    dsimp only
    rw [Function.update_of_ne hy1, Function.update_of_ne hy0]
  · simp [buildTopReplySpanContract, buildTopReplyReadContract, Expr.size, argsSize]

/-- Linear upper bound on the cost of `buildTopGather_meetsContract`. -/
theorem buildTopGather_cost_le (k : ℕ) (rows : ℕ → List ℕ) :
    rangeCost (fun i => 17 * (rows i).length + 70) 0 k + 30 * k + 40 ≤
      17 * (csrList k rows).length + 100 * k + 40 := by
  have hSum (xs : List ℕ) :
      (xs.map (fun i => 17 * (rows i).length + 70)).sum =
        17 * (xs.flatMap rows).length + 70 * xs.length := by
    induction xs with
    | nil => rfl
    | cons a l ih => simp [List.flatMap_cons, ih, Nat.mul_add]; omega
  rw [rangeCost_zero_eq_range, hSum, List.length_range]
  have hLen : (csrList k rows).length = k + 1 + (csrData k rows).length := by
    rw [csrList, List.length_append, length_csrOffsets]
  change 17 * (csrData k rows).length + 70 * k + 30 * k + 40 ≤ _
  omega

/-! ### Encoding length bound for the assembled `StaticData` -/

private lemma list_sum_map_range (k : ℕ) (f : ℕ → ℕ) :
    ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, Finset.sum_range_succ, ih]

private lemma csrList_length_le_sum {k : ℕ} {rows : ℕ → List ℕ} {B : ℕ → ℕ}
    (h : ∀ i < k, (rows i).length ≤ B i) :
    (csrList k rows).length ≤ k + 1 + ∑ i ∈ Finset.range k, B i := by
  rw [csrList, List.length_append, length_csrOffsets]
  have hData : (csrData k rows).length = ∑ i ∈ Finset.range k, (rows i).length := by
    unfold csrData
    rw [List.length_flatMap, list_sum_map_range]
  rw [hData]
  exact Nat.add_le_add_left (Finset.sum_le_sum fun i hi => h i (Finset.mem_range.mp hi)) _

private lemma child_m_le_of_good {H : Graph} {start s c Δ : ℕ}
    (hval : H.IsValid) (_hloop : H.IsLoopless)
    (hsupp : ∀ e ∈ H.edges, e.1 ∈ buildLevelChild start s c ∧
      e.2 ∈ buildLevelChild start s c)
    (hdeg : ∀ v ∈ buildLevelChild start s c, H.deg v ≤ Δ) :
    H.m ≤ Δ * s := by
  have hCard : (buildLevelChild start s c).card = s := by
    unfold buildLevelChild
    rw [card_shiftSet, Finset.card_range]
  have h2m : 2 * H.m ≤ ∑ v ∈ buildLevelChild start s c, H.deg v := by
    rw [← MinCostFlow.Expander.sum_deg_eq_two_mul_m hval]
    have hzero : ∀ v ∈ H.verts, v ∉ buildLevelChild start s c → H.deg v = 0 := by
      intro v _ hv
      unfold Graph.deg Graph.degIn
      have h1 : List.filter (fun e => decide (e.1 = v)) (H.inside H.verts) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e he
        simp only [Graph.inside, List.mem_filter] at he
        have := (hsupp e he.1).1
        simp only [decide_eq_true_eq]
        exact fun h => hv (h ▸ this)
      have h2 : List.filter (fun e => decide (e.2 = v)) (H.inside H.verts) = [] := by
        rw [List.filter_eq_nil_iff]
        intro e he
        simp only [Graph.inside, List.mem_filter] at he
        have := (hsupp e he.1).2
        simp only [decide_eq_true_eq]
        exact fun h => hv (h ▸ this)
      rw [h1, h2]; rfl
    have hsub : H.verts ∩ buildLevelChild start s c ⊆ buildLevelChild start s c :=
      Finset.inter_subset_right
    calc ∑ v ∈ H.verts, H.deg v
      _ = ∑ v ∈ H.verts ∩ buildLevelChild start s c, H.deg v := by
          symm
          apply Finset.sum_subset Finset.inter_subset_left
          intro v hv hnot
          exact hzero v hv (fun hmem => hnot (Finset.mem_inter.mpr ⟨hv, hmem⟩))
      _ ≤ ∑ v ∈ buildLevelChild start s c, H.deg v :=
          Finset.sum_le_sum_of_subset hsub
  have hle : ∑ v ∈ buildLevelChild start s c, H.deg v ≤ Δ * s := by
    calc ∑ v ∈ buildLevelChild start s c, H.deg v
      _ ≤ ∑ _v ∈ buildLevelChild start s c, Δ := Finset.sum_le_sum fun v hv => hdeg v hv
      _ = (buildLevelChild start s c).card * Δ := by simp
      _ = Δ * s := by rw [hCard, Nat.mul_comm]
  omega

private lemma conn_length_eq_s {D : BuildLevelData} {G : Graph}
    {start s k M r Δ L L' bh c c' : ℕ}
    (hGood : D.Good G start s k M r Δ L L' bh)
    (hc : c < k) (hc' : c' < k) (hlt : c < c') :
    (D.conn c c').length = s := by
  obtain ⟨hNodup, hToFin, _, _⟩ := hGood.connMatch c hc c' hc' hlt
  have h1 := List.toFinset_card_of_nodup hNodup
  rw [hToFin, List.length_map] at h1
  unfold buildLevelChild at h1
  rw [card_shiftSet, Finset.card_range] at h1
  exact h1.symm

private lemma sec3_length_le {x b : ℕ} {root : Graph} {reply : ℕ → ℕ → BuildLevelData}
    {M r L L' : ℕ} {bh : ℕ → ℕ}
    (hb : 0 < b) (hroot : root.m ≤ 12 * M)
    (hgood : buildTopRepliesGood x b root reply (2 ^ x) r (49 * L' + 2) L L' bh) :
    let D := leafDepth x b
    let P := 2 ^ x
    let H := buildTopHierarchy x b root reply
    (csrList ((D + 1) * P) fun k => (H.host (k / P) (k % P)).encode).length ≤
      3 * (D + 1) * P + 24 * M + 2 * D * (49 * L' + 2) * P + 1 := by
  dsimp only
  set D := leafDepth x b
  set P := 2 ^ x
  set Δ := 49 * L' + 2
  set H := buildTopHierarchy x b root reply
  have hPpos : 0 < P := Nat.two_pow_pos x
  have hEach : ∀ k < (D + 1) * P,
      (H.host (k / P) (k % P)).encode.length ≤
        2 + (if k = 0 then 2 * root.m
          else if 0 < k / P ∧ k % P < numGroups x b (k / P) then 2 * Δ * groupSize x b (k / P)
          else 0) := by
    intro k hk
    have hE := graph_encode_length (H.host (k / P) (k % P))
    rw [hE]
    cases ht : k / P with
    | zero =>
      by_cases hk0 : k = 0
      · subst hk0; simp [H, buildTopHierarchy]
      · have hmod : k % P ≠ 0 := by
          have := Nat.div_add_mod k P; rw [ht] at this; omega
        simp [hk0, H, buildTopHierarchy, hmod, Graph.m]
    | succ j =>
      have hk0 : k ≠ 0 := by intro h0; subst h0; simp at ht
      have hjlt : j < D := by
        have : (j + 1) * P ≤ k := by rw [← ht, Nat.mul_comm]; exact Nat.mul_div_le k P
        nlinarith
      by_cases hc : k % P < numGroups x b (j + 1)
      · have h1gs : 1 < groupSize x b j := one_lt_groupSize_of_lt_leafDepth hb hjlt
        have hp : parentGroup x b j (k % P) < numGroups x b j := by
          unfold parentGroup
          rw [Nat.div_lt_iff_lt_mul branching_pos, ← numGroups_succ]
          exact hc
        have hlc : (k % P) % branching x b j < branching x b j := Nat.mod_lt _ branching_pos
        have hG := hgood j (parentGroup x b j (k % P)) h1gs hp
        obtain ⟨_, hval, hloop, hsupp, hdeg, _, _⟩ := hG.graph _ hlc
        have hm := child_m_le_of_good hval hloop hsupp hdeg
        have hhost : H.host (j + 1) (k % P) =
            (reply j (parentGroup x b j (k % P))).host ((k % P) % branching x b j) := by
          simp [H, buildTopHierarchy, hc]
        rw [hhost]
        simp only [hk0, ↓reduceIte, Nat.succ_pos, hc, and_self]
        change 2 + 2 * ((reply j (parentGroup x b j (k % P))).host ((k % P) % branching x b j)).m ≤
          2 + 2 * Δ * groupSize x b (j + 1)
        have hΔeq : buildLevelDegree L' = Δ := rfl
        rw [hΔeq] at hm
        nlinarith
      · simp [hk0, hc, H, buildTopHierarchy, Graph.m]
  have hC := csrList_length_le_sum hEach
  have hSumSplit : ∑ k ∈ Finset.range ((D + 1) * P),
      (2 + (if k = 0 then 2 * root.m
        else if 0 < k / P ∧ k % P < numGroups x b (k / P) then 2 * Δ * groupSize x b (k / P)
        else 0)) ≤
      2 * ((D + 1) * P) + 2 * root.m + 2 * D * Δ * P := by
    rw [Finset.sum_add_distrib]
    have h2 : ∑ _k ∈ Finset.range ((D + 1) * P), 2 = 2 * ((D + 1) * P) := by
      simp [Nat.mul_comm]
    rw [h2, Nat.add_assoc]
    apply Nat.add_le_add_left
    have hSplit2 : ∑ k ∈ Finset.range ((D + 1) * P),
        (if k = 0 then 2 * root.m
          else if 0 < k / P ∧ k % P < numGroups x b (k / P) then 2 * Δ * groupSize x b (k / P)
          else 0) ≤
        2 * root.m + ∑ t ∈ Finset.range D,
          ∑ g ∈ Finset.range P,
            if g < numGroups x b (t + 1) then 2 * Δ * groupSize x b (t + 1) else 0 := by
      rw [show (D + 1) * P = P + D * P by ring, Finset.sum_range_add]
      have hFirst : ∑ k ∈ Finset.range P,
          (if k = 0 then 2 * root.m
            else if 0 < k / P ∧ k % P < numGroups x b (k / P) then 2 * Δ * groupSize x b (k / P)
            else 0) ≤ 2 * root.m := by
        have hP1 : Finset.range P = Finset.range (1 + (P - 1)) := by congr 1; omega
        rw [hP1, Finset.sum_range_add]
        have h0 : ∑ k ∈ Finset.range 1, (if k = 0 then 2 * root.m else
            if 0 < k / P ∧ k % P < numGroups x b (k / P) then 2 * Δ * groupSize x b (k / P) else 0) =
            2 * root.m := by simp
        have hRest : ∑ k ∈ Finset.range (P - 1),
            (if 1 + k = 0 then 2 * root.m else
              if 0 < (1 + k) / P ∧ (1 + k) % P < numGroups x b ((1 + k) / P) then
                2 * Δ * groupSize x b ((1 + k) / P) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          have hklt : 1 + k < P := by rw [Finset.mem_range] at hk; omega
          have hdiv : (1 + k) / P = 0 := Nat.div_eq_of_lt hklt
          simp [hdiv]
        rw [h0, hRest, Nat.add_zero]
      have hSecond : ∑ k ∈ Finset.range (D * P),
          (if P + k = 0 then 2 * root.m
            else if 0 < (P + k) / P ∧ (P + k) % P < numGroups x b ((P + k) / P) then
              2 * Δ * groupSize x b ((P + k) / P) else 0) =
          ∑ t ∈ Finset.range D, ∑ g ∈ Finset.range P,
            if g < numGroups x b (t + 1) then 2 * Δ * groupSize x b (t + 1) else 0 := by
        clear hFirst hEach hC
        induction D with
        | zero => simp
        | succ d ih =>
          rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]
          congr 1
          apply Finset.sum_congr rfl
          intro g hg
          have hglt : g < P := Finset.mem_range.mp hg
          have hEq : P + (d * P + g) = P * (d + 1) + g := by ring
          have hDiv : (P + (d * P + g)) / P = d + 1 := by
            rw [hEq, Nat.mul_add_div hPpos, Nat.div_eq_of_lt hglt, Nat.add_zero]
          have hMod : (P + (d * P + g)) % P = g := by
            rw [hEq, Nat.mul_add_mod, Nat.mod_eq_of_lt hglt]
          have hNe : P + (d * P + g) ≠ 0 := by omega
          rw [ite_eq_right (fun h => absurd h hNe), hDiv, hMod]
          simp
      rw [hSecond]
      exact Nat.add_le_add_right hFirst _
    refine hSplit2.trans (Nat.add_le_add_left ?_ _)
    have hPerT : ∀ t < D, (∑ g ∈ Finset.range P,
        if g < numGroups x b (t + 1) then 2 * Δ * groupSize x b (t + 1) else 0) ≤
        2 * Δ * P := by
      intro t _
      have hng : numGroups x b (t + 1) ≤ P := by
        have hmul : numGroups x b (t + 1) * groupSize x b (t + 1) = P := numGroups_mul_groupSize
        have hpos := groupSize_pos (x := x) (b := b) (j := t + 1)
        nlinarith
      have hPr : Finset.range P = Finset.range (numGroups x b (t + 1) + (P - numGroups x b (t + 1))) := by
        congr 1; omega
      rw [hPr, Finset.sum_range_add]
      have h1 : ∑ g ∈ Finset.range (numGroups x b (t + 1)),
          (if g < numGroups x b (t + 1) then 2 * Δ * groupSize x b (t + 1) else 0) =
          2 * Δ * P := by
        have : ∀ g ∈ Finset.range (numGroups x b (t + 1)),
            (if g < numGroups x b (t + 1) then 2 * Δ * groupSize x b (t + 1) else 0) =
            2 * Δ * groupSize x b (t + 1) := fun g hg => ite_eq_left (Finset.mem_range.mp hg)
        rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
        calc numGroups x b (t + 1) * (2 * Δ * groupSize x b (t + 1))
          _ = 2 * Δ * (numGroups x b (t + 1) * groupSize x b (t + 1)) := by ring
          _ = 2 * Δ * P := by rw [numGroups_mul_groupSize]
      have h2' : ∑ g ∈ Finset.range (P - numGroups x b (t + 1)),
          (if numGroups x b (t + 1) + g < numGroups x b (t + 1) then
            2 * Δ * groupSize x b (t + 1) else 0) = 0 := by
        apply Finset.sum_eq_zero; intro g _; simp
      rw [h1, h2', Nat.add_zero]
    calc ∑ t ∈ Finset.range D, ∑ g ∈ Finset.range P,
          (if g < numGroups x b (t + 1) then 2 * Δ * groupSize x b (t + 1) else 0)
      _ ≤ ∑ _t ∈ Finset.range D, (2 * Δ * P) := Finset.sum_le_sum fun t ht => hPerT t (Finset.mem_range.mp ht)
      _ = 2 * D * Δ * P := by simp; ring
  have hTotal := hC.trans (Nat.add_le_add_left hSumSplit _)
  nlinarith

private lemma sec4_length_le {x b : ℕ} {root : Graph} {reply : ℕ → ℕ → BuildLevelData}
    {r L L' dMax : ℕ} {bh : ℕ → ℕ}
    (hb : 0 < b)
    (hgood : buildTopRepliesGood x b root reply (2 ^ x) r (49 * L' + 2) L L' bh)
    (hdMax : ∀ j < leafDepth x b, routePathLen (49 * L' + 2) (bh j) L ≤ dMax) :
    let D := leafDepth x b
    let P := 2 ^ x
    let H := buildTopHierarchy x b root reply
    (csrList (D * P) fun k =>
      csrList (H.host (k / P + 1) (k % P)).m (H.emb (k / P) (k % P))).length ≤
      2 * D * P + D * (49 * L' + 2) * P * (dMax + 1) + 1 := by
  dsimp only
  set D := leafDepth x b
  set P := 2 ^ x
  set Δ := 49 * L' + 2
  set H := buildTopHierarchy x b root reply
  have hPpos : 0 < P := Nat.two_pow_pos x
  have hEach : ∀ k < D * P,
      (csrList (H.host (k / P + 1) (k % P)).m (H.emb (k / P) (k % P))).length ≤
        1 + (if k % P < numGroups x b (k / P + 1) then
          Δ * groupSize x b (k / P + 1) * (dMax + 1) else 0) := by
    intro k hk
    have hjlt : k / P < D := (Nat.div_lt_iff_lt_mul hPpos).mpr hk
    by_cases hc : k % P < numGroups x b (k / P + 1)
    · have h1gs : 1 < groupSize x b (k / P) := one_lt_groupSize_of_lt_leafDepth hb hjlt
      have hp : parentGroup x b (k / P) (k % P) < numGroups x b (k / P) := by
        unfold parentGroup
        rw [Nat.div_lt_iff_lt_mul branching_pos, ← numGroups_succ]
        exact hc
      have hlc : (k % P) % branching x b (k / P) < branching x b (k / P) :=
        Nat.mod_lt _ branching_pos
      have hG := hgood (k / P) (parentGroup x b (k / P) (k % P)) h1gs hp
      obtain ⟨_, hval, hloop, hsupp, hdeg, _, _⟩ := hG.graph _ hlc
      have hm := child_m_le_of_good hval hloop hsupp hdeg
      have hΔeq : buildLevelDegree L' = Δ := rfl
      rw [hΔeq] at hm
      have hhost : H.host (k / P + 1) (k % P) =
          (reply (k / P) (parentGroup x b (k / P) (k % P))).host ((k % P) % branching x b (k / P)) := by
        simp [H, buildTopHierarchy, hc]
      have hemb : H.emb (k / P) (k % P) =
          (reply (k / P) (parentGroup x b (k / P) (k % P))).emb ((k % P) % branching x b (k / P)) := by
        simp [H, buildTopHierarchy, hc]
      rw [hhost, hemb]
      have hRow := csrList_length_le_sum (k := ((reply (k / P) (parentGroup x b (k / P) (k % P))).host
          ((k % P) % branching x b (k / P))).m)
        (rows := (reply (k / P) (parentGroup x b (k / P) (k % P))).emb ((k % P) % branching x b (k / P)))
        (B := fun _ => dMax)
        (fun e he => (hG.embedLength _ hlc e he).trans (hdMax _ hjlt))
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, hc, ↓reduceIte] at hRow ⊢
      nlinarith
    · have hhost : (H.host (k / P + 1) (k % P)).m = 0 := by simp [H, buildTopHierarchy, hc, Graph.m]
      rw [hhost]
      simp [csrList, csrOffsets, csrData, hc]
  have hC := csrList_length_le_sum hEach
  have hSumSplit : ∑ k ∈ Finset.range (D * P),
      (1 + (if k % P < numGroups x b (k / P + 1) then
        Δ * groupSize x b (k / P + 1) * (dMax + 1) else 0)) ≤
      D * P + D * Δ * P * (dMax + 1) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    apply Nat.add_le_add_left
    have hDsum : ∑ k ∈ Finset.range (D * P),
        (if k % P < numGroups x b (k / P + 1) then
          Δ * groupSize x b (k / P + 1) * (dMax + 1) else 0) =
        ∑ t ∈ Finset.range D, ∑ g ∈ Finset.range P,
          if g < numGroups x b (t + 1) then
            Δ * groupSize x b (t + 1) * (dMax + 1) else 0 := by
      clear hEach hC
      induction D with
      | zero => simp
      | succ d ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]
        congr 1
        apply Finset.sum_congr rfl
        intro g hg
        have hglt : g < P := Finset.mem_range.mp hg
        have hDiv : (d * P + g) / P = d := by
          rw [Nat.mul_comm d P, Nat.mul_add_div hPpos, Nat.div_eq_of_lt hglt, Nat.add_zero]
        have hMod : (d * P + g) % P = g := by
          rw [Nat.mul_comm d P, Nat.mul_add_mod, Nat.mod_eq_of_lt hglt]
        simp [hDiv, hMod]
    rw [hDsum]
    have hPerT : ∀ t < D, (∑ g ∈ Finset.range P,
        if g < numGroups x b (t + 1) then Δ * groupSize x b (t + 1) * (dMax + 1) else 0) =
        Δ * P * (dMax + 1) := by
      intro t _
      have hng : numGroups x b (t + 1) ≤ P := by
        have hmul : numGroups x b (t + 1) * groupSize x b (t + 1) = P := numGroups_mul_groupSize
        have hpos := groupSize_pos (x := x) (b := b) (j := t + 1)
        nlinarith
      have hPr : Finset.range P = Finset.range (numGroups x b (t + 1) + (P - numGroups x b (t + 1))) := by
        congr 1; omega
      rw [hPr, Finset.sum_range_add]
      have h1 : ∑ g ∈ Finset.range (numGroups x b (t + 1)),
          (if g < numGroups x b (t + 1) then Δ * groupSize x b (t + 1) * (dMax + 1) else 0) =
          Δ * P * (dMax + 1) := by
        have : ∀ g ∈ Finset.range (numGroups x b (t + 1)),
            (if g < numGroups x b (t + 1) then Δ * groupSize x b (t + 1) * (dMax + 1) else 0) =
            Δ * groupSize x b (t + 1) * (dMax + 1) := fun g hg => ite_eq_left (Finset.mem_range.mp hg)
        rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
        calc numGroups x b (t + 1) * (Δ * groupSize x b (t + 1) * (dMax + 1))
          _ = Δ * (numGroups x b (t + 1) * groupSize x b (t + 1)) * (dMax + 1) := by ring
          _ = Δ * P * (dMax + 1) := by rw [numGroups_mul_groupSize]
      have h2' : ∑ g ∈ Finset.range (P - numGroups x b (t + 1)),
          (if numGroups x b (t + 1) + g < numGroups x b (t + 1) then
            Δ * groupSize x b (t + 1) * (dMax + 1) else 0) = 0 := by
        apply Finset.sum_eq_zero; intro g _; simp
      rw [h1, h2', Nat.add_zero]
    exact le_of_eq (calc ∑ t ∈ Finset.range D, ∑ g ∈ Finset.range P,
          (if g < numGroups x b (t + 1) then Δ * groupSize x b (t + 1) * (dMax + 1) else 0)
      _ = ∑ _t ∈ Finset.range D, (Δ * P * (dMax + 1)) :=
          Finset.sum_congr rfl fun t ht => hPerT t (Finset.mem_range.mp ht)
      _ = D * Δ * P * (dMax + 1) := by simp; ring)
  have hTotal := hC.trans (Nat.add_le_add_left hSumSplit _)
  nlinarith

private lemma sec5_length_le {x b : ℕ} {root : Graph} {reply : ℕ → ℕ → BuildLevelData}
    {r L L' dMax : ℕ} {bh : ℕ → ℕ}
    (hb : 0 < b)
    (hgood : buildTopRepliesGood x b root reply (2 ^ x) r (49 * L' + 2) L L' bh)
    (hdMax : ∀ j < leafDepth x b, routePathLen (49 * L' + 2) (bh j) L ≤ dMax) :
    let D := leafDepth x b
    let P := 2 ^ x
    let H := buildTopHierarchy x b root reply
    (csrList (D * P * 2 ^ b) fun k =>
      let l := H.conn (pairOfIdx x b k).1 (pairOfIdx x b k).2.1 (pairOfIdx x b k).2.2
      csrList l.length fun i => connWords (l.getD i (0, 0, []))).length ≤
      2 * D * P * 2 ^ b + D * P * 2 ^ b * (dMax + 3) + 1 := by
  dsimp only
  set D := leafDepth x b
  set P := 2 ^ x
  set B := 2 ^ b
  set H := buildTopHierarchy x b root reply
  have hPpos : 0 < P := Nat.two_pow_pos x
  have hBpos : 0 < B := Nat.two_pow_pos b
  have hEach : ∀ k < D * P * B,
      (let l := H.conn (pairOfIdx x b k).1 (pairOfIdx x b k).2.1 (pairOfIdx x b k).2.2
       csrList l.length fun i => connWords (l.getD i (0, 0, []))).length ≤
        1 + (if (k / B) % P < numGroups x b ((k / B) / P + 1) then
          groupSize x b ((k / B) / P + 1) * (dMax + 3) else 0) := by
    intro k hk
    set j := (k / B) / P
    set c := (k / B) % P
    set c' := (pairOfIdx x b k).2.2
    have hj_eq : (pairOfIdx x b k).1 = j := rfl
    have hc_eq : (pairOfIdx x b k).2.1 = c := rfl
    have hjlt : j < D := by
      have hq : k / B < D * P := (Nat.div_lt_iff_lt_mul hBpos).mpr hk
      exact (Nat.div_lt_iff_lt_mul hPpos).mpr hq
    rw [hj_eq, hc_eq]
    by_cases hact : c < c' ∧ c' < numGroups x b (j + 1) ∧ parentGroup x b j c = parentGroup x b j c'
    · obtain ⟨hlt, hc'ng, hpar⟩ := hact
      have hcng : c < numGroups x b (j + 1) := hlt.trans hc'ng
      have h1gs : 1 < groupSize x b j := one_lt_groupSize_of_lt_leafDepth hb hjlt
      have hp : parentGroup x b j c < numGroups x b j := by
        unfold parentGroup
        rw [Nat.div_lt_iff_lt_mul branching_pos, ← numGroups_succ]
        exact hcng
      have hlc : c % branching x b j < branching x b j := Nat.mod_lt _ branching_pos
      have hlc' : c' % branching x b j < branching x b j := Nat.mod_lt _ branching_pos
      have hlclt : c % branching x b j < c' % branching x b j := by
        have h1 := buildTopChild_decompose x b j c
        have h2 := buildTopChild_decompose x b j c'
        rw [hpar] at h1; omega
      have hG := hgood j (parentGroup x b j c) h1gs hp
      have hconn : H.conn j c c' =
          (reply j (parentGroup x b j c)).conn (c % branching x b j) (c' % branching x b j) := by
        simp [H, buildTopHierarchy, hlt, hc'ng, hpar]
      rw [hconn]
      have hlen := conn_length_eq_s hG hlc hlc' hlclt
      have hRow := csrList_length_le_sum
        (k := ((reply j (parentGroup x b j c)).conn (c % branching x b j) (c' % branching x b j)).length)
        (rows := fun i => connWords (((reply j (parentGroup x b j c)).conn
          (c % branching x b j) (c' % branching x b j)).getD i (0, 0, [])))
        (B := fun _ => dMax + 2)
        (fun i hi => by
          rw [List.getD_eq_getElem _ _ hi]
          have hmem := List.getElem_mem hi
          have hw := (hG.connWalk _ hlc _ hlc' hlclt _ hmem).2
          have hd := hdMax j hjlt
          unfold connWords
          simp only [List.length_cons]
          omega)
      dsimp only
      rw [hlen] at hRow ⊢
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hRow
      rw [ite_eq_left hcng]
      change _ ≤ 1 + groupSize x b (j + 1) * (dMax + 3)
      have hmul : groupSize x b (j + 1) * (dMax + 3) =
          groupSize x b (j + 1) + groupSize x b (j + 1) * (dMax + 2) := by ring
      omega
    · have hconn : H.conn j c c' = [] := by simp [H, buildTopHierarchy, hact]
      rw [hconn]
      simp [csrList, csrOffsets, csrData]
  have hC := csrList_length_le_sum hEach
  have hSumSplit : ∑ k ∈ Finset.range (D * P * B),
      (1 + (if (k / B) % P < numGroups x b ((k / B) / P + 1) then
        groupSize x b ((k / B) / P + 1) * (dMax + 3) else 0)) ≤
      D * P * B + D * P * B * (dMax + 3) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    apply Nat.add_le_add_left
    have hFactorB : ∀ n, ∑ k ∈ Finset.range (n * B),
        (if (k / B) % P < numGroups x b ((k / B) / P + 1) then
          groupSize x b ((k / B) / P + 1) * (dMax + 3) else 0) =
        B * ∑ q ∈ Finset.range n,
          (if q % P < numGroups x b (q / P + 1) then
            groupSize x b (q / P + 1) * (dMax + 3) else 0) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih, Nat.mul_add]
        congr 1
        have hconst : ∀ r ∈ Finset.range B,
            (if ((n * B + r) / B) % P < numGroups x b (((n * B + r) / B) / P + 1) then
              groupSize x b (((n * B + r) / B) / P + 1) * (dMax + 3) else 0) =
            (if n % P < numGroups x b (n / P + 1) then
              groupSize x b (n / P + 1) * (dMax + 3) else 0) := by
          intro r hr
          have hrlt : r < B := Finset.mem_range.mp hr
          have hdiv : (n * B + r) / B = n := by
            rw [Nat.mul_comm n B, Nat.mul_add_div hBpos, Nat.div_eq_of_lt hrlt, Nat.add_zero]
          rw [hdiv]
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [hFactorB (D * P)]
    have hDsum : ∑ q ∈ Finset.range (D * P),
        (if q % P < numGroups x b (q / P + 1) then
          groupSize x b (q / P + 1) * (dMax + 3) else 0) =
        D * P * (dMax + 3) := by
      have hSplit : ∑ q ∈ Finset.range (D * P),
          (if q % P < numGroups x b (q / P + 1) then
            groupSize x b (q / P + 1) * (dMax + 3) else 0) =
          ∑ t ∈ Finset.range D, ∑ g ∈ Finset.range P,
            if g < numGroups x b (t + 1) then
              groupSize x b (t + 1) * (dMax + 3) else 0 := by
        clear hEach hC hFactorB
        induction D with
        | zero => simp
        | succ d ih =>
          rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]
          congr 1
          apply Finset.sum_congr rfl
          intro g hg
          have hglt : g < P := Finset.mem_range.mp hg
          have hDiv : (d * P + g) / P = d := by
            rw [Nat.mul_comm d P, Nat.mul_add_div hPpos, Nat.div_eq_of_lt hglt, Nat.add_zero]
          have hMod : (d * P + g) % P = g := by
            rw [Nat.mul_comm d P, Nat.mul_add_mod, Nat.mod_eq_of_lt hglt]
          simp [hDiv, hMod]
      rw [hSplit]
      have hPerT : ∀ t < D, (∑ g ∈ Finset.range P,
          if g < numGroups x b (t + 1) then groupSize x b (t + 1) * (dMax + 3) else 0) =
          P * (dMax + 3) := by
        intro t _
        have hng : numGroups x b (t + 1) ≤ P := by
          have hmul : numGroups x b (t + 1) * groupSize x b (t + 1) = P := numGroups_mul_groupSize
          have hpos := groupSize_pos (x := x) (b := b) (j := t + 1)
          nlinarith
        have hPr : Finset.range P = Finset.range (numGroups x b (t + 1) + (P - numGroups x b (t + 1))) := by
          congr 1; omega
        rw [hPr, Finset.sum_range_add]
        have h1 : ∑ g ∈ Finset.range (numGroups x b (t + 1)),
            (if g < numGroups x b (t + 1) then groupSize x b (t + 1) * (dMax + 3) else 0) =
            P * (dMax + 3) := by
          have : ∀ g ∈ Finset.range (numGroups x b (t + 1)),
              (if g < numGroups x b (t + 1) then groupSize x b (t + 1) * (dMax + 3) else 0) =
              groupSize x b (t + 1) * (dMax + 3) := fun g hg => ite_eq_left (Finset.mem_range.mp hg)
          rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
          calc numGroups x b (t + 1) * (groupSize x b (t + 1) * (dMax + 3))
            _ = (numGroups x b (t + 1) * groupSize x b (t + 1)) * (dMax + 3) := by ring
            _ = P * (dMax + 3) := by rw [numGroups_mul_groupSize]
        have h2' : ∑ g ∈ Finset.range (P - numGroups x b (t + 1)),
            (if numGroups x b (t + 1) + g < numGroups x b (t + 1) then
              groupSize x b (t + 1) * (dMax + 3) else 0) = 0 := by
          apply Finset.sum_eq_zero; intro g _; simp
        rw [h1, h2', Nat.add_zero]
      calc ∑ t ∈ Finset.range D, ∑ g ∈ Finset.range P,
            (if g < numGroups x b (t + 1) then groupSize x b (t + 1) * (dMax + 3) else 0)
        _ = ∑ _t ∈ Finset.range D, (P * (dMax + 3)) :=
            Finset.sum_congr rfl fun t ht => hPerT t (Finset.mem_range.mp ht)
        _ = D * P * (dMax + 3) := by simp; ring
    rw [hDsum]
    nlinarith
  have hTotal := hC.trans (Nat.add_le_add_left hSumSplit _)
  nlinarith

/-- Bound `S.encode.length` and the section directory sizes by `G.m * gammaHP a d M`. -/
theorem buildTopStatic_encode_length_le {G : Graph} {phiNum phiDen a M : ℕ}
    {reply : ℕ → ℕ → BuildLevelData}
    (h1 : 1 ≤ phiNum) (h2 : phiNum ≤ phiDen) (hG : G.IsValid) (hm : 1 ≤ G.m) (hmM : G.m ≤ M)
    (hcond : G.IsConductanceExpanderOn G.verts ((phiNum : ℝ) / (phiDen : ℝ)))
    (ha : buildTopMinA ≤ a)
    (hgood : buildTopRepliesGood (Nat.clog 2 (2 * G.m)) (buildTopBranch (Nat.clog 2 (2 * G.m)) G.m)
      (hostGraph cloud G) reply (2 ^ Nat.clog 2 (2 * G.m)) (depthOf G.m)
      (49 * (Nat.clog 2 (2 * G.m) + 1) + 2) (Nat.clog 2 (2 * G.m) + 1)
      (Nat.clog 2 (2 * G.m) + 1) (buildTopBh (Nat.clog 2 (2 * G.m)) G.m (dOf phiNum phiDen))) :
    let x := Nat.clog 2 (2 * G.m)
    let b := buildTopBranch x G.m
    let D := leafDepth x b
    let d := dOf phiNum phiDen
    let S : StaticData := ⟨x, b, hostOwner G, hostLabel G,
      buildTopHierarchy x b (hostGraph cloud G) reply⟩
    S.encode.length ≤ G.m * gammaHP a d M ∧
    (D + 1) * 2 ^ x + D * 2 ^ x * 2 ^ b ≤ G.m * gammaHP a d M := by
  dsimp only
  set x := Nat.clog 2 (2 * G.m)
  set b := buildTopBranch x G.m
  set D := leafDepth x b
  set P := 2 ^ x
  set d := dOf phiNum phiDen
  set H := buildTopHierarchy x b (hostGraph cloud G) reply
  set S : StaticData := ⟨x, b, hostOwner G, hostLabel G, H⟩
  obtain ⟨hpc, _, hxpos, hlt4m, hxX⟩ := buildTop_x_facts hG hm
  have hbpos : 0 < b := buildTopBranch_pos hxpos
  obtain ⟨hφ, hd1, _⟩ := dOf_spec h1 h2
  have hroot_m : (hostGraph cloud G).m ≤ 12 * G.m := by
    have hmIn : 1 ≤ (G.inside G.verts).length := by rw [inside_verts_length hG]; exact hm
    have h := hostGraph_m_le (G := G) isCloudExpander_cloud hmIn
    rwa [inside_verts_length hG] at h
  have ha223 : 223 + 2 * ParamConfig.default.a₀ ≤ a := two_two_three_le_buildTopMinA.trans ha
  have ha1 : 1 ≤ a := one_le_buildTopMinA.trans ha
  have hD_le : D ≤ bigJ M := (leafDepth_buildTopBranch_le hxpos hxX).trans (depthOf_le_bigJ hmM)
  have h2b_le : 2 ^ b ≤ bigKB M := (buildTopBranch_pow_le x G.m).trans (branchOf_le_bigKB hmM)
  have h1_le_2b : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hu_le : uOf a G.m ≤ bigUX a M := uOf_le_bigUX a hmM
  have hJ2 : 2 ≤ bigJ M := two_le_depthOf M
  have hUX1 : 1 ≤ bigUX a M := Nat.one_le_two_pow
  have hdMax : ∀ j < D, routePathLen (49 * (x + 1) + 2) (buildTopBh x G.m d j) (x + 1) ≤
      hOf d * bigUX a M ^ bigJ M := by
    intro j hj
    have hbh1 : 1 ≤ buildTopBh x G.m d j := by
      cases j with
      | zero => simp [buildTopBh]; omega
      | succ _ =>
        change 1 ≤ 4 * PParam ParamConfig.default P (depthOf G.m)
        have := one_le_PParam ParamConfig.default P (depthOf G.m); omega
    have hρ := BuildParams.num_rho_le (route := buildTopDummyRoute) (core := buildTopDummyCore)
      hG hm hφ hcond (cfg := ParamConfig.default) (a := a) (dd := d) ha223 hd1 j
    rw [← buildTopBh_eq_numBh hG d j] at hρ
    have hκ : routeCong (49 * (x + 1) + 2) (buildTopBh x G.m d j) (x + 1) ≤
        lvlBound (hOf d) (uOf a G.m) j := by
      have hρ' : buildLevelDegree (x + 1) *
          routeCong (49 * (x + 1) + 2) (buildTopBh x G.m d j) (x + 1) ≤
          lvlBound (hOf d) (uOf a G.m) j := by
        simpa [buildLevelDegree, numParams, hpc] using hρ
      exact (Nat.le_mul_of_pos_left _ (by unfold buildLevelDegree; omega)).trans hρ'
    have hpl := (pathLen_le_cong (by omega) hbh1 (by omega)).trans hκ
    have hH1 : 1 ≤ hOf d := by unfold hOf; exact Nat.one_le_pow _ _ (by omega)
    have hU1 : 1 ≤ uOf a G.m := Nat.one_le_two_pow
    have hProd1 : 1 ≤ ∏ k ∈ Finset.range j, lvlBound (hOf d) (uOf a G.m) k :=
      Finset.one_le_prod fun k _ => one_le_lvlBound hH1 hU1 k
    have hlvl : lvlBound (hOf d) (uOf a G.m) j ≤ hOf d * bigUX a M ^ bigJ M := by
      calc lvlBound (hOf d) (uOf a G.m) j
        _ ≤ lvlBound (hOf d) (uOf a G.m) j * ∏ k ∈ Finset.range j, lvlBound (hOf d) (uOf a G.m) k :=
            Nat.le_mul_of_pos_right _ hProd1
        _ = hOf d * uOf a G.m ^ (j + 1) := lvlBound_mul_prod _ _ _
        _ ≤ hOf d * bigUX a M ^ (j + 1) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hu_le _)
        _ ≤ hOf d * bigUX a M ^ bigJ M := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hUX1 (by omega))
    exact hpl.trans hlvl
  clear ha ha223 hcond hφ h1 h2
  have hSec3 := sec3_length_le hbpos hroot_m hgood
  have hSec4 := sec4_length_le hbpos hgood hdMax
  have hSec5 := sec5_length_le hbpos hgood hdMax
  clear hgood hdMax
  have hEncLen : S.encode.length = 7 + (S.sections.map List.length).sum := by
    unfold StaticData.encode layoutList
    rw [csrList, List.length_append, length_csrOffsets, buildTopSections_count]
    have hData : (csrData 6 (S.sections.getD · [])).length = (S.sections.map List.length).sum := by
      simp [csrData, StaticData.sections, List.range_succ]; omega
    rw [hData]
  have hSecSum : (S.sections.map List.length).sum =
      3 + P + (hostGraph cloud G).m +
      (csrList ((D + 1) * P) fun k => (H.host (k / P) (k % P)).encode).length +
      (csrList (D * P) fun k =>
        csrList (H.host (k / P + 1) (k % P)).m (H.emb (k / P) (k % P))).length +
      (csrList (D * P * 2 ^ b) fun k =>
        let l := H.conn (pairOfIdx x b k).1 (pairOfIdx x b k).2.1 (pairOfIdx x b k).2.2
        csrList l.length fun i => connWords (l.getD i (0, 0, []))).length := by
    have hHost0 : (H.host 0 0).m = (hostGraph cloud G).m := by simp [H, buildTopHierarchy]
    have hX : S.x = x := rfl
    have hB : S.b = b := rfl
    have hH : S.H = H := rfl
    have hN : S.numTerm = P := rfl
    simp only [StaticData.sections, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, tabList, List.length_map, List.length_range,
      hX, hB, hH, hN, hHost0]
    change _ = _
    ring
  have hDelta_le : 49 * (x + 1) + 2 ≤ 51 * bigUX a M := by
    have hvx : xOf G.m + 2 ≤ 2 ^ vxOf G.m := Nat.le_pow_clog (by decide) _
    have hpow : 2 ^ vxOf G.m ≤ uOf a G.m := by
      unfold uOf
      have hdm : 2 ≤ depthOf G.m := two_le_depthOf G.m
      have h1ad : 1 ≤ a * depthOf G.m := Nat.mul_pos ha1 (by omega)
      exact Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left _ h1ad)
    have hx_le : x + 1 ≤ 2 ^ vxOf G.m := by omega
    have := hx_le.trans (hpow.trans hu_le)
    omega
  set HD := (1 + (2 + d) ^ 4) ^ 2
  have h1HD : 1 ≤ HD := Nat.one_le_pow 2 _ (by omega)
  have hdMax_le : hOf d * bigUX a M ^ bigJ M + 3 ≤ 4 * HD * bigUX a M ^ bigJ M := by
    have hH_le : hOf d ≤ HD := by
      unfold hOf HD
      calc (2 + d) ^ 4 ≤ 1 + (2 + d) ^ 4 := by omega
        _ ≤ (1 + (2 + d) ^ 4) ^ 2 := Nat.le_self_pow (by decide) _
    have h1u : 1 ≤ HD * bigUX a M ^ bigJ M :=
      Nat.mul_pos h1HD (Nat.one_le_pow _ _ hUX1)
    have hle : hOf d * bigUX a M ^ bigJ M ≤ HD * bigUX a M ^ bigJ M :=
      Nat.mul_le_mul_right _ hH_le
    calc hOf d * bigUX a M ^ bigJ M + 3
      _ ≤ HD * bigUX a M ^ bigJ M + 3 * (HD * bigUX a M ^ bigJ M) := by omega
      _ = 4 * HD * bigUX a M ^ bigJ M := by ring
  set UJ := bigUX a M ^ (bigJ M + 1)
  have hUJ1 : 1 ≤ UJ := Nat.one_le_pow _ _ hUX1
  have hGam : 2 ^ 12 * 64 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ ≤ gammaHP a d M := by
    unfold gammaHP
    have h4 : 64 ≤ 4 ^ (bigJ M + 1) := by
      have : 4 ^ 3 ≤ 4 ^ (bigJ M + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using this
    have hJ : bigJ M + 2 ≤ (bigJ M + 2) ^ 4 := Nat.le_self_pow (by decide) _
    have hKB : bigKB M + 1 ≤ (bigKB M + 1) ^ 4 := Nat.le_self_pow (by decide) _
    have hUXJ : UJ ≤ bigUX a M ^ (2 * bigJ M + 2) :=
      Nat.pow_le_pow_right hUX1 (by omega)
    calc 2 ^ 12 * 64 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ
      _ = 2 ^ 12 * (bigJ M + 2) * 64 * (bigKB M + 1) * HD * UJ := by ring
      _ ≤ 2 ^ 12 * (bigJ M + 2) ^ 4 * 4 ^ (bigJ M + 1) * (bigKB M + 1) ^ 4 *
            HD * bigUX a M ^ (2 * bigJ M + 2) := by gcongr
  have hUnit : (D + 1) * P * 2 ^ b ≤ 4 * G.m * (bigJ M + 2) * (bigKB M + 1) := by
    calc (D + 1) * P * 2 ^ b
      _ ≤ (bigJ M + 2) * (4 * G.m) * (bigKB M + 1) := by
          gcongr <;> omega
      _ = 4 * G.m * (bigJ M + 2) * (bigKB M + 1) := by ring
  have hDirLe : (D + 1) * P + D * P * 2 ^ b ≤ 2 * ((D + 1) * P * 2 ^ b) := by
    have h1' : (D + 1) * P ≤ (D + 1) * P * 2 ^ b := Nat.le_mul_of_pos_right _ h1_le_2b
    have h2' : D * P * 2 ^ b ≤ (D + 1) * P * 2 ^ b := by gcongr; omega
    omega
  have hProd : (bigJ M + 2) * (bigKB M + 1) ≤ (bigJ M + 2) * (bigKB M + 1) * HD * UJ := by
    have h1' : 1 ≤ HD * UJ := Nat.mul_pos h1HD hUJ1
    calc (bigJ M + 2) * (bigKB M + 1)
      _ = (bigJ M + 2) * (bigKB M + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (bigJ M + 2) * (bigKB M + 1) * (HD * UJ) := Nat.mul_le_mul_left _ h1'
      _ = _ := by ring
  have hPart2 : (D + 1) * P + D * P * 2 ^ b ≤ G.m * gammaHP a d M := by
    calc (D + 1) * P + D * P * 2 ^ b
      _ ≤ 2 * ((D + 1) * P * 2 ^ b) := hDirLe
      _ ≤ 2 * (4 * G.m * (bigJ M + 2) * (bigKB M + 1)) := Nat.mul_le_mul_left 2 hUnit
      _ = G.m * (8 * ((bigJ M + 2) * (bigKB M + 1))) := by ring
      _ ≤ G.m * (2 ^ 12 * 64 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ) := by
          apply Nat.mul_le_mul_left
          calc 8 * ((bigJ M + 2) * (bigKB M + 1))
            _ ≤ 8 * ((bigJ M + 2) * (bigKB M + 1) * HD * UJ) := Nat.mul_le_mul_left 8 hProd
            _ ≤ 2 ^ 12 * 64 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ := by
                have : 8 ≤ 2 ^ 12 * 64 := by decide
                calc 8 * ((bigJ M + 2) * (bigKB M + 1) * HD * UJ)
                  _ ≤ (2 ^ 12 * 64) * ((bigJ M + 2) * (bigKB M + 1) * HD * UJ) := by gcongr
                  _ = _ := by ring
      _ ≤ G.m * gammaHP a d M := Nat.mul_le_mul_left G.m hGam
  refine ⟨?_, hPart2⟩
  set Δ := 49 * (x + 1) + 2
  set dMax := hOf d * bigUX a M ^ bigJ M
  have hUJ_eq : bigUX a M * bigUX a M ^ bigJ M = UJ := by
    change bigUX a M * bigUX a M ^ bigJ M = bigUX a M ^ (bigJ M + 1)
    rw [pow_succ, Nat.mul_comm]
  have hUJ_ge : bigUX a M ^ bigJ M ≤ UJ := Nat.pow_le_pow_right hUX1 (by omega)
  have hBigTerm : D * Δ * P * (dMax + 3) ≤
      (bigJ M + 2) * (51 * bigUX a M) * (4 * G.m) * (4 * HD * bigUX a M ^ bigJ M) := by
    gcongr; omega
  have hDPB_d : D * P * 2 ^ b * (dMax + 3) ≤
      (bigJ M + 2) * (4 * G.m) * (bigKB M + 1) * (4 * HD * bigUX a M ^ bigJ M) := by
    gcongr <;> omega
  have hBase : 13 + 36 * G.m + 6 * ((D + 1) * P) + 2 * (D * P * 2 ^ b) ≤
      100 * (G.m * (bigJ M + 2) * (bigKB M + 1)) := by
    have h1' : (D + 1) * P ≤ 4 * (G.m * (bigJ M + 2) * (bigKB M + 1)) := by
      calc (D + 1) * P ≤ (D + 1) * P * 2 ^ b := Nat.le_mul_of_pos_right _ h1_le_2b
        _ ≤ 4 * G.m * (bigJ M + 2) * (bigKB M + 1) := hUnit
        _ = 4 * (G.m * (bigJ M + 2) * (bigKB M + 1)) := by ring
    have h2' : D * P * 2 ^ b ≤ 4 * (G.m * (bigJ M + 2) * (bigKB M + 1)) := by
      calc D * P * 2 ^ b ≤ (D + 1) * P * 2 ^ b := by gcongr; omega
        _ ≤ 4 * G.m * (bigJ M + 2) * (bigKB M + 1) := hUnit
        _ = 4 * (G.m * (bigJ M + 2) * (bigKB M + 1)) := by ring
    have h3' : G.m ≤ G.m * (bigJ M + 2) * (bigKB M + 1) := by
      have : 1 ≤ (bigJ M + 2) * (bigKB M + 1) := Nat.mul_pos (by omega) (by omega)
      calc G.m = G.m * 1 := (Nat.mul_one _).symm
        _ ≤ G.m * ((bigJ M + 2) * (bigKB M + 1)) := Nat.mul_le_mul_left _ this
        _ = _ := by ring
    omega
  have hEncRaw : S.encode.length ≤
      (13 + 36 * G.m + 6 * ((D + 1) * P) + 2 * (D * P * 2 ^ b)) +
      3 * (D * Δ * P * (dMax + 3)) + D * P * 2 ^ b * (dMax + 3) := by
    have hS3 : (csrList ((D + 1) * P) fun k => (H.host (k / P) (k % P)).encode).length ≤
        3 * ((D + 1) * P) + 24 * G.m + 2 * (D * Δ * P) + 1 := by
      rw [show 3 * ((D + 1) * P) = 3 * (D + 1) * P by ring,
        show 2 * (D * Δ * P) = 2 * D * Δ * P by ring]
      exact hSec3
    have hS4 : (csrList (D * P) fun k =>
        csrList (H.host (k / P + 1) (k % P)).m (H.emb (k / P) (k % P))).length ≤
        2 * (D * P) + D * Δ * P * (dMax + 1) + 1 := by
      rw [show 2 * (D * P) = 2 * D * P by ring]
      exact hSec4
    have hS5 : (csrList (D * P * 2 ^ b) fun k =>
        let l := H.conn (pairOfIdx x b k).1 (pairOfIdx x b k).2.1 (pairOfIdx x b k).2.2
        csrList l.length fun i => connWords (l.getD i (0, 0, []))).length ≤
        2 * (D * P * 2 ^ b) + D * P * 2 ^ b * (dMax + 3) + 1 := by
      rw [show 2 * (D * P * 2 ^ b) = 2 * D * P * 2 ^ b by ring]
      exact hSec5
    have h1' : 2 * (D * Δ * P) ≤ 2 * (D * Δ * P * (dMax + 3)) :=
      Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
    have h2' : D * Δ * P * (dMax + 1) ≤ D * Δ * P * (dMax + 3) := by gcongr; omega
    have h3' : P ≤ (D + 1) * P := Nat.le_mul_of_pos_left _ (Nat.succ_pos D)
    have h4' : D * P ≤ (D + 1) * P := by gcongr; omega
    omega
  have hAll : S.encode.length ≤
      G.m * (3000 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ) := by
    have hA : (13 + 36 * G.m + 6 * ((D + 1) * P) + 2 * (D * P * 2 ^ b)) ≤
        G.m * (100 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ) := by
      calc _ ≤ 100 * (G.m * (bigJ M + 2) * (bigKB M + 1)) := hBase
        _ = G.m * (100 * ((bigJ M + 2) * (bigKB M + 1))) := by ring
        _ ≤ G.m * (100 * ((bigJ M + 2) * (bigKB M + 1) * HD * UJ)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hProd)
        _ = _ := by ring
    have hB : 3 * (D * Δ * P * (dMax + 3)) ≤
        G.m * (2448 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ) := by
      have hKB1 : 1 ≤ bigKB M + 1 := by omega
      calc 3 * (D * Δ * P * (dMax + 3))
        _ ≤ 3 * ((bigJ M + 2) * (51 * bigUX a M) * (4 * G.m) *
              (4 * HD * bigUX a M ^ bigJ M)) := Nat.mul_le_mul_left 3 hBigTerm
        _ = G.m * (2448 * (bigJ M + 2) * 1 * HD * (bigUX a M * bigUX a M ^ bigJ M)) := by ring
        _ = G.m * (2448 * (bigJ M + 2) * 1 * HD * UJ) := by rw [hUJ_eq]
        _ ≤ G.m * (2448 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ) := by gcongr
    have hC : D * P * 2 ^ b * (dMax + 3) ≤
        G.m * (16 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ) := by
      calc D * P * 2 ^ b * (dMax + 3)
        _ ≤ (bigJ M + 2) * (4 * G.m) * (bigKB M + 1) * (4 * HD * bigUX a M ^ bigJ M) := hDPB_d
        _ = G.m * (16 * (bigJ M + 2) * (bigKB M + 1) * HD * bigUX a M ^ bigJ M) := by ring
        _ ≤ G.m * (16 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ) := by gcongr
    have hSum3 : G.m * (100 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ) +
        G.m * (2448 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ) +
        G.m * (16 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ) ≤
        G.m * (3000 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ) := by
      have : (100 + 2448 + 16) ≤ 3000 := by decide
      calc _ = G.m * ((100 + 2448 + 16) * ((bigJ M + 2) * (bigKB M + 1) * HD * UJ)) := by ring
        _ ≤ G.m * (3000 * ((bigJ M + 2) * (bigKB M + 1) * HD * UJ)) := by gcongr
        _ = _ := by ring
    exact hEncRaw.trans ((Nat.add_le_add (Nat.add_le_add hA hB) hC).trans hSum3)
  refine hAll.trans (Nat.mul_le_mul_left G.m ?_)
  refine le_trans ?_ hGam
  have : 3000 ≤ 2 ^ 12 * 64 := by decide
  calc 3000 * (bigJ M + 2) * (bigKB M + 1) * HD * UJ
    _ = 3000 * ((bigJ M + 2) * (bigKB M + 1) * HD * UJ) := by ring
    _ ≤ (2 ^ 12 * 64) * ((bigJ M + 2) * (bigKB M + 1) * HD * UJ) := by gcongr
    _ = _ := by ring

end MinCostFlow.HierPaths

end
