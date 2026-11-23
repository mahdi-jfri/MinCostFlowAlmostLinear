module

public import MinCostFlow.HierPaths.BuildRouterBridgeMath
public import MinCostFlow.HierPaths.BuildProgCopy
import Mathlib.Tactic.Linarith

/-!
# Output packing stage A of the static router bridge (`BuildRouterBridgeOutA`)

Implements and verifies `bridgeCountPrefixStmt`: setup + owner marking + per-pair matching edge
counting (`mem[cnt + i] = (Ms.getD i []).length`) in `O(|pairsWords| + |Ms.flatten|)` time without
touching `O(G.n)` cells, together with the disjointness and counting lemmas for valid terminal pairs.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Matched setup: `r16 = total`, `r17 = owner = vInner`, `r18 = cnt = vInner + G.n`,
`r19 = resBuf = cnt + k`, `r20 = 0`. -/
def bridgeMatchInit : Stmt :=
  .assign 16 (.load (.bin .add (.reg 12) (.const 1))) ;;
  .assign 17 (.reg 14) ;;
  .assign 18 (.bin .add (.reg 14) (.reg 15)) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 8)) ;;
  .assign 20 (.const 0)

def bridgeMarkOwnerHead : Stmt :=
  .assign 21 (.load (.bin .add (.bin .add (.reg 11) (.const 1)) (.bin .add (.reg 20) (.reg 20)))) ;;
  .assign 22 (.load (.reg 21)) ;;
  .assign 23 (.const 0)

def bridgeMarkOwnerInner : Stmt :=
  .assign 24 (.load (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 23))) ;;
  .store (.bin .add (.reg 17) (.reg 24)) (.bin .add (.reg 20) (.const 1)) ;;
  .assign 23 (.bin .add (.reg 23) (.const 1))

def bridgeMarkOwnerBody : Stmt :=
  bridgeMarkOwnerHead ;;
  (.loop (.bin .lt (.reg 23) (.reg 22)) bridgeMarkOwnerInner ;;
   .assign 20 (.bin .add (.reg 20) (.const 1)))

/-- Mark `owner[u] = i + 1` for every `i < k` and `u ∈ A_i`. -/
def bridgeMarkOwnerLoop : Stmt :=
  .loop (.bin .lt (.reg 20) (.reg 8)) bridgeMarkOwnerBody

def bridgeCountBody : Stmt :=
  .assign 21 (.load (.bin .add (.bin .add (.reg 12) (.const 2)) (.bin .add (.reg 20) (.reg 20)))) ;;
  .assign 22 (.bin .sub (.load (.bin .add (.reg 17) (.reg 21))) (.const 1)) ;;
  .assign 23 (.load (.bin .add (.reg 18) (.reg 22))) ;;
  .store (.bin .add (.reg 18) (.reg 22)) (.bin .add (.reg 23) (.const 1)) ;;
  .assign 20 (.bin .add (.reg 20) (.const 1))

/-- Count edges per matching `Ms[i]` into `cnt[i]` using `owner[e.1] - 1`. -/
def bridgeCountStmt : Stmt :=
  .assign 20 (.const 0) ;;
  .loop (.bin .lt (.reg 20) (.reg 16)) bridgeCountBody

/-- Combined setup + owner marking + per-pair counting prefix for the matched branch. -/
def bridgeCountPrefixStmt : Stmt :=
  bridgeMatchInit ;; (bridgeMarkOwnerLoop ;; bridgeCountStmt)

theorem bridgeCountPrefixStmt_noRand : bridgeCountPrefixStmt.NoRand := by
  simp [bridgeCountPrefixStmt, bridgeMatchInit, bridgeMarkOwnerLoop, bridgeMarkOwnerBody,
    bridgeMarkOwnerHead, bridgeMarkOwnerInner, bridgeCountStmt, bridgeCountBody, Stmt.NoRand]

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

private lemma runs_loop_zero_oa {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {body : Stmt} {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

private lemma runs_loop_step_oa {w c1 c2 : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {body : Stmt} {st st1 st2 : State} {v : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h1 : Runs w p ω body st .normal st1 c1)
    (h2 : Runs w p ω (.loop e body) st1 .normal st2 c2) :
    Runs w p ω (.loop e body) st .normal st2 (e.size + c1 + c2 + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st1, c1, c2, he, hv, h1, h2, rfl⟩))

/-! ## 1. Disjointness and Per-Pair Counting Lemmas -/

/-- Pairwise disjointness of `A_i` for valid terminal pairs. -/
theorem validTerminalPairs_fst_disjoint {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hv : ValidTerminalPairs X pairs) {i j : ℕ} (hi : i < pairs.length) (hj : j < pairs.length)
    (hij : i ≠ j) :
    Disjoint (pairs[i]'hi).1 (pairs[j]'hj).1 := by
  have hpw := hv.2
  have hlen_all : ∀ l : List (Finset ℕ × Finset ℕ),
      (l.flatMap fun p => [p.1, p.2]).length = 2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons _ _ ih => simp [ih]; omega
  have hlen := hlen_all pairs
  have hget : ∀ (l : List (Finset ℕ × Finset ℕ)) (t : ℕ) (ht : t < l.length),
      (l.flatMap fun p => [p.1, p.2])[2 * t]'(by rw [hlen_all l]; omega) = (l[t]'ht).1 := by
    intro l
    induction l with
    | nil => intro t ht; exact absurd ht (Nat.not_lt_zero _)
    | cons p rest ih =>
      intro t ht
      cases t with
      | zero => simp
      | succ t =>
        have hidx : 2 * (t + 1) = (2 * t) + 2 := by omega
        have h1 := ih t (Nat.lt_of_succ_lt_succ ht)
        simp only [List.flatMap_cons, List.cons_append, List.nil_append, hidx,
          List.getElem_cons_succ]
        exact h1
  rw [List.pairwise_iff_getElem] at hpw
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · have hd := hpw (2 * i) (2 * j) (by rw [hlen]; omega) (by rw [hlen]; omega) (by omega)
    rwa [hget pairs i hi, hget pairs j hj] at hd
  · have hd := hpw (2 * j) (2 * i) (by rw [hlen]; omega) (by rw [hlen]; omega) (by omega)
    rw [hget pairs j hj, hget pairs i hi] at hd
    exact hd.symm

/-- For a matched output of a valid call, `Ms.flatten.length ≤ X.card`. -/
theorem matched_total_le_cardX {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b z : ℕ}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hv : ValidTerminalPairs X pairs)
    (hSpec : RouteMatchedSpec G X pairs Δ L b z Ms emb) :
    Ms.flatten.length ≤ X.card := by
  have hlen : Ms.length = pairs.length := hSpec.1
  have hsub : ∀ i (hi : i < pairs.length), (Ms.getD i []).length ≤ (pairs[i]'hi).1.card := by
    intro i hi
    have hmi := hSpec.2.1 i hi
    have hnd : ((Ms.getD i []).map Prod.fst).Nodup := hmi.2.1
    calc (Ms.getD i []).length = ((Ms.getD i []).map Prod.fst).length := by simp
      _ = ((Ms.getD i []).map Prod.fst).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
      _ ≤ (pairs[i]'hi).1.card := Finset.card_le_card fun u hu => by
          rw [List.mem_toFinset, List.mem_map] at hu
          rcases hu with ⟨e, he, rfl⟩
          exact (hmi.1 e he).1
  have hsum : ∀ n ≤ pairs.length,
      ((Ms.take n).map List.length).sum ≤ ((List.range n).map fun i => (pairs.getD i (∅, ∅)).1.card).sum := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.take_succ_eq_append_getElem (by omega), List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
      have h1 := ih (Nat.le_of_succ_le hn)
      have h2 := hsub n hn
      rw [List.getD_eq_getElem _ _ (by omega)] at h2
      rw [List.getD_eq_getElem _ _ hn]
      omega
  have hdisjCard : ∀ n ≤ pairs.length,
      ((List.range n).map fun i => (pairs.getD i (∅, ∅)).1.card).sum =
      ((Finset.range n).biUnion fun i => (pairs.getD i (∅, ∅)).1).card := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        ih (Nat.le_of_succ_le hn), Finset.range_add_one, Finset.biUnion_insert,
        Finset.card_union_of_disjoint, Nat.add_comm]
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      rw [Finset.mem_range] at hj
      rw [List.getD_eq_getElem _ _ hn, List.getD_eq_getElem _ _ (by omega)]
      exact validTerminalPairs_fst_disjoint hv hn (by omega) (by omega)
  have hbiSub : (Finset.range pairs.length).biUnion (fun i => (pairs.getD i (∅, ∅)).1) ⊆ X := by
    intro u hu
    rw [Finset.mem_biUnion] at hu
    rcases hu with ⟨i, hi, hui⟩
    rw [Finset.mem_range] at hi
    rw [List.getD_eq_getElem _ _ hi] at hui
    exact (hv.1 _ (List.getElem_mem hi)).1 hui
  calc Ms.flatten.length = (Ms.map List.length).sum := List.length_flatten
    _ = ((Ms.take pairs.length).map List.length).sum := by rw [← hlen, List.take_length]
    _ ≤ ((List.range pairs.length).map fun i => (pairs.getD i (∅, ∅)).1.card).sum := hsum _ le_rfl
    _ = ((Finset.range pairs.length).biUnion fun i => (pairs.getD i (∅, ∅)).1).card := hdisjCard _ le_rfl
    _ ≤ X.card := Finset.card_le_card hbiSub

/-- Every edge `e ∈ Ms.flatten` belongs to a unique `A_i`, and filtering `Ms.flatten` by
`e.1 ∈ A_i` recovers `Ms[i].length`. -/
theorem matched_filter_length {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b z : ℕ}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hv : ValidTerminalPairs X pairs)
    (hSpec : RouteMatchedSpec G X pairs Δ L b z Ms emb)
    {i : ℕ} (hi : i < pairs.length) :
    (Ms.flatten.filter fun e => decide (e.1 ∈ (pairs[i]'hi).1)).length = (Ms.getD i []).length := by
  have hlen : Ms.length = pairs.length := hSpec.1
  have hgen : ∀ n ≤ pairs.length,
      ((Ms.take n).flatten.filter fun e => decide (e.1 ∈ (pairs[i]'hi).1)).length =
      if i < n then (Ms.getD i []).length else 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.take_succ_eq_append_getElem (by omega), List.flatten_append, List.flatten_singleton,
        List.filter_append, List.length_append, ih (Nat.le_of_succ_le hn)]
      have hmn := hSpec.2.1 n hn
      rw [List.getD_eq_getElem _ _ (by omega)] at hmn
      by_cases hni : n = i
      · subst hni
        have hfilt : (Ms[n]'(by omega)).filter (fun e => decide (e.1 ∈ (pairs[n]'hi).1)) =
            Ms[n]'(by omega) :=
          List.filter_eq_self.mpr fun e he => decide_eq_true (hmn.1 e he).1
        rw [hfilt, List.getD_eq_getElem _ _ (by omega)]
        simp
      · have hfilt : (Ms[n]'(by omega)).filter (fun e => decide (e.1 ∈ (pairs[i]'hi).1)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro e he
          simp only [decide_eq_true_eq]
          intro hmem
          have hdisj := validTerminalPairs_fst_disjoint hv hn hi hni
          exact Finset.disjoint_left.mp hdisj (hmn.1 e he).1 hmem
        rw [hfilt, List.length_nil, Nat.add_zero]
        have hiff : i < n + 1 ↔ i < n := by omega
        simp [hiff]
  have h := hgen pairs.length le_rfl
  rw [← hlen, List.take_length, hlen] at h
  simpa [hi] using h

/-- Sum of `|A_i|` over `pairs` is bounded by `(pairsWords pairs).length`. -/
lemma pairs_fst_sum_le_pLen (pairs : List (Finset ℕ × Finset ℕ)) :
    (pairs.map fun p => p.1.card).sum ≤ (pairsWords pairs).length := by
  have h2 : (pairs.map fun p => p.1.card).sum ≤ ((pairsSections pairs).map List.length).sum := by
    induction pairs with
    | nil => simp [pairsSections]
    | cons p rest ih =>
      have hsec : pairsSections (p :: rest) = [finsetWords p.1, finsetWords p.2] ++ pairsSections rest := by
        simp [pairsSections]
      have hl1 : (finsetWords p.1).length = p.1.card := Finset.length_sort _
      rw [hsec]
      simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append,
        List.map_nil, List.sum_nil, hl1]
      omega
  have h1 := pairsWords_length_eq pairs
  omega

/-! ## 3. Verification of `bridgeCountPrefixStmt` -/

/-- Verification of `bridgeCountPrefixStmt`: marks `owner[u] = i + 1` for `u ∈ A_i` and counts
`cnt[i] = (Ms.getD i []).length` for all `i < pairs.length`, preserving memory `< vInner` and
`ZeroFrom (vInner + G.n + pairs.length)`. -/
theorem bridgeCountPrefix_runs {w pTable outAddr vInner : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    {G : Graph} {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {Δ L b z : ℕ} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hr8 : st.regs 8 = pairs.length)
    (hr11 : st.regs 11 = pTable)
    (hr12 : st.regs 12 = outAddr)
    (hr14 : st.regs 14 = vInner)
    (hr15 : st.regs 15 = G.n)
    (hXsub : X ⊆ Finset.range G.n)
    (hValid : ValidTerminalPairs X pairs)
    (hSpec : RouteMatchedSpec G X pairs Δ L b z Ms emb)
    (hPairs : PairsAt st.mem pTable pairs)
    (hPairsB : PairsBounded st.mem pTable pairs outAddr)
    (hOut : RouteOutSortedAt st.mem outAddr (.matched Ms emb))
    (hOutV : outAddr + 2 + 2 * G.n ≤ vInner)
    (hZ : ZeroFrom st.mem vInner)
    (hRoom : vInner + G.n + pairs.length + 16 < 2 ^ w) :
    let owner := vInner
    let cnt := vInner + G.n
    let resBuf := cnt + pairs.length
    ∃ st' c,
      Runs w p ω bridgeCountPrefixStmt st .normal st' c ∧
      (∀ r ≤ 15, st'.regs r = st.regs r) ∧
      st'.regs 16 = Ms.flatten.length ∧
      st'.regs 17 = owner ∧ st'.regs 18 = cnt ∧ st'.regs 19 = resBuf ∧
      (∀ a < vInner, st'.mem a = st.mem a) ∧
      (∀ i < pairs.length, st'.mem (cnt + i) = (Ms.getD i []).length) ∧
      ZeroFrom st'.mem resBuf ∧
      c ≤ 60 * (pairsWords pairs).length + 60 * Ms.flatten.length + 80 := by
  set k := pairs.length
  set total := Ms.flatten.length
  set owner := vInner
  set cnt := vInner + G.n
  set resBuf := cnt + k
  have htot_le_n : total ≤ G.n := by
    have h1 := matched_total_le_cardX hValid hSpec
    have h2 : X.card ≤ G.n := by simpa using Finset.card_le_card hXsub
    omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hcntW : cnt < 2 ^ w := by omega
  have hresW : resBuf < 2 ^ w := by omega
  -- Stage 1: `bridgeMatchInit`
  have hInit : ∃ st1 c1,
      Runs w p ω bridgeMatchInit st .normal st1 c1 ∧
      st1.mem = st.mem ∧
      (∀ r ≤ 15, st1.regs r = st.regs r) ∧
      st1.regs 16 = total ∧ st1.regs 17 = owner ∧ st1.regs 18 = cnt ∧
      st1.regs 19 = resBuf ∧ st1.regs 20 = 0 ∧ c1 ≤ 35 := by
    suffices hS : ∃ o st1 c1,
        Runs w p ω bridgeMatchInit st o st1 c1 ∧
        (o = .normal ∧ st1.mem = st.mem ∧ (∀ r ≤ 15, st1.regs r = st.regs r) ∧
         st1.regs 16 = total ∧ st1.regs 17 = owner ∧ st1.regs 18 = cnt ∧
         st1.regs 19 = resBuf ∧ st1.regs 20 = 0) ∧ 0 + c1 ≤ 35 by
      obtain ⟨_, st1, c1, hr, ⟨rfl, h1⟩, hc⟩ := hS
      exact ⟨st1, c1, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1,
        h1.2.2.2.2.2.1, h1.2.2.2.2.2.2, by omega⟩
    unfold bridgeMatchInit
    refine runs_seq_assign_le (v := total)
      (by simp [Expr.eval, BinOp.eval, hr12, hw1, show outAddr + 1 < 2 ^ w by omega, hOut.2.1, total]) ?_
    refine runs_seq_assign_le (v := owner) (by simp [Expr.eval, hr14, owner]) ?_
    refine runs_seq_assign_le (v := cnt)
      (by simp [Expr.eval, hr14, hr15, owner, cnt, show vInner + G.n < 2 ^ w by omega]) ?_
    refine runs_seq_assign_le (v := resBuf)
      (by simp [Expr.eval, BinOp.eval, hr8, resBuf, hresW]) ?_
    refine runs_assign_le (v := 0) (by simp [Expr.eval]) ?_ (by simp [Expr.size])
    refine ⟨rfl, rfl, fun r hr => ?_, by simp, by simp, by simp, by simp, by simp⟩
    simp [Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 19),
      Function.update_of_ne (by omega : r ≠ 18), Function.update_of_ne (by omega : r ≠ 17),
      Function.update_of_ne (by omega : r ≠ 16)]
  rcases hInit with ⟨st1, c1, hrun1, hmem1, hr1lo, hr1_16, hr1_17, hr1_18, hr1_19, hr1_20, hc1⟩
  -- Stage 2: `bridgeMarkOwnerLoop`
  have hMark : ∀ rem i (s : State),
      (hi : i + rem = k) →
      (∀ r ≤ 15, s.regs r = st.regs r) →
      s.regs 16 = total → s.regs 17 = owner → s.regs 18 = cnt →
      s.regs 19 = resBuf → s.regs 20 = i →
      (∀ a < owner, s.mem a = st.mem a) →
      (∀ j (hj : j < i), ∀ u ∈ (pairs[j]'(by omega)).1, s.mem (owner + u) = j + 1) →
      ZeroFrom s.mem cnt →
      ∃ st2 c2,
        Runs w p ω bridgeMarkOwnerLoop s .normal st2 c2 ∧
        (∀ r ≤ 15, st2.regs r = st.regs r) ∧
        st2.regs 16 = total ∧ st2.regs 17 = owner ∧ st2.regs 18 = cnt ∧ st2.regs 19 = resBuf ∧
        (∀ a < owner, st2.mem a = st.mem a) ∧
        (∀ j (hj : j < k), ∀ u ∈ (pairs[j]'hj).1, st2.mem (owner + u) = j + 1) ∧
        ZeroFrom st2.mem cnt ∧
        c2 ≤ 40 * rem + 30 * ((pairs.drop i).map fun p => p.1.card).sum + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrlo hr16 hr17 hr18 hr19 hr20 hfr hown hz
      have hieq : i = k := by omega
      subst hieq
      have hcond0 : (Expr.bin .lt (.reg 20) (.reg 8)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, hr20, hrlo 8 (by decide), hr8]
      exact ⟨s, _, runs_loop_zero_oa hcond0, hrlo, hr16, hr17, hr18, hr19, hfr, hown, hz,
        by simp [Expr.size]⟩
    | succ rem ih =>
      intro i s hi hrlo hr16 hr17 hr18 hr19 hr20 hfr hown hz
      have hi_lt : i < k := by omega
      have hcond1 : (Expr.bin .lt (.reg 20) (.reg 8)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, hr20, hrlo 8 (by decide), hr8, hi_lt, hw1]
      have hpi := hPairs.2 i hi_lt
      have hpbi := hPairsB.2 i hi_lt
      rcases hpi.1 with ⟨xs, hnd, hfin, hSeqA⟩
      have hxsLen : xs.length = (pairs[i]'hi_lt).1.card := by
        rw [← hfin, List.toFinset_card_of_nodup hnd]
      set aPtr := st.mem (pTable + 1 + 2 * i)
      have haPtr_eq : s.mem (pTable + 1 + 2 * i) = aPtr :=
        hfr _ (by have := hPairsB.1; omega)
      have haLen_eq : s.mem aPtr = xs.length := by
        rw [hfr aPtr (by omega)]; exact hSeqA.1
      -- Head of outer body
      have hHead : ∃ sH cH,
          Runs w p ω bridgeMarkOwnerHead s .normal sH cH ∧
          sH.mem = s.mem ∧
          (∀ r ≤ 15, sH.regs r = st.regs r) ∧
          sH.regs 16 = total ∧ sH.regs 17 = owner ∧ sH.regs 18 = cnt ∧ sH.regs 19 = resBuf ∧
          sH.regs 20 = i ∧ sH.regs 21 = aPtr ∧ sH.regs 22 = xs.length ∧ sH.regs 23 = 0 ∧
          cH ≤ 20 := by
        suffices hS : ∃ o sH cH,
            Runs w p ω bridgeMarkOwnerHead s o sH cH ∧
            (o = .normal ∧ sH.mem = s.mem ∧ (∀ r ≤ 15, sH.regs r = st.regs r) ∧
             sH.regs 16 = total ∧ sH.regs 17 = owner ∧ sH.regs 18 = cnt ∧ sH.regs 19 = resBuf ∧
             sH.regs 20 = i ∧ sH.regs 21 = aPtr ∧ sH.regs 22 = xs.length ∧ sH.regs 23 = 0) ∧
            0 + cH ≤ 20 by
          obtain ⟨_, sH, cH, hr, ⟨rfl, h1⟩, hc⟩ := hS
          exact ⟨sH, cH, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
            h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2,
            by omega⟩
        unfold bridgeMarkOwnerHead
        have h2iW : i + i < 2 ^ w := by have := hPairsB.1; omega
        have hpt1W : pTable + 1 < 2 ^ w := by have := hPairsB.1; omega
        have hptIdxW : pTable + 1 + (i + i) < 2 ^ w := by have := hPairsB.1; omega
        have haPtr_eq' : s.mem (pTable + 1 + (i + i)) = aPtr := by
          rw [show i + i = 2 * i by omega]; exact haPtr_eq
        refine runs_seq_assign_le (v := aPtr)
          (by simp [Expr.eval, BinOp.eval, hrlo 11 (by decide), hr11, hr20, hw1, hpt1W, h2iW,
            hptIdxW, haPtr_eq']) ?_
        refine runs_seq_assign_le (v := xs.length)
          (by simp [Expr.eval, haLen_eq]) ?_
        refine runs_assign_le (v := 0) (by simp [Expr.eval]) ?_ (by simp [Expr.size])
        refine ⟨rfl, rfl, fun r hr => ?_, by simp [hr16], by simp [hr17], by simp [hr18],
          by simp [hr19], by simp [hr20], by simp, by simp, by simp⟩
        simp [Function.update_of_ne (by omega : r ≠ 23), Function.update_of_ne (by omega : r ≠ 22),
          Function.update_of_ne (by omega : r ≠ 21), hrlo r hr]
      rcases hHead with ⟨sH, cH, hrunH, hmemH, hrHlo, hrH16, hrH17, hrH18, hrH19, hrH20, hrH21,
        hrH22, hrH23, hcH⟩
      -- Inner loop over `t < xs.length`
      have hInner : ∀ r2 t (sI : State),
          (ht : t + r2 = xs.length) →
          (∀ r ≤ 15, sI.regs r = st.regs r) →
          sI.regs 16 = total → sI.regs 17 = owner → sI.regs 18 = cnt → sI.regs 19 = resBuf →
          sI.regs 20 = i → sI.regs 21 = aPtr → sI.regs 22 = xs.length → sI.regs 23 = t →
          (∀ a < owner, sI.mem a = st.mem a) →
          (∀ j (hj : j < i), ∀ u ∈ (pairs[j]'(by omega)).1, sI.mem (owner + u) = j + 1) →
          (∀ idx (hidx : idx < t), sI.mem (owner + xs[idx]'(by omega)) = i + 1) →
          ZeroFrom sI.mem cnt →
          ∃ sE cE,
            Runs w p ω (.loop (.bin .lt (.reg 23) (.reg 22)) bridgeMarkOwnerInner) sI .normal sE cE ∧
            (∀ r ≤ 15, sE.regs r = st.regs r) ∧
            sE.regs 16 = total ∧ sE.regs 17 = owner ∧ sE.regs 18 = cnt ∧ sE.regs 19 = resBuf ∧
            sE.regs 20 = i ∧
            (∀ a < owner, sE.mem a = st.mem a) ∧
            (∀ j (hj : j < i), ∀ u ∈ (pairs[j]'(by omega)).1, sE.mem (owner + u) = j + 1) ∧
            (∀ idx (hidx : idx < xs.length), sE.mem (owner + xs[idx]'hidx) = i + 1) ∧
            ZeroFrom sE.mem cnt ∧
            cE ≤ 30 * r2 + 6 := by
        intro r2
        induction r2 with
        | zero =>
          intro t sI ht hrIlo hrI16 hrI17 hrI18 hrI19 hrI20 hrI21 hrI22 hrI23 hIfr hIown hIcur hIz
          have hteq : t = xs.length := by omega
          subst hteq
          have hc0 : (Expr.bin .lt (.reg 23) (.reg 22)).eval w sI = some 0 := by
            simp [Expr.eval, BinOp.eval, hrI23, hrI22]
          exact ⟨sI, _, runs_loop_zero_oa hc0, hrIlo, hrI16, hrI17, hrI18, hrI19, hrI20,
            hIfr, hIown, hIcur, hIz, by simp [Expr.size]⟩
        | succ r2 ih2 =>
          intro t sI ht hrIlo hrI16 hrI17 hrI18 hrI19 hrI20 hrI21 hrI22 hrI23 hIfr hIown hIcur hIz
          have ht_lt : t < xs.length := by omega
          have hc1' : (Expr.bin .lt (.reg 23) (.reg 22)).eval w sI = some 1 := by
            simp [Expr.eval, BinOp.eval, hrI23, hrI22, ht_lt, hw1]
          set u := xs[t]'ht_lt
          have hu_in_Ai : u ∈ (pairs[i]'hi_lt).1 := by
            rw [← hfin, List.mem_toFinset]; exact List.getElem_mem ht_lt
          have hu_lt_n : u < G.n := by
            have := Finset.mem_range.mp (hXsub ((hValid.1 _ (List.getElem_mem hi_lt)).1 hu_in_Ai))
            exact this
          have hmemU : sI.mem (aPtr + 1 + t) = u := by
            rw [hIfr _ (by omega)]; exact hSeqA.2 t ht_lt
          have hStepI : ∃ sI1 cI1,
              Runs w p ω bridgeMarkOwnerInner sI .normal sI1 cI1 ∧
              (∀ r ≤ 15, sI1.regs r = st.regs r) ∧
              sI1.regs 16 = total ∧ sI1.regs 17 = owner ∧ sI1.regs 18 = cnt ∧ sI1.regs 19 = resBuf ∧
              sI1.regs 20 = i ∧ sI1.regs 21 = aPtr ∧ sI1.regs 22 = xs.length ∧ sI1.regs 23 = t + 1 ∧
              (∀ a < owner, sI1.mem a = st.mem a) ∧
              (∀ j (hj : j < i), ∀ v ∈ (pairs[j]'(by omega)).1, sI1.mem (owner + v) = j + 1) ∧
              (∀ idx (hidx : idx < t + 1), sI1.mem (owner + xs[idx]'(by omega)) = i + 1) ∧
              ZeroFrom sI1.mem cnt ∧
              cI1 ≤ 24 := by
            suffices hS : ∃ o sI1 cI1,
                Runs w p ω bridgeMarkOwnerInner sI o sI1 cI1 ∧
                (o = .normal ∧ (∀ r ≤ 15, sI1.regs r = st.regs r) ∧
                 sI1.regs 16 = total ∧ sI1.regs 17 = owner ∧ sI1.regs 18 = cnt ∧ sI1.regs 19 = resBuf ∧
                 sI1.regs 20 = i ∧ sI1.regs 21 = aPtr ∧ sI1.regs 22 = xs.length ∧ sI1.regs 23 = t + 1 ∧
                 (∀ a < owner, sI1.mem a = st.mem a) ∧
                 (∀ j (hj : j < i), ∀ v ∈ (pairs[j]'(by omega)).1, sI1.mem (owner + v) = j + 1) ∧
                 (∀ idx (hidx : idx < t + 1), sI1.mem (owner + xs[idx]'(by omega)) = i + 1) ∧
                 ZeroFrom sI1.mem cnt) ∧ 0 + cI1 ≤ 24 by
              obtain ⟨_, sI1, cI1, hr, ⟨rfl, h1⟩, hc⟩ := hS
              exact ⟨sI1, cI1, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
                h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2.1,
                h1.2.2.2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2.2.2.2.2,
                by omega⟩
            unfold bridgeMarkOwnerInner
            refine runs_seq_assign_le (v := u)
              (by simp [Expr.eval, BinOp.eval, hrI21, hrI23, hw1, show aPtr + 1 < 2 ^ w by omega,
                show aPtr + 1 + t < 2 ^ w by omega, hmemU]) ?_
            refine runs_seq_store_le (x := owner + u) (v := i + 1)
              (by simp [Expr.eval, BinOp.eval, hrI17, show owner + u < 2 ^ w by omega])
              (by simp [Expr.eval, BinOp.eval, hrI20, hw1, show i + 1 < 2 ^ w by omega]) ?_
            refine runs_assign_le (v := t + 1)
              (by simp [Expr.eval, BinOp.eval, hrI23, hw1, show t + 1 < 2 ^ w by omega]) ?_
              (by simp [Expr.size])
            refine ⟨rfl, fun r hr => ?_, by simp [hrI16], by simp [hrI17], by simp [hrI18],
              by simp [hrI19], by simp [hrI20], by simp [hrI21], by simp [hrI22], by simp,
              ?_, ?_, ?_, ?_⟩
            · simp [Function.update_of_ne (by omega : r ≠ 23),
                Function.update_of_ne (by omega : r ≠ 24), hrIlo r hr]
            · intro a ha; dsimp only; rw [Function.update_of_ne (by omega)]; exact hIfr a ha
            · intro j hj v hv
              dsimp only
              have hne : v ≠ u := by
                intro heq; subst heq
                exact Finset.disjoint_left.mp
                  (validTerminalPairs_fst_disjoint hValid (by omega) hi_lt (by omega)) hv hu_in_Ai
              rw [Function.update_of_ne (by omega)]
              exact hIown j hj v hv
            · intro idx hidx
              dsimp only
              by_cases hid : idx = t
              · subst hid; rw [Function.update_self]
              · by_cases heq : xs[idx]'(by omega) = u
                · rw [heq, Function.update_self]
                · rw [Function.update_of_ne (by omega)]; exact hIcur idx (by omega)
            · intro a ha; dsimp only; rw [Function.update_of_ne (by omega)]; exact hIz a ha
          rcases hStepI with ⟨sI1, cI1, hrunI1, hrI1lo, hrI1_16, hrI1_17, hrI1_18, hrI1_19, hrI1_20,
            hrI1_21, hrI1_22, hrI1_23, hI1fr, hI1own, hI1cur, hI1z, hcI1⟩
          obtain ⟨sE, cE, hrunE, hrElo, hrE16, hrE17, hrE18, hrE19, hrE20, hEfr, hEown, hEcur,
            hEz, hcE⟩ :=
            ih2 (t + 1) sI1 (by omega) hrI1lo hrI1_16 hrI1_17 hrI1_18 hrI1_19 hrI1_20 hrI1_21
              hrI1_22 hrI1_23 hI1fr hI1own hI1cur hI1z
          exact ⟨sE, _, runs_loop_step_oa hc1' (by decide) hrunI1 hrunE, hrElo, hrE16, hrE17,
            hrE18, hrE19, hrE20, hEfr, hEown, hEcur, hEz, by simp only [Expr.size]; omega⟩
      obtain ⟨sE, cE, hrunE, hrElo, hrE16, hrE17, hrE18, hrE19, hrE20, hEfr, hEown, hEcur,
        hEz, hcE⟩ :=
        hInner xs.length 0 sH (by omega) hrHlo hrH16 hrH17 hrH18 hrH19 hrH20 hrH21 hrH22 hrH23
          (by rw [hmemH]; exact hfr) (by rw [hmemH]; exact hown)
          (fun _ h => absurd h (Nat.not_lt_zero _)) (by rw [hmemH]; exact hz)
      -- Increment `r20 := i + 1`
      have hInc : Runs w p ω (.assign 20 (.bin .add (.reg 20) (.const 1))) sE .normal
          { sE with regs := Function.update sE.regs 20 (i + 1) } 4 := by
        refine runs_assign_iff.mpr ⟨i + 1, ?_, rfl, rfl, by simp [Expr.size]⟩
        simp [Expr.eval, BinOp.eval, hrE20, hw1, show i + 1 < 2 ^ w by omega]
      have hBodyRun : Runs w p ω bridgeMarkOwnerBody s .normal
          { sE with regs := Function.update sE.regs 20 (i + 1) } (cH + (cE + 4 + 1) + 1) := by
        unfold bridgeMarkOwnerBody
        exact runs_seq_iff.mpr (Or.inr ⟨sH, cH, cE + 4 + 1, hrunH,
          runs_seq_iff.mpr (Or.inr ⟨sE, cE, 4, hrunE, hInc, rfl⟩), rfl⟩)
      have hOwnNext : ∀ j (hj : j < i + 1), ∀ u ∈ (pairs[j]'(by omega)).1,
          sE.mem (owner + u) = j + 1 := by
        intro j hj u hu
        by_cases hji : j = i
        · subst hji
          rw [← hfin, List.mem_toFinset] at hu
          obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hu
          exact hEcur idx hidx
        · exact hEown j (by omega) u hu
      obtain ⟨st2, c2, hrun2, hr2lo, hr2_16, hr2_17, hr2_18, hr2_19, h2fr, h2own, h2z, hc2⟩ :=
        ih (i + 1) { sE with regs := Function.update sE.regs 20 (i + 1) } (by omega)
          (fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 20), hrElo r hr])
          (by simp [hrE16]) (by simp [hrE17]) (by simp [hrE18]) (by simp [hrE19]) (by simp)
          hEfr hOwnNext hEz
      have hdrop : ((pairs.drop i).map fun p => p.1.card).sum =
          (pairs[i]'hi_lt).1.card + ((pairs.drop (i + 1)).map fun p => p.1.card).sum := by
        rw [List.drop_eq_getElem_cons hi_lt, List.map_cons, List.sum_cons]
      refine ⟨st2, _, runs_loop_step_oa hcond1 (by decide) hBodyRun hrun2, hr2lo, hr2_16, hr2_17,
        hr2_18, hr2_19, h2fr, h2own, h2z, ?_⟩
      simp only [Expr.size]; omega
  obtain ⟨st2, c2, hrun2, hr2lo, hr2_16, hr2_17, hr2_18, hr2_19, h2fr, h2own, h2z, hc2⟩ :=
    hMark k 0 st1 (by omega) hr1lo hr1_16 hr1_17 hr1_18 hr1_19 hr1_20
      (by rw [hmem1]; exact fun _ _ => rfl) (fun _ h => absurd h (Nat.not_lt_zero _))
      (fun a ha => by rw [hmem1]; exact hZ a (by omega))
  -- Stage 3: `bridgeCountStmt`
  have hCountInit : Runs w p ω (.assign 20 (.const 0)) st2 .normal
      { st2 with regs := Function.update st2.regs 20 0 } 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have hCountLoop : ∀ rem j (s : State),
      (hj : j + rem = total) →
      (∀ r ≤ 15, s.regs r = st.regs r) →
      s.regs 16 = total → s.regs 17 = owner → s.regs 18 = cnt → s.regs 19 = resBuf →
      s.regs 20 = j →
      (∀ a < cnt, s.mem a = st2.mem a) →
      (∀ i (hi : i < k), s.mem (cnt + i) =
        ((Ms.flatten.take j).filter fun e => decide (e.1 ∈ (pairs[i]'hi).1)).length) →
      ZeroFrom s.mem resBuf →
      ∃ st3 c3,
        Runs w p ω (.loop (.bin .lt (.reg 20) (.reg 16)) bridgeCountBody) s .normal st3 c3 ∧
        (∀ r ≤ 15, st3.regs r = st.regs r) ∧
        st3.regs 16 = total ∧ st3.regs 17 = owner ∧ st3.regs 18 = cnt ∧ st3.regs 19 = resBuf ∧
        (∀ a < cnt, st3.mem a = st2.mem a) ∧
        (∀ i (hi : i < k), st3.mem (cnt + i) = (Ms.getD i []).length) ∧
        ZeroFrom st3.mem resBuf ∧
        c3 ≤ 55 * rem + 10 := by
    intro rem
    induction rem with
    | zero =>
      intro j s hj hrlo hr16 hr17 hr18 hr19 hr20 hfr hcnt hz
      have hjeq : j = total := by omega
      subst hjeq
      have hc0 : (Expr.bin .lt (.reg 20) (.reg 16)).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, hr20, hr16]
      refine ⟨s, _, runs_loop_zero_oa hc0, hrlo, hr16, hr17, hr18, hr19, hfr, ?_, hz,
        by simp [Expr.size]⟩
      intro i hi
      rw [hcnt i hi, List.take_length]
      exact matched_filter_length hValid hSpec hi
    | succ rem ih =>
      intro j s hj hrlo hr16 hr17 hr18 hr19 hr20 hfr hcnt hz
      have hj_lt : j < total := by omega
      have hc1' : (Expr.bin .lt (.reg 20) (.reg 16)).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, hr20, hr16, hj_lt, hw1]
      set e := Ms.flatten[j]'hj_lt
      -- Find the unique `idx < k` such that `e.1 ∈ (pairs[idx]).1`
      have hFindIdx : ∃ idx, ∃ (hidx : idx < k), e.1 ∈ (pairs[idx]'hidx).1 := by
        have hmem : e ∈ Ms.flatten := List.getElem_mem hj_lt
        rw [List.mem_flatten] at hmem
        rcases hmem with ⟨M, hM, heM⟩
        obtain ⟨idx, hidxM, rfl⟩ := List.getElem_of_mem hM
        have hidx : idx < k := by dsimp only [k]; rw [← hSpec.1]; exact hidxM
        have hmi := hSpec.2.1 idx hidx
        rw [List.getD_eq_getElem _ _ hidxM] at hmi
        exact ⟨idx, hidx, (hmi.1 e heM).1⟩
      rcases hFindIdx with ⟨idx, hidx, he1_in⟩
      have he1_lt_n : e.1 < G.n :=
        Finset.mem_range.mp (hXsub ((hValid.1 _ (List.getElem_mem hidx)).1 he1_in))
      have hmemE1 : s.mem (outAddr + 2 + 2 * j) = e.1 := by
        rw [hfr _ (by omega), h2fr _ (by omega)]
        exact (hOut.2.2 j hj_lt).1
      have hmemOwn : s.mem (owner + e.1) = idx + 1 := by
        rw [hfr _ (by omega)]
        exact h2own idx hidx e.1 he1_in
      set curCnt := ((Ms.flatten.take j).filter fun x => decide (x.1 ∈ (pairs[idx]'hidx).1)).length
      have hcurCnt_le : curCnt ≤ j := by
        calc curCnt ≤ (Ms.flatten.take j).length := List.length_filter_le _ _
          _ ≤ j := List.length_take_le _ _
      have hStepC : ∃ s1 cC,
          Runs w p ω bridgeCountBody s .normal s1 cC ∧
          (∀ r ≤ 15, s1.regs r = st.regs r) ∧
          s1.regs 16 = total ∧ s1.regs 17 = owner ∧ s1.regs 18 = cnt ∧ s1.regs 19 = resBuf ∧
          s1.regs 20 = j + 1 ∧
          (∀ a < cnt, s1.mem a = st2.mem a) ∧
          (∀ i (hi : i < k), s1.mem (cnt + i) =
            ((Ms.flatten.take (j + 1)).filter fun x => decide (x.1 ∈ (pairs[i]'hi).1)).length) ∧
          ZeroFrom s1.mem resBuf ∧
          cC ≤ 48 := by
        suffices hS : ∃ o s1 cC,
            Runs w p ω bridgeCountBody s o s1 cC ∧
            (o = .normal ∧ (∀ r ≤ 15, s1.regs r = st.regs r) ∧
             s1.regs 16 = total ∧ s1.regs 17 = owner ∧ s1.regs 18 = cnt ∧ s1.regs 19 = resBuf ∧
             s1.regs 20 = j + 1 ∧
             (∀ a < cnt, s1.mem a = st2.mem a) ∧
             (∀ i (hi : i < k), s1.mem (cnt + i) =
               ((Ms.flatten.take (j + 1)).filter fun x => decide (x.1 ∈ (pairs[i]'hi).1)).length) ∧
             ZeroFrom s1.mem resBuf) ∧ 0 + cC ≤ 48 by
          obtain ⟨_, s1, cC, hr, ⟨rfl, h1⟩, hc⟩ := hS
          exact ⟨s1, cC, hr, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1,
            h1.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.1, h1.2.2.2.2.2.2.2.2, by omega⟩
        unfold bridgeCountBody
        have hmemE1' : s.mem (outAddr + 2 + (j + j)) = e.1 := by
          rw [show j + j = 2 * j by omega]; exact hmemE1
        refine runs_seq_assign_le (v := e.1)
          (by simp [Expr.eval, BinOp.eval, hrlo 12 (by decide), hr12, hr20, hw2,
            show outAddr + 2 < 2 ^ w by omega, show j + j < 2 ^ w by omega,
            show outAddr + 2 + (j + j) < 2 ^ w by omega, hmemE1']) ?_
        refine runs_seq_assign_le (v := idx)
          (by simp [Expr.eval, BinOp.eval, hr17, hw1, show owner + e.1 < 2 ^ w by omega,
            hmemOwn, show idx < 2 ^ w by omega]) ?_
        refine runs_seq_assign_le (v := curCnt)
          (by simp [Expr.eval, BinOp.eval, hr18, show cnt + idx < 2 ^ w by omega,
            hcnt idx hidx, curCnt]) ?_
        refine runs_seq_store_le (x := cnt + idx) (v := curCnt + 1)
          (by simp [Expr.eval, BinOp.eval, hr18, show cnt + idx < 2 ^ w by omega])
          (by simp [Expr.eval, BinOp.eval, hw1, show curCnt + 1 < 2 ^ w by omega]) ?_
        refine runs_assign_le (v := j + 1)
          (by simp [Expr.eval, BinOp.eval, hr20, hw1, show j + 1 < 2 ^ w by omega]) ?_
          (by simp [Expr.size])
        refine ⟨rfl, fun r hr => ?_, by simp [hr16], by simp [hr17], by simp [hr18],
          by simp [hr19], by simp, ?_, ?_, ?_⟩
        · simp [Function.update_of_ne (by omega : r ≠ 20), Function.update_of_ne (by omega : r ≠ 23),
            Function.update_of_ne (by omega : r ≠ 22), Function.update_of_ne (by omega : r ≠ 21),
            hrlo r hr]
        · intro a ha; dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha
        · intro i hi
          dsimp only
          rw [List.take_succ_eq_append_getElem hj_lt, List.filter_append, List.length_append,
            List.filter_cons, List.filter_nil]
          by_cases hii : i = idx
          · subst hii
            rw [Function.update_self, decide_eq_true he1_in]
            simp [curCnt]
          · have hnot : e.1 ∉ (pairs[i]'hi).1 := fun hmem =>
              Finset.disjoint_left.mp (validTerminalPairs_fst_disjoint hValid hidx hi (Ne.symm hii))
                he1_in hmem
            rw [Function.update_of_ne (by omega), decide_eq_false hnot, hcnt i hi]
            simp
        · intro a ha; dsimp only; rw [Function.update_of_ne (by omega)]; exact hz a ha
      rcases hStepC with ⟨s1, cC, hrunC, hr1'lo, hr1'_16, hr1'_17, hr1'_18, hr1'_19, hr1'_20,
        h1'fr, h1'cnt, h1'z, hcC⟩
      obtain ⟨st3, c3, hrun3, hr3lo, hr3_16, hr3_17, hr3_18, hr3_19, h3fr, h3cnt, h3z, hc3⟩ :=
        ih (j + 1) s1 (by omega) hr1'lo hr1'_16 hr1'_17 hr1'_18 hr1'_19 hr1'_20 h1'fr h1'cnt h1'z
      exact ⟨st3, _, runs_loop_step_oa hc1' (by decide) hrunC hrun3, hr3lo, hr3_16, hr3_17,
        hr3_18, hr3_19, h3fr, h3cnt, h3z, by simp only [Expr.size]; omega⟩
  obtain ⟨st3, c3, hrun3, hr3lo, hr3_16, hr3_17, hr3_18, hr3_19, h3fr, h3cnt, h3z, hc3⟩ :=
    hCountLoop total 0 { st2 with regs := Function.update st2.regs 20 0 } (by omega)
      (fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 20), hr2lo r hr])
      (by simp [hr2_16]) (by simp [hr2_17]) (by simp [hr2_18]) (by simp [hr2_19]) (by simp)
      (fun _ _ => rfl) (fun i _ => by simp [h2z (cnt + i) (by omega)])
      (fun a ha => h2z a (by omega))
  -- Combine all 3 stages
  have hFull : Runs w p ω bridgeCountPrefixStmt st .normal st3 (c1 + (c2 + (2 + c3 + 1) + 1) + 1) := by
    unfold bridgeCountPrefixStmt bridgeCountStmt
    exact runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2 + (2 + c3 + 1) + 1, hrun1,
      runs_seq_iff.mpr (Or.inr ⟨st2, c2, 2 + c3 + 1, hrun2,
        runs_seq_iff.mpr (Or.inr ⟨_, 2, c3, hCountInit, hrun3, rfl⟩), rfl⟩), rfl⟩)
  have hfst := pairs_fst_sum_le_pLen pairs
  have hk_le_pLen : 2 * k + 1 ≤ (pairsWords pairs).length := by
    have := pairsWords_length_eq pairs; omega
  refine ⟨st3, _, hFull, hr3lo, hr3_16, hr3_17, hr3_18, hr3_19,
    fun a ha => (h3fr a (by omega)).trans (h2fr a ha), h3cnt, h3z, ?_⟩
  simp only [List.drop_zero] at hc2
  omega

end MinCostFlow.HierPaths
