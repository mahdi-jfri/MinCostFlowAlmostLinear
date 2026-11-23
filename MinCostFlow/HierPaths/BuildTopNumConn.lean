module

public import MinCostFlow.HierPaths.BuildTopScheduleGeometry
public import MinCostFlow.HierPaths.InitProg
import MinCostFlow.HierPaths.InitBlockLen

import Mathlib.Tactic.Ring

/-!
# Closed-form connector count and its procedure

In a valid hierarchy, every sibling pair `c < c'` of a parent at depth `t`
holds a perfect matching of size `groupSize x b (t + 1)`. Summing over all
parents and sibling pairs at depth `t < leafDepth x b` yields
`(2 ^ (x - 1)) * (branching x b t - 1)` connectors per depth, so
`S.numConn` depends only on `x` and `b` and is computed in `O(leafDepth x b)`
steps by `buildTopNumConn`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM
open scoped BigOperators

/-- Closed-form number of connectors in a valid `(x, b)` hierarchy. -/
def buildTopNumConnVal (x b : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (leafDepth x b), 2 ^ (x - 1) * (branching x b t - 1)

private lemma sum_lt_pairs_const (k s : ℕ) :
    ((List.range k).flatMap fun i => (List.range k).flatMap fun j =>
      if i < j then List.replicate s 0 else []).length =
    k * (k - 1) / 2 * s := by
  have h1 : ∀ i, ((List.range k).flatMap fun j =>
      if i < j then List.replicate s 0 else []).length = (k - 1 - i) * s := by
    intro i
    rw [List.length_flatMap]
    have : ∀ n, ((List.range n).map fun j =>
        (if i < j then List.replicate s 0 else []).length).sum = (n - 1 - i) * s := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_singleton, List.sum_singleton]
        split_ifs with h
        · simp only [List.length_replicate]
          have : n - i = (n - 1 - i) + 1 := by omega
          rw [show n + 1 - 1 - i = n - i by omega, this, Nat.add_mul, Nat.one_mul]
        · simp only [List.length_nil, Nat.add_zero]
          rw [show n + 1 - 1 - i = 0 by omega, show n - 1 - i = 0 by omega]
    exact this k
  rw [List.length_flatMap]
  simp only [h1]
  have hsum : ∀ n, ((List.range n).map fun i => (n - 1 - i) * s).sum = n * (n - 1) / 2 * s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hshift : ((List.range (n + 1)).map fun i => (n - i) * s).sum =
          n * s + ((List.range n).map fun i => (n - 1 - i) * s).sum := by
        rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, Nat.sub_zero, List.map_map]
        congr 1
        congr 1
        apply List.map_congr_left
        intro i _
        dsimp only [Function.comp]
        congr 1
        omega
      simp only [Nat.add_sub_cancel]
      rw [hshift, ih]
      have heven : 2 ∣ n * (n - 1) := by
        rcases Nat.even_or_odd n with ⟨r, rfl⟩ | ⟨r, rfl⟩
        · exact ⟨r * (2 * r - 1), by ring⟩
        · exact ⟨(2 * r + 1) * r, by simp only [Nat.add_sub_cancel]; ring⟩
      have hsucc : (n + 1) * n / 2 = n + n * (n - 1) / 2 := by
        rcases heven with ⟨q, hq⟩
        have hq2 : (n + 1) * n = 2 * (n + q) := by
          cases n with
          | zero => simp at hq; simp [hq]
          | succ m =>
            simp only [Nat.add_sub_cancel] at hq
            nlinarith
        rw [hq2, hq, Nat.mul_div_cancel_left _ (by decide), Nat.mul_div_cancel_left _ (by decide)]
      rw [hsucc, Nat.add_mul]
  exact hsum k

private lemma length_conn_of_perfect {H : HierData} {x b t g c c' : ℕ}
    (hV : H.IsValid x b) (ht : 1 < groupSize x b t) (hg : g < numGroups x b t)
    (hc : c ∈ childGroups x b t g) (hc' : c' ∈ childGroups x b t g) (hlt : c < c') :
    (H.conn t c c').length = groupSize x b (t + 1) := by
  have hp := hV.conn_perfect t g ht hg c hc c' hc' hlt
  have h1 : ((H.conn t c c').map Prod.fst).toFinset.card = (H.conn t c c').length := by
    rw [List.toFinset_card_of_nodup hp.1, List.length_map]
  rw [← h1, hp.2.1, card_members]

private lemma list_sum_map_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_singleton,
      List.sum_singleton, Finset.sum_range_succ]

/-- For every valid `(x, b)` hierarchy with `0 < x` and `0 < b`,
`(connRecs H x b).length` equals `buildTopNumConnVal x b`. -/
theorem length_connRecs_eq {H : HierData} {x b : ℕ} (hx : 0 < x) (hb : 0 < b)
    (hV : H.IsValid x b) :
    (connRecs H x b).length = buildTopNumConnVal x b := by
  unfold connRecs buildTopNumConnVal
  rw [List.length_flatMap, list_sum_map_range]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' : t < leafDepth x b := Finset.mem_range.mp ht
  have hgs1 : 1 < groupSize x b t := one_lt_groupSize_of_lt_leafDepth hb ht'
  rw [List.length_flatMap]
  have hg_len : ∀ g ∈ List.range (numGroups x b t),
      ((childList x b t g).flatMap fun c => (childList x b t g).flatMap fun c' =>
        pairRecs H x b t g c c').length =
      branching x b t * (branching x b t - 1) / 2 * groupSize x b (t + 1) := by
    intro g hg
    have hg' : g < numGroups x b t := List.mem_range.mp hg
    set k := branching x b t
    set s := groupSize x b (t + 1)
    have hcl : childList x b t g = (List.range k).map (fun i => g * k + i) := by
      unfold childList
      apply List.ext_getElem
      · simp [k]
      · intro i hi _
        simp [k]
    rw [hcl, List.flatMap_map]
    have hinner : ∀ i ∈ List.range k,
        (((List.range k).map (fun j => g * k + j)).flatMap fun c' =>
          pairRecs H x b t g (g * k + i) c').length =
        ((List.range k).flatMap fun j => if i < j then List.replicate s 0 else []).length := by
      intro i hi
      have hi' : i < k := List.mem_range.mp hi
      rw [List.flatMap_map, List.length_flatMap, List.length_flatMap]
      congr 1
      apply List.map_congr_left
      intro j hj
      have hj' : j < k := List.mem_range.mp hj
      unfold pairRecs
      have hci : g * k + i ∈ childGroups x b t g := by
        simp [childGroups, Nat.succ_mul, k]; omega
      have hcj : g * k + j ∈ childGroups x b t g := by
        simp [childGroups, Nat.succ_mul, k]; omega
      split_ifs with h1 h2
      · rw [List.length_map, List.length_replicate]
        exact length_conn_of_perfect hV hgs1 hg' hci hcj h1
      · omega
      · omega
      · rfl
    rw [List.length_flatMap]
    have hmap : ((List.range k).map fun i =>
        (((List.range k).map fun j => g * k + j).flatMap fun c' =>
          pairRecs H x b t g (g * k + i) c').length) =
        ((List.range k).map fun i =>
          ((List.range k).flatMap fun j => if i < j then List.replicate s 0 else []).length) :=
      List.map_congr_left hinner
    rw [hmap, ← List.length_flatMap]
    exact sum_lt_pairs_const k s
  have hmap_g : ((List.range (numGroups x b t)).map fun g =>
      ((childList x b t g).flatMap fun c => (childList x b t g).flatMap fun c' =>
        pairRecs H x b t g c c').length) =
      List.replicate (numGroups x b t)
        (branching x b t * (branching x b t - 1) / 2 * groupSize x b (t + 1)) := by
    apply List.ext_getElem
    · simp
    · intro i hi _
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      exact hg_len i (List.mem_range.mpr (by simpa using hi))
  rw [hmap_g, List.sum_replicate, smul_eq_mul]
  -- Simplify `numGroups * (k * (k - 1) / 2 * s) = 2^(x - 1) * (k - 1)`
  have h2k : 2 ∣ branching x b t := by
    have htb_le : t * b ≤ (t + 1) * b := Nat.mul_le_mul_right b (Nat.le_succ t)
    have hbr : branching x b t = 2 ^ (min x ((t + 1) * b) - min x (t * b)) := by
      unfold branching groupSize
      have hle : x - min x ((t + 1) * b) ≤ x - min x (t * b) := by omega
      rw [Nat.pow_div hle (by decide)]
      congr 1
      omega
    have htb_lt : t * b < x := by
      by_contra hge
      have : groupSize x b t = 1 := by
        unfold groupSize; rw [Nat.min_eq_left (by omega), Nat.sub_self, pow_zero]
      omega
    have hpos_diff : 1 ≤ min x ((t + 1) * b) - min x (t * b) := by
      have : (t + 1) * b = t * b + b := by ring
      omega
    rw [hbr]
    cases h : min x ((t + 1) * b) - min x (t * b) with
    | zero => omega
    | succ d => rw [pow_succ]; exact dvd_mul_left 2 _
  rcases h2k with ⟨q, hq⟩
  have hdiv : branching x b t * (branching x b t - 1) / 2 = q * (branching x b t - 1) := by
    rw [hq, show 2 * q * (2 * q - 1) = 2 * (q * (2 * q - 1)) by ring,
      Nat.mul_div_cancel_left _ (by decide)]
  have h2x : 2 * 2 ^ (x - 1) = 2 ^ x := by
    conv_rhs => rw [show x = (x - 1) + 1 by omega, pow_succ, Nat.mul_comm]
  have htot : numGroups x b t * (q * groupSize x b (t + 1)) = 2 ^ (x - 1) := by
    have h1 : 2 * (numGroups x b t * (q * groupSize x b (t + 1))) = 2 * 2 ^ (x - 1) := by
      calc 2 * (numGroups x b t * (q * groupSize x b (t + 1)))
          = numGroups x b t * (branching x b t * groupSize x b (t + 1)) := by rw [hq]; ring
        _ = numGroups x b t * groupSize x b t := by rw [← groupSize_eq_mul_branching]
        _ = 2 ^ x := numGroups_mul_groupSize
        _ = 2 * 2 ^ (x - 1) := h2x.symm
    omega
  rw [hdiv]
  calc numGroups x b t * (q * (branching x b t - 1) * groupSize x b (t + 1))
      = (numGroups x b t * (q * groupSize x b (t + 1))) * (branching x b t - 1) := by ring
    _ = 2 ^ (x - 1) * (branching x b t - 1) := by rw [htot]

/-- Upper bound on `buildTopNumConnVal x b`: at most `leafDepth x b * 2 ^ x * 2 ^ b`. -/
theorem buildTopNumConnVal_le (x b : ℕ) :
    buildTopNumConnVal x b ≤ leafDepth x b * 2 ^ x * 2 ^ b := by
  unfold buildTopNumConnVal
  calc ∑ t ∈ Finset.range (leafDepth x b), 2 ^ (x - 1) * (branching x b t - 1)
      ≤ ∑ _t ∈ Finset.range (leafDepth x b), 2 ^ x * 2 ^ b := by
        apply Finset.sum_le_sum
        intro t _
        exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (Nat.sub_le x 1))
          ((Nat.sub_le _ _).trans (branching_le_pow t))
    _ = leafDepth x b * (2 ^ x * 2 ^ b) := by simp [Finset.sum_const, smul_eq_mul]
    _ = leafDepth x b * 2 ^ x * 2 ^ b := by ring

/-- Procedure computing `buildTopNumConnVal x b` from `[x, b, leafDepth x b]`. -/
def buildTopNumConn : Stmt :=
  .assign 3 (.bin .shiftLeft (.const 1) (.bin .sub (.reg 0) (.const 1))) ;;
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 2) (
    .assign 6 (buildTopBranchingExpr (.reg 0) (.reg 1) (.reg 5)) ;;
    .assign 4 (.bin .add (.reg 4) (.bin .mul (.reg 3) (.bin .sub (.reg 6) (.const 1))))
  ) ;;
  .ret (.reg 4)

theorem buildTopNumConn_noRand : buildTopNumConn.NoRand := by
  simp [buildTopNumConn, forRange, forUp, Stmt.NoRand]

def buildTopNumConnContract (w x b : ℕ) : Contract where
  pre args _ := args = [x, b, leafDepth x b] ∧ 0 < x ∧ 0 < b ∧ b ≤ x ∧
    2 ^ x < 2 ^ w ∧ leafDepth x b * 2 ^ x * 2 ^ b < 2 ^ w
  post _ mem v mem' := v = buildTopNumConnVal x b ∧ mem' = mem
  cost _ _ := 70 * leafDepth x b + 40

theorem buildTopNumConn_meetsContract {w f x b : ℕ} {p : Program}
    (hp : p.procs[f]? = some buildTopNumConn) :
    MeetsContract w p f (buildTopNumConnContract w x b) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨rfl, hx, hb, hbx, h2x, htot⟩ := hpre
  set D := leafDepth x b
  have h1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.two_pow_pos x) h2x
  have hxW : x < 2 ^ w := x.lt_two_pow_self.trans h2x
  have hfits := buildTopScheduleWords_fit hb hbx h2x
  have hhalf_lt : 2 ^ (x - 1) < 2 ^ w :=
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le x 1)).trans_lt h2x
  have hD_lt : D < 2 ^ w := by
    have h1' : 1 ≤ 2 ^ x * 2 ^ b := Nat.mul_pos (Nat.two_pow_pos x) (Nat.two_pow_pos b)
    have h2' : D ≤ D * (2 ^ x * 2 ^ b) := Nat.le_mul_of_pos_right D h1'
    have h3' : D * (2 ^ x * 2 ^ b) = D * 2 ^ x * 2 ^ b := by ring
    omega
  refine runs_start_le ?_
  unfold buildTopNumConn
  refine runs_seq_assign_le (v := 2 ^ (x - 1)) ?_ ?_
  · have hsub : (Expr.bin .sub (.reg 0) (.const 1)).eval w (startState [x, b, D] mem pos) = some (x - 1) :=
      Expr.eval_sub (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) hxW
    simpa [Nat.shiftLeft_eq] using
      Expr.eval_shiftLeft (Expr.eval_const h1) hsub (by simpa [Nat.shiftLeft_eq] using hhalf_lt)
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (Nat.two_pow_pos w)) ?_
  let partialSum : ℕ → ℕ := fun k => ∑ t ∈ Finset.range k, 2 ^ (x - 1) * (branching x b t - 1)
  have hpart_le : ∀ k ≤ D, partialSum k ≤ D * 2 ^ x * 2 ^ b := fun k hk =>
    (Finset.sum_le_sum_of_subset (Finset.range_mono hk)).trans (buildTopNumConnVal_le x b)
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 0 = x ∧ st.regs 1 = b ∧ st.regs 2 = D ∧ st.regs 3 = 2 ^ (x - 1) ∧
    st.regs 4 = partialSum j ∧ st.regs 5 = j ∧ st.mem = mem
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (body := .assign 6 (buildTopBranchingExpr (.reg 0) (.reg 1) (.reg 5)) ;;
      .assign 4 (.bin .add (.reg 4) (.bin .mul (.reg 3) (.bin .sub (.reg 6) (.const 1)))))
    (P := fun st => st.regs 0 = x ∧ st.regs 1 = b ∧ st.regs 2 = D ∧
      st.regs 3 = 2 ^ (x - 1) ∧ st.regs 4 = 0 ∧ st.mem = mem)
    (Inv := Inv) 55 0 D (Nat.zero_le D) h1 (fun _ => hD_lt)
    (fun st ⟨r0, r1, r2, r3, r4, hm⟩ => ⟨Expr.eval_const (Nat.two_pow_pos w),
      by simp [Inv, Function.update_of_ne, r0, r1, r2, r3, r4, hm, partialSum]⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.1)
    (fun j _ hj => by
      intro st ω ⟨r0, r1, r2, r3, r4, r5, hm⟩
      obtain ⟨hj1, hmul⟩ := hfits.2 j hj
      have hbr_eval := eval_buildTopBranchingExpr (Expr.eval_reg_of_eq r0)
        (Expr.eval_reg_of_eq r1) (Expr.eval_reg_of_eq r5) h2x hj1 hmul
      have hbr_lt : branching x b j < 2 ^ w :=
        ((branching_le_pow j).trans (Nat.pow_le_pow_right (by decide) hbx)).trans_lt h2x
      have hnext_le : partialSum (j + 1) < 2 ^ w :=
        (hpart_le (j + 1) hj).trans_lt htot
      have hterm_eq : partialSum (j + 1) = partialSum j + 2 ^ (x - 1) * (branching x b j - 1) := by
        simp [partialSum, Finset.sum_range_succ]
      have hterm_lt : 2 ^ (x - 1) * (branching x b j - 1) < 2 ^ w := by omega
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := branching x b j) hbr_eval ?_
      refine runs_assign_le (v := partialSum (j + 1))
        (Expr.eval_eq_of_eq
          (Expr.eval_add
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), r4]))
            (Expr.eval_mul
              (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), r3]))
              (Expr.eval_sub (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const h1) hbr_lt)
              hterm_lt)
            (hterm_eq ▸ hnext_le))
          hterm_eq.symm) ?_ ?_
      · refine ⟨⟨?_, ?_, ?_, ?_, by simp, ?_, hm⟩, ?_⟩
        · simp [Function.update_of_ne, r0]
        · simp [Function.update_of_ne, r1]
        · simp [Function.update_of_ne, r2]
        · simp [Function.update_of_ne, r3]
        · simp [r5]
        · simp [Function.update_of_ne, r5]
      · simp [buildTopBranchingExpr, queryGroupSizeExpr, Expr.size])
  refine runs_seq_triple_le hloop ?_ ?_
  · simp [startState]
  intro st₁ ⟨_, _, _, _, r4, _, hm⟩
  refine runs_ret_le (v := buildTopNumConnVal x b) (Expr.eval_reg_of_eq r4) ⟨rfl, hm⟩ ?_
  simp [buildTopNumConnContract, Expr.size]
  omega

end MinCostFlow.HierPaths

end
