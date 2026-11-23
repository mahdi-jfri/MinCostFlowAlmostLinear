module

public import MinCostFlow.DynSpanner.Program.DynSpannerClearBucketsInner
public import MinCostFlow.DynSpanner.Program.DynSpannerPhase
import WordRAM.Tactic

/-!
# Emptying the buckets of the levels `lo ≤ i < hi`: the contract

`dsClearBuckets_outer_triple` proves one iteration of the outer loop of `dsClearBucketsStmt`: it
reads the head word and the length of bucket `i`, runs the inner loop over the bucket
(`dsClearBuckets_inner_triple`), and writes `0` to the head word and the length word.
`dsClearBuckets_meetsContract` proves the contract: afterwards `minH[e] = 0` for every edge of the
buckets, all head and length words of these levels are `0`, and every other cell is unchanged.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

private lemma head_word {mem : ℕ → ℕ} {a : ℕ} {L : List ℕ}
    (h : mem a = (match L with | [] => 0 | x :: _ => x + 1)) (hk : 0 < L.length) :
    mem a = L[0] + 1 := by
  cases L with
  | nil => simp at hk
  | cons x t => simpa using h

@[expose] public section

/-- The invariant of the outer loop before level `i`. -/
def CBOuter (c : CBCtx) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = c.nextBase ∧ st.regs 1 = c.headBase ∧ st.regs 2 = c.degBase ∧
  st.regs 4 = c.hi ∧ st.regs 5 = c.minH ∧ st.regs 6 = i ∧
  CBMem c (bucketsCat c.B c.lo (i - c.lo)) i st.mem

end

public section

/-- One iteration of the outer loop of `dsClearBucketsStmt`. -/
theorem dsClearBuckets_outer_triple (c : CBCtx) {p : Program} {i : ℕ} (hlo : c.lo ≤ i)
    (hi : i < c.hi) :
    Triple c.w p (CBOuter c i) dsClearBucketsOuterStmt
      (normalPost fun st₁ =>
        CBOuter c (i + 1) { st₁ with regs := Function.update st₁.regs 6 (i + 1) } ∧
          st₁.regs 6 = i)
      (fun _ => 40 * (c.B i).length + 50) := by
  intro st ω hI
  obtain ⟨r0, r1, r2, r4, r5, r6, hz, hzh, hfr⟩ := hI
  have hw16 := c.hw16
  have hhB := c.hhB
  have hdB := c.hdB
  obtain ⟨hdll, hlen⟩ := c.hB i hlo hi
  have hcat := c.cat_lt (i := i) (by omega)
  have hmh := c.dMH.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.headBase + i) (by omega)
    (by omega)
  have hmd := c.dMD.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.degBase + i) (by omega)
    (by omega)
  have hhd := c.dHD.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.degBase + i) (by omega)
    (by omega)
  have hhead_rd : st.mem (c.headBase + i) = c.mem0 (c.headBase + i) :=
    hfr _ (fun y hy => by have := hcat y hy; omega) (fun i' h1 h2 => ⟨by omega, by
      have := c.dHD.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.degBase + i') (by omega)
        (by omega)
      omega⟩)
  have hlen_rd : st.mem (c.degBase + i) = (c.B i).length :=
    (hfr _ (fun y hy => by have := hcat y hy; omega) (fun i' h1 h2 => ⟨by
      have := c.dHD.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.degBase + i) (by omega)
        (by omega)
      omega, by omega⟩)).trans hlen
  have hsucc := bucketsCat_succ c.B c.lo (i - c.lo)
  rw [show c.lo + (i - c.lo) = i by omega] at hsucc
  dsimp only [dsClearBucketsOuterStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := c.mem0 (c.headBase + i))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r1) (Expr.eval_reg_of_eq r6)
      (by omega)) hhead_rd) ?_
  refine runs_seq_assign_le (v := (c.B i).length)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2]))
      (Expr.eval_reg_of_eq (by simp [r6])) (by omega)) hlen_rd) ?_
  have hlenC := dll_length_le_cap hdll
  have hnB := c.hnB
  have hloop := Triple.forRange_const (w := c.w) (p := p)
    (P := fun st' => CBInner c i 0 { st' with regs := Function.update st'.regs 9 0 })
    (r := 9) (lo := .const 0) (hi := .reg 8) (body := dsClearBucketsInnerStmt)
    (Inv := CBInner c i) 25 0 (c.B i).length (Nat.zero_le _) (by omega)
    (fun _ => by omega) (fun st' h => ⟨Expr.eval_const (by omega), h⟩)
    (fun k st' _ _ h => h.2.2.2.2.2.2.2.1) (fun k st' _ _ h => Expr.eval_reg_of_eq h.2.2.2.2.2.2.1)
    (fun k _ hk => dsClearBuckets_inner_triple c hlo hi hk)
  refine runs_seq_triple_le hloop ?_ ?_
  · refine ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r4], by simp [r5], by simp [r6],
      by simp, by simp, fun hk => ?_, ?_⟩
    · simp only [Function.update_of_ne (show (7 : ℕ) ≠ 9 by omega),
        Function.update_of_ne (show (7 : ℕ) ≠ 8 by omega), Function.update_self]
      exact head_word hdll.2.2.1 hk
    · simp only [List.take_zero, List.append_nil]
      exact ⟨hz, hzh, hfr⟩
  · intro st₁ hI₁
    obtain ⟨q0, q1, q2, q4, q5, q6, _, _, _, hz₁, hzh₁, hfr₁⟩ := hI₁
    rw [List.take_of_length_le (Nat.le_refl _), ← hsucc] at hz₁ hfr₁
    refine runs_seq_store_le (x := c.headBase + i) (v := 0)
      (Expr.eval_add (Expr.eval_reg_of_eq q1) (Expr.eval_reg_of_eq q6) (by omega))
      (Expr.eval_const (by omega)) ?_
    refine runs_store_le (x := c.degBase + i) (v := 0)
      (Expr.eval_add (Expr.eval_reg_of_eq q2) (Expr.eval_reg_of_eq q6) (by omega))
      (Expr.eval_const (by omega)) ⟨⟨by simp [q0], by simp [q1], by simp [q2], by simp [q4],
        by simp [q5], by simp, ?_⟩, q6⟩ (by simp [Expr.size]; omega)
    rw [show i + 1 - c.lo = i - c.lo + 1 by omega]
    have hcat' : ∀ y ∈ bucketsCat c.B c.lo (i - c.lo + 1), y < c.eCap := by
      rw [show i - c.lo + 1 = i + 1 - c.lo by omega]; exact c.cat_lt (by omega)
    refine ⟨fun y hy => ?_, fun i' h1 h2 => ?_, fun addr h1 h2 => ?_⟩
    · show Function.update (Function.update st₁.mem _ _) _ _ _ = 0
      have := hcat' y hy
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hz₁ y hy
    · show Function.update (Function.update st₁.mem _ _) _ _ _ = 0 ∧
        Function.update (Function.update st₁.mem _ _) _ _ _ = 0
      by_cases hii : i' = i
      · subst hii
        constructor
        · rw [Function.update_of_ne (by omega)]; simp
        · simp
      · have hii' : i' < i := by omega
        obtain ⟨ha, hb⟩ := hzh₁ i' h1 hii'
        have := c.dHD.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.degBase + i') (by omega)
          (by omega)
        have := c.dHD.addr_sub (Nat.le_refl _) (Nat.le_refl _) (c.degBase + i) (by omega)
          (by omega)
        constructor
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact ha
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hb
    · show Function.update (Function.update st₁.mem _ _) _ _ _ = _
      obtain ⟨hA, hB'⟩ := h2 i (by omega) (by omega)
      rw [Function.update_of_ne hB', Function.update_of_ne hA]
      exact hfr₁ addr h1 fun i' h1' h2' => h2 i' h1' (by omega)

/-- `dsClearBucketsStmt` meets `dsClearBucketsContract`. -/
theorem dsClearBuckets_meetsContract (c : CBCtx) {p : Program} {bC : ℕ}
    (hpC : p.HasAt bC clearBucketsProcs) :
    MeetsContract c.w p (bC + clearBucketsIdx) (dsClearBucketsContract c) := by
  refine meetsContract_of_runs
    (hpC.get (i := clearBucketsIdx) (by simp [clearBucketsProcs, clearBucketsIdx])) ?_
  rintro args mem pos ω hwords ⟨rfl, hmem⟩
  subst hmem
  simp only [clearBucketsProcs, clearBucketsIdx, List.getElem_cons_zero]
  dsimp only [dsClearBucketsStmt]
  have hw16 := c.hw16
  have hhB := c.hhB
  have hle := c.hle
  let stepCost : ℕ → ℕ := fun i => 40 * (c.B i).length + 50
  have hloop := Triple.forRange_le (w := c.w) (p := p)
    (P := fun st' => st' = startState [c.nextBase, c.headBase, c.degBase, c.lo, c.hi, c.minH]
      c.mem0 pos)
    (r := 6) (lo := .reg 3) (hi := .reg 4) (body := dsClearBucketsOuterStmt)
    (Inv := CBOuter c) stepCost c.lo c.hi c.hle (by omega) (fun _ => by omega)
    (fun st' h => by
      subst h
      refine ⟨Expr.eval_reg_of_eq (by simp [startState]), by simp [startState],
        by simp [startState], by simp [startState], by simp [startState], by simp [startState],
        by simp, ?_⟩
      refine ⟨fun y hy => by simp [bucketsCat] at hy, fun i' h1 h2 => by omega,
        fun _ _ _ => rfl⟩)
    (fun k st' _ _ h => h.2.2.2.2.2.1) (fun k st' _ _ h => Expr.eval_reg_of_eq h.2.2.2.1)
    (fun k hk1 hk2 => dsClearBuckets_outer_triple c hk1 hk2)
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl ?_
  intro st hI
  obtain ⟨_, _, _, _, _, _, hM⟩ := hI
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) hM ?_
  have hsum : ∀ k, ((List.range' c.lo k).map stepCost).sum =
      40 * (bucketsCat c.B c.lo k).length + 50 * k := by
    intro k
    induction k with
    | zero => simp [bucketsCat]
    | succ k ih =>
      rw [List.range'_concat, List.map_append, List.sum_append, ih, bucketsCat_succ,
        List.length_append]
      simp only [stepCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.one_mul]
      omega
  have h : rangeCost stepCost c.lo c.hi = 40 * (bucketsCat c.B c.lo (c.hi - c.lo)).length +
      50 * (c.hi - c.lo) := hsum (c.hi - c.lo)
  simp only [Expr.size, dsClearBucketsContract]
  omega

end

end MinCostFlow.DynSpanner.Program
