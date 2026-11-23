module

public import MinCostFlow.DynSpanner.Program.DynSpannerDelRecords
import WordRAM.Tactic

/-!
# The deletions of `U_H` from the buckets of levels `lo ≤ i < hi`

`dsDelAllStmt` calls `dsDelRecordsStmt` for each bucket `B i` with `lo ≤ i < hi` and appends the
records. The output is the record list of the concatenation `bucketsCat B lo (hi - lo)` of the
buckets (`dsDelAll_meetsContract`). In a step with `0 < j` the levels are `j ≤ i ≤ L`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- The loop body: process bucket `r7` and add its number of records to `r8`. -/
def dsDelAllBodyStmt (bR : ℕ) : Stmt :=
  .call 9 (bR + delRecordsIdx) [.reg 0, .load (.bin .add (.reg 1) (.reg 7)),
    .load (.bin .add (.reg 2) (.reg 7)), .reg 5,
    .bin .add (.reg 6) (.bin .mul (.const 2) (.reg 8))] ;;
  .assign 8 (.bin .add (.reg 8) (.reg 9))

/-- `args = [nextBase, headBase, lenBase, lo, hi, presPtr, out]`; returns the number of
records. -/
def dsDelAllStmt (bR : ℕ) : Stmt :=
  .assign 8 (.const 0) ;;
  forRange 7 (.reg 3) (.reg 4) (dsDelAllBodyStmt bR) ;;
  .ret (.reg 8)

def delAllProcs (bR : ℕ) : List Stmt := [dsDelAllStmt bR]

def delAllIdx : ℕ := 0

lemma delAllProcs_noRand (bR : ℕ) : ∀ s ∈ delAllProcs bR, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The buckets `B lo, …, B (lo + k - 1)` one after the other. -/
def bucketsCat (B : ℕ → List ℕ) (lo k : ℕ) : List ℕ := (List.range' lo k).flatMap B

lemma bucketsCat_succ (B : ℕ → List ℕ) (lo k : ℕ) :
    bucketsCat B lo (k + 1) = bucketsCat B lo k ++ B (lo + k) := by
  simp [bucketsCat, List.range'_concat, List.flatMap_append]

lemma delList_append (X : Finset ℕ) (L₁ L₂ : List ℕ) :
    delList X (L₁ ++ L₂) = delList X L₁ ++ delList X L₂ := by
  simp [delList, List.filter_append]

lemma delWords_append (X : Finset ℕ) (L₁ L₂ : List ℕ) :
    delWords X (L₁ ++ L₂) = delWords X L₁ ++ delWords X L₂ := by
  simp [delWords, delList_append, List.flatMap_append]

/-- The data and the precondition of `dsDelAllStmt`. -/
structure DACtx where
  w : ℕ
  eCap : ℕ
  X : Finset ℕ
  B : ℕ → List ℕ
  lo : ℕ
  hi : ℕ
  prevBase : ℕ
  nextBase : ℕ
  headBase : ℕ
  lenBase : ℕ
  pres : ℕ
  out : ℕ
  mem0 : ℕ → ℕ
  hle : lo ≤ hi
  hw16 : 16 ≤ 2 ^ w
  hnB : nextBase + eCap < 2 ^ w
  hpB : pres + eCap < 2 ^ w
  hhB : headBase + hi < 2 ^ w
  hlB : lenBase + hi < 2 ^ w
  hoB : out + 2 * (bucketsCat B lo (hi - lo)).length < 2 ^ w
  dOR : IvlDisj out (2 * (bucketsCat B lo (hi - lo)).length) prevBase eCap
  dON : IvlDisj out (2 * (bucketsCat B lo (hi - lo)).length) nextBase eCap
  dOP : IvlDisj out (2 * (bucketsCat B lo (hi - lo)).length) pres eCap
  dOH : IvlDisj out (2 * (bucketsCat B lo (hi - lo)).length) (headBase + lo) (hi - lo)
  dOL : IvlDisj out (2 * (bucketsCat B lo (hi - lo)).length) (lenBase + lo) (hi - lo)
  hB : ∀ i, lo ≤ i → i < hi →
    IsDoublyLinkedList mem0 prevBase nextBase (headBase + i) eCap (B i) ∧
    mem0 (lenBase + i) = (B i).length
  hpres : ∀ e < eCap, mem0 (pres + e) = if e ∈ X then 1 else 0

/-- Contract of `dsDelAllStmt`. -/
def dsDelAllContract (c : DACtx) : Contract where
  pre args mem :=
    args = [c.nextBase, c.headBase, c.lenBase, c.lo, c.hi, c.pres, c.out] ∧ mem = c.mem0
  post _ mem ret mem' :=
    ret = (delList c.X (bucketsCat c.B c.lo (c.hi - c.lo))).length ∧
    ListAt mem' c.out (delWords c.X (bucketsCat c.B c.lo (c.hi - c.lo))) ∧
    ∀ addr, (addr < c.out ∨ c.out + 2 * (bucketsCat c.B c.lo (c.hi - c.lo)).length ≤ addr) →
      mem' addr = mem addr
  cost _ _ := 60 * (bucketsCat c.B c.lo (c.hi - c.lo)).length + 60 * (c.hi - c.lo) + 20

/-- The loop invariant after the buckets `lo ≤ i' < i`. -/
def DAInv (c : DACtx) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = c.nextBase ∧ st.regs 1 = c.headBase ∧ st.regs 2 = c.lenBase ∧
  st.regs 4 = c.hi ∧ st.regs 5 = c.pres ∧ st.regs 6 = c.out ∧ st.regs 7 = i ∧
  st.regs 8 = (delList c.X (bucketsCat c.B c.lo (i - c.lo))).length ∧
  ListAt st.mem c.out (delWords c.X (bucketsCat c.B c.lo (i - c.lo))) ∧
  ∀ addr, (addr < c.out ∨ c.out + 2 * (bucketsCat c.B c.lo (c.hi - c.lo)).length ≤ addr) →
    st.mem addr = c.mem0 addr

end

private lemma bucketsCat_mono (B : ℕ → List ℕ) (lo : ℕ) {k k' : ℕ} (h : k ≤ k') :
    (bucketsCat B lo k).length + 0 ≤ (bucketsCat B lo k').length := by
  induction k' with
  | zero => simp at h; subst h; simp
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with h' | h'
    · have := ih (by omega)
      rw [bucketsCat_succ, List.length_append]; omega
    · rw [show k = k' + 1 by omega]; simp

private lemma head_word_le {mem : ℕ → ℕ} {pb nb a cap : ℕ} {L : List ℕ}
    (h : IsDoublyLinkedList mem pb nb a cap L) : mem a ≤ cap := by
  obtain ⟨_, hlt, hhd, _⟩ := h
  cases L with
  | nil => simp at hhd; omega
  | cons x t =>
    simp only at hhd
    have := hlt x (List.mem_cons_self ..)
    omega

public section

/-- One iteration of the loop of `dsDelAllStmt`. -/
theorem dsDelAll_step_triple (c : DACtx) {p : Program} {bR : ℕ}
    (hpR : p.HasAt bR delRecordsProcs) {i : ℕ} (hlo : c.lo ≤ i) (hi : i < c.hi) :
    Triple c.w p (DAInv c i) (dsDelAllBodyStmt bR)
      (normalPost fun st₁ =>
        DAInv c (i + 1) { st₁ with regs := Function.update st₁.regs 7 (i + 1) } ∧
          st₁.regs 7 = i)
      (fun _ => 60 * (c.B i).length + 50) := by
  intro st ω hI
  obtain ⟨r0, r1, r2, r4, r5, r6, r7, r8, hW, hfr⟩ := hI
  have hw16 := c.hw16
  have hnB := c.hnB
  have hpB := c.hpB
  have hhB := c.hhB
  have hlB := c.hlB
  have hoB := c.hoB
  have hsucc := bucketsCat_succ c.B c.lo (i - c.lo)
  rw [show c.lo + (i - c.lo) = i by omega] at hsucc
  have hmono := bucketsCat_mono c.B c.lo (show i + 1 - c.lo ≤ c.hi - c.lo by omega)
  rw [show i + 1 - c.lo = i - c.lo + 1 by omega, hsucc, List.length_append] at hmono
  set P := bucketsCat c.B c.lo (i - c.lo) with hP
  set tot := (bucketsCat c.B c.lo (c.hi - c.lo)).length with htot
  have hcnt := delList_length_le c.X P
  have hWlen := delWords_length c.X P
  obtain ⟨hDLL, hlen⟩ := c.hB i hlo hi
  -- The bucket and its words are outside the output area.
  have hout : ∀ addr, (addr < c.out ∨ c.out + 2 * tot ≤ addr) → st.mem addr = c.mem0 addr := hfr
  have hDLL₁ : IsDoublyLinkedList st.mem c.prevBase c.nextBase (c.headBase + i) c.eCap (c.B i) :=
    hDLL.of_agree (hout _ (c.dOH.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega)))
      (fun h hh => hout _ (c.dOR.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega)
        (by have := hDLL.2.1 h hh; omega)))
      (fun h hh => hout _ (c.dON.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega)
        (by have := hDLL.2.1 h hh; omega)))
  have hhead_rd : st.mem (c.headBase + i) = c.mem0 (c.headBase + i) :=
    hout _ (c.dOH.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))
  have hlen_rd : st.mem (c.lenBase + i) = (c.B i).length :=
    (hout _ (c.dOL.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))).trans hlen
  let d : DLCtx := ⟨c.w, c.eCap, c.X, c.B i, c.prevBase, c.nextBase, c.headBase + i, c.pres,
    c.out + 2 * (delList c.X P).length, st.mem, hw16, hnB, hpB, by omega,
    c.dON.sub_left (by omega) (by omega), c.dOP.sub_left (by omega) (by omega), hDLL₁,
    fun e he => (hout _ (c.dOP.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega)
      (by omega))).trans (c.hpres e he)⟩
  dsimp only [dsDelAllBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_call_le (dsDelRecords_meetsContract d hpR) (by eval_expr)
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      have := head_word_le hDLL
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨by simp [d, hhead_rd, hlen_rd], rfl⟩ ?_
  rintro v mem₁ pos₁ ⟨rfl, hW₁, hfr₁⟩
  refine runs_assign_le (v := (delList c.X P).length + (delList c.X (c.B i)).length)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r8])) (Expr.eval_reg_of_eq (by simp [d]))
      (by have := delList_length_le c.X (c.B i); omega))
    ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r4], by simp [r5], by simp [r6], by simp,
      ?_, ?_, fun addr h => ?_⟩, by simp [r7]⟩ ?_
  · simp [show i + 1 - c.lo = i - c.lo + 1 by omega, bucketsCat_succ,
      show c.lo + (i - c.lo) = i by omega, delList_append, hP]
  · rw [show i + 1 - c.lo = i - c.lo + 1 by omega, bucketsCat_succ,
      show c.lo + (i - c.lo) = i by omega, ← hP, delWords_append]
    refine listAt_append.mpr ⟨?_, ?_⟩
    · exact hW.congr fun k hk1 hk2 => hfr₁ _ (Or.inl (by simp only [d]; omega))
    · rw [hWlen]; exact hW₁
  · show mem₁ addr = _
    rw [hfr₁ addr (by simp only [d]; omega)]
    exact hfr addr h
  · simp only [dsDelRecordsContract, d, Expr.size_const, Expr.size_reg, Expr.size_load,
      Expr.size_bin, argsSize_cons, argsSize_nil]
    omega

/-- `dsDelAllStmt` meets `dsDelAllContract`. -/
theorem dsDelAll_meetsContract (c : DACtx) {p : Program} {bA bR : ℕ}
    (hpR : p.HasAt bR delRecordsProcs) (hpA : p.HasAt bA (delAllProcs bR)) :
    MeetsContract c.w p (bA + delAllIdx) (dsDelAllContract c) := by
  refine meetsContract_of_runs
    (hpA.get (i := delAllIdx) (by simp [delAllProcs, delAllIdx])) ?_
  rintro args mem pos ω hwords ⟨rfl, hmem⟩
  subst hmem
  simp only [delAllProcs, delAllIdx, List.getElem_cons_zero]
  dsimp only [dsDelAllStmt]
  have hw16 := c.hw16
  have hhB := c.hhB
  have hle := c.hle
  let stepCost : ℕ → ℕ := fun i => 60 * (c.B i).length + 50
  have hloop := Triple.forRange_le (w := c.w) (p := p)
    (P := fun st' => st'.regs 0 = c.nextBase ∧ st'.regs 1 = c.headBase ∧
      st'.regs 2 = c.lenBase ∧ st'.regs 3 = c.lo ∧ st'.regs 4 = c.hi ∧ st'.regs 5 = c.pres ∧
      st'.regs 6 = c.out ∧ st'.regs 8 = 0 ∧ st'.mem = c.mem0)
    (r := 7) (lo := .reg 3) (hi := .reg 4) (body := dsDelAllBodyStmt bR)
    (Inv := DAInv c) stepCost c.lo c.hi c.hle (by omega) (fun _ => by omega)
    (fun st' h => ⟨Expr.eval_reg_of_eq h.2.2.2.1, by
      obtain ⟨q0, q1, q2, q3, q4, q5, q6, q8, hm⟩ := h
      refine ⟨by simp [q0], by simp [q1], by simp [q2], by simp [q4], by simp [q5], by simp [q6],
        by simp, by simp [q8, bucketsCat, delList], fun j hj => by
          simp [bucketsCat, delWords, delList] at hj, fun _ _ => by simp [hm]⟩⟩)
    (fun k st' _ _ h => h.2.2.2.2.2.2.1) (fun k st' _ _ h => Expr.eval_reg_of_eq h.2.2.2.1)
    (fun k hk1 hk2 => dsDelAll_step_triple c hpR hk1 hk2)
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState], by simp [startState],
    by simp [startState], by simp, rfl⟩ ?_
  intro st hI
  obtain ⟨_, _, _, _, _, _, _, q8, hW, hfr⟩ := hI
  refine runs_ret_le (v := (delList c.X (bucketsCat c.B c.lo (c.hi - c.lo))).length)
    (Expr.eval_reg_of_eq q8) ⟨rfl, hW, hfr⟩ ?_
  have hsum : ∀ k, ((List.range' c.lo k).map stepCost).sum =
      60 * (bucketsCat c.B c.lo k).length + 50 * k := by
    intro k
    induction k with
    | zero => simp [bucketsCat]
    | succ k ih =>
      rw [List.range'_concat, List.map_append, List.sum_append, ih, bucketsCat_succ,
        List.length_append]
      simp only [stepCost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      ring
  have h : rangeCost stepCost c.lo c.hi = 60 * (bucketsCat c.B c.lo (c.hi - c.lo)).length +
      50 * (c.hi - c.lo) := hsum (c.hi - c.lo)
  simp only [Expr.size, dsDelAllContract]
  omega

end

end MinCostFlow.DynSpanner.Program
