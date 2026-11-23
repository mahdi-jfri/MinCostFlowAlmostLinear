module

public import MinCostFlow.DynSpanner.Program.DynSpannerWalkHelpers
public import MinCostFlow.DynSpanner.Program.StateLayout
import WordRAM.Tactic

/-!
# The deletions of `U_H` from one bucket

At the end of a step with `0 < j`, an edge of `H` stays in `H` when it is in a level below `j` or
in `J̃`. The edges whose smallest level is at least `j` are in the buckets `hBuckets i` with
`j ≤ i` (`DynSpannerStateAt`), so the deletions of `U_H` are the bucket edges of these levels
that are not in `J̃`. The procedure `dsDelRecordsStmt` handles one bucket. It follows the linked
list (`IsDoublyLinkedList`, whose head word holds the first edge plus one and whose next words
hold the following edge plus one) for the given number of steps. It reads a presence array of a
set `X` (for `J̃`, the presence array of its `DynGraphAt` block) and writes the record `[1, e]`
(`UpdateAt` of `DynGraphLayout.lean`) for each edge `e` of the list outside `X`.
`delRecs_batchBodyAt` turns the records into a `BatchBodyAt`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## The program -/

/-- One element of the list: `r6` holds the element plus one. -/
def dsDelRecordsBodyStmt : Stmt :=
  .assign 8 (.bin .sub (.reg 6) (.const 1)) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.reg 8))) ;;
  .cond (.load (.bin .add (.reg 3) (.reg 8))) .nop
    (.store (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 5))) (.const 1) ;;
     .store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 5))) (.const 1)) (.reg 8) ;;
     .assign 5 (.bin .add (.reg 5) (.const 1)))

/-- `args = [nextBase, headWord, len, presPtr, out]`; returns the number of records. -/
def dsDelRecordsStmt : Stmt :=
  .assign 5 (.const 0) ;;
  .assign 6 (.reg 1) ;;
  forRange 7 (.const 0) (.reg 2) dsDelRecordsBodyStmt ;;
  .ret (.reg 5)

def delRecordsProcs : List Stmt := [dsDelRecordsStmt]

def delRecordsIdx : ℕ := 0

lemma delRecordsProcs_noRand : ∀ s ∈ delRecordsProcs, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## The records -/

/-- The elements of `L` outside `X`. -/
def delList (X : Finset ℕ) (L : List ℕ) : List ℕ := L.filter fun e => decide (e ∉ X)

/-- The words of the deletion records. -/
def delWords (X : Finset ℕ) (L : List ℕ) : List ℕ := (delList X L).flatMap fun e => [1, e]

lemma delList_succ (X : Finset ℕ) (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    delList X (L.take (k + 1)) = delList X (L.take k) ++ if L[k] ∈ X then [] else [L[k]] := by
  simp only [delList, List.take_succ_eq_append_getElem hk, List.filter_append]
  split_ifs with h <;> simp [h]

lemma delWords_succ (X : Finset ℕ) (L : List ℕ) (k : ℕ) (hk : k < L.length) :
    delWords X (L.take (k + 1)) = delWords X (L.take k) ++ if L[k] ∈ X then [] else [1, L[k]] := by
  simp only [delWords, delList_succ X L k hk, List.flatMap_append]
  split_ifs <;> simp

lemma delWords_length (X : Finset ℕ) (L : List ℕ) :
    (delWords X L).length = 2 * (delList X L).length := by
  simp only [delWords]
  induction delList X L with
  | nil => simp
  | cons a t ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]; omega

lemma delList_length_le (X : Finset ℕ) (L : List ℕ) : (delList X L).length ≤ L.length :=
  List.length_filter_le _ _

lemma mem_delList (X : Finset ℕ) (L : List ℕ) (e : ℕ) : e ∈ delList X L ↔ e ∈ L ∧ e ∉ X := by
  simp [delList]

/-- The records form a batch of deletions. -/
lemma delRecs_batchBodyAt {mem : ℕ → ℕ} (H : MGraph) (X : Finset ℕ) :
    ∀ (L : List ℕ) (a : ℕ), ListAt mem a (delWords X L) →
      BatchBodyAt mem a H ((delList X L).map Update.delete) (2 * (delList X L).length)
  | [], _, _ => by simp [delList, BatchBodyAt]
  | e :: L, a, h => by
    by_cases he : e ∈ X
    · have h' : delWords X (e :: L) = delWords X L := by simp [delWords, delList, he]
      have hl : delList X (e :: L) = delList X L := by simp [delList, he]
      rw [hl]
      exact delRecs_batchBodyAt _ X L a (h' ▸ h)
    · have h' : delWords X (e :: L) = [1, e] ++ delWords X L := by simp [delWords, delList, he]
      have hl : delList X (e :: L) = e :: delList X L := by simp [delList, he]
      rw [h'] at h
      obtain ⟨h1, h2⟩ := listAt_append.mp h
      rw [hl, List.map_cons, List.length_cons]
      refine ⟨2, by omega, ⟨rfl, h1⟩, ?_⟩
      rw [show 2 * ((delList X L).length + 1) - 2 = 2 * (delList X L).length by omega]
      exact delRecs_batchBodyAt _ X L (a + 2) (by simpa using h2)

/-! ## The contract -/

/-- The data and the precondition of `dsDelRecordsStmt`. -/
structure DLCtx where
  w : ℕ
  eCap : ℕ
  X : Finset ℕ
  L : List ℕ
  prevBase : ℕ
  nextBase : ℕ
  headAddr : ℕ
  pres : ℕ
  out : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hnB : nextBase + eCap < 2 ^ w
  hpB : pres + eCap < 2 ^ w
  hoB : out + 2 * L.length < 2 ^ w
  dON : IvlDisj out (2 * L.length) nextBase eCap
  dOP : IvlDisj out (2 * L.length) pres eCap
  hL : IsDoublyLinkedList mem0 prevBase nextBase headAddr eCap L
  hpres : ∀ e < eCap, mem0 (pres + e) = if e ∈ X then 1 else 0

/-- Contract of `dsDelRecordsStmt`. -/
def dsDelRecordsContract (c : DLCtx) : Contract where
  pre args mem := args = [c.nextBase, c.mem0 c.headAddr, c.L.length, c.pres, c.out] ∧ mem = c.mem0
  post _ mem ret mem' :=
    ret = (delList c.X c.L).length ∧ ListAt mem' c.out (delWords c.X c.L) ∧
    ∀ addr, (addr < c.out ∨ c.out + 2 * c.L.length ≤ addr) → mem' addr = mem addr
  cost _ _ := 60 * c.L.length + 20

/-- The loop invariant after the first `k` elements. -/
def DLInv (c : DLCtx) (k : ℕ) (st : State) : Prop :=
  st.regs 0 = c.nextBase ∧ st.regs 2 = c.L.length ∧ st.regs 3 = c.pres ∧ st.regs 4 = c.out ∧
  st.regs 5 = (delList c.X (c.L.take k)).length ∧
  (∀ hk : k < c.L.length, st.regs 6 = c.L[k] + 1) ∧ st.regs 7 = k ∧
  ListAt st.mem c.out (delWords c.X (c.L.take k)) ∧
  ∀ addr, (addr < c.out ∨ c.out + 2 * c.L.length ≤ addr) → st.mem addr = c.mem0 addr

end

private lemma head_word {mem : ℕ → ℕ} {a : ℕ} {L : List ℕ}
    (h : mem a = (match L with | [] => 0 | x :: _ => x + 1)) (hk : 0 < L.length) :
    mem a = L[0] + 1 := by
  cases L with
  | nil => simp at hk
  | cons x t => simpa using h

public section

/-- One iteration of the loop of `dsDelRecordsStmt`. -/
theorem dsDelRecords_step_triple (c : DLCtx) {p : Program} {k : ℕ} (hk : k < c.L.length) :
    Triple c.w p (DLInv c k) dsDelRecordsBodyStmt
      (normalPost fun st₁ =>
        DLInv c (k + 1) { st₁ with regs := Function.update st₁.regs 7 (k + 1) } ∧
          st₁.regs 7 = k)
      (fun _ => 50) := by
  intro st ω hI
  obtain ⟨r0, r2, r3, r4, r5, r6, r7, hW, hfr⟩ := hI
  have hw16 := c.hw16
  have hnB := c.hnB
  have hpB := c.hpB
  have hoB := c.hoB
  obtain ⟨_, hcap, _, hlinks⟩ := c.hL
  set e := c.L[k] with he
  have heC : e < c.eCap := hcap e (List.getElem_mem hk)
  have hcnt : (delList c.X (c.L.take k)).length ≤ k := by
    have := delList_length_le c.X (c.L.take k)
    simp only [List.length_take] at this
    omega
  have hnext_rd : st.mem (c.nextBase + e) =
      if k + 1 = c.L.length then 0 else c.L.getD (k + 1) 0 + 1 :=
    (hfr _ (c.dON.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))).trans
      (hlinks k hk).2
  have hp_rd : st.mem (c.pres + e) = if e ∈ c.X then 1 else 0 :=
    (hfr _ (c.dOP.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))).trans
      (c.hpres e heC)
  have hnext_ok : ∀ hk1 : k + 1 < c.L.length,
      (if k + 1 = c.L.length then 0 else c.L.getD (k + 1) 0 + 1) = c.L[k + 1] + 1 := by
    intro hk1
    have hne : ¬ (k + 1 = c.L.length) := by omega
    simp only [hne, ite_false, List.getD_eq_getElem _ _ hk1]
  have hWs := delWords_succ c.X c.L k hk
  have hls := delList_succ c.X c.L k hk
  rw [← he] at hWs hls
  dsimp only [dsDelRecordsBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e)
    (Expr.eval_eq_of_eq (Expr.eval_sub (Expr.eval_reg_of_eq (r6 hk)) (Expr.eval_const (by omega))
      (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := st.mem (c.nextBase + e))
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0]))
      (Expr.eval_reg_of_eq (by simp)) (by omega)) rfl) ?_
  refine runs_cond_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3]))
    (Expr.eval_reg_of_eq (by simp)) (by omega)) hp_rd) (fun hne => ?_) (fun hz => ?_)
  · -- `e ∈ X`: nothing to write.
    have hX : e ∈ c.X := by by_contra h; simp [h] at hne
    simp only [hX, ite_true, List.append_nil] at hWs hls
    refine runs_nop_le ⟨⟨by simp [r0], by simp [r2], by simp [r3], by simp [r4],
      by simp [r5, hls], fun hk1 => ?_, by simp, by rw [hWs]; exact hW, hfr⟩, by simp [r7]⟩
      (by simp [Expr.size])
    simp only [Function.update_of_ne (show (6 : ℕ) ≠ 7 by omega), Function.update_self]
    rw [hnext_rd, hnext_ok hk1]
  · -- `e ∉ X`: write the record.
    have hX : e ∉ c.X := by intro h; simp [h] at hz
    simp only [hX, ite_false] at hWs hls
    set n := (delList c.X (c.L.take k)).length with hn
    have hWlen := delWords_length c.X (c.L.take k)
    rw [← hn] at hWlen
    refine runs_seq_store_le (x := c.out + 2 * n) (v := 1)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r5]))
          (by omega)) (by omega)) (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (x := c.out + 2 * n + 1) (v := e)
      (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r5]))
          (by omega)) (by omega)) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_assign_le (v := n + 1)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5])) (Expr.eval_const (by omega))
        (by omega)) ⟨⟨by simp [r0], by simp [r2], by simp [r3], by simp [r4],
          by simp [hls]; exact hn, fun hk1 => ?_, by simp, ?_, fun addr h => ?_⟩, by simp [r7]⟩
          (by simp [Expr.size])
    · simp only [Function.update_of_ne (show (6 : ℕ) ≠ 7 by omega),
        Function.update_of_ne (show (6 : ℕ) ≠ 5 by omega), Function.update_self]
      rw [hnext_rd, hnext_ok hk1]
    · rw [hWs]
      refine listAt_append.mpr ⟨?_, ?_⟩
      · exact ((hW.update_ge (by omega)).update_ge (by omega))
      · intro j hj
        simp only [List.length_cons, List.length_nil] at hj
        rw [hWlen]
        show Function.update (Function.update st.mem _ _) _ _ _ = _
        interval_cases j
        · rw [Function.update_of_ne (by omega)]; simp
        · simp [show c.out + 2 * n + 1 = c.out + (2 * n + 1) by omega]
    · show Function.update (Function.update st.mem _ _) _ _ _ = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr addr h

/-- `dsDelRecordsStmt` meets `dsDelRecordsContract`. -/
theorem dsDelRecords_meetsContract (c : DLCtx) {p : Program} {bR : ℕ}
    (hpR : p.HasAt bR delRecordsProcs) :
    MeetsContract c.w p (bR + delRecordsIdx) (dsDelRecordsContract c) := by
  refine meetsContract_of_runs
    (hpR.get (i := delRecordsIdx) (by simp [delRecordsProcs, delRecordsIdx])) ?_
  rintro args mem pos ω hwords ⟨rfl, hmem⟩
  subst hmem
  simp only [delRecordsProcs, delRecordsIdx, List.getElem_cons_zero]
  dsimp only [dsDelRecordsStmt]
  have hw16 := c.hw16
  have hoB := c.hoB
  have hloop := Triple.forRange_const (w := c.w) (p := p)
    (P := fun st' => DLInv c 0 { st' with regs := Function.update st'.regs 7 0 })
    (r := 7) (lo := .const 0) (hi := .reg 2) (body := dsDelRecordsBodyStmt)
    (Inv := DLInv c) 50 0 c.L.length (Nat.zero_le _) (by omega)
    (fun _ => by omega) (fun st' h => ⟨Expr.eval_const (by omega), h⟩)
    (fun k st' _ _ h => h.2.2.2.2.2.2.1) (fun k st' _ _ h => Expr.eval_reg_of_eq h.2.1)
    (fun k _ hk => dsDelRecords_step_triple c hk)
  have hhead : ∀ hk : 0 < c.L.length, c.mem0 c.headAddr = c.L[0] + 1 :=
    fun hk => head_word c.hL.2.2.1 hk
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (v := c.mem0 c.headAddr) (Expr.eval_reg_of_eq (by simp [startState]))
    ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · exact ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp [delList], fun hk => by simp [hhead hk], by simp,
      fun j hj => by simp [delWords, delList] at hj, fun _ _ => rfl⟩
  · intro st hI
    obtain ⟨_, _, _, _, q5, _, _, hW, hfr⟩ := hI
    rw [List.take_of_length_le (Nat.le_refl _)] at q5 hW
    refine runs_ret_le (v := (delList c.X c.L).length) (Expr.eval_reg_of_eq q5)
      ⟨rfl, hW, hfr⟩ ?_
    simp only [Expr.size, dsDelRecordsContract]
    omega

end

end MinCostFlow.DynSpanner.Program
