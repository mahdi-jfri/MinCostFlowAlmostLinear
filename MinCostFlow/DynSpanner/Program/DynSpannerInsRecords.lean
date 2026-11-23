module

public import MinCostFlow.DynSpanner.Program.DynSpannerWalkHelpers
public import MinCostFlow.DynSpanner.Program.DynGraphOps
public import MinCostFlow.DynSpanner.Program.StateLayout
import WordRAM.Tactic

/-!
# The insertions of `U_H`

At the end of a step, `H` gets the edges of `J̃` that it does not have yet (the list `uhIns` of
`step`). The procedure `dsInsRecordsStmt` writes these insertions as update records
`[0, e, tail e, head e]` (the layout `UpdateAt` of `DynGraphLayout.lean`). It walks over a list
`es` of edges of the host graph `G` and reads a presence array of a set `X` (for `H`, the presence
array of its `DynGraphAt` block). For each `e ∈ es` outside `X` it reads the ends of `e` in `G`
and writes the record. The records are the batch `insRecs G X es`, which `insRecs_batchBodyAt`
turns into a `BatchBodyAt`. By `diffBatch_perm_props` in `DynSpannerStepHelpers.lean`, the order
of these insertions does not matter, so the program does not sort them.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## The program -/

/-- One edge `e = es[r7]`: write its insertion record if `e` is not in `X`. -/
def dsInsRecordsBodyStmt (bOps : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.reg 7))) ;;
  .cond (.load (.bin .add (.reg 2) (.reg 6))) .nop
    (.call 8 (bOps + dgIdxGetTail) [.reg 3, .reg 6] ;;
     .call 9 (bOps + dgIdxGetHead) [.reg 3, .reg 6] ;;
     .assign 10 (.bin .add (.reg 4) (.bin .mul (.const 4) (.reg 5))) ;;
     .store (.reg 10) (.const 0) ;;
     .store (.bin .add (.reg 10) (.const 1)) (.reg 6) ;;
     .store (.bin .add (.reg 10) (.const 2)) (.reg 8) ;;
     .store (.bin .add (.reg 10) (.const 3)) (.reg 9) ;;
     .assign 5 (.bin .add (.reg 5) (.const 1)))

/-- `args = [esPtr, esLen, presPtr, gPtr, out]`; returns the number of records. -/
def dsInsRecordsStmt (bOps : ℕ) : Stmt :=
  .assign 5 (.const 0) ;;
  forRange 7 (.const 0) (.reg 1) (dsInsRecordsBodyStmt bOps) ;;
  .ret (.reg 5)

def insRecordsProcs (bOps : ℕ) : List Stmt := [dsInsRecordsStmt bOps]

def insRecordsIdx : ℕ := 0

lemma insRecordsProcs_noRand (bOps : ℕ) : ∀ s ∈ insRecordsProcs bOps, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## The records -/

/-- The edges of `es` outside `X`. -/
def insList (X : Finset ℕ) (es : List ℕ) : List ℕ := es.filter fun e => decide (e ∉ X)

/-- The insertions of the edges of `es` outside `X`, with their ends in `G`. -/
def insRecs (G : MGraph) (X : Finset ℕ) (es : List ℕ) : List Update :=
  (insList X es).map fun e => Update.insert e (G.tail e) (G.head e)

/-- The words of the records. -/
def insWords (G : MGraph) (X : Finset ℕ) (es : List ℕ) : List ℕ :=
  (insList X es).flatMap fun e => [0, e, G.tail e, G.head e]

lemma insList_succ (X : Finset ℕ) (es : List ℕ) (i : ℕ) (hi : i < es.length) :
    insList X (es.take (i + 1)) =
      insList X (es.take i) ++ if es[i] ∈ X then [] else [es[i]] := by
  simp only [insList, List.take_succ_eq_append_getElem hi, List.filter_append]
  split_ifs with h <;> simp [h]

lemma insWords_succ (G : MGraph) (X : Finset ℕ) (es : List ℕ) (i : ℕ) (hi : i < es.length) :
    insWords G X (es.take (i + 1)) = insWords G X (es.take i) ++
      if es[i] ∈ X then [] else [0, es[i], G.tail es[i], G.head es[i]] := by
  simp only [insWords, insList_succ X es i hi, List.flatMap_append]
  split_ifs <;> simp

lemma insWords_length (G : MGraph) (X : Finset ℕ) (es : List ℕ) :
    (insWords G X es).length = 4 * (insList X es).length := by
  simp only [insWords]
  induction insList X es with
  | nil => simp
  | cons a t ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]; omega

lemma insList_length_le (X : Finset ℕ) (es : List ℕ) : (insList X es).length ≤ es.length :=
  List.length_filter_le _ _

lemma mem_insList (X : Finset ℕ) (es : List ℕ) (e : ℕ) : e ∈ insList X es ↔ e ∈ es ∧ e ∉ X := by
  simp [insList]

lemma insList_nodup (X : Finset ℕ) {es : List ℕ} (h : es.Nodup) : (insList X es).Nodup :=
  h.filter _

/-- The records form a batch (in any graph, since insertions are encoded without reference to
it). -/
lemma insRecs_batchBodyAt {mem : ℕ → ℕ} (G H : MGraph) (X : Finset ℕ) :
    ∀ (es : List ℕ) (a : ℕ), ListAt mem a (insWords G X es) →
      BatchBodyAt mem a H (insRecs G X es) (4 * (insList X es).length)
  | [], _, _ => by simp [insRecs, insList, BatchBodyAt]
  | e :: es, a, h => by
    by_cases he : e ∈ X
    · have h' : insWords G X (e :: es) = insWords G X es := by
        simp [insWords, insList, he]
      have hr : insRecs G X (e :: es) = insRecs G X es := by simp [insRecs, insList, he]
      have hl : insList X (e :: es) = insList X es := by simp [insList, he]
      rw [hr, hl]
      exact insRecs_batchBodyAt G _ X es a (h' ▸ h)
    · have h' : insWords G X (e :: es) = [0, e, G.tail e, G.head e] ++ insWords G X es := by
        simp [insWords, insList, he]
      have hr : insRecs G X (e :: es) = Update.insert e (G.tail e) (G.head e) :: insRecs G X es :=
        by simp [insRecs, insList, he]
      have hl : (insList X (e :: es)).length = (insList X es).length + 1 := by
        simp [insList, he]
      rw [h'] at h
      obtain ⟨h1, h2⟩ := listAt_append.mp h
      rw [hr, hl]
      refine ⟨4, by omega, ⟨rfl, h1⟩, ?_⟩
      rw [show 4 * ((insList X es).length + 1) - 4 = 4 * (insList X es).length by omega]
      exact insRecs_batchBodyAt G _ X es (a + 4) (by simpa using h2)

/-! ## The contract -/

/-- The data and the precondition of `dsInsRecordsStmt`. -/
structure IRCtx where
  w : ℕ
  vCap : ℕ
  eCap : ℕ
  G : MGraph
  X : Finset ℕ
  es : List ℕ
  esPtr : ℕ
  pres : ℕ
  gPtr : ℕ
  out : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hesB : esPtr + es.length < 2 ^ w
  hpB : pres + eCap < 2 ^ w
  hgB : gPtr + dynGraphSize vCap eCap < 2 ^ w
  hoB : out + 4 * es.length < 2 ^ w
  dOE : IvlDisj out (4 * es.length) esPtr es.length
  dOP : IvlDisj out (4 * es.length) pres eCap
  dOG : IvlDisj out (4 * es.length) gPtr (dynGraphSize vCap eCap)
  hes : ListAt mem0 esPtr es
  hesG : ∀ e ∈ es, e ∈ G.E
  hG : DynGraphAt mem0 gPtr vCap eCap G
  hpres : ∀ e < eCap, mem0 (pres + e) = if e ∈ X then 1 else 0

/-- Contract of `dsInsRecordsStmt`. -/
def dsInsRecordsContract (c : IRCtx) : Contract where
  pre args mem := args = [c.esPtr, c.es.length, c.pres, c.gPtr, c.out] ∧ mem = c.mem0
  post _ mem ret mem' :=
    ret = (insList c.X c.es).length ∧ ListAt mem' c.out (insWords c.G c.X c.es) ∧
    ∀ addr, (addr < c.out ∨ c.out + 4 * c.es.length ≤ addr) → mem' addr = mem addr
  cost _ _ := 210 * c.es.length + 20

/-- The loop invariant after the first `i` edges. -/
def IRInv (c : IRCtx) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = c.esPtr ∧ st.regs 1 = c.es.length ∧ st.regs 2 = c.pres ∧ st.regs 3 = c.gPtr ∧
  st.regs 4 = c.out ∧ st.regs 5 = (insList c.X (c.es.take i)).length ∧ st.regs 7 = i ∧
  ListAt st.mem c.out (insWords c.G c.X (c.es.take i)) ∧
  ∀ addr, (addr < c.out ∨ c.out + 4 * c.es.length ≤ addr) → st.mem addr = c.mem0 addr

end

public section

/-- One iteration of the loop of `dsInsRecordsStmt`. -/
theorem dsInsRecords_step_triple (c : IRCtx) {p : Program} {bOps : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) {i : ℕ} (hi : i < c.es.length) :
    Triple c.w p (IRInv c i) (dsInsRecordsBodyStmt bOps)
      (normalPost fun st₁ =>
        IRInv c (i + 1) { st₁ with regs := Function.update st₁.regs 7 (i + 1) } ∧
          st₁.regs 7 = i)
      (fun _ => 200) := by
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, r4, r5, r7, hL, hfr⟩ := hI
  have hw16 := c.hw16
  have hesB := c.hesB
  have hpB := c.hpB
  have hgB := c.hgB
  have hoB := c.hoB
  set e := c.es[i] with he
  have heG : e ∈ c.G.E := c.hesG e (List.getElem_mem hi)
  have heC : e < c.eCap := c.hG.2.2.1 e heG
  have hcnt : (insList c.X (c.es.take i)).length ≤ i := by
    have := insList_length_le c.X (c.es.take i)
    simp only [List.length_take] at this
    omega
  have hes_rd : st.mem (c.esPtr + i) = e :=
    (hfr _ (c.dOE.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))).trans
      (c.hes i hi)
  have hp_rd : st.mem (c.pres + e) = if e ∈ c.X then 1 else 0 :=
    (hfr _ (c.dOP.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))).trans
      (c.hpres e heC)
  have hGst : DynGraphAt st.mem c.gPtr c.vCap c.eCap c.G :=
    dynGraphAt_of_agree c.hG fun addr h1 h2 =>
      hfr addr (c.dOG.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr h1 h2)
  have hW := insWords_succ c.G c.X c.es i hi
  have hl := insList_succ c.X c.es i hi
  rw [← he] at hW hl
  dsimp only [dsInsRecordsBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r7)
      (by omega)) hes_rd) ?_
  refine runs_cond_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2]))
    (Expr.eval_reg_of_eq (by simp)) (by omega)) hp_rd) (fun hne => ?_) (fun hz => ?_)
  · -- `e ∈ X`: nothing to write.
    have hX : e ∈ c.X := by by_contra h; simp [h] at hne
    simp only [hX, ite_true, List.append_nil] at hW hl
    refine runs_nop_le ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
      by simp [r5, hl], by simp, by rw [hW]; exact hL, hfr⟩, by simp [r7]⟩
      (by simp [Expr.size])
  · -- `e ∉ X`: write the record.
    have hX : e ∉ c.X := by intro h; simp [h] at hz
    simp only [hX, ite_false] at hW hl
    set k := (insList c.X (c.es.take i)).length with hk
    have hWlen := insWords_length c.G c.X (c.es.take i)
    rw [← hk] at hWlen
    refine runs_seq_call_le (dgGetTail_meetsContract (w := c.w) (vCap := c.vCap) (eCap := c.eCap)
        (G := c.G) hpOps) (by eval_expr)
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> omega)
      ⟨c.gPtr, e, by simp [he], hw16, hgB, heG, hGst⟩ ?_
    rintro t mem₁ pos₁ ⟨_, _, hargs₁, hm₁, rfl⟩
    simp only [List.cons.injEq, and_true] at hargs₁
    obtain ⟨rfl, rfl⟩ := hargs₁
    subst hm₁
    refine runs_seq_call_le (dgGetHead_meetsContract (w := c.w) (vCap := c.vCap) (eCap := c.eCap)
        (G := c.G) hpOps) (by eval_expr)
      (fun v hv => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> omega)
      ⟨c.gPtr, e, by simp [he], hw16, hgB, heG, hGst⟩ ?_
    rintro h mem₂ pos₂ ⟨_, _, hargs₂, hm₂, rfl⟩
    simp only [List.cons.injEq, and_true] at hargs₂
    obtain ⟨rfl, rfl⟩ := hargs₂
    subst hm₂
    have ha : c.out + 4 * k + 3 < 2 ^ c.w := by omega
    refine runs_seq_assign_le (v := c.out + 4 * k)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r5]; try exact hk))
          (by omega)) (by omega)) ?_
    refine runs_seq_store_le (x := c.out + 4 * k) (v := 0) (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (x := c.out + 4 * k + 1) (v := e)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_seq_store_le (x := c.out + 4 * k + 2) (v := c.G.tail e)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp [he])) ?_
    refine runs_seq_store_le (x := c.out + 4 * k + 3) (v := c.G.head e)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp [he])) ?_
    refine runs_assign_le (v := k + 1)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5]; try exact hk)) (Expr.eval_const (by omega))
        (by omega)) ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
          by simp [hl]; exact hk, by simp, ?_, fun addr h => ?_⟩, by simp [r7]⟩ ?_
    · rw [hW]
      refine listAt_append.mpr ⟨?_, ?_⟩
      · refine (((hL.update_ge ?_).update_ge ?_).update_ge ?_).update_ge ?_ <;> omega
      · intro j hj
        simp only [List.length_cons, List.length_nil] at hj
        rw [hWlen]
        show Function.update (Function.update (Function.update (Function.update st.mem _ _) _ _)
          _ _) _ _ _ = _
        interval_cases j
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]; simp
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          simp [show c.out + 4 * k + 1 = c.out + (4 * k + 1) by omega]
        · rw [Function.update_of_ne (by omega)]
          simp [show c.out + 4 * k + 2 = c.out + (4 * k + 2) by omega]
        · simp [show c.out + 4 * k + 3 = c.out + (4 * k + 3) by omega]
    · show Function.update (Function.update (Function.update (Function.update st.mem _ _) _ _)
        _ _) _ _ _ = _
      have : k < c.es.length := by omega
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr addr h
    · simp only [dgGetTailContract, dgGetHeadContract, Expr.size_const, Expr.size_reg,
        Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil]
      omega

/-- `dsInsRecordsStmt` meets `dsInsRecordsContract`. -/
theorem dsInsRecords_meetsContract (c : IRCtx) {p : Program} {bI bOps : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpI : p.HasAt bI (insRecordsProcs bOps)) :
    MeetsContract c.w p (bI + insRecordsIdx) (dsInsRecordsContract c) := by
  refine meetsContract_of_runs
    (hpI.get (i := insRecordsIdx) (by simp [insRecordsProcs, insRecordsIdx])) ?_
  rintro args mem pos ω _ ⟨rfl, hmem⟩
  subst hmem
  simp only [insRecordsProcs, insRecordsIdx, List.getElem_cons_zero]
  dsimp only [dsInsRecordsStmt]
  have hw16 := c.hw16
  have hesB := c.hesB
  have hloop := Triple.forRange_const (w := c.w) (p := p)
    (P := fun st' => IRInv c 0 { st' with regs := Function.update st'.regs 7 0 })
    (r := 7) (lo := .const 0) (hi := .reg 1) (body := dsInsRecordsBodyStmt bOps)
    (Inv := IRInv c) 200 0 c.es.length (Nat.zero_le _) (by omega)
    (fun _ => by omega) (fun st' h => ⟨Expr.eval_const (by omega), h⟩)
    (fun k st' _ _ h => h.2.2.2.2.2.2.1) (fun k st' _ _ h => Expr.eval_reg_of_eq h.2.1)
    (fun k _ hk => dsInsRecords_step_triple c hpOps hk)
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · exact ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp [insList], by simp, fun j hj => by simp [insWords, insList] at hj,
      fun _ _ => rfl⟩
  · intro st hI
    obtain ⟨_, _, _, _, _, q5, _, hL, hfr⟩ := hI
    rw [List.take_of_length_le (Nat.le_refl _)] at q5 hL
    refine runs_ret_le (v := (insList c.X c.es).length) (Expr.eval_reg_of_eq q5)
      ⟨rfl, hL, hfr⟩ ?_
    simp only [Expr.size, dsInsRecordsContract]
    omega

end

end MinCostFlow.DynSpanner.Program
