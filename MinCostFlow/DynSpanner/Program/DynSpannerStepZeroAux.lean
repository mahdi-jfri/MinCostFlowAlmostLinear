module

public import MinCostFlow.DynSpanner.Program.DynSpannerDelRecords
public import MinCostFlow.DynSpanner.Program.DynSpannerInsRecords
import WordRAM.Tactic

/-!
# Auxiliary procedures for the `j = 0` restart step (`DynSpannerStepZeroAux`)

Provides three short deterministic Word-RAM procedures (`stepZeroAuxProcs`, length `3`) used by
the level-0 restart branch of Algorithm 6 (Theorem 8.2, page 64):

* `dsStampListStmt` (`stepZeroAuxIdxStampList = 0`): stamps `mem[stampBase + e] := stampVal` for
  every `e` in a list of edges at `listPtr` in `O(|es| + 1)` time.
* `dsListDelRecsStmt` (`stepZeroAuxIdxListDelRecs = 1`): scans a list `es` of old spanner edges
  against a 0/1 presence array for `X`, emitting `[1, e]` deletion records for `e ∉ X`
  (`delWords X es`, `delRecs_batchBodyAt`) in `O(|es| + 1)` time.
* `dsStampInsRecsStmt` (`stepZeroAuxIdxStampInsRecs = 2`): scans a list `es` of new spanner edges
  against a generation-stamp array (`mem[stampBase + e] = stampVal ↔ e ∈ X`), emitting
  `[0, e, tail e, head e]` insertion records for `e ∉ X` (`insWords G X es`, `insRecs_batchBodyAt`)
  in `O(|es| + 1)` time.

Also proves `restrictUpdate_length_eq_ite`, relating `(restrictUpdate u H).length` to whether its
encoded byte/word length is zero.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Procedure indices -/

def stepZeroAuxIdxStampList : ℕ := 0
def stepZeroAuxIdxListDelRecs : ℕ := 1
def stepZeroAuxIdxStampInsRecs : ℕ := 2

/-! ## Word-RAM statement bodies -/

/-- `args = [stampBase, listPtr, listLen, stampVal]`: sets
`mem[stampBase + mem[listPtr + k]] := stampVal` for `k < listLen`, returning `0`. -/
def dsStampListStmt : Stmt :=
  forRange 4 (.const 0) (.reg 2)
    (.assign 5 (.load (.bin .add (.reg 1) (.reg 4))) ;;
     .store (.bin .add (.reg 0) (.reg 5)) (.reg 3)) ;;
  .ret (.const 0)

/-- One iteration of `dsListDelRecsStmt`: emit `[1, e]` if `mem[pres + e] = 0`. -/
def dsListDelRecsBodyStmt : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
  .cond (.load (.bin .add (.reg 2) (.reg 6))) .nop
    (.assign 7 (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 4))) ;;
     .store (.reg 7) (.const 1) ;;
     .store (.bin .add (.reg 7) (.const 1)) (.reg 6) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1)))

/-- `args = [listPtr, listLen, presPtr, outPtr]`: emits deletion records for edges of `listPtr`
whose presence word is `0`, returning the number of records emitted. -/
def dsListDelRecsStmt : Stmt :=
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 1) dsListDelRecsBodyStmt ;;
  .ret (.reg 4)

/-- One iteration of `dsStampInsRecsStmt`: emit `[0, e, tail e, head e]` if
`mem[stampBase + e] ≠ stampVal`. -/
def dsStampInsRecsBodyStmt (bOps : ℕ) : Stmt :=
  .assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
  .cond (.bin .eq (.load (.bin .add (.reg 2) (.reg 8))) (.reg 3)) .nop
    (.call 9 (bOps + dgIdxGetTail) [.reg 4, .reg 8] ;;
     .call 10 (bOps + dgIdxGetHead) [.reg 4, .reg 8] ;;
     .assign 11 (.bin .add (.reg 5) (.bin .mul (.const 4) (.reg 6))) ;;
     .store (.reg 11) (.const 0) ;;
     .store (.bin .add (.reg 11) (.const 1)) (.reg 8) ;;
     .store (.bin .add (.reg 11) (.const 2)) (.reg 9) ;;
     .store (.bin .add (.reg 11) (.const 3)) (.reg 10) ;;
     .assign 6 (.bin .add (.reg 6) (.const 1)))

/-- `args = [listPtr, listLen, stampBase, stampVal, gPtr, outPtr]`: emits insertion records for
edges of `listPtr` whose stamp differs from `stampVal`, returning the number of records emitted. -/
def dsStampInsRecsStmt (bOps : ℕ) : Stmt :=
  .assign 6 (.const 0) ;;
  forRange 7 (.const 0) (.reg 1) (dsStampInsRecsBodyStmt bOps) ;;
  .ret (.reg 6)

/-- Auxiliary module for the `j = 0` step (`3` deterministic procedures). -/
def stepZeroAuxProcs (bOps : ℕ) : List Stmt :=
  [dsStampListStmt, dsListDelRecsStmt, dsStampInsRecsStmt bOps]

lemma stepZeroAuxProcs_length (bOps : ℕ) : (stepZeroAuxProcs bOps).length = 3 := rfl

lemma stepZeroAuxProcs_noRand (bOps : ℕ) : ∀ s ∈ stepZeroAuxProcs bOps, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Contracts -/

/-- Contract for `dsStampListStmt` (`[stampBase, listPtr, listLen, stampVal]`). -/
def dsStampListContract (w cap : ℕ) (es : List ℕ) (stampVal : ℕ) : Contract where
  pre args mem := ∃ stampBase listPtr,
    args = [stampBase, listPtr, es.length, stampVal] ∧ 16 ≤ 2 ^ w ∧
    stampBase + cap < 2 ^ w ∧ listPtr + es.length < 2 ^ w ∧ stampVal < 2 ^ w ∧
    IvlDisj stampBase cap listPtr es.length ∧
    ListAt mem listPtr es ∧ (∀ e ∈ es, e < cap)
  post args mem ret mem' := ∃ stampBase listPtr,
    args = [stampBase, listPtr, es.length, stampVal] ∧ ret = 0 ∧
    (∀ e ∈ es, mem' (stampBase + e) = stampVal) ∧
    ∀ addr, (∀ e ∈ es, addr ≠ stampBase + e) → mem' addr = mem addr
  cost _ _ := 35 * es.length + 25

/-- Context and precondition for `dsListDelRecsStmt`. -/
structure LDRCtx where
  w : ℕ
  eCap : ℕ
  X : Finset ℕ
  es : List ℕ
  listPtr : ℕ
  pres : ℕ
  out : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hlB : listPtr + es.length < 2 ^ w
  hpB : pres + eCap < 2 ^ w
  hoB : out + 2 * es.length < 2 ^ w
  dOL : IvlDisj out (2 * es.length) listPtr es.length
  dOP : IvlDisj out (2 * es.length) pres eCap
  hes : ListAt mem0 listPtr es
  hesC : ∀ e ∈ es, e < eCap
  hpres : ∀ e < eCap, mem0 (pres + e) = if e ∈ X then 1 else 0

/-- Contract for `dsListDelRecsStmt` (`[listPtr, listLen, presPtr, outPtr]`). -/
def dsListDelRecsContract (c : LDRCtx) : Contract where
  pre args mem := args = [c.listPtr, c.es.length, c.pres, c.out] ∧ mem = c.mem0
  post _ mem ret mem' :=
    ret = (delList c.X c.es).length ∧
    ListAt mem' c.out (delWords c.X c.es) ∧
    ∀ addr, (addr < c.out ∨ c.out + 2 * ret ≤ addr) → mem' addr = mem addr
  cost _ _ := 70 * c.es.length + 25

/-- Context and precondition for `dsStampInsRecsStmt`. -/
structure SIRCtx where
  w : ℕ
  vCap : ℕ
  eCap : ℕ
  G : MGraph
  X : Finset ℕ
  es : List ℕ
  listPtr : ℕ
  stampBase : ℕ
  stampVal : ℕ
  gPtr : ℕ
  out : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hlB : listPtr + es.length < 2 ^ w
  hsB : stampBase + eCap < 2 ^ w
  hsvB : stampVal < 2 ^ w
  hgB : gPtr + dynGraphSize vCap eCap < 2 ^ w
  hoB : out + 4 * es.length < 2 ^ w
  dOL : IvlDisj out (4 * es.length) listPtr es.length
  dOS : IvlDisj out (4 * es.length) stampBase eCap
  dOG : IvlDisj out (4 * es.length) gPtr (dynGraphSize vCap eCap)
  hes : ListAt mem0 listPtr es
  hesG : ∀ e ∈ es, e ∈ G.E
  hG : DynGraphAt mem0 gPtr vCap eCap G
  hstamp : ∀ e < eCap, mem0 (stampBase + e) = stampVal ↔ e ∈ X

/-- Contract for `dsStampInsRecsStmt` (`[listPtr, listLen, stampBase, stampVal, gPtr, outPtr]`). -/
def dsStampInsRecsContract (c : SIRCtx) : Contract where
  pre args mem :=
    args = [c.listPtr, c.es.length, c.stampBase, c.stampVal, c.gPtr, c.out] ∧ mem = c.mem0
  post _ mem ret mem' :=
    ret = (insList c.X c.es).length ∧
    ListAt mem' c.out (insWords c.G c.X c.es) ∧
    ∀ addr, (addr < c.out ∨ c.out + 4 * ret ≤ addr) → mem' addr = mem addr
  cost _ _ := 220 * c.es.length + 25

end

/-! ## Pure helpers and contract proofs -/

private def LDRInv (c : LDRCtx) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = c.listPtr ∧ st.regs 1 = c.es.length ∧ st.regs 2 = c.pres ∧ st.regs 3 = c.out ∧
  st.regs 4 = (delList c.X (c.es.take i)).length ∧ st.regs 5 = i ∧
  ListAt st.mem c.out (delWords c.X (c.es.take i)) ∧
  ∀ addr, (addr < c.out ∨ c.out + 2 * (delList c.X (c.es.take i)).length ≤ addr) →
    st.mem addr = c.mem0 addr

private def SIRInv (c : SIRCtx) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = c.listPtr ∧ st.regs 1 = c.es.length ∧ st.regs 2 = c.stampBase ∧
  st.regs 3 = c.stampVal ∧ st.regs 4 = c.gPtr ∧ st.regs 5 = c.out ∧
  st.regs 6 = (insList c.X (c.es.take i)).length ∧ st.regs 7 = i ∧
  ListAt st.mem c.out (insWords c.G c.X (c.es.take i)) ∧
  ∀ addr, (addr < c.out ∨ c.out + 4 * (insList c.X (c.es.take i)).length ≤ addr) →
    st.mem addr = c.mem0 addr

public section

/-- For any deletion or vertex split `u`, `(restrictUpdate u H).length` is `0` when its encoded
word count is `0` and `1` otherwise. -/
lemma restrictUpdate_length_eq_ite {mem : ℕ → ℕ} {a : ℕ} {H : MGraph} {u : Update} {prefWords : ℕ}
    (hdu : isDelOrSplit u) (hB : BatchBodyAt mem a H (restrictUpdate u H) prefWords) :
    (restrictUpdate u H).length = if prefWords = 0 then 0 else 1 := by
  cases u with
  | insert _ _ _ => exact hdu.elim
  | delete e =>
    by_cases he : e ∈ H.E
    · simp only [restrictUpdate, he, ↓reduceIte, List.length_singleton] at hB ⊢
      rcases hB with ⟨len, hle, ⟨rfl, _⟩, hrest⟩
      have h0 : prefWords - 2 = 0 := hrest
      have hp : prefWords = 2 := by omega
      simp [hp]
    · simp only [restrictUpdate, he, ↓reduceIte, List.length_nil] at hB ⊢
      have hp : prefWords = 0 := hB
      simp [hp]
  | split v v' St Sh =>
    simp only [restrictUpdate, List.length_singleton] at hB ⊢
    rcases hB with ⟨len, hle, hu, hrest⟩
    have h0 : prefWords - len = 0 := hrest
    have hlen_pos : 0 < len := by
      rcases hu with ⟨Lt, Lh, _, _, _, _, rfl, _⟩ | ⟨Lt, Lh, _, _, _, _, rfl, _⟩ <;> omega
    have hne : prefWords ≠ 0 := by omega
    simp [hne]

/-- `dsStampListStmt` meets `dsStampListContract`. -/
theorem dsStampList_meetsContract {w cap : ℕ} {es : List ℕ} {stampVal : ℕ}
    {p : Program} {bZA bOps : ℕ} (hpZA : p.HasAt bZA (stepZeroAuxProcs bOps)) :
    MeetsContract w p (bZA + stepZeroAuxIdxStampList) (dsStampListContract w cap es stampVal) := by
  refine meetsContract_of_runs
    (hpZA.get (i := stepZeroAuxIdxStampList) (by simp [stepZeroAuxProcs, stepZeroAuxIdxStampList])) ?_
  rintro args mem pos ω _ ⟨stampBase, listPtr, rfl, hw16, hsB, hlB, hsvB, hdisj, hL, hes⟩
  simp only [stepZeroAuxProcs, stepZeroAuxIdxStampList, List.getElem_cons_zero]
  dsimp only [dsStampListStmt]
  set Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = stampBase ∧ st.regs 1 = listPtr ∧ st.regs 2 = es.length ∧
    st.regs 3 = stampVal ∧ st.regs 4 = k ∧
    (∀ j < k, ∀ (hj : j < es.length), st.mem (stampBase + es[j]'hj) = stampVal) ∧
    ∀ addr, (∀ e ∈ es, addr ≠ stampBase + e) → st.mem addr = mem addr
  have hloop : Triple w p (fun st => Inv 0 { st with regs := Function.update st.regs 4 0 })
      (forRange 4 (.const 0) (.reg 2)
        (.assign 5 (.load (.bin .add (.reg 1) (.reg 4))) ;;
         .store (.bin .add (.reg 0) (.reg 5)) (.reg 3)))
      (normalPost (Inv es.length))
      (fun _ => 35 * es.length + 12) := by
    refine Triple.forRange_const 20 0 es.length (Nat.zero_le _) (by omega) (fun _ => by omega)
      (Inv := Inv) (fun _ h => ⟨Expr.eval_const (by omega), h⟩)
      (fun _ _ _ _ h => h.2.2.2.2.1) (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
      (fun k _ hk => ?_) |>.conseq (fun _ h => h) (fun o st h => h) (fun _ _ => by simp [Expr.size]; omega)
    intro st ω' ⟨r0, r1, r2, r3, r4, hst, hfr⟩
    have he : es[k]'hk < cap := hes _ (List.getElem_mem hk)
    have hmem_k : st.mem (listPtr + k) = es[k]'hk := by
      rw [hfr _ fun e he' => by
        have hec := hes e he'
        have := hdisj.addr_sub (Nat.le_refl _) (Nat.le_refl _) (listPtr + k) (by omega) (by omega)
        omega]
      exact hL k hk
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := es[k]'hk)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r1) (Expr.eval_reg_of_eq r4)
        (by omega)) hmem_k) ?_
    refine runs_store_le (x := stampBase + es[k]'hk) (v := stampVal)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0])) (Expr.eval_reg_of_eq (v := es[k]'hk) (by simp))
        (by omega)) (Expr.eval_reg_of_eq (by simp [r3])) ?_ ?_
    · refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp, fun j hj hje => ?_,
        fun addr ha => ?_⟩, by simp [r4]⟩
      · dsimp only
        by_cases hjk : j = k
        · subst hjk; simp [Function.update]
        · by_cases heq : stampBase + es[j]'hje = stampBase + es[k]'hk
          · rw [heq]; simp [Function.update]
          · rw [Function.update_of_ne heq]; exact hst j (by omega) hje
      · dsimp only
        rw [Function.update_of_ne (ha _ (List.getElem_mem hk))]
        exact hfr addr ha
    · simp [Expr.size]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState], by simp [startState],
    by simp [startState], by simp, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩ ?_
  intro st₁ ⟨_, _, _, _, _, hst, hfr⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega))
    ⟨stampBase, listPtr, rfl, rfl, fun e he => ?_, hfr⟩ ?_
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp he
    exact hst j hj hj
  · simp [Expr.size, dsStampListContract]

private theorem dsListDelRecs_step_triple (c : LDRCtx) {p : Program} {i : ℕ} (hi : i < c.es.length) :
    Triple c.w p (LDRInv c i) dsListDelRecsBodyStmt
      (normalPost fun st₁ =>
        LDRInv c (i + 1) { st₁ with regs := Function.update st₁.regs 5 (i + 1) } ∧
          st₁.regs 5 = i)
      (fun _ => 55) := by
  intro st ω ⟨r0, r1, r2, r3, r4, r5, hL, hfr⟩
  have hw16 := c.hw16
  have hlB := c.hlB
  have hpB := c.hpB
  have hoB := c.hoB
  set e := c.es[i] with he
  have heC : e < c.eCap := c.hesC e (List.getElem_mem hi)
  have hcnt : (delList c.X (c.es.take i)).length ≤ i := by
    have := delList_length_le c.X (c.es.take i)
    simp only [List.length_take] at this
    omega
  have hes_rd : st.mem (c.listPtr + i) = e :=
    (hfr _ ((c.dOL.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega)).imp id
      (fun h => by omega))).trans (c.hes i hi)
  have hp_rd : st.mem (c.pres + e) = if e ∈ c.X then 1 else 0 :=
    (hfr _ ((c.dOP.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega)).imp id
      (fun h => by omega))).trans (c.hpres e heC)
  have hW := delWords_succ c.X c.es i hi
  have hl := delList_succ c.X c.es i hi
  rw [← he] at hW hl
  dsimp only [dsListDelRecsBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r5)
      (by omega)) hes_rd) ?_
  refine runs_cond_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2]))
    (Expr.eval_reg_of_eq (by simp)) (by omega)) hp_rd) (fun hne => ?_) (fun hz => ?_)
  · have hX : e ∈ c.X := by by_contra h; simp [h] at hne
    simp only [hX, ite_true, List.append_nil] at hW hl
    refine runs_nop_le ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3],
      by simp [r4, hl], by simp, by rw [hW]; exact hL, by rw [hl]; exact hfr⟩, by simp [r5]⟩
      (by simp [Expr.size])
  · have hX : e ∉ c.X := by intro h; simp [h] at hz
    simp only [hX, ite_false] at hW hl
    set k := (delList c.X (c.es.take i)).length with hk
    have hWlen := delWords_length c.X (c.es.take i)
    rw [← hk] at hWlen
    have ha : c.out + 2 * k + 1 < 2 ^ c.w := by omega
    refine runs_seq_assign_le (v := c.out + 2 * k)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r4]; try exact hk))
          (by omega)) (by omega)) ?_
    refine runs_seq_store_le (x := c.out + 2 * k) (v := 1) (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (by omega)) ?_
    refine runs_seq_store_le (x := c.out + 2 * k + 1) (v := e)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_assign_le (v := k + 1)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r4]; try exact hk)) (Expr.eval_const (by omega))
        (by omega)) ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3],
          by simp [hl]; exact hk, by simp, ?_, fun addr h => ?_⟩, by simp [r5]⟩ ?_
    · rw [hW]
      refine listAt_append.mpr ⟨?_, ?_⟩
      · refine ((hL.update_ge ?_).update_ge ?_) <;> omega
      · intro j hj
        simp only [List.length_cons, List.length_nil] at hj
        rw [hWlen]
        show Function.update (Function.update st.mem _ _) _ _ _ = _
        interval_cases j
        · rw [Function.update_of_ne (by omega)]; simp
        · simp [show c.out + 2 * k + 1 = c.out + (2 * k + 1) by omega]
    · show Function.update (Function.update st.mem _ _) _ _ _ = _
      rw [hl, List.length_append, List.length_singleton, ← hk] at h
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr addr (h.imp id fun h2 => by omega)
    · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

/-- `dsListDelRecsStmt` meets `dsListDelRecsContract`. -/
theorem dsListDelRecs_meetsContract (c : LDRCtx) {p : Program} {bZA bOps : ℕ}
    (hpZA : p.HasAt bZA (stepZeroAuxProcs bOps)) :
    MeetsContract c.w p (bZA + stepZeroAuxIdxListDelRecs) (dsListDelRecsContract c) := by
  refine meetsContract_of_runs
    (hpZA.get (i := stepZeroAuxIdxListDelRecs) (by simp [stepZeroAuxProcs, stepZeroAuxIdxListDelRecs])) ?_
  rintro args mem pos ω _ ⟨rfl, hmem⟩
  subst hmem
  simp only [stepZeroAuxProcs, stepZeroAuxIdxListDelRecs, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsListDelRecsStmt]
  have hw16 := c.hw16
  have hlB := c.hlB
  have hloop := Triple.forRange_const (w := c.w) (p := p)
    (P := fun st' => LDRInv c 0 { st' with regs := Function.update st'.regs 5 0 })
    (r := 5) (lo := .const 0) (hi := .reg 1) (body := dsListDelRecsBodyStmt)
    (Inv := LDRInv c) 55 0 c.es.length (Nat.zero_le _) (by omega)
    (fun _ => by omega) (fun st' h => ⟨Expr.eval_const (by omega), h⟩)
    (fun k st' _ _ h => h.2.2.2.2.2.1) (fun k st' _ _ h => Expr.eval_reg_of_eq h.2.1)
    (fun k _ hk => dsListDelRecs_step_triple c hk)
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · exact ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp [delList], by simp, fun j hj => by simp [delWords, delList] at hj,
      fun _ _ => rfl⟩
  · intro st hI
    obtain ⟨_, _, _, _, q4, _, hL, hfr⟩ := hI
    rw [List.take_of_length_le (Nat.le_refl _)] at q4 hL hfr
    refine runs_ret_le (v := (delList c.X c.es).length) (Expr.eval_reg_of_eq q4)
      ⟨rfl, hL, hfr⟩ ?_
    simp only [Expr.size, dsListDelRecsContract]; omega

private theorem dsStampInsRecs_step_triple (c : SIRCtx) {p : Program} {bOps : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) {i : ℕ} (hi : i < c.es.length) :
    Triple c.w p (SIRInv c i) (dsStampInsRecsBodyStmt bOps)
      (normalPost fun st₁ =>
        SIRInv c (i + 1) { st₁ with regs := Function.update st₁.regs 7 (i + 1) } ∧
          st₁.regs 7 = i)
      (fun _ => 205) := by
  intro st ω ⟨r0, r1, r2, r3, r4, r5, r6, r7, hL, hfr⟩
  have hw16 := c.hw16
  have hlB := c.hlB
  have hsB := c.hsB
  have hsvB := c.hsvB
  have hgB := c.hgB
  have hoB := c.hoB
  set e := c.es[i] with he
  have heG : e ∈ c.G.E := c.hesG e (List.getElem_mem hi)
  have heC : e < c.eCap := c.hG.2.2.1 e heG
  have hcnt : (insList c.X (c.es.take i)).length ≤ i := by
    have := insList_length_le c.X (c.es.take i)
    simp only [List.length_take] at this
    omega
  have hes_rd : st.mem (c.listPtr + i) = e :=
    (hfr _ ((c.dOL.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega)).imp id
      (fun h => by omega))).trans (c.hes i hi)
  have hst_rd : st.mem (c.stampBase + e) = c.mem0 (c.stampBase + e) :=
    hfr _ ((c.dOS.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega)).imp id
      (fun h => by omega))
  have hGst : DynGraphAt st.mem c.gPtr c.vCap c.eCap c.G :=
    dynGraphAt_of_agree c.hG fun addr h1 h2 =>
      hfr addr ((c.dOG.addr_sub (Nat.le_refl _) (Nat.le_refl _) addr h1 h2).imp id
        (fun h => by omega))
  have hW := insWords_succ c.G c.X c.es i hi
  have hl := insList_succ c.X c.es i hi
  rw [← he] at hW hl
  dsimp only [dsStampInsRecsBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r7)
      (by omega)) hes_rd) ?_
  refine runs_cond_le (v := if c.mem0 (c.stampBase + e) = c.stampVal then 1 else 0)
    (Expr.eval_eq_op
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2]))
        (Expr.eval_reg_of_eq (by simp)) (by omega)) hst_rd)
      (Expr.eval_reg_of_eq (by simp [r3])) (by omega)) (fun hne => ?_) (fun hz => ?_)
  · have hX : e ∈ c.X := (c.hstamp e heC).mp (by by_contra h; simp [h] at hne)
    simp only [hX, ite_true, List.append_nil] at hW hl
    refine runs_nop_le ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
      by simp [r5], by simp [r6, hl], by simp, by rw [hW]; exact hL, by rw [hl]; exact hfr⟩,
      by simp [r7]⟩ (by simp [Expr.size])
  · have hX : e ∉ c.X := fun h => by
      have heq := (c.hstamp e heC).mpr h
      simp [heq] at hz
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
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r6]; try exact hk))
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
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r6]; try exact hk)) (Expr.eval_const (by omega))
        (by omega)) ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
          by simp [r5], by simp [hl]; exact hk, by simp, ?_, fun addr h => ?_⟩, by simp [r7]⟩ ?_
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
      rw [hl, List.length_append, List.length_singleton, ← hk] at h
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr addr (h.imp id fun h2 => by omega)
    · simp only [dgGetTailContract, dgGetHeadContract, Expr.size_const, Expr.size_reg,
        Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil]
      omega

/-- `dsStampInsRecsStmt` meets `dsStampInsRecsContract`. -/
theorem dsStampInsRecs_meetsContract (c : SIRCtx) {p : Program} {bZA bOps : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpZA : p.HasAt bZA (stepZeroAuxProcs bOps)) :
    MeetsContract c.w p (bZA + stepZeroAuxIdxStampInsRecs) (dsStampInsRecsContract c) := by
  refine meetsContract_of_runs
    (hpZA.get (i := stepZeroAuxIdxStampInsRecs) (by simp [stepZeroAuxProcs, stepZeroAuxIdxStampInsRecs])) ?_
  rintro args mem pos ω _ ⟨rfl, hmem⟩
  subst hmem
  simp only [stepZeroAuxProcs, stepZeroAuxIdxStampInsRecs, List.getElem_cons_succ, List.getElem_cons_zero]
  dsimp only [dsStampInsRecsStmt]
  have hw16 := c.hw16
  have hlB := c.hlB
  have hloop := Triple.forRange_const (w := c.w) (p := p)
    (P := fun st' => SIRInv c 0 { st' with regs := Function.update st'.regs 7 0 })
    (r := 7) (lo := .const 0) (hi := .reg 1) (body := dsStampInsRecsBodyStmt bOps)
    (Inv := SIRInv c) 205 0 c.es.length (Nat.zero_le _) (by omega)
    (fun _ => by omega) (fun st' h => ⟨Expr.eval_const (by omega), h⟩)
    (fun k st' _ _ h => h.2.2.2.2.2.2.2.1) (fun k st' _ _ h => Expr.eval_reg_of_eq h.2.1)
    (fun k _ hk => dsStampInsRecs_step_triple c hpOps hk)
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · exact ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp [startState], by simp [insList], by simp,
      fun j hj => by simp [insWords, insList] at hj, fun _ _ => rfl⟩
  · intro st hI
    obtain ⟨_, _, _, _, _, _, q6, _, hL, hfr⟩ := hI
    rw [List.take_of_length_le (Nat.le_refl _)] at q6 hL hfr
    refine runs_ret_le (v := (insList c.X c.es).length) (Expr.eval_reg_of_eq q6)
      ⟨rfl, hL, hfr⟩ ?_
    simp only [Expr.size, dsStampInsRecsContract]; omega

end

end MinCostFlow.DynSpanner.Program
