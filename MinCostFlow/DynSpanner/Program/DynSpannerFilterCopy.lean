module

public import MinCostFlow.DynSpanner.Program.DynSpannerWalkHelpers
public import MinCostFlow.DynSpanner.Program.StateLayout
import WordRAM.Tactic

/-!
# Keeping the elements of a list that lie in a set

The first records of `U_H` in a step are `restrictUpdate u H`. For a split of `v`, this is the
split record of `G` with its two edge lists cut down to the edges of `H`. `dsFilterCopyStmt`
does this cut for one list: it walks over a list `es` in memory, reads a presence array of a set
`X`, and copies each `e ∈ es` with `e ∈ X` to `out`, keeping the order. It returns the number of
copied words. `dsFilterCopy_meetsContract` proves its contract, with cost `40 · |es| + 20`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## The program -/

/-- One element `e = es[r7]`: copy it if `e ∈ X`. -/
def dsFilterCopyBodyStmt : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.reg 7))) ;;
  .cond (.load (.bin .add (.reg 2) (.reg 6)))
    (.store (.bin .add (.reg 3) (.reg 5)) (.reg 6) ;;
     .assign 5 (.bin .add (.reg 5) (.const 1)))
    .nop

/-- `args = [esPtr, esLen, presPtr, out]`; returns the number of copied elements. -/
def dsFilterCopyStmt : Stmt :=
  .assign 5 (.const 0) ;;
  forRange 7 (.const 0) (.reg 1) dsFilterCopyBodyStmt ;;
  .ret (.reg 5)

def filterCopyProcs : List Stmt := [dsFilterCopyStmt]

def filterCopyIdx : ℕ := 0

lemma filterCopyProcs_noRand : ∀ s ∈ filterCopyProcs, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The elements of `es` in `X`, in order. -/
def keepList (X : Finset ℕ) (es : List ℕ) : List ℕ := es.filter fun e => decide (e ∈ X)

lemma keepList_succ (X : Finset ℕ) (es : List ℕ) (i : ℕ) (hi : i < es.length) :
    keepList X (es.take (i + 1)) =
      keepList X (es.take i) ++ if es[i] ∈ X then [es[i]] else [] := by
  simp only [keepList, List.take_succ_eq_append_getElem hi, List.filter_append]
  split_ifs with h <;> simp [h]

lemma keepList_length_le (X : Finset ℕ) (es : List ℕ) : (keepList X es).length ≤ es.length :=
  List.length_filter_le _ _

/-! ## The contract -/

/-- The data and the precondition of `dsFilterCopyStmt`. -/
structure FCCtx where
  w : ℕ
  eCap : ℕ
  X : Finset ℕ
  es : List ℕ
  esPtr : ℕ
  pres : ℕ
  out : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hesB : esPtr + es.length < 2 ^ w
  hpB : pres + eCap < 2 ^ w
  hoB : out + es.length < 2 ^ w
  dOE : IvlDisj out es.length esPtr es.length
  dOP : IvlDisj out es.length pres eCap
  hes : ListAt mem0 esPtr es
  hesC : ∀ e ∈ es, e < eCap
  hpres : ∀ e < eCap, mem0 (pres + e) = if e ∈ X then 1 else 0

/-- Contract of `dsFilterCopyStmt`. -/
def dsFilterCopyContract (c : FCCtx) : Contract where
  pre args mem := args = [c.esPtr, c.es.length, c.pres, c.out] ∧ mem = c.mem0
  post _ mem ret mem' :=
    ret = (keepList c.X c.es).length ∧ ListAt mem' c.out (keepList c.X c.es) ∧
    ∀ addr, (addr < c.out ∨ c.out + c.es.length ≤ addr) → mem' addr = mem addr
  cost _ _ := 40 * c.es.length + 20

/-- The loop invariant after the first `i` elements. -/
def FCInv (c : FCCtx) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = c.esPtr ∧ st.regs 1 = c.es.length ∧ st.regs 2 = c.pres ∧
  st.regs 3 = c.out ∧ st.regs 5 = (keepList c.X (c.es.take i)).length ∧ st.regs 7 = i ∧
  ListAt st.mem c.out (keepList c.X (c.es.take i)) ∧
  ∀ addr, (addr < c.out ∨ c.out + c.es.length ≤ addr) → st.mem addr = c.mem0 addr

end

public section

/-- One iteration of the loop of `dsFilterCopyStmt`. -/
theorem dsFilterCopy_step_triple (c : FCCtx) {p : Program} {i : ℕ} (hi : i < c.es.length) :
    Triple c.w p (FCInv c i) dsFilterCopyBodyStmt
      (normalPost fun st₁ =>
        FCInv c (i + 1) { st₁ with regs := Function.update st₁.regs 7 (i + 1) } ∧
          st₁.regs 7 = i)
      (fun _ => 30) := by
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, r5, r7, hL, hfr⟩ := hI
  have hw16 := c.hw16
  have hesB := c.hesB
  have hpB := c.hpB
  have hoB := c.hoB
  set e := c.es[i] with he
  have heC : e < c.eCap := c.hesC e (List.getElem_mem hi)
  have hcnt : (keepList c.X (c.es.take i)).length ≤ i := by
    have := keepList_length_le c.X (c.es.take i)
    simp only [List.length_take] at this
    omega
  have hes_rd : st.mem (c.esPtr + i) = e :=
    (hfr _ (c.dOE.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))).trans
      (c.hes i hi)
  have hp_rd : st.mem (c.pres + e) = if e ∈ c.X then 1 else 0 :=
    (hfr _ (c.dOP.addr_sub (Nat.le_refl _) (Nat.le_refl _) _ (by omega) (by omega))).trans
      (c.hpres e heC)
  have hl := keepList_succ c.X c.es i hi
  rw [← he] at hl
  dsimp only [dsFilterCopyBodyStmt]
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r7)
      (by omega)) hes_rd) ?_
  refine runs_cond_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2]))
    (Expr.eval_reg_of_eq (by simp)) (by omega)) hp_rd) (fun hne => ?_) (fun hz => ?_)
  · -- `e ∈ X`: copy it.
    have hX : e ∈ c.X := by by_contra h; simp [h] at hne
    simp only [hX, ite_true] at hl
    set k := (keepList c.X (c.es.take i)).length with hk
    refine runs_seq_store_le (x := c.out + k) (v := e)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r3]))
        (Expr.eval_reg_of_eq (by simp [r5]; try exact hk)) (by omega))
      (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_assign_le (v := k + 1)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r5]; try exact hk)) (Expr.eval_const (by omega))
        (by omega)) ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3],
          by simp [hl]; exact hk, by simp, ?_, fun addr h => ?_⟩, by simp [r7]⟩ ?_
    · rw [hl]
      refine listAt_append.mpr ⟨hL.update_ge (by omega), ?_⟩
      intro j hj
      simp only [List.length_cons, List.length_nil] at hj
      interval_cases j
      simp [← hk]
    · show Function.update st.mem _ _ addr = _
      rw [Function.update_of_ne (by omega)]
      exact hfr addr h
    · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
      omega
  · -- `e ∉ X`: nothing to copy.
    have hX : e ∉ c.X := by intro h; simp [h] at hz
    simp only [hX, ite_false, List.append_nil] at hl
    refine runs_nop_le ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3],
      by simp [r5, hl], by simp, by rw [hl]; exact hL, hfr⟩, by simp [r7]⟩
      (by simp [Expr.size])

/-- `dsFilterCopyStmt` meets `dsFilterCopyContract`. -/
theorem dsFilterCopy_meetsContract (c : FCCtx) {p : Program} {bF : ℕ}
    (hpF : p.HasAt bF filterCopyProcs) :
    MeetsContract c.w p (bF + filterCopyIdx) (dsFilterCopyContract c) := by
  refine meetsContract_of_runs
    (hpF.get (i := filterCopyIdx) (by simp [filterCopyProcs, filterCopyIdx])) ?_
  rintro args mem pos ω _ ⟨rfl, hmem⟩
  subst hmem
  simp only [filterCopyProcs, filterCopyIdx, List.getElem_cons_zero]
  dsimp only [dsFilterCopyStmt]
  have hw16 := c.hw16
  have hesB := c.hesB
  have hloop := Triple.forRange_const (w := c.w) (p := p)
    (P := fun st' => FCInv c 0 { st' with regs := Function.update st'.regs 7 0 })
    (r := 7) (lo := .const 0) (hi := .reg 1) (body := dsFilterCopyBodyStmt)
    (Inv := FCInv c) 30 0 c.es.length (Nat.zero_le _) (by omega)
    (fun _ => by omega) (fun st' h => ⟨Expr.eval_const (by omega), h⟩)
    (fun k st' _ _ h => h.2.2.2.2.2.1) (fun k st' _ _ h => Expr.eval_reg_of_eq h.2.1)
    (fun k _ hk => dsFilterCopy_step_triple c hk)
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · exact ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp [keepList], by simp, fun j hj => by simp [keepList] at hj, fun _ _ => rfl⟩
  · intro st hI
    obtain ⟨_, _, _, _, q5, _, hL, hfr⟩ := hI
    rw [List.take_of_length_le (Nat.le_refl _)] at q5 hL
    refine runs_ret_le (v := (keepList c.X c.es).length) (Expr.eval_reg_of_eq q5)
      ⟨rfl, hL, hfr⟩ ?_
    simp only [Expr.size, dsFilterCopyContract]
    omega

end

end MinCostFlow.DynSpanner.Program
