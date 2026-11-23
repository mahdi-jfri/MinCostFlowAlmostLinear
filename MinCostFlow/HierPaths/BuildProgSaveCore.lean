module

public import MinCostFlow.HierPaths.BuildProgActiveCompact

/-!
# Saving the certified child sets

A certified child leaves the game. Keep a pointer to its core reply in the
table indexed by the original child number. The current terminal offset
determines that child number even after the active tables have been compacted.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The child numbers are recovered by subtracting the parent's first terminal
and dividing by the child size. -/
def originalChildExpr : Expr :=
  .bin .div (.bin .sub (.load (.bin .add (.reg 0) (.reg 7))) (.reg 4)) (.reg 3)

/-- A core reply is saved only on the nonzero tag branch. -/
def buildSaveCoreStep : Stmt :=
  .seq (.assign 8 (.load (.bin .add (.reg 1) (.reg 7))))
    (.cond (.load (.bin .add (.reg 8) (.const 3)))
      (.store (.bin .add (.reg 5) originalChildExpr) (.reg 8)) .nop)

/-- Args are `[offsets, replies, activeCount, childSize, parentStart, saved]`. -/
def buildSaveCoreProc : Stmt :=
  .seq (forRange 7 (.const 0) (.reg 2) buildSaveCoreStep) (.ret (.const 0))

theorem buildSaveCoreProc_noRand : buildSaveCoreProc.NoRand := by
  simp [buildSaveCoreProc, buildSaveCoreStep, forRange, forUp, Stmt.NoRand]

/-- The scan reads the active offsets and reply pointers above the saved table. -/
structure SaveCoreInput (w n s start offsets replies saved : ℕ) (mem : ℕ → ℕ)
    (child : ℕ → ℕ) (answer : ℕ → CoreResult) : Prop where
  size : 0 < s
  word : 3 < 2 ^ w
  offsetsEnd : offsets + n < 2 ^ w
  repliesEnd : replies + n < 2 ^ w
  childInj : ∀ i < n, ∀ j < n, child i = child j → i = j
  data : ∀ i < n, mem (offsets + i) = start + child i * s ∧
    start + child i * s < 2 ^ w ∧
    saved + child i < offsets ∧ saved + child i < replies ∧
    mem (replies + i) + 3 < 2 ^ w ∧
    mem (mem (replies + i) + 3) = coreTag (answer i)
  tagsAbove : ∀ i < n, ∀ j < n, saved + child i < mem (replies + j) + 3

/-- The table stores the pointers for all certified replies. Every other cell is
preserved. -/
def SavedCorePost (mem mem' : ℕ → ℕ) (replies saved n : ℕ) (child : ℕ → ℕ)
    (answer : ℕ → CoreResult) : Prop :=
  (∀ i < n, coreTag (answer i) ≠ 0 → mem' (saved + child i) = mem (replies + i)) ∧
  ∀ a, (∀ i < n, coreTag (answer i) ≠ 0 → a ≠ saved + child i) → mem' a = mem a

/-- A pass over the active table records the expander replies for the injection pass. -/
def buildSaveCoreContract (w n : ℕ) (child : ℕ → ℕ) (answer : ℕ → CoreResult) : Contract where
  pre args mem := ∃ offsets replies s start saved,
    args = [offsets,replies,n,s,start,saved] ∧ SaveCoreInput w n s start offsets replies saved mem child answer
  post args mem _ mem' := ∃ offsets replies s start saved,
    args = [offsets,replies,n,s,start,saved] ∧ SavedCorePost mem mem' replies saved n child answer
  cost _ _ := 50 * n + 14

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

private def saveCoreInv (mem : ℕ → ℕ) (offsets replies n s start saved : ℕ)
    (child : ℕ → ℕ) (answer : ℕ → CoreResult) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = offsets ∧ st.regs 1 = replies ∧ st.regs 2 = n ∧ st.regs 3 = s ∧
    st.regs 4 = start ∧ st.regs 5 = saved ∧ st.regs 7 = i ∧
    SavedCorePost mem st.mem replies saved i child answer

private theorem saveCoreStep_triple {w offsets replies n s start saved i : ℕ}
    {mem : ℕ → ℕ} {child : ℕ → ℕ} {answer : ℕ → CoreResult} (p : Program)
    (h : SaveCoreInput w n s start offsets replies saved mem child answer) (hi : i < n) :
    Triple w p (saveCoreInv mem offsets replies n s start saved child answer i) buildSaveCoreStep
      (normalPost fun st => saveCoreInv mem offsets replies n s start saved child answer (i + 1)
        {st with regs := Function.update st.regs 7 (i + 1)} ∧ st.regs 7 = i)
      (fun _ => 36) := by
  intro st ω ⟨h0,h1,h2,h3,h4,h5,h7,hTaken,hFrame⟩
  let ptr := mem (replies + i)
  let tag := coreTag (answer i)
  let dst := saved + child i
  obtain ⟨hOffset,hWord,hSO,hSR,hPtrW,hTag⟩ := h.data i hi
  have hW1 : 1 < 2 ^ w := by have := h.word; omega
  have hW2 : offsets + i < 2 ^ w := by have := h.offsetsEnd; omega
  have hW3 : replies + i < 2 ^ w := by have := h.repliesEnd; omega
  have hDest : dst < 2 ^ w := hSO.trans (Nat.le_of_lt (by have := h.offsetsEnd; omega))
  have hReadO : st.mem (offsets + i) = start + child i * s := by
    rw [hFrame _ ?_, hOffset]
    intro t ht _
    have hb := (h.data t (ht.trans hi)).2.2.1
    omega
  have hReadR : st.mem (replies + i) = ptr := hFrame _ (by
    intro t ht _
    have hb := (h.data t (ht.trans hi)).2.2.2.1
    omega)
  have hReadT : st.mem (ptr + 3) = tag :=
    (hFrame _ (fun t ht _ => (ne_of_lt (h.tagsAbove t (ht.trans hi) i hi)).symm)).trans hTag
  have hBody : ∀ (flag : ℕ), flag = tag →
      ∃ o st' c, Runs w p ω (.seq
        (.cond (.load (.bin .add (.reg 8) (.const 3)))
          (.store (.bin .add (.reg 5) originalChildExpr) (.reg 8)) .nop) .nop)
        {st with regs := Function.update st.regs 8 ptr} o st' c ∧
        (normalPost fun st => saveCoreInv mem offsets replies n s start saved child answer (i + 1)
          {st with regs := Function.update st.regs 7 (i + 1)} ∧ st.regs 7 = i) o st' ∧ c ≤ 30 := by
    intro flag hFlag
    refine runs_start_le ?_
    refine runs_seq_cond_le (v := flag) ?_ ?_ ?_
    · rw [hFlag]
      exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [ptr]))
        (Expr.eval_const h.word) hPtrW) hReadT
    · intro hNonzero
      have hTagNZ : tag ≠ 0 := hFlag ▸ hNonzero
      have hMul : child i * s < 2 ^ w := by omega
      have hChildW : child i < 2 ^ w := by dsimp [dst] at hDest; omega
      refine runs_seq_store_le (x := dst) (v := ptr) ?_ (Expr.eval_reg_of_eq (by simp)) ?_
      · simp [Expr.eval, originalChildExpr, Function.update, h0,h3,h4,h5,h7,hW2,hReadO,
          hMul,hChildW,h.size,dst,hDest]
      refine runs_nop_le ?_ ?_
      · refine ⟨⟨by simpa using h0,by simpa using h1,by simpa using h2,by simpa using h3,
          by simpa using h4,by simpa using h5,by simp,?_,?_⟩,h7⟩
        · intro j hj hNZ
          change Function.update st.mem dst ptr (saved + child j) = _
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · have hNe : saved + child j ≠ dst := by
              intro he
              have he' : child j = child i := Nat.add_left_cancel he
              exact (ne_of_lt hj) (h.childInj j (hj.trans hi) i hi he')
            rw [Function.update_of_ne hNe]
            exact hTaken j hj hNZ
          · simp [dst,ptr]
        · intro a ha
          change Function.update st.mem dst ptr a = mem a
          rw [Function.update_of_ne (ha i (Nat.lt_succ_self i) hTagNZ)]
          exact hFrame a fun j hj => ha j (hj.trans (Nat.lt_succ_self i))
      · simp [Expr.size,originalChildExpr]
    · intro hEq
      refine runs_seq_nop_le ?_
      refine runs_nop_le ?_ ?_
      · refine ⟨⟨by simpa using h0,by simpa using h1,by simpa using h2,by simpa using h3,
          by simpa using h4,by simpa using h5,by simp,?_,?_⟩,h7⟩
        · intro j hj hNZ
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hTaken j hj hNZ
          · rw [hFlag] at hEq
            exact False.elim (hNZ hEq)
        · intro a ha
          exact hFrame a fun j hj => ha j (hj.trans (Nat.lt_succ_self i))
      · simp [Expr.size]
  have hAssign : (Expr.load (.bin .add (.reg 1) (.reg 7))).eval w st = some ptr :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h1) (Expr.eval_reg_of_eq h7) hW3) hReadR
  obtain ⟨o, s', c', hRun, hPost, hc⟩ := hBody tag rfl
  have hCond : ∃ c ≤ c', Runs w p ω
      (.cond (.load (.bin .add (.reg 8) (.const 3)))
        (.store (.bin .add (.reg 5) originalChildExpr) (.reg 8)) .nop)
      {st with regs := Function.update st.regs 8 ptr} o s' c := by
    rcases runs_seq_iff.mp hRun with ⟨v,c,hcRun,rfl,rfl⟩ | ⟨u,c,c₂,hcRun,hN,rfl⟩
    · exact ⟨c,by omega,hcRun⟩
    · obtain ⟨rfl,rfl,rfl⟩ := runs_nop_iff.mp hN
      exact ⟨c,by omega,hcRun⟩
  obtain ⟨c,hc',hCond⟩ := hCond
  refine ⟨o,s',c+6,?_,hPost,by change c + 6 ≤ 36; omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨_,5,c,runs_assign_iff.mpr ⟨ptr,hAssign,rfl,rfl,rfl⟩,hCond,by omega⟩)

/-- The certificate pass records the expander replies in their original child slots. -/
theorem buildSaveCoreProc_meetsContract {w n f : ℕ} {p : Program}
    {child : ℕ → ℕ} {answer : ℕ → CoreResult}
    (hf : p.procs[f]? = some buildSaveCoreProc) :
    MeetsContract w p f (buildSaveCoreContract w n child answer) := by
  refine meetsContract_of_runs hf fun args mem pos ω hArgs hPre => ?_
  obtain ⟨offsets,replies,s,start,saved,rfl,hInput⟩ := hPre
  let st0 := startState [offsets,replies,n,s,start,saved] mem pos
  have hw : 1 < 2 ^ w := by have := hInput.word; omega
  have hLoop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 2)
    (body := buildSaveCoreStep) (P := fun st => st = st0)
    (Inv := saveCoreInv mem offsets replies n s start saved child answer)
    36 0 n (Nat.zero_le _) hw (fun _ => hArgs n (by simp))
    (fun st he => by
      subst st
      exact ⟨Expr.eval_const (Nat.two_pow_pos _),rfl,rfl,rfl,rfl,rfl,rfl,rfl,
        fun i hi => False.elim (Nat.not_lt_zero i hi),fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
    (fun _ _ hi => saveCoreStep_triple p hInput hi)
  refine runs_start_le ?_
  unfold buildSaveCoreProc
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_,_,_,_,_,_,_,hSave⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _))
    ⟨offsets,replies,s,start,saved,rfl,hSave⟩ ?_
  simp [buildSaveCoreContract,Expr.size]
  omega

end MinCostFlow.HierPaths
