module

public import MinCostFlow.DynSpanner.Program.DynSpannerFilterCopy
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
import WordRAM.Tactic

/-!
# The first records of `U_H`: the update restricted to `H`

The batch `U_H` of a step starts with `restrictUpdate u H`: the part of `u` that concerns `H`.
For a deletion of `e` this is the same deletion when `e ∈ E(H)`, and nothing otherwise. For a
split of `v`, it is the split with the moved edges cut down to the edges of `H`. In the record
format of `UpdateAt`, the split record of `G` holds two lists of edges, and the record for `H`
holds the same lists without the edges outside `H` (`dsFilterCopyStmt`).

`dsRestrictRecStmt` reads the record of `u` (for `G`) and a presence array of `E(H)`, and writes
the records of `restrictUpdate u H` (for `H`). `dsRestrictRec_meetsContract` proves its contract:
the output is a `BatchBodyAt` for `H`, no longer than the input, with cost `40 · len + 200`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args = [updPtr, pres, out]`; returns the number of words written. -/
def dsRestrictRecStmt (bF : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .cond (.bin .eq (.reg 3) (.const 1))
    (.assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
     .cond (.load (.bin .add (.reg 1) (.reg 4)))
       (.store (.reg 2) (.const 1) ;;
        .store (.bin .add (.reg 2) (.const 1)) (.reg 4) ;;
        .ret (.const 2))
       (.ret (.const 0)))
    (.assign 4 (.load (.bin .add (.reg 0) (.const 3))) ;;
     .assign 5 (.load (.bin .add (.reg 0) (.const 4))) ;;
     .assign 6 (.load (.bin .add (.reg 0) (.const 1))) ;;
     .assign 10 (.load (.bin .add (.reg 0) (.const 2))) ;;
     .call 8 (bF + filterCopyIdx)
       [.bin .add (.reg 0) (.const 5), .reg 4, .reg 1, .bin .add (.reg 2) (.const 5)] ;;
     .call 9 (bF + filterCopyIdx)
       [.bin .add (.bin .add (.reg 0) (.const 5)) (.reg 4), .reg 5, .reg 1,
        .bin .add (.bin .add (.reg 2) (.const 5)) (.reg 8)] ;;
     .store (.reg 2) (.reg 3) ;;
     .store (.bin .add (.reg 2) (.const 1)) (.reg 6) ;;
     .store (.bin .add (.reg 2) (.const 2)) (.reg 10) ;;
     .store (.bin .add (.reg 2) (.const 3)) (.reg 8) ;;
     .store (.bin .add (.reg 2) (.const 4)) (.reg 9) ;;
     .ret (.bin .add (.bin .add (.const 5) (.reg 8)) (.reg 9)))

def restrictRecProcs (bF : ℕ) : List Stmt := [dsRestrictRecStmt bF]

def restrictRecIdx : ℕ := 0

lemma restrictRecProcs_noRand (bF : ℕ) : ∀ s ∈ restrictRecProcs bF, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Contract of `dsRestrictRecStmt` for the record of `u` (for `G`) of `len` words. -/
def dsRestrictRecContract (w eCap : ℕ) (G H : MGraph) (u : Update)
    (len updPtr pres out : ℕ) : Contract where
  pre args mem :=
    args = [updPtr, pres, out] ∧ 16 ≤ 2 ^ w ∧ updPtr + len < 2 ^ w ∧ pres + eCap < 2 ^ w ∧
    out + len < 2 ^ w ∧ IvlDisj out len updPtr len ∧ IvlDisj out len pres eCap ∧
    (∀ i < len, mem (updPtr + i) < 2 ^ w) ∧
    UpdateAt mem updPtr G u len ∧ isDelOrSplit u ∧ G.UpdateIsValid u ∧
    (∀ e ∈ G.E, e < eCap) ∧ G.IsSubgraph H ∧
    (∀ e < eCap, mem (pres + e) = if e ∈ H.E then 1 else 0)
  post _ mem ret mem' :=
    ret ≤ len ∧ BatchBodyAt mem' out H (restrictUpdate u H) ret ∧
    ∀ addr, (addr < out ∨ out + len ≤ addr) → mem' addr = mem addr
  cost _ _ := 40 * len + 200

end

public section

/-- The data of a split record that the program needs, for both tags. The last clause turns the
cut record (lists filtered by `E(H)`) into the record of the restricted split for `H`. -/
theorem split_record_data {mem : ℕ → ℕ} {a : ℕ} {G H : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    {len : ℕ} (hu : UpdateAt mem a G (.split v v' St Sh) len) (hsub : G.IsSubgraph H) :
    ∃ tag Lt Lh, (tag = 2 ∨ tag = 3) ∧ (∀ e ∈ Lt, e ∈ G.E) ∧ (∀ e ∈ Lh, e ∈ G.E) ∧
      len = 5 + Lt.length + Lh.length ∧
      ListAt mem a ([tag, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) ∧
      ∀ mem' a', ListAt mem' a' ([tag, v, v', (keepList H.E Lt).length,
          (keepList H.E Lh).length] ++ keepList H.E Lt ++ keepList H.E Lh) →
        UpdateAt mem' a' H (.split v v' (St ∩ H.E) (Sh ∩ H.E))
          (5 + (keepList H.E Lt).length + (keepList H.E Lh).length) := by
  obtain ⟨_, hHE, htl⟩ := hsub
  rcases hu with ⟨Lt, Lh, hnt, hnh, hmt, hmh, hlen, hLA⟩ | ⟨Lt, Lh, hnt, hnh, hmt, hmh, hlen, hLA⟩
  · refine ⟨2, Lt, Lh, Or.inl rfl, fun e he => ((hmt e).mp he).1, fun e he => ((hmh e).mp he).1,
      hlen, hLA, fun mem' a' h => Or.inl ⟨keepList H.E Lt, keepList H.E Lh, hnt.filter _,
        hnh.filter _, fun e => ?_, fun e => ?_, rfl, h⟩⟩
    · simp only [keepList, List.mem_filter, decide_eq_true_eq, hmt, Finset.mem_inter]
      constructor
      · rintro ⟨⟨_, h2, h3⟩, h4⟩; exact ⟨h4, by rw [(htl e h4).1]; exact h2, h3, h4⟩
      · rintro ⟨h1, h2, h3, _⟩; exact ⟨⟨hHE h1, by rw [← (htl e h1).1]; exact h2, h3⟩, h1⟩
    · simp only [keepList, List.mem_filter, decide_eq_true_eq, hmh, Finset.mem_inter]
      constructor
      · rintro ⟨⟨_, h2, h3⟩, h4⟩; exact ⟨h4, by rw [(htl e h4).2]; exact h2, h3, h4⟩
      · rintro ⟨h1, h2, h3, _⟩; exact ⟨⟨hHE h1, by rw [← (htl e h1).2]; exact h2, h3⟩, h1⟩
  · refine ⟨3, Lt, Lh, Or.inr rfl, fun e he => ((hmt e).mp he).1, fun e he => ((hmh e).mp he).1,
      hlen, hLA, fun mem' a' h => Or.inr ⟨keepList H.E Lt, keepList H.E Lh, hnt.filter _,
        hnh.filter _, fun e => ?_, fun e => ?_, rfl, h⟩⟩
    · simp only [keepList, List.mem_filter, decide_eq_true_eq, hmt, Finset.mem_inter]
      constructor
      · rintro ⟨⟨_, h2, h3⟩, h4⟩
        exact ⟨h4, by rw [(htl e h4).1]; exact h2, fun h => h3 h.1⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨hHE h1, by rw [← (htl e h1).1]; exact h2, fun h => h3 ⟨h, h1⟩⟩, h1⟩
    · simp only [keepList, List.mem_filter, decide_eq_true_eq, hmh, Finset.mem_inter]
      constructor
      · rintro ⟨⟨_, h2, h3⟩, h4⟩
        exact ⟨h4, by rw [(htl e h4).2]; exact h2, fun h => h3 h.1⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨hHE h1, by rw [← (htl e h1).2]; exact h2, fun h => h3 ⟨h, h1⟩⟩, h1⟩

/-- `dsRestrictRecStmt` meets `dsRestrictRecContract`. -/
theorem dsRestrictRec_meetsContract {w eCap : ℕ} {G H : MGraph} {u : Update}
    {len updPtr pres out : ℕ} {p : Program} {bR bF : ℕ}
    (hpF : p.HasAt bF filterCopyProcs) (hpR : p.HasAt bR (restrictRecProcs bF)) :
    MeetsContract w p (bR + restrictRecIdx)
      (dsRestrictRecContract w eCap G H u len updPtr pres out) := by
  refine meetsContract_of_runs
    (hpR.get (i := restrictRecIdx) (by simp [restrictRecProcs, restrictRecIdx])) ?_
  rintro args mem pos ω _ ⟨rfl, hw16, huB, hpB, hoB, dOU, dOP, hwords, hu_at, hds, hvalid, heC,
    hsub, hpres⟩
  simp only [restrictRecProcs, restrictRecIdx, List.getElem_cons_zero]
  dsimp only [dsRestrictRecStmt]
  unfold IvlDisj at dOU dOP
  refine runs_start_le ?_
  cases u with
  | insert _ _ _ => exact absurd hds (by simp [isDelOrSplit])
  | delete e =>
    obtain ⟨rfl, hLA⟩ := hu_at
    have ht0 : mem updPtr = 1 := by simpa using hLA 0 (by simp)
    have ht1 : mem (updPtr + 1) = e := by simpa using hLA 1 (by simp)
    have he_lt : e < eCap := heC e hvalid
    refine runs_seq_assign_le (v := 1)
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) ht0) ?_
    refine runs_cond_le (v := 1) (Expr.eval_eq_true (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (by omega)) rfl (by omega)) (fun _ => ?_) (fun h => absurd h one_ne_zero)
    refine runs_seq_assign_le (v := e)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const (by omega)) (by omega)) ht1) ?_
    refine runs_cond_le (Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_reg_of_eq (by simp)) (by omega))
      (hpres e he_lt)) (fun hne => ?_) (fun hz => ?_)
    · have hH : e ∈ H.E := by by_contra h; simp [h] at hne
      refine runs_seq_store_le (x := out) (v := 1)
        (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) ?_
      refine runs_seq_store_le (x := out + 1) (v := e)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega))
          (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
      refine runs_ret_le (v := 2) (Expr.eval_const (by omega)) ⟨le_refl _, ?_, fun addr h => ?_⟩ ?_
      · simp only [restrictUpdate, hH, ite_true]
        refine ⟨2, le_refl _, ⟨rfl, fun j hj => ?_⟩, by simp [BatchBodyAt, Outcome.value]⟩
        simp only [List.length_cons, List.length_nil] at hj
        show Function.update (Function.update mem out 1) (out + 1) e (out + j) = _
        interval_cases j
        · simp
        · simp
      · show Function.update (Function.update mem out 1) (out + 1) e addr = _
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · simp only [Expr.size, dsRestrictRecContract]; omega
    · have hH : e ∉ H.E := by intro h; simp [h] at hz
      refine runs_ret_le (v := 0) (Expr.eval_const (by omega))
        ⟨Nat.zero_le _, by simp [restrictUpdate, hH, BatchBodyAt, Outcome.value], fun _ _ => rfl⟩ ?_
      simp only [Expr.size, dsRestrictRecContract]; omega
  | split v v' St Sh =>
    obtain ⟨tag, Lt, Lh, htag, hLtG, hLhG, hlen, hLA, hmk⟩ := split_record_data hu_at hsub
    subst hlen
    have hLA' := hLA
    rw [listAt_append, listAt_append] at hLA'
    obtain ⟨⟨hhdr, hLt⟩, hLh⟩ := hLA'
    simp only [List.length_cons, List.length_nil] at hLt hLh
    rw [List.length_append] at hLh
    simp only [List.length_cons, List.length_nil] at hLh
    have ht0 : mem updPtr = tag := by simpa using hhdr 0 (by simp)
    have ht1 : mem (updPtr + 1) = v := by simpa using hhdr 1 (by simp)
    have ht2 : mem (updPtr + 2) = v' := by simpa using hhdr 2 (by simp)
    have ht3 : mem (updPtr + 3) = Lt.length := by simpa using hhdr 3 (by simp)
    have ht4 : mem (updPtr + 4) = Lh.length := by simpa using hhdr 4 (by simp)
    have hwv : v < 2 ^ w := ht1 ▸ hwords 1 (by omega)
    have hwv' : v' < 2 ^ w := ht2 ▸ hwords 2 (by omega)
    have hwt : tag < 2 ^ w := by rcases htag with rfl | rfl <;> omega
    refine runs_seq_assign_le (v := tag)
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [startState])) ht0) ?_
    refine runs_cond_le (v := 0) (Expr.eval_eq_false (x := tag) (y := 1) (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const (by omega)) (by rcases htag with rfl | rfl <;> decide) (by omega))
      (fun h => absurd rfl h) (fun _ => ?_)
    refine runs_seq_assign_le (v := Lt.length)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const (by omega)) (by omega)) ht3) ?_
    refine runs_seq_assign_le (v := Lh.length)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const (by omega)) (by omega)) ht4) ?_
    refine runs_seq_assign_le (v := v)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const (by omega)) (by omega)) ht1) ?_
    refine runs_seq_assign_le (v := v')
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
        (Expr.eval_const (by omega)) (by omega)) ht2) ?_
    -- First list.
    let c₁ : FCCtx :=
      { w := w, eCap := eCap, X := H.E, es := Lt, esPtr := updPtr + 5, pres := pres,
        out := out + 5, mem0 := mem, hw16 := hw16, hesB := by omega, hpB := hpB,
        hoB := by omega, dOE := by unfold IvlDisj; omega, dOP := by unfold IvlDisj; omega,
        hes := by simpa [Nat.add_assoc] using hLt, hesC := fun e he => heC e (hLtG e he),
        hpres := hpres }
    refine runs_seq_call_le (vs := [updPtr + 5, Lt.length, pres, out + 5])
      (dsFilterCopy_meetsContract c₁ hpF)
      (by
        simp only [evalArgs, Expr.eval, BinOp.eval]
        simp [startState, show (5 : ℕ) < 2 ^ w by omega, show updPtr + 5 < 2 ^ w by omega,
          show out + 5 < 2 ^ w by omega])
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl|rfl) <;> omega)
      ⟨rfl, rfl⟩ ?_
    rintro r₈ mem₁ pos₁ ⟨hr₈, hL₁, hfr₁⟩
    simp only [c₁] at hr₈ hL₁ hfr₁
    subst hr₈
    have hk₁ := keepList_length_le H.E Lt
    -- Second list.
    have hLh₁ : ListAt mem₁ (updPtr + 5 + Lt.length) Lh :=
      (show ListAt mem (updPtr + 5 + Lt.length) Lh by simpa [Nat.add_assoc] using hLh).congr
        fun k h1 h2 => hfr₁ k (by
          show k < out + 5 ∨ out + 5 + Lt.length ≤ k
          omega)
    have hpres₁ : ∀ e < eCap, mem₁ (pres + e) = if e ∈ H.E then 1 else 0 := fun e he =>
      (hfr₁ _ (by show pres + e < out + 5 ∨ out + 5 + Lt.length ≤ pres + e; omega)).trans
        (hpres e he)
    let c₂ : FCCtx :=
      { w := w, eCap := eCap, X := H.E, es := Lh, esPtr := updPtr + 5 + Lt.length, pres := pres,
        out := out + 5 + (keepList H.E Lt).length, mem0 := mem₁, hw16 := hw16, hesB := by omega, hpB := hpB,
        hoB := by omega, dOE := by unfold IvlDisj; omega, dOP := by unfold IvlDisj; omega,
        hes := hLh₁, hesC := fun e he => heC e (hLhG e he), hpres := hpres₁ }
    refine runs_seq_call_le (vs := [updPtr + 5 + Lt.length, Lh.length, pres, out + 5 + (keepList H.E Lt).length])
      (dsFilterCopy_meetsContract c₂ hpF)
      (by
        simp only [evalArgs, Expr.eval, BinOp.eval]
        simp [startState, show (5 : ℕ) < 2 ^ w by omega, show updPtr + 5 < 2 ^ w by omega,
          show out + 5 < 2 ^ w by omega, show updPtr + 5 + Lt.length < 2 ^ w by omega,
          show out + 5 + (keepList H.E Lt).length < 2 ^ w by omega])
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl|rfl) <;> omega)
      ⟨rfl, rfl⟩ ?_
    rintro r₉ mem₂ pos₂ ⟨hr₉, hL₂, hfr₂⟩
    have hk₂ := keepList_length_le H.E Lh
    simp only [c₂] at hr₉ hL₂ hfr₂
    subst hr₉
    set a₁ := (keepList H.E Lt).length with ha₁
    set a₂ := (keepList H.E Lh).length with ha₂
    refine runs_seq_store_le (x := out) (v := tag)
      (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_seq_store_le (x := out + 1) (v := v)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega))
        (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_seq_store_le (x := out + 2) (v := v')
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega))
        (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_seq_store_le (x := out + 3) (v := a₁)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega))
        (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_seq_store_le (x := out + 4) (v := a₂)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega))
        (by omega)) (Expr.eval_reg_of_eq (by simp)) ?_
    refine runs_ret_le (v := 5 + a₁ + a₂)
      (Expr.eval_add (Expr.eval_add (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp))
        (by omega)) (Expr.eval_reg_of_eq (by simp)) (by omega))
      ⟨by show 5 + a₁ + a₂ ≤ _; omega, ?_, fun addr h => ?_⟩ ?_
    · -- The record.
      have hrec : ListAt (Function.update (Function.update (Function.update (Function.update
          (Function.update mem₂ out tag) (out + 1) v) (out + 2) v') (out + 3) a₁) (out + 4) a₂) out
          ([tag, v, v', a₁, a₂] ++ keepList H.E Lt ++ keepList H.E Lh) := by
        rw [listAt_append, listAt_append]
        refine ⟨⟨fun j hj => ?_, ?_⟩, ?_⟩
        · simp only [List.length_cons, List.length_nil] at hj
          interval_cases j <;> simp
        · have h1 : ListAt mem₂ (out + 5) (keepList H.E Lt) :=
            hL₁.congr fun k h1 h2 => hfr₂ k (by
              show k < out + 5 + a₁ ∨ out + 5 + a₁ + Lh.length ≤ k
              omega)
          have h2 := ((((h1.update_outside (x := out) (v := tag) (by omega)).update_outside
            (x := out + 1) (v := v) (by omega)).update_outside (x := out + 2) (v := v')
            (by omega)).update_outside (x := out + 3) (v := a₁) (by omega)).update_outside
            (x := out + 4) (v := a₂) (by omega)
          simpa using h2
        · have h2 := ((((hL₂.update_outside (x := out) (v := tag) (by omega)).update_outside
            (x := out + 1) (v := v) (by omega)).update_outside (x := out + 2) (v := v')
            (by omega)).update_outside (x := out + 3) (v := a₁) (by omega)).update_outside
            (x := out + 4) (v := a₂) (by omega)
          rw [show out + ([tag, v, v', a₁, a₂] ++ keepList H.E Lt).length = out + (5 + a₁) by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega]
          simpa [Nat.add_assoc] using h2
      simp only [restrictUpdate]
      refine ⟨5 + a₁ + a₂, le_refl _, hmk _ _ hrec, by simp [BatchBodyAt, Outcome.value]⟩
    · show Function.update (Function.update (Function.update (Function.update
          (Function.update mem₂ out tag) (out + 1) v) (out + 2) v') (out + 3) a₁) (out + 4) a₂
          addr = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      rw [hfr₂ addr (by omega), hfr₁ addr (by omega)]
      rfl
    · simp only [Expr.size, argsSize, dsRestrictRecContract, dsFilterCopyContract, c₁, c₂]
      omega

end

end MinCostFlow.DynSpanner.Program
