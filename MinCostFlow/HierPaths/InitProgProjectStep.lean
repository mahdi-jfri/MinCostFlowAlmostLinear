module

public import MinCostFlow.HierPaths.InitProgProjectModel

/-!
# Emitting one projected word

A zero label leaves the output pointer unchanged. A positive label emits the
input edge number or the owner of the current terminal, depending on the column.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Words emitted by one step in the chosen column. -/
def initProjectEntry (owner : ℕ → ℕ) (label : Option ℕ) (verts : Bool) (u : ℕ) :
    List ℕ :=
  label.toList.map fun e => if verts then owner u else e

/-- Arguments are the label and owner arrays, input edge and terminal, and destination. -/
def initProjectEmit (verts : Bool) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.reg 2))) ;;
  .cond (.reg 5)
    (.store (.reg 4) (if verts then .load (.bin .add (.reg 1) (.reg 3))
      else .bin .sub (.reg 5) (.const 1)) ;;
      .ret (.bin .add (.reg 4) (.const 1)))
    (.ret (.reg 4))

theorem initProjectEmit_noRand (verts : Bool) : (initProjectEmit verts).NoRand := by
  cases verts <;> simp [initProjectEmit, Stmt.NoRand]

/-- The caller supplies the two read addresses and room for the output word if present. -/
def initProjectEmitContract (w : ℕ) (owner : ℕ → ℕ) (label : Option ℕ) (verts : Bool)
    (e u : ℕ) : Contract where
  pre args mem := ∃ L O dst, args = [L, O, e, u, dst] ∧ L + e < 2 ^ w ∧ O + u < 2 ^ w ∧
    mem (L + e) = labelWord label ∧ mem (O + u) = owner u ∧ labelWord label < 2 ^ w ∧
    owner u < 2 ^ w ∧ dst + (initProjectEntry owner label verts u).length < 2 ^ w ∧ 1 < 2 ^ w
  post args mem r mem' := ∃ L O dst, args = [L, O, e, u, dst] ∧
    r = dst + (initProjectEntry owner label verts u).length ∧
    ListAt mem' dst (initProjectEntry owner label verts u) ∧
    ∀ y, y < dst ∨ r ≤ y → mem' y = mem y
  cost _ _ := 30

theorem initProjectEmit_meetsContract {w f e u : ℕ} {owner : ℕ → ℕ} {label : Option ℕ}
    {verts : Bool} {p : Program} (hp : p.procs[f]? = some (initProjectEmit verts)) :
    MeetsContract w p f (initProjectEmitContract w owner label verts e u) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨L, O, dst, rfl, hL, hO, hl, ho, hlw, how, hroom, h1⟩ := hpre
  refine runs_start_le ?_
  unfold initProjectEmit
  refine runs_seq_assign_le (v := labelWord label) (Expr.eval_load_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hL) hl) ?_
  cases label with
  | none =>
    refine runs_cond_le (v := 0) (Expr.eval_reg_of_eq rfl) (fun h => (h rfl).elim) ?_
    intro _
    refine runs_ret_le (v := dst) (Expr.eval_reg_of_eq rfl) ⟨L, O, dst, rfl, rfl, ?_, ?_⟩ ?_
    · simp [initProjectEntry, ListAt]
    · exact fun _ _ => rfl
    · simp [initProjectEmitContract, Expr.size]
  | some k =>
    refine runs_cond_le (v := k + 1) (Expr.eval_reg_of_eq rfl) ?_ (by omega)
    intro _
    let x := if verts then owner u else k
    have hd : dst + 1 < 2 ^ w := by simpa [initProjectEntry] using hroom
    refine runs_seq_store_le (x := dst) (v := x) (Expr.eval_reg_of_eq rfl) ?_ ?_
    · cases verts
      · exact Expr.eval_eq_of_eq
          (Expr.eval_sub (Expr.eval_reg_of_eq (v := k + 1) rfl) (Expr.eval_const h1) hlw)
          (Nat.add_sub_cancel k 1)
      · exact Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hO) ho
    refine runs_ret_le (v := dst + 1)
      (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) hd)
      ⟨L, O, dst, rfl, rfl, ?_, ?_⟩ ?_
    · change ListAt (Function.update mem dst x) dst (x :: [])
      exact listAt_cons.mpr ⟨Function.update_self .., by simp [ListAt]⟩
    · intro y hy
      change y < dst ∨ dst + 1 ≤ y at hy
      exact Function.update_of_ne (by omega) _ _
    · cases verts <;> simp [initProjectEmitContract, Expr.size]

/-- The output chunks follow the same terminal sequence as a substitution pass. -/
def initProjectChunk (S : StaticData) (verts : Bool) (u : ℕ) (es : List ℕ) (i : ℕ) :
    List ℕ :=
  initProjectEntry S.owner (S.label es[i]!) verts
    (initFlatTerminal (S.H.host 0 0) u es i)

theorem initProjectPrefix_eq (S : StaticData) (verts : Bool) (u : ℕ) (es : List ℕ) :
    initAppendPrefix (initProjectChunk S verts u es) es.length = initProjectWords S verts u es := by
  induction es generalizing u with
  | nil => rfl
  | cons e es ih =>
    rw [List.length_cons]
    change (List.range (es.length + 1)).flatMap (initProjectChunk S verts u (e :: es)) = _
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    change initProjectEntry S.owner (S.label e) verts u ++
      initAppendPrefix (initProjectChunk S verts (otherEnd (S.H.host 0 0).edges e u) es) es.length =
      _
    rw [ih, initProjectWords]
    cases S.label e <;> rfl

end MinCostFlow.HierPaths

end
