module

public import MinCostFlow.DynSpanner.Program.EmbLayouts
public import WordRAM.DataStructure
public import WordRAM.CopyWords
public import WordRAM.Tactic

/-!
# The embedding table of a branch (readout 4)

Readout `4` of the sparse-core contract asks, for a branch, for a table that gives each edge `e`
of the core graph a pointer to an encoding (`MWalkAt`) of its walk `emb e`. The readout costs a
constant, so the table must be kept current on each update and restart of the branch.

The piece here keeps such a table. Its view is `EmbView = ⟨emb, dom⟩`: the walks, and the set of
edges that have a stored walk. It does not know the model. The caller gives it, on each update or
restart of the branch, a change list `X` (`EmbChange`): the edges whose walk changed, or that need
a walk now, each with its new walk. The table then becomes `v.apply X`. The dynamic spanner
reports the edges it re-embeds: the list `rOut` of its update post `DSUpdatePost`. The caller builds `X` from that list.

The memory form:
* the record at `r`: `mem r = r + 2` (the table) and `mem (r + 1) = eCap`;
* the table at `r + 2`, one word per edge name below `eCap`, which points to the walk of the edge
  when the edge is in `dom` (other words are not read);
* the walks, each written once, above the table. A new walk goes to fresh memory at the heap
  pointer, and the old copy is left as garbage.

The operations, all with procedure `copyWords` at `bCopy`:
* `embReadStmt`, `[r, h]`: writes the table pointer and `eCap` at `h`. Cost `10`.
* `embStepStmt bCopy`, `[r, a, n, h]`: applies the `n` entries of the change list at `a`.
* `embInitStmt bCopy`, `[eCap, a, n, h]`: builds the record at `h` and applies the list.
The two last ones cost at most `50 · (embChangeWords X + 1)`, where `embChangeWords X` counts the
words of the input list and of its walks.
-/

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## The view and the change lists -/

/-- The view of the table: the walks `emb`, and the edges `dom` that have a stored walk. -/
structure EmbView where
  emb : Embedding
  dom : Finset ℕ

/-- A change of the table: a list of edges, each with its new walk. Later entries win. -/
abbrev EmbChange := List (ℕ × List (ℕ × Bool))

/-- One entry of a change list, applied to the walks. -/
def embUpd (f : Embedding) (p : ℕ × List (ℕ × Bool)) : Embedding := Function.update f p.1 p.2

/-- The view after a change list. -/
def EmbView.apply (v : EmbView) (X : EmbChange) : EmbView :=
  ⟨X.foldl embUpd v.emb, v.dom ∪ (X.map Prod.fst).toFinset⟩

/-- The empty table. -/
def EmbView.empty : EmbView := ⟨fun _ => [], ∅⟩

/-- The number of words of an encoded walk (`MWalkAt`). -/
def walkWords (P : List (ℕ × Bool)) : ℕ := 1 + 2 * P.length

/-- The words of a change list: two per entry, and the words of each walk. -/
def embChangeWords (X : EmbChange) : ℕ := (X.map fun p => 2 + walkWords p.2).sum

/-- A change list in memory: entry `i` is the two words `mem (a + 2 i) = e` and
`mem (a + 2 i + 1) = q`, with the walk of `e` encoded at `q`. -/
def EmbChangeAt (mem : ℕ → ℕ) (a : ℕ) (X : EmbChange) : Prop :=
  ∀ i (hi : i < X.length), mem (a + 2 * i) = X[i].1 ∧ MWalkAt mem (mem (a + 2 * i + 1)) X[i].2

/-- The input cells of a change list (its `2 n` words and the cells of its walks) lie below `h` and
outside `foot`, and its edges are below `eCap`. -/
def EmbInputAt (mem : ℕ → ℕ) (foot : ℕ → Prop) (a eCap h : ℕ) (X : EmbChange) : Prop :=
  a + 2 * X.length ≤ h ∧ (∀ i < 2 * X.length, ¬ foot (a + i)) ∧
  ∀ i (hi : i < X.length), X[i].1 < eCap ∧ mem (a + 2 * i + 1) + walkWords X[i].2 ≤ h ∧
    ∀ j < walkWords X[i].2, ¬ foot (mem (a + 2 * i + 1) + j)

/-! ## The representation -/

/-- The concrete state: where the walk of each edge is stored, and the view (the footprint needs
the lengths of the walks). -/
structure EmbConc where
  ptr : ℕ → ℕ
  view : EmbView

/-- The record and the table at `r`, and the walks of the edges of `dom`. -/
def EmbRepAt (eCap r : ℕ) (v : EmbView) (ptr : ℕ → ℕ) (mem : ℕ → ℕ) : Prop :=
  mem r = r + 2 ∧ mem (r + 1) = eCap ∧
  ∀ e ∈ v.dom, e < eCap ∧ r + 2 + eCap ≤ ptr e ∧ mem (r + 2 + e) = ptr e ∧
    MWalkAt mem (ptr e) (v.emb e)

/-- The footprint: the record, the table, and the walks of the edges of `dom`. -/
def embFoot (eCap r : ℕ) (y : EmbConc) (a : ℕ) : Prop :=
  (r ≤ a ∧ a < r + 2 + eCap) ∨
    ∃ e ∈ y.view.dom, y.ptr e ≤ a ∧ a < y.ptr e + walkWords (y.view.emb e)

/-- The representation of the table, for edge names below `eCap`. -/
def embRep (eCap : ℕ) : DSRep EmbView where
  τ := EmbConc
  rep r v y mem := y.view = v ∧ EmbRepAt eCap r v y.ptr mem
  phi _ _ _ := 0
  foot := embFoot eCap

/-- What the readout writes at `h`: the table pointer and `eCap`, with the walk of each edge of
`dom`. -/
def ReadEmbOut (mem : ℕ → ℕ) (h eCap : ℕ) (v : EmbView) : Prop :=
  mem (h + 1) = eCap ∧ ∀ e ∈ v.dom, e < eCap ∧ MWalkAt mem (mem (mem h + e)) (v.emb e)

/-- The readout gives the table of readout `4` (`MEmbAt`) for every set of edges in `dom` and
every embedding that agrees with the view there. -/
theorem ReadEmbOut.mEmbAt {mem : ℕ → ℕ} {h eCap : ℕ} {v : EmbView} (hout : ReadEmbOut mem h eCap v)
    {E : Finset ℕ} (hE : E ⊆ v.dom) {emb : Embedding} (hemb : ∀ e ∈ E, v.emb e = emb e) :
    MEmbAt mem (mem h) E (mem (h + 1)) emb := by
  intro e he
  obtain ⟨hlt, hw⟩ := hout.2 e (hE he)
  exact ⟨hout.1 ▸ hlt, hemb e he ▸ hw⟩

/-! ## The procedures -/

/-- `[r, h]`: write the table pointer and `eCap` at `h`, and return `h + 2`. -/
def embReadStmt : Stmt :=
  .store (.reg 1) (.load (.reg 0)) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.load (.bin .add (.reg 0) (.const 1))) ;;
  .ret (.bin .add (.reg 1) (.const 2))

/-- One entry of the change list (register `5` points to it): copy its walk to the heap
(register `7`), and point the table (register `4`) to the copy. Register `6` counts the entries
left. -/
def embLoopBody (bCopy : ℕ) : Stmt :=
  .assign 8 (.load (.reg 5)) ;;
  .assign 9 (.load (.bin .add (.reg 5) (.const 1))) ;;
  .assign 10 (.bin .add (.const 1) (.bin .mul (.const 2) (.load (.reg 9)))) ;;
  .call 11 bCopy [.reg 9, .reg 7, .reg 10] ;;
  .store (.bin .add (.reg 4) (.reg 8)) (.reg 7) ;;
  .assign 7 (.bin .add (.reg 7) (.reg 10)) ;;
  .assign 5 (.bin .add (.reg 5) (.const 2)) ;;
  .assign 6 (.bin .sub (.reg 6) (.const 1))

/-- `[r, a, n, h]`: apply the `n` entries of the change list at `a`, and return the new heap
pointer. -/
def embStepStmt (bCopy : ℕ) : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.reg 1) ;;
  .assign 6 (.reg 2) ;;
  .assign 7 (.reg 3) ;;
  .loop (.reg 6) (embLoopBody bCopy) ;;
  .ret (.reg 7)

/-- `[eCap, a, n, h]`: write the record at `h`, leave the table at `h + 2` (its words are zero and
are not read before they are set), apply the change list, and return the new heap pointer. -/
def embInitStmt (bCopy : ℕ) : Stmt :=
  .store (.reg 3) (.bin .add (.reg 3) (.const 2)) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 0) ;;
  .assign 4 (.bin .add (.reg 3) (.const 2)) ;;
  .assign 5 (.reg 1) ;;
  .assign 6 (.reg 2) ;;
  .assign 7 (.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 0)) ;;
  .loop (.reg 6) (embLoopBody bCopy) ;;
  .ret (.reg 7)

/-- The procedures of the piece, with `copyWords` at `bCopy`: read, step, init. -/
def embProcs (bCopy : ℕ) : List Stmt := [embReadStmt, embStepStmt bCopy, embInitStmt bCopy]

/-! ## Facts on the views -/

/-- The concrete step of one entry: point the edge to the heap, and move the heap past its walk. -/
def embConcStep (s : (ℕ → ℕ) × ℕ) (p : ℕ × List (ℕ × Bool)) : (ℕ → ℕ) × ℕ :=
  (Function.update s.1 p.1 s.2, s.2 + walkWords p.2)

theorem embConcStep_fold_snd (X : EmbChange) (s : (ℕ → ℕ) × ℕ) :
    (X.foldl embConcStep s).2 = s.2 + (X.map fun p => walkWords p.2).sum := by
  induction X generalizing s with
  | nil => simp
  | cons p X ih => simp [ih, embConcStep, Nat.add_assoc]

theorem EmbView.apply_append (v : EmbView) (X Y : EmbChange) :
    v.apply (X ++ Y) = (v.apply X).apply Y := by
  simp only [EmbView.apply, List.foldl_append, List.map_append, List.toFinset_append,
    Finset.union_assoc]

theorem EmbView.apply_singleton (v : EmbView) (p : ℕ × List (ℕ × Bool)) :
    v.apply [p] = ⟨Function.update v.emb p.1 p.2, insert p.1 v.dom⟩ := by
  simp only [EmbView.apply, List.foldl_cons, List.foldl_nil, embUpd, List.map_cons,
    List.map_nil, List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
  congr 1
  ext x
  simp

theorem walkWords_sum_le (X : EmbChange) :
    (X.map fun p => walkWords p.2).sum + 2 * X.length = embChangeWords X := by
  induction X with
  | nil => simp [embChangeWords]
  | cons p X ih =>
    simp only [embChangeWords, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

end

end MinCostFlow.SparseCore.Program.Read
