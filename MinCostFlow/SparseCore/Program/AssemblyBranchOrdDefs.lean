module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRead
public import MinCostFlow.SparseCore.Program.OutEditsModel
public import MinCostFlow.SparseCore.Program.OrdStoreCapContract

/-!
# Readout `5` of a branch: the program and its tools (`AssemblyBranchOrdDefs`)

Readout `5` of a branch writes the output order `tr.outOrder ord` (`OrdListAt`): one record
`[v, len, keys…]` for each vertex `v` of `S_cur`. The list at `v` is the list of the tour at `v`
restricted to the ends of `S_cur` (`outOrder_eq_filter`), which is what the tour lists as its
marked ends (`asmBr_markedList_eq`). So the program walks the vertex list of the output graph
(`DynGraphAt`) and, for each vertex, writes `v` and asks the tour for its marked list right after
it (`asmBrReadOrdStmt`).

The contract gives readout `5` exactly the words of its output as space. So the listing must
write its list and nothing else. This is operation `9` of the tour contract (`tourContract`,
P2), whose space bound is `3 + |out|`, with space exactly `1 + |out|` and without growing the
cells of the tour. The interface `AsmBrTourListAt` states it; the tour piece must meet it.

This file has the interface, the program, the records predicate `AsmBrRecsAt` with its reading
lemma, and a loop rule with a potential that depends on a ghost value (`asmBr_runs_loop_ghost`):
the concrete state of the tour changes at each call, and its potential pays for the call.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.SparseCore.Program.Read

/-! ## The listing operation of the tour -/

/-- **Interface of the listing of marked ends (P2, `tourContract` operation `9`).** For every
caps `vCap`, `eCap`, procedure `f` of `p`, called as `[tourH, r, h]` on the tour family `TR`
with `r < vCap`, writes the marked ends of the list at `r` (`OutTourAbs.markedList`) at `h` in
`EndListAt` form, returns `h + 1 + |list|`, keeps the abstract state, writes below `h` only in
the cells of the tour, does not grow these cells, and costs at most
`mul · (|list| + 1) · ordStoreLog eCap` against the potential of the tour. The handle of the
tour is one of its cells (`handle_foot`), so it lies below the heap pointer. -/
structure AsmBrTourListAt (TR : ℕ → ℕ → DSRep OutTourAbs) (w : ℕ) (p : Program) (f mul : ℕ) :
    Prop where
  handle_foot : ∀ (vCap eCap tourH : ℕ) (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH
  runs : ∀ (vCap eCap tourH r h : ℕ) (s : OutTourAbs) (tx : (TR vCap eCap).τ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      tourH < 2 ^ w → r < vCap → h < 2 ^ w →
      (TR vCap eCap).rep tourH s tx mem → (∀ a, (TR vCap eCap).foot tourH tx a → a < h) →
      ZeroFrom mem h → h + 1 + (s.markedList r).length < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c tx',
        Runs w p ω body (startState [tourH, r, h] mem pos) o st' c ∧
        (TR vCap eCap).rep tourH s tx' st'.mem ∧
        EndListAt st'.mem h (s.markedList r) ∧
        o.value = h + 1 + (s.markedList r).length ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ (TR vCap eCap).foot tourH tx a → st'.mem a = mem a) ∧
        (∀ a, (TR vCap eCap).foot tourH tx' a → (TR vCap eCap).foot tourH tx a) ∧
        c + (TR vCap eCap).phi tourH tx' st'.mem ≤
          mul * ((s.markedList r).length + 1) * ordStoreLog eCap +
            (TR vCap eCap).phi tourH tx mem

/-! ## The program -/

/-- The address of vertex `i` of the vertex list of the graph at register `3` with vertex cap at
register `4` and counter at register `8`: `g + 4 + vCap + i` (`dgVListBase`). -/
def asmBrOrdVertexExpr : Expr :=
  .load (.bin .add (.bin .add (.bin .add (.reg 3) (.const 4)) (.reg 4)) (.reg 8))

/-- One round of readout `5`: read vertex `v` number `i` of the output graph, write it at the
cursor (register `7`), and let the tour list its marked ends right after it; the cursor becomes
the returned heap pointer. -/
def asmBrOrdBody (fList : ℕ) : Stmt :=
  .assign 9 asmBrOrdVertexExpr ;;
  .store (.reg 7) (.reg 9) ;;
  .call 7 fList [.reg 6, .reg 9, .bin .add (.reg 7) (.const 1)] ;;
  .assign 8 (.bin .add (.reg 8) (.const 1))

/-- The loop test of readout `5`: the counter is below the number of vertices. -/
def asmBrOrdTest : Expr := .bin .lt (.reg 8) (.reg 5)

/-- **Readout `5` of a branch**, `[b, h]`. Read the output graph `g` (its handle at `b + 2`),
its vertex cap and its vertex count `n`, and the tour handle (at `b + 3`). Write the pointer
`h + 1` at `h` and the count `n` at `h + 1`. Then for each vertex of the vertex list of `g`, write
the vertex and its list of marked ends. Return the cursor. -/
def asmBrReadOrdStmt (fList : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const ASM_BR_OUT))) ;;
  .assign 3 (.load (.reg 2)) ;;
  .assign 4 (.load (.reg 3)) ;;
  .assign 5 (.load (.bin .add (.reg 3) (.const 2))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const ASM_BR_TOUR))) ;;
  .store (.reg 1) (.bin .add (.reg 1) (.const 1)) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.reg 5) ;;
  .assign 7 (.bin .add (.reg 1) (.const 2)) ;;
  .assign 8 (.const 0) ;;
  .loop asmBrOrdTest (asmBrOrdBody fList) ;;
  .ret (.reg 7)

/-- Readout `5` never reads random bits. -/
theorem asmBrReadOrdStmt_noRand (fList : ℕ) : (asmBrReadOrdStmt fList).NoRand := by
  simp [asmBrReadOrdStmt, asmBrOrdBody, Stmt.NoRand]

/-! ## Records written one after the other -/

/-- The records `[v, len, keys…]` of `recs`, written one after the other from `a`. -/
def AsmBrRecsAt (mem : ℕ → ℕ) : ℕ → List (ℕ × List End) → Prop
  | _, [] => True
  | a, (v, xs) :: rest =>
    mem a = v ∧ EndListAt mem (a + 1) xs ∧ AsmBrRecsAt mem (a + 2 + xs.length) rest

/-- The list `xs` read back from its `EndListAt` form. -/
theorem endListAt_readList {mem : ℕ → ℕ} {a : ℕ} {xs : List End} (h : EndListAt mem a xs) :
    (readList mem (a + 1) (mem a)).map endOfKey = xs := by
  obtain ⟨hlen, hkeys⟩ := h
  rw [hlen]
  apply List.ext_getElem
  · simp [readList]
  · intro i h1 h2
    simp only [readList, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply]
    rw [hkeys i h2, endOfKey_endKey, List.getD_eq_getElem _ _ h2]

/-- Records written one after the other are read back by `readOrdRecords`. -/
theorem AsmBrRecsAt.readOrdRecords_eq {mem : ℕ → ℕ} :
    ∀ {a : ℕ} {recs : List (ℕ × List End)}, AsmBrRecsAt mem a recs →
      readOrdRecords mem recs.length a = recs
  | _, [], _ => rfl
  | a, (v, xs) :: rest, ⟨hv, hxs, hrest⟩ => by
    have hlen : mem (a + 1) = xs.length := hxs.1
    have hread := endListAt_readList hxs
    rw [hlen] at hread
    simp only [List.length_cons, readOrdRecords, hv, hlen, AsmBrRecsAt.readOrdRecords_eq hrest]
    rw [show a + 2 = a + 1 + 1 by omega, hread]

/-- Records keep their values when the memory agrees on their words. -/
theorem AsmBrRecsAt.of_agree {mem mem' : ℕ → ℕ} :
    ∀ {a : ℕ} {recs : List (ℕ × List End)}, AsmBrRecsAt mem a recs →
      (∀ c, a ≤ c → c < a + ordRecordsWords recs → mem' c = mem c) → AsmBrRecsAt mem' a recs
  | _, [], _, _ => trivial
  | a, (v, xs) :: rest, ⟨hv, hxs, hrest⟩, hag => by
    have hw : ordRecordsWords ((v, xs) :: rest) = 2 + xs.length + ordRecordsWords rest := by
      simp [ordRecordsWords, Nat.add_assoc]
    rw [hw] at hag
    refine ⟨(hag a le_rfl (by omega)).trans hv, ⟨?_, fun i hi => ?_⟩,
      AsmBrRecsAt.of_agree hrest fun c h1 h2 => hag c (by omega) (by omega)⟩
    · rw [hag (a + 1) (by omega) (by omega)]; exact hxs.1
    · rw [hag (a + 1 + 1 + i) (by omega) (by omega)]; exact hxs.2 i hi

/-- One more record after the records of `recs`. -/
theorem AsmBrRecsAt.append {mem : ℕ → ℕ} {v : ℕ} {xs : List End} :
    ∀ {a : ℕ} {recs : List (ℕ × List End)}, AsmBrRecsAt mem a recs →
      mem (a + ordRecordsWords recs) = v → EndListAt mem (a + ordRecordsWords recs + 1) xs →
      AsmBrRecsAt mem a (recs ++ [(v, xs)])
  | a, [], _, hv, hxs => by
    simp only [ordRecordsWords, List.map_nil, List.sum_nil, Nat.add_zero] at hv hxs
    exact ⟨hv, hxs, trivial⟩
  | a, (u, ys) :: rest, ⟨hu, hys, hrest⟩, hv, hxs => by
    have hw : a + ordRecordsWords ((u, ys) :: rest) =
        a + 2 + ys.length + ordRecordsWords rest := by
      simp [ordRecordsWords]; omega
    rw [hw] at hv hxs
    exact ⟨hu, hys, AsmBrRecsAt.append hrest hv hxs⟩

/-- The words of the records grow by `2 + |xs|` with one more record. -/
theorem ordRecordsWords_append (recs : List (ℕ × List End)) (v : ℕ) (xs : List End) :
    ordRecordsWords (recs ++ [(v, xs)]) = ordRecordsWords recs + (2 + xs.length) := by
  simp [ordRecordsWords]

/-! ## A loop rule with a ghost potential -/

/-- **Loop rule with a potential that depends on a ghost value** (the concrete state of a piece
called in the body). As `runs_loop_pot`, with the invariant, the post and the potential indexed
by a value `g` that each step may change. -/
theorem asmBr_runs_loop_ghost {γ : Type} {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr}
    {body : Stmt} {Inv Q : γ → State → Prop} {m rem condVal : State → ℕ}
    {pot : γ → State → ℕ}
    (hcond : ∀ g st, Inv g st → e.eval w st = some (condVal st))
    (hexit : ∀ g st, Inv g st → condVal st = 0 → Q g st ∧ e.size + 1 ≤ rem st)
    (hstep : ∀ g st, Inv g st → condVal st ≠ 0 → ∃ st' c g',
      Runs w p ω body st .normal st' c ∧ Inv g' st' ∧ m st' < m st ∧
      e.size + c + rem st' + pot g' st' + 1 ≤ rem st + pot g st) :
    ∀ g st, Inv g st → ∃ st' c g', Runs w p ω (.loop e body) st .normal st' c ∧ Q g' st' ∧
      c + pot g' st' ≤ rem st + pot g st := by
  suffices h : ∀ k g st, m st ≤ k → Inv g st → ∃ st' c g',
      Runs w p ω (.loop e body) st .normal st' c ∧ Q g' st' ∧ c + pot g' st' ≤ rem st + pot g st
    from fun g st hInv => h (m st) g st le_rfl hInv
  intro k
  induction k with
  | zero =>
    intro g st hm hInv
    by_cases hv : condVal st = 0
    · obtain ⟨hq, hrem⟩ := hexit g st hInv hv
      exact ⟨st, e.size + 1, g, runs_loop_iff.mpr (Or.inl ⟨hv ▸ hcond g st hInv, rfl, rfl, rfl⟩),
        hq, by omega⟩
    · obtain ⟨st₁, c₁, g₁, -, -, hm₁, -⟩ := hstep g st hInv hv
      omega
  | succ k ih =>
    intro g st hm hInv
    by_cases hv : condVal st = 0
    · obtain ⟨hq, hrem⟩ := hexit g st hInv hv
      exact ⟨st, e.size + 1, g, runs_loop_iff.mpr (Or.inl ⟨hv ▸ hcond g st hInv, rfl, rfl, rfl⟩),
        hq, by omega⟩
    · obtain ⟨st₁, c₁, g₁, hr₁, hInv₁, hm₁, hc₁⟩ := hstep g st hInv hv
      obtain ⟨st₂, c₂, g₂, hr₂, hq₂, hc₂⟩ := ih g₁ st₁ (by omega) hInv₁
      exact ⟨st₂, e.size + c₁ + c₂ + 1, g₂, runs_loop_iff.mpr
        (Or.inr (Or.inr ⟨condVal st, st₁, c₁, c₂, hcond g st hInv, hv, hr₁, hr₂, rfl⟩)), hq₂,
        by omega⟩

/-! ## The marked lists are the output lists -/

/-- When the tour marks exactly the ends of `S_cur` (`OutMarksOf`), the marked list at `v` is the
output list at `v`. -/
theorem asmBr_markedList_eq {L : ℕ} {s : OutTourAbs} {tr : BundleTreeState L}
    {ord : ℕ → List End} (h : OutMarksOf s (outCoreOrder tr ord) tr.S_cur.E) (v : ℕ) :
    s.markedList v = tr.outOrder ord v := by
  classical
  obtain ⟨hcord, hmarked⟩ := h
  rw [outOrder_eq_filter, OutTourAbs.markedList, hcord]
  refine List.filter_congr fun z hz => ?_
  have hiff : z ∈ s.marked ↔ z.1 ∈ tr.S_cur.E := by
    rw [hmarked]
    exact ⟨fun h => h.2, fun h => ⟨⟨v, hz⟩, h⟩⟩
  simp only [hiff]

end MinCostFlow.SparseCore.Program
