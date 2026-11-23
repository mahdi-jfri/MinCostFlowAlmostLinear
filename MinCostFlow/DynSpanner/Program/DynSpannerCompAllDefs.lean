module

public import MinCostFlow.DynSpanner.Program.DynSpannerCompDefs

/-!
# Composing the walks of all affected edges: program, contract and invariant

For each affected edge `e`, Algorithm 6 needs the walk `embMid e = Embedding.comp embJH outEmb e`
before re-embedding `e`. The procedure `dsCompAllStmt` gets the affected edges as a list `es`, an
edge-indexed table `qTab` of pointers to the walks `outEmb e` (written by the shortcut procedure)
and an edge-indexed table `tab` of pointers to the walks `embJH x` (written while building `J`).
For each position `k` it calls `dsCompEdgeStmt` with output at the current heap pointer and stores
this pointer at `mpPtr + k`, the table that `dsReembedAllStmt` reads.

The output of edge `es[k]` starts at `compHeapAt … k`, so the pointer table holds exact
addresses. The proof is in `DynSpannerCompAll.lean`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- Loop body of `dsCompAllStmt` for the edge at position `reg 6`. -/
def dsCompAllBodyStmt (bC : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 2) (.reg 6))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
  .call 9 (bC + compIdxEdge) [.reg 8, .reg 1, .reg 5] ;;
  .store (.bin .add (.reg 4) (.reg 6)) (.reg 5) ;;
  .assign 5 (.reg 9)

/-- Compose the walks of all edges of a list (`args = [qTab, tab, esPtr, esLen, mpPtr, heap]`);
returns the final heap pointer. -/
def dsCompAllStmt (bC : ℕ) : Stmt :=
  forRange 6 (.const 0) (.reg 3) (dsCompAllBodyStmt bC) ;;
  .ret (.reg 5)

def compAllProcs (bC : ℕ) : List Stmt := [dsCompAllStmt bC]

def compAllIdx : ℕ := 0

lemma compAllProcs_noRand (bC : ℕ) : ∀ s ∈ compAllProcs bC, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- Words of the output for edge `e`. -/
def compOutLen (T outEmb : Embedding) (e : ℕ) : ℕ :=
  2 * ((outEmb e).flatMap (compPiece T)).length + 1

/-- Heap pointer after the first `i` edges. -/
def compHeapAt (T outEmb : Embedding) (es : List ℕ) (heap i : ℕ) : ℕ :=
  heap + ((es.take i).map (compOutLen T outEmb)).sum

/-- Heap words needed by `dsCompAllStmt`. -/
def compHeapNeed (T outEmb : Embedding) (es : List ℕ) : ℕ :=
  (es.map (compOutLen T outEmb)).sum

/-- Total cost bound of `dsCompAllStmt`. -/
def compAllCost (T outEmb : Embedding) (es : List ℕ) : ℕ :=
  (es.map fun e => 70 * ((outEmb e).flatMap (compPiece T)).length +
    120 * (outEmb e).length + 80).sum + 20

/-- Contract of `dsCompAllStmt`. The walk `outEmb e` is at `mem (qTab + e)` and the walk
`T x` at `mem (tab + x)`. On return position `k` of the table at `mpPtr` holds `compHeapAt … k`,
where the walk `Embedding.comp T outEmb es[k]` is written. -/
def dsCompAllContract (w eCap : ℕ) (T outEmb : Embedding) (es : List ℕ) : Contract where
  pre args mem := ∃ qTab tab esPtr mpPtr heap,
    args = [qTab, tab, esPtr, es.length, mpPtr, heap] ∧ 16 ≤ 2 ^ w ∧
    qTab + eCap < 2 ^ w ∧ tab + eCap < 2 ^ w ∧ esPtr + es.length < 2 ^ w ∧
    mpPtr + es.length < 2 ^ w ∧ heap + compHeapNeed T outEmb es < 2 ^ w ∧
    IvlDisj heap (compHeapNeed T outEmb es) qTab eCap ∧
    IvlDisj heap (compHeapNeed T outEmb es) tab eCap ∧
    IvlDisj heap (compHeapNeed T outEmb es) esPtr es.length ∧
    IvlDisj heap (compHeapNeed T outEmb es) mpPtr es.length ∧
    IvlDisj mpPtr es.length qTab eCap ∧
    IvlDisj mpPtr es.length tab eCap ∧
    IvlDisj mpPtr es.length esPtr es.length ∧
    ListAt mem esPtr es ∧
    (∀ k (hk : k < es.length), es[k] < eCap ∧
      MWalkAt mem (mem (qTab + es[k])) (outEmb es[k]) ∧
      mem (qTab + es[k]) + (2 * (outEmb es[k]).length + 1) < 2 ^ w ∧
      IvlDisj heap (compHeapNeed T outEmb es) (mem (qTab + es[k]))
        (2 * (outEmb es[k]).length + 1) ∧
      IvlDisj mpPtr es.length (mem (qTab + es[k])) (2 * (outEmb es[k]).length + 1) ∧
      ∀ x ∈ outEmb es[k], x.1 < eCap ∧ MWalkAt mem (mem (tab + x.1)) (T x.1) ∧
        mem (tab + x.1) + (2 * (T x.1).length + 1) < 2 ^ w ∧
        IvlDisj heap (compHeapNeed T outEmb es) (mem (tab + x.1)) (2 * (T x.1).length + 1) ∧
        IvlDisj mpPtr es.length (mem (tab + x.1)) (2 * (T x.1).length + 1) ∧
        ∀ y ∈ T x.1, y.1 < eCap)
  post args mem ret mem' := ∃ qTab tab esPtr mpPtr heap,
    args = [qTab, tab, esPtr, es.length, mpPtr, heap] ∧
    (∀ k (hk : k < es.length), mem' (mpPtr + k) = compHeapAt T outEmb es heap k ∧
      MWalkAt mem' (compHeapAt T outEmb es heap k) (Embedding.comp T outEmb es[k])) ∧
    ret = compHeapAt T outEmb es heap es.length ∧
    ∀ addr, (addr < heap ∨ heap + compHeapNeed T outEmb es ≤ addr) →
      (addr < mpPtr ∨ mpPtr + es.length ≤ addr) → mem' addr = mem addr
  cost _ _ := compAllCost T outEmb es

/-! ## Heap pointer facts -/

private lemma sum_take_add_getElem (f : ℕ → ℕ) :
    ∀ (l : List ℕ) (i : ℕ) (hi : i < l.length),
      ((l.take i).map f).sum + f l[i] = ((l.take (i + 1)).map f).sum
  | [], _, hi => by simp at hi
  | x :: l, 0, _ => by simp
  | x :: l, i + 1, hi => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    have := sum_take_add_getElem f l i (by simpa using hi)
    omega

private lemma sum_take_le_sum (f : ℕ → ℕ) :
    ∀ (l : List ℕ) (i : ℕ), ((l.take i).map f).sum ≤ (l.map f).sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: l, i + 1 => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
    exact Nat.add_le_add_left (sum_take_le_sum f l i) _

private lemma sum_take_mono (f : ℕ → ℕ) :
    ∀ (l : List ℕ) (i j : ℕ), i ≤ j → ((l.take i).map f).sum ≤ ((l.take j).map f).sum
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => by simp
  | x :: l, i + 1, 0, h => by omega
  | x :: l, i + 1, j + 1, h => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
    exact Nat.add_le_add_left (sum_take_mono f l i j (by omega)) _

lemma compHeapAt_succ (T outEmb : Embedding) (es : List ℕ) (heap i : ℕ) (hi : i < es.length) :
    compHeapAt T outEmb es heap (i + 1) = compHeapAt T outEmb es heap i + compOutLen T outEmb es[i] := by
  simp only [compHeapAt]
  rw [← sum_take_add_getElem _ es i hi]
  omega

lemma compHeapAt_le_need (T outEmb : Embedding) (es : List ℕ) (heap i : ℕ) :
    compHeapAt T outEmb es heap i ≤ heap + compHeapNeed T outEmb es := by
  have := sum_take_le_sum (compOutLen T outEmb) es i
  simp only [compHeapAt, compHeapNeed]; omega

lemma compHeapAt_mono (T outEmb : Embedding) (es : List ℕ) (heap : ℕ) {i j : ℕ} (h : i ≤ j) :
    compHeapAt T outEmb es heap i ≤ compHeapAt T outEmb es heap j := by
  have := sum_take_mono (compOutLen T outEmb) es i j h
  simp only [compHeapAt]; omega

lemma compHeapAt_all (T outEmb : Embedding) (es : List ℕ) (heap : ℕ) :
    compHeapAt T outEmb es heap es.length = heap + compHeapNeed T outEmb es := by
  simp [compHeapAt, compHeapNeed]

/-! ## Context and invariant -/

/-- The data and the precondition of `dsCompAllContract`, unpacked. -/
structure CACtx where
  w : ℕ
  eCap : ℕ
  T : Embedding
  outEmb : Embedding
  es : List ℕ
  qTab : ℕ
  tab : ℕ
  esPtr : ℕ
  mpPtr : ℕ
  heap : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hqB : qTab + eCap < 2 ^ w
  htB : tab + eCap < 2 ^ w
  hesB : esPtr + es.length < 2 ^ w
  hmpB : mpPtr + es.length < 2 ^ w
  hhB : heap + compHeapNeed T outEmb es < 2 ^ w
  dHQ : IvlDisj heap (compHeapNeed T outEmb es) qTab eCap
  dHT : IvlDisj heap (compHeapNeed T outEmb es) tab eCap
  dHE : IvlDisj heap (compHeapNeed T outEmb es) esPtr es.length
  dHM : IvlDisj heap (compHeapNeed T outEmb es) mpPtr es.length
  dMQ : IvlDisj mpPtr es.length qTab eCap
  dMT : IvlDisj mpPtr es.length tab eCap
  dME : IvlDisj mpPtr es.length esPtr es.length
  hes : ListAt mem0 esPtr es
  hk : ∀ k (hk : k < es.length), es[k] < eCap ∧
    MWalkAt mem0 (mem0 (qTab + es[k])) (outEmb es[k]) ∧
    mem0 (qTab + es[k]) + (2 * (outEmb es[k]).length + 1) < 2 ^ w ∧
    IvlDisj heap (compHeapNeed T outEmb es) (mem0 (qTab + es[k]))
      (2 * (outEmb es[k]).length + 1) ∧
    IvlDisj mpPtr es.length (mem0 (qTab + es[k])) (2 * (outEmb es[k]).length + 1) ∧
    ∀ x ∈ outEmb es[k], x.1 < eCap ∧ MWalkAt mem0 (mem0 (tab + x.1)) (T x.1) ∧
      mem0 (tab + x.1) + (2 * (T x.1).length + 1) < 2 ^ w ∧
      IvlDisj heap (compHeapNeed T outEmb es) (mem0 (tab + x.1)) (2 * (T x.1).length + 1) ∧
      IvlDisj mpPtr es.length (mem0 (tab + x.1)) (2 * (T x.1).length + 1) ∧
      ∀ y ∈ T x.1, y.1 < eCap

/-- Invariant of the loop of `dsCompAllStmt` after `i` edges. -/
def CAInv (c : CACtx) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = c.qTab ∧ st.regs 1 = c.tab ∧ st.regs 2 = c.esPtr ∧ st.regs 3 = c.es.length ∧
  st.regs 4 = c.mpPtr ∧ st.regs 5 = compHeapAt c.T c.outEmb c.es c.heap i ∧ st.regs 6 = i ∧
  (∀ k (hk : k < c.es.length), k < i →
    st.mem (c.mpPtr + k) = compHeapAt c.T c.outEmb c.es c.heap k ∧
    MWalkAt st.mem (compHeapAt c.T c.outEmb c.es c.heap k) (Embedding.comp c.T c.outEmb c.es[k])) ∧
  ∀ addr, (addr < c.heap ∨ c.heap + compHeapNeed c.T c.outEmb c.es ≤ addr) →
    (addr < c.mpPtr ∨ c.mpPtr + c.es.length ≤ addr) → st.mem addr = c.mem0 addr

end

end MinCostFlow.DynSpanner.Program
