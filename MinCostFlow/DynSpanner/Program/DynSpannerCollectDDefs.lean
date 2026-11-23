module

public import MinCostFlow.DynSpanner.Program.DynSpannerWalkHelpers
public import WordRAM.Logic

/-!
# The set `D` of a step: definitions

After the rebuild of level `j`, Algorithm 6 reports the set
`D = ⋃_{e ∈ E(J̃)} edges(Π_{J→H}(e))` (`step` in `Defs.lean`). The procedure `dsCollectDStmt`
writes this set as a list without repeats. It walks over the edges `e` of a list `es` and over
the edges `x` of the walk `T e`. A stamp array marks the edges already written: the word
`stamp + x` equals the fresh value `g` exactly when `x` is already in the output. So each edge is
written once, and the work is one step per edge of each walk.

This file has the program, the pure list `dList T es` that it computes, and the context of the
proofs. The output list is `addNew [] (es.flatMap fun e => (T e).map Prod.fst)`, where
`addNew acc xs` appends the elements of `xs` that are not yet present.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## The program -/

/-- The address of the edge word of position `r11` of the walk at `r9`. -/
def dsCollectDAddr : Expr :=
  .bin .add (.bin .add (.reg 9) (.const 1)) (.bin .mul (.const 2) (.reg 11))

/-- One edge `x` of the walk: write it if its stamp is not `g`. -/
def dsCollectDInnerStmt : Stmt :=
  .assign 12 (.load dsCollectDAddr) ;;
  .assign 13 (.load (.bin .add (.reg 3) (.reg 12))) ;;
  .cond (.bin .eq (.reg 13) (.reg 4)) .nop
    (.store (.bin .add (.reg 3) (.reg 12)) (.reg 4) ;;
     .store (.bin .add (.reg 5) (.reg 6)) (.reg 12) ;;
     .assign 6 (.bin .add (.reg 6) (.const 1)))

/-- One edge `e` of the list: read the walk `T e` and process its edges. -/
def dsCollectDOuterStmt : Stmt :=
  .assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
  .assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ;;
  .assign 10 (.load (.reg 9)) ;;
  forRange 11 (.const 0) (.reg 10) dsCollectDInnerStmt

/-- `args = [esPtr, esLen, tab, stamp, g, out]`; returns the length of the output. -/
def dsCollectDStmt : Stmt :=
  .assign 6 (.const 0) ;;
  forRange 7 (.const 0) (.reg 1) dsCollectDOuterStmt ;;
  .ret (.reg 6)

def collectDProcs : List Stmt := [dsCollectDStmt]

def collectDIdx : ℕ := 0

lemma collectDProcs_noRand : ∀ s ∈ collectDProcs, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## The list that the program computes -/

/-- Append the elements of `xs` that are not in the list yet, in order. -/
def addNew (acc xs : List ℕ) : List ℕ :=
  xs.foldl (fun a x => if x ∈ a then a else a ++ [x]) acc

lemma addNew_nil (acc : List ℕ) : addNew acc [] = acc := rfl

lemma addNew_append (acc xs ys : List ℕ) : addNew acc (xs ++ ys) = addNew (addNew acc xs) ys := by
  simp only [addNew, List.foldl_append]

lemma addNew_singleton (acc : List ℕ) (x : ℕ) :
    addNew acc [x] = if x ∈ acc then acc else acc ++ [x] := rfl

lemma mem_addNew (acc xs : List ℕ) (x : ℕ) : x ∈ addNew acc xs ↔ x ∈ acc ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => simp [addNew_nil]
  | cons y ys ih =>
    rw [show y :: ys = [y] ++ ys from rfl, addNew_append, ih, addNew_singleton]
    split_ifs with hy
    · simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hy
        · exact Or.inr h
    · simp only [List.mem_append, List.mem_singleton]
      tauto

lemma nodup_addNew {acc : List ℕ} (h : acc.Nodup) (xs : List ℕ) : (addNew acc xs).Nodup := by
  induction xs generalizing acc with
  | nil => exact h
  | cons y ys ih =>
    rw [show y :: ys = [y] ++ ys from rfl, addNew_append]
    refine ih ?_
    rw [addNew_singleton]
    split_ifs with hy
    · exact h
    · exact List.nodup_append.mpr ⟨h, List.nodup_singleton y, by simp; exact fun a ha h => hy (h ▸ ha)⟩

lemma length_addNew_le (acc xs : List ℕ) : (addNew acc xs).length ≤ acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => simp [addNew_nil]
  | cons y ys ih =>
    rw [show y :: ys = [y] ++ ys from rfl, addNew_append]
    refine (ih _).trans ?_
    rw [addNew_singleton]
    split_ifs <;> simp; omega

/-- The edges of the walks of the list `es`, each once, in order of first appearance. -/
def dList (T : Embedding) (es : List ℕ) : List ℕ :=
  addNew [] (es.flatMap fun e => (T e).map Prod.fst)

lemma dList_succ (T : Embedding) (es : List ℕ) (i : ℕ) (hi : i < es.length) :
    dList T (es.take (i + 1)) = addNew (dList T (es.take i)) ((T es[i]).map Prod.fst) := by
  simp only [dList, List.take_succ_eq_append_getElem hi, List.flatMap_append, addNew_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

lemma mem_dList (T : Embedding) (es : List ℕ) (x : ℕ) :
    x ∈ dList T es ↔ ∃ e ∈ es, x ∈ walkEdges (T e) := by
  simp [dList, mem_addNew, walkEdges]

lemma dList_nodup (T : Embedding) (es : List ℕ) : (dList T es).Nodup :=
  nodup_addNew List.nodup_nil _

/-- For a list `es` of the edges of `J̃`, the output is the set `D` of `step`. -/
lemma dList_toFinset (T : Embedding) (es : List ℕ) :
    (dList T es).toFinset = es.toFinset.biUnion fun e => walkEdges (T e) := by
  ext x
  simp [mem_dList]

/-- The total length of the walks of `es`, a bound on the output. -/
def dTotal (T : Embedding) (es : List ℕ) : ℕ := (es.map fun e => (T e).length).sum

lemma dTotal_succ (T : Embedding) (es : List ℕ) (i : ℕ) (hi : i < es.length) :
    dTotal T (es.take (i + 1)) = dTotal T (es.take i) + (T es[i]).length := by
  simp only [dTotal, List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

lemma dTotal_take_le (T : Embedding) (es : List ℕ) (i : ℕ) :
    dTotal T (es.take i) ≤ dTotal T es := by
  simp only [dTotal]
  nth_rewrite 2 [← List.take_append_drop i es]
  rw [List.map_append, List.sum_append]
  omega

lemma length_dList_le (T : Embedding) (es : List ℕ) : (dList T es).length ≤ dTotal T es := by
  have h := length_addNew_le [] (es.flatMap fun e => (T e).map Prod.fst)
  simp only [List.length_nil, zero_add, List.length_flatMap, List.length_map] at h
  simpa [dTotal, dList] using h

/-- The output after the first `i` edges of `es` and the first `k` edges of the walk of
`es[i]`. -/
def dAcc (T : Embedding) (es : List ℕ) (i k : ℕ) (hi : i < es.length) : List ℕ :=
  addNew (dList T (es.take i)) (((T es[i]).map Prod.fst).take k)

lemma dAcc_zero (T : Embedding) (es : List ℕ) (i : ℕ) (hi : i < es.length) :
    dAcc T es i 0 hi = dList T (es.take i) := by
  simp [dAcc, addNew_nil]

lemma dAcc_len (T : Embedding) (es : List ℕ) (i : ℕ) (hi : i < es.length) :
    dAcc T es i (T es[i]).length hi = dList T (es.take (i + 1)) := by
  rw [dList_succ T es i hi, dAcc]
  congr 1
  exact List.take_of_length_le (by simp)

lemma dAcc_succ (T : Embedding) (es : List ℕ) (i k : ℕ) (hi : i < es.length)
    (hk : k < (T es[i]).length) :
    dAcc T es i (k + 1) hi = addNew (dAcc T es i k hi) [((T es[i])[k]).1] := by
  simp only [dAcc]
  rw [← addNew_append]
  congr 1
  rw [List.take_succ_eq_append_getElem (by simpa using hk), List.getElem_map]

lemma length_dAcc_le (T : Embedding) (es : List ℕ) (i k : ℕ) (hi : i < es.length) :
    (dAcc T es i k hi).length ≤ dTotal T (es.take i) + k := by
  have h1 := length_addNew_le (dList T (es.take i)) (((T es[i]).map Prod.fst).take k)
  have h2 := length_dList_le T (es.take i)
  simp only [dAcc, List.length_take] at h1 ⊢
  omega

/-! ## The context of the proofs -/

/-- The data and the precondition of `dsCollectDStmt`. -/
structure DCtx where
  w : ℕ
  eCap : ℕ
  T : Embedding
  es : List ℕ
  esPtr : ℕ
  tab : ℕ
  stamp : ℕ
  g : ℕ
  out : ℕ
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  hesB : esPtr + es.length < 2 ^ w
  htB : tab + eCap < 2 ^ w
  hsB : stamp + eCap < 2 ^ w
  hoB : out + dTotal T es < 2 ^ w
  hg : g < 2 ^ w
  dSE : IvlDisj stamp eCap esPtr es.length
  dST : IvlDisj stamp eCap tab eCap
  dOE : IvlDisj out (dTotal T es) esPtr es.length
  dOT : IvlDisj out (dTotal T es) tab eCap
  dOS : IvlDisj out (dTotal T es) stamp eCap
  hes : ListAt mem0 esPtr es
  hk : ∀ k (hk : k < es.length), es[k] < eCap ∧
    MWalkAt mem0 (mem0 (tab + es[k])) (T es[k]) ∧
    mem0 (tab + es[k]) + (2 * (T es[k]).length + 1) < 2 ^ w ∧
    IvlDisj stamp eCap (mem0 (tab + es[k])) (2 * (T es[k]).length + 1) ∧
    IvlDisj out (dTotal T es) (mem0 (tab + es[k])) (2 * (T es[k]).length + 1) ∧
    ∀ y ∈ T es[k], y.1 < eCap
  hstamp : ∀ x < eCap, mem0 (stamp + x) < g

/-- The facts that hold whenever the output is `acc`: the registers of the arguments, the
counter `r6`, the output, the stamps, and the frame. -/
def DState (c : DCtx) (acc : List ℕ) (st : State) : Prop :=
  st.regs 0 = c.esPtr ∧ st.regs 1 = c.es.length ∧ st.regs 2 = c.tab ∧ st.regs 3 = c.stamp ∧
  st.regs 4 = c.g ∧ st.regs 5 = c.out ∧ st.regs 6 = acc.length ∧
  ListAt st.mem c.out acc ∧
  (∀ x < c.eCap, (x ∈ acc → st.mem (c.stamp + x) = c.g) ∧
    (x ∉ acc → st.mem (c.stamp + x) = c.mem0 (c.stamp + x))) ∧
  ∀ addr, (addr < c.stamp ∨ c.stamp + c.eCap ≤ addr) →
    (addr < c.out ∨ c.out + dTotal c.T c.es ≤ addr) → st.mem addr = c.mem0 addr

/-- Contract of `dsCollectDStmt`. -/
def dsCollectDContract (c : DCtx) : Contract where
  pre args mem := args = [c.esPtr, c.es.length, c.tab, c.stamp, c.g, c.out] ∧ mem = c.mem0
  post _ mem ret mem' :=
    ret = (dList c.T c.es).length ∧ ListAt mem' c.out (dList c.T c.es) ∧
    (∀ x < c.eCap, (x ∈ dList c.T c.es → mem' (c.stamp + x) = c.g) ∧
      (x ∉ dList c.T c.es → mem' (c.stamp + x) = mem (c.stamp + x))) ∧
    ∀ addr, (addr < c.stamp ∨ c.stamp + c.eCap ≤ addr) →
      (addr < c.out ∨ c.out + dTotal c.T c.es ≤ addr) → mem' addr = mem addr
  cost _ _ := 50 * dTotal c.T c.es + 50 * c.es.length + 20

end

end MinCostFlow.DynSpanner.Program
