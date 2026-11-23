module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitCompMath
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import MinCostFlow.Expander.BfsCompProg
import all MinCostFlow.Expander.BfsCompProg
import MinCostFlow.Spanner.PathDSContract
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The map from vertices to components at the init (`AssemblyFirstInitComp`)

The bundle side of a branch keeps an array from vertices to the index of their component
(`AsmSdMapsAt`, `AssemblyBranchSide.lean`). This file writes that array for a graph `G` in its
memory form (`DynGraphAt`).

The procedure `compMapBody` works in four steps.
1. It writes `G` as a plain graph on the positions `0, …, n - 1` of its vertex list `vL`: the
   edge `e` becomes the pair of the positions of its two ends (`dynCited`,
   `AssemblyFirstInitCompMath.lean`). The position of a vertex is in the memory form of `G`.
2. It calls the verified adjacency builder (`buildCsrProc`) on this graph.
3. It calls the verified breadth-first search (`bfsLabelsProc`). The search gives each position a
   label, and two positions get the same label exactly when their vertices are connected.
4. It walks the positions in order and numbers the labels in the order they first appear. A
   table `first` from labels to numbers (plus one, and `0` for a label not seen yet) does this in
   one pass. It stores the number of the label of position `x` at `cmpH + vL[x]`.

So the index of a component is the number of representatives (first positions of a label) before
its own representative (`repRank`, `AssemblyFirstInitCompMath.lean`), and the list of the
components is `compList G vL lab n`. The main result is `compMap_runs`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program MinCostFlow.LSF
open MinCostFlow.Expander MinCostFlow.Spanner

/-! ## The procedure -/

/-- One step of the first loop: register `17` holds the index `i`, and the edge `e = eL[i]` goes
to register `18`. The positions of its tail and head go to registers `19` and `20`: the slot of
the end, then its name, then the position of the name. They are stored at `heap + 2 + 2 i` and
`heap + 3 + 2 i`. -/
def compCitedStep : Stmt :=
  .assign 18 (.load (.bin .add (.reg 10) (.reg 17))) ;;
  .assign 19 (.load (.bin .add (.reg 11) (.reg 18))) ;;
  .assign 19 (.load (.bin .add (.reg 9) (.reg 19))) ;;
  .assign 19 (.load (.bin .add (.reg 8) (.reg 19))) ;;
  .assign 20 (.load (.bin .add (.reg 12) (.reg 18))) ;;
  .assign 20 (.load (.bin .add (.reg 9) (.reg 20))) ;;
  .assign 20 (.load (.bin .add (.reg 8) (.reg 20))) ;;
  .store (.bin .add (.reg 13) (.bin .mul (.const 2) (.reg 17))) (.reg 19) ;;
  .store (.bin .add (.bin .add (.reg 13) (.const 1)) (.bin .mul (.const 2) (.reg 17))) (.reg 20)

/-- One step of the second loop: register `17` holds the position `x`, register `23` the number
of labels seen so far. Let `l` be the label of `x` and `f = first[l]`. When `f = 0` the label is
new: the count goes up by one and `first[l]` becomes the count. Then `cmpH + vL[x]` gets
`first[l] - 1`. -/
def compDenseStep : Stmt :=
  .assign 24 (.load (.bin .add (.reg 16) (.reg 17))) ;;
  .assign 25 (.load (.bin .add (.reg 21) (.reg 24))) ;;
  .assign 26 (.bin .eq (.reg 25) (.const 0)) ;;
  .assign 23 (.bin .add (.reg 23) (.reg 26)) ;;
  .assign 25 (.bin .add (.reg 25) (.bin .mul (.reg 26) (.reg 23))) ;;
  .store (.bin .add (.reg 21) (.reg 24)) (.reg 25) ;;
  .assign 24 (.load (.bin .add (.reg 7) (.reg 17))) ;;
  .store (.bin .add (.reg 1) (.reg 24)) (.bin .sub (.reg 25) (.const 1))

/-- The part of the procedure after the addresses are set: the two loops and the two calls. -/
def compMapTail (fCsr fBfs : ℕ) : Stmt :=
  forRange 17 (.const 0) (.reg 6) compCitedStep ;;
  .store (.reg 2) (.reg 5) ;;
  .store (.bin .add (.reg 2) (.const 1)) (.reg 6) ;;
  .call 22 fCsr [.reg 2, .reg 14] ;;
  .call 22 fBfs [.reg 5, .reg 6, .reg 14, .reg 15, .reg 16] ;;
  .assign 23 (.const 0) ;;
  forRange 17 (.const 0) (.reg 5) compDenseStep ;;
  .ret (.reg 23)

/-- **The map from vertices to components**, `[graph, cmpH, heap]`. Registers: `3 = vCap`,
`4 = eCap`, `5 = n`, `6 = m`, then the starts of the vertex list (`7`), the positions (`8`), the
names of the slots (`9`), the edge list (`10`), the tail slots (`11`) and the head slots (`12`)
of `G`. From `heap`: the plain graph (`2 + 2 m` words, edges from `13`), the adjacency arrays
(`14`, `2 n + 1 + 4 m` words), the queue (`15`), the labels (`16`) and the table `first` (`21`),
`n` words each. It returns the number of components. -/
def compMapBody (fCsr fBfs : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 7 (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 3)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 3)) ;;
  .assign 9 (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 3))) ;;
  .assign 10 (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 3) (.reg 3))) (.reg 4)) ;;
  .assign 11 (.bin .add (.reg 10) (.bin .mul (.const 2) (.reg 4))) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 4)) ;;
  .assign 13 (.bin .add (.reg 2) (.const 2)) ;;
  .assign 14 (.bin .add (.reg 13) (.bin .mul (.const 2) (.reg 6))) ;;
  .assign 15 (.bin .add (.bin .add (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 5)))
    (.const 1)) (.bin .mul (.const 4) (.reg 6))) ;;
  .assign 16 (.bin .add (.reg 15) (.reg 5)) ;;
  .assign 21 (.bin .add (.reg 16) (.reg 5)) ;;
  compMapTail fCsr fBfs

/-- The module: the procedure, then the adjacency builder and the search. -/
def compMapModule (b : ℕ) : List Stmt :=
  [compMapBody (b + 1) (b + 2), buildCsrProc, bfsLabelsProc]

theorem compMapBody_noRand (fCsr fBfs : ℕ) : (compMapBody fCsr fBfs).NoRand := by
  simp [compMapBody, compMapTail, compCitedStep, compDenseStep, forRange, forUp, Stmt.NoRand]

/-- The scratch memory of the procedure, from `heap`: `5 n + 6 m + 3` words. -/
def compMapSpace (n m : ℕ) : ℕ := 5 * n + 6 * m + 3

/-- The cost bound of the procedure. -/
def compMapCost (n m : ℕ) : ℕ := 500 * (n + m) + 700

/-! ## The first loop: the plain graph on the positions -/

/-- **The first loop** writes the edges of the plain graph on the positions: for the edge
`eL[j]`, the positions of its tail and head at `heap + 2 + 2 j` and `heap + 3 + 2 j`. The registers
below `17` and above `20` do not change, nor the memory outside these cells. -/
theorem compCited_loop {w : ℕ} {p : Program} {mem : ℕ → ℕ} {graph vCap eCap heap : ℕ}
    {G : MGraph} {vL eL : List ℕ} (R : ℕ → ℕ)
    (hGval : G.IsValid) (hVlt : ∀ v ∈ G.V, v < vCap)
    (hvMem : ∀ v, v ∈ vL ↔ v ∈ G.V)
    (hvPos : ∀ i (hi : i < vL.length), mem (dgVPosBase graph vCap + vL[i]) = i)
    (hext : ∀ v ∈ G.V, mem (dgExtToIntBase graph vCap + v) ∈ G.V ∧
      mem (dgIntToExtBase graph vCap + mem (dgExtToIntBase graph vCap + v)) = v)
    (heMem : ∀ e, e ∈ eL ↔ e ∈ G.E) (heLA : ListAt mem (dgEListBase graph vCap eCap) eL)
    (hslot : ∀ e ∈ G.E,
      mem (dgETailSlotBase graph vCap eCap + e) = mem (dgExtToIntBase graph vCap + G.tail e) ∧
      mem (dgEHeadSlotBase graph vCap eCap + e) = mem (dgExtToIntBase graph vCap + G.head e))
    (hElt : ∀ e ∈ G.E, e < eCap) (hmE : eL.length ≤ eCap)
    (hGle : graph + dynGraphSize vCap eCap ≤ heap)
    (hw : heap + 2 + 2 * eL.length < 2 ^ w)
    (hR6 : R 6 = eL.length) (hR8 : R 8 = graph + 4 + 2 * vCap)
    (hR9 : R 9 = graph + 4 + 4 * vCap) (hR10 : R 10 = graph + 4 + 7 * vCap + eCap)
    (hR11 : R 11 = graph + 4 + 7 * vCap + 3 * eCap)
    (hR12 : R 12 = graph + 4 + 7 * vCap + 4 * eCap) (hR13 : R 13 = heap + 2) :
    Triple w p (fun st => st.mem = mem ∧ ∀ r, r < 17 ∨ 20 < r → st.regs r = R r)
      (forRange 17 (.const 0) (.reg 6) compCitedStep)
      (normalPost fun st => (∀ r, r < 17 ∨ 20 < r → st.regs r = R r) ∧
        (∀ a, (a < heap + 2 ∨ heap + 2 + 2 * eL.length ≤ a) → st.mem a = mem a) ∧
        ∀ j (hj : j < eL.length), st.mem (heap + 2 + 2 * j) = vL.idxOf (G.tail eL[j]) ∧
          st.mem (heap + 3 + 2 * j) = vL.idxOf (G.head eL[j]))
      (fun _ => eL.length * 120 + 10) := by
  set m := eL.length with hm
  have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ r, r < 17 ∨ 20 < r → st.regs r = R r) ∧ st.regs 17 = i ∧
    (∀ a, (a < heap + 2 ∨ heap + 2 + 2 * m ≤ a) → st.mem a = mem a) ∧
    ∀ j (hj : j < m), j < i → st.mem (heap + 2 + 2 * j) = vL.idxOf (G.tail eL[j]) ∧
      st.mem (heap + 3 + 2 * j) = vL.idxOf (G.head eL[j])
  -- the position of a vertex, read through its slot
  have hpos : ∀ v ∈ G.V, mem (dgVPosBase graph vCap + v) = vL.idxOf v := by
    intro v hv
    have hlt := List.idxOf_lt_length_of_mem ((hvMem v).mpr hv)
    have := hvPos _ hlt
    rwa [List.getElem_idxOf hlt] at this
  -- one step of the loop
  have hstep : ∀ i, 0 ≤ i → i < m →
      Triple w p (Inv i) compCitedStep
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 17 (i + 1) } ∧
            st₁.regs 17 = i)
        (fun _ => 110) := by
    intro i _ hi st ω' hI
    obtain ⟨hR, r17, hfr, hcells⟩ := hI
    have r8 : st.regs 8 = graph + 4 + 2 * vCap := (hR 8 (by omega)).trans hR8
    have r9 : st.regs 9 = graph + 4 + 4 * vCap := (hR 9 (by omega)).trans hR9
    have r10 : st.regs 10 = graph + 4 + 7 * vCap + eCap := (hR 10 (by omega)).trans hR10
    have r11 : st.regs 11 = graph + 4 + 7 * vCap + 3 * eCap := (hR 11 (by omega)).trans hR11
    have r12 : st.regs 12 = graph + 4 + 7 * vCap + 4 * eCap := (hR 12 (by omega)).trans hR12
    have r13 : st.regs 13 = heap + 2 := (hR 13 (by omega)).trans hR13
    have hiL : i < eL.length := hi
    set e := eL[i] with he_def
    have heG : e ∈ G.E := (heMem e).mp (List.getElem_mem hiL)
    have heC := hElt e heG
    have htV := (hGval e heG).1
    have hhV := (hGval e heG).2
    have htlt := hVlt _ htV
    have hhlt := hVlt _ hhV
    obtain ⟨hst, hsh⟩ := hslot e heG
    obtain ⟨hsV_t, hnm_t⟩ := hext _ htV
    obtain ⟨hsV_h, hnm_h⟩ := hext _ hhV
    set sT := mem (dgExtToIntBase graph vCap + G.tail e) with hsT
    set sH := mem (dgExtToIntBase graph vCap + G.head e) with hsH
    have hslt_t : sT < vCap := hVlt _ hsV_t
    have hslt_h : sH < vCap := hVlt _ hsV_h
    have hlow : ∀ a, a < heap → st.mem a = mem a := fun a ha => hfr a (Or.inl (by omega))
    have h1 : st.mem (graph + 4 + 7 * vCap + eCap + i) = e := by
      rw [hlow _ (by omega)]; exact heLA i hiL
    have h2 : st.mem (graph + 4 + 7 * vCap + 3 * eCap + e) = sT := by
      rw [hlow _ (by omega)]; exact hst
    have h3 : st.mem (graph + 4 + 4 * vCap + sT) = G.tail e := by
      rw [hlow _ (by omega)]; exact hnm_t
    have h4 : st.mem (graph + 4 + 2 * vCap + G.tail e) = vL.idxOf (G.tail e) := by
      rw [hlow _ (by omega)]; exact hpos _ htV
    have h5 : st.mem (graph + 4 + 7 * vCap + 4 * eCap + e) = sH := by
      rw [hlow _ (by omega)]; exact hsh
    have h6 : st.mem (graph + 4 + 4 * vCap + sH) = G.head e := by
      rw [hlow _ (by omega)]; exact hnm_h
    have h7 : st.mem (graph + 4 + 2 * vCap + G.head e) = vL.idxOf (G.head e) := by
      rw [hlow _ (by omega)]; exact hpos _ hhV
    refine runs_start_le ?_
    unfold compCitedStep
    refine runs_seq_assign_le (v := e) (Expr.eval_load_of_eq (by eval_expr) h1) ?_
    refine runs_seq_assign_le (v := sT) (Expr.eval_load_of_eq (by eval_expr) h2) ?_
    refine runs_seq_assign_le (v := G.tail e) (Expr.eval_load_of_eq (by eval_expr) h3) ?_
    refine runs_seq_assign_le (v := vL.idxOf (G.tail e))
      (Expr.eval_load_of_eq (by eval_expr) h4) ?_
    refine runs_seq_assign_le (v := sH) (Expr.eval_load_of_eq (by eval_expr) h5) ?_
    refine runs_seq_assign_le (v := G.head e) (Expr.eval_load_of_eq (by eval_expr) h6) ?_
    refine runs_seq_assign_le (v := vL.idxOf (G.head e))
      (Expr.eval_load_of_eq (by eval_expr) h7) ?_
    refine runs_seq_store_le (x := heap + 2 + 2 * i) (v := vL.idxOf (G.tail e))
      (Expr.eval_eq_of_eq (by eval_expr) (by omega)) (by eval_expr) ?_
    refine runs_store_le (x := heap + 3 + 2 * i) (v := vL.idxOf (G.head e))
      (Expr.eval_eq_of_eq (by eval_expr) (by omega)) (by eval_expr) ?_ ?_
    · refine ⟨⟨fun r hr => ?_, by simp, fun a ha => ?_, fun j hj hji => ?_⟩, by simp [r17]⟩
      · have h17 : r ≠ 17 := by omega
        have h18 : r ≠ 18 := by omega
        have h19 : r ≠ 19 := by omega
        have h20 : r ≠ 20 := by omega
        simp [h17, h18, h19, h20, hR r hr]
      · dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr a ha
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hji with hlt | rfl
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hcells j hj hlt
        · refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_self]
          · rw [show heap + 3 + 2 * j = heap + 3 + 2 * j from rfl, Function.update_self]
    · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, Expr.size_const]
      omega
  -- the loop
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 17) (lo := .const 0) (hi := .reg 6)
    (body := compCitedStep)
    (P := fun st => st.mem = mem ∧ ∀ r, r < 17 ∨ 20 < r → st.regs r = R r)
    (Inv := Inv) 110 0 m (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hP => ⟨Expr.eval_const (by omega), fun r hr => by
        simp [show r ≠ 17 by omega, hP.2 r hr], by simp,
      fun a _ => by simp [hP.1], fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.1 6 (by omega)).trans hR6)) hstep
  refine (hloop.conseq (fun st h => h) ?_ ?_)
  · intro o st' hQ
    cases o with
    | returned _ => exact hQ
    | normal =>
      obtain ⟨hR, -, hfr, hcells⟩ := hQ
      exact ⟨hR, hfr, fun j hj => hcells j hj hj⟩
  · intro st _
    simp only [Expr.size_reg, Expr.size_const]
    omega

/-! ## The second loop: numbers in the order of first appearance -/

theorem repRank_le (lab : ℕ → ℕ) (x : ℕ) : repRank lab x ≤ x := by
  unfold repRank repList
  exact (List.length_filter_le _ _).trans (by simp)

/-- The invariant of the second loop after `x` positions, for the labels `lab`, the table
`first` at `root + n` and the registers `R` (see `compDense_loop`). -/
def CompDenseInv (m2 : ℕ → ℕ) (cmpH vCap n root : ℕ) (vL : List ℕ) (lab R : ℕ → ℕ) (x : ℕ)
    (st : State) : Prop :=
  (∀ r, r < 17 ∨ r = 21 → st.regs r = R r) ∧ st.regs 17 = x ∧ st.regs 23 = repRank lab x ∧
  (∀ a, (a < cmpH ∨ cmpH + vCap ≤ a) → (a < root + n ∨ root + 2 * n ≤ a) →
    st.mem a = m2 a) ∧
  (∀ l < n, (∀ y < x, lab y ≠ l) → st.mem (root + n + l) = 0) ∧
  (∀ r < x, isRep lab r = true → st.mem (root + n + lab r) = repRank lab r + 1) ∧
  (∀ y < x, ∀ r ≤ y, isRep lab r = true → lab r = lab y →
    st.mem (cmpH + vL.getD y 0) = repRank lab r) ∧
  (∀ v < vCap, st.mem (cmpH + v) ≤ n)

/-- One step of the second loop keeps `CompDenseInv`. -/
theorem compDense_step {w : ℕ} {p : Program} {m2 : ℕ → ℕ} {cmpH vCap n root : ℕ}
    {vL : List ℕ} (lab : ℕ → ℕ) (R : ℕ → ℕ)
    (hvNd : vL.Nodup) (hvlen : vL.length = n) (hvlt : ∀ v ∈ vL, v < vCap)
    (hvLA : ListAt m2 (R 7) vL) (hR7 : R 7 + n ≤ cmpH)
    (hroot : ∀ x < n, m2 (root + x) = lab x) (hlab : ∀ x < n, lab x < n)
    (hcmp : cmpH + vCap ≤ root) (hw : root + 2 * n < 2 ^ w)
    (hR1 : R 1 = cmpH) (hR16 : R 16 = root) (hR21 : R 21 = root + n) (x : ℕ) (hx : x < n) :
    Triple w p (CompDenseInv m2 cmpH vCap n root vL lab R x) compDenseStep
      (normalPost fun st₁ =>
        CompDenseInv m2 cmpH vCap n root vL lab R (x + 1)
          { st₁ with regs := Function.update st₁.regs 17 (x + 1) } ∧ st₁.regs 17 = x)
      (fun _ => 60) := by
  intro st ω' hI
  obtain ⟨hR, r17, r23, hfr, hB, hC, hD, hE⟩ := hI
  have r1 : st.regs 1 = cmpH := (hR 1 (by omega)).trans hR1
  have r7 : st.regs 7 = R 7 := hR 7 (by omega)
  have r16 : st.regs 16 = root := (hR 16 (by omega)).trans hR16
  have r21 : st.regs 21 = root + n := (hR 21 (by omega)).trans hR21
  have hxL : x < vL.length := by omega
  set v := vL[x] with hv_def
  have hvlt' : v < vCap := hvlt v (List.getElem_mem hxL)
  have hlx := hlab x hx
  obtain ⟨r0, hr0x, hr0rep, hr0lab⟩ := exists_rep lab x
  have hrd1 : st.mem (root + x) = lab x := by
    rw [hfr _ (Or.inr (by omega)) (Or.inl (by omega))]; exact hroot x hx
  set f := st.mem (root + n + lab x) with hf_def
  have hcase : (r0 = x ∧ f = 0 ∧ isRep lab x = true) ∨
      (r0 < x ∧ f = repRank lab r0 + 1 ∧ isRep lab x = false) := by
    rcases Nat.lt_or_eq_of_le hr0x with hlt | heq
    · right
      refine ⟨hlt, ?_, ?_⟩
      · rw [hf_def, ← hr0lab]; exact hC r0 hlt hr0rep
      · cases h : isRep lab x
        · rfl
        · exact absurd hr0lab (isRep_iff.mp h r0 hlt)
    · left
      have hxr : isRep lab x = true := heq ▸ hr0rep
      exact ⟨heq, hB _ hlx (fun y hy => isRep_iff.mp hxr y hy), hxr⟩
  have hrr0 := repRank_le lab r0
  have hrrx := repRank_le lab (x + 1)
  have ht : repRank lab x + (if f = 0 then 1 else 0) = repRank lab (x + 1) := by
    rw [repRank_succ]
    rcases hcase with ⟨-, hf0, hrep⟩ | ⟨-, hf0, hrep⟩
    · simp [hf0, hrep]
    · simp [hf0, hrep]
  have hf' : f + (if f = 0 then 1 else 0) * repRank lab (x + 1) = repRank lab r0 + 1 := by
    rw [repRank_succ]
    rcases hcase with ⟨rfl, hf0, hrep⟩ | ⟨-, hf0, hrep⟩
    · simp [hf0, hrep]
    · simp [hf0, hrep]
  have hrd2 : Function.update st.mem (root + n + lab x) (repRank lab r0 + 1) (R 7 + x) = v := by
    rw [Function.update_of_ne (by omega), hfr _ (Or.inl (by omega)) (Or.inl (by omega))]
    exact hvLA x hxL
  refine runs_start_le ?_
  unfold compDenseStep
  refine runs_seq_assign_le (v := lab x) (Expr.eval_load_of_eq (by eval_expr) hrd1) ?_
  refine runs_seq_assign_le (v := f) (Expr.eval_load_of_eq (by eval_expr) rfl) ?_
  refine runs_seq_assign_le (v := if f = 0 then 1 else 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := repRank lab (x + 1)) (Expr.eval_eq_of_eq (by eval_expr) ht) ?_
  refine runs_seq_assign_le (v := repRank lab r0 + 1) (Expr.eval_eq_of_eq (by eval_expr) hf') ?_
  refine runs_seq_store_le (x := root + n + lab x) (v := repRank lab r0 + 1) (by eval_expr)
    (by eval_expr) ?_
  refine runs_seq_assign_le (v := v) (Expr.eval_load_of_eq (by eval_expr) hrd2) ?_
  refine runs_store_le (x := cmpH + v) (v := repRank lab r0) (by eval_expr)
    (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_ ?_
  · refine ⟨⟨fun r hr => ?_, by simp, by simp, fun a ha1 ha2 => ?_, fun l hl hly => ?_,
      fun r hr hrep => ?_, fun y hy r hry hrep hlr => ?_, fun v' hv' => ?_⟩, by simp [r17]⟩
    · have h17 : r ≠ 17 := by omega
      have h23 : r ≠ 23 := by omega
      have h24 : r ≠ 24 := by omega
      have h25 : r ≠ 25 := by omega
      have h26 : r ≠ 26 := by omega
      simp [h17, h23, h24, h25, h26, hR r hr]
    · dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr a ha1 ha2
    · dsimp only
      have hl' : l ≠ lab x := fun h => hly x (by omega) h.symm
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hB l hl fun y hy => hly y (by omega)
    · dsimp only
      rw [Function.update_of_ne (by have := hlab r (by omega); omega)]
      by_cases hl : lab r = lab x
      · have hrr : r = r0 := rep_unique hrep hr0rep (hl.trans hr0lab.symm)
        rw [hl, Function.update_self, hrr]
      · have hrx : r < x := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h | h
          · exact h
          · exact absurd (congrArg lab h) hl
        rw [Function.update_of_ne (by omega)]
        exact hC r hrx hrep
    · dsimp only
      rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hlt | rfl
      · have hyL : y < vL.length := by omega
        have hne : vL.getD y 0 ≠ v := by
          rw [List.getD_eq_getElem _ _ hyL, hv_def]
          intro h
          exact absurd ((hvNd.getElem_inj_iff).mp h) (by omega)
        have hylt : vL.getD y 0 < vCap := by
          rw [List.getD_eq_getElem _ _ hyL]; exact hvlt _ (List.getElem_mem hyL)
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hD y hlt r hry hrep hlr
      · have hrr : r = r0 := rep_unique hrep hr0rep (hlr.trans hr0lab.symm)
        rw [List.getD_eq_getElem _ _ hxL, ← hv_def, Function.update_self, hrr]
    · dsimp only
      by_cases hvv : v' = v
      · rw [hvv, Function.update_self]; omega
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hE v' hv'
  · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, Expr.size_const]
    omega

/-- **The second loop** numbers the labels `lab x` of the positions `x < n` in the order of
first appearance, with the table `first` at `root + n`, and stores at `cmpH + vL[y]` the number
`repRank lab r` of the representative `r` of the label of `y`. The registers below `17` and
register `21` do not change; the memory changes only at `cmpH + v` for `v < vCap` and in the
table. Afterwards register `23` holds the number of labels, and the cells at `cmpH` are at most
`n`. -/
theorem compDense_loop {w : ℕ} {p : Program} {m2 : ℕ → ℕ} {cmpH vCap n root : ℕ}
    {vL : List ℕ} (lab : ℕ → ℕ) (R : ℕ → ℕ)
    (hvNd : vL.Nodup) (hvlen : vL.length = n) (hvlt : ∀ v ∈ vL, v < vCap)
    (hvLA : ListAt m2 (R 7) vL) (hR7 : R 7 + n ≤ cmpH)
    (hroot : ∀ x < n, m2 (root + x) = lab x) (hlab : ∀ x < n, lab x < n)
    (hcmp : cmpH + vCap ≤ root)
    (hz : ∀ l < n, m2 (root + n + l) = 0) (hzc : ∀ v < vCap, m2 (cmpH + v) = 0)
    (hw : root + 2 * n < 2 ^ w) (hw4 : 4 ≤ 2 ^ w)
    (hR1 : R 1 = cmpH) (hR5 : R 5 = n) (hR16 : R 16 = root) (hR21 : R 21 = root + n) :
    Triple w p
      (fun st => st.mem = m2 ∧ (∀ r, r < 17 ∨ r = 21 → st.regs r = R r) ∧ st.regs 23 = 0)
      (forRange 17 (.const 0) (.reg 5) compDenseStep)
      (normalPost fun st => st.regs 23 = repRank lab n ∧
        (∀ a, (a < cmpH ∨ cmpH + vCap ≤ a) → (a < root + n ∨ root + 2 * n ≤ a) →
          st.mem a = m2 a) ∧
        (∀ y < n, ∀ r ≤ y, isRep lab r = true → lab r = lab y →
          st.mem (cmpH + vL.getD y 0) = repRank lab r) ∧
        (∀ v < vCap, st.mem (cmpH + v) ≤ n))
      (fun _ => n * 100 + 10) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 17) (lo := .const 0) (hi := .reg 5)
    (body := compDenseStep)
    (P := fun st => st.mem = m2 ∧ (∀ r, r < 17 ∨ r = 21 → st.regs r = R r) ∧ st.regs 23 = 0)
    (Inv := CompDenseInv m2 cmpH vCap n root vL lab R) 60 0 n (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun st hP => ⟨Expr.eval_const (by omega), fun r hr => by
        simp [show r ≠ 17 by omega, hP.2.1 r hr], by simp,
      by simp [hP.2.2, repRank, repList], fun a _ _ => by simp [hP.1],
      fun l hl _ => by simp [hP.1, hz l hl], fun r hr => absurd hr (Nat.not_lt_zero _),
      fun y hy => absurd hy (Nat.not_lt_zero _), fun v hv => by simp [hP.1, hzc v hv]⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.1 5 (by omega)).trans hR5))
    (fun x _ hx => compDense_step lab R hvNd hvlen hvlt hvLA hR7 hroot hlab hcmp hw hR1 hR16 hR21
      x hx)
  refine (hloop.conseq (fun st h => h) ?_ ?_)
  · intro o st' hQ
    cases o with
    | returned _ => exact hQ
    | normal =>
      obtain ⟨-, -, r23, hfr, -, -, hD, hE⟩ := hQ
      exact ⟨r23, hfr, hD, hE⟩
  · intro st _
    simp only [Expr.size_reg, Expr.size_const]
    omega

/-! ## The whole procedure -/

/-- **What the map gives**, for the list `comps` of the components of `G`, the memory `mem`
before and `mem'` after: `comps` names each component of `G` once; the cell `cmpH + v` holds the
index of the component of `v`; the cells at `cmpH` below `vCap` hold words; the memory below
`cmpH` and from `cmpH + vCap` below `heap` does not change; and the memory is fresh after the
scratch. -/
def CompMapPost (w : ℕ) (G : MGraph) (vCap cmpH heap : ℕ) (mem mem' : ℕ → ℕ)
    (comps : List (Finset ℕ)) : Prop :=
  comps.Nodup ∧ (∀ C, C ∈ comps ↔ C ∈ components G) ∧
  (∀ c (hc : c < comps.length), ∀ v ∈ comps[c], mem' (cmpH + v) = c) ∧
  (∀ v < vCap, mem' (cmpH + v) < 2 ^ w) ∧ (∀ a < cmpH, mem' a = mem a) ∧
  (∀ a, cmpH + vCap ≤ a → a < heap → mem' a = mem a) ∧
  ZeroFrom mem' (heap + compMapSpace G.n G.m)

private theorem length_le_of_nodup {L : List ℕ} {cap : ℕ} (hnd : L.Nodup)
    (hlt : ∀ x ∈ L, x < cap) : L.length ≤ cap := by
  calc L.length = L.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (Finset.range cap).card := Finset.card_le_card fun x hx =>
        Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
    _ = cap := Finset.card_range cap

/-- **The front of the procedure**: the first loop writes the plain graph on the positions, then
the procedure stores its header and calls the adjacency builder and the search. Afterwards the
registers below `17` and register `21` are as before, the memory below `heap` and from the end of
the labels is as before, and the labels at `root = heap + 2 + 2m + 2n + 1 + 4m + n` are the labels
of a search of the plain graph. The rest `s` of the procedure continues from there. -/
theorem compMapFront_runs {w b : ℕ} {p : Program} (hp : p.HasAt b (compMapModule b))
    (ω : ℕ → Bool) {graph heap vCap eCap : ℕ} {G : MGraph} {mem : ℕ → ℕ} {st : State}
    {vL eL : List ℕ}
    (hGval : G.IsValid) (hVlt : ∀ v ∈ G.V, v < vCap) (hElt : ∀ e ∈ G.E, e < eCap)
    (hvLen : vL.length = G.n) (hvMem : ∀ v, v ∈ vL ↔ v ∈ G.V)
    (hvPos : ∀ i (hi : i < vL.length), mem (dgVPosBase graph vCap + vL[i]) = i)
    (hext : ∀ v ∈ G.V, mem (dgExtToIntBase graph vCap + v) ∈ G.V ∧
      mem (dgIntToExtBase graph vCap + mem (dgExtToIntBase graph vCap + v)) = v)
    (heLen : eL.length = G.m) (heMem : ∀ e, e ∈ eL ↔ e ∈ G.E)
    (heLA : ListAt mem (dgEListBase graph vCap eCap) eL)
    (hslot : ∀ e ∈ G.E,
      mem (dgETailSlotBase graph vCap eCap + e) = mem (dgExtToIntBase graph vCap + G.tail e) ∧
      mem (dgEHeadSlotBase graph vCap eCap + e) = mem (dgExtToIntBase graph vCap + G.head e))
    (hmE : eL.length ≤ eCap) (hGle : graph + dynGraphSize vCap eCap ≤ heap)
    (hsp : heap + (5 * G.n + 6 * G.m + 3) < 2 ^ w) (hw4 : 4 ≤ 2 ^ w) (hmem : st.mem = mem)
    (r2 : st.regs 2 = heap) (r5 : st.regs 5 = G.n) (r6 : st.regs 6 = G.m)
    (r8 : st.regs 8 = graph + 4 + 2 * vCap) (r9 : st.regs 9 = graph + 4 + 4 * vCap)
    (r10 : st.regs 10 = graph + 4 + 7 * vCap + eCap)
    (r11 : st.regs 11 = graph + 4 + 7 * vCap + 3 * eCap)
    (r12 : st.regs 12 = graph + 4 + 7 * vCap + 4 * eCap) (r13 : st.regs 13 = heap + 2)
    (r14 : st.regs 14 = heap + 2 + 2 * G.m)
    (r15 : st.regs 15 = heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m)
    (r16 : st.regs 16 = heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n)
    {s : Stmt} {Q : Outcome → State → Prop} {k T : ℕ}
    (hrest : ∀ st2 : State, (∀ r, r < 17 ∨ r = 21 → st2.regs r = st.regs r) →
      (∀ a, (a < heap ∨ heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + 2 * G.n ≤ a) →
        st2.mem a = mem a) →
      (∀ x < G.n, st2.mem (heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n + x) < G.n) →
      Cited.partsOf (dynCited G.n vL eL G) ((List.range G.n).map fun x =>
          st2.mem (heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n + x)) =
        Cited.partsOf (dynCited G.n vL eL G) (compLabels (dynCited G.n vL eL G)) →
      ∃ o st' c, Runs w p ω s st2 o st' c ∧ Q o st' ∧
        k + (360 * G.n + 420 * G.m + 300) + c ≤ T) :
    ∃ o st' c, Runs w p ω (forRange 17 (.const 0) (.reg 6) compCitedStep ;;
      .store (.reg 2) (.reg 5) ;; .store (.bin .add (.reg 2) (.const 1)) (.reg 6) ;;
      .call 22 (b + 1) [.reg 2, .reg 14] ;;
      .call 22 (b + 2) [.reg 5, .reg 6, .reg 14, .reg 15, .reg 16] ;; s) st o st' c ∧
      Q o st' ∧ k + c ≤ T := by
  have hCsrAt : p.HasAt (b + 1) [buildCsrProc] :=
    Num.hasAt_append_left (ys := [bfsLabelsProc])
      (Num.hasAt_append_right (xs := [compMapBody (b + 1) (b + 2)]) hp)
  have hBfsAt : p.HasAt (b + 2) [bfsLabelsProc] :=
    Num.hasAt_append_right (xs := [compMapBody (b + 1) (b + 2), buildCsrProc]) hp
  have hGcn : (dynCited G.n vL eL G).n = G.n := rfl
  have hGcm : (dynCited G.n vL eL G).m = G.m := by simp [dynCited, Cited.Graph.m, heLen]
  have hGcV : (dynCited G.n vL eL G).IsValid := dynCited_isValid hGval hvLen hvMem heMem
  -- the first loop
  refine runs_seq_triple_le (compCited_loop (w := w) (p := p) (R := st.regs) hGval hVlt hvMem hvPos
    hext heMem heLA hslot hElt hmE hGle (by omega) (r6.trans heLen.symm) r8 r9 r10 r11 r12
    r13) ⟨hmem, fun r _ => rfl⟩ ?_
  rintro st1 ⟨hR1, hfr1, hcells1⟩
  have s2 : st1.regs 2 = heap := (hR1 2 (by omega)).trans r2
  have s5 : st1.regs 5 = G.n := (hR1 5 (by omega)).trans r5
  have s6 : st1.regs 6 = G.m := (hR1 6 (by omega)).trans r6
  have s14 : st1.regs 14 = heap + 2 + 2 * G.m := (hR1 14 (by omega)).trans r14
  have s15 : st1.regs 15 = heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m :=
    (hR1 15 (by omega)).trans r15
  have s16 : st1.regs 16 = heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n :=
    (hR1 16 (by omega)).trans r16
  clear r2 r5 r6 r8 r9 r10 r11 r12 r13 r14 r15 r16 hmem hvPos hext hslot heLA hElt hVlt hGle hmE
  -- the header of the plain graph
  refine runs_seq_store_le (x := heap) (v := G.n) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := heap + 1) (v := G.m) (by eval_expr) (by eval_expr) ?_
  have hGcAt : GraphAt (Function.update (Function.update st1.mem heap G.n) (heap + 1) G.m) heap
      (dynCited G.n vL eL G) := by
    refine graphAt_of_cells ?_ ?_ ?_
    · rw [Function.update_of_ne (by omega), Function.update_self, hGcn]
    · rw [Function.update_self, hGcm]
    · intro j hj
      have hjm : j < eL.length := by rw [heLen]; rw [hGcm] at hj; exact hj
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      obtain ⟨c1, c2⟩ := hcells1 j hjm
      simp only [dynCited, List.getElem_map]
      exact ⟨c1, c2⟩
  have hread := graphAt_iff_readGraph.mp hGcAt
  -- the adjacency arrays
  refine runs_seq_call_le (buildCsr_spec hCsrAt) (vs := [heap, heap + 2 + 2 * G.m])
    (by eval_expr) (by wram_words) ⟨heap, heap + 2 + 2 * G.m, dynCited G.n vL eL G, rfl, hGcAt,
      hGcV, by rw [graph_encode_length, hGcm]; omega, by rw [hGcn, hGcm]; omega, hw4⟩ ?_
  intro v1 memC pos1 hpost1
  have hpost1' : HasCsrAt memC (heap + 2 + 2 * G.m) (dynCited G.n vL eL G) ∧
      MemFrame (Function.update (Function.update st1.mem heap G.n) (heap + 1) G.m) memC
        (heap + 2 + 2 * G.m) (heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m) := by
    have h := hpost1.2
    change HasCsrAt memC (heap + 2 + 2 * G.m) (Cited.readGraph _ heap) ∧
      MemFrame _ memC (heap + 2 + 2 * G.m) (heap + 2 + 2 * G.m +
        2 * (Cited.readGraph _ heap).n + 1 + 4 * (Cited.readGraph _ heap).m) at h
    rw [hread, hGcn, hGcm] at h
    exact h
  obtain ⟨hcsrAt, hframeC⟩ := hpost1'
  -- the search
  have hpreB : (bfsLabelsContract w).pre [G.n, G.m, heap + 2 + 2 * G.m,
      heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m,
      heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n] memC := by
    dsimp only [bfsLabelsContract]
    exact ⟨G.n, G.m, heap + 2 + 2 * G.m, heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m,
      heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n, dynCited G.n vL eL G, rfl, hGcn, hGcm,
      hGcV, hcsrAt, Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), by omega,
      by omega, by omega, hw4⟩
  refine runs_seq_call_le (bfsLabels_spec w p (b + 2) hBfsAt)
    (vs := [G.n, G.m, heap + 2 + 2 * G.m, heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m,
      heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n]) (by eval_expr) (by wram_words) hpreB ?_
  intro v2 m2 pos2 hpost2
  have hpost2' : (bfsLabelsContract w).post [G.n, G.m, heap + 2 + 2 * G.m,
      heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m,
      heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n] memC v2 m2 := hpost2
  dsimp only [bfsLabelsContract] at hpost2'
  obtain ⟨hframeB, hlabAll⟩ := hpost2'
  obtain ⟨-, hlablt, hparts⟩ := hlabAll (dynCited G.n vL eL G) hGcn hGcm hGcV hcsrAt
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hframeB hlablt hparts
  have hR2 : ∀ r, r < 17 ∨ r = 21 → (Function.update (Function.update st1.regs 22 v1) 22 v2) r =
      st.regs r := by
    intro r hr
    have h22 : r ≠ 22 := by omega
    rw [Function.update_of_ne h22, Function.update_of_ne h22]
    exact hR1 r (by omega)
  have hM2 : ∀ a, (a < heap ∨ heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + 2 * G.n ≤ a) →
      m2 a = mem a := by
    intro a ha
    rw [hframeB a (by omega) (by omega), hframeC a (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hfr1 a (by omega)
  obtain ⟨o, st', c, hr, hq, hc⟩ :=
    hrest ⟨m2, Function.update (Function.update st1.regs 22 v1) 22 v2, pos2⟩ hR2 hM2 hlablt hparts
  refine ⟨o, st', c, hr, hq, ?_⟩
  have hcC : (buildCsrContract w).cost [heap, heap + 2 + 2 * G.m]
      (Function.update (Function.update st1.mem heap G.n) (heap + 1) G.m) =
        200 * (G.n + G.m + 1) := by
    show 200 * ((Cited.readGraph _ heap).n + (Cited.readGraph _ heap).m + 1) = _
    rw [hread, hGcn, hGcm]
  have hcB : (bfsLabelsContract w).cost [G.n, G.m, heap + 2 + 2 * G.m,
      heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m,
      heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n] memC = 152 * G.n + 92 * G.m + 40 := rfl
  simp only [Expr.size_reg, Expr.size_bin, Expr.size_const, argsSize_cons, argsSize_nil, hcC,
    hcB, heLen]
  omega

/-- **The run of the map from vertices to components.** Let `G` be in memory form at `graph`,
below `cmpH`, with `cmpH + vCap ≤ heap`, and let the memory be fresh from `cmpH`. Then the
procedure returns the number of components of `G`, and afterwards there is a list `comps` of the
components of `G` with `CompMapPost`. The cost is at most `compMapCost G.n G.m`. -/
theorem compMap_runs {w b : ℕ} {p : Program} (hp : p.HasAt b (compMapModule b))
    (ω : ℕ → Bool) {pos graph cmpH heap vCap eCap : ℕ} {G : MGraph} {mem : ℕ → ℕ}
    (hG : DynGraphAt mem graph vCap eCap G) (hGle : graph + dynGraphSize vCap eCap ≤ cmpH)
    (hcmp : cmpH + vCap ≤ heap) (hz : ZeroFrom mem cmpH)
    (hsp : heap + compMapSpace G.n G.m < 2 ^ w) (hw4 : 4 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω (compMapBody (b + 1) (b + 2))
        (startState [graph, cmpH, heap] mem pos) o st' c ∧
      (∃ comps : List (Finset ℕ), o = .returned comps.length ∧
        CompMapPost w G vCap cmpH heap mem st'.mem comps) ∧ c ≤ compMapCost G.n G.m := by
  obtain ⟨hGval, hVlt, hElt, hmVCap, hmECap, hmN, hmM, -, ⟨vL, hvLen, hvNd, hvMem, hvLA, hvPos⟩,
    hext, -, -, ⟨eL, heLen, heNd, heMem, heLA, -⟩, hslot, -⟩ := hG
  have hmV' : mem graph = vCap := by simpa [dgVCapOff] using hmVCap
  have hmE' : mem (graph + 1) = eCap := by simpa [dgECapOff] using hmECap
  have hmN' : mem (graph + 2) = G.n := by simpa [dgNOff] using hmN
  have hmM' : mem (graph + 3) = G.m := by simpa [dgMOff] using hmM
  have hdg : graph + (4 + 7 * vCap + 9 * eCap) ≤ cmpH := hGle
  have hsp' : heap + (5 * G.n + 6 * G.m + 3) < 2 ^ w := hsp
  have hmE : eL.length ≤ eCap := length_le_of_nodup heNd fun e he => hElt e ((heMem e).mp he)
  have hnV : vL.length ≤ vCap := length_le_of_nodup hvNd fun v hv => hVlt v ((hvMem v).mp hv)
  refine runs_start_le ?_
  unfold compMapBody
  refine runs_seq_assign_le (v := vCap) (Expr.eval_load_of_eq (by eval_expr) hmV') ?_
  refine runs_seq_assign_le (v := eCap) (Expr.eval_load_of_eq (by eval_expr) hmE') ?_
  refine runs_seq_assign_le (v := G.n) (Expr.eval_load_of_eq (by eval_expr) hmN') ?_
  refine runs_seq_assign_le (v := G.m) (Expr.eval_load_of_eq (by eval_expr) hmM') ?_
  refine runs_seq_assign_le (v := graph + 4 + vCap) (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := graph + 4 + 2 * vCap)
    (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := graph + 4 + 4 * vCap)
    (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := graph + 4 + 7 * vCap + eCap)
    (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := graph + 4 + 7 * vCap + 3 * eCap)
    (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := graph + 4 + 7 * vCap + 4 * eCap)
    (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := heap + 2) (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := heap + 2 + 2 * G.m)
    (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m)
    (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n)
    (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + 2 * G.n)
    (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  unfold compMapTail
  refine compMapFront_runs hp ω hGval hVlt hElt hvLen hvMem hvPos hext heLen heMem heLA hslot hmE
    (by omega) hsp' hw4 rfl (by simp [startState]) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    fun st2 hR2 hM2 hlablt hparts => ?_
  have r1 : st2.regs 1 = cmpH := by rw [hR2 1 (by omega)]; simp [startState]
  have r5 : st2.regs 5 = G.n := by rw [hR2 5 (by omega)]; simp
  have r7 : st2.regs 7 = graph + 4 + vCap := by rw [hR2 7 (by omega)]; simp
  have r16 : st2.regs 16 = heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n := by
    rw [hR2 16 (by omega)]; simp
  have r21 : st2.regs 21 = heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n + G.n := by
    rw [hR2 21 (by omega)]; simp; omega
  clear hR2
  let lab : ℕ → ℕ := fun x => st2.mem (heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n + x)
  have hLF : LabelFacts G vL lab G.n :=
    ⟨hvNd, hvLen, hvMem, fun x hx y hy =>
      dynCited_lab_iff hGval hvNd hvLen hvMem heMem hparts hx hy⟩
  -- the numbering
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_triple_le (compDense_loop (w := w) (p := p) (m2 := st2.mem) (cmpH := cmpH)
    (vCap := vCap) (n := G.n) (root := heap + 2 + 2 * G.m + 2 * G.n + 1 + 4 * G.m + G.n) lab
    st2.regs hvNd hvLen (fun v hv => hVlt v ((hvMem v).mp hv))
    (fun i hi => by rw [r7, hM2 _ (Or.inl (by omega))]; exact hvLA i hi) (by omega)
    (fun _ _ => rfl) hlablt (by omega)
    (fun l hl => by rw [hM2 _ (Or.inr (by omega))]; exact hz _ (by omega))
    (fun v hv => by rw [hM2 _ (Or.inl (by omega))]; exact hz _ (by omega)) (by omega) hw4
    r1 r5 r16 (by rw [r21])) ⟨rfl, fun r hr => ?_, by simp⟩ ?_
  · have h23 : r ≠ 23 := by omega
    simp only [Function.update_of_ne h23]
  rintro st3 ⟨r23, hfr3, hD3, hE3⟩
  refine runs_ret_le (v := repRank lab G.n) (by eval_expr)
    ⟨compList G vL lab G.n, by rw [compList_length], ?_⟩ ?_
  · refine ⟨compList_nodup hLF, mem_compList_iff hLF,
      fun c hc v hv => compList_map hLF (cmp := fun v => st3.mem (cmpH + v)) hD3 c hc v hv,
      fun v hv => by have := hE3 v hv; omega, fun a ha => ?_, fun a ha1 ha2 => ?_, fun a ha => ?_⟩
    · rw [hfr3 a (Or.inl ha) (Or.inl (by omega))]; exact hM2 a (Or.inl (by omega))
    · rw [hfr3 a (Or.inr ha1) (Or.inl (by omega))]; exact hM2 a (Or.inl ha2)
    · have ha' : heap + (5 * G.n + 6 * G.m + 3) ≤ a := ha
      rw [hfr3 a (Or.inr (by omega)) (Or.inr (by omega)), hM2 a (Or.inr (by omega))]
      exact hz a (by omega)
  · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, Expr.size_const, compMapCost]
    omega

end MinCostFlow.SparseCore.Program
