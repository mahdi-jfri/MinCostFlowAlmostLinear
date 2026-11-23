module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OuterSubgraph
public import MinCostFlow.ExpanderDecomp.OuterProgContracts
import Mathlib.Tactic.Linarith

/-!
# Local Compact-Subgraph Word-RAM Procedures (`OuterProgSubgraphOps`)

Implements and verifies three deterministic (`NoRand`) linear-time Word-RAM procedures on compact
subgraphs `(verts, edges)` using a reusable zero-initialized local-ID table `locAddr` of size `n`
(restored to all zeros on exit, never scanning `range n`):

1. `stripIsolatedProc`: splits `verts` into isolated vertices (immediately labeled with fresh
   unique labels in `labelsAddr` using the counter at `nextLblAddr`) and active vertices written to
   `outActAddr`, matching `CompactSubgraph.stripIsolated` exactly in `O(|verts| + |edges| + 1)`.
2. `restrictProc`: filters `edges` to those with both endpoints in `sVerts`, writing
   `edges.filter (insideB sVerts.toFinset)` at `outEdgesAddr` and returning its length, in
   `O(|sVerts| + |edges| + 1)`.
3. `setDiffProc`: filters `verts` to those not in `rList`, writing the difference list at
   `outRestAddr` and returning its length, in `O(|verts| + |rList| + 1)`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited

/-! ## 1. Reusable `locAddr` Mark / Clear Statements -/

/-- Mark every vertex in `listAddr[0 .. len - 1]` by setting `locAddr[v] := val`.
Uses registers `rLen, rList, rLoc` (read-only) and `rI, rU` (scratch). -/
def markVertsStmt (rLen rList rLoc rI rU val : ℕ) : Stmt :=
  forRange rI (.const 0) (.reg rLen)
    (.assign rU (.load (.bin .add (.reg rList) (.reg rI))) ;;
     .store (.bin .add (.reg rLoc) (.reg rU)) (.const val))

/-- Mark both endpoints of every edge in `edgesAddr[0 .. 2*e - 1]` by setting `locAddr[u] := val`
and `locAddr[v] := val`. Uses `rE, rEdges, rLoc` (read-only) and `rI, rU, rV` (scratch). -/
def markEdgesStmt (rE rEdges rLoc rI rU rV val : ℕ) : Stmt :=
  forRange rI (.const 0) (.reg rE)
    (.assign rU (.load (.bin .add (.reg rEdges) (.bin .mul (.const 2) (.reg rI)))) ;;
     .assign rV (.load (.bin .add (.bin .add (.reg rEdges) (.bin .mul (.const 2) (.reg rI))) (.const 1))) ;;
     .store (.bin .add (.reg rLoc) (.reg rU)) (.const val) ;;
     .store (.bin .add (.reg rLoc) (.reg rV)) (.const val))

/-! ## 2. `stripIsolatedProc` -/

/-- Partition `verts` into isolated vertices (labeled immediately in `labelsAddr` using and
updating `mem[nextLblAddr]`) and active vertices (written to `outActAddr`), returning the active
vertex count. Args: `[k, vertsAddr, e, edgesAddr, locAddr, labelsAddr, nextLblAddr, outActAddr]`. -/
def stripIsolatedProc : Stmt :=
  markEdgesStmt 2 3 4 8 9 10 1 ;;
  .assign 11 (.load (.reg 6)) ;;
  .assign 12 (.const 0) ;;
  forRange 8 (.const 0) (.reg 0)
    (.assign 9 (.load (.bin .add (.reg 1) (.reg 8))) ;;
     .assign 10 (.load (.bin .add (.reg 4) (.reg 9))) ;;
     .cond (.bin .eq (.reg 10) (.const 0))
       (.store (.bin .add (.reg 5) (.reg 9)) (.reg 11) ;;
        .assign 11 (.bin .add (.reg 11) (.const 1)))
       (.store (.bin .add (.reg 7) (.reg 12)) (.reg 9) ;;
        .assign 12 (.bin .add (.reg 12) (.const 1)))) ;;
  .store (.reg 6) (.reg 11) ;;
  markEdgesStmt 2 3 4 8 9 10 0 ;;
  .ret (.reg 12)

/-- Step bound for `stripIsolatedProc`: `O(k + e + 1)`. -/
def stripIsolatedCost (k e : ℕ) : ℕ :=
  60 * k + 120 * e + 80

/-- Word-size bound for `stripIsolatedProc`. -/
def StripIsoWordBound (w n k e vertsAddr edgesAddr locAddr labelsAddr nextLblAddr outActAddr
    nl₀ : ℕ) : Prop :=
  vertsAddr + k < 2 ^ w ∧
  edgesAddr + 2 * e < 2 ^ w ∧
  locAddr + n < 2 ^ w ∧
  labelsAddr + n < 2 ^ w ∧
  nextLblAddr < 2 ^ w ∧
  outActAddr + k < 2 ^ w ∧
  nl₀ + k < 2 ^ w ∧
  16 < 2 ^ w

/-- Buffer disjointness for `stripIsolatedProc`. -/
def StripIsoDisjoint (n k e vertsAddr edgesAddr locAddr labelsAddr nextLblAddr outActAddr : ℕ) :
    Prop :=
  DisjointRange locAddr n vertsAddr k ∧
  DisjointRange locAddr n edgesAddr (2 * e) ∧
  DisjointRange locAddr n labelsAddr n ∧
  DisjointRange locAddr n nextLblAddr 1 ∧
  DisjointRange locAddr n outActAddr k ∧
  DisjointRange labelsAddr n vertsAddr k ∧
  DisjointRange labelsAddr n edgesAddr (2 * e) ∧
  DisjointRange labelsAddr n nextLblAddr 1 ∧
  DisjointRange labelsAddr n outActAddr k ∧
  DisjointRange outActAddr k vertsAddr k ∧
  DisjointRange outActAddr k edgesAddr (2 * e) ∧
  DisjointRange outActAddr k nextLblAddr 1 ∧
  DisjointRange nextLblAddr 1 vertsAddr k ∧
  DisjointRange nextLblAddr 1 edgesAddr (2 * e)

/-- Contract for `stripIsolatedProc`: computes `CompactSubgraph.stripIsolated` exactly, writes
unique labels in `[nl₀, nl₀ + iso.length)` for isolated vertices into `labelsAddr`, updates
`nextLblAddr` to `nl₀ + iso.length`, writes `act.verts` at `outActAddr`, restores `locAddr` to
all zeros, and returns `act.verts.length`. -/
def stripIsolatedContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n k vertsAddr e edgesAddr locAddr labelsAddr nextLblAddr outActAddr : ℕ)
      (verts : List ℕ) (edges : List (ℕ × ℕ)),
      args = [k, vertsAddr, e, edgesAddr, locAddr, labelsAddr, nextLblAddr, outActAddr] ∧
      verts.length = k ∧ verts.Nodup ∧ (∀ u ∈ verts, u < n) ∧
      edges.length = e ∧ (∀ ed ∈ edges, ed.1 < n ∧ ed.2 < n) ∧
      ListAt mem vertsAddr verts ∧
      EdgesAt mem edgesAddr edges ∧
      (∀ u < n, mem (locAddr + u) = 0) ∧
      StripIsoWordBound w n k e vertsAddr edgesAddr locAddr labelsAddr nextLblAddr outActAddr
        (mem nextLblAddr) ∧
      StripIsoDisjoint n k e vertsAddr edgesAddr locAddr labelsAddr nextLblAddr outActAddr
  post args mem v mem' :=
    let k := args.getD 0 0
    let vertsAddr := args.getD 1 0
    let e := args.getD 2 0
    let edgesAddr := args.getD 3 0
    let locAddr := args.getD 4 0
    let labelsAddr := args.getD 5 0
    let nextLblAddr := args.getD 6 0
    let outActAddr := args.getD 7 0
    let verts := readList mem vertsAddr k
    let edges := readEdges mem edgesAddr e
    let res := (CompactSubgraph.mk verts edges).stripIsolated
    let iso := res.1
    let act := res.2
    let nl₀ := mem nextLblAddr
    v = act.verts.length ∧
    ListAt mem' outActAddr act.verts ∧
    mem' nextLblAddr = nl₀ + iso.length ∧
    (∀ u ∈ iso, mem' (labelsAddr + u) = nl₀ + iso.idxOf u) ∧
    (∀ a,
      (∀ u ∈ iso, a ≠ labelsAddr + u) →
      a ≠ nextLblAddr →
      (a < outActAddr ∨ outActAddr + k ≤ a) →
      mem' a = mem a)
  cost args _mem :=
    stripIsolatedCost (args.getD 0 0) (args.getD 2 0)

/-! ## 3. `restrictProc` -/

/-- Filter `edges` to those with both endpoints in `sVerts`, writing them at `outEdgesAddr` and
returning their count. Args: `[kS, sVertsAddr, e, edgesAddr, locAddr, outEdgesAddr]`. -/
def restrictProc : Stmt :=
  markVertsStmt 0 1 4 6 7 1 ;;
  .assign 11 (.const 0) ;;
  forRange 6 (.const 0) (.reg 2)
    (.assign 7 (.load (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 6)))) ;;
     .assign 8 (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 6))) (.const 1))) ;;
     .assign 9 (.load (.bin .add (.reg 4) (.reg 7))) ;;
     .assign 10 (.load (.bin .add (.reg 4) (.reg 8))) ;;
     .cond (.bin .lt (.const 0) (.reg 9))
       (.cond (.bin .lt (.const 0) (.reg 10))
         (.store (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 11))) (.reg 7) ;;
          .store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 11))) (.const 1)) (.reg 8) ;;
          .assign 11 (.bin .add (.reg 11) (.const 1)))
         .nop)
       .nop) ;;
  markVertsStmt 0 1 4 6 7 0 ;;
  .ret (.reg 11)

/-- Step bound for `restrictProc`: `O(kS + e + 1)`. -/
def restrictCost (kS e : ℕ) : ℕ :=
  60 * kS + 90 * e + 80

/-- Contract for `restrictProc`: writes `edges.filter (insideB sVerts.toFinset)` at `outEdgesAddr`
and returns its length, restoring `locAddr` to all zeros and preserving all memory outside
`[outEdgesAddr, outEdgesAddr + 2 * e)`. -/
def restrictContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n kS sVertsAddr e edgesAddr locAddr outEdgesAddr : ℕ)
      (sVerts : List ℕ) (edges : List (ℕ × ℕ)),
      args = [kS, sVertsAddr, e, edgesAddr, locAddr, outEdgesAddr] ∧
      sVerts.length = kS ∧ (∀ u ∈ sVerts, u < n) ∧
      edges.length = e ∧ (∀ ed ∈ edges, ed.1 < n ∧ ed.2 < n) ∧
      ListAt mem sVertsAddr sVerts ∧
      EdgesAt mem edgesAddr edges ∧
      (∀ u < n, mem (locAddr + u) = 0) ∧
      sVertsAddr + kS < 2 ^ w ∧
      edgesAddr + 2 * e < 2 ^ w ∧
      locAddr + n < 2 ^ w ∧
      outEdgesAddr + 2 * e < 2 ^ w ∧
      16 < 2 ^ w ∧
      DisjointRange locAddr n sVertsAddr kS ∧
      DisjointRange locAddr n edgesAddr (2 * e) ∧
      DisjointRange locAddr n outEdgesAddr (2 * e) ∧
      DisjointRange outEdgesAddr (2 * e) sVertsAddr kS ∧
      DisjointRange outEdgesAddr (2 * e) edgesAddr (2 * e)
  post args mem v mem' :=
    let kS := args.getD 0 0
    let sVertsAddr := args.getD 1 0
    let e := args.getD 2 0
    let edgesAddr := args.getD 3 0
    let outEdgesAddr := args.getD 5 0
    let sVerts := readList mem sVertsAddr kS
    let edges := readEdges mem edgesAddr e
    let filtered := edges.filter fun ed => decide (ed.1 ∈ sVerts.toFinset ∧ ed.2 ∈ sVerts.toFinset)
    v = filtered.length ∧
    EdgesAt mem' outEdgesAddr filtered ∧
    (∀ a, a < outEdgesAddr ∨ outEdgesAddr + 2 * e ≤ a → mem' a = mem a)
  cost args _mem :=
    restrictCost (args.getD 0 0) (args.getD 2 0)

/-! ## 4. `setDiffProc` -/

/-- Filter `verts` to vertices not in `rList`, writing the result at `outRestAddr` and returning
its length. Args: `[k, vertsAddr, kR, rAddr, locAddr, outRestAddr]`. -/
def setDiffProc : Stmt :=
  markVertsStmt 2 3 4 6 7 1 ;;
  .assign 9 (.const 0) ;;
  forRange 6 (.const 0) (.reg 0)
    (.assign 7 (.load (.bin .add (.reg 1) (.reg 6))) ;;
     .assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
     .cond (.bin .eq (.reg 8) (.const 0))
       (.store (.bin .add (.reg 5) (.reg 9)) (.reg 7) ;;
        .assign 9 (.bin .add (.reg 9) (.const 1)))
       .nop) ;;
  markVertsStmt 2 3 4 6 7 0 ;;
  .ret (.reg 9)

/-- Step bound for `setDiffProc`: `O(k + kR + 1)`. -/
def setDiffCost (k kR : ℕ) : ℕ :=
  60 * k + 60 * kR + 80

/-- Contract for `setDiffProc`: writes `verts.filter (fun u => decide (u ∉ rList.toFinset))` at
`outRestAddr` and returns its length, restoring `locAddr` to all zeros and preserving all memory
outside `[outRestAddr, outRestAddr + k)`. -/
def setDiffContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n k vertsAddr kR rAddr locAddr outRestAddr : ℕ)
      (verts rList : List ℕ),
      args = [k, vertsAddr, kR, rAddr, locAddr, outRestAddr] ∧
      verts.length = k ∧ (∀ u ∈ verts, u < n) ∧
      rList.length = kR ∧ (∀ u ∈ rList, u < n) ∧
      ListAt mem vertsAddr verts ∧
      ListAt mem rAddr rList ∧
      (∀ u < n, mem (locAddr + u) = 0) ∧
      vertsAddr + k < 2 ^ w ∧
      rAddr + kR < 2 ^ w ∧
      locAddr + n < 2 ^ w ∧
      outRestAddr + k < 2 ^ w ∧
      16 < 2 ^ w ∧
      DisjointRange locAddr n vertsAddr k ∧
      DisjointRange locAddr n rAddr kR ∧
      DisjointRange locAddr n outRestAddr k ∧
      DisjointRange outRestAddr k vertsAddr k ∧
      DisjointRange outRestAddr k rAddr kR
  post args mem v mem' :=
    let k := args.getD 0 0
    let vertsAddr := args.getD 1 0
    let kR := args.getD 2 0
    let rAddr := args.getD 3 0
    let outRestAddr := args.getD 5 0
    let verts := readList mem vertsAddr k
    let rList := readList mem rAddr kR
    let diff := verts.filter fun u => decide (u ∉ rList.toFinset)
    v = diff.length ∧
    ListAt mem' outRestAddr diff ∧
    (∀ a, a < outRestAddr ∨ outRestAddr + k ≤ a → mem' a = mem a)
  cost args _mem :=
    setDiffCost (args.getD 0 0) (args.getD 2 0)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited

lemma markVertsStmt_noRand (rLen rList rLoc rI rU val : ℕ) :
    (markVertsStmt rLen rList rLoc rI rU val).NoRand := by
  simp [markVertsStmt, forRange, forUp, Stmt.NoRand]

lemma markEdgesStmt_noRand (rE rEdges rLoc rI rU rV val : ℕ) :
    (markEdgesStmt rE rEdges rLoc rI rU rV val).NoRand := by
  simp [markEdgesStmt, forRange, forUp, Stmt.NoRand]

lemma stripIsolatedProc_noRand : stripIsolatedProc.NoRand := by
  simp [stripIsolatedProc, markEdgesStmt_noRand, forRange, forUp, Stmt.NoRand]

lemma restrictProc_noRand : restrictProc.NoRand := by
  simp [restrictProc, markVertsStmt_noRand, forRange, forUp, Stmt.NoRand]

lemma setDiffProc_noRand : setDiffProc.NoRand := by
  simp [setDiffProc, markVertsStmt_noRand, forRange, forUp, Stmt.NoRand]

/-! ## 5. Shared Mark/Clear Loop Triples -/

lemma disjointRange_ne {a la b lb x y : ℕ} (hd : DisjointRange a la b lb)
    (hx1 : a ≤ x) (hx2 : x < a + la) (hy1 : b ≤ y) (hy2 : y < b + lb) : x ≠ y := by
  rcases hd with h | h <;> omega

lemma markVerts_triple {w n len listAddr locAddr val rLen rList rLoc rI rU : ℕ}
    (pProg : Program) (st₀ : State) (xs : List ℕ)
    (hdReg : [rLen, rList, rLoc, rI, rU].Nodup)
    (hrLen : st₀.regs rLen = len) (hrList : st₀.regs rList = listAddr)
    (hrLoc : st₀.regs rLoc = locAddr)
    (hlen : xs.length = len) (hxs_lt : ∀ u ∈ xs, u < n)
    (hlist : ListAt st₀.mem listAddr xs)
    (hdisj : DisjointRange locAddr n listAddr len)
    (hwList : listAddr + len < 2 ^ w) (hwLoc : locAddr + n < 2 ^ w)
    (hwVal : val < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀)
      (markVertsStmt rLen rList rLoc rI rU val)
      (normalPost fun s' =>
        (∀ u ∈ xs, s'.mem (locAddr + u) = val) ∧
        (∀ a, (∀ u ∈ xs, a ≠ locAddr + u) → s'.mem a = st₀.mem a) ∧
        (∀ r, r ≠ rI → r ≠ rU → s'.regs r = st₀.regs r))
      (fun _ => 25 * len + 15) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hdReg
  rcases hdReg with ⟨⟨_, _, hLenI, hLenU⟩, ⟨_, hListI, hListU⟩, ⟨hLocI, hLocU⟩, hIU, _⟩
  have hloop := Triple.forRange_const (p := pProg) (r := rI) (lo := .const 0) (hi := .reg rLen)
    (body := .assign rU (.load (.bin .add (.reg rList) (.reg rI))) ;;
      .store (.bin .add (.reg rLoc) (.reg rU)) (.const val))
    (P := fun s => s = st₀)
    (Inv := fun i s =>
      s.regs rI = i ∧
      (∀ r, r ≠ rI → r ≠ rU → s.regs r = st₀.regs r) ∧
      (∀ u ∈ xs.take i, s.mem (locAddr + u) = val) ∧
      (∀ a, (∀ u ∈ xs.take i, a ≠ locAddr + u) → s.mem a = st₀.mem a))
    14 0 len (Nat.zero_le len) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun r hrI _ => by simp [Function.update_of_ne hrI],
        by simp, fun a _ => rfl⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hrl : s.regs rLen = len := by rw [hi.2.1 rLen hLenI hLenU, hrLen]
      simp [Expr.eval, hrl])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hkeep, hmark, hframe⟩
      have hiLen : i < xs.length := by omega
      have hlist_s : s.mem (listAddr + i) = xs[i]'hiLen := by
        rw [hframe (listAddr + i) (fun u hu =>
          (disjointRange_ne hdisj (by omega) (by have := hxs_lt u (List.mem_of_mem_take hu); omega)
            (by omega) (by omega)).symm)]
        exact hlist i hiLen
      have hrl : s.regs rList = listAddr := by rw [hkeep rList hListI hListU, hrList]
      have hrloc : s.regs rLoc = locAddr := by rw [hkeep rLoc hLocI hLocU, hrLoc]
      have hu_lt : xs[i]'hiLen < n := hxs_lt _ (List.getElem_mem hiLen)
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := xs[i]'hiLen)
        (by simp [Expr.eval, BinOp.eval, hrl, hiReg, (by omega : listAddr + i < 2 ^ w), hlist_s]) ?_
      refine runs_store_le (x := locAddr + xs[i]'hiLen) (v := val)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne hLocU, hrloc,
              (by omega : locAddr + xs[i]'hiLen < 2 ^ w)])
        (by simp [Expr.eval, hwVal]) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp, fun r hrI hrU => by simp [Function.update_of_ne hrI, Function.update_of_ne hrU, hkeep r hrI hrU],
        fun u hu => ?_, fun a ha => ?_⟩, by simp [Function.update_of_ne hIU, hiReg]⟩
      · dsimp only
        rw [List.take_succ_eq_append_getElem hiLen, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · by_cases heq : u = xs[i]'hiLen
          · subst heq; simp
          · rw [Function.update_of_ne (by omega)]; exact hmark u hu
        · simp
      · dsimp only
        have hmem_cur : xs[i]'hiLen ∈ xs.take (i + 1) := by
          rw [List.take_succ_eq_append_getElem hiLen]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hne_cur : a ≠ locAddr + xs[i]'hiLen := ha (xs[i]'hiLen) hmem_cur
        rw [Function.update_of_ne hne_cur]
        exact hframe a fun u hu => ha u (by rw [List.take_succ_eq_append_getElem hiLen]; exact List.mem_append_left _ hu))
  refine hloop.conseq (fun _ h => h)
    (fun o s' h => by
      cases o with
      | returned _ => exact False.elim h
      | normal =>
        rcases h with ⟨_, hkeep, hmark, hframe⟩
        have htake : xs.take len = xs := by rw [← hlen, List.take_length]
        rw [htake] at hmark hframe
        exact ⟨hmark, hframe, hkeep⟩)
    (fun _ _ => by simp [Expr.size]; omega)

lemma markEdges_triple {w n e edgesAddr locAddr val rE rEdges rLoc rI rU rV : ℕ}
    (pProg : Program) (st₀ : State) (edges : List (ℕ × ℕ))
    (hdReg : [rE, rEdges, rLoc, rI, rU, rV].Nodup)
    (hrE : st₀.regs rE = e) (hrEdges : st₀.regs rEdges = edgesAddr)
    (hrLoc : st₀.regs rLoc = locAddr)
    (hlen : edges.length = e) (hed_lt : ∀ ed ∈ edges, ed.1 < n ∧ ed.2 < n)
    (hedges : EdgesAt st₀.mem edgesAddr edges)
    (hdisj : DisjointRange locAddr n edgesAddr (2 * e))
    (hwEdges : edgesAddr + 2 * e < 2 ^ w) (hwLoc : locAddr + n < 2 ^ w)
    (hwVal : val < 2 ^ w) (hw2 : 2 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀)
      (markEdgesStmt rE rEdges rLoc rI rU rV val)
      (normalPost fun s' =>
        (∀ ed ∈ edges, s'.mem (locAddr + ed.1) = val ∧ s'.mem (locAddr + ed.2) = val) ∧
        (∀ a, (∀ ed ∈ edges, a ≠ locAddr + ed.1 ∧ a ≠ locAddr + ed.2) → s'.mem a = st₀.mem a) ∧
        (∀ r, r ≠ rI → r ≠ rU → r ≠ rV → s'.regs r = st₀.regs r))
      (fun _ => 50 * e + 15) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hdReg
  rcases hdReg with ⟨⟨_, _, hEI, hEU, hEV⟩, ⟨_, hEdI, hEdU, hEdV⟩,
    ⟨hLocI, hLocU, hLocV⟩, ⟨hIU, hIV⟩, hUV, _⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := pProg) (r := rI) (lo := .const 0) (hi := .reg rE)
    (body :=
      .assign rU (.load (.bin .add (.reg rEdges) (.bin .mul (.const 2) (.reg rI)))) ;;
      .assign rV (.load (.bin .add (.bin .add (.reg rEdges) (.bin .mul (.const 2) (.reg rI))) (.const 1))) ;;
      .store (.bin .add (.reg rLoc) (.reg rU)) (.const val) ;;
      .store (.bin .add (.reg rLoc) (.reg rV)) (.const val))
    (P := fun s => s = st₀)
    (Inv := fun i s =>
      s.regs rI = i ∧
      (∀ r, r ≠ rI → r ≠ rU → r ≠ rV → s.regs r = st₀.regs r) ∧
      (∀ ed ∈ edges.take i, s.mem (locAddr + ed.1) = val ∧ s.mem (locAddr + ed.2) = val) ∧
      (∀ a, (∀ ed ∈ edges.take i, a ≠ locAddr + ed.1 ∧ a ≠ locAddr + ed.2) → s.mem a = st₀.mem a))
    38 0 e (Nat.zero_le e) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun r hrI _ _ => by simp [Function.update_of_ne hrI],
        by simp, fun a _ => rfl⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hre : s.regs rE = e := by rw [hi.2.1 rE hEI hEU hEV, hrE]
      simp [Expr.eval, hre])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hkeep, hmark, hframe⟩
      have hiLen : i < edges.length := by omega
      have hed_pair := hedges i hiLen
      have hfr1 : s.mem (edgesAddr + 2 * i) = (edges[i]'hiLen).1 := by
        rw [hframe (edgesAddr + 2 * i) (fun ed hed => by
          have hl := hed_lt ed (List.mem_of_mem_take hed)
          exact ⟨(disjointRange_ne hdisj (by omega) (by omega) (by omega) (by omega)).symm,
            (disjointRange_ne hdisj (by omega) (by omega) (by omega) (by omega)).symm⟩)]
        exact hed_pair.1
      have hfr2 : s.mem (edgesAddr + 2 * i + 1) = (edges[i]'hiLen).2 := by
        rw [hframe (edgesAddr + 2 * i + 1) (fun ed hed => by
          have hl := hed_lt ed (List.mem_of_mem_take hed)
          exact ⟨(disjointRange_ne hdisj (by omega) (by omega) (by omega) (by omega)).symm,
            (disjointRange_ne hdisj (by omega) (by omega) (by omega) (by omega)).symm⟩)]
        exact hed_pair.2
      have hred : s.regs rEdges = edgesAddr := by rw [hkeep rEdges hEdI hEdU hEdV, hrEdges]
      have hrloc : s.regs rLoc = locAddr := by rw [hkeep rLoc hLocI hLocU hLocV, hrLoc]
      have hcur_lt := hed_lt _ (List.getElem_mem hiLen)
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := (edges[i]'hiLen).1)
        (by simp [Expr.eval, BinOp.eval, hred, hiReg, hw2, (by omega : 2 * i < 2 ^ w),
              (by omega : edgesAddr + 2 * i < 2 ^ w), hfr1]) ?_
      refine runs_seq_assign_le (v := (edges[i]'hiLen).2)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne hEdU, Function.update_of_ne hIU,
              hred, hiReg, hw1, hw2, (by omega : 2 * i < 2 ^ w),
              (by omega : edgesAddr + 2 * i < 2 ^ w),
              (by omega : edgesAddr + 2 * i + 1 < 2 ^ w), hfr2]) ?_
      refine runs_seq_store_le (x := locAddr + (edges[i]'hiLen).1) (v := val)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne hLocV, Function.update_of_ne hLocU,
              Function.update_of_ne hUV, hrloc, (by omega : locAddr + (edges[i]'hiLen).1 < 2 ^ w)])
        (by simp [Expr.eval, hwVal]) ?_
      refine runs_store_le (x := locAddr + (edges[i]'hiLen).2) (v := val)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne hLocV, Function.update_of_ne hLocU,
              hrloc, (by omega : locAddr + (edges[i]'hiLen).2 < 2 ^ w)])
        (by simp [Expr.eval, hwVal]) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp, fun r hrI hrU hrV => by
          simp [Function.update_of_ne hrI, Function.update_of_ne hrV, Function.update_of_ne hrU,
            hkeep r hrI hrU hrV],
        fun ed hed => ?_, fun a ha => ?_⟩,
        by simp [Function.update_of_ne hIV, Function.update_of_ne hIU, hiReg]⟩
      · dsimp only
        rw [List.take_succ_eq_append_getElem hiLen, List.mem_append, List.mem_singleton] at hed
        rcases hed with hed | rfl
        · constructor
          · by_cases h2 : ed.1 = (edges[i]'hiLen).2
            · simp [h2]
            · rw [Function.update_of_ne (by omega)]
              by_cases h1 : ed.1 = (edges[i]'hiLen).1
              · simp [h1]
              · rw [Function.update_of_ne (by omega)]; exact (hmark ed hed).1
          · by_cases h2 : ed.2 = (edges[i]'hiLen).2
            · simp [h2]
            · rw [Function.update_of_ne (by omega)]
              by_cases h1 : ed.2 = (edges[i]'hiLen).1
              · simp [h1]
              · rw [Function.update_of_ne (by omega)]; exact (hmark ed hed).2
        · constructor
          · by_cases h12 : (edges[i]'hiLen).1 = (edges[i]'hiLen).2
            · simp [h12]
            · rw [Function.update_of_ne (by omega)]; simp
          · simp
      · dsimp only
        have hmem_cur : edges[i]'hiLen ∈ edges.take (i + 1) := by
          rw [List.take_succ_eq_append_getElem hiLen]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have hcur := ha (edges[i]'hiLen) hmem_cur
        rw [Function.update_of_ne hcur.2, Function.update_of_ne hcur.1]
        exact hframe a fun ed hed =>
          ha ed (by rw [List.take_succ_eq_append_getElem hiLen]; exact List.mem_append_left _ hed))
  refine hloop.conseq (fun _ h => h)
    (fun o s' h => by
      cases o with
      | returned _ => exact False.elim h
      | normal =>
        rcases h with ⟨_, hkeep, hmark, hframe⟩
        have htake : edges.take e = edges := by rw [← hlen, List.take_length]
        rw [htake] at hmark hframe
        exact ⟨hmark, hframe, hkeep⟩)
    (fun _ _ => by simp [Expr.size]; omega)


end MinCostFlow.ExpanderDecomp
