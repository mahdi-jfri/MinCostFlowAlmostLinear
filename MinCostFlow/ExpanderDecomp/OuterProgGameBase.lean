module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OuterGame
public import MinCostFlow.ExpanderDecomp.OuterProgContracts
public import MinCostFlow.ExpanderDecomp.CoreOuter
public import MinCostFlow.ExpanderDecomp.OuterProgParams
public import MinCostFlow.ExpanderDecomp.OuterProgMatching
import Mathlib.Tactic.Linarith

/-!
# Helper Procedures and Layout for the Outer Cut-Matching Game (`OuterProgGameBase`)

Defines the procedure-index bundle `OuterGameIndices`, output descriptor `OuterGameOutAt`, heap
space and cost bounds, and the five deterministic (`NoRand`) building-block statements used by
`outerGameProc` (`OuterProgGame.lean`):

1. `appendEdgesStmt`: appends a flat edge array `src[0..len-1]` onto `dst` starting at edge offset
   `off` in `O(len + 1)` time.
2. `gameLoadParamsStmt`: loads `(M, r, L, N, bOut, DOut, gameFuel)` from `OuterParamBlockAt` and
   computes `twoE = 2 * e` and `z = e / DOut`.
3. `gameAllocBufsStmt`: computes the disjoint fixed buffer addresses carved out of `[h, hInit)` and
   initializes `wLen = 0`, `fLen = 0`, `hCur = hInit`, `rem = gameFuel`.
4. `gameInitBufsStmt`: fills `xPortAddr` with `[2 * e, 0, 1, ..., 2 * e - 1]` and initializes the
   empty witness graph header `[2 * e, 0]` at `wAddr`.
5. `gameAppendMatchedStmt`: appends `M_k` and `F_k` onto `wAddr` (updating `mem[wAddr + 1]` and
   `wLen`) and appends `F_k` onto `fAddr` (updating `fLen`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Indices, Output Descriptor, Space and Cost Bounds -/

/-- Procedure indices invoked by `outerGameProc`. -/
structure OuterGameIndices where
  /-- Index of `coreLevelProc` meeting `coreLevelContract`. -/
  bCoreLevel : ℕ
  /-- Index of the recursive core player meeting `outerCoreContract`. -/
  bCore : ℕ
  /-- Index of the static matching player meeting `outerRouterContract`. -/
  bRoute : ℕ
  /-- Index of `padToBisectionProc` meeting `padToBisectionContract`. -/
  bPad : ℕ
  /-- Index of `buildInjPairProc` meeting `buildInjPairContract`. -/
  bInj : ℕ
  /-- Index of `fakeCompletionProc` meeting `fakeCompletionContract`. -/
  bFake : ℕ

/-- Four-word output descriptor written by `outerGameProc` at `outResAddr`:
* `.cut U`: `[0, kU, uAddr, _]` with `U_list.Nodup`, `U_list.toFinset = U`, `ListAt mem uAddr U_list`,
  and `h ≤ uAddr`, `uAddr + kU ≤ h'`.
* `.witness W_edges F_edges`: `[1, wAddr, |F_edges|, fAddr]` with `GraphAt mem wAddr ⟨2 * e, W_edges⟩`,
  `EdgesAt mem fAddr F_edges`, and both buffers below `h'`. -/
def OuterGameOutAt (mem : ℕ → ℕ) (outResAddr h h' e : ℕ) : OuterGameResult → Prop
  | .cut U =>
      mem outResAddr = 0 ∧
      ∃ U_list : List ℕ,
        U_list.Nodup ∧ U_list.toFinset = U ∧
        mem (outResAddr + 1) = U_list.length ∧
        ListAt mem (mem (outResAddr + 2)) U_list ∧
        h ≤ mem (outResAddr + 2) ∧
        mem (outResAddr + 2) + U_list.length ≤ h'
  | .witness W_edges F_edges =>
      mem outResAddr = 1 ∧
      GraphAt mem (mem (outResAddr + 1)) (Graph.mk (2 * e) W_edges) ∧
      mem (outResAddr + 1) + 2 + 2 * W_edges.length ≤ h' ∧
      mem (outResAddr + 2) = F_edges.length ∧
      EdgesAt mem (mem (outResAddr + 3)) F_edges ∧
      mem (outResAddr + 3) + 2 * F_edges.length ≤ h'

lemma OuterGameOutAt.mono_h {mem : ℕ → ℕ} {outResAddr h₁ h₂ h' e : ℕ} {res : OuterGameResult}
    (hle : h₁ ≤ h₂) (hOut : OuterGameOutAt mem outResAddr h₂ h' e res) :
    OuterGameOutAt mem outResAddr h₁ h' e res := by
  cases res with
  | cut U =>
    rcases hOut with ⟨h0, Ul, hnd, hfin, hlen, hlist, hge, hle'⟩
    exact ⟨h0, Ul, hnd, hfin, hlen, hlist, le_trans hle hge, hle'⟩
  | witness W F => exact hOut

/-- Existential mathematical specification of the outer cut-matching game outcome,
matching `OuterGame.outerGame_spec` without naming a deterministic core function:
* `.cut U`: sparse balanced port cut in `Hhat`;
* `.witness W_out F_out`: `1 / (2 P_r)`-expansion expander on `Finset.range (2 * e)` with at most
  `t * z` fake edges of max degree `≤ t`, embedded into `Hhat ∪ F_out` with congestion `≤ t * R_out`. -/
def OuterGameOutcomeSpec (cfg : ParamConfig) (M r e : ℕ) (Hhat : Graph) : OuterGameResult → Prop
  | .cut U =>
      U ⊆ Hhat.verts ∧
        bOut cfg M * Hhat.cut U ≤ min U.card (Hhat.verts \ U).card ∧
        e / DOut cfg M r + 1 ≤ 2 * U.card ∧
        e / DOut cfg M r + 1 ≤ 2 * (Hhat.verts \ U).card
  | .witness W_out F_out =>
      (Graph.mk (2 * e) W_out).IsExpansionExpanderOn (Finset.range (2 * e))
          (1 / (2 * (PParam cfg M r : ℝ))) ∧
        (∀ ed ∈ F_out, ed.1 < 2 * e ∧ ed.2 < 2 * e) ∧
        F_out.length ≤ tParam M * (e / DOut cfg M r) ∧
        (∀ v < 2 * e, (Graph.mk (2 * e) F_out).deg v ≤ tParam M) ∧
        ∃ emb : ℕ → List ℕ,
          IsEmbeddingOn ⟨2 * e, W_out⟩ ⟨2 * e, Hhat.edges ++ F_out⟩ (Finset.range (2 * e)) emb ∧
          ∀ i < (Graph.mk (2 * e) (Hhat.edges ++ F_out)).m,
            congestion ⟨2 * e, W_out⟩ emb i ≤ tParam M * ROut cfg M

/-- Per-round model cost upper bound for one iteration of the outer cut-matching game on an
`e`-edge subgraph (`2 * e` ports, `Hhat.m ≤ 10 * e`). -/
def outerGameRoundBudget (cfg : ParamConfig) (M r routeC e : ℕ) : ℕ :=
  2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
    routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e

/-- Total model cost upper bound across all `49 * L + 1` rounds of the outer cut-matching game. -/
def outerGameMaxCost (cfg : ParamConfig) (M r routeC e : ℕ) : ℕ :=
  (49 * LParam M + 1) * outerGameRoundBudget cfg M r routeC e

/-- Fixed upfront buffer space (words) carved out of `[h, hInit)` by `outerGameProc`. -/
def outerGameBufSpace (M e : ℕ) : ℕ :=
  11 + 12 * e + 4 * (49 * LParam M + 1) * e

/-- Size-sensitive cost bound for a recursive core cut-player cost function
`coreCost` at global parameters `(cfg, M, r)`: whenever `1 ≤ q ≤ r` is the least level with
`G.n ≤ N^q` (so `N^{q-1} < G.n`) and `G` is valid, loopless, of max degree `≤ Δ`, we have
`coreCost q G ≤ G.n * N^2 * W^{10 r^2 + 10}`. -/
def CoreCostBounded (cfg : ParamConfig) (M r : ℕ) (coreCost : ℕ → Graph → ℕ) : Prop :=
  ∀ q (G : Graph), 1 ≤ q → q ≤ r → G.IsValid → G.IsLoopless →
    (NOf M r) ^ (q - 1) < G.n → G.n ≤ (NOf M r) ^ q →
    (∀ v < G.n, G.deg v ≤ deltaParam M) →
    coreCost q G ≤ G.n * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)

/-- Dynamic zero-heap space (words) across `fuel` remaining rounds of the outer cut-matching game
at global parameters `(M, r)` with model cost budget `loopCost`. -/
def outerGameLoopSpace (C_sp M r e fuel loopCost : ℕ) : ℕ :=
  C_sp * coreSpaceBase M r * (loopCost + fuel) + fuel * (2 * C_sp * ((2 * e + 3) ^ 5 + 1) + 10 * e)

/-- Total zero-heap space (words) used by `outerGameProc`. -/
def outerGameSpace (C_sp M r e loopCost : ℕ) : ℕ :=
  outerGameBufSpace M e + outerGameLoopSpace C_sp M r e (49 * LParam M + 1) loopCost

/-- Multiplicative step-cost constant of `outerGameProc` over `outerGameLoopCost`. -/
def outerGameCostFactor (C_core C_rt : ℕ) : ℕ :=
  2 * C_core + 2 * C_rt + 2000

/-- Step bound for `outerGameProc` on `e` edges, `r` levels, and model loop cost `loopCost`. -/
def outerGameStepBound (C_core C_rt r e loopCost : ℕ) : ℕ :=
  outerGameCostFactor C_core C_rt * (loopCost + e + 1) + 40 * r + 500

/-! ## 2. Building-Block Statements -/

/-- Append `len` edges from `srcAddr` onto `dstAddr` starting at edge offset `off`.
Uses read-only `rLen, rSrc, rDst, rOff` and scratch `rI, rU, rV`. -/
def appendEdgesStmt (rLen rSrc rDst rOff rI rU rV : ℕ) : Stmt :=
  forRange rI (.const 0) (.reg rLen)
    (.assign rU (.load (.bin .add (.reg rSrc) (.bin .mul (.const 2) (.reg rI)))) ;;
     .assign rV (.load (.bin .add (.bin .add (.reg rSrc) (.bin .mul (.const 2) (.reg rI))) (.const 1))) ;;
     .store (.bin .add (.reg rDst) (.bin .mul (.const 2) (.bin .add (.reg rOff) (.reg rI)))) (.reg rU) ;;
     .store (.bin .add (.bin .add (.reg rDst) (.bin .mul (.const 2) (.bin .add (.reg rOff) (.reg rI)))) (.const 1)) (.reg rV))

/-- Load outer parameters from `paramAddr` (reg 2) into regs 5..11 and compute `twoE` (reg 12)
and `z = e / DOut` (reg 13). -/
def gameLoadParamsStmt : Stmt :=
  (.assign 5 (.load (.bin .add (.reg 2) (.const 1))) ;;
   .assign 6 (.load (.bin .add (.reg 2) (.const 2))) ;;
   .assign 7 (.load (.bin .add (.reg 2) (.const 4))) ;;
   .assign 8 (.load (.bin .add (.reg 2) (.const 5)))) ;;
  (.assign 9 (.load (.bin .add (.reg 2) (.const 7))) ;;
   .assign 10 (.load (.bin .add (.reg 2) (.const 9))) ;;
   .assign 11 (.load (.bin .add (.reg 2) (.const 11))) ;;
   .assign 12 (.bin .mul (.const 2) (.reg 0)) ;;
   .assign 13 (.bin .div (.reg 0) (.reg 10)))

/-- Compute disjoint buffer pointers `regs 15..23`, initialize `wLen = 0` (`reg 24`),
`fLen = 0` (`reg 25`), `hCur = hInit` (`reg 26`), and `rem = gameFuel` (`reg 27`). -/
def gameAllocBufsStmt : Stmt :=
  (.assign 15 (.reg 4) ;;
   .assign 16 (.bin .add (.bin .add (.reg 15) (.const 1)) (.reg 12)) ;;
   .assign 23 (.bin .add (.reg 16) (.const 2)) ;;
   .assign 28 (.bin .mul (.reg 11) (.reg 12))) ;;
  (.assign 17 (.bin .add (.reg 23) (.reg 28)) ;;
   .assign 18 (.bin .add (.reg 17) (.reg 28)) ;;
   .assign 19 (.bin .add (.bin .add (.reg 18) (.const 2)) (.reg 12)) ;;
   .assign 20 (.bin .add (.bin .add (.reg 19) (.const 3)) (.reg 12))) ;;
  (.assign 21 (.bin .add (.bin .add (.reg 20) (.const 2)) (.bin .mul (.const 2) (.reg 12))) ;;
   .assign 22 (.bin .add (.reg 21) (.reg 12)) ;;
   .assign 26 (.bin .add (.reg 22) (.const 1))) ;;
  (.assign 24 (.const 0) ;;
   .assign 25 (.const 0) ;;
   .assign 27 (.reg 11))

/-- Fill `xPortAddr` (`reg 15`) with `[2*e, 0, 1, ..., 2*e-1]` and initialize `wAddr` (`reg 16`)
with `[2*e, 0]`. -/
def gameInitBufsStmt : Stmt :=
  (.store (.reg 15) (.reg 12) ;;
   .store (.reg 16) (.reg 12) ;;
   .store (.bin .add (.reg 16) (.const 1)) (.const 0)) ;;
  forRange 28 (.const 0) (.reg 12)
    (.store (.bin .add (.bin .add (.reg 15) (.const 1)) (.reg 28)) (.reg 28))

/-- Append `M` (`reg 29` edges at `reg 30`) and `F_k` (`mem[reg 22]` edges at `reg 21`) to
`wEdgesAddr` (`reg 23`, offset `reg 24`), update `mem[wAddr + 1]`, and append `F_k` to `fAddr`
(`reg 17`, offset `reg 25`). -/
def gameAppendMatchedStmt : Stmt :=
  appendEdgesStmt 29 30 23 24 32 33 34 ;;
  (.assign 24 (.bin .add (.reg 24) (.reg 29)) ;;
   .assign 31 (.load (.reg 22))) ;;
  appendEdgesStmt 31 21 23 24 32 33 34 ;;
  (.assign 24 (.bin .add (.reg 24) (.reg 31)) ;;
   .store (.bin .add (.reg 16) (.const 1)) (.reg 24)) ;;
  appendEdgesStmt 31 21 17 25 32 33 34 ;;
  .assign 25 (.bin .add (.reg 25) (.reg 31))

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

lemma appendEdgesStmt_noRand (rLen rSrc rDst rOff rI rU rV : ℕ) :
    (appendEdgesStmt rLen rSrc rDst rOff rI rU rV).NoRand := by
  simp [appendEdgesStmt, forRange, forUp, Stmt.NoRand]

lemma gameLoadParamsStmt_noRand : gameLoadParamsStmt.NoRand := by
  simp [gameLoadParamsStmt, Stmt.NoRand]

lemma gameAllocBufsStmt_noRand : gameAllocBufsStmt.NoRand := by
  simp [gameAllocBufsStmt, Stmt.NoRand]

lemma gameInitBufsStmt_noRand : gameInitBufsStmt.NoRand := by
  simp [gameInitBufsStmt, forRange, forUp, Stmt.NoRand]

lemma gameAppendMatchedStmt_noRand : gameAppendMatchedStmt.NoRand := by
  simp [gameAppendMatchedStmt, appendEdgesStmt_noRand, Stmt.NoRand]

/-! ## 3. Verified Triples for the Building Blocks -/

/-- Specification of `appendEdgesStmt`: appends `src` onto `old` at `dstAddr` (at edge offset
`old.length`), preserving all memory outside `[dstAddr + 2 * old.length, dstAddr + 2 * (old.length + src.length))`. -/
lemma appendEdges_triple {w len srcAddr dstAddr off rLen rSrc rDst rOff rI rU rV : ℕ}
    (pProg : Program) (st₀ : State) (old src : List (ℕ × ℕ))
    (hdReg : [rLen, rSrc, rDst, rOff, rI, rU, rV].Nodup)
    (hrLen : st₀.regs rLen = len) (hrSrc : st₀.regs rSrc = srcAddr)
    (hrDst : st₀.regs rDst = dstAddr) (hrOff : st₀.regs rOff = off)
    (hlenSrc : src.length = len) (hlenOld : old.length = off)
    (hOld : EdgesAt st₀.mem dstAddr old) (hSrc : EdgesAt st₀.mem srcAddr src)
    (hdisj : DisjointRange (dstAddr + 2 * off) (2 * len) srcAddr (2 * len))
    (hwSrc : srcAddr + 2 * len < 2 ^ w)
    (hwDst : dstAddr + 2 * (off + len) < 2 ^ w)
    (hw2 : 2 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀) (appendEdgesStmt rLen rSrc rDst rOff rI rU rV)
      (normalPost fun s' =>
        EdgesAt s'.mem dstAddr (old ++ src) ∧
        (∀ a, a < dstAddr + 2 * off ∨ dstAddr + 2 * (off + len) ≤ a → s'.mem a = st₀.mem a) ∧
        (∀ r, r ≠ rI → r ≠ rU → r ≠ rV → s'.regs r = st₀.regs r))
      (fun _ => 65 * len + 20) := by
  intro s ω hs; subst s
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hdReg
  rcases hdReg with ⟨⟨_, _, _, hLI, hLU, hLV⟩, ⟨_, _, hSI, hSU, hSV⟩,
    ⟨_, hDI, hDU, hDV⟩, ⟨hOI, hOU, hOV⟩, ⟨hIU, hIV⟩, hUV, _⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := pProg) (r := rI) (lo := .const 0) (hi := .reg rLen)
    (body :=
      .assign rU (.load (.bin .add (.reg rSrc) (.bin .mul (.const 2) (.reg rI)))) ;;
      .assign rV (.load (.bin .add (.bin .add (.reg rSrc) (.bin .mul (.const 2) (.reg rI))) (.const 1))) ;;
      .store (.bin .add (.reg rDst) (.bin .mul (.const 2) (.bin .add (.reg rOff) (.reg rI)))) (.reg rU) ;;
      .store (.bin .add (.bin .add (.reg rDst) (.bin .mul (.const 2) (.bin .add (.reg rOff) (.reg rI)))) (.const 1)) (.reg rV))
    (P := fun s => s = st₀)
    (Inv := fun i s =>
      s.regs rI = i ∧
      EdgesAt s.mem dstAddr (old ++ src.take i) ∧
      (∀ a, a < dstAddr + 2 * off ∨ dstAddr + 2 * (off + len) ≤ a → s.mem a = st₀.mem a) ∧
      (∀ r, r ≠ rI → r ≠ rU → r ≠ rV → s.regs r = st₀.regs r))
    52 0 len (Nat.zero_le len) hw1 (fun _ => by omega)
    (fun s hs => by
      subst s
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        by simpa using hOld, fun _ _ => rfl,
        fun r hrI _ _ => Function.update_of_ne hrI _ _⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hrl : s.regs rLen = len := by rw [hi.2.2.2 rLen hLI hLU hLV, hrLen]
      simp [Expr.eval, hrl])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hEd, hfr, hkr⟩
      have hiSrc : i < src.length := by omega
      set ed := src[i]'hiSrc
      have hmu : s.mem (srcAddr + 2 * i) = ed.1 := by
        rw [hfr _ (Or.elim hdisj (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact (hSrc i hiSrc).1
      have hmv : s.mem (srcAddr + 2 * i + 1) = ed.2 := by
        rw [hfr _ (Or.elim hdisj (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact (hSrc i hiSrc).2
      have hrs : s.regs rSrc = srcAddr := by rw [hkr rSrc hSI hSU hSV, hrSrc]
      have hrd : s.regs rDst = dstAddr := by rw [hkr rDst hDI hDU hDV, hrDst]
      have hro : s.regs rOff = off := by rw [hkr rOff hOI hOU hOV, hrOff]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := ed.1)
        (by simp [Expr.eval, BinOp.eval, hrs, hiReg, hw2, (by omega : 2 * i < 2 ^ w),
              (by omega : srcAddr + 2 * i < 2 ^ w), hmu]) ?_
      refine runs_seq_assign_le (v := ed.2)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne hSU, hrs,
              Function.update_of_ne hIU, hiReg, hw1, hw2, (by omega : 2 * i < 2 ^ w),
              (by omega : srcAddr + 2 * i < 2 ^ w), (by omega : srcAddr + 2 * i + 1 < 2 ^ w), hmv]) ?_
      refine runs_seq_store_le (x := dstAddr + 2 * (off + i)) (v := ed.1)
        (by simp [Expr.eval, BinOp.eval, Function.update_of_ne hDV, Function.update_of_ne hDU, hrd,
              Function.update_of_ne hOV, Function.update_of_ne hOU, hro,
              Function.update_of_ne hIV, Function.update_of_ne hIU, hiReg, hw2,
              (by omega : off + i < 2 ^ w), (by omega : 2 * (off + i) < 2 ^ w),
              (by omega : dstAddr + 2 * (off + i) < 2 ^ w)])
        (by simp [Expr.eval, Function.update_of_ne hUV]) ?_
      let stA : State := {
        mem := Function.update s.mem (dstAddr + 2 * (off + i)) ed.1
        regs := Function.update (Function.update s.regs rU ed.1) rV ed.2
        pos := s.pos }
      let stB : State := { stA with mem := Function.update stA.mem (dstAddr + 2 * (off + i) + 1) ed.2 }
      refine ⟨.normal, stB, 11, runs_store_iff.mpr ⟨dstAddr + 2 * (off + i) + 1, ed.2,
          by simp [Expr.eval, BinOp.eval, stA, Function.update_of_ne hDV, Function.update_of_ne hDU, hrd,
               Function.update_of_ne hOV, Function.update_of_ne hOU, hro,
               Function.update_of_ne hIV, Function.update_of_ne hIU, hiReg, hw1, hw2,
               (by omega : off + i < 2 ^ w), (by omega : 2 * (off + i) < 2 ^ w),
               (by omega : dstAddr + 2 * (off + i) < 2 ^ w),
               (by omega : dstAddr + 2 * (off + i) + 1 < 2 ^ w)],
          by simp [Expr.eval, stA], rfl, rfl, by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
      refine ⟨⟨by simp, ?_, ?_, fun r hrI hrU hrV => by
          simp [stB, stA, Function.update_of_ne hrI, Function.update_of_ne hrV,
            Function.update_of_ne hrU, hkr r hrI hrU hrV]⟩,
        by simp [stB, stA, Function.update_of_ne hIV, Function.update_of_ne hIU, hiReg]⟩
      · intro j hj
        have hlen1 : (old ++ src.take i).length = off + i := by
          rw [List.length_append, List.length_take]; omega
        have hj_lt : j < off + i + 1 := by
          rw [List.length_append, List.length_take] at hj; omega
        by_cases hlt : j < off + i
        · have hj1 : j < (old ++ src.take i).length := by omega
          have hget : (old ++ src.take (i + 1))[j]'hj = (old ++ src.take i)[j]'hj1 := by
            by_cases hjo : j < old.length
            · rw [List.getElem_append_left hjo, List.getElem_append_left hjo]
            · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega),
                  List.getElem_take, List.getElem_take]
          rw [hget]
          dsimp only [stB, stA]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hEd j hj1
        · have hjeq : j = off + i := by omega
          subst j
          have hget : (old ++ src.take (i + 1))[off + i]'hj = ed := by
            rw [List.getElem_append_right (by omega), List.getElem_take]
            have hsub : off + i - old.length = i := by omega
            simp [hsub, ed]
          rw [hget]
          dsimp only [stB, stA]
          exact ⟨by rw [Function.update_of_ne (by omega), Function.update_self],
                 by rw [Function.update_self]⟩
      · intro a ha; dsimp only [stB, stA]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hfr a ha)
  refine runs_start_le ?_
  refine runs_triple_le hloop rfl (fun o st2 h => by
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨_, h2_Ed, h2_fr, h2_kr⟩
      have htake : src.take len = src := by rw [← hlenSrc, List.take_length]
      rw [htake] at h2_Ed
      exact ⟨h2_Ed, h2_fr, h2_kr⟩)
    (by simp [Expr.size]; omega)

lemma gameLoadParams_triple {cfg : ParamConfig} {w n M r e paramAddr : ℕ}
    (pProg : Program) (st₀ : State)
    (h0 : st₀.regs 0 = e) (h2 : st₀.regs 2 = paramAddr)
    (hPB : OuterParamBlockAt st₀.mem paramAddr cfg n M r)
    (hwP : paramAddr + 12 < 2 ^ w) (hwE : 2 * e + 16 < 2 ^ w)
    (hDpos : 0 < DOut cfg M r) :
    Triple w pProg (fun s => s = st₀) gameLoadParamsStmt
      (normalPost fun s' =>
        s'.mem = st₀.mem ∧
        s'.regs 5 = M ∧ s'.regs 6 = r ∧ s'.regs 7 = LParam M ∧
        s'.regs 8 = NOf M r ∧ s'.regs 9 = bOut cfg M ∧ s'.regs 10 = DOut cfg M r ∧
        s'.regs 11 = 49 * LParam M + 1 ∧ s'.regs 12 = 2 * e ∧
        s'.regs 13 = e / DOut cfg M r ∧
        (∀ r' ≤ 4, s'.regs r' = st₀.regs r'))
      (fun _ => 80) := by
  intro s ω hs; subst s
  rcases hPB with ⟨_, hM, hr, _, hL, hN, _, hb, _, hD, _, hF⟩
  have h1 : Triple w pProg (fun s => s = st₀)
      (.assign 5 (.load (.bin .add (.reg 2) (.const 1))) ;;
       .assign 6 (.load (.bin .add (.reg 2) (.const 2))) ;;
       .assign 7 (.load (.bin .add (.reg 2) (.const 4))) ;;
       .assign 8 (.load (.bin .add (.reg 2) (.const 5))))
      (normalPost fun s' =>
        s'.mem = st₀.mem ∧ s'.regs 5 = M ∧ s'.regs 6 = r ∧
        s'.regs 7 = LParam M ∧ s'.regs 8 = NOf M r ∧
        (∀ r' ≤ 4, s'.regs r' = st₀.regs r'))
      (fun _ => 35) := by
    intro s1 ω1 hs1; subst s1
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := M)
      (by simp [Expr.eval, BinOp.eval, h2, (by omega : 1 < 2 ^ w), (by omega : paramAddr + 1 < 2 ^ w), hM]) ?_
    refine runs_seq_assign_le (v := r)
      (by simp [Expr.eval, BinOp.eval, h2, (by omega : 2 < 2 ^ w), (by omega : paramAddr + 2 < 2 ^ w), hr]) ?_
    refine runs_seq_assign_le (v := LParam M)
      (by simp [Expr.eval, BinOp.eval, h2, (by omega : 4 < 2 ^ w), (by omega : paramAddr + 4 < 2 ^ w), hL]) ?_
    refine runs_assign_le (v := NOf M r)
      (by simp [Expr.eval, BinOp.eval, h2, (by omega : 5 < 2 ^ w), (by omega : paramAddr + 5 < 2 ^ w), hN]) ?_
      (by simp [Expr.size])
    exact ⟨rfl, by simp, by simp, by simp, by simp,
      fun r' hr' => by simp (disch := omega) only [Function.update_of_ne]⟩
  refine runs_start_le ?_
  dsimp only [gameLoadParamsStmt]
  refine runs_seq_triple_le h1 rfl ?_
  intro st1 ⟨h1_mem, h1_5, h1_6, h1_7, h1_8, h1_r⟩
  have h1_0 : st1.regs 0 = e := by rw [h1_r 0 (by omega), h0]
  have h1_2 : st1.regs 2 = paramAddr := by rw [h1_r 2 (by omega), h2]
  refine runs_seq_assign_le (v := bOut cfg M)
    (by simp [Expr.eval, BinOp.eval, h1_2, h1_mem, (by omega : 7 < 2 ^ w), (by omega : paramAddr + 7 < 2 ^ w), hb]) ?_
  refine runs_seq_assign_le (v := DOut cfg M r)
    (by simp [Expr.eval, BinOp.eval, h1_2, h1_mem, (by omega : 9 < 2 ^ w), (by omega : paramAddr + 9 < 2 ^ w), hD]) ?_
  refine runs_seq_assign_le (v := 49 * LParam M + 1)
    (by simp [Expr.eval, BinOp.eval, h1_2, h1_mem, (by omega : 11 < 2 ^ w), (by omega : paramAddr + 11 < 2 ^ w), hF]) ?_
  refine runs_seq_assign_le (v := 2 * e)
    (by simp [Expr.eval, BinOp.eval, h1_0, (by omega : 2 < 2 ^ w), (by omega : 2 * e < 2 ^ w)]) ?_
  refine runs_assign_le (v := e / DOut cfg M r)
    (by simp [Expr.eval, BinOp.eval, h1_0, (by omega : DOut cfg M r ≠ 0),
          (by have := Nat.div_le_self e (DOut cfg M r); omega : e / DOut cfg M r < 2 ^ w)]) ?_
    (by simp [Expr.size])
  exact ⟨h1_mem, by simp [h1_5], by simp [h1_6], by simp [h1_7], by simp [h1_8],
    by simp, by simp, by simp, by simp, by simp,
    fun r' hr' => by simp (disch := omega) only [Function.update_of_ne, h1_r r' hr']⟩

lemma gameAllocBufs_triple {w M e h : ℕ}
    (pProg : Program) (st₀ : State)
    (h4 : st₀.regs 4 = h) (h11 : st₀.regs 11 = 49 * LParam M + 1) (h12 : st₀.regs 12 = 2 * e)
    (hwH : h + outerGameBufSpace M e < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    let F := 49 * LParam M + 1
    let xPortAddr := h
    let wAddr := h + 1 + 2 * e
    let wEdgesAddr := wAddr + 2
    let fAddr := wEdgesAddr + 2 * F * e
    let coreOutAddr := fAddr + 2 * F * e
    let pairsAddr := coreOutAddr + 2 + 2 * e
    let routeOutAddr := pairsAddr + 3 + 2 * e
    let fRoundAddr := routeOutAddr + 2 + 4 * e
    let fLenAddr := fRoundAddr + 2 * e
    let hInit := fLenAddr + 1
    Triple w pProg (fun s => s = st₀) gameAllocBufsStmt
      (normalPost fun s' =>
        s'.mem = st₀.mem ∧
        s'.regs 15 = xPortAddr ∧ s'.regs 16 = wAddr ∧ s'.regs 17 = fAddr ∧
        s'.regs 18 = coreOutAddr ∧ s'.regs 19 = pairsAddr ∧ s'.regs 20 = routeOutAddr ∧
        s'.regs 21 = fRoundAddr ∧ s'.regs 22 = fLenAddr ∧ s'.regs 23 = wEdgesAddr ∧
        s'.regs 24 = 0 ∧ s'.regs 25 = 0 ∧ s'.regs 26 = hInit ∧ s'.regs 27 = F ∧
        hInit = h + outerGameBufSpace M e ∧
        (∀ r' ≤ 14, s'.regs r' = st₀.regs r'))
      (fun _ => 95) := by
  intro F xPortAddr wAddr wEdgesAddr fAddr coreOutAddr pairsAddr routeOutAddr fRoundAddr fLenAddr hInit
  intro s ω hs; subst s
  have hInit_eq : hInit = h + outerGameBufSpace M e := by
    simp only [hInit, fLenAddr, fRoundAddr, routeOutAddr, pairsAddr, coreOutAddr, fAddr,
      wEdgesAddr, wAddr, xPortAddr, F, outerGameBufSpace]
    ring
  have h2Fe : F * (2 * e) = 2 * F * e := by ring
  have hb1 : Triple w pProg (fun s => s = st₀)
      (.assign 15 (.reg 4) ;;
       .assign 16 (.bin .add (.bin .add (.reg 15) (.const 1)) (.reg 12)) ;;
       .assign 23 (.bin .add (.reg 16) (.const 2)) ;;
       .assign 28 (.bin .mul (.reg 11) (.reg 12)))
      (normalPost fun s' =>
        s'.mem = st₀.mem ∧ s'.regs 15 = xPortAddr ∧ s'.regs 16 = wAddr ∧
        s'.regs 23 = wEdgesAddr ∧ s'.regs 28 = 2 * F * e ∧
        (∀ r' ≤ 14, s'.regs r' = st₀.regs r'))
      (fun _ => 25) := by
    intro s1 ω1 hs1; subst s1
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := xPortAddr) (by simp [Expr.eval, h4, xPortAddr]) ?_
    refine runs_seq_assign_le (v := wAddr)
      (by simp [Expr.eval, BinOp.eval, h12, xPortAddr, wAddr, (by omega : 1 < 2 ^ w),
            (by omega : h + 1 < 2 ^ w), (by omega : h + 1 + 2 * e < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := wEdgesAddr)
      (by simp [Expr.eval, BinOp.eval, wAddr, wEdgesAddr, (by omega : 2 < 2 ^ w),
            (by omega : h + 1 + 2 * e + 2 < 2 ^ w)]) ?_
    refine runs_assign_le (v := 2 * F * e)
      (by simp [Expr.eval, BinOp.eval, h11, h12, F, h2Fe, (by omega : 2 * F * e < 2 ^ w)]) ?_
      (by simp [Expr.size])
    exact ⟨rfl, by simp, by simp, by simp, by simp,
      fun r' hr' => by simp (disch := omega) only [Function.update_of_ne]⟩
  refine runs_start_le ?_
  dsimp only [gameAllocBufsStmt]
  refine runs_seq_triple_le hb1 rfl ?_
  intro st1 ⟨h1_mem, h1_15, h1_16, h1_23, h1_28, h1_r⟩
  have hb2 : Triple w pProg (fun s => s = st1)
      (.assign 17 (.bin .add (.reg 23) (.reg 28)) ;;
       .assign 18 (.bin .add (.reg 17) (.reg 28)) ;;
       .assign 19 (.bin .add (.bin .add (.reg 18) (.const 2)) (.reg 12)) ;;
       .assign 20 (.bin .add (.bin .add (.reg 19) (.const 3)) (.reg 12)))
      (normalPost fun s' =>
        s'.mem = st₀.mem ∧ s'.regs 15 = xPortAddr ∧ s'.regs 16 = wAddr ∧
        s'.regs 17 = fAddr ∧ s'.regs 18 = coreOutAddr ∧ s'.regs 19 = pairsAddr ∧
        s'.regs 20 = routeOutAddr ∧ s'.regs 23 = wEdgesAddr ∧
        (∀ r' ≤ 14, s'.regs r' = st₀.regs r'))
      (fun _ => 30) := by
    intro s2 ω2 hs2; subst s2
    have h1_12 : st1.regs 12 = 2 * e := by rw [h1_r 12 (by omega), h12]
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := fAddr)
      (by simp [Expr.eval, BinOp.eval, h1_23, h1_28, fAddr, (by omega : fAddr < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := coreOutAddr)
      (by simp [Expr.eval, BinOp.eval, h1_28, coreOutAddr, (by omega : coreOutAddr < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := pairsAddr)
      (by simp [Expr.eval, BinOp.eval, h1_12, pairsAddr, (by omega : 2 < 2 ^ w),
            (by omega : coreOutAddr + 2 < 2 ^ w), (by omega : pairsAddr < 2 ^ w)]) ?_
    refine runs_assign_le (v := routeOutAddr)
      (by simp [Expr.eval, BinOp.eval, h1_12, routeOutAddr, (by omega : 3 < 2 ^ w),
            (by omega : pairsAddr + 3 < 2 ^ w), (by omega : routeOutAddr < 2 ^ w)]) ?_
      (by simp [Expr.size])
    exact ⟨h1_mem, by simp [h1_15], by simp [h1_16], by simp, by simp, by simp, by simp,
      by simp [h1_23], fun r' hr' => by simp (disch := omega) only [Function.update_of_ne, h1_r r' hr']⟩
  refine runs_seq_triple_le hb2 rfl ?_
  intro st2 ⟨h2_mem, h2_15, h2_16, h2_17, h2_18, h2_19, h2_20, h2_23, h2_r⟩
  have hb3 : Triple w pProg (fun s => s = st2)
      (.assign 21 (.bin .add (.bin .add (.reg 20) (.const 2)) (.bin .mul (.const 2) (.reg 12))) ;;
       .assign 22 (.bin .add (.reg 21) (.reg 12)) ;;
       .assign 26 (.bin .add (.reg 22) (.const 1)))
      (normalPost fun s' =>
        s'.mem = st₀.mem ∧ s'.regs 15 = xPortAddr ∧ s'.regs 16 = wAddr ∧
        s'.regs 17 = fAddr ∧ s'.regs 18 = coreOutAddr ∧ s'.regs 19 = pairsAddr ∧
        s'.regs 20 = routeOutAddr ∧ s'.regs 21 = fRoundAddr ∧ s'.regs 22 = fLenAddr ∧
        s'.regs 23 = wEdgesAddr ∧ s'.regs 26 = hInit ∧
        (∀ r' ≤ 14, s'.regs r' = st₀.regs r'))
      (fun _ => 25) := by
    intro s3 ω3 hs3; subst s3
    have h2_12 : st2.regs 12 = 2 * e := by rw [h2_r 12 (by omega), h12]
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := fRoundAddr)
      (by simp [Expr.eval, BinOp.eval, h2_20, h2_12, fRoundAddr, (by omega : 2 < 2 ^ w),
            (by omega : routeOutAddr + 2 < 2 ^ w), (by omega : 2 * (2 * e) < 2 ^ w),
            (by omega : routeOutAddr + 2 + 2 * (2 * e) < 2 ^ w)]; omega) ?_
    refine runs_seq_assign_le (v := fLenAddr)
      (by simp [Expr.eval, BinOp.eval, h2_12, fLenAddr, (by omega : fLenAddr < 2 ^ w)]) ?_
    refine runs_assign_le (v := hInit)
      (by simp [Expr.eval, BinOp.eval, hInit, (by omega : 1 < 2 ^ w), (by omega : hInit < 2 ^ w)]) ?_
      (by simp [Expr.size])
    exact ⟨h2_mem, by simp [h2_15], by simp [h2_16], by simp [h2_17], by simp [h2_18],
      by simp [h2_19], by simp [h2_20], by simp, by simp, by simp [h2_23], by simp,
      fun r' hr' => by simp (disch := omega) only [Function.update_of_ne, h2_r r' hr']⟩
  refine runs_seq_triple_le hb3 rfl ?_
  intro st3 ⟨h3_mem, h3_15, h3_16, h3_17, h3_18, h3_19, h3_20, h3_21, h3_22, h3_23, h3_26, h3_r⟩
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  refine runs_assign_le (v := F)
    (by simp [Expr.eval, h3_r 11 (by omega), h11, F]) ?_ (by simp [Expr.size])
  exact ⟨h3_mem, by simp [h3_15], by simp [h3_16], by simp [h3_17], by simp [h3_18],
    by simp [h3_19], by simp [h3_20], by simp [h3_21], by simp [h3_22], by simp [h3_23],
    by simp, by simp, by simp [h3_26], by simp, hInit_eq,
    fun r' hr' => by simp (disch := omega) only [Function.update_of_ne, h3_r r' hr']⟩

lemma gameInitBufs_triple {w e xPortAddr wAddr : ℕ}
    (pProg : Program) (st₀ : State)
    (h12 : st₀.regs 12 = 2 * e) (h15 : st₀.regs 15 = xPortAddr) (h16 : st₀.regs 16 = wAddr)
    (hdXW : DisjointRange xPortAddr (1 + 2 * e) wAddr 2)
    (hwX : xPortAddr + 1 + 2 * e < 2 ^ w) (hwW : wAddr + 2 < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀) gameInitBufsStmt
      (normalPost fun s' =>
        LenListAt s'.mem xPortAddr (List.range (2 * e)) ∧
        GraphAt s'.mem wAddr (Graph.mk (2 * e) []) ∧
        (∀ a, (a < xPortAddr ∨ xPortAddr + 1 + 2 * e ≤ a) →
          (a < wAddr ∨ wAddr + 2 ≤ a) → s'.mem a = st₀.mem a) ∧
        (∀ r' ≤ 27, s'.regs r' = st₀.regs r'))
      (fun _ => 50 * e + 40) := by
  intro s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  have h1 : Triple w pProg (fun s => s = st₀)
      (.store (.reg 15) (.reg 12) ;;
       .store (.reg 16) (.reg 12) ;;
       .store (.bin .add (.reg 16) (.const 1)) (.const 0))
      (normalPost fun s' =>
        s'.regs = st₀.regs ∧
        s'.mem xPortAddr = 2 * e ∧
        s'.mem wAddr = 2 * e ∧
        s'.mem (wAddr + 1) = 0 ∧
        (∀ a, a ≠ xPortAddr → a ≠ wAddr → a ≠ wAddr + 1 → s'.mem a = st₀.mem a))
      (fun _ => 20) := by
    intro s1 ω1 hs1; subst s1
    refine runs_start_le ?_
    refine runs_seq_store_le (x := xPortAddr) (v := 2 * e)
      (by simp [Expr.eval, h15]) (by simp [Expr.eval, h12]) ?_
    refine runs_seq_store_le (x := wAddr) (v := 2 * e)
      (by simp [Expr.eval, h16]) (by simp [Expr.eval, h12]) ?_
    refine runs_store_le (x := wAddr + 1) (v := 0)
      (by simp [Expr.eval, BinOp.eval, h16, hw1, (by omega : wAddr + 1 < 2 ^ w)])
      (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_ (by simp [Expr.size])
    have hneX1 : xPortAddr ≠ wAddr + 1 :=
      disjointRange_ne hdXW (by omega) (by omega) (by omega) (by omega)
    have hneX0 : xPortAddr ≠ wAddr :=
      disjointRange_ne hdXW (by omega) (by omega) (by omega) (by omega)
    exact ⟨rfl,
      by simp [Function.update_of_ne hneX1, Function.update_of_ne hneX0],
      by simp [Function.update_of_ne (by omega : wAddr ≠ wAddr + 1)],
      by simp,
      fun a h1 h2 h3 => by simp [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]⟩
  refine runs_start_le ?_
  dsimp only [gameInitBufsStmt]
  refine runs_seq_triple_le h1 rfl ?_
  intro st1 ⟨h1_regs, h1_x0, h1_w0, h1_w1, h1_fr⟩
  have hloop := Triple.forRange_const (p := pProg) (r := 28) (lo := .const 0) (hi := .reg 12)
    (body := .store (.bin .add (.bin .add (.reg 15) (.const 1)) (.reg 28)) (.reg 28))
    (P := fun s => s = st1)
    (Inv := fun i s =>
      s.regs 28 = i ∧
      ListAt s.mem (xPortAddr + 1) (List.range i) ∧
      (∀ a, a < xPortAddr + 1 ∨ xPortAddr + 1 + 2 * e ≤ a → s.mem a = st1.mem a) ∧
      (∀ r' ≤ 27, s.regs r' = st₀.regs r'))
    15 0 (2 * e) (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun s hs => by
      subst s
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun j hj => by simp at hj, fun _ _ => rfl,
        fun r' hr' => by simp [Function.update_of_ne (by omega : r' ≠ 28), h1_regs]⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hr12 : s.regs 12 = 2 * e := by rw [hi.2.2.2 12 (by omega), h12]
      simp [Expr.eval, hr12])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hL, hfr, hkr⟩
      have hr15 : s.regs 15 = xPortAddr := by rw [hkr 15 (by omega), h15]
      refine runs_start_le ?_
      refine runs_store_le (x := xPortAddr + 1 + i) (v := i)
        (by simp [Expr.eval, BinOp.eval, hr15, hiReg, hw1, (by omega : xPortAddr + 1 < 2 ^ w),
              (by omega : xPortAddr + 1 + i < 2 ^ w)])
        (by simp [Expr.eval, hiReg]) ?_ (by simp [Expr.size])
      refine ⟨⟨by simp, ?_, ?_, fun r' hr' => by
          simp [Function.update_of_ne (by omega : r' ≠ 28), hkr r' hr']⟩, by simp [hiReg]⟩
      · rw [List.range_succ]
        simpa [List.length_range] using hL.snoc i
      · intro a ha; dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha)
  refine runs_triple_le hloop rfl (fun o st2 h => by
    cases o with
    | returned _ => exact False.elim h
    | normal =>
      rcases h with ⟨_, h2_L, h2_fr, h2_kr⟩
      refine ⟨⟨by rw [h2_fr xPortAddr (Or.inl (by omega)), h1_x0, List.length_range], h2_L⟩, ?_, ?_, h2_kr⟩
      · intro i hi
        simp only [Graph.encode, Graph.m, List.flatMap_nil, List.length_cons, List.length_nil] at hi
        rcases i with _ | _ | i
        · simp [Graph.encode, h2_fr wAddr (Or.elim hdXW (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega))), h1_w0]
        · simp [Graph.encode, Graph.m,
            h2_fr (wAddr + 1) (Or.elim hdXW (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega))), h1_w1]
        · omega
      · intro a haX haW
        rw [h2_fr a (by omega), h1_fr a (by omega) (by omega) (by omega)])
    (by simp [Expr.size]; omega)

lemma graphAt_of_edgesAt {mem : ℕ → ℕ} {a n : ℕ} {es : List (ℕ × ℕ)}
    (hn : mem a = n) (hm : mem (a + 1) = es.length) (he : EdgesAt mem (a + 2) es) :
    GraphAt mem a (Graph.mk n es) := by
  have hflat : ∀ (l : List (ℕ × ℕ)) (i : ℕ) (hi : i < (l.flatMap fun e => [e.1, e.2]).length),
      (l.flatMap fun e => [e.1, e.2])[i]'hi =
        if i % 2 = 0 then (l[i / 2]'(by simp [List.length_flatMap] at hi; omega)).1
        else (l[i / 2]'(by simp [List.length_flatMap] at hi; omega)).2 := by
    intro l
    induction l with
    | nil => intro i hi; simp at hi
    | cons p t ih =>
      intro i hi
      rcases i with _ | _ | i
      · simp
      · simp
      · have hi' : i < (t.flatMap fun e => [e.1, e.2]).length := by
          simp [List.flatMap_cons] at hi ⊢; omega
        have h1 : ((p :: t).flatMap fun e => [e.1, e.2])[i + 2]'hi =
            (t.flatMap fun e => [e.1, e.2])[i]'hi' := by simp [List.flatMap_cons]
        rw [h1, ih i hi']
        have hmod : (i + 2) % 2 = i % 2 := by omega
        have hdiv : (i + 2) / 2 = i / 2 + 1 := by omega
        simp [hmod, hdiv]
  intro i hi
  rcases i with _ | _ | i
  · simpa [Graph.encode] using hn
  · simpa [Graph.encode, Graph.m] using hm
  · have hi' : i < (es.flatMap fun e => [e.1, e.2]).length := by
      simp only [Graph.encode, List.length_cons] at hi; omega
    have hdiv : i / 2 < es.length := by simp [List.length_flatMap] at hi'; omega
    have hEnc : (Graph.mk n es).encode[i + 2]'hi = (es.flatMap fun e => [e.1, e.2])[i]'hi' := by
      simp [Graph.encode]
    rw [hEnc, hflat es i hi']
    have hEd_i := he (i / 2) hdiv
    split_ifs with hmod
    · have haddr : a + (i + 2) = a + 2 + 2 * (i / 2) := by omega
      rw [haddr]; exact hEd_i.1
    · have haddr : a + (i + 2) = a + 2 + 2 * (i / 2) + 1 := by omega
      rw [haddr]; exact hEd_i.2

lemma gameAppendMatched_triple {w e wAddr wEdgesAddr fAddr routeListAddr fRoundAddr fLenAddr
    wLen fLen mM mF maxW maxF : ℕ}
    (pProg : Program) (st₀ : State)
    (W_edges F_edges M_edges F_round : List (ℕ × ℕ))
    (h16 : st₀.regs 16 = wAddr) (h17 : st₀.regs 17 = fAddr)
    (h21 : st₀.regs 21 = fRoundAddr) (h22 : st₀.regs 22 = fLenAddr)
    (h23 : st₀.regs 23 = wEdgesAddr) (h24 : st₀.regs 24 = wLen)
    (h25 : st₀.regs 25 = fLen) (h29 : st₀.regs 29 = mM) (h30 : st₀.regs 30 = routeListAddr)
    (hwEd_eq : wEdgesAddr = wAddr + 2)
    (hW_len : W_edges.length = wLen) (hF_len : F_edges.length = fLen)
    (hM_len : M_edges.length = mM) (hFr_len : F_round.length = mF)
    (hW_cap : wLen + mM + mF ≤ maxW) (hF_cap : fLen + mF ≤ maxF)
    (hW_g : GraphAt st₀.mem wAddr (Graph.mk (2 * e) W_edges))
    (hF_e : EdgesAt st₀.mem fAddr F_edges)
    (hM_e : EdgesAt st₀.mem routeListAddr M_edges)
    (hFr_e : EdgesAt st₀.mem fRoundAddr F_round)
    (hFr_l : st₀.mem fLenAddr = mF)
    (hdW_M : DisjointRange wAddr (2 + 2 * maxW) routeListAddr (2 * mM))
    (hdW_Fr : DisjointRange wAddr (2 + 2 * maxW) fRoundAddr (2 * mF))
    (hdW_Fl : DisjointRange wAddr (2 + 2 * maxW) fLenAddr 1)
    (hdW_F : DisjointRange wAddr (2 + 2 * maxW) fAddr (2 * maxF))
    (hdF_Fr : DisjointRange fAddr (2 * maxF) fRoundAddr (2 * mF))
    (hwW : wAddr + 2 + 2 * maxW < 2 ^ w)
    (hwF : fAddr + 2 * maxF < 2 ^ w)
    (hwM : routeListAddr + 2 * mM < 2 ^ w)
    (hwFr : fRoundAddr + 2 * mF < 2 ^ w)
    (hwFl : fLenAddr < 2 ^ w)
    (hw16 : 16 < 2 ^ w) :
    Triple w pProg (fun s => s = st₀) gameAppendMatchedStmt
      (normalPost fun s' =>
        GraphAt s'.mem wAddr (Graph.mk (2 * e) (W_edges ++ (M_edges ++ F_round))) ∧
        EdgesAt s'.mem fAddr (F_edges ++ F_round) ∧
        s'.regs 24 = wLen + mM + mF ∧
        s'.regs 25 = fLen + mF ∧
        (∀ a, (a < wAddr ∨ wAddr + 2 + 2 * maxW ≤ a) →
          (a < fAddr ∨ fAddr + 2 * maxF ≤ a) → s'.mem a = st₀.mem a) ∧
        (∀ r', r' ≤ 23 ∨ r' = 26 ∨ r' = 27 ∨ r' = 35 → s'.regs r' = st₀.regs r'))
      (fun _ => 70 * mM + 140 * mF + 100) := by
  intro s ω hs; subst s
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hW_n : st₀.mem wAddr = 2 * e := graphAt_n hW_g
  have hW_edges : EdgesAt st₀.mem wEdgesAddr W_edges := by
    rw [hwEd_eq]; exact graphAt_to_edgesAt hW_g
  refine runs_start_le ?_
  dsimp only [gameAppendMatchedStmt]
  -- 1. Append M_edges to wEdgesAddr
  refine runs_seq_triple_le
    (appendEdges_triple (w := w) (len := mM) (srcAddr := routeListAddr) (dstAddr := wEdgesAddr)
      (off := wLen) (rLen := 29) (rSrc := 30) (rDst := 23) (rOff := 24)
      (rI := 32) (rU := 33) (rV := 34) pProg st₀ W_edges M_edges (by decide)
      h29 h30 h23 h24 hM_len hW_len hW_edges hM_e
      (Or.elim hdW_M (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))
      hwM (by omega) hw2) rfl ?_
  intro st1 ⟨h1_Ed, h1_fr, h1_kr⟩
  -- 2. wLen += mM; mF := mem[fLenAddr]
  have hStep2 : Triple w pProg (fun s => s = st1)
      (.assign 24 (.bin .add (.reg 24) (.reg 29)) ;; .assign 31 (.load (.reg 22)))
      (normalPost fun s' =>
        s'.mem = st1.mem ∧ s'.regs 24 = wLen + mM ∧ s'.regs 31 = mF ∧
        (∀ r', r' ≠ 24 → r' ≠ 31 → s'.regs r' = st1.regs r'))
      (fun _ => 12) := by
    intro s2 ω2 hs2; subst s2
    have h1_24 : st1.regs 24 = wLen := by rw [h1_kr 24 (by omega) (by omega) (by omega), h24]
    have h1_29 : st1.regs 29 = mM := by rw [h1_kr 29 (by omega) (by omega) (by omega), h29]
    have h1_22 : st1.regs 22 = fLenAddr := by rw [h1_kr 22 (by omega) (by omega) (by omega), h22]
    have h1_fl : st1.mem fLenAddr = mF := by
      rw [h1_fr fLenAddr (Or.elim hdW_Fl (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega))), hFr_l]
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := wLen + mM)
      (by simp [Expr.eval, BinOp.eval, h1_24, h1_29, (by omega : wLen + mM < 2 ^ w)]) ?_
    refine runs_assign_le (v := mF)
      (by simp [Expr.eval, h1_22, h1_fl]) ?_ (by simp [Expr.size])
    exact ⟨rfl, by simp, by simp,
      fun r' h24' h31' => by simp [Function.update_of_ne h31', Function.update_of_ne h24']⟩
  refine runs_seq_triple_le hStep2 rfl ?_
  intro st2 ⟨h2_mem, h2_24, h2_31, h2_kr⟩
  have h2_Fr : EdgesAt st2.mem fRoundAddr F_round := by
    rw [h2_mem]; intro j hj
    have hj' : j < mF := by omega
    rw [h1_fr _ (Or.elim hdW_Fr (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega))),
        h1_fr _ (Or.elim hdW_Fr (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
    exact hFr_e j hj
  -- 3. Append F_round to wEdgesAddr
  refine runs_seq_triple_le
    (appendEdges_triple (w := w) (len := mF) (srcAddr := fRoundAddr) (dstAddr := wEdgesAddr)
      (off := wLen + mM) (rLen := 31) (rSrc := 21) (rDst := 23) (rOff := 24)
      (rI := 32) (rU := 33) (rV := 34) pProg st2 (W_edges ++ M_edges) F_round (by decide)
      h2_31 (by rw [h2_kr 21 (by omega) (by omega), h1_kr 21 (by omega) (by omega) (by omega), h21])
      (by rw [h2_kr 23 (by omega) (by omega), h1_kr 23 (by omega) (by omega) (by omega), h23])
      h2_24 hFr_len (by simp [hW_len, hM_len]) (h2_mem ▸ h1_Ed) h2_Fr
      (Or.elim hdW_Fr (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))
      hwFr (by omega) hw2) rfl ?_
  intro st3 ⟨h3_Ed, h3_fr, h3_kr⟩
  -- 4. wLen += mF; store mem[wAddr + 1] := wLen
  have hStep4 : Triple w pProg (fun s => s = st3)
      (.assign 24 (.bin .add (.reg 24) (.reg 31)) ;;
       .store (.bin .add (.reg 16) (.const 1)) (.reg 24))
      (normalPost fun s' =>
        s'.mem (wAddr + 1) = wLen + mM + mF ∧
        (∀ a, a ≠ wAddr + 1 → s'.mem a = st3.mem a) ∧
        s'.regs 24 = wLen + mM + mF ∧
        (∀ r', r' ≠ 24 → s'.regs r' = st3.regs r'))
      (fun _ => 12) := by
    intro s4 ω4 hs4; subst s4
    have h3_24 : st3.regs 24 = wLen + mM := by rw [h3_kr 24 (by omega) (by omega) (by omega), h2_24]
    have h3_31 : st3.regs 31 = mF := by rw [h3_kr 31 (by omega) (by omega) (by omega), h2_31]
    have h3_16 : st3.regs 16 = wAddr := by
      rw [h3_kr 16 (by omega) (by omega) (by omega), h2_kr 16 (by omega) (by omega),
          h1_kr 16 (by omega) (by omega) (by omega), h16]
    refine runs_start_le ?_
    refine runs_seq_assign_le (v := wLen + mM + mF)
      (by simp [Expr.eval, BinOp.eval, h3_24, h3_31, (by omega : wLen + mM + mF < 2 ^ w)]) ?_
    refine runs_store_le (x := wAddr + 1) (v := wLen + mM + mF)
      (by simp [Expr.eval, BinOp.eval, h3_16, hw1, (by omega : wAddr + 1 < 2 ^ w)])
      (by simp [Expr.eval]) ?_ (by simp [Expr.size])
    exact ⟨by simp, fun a ha => by simp [Function.update_of_ne ha], by simp,
      fun r' hr' => Function.update_of_ne hr' _ _⟩
  refine runs_seq_triple_le hStep4 rfl ?_
  intro st4 ⟨h4_mW, h4_fr, h4_24, h4_kr⟩
  have h4_F : EdgesAt st4.mem fAddr F_edges := by
    intro j hj
    have hj' : j < maxF := by omega
    rw [h4_fr _ (disjointRange_ne hdW_F (by omega) (by omega) (by omega) (by omega)).symm,
        h3_fr _ (Or.elim hdW_F (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega))),
        h2_mem,
        h1_fr _ (Or.elim hdW_F (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega))),
        h4_fr _ (disjointRange_ne hdW_F (by omega) (by omega) (by omega) (by omega)).symm,
        h3_fr _ (Or.elim hdW_F (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega))),
        h2_mem,
        h1_fr _ (Or.elim hdW_F (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
    exact hF_e j hj
  have h4_Fr : EdgesAt st4.mem fRoundAddr F_round := by
    intro j hj
    have hj' : j < mF := by omega
    rw [h4_fr _ (disjointRange_ne hdW_Fr (by omega) (by omega) (by omega) (by omega)).symm,
        h3_fr _ (Or.elim hdW_Fr (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega))),
        h4_fr _ (disjointRange_ne hdW_Fr (by omega) (by omega) (by omega) (by omega)).symm,
        h3_fr _ (Or.elim hdW_Fr (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
    exact h2_Fr j hj
  -- 5. Append F_round to fAddr
  refine runs_seq_triple_le
    (appendEdges_triple (w := w) (len := mF) (srcAddr := fRoundAddr) (dstAddr := fAddr)
      (off := fLen) (rLen := 31) (rSrc := 21) (rDst := 17) (rOff := 25)
      (rI := 32) (rU := 33) (rV := 34) pProg st4 F_edges F_round (by decide)
      (by rw [h4_kr 31 (by omega), h3_kr 31 (by omega) (by omega) (by omega), h2_31])
      (by rw [h4_kr 21 (by omega), h3_kr 21 (by omega) (by omega) (by omega),
              h2_kr 21 (by omega) (by omega), h1_kr 21 (by omega) (by omega) (by omega), h21])
      (by rw [h4_kr 17 (by omega), h3_kr 17 (by omega) (by omega) (by omega),
              h2_kr 17 (by omega) (by omega), h1_kr 17 (by omega) (by omega) (by omega), h17])
      (by rw [h4_kr 25 (by omega), h3_kr 25 (by omega) (by omega) (by omega),
              h2_kr 25 (by omega) (by omega), h1_kr 25 (by omega) (by omega) (by omega), h25])
      hFr_len hF_len h4_F h4_Fr
      (Or.elim hdF_Fr (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))
      hwFr (by omega) hw2) rfl ?_
  intro st5 ⟨h5_F, h5_fr, h5_kr⟩
  -- 6. fLen += mF
  refine runs_assign_le (v := fLen + mF)
    (by simp [Expr.eval, BinOp.eval, h5_kr 25 (by omega) (by omega) (by omega), h4_kr 25 (by omega),
          h3_kr 25 (by omega) (by omega) (by omega), h2_kr 25 (by omega) (by omega),
          h1_kr 25 (by omega) (by omega) (by omega), h25,
          h5_kr 31 (by omega) (by omega) (by omega), h4_kr 31 (by omega),
          h3_kr 31 (by omega) (by omega) (by omega), h2_31,
          (by omega : fLen + mF < 2 ^ w)]) ?_ (by simp [Expr.size]; omega)
  refine ⟨?_, h5_F, by simp [h5_kr 24 (by omega) (by omega) (by omega), h4_24], by simp, ?_, ?_⟩
  · -- GraphAt wAddr ⟨2 * e, W_edges ++ (M_edges ++ F_round)⟩
    have hAssoc : W_edges ++ (M_edges ++ F_round) = (W_edges ++ M_edges) ++ F_round :=
      (List.append_assoc _ _ _).symm
    rw [hAssoc]
    have hEd5 : EdgesAt st5.mem (wAddr + 2) ((W_edges ++ M_edges) ++ F_round) := by
      intro j hj
      have hj' : j < maxW := by simp [hW_len, hM_len, hFr_len] at hj; omega
      rw [h5_fr _ (Or.elim hdW_F (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega))),
          h4_fr _ (by omega),
          h5_fr _ (Or.elim hdW_F (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega))),
          h4_fr _ (by omega)]
      simpa [hwEd_eq] using h3_Ed j hj
    have hm5_0 : st5.mem wAddr = 2 * e := by
      rw [h5_fr wAddr (Or.elim hdW_F (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega))),
          h4_fr wAddr (by omega), h3_fr wAddr (Or.inl (by omega)), h2_mem,
          h1_fr wAddr (Or.inl (by omega)), hW_n]
    have hm5_1 : st5.mem (wAddr + 1) = ((W_edges ++ M_edges) ++ F_round).length := by
      rw [h5_fr (wAddr + 1) (Or.elim hdW_F (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega))),
          h4_mW]
      simp [List.length_append, hW_len, hM_len, hFr_len]; omega
    exact graphAt_of_edgesAt hm5_0 hm5_1 hEd5
  · intro a haW haF
    rw [h5_fr a (by omega), h4_fr a (by omega), h3_fr a (by omega), h2_mem, h1_fr a (by omega)]
  · intro r' hr'
    dsimp only
    rw [Function.update_of_ne (by omega : r' ≠ 25),
        h5_kr r' (by omega) (by omega) (by omega), h4_kr r' (by omega),
        h3_kr r' (by omega) (by omega) (by omega), h2_kr r' (by omega) (by omega),
        h1_kr r' (by omega) (by omega) (by omega)]

end MinCostFlow.ExpanderDecomp
