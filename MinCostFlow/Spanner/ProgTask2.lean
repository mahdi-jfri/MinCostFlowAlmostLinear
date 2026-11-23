module

public import MinCostFlow.Spanner.ProgTask1

/-!
# Word-RAM Task 2 program (`Algorithm 4`, lines 2–9)

This module defines the deterministic Word-RAM implementation `task2Module` of **Task 2** from
Algorithm 4 (`spanner.tex`, page 42) together with its memory layout (`Task2Input`, `Task2OutAt`),
runtime upper bound (`task2Cost`), and `WordRAM.Contract` (`task2Contract`).

To avoid scanning all `H'.n` vertices on each inner-loop congestion step, `t2BuildInc` precomputes
a vertex-to-component-edge incidence linked list `vHead` of total size `≤ ∑ eJ, |(embJH eJ).verts|`
using zero-initialized heap storage `[v1, ...)`. Each newly embedded path `P_J` adds `wWNum[eW]`
to `vcongNum[x]` (deduplicated per query via `eWVertStamp[x]`) and checks the exact integer
threshold `η₁ * tau1Int * phiDen_dec ≤ vcongNum[x]`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Task 2 input bounds, layout offsets, and contract predicates -/

/-- Bundled inputs for Word-RAM Task 2. -/
structure Task2Input where
  /-- Address of `GraphAt H'`. -/
  hAddr : ℕ
  /-- Address of `GraphAt J`. -/
  jAddr : ℕ
  /-- Address of `EmbAt embJH`. -/
  embJHAddr : ℕ
  /-- Output header address from Task 1 (`inp1.h`). -/
  t1OutAddr : ℕ
  /-- Free heap pointer returned by Task 1 (`v1`). -/
  v1 : ℕ
  /-- Host graph `H'`. -/
  H' : Graph
  /-- Input graph `J`. -/
  J : Graph
  /-- Embedding `Π_{J → H'}`. -/
  embJH : ℕ → Walk

namespace Task2Input

/-- Sum of `verts.length` over all `eJ < J.m` in `embJH`. -/
def embVertSum (inp : Task2Input) : ℕ :=
  ∑ eJ ∈ Finset.range inp.J.m, (inp.embJH eJ).verts.length

/-- Uniform upper cap on `φ_ds` path length bound `γ_J` for Task 2. -/
noncomputable def gammaJCap (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  impl.pathDS.params.gExp (Task1Input.dJCap impl J) (stripLoops J).m

/-- Uniform upper cap on the outer-round count `η₁` (`Claim 8.7` / `eta1Bound`). -/
noncomputable def eta1Cap (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  have cdeg := 2 * (impl.constructExpander.c_deg_int : ℝ)
  have φlb := impl.decompose.φ_lb (stripLoops J).m
  1 + ⌈2 * cdeg⌉₊ * (Nat.log 2 (⌈cdeg * (J.m : ℝ) / (2 * φlb)⌉₊ + 1) + 1)

/-- Uniform upper cap on `γExpInt = max(gExp_J, gExp_W)`. -/
noncomputable def gammaExpCap (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  have pds := impl.pathDS.params
  max (pds.gExp (Task1Input.dJCap impl J) (stripLoops J).m)
    (pds.gExp (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl J))

/-- Fixed 32-word control/output header at `inp.v1`. -/
def embWJAddr (inp : Task2Input) : ℕ := inp.v1 + 32

/-- Address of `dsHandles` array (`W.m` upper-bounded or `comps.length`). -/
def dsHandlesAddr (inp : Task2Input) (mW : ℕ) : ℕ := inp.embWJAddr + mW

/-- Address of `compEdgeBase` array. -/
def compEdgeBaseAddr (inp : Task2Input) (mW K : ℕ) : ℕ := inp.dsHandlesAddr mW + K

/-- Address of `vhatOffset` array. -/
def vhatOffsetAddr (inp : Task2Input) (mW K : ℕ) : ℕ := inp.compEdgeBaseAddr mW K + K

/-- Address of `compEdgeDelRound` array (size `J.m`). -/
def compEdgeDelRoundAddr (inp : Task2Input) (mW K : ℕ) : ℕ := inp.vhatOffsetAddr mW K + K

/-- Address of `vhatStamp` array (size `2 * J.m`). -/
def vhatStampAddr (inp : Task2Input) (mW K : ℕ) : ℕ := inp.compEdgeDelRoundAddr mW K + inp.J.m

/-- Address of `vHead` linked-list head array (size `H'.n`). -/
def vHeadAddr (inp : Task2Input) (mW K : ℕ) : ℕ := inp.vhatStampAddr mW K + 2 * inp.J.m

/-- Address of `vcongNum` array (size `H'.n`). -/
def vcongNumAddr (inp : Task2Input) (mW K : ℕ) : ℕ := inp.vHeadAddr mW K + inp.H'.n

/-- Address of `procStamp` array (size `H'.n`). -/
def procStampAddr (inp : Task2Input) (mW K : ℕ) : ℕ := inp.vcongNumAddr mW K + inp.H'.n

/-- Address of `eWVertStamp` array (size `H'.n`). -/
def eWVertStampAddr (inp : Task2Input) (mW K : ℕ) : ℕ := inp.procStampAddr mW K + inp.H'.n

/-- Address of congested-vertex `queue` array (size `H'.n`). -/
def queueAddr (inp : Task2Input) (mW K : ℕ) : ℕ := inp.eWVertStampAddr mW K + inp.H'.n

/-- Start address of `vHead` linked-list nodes (each 3 words). -/
def nodesAddr (inp : Task2Input) (mW K : ℕ) : ℕ := inp.queueAddr mW K + inp.H'.n

/-- Upper bound on the end of static Task 2 arrays + walk arena (before DS heap allocations). -/
noncomputable def staticEndCap (impl : SpannerToolImpl) (inp : Task2Input) : ℕ :=
  have mw := Task1Input.mwCap impl inp.J
  have γ := gammaExpCap impl inp.J
  inp.nodesAddr mw inp.J.m + 3 * inp.embVertSum + mw * (2 * γ + 5)

/-- Upper bound on the final heap end `v2` after Task 2. -/
noncomputable def maxHeapEnd (impl : SpannerToolImpl) (inp : Task2Input) : ℕ :=
  have m0 := (stripLoops inp.J).m
  have pdCap := Task1Input.phiDenCap impl inp.J
  have dJ := Task1Input.dJCap impl inp.J
  have mw := Task1Input.mwCap impl inp.J
  have η₁ := eta1Cap impl inp.J
  have pds := impl.pathDS.params
  have dsOne := pds.C_space * (pdCap + inp.J.n + m0 + m0 + pds.gExp dJ m0 + 2) ^ pds.c_space
  staticEndCap impl inp + η₁ * inp.J.m * dsOne + η₁ * inp.J.m * dsOne + mw * dsOne

/-- Maximum integer word value occurring in Task 2 arithmetic or addresses. -/
noncomputable def maxWordBound (impl : SpannerToolImpl) (inp : Task2Input) : ℕ :=
  have pdCap := Task1Input.phiDenCap impl inp.J
  have dJ := Task1Input.dJCap impl inp.J
  have mw := Task1Input.mwCap impl inp.J
  have dW := WitnessCoreInput.dWInt impl.constructExpander
  have pds := impl.pathDS.params
  have m0 := (stripLoops inp.J).m
  have γCap := gammaExpCap impl inp.J
  have γD := max (pds.gDel dJ m0) (pds.gDel dW mw)
  have φDsCap := max (pds.phiOutDen dJ m0) (pds.phiOutDen dW mw)
  have τ₁Cap :=
    2 * γCap * γD * φDsCap * (length inp.J inp.embJH + 1) *
      (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)
  have η₁ := eta1Cap impl inp.J
  max (maxHeapEnd impl inp + 3)
    (max (η₁ * τ₁Cap * pdCap + 2 * mw * maxDeg inp.J * pdCap + 2)
      (max (mw * γCap * (length inp.J inp.embJH + 1) + inp.embVertSum + 4)
        (η₁ * inp.J.m + 2 * mw + 2)))

/-- Word-width sufficiency condition for Task 2. -/
def WordWidthOK (impl : SpannerToolImpl) (inp : Task2Input) (w : ℕ) : Prop :=
  have m0 := (stripLoops inp.J).m
  have pdCap := Task1Input.phiDenCap impl inp.J
  have dJ := Task1Input.dJCap impl inp.J
  have pds := impl.pathDS.params
  1 < 2 ^ w ∧
    pds.cw * (Nat.log 2 (inp.J.n + m0 + pdCap + m0 + pds.gExp dJ m0 + 2) + 1) ≤ w ∧
      maxWordBound impl inp < 2 ^ w

/-- Precondition for running Word-RAM Task 2 on `[hAddr, jAddr, embJHAddr, t1OutAddr, v1]`. -/
def Valid (inp : Task2Input) (impl : SpannerToolImpl) (mem : ℕ → ℕ) (w : ℕ) : Prop :=
  inp.H'.IsValid ∧
    GraphAt mem inp.hAddr inp.H' ∧
      inp.J.IsValid ∧
        GraphAt mem inp.jAddr inp.J ∧
          IsEmbedding inp.J inp.H' inp.embJH ∧
            EmbAt mem inp.embJHAddr inp.J.m inp.embJH ∧
              EmbBounded mem inp.embJHAddr inp.J.m inp.embJH inp.t1OutAddr ∧
                inp.hAddr + inp.H'.encode.length ≤ inp.t1OutAddr ∧
                  inp.jAddr + inp.J.encode.length ≤ inp.t1OutAddr ∧
                    (∃ memPre, Task1OutAt impl inp.jAddr inp.t1OutAddr inp.H' inp.J inp.embJH memPre mem inp.v1 w) ∧
                      WordWidthOK impl inp w

end Task2Input

/-- Postcondition of Word-RAM Task 2 tying machine memory at `v1` to `WitnessData` and Corollary 8.8. -/
def Task2OutAt (impl : SpannerToolImpl) (inp : Task2Input) (mem₀ mem' : ℕ → ℕ) (v2 w : ℕ) : Prop :=
  ∃ (wInp : WitnessCoreInput) (WSubs : List Graph) (η₁ : ℕ) (embWJ : ℕ → Walk)
      (initCountJ initEdgesJ getPathCountJ deleteCountJ vcongUpdates innerIters1 : ℕ),
    let wd := wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs
    wInp.H' = inp.H' ∧
      (∀ e < inp.J.m, wInp.embJH e = inp.embJH e) ∧
        wInp.prep.J = inp.J ∧
          wInp.prep.jAddr = inp.jAddr ∧
            wInp.prep.StaticValid mem' w ∧
              wInp.ValidWSubs impl.constructExpander WSubs ∧
                (∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
                  WitnessOK tools inp.H' inp.J inp.embJH wd) ∧
                  (∀ x < inp.v1, mem' x = mem₀ x) ∧
                    ZeroFrom mem' v2 ∧
                      inp.v1 + 32 ≤ v2 ∧
                        v2 ≤ inp.maxHeapEnd impl ∧
                          mem' inp.v1 = inp.embWJAddr ∧
                            mem' (inp.v1 + 1) = η₁ ∧
                              mem' (inp.v1 + 2) = initCountJ ∧
                                mem' (inp.v1 + 3) = initEdgesJ ∧
                                  mem' (inp.v1 + 4) = getPathCountJ ∧
                                    mem' (inp.v1 + 5) = deleteCountJ ∧
                                      mem' (inp.v1 + 6) = vcongUpdates ∧
                                        mem' (inp.v1 + 7) = innerIters1 ∧
                                          mem' (inp.v1 + 8) = wd.W.m ∧
                                            mem' (inp.v1 + 9) = inp.H'.n ∧
                                              mem' (inp.v1 + 10) = wd.comps.length ∧
                                                mem' (inp.v1 + 11) = v2 ∧
                                                  EmbAt mem' inp.embWJAddr wd.W.m embWJ ∧
                                                    EmbBounded mem' inp.embWJAddr wd.W.m embWJ v2 ∧
                                                      1 ≤ η₁ ∧
                                                        η₁ ≤ eta1Bound wd inp.J ∧
                                                          IsEmbedding wd.W inp.J embWJ ∧
                                                            vcong wd.W inp.H' wd.wW (compose inp.J inp.embJH embWJ) ≤
                                                              (↑η₁ + 1 / 2) * wd.τ₁ ∧
                                                              vcong wd.W inp.H' wd.wW (compose inp.J inp.embJH embWJ) ≤
                                                                (↑(eta1Bound wd inp.J) + 1 / 2) * wd.τ₁ ∧
                                                                (length wd.W embWJ : ℝ) ≤ wd.γ_ExpPath ∧
                                                                  initCountJ = η₁ * wd.comps.length ∧
                                                                    initEdgesJ = η₁ * (wd.comps.map fun c => c.J_sub.m).sum ∧
                                                                      getPathCountJ = wd.W.m - wd.j0Edges.length ∧
                                                                        deleteCountJ ≤ η₁ * inp.J.m ∧
                                                                          (vcongUpdates : ℝ) ≤
                                                                            (getPathCountJ : ℝ) *
                                                                              (wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1)) ∧
                                                                            (innerIters1 : ℝ) ≤
                                                                              (getPathCountJ : ℝ) *
                                                                                (wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1)) ∧
    mem₀ (inp.t1OutAddr + 5) = wInp.h ∧
    wInp.OutputAt impl.constructExpander impl.pathDS.params
      (fun x => if x < wInp.h then mem₀ x else 0) mem₀ inp.v1 wd ∧
    mem₀ (inp.t1OutAddr + 3) = wInp.prep.decAddr ∧ wInp.prep.hEnd ≤ wInp.h

/-! ## Word-RAM sub-procedures for Task 2 -/

abbrev t2Add (a b : Expr) : Expr := Expr.bin BinOp.add a b
abbrev t2Sub (a b : Expr) : Expr := Expr.bin BinOp.sub a b
abbrev t2Mul (a b : Expr) : Expr := Expr.bin BinOp.mul a b
abbrev t2Lt (a b : Expr) : Expr := Expr.bin BinOp.lt a b
abbrev t2Eq (a b : Expr) : Expr := Expr.bin BinOp.eq a b
abbrev t2Ne (a b : Expr) : Expr := Expr.bin BinOp.eq (Expr.bin BinOp.eq a b) (Expr.const 0)
abbrev t2Le (a b : Expr) : Expr := Expr.bin BinOp.eq (Expr.bin BinOp.lt b a) (Expr.const 0)
abbrev t2Ld (base off : Expr) : Expr := Expr.load (t2Add base off)
abbrev t2St (base off val : Expr) : Stmt := Stmt.store (t2Add base off) val

/-- Sub-procedure `base + 1`: builds `compEdgeBase`, `vhatOffset`, and the `vHead` linked lists.
Arguments: `[v1, nodesAddr]`. Returns `nodesEnd`. -/
def t2BuildIncBody : Stmt :=
  Stmt.assign 2 (t2Ld (.reg 0) (.const 13)) ;;       -- prepH
  Stmt.assign 3 (t2Ld (.reg 2) (.const 2)) ;;        -- numComps
  Stmt.assign 4 (t2Ld (.reg 2) (.const 3)) ;;        -- aComps
  Stmt.assign 5 (t2Ld (.reg 0) (.const 16)) ;;       -- compEdgeBaseAddr
  Stmt.assign 6 (t2Ld (.reg 0) (.const 17)) ;;       -- vhatOffsetAddr
  Stmt.assign 7 (t2Ld (.reg 0) (.const 12)) ;;       -- embJHAddr
  Stmt.assign 8 (t2Ld (.reg 0) (.const 20)) ;;       -- vHeadAddr
  Stmt.assign 9 (.const 0) ;;                         -- ebase := 0
  Stmt.assign 10 (.const 0) ;;                        -- voff := 0
  Stmt.assign 11 (.reg 1) ;;                          -- nodesPtr := nodesAddr
  forRange 12 (.const 0) (.reg 3) (
    t2St (.reg 5) (.reg 12) (.reg 9) ;;
    t2St (.reg 6) (.reg 12) (.reg 10) ;;
    Stmt.assign 13 (t2Add (.reg 4) (t2Mul (.const 7) (.reg 12))) ;;
    Stmt.assign 14 (t2Ld (.reg 13) (.const 1)) ;;     -- cardX
    Stmt.assign 15 (t2Ld (.reg 13) (.const 4)) ;;     -- cJOrigPtr
    Stmt.assign 16 (t2Ld (.reg 13) (.const 6)) ;;     -- cJm
    Stmt.assign 9 (t2Add (.reg 9) (.reg 16)) ;;
    Stmt.assign 10 (t2Add (.reg 10) (.reg 14)) ;;
    forRange 17 (.const 0) (.reg 16) (
      Stmt.assign 18 (t2Ld (.reg 15) (.reg 17)) ;;   -- eJ
      Stmt.assign 19 (t2Ld (.reg 7) (.reg 18)) ;;    -- walkPtr
      Stmt.assign 20 (.load (.reg 19)) ;;             -- vertsLen
      forRange 21 (.const 0) (.reg 20) (
        Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;; -- x
        Stmt.assign 23 (t2Ld (.reg 8) (.reg 22)) ;;   -- oldHead
        Stmt.store (.reg 11) (.reg 12) ;;
        t2St (.reg 11) (.const 1) (.reg 17) ;;
        t2St (.reg 11) (.const 2) (.reg 23) ;;
        t2St (.reg 8) (.reg 22) (.reg 11) ;;
        Stmt.assign 11 (t2Add (.reg 11) (.const 3))
      )
    )
  ) ;;
  Stmt.ret (.reg 11)

/-- Sub-procedure `base + 2`: embeds `j0Edges` as single-edge walks and populates initial `vcongNum`.
Arguments: `[v1, jAddr, arenaAddr]`. Returns updated `arenaPtr`. -/
def t2InitJ0Body : Stmt :=
  Stmt.assign 3 (t2Ld (.reg 0) (.const 13)) ;;        -- prepH
  Stmt.assign 4 (.load (.reg 3)) ;;                   -- j0Len
  Stmt.assign 5 (t2Ld (.reg 3) (.const 1)) ;;         -- aJ0Out
  Stmt.assign 6 (.load (.reg 0)) ;;                   -- embWJAddr
  Stmt.assign 7 (t2Ld (.reg 0) (.const 14)) ;;        -- wH
  Stmt.assign 8 (t2Ld (.reg 7) (.const 14)) ;;        -- wWNumAddr
  Stmt.assign 9 (t2Ld (.reg 0) (.const 12)) ;;        -- embJHAddr
  Stmt.assign 10 (t2Ld (.reg 0) (.const 21)) ;;       -- vcongNumAddr
  Stmt.assign 11 (t2Ld (.reg 0) (.const 23)) ;;       -- eWVertStampAddr
  Stmt.assign 12 (.reg 2) ;;                          -- arenaPtr
  forRange 13 (.const 0) (.reg 4) (
    Stmt.assign 14 (t2Ld (.reg 5) (.reg 13)) ;;       -- jOrig
    Stmt.assign 15 (t2Ld (.reg 1) (t2Add (.const 2) (t2Mul (.const 2) (.reg 14)))) ;; -- u
    Stmt.assign 16 (t2Ld (.reg 1) (t2Add (.const 3) (t2Mul (.const 2) (.reg 14)))) ;; -- v
    Stmt.store (.reg 12) (.const 2) ;;
    t2St (.reg 12) (.const 1) (.reg 15) ;;
    t2St (.reg 12) (.const 2) (.reg 16) ;;
    t2St (.reg 12) (.const 3) (.const 1) ;;
    t2St (.reg 12) (.const 4) (.reg 14) ;;
    t2St (.reg 6) (.reg 13) (.reg 12) ;;
    Stmt.assign 12 (t2Add (.reg 12) (.const 5)) ;;
    Stmt.assign 17 (t2Add (.reg 13) (.const 1)) ;;     -- stamp := eW + 1
    Stmt.assign 18 (t2Ld (.reg 8) (.reg 13)) ;;       -- wWNum[eW]
    Stmt.assign 19 (t2Ld (.reg 9) (.reg 14)) ;;       -- walkPtr
    Stmt.assign 20 (.load (.reg 19)) ;;               -- vertsLen
    forRange 21 (.const 0) (.reg 20) (
      Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;; -- x
      Stmt.cond (t2Ne (t2Ld (.reg 11) (.reg 22)) (.reg 17)) (
        t2St (.reg 11) (.reg 22) (.reg 17) ;;
        t2St (.reg 10) (.reg 22) (t2Add (t2Ld (.reg 10) (.reg 22)) (.reg 18))
      ) Stmt.nop
    )
  ) ;;
  t2St (.reg 0) (.const 25) (.reg 12) ;;
  t2St (.reg 0) (.const 26) (.reg 4) ;;
  Stmt.ret (.reg 12)

/-- Sub-procedure `base + 4`: drains the congested-vertex queue, calling `ds.delete` on each active
incident component edge and marking newly deleted vertices in `vhatStamp`.
Arguments: `[v1, h_cur]`. Returns updated `h_cur`. -/
def t2DrainQueueBody (dsBase : ℕ) : Stmt :=
  Stmt.assign 2 (t2Ld (.reg 0) (.const 27)) ;;        -- qTail
  Stmt.assign 3 (t2Ld (.reg 0) (.const 1)) ;;         -- η₁
  Stmt.assign 4 (t2Ld (.reg 0) (.const 24)) ;;        -- queueAddr
  Stmt.assign 5 (t2Ld (.reg 0) (.const 20)) ;;        -- vHeadAddr
  Stmt.assign 6 (t2Ld (.reg 0) (.const 16)) ;;        -- compEdgeBaseAddr
  Stmt.assign 7 (t2Ld (.reg 0) (.const 18)) ;;        -- compEdgeDelRoundAddr
  Stmt.assign 8 (t2Ld (.reg 0) (.const 17)) ;;        -- vhatOffsetAddr
  Stmt.assign 9 (t2Ld (.reg 0) (.const 19)) ;;        -- vhatStampAddr
  Stmt.assign 10 (t2Ld (.reg 0) (.const 15)) ;;       -- dsHandlesAddr
  Stmt.assign 11 (.reg 1) ;;                          -- h_cur
  t2St (.reg 0) (.const 7) (t2Add (t2Ld (.reg 0) (.const 7)) (.reg 2)) ;; -- innerIters1 += qTail
  forRange 12 (.const 0) (.reg 2) (
    Stmt.assign 13 (t2Ld (.reg 4) (.reg 12)) ;;       -- x
    Stmt.assign 14 (t2Ld (.reg 5) (.reg 13)) ;;       -- nodePtr := vHead[x]
    Stmt.loop (.reg 14) (
      Stmt.assign 15 (.load (.reg 14)) ;;             -- ci
      Stmt.assign 16 (t2Ld (.reg 14) (.const 1)) ;;   -- b
      Stmt.assign 17 (t2Add (t2Ld (.reg 6) (.reg 15)) (.reg 16)) ;; -- delIdx
      Stmt.cond (t2Lt (t2Ld (.reg 7) (.reg 17)) (.reg 3)) (
        t2St (.reg 7) (.reg 17) (.reg 3) ;;
        t2St (.reg 0) (.const 5) (t2Add (t2Ld (.reg 0) (.const 5)) (.const 1)) ;;
        Stmt.assign 18 (t2Ld (.reg 10) (.reg 15)) ;;  -- dsHandle
        Stmt.assign 19 (.reg 11) ;;                   -- save h_cur
        Stmt.call 11 (dsBase + 1) [.reg 18, .reg 16, .reg 11] ;;
        Stmt.assign 20 (.load (.reg 19)) ;;           -- L.length
        Stmt.assign 21 (t2Ld (.reg 8) (.reg 15)) ;;   -- voff
        forRange 22 (.const 0) (.reg 20) (
          Stmt.assign 23 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 22))) ;;
          t2St (.reg 9) (t2Add (.reg 21) (.reg 23)) (.reg 3)
        )
      ) Stmt.nop ;;
      Stmt.assign 14 (t2Ld (.reg 14) (.const 2))
    )
  ) ;;
  t2St (.reg 0) (.const 27) (.const 0) ;;
  Stmt.ret (.reg 11)

/-- Sub-procedure `base + 3`: queries `ds.getPath` for `(ci, eL)`, lifts to `P_J` into `embWJ`,
updates `vcongNum`, enqueues newly congested vertices, and calls `t2DrainQueue` (`drainBase`).
Arguments: `[v1, ci, eL, eW, h_cur]`. Returns updated `h_cur`. -/
def t2MiddleEdgeBody (dsBase drainBase : ℕ) : Stmt :=
  Stmt.assign 5 (t2Ld (.reg 0) (.const 13)) ;;        -- prepH
  Stmt.assign 6 (t2Ld (.reg 5) (.const 3)) ;;         -- aComps
  Stmt.assign 7 (t2Add (.reg 6) (t2Mul (.const 7) (.reg 1))) ;;
  Stmt.assign 8 (t2Ld (.reg 7) (.const 2)) ;;         -- cVertsPtr
  Stmt.assign 9 (t2Ld (.reg 7) (.const 4)) ;;         -- cJOrigPtr
  Stmt.assign 10 (t2Ld (.reg 0) (.const 14)) ;;       -- wH
  Stmt.assign 11 (t2Add (t2Ld (.reg 10) (.const 12)) (t2Mul (.const 6) (.reg 1))) ;;
  Stmt.assign 12 (t2Ld (.reg 11) (.const 1)) ;;       -- wSubPtr
  Stmt.assign 13 (t2Ld (.reg 12) (t2Add (.const 2) (t2Mul (.const 2) (.reg 2)))) ;; -- u_loc
  Stmt.assign 14 (t2Ld (.reg 12) (t2Add (.const 3) (t2Mul (.const 2) (.reg 2)))) ;; -- v_loc
  Stmt.assign 15 (t2Ld (.reg 0) (.const 15)) ;;       -- dsHandlesAddr
  Stmt.assign 16 (t2Ld (.reg 15) (.reg 1)) ;;         -- dsHandle
  Stmt.assign 17 (.reg 4) ;;                          -- saved h_cur (P_sub)
  Stmt.call 4 (dsBase + 2) [.reg 16, .reg 13, .reg 14, .reg 4] ;;
  Stmt.assign 18 (t2Ld (.reg 0) (.const 25)) ;;       -- arenaPtr (P_J)
  Stmt.assign 19 (.load (.reg 17)) ;;                 -- vertsLen
  Stmt.assign 20 (t2Add (t2Add (.reg 17) (.const 1)) (.reg 19)) ;; -- P_sub edgesLen addr
  Stmt.assign 21 (.load (.reg 20)) ;;                 -- edgesLen
  Stmt.store (.reg 18) (.reg 19) ;;
  forRange 22 (.const 0) (.reg 19) (
    Stmt.assign 23 (t2Ld (.reg 17) (t2Add (.const 1) (.reg 22))) ;;
    t2St (.reg 18) (t2Add (.const 1) (.reg 22)) (t2Ld (.reg 8) (.reg 23))
  ) ;;
  Stmt.assign 24 (t2Add (t2Add (.reg 18) (.const 1)) (.reg 19)) ;; -- P_J edgesLen addr
  Stmt.store (.reg 24) (.reg 21) ;;
  Stmt.assign 25 (t2Add (t2Ld (.reg 0) (.const 26)) (.const 1)) ;; -- queryId
  t2St (.reg 0) (.const 26) (.reg 25) ;;
  Stmt.assign 26 (t2Ld (t2Ld (.reg 10) (.const 14)) (.reg 3)) ;; -- wWNum[eW]
  Stmt.assign 27 (t2Ld (.reg 0) (.const 12)) ;;       -- embJHAddr
  Stmt.assign 28 (t2Ld (.reg 0) (.const 23)) ;;       -- eWVertStampAddr
  Stmt.assign 29 (t2Ld (.reg 0) (.const 21)) ;;       -- vcongNumAddr
  Stmt.assign 30 (t2Ld (.reg 0) (.const 22)) ;;       -- procStampAddr
  Stmt.assign 31 (t2Ld (.reg 0) (.const 28)) ;;       -- thresh
  Stmt.assign 32 (t2Ld (.reg 0) (.const 1)) ;;        -- η₁
  Stmt.assign 33 (t2Ld (.reg 0) (.const 24)) ;;       -- queueAddr
  Stmt.assign 34 (.const 0) ;;                        -- qTail := 0
  Stmt.assign 35 (.const 0) ;;                        -- updVerts := 0
  forRange 22 (.const 0) (.reg 21) (
    Stmt.assign 36 (t2Ld (.reg 20) (t2Add (.const 1) (.reg 22))) ;;
    Stmt.assign 37 (t2Ld (.reg 9) (.reg 36)) ;;       -- eJ
    t2St (.reg 24) (t2Add (.const 1) (.reg 22)) (.reg 37) ;;
    Stmt.assign 38 (t2Ld (.reg 27) (.reg 37)) ;;      -- walkPtr
    Stmt.assign 39 (.load (.reg 38)) ;;               -- eVertsLen
    Stmt.assign 35 (t2Add (.reg 35) (.reg 39)) ;;
    forRange 40 (.const 0) (.reg 39) (
      Stmt.assign 41 (t2Ld (.reg 38) (t2Add (.const 1) (.reg 40))) ;; -- x
      Stmt.cond (t2Ne (t2Ld (.reg 28) (.reg 41)) (.reg 25)) (
        t2St (.reg 28) (.reg 41) (.reg 25) ;;
        Stmt.assign 42 (t2Add (t2Ld (.reg 29) (.reg 41)) (.reg 26)) ;;
        t2St (.reg 29) (.reg 41) (.reg 42) ;;
        Stmt.cond (t2Lt (t2Ld (.reg 30) (.reg 41)) (.reg 32)) (
          Stmt.cond (t2Le (.reg 31) (.reg 42)) (
            t2St (.reg 30) (.reg 41) (.reg 32) ;;
            t2St (.reg 33) (.reg 34) (.reg 41) ;;
            Stmt.assign 34 (t2Add (.reg 34) (.const 1))
          ) Stmt.nop
        ) Stmt.nop
      ) Stmt.nop
    )
  ) ;;
  t2St (.load (.reg 0)) (.reg 3) (.reg 18) ;;         -- embWJ[eW] := P_J ptr
  t2St (.reg 0) (.const 25) (t2Add (t2Add (.reg 24) (.const 1)) (.reg 21)) ;;
  t2St (.reg 0) (.const 4) (t2Add (t2Ld (.reg 0) (.const 4)) (.const 1)) ;;
  t2St (.reg 0) (.const 6) (t2Add (t2Ld (.reg 0) (.const 6)) (.reg 35)) ;;
  t2St (.reg 0) (.const 30) (t2Sub (t2Ld (.reg 0) (.const 30)) (.const 1)) ;;
  t2St (.reg 0) (.const 27) (.reg 34) ;;
  Stmt.call 4 drainBase [.reg 0, .reg 4] ;;
  Stmt.ret (.reg 4)

/-- Main Task 2 procedure (`base + 0`).
Arguments: `[hAddr, jAddr, embJHAddr, t1OutAddr, v1]`. Returns `v2`. -/
def task2Body (selfBase dsBase : ℕ) : Stmt :=
  Stmt.assign 5 (t2Ld (.reg 3) (.const 4)) ;;         -- prepH
  Stmt.assign 6 (t2Ld (.reg 3) (.const 5)) ;;         -- wH
  Stmt.assign 7 (.load (.reg 0)) ;;                   -- nH
  Stmt.assign 8 (t2Ld (.reg 1) (.const 1)) ;;         -- mJ
  Stmt.assign 9 (.load (.reg 5)) ;;                   -- j0Len
  Stmt.assign 10 (t2Ld (.reg 5) (.const 2)) ;;        -- numComps
  Stmt.assign 11 (t2Ld (.reg 6) (.const 13)) ;;       -- wAddr
  Stmt.assign 12 (t2Ld (.reg 11) (.const 1)) ;;       -- mW
  Stmt.assign 13 (t2Ld (.reg 6) (.const 8)) ;;        -- γExpInt
  Stmt.assign 14 (t2Ld (.reg 6) (.const 10)) ;;       -- tau1Int
  Stmt.assign 15 (t2Ld (.reg 6) (.const 18)) ;;       -- phiDen_dec
  -- Compute layout pointers in header at `r4` (`v1`)
  Stmt.assign 16 (t2Add (.reg 4) (.const 32)) ;;       -- embWJAddr
  Stmt.store (.reg 4) (.reg 16) ;;
  t2St (.reg 4) (.const 8) (.reg 12) ;;
  t2St (.reg 4) (.const 9) (.reg 7) ;;
  t2St (.reg 4) (.const 10) (.reg 10) ;;
  t2St (.reg 4) (.const 12) (.reg 2) ;;
  t2St (.reg 4) (.const 13) (.reg 5) ;;
  t2St (.reg 4) (.const 14) (.reg 6) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 12)) ;;        -- dsHandlesAddr
  t2St (.reg 4) (.const 15) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 10)) ;;        -- compEdgeBaseAddr
  t2St (.reg 4) (.const 16) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 10)) ;;        -- vhatOffsetAddr
  t2St (.reg 4) (.const 17) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 10)) ;;        -- compEdgeDelRoundAddr
  t2St (.reg 4) (.const 18) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 8)) ;;         -- vhatStampAddr
  t2St (.reg 4) (.const 19) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (t2Mul (.const 2) (.reg 8))) ;; -- vHeadAddr
  t2St (.reg 4) (.const 20) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 7)) ;;         -- vcongNumAddr
  t2St (.reg 4) (.const 21) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 7)) ;;         -- procStampAddr
  t2St (.reg 4) (.const 22) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 7)) ;;         -- eWVertStampAddr
  t2St (.reg 4) (.const 23) (.reg 16) ;;
  Stmt.assign 16 (t2Add (.reg 16) (.reg 7)) ;;         -- queueAddr
  t2St (.reg 4) (.const 24) (.reg 16) ;;
  Stmt.assign 17 (t2Add (.reg 16) (.reg 7)) ;;         -- nodesAddr
  t2St (.reg 4) (.const 29) (t2Mul (.reg 14) (.reg 15)) ;; -- tau1MulPhi
  t2St (.reg 4) (.const 30) (t2Sub (.reg 12) (.reg 9)) ;; -- unemb
  t2St (.reg 4) (.const 31) (.reg 15) ;;
  -- Build incidence lists & embed J0 edges
  Stmt.call 16 (selfBase + 1) [.reg 4, .reg 17] ;;    -- r16 := nodesEnd = arenaAddr
  Stmt.assign 18 (t2Add (.reg 16) (t2Mul (.reg 12) (t2Add (t2Mul (.const 2) (.reg 13)) (.const 5)))) ;;
  Stmt.call 17 (selfBase + 2) [.reg 4, .reg 1, .reg 16] ;;
  -- Loop-invariant caches in r31..r37
  Stmt.assign 31 (t2Ld (.reg 5) (.const 3)) ;;        -- aComps
  Stmt.assign 32 (t2Ld (.reg 6) (.const 12)) ;;       -- aCompExt
  Stmt.assign 33 (t2Ld (.reg 6) (.const 17)) ;;       -- phiNum_dec
  Stmt.assign 34 (.reg 15) ;;                         -- phiDen_dec
  Stmt.assign 35 (t2Ld (.reg 6) (.const 19)) ;;       -- m0
  Stmt.assign 36 (t2Ld (.reg 4) (.const 15)) ;;       -- dsHandlesAddr
  Stmt.assign 37 (t2Ld (.reg 4) (.const 17)) ;;       -- vhatOffsetAddr
  Stmt.assign 38 (.load (.reg 4)) ;;                  -- embWJAddr
  Stmt.assign 39 (t2Ld (.reg 4) (.const 19)) ;;       -- vhatStampAddr
  Stmt.assign 40 (t2Ld (.reg 4) (.const 29)) ;;       -- tau1MulPhi
  Stmt.assign 19 (.const 1) ;;                        -- do-while flag
  Stmt.loop (.reg 19) (
    Stmt.assign 41 (t2Add (t2Ld (.reg 4) (.const 1)) (.const 1)) ;; -- η₁
    t2St (.reg 4) (.const 1) (.reg 41) ;;
    t2St (.reg 4) (.const 28) (t2Mul (.reg 41) (.reg 40)) ;;
    t2St (.reg 4) (.const 2) (t2Add (t2Ld (.reg 4) (.const 2)) (.reg 10)) ;;
    forRange 20 (.const 0) (.reg 10) (
      Stmt.assign 21 (t2Add (.reg 31) (t2Mul (.const 7) (.reg 20))) ;;
      Stmt.assign 22 (t2Ld (.reg 21) (.const 3)) ;;   -- cJSubPtr
      Stmt.assign 23 (t2Ld (.reg 21) (.const 6)) ;;   -- cJm
      t2St (.reg 4) (.const 3) (t2Add (t2Ld (.reg 4) (.const 3)) (.reg 23)) ;;
      t2St (.reg 36) (.reg 20) (.reg 18) ;;
      Stmt.call 18 dsBase [.reg 22, .reg 33, .reg 34, .reg 35, .reg 18]
    ) ;;
    forRange 20 (.const 0) (.reg 10) (
      Stmt.assign 21 (t2Add (.reg 32) (t2Mul (.const 6) (.reg 20))) ;;
      Stmt.assign 22 (.load (.reg 21)) ;;             -- wStart
      Stmt.assign 23 (t2Ld (.reg 21) (.const 1)) ;;   -- wSubPtr
      Stmt.assign 24 (t2Ld (.reg 21) (.const 5)) ;;   -- cWm
      Stmt.assign 25 (t2Ld (.reg 37) (.reg 20)) ;;   -- voff
      forRange 27 (.const 0) (.reg 24) (
        Stmt.assign 28 (t2Add (.reg 22) (.reg 27)) ;; -- eW
        Stmt.cond (t2Eq (t2Ld (.reg 38) (.reg 28)) (.const 0)) (
          Stmt.assign 29 (t2Ld (.reg 23) (t2Add (.const 2) (t2Mul (.const 2) (.reg 27)))) ;;
          Stmt.assign 30 (t2Ld (.reg 23) (t2Add (.const 3) (t2Mul (.const 2) (.reg 27)))) ;;
          Stmt.cond (t2Lt (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 29))) (.reg 41)) (
            Stmt.cond (t2Lt (t2Ld (.reg 39) (t2Add (.reg 25) (.reg 30))) (.reg 41)) (
              Stmt.call 18 (selfBase + 3) [.reg 4, .reg 20, .reg 27, .reg 28, .reg 18]
            ) Stmt.nop
          ) Stmt.nop
        ) Stmt.nop
      )
    ) ;;
    Stmt.assign 19 (t2Ld (.reg 4) (.const 30))
  ) ;;
  t2St (.reg 4) (.const 11) (.reg 18) ;;
  Stmt.ret (.reg 18)

/-- Five-procedure Task 2 module at `[selfBase, selfBase + 5)`, calling `dsBase .. dsBase + 2`. -/
def task2Module (selfBase dsBase : ℕ) : List Stmt :=
  [ task2Body selfBase dsBase
  , t2BuildIncBody
  , t2InitJ0Body
  , t2MiddleEdgeBody dsBase (selfBase + 4)
  , t2DrainQueueBody dsBase ]

theorem task2Module_noRand (selfBase dsBase : ℕ) :
    ∀ s ∈ task2Module selfBase dsBase, s.NoRand := by
  intro s hs
  simp only [task2Module, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    simp [task2Body, t2BuildIncBody, t2InitJ0Body, t2MiddleEdgeBody, t2DrainQueueBody,
      forRange, forUp, Stmt.NoRand]

/-! ## Task 2 cost bound and contract -/

/-- Worst-case Word-RAM cost bound for `task2Module`. -/
noncomputable def task2Cost (impl : SpannerToolImpl) (J : Graph) (lenJH evs : ℕ) : ℕ :=
  have m := J.m
  have m0 := (stripLoops J).m
  have pds := impl.pathDS.params
  have dJ := Task1Input.dJCap impl J
  have mw := Task1Input.mwCap impl J
  have η₁ := Task2Input.eta1Cap impl J
  have γJ := pds.gExp dJ m0
  have γJq := pds.gQuery dJ m0
  η₁ * (m * ⌈pds.K_init * γJ⌉₊ + m * ⌈pds.K_del * γJq⌉₊ + 400 * m + 100 * mw + 80 * evs + 250) +
    mw * (⌈pds.K_query * γJq⌉₊ + 200 * γJ * (lenJH + 1) + 600) +
    250 * m + 200 * evs + 600

open Classical in
/-- `WordRAM.Contract` for Word-RAM Task 2. -/
noncomputable def task2Contract (impl : SpannerToolImpl) (w : ℕ) : Contract :=
  { pre := fun args mem =>
      ∃ inp : Task2Input,
        args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.t1OutAddr, inp.v1] ∧
          inp.Valid impl mem w
    post := fun args mem v2 mem' =>
      ∀ inp : Task2Input,
        args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.t1OutAddr, inp.v1] →
          inp.Valid impl mem w →
            Task2OutAt impl inp mem mem' v2 w
    cost := fun args mem =>
      if h : ∃ inp : Task2Input,
          args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.t1OutAddr, inp.v1] ∧
            inp.Valid impl mem w then
        let inp := Classical.choose h
        task2Cost impl inp.J (length inp.J inp.embJH) inp.embVertSum
      else 0 }

end MinCostFlow.Spanner
