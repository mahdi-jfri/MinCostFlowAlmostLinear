module

public import MinCostFlow.LSF.Program.BatchBFSMath
import Mathlib.Tactic.Linarith

/-!
# Lock-Step Dual-BFS Definitions and Micro-Step Verification (`BatchBFSBase`)

Defines `splitCompBFSProc`, its sub-statements, `splitCompBFSContract`, `SideMemAt`, and proves
`bfsMicroStep_triple`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Sub-statements and main procedure -/

/-- One BFS micro-step on a single side `(rQBuf, rVis, rQHead, rQTail, rCurHe)`, reading graph
base addresses from `r12 = extToInt`, `r13 = intToExt`, `r14 = incHead`, `r15 = eTailSlot`,
`r16 = eHeadSlot`, `r17 = heNext`, and using scratch registers `r29..r32`. -/
def bfsMicroStepStmt (rQBuf rVis rQHead rQTail rCurHe : ℕ) : Stmt :=
  .cond (.reg rCurHe)
    (.assign 29 (.bin .sub (.reg rCurHe) (.const 1)) ;;
     .assign rCurHe (.load (.bin .add (.reg 17) (.reg 29))) ;;
     .assign 30 (.bin .div (.reg 29) (.const 2)) ;;
     .cond (.bin .mod (.reg 29) (.const 2))
       (.assign 31 (.load (.bin .add (.reg 15) (.reg 30))))
       (.assign 31 (.load (.bin .add (.reg 16) (.reg 30)))) ;;
     .assign 32 (.load (.bin .add (.reg 13) (.reg 31))) ;;
     .cond (.load (.bin .add (.reg rVis) (.reg 32)))
       .nop
       (.store (.bin .add (.reg rVis) (.reg 32)) (.const 1) ;;
        .store (.bin .add (.reg rQBuf) (.reg rQTail)) (.reg 32) ;;
        .assign rQTail (.bin .add (.reg rQTail) (.const 1))))
    (.assign 32 (.load (.bin .add (.reg rQBuf) (.reg rQHead))) ;;
     .assign rQHead (.bin .add (.reg rQHead) (.const 1)) ;;
     .assign 31 (.load (.bin .add (.reg 12) (.reg 32))) ;;
     .assign rCurHe (.load (.bin .add (.reg 14) (.reg 31))))

/-- Lock-step iteration body: checks whether either side A (`r22..r24`) or side B (`r25..r27`) has
finished; if so sets `r28 := 0`, otherwise advances both sides by one micro-step. -/
def bfsLockStepBody : Stmt :=
  .cond (.bin .add (.reg 24) (.bin .sub (.reg 23) (.reg 22)))
    (.cond (.bin .add (.reg 27) (.bin .sub (.reg 26) (.reg 25)))
      (bfsMicroStepStmt 18 20 22 23 24 ;;
       bfsMicroStepStmt 19 21 25 26 27)
      (.assign 28 (.const 0)))
    (.assign 28 (.const 0))

/-- Relabels `compId[qBuf[i]] := r10` (`root2`) for `0 ≤ i < rQTail`, using `r29 = compIdBase`
and loop counter `r32`. -/
def relabelCompStmt (rQBuf rQTail : ℕ) : Stmt :=
  forRange 32 (.const 0) (.reg rQTail)
    (.store (.bin .add (.reg 29) (.load (.bin .add (.reg rQBuf) (.reg 32)))) (.reg 10))

/-- Clears `vis[qBuf[i]] := 0` for `0 ≤ i < rQTail`, using loop counter `r32`. -/
def clearVisStmt (rQBuf rVis rQTail : ℕ) : Stmt :=
  forRange 32 (.const 0) (.reg rQTail)
    (.store (.bin .add (.reg rVis) (.load (.bin .add (.reg rQBuf) (.reg 32)))) (.const 0))

/-- Relabels the finished smaller side `(rQBufS, rVisS, rQTailS)` to `root2` (`r10`), and updates
`compSize` (`r31`) and `compRoot` (`r30`) for `root2` (`r10`) and `oldCid` (`r8`). -/
def finishSideStmt (rQBufS rVisS rQTailS : ℕ) : Stmt :=
  relabelCompStmt rQBufS rQTailS ;;
  .store (.bin .add (.reg 31) (.reg 10)) (.reg rQTailS) ;;
  .store (.bin .add (.reg 31) (.reg 8)) (.bin .sub (.reg 11) (.reg rQTailS)) ;;
  .cond (.load (.bin .add (.reg rVisS) (.reg 10)))
    (.store (.bin .add (.reg 30) (.reg 10)) (.reg 10) ;;
     .store (.bin .add (.reg 30) (.reg 8)) (.reg 9))
    (.store (.bin .add (.reg 30) (.reg 10)) (.reg 9) ;;
     .store (.bin .add (.reg 30) (.reg 8)) (.reg 10))

/-- Setup prefix of `splitCompBFSProc`: computes the six `dgFPtr` array bases in `r12..r17`,
loads `qBufA, qBufB, visA, visB` from `auxPtr` into `r18..r21`, and seeds both BFS queues. -/
def bfsSetupStmt : Stmt :=
  .assign 12 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 3))) ;;
  .assign 13 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 3))) ;;
  .assign 14 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 6) (.reg 3))) ;;
  .assign 15 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 3)))
    (.bin .mul (.const 3) (.reg 4))) ;;
  .assign 16 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 3)))
    (.bin .mul (.const 4) (.reg 4))) ;;
  .assign 17 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 3)))
    (.bin .mul (.const 7) (.reg 4))) ;;
  .assign 18 (.load (.bin .add (.reg 2) (.const auxOffQBufAPtr))) ;;
  .assign 19 (.load (.bin .add (.reg 2) (.const auxOffQBufBPtr))) ;;
  .assign 20 (.load (.bin .add (.reg 2) (.const auxOffVisAPtr))) ;;
  .assign 21 (.load (.bin .add (.reg 2) (.const auxOffVisBPtr))) ;;
  .store (.reg 18) (.reg 6) ;;
  .store (.bin .add (.reg 20) (.reg 6)) (.const 1) ;;
  .assign 22 (.const 0) ;;
  .assign 23 (.const 1) ;;
  .assign 24 (.const 0) ;;
  .store (.reg 19) (.reg 7) ;;
  .store (.bin .add (.reg 21) (.reg 7)) (.const 1) ;;
  .assign 25 (.const 0) ;;
  .assign 26 (.const 1) ;;
  .assign 27 (.const 0) ;;
  .assign 28 (.const 1)

/-- Dual lock-step BFS component split procedure:
`args = [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, uA, uB, oldCid, root1, root2, newSum]`. -/
def splitCompBFSProc : Stmt :=
  bfsSetupStmt ;;
  .loop (.reg 28) bfsLockStepBody ;;
  .assign 29 (.load (.bin .add (.reg 1) (.const fOffCompIdPtr))) ;;
  .assign 30 (.load (.bin .add (.reg 1) (.const fOffCompRootPtr))) ;;
  .assign 31 (.load (.bin .add (.reg 1) (.const fOffCompSizePtr))) ;;
  .cond (.bin .add (.reg 24) (.bin .sub (.reg 23) (.reg 22)))
    (finishSideStmt 19 21 26)
    (finishSideStmt 18 20 23) ;;
  clearVisStmt 18 20 23 ;;
  clearVisStmt 19 21 26 ;;
  .ret (.const 0)

lemma splitCompBFSProc_noRand : splitCompBFSProc.NoRand := by
  simp [splitCompBFSProc, bfsSetupStmt, bfsLockStepBody, bfsMicroStepStmt, finishSideStmt,
    relabelCompStmt, clearVisStmt, forRange, forUp, Stmt.NoRand]

/-! ## Contract specification -/

/-- Contract for `splitCompBFSProc`:
`args = [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, uA, uB, oldCid, root1, root2, newSum]`. -/
noncomputable def splitCompBFSContract (w : ℕ) (F : MGraph) : Contract where
  pre args mem :=
    open Classical in
    ∃ dgFPtr fAncPtr auxPtr vCap eCapF n0 uA uB oldCid root1 root2 newSum,
      args = [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, uA, uB, oldCid, root1, root2, newSum] ∧
      16 ≤ 2 ^ w ∧
      dgFPtr + dynGraphSize vCap eCapF ≤ fAncPtr ∧
      fAncPtr + fAncSize vCap ≤ auxPtr ∧
      auxPtr + auxSize vCap n0 < 2 ^ w ∧
      F.IsForest ∧
      DynGraphAt mem dgFPtr vCap eCapF F ∧
      mem (fAncPtr + fOffCompIdPtr) = fCompIdBase fAncPtr vCap ∧
      mem (fAncPtr + fOffCompRootPtr) = fCompRootBase fAncPtr vCap ∧
      mem (fAncPtr + fOffCompSizePtr) = fCompSizeBase fAncPtr vCap ∧
      mem (auxPtr + auxOffQBufAPtr) = auxQBufABase auxPtr vCap n0 ∧
      mem (auxPtr + auxOffQBufBPtr) = auxQBufBBase auxPtr vCap n0 ∧
      mem (auxPtr + auxOffVisAPtr) = auxVisABase auxPtr vCap n0 ∧
      mem (auxPtr + auxOffVisBPtr) = auxVisBBase auxPtr vCap n0 ∧
      (∀ v < vCap, mem (auxVisABase auxPtr vCap n0 + v) = 0 ∧
        mem (auxVisBBase auxPtr vCap n0 + v) = 0) ∧
      uA ∈ F.V ∧ uB ∈ F.V ∧ ¬ F.Connected uA uB ∧
      oldCid < vCap ∧ root1 < vCap ∧ root2 < vCap ∧ oldCid ≠ root2 ∧
      ((F.Connected root1 uA ∧ F.Connected root2 uB) ∨
        (F.Connected root1 uB ∧ F.Connected root2 uA)) ∧
      newSum = (F.V.filter fun v => F.Connected v uA).card +
        (F.V.filter fun v => F.Connected v uB).card
  post args mem ret mem' :=
    open Classical in
    ∃ dgFPtr fAncPtr auxPtr vCap eCapF n0 uA uB oldCid root1 root2 newSum,
      args = [dgFPtr, fAncPtr, auxPtr, vCap, eCapF, n0, uA, uB, oldCid, root1, root2, newSum] ∧
      ret = 0 ∧
      (∀ a, ¬ (fCompIdBase fAncPtr vCap ≤ a ∧ a < fCompSizeBase fAncPtr vCap + vCap) →
            ¬ (auxQBufABase auxPtr vCap n0 ≤ a ∧ a < auxQBufBBase auxPtr vCap n0 + vCap) →
            mem' a = mem a) ∧
      ∃ Csmall Cbig : Finset ℕ,
        ((Csmall = F.V.filter (fun v => F.Connected v uA) ∧
          Cbig = F.V.filter (fun v => F.Connected v uB)) ∨
         (Csmall = F.V.filter (fun v => F.Connected v uB) ∧
          Cbig = F.V.filter (fun v => F.Connected v uA))) ∧
        Csmall.card ≤ Cbig.card ∧
        (∀ v < vCap, mem' (fCompIdBase fAncPtr vCap + v) =
          if v ∈ Csmall then root2 else mem (fCompIdBase fAncPtr vCap + v)) ∧
        (∀ c < vCap, c ≠ oldCid → c ≠ root2 →
          mem' (fCompRootBase fAncPtr vCap + c) = mem (fCompRootBase fAncPtr vCap + c) ∧
          mem' (fCompSizeBase fAncPtr vCap + c) = mem (fCompSizeBase fAncPtr vCap + c)) ∧
        mem' (fCompSizeBase fAncPtr vCap + root2) = Csmall.card ∧
        mem' (fCompSizeBase fAncPtr vCap + oldCid) = Cbig.card ∧
        ((root2 ∈ Csmall ∧
            mem' (fCompRootBase fAncPtr vCap + root2) = root2 ∧
            mem' (fCompRootBase fAncPtr vCap + oldCid) = root1) ∨
         (root2 ∉ Csmall ∧
            mem' (fCompRootBase fAncPtr vCap + root2) = root1 ∧
            mem' (fCompRootBase fAncPtr vCap + oldCid) = root2))
  cost args _ :=
    open Classical in
    let uA := args.getD 6 0
    let uB := args.getD 7 0
    600 * min (F.E.filter fun e => F.Connected (F.tail e) uA).card
              (F.E.filter fun e => F.Connected (F.tail e) uB).card + 700

/-! ## Helper invariants and Triples -/

/-- Memory state of one BFS side `(qBuf, vis)` representing queue `q` with capacity `vCap`. -/
def SideMemAt (mem : ℕ → ℕ) (qBuf vis vCap : ℕ) (q : List ℕ) : Prop :=
  open Classical in
  ListAt mem qBuf q ∧
  ∀ v < vCap, mem (vis + v) = if v ∈ q then 1 else 0

lemma SideMemAt.of_agree {mem mem' : ℕ → ℕ} {qBuf vis vCap : ℕ} {q : List ℕ}
    (h : SideMemAt mem qBuf vis vCap q)
    (hq : ∀ i < vCap, mem' (qBuf + i) = mem (qBuf + i))
    (hv : ∀ v < vCap, mem' (vis + v) = mem (vis + v))
    (hlen : q.length ≤ vCap) :
    SideMemAt mem' qBuf vis vCap q := by
  classical
  refine ⟨fun i hi => (hq i (lt_of_lt_of_le hi hlen)).trans (h.1 i hi),
    fun v hvlt => (hv v hvlt).trans (h.2 v hvlt)⟩

/-- Helper bound: any nodup list of vertices in `F.V` has length `≤ vCap`, and strictly `< vCap`
if there is a vertex `y ∈ F.V` not in `q`. -/
lemma list_len_lt_vCap {F : MGraph} {vCap y : ℕ} {q : List ℕ}
    (hvCap : ∀ v ∈ F.V, v < vCap) (hnd : q.Nodup) (hsub : ∀ v ∈ q, v ∈ F.V)
    (hyV : y ∈ F.V) (hyNot : y ∉ q) :
    q.length < vCap := by
  classical
  have hsub' : insert y q.toFinset ⊆ Finset.range vCap := by
    intro v hv
    rw [Finset.mem_range]
    rcases Finset.mem_insert.mp hv with rfl | hvq
    · exact hvCap v hyV
    · exact hvCap v (hsub v (List.mem_toFinset.mp hvq))
  have hcard := Finset.card_le_card hsub'
  rw [Finset.card_insert_of_notMem (by simp [hyNot]), List.toFinset_card_of_nodup hnd,
    Finset.card_range] at hcard
  omega

lemma list_len_le_vCap {F : MGraph} {vCap : ℕ} {q : List ℕ}
    (hvCap : ∀ v ∈ F.V, v < vCap) (hnd : q.Nodup) (hsub : ∀ v ∈ q, v ∈ F.V) :
    q.length ≤ vCap := by
  classical
  have hsub' : q.toFinset ⊆ Finset.range vCap := fun v hv =>
    Finset.mem_range.mpr (hvCap v (hsub v (List.mem_toFinset.mp hv)))
  have hcard := Finset.card_le_card hsub'
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at hcard
  exact hcard

/-- One micro-step of BFS advances `(q, qHead, remHe, steps)` to `(q', qHead', remHe', steps + 1)`,
modifying memory only inside `[qBuf, qBuf + vCap) ∪ [vis, vis + vCap)` and registers only in
`{rQHead, rQTail, rCurHe, 29, 30, 31, 32}`, in at most `65` steps. -/
lemma bfsMicroStep_triple {w dgFPtr vCap eCapF qBuf vis u₀ qHead steps : ℕ}
    {rQBuf rVis rQHead rQTail rCurHe : ℕ}
    {p : Program} {mem0 mem_in regs_in : ℕ → ℕ} {F : MGraph} {incL : ℕ → List ℕ} {q remHe : List ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hr_dist : [12, 13, 14, 15, 16, 17, 29, 30, 31, 32, rQBuf, rVis, rQHead, rQTail, rCurHe].Nodup)
    (hdg_ltw : dgFPtr + dynGraphSize vCap eCapF < 2 ^ w)
    (hqBuf_disj_dg : dgFPtr + dynGraphSize vCap eCapF ≤ qBuf)
    (hvis_disj_dg : dgFPtr + dynGraphSize vCap eCapF ≤ vis)
    (hq_disj_vis : qBuf + vCap ≤ vis ∨ vis + vCap ≤ qBuf)
    (hqBuf_ltw : qBuf + vCap < 2 ^ w)
    (hvis_ltw : vis + vCap < 2 ^ w)
    (hFval : F.IsValid)
    (hvCap : ∀ v ∈ F.V, v < vCap) (heCap : ∀ e ∈ F.E, e < eCapF)
    (hExtToInt : ∀ v ∈ F.V,
      mem0 (dgExtToIntBase dgFPtr vCap + v) ∈ F.V ∧
      mem0 (dgIntToExtBase dgFPtr vCap + mem0 (dgExtToIntBase dgFPtr vCap + v)) = v)
    (_hIntToExt : ∀ s ∈ F.V,
      mem0 (dgIntToExtBase dgFPtr vCap + s) ∈ F.V ∧
      mem0 (dgExtToIntBase dgFPtr vCap + mem0 (dgIntToExtBase dgFPtr vCap + s)) = s)
    (hEndSlot : ∀ e ∈ F.E,
      mem0 (dgETailSlotBase dgFPtr vCap eCapF + e) = mem0 (dgExtToIntBase dgFPtr vCap + F.tail e) ∧
      mem0 (dgEHeadSlotBase dgFPtr vCap eCapF + e) = mem0 (dgExtToIntBase dgFPtr vCap + F.head e))
    (hincL : ∀ s < vCap,
      IsDoublyLinkedList mem0 (dgHePrevBase dgFPtr vCap eCapF) (dgHeNextBase dgFPtr vCap eCapF)
        (dgIncHeadBase dgFPtr vCap + s) (2 * eCapF) (incL s) ∧
      mem0 (dgSlotDegBase dgFPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCapF ∧ h / 2 ∈ F.E ∧
        (if h % 2 = 0 then mem0 (dgExtToIntBase dgFPtr vCap + F.tail (h / 2))
         else mem0 (dgExtToIntBase dgFPtr vCap + F.head (h / 2))) = s)
    (hB : BfsInv F (fun v => mem0 (dgExtToIntBase dgFPtr vCap + v)) incL u₀ q qHead remHe steps)
    (hnotDone : remHe ≠ [] ∨ qHead < q.length) :
    Triple w p
      (fun st =>
        st.mem = mem_in ∧ st.regs = regs_in ∧
        (∀ a, a < dgFPtr + dynGraphSize vCap eCapF → st.mem a = mem0 a) ∧
        SideMemAt st.mem qBuf vis vCap q ∧
        DllTailAt st.mem (dgHeNextBase dgFPtr vCap eCapF) (2 * eCapF) remHe (st.regs rCurHe) ∧
        st.regs 12 = dgExtToIntBase dgFPtr vCap ∧
        st.regs 13 = dgIntToExtBase dgFPtr vCap ∧
        st.regs 14 = dgIncHeadBase dgFPtr vCap ∧
        st.regs 15 = dgETailSlotBase dgFPtr vCap eCapF ∧
        st.regs 16 = dgEHeadSlotBase dgFPtr vCap eCapF ∧
        st.regs 17 = dgHeNextBase dgFPtr vCap eCapF ∧
        st.regs rQBuf = qBuf ∧ st.regs rVis = vis ∧
        st.regs rQHead = qHead ∧ st.regs rQTail = q.length)
      (bfsMicroStepStmt rQBuf rVis rQHead rQTail rCurHe)
      (normalPost fun st' =>
        ∃ q' qHead' remHe',
          BfsInv F (fun v => mem0 (dgExtToIntBase dgFPtr vCap + v)) incL u₀ q' qHead' remHe' (steps + 1) ∧
          SideMemAt st'.mem qBuf vis vCap q' ∧
          DllTailAt st'.mem (dgHeNextBase dgFPtr vCap eCapF) (2 * eCapF) remHe' (st'.regs rCurHe) ∧
          st'.regs rQHead = qHead' ∧ st'.regs rQTail = q'.length ∧
          (∀ a, ¬ (qBuf ≤ a ∧ a < qBuf + vCap) → ¬ (vis ≤ a ∧ a < vis + vCap) →
            st'.mem a = mem_in a) ∧
          (∀ r, r ≠ rQHead → r ≠ rQTail → r ≠ rCurHe →
            r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 32 → st'.regs r = regs_in r))
      (fun _ => 65) := by
  classical
  -- Extract pairwise register inequalities from `hr_dist`
  have hne : ∀ i j (hi : i < 15) (hj : j < 15), i ≠ j →
      ([12, 13, 14, 15, 16, 17, 29, 30, 31, 32, rQBuf, rVis, rQHead, rQTail, rCurHe][i]'(by simpa using hi)) ≠
      ([12, 13, 14, 15, 16, 17, 29, 30, 31, 32, rQBuf, rVis, rQHead, rQTail, rCurHe][j]'(by simpa using hj)) := by
    intro i j hi hj hij
    exact fun h => hij ((hr_dist.getElem_inj_iff).mp h)
  have h12_29 : (12 : ℕ) ≠ 29 := by decide
  have h13_29 : (13 : ℕ) ≠ 29 := by decide
  have h13_30 : (13 : ℕ) ≠ 30 := by decide
  have h13_31 : (13 : ℕ) ≠ 31 := by decide
  have h14_31 : (14 : ℕ) ≠ 31 := by decide
  have h14_32 : (14 : ℕ) ≠ 32 := by decide
  have h15_29 : (15 : ℕ) ≠ 29 := by decide
  have h15_30 : (15 : ℕ) ≠ 30 := by decide
  have h16_29 : (16 : ℕ) ≠ 29 := by decide
  have h16_30 : (16 : ℕ) ≠ 30 := by decide
  have h17_29 : (17 : ℕ) ≠ 29 := by decide
  have hrQBuf_32 : rQBuf ≠ 32 := hne 10 9 (by decide) (by decide) (by decide)
  have hrQBuf_rVis : rQBuf ≠ rVis := hne 10 11 (by decide) (by decide) (by decide)
  have hrQBuf_rQH : rQBuf ≠ rQHead := hne 10 12 (by decide) (by decide) (by decide)
  have hrQBuf_rQT : rQBuf ≠ rQTail := hne 10 13 (by decide) (by decide) (by decide)
  have hrQBuf_rCH : rQBuf ≠ rCurHe := hne 10 14 (by decide) (by decide) (by decide)
  have hrQBuf_29 : rQBuf ≠ 29 := hne 10 6 (by decide) (by decide) (by decide)
  have hrQBuf_30 : rQBuf ≠ 30 := hne 10 7 (by decide) (by decide) (by decide)
  have hrQBuf_31 : rQBuf ≠ 31 := hne 10 8 (by decide) (by decide) (by decide)
  have hrVis_29 : rVis ≠ 29 := hne 11 6 (by decide) (by decide) (by decide)
  have hrVis_30 : rVis ≠ 30 := hne 11 7 (by decide) (by decide) (by decide)
  have hrVis_31 : rVis ≠ 31 := hne 11 8 (by decide) (by decide) (by decide)
  have hrVis_32 : rVis ≠ 32 := hne 11 9 (by decide) (by decide) (by decide)
  have hrVis_rCH : rVis ≠ rCurHe := hne 11 14 (by decide) (by decide) (by decide)
  have hrQH_32 : rQHead ≠ 32 := hne 12 9 (by decide) (by decide) (by decide)
  have hrQH_31 : rQHead ≠ 31 := hne 12 8 (by decide) (by decide) (by decide)
  have hrQH_rCH : rQHead ≠ rCurHe := hne 12 14 (by decide) (by decide) (by decide)
  have hrQT_29 : rQTail ≠ 29 := hne 13 6 (by decide) (by decide) (by decide)
  have hrQT_30 : rQTail ≠ 30 := hne 13 7 (by decide) (by decide) (by decide)
  have hrQT_31 : rQTail ≠ 31 := hne 13 8 (by decide) (by decide) (by decide)
  have hrQT_32 : rQTail ≠ 32 := hne 13 9 (by decide) (by decide) (by decide)
  have hrQT_rCH : rQTail ≠ rCurHe := hne 13 14 (by decide) (by decide) (by decide)
  have hrCH_13 : rCurHe ≠ 13 := hne 14 1 (by decide) (by decide) (by decide)
  have hrCH_15 : rCurHe ≠ 15 := hne 14 3 (by decide) (by decide) (by decide)
  have hrCH_16 : rCurHe ≠ 16 := hne 14 4 (by decide) (by decide) (by decide)
  have hrCH_17 : rCurHe ≠ 17 := hne 14 5 (by decide) (by decide) (by decide)
  have hrCH_29 : rCurHe ≠ 29 := hne 14 6 (by decide) (by decide) (by decide)
  have h29_rCH : (29 : ℕ) ≠ rCurHe := hrCH_29.symm
  have hrCH_30 : rCurHe ≠ 30 := hne 14 7 (by decide) (by decide) (by decide)
  have hrCH_31 : rCurHe ≠ 31 := hne 14 8 (by decide) (by decide) (by decide)
  have hrCH_32 : rCurHe ≠ 32 := hne 14 9 (by decide) (by decide) (by decide)
  have h15_rCH : (15 : ℕ) ≠ rCurHe := hrCH_15.symm
  have h16_rCH : (16 : ℕ) ≠ rCurHe := hrCH_16.symm
  have h17_rCH : (17 : ℕ) ≠ rCurHe := hrCH_17.symm
  have h12_rQH : (12 : ℕ) ≠ rQHead := hne 0 12 (by decide) (by decide) (by decide)
  have h14_rQH : (14 : ℕ) ≠ rQHead := hne 2 12 (by decide) (by decide) (by decide)
  have hrQH_29 : rQHead ≠ 29 := hne 12 6 (by decide) (by decide) (by decide)
  have hrQH_30 : rQHead ≠ 30 := hne 12 7 (by decide) (by decide) (by decide)
  have hrQT_rQH : rQTail ≠ rQHead := hne 13 12 (by decide) (by decide) (by decide)
  have hrQH_rQT : rQHead ≠ rQTail := hrQT_rQH.symm
  -- Address bounds for `dgFPtr`
  have hExt_lt : dgExtToIntBase dgFPtr vCap + vCap ≤ dgFPtr + dynGraphSize vCap eCapF := by
    dsimp [dgExtToIntBase, dynGraphSize]; omega
  have hInt_lt : dgIntToExtBase dgFPtr vCap + vCap ≤ dgFPtr + dynGraphSize vCap eCapF := by
    dsimp [dgIntToExtBase, dynGraphSize]; omega
  have hInc_lt : dgIncHeadBase dgFPtr vCap + vCap ≤ dgFPtr + dynGraphSize vCap eCapF := by
    dsimp [dgIncHeadBase, dynGraphSize]; omega
  have hETail_lt : dgETailSlotBase dgFPtr vCap eCapF + eCapF ≤ dgFPtr + dynGraphSize vCap eCapF := by
    dsimp [dgETailSlotBase, dynGraphSize]; omega
  have hEHead_lt : dgEHeadSlotBase dgFPtr vCap eCapF + eCapF ≤ dgFPtr + dynGraphSize vCap eCapF := by
    dsimp [dgEHeadSlotBase, dynGraphSize]; omega
  have hHeNext_lt : dgHeNextBase dgFPtr vCap eCapF + 2 * eCapF ≤ dgFPtr + dynGraphSize vCap eCapF := by
    dsimp [dgHeNextBase, dynGraphSize]; omega
  intro st ω ⟨hm_in, hr_in, hdgAg, hSide, hDll, h12, h13, h14, h15, h16, h17, hrQB, hrV, hrQH, hrQT⟩
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hm_in hr_in hdgAg hSide hDll h12 h13 h14 h15 h16 h17 hrQB hrV hrQH hrQT
  subst mem_in; subst regs_in
  suffices h : ∃ o st' c,
      Runs w p ω (bfsMicroStepStmt rQBuf rVis rQHead rQTail rCurHe)
        { mem := stm, regs := str, pos := stp } o st' c ∧
      normalPost (fun st' =>
        ∃ q' qHead' remHe',
          BfsInv F (fun v => mem0 (dgExtToIntBase dgFPtr vCap + v)) incL u₀ q' qHead' remHe' (steps + 1) ∧
          SideMemAt st'.mem qBuf vis vCap q' ∧
          DllTailAt st'.mem (dgHeNextBase dgFPtr vCap eCapF) (2 * eCapF) remHe' (st'.regs rCurHe) ∧
          st'.regs rQHead = qHead' ∧ st'.regs rQTail = q'.length ∧
          (∀ a, ¬ (qBuf ≤ a ∧ a < qBuf + vCap) → ¬ (vis ≤ a ∧ a < vis + vCap) →
            st'.mem a = stm a) ∧
          (∀ r, r ≠ rQHead → r ≠ rQTail → r ≠ rCurHe →
            r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 32 → st'.regs r = str r)) o st' ∧
      0 + c ≤ 65 by
    rcases h with ⟨o, st', c, hr, hq, hc⟩
    exact ⟨o, st', c, hr, hq, by simpa using hc⟩
  have hch_ltw_init : str rCurHe < 2 ^ w := by
    cases remHe with
    | nil => rw [hDll]; omega
    | cons a tl => obtain ⟨h1, h2, _⟩ := hDll; dsimp [dynGraphSize] at hdg_ltw; omega
  dsimp only [bfsMicroStepStmt]
  refine WordRAM.runs_cond_le (v := str rCurHe) (by eval_expr) ?_ ?_
  · -- Branch 1: `str rCurHe ≠ 0`, so `remHe = he :: tl`
    intro hch_ne
    cases remHe with
    | nil => exact absurd hDll hch_ne
    | cons he tl =>
      obtain ⟨hch_eq, hhe_lt, hDll_tl⟩ := hDll
      have hqh_pos : 0 < qHead := by
        by_contra h0
        have := hB.hrem_zero (by omega)
        cases this
      have hqh_le := hB.hqh_le
      obtain ⟨pref, hpref_eq, _⟩ := hB.hrem_pos hqh_pos
      set uCur := q[qHead - 1]'(by omega)
      have huCur_mem : uCur ∈ q := List.getElem_mem _
      have huCur_V : uCur ∈ F.V := (hB.hq_sub _ huCur_mem).1
      have huCur_conn : F.Connected uCur u₀ := (hB.hq_sub _ huCur_mem).2
      have hslot_lt : mem0 (dgExtToIntBase dgFPtr vCap + uCur) < vCap :=
        hvCap _ (hExtToInt uCur huCur_V).1
      have hhe_in_inc : he ∈ incL (mem0 (dgExtToIntBase dgFPtr vCap + uCur)) := by
        rw [hpref_eq]; simp
      have ⟨_, heE, hslot_eq⟩ := ((hincL _ hslot_lt).2.2 he).mp hhe_in_inc
      have he_lt_cap : he / 2 < eCapF := heCap _ heE
      have hhe_ltw : he < 2 ^ w := by omega
      have hch_ltw : str rCurHe < 2 ^ w := by omega
      have hlt2 : 2 < 2 ^ w := by omega
      have hother_vert :
          (if he % 2 = 0 then mem0 (dgIntToExtBase dgFPtr vCap + mem0 (dgEHeadSlotBase dgFPtr vCap eCapF + he / 2))
           else mem0 (dgIntToExtBase dgFPtr vCap + mem0 (dgETailSlotBase dgFPtr vCap eCapF + he / 2))) =
          heOther F he := by
        obtain ⟨htS, hhS⟩ := hEndSlot _ heE
        have htV := (hFval _ heE).1
        have hhV := (hFval _ heE).2
        dsimp only [heOther]
        by_cases hm : he % 2 = 0
        · simp only [hm, ↓reduceIte, hhS]
          exact (hExtToInt _ hhV).2
        · have hm1 : he % 2 = 1 := by omega
          simp only [hm1, ↓reduceIte, htS]
          exact (hExtToInt _ htV).2
      have hother_conn : heOther F he ∈ F.V ∧ F.Connected (heOther F he) u₀ := by
        have hconn_u := incL_mem_connected hFval hExtToInt hvCap hincL huCur_V hhe_in_inc
        exact ⟨hconn_u.2.2.1, connected_trans (connected_symm hconn_u.2.2.2) huCur_conn⟩
      set y := heOther F he
      have hy_lt : y < vCap := hvCap y hother_conn.1
      set nextPtr := stm (dgHeNextBase dgFPtr vCap eCapF + he)
      -- Step 1: r29 := curHe - 1 = he
      have hstep1_eval : (Expr.bin .sub (.reg rCurHe) (.const 1)).eval w
          { mem := stm, regs := str, pos := stp } = some he := by
        have h := Expr.eval_sub
          (Expr.eval_reg_of_eq (st := { mem := stm, regs := str, pos := stp }) hch_eq)
          (Expr.eval_const (k := 1) (by omega)) (hch_eq ▸ hch_ltw)
        rwa [Nat.add_sub_cancel] at h
      refine runs_seq_assign_le hstep1_eval ?_; dsimp only
      -- Step 2: rCurHe := heNext[he] = nextPtr
      refine runs_seq_assign_le (Expr.eval_load_of_eq (v := nextPtr) (by eval_expr) rfl) ?_; dsimp only
      -- Step 3: r30 := he / 2
      refine runs_seq_assign_le (v := he / 2)
        (Expr.eval_div (Expr.eval_reg_of_eq (by dsimp only; simp [h29_rCH]))
          (Expr.eval_const (by omega)) hhe_ltw) ?_; dsimp only
      -- Step 4: branch on `he % 2` to load `otherSlot` into `r31`
      set otherSlot := if he % 2 = 0 then mem0 (dgEHeadSlotBase dgFPtr vCap eCapF + he / 2)
        else mem0 (dgETailSlotBase dgFPtr vCap eCapF + he / 2)
      have hslot_in_V : otherSlot ∈ F.V := by
        obtain ⟨htS, hhS⟩ := hEndSlot _ heE
        dsimp only [otherSlot]; split_ifs
        · rw [hhS]; exact (hExtToInt _ (hFval _ heE).2).1
        · rw [htS]; exact (hExtToInt _ (hFval _ heE).1).1
      have hslot_lt_vCap : otherSlot < vCap := hvCap _ hslot_in_V
      have hy_eq_int : stm (dgIntToExtBase dgFPtr vCap + otherSlot) = y := by
        rw [hdgAg _ (by omega)]
        dsimp only [y, otherSlot]
        by_cases hm : he % 2 = 0 <;> simp only [hm, ↓reduceIte] at hother_vert ⊢ <;> exact hother_vert
      have hmod_ltw : he % 2 < 2 ^ w := lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by omega)
      -- Helper to finish Steps 5 & 6 once `r31 = otherSlot`
      have hfinish : ∀ (r31_st : ℕ → ℕ),
          r31_st 13 = dgIntToExtBase dgFPtr vCap →
          r31_st rVis = vis → r31_st rQBuf = qBuf → r31_st rQHead = qHead →
          r31_st rQTail = q.length → r31_st rCurHe = nextPtr → r31_st 31 = otherSlot →
          (∀ r, r ≠ rQHead → r ≠ rQTail → r ≠ rCurHe →
            r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 32 → r31_st r = str r) →
          ∀ acc : ℕ, acc ≤ 33 →
          ∃ o st' c,
            Runs w p ω
              (.assign 32 (.load (.bin .add (.reg 13) (.reg 31))) ;;
               .cond (.load (.bin .add (.reg rVis) (.reg 32)))
                 .nop
                 (.store (.bin .add (.reg rVis) (.reg 32)) (.const 1) ;;
                  .store (.bin .add (.reg rQBuf) (.reg rQTail)) (.reg 32) ;;
                  .assign rQTail (.bin .add (.reg rQTail) (.const 1))))
              { mem := stm, regs := r31_st, pos := stp } o st' c ∧
            normalPost (fun st' =>
              ∃ q' qHead' remHe',
                BfsInv F (fun v => mem0 (dgExtToIntBase dgFPtr vCap + v)) incL u₀ q' qHead' remHe' (steps + 1) ∧
                SideMemAt st'.mem qBuf vis vCap q' ∧
                DllTailAt st'.mem (dgHeNextBase dgFPtr vCap eCapF) (2 * eCapF) remHe' (st'.regs rCurHe) ∧
                st'.regs rQHead = qHead' ∧ st'.regs rQTail = q'.length ∧
                (∀ a, ¬ (qBuf ≤ a ∧ a < qBuf + vCap) → ¬ (vis ≤ a ∧ a < vis + vCap) →
                  st'.mem a = stm a) ∧
                (∀ r, r ≠ rQHead → r ≠ rQTail → r ≠ rCurHe →
                  r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 32 → st'.regs r = str r)) o st' ∧
            acc + c ≤ 65 := by
        intro r31_st hr13' hrV' hrQB' hrQH' hrQT' hrCH' hr31' hpres acc hacc
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := y) (by eval_expr) hy_eq_int) ?_; dsimp only
        have hvis_y : stm (vis + y) = if y ∈ q then 1 else 0 := hSide.2 y hy_lt
        refine WordRAM.runs_cond_le (Expr.eval_load_of_eq (v := if y ∈ q then 1 else 0)
          (Expr.eval_bin (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hrVis_32, hrV']))
            (Expr.eval_reg_of_eq (by simp)) (by dsimp [BinOp.eval]; omega)) hvis_y) ?_ ?_
        · -- Already visited (`y ∈ q`)
          intro hvis_ne
          have hy_in : y ∈ q := by by_contra hc; simp only [hc, ↓reduceIte] at hvis_ne; exact hvis_ne rfl
          refine runs_nop_le ?_ (by dsimp [Expr.size]; omega)
          have hB' := hB.step_edge hother_conn.1 hother_conn.2
          simp only [y, hy_in, ↓reduceIte] at hB'
          refine ⟨q, qHead, tl, hB', hSide, ?_, by simp [hrQH', hrQH_32], by simp [hrQT', hrQT_32],
            fun _ _ _ => rfl, fun r h1 h2 h3 h4 h5 h6 h7 => by
              dsimp only; rw [Function.update_of_ne h7]; exact hpres r h1 h2 h3 h4 h5 h6 h7⟩
          simpa [hrCH', hrCH_32] using hDll_tl
        · -- Unvisited (`y ∉ q`): mark `vis[y] := 1`, push `qBuf[qTail] := y`, `qTail := qTail + 1`
          intro hvis_0
          have hy_not : y ∉ q := fun hc => by simp only [hc, ↓reduceIte] at hvis_0; exact Nat.one_ne_zero hvis_0
          have hq_lt_cap : q.length < vCap :=
            list_len_lt_vCap hvCap hB.hq_nd (fun v hv => (hB.hq_sub v hv).1) hother_conn.1 hy_not
          refine runs_seq_store_le (x := vis + y) (v := 1)
            (Expr.eval_bin (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hrVis_32, hrV']))
              (Expr.eval_reg_of_eq (by simp)) (by dsimp [BinOp.eval]; omega))
            (by eval_expr) ?_; dsimp only
          refine runs_seq_store_le (x := qBuf + q.length) (v := y)
            (Expr.eval_bin (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hrQBuf_32, hrQB']))
              (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hrQT_32, hrQT']))
              (by dsimp [BinOp.eval]; omega))
            (by eval_expr) ?_; dsimp only
          refine runs_assign_le (v := q.length + 1)
            (Expr.eval_bin (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne hrQT_32, hrQT']))
              (Expr.eval_const (by omega)) (by dsimp [BinOp.eval]; omega))
            ?_ (by dsimp [Expr.size]; omega)
          have hB' := hB.step_edge hother_conn.1 hother_conn.2
          simp only [y, hy_not, ↓reduceIte] at hB'
          have hmem_frame : ∀ a, ¬ (qBuf ≤ a ∧ a < qBuf + vCap) → ¬ (vis ≤ a ∧ a < vis + vCap) →
              Function.update (Function.update stm (vis + y) 1) (qBuf + q.length) y a = stm a := by
            intro a haQ haV
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          refine ⟨q ++ [y], qHead, tl, hB', ?_, ?_, ?_, ?_, hmem_frame, ?_⟩
          · refine ⟨fun i hi => ?_, fun v hv => ?_⟩
            · simp only [List.length_append, List.length_singleton] at hi
              by_cases hilt : i < q.length
              · dsimp only
                rw [List.getElem_append_left hilt, Function.update_of_ne (by omega),
                  Function.update_of_ne (by rcases hq_disj_vis with h | h <;> omega)]
                exact hSide.1 i hilt
              · have hieq : i = q.length := by omega
                subst hieq
                simp
            · dsimp only
              rw [Function.update_of_ne (by rcases hq_disj_vis with h | h <;> omega)]
              by_cases hvy : v = y
              · subst hvy; simp
              · rw [Function.update_of_ne (by omega), hSide.2 v hv]
                simp [hvy]
          · have hDll_tl' := dllTailAt_congr hDll_tl (fun h hh => by
              have ha_lt : dgHeNextBase dgFPtr vCap eCapF + h < dgFPtr + dynGraphSize vCap eCapF := by omega
              exact hmem_frame _ (by omega) (by omega))
            simpa [hrCH', hrQT_rCH.symm, hrCH_32] using hDll_tl'
          · dsimp only
            rw [Function.update_of_ne hrQH_rQT, Function.update_of_ne hrQH_32, hrQH']
          · simp
          · intro r h1 h2 h3 h4 h5 h6 h7
            dsimp only
            rw [Function.update_of_ne h2, Function.update_of_ne h7]
            exact hpres r h1 h2 h3 h4 h5 h6 h7
      refine runs_seq_cond_le (v := he % 2)
        (by have : Function.update (Function.update (Function.update str 29 he) rCurHe nextPtr) 30 (he / 2) 29 = he := by
              simp [h29_rCH]
            eval_expr) ?_ ?_
      · -- `he % 2 = 1`: otherSlot is tailSlot
        intro hm1
        have hmod_ne0 : ¬ he % 2 = 0 := hm1
        have he_tail_eq : stm (dgETailSlotBase dgFPtr vCap eCapF + he / 2) = otherSlot := by
          rw [hdgAg _ (by omega)]
          simp [otherSlot, hmod_ne0]
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := otherSlot)
          (by have : Function.update (Function.update (Function.update str 29 he) rCurHe nextPtr) 30 (he / 2) 15 =
                dgETailSlotBase dgFPtr vCap eCapF := by simp [h15, h15_rCH]
              eval_expr) he_tail_eq) ?_; dsimp only
        exact hfinish _ (by simp [h13, hrCH_13.symm]) (by simp [hrV, hrVis_31, hrVis_30, hrVis_rCH, hrVis_29])
          (by simp [hrQB, hrQBuf_31, hrQBuf_30, hrQBuf_rCH, hrQBuf_29])
          (by simp [hrQH, hrQH_31, hrQH_30, hrQH_rCH, hrQH_29])
          (by simp [hrQT, hrQT_31, hrQT_30, hrQT_rCH, hrQT_29])
          (by simp [hrCH_31, hrCH_30]) (by simp)
          (fun r h1 h2 h3 h4 h5 h6 h7 => by
            rw [Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h3,
              Function.update_of_ne h4])
          _ (by dsimp [Expr.size]; omega)
      · -- `he % 2 = 0`: otherSlot is headSlot
        intro hm0
        have he_head_eq : stm (dgEHeadSlotBase dgFPtr vCap eCapF + he / 2) = otherSlot := by
          rw [hdgAg _ (by omega)]
          simp [otherSlot, hm0]
        refine runs_seq_assign_le (Expr.eval_load_of_eq (v := otherSlot)
          (by have : Function.update (Function.update (Function.update str 29 he) rCurHe nextPtr) 30 (he / 2) 16 =
                dgEHeadSlotBase dgFPtr vCap eCapF := by simp [h16, h16_rCH]
              eval_expr) he_head_eq) ?_; dsimp only
        exact hfinish _ (by simp [h13, hrCH_13.symm]) (by simp [hrV, hrVis_31, hrVis_30, hrVis_rCH, hrVis_29])
          (by simp [hrQB, hrQBuf_31, hrQBuf_30, hrQBuf_rCH, hrQBuf_29])
          (by simp [hrQH, hrQH_31, hrQH_30, hrQH_rCH, hrQH_29])
          (by simp [hrQT, hrQT_31, hrQT_30, hrQT_rCH, hrQT_29])
          (by simp [hrCH_31, hrCH_30]) (by simp)
          (fun r h1 h2 h3 h4 h5 h6 h7 => by
            rw [Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h3,
              Function.update_of_ne h4])
          _ (by dsimp [Expr.size]; omega)
  · -- Branch 2: `str rCurHe = 0`, so `remHe = []` and `qHead < q.length`
    intro hch_0
    have hrem_nil : remHe = [] := by
      cases remHe with
      | nil => rfl
      | cons a tl => exfalso; exact Nat.succ_ne_zero a (hDll.1.symm.trans hch_0)
    subst hrem_nil
    have hqh_lt : qHead < q.length := by
      rcases hnotDone with h | h
      · exact absurd rfl h
      · exact h
    have hq_le_cap : q.length ≤ vCap :=
      list_len_le_vCap hvCap hB.hq_nd (fun v hv => (hB.hq_sub v hv).1)
    set uPop := q[qHead]'hqh_lt
    have huPop_V : uPop ∈ F.V := (hB.hq_sub uPop (List.getElem_mem hqh_lt)).1
    have huPop_lt : uPop < vCap := hvCap uPop huPop_V
    set sPop := mem0 (dgExtToIntBase dgFPtr vCap + uPop)
    have hsPop_lt : sPop < vCap := hvCap _ (hExtToInt uPop huPop_V).1
    have hq_mem : stm (qBuf + qHead) = uPop := hSide.1 qHead hqh_lt
    have hs_mem : stm (dgExtToIntBase dgFPtr vCap + uPop) = sPop := hdgAg _ (by omega)
    set headVal := stm (dgIncHeadBase dgFPtr vCap + sPop)
    have hDll_new : DllTailAt stm (dgHeNextBase dgFPtr vCap eCapF) (2 * eCapF) (incL sPop) headVal := by
      have h0 := dllTailAt_of_isDll (hincL sPop hsPop_lt).1
      have hhead_eq : headVal = mem0 (dgIncHeadBase dgFPtr vCap + sPop) := hdgAg _ (by omega)
      rw [hhead_eq]
      exact dllTailAt_congr h0 (fun h hh => hdgAg _ (by omega))
    -- Step 1: r32 := qBuf[qHead] = uPop
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := uPop) (by eval_expr) hq_mem) ?_; dsimp only
    -- Step 2: rQHead := qHead + 1
    refine runs_seq_assign_le (v := qHead + 1)
      (by have : Function.update str 32 uPop rQHead = qHead := by rw [Function.update_of_ne hrQH_32, hrQH]
          eval_expr) ?_; dsimp only
    -- Step 3: r31 := extToInt[uPop] = sPop
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := sPop)
      (by have : Function.update (Function.update str 32 uPop) rQHead (qHead + 1) 12 =
            dgExtToIntBase dgFPtr vCap := by simp [h12, h12_rQH]
          have : Function.update (Function.update str 32 uPop) rQHead (qHead + 1) 32 = uPop := by
            simp [hrQH_32.symm]
          eval_expr) hs_mem) ?_; dsimp only
    -- Step 4: rCurHe := incHead[sPop] = headVal
    refine runs_assign_le (Expr.eval_load_of_eq (v := headVal)
      (by have : Function.update (Function.update (Function.update str 32 uPop) rQHead (qHead + 1)) 31 sPop 14 =
            dgIncHeadBase dgFPtr vCap := by simp [h14, h14_rQH]
          eval_expr) rfl) ?_
      (by dsimp [Expr.size]; omega)
    refine ⟨q, qHead + 1, incL sPop, hB.step_pop hqh_lt, hSide, by simpa using hDll_new,
      by simp [hrQH_rCH, hrQH_31], by simp [hrQT, hrQT_rCH, hrQT_31, hrQT_rQH, hrQT_32],
      fun _ _ _ => rfl, fun r h1 h2 h3 h4 h5 h6 h7 => by
        dsimp only
        rw [Function.update_of_ne h3, Function.update_of_ne h6, Function.update_of_ne h1,
          Function.update_of_ne h7]⟩

end

end MinCostFlow.LSF.Program
