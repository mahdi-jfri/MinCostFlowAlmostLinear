module

public import MinCostFlow.LowStretch.ProgramBody
public import MinCostFlow.LowStretch.ProgramOwed
public import MinCostFlow.LowStretch.ProgChildTop
public import MinCostFlow.LowStretch.ProgChildHw
public import MinCostFlow.LowStretch.ProgChildPairs
public import MinCostFlow.LowStretch.ProgChildNodes
public import MinCostFlow.LowStretch.ProgChildSize
public import MinCostFlow.LowStretch.ProgChildDrawRun
public import MinCostFlow.LowStretch.ProgLog
public import MinCostFlow.LowStretch.ProgSplitSpec
public import MinCostFlow.LowStretch.ProgSplitLab
public import MinCostFlow.LowStretch.ProgChildIota
public import MinCostFlow.LowStretch.ProgSplitGrp
public import MinCostFlow.LowStretch.ProgChildIdx
public import MinCostFlow.LowStretch.ProgCSR
public import MinCostFlow.LowStretch.ProgChildKey
public import MinCostFlow.LowStretch.ProgArcs2
public import MinCostFlow.LowStretch.ProgDijRun
public import MinCostFlow.LowStretch.ProgAct
public import MinCostFlow.LowStretch.ProgClusterSetup
public import MinCostFlow.LowStretch.ProgClusterSetupTc
public import MinCostFlow.LowStretch.ProgClusterMax
public import MinCostFlow.LowStretch.ProgTree
public import MinCostFlow.LowStretch.ProgHwFix
public import MinCostFlow.LowStretch.ProgPGraph
public import MinCostFlow.LowStretch.ProgClog

/-!
# The other procedures of the body: the setup and the child step

`restProcs` is the list of the procedures of the body from index `47` on, after the petal
procedures (`petalProcs 33` at `33` to `46`). It holds the setup at `68` and the child step at
`55`, and every procedure they call:

| index | procedure | calls |
|---|---|---|
| `47` | `log2P` | |
| `48` | the first run of Dijkstra, `drawP` | `49`, `36` (`pqClear`), `53`, `54` |
| `49` | `arcP` | `50`, `51`, `52` |
| `50` | `arcFill` | |
| `51` | `csrB` | |
| `52` | `arcCopy` | |
| `53` | `dijRun` | `34` (`pqPush`), `38` (`dijStep`) |
| `54` | `maxP` | |
| `55` | the child step `childP` | the indices `childIdx` |
| `56` | one child, `oneP` | the indices `childIdx` |
| `57` | the reset rule, `rsP` | the indices `childIdx` |
| `58` to `67` | `hwWalkP`, `pcP`, `ncP`, `smP`, `splitP`, `fillAtP`, `iotaP`, `grpCopyP`, `chxP`, `keyP` | `62` calls `63` |
| `68` | the setup `setupP` | the indices `setupIdx` |
| `69` to `72` | `treeP`, `hwFix`, `actP`, `pgP` | `72` calls `73`, `74`, `51`, `52` |
| `73` to `76` | `pfill`, `slotF`, `rclsP`, `clogP` | `73` calls `75`, `75` calls `76` |
| `77` to `82` | `tabP cpE`, `tabP halfE`, `tabP expE`, `maxtP`, `tabP p2E`, `tabP sqE` | |

The program is `lsstP = lsstProg (lsstBody restProcs 68 55)`. Here we prove the contracts of the
procedures of this list: `childP_meets` (`MeetsChild` at `55`) and `setupCallees_meets` (the
contracts of the procedures that the setup calls).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- The procedure indices of the child step. -/
def childIdx : CIdx :=
  { hw := 58, pc := 59, nc := 60, sm := 61, dr := 48, rs := 57, lg := 47, sp := 62, io := 64,
    gc := 65, cx := 66, csr := 51, key := 67, one := 56 }

/-- The procedure indices of the setup. -/
def setupIdx : SuIdx :=
  { lg := 47, dr := 48, tr := 69, hf := 70, ac := 71, pg := 72, cp := 77, hl := 78, ex := 79,
    mx := 80, p2 := 81, sq := 82, cl := 36 }

/-- The procedures of the body from index `47` on. -/
def restProcs : List Stmt :=
  [log2P, drawP 49 36 53 54, arcP 50 51 52, arcFill, csrB, arcCopy, dijRun 34 38, maxP,
    childP childIdx, oneP childIdx, rsP childIdx, hwWalkP, pcP, ncP, smP, splitP 63, fillAtP,
    iotaP, grpCopyP, chxP, keyP,
    setupP setupIdx, treeP, hwFix, actP, pgP 73 74 51 52, pfill 75, slotF, rclsP 76, clogP,
    tabP cpE, tabP halfE, tabP expE, maxtP, tabP p2E, tabP sqE]

theorem restProcs_length : restProcs.length = 36 := rfl

/-- **The program of the low-stretch spanning tree.** -/
def lsstP : Program := lsstProg (lsstBody restProcs 68 55)

theorem lsstP_rest : lsstP.HasAt 47 restProcs := by
  have h := lsstProg_body (lsstBody restProcs 68 55)
  intro i hi
  have := h (17 + i) (by simp [lsstBody, petalProcs_length]; omega)
  rw [show 30 + (17 + i) = 47 + i by omega] at this
  rw [lsstP, this]
  simp only [lsstBody, List.append_assoc]
  rw [List.getElem_append_right (by simp; omega),
    List.getElem_append_right (by simp [petalProcs_length]; omega)]
  have e : 17 + i - [bodyP 31, nodeP 68 45 46 32 55, regP 45 46].length -
      (petalProcs 33).length = i := by simp [petalProcs_length]; omega
  simp only [e]

theorem lsstP_petals : lsstP.HasAt 33 (petalProcs 33) := (lsstBody_procs restProcs 68 55).2.2.2

/-- Procedure `47 + i` of `lsstP` is entry `i` of `restProcs`. -/
theorem lsstP_at (i : ℕ) (hi : i < restProcs.length) : lsstP.HasAt (47 + i) [restProcs[i]] :=
  hasAt_one lsstP_rest i hi

theorem lsstP_proc (i : ℕ) (hi : i < restProcs.length) :
    lsstP.procs[47 + i]? = some restProcs[i] := lsstP_at i hi 0 (by simp)

/-- The contract of the first run of Dijkstra at `48`, which both the setup and the child step
call. -/
theorem lsstP_draw {w : ℕ} : MeetsContract w lsstP 48 (drawC w) := by
  have hP := petalProcs_meets (w := w) lsstP_petals
  have hStep : MeetsContract w lsstP 38 (dijStepC w) := petalProcs_dijStep lsstP_petals
  exact drawP_spec (lsstP_at 1 (by decide))
    (arcP_spec (lsstP_at 2 (by decide)) (lsstP_at 3 (by decide)) (lsstP_at 4 (by decide))
      (lsstP_at 5 (by decide)))
    hP.2.2.2.1 (dijRun_spec (lsstP_at 6 (by decide)) hP.2.1 hStep)
    (maxP_spec (lsstP_at 7 (by decide)))

/-- **The child step meets its contract** at `55`. -/
theorem childP_meets {w : ℕ} : MeetsChild w lsstP 55 :=
  childP_meetsChild (I := childIdx) (lsstP_proc 8 (by decide)) (lsstP_proc 9 (by decide))
    (lsstP_proc 10 (by decide)) (hwWalkP_spec (lsstP_at 11 (by decide)))
    (pcP_spec (lsstP_at 12 (by decide))) (ncP_spec (lsstP_at 13 (by decide)))
    (smP_spec (lsstP_at 14 (by decide))) lsstP_draw (log2P_spec (lsstP_at 0 (by decide)))
    (splitP_spec (lsstP_at 15 (by decide)) (fillAtP_spec (lsstP_at 16 (by decide))))
    (iotaP_spec (lsstP_at 17 (by decide))) (grpCopyP_spec (lsstP_at 18 (by decide)))
    (chxP_spec (lsstP_at 19 (by decide))) (csrB_spec (lsstP_at 4 (by decide)))
    (keyP_spec (lsstP_at 20 (by decide)))

/-- **The procedures that the setup calls meet their contracts**, at the indices `setupIdx`. -/
theorem setupCallees_meets {w : ℕ} :
    lsstP.procs[68]? = some (setupP setupIdx) ∧
      MeetsContract w lsstP setupIdx.lg (log2C w) ∧ MeetsContract w lsstP setupIdx.dr (drawC w) ∧
      MeetsContract w lsstP setupIdx.tr (treePC w) ∧
      MeetsContract w lsstP setupIdx.hf (hwFixC w) ∧
      MeetsContract w lsstP setupIdx.ac (actPC w) ∧ MeetsContract w lsstP setupIdx.pg (pgPC w) ∧
      MeetsContract w lsstP setupIdx.cp (suCpC w) ∧
      MeetsContract w lsstP setupIdx.hl (suHalfC w) ∧
      MeetsContract w lsstP setupIdx.ex (suExpC w) ∧
      MeetsContract w lsstP setupIdx.mx (maxtC w) ∧ MeetsContract w lsstP setupIdx.p2 (suP2C w) ∧
      MeetsContract w lsstP setupIdx.sq (suSqC w) ∧
      MeetsContract w lsstP setupIdx.cl (pqClearC w) :=
  ⟨lsstP_proc 21 (by decide), log2P_spec (lsstP_at 0 (by decide)), lsstP_draw,
    treeP_spec (lsstP_at 22 (by decide)), hwFix_spec (lsstP_at 23 (by decide)),
    actP_spec (lsstP_at 24 (by decide)),
    pgP_spec (lsstP_at 25 (by decide)) (lsstP_at 26 (by decide))
      (rclsP_spec (lsstP_at 28 (by decide)) (clogP_spec (lsstP_at 29 (by decide))))
      (lsstP_at 27 (by decide)) (lsstP_at 4 (by decide)) (lsstP_at 5 (by decide)),
    suCpC_spec (lsstP_at 30 (by decide)), suHalfC_spec (lsstP_at 31 (by decide)),
    suExpC_spec (lsstP_at 32 (by decide)), maxtP_spec (lsstP_at 33 (by decide)),
    suP2C_spec (lsstP_at 34 (by decide)), suSqC_spec (lsstP_at 35 (by decide)),
    (petalProcs_meets (w := w) lsstP_petals).2.2.2.1⟩

/-- **[AN19] Theorem 1 for the program `lsstP`**, from the contract of the setup at `68`. All
other procedures meet their contracts: the loop of the regular petals by `regPrefix_of`, the
child step by `childP_meets`. -/
theorem lowStretchSpanningTree_of_setup (hSetup : ∀ w, MeetsContract w lsstP 68 (setupC w)) :
    LowStretchSpanningTree :=
  lowStretchSpanningTree_of_parts restProcs (fun w => setupCJ_of (hSetup w))
    (fun _ => regPrefix_of lsstP_petals) fun _ => childP_meets

end MinCostFlow.LowStretch
