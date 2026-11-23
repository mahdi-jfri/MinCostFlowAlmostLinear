module

public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgRelabel
public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.Expander.PruningBucketBase

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `RemoveFake` Word-RAM Layout, Statements, and Linear-Pass Triples

Defines the workspace layout, register map, machine statements, and verified `Triple`
specifications for the `RemoveFake` Word-RAM procedure (`rfSetupStmt`, `rfFillLocStmt`,
`rfBuildJStmt`, `rfClearLocStmt`, `rfBuildInBStmt`, `rfComputeHStmt`, `rfExtractRStmt`).
The subdivided-graph construction (`rfBuildJ_triple`) is proved in `ProgRemoveFakeBuildJ.lean`,
and the full assembly and contract (`removeFake_spec_prog`) are in `ProgRemoveFake.lean`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Register Map and Workspace Layout -/

abbrev rfK : ℕ := 0
abbrev rfVerts : ℕ := 1
abbrev rfMH : ℕ := 2
abbrev rfH : ℕ := 3
abbrev rfMF : ℕ := 4
abbrev rfF : ℕ := 5
abbrev rfRho : ℕ := 6
abbrev rfLoc : ℕ := 7
abbrev rfOutR : ℕ := 8
abbrev rfWork : ℕ := 9

abbrev rfNJ : ℕ := 10
abbrev rfMJ : ℕ := 11
abbrev rfJGraph : ℕ := 12
abbrev rfInB : ℕ := 13
abbrev rfOutRLoc : ℕ := 14
abbrev rfCsr : ℕ := 15
abbrev rfPruneWork : ℕ := 16
abbrev rfCcapReg : ℕ := 17
abbrev rfHParamReg : ℕ := 18

abbrev rfI : ℕ := 20
abbrev rfTmp1 : ℕ := 21
abbrev rfTmp2 : ℕ := 22
abbrev rfTmp3 : ℕ := 23
abbrev rfTmp4 : ℕ := 24
abbrev rfTmp5 : ℕ := 25
abbrev rfCnt : ℕ := 26

/-- Address of the subdivided local graph `J_loc` inside `workAddr`. -/
abbrev rfJGraphAddr (workAddr : ℕ) : ℕ := workAddr

/-- Address of the midpoint flag array `inB` inside `workAddr`. -/
abbrev rfInBAddr (workAddr mH mF : ℕ) : ℕ :=
  workAddr + 2 + 2 * (mH + 2 * mF)

/-- Address of the local pruning output `outRLoc` inside `workAddr`. -/
abbrev rfOutRLocAddr (workAddr k mH mF : ℕ) : ℕ :=
  workAddr + 2 + 2 * (mH + 2 * mF) + (k + mF)

/-- Address of the CSR representation of `J_loc` inside `workAddr`. -/
abbrev rfCsrAddr (workAddr k mH mF : ℕ) : ℕ :=
  workAddr + 2 + 2 * (mH + 2 * mF) + 2 * (k + mF)

/-- Address of the pruning scratch workspace inside `workAddr`. -/
abbrev rfPruneWorkAddr (workAddr k mH mF : ℕ) : ℕ :=
  workAddr + 4 * (k + mF) + 6 * (mH + 2 * mF) + 3

/-- Total scratch words required at `workAddr` for `RemoveFake`. -/
def removeFakeWorkSpace (k mH mF H_param : ℕ) : ℕ :=
  4 * (k + mF) + 6 * (mH + 2 * mF) + 3 + pruneWorkSpace (k + mF) (mH + 2 * mF) H_param

/-- Word-size bound ensuring every address and intermediate value of `RemoveFake` fits `< 2 ^ w`. -/
def RemoveFakeWordBound (w n k mH mF rhoNum rhoDen
    vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr : ℕ) : Prop :=
  vertsAddr + k < 2 ^ w ∧
  hAddr + 2 * mH < 2 ^ w ∧
  fAddr + 2 * mF < 2 ^ w ∧
  rhoAddr + 2 < 2 ^ w ∧
  locAddr + n < 2 ^ w ∧
  outRAddr + k < 2 ^ w ∧
  12 * rhoDen + rhoNum < 2 ^ w ∧
  PruneWordBound w (k + mF) (mH + 2 * mF) (rfCcap rhoNum rhoDen)
    (rfHParam mH mF rhoNum rhoDen) (rfPruneWorkAddr workAddr k mH mF)

/-- Disjointness of two half-open address intervals `[a, a + la)` and `[b, b + lb)`. -/
def DisjointRange (a la b lb : ℕ) : Prop :=
  a + la ≤ b ∨ b + lb ≤ a

/-- Memory disjointness for `RemoveFake`: mutable buffers `locAddr`, `outRAddr`, `workAddr` are
pairwise disjoint and disjoint from all four input regions (`vertsAddr`, `hAddr`, `fAddr`,
`rhoAddr`). -/
def RemoveFakeDisjoint (n k mH mF H_param
    vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr : ℕ) : Prop :=
  let ws := removeFakeWorkSpace k mH mF H_param
  DisjointRange locAddr n vertsAddr k ∧
  DisjointRange locAddr n hAddr (2 * mH) ∧
  DisjointRange locAddr n fAddr (2 * mF) ∧
  DisjointRange locAddr n rhoAddr 2 ∧
  DisjointRange locAddr n outRAddr k ∧
  DisjointRange locAddr n workAddr ws ∧
  DisjointRange outRAddr k vertsAddr k ∧
  DisjointRange outRAddr k hAddr (2 * mH) ∧
  DisjointRange outRAddr k fAddr (2 * mF) ∧
  DisjointRange outRAddr k rhoAddr 2 ∧
  DisjointRange outRAddr k workAddr ws ∧
  DisjointRange workAddr ws vertsAddr k ∧
  DisjointRange workAddr ws hAddr (2 * mH) ∧
  DisjointRange workAddr ws fAddr (2 * mF) ∧
  DisjointRange workAddr ws rhoAddr 2

/-! ## 2. Machine Statements -/

/-- Stage 0: compute `nJ`, `mJ`, contiguous workspace pointers, and `C_cap`. -/
def rfSetupStmt : Stmt :=
  seqStmts
    [ .assign rfNJ (.bin .add (.reg rfK) (.reg rfMF))
    , .assign rfMJ (.bin .add (.reg rfMH) (.bin .mul (.const 2) (.reg rfMF)))
    , .assign rfJGraph (.reg rfWork)
    , .assign rfInB (.bin .add (.bin .add (.reg rfJGraph) (.const 2))
        (.bin .mul (.const 2) (.reg rfMJ)))
    , .assign rfOutRLoc (.bin .add (.reg rfInB) (.reg rfNJ))
    , .assign rfCsr (.bin .add (.reg rfOutRLoc) (.reg rfNJ))
    , .assign rfPruneWork (.bin .add (.bin .add (.reg rfCsr)
        (.bin .add (.bin .mul (.const 2) (.reg rfNJ)) (.const 1)))
        (.bin .mul (.const 4) (.reg rfMJ)))
    , .assign rfTmp1 (.load (.reg rfRho))
    , .assign rfTmp2 (.load (.bin .add (.reg rfRho) (.const 1)))
    , .assign rfCcapReg (.bin .add
        (.bin .div
          (.bin .sub (.bin .add (.bin .mul (.const 12) (.reg rfTmp2)) (.reg rfTmp1)) (.const 1))
          (.reg rfTmp1))
        (.const 2)) ]

/-- Stage 1: write `locAddr[verts[i]] := i` for `i = 0 .. k - 1`. -/
def rfFillLocStmt : Stmt :=
  forRange rfI (.const 0) (.reg rfK)
    (seqStmts
      [ .assign rfTmp1 (.load (.bin .add (.reg rfVerts) (.reg rfI)))
      , .store (.bin .add (.reg rfLoc) (.reg rfTmp1)) (.reg rfI) ])

/-- Stage 2: write `subdivGraph k H_loc F_loc` into `rfJGraph`. -/
def rfBuildJStmt : Stmt :=
  seqStmts
    [ .store (.reg rfJGraph) (.reg rfNJ)
    , .store (.bin .add (.reg rfJGraph) (.const 1)) (.reg rfMJ)
    , forRange rfI (.const 0) (.reg rfMH)
        (seqStmts
          [ .assign rfTmp1 (.load (.bin .add (.reg rfH) (.bin .mul (.const 2) (.reg rfI))))
          , .assign rfTmp2 (.load (.bin .add (.bin .add (.reg rfH) (.bin .mul (.const 2) (.reg rfI))) (.const 1)))
          , .assign rfTmp3 (.load (.bin .add (.reg rfLoc) (.reg rfTmp1)))
          , .assign rfTmp4 (.load (.bin .add (.reg rfLoc) (.reg rfTmp2)))
          , .store (.bin .add (.bin .add (.reg rfJGraph) (.const 2)) (.bin .mul (.const 2) (.reg rfI))) (.reg rfTmp3)
          , .store (.bin .add (.bin .add (.reg rfJGraph) (.const 3)) (.bin .mul (.const 2) (.reg rfI))) (.reg rfTmp4) ])
    , forRange rfI (.const 0) (.reg rfMF)
        (seqStmts
          [ .assign rfTmp1 (.load (.bin .add (.reg rfF) (.bin .mul (.const 2) (.reg rfI))))
          , .assign rfTmp2 (.load (.bin .add (.bin .add (.reg rfF) (.bin .mul (.const 2) (.reg rfI))) (.const 1)))
          , .assign rfTmp3 (.load (.bin .add (.reg rfLoc) (.reg rfTmp1)))
          , .assign rfTmp4 (.load (.bin .add (.reg rfLoc) (.reg rfTmp2)))
          , .assign rfTmp5 (.bin .add (.reg rfK) (.reg rfI))
          , .assign rfTmp1 (.bin .add (.bin .add (.bin .add (.reg rfJGraph) (.const 2))
              (.bin .mul (.const 2) (.reg rfMH))) (.bin .mul (.const 4) (.reg rfI)))
          , .store (.reg rfTmp1) (.reg rfTmp3)
          , .store (.bin .add (.reg rfTmp1) (.const 1)) (.reg rfTmp5)
          , .store (.bin .add (.reg rfTmp1) (.const 2)) (.reg rfTmp5)
          , .store (.bin .add (.reg rfTmp1) (.const 3)) (.reg rfTmp4) ]) ]

/-- Stage 3: clear `locAddr[verts[i]] := 0` for `i = 0 .. k - 1`. -/
def rfClearLocStmt : Stmt :=
  forRange rfI (.const 0) (.reg rfK)
    (seqStmts
      [ .assign rfTmp1 (.load (.bin .add (.reg rfVerts) (.reg rfI)))
      , .store (.bin .add (.reg rfLoc) (.reg rfTmp1)) (.const 0) ])

/-- Stage 4: write midpoint indicator `inB[0..k-1] := 0`, `inB[k..k+mF-1] := 1`. -/
def rfBuildInBStmt : Stmt :=
  seqStmts
    [ forRange rfI (.const 0) (.reg rfK)
        (.store (.bin .add (.reg rfInB) (.reg rfI)) (.const 0))
    , forRange rfI (.const 0) (.reg rfMF)
        (.store (.bin .add (.bin .add (.reg rfInB) (.reg rfK)) (.reg rfI)) (.const 1)) ]

/-- Stage 5: compute `logVal = ⌊log₂(2 * mJ + 1)⌋` and `H_param = 4 * C_cap * (logVal + 1) + 2`. -/
def rfComputeHStmt : Stmt :=
  seqStmts
    [ .assign rfTmp1 (.bin .add (.bin .mul (.const 2) (.reg rfMJ)) (.const 1))
    , .assign rfTmp2 (.const 0)
    , .loop (.bin .lt (.const 1) (.reg rfTmp1))
        (seqStmts
          [ .assign rfTmp1 (.bin .div (.reg rfTmp1) (.const 2))
          , .assign rfTmp2 (.bin .add (.reg rfTmp2) (.const 1)) ])
    , .assign rfHParamReg (.bin .add
        (.bin .mul (.bin .mul (.const 4) (.reg rfCcapReg)) (.bin .add (.reg rfTmp2) (.const 1)))
        (.const 2)) ]

/-- Stage 8: collect kept vertices `verts[i]` with `outRLoc[i] > 0` into `outRAddr`, returning `|R|`. -/
def rfExtractRStmt : Stmt :=
  seqStmts
    [ .assign rfCnt (.const 0)
    , forRange rfI (.const 0) (.reg rfK)
        (seqStmts
          [ .assign rfTmp1 (.load (.bin .add (.reg rfOutRLoc) (.reg rfI)))
          , .cond (.bin .lt (.const 0) (.reg rfTmp1))
              (seqStmts
                [ .assign rfTmp2 (.load (.bin .add (.reg rfVerts) (.reg rfI)))
                , .store (.bin .add (.reg rfOutR) (.reg rfCnt)) (.reg rfTmp2)
                , .assign rfCnt (.bin .add (.reg rfCnt) (.const 1)) ])
              .nop ])
    , .ret (.reg rfCnt) ]

/-- Register invariant holding the fixed arguments and computed pointers `0 .. 17`. -/
structure RfRegs (k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr
    rhoNum rhoDen : ℕ) (st : State) : Prop where
  r_k : st.regs rfK = k
  r_verts : st.regs rfVerts = vertsAddr
  r_mH : st.regs rfMH = mH
  r_h : st.regs rfH = hAddr
  r_mF : st.regs rfMF = mF
  r_f : st.regs rfF = fAddr
  r_rho : st.regs rfRho = rhoAddr
  r_loc : st.regs rfLoc = locAddr
  r_outR : st.regs rfOutR = outRAddr
  r_work : st.regs rfWork = workAddr
  r_nJ : st.regs rfNJ = k + mF
  r_mJ : st.regs rfMJ = mH + 2 * mF
  r_jGraph : st.regs rfJGraph = rfJGraphAddr workAddr
  r_inB : st.regs rfInB = rfInBAddr workAddr mH mF
  r_outRLoc : st.regs rfOutRLoc = rfOutRLocAddr workAddr k mH mF
  r_csr : st.regs rfCsr = rfCsrAddr workAddr k mH mF
  r_pruneWork : st.regs rfPruneWork = rfPruneWorkAddr workAddr k mH mF
  r_ccap : st.regs rfCcapReg = rfCcap rhoNum rhoDen

/-- Original vertices selected by nonzero flags in `mem (outRLocAddr + i)`. -/
def filterVertsByMem (mem : ℕ → ℕ) (outRLocAddr : ℕ) (verts : List ℕ) : List ℕ :=
  ((List.range verts.length).filter fun i => decide (mem (outRLocAddr + i) ≠ 0)).map
    fun i => verts.getD i 0

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

lemma rfSetupStmt_noRand : rfSetupStmt.NoRand := by
  simp [rfSetupStmt, seqStmts, Stmt.NoRand]

lemma rfFillLocStmt_noRand : rfFillLocStmt.NoRand := by
  simp [rfFillLocStmt, forRange, forUp, seqStmts, Stmt.NoRand]

lemma rfBuildJStmt_noRand : rfBuildJStmt.NoRand := by
  simp [rfBuildJStmt, forRange, forUp, seqStmts, Stmt.NoRand]

lemma rfClearLocStmt_noRand : rfClearLocStmt.NoRand := by
  simp [rfClearLocStmt, forRange, forUp, seqStmts, Stmt.NoRand]

lemma rfBuildInBStmt_noRand : rfBuildInBStmt.NoRand := by
  simp [rfBuildInBStmt, forRange, forUp, seqStmts, Stmt.NoRand]

lemma rfComputeHStmt_noRand : rfComputeHStmt.NoRand := by
  simp [rfComputeHStmt, seqStmts, Stmt.NoRand]

lemma rfExtractRStmt_noRand : rfExtractRStmt.NoRand := by
  simp [rfExtractRStmt, forRange, forUp, seqStmts, Stmt.NoRand]

lemma rfRegs_of_agree {k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr
    rhoNum rhoDen : ℕ} {st st' : State}
    (h : RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st)
    (hag : ∀ r ≤ 17, st'.regs r = st.regs r) :
    RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st' :=
  ⟨(hag 0 (by omega)).trans h.r_k,
   (hag 1 (by omega)).trans h.r_verts,
   (hag 2 (by omega)).trans h.r_mH,
   (hag 3 (by omega)).trans h.r_h,
   (hag 4 (by omega)).trans h.r_mF,
   (hag 5 (by omega)).trans h.r_f,
   (hag 6 (by omega)).trans h.r_rho,
   (hag 7 (by omega)).trans h.r_loc,
   (hag 8 (by omega)).trans h.r_outR,
   (hag 9 (by omega)).trans h.r_work,
   (hag 10 (by omega)).trans h.r_nJ,
   (hag 11 (by omega)).trans h.r_mJ,
   (hag 12 (by omega)).trans h.r_jGraph,
   (hag 13 (by omega)).trans h.r_inB,
   (hag 14 (by omega)).trans h.r_outRLoc,
   (hag 15 (by omega)).trans h.r_csr,
   (hag 16 (by omega)).trans h.r_pruneWork,
   (hag 17 (by omega)).trans h.r_ccap⟩

lemma rfRegs_update_ge {k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr
    rhoNum rhoDen : ℕ} {st : State} {r v : ℕ} (hr18 : 18 ≤ r)
    (h : RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st) :
    RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen
      { st with regs := Function.update st.regs r v } :=
  rfRegs_of_agree h fun j hj => Function.update_of_ne (by omega) v st.regs

lemma rfRegs_update_mem {k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr
    rhoNum rhoDen : ℕ} {st : State} {mem' : ℕ → ℕ}
    (h : RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st) :
    RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen
      { st with mem := mem' } :=
  rfRegs_of_agree h fun _ _ => rfl

lemma disjointRange_outside {a la b lb x : ℕ} (h : DisjointRange a la b lb)
    (hx1 : b ≤ x) (hx2 : x < b + lb) : x < a ∨ a + la ≤ x := by
  rcases h with h | h
  · right; omega
  · left; omega

lemma disjointRange_shrink_left {a la la' b lb : ℕ} (h : DisjointRange a la b lb)
    (hle : la' ≤ la) : DisjointRange a la' b lb := by
  rcases h with h | h
  · left; omega
  · right; exact h

lemma disjointRange_shrink_right {a la b lb lb' : ℕ} (h : DisjointRange a la b lb)
    (hle : lb' ≤ lb) : DisjointRange a la b lb' := by
  rcases h with h | h
  · left; exact h
  · right; omega

lemma rfWorkSpace_word_lt {w n k mH mF rhoNum rhoDen
    vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr : ℕ}
    (hw : RemoveFakeWordBound w n k mH mF rhoNum rhoDen
      vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr) :
    workAddr + 4 * (k + mF) + 6 * (mH + 2 * mF) + 3 +
      pruneWorkSpace (k + mF) (mH + 2 * mF) (rfHParam mH mF rhoNum rhoDen) + 2 < 2 ^ w ∧
    8 * rfCcap rhoNum rhoDen * (mH + 2 * mF) + 4 * rfCcap rhoNum rhoDen +
      2 * (k + mF) + 2 * (mH + 2 * mF) + rfHParam mH mF rhoNum rhoDen + 16 < 2 ^ w := by
  have hp := hw.2.2.2.2.2.2.2
  unfold PruneWordBound at hp
  have h1 : rfPruneWorkAddr workAddr k mH mF +
      pruneWorkSpace (k + mF) (mH + 2 * mF) (rfHParam mH mF rhoNum rhoDen) + 2 < 2 ^ w :=
    lt_of_le_of_lt (le_max_left _ _) hp
  have h2 : 8 * rfCcap rhoNum rhoDen * (mH + 2 * mF) + 4 * rfCcap rhoNum rhoDen +
      2 * (k + mF) + 2 * (mH + 2 * mF) + rfHParam mH mF rhoNum rhoDen + 16 < 2 ^ w :=
    lt_of_le_of_lt (le_max_right _ _) hp
  exact ⟨by dsimp only [rfPruneWorkAddr] at h1; omega, h2⟩

/-! ## 3. Stage 0 (`rfSetupStmt`) -/

/-- Stage 0: computes all workspace pointers and `C_cap` without modifying memory. -/
theorem rfSetup_triple {w n k mH mF rhoNum rhoDen
    vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr : ℕ}
    (p : Program) (mem : ℕ → ℕ) (pos : ℕ)
    (hrho1 : mem rhoAddr = rhoNum) (hrho2 : mem (rhoAddr + 1) = rhoDen)
    (hw : RemoveFakeWordBound w n k mH mF rhoNum rhoDen
      vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr) :
    let args := [k, vertsAddr, mH, hAddr, mF, fAddr, rhoAddr, locAddr, outRAddr, workAddr]
    Triple w p (fun st => st = startState args mem pos) rfSetupStmt
      (normalPost fun st' =>
        RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st' ∧
        st'.mem = mem ∧ st'.pos = pos)
      (fun _ => 100) := by
  intro args
  obtain ⟨hws, hval⟩ := rfWorkSpace_word_lt hw
  have hrho_w := hw.2.2.2.1
  have h12_w := hw.2.2.2.2.2.2.1
  have hdiv_lt : (12 * rhoDen + rhoNum - 1) / rhoNum < 2 ^ w :=
    lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hccap_lt : rfCcap rhoNum rhoDen < 2 ^ w := by omega
  intro st ω hst
  subst hst
  refine runs_start_le ?_
  dsimp only [rfSetupStmt, seqStmts]
  refine runs_seq_assign_le (v := k + mF)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState, args]))
      (Expr.eval_reg_of_eq (by simp [startState, args])) (by omega)) ?_
  refine runs_seq_assign_le (v := mH + 2 * mF)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState, args]))
      (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (by simp [startState, args])) (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := rfJGraphAddr workAddr)
    (Expr.eval_reg_of_eq (by simp [startState, args, rfJGraphAddr])) ?_
  refine runs_seq_assign_le (v := rfInBAddr workAddr mH mF)
    (Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq (v := workAddr) (by simp [rfJGraphAddr]))
        (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq (v := mH + 2 * mF) (by simp)) (by omega))
      (by omega)) ?_
  refine runs_seq_assign_le (v := rfOutRLocAddr workAddr k mH mF)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := rfInBAddr workAddr mH mF) (by simp))
      (Expr.eval_reg_of_eq (v := k + mF) (by simp)) (by omega)) ?_
  refine runs_seq_assign_le (v := rfCsrAddr workAddr k mH mF)
    (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (v := rfOutRLocAddr workAddr k mH mF) (by simp))
        (Expr.eval_reg_of_eq (v := k + mF) (by simp)) (by dsimp only [rfOutRLocAddr]; omega))
      (by dsimp only [rfOutRLocAddr, rfCsrAddr]; omega)) ?_
  refine runs_seq_assign_le (v := rfPruneWorkAddr workAddr k mH mF)
    (Expr.eval_eq_of_eq
      (Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (v := rfCsrAddr workAddr k mH mF) (by simp))
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := k + mF) (by simp)) (by omega))
            (Expr.eval_const (by omega)) (by omega))
          (by dsimp only [rfCsrAddr]; omega))
        (Expr.eval_mul (Expr.eval_const (by omega))
          (Expr.eval_reg_of_eq (v := mH + 2 * mF) (by simp)) (by omega))
        (by dsimp only [rfCsrAddr]; omega))
      (by dsimp only [rfCsrAddr, rfPruneWorkAddr]; omega)) ?_
  refine runs_seq_assign_le (v := rhoNum)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := rhoAddr) (by simp [startState, args])) hrho1) ?_
  refine runs_seq_assign_le (v := rhoDen)
    (Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (v := rhoAddr) (by simp [startState, args]))
        (Expr.eval_const (by omega)) (by omega))
      hrho2) ?_
  refine runs_assign_le (v := rfCcap rhoNum rhoDen)
    (Expr.eval_add
      (Expr.eval_div
        (Expr.eval_sub
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (v := rhoDen) (by simp)) (by omega))
            (Expr.eval_reg_of_eq (v := rhoNum) (by simp)) (by omega))
          (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (v := rhoNum) (by simp)) (by omega))
      (Expr.eval_const (by omega)) hccap_lt) ?_ ?_
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl⟩ <;>
      simp [startState, args]
  · simp [Expr.size]

/-! ## 4. Stages 1 & 3 (`rfFillLocStmt`, `rfClearLocStmt`) -/

/-- Stage 1: populates `locAddr[verts[i]] := i` for `i < k`. -/
theorem rfFillLoc_triple {w n k mH mF rhoNum rhoDen
    vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (st₀ : State)
    (hvlen : verts.length = k) (hnd : verts.Nodup)
    (hverts_lt : ∀ u ∈ verts, u < n) (hlist : ListAt mem vertsAddr verts)
    (hdisj : DisjointRange locAddr n vertsAddr k)
    (hw : RemoveFakeWordBound w n k mH mF rhoNum rhoDen
      vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr)
    (hregs : RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st₀)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) rfFillLocStmt
      (normalPost fun st' =>
        RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st' ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem locAddr (locAddr + n) ∧
        (∀ a, (∀ u ∈ verts, a ≠ locAddr + u) → st'.mem a = mem a) ∧
        (∀ u ∈ verts, st'.mem (locAddr + u) = verts.idxOf u))
      (fun _ => 35 * k + 20) := by
  obtain ⟨_, hval⟩ := rfWorkSpace_word_lt hw
  have hw2 : 1 < 2 ^ w := by omega
  have hvk_w := hw.1
  have hloc_w := hw.2.2.2.2.1
  let Inv : ℕ → State → Prop := fun i st =>
    RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st ∧
    st.regs rfI = i ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem locAddr (locAddr + n) ∧
    (∀ a, (∀ u ∈ verts, a ≠ locAddr + u) → st.mem a = mem a) ∧
    (∀ j (hj : j < i), ∀ (hjk : j < verts.length), st.mem (locAddr + verts[j]'hjk) = j)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := rfI) (lo := .const 0) (hi := .reg rfK)
    (body := seqStmts
      [ .assign rfTmp1 (.load (.bin .add (.reg rfVerts) (.reg rfI)))
      , .store (.bin .add (.reg rfLoc) (.reg rfTmp1)) (.reg rfI) ])
    (P := fun st => st = st₀) (Inv := Inv) 18 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega), ?_⟩
      refine ⟨rfRegs_update_ge (by decide) hregs, by simp, rfl,
        hmem ▸ memFrame_refl mem _ _, fun a _ => by simp [hmem], fun j hj => by omega⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_k)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hpos, hfr, hpt, hmap⟩
      have hi_lt : i < verts.length := hvlen ▸ hilt
      have hv_lt : verts[i]'hi_lt < n := hverts_lt _ (List.getElem_mem hi_lt)
      have hmem_v : st.mem (vertsAddr + i) = verts[i]'hi_lt := by
        rw [hfr (vertsAddr + i) (disjointRange_outside hdisj (by omega) (by omega))]
        exact hlist i hi_lt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := verts[i]'hi_lt)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_verts) (Expr.eval_reg_of_eq hi) (by omega))
          hmem_v) ?_
      refine runs_store_le (x := locAddr + verts[i]'hi_lt) (v := i)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r_loc]))
          (Expr.eval_reg_of_eq (v := verts[i]'hi_lt) (by simp)) (by omega))
        (Expr.eval_reg_of_eq (v := i) (by simp [hi])) ?_ ?_
      · refine ⟨⟨rfRegs_update_ge (r := rfI) (by decide)
            (rfRegs_update_mem (rfRegs_update_ge (r := rfTmp1) (by decide) hr)),
          by simp, hpos,
          memFrame_trans hfr (memFrame_update (by omega) (by omega)),
          fun a ha => by
            dsimp only
            rw [Function.update_of_ne (ha _ (List.getElem_mem hi_lt))]
            exact hpt a ha, ?_⟩, by simp [hi]⟩
        intro j hj hjk
        dsimp only
        by_cases hji : j = i
        · subst hji; simp
        · have hne : verts[j]'hjk ≠ verts[i]'hi_lt := fun heq =>
            hji ((List.Nodup.getElem_inj_iff hnd).mp heq)
          rw [Function.update_of_ne (by omega)]
          exact hmap j (by omega) hjk
      · simp [Expr.size])
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr, _, hpos, hfr, hpt, hmap⟩
    refine ⟨hr, hpos, hfr, hpt, fun u hu => ?_⟩
    have hidx_lt : verts.idxOf u < verts.length := List.idxOf_lt_length_of_mem hu
    have hget : verts[verts.idxOf u]'hidx_lt = u := List.getElem_idxOf hidx_lt
    have := hmap (verts.idxOf u) (hvlen ▸ hidx_lt) hidx_lt
    rwa [hget] at this
  · exact False.elim hq

/-- Stage 3: clears `locAddr[verts[i]] := 0` for `i < k`. -/
theorem rfClearLoc_triple {w n k mH mF rhoNum rhoDen
    vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr : ℕ}
    (p : Program) (mem : ℕ → ℕ) (verts : List ℕ) (st₀ : State)
    (hvlen : verts.length = k)
    (hverts_lt : ∀ u ∈ verts, u < n) (hlist : ListAt mem vertsAddr verts)
    (hdisj : DisjointRange locAddr n vertsAddr k)
    (hw : RemoveFakeWordBound w n k mH mF rhoNum rhoDen
      vertsAddr hAddr fAddr rhoAddr locAddr outRAddr workAddr)
    (hregs : RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st₀)
    (hmem : st₀.mem = mem) :
    Triple w p (fun st => st = st₀) rfClearLocStmt
      (normalPost fun st' =>
        RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st' ∧
        st'.pos = st₀.pos ∧
        MemFrame mem st'.mem locAddr (locAddr + n) ∧
        (∀ a, (∀ u ∈ verts, a ≠ locAddr + u) → st'.mem a = mem a) ∧
        (∀ u ∈ verts, st'.mem (locAddr + u) = 0))
      (fun _ => 35 * k + 20) := by
  obtain ⟨_, hval⟩ := rfWorkSpace_word_lt hw
  have hw2 : 1 < 2 ^ w := by omega
  have hvk_w := hw.1
  have hloc_w := hw.2.2.2.2.1
  let Inv : ℕ → State → Prop := fun i st =>
    RfRegs k vertsAddr mH hAddr mF fAddr rhoAddr locAddr outRAddr workAddr rhoNum rhoDen st ∧
    st.regs rfI = i ∧ st.pos = st₀.pos ∧
    MemFrame mem st.mem locAddr (locAddr + n) ∧
    (∀ a, (∀ u ∈ verts, a ≠ locAddr + u) → st.mem a = mem a) ∧
    (∀ j (hj : j < i), ∀ (hjk : j < verts.length), st.mem (locAddr + verts[j]'hjk) = 0)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := rfI) (lo := .const 0) (hi := .reg rfK)
    (body := seqStmts
      [ .assign rfTmp1 (.load (.bin .add (.reg rfVerts) (.reg rfI)))
      , .store (.bin .add (.reg rfLoc) (.reg rfTmp1)) (.const 0) ])
    (P := fun st => st = st₀) (Inv := Inv) 18 0 k (Nat.zero_le k) hw2 (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const (by omega), ?_⟩
      refine ⟨rfRegs_update_ge (by decide) hregs, by simp, rfl,
        hmem ▸ memFrame_refl mem _ _, fun a _ => by simp [hmem], fun j hj => by omega⟩)
    (fun _ st _ _ hInv => hInv.2.1)
    (fun _ st _ _ hInv => Expr.eval_reg_of_eq hInv.1.r_k)
    (fun i _ hilt => by
      intro st ω ⟨hr, hi, hpos, hfr, hpt, hclr⟩
      have hi_lt : i < verts.length := hvlen ▸ hilt
      have hv_lt : verts[i]'hi_lt < n := hverts_lt _ (List.getElem_mem hi_lt)
      have hmem_v : st.mem (vertsAddr + i) = verts[i]'hi_lt := by
        rw [hfr (vertsAddr + i) (disjointRange_outside hdisj (by omega) (by omega))]
        exact hlist i hi_lt
      refine runs_start_le ?_
      dsimp only [seqStmts]
      refine runs_seq_assign_le (v := verts[i]'hi_lt)
        (Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr.r_verts) (Expr.eval_reg_of_eq hi) (by omega))
          hmem_v) ?_
      refine runs_store_le (x := locAddr + verts[i]'hi_lt) (v := 0)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := locAddr) (by simp [hr.r_loc]))
          (Expr.eval_reg_of_eq (v := verts[i]'hi_lt) (by simp)) (by omega))
        (Expr.eval_const (by omega)) ?_ ?_
      · refine ⟨⟨rfRegs_update_ge (r := rfI) (by decide)
            (rfRegs_update_mem (rfRegs_update_ge (r := rfTmp1) (by decide) hr)),
          by simp, hpos,
          memFrame_trans hfr (memFrame_update (by omega) (by omega)),
          fun a ha => by
            dsimp only
            rw [Function.update_of_ne (ha _ (List.getElem_mem hi_lt))]
            exact hpt a ha, ?_⟩, by simp [hi]⟩
        intro j hj hjk
        dsimp only
        by_cases hji : verts[j]'hjk = verts[i]'hi_lt
        · rw [hji]; simp
        · have hne_ji : j ≠ i := fun h => hji (by subst h; rfl)
          rw [Function.update_of_ne (by omega)]
          exact hclr j (by omega) hjk
      · simp [Expr.size])
  refine (hloop.strengthen_post ?_).mono_cost (fun _ _ => by simp [Expr.size]; omega)
  rintro (_ | _) st' hq
  · rcases hq with ⟨hr, _, hpos, hfr, hpt, hclr⟩
    refine ⟨hr, hpos, hfr, hpt, fun u hu => ?_⟩
    rcases List.getElem_of_mem hu with ⟨j, hj, rfl⟩
    exact hclr j (hvlen ▸ hj) hj
  · exact False.elim hq

end MinCostFlow.ExpanderDecomp
