module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase1Model
public import WordRAM.Logic

import WordRAM.Tactic

/-!
# First-phase step Phase 1 Word-RAM program and memory lemmas (`AssemblyFirstStepPhase1Prog`)

Defines the deterministic Word-RAM procedure `asmFirstScanBatchStmt`
(`[gPtr, cmpH, ctH, batch, words, vCap, eCap, h]`), its heap layout (`asmFirstScanBatchSpace`),
its memory/register invariants (`ScanMemAt`, `ScanGeom`, `ScanRegsAt`), the activation helper
verification (`asmScanActivate_runs`), and the three `ScanMemAt` update lemmas
(`scanMemAt_insert`, `scanMemAt_delete`, `scanMemAt_split`).

The single-iteration and full-loop proofs are in `AssemblyFirstStepPhase1Proof.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## 1. Space, layout offsets, and deterministic Word-RAM procedure -/

@[expose] public section

/-- Heap space allocated by `asmFirstScanBatchStmt`. -/
def asmFirstScanBatchSpace (vCap eCap words : ℕ) : ℕ :=
  3 + 2 * eCap + vCap + 6 * words

/-- Base addresses of the six arrays written by `asmFirstScanBatchStmt` starting at `h`. -/
def scanInsFlagBase (h : ℕ) : ℕ := h + 3
def scanDelFlagBase (h eCap : ℕ) : ℕ := h + 3 + eCap
def scanOrigVertBase (h eCap : ℕ) : ℕ := h + 3 + 2 * eCap
def scanNewCompsBase (h vCap eCap : ℕ) : ℕ := h + 3 + 2 * eCap + vCap
def scanDelEdgesBase (h vCap eCap words : ℕ) : ℕ := h + 3 + 2 * eCap + vCap + 4 * words
def scanInsEdgesBase (h vCap eCap words : ℕ) : ℕ := h + 3 + 2 * eCap + vCap + 5 * words

/-- Inline activation block: if `mem[ctH + 3 * reg rComp] = 0`, set it to `1`, append
`(reg rComp, reg rVert)` to `newComps` (base `reg 11`, count `reg 16`), and increment `reg 16`.
Uses scratch `reg 27`. -/
def asmScanActivateStmt (rComp rVert : ℕ) : Stmt :=
  .assign 27 (.load (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg rComp)))) ;;
  .cond (.bin .eq (.reg 27) (.const 0))
    (.store (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg rComp))) (.const 1) ;;
     .store (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 16))) (.reg rComp) ;;
     .store (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 16))) (.const 1)) (.reg rVert) ;;
     .assign 16 (.bin .add (.reg 16) (.const 1)))
    .nop

/-- Loop body processing one encoded update at `reg 15 = cur`.
Registers `0..7` = `[gPtr, cmpH, ctH, batch, words, vCap, eCap, h]`,
`8..13` = `[insFlagBase, delFlagBase, origVertBase, newCompsBase, delEdgesBase, insEdgesBase]`,
`14 = nUpd`, `15 = cur`, `16 = nNew`, `17 = nDel`, `18 = nIns`, `19 = i`, `20..27` scratch. -/
def asmFirstScanBatchBody : Stmt :=
  .assign 20 (.load (.reg 15)) ;;
  .cond (.bin .eq (.reg 20) (.const 0))
    (.assign 21 (.load (.bin .add (.reg 15) (.const 1))) ;;
     .assign 22 (.load (.bin .add (.reg 15) (.const 2))) ;;
     .assign 23 (.load (.bin .add (.reg 15) (.const 3))) ;;
     .store (.bin .add (.reg 8) (.reg 21)) (.const 1) ;;
     .store (.bin .add (.reg 13) (.reg 18)) (.reg 21) ;;
     .assign 18 (.bin .add (.reg 18) (.const 1)) ;;
     .assign 24 (.load (.bin .add (.reg 1) (.reg 22))) ;;
     asmScanActivateStmt 24 22 ;;
     .assign 25 (.load (.bin .add (.reg 1) (.reg 23))) ;;
     asmScanActivateStmt 25 23 ;;
     .assign 15 (.bin .add (.reg 15) (.const 4)))
    (.cond (.bin .eq (.reg 20) (.const 1))
      (.assign 21 (.load (.bin .add (.reg 15) (.const 1))) ;;
       .store (.bin .add (.reg 9) (.reg 21)) (.const 1) ;;
       .store (.bin .add (.reg 12) (.reg 17)) (.reg 21) ;;
       .assign 17 (.bin .add (.reg 17) (.const 1)) ;;
       .assign 22 (.load (.bin .add (.reg 8) (.reg 21))) ;;
       .cond (.bin .eq (.reg 22) (.const 0))
         (.assign 23 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
            (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 3) (.reg 6)))) (.reg 21))) ;;
          .assign 24 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
            (.bin .mul (.const 4) (.reg 5))) (.reg 23))) ;;
          .assign 25 (.load (.bin .add (.reg 1) (.reg 24))) ;;
          asmScanActivateStmt 25 24 ;;
          .assign 23 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
            (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 4) (.reg 6)))) (.reg 21))) ;;
          .assign 24 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
            (.bin .mul (.const 4) (.reg 5))) (.reg 23))) ;;
          .assign 25 (.load (.bin .add (.reg 1) (.reg 24))) ;;
          asmScanActivateStmt 25 24)
         .nop ;;
       .assign 15 (.bin .add (.reg 15) (.const 2)))
      (.assign 21 (.load (.bin .add (.reg 15) (.const 1))) ;;
       .assign 22 (.load (.bin .add (.reg 15) (.const 2))) ;;
       .assign 23 (.load (.bin .add (.reg 15) (.const 3))) ;;
       .assign 24 (.load (.bin .add (.reg 15) (.const 4))) ;;
       .assign 25 (.load (.bin .add (.reg 1) (.reg 21))) ;;
       .store (.bin .add (.reg 1) (.reg 22)) (.reg 25) ;;
       .assign 26 (.load (.bin .add (.reg 10) (.reg 21))) ;;
       .cond (.bin .eq (.reg 26) (.const 0))
         (.store (.bin .add (.reg 10) (.reg 22)) (.bin .add (.reg 21) (.const 1)))
         (.store (.bin .add (.reg 10) (.reg 22)) (.reg 26)) ;;
       asmScanActivateStmt 25 21 ;;
       .assign 15 (.bin .add (.bin .add (.bin .add (.reg 15) (.const 5)) (.reg 23)) (.reg 24))))

/-- **Phase 1 batch-scan procedure**, `[gPtr, cmpH, ctH, batch, words, vCap, eCap, h]`. -/
def asmFirstScanBatchStmt : Stmt :=
  .assign 8 (.bin .add (.reg 7) (.const 3)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 6)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 6)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 5)) ;;
  .assign 12 (.bin .add (.reg 11) (.bin .mul (.const 4) (.reg 4))) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 4)) ;;
  .assign 14 (.load (.reg 3)) ;;
  .assign 15 (.bin .add (.reg 3) (.const 1)) ;;
  .assign 16 (.const 0) ;;
  .assign 17 (.const 0) ;;
  .assign 18 (.const 0) ;;
  forRange 19 (.const 0) (.reg 14) asmFirstScanBatchBody ;;
  .store (.reg 7) (.reg 16) ;;
  .store (.bin .add (.reg 7) (.const 1)) (.reg 17) ;;
  .store (.bin .add (.reg 7) (.const 2)) (.reg 18) ;;
  .ret (.bin .add (.reg 13) (.reg 4))

/-- Memory representation of `ScanBatchState` during `asmFirstScanBatchStmt`. -/
def ScanMemAt (mem₀ mem : ℕ → ℕ) (cmpH ctH nComp vCap eCap words h : ℕ)
    (sb : ScanBatchState) : Prop :=
  (∀ v < vCap, mem (cmpH + v) = sb.cmpMap v) ∧
  (∀ c < nComp, mem (ctH + 3 * c) = if sb.actFlag c then 1 else 0) ∧
  (∀ e < eCap, mem (scanInsFlagBase h + e) = if sb.insFlag e then 1 else 0) ∧
  (∀ e < eCap, mem (scanDelFlagBase h eCap + e) = if sb.delFlag e then 1 else 0) ∧
  (∀ v < vCap, mem (scanOrigVertBase h eCap + v) = sb.origVert v) ∧
  (∀ i (hi : i < sb.newComps.length),
    mem (scanNewCompsBase h vCap eCap + 2 * i) = sb.newComps[i].1 ∧
    mem (scanNewCompsBase h vCap eCap + 2 * i + 1) = sb.newComps[i].2) ∧
  ListAt mem (scanDelEdgesBase h vCap eCap words) sb.delEdges ∧
  ListAt mem (scanInsEdgesBase h vCap eCap words) sb.insEdges ∧
  (∀ a < h, (a < cmpH ∨ cmpH + vCap ≤ a) →
    (∀ c < nComp, a ≠ ctH + 3 * c) → mem a = mem₀ a) ∧
  ZeroFrom mem (h + asmFirstScanBatchSpace vCap eCap words)

/-- Static geometry & disjointness hypotheses for `asmFirstScanBatchStmt`. -/
structure ScanGeom (w gPtr cmpH ctH nComp batch words vCap eCap h : ℕ) : Prop where
  hw16 : 16 ≤ 2 ^ w
  hg_le : gPtr + dynGraphSize vCap eCap ≤ h
  hcmp_le : vCap = 0 ∨ cmpH + vCap ≤ h
  hct_le : nComp = 0 ∨ ctH + 3 * nComp ≤ h
  hbat_le : batch + words ≤ h
  hdisj_g_cmp : vCap = 0 ∨ gPtr + dynGraphSize vCap eCap ≤ cmpH ∨ cmpH + vCap ≤ gPtr
  hdisj_g_ct : nComp = 0 ∨ gPtr + dynGraphSize vCap eCap ≤ ctH ∨ ctH + 3 * nComp ≤ gPtr
  hdisj_bat_cmp : vCap = 0 ∨ batch + words ≤ cmpH ∨ cmpH + vCap ≤ batch
  hdisj_bat_ct : nComp = 0 ∨ batch + words ≤ ctH ∨ ctH + 3 * nComp ≤ batch
  hdisj_cmp_ct : vCap = 0 ∨ nComp = 0 ∨ cmpH + vCap ≤ ctH ∨ ctH + 3 * nComp ≤ cmpH
  hsp : h + asmFirstScanBatchSpace vCap eCap words < 2 ^ w

/-- Loop register invariant for `asmFirstScanBatchStmt`. -/
def ScanRegsAt (regs : ℕ → ℕ) (gPtr cmpH ctH batch words vCap eCap h nUpd cur : ℕ)
    (sb : ScanBatchState) (i : ℕ) : Prop :=
  regs 0 = gPtr ∧ regs 1 = cmpH ∧ regs 2 = ctH ∧ regs 3 = batch ∧ regs 4 = words ∧
  regs 5 = vCap ∧ regs 6 = eCap ∧ regs 7 = h ∧
  regs 8 = scanInsFlagBase h ∧ regs 9 = scanDelFlagBase h eCap ∧
  regs 10 = scanOrigVertBase h eCap ∧ regs 11 = scanNewCompsBase h vCap eCap ∧
  regs 12 = scanDelEdgesBase h vCap eCap words ∧ regs 13 = scanInsEdgesBase h vCap eCap words ∧
  regs 14 = nUpd ∧ regs 15 = cur ∧
  regs 16 = sb.newComps.length ∧ regs 17 = sb.delEdges.length ∧
  regs 18 = sb.insEdges.length ∧ regs 19 = i

end

/-! ## 2. Determinism and helper lemmas -/

public section

theorem asmFirstScanBatchStmt_noRand : asmFirstScanBatchStmt.NoRand := by
  simp [asmFirstScanBatchStmt, asmFirstScanBatchBody, asmScanActivateStmt,
    forRange, forUp, Stmt.NoRand]

lemma batchBodyAt_len_le {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} :
    ∀ {U : List Update} {W : ℕ}, BatchBodyAt mem a G U W → 2 * U.length ≤ W
  | [], _, _ => by simp
  | u :: us, W, ⟨len, hle, hu, hrest⟩ => by
    have hlen2 : 2 ≤ len := by
      cases u with
      | insert _ _ _ => exact hu.1 ▸ (by omega)
      | delete _ => exact hu.1 ▸ (by omega)
      | split _ _ _ _ => rcases hu with ⟨_, _, _, _, _, _, h, _⟩ | ⟨_, _, _, _, _, _, h, _⟩ <;> omega
    have ih := batchBodyAt_len_le hrest
    simp only [List.length_cons]; omega

lemma dynGraph_tail_head_read {mem : ℕ → ℕ} {gPtr vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem gPtr vCap eCap G) {e : ℕ} (he : e ∈ G.E) :
    let ts := mem (dgETailSlotBase gPtr vCap eCap + e)
    let hs := mem (dgEHeadSlotBase gPtr vCap eCap + e)
    ts < vCap ∧ mem (dgIntToExtBase gPtr vCap + ts) = G.tail e ∧
    hs < vCap ∧ mem (dgIntToExtBase gPtr vCap + hs) = G.head e := by
  obtain ⟨hVal, hVlt, -, -, -, -, -, -, -, hext, -, -, -, hslot, -⟩ := hG
  obtain ⟨hts, hhs⟩ := hslot e he
  obtain ⟨htIn, htBack⟩ := hext _ (hVal e he).1
  obtain ⟨hhIn, hhBack⟩ := hext _ (hVal e he).2
  exact ⟨by rw [hts]; exact hVlt _ htIn, by rw [hts]; exact htBack,
         by rw [hhs]; exact hVlt _ hhIn, by rw [hhs]; exact hhBack⟩

/-- Execution of `asmScanActivateStmt rComp rVert` matching `scanActivate`. -/
lemma asmScanActivate_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {gPtr cmpH ctH nComp batch words vCap eCap h : ℕ} {mem₀ : ℕ → ℕ}
    {rComp rVert c v : ℕ} {sb : ScanBatchState} {st : State}
    (hG : ScanGeom w gPtr cmpH ctH nComp batch words vCap eCap h)
    (hr2 : st.regs 2 = ctH) (hr11 : st.regs 11 = scanNewCompsBase h vCap eCap)
    (hr16 : st.regs 16 = sb.newComps.length)
    (hrC : st.regs rComp = c) (hrV : st.regs rVert = v)
    (hrC_ne : rComp ≠ 27) (hrV_ne : rVert ≠ 27)
    (hc : c < nComp) (hv : v < vCap) (hnew_lt : sb.newComps.length < 2 * words)
    (hM : ScanMemAt mem₀ st.mem cmpH ctH nComp vCap eCap words h sb) :
    ∃ st' cost,
      Runs w p ω (asmScanActivateStmt rComp rVert) st .normal st' cost ∧
      (∀ r, r ≠ 16 → r ≠ 27 → st'.regs r = st.regs r) ∧
      st'.regs 16 = (scanActivate sb c v).newComps.length ∧
      ScanMemAt mem₀ st'.mem cmpH ctH nComp vCap eCap words h (scanActivate sb c v) ∧
      cost ≤ 45 := by
  have hsp' : h + (3 + 2 * eCap + vCap + 6 * words) < 2 ^ w := hG.hsp
  have hct_c : st.mem (ctH + 3 * c) = if sb.actFlag c then 1 else 0 := hM.2.1 c hc
  have hct_w : ctH + 3 * c < 2 ^ w := by have := hG.hct_le; omega
  have h3c_w : 3 * c < 2 ^ w := by have := hG.hct_le; omega
  have h1w : 1 < 2 ^ w := by have := hG.hw16; omega
  have h3w : 3 < 2 ^ w := by have := hG.hw16; omega
  set flagV := if sb.actFlag c then 1 else 0
  have heLoad : (Expr.load (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg rComp)))).eval w st =
      some flagV :=
    Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq hr2)
        (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq hrC) h3c_w) hct_w) hct_c
  set st1 : State := ⟨st.mem, Function.update st.regs 27 flagV, st.pos⟩
  have hr_a27 : Runs w p ω (.assign 27 (.load (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg rComp)))))
      st .normal st1 7 :=
    runs_assign_iff.mpr ⟨flagV, heLoad, rfl, rfl, rfl⟩
  cases hact : sb.actFlag c with
  | true =>
    have hfl1 : flagV = 1 := by simp [flagV, hact]
    have heCond : (Expr.bin .eq (.reg 27) (.const 0)).eval w st1 = some 0 := by
      simp [Expr.eval, st1, hfl1, BinOp.eval, (by omega : 0 < 2 ^ w)]
    have hnop : Runs w p ω .nop st1 .normal st1 1 := runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
    rw [show scanActivate sb c v = sb by simp [scanActivate, hact]]
    refine ⟨st1, 13, runs_seq_iff.mpr (Or.inr ⟨st1, 7, 5, hr_a27,
      runs_cond_iff.mpr ⟨0, 1, heCond, by simpa using hnop, rfl⟩, rfl⟩),
      fun r _ h27 => by simp [st1, Function.update_of_ne h27],
      by simp [st1, hr16], hM, by omega⟩
  | false =>
    have hfl0 : flagV = 0 := by simp [flagV, hact]
    have heCond : (Expr.bin .eq (.reg 27) (.const 0)).eval w st1 = some 1 := by
      simp [Expr.eval, st1, hfl0, BinOp.eval, (by omega : 0 < 2 ^ w), h1w]
    set n0 := sb.newComps.length
    have hbase : scanNewCompsBase h vCap eCap = h + 3 + 2 * eCap + vCap := rfl
    have hst1_2 : st1.regs 2 = ctH := by simp [st1, hr2]
    have hst1_11 : st1.regs 11 = scanNewCompsBase h vCap eCap := by simp [st1, hr11]
    have hst1_16 : st1.regs 16 = n0 := by simp [st1, hr16]
    have hst1_C : st1.regs rComp = c := by simp [st1, Function.update_of_ne hrC_ne, hrC]
    have hst1_V : st1.regs rVert = v := by simp [st1, Function.update_of_ne hrV_ne, hrV]
    set mem1 := Function.update st.mem (ctH + 3 * c) 1
    set mem2 := Function.update mem1 (scanNewCompsBase h vCap eCap + 2 * n0) c
    set mem3 := Function.update mem2 (scanNewCompsBase h vCap eCap + 2 * n0 + 1) v
    set regs3 := Function.update st1.regs 16 (n0 + 1)
    have hr_s1 : Runs w p ω (.store (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg rComp))) (.const 1))
        st1 .normal ⟨mem1, st1.regs, st.pos⟩ 7 :=
      runs_store_iff.mpr ⟨ctH + 3 * c, 1,
        Expr.eval_add (Expr.eval_reg_of_eq hst1_2)
          (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq hst1_C) h3c_w) hct_w,
        Expr.eval_const h1w, rfl, rfl, rfl⟩
    have hr_s2 : Runs w p ω (.store (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 16))) (.reg rComp))
        ⟨mem1, st1.regs, st.pos⟩ .normal ⟨mem2, st1.regs, st.pos⟩ 7 :=
      runs_store_iff.mpr ⟨scanNewCompsBase h vCap eCap + 2 * n0, c,
        Expr.eval_add (Expr.eval_reg_of_eq hst1_11)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hst1_16) (by omega)) (by omega),
        Expr.eval_reg_of_eq hst1_C, rfl, rfl, rfl⟩
    have hr_s3 : Runs w p ω (.store (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 16))) (.const 1)) (.reg rVert))
        ⟨mem2, st1.regs, st.pos⟩ .normal ⟨mem3, st1.regs, st.pos⟩ 9 :=
      runs_store_iff.mpr ⟨scanNewCompsBase h vCap eCap + 2 * n0 + 1, v,
        Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hst1_11)
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hst1_16) (by omega)) (by omega))
          (Expr.eval_const h1w) (by omega),
        Expr.eval_reg_of_eq hst1_V, rfl, rfl, rfl⟩
    have hr_a16 : Runs w p ω (.assign 16 (.bin .add (.reg 16) (.const 1)))
        ⟨mem3, st1.regs, st.pos⟩ .normal ⟨mem3, regs3, st.pos⟩ 4 :=
      runs_assign_iff.mpr ⟨n0 + 1,
        Expr.eval_add (Expr.eval_reg_of_eq hst1_16) (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
    have hbody := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_s1,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_s2, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_s3, hr_a16, rfl⟩), rfl⟩), rfl⟩)
    have hrun : Runs w p ω (asmScanActivateStmt rComp rVert) st .normal ⟨mem3, regs3, st.pos⟩
        (7 + (3 + (7 + (7 + (9 + 4 + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st1, 7, _, hr_a27,
        runs_cond_iff.mpr ⟨1, _, heCond, by simpa using hbody, rfl⟩, rfl⟩)
    rw [show scanActivate sb c v =
      { sb with actFlag := Function.update sb.actFlag c true, newComps := sb.newComps ++ [(c, v)] }
      by simp [scanActivate, hact]]
    obtain ⟨hMc, hMct, hMif, hMdf, hMo, hMn, hMde, hMie, hMfr, hMzf⟩ := hM
    have hmem3_of : ∀ a, a ≠ ctH + 3 * c → a ≠ scanNewCompsBase h vCap eCap + 2 * n0 →
        a ≠ scanNewCompsBase h vCap eCap + 2 * n0 + 1 → mem3 a = st.mem a := fun a h1 h2 h3 => by
      simp [mem3, mem2, mem1, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
    have hcl := hG.hcmp_le; have htl := hG.hct_le; have hcc := hG.hdisj_cmp_ct
    refine ⟨⟨mem3, regs3, st.pos⟩, _, hrun,
      fun r h16 h27 => by simp [regs3, st1, Function.update_of_ne h16, Function.update_of_ne h27],
      by simp [regs3, n0], ?_, by omega⟩
    show ScanMemAt mem₀ mem3 cmpH ctH nComp vCap eCap words h _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx; rw [hmem3_of _ (by omega) (by omega) (by omega)]; exact hMc x hx
    · intro c' hc'
      by_cases hEq : c' = c
      · subst hEq; simp only [Function.update_self, ↓reduceIte, mem3, mem2, mem1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      · dsimp only; rw [hmem3_of _ (by omega) (by omega) (by omega)]; simp only [Function.update_of_ne hEq]; exact hMct c' hc'
    · intro e he; rw [hmem3_of _ (by unfold scanInsFlagBase; omega) (by unfold scanInsFlagBase; omega)
        (by unfold scanInsFlagBase; omega)]; exact hMif e he
    · intro e he; rw [hmem3_of _ (by unfold scanDelFlagBase; omega) (by unfold scanDelFlagBase; omega)
        (by unfold scanDelFlagBase; omega)]; exact hMdf e he
    · intro x hx; rw [hmem3_of _ (by unfold scanOrigVertBase; omega) (by unfold scanOrigVertBase; omega)
        (by unfold scanOrigVertBase; omega)]; exact hMo x hx
    · intro i hi
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      by_cases hilt : i < n0
      · rw [List.getElem_append_left hilt, hmem3_of _ (by omega) (by omega) (by omega),
          hmem3_of _ (by omega) (by omega) (by omega)]; exact hMn i hilt
      · have hiEq : i = n0 := by omega
        subst hiEq; rw [List.getElem_append_right (le_refl _)]; simp only [n0, Nat.sub_self, List.getElem_cons_zero]
        exact ⟨by simp [mem3, mem2, n0],
               by simp [mem3, n0]⟩
    · intro i hi
      rw [hmem3_of _ (by unfold scanDelEdgesBase; omega) (by unfold scanDelEdgesBase; omega)
        (by unfold scanDelEdgesBase; omega)]; exact hMde i hi
    · intro i hi
      rw [hmem3_of _ (by unfold scanInsEdgesBase; omega) (by unfold scanInsEdgesBase; omega)
        (by unfold scanInsEdgesBase; omega)]; exact hMie i hi
    · intro a ha h1 h2; rw [hmem3_of a (h2 c hc) (by omega) (by omega)]; exact hMfr a ha h1 h2
    · intro a ha; unfold asmFirstScanBatchSpace at ha
      rw [hmem3_of a (by omega) (by omega) (by omega)]; exact hMzf a ha

/-! ## 3. Memory-update lemmas for `ScanMemAt` -/

lemma scanMemAt_insert {w gPtr cmpH ctH nComp batch words vCap eCap h e : ℕ}
    {mem₀ mem : ℕ → ℕ} {sb : ScanBatchState}
    (hGeo : ScanGeom w gPtr cmpH ctH nComp batch words vCap eCap h)
    (he : e < eCap) (hnew_le : sb.newComps.length ≤ 2 * words)
    (hdel_le : sb.delEdges.length ≤ words) (hins_lt : sb.insEdges.length < words)
    (hM : ScanMemAt mem₀ mem cmpH ctH nComp vCap eCap words h sb) :
    ScanMemAt mem₀
      (Function.update (Function.update mem (scanInsFlagBase h + e) 1)
        (scanInsEdgesBase h vCap eCap words + sb.insEdges.length) e)
      cmpH ctH nComp vCap eCap words h
      { sb with insFlag := Function.update sb.insFlag e true, insEdges := sb.insEdges ++ [e] } := by
  obtain ⟨hMc, hMct, hMif, hMdf, hMo, hMn, hMde, hMie, hMfr, hMzf⟩ := hM
  have hcl := hGeo.hcmp_le; have htl := hGeo.hct_le
  have h1 : ∀ x, x < h → x ≠ scanInsFlagBase h + e := fun x hx => by unfold scanInsFlagBase; omega
  have h2 : ∀ x, x < h → x ≠ scanInsEdgesBase h vCap eCap words + sb.insEdges.length :=
    fun x hx => by unfold scanInsEdgesBase; omega
  refine ⟨fun v hv => by rw [Function.update_of_ne (h2 _ (by omega)), Function.update_of_ne (h1 _ (by omega))]; exact hMc v hv,
    fun c hc => by rw [Function.update_of_ne (h2 _ (by omega)), Function.update_of_ne (h1 _ (by omega))]; exact hMct c hc,
    fun e' he' => by
      rw [Function.update_of_ne (by unfold scanInsFlagBase scanInsEdgesBase; omega)]
      by_cases hEq : e' = e
      · subst hEq; simp
      · dsimp only; rw [Function.update_of_ne (by omega)]; simp only [Function.update_of_ne hEq]; exact hMif e' he',
    fun e' he' => by
      rw [Function.update_of_ne (by unfold scanDelFlagBase scanInsEdgesBase; omega),
          Function.update_of_ne (by unfold scanDelFlagBase scanInsFlagBase; omega)]; exact hMdf e' he',
    fun v hv => by
      rw [Function.update_of_ne (by unfold scanOrigVertBase scanInsEdgesBase; omega),
          Function.update_of_ne (by unfold scanOrigVertBase scanInsFlagBase; omega)]; exact hMo v hv,
    fun j hj => by
      change j < sb.newComps.length at hj
      rw [Function.update_of_ne (by unfold scanNewCompsBase scanInsEdgesBase; omega),
          Function.update_of_ne (by unfold scanNewCompsBase scanInsFlagBase; omega),
          Function.update_of_ne (by unfold scanNewCompsBase scanInsEdgesBase; omega),
          Function.update_of_ne (by unfold scanNewCompsBase scanInsFlagBase; omega)]; exact hMn j hj,
    fun j hj => by
      change j < sb.delEdges.length at hj
      rw [Function.update_of_ne (by unfold scanDelEdgesBase scanInsEdgesBase; omega),
          Function.update_of_ne (by unfold scanDelEdgesBase scanInsFlagBase; omega)]; exact hMde j hj,
    fun j hj => by
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      by_cases hjlt : j < sb.insEdges.length
      · rw [List.getElem_append_left hjlt, Function.update_of_ne (by omega),
            Function.update_of_ne (by unfold scanInsEdgesBase scanInsFlagBase; omega)]; exact hMie j hjlt
      · have hjEq : j = sb.insEdges.length := by omega
        subst hjEq; rw [List.getElem_append_right (le_refl _)]; simp,
    fun x hx ha hb => by rw [Function.update_of_ne (h2 _ hx), Function.update_of_ne (h1 _ hx)]; exact hMfr x hx ha hb,
    fun x hx => by
      unfold asmFirstScanBatchSpace at hx
      rw [Function.update_of_ne (by unfold scanInsEdgesBase; omega),
          Function.update_of_ne (by unfold scanInsFlagBase; omega)]; exact hMzf x hx⟩

lemma scanMemAt_delete {w gPtr cmpH ctH nComp batch words vCap eCap h e : ℕ}
    {mem₀ mem : ℕ → ℕ} {sb : ScanBatchState}
    (hGeo : ScanGeom w gPtr cmpH ctH nComp batch words vCap eCap h)
    (he : e < eCap) (hnew_le : sb.newComps.length ≤ 2 * words) (hdel_lt : sb.delEdges.length < words)
    (hM : ScanMemAt mem₀ mem cmpH ctH nComp vCap eCap words h sb) :
    ScanMemAt mem₀
      (Function.update (Function.update mem (scanDelFlagBase h eCap + e) 1)
        (scanDelEdgesBase h vCap eCap words + sb.delEdges.length) e)
      cmpH ctH nComp vCap eCap words h
      { sb with delFlag := Function.update sb.delFlag e true, delEdges := sb.delEdges ++ [e] } := by
  obtain ⟨hMc, hMct, hMif, hMdf, hMo, hMn, hMde, hMie, hMfr, hMzf⟩ := hM
  have hcl := hGeo.hcmp_le; have htl := hGeo.hct_le
  have h1 : ∀ x, x < h → x ≠ scanDelFlagBase h eCap + e := fun x hx => by unfold scanDelFlagBase; omega
  have h2 : ∀ x, x < h → x ≠ scanDelEdgesBase h vCap eCap words + sb.delEdges.length :=
    fun x hx => by unfold scanDelEdgesBase; omega
  refine ⟨fun v hv => by rw [Function.update_of_ne (h2 _ (by omega)), Function.update_of_ne (h1 _ (by omega))]; exact hMc v hv,
    fun c hc => by rw [Function.update_of_ne (h2 _ (by omega)), Function.update_of_ne (h1 _ (by omega))]; exact hMct c hc,
    fun e' he' => by
      rw [Function.update_of_ne (by unfold scanInsFlagBase scanDelEdgesBase; omega),
          Function.update_of_ne (by unfold scanInsFlagBase scanDelFlagBase; omega)]; exact hMif e' he',
    fun e' he' => by
      rw [Function.update_of_ne (by unfold scanDelFlagBase scanDelEdgesBase; omega)]
      by_cases hEq : e' = e
      · subst hEq; simp
      · dsimp only; rw [Function.update_of_ne (by omega)]; simp only [Function.update_of_ne hEq]; exact hMdf e' he',
    fun v hv => by
      rw [Function.update_of_ne (by unfold scanOrigVertBase scanDelEdgesBase; omega),
          Function.update_of_ne (by unfold scanOrigVertBase scanDelFlagBase; omega)]; exact hMo v hv,
    fun j hj => by
      change j < sb.newComps.length at hj
      rw [Function.update_of_ne (by unfold scanNewCompsBase scanDelEdgesBase; omega),
          Function.update_of_ne (by unfold scanNewCompsBase scanDelFlagBase; omega),
          Function.update_of_ne (by unfold scanNewCompsBase scanDelEdgesBase; omega),
          Function.update_of_ne (by unfold scanNewCompsBase scanDelFlagBase; omega)]; exact hMn j hj,
    fun j hj => by
      simp only [List.length_append, List.length_cons, List.length_nil] at hj
      by_cases hjlt : j < sb.delEdges.length
      · rw [List.getElem_append_left hjlt, Function.update_of_ne (by omega),
            Function.update_of_ne (by unfold scanDelEdgesBase scanDelFlagBase; omega)]; exact hMde j hjlt
      · have hjEq : j = sb.delEdges.length := by omega
        subst hjEq; rw [List.getElem_append_right (le_refl _)]; simp,
    fun j hj => by
      rw [Function.update_of_ne (by unfold scanInsEdgesBase scanDelEdgesBase; omega),
          Function.update_of_ne (by unfold scanInsEdgesBase scanDelFlagBase; omega)]; exact hMie j hj,
    fun x hx ha hb => by rw [Function.update_of_ne (h2 _ hx), Function.update_of_ne (h1 _ hx)]; exact hMfr x hx ha hb,
    fun x hx => by
      unfold asmFirstScanBatchSpace at hx
      rw [Function.update_of_ne (by unfold scanDelEdgesBase; omega),
          Function.update_of_ne (by unfold scanDelFlagBase; omega)]; exact hMzf x hx⟩

lemma scanMemAt_split {w gPtr cmpH ctH nComp batch words vCap eCap h v v' ov' : ℕ}
    {mem₀ mem : ℕ → ℕ} {sb : ScanBatchState}
    (hGeo : ScanGeom w gPtr cmpH ctH nComp batch words vCap eCap h)
    (hv' : v' < vCap)
    (hM : ScanMemAt mem₀ mem cmpH ctH nComp vCap eCap words h sb) :
    let sb1 : ScanBatchState :=
      { sb with
        cmpMap := Function.update sb.cmpMap v' (sb.cmpMap v)
        origVert := Function.update sb.origVert v' ov' }
    ScanMemAt mem₀
      (Function.update (Function.update mem (cmpH + v') (sb.cmpMap v))
        (scanOrigVertBase h eCap + v') ov')
      cmpH ctH nComp vCap eCap words h sb1 := by
  intro sb1
  obtain ⟨hMc, hMct, hMif, hMdf, hMo, hMn, hMde, hMie, hMfr, hMzf⟩ := hM
  have hcl := hGeo.hcmp_le; have htl := hGeo.hct_le; have hcc := hGeo.hdisj_cmp_ct
  have h2 : ∀ x, x < h → x ≠ scanOrigVertBase h eCap + v' := fun x hx => by unfold scanOrigVertBase; omega
  refine ⟨fun x hx => by
      rw [Function.update_of_ne (h2 _ (by omega))]
      by_cases hEq : x = v'
      · subst hEq; simp [sb1]
      · dsimp only [sb1]; rw [Function.update_of_ne (by omega), Function.update_of_ne hEq]; exact hMc x hx,
    fun c hc => by rw [Function.update_of_ne (h2 _ (by omega)), Function.update_of_ne (by omega)]; exact hMct c hc,
    fun e' he' => by
      rw [Function.update_of_ne (by unfold scanInsFlagBase scanOrigVertBase; omega),
          Function.update_of_ne (by unfold scanInsFlagBase; omega)]; exact hMif e' he',
    fun e' he' => by
      rw [Function.update_of_ne (by unfold scanDelFlagBase scanOrigVertBase; omega),
          Function.update_of_ne (by unfold scanDelFlagBase; omega)]; exact hMdf e' he',
    fun x hx => by
      by_cases hEq : x = v'
      · subst hEq; simp [sb1]
      · dsimp only [sb1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by unfold scanOrigVertBase; omega),
            Function.update_of_ne hEq]; exact hMo x hx,
    fun j hj => by
      rw [Function.update_of_ne (by unfold scanNewCompsBase scanOrigVertBase; omega),
          Function.update_of_ne (by unfold scanNewCompsBase; omega),
          Function.update_of_ne (by unfold scanNewCompsBase scanOrigVertBase; omega),
          Function.update_of_ne (by unfold scanNewCompsBase; omega)]; exact hMn j hj,
    fun j hj => by
      rw [Function.update_of_ne (by unfold scanDelEdgesBase scanOrigVertBase; omega),
          Function.update_of_ne (by unfold scanDelEdgesBase; omega)]; exact hMde j hj,
    fun j hj => by
      rw [Function.update_of_ne (by unfold scanInsEdgesBase scanOrigVertBase; omega),
          Function.update_of_ne (by unfold scanInsEdgesBase; omega)]; exact hMie j hj,
    fun x hx ha hb => by rw [Function.update_of_ne (h2 _ hx), Function.update_of_ne (by omega)]; exact hMfr x hx ha hb,
    fun x hx => by
      unfold asmFirstScanBatchSpace at hx
      rw [Function.update_of_ne (by unfold scanOrigVertBase; omega),
          Function.update_of_ne (by omega)]; exact hMzf x hx⟩

lemma rAssignLe {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr} {s : Stmt}
    {st st' : State} {v K T : ℕ} {o : Outcome}
    (he : e.eval w st = some v)
    (hrest : ∃ c, Runs w p ω s { st with regs := Function.update st.regs r v } o st' c ∧ K + (e.size + 2) + c ≤ T) :
    ∃ c, Runs w p ω (.assign r e ;; s) st o st' c ∧ K + c ≤ T := by
  obtain ⟨c, hr, hc⟩ := hrest
  exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨_, _, _, runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr, rfl⟩), by omega⟩

lemma rStoreLe {w : ℕ} {p : Program} {ω : ℕ → Bool} {ea ev : Expr} {s : Stmt}
    {st st' : State} {a v K T : ℕ} {o : Outcome}
    (ha : ea.eval w st = some a) (hv : ev.eval w st = some v)
    (hrest : ∃ c, Runs w p ω s { st with mem := Function.update st.mem a v } o st' c ∧ K + (ea.size + ev.size + 2) + c ≤ T) :
    ∃ c, Runs w p ω (.store ea ev ;; s) st o st' c ∧ K + c ≤ T := by
  obtain ⟨c, hr, hc⟩ := hrest
  exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨_, _, _, runs_store_iff.mpr ⟨a, v, ha, hv, rfl, rfl, rfl⟩, hr, rfl⟩), by omega⟩

lemma rCondTLe {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st st' : State} {v K T : ℕ} {o : Outcome}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h : ∃ c, Runs w p ω s₁ st o st' c ∧ K + (e.size + 1) + c ≤ T) :
    ∃ c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ K + c ≤ T := by
  obtain ⟨c, hr, hc⟩ := h
  exact ⟨_, runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩, by omega⟩

lemma rCondFLe {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st st' : State} {K T : ℕ} {o : Outcome}
    (he : e.eval w st = some 0)
    (h : ∃ c, Runs w p ω s₂ st o st' c ∧ K + (e.size + 1) + c ≤ T) :
    ∃ c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ K + c ≤ T := by
  obtain ⟨c, hr, hc⟩ := h
  exact ⟨_, runs_cond_iff.mpr ⟨0, c, he, by simpa using hr, rfl⟩, by omega⟩

end

end MinCostFlow.SparseCore.Program
