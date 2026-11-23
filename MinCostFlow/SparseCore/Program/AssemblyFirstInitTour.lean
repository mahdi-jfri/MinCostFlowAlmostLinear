module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBuild
public import MinCostFlow.SparseCore.Program.TourBranchInit

/-!
# The build of a branch at its init: the record words and the tour (`AssemblyFirstInitTour`)

The build of a branch at its init (`AsmFirstInitBuildAt`, `AssemblyFirstInitBuild.lean`) writes the
record of the branch at the heap pointer `h` and builds the parts of the branch above it. This file
does its first two steps, as a piece `asmFirstInitTourStmt` of the program of the build.

1. **The record words.** The build writes the caps `vCap`, `eCap` into the record, and `tCap`,
   `L_w` as P4's export of the branch gives them (the words `expPtr + 7` and `expPtr + 6`).
2. **The tour, with no marks.** It calls P2's procedure `tourBranchInitStmt`
   (`TourBranchInit.lean`) at the first cell after the record. That procedure reads the forest and
   the roots from P4's export and builds P2's tour on the input order. Through P7's view the tour
   then holds the core lists `outCoreOrder tr ord`, with no marks
   (`tourBranchInit_runs`). It leaves the handle of the tour in the first cell after the record,
   and the build copies it into the word `h + ASM_BR_TOUR`.

The marks of the edges of the output graph `S₀` come later, when the output graph is built: they
need the spanners of the bundle side.

The registers are those of the build: `3` holds `cOrdPtr`, `4` holds `expPtr`, `10` and `11` hold
the caps and `14` holds `h`. The piece leaves the end of the tour in register `15`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-- **The record words and the tour.** Registers: `3 = cOrdPtr`, `4 = expPtr`, `10 = vCap`,
`11 = eCap`, `14 = h`.
1. call the tour init `fTour` on `[vCap, eCap, cOrdPtr, expPtr, h + ASM_BR_SIZE]`, into
   register `15`;
2. copy the handle of the tour, which the call leaves at `h + ASM_BR_SIZE`, into the word
   `h + ASM_BR_TOUR`;
3. store `vCap`, `eCap` and the words `expPtr + 7` (`tCap`) and `expPtr + 6` (`L_w`) into the
   record. -/
def asmFirstInitTourStmt (fTour : ℕ) : Stmt :=
  .call 15 fTour [.reg 10, .reg 11, .reg 3, .reg 4, .bin .add (.reg 14) (.const ASM_BR_SIZE)] ;;
  .store (.bin .add (.reg 14) (.const ASM_BR_TOUR))
    (.load (.bin .add (.reg 14) (.const ASM_BR_SIZE))) ;;
  (.store (.bin .add (.reg 14) (.const ASM_BR_VCAP)) (.reg 10) ;;
   .store (.bin .add (.reg 14) (.const ASM_BR_ECAP)) (.reg 11) ;;
   .store (.bin .add (.reg 14) (.const ASM_BR_TCAP)) (.load (.bin .add (.reg 4) (.const 7))) ;;
   .store (.bin .add (.reg 14) (.const ASM_BR_LW)) (.load (.bin .add (.reg 4) (.const 6))))

/-- The piece never reads random bits. -/
theorem asmFirstInitTourStmt_noRand (fTour : ℕ) : (asmFirstInitTourStmt fTour).NoRand := by
  simp [asmFirstInitTourStmt, Stmt.NoRand]

/-- The memory after the four stores of the record words. -/
def asmFirstInitRecMem (mem : ℕ → ℕ) (h vCap eCap expPtr : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update mem
    (h + ASM_BR_VCAP) vCap) (h + ASM_BR_ECAP) eCap) (h + ASM_BR_TCAP) (mem (expPtr + 7)))
    (h + ASM_BR_LW) (mem (expPtr + 6))

/-- The stores of the record words change only the four words of the record. -/
theorem asmFirstInitRecMem_of_ne {mem : ℕ → ℕ} {h vCap eCap expPtr a : ℕ}
    (h5 : a ≠ h + ASM_BR_VCAP) (h6 : a ≠ h + ASM_BR_ECAP) (h7 : a ≠ h + ASM_BR_TCAP)
    (h8 : a ≠ h + ASM_BR_LW) : asmFirstInitRecMem mem h vCap eCap expPtr a = mem a := by
  simp [asmFirstInitRecMem, Function.update_of_ne h5, Function.update_of_ne h6,
    Function.update_of_ne h7, Function.update_of_ne h8]

/-- The four stores of the record words. -/
private theorem asmFirstInitRec_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {expPtr vCap eCap h : ℕ} (r4 : st.regs 4 = expPtr) (r10 : st.regs 10 = vCap)
    (r11 : st.regs 11 = eCap) (r14 : st.regs 14 = h) (hh : h + ASM_BR_SIZE < 2 ^ w)
    (he : expPtr + 8 ≤ h) :
    Runs w p ω
      (.store (.bin .add (.reg 14) (.const ASM_BR_VCAP)) (.reg 10) ;;
       .store (.bin .add (.reg 14) (.const ASM_BR_ECAP)) (.reg 11) ;;
       .store (.bin .add (.reg 14) (.const ASM_BR_TCAP)) (.load (.bin .add (.reg 4) (.const 7))) ;;
       .store (.bin .add (.reg 14) (.const ASM_BR_LW)) (.load (.bin .add (.reg 4) (.const 6))))
      st .normal { st with mem := asmFirstInitRecMem st.mem h vCap eCap expPtr } 29 := by
  have c5 : ASM_BR_VCAP < 2 ^ w := by simp only [ASM_BR_VCAP, ASM_BR_SIZE] at *; omega
  have c6 : ASM_BR_ECAP < 2 ^ w := by simp only [ASM_BR_ECAP, ASM_BR_SIZE] at *; omega
  have c7 : ASM_BR_TCAP < 2 ^ w := by simp only [ASM_BR_TCAP, ASM_BR_SIZE] at *; omega
  have c8 : ASM_BR_LW < 2 ^ w := by simp only [ASM_BR_LW, ASM_BR_SIZE] at *; omega
  have a5 : h + ASM_BR_VCAP < 2 ^ w := by simp only [ASM_BR_VCAP, ASM_BR_SIZE] at *; omega
  have a6 : h + ASM_BR_ECAP < 2 ^ w := by simp only [ASM_BR_ECAP, ASM_BR_SIZE] at *; omega
  have a7 : h + ASM_BR_TCAP < 2 ^ w := by simp only [ASM_BR_TCAP, ASM_BR_SIZE] at *; omega
  have a8 : h + ASM_BR_LW < 2 ^ w := by simp only [ASM_BR_LW, ASM_BR_SIZE] at *; omega
  have k7 : (7 : ℕ) < 2 ^ w := by omega
  have k6 : (6 : ℕ) < 2 ^ w := by omega
  have e7 : expPtr + 7 < 2 ^ w := by omega
  have e6 : expPtr + 6 < 2 ^ w := by omega
  set m1 := Function.update st.mem (h + ASM_BR_VCAP) vCap with hm1
  set m2 := Function.update m1 (h + ASM_BR_ECAP) eCap with hm2
  set m3 := Function.update m2 (h + ASM_BR_TCAP) (st.mem (expPtr + 7)) with hm3
  have q1 : Runs w p ω (.store (.bin .add (.reg 14) (.const ASM_BR_VCAP)) (.reg 10)) st .normal
      { st with mem := m1 } 5 :=
    runs_store_iff.mpr ⟨_, _, Expr.eval_add (Expr.eval_reg_of_eq r14) (Expr.eval_const c5) a5,
      Expr.eval_reg_of_eq r10, rfl, rfl, rfl⟩
  have q2 : Runs w p ω (.store (.bin .add (.reg 14) (.const ASM_BR_ECAP)) (.reg 11))
      { st with mem := m1 } .normal { st with mem := m2 } 5 :=
    runs_store_iff.mpr ⟨_, _, Expr.eval_add (Expr.eval_reg_of_eq r14) (Expr.eval_const c6) a6,
      Expr.eval_reg_of_eq r11, rfl, rfl, rfl⟩
  have q3 : Runs w p ω (.store (.bin .add (.reg 14) (.const ASM_BR_TCAP))
      (.load (.bin .add (.reg 4) (.const 7)))) { st with mem := m2 } .normal
      { st with mem := Function.update m2 (h + ASM_BR_TCAP) (m2 (expPtr + 7)) } 8 :=
    runs_store_iff.mpr ⟨_, _, Expr.eval_add (Expr.eval_reg_of_eq r14) (Expr.eval_const c7) a7,
      Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq r4) (Expr.eval_const k7) e7),
      rfl, rfl, rfl⟩
  set m3' := Function.update m2 (h + ASM_BR_TCAP) (m2 (expPtr + 7)) with hm3'
  have q4 : Runs w p ω (.store (.bin .add (.reg 14) (.const ASM_BR_LW))
      (.load (.bin .add (.reg 4) (.const 6)))) { st with mem := m3' } .normal
      { st with mem := Function.update m3' (h + ASM_BR_LW) (m3' (expPtr + 6)) } 8 :=
    runs_store_iff.mpr ⟨_, _, Expr.eval_add (Expr.eval_reg_of_eq r14) (Expr.eval_const c8) a8,
      Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq r4) (Expr.eval_const k6) e6),
      rfl, rfl, rfl⟩
  have t := tour_runs_seq_normal q1 (tour_runs_seq_normal q2 (tour_runs_seq_normal q3 q4))
  have hm7 : m2 (expPtr + 7) = st.mem (expPtr + 7) := by
    simp only [hm2, hm1, ASM_BR_VCAP, ASM_BR_ECAP]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hm6 : m3' (expPtr + 6) = st.mem (expPtr + 6) := by
    simp only [hm3', hm2, hm1, ASM_BR_VCAP, ASM_BR_ECAP, ASM_BR_TCAP]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  rw [hm6, hm3', hm7] at t
  exact t

/-- **The run of the record words and the tour.** Let `st` hold `cOrdPtr`, `expPtr`, `vCap`,
`eCap` and `h` in registers `3`, `4`, `10`, `11` and `14`, and let its memory hold the input
order at `cOrdPtr` and P4's export of the branch at `expPtr`, both below `h`, with fresh memory
from `h`. Then the piece runs, leaves the end `o` of the tour in register `15`, writes the handle
`tourH` of the tour and the four words `vCap`, `eCap`, `tCap`, `L_w` into the record, and builds
the tour with no marks in `[tourH, o)`, after the record. Memory below `h` does not change, and the
cost is that of `tourBranchInit_runs` plus `60`. -/
theorem asmFirstInitTourStmt_runs {depth w b L capExp M N vCap eCap cOrdPtr expPtr expEnd h
    cWords : ℕ} {p : Program} (hp : HasTourProcs p b) (ω : ℕ → Bool) {fTour : ℕ}
    (hfT : p.procs[fTour]? = some (tourBranchInitStmt (tourInit b)))
    {tr : BundleTreeState depth} {ord : ℕ → List End} {st : State}
    (r3 : st.regs 3 = cOrdPtr) (r4 : st.regs 4 = expPtr) (r10 : st.regs 10 = vCap)
    (r11 : st.regs 11 = eCap) (r14 : st.regs 14 = h)
    (hRot : HasRotOrder tr ord)
    (hVlt : ∀ v ∈ tr.cs.G.V, v < vCap) (hElt : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (hOrdAt : OrdListAt st.mem cOrdPtr ord cWords) (hOrdLe : cOrdPtr + cWords ≤ h)
    (hExp : CompBranchExportAt w st.mem expPtr expEnd L capExp M N vCap eCap tr.cs)
    (hExpLe : expEnd ≤ h) (hz : ZeroFrom st.mem h)
    (hsp : h + ASM_BR_SIZE + tourBranchInitSpace vCap eCap < 2 ^ w) :
    ∃ o st' c tourH xTour,
      Runs w p ω (asmFirstInitTourStmt fTour) st .normal st' c ∧
      st'.regs = Function.update st.regs 15 o ∧
      st'.mem (h + ASM_BR_TOUR) = tourH ∧
      st'.mem (h + ASM_BR_VCAP) = vCap ∧ st'.mem (h + ASM_BR_ECAP) = eCap ∧
      st'.mem (h + ASM_BR_TCAP) = st.mem (expPtr + 7) ∧
      st'.mem (h + ASM_BR_LW) = st.mem (expPtr + 6) ∧
      h + ASM_BR_SIZE < tourH ∧ tourH < o ∧
      (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap).rep tourH
        ⟨outCoreOrder tr ord, ∅⟩ xTour st'.mem ∧
      (∀ a, (tourAsmRep vCap eCap).foot tourH xTour a → tourH ≤ a ∧ a < o) ∧
      o + 2 ≤ h + ASM_BR_SIZE + tourBranchInitSpace vCap eCap ∧
      ZeroFrom st'.mem o ∧
      (∀ a < h, st'.mem a = st.mem a) ∧
      c + (tourAsmRep vCap eCap).phi tourH xTour st'.mem ≤
        tourBranchInitMul * (1 + cWords + tr.cs.G.m + tr.cs.G.n) * tourLog eCap + 60 := by
  have hE8 : expPtr + 8 ≤ h := le_trans hExp.1 hExpLe
  have hS : ASM_BR_SIZE = 16 := rfl
  have hT : ASM_BR_TOUR = 3 := rfl
  have hV : ASM_BR_VCAP = 5 := rfl
  have hEc : ASM_BR_ECAP = 6 := rfl
  have hTc : ASM_BR_TCAP = 7 := rfl
  have hL : ASM_BR_LW = 8 := rfl
  have hz' : ZeroFrom st.mem (h + ASM_BR_SIZE) := fun a ha => hz a (by omega)
  obtain ⟨o1, stT, cT, tourH, xT, hrun, hmh, hlt1, hlt2, hrep, -, hfoot, -, hhi, hzT, hpre,
      hcost⟩ :=
    tourBranchInit_runs (h := h + ASM_BR_SIZE) (pos := st.pos) hp ω hRot hVlt hElt hw hOrdAt
      (by omega) hExp (by omega) hz' hsp
  have hspw : (16 : ℕ) < 2 ^ w := by
    simp only [tourBranchInitSpace] at hsp; rw [hS] at hsp; omega
  have hhS : h + ASM_BR_SIZE < 2 ^ w := by
    simp only [tourBranchInitSpace] at hsp; omega
  -- the call of the tour init
  have hargs : evalArgs w st [.reg 10, .reg 11, .reg 3, .reg 4,
      .bin .add (.reg 14) (.const ASM_BR_SIZE)] =
      some [vCap, eCap, cOrdPtr, expPtr, h + ASM_BR_SIZE] := by
    simp [evalArgs, Expr.eval, r3, r4, r10, r11, r14, BinOp.eval, hS, show (16 : ℕ) < 2 ^ w from
      hspw, show h + 16 < 2 ^ w by rw [hS] at hhS; exact hhS]
  set s1 : State := { stT with regs := Function.update st.regs 15 o1.value } with hs1
  have hcall : Runs w p ω (.call 15 fTour [.reg 10, .reg 11, .reg 3, .reg 4,
      .bin .add (.reg 14) (.const ASM_BR_SIZE)]) st .normal s1
      (argsSize [.reg 10, .reg 11, .reg 3, .reg 4, .bin .add (.reg 14) (.const ASM_BR_SIZE)] +
        cT + 1) :=
    runs_call_iff.mpr ⟨_, _, o1, stT, cT, hargs, hfT, hrun, rfl, rfl, rfl⟩
  have s14 : s1.regs 14 = h := by simp [hs1, r14]
  have s4 : s1.regs 4 = expPtr := by simp [hs1, r4]
  have s10 : s1.regs 10 = vCap := by simp [hs1, r10]
  have s11 : s1.regs 11 = eCap := by simp [hs1, r11]
  -- the store of the handle of the tour
  have cT3 : ASM_BR_TOUR < 2 ^ w := by omega
  have cS : ASM_BR_SIZE < 2 ^ w := by omega
  set m2 := Function.update stT.mem (h + ASM_BR_TOUR) tourH with hm2
  have hst : Runs w p ω (.store (.bin .add (.reg 14) (.const ASM_BR_TOUR))
      (.load (.bin .add (.reg 14) (.const ASM_BR_SIZE)))) s1 .normal { s1 with mem := m2 } 8 :=
    runs_store_iff.mpr ⟨h + ASM_BR_TOUR, tourH,
      Expr.eval_add (Expr.eval_reg_of_eq s14) (Expr.eval_const cT3) (by omega),
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq s14) (Expr.eval_const cS) hhS)
        (by simpa [hs1] using hmh), rfl, rfl, rfl⟩
  -- the record words
  have hrec := asmFirstInitRec_runs (p := p) (ω := ω) (st := { s1 with mem := m2 }) s4 s10 s11
    s14 hhS hE8
  have hrunAll := tour_runs_seq_normal hcall (tour_runs_seq_normal hst hrec)
  set mF := asmFirstInitRecMem m2 h vCap eCap expPtr with hmF
  -- the final memory
  have hmF_out : ∀ a, a ≠ h + ASM_BR_TOUR → a ≠ h + ASM_BR_VCAP → a ≠ h + ASM_BR_ECAP →
      a ≠ h + ASM_BR_TCAP → a ≠ h + ASM_BR_LW → mF a = stT.mem a := by
    intro a h3 h5 h6 h7 h8
    rw [hmF, asmFirstInitRecMem_of_ne h5 h6 h7 h8, hm2, Function.update_of_ne h3]
  have hfar : ∀ a, h + ASM_BR_SIZE ≤ a → mF a = stT.mem a := fun a ha =>
    hmF_out a (by omega) (by omega) (by omega) (by omega) (by omega)
  have hbelow : ∀ a < h, mF a = st.mem a := fun a ha => by
    rw [hmF_out a (by omega) (by omega) (by omega) (by omega) (by omega), hpre a (by omega)]
  have hm2e : ∀ a < h, m2 a = st.mem a := fun a ha => by
    rw [hm2, Function.update_of_ne (by omega), hpre a (by omega)]
  have hkeep := asmBrTourView_keep (fun vCap eCap => tourAsmRep_local vCap eCap)
    ⟨tr, ord, vCap, eCap⟩ (s := ⟨outCoreOrder tr ord, ∅⟩) (mem := stT.mem) (mem' := mF)
    (fun c hc => (hfar c (by have := (hfoot c hc).1; omega)).symm)
  refine ⟨o1.value, _, _, tourH, xT, hrunAll, rfl, ?_, ?_, ?_, ?_, ?_, hlt1, hlt2,
    hkeep.1 hrep, hfoot, hhi, fun a ha => ?_, hbelow, ?_⟩
  · show mF (h + ASM_BR_TOUR) = tourH
    rw [hmF, asmFirstInitRecMem_of_ne (by omega) (by omega) (by omega) (by omega), hm2,
      Function.update_self]
  · show mF (h + ASM_BR_VCAP) = vCap
    simp only [hmF, asmFirstInitRecMem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  · show mF (h + ASM_BR_ECAP) = eCap
    simp only [hmF, asmFirstInitRecMem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · show mF (h + ASM_BR_TCAP) = st.mem (expPtr + 7)
    simp only [hmF, asmFirstInitRecMem]
    rw [Function.update_of_ne (by omega), Function.update_self, hm2e _ (by omega)]
  · show mF (h + ASM_BR_LW) = st.mem (expPtr + 6)
    simp only [hmF, asmFirstInitRecMem]
    rw [Function.update_self, hm2e _ (by omega)]
  · show mF a = 0
    rw [hfar a (by omega)]
    exact hzT a ha
  · rw [← hkeep.2]
    simp only [argsSize, Expr.size]
    omega

end MinCostFlow.SparseCore.Program
