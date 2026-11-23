module

public import MinCostFlow.SparseCore.Program.TourBranchInitMark
public import MinCostFlow.SparseCore.Program.AssemblyFirstExport
public import MinCostFlow.SparseCore.Program.AssemblyBranchTour

/-!
# The marks of the output graph at the init (`AssemblyFirstInitMark`)

At the init, the build makes P2's tour with no marks (`asmFirstInitTourStmt_runs`), and later the
memory form of the output graph `S₀ = tr₀.S_cur` (`asmFirstInitS0_runs`). P7 asks that the tour
marks the two ends of each edge of `S₀` (`OutMarksOf`). This file adds these marks.

P2's procedure `tourMarkExportStmt` marks the ends of the edges of a graph given as an export
(`tourMarkExport_runs`). So the piece `asmFirstInitMarkBody` first writes an export of the output
graph at the heap pointer, with `asmFirstExportDynGraphStmt`, and then calls
`tourMarkExportStmt` on that export. The export stays in memory after the call, but nothing reads
it again.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-- **The marks of the output graph**, `[tourH, g, h]`, where `tourH` is the handle of the tour,
`g` is the memory form of the output graph and `h` is the heap pointer.
1. export the graph at `g` to `h`, with `fExp` (`asmFirstExportDynGraphStmt`), into register `3`;
2. mark the ends of the edges of the export, with `fMark` (`tourMarkExportStmt`);
3. return the end of the export. -/
def asmFirstInitMarkBody (fExp fMark : ℕ) : Stmt :=
  .call 3 fExp [.reg 1, .reg 2] ;;
  .call 4 fMark [.reg 0, .reg 2, .reg 3] ;;
  .ret (.reg 3)

/-- The piece never reads random bits. -/
theorem asmFirstInitMarkBody_noRand (fExp fMark : ℕ) : (asmFirstInitMarkBody fExp fMark).NoRand := by
  simp [asmFirstInitMarkBody, Stmt.NoRand]

/-- **The run of the marks.** Let the tour at `tourH` hold the core lists `outCoreOrder tr ord`
with no marks, below `h`, and let `g` hold a memory form of a graph `S` whose edges are edges of
the core graph. Then the piece writes an export of `S` in `[h, o)` with `o = h + 4 + S.n + 3 S.m`,
and the tour then holds the same lists with the marks of the edges of `S`. The cells of the tour
do not grow, and memory below `h` changes only in the cells of the tour. The cost is that of the
export and of `tourMarkExport_runs`, plus `20`. -/
theorem asmFirstInitMark_runs {depth w b vCap eCap tourH g h pos : ℕ} {p : Program}
    (hp : HasTourProcs p b) (ω : ℕ → Bool) {fExp fMark : ℕ}
    (hfE : p.procs[fExp]? = some asmFirstExportDynGraphStmt)
    (hfM : p.procs[fMark]? = some (tourMarkExportStmt (tourOp b 7)))
    {tr : BundleTreeState depth} {ord : ℕ → List End} {S : MGraph}
    {xTour : (tourAsmRep vCap eCap).τ} {mem : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hRot : HasRotOrder tr ord)
    (hS_sub : S.E ⊆ (coreGraph tr.cs.G tr.cs.lsf).E)
    (hS : DynGraphAt mem g vCap eCap S) (hg : g + dynGraphSize vCap eCap ≤ h)
    (hrep : (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap).rep tourH
      ⟨outCoreOrder tr ord, ∅⟩ xTour mem)
    (hfoot : ∀ a, (tourAsmRep vCap eCap).foot tourH xTour a → a < h)
    (hz : ZeroFrom mem h) (hroom : h + 4 + S.n + 3 * S.m + 2 < 2 ^ w) :
    ∃ o st' c sTour' xTour',
      Runs w p ω (asmFirstInitMarkBody fExp fMark) (startState [tourH, g, h] mem pos) o st' c ∧
      o.value = h + 4 + S.n + 3 * S.m ∧
      (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap).rep tourH sTour' xTour' st'.mem ∧
      OutMarksOf sTour' (outCoreOrder tr ord) S.E ∧
      (∀ a, (tourAsmRep vCap eCap).foot tourH xTour' a →
        (tourAsmRep vCap eCap).foot tourH xTour a) ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ (tourAsmRep vCap eCap).foot tourH xTour a → st'.mem a = mem a) ∧
      c + (tourAsmRep vCap eCap).phi tourH xTour' st'.mem ≤
        200 * (S.n + S.m + 1) + tourMarkExportMul * (S.m + 1) * tourLog eCap +
          (tourAsmRep vCap eCap).phi tourH xTour mem + 20 := by
  obtain ⟨oE, stE, cE, hrunE, hoE, hexp, hzE, hkeepE, -, hcE⟩ :=
    asmFirstExportDynGraph_runs (p := p) (ω := ω) (pos := pos) hw16 hS hg hz (by omega)
  -- the tour does not see the export, which lies from `h` on
  have hagE : ∀ a, (tourAsmRep vCap eCap).foot tourH xTour a → mem a = stE.mem a :=
    fun a ha => (hkeepE a (hfoot a ha)).symm
  obtain ⟨hrepE, hphiE⟩ := asmBrTourView_keep (fun vCap eCap => tourAsmRep_local vCap eCap)
    ⟨tr, ord, vCap, eCap⟩ hagE
  obtain ⟨stM, cM, sTour', xTour', hrunM, hrepM, hmarks, hfootM, hzM, hkeepM, hcM⟩ :=
    tourMarkExport_runs (w := w) (pos := stE.pos) (sExpEnd := oE.value) hp ω hRot hS_sub hexp le_rfl
      (fun a ha _ hf => by have := hfoot a hf; omega) (hrepE hrep)
      (fun a hf => by have := hfoot a hf; omega) hzE (by omega)
  -- the three steps
  set st0 := startState [tourH, g, h] mem pos with hst0
  have hargsE : evalArgs w st0 [.reg 1, .reg 2] = some [g, h] := by
    simp [evalArgs, Expr.eval, hst0, startState]
  set s1 : State := { stE with regs := Function.update st0.regs 3 oE.value } with hs1
  have hcallE : Runs w p ω (.call 3 fExp [.reg 1, .reg 2]) st0 .normal s1
      (argsSize [.reg 1, .reg 2] + cE + 1) :=
    runs_call_iff.mpr ⟨_, _, oE, stE, cE, hargsE, hfE, hrunE, rfl, rfl, rfl⟩
  have hargsM : evalArgs w s1 [.reg 0, .reg 2, .reg 3] = some [tourH, h, oE.value] := by
    simp [evalArgs, Expr.eval, hs1, hst0, startState]
  set s2 : State := { stM with regs := Function.update s1.regs 4 oE.value } with hs2
  have hcallM : Runs w p ω (.call 4 fMark [.reg 0, .reg 2, .reg 3]) s1 .normal s2
      (argsSize [.reg 0, .reg 2, .reg 3] + cM + 1) :=
    runs_call_iff.mpr ⟨_, _, .returned oE.value, stM, cM, hargsM, hfM, hrunM, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 3)) s2 (.returned oE.value) s2 2 :=
    runs_ret_iff.mpr ⟨oE.value, by simp [Expr.eval, hs2, hs1], rfl, rfl, rfl⟩
  have t1 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcallM, hret, rfl⟩)
  have t2 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcallE, t1, rfl⟩)
  refine ⟨_, s2, _, sTour', xTour', t2, hoE, hrepM, hmarks, hfootM, hzM, fun a ha hf => ?_, ?_⟩
  · show stM.mem a = mem a
    rw [hkeepM a (by omega) hf, hkeepE a ha]
  · show _ + (tourAsmRep vCap eCap).phi tourH xTour' stM.mem ≤ _
    simp only [argsSize, Expr.size] at *
    rw [← hphiE] at hcM
    omega

end MinCostFlow.SparseCore.Program
