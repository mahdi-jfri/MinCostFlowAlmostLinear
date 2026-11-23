module

public import MinCostFlow.SparseCore.Program.AssemblyBranchInitIface
public import MinCostFlow.SparseCore.Program.AssemblyFirstExport

/-!
# The first phase of the init of a branch: the build and the program (`AssemblyFirstInitBuild`)

The first phase of the init of a branch (`AsmBrCoreInitAt`, `AssemblyBranchInitIface.lean`) does
two things. It builds the branch: the record at `h`, the embedding table, the output graph `S₀`,
P2's tour and the bundle side. Then it writes exports of `G` and `S₀` for P10's init. The second
part needs no model: P10 reads the two graphs from their exports, and scfirst's procedure
`asmFirstExportDynGraphStmt` writes an export of any graph in the memory form `DynGraphAt`.

So the program `asmFirstInitStmt` makes three calls:
1. the build (`AsmFirstInitBuildAt`), on the arguments of the first phase;
2. the export of `G`, from its memory form at `graph`, at the end of the build;
3. the export of `S₀`, from the memory form of the output graph, after the first export.
Then it stores the starts of the two exports in the words `h + ASM_BR_GEXP` and `h + ASM_BR_SEXP`
of the record, and returns the end of the second export.

`AsmFirstInitBuildAt` asks of the build what `AsmBrCoreInitAt` asks of the first phase, except the
two exports. The proof that the program meets `AsmBrCoreInitAt` is in `AssemblyFirstInit.lean`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- **Interface of the build of a branch at its init**, `[cfH, j, graph, cOrdPtr, expPtr, k, M, N,
L, P, vCap, eCap, depth, lengths, h]`. It has the hypotheses of `AsmBrCoreInitAt.runs` and the
post of that clause without the two exports: the record of the branch at `h` (all but the words
of the readout data and of the two exports), the embedding table, the output graph `tr₀.S_cur`,
P2's tour with the core lists and the marks of `tr₀.S_cur`, and the bundle side, in `[h, o)` and
pairwise apart, with memory below `h` unchanged, at most `space` new cells, and cost at most `mul`
times the machine cost of `tr₀`, with the potentials of the tour and the bundle side. -/
structure AsmFirstInitBuildAt (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (CFR : DSRep CompFamilyAbs) (lsfInit : LSFInit) (impl : SparsifyImpl)
    (depth P L capExp limbMul wordExp w : ℕ) (Ψ : BundleTreeState depth → ℕ) (p : Program)
    (f : ℕ) where
  mul : ℕ
  space : PolyBound
  runs : ∀ (cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords : ℕ)
      (G : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (cfs : CompFamilyAbs) (xcf : CFR.τ)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      let X := asmBrSideRep B5 impl w depth L capExp limbMul Ψ
      let tr₀ := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
      0 < k → j < k → G.IsValid → G.V.Nonempty → G.m ≤ M → G.n ≤ N → G.n ≤ G.m + 1 →
      P ≤ 4 * L → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w →
      CFR.rep cfH cfs xcf mem → cfs j = initCompLSFWith lsfInit G ℓ₀ k j →
      BranchLengthsAt mem lengths eCap L P h G ℓ₀ →
      DynGraphAt mem graph vCap eCap G → graph + dynGraphSize vCap eCap ≤ h →
      OrdListAt mem cOrdPtr ord cWords → cOrdPtr + cWords ≤ h → cWords ≤ 1 + 6 * G.m →
      IsRotationOrder G ord →
      CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap (cfs j) → expEnd ≤ h →
      (∀ a, CFR.foot cfH xcf a → a < h) →
      (∀ a ∈ [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h],
        a < 2 ^ w) →
      ZeroFrom mem h →
      h + space.eval (M + N + k + vCap + eCap + L + depth) < 2 ^ w →
      AsmBrModelFacts impl vCap eCap tr₀ ord →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' cost,
        ∃ x : AsmBrConc TR X.τ,
        Runs w p ω body
          (startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h]
            mem pos)
          o st' cost ∧
        st'.mem (h + ASM_BR_EMB) = x.embH ∧ st'.mem (h + ASM_BR_OUT) = x.outH ∧
        st'.mem (h + ASM_BR_TOUR) = x.tourH ∧ st'.mem (h + ASM_BR_REST) = x.restH ∧
        st'.mem (h + ASM_BR_VCAP) = x.vCap ∧ st'.mem (h + ASM_BR_ECAP) = x.eCap ∧
        st'.mem (h + ASM_BR_TCAP) = x.tCap ∧ st'.mem (h + ASM_BR_LW) = x.L_w ∧
        x.vCap = vCap ∧ x.eCap = eCap ∧ x.tCap = mem (expPtr + 7) ∧ x.L_w = mem (expPtr + 6) ∧
        (embRep x.eCap).rep x.embH x.yEmb.view x.yEmb st'.mem ∧
        (coreGraph tr₀.cs.G tr₀.cs.lsf).E ⊆ x.yEmb.view.dom ∧
        (∀ e ∈ (coreGraph tr₀.cs.G tr₀.cs.lsf).E, x.yEmb.view.emb e = tr₀.emb e) ∧
        (outGraphRep x.vCap x.eCap).rep x.outH tr₀.S_cur x.gOut st'.mem ∧
        (asmBrTourView TR ⟨tr₀, ord, vCap, eCap⟩ x.vCap x.eCap).rep x.tourH x.sTour x.xTour
          st'.mem ∧
        OutMarksOf x.sTour (outCoreOrder tr₀ ord) tr₀.S_cur.E ∧
        X.rep x.restH ⟨tr₀, ord, vCap, eCap⟩ x.xRest st'.mem ∧
        x.xRest.vCap5 = vCap ∧ x.xRest.eCap5 = eCap ∧
        x.xRest.slotCap ≤ 2 * (vCap + eCap + 2) ^ 2 ∧
        (∀ i < 6, i ≠ 1 → ∀ a, asmBrPart X h x i a → h ≤ a ∧ a < o.value) ∧
        (∀ i < 6, ∀ i' < 6, i ≠ 1 → i' ≠ 1 → i ≠ i' → ∀ a, asmBrPart X h x i a →
          ¬ asmBrPart X h x i' a) ∧
        h + ASM_BR_SIZE ≤ o.value ∧
        o.value ≤ h + space.eval (M + N + k + vCap + eCap + L + depth) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, st'.mem a = mem a) ∧
        cost + (TR x.vCap x.eCap).phi x.tourH x.xTour st'.mem + X.phi x.restH x.xRest st'.mem ≤
          mul * tr₀.machCost

/-! ## The program -/

/-- **The first phase of the init of a branch**, `[cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P,
vCap, eCap, depth, lengths, h]`. Registers `15`, `16`, `17` hold the heap pointers after the three
calls.
1. call the build (`fBuild`) on the arguments;
2. call the export (`fExp`) on the graph `G` at `graph`, at the end of the build;
3. call the export on the output graph, whose memory form starts at the word that the handle of
   the output graph (in the word `h + ASM_BR_OUT`) points to, at the end of the first export;
4. store the starts of the two exports in the words `h + ASM_BR_GEXP` and `h + ASM_BR_SEXP`, and
   return the end of the second export. -/
def asmFirstInitStmt (fBuild fExp : ℕ) : Stmt :=
  .call 15 fBuild [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14] ;;
  .call 16 fExp [.reg 2, .reg 15] ;;
  .call 17 fExp [.load (.load (.bin .add (.reg 14) (.const ASM_BR_OUT))), .reg 16] ;;
  .store (.bin .add (.reg 14) (.const ASM_BR_GEXP)) (.reg 15) ;;
  .store (.bin .add (.reg 14) (.const ASM_BR_SEXP)) (.reg 16) ;;
  .ret (.reg 17)

/-- The first phase of the init never reads random bits. -/
theorem asmFirstInitStmt_noRand (fBuild fExp : ℕ) : (asmFirstInitStmt fBuild fExp).NoRand := by
  simp [asmFirstInitStmt, Stmt.NoRand]

/-- **The run of the first phase.** If the build runs on the arguments, the export runs on `graph`
at the end `o₁` of the build, and the export runs again on the address `g` at the end `o₂` of the
first export, where `g` is the word at the address in the word `h + ASM_BR_OUT` after the first
export, then the program runs and returns `o₃`, the end of the second export. Its memory is that
of the second export with `o₁` and `o₂` stored at `h + ASM_BR_GEXP` and `h + ASM_BR_SEXP`, and it
costs at most the three calls and `50` steps. -/
theorem asmFirstInitStmt_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {fBuild fExp : ℕ}
    {cfH j graph cOrdPtr expPtr k M N L P vCap eCap depth lengths h pos : ℕ} {mem : ℕ → ℕ}
    {bodyB bodyE : Stmt} {oB oE oF : Outcome} {stB stE stF : State} {cB cE cF : ℕ}
    (hh : h + ASM_BR_SIZE < 2 ^ w)
    (hfB : p.procs[fBuild]? = some bodyB) (hfE : p.procs[fExp]? = some bodyE)
    (hrunB : Runs w p ω bodyB
      (startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h]
        mem pos)
      oB stB cB)
    (hrunE : Runs w p ω bodyE (startState [graph, oB.value] stB.mem stB.pos) oE stE cE)
    (hrunF : Runs w p ω bodyE
      (startState [stE.mem (stE.mem (h + ASM_BR_OUT)), oE.value] stE.mem stE.pos) oF stF cF) :
    ∃ st' c, Runs w p ω (asmFirstInitStmt fBuild fExp)
      (startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h]
        mem pos)
      (.returned oF.value) st' c ∧
      st'.mem = Function.update (Function.update stF.mem (h + ASM_BR_GEXP) oB.value)
        (h + ASM_BR_SEXP) oE.value ∧
      c ≤ cB + cE + cF + 50 := by
  set st0 := startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth,
    lengths, h] mem pos with hst0
  have hargsB : evalArgs w st0 [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
      .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14] =
      some [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h] := by
    simp [evalArgs, Expr.eval, hst0, startState]
  set s1 : State := { stB with regs := Function.update st0.regs 15 oB.value } with hs1
  have hcallB : Runs w p ω (.call 15 fBuild [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5,
      .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14]) st0 .normal s1
      (argsSize [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
        .reg 10, .reg 11, .reg 12, .reg 13, .reg 14] + cB + 1) :=
    runs_call_iff.mpr ⟨_, bodyB, oB, stB, cB, hargsB, hfB, hrunB, rfl, rfl, rfl⟩
  have hargsE : evalArgs w s1 [.reg 2, .reg 15] = some [graph, oB.value] := by
    simp [evalArgs, Expr.eval, hs1, hst0, startState]
  set s2 : State := { stE with regs := Function.update s1.regs 16 oE.value } with hs2
  have hcallE : Runs w p ω (.call 16 fExp [.reg 2, .reg 15]) s1 .normal s2
      (argsSize [.reg 2, .reg 15] + cE + 1) :=
    runs_call_iff.mpr ⟨_, bodyE, oE, stE, cE, hargsE, hfE, hrunE, rfl, rfl, rfl⟩
  have hreg14 : s2.regs 14 = h := by simp [hs2, hs1, hst0, startState]
  have hout : ASM_BR_OUT < 2 ^ w := by simp only [ASM_BR_OUT, ASM_BR_SIZE] at *; omega
  have hhout : h + ASM_BR_OUT < 2 ^ w := by simp only [ASM_BR_OUT, ASM_BR_SIZE] at *; omega
  have hargsF : evalArgs w s2 [.load (.load (.bin .add (.reg 14) (.const ASM_BR_OUT))), .reg 16] =
      some [stE.mem (stE.mem (h + ASM_BR_OUT)), oE.value] := by
    have e1 : (Expr.bin .add (.reg 14) (.const ASM_BR_OUT)).eval w s2 = some (h + ASM_BR_OUT) :=
      Expr.eval_add (Expr.eval_reg_of_eq hreg14) (Expr.eval_const hout) hhout
    have e2 := Expr.eval_load (Expr.eval_load e1)
    simp only [evalArgs, e2]
    simp [Expr.eval, hs2]
  set s3 : State := { stF with regs := Function.update s2.regs 17 oF.value } with hs3
  have hcallF : Runs w p ω (.call 17 fExp [.load (.load (.bin .add (.reg 14) (.const ASM_BR_OUT))),
      .reg 16]) s2 .normal s3
      (argsSize [.load (.load (.bin .add (.reg 14) (.const ASM_BR_OUT))), .reg 16] + cF + 1) :=
    runs_call_iff.mpr ⟨_, bodyE, oF, stF, cF, hargsF, hfE, hrunF, rfl, rfl, rfl⟩
  have r14 : s3.regs 14 = h := by simp [hs3, hreg14]
  have r15 : s3.regs 15 = oB.value := by simp [hs3, hs2, hs1]
  have r16 : s3.regs 16 = oE.value := by simp [hs3, hs2]
  have r17 : s3.regs 17 = oF.value := by simp [hs3]
  have cG : ASM_BR_GEXP < 2 ^ w := by simp only [ASM_BR_GEXP, ASM_BR_SIZE] at *; omega
  have cS : ASM_BR_SEXP < 2 ^ w := by simp only [ASM_BR_SEXP, ASM_BR_SIZE] at *; omega
  have hG : h + ASM_BR_GEXP < 2 ^ w := by simp only [ASM_BR_GEXP, ASM_BR_SIZE] at *; omega
  have hS : h + ASM_BR_SEXP < 2 ^ w := by simp only [ASM_BR_SEXP, ASM_BR_SIZE] at *; omega
  set s4 : State := { s3 with mem := Function.update stF.mem (h + ASM_BR_GEXP) oB.value }
    with hs4
  have q1 : Runs w p ω (.store (.bin .add (.reg 14) (.const ASM_BR_GEXP)) (.reg 15)) s3 .normal
      s4 5 :=
    runs_store_iff.mpr ⟨h + ASM_BR_GEXP, oB.value,
      Expr.eval_add (Expr.eval_reg_of_eq r14) (Expr.eval_const cG) hG,
      Expr.eval_reg_of_eq r15, rfl, rfl, rfl⟩
  have r14' : s4.regs 14 = h := r14
  have r16' : s4.regs 16 = oE.value := r16
  have r17' : s4.regs 17 = oF.value := r17
  set s5 : State := { s4 with mem := Function.update s4.mem (h + ASM_BR_SEXP) oE.value }
    with hs5
  have q2 : Runs w p ω (.store (.bin .add (.reg 14) (.const ASM_BR_SEXP)) (.reg 16)) s4 .normal
      s5 5 :=
    runs_store_iff.mpr ⟨h + ASM_BR_SEXP, oE.value,
      Expr.eval_add (Expr.eval_reg_of_eq r14') (Expr.eval_const cS) hS,
      Expr.eval_reg_of_eq r16', rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 17)) s5 (.returned oF.value) s5 2 :=
    runs_ret_iff.mpr ⟨oF.value, by simp [Expr.eval, hs5, r17'], rfl, rfl, rfl⟩
  have t1 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q2, hret, rfl⟩)
  have t2 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q1, t1, rfl⟩)
  have t3 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcallF, t2, rfl⟩)
  have t4 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcallE, t3, rfl⟩)
  have t5 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcallB, t4, rfl⟩)
  refine ⟨_, _, t5, rfl, ?_⟩
  simp only [argsSize, Expr.size]
  omega

end MinCostFlow.SparseCore.Program
