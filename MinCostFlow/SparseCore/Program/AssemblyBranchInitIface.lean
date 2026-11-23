module

public import MinCostFlow.SparseCore.Program.AssemblyBranchFull

/-!
# The init of a branch: the first phase and the program (`AssemblyBranchInitIface`)

The init of the sparse-core tool builds every branch `j < k` by `initBundleTreeWithParams`
(`AsmBranchAt.init_runs`, `AssemblyTopIface.lean`). As for the step (`AssemblyBranchStepIface`),
the program of the init (`asmBrInitStmt`) makes two calls:
1. **the first phase** (`AsmBrCoreInitAt`): it writes the record of the branch at the heap pointer
   `h` and builds every part but the readout data: the embedding table, the output graph `S₀`,
   the tour with the core lists of the input order and the marks of `S₀`, and the bundle side.
   It also writes exports of `G` and `S₀` (`ExportAt`) and leaves their addresses in two spare
   words of the record;
2. **the init of the readout data of P10** (`ReadBranchAt.init`). It reads `T`, `F`, the roots
   and the stretch tables from P4's export of branch `j` (`CompBranchExportAt`), and `G` and `S₀`
   from the two exports of the first phase.
Then the program stores the handle of the readout data in the record and returns.

The first phase runs the tour (P2), the bundles (P5), the bucket spanners (P6) and the embedding
table. It is stated here as an interface, whose post is what P10's init and the representation of
the branch need.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- Offset of the spare word of the record where the first phase of the init leaves the address
of the export of `G`. -/
def ASM_BR_GEXP : ℕ := 9
/-- Offset of the spare word of the record where the first phase of the init leaves the address
of the export of `S₀`. -/
def ASM_BR_SEXP : ℕ := 10

/-- The concrete state of a branch with new readout data: only the handle and the concrete state
of the readout data change. -/
def AsmBrConc.withRead {TR : ℕ → ℕ → DSRep AsmTourAbs} {τX : Type} (x : AsmBrConc TR τX)
    (readH : ℕ) (yRead : ReadConc) : AsmBrConc TR τX :=
  { x with readH := readH, yRead := yRead }

/-- The parts of a branch other than the readout data do not see the readout data. -/
theorem asmBrPart_withRead {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX} {b : ℕ}
    {x : AsmBrConc TR X.τ} {r : ℕ} {y : ReadConc} {i : ℕ} (hi : i ≠ 1) (a : ℕ) :
    asmBrPart X b (x.withRead r y) i a ↔ asmBrPart X b x i a := by
  match i, hi with
  | 0, _ => exact Iff.rfl
  | 2, _ => exact Iff.rfl
  | 3, _ => exact Iff.rfl
  | 4, _ => exact Iff.rfl
  | 5, _ => exact Iff.rfl
  | n + 6, _ => exact Iff.rfl

/-- **Interface of the first phase of the init of a branch**, `[cfH, j, graph, cOrdPtr, expPtr,
k, M, N, L, P, vCap, eCap, depth, lengths, h]` (the arguments of `AsmBranchAt.init_runs`, at
precision `P`), under the hypotheses of that clause, with `wordExp` for the word exponent of the
clause. The lengths `ℓ₀` of `G` are at `lengths`, as `CF.init_runs` reads them: the buckets of the
edges (`origBucket`) depend on them. Let `tr₀` be `initBundleTreeWithParams` of branch `j`. The call writes the record of a branch at `h` (all but
its first word, the handle of the readout data) and ends with:
* the caps `vCap`, `eCap` in the record, and `tCap`, `L_w` as P4's export gives them;
* the embedding table holding `tr₀.emb` on the edges of the core graph, the output graph holding
  `tr₀.S_cur`, P2's tour holding the input order and the forest of the LSF of `tr₀` (so that P7's
  view of it holds the core lists `outCoreOrder tr₀ ord`) with the marks of the edges of
  `tr₀.S_cur`, and the bundle side holding `⟨tr₀, ord, vCap, eCap⟩` with the caps of the branch;
* the record and these four parts in `[h, o)` and pairwise apart;
* exports of `G` and `tr₀.S_cur` (`ExportAt`, ending by `o`) at the addresses in the words
  `h + ASM_BR_GEXP` and `h + ASM_BR_SEXP`, which hold words;
* memory below `h` unchanged, at most `space` new cells, and cost at most `mul` times the machine
  cost of `tr₀`, with the potentials of the tour and the bundle side. -/
structure AsmBrCoreInitAt (TR : ℕ → ℕ → DSRep AsmTourAbs)
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
        ExportAt st'.mem (st'.mem (h + ASM_BR_GEXP)) o.value G ∧
        ExportAt st'.mem (st'.mem (h + ASM_BR_SEXP)) o.value tr₀.S_cur ∧
        st'.mem (h + ASM_BR_GEXP) < 2 ^ w ∧ st'.mem (h + ASM_BR_SEXP) < 2 ^ w ∧
        h + ASM_BR_SIZE ≤ o.value ∧
        o.value ≤ h + space.eval (M + N + k + vCap + eCap + L + depth) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, st'.mem a = mem a) ∧
        cost + (TR x.vCap x.eCap).phi x.tourH x.xTour st'.mem + X.phi x.restH x.xRest st'.mem ≤
          mul * tr₀.machCost

/-! ## The program -/

/-- **The init of a branch**, `[cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth,
lengths, h]` (the arguments of `AsmBranchAt.init_runs`). Registers: `15`, `16` the heap pointers
after the two calls.
1. call the first phase (`fCore`) on the arguments;
2. call the init of P10 (`fRead`) on the caps, `tCap` and `L_w` from P4's export at `expPtr`, the
   export of `G` from the record, the descriptors of `T` and `F`, the roots and the stretch tables
   from P4's export, the export of `S₀` from the record, and the heap pointer;
3. store the handle of the readout data (the heap pointer of the second call) in the first word of
   the record, and return the heap pointer. -/
def asmBrInitStmt (fCore fRead : ℕ) : Stmt :=
  .call 15 fCore [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13, .reg 14] ;;
  .call 16 fRead [.reg 10, .reg 11, .load (.bin .add (.reg 4) (.const 7)),
    .load (.bin .add (.reg 4) (.const 6)), .load (.bin .add (.reg 14) (.const ASM_BR_GEXP)),
    .load (.reg 4), .load (.bin .add (.reg 4) (.const 1)), .load (.bin .add (.reg 4) (.const 2)),
    .load (.bin .add (.reg 4) (.const 3)), .load (.bin .add (.reg 4) (.const 4)),
    .load (.bin .add (.reg 4) (.const 5)), .load (.bin .add (.reg 14) (.const ASM_BR_SEXP)),
    .reg 15] ;;
  .store (.bin .add (.reg 14) (.const ASM_BR_READ)) (.reg 15) ;;
  .ret (.reg 16)

/-- The init of a branch never reads random bits. -/
theorem asmBrInitStmt_noRand (fCore fRead : ℕ) : (asmBrInitStmt fCore fRead).NoRand := by
  simp [asmBrInitStmt, Stmt.NoRand]

/-- **The run of the init program.** If the first phase runs on the arguments and the init of
P10 then runs on the words that the program reads, then the program runs and returns the end of
the second call. Its memory is that of the second call with the end `h₁` of the first call stored
at `h + ASM_BR_READ`, and it costs at most the two calls and `120` steps. -/
theorem asmBrInitStmt_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {fCore fRead : ℕ}
    {cfH j graph cOrdPtr expPtr k M N L P vCap eCap depth lengths h pos : ℕ} {mem : ℕ → ℕ}
    {bodyC bodyR : Stmt} {oC oR : Outcome} {stC stR : State} {cC cR : ℕ}
    (hh : h + ASM_BR_SIZE < 2 ^ w) (he : expPtr + 8 < 2 ^ w)
    (hfC : p.procs[fCore]? = some bodyC) (hfR : p.procs[fRead]? = some bodyR)
    (hrunC : Runs w p ω bodyC
      (startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h]
        mem pos)
      oC stC cC)
    (hrunR : Runs w p ω bodyR
      (startState [vCap, eCap, stC.mem (expPtr + 7), stC.mem (expPtr + 6),
        stC.mem (h + ASM_BR_GEXP), stC.mem expPtr, stC.mem (expPtr + 1), stC.mem (expPtr + 2),
        stC.mem (expPtr + 3), stC.mem (expPtr + 4), stC.mem (expPtr + 5),
        stC.mem (h + ASM_BR_SEXP), oC.value] stC.mem stC.pos) oR stR cR) :
    ∃ st' c, Runs w p ω (asmBrInitStmt fCore fRead)
      (startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h]
        mem pos)
      (.returned oR.value) st' c ∧
      st'.mem = Function.update stR.mem (h + ASM_BR_READ) oC.value ∧ c ≤ cC + cR + 120 := by
  have hk : ∀ i, i ≤ 8 → i < 2 ^ w := fun i hi => by omega
  have hke : ∀ i, i ≤ 8 → expPtr + i < 2 ^ w := fun i hi => by omega
  set st0 := startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth,
    lengths, h] mem pos with hst0
  have hargsC : evalArgs w st0 [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
      .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14] =
      some [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, P, vCap, eCap, depth, lengths, h] := by
    simp [evalArgs, Expr.eval, hst0, startState]
  set s1 : State := { stC with regs := Function.update st0.regs 15 oC.value } with hs1
  have hcallC : Runs w p ω (.call 15 fCore [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5,
      .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14]) st0 .normal s1
      (argsSize [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
        .reg 10, .reg 11, .reg 12, .reg 13, .reg 14] + cC + 1) :=
    runs_call_iff.mpr ⟨_, bodyC, oC, stC, cC, hargsC, hfC, hrunC, rfl, rfl, rfl⟩
  have hargsR : evalArgs w s1 [.reg 10, .reg 11, .load (.bin .add (.reg 4) (.const 7)),
      .load (.bin .add (.reg 4) (.const 6)), .load (.bin .add (.reg 14) (.const ASM_BR_GEXP)),
      .load (.reg 4), .load (.bin .add (.reg 4) (.const 1)), .load (.bin .add (.reg 4) (.const 2)),
      .load (.bin .add (.reg 4) (.const 3)), .load (.bin .add (.reg 4) (.const 4)),
      .load (.bin .add (.reg 4) (.const 5)), .load (.bin .add (.reg 14) (.const ASM_BR_SEXP)),
      .reg 15] =
      some [vCap, eCap, stC.mem (expPtr + 7), stC.mem (expPtr + 6), stC.mem (h + ASM_BR_GEXP),
        stC.mem expPtr, stC.mem (expPtr + 1), stC.mem (expPtr + 2), stC.mem (expPtr + 3),
        stC.mem (expPtr + 4), stC.mem (expPtr + 5), stC.mem (h + ASM_BR_SEXP), oC.value] := by
    have a1 : h + ASM_BR_GEXP < 2 ^ w := by simp only [ASM_BR_GEXP, ASM_BR_SIZE] at *; omega
    have a2 : h + ASM_BR_SEXP < 2 ^ w := by simp only [ASM_BR_SEXP, ASM_BR_SIZE] at *; omega
    have a3 : ASM_BR_GEXP < 2 ^ w := by simp only [ASM_BR_GEXP, ASM_BR_SIZE] at *; omega
    have a4 : ASM_BR_SEXP < 2 ^ w := by simp only [ASM_BR_SEXP, ASM_BR_SIZE] at *; omega
    simp [evalArgs, Expr.eval, hs1, hst0, startState, BinOp.eval, a1, a2, a3, a4, hk 1 (by omega),
      hk 2 (by omega), hk 3 (by omega), hk 4 (by omega), hk 5 (by omega), hk 6 (by omega),
      hk 7 (by omega), hke 1 (by omega), hke 2 (by omega), hke 3 (by omega), hke 4 (by omega),
      hke 5 (by omega), hke 6 (by omega), hke 7 (by omega)]
  set s2 : State := { stR with regs := Function.update s1.regs 16 oR.value } with hs2
  have hcallR : Runs w p ω (.call 16 fRead [.reg 10, .reg 11,
      .load (.bin .add (.reg 4) (.const 7)), .load (.bin .add (.reg 4) (.const 6)),
      .load (.bin .add (.reg 14) (.const ASM_BR_GEXP)), .load (.reg 4),
      .load (.bin .add (.reg 4) (.const 1)), .load (.bin .add (.reg 4) (.const 2)),
      .load (.bin .add (.reg 4) (.const 3)), .load (.bin .add (.reg 4) (.const 4)),
      .load (.bin .add (.reg 4) (.const 5)), .load (.bin .add (.reg 14) (.const ASM_BR_SEXP)),
      .reg 15]) s1 .normal s2
      (argsSize [.reg 10, .reg 11, .load (.bin .add (.reg 4) (.const 7)),
        .load (.bin .add (.reg 4) (.const 6)), .load (.bin .add (.reg 14) (.const ASM_BR_GEXP)),
        .load (.reg 4), .load (.bin .add (.reg 4) (.const 1)),
        .load (.bin .add (.reg 4) (.const 2)), .load (.bin .add (.reg 4) (.const 3)),
        .load (.bin .add (.reg 4) (.const 4)), .load (.bin .add (.reg 4) (.const 5)),
        .load (.bin .add (.reg 14) (.const ASM_BR_SEXP)), .reg 15] + cR + 1) :=
    runs_call_iff.mpr ⟨_, bodyR, oR, stR, cR, hargsR, hfR, hrunR, rfl, rfl, rfl⟩
  have hreg14 : s2.regs 14 = h := by simp [hs2, hs1, hst0, startState]
  have hreg15 : s2.regs 15 = oC.value := by simp [hs2, hs1]
  have hreg16 : s2.regs 16 = oR.value := by simp [hs2]
  have hc0 : ASM_BR_READ < 2 ^ w := by simp only [ASM_BR_READ, ASM_BR_SIZE] at *; omega
  have hh0 : h + ASM_BR_READ < 2 ^ w := by simp only [ASM_BR_READ, ASM_BR_SIZE] at *; omega
  have q1 : Runs w p ω (.store (.bin .add (.reg 14) (.const ASM_BR_READ)) (.reg 15)) s2 .normal
      { s2 with mem := Function.update stR.mem (h + ASM_BR_READ) oC.value } 5 :=
    runs_store_iff.mpr ⟨h + ASM_BR_READ, oC.value,
      Expr.eval_add (Expr.eval_reg_of_eq hreg14) (Expr.eval_const hc0) hh0,
      Expr.eval_reg_of_eq hreg15, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 16))
      { s2 with mem := Function.update stR.mem (h + ASM_BR_READ) oC.value } (.returned oR.value)
      { s2 with mem := Function.update stR.mem (h + ASM_BR_READ) oC.value } 2 :=
    runs_ret_iff.mpr ⟨oR.value, by simp [Expr.eval, hreg16], rfl, rfl, rfl⟩
  have t1 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q1, hret, rfl⟩)
  have t2 := runs_seq_iff.mpr (Or.inr ⟨s2, _, _, hcallR, t1, rfl⟩)
  have t3 := runs_seq_iff.mpr (Or.inr ⟨s1, _, _, hcallC, t2, rfl⟩)
  refine ⟨_, _, t3, rfl, ?_⟩
  simp only [argsSize, Expr.size]
  omega

end MinCostFlow.SparseCore.Program
