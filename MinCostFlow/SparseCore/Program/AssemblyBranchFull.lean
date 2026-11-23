module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRestart
public import MinCostFlow.SparseCore.Program.AssemblyBranchOrd
public import MinCostFlow.SparseCore.Program.AssemblyBranchRead

/-!
# The full representation of a branch (`AssemblyBranchFull`)

The representation `asmBrRep TR X` of a branch takes any part `X` for the bundle side, and the
restart (`asmBr_restart_runs`) takes as a hypothesis that the bundle table and the branch share
the caps (`x.xRest.vCap5 = x.vCap`, `x.xRest.eCap5 = x.eCap`). Here we fix `X` to the bundle side
`asmBrSideRep B5 impl w depth L capExp limbMul Ψ` and add the shared caps to the representation
(`asmBrFullRep`), with bounds on the caps `tCap` and `slotCap` of the tree edges and of the bundle
table. This is the representation that the branch gives to `AsmBranchAt`.

Every operation keeps these facts. The readouts keep the caps of the branch and the whole bundle
side (the posts `x'.eCap = x.eCap ∧ x'.xRest = x.xRest` of the readouts), and the restart ends
with `x'.xRest.vCap5 = x'.vCap`, `x'.xRest.eCap5 = x'.eCap` and the same `slotCap`.

The main results restate the readouts and the restart for `asmBrFullRep`, in the form of the
clauses of `AsmBranchAt`:
* `asmBrFull_readLSF_runs`, `asmBrFull_readS_runs`, `asmBrFull_readEmb_runs` and
  `asmBrFull_readOrd_runs`: the clauses of readouts `2` to `5`, with the readout cost
  `asmBrReadoutCost` and the multiplier `asmBrOrdMul mulT capExp` in place of the costs of the spec;
* `asmBrFull_restart_runs`: the restart, for a branch whose bundle cap `tr.k` is the cap of
  P5's restart, with P4's root query taken from `AsmCompFamilyAt`
  (`CF.toRootQueryAt k`), the roots of P4 read from `cfs j = tr.cs`, the embedding refresh
  `embRefreshStmt`, and the bound `(vCap + eCap + 2) ^ 2 < 2 ^ w` derived from the
  word size of the clause when `2 * capExp ≤ wordExp`. The cost has the form of the clause, with
  the factor `asmBrRestartMul`. The heap space `sp` stays as in `asmBr_restart_runs`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- **The full representation of a branch**: the branch with the bundle side
`asmBrSideRep B5 impl w depth L capExp limbMul Ψ` for the walk potential `Ψ`, whose bundle table
has the caps of the branch.
The caps of the branch are the caps `a.vCap`, `a.eCap` of the abstract state. The cap on the names
of the tree edges is at most `2 (vCap + eCap + 2) ^ 2`, and the stretch tables have at least one
limb; P10 needs both (`readBranchAt_readRep`). The number of slots of the bundle table is at most
`2 (vCap + eCap + 2) ^ 2` too, so that the space of P5's restart, which has the factor
`slotCap + 1`, is a polynomial in the caps. The walk length bound of the spanners of the model
is at most the walk length bound of the sparsifier at `m₀`, as at the init of the model
(`initBundleTreeWithParams` sets `spanParams` to the parameters at `m₀`, and no operation changes
them). With the bound `SparsifyParamsLe` of the bundle side, it bounds the walk length bound
`γ_ℓ mMax` of the spanners of the program, which the space of a restart has as a factor. The
potential and the cells are those of `asmBrRep`. -/
noncomputable def asmBrFullRep {depth : ℕ} (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (impl : SparsifyImpl) (w P L capExp limbMul : ℕ) (Ψ : BundleTreeState depth → ℕ) :
    DSRep (AsmBranchAbs depth) where
  τ := AsmBrConc TR (asmBrSideRep B5 impl w depth L capExp limbMul Ψ).τ
  rep b a x mem :=
    AsmBrRepAt TR (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) P L capExp b a x mem ∧
      x.xRest.vCap5 = x.vCap ∧ x.xRest.eCap5 = x.eCap ∧ x.vCap = a.vCap ∧ x.eCap = a.eCap ∧
      x.tCap ≤ 2 * (x.vCap + x.eCap + 2) ^ 2 ∧ x.xRest.slotCap ≤ 2 * (x.vCap + x.eCap + 2) ^ 2 ∧
      1 ≤ x.L_w ∧ a.tr.spanParams.γ_ℓ ≤ impl.γ_ℓ a.tr.m₀
  phi _ x mem := asmBrPhi (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) x mem
  foot b x a := asmBrFoot (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) b x a

section Full

variable {depth w : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
  {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
  {impl : SparsifyImpl} {P L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ}

/-- The full representation is local, since `asmBrRep` is local and the shared edge cap does not
read memory. -/
theorem asmBrFullRep_local (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local) :
    (asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ).Local := by
  intro b a x mem mem' hag
  have h := asmBrRep_local hTR (asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ) P L capExp
    b a x mem mem' hag
  exact ⟨fun hr => ⟨h.1 hr.1, hr.2⟩, h.2⟩

end Full

/-! ## The readouts -/

section Readouts

variable {depth w : ℕ} {fmt : Num.Format w} {TR : ℕ → ℕ → DSRep AsmTourAbs}
  {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
  {impl : SparsifyImpl} {L capExp limbMul : ℕ} {Ψ : BundleTreeState depth → ℕ}

/-- **Readout `2` for the full representation**, in the form of the clause `readLSF_runs` of
`AsmBranchAt`, from `asmBr_readLSF_runs`. -/
theorem asmBrFull_readLSF_runs (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    {p : Program} {f fRL : ℕ} (hp : p.procs[f]? = some (asmBrReadStmt fRL ASM_BR_READ))
    (hRL : p.procs[fRL]? = some readLSFStmt) :
    let R := asmBrFullRep (depth := depth) TR B5 impl w fmt.precision L capExp limbMul Ψ
    ∀ (brH h M N vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → tr.m₀ = M → tr.n₀ = N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      R.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, R.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 5 < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        R.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ forestVCap forestECap,
          st'.mem (h + 4) ≤
            L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
          LSFAt st'.mem h forestVCap forestECap fmt.limbBits (st'.mem (h + 4)) fmt.precision
            tr.cs.G.E tr.cs.lsf) ∧
        R.Respects (R.foot brH x) h 5 mem o.value brH x' st'.mem ∧
        c + R.phi brH x' st'.mem ≤ asmBrReadoutCost + R.phi brH x mem := by
  intro R brH h M N vCap eCap tr ord x mem pos ω hfmt hM hN _ hrep hfoot hb hh hz hroom
  obtain ⟨body, hbody, o, st', c, x', hrun, hV, hE, hT, hLw', hX, hrep', hout, hresp, hcost⟩ :=
    asmBr_readLSF_runs (fmt := fmt) hTR (asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ)
      hp hRL brH h M N vCap eCap tr ord x mem pos ω hfmt hM hN hrep.1 hfoot hb hh hz hroom
  exact ⟨body, hbody, o, st', c, x', hrun, ⟨hrep', by rw [hX, hE, hV, hT, hLw']; exact hrep.2⟩,
    hout, hresp, hcost⟩

/-- **Readout `3` for the full representation**, in the form of the clause `readS_runs` of
`AsmBranchAt`, from `asmBr_readS_runs`. -/
theorem asmBrFull_readS_runs (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    {p : Program} {f fRS : ℕ} (hp : p.procs[f]? = some (asmBrReadStmt fRS ASM_BR_READ))
    (hRS : p.procs[fRS]? = some readSStmt) :
    let R := asmBrFullRep (depth := depth) TR B5 impl w fmt.precision L capExp limbMul Ψ
    ∀ (brH h vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      R.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, R.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 1 < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        R.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ graphVCap graphECap, DynGraphAt st'.mem (st'.mem h) graphVCap graphECap tr.S_cur) ∧
        R.Respects (R.foot brH x) h 1 mem o.value brH x' st'.mem ∧
        c + R.phi brH x' st'.mem ≤ asmBrReadoutCost + R.phi brH x mem := by
  intro R brH h vCap eCap tr ord x mem pos ω hrep hfoot hb hh hz hroom
  obtain ⟨body, hbody, o, st', c, x', hrun, hV, hE, hT, hLw', hX, hrep', hout, hresp, hcost⟩ :=
    asmBr_readS_runs (fmt := fmt) hTR (asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ)
      hp hRS brH h vCap eCap tr ord x mem pos ω hrep.1 hfoot hb hh hz hroom
  exact ⟨body, hbody, o, st', c, x', hrun, ⟨hrep', by rw [hX, hE, hV, hT, hLw']; exact hrep.2⟩,
    hout, hresp, hcost⟩

/-- **Readout `4` for the full representation**, in the form of the clause `readEmb_runs` of
`AsmBranchAt`, from `asmBr_readEmb_runs`. -/
theorem asmBrFull_readEmb_runs (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    {p : Program} {f fRE : ℕ} (hp : p.procs[f]? = some (asmBrReadStmt fRE ASM_BR_EMB))
    (hRE : p.procs[fRE]? = some embReadStmt) :
    let R := asmBrFullRep (depth := depth) TR B5 impl w fmt.precision L capExp limbMul Ψ
    ∀ (brH h vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      R.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, R.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 2 < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        R.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        EmbeddingReadoutAt st'.mem h (st'.mem (h + 1)) tr.cs.G tr.cs.lsf tr.emb ∧
        R.Respects (R.foot brH x) h 2 mem o.value brH x' st'.mem ∧
        c + R.phi brH x' st'.mem ≤ asmBrReadoutCost + R.phi brH x mem := by
  intro R brH h vCap eCap tr ord x mem pos ω hrep hfoot hb hh hz hroom
  obtain ⟨body, hbody, o, st', c, x', hrun, hV, hE, hT, hLw', hX, hrep', hout, hresp, hcost⟩ :=
    asmBr_readEmb_runs (fmt := fmt) hTR (asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ)
      hp hRE brH h vCap eCap tr ord x mem pos ω hrep.1 hfoot hb hh hz hroom
  exact ⟨body, hbody, o, st', c, x', hrun, ⟨hrep', by rw [hX, hE, hV, hT, hLw']; exact hrep.2⟩,
    hout, hresp, hcost⟩

/-- **Readout `5` for the full representation**, in the form of the clause `readOrd_runs` of
`AsmBranchAt`, from `asmBr_readOrd_runs`. -/
theorem asmBrFull_readOrd_runs {P : ℕ} (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    {p : Program} {f fList mulT : ℕ} (hp : p.procs[f]? = some (asmBrReadOrdStmt fList))
    (hL : AsmBrTourListProj TR w p fList mulT) :
    let R := asmBrFullRep (depth := depth) TR B5 impl w P L capExp limbMul Ψ
    ∀ (brH h M N vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      tr.m₀ = M → tr.n₀ = N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      R.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, R.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h →
      h + (1 + ordWordsOn tr.S_cur.V (tr.outOrder ord)) < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        R.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ words, OrdListAt st'.mem (st'.mem h) (tr.outOrder ord) words ∧
          words ≤ ordWordsOn tr.S_cur.V (tr.outOrder ord)) ∧
        R.Respects (R.foot brH x) h (1 + ordWordsOn tr.S_cur.V (tr.outOrder ord))
          mem o.value brH x' st'.mem ∧
        c + R.phi brH x' st'.mem ≤
          asmBrOrdMul mulT capExp * (ordWordsOn tr.S_cur.V (tr.outOrder ord) + 1) *
            bundleLogFactor M N + R.phi brH x mem := by
  intro R brH h M N vCap eCap tr ord x mem pos ω hM hN hcap hrep hfoot hb hh hz hroom
  obtain ⟨body, hbody, o, st', c, x', hrun, hV, hE, hT, hLw', hX, hrep', hout, hresp, hcost⟩ :=
    asmBr_readOrd_runs (P := P) (L := L) (capExp := capExp) hTR
      (asmBrSideRep_local hB5 impl w depth L capExp limbMul Ψ) hp hL brH h M N vCap eCap tr ord x
      mem pos ω hM hN hcap hrep.1 hfoot hb hh hz hroom
  exact ⟨body, hbody, o, st', c, x', hrun, ⟨hrep', by rw [hX, hE, hV, hT, hLw']; exact hrep.2⟩,
    hout, hresp, hcost⟩

end Readouts

/-! ## The restart -/

/-- The cost factor of the restart of a branch in the form of the clause `restart_runs` of
`AsmBranchAt`: the factor `asmBrRestartConst` of the first two calls, `1200` for the refresh
(`asmBrEmbBound_le_machCost`), and `100` for the steps of the dispatch. -/
def asmBrRestartMul (bunMul readMul rootCost tourMul capExp : ℕ) : ℕ :=
  asmBrRestartConst bunMul readMul rootCost tourMul capExp + 1300

/-- **The walk potential after a restart is at most the restart cost** of the model, for a state
with the invariants that the bundle side keeps (`RestartScurModelInv`, `BunDisjointInv`, the
sparsifier parameter and constant comparisons from `AsmBrSideModel`, and validity and edge-count
bound of each restarted bucket graph). The model lemma is for the definition of `Ψ` in the model
(`walkPot_restartOK`); here `Ψ` is a parameter, and this is asked of it. -/
def AsmWalkPotRestartOK (impl : SparsifyImpl) (depth : ℕ) (Ψ : BundleTreeState depth → ℕ) :
    Prop :=
  ∀ (tr : BundleTreeState depth) (ord : ℕ → List End) (mMax : ℕ),
    RestartScurModelInv tr →
    BunDisjointInv tr →
    SparsifyParamsLe (canonicalSparsifyParams impl mMax).absorbTime tr.spanParams →
    dsAmortConst impl ≤ tr.spanConst →
    (∀ C ∈ tr.activeComps, ∀ b ∈ tr.activeBuckets C,
      let Hb := SparseCore.normGraph (restartBucketBundle tr ord C b).graph
      Hb.IsValid ∧ Hb.m ≤ mMax) →
    Ψ (restartBundleTree depth (fun _ => canonicalSparsify impl) tr ord) ≤
      singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord

/-- **The restart for the full representation**, in the form of the clause `restart_runs` of
`AsmBranchAt` up to the heap space. P4's root query is `CF.toRootQueryAt k`, and its roots for
branch `j` are those of `tr.cs.lsf` since `cfs j = tr.cs`. The refresh is `embRefreshStmt`
(`embRefresh_asmBrEmbRefreshDisjAt_of_bucketSpanner`), and its cost is paid by the model's
charge (`asmBrEmbBound_le_machCost`). The bound `(vCap + eCap + 2) ^ 2 < 2 ^ w` of
`asmBr_restart_runs` and P10's word condition follow from the cap bound of the representation and
the word size of the clause, since `asmP10WordExp capExp ≤ wordExp` (`p10Word_of_wordExp`). P10 is
asked only at caps that meet its word condition, as `readBranchAt_readRep` gives it; the spanner
caps lie below the caps of the branch by the bundle side. The heap space `sp` stays as in
`asmBr_restart_runs`. P5's restart `J` cuts the bundles with the cap `kB` of its table, which is
`tr.k` by the bundle side. The walk potential `Ψ` after the restart is paid by `AsmWalkPotRestartOK`. -/
theorem asmBrFull_restart_runs {w depth L capExp limbMul wordExp : ℕ} {fmt : Num.Format w}
    {impl : SparsifyImpl} {Ψ : BundleTreeState depth → ℕ} (hΨ : AsmWalkPotRestartOK impl depth Ψ)
    {OS : OutTourSpec} {nm sm fm lm : ℕ} {p : Program}
    {TR : ℕ → ℕ → DSRep AsmTourAbs} (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hOP : AsmBrOutProj OS TR w p nm sm fm lm)
    (hTh : ∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH)
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {fBun : ℕ}
    (J : AsmBrBunAt TR B5 w p fBun)
    {CFS : AsmCompFamilySpec} {lsfInit : LSFInit} {fCFInit fCFBatch : ℕ}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    {bRead readMul : ℕ} {readIdx : ℕ → ℕ} {f f8 bOut bSpan fEmb bCopy : ℕ}
    (hf : p.procs[f]? = some (asmBrRestartStmt f8 (outIdxReset bOut) fEmb))
    (hpS : p.HasAt bSpan (bucketSpannerProcs impl bSpan))
    (hpOut : OutProcsAt p bOut nm sm fm lm)
    (hp8 : p.procs[f8]? = some (restartBranchStmt fBun (bSpan + bsIdxOp0 + 0) (bRead + readIdx 3)))
    (hfE : p.procs[fEmb]? = some (embRefreshStmt bCopy (bSpan + bsOffRead + spanReadIdxPiWalkPtr)))
    (hcopy : p.HasAt bCopy [copyWords])
    (hB : ∀ k vCap eCap tCap L_w (P' : DSParams) cap,
      P'.w = w → P'.eCap ≤ eCap → eCap ≤ tCap → 1 ≤ L_w →
      (vCap + tCap + 2) ^ 2 * (L_w + 1) < 2 ^ w →
      ReadBranchAt (readRep vCap eCap tCap L_w fmt.precision) w vCap eCap tCap L_w fmt.precision
        P' cap p bRead readIdx CF.fRoot (CF.toRootQueryAtCaps k vCap eCap) readMul)
    (hWE : asmP10WordExp capExp ≤ wordExp) :
    let R := asmBrFullRep (depth := depth) TR B5 impl w fmt.precision L capExp limbMul Ψ
    ∀ (brH cfH j k M N vCap eCap h sp : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : R.τ) (cfs : CompFamilyAbs) (xcf : CF.rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      j < k → tr.m₀ = M → tr.n₀ = N →
      16 ≤ 2 ^ w → (M + N + 2) ^ wordExp * (L + 1) < 2 ^ w →
      R.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      CF.rep.rep cfH cfs xcf mem → CF.vCapOf xcf = vCap → CF.eCapOf xcf = eCap → cfs j = tr.cs → k = (cfs 0).k →
      (∀ a, R.foot brH x a → a < h) → (∀ a, CF.rep.foot cfH xcf a → a < h) →
      (∀ a, R.foot brH x a → ¬ CF.rep.foot cfH xcf a) →
      (∀ a ∈ [brH, cfH, j, h], a < 2 ^ w) →
      ZeroFrom mem h →
      asmBrRestartSpace (J.space x.xRest.slotCap) readMul embRefreshMul OS
        (asmBrSP impl w depth x.xRest)
        x.xRest.bunS x.xRest.spanS tr.cs ord tr.k x.xRest.slots x.vCap x.eCap x.tCap x.L_w ≤ sp →
      h + sp < 2 ^ w →
      let tr' := restartBundleTree depth (fun _ => canonicalSparsify impl) tr ord
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x' xcf',
        Runs w p ω body (startState [brH, cfH, j, h] mem pos) o st' c ∧
        R.rep brH ⟨tr', ord, vCap, eCap⟩ x' st'.mem ∧
        CF.rep.rep cfH cfs xcf' st'.mem ∧ CF.vCapOf xcf' = vCap ∧ CF.eCapOf xcf' = eCap ∧
        h ≤ o.value ∧ o.value ≤ h + sp ∧ ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ R.foot brH x a → ¬ CF.rep.foot cfH xcf a → st'.mem a = mem a) ∧
        (∀ a, R.foot brH x' a → R.foot brH x a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, CF.rep.foot cfH xcf' a → CF.rep.foot cfH xcf a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, R.foot brH x' a → ¬ CF.rep.foot cfH xcf' a) ∧
        c + R.phi brH x' st'.mem + CF.rep.phi cfH xcf' st'.mem ≤
          asmBrRestartMul J.mul readMul (CFS.rootCost capExp) OS.mul capExp *
              (singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord + 1) +
            R.phi brH x mem + CF.rep.phi cfH xcf mem := by
  intro R brH cfH j k M N vCap eCap h sp tr ord x cfs xcf mem pos ω hj hM hN h16 hword hrep
    hrep4 hv4 he4 hcfs hk0 hfoot hf4 hd4 hargs hz hsp hspW tr'
  have hroots : ∀ u ∈ tr.cs.G.V, (CF.toRootQueryAtCaps k vCap eCap).ok cfs j u ∧
      (CF.toRootQueryAtCaps k vCap eCap).root cfs j u = tr.cs.lsf.F.root u := fun u hu =>
    ⟨⟨h16, hj, hk0, hcfs ▸ hu⟩, by show (cfs j).RF.root u = _; rw [hcfs]; rfl⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hinv, -, -, -, -, -, -, -, hXr, -, hcap, hLwB, -⟩ :=
    id hrep.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmod⟩ := hXr
  obtain ⟨hMap, hMatch, -, hRS, hSG, -, -, hPar, hCon, -, hCapS, hBD, -, -, -, -, hspE, -⟩ :=
    id hmod
  have hcap' : x.vCap + x.eCap + 2 ≤ (M + N + 2) ^ capExp := by
    rw [← hM, ← hN]; exact hcap
  have hw2 : (x.vCap + x.eCap + 2) ^ 2 < 2 ^ w := by
    calc (x.vCap + x.eCap + 2) ^ 2 ≤ ((M + N + 2) ^ capExp) ^ 2 := Nat.pow_le_pow_left hcap' 2
      _ = (M + N + 2) ^ (2 * capExp) := by rw [← pow_mul, mul_comm]
      _ ≤ (M + N + 2) ^ wordExp :=
          Nat.pow_le_pow_right (by omega) ((asmP10WordExp_ge_two_mul capExp).trans hWE)
      _ ≤ (M + N + 2) ^ wordExp * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
      _ < 2 ^ w := hword
  -- P10 at the caps of the branch and the spanner parameters of the bundle side
  have hvx : x.vCap = vCap := hrep.2.2.2.1
  have hex : x.eCap = eCap := hrep.2.2.2.2.1
  have hP10 : (x.vCap + x.tCap + 2) ^ 2 * (x.L_w + 1) < 2 ^ w := by
    have hLw' : x.L_w ≤
        L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) := by
      rw [← hM, ← hN]; exact hLwB
    have hcapM : SparseCoreCapHyp capExp limbMul L M N x.vCap x.eCap :=
      ⟨hcap', by rw [← hM, ← hN]; exact hCapS.2⟩
    exact p10Word_of_wordExp hcapM hrep.2.2.2.2.2.1 hLw' hWE hword
  have hRB := hB k x.vCap x.eCap x.tCap x.L_w (asmBrSP impl w depth x.xRest) x.xRest.cap rfl
    (show x.xRest.spE ≤ x.eCap by rw [hex]; exact hspE) hinv.2.2.2.1
    hrep.2.2.2.2.2.2.2.1 hP10
  rw [hvx, hex] at hRB
  obtain ⟨body, hbody, o, st', c, x', x4', hrun, hrep', hV5', hE5', hS', hV', hE', hT', hL',
      hrep4', hlo, hhi, hz', hfr, hft, hft4, hd, hcost⟩ :=
    asmBr_restart_runs (P := fmt.precision) (L := L) (capExp := capExp) (limbMul := limbMul) hTR
      hOP hTh J (CF.toRootQueryAtCaps k vCap eCap)
      (embRefresh_asmBrEmbRefreshDisjAt_of_bucketSpanner impl w depth p fEmb bCopy bSpan hfE hcopy
        hpS) hf hpS hpOut brH cfH j h sp vCap eCap tr ord x cfs xcf mem pos ω hp8
      (by rwa [hvx, hex]) hrep.1 hrep.2.1
      hrep.2.2.1 hrep.2.2.2.1 hrep.2.2.2.2.1 ⟨hrep4, hv4, he4⟩ hroots hfoot hf4 hd4 hargs hw2 hz hsp hspW
      (hΨ tr ord x.xRest.mMax hRS hBD hPar hCon fun C hCmem b hb => by
        have hq : (C, b) ∈ activePairs tr := mem_activePairs.mpr ⟨hCmem, hb⟩
        have hok := hSG (x.xRest.slotOf (C, b)) (hMap.2.1 (C, b) hq)
        obtain ⟨hslot, B, hB, hAg⟩ := hMatch (C, b) hq
        have hrg : restartSlotGraph x.xRest.bunS tr.cs ord tr.k (x.xRest.slotOf (C, b)) =
            SparseCore.normGraph (restartBucketBundle tr ord C b).graph := by
          simp only [restartSlotGraph, restartSlotBundle, hslot, ↓reduceDIte, hB,
            restartBucketBundle, hAg.2.1]; rfl
        rw [hrg] at hok
        exact ⟨hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1⟩)
  refine ⟨body, hbody, o, st', c, x', x4', hrun,
    ⟨hrep', hV5', hE5', by rw [hV', hE', hT', hS', hL']; exact hrep.2.2.2⟩,
    hrep4'.1, hrep4'.2.1, hrep4'.2.2, hlo, hhi, hz',
    hfr, hft,
    hft4, hd, ?_⟩
  have hEB := asmBrEmbBound_le_machCost hmod
  have hexp : asmBrRestartMul J.mul readMul (CFS.rootCost capExp) OS.mul capExp *
      (singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord + 1) =
      asmBrRestartConst J.mul readMul (CFS.rootCost capExp) OS.mul capExp *
          singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord +
        asmBrRestartConst J.mul readMul (CFS.rootCost capExp) OS.mul capExp +
        1300 * singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord +
        1300 := by
    simp only [asmBrRestartMul]; ring
  have hcost' : c + R.phi brH x' st'.mem + CF.rep.phi cfH x4' st'.mem ≤
      asmBrRestartConst J.mul readMul (CFS.rootCost capExp) OS.mul capExp *
          singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord +
        asmBrEmbBound embRefreshMul (asmBrSP impl w depth x.xRest) x.xRest.bunS
          x.xRest.spanS tr.cs ord tr.k x.xRest.slots + 100 +
        R.phi brH x mem + CF.rep.phi cfH xcf mem := hcost
  rw [hexp]
  omega

end MinCostFlow.SparseCore.Program
