module

public import MinCostFlow.SparseCore.Program.AssemblyBranchValueBridge

/-!
# The value of `AsmBranchAt` (`AssemblyBranchValue`)

The branch module `AsmBranchAt` (`AssemblyTopIface.lean`) has a representation, an init, a step,
a restart and four readouts. Each of them is proved in clause form in earlier files:
* the init: `asmBrFull_init_runs` (`AssemblyBranchInit.lean`);
* the step: `asmBrFull_step_runs_clause` (`AssemblyBranchStepSpace.lean`), with the bridge of
  `AssemblyBranchValueBridge.lean`;
* the restart: `asmBrFull_restart_runs_clause` (`AssemblyBranchRestartClause.lean`);
* the readouts: `asmBrFull_readLSF_runs`, `asmBrFull_readS_runs`, `asmBrFull_readEmb_runs` and
  `asmBrFull_readOrd_runs` (`AssemblyBranchFull.lean`).
This file puts them together into one value of `AsmBranchAt` (`asmBranchAt_value`).

**Five pieces** come in as interfaces (`AsmBrPieces`), which other files supply: the first phase
of the step (`AsmBrCoreStepAt`), the first phase of the init (`AsmBrCoreInitAt`), P5's restart (`AsmBrBunAt`, from `bunRestartAtK` by `asmBrBunAt_of_bunRestart`
once P2's tour gives P5's tour queries), P7's view of P2's tour (`AsmBrOutProj`) and P2's listing
for readout 5 (`AsmBrTourListProj`). P10 enters by its procedures (`HasReadProcs`), P7's output
step by its procedures (`OutProcsAt`, `sig_outStepSmall_runs_outProcs`).

**The constants, in order.** The spec `asmBrSpec CFS impl K` of the module is fixed before
`capExp`, `limbMul`, `depth`, `w`, `fmt`, `L` and the family `CF`, as `ScBranchModuleHyp` asks.
It depends on P4's spec `CFS` (the cost of a root query), on `impl` (the exponent `impl.cw`), and
on the constants `K : AsmBrConsts`, which the pieces must meet at every parameter:
1. the word exponent: `max (asmP10WordExp capExp) (K.firstWordExp capExp)`, so that P10's word
   condition holds (`p10Word_of_wordExp`), and the first phase of the init gets the word size it
   asks. At `capExp = 3` it is at most `39` when `K.firstWordExp 3 ≤ 39`
   (`asmBrSpec_wordExp_three`), since `asmP10WordExp 3 = 24`;
2. the spaces: `asmBrInitPoly`, `asmBrStepPoly` and `asmBrRestartPoly`, from the polynomials of
   the first phases (`K.initSpace capExp`, `K.stepSpace capExp`, free of `limbMul`), P10's
   multiplier `readBranchMul`, the query space of P7's tour, P5's multiplier `K.bunMul`, and the
   stretch bound `⌈γ_ℓ m⌉ ≤ Cγ (m + 2) ^ cγ` of the sparsifier;
3. the cost multiplier: the sum of the multipliers of the init, the step, the restart and
   readout 5, from the multipliers of the first phases (`K.initMul`, `K.stepMul`, `K.stepYs`, which
   may depend on `capExp` and `limbMul`), P7's multiplier `asmBrMulOut`, P10's, P5's, P4's root
   cost and the multiplier `K.listMul` of P2's listing. The readouts 2 to 4 cost the constant
   `asmBrReadoutCost`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## The constants -/

/-- The multiplier of P7's output step in the step of a branch (`asmBrFull_step_runs_clause` with
P7's procedures `OutProcsAt`). -/
noncomputable def asmBrMulOut : ℕ :=
  Classical.choose (asmBrFull_step_runs_clause sig_outStepSmall_blocks_runs_outProcs)

/-- **The constants of the other pieces of a branch**, fixed before `capExp`,
`limbMul` and the sizes: the multipliers and space polynomials of the two first phases (as
functions of `capExp` and `limbMul`, the spaces of `capExp` alone), the word exponent that the
first phase of the init asks, P7's spec `OS` of the tour, P5's multiplier, the multiplier of P2's
listing, and the stretch bound `⌈γ_ℓ m⌉ ≤ Cγ (m + 2) ^ cγ`. -/
structure AsmBrConsts where
  stepMul : ℕ → ℕ → ℕ
  stepYs : ℕ → ℕ → ℕ
  stepSpace : ℕ → PolyBound
  initMul : ℕ → ℕ → ℕ
  initSpace : ℕ → PolyBound
  firstWordExp : ℕ → ℕ
  OS : OutTourSpec
  bunMul : ℕ
  listMul : ℕ
  Cγ : ℕ
  cγ : ℕ

/-- The word exponent of a branch: P10's and the one the first phase of the init asks. -/
def asmBrWordExp (K : AsmBrConsts) (capExp : ℕ) : ℕ :=
  max (asmP10WordExp capExp) (K.firstWordExp capExp)

/-- **The spec of the branch module**, from P4's spec `CFS`, the sparsifier `impl` and the
constants `K`. -/
noncomputable def asmBrSpec (CFS : AsmCompFamilySpec) (impl : SparsifyImpl) (K : AsmBrConsts) :
    AsmBranchSpec where
  mul capExp limbMul :=
    asmBrInitMul (K.initMul capExp limbMul) readBranchMul capExp limbMul +
      asmBrStepMul (K.stepMul capExp limbMul) (K.stepYs capExp limbMul) asmBrMulOut K.OS.mul
        readBranchMul capExp limbMul +
      asmBrRestartMul K.bunMul readBranchMul (CFS.rootCost capExp) K.OS.mul capExp +
      asmBrOrdMul K.listMul capExp
  readout _ := asmBrReadoutCost
  wordExp capExp := asmBrWordExp K capExp
  initSpace capExp := asmBrInitPoly (K.initSpace capExp) readBranchMul capExp
  stepSpace capExp := asmBrStepPoly (K.stepSpace capExp) readBranchMul K.OS.querySpace capExp
  restartSpace capExp :=
    asmBrRestartPoly K.bunMul readBranchMul embRefreshMul K.OS.querySpace impl.cw K.Cγ K.cγ capExp

/-- **The word exponent at `capExp = 3`** is at most `39` when the first phase of the init asks at
most `39` there, since `asmP10WordExp 3 = 24`. -/
theorem asmBrSpec_wordExp_three {CFS : AsmCompFamilySpec} {impl : SparsifyImpl} {K : AsmBrConsts}
    (h : K.firstWordExp 3 ≤ 39) : (asmBrSpec CFS impl K).wordExp 3 ≤ 39 := by
  show max (asmP10WordExp 3) (K.firstWordExp 3) ≤ 39
  rw [asmP10WordExp_at_3]
  exact max_le (by decide) h

section Mul

variable {CFS : AsmCompFamilySpec} {impl : SparsifyImpl} {K : AsmBrConsts} {capExp limbMul : ℕ}

theorem asmBrSpec_mul_init :
    asmBrInitMul (K.initMul capExp limbMul) readBranchMul capExp limbMul ≤
      (asmBrSpec CFS impl K).mul capExp limbMul := by
  show _ ≤ _ + _ + _ + _
  omega

theorem asmBrSpec_mul_step :
    asmBrStepMul (K.stepMul capExp limbMul) (K.stepYs capExp limbMul) asmBrMulOut K.OS.mul
      readBranchMul capExp limbMul ≤ (asmBrSpec CFS impl K).mul capExp limbMul := by
  show _ ≤ _ + _ + _ + _
  omega

theorem asmBrSpec_mul_restart :
    asmBrRestartMul K.bunMul readBranchMul (CFS.rootCost capExp) K.OS.mul capExp ≤
      (asmBrSpec CFS impl K).mul capExp limbMul := by
  show _ ≤ _ + _ + _ + _
  omega

theorem asmBrSpec_mul_ord :
    asmBrOrdMul K.listMul capExp ≤ (asmBrSpec CFS impl K).mul capExp limbMul := by
  show _ ≤ _ + _ + _ + _
  omega

end Mul

/-! ## The procedures and the pieces -/

/-- The procedure indices of a branch besides the seven of `AsmBranchProcs`: the two first
phases, P7's block, P8's restart, the refresh, P6's block, the copy, P10's block, P5's restart,
the three readout procedures of P10 and P2's listing. -/
structure AsmBrProcIdx where
  fCoreI : ℕ
  fCoreS : ℕ
  bOut : ℕ
  nm : ℕ
  sm : ℕ
  fm : ℕ
  lm : ℕ
  f8 : ℕ
  fEmb : ℕ
  bSpan : ℕ
  bCopy : ℕ
  bRead : ℕ
  fBun : ℕ
  fRL : ℕ
  fRS : ℕ
  fRE : ℕ
  fList : ℕ

/-- **The program holds the procedures of a branch**: the seven operations of `bp` and the
procedures they call, with P10's procedures at `I.bRead` on P4's root query `fRoot`. Independent
of `depth` (P8 reads `depth` at run time from `s + ASM_SD_SPL`). -/
structure HasAsmBrProcs (p : Program) (bp : AsmBranchProcs) (impl : SparsifyImpl)
    (fRoot : ℕ) (I : AsmBrProcIdx) : Prop where
  init : p.procs[bp.fInit]? = some (asmBrInitStmt I.fCoreI (I.bRead + readBranchIdx13 4))
  step : p.procs[bp.fStep]? =
    some (asmBrStepStmt I.fCoreS (outIdxStep I.bOut) (I.bRead + readBranchIdx13 2))
  restart : p.procs[bp.fRestart]? = some (asmBrRestartStmt I.f8 (outIdxReset I.bOut) I.fEmb)
  span : p.HasAt I.bSpan (bucketSpannerProcs impl I.bSpan)
  out : OutProcsAt p I.bOut I.nm I.sm I.fm I.lm
  p8 : p.procs[I.f8]? = some (restartBranchStmt I.fBun (I.bSpan + bsIdxOp0 + 0)
    (I.bRead + readBranchIdx13 3))
  emb : p.procs[I.fEmb]? =
    some (embRefreshStmt I.bCopy (I.bSpan + bsOffRead + spanReadIdxPiWalkPtr))
  copy : p.HasAt I.bCopy [copyWords]
  read : HasReadProcs p I.bRead fRoot
  readLSF : p.procs[bp.fReadLSF]? = some (asmBrReadStmt I.fRL ASM_BR_READ)
  readLSFBody : p.procs[I.fRL]? = some readLSFStmt
  readS : p.procs[bp.fReadS]? = some (asmBrReadStmt I.fRS ASM_BR_READ)
  readSBody : p.procs[I.fRS]? = some readSStmt
  readEmb : p.procs[bp.fReadEmb]? = some (asmBrReadStmt I.fRE ASM_BR_EMB)
  readEmbBody : p.procs[I.fRE]? = some embReadStmt
  readOrd : p.procs[bp.fReadOrd]? = some (asmBrReadOrdStmt I.fList)

/-- **The pieces of a branch given as interfaces**, at the parameters of one branch module,
with the constants `K`: the first phase of the step and of the init with their
multipliers and spaces from `K`, P5's restart for every word size with `16 ≤ 2 ^ w`, with
multiplier `K.bunMul`, P7's view of P2's tour and P2's listing. -/
structure AsmBrPieces (K : AsmBrConsts) (lsfInit : LSFInit) (depth w : ℕ) (fmt : Num.Format w)
    (L capExp limbMul : ℕ) (impl : SparsifyImpl) (p : Program) (I : AsmBrProcIdx)
    (TR : ℕ → ℕ → DSRep AsmTourAbs)
    (B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState))
    (Ψ : BundleTreeState depth → ℕ) (CFR : DSRep CompFamilyAbs) where
  JS : AsmBrCoreStepAt TR B5 impl depth fmt.precision L capExp limbMul
    (asmBrWordExp K capExp) w Ψ p I.fCoreS
  JS_mul : JS.mul = K.stepMul capExp limbMul
  JS_ys : JS.ysMul = K.stepYs capExp limbMul
  JS_space : JS.spaceP = K.stepSpace capExp
  JI : AsmBrCoreInitAt TR B5 CFR lsfInit impl depth fmt.precision L capExp limbMul
    (asmBrWordExp K capExp) w Ψ p I.fCoreI
  JI_mul : JI.mul = K.initMul capExp limbMul
  JI_space : JI.space = K.initSpace capExp
  JB : 16 ≤ 2 ^ w → AsmBrBunAt TR B5 w p I.fBun
  JB_mul : ∀ h16, (JB h16).mul = K.bunMul
  out : AsmBrOutProj K.OS TR w p I.nm I.sm I.fm I.lm
  list : AsmBrTourListProj TR w p I.fList K.listMul

/-! ## The value -/

/-- **The value of `AsmBranchAt`.** Given the locality of the tour and the bundle tables, the
tour handle in the cells of the tour, the walk potential `Ψ` paid by a restart, the stretch bound
of the sparsifier, the re-embedded list `brReemb` of the model, the procedures of the program and
the other pieces, the branch program meets `AsmBranchAt` with the spec
`asmBrSpec CFS impl K` and the representation `asmBrFullRep`. -/
noncomputable def asmBranchAt_value {K : AsmBrConsts} {CFS : AsmCompFamilySpec}
    {lsfInit : LSFInit} {C_lsst : ℝ} {depth w : ℕ} {fmt : Num.Format w} {L capExp limbMul : ℕ}
    {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {fCFInit fCFBatch : ℕ}
    {CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch}
    {bp : AsmBranchProcs} {I : AsmBrProcIdx} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {Ψ : BundleTreeState depth → ℕ}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local)
    (hB5 : ∀ kB slotCap vCap eCap, (B5 kB slotCap vCap eCap).Local)
    (hTh : ∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH)
    (hΨ : AsmWalkPotRestartOK impl depth Ψ)
    (hγ : ∀ m, ⌈impl.γ_ℓ m⌉₊ ≤ K.Cγ * (m + 2) ^ K.cγ)
    (hRe : ∀ tr U ord ord', brReemb tr U ord ord' =
      stepBundleTree_reembList (fun _ => canonicalSparsify impl) tr U ord ord')
    (hP : HasAsmBrProcs p bp impl CF.fRoot I)
    (X : AsmBrPieces K lsfInit depth w fmt L capExp limbMul impl p I TR B5 Ψ CF.rep) :
    AsmBranchAt (asmBrSpec CFS impl K) CFS lsfInit C_lsst depth w fmt L capExp limbMul impl
      brReemb p fCFInit fCFBatch CF bp where
  rep := asmBrFullRep TR B5 impl w fmt.precision L capExp limbMul Ψ
  rep_local := asmBrFullRep_local hTR hB5
  init_runs := by
    intro cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords G ℓ₀ ord cfs xcf mem
      pos ω _ hPL hk0 hj hGv hGne hGm hGn hGnm hcap hword hcf hcfs hlen hdg hdgE hol holE
      hcW hrot hexp hexpE hcfF hargs hz hsp tr₀ hmf _
    have hWE : asmP10WordExp capExp ≤ asmBrWordExp K capExp := le_max_left _ _
    have hsp' : h + (asmBrInitPoly X.JI.space readBranchMul capExp).eval
        (M + N + k + vCap + eCap + L + depth) < 2 ^ w := by
      rw [X.JI_space]; exact hsp
    obtain ⟨body, hbody, o, st', c, x', hrun, hrep', hresp, hcost⟩ :=
      asmBrFull_init_runs hTR hB5 X.JI
        (asmBrReadAt_of_hasReadProcs (Q := CF.toRootQueryAt) hP.read) hP.init hWE
        cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords G ℓ₀ ord cfs xcf mem
        pos ω hk0 hj hGv hGne hGm hGn hGnm hPL hcap hword hcf hcfs hlen hdg hdgE hol holE
        hcW hrot hexp hexpE hcfF hargs hz hsp' hmf
    refine ⟨body, hbody, o, st', c, x', hrun, hrep', ?_, ?_⟩
    · rw [X.JI_space] at hresp; exact hresp
    · refine hcost.trans (Nat.mul_le_mul_right _ ?_)
      rw [X.JI_mul]; exact asmBrSpec_mul_init
  step_runs := by
    intro brH cfH j batch words edits editWords fChgPtr fChgEnd outSlotPtr reembSlotPtr h k M N
      vCap eCap n tr ord x cfsOld cfsNew xcf U ed mem pos ω _ _ hj hM hN hdepth hdepth_lg hdepth_ch hcap hword hrep _ hold _
      hC hSp hCend hBat hBU hcaps hEd hord hEdV hEdB hbW heW hbE heE hos hrs hslots hfoot _ _ hosF
      hrsF hbF heF hCF hfj hchgW hargs hz hsp ord' info hThU hBUn hBUn' hmf hmf'
    have hWE : asmP10WordExp capExp ≤ asmBrWordExp K capExp := le_max_left _ _
    have h16 : 16 ≤ 2 ^ w :=
      Nat.le_of_lt <| lt_of_le_of_lt (show 16 ≤ (M + N + 2) ^ asmBrWordExp K capExp * (L + 1) from
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ (M + N + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
          _ ≤ (M + N + 2) ^ asmBrWordExp K capExp :=
              Nat.pow_le_pow_right (by omega) ((asmP10WordExp_ge_four capExp).trans hWE)
          _ ≤ (M + N + 2) ^ asmBrWordExp K capExp * (L + 1) := Nat.le_mul_of_pos_right _ (by omega))
        hword
    obtain ⟨c, hcAt, hcEx, hCin⟩ := compFamilyChgAt_branch hC hj hold hCend hCF
    obtain ⟨hSpAt, hSpin, hspW⟩ := compSplitListAt_branch hSp hj hold hCend
      (fun a h1 h2 => hCF a (by omega) h2)
    have hspjW : fChgPtr + k + j < 2 ^ w := by
      have hhW : h < 2 ^ w := hargs h (by simp)
      have := hSp.1; omega
    have hRB := asmBrFull_readBranchAt (Q := CF.toRootQueryAt)
      (asmBrReadAt_of_hasReadProcs hP.read) hWE hM hN hcap hword hrep k
      ⟨impl, 0, w, 0, 0, 0, 0⟩ 0 rfl (Nat.zero_le _)
    have hsp' : h + (asmBrStepPoly X.JS.spaceP readBranchMul K.OS.querySpace capExp).eval
        (M + N + k + vCap + eCap + L + depth + words + editWords) < 2 ^ w := by
      rw [X.JS_space]; exact hsp
    obtain ⟨body, hbody, o, st', cst, x', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
        h14, h15, h16', -, -, -, -, hcost⟩ :=
      Classical.choose_spec (asmBrFull_step_runs_clause sig_outStepSmall_blocks_runs_outProcs) X.JS hB5
        hTR X.out hTh hP.out hP.step brH cfH j batch words edits editWords fChgPtr outSlotPtr
        reembSlotPtr h (fChgPtr + k) k M N vCap eCap n tr ord x U ed c ⟨impl, 0, w, 0, 0, 0, 0⟩ 0
        mem pos ω hRB hM hN hdepth hdepth_lg hdepth_ch hcap h16 hword hThU hBUn hBUn' hrep hmf hmf' hBat hBU hcaps hEd hord
        hEdV hEdB hcAt hcEx hSpAt
        (inputAt_of hbW hbE hbF) (inputAt_of heW heE heF) hCin hSpin hos hrs hslots
        (fun a h1 h2 => (hosF a h1 h2).1) (fun a h1 h2 => (hrsF a h1 h2).1) hfoot hargs hchgW hfj
        hspW hspjW (capSq_lt_of_wordExp hcap hWE hword) hz hsp'
    refine ⟨body, hbody, o, st', cst, x', h1, h2, h3, h4, h5, h6, h7, h8, ?_, h10, h11, h12, ?_,
      h14, h15, h16', ?_⟩
    · rw [hRe]; exact h9
    · rw [X.JS_space] at h13; exact h13
    · refine hcost.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ?_) _)
      rw [X.JS_mul, X.JS_ys]; exact asmBrSpec_mul_step
  restart_runs := by
    intro brH cfH j k M N vCap eCap h tr ord x cfs xcf mem pos ω _ _ hj hM hN _ h16 hword hrep hcf
      hv4 he4 hcfs hk0 hfoot hcfF hdisj hargs hz hsp tr' hmf _
    have hWE : asmP10WordExp capExp ≤ asmBrWordExp K capExp := le_max_left _ _
    have hsp' : h + (asmBrRestartPoly (X.JB h16).mul readBranchMul embRefreshMul K.OS.querySpace
        impl.cw K.Cγ K.cγ capExp).eval (M + N + k + vCap + eCap + L + depth) < 2 ^ w := by
      rw [X.JB_mul h16]; exact hsp
    obtain ⟨body, hbody, o, st', c, x', xcf', h1, h2, h3, hv4', he4', h4, h5, h6, h7, h8, h9, h10, hcost⟩ :=
      asmBrFull_restart_runs_clause hΨ hγ hTR X.out hTh (X.JB h16) CF hP.restart hP.span hP.out
        hP.p8 hP.emb hP.copy
        (fun k vCap eCap tCap L_w P' cap hw he ht hLw hbd =>
          asmBrReadAt_of_hasReadProcs (Q := fun k => CF.toRootQueryAtCaps k vCap eCap) hP.read
            k vCap eCap tCap L_w P' cap hw he ht hLw hbd)
        hWE brH cfH j k M N vCap eCap
        h tr ord x cfs xcf mem pos ω hj hM hN h16 hword hrep hcf hv4 he4 hcfs hk0 hfoot hcfF hdisj hargs hz
        hsp' hmf
    refine ⟨body, hbody, o, st', c, x', xcf', h1, h2, h3, hv4', he4', h4, ?_, h6, h7, h8, h9, h10, ?_⟩
    · rw [X.JB_mul h16] at h5; exact h5
    · refine hcost.trans (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_right _ ?_) _) _)
      rw [X.JB_mul h16]; exact asmBrSpec_mul_restart
  readLSF_runs := asmBrFull_readLSF_runs hTR hB5 hP.readLSF hP.readLSFBody
  readS_runs := asmBrFull_readS_runs hTR hB5 hP.readS hP.readSBody
  readEmb_runs := asmBrFull_readEmb_runs hTR hB5 hP.readEmb hP.readEmbBody
  readOrd_runs := by
    intro brH h M N vCap eCap tr ord x mem pos ω hM hN hcap hrep hfoot hb hh hz hroom
    obtain ⟨body, hbody, o, st', c, x', h1, h2, h3, h4, hcost⟩ :=
      asmBrFull_readOrd_runs hTR hB5 hP.readOrd X.list brH h M N vCap eCap tr ord x mem pos ω hM
        hN hcap hrep hfoot hb hh hz hroom
    refine ⟨body, hbody, o, st', c, x', h1, h2, h3, h4, hcost.trans ?_⟩
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      asmBrSpec_mul_ord)) _

end MinCostFlow.SparseCore.Program
