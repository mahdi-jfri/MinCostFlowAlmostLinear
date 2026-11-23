module

public import MinCostFlow.SparseCore.Program.AssemblyTopInit
public import MinCostFlow.SparseCore.Program.AssemblyTopUpdate

import MinCostFlow.SparseCore.Program.AssemblyInputInv

/-!
# Full top-layer implementation of the sparse-core contract (`AssemblyTop`)

Completes the verification of the top-layer sparse-core program (`asmTopProcs`, 29 deterministic
procedures combining the real P1 order store `ordStore_implements_cap`, the linear-time order
compactor, empty-graph dispatch, and `WordRAM.copyWords`, parameterized by the component-LSF
family interface P4 `AsmCompFamilyAt` and the branch module interface `AsmBranchAt`):
* `asmTop_restart_runs` (`op 1`): dispatches to `BR.restart_runs` (or returns `heap` when empty).
* `asmTop_readLSF_runs` (`op 2`): dispatches to `BR.readLSF_runs` (or writes empty `LSFAt`).
* `asmTop_readS_runs` (`op 3`): dispatches to `BR.readS_runs` (or points to the header's `emptyGraph`).
* `asmTop_readEmb_runs` (`op 4`): dispatches to `BR.readEmb_runs` (or returns `heap + 2` when empty).
* `asmTop_readOrd_runs` (`op 5`): dispatches to `BR.readOrd_runs` (or writes empty `OrdListAt`).
* `asmTop_implements_kfr`: full `DSRep.Implements` theorem against `sparseCoreOrdMachineContractKFR`
  (with `reembList` on `op 0`), and `asmTop_implements_kf` against `sparseCoreOrdMachineContractKF`.
* `asmTop_uniform_reemb_cap` and `asmTop_uniform_cap`: uniform top-layer statements (with uniform
  `τ`, `phi`, `foot` across all levels and rebuilds, and `R` before `L` for limb-count-independent
  LSF initializers).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

/-! ## `op 1` (Restart) -/

theorem asmTop_restart_runs
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    {G₀ : MGraph} {k M N vCap eCap sizeParam : ℕ}
    (hfmt : fmt.limbBits = 4) (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hdepth : 1 ≤ depth) (_hdepth_le : depth ≤ M + N + k + L)
    (hsize : M + N + k + vCap + eCap + L + depth ≤ sizeParam)
    (hγt : impl.γ_t M = 1)
    (hInit : ∀ j < k, IsValidLSFInitFor lsfInit C_lsst k j) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let P := asmTopParams CFS BRS capExp limbMul
    let alloc := asmTopAlloc CFS BRS capExp sizeParam
    let D := sparseCoreOrdMachineContractKFR fmt L T (bundleToolReemb brReemb) G₀ k M N vCap eCap capExp P alloc
    let R := asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap
    ∀ (hndl : ℕ) (a : SparseCoreOrdAbs T) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some hndl → R.rep hndl a x mem →
      D.pre 1 a args mem → (∀ addr, R.foot hndl x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 1 a args mem < 2 ^ w →
      ∃ body, p.procs[asmTopOpIdx b 1]? = some body ∧
        ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
        ∃ a' x', R.rep hndl a' x' st'.mem ∧ D.post 1 a args mem a' st'.mem ∧
          R.Respects (R.foot hndl x) (heapArg args) (D.space 1 a args mem) mem o.value hndl x' st'.mem ∧
          c + R.phi hndl x' st'.mem ≤ D.cost 1 a args mem + R.phi hndl x mem := by
  intro T P alloc D R hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
  refine ⟨_, hp.at_op1, ?_⟩
  rcases hpre with ⟨hinp, h0', branch, heap, hargs_eq, hbr_lt⟩
  subst hargs_eq
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst h0'
  have hheapArg : heapArg [hndl, branch, heap] = heap := rfl
  rw [hheapArg] at hfoot hz hsp ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargsW
  rcases hargsW with ⟨hhndlW, hbrW, hheapW⟩
  rcases hrep with ⟨⟨⟨hxne, hxk, hxres, h0, h1, h2, h3, h4, h5, h6, h7,
    he0, he1, he2, he3, hnonempty⟩, hxL, hxPfp, hxvCap, hxeCap, hxwM, hxcap, hxk_pos⟩, hEmpty, hCaps⟩
  obtain ⟨hinp_k, hinp_ord, hinp_mn⟩ := asm_input_inv lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    (canonicalSparsifyParams impl) (dsAmortConst impl) hinp
  have hk_eq : x.k = k := hxk.trans hinp_k
  have hk_pos : 0 < k := by omega
  have hhdr_sz : ASM_HDR_SIZE = 20 := rfl
  have hresHi_le : x.resHi ≤ heap := by have := hfoot (x.resHi - 1) (Or.inr (Or.inl ⟨by omega, by omega⟩)); omega
  have hhdr_lt : hndl + ASM_HDR_SIZE ≤ heap := by have := hfoot (hndl + ASM_HDR_SIZE - 1) (Or.inl ⟨by omega, by omega⟩); omega
  have hw16 : 16 < 2 ^ w := by unfold ASM_HDR_SIZE at hxres; omega
  set st0 := startState [hndl, branch, heap] mem pos
  have hload3 : Runs w p ω (.assign 3 (.load (.reg 0))) st0 .normal
      { st0 with regs := Function.update st0.regs 3 (if x.ne.isSome then 1 else 0) } _ :=
    runs_assign_iff.mpr ⟨if x.ne.isSome then 1 else 0,
      Expr.eval_load_of_eq (w := w) (Expr.eval_reg_of_eq (v := hndl) (by simp [st0, startState]))
        (by simpa [st0, startState, ASM_HDR_NE] using h0), rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 3 (if x.ne.isSome then 1 else 0) }
  let a' := ordRestartNext a branch
  cases hxne_b : x.ne with
  | none =>
    have hst_em : a.st.isNonempty = false := by simpa [hxne_b] using hxne.symm
    have ha'_st : a'.st = a.st := by
      have hR := sparseCoreBundleRestartTool_restart_eq lsfInit C_lsst depth (fun _ => canonicalSparsify impl) a.st branch
      change T.restart a.st branch = _ at hR
      change T.restart a.st branch = a.st
      rw [hR]; simp [hst_em]
    have hret : Runs w p ω (.ret (.reg 2)) st1 (.returned heap) st1 _ :=
      runs_ret_iff.mpr ⟨heap, Expr.eval_reg_of_eq (by simp [st1, st0, startState]), rfl, rfl, rfl⟩
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopRestartBody bp.fRestart) st0 (.returned heap) st1 cF ∧ cF ≤ 30 := by
      unfold asmTopRestartBody
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload3,
        runs_cond_iff.mpr ⟨0, _, Expr.eval_reg_of_eq (v := 0) (by simp [st1, hxne_b]),
          by simp only [↓reduceIte]; exact hret, rfl⟩, rfl⟩), ?_⟩
      simp only [Expr.size]; omega
    refine ⟨.returned heap, st1, cF, hfull, a', x, ?_, rfl,
      ⟨le_rfl, by simp [Outcome.value], hz, fun _ _ _ => rfl, fun _ ha => Or.inl ha⟩, ?_⟩
    · refine ⟨⟨⟨by rw [ha'_st]; exact hxne, by rw [ha'_st]; exact hxk, hxres, h0, h1, h2, h3, h4, h5, h6, h7,
        he0, he1, he2, he3, fun _ hS => by simp [hxne_b] at hS⟩, hxL, hxPfp, hxvCap, hxeCap, hxwM, hxcap, hxk_pos⟩,
        hEmpty, hCaps⟩
    · have hphi0 : R.phi hndl x st1.mem = 0 ∧ R.phi hndl x mem = 0 := by simp [R, asmTopRepEq, asmTopPhi, hxne_b]
      rw [hphi0.1, hphi0.2]
      change cF + 0 ≤ P.mul * (T.cost (T.restart a.st branch) - T.cost a.st + 1) + 0
      have hmul : 400 ≤ P.mul := by simp [P, asmTopParams]
      have h1 : 400 * 1 ≤ P.mul * (T.cost (T.restart a.st branch) - T.cost a.st + 1) := Nat.mul_le_mul hmul (by omega)
      omega
  | some ne =>
    have hst_ne : a.st.isNonempty = true := by simpa [hxne_b] using hxne.symm
    obtain ⟨h8, h9, h10, hcfLt, htblLt, hbrLt, hvG, heG, hG_br, hOrdRep, hCFRep, hTbl, hBRRep, hd1, hd2, hd3, hd4, hd5⟩ :=
      hnonempty ne hxne_b
    have hxM_eq : x.M = M := (hG_br 0 (by omega)).2.1.symm.trans (hinp_mn 0).1
    have hxN_eq : x.N = N := (hG_br 0 (by omega)).2.2.symm.trans (hinp_mn 0).2.1
    have hwPL : (M + N + 2) ^ P.wordExp * (L + 1) < 2 ^ w := by
      simpa [hxM_eq, hxN_eq, hxL] using hxwM
    have hwBR : (M + N + 2) ^ BRS.wordExp capExp * (L + 1) < 2 ^ w :=
      lt_of_le_of_lt (Nat.mul_le_mul_right (L + 1)
        (Nat.pow_le_pow_right (by omega) (by simp [P, asmTopParams, asmTopWordExp]))) hwPL
    have hord_eq : a.st.ord = a.ord := hinp_ord hst_ne
    have hsp_br : heap + (BRS.restartSpace capExp).eval (M + N + k + vCap + eCap + L + depth) < 2 ^ w := by
      have h1 : (BRS.restartSpace capExp).eval (M + N + k + vCap + eCap + L + depth) ≤ (BRS.restartSpace capExp).eval sizeParam :=
        (BRS.restartSpace capExp).eval_mono hsize
      change heap + (BRS.restartSpace capExp).eval sizeParam < 2 ^ w at hsp; omega
    have hload4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const ASM_HDR_CFH)))) st1 .normal
        { st1 with regs := Function.update st1.regs 4 ne.cfH } _ :=
      runs_assign_iff.mpr ⟨ne.cfH, Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st1, st0, startState]))
          (Expr.eval_const (by unfold ASM_HDR_CFH; omega)) (by unfold ASM_HDR_CFH ASM_HDR_SIZE at *; omega)) h9,
        rfl, rfl, rfl⟩
    set st2 : State := { st1 with regs := Function.update st1.regs 4 ne.cfH }
    have hload5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL)))) st2 .normal
        { st2 with regs := Function.update st2.regs 5 ne.tbl } _ :=
      runs_assign_iff.mpr ⟨ne.tbl, Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st2, st1, st0, startState]))
          (Expr.eval_const (by unfold ASM_HDR_TBL; omega)) (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)) h10,
        rfl, rfl, rfl⟩
    set st3 : State := { st2 with regs := Function.update st2.regs 5 ne.tbl }
    have hload6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 5) (.reg 1)))) st3 .normal
        { st3 with regs := Function.update st3.regs 6 (ne.brH branch) } _ :=
      runs_assign_iff.mpr ⟨ne.brH branch, Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := ne.tbl) (by simp [st3]))
          (Expr.eval_reg_of_eq (v := branch) (by simp [st3, st2, st1, st0, startState])) (by omega))
        (hTbl branch (by omega)), rfl, rfl, rfl⟩
    set st4 : State := { st3 with regs := Function.update st3.regs 6 (ne.brH branch) }
    have hbrFt_lt : ∀ addr, BR.rep.foot (ne.brH branch) (ne.xBR branch) addr → addr < heap := fun addr ha =>
      hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨branch, by omega, ha⟩)))
    have hcfFt_lt : ∀ addr, CF.rep.foot ne.cfH ne.xCF addr → addr < heap := fun addr ha =>
      hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; left; exact ha)))
    have ha'_st : a'.st = { a.st with trees := (Function.update a.st.trees branch
        (restartBundleTree depth (fun _ => canonicalSparsify impl) (a.st.trees branch) a.st.ord)) } := by
      have hR := sparseCoreBundleRestartTool_restart_eq lsfInit C_lsst depth (fun _ => canonicalSparsify impl) a.st branch
      change T.restart a.st branch = _ at hR
      change T.restart a.st branch = _
      rw [hR]; simp only [hst_ne, ↓reduceIte]; congr 1
    have ha'_ne : a'.st.isNonempty = true := by rw [ha'_st]; exact hst_ne
    have hvG_v : ∀ v ∈ a.G.V, v < vCap := by rwa [hxvCap] at hvG
    have heG_e : ∀ e ∈ a.G.E, e < eCap := by rwa [hxeCap] at heG
    have hinp' : SparseCoreOrdInput T k M N a'.st a.G a.ord a.n :=
      SparseCoreOrdInput.restart hinp branch hbr_lt
    have hModPre : AsmBrModelFacts impl vCap eCap (a.st.trees branch) a.st.ord := by
      rw [hord_eq]
      exact (asm_input_model_inv hk_pos hdepth hγt hvG_v heG_e hinp hst_ne (hInit branch hbr_lt)).1
    have hModPost : AsmBrModelFacts impl vCap eCap
        (restartBundleTree depth (fun _ => canonicalSparsify impl) (a.st.trees branch) a.st.ord) a.st.ord := by
      have h := (asm_input_model_inv hk_pos hdepth hγt hvG_v heG_e hinp' ha'_ne (hInit branch hbr_lt)).1
      simpa [ha'_st, ← hord_eq] using h
    have hvCF : CF.vCapOf ne.xCF = vCap := (hCaps ne hxne_b).1.trans hxvCap
    have heCF : CF.eCapOf ne.xCF = eCap := (hCaps ne hxne_b).2.trans hxeCap
    obtain ⟨bodyBR, hbodyBR, oBR, stBR, cBR, xBr', xcf', hrunBR, hBRRep', hCFRepBR', hvCF', heCF',
        hB_lo, hB_hi, hzB, hB_fr, hB_ft, hCF_ft, hBRCF_disj, hBRCost⟩ :=
      BR.restart_runs (ne.brH branch) ne.cfH branch k M N vCap eCap heap (a.st.trees branch) a.st.ord
        (ne.xBR branch) (fun j => (a.st.trees j).cs) ne.xCF st4.mem st4.pos ω
        hfmt hk_pos hbr_lt (hinp_mn branch).1 (hinp_mn branch).2.1 hcap (by omega) hwBR
        (by rw [← hxvCap, ← hxeCap]; exact hBRRep branch (by omega)) hCFRep hvCF heCF rfl
        (asm_input_cs_k lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
          (canonicalSparsifyParams impl) (dsAmortConst impl) hinp hst_ne 0).symm
        hbrFt_lt hcfFt_lt
        (fun addr ha hcf => (hd3 addr hcf).2 branch (by omega) ha)
        (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl | rfl
            · have := hbrLt branch (by omega); omega
            all_goals omega)
        hz hsp_br hModPre hModPost
    have hcallBR : Runs w p ω (.call 7 bp.fRestart [.reg 6, .reg 4, .reg 1, .reg 2]) st4 .normal
        { stBR with regs := Function.update st4.regs 7 oBR.value }
        (argsSize [.reg 6, .reg 4, .reg 1, .reg 2] + cBR + 1) := by
      refine (runs_call_iff (r := 7) (f := bp.fRestart) (st := st4) (o := .normal)
        (st' := { stBR with regs := Function.update st4.regs 7 oBR.value })).mpr
        ⟨[ne.brH branch, ne.cfH, branch, heap], bodyBR, oBR, stBR, cBR, ?_, hbodyBR, hrunBR, rfl, rfl, rfl⟩
      simp [evalArgs, Expr.eval, st4, st3, st2, st1, st0, startState]
    set st5 : State := { stBR with regs := Function.update st4.regs 7 oBR.value }
    have hret : Runs w p ω (.ret (.reg 7)) st5 (.returned oBR.value) st5 _ :=
      runs_ret_iff.mpr ⟨oBR.value, Expr.eval_reg_of_eq (by simp [st5]), rfl, rfl, rfl⟩
    have hthen := runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hload4,
      runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hload5,
        runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hload6,
          runs_seq_iff.mpr (Or.inr ⟨st5, _, _, hcallBR, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopRestartBody bp.fRestart) st0 (.returned oBR.value) st5 cF ∧ cF ≤ cBR + 60 := by
      unfold asmTopRestartBody
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload3,
        runs_cond_iff.mpr ⟨1, _, Expr.eval_reg_of_eq (v := 1) (by simp [st1, hxne_b]),
          by simp only [one_ne_zero, ↓reduceIte]; exact hthen, rfl⟩, rfl⟩), ?_⟩
      simp only [argsSize_cons, argsSize_nil, Expr.size]; omega
    let ne' : AsmTopNE CF.rep.τ BR.rep.τ := { ne with xCF := xcf', xBR := Function.update ne.xBR branch xBr' }
    let x' : R.τ := { x with ne := some ne' }
    have hfr_hdr : ∀ i < ASM_HDR_SIZE, stBR.mem (hndl + i) = mem (hndl + i) := fun i hi =>
      hB_fr _ (by omega) (fun hf => (hd1 _ ⟨by omega, by omega⟩).2.2.2 branch (by omega) hf)
        (fun hc => (hd1 _ ⟨by omega, by omega⟩).2.1 hc)
    have hOrdRep' : (ordStoreRep x.vCap x.eCap).rep ne.ordH a.st.ord ne.xOrd stBR.mem :=
      (ordStoreRep_local x.vCap x.eCap ne.ordH a.st.ord ne.xOrd mem stBR.mem fun addr ha =>
        (hB_fr addr (hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; exact Or.inl ha))))
          (fun hb => (hd2 addr ha).2.2 branch (by omega) hb)
          (fun hc => (hd2 addr ha).1 hc)).symm).1 hOrdRep
    have hCFRep' : CF.rep.rep ne.cfH (fun j => (a'.st.trees j).cs) xcf' stBR.mem := by
      have hcs_eq : (fun j => (a'.st.trees j).cs) = (fun j => (a.st.trees j).cs) := by
        funext j; rw [ha'_st]; dsimp only
        by_cases hj : j = branch
        · subst hj; simp [restartBundleTree]
        · simp [Function.update_of_ne hj]
      rw [hcs_eq]
      exact hCFRepBR'
    refine ⟨.returned oBR.value, st5, _, hfull, a', x', ⟨?_, fun h => by simp [x'] at h,
      fun ne₁ hne₁ => by cases Option.some.inj hne₁.symm; exact ⟨by rw [hxvCap]; exact hvCF', by rw [hxeCap]; exact heCF'⟩⟩, rfl, ?_, ?_⟩
    · refine ⟨⟨by rw [ha'_st]; simpa [x', hxne_b] using hxne, by rw [ha'_st]; exact hxk, hxres,
        by simpa [x', hxne_b] using (hfr_hdr ASM_HDR_NE (by decide)).trans h0,
        (hfr_hdr ASM_HDR_K (by decide)).trans h1, (hfr_hdr ASM_HDR_M (by decide)).trans h2,
        (hfr_hdr ASM_HDR_N (by decide)).trans h3, (hfr_hdr ASM_HDR_VCAP (by decide)).trans h4,
        (hfr_hdr ASM_HDR_ECAP (by decide)).trans h5, (hfr_hdr ASM_HDR_L (by decide)).trans h6,
        (hfr_hdr ASM_HDR_PFP (by decide)).trans h7,
        (hfr_hdr ASM_HDR_EMPTYG (by decide)).trans he0, (hfr_hdr (ASM_HDR_EMPTYG + 1) (by decide)).trans he1,
        (hfr_hdr (ASM_HDR_EMPTYG + 2) (by decide)).trans he2, (hfr_hdr (ASM_HDR_EMPTYG + 3) (by decide)).trans he3,
        fun ne₁ hne₁ => ?_⟩, hxL, hxPfp, hxvCap, hxeCap, hxwM, hxcap, hxk_pos⟩
      have hne_eq : ne₁ = ne' := Option.some.inj hne₁.symm; subst hne_eq
      refine ⟨(hfr_hdr ASM_HDR_ORDH (by decide)).trans h8, (hfr_hdr ASM_HDR_CFH (by decide)).trans h9,
        (hfr_hdr ASM_HDR_TBL (by decide)).trans h10, hcfLt, htblLt, hbrLt, hvG, heG, ?_,
        by rw [ha'_st]; exact hOrdRep', hCFRep',
        fun j hj => by
          dsimp only [x'] at hj
          exact (hB_fr (ne.tbl + j) (hfoot (ne.tbl + j) (Or.inr (Or.inr (by simp only [hxne_b]; right; right; left; exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩))))
            (fun hb => hd4 (ne.tbl + j) ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩ branch (by omega) hb)
            (fun hc => (hd3 (ne.tbl + j) hc).1 ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩)).trans (hTbl j hj),
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj; rw [ha'_st]; dsimp only
        by_cases hjb : j = branch
        · subst hjb; simp only [Function.update_self]; exact hG_br j hj
        · simp only [Function.update_of_ne hjb]; exact hG_br j hj
      · intro j hj; rw [ha'_st]; dsimp only [ne']
        by_cases hjb : j = branch
        · subst hjb; simp only [Function.update_self, x']; rw [hxvCap, hxeCap]; exact hBRRep'
        · simp only [Function.update_of_ne hjb]
          exact (BR.rep_local (ne.brH j) ⟨a.st.trees j, a.st.ord, x.vCap, x.eCap⟩ (ne.xBR j) mem stBR.mem fun addr ha =>
            (hB_fr addr (hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j, hj, ha⟩))))
              (fun hb => hd5 j hj branch (by omega) hjb addr ha hb)
              (fun hc => (hd3 addr hc).2 j hj ha)).symm).1 (hBRRep j hj)
      · intro addr ha
        refine ⟨(hd1 addr ha).1, ?_, (hd1 addr ha).2.2.1, fun j hj hb => ?_⟩
        · intro hc; rcases hCF_ft addr hc with hold | hnew; exact (hd1 addr ha).2.1 hold; omega
        · by_cases hjb : j = branch
          · subst hjb; simp only [ne', Function.update_self] at hb
            rcases hB_ft addr hb with hold | hnew; exact (hd1 addr ha).2.2.2 j hj hold; omega
          · simp only [ne', Function.update_of_ne hjb] at hb; exact (hd1 addr ha).2.2.2 j hj hb
      · intro addr ha
        have halt := hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; exact Or.inl ha)))
        refine ⟨?_, (hd2 addr ha).2.1, fun j hj hb => ?_⟩
        · intro hc; rcases hCF_ft addr hc with hold | hnew; exact (hd2 addr ha).1 hold; omega
        · by_cases hjb : j = branch
          · subst hjb; simp only [ne', Function.update_self] at hb
            rcases hB_ft addr hb with hold | hnew; exact (hd2 addr ha).2.2 j hj hold; omega
          · simp only [ne', Function.update_of_ne hjb] at hb; exact (hd2 addr ha).2.2 j hj hb
      · intro addr ha
        refine ⟨?_, fun j hj hb => ?_⟩
        · intro htb
          have hlt := hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; left; exact htb)))
          rcases hCF_ft addr ha with hold | hnew; exact (hd3 addr hold).1 htb; omega
        · by_cases hjb : j = branch
          · subst hjb; simp only [ne', Function.update_self] at hb
            exact hBRCF_disj addr hb ha
          · simp only [ne', Function.update_of_ne hjb] at hb
            have hlt := hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j, hj, hb⟩)))
            rcases hCF_ft addr ha with hold | hnew; exact (hd3 addr hold).2 j hj hb; omega
      · intro addr ha j hj hb
        have halt := hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; left; exact ha)))
        by_cases hjb : j = branch
        · subst hjb; simp only [ne', Function.update_self] at hb
          rcases hB_ft addr hb with hold | hnew; exact hd4 addr ha j hj hold; omega
        · simp only [ne', Function.update_of_ne hjb] at hb; exact hd4 addr ha j hj hb
      · intro j₁ h₁ j₂ h₂ hne addr ha1 ha2
        by_cases h1b : j₁ = branch
        · subst h1b; have h2b : j₂ ≠ j₁ := Ne.symm hne
          simp only [ne', Function.update_self, Function.update_of_ne h2b] at ha1 ha2
          rcases hB_ft addr ha1 with hold | hnew
          · exact hd5 j₁ h₁ j₂ h₂ hne addr hold ha2
          · have := hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j₂, h₂, ha2⟩))); omega
        · by_cases h2b : j₂ = branch
          · subst h2b; simp only [ne', Function.update_self, Function.update_of_ne h1b] at ha1 ha2
            rcases hB_ft addr ha2 with hold | hnew
            · exact hd5 j₁ h₁ j₂ h₂ hne addr ha1 hold
            · have := hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j₁, h₁, ha1⟩))); omega
          · simp only [ne', Function.update_of_ne h1b, Function.update_of_ne h2b] at ha1 ha2
            exact hd5 j₁ h₁ j₂ h₂ hne addr ha1 ha2
    · have hretV : (Outcome.returned oBR.value).value = oBR.value := rfl
      refine ⟨by rw [hretV]; exact hB_lo,
        by rw [hretV]
           simp only [D, sparseCoreOrdMachineContractKFR, sparseCoreOrdMachineContractKF,
             sparseCoreOrdMachineContractK, sparseCoreOrdMachineContract, alloc, asmTopAlloc]
           have h1 := (BRS.restartSpace capExp).eval_mono hsize
           omega,
        by rw [hretV]; exact hzB,
        fun addr ha hnf => hB_fr addr ha
          (fun hb => hnf (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨branch, by omega, hb⟩))))
          (fun hc => hnf (Or.inr (Or.inr (by simp only [hxne_b]; exact Or.inr (Or.inl hc))))),
        fun addr ha => ?_⟩
      rcases ha with h1 | h2 | h3
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr (Or.inl h2))
      · rcases h3 with h3a | h3b | h3c | ⟨j, hj, h3d⟩
        · exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; exact Or.inl h3a)))
        · rcases hCF_ft addr h3b with hold | hnew
          · exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; exact Or.inr (Or.inl hold))))
          · exact Or.inr (by rw [hretV]; exact hnew)
        · exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; right; right; left; exact h3c)))
        · by_cases hjb : j = branch
          · subst hjb; simp only [ne', Function.update_self] at h3d
            rcases hB_ft addr h3d with hold | hnew
            · exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j, hj, hold⟩)))
            · exact Or.inr (by rw [hretV]; exact hnew)
          · simp only [ne', Function.update_of_ne hjb] at h3d
            exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j, hj, h3d⟩)))
    · -- Cost bound
      have hΔ : T.cost (T.restart a.st branch) - T.cost a.st =
          singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) (a.st.trees branch) a.st.ord := by
        have h := bundleRestartToolMachWith_restart_cost_eq lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
          (canonicalSparsifyParams impl) (dsAmortConst impl) a.st branch hst_ne (by omega)
        change T.cost (T.restart a.st branch) = T.cost a.st + _ at h
        omega
      have hmem_br : branch ∈ Finset.range k := Finset.mem_range.mpr hbr_lt
      have hsum_new : (Finset.range k).sum (fun j => BR.rep.phi (ne'.brH j) (ne'.xBR j) stBR.mem) =
          BR.rep.phi (ne.brH branch) xBr' stBR.mem +
          ((Finset.range k).erase branch).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) mem) := by
        rw [← Finset.add_sum_erase _ _ hmem_br]
        simp only [ne', Function.update_self]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hne := Finset.ne_of_mem_erase hj
        have hjk := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
        simp only [Function.update_of_ne hne]
        exact (BR.rep_local (ne.brH j) ⟨a.st.trees j, a.st.ord, x.vCap, x.eCap⟩ (ne.xBR j) mem stBR.mem fun addr ha =>
          (hB_fr addr (hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j, by omega, ha⟩))))
            (fun hb => hd5 j (by omega) branch (by omega) hne addr ha hb)
            (fun hc => (hd3 addr hc).2 j (by omega) ha)).symm).2.symm
      have hsum_old : (Finset.range k).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) mem) =
          BR.rep.phi (ne.brH branch) (ne.xBR branch) mem +
          ((Finset.range k).erase branch).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) mem) :=
        (Finset.add_sum_erase _ _ hmem_br).symm
      have hphi_new : R.phi hndl x' st5.mem =
          (ordStoreRep x.vCap x.eCap).phi ne.ordH ne.xOrd mem + CF.rep.phi ne.cfH xcf' stBR.mem +
          (Finset.range k).sum (fun j => BR.rep.phi (ne'.brH j) (ne'.xBR j) stBR.mem) := by
        have hOrdPhi : (ordStoreRep x.vCap x.eCap).phi ne.ordH ne.xOrd stBR.mem =
            (ordStoreRep x.vCap x.eCap).phi ne.ordH ne.xOrd mem := rfl
        show (ordStoreRep x.vCap x.eCap).phi ne.ordH ne.xOrd stBR.mem + CF.rep.phi ne.cfH xcf' stBR.mem +
          (Finset.range x.k).sum (fun j => BR.rep.phi (ne'.brH j) (ne'.xBR j) stBR.mem) = _
        rw [hOrdPhi, hk_eq]
      have hphi_old : R.phi hndl x mem =
          (ordStoreRep x.vCap x.eCap).phi ne.ordH ne.xOrd mem + CF.rep.phi ne.cfH ne.xCF mem +
          (Finset.range k).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) mem) := by
        simp only [R, asmTopRepEq, asmTopPhi, hxne_b, hk_eq]
      change cF + R.phi hndl x' st5.mem ≤ P.mul * (T.cost (T.restart a.st branch) - T.cost a.st + 1) + R.phi hndl x mem
      rw [hΔ, hphi_new, hphi_old, hsum_new, hsum_old]
      have hmul_le : (BRS.mul capExp limbMul + 400) * (singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl)
          (a.st.trees branch) a.st.ord + 1) ≤
          P.mul * (singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl)
          (a.st.trees branch) a.st.ord + 1) := Nat.mul_le_mul_right _ (by simp only [P, asmTopParams]; omega)
      have hdist : (BRS.mul capExp limbMul + 400) * (singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl)
          (a.st.trees branch) a.st.ord + 1) =
          BRS.mul capExp limbMul * (singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl)
          (a.st.trees branch) a.st.ord + 1) + 400 * (singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl)
          (a.st.trees branch) a.st.ord + 1) := by ring
      have h400 : 60 ≤ 400 * (singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl)
          (a.st.trees branch) a.st.ord + 1) := by
        have := Nat.mul_le_mul_left 400 (show 1 ≤ singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl)
          (a.st.trees branch) a.st.ord + 1 by omega)
        omega
      change cBR + BR.rep.phi (ne.brH branch) xBr' stBR.mem + CF.rep.phi ne.cfH xcf' stBR.mem ≤
        BRS.mul capExp limbMul * (singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl)
          (a.st.trees branch) a.st.ord + 1) +
        BR.rep.phi (ne.brH branch) (ne.xBR branch) mem + CF.rep.phi ne.cfH ne.xCF mem at hBRCost
      omega

/-! ## Readouts `op 2`, `op 3`, `op 4`, `op 5` -/

/-- Helper updating a single branch witness `xBr'` inside a nonempty `AsmTopMeta` for readouts
`op 2..5` that leave `a` unchanged and respect `BR.rep.foot (ne.brH branch) (ne.xBR branch)`. -/
theorem asmTop_branch_readout_frame
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {fCFInit fCFBatch : ℕ} {bp : AsmBranchProcs}
    {CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch}
    {BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp}
    {hndl branch heap space outVal : ℕ} {vCap eCap : ℕ}
    {a : SparseCoreOrdAbs (sparseCoreProgTool lsfInit C_lsst depth impl)}
    {x : AsmTopMeta CF.rep.τ BR.rep.τ} {ne : AsmTopNE CF.rep.τ BR.rep.τ} {xBr' : BR.rep.τ}
    {mem mem' : ℕ → ℕ}
    (hxne_b : x.ne = some ne) (hbr_lt : branch < x.k)
    (hrep : (asmTopRep (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      (asmTopParams CFS BRS capExp limbMul).wordExp capExp limbMul w L fmt.precision vCap eCap).rep hndl a x mem)
    (hfoot : ∀ addr, (asmTopRep (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      (asmTopParams CFS BRS capExp limbMul).wordExp capExp limbMul w L fmt.precision vCap eCap).foot hndl x addr → addr < heap)
    (hBRRep' : BR.rep.rep (ne.brH branch) ⟨a.st.trees branch, a.st.ord, vCap, eCap⟩ xBr' mem')
    (hResp : BR.rep.Respects (BR.rep.foot (ne.brH branch) (ne.xBR branch)) heap space mem outVal (ne.brH branch) xBr' mem') :
    let R := asmTopRep (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      (asmTopParams CFS BRS capExp limbMul).wordExp capExp limbMul w L fmt.precision vCap eCap
    let x' : R.τ := { x with ne := some { ne with xBR := Function.update ne.xBR branch xBr' } }
    R.rep hndl a x' mem' ∧
    R.Respects (R.foot hndl x) heap space mem outVal hndl x' mem' ∧
    R.phi hndl x' mem' + BR.rep.phi (ne.brH branch) (ne.xBR branch) mem =
      R.phi hndl x mem + BR.rep.phi (ne.brH branch) xBr' mem' := by
  intro R x'
  rcases hrep with ⟨⟨hxne, hxk, hxres, h0, h1, h2, h3, h4, h5, h6, h7, he0, he1, he2, he3, hnonempty⟩,
    hxL, hxPfp, hxvCap, hxeCap, hxwM, hxcap, hxk_pos⟩
  obtain ⟨h8, h9, h10, hcfLt, htblLt, hbrLt, hvG, heG, hG_br, hOrdRep, hCFRep, hTbl, hBRRep, hd1, hd2, hd3, hd4, hd5⟩ :=
    hnonempty ne hxne_b
  rcases hResp with ⟨hB_lo, hB_hi, hzB, hB_fr, hB_ft⟩
  have hhdr_sz : ASM_HDR_SIZE = 20 := rfl
  have hhdr_lt : hndl + ASM_HDR_SIZE ≤ heap := by have := hfoot (hndl + ASM_HDR_SIZE - 1) (Or.inl ⟨by omega, by omega⟩); omega
  have hfr_hdr : ∀ i < ASM_HDR_SIZE, mem' (hndl + i) = mem (hndl + i) := fun i hi =>
    hB_fr _ (by omega) (fun hb => (hd1 _ ⟨by omega, by omega⟩).2.2.2 branch hbr_lt hb)
  have hcfFt_lt : ∀ addr, CF.rep.foot ne.cfH ne.xCF addr → addr < heap := fun addr ha =>
    hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; left; exact ha)))
  have hCFPhi' : CF.rep.phi ne.cfH ne.xCF mem' = CF.rep.phi ne.cfH ne.xCF mem :=
    (CF.rep_local ne.cfH (fun j => (a.st.trees j).cs) ne.xCF mem mem' fun addr ha =>
      (hB_fr addr (hcfFt_lt addr ha) (fun hb => (hd3 addr ha).2 branch hbr_lt hb)).symm).2.symm
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨by simpa [x', hxne_b] using hxne, hxk, hxres,
      by simpa [x', hxne_b] using (hfr_hdr ASM_HDR_NE (by decide)).trans h0,
      (hfr_hdr ASM_HDR_K (by decide)).trans h1, (hfr_hdr ASM_HDR_M (by decide)).trans h2,
      (hfr_hdr ASM_HDR_N (by decide)).trans h3, (hfr_hdr ASM_HDR_VCAP (by decide)).trans h4,
      (hfr_hdr ASM_HDR_ECAP (by decide)).trans h5, (hfr_hdr ASM_HDR_L (by decide)).trans h6,
      (hfr_hdr ASM_HDR_PFP (by decide)).trans h7,
      (hfr_hdr ASM_HDR_EMPTYG (by decide)).trans he0, (hfr_hdr (ASM_HDR_EMPTYG + 1) (by decide)).trans he1,
      (hfr_hdr (ASM_HDR_EMPTYG + 2) (by decide)).trans he2, (hfr_hdr (ASM_HDR_EMPTYG + 3) (by decide)).trans he3,
      fun ne₁ hne₁ => ?_⟩, hxL, hxPfp, hxvCap, hxeCap, hxwM, hxcap, hxk_pos⟩
    have hne_eq : ne₁ = { ne with xBR := Function.update ne.xBR branch xBr' } := Option.some.inj hne₁.symm
    subst hne_eq
    refine ⟨(hfr_hdr ASM_HDR_ORDH (by decide)).trans h8, (hfr_hdr ASM_HDR_CFH (by decide)).trans h9,
      (hfr_hdr ASM_HDR_TBL (by decide)).trans h10, hcfLt, htblLt, hbrLt, hvG, heG, hG_br,
      (ordStoreRep_local x.vCap x.eCap ne.ordH a.st.ord ne.xOrd mem mem' fun addr ha =>
        (hB_fr addr (hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; exact Or.inl ha))))
          (fun hb => (hd2 addr ha).2.2 branch hbr_lt hb)).symm).1 hOrdRep,
      (CF.rep_local ne.cfH _ ne.xCF mem mem' fun addr ha =>
        (hB_fr addr (hcfFt_lt addr ha) (fun hb => (hd3 addr ha).2 branch hbr_lt hb)).symm).1 hCFRep,
      fun j hj => by
        dsimp only [x'] at hj
        exact (hB_fr (ne.tbl + j) (hfoot (ne.tbl + j) (Or.inr (Or.inr (by simp only [hxne_b]; right; right; left; exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩))))
          (fun hb => hd4 (ne.tbl + j) ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hj _⟩ branch hbr_lt hb)).trans (hTbl j hj),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      by_cases hjb : j = branch
      · subst hjb; simp only [Function.update_self, x']; rw [hxvCap, hxeCap]; exact hBRRep'
      · simp only [Function.update_of_ne hjb]
        exact (BR.rep_local (ne.brH j) ⟨a.st.trees j, a.st.ord, x.vCap, x.eCap⟩ (ne.xBR j) mem mem' fun addr ha =>
          (hB_fr addr (hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j, hj, ha⟩))))
            (fun hb => hd5 j hj branch hbr_lt hjb addr ha hb)).symm).1 (hBRRep j hj)
    · intro addr ha
      refine ⟨(hd1 addr ha).1, (hd1 addr ha).2.1, (hd1 addr ha).2.2.1, fun j hj hb => ?_⟩
      by_cases hjb : j = branch
      · subst hjb; simp only [Function.update_self] at hb
        rcases hB_ft addr hb with hold | hnew; exact (hd1 addr ha).2.2.2 j hj hold; omega
      · simp only [Function.update_of_ne hjb] at hb; exact (hd1 addr ha).2.2.2 j hj hb
    · intro addr ha
      have halt := hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; exact Or.inl ha)))
      refine ⟨(hd2 addr ha).1, (hd2 addr ha).2.1, fun j hj hb => ?_⟩
      by_cases hjb : j = branch
      · subst hjb; simp only [Function.update_self] at hb
        rcases hB_ft addr hb with hold | hnew; exact (hd2 addr ha).2.2 j hj hold; omega
      · simp only [Function.update_of_ne hjb] at hb; exact (hd2 addr ha).2.2 j hj hb
    · intro addr ha
      have halt := hcfFt_lt addr ha
      refine ⟨(hd3 addr ha).1, fun j hj hb => ?_⟩
      by_cases hjb : j = branch
      · subst hjb; simp only [Function.update_self] at hb
        rcases hB_ft addr hb with hold | hnew; exact (hd3 addr ha).2 j hj hold; omega
      · simp only [Function.update_of_ne hjb] at hb; exact (hd3 addr ha).2 j hj hb
    · intro addr ha j hj hb
      have halt := hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; left; exact ha)))
      by_cases hjb : j = branch
      · subst hjb; simp only [Function.update_self] at hb
        rcases hB_ft addr hb with hold | hnew; exact hd4 addr ha j hj hold; omega
      · simp only [Function.update_of_ne hjb] at hb; exact hd4 addr ha j hj hb
    · intro j₁ h₁ j₂ h₂ hne addr ha1 ha2
      by_cases h1b : j₁ = branch
      · subst h1b; have h2b : j₂ ≠ j₁ := Ne.symm hne
        simp only [Function.update_self, Function.update_of_ne h2b] at ha1 ha2
        rcases hB_ft addr ha1 with hold | hnew
        · exact hd5 j₁ h₁ j₂ h₂ hne addr hold ha2
        · have := hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j₂, h₂, ha2⟩))); omega
      · by_cases h2b : j₂ = branch
        · subst h2b; simp only [Function.update_self, Function.update_of_ne h1b] at ha1 ha2
          rcases hB_ft addr ha2 with hold | hnew
          · exact hd5 j₁ h₁ j₂ h₂ hne addr ha1 hold
          · have := hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j₁, h₁, ha1⟩))); omega
        · simp only [Function.update_of_ne h1b, Function.update_of_ne h2b] at ha1 ha2
          exact hd5 j₁ h₁ j₂ h₂ hne addr ha1 ha2
  · refine ⟨hB_lo, hB_hi, hzB,
      fun addr ha hnf => hB_fr addr ha (fun hb => hnf (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨branch, hbr_lt, hb⟩)))),
      fun addr ha => ?_⟩
    rcases ha with h1 | h2 | h3
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr (Or.inl h2))
    · rcases h3 with h3a | h3b | h3c | ⟨j, hj, h3d⟩
      · exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; exact Or.inl h3a)))
      · exact Or.inl (Or.inr (Or.inr (by simp [hxne_b, h3b])))
      · exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; right; right; left; exact h3c)))
      · by_cases hjb : j = branch
        · subst hjb; simp only [Function.update_self] at h3d
          rcases hB_ft addr h3d with hold | hnew
          · exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j, hj, hold⟩)))
          · exact Or.inr hnew
        · simp only [Function.update_of_ne hjb] at h3d
          exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j, hj, h3d⟩)))
  · have hmem_br : branch ∈ Finset.range x.k := Finset.mem_range.mpr hbr_lt
    have hsum_new : (Finset.range x.k).sum (fun j => BR.rep.phi (ne.brH j) (Function.update ne.xBR branch xBr' j) mem') =
        BR.rep.phi (ne.brH branch) xBr' mem' +
        ((Finset.range x.k).erase branch).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) mem) := by
      rw [← Finset.add_sum_erase _ _ hmem_br, Function.update_self]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hne := Finset.ne_of_mem_erase hj
      have hjk := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
      simp only [Function.update_of_ne hne]
      exact (BR.rep_local (ne.brH j) ⟨a.st.trees j, a.st.ord, x.vCap, x.eCap⟩ (ne.xBR j) mem mem' fun addr ha =>
        (hB_fr addr (hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j, hjk, ha⟩))))
          (fun hb => hd5 j hjk branch hbr_lt hne addr ha hb)).symm).2.symm
    have hsum_old : (Finset.range x.k).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) mem) =
        BR.rep.phi (ne.brH branch) (ne.xBR branch) mem +
        ((Finset.range x.k).erase branch).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) mem) :=
      (Finset.add_sum_erase _ _ hmem_br).symm
    have hphi_new : R.phi hndl x' mem' =
        (ordStoreRep x.vCap x.eCap).phi ne.ordH ne.xOrd mem' + CF.rep.phi ne.cfH ne.xCF mem' +
        (Finset.range x.k).sum (fun j => BR.rep.phi (ne.brH j) (Function.update ne.xBR branch xBr' j) mem') := rfl
    have hphi_old : R.phi hndl x mem =
        (ordStoreRep x.vCap x.eCap).phi ne.ordH ne.xOrd mem + CF.rep.phi ne.cfH ne.xCF mem +
        (Finset.range x.k).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) mem) := by
      simp only [R, asmTopRep, asmTopPhi, hxne_b]
    have hOrdPhi : (ordStoreRep x.vCap x.eCap).phi ne.ordH ne.xOrd mem' =
        (ordStoreRep x.vCap x.eCap).phi ne.ordH ne.xOrd mem := rfl
    rw [hphi_new, hphi_old, hOrdPhi, hCFPhi', hsum_new, hsum_old]; omega


end MinCostFlow.SparseCore.Program
