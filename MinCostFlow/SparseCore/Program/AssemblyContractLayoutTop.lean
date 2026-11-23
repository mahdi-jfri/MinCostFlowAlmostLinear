module

public import MinCostFlow.SparseCore.Program.AssemblyTopOps
public import MinCostFlow.SparseCore.Program.AssemblyContractLayout
public import MinCostFlow.SparseCore.Program.AssemblyContractLayoutTopEmb

/-!
# Top-layer readout operations `2`, `3`, `5` with layout and footprint bounds (`AssemblyContractLayoutTop`)

Proves the three readout operations `asmTop_op2_runs` (`readLSF`), `asmTop_op3_runs` (`readS`), and
`asmTop_op5_runs` (`readOrd`) with both the memory-layout postconditions of
`sparseCoreOrdMachineContractKFBL` and the companion per-run `R.foot` / `o.value` clauses of
`SparseCoreReadoutFootAt`, then packages them as `asmTop_readoutFoot_implements`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

theorem asmTop_op2_runs
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    (hLay : AsmBranchReadoutLayout BR)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (G : MGraph) (k M N vCap eCap sizeParam : ℕ)
    (hfmt : fmt.limbBits = 4) (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let P := asmTopParams CFS BRS capExp limbMul
    let alloc := asmTopAlloc CFS BRS capExp sizeParam
    let D := sparseCoreOrdMachineContractKFBL fmt L depth T G k M N vCap eCap capExp P alloc
    let R := asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap
    ∀ (hndl : ℕ) (a : SparseCoreOrdAbs T) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some hndl →
      R.rep hndl a x mem → D.pre 2 a args mem →
      (∀ addr, R.foot hndl x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 2 a args mem < 2 ^ w →
      ∃ body, p.procs[asmTopOpIdx b 2]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep hndl a x' st'.mem ∧
        (let cur := heapArg args
         let br := args.getD 1 0
         let fBase := st'.mem (cur + 1)
         let stDesc := st'.mem (cur + 3)
         let Lw := st'.mem (cur + 4)
         ∃ forestVCap forestECap,
           Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
           LSFAt st'.mem cur forestVCap forestECap fmt.limbBits Lw fmt.precision a.G.E
             (T.lsfs a.st br) ∧
           fBase + dynGraphSize forestVCap forestECap ≤ cur ∧
           (∀ addr, fBase ≤ addr → addr < fBase + dynGraphSize forestVCap forestECap →
             R.foot hndl x' addr ∨ (cur ≤ addr ∧ addr < o.value)) ∧
           stDesc + 2 ≤ cur ∧
           (∀ e ∈ a.G.E, st'.mem stDesc + e * Lw + Lw ≤ cur ∧
             ∀ t < Lw, R.foot hndl x' (st'.mem stDesc + e * Lw + t) ∨
               (cur ≤ st'.mem stDesc + e * Lw + t ∧ st'.mem stDesc + e * Lw + t < o.value)) ∧
           (∀ e ∈ a.G.E, st'.mem (stDesc + 1) + e * Lw + Lw ≤ cur ∧
             ∀ t < Lw, R.foot hndl x' (st'.mem (stDesc + 1) + e * Lw + t) ∨
               (cur ≤ st'.mem (stDesc + 1) + e * Lw + t ∧ st'.mem (stDesc + 1) + e * Lw + t < o.value)) ∧
           dynGraphSize forestVCap forestECap ≤ dynGraphSize vCap (2 * (vCap + eCap + 2) ^ 2)) ∧
        R.Respects (R.foot hndl x) (heapArg args) (D.space 2 a args mem) mem o.value hndl x' st'.mem ∧
        c + R.phi hndl x' st'.mem ≤ D.cost 2 a args mem + R.phi hndl x mem := by
  intro T P alloc D R hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
  refine ⟨_, hp.at_op2, ?_⟩
  rcases hpre with ⟨hinp, h0', branch, graph, heap, rfl, hbr_lt, _, _⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst h0'
  have hheapArg : heapArg [hndl, branch, graph, heap] = heap := rfl
  rw [hheapArg] at hfoot hz hsp ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargsW
  rcases hargsW with ⟨hhndlW, hbrW, hgrW, hheapW⟩
  have hrep_orig := hrep
  rcases hrep with ⟨⟨⟨hxne, hxk, hxres, h0, h1, h2, h3, h4, h5, h6, h7,
    he0, he1, he2, he3, hnonempty⟩, hxL, hxPfp, hxvCap, hxeCap, hxwM, hxcap, _⟩, _, hCaps⟩
  obtain ⟨hinp_k, _, hinp_mn⟩ := asm_input_inv lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    (canonicalSparsifyParams impl) (dsAmortConst impl) hinp
  have hresHi_le : x.resHi ≤ heap := by have := hfoot (x.resHi - 1) (Or.inr (Or.inl ⟨by omega, by omega⟩)); omega
  have hhdr_lt : hndl + ASM_HDR_SIZE ≤ heap := by
    have := hfoot (hndl + ASM_HDR_SIZE - 1) (Or.inl ⟨by unfold ASM_HDR_SIZE; omega, by unfold ASM_HDR_SIZE; omega⟩)
    unfold ASM_HDR_SIZE at *; omega
  have hw16 : 16 < 2 ^ w := by unfold ASM_HDR_SIZE at hxres; omega
  set st0 := startState [hndl, branch, graph, heap] mem pos
  have hload4 : Runs w p ω (.assign 4 (.load (.reg 0))) st0 .normal
      { st0 with regs := Function.update st0.regs 4 (if x.ne.isSome then 1 else 0) } _ :=
    runs_assign_iff.mpr ⟨if x.ne.isSome then 1 else 0,
      Expr.eval_load_of_eq (w := w) (Expr.eval_reg_of_eq (v := hndl) (by simp [st0, startState]))
        (by simpa [st0, startState, ASM_HDR_NE] using h0), rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 4 (if x.ne.isSome then 1 else 0) }
  cases hxne_b : x.ne with
  | none =>
    have hst_em : a.st.isNonempty = false := by simpa [hxne_b] using hxne.symm
    obtain ⟨_, hE_em⟩ := asmEmpty_inv hinp hst_em
    have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 0) (.const ASM_HDR_EMPTYG))) st1 .normal
        { st1 with regs := Function.update st1.regs 5 (hndl + ASM_HDR_EMPTYG) } _ :=
      runs_assign_iff.mpr ⟨hndl + ASM_HDR_EMPTYG,
        Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st1, st0, startState]))
          (Expr.eval_const (by unfold ASM_HDR_EMPTYG; omega)) (by unfold ASM_HDR_EMPTYG ASM_HDR_SIZE at *; omega),
        rfl, rfl, rfl⟩
    set st2 : State := { st1 with regs := Function.update st1.regs 5 (hndl + ASM_HDR_EMPTYG) }
    have hst_0 : Runs w p ω (.store (.reg 3) (.reg 5)) st2 .normal
        { st2 with mem := Function.update mem heap (hndl + ASM_HDR_EMPTYG) } _ :=
      runs_store_iff.mpr ⟨heap, hndl + ASM_HDR_EMPTYG,
        Expr.eval_reg_of_eq (by simp [st2, st1, st0, startState]), Expr.eval_reg_of_eq (by simp [st2]), rfl, rfl, rfl⟩
    set st3 : State := { st2 with mem := Function.update mem heap (hndl + ASM_HDR_EMPTYG) }
    have hst_1 : Runs w p ω (.store (.bin .add (.reg 3) (.const 1)) (.reg 5)) st3 .normal
        { st3 with mem := Function.update st3.mem (heap + 1) (hndl + ASM_HDR_EMPTYG) } _ :=
      runs_store_iff.mpr ⟨heap + 1, hndl + ASM_HDR_EMPTYG,
        Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st3, st2, st1, st0, startState]))
          (Expr.eval_const (by omega)) (by change heap + 5 < 2 ^ w at hsp; omega),
        Expr.eval_reg_of_eq (by simp [st3, st2]), rfl, rfl, rfl⟩
    set st4 : State := { st3 with mem := Function.update st3.mem (heap + 1) (hndl + ASM_HDR_EMPTYG) }
    have hret : Runs w p ω (.ret (.bin .add (.reg 3) (.const 5))) st4 (.returned (heap + 5)) st4 _ :=
      runs_ret_iff.mpr ⟨heap + 5,
        Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st4, st3, st2, st1, st0, startState]))
          (Expr.eval_const (by omega)) (by change heap + 5 < 2 ^ w at hsp; omega), rfl, rfl, rfl⟩
    have helse := runs_seq_iff.mpr (Or.inr ⟨st2, _, _, ha5,
      runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hst_0,
        runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hst_1, hret, rfl⟩), rfl⟩), rfl⟩)
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopReadLSFBody bp.fReadLSF) st0 (.returned (heap + 5)) st4 cF ∧ cF ≤ 50 := by
      unfold asmTopReadLSFBody
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload4,
        runs_cond_iff.mpr ⟨0, _, Expr.eval_reg_of_eq (v := 0) (by simp [st1, hxne_b]),
          by simp only [↓reduceIte]; exact helse, rfl⟩, rfl⟩), ?_⟩
      simp only [Expr.size]; omega
    have hfr4 : ∀ addr < heap, st4.mem addr = mem addr := fun addr ha => by
      dsimp only [st4, st3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hrep' := (asmTopRepEq_local CF.rep_local BR.rep_local hndl a x mem st4.mem
      (fun addr ha => (hfr4 addr (hfoot addr ha)).symm)).1 hrep_orig
    have h1eq : st4.mem (heap + 1) = hndl + ASM_HDR_EMPTYG := by simp [st4]
    have h3z : st4.mem (heap + 3) = 0 := by
      dsimp only [st4, st3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hz (heap + 3) (by omega)
    have h4z : st4.mem (heap + 4) = 0 := by
      dsimp only [st4, st3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hz (heap + 4) (by omega)
    have hS_em : T.S a.st branch = emptyGraph := by
      change (if a.st.isNonempty then _ else emptyGraph) = _; simp [hst_em]
    refine ⟨.returned (heap + 5), st4, cF, x, hfull, hrep', ?_, ?_, ?_⟩
    · refine ⟨0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h4z]; exact Nat.zero_le _
      · have hlsf_em : T.lsfs a.st branch = emptyLSF := by
          change (if a.st.isNonempty then _ else emptyLSF) = _; simp [hst_em]
        change LSFAt st4.mem heap 0 0 fmt.limbBits (st4.mem (heap + 4)) fmt.precision a.G.E (T.lsfs a.st branch)
        rw [hlsf_em, hE_em]
        refine lsfAt_emptyLSF (dynGraphAt_emptyGraph
          ((hfr4 _ (by unfold ASM_HDR_EMPTYG ASM_HDR_SIZE at *; omega)).trans he0)
          ((hfr4 _ (by unfold ASM_HDR_EMPTYG ASM_HDR_SIZE at *; omega)).trans he1)
          ((hfr4 _ (by unfold ASM_HDR_EMPTYG ASM_HDR_SIZE at *; omega)).trans he2)
          ((hfr4 _ (by unfold ASM_HDR_EMPTYG ASM_HDR_SIZE at *; omega)).trans he3))
          (by dsimp only [st4, st3]; rw [Function.update_of_ne (by omega), Function.update_self]) h1eq
      · rw [h1eq]; unfold dynGraphSize ASM_HDR_EMPTYG ASM_HDR_SIZE at *; omega
      · intro addr ha1 ha2
        change st4.mem (heap + 1) ≤ addr at ha1
        change addr < st4.mem (heap + 1) + dynGraphSize 0 0 at ha2
        rw [h1eq] at ha1 ha2
        exact Or.inl (Or.inl ⟨by unfold ASM_HDR_EMPTYG at *; omega,
          by unfold dynGraphSize ASM_HDR_EMPTYG ASM_HDR_SIZE at *; omega⟩)
      · rw [h3z]; unfold ASM_HDR_SIZE at *; omega
      · intro e he; rw [hE_em] at he; cases he
      · intro e he; rw [hE_em] at he; cases he
      · unfold dynGraphSize; omega
    · refine ⟨by simp [Outcome.value], by change heap + 5 ≤ heap + 5; exact le_rfl, fun addr ha => by
        simp only [Outcome.value] at ha
        dsimp only [st4, st3]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hz addr (by omega), fun addr ha _ => hfr4 addr ha, fun _ ha => Or.inl ha⟩
    · have hphi0 : R.phi hndl x st4.mem = 0 ∧ R.phi hndl x mem = 0 := by simp [R, asmTopRepEq, asmTopPhi, hxne_b]
      rw [hphi0.1, hphi0.2]; change cF + 0 ≤ P.readout + 0; simp only [P, asmTopParams]; omega
  | some ne =>
    have hst_ne : a.st.isNonempty = true := by simpa [hxne_b] using hxne.symm
    obtain ⟨_, _, h10, _, htblLt, hbrLt, _, _, hG_br, _, _, hTbl, hBRRep, _, _, _, _, _⟩ := hnonempty ne hxne_b
    have hload5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL)))) st1 .normal
        { st1 with regs := Function.update st1.regs 5 ne.tbl } _ :=
      runs_assign_iff.mpr ⟨ne.tbl, Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st1, st0, startState]))
          (Expr.eval_const (by unfold ASM_HDR_TBL; omega)) (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)) h10,
        rfl, rfl, rfl⟩
    set st2 : State := { st1 with regs := Function.update st1.regs 5 ne.tbl }
    have hload6 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 5) (.reg 1)))) st2 .normal
        { st2 with regs := Function.update st2.regs 6 (ne.brH branch) } _ :=
      runs_assign_iff.mpr ⟨ne.brH branch, Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := ne.tbl) (by simp [st2]))
          (Expr.eval_reg_of_eq (v := branch) (by simp [st2, st1, st0, startState])) (by omega))
        (hTbl branch (by omega)), rfl, rfl, rfl⟩
    set st3 : State := { st2 with regs := Function.update st2.regs 6 (ne.brH branch) }
    obtain ⟨bodyBR, hbodyBR, oBR, stBR, cBR, xBr', hrunBR, hBRRep', hLSF', hRespBR, hCostBR⟩ :=
      hLay.readLSF_layout_runs (ne.brH branch) heap M N vCap eCap (a.st.trees branch) a.st.ord (ne.xBR branch)
        st3.mem st3.pos ω hfmt (hinp_mn branch).1 (hinp_mn branch).2.1 hcap
        (by rw [← hxvCap, ← hxeCap]; exact hBRRep branch (by omega))
        (fun addr ha => hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨branch, by omega, ha⟩))))
        (by have := hbrLt branch (by omega); omega) hheapW hz (by change heap + 5 < 2 ^ w at hsp; exact hsp)
    have hcallBR : Runs w p ω (.call 7 bp.fReadLSF [.reg 6, .reg 3]) st3 .normal
        { stBR with regs := Function.update st3.regs 7 oBR.value }
        (argsSize [.reg 6, .reg 3] + cBR + 1) := by
      refine (runs_call_iff (r := 7) (f := bp.fReadLSF) (st := st3) (o := .normal)
        (st' := { stBR with regs := Function.update st3.regs 7 oBR.value })).mpr
        ⟨[ne.brH branch, heap], bodyBR, oBR, stBR, cBR, ?_, hbodyBR, hrunBR, rfl, rfl, rfl⟩
      simp [evalArgs, Expr.eval, st3, st2, st1, st0, startState]
    set st4 : State := { stBR with regs := Function.update st3.regs 7 oBR.value }
    have hret : Runs w p ω (.ret (.reg 7)) st4 (.returned oBR.value) st4 _ :=
      runs_ret_iff.mpr ⟨oBR.value, Expr.eval_reg_of_eq (by simp [st4]), rfl, rfl, rfl⟩
    have hthen := runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hload5,
      runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hload6,
        runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hcallBR, hret, rfl⟩), rfl⟩), rfl⟩)
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopReadLSFBody bp.fReadLSF) st0 (.returned oBR.value) st4 cF ∧ cF ≤ cBR + 50 := by
      unfold asmTopReadLSFBody
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload4,
        runs_cond_iff.mpr ⟨1, _, Expr.eval_reg_of_eq (v := 1) (by simp [st1, hxne_b]),
          by simp only [one_ne_zero, ↓reduceIte]; exact hthen, rfl⟩, rfl⟩), ?_⟩
      simp only [argsSize_cons, argsSize_nil, Expr.size]; omega
    obtain ⟨hrep', hresp', hphi'⟩ := asmTop_branch_readout_frame hxne_b (by omega) hrep_orig.1 hfoot hBRRep' hRespBR
    have hlsf_eq : T.lsfs a.st branch = (a.st.trees branch).cs.lsf := by
      change (if a.st.isNonempty then _ else emptyLSF) = _; simp [hst_ne]
    have hS_eq : T.S a.st branch = (a.st.trees branch).S_cur := by
      change (if a.st.isNonempty then _ else emptyGraph) = _; simp [hst_ne]
    obtain ⟨fv, fe, hLw, hLSF, hfEnd, hfIn, hStDesc, hNum, hDen, hFCap⟩ := hLSF'
    refine ⟨.returned oBR.value, st4, cF, _, hfull,
      ⟨hrep', fun h => by simp at h, fun ne₁ hne₁ => by cases Option.some.inj hne₁.symm; exact hCaps ne hxne_b⟩, ?_, hresp', ?_⟩
    · refine ⟨fv, fe, hLw, ?_, hfEnd, ?_, hStDesc, ?_, ?_, hFCap⟩
      · change LSFAt stBR.mem heap fv fe fmt.limbBits (stBR.mem (heap + 4)) fmt.precision a.G.E (T.lsfs a.st branch)
        rw [hlsf_eq, ← (hG_br branch (by omega)).1]; exact hLSF
      · intro addr ha1 ha2
        rcases hfIn addr ha1 ha2 with hbf | hnew
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨branch, by dsimp only; omega, by simpa using hbf⟩)))))
        · exact Or.inr hnew
      · intro e he
        rw [← (hG_br branch (by omega)).1] at he
        obtain ⟨hEnd, hFt⟩ := hNum e he
        refine ⟨hEnd, fun t ht => ?_⟩
        rcases hFt t ht with hbf | hnew
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨branch, by dsimp only; omega, by simpa using hbf⟩)))))
        · exact Or.inr hnew
      · intro e he
        rw [← (hG_br branch (by omega)).1] at he
        obtain ⟨hEnd, hFt⟩ := hDen e he
        refine ⟨hEnd, fun t ht => ?_⟩
        rcases hFt t ht with hbf | hnew
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨branch, by dsimp only; omega, by simpa using hbf⟩)))))
        · exact Or.inr hnew
    · change cF + R.phi hndl _ stBR.mem ≤ P.readout + R.phi hndl x mem
      change cBR + BR.rep.phi (ne.brH branch) xBr' stBR.mem ≤ BRS.readout capExp + BR.rep.phi (ne.brH branch) (ne.xBR branch) mem at hCostBR
      change R.phi hndl _ stBR.mem + BR.rep.phi (ne.brH branch) (ne.xBR branch) mem =
        R.phi hndl x mem + BR.rep.phi (ne.brH branch) xBr' stBR.mem at hphi'
      simp only [P, asmTopParams]; omega

theorem asmTop_op3_runs
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    (hLay : AsmBranchReadoutLayout BR)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (G : MGraph) (k M N vCap eCap sizeParam : ℕ) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let P := asmTopParams CFS BRS capExp limbMul
    let alloc := asmTopAlloc CFS BRS capExp sizeParam
    let D := sparseCoreOrdMachineContractKFBL fmt L depth T G k M N vCap eCap capExp P alloc
    let R := asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap
    ∀ (hndl : ℕ) (a : SparseCoreOrdAbs T) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some hndl →
      R.rep hndl a x mem → D.pre 3 a args mem →
      (∀ addr, R.foot hndl x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 3 a args mem < 2 ^ w →
      ∃ body, p.procs[asmTopOpIdx b 3]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep hndl a x' st'.mem ∧
        (let cur := heapArg args
         let br := args.getD 1 0
         ∃ graphVCap graphECap,
           DynGraphAt st'.mem (st'.mem cur) graphVCap graphECap (T.S a.st br) ∧
           graphVCap = vCap ∧ graphECap = eCap ∧
           st'.mem cur + dynGraphSize graphVCap graphECap ≤ cur ∧
           (∀ addr, st'.mem cur ≤ addr → addr < st'.mem cur + dynGraphSize graphVCap graphECap →
             R.foot hndl x' addr ∨ (cur ≤ addr ∧ addr < o.value))) ∧
        R.Respects (R.foot hndl x) (heapArg args) (D.space 3 a args mem) mem o.value hndl x' st'.mem ∧
        c + R.phi hndl x' st'.mem ≤ D.cost 3 a args mem + R.phi hndl x mem := by
  intro T P alloc D R hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
  refine ⟨_, hp.at_op3, ?_⟩
  rcases hpre with ⟨hinp, h0', branch, heap, rfl, hbr_lt⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst h0'
  have hheapArg : heapArg [hndl, branch, heap] = heap := rfl
  rw [hheapArg] at hfoot hz hsp ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargsW
  rcases hargsW with ⟨hhndlW, hbrW, hheapW⟩
  have hrep_orig := hrep
  rcases hrep with ⟨⟨⟨hxne, hxk, hxres, h0, _, _, _, _, _, _, _, he0, he1, he2, he3, hnonempty⟩, _, _, hxvCap, hxeCap, _, _, _⟩, hEmpty, hCaps⟩
  obtain ⟨hinp_k, _, _⟩ := asm_input_inv lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    (canonicalSparsifyParams impl) (dsAmortConst impl) hinp
  have hresHi_le : x.resHi ≤ heap := by have := hfoot (x.resHi - 1) (Or.inr (Or.inl ⟨by omega, by omega⟩)); omega
  have hhdr_lt : hndl + ASM_HDR_SIZE ≤ heap := by
    have := hfoot (hndl + ASM_HDR_SIZE - 1) (Or.inl ⟨by unfold ASM_HDR_SIZE; omega, by unfold ASM_HDR_SIZE; omega⟩)
    unfold ASM_HDR_SIZE at *; omega
  have hw16 : 16 < 2 ^ w := by unfold ASM_HDR_SIZE at hxres; omega
  set st0 := startState [hndl, branch, heap] mem pos
  have hload3 : Runs w p ω (.assign 3 (.load (.reg 0))) st0 .normal
      { st0 with regs := Function.update st0.regs 3 (if x.ne.isSome then 1 else 0) } _ :=
    runs_assign_iff.mpr ⟨if x.ne.isSome then 1 else 0,
      Expr.eval_load_of_eq (w := w) (Expr.eval_reg_of_eq (v := hndl) (by simp [st0, startState]))
        (by simpa [st0, startState, ASM_HDR_NE] using h0), rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 3 (if x.ne.isSome then 1 else 0) }
  cases hxne_b : x.ne with
  | none =>
    have hst_em : a.st.isNonempty = false := by simpa [hxne_b] using hxne.symm
    obtain ⟨hresLo_eq, hdg_le_resHi, hDG_orig⟩ := hEmpty hxne_b
    have hst_0 : Runs w p ω (.store (.reg 2) (.bin .add (.reg 0) (.const ASM_HDR_SIZE))) st1 .normal
        { st1 with mem := Function.update mem heap (hndl + ASM_HDR_SIZE) } _ :=
      runs_store_iff.mpr ⟨heap, hndl + ASM_HDR_SIZE,
        Expr.eval_reg_of_eq (by simp [st1, st0, startState]),
        Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st1, st0, startState]))
          (Expr.eval_const (by omega)) (by omega),
        rfl, rfl, rfl⟩
    set st2 : State := { st1 with mem := Function.update mem heap (hndl + ASM_HDR_SIZE) }
    have hret : Runs w p ω (.ret (.bin .add (.reg 2) (.const 1))) st2 (.returned (heap + 1)) st2 _ :=
      runs_ret_iff.mpr ⟨heap + 1,
        Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st2, st1, st0, startState]))
          (Expr.eval_const (by omega)) (by change heap + 1 < 2 ^ w at hsp; exact hsp), rfl, rfl, rfl⟩
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopReadSBody bp.fReadS) st0 (.returned (heap + 1)) st2 cF ∧ cF ≤ 50 := by
      unfold asmTopReadSBody
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload3,
        runs_cond_iff.mpr ⟨0, _, Expr.eval_reg_of_eq (v := 0) (by simp [st1, hxne_b]),
          by simp only [↓reduceIte]; exact runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hst_0, hret, rfl⟩), rfl⟩, rfl⟩), ?_⟩
      simp only [Expr.size]; omega
    have hfr2 : ∀ addr < heap, st2.mem addr = mem addr := fun addr ha => by
      dsimp only [st2]; exact Function.update_of_ne (by omega) _ _
    have hrep' := (asmTopRepEq_local CF.rep_local BR.rep_local hndl a x mem st2.mem
      (fun addr ha => (hfr2 addr (hfoot addr ha)).symm)).1 hrep_orig
    have hS_em : T.S a.st branch = emptyGraph := by
      change (if a.st.isNonempty then _ else emptyGraph) = _; simp [hst_em]
    have hmeq : st2.mem heap = hndl + ASM_HDR_SIZE := by simp [st2]
    have hDG_em : DynGraphAt st2.mem (st2.mem heap) vCap eCap (T.S a.st branch) := by
      rw [hS_em, hmeq, ← hxvCap, ← hxeCap]
      exact dynGraphAt_of_agree hDG_orig fun addr ha1 ha2 => hfr2 addr (by omega)
    refine ⟨.returned (heap + 1), st2, cF, x, hfull, hrep', ?_,
      ⟨by simp [Outcome.value], by change heap + 1 ≤ heap + 1; exact le_rfl,
        fun addr ha => by simp only [Outcome.value] at ha; dsimp only [st2]; rw [Function.update_of_ne (by omega)]; exact hz addr (by omega),
        fun addr ha _ => hfr2 addr ha, fun _ ha => Or.inl ha⟩, ?_⟩
    · refine ⟨vCap, eCap, hDG_em, rfl, rfl, ?_, ?_⟩
      · rw [hmeq, ← hxvCap, ← hxeCap]; omega
      · intro addr ha1 ha2
        change st2.mem heap ≤ addr at ha1
        change addr < st2.mem heap + dynGraphSize vCap eCap at ha2
        rw [hmeq] at ha1 ha2
        rw [hxvCap, hxeCap] at hdg_le_resHi
        exact Or.inl (Or.inr (Or.inl ⟨by omega, by omega⟩))
    · have hphi0 : R.phi hndl x st2.mem = 0 ∧ R.phi hndl x mem = 0 := by simp [R, asmTopRepEq, asmTopPhi, hxne_b]
      rw [hphi0.1, hphi0.2]; change cF + 0 ≤ P.readout + 0; simp only [P, asmTopParams]; omega
  | some ne =>
    have hst_ne : a.st.isNonempty = true := by simpa [hxne_b] using hxne.symm
    obtain ⟨_, _, h10, _, htblLt, hbrLt, _, _, _, _, _, hTbl, hBRRep, _, _, _, _, _⟩ := hnonempty ne hxne_b
    have hload4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL)))) st1 .normal
        { st1 with regs := Function.update st1.regs 4 ne.tbl } _ :=
      runs_assign_iff.mpr ⟨ne.tbl, Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st1, st0, startState]))
          (Expr.eval_const (by unfold ASM_HDR_TBL; omega)) (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)) h10,
        rfl, rfl, rfl⟩
    set st2 : State := { st1 with regs := Function.update st1.regs 4 ne.tbl }
    have hload5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 4) (.reg 1)))) st2 .normal
        { st2 with regs := Function.update st2.regs 5 (ne.brH branch) } _ :=
      runs_assign_iff.mpr ⟨ne.brH branch, Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := ne.tbl) (by simp [st2]))
          (Expr.eval_reg_of_eq (v := branch) (by simp [st2, st1, st0, startState])) (by omega))
        (hTbl branch (by omega)), rfl, rfl, rfl⟩
    set st3 : State := { st2 with regs := Function.update st2.regs 5 (ne.brH branch) }
    obtain ⟨bodyBR, hbodyBR, oBR, stBR, cBR, xBr', hrunBR, hBRRep', hS', hRespBR, hCostBR⟩ :=
      hLay.readS_layout_runs (ne.brH branch) heap vCap eCap (a.st.trees branch) a.st.ord (ne.xBR branch)
        st3.mem st3.pos ω (by rw [← hxvCap, ← hxeCap]; exact hBRRep branch (by omega))
        (fun addr ha => hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨branch, by omega, ha⟩))))
        (by have := hbrLt branch (by omega); omega) hheapW hz (by change heap + 1 < 2 ^ w at hsp; exact hsp)
    have hcallBR : Runs w p ω (.call 6 bp.fReadS [.reg 5, .reg 2]) st3 .normal
        { stBR with regs := Function.update st3.regs 6 oBR.value }
        (argsSize [.reg 5, .reg 2] + cBR + 1) := by
      refine (runs_call_iff (r := 6) (f := bp.fReadS) (st := st3) (o := .normal)
        (st' := { stBR with regs := Function.update st3.regs 6 oBR.value })).mpr
        ⟨[ne.brH branch, heap], bodyBR, oBR, stBR, cBR, ?_, hbodyBR, hrunBR, rfl, rfl, rfl⟩
      simp [evalArgs, Expr.eval, st3, st2, st1, st0, startState]
    set st4 : State := { stBR with regs := Function.update st3.regs 6 oBR.value }
    have hret : Runs w p ω (.ret (.reg 6)) st4 (.returned oBR.value) st4 _ :=
      runs_ret_iff.mpr ⟨oBR.value, Expr.eval_reg_of_eq (by simp [st4]), rfl, rfl, rfl⟩
    have hthen := runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hload4,
      runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hload5,
        runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hcallBR, hret, rfl⟩), rfl⟩), rfl⟩)
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopReadSBody bp.fReadS) st0 (.returned oBR.value) st4 cF ∧ cF ≤ cBR + 50 := by
      unfold asmTopReadSBody
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload3,
        runs_cond_iff.mpr ⟨1, _, Expr.eval_reg_of_eq (v := 1) (by simp [st1, hxne_b]),
          by simp only [one_ne_zero, ↓reduceIte]; exact hthen, rfl⟩, rfl⟩), ?_⟩
      simp only [argsSize_cons, argsSize_nil, Expr.size]; omega
    obtain ⟨hrep', hresp', hphi'⟩ := asmTop_branch_readout_frame hxne_b (by omega) hrep_orig.1 hfoot hBRRep' hRespBR
    have hS_eq : T.S a.st branch = (a.st.trees branch).S_cur := by
      change (if a.st.isNonempty then _ else emptyGraph) = _; simp [hst_ne]
    obtain ⟨gv, ge, hDG, hgv, hge, hEnd, hIn⟩ := hS'
    refine ⟨.returned oBR.value, st4, cF, _, hfull,
      ⟨hrep', fun h => by simp at h, fun ne₁ hne₁ => by cases Option.some.inj hne₁.symm; exact hCaps ne hxne_b⟩, ?_, hresp', ?_⟩
    · refine ⟨gv, ge, ?_, hgv, hge, hEnd, ?_⟩
      · change DynGraphAt stBR.mem (stBR.mem heap) gv ge (T.S a.st branch)
        rw [hS_eq]; exact hDG
      · intro addr ha1 ha2
        rcases hIn addr ha1 ha2 with hbf | hnew
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨branch, by dsimp only; omega, by simpa using hbf⟩)))))
        · exact Or.inr hnew
    · change cF + R.phi hndl _ stBR.mem ≤ P.readout + R.phi hndl x mem
      change cBR + BR.rep.phi (ne.brH branch) xBr' stBR.mem ≤ BRS.readout capExp + BR.rep.phi (ne.brH branch) (ne.xBR branch) mem at hCostBR
      change R.phi hndl _ stBR.mem + BR.rep.phi (ne.brH branch) (ne.xBR branch) mem =
        R.phi hndl x mem + BR.rep.phi (ne.brH branch) xBr' stBR.mem at hphi'
      simp only [P, asmTopParams]; omega

theorem asmTop_op5_runs
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    (hLay : AsmBranchReadoutLayout BR)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (G : MGraph) (k M N vCap eCap sizeParam : ℕ)
    (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let P := asmTopParams CFS BRS capExp limbMul
    let alloc := asmTopAlloc CFS BRS capExp sizeParam
    let D := sparseCoreOrdMachineContractKFBL fmt L depth T G k M N vCap eCap capExp P alloc
    let R := asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap
    ∀ (hndl : ℕ) (a : SparseCoreOrdAbs T) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some hndl →
      R.rep hndl a x mem → D.pre 5 a args mem →
      (∀ addr, R.foot hndl x addr → addr < heapArg args) →
      ZeroFrom mem (heapArg args) → heapArg args + D.space 5 a args mem < 2 ^ w →
      ∃ body, p.procs[asmTopOpIdx b 5]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState args mem pos) o st' c ∧
        R.rep hndl a x' st'.mem ∧
        (let cur := heapArg args
         let br := args.getD 1 0
         ∃ words,
           OrdListAt st'.mem (st'.mem cur) (T.rot a.st br) words ∧
           words ≤ ordRotWords a br ∧
           st'.mem cur = cur + 1 ∧
           st'.mem cur + words ≤ o.value ∧
           (∀ j < words, st'.mem (st'.mem cur + j) < 2 ^ w)) ∧
        R.Respects (R.foot hndl x) (heapArg args) (D.space 5 a args mem) mem o.value hndl x' st'.mem ∧
        c + R.phi hndl x' st'.mem ≤ D.cost 5 a args mem + R.phi hndl x mem := by
  intro T P alloc D R hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
  refine ⟨_, hp.at_op5, ?_⟩
  rcases hpre with ⟨hinp, h0', branch, heap, rfl, hbr_lt⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst h0'
  have hheapArg : heapArg [hndl, branch, heap] = heap := rfl
  rw [hheapArg] at hfoot hz hsp ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargsW
  rcases hargsW with ⟨hhndlW, hbrW, hheapW⟩
  have hrep_orig := hrep
  rcases hrep with ⟨⟨⟨hxne, hxk, hxres, h0, _, _, _, _, _, _, _, _, _, _, _, hnonempty⟩, _, _, hxvCap, hxeCap, _, _, _⟩, _, hCaps⟩
  obtain ⟨hinp_k, _, hinp_mn⟩ := asm_input_inv lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    (canonicalSparsifyParams impl) (dsAmortConst impl) hinp
  have hresHi_le : x.resHi ≤ heap := by have := hfoot (x.resHi - 1) (Or.inr (Or.inl ⟨by omega, by omega⟩)); omega
  have hhdr_lt : hndl + ASM_HDR_SIZE ≤ heap := by
    have := hfoot (hndl + ASM_HDR_SIZE - 1) (Or.inl ⟨by unfold ASM_HDR_SIZE; omega, by unfold ASM_HDR_SIZE; omega⟩)
    unfold ASM_HDR_SIZE at *; omega
  have hw16 : 16 < 2 ^ w := by unfold ASM_HDR_SIZE at hxres; omega
  have hlg_pos : 1 ≤ bundleLogFactor M N := le_trans (by omega) (logStep_le_bundleLogFactor M N)
  set st0 := startState [hndl, branch, heap] mem pos
  have hload3 : Runs w p ω (.assign 3 (.load (.reg 0))) st0 .normal
      { st0 with regs := Function.update st0.regs 3 (if x.ne.isSome then 1 else 0) } _ :=
    runs_assign_iff.mpr ⟨if x.ne.isSome then 1 else 0,
      Expr.eval_load_of_eq (w := w) (Expr.eval_reg_of_eq (v := hndl) (by simp [st0, startState]))
        (by simpa [st0, startState, ASM_HDR_NE] using h0), rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 3 (if x.ne.isSome then 1 else 0) }
  cases hxne_b : x.ne with
  | none =>
    have hst_em : a.st.isNonempty = false := by simpa [hxne_b] using hxne.symm
    have hrotW : ordRotWords a branch = 1 := by
      unfold ordRotWords ordWordsOn
      have hS_em : T.S a.st branch = emptyGraph := by
        change (if a.st.isNonempty then _ else emptyGraph) = _; simp [hst_em]
      rw [hS_em]; simp [emptyGraph]
    have hsp2 : heap + 2 < 2 ^ w := by
      change heap + (1 + ordRotWords a branch) < 2 ^ w at hsp; rw [hrotW] at hsp; exact hsp
    have hst_0 : Runs w p ω (.store (.reg 2) (.bin .add (.reg 2) (.const 1))) st1 .normal
        { st1 with mem := Function.update mem heap (heap + 1) } _ :=
      runs_store_iff.mpr ⟨heap, heap + 1, Expr.eval_reg_of_eq (by simp [st1, st0, startState]),
        Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st1, st0, startState]))
          (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
    set st2 : State := { st1 with mem := Function.update mem heap (heap + 1) }
    have hret : Runs w p ω (.ret (.bin .add (.reg 2) (.const 2))) st2 (.returned (heap + 2)) st2 _ :=
      runs_ret_iff.mpr ⟨heap + 2,
        Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st2, st1, st0, startState]))
          (Expr.eval_const (by omega)) hsp2, rfl, rfl, rfl⟩
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopReadOrdBody bp.fReadOrd) st0 (.returned (heap + 2)) st2 cF ∧ cF ≤ 50 := by
      unfold asmTopReadOrdBody
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload3,
        runs_cond_iff.mpr ⟨0, _, Expr.eval_reg_of_eq (v := 0) (by simp [st1, hxne_b]),
          by simp only [↓reduceIte]; exact runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hst_0, hret, rfl⟩), rfl⟩, rfl⟩), ?_⟩
      simp only [Expr.size]; omega
    have hfr2 : ∀ addr < heap, st2.mem addr = mem addr := fun addr ha => by
      dsimp only [st2]; exact Function.update_of_ne (by omega) _ _
    have hrep' := (asmTopRepEq_local CF.rep_local BR.rep_local hndl a x mem st2.mem
      (fun addr ha => (hfr2 addr (hfoot addr ha)).symm)).1 hrep_orig
    have hrot_em : T.rot a.st branch = fun _ => [] := by
      funext v; change (if a.st.isNonempty then _ else fun _ => []) v = _; simp [hst_em]
    have hmeq : st2.mem heap = heap + 1 := by simp [st2]
    have hm1z : st2.mem (heap + 1) = 0 := by
      dsimp only [st2]; rw [Function.update_of_ne (by omega)]; exact hz (heap + 1) (by omega)
    have hOrd_em : OrdListAt st2.mem (st2.mem heap) (T.rot a.st branch) 1 := by
      rw [hrot_em, hmeq]; exact ordListAt_empty hm1z
    refine ⟨.returned (heap + 2), st2, cF, x, hfull, hrep', ?_,
      ⟨by simp [Outcome.value], by change heap + 2 ≤ heap + (1 + ordRotWords a branch); rw [hrotW],
        fun addr ha => by simp only [Outcome.value] at ha; dsimp only [st2]; rw [Function.update_of_ne (by omega)]; exact hz addr (by omega),
        fun addr ha _ => hfr2 addr ha, fun _ ha => Or.inl ha⟩, ?_⟩
    · refine ⟨1, hOrd_em, by change 1 ≤ ordRotWords a branch; rw [hrotW], hmeq,
        by simp [Outcome.value, hmeq], fun j hj => ?_⟩
      have hj0 : j = 0 := by omega
      subst hj0
      rw [hmeq, Nat.add_zero, hm1z]; omega
    · have hphi0 : R.phi hndl x st2.mem = 0 ∧ R.phi hndl x mem = 0 := by simp [R, asmTopRepEq, asmTopPhi, hxne_b]
      rw [hphi0.1, hphi0.2]
      change cF + 0 ≤ P.mul * (ordRotWords a branch + 1) * bundleLogFactor M N + 0
      have hmul : 400 ≤ P.mul := by simp [P, asmTopParams]
      have h1 : 400 * 1 ≤ P.mul * (ordRotWords a branch + 1) * bundleLogFactor M N :=
        le_trans (Nat.mul_le_mul hmul (by omega)) (Nat.le_mul_of_pos_right _ hlg_pos)
      omega
  | some ne =>
    have hst_ne : a.st.isNonempty = true := by simpa [hxne_b] using hxne.symm
    obtain ⟨_, _, h10, _, htblLt, hbrLt, _, _, _, _, _, hTbl, hBRRep, _, _, _, _, _⟩ := hnonempty ne hxne_b
    have hrotW_eq : ordRotWords a branch = ordWordsOn (a.st.trees branch).S_cur.V ((a.st.trees branch).outOrder a.st.ord) := by
      unfold ordRotWords
      have hS : T.S a.st branch = (a.st.trees branch).S_cur := by change (if a.st.isNonempty then _ else emptyGraph) = _; simp [hst_ne]
      have hr : T.rot a.st branch = (a.st.trees branch).outOrder a.st.ord := by change (if a.st.isNonempty then _ else fun _ => []) = _; simp [hst_ne]
      rw [hS, hr]
    have hload4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL)))) st1 .normal
        { st1 with regs := Function.update st1.regs 4 ne.tbl } _ :=
      runs_assign_iff.mpr ⟨ne.tbl, Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st1, st0, startState]))
          (Expr.eval_const (by unfold ASM_HDR_TBL; omega)) (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)) h10,
        rfl, rfl, rfl⟩
    set st2 : State := { st1 with regs := Function.update st1.regs 4 ne.tbl }
    have hload5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 4) (.reg 1)))) st2 .normal
        { st2 with regs := Function.update st2.regs 5 (ne.brH branch) } _ :=
      runs_assign_iff.mpr ⟨ne.brH branch, Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := ne.tbl) (by simp [st2]))
          (Expr.eval_reg_of_eq (v := branch) (by simp [st2, st1, st0, startState])) (by omega))
        (hTbl branch (by omega)), rfl, rfl, rfl⟩
    set st3 : State := { st2 with regs := Function.update st2.regs 5 (ne.brH branch) }
    obtain ⟨bodyBR, hbodyBR, oBR, stBR, cBR, xBr', hrunBR, hBRRep', hOrd', hRespBR, hCostBR⟩ :=
      hLay.readOrd_layout_runs (ne.brH branch) heap M N vCap eCap (a.st.trees branch) a.st.ord (ne.xBR branch)
        st3.mem st3.pos ω (hinp_mn branch).1 (hinp_mn branch).2.1 hcap
        (by rw [← hxvCap, ← hxeCap]; exact hBRRep branch (by omega))
        (fun addr ha => hfoot addr (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨branch, by omega, ha⟩))))
        (by have := hbrLt branch (by omega); omega) hheapW hz
        (by change heap + (1 + ordRotWords a branch) < 2 ^ w at hsp; rw [← hrotW_eq]; exact hsp)
    have hcallBR : Runs w p ω (.call 6 bp.fReadOrd [.reg 5, .reg 2]) st3 .normal
        { stBR with regs := Function.update st3.regs 6 oBR.value }
        (argsSize [.reg 5, .reg 2] + cBR + 1) := by
      refine (runs_call_iff (r := 6) (f := bp.fReadOrd) (st := st3) (o := .normal)
        (st' := { stBR with regs := Function.update st3.regs 6 oBR.value })).mpr
        ⟨[ne.brH branch, heap], bodyBR, oBR, stBR, cBR, ?_, hbodyBR, hrunBR, rfl, rfl, rfl⟩
      simp [evalArgs, Expr.eval, st3, st2, st1, st0, startState]
    set st4 : State := { stBR with regs := Function.update st3.regs 6 oBR.value }
    have hret : Runs w p ω (.ret (.reg 6)) st4 (.returned oBR.value) st4 _ :=
      runs_ret_iff.mpr ⟨oBR.value, Expr.eval_reg_of_eq (by simp [st4]), rfl, rfl, rfl⟩
    have hthen := runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hload4,
      runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hload5,
        runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hcallBR, hret, rfl⟩), rfl⟩), rfl⟩)
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopReadOrdBody bp.fReadOrd) st0 (.returned oBR.value) st4 cF ∧ cF ≤ cBR + 50 := by
      unfold asmTopReadOrdBody
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload3,
        runs_cond_iff.mpr ⟨1, _, Expr.eval_reg_of_eq (v := 1) (by simp [st1, hxne_b]),
          by simp only [one_ne_zero, ↓reduceIte]; exact hthen, rfl⟩, rfl⟩), ?_⟩
      simp only [argsSize_cons, argsSize_nil, Expr.size]; omega
    obtain ⟨hrep', hresp', hphi'⟩ := asmTop_branch_readout_frame hxne_b (by omega) hrep_orig.1 hfoot hBRRep' hRespBR
    have hr_eq : T.rot a.st branch = (a.st.trees branch).outOrder a.st.ord := by
      change (if a.st.isNonempty then _ else fun _ => []) = _; simp [hst_ne]
    obtain ⟨words, hOrd, hLe, hPtr, hEnd, hW⟩ := hOrd'
    refine ⟨.returned oBR.value, st4, cF, _, hfull,
      ⟨hrep', fun h => by simp at h, fun ne₁ hne₁ => by cases Option.some.inj hne₁.symm; exact hCaps ne hxne_b⟩,
      ⟨words, by change OrdListAt stBR.mem (stBR.mem heap) (T.rot a.st branch) words; rw [hr_eq]; exact hOrd,
        by change words ≤ ordRotWords a branch; rw [hrotW_eq]; exact hLe, hPtr, hEnd, hW⟩,
      by change R.Respects (R.foot hndl x) heap (1 + ordRotWords a branch) mem oBR.value hndl _ stBR.mem
         rw [hrotW_eq]; exact hresp', ?_⟩
    change cF + R.phi hndl _ stBR.mem ≤ P.mul * (ordRotWords a branch + 1) * bundleLogFactor M N + R.phi hndl x mem
    change cBR + BR.rep.phi (ne.brH branch) xBr' stBR.mem ≤ _ + BR.rep.phi (ne.brH branch) (ne.xBR branch) mem at hCostBR
    change R.phi hndl _ stBR.mem + BR.rep.phi (ne.brH branch) (ne.xBR branch) mem =
      R.phi hndl x mem + BR.rep.phi (ne.brH branch) xBr' stBR.mem at hphi'
    rw [hrotW_eq]
    have hmul : (BRS.mul capExp limbMul + 400) * (ordWordsOn (a.st.trees branch).S_cur.V ((a.st.trees branch).outOrder a.st.ord) + 1) *
        bundleLogFactor M N ≤ P.mul * (ordWordsOn (a.st.trees branch).S_cur.V ((a.st.trees branch).outOrder a.st.ord) + 1) *
        bundleLogFactor M N :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by simp only [P, asmTopParams]; omega))
    have hdist : (BRS.mul capExp limbMul + 400) * (ordWordsOn (a.st.trees branch).S_cur.V ((a.st.trees branch).outOrder a.st.ord) + 1) *
        bundleLogFactor M N =
        BRS.mul capExp limbMul * (ordWordsOn (a.st.trees branch).S_cur.V ((a.st.trees branch).outOrder a.st.ord) + 1) * bundleLogFactor M N +
        400 * ((ordWordsOn (a.st.trees branch).S_cur.V ((a.st.trees branch).outOrder a.st.ord) + 1) * bundleLogFactor M N) := by ring
    have h400 : 400 ≤ 400 * ((ordWordsOn (a.st.trees branch).S_cur.V ((a.st.trees branch).outOrder a.st.ord) + 1) * bundleLogFactor M N) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) hlg_pos)
    omega

/-- Companion per-run footprint and returned-heap-pointer readout guarantees for the top layer. -/
theorem asmTop_readoutFoot_implements
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    (hLay : AsmBranchReadoutLayout BR)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (G : MGraph) (k M N vCap eCap sizeParam : ℕ)
    (hfmt : fmt.limbBits = 4) (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hdepth : 1 ≤ depth) (hInit : ∀ j < k, IsValidLSFInitFor lsfInit C_lsst k j) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let P := asmTopParams CFS BRS capExp limbMul
    let alloc := asmTopAlloc CFS BRS capExp sizeParam
    SparseCoreReadoutFootAt fmt L depth T G k M N vCap eCap capExp P alloc
      (asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
        CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap) p (asmTopOpIdx b) :=
  ⟨asmTop_op2_runs CF BR hLay hp G k M N vCap eCap sizeParam hfmt hcap,
   asmTop_op3_runs CF BR hLay hp G k M N vCap eCap sizeParam,
   asmTop_op4_runs CF BR hLay hp G k M N vCap eCap sizeParam hdepth hInit,
   asmTop_op5_runs CF BR hLay hp G k M N vCap eCap sizeParam hcap⟩

end MinCostFlow.SparseCore.Program
