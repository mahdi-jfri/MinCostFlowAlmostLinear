module

public import MinCostFlow.SparseCore.Program.AssemblyTopProcs
public import MinCostFlow.SparseCore.Program.AssemblyTopStepLoopOut
public import MinCostFlow.SparseCore.Program.AssemblyContractLayout
import MinCostFlow.SparseCore.Program.AssemblyInputInv

/-!
# Empty-state helper and auxiliary lemmas for top-layer `op 0` output layout (`AssemblyContractLayoutTopOp0Empty`)

Provides the empty-state (`x.ne = none`) branch of `asmTop_updateOutFoot_implements` together with
the small `LSFChangeAt` helpers used by both branches of `AssemblyContractLayoutTopOp0.lean`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF
open MinCostFlow.SparseCore.Program.Read

theorem lsfChange_fDel_lt_of_compFamilyChgAt {w k j : ℕ} {mem : ℕ → ℕ}
    {fChgPtr fChgEnd : ℕ} {c : LSFChange}
    (hW : ∀ a, fChgPtr ≤ a → a < fChgEnd → mem a < 2 ^ w)
    (hAt : LSFChangeAt mem (mem (fChgPtr + j)) c)
    (hlo : fChgPtr + k ≤ mem (fChgPtr + j)) (hhi : mem (fChgPtr + j) + c.words ≤ fChgEnd) :
    ∀ e ∈ c.fDel, e < 2 ^ w := by
  intro e he
  obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem he
  have hmem := hAt.2.2.2 idx hidx
  have hw := hW (mem (fChgPtr + j) + 2 + c.roots.length + idx) (by omega)
    (by unfold LSFChange.words LSFChange.size at hhi; omega)
  rwa [hmem] at hw

theorem emptyLSF_exact : (⟨[], []⟩ : LSFChange).Exact emptyLSF emptyLSF :=
  ⟨List.nodup_nil, by simp [emptyLSF, emptyGraph], List.nodup_nil, by simp [emptyLSF, emptyGraph]⟩

theorem lsfChangeAt_empty_of_zero {mem : ℕ → ℕ} {a : ℕ}
    (h0 : mem a = 0) (h1 : mem (a + 1) = 0) : LSFChangeAt mem a ⟨[], []⟩ :=
  ⟨h0, fun _ h => by simp at h, by simpa using h1, fun _ h => by simp at h⟩

/-- Empty-state (`x.ne = none`) branch of `asmTop_updateOutFoot_implements`. -/
theorem asmTop_op0_empty_outFoot
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p
      fCFInit fCFBatch CF bp)
    {edMul : ℕ} (hedPos : 1 ≤ edMul)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    {G₀ : MGraph} {k M N vCap eCap sizeParam : ℕ}
    (hsize : M + N + k + vCap + eCap + L + depth ≤ sizeParam)
    {hndl graph batch words edits editWords lengths gradient heap : ℕ}
    {a : SparseCoreOrdAbs (sparseCoreProgTool lsfInit C_lsst depth impl)}
    {x : (asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf (asmTopParams CFS BRS capExp limbMul).wordExp capExp limbMul w L fmt.precision vCap eCap).τ}
    {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hrep : (asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf (asmTopParams CFS BRS capExp limbMul).wordExp capExp limbMul w L fmt.precision vCap eCap).rep
      hndl a x mem)
    (hxne_b : x.ne = none)
    (hinp : SparseCoreOrdInput (sparseCoreProgTool lsfInit C_lsst depth impl) k M N a.st a.G a.ord a.n)
    (hUval : a.G.BatchIsValid (ordUpdateBatch a
      [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap] mem))
    (hfoot : ∀ addr, (asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf (asmTopParams CFS BRS capExp limbMul).wordExp capExp limbMul w L fmt.precision vCap eCap).foot
      hndl x addr → addr < heap)
    (hz : ZeroFrom mem heap)
    (hsp : heap + asmTopAlloc CFS BRS capExp sizeParam 0
      [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap] < 2 ^ w) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let P := asmTopParams CFS BRS capExp limbMul
    let alloc := asmTopAlloc CFS BRS capExp sizeParam
    let D := sparseCoreOrdMachineContractKFBL fmt L depth T G₀ k M N vCap eCap capExp P alloc
    let R := asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap
    let args := [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap]
    let a' := ordUpdateNext fmt L a args mem
    let batches := (ordUpdateModel fmt L a args mem).2
    ∃ o st' c x',
      Runs w p ω (asmTopUpdateBody (b + 20) (b + 21) (ordStoreOp b 0) fCFBatch bp.fStep)
        (startState args mem pos) o st' c ∧
      R.rep hndl a' x' st'.mem ∧
      D.post 0 a args mem a' st'.mem ∧
      BranchOutFChgAt w st'.mem heap o.value k (T.lsfs a.st) (T.lsfs a'.st) ∧
      (∀ j < k,
        let base := heap + 1 + 4 * j
        let bPtr := st'.mem base
        let bW := st'.mem (base + 1)
        let ePtr := st'.mem (base + 2)
        let eW := st'.mem (base + 3)
        heap + 1 + 4 * j + 3 < o.value ∧
        heap ≤ bPtr ∧ bPtr + bW ≤ o.value ∧
        heap ≤ ePtr ∧ ePtr + eW ≤ o.value ∧
        (∀ t < bW, st'.mem (bPtr + t) < 2 ^ w) ∧
        (∀ t < eW, st'.mem (ePtr + t) < 2 ^ w) ∧
        (∀ t < bW, ¬ R.foot hndl x' (bPtr + t)) ∧
        (∀ t < eW, ¬ R.foot hndl x' (ePtr + t)) ∧
        (decodeBatch st'.mem bPtr (T.S a.st j)).1 = batches j ∧
        eW ≤ edMul * (T.cost a'.st - T.cost a.st +
          (words + editWords + 1) * bundleLogFactor M N)) ∧
      R.Respects (R.foot hndl x) heap (alloc 0 args) mem o.value hndl x' st'.mem ∧
      (c + R.phi hndl x' st'.mem ≤ D.cost 0 a args mem + R.phi hndl x mem) ∧
      (∀ j < k, heap ≤ st'.mem (heap + 1 + 4 * k + 2 * j) ∧
        st'.mem (heap + 1 + 4 * k + 2 * j) + st'.mem (heap + 2 + 4 * k + 2 * j) ≤ o.value) := by
  intro T P alloc D R args a' batches
  rcases hrep with ⟨⟨⟨hxne, hxk, hxres, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7,
    he0, he1, he2, he3, _⟩, hxL, hxPfp, hxvCap, hxeCap, hxwM, hxcap, hxk_pos⟩, hEmpty, _⟩
  obtain ⟨hinp_k, _, _⟩ := asm_input_inv lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    (canonicalSparsifyParams impl) (dsAmortConst impl) hinp
  have hk_eq : x.k = k := hxk.trans hinp_k
  have hhdr_sz : ASM_HDR_SIZE = 20 := rfl
  have hresHi_le : x.resHi ≤ heap := by
    have hlt := hfoot (x.resHi - 1) (Or.inr (Or.inl ⟨by omega, by omega⟩)); omega
  have hhdr_lt : hndl + ASM_HDR_SIZE ≤ heap := by
    have hlt := hfoot (hndl + ASM_HDR_SIZE - 1) (Or.inl ⟨by omega, by omega⟩); omega
  have hw16 : 16 < 2 ^ w := by omega
  have hlg_pos : 1 ≤ bundleLogFactor M N := le_trans (by omega) (logStep_le_bundleLogFactor M N)
  set st0 := startState args mem pos
  have hload9 : Runs w p ω (.assign 9 (.load (.reg 0))) st0 .normal
      { st0 with regs := Function.update st0.regs 9 (if x.ne.isSome then 1 else 0) } _ :=
    runs_assign_iff.mpr ⟨if x.ne.isSome then 1 else 0,
      Expr.eval_load_of_eq (w := w) (Expr.eval_reg_of_eq (v := hndl) (by simp [st0, args, startState]))
        (by simpa [st0, args, startState, ASM_HDR_NE] using hm0), rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 9 (if x.ne.isSome then 1 else 0) }
  have hload10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const ASM_HDR_K)))) st1 .normal
      { st1 with regs := Function.update st1.regs 10 k } _ :=
    runs_assign_iff.mpr ⟨k,
      Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st1, st0, args, startState]))
          (Expr.eval_const (by unfold ASM_HDR_K; omega)) (by unfold ASM_HDR_K ASM_HDR_SIZE at *; omega))
        (by simpa [st1, st0, args, startState, hk_eq] using hm1), rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 10 k }
  have hst_empty : a.st.isNonempty = false := by simpa [hxne_b] using hxne.symm
  obtain ⟨hV_em, hE_em⟩ := asmEmpty_inv hinp hst_empty
  obtain ⟨_, _, _⟩ := applyBatch_empty_of_valid hV_em hE_em hUval
  have hsp_em : heap + (7 * k + 4) < 2 ^ w := by
    simp only [asmTopAlloc, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at hsp
    omega
  obtain ⟨oE, stE, cE, hrunE, hvalE, hBO_em, hfChgE, hfChgJ, hSlotsE, hReembE, hOE_em, _, hfrE,
      hzEptr, hzE, hcostE⟩ :=
    asmEmptyUpdateBody_runs (w := w) (k := k) (heap := heap) (pos := st2.pos) (p := p) ω
      (mem := mem) (by omega) hsp_em hz
  have hcallE : Runs w p ω (.call 14 (b + 20) [.reg 10, .reg 8]) st2 .normal
      { stE with regs := Function.update st2.regs 14 oE.value }
      (argsSize [.reg 10, .reg 8] + cE + 1) := by
    refine (runs_call_iff (r := 14) (f := b + 20) (st := st2) (o := .normal)
      (st' := { stE with regs := Function.update st2.regs 14 oE.value })).mpr
      ⟨[k, heap], asmEmptyUpdateBody, oE, stE, cE, ?_, hp.at_emptyUpd, hrunE, rfl, rfl, rfl⟩
    simp [evalArgs, Expr.eval, st2, st1, st0, args, startState]
  set st3 : State := { stE with regs := Function.update st2.regs 14 oE.value }
  have hretE : Runs w p ω (.ret (.reg 14)) st3 (.returned oE.value) st3 ((Expr.reg 14).size + 1) :=
    runs_ret_iff.mpr ⟨oE.value, Expr.eval_reg_of_eq (by simp [st3]), rfl, rfl, rfl⟩
  obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
      Runs w p ω (asmTopUpdateBody (b + 20) (b + 21) (ordStoreOp b 0) fCFBatch bp.fStep) st0
        (.returned oE.value) st3 cF ∧ cF ≤ cE + 50 := by
    unfold asmTopUpdateBody
    have hbr := runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hcallE, hretE, rfl⟩)
    refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload9,
      runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hload10,
        runs_cond_iff.mpr ⟨0, _, Expr.eval_reg_of_eq (v := 0) (by simp [st2, st1, hxne_b]),
          by simpa using hbr, rfl⟩, rfl⟩), rfl⟩), ?_⟩
    simp only [Expr.size]; omega
  have ha'_st : a'.st = a.st := by
    unfold a' ordUpdateNext ordUpdateModel
    exact congrArg Prod.fst (asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) a.st hst_empty _ _ _ _)
  have ha'_US : (ordUpdateModel fmt L a args mem).2 = fun _ => [] := by
    unfold ordUpdateModel
    exact congrArg Prod.snd (asm_updateOrd_of_empty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) a.st hst_empty _ _ _ _)
  have hS_em : T.S a.st = fun _ => emptyGraph := by
    funext j; change (if a.st.isNonempty then _ else emptyGraph) = _; simp [hst_empty]
  have hlsf_em : T.lsfs a.st = fun _ => emptyLSF := by
    funext j; change (if a.st.isNonempty then _ else emptyLSF) = _; simp [hst_empty]
  have hlsf'_em : T.lsfs a'.st = fun _ => emptyLSF := by rw [ha'_st]; exact hlsf_em
  have hrot_em : T.rot a.st = fun _ _ => [] := by
    funext j v; change (if a.st.isNonempty then _ else fun _ => []) v = _; simp [hst_empty]
  have hrot'_em : T.rot a'.st = fun _ _ => [] := by rw [ha'_st]; exact hrot_em
  have hret_val : (Outcome.returned oE.value).value = heap + 7 * k + 4 := hvalE
  refine ⟨.returned oE.value, st3, cF, x, hfull, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨by rw [ha'_st]; exact hxne, by rw [ha'_st]; exact hxk, hxres,
      (hfrE _ (by unfold ASM_HDR_NE ASM_HDR_SIZE at *; omega)).trans hm0,
      (hfrE _ (by unfold ASM_HDR_K ASM_HDR_SIZE at *; omega)).trans hm1,
      (hfrE _ (by unfold ASM_HDR_M ASM_HDR_SIZE at *; omega)).trans hm2,
      (hfrE _ (by unfold ASM_HDR_N ASM_HDR_SIZE at *; omega)).trans hm3,
      (hfrE _ (by unfold ASM_HDR_VCAP ASM_HDR_SIZE at *; omega)).trans hm4,
      (hfrE _ (by unfold ASM_HDR_ECAP ASM_HDR_SIZE at *; omega)).trans hm5,
      (hfrE _ (by unfold ASM_HDR_L ASM_HDR_SIZE at *; omega)).trans hm6,
      (hfrE _ (by unfold ASM_HDR_PFP ASM_HDR_SIZE at *; omega)).trans hm7,
      (hfrE _ (by unfold ASM_HDR_EMPTYG ASM_HDR_SIZE at *; omega)).trans he0,
      (hfrE _ (by unfold ASM_HDR_EMPTYG ASM_HDR_SIZE at *; omega)).trans he1,
      (hfrE _ (by unfold ASM_HDR_EMPTYG ASM_HDR_SIZE at *; omega)).trans he2,
      (hfrE _ (by unfold ASM_HDR_EMPTYG ASM_HDR_SIZE at *; omega)).trans he3,
      fun _ hS => by simp [hxne_b] at hS⟩, hxL, hxPfp, hxvCap, hxeCap, hxwM, hxcap, hxk_pos⟩,
      fun hne => by
        obtain ⟨hlo, hhi, hdg⟩ := hEmpty hne
        exact ⟨hlo, hhi, dynGraphAt_of_agree hdg fun addr ha1 ha2 => hfrE addr (by omega)⟩,
      fun _ hS => by simp [hxne_b] at hS⟩
  · refine ⟨⟨rfl, ?_⟩, fun j hj => ?_, fun j hj => ?_⟩
    · change BranchOutAt stE.mem heap k (T.S a.st) _ (T.rot a.st) (T.rot a'.st)
      rw [hS_em, ha'_US, hrot_em, hrot'_em]; exact hBO_em
    · change OrdEditsForBatch (T.S a.st j) _ (readOrdEdits stE.mem (stE.mem (heap + 3 + 4 * j)))
      rw [hS_em, ha'_US, hOE_em j hj]; exact fun _ h => (List.not_mem_nil h).elim
    · change OrdEditsValidFor vCap eCap (T.rot a.st j) (readOrdEdits stE.mem (stE.mem (heap + 3 + 4 * j)))
      rw [hrot_em, hOE_em j hj]
      exact ⟨fun _ hd => (List.not_mem_nil hd).elim, fun t ht => by
        have ht0 : t = 0 := by simp at ht; omega
        subst ht0; exact ⟨⟨fun _ => List.nodup_nil, fun _ _ => rfl,
          fun _ _ h => (List.not_mem_nil h).elim⟩, fun _ _ _ h => (List.not_mem_nil h).elim⟩⟩
  · refine ⟨by rw [hret_val]; omega, by change heap ≤ stE.mem (heap + 1 + 6 * k); rw [hfChgE]; omega,
      by change stE.mem (heap + 1 + 6 * k) + k ≤ _; rw [hfChgE, hret_val]; omega, fun j hj => ?_⟩
    refine ⟨⟨[], []⟩, ?_, ?_, ?_, ?_, fun _ h => by cases h⟩
    · change LSFChangeAt stE.mem (stE.mem (stE.mem (heap + 1 + 6 * k) + j)) ⟨[], []⟩
      rw [hfChgE, hfChgJ j hj]
      exact lsfChangeAt_empty_of_zero (hzEptr _ le_rfl) (hzEptr _ (by omega))
    · rw [hlsf_em, hlsf'_em]; exact emptyLSF_exact
    · change heap ≤ stE.mem (stE.mem (heap + 1 + 6 * k) + j)
      rw [hfChgE, hfChgJ j hj]; omega
    · change stE.mem (stE.mem (heap + 1 + 6 * k) + j) + (⟨[], []⟩ : LSFChange).words ≤ _
      rw [hfChgE, hfChgJ j hj, hret_val]; simp [LSFChange.words, LSFChange.size]; omega
  · intro j hj
    obtain ⟨hb0, hb1, hb2, hb3⟩ := hSlotsE j hj
    have hb0' : st3.mem (heap + 1 + 4 * j) = heap + 2 + 7 * k := hb0
    have hb1' : st3.mem (heap + 1 + 4 * j + 1) = 1 := by
      rw [show heap + 1 + 4 * j + 1 = heap + 2 + 4 * j by omega]; exact hb1
    have hb2' : st3.mem (heap + 1 + 4 * j + 2) = heap + 2 + 7 * k := by
      rw [show heap + 1 + 4 * j + 2 = heap + 3 + 4 * j by omega]; exact hb2
    have hb3' : st3.mem (heap + 1 + 4 * j + 3) = 1 := by
      rw [show heap + 1 + 4 * j + 3 = heap + 4 + 4 * j by omega]; exact hb3
    refine ⟨by rw [hret_val]; omega, by rw [hb0']; omega, by rw [hb0', hb1', hret_val]; omega,
      by rw [hb2']; omega, by rw [hb2', hb3', hret_val]; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht; rw [hb1'] at ht; have ht0 : t = 0 := by omega
      subst ht0; rw [hb0', Nat.add_zero]; change stE.mem (heap + 2 + 7 * k) < 2 ^ w
      rw [hzEptr _ le_rfl]; omega
    · intro t ht; rw [hb3'] at ht; have ht0 : t = 0 := by omega
      subst ht0; rw [hb2', Nat.add_zero]; change stE.mem (heap + 2 + 7 * k) < 2 ^ w
      rw [hzEptr _ le_rfl]; omega
    · intro t _ hft; rw [hb0'] at hft; have := hfoot _ hft; omega
    · intro t _ hft; rw [hb2'] at hft; have := hfoot _ hft; omega
    · change (decodeBatch st3.mem (st3.mem (heap + 1 + 4 * j)) (T.S a.st j)).1 =
        (ordUpdateModel fmt L a args mem).2 j
      rw [hb0', ha'_US]; unfold decodeBatch
      change (decodeBatchBody stE.mem (stE.mem (heap + 2 + 7 * k)) _ _).1 = []
      rw [hzEptr _ le_rfl]; rfl
    · rw [hb3']
      have hpos : 1 ≤ (words + editWords + 1) * bundleLogFactor M N := Nat.mul_pos (by omega) hlg_pos
      have := Nat.mul_le_mul hedPos (show 1 ≤ T.cost a'.st - T.cost a.st +
        (words + editWords + 1) * bundleLogFactor M N by omega)
      omega
  · refine ⟨by rw [hret_val]; omega, ?_, ?_, fun addr ha _ => hfrE addr ha, fun addr ha => Or.inl ha⟩
    · rw [hret_val]
      simp only [alloc, asmTopAlloc, args, List.getD_eq_getElem?_getD,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      omega
    · rw [hret_val]; exact fun a ha => hzE a (by omega)
  · have hphi0 : R.phi hndl x st3.mem = 0 ∧ R.phi hndl x mem = 0 := by
      simp [R, asmTopRepEq, asmTopPhi, hxne_b]
    rw [hphi0.1, hphi0.2]
    change _ ≤ P.mul * (T.cost a'.st - T.cost a.st +
      (k + 1) * (words + editWords + 1) * bundleLogFactor M N) + 0
    have hmul_ge : 400 ≤ P.mul := by simp [P, asmTopParams]
    have hterm : k + 1 ≤ (k + 1) * (words + editWords + 1) * bundleLogFactor M N :=
      le_trans (Nat.le_mul_of_pos_right _ (by omega)) (Nat.le_mul_of_pos_right _ hlg_pos)
    have hmul_le : 400 * (k + 1) ≤ P.mul * (T.cost a'.st - T.cost a.st +
        (k + 1) * (words + editWords + 1) * bundleLogFactor M N) :=
      Nat.mul_le_mul hmul_ge (by omega)
    omega
  · intro j hj
    obtain ⟨hr0, hr1⟩ := hReembE j hj
    change heap ≤ stE.mem (heap + 1 + 4 * k + 2 * j) ∧
      stE.mem (heap + 1 + 4 * k + 2 * j) + stE.mem (heap + 2 + 4 * k + 2 * j) ≤
        (Outcome.returned oE.value).value
    rw [hr0, hr1, hret_val]; omega

end MinCostFlow.SparseCore.Program
