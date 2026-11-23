module

public import MinCostFlow.SparseCore.Program.AssemblyContractLayoutTopOp0Empty
import MinCostFlow.SparseCore.Program.AssemblyInputInv
import MinCostFlow.SparseCore.Program.OutStepJoinModel

/-!
# Top-layer `op 0` output footprint and `fChgPtr` layout (`AssemblyContractLayoutTopOp0`)

Proves `asmTop_updateOutFoot_implements`: `asmTopUpdateBody` (`op 0`) at `asmTopRepEq` satisfies
`SparseCoreUpdateOutFootAt` (`MinRatio/WireChainCoreOp0KFBL.lean`) with the input-independent
edit-word multiplier `edMul` from `AsmBranchStepOutLayout BR edMul`.

* On an empty state (`x.ne = none`), `asmEmptyUpdateBody_runs` publishes the `k`-entry table of
  empty `LSFChangeAt` records at `mem (heap + 1 + 6 * k) = heap + 2 + 6 * k` and `k` empty
  `(bPtr, 1, ePtr, 1)` slots in `[heap, heap + 7 * k + 4)`.
* On a nonempty state (`x.ne = some ne`), `asmTopUpdateBody` publishes P4's `fChgPtr` at
  `heap + 1 + 6 * k` (giving `BranchOutFChgAt` via `CompFamilyChgAt`), and runs
  `asmStepBranchesLoop_outLayout_runs`, giving buffer placement inside `[heap, o.value)`,
  disjointness from `R.foot`, word-range bounds `< 2 ^ w`, `(decodeBatch ...).1 = batches j`
  (via `stepBundleTree_U_S_splitEndsExact`), and the `edMul` bound on `eW`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF
open MinCostFlow.SparseCore.Program.Read

private theorem sum_lsfBatchSize_le_sum_branchStepCharge_op0 {depth : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {k M N : ℕ} {tr : ℕ → BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    (hMN : ∀ j < k, (tr j).m₀ = M ∧ (tr j).n₀ = N) :
    ((Finset.range k).sum fun j => lsfBatchSize (tr j).cs U) * bundleLogFactor M N ≤
      (Finset.range k).sum fun j => branchStepCharge sparsify (tr j) U ord ord' := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk := Finset.mem_range.mp hj
  obtain ⟨hm, hn⟩ := hMN j hjk
  unfold branchStepCharge
  rw [hm, hn]
  exact Nat.mul_le_mul_right _ (by omega)

set_option maxHeartbeats 1600000 in
/-- **Top-layer `SparseCoreUpdateOutFootAt` and `SparseCoreReembPlaceAt`**: executing
`asmTopUpdateBody` (`op 0`) at `asmTopRepEq` meets every output placement, `BranchOutFChgAt`,
disjointness, `decodeBatch`, word-range, and `edMul` guarantee of `SparseCoreUpdateOutFootAt`,
together with re-embedding-list placement in `[heap, o.value)` (`SparseCoreReembPlaceAt`). -/
theorem asmTop_updateOutFoot_reembPlace
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    {edMul : ℕ} (hStepLay : AsmBranchStepOutLayout BR edMul)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp) (G₀ : MGraph) (k M N vCap eCap sizeParam : ℕ)
    (hfmt : fmt.limbBits = 4) (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hdepth : 1 ≤ depth) (hdepth_le : depth ≤ M + N + k + L) (hdepth_lg : depth ≤ bundleLogFactor M N)
    (hdepth_ch : depth ≤ Expander.chosenL ((M + N) ^ 2))
    (hsize : M + N + k + vCap + eCap + L + depth ≤ sizeParam) (hγt : impl.γ_t M = 1)
    (hInit : ∀ j < k, IsValidLSFInitFor lsfInit C_lsst k j) (hkCap : k ≤ (M + N + 2) ^ capExp) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let P := asmTopParams CFS BRS capExp limbMul
    let alloc := asmTopAlloc CFS BRS capExp sizeParam
    let R := asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap
    SparseCoreUpdateOutFootAt fmt L depth T G₀ k M N vCap eCap capExp P alloc edMul R p (asmTopOpIdx b) ∧
      SparseCoreReembPlaceAt fmt L depth T G₀ k M N vCap eCap capExp P alloc R p (asmTopOpIdx b) := by
  intro T P alloc R
  let D := sparseCoreOrdMachineContractKFBL fmt L depth T G₀ k M N vCap eCap capExp P alloc
  suffices hBoth : ∀ (hndl : ℕ) (a : SparseCoreOrdAbs T) (x : R.τ) (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) → args.head? = some hndl → R.rep hndl a x mem → D.pre 0 a args mem →
      (∀ addr, R.foot hndl x addr → addr < heapArg args) → ZeroFrom mem (heapArg args) →
      heapArg args + D.space 0 a args mem < 2 ^ w →
      ∃ body, p.procs[asmTopOpIdx b 0]? = some body ∧ ∃ o st' c x',
        let h := heapArg args; let words := args.getD 3 0; let editWords := args.getD 5 0
        let a' := ordUpdateNext fmt L a args mem; let batches := (ordUpdateModel fmt L a args mem).2
        Runs w p ω body (startState args mem pos) o st' c ∧ R.rep hndl a' x' st'.mem ∧
        D.post 0 a args mem a' st'.mem ∧ BranchOutFChgAt w st'.mem h o.value k (T.lsfs a.st) (T.lsfs a'.st) ∧
        (∀ j < k, let base := h + 1 + 4 * j; let bPtr := st'.mem base; let bW := st'.mem (base + 1)
          let ePtr := st'.mem (base + 2); let eW := st'.mem (base + 3)
          h + 1 + 4 * j + 3 < o.value ∧ h ≤ bPtr ∧ bPtr + bW ≤ o.value ∧ h ≤ ePtr ∧ ePtr + eW ≤ o.value ∧
          (∀ t < bW, st'.mem (bPtr + t) < 2 ^ w) ∧ (∀ t < eW, st'.mem (ePtr + t) < 2 ^ w) ∧
          (∀ t < bW, ¬ R.foot hndl x' (bPtr + t)) ∧ (∀ t < eW, ¬ R.foot hndl x' (ePtr + t)) ∧
          (decodeBatch st'.mem bPtr (T.S a.st j)).1 = batches j ∧
          eW ≤ edMul * (T.cost a'.st - T.cost a.st + (words + editWords + 1) * bundleLogFactor M N)) ∧
        R.Respects (R.foot hndl x) h (D.space 0 a args mem) mem o.value hndl x' st'.mem ∧
        c + R.phi hndl x' st'.mem ≤ D.cost 0 a args mem + R.phi hndl x mem ∧
        (∀ j < k, h ≤ st'.mem (h + 1 + 4 * k + 2 * j) ∧
          st'.mem (h + 1 + 4 * k + 2 * j) + st'.mem (h + 2 + 4 * k + 2 * j) ≤ o.value) by
    exact ⟨⟨fun b a x args mem pos ω h1 h2 h3 h4 h5 h6 h7 =>
      let ⟨body, hb, o, st', c, x', hA, hB, hC, hD, hE, hF, hG, _⟩ := hBoth b a x args mem pos ω h1 h2 h3 h4 h5 h6 h7
      ⟨body, hb, o, st', c, x', hA, hB, hC, hD, hE, hF, hG⟩⟩,
      ⟨fun b a x args mem pos ω h1 h2 h3 h4 h5 h6 h7 =>
      let ⟨body, hb, o, st', c, _, hA, _, _, _, _, _, _, hH⟩ := hBoth b a x args mem pos ω h1 h2 h3 h4 h5 h6 h7
      ⟨body, hb, o, st', c, hA, hH⟩⟩⟩
  intro hndl a x args mem pos ω hargsW hhead hrep hpre hfoot hz hsp
  refine ⟨_, hp.at_op0, ?_⟩
  rcases hpre with ⟨⟨⟨hndl', graph, batch, words, edits, editWords, lengths, gradient, heap,
    hargs_eq, hinp, hG, hSB, hUval, hUcap, hEdAt, hOrdB, hThr, hBw, hEw,
    hG_le, hB_le, hE_le, hL_le, hGr_le, hValidE, hPosE⟩, hEdVal⟩, hEdBlocks⟩
  subst hargs_eq
  simp only [List.head?_cons, Option.some.injEq] at hhead
  subst hndl'
  have hheapArg : heapArg [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap] = heap := rfl
  rw [hheapArg] at hfoot hz hsp ⊢
  have hspD : (sparseCoreOrdMachineContractKFBL fmt L depth T G₀ k M N vCap eCap capExp P alloc).space 0
      a [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap] mem =
      alloc 0 [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap] := rfl
  rw [hspD] at hsp ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargsW
  rcases hargsW with ⟨hhndlW, hgraphW, hbatchW, hwordsW, heditsW, heditWordsW, hlenW, hgradW, hheapW⟩
  have hrep_orig := hrep
  rcases hrep with ⟨⟨⟨hxne, hxk, hxres, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7,
    he0, he1, he2, he3, hnonempty⟩, hxL, hxPfp, hxvCap, hxeCap, hxwM, hxcap, hxk_pos⟩, hEmpty, hCaps⟩
  obtain ⟨hinp_k, hinp_ord, hinp_mn⟩ := asm_input_inv lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
    (canonicalSparsifyParams impl) (dsAmortConst impl) hinp
  have hk_eq : x.k = k := hxk.trans hinp_k
  have hk_pos : 0 < k := by omega
  have hhdr_sz : ASM_HDR_SIZE = 20 := rfl
  have hresHi_le : x.resHi ≤ heap := by
    have hlt := hfoot (x.resHi - 1) (Or.inr (Or.inl ⟨by omega, by omega⟩)); omega
  have hres_le : x.M + x.N + x.k + x.vCap + x.eCap + x.L + ASM_HDR_SIZE ≤ heap := by omega
  have hhdr_lt : hndl + ASM_HDR_SIZE ≤ heap := by
    have hlt := hfoot (hndl + ASM_HDR_SIZE - 1) (Or.inl ⟨by omega, by omega⟩); omega
  have hw16 : 16 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have hlg_pos : 1 ≤ bundleLogFactor M N := le_trans (by omega) (logStep_le_bundleLogFactor M N)
  set st0 := startState [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap] mem pos
  have hload9 : Runs w p ω (.assign 9 (.load (.reg 0))) st0 .normal
      { st0 with regs := Function.update st0.regs 9 (if x.ne.isSome then 1 else 0) } _ :=
    runs_assign_iff.mpr ⟨if x.ne.isSome then 1 else 0,
      Expr.eval_load_of_eq (w := w) (Expr.eval_reg_of_eq (v := hndl) (by simp [st0, startState]))
        (by simpa [st0, startState, ASM_HDR_NE] using hm0), rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 9 (if x.ne.isSome then 1 else 0) }
  have hload10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 0) (.const ASM_HDR_K)))) st1 .normal
      { st1 with regs := Function.update st1.regs 10 k } _ :=
    runs_assign_iff.mpr ⟨k,
      Expr.eval_load_of_eq (w := w)
        (Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st1, st0, startState]))
          (Expr.eval_const (by unfold ASM_HDR_K; omega)) (by unfold ASM_HDR_K ASM_HDR_SIZE at *; omega))
        (by simpa [st1, st0, startState, hk_eq] using hm1), rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 10 k }
  set U := ordUpdateBatch a [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap] mem
  set ed := readOrdEdits mem edits
  set ord' := applyOrdEdits a.ord ed
  cases hxne_b : x.ne with
  | none =>
    exact asmTop_op0_empty_outFoot CF BR hStepLay.edMul_pos hp hsize hrep_orig hxne_b hinp hUval
      hfoot hz hsp
  | some ne =>
    have hst_ne : a.st.isNonempty = true := by simpa [hxne_b] using hxne.symm
    obtain ⟨h8, h9, h10, hcfLt, htblLt, hbrLt, hvG, heG, hG_br, hOrdRep, hCFRep, hTbl, hBRRep,
        hd1, hd2, hd3, hd4, hd5⟩ := hnonempty ne hxne_b
    have hxM_eq : x.M = M := (hG_br 0 (by omega)).2.1.symm.trans (hinp_mn 0).1
    have hxN_eq : x.N = N := (hG_br 0 (by omega)).2.2.symm.trans (hinp_mn 0).2.1
    have hwPL : (M + N + 2) ^ P.wordExp * (L + 1) < 2 ^ w := by
      simpa [hxM_eq, hxN_eq, hxL] using hxwM
    have hwP : (M + N + 2) ^ P.wordExp < 2 ^ w :=
      lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.succ_pos L)) hwPL
    have hwOrd : (vCap + eCap + 2) ^ 2 < 2 ^ w :=
      capWord_of_wordExp hcap (le_trans (asmP10WordExp_ge_two_mul capExp) (le_max_right _ _)) hwP
    have hwCF : (M + N + 2) ^ CFS.wordExp capExp * (L + 1) < 2 ^ w :=
      lt_of_le_of_lt (Nat.mul_le_mul_right (L + 1)
        (Nat.pow_le_pow_right (by omega) (by simp [P, asmTopParams, asmTopWordExp]))) hwPL
    have hwBR : (M + N + 2) ^ BRS.wordExp capExp * (L + 1) < 2 ^ w :=
      lt_of_le_of_lt (Nat.mul_le_mul_right (L + 1)
        (Nat.pow_le_pow_right (by omega) (by simp [P, asmTopParams, asmTopWordExp]))) hwPL
    have hord_eq : a.st.ord = a.ord := hinp_ord hst_ne
    have hsp_raw : heap + ((4 + 7 * sizeParam) + words + editWords + (3 * editWords + 2) +
        (CFS.batchSpace capExp).eval (sizeParam + words) +
        sizeParam * (BRS.stepSpace capExp).eval (sizeParam + words + editWords)) < 2 ^ w := by
      simpa [alloc, asmTopAlloc] using hsp
    have hcfSp_le : (CFS.batchSpace capExp).eval (vCap + eCap + L + k + words) ≤
        (CFS.batchSpace capExp).eval (sizeParam + words) := (CFS.batchSpace capExp).eval_mono (by omega)
    have hbrSp_le : (BRS.stepSpace capExp).eval (M + N + k + vCap + eCap + L + depth + words + editWords) ≤
        (BRS.stepSpace capExp).eval (sizeParam + words + editWords) := (BRS.stepSpace capExp).eval_mono (by omega)
    have hkbrSp_le : k * (BRS.stepSpace capExp).eval (M + N + k + vCap + eCap + L + depth + words + editWords) ≤
        sizeParam * (BRS.stepSpace capExp).eval (sizeParam + words + editWords) := Nat.mul_le_mul (by omega) hbrSp_le
    set bCopy := heap + 2 + 6 * k
    set eCopy := bCopy + words
    set h0 := eCopy + editWords
    obtain ⟨st5f, hcp_wrap, h5f_r, h5f_lt_raw, h5f_heap, h5f_b, h5f_e, hz5f⟩ :=
      asmTopUpdate_copies (w := w) (b := b) (hndl := hndl)
        (batch := batch) (words := words) (edits := edits) (editWords := editWords)
        (heap := heap) (k := k)
        (p := p) ω st2 (hp.copy_meetsContract (w := w)) hw16 hB_le hE_le (by omega)
        (by simp [st2, st1, st0, startState]) (by simp [st2, st1, st0, startState])
        (by simp [st2, st1, st0, startState]) (by simp [st2, st1, st0, startState])
        (by simp [st2, st1, st0, startState]) (by simp [st2, st1, st0, startState])
        (by simp [st2]) hz
    have h5f_lt : ∀ addr < heap, st5f.mem addr = mem addr := h5f_lt_raw
    have h5f_r2 : st5f.regs 2 = bCopy := h5f_r.2.1
    have h5f_r4 : st5f.regs 4 = eCopy := h5f_r.2.2.2.1
    have h5f_r14 : st5f.regs 14 = h0 := h5f_r.2.2.2.2.2.2.2
    have hSB5f : SmallBatchAt st5f.mem bCopy a.G U words := smallBatchAt_shift hSB h5f_b
    have hEd5f : OrdEditsAt st5f.mem eCopy ed editWords := ordEditsAt_shift hEdAt h5f_e
    have hBw5f : ∀ t < words, st5f.mem (bCopy + t) < 2 ^ w := fun t ht => by
      rw [h5f_b t ht]; exact hBw t ht
    have hEw5f : ∀ t < editWords, st5f.mem (eCopy + t) < 2 ^ w := fun t ht => by
      rw [h5f_e t ht]; exact hEw t ht
    have hload_ordH : Runs w p ω (.assign 11 (.load (.bin .add (.reg 0) (.const ASM_HDR_ORDH)))) st5f .normal
        { st5f with regs := Function.update st5f.regs 11 ne.ordH } _ :=
      runs_assign_iff.mpr ⟨ne.ordH,
        Expr.eval_load_of_eq (w := w)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) h5f_r.1)
            (Expr.eval_const (by unfold ASM_HDR_ORDH; omega)) (by unfold ASM_HDR_ORDH ASM_HDR_SIZE at *; omega))
          ((h5f_lt _ (by unfold ASM_HDR_ORDH ASM_HDR_SIZE at *; omega)).trans h8), rfl, rfl, rfl⟩
    let st5 : State := { st5f with regs := Function.update st5f.regs 11 ne.ordH }
    have hordFoot_lt : ∀ addr, ordFoot ne.ordH vCap eCap addr → addr < heap := fun addr ha =>
      hfoot addr (Or.inr (Or.inr (by simp [hxne_b]; exact Or.inl (by rwa [hxvCap, hxeCap]))))
    have hordH_w : ne.ordH < 2 ^ w := by
      have hpos : 0 < ordArenaSize vCap eCap := by unfold ordArenaSize; omega
      have := hordFoot_lt ne.ordH (by unfold ordFoot; omega); omega
    have hOrdRep5 : (ordStoreRep vCap eCap).rep ne.ordH a.ord ne.xOrd st5.mem := by
      rw [← hord_eq]
      exact (ordStoreRep_local vCap eCap ne.ordH a.st.ord ne.xOrd mem st5.mem fun addr ha =>
        (h5f_lt addr (hordFoot_lt addr ha)).symm).1 (by rwa [hxvCap, hxeCap] at hOrdRep)
    have hreadEd5 : readOrdEdits st5.mem eCopy = ed := hEd5f.1
    have hOrdImpl := (ordStore_implements_cap w vCap eCap p b hp.hasOrdStore hwOrd).2
    obtain ⟨bodyOrd, hbodyOrd, oOrd, stOrd, cOrd, hrunOrd, sOrd', xOrd', hOrdRep', hOrdPost', hOrdResp, hOrdCost⟩ :=
      hOrdImpl.2.2 0 ne.ordH a.ord ne.xOrd [ne.ordH, eCopy, editWords, h0] st5.mem st5.pos ω
        (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl | rfl <;> omega)
        rfl hOrdRep5
        ⟨ne.ordH, eCopy, editWords, h0, rfl, hreadEd5 ▸ hEd5f, le_rfl, hreadEd5 ▸ hEdVal.1, hreadEd5 ▸ hEdVal.2⟩
        (fun addr ha => by change addr < h0; have := hordFoot_lt addr ha; omega) hz5f
        (by change h0 + (3 * editWords + 2) < 2 ^ w; omega)
    rcases hOrdResp with ⟨hOrd_lo, hOrd_hi, hzOrd, hOrd_fr, _⟩
    change h0 ≤ oOrd.value at hOrd_lo
    change oOrd.value ≤ h0 + (3 * editWords + 2) at hOrd_hi
    change ∀ a < h0, ¬ ordFoot ne.ordH vCap eCap a → stOrd.mem a = st5.mem a at hOrd_fr
    let h1 := oOrd.value
    have hsOrd'_eq : sOrd' = ord' := by simpa [ordStoreCapContract, ordStoreContract, ord', hreadEd5] using hOrdPost'
    rw [hsOrd'_eq] at hOrdRep'
    have hcallOrd : Runs w p ω (.call 14 (ordStoreOp b 0) [.reg 11, .reg 4, .reg 5, .reg 14]) st5 .normal
        { stOrd with regs := Function.update st5.regs 14 h1 }
        (argsSize [.reg 11, .reg 4, .reg 5, .reg 14] + cOrd + 1) := by
      refine (runs_call_iff (r := 14) (f := ordStoreOp b 0) (st := st5) (o := .normal)
        (st' := { stOrd with regs := Function.update st5.regs 14 h1 })).mpr
        ⟨[ne.ordH, eCopy, editWords, h0], bodyOrd, oOrd, stOrd, cOrd, ?_, hbodyOrd, hrunOrd, rfl, rfl, rfl⟩
      simp [evalArgs, Expr.eval, st5, h5f_r4, h5f_r.2.2.2.2.1, h5f_r14]
    let st6 : State := { stOrd with regs := Function.update st5.regs 14 h1 }
    have hOrd_fr_hdr : ∀ i < ASM_HDR_SIZE, stOrd.mem (hndl + i) = mem (hndl + i) := fun i hi => by
      rw [hOrd_fr _ (by omega) (fun hf => (hd1 _ ⟨Nat.le_add_right hndl i, Nat.add_lt_add_left hi hndl⟩).1 (by rwa [← hxvCap, ← hxeCap] at hf)),
        h5f_lt _ (by omega)]
    have hload_cfH : Runs w p ω (.assign 11 (.load (.bin .add (.reg 0) (.const ASM_HDR_CFH)))) st6 .normal
        { st6 with regs := Function.update st6.regs 11 ne.cfH } _ :=
      runs_assign_iff.mpr ⟨ne.cfH,
        Expr.eval_load_of_eq (w := w)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st6, st5, h5f_r.1]))
            (Expr.eval_const (by unfold ASM_HDR_CFH; omega)) (by unfold ASM_HDR_CFH ASM_HDR_SIZE at *; omega))
          ((hOrd_fr_hdr ASM_HDR_CFH (by decide)).trans h9), rfl, rfl, rfl⟩
    let st7 : State := { st6 with regs := Function.update st6.regs 11 ne.cfH }
    have ha13_h1 : Runs w p ω (.assign 13 (.reg 14)) st7 .normal
        { st7 with regs := Function.update st7.regs 13 h1 } _ :=
      runs_assign_iff.mpr ⟨h1, Expr.eval_reg_of_eq (by simp [st7, st6]), rfl, rfl, rfl⟩
    let st8 : State := { st7 with regs := Function.update st7.regs 13 h1 }
    have hcfFoot_lt : ∀ addr, CF.rep.foot ne.cfH ne.xCF addr → addr < heap := fun addr ha =>
      hfoot addr (Or.inr (Or.inr (by simp [hxne_b]; exact Or.inr (Or.inl ha))))
    have hCF8_loc := CF.rep_local ne.cfH (fun j => (a.st.trees j).cs) ne.xCF mem st8.mem fun addr ha => by
      change mem addr = stOrd.mem addr
      rw [hOrd_fr addr (by have := hcfFoot_lt addr ha; omega)
        (fun hf => (hd2 addr (by rwa [← hxvCap, ← hxeCap] at hf)).1 ha),
        h5f_lt addr (hcfFoot_lt addr ha)]
    have hCFRep8 : CF.rep.rep ne.cfH (fun j => (a.st.trees j).cs) ne.xCF st8.mem := hCF8_loc.1 hCFRep
    have hCFPhi_eq : CF.rep.phi ne.cfH ne.xCF st8.mem = CF.rep.phi ne.cfH ne.xCF mem := hCF8_loc.2.symm
    have hSB8 : SmallBatchAt st8.mem bCopy (a.st.trees 0).cs.G U words := by
      rw [(hG_br 0 (by omega)).1]
      exact smallBatchAt_of_agree hSB5f fun addr ha1 ha2 =>
        hOrd_fr addr (by omega) (fun hf => by have := hordFoot_lt addr hf; omega)
    have hBw8 : ∀ t < words, st8.mem (bCopy + t) < 2 ^ w := fun t ht => by
      change stOrd.mem (bCopy + t) < 2 ^ w
      rw [hOrd_fr (bCopy + t) (by omega) (fun hf => by have := hordFoot_lt _ hf; omega)]
      exact hBw5f t ht
    have hvCF : CF.vCapOf ne.xCF = vCap := (hCaps ne hxne_b).1.trans hxvCap
    have heCF : CF.eCapOf ne.xCF = eCap := (hCaps ne hxne_b).2.trans hxeCap
    obtain ⟨bodyCF, hbodyCF, oCF, stCF, cCF, xCF', hrunCF, hCFRep', hvCF', heCF', hCF_h1, hfChg_lo,
        hfChg_hi, hChgAt, hSplitAt, hCFResp, hCFCost⟩ :=
      CF.batch_runs ne.cfH bCopy words k M N vCap eCap h1 (fun j => (a.st.trees j).cs) ne.xCF U
        st8.mem st8.pos ω hfmt hk_pos
        (asm_input_cs_k lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
          (canonicalSparsifyParams impl) (dsAmortConst impl) hinp hst_ne 0).symm
        hkCap (Read.sparseCoreOrdInput_cs_G₀_n_le hinp hst_ne 0)
        hcap hwCF hCFRep8 hvCF heCF
        (fun j hj => ((hG_br j (by omega)).1).trans ((hG_br 0 (by omega)).1).symm)
        hSB8 (by rw [(hG_br 0 (by omega)).1]; exact hUval) hUcap hBw8 (by omega)
        (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl | rfl <;> omega)
        (fun addr ha => by have := hcfFoot_lt addr ha; omega) hzOrd (by omega)
    rcases hCFResp with ⟨hCF_lo, hCF_hi, hzCF, hCF_fr, hCF_ft⟩
    let h2 := oCF.value
    let fChgPtr := stCF.mem h1
    have hcallCF : Runs w p ω (.call 14 fCFBatch [.reg 11, .reg 2, .reg 3, .reg 14]) st8 .normal
        { stCF with regs := Function.update st8.regs 14 h2 }
        (argsSize [.reg 11, .reg 2, .reg 3, .reg 14] + cCF + 1) := by
      refine (runs_call_iff (r := 14) (f := fCFBatch) (st := st8) (o := .normal)
        (st' := { stCF with regs := Function.update st8.regs 14 h2 })).mpr
        ⟨[ne.cfH, bCopy, words, h1], bodyCF, oCF, stCF, cCF, ?_, hbodyCF, hrunCF, rfl, rfl, rfl⟩
      simp [evalArgs, Expr.eval, st8, st7, st6, st5, h5f_r2, h5f_r.2.2.1]
    let st9 : State := { stCF with regs := Function.update st8.regs 14 h2 }
    have hload_fChg : Runs w p ω (.assign 13 (.load (.reg 13))) st9 .normal
        { st9 with regs := Function.update st9.regs 13 fChgPtr } _ :=
      runs_assign_iff.mpr ⟨fChgPtr, Expr.eval_load_of_eq (w := w)
        (Expr.eval_reg_of_eq (v := h1) (by simp [st9, st8])) rfl, rfl, rfl, rfl⟩
    let st10 : State := { st9 with regs := Function.update st9.regs 13 fChgPtr }
    have hst_fChg : Runs w p ω
        (.store (.bin .add (.bin .add (.reg 8) (.const 1)) (.bin .mul (.const 6) (.reg 10))) (.reg 13))
        st10 .normal
        { st10 with mem := Function.update st10.mem (heap + 1 + 6 * k) fChgPtr } _ :=
      runs_store_iff.mpr ⟨heap + 1 + 6 * k, fChgPtr,
        Expr.eval_add
          (Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st10, st9, st8, st7, st6, st5, h5f_r.2.2.2.2.2.1]))
            (Expr.eval_const h1w) (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (v := k) (by simp [st10, st9, st8, st7, st6, st5, h5f_r.2.2.2.2.2.2.1])) (by omega))
          (by omega),
        Expr.eval_reg_of_eq (by simp [st10]), rfl, rfl, rfl⟩
    let st10b : State := { st10 with mem := Function.update st10.mem (heap + 1 + 6 * k) fChgPtr }
    have hCF_fr_hdr : ∀ i < ASM_HDR_SIZE, stCF.mem (hndl + i) = mem (hndl + i) := fun i hi => by
      rw [hCF_fr _ (by omega) (fun hf => (hd1 _ ⟨by omega, by omega⟩).2.1 hf), hOrd_fr_hdr i hi]
    have h10b_ne : ∀ addr, addr ≠ heap + 1 + 6 * k → st10b.mem addr = stCF.mem addr := fun addr hne =>
      Function.update_of_ne hne _ _
    have hload_tbl : Runs w p ω (.assign 12 (.load (.bin .add (.reg 0) (.const ASM_HDR_TBL)))) st10b .normal
        { st10b with regs := Function.update st10b.regs 12 ne.tbl } _ :=
      runs_assign_iff.mpr ⟨ne.tbl,
        Expr.eval_load_of_eq (w := w)
          (Expr.eval_add (Expr.eval_reg_of_eq (v := hndl) (by simp [st10b, st10, st9, st8, st7, st6, st5, h5f_r.1]))
            (Expr.eval_const (by unfold ASM_HDR_TBL; omega)) (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega))
          ((h10b_ne _ (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)).trans
            ((hCF_fr_hdr ASM_HDR_TBL (by decide)).trans h10)), rfl, rfl, rfl⟩
    let st11 : State := { st10b with regs := Function.update st10b.regs 12 ne.tbl }
    have hbrFoot_lt : ∀ j < k, ∀ addr, BR.rep.foot (ne.brH j) (ne.xBR j) addr → addr < heap := fun j hj addr ha =>
      hfoot addr (Or.inr (Or.inr (by simp [hxne_b]; exact Or.inr (Or.inr (Or.inr ⟨j, by omega, ha⟩)))))
    have hst11_br : ∀ j < k, ∀ addr, BR.rep.foot (ne.brH j) (ne.xBR j) addr → st11.mem addr = mem addr := fun j hj addr ha => by
      have halt := hbrFoot_lt j hj addr ha
      change st10b.mem addr = mem addr
      rw [h10b_ne addr (by omega),
        hCF_fr addr (by omega) (fun hcf => (hd3 addr hcf).2 j (by omega) ha),
        hOrd_fr addr (by omega) (fun hord => (hd2 addr (by rwa [← hxvCap, ← hxeCap] at hord)).2.2 j (by omega) ha),
        h5f_lt addr halt]
    have hBRRep11 : ∀ j < k, BR.rep.rep (ne.brH j) ⟨a.st.trees j, a.ord, vCap, eCap⟩ (ne.xBR j) st11.mem := fun j hj => by
      rw [← hord_eq, ← hxvCap, ← hxeCap]
      exact (BR.rep_local (ne.brH j) ⟨a.st.trees j, a.st.ord, x.vCap, x.eCap⟩ (ne.xBR j) mem st11.mem
        fun addr ha => (hst11_br j hj addr ha).symm).1 (hBRRep j (by omega))
    have hBRPhi11 : (Finset.range k).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) st11.mem) =
        (Finset.range k).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) mem) :=
      Finset.sum_congr rfl fun j hj => by
        have hjk := Finset.mem_range.mp hj
        exact (BR.rep_local (ne.brH j) ⟨a.st.trees j, a.ord, x.vCap, x.eCap⟩ (ne.xBR j) mem st11.mem
          fun addr ha => (hst11_br j hjk addr ha).symm).2.symm
    have htbl11 : ∀ j < k, st11.mem (ne.tbl + j) = ne.brH j := fun j hj => by
      have hlt : ne.tbl + j < heap :=
        hfoot (ne.tbl + j) (Or.inr (Or.inr (by simp only [hxne_b]; right; right; left; exact ⟨by omega, by omega⟩)))
      change st10b.mem (ne.tbl + j) = ne.brH j
      rw [h10b_ne _ (by omega),
        hCF_fr _ (by omega) (fun hcf => (hd3 _ hcf).1 ⟨by omega, by omega⟩),
        hOrd_fr _ (by omega) (fun hord => (hd2 _ (by rwa [← hxvCap, ← hxeCap] at hord)).2.1 ⟨by omega, by omega⟩),
        h5f_lt _ hlt]
      exact hTbl j (by omega)
    have hSB11 : SmallBatchAt st11.mem bCopy (a.st.trees 0).cs.G U words :=
      smallBatchAt_of_agree hSB8 fun addr ha1 ha2 =>
        (h10b_ne addr (by omega)).trans
          (hCF_fr addr (by omega) (fun hcf => by have := hcfFoot_lt addr hcf; omega))
    have hEd11 : OrdEditsAt st11.mem eCopy ed editWords :=
      ordEditsAt_of_agree hEd5f fun addr ha1 ha2 => by
        change st10b.mem addr = st5f.mem addr
        rw [h10b_ne addr (by omega),
          hCF_fr addr (by omega) (fun hcf => by have := hcfFoot_lt addr hcf; omega),
          hOrd_fr addr (by omega) (fun hord => by have := hordFoot_lt addr hord; omega)]
    have hBw11 : ∀ t < words, st11.mem (bCopy + t) < 2 ^ w := fun t ht => by
      change st10b.mem (bCopy + t) < 2 ^ w
      rw [h10b_ne (bCopy + t) (by omega),
        hCF_fr (bCopy + t) (by omega) (fun hcf => by have := hcfFoot_lt _ hcf; omega)]
      exact hBw8 t ht
    have hEw11 : ∀ t < editWords, st11.mem (eCopy + t) < 2 ^ w := fun t ht => by
      change st10b.mem (eCopy + t) < 2 ^ w
      rw [h10b_ne (eCopy + t) (by omega),
        hCF_fr (eCopy + t) (by omega) (fun hcf => by have := hcfFoot_lt _ hcf; omega),
        hOrd_fr (eCopy + t) (by omega) (fun hord => by have := hordFoot_lt _ hord; omega)]
      exact hEw5f t ht
    have hCFRep11 : CF.rep.rep ne.cfH (fun j => compLSFBatch (a.st.trees j).cs U) xCF' st11.mem :=
      (CF.rep_local ne.cfH (fun j => compLSFBatch (a.st.trees j).cs U) xCF' stCF.mem st11.mem fun addr ha => by
        rcases hCF_ft addr ha with hold | hnew
        · have := hcfFoot_lt addr hold; exact (h10b_ne addr (by omega)).symm
        · exact (h10b_ne addr (by omega)).symm).1 hCFRep'
    have hChgAt11 : CompFamilyChgAt w k st11.mem fChgPtr h2 (fun j => (a.st.trees j).cs) U :=
      compFamilyChgAt_congr (fun addr ha1 _ => (h10b_ne addr (by omega)).symm) hChgAt
    have hSplitAt11 : CompSplitListAt w k st11.mem (fChgPtr + k) h2 (fun j => (a.st.trees j).cs) U :=
      compSplitListAt_congr (fun addr ha1 _ => (h10b_ne addr (by omega)).symm) hSplitAt
    have hz11 : ZeroFrom st11.mem h2 := fun addr ha => (h10b_ne addr (by omega)).trans (hzCF addr ha)
    have hstepArgsW : ∀ v ∈ [ne.cfH, bCopy, words, eCopy, editWords, heap, k, ne.tbl, fChgPtr], v < 2 ^ w := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    let a' := ordUpdateNext fmt L a [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap] mem
    have hmod_eq := asm_updateOrd_of_nonempty lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
      (canonicalSparsifyParams impl) (dsAmortConst impl) a.st hst_ne U
      (readEdgeValues mem lengths fmt.limbBits L fmt.precision (a.G.applyBatch U).E)
      (readEdgeValues mem gradient fmt.limbBits L fmt.precision (a.G.applyBatch U).E) ord'
    have ha'_st : a'.st = { a.st with ord := ord', trees := fun j =>
        (stepBundleTree (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord').state } := by
      have h1 := congrArg Prod.fst hmod_eq; rw [hord_eq] at h1; exact h1
    have ha'_US : (ordUpdateModel fmt L a [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap] mem).2 =
        fun j => (stepBundleTree (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord').U_S := by
      have h2 := congrArg Prod.snd hmod_eq; rw [hord_eq] at h2; exact h2
    have ha'_ne : a'.st.isNonempty = true := by rw [ha'_st]; exact hst_ne
    have hvG_v : ∀ v ∈ a.G.V, v < vCap := by rwa [hxvCap] at hvG
    have heG_e : ∀ e ∈ a.G.E, e < eCap := by rwa [hxeCap] at heG
    obtain ⟨hvG', heG'⟩ := batchWithinCaps_applyBatch hUcap hvG_v heG_e
    have hinp' : SparseCoreOrdInput T k M N a'.st (a.G.applyBatch U) ord' (a.n + U.length) :=
      SparseCoreOrdInput.update hinp U
        (readEdgeValues mem lengths fmt.limbBits L fmt.precision (a.G.applyBatch U).E)
        (readEdgeValues mem gradient fmt.limbBits L fmt.precision (a.G.applyBatch U).E)
        ord' hUval hPosE hOrdB hThr
    have hPreInv : ∀ j < k, AsmBrModelFacts impl vCap eCap (a.st.trees j) a.ord ∧
        BranchUpdatesBelow impl (a.st.trees j) a.n :=
      fun j hj => asm_input_model_inv hk_pos hdepth hγt hvG_v heG_e hinp hst_ne (hInit j hj)
    have hPostInv : ∀ j < k,
        AsmBrModelFacts impl vCap eCap
          (stepBundleTree (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord').state ord' ∧
        BranchUpdatesBelow impl
          (stepBundleTree (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord').state
          (a.n + U.length) := fun j hj => by
      have h := asm_input_model_inv hk_pos hdepth hγt hvG' heG' hinp' ha'_ne (hInit j hj)
      simpa [ha'_st] using h
    obtain ⟨stL, cL, xBR', hrunL, hL_lo, hL_hi, hzL, hL_fr, hBRRep', hBRFt', hBRDisj', hOut', hCostL⟩ :=
      asmStepBranchesLoop_outLayout_runs BR hStepLay (batch := bCopy) (words := words) (edits := eCopy)
        (editWords := editWords) (outPtr := heap) (k := k) (M := M) (N := N) (vCap := vCap)
        (eCap := eCap) (cfH := ne.cfH) (tbl := ne.tbl) (fChgPtr := fChgPtr) (fChgEnd := h2)
        (hStart := h2) (tr := a.st.trees) (ord := a.ord) (cfsOld := fun j => (a.st.trees j).cs)
        (cfsNew := fun j => compLSFBatch (a.st.trees j).cs U) (xcf := xCF') (U := U) (ed := ed)
        (brH := ne.brH) (xCur := ne.xBR) st11 ω
        hfmt hk_pos (fun j hj => ⟨(hinp_mn j).1, (hinp_mn j).2.1, ((hG_br j (by omega)).1).trans ((hG_br 0 (by omega)).1).symm⟩)
        hdepth hdepth_lg hdepth_ch hcap hwBR (by omega) (fun _ _ => rfl) (fun _ _ => rfl)
        (by rw [(hG_br 0 (by omega)).1]; exact hUval) hUcap
        (by rw [(hG_br 0 (by omega)).1]; exact hOrdB) hEdVal
        (by rw [(hG_br 0 (by omega)).1]; exact hEdBlocks)
        (by omega) (by omega) (by omega) (by omega) le_rfl
        (fun addr ha => by rcases hCF_ft addr ha with hold | hnew; exact lt_of_lt_of_le (hcfFoot_lt addr hold) (by omega); exact hnew.2)
        (fun addr ha1 ha2 ha => by rcases hCF_ft addr ha with hold | hnew; exact absurd (hcfFoot_lt addr hold) (by omega); omega)
        (fun addr ha1 ha2 => by omega) (fun addr ha1 ha2 => by omega)
        (fun addr ha1 ha2 => by
          have := hfoot addr (Or.inr (Or.inr (by simp [hxne_b]; exact Or.inr (Or.inr (Or.inl ⟨ha1, by omega⟩))))); omega)
        (fun addr ha1 ha2 => by omega)
        hstepArgsW
        (fun j hj => by have := hbrLt j (by omega); omega)
        (by omega) hThr (fun j hj => (hPreInv j hj).2) (fun j hj => (hPostInv j hj).2)
        (fun j hj => (hPreInv j hj).1) (fun j hj => (hPostInv j hj).1)
        (by simp [st11, st10b, st10, st9, st8, st7, st6, st5, h5f_r2])
        (by simp [st11, st10b, st10, st9, st8, st7, st6, st5, h5f_r.2.2.1])
        (by simp [st11, st10b, st10, st9, st8, st7, st6, st5, h5f_r4])
        (by simp [st11, st10b, st10, st9, st8, st7, st6, st5, h5f_r.2.2.2.2.1])
        (by simp [st11, st10b, st10, st9, st8, st7, st6, st5, h5f_r.2.2.2.2.2.1])
        (by simp [st11, st10b, st10, st9, st8, st7, st6, st5, h5f_r.2.2.2.2.2.2.1])
        (by simp [st11, st10b, st10, st9, st8, st7])
        (by simp [st11]) (by simp [st11, st10b, st10]) (by simp [st11, st10b, st10, st9])
        hz11 hCFRep11 hChgAt11 hSplitAt11 hSB11 hEd11 hBw11 hEw11 htbl11 hBRRep11
        (fun j hj addr ha => by
          have halt := hbrFoot_lt j hj addr ha
          refine ⟨by omega, fun hcf => ?_, by omega,
            fun htb => (hd4 addr ⟨htb.1, by omega⟩ j (by omega) ha), by omega, by omega, by omega⟩
          rcases hCF_ft addr hcf with hold | hnew
          · exact (hd3 addr hold).2 j (by omega) ha
          · omega)
        (fun j₁ h₁ j₂ h₂ hne addr ha1 ha2 => hd5 j₁ (by omega) j₂ (by omega) hne addr ha1 ha2)
    let h3 := stL.regs 14
    have hret : Runs w p ω (.ret (.reg 14)) stL (.returned h3) stL _ :=
      runs_ret_iff.mpr ⟨h3, Expr.eval_reg_of_eq rfl, rfl, rfl, rfl⟩
    have hrest_runs : Runs w p ω _ st5f (.returned h3) stL _ :=
      runs_seq_iff.mpr (Or.inr ⟨st5, _, _, hload_ordH,
        runs_seq_iff.mpr (Or.inr ⟨st6, _, _, hcallOrd,
          runs_seq_iff.mpr (Or.inr ⟨st7, _, _, hload_cfH,
            runs_seq_iff.mpr (Or.inr ⟨st8, _, _, ha13_h1,
              runs_seq_iff.mpr (Or.inr ⟨st9, _, _, hcallCF,
                runs_seq_iff.mpr (Or.inr ⟨st10, _, _, hload_fChg,
                  runs_seq_iff.mpr (Or.inr ⟨st10b, _, _, hst_fChg,
                    runs_seq_iff.mpr (Or.inr ⟨st11, _, _, hload_tbl,
                      runs_seq_iff.mpr (Or.inr ⟨stL, _, _, hrunL, hret, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
                rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    obtain ⟨cTh, hthen, hcTh⟩ := hcp_wrap _ _ _ _ hrest_runs
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopUpdateBody (b + 20) (b + 21) (ordStoreOp b 0) fCFBatch bp.fStep) st0
          (.returned h3) stL cF ∧ cF ≤ 17 * words + 17 * editWords + cOrd + cCF + cL + 190 := by
      unfold asmTopUpdateBody
      refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, hload9,
        runs_seq_iff.mpr (Or.inr ⟨st2, _, _, hload10,
          runs_cond_iff.mpr ⟨1, _, Expr.eval_reg_of_eq (v := 1) (by simp [st2, st1, hxne_b]),
            by simp only [one_ne_zero, ↓reduceIte]; exact hthen, rfl⟩, rfl⟩), rfl⟩), ?_⟩
      simp only [argsSize_cons, argsSize_nil, Expr.size] at hcTh ⊢; omega
    let ne' : AsmTopNE CF.rep.τ BR.rep.τ := { ne with xOrd := xOrd', xCF := xCF', xBR := xBR' }
    let x' : R.τ := { x with ne := some ne' }
    have hL_fr_hdr : ∀ i < ASM_HDR_SIZE, stL.mem (hndl + i) = mem (hndl + i) := fun i hi => by
      rw [hL_fr _ (by omega) (fun j hj hf => (hd1 _ ⟨by omega, by omega⟩).2.2.2 j (by omega) hf) (by omega)]
      exact (h10b_ne _ (by unfold ASM_HDR_SIZE at *; omega)).trans (hCF_fr_hdr i hi)
    have hOrdRepL : (ordStoreRep x.vCap x.eCap).rep ne.ordH ord' xOrd' stL.mem := by
      rw [hxvCap, hxeCap]
      refine (ordStoreRep_local vCap eCap ne.ordH ord' xOrd' stOrd.mem stL.mem fun addr ha => ?_).1 hOrdRep'
      have halt := hordFoot_lt addr ha
      have ha_x : (ordStoreRep x.vCap x.eCap).foot ne.ordH ne.xOrd addr := by rwa [hxvCap, hxeCap]
      rw [hL_fr addr (by omega) (fun j hj hbr => (hd2 addr ha_x).2.2 j (by omega) hbr) (by omega)]
      exact ((h10b_ne addr (by omega)).trans (hCF_fr addr (by omega) (fun hcf => (hd2 addr ha_x).1 hcf))).symm
    have hCF_loc := CF.rep_local ne.cfH (fun j => compLSFBatch (a.st.trees j).cs U) xCF' stCF.mem stL.mem fun addr ha => by
      rcases hCF_ft addr ha with hold | hnew
      · have hlt := hcfFoot_lt addr hold
        rw [hL_fr addr (by omega) (fun j hj hbr => (hd3 addr hold).2 j (by omega) hbr) (by omega)]
        exact (h10b_ne addr (by omega)).symm
      · rw [hL_fr addr hnew.2 (fun j hj hbr => by have := hbrFoot_lt j hj addr hbr; omega) (by omega)]
        exact (h10b_ne addr (by omega)).symm
    have hCFRepL : CF.rep.rep ne.cfH (fun j => compLSFBatch (a.st.trees j).cs U) xCF' stL.mem := hCF_loc.1 hCFRep'
    have hCFPhiL : CF.rep.phi ne.cfH xCF' stL.mem = CF.rep.phi ne.cfH xCF' stCF.mem := hCF_loc.2.symm
    have hΔcost : T.cost a'.st - T.cost a.st =
        (Finset.range k).sum fun j =>
          branchStepCharge (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord' := by
      have hup := asm_update_cost_eq lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) a.st hst_ne U
        (readEdgeValues mem lengths fmt.limbBits L fmt.precision (a.G.applyBatch U).E)
        (readEdgeValues mem gradient fmt.limbBits L fmt.precision (a.G.applyBatch U).E) ord'
      rw [hinp_k, hord_eq] at hup
      have h1 : T.cost a'.st = T.cost a.st +
          (Finset.range k).sum fun j =>
            branchStepCharge (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord' := hup
      omega
    have hSj : ∀ j < k, T.S a.st j = (a.st.trees j).S_cur := fun j _ => by
      change (if a.st.isNonempty then (a.st.trees j).S_cur else emptyGraph) = _; simp [hst_ne]
    have hrotj : ∀ j < k, T.rot a.st j = (a.st.trees j).outOrder a.ord := fun j _ => by
      change (if a.st.isNonempty then (a.st.trees j).outOrder a.st.ord else fun _ => []) = _
      simp [hst_ne, hord_eq]
    have hrotj' : ∀ j < k, T.rot a'.st j =
        (stepBundleTree (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord').state.outOrder ord' :=
      fun j _ => by
        change (if a'.st.isNonempty then (a'.st.trees j).outOrder a'.st.ord else fun _ => []) = _
        rw [ha'_st]; simp [hst_ne]
    have hlsfj : ∀ j < k, T.lsfs a.st j = (a.st.trees j).cs.lsf := fun j _ => by
      change (if a.st.isNonempty then (a.st.trees j).cs.lsf else emptyLSF) = _; simp [hst_ne]
    have hlsfj' : ∀ j < k, T.lsfs a'.st j = (compLSFBatch (a.st.trees j).cs U).lsf := fun j _ => by
      change (if a'.st.isNonempty then (a'.st.trees j).cs.lsf else emptyLSF) = _
      rw [ha'_st]; simp [hst_ne, stepBundleTree]
    refine ⟨.returned h3, stL, cF, x', hfull, ⟨?_, fun h => by simp [x'] at h,
      fun ne₁ hne₁ => by cases Option.some.inj hne₁.symm; exact ⟨by rw [hxvCap]; exact hvCF', by rw [hxeCap]; exact heCF'⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- R.rep hndl a' x' stL.mem
      refine ⟨⟨by rw [ha'_st]; simpa [x', hxne_b] using hxne, by rw [ha'_st]; exact hxk, hxres,
        by simpa [x', hxne_b] using (hL_fr_hdr ASM_HDR_NE (by decide)).trans hm0,
        (hL_fr_hdr ASM_HDR_K (by decide)).trans hm1, (hL_fr_hdr ASM_HDR_M (by decide)).trans hm2,
        (hL_fr_hdr ASM_HDR_N (by decide)).trans hm3, (hL_fr_hdr ASM_HDR_VCAP (by decide)).trans hm4,
        (hL_fr_hdr ASM_HDR_ECAP (by decide)).trans hm5, (hL_fr_hdr ASM_HDR_L (by decide)).trans hm6,
        (hL_fr_hdr ASM_HDR_PFP (by decide)).trans hm7,
        (hL_fr_hdr ASM_HDR_EMPTYG (by decide)).trans he0, (hL_fr_hdr (ASM_HDR_EMPTYG + 1) (by decide)).trans he1,
        (hL_fr_hdr (ASM_HDR_EMPTYG + 2) (by decide)).trans he2, (hL_fr_hdr (ASM_HDR_EMPTYG + 3) (by decide)).trans he3,
        fun ne₁ hne₁ => ?_⟩, hxL, hxPfp, hxvCap, hxeCap, hxwM, hxcap, hxk_pos⟩
      have hne_eq : ne₁ = ne' := Option.some.inj hne₁.symm; subst hne_eq
      refine ⟨(hL_fr_hdr ASM_HDR_ORDH (by decide)).trans h8, (hL_fr_hdr ASM_HDR_CFH (by decide)).trans h9,
        (hL_fr_hdr ASM_HDR_TBL (by decide)).trans h10, hcfLt, htblLt, hbrLt,
        by dsimp only [x']; rw [hxvCap]; exact hvG', by dsimp only [x']; rw [hxeCap]; exact heG', ?_,
        by rw [ha'_st]; exact hOrdRepL, by rw [ha'_st]; exact hCFRepL, ?_,
        by rw [ha'_st]; intro j hj; dsimp only [x']; rw [hxvCap, hxeCap]; exact hBRRep' j (by dsimp only [x'] at hj; omega),
        ?_, ?_, ?_, ?_, fun j₁ h₁ j₂ h₂ hne addr ha1 ha2 =>
          hBRDisj' j₁ (by dsimp only [x'] at h₁; omega) j₂ (by dsimp only [x'] at h₂; omega) hne addr ha1 ha2⟩
      · intro j hj; rw [ha'_st]
        exact ⟨by change (compLSFBatch (a.st.trees j).cs U).G = a.G.applyBatch U; rw [compLSFBatch_G, (hG_br j hj).1],
          (hG_br j hj).2.1, (hG_br j hj).2.2⟩
      · intro j hj
        have hjk : j < k := by dsimp only [x'] at hj; omega
        rw [hL_fr (ne.tbl + j) (by have := htblLt; omega) (fun j' hj' hbr => hd4 _ ⟨by omega, by omega⟩ j' (by omega) hbr)
          (by have := hfoot (ne.tbl + j) (Or.inr (Or.inr (by simp only [hxne_b]; right; right; left; exact ⟨by omega, by omega⟩))); omega)]
        exact htbl11 j hjk
      · intro addr ha
        refine ⟨(hd1 addr ha).1, ?_, (hd1 addr ha).2.2.1, fun j hj hbr => ?_⟩
        · intro hcf; rcases hCF_ft addr hcf with hold | hnew; exact (hd1 addr ha).2.1 hold; omega
        · have hjk : j < k := by dsimp only [x'] at hj; omega
          rcases hBRFt' j hjk addr hbr with hold | hnew; exact (hd1 addr ha).2.2.2 j hj hold; omega
      · intro addr ha
        have halt := hordFoot_lt addr (by rwa [hxvCap, hxeCap] at ha)
        refine ⟨?_, (hd2 addr ha).2.1, fun j hj hbr => ?_⟩
        · intro hcf; rcases hCF_ft addr hcf with hold | hnew; exact (hd2 addr ha).1 hold; omega
        · have hjk : j < k := by dsimp only [x'] at hj; omega
          rcases hBRFt' j hjk addr hbr with hold | hnew; exact (hd2 addr ha).2.2 j hj hold; omega
      · intro addr ha
        refine ⟨?_, fun j hj hbr => ?_⟩
        · intro htb
          have hlt := hfoot addr (Or.inr (Or.inr (by simp [hxne_b]; exact Or.inr (Or.inr (Or.inl htb)))))
          rcases hCF_ft addr ha with hold | hnew; exact (hd3 addr hold).1 htb; omega
        · have hjk : j < k := by dsimp only [x'] at hj; omega
          rcases hCF_ft addr ha with hold | hnew
          · rcases hBRFt' j hjk addr hbr with holdB | hnewB
            · exact (hd3 addr hold).2 j hj holdB
            · have := hcfFoot_lt addr hold; omega
          · rcases hBRFt' j hjk addr hbr with holdB | hnewB
            · have := hbrFoot_lt j hjk addr holdB; omega
            · omega
      · intro addr htb j hj hbr
        have hjk : j < k := by dsimp only [x'] at hj; omega
        have hlt := hfoot addr (Or.inr (Or.inr (by simp [hxne_b]; exact Or.inr (Or.inr (Or.inl htb)))))
        rcases hBRFt' j hjk addr hbr with hold | hnew; exact hd4 addr htb j hj hold; omega
    · -- D.post 0 (KFBL)
      have hheap_k : stL.mem heap = k := by
        rw [hL_fr heap (by omega) (fun j hj hbr => by have := hbrFoot_lt j hj heap hbr; omega) (by omega)]
        exact (h10b_ne heap (by omega)).trans
          (by rw [hCF_fr heap (by omega) (fun hcf => by have := hcfFoot_lt heap hcf; omega),
            hOrd_fr heap (by omega) (fun hord => by have := hordFoot_lt heap hord; omega), h5f_heap])
      refine ⟨⟨rfl, ⟨hheap_k, fun j hj => ?_⟩⟩, fun j hj => ?_, fun j hj => ?_⟩
      · obtain ⟨hSBj, -, -, ⟨outEd, hOE, hApply, -, -⟩, -⟩ := hOut' j hj
        rw [hSj j hj, ha'_US, hrotj j hj, hrotj' j hj]
        exact ⟨hSBj, ⟨outEd, hOE, hApply⟩⟩
      · obtain ⟨-, -, -, ⟨outEd, hOE, -, -, hFB⟩, -⟩ := hOut' j hj
        change OrdEditsForBatch (T.S a.st j) _ (readOrdEdits stL.mem (stL.mem (heap + 3 + 4 * j)))
        rw [hSj j hj, ha'_US, hOE.1]; exact hFB
      · obtain ⟨-, -, -, ⟨outEd, hOE, -, hV, -⟩, -⟩ := hOut' j hj
        change OrdEditsValidFor vCap eCap (T.rot a.st j) (readOrdEdits stL.mem (stL.mem (heap + 3 + 4 * j)))
        rw [hrotj j hj, hOE.1]; exact hV
    · -- BranchOutFChgAt (nonempty)
      have hfChg_slot : stL.mem (heap + 1 + 6 * k) = fChgPtr := by
        rw [hL_fr (heap + 1 + 6 * k) (by omega)
          (fun j hj hbr => by have := hbrFoot_lt j hj _ hbr; omega) (by omega)]
        exact Function.update_self (heap + 1 + 6 * k) fChgPtr st10.mem
      have hChgAtL : CompFamilyChgAt w k stL.mem fChgPtr h2 (fun j => (a.st.trees j).cs) U :=
        compFamilyChgAt_congr (fun addr ha1 ha2 =>
          (hL_fr addr ha2 (fun j hj hbr => by have := hbrFoot_lt j hj addr hbr; omega)
            (by omega)).symm) hChgAt11
      obtain ⟨hfk_le, hChgW, chg, hchg⟩ := hChgAtL
      refine ⟨by dsimp only [Outcome.value]; omega, by rw [hfChg_slot]; omega,
        by rw [hfChg_slot]; dsimp only [Outcome.value]; omega, fun j hj => ?_⟩
      obtain ⟨hAt, hEx, hp1, hp2⟩ := hchg j hj
      refine ⟨chg j, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfChg_slot]; exact hAt
      · rw [hlsfj j hj, hlsfj' j hj]; exact hEx
      · rw [hfChg_slot]; omega
      · rw [hfChg_slot]; dsimp only [Outcome.value]; omega
      · exact lsfChange_fDel_lt_of_compFamilyChgAt hChgW hAt hp1 hp2
    · -- Per-branch output slots (nonempty)
      intro j hj
      obtain ⟨hSBj, hbLo, hbHi, ⟨outEd, hOE, -, -, -⟩, heLo, heHi, -, -, heLt, hDisjB, hDisjE, heW⟩ :=
        hOut' j hj
      have hb0_eq : heap + 1 + 4 * j = heap + 1 + 4 * j := rfl
      have hb1_eq : heap + 1 + 4 * j + 1 = heap + 2 + 4 * j := by omega
      have hb2_eq : heap + 1 + 4 * j + 2 = heap + 3 + 4 * j := by omega
      have hb3_eq : heap + 1 + 4 * j + 3 = heap + 4 + 4 * j := by omega
      have hWget : [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap].getD 3 0 = words := rfl
      have hEWget : [hndl, graph, batch, words, edits, editWords, lengths, gradient, heap].getD 5 0 = editWords := rfl
      have hGeq : (a.st.trees j).cs.G = a.G := (hG_br j (by omega)).1
      have hready_j := asmBr_outStepReady (fun _ => canonicalSparsify impl)
        (hPreInv j hj).1 (hPostInv j hj).1 (hGeq ▸ hUval) (hGeq ▸ hOrdB)
      obtain ⟨-, -, -, -, -, hUS_val⟩ :=
        outStep_rotations (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord' hready_j
      have hUS_V : ∀ v ∈ ((a.st.trees j).S_cur.applyBatch
          (stepBundleTree (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord').U_S).V,
          v < vCap := by
        intro v hv
        have hVeq : ((a.st.trees j).S_cur.applyBatch
            (stepBundleTree (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord').U_S).V =
            (stepBundleTree (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord').state.cs.RF.R :=
          outStep_V (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord' hready_j
        rw [hVeq] at hv
        exact asmBr_newRoots_lt (fun _ => canonicalSparsify impl) (hPostInv j hj).1 v hv
      have hUS_E : ∀ e ∈ (a.st.trees j).S_cur.E, e < eCap :=
        (hPreInv j hj).1.2.2.2.2.2.2.2.2.2
      have hUS_ins : ∀ e x y, Update.insert e x y ∈
          (stepBundleTree (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord').U_S →
          e < eCap := fun e x y hm =>
        stepBundleTree_U_S_insert_lt (hPreInv j hj).1 (hPostInv j hj).1 (hGeq ▸ hUval) (hGeq ▸ hOrdB) hm
      have hVltW : vCap < 2 ^ w := by
        have := Nat.le_self_pow (show 2 ≠ 0 by decide) (vCap + eCap + 2); omega
      have hEltW : eCap < 2 ^ w := by
        have := Nat.le_self_pow (show 2 ≠ 0 by decide) (vCap + eCap + 2); omega
      have hfoot_ge_h2 : ∀ addr, h2 ≤ addr →
          (∀ j' < k, ¬ BR.rep.foot (ne.brH j') (xBR' j') addr) → ¬ R.foot hndl x' addr := by
        intro addr hge hnoBR hft
        rcases hft with h1 | h2f | h3f
        · have := hfoot addr (Or.inl h1); omega
        · have := hfoot addr (Or.inr (Or.inl h2f)); omega
        · rcases h3f with ha | hb | hc | ⟨j', hj', hd⟩
          · have := hordFoot_lt addr (by rwa [hxvCap, hxeCap] at ha); omega
          · rcases hCF_ft addr hb with hold | hnew
            · have := hcfFoot_lt addr hold; omega
            · omega
          · have := hfoot addr (Or.inr (Or.inr (by simp [hxne_b]; exact Or.inr (Or.inr (Or.inl hc))))); omega
          · exact hnoBR j' (by dsimp only [x'] at hj'; omega) hd
      refine ⟨by dsimp only [Outcome.value]; omega,
        by omega, by rw [hb1_eq]; dsimp only [Outcome.value]; omega,
        by rw [hb2_eq]; omega, by rw [hb2_eq, hb3_eq]; dsimp only [Outcome.value]; omega,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hb1_eq]
        exact batchAt_words_lt hSBj.1 hUS_val hUS_V hUS_E hUS_ins (by omega) hVltW hEltW (by omega)
      · rw [hb2_eq, hb3_eq]; exact heLt
      · intro t ht
        rw [hb1_eq] at ht
        exact hfoot_ge_h2 _ (by omega) (fun j' hj' => hDisjB j' hj' t ht)
      · intro t ht
        rw [hb3_eq] at ht
        rw [hb2_eq]
        exact hfoot_ge_h2 _ (by omega) (fun j' hj' => hDisjE j' hj' t ht)
      · rw [hSj j hj, ha'_US]
        exact decodeBatch_eq_of_batchAt hSBj.1
          (stepBundleTree_U_S_splitEndsExact (hPreInv j hj).1 (hGeq ▸ hUval) (hGeq ▸ hOrdB))
      · rw [hb3_eq, hWget, hEWget, hΔcost]
        have hch_le : branchStepCharge (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord' ≤
            (Finset.range k).sum fun j' =>
              branchStepCharge (fun _ => canonicalSparsify impl) (a.st.trees j') U a.ord ord' :=
          Finset.single_le_sum (f := fun j' => branchStepCharge (fun _ => canonicalSparsify impl)
            (a.st.trees j') U a.ord ord') (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
        dsimp only [ord'] at hch_le ⊢
        exact heW.trans (Nat.mul_le_mul_left edMul (by omega))
    · -- R.Respects
      refine ⟨by simp [Outcome.value]; omega,
        by simp [Outcome.value, alloc, asmTopAlloc]; omega,
        by simpa [Outcome.value] using hzL, ?_, ?_⟩
      · intro addr ha hnf
        have hnoOrd : ¬ ordFoot ne.ordH vCap eCap addr := fun h =>
          hnf (Or.inr (Or.inr (by simp [hxne_b]; exact Or.inl (by rwa [hxvCap, hxeCap]))))
        have hnoCF : ¬ CF.rep.foot ne.cfH ne.xCF addr := fun h =>
          hnf (Or.inr (Or.inr (by simp [hxne_b]; exact Or.inr (Or.inl h))))
        have hnoBR : ∀ j < k, ¬ BR.rep.foot (ne.brH j) (ne.xBR j) addr := fun j hj h =>
          hnf (Or.inr (Or.inr (by simp [hxne_b]; exact Or.inr (Or.inr (Or.inr ⟨j, by omega, h⟩)))))
        rw [hL_fr addr (by omega) hnoBR (by omega)]
        exact (h10b_ne addr (by omega)).trans
          (by rw [hCF_fr addr (by omega) hnoCF, hOrd_fr addr (by omega) hnoOrd, h5f_lt addr ha])
      · intro addr ha
        rcases ha with h1 | h2 | h3
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr (Or.inl h2))
        · rcases h3 with h3a | h3b | h3c | ⟨j, hj, h3d⟩
          · exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; exact Or.inl h3a)))
          · rcases hCF_ft addr h3b with hold | hnew
            · exact Or.inl (Or.inr (Or.inr (by simp [hxne_b, hold])))
            · exact Or.inr ⟨by omega, by simp [Outcome.value]; omega⟩
          · exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; right; right; left; exact h3c)))
          · have hjk : j < k := by dsimp only [x'] at hj; omega
            rcases hBRFt' j hjk addr h3d with hold | hnew
            · exact Or.inl (Or.inr (Or.inr (by simp only [hxne_b]; right; right; right; exact ⟨j, hj, hold⟩)))
            · exact Or.inr ⟨by omega, by simp [Outcome.value]; omega⟩
    · -- Cost bound
      set Δ := (Finset.range k).sum fun j =>
        branchStepCharge (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord'
      set W := (words + editWords + 1) * bundleLogFactor M N
      have hOrdCost' : cOrd + (ordStoreRep vCap eCap).phi ne.ordH xOrd' stOrd.mem ≤
          ordStoreMul * (editWords + 1) * ordStoreLog eCap +
            (ordStoreRep vCap eCap).phi ne.ordH ne.xOrd st5.mem := by
        simpa [ordStoreCapContract] using hOrdCost
      have hOrdLog := ordStoreLog_le_capExp_mul_lg hcap
      have hOrdBound : ordStoreMul * (editWords + 1) * ordStoreLog eCap ≤
          32000 * (capExp + 1) * ((k + 1) * W) := by
        calc ordStoreMul * (editWords + 1) * ordStoreLog eCap
            ≤ 32000 * (words + editWords + 1) * ((capExp + 1) * bundleLogFactor M N) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (le_trans hOrdLog (Nat.mul_le_mul_right _ (by omega)))
          _ = 32000 * (capExp + 1) * W := by dsimp only [W]; ring
          _ ≤ 32000 * (capExp + 1) * ((k + 1) * W) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      have hLSFBound := sum_lsfBatchSize_le_sum_branchStepCharge_op0 (k := k)
        (sparsify := fun _ => canonicalSparsify impl) (tr := a.st.trees) (U := U) (ord := a.ord) (ord' := ord')
        (fun j _ => ⟨(hinp_mn j).1, (hinp_mn j).2.1⟩)
      have hCFBound : CFS.mul capExp limbMul * ((Finset.range k).sum (fun j => lsfBatchSize (a.st.trees j).cs U) +
          (k + 1) * (words + 1)) * bundleLogFactor M N ≤
          CFS.mul capExp limbMul * (Δ + (k + 1) * W) := by
        calc CFS.mul capExp limbMul * ((Finset.range k).sum (fun j => lsfBatchSize (a.st.trees j).cs U) +
              (k + 1) * (words + 1)) * bundleLogFactor M N
            = CFS.mul capExp limbMul * (((Finset.range k).sum (fun j => lsfBatchSize (a.st.trees j).cs U)) *
                bundleLogFactor M N + (k + 1) * ((words + 1) * bundleLogFactor M N)) := by ring
          _ ≤ CFS.mul capExp limbMul * (Δ + (k + 1) * W) :=
              Nat.mul_le_mul_left _ (Nat.add_le_add hLSFBound
                (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))))
      have hBRSum : (Finset.range k).sum (fun j => BRS.mul capExp limbMul *
          (branchStepCharge (fun _ => canonicalSparsify impl) (a.st.trees j) U a.ord ord' + W)) =
          BRS.mul capExp limbMul * (Δ + k * W) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
      have hBRBound : BRS.mul capExp limbMul * (Δ + k * W) ≤ BRS.mul capExp limbMul * (Δ + (k + 1) * W) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
      have hOvh : 17 * words + 17 * editWords + 70 * k + 220 ≤ 400 * ((k + 1) * W) := by
        have hW_ge : words + editWords + 1 ≤ W := Nat.le_mul_of_pos_right _ hlg_pos
        have hkW : (k + 1) * (words + editWords + 1) ≤ (k + 1) * W := Nat.mul_le_mul_left _ hW_ge
        have hlin : words + editWords + k + 1 ≤ (k + 1) * (words + editWords + 1) := by
          rw [Nat.add_one_mul]; have := Nat.le_mul_of_pos_right k (show 0 < words + editWords + 1 by omega); omega
        omega
      have hphi_new : R.phi hndl x' stL.mem = (ordStoreRep vCap eCap).phi ne.ordH xOrd' stOrd.mem +
          CF.rep.phi ne.cfH xCF' stCF.mem + (Finset.range k).sum (fun j => BR.rep.phi (ne.brH j) (xBR' j) stL.mem) := by
        simp only [R, asmTopRepEq, asmTopPhi, x', ne', hxvCap, hxeCap, hk_eq, hCFPhiL]; rfl
      have hphi_old : R.phi hndl x mem = (ordStoreRep vCap eCap).phi ne.ordH ne.xOrd st5.mem +
          CF.rep.phi ne.cfH ne.xCF st8.mem + (Finset.range k).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) st11.mem) := by
        simp only [R, asmTopRepEq, asmTopPhi, hxne_b, hk_eq, hCFPhi_eq, hBRPhi11]; rfl
      have hPmul : (32000 * (capExp + 1) + CFS.mul capExp limbMul + BRS.mul capExp limbMul + 400) * (Δ + (k + 1) * W) ≤
          P.mul * (Δ + (k + 1) * W) := Nat.mul_le_mul_right _ (by simp only [P, asmTopParams]; omega)
      change cF + R.phi hndl x' stL.mem ≤ P.mul * (T.cost a'.st - T.cost a.st + (k + 1) * (words + editWords + 1) * bundleLogFactor M N) + R.phi hndl x mem
      rw [Nat.mul_assoc (k + 1), hΔcost, hphi_new, hphi_old]; rw [hBRSum] at hCostL
      change cF + ((ordStoreRep vCap eCap).phi ne.ordH xOrd' stOrd.mem + CF.rep.phi ne.cfH xCF' stCF.mem +
          (Finset.range k).sum (fun j => BR.rep.phi (ne.brH j) (xBR' j) stL.mem)) ≤ P.mul * (Δ + (k + 1) * W) +
          ((ordStoreRep vCap eCap).phi ne.ordH ne.xOrd st5.mem + CF.rep.phi ne.cfH ne.xCF st8.mem +
           (Finset.range k).sum (fun j => BR.rep.phi (ne.brH j) (ne.xBR j) st11.mem))
      have hdist : (32000 * (capExp + 1) + CFS.mul capExp limbMul + BRS.mul capExp limbMul + 400) * (Δ + (k + 1) * W) =
          32000 * (capExp + 1) * (Δ + (k + 1) * W) + CFS.mul capExp limbMul * (Δ + (k + 1) * W) +
          BRS.mul capExp limbMul * (Δ + (k + 1) * W) + 400 * (Δ + (k + 1) * W) := by ring
      have hOrdBig : 32000 * (capExp + 1) * ((k + 1) * W) ≤ 32000 * (capExp + 1) * (Δ + (k + 1) * W) := Nat.mul_le_mul_left _ (by omega)
      have hOvhBig : 400 * ((k + 1) * W) ≤ 400 * (Δ + (k + 1) * W) := Nat.mul_le_mul_left _ (by omega)
      omega
    · intro j hj
      obtain ⟨-, -, -, -, -, -, hrLo, hrHi, -⟩ := hOut' j hj
      dsimp only [Outcome.value]; exact ⟨by omega, hrHi⟩

end MinCostFlow.SparseCore.Program
