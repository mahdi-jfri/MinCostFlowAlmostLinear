module

public import MinCostFlow.SparseCore.Program.AssemblyTopProcs
public import MinCostFlow.SparseCore.Program.AssemblyContractLayout

import MinCostFlow.SparseCore.Program.AssemblyInputInv

/-!
# Verification of `init` for the top-layer sparse-core program (`AssemblyTopInit`)

Proves `asmTop_init_runs`: executing `asmTopInitBody` meets the `init` clause of
`sparseCoreOrdMachineContractKFR` (and `KF`) with the representation `asmTopRep`:
* On an empty graph (`G.n = 0`), writes the header with `isNonempty = 0` and reserves
  `[heap + 20, heap + 20 + M + N + k + vCap + eCap + L + 20)` in `O(1)` time.
* On a nonempty graph (`G.n > 0`), runs `asmCompactOrdBody_runs` (linear time, no log factor),
  the real P1 `ordStore_implements_cap` initializer on the compacted order (bounded by
  `32000 * 6 * capExp * (G.m + 1) * bundleLogFactor M N`), P4 `CF.init_runs`, and
  `asmInitBranchesLoop_runs` over all `k` branches, then reserves the trailing footprint block.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

/-- Every rotation order of a graph `G` represented by `DynGraphAt mem graph vCap eCap G` satisfies
`OrdUniqueWithin vCap eCap ord`. -/
private theorem asmInit_ordUniqueWithin_of_rotation {mem : ℕ → ℕ} {graph vCap eCap : ℕ} {G : MGraph}
    {ord : ℕ → List End} (hG : DynGraphAt mem graph vCap eCap G) (hrot : IsRotationOrder G ord) :
    OrdUniqueWithin vCap eCap ord := by
  obtain ⟨ρ, rfl⟩ := hrot
  have hval := hG.1
  have hvlt := hG.2.1
  have helt := hG.2.2.1
  refine ⟨⟨ρ.nodup, fun v hv => ?_, fun v x hx => helt x.1 ((ρ.mem_order v x).mp hx).1⟩,
    fun u v x hu hv => ((ρ.mem_order u x).mp hu).2.symm.trans ((ρ.mem_order v x).mp hv).2⟩
  cases h : ρ.order v with
  | nil => rfl
  | cons x xs =>
    have hmem : x ∈ ρ.order v := by simp [h]
    obtain ⟨he, hsrc⟩ := (ρ.mem_order v x).mp hmem
    have hvV : v ∈ G.V := by
      rw [← hsrc]; unfold MGraph.src; cases x.2
      · exact (hval x.1 he).2
      · exact (hval x.1 he).1
    exact absurd (hvlt v hvV) (by omega)

private theorem init_machCost_bounds {lsfInit : LSFInit} {depth : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {params : ℕ → SparsifyParams} {spanConst : ℕ}
    {k M N : ℕ} {G : MGraph} {ℓ₀ : ℕ → ℝ} {ord : ℕ → List End} (hk : 0 < k) :
    let S := (Finset.range k).sum fun j =>
      (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j).machCost
    (G.m + 1) * bundleLogFactor M N ≤ S ∧
    k * lsfInitSize G * bundleLogFactor M N ^ 3 ≤ S ∧
    k ≤ S ∧
    k * ((G.m + 1) * bundleLogFactor M N) ≤ S := by
  intro S
  have hlg : 1 ≤ bundleLogFactor M N := le_trans (by omega) (logStep_le_bundleLogFactor M N)
  have hterm : ∀ j, (G.m + 1) * bundleLogFactor M N ≤
      (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j).machCost ∧
      lsfInitSize G * bundleLogFactor M N ^ 3 ≤
      (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j).machCost ∧
      1 ≤ (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j).machCost := by
    intro j
    rw [initBundleTreeWithParams_machCost]
    refine ⟨Nat.mul_le_mul_right _ (by omega), ?_, ?_⟩
    · calc lsfInitSize G * bundleLogFactor M N ^ 3
          = (lsfInitSize G * bundleLogFactor M N ^ 2) * bundleLogFactor M N := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    · exact le_trans (by omega) (Nat.mul_le_mul (by omega : 1 ≤ 3 * G.m + 3 * (activeSubgraph G).n + 2 + _ + _) hlg)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h0 : 0 ∈ Finset.range k := Finset.mem_range.mpr hk
    exact le_trans (hterm 0).1 (Finset.single_le_sum (f := fun j =>
      (initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j).machCost) (fun _ _ => Nat.zero_le _) h0)
  · calc k * lsfInitSize G * bundleLogFactor M N ^ 3
        = (Finset.range k).sum (fun _ => lsfInitSize G * bundleLogFactor M N ^ 3) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring
      _ ≤ S := Finset.sum_le_sum fun j _ => (hterm j).2.1
  · calc k = (Finset.range k).sum (fun _ => 1) := by simp
      _ ≤ S := Finset.sum_le_sum fun j _ => (hterm j).2.2
  · calc k * ((G.m + 1) * bundleLogFactor M N)
        = (Finset.range k).sum (fun _ => (G.m + 1) * bundleLogFactor M N) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ S := Finset.sum_le_sum fun j _ => (hterm j).1

private theorem readOrdRecords_of_agree {mem₁ mem₂ : ℕ → ℕ} :
    ∀ cnt a, (∀ x, a ≤ x → x < a + ordRecordsWords (readOrdRecords mem₁ cnt a) → mem₂ x = mem₁ x) →
      readOrdRecords mem₂ cnt a = readOrdRecords mem₁ cnt a
  | 0, _, _ => rfl
  | cnt + 1, a, ha => by
    have hws : ordRecordsWords (readOrdRecords mem₁ (cnt + 1) a) =
        2 + mem₁ (a + 1) + ordRecordsWords (readOrdRecords mem₁ cnt (a + 2 + mem₁ (a + 1))) := by
      simp [readOrdRecords, ordRecordsWords, readList_length]
    have ha0 : mem₂ a = mem₁ a := ha a le_rfl (by omega)
    have ha1 : mem₂ (a + 1) = mem₁ (a + 1) := ha (a + 1) (by omega) (by omega)
    have hrl := readList_of_agree (mem₁ := mem₁) (mem₂ := mem₂) (a := a + 2) (n := mem₁ (a + 1))
      (fun x hx1 hx2 => ha x (by omega) (by omega))
    simp only [readOrdRecords, ha0, ha1, hrl]
    congr 1
    exact readOrdRecords_of_agree cnt _ fun x hx1 hx2 => ha x (by omega) (by omega)

private theorem readOrdRecordsAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a words : ℕ}
    (hw : words = 1 + ordRecordsWords (readOrdRecordsAt mem₁ a))
    (hag : ∀ x, a ≤ x → x < a + words → mem₂ x = mem₁ x) :
    readOrdRecordsAt mem₂ a = readOrdRecordsAt mem₁ a := by
  unfold readOrdRecordsAt at hw ⊢
  rw [hag a le_rfl (by omega)]
  exact readOrdRecords_of_agree (mem₁ a) (a + 1) fun x hx1 hx2 => hag x (by omega) (by omega)

set_option maxHeartbeats 800000 in
/-- Execution of `asmTopInitBody` (`init`) against `sparseCoreOrdMachineContractKFR`. -/
theorem asmTop_init_runs
    {CFS : AsmCompFamilySpec} {BRS : AsmBranchSpec} {lsfInit : LSFInit} {C_lsst : ℝ}
    {depth w L capExp limbMul : ℕ} {fmt : Num.Format w} {impl : SparsifyImpl}
    {brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ}
    {p : Program} {b fCFInit fCFBatch fCFExport : ℕ} {bp : AsmBranchProcs}
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (BR : AsmBranchAt BRS CFS lsfInit C_lsst depth w fmt L capExp limbMul impl brReemb p fCFInit fCFBatch CF bp)
    (hp : HasAsmTopProcs p b fCFInit fCFBatch fCFExport bp)
    (hfExp : fCFExport = CF.fExport)
    {G : MGraph} {k M N vCap eCap sizeParam : ℕ}
    (hfmt : fmt.limbBits = 4) (hPL : fmt.precision ≤ 4 * L) (hcap : SparseCoreCapHyp capExp limbMul L M N vCap eCap)
    (hdepth : 1 ≤ depth) (hdepth_le : depth ≤ M + N + k + L)
    (hγt : impl.γ_t M = 1)
    (hInit : ∀ j < k, IsValidLSFInitFor lsfInit C_lsst k j)
    (hGn_le : G.n ≤ G.m + 1)
    (hCFmt : CompInitFormatHyp L fmt.precision k G.m)
    (hkCap : k ≤ (M + N + 2) ^ capExp) :
    let T := sparseCoreProgTool lsfInit C_lsst depth impl
    let P := asmTopParams CFS BRS capExp limbMul
    let alloc := asmTopAlloc CFS BRS capExp sizeParam
    let D := sparseCoreOrdMachineContractKFRBL fmt L depth T (bundleToolReemb brReemb) G k M N vCap eCap capExp P alloc
    let R := asmTopRepEq (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) CF.rep BR.rep
      CF.vCapOf CF.eCapOf P.wordExp capExp limbMul w L fmt.precision vCap eCap
    ∀ (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      (∀ v ∈ args, v < 2 ^ w) →
      D.initPre args mem →
      ZeroFrom mem (heapArg args) →
      heapArg args + D.initSpace args mem < 2 ^ w →
      ∃ body, p.procs[asmTopInitIdx b]? = some body ∧
        ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
        ∃ a' x',
          R.rep (heapArg args) a' x' st'.mem ∧
          D.initPost args mem a' st'.mem ∧
          R.Respects (fun _ => False) (heapArg args) (D.initSpace args mem) mem o.value (heapArg args) x' st'.mem ∧
          c + R.phi (heapArg args) x' st'.mem ≤ D.initCost args mem := by
  intro T P alloc D R args mem pos ω hargsW hpre hz hsp
  refine ⟨_, hp.at_init, ?_⟩
  rcases hpre with ⟨graph, lengths, gradient, ord, heap, hargs_eq,
    g0, l0, r0, o0, h0, hargs_kf,
    g1, l1, r1, o1, h1, hargs_k, hwPL,
    g2, l2, r2, o2, h2, hargs_base, hk, hwP, hG, hGval, hGm, hGn, hG_le, hL_le, hGr_le,
    hOrdAt, hOrd_le, hOrdW, hRot, hE_valid, hE_pos⟩
  subst hargs_eq
  simp only [List.cons.injEq, and_true] at hargs_kf hargs_k hargs_base
  rcases hargs_kf with ⟨rfl, rfl, rfl, rfl, -, -, -, -, -, rfl⟩
  rcases hargs_k with ⟨rfl, rfl, rfl, rfl, -, -, -, rfl⟩
  rcases hargs_base with ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hheapArg : heapArg [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap] = heap := rfl
  rw [hheapArg] at hz hsp ⊢
  have hspD : D.initSpace [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap] mem =
      alloc 6 [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap] := rfl
  rw [hspD] at hsp ⊢
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hargsW
  rcases hargsW with ⟨hgraphW, hlenW, hgradW, hordW, hkW, hMW, hNW, hLW, hPfpW, hdepthW, hheapW⟩
  have hw16 : 16 < 2 ^ w := wordBound_ge_16 hwP
  have h1w : 1 < 2 ^ w := by omega
  have hwOrd : (vCap + eCap + 2) ^ 2 < 2 ^ w :=
    capWord_of_wordExp hcap (le_trans (asmP10WordExp_ge_two_mul capExp) (le_max_right _ _)) hwP
  have hwCF : (M + N + 2) ^ CFS.wordExp capExp * (L + 1) < 2 ^ w :=
    lt_of_le_of_lt (Nat.mul_le_mul_right (L + 1)
      (Nat.pow_le_pow_right (by omega) (by simp [P, asmTopParams, asmTopWordExp]))) hwPL
  have hwBR : (M + N + 2) ^ BRS.wordExp capExp * (L + 1) < 2 ^ w :=
    lt_of_le_of_lt (Nat.mul_le_mul_right (L + 1)
      (Nat.pow_le_pow_right (by omega) (by simp [P, asmTopParams, asmTopWordExp]))) hwPL
  have hvCapW : vCap < 2 ^ w := by have := hcap.1; have := hwOrd; nlinarith
  have heCapW : eCap < 2 ^ w := by have := hcap.1; have := hwOrd; nlinarith
  have hGnW : G.n < 2 ^ w := by omega
  set capB := (M + N + 2) ^ capExp
  have hcap_ve : vCap + eCap + 2 ≤ capB := hcap.1
  have hsp_raw : heap + (ASM_HDR_SIZE + (1 + 6 * M) + (16 + 2 * capB + 16 * capB) +
      (CFS.initSpace capExp).eval (capB + L + k) + k +
      k * ((CFS.exportSpace capExp).eval (M + N + k + capB + L) +
        (BRS.initSpace capExp).eval (2 * (M + N + k + capB + L))) +
      (M + N + k + capB + L + ASM_HDR_SIZE)) < 2 ^ w := by
    simpa [alloc, asmTopAlloc, capB] using hsp
  have hordArena_le : ordArenaSize vCap eCap ≤ 16 + 2 * capB + 16 * capB := ordArenaSize_le_of_cap hcap
  have hcfSp_le : (CFS.initSpace capExp).eval (vCap + eCap + L + k) ≤
      (CFS.initSpace capExp).eval (capB + L + k) := (CFS.initSpace capExp).eval_mono (by omega)
  have hcfExpSp_le : (CFS.exportSpace capExp).eval (M + N + k + vCap + eCap + L) ≤
      (CFS.exportSpace capExp).eval (M + N + k + capB + L) :=
    (CFS.exportSpace capExp).eval_mono (by omega)
  have hbrSp_le : (BRS.initSpace capExp).eval (M + N + k + vCap + eCap + L + depth) ≤
      (BRS.initSpace capExp).eval (2 * (M + N + k + capB + L)) :=
    (BRS.initSpace capExp).eval_mono (by omega)
  have hkbrSp_le : k * ((CFS.exportSpace capExp).eval (M + N + k + vCap + eCap + L) +
      (BRS.initSpace capExp).eval (M + N + k + vCap + eCap + L + depth)) ≤
      k * ((CFS.exportSpace capExp).eval (M + N + k + capB + L) +
        (BRS.initSpace capExp).eval (2 * (M + N + k + capB + L))) :=
    Nat.mul_le_mul_left k (Nat.add_le_add hcfExpSp_le hbrSp_le)
  -- Execute the 13-statement prefix (move depth/heap, 3 loads, 7 header stores, r14 := heap + 20)
  set st0 := startState [graph, lengths, gradient, ord, k, M, N, L, fmt.precision, depth, heap] mem pos
  have hG_m0 : mem graph = vCap := by simpa [dgVCapOff] using hG.2.2.2.1
  have hG_m1 : mem (graph + 1) = eCap := by simpa [dgECapOff] using hG.2.2.2.2.1
  have hG_m2 : mem (graph + 2) = G.n := by simpa [dgNOff] using hG.2.2.2.2.2.1
  have hdg4 : 4 ≤ dynGraphSize vCap eCap := by unfold dynGraphSize; omega
  have hst_hdr : ∀ (st : State) (off val : ℕ) (r : ℕ),
      st.regs 9 = heap → st.regs r = val → off < ASM_HDR_SIZE →
      Runs w p ω (.store (.bin .add (.reg 9) (.const off)) (.reg r)) st .normal
        { st with mem := Function.update st.mem (heap + off) val }
        ((Expr.bin .add (.reg 9) (.const off)).size + (Expr.reg r).size + 1) := by
    intro st off val r hr9 hrr hoff
    exact runs_store_iff.mpr ⟨heap + off, val,
      Expr.eval_add (Expr.eval_reg_of_eq hr9) (Expr.eval_const (by unfold ASM_HDR_SIZE at hoff; omega))
        (by unfold ASM_HDR_SIZE at hoff; omega),
      Expr.eval_reg_of_eq hrr, rfl, rfl, rfl⟩
  obtain ⟨s11, hpre_wrap, hs11_r, hs11_r14, hs11_r19, hs11_lt, hs11_ge, hs11_0, hs11_hdr⟩ :=
    asmTopInit_preamble (w := w) (graph := graph) (lengths := lengths) (gradient := gradient)
      (ord := ord) (k := k) (M := M) (N := N) (L := L) (Pfp := fmt.precision) (depth := depth)
      (heap := heap) (vCap := vCap) (eCap := eCap) (gn := G.n) (pos := pos) (p := p) ω
      hw16 (by omega) (by omega) hG_m0 hG_m1 hG_m2 hz
  set resSz := M + N + k + vCap + eCap + L + ASM_HDR_SIZE
  set ℓ₀ := readEdgeValues mem lengths fmt.limbBits L fmt.precision G.E
  set g₀ := readEdgeValues mem gradient fmt.limbBits L fmt.precision G.E
  set ord₀ := readOrd mem ord
  set a' : SparseCoreOrdAbs T := ⟨T.initOrd k M N G ℓ₀ g₀ ord₀, G, ord₀, 0⟩
  -- Branch on G.n = 0 vs G.n > 0
  by_cases hGn0 : G.n = 0
  · have hnotne : ¬ G.V.Nonempty := by
      intro hne; have := Finset.card_pos.mpr hne; change 0 < G.n at this; omega
    have ha'_ne : a'.st.isNonempty = false := by
      change decide G.V.Nonempty = false; exact decide_eq_false hnotne
    have hdg_le_capB : dynGraphSize vCap eCap ≤ 16 + 2 * capB + 16 * capB := by
      unfold dynGraphSize; omega
    obtain ⟨cE, hbranchE, hcE, hDG_em, hEg_lt, hEg_hz⟩ := asmTopInit_emptyBranch (w := w) (p := p) ω
      s11 hw16 hs11_r.2.2.2.1 hs11_r.2.2.2.2.1 hs11_r.2.2.2.2.2.1 hs11_r.2.2.2.2.2.2.1
      hs11_r.2.2.2.2.2.2.2.2.2.1 hs11_r.2.2.2.2.2.2.2.2.2.2.1 hs11_r14
      (fun addr ha => hs11_ge addr (by unfold ASM_HDR_SIZE at ha; omega)) (by omega)
    let stE : State :=
      { s11 with
        mem := Function.update (Function.update s11.mem (heap + ASM_HDR_SIZE) vCap) (heap + ASM_HDR_SIZE + 1) eCap
        regs := Function.update (Function.update s11.regs 14 (heap + ASM_HDR_SIZE + dynGraphSize vCap eCap)) 17 resSz }
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopInitBody (b + 19) (ordStoreInit b) fCFInit fCFExport bp.fInit) st0
          (.returned (heap + ASM_HDR_SIZE + dynGraphSize vCap eCap + resSz)) stE cF ∧ cF ≤ 200 := by
      unfold asmTopInitBody
      refine hpre_wrap _ _ _ ((Expr.reg 16).size + cE + 1) _ ?_ (by simp only [Expr.size]; omega)
      exact runs_cond_iff.mpr ⟨0, cE, Expr.eval_reg_of_eq (v := 0) (by rw [hs11_r.2.2.2.2.2.2.2.2.2.2.2, hGn0]),
        by simpa using hbranchE, rfl⟩
    let x' : R.τ := ⟨k, M, N, vCap, eCap, L, fmt.precision, none,
      heap + ASM_HDR_SIZE, heap + ASM_HDR_SIZE + dynGraphSize vCap eCap + resSz⟩
    have hE_hdr : ∀ off < ASM_HDR_SIZE, stE.mem (heap + off) = s11.mem (heap + off) := fun off hoff =>
      hEg_lt _ (by omega)
    refine ⟨.returned (heap + ASM_HDR_SIZE + dynGraphSize vCap eCap + resSz), _, _, hfull, a', x', ?_, rfl, ?_, ?_⟩
    · refine ⟨⟨⟨by simp [x', ha'_ne], rfl, by dsimp only [x', resSz]; omega,
        by simpa [x'] using (hE_hdr ASM_HDR_NE (by decide)).trans hs11_0,
        (hE_hdr ASM_HDR_K (by decide)).trans hs11_hdr.1,
        (hE_hdr ASM_HDR_M (by decide)).trans hs11_hdr.2.1,
        (hE_hdr ASM_HDR_N (by decide)).trans hs11_hdr.2.2.1,
        (hE_hdr ASM_HDR_VCAP (by decide)).trans hs11_hdr.2.2.2.1,
        (hE_hdr ASM_HDR_ECAP (by decide)).trans hs11_hdr.2.2.2.2.1,
        (hE_hdr ASM_HDR_L (by decide)).trans hs11_hdr.2.2.2.2.2.1,
        (hE_hdr ASM_HDR_PFP (by decide)).trans hs11_hdr.2.2.2.2.2.2,
        (hE_hdr ASM_HDR_EMPTYG (by decide)).trans (hs11_ge _ (by unfold ASM_HDR_EMPTYG; omega)),
        (hE_hdr (ASM_HDR_EMPTYG + 1) (by decide)).trans (hs11_ge _ (by unfold ASM_HDR_EMPTYG; omega)),
        (hE_hdr (ASM_HDR_EMPTYG + 2) (by decide)).trans (hs11_ge _ (by unfold ASM_HDR_EMPTYG; omega)),
        (hE_hdr (ASM_HDR_EMPTYG + 3) (by decide)).trans (hs11_ge _ (by unfold ASM_HDR_EMPTYG; omega)),
        fun _ h => by simp [x'] at h⟩, rfl, rfl, rfl, rfl, hwPL, hcap, hk⟩,
        fun _ => ⟨rfl, by dsimp only [x', resSz]; omega, hDG_em⟩,
        fun _ h => by simp [x'] at h⟩
    · refine ⟨by simp [Outcome.value]; omega,
        by simp [Outcome.value, alloc, asmTopAlloc, resSz]; omega,
        fun addr ha => hEg_hz addr (by simp only [Outcome.value] at ha; omega),
        fun addr ha _ => (hEg_lt addr (by omega)).trans (hs11_lt addr ha),
        fun addr ha => by
          rcases ha with h1 | h2 | h3
          · exact Or.inr ⟨h1.1, by simp [Outcome.value]; omega⟩
          · exact Or.inr ⟨by dsimp only [x'] at h2; omega, by simp [Outcome.value]; exact h2.2⟩
          · exact False.elim h3⟩
    · have hphi0 : R.phi heap x' stE.mem = 0 := rfl
      rw [hphi0]
      change _ ≤ P.mul * (T.cost a'.st + G.n + G.m + ordListWords mem ord + 1)
      have hmul : 400 ≤ P.mul := by simp [P, asmTopParams]
      have hmul1 : 400 * 1 ≤ P.mul * (T.cost a'.st + G.n + G.m + ordListWords mem ord + 1) :=
        Nat.mul_le_mul hmul (by omega)
      omega
  · -- Nonempty case: G.n > 0
    have hGne : G.V.Nonempty := Finset.card_pos.mp (by change 0 < G.n; omega)
    have ha'_ne : a'.st.isNonempty = true := by
      change decide G.V.Nonempty = true; exact decide_eq_true hGne
    -- Step 1: store 1 at heap, compact ord at cOrdPtr = heap + ASM_HDR_SIZE
    set cOrdPtr := heap + ASM_HDR_SIZE
    have hcOrd_def : cOrdPtr = heap + 20 := rfl
    have hhdr_sz : ASM_HDR_SIZE = 20 := rfl
    have hst1 : Runs w p ω (.store (.reg 9) (.const 1)) s11 .normal
        { s11 with mem := Function.update s11.mem heap 1 } _ :=
      runs_store_iff.mpr ⟨heap, 1, Expr.eval_reg_of_eq hs11_r.2.2.2.2.2.2.2.2.1,
        Expr.eval_const h1w, rfl, rfl, rfl⟩
    set s12 : State := { s11 with mem := Function.update s11.mem heap 1 }
    have ha17_c : Runs w p ω (.assign 17 (.reg 14)) s12 .normal
        { s12 with regs := Function.update s12.regs 17 cOrdPtr } _ :=
      runs_assign_iff.mpr ⟨cOrdPtr, Expr.eval_reg_of_eq (by simp [s12, hs11_r14, cOrdPtr]), rfl, rfl, rfl⟩
    set s13 : State := { s12 with regs := Function.update s12.regs 17 cOrdPtr }
    have hs13_lt : ∀ addr < heap, s13.mem addr = mem addr := fun addr ha => by
      dsimp only [s13, s12]; rw [Function.update_of_ne (by omega)]; exact hs11_lt addr ha
    have hs13_ge : ∀ addr, heap + 8 ≤ addr → s13.mem addr = 0 := fun addr ha => by
      dsimp only [s13, s12]; rw [Function.update_of_ne (by omega)]; exact hs11_ge addr ha
    have hOrd13 : OrdListAt s13.mem ord ord₀ (ordListWords mem ord) :=
      ordListAt_of_agree hOrdAt fun addr ha1 ha2 => hs13_lt addr (by omega)
    have hOrdW13 : ∀ j < ordListWords mem ord, s13.mem (ord + j) < 2 ^ w := fun j hj => by
      rw [hs13_lt (ord + j) (by omega)]; exact hOrdW j hj
    have hrecs13 : readOrdRecordsAt s13.mem ord = readOrdRecordsAt mem ord :=
      readOrdRecordsAt_of_agree hOrdAt.2.2 fun x hx1 hx2 => hs13_lt x (by omega)
    let recs := readOrdRecordsAt mem ord
    obtain ⟨cWords, hcWords_eq⟩ : ∃ n, n = 1 + ordRecordsWords (compactRecs recs) := ⟨_, rfl⟩
    have hcWords_le_6m : cWords ≤ 1 + 6 * G.m := by
      rw [hcWords_eq]; exact compactOrdWords_le_of_rotation hGval hOrdAt.1 hRot
    have hcOrd_lt : cOrdPtr + cWords < 2 ^ w := by omega
    have h4w : 4 < 2 ^ w := lt_trans (by decide : 4 < 16) hw16
    have hord_le_c : ord + ordListWords mem ord ≤ cOrdPtr :=
      le_trans hOrd_le (Nat.le_add_right heap ASM_HDR_SIZE)
    have hdst_lt : cOrdPtr + (1 + ordRecordsWords (compactRecs (readOrdRecordsAt s13.mem ord))) < 2 ^ w := by
      rw [hrecs13]
      show cOrdPtr + (1 + ordRecordsWords (compactRecs recs)) < 2 ^ w
      rw [← hcWords_eq]
      exact hcOrd_lt
    obtain ⟨oCp, stCp, cCp, hrunCp, hvalCp, hcW_le, hrecsCp, hOrdCp, hfrCp, hzCp, hcostCp⟩ :=
      asmCompactOrdBody_runs (w := w) (ordPtr := ord) (dst := cOrdPtr) (words := ordListWords mem ord)
        (pos := s13.pos) (p := p) ω h4w hOrd13 hord_le_c hOrdW13
        (fun addr ha => hs13_ge addr (by omega)) hdst_lt
    rw [hrecs13] at hvalCp hrecsCp hOrdCp hzCp
    change oCp.value = cOrdPtr + (1 + ordRecordsWords (compactRecs recs)) at hvalCp
    change OrdListAt stCp.mem cOrdPtr ord₀ (1 + ordRecordsWords (compactRecs recs)) at hOrdCp
    change ZeroFrom stCp.mem (cOrdPtr + (1 + ordRecordsWords (compactRecs recs))) at hzCp
    rw [← hcWords_eq] at hvalCp hOrdCp hzCp
    obtain ⟨ordH, hordH_eq⟩ : ∃ n, n = cOrdPtr + cWords := ⟨_, rfl⟩
    have hcallCp : Runs w p ω (.call 14 (b + 19) [.reg 3, .reg 14]) s13 .normal
        { stCp with regs := Function.update s13.regs 14 ordH }
        (argsSize [.reg 3, .reg 14] + cCp + 1) := by
      refine (runs_call_iff (r := 14) (f := b + 19) (st := s13) (o := .normal)
        (st' := { stCp with regs := Function.update s13.regs 14 ordH })).mpr
        ⟨[ord, cOrdPtr], asmCompactOrdBody, oCp, stCp, cCp, ?_, hp.at_compact, hrunCp, rfl,
          by rw [hvalCp, ← hordH_eq], rfl⟩
      simp [evalArgs, Expr.eval, s13, s12, hs11_r.2.2.1, hs11_r14, cOrdPtr]
    let s14 : State := { stCp with regs := Function.update s13.regs 14 ordH }
    have ha3_c : Runs w p ω (.assign 3 (.reg 17)) s14 .normal
        { s14 with regs := Function.update s14.regs 3 cOrdPtr } _ :=
      runs_assign_iff.mpr ⟨cOrdPtr, Expr.eval_reg_of_eq (by simp [s14, s13]), rfl, rfl, rfl⟩
    let s15 : State := { s14 with regs := Function.update s14.regs 3 cOrdPtr }
    have hst_ordH : Runs w p ω (.store (.bin .add (.reg 9) (.const ASM_HDR_ORDH)) (.reg 14)) s15 .normal
        { s15 with mem := Function.update s15.mem (heap + ASM_HDR_ORDH) ordH } _ :=
      hst_hdr s15 ASM_HDR_ORDH ordH 14 (by simp [s15, s14, s13, s12, hs11_r.2.2.2.2.2.2.2.2.1])
        (by simp [s15, s14]) (by decide)
    let s16 : State := { s15 with mem := Function.update s15.mem (heap + ASM_HDR_ORDH) ordH }
    have hs16_r : ∀ r, r ≠ 3 → r ≠ 14 → r ≠ 17 → s16.regs r = s11.regs r := fun r h3 h14 h17 => by
      simp [s16, s15, s14, s13, s12, h3, h14, h17]
    -- Step 2: call real P1 ordStore_implements_cap init on [vCap, eCap, cOrdPtr, ordH]
    have hOrd16 : OrdListAt s16.mem cOrdPtr ord₀ cWords :=
      ordListAt_of_agree hOrdCp fun addr ha1 ha2 => by
        dsimp only [s16, s15, s14]; exact Function.update_of_ne (by unfold ASM_HDR_ORDH; omega) _ _
    have hrecs16 : readOrdRecordsAt s16.mem cOrdPtr = compactRecs recs := by
      rw [← hrecsCp]
      exact readOrdRecordsAt_of_agree hOrdCp.2.2 fun x hx1 hx2 => by
        dsimp only [s16, s15, s14]; exact Function.update_of_ne (by unfold ASM_HDR_ORDH; omega) _ _
    have huniq : OrdUniqueWithin vCap eCap ord₀ := asmInit_ordUniqueWithin_of_rotation hG hRot
    have hz16 : ZeroFrom s16.mem ordH := fun addr ha => by
      dsimp only [s16, s15, s14]; rw [Function.update_of_ne (by unfold ASM_HDR_ORDH; omega)]
      exact hzCp addr (by omega)
    have hOrdImpl := (ordStore_implements_cap w vCap eCap p b hp.hasOrdStore hwOrd).2
    obtain ⟨bodyOrd, hbodyOrd, oOrd, stOrd, cOrd, hrunOrd, sOrd', xOrd', hOrdRep', hOrdPost', hOrdResp, hOrdCost⟩ :=
      hOrdImpl.2.1 [vCap, eCap, cOrdPtr, ordH] s16.mem s16.pos ω
        (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; rcases hv with rfl | rfl | rfl | rfl <;> omega)
        ⟨cOrdPtr, ordH, cWords, rfl, hOrd16.2.1.symm ▸ hOrd16, hordH_eq.ge, hOrd16.2.1.symm ▸ huniq⟩
        hz16 (by change ordH + ordArenaSize vCap eCap < 2 ^ w; omega)
    rcases hOrdResp with ⟨hOrd_lo, hOrd_hi, hzOrd, hOrd_fr, hOrd_ft⟩
    change ordH ≤ oOrd.value at hOrd_lo
    change oOrd.value ≤ ordH + ordArenaSize vCap eCap at hOrd_hi
    change ∀ a < ordH, ¬ False → stOrd.mem a = s16.mem a at hOrd_fr
    let cfH := oOrd.value
    have hsOrd'_eq : sOrd' = ord₀ := hOrdPost'.trans hOrd16.2.1
    rw [hsOrd'_eq] at hOrdRep'
    have hcallOrd : Runs w p ω (.call 14 (ordStoreInit b) [.reg 10, .reg 11, .reg 3, .reg 14]) s16 .normal
        { stOrd with regs := Function.update s16.regs 14 cfH }
        (argsSize [.reg 10, .reg 11, .reg 3, .reg 14] + cOrd + 1) := by
      refine (runs_call_iff (r := 14) (f := ordStoreInit b) (st := s16) (o := .normal)
        (st' := { stOrd with regs := Function.update s16.regs 14 cfH })).mpr
        ⟨[vCap, eCap, cOrdPtr, ordH], bodyOrd, oOrd, stOrd, cOrd, ?_, hbodyOrd, hrunOrd, rfl, rfl, rfl⟩
      have hr10 : s16.regs 10 = vCap := (hs16_r 10 (by decide) (by decide) (by decide)).trans hs11_r.2.2.2.2.2.2.2.2.2.1
      have hr11 : s16.regs 11 = eCap := (hs16_r 11 (by decide) (by decide) (by decide)).trans hs11_r.2.2.2.2.2.2.2.2.2.2.1
      have hr3 : s16.regs 3 = cOrdPtr := by simp [s16, s15]
      have hr14 : s16.regs 14 = ordH := by simp [s16, s15, s14]
      simp [evalArgs, Expr.eval, hr10, hr11, hr3, hr14]
    let s17 : State := { stOrd with regs := Function.update s16.regs 14 cfH }
    have ha12_cf : Runs w p ω (.assign 12 (.reg 14)) s17 .normal
        { s17 with regs := Function.update s17.regs 12 cfH } _ :=
      runs_assign_iff.mpr ⟨cfH, Expr.eval_reg_of_eq (by simp [s17]), rfl, rfl, rfl⟩
    let s18 : State := { s17 with regs := Function.update s17.regs 12 cfH }
    have hst_cfH := hst_hdr s18 ASM_HDR_CFH cfH 12
      (by simp [s18, s17, hs16_r 9 (by decide) (by decide) (by decide), hs11_r.2.2.2.2.2.2.2.2.1])
      (by simp [s18]) (by decide)
    let s19 : State := { s18 with mem := Function.update s18.mem (heap + ASM_HDR_CFH) cfH }
    have hs19_r : ∀ r, r ≠ 12 → r ≠ 14 → s19.regs r = s16.regs r := fun r h12 h14 => by
      simp [s19, s18, s17, h12, h14]
    -- Step 3: call P4 CF.init_runs on [graph, lengths, L, fmt.precision, k, vCap, eCap, cfH]
    have hs19_lt : ∀ addr < heap, s19.mem addr = mem addr := fun addr ha => by
      dsimp only [s19, s18, s17]; rw [Function.update_of_ne (by omega)]
      rw [hOrd_fr addr (by omega) (fun hf => hf)]
      dsimp only [s16, s15, s14]; rw [Function.update_of_ne (by omega)]
      rw [hfrCp addr (by omega), hs13_lt addr ha]
    have hG19 : DynGraphAt s19.mem graph vCap eCap G :=
      DynGraphAt.of_agree hG fun addr ha1 ha2 => hs19_lt addr (by omega)
    have hlen19_eq : readEdgeValues s19.mem lengths 4 L fmt.precision G.E = ℓ₀ := by
      funext e; dsimp only [ℓ₀]; unfold readEdgeValues; rw [hfmt]
      by_cases he : e ∈ G.E
      · simp only [he, ↓reduceIte]
        have he_lt := (hE_valid e he).1
        have hcon : ∀ i < L, s19.mem (lengths + e * L + i) = mem (lengths + e * L + i) := fun i hi => by
          refine hs19_lt (lengths + e * L + i) ?_
          have h1 : (e + 1) * L ≤ eCap * L := Nat.mul_le_mul_right L (by omega)
          rw [Nat.add_one_mul] at h1; omega
        unfold Num.fixVal
        rw [Num.intVal_congr hcon]
      · simp [he]
    have hEv19 : ∀ e ∈ G.E, e < eCap ∧ Num.Valid s19.mem (lengths + e * L) 4 L ∧
        0 < readEdgeValues s19.mem lengths 4 L fmt.precision G.E e := by
      intro e he
      obtain ⟨hlt, hval, _⟩ := hE_valid e he
      have hpos := hE_pos e he
      refine ⟨hlt, ?_, by rw [hlen19_eq]; exact hpos⟩
      have hcon : ∀ i < L, s19.mem (lengths + e * L + i) = mem (lengths + e * L + i) := fun i hi =>
        hs19_lt _ (by have h1 : (e + 1) * L ≤ eCap * L := Nat.mul_le_mul_right L (by omega); rw [Nat.add_one_mul] at h1; omega)
      rw [hfmt] at hval
      exact fun i hi => by rw [hcon i hi]; exact hval i hi
    have hz19 : ZeroFrom s19.mem cfH := fun addr ha => by
      dsimp only [s19, s18, s17]; rw [Function.update_of_ne (by unfold ASM_HDR_CFH; omega)]
      exact hzOrd addr ha
    have hcfH_w : cfH < 2 ^ w := by omega
    have hcfArgsW : ∀ v ∈ [graph, lengths, L, fmt.precision, k, vCap, eCap, cfH], v < 2 ^ w := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hgraphW
      · exact hlenW
      · exact hLW
      · exact hPfpW
      · exact hkW
      · exact hvCapW
      · exact heCapW
      · exact hcfH_w
    obtain ⟨bodyCF, hbodyCF, oCF, stCF, cCF, xCF, hrunCF, hCFRep, hvCF, heCF, hCFResp, hCFCost⟩ :=
      CF.init_runs graph lengths k M N vCap eCap cfH G s19.mem s19.pos ω
        hfmt hk hGval hGne hGm hGn hCFmt hkCap hcap hwCF hG19 (by omega) (by omega) hEv19
        hcfArgsW hz19 (by omega)
    rw [hlen19_eq] at hCFRep
    rcases hCFResp with ⟨hCF_lo, hCF_hi, hzCF, hCF_fr, hCF_ft⟩
    let tbl := oCF.value
    have hcallCF : Runs w p ω (.call 14 fCFInit [.reg 0, .reg 1, .reg 7, .reg 8, .reg 4, .reg 10, .reg 11, .reg 14]) s19 .normal
        { stCF with regs := Function.update s19.regs 14 tbl }
        (argsSize [.reg 0, .reg 1, .reg 7, .reg 8, .reg 4, .reg 10, .reg 11, .reg 14] + cCF + 1) := by
      refine (runs_call_iff (r := 14) (f := fCFInit) (st := s19) (o := .normal)
        (st' := { stCF with regs := Function.update s19.regs 14 tbl })).mpr
        ⟨[graph, lengths, L, fmt.precision, k, vCap, eCap, cfH], bodyCF, oCF, stCF, cCF, ?_, hbodyCF, hrunCF, rfl, rfl, rfl⟩
      have hr0 : s19.regs 0 = graph := (hs19_r 0 (by decide) (by decide)).trans ((hs16_r 0 (by decide) (by decide) (by decide)).trans hs11_r.1)
      have hr1 : s19.regs 1 = lengths := (hs19_r 1 (by decide) (by decide)).trans ((hs16_r 1 (by decide) (by decide) (by decide)).trans hs11_r.2.1)
      have hr7 : s19.regs 7 = L := (hs19_r 7 (by decide) (by decide)).trans ((hs16_r 7 (by decide) (by decide) (by decide)).trans hs11_r.2.2.2.2.2.2.1)
      have hr8 : s19.regs 8 = fmt.precision := (hs19_r 8 (by decide) (by decide)).trans ((hs16_r 8 (by decide) (by decide) (by decide)).trans hs11_r.2.2.2.2.2.2.2.1)
      have hr4 : s19.regs 4 = k := (hs19_r 4 (by decide) (by decide)).trans ((hs16_r 4 (by decide) (by decide) (by decide)).trans hs11_r.2.2.2.1)
      have hr10 : s19.regs 10 = vCap := (hs19_r 10 (by decide) (by decide)).trans ((hs16_r 10 (by decide) (by decide) (by decide)).trans hs11_r.2.2.2.2.2.2.2.2.2.1)
      have hr11 : s19.regs 11 = eCap := (hs19_r 11 (by decide) (by decide)).trans ((hs16_r 11 (by decide) (by decide) (by decide)).trans hs11_r.2.2.2.2.2.2.2.2.2.2.1)
      have hr14 : s19.regs 14 = cfH := by simp [s19, s18, s17]
      simp [evalArgs, Expr.eval, hr0, hr1, hr7, hr8, hr4, hr10, hr11, hr14]
    let s20 : State := { stCF with regs := Function.update s19.regs 14 tbl }
    have ha13_tbl : Runs w p ω (.assign 13 (.reg 14)) s20 .normal
        { s20 with regs := Function.update s20.regs 13 tbl } _ :=
      runs_assign_iff.mpr ⟨tbl, Expr.eval_reg_of_eq (by simp [s20]), rfl, rfl, rfl⟩
    let s21 : State := { s20 with regs := Function.update s20.regs 13 tbl }
    have hst_tbl := hst_hdr s21 ASM_HDR_TBL tbl 13
      (by simp [s21, s20, hs19_r 9 (by decide) (by decide), hs16_r 9 (by decide) (by decide) (by decide), hs11_r.2.2.2.2.2.2.2.2.1])
      (by simp [s21]) (by decide)
    let s22 : State := { s21 with mem := Function.update s21.mem (heap + ASM_HDR_TBL) tbl }
    let hStart := tbl + k
    have ha14_hS : Runs w p ω (.assign 14 (.bin .add (.reg 13) (.reg 4))) s22 .normal
        { s22 with regs := Function.update s22.regs 14 hStart } _ :=
      runs_assign_iff.mpr ⟨hStart,
        Expr.eval_add (Expr.eval_reg_of_eq (v := tbl) (by simp [s22, s21]))
          (Expr.eval_reg_of_eq (v := k) (by simp [s22, s21, s20, hs19_r 4 (by decide) (by decide),
            hs16_r 4 (by decide) (by decide) (by decide), hs11_r.2.2.2.1]))
          (by omega), rfl, rfl, rfl⟩
    let s23 : State := { s22 with regs := Function.update s22.regs 14 hStart }
    have hs23_r : ∀ r, r ≠ 13 → r ≠ 14 → s23.regs r = s19.regs r := fun r h13 h14 => by
      simp [s23, s22, s21, s20, h13, h14]
    -- Step 4: run asmInitBranchesLoop_runs on all k branches
    have hcfFt_rg : ∀ addr, CF.rep.foot cfH xCF addr → cfH ≤ addr ∧ addr < tbl := fun addr ha => by
      rcases hCF_ft addr ha with hf | hrg; exact False.elim hf; exact hrg
    have hs23_lt : ∀ addr < heap, s23.mem addr = mem addr := fun addr ha => by
      dsimp only [s23, s22, s21, s20]; rw [Function.update_of_ne (by omega)]
      rw [hCF_fr addr (by omega) (fun hf => hf), hs19_lt addr ha]
    have hCF23_loc := CF.rep_local cfH (fun j => initCompLSFWith lsfInit G ℓ₀ k j) xCF stCF.mem s23.mem fun addr ha => by
      have := (hcfFt_rg addr ha).1
      dsimp only [s23, s22, s21, s20]; exact (Function.update_of_ne (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega) _ _).symm
    have hCF23 : CF.rep.rep cfH (fun j => initCompLSFWith lsfInit G ℓ₀ k j) xCF s23.mem := hCF23_loc.1 hCFRep
    have hCFPhi23 : CF.rep.phi cfH xCF s23.mem = CF.rep.phi cfH xCF stCF.mem := hCF23_loc.2.symm
    have hG23 : DynGraphAt s23.mem graph vCap eCap G :=
      DynGraphAt.of_agree hG fun addr ha1 ha2 => hs23_lt addr (by omega)
    have hOrd23 : OrdListAt s23.mem cOrdPtr ord₀ cWords :=
      ordListAt_of_agree hOrd16 fun addr ha1 ha2 => by
        dsimp only [s23, s22, s21, s20]; rw [Function.update_of_ne (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)]
        rw [hCF_fr addr (by omega) (fun hf => hf)]
        dsimp only [s19, s18, s17]; rw [Function.update_of_ne (by unfold ASM_HDR_CFH ASM_HDR_SIZE at *; omega)]
        exact hOrd_fr addr (by omega) (fun hf => hf)
    have hz23 : ZeroFrom s23.mem hStart := fun addr ha => by
      dsimp only [s23, s22, s21, s20]; rw [Function.update_of_ne (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)]
      exact hzCF addr (by omega)
    have hloopArgsW : ∀ v ∈ [cfH, graph, cOrdPtr, k, M, N, L, fmt.precision, vCap, eCap, depth, tbl], v < 2 ^ w := by
      have hcOrdW : cOrdPtr < 2 ^ w := by omega
      have htblW : tbl < 2 ^ w := by omega
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hcfH_w
      · exact hgraphW
      · exact hcOrdW
      · exact hkW
      · exact hMW
      · exact hNW
      · exact hLW
      · exact hPfpW
      · exact hvCapW
      · exact heCapW
      · exact hdepthW
      · exact htblW
    have hLen23 : BranchLengthsAt s23.mem lengths eCap L fmt.precision (tbl + k) G ℓ₀ :=
      BranchLengthsAt.of_agree (mem := s19.mem) ⟨hL_le, hEv19, hlen19_eq.symm⟩
        (fun addr ha1 ha2 => by rw [hs23_lt addr (by omega), hs19_lt addr (by omega)])
        (by omega)
    have hinp₀ : SparseCoreOrdInput T k M N a'.st G ord₀ 0 :=
      SparseCoreOrdInput.init G ℓ₀ g₀ ord₀ hGval hGm hGn hE_pos hRot
    have hModUpd : ∀ j < k,
        AsmBrModelFacts impl vCap eCap
          (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
            (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord₀ j) ord₀ ∧
        BranchUpdatesBelow impl
          (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
            (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord₀ j) 0 :=
      fun j hj => asm_input_model_inv hk hdepth hγt hG.2.1 hG.2.2.1 hinp₀ ha'_ne (hInit j hj)
    obtain ⟨stL, cL, xCF', brH, xBR, hrunL, hregsL, hL_lo, hL_hi, hzL, hCFRepL, hvCF', heCF',
        hCFFtL, hL_fr, hBR_all, hBR_disj, hCostL⟩ :=
      asmInitBranchesLoop_runs BR (graph := graph) (lengths := lengths) (cOrdPtr := cOrdPtr) (k := k)
        (M := M) (N := N)
        (vCap := vCap) (eCap := eCap) (cfH := cfH) (tbl := tbl) (cWords := cWords) (hStart := hStart)
        (G := G) (ℓ₀ := ℓ₀) (ord := ord₀) (cfs := fun j => initCompLSFWith lsfInit G ℓ₀ k j) (xcf := xCF)
        s23 ω hfmt hPL hk hGval hGne hGm hGn hGn_le hkCap hcap hwCF hwBR (by omega) (fun _ _ => rfl)
        (fun addr ha1 ha2 => by omega)
        (by omega) (by omega) hcWords_le_6m hRot le_rfl
        (fun addr ha => by have := hcfFt_rg addr ha; omega)
        (fun addr ha1 ha2 => by omega) (fun addr ha1 ha2 => by omega)
        hloopArgsW (by omega)
        (fun j hj => (hModUpd j hj).1) (fun j hj => (hModUpd j hj).2)
        (by rw [hs23_r 0 (by decide) (by decide), hs19_r 0 (by decide) (by decide), hs16_r 0 (by decide) (by decide) (by decide)]; exact hs11_r.1)
        (by rw [hs23_r 1 (by decide) (by decide), hs19_r 1 (by decide) (by decide), hs16_r 1 (by decide) (by decide) (by decide)]; exact hs11_r.2.1)
        (by rw [hs23_r 3 (by decide) (by decide), hs19_r 3 (by decide) (by decide)]; simp [s16, s15])
        (by rw [hs23_r 4 (by decide) (by decide), hs19_r 4 (by decide) (by decide), hs16_r 4 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.1)
        (by rw [hs23_r 5 (by decide) (by decide), hs19_r 5 (by decide) (by decide), hs16_r 5 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.2.1)
        (by rw [hs23_r 6 (by decide) (by decide), hs19_r 6 (by decide) (by decide), hs16_r 6 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.2.2.1)
        (by rw [hs23_r 7 (by decide) (by decide), hs19_r 7 (by decide) (by decide), hs16_r 7 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.2.2.2.1)
        (by rw [hs23_r 8 (by decide) (by decide), hs19_r 8 (by decide) (by decide), hs16_r 8 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.2.2.2.2.1)
        (by rw [hs23_r 10 (by decide) (by decide), hs19_r 10 (by decide) (by decide), hs16_r 10 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.2.2.2.2.2.2.1)
        (by rw [hs23_r 11 (by decide) (by decide), hs19_r 11 (by decide) (by decide), hs16_r 11 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.2.2.2.2.2.2.2.1)
        (by rw [hs23_r 12 (by decide) (by decide)]; simp [s19, s18])
        (by simp [s23, s22, s21]) (by simp [s23])
        (by rw [hs23_r 19 (by decide) (by decide), hs19_r 19 (by decide) (by decide), hs16_r 19 (by decide) (by decide) (by decide)]; exact hs11_r19)
        hz23 hCF23 hvCF heCF (fun addr ha hin => by have := hcfFt_rg addr ha; omega) hG23 hOrd23
        hLen23
    set hEnd := stL.regs 14
    obtain ⟨cT, htail, hcT⟩ := asmTopInit_tail (w := w) (k := k) (M := M) (N := N) (L := L)
      (vCap := vCap) (eCap := eCap) (hCur := hEnd) (p := p) ω stL
      ((hregsL 4 (by decide) (by decide) (by decide)).trans (by rw [hs23_r 4 (by decide) (by decide), hs19_r 4 (by decide) (by decide), hs16_r 4 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.1))
      ((hregsL 5 (by decide) (by decide) (by decide)).trans (by rw [hs23_r 5 (by decide) (by decide), hs19_r 5 (by decide) (by decide), hs16_r 5 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.2.1))
      ((hregsL 6 (by decide) (by decide) (by decide)).trans (by rw [hs23_r 6 (by decide) (by decide), hs19_r 6 (by decide) (by decide), hs16_r 6 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.2.2.1))
      ((hregsL 7 (by decide) (by decide) (by decide)).trans (by rw [hs23_r 7 (by decide) (by decide), hs19_r 7 (by decide) (by decide), hs16_r 7 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.2.2.2.1))
      ((hregsL 10 (by decide) (by decide) (by decide)).trans (by rw [hs23_r 10 (by decide) (by decide), hs19_r 10 (by decide) (by decide), hs16_r 10 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.2.2.2.2.2.2.1))
      ((hregsL 11 (by decide) (by decide) (by decide)).trans (by rw [hs23_r 11 (by decide) (by decide), hs19_r 11 (by decide) (by decide), hs16_r 11 (by decide) (by decide) (by decide)]; exact hs11_r.2.2.2.2.2.2.2.2.2.2.1))
      rfl (by omega)
    obtain ⟨cF, hfull, hcF⟩ : ∃ cF,
        Runs w p ω (asmTopInitBody (b + 19) (ordStoreInit b) fCFInit fCFExport bp.fInit) st0
          (.returned (hEnd + resSz)) { stL with regs := Function.update stL.regs 17 resSz } cF ∧
        cF ≤ cCp + cOrd + cCF + cL + 200 := by
      unfold asmTopInitBody
      rw [hfExp]
      obtain ⟨cTh, hth, hcTh⟩ : ∃ cTh, Runs w p ω _ s11 (.returned (hEnd + resSz))
          { stL with regs := Function.update stL.regs 17 resSz } cTh ∧
          cTh ≤ cCp + cOrd + cCF + cL + 110 := by
        refine ⟨_, runs_seq_iff.mpr (Or.inr ⟨s12, _, _, hst1,
          runs_seq_iff.mpr (Or.inr ⟨s13, _, _, ha17_c,
            runs_seq_iff.mpr (Or.inr ⟨s14, _, _, hcallCp,
              runs_seq_iff.mpr (Or.inr ⟨s15, _, _, ha3_c,
                runs_seq_iff.mpr (Or.inr ⟨s16, _, _, hst_ordH,
                  runs_seq_iff.mpr (Or.inr ⟨s17, _, _, hcallOrd,
                    runs_seq_iff.mpr (Or.inr ⟨s18, _, _, ha12_cf,
                      runs_seq_iff.mpr (Or.inr ⟨s19, _, _, hst_cfH,
                        runs_seq_iff.mpr (Or.inr ⟨s20, _, _, hcallCF,
                          runs_seq_iff.mpr (Or.inr ⟨s21, _, _, ha13_tbl,
                            runs_seq_iff.mpr (Or.inr ⟨s22, _, _, hst_tbl,
                              runs_seq_iff.mpr (Or.inr ⟨s23, _, _, ha14_hS,
                                runs_seq_iff.mpr (Or.inr ⟨stL, _, _, hrunL, htail, rfl⟩), rfl⟩), rfl⟩),
                            rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), ?_⟩
        simp only [argsSize_cons, argsSize_nil, Expr.size]; omega
      refine hpre_wrap _ _ _ ((Expr.reg 16).size + cTh + 1) _ ?_ (by simp only [Expr.size]; omega)
      exact runs_cond_iff.mpr ⟨G.n, cTh, Expr.eval_reg_of_eq (v := G.n) hs11_r.2.2.2.2.2.2.2.2.2.2.2,
        by simpa [hGn0] using hth, rfl⟩
    -- Frame sub-structures and header words to stL.mem
    have hhdr_stL : ∀ off < ASM_HDR_SIZE, off ≠ ASM_HDR_ORDH → off ≠ ASM_HDR_CFH → off ≠ ASM_HDR_TBL →
        stL.mem (heap + off) = s12.mem (heap + off) := fun off hoff hno8 hno9 hno10 => by
      rw [hL_fr _ (by omega) (fun hc => by have := (hcfFt_rg _ hc).1; omega) (by omega)]
      dsimp only [s23, s22, s21, s20]; rw [Function.update_of_ne (by omega)]
      rw [hCF_fr _ (by omega) (fun hf => hf)]
      dsimp only [s19, s18, s17]; rw [Function.update_of_ne (by omega)]
      rw [hOrd_fr _ (by omega) (fun hf => hf)]
      dsimp only [s16, s15, s14]; rw [Function.update_of_ne (by omega)]
      rw [hfrCp _ (by omega)]
    have hordFt_rg : ∀ addr, ordFoot ordH vCap eCap addr → ordH ≤ addr ∧ addr < cfH := fun addr ha => by
      rcases hOrd_ft addr ha with hf | hrg; exact False.elim hf; exact hrg
    have hOrdRepL : (ordStoreRep vCap eCap).rep ordH ord₀ xOrd' stL.mem :=
      (ordStoreRep_local vCap eCap ordH ord₀ xOrd' stOrd.mem stL.mem fun addr ha => by
        have hrg := hordFt_rg addr ha
        rw [hL_fr addr (by omega) (fun hc => by have := (hcfFt_rg addr hc).1; omega) (by omega)]
        dsimp only [s23, s22, s21, s20]; rw [Function.update_of_ne (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)]
        rw [hCF_fr addr (by omega) (fun hf => hf)]
        dsimp only [s19, s18, s17]; rw [Function.update_of_ne (by unfold ASM_HDR_CFH ASM_HDR_SIZE at *; omega)]).1 hOrdRep'
    have hbrH_lt : ∀ j < k, brH j < hEnd + resSz := fun j hj => by
      have := (hBR_all j hj).2.1; dsimp only [hEnd, resSz, ASM_HDR_SIZE]; omega
    let ne : AsmTopNE CF.rep.τ BR.rep.τ := ⟨ordH, xOrd', cfH, xCF', tbl, brH, xBR⟩
    let x' : R.τ := ⟨k, M, N, vCap, eCap, L, fmt.precision, some ne, hEnd, hEnd + resSz⟩
    have ha'_trees : ∀ j, a'.st.trees j =
        initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
          (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord₀ j := fun j => rfl
    have ha'_ord : a'.st.ord = ord₀ := rfl
    have hhdr_ge_tbl : heap + ASM_HDR_SIZE ≤ tbl := by omega
    have hordA_le := ordArenaSize_le_of_cap hcap
    refine ⟨.returned (hEnd + resSz), { stL with regs := Function.update stL.regs 17 resSz }, _, hfull,
      a', x', ⟨?_, fun h => by simp [x'] at h,
        fun ne' hne' => by cases Option.some.inj hne'.symm; exact ⟨hvCF', heCF'⟩⟩, rfl, ?_, ?_⟩
    · refine ⟨⟨by simp [x', ha'_ne], rfl, by dsimp only [x', resSz]; omega,
        by simp only [x', Option.isSome_some, ↓reduceIte]; rw [hhdr_stL ASM_HDR_NE (by decide) (by decide) (by decide) (by decide)]; simp [s12, ASM_HDR_NE],
        by rw [hhdr_stL ASM_HDR_K (by decide) (by decide) (by decide) (by decide)]; dsimp only [s12]; rw [Function.update_of_ne (by unfold ASM_HDR_K; omega)]; exact hs11_hdr.1,
        by rw [hhdr_stL ASM_HDR_M (by decide) (by decide) (by decide) (by decide)]; dsimp only [s12]; rw [Function.update_of_ne (by unfold ASM_HDR_M; omega)]; exact hs11_hdr.2.1,
        by rw [hhdr_stL ASM_HDR_N (by decide) (by decide) (by decide) (by decide)]; dsimp only [s12]; rw [Function.update_of_ne (by unfold ASM_HDR_N; omega)]; exact hs11_hdr.2.2.1,
        by rw [hhdr_stL ASM_HDR_VCAP (by decide) (by decide) (by decide) (by decide)]; dsimp only [s12]; rw [Function.update_of_ne (by unfold ASM_HDR_VCAP; omega)]; exact hs11_hdr.2.2.2.1,
        by rw [hhdr_stL ASM_HDR_ECAP (by decide) (by decide) (by decide) (by decide)]; dsimp only [s12]; rw [Function.update_of_ne (by unfold ASM_HDR_ECAP; omega)]; exact hs11_hdr.2.2.2.2.1,
        by rw [hhdr_stL ASM_HDR_L (by decide) (by decide) (by decide) (by decide)]; dsimp only [s12]; rw [Function.update_of_ne (by unfold ASM_HDR_L; omega)]; exact hs11_hdr.2.2.2.2.2.1,
        by rw [hhdr_stL ASM_HDR_PFP (by decide) (by decide) (by decide) (by decide)]; dsimp only [s12]; rw [Function.update_of_ne (by unfold ASM_HDR_PFP; omega)]; exact hs11_hdr.2.2.2.2.2.2,
        by rw [hhdr_stL ASM_HDR_EMPTYG (by decide) (by decide) (by decide) (by decide)]; exact hs13_ge _ (by unfold ASM_HDR_EMPTYG; omega),
        by rw [Nat.add_assoc, hhdr_stL (ASM_HDR_EMPTYG + 1) (by decide) (by decide) (by decide) (by decide)]; exact hs13_ge _ (by unfold ASM_HDR_EMPTYG; omega),
        by rw [Nat.add_assoc, hhdr_stL (ASM_HDR_EMPTYG + 2) (by decide) (by decide) (by decide) (by decide)]; exact hs13_ge _ (by unfold ASM_HDR_EMPTYG; omega),
        by rw [Nat.add_assoc, hhdr_stL (ASM_HDR_EMPTYG + 3) (by decide) (by decide) (by decide) (by decide)]; exact hs13_ge _ (by unfold ASM_HDR_EMPTYG; omega),
        fun ne' hne' => ?_⟩, rfl, rfl, rfl, rfl, hwPL, hcap, hk⟩
      have hne_eq : ne' = ne := Option.some.inj hne'.symm
      subst hne_eq
      refine ⟨?_, ?_, ?_, by dsimp only [x', ne, resSz]; omega, by dsimp only [x', ne, resSz]; omega, hbrH_lt,
        hG.2.1, hG.2.2.1,
        fun j _ => ⟨by rw [ha'_trees]; rfl, by rw [ha'_trees]; rfl, by rw [ha'_trees]; rfl⟩,
        by rw [ha'_ord]; exact hOrdRepL,
        by exact hCFRepL,
        fun j hj => (hBR_all j hj).1,
        fun j hj => by rw [ha'_trees, ha'_ord]; exact (hBR_all j hj).2.2.1,
        fun addr ha => ⟨fun ho => by have := (hordFt_rg addr ho).1; omega,
          fun hc => by rcases hCFFtL addr hc with hold | hnew; have := (hcfFt_rg addr hold).1; omega; omega,
          by dsimp only [x', ne]; omega,
          fun j hj hb => by have := ((hBR_all j hj).2.2.2 addr hb).1; omega⟩,
        fun addr ho => ⟨fun hc => by
            have := (hordFt_rg addr ho).2
            rcases hCFFtL addr hc with hold | hnew
            · have := (hcfFt_rg addr hold).1; omega
            · omega,
          by have := (hordFt_rg addr ho).2; dsimp only [x', ne]; omega,
          fun j hj hb => by have := (hordFt_rg addr ho).2; have := ((hBR_all j hj).2.2.2 addr hb).1; omega⟩,
        fun addr hc => ⟨by
            dsimp only [x', ne]
            rcases hCFFtL addr hc with hold | hnew
            · have := (hcfFt_rg addr hold).2; omega
            · omega,
          fun j hj hb => ((hBR_all j hj).2.2.2 addr hb).2.2 hc⟩,
        fun addr ht j hj hb => by have := ((hBR_all j hj).2.2.2 addr hb).1; dsimp only [x', ne] at ht; omega,
        hBR_disj⟩
      · rw [hL_fr _ (by unfold ASM_HDR_ORDH ASM_HDR_SIZE at *; omega)
          (fun hc => by have := (hcfFt_rg _ hc).1; unfold ASM_HDR_ORDH ASM_HDR_SIZE at *; omega)
          (by unfold ASM_HDR_ORDH ASM_HDR_SIZE at *; omega)]
        dsimp only [s23, s22, s21, s20]; rw [Function.update_of_ne (by unfold ASM_HDR_ORDH ASM_HDR_TBL; omega)]
        rw [hCF_fr _ (by unfold ASM_HDR_ORDH ASM_HDR_SIZE at *; omega) (fun hf => hf)]
        dsimp only [s19, s18, s17]; rw [Function.update_of_ne (by unfold ASM_HDR_ORDH ASM_HDR_CFH; omega)]
        rw [hOrd_fr _ (by unfold ASM_HDR_ORDH ASM_HDR_SIZE at *; omega) (fun hf => hf)]
        simp [s16, ne]
      · rw [hL_fr _ (by unfold ASM_HDR_CFH ASM_HDR_SIZE at *; omega)
          (fun hc => by have := (hcfFt_rg _ hc).1; unfold ASM_HDR_CFH ASM_HDR_SIZE at *; omega)
          (by unfold ASM_HDR_CFH ASM_HDR_SIZE at *; omega)]
        dsimp only [s23, s22, s21, s20]; rw [Function.update_of_ne (by unfold ASM_HDR_CFH ASM_HDR_TBL; omega)]
        rw [hCF_fr _ (by unfold ASM_HDR_CFH ASM_HDR_SIZE at *; omega) (fun hf => hf)]
        simp [s19, ne]
      · rw [hL_fr _ (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)
          (fun hc => by have := (hcfFt_rg _ hc).1; unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)
          (by unfold ASM_HDR_TBL ASM_HDR_SIZE at *; omega)]
        simp [s23, s22, ne]
    · -- R.Respects
      have hcap1 : vCap + eCap + 2 ≤ capB := hcap.1
      refine ⟨by simp [Outcome.value]; omega,
        by simp only [Outcome.value, alloc, asmTopAlloc, List.getD_eq_getElem?_getD,
             List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
           dsimp only [hStart, cOrdPtr, resSz, capB] at *; omega,
        fun addr ha => hzL addr (by simp only [Outcome.value] at ha; omega),
        fun addr ha _ => by
          rw [hL_fr addr (by omega) (fun hc => by have := (hcfFt_rg addr hc).1; omega) (by omega)]
          exact hs23_lt addr ha,
        fun addr ha => ?_⟩
      rcases ha with h1 | h2 | h3
      · exact Or.inr ⟨h1.1, by simp [Outcome.value]; omega⟩
      · exact Or.inr ⟨by dsimp only [x'] at h2; omega, by simp [Outcome.value]; exact h2.2⟩
      · rcases h3 with ho | hc | ht | ⟨j, hj, hb⟩
        · have := hordFt_rg addr ho; exact Or.inr ⟨by omega, by simp [Outcome.value]; omega⟩
        · rcases hCFFtL addr hc with hold | hnew
          · have := hcfFt_rg addr hold; exact Or.inr ⟨by omega, by simp [Outcome.value]; omega⟩
          · exact Or.inr ⟨by omega, by simp [Outcome.value]; omega⟩
        · dsimp only [x', ne] at ht; exact Or.inr ⟨by omega, by simp [Outcome.value]; omega⟩
        · have := (hBR_all j hj).2.2.2 addr hb; exact Or.inr ⟨by omega, by simp [Outcome.value]; omega⟩
    · -- Cost bound
      have hTcost : T.cost a'.st =
          (Finset.range k).sum fun j =>
            (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
              (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord₀ j).machCost := by
        have h := asm_init_cost_eq lsfInit C_lsst depth (fun _ => canonicalSparsify impl)
          (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ g₀ ord₀
        simpa [a', hGne] using h
      set S := (Finset.range k).sum fun j =>
        (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
          (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord₀ j).machCost
      obtain ⟨hGm_le_S, hLSF_le_S, hk_le_S, hkGm_le_S⟩ :=
        init_machCost_bounds (lsfInit := lsfInit) (depth := depth)
          (sparsify := fun _ => canonicalSparsify impl)
          (params := canonicalSparsifyParams impl) (spanConst := dsAmortConst impl)
          (M := M) (N := N) (G := G) (ℓ₀ := ℓ₀) (ord := ord₀) hk
      have hOrdCost' : cOrd + (ordStoreRep vCap eCap).phi ordH xOrd' stOrd.mem ≤
          ordStoreMul * (1 + ordRecordsWords (compactRecs recs)) * ordStoreLog eCap := by
        change cOrd + (ordStoreRep vCap eCap).phi ordH xOrd' stOrd.mem ≤
          ordStoreMul * (1 + ordRecordsWords (readOrdRecordsAt s16.mem cOrdPtr)) * ordStoreLog eCap at hOrdCost
        rw [hrecs16] at hOrdCost; exact hOrdCost
      have hOrdBound := ordStoreInitCost_le_of_compact hGval hcap hOrdAt.1 hRot
      have hOrdBoundS : ordStoreMul * (1 + ordRecordsWords (compactRecs recs)) * ordStoreLog eCap ≤
          32000 * 6 * (capExp + 1) * S := by
        calc ordStoreMul * (1 + ordRecordsWords (compactRecs recs)) * ordStoreLog eCap
            ≤ 32000 * 6 * capExp * ((G.m + 1) * bundleLogFactor M N) := hOrdBound
          _ ≤ 32000 * 6 * (capExp + 1) * S := Nat.mul_le_mul (by omega) hGm_le_S
      have hCFBoundS : CFS.mul capExp limbMul * (G.n + G.m + 1 + k * lsfInitSize G * bundleLogFactor M N ^ 3) ≤
          CFS.mul capExp limbMul * (S + G.n + G.m + ordListWords mem ord + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hCFExpBoundS : CFS.mul capExp limbMul * (k * ((G.n + G.m + 1) * bundleLogFactor M N)) ≤
          2 * CFS.mul capExp limbMul * (S + G.n + G.m + ordListWords mem ord + 1) := by
        have h1 : k * ((G.n + G.m + 1) * bundleLogFactor M N) ≤ 2 * S := by
          calc k * ((G.n + G.m + 1) * bundleLogFactor M N)
              ≤ k * (2 * (G.m + 1) * bundleLogFactor M N) :=
                Nat.mul_le_mul_left k (Nat.mul_le_mul_right _ (by omega))
            _ = 2 * (k * ((G.m + 1) * bundleLogFactor M N)) := by ring
            _ ≤ 2 * S := Nat.mul_le_mul_left 2 hkGm_le_S
        calc CFS.mul capExp limbMul * (k * ((G.n + G.m + 1) * bundleLogFactor M N))
            ≤ CFS.mul capExp limbMul * (2 * S) := Nat.mul_le_mul_left _ h1
          _ = 2 * CFS.mul capExp limbMul * S := by ring
          _ ≤ 2 * CFS.mul capExp limbMul * (S + G.n + G.m + ordListWords mem ord + 1) :=
              Nat.mul_le_mul_left _ (by omega)
      have hBRSum : (Finset.range k).sum (fun j => BRS.mul capExp limbMul *
          (initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
            (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord₀ j).machCost) =
          BRS.mul capExp limbMul * S := (Finset.mul_sum ..).symm
      have hphi_new : R.phi heap x' { stL with regs := Function.update stL.regs 17 resSz }.mem =
          (ordStoreRep vCap eCap).phi ordH xOrd' stOrd.mem +
          CF.rep.phi cfH xCF' stL.mem +
          (Finset.range k).sum (fun j => BR.rep.phi (brH j) (xBR j) stL.mem) := by
        simp only [R, asmTopRepEq, asmTopPhi, x', ne]; rfl
      change _ + R.phi heap x' _ ≤ P.mul * (T.cost a'.st + G.n + G.m + ordListWords mem ord + 1)
      rw [hTcost, hphi_new]
      rw [hBRSum, hCFPhi23] at hCostL
      have hdist : P.mul * (S + G.n + G.m + ordListWords mem ord + 1) =
          32000 * 6 * (capExp + 1) * (S + G.n + G.m + ordListWords mem ord + 1) +
          3 * CFS.mul capExp limbMul * (S + G.n + G.m + ordListWords mem ord + 1) +
          BRS.mul capExp limbMul * (S + G.n + G.m + ordListWords mem ord + 1) +
          500 * (S + G.n + G.m + ordListWords mem ord + 1) := by
        simp only [P, asmTopParams]; ring
      have hcf3 : 3 * CFS.mul capExp limbMul * (S + G.n + G.m + ordListWords mem ord + 1) =
          CFS.mul capExp limbMul * (S + G.n + G.m + ordListWords mem ord + 1) +
          2 * CFS.mul capExp limbMul * (S + G.n + G.m + ordListWords mem ord + 1) := by ring
      have h1 : 32000 * 6 * (capExp + 1) * S ≤ 32000 * 6 * (capExp + 1) * (S + G.n + G.m + ordListWords mem ord + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : BRS.mul capExp limbMul * S ≤ BRS.mul capExp limbMul * (S + G.n + G.m + ordListWords mem ord + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega

end MinCostFlow.SparseCore.Program
