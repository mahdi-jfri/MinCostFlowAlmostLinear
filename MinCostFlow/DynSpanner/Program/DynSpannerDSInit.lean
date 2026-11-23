module

public import MinCostFlow.DynSpanner.Program.DynSpannerDSLemmas
public import MinCostFlow.DynSpanner.Program.DynSpannerInit

/-!
# The data structure of Theorem 8.2: the initialization

`dynSpannerDS_init` proves the initialization clause of `DSRep.Implements` for the procedure
`dsInitStmt`: from the graph read from memory it builds the representation of the abstract state
`⟨G, []⟩`, with the clauses of Theorem 8.2 for the empty history, within the cost bound of
`dsInitContract` plus the first potential `1440 Φ₀` (`dsInitBank`, the bank of the empty
history). The proof reads the post of `dsInit_meetsContract`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- The bases of the procedures that `dsInitStmt` calls. -/
structure DSInitBases where
  bOps : ℕ
  bEdge : ℕ
  bBatch : ℕ
  bPhase : ℕ
  bLW : ℕ
  bSpDyn : ℕ
  bInit : ℕ
  bSort : ℕ
  bSplit : ℕ
  bFwd : ℕ
  bRevPrim : ℕ
  bGT : ℕ
  bRevCore : ℕ
  bRevDyn : ℕ
  bEmit : ℕ
  bGuest : ℕ
  bRev : ℕ

/-- Program `p` holds the procedures that `dsInitStmt` calls, at the bases `bi`. -/
structure HasDSInitProcs (impl : SparsifyImpl) (p : Program) (bi : DSInitBases) : Prop where
  hpInit : p.HasAt bi.bInit
    (initProcs bi.bOps bi.bEdge bi.bBatch bi.bPhase bi.bLW bi.bSpDyn bi.bInit)
  hpOps : p.HasAt bi.bOps dgOpsProcs
  hpBatch : p.HasAt bi.bBatch (dgBatchProcs bi.bOps bi.bEdge bi.bSplit bi.bBatch)
  hpPhase : p.HasAt bi.bPhase (phaseProcs bi.bOps bi.bEdge)
  hpLW : p.HasAt bi.bLW (levelWalkProcs bi.bOps bi.bRev)
  hpRev : p.HasAt bi.bRev (revProcs bi.bOps bi.bRev)
  hpSpDyn : p.HasAt bi.bSpDyn
    (sparsifyDynProcs impl.program.regBound impl.cw bi.bFwd bi.bRevDyn bi.bGuest)
  hpGuest : p.HasAt bi.bGuest (sparsifyGuestProcs impl bi.bGuest)
  hpFwd : p.HasAt bi.bFwd (gtForwardProcs bi.bOps bi.bGT bi.bEmit bi.bFwd)
  hpEmit : p.HasAt bi.bEmit (gtEmitProcs bi.bSort bi.bOps bi.bGT)
  hpRevDyn : p.HasAt bi.bRevDyn (gtRevDynProcs bi.bOps bi.bGT bi.bRevCore)
  hpRevCore : p.HasAt bi.bRevCore (gtRevCoreProcs bi.bBatch bi.bRevPrim)
  hpRevPrim : p.HasAt bi.bRevPrim gtRevPrimProcs
  hpEdge : p.HasAt bi.bEdge (dgEdgeProcs bi.bOps)
  hpGT : p.HasAt bi.bGT (gtProcs bi.bSort bi.bOps)
  hpSort : p.HasAt bi.bSort (sortProcs bi.bSort)

/-- The initialization clause of `DSRep.Implements` for the data structure of Theorem 8.2. -/
theorem dynSpannerDS_init (P : DSParams) {p : Program} {bi : DSInitBases}
    (hp : HasDSInitProcs P.impl p bi) :
    ∀ args mem pos ω, (∀ a ∈ args, a < 2 ^ P.w) → (dynSpannerDS P).initPre args mem →
      ZeroFrom mem (heapArg args) →
      heapArg args + (dynSpannerDS P).initSpace args mem < 2 ^ P.w →
      ∃ body, p.procs[bi.bInit + initIdx]? = some body ∧ ∃ o st' c,
        Runs P.w p ω body (startState args mem pos) o st' c ∧ ∃ s' x',
          (dynSpannerRep P).rep (heapArg args) s' x' st'.mem ∧
          (dynSpannerDS P).initPost args mem s' st'.mem ∧
          (dynSpannerRep P).Respects (fun _ => False) (heapArg args)
            ((dynSpannerDS P).initSpace args mem) mem o.value (heapArg args) x' st'.mem ∧
          c + (dynSpannerRep P).phi (heapArg args) x' st'.mem ≤
            (dynSpannerDS P).initCost args mem := by
  intro args mem pos ω hW hpre _ _
  obtain ⟨q, nV, V_ptr, nE, E_ptr, h, rfl, hq, hL, hpst, hpreI⟩ := hpre
  have hpreI' := hpreI
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hGval, hGm, -, hGe, -⟩ := hpreI'
  obtain ⟨body, hget, o, st', c, hrun, hpost, hcost⟩ :=
    dsInit_meetsContract hp.hpInit hp.hpOps hp.hpBatch hp.hpPhase hp.hpLW hp.hpRev hp.hpSpDyn
      hp.hpGuest hp.hpFwd hp.hpEmit hp.hpRevDyn hp.hpRevCore hp.hpRevPrim hp.hpEdge hp.hpGT
      hp.hpSort _ mem pos ω hW hpreI
  refine ⟨body, hget, o, st', c, hrun, ?_⟩
  obtain ⟨V_ptr', E_ptr', b, hargs, hret_ge, hret_le, hzF,
    ⟨x, hxV, hxE, hxIv, -, hStateAt, hRevAll⟩, hfr, hgenF⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := hargs
  set G := initArgsGraph [P.L, q, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h] mem with hG
  have hheap : heapArg [P.L, q, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h] = h := rfl
  rw [hheap]
  have hqs : DSHist.q P ⟨G, []⟩ = q := hq.symm
  have hstate : DSHist.state P ⟨G, []⟩ = (init G P.L q (canonicalSparsify P.impl)).state := by
    simp only [DSHist.state, DSHist.flat, List.flatten_nil, List.length_nil, runState, hqs]
  have hbank : DSHist.bank P ⟨G, []⟩ = dsInitBank P G := by
    simp [DSHist.bank, dsBank, dsBankTotal, dsSpent, dsInitBank, DSHist.q]
  refine ⟨⟨G, []⟩, (⟨G, []⟩, x), ⟨rfl, ⟨hL, hGval, hGm, hGe,
      by simp [DSHist.flat, MGraph.BatchIsValid],
      by simp [DSHist.flat], by simp [DSHist.flat, batchSplitCount], hstate ▸ hStateAt,
      by simpa [DSHist.flat, hqs] using hRevAll [], ?_⟩, hpst⟩,
    ⟨rfl, theorem82Clauses_of P hGval hL hGm (by simp [MGraph.BatchIsValid]) (by simp)
      (by simp [batchSplitCount])⟩,
    ⟨by omega, ?_, hzF, fun a ha _ => hfr a ha, fun a ha => Or.inr ?_⟩, ?_⟩
  · rw [hgenF]; simp [DSHist.genBound, DSHist.flat]
  · show o.value ≤ h + (dsFixedSize P.L P.vCap P.eCap +
      dsInitCoreSpaceBound P.impl P.mMax P.vCap P.eCap G)
    omega
  · rcases ha with ⟨h1, h2⟩ | ⟨iv, hiv, h1, h2⟩
    · rw [hxV, hxE] at h2; exact ⟨h1, by omega⟩
    · rw [hxIv] at hiv
      simp only [List.mem_singleton] at hiv
      subst hiv
      exact ⟨le_trans (Nat.le_add_right _ _) h1, h2⟩
  · simp only [dynSpannerRep, dynSpannerDS, hbank]
    have hc : c ≤ (dsInitContract P.impl P.mMax P.w P.L q P.vCap P.eCap G [] []).cost
        [P.L, q, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h] mem := by
      simpa only [dsInitContract] using hcost
    have hq1 : [P.L, q, P.vCap, P.eCap, nV, V_ptr, nE, E_ptr, h].getD 1 0 = q := rfl
    rw [hq1, ← hG]
    omega

end

end MinCostFlow.DynSpanner.Program
