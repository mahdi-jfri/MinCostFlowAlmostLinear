module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBody
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBackCode
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitS0Model
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitEmbModel
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitFront
import MinCostFlow.SparseCore.Program.SpanBucketInit
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The back of the build: the root table, `S₀`, its marks, and the embedding table (`AssemblyFirstInitBack`)

Steps 5 and 6 of the body of the build (`asmFirstInitBackStmt`, `AssemblyFirstInitBody.lean`):
1. the table of roots (`rootTblBody`), placed at register `29`;
2. the output graph `S₀` (`asmFirstInitS0Body`), rebuilt from the spanners at register `26` using
   the root table query (`rootTblQuery`) so that P4's cells below the heap pointer are untouched;
3. the marks of `S₀` on the tour (`asmFirstInitMarkBody`), exporting `S₀` from `r30 + 7` and
   marking both ends of every edge of `S₀` without growing the tour's footprint;
4. the embedding table (`asmFirstInitEmbBody`), starting from empty walks on `G` and refreshing
   with the spanner table at register `26`.

`AsmFiBackIn` packs the exact inputs that these four calls read at register `29`, and
`asmFirstInitBack_runs` carries their postconditions into `AsmFiBackOut`: the registers `30` to
`33`, the output graph `tr.S_cur` at `r30 + 7` with handle `r30 + 5` (`outGraphRep`), the tour
with `OutMarksOf`, the embedding table agreeing with `tr.emb` on every core edge, memory below
register `29` unchanged outside the tour's footprint, fresh memory from register `33` on, and the
cost as the sum of the four steps plus `100`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Space bound, input state, and output state -/

/-- The fresh words used by the four calls of the back (`asmFirstInitBackStmt`): the table of
roots, `S₀` with P10's rebuild scratch, the temporary export of `S₀` for the marks, and the
embedding table with its refresh walks. -/
noncomputable def asmFiBackSpace (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (slots : List ℕ) (vCap eCap : ℕ) (S : MGraph) : ℕ :=
  rootTblSpace vCap eCap +
    (7 + dynGraphSize vCap eCap + slots.length + 2 * rebuildSize P S6 slots) +
    (4 + S.n + 3 * S.m) +
    (3 + eCap + embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1))

/-- **The input of the back** at the start of `asmFirstInitBackStmt` (heap pointer `h29` in
register `29`): the registers read by the four calls, P4's export at `expPtr`, the graph `G` at
`graph`, the tour handle at `h + ASM_BR_TOUR` and the unmarked tour by its footprint, the slot
list at `slotsPtr`, the spanner table `S6` at `spanTbl`, the model facts tying `S6` and `tr`
together, and zero memory from `h29` on. -/
structure AsmFiBackIn (P : DSParams) (slotCap cap : ℕ) (tr : BundleTreeState P.L)
    (ord : ℕ → List End) (G : MGraph) (j graph expPtr expEnd L capExp M N vCap eCap h tourH : ℕ)
    (xTour : (tourAsmRep vCap eCap).τ) (slotsPtr spanTbl h29 : ℕ) (slots : List ℕ)
    (slotOf : Finset ℕ × ℤ → ℕ) (S6 : BucketSpannerState cap) (x6 : BucketSpannerMeta P.L cap)
    (st : State) : Prop where
  r1 : st.regs 1 = j
  r2 : st.regs 2 = graph
  r4 : st.regs 4 = expPtr
  r10 : st.regs 10 = vCap
  r11 : st.regs 11 = eCap
  r14 : st.regs 14 = h
  r23 : st.regs 23 = slotsPtr
  r24 : st.regs 24 = slots.length
  r26 : st.regs 26 = spanTbl
  r29 : st.regs 29 = h29
  rec_tour : st.mem (h + ASM_BR_TOUR) = tourH
  rec_tour_lt : h + ASM_BR_TOUR < h29
  hG : DynGraphAt st.mem graph vCap eCap G
  hG_le : graph + dynGraphSize vCap eCap ≤ h29
  hExp : CompBranchExportAt P.w st.mem expPtr expEnd L capExp M N vCap eCap tr.cs
  hExp_le : expEnd ≤ h29
  hlist : ListAt st.mem slotsPtr slots
  hlist_le : slotsPtr + slots.length ≤ h29
  hS6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 st.mem
  hfoot6 : ∀ a, bucketFoot spanTbl x6 a → a < h29
  hspan_le : spanTbl ≤ h29
  htour_rep : (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap).rep tourH
    ⟨outCoreOrder tr ord, ∅⟩ xTour st.mem
  htour_foot : ∀ a, (tourAsmRep vCap eCap).foot tourH xTour a → a < h29
  htour_disj_G : ∀ a, graph ≤ a → a < graph + dynGraphSize vCap eCap →
    ¬ (tourAsmRep vCap eCap).foot tourH xTour a
  htour_disj_span : ∀ a, bucketFoot spanTbl x6 a →
    ¬ (tourAsmRep vCap eCap).foot tourH xTour a
  htour_disj_slots : ∀ a, slotsPtr ≤ a → a < slotsPtr + slots.length →
    ¬ (tourAsmRep vCap eCap).foot tourH xTour a
  hz : ZeroFrom st.mem h29
  hcsG : tr.cs.G = G
  hVlt : ∀ v ∈ G.V, v < vCap
  hElt : ∀ e ∈ G.E, e < eCap
  hRot : HasRotOrder tr ord
  hScurInv : RestartScurModelInv tr
  hScurVal : tr.S_cur.IsValid
  hBD : BunDisjointInv tr
  hSE : tr.S_cur.E = (activePairs tr).biUnion fun q => (tr.dyn q).H.E
  hMap : SlotMapOK tr slotCap cap slots slotOf
  hspanMatch : ∀ q ∈ activePairs tr, ∃ (hs : slotOf q < cap) (d : DSHist),
    S6 ⟨slotOf q, hs⟩ = some d ∧ d.state P = tr.dyn q
  hGE : ∀ q ∈ activePairs tr, (tr.dyn q).G.E = (tr.bun q).edges
  hw16 : 16 ≤ 2 ^ P.w
  hjW : j < 2 ^ P.w
  hSPe : P.eCap ≤ eCap
  hroom : h29 + asmFiBackSpace P S6 slots vCap eCap tr.S_cur < 2 ^ P.w

/-- **What the back leaves** at the end of `asmFirstInitBackStmt`, in the state `st'`, from the
start memory `mem` and registers `regs`: the registers `30` to `33` (and all registers below `30`
unchanged), the output graph `tr.S_cur` at `h30 + 7` with handle `h30 + 5` (`outGraphRep`), the
tour marked with `tr.S_cur.E` (`OutMarksOf`) without growing its footprint, the embedding table at
`h32` agreeing with `tr.emb` on every core edge, memory below `h29` unchanged outside the tour's
footprint, and zero memory from `h33` on. -/
structure AsmFiBackOut (P : DSParams) {cap : ℕ} (tr : BundleTreeState P.L) (ord : ℕ → List End)
    (vCap eCap tourH h29 : ℕ) (xTour : (tourAsmRep vCap eCap).τ)
    (S6 : BucketSpannerState cap) (slots : List ℕ) (mem regs : ℕ → ℕ)
    (h30 h31 h32 h33 : ℕ) (sTour' : OutTourAbs) (xTour' : (tourAsmRep vCap eCap).τ)
    (yEmb : EmbConc) (st' : State) : Prop where
  regs_in : ∀ i < 30, st'.regs i = regs i
  r30 : st'.regs 30 = h30
  r31 : st'.regs 31 = h31
  r32 : st'.regs 32 = h32
  r33 : st'.regs 33 = h33
  h30_eq : h30 = h29 + rootTblSpace vCap eCap
  h31_lo : h30 + 7 + dynGraphSize vCap eCap ≤ h31
  h31_hi : h31 ≤ h30 + 7 + dynGraphSize vCap eCap + slots.length + 2 * rebuildSize P S6 slots
  h32_eq : h32 = h31 + 4 + tr.S_cur.n + 3 * tr.S_cur.m
  h33_lo : h32 + 3 + eCap ≤ h33
  h33_hi : h33 ≤ h32 + 3 + eCap + embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1)
  h33_space : h33 ≤ h29 + asmFiBackSpace P S6 slots vCap eCap tr.S_cur
  out_ptr : st'.mem (h30 + 5) = h30 + 7
  out_graph : DynGraphAt st'.mem (h30 + 7) vCap eCap tr.S_cur
  out_rep : (outGraphRep vCap eCap).rep (h30 + 5) tr.S_cur (h30 + 7) st'.mem
  out_foot : ∀ a, (outGraphRep vCap eCap).foot (h30 + 5) (h30 + 7) a → h30 ≤ a ∧ a < h31
  tour_rep : (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap).rep tourH sTour' xTour'
    st'.mem
  tour_marks : OutMarksOf sTour' (outCoreOrder tr ord) tr.S_cur.E
  tour_foot : ∀ a, (tourAsmRep vCap eCap).foot tourH xTour' a →
    (tourAsmRep vCap eCap).foot tourH xTour a
  emb_rep : (embRep eCap).rep h32 yEmb.view yEmb st'.mem
  emb_dom : (coreGraph tr.cs.G tr.cs.lsf).E ⊆ yEmb.view.dom
  emb_eq : ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E, yEmb.view.emb e = tr.emb e
  emb_foot : ∀ a, embFoot eCap h32 yEmb a → h32 ≤ a ∧ a < h33
  low : ∀ a < h29, ¬ (tourAsmRep vCap eCap).foot tourH xTour a → st'.mem a = mem a
  zero : ZeroFrom st'.mem h33

/-! ## Helper lemmas -/

/-- The footprint of `rootTblRep` produced by `rootTbl_runs` lies inside
`[heap, heap + rootTblSpace vCap eCap)`. -/
private theorem rootTbl_foot_bounds {vCap eCap heap : ℕ} {V : Finset ℕ} {a : ℕ}
    (ha : (rootTblRep vCap V).foot heap
      (heap + 2 + dynGraphSize vCap eCap, heap + 2 + dynGraphSize vCap eCap + vCap) a) :
    heap ≤ a ∧ a < heap + rootTblSpace vCap eCap := by
  unfold rootTblRep at ha
  unfold rootTblSpace
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- Rooted-spanning-forest properties needed by `rootTbl_runs`, extracted from
`IsRootedSpanningForestOf`. -/
private theorem rsf_rootTbl_facts {G : MGraph} {RF : RootedForest} {roots : List ℕ}
    (hRF : RF.IsRootedSpanningForestOf G) (hroots_fs : roots.toFinset = RF.R) :
    RF.F.IsValid ∧ RF.F.V = G.V ∧
    (∀ r ∈ roots, r ∈ RF.F.V) ∧
    (∀ u ∈ RF.F.V, RF.root u ∈ roots ∧ RF.F.Connected u (RF.root u)) ∧
    (∀ r₁ ∈ roots, ∀ r₂ ∈ roots, RF.F.Connected r₁ r₂ → r₁ = r₂) := by
  obtain ⟨hFor, hFV, hRsub, hUniq, -⟩ := hRF
  have hrR : ∀ r ∈ roots, r ∈ RF.R := fun r hr => hroots_fs ▸ List.mem_toFinset.mpr hr
  refine ⟨hFor.1, hFV, fun r hr => hFV ▸ hRsub (hrR r hr), fun u hu => ?_, fun r₁ h₁ r₂ h₂ hc => ?_⟩
  · have huG : u ∈ G.V := hFV ▸ hu
    have hex : ∃ r, r ∈ RF.R ∧ RF.F.Connected u r := by
      obtain ⟨r, hr, -⟩ := hUniq u huG
      exact ⟨r, hr⟩
    have hsp : Classical.choose hex ∈ RF.R ∧ RF.F.Connected u (Classical.choose hex) :=
      Classical.choose_spec hex
    have hrt_eq : RF.root u = Classical.choose hex := by
      unfold RootedForest.root
      exact dite_eq_left_of_eq_true (eq_true hex)
    rw [hrt_eq]
    exact ⟨List.mem_toFinset.mp (hroots_fs.symm ▸ hsp.1), hsp.2⟩
  · have h1R := hrR r₁ h₁
    have h2R := hrR r₂ h₂
    exact (hUniq r₁ (hRsub h1R)).unique ⟨h1R, MGraph.connected_refl RF.F r₁⟩ ⟨h2R, hc⟩

/-- Arithmetic step separating the four space requirements from `asmFiBackSpace`. -/
private theorem back_space_parts {h29 rts s0b mk embB W : ℕ}
    (hroom : h29 + (rts + s0b + mk + embB) < W) (hmk : 2 ≤ mk) (hemb : 2 ≤ embB) :
    h29 + rts < W ∧
    (h29 + rts) + s0b + 2 < W ∧
    ∀ h31, h31 ≤ (h29 + rts) + s0b →
      h31 + mk + 2 < W ∧ (h31 + mk) + embB < W := by
  refine ⟨by omega, by omega, fun h31 hle => ⟨by omega, by omega⟩⟩

/-! ## The run of the back -/

set_option maxHeartbeats 1000000 in
/-- **The run of the back.** From `AsmFiBackIn`, the four calls of `asmFirstInitBackStmt` run
(`rootTbl_runs`, `asmFirstInitS0_runs` with `rootTblQuery`, `asmFirstInitMark_runs` on
`g = r30 + 7`, and `asmFirstInitEmb_runs` with the spanner table `r26`) and leave `AsmFiBackOut`,
with cost at most the sum of the four steps plus `100`. -/
theorem asmFirstInitBack_runs {P : DSParams} {slotCap cap : ℕ}
    {tr : BundleTreeState P.L} {ord : ℕ → List End} {G : MGraph}
    {j graph expPtr expEnd L capExp M N vCap eCap h tourH : ℕ}
    {xTour : (tourAsmRep vCap eCap).τ} {slotsPtr spanTbl h29 : ℕ} {slots : List ℕ}
    {slotOf : Finset ℕ × ℤ → ℕ} {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap}
    {st : State} {p : Program} (F : AsmFirstInitProcs) (ω : ℕ → Bool)
    {fGraph bC bOps bEdge bSplit bBatch bLoop bT fExp fTourMark fEmbTbl fEmbRef bCopy bSpan : ℕ}
    (hfRootTbl : p.procs[F.fRootTbl]? = some (rootTblBody fGraph bC))
    (hpG : MeetsContract P.w p fGraph (initGraphFromExportContract P.w vCap eCap tr.cs.lsf.F.F))
    (hpC : p.HasAt bC (compMapModule bC))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpLoop : p.HasAt bLoop (readLoopProcs bEdge))
    (hpS0 : p.HasAt F.fS0 (asmFirstInitS0Module bOps bEdge bBatch bLoop F.fS0))
    (hpT : HasTourProcs p bT)
    (hfMark : p.procs[F.fMark]? = some (asmFirstInitMarkBody fExp fTourMark))
    (hfExp : p.procs[fExp]? = some asmFirstExportDynGraphStmt)
    (hfTourMark : p.procs[fTourMark]? = some (tourMarkExportStmt (tourOp bT 7)))
    (hfEmb : p.procs[F.fEmb]? = some (asmFirstInitEmbBody fEmbTbl fEmbRef))
    (hfEmbTbl : p.procs[fEmbTbl]? = some asmFirstInitEmbTblBody)
    (hfEmbRef : p.procs[fEmbRef]? =
      some (embRefreshStmt bCopy (bSpan + bsOffRead + spanReadIdxPiWalkPtr)))
    (hpCopy : p.HasAt bCopy [copyWords])
    (hpSpan : p.HasAt bSpan (bucketSpannerProcs P.impl bSpan))
    (hIn : AsmFiBackIn P slotCap cap tr ord G j graph expPtr expEnd L capExp M N vCap eCap h tourH
      xTour slotsPtr spanTbl h29 slots slotOf S6 x6 st) :
    ∃ h30 h31 h32 h33 sTour' xTour' yEmb st' c,
      Runs P.w p ω (asmFirstInitBackStmt F) st .normal st' c ∧
      AsmFiBackOut P tr ord vCap eCap tourH h29 xTour S6 slots st.mem st.regs
        h30 h31 h32 h33 sTour' xTour' yEmb st' ∧
      c + (tourAsmRep vCap eCap).phi tourH xTour' st'.mem ≤
        rootTblCost tr.cs.lsf.F.F.n tr.cs.lsf.F.F.m tr.cs.lsf.F.R.card +
        (840 * (rebuildSize P S6 slots + slots.length + 1) +
          130 * tr.cs.lsf.F.R.card + 200) +
        (200 * (tr.S_cur.n + tr.S_cur.m + 1) +
          tourMarkExportMul * (tr.S_cur.m + 1) * tourLog eCap + 20) +
        (30 * G.m + embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) + 80) +
        (tourAsmRep vCap eCap).phi tourH xTour st.mem + 100 := by
  set mem := st.mem with hmem
  set Fg := tr.cs.lsf.F.F with hFg
  -- Unpack the `S₀` module procedures
  obtain ⟨hfS0, hfRootQ, hpS0Rest⟩ := asmFirstInitS0Module_hasAt hpS0
  -- Unpack P4's export
  obtain ⟨hExp8, hExpW, -, -, -, hfD_exp,
    ⟨roots, hroots_len, hroots_nd, hroots_fs, hroots_at, -, hroots_hi⟩, -⟩ := hIn.hExp
  have hroots_card : roots.length = tr.cs.lsf.F.R.card := by
    rw [← hroots_fs, List.toFinset_card_of_nodup hroots_nd]
  -- Rooted-spanning-forest facts from `HasRotOrder`
  obtain ⟨C_lsst, ℓ₀, hI, ρ, -⟩ := hIn.hRot
  have hRF : tr.cs.lsf.F.IsRootedSpanningForestOf G := hIn.hcsG ▸ compLSF_RF_isRSF hI
  obtain ⟨hF_val, hF_V, hrV, hrt, huniq⟩ := rsf_rootTbl_facts hRF hroots_fs
  have hFV : ∀ v ∈ Fg.V, v < vCap := fun v hv => hIn.hVlt v (hF_V ▸ hv)
  have hFE : ∀ e ∈ Fg.E, e < eCap := fun e he => hIn.hElt e (hRF.2.2.2.2.2.1 he)
  have hrV_lt : ∀ r ∈ roots, r < vCap := fun r hr => hFV r (hrV r hr)
  -- Active slots, `slotsHE`, edge caps, and `SlotWalkAgree`
  have hact : ∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome := by
    intro s hs
    obtain ⟨q, hq, rfl⟩ := hIn.hMap.2.2.1 s hs
    obtain ⟨hs', d, hd, -⟩ := hIn.hspanMatch q hq
    exact ⟨hs', by rw [hd]; rfl⟩
  have hslotsHE : slotsHE P S6 slots = tr.S_cur.E :=
    (slotsHE_eq_activePairs P hIn.hMap hIn.hspanMatch).trans hIn.hSE.symm
  have hslotGE : ∀ q ∈ activePairs tr, slotGE P S6 (slotOf q) = (tr.bun q).edges := by
    intro q hq
    obtain ⟨hs, d, hd, hst⟩ := hIn.hspanMatch q hq
    unfold slotGE
    simp only [hs, ↓reduceDIte, hd, hst]
    exact hIn.hGE q hq
  have hecap : ∀ s ∈ slots, ∀ e ∈ slotGE P S6 s, e < eCap := by
    intro s hs e he
    obtain ⟨q, hq, rfl⟩ := hIn.hMap.2.2.1 s hs
    rw [hslotGE q hq] at he
    have hq' := mem_activePairs.mp hq
    have hsub := (hIn.hScurInv.2.2.2.2 q.1 hq'.1 q.2 hq'.2).1 he
    exact hIn.hElt e (hIn.hcsG ▸ Finset.sdiff_subset hsub)
  have hagree : SlotWalkAgree P S6 slots :=
    asmFirstInit_slotWalkAgree P hIn.hMap hslotGE hIn.hBD
  have hHB : ∀ q ∈ activePairs tr, (tr.dyn q).H.E ⊆ (tr.bun q).edges := by
    intro q hq
    have hq' := mem_activePairs.mp hq
    exact (hIn.hScurInv.2.2.2.2 q.1 hq'.1 q.2 hq'.2).2.2.2
  have hcoreSub : (coreGraph tr.cs.G tr.cs.lsf).E ⊆ G.E := by
    rw [← hIn.hcsG]; exact Finset.sdiff_subset
  have hEmbModel := asmFirstInit_refresh_emb_eq P hIn.hMap hIn.hspanMatch hIn.hGE hHB hIn.hSE
    hIn.hBD hcoreSub
  -- Space bounds split
  have hspParts := back_space_parts hIn.hroom (by omega) (by omega)
  have hrtPos : 0 < rootTblSpace vCap eCap := by unfold rootTblSpace; omega
  have hw16 := hIn.hw16
  have hASM3 : ASM_BR_TOUR = 3 := rfl
  set fD := mem (expPtr + 1) with hfD
  set rootsPtr := mem (expPtr + 2) with hrootsPtr
  have hnR : mem (expPtr + 3) = roots.length := hroots_len.symm
  have hfDw : fD < 2 ^ P.w := hExpW (expPtr + 1) (by omega) (by omega)
  have hrootsW : rootsPtr < 2 ^ P.w := hExpW (expPtr + 2) (by omega) (by omega)
  have hExp_le := hIn.hExp_le
  have hlist_le := hIn.hlist_le
  have hG_le := hIn.hG_le
  have hspan_le := hIn.hspan_le
  have hrec_tour_lt := hIn.rec_tour_lt
  have hroots_le : rootsPtr + roots.length ≤ h29 := by
    rw [hrootsPtr, hmem, hroots_len]; exact le_trans hroots_hi hExp_le
  have hexpLt : expPtr + 8 ≤ h29 := le_trans hExp8 hExp_le
  set h30 := h29 + rootTblSpace vCap eCap with hh30
  set cmpF := h29 + 2 + dynGraphSize vCap eCap with hcmpF
  set rootOf := cmpF + vCap with hrootOf
  set phi0 := (tourAsmRep vCap eCap).phi tourH xTour mem with hphi0
  set C1 := rootTblCost Fg.n Fg.m tr.cs.lsf.F.R.card with hC1
  set C2 := 840 * (rebuildSize P S6 slots + slots.length + 1) +
    130 * tr.cs.lsf.F.R.card + 200 with hC2
  set C3 := 200 * (tr.S_cur.n + tr.S_cur.m + 1) +
    tourMarkExportMul * (tr.S_cur.m + 1) * tourLog eCap + 20 with hC3
  set C4 := 30 * G.m + embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) + 80
    with hC4
  set T := C1 + C2 + C3 + C4 + phi0 + 100 with hT
  -- Goal in forward cost form
  suffices H : ∃ o st' c, Runs P.w p ω (asmFirstInitBackStmt F) st o st' c ∧
      normalPost (fun st' => ∃ h31 h32 h33 sTour' xTour' yEmb,
        AsmFiBackOut P tr ord vCap eCap tourH h29 xTour S6 slots mem st.regs
          h30 h31 h32 h33 sTour' xTour' yEmb st' ∧
        c + (tourAsmRep vCap eCap).phi tourH xTour' st'.mem ≤ T) o st' by
    obtain ⟨o, st', c, hr, hq⟩ := H
    cases o with
    | returned _ => exact absurd hq id
    | normal =>
      obtain ⟨h31, h32, h33, sTour', xTour', yEmb, hout, hcost⟩ := hq
      exact ⟨h30, h31, h32, h33, sTour', xTour', yEmb, st', c, hr, hout, hcost⟩
  -- Step 1: `rootTbl_runs`
  obtain ⟨st1, c1, hrun1, hrepRT1, hlo1, hz1, hc1⟩ :=
    rootTbl_runs (w := P.w) (bC := bC) (fGraph := fGraph) (vCap := vCap) (eCap := eCap)
      (fD := fD) (hEnd := expEnd) (rootsPtr := rootsPtr) (heap := h29) (pos := st.pos)
      (p := p) ω (F := Fg) (roots := roots) (rt := tr.cs.lsf.F.root) (mem := mem)
      hpG hpC hF_val hFV hFE hfD_exp hIn.hExp_le hroots_at (by omega)
      hrV hrt huniq hIn.hz hspParts.1 hw16 hfDw
  have hargs1 : evalArgs P.w st [.load (.bin .add (.reg 4) (.const 1)), .reg 10, .reg 11,
      .load (.bin .add (.reg 4) (.const 2)), .load (.bin .add (.reg 4) (.const 3)), .reg 29] =
      some [fD, vCap, eCap, rootsPtr, roots.length, h29] := by
    have r4 := hIn.r4; have r10 := hIn.r10; have r11 := hIn.r11; have r29 := hIn.r29
    have e1 : (Expr.load (.bin .add (.reg 4) (.const 1))).eval P.w st = some fD :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r4)
        (Expr.eval_const (by omega)) (by omega)) rfl
    have e2 : (Expr.load (.bin .add (.reg 4) (.const 2))).eval P.w st = some rootsPtr :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r4)
        (Expr.eval_const (by omega)) (by omega)) rfl
    have e3 : (Expr.load (.bin .add (.reg 4) (.const 3))).eval P.w st = some roots.length :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r4)
        (Expr.eval_const (by omega)) (by omega)) hnR
    simp only [evalArgs, e1, e2, e3, Expr.eval_reg_of_eq r10, Expr.eval_reg_of_eq r11,
      Expr.eval_reg_of_eq r29]
  set s1 : State := { mem := st1.mem, regs := Function.update st.regs 30 h30, pos := st1.pos }
    with hs1
  have hcall1 : Runs P.w p ω (.call 30 F.fRootTbl [.load (.bin .add (.reg 4) (.const 1)), .reg 10,
      .reg 11, .load (.bin .add (.reg 4) (.const 2)), .load (.bin .add (.reg 4) (.const 3)),
      .reg 29]) st .normal s1
      (argsSize [.load (.bin .add (.reg 4) (.const 1)), .reg 10, .reg 11,
        .load (.bin .add (.reg 4) (.const 2)), .load (.bin .add (.reg 4) (.const 3)),
        .reg 29] + c1 + 1) :=
    runs_call_iff.mpr ⟨_, _, .returned h30, st1, c1, hargs1, hfRootTbl, hrun1, rfl, rfl, rfl⟩
  -- Step 2: `asmFirstInitS0_runs` with `Q := rootTblQuery`
  let Q := rootTblQuery P.w p (F.fS0 + 1) vCap Fg.V hfRootQ
  have hRTfoot : ∀ a, Q.R.foot h29 (cmpF, rootOf) a → h29 ≤ a ∧ a < h30 :=
    fun a ha => rootTbl_foot_bounds ha
  have hlist1 : ListAt st1.mem slotsPtr slots := fun i hi =>
    (hlo1 _ (by omega)).trans (hIn.hlist i hi)
  have hroots1 : ListAt st1.mem rootsPtr roots := fun i hi =>
    (hlo1 _ (by omega)).trans (hroots_at i hi)
  have hG1 : DynGraphAt st1.mem graph vCap eCap G :=
    hIn.hG.of_agree fun a ha1 ha2 => hlo1 a (by omega)
  have hS6_1 : (bucketSpannerRep P cap).rep spanTbl S6 x6 st1.mem :=
    ((bucketSpannerRep_local P cap) spanTbl S6 x6 mem st1.mem
      fun a ha => (hlo1 a (hIn.hfoot6 a ha)).symm).1 hIn.hS6
  have hQok : ∀ u ∈ G.V, Q.ok tr.cs.lsf.F.root j u ∧ Q.root tr.cs.lsf.F.root j u = tr.cs.lsf.F.root u :=
    fun u hu => ⟨show u ∈ Fg.V from hF_V.symm ▸ hu, rfl⟩
  obtain ⟨o2, st2, c2, x4', hrun2, hptr2, hS0_raw, -, h31_lo, h31_hi, hz2, hfr2, -, hc2⟩ :=
    asmFirstInitS0_runs (w := P.w) (vCap := vCap) (eCap := eCap) (cap := cap) (SP := P)
      (Q := Q) hpOps hpEdge hpBatch hpLoop hpS0Rest
      (b4 := h29) (j := j) (graph := graph) (spanTbl := spanTbl) (slotsPtr := slotsPtr)
      (rootsPtr := rootsPtr) (h := h30) (pos := st1.pos) (slots := slots) (roots := roots)
      (G := G) (lsf := tr.cs.lsf) (S6 := S6) (x6 := x6) (s4 := tr.cs.lsf.F.root)
      (x4 := (cmpF, rootOf)) (mem := st1.mem) (ω := ω)
      hw16 hIn.hSPe (by omega) hIn.hjW (by omega) hrootsW hlist1 (by omega) hact
      hroots1 (by omega) hrV_lt hG1 (by omega) hS6_1 hrepRT1 hQok
      (fun a ha => by have := hIn.hfoot6 a ha; omega)
      (fun a ha => (hRTfoot a ha).2)
      (fun a ha1 ha2 hf => by have := (hRTfoot a hf).1; omega)
      (fun a ha hf => by have := hIn.hfoot6 a ha; have := (hRTfoot a hf).1; omega)
      hz1 (by have := hspParts.2.1; omega)
  set h31 := o2.value with hh31
  have hS0_dg2 : DynGraphAt st2.mem (h30 + 7) vCap eCap tr.S_cur :=
    asmFirstInit_S0_dynGraphAt P hIn.hScurInv hIn.hScurVal
      (hroots_fs.trans hIn.hScurInv.2.1.symm) hslotsHE (hIn.hcsG ▸ hS0_raw)
  have hlo2 : ∀ a < h29, st2.mem a = mem a := fun a ha => by
    have hnot : ¬ Q.R.foot h29 (cmpF, rootOf) a := fun hf => by have := (hRTfoot a hf).1; omega
    exact (hfr2 a (by omega) hnot).trans (hlo1 a ha)
  have hargs2 : evalArgs P.w s1 [.reg 29, .reg 1, .reg 2, .reg 26, .reg 24, .reg 23,
      .load (.bin .add (.reg 4) (.const 2)), .load (.bin .add (.reg 4) (.const 3)),
      .reg 10, .reg 11, .reg 30] =
      some [h29, j, graph, spanTbl, slots.length, slotsPtr, rootsPtr, roots.length, vCap, eCap,
        h30] := by
    have qs : ∀ i, i ≠ 30 → s1.regs i = st.regs i := fun i hi => by
      simp [hs1, Function.update_of_ne hi]
    have r1' : s1.regs 1 = j := (qs 1 (by decide)).trans hIn.r1
    have r2' : s1.regs 2 = graph := (qs 2 (by decide)).trans hIn.r2
    have r4' : s1.regs 4 = expPtr := (qs 4 (by decide)).trans hIn.r4
    have r10' : s1.regs 10 = vCap := (qs 10 (by decide)).trans hIn.r10
    have r11' : s1.regs 11 = eCap := (qs 11 (by decide)).trans hIn.r11
    have r23' : s1.regs 23 = slotsPtr := (qs 23 (by decide)).trans hIn.r23
    have r24' : s1.regs 24 = slots.length := (qs 24 (by decide)).trans hIn.r24
    have r26' : s1.regs 26 = spanTbl := (qs 26 (by decide)).trans hIn.r26
    have r29' : s1.regs 29 = h29 := (qs 29 (by decide)).trans hIn.r29
    have r30' : s1.regs 30 = h30 := by simp [hs1]
    have hm2 : s1.mem (expPtr + 2) = rootsPtr := hlo1 _ (by omega)
    have hm3 : s1.mem (expPtr + 3) = roots.length := (hlo1 _ (by omega)).trans hnR
    have e2 : (Expr.load (.bin .add (.reg 4) (.const 2))).eval P.w s1 = some rootsPtr :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r4')
        (Expr.eval_const (by omega)) (by omega)) hm2
    have e3 : (Expr.load (.bin .add (.reg 4) (.const 3))).eval P.w s1 = some roots.length :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r4')
        (Expr.eval_const (by omega)) (by omega)) hm3
    simp only [evalArgs, e2, e3, Expr.eval_reg_of_eq r29', Expr.eval_reg_of_eq r1',
      Expr.eval_reg_of_eq r2', Expr.eval_reg_of_eq r26', Expr.eval_reg_of_eq r24',
      Expr.eval_reg_of_eq r23', Expr.eval_reg_of_eq r10', Expr.eval_reg_of_eq r11',
      Expr.eval_reg_of_eq r30']
  set s2 : State := { mem := st2.mem, regs := Function.update s1.regs 31 h31, pos := st2.pos }
    with hs2
  have hcall2 : Runs P.w p ω (.call 31 F.fS0 [.reg 29, .reg 1, .reg 2, .reg 26, .reg 24, .reg 23,
      .load (.bin .add (.reg 4) (.const 2)), .load (.bin .add (.reg 4) (.const 3)),
      .reg 10, .reg 11, .reg 30]) s1 .normal s2
      (argsSize [.reg 29, .reg 1, .reg 2, .reg 26, .reg 24, .reg 23,
        .load (.bin .add (.reg 4) (.const 2)), .load (.bin .add (.reg 4) (.const 3)),
        .reg 10, .reg 11, .reg 30] + c2 + 1) :=
    runs_call_iff.mpr ⟨_, _, o2, st2, c2, hargs2, hfS0, hrun2, rfl, rfl, rfl⟩
  -- Step 3: `asmFirstInitMark_runs`
  have hsp34 := hspParts.2.2 h31 (by omega)
  obtain ⟨htour2_rep, htour2_phi⟩ := asmBrTourView_keep tourAsmRep_local ⟨tr, ord, vCap, eCap⟩
    (s := ⟨outCoreOrder tr ord, ∅⟩) (tourH := tourH) (tx := xTour) (mem := mem) (mem' := st2.mem)
    fun a ha => (hlo2 a (hIn.htour_foot a ha)).symm
  obtain ⟨o3, st3, c3, sTour', xTour', hrun3, h32_eq, htour_rep3, htour_marks, htour_foot3,
      hz3, hkeep3, hc3⟩ :=
    asmFirstInitMark_runs (depth := P.L) (w := P.w) (b := bT) (vCap := vCap) (eCap := eCap)
      (tourH := tourH) (g := h30 + 7) (h := h31) (pos := st2.pos) (p := p) hpT ω
      hfExp hfTourMark (tr := tr) (ord := ord) (S := tr.S_cur) (xTour := xTour) (mem := st2.mem)
      hw16 hIn.hRot hIn.hScurInv.2.2.2.1.2.1 hS0_dg2 h31_lo (htour2_rep hIn.htour_rep)
      (fun a ha => by have := hIn.htour_foot a ha; omega) hz2 (by have := hsp34.1; omega)
  set h32 := o3.value with hh32
  have hargs3 : evalArgs P.w s2 [asmFiTourH, .bin .add (.reg 30) (.const 7), .reg 31] =
      some [tourH, h30 + 7, h31] := by
    have r14' : s2.regs 14 = h := by simp [hs2, hs1, hIn.r14]
    have r30' : s2.regs 30 = h30 := by simp [hs2, hs1]
    have r31' : s2.regs 31 = h31 := by simp [hs2]
    have hmT : s2.mem (h + ASM_BR_TOUR) = tourH := (hlo2 _ hIn.rec_tour_lt).trans hIn.rec_tour
    have e0 : asmFiTourH.eval P.w s2 = some tourH :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r14')
        (Expr.eval_const (by omega)) (by omega)) hmT
    have e1 : (Expr.bin .add (.reg 30) (.const 7)).eval P.w s2 = some (h30 + 7) :=
      Expr.eval_add (Expr.eval_reg_of_eq r30') (Expr.eval_const (by omega)) (by omega)
    simp only [evalArgs, e0, e1, Expr.eval_reg_of_eq r31']
  set s3 : State := { mem := st3.mem, regs := Function.update s2.regs 32 h32, pos := st3.pos }
    with hs3
  have hcall3 : Runs P.w p ω (.call 32 F.fMark [asmFiTourH, .bin .add (.reg 30) (.const 7),
      .reg 31]) s2 .normal s3
      (argsSize [asmFiTourH, .bin .add (.reg 30) (.const 7), .reg 31] + c3 + 1) :=
    runs_call_iff.mpr ⟨_, _, o3, st3, c3, hargs3, hfMark, hrun3, rfl, rfl, rfl⟩
  -- Step 4: `asmFirstInitEmb_runs`
  have hlo3 : ∀ a < h29, ¬ (tourAsmRep vCap eCap).foot tourH xTour a → st3.mem a = mem a :=
    fun a ha hnf => (hkeep3 a (by omega) hnf).trans (hlo2 a ha)
  have hG3 : DynGraphAt st3.mem graph vCap eCap G :=
    hIn.hG.of_agree fun a ha1 ha2 => hlo3 a (by omega) (hIn.htour_disj_G a ha1 ha2)
  have hS6_3 : (bucketSpannerRep P cap).rep spanTbl S6 x6 st3.mem :=
    ((bucketSpannerRep_local P cap) spanTbl S6 x6 mem st3.mem fun a ha =>
      (hlo3 a (hIn.hfoot6 a ha) (hIn.htour_disj_span a ha)).symm).1 hIn.hS6
  have hlist3 : ListAt st3.mem slotsPtr slots := fun i hi =>
    (hlo3 _ (by omega) (hIn.htour_disj_slots _ (by omega) (by omega))).trans (hIn.hlist i hi)
  obtain ⟨o4, st4, c4, yEmb, hrun4, hemb_rep4, h33_lo, h33_hi, hz4, hkeep4, hemb_foot4, hc4⟩ :=
    asmFirstInitEmb_runs (w := P.w) (graph := graph) (vCap := vCap) (eCap := eCap)
      (spanH := spanTbl) (slotsPtr := slotsPtr) (h := h32) (pos := st3.pos)
      (fTbl := fEmbTbl) (fRef := fEmbRef) (bCopy := bCopy) (bSpan := bSpan) (cap := cap)
      (p := p) (ω := ω) P rfl hfEmbTbl hfEmbRef hpCopy hpSpan
      hG3 (by omega) hS6_3 (fun a ha => by have := hIn.hfoot6 a ha; omega) (by omega)
      hlist3 (by omega) hact hecap hagree hz3 (by have := hsp34.2; omega)
  set h33 := o4.value with hh33
  have hargs4 : evalArgs P.w s3 [.reg 2, .reg 10, .reg 11, .reg 26, .reg 23, .reg 24, .reg 32] =
      some [graph, vCap, eCap, spanTbl, slotsPtr, slots.length, h32] := by
    have r2' : s3.regs 2 = graph := by simp [hs3, hs2, hs1, hIn.r2]
    have r10' : s3.regs 10 = vCap := by simp [hs3, hs2, hs1, hIn.r10]
    have r11' : s3.regs 11 = eCap := by simp [hs3, hs2, hs1, hIn.r11]
    have r26' : s3.regs 26 = spanTbl := by simp [hs3, hs2, hs1, hIn.r26]
    have r23' : s3.regs 23 = slotsPtr := by simp [hs3, hs2, hs1, hIn.r23]
    have r24' : s3.regs 24 = slots.length := by simp [hs3, hs2, hs1, hIn.r24]
    have r32' : s3.regs 32 = h32 := by simp [hs3]
    simp only [evalArgs, Expr.eval_reg_of_eq r2', Expr.eval_reg_of_eq r10',
      Expr.eval_reg_of_eq r11', Expr.eval_reg_of_eq r26', Expr.eval_reg_of_eq r23',
      Expr.eval_reg_of_eq r24', Expr.eval_reg_of_eq r32']
  set s4 : State := { mem := st4.mem, regs := Function.update s3.regs 33 h33, pos := st4.pos }
    with hs4
  have hcall4 : Runs P.w p ω (.call 33 F.fEmb [.reg 2, .reg 10, .reg 11, .reg 26, .reg 23,
      .reg 24, .reg 32]) s3 .normal s4
      (argsSize [.reg 2, .reg 10, .reg 11, .reg 26, .reg 23, .reg 24, .reg 32] + c4 + 1) :=
    runs_call_iff.mpr ⟨_, _, o4, st4, c4, hargs4, hfEmb, hrun4, rfl, rfl, rfl⟩
  -- Combine the four calls into `asmFirstInitBackStmt F`
  have t34 := runs_seq_iff.mpr (Or.inr ⟨s3, _, _, hcall3, hcall4, rfl⟩)
  have t234 := runs_seq_iff.mpr (Or.inr ⟨s2, _, _, hcall2, t34, rfl⟩)
  have t1234 := runs_seq_iff.mpr (Or.inr ⟨s1, _, _, hcall1, t234, rfl⟩)
  -- Carry `S₀` and the tour across calls 3 and 4
  have hmid3 : ∀ a, h30 ≤ a → a < h31 → st3.mem a = st2.mem a := fun a h1 h2 =>
    hkeep3 a h2 fun hf => by have := hIn.htour_foot a hf; omega
  have hptr4 : st4.mem (h30 + 5) = h30 + 7 :=
    (hkeep4 _ (by omega)).trans ((hmid3 _ (by omega) (by omega)).trans hptr2)
  have hS0_dg4 : DynGraphAt st4.mem (h30 + 7) vCap eCap tr.S_cur :=
    hS0_dg2.of_agree fun a ha1 ha2 =>
      (hkeep4 a (by omega)).trans (hmid3 a (by omega) (by omega))
  have hout_rep4 : (outGraphRep vCap eCap).rep (h30 + 5) tr.S_cur (h30 + 7) st4.mem :=
    ⟨hptr4, Or.inl (by omega), hS0_dg4⟩
  have hout_foot : ∀ a, (outGraphRep vCap eCap).foot (h30 + 5) (h30 + 7) a → h30 ≤ a ∧ a < h31 := by
    intro a ha
    rcases ha with rfl | ⟨h1, h2⟩ <;> omega
  obtain ⟨htour4_rep, htour4_phi⟩ := asmBrTourView_keep tourAsmRep_local ⟨tr, ord, vCap, eCap⟩
    (s := sTour') (tourH := tourH) (tx := xTour') (mem := st3.mem) (mem' := st4.mem)
    fun a ha => (hkeep4 a (by have := hIn.htour_foot a (htour_foot3 a ha); omega)).symm
  have hlo4 : ∀ a < h29, ¬ (tourAsmRep vCap eCap).foot tourH xTour a → st4.mem a = mem a :=
    fun a ha hnf => (hkeep4 a (by omega)).trans (hlo3 a ha hnf)
  have hemb_view : yEmb.view = (⟨fun _ => [], G.E⟩ : EmbView).refresh P S6 slots := hemb_rep4.1
  have hemb_rep4' : (embRep eCap).rep h32 yEmb.view yEmb st4.mem := hemb_view.symm ▸ hemb_rep4
  have hemb_dom4 : (coreGraph tr.cs.G tr.cs.lsf).E ⊆ yEmb.view.dom := hemb_view.symm ▸ hEmbModel.1
  have hemb_eq4 : ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E, yEmb.view.emb e = tr.emb e :=
    hemb_view.symm ▸ hEmbModel.2
  have h33_space : h33 ≤ h29 + asmFiBackSpace P S6 slots vCap eCap tr.S_cur := by
    unfold asmFiBackSpace
    omega
  refine ⟨.normal, s4, _, t1234, h31, h32, h33, sTour', xTour', yEmb, ?_, ?_⟩
  · refine ⟨fun i hi => ?_, by simp [hs4, hs3, hs2, hs1], by simp [hs4, hs3, hs2],
      by simp [hs4, hs3], by simp [hs4], rfl, h31_lo, h31_hi, h32_eq, h33_lo, h33_hi,
      h33_space, hptr4, hS0_dg4, hout_rep4, hout_foot, htour4_rep htour_rep3, htour_marks,
      htour_foot3, hemb_rep4', hemb_dom4, hemb_eq4, hemb_foot4, hlo4, hz4⟩
    have hne : ∀ k, 30 ≤ k → i ≠ k := fun k hk => Nat.ne_of_lt (lt_of_lt_of_le hi hk)
    simp only [hs4, hs3, hs2, hs1, Function.update_apply, hne 30 (by norm_num),
      hne 31 (by norm_num), hne 32 (by norm_num), hne 33 (by norm_num), ite_false]
  · -- Total cost: sum of the four steps plus constant overhead ≤ 100
    have hc1' : c1 ≤ C1 := by rw [hC1, ← hroots_card]; exact hc1
    have hc2' : c2 ≤ C2 := by
      have hQc : Q.cost = 20 := rfl
      have hQp1 : Q.R.phi h29 x4' st2.mem = 0 := rfl
      have hQp0 : Q.R.phi h29 (cmpF, rootOf) st1.mem = 0 := rfl
      rw [hQc, hQp1, hQp0, hroots_card] at hc2
      rw [hC2]
      omega
    have hc3' : c3 + (tourAsmRep vCap eCap).phi tourH xTour' st4.mem ≤ C3 + phi0 := by
      rw [htour4_phi, ← htour2_phi, ← hphi0] at hc3
      rw [hC3]
      omega
    have hc4' : c4 ≤ C4 := hc4
    simp only [argsSize_cons, argsSize_nil, Expr.size_reg, Expr.size_const, Expr.size_bin,
      Expr.size_load, asmFiTourH, hs4]
    clear * - hc1' hc2' hc3' hc4' hT
    omega

/-- **The run of the back from `asmFirstInitBackModule`**, placed at `bBack` inside a program
having `ReadLib`, `readBranchProcs`, `compMapModule`, `HasTourProcs`, `asmFirstExportDynGraphStmt`,
and `bucketSpannerProcs` (as in `scProg`). -/
theorem asmFirstInitBack_runs_of_module {P : DSParams} {slotCap cap : ℕ}
    {tr : BundleTreeState P.L} {ord : ℕ → List End} {G : MGraph}
    {j graph expPtr expEnd L capExp M N vCap eCap h tourH : ℕ}
    {xTour : (tourAsmRep vCap eCap).τ} {slotsPtr spanTbl h29 : ℕ} {slots : List ℕ}
    {slotOf : Finset ℕ × ℤ → ℕ} {S6 : BucketSpannerState cap} {x6 : BucketSpannerMeta P.L cap}
    {st : State} {p : Program} (F : AsmFirstInitProcs) (ω : ℕ → Bool)
    {RL : ReadLib} {fCFRoot bRead bSpan bTour bComp fExp bBack : ℕ}
    (hfR : F.fRootTbl = bBack) (hfS : F.fS0 = bBack + 1)
    (hfM : F.fMark = bBack + 7) (hfE : F.fEmb = bBack + 9)
    (hRL : RL.Has p) (hpRead : p.HasAt bRead (readBranchProcs RL fCFRoot bRead))
    (hpComp : p.HasAt bComp (compMapModule bComp))
    (hpTour : HasTourProcs p bTour)
    (hfExp : p.procs[fExp]? = some asmFirstExportDynGraphStmt)
    (hpSpan : p.HasAt bSpan (bucketSpannerProcs P.impl bSpan))
    (hpBack : p.HasAt bBack (asmFirstInitBackModule RL bRead bSpan bTour bComp fExp bBack))
    (hIn : AsmFiBackIn P slotCap cap tr ord G j graph expPtr expEnd L capExp M N vCap eCap h tourH
      xTour slotsPtr spanTbl h29 slots slotOf S6 x6 st) :
    ∃ h30 h31 h32 h33 sTour' xTour' yEmb st' c,
      Runs P.w p ω (asmFirstInitBackStmt F) st .normal st' c ∧
      AsmFiBackOut P tr ord vCap eCap tourH h29 xTour S6 slots st.mem st.regs
        h30 h31 h32 h33 sTour' xTour' yEmb st' ∧
      c + (tourAsmRep vCap eCap).phi tourH xTour' st'.mem ≤
        rootTblCost tr.cs.lsf.F.F.n tr.cs.lsf.F.F.m tr.cs.lsf.F.R.card +
        (840 * (rebuildSize P S6 slots + slots.length + 1) +
          130 * tr.cs.lsf.F.R.card + 200) +
        (200 * (tr.S_cur.n + tr.S_cur.m + 1) +
          tourMarkExportMul * (tr.S_cur.m + 1) * tourLog eCap + 20) +
        (30 * G.m + embRefreshMul * (embRefreshSizeAt P S6 slots + slots.length + 1) + 80) +
        (tourAsmRep vCap eCap).phi tourH xTour st.mem + 100 := by
  obtain ⟨h0, hS0, h7, h8, h9, h10, h11⟩ := asmFirstInitBackModule_hasAt hpBack
  exact asmFirstInitBack_runs F ω (hfR ▸ h0)
    (initGraphFromExport_meetsContract_of_readBranch hRL hpRead) hpComp
    hRL.1 hRL.2.1 hRL.2.2.2.1 hRL.2.2.2.2.2.2.2 (hfS ▸ hS0) hpTour
    (hfM ▸ h7) hfExp h8 (hfE ▸ h9) h10 h11 hRL.2.2.2.2.2.1 hpSpan hIn

/-- **The model fields of `AsmFiBackIn` at the init state** `initBundleTreeWithParams`: from
`AsmBrModelFacts`, `SlotMapOK`, `BunTableMatches`, and `SpanGraphOK` on the start graphs of the
active pairs, the spanner table `spanAfter (fun _ => none) (asmFirstInitSlotGraph S) slots`
produced by `asmFirstInitSpan_runs` meets `hSE`, `hspanMatch`, and `hGE`. -/
theorem asmFiBack_init_model_facts (P : DSParams) (lsfInit : LSFInit)
    (params : ℕ → SparsifyParams) (spanConst k M N : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ)
    (ord : ℕ → List End) (j : ℕ) {slotCap cap : ℕ} {slots : List ℕ}
    {slotOf : Finset ℕ × ℤ → ℕ} {S : Fin slotCap → Option BundleState}
    (hSB : P.splitBound = bundleSplitBudget k M)
    (hMap : SlotMapOK
      (initBundleTreeWithParams lsfInit P.L (fun _ => canonicalSparsify P.impl) params spanConst
        k M N G₀ ℓ₀ ord j) slotCap cap slots slotOf)
    (hMatch : BunTableMatches
      (initBundleTreeWithParams lsfInit P.L (fun _ => canonicalSparsify P.impl) params spanConst
        k M N G₀ ℓ₀ ord j) slotOf S)
    (hok : ∀ q ∈ activePairs
      (initBundleTreeWithParams lsfInit P.L (fun _ => canonicalSparsify P.impl) params spanConst
        k M N G₀ ℓ₀ ord j),
      SpanGraphOK P
        ((initBundleTreeWithParams lsfInit P.L (fun _ => canonicalSparsify P.impl) params spanConst
          k M N G₀ ℓ₀ ord j).initBunG q)) :
    let tr := initBundleTreeWithParams lsfInit P.L (fun _ => canonicalSparsify P.impl) params
      spanConst k M N G₀ ℓ₀ ord j
    let S6 : BucketSpannerState cap := spanAfter (fun _ => none) (asmFirstInitSlotGraph S) slots
    tr.S_cur.E = (activePairs tr).biUnion (fun q => (tr.dyn q).H.E) ∧
    (∀ q ∈ activePairs tr, ∃ (hs : slotOf q < cap) (d : DSHist),
      S6 ⟨slotOf q, hs⟩ = some d ∧ d.state P = tr.dyn q) ∧
    (∀ q ∈ activePairs tr, (tr.dyn q).G.E = (tr.bun q).edges) := by
  intro tr S6
  refine ⟨?_, ?_, ?_⟩
  · exact (initTree_S_cur_E lsfInit P.L (fun _ => canonicalSparsify P.impl) params spanConst
      k M N G₀ ℓ₀ ord j).trans (activePairs_biUnion_H tr).symm
  · intro q hq
    obtain ⟨hs, d, hd, hst, -⟩ :=
      asmFirstInit_spanMatch P hMap hMatch
        (initTree_initBunG lsfInit P.L (fun _ => canonicalSparsify P.impl) params spanConst
          k M N G₀ ℓ₀ ord j)
        (initTree_dyn P lsfInit params spanConst k M N G₀ ℓ₀ ord j hSB) q hq
    exact ⟨hs, d, hd, hst⟩
  · intro q hq
    exact (initTree_dyn_GE_HE P lsfInit params spanConst k M N G₀ ℓ₀ ord j hSB q (hok q hq)).1

end MinCostFlow.SparseCore.Program
