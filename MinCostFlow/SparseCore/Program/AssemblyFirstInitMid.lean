module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitMidFacts
public import MinCostFlow.SparseCore.Program.TourAsmBridge
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The middle of the build: P5's slots and P6's spanners (`AssemblyFirstInitMid`)

Steps 3 and 4 of the body of the build (`asmFirstInitMidStmt`, `AssemblyFirstInitBody.lean`).
They start from what the front leaves (`AsmFiFrontOut`) and make three calls.
1. **The sorted roots** (`rootsList_runs`): the roots of P4's export, sorted, at the end `sEnd` of
   the slot lists. P5 walks the tour lists of these vertices.
2. **P5** (`asmFirstInitBun_runs`): the empty table and the slots of the active pairs, with the
   specs and the assignments that the slot lists wrote (`slotListOut_specs_read`,
   `slotListOut_assigns_read`). P5 reads the tour through its view
   `tourDS_asmTourCordView_bundleTourAt`, which is P7's view of the front with the core lists as
   the state. P5 may change the tour in its cells and grow it after its table, so the tour is
   carried by its cells, not by an interval.
3. **P6** (`asmFirstInitSpan_runs`): the spanner of each listed slot, on the graph of its bundle,
   with the spanner parameters `asmFiSP` (split bound `bundleSplitBudget k M`, vertex cap
   `2 eCap + splitB + 1`, edge cap `eCap`, edge bound `M`).

`asmFirstInitMid_runs` proves the run and returns `AsmFiMidOut`: the registers `25` to `29`, the
memory below `sEnd` kept outside the old cells of the tour, the sorted roots, P5's table with its
model link (`BunTableMatches`, `SlotMapOK`, `bunRestartInv`), the tour, the spanners, and the
zero memory from the end of P6's part. The table of P5 lies in `[r25, tblEnd)`, the new cells of
the tour in `[tblEnd, r26)`, and the spanners in `[r26, r29)`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-- **What the middle leaves** in the state `st'`, from the state `st` after the front. Here `SP`
are the spanner parameters, `specs` and `assigns` the inputs of P5, `rList` the sorted roots,
`S5` P5's table with meta `m5`, `xTour` the tour and `x6` the meta of the spanners. -/
structure AsmFiMidOut (w : ℕ) {depth : ℕ} (tr : BundleTreeState depth) (ord : ℕ → List End)
    (SP : DSParams) (k vCap eCap : ℕ) (comps : List (Finset ℕ)) (B : ℕ) (D : List ℕ)
    (specs assigns : List (ℕ × ℕ)) (st : State) (tourH o₁ : ℕ) (rList : List ℕ)
    (S5 : Fin eCap → Option BundleState) (m5 : BundleTableMeta eCap) (tblEnd : ℕ)
    (xTour : (tourAsmRep vCap eCap).τ) (x6 : (bucketSpannerRep SP eCap).τ) (st' : State) :
    Prop where
  regs_lo : ∀ i < 25, st'.regs i = st.regs i
  r25 : st'.regs 25 = st.regs 20 + 2 * rList.length
  r27 : st'.regs 27 = SP.splitBound
  r28 : st'.regs 28 = SP.vCap
  keep : ∀ a < st.regs 20, (a < tourH ∨ o₁ ≤ a) → st'.mem a = st.mem a
  roots_sorted : rList.Pairwise (· < ·)
  roots_iff : ∀ v, v ∈ rList ↔ v ∈ tr.cs.lsf.F.R
  roots_at : ListAt st'.mem (st.regs 20) rList
  S5_eq : S5 = tableAfterInitSlots (fun _ => none) specs assigns (outCoreOrder tr ord) rList k
  bun_rep : (bunTableHeadroomRep eCap vCap eCap k).rep (st'.regs 25) S5 m5 st'.mem
  bun_foot : ∀ a, bundleTableFoot eCap (st'.regs 25) m5 a → st'.regs 25 ≤ a ∧ a < tblEnd
  tblEnd_le : tblEnd ≤ st'.regs 26
  bun_inv : bunRestartInv vCap eCap S5 (outCoreOrder tr ord)
  bun_match : BunTableMatches tr (slotOfD comps B D) S5
  slot_map : SlotMapOK tr eCap eCap (List.range D.length) (slotOfD comps B D)
  tour_rep : (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap).rep tourH
    ⟨outCoreOrder tr ord, ∅⟩ xTour st'.mem
  tour_foot : ∀ a, (tourAsmRep vCap eCap).foot tourH xTour a →
    (tourH ≤ a ∧ a < o₁) ∨ (tblEnd ≤ a ∧ a < st'.regs 26)
  span_rep : (bucketSpannerRep SP eCap).rep (st'.regs 26)
    (spanAfter (fun _ => none) (asmFirstInitSlotGraph S5) (List.range D.length)) x6 st'.mem
  span_foot : ∀ a, (bucketSpannerRep SP eCap).foot (st'.regs 26) x6 a →
    st'.regs 26 ≤ a ∧ a < st'.regs 29
  span_ok : ∀ s ∈ List.range D.length, SpanGraphOK SP (asmFirstInitSlotGraph S5 s)
  r29_lo : st'.regs 26 + eCap ≤ st'.regs 29
  r29_hi : st'.regs 29 ≤ st.regs 20 + asmFiMidSpace SP vCap eCap
  zero : ZeroFrom st'.mem (st'.regs 29)
  tbl_lo : st'.regs 25 ≤ tblEnd

set_option maxHeartbeats 4000000 in
/-- **The run of the middle.** From the state after the front (`AsmFiFrontOut`), steps 3 and 4 run
and leave `AsmFiMidOut`. The hypotheses are those of the three calls: the procedures, P4's export,
the model facts of the slots (the buckets, the active pairs, the bundles of the pairs and
`SpanGraphOK` of their start graphs), and the words. The cost of the three calls is in the
amortized form, with the potentials of P5's table, the tour and the spanners. -/
theorem asmFirstInitMid_runs {depth w bT b bSort bSpan bExport fExp capExp M N vCap eCap
    expPtr expEnd h k L P : ℕ} {impl : SparsifyImpl} {p : Program} (F : AsmFirstInitProcs)
    (ω : ℕ → Bool)
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hfR : p.procs[F.fRoots]? = some (rootsListBody bSort))
    (hpT : HasTourProcs p bT)
    (hpB : p.HasAt b (bundleProcs b (tourOp bT 4) (tourOp bT 12) (tourOp bT 10)))
    (hfB : p.procs[F.fBun]? =
      some (asmFirstInitBunBody (b + bundleIdxTableInit) (b + bundleIdxInitSlots)))
    (hfS : p.procs[F.fSpan]? = some (asmFirstInitSpanBody fExp (bSpan + bsIdxOp0 + 0)))
    (hfE : p.procs[fExp]? = some (asmFirstInitExpBody bExport))
    (hpExport : p.HasAt bExport [bundleExportGraphStmt])
    (hpSp : p.HasAt bSpan (bucketSpannerProcs impl bSpan))
    {tr : BundleTreeState depth} {ord : ℕ → List End} {G : MGraph} {ℓ₀ : ℕ → ℝ}
    {mem regs : ℕ → ℕ} {o₁ tourH : ℕ} {xTour : (tourAsmRep vCap eCap).τ} {cmpH ctH sH : ℕ}
    {comps : List (Finset ℕ)} {S D : List ℕ} {memC : ℕ → ℕ} {st : State}
    (hF : AsmFiFrontOut w depth tr ord G ℓ₀ mem regs expPtr k L P vCap eCap h o₁ tourH xTour
      cmpH ctH sH comps S D memC st)
    (r4 : regs 4 = expPtr) (r5 : regs 5 = k) (r6 : regs 6 = M) (r10 : regs 10 = vCap)
    (r11 : regs 11 = eCap) (r12 : regs 12 = depth) (r14 : regs 14 = h)
    (hw10 : 10 ≤ w) (hcsG : tr.cs.G = G) (hGval : G.IsValid) (hRot : HasRotOrder tr ord)
    (hVlt : ∀ v ∈ G.V, v < vCap) (hElt : ∀ e ∈ G.E, e < eCap) (hk1 : 1 ≤ k)
    (hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap tr.cs)
    (hExpLe : expEnd ≤ h)
    (hbktM : ∀ e ∈ G.E, bucketOf (tr.cs.lsf.wstr e * ℓ₀ e) = tr.origBucket e)
    (hcode : ∀ e ∈ G.E,
      bucketCode (tr.origBucket e) < asmFirstInitKeyBase P (mem (expPtr + 6)) L)
    (hact : ∀ q, q ∈ activePairs tr ↔ q.1 ∈ largeComps k G ∧
      ∃ e ∈ G.E, e ∉ tr.cs.lsf.F.F.E ∧ G.tail e ∈ q.1 ∧ tr.origBucket e = q.2)
    (hbun : ∀ q, tr.bun q = initBundleFor tr.cs ord
      (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket q.1 q.2) k)
    (hG : ∀ q, tr.initBunG q = normGraph (tr.bun q).graph)
    (hokM : ∀ q ∈ activePairs tr, SpanGraphOK (asmFiSP impl w M depth k eCap) (tr.initBunG q))
    (hMw : 56 * M + k < 2 ^ w) (hdw : depth < 2 ^ w)
    (hsp : st.regs 20 + asmFiMidSpace (asmFiSP impl w M depth k eCap) vCap eCap < 2 ^ w) :
    ∃ rList S5 m5 tblEnd xT' x6 st' c,
      Runs w p ω (asmFirstInitMidStmt F) st .normal st' c ∧
      AsmFiMidOut w tr ord (asmFiSP impl w M depth k eCap) k vCap eCap comps
        (asmFirstInitKeyBase P (mem (expPtr + 6)) L) D
        (slotSpecsL memC cmpH (o₁ + 16) (asmFirstInitKeyBase P (mem (expPtr + 6)) L) G S D)
        (slotAssignsL memC cmpH (o₁ + 16) (asmFirstInitKeyBase P (mem (expPtr + 6)) L) G S D)
        st tourH o₁ rList S5 m5 tblEnd xT' x6 st' ∧
      c + (bunTableHeadroomRep eCap vCap eCap k).phi (st'.regs 25) m5 st'.mem +
          (tourAsmRep vCap eCap).phi tourH xT' st'.mem +
          specPhi (asmFiSP impl w M depth k eCap)
            (spanAfter (fun _ => none : BucketSpannerState eCap) (asmFirstInitSlotGraph S5)
              (List.range D.length)) ≤
        rootsListCost rList.length +
          bundleInitSlotsCost tourBundleSpec eCap D.length S.length (outCoreOrder tr ord) rList +
          bunPhiMul * (2 * S.length) +
          ((List.range D.length).map fun s => bundleExportCost (slotB S5 s)).sum +
          ((List.range D.length).map fun s =>
            spanActivateCost (asmFiSP impl w M depth k eCap) (asmFirstInitSlotGraph S5 s)).sum +
          200 * D.length + (tourAsmRep vCap eCap).phi tourH xTour st.mem + 600 := by
  set SP := asmFiSP impl w M depth k eCap with hSP
  set B := asmFirstInitKeyBase P (mem (expPtr + 6)) L with hB
  set specs := slotSpecsL memC cmpH (o₁ + 16) B G S D with hspecs
  set assigns := slotAssignsL memC cmpH (o₁ + 16) B G S D with hassigns
  set cord := outCoreOrder tr ord with hcord
  set sEnd := sH + slotListSpace eCap G.m with hsEnd
  set splitB := bundleSplitBudget k M with hsplitB
  have hw16 : 16 ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw10)
  have hw64 : 64 ≤ 2 ^ w := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hw10)
  -- the registers after the front
  have s4 : st.regs 4 = expPtr := (hF.regs_in 4 (by norm_num)).trans r4
  have s5 : st.regs 5 = k := (hF.regs_in 5 (by norm_num)).trans r5
  have s6 : st.regs 6 = M := (hF.regs_in 6 (by norm_num)).trans r6
  have s10 : st.regs 10 = vCap := (hF.regs_in 10 (by norm_num)).trans r10
  have s11 : st.regs 11 = eCap := (hF.regs_in 11 (by norm_num)).trans r11
  have s12 : st.regs 12 = depth := (hF.regs_in 12 (by norm_num)).trans r12
  have s14 : st.regs 14 = h := (hF.regs_in 14 (by norm_num)).trans r14
  have s20 : st.regs 20 = sEnd := hF.r20
  have s21 : st.regs 21 = sH := hF.r21
  have s22 : st.regs 22 = G.m := hF.r22
  have s23 : st.regs 23 = sH + 2 + eCap + 5 * G.m := hF.r23
  have s24 : st.regs 24 = D.length := hF.r24
  -- sizes and layout
  have hm : G.m ≤ eCap := card_le_of_lt_cap hElt
  have hSm : S.length ≤ G.m := hF.slots.S_len
  have hDS : D.length ≤ S.length := hF.slots.D_len
  have hDe : D.length ≤ eCap := by omega
  have hsl : slotListSpace eCap G.m = eCap + 10 * G.m + 3 := rfl
  have hS16 : ASM_BR_SIZE = 16 := rfl
  have hT3 : ASM_BR_TOUR = 3 := rfl
  have htl : h + ASM_BR_SIZE < tourH := hF.tourH_lo
  have hth : tourH < o₁ := hF.tourH_hi
  have hcmpH := hF.cmpH_eq
  have hctH := hF.ctH_eq
  have hsH := hF.sH_eq
  have hspV : SP.vCap = 2 * eCap + splitB + 1 := rfl
  have hspE : SP.eCap = eCap := rfl
  have hspS : SP.splitBound = splitB := rfl
  have hspL : SP.L = depth := rfl
  set Q1 := eCap * (3 + 24 * eCap) with hQ1
  set Q2 := eCap * (6 + 10 * SP.eCap + (4 + SP.vCap + 3 * SP.eCap) + asmFiSpanCapSpace SP)
    with hQ2
  have hspX : sEnd + (5 * vCap + (14 + 7 * eCap + 8 * eCap) + Q1 + 3 * eCap + SP.vCap + Q2) <
      2 ^ w := by rw [← s20]; exact hsp
  have hsb : splitB = 2 * ((56 * M + k - 1) / k) := bundleSplitBudget_eq_div k M hk1
  -- the model
  obtain ⟨C_lsst, ℓ₁, hI, ρ, hρ⟩ := id hRot
  have hRF : tr.cs.lsf.F.IsRootedSpanningForestOf tr.cs.G := compLSF_RF_isRSF hI
  have hRF' : tr.cs.lsf.F.IsRootedSpanningForestOf G := hcsG ▸ hRF
  have hC : CoreCordOf tr.cs ord cord := coreCordOf_outCoreOrder hRot
  have hVcs : ∀ v ∈ tr.cs.G.V, v < vCap := by rw [hcsG]; exact hVlt
  have hEcs : ∀ e ∈ tr.cs.G.E, e < eCap := by rw [hcsG]; exact hElt
  obtain ⟨hcordU, hcordB, hcordN, -⟩ := coreCord_initSlots_facts hC hVcs hEcs
  have hcsm : tr.cs.G.m = G.m := by rw [hcsG]
  -- the roots of P4's export
  have hE8 : expPtr + 8 ≤ h := le_trans hExp.1 hExpLe
  obtain ⟨-, -, -, -, -, -, ⟨roots, hrLen, hrNd, hrFs, hrLA, hrLo, hrHi⟩, -⟩ := id hExp
  set rootsPtr := mem (expPtr + 2) with hrootsPtr
  set nR := mem (expPtr + 3) with hnR
  have hlo : ∀ a < h, st.mem a = mem a := hF.low
  have m2 : st.mem (expPtr + 2) = rootsPtr := hlo _ (by omega)
  have m3 : st.mem (expPtr + 3) = nR := hlo _ (by omega)
  have hrLA0 : ListAt st.mem rootsPtr roots := fun i hi =>
    (hlo _ (by omega)).trans (hrLA i hi)
  have hRV : ∀ v ∈ roots, v ∈ G.V := fun v hv => by
    have h1 : v ∈ tr.cs.lsf.F.R := by rw [← hrFs]; exact List.mem_toFinset.mpr hv
    have h2 := hRF.2.2.1 h1
    rwa [hcsG] at h2
  have hnRv : nR ≤ vCap := by
    rw [← hrLen, ← List.toFinset_card_of_nodup hrNd]
    exact card_le_of_lt_cap fun v hv => hVlt v (hRV v (List.mem_toFinset.mp hv))
  -- step 1: the sorted roots at `sEnd`
  obtain ⟨o1, st1, c1, hr1, ⟨ho1, ⟨rList, hrS, hrM, hrAt⟩, hlo1, hz1⟩, hc1⟩ :=
    rootsList_runs (w := w) hpSort ω (pos := st.pos) (heap := sEnd) hrLen hrNd hrLA0
      (by omega) hF.zero (by omega) hw16 (fun x hx => by have := hVlt x (hRV x hx); omega)
  have hrNd' : rList.Nodup := hrS.imp fun h' => Nat.ne_of_lt h'
  have hnRl : rList.length = nR := (length_eq_of_mem_iff hrNd' hrNd hrM).trans hrLen
  have hrR : ∀ v, v ∈ rList ↔ v ∈ tr.cs.lsf.F.R := fun v => by
    rw [hrM, ← hrFs, List.mem_toFinset]
  have hargs1 : evalArgs w st [.load (.bin .add (.reg 4) (.const 2)),
      .load (.bin .add (.reg 4) (.const 3)), .reg 20] = some [rootsPtr, nR, sEnd] := by
    eval_expr
  obtain ⟨s1, hs1⟩ : ∃ s : State, s = { st1 with regs := Function.update st.regs 25 o1.value } :=
    ⟨_, rfl⟩
  have hcall1 : Runs w p ω (.call 25 F.fRoots [.load (.bin .add (.reg 4) (.const 2)),
      .load (.bin .add (.reg 4) (.const 3)), .reg 20]) st .normal s1
      (argsSize [.load (.bin .add (.reg 4) (.const 2)), .load (.bin .add (.reg 4) (.const 3)),
        .reg 20] + c1 + 1) := by
    rw [hs1]
    exact runs_call_iff.mpr ⟨_, _, o1, st1, c1, hargs1, hfR, hr1, rfl, rfl, rfl⟩
  have u1 : ∀ i, i ≠ 25 → s1.regs i = st.regs i := fun i hi => by
    rw [hs1]; exact Function.update_of_ne hi _ _
  have u1' : s1.regs 25 = sEnd + 2 * nR := by
    rw [hs1, ho1]; simp only [Function.update_self]; rfl
  set mem1 := st1.mem with hmem1
  have hs1m : s1.mem = mem1 := by rw [hs1]
  -- the inputs of P5 in `mem1`
  have l1 : mem1 (sH + 1) = S.length := (hlo1 _ (by omega)).trans hF.slots.nK
  have lT : mem1 (h + ASM_BR_TOUR) = tourH := (hlo1 _ (by omega)).trans hF.rec_tour
  have l3 : mem1 (expPtr + 3) = nR := (hlo1 _ (by omega)).trans m3
  have hspecs1 : bundleReadPairs mem1 (sH + 3 + eCap + 6 * G.m) D.length = specs := by
    rw [bundleReadPairs_congr fun a _ ha => hlo1 a (by omega)]
    exact slotListOut_specs_read hF.slots
  have hassigns1 : bundleReadPairs mem1 (sH + 3 + eCap + 8 * G.m) S.length = assigns := by
    rw [bundleReadPairs_congr fun a _ ha => hlo1 a (by omega)]
    exact slotListOut_assigns_read hF.slots
  -- the model of the slot lists
  have hcmpC : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], memC (cmpH + v) = c := by
    intro c hc v hv
    have hvV : v ∈ G.V := by
      have hCc := (hF.comps_iff _).mp (List.getElem_mem hc)
      obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hCc
      rw [← hu] at hv
      exact (mem_compOf_iff.mp hv).1
    have := hVlt v hvV
    exact (hF.memC_agree _ (by omega)).trans (hF.comps_idx c hc v hv)
  have hbkC : ∀ e ∈ G.E, memC (o₁ + 16 + e) = bucketCode (tr.origBucket e) := by
    intro e he
    have := hElt e he
    rw [hF.memC_agree _ (by omega), hF.bkt_in e he, hbktM e he]
  have hfe : ∀ e ∈ G.E, e ∈ slotForestEdges mem (mem (mem (expPtr + 1) + 3))
      (mem (mem (expPtr + 1) + 2)) ↔ e ∈ tr.cs.lsf.F.F.E := fun e _ => asmFi_fe_iff hExp e
  have H : SlotKeyHyps tr comps G tr.cs.lsf.F.F.E k B G.E.toList :=
    ⟨hGval, hF.comps_nodup, hF.comps_iff, fun e => Finset.mem_toList, hcode, hact⟩
  have hroots := rList_of_roots hC hrFs hrM
  have hcov : ∀ es ∈ assigns, ∀ side : Bool, ∃ v ∈ rList, (es.1, side) ∈ cord v :=
    slotAssignsL_cov H hF.slots hcmpC hfe hcsG hC hroots.2
  have hMatch : BunTableMatches tr (slotOfD comps B D)
      (tableAfterInitSlots (fun _ => none) specs assigns cord rList k :
        Fin eCap → Option BundleState) :=
    bunTableMatches_slotOfD H hF.slots hcmpC hbkC hfe hcsG hRF' hbun hk1 hC hDe hrS hroots.1
      hroots.2
  have hMap : SlotMapOK tr eCap eCap (List.range D.length) (slotOfD comps B D) :=
    slotListOut_slotMapOK H hF.slots hcmpC hbkC hfe hDe hDe
  -- the space of P5
  have hIS : bundleInitSlotsSpace tourBundleSpec specs cord rList ≤
      D.length * (3 + 24 * S.length) + 3 * rList.length + 2 * tr.cs.G.m :=
    asmFi_initSlotsSpace_le hC hrNd'
  have hDQ : D.length * (3 + 24 * S.length) ≤ Q1 := Nat.mul_le_mul hDe (by omega)
  have hfix : bundleTableFixedSize eCap eCap = 14 + 7 * eCap + 8 * eCap := rfl
  -- the tour in `mem1`
  have htour1 := (asmBrTourView_keep (fun vCap eCap => tourAsmRep_local vCap eCap)
    ⟨tr, ord, vCap, eCap⟩ (s := ⟨cord, ∅⟩) (tourH := tourH) (tx := xTour) (mem := st.mem)
    (mem' := mem1) fun a ha => by
      have := hF.tour_foot a ha
      exact (hlo1 a (by omega)).symm).1 hF.tour_rep
  have hargs2 : evalArgs w s1 [.reg 11, .reg 10, .reg 11, .reg 5, asmFiTourH, .reg 24,
      .bin .add (.bin .add (.bin .add (.reg 21) (.const 3)) (.reg 11)) (.bin .mul (.const 6) (.reg 22)),
      .load (.bin .add (.reg 21) (.const 1)),
      .bin .add (.bin .add (.bin .add (.reg 21) (.const 3)) (.reg 11)) (.bin .mul (.const 8) (.reg 22)),
      .load (.bin .add (.reg 4) (.const 3)), .reg 20, .reg 25] =
      some [eCap, vCap, eCap, k, tourH, D.length, sH + 3 + eCap + 6 * G.m, S.length,
        sH + 3 + eCap + 8 * G.m, nR, sEnd, sEnd + 2 * nR] := by
    have t4 : s1.regs 4 = expPtr := (u1 4 (by norm_num)).trans s4
    have t5 : s1.regs 5 = k := (u1 5 (by norm_num)).trans s5
    have t10 : s1.regs 10 = vCap := (u1 10 (by norm_num)).trans s10
    have t11 : s1.regs 11 = eCap := (u1 11 (by norm_num)).trans s11
    have t14 : s1.regs 14 = h := (u1 14 (by norm_num)).trans s14
    have t20 : s1.regs 20 = sEnd := (u1 20 (by norm_num)).trans s20
    have t21 : s1.regs 21 = sH := (u1 21 (by norm_num)).trans s21
    have t22 : s1.regs 22 = G.m := (u1 22 (by norm_num)).trans s22
    have t24 : s1.regs 24 = D.length := (u1 24 (by norm_num)).trans s24
    have v1 : s1.mem (sH + 1) = S.length := by rw [hs1m]; exact l1
    have vT : s1.mem (h + ASM_BR_TOUR) = tourH := by rw [hs1m]; exact lT
    have v3 : s1.mem (expPtr + 3) = nR := by rw [hs1m]; exact l3
    have cT : ASM_BR_TOUR < 2 ^ w := by omega
    have cT' : h + ASM_BR_TOUR < 2 ^ w := by omega
    eval_expr
  -- step 2: P5
  obtain ⟨body2, hb2, st2, c2, hEnd, tx', hr2, hEndLo, hEndHi, hz2, hrep2, hinv2, htr2, hfootB2,
      hfootT2, hfr2, hc2⟩ :=
    asmFirstInitBun_runs (TS := tourBundleSpec) (slotCap := eCap) (vCap := vCap) (eCap := eCap)
      (k := k) (tourH := tourH) (nSlots := D.length) (specPtr := sH + 3 + eCap + 6 * G.m)
      (nEdges := S.length) (asgPtr := sH + 3 + eCap + 8 * G.m) (nR := nR) (rPtr := sEnd)
      (heap := sEnd + 2 * nR) (mem := mem1) (pos := s1.pos) (tx₀ := xTour) (ω := ω)
      (specs := specs) (assigns := assigns) (cord := cord) (rList := rList)
      hpB (tourDS_asmTourCordView_bundleTourAt w vCap eCap p bT hpT ord tr.cs.lsf.F cord ∅) hfB
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          omega)
      hw16 hk1 (by omega) (by omega) (by omega) (by omega) hz1 htour1
      (fun a ha => by have := hF.tour_foot a ha; omega)
      (fun a ha => by have := hF.tour_foot a ha; omega)
      (fun a ha => by have := hF.tour_foot a ha; omega)
      hcordU hcordB slotSpecsL_length hspecs1 (slotSpecsL_lt hDe) slotSpecsL_nodup
      slotSpecsL_cap4 slotAssignsL_length hassigns1 (slotListOut_assigns_in hF.slots hElt)
      (slotListOut_assigns_nodup hF.slots) hnRl hrAt
      (fun v hv => by
        have h1 := hVlt v (hRV v ((hrM v).mp hv))
        exact ⟨h1, by omega⟩)
      hrNd' (fun v _ => hcordN v) hcov
  set S5 : Fin eCap → Option BundleState :=
    tableAfterInitSlots (fun _ => none) specs assigns cord rList k with hS5
  set m5 : BundleTableMeta eCap := allocSlotBlocksMeta (⟨fun _ => none⟩ : BundleTableMeta eCap)
    specs (sEnd + 2 * nR + bundleTableFixedSize eCap eCap) with hm5
  set tblEnd := sEnd + 2 * nR + bundleTableFixedSize eCap eCap + slotBlocksSpace specs
    with htblEnd
  have hnotT : ∀ a, (a < tourH ∨ o₁ ≤ a) → ¬ (tourAsmRep vCap eCap).foot tourH xTour a :=
    fun a ha hf => by have := hF.tour_foot a hf; omega
  obtain ⟨s2, hs2⟩ : ∃ s : State, s = { st2 with regs := Function.update s1.regs 26 hEnd } :=
    ⟨_, rfl⟩
  have hr2' : Runs w p ω body2 (startState [eCap, vCap, eCap, k, tourH, D.length,
      sH + 3 + eCap + 6 * G.m, S.length, sH + 3 + eCap + 8 * G.m, nR, sEnd, sEnd + 2 * nR]
      s1.mem s1.pos) (.returned hEnd) st2 c2 := by rw [hs1m]; exact hr2
  have hcall2 := (runs_call_iff (r := 26) (st' := s2)).mpr
    ⟨_, body2, .returned hEnd, st2, c2, hargs2, hb2, hr2', rfl, hs2, rfl⟩
  have u2 : ∀ i, i ≠ 26 → s2.regs i = s1.regs i := fun i hi => by
    rw [hs2]; exact Function.update_of_ne hi _ _
  have hs2m : s2.mem = st2.mem := by rw [hs2]
  -- step 3: the split bound and the vertex cap of the spanners
  obtain ⟨s3, hs3⟩ : ∃ s : State, s = { s2 with regs := Function.update s2.regs 27 splitB } :=
    ⟨_, rfl⟩
  have he27 : (Expr.bin .mul (.const 2) (.bin .div
      (.bin .sub (.bin .add (.bin .mul (.const 56) (.reg 6)) (.reg 5)) (.const 1))
      (.reg 5))).eval w s2 = some splitB := by
    have t5 : s2.regs 5 = k := ((u2 5 (by norm_num)).trans (u1 5 (by norm_num))).trans s5
    have t6 : s2.regs 6 = M := ((u2 6 (by norm_num)).trans (u1 6 (by norm_num))).trans s6
    have hdivw : 2 * ((56 * M + k - 1) / k) < 2 ^ w := by rw [← hsb]; omega
    exact Expr.eval_eq_of_eq (by eval_expr) hsb.symm
  have hasg27 := (runs_assign_iff (w := w) (p := p) (ω := ω) (r := 27) (st' := s3)).mpr ⟨splitB, he27, rfl, hs3, rfl⟩
  have u3 : ∀ i, i ≠ 27 → s3.regs i = s2.regs i := fun i hi => by
    rw [hs3]; exact Function.update_of_ne hi _ _
  obtain ⟨s4, hs4⟩ : ∃ s : State, s = { s3 with regs := Function.update s3.regs 28 SP.vCap } :=
    ⟨_, rfl⟩
  have he28 : (Expr.bin .add (.bin .add (.bin .mul (.const 2) (.reg 11)) (.reg 27))
      (.const 1)).eval w s3 = some SP.vCap := by
    have t11 : s3.regs 11 = eCap := (((u3 11 (by norm_num)).trans (u2 11 (by norm_num))).trans
      (u1 11 (by norm_num))).trans s11
    have t27 : s3.regs 27 = splitB := by rw [hs3]; simp only [Function.update_self]
    exact Expr.eval_eq_of_eq (by eval_expr) hspV.symm
  have hasg28 := (runs_assign_iff (w := w) (p := p) (ω := ω) (r := 28) (st' := s4)).mpr ⟨SP.vCap, he28, rfl, hs4, rfl⟩
  have u4 : ∀ i, i ≠ 28 → s4.regs i = s3.regs i := fun i hi => by
    rw [hs4]; exact Function.update_of_ne hi _ _
  have hs4m : s4.mem = st2.mem := by rw [hs4, hs3, hs2m]
  have v0 : ∀ i, i < 25 → s4.regs i = st.regs i := fun i hi =>
    (((u4 i (by omega)).trans (u3 i (by omega))).trans (u2 i (by omega))).trans (u1 i (by omega))
  -- step 4: P6
  have hok5 : ∀ s ∈ List.range D.length, SpanGraphOK SP (asmFirstInitSlotGraph S5 s) :=
    asmFi_slotGraphOK SP hMap hMatch hG hokM
  have hE2 := asmFi_edgeTot_le SP hok5
  have hX2 := asmFi_exportSpace_le SP hok5
  have hA2 := asmFi_activateSpace_le SP hok5
  rw [List.length_range] at hE2 hX2 hA2
  have hQ2' : 6 * D.length + 10 * (D.length * SP.eCap) + D.length * (4 + SP.vCap + 3 * SP.eCap) +
      D.length * asmFiSpanCapSpace SP ≤ Q2 := by
    calc _ = D.length * (6 + 10 * SP.eCap + (4 + SP.vCap + 3 * SP.eCap) + asmFiSpanCapSpace SP) :=
          by ring
      _ ≤ Q2 := Nat.mul_le_mul_right _ hDe
  have hlist2 : ListAt st2.mem (sH + 2 + eCap + 5 * G.m) (List.range D.length) := by
    intro i hi
    rw [List.length_range] at hi
    rw [List.getElem_range, hfr2 _ (by omega) (hnotT _ (Or.inr (by omega))), hlo1 _ (by omega)]
    exact hF.slots.slots i hi
  have hSPw : SP.w = w := rfl
  obtain ⟨o5, st5, c5, x6, hr5, hrep5, hfoot5, hfr5, hlo5, hhi5, hz5, hc5⟩ :=
    asmFirstInitSpan_runs (P := SP) (cap := eCap) (ω := ω) hfE hpExport hpSp
      (slotCap := eCap) (vCap := vCap) (eCap := eCap) (bunTbl := sEnd + 2 * nR) (tourH := tourH)
      (spanTbl := hEnd) (x3 := 0) (slotsPtr := sH + 2 + eCap + 5 * G.m) (h := hEnd + eCap)
      (x7 := 0) (x8 := 0) (pos := s4.pos) (slots := List.range D.length) (S := S5) (m := m5)
      (mem := st2.mem)
      hw16 hdw (by rw [hSPw]; omega) (by rw [hSPw]; omega) (by rw [hSPw]; omega) hrep2.1
      (fun a ha => by have := hfootB2 a ha; omega)
      (tableAfterInitSlots_some_range assigns cord rList k hDe)
      hlist2 (by rw [List.length_range]; omega) (fun a ha => hz2 a (by omega))
      (by rw [hSPw]; omega) hok5 (fun s hs => by have := List.mem_range.mp hs; omega) le_rfl
      (fun j hj => hz2 _ (by omega))
      (fun a h1 h2 h3 => by rw [List.length_range] at h3; omega)
      (by rw [hSPw, List.length_range]; omega)
  rw [List.length_range] at hr5 hhi5 hc5
  have hT2 : st2.mem (h + ASM_BR_TOUR) = tourH := by
    rw [hfr2 _ (by omega) (hnotT _ (Or.inl (by omega)))]; exact lT
  have hargs5 : evalArgs w s4 [.reg 25, asmFiTourH, .reg 26, .const 0, .reg 24, .reg 23,
      .bin .add (.reg 26) (.reg 11), .const 0, .const 0, .reg 27, .reg 28, .reg 11, .reg 12] =
      some [sEnd + 2 * nR, tourH, hEnd, 0, D.length, sH + 2 + eCap + 5 * G.m, hEnd + eCap, 0, 0,
        SP.splitBound, SP.vCap, SP.eCap, SP.L] := by
    have t11 : s4.regs 11 = eCap := (v0 11 (by norm_num)).trans s11
    have t12 : s4.regs 12 = SP.L := (v0 12 (by norm_num)).trans s12
    have t14 : s4.regs 14 = h := (v0 14 (by norm_num)).trans s14
    have t23 : s4.regs 23 = sH + 2 + eCap + 5 * G.m := (v0 23 (by norm_num)).trans s23
    have t24 : s4.regs 24 = D.length := (v0 24 (by norm_num)).trans s24
    have t25 : s4.regs 25 = sEnd + 2 * nR := by
      rw [u4 25 (by norm_num), u3 25 (by norm_num), u2 25 (by norm_num)]; exact u1'
    have t26 : s4.regs 26 = hEnd := by
      rw [u4 26 (by norm_num), u3 26 (by norm_num), hs2]; simp only [Function.update_self]
    have t27s : s4.regs 27 = splitB := by
      rw [u4 27 (by norm_num), hs3]; simp only [Function.update_self]
    have t27 : s4.regs 27 = SP.splitBound := t27s
    have t28 : s4.regs 28 = SP.vCap := by rw [hs4]; simp only [Function.update_self]
    have vT : s4.mem (h + ASM_BR_TOUR) = tourH := by rw [hs4m]; exact hT2
    have cT : ASM_BR_TOUR < 2 ^ w := by omega
    have cT' : h + ASM_BR_TOUR < 2 ^ w := by omega
    eval_expr
  obtain ⟨s5, hs5⟩ : ∃ s : State, s = { st5 with regs := Function.update s4.regs 29 o5.value } :=
    ⟨_, rfl⟩
  have hr5' : Runs w p ω (asmFirstInitSpanBody fExp (bSpan + bsIdxOp0 + 0))
      (startState [sEnd + 2 * nR, tourH, hEnd, 0, D.length, sH + 2 + eCap + 5 * G.m, hEnd + eCap,
        0, 0, SP.splitBound, SP.vCap, SP.eCap, SP.L] s4.mem s4.pos) o5 st5 c5 := by
    rw [hs4m]; exact hr5
  have hcall5 := (runs_call_iff (r := 29) (st' := s5)).mpr
    ⟨_, _, o5, st5, c5, hargs5, hfS, hr5', rfl, hs5, rfl⟩
  have hrun := runs_seq_iff.mpr (Or.inr ⟨s1, _, _, hcall1, runs_seq_iff.mpr (Or.inr ⟨s2, _, _,
    hcall2, runs_seq_iff.mpr (Or.inr ⟨s3, _, _, hasg27, runs_seq_iff.mpr (Or.inr ⟨s4, _, _,
      hasg28, hcall5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- the state at the end
  have hs5m : s5.mem = st5.mem := by rw [hs5]
  have e29 : s5.regs 29 = o5.value := by rw [hs5]; simp only [Function.update_self]
  have u5 : ∀ i, i ≠ 29 → s5.regs i = s4.regs i := fun i hi => by
    rw [hs5]; exact Function.update_of_ne hi _ _
  have e25 : s5.regs 25 = sEnd + 2 * nR := by
    rw [u5 25 (by norm_num), u4 25 (by norm_num), u3 25 (by norm_num), u2 25 (by norm_num)]
    exact u1'
  have e26 : s5.regs 26 = hEnd := by
    rw [u5 26 (by norm_num), u4 26 (by norm_num), u3 26 (by norm_num), hs2]
    simp only [Function.update_self]
  have e27 : s5.regs 27 = splitB := by
    rw [u5 27 (by norm_num), u4 27 (by norm_num), hs3]; simp only [Function.update_self]
  have e28 : s5.regs 28 = SP.vCap := by
    rw [u5 28 (by norm_num), hs4]; simp only [Function.update_self]
  have hag2 : ∀ a < hEnd, s5.mem a = st2.mem a := fun a ha => by
    rw [hs5m]; exact hfr5 a (by omega) (by omega)
  have hlocB := bunTableHeadroomRep_local eCap vCap eCap k (sEnd + 2 * nR) S5 m5 st2.mem s5.mem
    fun a ha => by have := hfootB2 a ha; exact (hag2 a (by omega)).symm
  have hlocT := asmBrTourView_keep (fun vCap eCap => tourAsmRep_local vCap eCap)
    ⟨tr, ord, vCap, eCap⟩ (s := ⟨cord, ∅⟩) (tourH := tourH) (tx := tx') (mem := st2.mem)
    (mem' := s5.mem) fun a ha => by
      rcases hfootT2 a ha with h0 | ⟨_, h1⟩
      · have := hF.tour_foot a h0
        exact (hag2 a (by omega)).symm
      · exact (hag2 a h1).symm
  have hphiT1 := (asmBrTourView_keep (fun vCap eCap => tourAsmRep_local vCap eCap)
    ⟨tr, ord, vCap, eCap⟩ (s := ⟨cord, ∅⟩) (tourH := tourH) (tx := xTour) (mem := st.mem)
    (mem' := mem1) fun a ha => by
      have := hF.tour_foot a ha
      exact (hlo1 a (by omega)).symm).2
  have hmidEq : asmFiMidSpace SP vCap eCap =
      5 * vCap + (14 + 7 * eCap + 8 * eCap) + Q1 + 3 * eCap + SP.vCap + Q2 := rfl
  refine ⟨rList, S5, m5, tblEnd, tx', x6, s5, _, hrun, ⟨?_, ?_, ?_, ?_, ?_, hrS, hrR, ?_, rfl, ?_,
    ?_, ?_, hinv2, hMatch, hMap, ?_, ?_, ?_, ?_, hok5, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [u5 i (by omega)]; exact v0 i hi
  · rw [e25, s20, hnRl]
  · exact e27
  · exact e28
  · intro a ha hT
    rw [s20] at ha
    rw [hag2 a (by omega), hfr2 a (by omega) (hnotT a hT), hlo1 a ha]
  · intro i hi
    rw [s20, hag2 _ (by omega), hfr2 _ (by omega) (hnotT _ (Or.inr (by omega)))]
    exact hrAt i hi
  · rw [e25]; exact hlocB.1 hrep2
  · rw [e25]; exact fun a ha => hfootB2 a ha
  · rw [e26]; exact hEndLo
  · exact hlocT.1 htr2
  · intro a ha
    rw [e26]
    rcases hfootT2 a ha with h0 | h1
    · exact Or.inl (hF.tour_foot a h0)
    · exact Or.inr h1
  · rw [e26, hs5m]; exact hrep5
  · intro a ha
    rw [e26, e29]
    rw [e26] at ha
    rcases hfoot5 a ha with h0 | h1 <;> omega
  · rw [e26, e29]; exact hlo5
  · rw [e29, s20, hmidEq]
    omega
  · rw [e29, hs5m]; exact hz5
  · rw [e25, htblEnd]; omega
  · rw [e25, hnRl, ← hlocB.2, ← hlocT.2]
    have hc2' : c2 + (bunTableHeadroomRep eCap vCap eCap k).phi (sEnd + 2 * nR) m5 st2.mem +
        (tourAsmRep vCap eCap).phi tourH tx' st2.mem ≤
        bundleInitSlotsCost tourBundleSpec eCap D.length S.length cord rList +
          bunPhiMul * (2 * S.length) + (tourAsmRep vCap eCap).phi tourH xTour mem1 + 220 := hc2
    simp only [argsSize_cons, argsSize_nil, Expr.size_reg, Expr.size_const, Expr.size_bin,
      Expr.size_load, asmFiTourH]
    omega

end MinCostFlow.SparseCore.Program
