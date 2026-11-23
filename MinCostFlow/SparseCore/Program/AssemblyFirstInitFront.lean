module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBody
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBktTable
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitRootTbl
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlotRun
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The front of the build: the tour and the maps (`AssemblyFirstInitFront`)

Steps 1 and 2 of the body of the build (`asmFirstInitFrontStmt`, `AssemblyFirstInitBody.lean`):
the record words and the tour, the bucket table at `bktH = o₁ + 16` (after the record of the bundle
side at the end `o₁` of the tour), the map to the components, and the slot lists. Each step reads
only cells below its own heap pointer and writes only from it, so the facts of the earlier steps
stay true: `asmFirstInitFront_runs` carries them to the end of step 2, in `AsmFiFrontOut`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-- A statement that ends normally, then a statement in the forward form. -/
theorem runs_seq_runs_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt} {st st₁ : State}
    {c₁ k T : ℕ} {Q : Outcome → State → Prop} (h₁ : Runs w p ω s st .normal st₁ c₁)
    (hrest : ∃ o st' c, Runs w p ω t st₁ o st' c ∧ Q o st' ∧ (k + c₁ + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (s ;; t) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c, hr, hq, hc⟩ := hrest
  exact ⟨o, st', c₁ + c + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c, h₁, hr, rfl⟩), hq, by omega⟩

/-- The words of the front: the tour (with the record of the branch before it), the record of
the bundle side, the bucket table and its scratch, the map to the components and its scratch, the
table of the components, the slot lists, and the room that the slot lists ask for. -/
def asmFiFrontSpace (vCap eCap Lw L : ℕ) : ℕ :=
  16 + tourBranchInitSpace vCap eCap + 16 + eCap + eCap * bucketWordSpace Lw L + vCap +
    (5 * vCap + 6 * eCap + 3) + 3 * vCap + slotListSpace eCap eCap + 4 * eCap + 4

/-- **What the front leaves** at the end of step 2, in the state `st'`, from the start memory
`mem`. The tour ends at `o₁`; the bucket table is at `o₁ + 16`; the map to the components at
`cmpH`; the table of the components at `ctH`; the slot lists at `sH`. The memory `memC` is the one
before the slot lists. -/
structure AsmFiFrontOut (w depth : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
    (G : MGraph) (ℓ₀ : ℕ → ℝ) (mem : ℕ → ℕ) (regs : ℕ → ℕ)
    (expPtr k L P vCap eCap h : ℕ) (o₁ tourH : ℕ) (xTour : (tourAsmRep vCap eCap).τ)
    (cmpH ctH sH : ℕ) (comps : List (Finset ℕ)) (S D : List ℕ) (memC : ℕ → ℕ) (st' : State) :
    Prop where
  regs_in : ∀ i < 15, st'.regs i = regs i
  r15 : st'.regs 15 = o₁
  r16 : st'.regs 16 = cmpH
  r17 : st'.regs 17 = comps.length
  r18 : st'.regs 18 = ctH
  r19 : st'.regs 19 = asmFirstInitKeyBase P (mem (expPtr + 6)) L
  r20 : st'.regs 20 = sH + slotListSpace eCap G.m
  r21 : st'.regs 21 = sH
  r22 : st'.regs 22 = G.m
  r23 : st'.regs 23 = sH + 2 + eCap + 5 * G.m
  r24 : st'.regs 24 = D.length
  cmpH_eq : cmpH = o₁ + 16 + eCap + G.m * bucketWordSpace (mem (expPtr + 6)) L
  ctH_eq : ctH = cmpH + vCap + (5 * vCap + 6 * eCap + 3)
  sH_eq : sH = ctH + 3 * comps.length
  low : ∀ a < h, st'.mem a = mem a
  rec_tour : st'.mem (h + ASM_BR_TOUR) = tourH
  rec_vCap : st'.mem (h + ASM_BR_VCAP) = vCap
  rec_eCap : st'.mem (h + ASM_BR_ECAP) = eCap
  rec_tCap : st'.mem (h + ASM_BR_TCAP) = mem (expPtr + 7)
  rec_Lw : st'.mem (h + ASM_BR_LW) = mem (expPtr + 6)
  tourH_lo : h + ASM_BR_SIZE < tourH
  tourH_hi : tourH < o₁
  tour_rep : (asmBrTourView tourAsmRep ⟨tr, ord, vCap, eCap⟩ vCap eCap).rep tourH
    ⟨outCoreOrder tr ord, ∅⟩ xTour st'.mem
  tour_foot : ∀ a, (tourAsmRep vCap eCap).foot tourH xTour a → tourH ≤ a ∧ a < o₁
  o₁_le : o₁ + 2 ≤ h + ASM_BR_SIZE + tourBranchInitSpace vCap eCap
  sd_zero : ∀ a, o₁ ≤ a → a < o₁ + 16 → st'.mem a = 0
  bkt_in : ∀ e ∈ G.E, st'.mem (o₁ + 16 + e) = bucketCode (bucketOf (tr.cs.lsf.wstr e * ℓ₀ e))
  bkt_out : ∀ e < eCap, e ∉ G.E → st'.mem (o₁ + 16 + e) = 0
  bkt_word : ∀ e < eCap, st'.mem (o₁ + 16 + e) < 2 ^ w
  comps_nodup : comps.Nodup
  comps_iff : ∀ C, C ∈ comps ↔ C ∈ components G
  comps_idx : ∀ c (hc : c < comps.length), ∀ v ∈ comps[c], st'.mem (cmpH + v) = c
  comps_word : ∀ v < vCap, st'.mem (cmpH + v) < 2 ^ w
  slots : SlotListOut memC st'.mem G
    (slotForestEdges mem (mem (mem (expPtr + 1) + 3)) (mem (mem (expPtr + 1) + 2)))
    cmpH (o₁ + 16) comps.length k (asmFirstInitKeyBase P (mem (expPtr + 6)) L) ctH sH eCap S D
  memC_agree : ∀ a < ctH, memC a = st'.mem a
  zero : ZeroFrom st'.mem (sH + slotListSpace eCap G.m)
  r20_le : sH + slotListSpace eCap G.m ≤ h + asmFiFrontSpace vCap eCap (mem (expPtr + 6)) L

/-- **The forest edges of P4's export**, for the slot lists: the triples of the forest lie below
the end of the export, and their first words are edges of `cs.G` when the forest is a subgraph of
`cs.G`. These are the hypotheses `hfDle`, `hfe` and `hfeL` of `asmFirstInitFront_runs`. -/
theorem asmFi_forestEdges_of_export {w : ℕ} {mem : ℕ → ℕ}
    {expPtr expEnd L capExp M N vCap eCap h : ℕ} {cs : CompLSFState}
    (hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap cs)
    (hExpLe : expEnd ≤ h) (hsub : ∀ e ∈ cs.lsf.F.F.E, e ∈ cs.G.E) :
    mem (expPtr + 1) + 4 ≤ h ∧
    (∀ e ∈ slotForestEdges mem (mem (mem (expPtr + 1) + 3)) (mem (mem (expPtr + 1) + 2)),
      e ∈ cs.G.E) ∧
    mem (mem (expPtr + 1) + 3) + 3 * mem (mem (expPtr + 1) + 2) ≤ h := by
  obtain ⟨-, -, -, -, -, hfEx, -⟩ := hExp
  obtain ⟨-, -, -, -, -, hT, -, hd4, -, -, -, hEend⟩ := hfEx
  refine ⟨by omega, fun e he => ?_, by omega⟩
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  exact hsub _ (hT (mem (mem (mem (expPtr + 1) + 3) + 3 * t),
    mem (mem (mem (expPtr + 1) + 3) + 3 * t + 1), mem (mem (mem (expPtr + 1) + 3) + 3 * t + 2))
    (List.mem_map.mpr ⟨t, ht, rfl⟩)).1

/-- **The bucket codes lie below the key base**: the code of the bucket of `wstr e · ℓ₀ e` is at
most `2 (8 L_w + 4 L + P + 1)` (`bucketCode_blocks_le`, on the blocks of `wstr e` in P4's export
and of `ℓ₀ e` in the lengths), which is below `asmFirstInitKeyBase P L_w L`. This is the
hypothesis `hcode` of `asmFirstInitFront_runs`. -/
theorem asmFi_code_lt {w : ℕ} {mem : ℕ → ℕ}
    {expPtr expEnd L capExp M N vCap eCap lengths P h : ℕ} {cs : CompLSFState} {G : MGraph}
    {ℓ₀ : ℕ → ℝ} (hExp : CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap cs)
    (hcsG : cs.G = G) (hlen : BranchLengthsAt mem lengths eCap L P h G ℓ₀) :
    ∀ e ∈ G.E, bucketCode (bucketOf (cs.lsf.wstr e * ℓ₀ e)) <
      asmFirstInitKeyBase P (mem (expPtr + 6)) L := by
  intro e he
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, num, den, hnd⟩ := hExp
  obtain ⟨-, -, -, -, hvn, hvd, hn, hd, hd0, hw⟩ := hnd e (hcsG ▸ he)
  obtain ⟨-, hAt, hℓ⟩ := hlen
  obtain ⟨-, hvl, hpos⟩ := hAt e he
  have hℓe : ℓ₀ e = Num.fixVal mem (lengths + e * L) 4 L P := by
    rw [hℓ]; simp [MinRatio.readEdgeValues, he]
  have hl0 : 0 < Num.intVal mem (lengths + e * L) 4 L := by
    have h1 : (0 : ℝ) < Num.fixVal mem (lengths + e * L) 4 L P := by
      simpa [MinRatio.readEdgeValues, he] using hpos
    unfold Num.fixVal at h1
    have h2 : (0 : ℝ) < (Num.intVal mem (lengths + e * L) 4 L : ℝ) :=
      (div_pos_iff_of_pos_right (by positivity)).mp h1
    exact_mod_cast h2
  have hle := bucketCode_blocks_le (P := P) hvn hvd hvl (by rw [hd]; exact hd0) hl0
  rw [hn, hd, hw, ← hℓe] at hle
  unfold asmFirstInitKeyBase
  omega

set_option maxHeartbeats 1000000 in
/-- **The run of the front.** From a state whose registers hold the arguments of the build, steps
1 and 2 run and leave `AsmFiFrontOut`. The hypotheses are those of the four steps, on the start
memory: the order and P4's export for the tour, the graph and the lengths for the bucket table,
the forest edges of P4's export for the slot lists, and a bound `B` on the bucket codes. -/
theorem asmFirstInitFront_runs {depth w bT capExp M N vCap eCap cOrdPtr expPtr expEnd h cWords
    graph lengths L P k : ℕ} {p : Program} (F : AsmFirstInitProcs) (ω : ℕ → Bool)
    (hpT : HasTourProcs p bT) (hfT : p.procs[F.fTour]? = some (tourBranchInitStmt (tourInit bT)))
    (hw10 : 10 ≤ w) (hpB : p.HasAt F.fBkt (bucketTableModule F.fBkt))
    (hpC : p.HasAt F.fComp (compMapModule F.fComp)) (hpS : p.HasAt F.fSlot (slotListModule F.fSlot))
    {tr : BundleTreeState depth} {ord : ℕ → List End} {G : MGraph} {ℓ₀ : ℕ → ℝ} {st : State}
    (r2 : st.regs 2 = graph) (r3 : st.regs 3 = cOrdPtr) (r4 : st.regs 4 = expPtr)
    (r5 : st.regs 5 = k) (r8 : st.regs 8 = L) (r9 : st.regs 9 = P) (r10 : st.regs 10 = vCap)
    (r11 : st.regs 11 = eCap) (r13 : st.regs 13 = lengths) (r14 : st.regs 14 = h)
    (hcsG : tr.cs.G = G) (hGval : G.IsValid) (hRot : HasRotOrder tr ord)
    (hVlt : ∀ v ∈ G.V, v < vCap) (hElt : ∀ e ∈ G.E, e < eCap)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (hOrdAt : OrdListAt st.mem cOrdPtr ord cWords) (hOrdLe : cOrdPtr + cWords ≤ h)
    (hExp : CompBranchExportAt w st.mem expPtr expEnd L capExp M N vCap eCap tr.cs)
    (hExpLe : expEnd ≤ h)
    (hG : DynGraphAt st.mem graph vCap eCap G) (hGle : graph + dynGraphSize vCap eCap ≤ h)
    (hlen : BranchLengthsAt st.mem lengths eCap L P h G ℓ₀)
    (hfDle : st.mem (expPtr + 1) + 4 ≤ h)
    (hfe : ∀ e ∈ slotForestEdges st.mem (st.mem (st.mem (expPtr + 1) + 3))
      (st.mem (st.mem (expPtr + 1) + 2)), e ∈ G.E)
    (hfeL : st.mem (st.mem (expPtr + 1) + 3) + 3 * st.mem (st.mem (expPtr + 1) + 2) ≤ h)
    (hcode : ∀ e ∈ G.E, bucketCode (bucketOf (tr.cs.lsf.wstr e * ℓ₀ e)) <
      asmFirstInitKeyBase P (st.mem (expPtr + 6)) L)
    (hz : ZeroFrom st.mem h)
    (hsp : h + asmFiFrontSpace vCap eCap (st.mem (expPtr + 6)) L < 2 ^ w)
    (hBw : asmFirstInitKeyBase P (st.mem (expPtr + 6)) L < 2 ^ w)
    (hkw : vCap * asmFirstInitKeyBase P (st.mem (expPtr + 6)) L < 2 ^ w) :
    ∃ o₁ tourH xTour cmpH ctH sH comps S D memC st' c,
      Runs w p ω (asmFirstInitFrontStmt F) st .normal st' c ∧
      AsmFiFrontOut w depth tr ord G ℓ₀ st.mem st.regs expPtr k L P vCap eCap h o₁ tourH xTour
        cmpH ctH sH comps S D memC st' ∧
      c + (tourAsmRep vCap eCap).phi tourH xTour st'.mem ≤
        tourBranchInitMul * (1 + cWords + G.m + G.n) * tourLog eCap + 60 +
        bucketTableCost (st.mem (expPtr + 6)) L G.m + compMapCost G.n G.m +
        slotListCost G.m (components G).card (st.mem (st.mem (expPtr + 1) + 2)) + 200 := by
  set mem := st.mem with hmem
  set Lw := mem (expPtr + 6) with hLw
  set B := asmFirstInitKeyBase P Lw L with hB
  have hE8 : expPtr + 8 ≤ h := le_trans hExp.1 hExpLe
  have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hm : G.m ≤ eCap := card_le_of_lt_cap hElt
  have hn : G.n ≤ vCap := card_le_of_lt_cap hVlt
  have hmb : G.m * bucketWordSpace Lw L ≤ eCap * bucketWordSpace Lw L :=
    Nat.mul_le_mul_right _ hm
  have hsp' : h + (16 + tourBranchInitSpace vCap eCap + 16 + eCap + eCap * bucketWordSpace Lw L +
      vCap + (5 * vCap + 6 * eCap + 3) + 3 * vCap + (eCap + 10 * eCap + 3) + 4 * eCap + 4) <
      2 ^ w := hsp
  -- step 1: the record words and the tour
  obtain ⟨o₁, st1, c1, tourH, xT, hrun1, hregs1, hT3, hT5, hT6, hT7, hT8, hlt1, hlt2, hrepT,
      hfootT, ho₁, hz1, hlo1, hcost1⟩ :=
    asmFirstInitTourStmt_runs (tr := tr) (cWords := cWords) hpT ω hfT r3 r4 r10 r11 r14 hRot
      (by rw [hcsG]; exact hVlt) (by rw [hcsG]; exact hElt) hw hOrdAt hOrdLe hExp hExpLe hz
      (by simp only [ASM_BR_SIZE]; omega)
  have q : ∀ i, i ≠ 15 → st1.regs i = st.regs i := fun i hi => by
    rw [hregs1, Function.update_of_ne hi]
  have q15 : st1.regs 15 = o₁ := by rw [hregs1, Function.update_self]
  have q2 : st1.regs 2 = graph := (q 2 (by omega)).trans r2
  have q4 : st1.regs 4 = expPtr := (q 4 (by omega)).trans r4
  have q5 : st1.regs 5 = k := (q 5 (by omega)).trans r5
  have q8 : st1.regs 8 = L := (q 8 (by omega)).trans r8
  have q9 : st1.regs 9 = P := (q 9 (by omega)).trans r9
  have q10 : st1.regs 10 = vCap := (q 10 (by omega)).trans r10
  have q11 : st1.regs 11 = eCap := (q 11 (by omega)).trans r11
  have q13 : st1.regs 13 = lengths := (q 13 (by omega)).trans r13
  have hS16 : ASM_BR_SIZE = 16 := rfl
  have ho₁' : o₁ + 2 ≤ h + 16 + tourBranchInitSpace vCap eCap := by rw [← hS16]; exact ho₁
  set mem1 := st1.mem with hmem1
  have hlo1' : ∀ a < h, mem1 a = mem a := hlo1
  have hbws : bucketWordSpace Lw L = 5 * Lw + 16 * (Lw + L + 1) + 4 := rfl
  have hB' : B = 2 * (P + (5 * Lw + 16 * (Lw + L + 1) + 4)) + 1 := rfl
  set fD := mem (expPtr + 1) with hfD
  set nF := mem (fD + 2) with hnF
  set fTrip := mem (fD + 3) with hfTrip
  set phi1 := (tourAsmRep vCap eCap).phi tourH xT mem1 with hphi1
  set T := tourBranchInitMul * (1 + cWords + G.m + G.n) * tourLog eCap + 60 +
    bucketTableCost Lw L G.m + compMapCost G.n G.m +
    slotListCost G.m (components G).card nF + 200 with hT
  have hcost1' : c1 + phi1 ≤ tourBranchInitMul * (1 + cWords + G.m + G.n) * tourLog eCap + 60 := by
    rw [← hcsG]; exact hcost1
  suffices H : ∃ o st' c, Runs w p ω (asmFirstInitFrontStmt F) st o st' c ∧
      normalPost (fun st' => ∃ cmpH ctH sH comps S D memC,
        AsmFiFrontOut w depth tr ord G ℓ₀ mem st.regs expPtr k L P vCap eCap h o₁ tourH xT
          cmpH ctH sH comps S D memC st' ∧
        (tourAsmRep vCap eCap).phi tourH xT st'.mem = phi1) o st' ∧
      phi1 + c ≤ T by
    obtain ⟨o, st', c, hr, hq, hc⟩ := H
    cases o with
    | returned _ => exact absurd hq id
    | normal =>
      obtain ⟨cmpH, ctH, sH, comps, S, D, memC, hout, hphi⟩ := hq
      exact ⟨o₁, tourH, xT, cmpH, ctH, sH, comps, S, D, memC, st', c, hr, hout, by omega⟩
  unfold asmFirstInitFrontStmt
  refine runs_seq_runs_le hrun1 ?_
  -- step 2a: the bucket table at `o₁ + 16`
  have hG1 : DynGraphAt mem1 graph vCap eCap G :=
    dynGraphAt_of_agree hG fun a h1 h2 => hlo1' a (by omega)
  have hExp1 : CompBranchExportAt w mem1 expPtr expEnd L capExp M N vCap eCap tr.cs :=
    compBranchExportAt_congr (fun a h1 h2 => (hlo1' a (by omega)).symm) hExp
  have hlenLe : lengths + eCap * L ≤ h := hlen.1
  have hlen1 : BranchLengthsAt mem1 lengths eCap L P h G ℓ₀ :=
    BranchLengthsAt.of_agree hlen (fun a h1 h2 => hlo1' a (by omega)) hlenLe
  have hLw1 : mem1 (expPtr + 6) = Lw := hlo1' _ (by omega)
  obtain ⟨st2b, c2, hrun2, hbIn, hbOut, hbWord, hbLow, -, hbZ, hc2⟩ :=
    bucketTable_runs (b := F.fBkt) hw10 hpB ω (pos := st1.pos) (graph := graph)
      (expPtr := expPtr) (lengths := lengths) (L := L) (P := P) (bktH := o₁ + 16)
      (heap := o₁ + 16 + eCap) (h₀ := h) hG1 (by omega) hExp1 hcsG (by omega) hlen1 (by omega)
      (le_refl _) (fun a ha => hz1 a (by omega))
      (by rw [hLw1]; omega) (by rw [hLw1]; omega)
  rw [hLw1] at hrun2 hbZ hc2
  have hb0 : p.procs[F.fBkt]? = some (bucketTableBody (F.fBkt + 1)) := by
    simpa [bucketTableModule] using hpB 0 (by simp [bucketTableModule])
  set bktEnd := o₁ + 16 + eCap + G.m * bucketWordSpace Lw L with hbktEnd
  refine runs_seq_call_post_le (B := bucketTableCost Lw L G.m)
    (vs := [graph, expPtr, lengths, L, P, o₁ + 16, o₁ + 16 + eCap])
    (Q_call := fun v m' => v = bktEnd ∧ (∀ a < o₁ + 16, m' a = mem1 a) ∧
      (∀ e ∈ G.E, m' (o₁ + 16 + e) = bucketCode (bucketOf (tr.cs.lsf.wstr e * ℓ₀ e))) ∧
      (∀ e < eCap, e ∉ G.E → m' (o₁ + 16 + e) = 0) ∧ (∀ e < eCap, m' (o₁ + 16 + e) < 2 ^ w) ∧
      ZeroFrom m' bktEnd) hb0 (by eval_expr)
    ⟨.returned bktEnd, st2b, c2, hrun2, ⟨rfl, hbLow, hbIn, hbOut, hbWord, hbZ⟩, hc2⟩
    (fun v2 mem2 pos2 hpost2 => ?_)
  obtain ⟨rfl, hlo2, hbIn2, hbOut2, hbWord2, hz2⟩ := hpost2
  -- step 2b: the map to the components at `bktEnd`
  have hG2 : DynGraphAt mem2 graph vCap eCap G :=
    dynGraphAt_of_agree hG1 fun a h1 h2 => hlo2 a (by omega)
  obtain ⟨o3, st3, c3, hr3, ⟨comps, ho3, hpost3⟩, hc3⟩ :=
    compMap_runs (w := w) (ω := ω) (pos := pos2) (cmpH := bktEnd) (heap := bktEnd + vCap) hpC hG2
      (by omega) (le_refl _) hz2 (by unfold compMapSpace; omega) (by omega)
  have hc0 : p.procs[F.fComp]? = some (compMapBody (F.fComp + 1) (F.fComp + 2)) := by
    simpa [compMapModule] using hpC 0 (by simp [compMapModule])
  refine runs_seq_call_post_le (B := compMapCost G.n G.m) (vs := [graph, bktEnd, bktEnd + vCap])
    (Q_call := fun v m' => ∃ comps : List (Finset ℕ), v = comps.length ∧
      CompMapPost w G vCap bktEnd (bktEnd + vCap) mem2 m' comps) hc0
    (by eval_expr) ⟨o3, st3, c3, hr3, ⟨comps, by rw [ho3]; rfl, hpost3⟩, hc3⟩
    (fun v3 mem3 pos3 hq3 => ?_)
  clear hr3 hpost3 ho3 hc3 st3 o3 comps
  obtain ⟨comps, rfl, hP⟩ := hq3
  obtain ⟨hnd3, hiff3, hidx3, hword3, hlo3, -, hz3⟩ := id hP
  have hncomp : comps.length ≤ vCap := compMapPost_length_le hP hVlt
  have hlenC : comps.length = (components G).card := by
    rw [← List.toFinset_card_of_nodup hnd3]
    congr 1
    ext C
    simp [hiff3]
  have hlo3h : ∀ a < h, mem3 a = mem a := fun a ha => by
    rw [hlo3 a (by omega), hlo2 a (by omega), hlo1' a ha]
  have hLw3 : mem3 (expPtr + 6) = Lw := hlo3h _ (by omega)
  -- the start of the table of the components, and the key base
  refine runs_seq_assign_le (v := bktEnd + vCap + (5 * vCap + 6 * eCap + 3)) (by eval_expr) ?_
  refine runs_seq_assign_le (v := B) (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  -- step 2c: the slot lists
  set ctH := bktEnd + vCap + (5 * vCap + 6 * eCap + 3) with hctH
  have hG3 : DynGraphAt mem3 graph vCap eCap G :=
    dynGraphAt_of_agree hG2 fun a h1 h2 => hlo3 a (by omega)
  have hfe_eq : slotForestEdges mem3 fTrip nF = slotForestEdges mem fTrip nF := by
    unfold slotForestEdges
    refine List.map_congr_left fun t ht => ?_
    have := List.mem_range.mp ht
    exact hlo3h _ (by omega)
  have hkw3 : comps.length * B < 2 ^ w :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hncomp) hkw
  obtain ⟨o4, st4, c4, hr4, ⟨ho4, S, D, hout4⟩, hc4⟩ :=
    slotList_runs (w := w) (b := F.fSlot) (ω := ω) (pos := pos3) (graph := graph)
      (expPtr := expPtr) (cmpH := bktEnd) (bktH := o₁ + 16) (nComp := comps.length) (k := k)
      (B := B) (ctH := ctH) (heap := ctH + 3 * comps.length) (fD := fD) (nF := nF)
      (fTrip := fTrip) hpS hG3 (by omega) (hlo3h _ (by omega)) (hlo3h _ (by omega))
      (hlo3h _ (by omega)) (by rw [hfe_eq]; exact hfe) (by omega)
      (fun e he => by
        have htl := hVlt _ (hGval e he).1
        obtain ⟨c, hc, -, hcv⟩ := compMapPost_idx hP (hGval e he).1
        exact ⟨by omega, by unfold slotCOf; omega⟩)
      (fun e he => by
        have := hElt e he
        refine ⟨by omega, ?_⟩
        rw [hlo3 _ (by omega), hbIn2 e he]
        exact hcode e he)
      (le_refl _) (fun a ha => hz3 a (by unfold compMapSpace; omega))
      (by unfold slotListSpace; omega) hkw3 (by omega) (by omega) (by omega)
  have hs0 : p.procs[F.fSlot]? = some (slotListBody (F.fSlot + 1)) := by
    simpa [slotListModule] using hpS 0 (by simp [slotListModule])
  set sH := ctH + 3 * comps.length with hsH
  refine runs_seq_call_post_le (B := slotListCost G.m comps.length nF)
    (vs := [graph, expPtr, bktEnd, o₁ + 16, comps.length, k, B, ctH, sH])
    (Q_call := fun v m' => v = sH + slotListSpace eCap G.m ∧ ∃ S D,
      SlotListOut mem3 m' G (slotForestEdges mem3 fTrip nF) bktEnd (o₁ + 16) comps.length k B
        ctH sH eCap S D) hs0
    (by eval_expr) ⟨o4, st4, c4, hr4, ⟨by rw [ho4]; rfl, S, D, hout4⟩, hc4⟩
    (fun v4 mem4 pos4 hq4 => ?_)
  clear hr4 hout4 ho4 hc4 st4 o4 S D
  obtain ⟨rfl, S, D, hO⟩ := hq4
  have hGm : mem3 (graph + 3) = G.m := by
    obtain ⟨-, -, -, -, -, -, hmM, -⟩ := hG3
    simpa [dgMOff] using hmM
  have hm4 : mem4 (graph + 3) = G.m := (hO.low _ (by omega)).trans hGm
  have hnD : mem4 sH = D.length := hO.nD
  refine runs_seq_assign_le (v := sH) (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_assign_le (v := G.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := sH + 2 + eCap + 5 * G.m)
    (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  have hlo41 : ∀ a < o₁ + 16, mem4 a = mem1 a := fun a ha => by
    rw [hO.low a (by omega), hlo3 a (by omega), hlo2 a ha]
  obtain ⟨hrep4, hphi4⟩ := asmBrTourView_keep (fun vCap eCap => tourAsmRep_local vCap eCap)
    ⟨tr, ord, vCap, eCap⟩ (s := ⟨outCoreOrder tr ord, ∅⟩) (tourH := tourH) (tx := xT)
    (mem := mem1) (mem' := mem4) fun a ha => (hlo41 a (by have := hfootT a ha; omega)).symm
  have hsl : slotListCost G.m comps.length nF = slotListCost G.m (components G).card nF := by
    rw [hlenC]
  refine runs_assign_le (v := D.length) (by eval_expr) ⟨bktEnd, ctH, sH, comps, S, D, mem3,
    ⟨fun i hi => ?_, by simp [q15],
      by simp, by simp,
      by simp, by simp; rfl,
      by simp, by simp,
      by simp, by simp,
      by simp,
      rfl, rfl, rfl, fun a ha => (hO.low a (by omega)).trans (hlo3h a ha),
      (hlo41 _ (by simp only [ASM_BR_TOUR]; omega)).trans hT3,
      (hlo41 _ (by simp only [ASM_BR_VCAP]; omega)).trans hT5,
      (hlo41 _ (by simp only [ASM_BR_ECAP]; omega)).trans hT6,
      (hlo41 _ (by simp only [ASM_BR_TCAP]; omega)).trans hT7,
      (hlo41 _ (by simp only [ASM_BR_LW]; omega)).trans hT8,
      hlt1, hlt2, hrep4 hrepT, hfootT, ho₁,
      fun a h1 h2 => (hlo41 a h2).trans (hz1 a h1),
      fun e he => by
        have := hElt e he
        exact (hO.low _ (by omega)).trans ((hlo3 _ (by omega)).trans (hbIn2 e he)),
      fun e he hne => (hO.low _ (by omega)).trans ((hlo3 _ (by omega)).trans (hbOut2 e he hne)),
      fun e he => by
        show mem4 (o₁ + 16 + e) < 2 ^ w
        rw [show mem4 (o₁ + 16 + e) = mem2 (o₁ + 16 + e) from
          (hO.low _ (by omega)).trans (hlo3 _ (by omega))]
        exact hbWord2 e he,
      hnd3, hiff3,
      fun c hc v hv => by
        have hvV : v ∈ G.V := by
          have hC := (hiff3 _).mp (List.getElem_mem hc)
          obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hC
          rw [← hu] at hv
          exact (mem_compOf_iff.mp hv).1
        have := hVlt v hvV
        exact (hO.low _ (by omega)).trans (hidx3 c hc v hv),
      fun v hv => by
        show mem4 (bktEnd + v) < 2 ^ w
        rw [show mem4 (bktEnd + v) = mem3 (bktEnd + v) from hO.low _ (by omega)]
        exact hword3 v hv,
      hfe_eq ▸ hO, fun a ha => (hO.low a ha).symm, hO.zero, by
        have hsl1 : slotListSpace eCap G.m ≤ slotListSpace eCap eCap := by
          simp only [slotListSpace]; omega
        show sH + slotListSpace eCap G.m ≤ h + asmFiFrontSpace vCap eCap Lw L
        simp only [asmFiFrontSpace, ASM_BR_SIZE] at ho₁ ⊢
        omega⟩,
    by rw [← hphi4]⟩ ?_
  · have hne : ∀ j, 15 ≤ j → i ≠ j := fun j hj => Nat.ne_of_lt (lt_of_lt_of_le hi hj)
    simp only [Function.update_apply, hne 16 (by norm_num), hne 17 (by norm_num),
      hne 18 (by norm_num), hne 19 (by norm_num), hne 20 (by norm_num), hne 21 (by norm_num),
      hne 22 (by norm_num), hne 23 (by norm_num), hne 24 (by norm_num), ite_false]
    exact q i (hne 15 le_rfl)
  · simp only [argsSize_cons, argsSize_nil, Expr.size_reg, Expr.size_const, Expr.size_bin,
      Expr.size_load]
    clear * - hcost1' hsl hT
    omega

end MinCostFlow.SparseCore.Program
