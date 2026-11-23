module

public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartBound
public import MinCostFlow.SparseCore.Program.AssemblyBranchEmbLink
public import MinCostFlow.SparseCore.Program.OutProcs
import MinCostFlow.SparseCore.Program.SpanBucketInit

/-!
# The restart of a branch (`AssemblyBranchRestart`)

This file proves that the program `asmBrRestartStmt` restarts a branch: it ends with the
representation of the branch at the model state `restartBundleTree depth sparsify tr ord`
(`asmBr_restart_runs`). The representation is `asmBrRep` with the bundle side
`asmBrSideRep` as its other parts, and the tour family `TR` of piece P2. P7 and P5 run on their
views of the tour (`AsmBrOutProj`, `AsmBrBunAt`).

The program makes three calls (`AssemblyBranchRestartRun.lean`).
1. The restart of P8 (`restartBranch_model_runs`). It restarts the bundles (P5, through the
   interface `AsmBrBunAt`), the bucket spanners (P6) and the graph `S` of the readout data (P10),
   and asks the root query `Q` of P4. The bundle side gives the model facts that it needs
   (`AsmBrSideModel`).
2. The reset of P7, in the block `OutProcsAt` of P7 (`outReset_body_runs`, the theorem that
   `sig_outReset_runs_outProcs` wraps). The output graph becomes the new `S_cur`, read from
   the readout data, and the marks of the tour become its ends. The ends lie in the core lists
   (`exists_mem_outCoreOrder`), since the old and the new `S_cur` have core edges only.
3. The refresh of the embedding table (`AsmBrEmbRefreshDisjAt`). The table then holds the walks
   of the restarted state (`refresh_emb_eq`, `asmBrEmbLink_of_inv`).

The bundle side keeps its model facts (`asmBrSideModel_restart`). The parts of the branch stay
disjoint, since each call writes below the heap pointer only to the cells of the parts it changes,
and the three calls allocate their new cells one after the other (`asmBr_disjoint_of_fresh`).

The cost is at most `asmBrRestartConst · singleBundleRestartMachCost`, plus the cost of the
refresh and `100` steps, against the potentials of the branch and of P4. The heap space is at most
`asmBrRestartSpace`. The cells of the branch after the restart are apart from those of P4: the
restart of P8 says that its new cells are apart from P4's.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- **The restart of a branch.** Let `p` hold the restart program at `f`, P8's restart at `f8`,
P7's block at `bOut`, the refresh at `fEmb` and the bucket spanners at `bSpan`. Let the branch at
`brH` hold `⟨tr, ord⟩` with the bundle side, the caps of the bundle table equal to those of the
branch, and `tr.k` equal to the cap `k` of P5's restart `J`. Let P4 hold `s4` at `cfH` with the
roots of the LSF of `tr`. Then the program, called as `[brH, cfH, j, h]`, ends with the branch at
the restarted state, P4 at `s4`, at most `sp` new cells, the memory below `h` changed only in the
cells of the branch and of P4, the two apart, and the cost of the module docstring. -/
theorem asmBr_restart_runs {w depth L capExp limbMul P : ℕ} {impl : SparsifyImpl}
    {OS : OutTourSpec} {nm sm fm lm : ℕ} {p : Program} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local) (hOP : AsmBrOutProj OS TR w p nm sm fm lm)
    (hTh : ∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH)
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {fBun : ℕ}
    (J : AsmBrBunAt TR B5 w p fBun)
    {fRoot : ℕ} (Q : RootQueryAt w p fRoot) {bRead readMul : ℕ} {readIdx : ℕ → ℕ}
    {fEmb embMul : ℕ} (E : AsmBrEmbRefreshDisjAt impl w depth p fEmb embMul)
    {f f8 bOut bSpan : ℕ}
    (hf : p.procs[f]? = some (asmBrRestartStmt f8 (outIdxReset bOut) fEmb))
    (hpS : p.HasAt bSpan (bucketSpannerProcs impl bSpan))
    (hpOut : OutProcsAt p bOut nm sm fm lm)
    (brH cfH j h sp vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
    (x : AsmBrConc TR (AsmBrSide B5 depth)) {Ψ : BundleTreeState depth → ℕ}
    (s4 : Q.σ) (x4 : Q.R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hp8 : p.procs[f8]? = some (restartBranchStmt fBun (bSpan + bsIdxOp0 + 0) (bRead + readIdx 3)))
    (hB : ReadBranchAt (readRep x.vCap x.eCap x.tCap x.L_w P) w x.vCap x.eCap x.tCap x.L_w P
      (asmBrSP impl w depth x.xRest) x.xRest.cap p bRead readIdx fRoot Q readMul)
    (hrep : AsmBrRepAt TR (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) P L capExp brH
      ⟨tr, ord, vCap, eCap⟩ x mem)
    (hV5 : x.xRest.vCap5 = x.vCap) (hE5 : x.xRest.eCap5 = x.eCap) (hvc : x.vCap = vCap)
    (hec : x.eCap = eCap)
    (hrep4 : Q.R.rep cfH s4 x4 mem)
    (hroots : ∀ u ∈ tr.cs.G.V, Q.ok s4 j u ∧ Q.root s4 j u = tr.cs.lsf.F.root u)
    (hfoot : ∀ a, asmBrFoot (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) brH x a → a < h)
    (hf4 : ∀ a, Q.R.foot cfH x4 a → a < h)
    (hd4 : ∀ a, asmBrFoot (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) brH x a →
      ¬ Q.R.foot cfH x4 a)
    (hargs : ∀ a ∈ [brH, cfH, j, h], a < 2 ^ w)
    (hw2 : (x.vCap + x.eCap + 2) ^ 2 < 2 ^ w) (hz : ZeroFrom mem h)
    (hsp : asmBrRestartSpace (J.space x.xRest.slotCap) readMul embMul OS
      (asmBrSP impl w depth x.xRest)
      x.xRest.bunS x.xRest.spanS tr.cs ord tr.k x.xRest.slots x.vCap x.eCap x.tCap x.L_w ≤ sp)
    (hspW : h + sp < 2 ^ w) (hΨ : Ψ (restartBundleTree depth (fun _ => canonicalSparsify impl) tr
      ord) ≤ singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord) :
    let tr' := restartBundleTree depth (fun _ => canonicalSparsify impl) tr ord
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x' x4',
      Runs w p ω body (startState [brH, cfH, j, h] mem pos) o st' c ∧
      AsmBrRepAt TR (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) P L capExp brH
        ⟨tr', ord, vCap, eCap⟩ x' st'.mem ∧
      x'.xRest.vCap5 = x'.vCap ∧ x'.xRest.eCap5 = x'.eCap ∧
      x'.xRest.slotCap = x.xRest.slotCap ∧ x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧
      x'.tCap = x.tCap ∧ x'.L_w = x.L_w ∧
      Q.R.rep cfH s4 x4' st'.mem ∧
      h ≤ o.value ∧ o.value ≤ h + sp ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ asmBrFoot (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) brH x a →
        ¬ Q.R.foot cfH x4 a → st'.mem a = mem a) ∧
      (∀ a, asmBrFoot (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) brH x' a →
        asmBrFoot (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) brH x a ∨
          (h ≤ a ∧ a < o.value)) ∧
      (∀ a, Q.R.foot cfH x4' a → Q.R.foot cfH x4 a ∨ (h ≤ a ∧ a < o.value)) ∧
      (∀ a, asmBrFoot (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) brH x' a →
        ¬ Q.R.foot cfH x4' a) ∧
      c + asmBrPhi (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) x' st'.mem +
          Q.R.phi cfH x4' st'.mem ≤
        asmBrRestartConst J.mul readMul Q.cost OS.mul capExp *
            singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord +
          asmBrEmbBound embMul (asmBrSP impl w depth x.xRest) x.xRest.bunS
            x.xRest.spanS tr.cs ord tr.k x.xRest.slots + 100 +
          asmBrPhi (asmBrSideRep B5 impl w depth L capExp limbMul Ψ) x mem +
          Q.R.phi cfH x4 mem := by
  intro tr'
  set XS := asmBrSideRep B5 impl w depth L capExp limbMul Ψ with hXS
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hG, hlsf, hS, hinv, hR, hE, hdom, hemb, hO, hT,
    hmarks, hXr, hV, hcap, hLw, hdisj⟩ := hrep
  obtain ⟨s0, s1, s2, s3, s4', s5, s6, s7, s8, s9, s10, s11, hwd, hB5, hS6, hL, hSCap, hsdisj, hmaps,
    hmod⟩ := hXr
  obtain ⟨hMap, hMatch, hSpan0, hMod, hok, hk, hrot, hPle, hC, hSB, hCapS, hBD, hinvB⟩ := id hmod
  -- P7's operations on P7's view of the tour
  obtain ⟨⟨repT, hlocT, hnT, hsT, hfT, hlT⟩, hrepT⟩ :=
    hOP x.vCap x.eCap ord tr.cs.lsf.F (outCoreOrder tr ord)
  subst hrepT
  let TT : OutTourAt OS w x.vCap x.eCap p nm sm fm lm := ⟨_, hlocT, hnT, hsT, hfT, hlT⟩
  -- every part lies below `h` and apart from P4
  have hP : ∀ i < 6, ∀ a, asmBrPart XS brH x i a → a < h := fun i hi a ha => hfoot a ⟨i, hi, ha⟩
  have hQ : ∀ i < 6, ∀ a, asmBrPart XS brH x i a →
      ¬ Q.R.foot cfH x4 a := fun i hi a ha => hd4 a ⟨i, hi, ha⟩
  have hSd : ∀ i < 4, ∀ a, asmSdPart x.restH x.xRest i a →
      asmBrPart XS brH x 5 a := fun i hi a ha => ⟨i, hi, ha⟩
  have hD : ∀ i < 6, ∀ j < 6, i ≠ j → ∀ a,
      asmBrPart XS brH x i a →
      ¬ asmBrPart XS brH x j a := hdisj
  -- word bounds
  have hhW : h < 2 ^ w := hargs h (by simp)
  have hbrec := asmBr_record_lt hfoot
  have hsdrec : x.restH + ASM_SD_SIZE ≤ h := by
    have := hP 5 (by decide) (x.restH + (ASM_SD_SIZE - 1)) (hSd 0 (by decide) _ ⟨by omega, by simp [ASM_SD_SIZE]⟩)
    simp only [ASM_SD_SIZE] at this ⊢; omega
  have hrdrec : x.readH + readFullWords ≤ h := by
    have := hP 1 (by decide) (x.readH + (readFullWords - 1)) (Or.inl ⟨by omega, by simp [readFullWords]⟩)
    simp only [readFullWords] at this ⊢; omega
  have htourH : x.tourH < h := hP 4 (by decide) _ (hTh _ _ _ _)
  have hrecW : ∀ i < ASM_SD_SIZE, ∀ v, mem (x.restH + i) = v → v < 2 ^ w := fun i hi v hv => hv ▸ hwd i hi
  have hbunW := hrecW _ (by decide) _ s0; have hspanW := hrecW _ (by decide) _ s1
  have hslotsW := hrecW _ (by decide) _ s2; have hnW := hrecW _ (by decide) _ s3
  have hLW := hrecW _ (by decide) _ s7; have hsplitW := hrecW _ (by decide) _ s8
  have hspVW := hrecW _ (by decide) _ s9; have hspEW := hrecW _ (by decide) _ s10
  have hw16 : 16 ≤ 2 ^ w := by have := hbrec; simp only [ASM_BR_SIZE] at this; omega
  have hslotsH : x.xRest.slotsPtr + x.xRest.slots.length ≤ h := by
    have := hP 5 (by decide) _ (hSd 3 (by decide) (x.xRest.slotsPtr + x.xRest.slots.length) (Or.inl ⟨by omega, by omega⟩)); omega
  -- the facts on the model that P8 asks
  have hcord := coreCordOf_outCoreOrder (st := tr) (ord := ord) hrot
  have hcordT : CoreCordOf tr.cs ord x.sTour.cord := by rw [hmarks.1]; exact hcord
  have hinvT : bunRestartInv x.vCap x.eCap x.xRest.bunS x.sTour.cord := by
    rw [hmarks.1, hvc, hec]; exact hinvB.1
  obtain ⟨heW, hvW⟩ := caps_lt_word hw2
  have hB' : ReadBranchAt (readRep x.vCap x.eCap x.tCap x.L_w P) w x.vCap x.xRest.eCap5 x.tCap
      x.L_w P (asmBrSP impl w depth x.xRest) x.xRest.cap p bRead readIdx fRoot Q readMul := by
    rw [hE5]; exact hB
  have hcap5 : SparseCoreCapHyp (capExp + 7) limbMul L tr.m₀ tr.n₀ x.vCap x.xRest.eCap5 := by
    rw [hE5]; exact ⟨hcap.trans (Nat.pow_le_pow_right (by omega) (by omega)), hCapS.2⟩
  have hroots' : ∀ u ∈ x.yRead.view.G.V,
      Q.ok s4 j u ∧ Q.root s4 j u = x.yRead.view.lsf.F.root u := by
    rw [hG, hlsf]; exact hroots
  have hS6act : ∀ s ∈ x.xRest.slots, ∃ hs : s < x.xRest.cap, (x.xRest.spanS ⟨s, hs⟩).isSome := by
    intro s hs
    obtain ⟨q, hq, rfl⟩ := hMap.2.2.1 s hs
    obtain ⟨hs', d, hd, -⟩ := hSpan0 q hq
    exact ⟨hs', by simp [hd]⟩
  have hfree : ∀ a, x.xRest.slotsPtr ≤ a → a < x.xRest.slotsPtr + x.xRest.slots.length →
      ¬ (B5 x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5).foot x.xRest.bunH x.xRest.xBun a ∧
      ¬ TT.rep.foot x.tourH x.xTour a ∧
      ¬ bucketFoot x.xRest.spanH x.xRest.xSpan a ∧
      ¬ readFoot x.vCap x.eCap x.tCap x.L_w x.readH x.yRead a := by
    intro a ha1 ha2
    have h3 : asmSdPart x.restH x.xRest 3 a := Or.inl ⟨ha1, by omega⟩
    exact ⟨fun hb => hsdisj 3 (by decide) 1 (by decide) (by decide) a h3 hb,
      fun ht => hD 5 (by decide) 4 (by decide) (by decide) a (hSd 3 (by decide) a h3) ht,
      fun hb => hsdisj 3 (by decide) 2 (by decide) (by decide) a h3 hb,
      fun hr => hD 5 (by decide) 1 (by decide) (by decide) a (hSd 3 (by decide) a h3) hr⟩
  have hfeet : FeetDisjoint
      ((B5 x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5).foot x.xRest.bunH x.xRest.xBun)
      (TT.rep.foot x.tourH x.xTour) (bucketFoot x.xRest.spanH x.xRest.xSpan)
      (readFoot x.vCap x.eCap x.tCap x.L_w x.readH x.yRead) :=
    ⟨fun a hb ht => hD 5 (by decide) 4 (by decide) (by decide) a (hSd 1 (by decide) a hb) ht,
      fun a hb hs => hsdisj 1 (by decide) 2 (by decide) (by decide) a hb hs,
      fun a hb hr => hD 5 (by decide) 1 (by decide) (by decide) a (hSd 1 (by decide) a hb) hr,
      fun a ht hs => hD 4 (by decide) 5 (by decide) (by decide) a ht (hSd 2 (by decide) a hs),
      fun a ht hr => hD 4 (by decide) 1 (by decide) (by decide) a ht hr,
      fun a hs hr => hD 5 (by decide) 1 (by decide) (by decide) a (hSd 2 (by decide) a hs) hr⟩
  unfold asmBrRestartSpace at hsp
  have hhsp : h + asmBrP8Space (J.space x.xRest.slotCap) readMul (asmBrSP impl w depth x.xRest)
      x.xRest.bunS x.xRest.spanS tr.cs ord tr.k x.xRest.slots x.vCap x.tCap x.L_w < 2 ^ w := by
    omega
  have htourW : x.tourH < 2 ^ w := by omega
  have hreadW : x.readH < 2 ^ w := by
    have : x.readH < h := by simp only [readFullWords] at hrdrec; omega
    omega
  -- step 1: the restart of P8
  obtain ⟨body8, hb8, o8, st8, c8, S', x5', tx', x6', y', x4', hrun8, hrep5', hrepT', hinv8,
      hrep6', hrep7', hrep4', hBunKeep, hMatch', -, hSpan', hvG', hvLSF', hvS', hlo8, hhi8, hz8, hfr8,
      hft5, hftT, hft6, hft7, hft4, hdisj8, d54', dT4', d64', d74', hcost8⟩ :=
    restartBranch_model_runs (asmBrSP impl w depth x.xRest) p f8 fBun bSpan bRead readIdx fRoot Q
      readMul
      (J.toBR hTR x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5 x.vCap x.eCap ord tr.cs.lsf.F
        (outCoreOrder tr ord) x.sTour.marked hV5 hE5 heW hvW)
      (readRep_local x.vCap x.eCap x.tCap x.L_w P) hB'
      x.xRest.bunH x.tourH x.xRest.spanH x.readH x.xRest.slotsPtr h cfH j x.xRest.slots
      x.xRest.slotOf x.xRest.bunS x.xRest.xBun x.sTour.cord x.xTour x.xRest.spanS x.xRest.xSpan
      x.yRead.view x.yRead s4 x4 tr ord mem pos ω _
      hp8 hpS hbunW htourW hspanW hreadW hslotsW hhW (hargs cfH (by simp))
      (hargs j (by simp)) hLW hsplitW hspVW hspEW hw16 hL hslotsH hfree hMap hMatch hS6act hok
      hinvB.2.2.2.2.2.1.symm hk hcordT hinvT hMod hG hlsf (hS ▸ graphEq_refl _) hPle hC hSB hcap5 hCapS hB5 hT hS6 hR
      hrep4 hroots' hfeet (fun a hb => hQ 5 (by decide) a (hSd 1 (by decide) a hb))
      (fun a ht => hQ 4 (by decide) a ht) (fun a hs => hQ 5 (by decide) a (hSd 2 (by decide) a hs))
      (fun a hr => hQ 1 (by decide) a hr) (fun a hb => hP 5 (by decide) a (hSd 1 (by decide) a hb))
      (fun a ht => hP 4 (by decide) a ht) (fun a hs => hP 5 (by decide) a (hSd 2 (by decide) a hs))
      (fun a hr => hP 1 (by decide) a hr) hf4 hz le_rfl hhsp
  have hhi8' : o8.value ≤ h + asmBrP8Space (J.space x.xRest.slotCap) readMul (asmBrSP impl w depth
      x.xRest) x.xRest.bunS x.xRest.spanS tr.cs ord tr.k x.xRest.slots x.vCap x.tCap x.L_w := hhi8
  -- the model after the restart
  have hinvN : bunRestartInv vCap eCap S' (outCoreOrder tr ord) := by
    rw [← hvc, ← hec, ← hmarks.1]; exact hinv8
  have hmodN := asmBrSideModel_restart (y := x.xRest) (x' := x5') (x6' := x6') hmod hMatch' hSpan'
    hinvN hBunKeep (fun j hj => by simp [restartSpanState, hj])
  have hModN : RestartScurModelInv tr' := hmodN.2.2.2.1
  -- the graph `S` of the readout data after P8
  obtain ⟨hview', -, -, hrec', -, -, -, -⟩ := id hrep7'
  obtain ⟨-, -, -, -, -, r5, -, -, -, -, -, -, -, -, hSc', -⟩ := hrec'
  have hS2 : DynGraphAt st8.mem y'.q.s x.vCap x.eCap tr'.S_cur := dynGraphAt_of_graphEq hvS' hSc'
  have hg2 : ∀ a, y'.q.s ≤ a → a < y'.q.s + dynGraphSize x.vCap x.eCap →
      readFoot x.vCap x.eCap x.tCap x.L_w x.readH y' a :=
    fun a h1 h2 => Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))
  have hdsz : 4 ≤ dynGraphSize x.vCap x.eCap := by unfold dynGraphSize; omega
  have hg2h : y'.q.s + dynGraphSize x.vCap x.eCap ≤ o8.value := by
    have hr := hg2 (y'.q.s + dynGraphSize x.vCap x.eCap - 1) (by omega) (by omega)
    rcases hft7 _ hr with hr | hr
    · have := hP 1 (by decide) _ hr; omega
    · omega
  have houtH : x.outH < h := hP 3 (by decide) _ (Or.inl rfl)
  -- step 2: the reset of P7
  have hargsR : ∀ a ∈ [x.outH, x.tourH, y'.q.s, o8.value], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  have hrepO : (outGraphRep x.vCap x.eCap).rep x.outH tr.S_cur x.gOut st8.mem :=
    ((outGraphRep_local x.vCap x.eCap) x.outH tr.S_cur x.gOut mem st8.mem (fun a ha =>
      (hfr8 a (hP 3 (by decide) a ha)
        (fun hb => hD 3 (by decide) 5 (by decide) (by decide) a ha (hSd 1 (by decide) a hb))
        (fun ht => hD 3 (by decide) 4 (by decide) (by decide) a ha ht)
        (fun hs => hD 3 (by decide) 5 (by decide) (by decide) a ha (hSd 2 (by decide) a hs))
        (fun hr => hD 3 (by decide) 1 (by decide) (by decide) a ha hr)
        (hQ 3 (by decide) a ha)).symm)).1 hO
  have hmarksT : OutMarksOf x.sTour x.sTour.cord tr.S_cur.E := by rw [hmarks.1]; exact hmarks
  have hVlt : ∀ u ∈ tr.cs.G.V, u < x.vCap := by rw [← hG]; exact hinv.2.1
  have hendsR : ∀ e ∈ tr.S_cur.E ∪ tr'.S_cur.E, ∀ t : Bool,
      ∃ v < x.vCap, (e, t) ∈ x.sTour.cord v := by
    intro e he t
    rw [hmarks.1]
    have hcore : e ∈ (coreGraph tr.cs.G tr.cs.lsf).E := by
      rcases Finset.mem_union.mp he with he | he
      · exact hMod.2.2.2.1.2.1 he
      · exact hModN.2.2.2.1.2.1 he
    exact exists_mem_outCoreOrder hrot hVlt hcore t
  obtain ⟨bodyR, hbR, oR, stR, cR, txR, sR, hrunR, hOR, hTRo, hmarksR, hloR, hhiR, hzR, hfrR,
      hftR, hcostR⟩ :=
    outReset_body_runs TT hw2 hpOut.main.2.1 hpOut.parts.2.1
      hpOut.parts.2.2.1 tr.S_cur tr'.S_cur x.outH x.tourH
      y'.q.s o8.value x.gOut x.sTour tx' st8.mem st8.pos ω hargsR hrepO hrepT' hmarksT hS2 hV.symm
      hendsR (fun a ha => by have := hP 3 (by decide) a ha; omega) (fun a ha => by
        rcases hftT a ha with ha | ha
        · have := hP 4 (by decide) a ha; omega
        · omega)
      hg2h
      (fun a ho ht => by
        rcases hftT a ht with ht | ht
        · exact hD 3 (by decide) 4 (by decide) (by decide) a ho ht
        · have := hP 3 (by decide) a ho; omega)
      (fun a h1 h2 => by
        have hr := hg2 a h1 h2
        refine ⟨fun ho => ?_, fun ht => hdisj8.2.2.2.2.1 a ht hr⟩
        rcases hft7 a hr with hr | hr
        · exact hD 1 (by decide) 3 (by decide) (by decide) a hr ho
        · have := hP 3 (by decide) a ho; omega)
      hz8 (by omega)
  -- the cells that the first two calls keep
  have keepOld : ∀ a < h, ¬ asmBrPart XS brH x 1 a → ¬ asmBrPart XS brH x 3 a →
      ¬ asmBrPart XS brH x 4 a →
      ¬ (B5 x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5).foot x.xRest.bunH x.xRest.xBun a →
      ¬ bucketFoot x.xRest.spanH x.xRest.xSpan a → ¬ Q.R.foot cfH x4 a →
      stR.mem a = mem a := by
    intro a ha h1 h3 h4 hb hs hq
    rw [hfrR a (by omega) h3 (fun ht => by
      rcases hftT a ht with ht | ht
      · exact h4 ht
      · omega)]
    exact hfr8 a ha hb h4 hs h1 hq
  have keepNew : ∀ a < o8.value, ¬ (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a →
      ¬ TT.rep.foot x.tourH tx' a → stR.mem a = st8.mem a := hfrR
  have hrecR : ∀ i < ASM_BR_SIZE, stR.mem (brH + i) = mem (brH + i) := by
    intro i hi
    have h0' : asmBrPart XS brH x 0 (brH + i) := ⟨by omega, by omega⟩
    exact keepOld _ (by omega) (hD 0 (by decide) 1 (by decide) (by decide) _ h0')
      (hD 0 (by decide) 3 (by decide) (by decide) _ h0')
      (hD 0 (by decide) 4 (by decide) (by decide) _ h0')
      (fun hb => hD 0 (by decide) 5 (by decide) (by decide) _ h0' (hSd 1 (by decide) _ hb))
      (fun hs => hD 0 (by decide) 5 (by decide) (by decide) _ h0' (hSd 2 (by decide) _ hs))
      (hQ 0 (by decide) _ h0')
  have hrec8 : ∀ i < ASM_BR_SIZE, st8.mem (brH + i) = mem (brH + i) := by
    intro i hi
    have h0' : asmBrPart XS brH x 0 (brH + i) := ⟨by omega, by omega⟩
    exact hfr8 _ (by omega)
      (fun hb => hD 0 (by decide) 5 (by decide) (by decide) _ h0' (hSd 1 (by decide) _ hb))
      (hD 0 (by decide) 4 (by decide) (by decide) _ h0')
      (fun hs => hD 0 (by decide) 5 (by decide) (by decide) _ h0' (hSd 2 (by decide) _ hs))
      (hD 0 (by decide) 1 (by decide) (by decide) _ h0') (hQ 0 (by decide) _ h0')
  have hsdR : ∀ a, (asmSdPart x.restH x.xRest 0 a ∨ asmSdPart x.restH x.xRest 3 a) →
      stR.mem a = mem a := by
    intro a ha
    have h5 : asmBrPart XS brH x 5 a := by
      rcases ha with ha | ha
      · exact hSd 0 (by decide) a ha
      · exact hSd 3 (by decide) a ha
    exact keepOld a (hP 5 (by decide) a h5) (hD 5 (by decide) 1 (by decide) (by decide) a h5)
      (hD 5 (by decide) 3 (by decide) (by decide) a h5)
      (hD 5 (by decide) 4 (by decide) (by decide) a h5)
      (fun hb => by
        rcases ha with ha | ha
        · exact hsdisj 0 (by decide) 1 (by decide) (by decide) a ha hb
        · exact hsdisj 3 (by decide) 1 (by decide) (by decide) a ha hb)
      (fun hs => by
        rcases ha with ha | ha
        · exact hsdisj 0 (by decide) 2 (by decide) (by decide) a ha hs
        · exact hsdisj 3 (by decide) 2 (by decide) (by decide) a ha hs)
      (hQ 5 (by decide) a h5)
  -- step 3: the refresh of the embedding table
  have hslotsQ : ∀ q ∈ activePairs tr, ∃ (hs : x.xRest.slotOf q < x.xRest.cap) (d : DSHist),
      restartSpanState x.xRest.spanS x.xRest.bunS tr.cs ord tr.k x.xRest.slots
        ⟨x.xRest.slotOf q, hs⟩ = some d ∧ d = ⟨tr'.initBunG q, []⟩ ∧
      d.state (asmBrSP impl w depth x.xRest) = tr'.dyn q :=
    fun q hq => hSpan' q.1 (mem_activePairs.mp hq).1 q.2 (mem_activePairs.mp hq).2
  have hEmbR : (embRep x.eCap).rep x.embH x.yEmb.view x.yEmb stR.mem :=
    ((embRep_local x.eCap) x.embH x.yEmb.view x.yEmb mem stR.mem (fun a ha => by
      have ha' : asmBrPart XS brH x 2 a := ha
      exact (keepOld a (hP 2 (by decide) a ha') (hD 2 (by decide) 1 (by decide) (by decide) a ha')
        (hD 2 (by decide) 3 (by decide) (by decide) a ha')
        (hD 2 (by decide) 4 (by decide) (by decide) a ha')
        (fun hb => hD 2 (by decide) 5 (by decide) (by decide) a ha' (hSd 1 (by decide) a hb))
        (fun hs => hD 2 (by decide) 5 (by decide) (by decide) a ha' (hSd 2 (by decide) a hs))
        (hQ 2 (by decide) a ha')).symm)).1 hE
  have hS6R : (bucketSpannerRep (asmBrSP impl w depth x.xRest) x.xRest.cap).rep x.xRest.spanH
      (restartSpanState x.xRest.spanS x.xRest.bunS tr.cs ord tr.k x.xRest.slots) x6' stR.mem :=
    ((bucketSpannerRep_local (asmBrSP impl w depth x.xRest) x.xRest.cap) x.xRest.spanH _ x6'
      st8.mem stR.mem (fun a ha => by
        refine (keepNew a ?_ ?_ (fun ht => hdisj8.2.2.2.1 a ht ha)).symm
        · rcases hft6 a ha with ha | ha
          · have := hP 5 (by decide) a (hSd 2 (by decide) a ha); omega
          · omega
        · intro ho
          rcases hft6 a ha with ha | ha
          · exact hD 3 (by decide) 5 (by decide) (by decide) a ho (hSd 2 (by decide) a ha)
          · have := hP 3 (by decide) a ho; omega)).1 hrep6'
  have hLR : ListAt stR.mem x.xRest.slotsPtr x.xRest.slots := by
    intro i hi
    rw [hsdR _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact hL i hi
  have hEdgesLt : ∀ s ∈ x.xRest.slots, ∀ e ∈ slotGE (asmBrSP impl w depth x.xRest)
      (restartSpanState x.xRest.spanS x.xRest.bunS tr.cs ord tr.k x.xRest.slots) s,
      e < x.eCap := by
    intro s hs e he
    obtain ⟨q, hq, rfl⟩ := hMap.2.2.1 s hs
    rw [(slotGE_restart (P := asmBrSP impl w depth x.xRest) (fun _ => canonicalSparsify impl) hcord
      hq (hslotsQ q hq)).1] at he
    have hC' := mem_activePairs.mp hq
    have hcore := (hMod.2.2.2.2 q.1 hC'.1 q.2 hC'.2).1 he
    have heG : e ∈ x.yRead.view.G.E := by rw [hG]; exact (Finset.mem_sdiff.mp hcore).1
    exact hinv.2.2.1 e heG
  have hspE : oR.value + asmBrEmbBound embMul (asmBrSP impl w depth x.xRest) x.xRest.bunS
      x.xRest.spanS tr.cs ord tr.k x.xRest.slots < 2 ^ w := by
    omega
  obtain ⟨bodyE, hbE, oE, stE, cE, yE', hrunE, hE', hloE, hhiE, hzE, hfrE, hftE, hcostE⟩ :=
    E.runs x.xRest.mMax x.xRest.spV x.xRest.spE x.xRest.splitB x.xRest.cap x.eCap x.embH
      x.xRest.spanH x.xRest.slotsPtr oR.value x.xRest.slots x.yEmb.view x.yEmb
      (restartSpanState x.xRest.spanS x.xRest.bunS tr.cs ord tr.k x.xRest.slots) x6' stR.mem
      stR.pos ω
      (by
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        have := hP 2 (by decide) x.embH (Or.inl ⟨le_rfl, by omega⟩)
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega)
      hEmbR hS6R hLR (by omega)
      (fun s hs => by
        obtain ⟨q, hq, rfl⟩ := hMap.2.2.1 s hs
        obtain ⟨hs', d, hd, -⟩ := hslotsQ q hq
        exact ⟨hs', by simp [hd]⟩)
      hEdgesLt (slotWalkAgree_restartSpanState (asmBrSP impl w depth x.xRest) x.xRest.spanS hcordT
        hMap hMatch hSB hBD)
      (fun a ha => by have := hP 2 (by decide) a ha; omega)
      (fun a ha => by
        rcases hft6 a ha with ha | ha
        · have := hP 5 (by decide) a (hSd 2 (by decide) a ha); omega
        · omega)
      (fun a he hs => by
        rcases hft6 a hs with hs | hs
        · exact hD 2 (by decide) 5 (by decide) (by decide) a he (hSd 2 (by decide) a hs)
        · have := hP 2 (by decide) a he; omega)
      (fun a h1 h2 he => hD 5 (by decide) 2 (by decide) (by decide) a
        (hSd 3 (by decide) a (Or.inl ⟨h1, by omega⟩)) he)
      hzR hspE
  have hhiE' : oE.value ≤ oR.value + asmBrEmbBound embMul (asmBrSP impl w depth x.xRest)
      x.xRest.bunS x.xRest.spanS tr.cs ord tr.k x.xRest.slots := hhiE
  have hcostE' : cE ≤ asmBrEmbBound embMul (asmBrSP impl w depth x.xRest) x.xRest.bunS
      x.xRest.spanS tr.cs ord tr.k x.xRest.slots := hcostE
  -- the run of the program
  have hrun8' : Runs w p ω body8 (startState [mem (mem (brH + ASM_BR_REST) + ASM_SD_BUN),
      mem (brH + ASM_BR_TOUR), mem (mem (brH + ASM_BR_REST) + ASM_SD_SPAN),
      mem (brH + ASM_BR_READ), mem (mem (brH + ASM_BR_REST) + ASM_SD_NSLOTS),
      mem (mem (brH + ASM_BR_REST) + ASM_SD_SLOTS), h, cfH, j,
      mem (mem (brH + ASM_BR_REST) + ASM_SD_SPLIT), mem (mem (brH + ASM_BR_REST) + ASM_SD_SPV),
      mem (mem (brH + ASM_BR_REST) + ASM_SD_SPE),
      mem (mem (brH + ASM_BR_REST) + ASM_SD_SPL)] mem pos) o8 st8 c8 := by
    rw [h4, s0, h3, s1, h0, s3, s2, s8, s9, s10, s7]; exact hrun8
  have hrunR' : Runs w p ω bodyR (startState [st8.mem (brH + ASM_BR_OUT), mem (brH + ASM_BR_TOUR),
      st8.mem (mem (brH + ASM_BR_READ) + ASM_READ_S), o8.value] st8.mem st8.pos) oR stR cR := by
    rw [hrec8 ASM_BR_OUT (by decide), h2, h3, h0, show ASM_READ_S = 5 from rfl, r5]
    exact hrunR
  have hrunE' : Runs w p ω bodyE (startState [stR.mem (brH + ASM_BR_EMB),
      mem (mem (brH + ASM_BR_REST) + ASM_SD_SPAN), mem (mem (brH + ASM_BR_REST) + ASM_SD_SLOTS),
      mem (mem (brH + ASM_BR_REST) + ASM_SD_NSLOTS), oR.value] stR.mem stR.pos) oE stE cE := by
    rw [hrecR ASM_BR_EMB (by decide), h1, h4, s1, s2, s3]; exact hrunE
  obtain ⟨st', c, hrun, hmemE, hc⟩ := asmBrRestartStmt_runs (by omega)
    (by rw [h4]; omega) (by rw [h0]; simp only [ASM_READ_S, readFullWords] at hrdrec ⊢; omega)
    hb8 hbR hbE hrun8' hrunR' hrunE'
  -- the cells that the three calls keep
  have keepE : ∀ a < oR.value, ¬ embFoot x.eCap x.embH x.yEmb a → stE.mem a = stR.mem a := hfrE
  have hembLt : ∀ a, embFoot x.eCap x.embH x.yEmb a → a < h := fun a ha => hP 2 (by decide) a ha
  have keep8E : ∀ a < o8.value, ¬ (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a →
      ¬ TT.rep.foot x.tourH tx' a → ¬ embFoot x.eCap x.embH x.yEmb a →
      stE.mem a = st8.mem a := by
    intro a ha ho ht he
    rw [keepE a (by omega) he, keepNew a ha ho ht]
  have hslotsH1 : x.xRest.slotsPtr + x.xRest.slots.length + 1 ≤ h := by
    have := hP 5 (by decide) _ (hSd 3 (by decide) (x.xRest.slotsPtr + x.xRest.slots.length)
      (Or.inl ⟨by omega, by omega⟩))
    omega
  have hsdE : ∀ a, (asmSdPart x.restH x.xRest 0 a ∨ asmSdPart x.restH x.xRest 3 a) →
      stE.mem a = mem a := by
    intro a ha
    have h5 : asmBrPart XS brH x 5 a := by
      rcases ha with ha | ha
      · exact hSd 0 (by decide) a ha
      · exact hSd 3 (by decide) a ha
    rw [keepE a (by have := hP 5 (by decide) a h5; omega)
      (hD 5 (by decide) 2 (by decide) (by decide) a h5)]
    exact hsdR a ha
  have hsdRec : ∀ i < ASM_SD_SIZE, stE.mem (x.restH + i) = mem (x.restH + i) :=
    fun i hi => hsdE _ (Or.inl ⟨by omega, by omega⟩)
  have hrecE : ∀ i < ASM_BR_SIZE, stE.mem (brH + i) = mem (brH + i) := by
    intro i hi
    have h0' : asmBrPart XS brH x 0 (brH + i) := ⟨by omega, by omega⟩
    rw [keepE _ (by omega) (hD 0 (by decide) 2 (by decide) (by decide) _ h0'), hrecR i hi]
  -- each new cell of a part of P8 is kept by the last two calls
  have hnewOut : ∀ a, (a < h → ∃ i < 6, i ≠ 3 ∧
      asmBrPart XS brH x i a) →
      ¬ (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a := by
    intro a ha ho
    have hlt := hP 3 (by decide) a ho
    obtain ⟨i, hi, hi3, hai⟩ := ha hlt
    exact hD i hi 3 (by decide) hi3 a hai ho
  have hnewEmb : ∀ a, (a < h → ∃ i < 6, i ≠ 2 ∧
      asmBrPart XS brH x i a) →
      ¬ embFoot x.eCap x.embH x.yEmb a := by
    intro a ha he
    have hlt := hembLt a he
    obtain ⟨i, hi, hi2, hai⟩ := ha hlt
    exact hD i hi 2 (by decide) hi2 a hai he
  -- the readout data, the bundle table, the spanners and P4 in the final memory
  have hread8 : ∀ a, readFoot x.vCap x.eCap x.tCap x.L_w x.readH y' a → st8.mem a = stE.mem a := by
    intro a ha
    have hold : a < h → asmBrPart XS brH x 1 a := by
      intro hlt
      rcases hft7 a ha with ha' | ha'
      · exact ha'
      · omega
    refine (keep8E a ?_ (hnewOut a fun hlt => ⟨1, by decide, by decide, hold hlt⟩)
      (fun ht => hdisj8.2.2.2.2.1 a ht ha) (hnewEmb a fun hlt => ⟨1, by decide, by decide,
        hold hlt⟩)).symm
    rcases hft7 a ha with ha' | ha'
    · have := hP 1 (by decide) a ha'; omega
    · omega
  have hbun8 : ∀ a, (B5 x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5).foot x.xRest.bunH x5' a →
      st8.mem a = stE.mem a := by
    intro a ha
    have hold : a < h → asmBrPart XS brH x 5 a := by
      intro hlt
      rcases hft5 a ha with ha' | ha'
      · exact hSd 1 (by decide) a ha'
      · omega
    refine (keep8E a ?_ (hnewOut a fun hlt => ⟨5, by decide, by decide, hold hlt⟩)
      (fun ht => hdisj8.1 a ha ht) (hnewEmb a fun hlt => ⟨5, by decide, by decide,
        hold hlt⟩)).symm
    rcases hft5 a ha with ha' | ha'
    · have := hP 5 (by decide) a (hSd 1 (by decide) a ha'); omega
    · omega
  have hspanE : ∀ a, bucketFoot x.xRest.spanH x6' a → stR.mem a = stE.mem a := by
    intro a ha
    have hold : a < h → asmBrPart XS brH x 5 a := by
      intro hlt
      rcases hft6 a ha with ha' | ha'
      · exact hSd 2 (by decide) a ha'
      · omega
    refine (keepE a ?_ (hnewEmb a fun hlt => ⟨5, by decide, by decide, hold hlt⟩)).symm
    rcases hft6 a ha with ha' | ha'
    · have := hP 5 (by decide) a (hSd 2 (by decide) a ha'); omega
    · omega
  have hQ8 : ∀ a, Q.R.foot cfH x4' a → st8.mem a = stE.mem a := by
    intro a ha
    refine (keep8E a ?_ (fun ho => ?_) (fun ht => dT4' a ht ha) (fun he => ?_)).symm
    · rcases hft4 a ha with ha' | ha'
      · have := hf4 a ha'; omega
      · omega
    · rcases hft4 a ha with ha' | ha'
      · exact hQ 3 (by decide) a ho ha'
      · have := hP 3 (by decide) a ho; omega
    · rcases hft4 a ha with ha' | ha'
      · exact hQ 2 (by decide) a he ha'
      · have := hembLt a he; omega
  have hTE : ∀ a, TT.rep.foot x.tourH txR a → stR.mem a = stE.mem a := by
    intro a ha
    rcases hftR a ha with ha' | ha'
    · rcases hftT a ha' with ha'' | ha''
      · have := hP 4 (by decide) a ha''
        exact (keepE a (by omega) (fun he => hD 4 (by decide) 2 (by decide) (by decide) a ha''
          he)).symm
      · exact (keepE a (by omega) (fun he => by have := hembLt a he; omega)).symm
    · exact (keepE a (by omega) (fun he => by have := hembLt a he; omega)).symm
  have hOE : ∀ a, (outGraphRep x.vCap x.eCap).foot x.outH x.gOut a → stR.mem a = stE.mem a :=
    fun a ha => (keepE a (by have := hP 3 (by decide) a ha; omega)
      (fun he => hD 3 (by decide) 2 (by decide) (by decide) a ha he)).symm
  have hR8 := (readRep_local x.vCap x.eCap x.tCap x.L_w P x.readH _ (y'.withS tr'.S_cur) st8.mem
    stE.mem (fun a ha => hread8 a ha)).1 (readRep_of_graphEq_S hvS' hrep7')
  have hB5E := (J.rep_local x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5) x.xRest.bunH S' x5'
    st8.mem stE.mem
    hbun8
  have hS6E := (bucketSpannerRep_local (asmBrSP impl w depth x.xRest) x.xRest.cap) x.xRest.spanH
    (restartSpanState x.xRest.spanS x.xRest.bunS tr.cs ord tr.k x.xRest.slots) x6' stR.mem
    stE.mem hspanE
  have hQE := Q.R_local cfH s4 x4' st8.mem stE.mem hQ8
  have hTTE := (TT.rep_local) x.tourH sR txR stR.mem stE.mem hTE
  have hOE' := (outGraphRep_local x.vCap x.eCap) x.outH tr'.S_cur x.gOut stR.mem stE.mem hOE
  -- the embedding table
  have hRef := refresh_emb_eq (P := asmBrSP impl w depth x.xRest)
    (fun _ => canonicalSparsify impl) hcord hMap hslotsQ
    (asmBrEmbLink_of_inv _ hcord hMod hModN hBD) hdom hemb
  -- the new branch
  set xN : AsmBrConc TR (AsmBrSide B5 depth) :=
    { x with
      yRead := y'.withS tr'.S_cur, yEmb := yE', sTour := sR, xTour := txR
      xRest := { x.xRest with
        bunS := S', xBun := x5', xSpan := x6', walkPot := Ψ tr'
        spanS := restartSpanState x.xRest.spanS x.xRest.bunS tr.cs ord tr.k x.xRest.slots } }
    with hxN
  have hPm2 : ∀ i < 6, ∀ c, asmBrPart XS brH xN i c →
      asmBrPart XS brH x i c ∨ (h ≤ c ∧ c < oE.value) := by
    intro i hi c hc
    interval_cases i
    · exact Or.inl hc
    · rcases hft7 c hc with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h'.1, by omega⟩
    · rcases hftE c hc with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨by omega, h'.2⟩
    · exact Or.inl hc
    · rcases hftR c hc with h' | h'
      · rcases hftT c h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr ⟨h''.1, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · obtain ⟨k, hk, hck⟩ := hc
      interval_cases k
      · exact Or.inl ⟨0, by decide, hck⟩
      · rcases hft5 c hck with h' | h'
        · exact Or.inl ⟨1, by decide, h'⟩
        · exact Or.inr ⟨h'.1, by omega⟩
      · rcases hft6 c hck with h' | h'
        · exact Or.inl ⟨2, by decide, h'⟩
        · exact Or.inr ⟨h'.1, by omega⟩
      · exact Or.inl ⟨3, by decide, hck⟩
  -- the cost
  have hcost8' : c8 +
      (B5 x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5).phi x.xRest.bunH x5' st8.mem +
      TT.rep.phi x.tourH tx' st8.mem +
      bucketPhi (asmBrSP impl w depth x.xRest) x6' +
      (readRep x.vCap x.eCap x.tCap x.L_w P).phi x.readH y' st8.mem + Q.R.phi cfH x4' st8.mem ≤
      restartModelConst J.mul readMul Q.cost (capExp + 7) *
          singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord +
        ((B5 x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5).phi x.xRest.bunH x.xRest.xBun mem +
          TT.rep.phi x.tourH x.xTour mem +
          bucketPhi (asmBrSP impl w depth x.xRest) x.xRest.xSpan +
          (readRep x.vCap x.eCap x.tCap x.L_w P).phi x.readH x.yRead mem +
          Q.R.phi cfH x4 mem) := hcost8
  have hSoldG : tr.S_cur.E ⊆ tr.cs.G.E :=
    fun e he => (Finset.mem_sdiff.mp (hMod.2.2.2.1.2.1 he)).1
  have hSnewG : tr'.S_cur.E ⊆ tr.cs.G.E :=
    fun e he => (Finset.mem_sdiff.mp (hModN.2.2.2.1.2.1 he)).1
  have hreset := outResetCost_le_restartMachCost (mul := OS.mul)
    (fun _ => canonicalSparsify impl) (ord := ord) hSoldG hSnewG
    (show SparseCoreCapHyp capExp limbMul L tr.m₀ tr.n₀ x.vCap x.eCap from ⟨hcap, hCapS.2⟩)
  have hconst : asmBrRestartConst J.mul readMul Q.cost OS.mul capExp *
      singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord =
      restartModelConst J.mul readMul Q.cost (capExp + 7) *
        singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord +
      2000 * (OS.mul + 1) * (capExp + 1) *
        singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord +
      320 * (capExp + 1) *
        singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord +
      300 * singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord := by
    unfold asmBrRestartConst; ring
  have hLg : x.xRest.lgFac = bundleLogFactor tr.m₀ tr.n₀ := hinvB.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hΨ' : Ψ tr' ≤ _ := hΨ
  refine ⟨_, hf, .returned oE.value, st', c, xN, x4', hrun, ?_, hV5, hE5, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmemE]
    have hview2 : (y'.withS tr'.S_cur).view = { (x.yRead.view.rebuild
        (asmBrSP impl w depth x.xRest)
        (restartSpanState x.xRest.spanS x.xRest.bunS tr.cs ord tr.k x.xRest.slots)
        x.xRest.slots) with S := tr'.S_cur } := by
      show { y'.view with S := tr'.S_cur } = _
      rw [hview']
    have hR' := hR8
    rw [← hview2] at hR'
    refine ⟨(hrecE _ (by decide)).trans h0, (hrecE _ (by decide)).trans h1,
      (hrecE _ (by decide)).trans h2, (hrecE _ (by decide)).trans h3,
      (hrecE _ (by decide)).trans h4, (hrecE _ (by decide)).trans h5,
      (hrecE _ (by decide)).trans h6, (hrecE _ (by decide)).trans h7,
      (hrecE _ (by decide)).trans h8, ?_, ?_, rfl, ?_, hR', ?_, ?_, ?_, hOE'.1 hOR, hTTE.1 hTRo,
      ?_, ?_, rfl, hcap, hLw, ?_⟩
    · show y'.view.G = tr'.cs.G
      rw [hview']; exact hvG'
    · show y'.view.lsf = tr'.cs.lsf
      rw [hview']; exact hvLSF'
    · show ReadView.Inv x.vCap x.eCap x.tCap { y'.view with S := tr'.S_cur }
      rw [hview']; exact readViewInv_withS hinv hS2
    · show (embRep x.eCap).rep x.embH yE'.view yE' stE.mem
      exact ⟨rfl, hE'.1 ▸ hE'.2⟩
    · show _ ⊆ yE'.view.dom
      rw [hE'.1]; exact hRef.1
    · intro e he
      show yE'.view.emb e = _
      rw [hE'.1]; exact hRef.2 e he
    · show OutMarksOf sR (outCoreOrder tr' ord) tr'.S_cur.E
      have hm := hmarksR
      rw [hmarks.1] at hm
      exact hm
    · refine ⟨(hsdRec _ (by decide)).trans s0, (hsdRec _ (by decide)).trans s1,
        (hsdRec _ (by decide)).trans s2, (hsdRec _ (by decide)).trans s3,
        (hsdRec _ (by decide)).trans s4', (hsdRec _ (by decide)).trans s5,
        (hsdRec _ (by decide)).trans s6, (hsdRec _ (by decide)).trans s7,
        (hsdRec _ (by decide)).trans s8, (hsdRec _ (by decide)).trans s9,
        (hsdRec _ (by decide)).trans s10, (hsdRec _ (by decide)).trans s11,
        fun i hi => by rw [hsdRec i hi]; exact hwd i hi, hB5E.1 hrep5', hS6E.1 hS6R,
        fun i hi => by
          have hi' : i < x.xRest.slots.length := hi
          exact (hsdE (x.xRest.slotsPtr + i) (Or.inr (Or.inl ⟨by omega, by omega⟩))).trans
            (hL i hi'),
        hSCap, ?_, asmSdMaps_restart _ hsdRec (fun c hc => hsdE c (Or.inr (Or.inr hc))) hmaps, hmodN⟩
      exact asmSd_disjoint_of_new12 hsdisj (fun c hc => hP 5 (by decide) c hc)
        (fun c hc => (hft5 c hc).imp id fun h' => h'.1)
        (fun c hc => (hft6 c hc).imp id fun h' => h'.1) hdisj8.2.1
    · have z1 : ∀ c, h ≤ c → asmBrPart XS brH xN 1 c → c < o8.value := by
        intro c hc hc1
        rcases hft7 c hc1 with h' | h'
        · have := hP 1 (by decide) c h'; omega
        · exact h'.2
      have z2 : ∀ c, h ≤ c → asmBrPart XS brH xN 2 c → oR.value ≤ c := by
        intro c hc hc2
        rcases hftE c hc2 with h' | h'
        · have := hP 2 (by decide) c h'; omega
        · exact h'.1
      have z4 : ∀ c, h ≤ c → asmBrPart XS brH xN 4 c →
          (TT.rep.foot x.tourH tx' c ∧ c < o8.value) ∨
            (o8.value ≤ c ∧ c < oR.value) := by
        intro c hc hc4
        rcases hftR c hc4 with h' | h'
        · rcases hftT c h' with h'' | h''
          · have := hP 4 (by decide) c h''; omega
          · exact Or.inl ⟨h', h''.2⟩
        · exact Or.inr h'
      have z5 : ∀ c, h ≤ c → asmBrPart XS brH xN 5 c →
          c < o8.value ∧ ((B5 x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5).foot x.xRest.bunH x5' c ∨
            bucketFoot x.xRest.spanH x6' c) := by
        intro c hc hc5
        obtain ⟨k, hk, hck⟩ := hc5
        interval_cases k
        · exact absurd (show c < x.restH + ASM_SD_SIZE from hck.2) (by omega)
        · rcases hft5 c hck with h' | h'
          · have := hP 5 (by decide) c (hSd 1 (by decide) c h'); omega
          · exact ⟨h'.2, Or.inl hck⟩
        · rcases hft6 c hck with h' | h'
          · have := hP 5 (by decide) c (hSd 2 (by decide) c h'); omega
          · exact ⟨h'.2, Or.inr hck⟩
        · have := hP 5 (by decide) c (hSd 3 (by decide) c hck); omega
      apply asmBr_disjoint_of_fresh hdisj hfoot
        (fun i hi c hc => (hPm2 i hi c hc).imp id (fun h' => h'.1))
      intro i hi j hj hij c hc hci hcj
      interval_cases i <;> interval_cases j
      · exact absurd hci.2 (by omega)
      · exact absurd hci.2 (by omega)
      · exact absurd hci.2 (by omega)
      · exact absurd hci.2 (by omega)
      · exact absurd hci.2 (by omega)
      · have := z1 c hc hci; have := z2 c hc hcj; omega
      · have := hP 3 (by decide) c hcj; omega
      · rcases z4 c hc hcj with ⟨ht, -⟩ | ⟨h', -⟩
        · exact hdisj8.2.2.2.2.1 c ht hci
        · have := z1 c hc hci; omega
      · obtain ⟨-, hb | hs⟩ := z5 c hc hcj
        · exact hdisj8.2.2.1 c hb hci
        · exact hdisj8.2.2.2.2.2 c hs hci
      · have := hP 3 (by decide) c hcj; omega
      · have := z2 c hc hci
        rcases z4 c hc hcj with ⟨-, h'⟩ | ⟨-, h'⟩ <;> omega
      · have := z2 c hc hci; have := (z5 c hc hcj).1; omega
      · have := hP 3 (by decide) c hci; omega
      · have := hP 3 (by decide) c hci; omega
      · obtain ⟨h5, hb | hs⟩ := z5 c hc hcj <;> rcases z4 c hc hci with ⟨ht, -⟩ | ⟨h', -⟩
        · exact hdisj8.1 c hb ht
        · omega
        · exact hdisj8.2.2.2.1 c ht hs
        · omega
  · rw [hmemE]; exact hQE.1 hrep4'
  · show h ≤ oE.value; omega
  · show oE.value ≤ h + sp
    omega
  · rw [hmemE]; exact hzE
  · intro a ha hnf hnq
    rw [hmemE, keepE a (by omega) (fun he => hnf ⟨2, by decide, he⟩)]
    exact keepOld a ha (fun h1 => hnf ⟨1, by decide, h1⟩) (fun h3 => hnf ⟨3, by decide, h3⟩)
      (fun h4 => hnf ⟨4, by decide, h4⟩) (fun hb => hnf ⟨5, by decide, hSd 1 (by decide) a hb⟩)
      (fun hs => hnf ⟨5, by decide, hSd 2 (by decide) a hs⟩) hnq
  · rintro a ⟨i, hi, hai⟩
    rcases hPm2 i hi a hai with h' | h'
    · exact Or.inl ⟨i, hi, h'⟩
    · exact Or.inr h'
  · intro a ha
    rcases hft4 a ha with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h'.1, show a < oE.value by omega⟩
  · refine asmBr_apart_of_fresh hd4 hf4 hft4
      (fun i hi c hc => (hPm2 i hi c hc).imp id fun h' => h'.1) fun i hi a hh hlt hai hq => ?_
    interval_cases i
    · have := hP 0 (by decide) a hai; omega
    · exact d74' a hai hq
    · rcases hftE a hai with h'' | h''
      · have := hP 2 (by decide) a h''; omega
      · omega
    · have := hP 3 (by decide) a hai; omega
    · rcases hftR a hai with h'' | h''
      · rcases hftT a h'' with h3 | h3
        · have := hP 4 (by decide) a h3; omega
        · exact dT4' a h'' hq
      · omega
    · obtain ⟨k, hk, hck⟩ := hai
      interval_cases k
      · have := hP 5 (by decide) a (hSd 0 (by decide) a hck); omega
      · exact d54' a hck hq
      · exact d64' a hck hq
      · have := hP 5 (by decide) a (hSd 3 (by decide) a hck); omega
  · rw [hmemE]
    show c + (readPotMul * treePot y'.view.G y'.view.lsf.T + TT.rep.phi x.tourH txR stE.mem +
        ((B5 x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5).phi x.xRest.bunH x5' stE.mem +
          320 * (capExp + 1) * x.xRest.lgFac * bucketPhi (asmBrSP impl w depth x.xRest) x6' +
          300 * Ψ tr')) + Q.R.phi cfH x4' stE.mem ≤ _
    rw [← hTTE.2, ← hB5E.2, ← hQE.2]
    show _ ≤ _ + _ + 100 + (readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T +
        TT.rep.phi x.tourH x.xTour mem +
        ((B5 x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5).phi x.xRest.bunH x.xRest.xBun mem +
          320 * (capExp + 1) * x.xRest.lgFac * bucketPhi (asmBrSP impl w depth x.xRest) x.xRest.xSpan +
          300 * x.xRest.walkPot)) + Q.R.phi cfH x4 mem
    change c8 + _ + _ + _ + readPotMul * treePot y'.view.G y'.view.lsf.T + _ ≤
      _ + (_ + _ + _ + readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T + _) at hcost8'
    have hscaled := bucketPhi_restart_scaled_add_le (capExp := capExp) hS6 hrep6' hMap hMatch hok
      hPle hC hSB.le hLg (A := c8 + (B5 x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5).phi
        x.xRest.bunH x5' st8.mem + TT.rep.phi x.tourH tx' st8.mem +
        readPotMul * treePot y'.view.G y'.view.lsf.T + Q.R.phi cfH x4' st8.mem)
      (B := restartModelConst J.mul readMul Q.cost (capExp + 7) *
          singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord +
        (B5 x.xRest.kB x.xRest.slotCap x.xRest.vCap5 x.xRest.eCap5).phi x.xRest.bunH x.xRest.xBun mem +
        TT.rep.phi x.tourH x.xTour mem + readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T +
        Q.R.phi cfH x4 mem) (by omega)
    change _ ≤ _ + 320 * (capExp + 1) *
        singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord + _ at hscaled
    omega

end MinCostFlow.SparseCore.Program
