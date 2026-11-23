module

public import MinCostFlow.SparseCore.Program.BundleStepEmitState

/-!
# Phase 3 candidate-splitting loop verification (`BundleStepEmitLoop`)

Verifies `forRange 24 0 candCnt (bundleStepEmitOneCandStmt ...)` across all sorted candidate
bundles of a single slot (`bundleStepEmitSlot_candsLoop`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

private lemma rangeCost_cands_eq (cA : ℕ) (f : ℕ → ℕ) (cands : List ℕ) :
    rangeCost (fun i => cA * f (cands.getD i 0) + 420) 0 cands.length =
      cA * (cands.map f).sum + 420 * cands.length := by
  have hgo : ∀ k ≤ cands.length,
      rangeCost (fun i => cA * f (cands.getD i 0) + 420) 0 k =
        cA * ((cands.take k).map f).sum + 420 * k := by
    intro k; induction k with
    | zero => intro _; simp [rangeCost]
    | succ k ih =>
      intro hk
      have hk_lt : k < cands.length := by omega
      have hrc_s : rangeCost (fun i => cA * f (cands.getD i 0) + 420) 0 (k + 1) =
          rangeCost (fun i => cA * f (cands.getD i 0) + 420) 0 k + (cA * f (cands.getD k 0) + 420) := by
        unfold rangeCost
        rw [Nat.sub_zero, Nat.sub_zero, List.range'_concat, List.map_append, List.sum_append]; simp
      have htk : ((cands.take (k + 1)).map f).sum = ((cands.take k).map f).sum + f (cands[k]'hk_lt) := by
        rw [List.take_succ_eq_append_getElem hk_lt, List.map_append, List.sum_append]; simp
      rw [hrc_s, ih (by omega), htk, List.getD_eq_getElem cands 0 hk_lt]; ring
  have hlen : (cands.take cands.length).map f = cands.map f := congrArg (List.map f) List.take_length
  simpa [hlen] using hgo cands.length (le_refl _)

set_option maxHeartbeats 400000 in
lemma bundleStepEmitSlot_candsLoop {TS : BundleTourSpec}
    {w vCap eCap p bunCap nB₀ tourH candArr offPtr bufPtr batchPtr writeOff₀ updCnt₀ prevBase nextBase endBundleBase h₀ : ℕ}
    {pProg : Program} {bDllPush bDllErase bMergeSort bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    {htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner}
    {cord' : ℕ → List End} {src' : End → ℕ} {G₀ : MGraph} {ops₀ : List Update} {B₀ : BundleState}
    {cands : List ℕ} {candSet_j : Finset ℕ} {scan_j : List (ℕ × ℕ × ℕ)}
    {tx₀ : htour.rep.τ} {st₀ : State}
    (hpPush : pProg.HasAt bDllPush [bundleDllPushStmt])
    (hpErase : pProg.HasAt bDllErase [bundleDllEraseStmt])
    (hMergeSort : ∀ L : List ℕ, MeetsContract w pProg bMergeSort (mergeSortContract w L))
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w) (heCap_w : 2 * eCap < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (hprev_w : prevBase + 2 * eCap < 2 ^ w) (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (heb_w : endBundleBase + 2 * eCap < 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hcand_w : candArr + cands.length < 2 ^ w)
    (hoff_w : offPtr + cands.length + 1 < 2 ^ w)
    (hbuf_w : bufPtr + scan_j.length < 2 ^ w)
    (hbat_w : batchPtr + writeOff₀ + 6 * scan_j.length < 2 ^ w)
    (hupd_w : updCnt₀ + scan_j.length < 2 ^ w)
    (hh_w : h₀ + (8 + 2 * TS.querySpace) * scan_j.length < 2 ^ w)
    (hV₀ : B₀.vertices = Finset.range nB₀)
    (hcands_nd : cands.Nodup) (hcands_lt : ∀ b ∈ cands, b < nB₀)
    (hcands_in_set : ∀ b ∈ cands, b ∈ candSet_j)
    (hscan_in_cands : ∀ t ∈ scan_j, t.1 ∈ cands)
    (hval : ScanValidForSlot B₀ src' candSet_j scan_j)
    (hnb_cap : nB₀ + scan_j.length ≤ bunCap)
    (hsrc_lt : ∀ x ∈ edgeEnds B₀.edges, src' x < vCap)
    (hsrc_mem : ∀ x ∈ edgeEnds B₀.edges, x ∈ cord' (src' x))
    (hsrc_uniq : ∀ x ∈ edgeEnds B₀.edges, ∀ v', x ∈ cord' v' → v' = src' x)
    (hprev_next : prevBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ prevBase)
    (hblk_prev : p + bundleSlotBlockSize bunCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ p)
    (hblk_next : p + bundleSlotBlockSize bunCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ p)
    (heb_prev : endBundleBase + 2 * eCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ endBundleBase)
    (heb_next : endBundleBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ endBundleBase)
    (heb_blk : endBundleBase + 2 * eCap ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ endBundleBase)
    (hbat_blk : batchPtr + writeOff₀ + 6 * scan_j.length ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ batchPtr)
    (hbat_prev : batchPtr + writeOff₀ + 6 * scan_j.length ≤ prevBase ∨ prevBase + 2 * eCap ≤ batchPtr)
    (hbat_next : batchPtr + writeOff₀ + 6 * scan_j.length ≤ nextBase ∨ nextBase + 2 * eCap ≤ batchPtr)
    (hbat_eb : batchPtr + writeOff₀ + 6 * scan_j.length ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ batchPtr)
    (hbat_h : batchPtr + writeOff₀ + 6 * scan_j.length ≤ h₀)
    (hh_blk : p + bundleSlotBlockSize bunCap ≤ h₀)
    (hh_prev : prevBase + 2 * eCap ≤ h₀) (hh_next : nextBase + 2 * eCap ≤ h₀)
    (hh_eb : endBundleBase + 2 * eCap ≤ h₀)
    (hcand_h : candArr + cands.length ≤ h₀)
    (hcand_blk : candArr + cands.length ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ candArr)
    (hcand_prev : candArr + cands.length ≤ prevBase ∨ prevBase + 2 * eCap ≤ candArr)
    (hcand_next : candArr + cands.length ≤ nextBase ∨ nextBase + 2 * eCap ≤ candArr)
    (hcand_eb : candArr + cands.length ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ candArr)
    (hcand_bat : candArr + cands.length ≤ batchPtr ∨ batchPtr + writeOff₀ + 6 * scan_j.length ≤ candArr)
    (hoff_h : offPtr + cands.length + 1 ≤ h₀)
    (hoff_blk : offPtr + cands.length + 1 ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ offPtr)
    (hoff_prev : offPtr + cands.length + 1 ≤ prevBase ∨ prevBase + 2 * eCap ≤ offPtr)
    (hoff_next : offPtr + cands.length + 1 ≤ nextBase ∨ nextBase + 2 * eCap ≤ offPtr)
    (hoff_eb : offPtr + cands.length + 1 ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ offPtr)
    (hoff_bat : offPtr + cands.length + 1 ≤ batchPtr ∨ batchPtr + writeOff₀ + 6 * scan_j.length ≤ offPtr)
    (hbuf_h : bufPtr + scan_j.length ≤ h₀)
    (hbuf_blk : bufPtr + scan_j.length ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ bufPtr)
    (hbuf_prev : bufPtr + scan_j.length ≤ prevBase ∨ prevBase + 2 * eCap ≤ bufPtr)
    (hbuf_next : bufPtr + scan_j.length ≤ nextBase ∨ nextBase + 2 * eCap ≤ bufPtr)
    (hbuf_eb : bufPtr + scan_j.length ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ bufPtr)
    (hbuf_bat : bufPtr + scan_j.length ≤ batchPtr ∨ batchPtr + writeOff₀ + 6 * scan_j.length ≤ bufPtr)
    (htrep : htour.rep.rep tourH cord' tx₀ st₀.mem)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < h₀)
    (htfoot_disj_blk : ∀ a, htour.rep.foot tourH tx₀ a → a < p ∨ p + bundleSlotBlockSize bunCap ≤ a)
    (htfoot_disj_prev : ∀ a, htour.rep.foot tourH tx₀ a → a < prevBase ∨ prevBase + 2 * eCap ≤ a)
    (htfoot_disj_next : ∀ a, htour.rep.foot tourH tx₀ a → a < nextBase ∨ nextBase + 2 * eCap ≤ a)
    (htfoot_disj_eb : ∀ a, htour.rep.foot tourH tx₀ a → a < endBundleBase ∨ endBundleBase + 2 * eCap ≤ a)
    (htfoot_disj_bat : ∀ a, htour.rep.foot tourH tx₀ a →
      a < batchPtr ∨ batchPtr + writeOff₀ + 6 * scan_j.length ≤ a)
    (htfoot_disj_cand : ∀ a, htour.rep.foot tourH tx₀ a → a < candArr ∨ candArr + cands.length ≤ a)
    (htfoot_disj_off : ∀ a, htour.rep.foot tourH tx₀ a → a < offPtr ∨ offPtr + cands.length + 1 ≤ a)
    (htfoot_disj_buf : ∀ a, htour.rep.foot tourH tx₀ a → a < bufPtr ∨ bufPtr + scan_j.length ≤ a)
    (hzero : ZeroFrom st₀.mem h₀)
    (hrep : BundleSlotRepAt eCap prevBase nextBase p bunCap B₀ st₀.mem)
    (heb₀ : ∀ x ∈ edgeEnds B₀.edges, st₀.mem (endBundleBase + endKey x) = B₀.bundleOf x)
    (hG₀ : G₀.applyBatch ops₀ = B₀.graph)
    (hbat : SmallBatchBodyAt st₀.mem (batchPtr + 1) G₀ ops₀ (writeOff₀ - 1)) (hw1 : 1 ≤ writeOff₀)
    (hupd0_eq : updCnt₀ = ops₀.length)
    (hcand_at : ListAt st₀.mem candArr cands)
    (hcsr : CSRAt eCap st₀.mem offPtr bufPtr cands scan_j)
    (hr1 : st₀.regs 1 = tourH) (hr4 : st₀.regs 4 = h₀) (hr6 : st₀.regs 6 = 2 * eCap)
    (hr7 : st₀.regs 7 = p) (hr8 : st₀.regs 8 = bunCap) (hr9 : st₀.regs 9 = endBundleBase)
    (hr10 : st₀.regs 10 = prevBase) (hr11 : st₀.regs 11 = nextBase)
    (hr13 : st₀.regs 13 = offPtr) (hr14 : st₀.regs 14 = bufPtr)
    (hr18 : st₀.regs 18 = candArr) (hr19 : st₀.regs 19 = cands.length)
    (hr20 : st₀.regs 20 = batchPtr) (hr21 : st₀.regs 21 = writeOff₀) (hr22 : st₀.regs 22 = updCnt₀) :
    let finalRes := (cands.map fun b => (b, byRootVRuns B₀ B₀.edges src' b)).foldl runsFoldStep (ops₀, B₀)
    ∃ stEnd cEnd txEnd hEnd totalWords,
      Runs w pProg ω
        (forRange 24 (.const 0) (.reg 19)
          (bundleStepEmitOneCandStmt bDllPush bDllErase bMergeSort bTourOwner))
        st₀ .normal stEnd cEnd ∧
      (∀ r ≤ 22, r ≠ 4 → r ≠ 21 → r ≠ 22 → stEnd.regs r = st₀.regs r) ∧
      stEnd.regs 4 = hEnd ∧ h₀ ≤ hEnd ∧ hEnd ≤ h₀ + (8 + 2 * TS.querySpace) * scan_j.length ∧
      stEnd.regs 21 = totalWords ∧ writeOff₀ ≤ totalWords ∧ totalWords ≤ writeOff₀ + 6 * scan_j.length ∧
      stEnd.regs 22 = finalRes.1.length ∧
      BundleSlotRepAt eCap prevBase nextBase p bunCap finalRes.2 stEnd.mem ∧
      finalRes.2.edges = B₀.edges ∧
      G₀.applyBatch finalRes.1 = finalRes.2.graph ∧
      SmallBatchBodyAt stEnd.mem (batchPtr + 1) G₀ finalRes.1 (totalWords - 1) ∧
      (∀ x ∈ edgeEnds B₀.edges, stEnd.mem (endBundleBase + endKey x) = finalRes.2.bundleOf x) ∧
      htour.rep.rep tourH cord' txEnd stEnd.mem ∧
      (∀ a, htour.rep.foot tourH txEnd a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < hEnd)) ∧
      ZeroFrom stEnd.mem hEnd ∧
      (∀ a, ¬ htour.rep.foot tourH tx₀ a →
        (a < p ∨ p + bundleSlotBlockSize bunCap ≤ a) →
        (∀ x ∈ edgeEnds B₀.edges, a ≠ prevBase + endKey x ∧ a ≠ nextBase + endKey x ∧ a ≠ endBundleBase + endKey x) →
        (a < batchPtr + writeOff₀ ∨ batchPtr + writeOff₀ + 6 * scan_j.length ≤ a) →
        (a < h₀ ∨ hEnd ≤ a) → stEnd.mem a = st₀.mem a) ∧
      cEnd + htour.rep.phi tourH txEnd stEnd.mem ≤
        (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * scan_j.length + 1) + 1) + 920) * scan_j.length +
        429 * cands.length + 7 + htour.rep.phi tourH tx₀ st₀.mem := by
  intro finalRes
  have hE0_lt : ∀ e ∈ B₀.edges, e < eCap := hrep.choose_spec.2.2.1
  have hsum_all : (cands.map fun b => (scan_j.filter fun t => t.1 == b).length).sum = scan_j.length :=
    sum_filter_lengths_eq hcands_nd hscan_in_cands
  have hsum_take : ∀ i ≤ cands.length,
      ((cands.take i).map fun b => (scan_j.filter fun t => t.1 == b).length).sum ≤ scan_j.length := fun i _ => by
    have h := congrArg (fun l => (l.map fun b => (scan_j.filter fun t => t.1 == b).length).sum)
      (List.take_append_drop i cands)
    rw [List.map_append, List.sum_append, hsum_all] at h; omega
  let Acc := ℕ × htour.rep.τ × ℕ × ℕ
  let prefRes : ℕ → List Update × BundleState := fun i =>
    ((cands.take i).map fun b => (b, byRootVRuns B₀ B₀.edges src' b)).foldl runsFoldStep (ops₀, B₀)
  let prefSum : ℕ → ℕ := fun i => ((cands.take i).map fun b => (scan_j.filter fun t => t.1 == b).length).sum
  let Inv : ℕ → Acc → State → Prop := fun i acc st =>
    let (hCur, tx, writeOff, nB) := acc
    let cur := prefRes i
    (∀ r ≤ 22, r ≠ 4 → r ≠ 21 → r ≠ 22 → st.regs r = st₀.regs r) ∧
    st.regs 4 = hCur ∧ st.regs 21 = writeOff ∧ st.regs 22 = cur.1.length ∧ st.regs 24 = i ∧
    h₀ ≤ hCur ∧ hCur ≤ h₀ + (8 + 2 * TS.querySpace) * prefSum i ∧
    writeOff₀ ≤ writeOff ∧ writeOff ≤ writeOff₀ + 6 * prefSum i ∧
    cur.1.length ≤ updCnt₀ + prefSum i ∧
    nB₀ ≤ nB ∧ nB ≤ nB₀ + prefSum i ∧
    cur.2.vertices = Finset.range nB ∧ cur.2.edges = B₀.edges ∧
    (∀ c < nB₀, c ∉ cands.take i → cur.2.ends c = B₀.ends c) ∧
    BundleSlotRepAt eCap prevBase nextBase p bunCap cur.2 st.mem ∧
    G₀.applyBatch cur.1 = cur.2.graph ∧
    SmallBatchBodyAt st.mem (batchPtr + 1) G₀ cur.1 (writeOff - 1) ∧
    (∀ x ∈ edgeEnds B₀.edges, st.mem (endBundleBase + endKey x) = cur.2.bundleOf x) ∧
    htour.rep.rep tourH cord' tx st.mem ∧
    (∀ a, htour.rep.foot tourH tx a → htour.rep.foot tourH tx₀ a ∨ (h₀ ≤ a ∧ a < hCur)) ∧
    ZeroFrom st.mem hCur ∧
    (∀ a, ¬ htour.rep.foot tourH tx₀ a →
      (a < p ∨ p + bundleSlotBlockSize bunCap ≤ a) →
      (∀ x ∈ edgeEnds B₀.edges, a ≠ prevBase + endKey x ∧ a ≠ nextBase + endKey x ∧ a ≠ endBundleBase + endKey x) →
      (a < batchPtr + writeOff₀ ∨ batchPtr + writeOff₀ + 6 * prefSum i ≤ a) →
      (a < h₀ ∨ hCur ≤ a) → st.mem a = st₀.mem a)
  let stepCost : ℕ → ℕ := fun i =>
    (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * scan_j.length + 1) + 1) + 920) *
      (scan_j.filter fun t => t.1 == cands.getD i 0).length + 420
  obtain ⟨stEnd, cEnd, ⟨hEnd, txEnd, totalWords, _⟩, hrunL, hInvEnd, hcL⟩ :=
    runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 24) (lo := .const 0) (hi := .reg 19)
      (body := bundleStepEmitOneCandStmt bDllPush bDllErase bMergeSort bTourOwner)
      (fun acc st => htour.rep.phi tourH acc.2.1 st.mem) Inv stepCost cands.length (by omega)
      (fun _ => by omega) (st₀ := st₀) (a₀ := (h₀, tx₀, writeOff₀, nB₀))
      (by
        refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], ?_, rfl⟩
        refine ⟨fun r hr _ _ _ => by simp [show r ≠ 24 by omega], by simp [hr4], by simp [hr21],
          by simp [prefRes, hr22, hupd0_eq], by simp, le_refl _, by simp [prefSum],
          le_refl _, by simp [prefSum], by simp [prefRes, prefSum, hupd0_eq], le_refl _, by simp [prefSum],
          hV₀, rfl, fun _ _ _ => rfl, hrep, hG₀, hbat, heb₀, htrep, fun _ h => Or.inl h,
          hzero, fun _ _ _ _ _ _ => rfl⟩)
      (fun _ _ _ _ hI => hI.2.2.2.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, hI.1 19 (by decide) (by decide) (by decide) (by decide), hr19])
      (fun i ⟨hCur, tx, writeOff, nB⟩ st hi hI => by
        rcases hI with ⟨hregs, hr4c, hr21c, hr22c, hr24c, hh0_le, hhCur_le, hwo_le, hwo_hi, hupd_hi,
          hnB0_le, hnB_hi, hVc, hEc, hother_c, hrepc, hGc, hbatc, hebc, htrc, htfc, hzfc, hfrc⟩
        set b := cands[i]'hi
        set m_b := (scan_j.filter fun t => t.1 == b).length
        have hb_mem : b ∈ cands := List.getElem_mem hi
        have hb_lt0 : b < nB₀ := hcands_lt b hb_mem
        have hb_not_take : b ∉ cands.take i := fun hm => by
          obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hm
          rw [List.length_take, Nat.min_eq_left (by omega)] at hj
          rw [List.getElem_take] at hjb
          have heq : j = i := (List.Nodup.getElem_inj_iff hcands_nd).mp hjb
          omega
        have hends_b_eq : (prefRes i).2.ends b = B₀.ends b := hother_c b hb_lt0 hb_not_take
        have hps_succ : prefSum (i + 1) = prefSum i + m_b := by
          simp only [prefSum, List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]; simp [b, m_b]
        have hps_le : prefSum (i + 1) ≤ scan_j.length := hsum_take (i + 1) (by omega)
        have hmb_le : m_b ≤ scan_j.length := by omega
        have hmem_pres : ∀ a, ¬ htour.rep.foot tourH tx₀ a →
            (a < p ∨ p + bundleSlotBlockSize bunCap ≤ a) →
            (a < prevBase ∨ prevBase + 2 * eCap ≤ a) →
            (a < nextBase ∨ nextBase + 2 * eCap ≤ a) →
            (a < endBundleBase ∨ endBundleBase + 2 * eCap ≤ a) →
            (a < batchPtr + writeOff₀ ∨ batchPtr + writeOff₀ + 6 * scan_j.length ≤ a) →
            a < h₀ → st.mem a = st₀.mem a := fun a hnf haB haP haN haE haBat ha0 =>
          hfrc a hnf haB (fun x hx => by
            have hxk : endKey x < 2 * eCap := by
              have := hE0_lt x.1 ((mem_edgeEnds _ _).mp hx)
              rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
            exact ⟨by omega, by omega, by omega⟩) (by omega) (Or.inl ha0)
        have hcand_eq : st.mem (candArr + i) = b := by
          rw [hmem_pres (candArr + i)
            (fun hf => by have := htfoot_disj_cand _ hf; clear * - this hi; omega)
            (by clear * - hcand_blk hi; omega)
            (by clear * - hcand_prev hi; omega)
            (by clear * - hcand_next hi; omega)
            (by clear * - hcand_eb hi; omega)
            (by clear * - hcand_bat hi; omega)
            (by clear * - hcand_h hi; omega)]
          exact hcand_at i hi
        have hlo_eq : st.mem (offPtr + i) = prefSum i := by
          rw [hmem_pres (offPtr + i)
            (fun hf => by have := htfoot_disj_off _ hf; clear * - this hi; omega)
            (by clear * - hoff_blk hi; omega)
            (by clear * - hoff_prev hi; omega)
            (by clear * - hoff_next hi; omega)
            (by clear * - hoff_eb hi; omega)
            (by clear * - hoff_bat hi; omega)
            (by clear * - hoff_h hi; omega)]
          exact hcsr.1 i (by omega)
        have hhi_eq : st.mem (offPtr + (i + 1)) = prefSum i + m_b := by
          rw [hmem_pres (offPtr + (i + 1))
            (fun hf => by have := htfoot_disj_off _ hf; clear * - this hi; omega)
            (by clear * - hoff_blk hi; omega)
            (by clear * - hoff_prev hi; omega)
            (by clear * - hoff_next hi; omega)
            (by clear * - hoff_eb hi; omega)
            (by clear * - hoff_bat hi; omega)
            (by clear * - hoff_h hi; omega), ← hps_succ]
          exact hcsr.1 (i + 1) (by omega)
        obtain ⟨L_perm, hperm, hbuf0⟩ := hcsr.2 i hi
        rw [hcsr.1 i (by omega)] at hbuf0
        have hLperm_len : L_perm.length = m_b := by rw [hperm.length_eq, List.length_map]
        have hbuf_at : ListAt st.mem (bufPtr + prefSum i) L_perm := fun t ht => by
          have ht_m : t < m_b := hLperm_len ▸ ht
          rw [hmem_pres (bufPtr + prefSum i + t)
            (fun hf => by have := htfoot_disj_buf _ hf; clear * - this hps_succ hps_le ht_m; omega)
            (by clear * - hbuf_blk hps_succ hps_le ht_m; omega)
            (by clear * - hbuf_prev hps_succ hps_le ht_m; omega)
            (by clear * - hbuf_next hps_succ hps_le ht_m; omega)
            (by clear * - hbuf_eb hps_succ hps_le ht_m; omega)
            (by clear * - hbuf_bat hps_succ hps_le ht_m; omega)
            (by clear * - hbuf_h hps_succ hps_le ht_m; omega)]
          exact hbuf0 t ht
        have hmul_split : (8 + 2 * TS.querySpace) * prefSum i + (8 + 2 * TS.querySpace) * m_b =
            (8 + 2 * TS.querySpace) * prefSum (i + 1) := by rw [hps_succ, Nat.mul_add]
        have hsp_le : (8 + 2 * TS.querySpace) * prefSum (i + 1) ≤ (8 + 2 * TS.querySpace) * scan_j.length :=
          Nat.mul_le_mul_left _ hps_le
        obtain ⟨st1, c1, tx1, h1, addedWords, hrun1, hregs1, hr4_1, hh1_lo, hh1_hi, hr21_1, hr22_1,
          haddW_le, haddU_le, hV1, hrep1, hG1, hbat1, heb1_b, htr1, htf1, hzf1, hfr1, hc1⟩ :=
          bundleStepEmitOneCand_runs (htour := htour) (ω := ω) (st₀ := st)
            (b := b) (nB := nB) (candIdx := i) (offPtr := offPtr) (bufPtr := bufPtr) (lo := prefSum i)
            (ops := (prefRes i).1) (B := (prefRes i).2) (B_init := B₀)
            (candSet_j := candSet_j) (scan_j := scan_j) (L_perm := L_perm)
            hpPush hpErase hMergeSort hw16 htourH_w heCap_w hpk_w hprev_w hnext_w heb_w hp_w
            (by clear * - hcand_w hi; omega) (by clear * - hoff_w hi; omega)
            (by change bufPtr + prefSum i + m_b < 2 ^ w; clear * - hbuf_w hps_succ hps_le; omega)
            (by change bufPtr + prefSum i + m_b ≤ hCur; clear * - hbuf_h hh0_le hps_succ hps_le; omega)
            (by change batchPtr + writeOff + 6 * m_b < 2 ^ w; clear * - hbat_w hwo_hi hps_succ hps_le; omega)
            (by change (prefRes i).1.length + m_b < 2 ^ w; clear * - hupd_w hupd_hi hps_succ hps_le; omega)
            (by change hCur + (8 + 2 * TS.querySpace) * m_b < 2 ^ w; clear * - hh_w hhCur_le hmul_split hsp_le; omega)
            hVc (by clear * - hb_lt0 hnB0_le; omega)
            (by change nB + m_b ≤ bunCap; clear * - hnb_cap hnB_hi hps_succ hps_le; omega)
            hEc hends_b_eq hval (hcands_in_set b hb_mem)
            (fun x hx => hsrc_lt x ((mem_edgeEnds _ _).mpr (by rw [← hEc]; exact ((BundleState.mem_ends _ _ _).mp hx).1)))
            (fun x hx => hsrc_mem x ((mem_edgeEnds _ _).mpr (by rw [← hEc]; exact ((BundleState.mem_ends _ _ _).mp hx).1)))
            (fun x hx => hsrc_uniq x ((mem_edgeEnds _ _).mpr (by rw [← hEc]; exact ((BundleState.mem_ends _ _ _).mp hx).1)))
            hprev_next hblk_prev hblk_next heb_prev heb_next heb_blk
            (by change batchPtr + writeOff + 6 * m_b ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ batchPtr; clear * - hbat_blk hwo_hi hps_succ hps_le; omega)
            (by change batchPtr + writeOff + 6 * m_b ≤ prevBase ∨ prevBase + 2 * eCap ≤ batchPtr; clear * - hbat_prev hwo_hi hps_succ hps_le; omega)
            (by change batchPtr + writeOff + 6 * m_b ≤ nextBase ∨ nextBase + 2 * eCap ≤ batchPtr; clear * - hbat_next hwo_hi hps_succ hps_le; omega)
            (by change batchPtr + writeOff + 6 * m_b ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ batchPtr; clear * - hbat_eb hwo_hi hps_succ hps_le; omega)
            (by change batchPtr + writeOff + 6 * m_b ≤ hCur; clear * - hbat_h hh0_le hwo_hi hps_succ hps_le; omega)
            (by clear * - hh_blk hh0_le; omega) (by clear * - hh_prev hh0_le; omega)
            (by clear * - hh_next hh0_le; omega) (by clear * - hh_eb hh0_le; omega)
            htrc (fun a ha => by rcases htfc a ha with h0 | ⟨_, h2⟩; exact lt_of_lt_of_le (htfoot_lt a h0) hh0_le; exact h2)
            (fun a ha => by rcases htfc a ha with h0 | ⟨h1, _⟩; exact htfoot_disj_blk a h0; right; omega)
            (fun a ha => by rcases htfc a ha with h0 | ⟨h1, _⟩; exact htfoot_disj_prev a h0; right; omega)
            (fun a ha => by rcases htfc a ha with h0 | ⟨h1, _⟩; exact htfoot_disj_next a h0; right; omega)
            (fun a ha => by rcases htfc a ha with h0 | ⟨h1, _⟩; exact htfoot_disj_eb a h0; right; omega)
            (fun a ha => by
              change a < batchPtr ∨ batchPtr + writeOff + 6 * m_b ≤ a
              rcases htfc a ha with h0 | ⟨h1, _⟩
              · have := htfoot_disj_bat a h0; clear * - this hwo_hi hps_succ hps_le; omega
              · right; clear * - hbat_h hwo_hi hps_succ hps_le h1; omega)
            hzfc hrepc hGc hbatc (by omega) hcand_eq hlo_eq hhi_eq hperm hbuf_at
            ((hregs 1 (by decide) (by decide) (by decide) (by decide)).trans hr1) hr4c
            ((hregs 6 (by decide) (by decide) (by decide) (by decide)).trans hr6)
            ((hregs 7 (by decide) (by decide) (by decide) (by decide)).trans hr7)
            ((hregs 8 (by decide) (by decide) (by decide) (by decide)).trans hr8)
            ((hregs 9 (by decide) (by decide) (by decide) (by decide)).trans hr9)
            ((hregs 10 (by decide) (by decide) (by decide) (by decide)).trans hr10)
            ((hregs 11 (by decide) (by decide) (by decide) (by decide)).trans hr11)
            ((hregs 13 (by decide) (by decide) (by decide) (by decide)).trans hr13)
            ((hregs 14 (by decide) (by decide) (by decide) (by decide)).trans hr14)
            ((hregs 18 (by decide) (by decide) (by decide) (by decide)).trans hr18)
            ((hregs 20 (by decide) (by decide) (by decide) (by decide)).trans hr20)
            hr21c hr22c hr24c
        have hvruns_eq : byRootVRuns (prefRes i).2 (prefRes i).2.edges src' b =
            byRootVRuns B₀ B₀.edges src' b := by
          have hsurv_eq : survivingEnds (prefRes i).2 (prefRes i).2.edges b = survivingEnds B₀ B₀.edges b := by
            ext x; simp only [survivingEnds, Finset.mem_filter, hends_b_eq, hEc]
          simp only [byRootVRuns, rawByRootVRuns, finalRootsOf, hsurv_eq]
        have hpref_succ : prefRes (i + 1) = runsFoldStep (prefRes i) (b, byRootVRuns (prefRes i).2 (prefRes i).2.edges src' b) := by
          simp only [prefRes, List.take_succ_eq_append_getElem hi, List.map_append, List.foldl_append,
            List.map_singleton, List.foldl_cons, List.foldl_nil, hvruns_eq, b]
        have hbo_lt_c : ∀ x ∈ edgeEnds (prefRes i).2.edges, (prefRes i).2.bundleOf x < nB := by
          have hV' := hrepc.choose_spec.1
          have heq : hrepc.choose = nB := by
            have := congrArg Finset.card (hV'.symm.trans hVc); simpa [Finset.card_range] using this
          rw [← heq]; exact hrepc.choose_spec.2.2.2.1
        obtain ⟨_, hE1_eq, hpres_ne, hother1⟩ := runsFoldStep_other_ends (ops := (prefRes i).1)
          (b := b) (src' := src') hVc (by omega) hbo_lt_c
        have hlen1 : (prefRes (i + 1)).1.length = (prefRes i).1.length + ((byRootVRuns (prefRes i).2 (prefRes i).2.edges src' b).drop 1).length := by
          rw [hpref_succ]; simp [runsFoldStep, bundleSplitFoldStep, bundleRunUpdates]
        change h1 ≤ hCur + (8 + 2 * TS.querySpace) * m_b at hh1_hi
        change addedWords ≤ 6 * m_b at haddW_le
        change ((byRootVRuns (prefRes i).2 (prefRes i).2.edges src' b).drop 1).length ≤ m_b at haddU_le
        change c1 + htour.rep.phi tourH tx1 st1.mem ≤
          (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * m_b + 1) + 1) + 920) * m_b + 420 +
          htour.rep.phi tourH tx st.mem at hc1
        rw [← hpref_succ] at hV1 hrep1 hG1 hbat1 heb1_b hE1_eq hpres_ne hother1
        refine ⟨st1, c1, (h1, tx1, writeOff + addedWords,
            nB + ((byRootVRuns (prefRes i).2 (prefRes i).2.edges src' b).drop 1).length),
          hrun1, (hregs1 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr24c, ?_, rfl, ?_⟩
        · refine ⟨fun r hr h4 h21 h22 => by
              simp only [Function.update_of_ne (show r ≠ 24 by omega)]
              exact (hregs1 r (by omega) h4 h21 h22 (by omega)).trans (hregs r hr h4 h21 h22),
            by simp [hr4_1], by simp [hr21_1], by simp [hr22_1, hlen1], by simp,
            by clear * - hh0_le hh1_lo; omega, by clear * - hhCur_le hh1_hi hmul_split; omega,
            by clear * - hwo_le; omega, by clear * - hwo_hi haddW_le hps_succ; omega,
            by clear * - hlen1 hupd_hi haddU_le hps_succ; omega,
            by clear * - hnB0_le; omega, by clear * - hnB_hi haddU_le hps_succ; omega,
            hV1, hE1_eq.trans hEc, ?_, hrep1, hG1, hbat1, ?_, htr1,
            fun a ha => by
              rcases htf1 a ha with h0 | ⟨h_1, h_2⟩
              · rcases htfc a h0 with h00 | ⟨h_1, h_2⟩; exact Or.inl h00; exact Or.inr ⟨h_1, by omega⟩
              · exact Or.inr ⟨by omega, h_2⟩,
            hzf1, ?_⟩
          · intro c hc hnot
            have hcb : c ≠ b := fun heq => hnot (by
              subst heq; rw [List.take_succ_eq_append_getElem hi]; exact List.mem_append_right _ List.mem_cons_self)
            have hnot_i : c ∉ cands.take i := fun hm => hnot (by
              rw [List.take_succ_eq_append_getElem hi]; exact List.mem_append_left _ hm)
            exact (hother1 c (by omega) hcb).trans (hother_c c hc hnot_i)
          · intro x hx
            have hx_c : x ∈ edgeEnds (prefRes i).2.edges := hEc.symm ▸ hx
            by_cases hxb : (prefRes i).2.bundleOf x = b
            · have hx_end : x ∈ (prefRes i).2.ends b := (BundleState.mem_ends _ _ _).mpr ⟨(mem_edgeEnds _ _).mp hx_c, hxb⟩
              rcases heb1_b x hx_end with hEq | ⟨hbo_b, hmem_eq⟩
              · exact hEq
              · rw [hmem_eq, hebc x hx, hxb, hbo_b]
            · have hxk : endKey x < 2 * eCap := by
                have := hE0_lt x.1 ((mem_edgeEnds _ _).mp hx)
                rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
              have hmem_eq : st1.mem (endBundleBase + endKey x) = st.mem (endBundleBase + endKey x) :=
                hfr1 _ (fun hf => by
                  rcases htfc _ hf with h0 | ⟨h_1, _⟩
                  · have := htfoot_disj_eb _ h0; omega
                  · omega)
                  (by unfold bundleSlotBlockSize at heb_blk ⊢; clear * - heb_blk hxk; omega)
                  (fun y hy => by
                    have hyk : endKey y < 2 * eCap := by
                      have := hE0_lt y.1 (by rw [← hEc]; exact ((BundleState.mem_ends _ _ _).mp hy).1)
                      rcases y with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
                    refine ⟨by clear * - heb_prev hxk hyk; omega, by clear * - heb_next hxk hyk; omega, fun heq => ?_⟩
                    have : x = y := endKey_injective (by omega)
                    subst this; exact hxb ((BundleState.mem_ends _ _ _).mp hy).2)
                  (by clear * - hbat_eb hwo_hi hps_succ hps_le hxk; omega)
                  (Or.inl (by omega))
              rw [hmem_eq, hebc x hx, hpres_ne x hx_c hxb]
          · intro a hnf haBlk haE haBat haH
            rw [hfr1 a (fun hf => by
                rcases htfc a hf with h0 | ⟨h_1, h_2⟩
                · exact hnf h0
                · omega)
              haBlk (fun x hx => haE x ((mem_edgeEnds _ _).mpr (by rw [← hEc]; exact ((BundleState.mem_ends _ _ _).mp hx).1)))
              (by omega) (by omega)]
            exact hfrc a hnf haBlk haE (by omega) (by omega)
        · have hlog_le : Nat.log 2 (2 * m_b + 1) ≤ Nat.log 2 (2 * scan_j.length + 1) :=
            Nat.log_mono_right (by omega)
          have hget : cands.getD i 0 = b := List.getD_eq_getElem cands 0 hi
          have hmul_le : (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * m_b + 1) + 1) + 920) * m_b ≤
              (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * scan_j.length + 1) + 1) + 920) * m_b :=
            Nat.mul_le_mul_right _ (by omega)
          dsimp only [stepCost]; rw [hget]; change c1 + htour.rep.phi tourH tx1 st1.mem ≤
            (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * scan_j.length + 1) + 1) + 920) * m_b + 420 +
            htour.rep.phi tourH tx st.mem
          exact le_trans hc1 (Nat.add_le_add_right (Nat.add_le_add_right hmul_le 420) _))
  have hrc_eq : rangeCost stepCost 0 cands.length =
      (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * scan_j.length + 1) + 1) + 920) * scan_j.length +
      420 * cands.length := by
    have := rangeCost_cands_eq
      (2 * TS.mul * ordStoreLog eCap + 600 * (Nat.log 2 (2 * scan_j.length + 1) + 1) + 920)
      (fun b => (scan_j.filter fun t => t.1 == b).length) cands
    rwa [hsum_all] at this
  have hpref_full : prefRes cands.length = finalRes :=
    congrArg (fun l => (l.map fun b => (b, byRootVRuns B₀ B₀.edges src' b)).foldl runsFoldStep (ops₀, B₀)) List.take_length
  have hps_full : prefSum cands.length = scan_j.length := by
    rw [← hsum_all]; exact congrArg (fun l => (l.map fun b => (scan_j.filter fun t => t.1 == b).length).sum) List.take_length
  rcases hInvEnd with ⟨hregsE, hr4E, hr21E, hr22E, _, hh0E, hhHiE, hwoLoE, hwoHiE, _, _, _, _,
    hEE, _, hrepE, hGE, hbatE, hebE, htrE, htfE, hzfE, hfrE⟩
  rw [hpref_full] at hr22E hEE hrepE hGE hbatE hebE
  rw [hps_full] at hhHiE hwoHiE hfrE
  refine ⟨stEnd, cEnd, txEnd, hEnd, totalWords, hrunL, hregsE, hr4E, hh0E, hhHiE,
    hr21E, hwoLoE, hwoHiE, hr22E, hrepE, hEE, hGE, hbatE, hebE, htrE, htfE, hzfE, hfrE, ?_⟩
  rw [hrc_eq] at hcL; simp only [Expr.size] at hcL; clear * - hcL; omega

/-- Post-emission table-state update lemma: given `BundleTableEmitState` before emitting slot `s`
and the updated slot-`s` representation, cleared scratch flags/heads, and memory preservation on
all other cells of `bundleTableFoot`, produces `BundleTableEmitState` with `s` erased from
`remTouched` and slot `s` replaced by `B_new`. -/
lemma bundleStepEmitSlot_postEmit {slotCap vCap eCap tbl s p bunCap : ℕ}
    {S₀ S_cur : BundleTableState slotCap} {D : Finset ℕ} {m : BundleTableMeta slotCap}
    {candSet : Fin slotCap → Finset ℕ} {remTouched : List ℕ}
    {B₀ B_new : BundleState} {mem₀ mem' : ℕ → ℕ}
    (hs_mem : s ∈ remTouched) (hs_lt : s < slotCap)
    (hS₀s : S₀ ⟨s, hs_lt⟩ = some B₀)
    (hblks : m.slotBlocks ⟨s, hs_lt⟩ = some (p, bunCap))
    (hemit : BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet S_cur remTouched mem₀)
    (hED : B_new.edges = B₀.edges \ D)
    (hrepEnd : BundleSlotRepAt eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
      p bunCap B_new mem')
    (hebEnd : ∀ x ∈ edgeEnds (B₀.edges \ D),
      mem' (btEndBundleBase tbl slotCap eCap + endKey x) = B_new.bundleOf x)
    (htch0 : mem' (btSlotTouchedBase tbl slotCap eCap + s) = 0)
    (hdelH0 : mem' (btSlotDelHeadBase tbl slotCap eCap + s) = 0)
    (hdL0 : ∀ e ∈ B₀.edges ∩ D, mem' (btSlotDelNextBase tbl slotCap eCap + e) = 0)
    (hcandH0 : mem' (btSlotCandHeadBase tbl slotCap eCap + s) = 0)
    (htbl_unch : ∀ a, bundleTableFoot eCap tbl m a →
      a ≠ btSlotTouchedBase tbl slotCap eCap + s →
      a ≠ btSlotDelHeadBase tbl slotCap eCap + s →
      (∀ e ∈ B₀.edges ∩ D, a ≠ btSlotDelNextBase tbl slotCap eCap + e) →
      a ≠ btSlotCandHeadBase tbl slotCap eCap + s →
      a ≠ btCurBunBase tbl slotCap eCap + s →
      a ≠ btCurTagBase tbl slotCap eCap + s →
      (a < p ∨ p + bundleSlotBlockSize bunCap ≤ a) →
      (∀ x ∈ edgeEnds (B₀.edges \ D),
        a ≠ btEndPrevBase tbl slotCap eCap + endKey x ∧
        a ≠ btEndNextBase tbl slotCap eCap + endKey x ∧
        a ≠ btEndBundleBase tbl slotCap eCap + endKey x) →
      mem' a = mem₀ a) :
    BundleTableEmitState slotCap vCap eCap tbl S₀ D m candSet
      (Function.update S_cur ⟨s, hs_lt⟩ (some B_new)) (remTouched.erase s) mem' := by
  set js : Fin slotCap := ⟨s, hs_lt⟩
  set B_del : BundleState := { B₀ with edges := B₀.edges \ D }
  set S_next : BundleTableState slotCap := Function.update S_cur js (some B_new)
  rcases hemit with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11,
    hdisj₀, hdisjC, hS_rel, hedSlot, hendB, hslots, hdisjB, hndT, hltT, htouch, hdel, hdelN0⟩
  have hS_js : S_cur js = some B_del := by
    have hr := hS_rel js; rw [hS₀s] at hr
    cases hSc : S_cur js with
    | none => rw [hSc] at hr; exact False.elim hr
    | some Bc => rw [hSc] at hr; congr 1; exact hr.2 hs_mem
  have hslot_js := hslots js; rw [hS_js, hblks] at hslot_js; simp only [js, hs_mem, ↓reduceIte] at hslot_js
  obtain ⟨hp_mem, hp_disj_tbl, hrepCand_js⟩ := hslot_js
  obtain ⟨_, _, _, hE₀_lt, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hrepCand_js
  have hdel_js := hdel js; rw [hS₀s] at hdel_js; simp only [js, hs_mem, ↓reduceIte] at hdel_js
  obtain ⟨dL, hdL_sll, hdL_mem⟩ := hdel_js
  have hD_lt : ∀ e ∈ B₀.edges ∩ D, e < eCap := fun e he => hdL_sll.mem_lt e ((hdL_mem e).mpr he)
  have hend_lt : ∀ x ∈ edgeEnds (B₀.edges \ D), endKey x < 2 * eCap := fun x hx => by
    have := hE₀_lt x.1 ((mem_edgeEnds _ _).mp hx)
    rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
  have hnot_er : s ∉ remTouched.erase s := hndT.not_mem_erase
  have hp_disj_tbl' : p + bundleSlotBlockSize bunCap ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ p := hp_disj_tbl
  have hhdr_eq : ∀ off < 12, mem' (tbl + off) = mem₀ (tbl + off) := fun off hoff =>
    htbl_unch (tbl + off) (btHeader_in_foot hoff)
      (by unfold btSlotTouchedBase; omega) (by unfold btSlotDelHeadBase; omega)
      (fun e _ => by unfold btSlotDelNextBase; omega) (by unfold btSlotCandHeadBase; omega)
      (by unfold btCurBunBase; omega) (by unfold btCurTagBase; omega)
      (by omega)
      (fun _ _ => ⟨by unfold btEndPrevBase; omega, by unfold btEndNextBase; omega, by unfold btEndBundleBase; omega⟩)
  refine ⟨(hhdr_eq 0 (by decide)).trans hr0, (hhdr_eq 1 (by decide)).trans hr1,
    (hhdr_eq 2 (by decide)).trans hr2, (hhdr_eq 3 (by decide)).trans hr3,
    (hhdr_eq 4 (by decide)).trans hr4, (hhdr_eq 5 (by decide)).trans hr5,
    (hhdr_eq 6 (by decide)).trans hr6, (hhdr_eq 7 (by decide)).trans hr7,
    (hhdr_eq 8 (by decide)).trans hr8, (hhdr_eq 9 (by decide)).trans hr9,
    (hhdr_eq 10 (by decide)).trans hr10, (hhdr_eq 11 (by decide)).trans hr11, hdisj₀, ?_, ?_, ?_, ?_, ?_,
    hdisjB, hndT.erase s, fun s' hs' => hltT s' (List.mem_of_mem_erase hs'), ?_, ?_, ?_⟩
  · intro j₁ j₂ hne B₁ B₂ h1 h2
    by_cases hj1 : j₁ = js
    · subst hj1; simp only [S_next, Function.update_self, Option.some.injEq] at h1; subst h1
      simp only [S_next, Function.update_of_ne hne.symm] at h2
      rw [hED]; exact hdisjC js j₂ hne B_del B₂ hS_js h2
    · simp only [S_next, Function.update_of_ne hj1] at h1
      by_cases hj2 : j₂ = js
      · subst hj2; simp only [S_next, Function.update_self, Option.some.injEq] at h2; subst h2
        rw [hED]; exact hdisjC j₁ js hne B₁ B_del h1 hS_js
      · simp only [S_next, Function.update_of_ne hj2] at h2; exact hdisjC j₁ j₂ hne B₁ B₂ h1 h2
  · intro j
    by_cases hj : j = js
    · subst hj; rw [hS₀s]; simp only [S_next, Function.update_self]
      exact ⟨hED, fun hm => False.elim (hnot_er hm)⟩
    · simp only [S_next, Function.update_of_ne hj]
      have hr := hS_rel j
      cases hS0 : S₀ j <;> cases hSc : S_cur j <;> simp only [hS0, hSc] at hr ⊢
      exact ⟨hr.1, fun hm => hr.2 (List.mem_of_mem_erase hm)⟩
  · intro e he
    have hes_eq : mem' (btEdgeSlotBase tbl slotCap + e) = mem₀ (btEdgeSlotBase tbl slotCap + e) :=
      htbl_unch _ (btEdgeSlot_in_foot he)
        (by unfold btEdgeSlotBase btSlotTouchedBase; omega)
        (by unfold btEdgeSlotBase btSlotDelHeadBase; omega)
        (fun _ _ => by unfold btEdgeSlotBase btSlotDelNextBase; omega)
        (by unfold btEdgeSlotBase btSlotCandHeadBase; omega)
        (by unfold btEdgeSlotBase btCurBunBase; omega)
        (by unfold btEdgeSlotBase btCurTagBase; omega)
        (by unfold btEdgeSlotBase; omega)
        (fun _ _ => ⟨by unfold btEdgeSlotBase btEndPrevBase; omega,
          by unfold btEdgeSlotBase btEndNextBase; omega, by unfold btEdgeSlotBase btEndBundleBase; omega⟩)
    rw [hes_eq]
    refine ⟨fun j B hSj heB => ?_, fun hnone => ?_⟩
    · by_cases hj : j = js
      · subst hj; simp only [S_next, Function.update_self, Option.some.injEq] at hSj; subst hSj
        exact (hedSlot e he).1 js B_del hS_js (show e ∈ B_del.edges by change e ∈ B₀.edges \ D; rwa [← hED])
      · simp only [S_next, Function.update_of_ne hj] at hSj; exact (hedSlot e he).1 j B hSj heB
    · refine (hedSlot e he).2 fun j B hSj heB => ?_
      by_cases hj : j = js
      · subst hj; rw [hS_js] at hSj; cases hSj
        exact hnone js B_new (by simp [S_next]) (show e ∈ B_new.edges by rw [hED]; exact heB)
      · exact hnone j B (by simp [S_next, Function.update_of_ne hj, hSj]) heB
  · intro j B hSj x hx
    by_cases hj : j = js
    · subst hj; simp only [S_next, Function.update_self, Option.some.injEq] at hSj; subst hSj
      exact hebEnd x (hED ▸ hx)
    · simp only [S_next, Function.update_of_ne hj] at hSj
      have hdisj_j : Disjoint B.edges B_del.edges := hdisjC j js hj B B_del hSj hS_js
      have hxE : x.1 ∈ B.edges := (mem_edgeEnds _ _).mp hx
      have hxk : endKey x < 2 * eCap := by
        have hsj := hslots j; rw [hSj] at hsj
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hsj; exact False.elim hsj
        | some pb =>
          rw [hm] at hsj
          have he_lt : x.1 < eCap := by
            split_ifs at hsj
            · exact hsj.2.2.choose_spec.2.2.1 x.1 hxE
            · exact hsj.2.2.1.choose_spec.2.2.1 x.1 hxE
          rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
      rw [htbl_unch _ (btEndBundle_in_foot hxk)
        (by unfold btEndBundleBase btSlotTouchedBase; omega)
        (by unfold btEndBundleBase btSlotDelHeadBase; omega)
        (fun _ _ => by unfold btEndBundleBase btSlotDelNextBase; omega)
        (by unfold btEndBundleBase btSlotCandHeadBase; omega)
        (by unfold btEndBundleBase btCurBunBase; omega)
        (by unfold btEndBundleBase btCurTagBase; omega)
        (by unfold btEndBundleBase; omega)
        (fun y hy => ⟨by unfold btEndBundleBase btEndPrevBase; omega,
          by unfold btEndBundleBase btEndNextBase; omega, fun heq => by
            have hxy : x = y := endKey_injective (by omega)
            subst hxy; exact Finset.disjoint_left.mp hdisj_j hxE ((mem_edgeEnds _ _).mp hy)⟩)]
      exact hendB j B hSj x hx
  · intro j
    by_cases hj : j = js
    · subst hj; simp only [S_next, Function.update_self, hblks, js, hnot_er, ↓reduceIte]
      have hp_eq : mem' (btSlotPtrBase tbl + s) = p :=
        (htbl_unch _ (btSlotPtr_in_foot hs_lt)
          (by unfold btSlotPtrBase btSlotTouchedBase; omega)
          (by unfold btSlotPtrBase btSlotDelHeadBase; omega)
          (fun _ _ => by unfold btSlotPtrBase btSlotDelNextBase; omega)
          (by unfold btSlotPtrBase btSlotCandHeadBase; omega)
          (by unfold btSlotPtrBase btCurBunBase; omega)
          (by unfold btSlotPtrBase btCurTagBase; omega)
          (by unfold btSlotPtrBase; omega)
          (fun _ _ => ⟨by unfold btSlotPtrBase btEndPrevBase; omega,
            by unfold btSlotPtrBase btEndNextBase; omega, by unfold btSlotPtrBase btEndBundleBase; omega⟩)).trans hp_mem
      exact ⟨hp_eq, hp_disj_tbl, hrepEnd, hcandH0⟩
    · simp only [S_next, Function.update_of_ne hj]
      have hsj := hslots j
      have hne_s : j.1 ≠ s := fun h => hj (Fin.ext h)
      have herase_iff : j.1 ∈ remTouched.erase s ↔ j.1 ∈ remTouched := List.mem_erase_of_ne hne_s
      have hptr_eq : mem' (btSlotPtrBase tbl + j.1) = mem₀ (btSlotPtrBase tbl + j.1) :=
        htbl_unch _ (btSlotPtr_in_foot j.2)
          (by unfold btSlotPtrBase btSlotTouchedBase; omega)
          (by unfold btSlotPtrBase btSlotDelHeadBase; omega)
          (fun _ _ => by unfold btSlotPtrBase btSlotDelNextBase; omega)
          (by unfold btSlotPtrBase btSlotCandHeadBase; omega)
          (by unfold btSlotPtrBase btCurBunBase; omega)
          (by unfold btSlotPtrBase btCurTagBase; omega)
          (by unfold btSlotPtrBase; omega)
          (fun _ _ => ⟨by unfold btSlotPtrBase btEndPrevBase; omega,
            by unfold btSlotPtrBase btEndNextBase; omega, by unfold btSlotPtrBase btEndBundleBase; omega⟩)
      have hch_eq : mem' (btSlotCandHeadBase tbl slotCap eCap + j.1) =
          mem₀ (btSlotCandHeadBase tbl slotCap eCap + j.1) :=
        htbl_unch _ (btSlotCandHead_in_foot j.2)
          (by unfold btSlotCandHeadBase btSlotTouchedBase; omega)
          (by unfold btSlotCandHeadBase btSlotDelHeadBase; omega)
          (fun e' he' => by have := hD_lt e' he'; unfold btSlotCandHeadBase btSlotDelNextBase; omega)
          (by omega)
          (by unfold btSlotCandHeadBase btCurBunBase; omega)
          (by unfold btSlotCandHeadBase btCurTagBase; omega)
          (by unfold btSlotCandHeadBase; omega)
          (fun x hx => by have := hend_lt x hx; exact ⟨by unfold btSlotCandHeadBase btEndPrevBase; omega,
            by unfold btSlotCandHeadBase btEndNextBase; omega, by unfold btSlotCandHeadBase btEndBundleBase; omega⟩)
      cases hSc : S_cur j with
      | none =>
        rw [hSc] at hsj
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hsj; exact ⟨hptr_eq.trans hsj.1, hch_eq.trans hsj.2.1, fun h => hsj.2.2 (herase_iff.mp h)⟩
        | some _ => rw [hm] at hsj; exact False.elim hsj
      | some B =>
        rw [hSc] at hsj
        cases hm : m.slotBlocks j with
        | none => rw [hm] at hsj; exact False.elim hsj
        | some pb =>
          rcases pb with ⟨q, qCap⟩; rw [hm] at hsj
          have hq_disj_p := hdisjB j js hj q qCap p bunCap hm hblks
          have hdisj_j : Disjoint B.edges B_del.edges := hdisjC j js hj B B_del hSc hS_js
          have hq_mem : ∀ a, q ≤ a → a < q + bundleSlotBlockSize qCap → mem' a = mem₀ a := fun a h1 h2 =>
            htbl_unch a (Or.inr ⟨j, q, qCap, hm, h1, h2⟩)
              (by have hqd := hsj.2.1; unfold bundleTableFixedSize at hqd; unfold btSlotTouchedBase; omega)
              (by have hqd := hsj.2.1; unfold bundleTableFixedSize at hqd; unfold btSlotDelHeadBase; omega)
              (fun e' he' => by have hqd := hsj.2.1; have he'lt := hD_lt e' he'; unfold bundleTableFixedSize at hqd; unfold btSlotDelNextBase; omega)
              (by have hqd := hsj.2.1; unfold bundleTableFixedSize at hqd; unfold btSlotCandHeadBase; omega)
              (by have hqd := hsj.2.1; unfold bundleTableFixedSize at hqd; unfold btCurBunBase; omega)
              (by have hqd := hsj.2.1; unfold bundleTableFixedSize at hqd; unfold btCurTagBase; omega)
              (by omega)
              (fun x hx => by
                have hxk := hend_lt x hx; have hqd := hsj.2.1
                exact ⟨by unfold bundleTableFixedSize at hqd; unfold btEndPrevBase; omega,
                  by unfold bundleTableFixedSize at hqd; unfold btEndNextBase; omega,
                  by unfold bundleTableFixedSize at hqd; unfold btEndBundleBase; omega⟩)
          have hpn_mem : ∀ k < 2 * eCap, endOfKey k ∈ edgeEnds B.edges →
              mem' (btEndPrevBase tbl slotCap eCap + k) = mem₀ (btEndPrevBase tbl slotCap eCap + k) ∧
              mem' (btEndNextBase tbl slotCap eCap + k) = mem₀ (btEndNextBase tbl slotCap eCap + k) := fun k hk hke => by
            have hne_end : ∀ y ∈ edgeEnds B_del.edges, endKey y ≠ k := fun y hy heq => by
              have hy' : y = endOfKey k := by rw [← heq, bundle_endOfKey_endKey]
              subst hy'; exact Finset.disjoint_left.mp hdisj_j ((mem_edgeEnds _ _).mp hke) ((mem_edgeEnds _ _).mp hy)
            exact ⟨htbl_unch _ (btEndPrev_in_foot hk)
              (by unfold btEndPrevBase btSlotTouchedBase; omega) (by unfold btEndPrevBase btSlotDelHeadBase; omega)
              (fun _ _ => by unfold btEndPrevBase btSlotDelNextBase; omega) (by unfold btEndPrevBase btSlotCandHeadBase; omega)
              (by unfold btEndPrevBase btCurBunBase; omega) (by unfold btEndPrevBase btCurTagBase; omega)
              (by unfold btEndPrevBase; omega)
              (fun y hy => by have := hend_lt y hy; exact ⟨by have := hne_end y hy; omega, by unfold btEndPrevBase btEndNextBase; omega, by unfold btEndPrevBase btEndBundleBase; omega⟩),
              htbl_unch _ (btEndNext_in_foot hk)
              (by unfold btEndNextBase btSlotTouchedBase; omega) (by unfold btEndNextBase btSlotDelHeadBase; omega)
              (fun _ _ => by unfold btEndNextBase btSlotDelNextBase; omega) (by unfold btEndNextBase btSlotCandHeadBase; omega)
              (by unfold btEndNextBase btCurBunBase; omega) (by unfold btEndNextBase btCurTagBase; omega)
              (by unfold btEndNextBase; omega)
              (fun y hy => by have := hend_lt y hy; exact ⟨by unfold btEndNextBase btEndPrevBase; omega, by have := hne_end y hy; omega, by unfold btEndNextBase btEndBundleBase; omega⟩)⟩
          refine ⟨hptr_eq.trans hsj.1, hsj.2.1, ?_⟩
          by_cases hmem_j : j.1 ∈ remTouched
          · simp only [herase_iff, hmem_j, ↓reduceIte] at hsj ⊢
            exact BundleSlotRepCand.of_agree_ends hsj.2.2 (fun off hoff => hq_mem _ (Nat.le_add_right _ _) (by omega))
              hch_eq hpn_mem
          · simp only [herase_iff, hmem_j, ↓reduceIte] at hsj ⊢
            exact ⟨BundleSlotRepAt.of_agree_ends hsj.2.2.1 (fun off hoff => hq_mem _ (Nat.le_add_right _ _) (by omega))
              hpn_mem, hch_eq.trans hsj.2.2.2⟩
  · intro s' hs'
    by_cases hss : s' = s
    · subst hss; simp only [hnot_er, ↓reduceIte]; exact htch0
    · rw [htbl_unch _ (btSlotTouched_in_foot hs') (by omega)
        (by unfold btSlotTouchedBase btSlotDelHeadBase; omega) (fun _ _ => by unfold btSlotTouchedBase btSlotDelNextBase; omega)
        (by unfold btSlotTouchedBase btSlotCandHeadBase; omega)
        (by unfold btSlotTouchedBase btCurBunBase; omega) (by unfold btSlotTouchedBase btCurTagBase; omega)
        (by unfold btSlotTouchedBase; omega)
        (fun x hx => by have := hend_lt x hx; exact ⟨by unfold btSlotTouchedBase btEndPrevBase; omega, by unfold btSlotTouchedBase btEndNextBase; omega, by unfold btSlotTouchedBase btEndBundleBase; omega⟩),
        htouch s' hs']
      simp only [List.mem_erase_of_ne hss]
  · intro j
    have hd := hdel j
    cases hS0 : S₀ j with
    | none =>
      rw [hS0] at hd
      have hne_s : j.1 ≠ s := fun h => by have : j = js := Fin.ext h; subst this; rw [hS₀s] at hS0; cases hS0
      exact (htbl_unch _ (btSlotDelHead_in_foot j.2)
        (by unfold btSlotDelHeadBase btSlotTouchedBase; omega) (by omega)
        (fun _ _ => by unfold btSlotDelHeadBase btSlotDelNextBase; omega)
        (by unfold btSlotDelHeadBase btSlotCandHeadBase; omega)
        (by unfold btSlotDelHeadBase btCurBunBase; omega) (by unfold btSlotDelHeadBase btCurTagBase; omega)
        (by unfold btSlotDelHeadBase; omega)
        (fun x hx => by have := hend_lt x hx; exact ⟨by unfold btSlotDelHeadBase btEndPrevBase; omega, by unfold btSlotDelHeadBase btEndNextBase; omega, by unfold btSlotDelHeadBase btEndBundleBase; omega⟩)).trans hd
    | some Bj =>
      rw [hS0] at hd
      by_cases hj : j = js
      · subst hj; simp only [js, hnot_er, ↓reduceIte]; exact hdelH0
      · have hne_s : j.1 ≠ s := fun h => hj (Fin.ext h)
        have hdh_eq : mem' (btSlotDelHeadBase tbl slotCap eCap + j.1) =
            mem₀ (btSlotDelHeadBase tbl slotCap eCap + j.1) :=
          htbl_unch _ (btSlotDelHead_in_foot j.2)
            (by unfold btSlotDelHeadBase btSlotTouchedBase; omega) (by omega)
            (fun _ _ => by unfold btSlotDelHeadBase btSlotDelNextBase; omega)
            (by unfold btSlotDelHeadBase btSlotCandHeadBase; omega)
            (by unfold btSlotDelHeadBase btCurBunBase; omega) (by unfold btSlotDelHeadBase btCurTagBase; omega)
            (by unfold btSlotDelHeadBase; omega)
            (fun x hx => by have := hend_lt x hx; exact ⟨by unfold btSlotDelHeadBase btEndPrevBase; omega, by unfold btSlotDelHeadBase btEndNextBase; omega, by unfold btSlotDelHeadBase btEndBundleBase; omega⟩)
        simp only [List.mem_erase_of_ne hne_s]
        by_cases hmem_j : j.1 ∈ remTouched
        · simp only [hmem_j, ↓reduceIte] at hd ⊢
          rcases hd with ⟨dLj, hsllj, hdLj⟩
          refine ⟨dLj, hsllj.of_agree hdh_eq fun e he => ?_, hdLj⟩
          have he_lt := hsllj.mem_lt e he
          have he_not_D : ∀ e' ∈ B₀.edges ∩ D, e ≠ e' := fun e' he' heq => by
            subst heq
            exact Finset.disjoint_left.mp (hdisj₀ j js hj Bj B₀ hS0 hS₀s)
              (Finset.mem_inter.mp ((hdLj e).mp he)).1 (Finset.mem_inter.mp he').1
          exact htbl_unch _ (btSlotDelNext_in_foot he_lt)
            (by unfold btSlotDelNextBase btSlotTouchedBase; omega) (by unfold btSlotDelNextBase btSlotDelHeadBase; omega)
            (fun e' he' => by have := he_not_D e' he'; omega)
            (by unfold btSlotDelNextBase btSlotCandHeadBase; omega)
            (by unfold btSlotDelNextBase btCurBunBase; omega) (by unfold btSlotDelNextBase btCurTagBase; omega)
            (by unfold btSlotDelNextBase; omega)
            (fun x hx => by have := hend_lt x hx; exact ⟨by unfold btSlotDelNextBase btEndPrevBase; omega, by unfold btSlotDelNextBase btEndNextBase; omega, by unfold btSlotDelNextBase btEndBundleBase; omega⟩)
        · simp only [hmem_j, ↓reduceIte] at hd ⊢; exact hdh_eq.trans hd
  · intro e he hnot
    by_cases heBD : e ∈ B₀.edges ∩ D
    · exact hdL0 e heBD
    · rw [htbl_unch _ (btSlotDelNext_in_foot he)
        (by unfold btSlotDelNextBase btSlotTouchedBase; omega) (by unfold btSlotDelNextBase btSlotDelHeadBase; omega)
        (fun e' he' heq => heBD (by have : e = e' := by unfold btSlotDelNextBase at heq; omega
                                    rwa [this]))
        (by unfold btSlotDelNextBase btSlotCandHeadBase; omega)
        (by unfold btSlotDelNextBase btCurBunBase; omega) (by unfold btSlotDelNextBase btCurTagBase; omega)
        (by unfold btSlotDelNextBase; omega)
        (fun x hx => by have := hend_lt x hx; exact ⟨by unfold btSlotDelNextBase btEndPrevBase; omega, by unfold btSlotDelNextBase btEndNextBase; omega, by unfold btSlotDelNextBase btEndBundleBase; omega⟩)]
      refine hdelN0 e he fun j Bj hmj hS0 heBj => ?_
      by_cases hj : j = js
      · subst hj; rw [hS₀s] at hS0; cases hS0; exact heBD heBj
      · exact hnot j Bj ((List.mem_erase_of_ne (fun h => hj (Fin.ext h))).mpr hmj) hS0 heBj


end

end MinCostFlow.SparseCore.Program
