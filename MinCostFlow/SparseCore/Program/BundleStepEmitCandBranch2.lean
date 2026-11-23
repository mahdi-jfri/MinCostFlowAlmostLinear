module

public import MinCostFlow.SparseCore.Program.BundleStepEmitCandHelpers

/-!
# Phase 3 single-candidate Branch 2 verification (`BundleStepEmitCandBranch2`)

Verifies the Branch 2 fallback of `bundleStepEmitOneCandStmt` (entered when `degB - m_b ≤ winLen`,
which implies `degB ≤ 2 * m_b` and `vRunsEndsLen (pre ++ post) ≤ m_b`): packs all `degB` ends
via `bTourOwner`, sorts via `bMergeSort`, finds the first maximum-length run `[winStart, winEnd)`
via `bundleStepEmitMaxRunStmt`, keeps it in bundle `b`, and runs `bundleStepEmitCand_runsLoop`
on `pre = raw.take bestIdx` (`[0, winStart)`) and `post = raw.drop (bestIdx + 1)`
(`[winEnd, degB)`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

set_option maxHeartbeats 400000 in
/-- Verification of the Branch 2 body of `bundleStepEmitOneCandStmt`: packs all `degB` ends of
`b`, sorts, locates the largest run `bestIdx = maxRunIdx raw`, and emits runs before and after
`bestIdx`, matching `runsFoldStep (ops, B) (b, byRootVRuns B B.edges src' b)` within space
`(6 + 2 * TS.querySpace) * m_b`, batch words `6 * m_b`, and new bundles `m_b`. -/
theorem bundleStepEmitOneCandBranch2_runs {TS : BundleTourSpec} {w vCap eCap p bunCap b nB tourH
    batchPtr writeOff updCnt prevBase nextBase endBundleBase hCur m_b : ℕ}
    {pProg : Program} {bDllPush bDllErase bMergeSort bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    {htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner}
    {cord' : ℕ → List End} {src' : End → ℕ} {G₀ : MGraph} {ops : List Update} {B : BundleState}
    {tx₀ : htour.rep.τ} {st₀ : State}
    (hpPush : pProg.HasAt bDllPush [bundleDllPushStmt])
    (hpErase : pProg.HasAt bDllErase [bundleDllEraseStmt])
    (hMergeSort : ∀ L : List ℕ, MeetsContract w pProg bMergeSort (mergeSortContract w L))
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w) (heCap_w : 2 * eCap < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (hprev_w : prevBase + 2 * eCap < 2 ^ w) (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (heb_w : endBundleBase + 2 * eCap < 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hbat_w : batchPtr + writeOff + 6 * m_b < 2 ^ w)
    (hupd_w : updCnt + m_b < 2 ^ w)
    (hh_w : hCur + (6 + 2 * TS.querySpace) * m_b < 2 ^ w)
    (hV : B.vertices = Finset.range nB) (hb_lt : b < nB) (hnb_cap : nB + m_b ≤ bunCap)
    (hdeg_pos : 0 < (B.ends b).card) (hdeg_le : (B.ends b).card ≤ 2 * m_b)
    (hlt_best : maxRunIdx (rawByRootVRuns B B.edges src' b) < (rawByRootVRuns B B.edges src' b).length)
    (hby_eq : byRootVRuns B B.edges src' b =
      ((rawByRootVRuns B B.edges src' b)[maxRunIdx (rawByRootVRuns B B.edges src' b)]'hlt_best) ::
        ((rawByRootVRuns B B.edges src' b).take (maxRunIdx (rawByRootVRuns B B.edges src' b)) ++
         (rawByRootVRuns B B.edges src' b).drop (maxRunIdx (rawByRootVRuns B B.edges src' b) + 1)))
    (hsplit_len :
      vRunsEndsLen ((rawByRootVRuns B B.edges src' b).take (maxRunIdx (rawByRootVRuns B B.edges src' b))) +
      ((rawByRootVRuns B B.edges src' b)[maxRunIdx (rawByRootVRuns B B.edges src' b)]'hlt_best).2.length +
      vRunsEndsLen ((rawByRootVRuns B B.edges src' b).drop (maxRunIdx (rawByRootVRuns B B.edges src' b) + 1)) =
      (B.ends b).card)
    (hmoved_le :
      vRunsEndsLen ((rawByRootVRuns B B.edges src' b).take (maxRunIdx (rawByRootVRuns B B.edges src' b))) +
      vRunsEndsLen ((rawByRootVRuns B B.edges src' b).drop (maxRunIdx (rawByRootVRuns B B.edges src' b) + 1)) ≤ m_b)
    (hsrc_lt : ∀ x ∈ B.ends b, src' x < vCap)
    (hsrc_mem : ∀ x ∈ B.ends b, x ∈ cord' (src' x))
    (hsrc_uniq : ∀ x ∈ B.ends b, ∀ v', x ∈ cord' v' → v' = src' x)
    (hprev_next : prevBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ prevBase)
    (hblk_prev : p + bundleSlotBlockSize bunCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ p)
    (hblk_next : p + bundleSlotBlockSize bunCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ p)
    (heb_prev : endBundleBase + 2 * eCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ endBundleBase)
    (heb_next : endBundleBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ endBundleBase)
    (heb_blk : endBundleBase + 2 * eCap ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ endBundleBase)
    (hbat_blk : batchPtr + writeOff + 6 * m_b ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ batchPtr)
    (hbat_prev : batchPtr + writeOff + 6 * m_b ≤ prevBase ∨ prevBase + 2 * eCap ≤ batchPtr)
    (hbat_next : batchPtr + writeOff + 6 * m_b ≤ nextBase ∨ nextBase + 2 * eCap ≤ batchPtr)
    (hbat_eb : batchPtr + writeOff + 6 * m_b ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ batchPtr)
    (hbat_h : batchPtr + writeOff + 6 * m_b ≤ hCur)
    (hh_blk : p + bundleSlotBlockSize bunCap ≤ hCur)
    (hh_prev : prevBase + 2 * eCap ≤ hCur)
    (hh_next : nextBase + 2 * eCap ≤ hCur)
    (hh_eb : endBundleBase + 2 * eCap ≤ hCur)
    (htrep : htour.rep.rep tourH cord' tx₀ st₀.mem)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < hCur)
    (htfoot_disj_blk : ∀ a, htour.rep.foot tourH tx₀ a → a < p ∨ p + bundleSlotBlockSize bunCap ≤ a)
    (htfoot_disj_prev : ∀ a, htour.rep.foot tourH tx₀ a → a < prevBase ∨ prevBase + 2 * eCap ≤ a)
    (htfoot_disj_next : ∀ a, htour.rep.foot tourH tx₀ a → a < nextBase ∨ nextBase + 2 * eCap ≤ a)
    (htfoot_disj_eb : ∀ a, htour.rep.foot tourH tx₀ a → a < endBundleBase ∨ endBundleBase + 2 * eCap ≤ a)
    (htfoot_disj_bat : ∀ a, htour.rep.foot tourH tx₀ a → a < batchPtr ∨ batchPtr + writeOff + 6 * m_b ≤ a)
    (hzero : ZeroFrom st₀.mem hCur)
    (hrep : BundleSlotRepAt eCap prevBase nextBase p bunCap B st₀.mem)
    (hG₀ : G₀.applyBatch ops = B.graph)
    (hbat : SmallBatchBodyAt st₀.mem (batchPtr + 1) G₀ ops (writeOff - 1)) (hw1 : 1 ≤ writeOff)
    (hr1 : st₀.regs 1 = tourH) (hr4 : st₀.regs 4 = hCur) (hr6 : st₀.regs 6 = 2 * eCap)
    (hr7 : st₀.regs 7 = p) (hr8 : st₀.regs 8 = bunCap) (hr9 : st₀.regs 9 = endBundleBase)
    (hr10 : st₀.regs 10 = prevBase) (hr11 : st₀.regs 11 = nextBase)
    (hr20 : st₀.regs 20 = batchPtr) (hr21 : st₀.regs 21 = writeOff) (hr22 : st₀.regs 22 = updCnt)
    (hr25 : st₀.regs 25 = b) (hr26 : st₀.regs 26 = (B.ends b).card) :
    let vruns := byRootVRuns B B.edges src' b
    let res := runsFoldStep (ops, B) (b, vruns)
    let addedUpds := (vruns.drop 1).length
    ∃ stEnd cEnd txEnd hEnd addedWords,
      Runs w pProg ω
        (.assign 27 (.reg 4) ;;
         .assign 4 (.bin .add (.reg 27) (.reg 26)) ;;
         .assign 28 (.load (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25))) ;;
         .assign 29 (.const 0) ;;
         .loop (.reg 28)
           (.assign 30 (.bin .sub (.reg 28) (.const 1)) ;;
            .assign 31 (.reg 4) ;;
            .call 4 bTourOwner [.reg 1, .reg 30, .reg 4] ;;
            .assign 32 (.load (.reg 31)) ;;
            .store (.bin .add (.reg 27) (.reg 29))
              (.bin .add (.bin .mul (.reg 32) (.reg 6)) (.reg 30)) ;;
            .assign 29 (.bin .add (.reg 29) (.const 1)) ;;
            .assign 28 (.load (.bin .add (.reg 11) (.reg 30)))) ;;
         .assign 28 (.reg 4) ;;
         .assign 4 (.bin .add (.reg 28) (.reg 26)) ;;
         .call 29 bMergeSort [.reg 27, .reg 26, .reg 28] ;;
         .assign 30 (.reg 26) ;;
         bundleStepEmitMaxRunStmt ;;
         .assign 23 (.reg 26) ;;
         .assign 28 (.reg 32) ;;
         .assign 26 (.reg 31) ;;
         .assign 29 (.const 0) ;;
         .loop (.bin .lt (.reg 29) (.reg 26))
           (bundleStepEmitOneRunStmt bDllPush bDllErase) ;;
         .assign 26 (.reg 23) ;;
         .assign 29 (.reg 28) ;;
         .loop (.bin .lt (.reg 29) (.reg 26))
           (bundleStepEmitOneRunStmt bDllPush bDllErase))
        st₀ .normal stEnd cEnd ∧
      (∀ r ≤ 24, r ≠ 4 → r ≠ 21 → r ≠ 22 → r ≠ 23 → stEnd.regs r = st₀.regs r) ∧
      stEnd.regs 4 = hEnd ∧ hCur ≤ hEnd ∧ hEnd ≤ hCur + (6 + 2 * TS.querySpace) * m_b ∧
      stEnd.regs 21 = writeOff + addedWords ∧
      stEnd.regs 22 = updCnt + addedUpds ∧
      addedWords ≤ 6 * m_b ∧ addedUpds ≤ m_b ∧
      res.2.vertices = Finset.range (nB + addedUpds) ∧
      BundleSlotRepAt eCap prevBase nextBase p bunCap res.2 stEnd.mem ∧
      G₀.applyBatch res.1 = res.2.graph ∧
      SmallBatchBodyAt stEnd.mem (batchPtr + 1) G₀ res.1 (writeOff + addedWords - 1) ∧
      (∀ x ∈ B.ends b, stEnd.mem (endBundleBase + endKey x) = res.2.bundleOf x ∨
        (res.2.bundleOf x = b ∧ stEnd.mem (endBundleBase + endKey x) = st₀.mem (endBundleBase + endKey x))) ∧
      htour.rep.rep tourH cord' txEnd stEnd.mem ∧
      (∀ a, htour.rep.foot tourH txEnd a → htour.rep.foot tourH tx₀ a ∨ (hCur ≤ a ∧ a < hEnd)) ∧
      ZeroFrom stEnd.mem hEnd ∧
      (∀ a, ¬ htour.rep.foot tourH tx₀ a →
        (a < p ∨ p + bundleSlotBlockSize bunCap ≤ a) →
        (∀ x ∈ B.ends b, a ≠ prevBase + endKey x ∧ a ≠ nextBase + endKey x ∧ a ≠ endBundleBase + endKey x) →
        (a < batchPtr + writeOff ∨ batchPtr + writeOff + 6 * m_b ≤ a) →
        (a < hCur ∨ hEnd ≤ a) → stEnd.mem a = st₀.mem a) ∧
      cEnd + htour.rep.phi tourH txEnd stEnd.mem ≤
        (2 * TS.mul * ordStoreLog eCap + 400 * (Nat.log 2 (2 * m_b + 1) + 1) + 820) * m_b + 220 +
        htour.rep.phi tourH tx₀ st₀.mem := by
  intro vruns res addedUpds
  set degB := (B.ends b).card
  set raw := rawByRootVRuns B B.edges src' b
  set bestIdx := maxRunIdx raw
  set best := raw[bestIdx]'hlt_best
  set pre := raw.take bestIdx
  set post := raw.drop (bestIdx + 1)
  have hrep_copy := hrep
  obtain ⟨nB', hV', _, hE_lt, hbo_lt', _, _, _, _, _, _, _, _⟩ := hrep
  have hnB_eq : nB' = nB := by
    have := congrArg Finset.card (hV'.symm.trans hV); simpa [Finset.card_range] using this
  rw [hnB_eq] at hbo_lt'
  have h1q_deg_le : (1 + TS.querySpace) * degB ≤ (2 + 2 * TS.querySpace) * m_b := by
    calc (1 + TS.querySpace) * degB ≤ (1 + TS.querySpace) * (2 * m_b) := Nat.mul_le_mul_left _ hdeg_le
      _ = (2 + 2 * TS.querySpace) * m_b := by ring
  have hdeg_budget : (1 + TS.querySpace) * degB + degB + 2 * m_b ≤ (6 + 2 * TS.querySpace) * m_b := by
    have hmul : (6 + 2 * TS.querySpace) * m_b = (2 + 2 * TS.querySpace) * m_b + 2 * m_b + 2 * m_b := by ring
    omega
  -- Steps 1–3 via `branch2_pack_sort_maxRun_runs`
  obtain ⟨stMR, cPref, txP, hP, hrunPref, hregsMR, hr4MR, hr27MR, hr31MR, hr32MR,
    hhP_lo, hhP_hi, hraw_len, hLatMR, htrMR, htfP, hfrMR, hcPref⟩ :=
    branch2_pack_sort_maxRun_runs (htour := htour) (ω := ω) (st₀ := st₀) (m_b := m_b)
      hMergeSort hw16 htourH_w heCap_w hpk_w hnext_w hp_w hh_w
      hV hb_lt hdeg_le hsrc_lt hsrc_mem hsrc_uniq hh_blk hh_next htrep htfoot_lt htfoot_disj_next
      hzero hrep_copy hr1 hr4 hr6 hr7 hr11 hr25 hr26
  change stMR.regs 4 = hP + degB at hr4MR
  change stMR.regs 31 = vRunsEndsLen pre at hr31MR
  change stMR.regs 32 = vRunsEndsLen (raw.take (bestIdx + 1)) at hr32MR
  change hCur + degB ≤ hP at hhP_lo
  change hP ≤ hCur + (1 + TS.querySpace) * degB at hhP_hi
  change vRunsEndsLen raw = degB at hraw_len
  change ListAt stMR.mem hCur (vRunsPacked eCap raw) at hLatMR
  change ∀ a, htour.rep.foot tourH txP a → htour.rep.foot tourH tx₀ a ∨ (hCur + degB ≤ a ∧ a < hP) at htfP
  change ∀ a, ¬ htour.rep.foot tourH tx₀ a → (a < hCur ∨ hP + degB ≤ a) → stMR.mem a = st₀.mem a at hfrMR
  -- Decomposition of `raw = pre ++ best :: post`
  have hraw_pw : (raw.map Prod.fst).Pairwise (· < ·) := rawByRootVRuns_pairwise
  have hraw_keys : ∀ vr ∈ raw, ∀ x ∈ vr.2, endKey x < 2 * eCap := fun vr hvr x hx => by
    have := hE_lt x.1 ((BundleState.mem_ends B b x).mp ((rawByRootVRuns_info vr hvr).2.2 x hx).1).1
    rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
  have hraw_pos : ∀ vr ∈ raw, vr.1 < vCap ∧ 0 < vr.2.length := fun vr hvr => by
    have hi := rawByRootVRuns_info vr hvr
    obtain ⟨x₀, hx₀⟩ := List.length_pos_iff_exists_mem.mp hi.1
    have hx_info := hi.2.2 x₀ hx₀
    exact ⟨hx_info.2 ▸ hsrc_lt x₀ hx_info.1, hi.1⟩
  have hpre_sub : ∀ vr ∈ pre, vr ∈ raw := fun vr h => List.mem_of_mem_take h
  have hpost_sub : ∀ vr ∈ post, vr ∈ raw := fun vr h => List.mem_of_mem_drop h
  have hbest_mem : best ∈ raw := List.getElem_mem hlt_best
  have hbest_info := rawByRootVRuns_info best hbest_mem
  have hraw_decomp : raw = pre ++ best :: post := by
    conv_lhs => rw [← List.take_append_drop bestIdx raw, List.drop_eq_getElem_cons hlt_best]
  have hwinEnd_eq : vRunsEndsLen (raw.take (bestIdx + 1)) = vRunsEndsLen pre + best.2.length := by
    rw [List.take_succ_eq_append_getElem hlt_best, vRunsEndsLen_append]; simp [vRunsEndsLen, pre, best]
  rw [hwinEnd_eq] at hr32MR
  have hpack_raw_split : vRunsPacked eCap raw =
      vRunsPacked eCap pre ++ (best.2.map fun x => packEndKey eCap best.1 (endKey x)) ++
      vRunsPacked eCap post := by
    conv_lhs => rw [hraw_decomp]
    simp [vRunsPacked, List.append_assoc]
  have hpw_pre : (pre.map Prod.fst).Pairwise (· < ·) :=
    hraw_pw.sublist ((List.take_sublist bestIdx raw).map Prod.fst)
  have hpw_post : (post.map Prod.fst).Pairwise (· < ·) :=
    hraw_pw.sublist ((List.drop_sublist (bestIdx + 1) raw).map Prod.fst)
  have hpw_pre_post : ∀ vr₁ ∈ pre, ∀ vr₂ ∈ post, vr₁.1 < vr₂.1 := by
    intro vr₁ h1 vr₂ h2
    have hpw_d := hraw_pw; rw [hraw_decomp, List.map_append, List.map_cons, List.pairwise_append] at hpw_d
    exact hpw_d.2.2 vr₁.1 (List.mem_map.mpr ⟨vr₁, h1, rfl⟩) vr₂.1 (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨vr₂, h2, rfl⟩))
  have hpw_pre_best : ∀ vr ∈ pre, vr.1 < best.1 := by
    intro vr h1
    have hpw_d := hraw_pw; rw [hraw_decomp, List.map_append, List.map_cons, List.pairwise_append] at hpw_d
    exact hpw_d.2.2 vr.1 (List.mem_map.mpr ⟨vr, h1, rfl⟩) best.1 List.mem_cons_self
  have hpw_best_post : ∀ vr ∈ post, best.1 < vr.1 := by
    intro vr h2
    have hpw_d := hraw_pw; rw [hraw_decomp, List.map_append, List.map_cons, List.pairwise_append, List.pairwise_cons] at hpw_d
    exact hpw_d.2.1.1 vr.1 (List.mem_map.mpr ⟨vr, h2, rfl⟩)
  have hdisj_of_pw : ∀ (rs : List (ℕ × List End)), (∀ vr ∈ rs, vr ∈ raw) →
      (rs.map Prod.fst).Pairwise (· < ·) →
      ∀ i j (hi : i < rs.length) (hj : j < rs.length), i ≠ j → ∀ x ∈ rs[i].2, x ∉ rs[j].2 := by
    intro rs hsub hpw i j hi hj hne x hxi hxj
    have h1 := ((rawByRootVRuns_info _ (hsub _ (List.getElem_mem hi))).2.2 x hxi).2
    have h2 := ((rawByRootVRuns_info _ (hsub _ (List.getElem_mem hj))).2.2 x hxj).2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := List.pairwise_iff_getElem.mp hpw i j (by simp; omega) (by simp; omega) hlt
      simp only [List.getElem_map] at this; omega
    · have := List.pairwise_iff_getElem.mp hpw j i (by simp; omega) (by simp; omega) hgt
      simp only [List.getElem_map] at this; omega
  have hdisj_pre := hdisj_of_pw pre hpre_sub hpw_pre
  have hdisj_post := hdisj_of_pw post hpost_sub hpw_post
  have hrepMR_mem : ∀ a, (p ≤ a ∧ a < p + bundleSlotBlockSize bunCap) ∨
      (prevBase ≤ a ∧ a < prevBase + 2 * eCap) ∨ (nextBase ≤ a ∧ a < nextBase + 2 * eCap) ∨
      (endBundleBase ≤ a ∧ a < endBundleBase + 2 * eCap) ∨
      (batchPtr ≤ a ∧ a < batchPtr + writeOff + 6 * m_b) → stMR.mem a = st₀.mem a := fun a ha => by
    refine hfrMR a (fun hf => ?_) (Or.inl ?_)
    · rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := htfoot_disj_blk a hf; omega
      · have := htfoot_disj_prev a hf; omega
      · have := htfoot_disj_next a hf; omega
      · have := htfoot_disj_eb a hf; omega
      · have := htfoot_disj_bat a hf; omega
    · rcases ha with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
  let B0 : BundleState := { B with parent := Function.update B.parent b best.1 }
  have hrep_B0 : BundleSlotRepAt eCap prevBase nextBase p bunCap B0 stMR.mem := by
    have hrep_B : BundleSlotRepAt eCap prevBase nextBase p bunCap B stMR.mem :=
      hrep_copy.of_agree (fun a h1 h2 => (hrepMR_mem a (Or.inl ⟨h1, h2⟩)).symm)
        (fun k hk => (hrepMR_mem _ (Or.inr (Or.inl ⟨by omega, by omega⟩))).symm)
        (fun k hk => (hrepMR_mem _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))).symm)
    obtain ⟨nB'', hV'', hnB'', hE'', hbo'', hpar0'', hc0, hc1, hc2, hdll'', hpar'', htail'', hscr''⟩ := hrep_B
    have hnB''_eq : nB'' = nB := by
      have := congrArg Finset.card (hV''.symm.trans hV); simpa [Finset.card_range] using this
    refine ⟨nB'', hV'', hnB'', hE'', hbo'', fun c hc => by
      dsimp only [B0]; rw [Function.update_of_ne (by omega)]; exact hpar0'' c hc,
      hc0, hc1, hc2, hdll'', fun c hc hem => by
      have hcb : c ≠ b := fun heq => (Finset.card_pos.mp hdeg_pos).ne_empty (heq ▸ hem)
      dsimp only [B0]; rw [Function.update_of_ne hcb]; exact hpar'' c hc hem, htail'', hscr''⟩
  -- Step 4: Save `r23 := degB`, `r28 := winEnd`, set `r26 := winStart`, `r29 := 0`
  have hr26MR : stMR.regs 26 = degB := (hregsMR 26 (le_refl _) (by decide)).trans hr26
  let r23a := Function.update stMR.regs 23 degB
  let r28a := Function.update r23a 28 (vRunsEndsLen pre + best.2.length)
  let r26a := Function.update r28a 26 (vRunsEndsLen pre)
  let r29a := Function.update r26a 29 0
  let stPre0 : State := { stMR with regs := r29a }
  have ha23 : Runs w pProg ω (.assign 23 (.reg 26)) stMR .normal { stMR with regs := r23a } 2 :=
    runs_assign_iff.mpr ⟨degB, by simp [Expr.eval, hr26MR], rfl, rfl, rfl⟩
  have ha28a : Runs w pProg ω (.assign 28 (.reg 32)) { stMR with regs := r23a } .normal { stMR with regs := r28a } 2 :=
    runs_assign_iff.mpr ⟨vRunsEndsLen pre + best.2.length, by simp [Expr.eval, r23a, hr32MR], rfl, rfl, rfl⟩
  have ha26a : Runs w pProg ω (.assign 26 (.reg 31)) { stMR with regs := r28a } .normal { stMR with regs := r26a } 2 :=
    runs_assign_iff.mpr ⟨vRunsEndsLen pre, by simp [Expr.eval, r28a, r23a, hr31MR, pre, bestIdx], rfl, rfl, rfl⟩
  have ha29a : Runs w pProg ω (.assign 29 (.const 0)) { stMR with regs := r26a } .normal stPre0 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  -- Step 5: First `runsLoop` on `pre`
  have hpre_len_le : pre.length ≤ vRunsEndsLen pre := vRuns_len_le_ends pre fun vr hvr => (hraw_pos vr (hpre_sub vr hvr)).2
  have hpost_len_le : post.length ≤ vRunsEndsLen post := vRuns_len_le_ends post fun vr hvr => (hraw_pos vr (hpost_sub vr hvr)).2
  have hpre_bw_le : vRunsBatchWords pre ≤ 6 * vRunsEndsLen pre :=
    vRunsBatchWords_le pre fun vr hvr => (hraw_pos vr (hpre_sub vr hvr)).2
  have hpost_bw_le : vRunsBatchWords post ≤ 6 * vRunsEndsLen post :=
    vRunsBatchWords_le post fun vr hvr => (hraw_pos vr (hpost_sub vr hvr)).2
  have hpack_pre : ListAt stPre0.mem (hCur + 0) (vRunsPacked eCap pre) := fun t ht => by
    dsimp only [stPre0]; rw [Nat.add_zero]
    have hlt : t < (vRunsPacked eCap raw).length := by
      rw [vRunsPacked_length] at ht ⊢; rw [hraw_len]; omega
    rw [hLatMR t hlt]; simp only [hpack_raw_split]
    rw [List.getElem_append_left (by simp [vRunsPacked_length] at ht ⊢; omega),
        List.getElem_append_left (by simpa [vRunsPacked_length] using ht)]
  set xBest := best.2[0]'hbest_info.1
  have hxBest_info : xBest ∈ B.ends b ∧ src' xBest = best.1 := hbest_info.2.2 xBest (List.getElem_mem hbest_info.1)
  have hPreReg : ∀ r ≤ 22, r ≠ 4 → stPre0.regs r = st₀.regs r := fun r hr h4 => by
    simp only [stPre0, r29a, r26a, r28a, r23a,
      Function.update_of_ne (show r ≠ 29 by omega), Function.update_of_ne (show r ≠ 26 by omega),
      Function.update_of_ne (show r ≠ 28 by omega), Function.update_of_ne (show r ≠ 23 by omega)]
    exact hregsMR r (by omega) h4
  obtain ⟨st1, cPre, h1, wPre, hrunPre, hregs1, hr4_1, hh1_lo, hh1_hi, hwPre_le,
    hr21_1, hr22_1, _, hrep1, hbat1, heb1, hfr1, hcPre⟩ :=
    bundleStepEmitCand_runsLoop (ω := ω) (degB := vRunsEndsLen pre) (packArr := hCur)
      hpPush hpErase hw16 heCap_w hpk_w hprev_w hnext_w heb_w hp_w
      (by omega) hprev_next hblk_prev hblk_next heb_prev heb_next heb_blk
      (by omega) (by omega) (by omega) (by omega)
      pre ops B0 nB 0 writeOff updCnt (hP + degB) G₀ stPre0
      hV hb_lt (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun vr hvr =>
        have hi := rawByRootVRuns_info vr (hpre_sub vr hvr)
        ⟨(hraw_pos vr (hpre_sub vr hvr)).1, hi.1, hi.2.1, fun x hx => (hi.2.2 x hx).1⟩)
      hpw_pre hdisj_pre
      ⟨xBest, hxBest_info.1, fun vr hvr hmem => by
        have h1 := ((rawByRootVRuns_info vr (hpre_sub vr hvr)).2.2 xBest hmem).2
        have hlt := hpw_pre_best vr hvr; omega⟩
      (by omega) (Or.inl (by omega))
      (by clear * - hbat_blk hpre_bw_le hmoved_le; omega) (by clear * - hbat_prev hpre_bw_le hmoved_le; omega)
      (by clear * - hbat_next hpre_bw_le hmoved_le; omega) (by clear * - hbat_eb hpre_bw_le hmoved_le; omega)
      (by clear * - hbat_h hhP_lo hpre_bw_le hmoved_le; omega)
      (by omega) (by omega) (by omega) (by omega)
      hrep_B0 hG₀ (smallBatchBodyAt_agree hbat fun a ha1 ha2 => hrepMR_mem a (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))
      hw1 hpack_pre
      (by simp [stPre0, r29a, r26a, r28a, r23a, hr4MR])
      ((hPreReg 6 (by decide) (by decide)).trans hr6)
      ((hPreReg 7 (by decide) (by decide)).trans hr7)
      ((hPreReg 8 (by decide) (by decide)).trans hr8)
      ((hPreReg 9 (by decide) (by decide)).trans hr9)
      ((hPreReg 10 (by decide) (by decide)).trans hr10)
      ((hPreReg 11 (by decide) (by decide)).trans hr11)
      ((hPreReg 20 (by decide) (by decide)).trans hr20)
      ((hPreReg 21 (by decide) (by decide)).trans hr21)
      ((hPreReg 22 (by decide) (by decide)).trans hr22)
      (by simp [stPre0, r29a, r26a, r28a, r23a, hregsMR 25 (by decide) (by decide), hr25])
      (by simp [stPre0, r29a, r26a])
      (by simp [stPre0, r29a, r26a, r28a, r23a, hr27MR])
      (by simp [stPre0, r29a])
  -- Intermediate state `mid = foldOneSplitRuns b pre (ops, B0, nB)`
  set mid := foldOneSplitRuns b pre (ops, B0, nB)
  have hmid_nB : mid.2.2 = nB + pre.length := by
    have hgo : ∀ (rs : List (ℕ × List End)) (acc : List Update × BundleState × ℕ),
        (foldOneSplitRuns b rs acc).2.2 = acc.2.2 + rs.length := by
      intro rs; induction rs with
      | nil => intro acc; simp [foldOneSplitRuns]
      | cons r tl ih => rcases r with ⟨vc, xs⟩; intro ⟨o, B', n⟩; dsimp only [foldOneSplitRuns]; rw [ih]; simp; omega
    exact hgo pre (ops, B0, nB)
  obtain ⟨hV_m, hE_m, hG_m, hstay_m⟩ := foldOneSplitRuns_props pre G₀ ops B0 nB hV hb_lt hG₀
    (fun vr hvr x hx => ((rawByRootVRuns_info vr (hpre_sub vr hvr)).2.2 x hx).1) hdisj_pre hbo_lt'
  have hpost_in_mid : ∀ vr ∈ post, ∀ x ∈ vr.2, x ∈ mid.2.1.ends b := by
    intro vr hvr x hx
    have hxi := (rawByRootVRuns_info vr (hpost_sub vr hvr)).2.2 x hx
    have hxE : x ∈ edgeEnds B.edges := (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp hxi.1).1
    have hnot_pre : ∀ vr' ∈ pre, x ∉ vr'.2 := fun vr' hvr' hmem => by
      have h1 := ((rawByRootVRuns_info vr' (hpre_sub vr' hvr')).2.2 x hmem).2
      have hlt := hpw_pre_post vr' hvr' vr hvr; omega
    rw [BundleState.mem_ends, hE_m]
    exact ⟨((BundleState.mem_ends B b x).mp hxi.1).1,
      (hstay_m x hxE hnot_pre).trans ((BundleState.mem_ends B b x).mp hxi.1).2⟩
  have hxBest_in_mid : xBest ∈ mid.2.1.ends b := by
    have hxE : xBest ∈ edgeEnds B.edges := (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b xBest).mp hxBest_info.1).1
    have hnot_pre : ∀ vr' ∈ pre, xBest ∉ vr'.2 := fun vr' hvr' hmem => by
      have h1 := ((rawByRootVRuns_info vr' (hpre_sub vr' hvr')).2.2 xBest hmem).2
      have hlt := hpw_pre_best vr' hvr'; omega
    rw [BundleState.mem_ends, hE_m]
    exact ⟨((BundleState.mem_ends B b xBest).mp hxBest_info.1).1,
      (hstay_m xBest hxE hnot_pre).trans ((BundleState.mem_ends B b xBest).mp hxBest_info.1).2⟩
  -- Step 6: Restore `r26 := r23`, `r29 := r28`
  have hr23_1 : st1.regs 23 = degB := (hregs1 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (by simp [stPre0, r29a, r26a, r28a, r23a])
  have hr28_1 : st1.regs 28 = vRunsEndsLen pre + best.2.length :=
    (hregs1 28 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    (by simp [stPre0, r29a, r26a, r28a])
  let r26b := Function.update st1.regs 26 degB
  let r29b := Function.update r26b 29 (vRunsEndsLen pre + best.2.length)
  let stPost0 : State := { st1 with regs := r29b }
  have ha26b : Runs w pProg ω (.assign 26 (.reg 23)) st1 .normal { st1 with regs := r26b } 2 :=
    runs_assign_iff.mpr ⟨degB, by simp [Expr.eval, hr23_1], rfl, rfl, rfl⟩
  have ha29b : Runs w pProg ω (.assign 29 (.reg 28)) { st1 with regs := r26b } .normal stPost0 2 :=
    runs_assign_iff.mpr ⟨vRunsEndsLen pre + best.2.length, by simp [Expr.eval, r26b, hr28_1], rfl, rfl, rfl⟩
  -- Step 7: Second `runsLoop` on `post`
  have hpack_post : ListAt stPost0.mem (hCur + (vRunsEndsLen pre + best.2.length)) (vRunsPacked eCap post) := fun t ht => by
    dsimp only [stPost0]
    have hlt_raw : vRunsEndsLen pre + best.2.length + t < (vRunsPacked eCap raw).length := by
      rw [vRunsPacked_length] at ht ⊢; rw [hraw_len]; omega
    have hlt_deg : vRunsEndsLen pre + best.2.length + t < degB := by
      rw [vRunsPacked_length] at ht; omega
    have hmem1 : st1.mem (hCur + (vRunsEndsLen pre + best.2.length) + t) =
        stMR.mem (hCur + (vRunsEndsLen pre + best.2.length) + t) :=
      hfr1 _ (by omega)
        (fun x hx => by
          have hxk : endKey x < 2 * eCap := by
            have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
            rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
          exact ⟨by omega, by omega⟩)
        (fun vr hvr x hx => by have := hraw_keys vr (hpre_sub vr hvr) x hx; omega)
        (Or.inr (by clear * - hbat_h hpre_bw_le hmoved_le; omega))
        (Or.inl (by omega))
    rw [hmem1]
    have h1 := hLatMR (vRunsEndsLen pre + best.2.length + t) hlt_raw
    rw [show hCur + (vRunsEndsLen pre + best.2.length) + t =
      hCur + (vRunsEndsLen pre + best.2.length + t) by omega, h1]
    simp only [hpack_raw_split]
    rw [List.getElem_append_right (by simp [vRunsPacked_length])]
    simp [vRunsPacked_length, show vRunsEndsLen pre + best.2.length + t -
      (vRunsEndsLen pre + best.2.length) = t by omega]
  obtain ⟨stEnd, cPost, hEnd, wPost, hrunPost, hregs2, hr4End, hhEnd_lo, hhEnd_hi, hwPost_le,
    hr21End, hr22End, _, hrepEnd, hbatEnd, hebEnd2, hfr2, hcPost⟩ :=
    bundleStepEmitCand_runsLoop (ω := ω) (degB := degB) (packArr := hCur)
      hpPush hpErase hw16 heCap_w hpk_w hprev_w hnext_w heb_w hp_w
      (by omega) hprev_next hblk_prev hblk_next heb_prev heb_next heb_blk
      (by omega) (by omega) (by omega) (by omega)
      post mid.1 mid.2.1 (nB + pre.length) (vRunsEndsLen pre + best.2.length)
      (writeOff + wPre) (updCnt + pre.length) h1 G₀ stPost0
      hV_m (by omega) (by omega) (by omega)
      (by clear * - hbat_w hwPre_le hpre_bw_le hpost_bw_le hmoved_le; omega)
      (by clear * - hupd_w hpre_len_le hpost_len_le hmoved_le; omega)
      (by clear * - hh_w hhP_hi hh1_hi hdeg_budget hmoved_le; omega)
      (fun vr hvr =>
        have hi := rawByRootVRuns_info vr (hpost_sub vr hvr)
        ⟨(hraw_pos vr (hpost_sub vr hvr)).1, hi.1, hi.2.1, hpost_in_mid vr hvr⟩)
      hpw_post hdisj_post
      ⟨xBest, hxBest_in_mid, fun vr hvr hmem => by
        have h1 := ((rawByRootVRuns_info vr (hpost_sub vr hvr)).2.2 xBest hmem).2
        have hlt := hpw_best_post vr hvr; omega⟩
      (by clear * - hbat_h hwPre_le hpre_bw_le hpost_bw_le hmoved_le; omega) (Or.inl (by omega))
      (by clear * - hbat_blk hwPre_le hpre_bw_le hpost_bw_le hmoved_le; omega)
      (by clear * - hbat_prev hwPre_le hpre_bw_le hpost_bw_le hmoved_le; omega)
      (by clear * - hbat_next hwPre_le hpre_bw_le hpost_bw_le hmoved_le; omega)
      (by clear * - hbat_eb hwPre_le hpre_bw_le hpost_bw_le hmoved_le; omega)
      (by clear * - hbat_h hhP_lo hh1_lo hwPre_le hpre_bw_le hpost_bw_le hmoved_le; omega)
      (by omega) (by omega) (by omega) (by omega)
      hrep1 hG_m hbat1 (by omega) hpack_post
      (by simp [stPost0, r29b, r26b, hr4_1])
      (by simp [stPost0, r29b, r26b, hregs1 6 (by decide) (by decide) (by decide) (by decide) (by decide), hPreReg 6 (by decide) (by decide), hr6])
      (by simp [stPost0, r29b, r26b, hregs1 7 (by decide) (by decide) (by decide) (by decide) (by decide), hPreReg 7 (by decide) (by decide), hr7])
      (by simp [stPost0, r29b, r26b, hregs1 8 (by decide) (by decide) (by decide) (by decide) (by decide), hPreReg 8 (by decide) (by decide), hr8])
      (by simp [stPost0, r29b, r26b, hregs1 9 (by decide) (by decide) (by decide) (by decide) (by decide), hPreReg 9 (by decide) (by decide), hr9])
      (by simp [stPost0, r29b, r26b, hregs1 10 (by decide) (by decide) (by decide) (by decide) (by decide), hPreReg 10 (by decide) (by decide), hr10])
      (by simp [stPost0, r29b, r26b, hregs1 11 (by decide) (by decide) (by decide) (by decide) (by decide), hPreReg 11 (by decide) (by decide), hr11])
      (by simp [stPost0, r29b, r26b, hregs1 20 (by decide) (by decide) (by decide) (by decide) (by decide), hPreReg 20 (by decide) (by decide), hr20])
      (by simp [stPost0, r29b, r26b, hr21_1])
      (by simp [stPost0, r29b, r26b, hr22_1])
      (by simp [stPost0, r29b, r26b, hregs1 25 (by decide) (by decide) (by decide) (by decide) (by decide),
        stPre0, r29a, r26a, r28a, r23a, hregsMR 25 (by decide) (by decide), hr25])
      (by simp [stPost0, r29b, r26b])
      (by simp [stPost0, r29b, r26b, hregs1 27 (by decide) (by decide) (by decide) (by decide) (by decide),
        stPre0, r29a, r26a, r28a, r23a, hr27MR])
      (by simp [stPost0, r29b])
  -- Connect to `runsFoldStep`
  have hfold_cat : foldOneSplitRuns b post (mid.1, mid.2.1, nB + pre.length) =
      foldOneSplitRuns b (pre ++ post) (ops, B0, nB) := by
    rw [foldOneSplitRuns_append, ← hmid_nB]
  obtain ⟨hfold_eq, _⟩ := runsFoldStep_eq_fold_oneRun (ops := ops) (B := B) (nB := nB) (b := b)
    (v0 := best.1) (xs0 := best.2) (rest := pre ++ post) hV hb_lt
  have hres_eq1 : (foldOneSplitRuns b post (mid.1, mid.2.1, nB + pre.length)).1 = res.1 := by
    rw [hfold_cat]; have := congrArg Prod.fst hfold_eq; simpa [res, vruns, hby_eq] using this
  have hres_eq2 : (foldOneSplitRuns b post (mid.1, mid.2.1, nB + pre.length)).2.1 = res.2 := by
    rw [hfold_cat]; have := congrArg Prod.snd hfold_eq; simpa [res, vruns, hby_eq] using this
  rw [hres_eq2] at hrepEnd hebEnd2
  rw [hres_eq1] at hbatEnd
  have hdisj_all := hdisj_of_pw (pre ++ post)
    (fun vr hvr => by rcases List.mem_append.mp hvr with h | h; exact hpre_sub vr h; exact hpost_sub vr h)
    (by rw [List.map_append, List.pairwise_append]
        exact ⟨hpw_pre, hpw_post, fun v1 hv1 v2 hv2 => by
          obtain ⟨vr1, h1, rfl⟩ := List.mem_map.mp hv1
          obtain ⟨vr2, h2, rfl⟩ := List.mem_map.mp hv2
          exact hpw_pre_post vr1 h1 vr2 h2⟩)
  obtain ⟨hV_f, hE_f, hG_f, hstay_f⟩ := foldOneSplitRuns_props (pre ++ post) G₀ ops B0 nB hV hb_lt hG₀
    (fun vr hvr x hx => ((rawByRootVRuns_info vr (by
      rcases List.mem_append.mp hvr with h | h; exact hpre_sub vr h; exact hpost_sub vr h)).2.2 x hx).1)
    hdisj_all hbo_lt'
  have hres_f1 : (foldOneSplitRuns b (pre ++ post) (ops, B0, nB)).1 = res.1 := hfold_cat ▸ hres_eq1
  have hres_f2 : (foldOneSplitRuns b (pre ++ post) (ops, B0, nB)).2.1 = res.2 := hfold_cat ▸ hres_eq2
  -- Frame + tour preservation
  have hfr_all : ∀ a, ¬ htour.rep.foot tourH tx₀ a →
      (a < p ∨ p + bundleSlotBlockSize bunCap ≤ a) →
      (∀ x ∈ B.ends b, a ≠ prevBase + endKey x ∧ a ≠ nextBase + endKey x ∧ a ≠ endBundleBase + endKey x) →
      (a < batchPtr + writeOff ∨ batchPtr + writeOff + 6 * m_b ≤ a) →
      (a < hCur ∨ hEnd ≤ a) → stEnd.mem a = st₀.mem a := fun a hnf haBlk haE haBat haH => by
    have h21 : stEnd.mem a = st1.mem a := hfr2 a haBlk
      (fun x hx => by
        have hxB : x ∈ B.ends b := by
          by_cases hxp : ∃ vr ∈ pre, x ∈ vr.2
          · obtain ⟨vr, hvr, hxvr⟩ := hxp; exact ((rawByRootVRuns_info vr (hpre_sub vr hvr)).2.2 x hxvr).1
          · rw [BundleState.mem_ends] at hx ⊢
            have hxE : x ∈ edgeEnds B.edges := (mem_edgeEnds _ _).mpr (hE_m ▸ hx.1)
            push Not at hxp
            exact ⟨hE_m ▸ hx.1, (hstay_m x hxE hxp).symm.trans hx.2⟩
        exact ⟨(haE x hxB).1, (haE x hxB).2.1⟩)
      (fun vr hvr x hx => (haE x ((rawByRootVRuns_info vr (hpost_sub vr hvr)).2.2 x hx).1).2.2)
      (by clear * - haBat hwPre_le hpre_bw_le hpost_bw_le hmoved_le; omega)
      (by clear * - haH hhP_lo hh1_lo hhEnd_lo; omega)
    have h10 : st1.mem a = stMR.mem a := hfr1 a haBlk (fun x hx => ⟨(haE x hx).1, (haE x hx).2.1⟩)
      (fun vr hvr x hx => (haE x ((rawByRootVRuns_info vr (hpre_sub vr hvr)).2.2 x hx).1).2.2)
      (by clear * - haBat hpre_bw_le hmoved_le; omega) (by clear * - haH hhP_lo hh1_lo hhEnd_lo; omega)
    have h00 : stMR.mem a = st₀.mem a := hfrMR a hnf (by clear * - haH hhP_lo hh1_lo hhEnd_lo; omega)
    exact h21.trans (h10.trans h00)
  have htour_agree : ∀ a, htour.rep.foot tourH txP a → stEnd.mem a = stMR.mem a := fun a ha => by
    have hsub := htfP a ha
    have hEnd_1 : stEnd.mem a = st1.mem a := hfr2 a
      (by rcases hsub with h0 | ⟨h1, _⟩; exact htfoot_disj_blk a h0; right; clear * - hh_blk h1; omega)
      (fun x hx => by
        have hxk : endKey x < 2 * eCap := by
          have := hE_lt x.1 (hE_m ▸ ((BundleState.mem_ends _ _ _).mp hx).1)
          rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
        rcases hsub with h0 | ⟨h1, _⟩
        · exact ⟨by have := htfoot_disj_prev a h0; omega, by have := htfoot_disj_next a h0; omega⟩
        · exact ⟨by clear * - hh_prev h1 hxk; omega, by clear * - hh_next h1 hxk; omega⟩)
      (fun vr hvr x hx => by
        have hxk := hraw_keys vr (hpost_sub vr hvr) x hx
        rcases hsub with h0 | ⟨h1, _⟩; have := htfoot_disj_eb a h0; omega; clear * - hh_eb h1 hxk; omega)
      (by rcases hsub with h0 | ⟨h1, _⟩
          · have := htfoot_disj_bat a h0; clear * - this hwPre_le hpre_bw_le hpost_bw_le hmoved_le; omega
          · clear * - hbat_h h1 hwPre_le hpre_bw_le hpost_bw_le hmoved_le; omega)
      (Or.inl (by rcases hsub with h0 | ⟨_, h2⟩; have := htfoot_lt a h0; clear * - this hhP_lo hh1_lo; omega; clear * - h2 hh1_lo; omega))
    have h1_MR : st1.mem a = stMR.mem a := hfr1 a
      (by rcases hsub with h0 | ⟨h1, _⟩; exact htfoot_disj_blk a h0; right; clear * - hh_blk h1; omega)
      (fun x hx => by
        have hxk : endKey x < 2 * eCap := by
          have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
          rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
        rcases hsub with h0 | ⟨h1, _⟩
        · exact ⟨by have := htfoot_disj_prev a h0; omega, by have := htfoot_disj_next a h0; omega⟩
        · exact ⟨by clear * - hh_prev h1 hxk; omega, by clear * - hh_next h1 hxk; omega⟩)
      (fun vr hvr x hx => by
        have hxk := hraw_keys vr (hpre_sub vr hvr) x hx
        rcases hsub with h0 | ⟨h1, _⟩; have := htfoot_disj_eb a h0; omega; clear * - hh_eb h1 hxk; omega)
      (by rcases hsub with h0 | ⟨h1, _⟩
          · have := htfoot_disj_bat a h0; clear * - this hpre_bw_le hmoved_le; omega
          · clear * - hbat_h h1 hpre_bw_le hmoved_le; omega)
      (Or.inl (by rcases hsub with h0 | ⟨_, h2⟩; have := htfoot_lt a h0; clear * - this hhP_lo; omega; clear * - h2; omega))
    exact hEnd_1.trans h1_MR
  have hlocEnd := htour.rep_local tourH cord' txP stMR.mem stEnd.mem fun a ha => (htour_agree a ha).symm
  -- Assemble full `Runs`
  have htail2 := bundle_runs_seq_normal ha26b (bundle_runs_seq_normal ha29b hrunPost)
  have htail1 := bundle_runs_seq_normal ha23 (bundle_runs_seq_normal ha28a (bundle_runs_seq_normal ha26a
    (bundle_runs_seq_normal ha29a (bundle_runs_seq_normal hrunPre htail2))))
  have haddU_eq : addedUpds = pre.length + post.length := by simp [addedUpds, vruns, hby_eq]
  refine ⟨stEnd, _, txP, hEnd, wPre + wPost, hrunPref htail1,
    fun r hr h4 h21 h22 h23 => by
      rw [hregs2 r (by omega) h4 h21 h22 (by omega)]
      simp only [stPost0, r29b, r26b, Function.update_of_ne (show r ≠ 29 by omega),
        Function.update_of_ne (show r ≠ 26 by omega)]
      rw [hregs1 r (by omega) h4 h21 h22 (by omega)]
      by_cases hr24 : r = 24
      · subst hr24
        simp [stPre0, r29a, r26a, r28a, r23a, hregsMR 24 (by decide) (by decide)]
      · exact hPreReg r (by omega) h4,
    hr4End, by clear * - hhP_lo hh1_lo hhEnd_lo; omega,
    by clear * - hhP_hi hh1_hi hhEnd_hi hdeg_budget hmoved_le; omega,
    by rw [hr21End]; clear * -; omega,
    by rw [hr22End, haddU_eq]; clear * -; omega,
    by clear * - hwPre_le hwPost_le hpre_bw_le hpost_bw_le hmoved_le; omega,
    by clear * - haddU_eq hpre_len_le hpost_len_le hmoved_le; omega,
    by rw [← hres_f2]; simpa [haddU_eq] using hV_f,
    hrepEnd,
    by rw [← hres_f1, ← hres_f2]; exact hG_f,
    by rw [show writeOff + (wPre + wPost) - 1 = writeOff + wPre + wPost - 1 by clear * -; omega]; exact hbatEnd,
    ?_,
    hlocEnd.1 htrMR,
    fun a ha => by rcases htfP a ha with h0 | ⟨h1, h2⟩; exact Or.inl h0; exact Or.inr ⟨by clear * - h1; omega, by clear * - h2 hh1_lo hhEnd_lo; omega⟩,
    fun a ha => by
      refine (hfr_all a (fun hf => by have := htfoot_lt a hf; clear * - this hhP_lo hh1_lo hhEnd_lo ha; omega)
        (by clear * - hh_blk hhP_lo hh1_lo hhEnd_lo ha; omega)
        (fun x hx => by
          have hxk : endKey x < 2 * eCap := by
            have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
            rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
          exact ⟨by clear * - hh_prev hhP_lo hh1_lo hhEnd_lo hxk ha; omega,
                 by clear * - hh_next hhP_lo hh1_lo hhEnd_lo hxk ha; omega,
                 by clear * - hh_eb hhP_lo hh1_lo hhEnd_lo hxk ha; omega⟩)
        (by clear * - hbat_h hhP_lo hh1_lo hhEnd_lo ha; omega) (Or.inr ha)).trans
        (hzero a (by clear * - hhP_lo hh1_lo hhEnd_lo ha; omega)),
    hfr_all, ?_⟩
  · intro x hx
    have hxE : x ∈ edgeEnds res.2.edges := by
      rw [← hres_f2, hE_f]; exact (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp hx).1
    by_cases hxpost : ∃ vr ∈ post, x ∈ vr.2
    · left; exact hebEnd2 x hxE hxpost
    · push Not at hxpost
      have hxk : endKey x < 2 * eCap := by
        have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
        rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
      have hmem_2 : stEnd.mem (endBundleBase + endKey x) = st1.mem (endBundleBase + endKey x) :=
        hfr2 _ (by unfold bundleSlotBlockSize at heb_blk ⊢; clear * - heb_blk hxk; omega)
          (fun y hy => by
            have hyk : endKey y < 2 * eCap := by
              have := hE_lt y.1 (hE_m ▸ ((BundleState.mem_ends _ _ _).mp hy).1)
              rcases y with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
            exact ⟨by clear * - heb_prev hxk hyk; omega, by clear * - heb_next hxk hyk; omega⟩)
          (fun vr hvr y hy heq => hxpost vr hvr ((endKey_injective (by omega : endKey x = endKey y)) ▸ hy))
          (by clear * - hbat_eb hwPre_le hpre_bw_le hpost_bw_le hmoved_le hxk; omega)
          (Or.inl (by omega))
      by_cases hxpre : ∃ vr ∈ pre, x ∈ vr.2
      · left
        rw [hmem_2, heb1 x (by rw [hE_m]; exact (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp hx).1) hxpre]
        obtain ⟨_, _, _, hstay_2⟩ := foldOneSplitRuns_props post G₀ mid.1 mid.2.1 (nB + pre.length)
          hV_m (by omega) hG_m hpost_in_mid hdisj_post
          (by have hV1 := hrep1.choose_spec.1
              have heq : hrep1.choose = nB + pre.length := by
                have := congrArg Finset.card (hV1.symm.trans hV_m); simpa [Finset.card_range] using this
              rw [← heq]; exact hrep1.choose_spec.2.2.2.1)
        rw [← hres_eq2]
        exact (hstay_2 x (by rw [hE_m]; exact (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp hx).1) hxpost).symm
      · right
        push Not at hxpre
        have hmem_1 : st1.mem (endBundleBase + endKey x) = st₀.mem (endBundleBase + endKey x) := by
          rw [hfr1 (endBundleBase + endKey x) (by unfold bundleSlotBlockSize at heb_blk ⊢; clear * - heb_blk hxk; omega)
              (fun y hy => by
                have hyk : endKey y < 2 * eCap := by
                  have := hE_lt y.1 ((BundleState.mem_ends B b y).mp hy).1
                  rcases y with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
                exact ⟨by clear * - heb_prev hxk hyk; omega, by clear * - heb_next hxk hyk; omega⟩)
              (fun vr hvr y hy heq => hxpre vr hvr ((endKey_injective (by omega : endKey x = endKey y)) ▸ hy))
              (by clear * - hbat_eb hpre_bw_le hmoved_le hxk; omega)
              (Or.inl (by omega))]
          exact hrepMR_mem _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
        have hxE0 : x ∈ edgeEnds B.edges := (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp hx).1
        refine ⟨?_, hmem_2.trans hmem_1⟩
        rw [← hres_f2, hstay_f x hxE0 (fun vr hvr => by
          rcases List.mem_append.mp hvr with h | h; exact hxpre vr h; exact hxpost vr h)]
        exact ((BundleState.mem_ends B b x).mp hx).2
  · rw [hlocEnd.2.symm]
    have hmul_tot : (2 * TS.mul * ordStoreLog eCap + 400 * (Nat.log 2 (2 * m_b + 1) + 1) + 820) * m_b =
        (2 * TS.mul * ordStoreLog eCap + 400 * (Nat.log 2 (2 * m_b + 1) + 1) + 250) * m_b + 570 * m_b := by ring
    clear * - hcPref hcPre hcPost hmoved_le hmul_tot
    omega

end

end MinCostFlow.SparseCore.Program
