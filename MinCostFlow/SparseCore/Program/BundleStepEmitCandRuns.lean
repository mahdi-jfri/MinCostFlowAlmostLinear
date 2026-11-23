module

public import MinCostFlow.SparseCore.Program.BundleStepEmitCandPack

/-!
# Phase 3 multi-run emission loop (`BundleStepEmitCandRuns`)

Verifies the outer `.loop (.bin .lt (.reg 29) (.reg 26)) (bundleStepEmitOneRunStmt ...)` of
`bundleStepEmitOneCandStmt` over `rest = vruns.drop 1`, accumulating `BatchBodyAt` and preserving
`BundleSlotRepAt`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

/-! ## 3. Multi-run emission loop (`bundleStepEmitCand_runsLoop`) -/

lemma foldOneSplitRuns_props {b : ℕ} :
    ∀ (rs : List (ℕ × List End)) (G₀ : MGraph) (ops : List Update) (B : BundleState) (nB : ℕ),
      B.vertices = Finset.range nB → b < nB → G₀.applyBatch ops = B.graph →
      (∀ vr ∈ rs, ∀ y ∈ vr.2, y ∈ B.ends b) →
      (∀ i j (hi : i < rs.length) (hj : j < rs.length), i ≠ j → ∀ y ∈ rs[i].2, y ∉ rs[j].2) →
      (∀ y ∈ edgeEnds B.edges, B.bundleOf y < nB) →
      let r := foldOneSplitRuns b rs (ops, B, nB)
      r.2.1.vertices = Finset.range (nB + rs.length) ∧
      r.2.1.edges = B.edges ∧
      G₀.applyBatch r.1 = r.2.1.graph ∧
      (∀ x ∈ edgeEnds B.edges, (∀ vr ∈ rs, x ∉ vr.2) → r.2.1.bundleOf x = B.bundleOf x)
  | [], _, _, _, _, hV, _, hG, _, _, _ => ⟨by simpa [foldOneSplitRuns] using hV, rfl, hG, fun _ _ _ => rfl⟩
  | (vCur, xs) :: tl, G₀, ops, B, nB, hV, hb, hG, hsub, hdisj, hbo_lt => by
    have hxs_sub : ∀ y ∈ xs, y ∈ B.ends b := hsub (vCur, xs) List.mem_cons_self
    obtain ⟨hV1, hE1, hsrc1, hG1⟩ := oneRunUpdate_graph_apply B hV hb hxs_sub
    obtain ⟨hends_b1, _, _⟩ := applyOneSplitRun_ends hV hb hbo_lt hxs_sub
    have htl_sub : ∀ vr ∈ tl, ∀ y ∈ vr.2, y ∈ (applyOneSplitRun B b nB vCur xs).2.ends b := by
      intro vr hvr y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvr
      rw [hends_b1, Finset.mem_sdiff, List.mem_toFinset]
      exact ⟨hsub _ (List.mem_cons_of_mem _ (List.getElem_mem hj)) y hy,
        fun hyxs => hdisj 0 (j + 1) (by simp) (by simp; omega) (by omega) y hyxs hy⟩
    have hdisj_tl : ∀ i j (hi : i < tl.length) (hj : j < tl.length), i ≠ j → ∀ y ∈ tl[i].2, y ∉ tl[j].2 :=
      fun i j hi hj h => hdisj (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
    have hbo1_lt : ∀ y ∈ edgeEnds (applyOneSplitRun B b nB vCur xs).2.edges,
        (applyOneSplitRun B b nB vCur xs).2.bundleOf y < nB + 1 := fun y hy => by
      rw [hE1] at hy; rw [hsrc1 y hy]; split_ifs
      · omega
      · exact Nat.lt_succ_of_lt (hbo_lt y hy)
    have hG1' : G₀.applyBatch (ops ++ [(applyOneSplitRun B b nB vCur xs).1]) =
        (applyOneSplitRun B b nB vCur xs).2.graph := by
      simp only [MGraph.applyBatch, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [show List.foldl MGraph.applyUpdate G₀ ops = B.graph from hG]; exact hG1.symm
    have ih := foldOneSplitRuns_props tl G₀ (ops ++ [(applyOneSplitRun B b nB vCur xs).1])
      (applyOneSplitRun B b nB vCur xs).2 (nB + 1) hV1 (by omega) hG1' htl_sub hdisj_tl hbo1_lt
    refine ⟨?_, ih.2.1.trans hE1, ih.2.2.1, fun x hx hnot => ?_⟩
    · simp only [foldOneSplitRuns, List.length_cons]
      convert ih.1 using 2; omega
    · have h1 := ih.2.2.2 x (hE1 ▸ hx) (fun vr hvr => hnot vr (List.mem_cons_of_mem _ hvr))
      rw [hsrc1 x hx, ite_eq_right (hnot (vCur, xs) List.mem_cons_self)] at h1
      exact h1

private lemma foldOneSplitRuns_preserves_ne {b : ℕ} :
    ∀ (rs : List (ℕ × List End)) (ops : List Update) (B : BundleState) (nB : ℕ) (x : End),
      B.vertices = Finset.range nB → b < nB →
      (∀ vr ∈ rs, ∀ y ∈ vr.2, y ∈ B.ends b) →
      (∀ i j (hi : i < rs.length) (hj : j < rs.length), i ≠ j → ∀ y ∈ rs[i].2, y ∉ rs[j].2) →
      (∀ y ∈ edgeEnds B.edges, B.bundleOf y < nB) →
      B.bundleOf x ≠ b → x ∈ edgeEnds B.edges →
      (foldOneSplitRuns b rs (ops, B, nB)).2.1.edges = B.edges ∧
      (foldOneSplitRuns b rs (ops, B, nB)).2.1.bundleOf x = B.bundleOf x
  | [], _, _, _, _, _, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | (vCur, xs) :: tl, ops, B, nB, x, hV, hb, hsub, hdisj, hbo_lt, hne, hxE => by
    have hxs_sub : ∀ y ∈ xs, y ∈ B.ends b := hsub (vCur, xs) List.mem_cons_self
    obtain ⟨hV1, hE1, hsrc1, _⟩ := oneRunUpdate_graph_apply B hV hb hxs_sub
    obtain ⟨hends_b1, _, _⟩ := applyOneSplitRun_ends hV hb hbo_lt hxs_sub
    have hx_notin : x ∉ xs := fun hx => hne ((BundleState.mem_ends B b x).mp (hxs_sub x hx)).2
    have hbo1 : (applyOneSplitRun B b nB vCur xs).2.bundleOf x = B.bundleOf x := by
      rw [hsrc1 x hxE, ite_eq_right hx_notin]
    have htl_sub : ∀ vr ∈ tl, ∀ y ∈ vr.2, y ∈ (applyOneSplitRun B b nB vCur xs).2.ends b := by
      intro vr hvr y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvr
      rw [hends_b1, Finset.mem_sdiff, List.mem_toFinset]
      exact ⟨hsub _ (List.mem_cons_of_mem _ (List.getElem_mem hj)) y hy,
        fun hyxs => hdisj 0 (j + 1) (by simp) (by simp; omega) (by omega) y hyxs hy⟩
    have hdisj_tl : ∀ i j (hi : i < tl.length) (hj : j < tl.length), i ≠ j → ∀ y ∈ tl[i].2, y ∉ tl[j].2 :=
      fun i j hi hj h => hdisj (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
    have hbo1_lt : ∀ y ∈ edgeEnds (applyOneSplitRun B b nB vCur xs).2.edges,
        (applyOneSplitRun B b nB vCur xs).2.bundleOf y < nB + 1 := fun y hy => by
      rw [hE1] at hy; rw [hsrc1 y hy]; split_ifs
      · omega
      · exact Nat.lt_succ_of_lt (hbo_lt y hy)
    have ih := foldOneSplitRuns_preserves_ne tl (ops ++ [(applyOneSplitRun B b nB vCur xs).1])
      (applyOneSplitRun B b nB vCur xs).2 (nB + 1) x hV1 (by omega) htl_sub hdisj_tl hbo1_lt
      (hbo1 ▸ hne) (hE1 ▸ hxE)
    exact ⟨ih.1.trans hE1, ih.2.trans hbo1⟩

lemma bundleStepEmitCand_runsLoop {w eCap vCap p bunCap b degB packArr batchPtr
    prevBase nextBase endBundleBase : ℕ}
    {pProg : Program} {bDllPush bDllErase : ℕ} {ω : ℕ → Bool}
    (hpPush : pProg.HasAt bDllPush [bundleDllPushStmt])
    (hpErase : pProg.HasAt bDllErase [bundleDllEraseStmt])
    (hw16 : 16 ≤ 2 ^ w) (heCap_w : 2 * eCap < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (hprev_w : prevBase + 2 * eCap < 2 ^ w) (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (heb_w : endBundleBase + 2 * eCap < 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hpack_w : packArr + degB < 2 ^ w)
    (hprev_next : prevBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ prevBase)
    (hblk_prev : p + bundleSlotBlockSize bunCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ p)
    (hblk_next : p + bundleSlotBlockSize bunCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ p)
    (heb_prev : endBundleBase + 2 * eCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ endBundleBase)
    (heb_next : endBundleBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ endBundleBase)
    (heb_blk : endBundleBase + 2 * eCap ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ endBundleBase)
    (hpack_disj_blk : packArr + degB ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ packArr)
    (hpack_disj_prev : packArr + degB ≤ prevBase ∨ prevBase + 2 * eCap ≤ packArr)
    (hpack_disj_next : packArr + degB ≤ nextBase ∨ nextBase + 2 * eCap ≤ packArr)
    (hpack_disj_eb : packArr + degB ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ packArr) :
    ∀ (rest : List (ℕ × List End)) (ops : List Update) (B : BundleState) (nB idx writeOff updCnt hCur : ℕ)
      (G₀ : MGraph) (st₀ : State),
      B.vertices = Finset.range nB → b < nB → nB + rest.length ≤ bunCap →
      idx + vRunsEndsLen rest = degB →
      batchPtr + writeOff + vRunsBatchWords rest < 2 ^ w →
      updCnt + rest.length < 2 ^ w →
      hCur + 2 * vRunsEndsLen rest < 2 ^ w →
      (∀ vr ∈ rest, vr.1 < vCap ∧ 0 < vr.2.length ∧ vr.2.Nodup ∧ ∀ x ∈ vr.2, x ∈ B.ends b) →
      (rest.map Prod.fst).Pairwise (· < ·) →
      (∀ i j (hi : i < rest.length) (hj : j < rest.length), i ≠ j →
        ∀ x ∈ rest[i].2, x ∉ rest[j].2) →
      (∃ y ∈ B.ends b, ∀ vr ∈ rest, y ∉ vr.2) →
      (packArr + degB ≤ batchPtr ∨ batchPtr + writeOff + vRunsBatchWords rest ≤ packArr) →
      (packArr + degB ≤ hCur ∨ hCur + 2 * vRunsEndsLen rest ≤ packArr) →
      (batchPtr + writeOff + vRunsBatchWords rest ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ batchPtr) →
      (batchPtr + writeOff + vRunsBatchWords rest ≤ prevBase ∨ prevBase + 2 * eCap ≤ batchPtr) →
      (batchPtr + writeOff + vRunsBatchWords rest ≤ nextBase ∨ nextBase + 2 * eCap ≤ batchPtr) →
      (batchPtr + writeOff + vRunsBatchWords rest ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ batchPtr) →
      (batchPtr + writeOff + vRunsBatchWords rest ≤ hCur ∨ hCur + 2 * vRunsEndsLen rest ≤ batchPtr) →
      (hCur + 2 * vRunsEndsLen rest ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ hCur) →
      (hCur + 2 * vRunsEndsLen rest ≤ prevBase ∨ prevBase + 2 * eCap ≤ hCur) →
      (hCur + 2 * vRunsEndsLen rest ≤ nextBase ∨ nextBase + 2 * eCap ≤ hCur) →
      (hCur + 2 * vRunsEndsLen rest ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ hCur) →
      BundleSlotRepAt eCap prevBase nextBase p bunCap B st₀.mem →
      G₀.applyBatch ops = B.graph →
      SmallBatchBodyAt st₀.mem (batchPtr + 1) G₀ ops (writeOff - 1) → 1 ≤ writeOff →
      ListAt st₀.mem (packArr + idx) (vRunsPacked eCap rest) →
      st₀.regs 4 = hCur → st₀.regs 6 = 2 * eCap → st₀.regs 7 = p → st₀.regs 8 = bunCap →
      st₀.regs 9 = endBundleBase → st₀.regs 10 = prevBase → st₀.regs 11 = nextBase →
      st₀.regs 20 = batchPtr → st₀.regs 21 = writeOff → st₀.regs 22 = updCnt →
      st₀.regs 25 = b → st₀.regs 26 = degB → st₀.regs 27 = packArr → st₀.regs 29 = idx →
      let res := foldOneSplitRuns b rest (ops, B, nB)
      ∃ stEnd cEnd hEnd addedWords,
        Runs w pProg ω (.loop (.bin .lt (.reg 29) (.reg 26))
          (bundleStepEmitOneRunStmt bDllPush bDllErase)) st₀ .normal stEnd cEnd ∧
        (∀ r ≤ 29, r ≠ 4 → r ≠ 21 → r ≠ 22 → r ≠ 29 → stEnd.regs r = st₀.regs r) ∧
        stEnd.regs 4 = hEnd ∧ hCur ≤ hEnd ∧ hEnd ≤ hCur + 2 * vRunsEndsLen rest ∧
        addedWords ≤ vRunsBatchWords rest ∧
        stEnd.regs 21 = writeOff + addedWords ∧
        stEnd.regs 22 = updCnt + rest.length ∧
        stEnd.regs 29 = degB ∧
        BundleSlotRepAt eCap prevBase nextBase p bunCap res.2.1 stEnd.mem ∧
        SmallBatchBodyAt stEnd.mem (batchPtr + 1) G₀ res.1 (writeOff + addedWords - 1) ∧
        (∀ x ∈ edgeEnds res.2.1.edges,
          (∃ vr ∈ rest, x ∈ vr.2) → stEnd.mem (endBundleBase + endKey x) = res.2.1.bundleOf x) ∧
        (∀ a, (a < p ∨ p + bundleSlotBlockSize bunCap ≤ a) →
          (∀ x ∈ B.ends b, a ≠ prevBase + endKey x ∧ a ≠ nextBase + endKey x) →
          (∀ vr ∈ rest, ∀ x ∈ vr.2, a ≠ endBundleBase + endKey x) →
          (a < batchPtr + writeOff ∨ batchPtr + writeOff + vRunsBatchWords rest ≤ a) →
          (a < hCur ∨ hEnd ≤ a) →
          stEnd.mem a = st₀.mem a) ∧
        cEnd ≤ 570 * vRunsEndsLen rest + 5 := by
  intro rest
  induction rest with
  | nil =>
    intro ops B nB idx writeOff updCnt hCur G₀ st₀ _ _ _ hidx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hrep _ hbat _ _ hr4 _ _ _ _ _ _ _ hr21 hr22 _ hr26 _ hr29
    simp only [foldOneSplitRuns, vRunsEndsLen, vRunsBatchWords, List.map_nil, List.sum_nil,
      add_zero, List.length_nil] at hidx ⊢
    refine ⟨st₀, 4, hCur, 0,
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr29, hr26, hidx, show 0 < 2 ^ w by omega],
        rfl, rfl, rfl⟩),
      fun _ _ _ _ _ _ => rfl, hr4, le_refl _, le_refl _, le_refl _, hr21, hr22, hr29.trans hidx,
      hrep, hbat, (fun _ _ ⟨_, h, _⟩ => by cases h), fun _ _ _ _ _ _ => rfl, by omega⟩
  | cons hd tl ih =>
    rcases hd with ⟨vCur, xs⟩
    intro ops B nB idx writeOff updCnt hCur G₀ st₀ hV hb hnb hidx hbat_w hupd_w hh_w hinfo hpw hdisj
      hkeep hpb hph hbb hbp hbn hbe hbh hhb hhp hhn hhe hrep hG₀ hbat hw1 hpack
      hr4 hr6 hr7 hr8 hr9 hr10 hr11 hr20 hr21 hr22 hr25 hr26 hr27 hr29
    have hhd := hinfo (vCur, xs) List.mem_cons_self
    dsimp only at hhd
    rcases hhd with ⟨hv_lt, hxs_pos, hxs_nd, hxs_sub⟩
    have hE_lt : ∀ e ∈ B.edges, e < eCap := hrep.choose_spec.2.2.1
    have hbo_lt : ∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB := by
      have hV' := hrep.choose_spec.1
      have hnB_eq : hrep.choose = nB := by
        have := congrArg Finset.card (hV'.symm.trans hV); simpa [Finset.card_range] using this
      rw [← hnB_eq]; exact hrep.choose_spec.2.2.2.1
    have hpk_bound : (vCur + 1) * (2 * eCap) ≤ 2 ^ w := by
      have := Nat.mul_le_mul_right (2 * eCap) (show vCur + 1 ≤ vCap by omega); omega
    have hlen_cons : vRunsEndsLen ((vCur, xs) :: tl) = xs.length + vRunsEndsLen tl := by
      simp [vRunsEndsLen]
    have hbw_cons : vRunsBatchWords ((vCur, xs) :: tl) = (5 + xs.length) + vRunsBatchWords tl := by
      simp [vRunsBatchWords]
    rw [hlen_cons] at hidx hh_w hph hbh hhb hhp hhn hhe
    rw [hbw_cons] at hbat_w hpb hbb hbp hbn hbe hbh
    have hpack_in : ∀ t (ht : t < xs.length),
        st₀.mem (packArr + (idx + t)) = packEndKey eCap vCur (endKey xs[t]) := fun t ht => by
      have h1 := hpack t (by rw [vRunsPacked_length, hlen_cons]; omega)
      simp only [vRunsPacked, List.flatMap_cons] at h1
      rw [List.getElem_append_left (by simp; omega), List.getElem_map] at h1
      simpa [Nat.add_assoc] using h1
    have hpack_end : idx + xs.length < degB →
        st₀.mem (packArr + (idx + xs.length)) / (2 * eCap) ≠ vCur ∧
        st₀.mem (packArr + (idx + xs.length)) < 2 ^ w := fun hlt => by
      cases tl with
      | nil => simp [vRunsEndsLen] at hidx; omega
      | cons vr' tl' =>
        have hvr' := hinfo vr' (List.mem_cons_of_mem _ List.mem_cons_self)
        have h1 := hpack xs.length (by rw [vRunsPacked_length, hlen_cons]; simp [vRunsEndsLen]; omega)
        simp only [vRunsPacked, List.flatMap_cons] at h1
        rw [List.getElem_append_right (by simp), List.getElem_append_left (by simp; omega),
          List.getElem_map] at h1
        have hsub0 : xs.length - (xs.map fun x => packEndKey eCap vCur (endKey x)).length = 0 := by simp
        simp only [hsub0] at h1
        have hx0_lt : endKey (vr'.2[0]'hvr'.2.1) < 2 * eCap := by
          have hlt0 := hE_lt _ ((BundleState.mem_ends B b _).mp (hvr'.2.2.2 _ (List.getElem_mem hvr'.2.1))).1
          generalize vr'.2[0]'hvr'.2.1 = q at hlt0 ⊢
          rcases q with ⟨ee, side⟩; cases side <;> simp [endKey] at hlt0 ⊢ <;> omega
        rw [Nat.add_assoc] at h1
        refine ⟨?_, ?_⟩
        · rw [h1, packEndKey_div hx0_lt]
          have hlt_v : vCur < vr'.1 := (List.pairwise_cons.mp hpw).1 vr'.1 (List.mem_map.mpr ⟨vr', List.mem_cons_self, rfl⟩)
          omega
        · rw [h1]; unfold packEndKey
          have := Nat.mul_le_mul_right (2 * eCap) (show vr'.1 + 1 ≤ vCap by omega)
          rw [Nat.add_mul, Nat.one_mul] at this; omega
    obtain ⟨yKeep, hyKeepB, hyKeepNot⟩ := hkeep
    -- Run one iteration via `bundleStepEmitOneRun_runs`
    obtain ⟨st1, c1, hEnd1, len1, hrun1, hregs1, hr4_1, hh1_lo, hh1_hi, hlen1_le, hr21_1, hr22_1,
      hr29_1, hrep1, hupd1, heb1, hfr1, hc1⟩ :=
      bundleStepEmitOneRun_runs hpPush hpErase hw16 heCap_w hpk_bound hprev_w hnext_w heb_w hp_w
        hpack_w (by clear * - hbat_w hbw_cons; omega) (by clear * - hupd_w; simp only [List.length_cons] at hupd_w; omega)
        (by clear * - hh_w hlen_cons; omega) hV hb (by clear * - hnb; simp only [List.length_cons] at hnb; omega)
        (by clear * - hidx hlen_cons; omega) hxs_pos hxs_nd hxs_sub ⟨yKeep, hyKeepB, hyKeepNot _ List.mem_cons_self⟩
        hprev_next hblk_prev hblk_next heb_prev heb_next heb_blk hpack_disj_blk hpack_disj_prev
        hpack_disj_next hpack_disj_eb (by clear * - hpb hbw_cons; omega) (by clear * - hph hlen_cons; omega)
        (by clear * - hbb hbw_cons; omega) (by clear * - hbp hbw_cons; omega)
        (by clear * - hbn hbw_cons; omega) (by clear * - hbe hbw_cons; omega)
        (by clear * - hbh hbw_cons hlen_cons; omega) (by clear * - hhb hlen_cons; omega)
        (by clear * - hhp hlen_cons; omega) (by clear * - hhn hlen_cons; omega)
        (by clear * - hhe hlen_cons; omega) hrep hpack_in hpack_end
        hr4 hr6 hr7 hr8 hr9 hr10 hr11 hr20 hr21 hr22 hr25 hr26 hr27 hr29
    set res1 := applyOneSplitRun B b nB vCur xs
    obtain ⟨hV1, hE1, hsrc1, hG1⟩ := oneRunUpdate_graph_apply B hV hb hxs_sub
    obtain ⟨hends_b1, _, _⟩ := applyOneSplitRun_ends hV hb hbo_lt hxs_sub
    have hB_end_lt : ∀ x ∈ B.ends b, endKey x < 2 * eCap := fun x hx => by
      have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx).1
      rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
    have hbat_pre1 : SmallBatchBodyAt st1.mem (batchPtr + 1) G₀ ops (writeOff - 1) :=
      smallBatchBodyAt_agree hbat fun a ha1 ha2 =>
        hfr1 a (by clear * - hbb hbw_cons ha1 ha2; omega)
          (fun x hx => by have := hB_end_lt x hx; exact ⟨by clear * - hbp hbw_cons this ha1 ha2; omega, by clear * - hbn hbw_cons this ha1 ha2; omega⟩)
          (fun x hx => by have := hB_end_lt x (hxs_sub x hx); clear * - hbe hbw_cons this ha1 ha2; omega)
          (Or.inl (by omega)) (by clear * - hbh hbw_cons hh1_hi hlen_cons ha1 ha2; omega)
    have hbat1 : SmallBatchBodyAt st1.mem (batchPtr + 1) G₀ (ops ++ [res1.1]) (writeOff + len1 - 1) := by
      have hsub : writeOff + len1 - 1 = (writeOff - 1) + len1 := by omega
      rw [hsub]
      refine bundle_smallBatchBodyAt_snoc hbat_pre1 ?_
      have haddr : batchPtr + 1 + (writeOff - 1) = batchPtr + writeOff := by omega
      rw [haddr, hG₀]; exact hupd1
    have hG1' : G₀.applyBatch (ops ++ [res1.1]) = res1.2.graph := by
      simp only [MGraph.applyBatch, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [show List.foldl MGraph.applyUpdate G₀ ops = B.graph from hG₀]; exact hG1.symm
    have hpack_tl : ListAt st1.mem (packArr + (idx + xs.length)) (vRunsPacked eCap tl) := fun t ht => by
      rw [vRunsPacked_length] at ht
      have h1 := hfr1 (packArr + (idx + xs.length) + t)
        (by clear * - hpack_disj_blk hidx hlen_cons ht; omega)
        (fun x hx => by have := hB_end_lt x hx; exact ⟨by clear * - hpack_disj_prev this hidx hlen_cons ht; omega, by clear * - hpack_disj_next this hidx hlen_cons ht; omega⟩)
        (fun x hx => by have := hB_end_lt x (hxs_sub x hx); clear * - hpack_disj_eb this hidx hlen_cons ht; omega)
        (by clear * - hpb hbw_cons hidx hlen_cons ht; omega)
        (by clear * - hph hh1_hi hidx hlen_cons ht; omega)
      rw [h1]
      have h2 := hpack (xs.length + t) (by rw [vRunsPacked_length, hlen_cons]; omega)
      simp only [vRunsPacked, List.flatMap_cons] at h2
      rw [List.getElem_append_right (by simp)] at h2
      have hsub : xs.length + t - (xs.map fun x => packEndKey eCap vCur (endKey x)).length = t := by simp
      simp only [hsub, Nat.add_assoc] at h2 ⊢
      exact h2
    have htl_info : ∀ vr ∈ tl, vr.1 < vCap ∧ 0 < vr.2.length ∧ vr.2.Nodup ∧ ∀ x ∈ vr.2, x ∈ res1.2.ends b := by
      intro vr hvr
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvr
      have hbase := hinfo (tl[j]'hj) (List.mem_cons_of_mem _ (List.getElem_mem hj))
      refine ⟨hbase.1, hbase.2.1, hbase.2.2.1, fun x hx => ?_⟩
      rw [hends_b1, Finset.mem_sdiff, List.mem_toFinset]
      refine ⟨hbase.2.2.2 x hx, fun hxxs => hdisj 0 (j + 1) (by simp) (by simp; omega) (by omega) x hxxs hx⟩
    have hkeep1 : ∃ y ∈ res1.2.ends b, ∀ vr ∈ tl, y ∉ vr.2 :=
      ⟨yKeep, by rw [hends_b1, Finset.mem_sdiff, List.mem_toFinset]; exact ⟨hyKeepB, hyKeepNot _ List.mem_cons_self⟩,
        fun vr hvr => hyKeepNot vr (List.mem_cons_of_mem _ hvr)⟩
    have hdisj_tl : ∀ i j (hi : i < tl.length) (hj : j < tl.length), i ≠ j → ∀ x ∈ tl[i].2, x ∉ tl[j].2 :=
      fun i j hi hj hne => hdisj (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
    obtain ⟨stEnd, cEnd, hEnd, addedTl, hrunEnd, hregsEnd, hr4End, hhEnd_lo, hhEnd_hi, haddTl_le,
      hr21End, hr22End, hr29End, hrepEnd, hbatEnd, hebEnd, hfrEnd, hcEnd⟩ :=
      ih (ops ++ [res1.1]) res1.2 (nB + 1) (idx + xs.length) (writeOff + len1)
        (updCnt + 1) hEnd1 G₀ st1 hV1 (by omega) (by simp only [List.length_cons] at hnb; omega)
        (by omega) (by clear * - hbat_w hbw_cons hlen1_le; omega) (by simp only [List.length_cons] at hupd_w; omega)
        (by clear * - hh_w hlen_cons hh1_hi; omega) htl_info (List.pairwise_cons.mp hpw).2 hdisj_tl hkeep1
        (by clear * - hpb hbw_cons hlen1_le; omega) (by clear * - hph hlen_cons hh1_lo hh1_hi; omega)
        (by clear * - hbb hbw_cons hlen1_le; omega) (by clear * - hbp hbw_cons hlen1_le; omega)
        (by clear * - hbn hbw_cons hlen1_le; omega) (by clear * - hbe hbw_cons hlen1_le; omega)
        (by clear * - hbh hbw_cons hlen_cons hlen1_le hh1_lo hh1_hi; omega)
        (by clear * - hhb hlen_cons hh1_lo hh1_hi; omega)
        (by clear * - hhp hlen_cons hh1_lo hh1_hi; omega) (by clear * - hhn hlen_cons hh1_lo hh1_hi; omega)
        (by clear * - hhe hlen_cons hh1_lo hh1_hi; omega) hrep1 hG1' hbat1 (by omega) hpack_tl
        hr4_1 ((hregs1 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr6)
        ((hregs1 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr7)
        ((hregs1 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr8)
        ((hregs1 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr9)
        ((hregs1 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr10)
        ((hregs1 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr11)
        ((hregs1 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr20)
        hr21_1 hr22_1
        ((hregs1 25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr25)
        ((hregs1 26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr26)
        ((hregs1 27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr27) hr29_1
    have hcond : Expr.eval w st₀ (.bin .lt (.reg 29) (.reg 26)) = some 1 := by
      simp [Expr.eval, BinOp.eval, hr29, hr26, show idx < degB by omega, show 1 < 2 ^ w by omega]
    refine ⟨stEnd, 3 + c1 + cEnd + 1, hEnd, len1 + addedTl,
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, c1, cEnd, hcond, by decide, hrun1, hrunEnd, rfl⟩)),
      fun r hr h4 h21 h22 h29 => (hregsEnd r hr h4 h21 h22 h29).trans (hregs1 r hr h4 h21 h22 h29),
      hr4End, by omega, by rw [hlen_cons]; omega, by rw [hbw_cons]; omega,
      by rw [hr21End]; omega,
      by rw [hr22End]; simp only [List.length_cons]; omega, hr29End,
      hrepEnd, by rw [← Nat.add_assoc]; exact hbatEnd, ?_, ?_, by rw [hlen_cons]; clear * - hc1 hcEnd hxs_pos; omega⟩
    · intro x hx ⟨vr, hvr, hxvr⟩
      rcases List.mem_cons.mp hvr with rfl | hvr_tl
      · have hnot_tl : ∀ vr' ∈ tl, x ∉ vr'.2 := fun vr' hvr' hmem => by
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hvr'
          exact hdisj 0 (j + 1) (by simp) (by simp; omega) (by omega) x hxvr hmem
        have hxk_lt := hB_end_lt x (hxs_sub x hxvr)
        have hmem_eq : stEnd.mem (endBundleBase + endKey x) = st1.mem (endBundleBase + endKey x) :=
          hfrEnd (endBundleBase + endKey x)
            (by unfold bundleSlotBlockSize at heb_blk ⊢; clear * - heb_blk hxk_lt; omega)
            (fun y hy => by
              have hyk := hB_end_lt y (by rw [hends_b1, Finset.mem_sdiff] at hy; exact hy.1)
              exact ⟨by clear * - heb_prev hxk_lt hyk; omega, by clear * - heb_next hxk_lt hyk; omega⟩)
            (fun vr' hvr' y hy => fun heq => hnot_tl vr' hvr' (by
              have : endKey x = endKey y := by omega
              rwa [endKey_injective this]))
            (by clear * - hbe hbw_cons hlen1_le hxk_lt; omega) (by clear * - hhe hlen_cons hh1_lo hh1_hi hhEnd_hi hxk_lt; omega)
        have hxE0 : x ∈ edgeEnds B.edges := (mem_edgeEnds _ _).mpr ((BundleState.mem_ends B b x).mp (hxs_sub x hxvr)).1
        have hbo1_x : res1.2.bundleOf x = nB := by rw [hsrc1 x hxE0, ite_eq_left hxvr]
        have hbo1_lt : ∀ y ∈ edgeEnds res1.2.edges, res1.2.bundleOf y < nB + 1 := fun y hy => by
          rw [hE1] at hy; rw [hsrc1 y hy]; split_ifs
          · omega
          · exact Nat.lt_succ_of_lt (hbo_lt y hy)
        have hpres := foldOneSplitRuns_preserves_ne tl (ops ++ [res1.1]) res1.2 (nB + 1) x
          hV1 (by omega) (fun vr hvr => (htl_info vr hvr).2.2.2) hdisj_tl hbo1_lt
          (by rw [hbo1_x]; omega) (hE1 ▸ hxE0)
        dsimp only [foldOneSplitRuns]
        rw [hmem_eq, heb1 x hxvr, hpres.2, hbo1_x]
      · exact hebEnd x hx ⟨vr, hvr_tl, hxvr⟩
    · intro a haBlk haPN haEB haBat haH
      rw [hbw_cons] at haBat
      rw [hfrEnd a haBlk (fun x hx => haPN x (by rw [hends_b1, Finset.mem_sdiff] at hx; exact hx.1))
          (fun vr hvr => haEB vr (List.mem_cons_of_mem _ hvr)) (by clear * - haBat hlen1_le; omega) (by omega),
        hfr1 a haBlk haPN (haEB (vCur, xs) List.mem_cons_self) (by clear * - haBat; omega) (by omega)]


end

end MinCostFlow.SparseCore.Program
