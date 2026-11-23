module

public import MinCostFlow.SparseCore.Program.BundleStepEmitKept

/-!
# Full verification of `bundleStepEmitOneRunStmt` (`BundleStepEmitOneRunPost`)

Verifies `bundleStepEmitOneRun_runs`: given `BundleSlotRepAt` for slot block `p` with `nB < bunCap`,
a nonempty run `(vCur, xs)` starting at `packArr[idx]` with `b` retaining at least one end outside
`xs`, `bundleStepEmitOneRunStmt bDllPush bDllErase`:
* updates `BundleSlotRepAt` from `B` to `(applyOneSplitRun B b nB vCur xs).2`,
* writes `SmallUpdateAt` for `oneRunUpdate b nB xs` at `batchPtr + writeOff` (`len ≤ 5 + xs.length`
  words, listing whichever side of the split is smaller via tag `2` or tag `3`),
* updates `endBundle[endKey x] := nB` for all `x ∈ xs`,
* advances `r29` to `idx + xs.length`, `r21` to `writeOff + len`, `r22` to `updCnt + 1`,
  and `r4` to `hEnd ≤ hCur + 2 * xs.length`,
* runs in `≤ 290 * xs.length + 220` steps.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

private lemma bundleSlotRepAt_oneRun {eCap prevBase nextBase p bunCap b nB vCur : ℕ}
    {B : BundleState} {xs : List End} {L_b0 L_b' L_new' : List ℕ}
    {mem₀ memW memEnd : ℕ → ℕ}
    (hV : B.vertices = Finset.range nB) (hb_lt : b < nB) (hnb_lt : nB < bunCap)
    (hxs_pos : 0 < xs.length) (hxs_sub : ∀ x ∈ xs, x ∈ B.ends b)
    (hb_keep : ∃ y ∈ B.ends b, y ∉ xs)
    (hrep : BundleSlotRepAt eCap prevBase nextBase p bunCap B mem₀)
    (hL0_lt : ∀ k ∈ L_b0, k < 2 * eCap)
    (hL0_mem : ∀ k, k ∈ L_b0 ↔ endOfKey k ∈ B.ends b)
    (hprev_next : prevBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ prevBase)
    (hblk_prev : p + bundleSlotBlockSize bunCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ p)
    (hblk_next : p + bundleSlotBlockSize bunCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ p)
    (hdll_bW : IsDoublyLinkedList memW prevBase nextBase (bsHeadBase p + b) (2 * eCap) L_b')
    (hLbW_len : L_b'.length + xs.length = L_b0.length)
    (hLbW_mem : ∀ k, k ∈ L_b' ↔ endOfKey k ∈ B.ends b ∧ endOfKey k ∉ xs)
    (hdll_nW : IsDoublyLinkedList memW prevBase nextBase (bsHeadBase p + nB) (2 * eCap) L_new')
    (hLnW_len : L_new'.length = xs.length)
    (hLnW_mem : ∀ k, k ∈ L_new' ↔ endOfKey k ∈ xs)
    (hmem_nB : memEnd (p + bsOffNB) = nB + 1)
    (hmem_szb : memEnd (bsSizeBase p bunCap + b) = L_b0.length - xs.length)
    (hmem_szn : memEnd (bsSizeBase p bunCap + nB) = xs.length)
    (hEnd_W : ∀ a, (p ≤ a ∧ a < p + bundleSlotBlockSize bunCap) ∨
      (prevBase ≤ a ∧ a < prevBase + 2 * eCap) ∨ (nextBase ≤ a ∧ a < nextBase + 2 * eCap) →
      a ≠ bsSizeBase p bunCap + nB → a ≠ bsSizeBase p bunCap + b → memEnd a = memW a)
    (hW_0 : ∀ a, (p ≤ a ∧ a < p + bundleSlotBlockSize bunCap) ∨
      (prevBase ≤ a ∧ a < prevBase + 2 * eCap) ∨ (nextBase ≤ a ∧ a < nextBase + 2 * eCap) →
      a ≠ p + bsOffNB → a ≠ bsHeadBase p + b → a ≠ bsHeadBase p + nB →
      (∀ k ∈ L_b0, a ≠ prevBase + k ∧ a ≠ nextBase + k) → memW a = mem₀ a) :
    BundleSlotRepAt eCap prevBase nextBase p bunCap (applyOneSplitRun B b nB vCur xs).2 memEnd := by
  obtain ⟨nB', hV', hnB', hE_lt, hbo_lt, hpar0, h0_cap, h1_nB, h2_nE, hdll_all, hpar_em, htail0, hscr0⟩ := hrep
  have hnB_eq : nB' = nB := by
    have hc := congrArg Finset.card (hV'.symm.trans hV); simpa [Finset.card_range] using hc
  rw [hnB_eq] at hV' hnB' hbo_lt hpar0 h1_nB hdll_all hpar_em htail0
  have hblk_p' : p + (3 + 6 * bunCap) ≤ prevBase ∨ prevBase + 2 * eCap ≤ p := hblk_prev
  have hblk_n' : p + (3 + 6 * bunCap) ≤ nextBase ∨ nextBase + 2 * eCap ≤ p := hblk_next
  obtain ⟨hV_res, hE_res, hbo_res, _⟩ := oneRunUpdate_graph_apply B hV hb_lt hxs_sub
  obtain ⟨hends_b, hends_nB, hends_oth⟩ := applyOneSplitRun_ends hV hb_lt hbo_lt hxs_sub
  have hEnd_0_blk : ∀ off < bundleSlotBlockSize bunCap,
      p + off ≠ p + bsOffNB → p + off ≠ bsHeadBase p + b → p + off ≠ bsHeadBase p + nB →
      p + off ≠ bsSizeBase p bunCap + b → p + off ≠ bsSizeBase p bunCap + nB →
      memEnd (p + off) = mem₀ (p + off) := fun off hoff h1 h2 h3 h4 h5 =>
    (hEnd_W (p + off) (Or.inl ⟨by omega, by omega⟩) h5 h4).trans
      (hW_0 (p + off) (Or.inl ⟨by omega, by omega⟩) h1 h2 h3 fun k hk => by
        have := hL0_lt k hk; unfold bundleSlotBlockSize at hoff
        exact ⟨by clear * - hblk_p' hoff this; omega, by clear * - hblk_n' hoff this; omega⟩)
  refine ⟨nB + 1, hV_res, by omega, fun e he => hE_lt e (hE_res ▸ he),
    fun x hx => by
      have hx' : x ∈ edgeEnds B.edges := hE_res ▸ hx
      rw [hbo_res x hx']; split_ifs
      · omega
      · have := hbo_lt x hx'; omega,
    fun c hc => by
      change Function.update B.parent nB vCur c = 0
      rw [Function.update_of_ne (by omega)]; exact hpar0 c (by omega),
    ?_, hmem_nB, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEnd_0_blk bsOffBunCap (by unfold bsOffBunCap bundleSlotBlockSize; omega)
      (by unfold bsOffBunCap bsOffNB; omega) (by unfold bsOffBunCap bsHeadBase; omega)
      (by unfold bsOffBunCap bsHeadBase; omega) (by unfold bsOffBunCap bsSizeBase; omega)
      (by unfold bsOffBunCap bsSizeBase; omega)]; exact h0_cap
  · rw [hE_res, hEnd_0_blk bsOffNE (by unfold bsOffNE bundleSlotBlockSize; omega)
      (by unfold bsOffNE bsOffNB; omega) (by unfold bsOffNE bsHeadBase; omega)
      (by unfold bsOffNE bsHeadBase; omega) (by unfold bsOffNE bsSizeBase; omega)
      (by unfold bsOffNE bsSizeBase; omega)]; exact h2_nE
  · intro c hc
    by_cases hcn : c = nB
    · subst c
      refine ⟨L_new', hdll_nW.of_agree
        (hEnd_W (bsHeadBase p + nB) (Or.inl ⟨by unfold bsHeadBase; omega, by unfold bsHeadBase bundleSlotBlockSize; omega⟩)
          (by unfold bsHeadBase bsSizeBase; omega) (by unfold bsHeadBase bsSizeBase; omega))
        (fun k hk => hEnd_W (prevBase + k) (Or.inr (Or.inl ⟨by omega, by have := hdll_nW.2.1 k hk; omega⟩))
          (by have := hdll_nW.2.1 k hk; unfold bsSizeBase; clear * - hblk_p' this hnb_lt; omega)
          (by have := hdll_nW.2.1 k hk; unfold bsSizeBase; clear * - hblk_p' this hb_lt hnb_lt; omega))
        (fun k hk => hEnd_W (nextBase + k) (Or.inr (Or.inr ⟨by omega, by have := hdll_nW.2.1 k hk; omega⟩))
          (by have := hdll_nW.2.1 k hk; unfold bsSizeBase; clear * - hblk_n' this hnb_lt; omega)
          (by have := hdll_nW.2.1 k hk; unfold bsSizeBase; clear * - hblk_n' this hb_lt hnb_lt; omega)),
        by rw [hmem_szn, hLnW_len], fun k => by rw [hLnW_mem, hends_nB, List.mem_toFinset]⟩
    · by_cases hcb : c = b
      · subst c
        refine ⟨L_b', hdll_bW.of_agree
          (hEnd_W (bsHeadBase p + b) (Or.inl ⟨by unfold bsHeadBase; omega, by unfold bsHeadBase bundleSlotBlockSize; omega⟩)
            (by unfold bsHeadBase bsSizeBase; omega) (by unfold bsHeadBase bsSizeBase; omega))
          (fun k hk => hEnd_W (prevBase + k) (Or.inr (Or.inl ⟨by omega, by have := hdll_bW.2.1 k hk; omega⟩))
            (by have := hdll_bW.2.1 k hk; unfold bsSizeBase; clear * - hblk_p' this hnb_lt; omega)
            (by have := hdll_bW.2.1 k hk; unfold bsSizeBase; clear * - hblk_p' this hb_lt hnb_lt; omega))
          (fun k hk => hEnd_W (nextBase + k) (Or.inr (Or.inr ⟨by omega, by have := hdll_bW.2.1 k hk; omega⟩))
            (by have := hdll_bW.2.1 k hk; unfold bsSizeBase; clear * - hblk_n' this hnb_lt; omega)
            (by have := hdll_bW.2.1 k hk; unfold bsSizeBase; clear * - hblk_n' this hb_lt hnb_lt; omega)),
          by rw [hmem_szb]; omega, fun k => by rw [hLbW_mem, hends_b, Finset.mem_sdiff, List.mem_toFinset]⟩
      · obtain ⟨Lc, hdll_c, hsz_c, hmem_c⟩ := hdll_all c (by omega)
        have hLc_disj : ∀ k ∈ Lc, ∀ k' ∈ L_b0, k ≠ k' := fun k hk k' hk' heq => hcb (by
          have h1 := ((BundleState.mem_ends B c _).mp ((hmem_c k).mp hk)).2
          have h2 := ((BundleState.mem_ends B b _).mp ((hL0_mem k').mp hk')).2
          rw [heq] at h1; exact h1.symm.trans h2)
        refine ⟨Lc, hdll_c.of_agree ?_ ?_ ?_, ?_, fun k => by rw [hends_oth c hcb hcn, hmem_c]⟩
        · simpa [bsHeadBase, Nat.add_assoc] using hEnd_0_blk (3 + c) (by unfold bundleSlotBlockSize; omega)
            (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsHeadBase; omega)
            (by unfold bsSizeBase; omega) (by unfold bsSizeBase; omega)
        · intro k hk; have hk_lt := hdll_c.2.1 k hk
          exact (hEnd_W (prevBase + k) (Or.inr (Or.inl ⟨by omega, by omega⟩))
              (by unfold bsSizeBase; clear * - hblk_p' hk_lt hnb_lt; omega)
              (by unfold bsSizeBase; clear * - hblk_p' hk_lt hb_lt hnb_lt; omega)).trans
            (hW_0 (prevBase + k) (Or.inr (Or.inl ⟨by omega, by omega⟩))
              (by unfold bsOffNB; clear * - hblk_p' hk_lt; omega)
              (by unfold bsHeadBase; clear * - hblk_p' hk_lt hb_lt hnb_lt; omega)
              (by unfold bsHeadBase; clear * - hblk_p' hk_lt hnb_lt; omega)
              fun k' hk' => ⟨by have := hLc_disj k hk k' hk'; omega,
                             by have := hL0_lt k' hk'; clear * - hprev_next hk_lt this; omega⟩)
        · intro k hk; have hk_lt := hdll_c.2.1 k hk
          exact (hEnd_W (nextBase + k) (Or.inr (Or.inr ⟨by omega, by omega⟩))
              (by unfold bsSizeBase; clear * - hblk_n' hk_lt hnb_lt; omega)
              (by unfold bsSizeBase; clear * - hblk_n' hk_lt hb_lt hnb_lt; omega)).trans
            (hW_0 (nextBase + k) (Or.inr (Or.inr ⟨by omega, by omega⟩))
              (by unfold bsOffNB; clear * - hblk_n' hk_lt; omega)
              (by unfold bsHeadBase; clear * - hblk_n' hk_lt hb_lt hnb_lt; omega)
              (by unfold bsHeadBase; clear * - hblk_n' hk_lt hnb_lt; omega)
              fun k' hk' => ⟨by have := hL0_lt k' hk'; clear * - hprev_next hk_lt this; omega,
                             by have := hLc_disj k hk k' hk'; omega⟩)
        · have heq := hEnd_0_blk (3 + bunCap + c) (by unfold bundleSlotBlockSize; omega)
            (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsHeadBase; omega)
            (by unfold bsSizeBase; omega) (by unfold bsSizeBase; omega)
          simpa [bsSizeBase, Nat.add_assoc] using heq.trans (by simpa [bsSizeBase, Nat.add_assoc] using hsz_c)
  · intro c hc hem
    have hcn : c ≠ nB := fun heq => by
      subst heq; rw [hends_nB] at hem
      exact Finset.notMem_empty _ (hem ▸ List.mem_toFinset.mpr (List.getElem_mem hxs_pos))
    have hcb : c ≠ b := fun heq => by
      subst heq; rw [hends_b] at hem
      obtain ⟨y, hyB, hyNot⟩ := hb_keep
      exact Finset.notMem_empty _ (hem ▸ Finset.mem_sdiff.mpr ⟨hyB, by rwa [List.mem_toFinset]⟩)
    have heq := hEnd_0_blk (3 + 2 * bunCap + c) (by unfold bundleSlotBlockSize; omega)
      (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsHeadBase; omega)
      (by unfold bsSizeBase; omega) (by unfold bsSizeBase; omega)
    have hpe : memEnd (bsParentBase p bunCap + c) = mem₀ (bsParentBase p bunCap + c) := by
      simpa [bsParentBase, Nat.add_assoc] using heq
    rw [hpe]; change mem₀ (bsParentBase p bunCap + c) = Function.update B.parent nB vCur c
    rw [Function.update_of_ne hcn]
    exact hpar_em c (by omega) (by rwa [← hends_oth c hcb hcn])
  · intro c hge hlt
    obtain ⟨t1, t2, t3⟩ := htail0 c (by omega) hlt
    refine ⟨?_, ?_, ?_⟩
    · have heq := hEnd_0_blk (3 + c) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsHeadBase; omega)
        (by unfold bsSizeBase; omega) (by unfold bsSizeBase; omega)
      simpa [bsHeadBase, Nat.add_assoc] using heq.trans (by simpa [bsHeadBase, Nat.add_assoc] using t1)
    · have heq := hEnd_0_blk (3 + bunCap + c) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsHeadBase; omega)
        (by unfold bsSizeBase; omega) (by unfold bsSizeBase; omega)
      simpa [bsSizeBase, Nat.add_assoc] using heq.trans (by simpa [bsSizeBase, Nat.add_assoc] using t2)
    · have heq := hEnd_0_blk (3 + 2 * bunCap + c) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsHeadBase; omega)
        (by unfold bsSizeBase; omega) (by unfold bsSizeBase; omega)
      simpa [bsParentBase, Nat.add_assoc] using heq.trans (by simpa [bsParentBase, Nat.add_assoc] using t3)
  · intro c hc
    obtain ⟨s1, s2, s3⟩ := hscr0 c hc
    refine ⟨?_, ?_, ?_⟩
    · have heq := hEnd_0_blk (3 + 3 * bunCap + c) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsHeadBase; omega)
        (by unfold bsSizeBase; omega) (by unfold bsSizeBase; omega)
      simpa [bsSeenBase, Nat.add_assoc] using heq.trans (by simpa [bsSeenBase, Nat.add_assoc] using s1)
    · have heq := hEnd_0_blk (3 + 4 * bunCap + c) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsHeadBase; omega)
        (by unfold bsSizeBase; omega) (by unfold bsSizeBase; omega)
      simpa [bsInCandBase, Nat.add_assoc] using heq.trans (by simpa [bsInCandBase, Nat.add_assoc] using s2)
    · have heq := hEnd_0_blk (3 + 5 * bunCap + c) (by unfold bundleSlotBlockSize; omega)
        (by unfold bsOffNB; omega) (by unfold bsHeadBase; omega) (by unfold bsHeadBase; omega)
        (by unfold bsSizeBase; omega) (by unfold bsSizeBase; omega)
      simpa [bsCandNextBase, Nat.add_assoc] using heq.trans (by simpa [bsCandNextBase, Nat.add_assoc] using s3)

private lemma bundleStepEmitOneRun_hdr_runs {w eCap p bunCap nB packArr idx vCur hCur : ℕ}
    {pProg : Program} {ω : ℕ → Bool} {st₀ : State}
    (hw16 : 16 ≤ 2 ^ w) (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hpack_idx_w : packArr + idx < 2 ^ w) (hv_w : vCur < 2 ^ w) (hnb_lt : nB < bunCap)
    (h1_nB : st₀.mem (p + 1) = nB)
    (hpk0_div : st₀.mem (packArr + idx) / (2 * eCap) = vCur)
    (hr4 : st₀.regs 4 = hCur) (hr6 : st₀.regs 6 = 2 * eCap)
    (hr7 : st₀.regs 7 = p) (hr27 : st₀.regs 27 = packArr) (hr29 : st₀.regs 29 = idx) :
    ∃ stH,
      (∀ {sTail : Stmt} {o : Outcome} {stF : State} {cTail : ℕ},
        Runs w pProg ω sTail stH o stF cTail →
        Runs w pProg ω
          (.assign 30 (.bin .div (.load (.bin .add (.reg 27) (.reg 29))) (.reg 6)) ;;
           .assign 31 (.load (.bin .add (.reg 7) (.const 1))) ;;
           .store (.bin .add (.reg 7) (.const 1)) (.bin .add (.reg 31) (.const 1)) ;;
           .assign 32 (.reg 4) ;; .assign 33 (.const 0) ;; .assign 34 (.const 0) ;;
           .assign 35 (.const 1) ;; sTail) st₀ o stF (34 + cTail)) ∧
      (∀ r ≤ 29, stH.regs r = st₀.regs r) ∧
      stH.regs 30 = vCur ∧ stH.regs 31 = nB ∧ stH.regs 32 = hCur ∧
      stH.regs 33 = 0 ∧ stH.regs 34 = 0 ∧ stH.regs 35 = 1 ∧
      stH.mem (p + 1) = nB + 1 ∧ (∀ a, a ≠ p + 1 → stH.mem a = st₀.mem a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  let r30 := Function.update st₀.regs 30 vCur
  let r31 := Function.update r30 31 nB
  let mHdr := Function.update st₀.mem (p + 1) (nB + 1)
  let r32 := Function.update r31 32 hCur
  let r33 := Function.update r32 33 0
  let r34 := Function.update r33 34 0
  let r35 := Function.update r34 35 1
  let stH : State := { mem := mHdr, regs := r35, pos := st₀.pos }
  refine ⟨stH, ?_, fun r hr => by simp [stH, r35, r34, r33, r32, r31, r30, show r ≠ 30 by omega,
      show r ≠ 31 by omega, show r ≠ 32 by omega, show r ≠ 33 by omega, show r ≠ 34 by omega,
      show r ≠ 35 by omega],
    by simp [stH, r35, r34, r33, r32, r31, r30], by simp [stH, r35, r34, r33, r32, r31],
    by simp [stH, r35, r34, r33, r32], by simp [stH, r35, r34, r33], by simp [stH, r35, r34],
    by simp [stH, r35], by simp [stH, mHdr], fun a hne => Function.update_of_ne hne _ _⟩
  intro sTail o stF cTail hTail
  have ha30 : Runs w pProg ω (.assign 30 (.bin .div (.load (.bin .add (.reg 27) (.reg 29))) (.reg 6)))
      st₀ .normal { st₀ with regs := r30 } 7 :=
    runs_assign_iff.mpr ⟨vCur, by
      simp [Expr.eval, BinOp.eval, hr27, hr29, hr6, hpack_idx_w, hpk0_div, hv_w], rfl, rfl, by simp [Expr.size]⟩
  have ha31 : Runs w pProg ω (.assign 31 (.load (.bin .add (.reg 7) (.const 1))))
      { st₀ with regs := r30 } .normal { st₀ with regs := r31 } 5 :=
    runs_assign_iff.mpr ⟨nB, by
      simp [Expr.eval, BinOp.eval, r30, hr7, h1_w,
        show p + 1 < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega, h1_nB], rfl, rfl, rfl⟩
  have hst1 : Runs w pProg ω (.store (.bin .add (.reg 7) (.const 1)) (.bin .add (.reg 31) (.const 1)))
      { st₀ with regs := r31 } .normal { mem := mHdr, regs := r31, pos := st₀.pos } 7 :=
    runs_store_iff.mpr ⟨p + 1, nB + 1,
      by simp [Expr.eval, BinOp.eval, r31, r30, hr7, h1_w,
        show p + 1 < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega],
      by simp [Expr.eval, BinOp.eval, r31, h1_w,
        show nB + 1 < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega],
      rfl, rfl, by simp [Expr.size]⟩
  have ha32 : Runs w pProg ω (.assign 32 (.reg 4)) { mem := mHdr, regs := r31, pos := st₀.pos }
      .normal { mem := mHdr, regs := r32, pos := st₀.pos } 2 :=
    runs_assign_iff.mpr ⟨hCur, by simp [Expr.eval, r31, r30, hr4], rfl, rfl, rfl⟩
  have ha33 : Runs w pProg ω (.assign 33 (.const 0)) { mem := mHdr, regs := r32, pos := st₀.pos }
      .normal { mem := mHdr, regs := r33, pos := st₀.pos } 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  have ha34 : Runs w pProg ω (.assign 34 (.const 0)) { mem := mHdr, regs := r33, pos := st₀.pos }
      .normal { mem := mHdr, regs := r34, pos := st₀.pos } 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  have ha35 : Runs w pProg ω (.assign 35 (.const 1)) { mem := mHdr, regs := r34, pos := st₀.pos }
      .normal stH 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h1_w], rfl, rfl, rfl⟩
  exact (show 7 + (5 + (7 + (2 + (2 + (2 + (2 + cTail + 1) + 1) + 1) + 1) + 1) + 1) + 1 = 34 + cTail by omega) ▸
    bundle_runs_seq_normal ha30 (bundle_runs_seq_normal ha31 (bundle_runs_seq_normal hst1
      (bundle_runs_seq_normal ha32 (bundle_runs_seq_normal ha33 (bundle_runs_seq_normal ha34
        (bundle_runs_seq_normal ha35 hTail))))))

/-- Full verification of `bundleStepEmitOneRunStmt bDllPush bDllErase`. -/
theorem bundleStepEmitOneRun_runs {w eCap p bunCap b nB degB packArr batchPtr writeOff updCnt idx
    vCur prevBase nextBase endBundleBase hCur : ℕ}
    {pProg : Program} {bDllPush bDllErase : ℕ} {ω : ℕ → Bool}
    {B : BundleState} {xs : List End}
    (hpPush : pProg.HasAt bDllPush [bundleDllPushStmt])
    (hpErase : pProg.HasAt bDllErase [bundleDllEraseStmt])
    (hw16 : 16 ≤ 2 ^ w)
    (heCap_w : 2 * eCap < 2 ^ w)
    (hpk_bound : (vCur + 1) * (2 * eCap) ≤ 2 ^ w)
    (hprev_w : prevBase + 2 * eCap < 2 ^ w) (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (heb_w : endBundleBase + 2 * eCap < 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hpack_w : packArr + degB < 2 ^ w)
    (hbat_w : batchPtr + writeOff + 5 + xs.length < 2 ^ w)
    (hupd_w : updCnt + 1 < 2 ^ w)
    (hh_w : hCur + 2 * xs.length < 2 ^ w)
    (hV : B.vertices = Finset.range nB)
    (hb_lt : b < nB) (hnb_lt : nB < bunCap)
    (hidx_le : idx + xs.length ≤ degB)
    (hxs_pos : 0 < xs.length) (hxs_nd : xs.Nodup)
    (hxs_sub : ∀ x ∈ xs, x ∈ B.ends b)
    (hb_keep : ∃ y ∈ B.ends b, y ∉ xs)
    (hprev_next : prevBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ prevBase)
    (hblk_prev : p + bundleSlotBlockSize bunCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ p)
    (hblk_next : p + bundleSlotBlockSize bunCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ p)
    (heb_prev : endBundleBase + 2 * eCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ endBundleBase)
    (heb_next : endBundleBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ endBundleBase)
    (heb_blk : endBundleBase + 2 * eCap ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ endBundleBase)
    (hpack_disj_blk : packArr + degB ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ packArr)
    (hpack_disj_prev : packArr + degB ≤ prevBase ∨ prevBase + 2 * eCap ≤ packArr)
    (hpack_disj_next : packArr + degB ≤ nextBase ∨ nextBase + 2 * eCap ≤ packArr)
    (hpack_disj_eb : packArr + degB ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ packArr)
    (hpack_disj_bat : packArr + degB ≤ batchPtr + writeOff ∨
      batchPtr + writeOff + 5 + xs.length ≤ packArr)
    (hpack_disj_h : packArr + degB ≤ hCur ∨ hCur + 2 * xs.length ≤ packArr)
    (hbat_disj_blk : batchPtr + writeOff + 5 + xs.length ≤ p ∨
      p + bundleSlotBlockSize bunCap ≤ batchPtr + writeOff)
    (hbat_disj_prev : batchPtr + writeOff + 5 + xs.length ≤ prevBase ∨
      prevBase + 2 * eCap ≤ batchPtr + writeOff)
    (hbat_disj_next : batchPtr + writeOff + 5 + xs.length ≤ nextBase ∨
      nextBase + 2 * eCap ≤ batchPtr + writeOff)
    (hbat_disj_eb : batchPtr + writeOff + 5 + xs.length ≤ endBundleBase ∨
      endBundleBase + 2 * eCap ≤ batchPtr + writeOff)
    (hbat_disj_h : batchPtr + writeOff + 5 + xs.length ≤ hCur ∨
      hCur + 2 * xs.length ≤ batchPtr + writeOff)
    (hh_disj_blk : hCur + 2 * xs.length ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ hCur)
    (hh_disj_prev : hCur + 2 * xs.length ≤ prevBase ∨ prevBase + 2 * eCap ≤ hCur)
    (hh_disj_next : hCur + 2 * xs.length ≤ nextBase ∨ nextBase + 2 * eCap ≤ hCur)
    (hh_disj_eb : hCur + 2 * xs.length ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ hCur)
    {st₀ : State}
    (hrep : BundleSlotRepAt eCap prevBase nextBase p bunCap B st₀.mem)
    (hpack_in : ∀ t (ht : t < xs.length),
      st₀.mem (packArr + (idx + t)) = packEndKey eCap vCur (endKey xs[t]))
    (hpack_end : idx + xs.length < degB →
      st₀.mem (packArr + (idx + xs.length)) / (2 * eCap) ≠ vCur ∧
      st₀.mem (packArr + (idx + xs.length)) < 2 ^ w)
    (hr4 : st₀.regs 4 = hCur) (hr6 : st₀.regs 6 = 2 * eCap)
    (hr7 : st₀.regs 7 = p) (hr8 : st₀.regs 8 = bunCap) (hr9 : st₀.regs 9 = endBundleBase)
    (hr10 : st₀.regs 10 = prevBase) (hr11 : st₀.regs 11 = nextBase)
    (hr20 : st₀.regs 20 = batchPtr) (hr21 : st₀.regs 21 = writeOff) (hr22 : st₀.regs 22 = updCnt)
    (hr25 : st₀.regs 25 = b) (hr26 : st₀.regs 26 = degB) (hr27 : st₀.regs 27 = packArr)
    (hr29 : st₀.regs 29 = idx) :
    let res := applyOneSplitRun B b nB vCur xs
    ∃ stEnd cEnd hEnd len,
      Runs w pProg ω (bundleStepEmitOneRunStmt bDllPush bDllErase) st₀ .normal stEnd cEnd ∧
      (∀ r ≤ 29, r ≠ 4 → r ≠ 21 → r ≠ 22 → r ≠ 29 → stEnd.regs r = st₀.regs r) ∧
      stEnd.regs 4 = hEnd ∧ hCur ≤ hEnd ∧ hEnd ≤ hCur + 2 * xs.length ∧
      len ≤ 5 + xs.length ∧
      stEnd.regs 21 = writeOff + len ∧
      stEnd.regs 22 = updCnt + 1 ∧
      stEnd.regs 29 = idx + xs.length ∧
      BundleSlotRepAt eCap prevBase nextBase p bunCap res.2 stEnd.mem ∧
      SmallUpdateAt stEnd.mem (batchPtr + writeOff) B.graph res.1 len ∧
      (∀ x ∈ xs, stEnd.mem (endBundleBase + endKey x) = nB) ∧
      (∀ a, (a < p ∨ p + bundleSlotBlockSize bunCap ≤ a) →
        (∀ x ∈ B.ends b, a ≠ prevBase + endKey x ∧ a ≠ nextBase + endKey x) →
        (∀ x ∈ xs, a ≠ endBundleBase + endKey x) →
        (a < batchPtr + writeOff ∨ batchPtr + writeOff + 5 + xs.length ≤ a) →
        (a < hCur ∨ hEnd ≤ a) →
        stEnd.mem a = st₀.mem a) ∧
      cEnd ≤ 290 * xs.length + 220 := by
  intro res
  have hrep_copy := hrep
  obtain ⟨nB', hV', hnB', hE_lt, hbo_lt, _, _, h1_nB, _, hdll_all, _, htail0, _⟩ := hrep
  have hnB_eq : nB' = nB := by
    have hc := congrArg Finset.card (hV'.symm.trans hV); simpa [Finset.card_range] using hc
  rw [hnB_eq] at hV' hnB' hbo_lt h1_nB hdll_all htail0
  obtain ⟨L_b0, hdll_b0, hsz_b0, hmem_b0⟩ := hdll_all b hb_lt
  have hL0_nd : L_b0.Nodup := hdll_b0.1
  have hL0_lt : ∀ k ∈ L_b0, k < 2 * eCap := hdll_b0.2.1
  have hxs_key_lt : ∀ x ∈ xs, endKey x < 2 * eCap := fun x hx => by
    have he := hE_lt x.1 ((BundleState.mem_ends B b x).mp (hxs_sub x hx)).1
    rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
  -- The run `xs` is not empty, and the key of its first end is below `2 * eCap`.
  have h2e_pos : 0 < 2 * eCap :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (hxs_key_lt _ (List.getElem_mem hxs_pos))
  have hv_w : vCur < 2 ^ w := by
    rw [Nat.add_mul, Nat.one_mul] at hpk_bound
    have : vCur ≤ vCur * (2 * eCap) := Nat.le_mul_of_pos_right _ h2e_pos; omega
  have hpk0 : st₀.mem (packArr + idx) = packEndKey eCap vCur (endKey (xs[0]'hxs_pos)) := by
    simpa [Nat.add_zero] using hpack_in 0 hxs_pos
  have hk0_lt : endKey (xs[0]'hxs_pos) < 2 * eCap := hxs_key_lt _ (List.getElem_mem hxs_pos)
  have hblk_p' : p + (3 + 6 * bunCap) ≤ prevBase ∨ prevBase + 2 * eCap ≤ p := hblk_prev
  have hblk_n' : p + (3 + 6 * bunCap) ≤ nextBase ∨ nextBase + 2 * eCap ≤ p := hblk_next
  have hpack_b' : packArr + degB ≤ p ∨ p + (3 + 6 * bunCap) ≤ packArr := hpack_disj_blk
  have hbat_b' : batchPtr + writeOff + 5 + xs.length ≤ p ∨ p + (3 + 6 * bunCap) ≤ batchPtr + writeOff := hbat_disj_blk
  have hh_b' : hCur + 2 * xs.length ≤ p ∨ p + (3 + 6 * bunCap) ≤ hCur := hh_disj_blk
  have heb_b' : endBundleBase + 2 * eCap ≤ p ∨ p + (3 + 6 * bunCap) ≤ endBundleBase := heb_blk
  -- Step 1: Header setup (34 steps)
  obtain ⟨stH, hhdr_cps, hregsH, hr30H, hr31H, hr32H, hr33H, hr34H, hr35H, hmH_nB, hmHdr_ne⟩ :=
    bundleStepEmitOneRun_hdr_runs (st₀ := st₀) hw16 hp_w (by omega) hv_w hnb_lt h1_nB
      (by rw [hpk0, packEndKey_div hk0_lt]) hr4 hr6 hr7 hr27 hr29
  -- Step 2: Inner `while` loop (`runs_while_oneRun`)
  have hdll_bH : IsDoublyLinkedList stH.mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L_b0 :=
    hdll_b0.of_agree (hmHdr_ne (bsHeadBase p + b) (by unfold bsHeadBase; omega))
      (fun k hk => hmHdr_ne (prevBase + k) (by have := hL0_lt k hk; clear * - hblk_p' this; omega))
      (fun k hk => hmHdr_ne (nextBase + k) (by have := hL0_lt k hk; clear * - hblk_n' this; omega))
  have hdll_nH : IsDoublyLinkedList stH.mem prevBase nextBase (bsHeadBase p + nB) (2 * eCap) [] :=
    IsDoublyLinkedList.nil ((hmHdr_ne (bsHeadBase p + nB) (by unfold bsHeadBase; omega)).trans (htail0 nB (le_refl _) hnb_lt).1)
  obtain ⟨stW, cW, L_b', L_new', hrunW, hregsW, hr29W, hr33W, hr34W, hdll_bW, hLbW_len, hLbW_mem,
    hdll_nW, hLnW_len, hLnW_mem, hLtW, hLhW, hebW, hfrW, hcW⟩ :=
    runs_while_oneRun (st₀ := stH) hpPush hpErase hw16 heCap_w h2e_pos hpk_bound hprev_w hnext_w heb_w hp_w
      hpack_w hbat_w (by omega) hb_lt hnb_lt hidx_le hxs_nd hxs_sub hE_lt hL0_nd hL0_lt hmem_b0
      hprev_next hblk_prev hblk_next heb_prev heb_next heb_blk hpack_disj_blk hpack_disj_prev
      hpack_disj_next hpack_disj_eb (by clear * - hpack_disj_bat; omega) (by clear * - hpack_disj_h; omega)
      (by clear * - hbat_b'; unfold bundleSlotBlockSize; omega)
      (by clear * - hbat_disj_prev; omega) (by clear * - hbat_disj_next; omega)
      (by clear * - hbat_disj_eb; omega) (by clear * - hbat_disj_h; omega)
      (by clear * - hh_disj_blk; omega) (by clear * - hh_disj_prev; omega)
      (by clear * - hh_disj_next; omega) (by clear * - hh_disj_eb; omega)
      (fun t ht => by rw [hmHdr_ne _ (by clear * - hpack_b' hidx_le ht; omega)]; exact hpack_in t ht)
      (fun hlt => by rw [hmHdr_ne _ (by clear * - hpack_b' hlt; omega)]; exact hpack_end hlt)
      hdll_bH hdll_nH
      ((hregsH 6 (by decide)).trans hr6) ((hregsH 7 (by decide)).trans hr7)
      ((hregsH 9 (by decide)).trans hr9) ((hregsH 10 (by decide)).trans hr10)
      ((hregsH 11 (by decide)).trans hr11) ((hregsH 20 (by decide)).trans hr20)
      ((hregsH 21 (by decide)).trans hr21) ((hregsH 25 (by decide)).trans hr25)
      ((hregsH 26 (by decide)).trans hr26) ((hregsH 27 (by decide)).trans hr27)
      ((hregsH 29 (by decide)).trans hr29) hr30H hr31H hr32H hr33H hr34H hr35H
  -- Step 3: Tail (`bundleStepEmitOneRunTailStmt`: size updates + smaller-side tag 2 / tag 3 emission)
  set kt := (runTailEdges xs).length
  set kh := (runHeadEdges xs).length
  have hkt_kh : kt + kh = xs.length := runTailEdges_add_headEdges_length xs
  have hW_r : ∀ r ≤ 29, r ≠ 29 → stW.regs r = st₀.regs r := fun r hr h29 =>
    (hregsW r (by omega) h29).trans (hregsH r hr)
  have hsz_bW : stW.mem (bsSizeBase p bunCap + b) = L_b0.length := by
    rw [hfrW _ (by unfold bsSizeBase bsHeadBase; clear * - hb_lt hnb_lt; omega)
        (by unfold bsSizeBase bsHeadBase; clear * - hb_lt hnb_lt; omega)
        (fun k hk => ⟨by have := hL0_lt k hk; unfold bsSizeBase; clear * - hblk_p' this hb_lt hnb_lt; omega,
                      by have := hL0_lt k hk; unfold bsSizeBase; clear * - hblk_n' this hb_lt hnb_lt; omega⟩)
        (fun x hx => by have := hxs_key_lt x hx; unfold bsSizeBase; clear * - heb_b' this hb_lt hnb_lt; omega)
        (by unfold bsSizeBase; clear * - hbat_b' hkt_kh hb_lt hnb_lt; omega)
        (by unfold bsSizeBase; clear * - hh_b' hkt_kh hb_lt hnb_lt; omega),
      hmHdr_ne _ (by unfold bsSizeBase; omega)]
    exact hsz_b0
  have hL0_w : L_b0.length < 2 ^ w := by
    have hc := Finset.card_le_card (show L_b0.toFinset ⊆ Finset.range (2 * eCap) from
      fun k hk => Finset.mem_range.mpr (hL0_lt k (List.mem_toFinset.mp hk)))
    rw [List.toFinset_card_of_nodup hL0_nd, Finset.card_range] at hc
    exact lt_of_le_of_lt hc heCap_w
  set len := 5 + min L_b'.length xs.length
  have hlen_le : len ≤ 5 + xs.length := by simp [len]
  obtain ⟨stEnd, cT, hEnd, htail_run, hregsEnd, hr4End, hhEnd_lo, hhEnd_hi, hr21End, hr22End,
    hmEnd_szb, hmEnd_szn, hsmallUpd, hmEnd_eq_W, hcT⟩ :=
    bundleStepEmitOneRun_tail_runs (L_b0 := L_b0) (L_b' := L_b') (stW := stW)
      hw16 heCap_w hnext_w hp_w hbat_w hupd_w hh_w hL0_w hV hb_lt hnb_lt hbo_lt
      hxs_nd hxs_sub hLbW_len hLbW_mem hbat_disj_blk hbat_disj_next hbat_disj_h
      hh_disj_blk hh_disj_next hblk_prev hblk_next hdll_bW hsz_bW hLtW hLhW
      ((hW_r 7 (by decide) (by decide)).trans hr7)
      ((hW_r 8 (by decide) (by decide)).trans hr8)
      ((hW_r 11 (by decide) (by decide)).trans hr11)
      ((hW_r 20 (by decide) (by decide)).trans hr20)
      ((hW_r 21 (by decide) (by decide)).trans hr21)
      ((hW_r 22 (by decide) (by decide)).trans hr22)
      ((hW_r 25 (by decide) (by decide)).trans hr25)
      ((hregsW 31 (by decide) (by decide)).trans hr31H)
      ((hregsW 32 (by decide) (by decide)).trans hr32H) hr33W hr34W
  have hfull_run : Runs w pProg ω (bundleStepEmitOneRunStmt bDllPush bDllErase) st₀ .normal stEnd
      (34 + (cW + cT + 1)) :=
    hhdr_cps (bundle_runs_seq_normal hrunW htail_run)
  have hmEnd_eq_W_blk : ∀ a, (p ≤ a ∧ a < p + bundleSlotBlockSize bunCap) ∨
      (prevBase ≤ a ∧ a < prevBase + 2 * eCap) ∨ (nextBase ≤ a ∧ a < nextBase + 2 * eCap) ∨
      (endBundleBase ≤ a ∧ a < endBundleBase + 2 * eCap) →
      a ≠ bsSizeBase p bunCap + nB → a ≠ bsSizeBase p bunCap + b → stEnd.mem a = stW.mem a := by
    intro a ha h1 h2
    have hnot_bat : a < batchPtr + writeOff ∨ batchPtr + writeOff + len ≤ a := by
      rcases ha with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩
      · unfold bundleSlotBlockSize at h4; clear * - hbat_b' hlen_le h3 h4; omega
      · clear * - hbat_disj_prev hlen_le h3 h4; omega
      · clear * - hbat_disj_next hlen_le h3 h4; omega
      · clear * - hbat_disj_eb hlen_le h3 h4; omega
    have hnot_h : a < hCur + kh ∨ hEnd ≤ a := by
      rcases ha with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩
      · unfold bundleSlotBlockSize at h4; clear * - hh_b' hhEnd_hi h3 h4; omega
      · clear * - hh_disj_prev hhEnd_hi h3 h4; omega
      · clear * - hh_disj_next hhEnd_hi h3 h4; omega
      · clear * - hh_disj_eb hhEnd_hi h3 h4; omega
    exact hmEnd_eq_W a h1 h2 hnot_bat hnot_h
  have hrep_end : BundleSlotRepAt eCap prevBase nextBase p bunCap res.2 stEnd.mem :=
    bundleSlotRepAt_oneRun hV hb_lt hnb_lt hxs_pos hxs_sub hb_keep hrep_copy hL0_lt hmem_b0
      hprev_next hblk_prev hblk_next hdll_bW hLbW_len hLbW_mem hdll_nW hLnW_len hLnW_mem
      (by
        rw [hmEnd_eq_W_blk (p + bsOffNB) (Or.inl ⟨by omega, by unfold bsOffNB bundleSlotBlockSize; omega⟩)
              (by unfold bsOffNB bsSizeBase; omega) (by unfold bsOffNB bsSizeBase; omega),
            hfrW (p + bsOffNB) (by unfold bsOffNB bsHeadBase; omega) (by unfold bsOffNB bsHeadBase; omega)
              (fun k hk => ⟨by have := hL0_lt k hk; unfold bsOffNB; clear * - hblk_p' this; omega,
                            by have := hL0_lt k hk; unfold bsOffNB; clear * - hblk_n' this; omega⟩)
              (fun x hx => by have := hxs_key_lt x hx; unfold bsOffNB; clear * - heb_b' this; omega)
              (by unfold bsOffNB; clear * - hbat_b' hkt_kh; omega)
              (by unfold bsOffNB; clear * - hh_b' hkt_kh; omega)]
        simpa [bsOffNB] using hmH_nB)
      hmEnd_szb hmEnd_szn
      (fun a ha h1 h2 => hmEnd_eq_W_blk a (by rcases ha with h | h | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr (Or.inl h))) h1 h2)
      (fun a ha h1 h2 h3 h4 => by
        have hnot_eb : ∀ x ∈ xs, a ≠ endBundleBase + endKey x := fun x hx => by
          have hk := hxs_key_lt x hx
          rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
          · unfold bundleSlotBlockSize at ha2; clear * - heb_b' ha1 ha2 hk; omega
          · clear * - heb_prev ha1 ha2 hk; omega
          · clear * - heb_next ha1 ha2 hk; omega
        have hnot_bat : a < batchPtr + writeOff + 5 ∨ batchPtr + writeOff + 5 + kt ≤ a := by
          rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
          · unfold bundleSlotBlockSize at ha2; clear * - hbat_b' ha1 ha2 hkt_kh; omega
          · clear * - hbat_disj_prev ha1 ha2 hkt_kh; omega
          · clear * - hbat_disj_next ha1 ha2 hkt_kh; omega
        have hnot_h : a < hCur ∨ hCur + kh ≤ a := by
          rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
          · unfold bundleSlotBlockSize at ha2; clear * - hh_b' ha1 ha2 hkt_kh; omega
          · clear * - hh_disj_prev ha1 ha2 hkt_kh; omega
          · clear * - hh_disj_next ha1 ha2 hkt_kh; omega
        exact (hfrW a h2 h3 h4 hnot_eb hnot_bat hnot_h).trans (hmHdr_ne a (by unfold bsOffNB at h1; exact h1)))
  refine ⟨stEnd, _, hEnd, len, hfull_run,
    fun r hr h4 h21 h22 h29 => (hregsEnd r (by omega) h4 h21 h22).trans (hW_r r hr h29),
    hr4End, by omega, hhEnd_hi, hlen_le, hr21End, hr22End,
    (hregsEnd 29 (by decide) (by decide) (by decide) (by decide)).trans hr29W,
    hrep_end, hsmallUpd,
    fun x hx => by
      have hx_lt := hxs_key_lt x hx
      rw [hmEnd_eq_W_blk (endBundleBase + endKey x) (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
        (by unfold bsSizeBase; clear * - heb_b' hx_lt hnb_lt; omega)
        (by unfold bsSizeBase; clear * - heb_b' hx_lt hb_lt hnb_lt; omega)]
      exact hebW x hx,
    fun a haBlk haPN haEB haBat haH => by
      have hne_nB : a ≠ bsSizeBase p bunCap + nB := by unfold bsSizeBase; unfold bundleSlotBlockSize at haBlk; clear * - haBlk hnb_lt; omega
      have hne_b : a ≠ bsSizeBase p bunCap + b := by unfold bsSizeBase; unfold bundleSlotBlockSize at haBlk; clear * - haBlk hb_lt hnb_lt; omega
      rw [hmEnd_eq_W a hne_nB hne_b (by clear * - haBat hlen_le; omega) (by clear * - haH hhEnd_lo; omega),
        hfrW a (by unfold bsHeadBase; unfold bundleSlotBlockSize at haBlk; clear * - haBlk hb_lt hnb_lt; omega)
          (by unfold bsHeadBase; unfold bundleSlotBlockSize at haBlk; clear * - haBlk hnb_lt; omega)
          (fun k hk => by
            have := haPN (endOfKey k) ((hmem_b0 k).mp hk)
            rwa [bundle_endKey_endOfKey] at this)
          haEB (by clear * - haBat hkt_kh; omega) (by clear * - haH hhEnd_lo; omega)]
      exact hmHdr_ne a (by unfold bundleSlotBlockSize at haBlk; clear * - haBlk; omega),
    by clear * - hcW hcT; omega⟩

end

end MinCostFlow.SparseCore.Program
