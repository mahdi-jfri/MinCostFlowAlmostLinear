module

public import MinCostFlow.SparseCore.Program.BundleInitScan

import WordRAM.Tactic

/-!
# Chunk-selection and DLL-push step lemmas for bundle initialization (`BundleInitStep`)

Verifies the two sub-blocks of `bundleInitEndBody`:
1. `bundleInitChooseBun_triple`: the `curTag`/`size == k` branch selecting or opening the target
   bundle `bun`.
2. `bundleInitEndTail_triple`: the shared tail calling `bDllPush`, incrementing `size[bun]`, and
   storing `endBundle[key] := bun`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Chunk-selection branch of `bundleInitEndBody`: chooses `bun` (opening a new chunk iff
`curEnds.length % k = 0`), updating `curTag[s]`, `nB`, and `curBun[s]` as needed. -/
lemma bundleInitChooseBun_triple {w eCap prevBase nextBase endBunBase curBunBase curTagBase
    i t s p cap k : ℕ}
    {pProg : Program} {cord : ℕ → List End} {rList : List ℕ} {E : Finset ℕ} {mem regs0 : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hk1 : 1 ≤ k)
    (hi : i < rList.length) (hi1_w : i + 1 < 2 ^ w)
    (ht : t < (cord rList[i]).length) (hx_in : ((cord rList[i])[t]).1 ∈ E)
    (hp_w : p + bundleSlotBlockSize cap < 2 ^ w)
    (hcurB_w : curBunBase + s < 2 ^ w) (hcurT_w : curTagBase + s < 2 ^ w)
    (hdisj_pB : p + bundleSlotBlockSize cap ≤ curBunBase + s ∨ curBunBase + s < p)
    (hdisj_pT : p + bundleSlotBlockSize cap ≤ curTagBase + s ∨ curTagBase + s < p)
    (hdisj_BT : curBunBase + s ≠ curTagBase + s)
    (hI : InitScanSlotInv eCap prevBase nextBase endBunBase curBunBase curTagBase
      cord rList i t s p cap k E mem)
    (_hcap_next : (initMidSlots cord (rList.take i) rList[i] (t + 1) E k).length ≤ cap) :
    let curEnds := ((cord rList[i]).take t).filter fun y => decide (y.1 ∈ E)
    let oldChunks := initMidSlots cord (rList.take i) rList[i] t E k
    let newChunks := initMidSlots cord (rList.take i) rList[i] (t + 1) E k
    let bun := if curEnds.length % k = 0 then oldChunks.length else oldChunks.length - 1
    Triple w pProg
      (fun st => st.mem = mem ∧ st.regs = regs0 ∧ regs0 2 = k ∧ regs0 17 = curBunBase ∧
        regs0 18 = curTagBase ∧ regs0 19 = i ∧ regs0 27 = s ∧ regs0 29 = p ∧
        regs0 30 = cap ∧ regs0 31 = mem (curTagBase + s))
      (.cond (.bin .eq (.reg 31) (.bin .add (.reg 19) (.const 1)))
        (.assign 32 (.load (.bin .add (.reg 17) (.reg 27))) ;;
         .assign 33 (.load (.bin .add (.bin .add (.bin .add (.reg 29) (.const 3)) (.reg 30)) (.reg 32))) ;;
         .cond (.bin .eq (.reg 33) (.reg 2))
           (.assign 32 (.load (.bin .add (.reg 29) (.const 1))) ;;
            .store (.bin .add (.reg 29) (.const 1)) (.bin .add (.reg 32) (.const 1)) ;;
            .store (.bin .add (.reg 17) (.reg 27)) (.reg 32))
           .nop)
        (.store (.bin .add (.reg 18) (.reg 27)) (.bin .add (.reg 19) (.const 1)) ;;
         .assign 32 (.load (.bin .add (.reg 29) (.const 1))) ;;
         .store (.bin .add (.reg 29) (.const 1)) (.bin .add (.reg 32) (.const 1)) ;;
         .store (.bin .add (.reg 17) (.reg 27)) (.reg 32)))
      (normalPost fun st' =>
        (∀ r, r ≠ 32 → r ≠ 33 → st'.regs r = regs0 r) ∧
        st'.regs 32 = bun ∧
        st'.mem (p + bsOffNB) = newChunks.length ∧
        st'.mem (curTagBase + s) = i + 1 ∧
        st'.mem (curBunBase + s) = bun ∧
        (∀ a, a ≠ p + bsOffNB → a ≠ curTagBase + s → a ≠ curBunBase + s → st'.mem a = mem a))
      (fun _ => 55) := by
  intro curEnds oldChunks newChunks bun
  have hv : rList.getD i 0 = rList[i] := List.getD_eq_getElem _ _ hi
  have hcurEnds_next : ((cord rList[i]).take (t + 1)).filter (fun y => decide (y.1 ∈ E)) =
      curEnds ++ [(cord rList[i])[t]] := by
    rw [List.take_succ_eq_append_getElem ht, List.filter_append]; simp [curEnds, hx_in]
  have hold_len : oldChunks.length =
      (initPrefixSlots cord (rList.take i) E k).length + (initialChunks k curEnds).length := by
    simp [oldChunks, curEnds, initMidSlots]
  have hnew_len : newChunks.length =
      if curEnds.length % k = 0 then oldChunks.length + 1 else oldChunks.length := by
    have h1 : newChunks.length =
        (initPrefixSlots cord (rList.take i) E k).length + (initialChunks k (curEnds ++ [(cord rList[i])[t]])).length := by
      simp only [newChunks, initMidSlots, hcurEnds_next, List.length_append, List.length_map]
    rw [h1, initialChunks_snoc_length hk1, hold_len]
    split_ifs <;> omega
  simp only [InitScanSlotInv, hv] at hI
  rcases hI with ⟨hlen_cap, _, hnb, _, hdll, _, _, _, htag0, htag1⟩
  have hnb_w : oldChunks.length + 1 < 2 ^ w := by
    have : oldChunks.length ≤ cap := hlen_cap
    unfold bundleSlotBlockSize at hp_w; omega
  have htag_lt : mem (curTagBase + s) < 2 ^ w := by
    by_cases he : curEnds = []
    · have := htag0 he; omega
    · have := (htag1 he).1; omega
  have hp1_w : p + 1 < 2 ^ w := by unfold bundleSlotBlockSize at hp_w; omega
  wram_enter
  rcases st with ⟨mem_, regs_, pos_⟩
  rcases hpre with ⟨hmem, hregs, r2, r17, r18, r19, r27, r29, r30, r31⟩
  dsimp only at hmem hregs; subst mem_; subst regs_
  by_cases he : curEnds = []
  · have htag_le : mem (curTagBase + s) ≤ i := htag0 he
    have hmod : curEnds.length % k = 0 := by simp [he]
    have hbun_v : bun = oldChunks.length := by simp [bun, hmod]
    have hnew_v : newChunks.length = oldChunks.length + 1 := by simp [hnew_len, hmod]
    have hcond : (Expr.bin .eq (.reg 31) (.bin .add (.reg 19) (.const 1))).eval w ⟨mem, regs0, pos_⟩ =
        some 0 := by
      simp [Expr.eval, BinOp.eval, r19, r31, hi1_w,
        show 1 < 2 ^ w by omega, show mem (curTagBase + s) ≠ i + 1 by omega]
    refine runs_cond_false_le hcond ?_
    wram_step
    have hne1 : p + 1 ≠ curTagBase + s := by unfold bundleSlotBlockSize at hdisj_pT; omega
    have hmem1_p1 : Function.update mem (curTagBase + s) (i + 1) (p + 1) = oldChunks.length := by
      rw [Function.update_of_ne hne1]; exact hnb
    wram_step; dsimp only; simp only [hmem1_p1]
    wram_run
    · refine ⟨fun r h32 _ => by simp [h32], by simp [hbun_v], ?_, ?_, ?_, ?_⟩
      · dsimp only; simp only [r17, r27, r29, hnew_v, bsOffNB]
        rw [Function.update_of_ne (by unfold bundleSlotBlockSize at hdisj_pB; omega), Function.update_self]
      · dsimp only; simp only [r17, r27, r29]
        rw [Function.update_of_ne (Ne.symm hdisj_BT), Function.update_of_ne (Ne.symm hne1),
          Function.update_self]
      · dsimp only; simp only [r17, r27, hbun_v]; exact Function.update_self _ _ _
      · intro a ha1 ha2 ha3
        dsimp only; simp only [r17, r27, r29, bsOffNB] at ha1 ⊢
        rw [Function.update_of_ne ha3, Function.update_of_ne ha1, Function.update_of_ne ha2]
    · wram_cost
  · obtain ⟨htag_eq, hcurB_eq⟩ := htag1 he
    have hpos_cur : 0 < (initialChunks k curEnds).length := by
      rw [initialChunks_length_eq]
      exact Nat.div_pos (by have := List.length_pos_of_ne_nil he; omega) hk1
    have hpos_old : 0 < oldChunks.length := by rw [hold_len]; omega
    have hbun0_lt : oldChunks.length - 1 < oldChunks.length := by omega
    have hcurB_val : mem (curBunBase + s) = oldChunks.length - 1 := by
      change mem (curBunBase + s) + 1 = oldChunks.length at hcurB_eq; omega
    have hlast_eq : (oldChunks[oldChunks.length - 1]'hbun0_lt).2 =
        (initialChunks k curEnds)[(initialChunks k curEnds).length - 1]'(by omega) := by
      have hge : (initPrefixSlots cord (rList.take i) E k).length ≤ oldChunks.length - 1 := by
        rw [hold_len]; omega
      have hsub : oldChunks.length - 1 - (initPrefixSlots cord (rList.take i) E k).length =
          (initialChunks k curEnds).length - 1 := by rw [hold_len]; omega
      have he1 : (initPrefixSlots cord (rList.take i) E k ++
          (initialChunks k curEnds).map (rList[i], ·))[oldChunks.length - 1]'(by
            rw [List.length_append, List.length_map, ← hold_len]; exact hbun0_lt) =
          ((initialChunks k curEnds).map (rList[i], ·))[oldChunks.length - 1 -
            (initPrefixSlots cord (rList.take i) E k).length]'(by
            rw [hsub]; simp; omega) := List.getElem_append_right hge
      have he2 : (oldChunks[oldChunks.length - 1]'hbun0_lt).2 =
          (initialChunks k curEnds)[oldChunks.length - 1 -
            (initPrefixSlots cord (rList.take i) E k).length]'(by rw [hsub]; omega) := by
        have h := congrArg Prod.snd he1
        rw [List.getElem_map] at h
        exact h
      exact he2.trans (by congr 1)
    obtain ⟨L0, _, hsz0, hlen0, _⟩ := hdll (oldChunks.length - 1) hbun0_lt
    set szLast := ((initialChunks k curEnds)[(initialChunks k curEnds).length - 1]'(by omega)).length
    have hsz0_eq : mem (bsSizeBase p cap + (oldChunks.length - 1)) = szLast := by
      rw [hsz0, hlen0, hlast_eq]
    have hsz0_le : szLast ≤ k := by
      dsimp only [szLast]; rw [initialChunks_getElem_length]; exact Nat.min_le_left _ _
    have hcond : (Expr.bin .eq (.reg 31) (.bin .add (.reg 19) (.const 1))).eval w ⟨mem, regs0, pos_⟩ =
        some 1 := by
      simp [Expr.eval, BinOp.eval, r19, r31, htag_eq, hi1_w, show 1 < 2 ^ w by omega]
    refine runs_cond_true_le hcond (by decide) ?_
    wram_step; dsimp only; simp only [hcurB_val]
    have hps_w : p + 3 + cap + (oldChunks.length - 1) < 2 ^ w := by
      have : oldChunks.length ≤ cap := hlen_cap
      unfold bundleSlotBlockSize at hp_w; omega
    wram_step; dsimp only; simp only [r29, r30]
    have hsz0_eq' : mem (p + 3 + cap + (oldChunks.length - 1)) = szLast := by
      simpa [bsSizeBase] using hsz0_eq
    simp only [hsz0_eq']
    have hiff := last_initialChunk_length_eq_k_iff hk1 he
    by_cases hmod : curEnds.length % k = 0
    · have hk_eq : szLast = k := hiff.mpr hmod
      have hbun_v : bun = oldChunks.length := by simp [bun, hmod]
      have hnew_v : newChunks.length = oldChunks.length + 1 := by simp [hnew_len, hmod]
      have hcond2 : (Expr.bin .eq (.reg 33) (.reg 2)).eval w
          ⟨mem, Function.update (Function.update regs0 32 (oldChunks.length - 1)) 33 szLast, pos_⟩ =
          some 1 := by
        simp [Expr.eval, BinOp.eval, r2, hk_eq, show 1 < 2 ^ w by omega]
      refine runs_cond_true_le hcond2 (by decide) ?_
      have hnb_p1 : mem (p + 1) = oldChunks.length := hnb
      wram_step; dsimp only; simp only [r29, hnb_p1]
      wram_run
      · refine ⟨fun r h32 h33 => by simp [h32, h33], by simp [hbun_v], ?_, ?_, ?_, ?_⟩
        · dsimp only; simp only [r17, r27, r29, hnew_v, bsOffNB]
          rw [Function.update_of_ne (by unfold bundleSlotBlockSize at hdisj_pB; omega), Function.update_self]
        · dsimp only; simp only [r17, r27, r29]
          rw [Function.update_of_ne (Ne.symm hdisj_BT),
            Function.update_of_ne (by unfold bundleSlotBlockSize at hdisj_pT; omega), htag_eq]
        · dsimp only; simp only [r17, r27, hbun_v]; exact Function.update_self _ _ _
        · intro a ha1 ha2 ha3
          dsimp only; simp only [r17, r27, r29, bsOffNB] at ha1 ⊢
          rw [Function.update_of_ne ha3, Function.update_of_ne ha1]
      · wram_cost
    · have hk_ne : szLast ≠ k := fun h => hmod (hiff.mp h)
      have hbun_v : bun = oldChunks.length - 1 := by simp [bun, hmod]
      have hnew_v : newChunks.length = oldChunks.length := by simp [hnew_len, hmod]
      have hcond2 : (Expr.bin .eq (.reg 33) (.reg 2)).eval w
          ⟨mem, Function.update (Function.update regs0 32 (oldChunks.length - 1)) 33 szLast, pos_⟩ =
          some 0 := by
        simp [Expr.eval, BinOp.eval, r2, hk_ne]
      refine runs_cond_false_le hcond2 ?_
      wram_run
      · refine ⟨fun r h32 h33 => by simp [h32, h33], by simp [hbun_v],
          hnb.trans hnew_v.symm, htag_eq, hcurB_val.trans hbun_v.symm, fun _ _ _ _ => rfl⟩
      · wram_cost

/-- Shared tail of `bundleInitEndBody`: calls `bDllPush`, increments `size[bun]`, and stores
`endBundle[key] := bun`. -/
lemma bundleInitEndTail_triple {w eCap prevBase nextBase endBunBase p cap bun key sz : ℕ}
    {pProg : Program} {bDllPush : ℕ} {L : List ℕ} {mem regs0 : ℕ → ℕ}
    (hbPush : MeetsContract w pProg bDllPush
      (bundleDllPushContract w prevBase nextBase (bsHeadBase p + bun) (2 * eCap) key L))
    (hw16 : 16 ≤ 2 ^ w)
    (hprev_w : prevBase + 2 * eCap < 2 ^ w)
    (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (hprev_next : prevBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ prevBase)
    (hhead_prev : bsHeadBase p + bun < prevBase ∨ prevBase + 2 * eCap ≤ bsHeadBase p + bun)
    (hhead_next : bsHeadBase p + bun < nextBase ∨ nextBase + 2 * eCap ≤ bsHeadBase p + bun)
    (hsize_w : bsSizeBase p cap + bun < 2 ^ w)
    (hend_w : endBunBase + key < 2 ^ w)
    (hkey_lt : key < 2 * eCap)
    (hkey_not : key ∉ L)
    (hdll : IsDoublyLinkedList mem prevBase nextBase (bsHeadBase p + bun) (2 * eCap) L)
    (hsz_mem : mem (bsSizeBase p cap + bun) = sz)
    (hsz_w : sz + 1 < 2 ^ w)
    (hsz_ne_head : bsSizeBase p cap + bun ≠ bsHeadBase p + bun)
    (hsz_disj_prev : bsSizeBase p cap + bun < prevBase ∨ prevBase + 2 * eCap ≤ bsSizeBase p cap + bun)
    (hsz_disj_next : bsSizeBase p cap + bun < nextBase ∨ nextBase + 2 * eCap ≤ bsSizeBase p cap + bun)
    (hend_ne_sz : endBunBase + key ≠ bsSizeBase p cap + bun)
    (hend_ne_head : endBunBase + key ≠ bsHeadBase p + bun)
    (hend_disj_prev : endBunBase + key < prevBase ∨ prevBase + 2 * eCap ≤ endBunBase + key)
    (hend_disj_next : endBunBase + key < nextBase ∨ nextBase + 2 * eCap ≤ endBunBase + key) :
    Triple w pProg
      (fun st => st.mem = mem ∧ st.regs = regs0 ∧ regs0 13 = endBunBase ∧ regs0 14 = prevBase ∧
        regs0 15 = nextBase ∧ regs0 24 = key ∧ regs0 29 = p ∧ regs0 30 = cap ∧
        regs0 32 = bun)
      (.call 34 bDllPush [.reg 14, .reg 15,
        .bin .add (.bin .add (.reg 29) (.const 3)) (.reg 32), .reg 24] ;;
       .assign 33 (.load (.bin .add (.bin .add (.bin .add (.reg 29) (.const 3)) (.reg 30)) (.reg 32))) ;;
       .store (.bin .add (.bin .add (.bin .add (.reg 29) (.const 3)) (.reg 30)) (.reg 32))
         (.bin .add (.reg 33) (.const 1)) ;;
       .store (.bin .add (.reg 13) (.reg 24)) (.reg 32))
      (normalPost fun st' =>
        (∀ r, r ≠ 33 → r ≠ 34 → st'.regs r = regs0 r) ∧
        IsDoublyLinkedList st'.mem prevBase nextBase (bsHeadBase p + bun) (2 * eCap) (key :: L) ∧
        st'.mem (bsSizeBase p cap + bun) = sz + 1 ∧
        st'.mem (endBunBase + key) = bun ∧
        (∀ a, a ≠ bsHeadBase p + bun → a ≠ bsSizeBase p cap + bun → a ≠ endBunBase + key →
          a ≠ prevBase + key → a ≠ nextBase + key →
          (∀ y ys, L = y :: ys → a ≠ prevBase + y) → st'.mem a = mem a))
      (fun _ => 95) := by
  wram_enter
  rcases st with ⟨mem_, regs_, pos_⟩
  rcases hpre with ⟨hmem, hregs, r13, r14, r15, r24, r29, r30, r32⟩
  dsimp only at hmem hregs; subst mem_; subst regs_
  have hp3b_w : p + 3 + bun < 2 ^ w := by unfold bsSizeBase at hsize_w; omega
  have hp3cb_w : p + 3 + cap + bun < 2 ^ w := by unfold bsSizeBase at hsize_w; omega
  have hpush_pre : (bundleDllPushContract w prevBase nextBase (bsHeadBase p + bun) (2 * eCap) key L).pre
      [prevBase, nextBase, bsHeadBase p + bun, key] mem :=
    ⟨rfl, hw16, hprev_w, hnext_w, hprev_next, hhead_prev, hhead_next, hkey_lt, hkey_not, hdll⟩
  have hargs_eval : evalArgs w ⟨mem, regs0, pos_⟩ [.reg 14, .reg 15,
      .bin .add (.bin .add (.reg 29) (.const 3)) (.reg 32), .reg 24] =
      some [prevBase, nextBase, bsHeadBase p + bun, key] := by
    unfold bsHeadBase
    simp [evalArgs, Expr.eval, BinOp.eval, r14, r15, r24, r29, r32,
      show 3 < 2 ^ w by omega, show p + 3 < 2 ^ w by omega, hp3b_w]
  have hwords : ∀ v ∈ [prevBase, nextBase, bsHeadBase p + bun, key], v < 2 ^ w := by
    intro v hv; simp at hv; unfold bsHeadBase at hv; rcases hv with rfl | rfl | rfl | rfl <;> omega
  refine runs_seq_call_le hbPush hargs_eval hwords hpush_pre fun ret mem1 pos1 ⟨_, hdll1, hfr1⟩ => ?_
  have hsz1 : mem1 (p + 3 + cap + bun) = sz := by
    have h1 := hfr1 (bsSizeBase p cap + bun) hsz_ne_head (by omega) (by omega) (fun y ys hL => by
      have hy : y < 2 * eCap := hdll.2.1 y (by rw [hL]; simp); omega)
    exact h1.trans hsz_mem
  have hsz1_reg : mem1 (regs0 29 + 3 + regs0 30 + regs0 32) = sz := by
    rw [r29, r30, r32]; exact hsz1
  wram_step; dsimp only; simp only [r29, r30, r32, hsz1]
  wram_run
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hr33 hr34; simp [hr33, hr34]
    · refine hdll1.of_agree ?_ ?_ ?_
      · dsimp only; simp only [r13, r24, r29, r30, r32]
        rw [Function.update_of_ne (Ne.symm hend_ne_head),
          Function.update_of_ne (by simpa [bsSizeBase] using Ne.symm hsz_ne_head)]
      · intro k hk
        have hk_lt : k < 2 * eCap := hdll1.2.1 k hk
        dsimp only; simp only [r13, r24, r29, r30, r32]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by unfold bsSizeBase at hsz_disj_prev; omega)]
      · intro k hk
        have hk_lt : k < 2 * eCap := hdll1.2.1 k hk
        dsimp only; simp only [r13, r24, r29, r30, r32]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by unfold bsSizeBase at hsz_disj_next; omega)]
    · dsimp only; simp only [r13, r24, r29, r30, r32]; unfold bsSizeBase at hend_ne_sz ⊢
      rw [Function.update_of_ne (Ne.symm hend_ne_sz), Function.update_self]
    · dsimp only; simp only [r13, r24, r32]; exact Function.update_self _ _ _
    · intro a ha1 ha2 ha3 ha4 ha5 ha6
      dsimp only; unfold bsSizeBase at ha2; simp only [r13, r24, r29, r30, r32]
      rw [Function.update_of_ne ha3, Function.update_of_ne ha2, hfr1 a ha1 ha4 ha5 ha6]
  · simp only [bundleDllPushContract, argsSize, Expr.size_const, Expr.size_reg, Expr.size_load,
      Expr.size_bin]; clear * -; omega

/-- Postcondition preservation helper for the active-edge push branch of `bundleInitInner_triple`. -/
lemma bundleInitInner_post {slotCap eCap tbl tourH k nSlots slotSpecPtr nEdges
    edgeAssignPtr nR rPtr h hCur hNext i t q s p cap bun key e : ℕ}
    {mem₀ : ℕ → ℕ} {specs assigns : List (ℕ × ℕ)} {cord : ℕ → List End} {rList : List ℕ}
    {st st1 st2 : State} {L : List ℕ}
    (hk1 : 1 ≤ k) (htbl_h' : tbl + (14 + 7 * slotCap + 8 * eCap) ≤ h)
    (hi : i < rList.length) (hrList_nd : rList.Nodup)
    (hspecs_lt : ∀ sb ∈ specs, sb.1 < slotCap)
    (hspecs_nd : (specs.map Prod.fst).Nodup)
    (hcord_nd : ∀ w' ∈ rList, (cord w').Nodup)
    (hcord_disj : ∀ w₁ w₂ x, x ∈ cord w₁ → x ∈ cord w₂ → w₁ = w₂)
    (hblk_end : ∀ q' (hq' : q' < specs.length),
      slotBlocksSpace (specs.take q') + bundleSlotBlockSize specs[q'].2 ≤ slotBlocksSpace specs)
    (hblk_disj : ∀ q₁ q₂ (hq₁ : q₁ < specs.length) (hq₂ : q₂ < specs.length), q₁ ≠ q₂ →
      (h + slotBlocksSpace (specs.take q₁)) + bundleSlotBlockSize specs[q₁].2 ≤
        h + slotBlocksSpace (specs.take q₂) ∨
      (h + slotBlocksSpace (specs.take q₂)) + bundleSlotBlockSize specs[q₂].2 ≤
        h + slotBlocksSpace (specs.take q₁))
    (hdisj_slotE : ∀ s₁ s₂, s₁ ≠ s₂ → ∀ e' ∈ slotEdgesOf assigns s₁, e' ∉ slotEdgesOf assigns s₂)
    (hend_lt_2e : ∀ y : End, (∃ s' ∈ specs.map Prod.fst, y.1 ∈ slotEdgesOf assigns s') →
      endKey y < 2 * eCap)
    (hq_len : q < specs.length) (hsq_eq : specs[q].1 = s) (hs_lt : s < slotCap)
    (hs_mem : s ∈ specs.map Prod.fst)
    (hp_eq : p = h + slotBlocksSpace (specs.take q)) (hcap_eq : cap = specs[q].2)
    (hp_blk : p + (3 + 6 * cap) ≤ h + slotBlocksSpace specs) (hp_ge : h ≤ p)
    (hv_eq : rList.getD i 0 = rList[i])
    (ht : t < (cord (rList.getD i 0)).length) (ht_r : t < (cord rList[i]).length)
    (hkey_eq : key = endKey ((cord (rList.getD i 0))[t]'ht))
    (he_eq : e = ((cord (rList.getD i 0))[t]'ht).1)
    (he_s : e ∈ slotEdgesOf assigns s) (hx_r : ((cord rList[i])[t]'ht_r).1 ∈ slotEdgesOf assigns s)
    (hkey_lt : key < 2 * eCap)
    (hcap_next : (initMidSlots cord (rList.take i) rList[i] (t + 1) (slotEdgesOf assigns s) k).length ≤ cap)
    (hbun_eq_def : bun =
      if (((cord rList[i]).take t).filter fun y => decide (y.1 ∈ slotEdgesOf assigns s)).length % k = 0
      then (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k).length
      else (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k).length - 1)
    (hbun_lt_cap : bun < cap)
    (hpos_of_ne : (((cord rList[i]).take t).filter fun y => decide (y.1 ∈ slotEdgesOf assigns s)) ≠ [] →
      0 < (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k).length)
    (hfresh : ∀ b (hb : b < (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k).length),
      (cord rList[i])[t]'ht_r ∉ (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k)[b].2)
    (hL1 : IsDoublyLinkedList st1.mem (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) (bsHeadBase p + bun) (2 * eCap) L)
    (hsz1 : st1.mem (bsSizeBase p cap + bun) = L.length)
    (hL_nil : (((cord rList[i]).take t).filter fun y => decide (y.1 ∈ slotEdgesOf assigns s)).length % k = 0 →
      L = [])
    (hL_mem : ∀ key', key' ∈ L ↔
      ∃ hlt : bun < (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k).length,
        endOfKey key' ∈ (initMidSlots cord (rList.take i) rList[i] t (slotEdgesOf assigns s) k)[bun].2)
    (hc : BundleInitConstRegs st tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
      slotCap eCap)
    (r10 : st.regs 10 = hCur) (r17 : st.regs 17 = btCurBunBase tbl slotCap eCap)
    (r18 : st.regs 18 = btCurTagBase tbl slotCap eCap) (r19 : st.regs 19 = i)
    (r21 : st.regs 21 = hNext) (r22 : st.regs 22 = (cord (rList.getD i 0)).length) (r23 : st.regs 23 = t)
    (hslots : ∀ q' (hq' : q' < specs.length),
      InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
        (btEndBundleBase tbl slotCap eCap) (btCurBunBase tbl slotCap eCap)
        (btCurTagBase tbl slotCap eCap) cord rList i t specs[q'].1
        (h + slotBlocksSpace (specs.take q')) specs[q'].2 k (slotEdgesOf assigns specs[q'].1) st.mem)
    (hfr : ∀ a,
      (a < h ∨ h + slotBlocksSpace specs ≤ a) →
      (∀ y : End, (∃ s' ∈ specs.map Prod.fst, y.1 ∈ slotEdgesOf assigns s') →
        a ≠ btEndBundleBase tbl slotCap eCap + endKey y ∧
        a ≠ btEndPrevBase tbl slotCap eCap + endKey y ∧
        a ≠ btEndNextBase tbl slotCap eCap + endKey y) →
      (∀ s' ∈ specs.map Prod.fst,
        a ≠ btCurBunBase tbl slotCap eCap + s' ∧
        a ≠ btCurTagBase tbl slotCap eCap + s') →
      st.mem a = mem₀ a)
    (hregs1 : ∀ r, r ≠ 32 → r ≠ 33 →
      st1.regs r = (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update st.regs 24 key) 25 e) 26 (s + 1))
        27 s) 28 1) 29 p) 30 cap) 31 (st.mem (btCurTagBase tbl slotCap eCap + s))) r)
    (hnb1 : st1.mem (p + bsOffNB) =
      (initMidSlots cord (rList.take i) rList[i] (t + 1) (slotEdgesOf assigns s) k).length)
    (htag1 : st1.mem (btCurTagBase tbl slotCap eCap + s) = i + 1)
    (hcurB1 : st1.mem (btCurBunBase tbl slotCap eCap + s) = bun)
    (hfr1 : ∀ a, a ≠ p + bsOffNB → a ≠ btCurTagBase tbl slotCap eCap + s →
      a ≠ btCurBunBase tbl slotCap eCap + s → st1.mem a = st.mem a)
    (hregs2 : ∀ r, r ≠ 33 → r ≠ 34 → st2.regs r = st1.regs r)
    (hdll2 : IsDoublyLinkedList st2.mem (btEndPrevBase tbl slotCap eCap)
      (btEndNextBase tbl slotCap eCap) (bsHeadBase p + bun) (2 * eCap) (key :: L))
    (hsz2 : st2.mem (bsSizeBase p cap + bun) = L.length + 1)
    (hend2 : st2.mem (btEndBundleBase tbl slotCap eCap + key) = bun)
    (hfr2 : ∀ a, a ≠ bsHeadBase p + bun → a ≠ bsSizeBase p cap + bun →
      a ≠ btEndBundleBase tbl slotCap eCap + key →
      a ≠ btEndPrevBase tbl slotCap eCap + key →
      a ≠ btEndNextBase tbl slotCap eCap + key →
      (∀ y ys, L = y :: ys → a ≠ btEndPrevBase tbl slotCap eCap + y) →
      st2.mem a = st1.mem a) :
    let stNext := { st2 with regs := Function.update st2.regs 23 (t + 1) }
    (BundleInitConstRegs stNext tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
      slotCap eCap ∧
      stNext.regs 10 = hCur ∧ stNext.regs 17 = btCurBunBase tbl slotCap eCap ∧
      stNext.regs 18 = btCurTagBase tbl slotCap eCap ∧ stNext.regs 19 = i ∧
      stNext.regs 21 = hNext ∧ stNext.regs 22 = (cord (rList.getD i 0)).length ∧
      stNext.regs 23 = t + 1 ∧
      (∀ q' (hq' : q' < specs.length),
        InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
          (btEndBundleBase tbl slotCap eCap) (btCurBunBase tbl slotCap eCap)
          (btCurTagBase tbl slotCap eCap) cord rList i (t + 1) specs[q'].1
          (h + slotBlocksSpace (specs.take q')) specs[q'].2 k (slotEdgesOf assigns specs[q'].1) stNext.mem) ∧
      (∀ a,
        (a < h ∨ h + slotBlocksSpace specs ≤ a) →
        (∀ y : End, (∃ s' ∈ specs.map Prod.fst, y.1 ∈ slotEdgesOf assigns s') →
          a ≠ btEndBundleBase tbl slotCap eCap + endKey y ∧
          a ≠ btEndPrevBase tbl slotCap eCap + endKey y ∧
          a ≠ btEndNextBase tbl slotCap eCap + endKey y) →
        (∀ s' ∈ specs.map Prod.fst,
          a ≠ btCurBunBase tbl slotCap eCap + s' ∧
          a ≠ btCurTagBase tbl slotCap eCap + s') →
        stNext.mem a = mem₀ a)) ∧
    st2.regs 23 = t := by
  have ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc35,
    hr11, hr12, hr13, hr14, hr15, hr16⟩ : st.regs 0 = tbl ∧ _ := hc
  set E_q := slotEdgesOf assigns s
  set oldChunks := initMidSlots cord (rList.take i) rList[i] t E_q k
  have hx_eq : (cord (rList.getD i 0))[t]'ht = (cord rList[i])[t]'ht_r := by simp only [hv_eq]
  have hIq : InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap) (btEndNextBase tbl slotCap eCap)
      (btEndBundleBase tbl slotCap eCap) (btCurBunBase tbl slotCap eCap)
      (btCurTagBase tbl slotCap eCap) cord rList i t s p cap k E_q st.mem := by
    have hq := hslots q hq_len; rwa [hsq_eq, ← hp_eq, ← hcap_eq] at hq
  have hreg_eq : ∀ r, r < 24 ∨ r = 35 → st2.regs r = st.regs r := fun r hr => by
    rw [hregs2 r (by clear * - hr; omega) (by clear * - hr; omega),
      hregs1 r (by clear * - hr; omega) (by clear * - hr; omega)]
    simp [show r ≠ 31 by clear * - hr; omega, show r ≠ 30 by clear * - hr; omega,
      show r ≠ 29 by clear * - hr; omega, show r ≠ 28 by clear * - hr; omega,
      show r ≠ 27 by clear * - hr; omega, show r ≠ 26 by clear * - hr; omega,
      show r ≠ 25 by clear * - hr; omega, show r ≠ 24 by clear * - hr; omega]
  have hL1_lt : ∀ y ys, L = y :: ys → y < 2 * eCap := fun y ys hL => hL1.2.1 y (by rw [hL]; simp)
  have hfr2_ge_h : ∀ a, h ≤ a → a ≠ bsHeadBase p + bun → a ≠ bsSizeBase p cap + bun →
      st2.mem a = st1.mem a := fun a ha h1 h2 =>
    hfr2 a h1 h2
      (by unfold btEndBundleBase; clear * - htbl_h' ha hkey_lt; omega)
      (by unfold btEndPrevBase; clear * - htbl_h' ha hkey_lt; omega)
      (by unfold btEndNextBase; clear * - htbl_h' ha hkey_lt; omega)
      (fun y ys hL => by
        have hy := hL1_lt y ys hL; unfold btEndPrevBase; clear * - htbl_h' ha hy; omega)
  have hst2_ge_h : ∀ a, h ≤ a → a ≠ p + bsOffNB →
      a ≠ bsHeadBase p + bun → a ≠ bsSizeBase p cap + bun → st2.mem a = st.mem a :=
    fun a ha h1 h4 h5 => (hfr2_ge_h a ha h4 h5).trans
      (hfr1 a h1 (by unfold btCurTagBase; clear * - htbl_h' ha hs_lt; omega)
        (by unfold btCurBunBase; clear * - htbl_h' ha hs_lt; omega))
  have hst2_tbl : ∀ a, a < h →
      a ≠ btCurTagBase tbl slotCap eCap + s →
      a ≠ btCurBunBase tbl slotCap eCap + s →
      a ≠ btEndBundleBase tbl slotCap eCap + key →
      a ≠ btEndPrevBase tbl slotCap eCap + key →
      a ≠ btEndNextBase tbl slotCap eCap + key →
      (∀ y ys, L = y :: ys → a ≠ btEndPrevBase tbl slotCap eCap + y) →
      st2.mem a = st.mem a := fun a ha hct hcb h1 h2 h3 h4 =>
    (hfr2 a (by unfold bsHeadBase; clear * - ha hp_ge; omega)
      (by unfold bsSizeBase; clear * - ha hp_ge; omega) h1 h2 h3 h4).trans
      (hfr1 a (by unfold bsOffNB; clear * - ha hp_ge; omega) hct hcb)
  refine ⟨⟨?_, by dsimp only; rw [Function.update_of_ne (by decide), hreg_eq 10 (by decide)]; exact r10,
    by dsimp only; rw [Function.update_of_ne (by decide), hreg_eq 17 (by decide)]; exact r17,
    by dsimp only; rw [Function.update_of_ne (by decide), hreg_eq 18 (by decide)]; exact r18,
    by dsimp only; rw [Function.update_of_ne (by decide), hreg_eq 19 (by decide)]; exact r19,
    by dsimp only; rw [Function.update_of_ne (by decide), hreg_eq 21 (by decide)]; exact r21,
    by dsimp only; rw [Function.update_of_ne (by decide), hreg_eq 22 (by decide)]; exact r22,
    by simp, ?_, ?_⟩,
    by rw [hreg_eq 23 (by decide)]; exact r23⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (dsimp only; rwa [Function.update_of_ne (by decide), hreg_eq _ (by decide)])
  · intro q' hq'
    by_cases hqq : q' = q
    · subst hqq; rw [hsq_eq, ← hp_eq, ← hcap_eq]
      refine InitScanSlotInv.step_push hk1 hi ht_r hx_r hIq hcap_next hfresh hbun_eq_def hdll2 ?_ ?_
        ?_ hsz2 ?_ ?_ ?_ ?_ ?_ ?_
      · simp only [List.length_cons]
        split_ifs with hmod
        · rw [hL_nil hmod]; simp
        · have hpos_old := hpos_of_ne (fun h0 => hmod (by rw [h0]; simp))
          have hbun_lt : bun < oldChunks.length := by
            rw [hbun_eq_def]; dsimp only [E_q]; simp only [hmod, ↓reduceIte]; clear * - hpos_old; omega
          have hIq' : InitScanSlotInv eCap (btEndPrevBase tbl slotCap eCap)
              (btEndNextBase tbl slotCap eCap) (btEndBundleBase tbl slotCap eCap)
              (btCurBunBase tbl slotCap eCap) (btCurTagBase tbl slotCap eCap) cord rList i t
              s p cap k E_q st.mem := hIq
          simp only [InitScanSlotInv, List.getD_eq_getElem _ _ hi] at hIq'
          obtain ⟨L', _, hsz', hlen', _⟩ := hIq'.2.2.2.2.1 bun hbun_lt
          have hsz_eq : st1.mem (bsSizeBase p cap + bun) = st.mem (bsSizeBase p cap + bun) :=
            hfr1 _ (by unfold bsSizeBase bsOffNB; clear * -; omega)
              (by unfold bsSizeBase btCurTagBase; clear * - htbl_h' hp_ge hs_lt; omega)
              (by unfold bsSizeBase btCurBunBase; clear * - htbl_h' hp_ge hs_lt; omega)
          dsimp only [E_q] at hlen'
          clear * - hsz1 hsz_eq hsz' hlen'; omega
      · intro key'
        rw [List.mem_cons, hL_mem key']
        exact ⟨fun h => h.elim (fun he => Or.inl (by rw [he, hkey_eq, bundle_endOfKey_endKey, hx_eq]))
          Or.inr, fun h => h.elim (fun he => Or.inl (by rw [hkey_eq, hx_eq, ← he, bundle_endKey_endOfKey]))
          Or.inr⟩
      · exact (hfr2_ge_h _ (by clear * - hp_ge; omega)
          (by unfold bsOffNB bsHeadBase; clear * -; omega)
          (by unfold bsOffNB bsSizeBase; clear * -; omega)).trans hnb1
      · rw [← hx_eq, ← hkey_eq]; exact hend2
      · exact (hfr2 _
          (by unfold bsHeadBase btCurTagBase; clear * - htbl_h' hp_ge hs_lt; omega)
          (by unfold bsSizeBase btCurTagBase; clear * - htbl_h' hp_ge hs_lt; omega)
          (by unfold btEndBundleBase btCurTagBase; clear * - hkey_lt; omega)
          (by unfold btEndPrevBase btCurTagBase; clear * - hkey_lt; omega)
          (by unfold btEndNextBase btCurTagBase; clear * - hkey_lt; omega)
          (fun y ys hL => by
            have hy := hL1_lt y ys hL; unfold btEndPrevBase btCurTagBase; clear * - hy; omega)).trans htag1
      · exact (hfr2 _
          (by unfold bsHeadBase btCurBunBase; clear * - htbl_h' hp_ge hs_lt; omega)
          (by unfold bsSizeBase btCurBunBase; clear * - htbl_h' hp_ge hs_lt; omega)
          (by unfold btEndBundleBase btCurBunBase; clear * - hkey_lt; omega)
          (by unfold btEndPrevBase btCurBunBase; clear * - hkey_lt; omega)
          (by unfold btEndNextBase btCurBunBase; clear * - hkey_lt; omega)
          (fun y ys hL => by
            have hy := hL1_lt y ys hL; unfold btEndPrevBase btCurBunBase; clear * - hy; omega)).trans hcurB1
      · intro off _ hne1 hne2 hne3
        exact hst2_ge_h (p + off) (by clear * - hp_ge; omega) hne1 hne2 hne3
      · intro b hb hbb key' hkey'
        have hne_key : key' ≠ key := fun heq =>
          hfresh b hb (by
            have h1 : endOfKey key' = (cord rList[i])[t]'ht_r := by
              rw [heq, hkey_eq, bundle_endOfKey_endKey, hx_eq]
            rwa [← h1])
        have hkey'_lt : key' < 2 * eCap := by
          have he_in : (endOfKey key').1 ∈ E_q := (mem_initMidSlots_end hk1 hb hkey').1
          simpa [bundle_endKey_endOfKey] using hend_lt_2e (endOfKey key') ⟨s, hs_mem, he_in⟩
        have hne_y : ∀ y ys, L = y :: ys → key' ≠ y := fun y ys hL heq => by
          subst heq
          obtain ⟨hbun_lt, hmem_bun⟩ := (hL_mem key').mp (by rw [hL]; simp)
          have hflat_nd : (oldChunks.flatMap Prod.snd).Nodup := by
            have : oldChunks.flatMap Prod.snd =
                ((rList.take i).flatMap fun w' => (cord w').filter fun z => decide (z.1 ∈ E_q)) ++
                (((cord rList[i]).take t).filter fun z => decide (z.1 ∈ E_q)) := by
              simp only [oldChunks, initMidSlots, initPrefixSlots, List.flatMap_append,
                List.flatMap_assoc, List.flatMap_map]
              congr 1
              · apply List.flatMap_congr; intro w' _
                simpa [List.flatten] using (initialChunks_spec hk1 ((cord w').filter fun x => decide (x.1 ∈ E_q))).1
              · simpa [List.flatten] using (initialChunks_spec hk1 (((cord rList[i]).take t).filter fun x => decide (x.1 ∈ E_q))).1
            rw [this, List.nodup_append]
            refine ⟨List.nodup_flatMap.mpr ⟨fun w' hw' =>
                (hcord_nd w' (List.mem_of_mem_take hw')).filter _,
                hrList_nd.take.imp fun hne =>
                  List.disjoint_left.mpr fun z hz1 hz2 =>
                    hne (hcord_disj _ _ z (List.mem_filter.mp hz1).1 (List.mem_filter.mp hz2).1)⟩,
              ((hcord_nd rList[i] (List.getElem_mem hi)).take).filter _,
              fun z hz1 z' hz2 heq => ?_⟩
            subst heq
            obtain ⟨w', hw', hzw'⟩ := List.mem_flatMap.mp hz1
            have hw_eq := hcord_disj w' rList[i] z (List.mem_filter.mp hzw').1
              (List.mem_of_mem_take (List.mem_filter.mp hz2).1)
            subst hw_eq
            obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hw'
            have hj_lt : j < i := by simp at hj; omega
            have := hrList_nd.getElem_inj_iff.mp (show rList[j]'(by omega) = rList[i] by
              simpa [List.getElem_take] using hjeq)
            omega
          have hpw := (List.nodup_flatMap.mp hflat_nd).2
          rcases Nat.lt_or_gt_of_ne hbb with hlt | hgt
          · exact List.disjoint_left.mp (List.pairwise_iff_getElem.mp hpw b bun hb hbun_lt hlt)
              hkey' hmem_bun
          · exact List.disjoint_left.mp (List.pairwise_iff_getElem.mp hpw bun b hbun_lt hb hgt)
              hmem_bun hkey'
        exact ⟨hst2_tbl _ (by unfold btEndPrevBase; clear * - htbl_h' hkey'_lt; omega)
          (by unfold btEndPrevBase btCurTagBase; clear * - hkey'_lt; omega)
          (by unfold btEndPrevBase btCurBunBase; clear * - hkey'_lt; omega)
          (by unfold btEndPrevBase btEndBundleBase; clear * - hkey_lt; omega)
          (by clear * - hne_key; omega)
          (by unfold btEndPrevBase btEndNextBase; clear * - hkey'_lt; omega)
          (fun y ys hL => by have := hne_y y ys hL; clear * - this; omega),
          hst2_tbl _ (by unfold btEndNextBase; clear * - htbl_h' hkey'_lt; omega)
          (by unfold btEndNextBase btCurTagBase; clear * - hkey'_lt; omega)
          (by unfold btEndNextBase btCurBunBase; clear * - hkey'_lt; omega)
          (by unfold btEndNextBase btEndBundleBase; clear * - hkey_lt; omega)
          (by unfold btEndNextBase btEndPrevBase; clear * - hkey_lt; omega)
          (by clear * - hne_key; omega)
          (fun y ys hL => by
            have hy := hL1_lt y ys hL; unfold btEndNextBase btEndPrevBase; clear * - hy; omega)⟩
      · intro y hy_in hy
        have hy_lt : endKey y < 2 * eCap := hend_lt_2e y ⟨s, hs_mem, hy_in⟩
        have hne_k : endKey y ≠ key := fun heq => hy (by
          have := congrArg endOfKey heq
          rwa [bundle_endOfKey_endKey, hkey_eq, bundle_endOfKey_endKey, hx_eq] at this)
        exact hst2_tbl _ (by unfold btEndBundleBase; clear * - htbl_h' hy_lt; omega)
          (by unfold btEndBundleBase btCurTagBase; clear * - hy_lt; omega)
          (by unfold btEndBundleBase btCurBunBase; clear * - hy_lt; omega)
          (by clear * - hne_k; omega)
          (by unfold btEndBundleBase btEndPrevBase; clear * - hy_lt; omega)
          (by unfold btEndBundleBase btEndNextBase; clear * - hy_lt; omega)
          (fun z zs hL => by
            have hz := hL1_lt z zs hL; unfold btEndBundleBase btEndPrevBase; clear * - hy_lt hz; omega)
    · have hs'_ne : specs[q'].1 ≠ s := fun heq => hqq (hspecs_nd.getElem_inj_iff.mp
        (show (specs.map Prod.fst)[q']'(by simp [hq']) = (specs.map Prod.fst)[q]'(by simp [hq_len]) by
          simpa [hsq_eq] using heq))
      have hnot_in : ((cord (rList.getD i 0))[t]'ht).1 ∉ slotEdgesOf assigns specs[q'].1 :=
        he_eq ▸ hdisj_slotE s specs[q'].1 (Ne.symm hs'_ne) e he_s
      have hskip := (hslots q' hq').step_skip ht hnot_in
      have hdisj_q : p + (3 + 6 * cap) ≤ h + slotBlocksSpace (specs.take q') ∨
          h + slotBlocksSpace (specs.take q') + (3 + 6 * specs[q'].2) ≤ p := by
        rw [hp_eq, hcap_eq]; exact hblk_disj q q' hq_len hq' (Ne.symm hqq)
      have hs'_lt := hspecs_lt specs[q'] (List.getElem_mem hq')
      have hsq'_mem : specs[q'].1 ∈ specs.map Prod.fst :=
        List.mem_map.mpr ⟨specs[q'], List.getElem_mem hq', rfl⟩
      refine hskip.of_agree hk1 ?_ ?_ ?_ ?_ ?_ ?_
      · intro a ha1 ha2
        have ha2' : a < h + slotBlocksSpace (specs.take q') + (3 + 6 * specs[q'].2) := ha2
        exact (hst2_ge_h a (by clear * - ha1; omega)
          (by unfold bsOffNB; clear * - hdisj_q ha1 ha2'; omega)
          (by unfold bsHeadBase; clear * - hdisj_q ha1 ha2' hbun_lt_cap; omega)
          (by unfold bsSizeBase; clear * - hdisj_q ha1 ha2' hbun_lt_cap; omega)).symm
      · intro key' hkey'
        have hkey'_lt : key' < 2 * eCap := by
          simpa [bundle_endKey_endOfKey] using hend_lt_2e (endOfKey key') ⟨specs[q'].1, hsq'_mem, hkey'⟩
        have hne1 : key' ≠ key := fun heq => hnot_in (by
          have h1 := congrArg (fun z => (endOfKey z).1) heq
          rw [hkey_eq, bundle_endOfKey_endKey] at h1; exact h1 ▸ hkey')
        have hne_y : ∀ y ys, L = y :: ys → key' ≠ y := fun y ys hL heq => by
          subst heq
          obtain ⟨hlt, hmem⟩ := (hL_mem key').mp (by rw [hL]; simp)
          exact hdisj_slotE s specs[q'].1 (Ne.symm hs'_ne) (endOfKey key').1
            (mem_initMidSlots_end hk1 hlt hmem).1 hkey'
        exact (hst2_tbl _ (by unfold btEndPrevBase; clear * - htbl_h' hkey'_lt; omega)
          (by unfold btEndPrevBase btCurTagBase; clear * - hkey'_lt; omega)
          (by unfold btEndPrevBase btCurBunBase; clear * - hkey'_lt; omega)
          (by unfold btEndPrevBase btEndBundleBase; clear * - hkey_lt; omega)
          (by clear * - hne1; omega)
          (by unfold btEndPrevBase btEndNextBase; clear * - hkey'_lt; omega)
          (fun y ys hL => by have := hne_y y ys hL; clear * - this; omega)).symm
      · intro key' hkey'
        have hkey'_lt : key' < 2 * eCap := by
          simpa [bundle_endKey_endOfKey] using hend_lt_2e (endOfKey key') ⟨specs[q'].1, hsq'_mem, hkey'⟩
        have hne1 : key' ≠ key := fun heq => hnot_in (by
          have h1 := congrArg (fun z => (endOfKey z).1) heq
          rw [hkey_eq, bundle_endOfKey_endKey] at h1; exact h1 ▸ hkey')
        exact (hst2_tbl _ (by unfold btEndNextBase; clear * - htbl_h' hkey'_lt; omega)
          (by unfold btEndNextBase btCurTagBase; clear * - hkey'_lt; omega)
          (by unfold btEndNextBase btCurBunBase; clear * - hkey'_lt; omega)
          (by unfold btEndNextBase btEndBundleBase; clear * - hkey_lt; omega)
          (by unfold btEndNextBase btEndPrevBase; clear * - hkey_lt; omega)
          (by clear * - hne1; omega)
          (fun y ys hL => by
            have hy := hL1_lt y ys hL; unfold btEndNextBase btEndPrevBase; clear * - hy; omega)).symm
      · intro y hy
        have hy_lt : endKey y < 2 * eCap := hend_lt_2e y ⟨specs[q'].1, hsq'_mem, hy⟩
        have hne1 : endKey y ≠ key := fun heq => hnot_in (by
          have h1 := congrArg (fun z => (endOfKey z).1) heq
          rw [bundle_endOfKey_endKey, hkey_eq, bundle_endOfKey_endKey] at h1; exact h1 ▸ hy)
        exact (hst2_tbl _ (by unfold btEndBundleBase; clear * - htbl_h' hy_lt; omega)
          (by unfold btEndBundleBase btCurTagBase; clear * - hy_lt; omega)
          (by unfold btEndBundleBase btCurBunBase; clear * - hy_lt; omega)
          (by clear * - hne1; omega)
          (by unfold btEndBundleBase btEndPrevBase; clear * - hy_lt; omega)
          (by unfold btEndBundleBase btEndNextBase; clear * - hy_lt; omega)
          (fun z zs hL => by
            have hz := hL1_lt z zs hL; unfold btEndBundleBase btEndPrevBase; clear * - hy_lt hz; omega)).symm
      · exact (hst2_tbl _ (by unfold btCurBunBase; clear * - htbl_h' hs'_lt; omega)
          (by unfold btCurBunBase btCurTagBase; clear * - hs'_lt; omega)
          (by clear * - hs'_ne; omega)
          (by unfold btCurBunBase btEndBundleBase; clear * - hkey_lt; omega)
          (by unfold btCurBunBase btEndPrevBase; clear * - hkey_lt; omega)
          (by unfold btCurBunBase btEndNextBase; clear * - hkey_lt; omega)
          (fun y ys hL => by
            have hy := hL1_lt y ys hL; unfold btCurBunBase btEndPrevBase; clear * - hy; omega)).symm
      · exact (hst2_tbl _ (by unfold btCurTagBase; clear * - htbl_h' hs'_lt; omega)
          (by clear * - hs'_ne; omega)
          (by unfold btCurTagBase btCurBunBase; clear * - hs_lt; omega)
          (by unfold btCurTagBase btEndBundleBase; clear * - hkey_lt; omega)
          (by unfold btCurTagBase btEndPrevBase; clear * - hkey_lt; omega)
          (by unfold btCurTagBase btEndNextBase; clear * - hkey_lt; omega)
          (fun y ys hL => by
            have hy := hL1_lt y ys hL; unfold btCurTagBase btEndPrevBase; clear * - hy; omega)).symm
  · intro a ha1 ha2 ha3
    have hax := ha2 ((cord (rList.getD i 0))[t]'ht) ⟨s, hs_mem, he_eq ▸ he_s⟩
    have has := ha3 s hs_mem
    rw [← hkey_eq] at hax
    rcases ha1 with ha_lt | ha_ge
    · exact (hst2_tbl a ha_lt has.2 has.1 hax.1 hax.2.1 hax.2.2 fun y ys hL => by
        obtain ⟨hlt, hmem⟩ := (hL_mem y).mp (by rw [hL]; simp)
        have hay := ha2 (endOfKey y) ⟨s, hs_mem, (mem_initMidSlots_end hk1 hlt hmem).1⟩
        simpa [bundle_endKey_endOfKey] using hay.2.1).trans (hfr a (Or.inl ha_lt) ha2 ha3)
    · exact (hst2_ge_h a (by clear * - ha_ge; omega)
        (by unfold bsOffNB; clear * - hp_blk ha_ge; omega)
        (by unfold bsHeadBase; clear * - hp_blk hbun_lt_cap ha_ge; omega)
        (by unfold bsSizeBase; clear * - hp_blk hbun_lt_cap ha_ge; omega)).trans
        (hfr a (Or.inr ha_ge) ha2 ha3)

end

end MinCostFlow.SparseCore.Program
