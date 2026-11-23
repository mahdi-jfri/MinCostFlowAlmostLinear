module

public import MinCostFlow.SparseCore.Program.BundleStepDel

/-!
# Slot and table preservation for Phase 1 deletion (`BundleStepDelSlot`)

Proves `bundleSlotRepAt_erase_edge` and `bundleStepDel_active_post`, assembling the full
`BundleTableAfterDel`, `ListAt`, and external frame postconditions after one active-edge deletion.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

public section

/-- Preserves `BundleSlotRepAt` when removing edge `e ∈ B.edges` after erasing both ends `(e, true)`
and `(e, false)` from their respective DLLs and decrementing `nE`. -/
lemma bundleSlotRepAt_erase_edge {eCap prevBase nextBase p bunCap e b1 b2 : ℕ}
    {B : BundleState} {mem mem1 mem2 mem3 : ℕ → ℕ} {L1 L2 : List ℕ}
    (heB : e ∈ B.edges)
    (hrep : BundleSlotRepAt eCap prevBase nextBase p bunCap B mem)
    (hb1 : b1 = B.bundleOf (e, true)) (hb2 : b2 = B.bundleOf (e, false))
    (hL1_nd : L1.Nodup) (hL2_nd : L2.Nodup)
    (hL1_lt : ∀ k ∈ L1, k < 2 * eCap) (hL2_lt : ∀ k ∈ L2, k < 2 * eCap)
    (hL1_mem : ∀ k, k ∈ L1 ↔ endOfKey k ∈ B.ends b1)
    (hL2_mem : ∀ k, k ∈ L2 ↔ endOfKey k ∈ B.ends b2)
    (hprev_next : prevBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ prevBase)
    (h1_dll : IsDoublyLinkedList mem1 prevBase nextBase (bsHeadBase p + b1) (2 * eCap) (L1.erase (2 * e)))
    (h1_sz : mem1 (bsSizeBase p bunCap + b1) = (L1.erase (2 * e)).length)
    (h1_par0 : L1.erase (2 * e) = [] → mem1 (bsParentBase p bunCap + b1) = B.parent b1)
    (h1_fr : ∀ a, a ≠ bsHeadBase p + b1 → a ≠ bsSizeBase p bunCap + b1 →
      a ≠ bsParentBase p bunCap + b1 →
      (∀ k ∈ L1, a ≠ prevBase + k ∧ a ≠ nextBase + k) → mem1 a = mem a)
    (h2_dll : IsDoublyLinkedList mem2 prevBase nextBase (bsHeadBase p + b2) (2 * eCap)
      ((if b2 = b1 then L1.erase (2 * e) else L2).erase (2 * e + 1)))
    (h2_sz : mem2 (bsSizeBase p bunCap + b2) =
      ((if b2 = b1 then L1.erase (2 * e) else L2).erase (2 * e + 1)).length)
    (h2_par0 : (if b2 = b1 then L1.erase (2 * e) else L2).erase (2 * e + 1) = [] →
      mem2 (bsParentBase p bunCap + b2) = B.parent b2)
    (h2_fr : ∀ a, a ≠ bsHeadBase p + b2 → a ≠ bsSizeBase p bunCap + b2 →
      a ≠ bsParentBase p bunCap + b2 →
      (∀ k ∈ (if b2 = b1 then L1.erase (2 * e) else L2), a ≠ prevBase + k ∧ a ≠ nextBase + k) →
      mem2 a = mem1 a)
    (h3_nE : mem3 (p + bsOffNE) = B.edges.card - 1)
    (h3_eq : ∀ a, a ≠ p + bsOffNE → (p ≤ a ∧ a < p + bundleSlotBlockSize bunCap ∨
        (prevBase ≤ a ∧ a < prevBase + 2 * eCap) ∨ (nextBase ≤ a ∧ a < nextBase + 2 * eCap)) →
      mem3 a = mem2 a)
    (hblk_prev : p + bundleSlotBlockSize bunCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ p)
    (hblk_next : p + bundleSlotBlockSize bunCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ p) :
    BundleSlotRepAt eCap prevBase nextBase p bunCap { B with edges := B.edges.erase e } mem3 := by
  obtain ⟨nB, hV, hnB, hE, hbo, hpar0, h0, h1, h2, hdll, hpar, htail, hscr⟩ := hrep
  have hb1_lt : b1 < nB := hb1 ▸ hbo (e, true) ((mem_edgeEnds _ _).mpr heB)
  have hb2_lt : b2 < nB := hb2 ▸ hbo (e, false) ((mem_edgeEnds _ _).mpr heB)
  have hblk_prev' : p + (3 + 6 * bunCap) ≤ prevBase ∨ prevBase + 2 * eCap ≤ p := hblk_prev
  have hblk_next' : p + (3 + 6 * bunCap) ≤ nextBase ∨ nextBase + 2 * eCap ≤ p := hblk_next
  set L2pre := if b2 = b1 then L1.erase (2 * e) else L2
  have hL2pre_lt : ∀ k ∈ L2pre, k < 2 * eCap := fun k hk => by
    dsimp only [L2pre] at hk; split_ifs at hk
    · exact hL1_lt k (List.mem_of_mem_erase hk)
    · exact hL2_lt k hk
  have hmem3_blk : ∀ off < bundleSlotBlockSize bunCap, off ≠ bsOffNE → mem3 (p + off) = mem2 (p + off) :=
    fun off hoff hne => h3_eq (p + off) (by omega) (Or.inl ⟨by omega, by omega⟩)
  have hmem3_prev : ∀ k < 2 * eCap, mem3 (prevBase + k) = mem2 (prevBase + k) := fun k hk =>
    h3_eq (prevBase + k) (by unfold bsOffNE; clear * - hblk_prev' hk; omega)
      (Or.inr (Or.inl ⟨by omega, by omega⟩))
  have hmem3_next : ∀ k < 2 * eCap, mem3 (nextBase + k) = mem2 (nextBase + k) := fun k hk =>
    h3_eq (nextBase + k) (by unfold bsOffNE; clear * - hblk_next' hk; omega)
      (Or.inr (Or.inr ⟨by omega, by omega⟩))
  have hblk_not_pn : ∀ off < bundleSlotBlockSize bunCap, ∀ k < 2 * eCap,
      p + off ≠ prevBase + k ∧ p + off ≠ nextBase + k := fun off hoff k hk => by
    have hoff' : off < 3 + 6 * bunCap := hoff
    exact ⟨by clear * - hblk_prev' hoff' hk; omega, by clear * - hblk_next' hoff' hk; omega⟩
  have h21_eq : ∀ off < bundleSlotBlockSize bunCap,
      p + off ≠ bsHeadBase p + b1 → p + off ≠ bsSizeBase p bunCap + b1 →
      p + off ≠ bsParentBase p bunCap + b1 →
      p + off ≠ bsHeadBase p + b2 → p + off ≠ bsSizeBase p bunCap + b2 →
      p + off ≠ bsParentBase p bunCap + b2 →
      mem2 (p + off) = mem (p + off) := fun off hoff h1a h1b h1c h2a h2b h2c =>
    (h2_fr _ h2a h2b h2c fun k hk => hblk_not_pn off hoff k (hL2pre_lt k hk)).trans
      (h1_fr _ h1a h1b h1c fun k hk => hblk_not_pn off hoff k (hL1_lt k hk))
  have hends_erase : ∀ b x,
      x ∈ ({ B with edges := B.edges.erase e } : BundleState).ends b ↔
        x ∈ B.ends b ∧ x ≠ (e, true) ∧ x ≠ (e, false) := by
    intro b x; simp only [BundleState.mem_ends, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hne, hxE⟩, hbx⟩
      exact ⟨⟨hxE, hbx⟩, fun h => hne (by rw [h]), fun h => hne (by rw [h])⟩
    · rintro ⟨⟨hxE, hbx⟩, hnt, hnf⟩
      refine ⟨⟨fun heq => ?_, hxE⟩, hbx⟩
      rcases x with ⟨ee, side⟩; dsimp only at heq; subst heq
      cases side
      · exact hnf rfl
      · exact hnt rfl
  have hk_ne_2e : ∀ k, k ≠ 2 * e ↔ endOfKey k ≠ (e, true) := fun k => by
    constructor
    · intro hne heq; apply hne; have := congrArg endKey heq; rwa [bundle_endKey_endOfKey] at this
    · intro hne heq; apply hne; rw [heq]; exact bundle_endOfKey_endKey (e, true)
  have hk_ne_2e1 : ∀ k, k ≠ 2 * e + 1 ↔ endOfKey k ≠ (e, false) := fun k => by
    constructor
    · intro hne heq; apply hne; have := congrArg endKey heq; rwa [bundle_endKey_endOfKey] at this
    · intro hne heq; apply hne; rw [heq]; exact bundle_endOfKey_endKey (e, false)
  have hme : ∀ {b x}, x ∈ B.ends b → x.1 ∈ B.edges ∧ B.bundleOf x = b := fun h => by
    rwa [BundleState.mem_ends] at h
  have hmem_L2' : ∀ k, k ∈ L2pre.erase (2 * e + 1) ↔
      endOfKey k ∈ ({ B with edges := B.edges.erase e } : BundleState).ends b2 := fun k => by
    rw [hends_erase]; dsimp only [L2pre]; split_ifs with h21
    · have h1er : (L1.erase (2 * e)).Nodup := hL1_nd.erase (2 * e)
      rw [h1er.mem_erase_iff, hL1_nd.mem_erase_iff, hL1_mem, ← h21, hk_ne_2e, hk_ne_2e1]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h3, h2, h1⟩, fun ⟨h3, h2, h1⟩ => ⟨h1, h2, h3⟩⟩
    · rw [hL2_nd.mem_erase_iff, hL2_mem, hk_ne_2e1]
      refine ⟨fun ⟨hne1, hmem⟩ => ⟨hmem, fun ht => h21 (by
        have hbm := (hme hmem).2; rw [ht] at hbm; exact hbm.symm.trans hb1.symm), hne1⟩,
        fun ⟨hmem, _, hne1⟩ => ⟨hne1, hmem⟩⟩
  have hmem_L1' : b2 ≠ b1 → ∀ k, k ∈ L1.erase (2 * e) ↔
      endOfKey k ∈ ({ B with edges := B.edges.erase e } : BundleState).ends b1 := fun h21 k => by
    rw [hends_erase, hL1_nd.mem_erase_iff, hL1_mem, hk_ne_2e]
    refine ⟨fun ⟨hne0, hmem⟩ => ⟨hmem, hne0, fun hf => h21 (by
      have hbm := (hme hmem).2; rw [hf] at hbm; exact hb2.trans hbm)⟩,
      fun ⟨hmem, hne0, _⟩ => ⟨hne0, hmem⟩⟩
  have hpn_not_blk : ∀ k < 2 * eCap, ∀ b < bunCap,
      prevBase + k ≠ bsHeadBase p + b ∧ prevBase + k ≠ bsSizeBase p bunCap + b ∧
      prevBase + k ≠ bsParentBase p bunCap + b ∧
      nextBase + k ≠ bsHeadBase p + b ∧ nextBase + k ≠ bsSizeBase p bunCap + b ∧
      nextBase + k ≠ bsParentBase p bunCap + b := fun k hk b hb => by
    unfold bsHeadBase bsSizeBase bsParentBase
    refine ⟨by clear * - hblk_prev' hk hb; omega, by clear * - hblk_prev' hk hb; omega,
      by clear * - hblk_prev' hk hb; omega, by clear * - hblk_next' hk hb; omega,
      by clear * - hblk_next' hk hb; omega, by clear * - hblk_next' hk hb; omega⟩
  refine ⟨nB, hV, hnB, fun e' he' => hE e' (Finset.mem_of_mem_erase he'),
    fun x hx => hbo x ((mem_edgeEnds _ _).mpr (Finset.mem_of_mem_erase ((mem_edgeEnds _ _).mp hx))),
    hpar0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem3_blk bsOffBunCap (by unfold bsOffBunCap bundleSlotBlockSize; omega) (by decide),
      h21_eq bsOffBunCap (by unfold bsOffBunCap bundleSlotBlockSize; omega)
        (by unfold bsOffBunCap bsHeadBase; omega) (by unfold bsOffBunCap bsSizeBase; omega)
        (by unfold bsOffBunCap bsParentBase; omega) (by unfold bsOffBunCap bsHeadBase; omega)
        (by unfold bsOffBunCap bsSizeBase; omega) (by unfold bsOffBunCap bsParentBase; omega)]
    exact h0
  · rw [hmem3_blk bsOffNB (by unfold bsOffNB bundleSlotBlockSize; omega) (by decide),
      h21_eq bsOffNB (by unfold bsOffNB bundleSlotBlockSize; omega)
        (by unfold bsOffNB bsHeadBase; omega) (by unfold bsOffNB bsSizeBase; omega)
        (by unfold bsOffNB bsParentBase; omega) (by unfold bsOffNB bsHeadBase; omega)
        (by unfold bsOffNB bsSizeBase; omega) (by unfold bsOffNB bsParentBase; omega)]
    exact h1
  · rw [h3_nE, Finset.card_erase_of_mem heB]
  · intro b hb
    have hb_cap : b < bunCap := lt_of_lt_of_le hb hnB
    by_cases hbb2 : b = b2
    · subst b
      have hhd3 := hmem3_blk (3 + b2) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)
      refine ⟨L2pre.erase (2 * e + 1), h2_dll.of_agree
        (by simpa [bsHeadBase, Nat.add_assoc] using hhd3)
        (fun k hk => hmem3_prev k (h2_dll.2.1 k hk))
        (fun k hk => hmem3_next k (h2_dll.2.1 k hk)),
        ?_, hmem_L2'⟩
      have hsz3 := hmem3_blk (3 + bunCap + b2) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)
      simpa [bsSizeBase, Nat.add_assoc] using hsz3.trans (by simpa [bsSizeBase, Nat.add_assoc] using h2_sz)
    · by_cases hbb1 : b = b1
      · subst b
        have h2ne1 : b2 ≠ b1 := Ne.symm hbb2
        have hL2pre_eq : L2pre = L2 := by simp [L2pre, h2ne1]
        have h1_dll2 : IsDoublyLinkedList mem2 prevBase nextBase (bsHeadBase p + b1) (2 * eCap) (L1.erase (2 * e)) := by
          refine h1_dll.of_agree ?_ ?_ ?_
          · exact h2_fr (bsHeadBase p + b1) (by unfold bsHeadBase; omega)
              (by unfold bsHeadBase bsSizeBase; omega) (by unfold bsHeadBase bsParentBase; omega)
              fun k hk => by
                have := hblk_not_pn (3 + b1) (by unfold bundleSlotBlockSize; omega) k (hL2pre_lt k hk)
                simpa [bsHeadBase, Nat.add_assoc] using this
          · intro k hk
            have hk_lt : k < 2 * eCap := h1_dll.2.1 k hk
            have hnb := hpn_not_blk k hk_lt b2 (lt_of_lt_of_le hb2_lt hnB)
            exact h2_fr (prevBase + k) hnb.1 hnb.2.1 hnb.2.2.1 fun k' hk' => by
              rw [hL2pre_eq] at hk'
              have hk'_lt := hL2_lt k' hk'
              have hne_k : k ≠ k' := fun h => h2ne1 (by
                have h1m := (hme ((hL1_mem k).mp (List.mem_of_mem_erase hk))).2
                have h2m := (hme ((hL2_mem k').mp hk')).2
                rw [h] at h1m; exact h2m.symm.trans h1m)
              exact ⟨by omega, by clear * - hprev_next hk_lt hk'_lt; omega⟩
          · intro k hk
            have hk_lt : k < 2 * eCap := h1_dll.2.1 k hk
            have hnb := hpn_not_blk k hk_lt b2 (lt_of_lt_of_le hb2_lt hnB)
            exact h2_fr (nextBase + k) hnb.2.2.2.1 hnb.2.2.2.2.1 hnb.2.2.2.2.2 fun k' hk' => by
              rw [hL2pre_eq] at hk'
              have hk'_lt := hL2_lt k' hk'
              have hne_k : k ≠ k' := fun h => h2ne1 (by
                have h1m := (hme ((hL1_mem k).mp (List.mem_of_mem_erase hk))).2
                have h2m := (hme ((hL2_mem k').mp hk')).2
                rw [h] at h1m; exact h2m.symm.trans h1m)
              exact ⟨by clear * - hprev_next hk_lt hk'_lt; omega, by omega⟩
        have hhd3 := hmem3_blk (3 + b1) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)
        refine ⟨L1.erase (2 * e), h1_dll2.of_agree
          (by simpa [bsHeadBase, Nat.add_assoc] using hhd3)
          (fun k hk => hmem3_prev k (h1_dll2.2.1 k hk))
          (fun k hk => hmem3_next k (h1_dll2.2.1 k hk)),
          ?_, hmem_L1' h2ne1⟩
        have h1sz : mem2 (bsSizeBase p bunCap + b1) = mem1 (bsSizeBase p bunCap + b1) :=
          h2_fr (bsSizeBase p bunCap + b1) (by unfold bsSizeBase bsHeadBase; omega)
            (by unfold bsSizeBase; omega) (by unfold bsSizeBase bsParentBase; omega)
            fun k hk => by
              have := hblk_not_pn (3 + bunCap + b1) (by unfold bundleSlotBlockSize; omega) k (hL2pre_lt k hk)
              simpa [bsSizeBase, Nat.add_assoc] using this
        have hsz3 := hmem3_blk (3 + bunCap + b1) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)
        simpa [bsSizeBase, Nat.add_assoc] using hsz3.trans (by simpa [bsSizeBase, Nat.add_assoc] using h1sz.trans h1_sz)
      · obtain ⟨L, hL, hsz, hmemL⟩ := hdll b hb
        have hdisj_L1 : ∀ k ∈ L, ∀ k' ∈ L1, k ≠ k' := fun k hk k' hk' heq => hbb1 (by
          have h1m := (hme ((hmemL k).mp hk)).2
          have h2m := (hme ((hL1_mem k').mp hk')).2
          rw [heq] at h1m; exact h1m.symm.trans h2m)
        have hdisj_L2 : ∀ k ∈ L, ∀ k' ∈ L2pre, k ≠ k' := fun k hk k' hk' heq => by
          dsimp only [L2pre] at hk'; split_ifs at hk'
          · exact hdisj_L1 k hk k' (List.mem_of_mem_erase hk') heq
          · exact hbb2 (by
              have h1m := (hme ((hmemL k).mp hk)).2
              have h2m := (hme ((hL2_mem k').mp hk')).2
              rw [heq] at h1m; exact h1m.symm.trans h2m)
        have hL2 : IsDoublyLinkedList mem2 prevBase nextBase (bsHeadBase p + b) (2 * eCap) L := by
          refine hL.of_agree ?_ ?_ ?_
          · have h21h := h21_eq (3 + b) (by unfold bundleSlotBlockSize; omega)
              (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega) (by unfold bsParentBase; omega)
              (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega) (by unfold bsParentBase; omega)
            simpa [bsHeadBase, Nat.add_assoc] using h21h
          · intro k hk
            have hk_lt := hL.2.1 k hk
            have hnb1 := hpn_not_blk k hk_lt b1 (lt_of_lt_of_le hb1_lt hnB)
            have hnb2 := hpn_not_blk k hk_lt b2 (lt_of_lt_of_le hb2_lt hnB)
            exact (h2_fr (prevBase + k) hnb2.1 hnb2.2.1 hnb2.2.2.1 fun k' hk' =>
                ⟨by have := hdisj_L2 k hk k' hk'; omega,
                 by have := hL2pre_lt k' hk'; clear * - hprev_next hk_lt this; omega⟩).trans
              (h1_fr (prevBase + k) hnb1.1 hnb1.2.1 hnb1.2.2.1 fun k' hk' =>
                ⟨by have := hdisj_L1 k hk k' hk'; omega,
                 by have := hL1_lt k' hk'; clear * - hprev_next hk_lt this; omega⟩)
          · intro k hk
            have hk_lt := hL.2.1 k hk
            have hnb1 := hpn_not_blk k hk_lt b1 (lt_of_lt_of_le hb1_lt hnB)
            have hnb2 := hpn_not_blk k hk_lt b2 (lt_of_lt_of_le hb2_lt hnB)
            exact (h2_fr (nextBase + k) hnb2.2.2.2.1 hnb2.2.2.2.2.1 hnb2.2.2.2.2.2 fun k' hk' =>
                ⟨by have := hL2pre_lt k' hk'; clear * - hprev_next hk_lt this; omega,
                 by have := hdisj_L2 k hk k' hk'; omega⟩).trans
              (h1_fr (nextBase + k) hnb1.2.2.2.1 hnb1.2.2.2.2.1 hnb1.2.2.2.2.2 fun k' hk' =>
                ⟨by have := hL1_lt k' hk'; clear * - hprev_next hk_lt this; omega,
                 by have := hdisj_L1 k hk k' hk'; omega⟩)
        have hhd3 := hmem3_blk (3 + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)
        refine ⟨L, hL2.of_agree
          (by simpa [bsHeadBase, Nat.add_assoc] using hhd3)
          (fun k hk => hmem3_prev k (hL2.2.1 k hk))
          (fun k hk => hmem3_next k (hL2.2.1 k hk)),
          ?_, fun k => ?_⟩
        · have hsz3 := hmem3_blk (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)
          have hsz2 := h21_eq (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega)
            (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega) (by unfold bsParentBase; omega)
            (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega) (by unfold bsParentBase; omega)
          simpa [bsSizeBase, Nat.add_assoc] using hsz3.trans (hsz2.trans (by simpa [bsSizeBase, Nat.add_assoc] using hsz))
        · rw [hends_erase, hmemL k]
          refine ⟨fun h => ⟨h, fun ht => hbb1 (by have hbm := (hme h).2; rw [ht] at hbm; exact hbm.symm.trans hb1.symm),
            fun hf => hbb2 (by have hbm := (hme h).2; rw [hf] at hbm; exact hbm.symm.trans hb2.symm)⟩, fun h => h.1⟩
  · intro b hb hem
    have hb_cap : b < bunCap := lt_of_lt_of_le hb hnB
    have hm3 : mem3 (bsParentBase p bunCap + b) = mem2 (bsParentBase p bunCap + b) := by
      simpa [bsParentBase, Nat.add_assoc] using hmem3_blk (3 + 2 * bunCap + b)
        (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)
    rw [hm3]
    by_cases hbb2 : b = b2
    · subst b
      have hnil : L2pre.erase (2 * e + 1) = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro k hk
        have := (hmem_L2' k).mp hk; rw [hem] at this; exact Finset.notMem_empty _ this
      exact h2_par0 hnil
    · have hm2 : mem2 (bsParentBase p bunCap + b) = mem1 (bsParentBase p bunCap + b) :=
        h2_fr (bsParentBase p bunCap + b) (by unfold bsParentBase bsHeadBase; omega)
          (by unfold bsParentBase bsSizeBase; omega) (by unfold bsParentBase; omega)
          fun k hk => by
            have := hblk_not_pn (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega) k (hL2pre_lt k hk)
            simpa [bsParentBase, Nat.add_assoc] using this
      rw [hm2]
      by_cases hbb1 : b = b1
      · subst b
        have hnil : L1.erase (2 * e) = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro k hk
          have := (hmem_L1' (Ne.symm hbb2) k).mp hk; rw [hem] at this; exact Finset.notMem_empty _ this
        exact h1_par0 hnil
      · have hm1 : mem1 (bsParentBase p bunCap + b) = mem (bsParentBase p bunCap + b) :=
          h1_fr (bsParentBase p bunCap + b) (by unfold bsParentBase bsHeadBase; omega)
            (by unfold bsParentBase bsSizeBase; omega) (by unfold bsParentBase; omega)
            fun k hk => by
              have := hblk_not_pn (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega) k (hL1_lt k hk)
              simpa [bsParentBase, Nat.add_assoc] using this
        rw [hm1]
        apply hpar b hb
        ext x; simp only [Finset.notMem_empty, iff_false]
        intro hx
        have hx' : x ∈ ({ B with edges := B.edges.erase e } : BundleState).ends b :=
          (hends_erase b x).mpr ⟨hx,
            fun ht => hbb1 (by have hbm := (hme hx).2; rw [ht] at hbm; exact hbm.symm.trans hb1.symm),
            fun hf => hbb2 (by have hbm := (hme hx).2; rw [hf] at hbm; exact hbm.symm.trans hb2.symm)⟩
        rw [hem] at hx'; exact Finset.notMem_empty x hx'
  · intro b hge hlt
    have hneq1 : b ≠ b1 := by omega
    have hneq2 : b ≠ b2 := by omega
    obtain ⟨t1, t2, t3⟩ := htail b hge hlt
    refine ⟨?_, ?_, ?_⟩
    · simpa [bsHeadBase, Nat.add_assoc] using (hmem3_blk (3 + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)).trans
        ((h21_eq (3 + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega)).trans (by simpa [bsHeadBase, Nat.add_assoc] using t1))
    · simpa [bsSizeBase, Nat.add_assoc] using (hmem3_blk (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)).trans
        ((h21_eq (3 + bunCap + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega)).trans (by simpa [bsSizeBase, Nat.add_assoc] using t2))
    · simpa [bsParentBase, Nat.add_assoc] using (hmem3_blk (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)).trans
        ((h21_eq (3 + 2 * bunCap + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega)).trans (by simpa [bsParentBase, Nat.add_assoc] using t3))
  · intro b hb
    obtain ⟨s1, s2, s3⟩ := hscr b hb
    refine ⟨?_, ?_, ?_⟩
    · simpa [bsSeenBase, Nat.add_assoc] using (hmem3_blk (3 + 3 * bunCap + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)).trans
        ((h21_eq (3 + 3 * bunCap + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega)).trans (by simpa [bsSeenBase, Nat.add_assoc] using s1))
    · simpa [bsInCandBase, Nat.add_assoc] using (hmem3_blk (3 + 4 * bunCap + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)).trans
        ((h21_eq (3 + 4 * bunCap + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega)).trans (by simpa [bsInCandBase, Nat.add_assoc] using s2))
    · simpa [bsCandNextBase, Nat.add_assoc] using (hmem3_blk (3 + 5 * bunCap + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsOffNE; omega)).trans
        ((h21_eq (3 + 5 * bunCap + b) (by unfold bundleSlotBlockSize; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega) (by unfold bsHeadBase; omega) (by unfold bsSizeBase; omega)
          (by unfold bsParentBase; omega)).trans (by simpa [bsCandNextBase, Nat.add_assoc] using s3))

end

end MinCostFlow.SparseCore.Program
