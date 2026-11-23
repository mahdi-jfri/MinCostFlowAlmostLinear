module

public import MinCostFlow.SparseCore.Program.BunRestartPhaseA

/-!
# The restart of the bundles: phase B (`BunRestartPhaseB`)

Phase B walks the end list of every bundle of every listed slot (`outWalkBody`) and writes the
keys one after the other from `h + 6 n` on: the keys `allKeys` of the listed slots
(`brPhaseB_runs`). The walk of a slot `s` with `nB` bundles and `E_s` edges costs about
`60 E_s + 60 nB`; the bundles are paid by the potential of the table.

The proof has two loops: the walk of the bundles of one slot (`brInner_triple`) and the loop over
the slots.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

variable {w slotCap vCap eCap tbl tourH slotsPtr h : ℕ} {p : Program} {ω : ℕ → Bool}
  {S : Fin slotCap → Option BundleState} {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
  {slots : List ℕ} {bWalk : ℕ}

/-- **The walk of the bundles of one slot.** Before the inner loop of loop B for slot `s` (block
`p`, `nB` bundles), the keys `pre` of the earlier slots are at `h + 6 n` and register `20` holds
their number. The loop appends the keys of `s` and costs at most `60 |E_s| + 60 nB + 10`. -/
theorem brInner_triple (hpWalk : p.procs[bWalk]? = some outWalkBody)
    (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem)
    (hfoot : ∀ a, bundleTableFoot eCap tbl m a → a < h)
    {n E i h19 : ℕ} {M : ℕ → ℕ} (hlow : ∀ a < h, M a = mem a)
    (hw : 16 ≤ 2 ^ w) (hfit : h + 6 * n + 2 * E < 2 ^ w)
    {s : ℕ} (hs : s < slotCap) {B : BundleState} (hB : S ⟨s, hs⟩ = some B)
    (pre : List ℕ) (hpre : pre.length + 2 * B.edges.card ≤ 2 * E) :
    Triple w p
      (fun st => BRRegs st.regs tbl tourH n slotsPtr h slotCap eCap ∧ BRRegsL st.regs h n E ∧
        st.regs 19 = h19 ∧ st.regs 10 = i ∧ st.regs 12 = (slotBlk m s).1 ∧
        st.regs 21 = B.vertices.card ∧ st.regs 20 = pre.length ∧
        ListAt st.mem (h + 6 * n) pre ∧
        ∀ a, (a < h + 6 * n ∨ h + 6 * n + 2 * E ≤ a) → st.mem a = M a)
      (forRange 22 (.const 0) (.reg 21) (brBundleBody bWalk))
      (normalPost fun st => BRRegs st.regs tbl tourH n slotsPtr h slotCap eCap ∧
        BRRegsL st.regs h n E ∧ st.regs 19 = h19 ∧ st.regs 10 = i ∧
        st.regs 20 = (pre ++ bunKeys slotCap eCap tbl mem (slotBlk m s).1 B).length ∧
        ListAt st.mem (h + 6 * n) (pre ++ bunKeys slotCap eCap tbl mem (slotBlk m s).1 B) ∧
        ∀ a, (a < h + 6 * n ∨ h + 6 * n + 2 * E ≤ a) → st.mem a = M a)
      (fun _ => 60 * B.edges.card + 60 * B.vertices.card + 10) := by
  obtain ⟨hm, -, hslot, -⟩ := slot_facts hrep hs hB
  set pB := (slotBlk m s).1 with hpB
  set cB := (slotBlk m s).2 with hcB
  set nB := B.vertices.card with hnB
  set L : ℕ → List ℕ := bunList slotCap eCap tbl mem pB B with hLdef
  set prevB := btEndPrevBase tbl slotCap eCap
  set nextB := btEndNextBase tbl slotCap eCap
  have hlenK : (bunKeys slotCap eCap tbl mem pB B).length = 2 * B.edges.card :=
    bunKeys_length hslot
  have hnBc : nB ≤ cB := by
    obtain ⟨nB', hV, hle, -⟩ := hslot
    rw [hnB, hV, Finset.card_range]; exact hle
  have hpart : ∀ b ≤ nB, ((List.range b).flatMap L).length ≤ 2 * B.edges.card := by
    intro b hb
    rw [← hlenK]
    unfold bunKeys
    rw [← hnB, show nB = b + (nB - b) by omega, List.range_add, List.flatMap_append,
      List.length_append]
    exact Nat.le_add_right _ _
  have hnBw : nB < h := by
    rcases Nat.eq_zero_or_pos nB with h0 | hpos
    · have := hfoot _ (btHeader_in_foot (m := m) (tbl := tbl) (eCap := eCap) (off := 0)
        (by unfold btHdrSize; omega))
      omega
    · have := hfoot _ (bsAddr_in_foot (j := ⟨s, hs⟩) (p := pB) (bunCap := cB)
        (off := 3 + (nB - 1)) hm (by unfold bundleSlotBlockSize; omega))
      omega
  have hnext_tail : nextB + 2 * eCap < h := by
    have := hfoot _ (btSlotTouched_in_foot (m := m) (s := 0) (by omega))
    simp only [btSlotTouchedBase, nextB, btEndNextBase] at this ⊢
    omega
  let Inv : ℕ → State → Prop := fun b st =>
    BRRegs st.regs tbl tourH n slotsPtr h slotCap eCap ∧ BRRegsL st.regs h n E ∧
      st.regs 19 = h19 ∧ st.regs 10 = i ∧ st.regs 12 = pB ∧ st.regs 21 = nB ∧ st.regs 22 = b ∧
      st.regs 20 = (pre ++ (List.range b).flatMap L).length ∧
      ListAt st.mem (h + 6 * n) (pre ++ (List.range b).flatMap L) ∧
      ∀ a, (a < h + 6 * n ∨ h + 6 * n + 2 * E ≤ a) → st.mem a = M a
  refine Triple.conseq (Q := normalPost (Inv nB))
    (T := fun _ => rangeCost (fun b => 30 * (L b).length + 50) 0 nB +
      (nB - 0) * ((Expr.reg 21).size + 8) + ((Expr.const 0).size + (Expr.reg 21).size + 5))
    ?_ (fun _ h => h) ?_ ?_
  refine Triple.forRange_le (Inv := Inv) (fun b => 30 * (L b).length + 50) 0 nB
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Nat.zero_le _
  · omega
  · intro _; omega
  · intro st hP
    obtain ⟨hR, hL, h19', h10, h12, h21, h20, hlist, hfr⟩ := hP
    exact ⟨Expr.eval_const (by omega), hR.upd (by omega), hL.upd (by omega),
      by simp [h19'], by simp [h10], by simp [h12], by simp [h21], by simp,
      by simp [h20], by simpa using hlist, fun a ha => hfr a ha⟩
  · intro b st _ _ hI; exact hI.2.2.2.2.2.2.1
  · intro b st _ _ hI; simp [Expr.eval, hI.2.2.2.2.2.1]
  · intro b _ hb
    wram_enter
    obtain ⟨hR, hL, h19', h10, h12, h21, h22, h20, hlist, hfr⟩ := hpre
    have hR' := hR
    obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8⟩ := hR'
    have hL' := hL
    obtain ⟨hr9, hr13, hr14, hr15, hr16, hr17⟩ := hL'
    have hbV : b < B.vertices.card := hb
    obtain ⟨hdll, -⟩ := bunList_spec hslot hbV
    have hpartb := hpart (b + 1) (by omega)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append] at hpartb
    set k := (pre ++ (List.range b).flatMap L).length with hk
    have hklen : k + (L b).length ≤ 2 * E := by
      rw [hk, List.length_append]; omega
    have hhead : pB + 3 + b < h := by
      have := hfoot _ (bsAddr_in_foot (j := ⟨s, hs⟩) (p := pB) (bunCap := cB) (off := 3 + b) hm
        (by unfold bundleSlotBlockSize; omega))
      omega
    have hkeys : ∀ x ∈ L b, x < 2 * eCap := hdll.2.1
    have hdll' : IsDoublyLinkedList st.mem prevB nextB (pB + 3 + b) (2 * eCap) (L b) := by
      refine hdll.of_agree ?_ (fun x hx => ?_) (fun x hx => ?_)
      · show st.mem (pB + 3 + b) = mem (pB + 3 + b)
        rw [hfr _ (Or.inl (by omega)), hlow _ hhead]
      · have hlt := hfoot _ (btEndPrev_in_foot (m := m) (slotCap := slotCap) (hkeys x hx))
        rw [hfr _ (Or.inl (by omega)), hlow _ hlt]
      · have hlt := hfoot _ (btEndNext_in_foot (m := m) (slotCap := slotCap) (hkeys x hx))
        rw [hfr _ (Or.inl (by omega)), hlow _ hlt]
    have hwalk := brWalk_meetsContract (w := w) (prevB := prevB) (nb := nextB)
      (head := pB + 3 + b) (dst := h + 6 * n + k) (cap := 2 * eCap) (L := L b) hpWalk
    unfold brBundleBody
    refine runs_seq_call_le hwalk (vs := [nextB, pB + 3 + b, h + 6 * n + k]) (by eval_expr)
      (by wram_words) ⟨rfl, hdll', fun x hx => by have := hkeys x hx; omega, by omega,
        by omega, fun j _ => by omega, fun x hx j _ => by have := hkeys x hx; omega⟩
      (fun v mem' pos' hpost => ?_)
    obtain ⟨rfl, hlistL, hfrL⟩ := hpost
    wram_step
    · simp only [normalPost_normal]
      refine ⟨⟨((hR.upd (by omega)).upd (by omega)).upd (by omega),
        ((hL.upd (by omega)).upd (by omega)).upd (by omega), by simp [h19'], by simp [h10],
        by simp [h12], by simp [h21], by simp, ?_, ?_, ?_⟩, by simp [h22]⟩
      · simp [h20, hk, List.range_succ, List.flatMap_append]
        omega
      · simp only
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc]
        refine listAt_append' (listAt_congr' hlist fun j hj => ?_) ?_
        · exact hfrL _ fun ⟨h1, _⟩ => by rw [hk] at h1; omega
        · rw [← hk]; exact hlistL
      · intro a ha
        exact (hfrL a (by omega)).trans (hfr a ha)
    · simp only [brWalkContract]
      wram_cost
  · intro o st' hq
    cases o with
    | returned v => exact hq.elim
    | normal =>
      obtain ⟨hR, hL, h19', h10, -, -, -, h20, hlist, hfr⟩ := hq
      have hK : (List.range nB).flatMap L = bunKeys slotCap eCap tbl mem pB B := rfl
      rw [hK] at h20 hlist
      exact ⟨hR, hL, h19', h10, h20, hlist, hfr⟩
  · intro _ _
    rw [rangeCost_zero_eq_range]
    have hsum : ((List.range nB).map fun b => 30 * (L b).length + 50).sum =
        30 * (bunKeys slotCap eCap tbl mem pB B).length + 50 * nB := by
      unfold bunKeys
      rw [← hnB, List.length_flatMap, List.sum_map_add, List.sum_map_mul_left]
      simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
      rw [Nat.mul_comm nB 50]
    rw [hsum, hlenK]
    simp only [Expr.size_reg, Expr.size_const, Nat.sub_zero]
    omega

/-- **Phase B.** From the end of phase A, phase B writes the keys `allKeys` of the listed slots
at `h + 6 n`, keeps the registers, and writes nothing outside the `2 E` words of the keys. It costs
at most `60 E + 60 nB + 50 n + 10`, where `nB` is the number of bundles of the listed slots. -/
theorem brPhaseB_runs (hpWalk : p.procs[bWalk]? = some outWalkBody)
    (hrep : BundleTableRepAt slotCap vCap eCap tbl S m mem)
    (hfoot : ∀ a, bundleTableFoot eCap tbl m a → a < h)
    (hact : ∀ s ∈ slots, ∃ hs : s < slotCap, ∃ B, S ⟨s, hs⟩ = some B)
    (hw : 16 ≤ 2 ^ w)
    (hfit : h + 6 * slots.length + 10 * edgeTot S slots < 2 ^ w)
    {st : State} (hR : BRRegs st.regs tbl tourH slots.length slotsPtr h slotCap eCap)
    (hL : BRRegsL st.regs h slots.length (edgeTot S slots)) (h20 : st.regs 20 = 0)
    (hspec : ∀ i (hi : i < slots.length), st.mem (h + 4 * slots.length + 2 * i) = slots[i])
    (hlow : ∀ a < h, st.mem a = mem a) :
    ∃ st' c, Runs w p ω (brPhaseB bWalk) st .normal st' c ∧
      BRRegs st'.regs tbl tourH slots.length slotsPtr h slotCap eCap ∧
      BRRegsL st'.regs h slots.length (edgeTot S slots) ∧ st'.regs 19 = st.regs 19 ∧
      ListAt st'.mem (h + 6 * slots.length) (allKeys eCap tbl S m mem slots) ∧
      (∀ a, (a < h + 6 * slots.length ∨ h + 6 * slots.length + 2 * edgeTot S slots ≤ a) →
        st'.mem a = st.mem a) ∧
      c ≤ 60 * edgeTot S slots + 60 * (slots.map fun s => (slotB S s).vertices.card).sum +
        50 * slots.length + 10 := by
  set n := slots.length with hn
  set E := edgeTot S slots with hE
  set M := st.mem with hM
  set h19 := st.regs 19 with hh19
  let pre : ℕ → List ℕ := fun i => (slots.take i).flatMap (slotKeys eCap tbl S m mem)
  have hallLen : (allKeys eCap tbl S m mem slots).length = 2 * E := allKeys_length hrep hact
  let Inv : ℕ → State → Prop := fun i st =>
    BRRegs st.regs tbl tourH n slotsPtr h slotCap eCap ∧ BRRegsL st.regs h n E ∧
      st.regs 19 = h19 ∧ st.regs 10 = i ∧ st.regs 20 = (pre i).length ∧
      ListAt st.mem (h + 6 * n) (pre i) ∧
      ∀ a, (a < h + 6 * n ∨ h + 6 * n + 2 * E ≤ a) → st.mem a = M a
  let stepCost : ℕ → ℕ := fun i => 60 * (slotB S (slots.getD i 0)).edges.card +
    60 * (slotB S (slots.getD i 0)).vertices.card + 40
  have hbody : ∀ i, 0 ≤ i → i < n →
      Triple w p (Inv i) (brLoopBBody bWalk)
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 10 (i + 1) } ∧
            st₁.regs 10 = i)
        (fun _ => stepCost i) := by
    intro i _ hi
    wram_enter
    obtain ⟨hR, hL, h19', h10, h20, hlist, hfr⟩ := hpre
    have hR' := hR
    obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8⟩ := hR'
    have hsi : slots[i] ∈ slots := List.getElem_mem hi
    obtain ⟨hs, B, hB⟩ := hact _ hsi
    obtain ⟨hp, hpb, -, -⟩ := slot_reads hrep hfoot hs hB
    obtain ⟨hm, -, hslot, -⟩ := slot_facts hrep hs hB
    set pB := (slotBlk m slots[i]).1 with hpB
    have hnB1 : pB + 1 < h := by
      have := hfoot _ (bsAddr_in_foot (j := ⟨slots[i], hs⟩) (p := pB)
        (bunCap := (slotBlk m slots[i]).2) (off := 1) hm (by unfold bundleSlotBlockSize; omega))
      omega
    have hmS : st.mem (h + 4 * n + 2 * i) = slots[i] := by
      rw [hfr _ (Or.inl (by omega))]; exact hspec i hi
    have hm2 : st.mem (btSlotPtrBase tbl + slots[i]) = pB := by
      rw [hfr _ (Or.inl (by omega)), hlow _ hpb]; exact hp
    have hmNB : st.mem (pB + 1) = B.vertices.card := by
      rw [hfr _ (Or.inl (by omega)), hlow _ hnB1]
      obtain ⟨nB, hV, -, -, -, -, -, h1, -⟩ := hslot
      rw [hV, Finset.card_range]; exact h1
    have hsk : slotKeys eCap tbl S m mem slots[i] = bunKeys slotCap eCap tbl mem pB B := by
      unfold slotKeys; rw [slotB_eq hs hB]
    have hpre_s : pre (i + 1) = pre i ++ bunKeys slotCap eCap tbl mem pB B := by
      show (slots.take (i + 1)).flatMap (slotKeys eCap tbl S m mem) =
        (slots.take i).flatMap (slotKeys eCap tbl S m mem) ++ _
      rw [length_flatMap_take_succ hi, hsk]
    have hpre_len : (pre i).length + 2 * B.edges.card ≤ 2 * E := by
      have h1 := length_flatMap_take_le slots (slotKeys eCap tbl S m mem) (i + 1)
      have h2 : (pre (i + 1)).length = (pre i).length + 2 * B.edges.card := by
        rw [hpre_s, List.length_append, bunKeys_length hslot]
      have h3 : (slots.flatMap (slotKeys eCap tbl S m mem)).length = 2 * E := hallLen
      have h4 : (pre (i + 1)).length ≤ (slots.flatMap (slotKeys eCap tbl S m mem)).length := h1
      omega
    have hinner := brInner_triple (p := p) (bWalk := bWalk) (tourH := tourH)
      (slotsPtr := slotsPtr) (n := n) (E := E) (i := i) (h19 := h19) (M := M) hpWalk hrep hfoot
      (fun a ha => by rw [hM]; exact hlow a ha) hw (by omega) hs hB (pre i) hpre_len
    unfold brLoopBBody
    wram_step; simp only [hmS]
    wram_step; simp only [hr5, hm2]
    wram_step; simp only [hmNB]
    refine runs_triple_le hinner ⟨((hR.upd (by omega)).upd (by omega)).upd (by omega),
      ((hL.upd (by omega)).upd (by omega)).upd (by omega), by simp [h19'], by simp [h10],
      by simp [hpB], by simp, by simp [h20], hlist, hfr⟩ (fun o st' hq => ?_) ?_
    · cases o with
      | returned v => exact hq.elim
      | normal =>
        obtain ⟨hR₁, hL₁, h19₁, h10₁, h20₁, hlist₁, hfr₁⟩ := hq
        simp only [normalPost_normal]
        refine ⟨⟨hR₁.upd (by omega), hL₁.upd (by omega), by simp [h19₁], by simp, ?_, ?_, hfr₁⟩,
          h10₁⟩
        · simp only [Function.update_of_ne (show (20 : ℕ) ≠ 10 by omega)]
          rw [hpre_s]; exact h20₁
        · rw [hpre_s]; exact hlist₁
    · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, stepCost,
        List.getD_eq_getElem _ _ hi, slotB_eq hs hB]
      omega
  obtain ⟨o, st', c, hr, hq, hc⟩ := (Triple.forRange_le (w := w) (p := p)
    (P := fun st' => st' = st) (r := 10) (lo := .const 0) (hi := .reg 2)
    (body := brLoopBBody bWalk) (Inv := Inv) stepCost 0 n (Nat.zero_le _) (by omega)
    (fun _ => by omega)
    (fun st' hst' => by
      subst hst'
      exact ⟨Expr.eval_const (by omega), hR.upd (by omega), hL.upd (by omega), by simp [hh19],
        by simp, by simp [h20, pre], fun i hi => absurd hi (by simp [pre]), fun a _ => rfl⟩)
    (fun i st _ _ hI => hI.2.2.2.1)
    (fun i st _ _ hI => by simp [Expr.eval, hI.1.r2]) hbody) st ω rfl
  cases o with
  | returned v => exact hq.elim
  | normal =>
    obtain ⟨hR', hL', h19', -, -, hlist', hfr'⟩ := hq
    have hpreN : pre n = allKeys eCap tbl S m mem slots := by
      show (slots.take n).flatMap _ = _
      rw [hn, List.take_length]; rfl
    refine ⟨st', c, hr, hR', hL', h19', hpreN ▸ hlist', hfr', ?_⟩
    have hsum : rangeCost stepCost 0 n = 60 * E + 60 * (slots.map fun s =>
        (slotB S s).vertices.card).sum + 40 * n := by
      rw [rangeCost_zero_eq_range]
      simp only [stepCost, List.sum_map_add, List.sum_map_mul_left, List.map_const',
        List.length_range, List.sum_replicate, smul_eq_mul]
      rw [hn, brSum_range_getD slots (fun s => (slotB S s).edges.card),
        brSum_range_getD slots (fun s => (slotB S s).vertices.card)]
      simp only [hE, edgeTot]
      ring
    simp only [hsum, Expr.size_reg, Expr.size_const, Nat.sub_zero] at hc
    omega

end

end MinCostFlow.SparseCore.Program.Restart
