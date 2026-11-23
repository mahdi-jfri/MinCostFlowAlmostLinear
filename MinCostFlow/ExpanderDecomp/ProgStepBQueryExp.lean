module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBLayout

import Mathlib.Tactic.Linarith

/-!
# Step B Per-Block Post-Call Expander Branch (`ProgStepBQueryExp`)

Verifies the `.expander S` branch of `sbQueryAfterCallStmt`: saves `S` and `B \ S` into
persistent storage via `sbSaveExpStmt`, deactivates block `j`, and advances `SbQueryInv`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

lemma filterMap_range_congr {α : Type*} {j : ℕ} {f g : ℕ → Option α}
    (h : ∀ i < j, f i = g i) :
    (List.range j).filterMap f = (List.range j).filterMap g := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.filterMap_append, List.filterMap_append,
      ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), List.filterMap_cons, List.filterMap_cons,
      List.filterMap_nil, List.filterMap_nil, h j (Nat.lt_succ_self j)]

private lemma sbQueryAfterExp_run {w n b nBlocks k h0 L locA xA subOutA j : ℕ}
    {p : Program} {B_l S_l : List ℕ} {B_j S : Finset ℕ} {st st1 : State} {ω : ℕ → Bool}
    (hB_len : B_l.length = b) (hB_lt : B_l.Pairwise (· < ·)) (hB_fin : B_l.toFinset = B_j)
    (hB_sub : ∀ u ∈ B_l, u < n) (hB_at1 : ListAt st1.mem (xA + j * b) B_l)
    (hB_card : b = B_j.card)
    (htag1 : st1.mem subOutA = 1) (hS_fin : S_l.toFinset = S) (hS_sub : S ⊆ B_j)
    (hS_card : S_l.length = S.card) (hS_le : S_l.length ≤ b)
    (hS_len_mem : st1.mem (subOutA + 1) = S_l.length) (hS_at1 : ListAt st1.mem (subOutA + 2) S_l)
    (hloc1 : ∀ u < n, st1.mem (locA + u) = 0)
    (hj_lt : j < nBlocks) (hnb_b : nBlocks * b ≤ k) (hjb_le : j * b + b ≤ nBlocks * b)
    (hx_le : xA + k ≤ h0) (hloc_le : locA + n ≤ h0) (hd_loc_x : DisjointRange locA n xA k)
    (hsub_ge : (sbPersist h0 k b nBlocks L).hPersist ≤ subOutA)
    (hsubOut_w : subOutA + 2 + b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr4 : st1.regs 4 = b) (hr5 : st1.regs 5 = nBlocks) (hr8 : st1.regs 8 = locA)
    (hr17 : st1.regs 17 = (sbPersist h0 k b nBlocks L).actA)
    (hr18 : st1.regs 18 = (sbPersist h0 k b nBlocks L).savA)
    (hr19 : st1.regs 19 = (sbPersist h0 k b nBlocks L).cmpA)
    (hr27 : st1.regs 27 = j)
    (hregs1_lt : ∀ r < 28, r ≠ 12 → st1.regs r = st.regs r)
    (hr28 : st1.regs 28 = xA + j * b) (hr30 : st1.regs 30 = subOutA) :
    let ps := sbPersist h0 k b nBlocks L
    ∃ o st' cost,
      Runs w p ω sbQueryAfterCallStmt st1 o st' cost ∧
      (normalPost fun st' =>
        (∀ r < 28, r ≠ 12 → st'.regs r = st.regs r) ∧
        st'.regs 12 = st1.regs 12 ∧
        (∀ u < n, st'.mem (locA + u) = 0) ∧
        (∀ a, (a < locA ∨ locA + n ≤ a) →
          (a < ps.savA + j * b ∨ ps.savA + j * b + b ≤ a) →
          (a < ps.cmpA + j * b ∨ ps.cmpA + j * b + b ≤ a) →
          a ≠ ps.savLenA + j → a ≠ ps.cmpLenA + j → a ≠ ps.actA + j →
          st'.mem a = st1.mem a) ∧
        st'.mem (ps.savLenA + j) = S.card ∧
        st'.mem (ps.cmpLenA + j) = (B_j \ S).card ∧
        st'.mem (ps.actA + j) = 0 ∧
        ListAt st'.mem (ps.savA + j * b) (S.sort (· ≤ ·)) ∧
        ListAt st'.mem (ps.cmpA + j * b) ((B_j \ S).sort (· ≤ ·))) o st' ∧
      cost ≤ 96 * b + 200 := by
  intro ps
  have hsub_ge' : ps.hPersist ≤ subOutA := hsub_ge
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by dsimp only [ps, sbPersist]; omega
  have hSav_w : ps.savA + j * b + b < 2 ^ w := by omega
  have hCmp_w : ps.cmpA + j * b + b < 2 ^ w := by omega
  have hX_blk1 : b = B_j.card := hB_card
  refine runs_start_le ?_
  dsimp only [sbQueryAfterCallStmt, seqStmts]
  refine runs_seq_assign_le (v := S_l.length)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr30) (Expr.eval_const (by omega)) (by omega))
      (by rw [hS_len_mem])) ?_
  refine runs_cond_le (v := 1)
    (Expr.eval_eq_true
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr30]))
        htag1)
      (Expr.eval_const (by omega)) rfl (by omega))
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine runs_seq_assign_le (v := subOutA + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr30]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := ps.savA + j * b)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr18]))
      (Expr.eval_mul (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr27]))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr4])) (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := ps.cmpA + j * b)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr19]))
      (Expr.eval_mul (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr27]))
        (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr4])) (by omega)) (by omega)) ?_
  let st2 : State :=
    { mem := st1.mem,
      regs := Function.update (Function.update (Function.update (Function.update st1.regs
        31 S_l.length) 30 (subOutA + 2)) 32 (ps.savA + j * b)) 33 (ps.cmpA + j * b),
      pos := st1.pos }
  have hst2_lt30 : ∀ r < 30, st2.regs r = st1.regs r := fun r hr => by
    dsimp only [st2]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine runs_seq_triple_le
    (sbSaveExp_triple (w := w) (n := n) (b := b) (blkA := xA + j * b)
      (sA := subOutA + 2) (sLen := S_l.length) (locA := locA)
      (savDst := ps.savA + j * b) (cmpDst := ps.cmpA + j * b) (p := p) (mem := st1.mem)
      (B_l := B_l) (S_l := S_l) (S := S) (st₀ := st2)
      hB_len hB_lt hB_sub hB_at1 rfl hS_le hS_fin (hB_fin.symm ▸ hS_sub) hS_at1 hloc1
      (by rcases hd_loc_x with h | h <;> [left; right] <;> omega)
      (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (by omega) (by omega) (by omega) hSav_w hCmp_w hw16
      ((hst2_lt30 4 (by decide)).trans hr4)
      ((hst2_lt30 8 (by decide)).trans hr8)
      ((hst2_lt30 28 (by decide)).trans hr28)
      (by dsimp only [st2]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st2]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st2]; rw [Function.update_of_ne (by decide), Function.update_self])
      (by dsimp only [st2]; rw [Function.update_self]) rfl) rfl ?_
  intro st3 ⟨h34, h35, hoth3, _, hloc3, hfr3, hsav3, hcmp3⟩
  have hst3_lt30 : ∀ r < 30, st3.regs r = st1.regs r := fun r hr =>
    (hoth3 r (by omega)).trans (hst2_lt30 r hr)
  have h34' : st3.regs 34 = S.card := h34
  have h35' : st3.regs 35 = (B_j \ S).card := by rwa [hB_fin] at h35
  have hSavLen_eq : ps.actA + nBlocks + j = ps.savLenA + j := by omega
  have hCmpLen_eq : ps.actA + 2 * nBlocks + j = ps.cmpLenA + j := by omega
  refine runs_seq_store_le (x := ps.savLenA + j) (v := S.card)
    (hSavLen_eq ▸ Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq ((hst3_lt30 17 (by decide)).trans hr17))
      (Expr.eval_reg_of_eq ((hst3_lt30 5 (by decide)).trans hr5)) (by omega))
      (Expr.eval_reg_of_eq ((hst3_lt30 27 (by decide)).trans (hr27))) (by omega))
    (Expr.eval_reg_of_eq h34') ?_
  refine runs_seq_store_le (x := ps.cmpLenA + j) (v := (B_j \ S).card)
    (hCmpLen_eq ▸ Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq ((hst3_lt30 17 (by decide)).trans hr17))
      (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq ((hst3_lt30 5 (by decide)).trans hr5)) (by omega)) (by omega))
      (Expr.eval_reg_of_eq ((hst3_lt30 27 (by decide)).trans (hr27))) (by omega))
    (Expr.eval_reg_of_eq h35') ?_
  refine runs_store_le (x := ps.actA + j) (v := 0)
    (Expr.eval_add (Expr.eval_reg_of_eq ((hst3_lt30 17 (by decide)).trans hr17))
      (Expr.eval_reg_of_eq ((hst3_lt30 27 (by decide)).trans (hr27))) (by omega))
    (Expr.eval_const (by omega)) ?_ (by simp only [Expr.size]; omega)
  refine ⟨fun r hr hne => (hst3_lt30 r (by omega)).trans (hregs1_lt r hr hne),
    hst3_lt30 12 (by decide),
    fun u hu => by
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hloc3 u hu],
    fun a h1 h2 h3 h4 h5 h6 => by
      dsimp only
      rw [Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4, hfr3 a h1 h2 h3],
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self],
    by dsimp only; rw [Function.update_self],
    fun idx hidx => by
      have hlen : (S.sort (· ≤ ·)).length ≤ b := by rw [Finset.length_sort, ← hS_card]; exact hS_le
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact hsav3 idx hidx,
    fun idx hidx => by
      have hlen : ((B_j \ S).sort (· ≤ ·)).length ≤ b := by
        rw [Finset.length_sort]; exact (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq hX_blk1.symm)
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      have := hcmp3 idx (by rwa [hB_fin])
      simpa only [hB_fin] using this⟩

private lemma sbQueryAfterExp_other_eq {h0 k b nBlocks L locA n subOutA h12 i j : ℕ}
    {mem1 mem2 mem3 : ℕ → ℕ}
    (hloc_le : locA + n ≤ h0) (hsub_ge : (sbPersist h0 k b nBlocks L).hPersist ≤ subOutA)
    (hge : subOutA + 2 + b ≤ h12) (hi : i < nBlocks) (hj : j < nBlocks) (hij : i ≠ j)
    (hfr' : let ps := sbPersist h0 k b nBlocks L
      ∀ a, (a < locA ∨ locA + n ≤ a) →
        (a < ps.savA + j * b ∨ ps.savA + j * b + b ≤ a) →
        (a < ps.cmpA + j * b ∨ ps.cmpA + j * b + b ≤ a) →
        a ≠ ps.savLenA + j → a ≠ ps.cmpLenA + j → a ≠ ps.actA + j → mem3 a = mem2 a)
    (hfr1 : let ps := sbPersist h0 k b nBlocks L
      ∀ a < h12, (a < ps.wRelA ∨ ps.hPersist ≤ a) → (a < subOutA ∨ subOutA + 2 + b ≤ a) →
        mem2 a = mem1 a) :
    let ps := sbPersist h0 k b nBlocks L
    mem3 (ps.actA + i) = mem1 (ps.actA + i) ∧
    mem3 (ps.savLenA + i) = mem1 (ps.savLenA + i) ∧
    mem3 (ps.cmpLenA + i) = mem1 (ps.cmpLenA + i) ∧
    (∀ m < b, mem3 (ps.savA + i * b + m) = mem1 (ps.savA + i * b + m)) ∧
    (∀ m < b, mem3 (ps.cmpA + i * b + m) = mem1 (ps.cmpA + i * b + m)) := by
  intro ps
  have hps_id : sbPersist h0 k b nBlocks L = ps := rfl
  rw [hps_id] at hfr' hfr1
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA ≤ ps.wRelA ∧ ps.wRelA ≤ ps.hPersist := by dsimp only [ps, sbPersist]; omega
  have hib : i * b + b ≤ nBlocks * b := by
    have : (i + 1) * b ≤ nBlocks * b := Nat.mul_le_mul_right b (by omega); linarith
  have hjb : j * b + b ≤ nBlocks * b := by
    have : (j + 1) * b ≤ nBlocks * b := Nat.mul_le_mul_right b (by omega); linarith
  have hsub_ge' : ps.hPersist ≤ subOutA := hsub_ge
  have hstep : ∀ a, ps.actA ≤ a → a < ps.wBaseA →
      (a < ps.savA + j * b ∨ ps.savA + j * b + b ≤ a) →
      (a < ps.cmpA + j * b ∨ ps.cmpA + j * b + b ≤ a) →
      a ≠ ps.savLenA + j → a ≠ ps.cmpLenA + j → a ≠ ps.actA + j → mem3 a = mem1 a :=
    fun a h1 h2 h3 h4 h5 h6 h7 =>
      (hfr' a (Or.inr (by omega)) h3 h4 h5 h6 h7).trans
        (hfr1 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
  refine ⟨hstep _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega) (by omega),
    hstep _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega) (by omega),
    hstep _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega) (by omega),
    fun m hm => ?_, fun m hm => ?_⟩
  · have hne : ps.savA + i * b + m < ps.savA + j * b ∨ ps.savA + j * b + b ≤ ps.savA + i * b + m := by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · left; have : (i + 1) * b ≤ j * b := Nat.mul_le_mul_right b (by omega); linarith
      · right; have : (j + 1) * b ≤ i * b := Nat.mul_le_mul_right b (by omega); linarith
    exact hstep _ (by omega) (by omega) hne (Or.inl (by omega)) (by omega) (by omega) (by omega)
  · have hne : ps.cmpA + i * b + m < ps.cmpA + j * b ∨ ps.cmpA + j * b + b ≤ ps.cmpA + i * b + m := by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · left; have : (i + 1) * b ≤ j * b := Nat.mul_le_mul_right b (by omega); linarith
      · right; have : (j + 1) * b ≤ i * b := Nat.mul_le_mul_right b (by omega); linarith
    exact hstep _ (by omega) (by omega) (Or.inr (by omega)) hne (by omega) (by omega) (by omega)

private lemma sbQuery_recs_at_frame {h0 k b nBlocks L cutRecsA pairsA tmpA idx : ℕ}
    {mem1 mem2 : ℕ → ℕ} {cutIds : List ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {cPrimeAddrs compAddrs : List ℕ} {cPrimeLists compLists : List (List ℕ)}
    (hlens : cPrimeAddrs.length = cutIds.length ∧ compAddrs.length = cutIds.length ∧
      cPrimeLists.length = cutIds.length ∧ compLists.length = cutIds.length ∧
      pairs.length = cutIds.length)
    (hidx : idx < cutIds.length) (hidx_lt : idx < nBlocks)
    (hb_even : Even b) (hpairs_eq : pairsA = cutRecsA + 3 * nBlocks)
    (htmp_eq : tmpA = pairsA + 1 + nBlocks * (2 + b))
    (h1 : ∀ a, cutRecsA ≤ a → a < tmpA → mem2 a = mem1 a)
    (hrec :
      let cA := cPrimeAddrs[idx]'(hlens.1.symm ▸ hidx)
      let oA := compAddrs[idx]'(hlens.2.1.symm ▸ hidx)
      let cL := cPrimeLists[idx]'(hlens.2.2.1.symm ▸ hidx)
      let oL := compLists[idx]'(hlens.2.2.2.1.symm ▸ hidx)
      let p_i := pairs[idx]'(hlens.2.2.2.2.symm ▸ hidx)
      cA = pairsA + 1 + idx * (2 + b) + 1 ∧
      oA = pairsA + 1 + idx * (2 + b) + 2 + b / 2 ∧
      mem1 (cutRecsA + 3 * idx) =
        (sbPersist h0 k b nBlocks L).wBaseA + cutIds[idx]'hidx * (sbPersist h0 k b nBlocks L).wStride ∧
      mem1 (cutRecsA + 3 * idx + 1) = cA ∧
      mem1 (cutRecsA + 3 * idx + 2) = oA ∧
      mem1 (pairsA + 1 + idx * (2 + b)) = b / 2 ∧
      mem1 (pairsA + 1 + idx * (2 + b) + 1 + b / 2) = b / 2 ∧
      cL = p_i.1.sort (· ≤ ·) ∧ oL = p_i.2.sort (· ≤ ·) ∧
      cL.length = b / 2 ∧ oL.length = b / 2 ∧
      ListAt mem1 cA cL ∧ ListAt mem1 oA oL) :
    let cA := cPrimeAddrs[idx]'(hlens.1.symm ▸ hidx)
    let oA := compAddrs[idx]'(hlens.2.1.symm ▸ hidx)
    let cL := cPrimeLists[idx]'(hlens.2.2.1.symm ▸ hidx)
    let oL := compLists[idx]'(hlens.2.2.2.1.symm ▸ hidx)
    let p_i := pairs[idx]'(hlens.2.2.2.2.symm ▸ hidx)
    cA = pairsA + 1 + idx * (2 + b) + 1 ∧
    oA = pairsA + 1 + idx * (2 + b) + 2 + b / 2 ∧
    mem2 (cutRecsA + 3 * idx) =
      (sbPersist h0 k b nBlocks L).wBaseA + cutIds[idx]'hidx * (sbPersist h0 k b nBlocks L).wStride ∧
    mem2 (cutRecsA + 3 * idx + 1) = cA ∧
    mem2 (cutRecsA + 3 * idx + 2) = oA ∧
    mem2 (pairsA + 1 + idx * (2 + b)) = b / 2 ∧
    mem2 (pairsA + 1 + idx * (2 + b) + 1 + b / 2) = b / 2 ∧
    cL = p_i.1.sort (· ≤ ·) ∧ oL = p_i.2.sort (· ≤ ·) ∧
    cL.length = b / 2 ∧ oL.length = b / 2 ∧
    ListAt mem2 cA cL ∧ ListAt mem2 oA oL := by
  dsimp only at hrec ⊢
  rcases hrec with ⟨hcA, hoA, hr0, hr1, hr2, hp0, hp1, hcL, hoL, hcLen, hoLen, hLatC, hLatO⟩
  have h2half : 2 * (b / 2) = b := by rcases hb_even with ⟨m, hm⟩; omega
  have hidx_mul : (idx + 1) * (2 + b) ≤ nBlocks * (2 + b) := Nat.mul_le_mul_right (2 + b) (by omega)
  rw [Nat.succ_mul] at hidx_mul
  refine ⟨hcA, hoA,
    (h1 _ (by omega) (by omega)).trans hr0,
    (h1 _ (by omega) (by omega)).trans hr1,
    (h1 _ (by omega) (by omega)).trans hr2,
    (h1 _ (by omega) (by omega)).trans hp0,
    (h1 _ (by omega) (by omega)).trans hp1,
    hcL, hoL, hcLen, hoLen,
    fun m hm => (h1 _ (by omega) (by omega)).trans (hLatC m hm),
    fun m hm => (h1 _ (by omega) (by omega)).trans (hLatO m hm)⟩

theorem sbQueryOneBlock_afterExp {cfg : ParamConfig} {M r q w Sprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA tmpA hSub0 j : ℕ}
    {p : Program} {memStart : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState}
    {res : ℕ → CoreResult} {S : Finset ℕ}
    {cutIds : List ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {cPrimeAddrs compAddrs : List ℕ} {cPrimeLists compLists : List (List ℕ)}
    {st st1 : State} {ω : ℕ → Bool}
    (hX_at : VertsAt memStart xA k X) (hX_sub : X ⊆ Finset.range G.n)
    (hb_even : Even b) (hnb_eq : nBlocks = numFullBlocks (X.sort (· ≤ ·)) b)
    (hcur_lay : (sbPersist h0 k b nBlocks (LParam M)).hPersist ≤ cutRecsA ∧
      pairsA = cutRecsA + 3 * nBlocks ∧
      tmpA = pairsA + 1 + nBlocks * (2 + b) ∧
      hSub0 = tmpA + 4 * b + 2 + b ∧
      xA + k ≤ h0 ∧ pA + coreParamsSize r ≤ h0 ∧ locA + G.n ≤ h0 ∧
      DisjointRange locA G.n xA k ∧ DisjointRange locA G.n pA (coreParamsSize r) ∧
      hSub0 + nBlocks * Sprev < 2 ^ w ∧ 16 < 2 ^ w)
    (hj_lt : j < nBlocks) (hact_j : bst.active j = true)
    (hsav_le : ∀ i < nBlocks, bst.active i = false → (bst.savedS i).card ≤ b)
    (hInv : SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
      tmpA hSub0 memStart G X bst j res cutIds pairs cPrimeAddrs compAddrs cPrimeLists compLists st)
    (hOut_j : CoreOutAt st1.mem (tmpA + 4 * b) (.expander S))
    (hSpec_j : CoreSpec (coreParamsOf cfg M r) (q - 1)
      (Graph.mk G.n (witnessEdges (bst.rounds j) (bst.numRounds j)))
      (blockSet (X.sort (· ≤ ·)) b j) (.expander S))
    (hr12_ge : st.regs 12 ≤ st1.regs 12) (hr12_le : st1.regs 12 ≤ st.regs 12 + Sprev)
    (hzf1 : ZeroFrom st1.mem (st1.regs 12)) (hloc1 : ∀ u < G.n, st1.mem (locA + u) = 0)
    (hfr1 : ∀ a < st.regs 12, (a < (sbPersist h0 k b nBlocks (LParam M)).wRelA ∨ (sbPersist h0 k b nBlocks (LParam M)).hPersist ≤ a) →
      (a < tmpA + 4 * b ∨ tmpA + 4 * b + 2 + b ≤ a) → st1.mem a = st.mem a)
    (hregs1 : (∀ r < 28, r ≠ 12 → st1.regs r = st.regs r) ∧
      st1.regs 28 = xA + j * b ∧
      st1.regs 29 = (sbPersist h0 k b nBlocks (LParam M)).wBaseA + j * (sbPersist h0 k b nBlocks (LParam M)).wStride ∧
      st1.regs 30 = tmpA + 4 * b) :
    ∃ cutIds' pairs' cPrimeAddrs' compAddrs' cPrimeLists' compLists' st' cost,
      Runs w p ω sbQueryAfterCallStmt st1 .normal st' cost ∧
      SbQueryInv cfg M r q Sprev gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA
        tmpA hSub0 memStart G X bst (j + 1) (Function.update res j (.expander S))
        cutIds' pairs' cPrimeAddrs' compAddrs' cPrimeLists' compLists'
        { mem := st'.mem, regs := Function.update st'.regs 27 (j + 1), pos := st'.pos } ∧
      st'.regs 14 = st.regs 14 ∧ st'.regs 15 = st.regs 15 ∧ st'.regs 27 = j ∧
      cost ≤ 270 * b + 430 := by
  set ps := sbPersist h0 k b nBlocks (LParam M)
  set vs := X.sort (· ≤ ·)
  set B_j := blockSet vs b j
  set B_l := B_j.sort (· ≤ ·)
  set subOutA := tmpA + 4 * b
  set t := cutIds.length
  set pPtr := pairsA + 1 + t * (2 + b)
  rcases hcur_lay with ⟨hP_le, hpairs_eq, htmp_eq, hhSub_eq, hx_le, hp_le, hloc_le,
    hd_loc_x, hd_loc_p, hmem_w, hw16⟩
  have hnb_b : nBlocks * b ≤ k := by
    have := numFullBlocks_mul_le vs b
    rw [← hnb_eq, Finset.length_sort, ← hX_at.1] at this; exact this
  have hjb_le : j * b + b ≤ nBlocks * b := by
    have : (j + 1) * b ≤ nBlocks * b := Nat.mul_le_mul_right b (by omega)
    linarith
  have ht_le_j : t ≤ j := by
    dsimp only [t]; rw [hInv.cutIds_eq]
    exact (List.length_filterMap_le _ _).trans (by rw [List.length_range])
  have ht_lt_nb : t < nBlocks := lt_of_le_of_lt ht_le_j hj_lt
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by
    dsimp only [ps, sbPersist]; omega
  have hX_blk : VertsAt memStart (xA + j * b) b B_j :=
    vertsAt_blockSet hX_at (by rw [← hnb_eq]; exact hj_lt)
  have hB_len : B_l.length = b := by rw [Finset.length_sort, ← hX_blk.1]
  have hB_lt : B_l.Pairwise (· < ·) := pairwise_lt_sort B_j
  have hB_fin : B_l.toFinset = B_j := by ext u; simp [B_l]
  have hB_sub : ∀ u ∈ B_l, u < G.n := fun u hu => by
    have hu' : u ∈ B_j := hB_fin ▸ List.mem_toFinset.mpr hu
    have hsub : B_j ⊆ X := by
      have h1 := blockSet_subset_toFinset vs b j
      rwa [show vs.toFinset = X by ext v; simp [vs]] at h1
    exact Finset.mem_range.mp (hX_sub (hsub hu'))
  have hB_at1 : ListAt st1.mem (xA + j * b) B_l := fun idx hidx => by
    have ha_lt : xA + j * b + idx < ps.wRelA := by omega
    have ha_st : st1.mem (xA + j * b + idx) = st.mem (xA + j * b + idx) :=
      hfr1 _ (by have := hInv.h_ge; omega) (Or.inl (by omega)) (Or.inl (by omega))
    have ha_loc : xA + j * b + idx < locA ∨ locA + G.n ≤ xA + j * b + idx := by
      rcases hd_loc_x with h | h <;> [right; left] <;> omega
    have ha_ps : xA + j * b + idx < ps.actA ∨ ps.wBaseA ≤ xA + j * b + idx := Or.inl (by omega)
    rw [ha_st, hInv.frame_persist _ ha_lt ha_loc ha_ps]
    exact hX_blk.2 idx hidx
  have hsubOut_w : subOutA + 2 + b < 2 ^ w := by omega
  have hres'_eq : ∀ i < j, Function.update res j (.expander S) i = res i := fun i hi =>
    Function.update_of_ne (by omega) _ _
  have hargs1 : SbArgs q gA k xA b nBlocks z pA locA fA outA h0 (LParam M) st1 :=
    sbArgs_of_eq hInv.args (fun r hr => hregs1.1 r (by omega) (by omega))
  -- Split on `(.expander S)`
  rcases hOut_j with ⟨htag1, S_l, hS_nd, hS_fin, hS_len_mem, hS_at1⟩
  have hS_sub : S ⊆ B_j := hSpec_j.1
  have hS_card : S_l.length = S.card := by rw [← hS_fin, List.toFinset_card_of_nodup hS_nd]
  have hS_le : S_l.length ≤ b := by
    rw [hS_card, hX_blk.1]; exact Finset.card_le_card hS_sub
  have hSav_w : ps.savA + j * b + b < 2 ^ w := by omega
  have hCmp_w : ps.cmpA + j * b + b < 2 ^ w := by omega
  have hsub_ge_p : (sbPersist h0 k b nBlocks (LParam M)).hPersist ≤ subOutA := by
    change ps.hPersist ≤ subOutA; omega
  have hrun := sbQueryAfterExp_run (p := p) (ω := ω) hB_len hB_lt hB_fin hB_sub hB_at1 hX_blk.1
    htag1 hS_fin hS_sub hS_card hS_le hS_len_mem hS_at1 hloc1 hj_lt hnb_b hjb_le
    hx_le hloc_le hd_loc_x hsub_ge_p hsubOut_w hw16
    hargs1.r4 hargs1.r5 hargs1.r8 hargs1.r17 hargs1.r18 hargs1.r19
    ((hregs1.1 27 (by decide) (by decide)).trans hInv.r27) hregs1.1 hregs1.2.1 hregs1.2.2.2
  rcases hrun with ⟨o, st', cost, hruns, hpost, hcost⟩
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨hreg', hr12', hloc', hfr', hsavL', hcmpL', hact', hsav', hcmp'⟩
    have hps_id : sbPersist h0 k b nBlocks (LParam M) = ps := rfl
    rw [hps_id] at hsub_ge_p hfr' hsavL' hcmpL' hact' hsav' hcmp'
    have hfr_outside : ∀ a, (a < locA ∨ locA + G.n ≤ a) →
        (a < ps.actA ∨ ps.wBaseA ≤ a) → (a < ps.wRelA ∨ ps.hPersist ≤ a) →
        (a < subOutA ∨ subOutA + 2 + b ≤ a) →
        a < st.regs 12 → st'.mem a = st.mem a := fun a h1 h2 hrel h3 h4 => by
      rw [hfr' a h1 (by omega) (by omega) (by omega) (by omega) (by omega), hfr1 a h4 hrel h3]
    refine ⟨cutIds, pairs, cPrimeAddrs, compAddrs, cPrimeLists, compLists, st', cost, hruns,
      ?_, hreg' 14 (by decide) (by decide), hreg' 15 (by decide) (by decide),
      (hreg' 27 (by decide) (by decide)).trans hInv.r27, by omega⟩
    refine ⟨sbArgs_of_eq hInv.args (fun r hr => by
        dsimp only; rw [Function.update_of_ne (by omega)]; exact hreg' r (by omega) (by omega)),
      by dsimp only; rw [Function.update_of_ne (by decide), hreg' 13 (by decide) (by decide), hInv.r13],
      by dsimp only; rw [Function.update_of_ne (by decide), hreg' 22 (by decide) (by decide), hInv.r22],
      by dsimp only; rw [Function.update_of_ne (by decide), hreg' 23 (by decide) (by decide), hInv.r23],
      by dsimp only; rw [Function.update_of_ne (by decide), hreg' 24 (by decide) (by decide), hInv.r24],
      by dsimp only; rw [Function.update_of_ne (by decide), hreg' 25 (by decide) (by decide), hInv.r25],
      by dsimp only; rw [Function.update_of_ne (by decide), hreg' 26 (by decide) (by decide), hInv.r26],
      by dsimp only; rw [Function.update_self],
      by dsimp only; rw [Function.update_of_ne (by decide), hr12']; have := hInv.h_ge; omega,
      by dsimp only; rw [Function.update_of_ne (by decide), hr12']; have := hInv.h_le; rw [Nat.succ_mul]; omega,
      fun a ha => by
        dsimp only at ha ⊢; rw [Function.update_of_ne (by decide), hr12'] at ha
        have ha_ge : hSub0 ≤ a := le_trans (le_trans hInv.h_ge hr12_ge) ha
        rw [hfr' a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega)]
        exact hzf1 a ha,
      hloc', ?_, ?_, ?_, hInv.lens_eq, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi hact
      by_cases hij : i = j
      · subst hij; rw [Function.update_self]; exact hSpec_j
      · rw [Function.update_of_ne hij]; exact hInv.res_spec i (by omega) hact
    · rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        hact_j, Function.update_self]
      simp only [ite_true, List.append_nil]
      rw [hInv.cutIds_eq]
      exact filterMap_range_congr fun i hi => by rw [hres'_eq i hi]
    · rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        hact_j, Function.update_self]
      simp only [ite_true, List.append_nil]
      rw [hInv.pairs_eq]
      exact filterMap_range_congr fun i hi => by rw [hres'_eq i hi]
    · intro idx hidx
      have hidx_lt : idx < nBlocks := lt_of_lt_of_le hidx (le_of_lt ht_lt_nb)
      have hge := hInv.h_ge
      have h1 : ∀ a, cutRecsA ≤ a → a < tmpA → st'.mem a = st.mem a := fun a ha1 ha2 => by
        clear hruns hfr' hfr1 hB_at1 hS_at1 hsav' hcmp' hB_lt hB_sub hX_blk hX_at hX_sub hSpec_j hS_sub hS_fin hS_nd hInv
        exact hfr_outside a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (by omega)
      exact sbQuery_recs_at_frame (h0 := h0) (k := k) (L := LParam M)
        hInv.lens_eq hidx hidx_lt hb_even hpairs_eq htmp_eq h1 (hInv.recs_at idx hidx)
    · dsimp only
      intro i hi
      rw [hps_id]
      by_cases hij : i = j
      · subst hij; simp only [Nat.lt_succ_self, hact_j, and_self, ite_true, Function.update_self]; exact hact'
      · have hge := hInv.h_ge
        have hoth := sbQueryAfterExp_other_eq (h0 := h0) (k := k) (b := b) (nBlocks := nBlocks)
          (L := LParam M) hloc_le hsub_ge_p (by omega) hi hj_lt hij hfr' hfr1
        rw [hoth.1]
        have hprev := hInv.act_mem i hi
        dsimp only at hprev; rw [hps_id] at hprev
        rw [hprev]
        have hiff : i < j + 1 ↔ i < j := by omega
        simp only [hiff, Function.update_of_ne hij]
    · dsimp only
      intro i hi
      rw [hps_id]
      by_cases hij : i = j
      · subst hij
        refine ⟨fun hf => absurd hact_j (by simp [hf]), fun _ _ S' hS' => ?_⟩
        rw [Function.update_self] at hS'
        cases hS'
        exact ⟨hsavL', hcmpL', hsav', hcmp'⟩
      · have hpre := hInv.saved_mem i hi
        dsimp only at hpre; rw [hps_id] at hpre
        have hge := hInv.h_ge
        have hoth := sbQueryAfterExp_other_eq (h0 := h0) (k := k) (b := b) (nBlocks := nBlocks)
          (L := LParam M) hloc_le hsub_ge_p (by omega) hi hj_lt hij hfr' hfr1
        have hBi_card : (blockSet vs b i).card = b := card_blockSet (Finset.sort_nodup X (· ≤ ·)) (by rw [← hnb_eq]; exact hi)
        refine ⟨fun hf => ?_, fun hij1 hact S' hS' => ?_⟩
        · rcases hpre.1 hf with ⟨h1, h2, h3, h4⟩
          have hlenS : ((bst.savedS i).sort (· ≤ ·)).length ≤ b := by
            rw [Finset.length_sort]; exact hsav_le i hi hf
          exact ⟨hoth.2.1.trans h1, hoth.2.2.1.trans h2,
            fun m hm => (hoth.2.2.2.1 m (lt_of_lt_of_le hm hlenS)).trans (h3 m hm),
            fun m hm => (hoth.2.2.2.2 m (lt_of_lt_of_le hm (by rw [Finset.length_sort]; exact (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq hBi_card)))).trans (h4 m hm)⟩
        · rw [Function.update_of_ne hij] at hS'
          rcases hpre.2 (by omega) hact S' hS' with ⟨h1, h2, h3, h4⟩
          have hSp := hInv.res_spec i (by omega) hact
          rw [hS'] at hSp
          have hlenS' : (S'.sort (· ≤ ·)).length ≤ b := by
            rw [Finset.length_sort]; exact (Finset.card_le_card hSp.1).trans (le_of_eq hBi_card)
          exact ⟨hoth.2.1.trans h1, hoth.2.2.1.trans h2,
            fun m hm => (hoth.2.2.2.1 m (lt_of_lt_of_le hm hlenS')).trans (h3 m hm),
            fun m hm => (hoth.2.2.2.2 m (lt_of_lt_of_le hm (by rw [Finset.length_sort]; exact (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq hBi_card)))).trans (h4 m hm)⟩
    · dsimp only
      intro a ha h1 h2
      rw [hps_id] at ha h2
      have hge := hInv.h_ge
      have hfp := hInv.frame_persist a ha h1 h2
      clear hruns hB_lt hB_sub hX_blk hS_nd hS_fin hS_sub hInv hfr' hfr1
      rw [hfr_outside a h1 h2 (Or.inl ha) (Or.inl (by omega)) (by omega)]
      exact hfp
    · dsimp only
      intro a h1 h2
      rw [hps_id] at h1 h2
      have hge := hInv.h_ge
      have hfw := hInv.frame_w a h1 h2
      clear hruns hB_lt hB_sub hX_blk hS_nd hS_fin hS_sub hInv hfr' hfr1
      rw [hfr_outside a (Or.inr (by omega)) (Or.inr h1) (Or.inl h2) (Or.inl (by omega)) (by omega)]
      exact hfw


end MinCostFlow.ExpanderDecomp
