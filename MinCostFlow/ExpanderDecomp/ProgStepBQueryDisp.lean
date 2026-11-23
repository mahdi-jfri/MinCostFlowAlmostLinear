module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.ProgStepBQueryExp

import Mathlib.Tactic.Linarith

/-!
# Step B Per-Block Post-Call Cut Branch and Dispatch (`ProgStepBQueryDisp`)

Verifies the `.cut U` branch (`sbQueryOneBlock_afterCut`) and combines it with
`sbQueryOneBlock_afterExp` (`ProgStepBQueryExp.lean`) into `sbQueryOneBlock_afterCall`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

private lemma sbQueryAfterCut_run {w n b nBlocks k h0 L locA xA cutRecsA pairsA tmpA subOutA t j : ℕ}
    {p : Program} {B_l U_l : List ℕ} {B_j U : Finset ℕ} {st st1 : State} {ω : ℕ → Bool}
    (hb_even : Even b) (hB_len : B_l.length = b) (hB_lt : B_l.Pairwise (· < ·)) (hB_fin : B_l.toFinset = B_j)
    (hB_sub : ∀ u ∈ B_l, u < n) (hB_at1 : ListAt st1.mem (xA + j * b) B_l)
    (htag0 : st1.mem subOutA = 0) (hU_fin : U_l.toFinset = U) (hU_sub : U ⊆ B_j)
    (hU_le : U_l.length ≤ b) (hU_len_mem : st1.mem (subOutA + 1) = U_l.length)
    (hU_at1 : ListAt st1.mem (subOutA + 2) U_l)
    (hloc1 : ∀ u < n, st1.mem (locA + u) = 0)
    (hj_lt : j < nBlocks) (ht_lt_nb : t < nBlocks) (hnb_b : nBlocks * b ≤ k) (hjb_le : j * b + b ≤ nBlocks * b)
    (hx_le : xA + k ≤ h0) (hloc_le : locA + n ≤ h0) (hd_loc_x : DisjointRange locA n xA k)
    (hP_le : (sbPersist h0 k b nBlocks L).hPersist ≤ cutRecsA)
    (hpairs_eq : pairsA = cutRecsA + 3 * nBlocks)
    (htmp_eq : tmpA = pairsA + 1 + nBlocks * (2 + b))
    (hsub_eq : subOutA = tmpA + 4 * b)
    (hsubOut_w : subOutA + 2 + b < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hr4 : st1.regs 4 = b) (hr8 : st1.regs 8 = locA)
    (hr22 : st1.regs 22 = cutRecsA) (hr24 : st1.regs 24 = tmpA)
    (hr25 : st1.regs 25 = t) (hr26 : st1.regs 26 = pairsA + 1 + t * (2 + b))
    (hregs1_lt : ∀ r < 28, r ≠ 12 → st1.regs r = st.regs r)
    (hr28 : st1.regs 28 = xA + j * b)
    (hr29 : st1.regs 29 = (sbPersist h0 k b nBlocks L).wBaseA + j * (sbPersist h0 k b nBlocks L).wStride)
    (hr30 : st1.regs 30 = subOutA) :
    let ps := sbPersist h0 k b nBlocks L
    let pPtr := pairsA + 1 + t * (2 + b)
    let C' := padToHalf B_j (smallerSide B_j U)
    ∃ o st' cost,
      Runs w p ω sbQueryAfterCallStmt st1 o st' cost ∧
      (normalPost fun st' =>
        (∀ r < 28, r ≠ 12 → r ≠ 25 → r ≠ 26 → st'.regs r = st.regs r) ∧
        st'.regs 12 = st1.regs 12 ∧
        st'.regs 25 = t + 1 ∧
        st'.regs 26 = pPtr + 2 + b ∧
        (∀ u < n, st'.mem (locA + u) = 0) ∧
        (∀ a, (a < locA ∨ locA + n ≤ a) →
          (a < tmpA ∨ tmpA + 4 * b ≤ a) →
          (a < pPtr ∨ pPtr + 2 + b ≤ a) →
          a ≠ cutRecsA + 3 * t → a ≠ cutRecsA + 3 * t + 1 → a ≠ cutRecsA + 3 * t + 2 →
          st'.mem a = st1.mem a) ∧
        st'.mem (cutRecsA + 3 * t) = ps.wBaseA + j * ps.wStride ∧
        st'.mem (cutRecsA + 3 * t + 1) = pPtr + 1 ∧
        st'.mem (cutRecsA + 3 * t + 2) = pPtr + 2 + b / 2 ∧
        st'.mem pPtr = b / 2 ∧
        ListAt st'.mem (pPtr + 1) (C'.sort (· ≤ ·)) ∧
        st'.mem (pPtr + 1 + b / 2) = b / 2 ∧
        ListAt st'.mem (pPtr + 2 + b / 2) ((B_j \ C').sort (· ≤ ·))) o st' ∧
      cost ≤ 270 * b + 430 := by
  intro ps pPtr C'
  have hP_le' : ps.hPersist ≤ cutRecsA := hP_le
  have h2half : 2 * (b / 2) = b := by rcases hb_even with ⟨m, hm⟩; omega
  have hps_ord : h0 + 1 + k ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA + nBlocks * ps.wStride = ps.rangeB_A ∧ ps.rangeB_A + b = ps.wRelA ∧
      ps.wRelA + ps.wStride = ps.hPersist := by dsimp only [ps, sbPersist]; omega
  have hpPtr_le_tmp : pPtr + 2 + b ≤ tmpA := by
    have h1 : (t + 1) * (2 + b) ≤ nBlocks * (2 + b) := Nat.mul_le_mul_right (2 + b) (by omega)
    dsimp only [pPtr]; rw [Nat.succ_mul] at h1; omega
  refine runs_start_le ?_
  dsimp only [sbQueryAfterCallStmt, seqStmts]
  refine runs_seq_assign_le (v := U_l.length)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr30) (Expr.eval_const (by omega)) (by omega))
      (by rw [hU_len_mem])) ?_
  refine runs_cond_le (v := 0)
    (Expr.eval_eq_false
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr30]))
        htag0)
      (Expr.eval_const (by omega)) (by decide) (by omega))
    (fun h => absurd rfl h) (fun _ => ?_)
  refine runs_seq_assign_le (v := subOutA + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hr30]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  let st2 : State :=
    { mem := st1.mem,
      regs := Function.update (Function.update st1.regs 31 U_l.length) 30 (subOutA + 2),
      pos := st1.pos }
  have hst2_lt30 : ∀ r < 30, st2.regs r = st1.regs r := fun r hr => by
    dsimp only [st2]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine runs_seq_triple_le
    (sbPadBisect_triple (w := w) (n := n) (b := b) (blkA := xA + j * b)
      (uA := subOutA + 2) (uLen := U_l.length) (locA := locA)
      (tmpA := tmpA) (pPtr := pPtr) (p := p) (mem := st1.mem)
      (B_l := B_l) (U_l := U_l) (U := U) (st₀ := st2)
      hb_even hB_len hB_lt hB_sub hB_at1 rfl hU_le hU_fin (hB_fin.symm ▸ hU_sub) hU_at1 hloc1
      (by rcases hd_loc_x with h | h <;> [left; right] <;> omega)
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inl (by omega))
      (by omega) (by omega) (by omega) (by omega) (by omega) hw16
      ((hst2_lt30 4 (by decide)).trans hr4)
      ((hst2_lt30 8 (by decide)).trans hr8)
      ((hst2_lt30 24 (by decide)).trans hr24)
      ((hst2_lt30 26 (by decide)).trans hr26)
      ((hst2_lt30 28 (by decide)).trans hr28)
      (by simp [st2])
      (by simp [st2]) rfl) rfl ?_
  intro st3 ⟨hoth3, _, hloc3, hfr3, hp0, hpC', hpMid, hpComp⟩
  have hst3_lt30 : ∀ r < 30, st3.regs r = st1.regs r := fun r hr =>
    (hoth3 r (by omega)).trans (hst2_lt30 r hr)
  refine runs_seq_assign_le (v := cutRecsA + 3 * t)
    (Expr.eval_add (Expr.eval_reg_of_eq ((hst3_lt30 22 (by decide)).trans hr22))
      (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq ((hst3_lt30 25 (by decide)).trans hr25)) (by omega)) (by omega)) ?_
  refine runs_seq_store_le (x := cutRecsA + 3 * t) (v := ps.wBaseA + j * ps.wStride)
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self]))
    (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hst3_lt30 29 (by decide), hr29])) ?_
  refine runs_seq_store_le (x := cutRecsA + 3 * t + 1) (v := pPtr + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self])) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hst3_lt30 26 (by decide), hr26]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_store_le (x := cutRecsA + 3 * t + 2) (v := pPtr + 2 + b / 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_self])) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hst3_lt30 26 (by decide), hr26]))
        (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_div (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hst3_lt30 4 (by decide), hr4]))
        (Expr.eval_const (by omega)) (by omega)) (by omega)) ?_
  refine runs_seq_assign_le (v := t + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), hst3_lt30 25 (by decide), hr25]))
      (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_assign_le (v := pPtr + 2 + b)
    (by have heq : pPtr + (2 + b) = pPtr + 2 + b := by omega
        exact heq ▸ Expr.eval_add
          (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst3_lt30 26 (by decide), hr26]))
          (Expr.eval_add (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hst3_lt30 4 (by decide), hr4])) (by omega))
          (by omega)) ?_ (by simp only [Expr.size]; omega)
  refine ⟨fun r hr h12 h25 h26 => by
      dsimp only
      rw [Function.update_of_ne h26, Function.update_of_ne h25, Function.update_of_ne (by omega)]
      exact (hst3_lt30 r (by omega)).trans (hregs1_lt r hr h12),
    by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hst3_lt30 12 (by decide),
    by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self],
    by dsimp only; rw [Function.update_self],
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
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hp0],
    fun idx hidx => by
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      simpa only [hB_fin] using hpC' idx (by simpa only [hB_fin] using hidx),
    by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hpMid],
    fun idx hidx => by
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      simpa only [hB_fin] using hpComp idx (by simpa only [hB_fin] using hidx)⟩

private lemma sbQueryCut_recs_at_frame {h0 k b nBlocks L cutRecsA pairsA idx t : ℕ}
    {mem1 mem2 : ℕ → ℕ} {cutIds : List ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {cPrimeAddrs compAddrs : List ℕ} {cPrimeLists compLists : List (List ℕ)}
    (hlens : cPrimeAddrs.length = cutIds.length ∧ compAddrs.length = cutIds.length ∧
      cPrimeLists.length = cutIds.length ∧ compLists.length = cutIds.length ∧
      pairs.length = cutIds.length)
    (ht_def : t = cutIds.length) (hlt : idx < t) (hb_even : Even b)
    (h1 : ∀ a, cutRecsA ≤ a → a < cutRecsA + 3 * t → mem2 a = mem1 a)
    (h2 : ∀ a, pairsA + 1 + idx * (2 + b) ≤ a → a < pairsA + 1 + (idx + 1) * (2 + b) → mem2 a = mem1 a)
    (hrec :
      let hidx : idx < cutIds.length := ht_def ▸ hlt
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
    let hidx : idx < cutIds.length := ht_def ▸ hlt
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
  have hsucc : (idx + 1) * (2 + b) = idx * (2 + b) + (2 + b) := Nat.succ_mul idx (2 + b)
  refine ⟨hcA, hoA,
    (h1 _ (by omega) (by omega)).trans hr0,
    (h1 _ (by omega) (by omega)).trans hr1,
    (h1 _ (by omega) (by omega)).trans hr2,
    (h2 _ (by omega) (by omega)).trans hp0,
    (h2 _ (by omega) (by omega)).trans hp1,
    hcL, hoL, hcLen, hoLen,
    fun m hm => (h2 _ (by omega) (by omega)).trans (hLatC m hm),
    fun m hm => (h2 _ (by omega) (by omega)).trans (hLatO m hm)⟩

private lemma sbQueryCut_mem_outside {h0 k b nBlocks L locA n cutRecsA pairsA tmpA subOutA hSub0 h12 h12' t pPtr : ℕ}
    {mem1 mem2 mem3 : ℕ → ℕ}
    (hloc_le : locA + n ≤ h0) (hP_le : (sbPersist h0 k b nBlocks L).hPersist ≤ cutRecsA)
    (hpairs_eq : pairsA = cutRecsA + 3 * nBlocks)
    (htmp_eq : tmpA = pairsA + 1 + nBlocks * (2 + b))
    (hsub_eq : subOutA = tmpA + 4 * b) (hhSub_eq : hSub0 = subOutA + 2 + b)
    (ht_lt : t < nBlocks) (hpPtr_ge : pairsA + 1 ≤ pPtr) (hpPtr_le : pPtr + 2 + b ≤ tmpA)
    (h12_ge : hSub0 ≤ h12) (h12'_ge : h12 ≤ h12')
    (hfr' : ∀ a, (a < locA ∨ locA + n ≤ a) → (a < tmpA ∨ tmpA + 4 * b ≤ a) →
      (a < pPtr ∨ pPtr + 2 + b ≤ a) →
      a ≠ cutRecsA + 3 * t → a ≠ cutRecsA + 3 * t + 1 → a ≠ cutRecsA + 3 * t + 2 →
      mem3 a = mem2 a)
    (hfr1 : let ps := sbPersist h0 k b nBlocks L
      ∀ a < h12, (a < ps.wRelA ∨ ps.hPersist ≤ a) → (a < subOutA ∨ subOutA + 2 + b ≤ a) →
        mem2 a = mem1 a) :
    let ps := sbPersist h0 k b nBlocks L
    (∀ a, h12' ≤ a → mem3 a = mem2 a) ∧
    (∀ a, cutRecsA ≤ a → a < cutRecsA + 3 * t → mem3 a = mem1 a) ∧
    (∀ a, pairsA ≤ a → a < pPtr → mem3 a = mem1 a) ∧
    (∀ a < ps.wRelA, (a < locA ∨ locA + n ≤ a) → mem3 a = mem1 a) ∧
    (∀ i < nBlocks,
      mem3 (ps.actA + i) = mem1 (ps.actA + i) ∧
      mem3 (ps.savLenA + i) = mem1 (ps.savLenA + i) ∧
      mem3 (ps.cmpLenA + i) = mem1 (ps.cmpLenA + i) ∧
      (∀ m < b, mem3 (ps.savA + i * b + m) = mem1 (ps.savA + i * b + m)) ∧
      (∀ m < b, mem3 (ps.cmpA + i * b + m) = mem1 (ps.cmpA + i * b + m))) := by
  intro ps
  have hps_id : sbPersist h0 k b nBlocks L = ps := rfl
  rw [hps_id] at hP_le hfr1
  have hps_ord : h0 ≤ ps.actA ∧ ps.actA + nBlocks = ps.savLenA ∧
      ps.savLenA + nBlocks = ps.cmpLenA ∧ ps.cmpLenA + nBlocks = ps.savA ∧
      ps.savA + nBlocks * b = ps.cmpA ∧ ps.cmpA + nBlocks * b = ps.wBaseA ∧
      ps.wBaseA ≤ ps.wRelA ∧ ps.wRelA ≤ ps.hPersist := by
    dsimp only [ps, sbPersist]; omega
  have hbelow : ∀ a < ps.wRelA, (a < locA ∨ locA + n ≤ a) → mem3 a = mem1 a :=
    fun a ha hloc => (hfr' a hloc (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega) (by omega)).trans
      (hfr1 a (by omega) (Or.inl ha) (Or.inl (by omega)))
  refine ⟨fun a ha => hfr' a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega),
    fun a h1 h2 => (hfr' a (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega) (by omega) (by omega)).trans
      (hfr1 a (by omega) (Or.inr (by omega)) (Or.inl (by omega))),
    fun a h1 h2 => (hfr' a (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl h2) (by omega) (by omega) (by omega)).trans
      (hfr1 a (by omega) (Or.inr (by omega)) (Or.inl (by omega))),
    hbelow, fun i hi => ?_⟩
  have hib : i * b + b ≤ nBlocks * b := by
    have : (i + 1) * b ≤ nBlocks * b := Nat.mul_le_mul_right b (by omega); linarith
  exact ⟨hbelow _ (by omega) (Or.inr (by omega)), hbelow _ (by omega) (Or.inr (by omega)),
    hbelow _ (by omega) (Or.inr (by omega)), fun m hm => hbelow _ (by omega) (Or.inr (by omega)),
    fun m hm => hbelow _ (by omega) (Or.inr (by omega))⟩

private lemma sbQueryOneBlock_afterCut {cfg : ParamConfig} {M r q w Sprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA tmpA hSub0 j : ℕ}
    {p : Program} {memStart : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState}
    {res : ℕ → CoreResult} {U : Finset ℕ}
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
    (hOut_j : CoreOutAt st1.mem (tmpA + 4 * b) (.cut U))
    (hSpec_j : CoreSpec (coreParamsOf cfg M r) (q - 1)
      (Graph.mk G.n (witnessEdges (bst.rounds j) (bst.numRounds j)))
      (blockSet (X.sort (· ≤ ·)) b j) (.cut U))
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
        tmpA hSub0 memStart G X bst (j + 1) (Function.update res j (.cut U))
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
  have hres'_eq : ∀ i < j, Function.update res j (.cut U) i = res i := fun i hi =>
    Function.update_of_ne (by omega) _ _
  have hargs1 : SbArgs q gA k xA b nBlocks z pA locA fA outA h0 (LParam M) st1 :=
    sbArgs_of_eq hInv.args (fun r hr => hregs1.1 r (by omega) (by omega))
  -- Split on `(.cut U)`
  rcases hOut_j with ⟨htag0, U_l, hU_nd, hU_fin, hU_len_mem, hU_at1⟩
  have hU_sub : U ⊆ B_j := hSpec_j.1
  have hU_card : U_l.length = U.card := by rw [← hU_fin, List.toFinset_card_of_nodup hU_nd]
  have hU_le : U_l.length ≤ b := by
    rw [hU_card, hX_blk.1]; exact Finset.card_le_card hU_sub
  set C' := padToHalf B_j (smallerSide B_j U)
  have h2half : 2 * (b / 2) = b := by rcases hb_even with ⟨m, hm⟩; omega
  have hpad_lists := smallerSide_padToHalf_lists hB_lt (hB_fin.symm ▸ hU_sub) (hB_len.symm ▸ hb_even)
  have hC'_len : (C'.sort (· ≤ ·)).length = b / 2 := by
    have h := hpad_lists.2.2.2.1; have h1 := hpad_lists.2.1; rw [hB_fin] at h1; rw [← h1, h, hB_len]
  have hcomp_len : ((B_j \ C').sort (· ≤ ·)).length = b / 2 := by
    have h := hpad_lists.2.2.2.2; have h1 := hpad_lists.2.2.1; rw [hB_fin] at h1; rw [← h1, h, hB_len]
  clear hpad_lists
  have hpPtr_le_tmp : pPtr + 2 + b ≤ tmpA := by
    have h1 : (t + 1) * (2 + b) ≤ nBlocks * (2 + b) := Nat.mul_le_mul_right (2 + b) (by omega)
    dsimp only [pPtr]; rw [Nat.succ_mul] at h1; omega
  have hrun := sbQueryAfterCut_run (p := p) (ω := ω) hb_even hB_len hB_lt hB_fin hB_sub hB_at1
    htag0 hU_fin hU_sub hU_le hU_len_mem hU_at1 hloc1 hj_lt ht_lt_nb hnb_b hjb_le
    hx_le hloc_le hd_loc_x hP_le hpairs_eq htmp_eq rfl hsubOut_w hw16
    hargs1.r4 hargs1.r8
    ((hregs1.1 22 (by decide) (by decide)).trans hInv.r22)
    ((hregs1.1 24 (by decide) (by decide)).trans hInv.r24)
    ((hregs1.1 25 (by decide) (by decide)).trans hInv.r25)
    ((hregs1.1 26 (by decide) (by decide)).trans hInv.r26)
    hregs1.1 hregs1.2.1 hregs1.2.2.1 hregs1.2.2.2
  rcases hrun with ⟨o, st', cost, hruns, hpost, hcost⟩
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨hreg', hr12', hr25', hr26', hloc', hfr', hrec0, hrec1, hrec2, hp0, hpC', hpMid, hpComp⟩
    have hps_id : sbPersist h0 k b nBlocks (LParam M) = ps := rfl
    obtain ⟨hmem_zf, hmem_rec, hmem_pairs, hmem_below, hmem_blk⟩ :=
      sbQueryCut_mem_outside (h0 := h0) (k := k) (b := b) (nBlocks := nBlocks) (L := LParam M)
        hloc_le hP_le hpairs_eq htmp_eq rfl hhSub_eq ht_lt_nb (Nat.le_add_right _ _) hpPtr_le_tmp
        hInv.h_ge hr12_ge hfr' hfr1
    rw [hps_id] at hmem_below hmem_blk
    refine ⟨cutIds ++ [j], pairs ++ [(C', B_j \ C')],
      cPrimeAddrs ++ [pPtr + 1], compAddrs ++ [pPtr + 2 + b / 2],
      cPrimeLists ++ [C'.sort (· ≤ ·)], compLists ++ [(B_j \ C').sort (· ≤ ·)],
      st', cost, hruns, ?_, hreg' 14 (by decide) (by decide) (by decide) (by decide),
      hreg' 15 (by decide) (by decide) (by decide) (by decide),
      (hreg' 27 (by decide) (by decide) (by decide) (by decide)).trans hInv.r27, hcost⟩
    refine ⟨sbArgs_of_eq hInv.args (fun r hr => by
        dsimp only; rw [Function.update_of_ne (by omega)]; exact hreg' r (by omega) (by omega) (by omega) (by omega)),
      by dsimp only; rw [Function.update_of_ne (by decide), hreg' 13 (by decide) (by decide) (by decide) (by decide), hInv.r13],
      by dsimp only; rw [Function.update_of_ne (by decide), hreg' 22 (by decide) (by decide) (by decide) (by decide), hInv.r22],
      by dsimp only; rw [Function.update_of_ne (by decide), hreg' 23 (by decide) (by decide) (by decide) (by decide), hInv.r23],
      by dsimp only; rw [Function.update_of_ne (by decide), hreg' 24 (by decide) (by decide) (by decide) (by decide), hInv.r24],
      by dsimp only; rw [Function.update_of_ne (by decide), hr25', List.length_append, List.length_singleton],
      by dsimp only; rw [Function.update_of_ne (by decide), hr26', List.length_append, List.length_singleton, Nat.succ_mul]; dsimp only [pPtr, t]; omega,
      by dsimp only; rw [Function.update_self],
      by dsimp only; rw [Function.update_of_ne (by decide), hr12']; have := hInv.h_ge; omega,
      by dsimp only; rw [Function.update_of_ne (by decide), hr12']; have := hInv.h_le; rw [Nat.succ_mul]; omega,
      ?_, hloc', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      dsimp only at ha ⊢; rw [Function.update_of_ne (by decide), hr12'] at ha
      rw [hmem_zf a ha]; exact hzf1 a ha
    · intro i hi hact
      by_cases hij : i = j
      · subst hij; rw [Function.update_self]; exact hSpec_j
      · rw [Function.update_of_ne hij]; exact hInv.res_spec i (by omega) hact
    · rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        hact_j, Function.update_self]
      simp only [ite_true]
      rw [hInv.cutIds_eq]
      congr 1; exact filterMap_range_congr fun i hi => by rw [hres'_eq i hi]
    · rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        hact_j, Function.update_self]
      simp only [ite_true]
      rw [hInv.pairs_eq]
      congr 1; exact filterMap_range_congr fun i hi => by rw [hres'_eq i hi]
    · simp only [List.length_append, List.length_singleton,
        hInv.lens_eq.1, hInv.lens_eq.2.1, hInv.lens_eq.2.2.1, hInv.lens_eq.2.2.2.1, hInv.lens_eq.2.2.2.2, and_self]
    · intro idx hidx
      simp only [List.length_append, List.length_singleton] at hidx
      by_cases hlt : idx < t
      · dsimp only
        have hidx_p : pairsA + 1 + (idx + 1) * (2 + b) ≤ pPtr := by
          have := Nat.mul_le_mul_right (2 + b) (show idx + 1 ≤ t by omega); dsimp only [pPtr]; omega
        have h2 : ∀ a, pairsA + 1 + idx * (2 + b) ≤ a → a < pairsA + 1 + (idx + 1) * (2 + b) → st'.mem a = st.mem a :=
          fun a ha1 ha2 => hmem_pairs a
            (Nat.le_trans (Nat.le_add_right pairsA 1) (Nat.le_trans (Nat.le_add_right _ _) ha1))
            (lt_of_lt_of_le ha2 hidx_p)
        have hlt' : idx < cutIds.length := hlt
        simp only [List.getElem_append_left hlt',
          List.getElem_append_left (hInv.lens_eq.1.symm ▸ hlt'),
          List.getElem_append_left (hInv.lens_eq.2.1.symm ▸ hlt'),
          List.getElem_append_left (hInv.lens_eq.2.2.1.symm ▸ hlt'),
          List.getElem_append_left (hInv.lens_eq.2.2.2.1.symm ▸ hlt'),
          List.getElem_append_left (hInv.lens_eq.2.2.2.2.symm ▸ hlt')]
        exact sbQueryCut_recs_at_frame (h0 := h0) (k := k) (nBlocks := nBlocks) (L := LParam M)
          hInv.lens_eq rfl hlt hb_even hmem_rec h2 (hInv.recs_at idx hlt)
      · have heq : idx = t := by omega
        subst heq
        dsimp only [t]
        simp only [List.getElem_append_right (le_refl _),
          List.getElem_append_right (le_of_eq hInv.lens_eq.1),
          List.getElem_append_right (le_of_eq hInv.lens_eq.2.1),
          List.getElem_append_right (le_of_eq hInv.lens_eq.2.2.1),
          List.getElem_append_right (le_of_eq hInv.lens_eq.2.2.2.1),
          List.getElem_append_right (le_of_eq hInv.lens_eq.2.2.2.2),
          Nat.sub_self, hInv.lens_eq.1, hInv.lens_eq.2.1, hInv.lens_eq.2.2.1, hInv.lens_eq.2.2.2.1, hInv.lens_eq.2.2.2.2,
          List.getElem_singleton]
        exact ⟨rfl, rfl, hrec0, hrec1, hrec2, hp0, hpMid, trivial, trivial, hC'_len, hcomp_len, hpC', hpComp⟩
    · dsimp only
      intro i hi
      rw [hps_id]
      rw [(hmem_blk i hi).1]
      have hprev := hInv.act_mem i hi
      dsimp only at hprev; rw [hps_id] at hprev
      rw [hprev]
      by_cases hij : i = j
      · subst hij; simp [hact_j]
      · have hiff : i < j + 1 ↔ i < j := by omega
        simp only [hiff, Function.update_of_ne hij]
    · dsimp only
      intro i hi
      rw [hps_id]
      have hBi_card : (blockSet vs b i).card = b :=
        card_blockSet (Finset.sort_nodup X (· ≤ ·)) (by rw [← hnb_eq]; exact hi)
      have hbi := hmem_blk i hi
      have hpre := hInv.saved_mem i hi
      dsimp only at hpre; rw [hps_id] at hpre
      refine ⟨fun hf => ?_, fun hij1 hact S' hS' => ?_⟩
      · rcases hpre.1 hf with ⟨h1, h2, h3, h4⟩
        have hlenS : ((bst.savedS i).sort (· ≤ ·)).length ≤ b := by
          rw [Finset.length_sort]; exact hsav_le i hi hf
        have hlenC : ((blockSet vs b i \ bst.savedS i).sort (· ≤ ·)).length ≤ b := by
          rw [Finset.length_sort]; exact (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq hBi_card)
        exact ⟨hbi.2.1.trans h1, hbi.2.2.1.trans h2,
          fun m hm => (hbi.2.2.2.1 m (lt_of_lt_of_le hm hlenS)).trans (h3 m hm),
          fun m hm => (hbi.2.2.2.2 m (lt_of_lt_of_le hm hlenC)).trans (h4 m hm)⟩
      · by_cases hij : i = j
        · subst hij; rw [Function.update_self] at hS'; cases hS'
        · rw [Function.update_of_ne hij] at hS'
          rcases hpre.2 (by omega) hact S' hS' with ⟨h1, h2, h3, h4⟩
          have hSp := hInv.res_spec i (by omega) hact
          rw [hS'] at hSp
          have hlenS' : (S'.sort (· ≤ ·)).length ≤ b := by
            rw [Finset.length_sort]; exact (Finset.card_le_card hSp.1).trans (le_of_eq hBi_card)
          have hlenC : ((blockSet vs b i \ S').sort (· ≤ ·)).length ≤ b := by
            rw [Finset.length_sort]; exact (Finset.card_le_card Finset.sdiff_subset).trans (le_of_eq hBi_card)
          exact ⟨hbi.2.1.trans h1, hbi.2.2.1.trans h2,
            fun m hm => (hbi.2.2.2.1 m (lt_of_lt_of_le hm hlenS')).trans (h3 m hm),
            fun m hm => (hbi.2.2.2.2 m (lt_of_lt_of_le hm hlenC)).trans (h4 m hm)⟩
    · dsimp only
      intro a ha h1 h2
      rw [hps_id] at ha
      rw [hmem_below a ha h1]
      exact hInv.frame_persist a ha h1 h2
    · dsimp only
      intro a h1 h2
      rw [hps_id] at h1 h2
      rw [hmem_below a h2 (Or.inr (le_trans (by omega) h1))]
      exact hInv.frame_w a h1 h2



/-- Post-`bSubCore` dispatch lemma for an active block `j < nBlocks`. -/
theorem sbQueryOneBlock_afterCall {cfg : ParamConfig} {M r q w Sprev : ℕ}
    {gA k xA b nBlocks z pA locA fA outA h0 cutRecsA pairsA tmpA hSub0 j : ℕ}
    {p : Program} {memStart : ℕ → ℕ} {G : Graph} {X : Finset ℕ} {bst : BlockGameState}
    {res : ℕ → CoreResult} {res_j : CoreResult}
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
    (hOut_j : CoreOutAt st1.mem (tmpA + 4 * b) res_j)
    (hSpec_j : CoreSpec (coreParamsOf cfg M r) (q - 1)
      (Graph.mk G.n (witnessEdges (bst.rounds j) (bst.numRounds j)))
      (blockSet (X.sort (· ≤ ·)) b j) res_j)
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
        tmpA hSub0 memStart G X bst (j + 1) (Function.update res j res_j)
        cutIds' pairs' cPrimeAddrs' compAddrs' cPrimeLists' compLists'
        { mem := st'.mem, regs := Function.update st'.regs 27 (j + 1), pos := st'.pos } ∧
      st'.regs 14 = st.regs 14 ∧ st'.regs 15 = st.regs 15 ∧ st'.regs 27 = j ∧
      cost ≤ 270 * b + 430 := by
  cases res_j with
  | expander S =>
    exact sbQueryOneBlock_afterExp hX_at hX_sub hb_even hnb_eq hcur_lay hj_lt hact_j hsav_le hInv
      hOut_j hSpec_j hr12_ge hr12_le hzf1 hloc1 hfr1 hregs1
  | cut U =>
    exact sbQueryOneBlock_afterCut hX_at hX_sub hb_even hnb_eq hcur_lay hj_lt hact_j hsav_le hInv
      hOut_j hSpec_j hr12_ge hr12_le hzf1 hloc1 hfr1 hregs1

end MinCostFlow.ExpanderDecomp
