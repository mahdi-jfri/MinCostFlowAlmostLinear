module

public import MinCostFlow.HierPaths.DelProgScratch
public import MinCostFlow.HierPaths.Impl

/-!
# Word bounds at the Delete entry

The heap budget covers the pruned vertices and the two work lists. The encoded block
bounds the sizes of the cursor lists, and the depth and incidence bounds control the
loss counter arithmetic.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

/-- Scratch bound for one Delete call, including the returned output. -/
def hierDeleteSpace (_phiNum _phiDen n m _M : ℕ) : ℕ :=
  4 + 3 * n + 4 * delPortCap m + (delPortCap m) ^ 2

theorem hierDeleteSpace_form (a : ℕ) :
    SpaceForm a hierDeleteSpace (11 * 16 ^ 12) 12 := by
  intro phiNum phiDen n m M _ _
  let B := phiDen + n + m + M + gammaHP a ((phiDen + phiNum - 1) / phiNum) M + 2
  have hn : n ≤ B := by unfold B; omega
  have hb : 1 ≤ B := by unfold B; omega
  have hm : 16 * m + 16 ≤ 16 * B := by unfold B; omega
  have hcap : delPortCap m ≤ 16 ^ 6 * B ^ 6 := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hm _
  have hB6 : B ^ 6 ≤ B ^ 12 := Nat.pow_le_pow_right hb (by decide)
  have hnB : n ≤ B ^ 12 := hn.trans (by
    simpa only [pow_one] using (Nat.pow_le_pow_right hb (by decide : 1 ≤ 12)))
  have hcap' : delPortCap m ≤ 16 ^ 12 * B ^ 12 :=
    hcap.trans (Nat.mul_le_mul (by decide) hB6)
  have hsq : delPortCap m ^ 2 ≤ 16 ^ 12 * B ^ 12 := by
    have h := Nat.pow_le_pow_left hcap 2
    rwa [mul_pow, ← pow_mul, ← pow_mul] at h
  have hz : 1 ≤ 16 ^ 12 * B ^ 12 := Nat.mul_pos (by decide) (Nat.pow_pos hb)
  have hn' : n ≤ 16 ^ 12 * B ^ 12 := hnB.trans (Nat.le_mul_of_pos_left _ (by decide))
  change 4 + 3 * n + 4 * delPortCap m + delPortCap m ^ 2 ≤ (11 * 16 ^ 12) * B ^ 12
  rw [Nat.mul_assoc]
  omega

private theorem delBranchProduct_le (x b : ℕ) (hb : 0 < b) :
    (leafDepth x b - 1) * b ≤ x := by
  have h : leafDepth x b * b ≤ x + b - 1 := Nat.div_mul_le_self _ _
  cases he : leafDepth x b with
  | zero => simp
  | succ j =>
    rw [he, Nat.succ_mul] at h
    simp only [Nat.succ_sub_one]
    omega

private theorem delDepth_le (x b : ℕ) (hb : 0 < b) : leafDepth x b ≤ x := by
  apply Nat.le_of_lt_succ
  rw [leafDepth, Nat.div_lt_iff_lt_mul hb, Nat.succ_mul]
  have h := Nat.le_mul_of_pos_right x hb
  omega

private theorem delCsr_len_le_encode (x : HierConcrete) {i n j : ℕ}
    {f : ℕ → List ℕ} (hi : i < numSec)
    (hsec : x.sections.getD i [] = csrList n f) (hj : j < n) :
    (f j).length + 1 ≤ x.encode.length := by
  have hp : 0 < (x.sections.getD i []).length := by rw [hsec]; simp [csrList]
  have H := lt_length_of_sec (bs := x.sections) (i := i)
    (by rw [x.length_sections']; exact hi) (k := (x.sections.getD i []).length - 1) (by omega)
  change _ < x.encode.length at H
  have h := delCsrStart_le n f hj
  rw [delCsrStart_succ, ← hsec] at h
  have hstart : 1 ≤ delCsrStart n f j := by unfold delCsrStart; omega
  omega

private theorem delList_flatMap_length_le {f : ℕ → List ℕ} {l : List ℕ} {k : ℕ}
    (h : ∀ t ∈ l, (f t).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons t l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have ht := h t List.mem_cons_self
    have hl := ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    omega

/-- The operation's heap budget gives all word bounds of the functional run. -/
theorem delEntryWorkBounds_of_space {a w : ℕ} {p : PathDSParams}
    (x : HierConcrete) {b e h : ℕ} (hrel : x.H.Rel a x.ms) (hValid : x.ms.abs.Valid p)
    (hb : b + x.encode.length ≤ h)
    (hroom : h + hierDeleteSpace x.ms.abs.phiNum x.ms.abs.phiDen x.n x.m x.ms.abs.M < 2 ^ w)
    (hcur : (∀ v, x.ms.st.supCur v ≤ (x.H.A.C.supportArray v).length) ∧
      (∀ q, x.ms.st.pairCur q ≤ (x.H.A.pairConns q).length)) :
    DelEntryWorkBounds x e h w ∧ h + 1 + 3 * x.n + 1 < 2 ^ w := by
  let P := delPortCap x.m
  obtain ⟨hports, hκ⟩ := x.delPortCap_bounds hrel
  have hpow : 2 ^ x.H.A.x ≤ P := hrel.spec.arrays.numTerm_eq ▸ hports
  have hpowx : x.H.A.x ≤ P := (Nat.lt_two_pow_self (n := x.H.A.x)).le.trans hpow
  have hmP : x.m ≤ P := by
    unfold P delPortCap
    exact (by omega : x.m ≤ 16 * x.m + 16).trans (Nat.le_self_pow (by decide) _)
  have hdel : x.ms.st.deleted.card ≤ x.m := by
    obtain ⟨_, _, _, _, _, _, _, _, hd, _⟩ := hValid
    rw [← hrel.deleted]
    change x.ms.abs.deleted.card ≤ x.ms.abs.G.m
    simpa only [Finset.card_range] using Finset.card_le_card hd
  have hLost : (x.H.A.newLost x.ms.st e).length ≤ P := by
    have hn := length_scan_le hrel.inv.loss
      (l := x.H.A.revList e) (fun t ht => hrel.spec.arrays.numTerm_eq ▸ hrel.spec.arrays.rev_lt e t ht)
    exact hn.trans hpow
  have hConns : ((x.H.A.newLost x.ms.st e).flatMap x.H.A.termConns).length ≤ P ^ 2 := by
    rw [pow_two]
    exact (delList_flatMap_length_le (fun t _ => hrel.spec.arrays.termConns_length t)).trans
      (Nat.mul_le_mul hLost (by omega))
  have hDepth : x.depth ≤ P :=
    (delDepth_le _ _ hrel.spec.arrays.b_pos).trans hpowx
  have hdb : (x.depth - 1) * x.H.A.b ≤ P :=
    (delBranchProduct_le _ _ hrel.spec.arrays.b_pos).trans hpowx
  have hb' : x.encode.length < 2 ^ w := by omega
  change h + (4 + 3 * x.n + 4 * P + P ^ 2) < 2 ^ w at hroom
  refine ⟨⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, hcur.2, hcur.1⟩, by omega⟩
  · unfold delLostBase
    omega
  · unfold delLostBase
    omega
  · intro q hq
    exact (delCsr_len_le_encode x (i := 8) (by decide) rfl hq).trans_lt hb'
  · intro v hv
    have h := delCsr_len_le_encode x (i := 9) (f := fun v =>
      (x.H.A.C.supportArray v).flatMap entryWords) (by decide) rfl hv
    have hlen : ∀ l : List SupportEntry, l.length ≤ (l.flatMap entryWords).length := by
      intro l
      induction l with
      | nil => simp
      | cons t l ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons, length_entryWords]
        omega
    exact ((Nat.succ_le_succ (hlen _)).trans h).trans_lt hb'

end MinCostFlow.HierPaths

end
