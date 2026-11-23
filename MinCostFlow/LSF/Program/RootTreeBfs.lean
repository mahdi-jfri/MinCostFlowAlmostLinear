module

public import MinCostFlow.LSF.Program.RootTreeScan
import Mathlib.Tactic.Linarith

/-!
# Rooting a tree: the breadth-first search loop

The outer loop of the search takes the next vertex `u` of the queue and scans its half-edges
(`rtScan_triple`). We prove `rtBfs_triple` with `Triple.loop_inv`, indexed by the queue head
`qh` and the queue `Q`. The invariant says that the first `qh` vertices of `Q` are scanned, so
their neighbours are in `Q`. When the loop stops, `qh` is the length of `Q`, so `Q` is closed
under adjacency; since every vertex is reachable from `r`, every vertex is in `Q`.

The cost is paid by the potential `200 (n - qh) + 120 (2 m - D)`, where `D` is the sum of the
degrees of the scanned vertices; it is at most `2 m` because they are distinct
(`rtDeg_sum_le`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-- The invariant of the search loop with queue head `qh` and queue `Q`. -/
def RTBfsInv (n m tailArr headArr r outPtr sPtr : ℕ) (tl hd : ℕ → ℕ) (m₁ : ℕ → ℕ)
    (a : ℕ × List ℕ) (st : State) : Prop :=
  RTRegs st n m tailArr headArr r outPtr sPtr ∧ st.regs 14 = a.1 ∧ st.regs 15 = a.2.length ∧
  a.1 ≤ a.2.length ∧ RTCore n m r outPtr sPtr tl hd m₁ a.2 st.mem ∧
  ∀ j < a.1, ∀ h ∈ rtHalf tl hd (2 * m) (a.2.getD j 0), rtOther tl hd h ∈ a.2

/-- The remaining cost of the search loop. -/
def rtBfsRem (n m : ℕ) (tl hd : ℕ → ℕ) (a : ℕ × List ℕ) : ℕ :=
  200 * (n - a.1) + 120 * (2 * m - ((a.2.take a.1).map (rtDeg m tl hd)).sum) + 10

/-- The state when the search stops: every vertex is in the queue. -/
def RTBfsDone (n m tailArr headArr r outPtr sPtr : ℕ) (tl hd : ℕ → ℕ) (m₁ : ℕ → ℕ)
    (st : State) : Prop :=
  RTRegs st n m tailArr headArr r outPtr sPtr ∧
  ∃ Q, RTCore n m r outPtr sPtr tl hd m₁ Q st.mem ∧ ∀ x < n, x ∈ Q

private lemma take_succ_of_append {Q ext : List ℕ} {qh : ℕ} (hq : qh < Q.length) :
    (Q ++ ext).take (qh + 1) = Q.take qh ++ [Q[qh]] := by
  rw [List.take_append_of_le_length (by omega), List.take_succ_eq_append_getElem hq]

theorem rtBfs_triple {w : ℕ} {p : Program} {n m tailArr headArr r outPtr sPtr : ℕ}
    {tl hd : ℕ → ℕ} {m₁ : ℕ → ℕ}
    (hI : RTScanInput n m tailArr headArr outPtr sPtr tl hd m₁)
    (hw : 16 ≤ 2 ^ w) (hword : sPtr + 4 * n + 2 * m < 2 ^ w)
    (hchain : ∀ u < n, ChainFrom m₁ (sPtr + n) (m₁ (sPtr + u)) (rtHalf tl hd (2 * m) u))
    (hreach : ∀ x < n, Relation.ReflTransGen (rtAdj m tl hd) r x) (a₀ : ℕ × List ℕ) :
    Triple w p (RTBfsInv n m tailArr headArr r outPtr sPtr tl hd m₁ a₀)
      (.loop (.bin .lt (.reg 14) (.reg 15)) rtBfsBody)
      (normalPost (RTBfsDone n m tailArr headArr r outPtr sPtr tl hd m₁))
      (fun _ => rtBfsRem n m tl hd a₀) := by
  have hw1 : 1 < 2 ^ w := by omega
  refine Triple.loop_inv (Inv := RTBfsInv n m tailArr headArr r outPtr sPtr tl hd m₁)
    (condVal := fun st => if st.regs 14 < st.regs 15 then 1 else 0)
    (fun a => n - a.1) (rtBfsRem n m tl hd) ?_ ?_ ?_ a₀
  · intro a st hinv
    have h14 := hinv.2.1; have h15 := hinv.2.2.1
    have hlen := hinv.2.2.2.2.1.length_le
    eval_expr
  · rintro ⟨qh, Q⟩ st ⟨hb, h14, h15, hle, hc, hcl⟩ hv
    dsimp only at h14 h15 hle hc hcl ⊢
    have hqh : qh = Q.length := by
      by_contra hne
      have hlt : qh < Q.length := by omega
      simp [h14, h15, hlt] at hv
    refine ⟨⟨hb, Q, hc, ?_⟩, by simp only [rtBfsRem, Expr.size_bin, Expr.size_reg]; omega⟩
    -- `Q` is closed under adjacency, so it contains every vertex reachable from `r`
    have hclosed : ∀ y ∈ Q, ∀ x, rtAdj m tl hd y x → x ∈ Q := by
      intro y hy x hyx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
      obtain ⟨h, hh, rfl⟩ := rtAdj_iff.mp hyx
      exact hcl j (by omega) h (by rwa [List.getD_eq_getElem _ _ hj])
    have hall : ∀ x, Relation.ReflTransGen (rtAdj m tl hd) r x → x ∈ Q := by
      intro x hrt
      induction hrt with
      | refl => exact hc.r_mem
      | tail _ hyz ih => exact hclosed _ ih _ hyz
    exact fun x hx => hall x (hreach x hx)
  · rintro ⟨qh, Q⟩ st ⟨hb, h14, h15, hle, hc, hcl⟩ hv
    dsimp only at h14 h15 hle hc hcl ⊢
    have hqh : qh < Q.length := by
      by_contra hne
      simp [h14, h15, hne] at hv
    set u := Q[qh] with hu_def
    have huQ : u ∈ Q := List.getElem_mem hqh
    have hun := hc.lt u huQ
    have hlen := hc.length_le
    refine ⟨120 * rtDeg m tl hd u + 40, ?_⟩
    intro s ω hs
    subst s
    have r11 := hb.r11; have r6 := hb.r6
    have hout := hI.hout
    have hq := hc.q qh hqh
    have hfirst : st.mem (sPtr + u) = m₁ (sPtr + u) :=
      hc.fr _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
    refine runs_start_le ?_
    unfold rtBfsBody
    refine runs_seq_assign_le (v := u) (by eval_expr) ?_
    refine runs_seq_assign_le (v := qh + 1) (by eval_expr) ?_
    refine runs_seq_assign_le (v := m₁ (sPtr + u)) (by rw [← hfirst]; eval_expr) ?_
    have hstart : RTScanInv n m tailArr headArr r outPtr sPtr tl hd m₁ u (qh + 1) Q
        (rtHalf tl hd (2 * m) u)
        ⟨st.mem, Function.update (Function.update (Function.update st.regs 16 u) 14 (qh + 1))
          17 (m₁ (sPtr + u)), st.pos⟩ := by
      refine ⟨((hb.upd 16 u (by omega)).upd 14 (qh + 1) (by omega)).upd 17 _ (by omega),
        by simp, by simp, by simpa using hchain u hun, [], [], by simpa using h15,
        by simpa using hc, by simp, by simp⟩
    refine runs_triple_le (rtScan_triple (p := p) hI hword huQ) hstart ?_ ?_
    · intro o st' hpost
      cases o with
      | returned v => exact False.elim hpost
      | normal =>
        obtain ⟨hb', h14', h16', -, ext, pre, h15', hc', hpre, hpreQ⟩ := hpost
        simp only [List.append_nil] at hpre
        subst hpre
        refine ⟨(qh + 1, Q ++ ext), ⟨hb', h14', h15', by simp; omega, hc', ?_⟩, ?_, ?_⟩
        · intro j hj h hh
          by_cases hjq : j < qh
          · have hjQ : j < Q.length := by omega
            have heq : (Q ++ ext).getD j 0 = Q.getD j 0 := by
              rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hjQ,
                List.getElem_append_left hjQ]
            rw [heq] at hh
            exact List.mem_append_left _ (hcl j hjq h hh)
          · have hje : j = qh := by simp only at hj; omega
            subst hje
            have heq : (Q ++ ext).getD j 0 = u := by
              rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hqh]
            rw [heq] at hh
            exact hpreQ h hh
        · show n - (qh + 1) < n - qh
          omega
        · simp only [rtBfsRem, take_succ_of_append hqh, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton, Expr.size_bin, Expr.size_reg, ← hu_def]
          have hD : ((Q.take qh).map (rtDeg m tl hd)).sum + rtDeg m tl hd u ≤ 2 * m := by
            have h := rtDeg_sum_le (m := m) (tl := tl) (hd := hd)
              (L := Q.take (qh + 1)) (hc.nd.sublist (List.take_sublist _ _))
            rwa [List.take_succ_eq_append_getElem hqh, List.map_append, List.sum_append,
              List.map_singleton, List.sum_singleton, ← hu_def] at h
          omega
    · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

end

end MinCostFlow.LSF.Program
