module

public import MinCostFlow.LowStretch.ProgClusterSC2
public import MinCostFlow.LowStretch.ProgPSearch

/-!
# The start of a petal search inside a cluster

`PW.Ok.spre`: when the queues are empty, the stamps of the earlier searches are below the new
stamp `rs`, and the slot of the target is the only one that is on, the memory meets the
precondition `SC.SPre` of the search, for the setting `PW.sc`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {t : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ}
  {lo rs : ℕ}

/-- The graph in memory has the shape that Dijkstra asks, on the allowed nodes. -/
theorem Ok.shape (h : W.Ok w mem) (hrs : rs < 2 ^ w) :
    ({ W.L with rs := rs } : DL).Shape w mem (W.Nodes mem) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES
  have hNN := h.hNN
  refine ⟨fun v => ?_, fun u hu => ?_, fun k hk => ?_, h.classes, ?_, ?_, h.fits, hrs, (lt_of_le_of_lt (Nat.le_succ _) h.os_lt),
    h.INF_pos⟩
  · show v < W.L.NN ∧ _ ↔ _
    unfold Nodes; rw [Finset.mem_filter, Finset.mem_range]
  · have hu' := h.nodes_lt hu
    have hl := h.lohi u hu'
    have hm := h.hiMM u (by omega)
    show (if u < W.L.NN then _ else 0) ≤ (if u < W.L.NN then _ else 0) ∧
      (if u < W.L.NN then _ else 0) ≤ W.L.MM
    rw [if_pos (by omega), if_pos (by omega)]
    exact ⟨hl.le, hm⟩
  · exact ⟨h.hdNN k hk, (h.heads k hk).1, (h.heads k hk).2⟩
  · have hs0 : 0 < W.s := by have := h.sv_lt h.conn.1; omega
    have hsub : W.Nodes mem ⊆ Finset.range W.s := fun u hu => Finset.mem_range.mpr (h.nodes_lt hu)
    have e1 : ∑ u ∈ Finset.range W.s, (({ W.L with rs := rs } : DL).deg mem u + 1) =
        ∑ u ∈ Finset.range W.s, ({ W.L with rs := rs } : DL).deg mem u + W.s := by
      rw [Finset.sum_add_distrib]; simp
    have e2 : ∑ u ∈ W.Nodes mem, ({ W.L with rs := rs } : DL).deg mem u ≤
        ∑ u ∈ Finset.range W.s, ({ W.L with rs := rs } : DL).deg mem u :=
      Finset.sum_le_sum_of_subset hsub
    have e3 : ∑ u ∈ Finset.range W.s, (({ W.L with rs := rs } : DL).deg mem u + 1) ≤ W.L.A := by
      calc ∑ u ∈ Finset.range W.s, (({ W.L with rs := rs } : DL).deg mem u + 1)
      _ = ∑ u ∈ Finset.range W.s, (mem (W.L.HI + u) - mem (W.L.LO + u) + 1) := by
          refine Finset.sum_congr rfl fun u hu => ?_
          have := Finset.mem_range.mp hu
          show (if u < W.L.NN then _ else 0) - (if u < W.L.NN then _ else 0) + 1 = _
          rw [if_pos (by omega), if_pos (by omega)]
      _ ≤ W.L.A := h.budget
    show _ ≤ W.L.A
    omega
  · dsimp only
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, l12⟩

/-- **The start of a search.** -/
theorem Ok.spre (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) (hrs : rs < 2 ^ w)
    (hpq : PQRep mem W.L.D W.L.J W.L.A W.L.INF (fun _ => []))
    (htz : ∀ c < W.L.J, mem (pqT W.L.D W.L.J c) = 0)
    (hst : ∀ v < W.L.NN, mem (W.L.TS + v) < rs ∧ mem (W.L.TS + 2 * W.L.NN + v) < rs) :
    SC.SPre w (W.sc mem t st hw lo rs) ((W.sc mem t st hw lo rs).X.args ++ [W.sv t]) mem := by
  refine ⟨rfl, rfl, h.sc_ok hp, h.shape hrs, hpq, fun c hc _ => htz c hc, hst, fun i hi => ?_⟩
  change i < (W.Hl t st).length at hi
  show mem (W.L.HD + W.slotA mem ((W.Hl t st).getD i 0)) =
    if i = 0 then mem (W.NXT + (W.Hl t st).getD 0 0) else W.s
  split_ifs with h0
  · subst h0; exact hp.sl0
  · have hne : (W.Hl t st).getD i 0 ≠ W.sv t := by
      intro e
      have e0 : (W.Hl t st).getD 0 0 = W.sv t := rfl
      rw [← e0, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)] at e
      exact h0 ((List.Nodup.getElem_inj_iff hp.nd).mp e)
    exact hp.slS _ (h.H_lt hp (getD_mem' hi)) hne

end PW

end MinCostFlow.LowStretch
