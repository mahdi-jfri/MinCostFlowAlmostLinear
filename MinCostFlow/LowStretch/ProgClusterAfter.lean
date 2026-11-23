module

public import MinCostFlow.LowStretch.ProgClusterPetal
public import MinCostFlow.LowStretch.ProgClusterSPre
public import MinCostFlow.LowStretch.ProgPFin

/-!
# The memory after a petal search

After `psrchA`, the memory `memC` is the memory `memL` of the stopped state with the queues
emptied. This file reads from `memC` what the end of a petal needs: the cells of the graph are
those at the start (`PW.Ok.after_fix`), and the counter, the settled list and the pointer are
those of the stopped state (`PW.Ok.after_ctl`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {t : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ}
  {lo rs : ℕ}

theorem Ok.not_pqOut (h : W.Ok w mem) {x : ℕ} (hx : x < W.L.D ∨ W.RR ≤ x) :
    ¬ pqOut W.L.D W.L.J x := by
  have := h.hR
  unfold pqOut pqSize at *
  omega

/-- The cells of the graph after the search. -/
theorem Ok.after_fix (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) {a : SG} {memL memC : ℕ → ℕ}
    (hI : (W.sc mem t st hw lo rs).Inv w a memL) (hclr : (W.sc mem t st hw lo rs).SClr memL memC)
    {v : ℕ} (hv : v < W.L.NN) :
    memC (W.NXT + v) = mem (W.NXT + v) ∧ memC (W.L.HI + v) = mem (W.L.HI + v) ∧
      memC (W.L.LO + v) = mem (W.L.LO + v) ∧ memC (W.L.OK + v) = mem (W.L.OK + v) := by
  have hC := h.sc_ok (rs := rs) hp
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES
  have f := hC.fLO v hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hclr.2.2 _ (h.not_pqOut (Or.inl (by omega)))]; exact hI.fix _ f.2.2.2
  · rw [hclr.2.2 _ (h.not_pqOut (Or.inl (by omega)))]; exact hI.fix _ f.2.1
  · rw [hclr.2.2 _ (h.not_pqOut (Or.inl (by omega)))]; exact hI.fix _ f.1
  · rw [hclr.2.2 _ (h.not_pqOut (Or.inl (by omega)))]; exact hI.fix _ f.2.2.1

/-- The search leaves the cells below the heads and above the settled list alone. -/
theorem Ok.after_out (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) {a : SG} {memL memC : ℕ → ℕ}
    (hI : (W.sc mem t st hw lo rs).Inv w a memL) (hclr : (W.sc mem t st hw lo rs).SClr memL memC)
    {x : ℕ} (hx : x < W.L.HD ∨ W.SL + W.L.NN + 1 ≤ x) : memC x = mem x := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have := h.hR; have := h.hCTL; have := h.hSUM; have := h.hSL; have hES := h.lES
  rcases hx with hx | hx
  · rw [hclr.2.2 _ (h.not_pqOut (Or.inl (by omega)))]; exact hI.fix _ (h.fix hp (Or.inl hx))
  · rw [hclr.2.2 _ (h.not_pqOut (Or.inr (by omega)))]; exact hI.top x hx

/-- The counter, the settled list and the pointer after the search. -/
theorem Ok.after_ctl (h : W.Ok w mem) {a : SG} {memL memC : ℕ → ℕ}
    (hI : (W.sc mem t st hw lo rs).Inv w a memL) (hclr : (W.sc mem t st hw lo rs).SClr memL memC) :
    memC (W.CTL + 1) = a.ℓ.length ∧ memC (W.CTL + 2) = (W.Hl t st ++ [W.s]).getD a.j 0 ∧
      (∀ i < a.ℓ.length, memC (W.SL + i) = a.ℓ.getD i 0) := by
  have := h.hCTL; have := h.hSUM; have := h.hSL
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · rw [hclr.2.2 _ (h.not_pqOut (Or.inr (by omega)))]; exact hI.ns
  · rw [hclr.2.2 _ (h.not_pqOut (Or.inr (by omega)))]; exact hI.ptr
  · rw [hclr.2.2 _ (h.not_pqOut (Or.inr (by omega)))]; exact hI.sl i hi

/-- The settled nodes are allowed nodes, so there are at most `NN` of them. -/
theorem Ok.sett_lt (h : W.Ok w mem) {a : SG} {memL : ℕ → ℕ}
    (hI : (W.sc mem t st hw lo rs).Inv w a memL) {v : ℕ} (hv : v ∈ a.ℓ) :
    v ∈ W.Nodes mem ∧ v < W.s := by
  have hs := (hI.sett v).mpr hv
  have hn : v ∈ W.Nodes mem := ((hI.rep.sett v).mp hs).1
  exact ⟨hn, h.nodes_lt hn⟩

theorem Ok.sett_len (h : W.Ok w mem) {a : SG} {memL : ℕ → ℕ}
    (hI : (W.sc mem t st hw lo rs).Inv w a memL) : a.ℓ.length ≤ W.s := by
  have hsub : a.ℓ.toFinset ⊆ Finset.range W.s := fun v hv =>
    Finset.mem_range.mpr (h.sett_lt hI (List.mem_toFinset.mp hv)).2
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hI.nd, Finset.card_range] at this
  exact this

end PW

end MinCostFlow.LowStretch
