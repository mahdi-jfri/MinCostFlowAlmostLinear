module

public import MinCostFlow.LowStretch.ProgResetE
public import MinCostFlow.LowStretch.ProgSplitSpec

/-!
# The reset of child `k`: the precondition of the split walk

`rsP` calls `splitP` with the layout `CS.spL`: the arrays of the merge tree from the global block,
the work array at the end `drawEnd` of Dijkstra, the `θ`-nodes of child `k` at `NAK`, and the new
threshold `thrK k`. On any memory `M7` that agrees with `M6` below `OUTK + 2`, this layout meets
`SplitPre` for the ghost `(T, G, raw k, thrK k)` (`CS.splitPre_rs`).

The reasons: the arrays are read regions of the child step, so they are safe cells, which `MidOk`
keeps; the `θ`-nodes are at `NAK` by `MidOk.na`; the labels are the heads of the `θ`-nodes by
`lab6` and `lab_raw`; `SplitHyp` holds by `Cl.sat_raw` and `CS.thrK_le`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The layout of the split walk of child `k`. -/
noncomputable def spL (M1 : ℕ → ℕ) (k H : ℕ) : SplitL :=
  ⟨S.E.KCH1, S.E.KCH2, S.E.KMW, S.E.KSZ, S.E.KLO, S.E.ORDL, S.E.LAB, S.E.n,
    drawEnd (S.dwE M1 k H), S.NAK M1 H k, S.sNK M1 k, S.thrK k⟩

/-- The split walk of child `k` reads the `θ`-nodes of child `k`. -/
theorem spL_nodes (hmid : MidOk S M1 k H M M6) {M7 : ℕ → ℕ}
    (h7 : ∀ a, a < S.OUTK M1 H k + 2 → M7 a = M6 a) :
    (S.spL M1 k H).nodes M7 = S.nodesK M1 k := by
  apply List.ext_getElem
  · simp [SplitL.nodes, spL, length_nodesK]
  · intro i h1 h2
    have hi : i < S.sNK M1 k := by simpa [SplitL.nodes, spL] using h1
    simp only [SplitL.nodes, spL, List.getElem_map, List.getElem_range]
    rw [h7 _ (by unfold OUTK; omega), hmid.na i hi, List.getD_eq_getElem _ _ h2]

/-- **The precondition of the split walk of child `k`.** -/
theorem splitPre_rs (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k) {M7 : ℕ → ℕ} (h7 : ∀ a, a < S.OUTK M1 H k + 2 → M7 a = M6 a)
    (hroom : drawEnd (S.dwE M1 k H) + 3 * (S.sNK M1 k + S.T.N + 1) < 2 ^ w)
    (hxw : S.thrK k < 2 ^ w) :
    SplitPre w S.T S.G (S.raw k) (S.thrK k) (S.spL M1 k H) M7 := by
  have hθ : (S.raw k).θ = S.c.θ := Cl.raw_θ k
  have hle := hI.hle
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hHM := S.HM_le_H0
  have hO : H ≤ S.OUTK M1 H k := S.OUTK_ge M1 H k
  have hend : S.OUTK M1 H k + 2 ≤ drawEnd (S.dwE M1 k H) := by
    have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
        (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
    omega
  have hn : S.E.n = S.G.n := hpre.glob.n
  have hN : S.E.N = S.T.N := hpre.glob.N
  -- a cell of a read region keeps its value
  have keep : ∀ r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem, ∀ i < r.2,
      M7 (r.1 + i) = S.mem (r.1 + i) := fun r hr i hi => by
    have : r.1 + r.2 ≤ S.h := hpre.below r hr
    rw [h7 _ (by omega)]
    exact keep_safe hpre hT hI hk hmid (safe_reg hpre hr hi)
  have mR : ∀ {a b : ℕ}, (a, b) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem →
      a + b ≤ S.h ∧ RegDisj (a, b) (S.E.LAB, S.G.n) := fun hr =>
    ⟨hpre.below _ hr, hpre.lab_disj _ hr⟩
  have rCH1 : (S.E.KCH1, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have rCH2 : (S.E.KCH2, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have rMW : (S.E.KMW, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have rSZ : (S.E.KSZ, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have rLO : (S.E.KLO, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have rOR : (S.E.ORDL, S.E.n) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have lay : ∀ {Z : ℕ}, (Z, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem →
      (S.spL M1 k H).Lay S.T S.G Z := fun hr => by
    obtain ⟨h1, h2⟩ := mR hr
    unfold RegDisj at h2
    dsimp only at h1 h2
    simp only [SplitL.Lay, spL]
    omega
  have hglo := hpre.glob
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hpre' := pre_of hpre
  obtain ⟨hx1, hx4⟩ := thrK_le hpre hk hq
  refine ⟨⟨hpre.ok.tree, fun v hv => hpre.ok.n_of_mem (Cl.raw_X_subset k hv),
      by rw [hθ]; exact Cl.sat_raw hpre.ok k, hx1, by rw [hθ]; omega⟩, rfl, hn,
    fun j hj1 hj2 => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun v hv => ?_, ?_,
    fun j hj => ?_, fun v hv => ?_, fun v hv => ?_, lay rCH1, lay rCH2, lay rMW, lay rSZ, lay rLO,
    ?_, ?_, ?_, hroom, hxw⟩
  · simp only [spL]
    rw [keep _ rCH1 j (by dsimp only; omega), keep _ rCH2 j (by dsimp only; omega)]
    exact hglo.ch j hj1 hj2
  · simp only [spL]; rw [keep _ rMW j (by dsimp only; omega)]; exact hglo.mw j hj
  · simp only [spL]; rw [keep _ rSZ j (by dsimp only; omega)]; exact hglo.sz j hj
  · simp only [spL]; rw [keep _ rLO j (by dsimp only; omega)]; exact hglo.lo j hj
  · simp only [spL]
    have hlo : S.T.lo S.G v < S.G.n := KT.lo_lt hpre.ok.tree hv
    rw [keep _ rOR _ (by dsimp only; rw [hn]; exact hlo)]; exact hglo.ordl v hv
  · rw [spL_nodes hmid h7]; exact hpre'.nodesK_nodup k
  · rw [spL_nodes hmid h7] at hj
    obtain ⟨a, ha, he⟩ := (hpre'.nodesK_mem hT hk j).mp hj
    exact ⟨a, ha, by rw [hθ, he]⟩
  · rw [spL_nodes hmid h7, hθ]
    exact (hpre'.nodesK_mem hT hk _).mpr ⟨v, hv, rfl⟩
  · have hvn := hpre.ok.n_of_mem (Cl.raw_X_subset k hv)
    simp only [spL]
    rw [h7 _ (by omega), lab6 hpre hT hI hk hmid hvn, lab_raw hpre hT hI hk hv, hθ]
  · obtain ⟨h1, h2⟩ := mR rOR
    unfold RegDisj at h2
    dsimp only at h1 h2
    simp only [spL]
    omega
  · simp only [spL]; unfold OUTK at hend; omega
  · simp only [spL]; omega

end CS

end MinCostFlow.LowStretch
