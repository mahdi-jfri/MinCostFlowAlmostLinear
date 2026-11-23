module

public import MinCostFlow.LowStretch.ProgChildInv

/-!
# The record of a raw child in memory

After the highway, the stored pairs, the nodes and the record block of child `k` are written,
the memory holds what `MidOk` says. Then the record of raw child `k` is in memory (`CS.rawRecAt`):
the cells that the earlier children wrote are not read, since different pieces have different
vertices and different heads.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable (S : CS)

/-- The addresses of the stored pairs, the nodes and the two sums of child `k`. -/
noncomputable def SAK (H k : ℕ) : ℕ := H + 4 * S.ℓK k
noncomputable def NAK (M1 : ℕ → ℕ) (H k : ℕ) : ℕ := S.SAK H k + 2 * S.cntK M1 k
noncomputable def OUTK (M1 : ℕ → ℕ) (H k : ℕ) : ℕ := S.NAK M1 H k + S.sNK M1 k

/-- The entry `j` of the stored highway of raw child `k`. -/
noncomputable def hwK (k j : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (Cl.hwE S.G (S.raw k).t (S.raw k).hw (S.raw k).θ (S.raw k).half).getD j (0, 0, 0, 0)

/-- The record block of raw child `k`. -/
noncomputable def blkK (M1 : ℕ → ℕ) (H k : ℕ) : RecL :=
  ⟨S.sNK M1 k, S.cntK M1 k, S.SAK H k, S.L.lθ, S.NAK M1 H k, S.mem (S.X.CC + k),
    S.mem (S.X.CT + k), S.ℓK k, H⟩

end CS

/-- **The memory after the record of raw child `k` is written**, from the memory `M` at the start
of child `k` to `M6`. -/
structure MidOk (S : CS) (M1 : ℕ → ℕ) (k H : ℕ) (M M6 : ℕ → ℕ) : Prop where
  hw : ∀ j < S.ℓK k, M6 (H + 4 * j) = (S.hwK k j).1 ∧ M6 (H + 4 * j + 1) = (S.hwK k j).2.1 ∧
    M6 (H + 4 * j + 2) = (S.hwK k j).2.2.1 ∧ M6 (H + 4 * j + 3) = (S.hwK k j).2.2.2
  hm : ∀ u ∈ S.walk k, M6 (S.HM + u) = S.rgK k
  pr : ∀ j < S.cntK M1 k, M6 (S.SAK H k + 2 * j) = ((S.SK M1 k).getD j (0, 0)).1 ∧
    M6 (S.SAK H k + 2 * j + 1) = ((S.SK M1 k).getD j (0, 0)).2
  na : ∀ i < S.sNK M1 k, M6 (S.NAK M1 H k + i) = (S.nodesK M1 k).getD i 0
  loc : ∀ i < S.sNK M1 k, M6 (S.E.LOC + S.T.hd S.G ((S.nodesK M1 k).getD i 0)) = i
  blk : RecL.read M6 (S.h + 9 * k) = S.blkK M1 H k
  out1 : M6 (S.OUTK M1 H k) = (S.raw k).X.card
  out2 : M6 (S.OUTK M1 H k + 1) = (S.raw k).X.sup (fun a => S.T.mw (S.T.top S.c.θ a))
  frame : ∀ a, ¬ (H ≤ a ∧ a < S.OUTK M1 H k + 2) → ¬ (S.h + 9 * k ≤ a ∧ a < S.h + 9 * k + 9) →
    (∀ u ∈ S.walk k, a ≠ S.HM + u) →
    (∀ i < S.sNK M1 k, a ≠ S.E.LOC + S.T.hd S.G ((S.nodesK M1 k).getD i 0)) → M6 a = M a

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

theorem h_le_HM : S.h + 9 * S.nch ≤ S.HM := by
  unfold HM ORDK CNTK OFFK KEY ORDN CNTN OFFN CHX; omega

theorem HM_le_H0 : S.HM + S.s ≤ S.H0 := by unfold H0; omega

theorem Pre.nodesK_mem (h : Pre S) (hT : TopOk S M1) {k : ℕ} (hk : k < S.nch) (j : ℕ) :
    j ∈ S.nodesK M1 k ↔ ∃ a ∈ (S.raw k).X, S.T.top S.c.θ a = j := by
  have hc1 := chxF_one hT h.nd_lt
  have hc0 := chxF_zero (M := M1) hT
  unfold nodesK; rw [h.s]; exact h.ok.mem_chxNodes h.pet hc1 hc0 hk j

theorem Pre.nodesK_nodup (h : Pre S) (k : ℕ) : (S.nodesK M1 k).Nodup := by
  unfold nodesK; rw [h.s]; exact h.ok.chxNodes_nodup _ k

theorem length_nodesK (k : ℕ) : (S.nodesK M1 k).length = S.sNK M1 k := by
  simp [nodesK, sNK]

theorem length_SK (k : ℕ) : (S.SK M1 k).length = S.cntK M1 k := by
  simp [SK, cntK]

/-- A safe cell keeps its value at the call. -/
theorem keep_safe (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    {a : ℕ} (ha : S.Safe a) : M6 a = S.mem a := by
  have h1 := ha.1
  have h2 := ha.2.2
  have hH := hI.hle
  have hb := S.h_le_HM
  have hb2 := S.HM_le_H0
  have hkn : 9 * k + 9 ≤ 9 * S.nch := by omega
  rw [hmid.frame a (by omega) (by omega) (fun u _ => by omega) (fun i _ => ?_),
    hI.frame a (ha.not_wr hpre k H), hT.low a h1]
  intro he
  have hN := hpre.ok.tree.n_lt
  have hnd : (S.nodesK M1 k).getD i 0 < S.T.N := by
    have hi : i < (S.nodesK M1 k).length := by rw [length_nodesK]; assumption
    rw [List.getD_eq_getElem _ _ hi]
    obtain ⟨b, hb, he⟩ := ((Pre.mk hpre.two hpre.ok hpre.dec hpre.pet hpre.recAt.arcs.s).nodesK_mem
      hT hk _).mp (List.getElem_mem hi)
    rw [← he]
    exact KT.top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k hb)) hpre.ok.inv.one_le
  have := (KT.hd_under hpre.ok.tree _ hnd).lt_N hpre.ok.tree hnd
  rcases h2 with h2 | h2 <;> omega

end CS

end MinCostFlow.LowStretch
