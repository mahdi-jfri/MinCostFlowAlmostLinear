module

public import MinCostFlow.LowStretch.ProgChildOnePc

/-!
# One child: the nodes

The third call of `oneP` writes the nodes of child `k` and their new local indices (`ncP`): node
`i` of the child is node `i` of its node group, and its head gets local index `i`. This file proves
the precondition of `ncP` (`CS.ncOk`); the heads are distinct since distinct `θ`-nodes have
distinct heads (`CS.top_hd_inj`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

/-- Distinct `x`-nodes have distinct heads. -/
theorem top_hd_inj {T : KT} {G : PG} (h : T.Ok G) {x a b : ℕ} (ha : a < G.n) (hb : b < G.n)
    (hx : 1 ≤ x) (he : T.hd G (T.top x a) = T.hd G (T.top x b)) : T.top x a = T.top x b := by
  have hN := h.n_lt
  have ta := isTop_top h ha hx
  have tb := isTop_top h hb hx
  have haN : T.top x a < T.N := ta.1.lt_N h (by omega)
  have hbN : T.top x b < T.N := tb.1.lt_N h (by omega)
  rcases hd_eq h haN hbN he with hu | hu
  · exact IsTop.unique h (by omega) ta (IsTop.of_common h (by omega) tb tb.1 (ta.1.trans hu) tb.2.1)
  · exact (IsTop.unique h (by omega) tb
      (IsTop.of_common h (by omega) ta ta.1 (tb.1.trans hu) ta.2.1)).symm

namespace CS

variable {S : CS} {w : ℕ} {M1 M M2 M3 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- **What `ncP` reads for entry `i`.** -/
theorem nc_reads (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2)
    (hd2 : ((S.oneV M1 k H).pcE (S.ℓK k) M2).Done (S.cntK M1 k) M3) {i : ℕ}
    (hi : i < S.sNK M1 k) :
    M3 (S.ORDN + offOf (S.chxF M1) S.s k + i) = (grp (S.chxF M1) S.s k).getD i 0 ∧
    ((S.oneV M1 k H).ncE (S.ℓK k) M3).x i = (S.nodesK M1 k).getD i 0 ∧
      ((S.oneV M1 k H).ncE (S.ℓK k) M3).hd i = S.T.hd S.G ((S.nodesK M1 k).getD i 0) := by
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have k3 : ∀ {a}, a < S.HM → M3 a = M a := fun {a} ha => by
    rw [hd2.2 a (Or.inl (by show a < H + 4 * S.ℓK k; omega))]; exact keepM2 hd hle ha
  have kS := fun {a} (ha : S.Safe a) => keepM_safe hT hpre hI ha
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hi' : i < (grp (S.chxF M1) S.s k).length := hi
  have hu : (grp (S.chxF M1) S.s k).getD i 0 < S.s := by
    have := getD_mem_of_lt hi' 0
    simp only [grp, List.mem_filter, List.mem_range] at this; exact this.1
  have hoff := offOf_succ (f := S.chxF M1) S.s k
  have hle' := offOf_le' (S.chxF M1) S.s (k + 1)
  have e1 : M3 (S.ORDN + offOf (S.chxF M1) S.s k + i) = (grp (S.chxF M1) S.s k).getD i 0 := by
    have a1 : S.CHX ≤ S.ORDN := by unfold ORDN CNTN OFFN; omega
    have a2 : S.ORDN + S.s ≤ S.HM := by unfold HM ORDK CNTK OFFK KEY; omega
    rw [k3 (by omega), keepM_top hpre hI hk.le (by omega) (by omega), hT.ordN k hk i hi']
  have hNA : (S.L.NA, S.L.s) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, RecL.regs]
  have bN := hpre.below _ hNA
  dsimp only at bN
  have hs : S.s = S.L.s := rfl
  have hns : S.s = S.R.nodes.length := (pre_of hpre).s
  have e2 : M3 (S.L.NA + (grp (S.chxF M1) S.s k).getD i 0) = (S.nodesK M1 k).getD i 0 := by
    have hun : (grp (S.chxF M1) S.s k).getD i 0 < S.R.nodes.length := by omega
    rw [k3 (by omega), show M (S.L.NA + (grp (S.chxF M1) S.s k).getD i 0) = _ from
      kS (safe_reg hpre hNA (i := (grp (S.chxF M1) S.s k).getD i 0) (by omega)),
      show S.mem (S.L.NA + (grp (S.chxF M1) S.s k).getD i 0) = _ from
      hpre.recAt.nodes _ hun]
    rw [List.getD_eq_getElem (S.nodesK M1 k) 0 (by rw [length_nodesK]; exact hi)]
    unfold nodesK
    rw [List.getElem_map, ← List.getD_eq_getElem _ 0 hi']
  have hx : ((S.oneV M1 k H).ncE (S.ℓK k) M3).x i = (S.nodesK M1 k).getD i 0 := by
    show M3 (S.L.NA + M3 (S.ORDN + offOf (S.chxF M1) S.s k + i)) = _
    rw [e1, e2]
  refine ⟨e1, hx, ?_⟩
  show M3 (S.E.HEAD + _) = _
  rw [hx]
  obtain ⟨a, ha, he⟩ := nodesK_getD hpre hT hk hi
  have hN : (S.nodesK M1 k).getD i 0 < S.T.N := by
    rw [← he]
    exact KT.top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha)) hpre.ok.inv.one_le
  have hHD : (S.E.HEAD, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have bH := hpre.below _ hHD
  dsimp only at bH
  have hEN : S.E.N = S.T.N := hG.N
  rw [k3 (by omega), kS (safe_reg hpre hHD (i := (S.nodesK M1 k).getD i 0) (by omega))]
  exact hG.hd _ hN

/-- **The precondition of `ncP`** at child `k`, after `hwWalkP` and `pcP`. -/
theorem ncOk (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2)
    (hd2 : ((S.oneV M1 k H).pcE (S.ℓK k) M2).Done (S.cntK M1 k) M3)
    (hroom : S.NAK M1 H k + S.sNK M1 k + 1 < 2 ^ w) :
    ((S.oneV M1 k H).ncE (S.ℓK k) M3).Ok w S.T.N := by
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hEN : S.E.N = S.T.N := hG.N
  have hNA : (S.L.NA, S.L.s) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, RecL.regs]
  have hHD : (S.E.HEAD, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have bN : S.L.NA + S.L.s ≤ S.h := hpre.below _ hNA
  have bH : S.E.HEAD + S.E.N ≤ S.h := hpre.below _ hHD
  have dN : RegDisj (S.L.NA, S.L.s) (S.E.LOC, S.T.N) := hpre.loc_disj _ hNA
  have dH : RegDisj (S.E.HEAD, S.E.N) (S.E.LOC, S.T.N) := hpre.loc_disj _ hHD
  unfold RegDisj at dN dH
  dsimp only at bN bH dN dH
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hs : S.s = S.L.s := rfl
  have hNAK : S.NAK M1 H k = H + 4 * S.ℓK k + 2 * S.cntK M1 k := rfl
  have hoff := offOf_succ (f := S.chxF M1) S.s k
  have hle' := offOf_le' (S.chxF M1) S.s (k + 1)
  have a2 : S.ORDN + S.s ≤ S.HM := by unfold HM ORDK CNTK OFFK KEY; omega
  have hnd : ∀ i < S.sNK M1 k, (S.nodesK M1 k).getD i 0 < S.T.N := fun i hi => by
    obtain ⟨a, ha, he⟩ := nodesK_getD hpre hT hk hi
    rw [← he]
    exact KT.top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha)) hpre.ok.inv.one_le
  refine ⟨fun i hi => ?_, fun i hi j hj he => ?_, show S.E.LOC + S.T.N ≤ S.NAK M1 H k by omega,
    hroom⟩
  · have hi : i < S.sNK M1 k := hi
    obtain ⟨e1, hx, hhd⟩ := nc_reads hpre hT hI hk hd hd2 hi
    have hi' : i < (grp (S.chxF M1) S.s k).length := hi
    have hu : (grp (S.chxF M1) S.s k).getD i 0 < S.s := by
      have := getD_mem_of_lt hi' 0
      simp only [grp, List.mem_filter, List.mem_range] at this; exact this.1
    have hxN := hnd i hi
    have hdN := (KT.hd_under hpre.ok.tree _ hxN).lt_N hpre.ok.tree hxN
    have hdN' : ((S.oneV M1 k H).ncE (S.ℓK k) M3).hd i < S.T.N := by rw [hhd]; exact hdN
    have hx' : ((S.oneV M1 k H).ncE (S.ℓK k) M3).x i < S.T.N := by rw [hx]; exact hxN
    change (S.ORDN + offOf (S.chxF M1) S.s k + i < S.NAK M1 H k ∧
        (S.ORDN + offOf (S.chxF M1) S.s k + i < S.E.LOC ∨
          S.E.LOC + S.T.N ≤ S.ORDN + offOf (S.chxF M1) S.s k + i)) ∧
      (S.L.NA + M3 (S.ORDN + offOf (S.chxF M1) S.s k + i) < S.NAK M1 H k ∧
        (S.L.NA + M3 (S.ORDN + offOf (S.chxF M1) S.s k + i) < S.E.LOC ∨
          S.E.LOC + S.T.N ≤ S.L.NA + M3 (S.ORDN + offOf (S.chxF M1) S.s k + i))) ∧
      (S.E.HEAD + ((S.oneV M1 k H).ncE (S.ℓK k) M3).x i < S.NAK M1 H k ∧
        (S.E.HEAD + ((S.oneV M1 k H).ncE (S.ℓK k) M3).x i < S.E.LOC ∨
          S.E.LOC + S.T.N ≤ S.E.HEAD + ((S.oneV M1 k H).ncE (S.ℓK k) M3).x i)) ∧
      ((S.oneV M1 k H).ncE (S.ℓK k) M3).hd i < S.T.N
    rw [e1]
    rw [hx]
    have a3 : S.h ≤ S.ORDN := by unfold ORDN CNTN OFFN CHX; omega
    have bH' : S.E.HEAD + S.T.N ≤ S.h := by omega
    have dH' : S.E.HEAD + S.T.N ≤ S.E.LOC ∨ S.E.LOC + S.T.N ≤ S.E.HEAD := by omega
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hdN'⟩
  · have hi : i < S.sNK M1 k := hi
    have hj : j < S.sNK M1 k := hj
    obtain ⟨-, -, h1⟩ := nc_reads hpre hT hI hk hd hd2 hi
    obtain ⟨-, -, h2⟩ := nc_reads hpre hT hI hk hd hd2 hj
    rw [h1, h2] at he
    obtain ⟨a, ha, ea⟩ := nodesK_getD hpre hT hk hi
    obtain ⟨b, hb, eb⟩ := nodesK_getD hpre hT hk hj
    rw [← ea, ← eb] at he
    have := top_hd_inj hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha))
      (hpre.ok.n_of_mem (Cl.raw_X_subset k hb)) hpre.ok.inv.one_le he
    rw [ea, eb] at this
    have hl : (S.nodesK M1 k).length = S.sNK M1 k := length_nodesK k
    rw [List.getD_eq_getElem (S.nodesK M1 k) 0 (by omega),
      List.getD_eq_getElem (S.nodesK M1 k) 0 (by omega)] at this
    exact ((pre_of hpre).nodesK_nodup k).getElem_inj_iff.mp this

end CS

end MinCostFlow.LowStretch
