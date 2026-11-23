module

public import MinCostFlow.LowStretch.ProgResetN

/-!
# The reset of child `k`: labels and local indices after `ncP`

After `ncP` of the reset, a vertex `a` of child `k` has the label `hd (top x a)` (the split walk
wrote it, `SplitPost` part 6), and that head has a local index below `n = sN + v`: the node
`top x a` is entry `i` of column `1`, and `ncP` gives its head the local index `i`
(`CS.RsNc.lab_loc`). These are the facts that `pcP` needs to read the ends of the stored pairs.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}
  {M7 M8 M9 M10 : ℕ → ℕ} {v : ℕ}

/-- **The label and the local index of a vertex of child `k` after `ncP`.** -/
theorem RsNc.lab_loc (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k) (hR : RsNc w S M1 k H M6 M7 M8 M9 M10 v) {a : ℕ}
    (ha : a ∈ (S.raw k).X) :
    M10 (S.E.LAB + a) = S.T.hd S.G (S.T.top (S.thrK k) a) ∧
      M10 (S.E.LOC + S.T.hd S.G (S.T.top (S.thrK k) a)) < S.sNK M1 k + v := by
  have han := hpre.ok.n_of_mem (Cl.raw_X_subset k ha)
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hll : RegDisj (S.E.LAB, S.G.n) (S.E.LOC, S.T.N) := hpre.lab_loc
  unfold RegDisj at hll
  dsimp only at hll
  have hA : S.h ≤ drawEnd (S.dwE M1 k H) := by
    have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
        (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
    have := S.OUTK_ge M1 H k
    have := S.h_le_HM
    have := S.HM_le_H0
    have := hI.hle
    omega
  set A := drawEnd (S.dwE M1 k H) with hAe
  set n := S.sNK M1 k + v with hn
  have hx1 := (thrK_le hpre hk hq).1
  have hN := hpre.ok.tree.n_lt
  obtain ⟨-, -, -, hcol, -, hlab6, -, -, -⟩ := hR.sp
  -- the label
  have hl : M10 (S.E.LAB + a) = S.T.hd S.G (S.T.top (S.thrK k) a) := by
    rw [hR.nc.2.2 _ (fun hout => by
      rcases hout with ⟨h1, -⟩ | ⟨i, hi, he⟩
      · simp only [rsNcE] at h1; omega
      · have := (hR.ok.rd i hi).2.2.2
        simp only [rsNcE] at he this; omega)]
    show M9 _ = _
    rw [hR.io.2 _ (Or.inl (by omega))]
    exact hlab6 a ha
  refine ⟨hl, ?_⟩
  -- the node of `a` is entry `i` of column `1`
  obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp ((hcol (S.T.top (S.thrK k) a)).mpr ⟨a, ha, rfl⟩)
  have hi' : i < n := by rw [rdS_length] at hi; exact hi
  have e8 : M8 (A + 3 * i + 1) = S.T.top (S.thrK k) a := by rw [← hie]; simp [rdS, spL, hAe]
  have hxN : S.T.top (S.thrK k) a < S.T.N := top_lt_N hpre.ok.tree han hx1
  have hx : (rsNcE A n S.E.HEAD S.E.LOC M9).x i = S.T.top (S.thrK k) a := by
    show M9 (A + M9 (A + 3 * n + i)) = _
    rw [hR.io.1 i hi', show A + (3 * i + 1) = A + 3 * i + 1 by omega,
      hR.io.2 _ (Or.inl (by omega)), e8]
  -- the head array after `iotaP`
  have hHD : (S.E.HEAD, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have bH : S.E.HEAD + S.E.N ≤ S.h := hpre.below _ hHD
  have dH : RegDisj (S.E.HEAD, S.E.N) (S.E.LOC, S.T.N) := hpre.loc_disj _ hHD
  unfold RegDisj at dH
  dsimp only at bH dH
  have hEN : S.E.N = S.T.N := hpre.glob.N
  have hhd : M9 (S.E.HEAD + S.T.top (S.thrK k) a) = S.T.hd S.G (S.T.top (S.thrK k) a) := by
    have k10 := hR.keep hpre hT hI hk hmid hHD (i := S.T.top (S.thrK k) a) (by dsimp only; omega)
    rw [hR.nc.2.2 _ (fun hout => by
      rcases hout with ⟨h1, -⟩ | ⟨j, hj, he⟩
      · simp only [rsNcE] at h1; omega
      · have := (hR.ok.rd j hj).2.2.2
        simp only [rsNcE] at he this; omega)] at k10
    rw [show M9 _ = _ from k10]
    exact hpre.glob.hd _ hxN
  have hd : (rsNcE A n S.E.HEAD S.E.LOC M9).hd i = S.T.hd S.G (S.T.top (S.thrK k) a) := by
    show M9 (S.E.HEAD + _) = _
    rw [hx, hhd]
  have h2 : M10 (S.E.LOC + (rsNcE A n S.E.HEAD S.E.LOC M9).hd i) = i := hR.nc.2.1 i hi'
  rw [← hd, h2]; exact hi'

/-- Entry `j` of the key group of child `k` after `ncP`. -/
theorem RsNc.pc_it (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hR : RsNc w S M1 k H M6 M7 M8 M9 M10 v) {j : ℕ} (hj : j < S.cntK M1 k) :
    M10 (S.ORDK + offOf (S.keyF M1) S.nA k + j) = S.keyAt M1 k j := by
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hO : H ≤ S.OUTK M1 H k := S.OUTK_ge M1 H k
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hoff := offOf_succ (f := S.keyF M1) S.nA k
  have hle' := offOf_le' (S.keyF M1) S.nA (k + 1)
  have a1 : S.CHX ≤ S.ORDK := by unfold ORDK CNTK OFFK KEY ORDN CNTN OFFN; omega
  have a2 : S.HM = S.ORDK + S.nA := rfl
  have a3 : S.h + 9 * S.nch ≤ S.CHX := by unfold CHX; omega
  have hj' : j < (grp (S.keyF M1) S.nA k).length := hj
  have e1 : M10 (S.ORDK + offOf (S.keyF M1) S.nA k + j) = S.keyAt M1 k j := by
    rw [rsKeep10 hR.h7 hR.sp hR.io hR.ok hR.nc (by omega) (fun b hb => by
        have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb); omega) (by omega),
      hmid.frame _ (by omega) (by omega) (fun u _ => by omega) (fun i hi => by
        have := hd_nodesK_lt hpre hT hk hi; omega),
      keepM_top hpre hI hk.le (by omega) (by omega), hT.ordK k (by omega) j hj']
    rfl
  exact e1

set_option maxHeartbeats 1000000 in
/-- **The precondition of `pcP` in the reset**, on the memory `M10` after `ncP`. Entry `j` reads
key `keyAt k j` of the key group of child `k`, its active pair and the new local indices of its
ends, which are below `n`; so every read lies below `SA = A + 5 n`. -/
theorem RsNc.pcOk (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k) (hR : RsNc w S M1 k H M6 M7 M8 M9 M10 v)
    (hroom : drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) + 2 * S.cntK M1 k + 1 < 2 ^ w) :
    ((S.rsV M1 k H).rsPcE (S.sNK M1 k + v) M10).Ok w := by
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hO : H ≤ S.OUTK M1 H k := S.OUTK_ge M1 H k
  have hend : S.OUTK M1 H k + 2 ≤ drawEnd (S.dwE M1 k H) := by
    have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
        (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
    omega
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hACT : (S.X.ACT, 2 * S.X.nA) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have hIN : (S.E.IN, 3 * S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have hPP : (S.X.PP, S.L.s) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have bA : S.X.ACT + 2 * S.X.nA ≤ S.h := hpre.below _ hACT
  have bI : S.E.IN + 3 * S.E.m ≤ S.h := hpre.below _ hIN
  have bP : S.X.PP + S.L.s ≤ S.h := hpre.below _ hPP
  have hnA : S.nA = S.X.nA := rfl
  have hm : S.E.m = S.G.m := hG.m
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hN := hpre.ok.tree.n_lt
  have hll : RegDisj (S.E.LAB, S.G.n) (S.E.LOC, S.T.N) := hpre.lab_loc
  unfold RegDisj at hll
  dsimp only at hll
  refine ⟨fun j hj => ?_, fun j hj => ?_, by show 0 < 2 ^ w; omega, hroom⟩
  · have hj : j < S.cntK M1 k := hj
    obtain ⟨hiA, hact, hu, hv⟩ := key_ends hpre hT hk (keyAt_mem hj)
    have hpm : S.actP (S.keyAt M1 k j) < S.G.m := (Cl.mem_act.mp hact).1
    have hun := hpre.ok.n_of_mem (Cl.raw_X_subset k hu)
    have hvn := hpre.ok.n_of_mem (Cl.raw_X_subset k hv)
    -- the entry, in the key group of child `k`
    have hoff := offOf_succ (f := S.keyF M1) S.nA k
    have hle' := offOf_le' (S.keyF M1) S.nA (k + 1)
    have a2 : S.HM = S.ORDK + S.nA := rfl
    have hj' : j < (grp (S.keyF M1) S.nA k).length := hj
    have e1 := hR.pc_it hpre hT hI hk hmid hj
    have e2 : M10 (S.X.ACT + 2 * S.keyAt M1 k j) = S.actP (S.keyAt M1 k j) :=
      hR.keep hpre hT hI hk hmid hACT (i := 2 * S.keyAt M1 k j) (by dsimp only; omega)
    have e4 : M10 (S.E.IN + 3 * S.actP (S.keyAt M1 k j)) = S.G.pu (S.actP (S.keyAt M1 k j)) := by
      rw [hR.keep hpre hT hI hk hmid hIN (i := 3 * S.actP (S.keyAt M1 k j)) (by dsimp only; omega)]
      exact (hG.ends _ hpm).1
    have e5 : M10 (S.E.IN + 3 * S.actP (S.keyAt M1 k j) + 1) =
        S.G.pv (S.actP (S.keyAt M1 k j)) := by
      rw [add_assoc,
        hR.keep hpre hT hI hk hmid hIN (i := 3 * S.actP (S.keyAt M1 k j) + 1) (by dsimp only; omega),
        ← add_assoc]
      exact (hG.ends _ hpm).2
    obtain ⟨l1, n1⟩ := hR.lab_loc hpre hT hI hk hmid hq hu
    obtain ⟨l2, n2⟩ := hR.lab_loc hpre hT hI hk hmid hq hv
    have hx1 := (thrK_le hpre hk hq).1
    have d1 := (KT.hd_under hpre.ok.tree _ (top_lt_N hpre.ok.tree hun hx1)).lt_N hpre.ok.tree
      (top_lt_N hpre.ok.tree hun hx1)
    have d2 := (KT.hd_under hpre.ok.tree _ (top_lt_N hpre.ok.tree hvn hx1)).lt_N hpre.ok.tree
      (top_lt_N hpre.ok.tree hvn hx1)
    have hs : S.s = S.L.s := rfl
    simp only [RsV.rsPcE, rsV, PCE.it, PCE.pr, PCE.eu, PCE.ev, PCE.na, PCE.nb]
    rw [e1, e2, e4, e5, l1, l2]
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega⟩
  · have hj : j < S.cntK M1 k := hj
    obtain ⟨hiA, -, -, -⟩ := key_ends hpre hT hk (keyAt_mem hj)
    have e1 := hR.pc_it hpre hT hI hk hmid hj
    have e3 : M10 (S.X.ACT + 2 * S.keyAt M1 k j + 1) = S.actF (S.keyAt M1 k j) := by
      rw [add_assoc]
      exact hR.keep hpre hT hI hk hmid hACT (i := 2 * S.keyAt M1 k j + 1) (by dsimp only; omega)
    have hfl' : S.actF (S.keyAt M1 k j) =
        if S.actP (S.keyAt M1 k j) ∈ S.c.half then 1 else 0 := hpre.pet.act_fl _ hiA
    simp only [RsV.rsPcE, rsV, PCE.fl, PCE.it]
    rw [e1, e3, hfl']
    split_ifs <;> omega

/-- **The split nodes and the pairs grouped at them fit in `visK k`.** -/
theorem rs_vis_le (hq : S.resetQ k)
    (hsp : SplitPost S.T S.G (S.raw k) (S.thrK k) (S.spL M1 k H) M7 v M8 0) :
    v + ∑ u ∈ S.T.splitSet S.G (S.raw k) (S.thrK k), S.T.nLca S.G u ≤ S.visK k := by
  have hcs : S.csOf k = (S.raw k).reset (S.thrK k) := by unfold csOf; rw [if_pos hq]
  have hv : (S.T.splitSet S.G (S.raw k) (S.thrK k)).card = v := by
    rw [← hsp.1, List.toFinset_card_of_nodup hsp.2.1, rdS_length]
  unfold visK KT.visW
  rw [hcs]
  show _ ≤ ∑ u ∈ S.T.splitSet S.G (S.raw k) (S.thrK k), _
  rw [← hv, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun u _ => by omega

/-- **The room of the reset.** Everything that the reset writes, `v` split nodes and `g` grouped
pairs with `v + g ≤ visK k`, lies below `H + spaceK k`. -/
theorem rs_room (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) (hroom : H + S.spaceK M1 k + 2 < 2 ^ w) {v g : ℕ}
    (hg : v + g ≤ S.visK k) :
    drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) + 2 * (S.cntK M1 k + g) + 2 < 2 ^ w := by
  have hℓ := ℓK_le hpre hT hk
  have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
      (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
  have hO : S.OUTK M1 H k = H + 4 * S.ℓK k + 2 * S.cntK M1 k + S.sNK M1 k := rfl
  set a := S.cntK M1 k + S.sNK M1 k + 1
  have h1 : S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1) ≤ S.E.J * (2 * a) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : S.E.J ≤ S.E.J * a := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : S.spaceK M1 k = 50 * (S.E.J * a) + 50 * a + 10 * (S.E.J * S.visK k) + 10 * S.visK k := by
    unfold spaceK; ring
  have e3 : 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1) =
    2 * (S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) := by ring
  have e4 : S.E.J * (2 * a) = 2 * (S.E.J * a) := by ring
  omega

/-- A reset child has at least one node. -/
theorem sNK_pos (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) (hq : S.resetQ k) : 1 ≤ S.sNK M1 k := by
  obtain ⟨a, ha⟩ : (S.raw k).X.Nonempty := Finset.card_pos.mp (by have := hq.1; omega)
  have hm := ((pre_of hpre).nodesK_mem hT hk (S.T.top S.c.θ a)).mpr ⟨a, ha, rfl⟩
  rw [← length_nodesK k]
  exact List.length_pos_of_mem hm

end CS

end MinCostFlow.LowStretch
