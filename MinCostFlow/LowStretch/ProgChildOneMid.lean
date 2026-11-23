module

public import MinCostFlow.LowStretch.ProgChildOneSm
public import MinCostFlow.LowStretch.ProgChildDelta

/-!
# One child: the memory after the record

After the four calls of `oneP` and the record block, the memory meets `MidOk` (`CS.midOk_of_done`).
Each field comes from the `Done` fact of the call that writes it, and the later calls keep it,
since they write other cells. This file also gathers the preconditions of the four calls into
`OneV.CallsOk` (`CS.callsOk`), from one word bound on the end of the arrays of child `k`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable {S : CS} {w : ℕ} {M1 M M2 M3 M4 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The memory after the two sums are stored. -/
noncomputable def memM6 (S : CS) (M1 : ℕ → ℕ) (k H : ℕ) (M4 : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update ((S.oneV M1 k H).putBlk (S.ℓK k) M4) ((S.oneV M1 k H).OUT (S.ℓK k))
    (((S.oneV M1 k H).smE (S.ℓK k) ((S.oneV M1 k H).putBlk (S.ℓK k) M4)).sum (S.oneV M1 k H).sN))
    ((S.oneV M1 k H).OUT (S.ℓK k) + 1)
    (((S.oneV M1 k H).smE (S.ℓK k) ((S.oneV M1 k H).putBlk (S.ℓK k) M4)).mx (S.oneV M1 k H).sN)

/-- A head of a node of child `k` lies in the local index array. -/
theorem hd_nodesK_lt (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) {i : ℕ} (hi : i < S.sNK M1 k) :
    S.T.hd S.G ((S.nodesK M1 k).getD i 0) < S.T.N := by
  obtain ⟨a, ha, ea⟩ := nodesK_getD hpre hT hk hi
  have hxN : (S.nodesK M1 k).getD i 0 < S.T.N := by
    rw [← ea]
    exact KT.top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha)) hpre.ok.inv.one_le
  exact (KT.hd_under hpre.ok.tree _ hxN).lt_N hpre.ok.tree hxN

/-- **The memory after the record of child `k`** meets `MidOk`. -/
theorem midOk_of_done (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2)
    (hd2 : ((S.oneV M1 k H).pcE (S.ℓK k) M2).Done (S.cntK M1 k) M3)
    (hd3 : ((S.oneV M1 k H).ncE (S.ℓK k) M3).Done (S.sNK M1 k) M4) :
    MidOk S M1 k H M (S.memM6 M1 k H M4) := by
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hOUT : (S.oneV M1 k H).OUT (S.ℓK k) = S.OUTK M1 H k := rfl
  have hOUT' : S.OUTK M1 H k = H + 4 * S.ℓK k + 2 * S.cntK M1 k + S.sNK M1 k := rfl
  have hBK : (S.oneV M1 k H).BK = S.h + 9 * k := rfl
  have hNAO : ((S.oneV M1 k H).ncE (S.ℓK k) M3).NAO = S.NAK M1 H k := rfl
  have hLOC : ((S.oneV M1 k H).ncE (S.ℓK k) M3).LOC = S.E.LOC := rfl
  have hSA : ((S.oneV M1 k H).pcE (S.ℓK k) M2).SA = S.SAK H k := rfl
  have hNAK : S.NAK M1 H k = H + 4 * S.ℓK k + 2 * S.cntK M1 k := rfl
  have hSAK : S.SAK H k = H + 4 * S.ℓK k := rfl
  -- From `M6` back to `M4`, away from the two sums and the record block.
  have b6 : ∀ a, a < S.OUTK M1 H k → ¬ (S.h + 9 * k ≤ a ∧ a < S.h + 9 * k + 9) →
      S.memM6 M1 k H M4 a = M4 a := fun a ha hb => by
    simp only [memM6, Function.update_apply, OneV.putBlk, hOUT, hBK]
    split_ifs <;> omega
  -- From `M4` back to `M3`, away from the nodes and the new local indices.
  have b4 : ∀ a, a < S.NAK M1 H k →
      (∀ i < S.sNK M1 k, a ≠ S.E.LOC + S.T.hd S.G ((S.nodesK M1 k).getD i 0)) → M4 a = M3 a :=
    fun a ha hn => by
      refine hd3.2.2 a ?_
      rintro (⟨h1, -⟩ | ⟨i, hi, he⟩)
      · rw [hNAO] at h1; omega
      · rw [hLOC, (nc_reads hpre hT hI hk hd hd2 hi).2.2] at he
        exact hn i hi he
  have nb : ∀ a, S.h ≤ a → ∀ i < S.sNK M1 k,
      a ≠ S.E.LOC + S.T.hd S.G ((S.nodesK M1 k).getD i 0) := fun a ha i hi => by
    have := hd_nodesK_lt hpre hT hk hi
    omega
  -- From `M3` back to `M2`, away from the stored pairs.
  have b3 : ∀ a, (a < S.SAK H k ∨ S.SAK H k + 2 * S.cntK M1 k ≤ a) → M3 a = M2 a := fun a ha => by
    rw [hd2.2 a (by rw [hSA]; exact ha)]; rfl
  have hwalk : ∀ i < S.ℓK k, ((S.oneV M1 k H).hwE M).nd i ∈ S.walk k := fun i hi => by
    rw [nd_eq hpre hT hI hk hi.le]
    exact mem_parWalk.mpr ⟨i, hi, rfl⟩
  have hblk : ∀ i < 9, S.memM6 M1 k H M4 (S.h + 9 * k + i) = ((S.oneV M1 k H).blk (S.ℓK k)).getD i 0 :=
    fun i hi => by
      simp only [memM6, Function.update_apply, OneV.putBlk, hOUT, hBK]
      split_ifs <;> first | omega | (congr 1; omega)
  refine ⟨fun j hj => ?_, fun u hu => ?_, fun j hj => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_,
    fun a h1 h2 h3 h4 => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := hw_of_done hpre hT hI hk hd j hj
    have e : ∀ x < 4, S.memM6 M1 k H M4 (H + 4 * j + x) = M2 (H + 4 * j + x) := fun x hx => by
      rw [b6 _ (by omega) (by omega), b4 _ (by omega) (nb _ (by omega)), b3 _ (Or.inl (by omega))]
    exact ⟨(e 0 (by omega)).trans a1, (e 1 (by omega)).trans a2, (e 2 (by omega)).trans a3,
      (e 3 (by omega)).trans a4⟩
  · have hus := walk_lt hpre hk hu
    rw [b6 _ (by omega) (by omega), b4 _ (by omega) (nb _ (by omega)), b3 _ (Or.inl (by omega))]
    exact hm_of_done hpre hT hI hk hd u hu
  · obtain ⟨a1, a2⟩ := pr_of_done hpre hT hI hk hd hd2 j hj
    rw [b6 _ (by omega) (by omega), b4 _ (by omega) (nb _ (by omega)),
      b6 _ (by omega) (by omega), b4 _ (by omega) (nb _ (by omega))]
    exact ⟨a1, a2⟩
  · rw [b6 _ (by omega) (by omega)]
    rw [← hNAO, hd3.1 i hi]
    exact (nc_reads hpre hT hI hk hd hd2 hi).2.1
  · have := hd_nodesK_lt hpre hT hk hi
    rw [b6 _ (by omega) (by omega)]
    have e := hd3.2.1 i hi
    rw [hLOC, (nc_reads hpre hT hI hk hd hd2 hi).2.2] at e
    exact e
  · have e := fun i (hi : i < 9) => hblk i hi
    simp only [RecL.read, blkK]
    have e0 := e 0 (by omega)
    simp only [Nat.add_zero] at e0
    rw [e0, e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
      e 6 (by omega), e 7 (by omega), e 8 (by omega)]
    rfl
  · have e : S.memM6 M1 k H M4 (S.OUTK M1 H k) =
        ((S.oneV M1 k H).smE (S.ℓK k) ((S.oneV M1 k H).putBlk (S.ℓK k) M4)).sum (S.sNK M1 k) := by
      simp only [memM6, Function.update_apply, hOUT]
      simp only [show (S.OUTK M1 H k = S.OUTK M1 H k + 1) = False from by simp, ite_false,
        ite_true]
      rfl
    rw [e, sm_sum hpre hT hI hk hd hd2 hd3]
  · have e : S.memM6 M1 k H M4 (S.OUTK M1 H k + 1) =
        ((S.oneV M1 k H).smE (S.ℓK k) ((S.oneV M1 k H).putBlk (S.ℓK k) M4)).mx (S.sNK M1 k) := by
      simp only [memM6, Function.update_apply, hOUT]
      simp only [ite_true]
      rfl
    rw [e, sm_mx hpre hT hI hk hd hd2 hd3]
  · have hn : ¬ (H ≤ a ∧ a < S.OUTK M1 H k + 2) := h1
    have e6 : S.memM6 M1 k H M4 a = M4 a := by
      simp only [memM6, Function.update_apply, OneV.putBlk, hOUT, hBK]
      split_ifs <;> omega
    rw [e6, hd3.2.2 a ?_, show ((S.oneV M1 k H).ncE (S.ℓK k) M3).mem0 a = M3 a from rfl,
      b3 a (by omega), hd.2.2 a ?_]
    · rfl
    · rintro (⟨h5, h6⟩ | ⟨i, hi, he⟩)
      · have h6' : a < H + 4 * S.ℓK k := h6
        exact hn ⟨h5, by omega⟩
      · exact h3 _ (hwalk i hi) he
    · rintro (⟨h5, h6⟩ | ⟨i, hi, he⟩)
      · have h6' : a < S.NAK M1 H k + S.sNK M1 k := h6
        rw [hNAO] at h5; omega
      · rw [hLOC, (nc_reads hpre hT hI hk hd hd2 hi).2.2] at he
        exact h4 i hi he

/-- **The numbers of the global block are words.** The radius is at most `n` times the largest
weight (`Cl.Δ_le_card_mul`), the threshold is at most the radius (`Inv.big`, as `c` has two
vertices), and `ChildPre.room` bounds these and `J`, `INF`. -/
theorem big_words (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    S.E.J + S.E.INF + S.c.Δ S.G + S.L.lθ + S.h < 2 ^ w := by
  obtain ⟨Mw, hM, hINF, hroom⟩ := hpre.room
  have hJ' : S.E.J = (GlobL.read S.mem S.GB).J := rfl
  have hI' : S.E.INF = (GlobL.read S.mem S.GB).INF := rfl
  rw [hJ', hI']
  set J := (GlobL.read S.mem S.GB).J
  have hcard : S.c.X.card ≤ S.G.n := by
    have := Finset.card_le_card hpre.ok.inv.sub
    simpa using this
  have hΔ : S.c.Δ S.G ≤ S.G.n * Mw :=
    (Cl.Δ_le_card_mul hpre.ok.inv.good.conn hM).trans (Nat.mul_le_mul_right _ hcard)
  have hθΔ : S.c.θ ≤ S.c.Δ S.G := by
    have hB : 1 ≤ S.P.B := hpre.ok.hB
    have two := hpre.two
    rcases hpre.ok.inv.big with h | h
    · omega
    · have : 1 * 1 * S.c.θ ≤ S.P.B * S.c.X.card * S.c.θ :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hB (by omega))
      omega
  have hlθ : S.L.lθ < S.c.θ := by
    rw [hpre.recAt.arcs.th]; exact Nat.lt_two_pow_self
  have hN := hpre.ok.tree.n_lt
  set A := 2 ^ (2 * J + 20) with hA
  have hA8 : 8 ≤ A := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num)
    (show 3 ≤ 2 * J + 20 by omega))
  have hJA : J < A := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num)
    (by omega))
  have hZ : S.G.n * Mw + 4 ≤ (S.T.N + S.G.m + 2) ^ 2 * (Mw + 2) ^ 2 := by
    have h1 : S.G.n + 2 ≤ (S.T.N + S.G.m + 2) ^ 2 :=
      le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
    have h2 : Mw + 2 ≤ (Mw + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    calc S.G.n * Mw + 4 ≤ (S.G.n + 2) * (Mw + 2) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul h1 h2
  have h3 : A * (S.G.n * Mw + 4) ≤ A * ((S.T.N + S.G.m + 2) ^ 2 * (Mw + 2) ^ 2) :=
    Nat.mul_le_mul_left _ hZ
  have h4 : 8 * (S.G.n * Mw) ≤ A * (S.G.n * Mw) := Nat.mul_le_mul_right _ hA8
  have e : A * (S.G.n * Mw + 4) = A * (S.G.n * Mw) + 4 * A := by ring
  rw [← mul_assoc] at h3
  have hI2 : (GlobL.read S.mem S.GB).INF ≤ 4 * (S.G.n * Mw) + 4 := by
    rw [← mul_assoc]; exact hINF
  omega

/-- **The preconditions of the four calls** of child `k`, from one bound on the end of its heap. -/
theorem callsOk (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hroom : H + S.spaceK M1 k + 2 < 2 ^ w) :
    (S.oneV M1 k H).CallsOk w M S.s (S.ℓK k) := by
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hℓ := ℓK_le hpre hT hk
  have hsp : 50 * (S.cntK M1 k + S.sNK M1 k + 1) ≤ S.spaceK M1 k := by
    unfold spaceK
    exact le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_left _ (by omega))
  have hOUT' : S.OUTK M1 H k = H + 4 * S.ℓK k + 2 * S.cntK M1 k + S.sNK M1 k := rfl
  have hOUT : (S.oneV M1 k H).OUT (S.ℓK k) = S.OUTK M1 H k := rfl
  have hNAK : S.NAK M1 H k = H + 4 * S.ℓK k + 2 * S.cntK M1 k := rfl
  refine ⟨hwOk hpre hT hI hk (by omega), fun M2 hd => pcOk hpre hT hI hk hd (by omega),
    fun M2 M3 hd hd2 => ⟨S.T.N, ncOk hpre hT hI hk hd hd2 (by omega)⟩,
    fun M2 M3 M4 hd hd2 hd3 => smOk hpre hT hI hk hd hd2 hd3 (by omega), ?_,
    by rw [hOUT]; omega, show S.h + 9 * k + 9 < 2 ^ w by omega⟩
  -- The words in the registers.
  have bw := big_words hpre
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hEN : S.E.N = S.T.N := hG.N
  have rb : ∀ r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem, r.1 + r.2 ≤ S.h :=
    fun r hr => hpre.below _ hr
  have b1 := rb (S.GB, 21) (by simp [readRegs])
  have b2 := rb (S.RB, 9) (by simp [readRegs])
  have b3 := rb (S.XB, 16) (by simp [readRegs])
  have b4 := rb (S.E.IN, 3 * S.E.m) (by simp [readRegs])
  have b5 := rb (S.E.PW, S.E.m) (by simp [readRegs])
  have b6 := rb (S.E.EXP, S.E.m) (by simp [readRegs])
  have b7 := rb (S.E.HEAD, S.E.N) (by simp [readRegs])
  have b8 := rb (S.E.KMW, S.E.N) (by simp [readRegs])
  have b9 := rb (S.E.KSZ, S.E.N) (by simp [readRegs])
  have b10 := rb (S.X.PAR, S.L.s) (by simp [readRegs, PetL.regs])
  have b11 := rb (S.X.PP, S.L.s) (by simp [readRegs, PetL.regs])
  have b12 := rb (S.X.PF, S.L.s) (by simp [readRegs, PetL.regs])
  have b13 := rb (S.X.PA, S.L.s) (by simp [readRegs, PetL.regs])
  have b14 := rb (S.X.PB, S.L.s) (by simp [readRegs, PetL.regs])
  have b15 := rb (S.X.ACT, 2 * S.X.nA) (by simp [readRegs, PetL.regs])
  have b16 := rb (S.L.NA, S.L.s) (by simp [readRegs, RecL.regs])
  dsimp only at b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hN := hpre.ok.tree.n_lt
  have hDc : S.X.Dc = S.c.Δ S.G := hpre.pet.Dc
  have hct := ct_mem hpre hk
  have hcc := cc_mem hpre hk
  have hctn := hpre.ok.n_of_mem (Cl.raw_X_subset k hct)
  have hccn := hpre.ok.n_of_mem (Cl.raw_X_subset k hcc)
  have hns : S.s = S.R.nodes.length := (pre_of hpre).s
  have hu0 : S.R.sv S.T S.c (S.mem (S.X.CT + k)) < S.s := by
    rw [hns]; exact hpre.ok.sv_lt (Cl.raw_X_subset k hct)
  have hv0 : S.R.sv S.T S.c (S.mem (S.X.CC + k)) < S.s := by
    rw [hns]; exact hpre.ok.sv_lt (Cl.raw_X_subset k hcc)
  have hrg : S.rgK k ≤ 1 := by unfold rgK; split_ifs <;> omega
  have hs : S.s = S.L.s := rfl
  have hnA : S.nA = S.X.nA := rfl
  have o1 := offOf_le' (S.keyF M1) S.nA (k + 1)
  have o2 := offOf_le' (S.chxF M1) S.s (k + 1)
  have o3 := offOf_succ (f := S.keyF M1) S.nA k
  have o4 := offOf_succ (f := S.chxF M1) S.s k
  have hc1 : S.cntK M1 k = (grp (S.keyF M1) S.nA k).length := rfl
  have hc2 : S.sNK M1 k = (grp (S.chxF M1) S.s k).length := rfl
  have a1 : S.OFFN + S.nch + 1 ≤ S.HM := by unfold HM ORDK CNTK OFFK KEY ORDN CNTN; omega
  have a2 : S.OFFK + S.nch + 2 ≤ S.HM := by unfold HM ORDK CNTK; omega
  have a3 : S.ORDN + S.s ≤ S.HM := by unfold HM ORDK CNTK OFFK KEY; omega
  have a4 : S.ORDK + S.nA = S.HM := rfl
  have a5 : S.h ≤ S.OFFN := by unfold OFFN CHX; omega
  intro r hr
  interval_cases r <;>
    simp only [OneV.vals, CS.oneV, List.getD_cons_succ, List.getD_cons_zero] <;> omega

end CS

end MinCostFlow.LowStretch
