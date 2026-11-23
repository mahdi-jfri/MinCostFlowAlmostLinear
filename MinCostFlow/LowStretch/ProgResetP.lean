module

public import MinCostFlow.LowStretch.ProgResetO

/-!
# The reset of child `k`: the run of `rsP` for the child

`rsP_runs` gives the run of `rsP` for any words and any layout of the split walk, with the facts
of the child as hypotheses. This file fills them in for raw child `k` when it is reset
(`CS.rsP_child`): the words of `CS.rsV`, the layout `CS.spL`, the precondition of the split walk
(`splitPre_rs`), of `ncP` (`rsNcPre`), of `pcP` (`RsNc.pcOk`) and of `grpCopyP` (`RsRun.gcOk`),
and the room of `rs_room`. What the run leaves is `CS.RsEnd`, and its cost is at most `CS.rsCost`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable (S : CS)

/-- **What the reset of child `k` leaves**, started on the memory `M7`: the facts of the run up
to `pcP` (`RsRun`), the pairs that `grpCopyP` copies, the memory after the record block, and the
returned heap pointer. -/
def RsEnd (w : ℕ) (M1 : ℕ → ℕ) (k H : ℕ) (M6 M7 : ℕ → ℕ) (o : Outcome) (M' : ℕ → ℕ) : Prop :=
  ∃ v M8 M9 M10 M11 M12, RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v ∧
    ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).Done M12
      ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq ∧
    M' = (S.rsV M1 k H).rsBlk (S.sNK M1 k + v)
      (S.cntK M1 k + ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq.length)
      (S.rsV M1 k H).lx M12 ∧
    o = .returned (drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) +
      2 * (S.cntK M1 k + ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq.length))

/-- The cost bound of the reset of child `k`. -/
noncomputable def rsCost (M1 : ℕ → ℕ) (k : ℕ) : ℕ :=
  1300 + log2Cost (Cl.resetS S.T S.G S.P (S.raw k) / (4 * S.P.B * (S.raw k).X.card)) +
    590 * S.sNK M1 k + 200 * S.cntK M1 k + 1000 * S.visK k

variable {S} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The work of the split walk, the nodes and the copied pairs fits in `1000 visK k`. -/
theorem rs_cost_le (hq : S.resetQ k) {M7 M8 : ℕ → ℕ} {v : ℕ}
    (hsp : SplitPost S.T S.G (S.raw k) (S.thrK k) (S.spL M1 k H) M7 v M8 0) :
    800 * ∑ u ∈ S.T.splitSet S.G (S.raw k) (S.thrK k), (S.T.sz S.G (S.T.light S.G u) + 1) +
      150 * v + 60 * ∑ u ∈ S.T.splitSet S.G (S.raw k) (S.thrK k), S.T.nLca S.G u ≤
      1000 * S.visK k := by
  have hcs : S.csOf k = (S.raw k).reset (S.thrK k) := by unfold csOf; rw [if_pos hq]
  have hv : (S.T.splitSet S.G (S.raw k) (S.thrK k)).card = v := by
    rw [← hsp.1, List.toFinset_card_of_nodup hsp.2.1, rdS_length]
  unfold visK KT.visW
  rw [hcs]
  show _ ≤ 1000 * ∑ u ∈ S.T.splitSet S.G (S.raw k) (S.thrK k), _
  rw [← hv, Finset.card_eq_sum_ones, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun u _ => by omega

/-- `w ≥ 2` when `3` is a word. -/
theorem two_le_w {w : ℕ} (h : 3 < 2 ^ w) : 2 ≤ w := by
  by_contra hw
  have : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The small words of the reset: the radius, the largest weight, `4 B |X|`, `|X|`, `B` and
the threshold `θ` of `c`. -/
theorem rs_small (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hk : k < S.nch) (hq : S.resetQ k) :
    (S.raw k).Δ S.G < 2 ^ w ∧ (S.raw k).X.sup (fun a => S.T.mw (S.T.top S.c.θ a)) < 2 ^ w ∧
      4 * S.E.B * (S.raw k).X.card < 2 ^ w ∧ 1 ≤ 4 * S.E.B * (S.raw k).X.card ∧
      (S.raw k).X.card < 2 ^ w ∧ S.E.B < 2 ^ w ∧ S.c.θ < 2 ^ w := by
  have hB : S.E.B = S.P.B := hpre.glob.B
  have hbx := bxθ_lt hpre k
  have hθ1 : 1 ≤ S.c.θ := hpre.ok.inv.one_le
  obtain ⟨hx1, hx4⟩ := thrK_le hpre hk hq
  have hXc : 2 ≤ (S.raw k).X.card := hq.1
  have hB1 : 1 ≤ S.P.B := hpre.ok.hB
  have hθw : S.c.θ < 2 ^ w := by
    have : 1 * 1 * S.c.θ ≤ S.P.B * (S.raw k).X.card * S.c.θ :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul hB1 (by omega))
    omega
  have hBX : S.P.B * (S.raw k).X.card < 2 ^ w := by
    have : S.P.B * (S.raw k).X.card * 1 ≤ S.P.B * (S.raw k).X.card * S.c.θ :=
      Nat.mul_le_mul_left _ hθ1
    omega
  have h4BX : 4 * S.P.B * (S.raw k).X.card ≤ S.P.B * (S.raw k).X.card * S.c.θ := by
    have : S.P.B * (S.raw k).X.card * 4 ≤ S.P.B * (S.raw k).X.card * S.c.θ :=
      Nat.mul_le_mul_left _ (by omega)
    have e : 4 * S.P.B * (S.raw k).X.card = S.P.B * (S.raw k).X.card * 4 := by ring
    omega
  have hXw : (S.raw k).X.card < 2 ^ w := by
    have : 1 * (S.raw k).X.card ≤ S.P.B * (S.raw k).X.card := Nat.mul_le_mul_right _ hB1
    omega
  have hEBw : S.P.B < 2 ^ w := by
    have : S.P.B * 1 ≤ S.P.B * (S.raw k).X.card := Nat.mul_le_mul_left _ (by omega)
    omega
  have bw := big_words hpre
  have hΔr := raw_Δ_le hpre hk
  have hμ : (S.raw k).X.sup (fun a => S.T.mw (S.T.top S.c.θ a)) < S.c.θ := by
    refine (Finset.sup_lt_iff (by simp only [bot_eq_zero']; omega)).mpr fun a ha => ?_
    exact (isTop_top hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha)) hθ1).2.1
  rw [hB]
  exact ⟨by omega, by omega, by omega, Nat.mul_pos (Nat.mul_pos (by norm_num) hB1) (by omega),
    hXw, hEBw, hθw⟩

/-- The global arrays lie below `h`. -/
theorem glob_below (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) :
    S.E.KCH1 ≤ S.h ∧ S.E.KCH2 ≤ S.h ∧ S.E.KMW ≤ S.h ∧ S.E.KSZ ≤ S.h ∧ S.E.KLO ≤ S.h ∧
      S.E.ORDL ≤ S.h ∧ S.E.HEAD ≤ S.h ∧ S.E.GOFF ≤ S.h ∧ S.E.GPR ≤ S.h ∧
      S.E.LAB + S.E.n ≤ S.h := by
  have bG : ∀ {a b : ℕ}, (a, b) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem → a ≤ S.h :=
    fun hr => by have := hpre.below _ hr; dsimp only at this; omega
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hn : S.E.n = S.G.n := hpre.glob.n
  exact ⟨bG (b := S.E.N) (by simp [readRegs]), bG (b := S.E.N) (by simp [readRegs]),
    bG (b := S.E.N) (by simp [readRegs]), bG (b := S.E.N) (by simp [readRegs]),
    bG (b := S.E.N) (by simp [readRegs]), bG (b := S.E.n) (by simp [readRegs]),
    bG (b := S.E.N) (by simp [readRegs]), bG (b := S.E.N + 1) (by simp [readRegs]),
    bG (b := S.E.m) (by simp [readRegs]), by omega⟩

/-- The end of the cells of `drawP` is past `OUTK + 2`. -/
theorem drawEnd_ge : S.OUTK M1 H k + 2 ≤ drawEnd (S.dwE M1 k H) := by
  have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
      (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
  omega

/-- **The words of the reset**: the arguments and loads of `rsP`, and the arguments of the split
walk. -/
theorem rs_words (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hq : S.resetQ k)
    (hroom : H + S.spaceK M1 k + 2 < 2 ^ w)
    (hroom2 : drawEnd (S.dwE M1 k H) + 3 * (S.sNK M1 k + S.T.N + 1) < 2 ^ w) :
    (∀ x ∈ (S.rsV M1 k H).args ++ [(S.rsV M1 k H).SRCK, (S.rsV M1 k H).ACT, (S.rsV M1 k H).IN,
      (S.rsV M1 k H).LAB, (S.rsV M1 k H).LOC, (S.rsV M1 k H).HM, (S.rsV M1 k H).PP,
      (S.rsV M1 k H).GOFF, (S.rsV M1 k H).GPR], x < 2 ^ w) ∧
    (∀ v ∈ (S.spL M1 k H).args, v < 2 ^ w) := by
  obtain ⟨s1, s2, -, -, s5, s6, s7⟩ := rs_small hpre hk hq
  obtain ⟨hx1, hx4⟩ := thrK_le hpre hk hq
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := glob_below hpre
  have bw := big_words hpre
  have hle := hI.hle
  have hhM : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hHM := S.HM_le_H0
  have hO : H ≤ S.OUTK M1 H k := S.OUTK_ge M1 H k
  have hend := drawEnd_le (H := H) hpre hT hk
  have hend2 : S.OUTK M1 H k + 2 ≤ drawEnd (S.dwE M1 k H) := drawEnd_ge
  have hNA : S.NAK M1 H k ≤ S.OUTK M1 H k := by unfold OUTK; omega
  have hsN := sNK_le hpre hT hk
  have W := (callsOk hpre hT hI hk hroom).words
  have w11 := W 11 (by norm_num)
  have w14 := W 14 (by norm_num)
  have w15 := W 15 (by norm_num)
  have w22 := W 22 (by norm_num)
  have w26 := W 26 (by norm_num)
  have w31 := W 31 (by norm_num)
  have w35 := W 35 (by norm_num)
  have w36 := W 36 (by norm_num)
  simp only [OneV.vals, oneV, List.getD_cons_succ, List.getD_cons_zero] at w11 w14 w15 w22
  simp only [OneV.vals, oneV, List.getD_cons_succ, List.getD_cons_zero] at w26 w31 w35 w36
  have w0 : S.GB < 2 ^ w := by
    have := hpre.below (S.GB, 21) (by simp [readRegs]); dsimp only at this; omega
  have w2 : S.XB < 2 ^ w := by
    have := hpre.below (S.XB, 16) (by simp [readRegs]); dsimp only at this; omega
  have w3 : S.h + 9 * k < 2 ^ w := by omega
  constructor
  · simp only [RsV.args, rsV, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  · simp only [SplitL.args, spL, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> omega

set_option maxHeartbeats 2000000 in
/-- **The run of `rsP` for raw child `k`.** Started on any memory `M7` that agrees with `M6`
below `OUTK + 2`, the reset of a child that meets `resetQ` ends as `RsEnd` says, within
`rsCost`. -/
theorem rsP_child {p : Program} {ω : ℕ → Bool} {I : CIdx}
    (flg : MeetsContract w p I.lg (log2C w)) (fsp : MeetsContract w p I.sp (splitC w))
    (fio : MeetsContract w p I.io (iotaC w)) (fnc : MeetsContract w p I.nc (ncC w))
    (fpc : MeetsContract w p I.pc (pcC w)) (fgc : MeetsContract w p I.gc (grpCopyC w))
    (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k) (hroom : H + S.spaceK M1 k + 2 < 2 ^ w)
    (hroom2 : drawEnd (S.dwE M1 k H) + 3 * (S.sNK M1 k + S.T.N + 1) < 2 ^ w)
    {M7 : ℕ → ℕ} (h7 : ∀ a, a < S.OUTK M1 H k + 2 → M7 a = M6 a) (pos : ℕ) :
    ∃ o st' c, Runs w p ω (rsP I) (startState (S.rsV M1 k H).args M7 pos) o st' c ∧
      S.RsEnd w M1 k H M6 M7 o st'.mem ∧ c ≤ S.rsCost M1 k := by
  set V := S.rsV M1 k H with hV
  have hF : RsFacts w V M7 := rsFacts hpre hT hI hk hmid hroom h7
  have ex : V.x = S.thrK k := rsV_x hpre
  have eS : V.S = Cl.resetS S.T S.G S.P (S.raw k) := rsV_S hpre
  have hB : S.E.B = S.P.B := hpre.glob.B
  obtain ⟨hx1, hx4⟩ := thrK_le hpre hk hq
  obtain ⟨s1, s2, s3, s4, -, -, s7⟩ := rs_small hpre hk hq
  obtain ⟨hw1, hw2⟩ := rs_words hpre hT hI hk hq hroom hroom2
  have hHD := (glob_below hpre).2.2.2.2.2.2.1
  have bw := big_words hpre
  have hbk := (callsOk hpre hT hI hk hroom).bk
  have hP : SplitPre w S.T S.G (S.raw k) V.x (S.spL M1 k H) M7 := by
    rw [ex]; exact splitPre_rs hpre hT hI hk hmid hq h7 hroom2 (by omega)
  refine rsP_runs (N := S.T.N) (T := S.T) (G := S.G) (r := S.raw k) (E := S.spL M1 k H)
    flg fsp fio fnc fpc fgc hF s1 s2 s3 s4 (two_le_w hF.bw) hw1 (by show S.E.HEAD < 2 ^ w; omega)
    (by show S.h + 9 * k + 7 < 2 ^ w; simp only [OneV.vals, oneV] at hbk; omega)
    (by rw [ex]; rfl) hw2 hP ?_ ?_ ?_ ?_ ?_
  · -- the room of the index list
    intro v M8 hsp
    rw [ex] at hsp
    have := rs_room hpre hT hk hroom (rs_vis_le hq hsp)
    show drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) + 1 < 2 ^ w
    omega
  · -- the precondition of `ncP`
    intro v M8 M9 hsp hio
    rw [ex] at hsp
    have := rs_room hpre hT hk hroom (rs_vis_le hq hsp)
    exact rsNcPre hpre hT hI hk hmid hq h7 hsp hio.1 hio.2 (by omega)
  · -- the precondition of `pcP`
    intro v M8 M9 M10 hsp hio hd
    rw [ex] at hsp
    have := rs_room hpre hT hk hroom (rs_vis_le hq hsp)
    have hok := rsNcPre hpre hT hI hk hmid hq h7 hsp hio.1 hio.2 (by omega)
    exact RsNc.pcOk hpre hT hI hk hmid hq ⟨h7, hsp, hio, hok, hd⟩ (by omega)
  · -- the precondition of `grpCopyP`
    intro v M8 M9 M10 M11 hsp hio hd hd11
    rw [ex] at hsp
    have := rs_room hpre hT hk hroom (rs_vis_le hq hsp)
    have hok := rsNcPre hpre hT hI hk hmid hq h7 hsp hio.1 hio.2 (by omega)
    exact RsRun.gcOk hpre hT hI hk hmid ⟨⟨h7, hsp, hio, hok, hd⟩, hd11⟩ (sNK_pos hpre hT hk hq)
      this
  · -- the outcome and the cost
    intro v M8 M9 M10 M11 M12 pos' hsp hio hd hd11 hd12 regs
    rw [ex] at hsp
    have hv := rs_room hpre hT hk hroom (rs_vis_le hq hsp)
    have hok := rsNcPre hpre hT hI hk hmid hq h7 hsp hio.1 hio.2 (by omega)
    have hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v := ⟨⟨h7, hsp, hio, hok, hd⟩, hd11⟩
    have hg := hR.gc_len hpre hT hI hk hmid
    refine ⟨⟨v, M8, M9, M10, M11, M12, hR, hd12, rfl, rfl⟩, ?_⟩
    have hc := rs_cost_le hq hsp
    have hsb : splitBd ⟨S.T, S.G, S.raw k, V.x⟩ (S.spL M1 k H) = 500 * (S.sNK M1 k + 1) +
        800 * ∑ u ∈ S.T.splitSet S.G (S.raw k) (S.thrK k),
          (S.T.sz S.G (S.T.light S.G u) + 1) := by
      simp only [splitBd, spL, ex]
    have hlg : V.S / (4 * V.B * V.sz) =
        Cl.resetS S.T S.G S.P (S.raw k) / (4 * S.P.B * (S.raw k).X.card) := by
      rw [eS]; simp only [V, rsV, hB]
    have hg' : (V.rsGcE v (V.sN + v) M11).seq.length =
        ∑ u ∈ S.T.splitSet S.G (S.raw k) (S.thrK k), S.T.nLca S.G u := hg
    have hcnt : V.cnt = S.cntK M1 k := rfl
    have hsN' : V.sN = S.sNK M1 k := rfl
    rw [hsb, hlg, hg', hcnt, hsN']
    unfold rsCost
    omega

end CS

end MinCostFlow.LowStretch
