module

public import MinCostFlow.LowStretch.ProgChildOneB
public import MinCostFlow.LowStretch.ProgChildStepRaw2

/-!
# One child: the words loaded at child `k`

At the start of child `k` the memory `M` meets the loop invariant `CInv`. This file names the
words that the loads of `oneP` find (`CS.oneV`) and proves the memory facts that the loads use
(`CS.oneFacts`). The cells read are of three kinds.
* Cells of the three blocks and of the arrays they name: no child writes them, so they hold
  what they held at the call.
* Cells of the scratch arrays of the top level: no child writes them, so they hold what the top
  level left (`TopOk`).
* The label and the local index of the target and of the center of child `k`: only child `k`
  writes them, so they still hold the record of `c`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable (S : CS)

/-- **The words of child `k`**, with heap pointer `H`. -/
noncomputable def oneV (M1 : ℕ → ℕ) (k H : ℕ) : OneV where
  GB := S.GB
  RB := S.RB
  XB := S.XB
  BK := S.h + 9 * k
  k := k
  H := H
  OFFN := S.OFFN
  ORDN := S.ORDN
  OFFK := S.OFFK
  ORDK := S.ORDK
  HM := S.HM
  IN := S.E.IN
  PW := S.E.PW
  EXP := S.E.EXP
  LAB := S.E.LAB
  LOC := S.E.LOC
  HEAD := S.E.HEAD
  KMW := S.E.KMW
  KSZ := S.E.KSZ
  J := S.E.J
  INF := S.E.INF
  PAR := S.X.PAR
  PP := S.X.PP
  PF := S.X.PF
  PA := S.X.PA
  PB := S.X.PB
  ACT := S.X.ACT
  Dc := S.X.Dc
  lθ := S.L.lθ
  NAp := S.L.NA
  ct := S.mem (S.X.CT + k)
  cc := S.mem (S.X.CC + k)
  u0 := S.R.sv S.T S.c (S.mem (S.X.CT + k))
  v0 := S.R.sv S.T S.c (S.mem (S.X.CC + k))
  rg := S.rgK k
  SRCK := S.ORDK + offOf (S.keyF M1) S.nA k
  cnt := S.cntK M1 k
  SRCN := S.ORDN + offOf (S.chxF M1) S.s k
  sN := S.sNK M1 k
  B := S.E.B

variable {S} {w : ℕ} {M1 M : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- A safe cell still holds its value at the call. -/
theorem keepM_safe (hT : TopOk S M1)
    (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hI : CInv w S M1 k H Rs M) {a : ℕ} (ha : S.Safe a) : M a = S.mem a := by
  rw [hI.frame a (ha.not_wr hpre k H), hT.low a ha.1]

/-- A cell of the scratch arrays of the top level still holds what the top level left. -/
theorem keepM_top (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hI : CInv w S M1 k H Rs M) (hk : k ≤ S.nch) {a : ℕ} (h1 : S.CHX ≤ a) (h2 : a < S.HM) :
    M a = M1 a := by
  have hH := S.HM_le_H0
  refine hI.frame a ?_
  rintro (⟨-, h3⟩ | ⟨h3, -⟩ | ⟨j, hj, hw⟩)
  · unfold CHX at h1; omega
  · omega
  · have := wrJ_cases hpre (by omega) hw
    unfold CHX at h1
    omega

theorem raw_good' (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hk : k < S.nch) : (S.raw k).Good S.G :=
  Cl.raw_good hpre.ok.inv.good hpre.dec (hpre.ok.inv.Δ_pos hpre.ok.hB hpre.two) hpre.ok.hGo hk

theorem ct_mem (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hk : k < S.nch) : S.mem (S.X.CT + k) ∈ (S.raw k).X := by
  rw [show S.mem (S.X.CT + k) = _ from hpre.pet.ct k hk]
  exact Finset.mem_coe.mp (raw_good' hpre hk).high.1.start_mem

theorem cc_mem (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hk : k < S.nch) : S.mem (S.X.CC + k) ∈ (S.raw k).X := by
  rw [show S.mem (S.X.CC + k) = _ from hpre.pet.cc k hk]
  exact (raw_good' hpre hk).conn.1

/-- The local index of a vertex of child `k` at the start of child `k`. -/
theorem locM_raw (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) {v : ℕ}
    (hv : v ∈ (S.raw k).X) : M (S.E.LOC + M (S.E.LAB + v)) = S.R.sv S.T S.c v := by
  have hvX := Cl.raw_X_subset k hv
  have hvn := hpre.ok.n_of_mem hvX
  have hN := hpre.ok.tree.n_lt
  rw [lab_raw hpre hT hI hk hv]
  have hlt : S.T.hd S.G (S.T.top S.c.θ v) < S.T.N := by
    have ht := KT.top_lt_N hpre.ok.tree hvn hpre.ok.inv.one_le
    exact (KT.hd_under hpre.ok.tree _ ht).lt_N hpre.ok.tree ht
  have h2 : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hH : S.h ≤ S.H0 := by unfold H0 HM ORDK CNTK OFFK KEY ORDN CNTN OFFN CHX; omega
  have hle := hI.hle
  rw [hI.frame _ ?_, hT.low _ (by omega), ← hpre.recAt.lab v hvX]
  · exact hpre.recAt.arcs.loc v hvX
  rintro (⟨h3, -⟩ | ⟨h3, -⟩ | ⟨j, hj, hw⟩)
  · omega
  · omega
  · exact not_wrJ_loc hpre hk (by omega) (by omega) hv hpre.ok.inv.one_le le_rfl hw

theorem safe_reg (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {r : ℕ × ℕ} (hr : r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem) {i : ℕ} (hi : i < r.2) :
    S.Safe (r.1 + i) :=
  safe_of_read hpre hr (by omega) (by omega)

theorem offOf_le' (f : ℕ → ℕ) (n u : ℕ) : offOf f n u ≤ n := by
  unfold offOf
  exact (List.length_filter_le _ _).trans (by simp)

theorem rgK_eq (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) (k : ℕ) :
    S.rgK k = (if 0 < k then 1 else 0) * (1 - (if S.mem (S.XB + 1) = 1 then 1 else 0) *
      (if k = 1 then 1 else 0)) := by
  have hsp : S.mem (S.XB + 1) = if S.D.sp then 1 else 0 := hpre.pet.sp
  unfold rgK Cl.Dec.Reg
  rw [hsp]
  by_cases h0 : k = 0
  · subst h0; simp
  · by_cases h1 : k = 1
    · subst h1; by_cases hd : S.D.sp = true <;> simp [hd]
    · have : 0 < k := Nat.pos_of_ne_zero h0
      simp [h0, h1, this]

/-- **The memory facts of the loads** at the start of child `k`. -/
theorem oneFacts (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hw : H < 2 ^ w) :
    OneFacts w (S.oneV M1 k H) M := by
  have kS := fun {a} (ha : S.Safe a) => keepM_safe hT hpre hI ha
  have hGB : (S.GB, 21) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have hRB : (S.RB, 9) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have hXB : (S.XB, 16) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have hCT : (S.X.CT, S.X.nP + 1) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have hCC : (S.X.CC, S.X.nP + 1) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have hACT : (S.X.ACT, 2 * S.X.nA) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have hNA : (S.L.NA, S.L.s) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, RecL.regs]
  have bG := hpre.below _ hGB
  have bR := hpre.below _ hRB
  have bX := hpre.below _ hXB
  have bCT := hpre.below _ hCT
  have bCC := hpre.below _ hCC
  have bA := hpre.below _ hACT
  have bN := hpre.below _ hNA
  dsimp only at bG bR bX bCT bCC bA bN
  have hnP : S.X.nP + 1 = S.nch := congrArg (· + 1) hpre.pet.nP
  have hHM := S.HM_le_H0
  have hle := hI.hle
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have kT := fun {a} (h1 : S.CHX ≤ a) (h2 : a < S.HM) => keepM_top hpre hI hk.le h1 h2
  have hct := ct_mem hpre hk
  have hcc := cc_mem hpre hk
  have hctn := hpre.ok.n_of_mem (Cl.raw_X_subset k hct)
  have hccn := hpre.ok.n_of_mem (Cl.raw_X_subset k hcc)
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hlabct := lab_raw hpre hT hI hk hct
  have hlabcc := lab_raw hpre hT hI hk hcc
  have hN := hpre.ok.tree.n_lt
  have hdN : ∀ v ∈ (S.raw k).X, S.T.hd S.G (S.T.top S.c.θ v) < S.T.N := fun v hv => by
    have ht := KT.top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k hv))
      hpre.ok.inv.one_le
    exact (KT.hd_under hpre.ok.tree _ ht).lt_N hpre.ok.tree ht
  have hd1 := hdN _ hct
  have hd2 := hdN _ hcc
  have o1 := offOf_le' (S.keyF M1) S.nA k
  have o2 := offOf_le' (S.keyF M1) S.nA (k + 1)
  have o3 := offOf_le' (S.chxF M1) S.s k
  have o4 := offOf_le' (S.chxF M1) S.s (k + 1)
  have hnA : S.nA = S.X.nA := rfl
  have hs : S.s = S.L.s := rfl
  have eK0 : M (S.OFFK + k) = offOf (S.keyF M1) S.nA k := by
    rw [kT (by unfold OFFK KEY ORDN CNTN OFFN; omega)
      (by unfold HM ORDK CNTK; omega), hT.offK k (by omega)]
  have eK1 : M (S.OFFK + k + 1) = offOf (S.keyF M1) S.nA (k + 1) := by
    rw [kT (by unfold OFFK KEY ORDN CNTN OFFN; omega)
      (by unfold HM ORDK CNTK; omega), add_assoc, hT.offK (k + 1) (by omega)]
  have eN0 : M (S.OFFN + k) = offOf (S.chxF M1) S.s k := by
    rw [kT (by unfold OFFN; omega)
      (by unfold HM ORDK CNTK OFFK KEY ORDN CNTN; omega), hT.offN k (by omega)]
  have eN1 : M (S.OFFN + k + 1) = offOf (S.chxF M1) S.s (k + 1) := by
    rw [kT (by unfold OFFN; omega)
      (by unfold HM ORDK CNTK OFFK KEY ORDN CNTN; omega), add_assoc, hT.offN (k + 1) (by omega)]
  have hHM' : S.HM = S.ORDK + S.nA := rfl
  have hKEY : S.KEY = S.ORDN + S.s := rfl
  have hKH : S.KEY ≤ S.HM := by unfold HM ORDK CNTK OFFK; omega
  have e6 : M (S.XB + 6) = S.X.CT := kS (safe_reg hpre hXB (i := 6) (by norm_num))
  have e7 : M (S.XB + 7) = S.X.CC := kS (safe_reg hpre hXB (i := 7) (by norm_num))
  have eLct : M (S.E.LAB + S.mem (S.X.CT + k)) = S.T.hd S.G (S.T.top S.c.θ (S.mem (S.X.CT + k))) :=
    hlabct
  have eLcc : M (S.E.LAB + S.mem (S.X.CC + k)) = S.T.hd S.G (S.T.top S.c.θ (S.mem (S.X.CC + k))) :=
    hlabcc
  refine ⟨kS (safe_reg hpre hGB (i := 3) (by norm_num)),
    kS (safe_reg hpre hGB (i := 4) (by norm_num)),
    kS (safe_reg hpre hGB (i := 5) (by norm_num)), kS (safe_reg hpre hGB (i := 6) (by norm_num)),
    kS (safe_reg hpre hGB (i := 7) (by norm_num)), kS (safe_reg hpre hGB (i := 14) (by norm_num)),
    kS (safe_reg hpre hGB (i := 11) (by norm_num)), kS (safe_reg hpre hGB (i := 12) (by norm_num)),
    kS (safe_reg hpre hGB (i := 19) (by norm_num)), kS (safe_reg hpre hGB (i := 20) (by norm_num)),
    kS (safe_reg hpre hGB (i := 18) (by norm_num)),
    kS (safe_reg hpre hXB (i := 8) (by norm_num)), kS (safe_reg hpre hXB (i := 9) (by norm_num)),
    kS (safe_reg hpre hXB (i := 10) (by norm_num)), kS (safe_reg hpre hXB (i := 11) (by norm_num)),
    kS (safe_reg hpre hXB (i := 12) (by norm_num)), kS (safe_reg hpre hXB (i := 14) (by norm_num)),
    kS (safe_reg hpre hXB (i := 15) (by norm_num)),
    kS (safe_reg hpre hRB (i := 3) (by norm_num)), kS (safe_reg hpre hRB (i := 4) (by norm_num)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show M (M (S.XB + 6) + k) = S.mem (S.X.CT + k)
    rw [e6]; exact kS (safe_reg hpre hCT (i := k) (by omega))
  · show M (M (S.XB + 7) + k) = S.mem (S.X.CC + k)
    rw [e7]; exact kS (safe_reg hpre hCC (i := k) (by omega))
  · exact locM_raw hpre hT hI hk hct
  · exact locM_raw hpre hT hI hk hcc
  · show S.rgK k = _ * (1 - (if M (S.XB + 1) = 1 then 1 else 0) * _)
    rw [show M (S.XB + 1) = S.mem (S.XB + 1) from kS (safe_reg hpre hXB (i := 1) (by norm_num))]
    exact rgK_eq hpre k
  · show S.ORDK + offOf (S.keyF M1) S.nA k = S.ORDK + M (S.OFFK + k)
    rw [eK0]
  · show S.cntK M1 k = M (S.OFFK + k + 1) - M (S.OFFK + k)
    rw [eK0, eK1, offOf_succ]; unfold cntK; omega
  · show S.ORDN + offOf (S.chxF M1) S.s k = S.ORDN + M (S.OFFN + k)
    rw [eN0]
  · show S.sNK M1 k = M (S.OFFN + k + 1) - M (S.OFFN + k)
    rw [eN0, eN1, offOf_succ]; unfold sNK; omega
  · show S.GB + 21 < 2 ^ w; omega
  · show S.XB + 16 < 2 ^ w; omega
  · show S.RB + 9 < 2 ^ w; omega
  · show M (S.XB + 6) + k < 2 ^ w ∧ M (S.XB + 7) + k < 2 ^ w
    rw [e6, e7]; omega
  · show S.E.LAB + S.mem (S.X.CT + k) < 2 ^ w ∧ S.E.LAB + S.mem (S.X.CC + k) < 2 ^ w
    omega
  · show S.E.LOC + M (S.E.LAB + S.mem (S.X.CT + k)) < 2 ^ w ∧
      S.E.LOC + M (S.E.LAB + S.mem (S.X.CC + k)) < 2 ^ w
    rw [eLct, eLcc]; omega
  · show S.OFFK + k + 1 < 2 ^ w ∧ S.OFFN + k + 1 < 2 ^ w
    have a1 : S.OFFK + S.nch + 2 ≤ S.HM := by unfold HM ORDK CNTK; omega
    have a2 : S.OFFN + S.nch + 1 ≤ S.HM := by unfold HM ORDK CNTK OFFK KEY ORDN CNTN; omega
    omega
  · show M (S.OFFK + k + 1) < 2 ^ w ∧ M (S.OFFN + k + 1) < 2 ^ w
    rw [eK1, eN1]; omega
  · show S.ORDK + offOf (S.keyF M1) S.nA k < 2 ^ w ∧ S.ORDN + offOf (S.chxF M1) S.s k < 2 ^ w
    omega
  · omega

end CS

end MinCostFlow.LowStretch
