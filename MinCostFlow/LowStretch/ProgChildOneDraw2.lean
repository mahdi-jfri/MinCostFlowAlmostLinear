module

public import MinCostFlow.LowStretch.ProgChildOneDraw
public import MinCostFlow.LowStretch.ProgChildDrawP

/-!
# One child: the precondition of the radius search

The call of `drawP` in `oneD` runs on the record of raw child `k`, with the cutoff `D = Δ` of the
parent and its arrays from `OUTK + 2` on (`CS.dwE`). This file proves its precondition
(`CS.drawPre_mid`) from `MidOk` and one bound on the heap of the child.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable (S : CS)

/-- The arguments of `drawP` for raw child `k`. -/
noncomputable def dwE (M1 : ℕ → ℕ) (k H : ℕ) : DWE :=
  ⟨S.sNK M1 k, S.cntK M1 k, S.SAK H k, S.E.IN, S.E.PW, S.E.EXP, S.E.LAB, S.E.LOC, S.X.Dc,
    S.L.lθ, (S.rawRec M1 k).sv S.T (S.raw k) (S.raw k).x0, S.E.J, S.E.INF, S.OUTK M1 H k + 2⟩

/-- The ghost of `drawP` for raw child `k`. -/
noncomputable def dwG (M1 : ℕ → ℕ) (k : ℕ) : DWG :=
  ⟨S.T, S.G, S.raw k, S.rawRec M1 k, S.G.m, S.G.n, S.T.N⟩

variable {S} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The end of the cells of `drawP` is within the heap of child `k`. -/
theorem drawEnd_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) : drawEnd (S.dwE M1 k H) ≤ H + S.spaceK M1 k := by
  have hℓ := ℓK_le hpre hT hk
  have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
      (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
  have hO : S.OUTK M1 H k = H + 4 * S.ℓK k + 2 * S.cntK M1 k + S.sNK M1 k := rfl
  set a := S.cntK M1 k + S.sNK M1 k + 1
  have h1 : S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1) ≤ S.E.J * (2 * a) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : S.E.J ≤ S.E.J * a := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : (S.E.J + 1) * (50 * a) ≤ S.spaceK M1 k := by
    unfold spaceK; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have e2 : (S.E.J + 1) * (50 * a) = 50 * (S.E.J * a) + 50 * a := by ring
  have e3 : 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1) =
    2 * (S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) := by ring
  have e4 : S.E.J * (2 * a) = 2 * (S.E.J * a) := by ring
  omega

/-- A label cell after the record of child `k` still holds what it held at the start of child
`k`. -/
theorem lab6 (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    {v : ℕ} (hv : v < S.G.n) : M6 (S.E.LAB + v) = M (S.E.LAB + v) := by
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have d : RegDisj (S.E.LAB, S.G.n) (S.E.LOC, S.T.N) := hpre.lab_loc
  unfold RegDisj at d
  dsimp only at d
  exact hmid.frame _ (by omega) (by omega) (fun u hu => by omega)
    (fun i hi => by have := hd_nodesK_lt hpre hT hk hi; omega)

/-- A local index cell after the record of child `k` holds a word. -/
theorem loc6 (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    {x : ℕ} (hx : x < S.T.N) : M6 (S.E.LOC + x) < 2 ^ w := by
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have bw := big_words hpre
  by_cases he : ∃ i < S.sNK M1 k, x = S.T.hd S.G ((S.nodesK M1 k).getD i 0)
  · obtain ⟨i, hi, rfl⟩ := he
    rw [hmid.loc i hi]
    have := sNK_le hpre hT hk
    omega
  · push Not at he
    rw [hmid.frame _ (by omega) (by omega) (fun u hu => by omega)
      (fun i hi h => he i hi (by omega))]
    exact (hI.loc x hx).1

/-- The stored pair `j` of raw child `k`, and its flag. -/
theorem SK_getD {j : ℕ} (hj : j < S.cntK M1 k) :
    ((S.SK M1 k).getD j (0, 0)).1 = S.actP (S.keyAt M1 k j) ∧
      ((S.SK M1 k).getD j (0, 0)).2 ≤ 1 := by
  have hj' : j < (grp (S.keyF M1) S.nA k).length := hj
  have hl : j < (S.SK M1 k).length := by rw [length_SK]; exact hj
  rw [List.getD_eq_getElem _ _ hl]
  simp only [SK, keyAt, List.getElem_map]
  refine ⟨by rw [List.getD_eq_getElem _ _ hj'], by split_ifs <;> omega⟩

/-- The ends of stored pair `j` of raw child `k` lie in the child, and their local indices are
below the number of its nodes. -/
theorem end6 (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    {j : ℕ} (hj : j < S.cntK M1 k) :
    M6 (S.SAK H k + 2 * j) < S.G.m ∧ M6 (S.SAK H k + 2 * j + 1) ≤ 1 ∧
    M6 (S.E.IN + 3 * M6 (S.SAK H k + 2 * j)) = S.G.pu (M6 (S.SAK H k + 2 * j)) ∧
    M6 (S.E.IN + 3 * M6 (S.SAK H k + 2 * j) + 1) = S.G.pv (M6 (S.SAK H k + 2 * j)) ∧
    S.G.pu (M6 (S.SAK H k + 2 * j)) ∈ (S.raw k).X ∧ S.G.pv (M6 (S.SAK H k + 2 * j)) ∈ (S.raw k).X := by
  obtain ⟨p1, p2⟩ := hmid.pr j hj
  obtain ⟨s1, s2⟩ := SK_getD (S := S) (M1 := M1) (k := k) hj
  obtain ⟨-, hact, hu, hv⟩ := key_ends hpre hT hk (keyAt_mem hj)
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hm : S.E.m = S.G.m := hG.m
  have hplt : S.actP (S.keyAt M1 k j) < S.G.m := by
    have := hact
    simp only [Cl.act, Finset.mem_filter, Finset.mem_range] at this
    exact this.1
  rw [p1, s1]
  refine ⟨hplt, p2 ▸ s2, ?_, ?_, hu, hv⟩
  · have hIN : (S.E.IN, 3 * S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
      simp [readRegs]
    rw [keep_safe hpre hT hI hk hmid (safe_reg hpre hIN (i := 3 * S.actP (S.keyAt M1 k j))
      (by dsimp only; omega))]
    exact (hG.ends _ hplt).1
  · have hIN : (S.E.IN, 3 * S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
      simp [readRegs]
    have e := keep_safe hpre hT hI hk hmid (safe_reg hpre hIN
      (i := 3 * S.actP (S.keyAt M1 k j) + 1) (by dsimp only; omega))
    dsimp only at e
    rw [← add_assoc] at e
    rw [e]
    exact (hG.ends _ hplt).2

/-- **The precondition of `arcP`** inside `drawP`, for raw child `k`. -/
theorem apPre_mid (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hroom : H + S.spaceK M1 k + 2 < 2 ^ w) :
    (S.dwE M1 k H).ap.Pre w M6 S.G.m S.G.n S.T.N := by
  have hA := (rawRecAt hpre hT hI hk hmid).arcs
  rw [hmid.blk] at hA
  have hOK := (pre_of hpre).rawRec_okW hT hk
  have hend := drawEnd_le (H := H) hpre hT hk
  have hE : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
      (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
  have hO : S.OUTK M1 H k = H + 4 * S.ℓK k + 2 * S.cntK M1 k + S.sNK M1 k := rfl
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hm : S.E.m = S.G.m := hG.m
  have hEN : S.E.N = S.T.N := hG.N
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have rb : ∀ r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem, r.1 + r.2 ≤ S.h :=
    fun r hr => hpre.below _ hr
  have b4 := rb (S.E.IN, 3 * S.E.m) (by simp [readRegs])
  have b5 := rb (S.E.PW, S.E.m) (by simp [readRegs])
  have b6 := rb (S.E.EXP, S.E.m) (by simp [readRegs])
  dsimp only at b4 b5 b6
  have iw := inf_words hpre
  have hNn := hpre.ok.tree.n_lt
  have hpw : ∀ p < S.G.m, S.G.pω p < S.E.INF := fun p hp => by
    have := hG.hINF p hp
    have hn : 1 ≤ S.G.n := by have := (hG.hG p hp).1; omega
    have : S.G.pω p ≤ 2 * S.G.n * S.G.pω p :=
      Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hsafe : ∀ r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem, ∀ i < r.2,
      M6 (r.1 + i) = S.mem (r.1 + i) := fun r hr i hi =>
    keep_safe hpre hT hI hk hmid (safe_reg hpre hr hi)
  have hloc6 : ∀ v ∈ (S.raw k).X, M6 (S.E.LOC + M6 (S.E.LAB + v)) < S.sNK M1 k := fun v hv => by
    have e := hA.loc v hv
    have hl := hOK.sv_lt hv
    have hn : (S.rawRec M1 k).nodes.length = S.sNK M1 k := length_nodesK k
    exact (e.trans_lt hl).trans_eq hn
  have hSAK : S.SAK H k = H + 4 * S.ℓK k := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have hea : ∀ j < (S.dwE M1 k H).ap.nS, (S.dwE M1 k H).ap.toAF.ea M6 j < (S.dwE M1 k H).ap.s :=
    fun j hj => by
      show M6 (S.E.LOC + M6 (S.E.LAB + M6 (S.E.IN + 3 * M6 (S.SAK H k + 2 * j)))) < S.sNK M1 k
      obtain ⟨-, -, e1, -, hu, -⟩ := end6 hpre hT hI hk hmid hj
      rw [e1]
      exact hloc6 _ hu
  have heb : ∀ j < (S.dwE M1 k H).ap.nS, (S.dwE M1 k H).ap.toAF.eb M6 j < (S.dwE M1 k H).ap.s :=
    fun j hj => by
      show M6 (S.E.LOC + M6 (S.E.LAB + M6 (S.E.IN + 3 * M6 (S.SAK H k + 2 * j) + 1))) < S.sNK M1 k
      obtain ⟨-, -, -, e2, -, hv⟩ := end6 hpre hT hI hk hmid hj
      rw [e2]
      exact hloc6 _ hv
  have hlabA : ∀ j < (S.dwE M1 k H).ap.nS,
      M6 (S.E.LAB + M6 (S.E.IN + 3 * (S.dwE M1 k H).ap.toAF.pr M6 j)) < S.T.N ∧
      M6 (S.E.LAB + M6 (S.E.IN + 3 * (S.dwE M1 k H).ap.toAF.pr M6 j + 1)) < S.T.N :=
    fun j hj => by
      obtain ⟨hp, -, e1, e2, -, -⟩ := end6 hpre hT hI hk hmid hj
      have hn := hG.hG _ hp
      refine ⟨?_, ?_⟩
      · show M6 (S.E.LAB + M6 (S.E.IN + 3 * M6 (S.SAK H k + 2 * j))) < S.T.N
        rw [e1, lab6 hpre hT hI hk hmid hn.1]
        exact hI.lab _ hn.1
      · show M6 (S.E.LAB + M6 (S.E.IN + 3 * M6 (S.SAK H k + 2 * j) + 1)) < S.T.N
        rw [e2, lab6 hpre hT hI hk hmid hn.2]
        exact hI.lab _ hn.2
  have hlocA : ∀ j < (S.dwE M1 k H).ap.nS,
      (S.dwE M1 k H).ap.toAF.ea M6 j < 2 ^ w ∧ (S.dwE M1 k H).ap.toAF.eb M6 j < 2 ^ w :=
    fun j hj => by
      have h1 : (S.dwE M1 k H).ap.toAF.ea M6 j < S.sNK M1 k := hea j hj
      have h2 : (S.dwE M1 k H).ap.toAF.eb M6 j < S.sNK M1 k := heb j hj
      have h3 := sNK_le hpre hT hk
      have bw := big_words hpre
      exact ⟨by omega, by omega⟩
  refine ⟨⟨fun j hj => (end6 hpre hT hI hk hmid hj).1, fun j hj => (end6 hpre hT hI hk hmid hj).2.1,
    fun p hp => ?_, hlabA, hlocA, fun p hp => ?_,
    fun p hp => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    hea, heb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 := hsafe _ (by simp [readRegs] : (S.E.IN, 3 * S.E.m) ∈ _) (3 * p) (by dsimp only; omega)
    have h2 := hsafe _ (by simp [readRegs] : (S.E.IN, 3 * S.E.m) ∈ _) (3 * p + 1)
      (by dsimp only; omega)
    dsimp only at h1 h2
    show M6 (S.E.IN + 3 * p) < S.G.n ∧ M6 (S.E.IN + 3 * p + 1) < S.G.n
    rw [h1, ← add_assoc] at *
    rw [h2, (hG.ends p hp).1, (hG.ends p hp).2]
    exact hG.hG p hp
  · have h1 := hsafe _ (by simp [readRegs] : (S.E.PW, S.E.m) ∈ _) p (by dsimp only; omega)
    dsimp only at h1
    show M6 (S.E.PW + p) < 2 ^ w
    rw [h1, hG.pw p hp]
    have := hpw p hp
    omega
  · have h1 := hsafe _ (by simp [readRegs] : (S.E.EXP, S.E.m) ∈ _) p (by dsimp only; omega)
    dsimp only at h1
    show M6 (S.E.EXP + p) + 2 < 2 ^ w
    rw [h1]
    have e := hG.ex p hp
    have h3 : S.mem (S.E.EXP + p) < 2 ^ S.mem (S.E.EXP + p) := Nat.lt_two_pow_self
    have := hpw p hp
    have := two_le_Δ hpre
    omega
  all_goals (try simp only [DWE.ap, AP.toAF, dwE]); try omega

/-- **The precondition of `drawP`** for raw child `k`, after its record is written. -/
theorem drawPre_mid (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hroom : H + S.spaceK M1 k + 2 < 2 ^ w) :
    drawPre w (S.dwG M1 k) (S.dwE M1 k H).args M6 := by
  have hA := (rawRecAt hpre hT hI hk hmid).arcs
  rw [hmid.blk] at hA
  have hOK := (pre_of hpre).rawRec_okW hT hk
  have hend := drawEnd_le (H := H) hpre hT hk
  have hDc : S.X.Dc = S.c.Δ S.G := hpre.pet.Dc
  have hΔ := raw_Δ_le hpre hk
  have hI1 := Δc_lt_INF hpre
  have iw := inf_words hpre
  have hx0 : (S.raw k).x0 ∈ (S.raw k).X := (raw_good' hpre hk).conn.1
  have hsv := hOK.sv_lt hx0
  have hn : (S.rawRec M1 k).nodes.length = S.sNK M1 k := length_nodesK k
  refine ⟨S.dwE M1 k H, rfl, ⟨hA.nS, hA.s, hA.pr, hA.fl, hA.ends, hA.pw, hA.ex, hA.loc, hA.th⟩,
    hOK, apPre_mid hpre hT hI hk hmid hroom, ?_, ?_, ?_, J_pos hpre, rfl, ?_, ?_, by omega, ?_,
    ?_⟩
  · show (S.raw k).Δ S.G ≤ S.X.Dc
    omega
  · show (S.raw k).Δ S.G < S.E.INF
    omega
  · show 4 * S.X.Dc < 2 ^ (S.E.J + S.L.lθ)
    rw [hDc]; exact four_Δ_lt hpre
  · show (S.rawRec M1 k).sv S.T (S.raw k) (S.raw k).x0 < S.sNK M1 k
    omega
  · exact zero_mid hpre hT hI hk hmid
  · show S.E.INF * S.E.J + S.E.J < 2 ^ w
    omega
  · show S.E.INF + S.X.Dc < 2 ^ w
    omega

end CS

end MinCostFlow.LowStretch
