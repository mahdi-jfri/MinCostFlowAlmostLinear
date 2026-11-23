module

public import MinCostFlow.LowStretch.ProgChildOneHw

/-!
# One child: the stored pairs

The second call of `oneP` writes the stored pairs of child `k` (`pcP`): for each active entry of
key group `k`, its pair and its half flag in the child. The flag of the child is the flag in `c`,
or, for a regular petal, whether the pair is on the highway; `pcP` tests the latter with the marks
that `hwWalkP` has just written (`Ok.hw_test`). This file proves the precondition of `pcP`
(`CS.pcOk`) and reads the stored pairs off its result (`CS.pr_of_done`).

The marks of the earlier children are still in memory. They do no harm: an active pair of child
`k` has its ends in child `k`, and the nodes of these ends are not on the tree path of an earlier
child (`CS.mark_eq`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable {S : CS} {w : ℕ} {M1 M M2 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The active entries of key group `k` have both ends in child `k`. -/
theorem key_ends (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) {i : ℕ} (hi : i ∈ grp (S.keyF M1) S.nA k) :
    i < S.nA ∧ S.actP i ∈ S.c.act S.G S.P ∧ S.G.pu (S.actP i) ∈ (S.raw k).X ∧
      S.G.pv (S.actP i) ∈ (S.raw k).X := by
  have hi' : i < S.nA := by
    simp only [grp, List.mem_filter, List.mem_range] at hi; exact hi.1
  refine ⟨hi', ((pre_of hpre).mem_SK hT hk (S.actP i)).mp ?_⟩
  unfold SK
  rw [List.map_map]
  exact List.mem_map_of_mem hi

/-- Before `H`, below the marks, `hwWalkP` changes nothing. -/
theorem keepM2 (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2) (hle : S.H0 ≤ H) {a : ℕ}
    (ha : a < S.HM) : M2 a = M a := by
  have := S.HM_le_H0
  refine hd.2.2 a ?_
  rintro (⟨h1, -⟩ | ⟨i, -, h1⟩)
  · exact absurd h1 (by show ¬ H ≤ a; omega)
  · exact absurd h1 (by show a ≠ S.HM + _; omega)

/-- **The mark of the node of a vertex of child `k`** after `hwWalkP`: the flag of child `k` on its
tree path, and `0` elsewhere. -/
theorem mark_eq (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2) {v : ℕ} (hv : v ∈ (S.raw k).X) :
    M2 (S.HM + S.R.sv S.T S.c v) = if S.R.sv S.T S.c v ∈ S.walk k then S.rgK k else 0 := by
  have hvX := Cl.raw_X_subset k hv
  have hx : S.R.sv S.T S.c v < S.s := by rw [(pre_of hpre).s]; exact hpre.ok.sv_lt hvX
  split_ifs with hw
  · exact hm_of_done hpre hT hI hk hd _ hw
  have hle := hI.hle
  have h0 : S.H0 = S.HM + S.s := rfl
  rw [hd.2.2 _ ?_]
  · show M (S.HM + _) = 0
    rw [hI.frame _ ?_, hT.zero _ (by omega)]
    rintro (⟨-, h2⟩ | ⟨h2, -⟩ | ⟨j, hj, hwj⟩)
    · have := S.h_le_HM; omega
    · omega
    · rcases hwj with ⟨u, hu, he⟩ | ⟨u, hu, x, hux, -, he⟩ | ⟨u, hu, he⟩
      · have := hpre.ok.n_of_mem (Cl.raw_X_subset j hu)
        have : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
        have := S.h_le_HM; omega
      · have hN : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
        have hun := hpre.ok.n_of_mem (Cl.raw_X_subset j hu)
        have hnN := hpre.ok.tree.n_lt
        have hxN : x < S.T.N := hux.lt_N hpre.ok.tree (by omega)
        have := (KT.hd_under hpre.ok.tree x hxN).lt_N hpre.ok.tree hxN
        have := S.h_le_HM
        omega
      · have hux : u = S.R.sv S.T S.c v := by omega
        have hk' : k < S.D.nch := hk
        obtain ⟨ha, -, -, hue⟩ := hpre.ok.walk_mem hpre.two hpre.dec hpre.pet (by omega) hu
        have hsv : S.R.sv S.T S.c v = S.R.sv S.T S.c (S.mem (S.X.PA + u)) := hux.symm.trans hue
        have := hpre.ok.raw_of_sv hvX (Cl.raw_X_subset j ha) hsv k hv
        exact absurd (Cl.raw_unique (by omega) hk ha this) (by omega)
  · rintro (⟨h2, -⟩ | ⟨i, hi, h2⟩)
    · exact absurd h2 (by show ¬ H ≤ _; omega)
    · apply hw
      have h3 : S.R.sv S.T S.c v = ((S.oneV M1 k H).hwE M).nd i := by
        change S.HM + S.R.sv S.T S.c v = S.HM + ((S.oneV M1 k H).hwE M).nd i at h2
        omega
      rw [h3, nd_eq hpre hT hI hk hi.le]
      exact mem_parWalk.mpr ⟨i, hi, rfl⟩

variable (S) in
/-- The active entry `j` of key group `k`. -/
noncomputable def keyAt (M1 : ℕ → ℕ) (k j : ℕ) : ℕ := (grp (S.keyF M1) S.nA k).getD j 0

theorem keyAt_mem {j : ℕ} (hj : j < S.cntK M1 k) : S.keyAt M1 k j ∈ grp (S.keyF M1) S.nA k :=
  getD_mem_of_lt hj 0

/-- **What `pcP` reads for entry `j`.** -/
theorem pc_reads (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2) {j : ℕ} (hj : j < S.cntK M1 k) :
    ((S.oneV M1 k H).pcE (S.ℓK k) M2).it j = S.keyAt M1 k j ∧
      ((S.oneV M1 k H).pcE (S.ℓK k) M2).pr j = S.actP (S.keyAt M1 k j) ∧
      ((S.oneV M1 k H).pcE (S.ℓK k) M2).fl j = S.actF (S.keyAt M1 k j) ∧
      ((S.oneV M1 k H).pcE (S.ℓK k) M2).eu j = S.G.pu (S.actP (S.keyAt M1 k j)) ∧
      ((S.oneV M1 k H).pcE (S.ℓK k) M2).ev j = S.G.pv (S.actP (S.keyAt M1 k j)) ∧
      ((S.oneV M1 k H).pcE (S.ℓK k) M2).na j = S.R.sv S.T S.c (S.G.pu (S.actP (S.keyAt M1 k j))) ∧
      ((S.oneV M1 k H).pcE (S.ℓK k) M2).nb j =
        S.R.sv S.T S.c (S.G.pv (S.actP (S.keyAt M1 k j))) := by
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have k2 := fun {a} (ha : a < S.HM) => keepM2 hd hle ha
  have kS := fun {a} (ha : S.Safe a) => keepM_safe hT hpre hI ha
  obtain ⟨hiA, hact, hu, hv⟩ := key_ends hpre hT hk (keyAt_mem hj)
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hpm : S.actP (S.keyAt M1 k j) < S.G.m := (Cl.mem_act.mp hact).1
  -- the entry
  have e1 : M2 (S.ORDK + offOf (S.keyF M1) S.nA k + j) = S.keyAt M1 k j := by
    have hoff := offOf_succ (f := S.keyF M1) S.nA k
    have hle' := offOf_le' (S.keyF M1) S.nA (k + 1)
    have hj' : j < (grp (S.keyF M1) S.nA k).length := hj
    have a1 : S.CHX ≤ S.ORDK := by unfold ORDK CNTK OFFK KEY ORDN CNTN OFFN; omega
    have a2 : S.HM = S.ORDK + S.nA := rfl
    rw [k2 (by omega), keepM_top hpre hI hk.le (by omega) (by omega),
      hT.ordK k (by omega) j hj']
    rfl
  have hACT : (S.X.ACT, 2 * S.X.nA) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have hIN : (S.E.IN, 3 * S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have bA := hpre.below _ hACT
  have bI := hpre.below _ hIN
  dsimp only at bA bI
  have hnA : S.nA = S.X.nA := rfl
  have hm : S.E.m = S.G.m := hG.m
  have e2 : M2 (S.X.ACT + 2 * S.keyAt M1 k j) = S.actP (S.keyAt M1 k j) := by
    rw [k2 (by omega)]; exact kS (safe_reg hpre hACT (i := 2 * S.keyAt M1 k j) (by omega))
  have e3 : M2 (S.X.ACT + 2 * S.keyAt M1 k j + 1) = S.actF (S.keyAt M1 k j) := by
    rw [k2 (by omega), add_assoc]
    exact kS (safe_reg hpre hACT (i := 2 * S.keyAt M1 k j + 1) (by omega))
  have e4 : M2 (S.E.IN + 3 * S.actP (S.keyAt M1 k j)) = S.G.pu (S.actP (S.keyAt M1 k j)) := by
    rw [k2 (by omega), kS (safe_reg hpre hIN (i := 3 * S.actP (S.keyAt M1 k j)) (by omega))]
    exact (hG.ends _ hpm).1
  have e5 : M2 (S.E.IN + 3 * S.actP (S.keyAt M1 k j) + 1) = S.G.pv (S.actP (S.keyAt M1 k j)) := by
    rw [k2 (by omega), add_assoc,
      kS (safe_reg hpre hIN (i := 3 * S.actP (S.keyAt M1 k j) + 1) (by omega)), ← add_assoc]
    exact (hG.ends _ hpm).2
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hN := hpre.ok.tree.n_lt
  have hdN : ∀ v ∈ (S.raw k).X, S.T.hd S.G (S.T.top S.c.θ v) < S.T.N := fun v hv => by
    have ht := KT.top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k hv))
      hpre.ok.inv.one_le
    exact (KT.hd_under hpre.ok.tree _ ht).lt_N hpre.ok.tree ht
  have e6 : ∀ v ∈ (S.raw k).X, M2 (S.E.LOC + M2 (S.E.LAB + v)) = S.R.sv S.T S.c v := by
    intro v hv
    have hvn := hpre.ok.n_of_mem (Cl.raw_X_subset k hv)
    have hl := lab_raw hpre hT hI hk hv
    have := hdN v hv
    rw [k2 (a := S.E.LAB + v) (by omega), hl, k2 (by omega), ← hl]
    exact locM_raw hpre hT hI hk hv
  have hit : ((S.oneV M1 k H).pcE (S.ℓK k) M2).it j = S.keyAt M1 k j := e1
  have hpr : ((S.oneV M1 k H).pcE (S.ℓK k) M2).pr j = S.actP (S.keyAt M1 k j) := by
    show M2 (S.X.ACT + 2 * _) = _; rw [hit]; exact e2
  have heu : ((S.oneV M1 k H).pcE (S.ℓK k) M2).eu j = S.G.pu (S.actP (S.keyAt M1 k j)) := by
    show M2 (S.E.IN + 3 * _) = _; rw [hpr]; exact e4
  have hev : ((S.oneV M1 k H).pcE (S.ℓK k) M2).ev j = S.G.pv (S.actP (S.keyAt M1 k j)) := by
    show M2 (S.E.IN + 3 * _ + 1) = _; rw [hpr]; exact e5
  refine ⟨hit, hpr, ?_, heu, hev, ?_, ?_⟩
  · show M2 (S.X.ACT + 2 * _ + 1) = _; rw [hit]; exact e3
  · show M2 (S.E.LOC + M2 (S.E.LAB + _)) = _; rw [heu]; exact e6 _ hu
  · show M2 (S.E.LOC + M2 (S.E.LAB + _)) = _; rw [hev]; exact e6 _ hv

/-- **The precondition of `pcP`** at child `k`, after `hwWalkP`. -/
theorem pcOk (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2)
    (hroom : H + 4 * S.ℓK k + 2 * S.cntK M1 k + 1 < 2 ^ w) :
    ((S.oneV M1 k H).pcE (S.ℓK k) M2).Ok w := by
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have h0 : S.H0 = S.HM + S.s := rfl
  have k2 := fun {a} (ha : a < S.HM) => keepM2 hd hle ha
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hACT : (S.X.ACT, 2 * S.X.nA) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have hIN : (S.E.IN, 3 * S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have hPP : (S.X.PP, S.L.s) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have bA := hpre.below _ hACT
  have bI := hpre.below _ hIN
  have bP := hpre.below _ hPP
  dsimp only at bA bI bP
  have hnA : S.nA = S.X.nA := rfl
  have hs : S.s = S.L.s := rfl
  have hm : S.E.m = S.G.m := hG.m
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hN := hpre.ok.tree.n_lt
  have hw2 : 2 ≤ 2 ^ w := by omega
  refine ⟨fun j hj => ?_, fun j hj => ?_, by show 1 < 2 ^ w; omega, hroom⟩
  · obtain ⟨hit, hpr, -, heu, hev, hna, hnb⟩ := pc_reads hpre hT hI hk hd hj
    obtain ⟨hiA, hact, hu, hv⟩ := key_ends hpre hT hk (keyAt_mem hj)
    have hpm : S.actP (S.keyAt M1 k j) < S.G.m := (Cl.mem_act.mp hact).1
    have hun := hpre.ok.n_of_mem (Cl.raw_X_subset k hu)
    have hvn := hpre.ok.n_of_mem (Cl.raw_X_subset k hv)
    have hsu : S.R.sv S.T S.c (S.G.pu (S.actP (S.keyAt M1 k j))) < S.s := by
      rw [(pre_of hpre).s]; exact hpre.ok.sv_lt (Cl.raw_X_subset k hu)
    have hsv : S.R.sv S.T S.c (S.G.pv (S.actP (S.keyAt M1 k j))) < S.s := by
      rw [(pre_of hpre).s]; exact hpre.ok.sv_lt (Cl.raw_X_subset k hv)
    have hdN : ∀ v ∈ (S.raw k).X, S.T.hd S.G (S.T.top S.c.θ v) < S.T.N := fun v hv => by
      have ht := KT.top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k hv))
        hpre.ok.inv.one_le
      exact (KT.hd_under hpre.ok.tree _ ht).lt_N hpre.ok.tree ht
    have l1 : M2 (S.E.LAB + S.G.pu (S.actP (S.keyAt M1 k j))) =
        S.T.hd S.G (S.T.top S.c.θ (S.G.pu (S.actP (S.keyAt M1 k j)))) := by
      rw [k2 (by omega)]; exact lab_raw hpre hT hI hk hu
    have l2 : M2 (S.E.LAB + S.G.pv (S.actP (S.keyAt M1 k j))) =
        S.T.hd S.G (S.T.top S.c.θ (S.G.pv (S.actP (S.keyAt M1 k j)))) := by
      rw [k2 (by omega)]; exact lab_raw hpre hT hI hk hv
    have d1 := hdN _ hu
    have d2 := hdN _ hv
    have hoff := offOf_succ (f := S.keyF M1) S.nA k
    have hle' := offOf_le' (S.keyF M1) S.nA (k + 1)
    have a2 : S.HM = S.ORDK + S.nA := rfl
    have hj' : j < (grp (S.keyF M1) S.nA k).length := hj
    rw [hit, hpr, heu, hev, hna, hnb]
    change S.ORDK + offOf (S.keyF M1) S.nA k + j < H + 4 * S.ℓK k ∧
      S.X.ACT + 2 * S.keyAt M1 k j + 1 < H + 4 * S.ℓK k ∧
      S.E.IN + 3 * S.actP (S.keyAt M1 k j) + 1 < H + 4 * S.ℓK k ∧
      S.E.LAB + S.G.pu (S.actP (S.keyAt M1 k j)) < H + 4 * S.ℓK k ∧
      S.E.LAB + S.G.pv (S.actP (S.keyAt M1 k j)) < H + 4 * S.ℓK k ∧
      S.E.LOC + M2 (S.E.LAB + S.G.pu (S.actP (S.keyAt M1 k j))) < H + 4 * S.ℓK k ∧
      S.E.LOC + M2 (S.E.LAB + S.G.pv (S.actP (S.keyAt M1 k j))) < H + 4 * S.ℓK k ∧
      S.HM + S.R.sv S.T S.c (S.G.pu (S.actP (S.keyAt M1 k j))) < H + 4 * S.ℓK k ∧
      S.HM + S.R.sv S.T S.c (S.G.pv (S.actP (S.keyAt M1 k j))) < H + 4 * S.ℓK k ∧
      S.X.PP + S.R.sv S.T S.c (S.G.pu (S.actP (S.keyAt M1 k j))) < H + 4 * S.ℓK k ∧
      S.X.PP + S.R.sv S.T S.c (S.G.pv (S.actP (S.keyAt M1 k j))) < H + 4 * S.ℓK k
    rw [l1, l2]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega⟩
  · obtain ⟨-, -, hfl, -, -, hna, hnb⟩ := pc_reads hpre hT hI hk hd hj
    obtain ⟨hiA, -, hu, hv⟩ := key_ends hpre hT hk (keyAt_mem hj)
    have m1 := mark_eq hpre hT hI hk hd hu
    have m2 := mark_eq hpre hT hI hk hd hv
    have hr : S.rgK k ≤ 1 := by unfold rgK; split_ifs <;> omega
    have hf : S.actF (S.keyAt M1 k j) ≤ 1 := by
      have hfl' : S.actF (S.keyAt M1 k j) =
          if S.actP (S.keyAt M1 k j) ∈ S.c.half then 1 else 0 := hpre.pet.act_fl _ hiA
      rw [hfl']; split_ifs <;> omega
    rw [hfl]; omega

/-- **The stored pairs after `pcP`.** -/
theorem pr_of_done (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2) {M3 : ℕ → ℕ}
    (hd2 : ((S.oneV M1 k H).pcE (S.ℓK k) M2).Done (S.cntK M1 k) M3) :
    ∀ j < S.cntK M1 k, M3 (S.SAK H k + 2 * j) = ((S.SK M1 k).getD j (0, 0)).1 ∧
      M3 (S.SAK H k + 2 * j + 1) = ((S.SK M1 k).getD j (0, 0)).2 := by
  intro j hj
  obtain ⟨d1, d2⟩ := hd2.1 j hj
  obtain ⟨-, hpr, hfl, -, -, hna, hnb⟩ := pc_reads hpre hT hI hk hd hj
  obtain ⟨hiA, hact, hu, hv⟩ := key_ends hpre hT hk (keyAt_mem hj)
  have hSK : (S.SK M1 k).getD j (0, 0) = (S.actP (S.keyAt M1 k j),
      if S.actP (S.keyAt M1 k j) ∈ (S.raw k).half then 1 else 0) := by
    have hj' : j < (grp (S.keyF M1) S.nA k).length := hj
    unfold SK keyAt
    rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hj']
  rw [hSK]
  refine ⟨d1.trans hpr, d2.trans ?_⟩
  -- the flag
  have hle := hI.hle
  obtain ⟨hpm, hu', hv', hnl, -⟩ := Cl.mem_act.mp hact
  have hθ : S.c.θ ≤ S.G.pω (S.actP (S.keyAt M1 k j)) :=
    hpre.ok.toW.not_light ⟨hpm, Or.inl ⟨rfl, rfl⟩⟩ hu' hv' hnl
  have hk' : k < S.D.nch := hk
  have hmh := Cl.mem_raw_half (G := S.G) (D := S.D) (k := k) hθ
  have hwt := hpre.ok.hw_test hpre.two hpre.dec hpre.pet hk' hpm
  have m1 := mark_eq hpre hT hI hk hd hu
  have m2 := mark_eq hpre hT hI hk hd hv
  have hsu : S.R.sv S.T S.c (S.G.pu (S.actP (S.keyAt M1 k j))) < S.s := by
    rw [(pre_of hpre).s]; exact hpre.ok.sv_lt (Cl.raw_X_subset k hu)
  have hsv : S.R.sv S.T S.c (S.G.pv (S.actP (S.keyAt M1 k j))) < S.s := by
    rw [(pre_of hpre).s]; exact hpre.ok.sv_lt (Cl.raw_X_subset k hv)
  have p1 := (keepM_tree hpre hT hI hsu).2.1
  have p2 := (keepM_tree hpre hT hI hsv).2.1
  have hPP : (S.X.PP, S.L.s) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have bP := hpre.below _ hPP
  dsimp only at bP
  have hs : S.s = S.L.s := rfl
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have q1 := keepM2 hd hle (a := S.X.PP + S.R.sv S.T S.c (S.G.pu (S.actP (S.keyAt M1 k j))))
    (by omega)
  have q2 := keepM2 hd hle (a := S.X.PP + S.R.sv S.T S.c (S.G.pv (S.actP (S.keyAt M1 k j))))
    (by omega)
  have hfl' : S.actF (S.keyAt M1 k j) =
      if S.actP (S.keyAt M1 k j) ∈ S.c.half then 1 else 0 := hpre.pet.act_fl _ hiA
  show 1 &&& (((S.oneV M1 k H).pcE (S.ℓK k) M2).fl j |||
    (((S.oneV M1 k H).pcE (S.ℓK k) M2).tst j (((S.oneV M1 k H).pcE (S.ℓK k) M2).na j) |||
      ((S.oneV M1 k H).pcE (S.ℓK k) M2).tst j (((S.oneV M1 k H).pcE (S.ℓK k) M2).nb j))) = _
  rw [hfl, hna, hnb]
  unfold PCE.tst
  rw [hpr]
  change 1 &&& (S.actF (S.keyAt M1 k j) |||
    ((if M2 (S.X.PP + S.R.sv S.T S.c (S.G.pu (S.actP (S.keyAt M1 k j)))) =
        S.actP (S.keyAt M1 k j) then 1 else 0) &&&
      M2 (S.HM + S.R.sv S.T S.c (S.G.pu (S.actP (S.keyAt M1 k j)))) |||
    (if M2 (S.X.PP + S.R.sv S.T S.c (S.G.pv (S.actP (S.keyAt M1 k j)))) =
        S.actP (S.keyAt M1 k j) then 1 else 0) &&&
      M2 (S.HM + S.R.sv S.T S.c (S.G.pv (S.actP (S.keyAt M1 k j)))))) = _
  rw [hfl', m1, m2, q1, q2, p1, p2]
  have hmh' : S.actP (S.keyAt M1 k j) ∈ (S.raw k).half ↔ S.actP (S.keyAt M1 k j) ∈ S.c.half ∨
      (S.D.Reg k ∧ ((S.R.sv S.T S.c (S.G.pu (S.actP (S.keyAt M1 k j))) ∈ S.walk k ∧
        S.mem (S.X.PP + S.R.sv S.T S.c (S.G.pu (S.actP (S.keyAt M1 k j)))) =
          S.actP (S.keyAt M1 k j)) ∨
        (S.R.sv S.T S.c (S.G.pv (S.actP (S.keyAt M1 k j))) ∈ S.walk k ∧
        S.mem (S.X.PP + S.R.sv S.T S.c (S.G.pv (S.actP (S.keyAt M1 k j)))) =
          S.actP (S.keyAt M1 k j)))) := by
    rw [show (S.raw k).half = (S.c.raw S.G S.D k).half from rfl, hmh]
    exact or_congr Iff.rfl (and_congr Iff.rfl hwt)
  simp only [hmh']
  unfold rgK
  generalize S.actP (S.keyAt M1 k j) = q at *
  generalize S.R.sv S.T S.c (S.G.pu q) = a at *
  generalize S.R.sv S.T S.c (S.G.pv q) = b at *
  by_cases c1 : q ∈ S.c.half <;> by_cases c2 : S.D.Reg k <;> by_cases c3 : a ∈ S.walk k <;>
    by_cases c4 : S.mem (S.X.PP + a) = q <;> by_cases c5 : b ∈ S.walk k <;>
    by_cases c6 : S.mem (S.X.PP + b) = q <;> simp [c1, c2, c3, c4, c5, c6]

end CS

end MinCostFlow.LowStretch
