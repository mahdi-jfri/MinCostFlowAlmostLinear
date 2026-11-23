module

public import MinCostFlow.LowStretch.ProgResetR

/-!
# The reset of child `k`: the record in memory

After the record block is written, the record `CS.rsRec` of the reset child is in memory in the
form `RecAt` (`CS.rsRecAt`): the stored pairs are where `pcP` and `grpCopyP` wrote them, the
nodes are where `ncP` wrote them, each label is the head of the `x`-node of its vertex (the split
walk wrote it), and that head has as local index the position of the `x`-node (`ncP` wrote it).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}
  {M7 M8 M9 M10 M11 M12 : ℕ → ℕ} {v : ℕ}

/-- The pair that `pcP` reads for entry `j` in the reset is the stored pair `j` of the raw child. -/
theorem RsRun.pc_pr (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v) {j : ℕ} (hj : j < S.cntK M1 k) :
    ((S.rsV M1 k H).rsPcE (S.sNK M1 k + v) M10).pr j = ((S.SK M1 k).getD j (0, 0)).1 := by
  have hACT : (S.X.ACT, 2 * S.X.nA) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  obtain ⟨hiA, -, -, -⟩ := key_ends hpre hT hk (keyAt_mem hj)
  have hnA : S.nA = S.X.nA := rfl
  have e1 := hR.pc_it hpre hT hI hk hmid hj
  have e2 : M10 (S.X.ACT + 2 * S.keyAt M1 k j) = S.actP (S.keyAt M1 k j) :=
    hR.toRsNc.keep hpre hT hI hk hmid hACT (i := 2 * S.keyAt M1 k j) (by dsimp only; omega)
  rw [(SK_getD hj).1]
  simp only [RsV.rsPcE, rsV, PCE.pr, PCE.it]
  rw [e1, e2]

set_option maxHeartbeats 1000000 in
/-- **The record of the reset child is in memory.** -/
theorem rsRecAt (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k)
    (h7 : ∀ a, (a < S.OUTK M1 H k + 2 ∨ drawEnd (S.dwE M1 k H) ≤ a) → M7 a = M6 a)
    (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v)
    (hd12 : ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).Done M12
      ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq) :
    RecAt S.T S.G ((S.raw k).reset (S.thrK k)) (S.rsRec M1 k H v M8 M11) S.E
      (RecL.read ((S.rsV M1 k H).rsBlk (S.sNK M1 k + v)
        (S.cntK M1 k + ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq.length)
        (S.rsV M1 k H).lx M12) (S.h + 9 * k))
      ((S.rsV M1 k H).rsBlk (S.sNK M1 k + v)
        (S.cntK M1 k + ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq.length)
        (S.rsV M1 k H).lx M12) := by
  set A := drawEnd (S.dwE M1 k H) with hA
  set n := S.sNK M1 k + v with hn
  set E := (S.rsV M1 k H).rsGcE v n M11 with hE
  set g := E.seq.length with hg
  set M' := (S.rsV M1 k H).rsBlk n (S.cntK M1 k + g) (S.rsV M1 k H).lx M12 with hM'
  have hrd : RecL.read M' (S.h + 9 * k) =
      ⟨n, S.cntK M1 k + g, A + 5 * n, (S.rsV M1 k H).lx, A + 4 * n, M12 (S.h + 9 * k + 5),
        S.mem (S.X.CC + k), 0, M12 (S.h + 9 * k + 8)⟩ := rsBlk_read (S.rsV M1 k H) _ _ _ _
  rw [hrd]
  have hle := hI.hle
  have hO := S.OUTK_ge M1 H k
  have hb1 := S.h_le_HM
  have hb2 := S.HM_le_H0
  have hend := drawEnd_ge (S := S) (M1 := M1) (H := H) (k := k)
  have hkn : 9 * k + 9 ≤ 9 * S.nch := by omega
  have hlab : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hN := hpre.ok.tree.n_lt
  have hx1 := (thrK_le hpre hk hq).1
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hm : S.E.m = S.G.m := hG.m
  have keep : ∀ r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem, ∀ i < r.2,
      M' (r.1 + i) = S.mem (r.1 + i) := fun r hr i hi => hR.keep12 hpre hT hI hk hmid hd12 hr hi
  have rIN : (S.E.IN, 3 * S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have rPW : (S.E.PW, S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have rEX : (S.E.EXP, S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
  have hS : (S.rsRec M1 k H v M8 M11).S =
      (S.SK M1 k).map (fun e => (e.1, 0)) ++ E.seq.map (fun p => (p, 0)) := rfl
  have hnd : (S.rsRec M1 k H v M8 M11).nodes = rdS M8 A 1 n := rfl
  have hlen : (S.rsRec M1 k H v M8 M11).S.length = S.cntK M1 k + g := by
    rw [hS, List.length_append, List.length_map, List.length_map, length_SK]
  have hSK : (S.SK M1 k).length = S.cntK M1 k := length_SK k
  -- the labels and local indices of the vertices of the child
  have hlab' : ∀ a ∈ (S.raw k).X, M' (S.E.LAB + a) = S.T.hd S.G (S.T.top (S.thrK k) a) := by
    intro a ha
    have han := hpre.ok.n_of_mem (Cl.raw_X_subset k ha)
    rw [hM', hR.eq10 hd12 (by omega) (by omega)]
    exact (hR.lab_loc hpre hT hI hk hmid hq ha).1
  have hloc' : ∀ a ∈ (S.raw k).X, M' (S.E.LOC + S.T.hd S.G (S.T.top (S.thrK k) a)) =
      (rdS M8 A 1 n).idxOf (S.T.top (S.thrK k) a) := by
    intro a ha
    have han := hpre.ok.n_of_mem (Cl.raw_X_subset k ha)
    have hmem : S.T.top (S.thrK k) a ∈ rdS M8 A 1 n :=
      (hR.sp.2.2.2.1 _).mpr ⟨a, ha, rfl⟩
    have hi := List.idxOf_lt_length_of_mem hmem
    set i := (rdS M8 A 1 n).idxOf (S.T.top (S.thrK k) a)
    have hi' : i < n := by rw [rdS_length] at hi; exact hi
    have he : (rdS M8 A 1 n)[i] = S.T.top (S.thrK k) a := List.getElem_idxOf hi
    have he' : M8 (A + 3 * i + 1) = S.T.top (S.thrK k) a := by rw [← he]; simp [rdS]
    have hd := hR.hd_eq hpre hT hI hk hmid hq hi'
    rw [he'] at hd
    have hdN : S.T.hd S.G (S.T.top (S.thrK k) a) < S.T.N :=
      (KT.hd_under hpre.ok.tree _ (top_lt_N hpre.ok.tree han hx1)).lt_N hpre.ok.tree
        (top_lt_N hpre.ok.tree han hx1)
    rw [hM', hR.eq10 hd12 (by omega) (by omega), ← hd]
    exact hR.nc.2.1 i hi'
  -- the center
  have hx0 : M12 (S.h + 9 * k + 5) = (S.raw k).x0 := by
    rw [hR.frame12 hpre hT hI hk hmid hq h7 hd12 (Or.inl (by omega)) (fun b hb => by
        have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb); omega)
      (fun b hb u hu _ => by
        have hbn := hpre.ok.n_of_mem (Cl.raw_X_subset k hb)
        have huN : u < S.T.N := hu.lt_N hpre.ok.tree (by omega)
        have := (KT.hd_under hpre.ok.tree u huN).lt_N hpre.ok.tree huN
        omega)]
    have := congrArg RecL.x0 hmid.blk
    simp only [RecL.read, blkK] at this
    rw [this]
    exact hpre.pet.cc k hk
  refine ⟨⟨hlen.symm, by show n = (rdS M8 A 1 n).length; rw [rdS_length], fun j hj => ?_, fun j hj => ?_,
    fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun a ha => ?_, ?_⟩, fun i hi => ?_, hx0,
    ?_, by simp [Cl.hwE, Cl.reset], fun j hj => absurd hj (Nat.not_lt_zero _),
    fun a ha => hlab' a ha⟩
  · -- the pairs
    rw [hlen] at hj
    show M' (A + 5 * n + 2 * j) = _
    have e1 : E.OUT = A + 5 * n := rfl
    have e2 : E.c0 = S.cntK M1 k := rfl
    rw [hM', rsBlk_of_ne (by simp only [rsV]; omega), hS]
    rcases Nat.lt_or_ge j (S.cntK M1 k) with hj1 | hj1
    · rw [List.getD_append _ _ _ _ (by simp [hSK, hj1]), List.getD_eq_getElem _ _ (by
        simp [hSK, hj1]), List.getElem_map, ← List.getD_eq_getElem _ (0, 0) (by simp [hSK, hj1]),
        ← hR.pc_pr hpre hT hI hk hmid hj1]
      exact (hd12.2 _ (Or.inl (by rw [e1, e2]; omega))).trans (hR.pc.1 j hj1).1
    · obtain ⟨t, rfl⟩ : ∃ t, j = S.cntK M1 k + t := ⟨j - S.cntK M1 k, by omega⟩
      have ht : t < E.seq.length := by omega
      rw [List.getD_append_right _ _ _ _ (by simp [hSK]), List.getD_eq_getElem _ _ (by
        simp [hSK]; exact ht), List.getElem_map]
      simp only [List.length_map, hSK, Nat.add_sub_cancel_left]
      rw [← List.getD_eq_getElem _ 0 ht]
      exact (hd12.1 t ht).1
  · -- the flags
    rw [hlen] at hj
    show M' (A + 5 * n + 2 * j + 1) = _
    have e1 : E.OUT = A + 5 * n := rfl
    have e2 : E.c0 = S.cntK M1 k := rfl
    rw [hM', rsBlk_of_ne (by simp only [rsV]; omega), hS]
    rcases Nat.lt_or_ge j (S.cntK M1 k) with hj1 | hj1
    · rw [List.getD_append _ _ _ _ (by simp [hSK, hj1]), List.getD_eq_getElem _ _ (by
        simp [hSK, hj1]), List.getElem_map]
      refine (hd12.2 _ (Or.inl (by rw [e1, e2]; omega))).trans ((hR.pc.1 j hj1).2.trans ?_)
      simp [PCE.nf, RsV.rsPcE]
    · obtain ⟨t, rfl⟩ : ∃ t, j = S.cntK M1 k + t := ⟨j - S.cntK M1 k, by omega⟩
      have ht : t < E.seq.length := by omega
      rw [List.getD_append_right _ _ _ _ (by simp [hSK]), List.getD_eq_getElem _ _ (by
        simp [hSK]; exact ht), List.getElem_map]
      exact (hd12.1 t ht).2
  · -- the ends
    show M' (S.E.IN + 3 * p) = _ ∧ M' (S.E.IN + 3 * p + 1) = _
    rw [keep _ rIN (3 * p) (by dsimp only; omega), add_assoc,
      keep _ rIN (3 * p + 1) (by dsimp only; omega), ← add_assoc]
    exact hG.ends p hp
  · show M' (S.E.PW + p) = _
    rw [keep _ rPW p (by dsimp only; omega)]; exact hG.pw p hp
  · show _ = 2 ^ M' (S.E.EXP + p)
    rw [keep _ rEX p (by dsimp only; omega)]; exact hG.ex p hp
  · -- the local index of a vertex
    show M' (S.E.LOC + M' (S.E.LAB + a)) = _
    rw [hlab' a ha, hloc' a ha]
    rfl
  · -- the threshold
    show S.thrK k = 2 ^ (S.rsV M1 k H).lx
    rw [← rsV_x hpre]; rfl
  · -- the nodes
    have hi' : i < n := by rw [hnd, rdS_length] at hi; exact hi
    show M' (A + 4 * n + i) = _
    rw [hM', hR.eq10 hd12 (by omega) (by omega), hnd,
      List.getD_eq_getElem _ _ (by rw [rdS_length]; exact hi'),
      show A + 4 * n + i = A + 3 * n + n + i by omega]
    refine (hR.nc.1 i hi').trans ?_
    rw [hR.x_eq hi']
    simp [rdS, hA]
  · -- the target
    show S.mem (S.X.CC + k) = (S.raw k).x0
    exact hpre.pet.cc k hk

end CS

end MinCostFlow.LowStretch
