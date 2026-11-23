module

public import MinCostFlow.LowStretch.ProgResetM
public import MinCostFlow.LowStretch.CountVisTree

/-!
# The reset of child `k`: the precondition of `grpCopyP`

`grpCopyP` reads the split nodes in column `2` of the work array, and for each of them the range
of the pairs grouped at it, `[GOFF[u], GOFF[u + 1])`. These ranges are `offOf lf m u` and
`offOf lf m (u + 1)` for the lowest common node `lf` of `GlobL.Ok.lca`, so the range of `u` holds
the `nLca u` pairs whose lowest common node is `u` (`grp_len_nLca`). Hence the reset copies
`Σ_{u ∈ splitSet} nLca u` pairs (`CS.rsGc_len`), and `grpCopyP` meets its precondition
(`CS.rsGcOk`).

`CS.RsRun` bundles the facts of the run of the reset up to `pcP`, on the memories `M7` (at the
split call) to `M11` (after `pcP`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

/-- The group of `u` holds the pairs whose lowest common node is `u`. -/
theorem grp_len_nLca {T : KT} {G : PG} (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n)
    {lf : ℕ → ℕ} (hlf : ∀ p < G.m, T.IsLca (G.pu p) (G.pv p) (lf p)) (u : ℕ) :
    (grp lf G.m u).length = T.nLca G u := by
  classical
  unfold grp KT.nLca
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  ext p
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_filter,
    Finset.mem_range, decide_eq_true_eq]
  have hN := h.n_lt
  constructor
  · rintro ⟨hp, rfl⟩; exact ⟨hp, hlf p hp⟩
  · rintro ⟨hp, hu⟩
    exact ⟨hp, KT.IsLca.unique h (by have := (hG p hp).1; omega) (hlf p hp) hu⟩

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The facts of the run of the reset of child `k` up to `ncP`: `M7` agrees with `M6` below
`OUTK + 2`, `M8` is after the split walk with `v` split nodes, `M9` after `iotaP` and `M10` after
`ncP`. -/
structure RsNc (w : ℕ) (S : CS) (M1 : ℕ → ℕ) (k H : ℕ) (M6 M7 M8 M9 M10 : ℕ → ℕ) (v : ℕ) :
    Prop where
  h7 : ∀ a, a < S.OUTK M1 H k + 2 → M7 a = M6 a
  sp : SplitPost S.T S.G (S.raw k) (S.thrK k) (S.spL M1 k H) M7 v M8 0
  io : RsIota (drawEnd (S.dwE M1 k H)) (S.sNK M1 k + v) M8 M9
  ok : (rsNcE (drawEnd (S.dwE M1 k H)) (S.sNK M1 k + v) S.E.HEAD S.E.LOC M9).Ok w S.T.N
  nc : (rsNcE (drawEnd (S.dwE M1 k H)) (S.sNK M1 k + v) S.E.HEAD S.E.LOC M9).Done
    (S.sNK M1 k + v) M10

/-- The facts of the run of the reset of child `k` up to `pcP`, whose memory after is `M11`. -/
structure RsRun (w : ℕ) (S : CS) (M1 : ℕ → ℕ) (k H : ℕ) (M6 M7 M8 M9 M10 M11 : ℕ → ℕ) (v : ℕ) :
    Prop extends RsNc w S M1 k H M6 M7 M8 M9 M10 v where
  pc : ((S.rsV M1 k H).rsPcE (S.sNK M1 k + v) M10).Done (S.cntK M1 k) M11

variable {M7 M8 M9 M10 M11 : ℕ → ℕ} {v : ℕ}

/-- A cell of a read region holds after `ncP` its value at the start of the child step. -/
theorem RsNc.keep (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hR : RsNc w S M1 k H M6 M7 M8 M9 M10 v) {r : ℕ × ℕ}
    (hr : r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem) {i : ℕ} (hi : i < r.2) :
    M10 (r.1 + i) = S.mem (r.1 + i) := by
  have hb : r.1 + r.2 ≤ S.h := hpre.below r hr
  have dL : RegDisj r (S.E.LAB, S.G.n) := hpre.lab_disj r hr
  have dC : RegDisj r (S.E.LOC, S.T.N) := hpre.loc_disj r hr
  unfold RegDisj at dL dC
  dsimp only at hb dL dC
  have hle := hI.hle
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hHM := S.HM_le_H0
  have hO : H ≤ S.OUTK M1 H k := S.OUTK_ge M1 H k
  have hend : S.OUTK M1 H k + 2 ≤ drawEnd (S.dwE M1 k H) := by
    have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
        (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
    omega
  rw [rsKeep10 (a := r.1 + i) hR.h7 hR.sp hR.io hR.ok hR.nc (by omega) (fun b hb' => by
      have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb')
      omega) (by omega)]
  exact keep_safe hpre hT hI hk hmid (safe_reg hpre hr hi)

/-- A cell of a read region holds after `pcP` its value at the start of the child step. -/
theorem RsRun.keep (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v) {r : ℕ × ℕ}
    (hr : r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem) {i : ℕ} (hi : i < r.2) :
    M11 (r.1 + i) = S.mem (r.1 + i) := by
  have hb : r.1 + r.2 ≤ S.h := hpre.below r hr
  have hle := hI.hle
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hHM := S.HM_le_H0
  have hO : H ≤ S.OUTK M1 H k := S.OUTK_ge M1 H k
  have hend : S.OUTK M1 H k + 2 ≤ drawEnd (S.dwE M1 k H) := by
    have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
        (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
    omega
  rw [hR.pc.2 _ (Or.inl (by simp only [RsV.rsPcE, rsV]; omega))]
  exact hR.toRsNc.keep hpre hT hI hk hmid hr hi

/-- Entry `i` of column `2` after `pcP` is split node `i`. -/
theorem RsRun.col2 (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hI : CInv w S M1 k H Rs M) (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v) {i : ℕ}
    (hi : i < v) : M11 (drawEnd (S.dwE M1 k H) + 2 + 3 * i) = M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) := by
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hA : S.h ≤ drawEnd (S.dwE M1 k H) := by
    have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
        (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
    have : S.h ≤ S.OUTK M1 H k := by
      have := S.OUTK_ge M1 H k
      have := S.h_le_HM
      have := S.HM_le_H0
      have := hI.hle
      omega
    omega
  rw [hR.pc.2 _ (Or.inl (by simp only [RsV.rsPcE, rsV]; omega))]
  show M10 _ = _
  rw [hR.nc.2.2 _ (fun hout => by
      rcases hout with ⟨h1, -⟩ | ⟨j, hj, he⟩
      · simp only [rsNcE] at h1; omega
      · have := (hR.ok.rd j hj).2.2.2
        simp only [rsNcE] at he this; omega)]
  show M9 _ = _
  rw [hR.io.2 _ (Or.inl (by omega))]
  congr 1; omega

/-- The keys of `grpCopyP` are the split nodes, and their ranges are those of the grouping by the
lowest common node `lf`. -/
theorem RsRun.gc_reads (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v) {lf : ℕ → ℕ}
    (hoff : ∀ u ≤ S.T.N, S.mem (S.E.GOFF + u) = offOf lf S.G.m u) {i : ℕ} (hi : i < v) :
    ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).key i =
        M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) ∧
      M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) ∈ S.T.splitSet S.G (S.raw k) (S.thrK k) ∧
      ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).lo i =
        offOf lf S.G.m (M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2)) ∧
      ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).hi i =
        offOf lf S.G.m (M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) + 1) := by
  have hkey : ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).key i =
      M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) := hR.col2 hpre hI hi
  have hmem : M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) ∈ S.T.splitSet S.G (S.raw k) (S.thrK k) := by
    rw [← hR.sp.1, List.mem_toFinset]
    have : M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) =
        (rdS M8 (S.spL M1 k H).A 2 v)[i]'(by rw [rdS_length]; exact hi) := by simp [rdS, spL]
    rw [this]; exact List.getElem_mem _
  have hN : M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) < S.T.N := by
    have := hmem; simp only [KT.splitSet, Finset.mem_filter, Finset.mem_range] at this
    exact this.1
  have hGO : (S.E.GOFF, S.E.N + 1) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have hEN : S.E.N = S.T.N := hpre.glob.N
  refine ⟨hkey, hmem, ?_, ?_⟩
  · show M11 (S.E.GOFF + _) = _
    rw [hkey, hR.keep hpre hT hI hk hmid hGO (by dsimp only; omega), hoff _ hN.le]
  · show M11 (S.E.GOFF + _ + 1) = _
    rw [hkey, add_assoc, hR.keep hpre hT hI hk hmid hGO (by dsimp only; omega), hoff _ hN]

/-- **The number of pairs that the reset copies** is `Σ_{u ∈ splitSet} nLca u`. -/
theorem RsRun.gc_len (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v) :
    ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq.length =
      ∑ u ∈ S.T.splitSet S.G (S.raw k) (S.thrK k), S.T.nLca S.G u := by
  obtain ⟨lf, hlf, hoff, -⟩ := hpre.glob.lca
  have hoff' : ∀ u ≤ S.T.N, S.mem (S.E.GOFF + u) = offOf lf S.G.m u := hoff
  rw [GCE.seq_length, ← hR.sp.1, List.sum_toFinset _ hR.sp.2.1]
  show _ = (((List.range v).map fun i => M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2)).map _).sum
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < v := List.mem_range.mp hi
  obtain ⟨-, -, hlo, hhi⟩ := hR.gc_reads hpre hT hI hk hmid hoff' hi'
  show _ - _ = _
  have hrs : ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).nsp = v := rfl
  rw [hlo, hhi, offOf_succ, grp_len_nLca hpre.ok.tree hpre.glob.hG hlf]
  simp

/-- **The precondition of `grpCopyP` in the reset.** -/
theorem RsRun.gcOk (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v) (hs1 : 1 ≤ S.sNK M1 k)
    (hroom : drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) +
      2 * (S.cntK M1 k + ∑ u ∈ S.T.splitSet S.G (S.raw k) (S.thrK k), S.T.nLca S.G u) + 2 < 2 ^ w) :
    ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).Ok w := by
  obtain ⟨lf, hlf, hoff, -⟩ := hpre.glob.lca
  have hoff' : ∀ u ≤ S.T.N, S.mem (S.E.GOFF + u) = offOf lf S.G.m u := hoff
  have hGO : (S.E.GOFF, S.E.N + 1) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have hGP : (S.E.GPR, S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have bO : S.E.GOFF + (S.E.N + 1) ≤ S.h := hpre.below _ hGO
  have bP : S.E.GPR + S.E.m ≤ S.h := hpre.below _ hGP
  have hEN : S.E.N = S.T.N := hpre.glob.N
  have hEm : S.E.m = S.G.m := hpre.glob.m
  have hA : S.h ≤ drawEnd (S.dwE M1 k H) := by
    have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
        (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
    have := S.OUTK_ge M1 H k
    have := S.h_le_HM
    have := S.HM_le_H0
    have := hI.hle
    omega
  have hlen := hR.gc_len hpre hT hI hk hmid
  refine ⟨by omega, fun i hi => ?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · obtain ⟨-, -, hlo, hhi⟩ := hR.gc_reads hpre hT hI hk hmid hoff' hi
    rw [hlo, hhi]; exact offOf_mono (f := lf) (Nat.le_succ _)
  · show drawEnd (S.dwE M1 k H) + 2 + 3 * v ≤ drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) +
      2 * S.cntK M1 k
    omega
  · obtain ⟨hkey, hmem, -, -⟩ := hR.gc_reads hpre hT hI hk hmid hoff' hi
    have hN : M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) < S.T.N := by
      have := hmem; simp only [KT.splitSet, Finset.mem_filter, Finset.mem_range] at this
      exact this.1
    show S.E.GOFF + _ + 1 < drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) + 2 * S.cntK M1 k
    rw [hkey]; omega
  · obtain ⟨-, -, -, hhi⟩ := hR.gc_reads hpre hT hI hk hmid hoff' hi
    have := offOf_le' lf S.G.m (M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) + 1)
    show S.E.GPR + _ ≤ drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) + 2 * S.cntK M1 k
    rw [hhi]; omega
  · show drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) + 2 * (S.cntK M1 k + _) + 2 < 2 ^ w
    rw [hlen]; exact hroom

end CS

end MinCostFlow.LowStretch
