module

public import MinCostFlow.LowStretch.ProgResetQ
public import MinCostFlow.LowStretch.ProgSplitPairs

/-!
# The reset of child `k`: its record is in memory

The record of a reset child (`CS.rsRec`) has as nodes the `x`-nodes in column `1` of the split
walk, and as stored pairs, all with flag `0`, the active pairs of key group `k` followed by the
pairs that `grpCopyP` copies; its highway is empty. The copied pairs are the pairs whose lowest
common node is split, each once (`CS.RsRun.seq_facts`). After the record block is written, the
record is in memory (`CS.rsRecAt`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable (S : CS)

/-- **The record of the reset of child `k`**, for `v` split nodes, the memory `M8` after the split
walk and `M11` after `pcP`. -/
noncomputable def rsRec (M1 : ℕ → ℕ) (k H v : ℕ) (M8 M11 : ℕ → ℕ) : Rec :=
  ⟨rdS M8 (drawEnd (S.dwE M1 k H)) 1 (S.sNK M1 k + v),
    (S.SK M1 k).map (fun e => (e.1, 0)) ++
      ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq.map (fun p => (p, 0)), []⟩

variable {S} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}
  {M7 M8 M9 M10 M11 M12 : ℕ → ℕ} {v : ℕ}

/-- The record block after the seven stores of the reset. -/
theorem rsBlk_read (V : RsV) (n m lx : ℕ) (M : ℕ → ℕ) :
    RecL.read (V.rsBlk n m lx M) V.BK =
      ⟨n, m, V.A + 5 * n, lx, V.A + 4 * n, M (V.BK + 5), V.cc, 0, M (V.BK + 8)⟩ := by
  simp [RecL.read, RsV.rsBlk, Function.update_apply]

/-- **The pairs that the reset copies** are the pairs whose lowest common node is split, each
once. -/
theorem RsRun.seq_facts (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v) {lf : ℕ → ℕ}
    (hoff : ∀ u ≤ S.T.N, S.mem (S.E.GOFF + u) = offOf lf S.G.m u)
    (hgpr : ∀ u < S.T.N, ∀ j < (grp lf S.G.m u).length,
      S.mem (S.E.GPR + offOf lf S.G.m u + j) = (grp lf S.G.m u).getD j 0) :
    (∀ p, p ∈ ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq ↔
      p < S.G.m ∧ lf p ∈ S.T.splitSet S.G (S.raw k) (S.thrK k)) ∧
      ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq.Nodup := by
  set E := (S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11 with hE
  have hGO : (S.E.GOFF, S.E.N + 1) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have hGP : (S.E.GPR, S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have hEN : S.E.N = S.T.N := hpre.glob.N
  have hEm : S.E.m = S.G.m := hpre.glob.m
  have hoffE : ∀ u ≤ S.T.N, E.mem0 (E.GOFF + u) = offOf lf S.G.m u := fun u hu => by
    show M11 (S.E.GOFF + u) = _
    rw [hR.keep hpre hT hI hk hmid hGO (i := u) (by dsimp only; omega)]
    exact hoff u hu
  have hgprE : ∀ u < S.T.N, ∀ j < (grp lf S.G.m u).length,
      E.mem0 (E.GPR + offOf lf S.G.m u + j) = (grp lf S.G.m u).getD j 0 := fun u hu j hj => by
    show M11 (S.E.GPR + offOf lf S.G.m u + j) = _
    have h1 := offOf_succ (f := lf) S.G.m u
    have h2 := offOf_le' lf S.G.m (u + 1)
    rw [add_assoc, hR.keep hpre hT hI hk hmid hGP (i := offOf lf S.G.m u + j)
      (by dsimp only; omega), ← add_assoc]
    exact hgpr u hu j hj
  have hkey : ∀ i < E.nsp, E.key i = M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) ∧
      M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) ∈ S.T.splitSet S.G (S.raw k) (S.thrK k) :=
    fun i hi => by
      obtain ⟨a1, a2, -, -⟩ := hR.gc_reads hpre hT hI hk hmid hoff (i := i) hi
      exact ⟨a1, a2⟩
  have hkN : ∀ i < E.nsp, E.key i < S.T.N := fun i hi => by
    obtain ⟨a1, a2⟩ := hkey i hi
    rw [a1]
    simp only [KT.splitSet, Finset.mem_filter, Finset.mem_range] at a2
    exact a2.1
  have hcol : ∀ i (hi : i < v), M8 (drawEnd (S.dwE M1 k H) + 3 * i + 2) =
      (rdS M8 (S.spL M1 k H).A 2 v)[i]'(by rw [rdS_length]; exact hi) := fun i hi => by
    simp [rdS, spL]
  refine ⟨fun p => ?_, GCE.seq_nodup hoffE hgprE hkN fun i hi j hj he => ?_⟩
  · rw [GCE.mem_seq hoffE hgprE hkN]
    refine and_congr_right fun _ => ?_
    rw [← hR.sp.1, List.mem_toFinset, List.mem_iff_getElem]
    constructor
    · rintro ⟨i, hi, he⟩
      refine ⟨i, by rw [rdS_length]; exact hi, ?_⟩
      rw [← hcol i hi, ← (hkey i hi).1, he]
    · rintro ⟨i, hi, he⟩
      rw [rdS_length] at hi
      exact ⟨i, hi, by rw [(hkey i hi).1, hcol i hi, he]⟩
  · have hi' : i < v := hi
    have hj' : j < v := hj
    rw [(hkey i hi).1, (hkey j hj).1, hcol i hi', hcol j hj'] at he
    exact (List.Nodup.getElem_inj_iff hR.sp.2.1).mp he

/-- The cells of the read regions keep their values to the end of the reset. -/
theorem RsRun.keep12 (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v)
    (hd12 : ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).Done M12
      ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq) {n m lx : ℕ} {r : ℕ × ℕ}
    (hr : r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem) {i : ℕ} (hi : i < r.2) :
    (S.rsV M1 k H).rsBlk n m lx M12 (r.1 + i) = S.mem (r.1 + i) := by
  have hb : r.1 + r.2 ≤ S.h := hpre.below r hr
  have hA : S.h ≤ drawEnd (S.dwE M1 k H) := by
    have := drawEnd_ge (S := S) (M1 := M1) (H := H) (k := k)
    have := S.OUTK_ge M1 H k
    have := S.h_le_HM
    have := S.HM_le_H0
    have := hI.hle
    omega
  rw [rsBlk_of_ne (by simp only [rsV]; omega)]
  have e1 : ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).OUT =
    drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) := rfl
  rw [hd12.2 _ (Or.inl (by rw [e1]; omega))]
  exact hR.keep hpre hT hI hk hmid hr hi

/-- Below the stored pairs, the end of the reset agrees with the memory after `ncP`. -/
theorem RsRun.eq10 (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v)
    (hd12 : ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).Done M12
      ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq) {n m lx : ℕ} {a : ℕ}
    (ha : a < drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v))
    (hbk : a < S.h + 9 * k ∨ S.h + 9 * k + 9 ≤ a) :
    (S.rsV M1 k H).rsBlk n m lx M12 a = M10 a := by
  rw [rsBlk_of_ne (by simp only [rsV]; omega)]
  have e1 : ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).OUT =
    drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) := rfl
  rw [hd12.2 _ (Or.inl (by rw [e1]; omega))]
  exact hR.pc.2 _ (Or.inl (by simp only [RsV.rsPcE, rsV]; omega))

end CS

end MinCostFlow.LowStretch
