module

public import MinCostFlow.LowStretch.ProgResetS

/-!
# The reset of child `k`: the record meets `Rec.Ok`

The record `CS.rsRec` of a reset child meets `Rec.Ok` for the reset child
(`CS.rsRec_ok`), by `Rec.ok_reset`: its nodes are the `x`-nodes of the child once each, and its
stored pairs are the active pairs inside the child and the pairs whose lowest common node is
split, once each (an active pair is not grouped at a split node, `Rec.Ok.lca_not_split`).

The file also bounds the heap end of the reset by `H + spaceK k` (`CS.rs_end_le`) and the number
of its nodes by `T.N` (`CS.RsNc.n_le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}
  {M7 M8 M9 M10 M11 M12 : ℕ → ℕ} {v : ℕ}

/-- **The record of a reset child meets `Rec.Ok`.** -/
theorem rsRec_ok (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k) (hR : RsRun w S M1 k H M6 M7 M8 M9 M10 M11 v) :
    (S.rsRec M1 k H v M8 M11).Ok S.T S.G S.P ((S.raw k).reset (S.thrK k)) := by
  have hcs : S.csOf k = (S.raw k).reset (S.thrK k) := by unfold csOf; rw [if_pos hq]
  have hn : Next S.G S.P (S.raw k) ((S.raw k).reset (S.thrK k)) := by
    rw [← hcs]; exact next_reset hpre hk hq
  obtain ⟨hx1, hx4⟩ := thrK_le hpre hk hq
  obtain ⟨lf, hlf, hoff, hgpr⟩ := hpre.glob.lca
  obtain ⟨hseq, hseqnd⟩ := hR.seq_facts hpre hT hI hk hmid hoff hgpr
  have hpre' := pre_of hpre
  have hfst : (S.rsRec M1 k H v M8 M11).S.map Prod.fst = (S.SK M1 k).map Prod.fst ++
      ((S.rsV M1 k H).rsGcE v (S.sNK M1 k + v) M11).seq := by
    simp [rsRec, List.map_append, List.map_map, Function.comp_def]
  refine Rec.ok_reset hpre.ok hpre.two hpre.dec hk hn hx1 (by omega) hlf hR.sp.2.2.2.2.1
    (fun j => ?_) ?_ (fun e he => ?_) (fun p => ?_) rfl
  · show j ∈ rdS M8 (S.spL M1 k H).A 1 ((S.spL M1 k H).len0 + v) ↔ _
    rw [hR.sp.2.2.2.1 j]
    exact ⟨fun ⟨a, ha, he⟩ => ⟨a, ha, he.symm⟩, fun ⟨a, ha, he⟩ => ⟨a, ha, he.symm⟩⟩
  · rw [hfst]
    refine List.nodup_append.mpr ⟨hpre'.SK_nodup k, hseqnd, fun p hp q hq' hpq => ?_⟩
    subst hpq
    have h1 := ((hpre'.mem_SK hT hk p).mp hp).1
    have h2 := (hseq p).mp hq'
    exact hpre.ok.lca_not_split h1 (hlf p h2.1) k (S.thrK k) h2.2
  · simp only [rsRec, List.mem_append, List.mem_map] at he
    rcases he with ⟨e', -, rfl⟩ | ⟨p, -, rfl⟩ <;> rfl
  · rw [hfst, List.mem_append, hpre'.mem_SK hT hk p, hseq p]
    rfl

/-- **The heap end of the reset** is at most `H + spaceK k`, when its `v` split nodes and `g`
copied pairs fit in `visK k`. -/
theorem rs_end_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) {v g : ℕ} (hg : v + g ≤ S.visK k) :
    drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) + 2 * (S.cntK M1 k + g) ≤
      H + S.spaceK M1 k := by
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

/-- The reset has at most `T.N` nodes, since they are distinct nodes of the merge tree. -/
theorem RsNc.n_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hk : k < S.nch) (hq : S.resetQ k) (hR : RsNc w S M1 k H M6 M7 M8 M9 M10 v) :
    S.sNK M1 k + v ≤ S.T.N := by
  classical
  have hnd := hR.sp.2.2.2.2.1
  have hx1 := (thrK_le hpre hk hq).1
  set l := rdS M8 (S.spL M1 k H).A 1 ((S.spL M1 k H).len0 + v)
  have hl : l.length = S.sNK M1 k + v := rdS_length _ _ _ _
  rw [← hl, ← List.toFinset_card_of_nodup hnd]
  have : l.toFinset ⊆ Finset.range S.T.N := fun j hj => by
    obtain ⟨a, ha, rfl⟩ := (hR.sp.2.2.2.1 j).mp (List.mem_toFinset.mp hj)
    exact Finset.mem_range.mpr
      (top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha)) hx1)
  simpa using Finset.card_le_card this

end CS

end MinCostFlow.LowStretch
