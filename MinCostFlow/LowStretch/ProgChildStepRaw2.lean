module

public import MinCostFlow.LowStretch.ProgChildStepRaw

/-!
# One child that keeps its threshold: the step of the invariant

`CInv.step_raw`: when child `k` is not reset and the memory meets `MidOk`, with other cells
changed only from `OUTK + 2` on, the loop invariant holds for `k + 1`, with the record of the raw
child as record `k`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

theorem sNK_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) : S.sNK M1 k ≤ S.T.N := by
  classical
  rw [← length_nodesK, ← List.toFinset_card_of_nodup ((pre_of hpre).nodesK_nodup k)]
  have : (S.nodesK M1 k).toFinset ⊆ Finset.range S.T.N := fun j hj => by
    obtain ⟨a, ha, rfl⟩ := ((pre_of hpre).nodesK_mem hT hk j).mp (List.mem_toFinset.mp hj)
    exact Finset.mem_range.mpr
      (top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha)) hpre.ok.inv.one_le)
  simpa using Finset.card_le_card this

theorem OUTK_ge (M1 : ℕ → ℕ) (H k : ℕ) : H ≤ S.OUTK M1 H k := by
  unfold OUTK NAK SAK; omega

/-- **The invariant after a child that keeps its threshold.** -/
theorem CInv.step_raw (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hnr : ¬ S.resetQ k) {H' : ℕ} {M' : ℕ → ℕ} (hH' : S.OUTK M1 H k + 2 ≤ H')
    (hsp : H' ≤ H + S.spaceK M1 k)
    (hM' : ∀ a, (a < S.OUTK M1 H k + 2 ∨ H' ≤ a) → M' a = M6 a) (hNw : S.T.N < 2 ^ w) :
    CInv w S M1 (k + 1) H' (Function.update Rs k (S.rawRec M1 k)) M' := by
  have hb := S.h_le_HM
  have hb2 := S.HM_le_H0
  have hH := hI.hle
  have hO := S.OUTK_ge M1 H k
  have hkn : 9 * k + 9 ≤ 9 * S.nch := by omega
  have h1 : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have h2 : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hsN := sNK_le hpre hT hk
  have hkeep : ∀ a, ¬ (H ≤ a ∧ a < H') → ¬ (S.h + 9 * k ≤ a ∧ a < S.h + 9 * k + 9) →
      ¬ S.WrJ k a → M' a = M a := by
    intro a ha hbk hw
    rw [hM' a (by omega)]
    refine hmid.frame a (by omega) hbk (fun u hu he => hw (Or.inr (Or.inr ⟨u, hu, he⟩)))
      (fun i hi he => hw (he ▸ wrJ_of_loc hpre hT hk hi))
  have hcs : S.csOf k = S.raw k := by unfold csOf; rw [if_neg hnr]
  have hnext : Next S.G S.P (S.raw k) (S.csOf k) := by
    rw [hcs]
    refine Or.inl ⟨rfl, ?_⟩
    unfold resetQ at hnr
    by_cases h2 : 2 ≤ (S.raw k).X.card
    · exact Or.inr (by have := hnr; push Not at this; exact this h2)
    · exact Or.inl (by omega)
  have hinv : (S.raw k).Inv S.G S.P :=
    Cl.child_inv hpre.ok.hGo hpre.ok.hB hpre.ok.inv hpre.two hpre.dec hk (by rw [hcs] at hnext; exact hnext)
  have hlab' : ∀ v < S.G.n, M' (S.E.LAB + v) = M (S.E.LAB + v) := fun v hv => by
    rw [hM' _ (by omega)]; exact keep_lab6 hpre hT hI hk hmid hv
  refine ⟨hH.trans (by omega), ?_, fun a ha => ?_, fun a ha => ?_, fun j hj => ?_,
    fun v hv => ?_, fun x hx => ?_, fun u hu => ?_, fun j hj => ?_⟩
  · rw [Finset.sum_range_succ]; have := hI.hspace; omega
  · rw [hkeep a (by omega) (by omega) (fun hw => by
      rcases wrJ_cases hpre hk hw with h | h <;> omega)]
    exact hI.zero a (by omega)
  · have hnw : ¬ S.Wr k H a := fun hw => ha (by
      rcases hw with h | h | ⟨j, hj, hw⟩
      · exact Or.inl ⟨h.1, by omega⟩
      · exact Or.inr (Or.inl ⟨h.1, by omega⟩)
      · exact Or.inr (Or.inr ⟨j, by omega, hw⟩))
    rw [hkeep a (fun h => ha (Or.inr (Or.inl ⟨by omega, h.2⟩)))
      (fun h => ha (Or.inl ⟨by omega, by omega⟩)) (fun hw => ha (Or.inr (Or.inr ⟨k, by omega, hw⟩)))]
    exact hI.frame a hnw
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hjk
    · rw [Function.update_of_ne (by omega)]
      obtain ⟨hn, hok, -, -⟩ := hI.recs j hj
      obtain ⟨hat, hreg⟩ := recs_keep hpre hI hk hkeep hj
      exact ⟨hn, hok, hat, fun r hr => ⟨(hreg r hr).1, by have := hreg r hr; omega⟩⟩
    · rw [hjk, Function.update_self]
      have hat := rawRecAt hpre hT hI hk hmid
      have hbk : ∀ i < 9, M' (S.h + 9 * k + i) = M6 (S.h + 9 * k + i) := fun i hi =>
        hM' _ (by omega)
      have hrd := RecL.read_congr_blk hbk
      have hblk := hmid.blk
      refine ⟨hnext, hcs ▸ (pre_of hpre).rawRec_ok hT hk hinv, ?_, ?_⟩
      · rw [hcs]
        refine RecAt.congr_blk hat hbk (fun r hr a h1 h2 => ?_) (fun p hp => ⟨?_, ?_⟩)
          (fun p hp => ?_) (fun p hp => ?_) (fun v hv => ?_) (fun v hv => ?_)
        · rw [hblk] at hr
          simp only [RecL.regs, blkK, SAK, NAK, OUTK, List.mem_cons, List.mem_nil_iff,
            or_false] at hr
          refine hM' a (Or.inl ?_)
          rcases hr with rfl | rfl | rfl <;> dsimp only at h1 h2 <;> unfold OUTK NAK SAK <;> omega
        all_goals first
          | (have hm : S.E.m = S.G.m := hpre.glob.m
             have hr : (S.E.IN, 3 * S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
               simp [readRegs]
             have hb := hpre.below _ hr
             dsimp only at hb
             exact hM' _ (Or.inl (by omega)))
          | (have hm : S.E.m = S.G.m := hpre.glob.m
             have hr : (S.E.PW, S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
               simp [readRegs]
             have hb := hpre.below _ hr
             dsimp only at hb
             exact hM' _ (Or.inl (by omega)))
          | (have hm : S.E.m = S.G.m := hpre.glob.m
             have hr : (S.E.EXP, S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
               simp [readRegs]
             have hb := hpre.below _ hr
             dsimp only at hb
             exact hM' _ (Or.inl (by omega)))
          | (have := hpre.ok.n_of_mem (Cl.raw_X_subset k hv)
             exact hM' _ (Or.inl (by omega)))
          | skip
        · have hvn := hpre.ok.n_of_mem (Cl.raw_X_subset k hv)
          have := hI.lab v hvn
          rw [keep_lab6 hpre hT hI hk hmid hvn]
          exact hM' _ (Or.inl (by omega))
      · intro r hr
        rw [hrd, hblk] at hr
        simp only [RecL.regs, blkK, SAK, NAK, List.mem_cons, List.mem_nil_iff, or_false] at hr
        unfold OUTK NAK SAK at hH'
        rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
  · rw [hlab' v hv]; exact hI.lab v hv
  · rw [hM' _ (Or.inl (by omega))]
    by_cases hex : ∃ i < S.sNK M1 k, S.E.LOC + x = S.E.LOC + S.T.hd S.G ((S.nodesK M1 k).getD i 0)
    · obtain ⟨i, hi, he⟩ := hex
      rw [he, hmid.loc i hi]
      exact ⟨by omega, Or.inr (by omega)⟩
    · push Not at hex
      rw [hmid.frame _ (by omega) (by omega) (fun u hu => by have := walk_lt hpre hk hu; omega)
        hex]
      exact hI.loc x hx
  · rw [hM' _ (Or.inl (by omega))]
    by_cases hw : u ∈ S.walk k
    · rw [hmid.hm u hw]; unfold rgK; split_ifs <;> omega
    · rw [hmid.frame _ (by omega) (by omega) (fun u' hu' he => hw (by
        have : u = u' := by omega
        exact this ▸ hu')) (fun i _ => by
        have hN := hpre.ok.tree.n_lt
        obtain ⟨a, ha, he⟩ := nodesK_getD hpre hT hk ‹i < S.sNK M1 k›
        have han := hpre.ok.n_of_mem (Cl.raw_X_subset k ha)
        have htN := top_lt_N hpre.ok.tree han hpre.ok.inv.one_le
        have := (hd_under hpre.ok.tree _ htN).lt_N hpre.ok.tree htN
        rw [← he]; omega)]
      exact hI.hm u hu
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hjk
    · rw [Function.update_of_ne (by omega)]; exact hI.stor j hj
    · rw [hjk, Function.update_self]
      show (S.SK M1 k).length ≤ _
      rw [length_SK]; omega

end CS

end MinCostFlow.LowStretch
