module

public import MinCostFlow.LowStretch.ProgResetT

/-!
# The reset of child `k`: the step of the invariant

`CInv.step_reset`: when child `k` is reset and the reset ends as `RsEnd` says, the loop invariant
holds for `k + 1`, with the record `CS.rsRec` of the reset child as record `k`. As in
`CInv.step_raw`, the reset writes only the cells of child `k` (`CS.WrJ k`), its record block and
the heap from `H` on (`RsEnd.frame`). The record is in memory by `rsRecAt` and meets `Rec.Ok` by
`rsRec_ok`; it stores the active pairs of key group `k` and the `Σ nLca` pairs grouped at the
split nodes, which `visK k` pays for (`rs_vis_le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

set_option maxHeartbeats 1000000 in
/-- **The invariant after a child that is reset.** -/
theorem CInv.step_reset (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k) {M7 M' : ℕ → ℕ} {H' : ℕ}
    (h7 : ∀ a, (a < S.OUTK M1 H k + 2 ∨ drawEnd (S.dwE M1 k H) ≤ a) → M7 a = M6 a)
    (hE : S.RsEnd w M1 k H M6 M7 (.returned H') M') (hNw : S.T.N < 2 ^ w) :
    ∃ R', CInv w S M1 (k + 1) H' (Function.update Rs k R') M' := by
  have hE' := hE
  obtain ⟨v, M8, M9, M10, M11, M12, hR, hd12, hM', ho⟩ := hE'
  have hH' := Outcome.returned.inj ho
  have hb := S.h_le_HM
  have hb2 := S.HM_le_H0
  have hH := hI.hle
  have hO := S.OUTK_ge M1 H k
  have hend := drawEnd_ge (S := S) (M1 := M1) (H := H) (k := k)
  have hkn : 9 * k + 9 ≤ 9 * S.nch := by omega
  have h1 : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have h2 : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hll : RegDisj (S.E.LAB, S.G.n) (S.E.LOC, S.T.N) := hpre.lab_loc
  unfold RegDisj at hll
  dsimp only at hll
  have hN := hpre.ok.tree.n_lt
  have hvis := rs_vis_le hq hR.sp
  have hg := hR.gc_len hpre hT hI hk hmid
  set A := drawEnd (S.dwE M1 k H) with hA
  set n := S.sNK M1 k + v with hn
  set g := ((S.rsV M1 k H).rsGcE v n M11).seq.length with hgd
  have hsp : H' ≤ H + S.spaceK M1 k := by
    rw [hH']; exact rs_end_le hpre hT hk (g := g) (by omega)
  have hcs : S.csOf k = (S.raw k).reset (S.thrK k) := by unfold csOf; rw [if_pos hq]
  have hhd : ∀ u, u < S.T.N → S.T.hd S.G u < S.T.N := fun u hu =>
    (hd_under hpre.ok.tree u hu).lt_N hpre.ok.tree hu
  -- the cells that the reset keeps
  have hkeep : ∀ a, ¬ (H ≤ a ∧ a < H') → ¬ (S.h + 9 * k ≤ a ∧ a < S.h + 9 * k + 9) →
      ¬ S.WrJ k a → M' a = M a := by
    intro a ha hbk hw
    rw [RsEnd.frame hpre hT hI hk hmid hq h7 hE (by omega) (by omega)
      (fun b hb he => hw (Or.inl ⟨b, hb, he⟩))
      (fun b hb u hu hut he => hw (Or.inr (Or.inl ⟨b, hb, u, hu, hut, he⟩)))]
    exact hmid.frame a (by omega) hbk (fun u hu he => hw (Or.inr (Or.inr ⟨u, hu, he⟩)))
      (fun i hi he => hw (he ▸ wrJ_of_loc hpre hT hk hi))
  -- a cell below the heap that is neither a label nor a local index
  have hfr6 : ∀ a, a < S.OUTK M1 H k + 2 → (a < S.h + 9 * k ∨ S.h + 9 * k + 9 ≤ a) →
      (a < S.E.LAB ∨ S.E.LAB + S.G.n ≤ a) → (a < S.E.LOC ∨ S.E.LOC + S.T.N ≤ a) →
      M' a = M6 a := fun a ha hbk hl hc =>
    RsEnd.frame hpre hT hI hk hmid hq h7 hE (Or.inl ha) hbk
      (fun b hb => by have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb); omega)
      (fun b hb u hu _ => by
        have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb)
        have huN : u < S.T.N := hu.lt_N hpre.ok.tree (by omega)
        have := hhd u huN
        omega)
  -- the block of the record
  have hrd : RecL.read M' (S.h + 9 * k) =
      ⟨n, S.cntK M1 k + g, A + 5 * n, (S.rsV M1 k H).lx, A + 4 * n, M12 (S.h + 9 * k + 5),
        S.mem (S.X.CC + k), 0, M12 (S.h + 9 * k + 8)⟩ := by
    rw [hM']; exact rsBlk_read (S.rsV M1 k H) _ _ _ _
  have hHW : M12 (S.h + 9 * k + 8) = H := by
    rw [hR.frame12 hpre hT hI hk hmid hq h7 hd12 (Or.inl (by omega)) (fun b hb => by
        have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb); omega)
      (fun b hb u hu _ => by
        have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb)
        have huN : u < S.T.N := hu.lt_N hpre.ok.tree (by omega)
        have := hhd u huN
        omega)]
    have := congrArg RecL.HW hmid.blk
    simp only [RecL.read, blkK] at this
    exact this
  have hlen : (S.rsRec M1 k H v M8 M11).S.length = S.cntK M1 k + g := by
    show ((S.SK M1 k).map (fun e : ℕ × ℕ => (e.1, 0)) ++
      ((S.rsV M1 k H).rsGcE v n M11).seq.map (fun p => (p, 0))).length = _
    rw [List.length_append, List.length_map, List.length_map, length_SK]
  refine ⟨S.rsRec M1 k H v M8 M11, hH.trans (by omega), ?_, fun a ha => ?_, fun a ha => ?_,
    fun j hj => ?_, fun x hx => ?_, fun x hx => ?_, fun u hu => ?_, fun j hj => ?_⟩
  · rw [Finset.sum_range_succ]; have := hI.hspace; omega
  · -- zero
    rw [RsEnd.frame hpre hT hI hk hmid hq h7 hE (Or.inr ha) (by omega)
      (fun b hb => by have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb); omega)
      (fun b hb u hu _ => by
        have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb)
        have huN : u < S.T.N := hu.lt_N hpre.ok.tree (by omega)
        have := hhd u huN
        omega)]
    exact zero_mid hpre hT hI hk hmid a (by omega)
  · -- frame
    have hnw : ¬ S.Wr k H a := fun hw => ha (by
      rcases hw with h | h | ⟨j, hj, hw⟩
      · exact Or.inl ⟨h.1, by omega⟩
      · exact Or.inr (Or.inl ⟨h.1, by omega⟩)
      · exact Or.inr (Or.inr ⟨j, by omega, hw⟩))
    rw [hkeep a (fun h => ha (Or.inr (Or.inl ⟨by omega, h.2⟩)))
      (fun h => ha (Or.inl ⟨by omega, by omega⟩)) (fun hw => ha (Or.inr (Or.inr ⟨k, by omega, hw⟩)))]
    exact hI.frame a hnw
  · -- the records
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hjk
    · rw [Function.update_of_ne (by omega)]
      obtain ⟨hn', hok, -, -⟩ := hI.recs j hj
      obtain ⟨hat, hreg⟩ := recs_keep hpre hI hk hkeep hj
      exact ⟨hn', hok, hat, fun r hr => ⟨(hreg r hr).1, by have := hreg r hr; omega⟩⟩
    · rw [hjk, Function.update_self, hcs]
      refine ⟨hcs ▸ next_reset hpre hk hq, rsRec_ok hpre hT hI hk hmid hq hR, ?_, ?_⟩
      · rw [hM']; exact rsRecAt hpre hT hI hk hmid hq h7 hR hd12
      · intro r hr
        rw [hrd] at hr
        simp only [RecL.regs, List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega
  · -- the labels
    by_cases hv : x ∈ (S.raw k).X
    · rw [hM', hR.eq10 hd12 (by omega) (by omega), (hR.lab_loc hpre hT hI hk hmid hq hv).1]
      exact hhd _ (top_lt_N hpre.ok.tree hx (thrK_le hpre hk hq).1)
    · rw [RsEnd.frame hpre hT hI hk hmid hq h7 hE (Or.inl (by omega)) (by omega)
        (fun b hb he => hv (by have : x = b := by omega
                               exact this ▸ hb))
        (fun b hb u hu _ => by
          have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb)
          have huN : u < S.T.N := hu.lt_N hpre.ok.tree (by omega)
          have := hhd u huN
          omega), keep_lab6 hpre hT hI hk hmid hx]
      exact hI.lab x hx
  · -- the local indices
    by_cases hex : ∃ i < n, x = (rsNcE A n S.E.HEAD S.E.LOC M9).hd i
    · obtain ⟨i, hi, rfl⟩ := hex
      have hnN := hR.toRsNc.n_le hpre hk hq
      have e : M10 (S.E.LOC + (rsNcE A n S.E.HEAD S.E.LOC M9).hd i) = i := hR.nc.2.1 i hi
      rw [hM', hR.eq10 hd12 (by omega) (by omega), e]
      exact ⟨by omega, Or.inr (by omega)⟩
    · push Not at hex
      have e10 : M' (S.E.LOC + x) = M6 (S.E.LOC + x) := by
        rw [hM', hR.eq10 hd12 (by omega) (by omega), hR.nc.2.2 _ (fun hout => by
          rcases hout with ⟨h1', -⟩ | ⟨i, hi, he⟩
          · simp only [rsNcE] at h1'; omega
          · exact hex i hi (by
              have he' : S.E.LOC + x = S.E.LOC + (rsNcE A n S.E.HEAD S.E.LOC M9).hd i := he
              omega))]
        show M9 _ = _
        rw [hR.io.2 _ (Or.inl (by omega)), hR.sp.2.2.2.2.2.2.1 _ (by simp only [spL]; omega)
          (fun b hb => by
            have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb); simp only [spL]; omega),
          h7 _ (Or.inl (by omega))]
      rw [e10]
      by_cases hex2 : ∃ i < S.sNK M1 k,
          S.E.LOC + x = S.E.LOC + S.T.hd S.G ((S.nodesK M1 k).getD i 0)
      · obtain ⟨i, hi, he⟩ := hex2
        rw [he, hmid.loc i hi]
        have := sNK_le hpre hT hk
        exact ⟨by omega, Or.inr (by omega)⟩
      · push Not at hex2
        rw [hmid.frame _ (by omega) (by omega) (fun u hu => by have := walk_lt hpre hk hu; omega)
          hex2]
        exact hI.loc x hx
  · -- the highway marks
    rw [hfr6 _ (by omega) (by omega) (by omega) (by omega)]
    by_cases hw : u ∈ S.walk k
    · rw [hmid.hm u hw]; unfold rgK; split_ifs <;> omega
    · rw [hmid.frame _ (by omega) (by omega) (fun u' hu' he => hw (by
        have : u = u' := by omega
        exact this ▸ hu')) (fun i _ => by
        obtain ⟨a, ha, he⟩ := nodesK_getD hpre hT hk ‹i < S.sNK M1 k›
        have han := hpre.ok.n_of_mem (Cl.raw_X_subset k ha)
        have htN := top_lt_N hpre.ok.tree han hpre.ok.inv.one_le
        have := hhd _ htN
        rw [← he]; omega)]
      exact hI.hm u hu
  · -- the stored pairs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hjk
    · rw [Function.update_of_ne (by omega)]; exact hI.stor j hj
    · rw [hjk, Function.update_self, hlen]; omega

end CS

end MinCostFlow.LowStretch
