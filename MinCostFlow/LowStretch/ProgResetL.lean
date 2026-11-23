module

public import MinCostFlow.LowStretch.ProgResetK

/-!
# The reset of child `k`: the whole run of `rsP`

This file chains the runs of the parts of `rsP` (`rsP_runs`): the loads (`rsPro_runs`), the new
threshold (`rsThr_runs`), the split walk (`rsSplit_runs`), the index list (`rsIota_runs`), the
nodes (`rsNc_runs`) and the stored pairs with the record block (`rsTail_runs`).

The lemma is stated for any words `V` of `rsP` and any layout `E` of the split walk. The facts that
depend on the child (the preconditions of `ncP`, `pcP` and `grpCopyP`, and the room for the index
list) are hypotheses, each stated on the memories that the run has reached at that point. The
memories are `M` at the start, `M8` after the split walk, `M9` after `iotaP`, `M10` after `ncP`,
`M11` after `pcP` and `M12` after `grpCopyP`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- What `iotaP` leaves in the reset, for `n` nodes: the index list at `A + 3 n`, and the other
cells unchanged. -/
def RsIota (A n : ℕ) (M8 M9 : ℕ → ℕ) : Prop :=
  (∀ i < n, M9 (A + 3 * n + i) = 3 * i + 1) ∧
    ∀ a, (a < A + 3 * n ∨ A + 3 * n + n ≤ a) → M9 a = M8 a

set_option maxHeartbeats 2000000 in
/-- **The run of `rsP`.** -/
theorem rsP_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {I : CIdx}
    (flg : MeetsContract w p I.lg (log2C w)) (fsp : MeetsContract w p I.sp (splitC w))
    (fio : MeetsContract w p I.io (iotaC w)) (fnc : MeetsContract w p I.nc (ncC w))
    (fpc : MeetsContract w p I.pc (pcC w)) (fgc : MeetsContract w p I.gc (grpCopyC w))
    {V : RsV} {M : ℕ → ℕ} {pos : ℕ} (hF : RsFacts w V M)
    (hΔ : V.Δ < 2 ^ w) (hμ : V.μ < 2 ^ w) (hb : 4 * V.B * V.sz < 2 ^ w)
    (hb1 : 1 ≤ 4 * V.B * V.sz) (hw2 : 2 ≤ w)
    (hw : ∀ x ∈ V.args ++ [V.SRCK, V.ACT, V.IN, V.LAB, V.LOC, V.HM, V.PP, V.GOFF, V.GPR], x < 2 ^ w)
    (hHw : V.HEAD < 2 ^ w) (hBK : V.BK + 7 < 2 ^ w)
    {T : KT} {G : PG} {r : Cl} {E : SplitL}
    (hE : E.args = [V.CH1, V.CH2, V.MW, V.SZ, V.LO, V.ORDL, V.LAB, V.n, V.A, V.NA, V.sN, V.x])
    (hEw : ∀ v ∈ E.args, v < 2 ^ w) (P : SplitPre w T G r V.x E M) {N : ℕ}
    (hio : ∀ v M8, SplitPost T G r V.x E M v M8 0 → V.A + 5 * (V.sN + v) + 1 < 2 ^ w)
    (hnc : ∀ v M8 M9, SplitPost T G r V.x E M v M8 0 → RsIota V.A (V.sN + v) M8 M9 →
      (CS.rsNcE V.A (V.sN + v) V.HEAD V.LOC M9).Ok w N)
    (hpc : ∀ v M8 M9 M10, SplitPost T G r V.x E M v M8 0 → RsIota V.A (V.sN + v) M8 M9 →
      (CS.rsNcE V.A (V.sN + v) V.HEAD V.LOC M9).Done (V.sN + v) M10 →
      (V.rsPcE (V.sN + v) M10).Ok w)
    (hgc : ∀ v M8 M9 M10 M11, SplitPost T G r V.x E M v M8 0 → RsIota V.A (V.sN + v) M8 M9 →
      (CS.rsNcE V.A (V.sN + v) V.HEAD V.LOC M9).Done (V.sN + v) M10 →
      (V.rsPcE (V.sN + v) M10).Done V.cnt M11 → (V.rsGcE v (V.sN + v) M11).Ok w)
    {Q : Outcome → State → Prop} {T' : ℕ}
    (hfin : ∀ v M8 M9 M10 M11 M12 pos', SplitPost T G r V.x E M v M8 0 →
      RsIota V.A (V.sN + v) M8 M9 →
      (CS.rsNcE V.A (V.sN + v) V.HEAD V.LOC M9).Done (V.sN + v) M10 →
      (V.rsPcE (V.sN + v) M10).Done V.cnt M11 →
      (V.rsGcE v (V.sN + v) M11).Done M12 (V.rsGcE v (V.sN + v) M11).seq →
      ∀ regs, Q (.returned (V.A + 5 * (V.sN + v) +
          2 * (V.cnt + (V.rsGcE v (V.sN + v) M11).seq.length)))
        { mem := V.rsBlk (V.sN + v) (V.cnt + (V.rsGcE v (V.sN + v) M11).seq.length) V.lx M12,
          regs := regs, pos := pos' } ∧
      800 + log2Cost (V.S / (4 * V.B * V.sz)) + splitBd ⟨T, G, r, V.x⟩ E + 90 * (V.sN + v) +
        200 * V.cnt + 60 * ((V.rsGcE v (V.sN + v) M11).seq.length + v) ≤ T') :
    ∃ o st' c, Runs w p ω (rsP I) (startState V.args M pos) o st' c ∧ Q o st' ∧ c ≤ T' := by
  have hw3 := hF.bw
  refine rsPro_runs hF (fun st hR hM => ?_)
  unfold rsB
  refine rsThr_runs flg hR hΔ hμ hb hb1 hw2 (fun st1 hM1 hr1 _ h36 h37 => ?_)
  have hR1 : V.Regs st1 := fun r hr => by rw [hr1 r hr]; exact hR r hr
  rw [hM] at hM1
  have hvs : rsSpRegs.map st1.regs = E.args := by
    rw [hE]
    simp only [rsSpRegs, List.map_cons, List.map_nil, h37, hR1 14 (by norm_num),
      hR1 15 (by norm_num), hR1 16 (by norm_num), hR1 17 (by norm_num), hR1 18 (by norm_num),
      hR1 19 (by norm_num), hR1 20 (by norm_num), hR1 21 (by norm_num), hR1 2 (by norm_num),
      hR1 8 (by norm_num), hR1 9 (by norm_num)]
    rfl
  refine rsSplit_runs fsp hvs hEw (hM1 ▸ P) (fun v M8 pos8 hsp => ?_)
  rw [hM1] at hsp
  set st2 : State := { mem := M8, regs := Function.update st1.regs 38 v, pos := pos8 } with hst2
  have hR2 : V.Regs st2 := fun r hr => by
    simp only [st2, Function.update_apply]; rw [if_neg (by omega)]; exact hR1 r hr
  have h36' : st2.regs 36 = V.lx := by simp [st2, h36]
  have hroom := hio v M8 hsp
  refine rsIota_runs (v := v) fio hR2 (by simp [st2]) (by omega) hw3
    (fun st3 hr3 h38 h39 h40 h42 hidx hfr => ?_)
  have hR3 : V.Regs st3 := fun r hr => by rw [hr3 r (by omega)]; exact hR2 r hr
  have hio' : RsIota V.A (V.sN + v) M8 st3.mem := ⟨hidx, hfr⟩
  refine rsNc_runs fnc hR3 h39 h40 h42 hHw (hnc v M8 st3.mem hsp hio') (fun u M10 pos10 hd => ?_)
  set st4 : State := { mem := M10, regs := Function.update st3.regs 41 u, pos := pos10 } with hst4
  have hR4 : V.Regs st4 := fun r hr => by
    simp only [st4, Function.update_apply]; rw [if_neg (by omega)]; exact hR3 r hr
  have e36 : st4.regs 36 = V.lx := by simp only [st4, Function.update_apply]; simp [hr3 36 (by norm_num), h36']
  have e38 : st4.regs 38 = v := by simp [st4, h38]
  have e39 : st4.regs 39 = V.sN + v := by simp [st4, h39]
  have e42 : st4.regs 42 = V.A + 4 * (V.sN + v) := by simp [st4, h42]; omega
  refine rsTail_runs fpc fgc hR4 e36 e38 e39 (by omega) e42 (hpc v M8 st3.mem M10 hsp hio' hd)
    (fun M11 hd11 => hgc v M8 st3.mem M10 M11 hsp hio' hd hd11) hw hBK
    (fun M11 M12 pos' hd11 hd12 regs => ?_)
  obtain ⟨hq, hc⟩ := hfin v M8 st3.mem M10 M11 M12 pos' hsp hio' hd hd11 hd12 regs
  exact ⟨hq, by omega⟩

end MinCostFlow.LowStretch
