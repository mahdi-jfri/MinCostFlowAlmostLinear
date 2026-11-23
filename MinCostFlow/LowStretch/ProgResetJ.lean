module

public import MinCostFlow.LowStretch.ProgResetI

/-!
# The reset of child `k`: the call of `ncP`

After the index list, `rsB` calls `ncP` on the registers `[39, 40, 2, 22, 23, 42]`, which hold
`[cnt, IDX, A, HEAD, LOC, IDX + cnt]` with `IDX = A + 3 cnt` (`rsNc_runs`).

The precondition of the call (`CS.rsNcPre`) comes from `CS.rsNcOk`. Its facts on the memory `M9`
after `iotaP` come from the facts on the memory `M8` after the split walk: `iotaP` writes only
`[IDX, IDX + cnt)`, which lies above the work array `[A, IDX)`, so column `1` is the same in `M8`
and `M9`. The head array lies below `h ≤ A` and does not meet the labels, so the split walk keeps
it (`SplitPost`, part 7), and so does everything before the split walk (`keep_safe`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

/-- **The call of `ncP` in the reset.** -/
theorem rsNc_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {I : CIdx} {V : RsV} {st : State}
    (fnc : MeetsContract w p I.nc (ncC w)) (hR : V.Regs st) {cnt N : ℕ}
    (h39 : st.regs 39 = cnt) (h40 : st.regs 40 = V.A + 3 * cnt)
    (h42 : st.regs 42 = V.A + 3 * cnt + cnt) (hHw : V.HEAD < 2 ^ w)
    (hok : (CS.rsNcE V.A cnt V.HEAD V.LOC st.mem).Ok w N) {s : Stmt}
    {Q : Outcome → State → Prop} {k T : ℕ}
    (hrest : ∀ v M' pos', (CS.rsNcE V.A cnt V.HEAD V.LOC st.mem).Done cnt M' →
      ∃ o st' c, Runs w p ω s { mem := M', regs := Function.update st.regs 41 v, pos := pos' }
        o st' c ∧ Q o st' ∧ k + 68 + 60 * cnt + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call 41 I.nc (rgs [39, 40, 2, 22, 23, 42])) s) st o st' c ∧
      Q o st' ∧ k + c ≤ T := by
  have room := hok.room
  have hloc := hok.loc
  simp only [CS.rsNcE] at room hloc
  have hvs : [39, 40, 2, 22, 23, 42].map st.regs = (CS.rsNcE V.A cnt V.HEAD V.LOC st.mem).args := by
    simp only [List.map_cons, List.map_nil, h39, h40, h42, hR 2 (by norm_num),
      hR 22 (by norm_num), hR 23 (by norm_num)]
    rfl
  refine runs_seq_callR_le fnc hvs ?_ ⟨_, N, rfl, rfl, hok⟩ ?_
  · simp only [CS.rsNcE, NCE.args, List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl) <;> omega
  intro v M' pos' hpost
  refine runs_exists_mono (hrest v M' pos' (hpost _ rfl rfl)) ?_
  simp only [ncC, CS.rsNcE, NCE.args, List.getD_cons_zero, List.length_cons, List.length_nil]
  omega

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- **The precondition of `ncP` in the reset**, on the memory `M9` after `iotaP`. Here `M7` is
the memory at the split call, `M8` the memory after it, and `v` the number of split nodes. -/
theorem rsNcPre (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    (hq : S.resetQ k) {M7 M8 M9 : ℕ → ℕ} (h7 : ∀ a, a < S.OUTK M1 H k + 2 → M7 a = M6 a) {v : ℕ}
    (hsp : SplitPost S.T S.G (S.raw k) (S.thrK k) (S.spL M1 k H) M7 v M8 0)
    (hidx : ∀ i < S.sNK M1 k + v,
      M9 (drawEnd (S.dwE M1 k H) + 3 * (S.sNK M1 k + v) + i) = 3 * i + 1)
    (hfr : ∀ a, (a < drawEnd (S.dwE M1 k H) + 3 * (S.sNK M1 k + v) ∨
      drawEnd (S.dwE M1 k H) + 3 * (S.sNK M1 k + v) + (S.sNK M1 k + v) ≤ a) → M9 a = M8 a)
    (hroom : drawEnd (S.dwE M1 k H) + 5 * (S.sNK M1 k + v) + 1 < 2 ^ w) :
    (rsNcE (drawEnd (S.dwE M1 k H)) (S.sNK M1 k + v) S.E.HEAD S.E.LOC M9).Ok w S.T.N := by
  obtain ⟨-, -, -, hcol, hnd, -, hlow, -, -⟩ := hsp
  have hle := hI.hle
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hHM := S.HM_le_H0
  have hO : H ≤ S.OUTK M1 H k := S.OUTK_ge M1 H k
  have hend : S.OUTK M1 H k + 2 ≤ drawEnd (S.dwE M1 k H) := by
    have e : drawEnd (S.dwE M1 k H) = S.OUTK M1 H k + 2 + 16 * S.cntK M1 k + 8 * S.sNK M1 k + 9 +
        (3 + 4 * S.E.J + 2 * S.E.J * (2 * S.cntK M1 k + S.sNK M1 k + 1)) + 2 := rfl
    omega
  set A := drawEnd (S.dwE M1 k H) with hA
  set cnt := S.sNK M1 k + v with hcnt
  -- column `1` is the same in `M8` and `M9`
  have e1 : rdS M9 A 1 cnt = rdS M8 A 1 cnt :=
    rdS_congr fun i hi => hfr _ (Or.inl (by omega))
  have hcol' : ∀ j, j ∈ rdS M9 A 1 cnt ↔ ∃ a ∈ (S.raw k).X, j = S.T.top (S.thrK k) a := by
    rw [e1]; exact hcol
  have hnd' : (rdS M9 A 1 cnt).Nodup := by rw [e1]; exact hnd
  -- the head array is unchanged
  have hHD : (S.E.HEAD, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have bH : S.E.HEAD + S.E.N ≤ S.h := hpre.below _ hHD
  have dH : RegDisj (S.E.HEAD, S.E.N) (S.E.LAB, S.G.n) := hpre.lab_disj _ hHD
  unfold RegDisj at dH
  dsimp only at bH dH
  have hEN : S.E.N = S.T.N := hpre.glob.N
  have hhd : ∀ j < S.T.N, M9 (S.E.HEAD + j) = S.T.hd S.G j := fun j hj => by
    rw [hfr _ (Or.inl (by omega)), hlow _ (by show _ < A; omega) (fun b hb => by
        have := hpre.ok.n_of_mem (Cl.raw_X_subset k hb)
        show S.E.HEAD + j ≠ S.E.LAB + b
        omega),
      h7 _ (by omega), keep_safe hpre hT hI hk hmid (safe_reg hpre hHD (i := j) (by omega))]
    exact hpre.glob.hd j hj
  exact rsNcOk hpre (thrK_le hpre hk hq).1 (by omega) hidx hcol' hnd' hhd (by omega)

end CS

end MinCostFlow.LowStretch
