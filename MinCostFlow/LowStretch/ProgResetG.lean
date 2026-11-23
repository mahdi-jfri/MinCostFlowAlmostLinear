module

public import MinCostFlow.LowStretch.ProgResetF

/-!
# The reset of child `k`: the call of the split walk

The seventh step of `rsB` calls `splitP` on the registers `14`–`21`, `2`, `8`, `9`, `37`. When
these hold the arguments of a layout `E` that meets `SplitPre` for a ghost, the call returns some
`v` and a memory `M'` with `SplitPost … 0`, and it costs at most `splitBd` of that ghost
(`rsSplit_runs`, from `splitC` and `splitCost_le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The registers that `rsB` gives to `splitP`. -/
def rsSpRegs : List ℕ := [14, 15, 16, 17, 18, 19, 20, 21, 2, 8, 9, 37]

/-- **The call of the split walk.** -/
theorem rsSplit_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {I : CIdx} {st : State}
    (fsp : MeetsContract w p I.sp (splitC w)) {T : KT} {G : PG} {r : Cl} {x : ℕ} {E : SplitL}
    (hvs : rsSpRegs.map st.regs = E.args) (hwords : ∀ v ∈ E.args, v < 2 ^ w)
    (P : SplitPre w T G r x E st.mem) {s : Stmt} {Q : Outcome → State → Prop} {k T' : ℕ}
    (hrest : ∀ v M' pos', SplitPost T G r x E st.mem v M' 0 →
      ∃ o st' c, Runs w p ω s { mem := M', regs := Function.update st.regs 38 v, pos := pos' }
        o st' c ∧ Q o st' ∧ k + 14 + splitBd ⟨T, G, r, x⟩ E + c ≤ T') :
    ∃ o st' c, Runs w p ω (.seq (.call 38 I.sp (rgs rsSpRegs)) s) st o st' c ∧ Q o st' ∧
      k + c ≤ T' := by
  refine runs_seq_callR_le fsp hvs hwords ⟨⟨T, G, r, x⟩, E, rfl, P⟩ ?_
  intro v M' pos' hpost
  obtain ⟨o, st', c, hrun, hQ, hc⟩ := hrest v M' pos' (hpost ⟨T, G, r, x⟩ E rfl P)
  have hb := splitCost_le (g := ⟨T, G, r, x⟩) P
  refine ⟨o, st', c, hrun, hQ, ?_⟩
  show k + rsSpRegs.length + splitCost w E.args st.mem + 2 + c ≤ T'
  simp only [rsSpRegs, List.length_cons, List.length_nil] at hc ⊢
  omega

namespace CS

variable {S : CS} {w : ℕ} {M1 : ℕ → ℕ} {k H : ℕ}

/-- **The registers of the split call hold the layout `spL`**, once register `37` holds the
threshold. -/
theorem rsSp_args (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {st : State} (hR : (S.rsV M1 k H).Regs st) (h37 : st.regs 37 = (S.rsV M1 k H).x) :
    rsSpRegs.map st.regs = (S.spL M1 k H).args := by
  rw [rsV_x hpre] at h37
  simp only [rsSpRegs, List.map_cons, List.map_nil, h37, hR 14 (by norm_num), hR 15 (by norm_num),
    hR 16 (by norm_num), hR 17 (by norm_num), hR 18 (by norm_num), hR 19 (by norm_num),
    hR 20 (by norm_num), hR 21 (by norm_num), hR 2 (by norm_num), hR 8 (by norm_num),
    hR 9 (by norm_num)]
  rfl

end CS

end MinCostFlow.LowStretch
