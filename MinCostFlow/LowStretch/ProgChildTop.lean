module

public import MinCostFlow.LowStretch.ProgChildTopLoop

/-!
# The child step meets its contract

The child step `childP` loads the block sizes (`CS.topPro_runs`), fills the scratch arrays with
four calls (`CS.topCalls_runs`), runs the loop over the children (`CS.topLoop_runs`) and returns
the heap pointer. The loop starts from the invariant `CInv` before child `0` (`CS.cinv_zero`),
and `CInv` after the last child gives `ChildPost` (`CS.childPost_of`). So `childP` meets
`MeetsChild` (`childP_meetsChild`), when the procedures it calls meet their contracts.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable {S : CS} {w : ℕ} {M1 : ℕ → ℕ}

/-- **The invariant before the first child**: nothing is written yet past the scratch arrays. -/
theorem cinv_zero (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) : CInv w S M1 0 S.H0 (fun _ => S.R) M1 := by
  have hb := S.HM_le_H0
  have hLA : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hLO : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  refine ⟨le_rfl, by simp, fun a ha => hT.zero a (by omega), fun a _ => rfl,
    fun j hj => absurd hj (Nat.not_lt_zero _), fun v hv => ?_, fun x hx => ?_,
    fun u _ => ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · rw [hT.low _ (by omega)]
    exact hpre.lab_lt v hv
  · rw [hT.low _ (by omega)]
    exact ⟨hpre.loc_w x hx, Or.inl rfl⟩
  · rw [hT.zero _ (by omega)]
    omega

/-- **The postcondition**, from the invariant after the last child. -/
theorem childPost_of (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) {H : ℕ} {Rs : ℕ → Rec} {M : ℕ → ℕ} (hI : CInv w S M1 S.nch H Rs M)
    {c : ℕ} (hc : c ≤ childCost S.T S.G S.P S.c S.R S.D S.csOf S.E.J) :
    ChildPost S.T S.G S.P S.c S.R S.D S.E S.h S.mem H M c := by
  have hb := S.h_le_HM
  have hb2 := S.HM_le_H0
  have hle := hI.hle
  have hn : S.D.nch = S.nch := rfl
  refine ⟨S.csOf, Rs, fun k hk => ?_, by omega, hI.zero, fun a ha hw => ?_, ?_, hc,
    fun x hx _ => hI.lab x hx, fun x hx => (hI.loc x hx).2, stor_sum hpre hI⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hI.recs k hk
    exact ⟨h1, h2, h3, fun r hr => ⟨by have := (h4 r hr).1; omega, (h4 r hr).2⟩⟩
  · rw [hI.frame a ?_, hT.low a ha]
    rintro (⟨h1, -⟩ | ⟨h1, -⟩ | ⟨j, -, hw'⟩)
    · omega
    · omega
    · rcases hw' with ⟨v, hv, rfl⟩ | ⟨v, hv, u, hu, hut, rfl⟩ | ⟨u, -, rfl⟩
      · exact hw (Or.inl ⟨v, Cl.raw_X_subset j hv, rfl⟩)
      · exact hw (Or.inr ⟨v, Cl.raw_X_subset j hv, u, hu, hut, rfl⟩)
      · omega
  · have := hI.hspace
    have := top_space_le hpre M1
    omega

/-- **The run of the child step.** -/
theorem childP_runs {p : Program} {ω : ℕ → Bool} {I : CIdx}
    (fone : p.procs[I.one]? = some (oneP I)) (frs : p.procs[I.rs]? = some (rsP I))
    (fhw : MeetsContract w p I.hw (hwC w)) (fpc : MeetsContract w p I.pc (pcC w))
    (fnc : MeetsContract w p I.nc (ncC w)) (fsm : MeetsContract w p I.sm (smC w))
    (fdr : MeetsContract w p I.dr (drawC w)) (flg : MeetsContract w p I.lg (log2C w))
    (fsp : MeetsContract w p I.sp (splitC w)) (fio : MeetsContract w p I.io (iotaC w))
    (fgc : MeetsContract w p I.gc (grpCopyC w)) (fcx : MeetsContract w p I.cx (chxC w))
    (fcsr : MeetsContract w p I.csr (csrC w)) (fkey : MeetsContract w p I.key (keyC w))
    (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) (pos : ℕ) :
    ∃ o st' c, Runs w p ω (childP I) (startState S.topArgs S.mem pos) o st' c ∧
      ChildPost S.T S.G S.P S.c S.R S.D S.E S.h S.mem o.value st'.mem c := by
  have hb : S.H0 + S.nch + 4 < 2 ^ w := by have := top_room hpre (fun _ => 0); omega
  suffices h : ∃ o st' c, Runs w p ω (assigns topPro (topB I)) (startState S.topArgs S.mem pos)
      o st' c ∧ (∃ M1 H Rs, TopOk S M1 ∧ o = .returned H ∧ CInv w S M1 S.nch H Rs st'.mem) ∧
        c ≤ childCost S.T S.G S.P S.c S.R S.D S.csOf S.E.J by
    obtain ⟨o, st', c, hrun, ⟨M1, H, Rs, hT, rfl, hI⟩, hc⟩ := h
    exact ⟨_, st', c, hrun, childPost_of hpre hT hI hc⟩
  refine topPro_runs hpre hb (fun st hR hM => ?_)
  unfold topB
  refine topCalls_runs fcx fcsr fkey hpre hb hR hM (A := 300) (fun st' hR' hT => ?_)
  obtain ⟨o, st'', c, hrun, rfl, ⟨H, Rs, h26, hI⟩, hc⟩ := topLoop_runs (p := p) (ω := ω) (I := I)
    fone fhw fpc fnc fsm fdr frs flg fsp fio fgc hpre hT (st := st')
    ⟨Nat.zero_le _, fun r hr => hR' r (by omega), hR' 25 (by decide), S.H0, fun _ => S.R,
      hR' 26 (by decide), cinv_zero hpre hT⟩
  refine ⟨_, _, _, runs_seq_iff.mpr (Or.inr ⟨st'', c, _, hrun,
    runs_ret_iff.mpr ⟨H, Expr.eval_reg_of_eq h26, rfl, rfl, rfl⟩, rfl⟩),
    ⟨st'.mem, H, Rs, hT, rfl, hI⟩, ?_⟩
  have h1 := top_cost_le hpre st'.mem
  have h2 : S.loopRem st'.mem 0 = ∑ k ∈ Finset.range S.nch, (S.costK st'.mem k + 100) + 10 := by
    unfold loopRem
    rw [Finset.range_eq_Ico]
  have h3 : (Expr.reg 26).size ≤ 5 := by decide
  omega

end CS

/-- **The child step meets its contract**, when the procedures it calls meet theirs. -/
theorem childP_meetsChild {w : ℕ} {p : Program} {f : ℕ} {I : CIdx}
    (hf : p.procs[f]? = some (childP I))
    (fone : p.procs[I.one]? = some (oneP I)) (frs : p.procs[I.rs]? = some (rsP I))
    (fhw : MeetsContract w p I.hw (hwC w)) (fpc : MeetsContract w p I.pc (pcC w))
    (fnc : MeetsContract w p I.nc (ncC w)) (fsm : MeetsContract w p I.sm (smC w))
    (fdr : MeetsContract w p I.dr (drawC w)) (flg : MeetsContract w p I.lg (log2C w))
    (fsp : MeetsContract w p I.sp (splitC w)) (fio : MeetsContract w p I.io (iotaC w))
    (fgc : MeetsContract w p I.gc (grpCopyC w)) (fcx : MeetsContract w p I.cx (chxC w))
    (fcsr : MeetsContract w p I.csr (csrC w)) (fkey : MeetsContract w p I.key (keyC w)) :
    MeetsChild w p f := by
  intro T G P c R D GB RB XB h mem pos ω hpre
  exact ⟨childP I, hf, CS.childP_runs (S := ⟨T, G, P, c, R, D, GB, RB, XB, h, mem⟩) (ω := ω)
    fone frs fhw fpc fnc fsm fdr flg fsp fio fgc fcx fcsr fkey hpre pos⟩

end MinCostFlow.LowStretch
