module

public import MinCostFlow.LowStretch.ProgChildOneMid

/-!
# One child: the run up to the size test

From the start of `oneP` for child `k` to the test `|X| < 2`: the loads (`onePro_runs`), the four
calls and the record block (`oneB_runs`). The memory then meets `MidOk` (`CS.midOk_of_done`); the
preconditions of the calls come from `CS.callsOk`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem sub600 {a T : ℕ} (h : 600 + a ≤ T) : a ≤ T - 600 ∧ 600 ≤ T := by omega

theorem add600 {a T : ℕ} (h1 : 600 ≤ T) (h : a ≤ T - 600) : 600 + a ≤ T := by omega

namespace CS

variable {S : CS} {w : ℕ} {M1 M : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- **The run of child `k` up to the size test.** The continuation gets the memory `memM6`, which
meets `MidOk`, and the registers that `oneB_runs` gives. -/
theorem oneMid_runs {p : Program} {ω : ℕ → Bool} {I : CIdx} {pos : ℕ}
    (fhw : MeetsContract w p I.hw (hwC w)) (fpc : MeetsContract w p I.pc (pcC w))
    (fnc : MeetsContract w p I.nc (ncC w)) (fsm : MeetsContract w p I.sm (smC w))
    (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hroom : H + S.spaceK M1 k + 2 < 2 ^ w) {Q : Outcome → State → Prop} {T : ℕ}
    (hrest : ∀ (M4 : ℕ → ℕ) (st' : State), MidOk S M1 k H M (S.memM6 M1 k H M4) →
      st'.mem = S.memM6 M1 k H M4 → (S.oneV M1 k H).Regs st' → st'.regs 39 = S.ℓK k →
      st'.regs 40 = S.SAK H k → st'.regs 45 = S.NAK M1 H k → st'.regs 46 = S.OUTK M1 H k →
      st'.regs 47 = (S.raw k).X.card →
      st'.regs 48 = (S.raw k).X.sup (fun a => S.T.mw (S.T.top S.c.θ a)) →
      st'.regs 49 = S.OUTK M1 H k + 2 →
      ∃ o st'' c, Runs w p ω (.cond (.bin .lt (.reg 47) (.const 2)) (.ret (.reg 49)) (oneD I))
        st' o st'' c ∧ Q o st'' ∧
          600 + (160 * S.ℓK k + 200 * S.cntK M1 k + 110 * S.sNK M1 k + 1000 + c) ≤ T) :
    ∃ o st' c, Runs w p ω (oneP I) (startState (S.oneV M1 k H).args M pos) o st' c ∧ Q o st' ∧
      c ≤ T := by
  have hle := hI.hle
  have hw : H < 2 ^ w := by omega
  obtain ⟨o, st', c, hrun, ⟨hQ, -⟩, hc⟩ := onePro_runs (p := p) (ω := ω) (pos := pos)
    (oneFacts hpre hT hI hk hw) (s := oneB I) (Q := fun o st => Q o st ∧ 600 ≤ T) (T := T)
    (fun st hR hM => by
      obtain ⟨o, st', c, hrun, ⟨hQ, hT6⟩, hc⟩ := oneB_runs (Q := fun o st => Q o st ∧ 600 ≤ T)
        (T := T - 600) fhw fpc fnc fsm (callsOk hpre hT hI hk hroom) hR hM
        (fun M2 M3 M4 st' hd hd2 hd3 hm hR' h39 h40 h45 h46 h47 h48 h49 => by
          have hm' : st'.mem = S.memM6 M1 k H M4 := hm
          have hmid := midOk_of_done hpre hT hI hk hd hd2 hd3
          have h47' : st'.regs 47 = (S.raw k).X.card := by
            rw [h47, hm', show (S.oneV M1 k H).OUT (S.ℓK k) = S.OUTK M1 H k from rfl]
            exact hmid.out1
          have h48' : st'.regs 48 = (S.raw k).X.sup (fun a => S.T.mw (S.T.top S.c.θ a)) := by
            rw [h48, hm', show (S.oneV M1 k H).OUT (S.ℓK k) = S.OUTK M1 H k from rfl]
            exact hmid.out2
          obtain ⟨o, st'', c, hrun, hQ, hc⟩ := hrest M4 st' hmid hm' hR' h39 h40 h45 h46 h47' h48'
            h49
          exact ⟨o, st'', c, hrun, ⟨hQ, (sub600 hc).2⟩, (sub600 hc).1⟩)
      exact ⟨o, st', c, hrun, ⟨hQ, hT6⟩, add600 hT6 hc⟩)
  exact ⟨o, st', c, hrun, hQ, hc⟩

end CS

end MinCostFlow.LowStretch
