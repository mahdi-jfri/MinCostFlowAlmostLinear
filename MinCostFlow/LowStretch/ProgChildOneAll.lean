module

public import MinCostFlow.LowStretch.ProgResetU

/-!
# One child: the whole run of `oneP`

`CS.oneP_runs`: the run of `oneP` for child `k`, from a memory that meets the loop invariant
`CInv` before child `k`, ends with the invariant for `k + 1` (`OneQ`), within `costK k`. It chains
`oneMid_runs` (up to the size test), `oneT_runs` (the size test, Dijkstra and the reset test),
and for a reset child the call of `rsP` (`rs_call`) with `CInv.step_reset`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable {S : CS} {w : ℕ} {M1 M : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The cost of the radius search of child `k`. -/
theorem drawCost_eq (M6 : ℕ → ℕ) : drawCost (S.dwE M1 k H).args M6 =
    (200 * (Nat.log 2 S.E.J + 2) + 3000) * (2 * S.cntK M1 k + 2 * S.sNK M1 k + 2) +
      150 * S.E.J + 2000 := by
  simp only [drawCost, DWE.args, dwE, List.getD_cons_succ, List.getD_cons_zero]

/-- **The steps of child `k` fit in `costK k`.** -/
theorem oneCost_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) (M6 : ℕ → ℕ) :
    600 + (160 * S.ℓK k + 200 * S.cntK M1 k + 110 * S.sNK M1 k + 1000) + 300 +
      drawCost (S.dwE M1 k H).args M6 + S.rsCost M1 k + 20 ≤ S.costK M1 k := by
  rw [drawCost_eq]
  have hℓ := ℓK_le hpre hT hk
  have hJ := J_pos hpre
  have hlog := Nat.log_le_self 2 S.E.J
  unfold rsCost costK
  set L := Nat.log 2 S.E.J + 2
  set a := S.cntK M1 k
  set b := S.sNK M1 k
  have e1 : (200 * L + 3000) * (2 * a + 2 * b + 2) = (400 * L + 6000) * (a + b) + 400 * L + 6000 := by
    ring
  have e2 : (400 * L + 9000) * (a + b) = (400 * L + 6000) * (a + b) + 3000 * (a + b) := by ring
  rw [e1, e2]
  omega

theorem cost_drop {a b c T : ℕ} (h : a + 300 + b + c + 20 ≤ T) : a + 300 + b ≤ T := by omega

theorem cost_assoc {x c T : ℕ} (h : 600 + x + c ≤ T) : 600 + (x + c) ≤ T := by omega

/-- **The run of `oneP` for child `k`.** -/
theorem oneP_runs {p : Program} {ω : ℕ → Bool} {I : CIdx}
    (fhw : MeetsContract w p I.hw (hwC w)) (fpc : MeetsContract w p I.pc (pcC w))
    (fnc : MeetsContract w p I.nc (ncC w)) (fsm : MeetsContract w p I.sm (smC w))
    (fdr : MeetsContract w p I.dr (drawC w)) (frs : p.procs[I.rs]? = some (rsP I))
    (flg : MeetsContract w p I.lg (log2C w)) (fsp : MeetsContract w p I.sp (splitC w))
    (fio : MeetsContract w p I.io (iotaC w)) (fgc : MeetsContract w p I.gc (grpCopyC w))
    (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hroom : H + S.spaceK M1 k + 2 < 2 ^ w)
    (hroom2 : drawEnd (S.dwE M1 k H) + 3 * (S.sNK M1 k + S.T.N + 1) < 2 ^ w) (pos : ℕ) :
    ∃ o st' c, Runs w p ω (oneP I) (startState (S.oneV M1 k H).args M pos) o st' c ∧
      OneQ w S M1 k Rs o st' ∧ c ≤ S.costK M1 k := by
  have hNw : S.T.N < 2 ^ w := by
    have := big_words hpre
    have : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
    omega
  refine oneMid_runs fhw fpc fnc fsm hpre hT hI hk hroom
    (fun M4 st' hmid hm hR _ h40 h45 _ h47 h48 h49 => ?_)
  have hc := oneCost_le (H := H) hpre hT hk (S.memM6 M1 k H M4)
  obtain ⟨o, st3, c, h1, h2, h3⟩ := oneT_runs (p := p) (ω := ω) (I := I) fdr hpre hT hI hk hroom hmid hm hR h40 h47 h49
    (A := 600 + (160 * S.ℓK k + 200 * S.cntK M1 k + 110 * S.sNK M1 k + 1000))
    (T := S.costK M1 k) (cost_drop hc) (fun hq st'' hM7 hregs h51 h52 => by
      obtain ⟨o, st3, c, hrun, ⟨H', rfl, hE⟩, hcst⟩ := rs_call (ω := ω) frs flg fsp fio fnc fpc fgc hpre
        hT hI hk hmid hq hroom hroom2 hR h45 h47 h48 st'' (fun a ha => hM7 a (Or.inl ha)) hregs
        h51 h52 (A := 600 + (160 * S.ℓK k + 200 * S.cntK M1 k + 110 * S.sNK M1 k + 1000) + 300 +
          drawCost (S.dwE M1 k H).args (S.memM6 M1 k H M4)) (T := S.costK M1 k) hc
      obtain ⟨R', hI'⟩ := CInv.step_reset hpre hT hI hk hmid hq hM7 hE hNw
      exact ⟨_, st3, c, hrun, ⟨H', R', rfl, hI'⟩, hcst⟩)
  exact ⟨o, st3, c, h1, h2, cost_assoc h3⟩

end CS

end MinCostFlow.LowStretch
