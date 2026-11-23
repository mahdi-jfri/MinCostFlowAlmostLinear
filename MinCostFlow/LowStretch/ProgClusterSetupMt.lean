module

public import MinCostFlow.LowStretch.ProgClusterSetupOB

/-!
# The setup of a cluster: the run and its cost

The setup runs the chain of calls (`suChain_runs`) and then the stores of the block
(`suBlk_runs`), and leaves `SetupOut` (`SuFin.out`). Its cost is at most `setupCostOf`
(`suCost_le`): the chain costs `O(log J + L)` per stored pair and node, and `O(J)` once, and the
highway has at most `s` steps (`ClPre.nH_le`), since `hwFix` takes its nodes one to one.

The main result is `setup_runs`, which the contract of the setup (`setup_meets`) uses.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

/-- **The highway has at most `s` steps**: its nodes are distinct nodes (`HF.Pre.inj`). -/
theorem ClPre.nH_le (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
    {M M2 : ℕ → ℕ} (hF : Rec.First w T G c R (suVOf GB RB h mem).dwE mem M)
    (hfr : ∀ a, ¬ ((suVOf GB RB h mem).dwE.tf ((suVOf GB RB h mem).N P.L).Z).Out a →
      M2 a = M a) :
    (RecL.read mem RB).nH ≤ (RecL.read mem RB).s := by
  have hZ := suN_hZ GB RB h mem P.L
  have hS := hp.hS_lt hX
  have hroom := hp.room_h
  have hHV := hp.hfV hF hZ hfr
  set F := (suVOf GB RB h mem).dwE.hfx ((suVOf GB RB h mem).N P.L).Z (RecL.read mem RB).nH
    (RecL.read mem RB).HW with hFd
  have vs : ((suVOf GB RB h mem).N P.L).s = (RecL.read mem RB).s := rfl
  have vs2 : (suVOf GB RB h mem).s = (RecL.read mem RB).s := rfl
  have hpre : F.Pre M2 w := by
    refine hHV.pre (by simp only [hFd, DWE.hfx]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by omega)
      (fun p hp' => hp.pw_words hX p hp')
    all_goals simp only [hFd, DWE.hfx, SuV.dwE]
    all_goals try omega
    simp only [SuN.hS, SuN.r, SuN.RR, SuN.D, SuN.z] at hS
    omega
  have hinj : Set.InjOn (F.nu M2) ↑(Finset.range F.nH) := fun j hj j' hj' he =>
    hpre.inj j (Finset.mem_range.mp hj) j' (Finset.mem_range.mp hj') he
  have hmaps : ∀ j ∈ Finset.range F.nH, F.nu M2 j ∈ Finset.range F.s := fun j hj =>
    Finset.mem_range.mpr (hpre.nu_lt j (Finset.mem_range.mp hj))
  have := Finset.card_le_card_of_injOn (F.nu M2) hmaps hinj
  simp only [Finset.card_range] at this
  exact this

/-- `⌈log₂ (J + 3)⌉ ≤ ⌊log₂ J⌋ + 2`. -/
theorem clog_le_log (J : ℕ) : Nat.clog 2 (J + 3) ≤ Nat.log 2 J + 2 := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  have h1 : J < 2 ^ (Nat.log 2 J + 1) := Nat.lt_pow_succ_log_self (by norm_num) J
  have h2 : 1 ≤ 2 ^ Nat.log 2 J := Nat.one_le_two_pow
  rw [pow_succ] at h1
  rw [pow_add]
  omega

/-- The linear part of the arithmetic of the cost of the setup. -/
theorem suCost_lin {q s nS nA nH J D1 D2 P1 P2 : ℕ} (h1 : D1 ≤ 3400 * P1) (h2 : D2 ≤ 580 * P1)
    (h3 : 2 * (2 * nS + s + 1) ≤ P1) (h4 : q ≤ P2) (hnA : nA ≤ nS) (hnH : nH ≤ s) :
    300 + (100 * q + 200) + (32 + (D1 + 150 * J + 2000)) +
        (300 * s + 400) + (250 * nH + 300) + (80 * nS + 100) + (D2 + 500 * s + 1000) +
        (40 * s + 40 * (2 * nA + s) + 80 * nA + 40 * nA + 30 * nA + 1000) +
        (100 * (q + 2) + 150 * (J + 5) + 1000) + 2002 ≤
      100000 * P1 + 100000 * P2 + 400 * J + 10000 := by
  omega

/-- The arithmetic of the cost of the setup. -/
theorem suCost_arith {X L s nS nA nH J q cl : ℕ} (hX : 2 ≤ X) (hc : cl ≤ X) (hnA : nA ≤ nS)
    (hnH : nH ≤ s) (hq : q = L) :
    300 + (100 * q + 200) + (32 + ((200 * X + 3000) * (2 * nS + 2 * s + 2) + 150 * J + 2000)) +
        (300 * s + 400) + (250 * nH + 300) + (80 * nS + 100) +
        (nA * (80 * cl + 1000) + 500 * s + 1000) +
        (40 * s + 40 * (2 * nA + s) + 80 * nA + 40 * nA + 30 * nA + 1000) +
        (100 * (L + 2) + 150 * (J + 5) + 1000) + 2002 ≤
      100000 * (X + L) * (2 * nS + s + 1) + 400 * J + 10000 := by
  subst hq
  have h1a : 200 * X + 3000 ≤ 1700 * X := by omega
  have h1b : 2 * nS + 2 * s + 2 ≤ 2 * (2 * nS + s + 1) := by omega
  have h2a : nA ≤ 2 * nS + s + 1 := by omega
  have h2b : 80 * cl + 1000 ≤ 580 * X := by omega
  have h1 := Nat.mul_le_mul h1a h1b
  have h2 := Nat.mul_le_mul h2a h2b
  have e1' : 1700 * X * (2 * (2 * nS + s + 1)) = 3400 * (X * (2 * nS + s + 1)) := by ring
  have e2 : (2 * nS + s + 1) * (580 * X) = 580 * (X * (2 * nS + s + 1)) := by ring
  have h3 : 2 * (2 * nS + s + 1) ≤ X * (2 * nS + s + 1) := Nat.mul_le_mul_right _ hX
  have e1 : 100000 * (X + q) * (2 * nS + s + 1) =
      100000 * (X * (2 * nS + s + 1)) + 100000 * (q * (2 * nS + s + 1)) := by ring
  have h4 : q ≤ q * (2 * nS + s + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rw [e1]
  exact suCost_lin (h1.trans e1'.le) (h2.trans e2.le) h3 h4 hnA hnH

/-- **The cost of the setup** is at most `setupCost`. -/
theorem suCost_le {V : SuV} {L nA : ℕ} (hnA : nA ≤ V.nS) (hnH : V.nH ≤ V.s) (hL : pL V.n = L) :
    suChainCost V L nA (drawCost V.dwE.args mem) + 2002 ≤
      100000 * (Nat.log 2 V.J + 2 + L) * (2 * V.nS + V.s + 1) + 400 * V.J + 10000 :=
  suCost_arith (X := Nat.log 2 V.J + 2) (by omega) (clog_le_log V.J) hnA hnH hL

end MinCostFlow.LowStretch
