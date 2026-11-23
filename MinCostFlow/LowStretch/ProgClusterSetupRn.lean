module

public import MinCostFlow.LowStretch.ProgClusterSetupMt

/-!
# The setup of a cluster: the run and the contract

The run of `setupP` from the start state with arguments `[GB, RB, h]`: the chain of calls
(`suChain_runs`) reaches a state that `SuAt` describes, and the stores of the block
(`suBlk_runs`) write the block. The memory after them meets `SuFin`, so `SetupOut` holds
(`SuFin.out`), and the cost is at most `setupCostOf` (`suCost_le`). This gives
`setup_runs`, and from it the contract of the setup (`setup_meets`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

set_option maxHeartbeats 4000000 in
/-- **The words of the block.** -/
theorem SuAt.bkW {st : State} (a : SuAt w T G P c R GB RB h mem st)
    (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) (hP : P = par G.n G.m) :
    BkW w (suVOf GB RB h mem) a.Es (c.Δ G) (c.d G c.x0 c.t) := by
  have hR := a.wR hp hX hP
  have hM : a.W.M < 2 ^ w := hR _ (by simp [PW.LReg])
  have hκ : a.W.κ < 2 ^ w := hR _ (by simp [PW.LReg])
  have hJ : a.W.L.J < 2 ^ w := hR _ (by simp [PW.LReg])
  have hsw := hp.small_w hX
  have := Nat.zero_le (2 ^ ((RecL.read mem RB).lθ + ((GlobL.read mem GB).J + 3)))
  obtain ⟨E', hE', -, -, -, -, hI, -⟩ := hp.drawPre hX
  obtain rfl := DWE.eq_of_args hE'
  have hΔI : c.Δ G < (GlobL.read mem GB).INF := hI
  have hdt : c.d G c.x0 c.t ≤ c.Δ G := Cl.d_le_Δ hp.ok.inv.t_mem
  have hW := hp.words hX
  obtain ⟨Z, hZ1, -, -, hnZ, hroom⟩ := hp.room_core hX
  have hm : (GlobL.read mem GB).m = G.m := hp.glob.m
  have hn : (GlobL.read mem GB).n = G.n := hp.glob.n
  set J := (GlobL.read mem GB).J
  have hK : G.n ≤ 2 ^ J * Z := (by omega : G.n ≤ Z).trans (Nat.le_mul_of_pos_left _
    Nat.one_le_two_pow)
  have hnn : G.n * G.n ≤ 2 ^ 20 * ((2 ^ J * Z) * (2 ^ J * Z)) :=
    (Nat.mul_le_mul hK hK).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hm1 : G.m + 1 ≤ 1000 * (J + 1) * (G.m + T.N + P.L + 10) := by
    have : G.m + T.N + P.L + 10 ≤ 1000 * (J + 1) * (G.m + T.N + P.L + 10) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    omega
  refine ⟨hJ, ?_, ?_, hκ, ?_, ?_, ?_⟩
  · show (GlobL.read mem GB).n * (GlobL.read mem GB).n < 2 ^ w
    rw [hn]; omega
  · show (GlobL.read mem GB).m < 2 ^ w
    omega
  · rw [Nat.one_shiftLeft]; exact hM
  · omega
  · omega

/-- The block cells are zero at the end of the chain. -/
theorem SuAt.blk_zero {st : State} (a : SuAt w T G P c R GB RB h mem st)
    (hp : ClPre w A T G P c R GB RB h mem) {i : ℕ} (hi : i < 51) : st.mem (h + i) = 0 := by
  have hZ := suN_hZ GB RB h mem P.L
  rw [a.mem_eq, a.low (by simp only [SuN.z]; omega), a.hM.low_h (by omega)]
  exact hp.zero _ (Nat.le_add_right _ _)

set_option maxHeartbeats 4000000 in
/-- **The run of the setup.** -/
theorem setup_runs {p : Program} {ω : ℕ → Bool} {I : SuIdx}
    (hLg : MeetsContract w p I.lg (log2C w)) (hDr : MeetsContract w p I.dr (drawC2 w))
    (hTr : MeetsContract w p I.tr (treePC w)) (hHf : MeetsContract w p I.hf (hwFixC w))
    (hAc : MeetsContract w p I.ac (actPC w)) (hPg : MeetsContract w p I.pg (pgPC w))
    (hCp : MeetsContract w p I.cp (suCpC w)) (hHl : MeetsContract w p I.hl (suHalfC w))
    (hEx : MeetsContract w p I.ex (suExpC w)) (hMx : MeetsContract w p I.mx (maxtC w))
    (hP2 : MeetsContract w p I.p2 (suP2C w)) (hSq : MeetsContract w p I.sq (suSqC w))
    (hCl : MeetsContract w p I.cl (pqClearC w))
    (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) (hP : P = par G.n G.m)
    (h3 : SuRoom3 w T G h) (pos : ℕ) :
    ∃ o st' c', Runs w p ω (setupP I) (startState [GB, RB, h] mem pos) o st' c' ∧
      SetupOut w ⟨T, G, P, c, R⟩ h mem st'.mem ∧
      c' ≤ setupCostOf ⟨T, G, P, c, R⟩ := by
  have hW := hp.suWords hX
  obtain ⟨ht, hts⟩ := hp.t_eq
  have htX : c.t ∈ c.X := hp.ok.inv.t_mem
  have hsl : (RecL.read mem RB).s = R.nodes.length := hp.recAt.arcs.s
  have hnS : (RecL.read mem RB).nS = R.S.length := hp.recAt.arcs.nS
  have htS : R.sv T c c.t < (RecL.read mem RB).s := hsl ▸ hp.ok.sv_lt htX
  have hZ := suN_hZ GB RB h mem P.L
  refine suChain_runs (pos := pos) (Q := fun _ st' => SetupOut w ⟨T, G, P, c, R⟩ h mem st'.mem)
    (K := setupCostOf ⟨T, G, P, c, R⟩) hLg hDr hTr hHf hAc hPg hCp hHl hEx hMx hP2 hSq hCl
    hp hX hW (fun st a => ?_)
  have v1 : (suVOf GB RB h mem).h = h := rfl
  have v2 : SuN.h 𝔑 = h := rfl
  have v3 : (suVOf GB RB h mem).nS = SuN.nS 𝔑 := rfl
  have v4 : (suVOf GB RB h mem).s = SuN.s 𝔑 := rfl
  have v5 : SuN.s 𝔑 = (RecL.read mem RB).s := rfl
  have hdt : st.mem ((suVOf GB RB h mem).h + 51 + 16 * (suVOf GB RB h mem).nS +
      4 * (suVOf GB RB h mem).s + 5 + (suVOf GB RB h mem).ts) = c.d G c.x0 c.t := by
    rw [hts, a.mem_eq, a.low (by simp only [SuN.z, SuN.Z, SuN.H]; omega)]
    exact hp.fdM4 a.hM htX
  have hts' : (suVOf GB RB h mem).ts < (suVOf GB RB h mem).s := by rw [hts]; exact htS
  refine suBlk_runs a.hR a.r31 a.r32 a.r33 hdt hts' (fun i hi => a.blk_zero hp hi)
    (a.bkW hp hX hP) (fun st' hreg hblk hfr => ⟨?_, ?_⟩)
  · have hf : SuFin a st'.mem := ⟨hblk, fun x hx => by rw [hfr x hx, a.mem_eq]⟩
    exact hf.out hp hX hP h3
  · have hnH := hp.nH_le hX a.hM.first a.hM.tr_fr
    have hk := suCost_le (mem := mem) (V := suVOf GB RB h mem) (L := P.L) (nA := a.hM.nA)
      ((SuAt.nA_le (a := a)).trans le_rfl) hnH (by rw [hp.L_eq]; exact congrArg pL hp.glob.n)
    have e1 : (suVOf GB RB h mem).J = rootJ G.n := hp.J_eq
    have e2 : (suVOf GB RB h mem).nS = R.S.length := hnS
    have e3 : (suVOf GB RB h mem).s = R.nodes.length := hsl
    rw [e1, e2, e3] at hk
    exact hk

/-- **The contract of the setup.** -/
theorem setup_meets {p : Program} {f : ℕ} {I : SuIdx}
    (hproc : p.procs[f]? = some (setupP I))
    (hLg : MeetsContract w p I.lg (log2C w)) (hDr : MeetsContract w p I.dr (drawC2 w))
    (hTr : MeetsContract w p I.tr (treePC w)) (hHf : MeetsContract w p I.hf (hwFixC w))
    (hAc : MeetsContract w p I.ac (actPC w)) (hPg : MeetsContract w p I.pg (pgPC w))
    (hCp : MeetsContract w p I.cp (suCpC w)) (hHl : MeetsContract w p I.hl (suHalfC w))
    (hEx : MeetsContract w p I.ex (suExpC w)) (hMx : MeetsContract w p I.mx (maxtC w))
    (hP2 : MeetsContract w p I.p2 (suP2C w)) (hSq : MeetsContract w p I.sq (suSqC w))
    (hCl : MeetsContract w p I.cl (pqClearC w)) :
    MeetsContract w p f (setupC w) := by
  refine meets_of_ghost hproc ?_
  intro g args mem pos _ hpre st ω hst
  obtain ⟨GB, RB, h, rfl, hp, hX, -, -, hP, h3⟩ := hpre
  subst hst
  obtain ⟨o, st', c', hr, hout, hc⟩ := setup_runs (ω := ω) hLg hDr hTr hHf hAc hPg hCp hHl hEx
    hMx hP2 hSq hCl hp hX hP h3 pos
  refine ⟨o, st', c', hr, fun GB' RB' h' he => ?_, ?_⟩
  · simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl, -⟩ := he
    exact hout
  · rw [setupCost_eq hp]; exact hc

end MinCostFlow.LowStretch
