module

public import MinCostFlow.Chain.Ordered.Algorithm2
public import MinCostFlow.Chain.HiddenTrace

/-!
# Invariants of Algorithm 2 with orders

The two invariants of Algorithm 2 that several files use, as in `Chain/Algorithm2Uncond.lean`
(`Alg2UncondInvWith`) and `Chain/HiddenTrace.lean` (`Alg2HiddenTraceAt`), for Algorithm 2 with
orders (`Chain/Ordered/Algorithm2.lean`). They use the ordered `ChainInv`, `ChainBudgetInvWith`
and `LevelHistory`. The hidden trace also says that the input orders of a level are the orders
the level above returns.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section Alg2Invariants

/-- Full unconditional invariant maintained by `algorithm2_dsWith cfg κ` on any valid history
up to stage `t`, independent of `HiddenStable`. -/
def Alg2UncondInvWith (κ : ℝ) (cfg : Alg2Config) (D : DynamicInstance) (η : ℕ → ℝ)
    (isUpdate : ℕ → Bool) (t : ℕ) (st : Alg2State cfg) : Prop :=
  ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain ∧
  ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc ∧
  0 ≤ st.largeBatchEnc ∧
  st.largeBatchEnc ≤ (Finset.Icc 1 t).sum (fun s =>
    if isUpdate s then largeBatchEncCap cfg.P (D.U s) else 0) ∧
  FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh ∧
  st.extG = D.G t ∧
  (∀ e ∈ (D.G t).E, st.extℓ e = D.ℓ t e ∧ st.extg e = D.g t e) ∧
  st.chain.ℓ = (fun e' => st.extℓ (st.intToExt e')) ∧
  st.chain.g = (fun e' => st.extg (st.intToExt e')) ∧
  (∀ e, st.flow e = minRatioFailFlow (algorithm2_dsWith cfg κ) D η isUpdate t e) ∧
  (∀ e, st.detectAccum e =
    ∑ s ∈ Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) t,
      |minRatioFailIncrement (algorithm2_dsWith cfg κ) D η isUpdate s e|) ∧
  (∀ i : Fin (cfg.P.d + 1),
    (st.chain.shiftCount i.val : ℝ) ≤
      gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) st.chain.rebuildCount i.val) ∧
  st.branD < cfg.P.k ∧
  st.lctUpdateOps ≤ cfg.P.M₀ +
    (Finset.Icc 1 t).sum (fun s => if isUpdate s then (D.U s).length else 0) +
    2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
      ((Finset.range t).sum (fun s => if isUpdate (s + 1) then 1 else 0) +
        ∑ i ∈ Finset.range (cfg.P.d + 1), st.chain.shiftCount i) ∧
  st.lctDetectOps ≤ (Finset.Icc 1 t).sum (fun s =>
    if isUpdate s = false then
      ((algorithm2_dsWith cfg κ).detect (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (s - 1))).1.card + 1
    else 0)

/-- Full unconditional invariant maintained by `algorithm2_ds` (with orders) on any valid history up to stage
`t`, independent of `HiddenStable`. -/
abbrev Alg2UncondInv (cfg : Alg2Config) (D : DynamicInstance) (η : ℕ → ℝ)
    (isUpdate : ℕ → Bool) (t : ℕ) (st : Alg2State cfg) : Prop :=
  Alg2UncondInvWith (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) cfg D η isUpdate t st

/-- Full hidden-stable synchronization invariant linking `Algorithm 2` state `st`,
per-level `LevelHistory`, external witness `(D, c_ext, w_ext)`, and a valid Game
transcript `(moves, initStr, W_game)` ending in `.stage34`, parameterized by total stretch
cap `σ_cap`. As `Chain.Alg2HiddenTraceAt`, with the ordered level histories: the input orders of
level `k + 1` are the orders `rot` that the tool of level `k` returns for its active branch
(`hLvlCore`, last clause). -/
structure Alg2HiddenTraceAt (σ_cap : ℝ) (cfg : Alg2Config) (D : DynamicInstance)
    (c_ext w_ext : ℕ → ℕ → ℝ) (t : ℕ) (st : Alg2State cfg) where
  moves : List (Game.Move cfg.P.d cfg.P.k)
  hmne : moves ≠ []
  initStr : Fin (cfg.P.d + 1) → Fin cfg.P.k → ℝ
  W_game : ℕ → ℝ
  hv : Game.ValidPlayPrefix cfg.gameParams W_game initStr moves
  hf : Game.FollowsStrategyPrefix cfg.gameParams W_game initStr moves
  hPhase : (Game.stateAt W_game cfg.P.hk initStr moves moves.length).phase = .stage34
  timeOfRound : ℕ → ℕ
  hTimeMono : ∀ r₁ r₂, r₁ ≤ r₂ →
    r₂ ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
    timeOfRound r₁ ≤ timeOfRound r₂
  hTimeEnd : timeOfRound (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round = t
  hW_eq : ∀ r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round,
    W_game r = (D.G (timeOfRound r)).norm1 (w_ext (timeOfRound r))
  hShiftMatch : ∀ i : Fin (cfg.P.d + 1), Game.shiftCount moves i = st.chain.shiftCount i.val
  hRebMatch : ∀ i : Fin (cfg.P.d + 1), Game.rebuildCount moves i = st.chain.rebuildCount i.val
  hPassMatch : ∀ i : Fin (cfg.P.d + 1),
    Game.passesAt W_game cfg.P.hk initStr moves moves.length i = st.passes i
  hBranMatch : ∀ i : Fin (cfg.P.d + 1),
    ((Game.stateAt W_game cfg.P.hk initStr moves moves.length).bran i).val =
      if i.val < cfg.P.d then st.chain.bran i.val else st.branD
  -- Per-round `TreeChain` snapshots and fresh-ID translations
  snapC : ℕ → TreeChain
  snapE2I : ℕ → ℕ → ℕ
  snapI2E : ℕ → ℕ → ℕ
  snapNF : ℕ → ℕ
  hSnapEndC : snapC (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round =
    st.chain.toTreeChain
  hSnapEndE2I : snapE2I (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round = st.extToInt
  hSnapEndI2E : snapI2E (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round = st.intToExt
  hSnapEndNF : snapNF (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round = st.nextFresh
  hSnapFresh : ∀ r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round,
    FreshInv (D.G (timeOfRound r)) ((snapC r).G 0) (snapE2I r) (snapI2E r) (snapNF r)
  hSnapHolds : ∀ r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round,
    (snapC r).d = cfg.P.d ∧ (snapC r).k = cfg.P.k ∧
    (snapC r).Holds ((snapC r).G 0) (fun e' => D.ℓ (timeOfRound r) (snapI2E r e'))
      σ_cap
      (max (cfg.σ_mwu cfg.N₀) (cfg.LP.σ_mwu cfg.N₀))
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) (cfg.TP.γ_c (cfg.P.M₀ ^ 2)) ∧
    (snapC r).ForestsAreSubgraphs ∧
    ∀ i < cfg.P.d, ∀ e ∈ ((snapC r).G i).E,
      (∑ j ∈ Finset.range cfg.P.k, ((snapC r).lsfs i j).wstr e) / (cfg.P.k : ℝ) ≤ cfg.σ_mwu cfg.N₀
  reinit : Fin (cfg.P.d + 1) → ℕ
  hRebRep : ∀ i : Fin (cfg.P.d + 1),
    reinit i ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).repT i
  hRepRe : ∀ i : Fin cfg.P.d,
    (Game.stateAt W_game cfg.P.hk initStr moves moves.length).repT
      ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≤
    reinit ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  hSnapBran : ∀ i (hi : i ≤ cfg.P.d),
    ∀ r, reinit ⟨i, Nat.lt_succ_of_le hi⟩ ≤ r →
      r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
      ∀ b < i, (snapC r).bran b = st.chain.bran b
  hStrMatch : ∀ (i : Fin (cfg.P.d + 1)) (j : Fin cfg.P.k),
    (Game.stateAt W_game cfg.P.hk initStr moves moves.length).str i j =
      if _hi : i.val < cfg.P.d then
        hstrAt (snapC ((Game.stateAt W_game cfg.P.hk initStr moves moves.length).repT i))
          (fun e' => w_ext (timeOfRound ((Game.stateAt W_game cfg.P.hk initStr moves moves.length).repT i))
            (snapI2E ((Game.stateAt W_game cfg.P.hk initStr moves moves.length).repT i) e'))
          i.val j.val
      else 0
  -- Per-level histories synchronized with rounds `reinit i .. currRound`
  H : ∀ i < cfg.P.d, LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ st.chain i
  lvlIdx : ℕ → ℕ → ℕ
  hLvlReinit : ∀ i (hi : i < cfg.P.d),
    lvlIdx (reinit ⟨i, Nat.lt_succ_of_le hi.le⟩) i = 0
  hLvlEnd : ∀ i (hi : i < cfg.P.d),
    lvlIdx (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round i = (H i hi).len
  hLvlMono : ∀ i (hi : i < cfg.P.d), ∀ r₁ r₂,
    reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ r₁ →
    r₁ ≤ r₂ → r₂ ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
    lvlIdx r₁ i ≤ lvlIdx r₂ i
  hLvlSucc : ∀ i (hi : i + 1 < cfg.P.d),
    (H (i + 1) hi).len ≤ (H i (Nat.lt_of_succ_lt hi)).len ∧
    ∀ r, reinit ⟨i + 1, Nat.lt_succ_of_le hi.le⟩ ≤ r →
      r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
      lvlIdx r (i + 1) + ((H i (Nat.lt_of_succ_lt hi)).len - (H (i + 1) hi).len) = lvlIdx r i
  hLvlSnap : ∀ i (hi : i < cfg.P.d), ∀ r,
    reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ r →
    r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
    (snapC r).G i = (H i hi).D.G (lvlIdx r i) ∧
    (∀ j < cfg.P.k, (snapC r).lsfs i j =
      cfg.T.lsfs (cfg.T.runOrdAfterRestarts cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
        (H i hi).D (H i hi).ord (H i hi).restarts (lvlIdx r i)) j) ∧
    (reinit ⟨i + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hi)⟩ ≤ r →
      ∀ j < cfg.P.k, (snapC r).emb i j =
        cfg.T.emb (cfg.T.runOrdAfterRestarts cfg.P.k (levelM cfg.TP cfg.P i) cfg.N₀
          (H i hi).D (H i hi).ord (H i hi).restarts (lvlIdx r i)) j)
  hLvlCore : ∀ k (hk : k + 1 < cfg.P.d),
    let Hk := H k (Nat.lt_of_succ_lt hk)
    let Hk1 := H (k + 1) hk
    let off := Hk.len - Hk1.len
    Hk.s₀ ≤ off ∧
    (∀ δ ≤ Hk1.len,
      Hk1.D.G δ =
        (cfg.T.coreInstanceOrdFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
          Hk.D Hk.ord Hk.restarts Hk.s₀ (st.chain.bran k)).G
          ((off - Hk.s₀) + δ)) ∧
    (∀ δ, 1 ≤ δ → δ ≤ Hk1.len →
      Hk1.D.U δ =
        (cfg.T.coreInstanceOrdFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
          Hk.D Hk.ord Hk.restarts Hk.s₀ (st.chain.bran k)).U
          ((off - Hk.s₀) + δ)) ∧
    (∀ δ ≤ Hk1.len, ∀ e ∈ (Hk1.D.G δ).E,
      Hk1.D.ℓ δ e =
        (cfg.T.coreInstanceOrdFrom cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
          Hk.D Hk.ord Hk.restarts Hk.s₀ (st.chain.bran k)).ℓ
          ((off - Hk.s₀) + δ) e) ∧
    (∀ δ ≤ Hk1.len,
      Hk1.ord δ =
        cfg.T.rot (cfg.T.runOrdAfterRestarts cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
          Hk.D Hk.ord Hk.restarts (Hk.s₀ + ((off - Hk.s₀) + δ))) (st.chain.bran k))
  -- Level-0 external step timeline (`0 .. (H 0).len`)
  updRound : ℕ → ℕ
  hUpdBound : ∀ τ ≤ (H 0 cfg.P.hd).len,
    reinit ⟨0, Nat.succ_pos _⟩ ≤ updRound τ ∧
    updRound τ ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round
  hUpdMono : ∀ τ₁ τ₂, τ₁ < τ₂ → τ₂ ≤ (H 0 cfg.P.hd).len → updRound τ₁ < updRound τ₂
  hUpdBand : ∀ r,
    reinit ⟨0, Nat.succ_pos _⟩ ≤ r →
    r ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
    updRound (lvlIdx r 0) ≤ r ∧ (lvlIdx r 0 < (H 0 cfg.P.hd).len → r < updRound (lvlIdx r 0 + 1))
  hLvl0Match : ∀ τ ≤ (H 0 cfg.P.hd).len,
    (H 0 cfg.P.hd).D.G τ = (snapC (updRound τ)).G 0 ∧
    ∀ e' ∈ ((H 0 cfg.P.hd).D.G τ).E,
      (H 0 cfg.P.hd).D.ℓ τ e' = D.ℓ (timeOfRound (updRound τ)) (snapI2E (updRound τ) e')
  hLvl0NoIns : ∀ s τ, s ≤ τ → τ ≤ (H 0 cfg.P.hd).len →
    ∀ r_s r_τ,
      updRound s ≤ r_s → r_s ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
      (s < (H 0 cfg.P.hd).len → r_s < updRound (s + 1)) →
      updRound τ ≤ r_τ → r_τ ≤ (Game.stateAt W_game cfg.P.hk initStr moves moves.length).round →
      (τ < (H 0 cfg.P.hd).len → r_τ < updRound (τ + 1)) →
      r_s ≤ r_τ →
      ∀ e' ∈ ((H 0 cfg.P.hd).D.G τ).E,
        (s = τ →
          snapI2E r_τ e' = snapI2E r_s e' ∧
          D.NotInsertedBetween (snapI2E r_τ e') (timeOfRound r_s) (timeOfRound r_τ) ∧
          D.ℓ (timeOfRound r_τ) (snapI2E r_τ e') = D.ℓ (timeOfRound r_s) (snapI2E r_τ e')) ∧
        ((H 0 cfg.P.hd).D.NotInsertedBetween e' s τ →
          snapI2E r_τ e' = snapI2E r_s e' ∧
          D.NotInsertedBetween (snapI2E r_τ e') (timeOfRound r_s) (timeOfRound r_τ))

/-- `Alg2HiddenTrace` specialized to the global vertex cap `alg2SigmaTot cfg.TP cfg.LP cfg.P cfg.N₀`. -/
abbrev Alg2HiddenTrace (cfg : Alg2Config) (D : DynamicInstance)
    (c_ext w_ext : ℕ → ℕ → ℝ) (t : ℕ) (st : Alg2State cfg) :=
  Alg2HiddenTraceAt (alg2SigmaTot cfg.TP cfg.LP cfg.P cfg.N₀) cfg D c_ext w_ext t st

end Alg2Invariants

end MinCostFlow.Chain.Ordered
