module

public import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
public import MinCostFlow.MinRatio.SolverLevelMetaPreserve
import Mathlib.Tactic

/-!
# Level-cap invariant of the solver (`SolverLevelCapsInv`)

`ShiftDeepChainSyncSpecWExtKFBL` (`WireShiftDeepSpecKFBL.lean`) requires both `SolverLevelMetaAt`
and `SolverLevelCapsAt vCap eCap` before a non-terminal shift and preserves both after it.
This file defines the combined solver-level invariant `SolverLevelCapsInv` outside `SolverRep.lean`,
proves its equivalence with `SolverLevelMetaCapsAt`, and provides the preservation lemma
`SolverLevelCapsInv.preserve` across solver steps that leave the level metadata regions unchanged
(tags `20`, `21 + d`, `22 + d`, `23 + d`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program IPM.Machine

/-- Combined level-metadata and level-cap invariant required and maintained by
`ShiftDeepChainSyncSpecWExtKFBL` (`WireShiftDeepSpecKFBL.lean`). Defined outside `SolverRep.lean`
so `solverStateRep` stays unchanged. -/
@[expose] def SolverLevelCapsInv {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (P V vCap eCap : ℕ) (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (mem : ℕ → ℕ) :
    Prop :=
  SolverLevelMetaAt P V model tok mem ∧ SolverLevelCapsAt vCap eCap model tok mem

/-- `SolverLevelCapsInv` is equivalent to `SolverLevelMetaCapsAt`. -/
theorem solverLevelCapsInv_iff_metaCaps {cfg : Alg2Config} {L P V vCap eCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ} :
    SolverLevelCapsInv P V vCap eCap model tok mem ↔
      SolverLevelMetaCapsAt P V vCap eCap model tok mem := by
  constructor
  · rintro ⟨hM, hC⟩
    exact ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, hM.2.2.2.2.1,
      fun j hj => SolverLevelMetaAt.atCaps hM hC j hj⟩
  · exact SolverLevelMetaCapsAt.meta_caps

private theorem chainLen_congr_lt {T : SparseCoreRestartTool} {P : ChainParams}
    {c₁ c₂ : ChainState T P} {ℓ₁ ℓ₂ : ℕ → ℝ}
    (hℓ : ℓ₁ = ℓ₂)
    (hSc : ∀ j < P.d, c₁.scState j = c₂.scState j)
    (hBr : ∀ j < P.d, c₁.bran j = c₂.bran j) :
    ∀ j ≤ P.d, c₁.toTreeChain.chainLen ℓ₁ j = c₂.toTreeChain.chainLen ℓ₂ j := by
  intro j
  induction j with
  | zero => intro _; simpa [TreeChain.chainLen] using hℓ
  | succ j ih =>
    intro hj
    have hjLt : j < P.d := hj
    simp only [TreeChain.chainLen]
    rw [ih (Nat.le_of_lt hjLt)]
    congr 1
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjLt, ↓reduceIte, hSc j hjLt, hBr j hjLt]

/-- Frame/preservation lemma for `SolverLevelCapsInv`: any solver transition that preserves the
chain's non-terminal levels (`G`, `scState`, `bran` on `< d`, `ℓ`, `lvlM`, `N₀`), the table/core
handles, ownership and tags on `{20, 21 + d, 22 + d, 23 + d}`, and memory on all addresses tagged
in `{20, 21 + d, 22 + d, 23 + d}` preserves `SolverLevelCapsInv`. -/
theorem SolverLevelCapsInv.preserve {cfg : Alg2Config} {L P V vCap eCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {model model' : Alg2State cfg} {tok tok' : SolverToken cfg L Rcore} {mem mem' : ℕ → ℕ}
    (hInv : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hTable : tok'.table = tok.table)
    (hCoreOwn : ∀ j < cfg.P.d, tok'.owned (tok'.coreHandle j))
    (hOwnMeta : ∀ a,
      tok.tag a = 20 ∨ tok.tag a = 21 + cfg.P.d ∨ tok.tag a = 22 + cfg.P.d ∨
        tok.tag a = 23 + cfg.P.d →
      tok'.tag a = tok.tag a ∧ mem' a = mem a)
    (hOwnLen : ∀ j < cfg.P.d, tok'.owned (mem (solverLevelMetaAddr tok.table cfg.P.d + j)))
    (hN₀ : model'.chain.N₀ = model.chain.N₀)
    (hLvlM : ∀ j < cfg.P.d, model'.chain.lvlM j = model.chain.lvlM j)
    (hG : ∀ j < cfg.P.d, model'.chain.G j = model.chain.G j)
    (hSc : ∀ j < cfg.P.d, model'.chain.scState j = model.chain.scState j)
    (hBr : ∀ j < cfg.P.d, model'.chain.bran j = model.chain.bran j)
    (hℓ : model'.chain.ℓ = model.chain.ℓ) :
    SolverLevelCapsInv P V vCap eCap model' tok' mem' := by
  have hMC := solverLevelCapsInv_iff_metaCaps.mp hInv
  rw [solverLevelCapsInv_iff_metaCaps]
  obtain ⟨⟨hN0Val, hTagN0, hTagSH, hTagSB⟩, _, hMTab, hTagM, hTagMeta, hLvls⟩ := hMC
  have hLenEq := chainLen_congr_lt hℓ hSc hBr
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hCoreOwn, ?_, ?_, ?_, ?_⟩
  · rw [hTable, (hOwnMeta _ (Or.inr (Or.inl hTagN0))).2, hN0Val, hN₀]
  · rw [hTable, (hOwnMeta _ (Or.inr (Or.inl hTagN0))).1, hTagN0]
  · rw [hTable, (hOwnMeta _ (Or.inr (Or.inl hTagSH))).1, hTagSH]
  · rw [hTable, (hOwnMeta _ (Or.inr (Or.inl hTagSB))).1, hTagSB]
  · intro j hj
    rw [hTable, (hOwnMeta _ (Or.inr (Or.inl (hTagM j hj)))).2, hMTab j hj, hLvlM j hj]
  · intro j hj
    rw [hTable, (hOwnMeta _ (Or.inr (Or.inl (hTagM j hj)))).1, hTagM j hj]
  · intro j hj
    rw [hTable, (hOwnMeta _ (Or.inr (Or.inr (Or.inl (hTagMeta j hj))))).1, hTagMeta j hj]
  · intro j hj
    obtain ⟨hDG, hEV, _, hTagL, hTagG⟩ := hLvls j hj
    have hMemL : mem' (solverLevelMetaAddr tok'.table cfg.P.d + j) =
        mem (solverLevelMetaAddr tok.table cfg.P.d + j) := by
      rw [hTable]
      exact (hOwnMeta _ (Or.inr (Or.inr (Or.inl (hTagMeta j (by omega)))))).2
    have hMemG : mem' (solverLevelMetaAddr tok'.table cfg.P.d + cfg.P.d + j) =
        mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := by
      rw [hTable]
      have hidx : cfg.P.d + j < 2 * cfg.P.d := by omega
      have htag := hTagMeta (cfg.P.d + j) hidx
      rw [← Nat.add_assoc] at htag
      exact (hOwnMeta _ (Or.inr (Or.inr (Or.inl htag)))).2
    have hTagGOr (a : ℕ)
        (ha1 : mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) ≤ a)
        (ha2 : a < mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) +
          dynGraphSize vCap eCap) :
        tok.tag a = 20 ∨ tok.tag a = 21 + cfg.P.d ∨ tok.tag a = 22 + cfg.P.d ∨
          tok.tag a = 23 + cfg.P.d := by
      have ht := hTagG a ha1 ha2
      split_ifs at ht
      · exact Or.inl ht
      · exact Or.inr (Or.inr (Or.inr ht))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hMemG, hG j hj]
      exact dynGraphAt_of_agree hDG fun a ha1 ha2 => (hOwnMeta a (hTagGOr a ha1 ha2)).2
    · rw [hMemL, hG j hj, hLenEq j (Nat.le_of_lt hj)]
      intro e he
      have hev := hEV e he
      have hcap : e < eCap := hDG.2.2.1 e he
      have hAgr : ∀ k < L,
          mem' (mem (solverLevelMetaAddr tok.table cfg.P.d + j) + e * L + k) =
          mem (mem (solverLevelMetaAddr tok.table cfg.P.d + j) + e * L + k) := by
        intro k hk
        have hmul : e * L + L ≤ eCap * L := by
          rw [← Nat.succ_mul]
          exact Nat.mul_le_mul_right L (Nat.succ_le_of_lt hcap)
        have ha1 : mem (solverLevelMetaAddr tok.table cfg.P.d + j) ≤
            mem (solverLevelMetaAddr tok.table cfg.P.d + j) + e * L + k := by omega
        have ha2 : mem (solverLevelMetaAddr tok.table cfg.P.d + j) + e * L + k <
            mem (solverLevelMetaAddr tok.table cfg.P.d + j) + eCap * L := by omega
        exact (hOwnMeta _ (Or.inr (Or.inr (Or.inr (hTagL _ ha1 ha2))))).2
      refine ⟨fun k hk => by rw [hAgr k hk]; exact hev.1 k hk, ?_⟩
      unfold Num.fixVal
      rw [Num.intVal_congr hAgr]
      exact hev.2
    · rw [hMemL]
      exact hOwnLen j hj
    · intro a ha1 ha2
      rw [hMemL] at ha1 ha2
      rw [(hOwnMeta a (Or.inr (Or.inr (Or.inr (hTagL a ha1 ha2))))).1, hTagL a ha1 ha2]
    · intro a ha1 ha2
      rw [hMemG] at ha1 ha2
      rw [(hOwnMeta a (hTagGOr a ha1 ha2)).1, hTagG a ha1 ha2]

/-- Preservation of `SolverLevelCapsInv` directly from `PreservesLevelMeta` and chain equality on
the non-terminal levels `< d`. -/
theorem PreservesLevelMeta.to_capsInv {cfg : Alg2Config} {L P V vCap eCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {model model' : Alg2State cfg} {tok tok' : SolverToken cfg L Rcore} {mem mem' : ℕ → ℕ}
    (hPres : PreservesLevelMeta tok tok' mem mem')
    (hInv : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hN₀ : model'.chain.N₀ = model.chain.N₀)
    (hLvlM : ∀ j < cfg.P.d, model'.chain.lvlM j = model.chain.lvlM j)
    (hG : ∀ j < cfg.P.d, model'.chain.G j = model.chain.G j)
    (hSc : ∀ j < cfg.P.d, model'.chain.scState j = model.chain.scState j)
    (hBr : ∀ j < cfg.P.d, model'.chain.bran j = model.chain.bran j)
    (hℓ : model'.chain.ℓ = model.chain.ℓ) :
    SolverLevelCapsInv P V vCap eCap model' tok' mem' := by
  have hMC := solverLevelCapsInv_iff_metaCaps.mp hInv
  exact hInv.preserve hPres.1
    (fun j hj => by rw [hPres.2.2.2.1 j hj]; exact hPres.2.2.2.2.1 _ (hMC.2.1 j hj))
    hPres.metaEq
    (fun j hj => hPres.2.2.2.2.1 _ (hMC.2.2.2.2.2 j hj).2.2.1)
    hN₀ hLvlM hG hSc hBr hℓ

end MinCostFlow.MinRatio
