module

public import MinCostFlow.MinRatio.WireChainSpecs
import Mathlib.Tactic

/-!
# Level-metadata root identity and block disjointness (`SolverLevelLayout`)

Defines the two predicates capturing the layout properties of the `levelMeta` pointer
table at `solverLevelMetaAddr tok.table cfg.P.d`:

* `SolverLevelMetaDisjAt vCap eCap tok mem`: pairwise disjointness of the `d` level-graph blocks
  `[mem (levelMeta + d + j), + dynGraphSize vCap eCap)` and the `d` level-length blocks
  `[mem (levelMeta + r), + eCap * L)` for `j, r < cfg.P.d`. This is the exact conjunct exported
  by the chain core (`OrdChainUpdateCoreSpecWExtKFBL`, its meta-disjointness clause).
* `SolverLevelLayoutAt vCap eCap tok mem`: combines `mem (levelMeta + d + 0) = tok.rootGraph`
  (also exported by `OrdChainUpdateCoreSpecWExtKFBL` in `WireChainCoreSpecKFBL.lean`)
  with `SolverLevelMetaDisjAt vCap eCap tok mem`.

Also provides reusable construction and preservation lemmas for `Init`, `ShiftDeep`, non-level-
changing operations, and the chain core (`of_agree`, `of_monotone_blocks`, `of_prefix_and_suffix`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain DynSpanner.Program SparseCore.Program

/-- Pairwise disjointness of the `levelMeta` graph blocks `mem (levelMeta + d + j)` (of size
`dynGraphSize vCap eCap`) and length blocks `mem (levelMeta + r)` (of size `eCap * L`) for
`j, r < cfg.P.d`. This is the meta-disjointness clause of
`OrdChainUpdateCoreSpecWExtKFBL`. -/
@[expose] def SolverLevelMetaDisjAt {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (vCap eCap : ℕ) (tok : SolverToken cfg L Rcore) (mem : ℕ → ℕ) : Prop :=
  let d := cfg.P.d
  let levelMeta := solverLevelMetaAddr tok.table d
  (∀ j < d, ∀ a, mem (levelMeta + d + j) ≤ a →
    a < mem (levelMeta + d + j) + dynGraphSize vCap eCap →
    ∀ r < d,
      (a < mem (levelMeta + r) ∨ mem (levelMeta + r) + eCap * L ≤ a) ∧
      (r ≠ j → a < mem (levelMeta + d + r) ∨
        mem (levelMeta + d + r) + dynGraphSize vCap eCap ≤ a)) ∧
  (∀ j₁ < d, ∀ j₂ < d, j₁ ≠ j₂ →
    mem (levelMeta + j₁) + eCap * L ≤ mem (levelMeta + j₂) ∨
    mem (levelMeta + j₂) + eCap * L ≤ mem (levelMeta + j₁))

/-- Combined level-metadata layout invariant:
1. `mem (levelMeta + d + 0) = tok.rootGraph` (linking level `0`'s `levelMeta` graph pointer to
   `tok.rootGraph`, which implies `tok.rootECap = eCap` under `SolverLevelCapsAt vCap eCap`), and
2. `SolverLevelMetaDisjAt vCap eCap tok mem` (pairwise disjointness of all `levelMeta` graph and
   length blocks). -/
@[expose] def SolverLevelLayoutAt {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (vCap eCap : ℕ) (tok : SolverToken cfg L Rcore) (mem : ℕ → ℕ) : Prop :=
  let d := cfg.P.d
  let levelMeta := solverLevelMetaAddr tok.table d
  mem (levelMeta + d + 0) = tok.rootGraph ∧
  SolverLevelMetaDisjAt vCap eCap tok mem

theorem SolverLevelLayoutAt.of_root_and_disj {cfg : Alg2Config} {L vCap eCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hroot : mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d) = tok.rootGraph)
    (hdisj : SolverLevelMetaDisjAt vCap eCap tok mem) :
    SolverLevelLayoutAt vCap eCap tok mem :=
  ⟨by simpa only [Nat.add_zero] using hroot, hdisj⟩

theorem SolverLevelMetaDisjAt.of_agree {cfg : Alg2Config} {L vCap eCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ}
    (h : SolverLevelMetaDisjAt vCap eCap tok mem)
    (htab : tok'.table = tok.table)
    (hag : ∀ j < 2 * cfg.P.d,
      mem' (solverLevelMetaAddr tok.table cfg.P.d + j) =
        mem (solverLevelMetaAddr tok.table cfg.P.d + j)) :
    SolverLevelMetaDisjAt vCap eCap tok' mem' := by
  have hagL (r : ℕ) (hr : r < cfg.P.d) :
      mem' (solverLevelMetaAddr tok'.table cfg.P.d + r) =
        mem (solverLevelMetaAddr tok.table cfg.P.d + r) := by
    rw [htab]; exact hag r (by omega)
  have hagG (r : ℕ) (hr : r < cfg.P.d) :
      mem' (solverLevelMetaAddr tok'.table cfg.P.d + cfg.P.d + r) =
        mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + r) := by
    rw [htab, Nat.add_assoc]; exact hag (cfg.P.d + r) (by omega)
  refine ⟨fun j hj a ha1 ha2 r hr => ?_, fun j₁ hj₁ j₂ hj₂ hne => ?_⟩
  · rw [hagG j hj] at ha1 ha2
    rw [hagL r hr, hagG r hr]
    exact h.1 j hj a ha1 ha2 r hr
  · rw [hagL j₁ hj₁, hagL j₂ hj₂]
    exact h.2 j₁ hj₁ j₂ hj₂ hne

theorem SolverLevelLayoutAt.of_agree {cfg : Alg2Config} {L vCap eCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ}
    (h : SolverLevelLayoutAt vCap eCap tok mem)
    (hd : 0 < cfg.P.d)
    (htab : tok'.table = tok.table)
    (hroot : tok'.rootGraph = tok.rootGraph)
    (hag : ∀ j < 2 * cfg.P.d,
      mem' (solverLevelMetaAddr tok.table cfg.P.d + j) =
        mem (solverLevelMetaAddr tok.table cfg.P.d + j)) :
    SolverLevelLayoutAt vCap eCap tok' mem' := by
  refine ⟨?_, h.2.of_agree htab hag⟩
  rw [htab, hroot, Nat.add_zero]
  exact (hag cfg.P.d (by omega)).trans (by simpa only [Nat.add_zero] using h.1)

/-- Strict bump-pointer ordering across all `d` levels implies `SolverLevelMetaDisjAt`. -/
theorem SolverLevelMetaDisjAt.of_monotone_blocks {cfg : Alg2Config} {L vCap eCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hGL : ∀ j < cfg.P.d,
      mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap ≤
        mem (solverLevelMetaAddr tok.table cfg.P.d + j))
    (hLG : ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ < j₂ →
      mem (solverLevelMetaAddr tok.table cfg.P.d + j₁) + eCap * L ≤
        mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j₂)) :
    SolverLevelMetaDisjAt vCap eCap tok mem := by
  set d := cfg.P.d
  set lm := solverLevelMetaAddr tok.table d
  refine ⟨fun j hj a ha1 ha2 r hr => ⟨?_, fun hne => ?_⟩, fun j₁ hj₁ j₂ hj₂ hne => ?_⟩
  · rcases lt_trichotomy r j with hlt | rfl | hgt
    · exact Or.inr (le_trans (hLG r hr j hj hlt) ha1)
    · exact Or.inl (lt_of_lt_of_le ha2 (hGL r hr))
    · exact Or.inl (lt_of_lt_of_le ha2 (le_trans (hGL j hj)
        (le_trans (Nat.le_add_right _ _) (le_trans (hLG j hj r hr hgt)
          (le_trans (Nat.le_add_right _ _) (hGL r hr))))))
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inr (le_trans (hGL r hr) (le_trans (Nat.le_add_right _ _)
        (le_trans (hLG r hr j hj hlt) ha1)))
    · exact Or.inl (lt_of_lt_of_le ha2 (le_trans (hGL j hj)
        (le_trans (Nat.le_add_right _ _) (hLG j hj r hr hgt))))
  · rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (le_trans (hLG j₁ hj₁ j₂ hj₂ hlt) (le_trans (Nat.le_add_right _ _) (hGL j₂ hj₂)))
    · exact Or.inr (le_trans (hLG j₂ hj₂ j₁ hj₁ hgt) (le_trans (Nat.le_add_right _ _) (hGL j₁ hj₁)))

/-- Strict bump-pointer ordering across all `d` levels plus `mem (levelMeta + d + 0) = tok.rootGraph`
implies `SolverLevelLayoutAt` (used directly by `Init` and Branch A of the chain core). -/
theorem SolverLevelLayoutAt.of_monotone_blocks {cfg : Alg2Config} {L vCap eCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ}
    (hroot : mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + 0) = tok.rootGraph)
    (hGL : ∀ j < cfg.P.d,
      mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap ≤
        mem (solverLevelMetaAddr tok.table cfg.P.d + j))
    (hLG : ∀ j₁ < cfg.P.d, ∀ j₂ < cfg.P.d, j₁ < j₂ →
      mem (solverLevelMetaAddr tok.table cfg.P.d + j₁) + eCap * L ≤
        mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j₂)) :
    SolverLevelLayoutAt vCap eCap tok mem :=
  ⟨hroot, SolverLevelMetaDisjAt.of_monotone_blocks hGL hLG⟩

/-- Prefix/suffix builder for `SolverLevelMetaDisjAt`: if levels `≤ cut` keep their old pointers
strictly below `heap` (pairwise disjoint by `hOld`), and newly built levels `cut < j < d` are
allocated monotonically at `≥ heap`, then all `d` levels satisfy `SolverLevelMetaDisjAt`
(used directly by `ShiftDeep` and Branch B of the chain core). -/
theorem SolverLevelMetaDisjAt.of_prefix_and_suffix {cfg : Alg2Config} {L vCap eCap cut heap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem0 mem' : ℕ → ℕ}
    (hOld : SolverLevelMetaDisjAt vCap eCap tok mem0)
    (htab : tok'.table = tok.table)
    (hPreKeep : ∀ j ≤ cut, j < cfg.P.d →
      mem' (solverLevelMetaAddr tok.table cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) ∧
      mem' (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j))
    (hPreLt : ∀ j ≤ cut, j < cfg.P.d →
      mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) + eCap * L ≤ heap ∧
      mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap ≤ heap)
    (hSufGe : ∀ j, cut < j → j < cfg.P.d →
      heap ≤ mem' (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) ∧
      mem' (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap ≤
        mem' (solverLevelMetaAddr tok.table cfg.P.d + j))
    (hSufMono : ∀ j₁ j₂, cut < j₁ → j₁ < j₂ → j₂ < cfg.P.d →
      mem' (solverLevelMetaAddr tok.table cfg.P.d + j₁) + eCap * L ≤
        mem' (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j₂)) :
    SolverLevelMetaDisjAt vCap eCap tok' mem' := by
  dsimp only [SolverLevelMetaDisjAt]
  rw [htab]
  set d := cfg.P.d
  set lm := solverLevelMetaAddr tok.table d
  refine ⟨fun j hj a ha1 ha2 r hr => ⟨?_, fun hne => ?_⟩, fun j₁ hj₁ j₂ hj₂ hne => ?_⟩
  · by_cases hjP : j ≤ cut
    · rw [(hPreKeep j hjP hj).2] at ha1 ha2
      by_cases hrP : r ≤ cut
      · rw [(hPreKeep r hrP hr).1]
        exact (hOld.1 j hj a ha1 ha2 r hr).1
      · have hhi := (hPreLt j hjP hj).2
        have hlo := hSufGe r (by omega) hr
        exact Or.inl (by omega)
    · have hjS := hSufGe j (by omega) hj
      by_cases hrP : r ≤ cut
      · rw [(hPreKeep r hrP hr).1]
        have hhi := (hPreLt r hrP hr).1
        exact Or.inr (by omega)
      · rcases lt_trichotomy r j with hlt | rfl | hgt
        · exact Or.inr (le_trans (hSufMono r j (by omega) hlt hj) ha1)
        · exact Or.inl (lt_of_lt_of_le ha2 hjS.2)
        · have hrS := hSufGe r (by omega) hr
          exact Or.inl (lt_of_lt_of_le ha2 (le_trans hjS.2
            (le_trans (Nat.le_add_right _ _) (le_trans (hSufMono j r (by omega) hgt hr)
              (le_trans (Nat.le_add_right _ _) hrS.2)))))
  · by_cases hjP : j ≤ cut
    · rw [(hPreKeep j hjP hj).2] at ha1 ha2
      by_cases hrP : r ≤ cut
      · rw [(hPreKeep r hrP hr).2]
        exact (hOld.1 j hj a ha1 ha2 r hr).2 hne
      · have hhi := (hPreLt j hjP hj).2
        have hlo := (hSufGe r (by omega) hr).1
        exact Or.inl (by omega)
    · have hjS := hSufGe j (by omega) hj
      by_cases hrP : r ≤ cut
      · rw [(hPreKeep r hrP hr).2]
        have hhi := (hPreLt r hrP hr).2
        exact Or.inr (by omega)
      · have hrS := hSufGe r (by omega) hr
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inr (le_trans hrS.2 (le_trans (Nat.le_add_right _ _)
            (le_trans (hSufMono r j (by omega) hlt hj) ha1)))
        · exact Or.inl (lt_of_lt_of_le ha2 (le_trans hjS.2
            (le_trans (Nat.le_add_right _ _) (hSufMono j r (by omega) hgt hr))))
  · by_cases h1P : j₁ ≤ cut
    · rw [(hPreKeep j₁ h1P hj₁).1]
      by_cases h2P : j₂ ≤ cut
      · rw [(hPreKeep j₂ h2P hj₂).1]
        exact hOld.2 j₁ hj₁ j₂ hj₂ hne
      · have hhi := (hPreLt j₁ h1P hj₁).1
        have h2S := hSufGe j₂ (by omega) hj₂
        exact Or.inl (by omega)
    · have h1S := hSufGe j₁ (by omega) hj₁
      by_cases h2P : j₂ ≤ cut
      · rw [(hPreKeep j₂ h2P hj₂).1]
        have hhi := (hPreLt j₂ h2P hj₂).1
        exact Or.inr (by omega)
      · have h2S := hSufGe j₂ (by omega) hj₂
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl (le_trans (hSufMono j₁ j₂ (by omega) hlt hj₂)
            (le_trans (Nat.le_add_right _ _) h2S.2))
        · exact Or.inr (le_trans (hSufMono j₂ j₁ (by omega) hgt hj₁)
            (le_trans (Nat.le_add_right _ _) h1S.2))

/-- Prefix/suffix builder for `SolverLevelLayoutAt` when level `0` is in the preserved prefix
(`0 ≤ cut`, always true) and `tok'.rootGraph = tok.rootGraph`. -/
theorem SolverLevelLayoutAt.of_prefix_and_suffix {cfg : Alg2Config} {L vCap eCap cut heap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {tok tok' : SolverToken cfg L Rcore}
    {mem0 mem' : ℕ → ℕ}
    (hOld : SolverLevelLayoutAt vCap eCap tok mem0)
    (hd : 0 < cfg.P.d)
    (htab : tok'.table = tok.table)
    (hroot : tok'.rootGraph = tok.rootGraph)
    (hPreKeep : ∀ j ≤ cut, j < cfg.P.d →
      mem' (solverLevelMetaAddr tok.table cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) ∧
      mem' (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j))
    (hPreLt : ∀ j ≤ cut, j < cfg.P.d →
      mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) + eCap * L ≤ heap ∧
      mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap ≤ heap)
    (hSufGe : ∀ j, cut < j → j < cfg.P.d →
      heap ≤ mem' (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) ∧
      mem' (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap ≤
        mem' (solverLevelMetaAddr tok.table cfg.P.d + j))
    (hSufMono : ∀ j₁ j₂, cut < j₁ → j₁ < j₂ → j₂ < cfg.P.d →
      mem' (solverLevelMetaAddr tok.table cfg.P.d + j₁) + eCap * L ≤
        mem' (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j₂)) :
    SolverLevelLayoutAt vCap eCap tok' mem' := by
  refine ⟨?_, SolverLevelMetaDisjAt.of_prefix_and_suffix hOld.2 htab hPreKeep hPreLt hSufGe hSufMono⟩
  rw [htab, hroot, (hPreKeep 0 (Nat.zero_le _) hd).2]
  exact hOld.1

/-- Preservation of `SolverLevelLayoutAt` across any non-level-changing solver step satisfying
`PreservesLevelMeta` (since `levelMeta + j` has tag `22 + d ∈ LevelMetaFoot` by
`SolverLevelMetaAt`). -/
theorem PreservesLevelMeta.to_levelLayout {cfg : Alg2Config} {L P V vCap eCap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {model : Alg2State cfg} {tok tok' : SolverToken cfg L Rcore} {mem mem' : ℕ → ℕ}
    (hPres : PreservesLevelMeta tok tok' mem mem')
    (hMeta : SolverLevelMetaAt P V model tok mem)
    (hLay : SolverLevelLayoutAt vCap eCap tok mem) :
    SolverLevelLayoutAt vCap eCap tok' mem' :=
  hLay.of_agree cfg.P.hd hPres.tableEq hPres.rootGraphEq fun j hj =>
    (hPres.metaEq _ (Or.inr (Or.inr (Or.inl (hMeta.2.2.2.2.1 j hj))))).2

/-- Preservation of `SolverLevelLayoutAt` across a tail phase (such as select-region refresh)
that preserves `tok'.table = tok.table` and all memory tagged `≠ 0` and `≠ 21 + j` (`j < d`). -/
theorem SolverLevelLayoutAt.of_nonCore_agree {cfg : Alg2Config}
    {L P m V psi k epsExp drainUnit vCap eCap root : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok tok' : SolverToken cfg L Rcore} {mem mem' : ℕ → ℕ}
    (hLay : SolverLevelLayoutAt vCap eCap tok mem)
    (hRep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hRep' : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok' mem')
    (hMeta : SolverLevelMetaAt P V model tok mem)
    (htab : tok'.table = tok.table)
    (hAg : ∀ a, tok.tag a ≠ 0 → (∀ j < cfg.P.d, tok.tag a ≠ 21 + j) → mem' a = mem a) :
    SolverLevelLayoutAt vCap eCap tok' mem' := by
  have hRG : tok'.rootGraph = tok.rootGraph := by
    have h1 : mem' (root + 14) = tok'.rootGraph := by simpa using hRep'.1 14 (by simp)
    have h0 : mem (root + 14) = tok.rootGraph := by simpa using hRep.1 14 (by simp)
    have ht1 : tok.tag (root + 14) = 1 :=
      hRep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 14 (by omega)
    rw [← h1, hAg (root + 14) (by omega) (fun _ _ => by omega), h0]
  refine hLay.of_agree cfg.P.hd htab hRG fun j hj => ?_
  have ht22 : tok.tag (solverLevelMetaAddr tok.table cfg.P.d + j) = 22 + cfg.P.d :=
    hMeta.2.2.2.2.1 j hj
  exact hAg _ (by omega) (fun _ hr => by omega)

/-- Preservation of `SolverLevelLayoutAt` across a deep shift at level `cut`: levels `≤ cut` keep
their old blocks `< heap` (from tags in `Rrep.foot`), and rebuilt levels `> cut` have monotone
blocks allocated at `≥ heap`. -/
theorem SolverLevelLayoutAt.of_shiftDeep {cfg : Alg2Config}
    {L P V vCap eCap cut heap : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {model : Alg2State cfg}
    {tok tok' : SolverToken cfg L Rcore} {mem0 mem5 mem11 : ℕ → ℕ}
    (hOld : SolverLevelLayoutAt vCap eCap tok mem0)
    (hOwnOfTag : ∀ a, tok.tag a ≠ 0 → tok.owned a)
    (hOwnLt : ∀ a, tok.owned a → a < heap)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : ∀ j < cfg.P.d,
      DynGraphAt mem0 (mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j)) vCap eCap (model.chain.G j))
    (htab : tok'.table = tok.table)
    (hroot : tok'.rootGraph = tok.rootGraph)
    (hTag22 : ∀ a, tok.tag a = 22 + cfg.P.d → mem11 a = mem5 a)
    (hPreKeep : ∀ j ≤ cut, j < cfg.P.d →
      mem5 (solverLevelMetaAddr tok.table cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) ∧
      mem5 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
        mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j))
    (hSufGe5 : ∀ j, cut < j → j < cfg.P.d →
      heap ≤ mem5 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) ∧
      mem5 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap ≤
        mem5 (solverLevelMetaAddr tok.table cfg.P.d + j))
    (hSufMono5 : ∀ j₁ j₂, cut < j₁ → j₁ < j₂ → j₂ < cfg.P.d →
      mem5 (solverLevelMetaAddr tok.table cfg.P.d + j₁) + eCap * L ≤
        mem5 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j₂)) :
    SolverLevelLayoutAt vCap eCap tok' mem11 := by
  have h11L (j : ℕ) (hj : j < cfg.P.d) :
      mem11 (solverLevelMetaAddr tok.table cfg.P.d + j) =
        mem5 (solverLevelMetaAddr tok.table cfg.P.d + j) :=
    hTag22 _ (hMeta0.2.2.2.2.1 j (by omega))
  have h11G (j : ℕ) (hj : j < cfg.P.d) :
      mem11 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
        mem5 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := by
    have ht := hMeta0.2.2.2.2.1 (cfg.P.d + j) (by omega)
    rw [← Nat.add_assoc] at ht
    exact hTag22 _ ht
  refine hOld.of_prefix_and_suffix cfg.P.hd htab hroot
    (fun j hle hj => by rw [h11L j hj, h11G j hj]; exact hPreKeep j hle hj)
    (fun j _ hj => ?_)
    (fun j hgt hj => by rw [h11G j hj, h11L j hj]; exact hSufGe5 j hgt hj)
    (fun j₁ j₂ hgt hlt hj2 => by rw [h11L j₁ (lt_trans hlt hj2), h11G j₂ hj2]; exact hSufMono5 j₁ j₂ hgt hlt hj2)
  obtain ⟨vc, ec, hDG, _, hOwnL, hTagL, hTagG⟩ := hMeta0.2.2.2.2.2 j hj
  have hvc : vc = vCap := hDG.2.2.2.1.symm.trans (hCaps0 j hj).2.2.2.1
  have hec : ec = eCap := hDG.2.2.2.2.1.symm.trans (hCaps0 j hj).2.2.2.2.1
  subst vc ec
  refine ⟨?_, ?_⟩
  · by_cases heL : eCap * L = 0
    · have := hOwnLt _ hOwnL; omega
    · have ht := hTagL (mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) + eCap * L - 1) (by omega) (by omega)
      have hnz : tok.tag (mem0 (solverLevelMetaAddr tok.table cfg.P.d + j) + eCap * L - 1) ≠ 0 := by omega
      have := hOwnLt _ (hOwnOfTag _ hnz); omega
  · have hdgPos : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    have ht := hTagG (mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap - 1)
      (by omega) (by omega)
    have hnz : tok.tag (mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) + dynGraphSize vCap eCap - 1) ≠ 0 := by
      split_ifs at ht <;> omega
    have := hOwnLt _ (hOwnOfTag _ hnz); omega

/-- Transport `SolverLevelLayoutAt` across a `PreservesLevelMeta` step followed by a memory step
that agrees on the solver footprint `Rrep.foot root tok'`. -/
theorem PreservesLevelMeta.to_levelLayout_of_foot
    {cfg : Alg2Config} {L P m V psi k epsExp drainUnit vCap eCap root : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {model model' : Alg2State cfg} {tok tok' : SolverToken cfg L Rcore}
    {mem0 mem1 mem2 : ℕ → ℕ}
    (hPres : PreservesLevelMeta tok tok' mem0 mem1)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hRep1 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model' tok' mem1)
    (hAg : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a →
      mem2 a = mem1 a)
    (hLay0 : SolverLevelLayoutAt vCap eCap tok mem0) :
    SolverLevelLayoutAt vCap eCap tok' mem2 := by
  have hLay1 := hPres.to_levelLayout hMeta0 hLay0
  refine hLay1.of_agree cfg.P.hd rfl rfl (fun j hj => ?_)
  have hLM0 : LevelMetaFoot tok (solverLevelMetaAddr tok'.table cfg.P.d + j) := by
    rw [hPres.tableEq]; exact Or.inr (Or.inr (Or.inl (hMeta0.2.2.2.2.1 j hj)))
  exact hAg _ (LevelMetaFoot.mem_foot hRep1 (hPres.levelMetaFoot_mono hLM0))

end MinCostFlow.MinRatio
