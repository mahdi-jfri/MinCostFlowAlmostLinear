module

public import MinCostFlow.SparseCore.Program.CompSplitListCut
import Mathlib.Tactic.Linarith

/-!
# Functional Reverse Union-Find Model (`CompSplitListUF`)

Defines the union-by-size reverse Union-Find state `RevUFState`, operations (`ufInitOne`,
`ufFindFuel`, `ufUnion`, `ufPair`), and representation invariant `RevUFInv`, proving that
processing sorted released edges `D` in reverse order computes every release entry of
`canonStepSplits cs u` and matches `inputSplitEntries cs u` at the end.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.SparseCore

@[expose] public section

/-! ## 3. Functional Reverse Union-Find state, operations, and invariant -/

/-- Pure functional Union-Find state matching the four `vCap`-sized scratch arrays in Word-RAM:
`par[r]` (parent pointer), `sz[r]` (component size, `0` iff untouched singleton),
`minF[r]` (minimum final root in component), and `oldR[r]` (`oldRoot + 1`, or `0` if none). -/
structure RevUFState where
  par : ℕ → ℕ
  sz : ℕ → ℕ
  minF : ℕ → ℕ
  oldR : ℕ → ℕ

/-- Initial all-zero Union-Find state (every final root is an untouched singleton). -/
def RevUFState.zero : RevUFState := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- Lazy singleton initialization of a final root `r` if untouched (`U.sz r = 0`). -/
def ufInitOne (isOld : ℕ → Bool) (U : RevUFState) (r : ℕ) : RevUFState :=
  if U.sz r = 0 then
    ⟨Function.update U.par r r,
     Function.update U.sz r 1,
     Function.update U.minF r r,
     Function.update U.oldR r (if isOld r then r + 1 else 0)⟩
  else U

/-- Fuel-bounded parent walk in `U.par`. -/
def ufFindFuel : ℕ → (ℕ → ℕ) → ℕ → ℕ
  | 0, _, x => x
  | k + 1, par, x => if par x = x then x else ufFindFuel k par (par x)

/-- Union-by-size merging two active UF roots `ra` and `rb` (`ra ≠ rb`). -/
def ufUnion (U : RevUFState) (ra rb : ℕ) : RevUFState :=
  let (big, small) := if U.sz ra ≥ U.sz rb then (ra, rb) else (rb, ra)
  ⟨Function.update U.par small big,
   Function.update U.sz big (U.sz big + U.sz small),
   Function.update U.minF big (min (U.minF big) (U.minF small)),
   Function.update U.oldR big (if U.oldR big ≠ 0 then U.oldR big else U.oldR small)⟩

/-- Algebraic `(kept, fresh)` query on two active UF roots `ra, rb`. -/
def ufPair (U : RevUFState) (ra rb : ℕ) : ℕ × ℕ :=
  mergeSplitPair
    (if U.oldR ra = 0 then none else some (U.oldR ra - 1)) (U.minF ra)
    (if U.oldR rb = 0 then none else some (U.oldR rb - 1)) (U.minF rb)

/-- Representation invariant of `RevUFState` for an intermediate forest `F` (`F.V = RF'.F.V`,
`F.IsSubgraph RF'.F`) over final rooted forest `RF'` and old root set `R_old ⊆ RF'.R`. -/
structure RevUFInv (F : MGraph) (RF' : RootedForest) (R_old : Finset ℕ) (U : RevUFState) : Prop where
  /-- Non-roots of `RF'` are always untouched (`sz = 0`). -/
  hNotR : ∀ x, x ∉ RF'.R → U.sz x = 0
  /-- Untouched final roots (`sz r = 0`) are singleton `R_fin`-classes in `F`. -/
  hUntouched : ∀ r ∈ RF'.R, U.sz r = 0 → compOf F r ∩ RF'.R = {r}
  /-- Every active size is bounded by `RF'.R.card`. -/
  hSzLe : ∀ r ∈ RF'.R, U.sz r ≤ RF'.R.card
  /-- Active final roots have valid parent in `RF'.R`, connected in `F`, with doubling sizes. -/
  hActivePar : ∀ r ∈ RF'.R, 1 ≤ U.sz r →
    U.par r ∈ RF'.R ∧ 1 ≤ U.sz (U.par r) ∧ F.Connected r (U.par r) ∧
    (U.par r ≠ r → 2 * U.sz r ≤ U.sz (U.par r))
  /-- For every active root (`1 ≤ sz r` and `par r = r`), `sz`, `minF`, `oldR` match `compOf F r`. -/
  hRootMeta : ∀ r ∈ RF'.R, 1 ≤ U.sz r → U.par r = r →
    U.sz r = (compOf F r ∩ RF'.R).card ∧
    (∀ h : (compOf F r ∩ RF'.R).Nonempty, U.minF r = (compOf F r ∩ RF'.R).min' h) ∧
    (open Classical in U.oldR r = if h : (compOf F r ∩ R_old).Nonempty then ((compOf F r ∩ R_old).min' h) + 1 else 0)
  /-- Two active UF roots in the same `F`-component are equal. -/
  hRootUnique : ∀ r₁ ∈ RF'.R, ∀ r₂ ∈ RF'.R,
    1 ≤ U.sz r₁ → U.par r₁ = r₁ → 1 ≤ U.sz r₂ → U.par r₂ = r₂ →
    F.Connected r₁ r₂ → r₁ = r₂

/-- Parent walk from any active `x ∈ RF'.R` reaches an active UF root `rep` connected to `x` in `F`
in at most `steps ≤ Nat.log 2 (U.sz rep)` steps. -/
lemma RevUFInv.find_terminates {F : MGraph} {RF' : RootedForest} {R_old : Finset ℕ} {U : RevUFState}
    (hU : RevUFInv F RF' R_old U) {x : ℕ} (hxR : x ∈ RF'.R) (hxAct : 1 ≤ U.sz x) :
    ∃ rep steps, rep ∈ RF'.R ∧ 1 ≤ U.sz rep ∧ U.par rep = rep ∧
      F.Connected x rep ∧
      ufFindFuel steps U.par x = rep ∧
      (∀ k ≥ steps, ufFindFuel k U.par x = rep) ∧
      2 ^ steps * U.sz x ≤ U.sz rep ∧
      steps ≤ Nat.log 2 (U.sz rep) := by
  have hgo : ∀ rem x, x ∈ RF'.R → 1 ≤ U.sz x → RF'.R.card - U.sz x ≤ rem →
      ∃ rep steps, rep ∈ RF'.R ∧ 1 ≤ U.sz rep ∧ U.par rep = rep ∧
        F.Connected x rep ∧
        ufFindFuel steps U.par x = rep ∧
        (∀ k ≥ steps, ufFindFuel k U.par x = rep) ∧
        2 ^ steps * U.sz x ≤ U.sz rep := by
    intro rem
    induction rem with
    | zero =>
      intro x hxR hxAct hrem
      have hsz_eq : U.sz x = RF'.R.card := le_antisymm (hU.hSzLe x hxR) (by omega)
      obtain ⟨hpR, _, _, hdoub⟩ := hU.hActivePar x hxR hxAct
      have hpar_eq : U.par x = x := by
        by_contra hne
        have h1 := hdoub hne
        have h2 := hU.hSzLe (U.par x) hpR
        omega
      refine ⟨x, 0, hxR, hxAct, hpar_eq, connected_refl F x, rfl, ?_, by simp⟩
      intro k _
      cases k with
      | zero => rfl
      | succ k => simp [ufFindFuel, hpar_eq]
    | succ rem ih =>
      intro x hxR hxAct hrem
      by_cases hpar : U.par x = x
      · refine ⟨x, 0, hxR, hxAct, hpar, connected_refl F x, rfl, ?_, by simp⟩
        intro k _
        cases k with
        | zero => rfl
        | succ k => simp [ufFindFuel, hpar]
      · obtain ⟨hpR, hpAct, hconn, hdoub⟩ := hU.hActivePar x hxR hxAct
        have hsz_lt : U.sz x < U.sz (U.par x) := by have := hdoub hpar; omega
        have hsz_le := hU.hSzLe (U.par x) hpR
        obtain ⟨rep, steps, hrepR, hrepAct, hrepPar, hrepConn, hfind, hfindGe, hpow⟩ :=
          ih (U.par x) hpR hpAct (by omega)
        refine ⟨rep, steps + 1, hrepR, hrepAct, hrepPar, connected_trans hconn hrepConn,
          by simp [ufFindFuel, hpar, hfind], ?_, ?_⟩
        · intro k hk
          cases k with
          | zero => omega
          | succ k => simp [ufFindFuel, hpar, hfindGe k (by omega)]
        · calc 2 ^ (steps + 1) * U.sz x = 2 ^ steps * (2 * U.sz x) := by ring
            _ ≤ 2 ^ steps * U.sz (U.par x) := Nat.mul_le_mul_left _ (hdoub hpar)
            _ ≤ U.sz rep := hpow
  obtain ⟨rep, steps, hrepR, hrepAct, hrepPar, hconn, hfind, hfindGe, hpow⟩ :=
    hgo (RF'.R.card - U.sz x) x hxR hxAct le_rfl
  have hlog : steps ≤ Nat.log 2 (U.sz rep) := by
    have h2 : 2 ^ steps ≤ U.sz rep := le_trans (by
      have : 2 ^ steps * 1 ≤ 2 ^ steps * U.sz x := Nat.mul_le_mul_left _ hxAct
      simpa using this) hpow
    exact (Nat.le_log_of_pow_le (by omega) h2)
  exact ⟨rep, steps, hrepR, hrepAct, hrepPar, hconn, hfind, hfindGe, hpow, hlog⟩

/-- All-zero `RevUFState.zero` satisfies `RevUFInv` for the final forest `RF'.F`. -/
theorem revUFInv_zero {G : MGraph} {RF' : RootedForest} {R_old : Finset ℕ}
    (hRF' : RF'.IsRootedSpanningForestOf G) :
    RevUFInv RF'.F RF' R_old RevUFState.zero := by
  refine ⟨fun _ _ => rfl, fun r hr _ => ?_, fun _ _ => Nat.zero_le _,
    fun _ _ h => by simp [RevUFState.zero] at h,
    fun _ _ h => by simp [RevUFState.zero] at h,
    fun _ _ _ _ h => by simp [RevUFState.zero] at h⟩
  ext x
  simp only [Finset.mem_inter, mem_compOf_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨_, hc⟩, hxR⟩
    have h1 := root_eq_of_mem_R hRF' hr
    have h2 := root_eq_of_mem_R hRF' hxR
    have h3 := root_eq_of_connected hRF' (hRF'.2.2.1 hr) (hRF'.2.2.1 hxR) hc
    exact (h2.symm.trans (h3.symm.trans h1))
  · rintro rfl
    exact ⟨⟨hRF'.2.1.symm ▸ hRF'.2.2.1 hr, connected_refl RF'.F x⟩, hr⟩

/-- Lazy singleton initialization `ufInitOne` preserves `RevUFInv` and activates `r`. -/
theorem revUFInv_initOne {F : MGraph} {RF' : RootedForest} {R_old : Finset ℕ} {U : RevUFState}
    {isOld : ℕ → Bool}
    (hU : RevUFInv F RF' R_old U)
    (hOld : R_old ⊆ RF'.R)
    (hRF'V : ∀ x ∈ RF'.R, x ∈ F.V)
    (hisOld : ∀ r ∈ RF'.R, isOld r = true ↔ r ∈ R_old)
    {r : ℕ} (hrR : r ∈ RF'.R) :
    let U' := ufInitOne isOld U r
    RevUFInv F RF' R_old U' ∧ 1 ≤ U'.sz r := by
  classical
  intro U'
  by_cases hz : U.sz r = 0
  · have hsing : compOf F r ∩ RF'.R = {r} := hU.hUntouched r hrR hz
    have hcard_pos : 1 ≤ RF'.R.card := Finset.card_pos.mpr ⟨r, hrR⟩
    have hU'_def : U' = ⟨Function.update U.par r r, Function.update U.sz r 1,
        Function.update U.minF r r,
        Function.update U.oldR r (if isOld r then r + 1 else 0)⟩ := by
      simp [U', ufInitOne, hz]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [hU'_def]; simp⟩
    · intro x hx; rw [hU'_def]; dsimp only
      have hne : x ≠ r := fun h => hx (h ▸ hrR)
      rw [Function.update_of_ne hne]; exact hU.hNotR x hx
    · intro x hx hsz; rw [hU'_def] at hsz; dsimp only at hsz
      by_cases hxr : x = r
      · subst hxr; simp at hsz
      · rw [Function.update_of_ne hxr] at hsz; exact hU.hUntouched x hx hsz
    · intro x hx; rw [hU'_def]; dsimp only
      by_cases hxr : x = r
      · subst hxr; simp [hcard_pos]
      · rw [Function.update_of_ne hxr]; exact hU.hSzLe x hx
    · intro x hx hact; rw [hU'_def] at hact ⊢; dsimp only at hact ⊢
      by_cases hxr : x = r
      · subst x; simp [hrR, connected_refl F r]
      · rw [Function.update_of_ne hxr] at hact ⊢
        obtain ⟨hpR, hpAct, hconn, hdoub⟩ := hU.hActivePar x hx hact
        have hpr_ne : U.par x ≠ r := fun h => by rw [h] at hpAct; omega
        refine ⟨hpR, by rw [Function.update_of_ne hpr_ne]; exact hpAct, hconn, fun hne => ?_⟩
        rw [Function.update_of_ne hpr_ne, Function.update_of_ne hxr]; exact hdoub hne
    · intro x hx hact hpar; rw [hU'_def] at hact hpar ⊢; dsimp only at hact hpar ⊢
      by_cases hxr : x = r
      · subst x
        simp only [Function.update_self, hsing, Finset.card_singleton, Finset.min'_singleton, true_and]
        have hsub : compOf F r ∩ R_old ⊆ {r} := fun z hz => by
          have hz1 := (Finset.mem_inter.mp hz).1
          have hz2 := hOld (Finset.mem_inter.mp hz).2
          rw [← hsing]; exact Finset.mem_inter.mpr ⟨hz1, hz2⟩
        by_cases hro : r ∈ R_old
        · have hne : (compOf F r ∩ R_old).Nonempty :=
            ⟨r, Finset.mem_inter.mpr ⟨self_mem_compOf (hRF'V r hrR), hro⟩⟩
          have hmin : (compOf F r ∩ R_old).min' hne = r :=
            Finset.mem_singleton.mp (hsub (Finset.min'_mem _ hne))
          simp only [(hisOld r hrR).mpr hro, hne, ↓reduceIte, ↓reduceDIte, hmin]
          exact ⟨fun _ => trivial, trivial⟩
        · have hempty : ¬ (compOf F r ∩ R_old).Nonempty := by
            rintro ⟨z, hz⟩
            have hzr : z = r := Finset.mem_singleton.mp (hsub hz)
            exact hro (hzr ▸ (Finset.mem_inter.mp hz).2)
          have hfalse : isOld r = false := Bool.eq_false_iff.mpr fun h => hro ((hisOld r hrR).mp h)
          simp only [hfalse, Bool.false_eq_true, hempty, ↓reduceIte, ↓reduceDIte]
          exact ⟨fun _ => trivial, trivial⟩
      · simp only [Function.update_of_ne hxr] at hact hpar ⊢
        exact hU.hRootMeta x hx hact hpar
    · intro r₁ hr₁ r₂ hr₂ ha₁ hp₁ ha₂ hp₂ hconn
      rw [hU'_def] at ha₁ hp₁ ha₂ hp₂; dsimp only at ha₁ hp₁ ha₂ hp₂
      by_cases h1 : r₁ = r <;> by_cases h2 : r₂ = r
      · exact h1.trans h2.symm
      · subst h1
        have hmem : r₂ ∈ compOf F r₁ ∩ RF'.R :=
          Finset.mem_inter.mpr ⟨mem_compOf_iff.mpr ⟨hRF'V r₂ hr₂, hconn⟩, hr₂⟩
        rw [hsing, Finset.mem_singleton] at hmem; exact hmem.symm
      · subst h2
        have hmem : r₁ ∈ compOf F r₂ ∩ RF'.R :=
          Finset.mem_inter.mpr ⟨mem_compOf_iff.mpr ⟨hRF'V r₁ hr₁, connected_symm hconn⟩, hr₁⟩
        rw [hsing, Finset.mem_singleton] at hmem; exact hmem
      · rw [Function.update_of_ne h1] at ha₁ hp₁; rw [Function.update_of_ne h2] at ha₂ hp₂
        exact hU.hRootUnique r₁ hr₁ r₂ hr₂ ha₁ hp₁ ha₂ hp₂ hconn
  · have hpos : 1 ≤ U.sz r := by omega
    have hU'_eq : U' = U := by simp [U', ufInitOne, hz]
    exact ⟨hU'_eq ▸ hU, hU'_eq ▸ hpos⟩

/-- Merging edge `e ∈ F₀.E` in reverse (from `F₁ = eraseForestEdge F₀ e` back to `F₀`):
given `RevUFInv F₁ RF' R_old U` with active roots `ra, rb` of `RF'.root (F₀.tail e)` and
`RF'.root (F₀.head e)`, we have `ra ≠ rb`, `ufPair U ra rb` equals the exact canonical cut pair
`((RootedForest.mk F₀ R₀).root (F₀.tail e), newRoot R₁ R₀)`, and `ufUnion U ra rb` satisfies
`RevUFInv F₀ RF' R_old`. -/
theorem revUFInv_union_edge {G F₀ : MGraph} {RF' : RootedForest} {R_old : Finset ℕ}
    {U : RevUFState} {e ra rb : ℕ}
    (hF₀ : F₀.IsForest) (hV₀ : F₀.V = G.V) (hF₀G : G.IsSubgraph F₀)
    (he : e ∈ F₀.E) (hF₁sub : (eraseForestEdge F₀ e).IsSubgraph RF'.F)
    (hRF' : RF'.IsRootedSpanningForestOf G) (hOld : R_old ⊆ RF'.R)
    (hSep₀ : ∀ r ∈ R_old, ∀ s ∈ R_old, F₀.Connected r s → r = s)
    (hU : RevUFInv (eraseForestEdge F₀ e) RF' R_old U)
    (hraR : ra ∈ RF'.R) (hraAct : 1 ≤ U.sz ra) (hraPar : U.par ra = ra)
    (hraConn : (eraseForestEdge F₀ e).Connected (RF'.root (F₀.tail e)) ra)
    (hrbR : rb ∈ RF'.R) (hrbAct : 1 ≤ U.sz rb) (hrbPar : U.par rb = rb)
    (hrbConn : (eraseForestEdge F₀ e).Connected (RF'.root (F₀.head e)) rb) :
    let F₁ := eraseForestEdge F₀ e
    let R₀ := canonRoots F₀ R_old RF'.R
    let R₁ := canonRoots F₁ R₀ RF'.R
    ra ≠ rb ∧
    ufPair U ra rb = ((RootedForest.mk F₀ R₀).root (F₀.tail e), newRoot R₁ R₀) ∧
    RevUFInv F₀ RF' R_old (ufUnion U ra rb) := by
  classical
  intro F₁ R₀ R₁
  set a := F₀.tail e; set b := F₀.head e
  have haG : a ∈ G.V := hV₀ ▸ (hF₀.1 e he).1
  have hbG : b ∈ G.V := hV₀ ▸ (hF₀.1 e he).2
  have ha_ra : F₁.Connected a ra :=
    connected_trans (connected_of_subgraph hF₁sub (root_mem_R hRF' haG).2) hraConn
  have hb_rb : F₁.Connected b rb :=
    connected_trans (connected_of_subgraph hF₁sub (root_mem_R hRF' hbG).2) hrbConn
  set A := compOf F₁ a; set B := compOf F₁ b
  have hA_eq : compOf F₁ ra = A := compOf_eq_of_connected (connected_symm ha_ra)
  have hB_eq : compOf F₁ rb = B := compOf_eq_of_connected (connected_symm hb_rb)
  obtain ⟨hDisj, hP_eq, hOther⟩ := eraseForestEdge_compOf_split hF₀ he
  have hra_in_A : ra ∈ A := mem_compOf_iff.mpr ⟨hV₀.symm ▸ hRF'.2.2.1 hraR, ha_ra⟩
  have hrb_in_B : rb ∈ B := mem_compOf_iff.mpr ⟨hV₀.symm ▸ hRF'.2.2.1 hrbR, hb_rb⟩
  have hne : ra ≠ rb := fun h => Finset.disjoint_left.mp hDisj hra_in_A (h ▸ hrb_in_B)
  -- `ufPair U ra rb` matches `canonCut_pair_eq`
  obtain ⟨hszA, hminA, holdA⟩ := hU.hRootMeta ra hraR hraAct hraPar
  obtain ⟨hszB, hminB, holdB⟩ := hU.hRootMeta rb hrbR hrbAct hrbPar
  rw [hA_eq] at hszA hminA holdA
  rw [hB_eq] at hszB hminB holdB
  have hAf : (A ∩ RF'.R).Nonempty := ⟨ra, Finset.mem_inter.mpr ⟨hra_in_A, hraR⟩⟩
  have hBf : (B ∩ RF'.R).Nonempty := ⟨rb, Finset.mem_inter.mpr ⟨hrb_in_B, hrbR⟩⟩
  have hpair_eq : ufPair U ra rb = ((RootedForest.mk F₀ R₀).root a, newRoot R₁ R₀) := by
    rw [canonCut_pair_eq hF₀ hV₀ hF₀G he hF₁sub hRF' hOld hSep₀]
    dsimp only [ufPair]
    rw [hminA hAf, hminB hBf, holdA, holdB]
    have hopt : ∀ (S : Finset ℕ),
        (if (if h : S.Nonempty then S.min' h + 1 else 0) = 0 then none
         else some ((if h : S.Nonempty then S.min' h + 1 else 0) - 1)) =
        (if h : S.Nonempty then some (S.min' h) else none) := fun S => by
      by_cases h : S.Nonempty <;> simp [h]
    rw [hopt (A ∩ R_old), hopt (B ∩ R_old)]
  -- Prove `RevUFInv F₀ RF' R_old (ufUnion U ra rb)`
  have hsub01 : F₀.IsSubgraph F₁ := eraseForestEdge_subgraph F₀ e
  -- Orient `(big, small)` symmetrically
  have hunion_symm : ∀ (big small : ℕ),
      (big = ra ∧ small = rb ∨ big = rb ∧ small = ra) → U.sz small ≤ U.sz big →
      RevUFInv F₀ RF' R_old
        ⟨Function.update U.par small big,
         Function.update U.sz big (U.sz big + U.sz small),
         Function.update U.minF big (min (U.minF big) (U.minF small)),
         Function.update U.oldR big (if U.oldR big ≠ 0 then U.oldR big else U.oldR small)⟩ := by
    intro big small hor hsz_le
    have hbig_ne_small : big ≠ small := by rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact hne; exact hne.symm]
    have hbigR : big ∈ RF'.R := by rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hsmallR : small ∈ RF'.R := by rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hbigAct : 1 ≤ U.sz big := by rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hsmallAct : 1 ≤ U.sz small := by rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hbigPar : U.par big = big := by rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hsmallPar : U.par small = small := by rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hcomp_union : compOf F₁ big ∪ compOf F₁ small = A ∪ B := by
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hA_eq, hB_eq]
      · rw [hA_eq, hB_eq, Finset.union_comm]
    have hcomp_disj : Disjoint (compOf F₁ big) (compOf F₁ small) := by
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hA_eq, hB_eq]; exact hDisj
      · rw [hA_eq, hB_eq]; exact hDisj.symm
    have hcompF0_big : compOf F₀ big = A ∪ B := by
      have hbin : big ∈ A ∪ B := by rw [← hcomp_union]; exact Finset.mem_union_left _ (self_mem_compOf (hV₀.symm ▸ hRF'.2.2.1 hbigR))
      exact (compOf_eq_of_connected (connected_symm (mem_compOf_iff.mp (hP_eq.symm ▸ hbin)).2)).trans hP_eq
    have hsmall_big_F0 : F₀.Connected small big := by
      have hsin : small ∈ compOf F₀ big := by
        rw [hcompF0_big, ← hcomp_union]; exact Finset.mem_union_right _ (self_mem_compOf (hV₀.symm ▸ hRF'.2.2.1 hsmallR))
      exact connected_symm (mem_compOf_iff.mp hsin).2
    have hsum_card : U.sz big + U.sz small = (compOf F₀ big ∩ RF'.R).card := by
      have hdisj_inter : Disjoint (compOf F₁ big ∩ RF'.R) (compOf F₁ small ∩ RF'.R) :=
        Finset.disjoint_left.mpr fun x h1 h2 =>
          Finset.disjoint_left.mp hcomp_disj (Finset.mem_inter.mp h1).1 (Finset.mem_inter.mp h2).1
      rw [hcompF0_big, ← hcomp_union, Finset.union_inter_distrib_right, Finset.card_union_of_disjoint hdisj_inter]
      rw [(hU.hRootMeta big hbigR hbigAct hbigPar).1, (hU.hRootMeta small hsmallR hsmallAct hsmallPar).1]
    have hsum_le : U.sz big + U.sz small ≤ RF'.R.card := by
      rw [hsum_card]; exact Finset.card_le_card Finset.inter_subset_right
    -- Notice: no untouched vertex lies in `A ∪ B`! Because `ra ∈ A` and `rb ∈ B` are active,
    -- any `x ∈ A ∩ RF'.R` is connected to `ra` in `F₁`, so `compOf F₁ x ∩ RF'.R = A ∩ RF'.R`,
    -- which if `x` were untouched (`= {x}`) would force `x = ra`, contradicting `1 ≤ U.sz ra`!
    have hnot_untouched_AB : ∀ r ∈ RF'.R, U.sz r = 0 → r ∉ A ∪ B := fun r hr hsz hrAB => by
      have hsing := hU.hUntouched r hr hsz
      rcases Finset.mem_union.mp hrAB with hrA | hrB
      · have hceq : compOf F₁ r = A := compOf_eq_of_connected (connected_symm (mem_compOf_iff.mp hrA).2)
        have : ra ∈ compOf F₁ r ∩ RF'.R := Finset.mem_inter.mpr ⟨hceq.symm ▸ hra_in_A, hraR⟩
        rw [hsing, Finset.mem_singleton] at this; subst this; omega
      · have hceq : compOf F₁ r = B := compOf_eq_of_connected (connected_symm (mem_compOf_iff.mp hrB).2)
        have : rb ∈ compOf F₁ r ∩ RF'.R := Finset.mem_inter.mpr ⟨hceq.symm ▸ hrb_in_B, hrbR⟩
        rw [hsing, Finset.mem_singleton] at this; subst this; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx; dsimp only
      have hxb : x ≠ big := fun h => hx (h ▸ hbigR)
      rw [Function.update_of_ne hxb]; exact hU.hNotR x hx
    · intro r hr hsz; dsimp only at hsz
      by_cases hrb' : r = big
      · subst r; simp at hsz; omega
      · rw [Function.update_of_ne hrb'] at hsz
        rw [hOther r (hV₀.symm ▸ hRF'.2.2.1 hr) (hnot_untouched_AB r hr hsz)]
        exact hU.hUntouched r hr hsz
    · intro r hr; dsimp only
      by_cases hrb' : r = big
      · subst r; simpa using hsum_le
      · rw [Function.update_of_ne hrb']; exact hU.hSzLe r hr
    · intro r hr hact; dsimp only at hact ⊢
      have hrAct0 : 1 ≤ U.sz r := by
        by_cases hrb' : r = big
        · subst r; exact hbigAct
        · rwa [Function.update_of_ne hrb'] at hact
      by_cases hrs : r = small
      · subst r
        simp only [Function.update_self, Function.update_of_ne hbig_ne_small.symm]
        refine ⟨hbigR, by omega, hsmall_big_F0, fun _ => by omega⟩
      · rw [Function.update_of_ne hrs]
        obtain ⟨hpR, hpAct, hconn, hdoub⟩ := hU.hActivePar r hr hrAct0
        refine ⟨hpR, ?_, connected_of_subgraph hsub01 hconn, fun hne' => ?_⟩
        · by_cases hpb : U.par r = big
          · rw [hpb, Function.update_self]; omega
          · rw [Function.update_of_ne hpb]; exact hpAct
        · have hrb' : r ≠ big := fun h => hne' (h ▸ hbigPar)
          rw [Function.update_of_ne hrb']
          by_cases hpb : U.par r = big
          · rw [hpb, Function.update_self]; have := hdoub hne'; rw [hpb] at this; omega
          · rw [Function.update_of_ne hpb]; exact hdoub hne'
    · intro r hr hact hpar; dsimp only at hact hpar ⊢
      by_cases hrb' : r = big
      · subst r
        simp only [Function.update_self]
        have hbigf : (compOf F₁ big ∩ RF'.R).Nonempty := ⟨big, Finset.mem_inter.mpr ⟨self_mem_compOf (hV₀.symm ▸ hRF'.2.2.1 hbigR), hbigR⟩⟩
        have hsmallf : (compOf F₁ small ∩ RF'.R).Nonempty := ⟨small, Finset.mem_inter.mpr ⟨self_mem_compOf (hV₀.symm ▸ hRF'.2.2.1 hsmallR), hsmallR⟩⟩
        obtain ⟨_, hminBig, holdBig⟩ := hU.hRootMeta big hbigR hbigAct hbigPar
        obtain ⟨_, hminSm, holdSm⟩ := hU.hRootMeta small hsmallR hsmallAct hsmallPar
        refine ⟨hsum_card, fun hPf => ?_, ?_⟩
        · rw [hminBig hbigf, hminSm hsmallf]
          have hset : compOf F₀ big ∩ RF'.R = (compOf F₁ big ∩ RF'.R) ∪ (compOf F₁ small ∩ RF'.R) := by
            rw [hcompF0_big, ← hcomp_union, Finset.union_inter_distrib_right]
          apply le_antisymm
          · have hm := Finset.min'_mem _ hPf
            have hm' : (compOf F₀ big ∩ RF'.R).min' hPf ∈ (compOf F₁ big ∩ RF'.R) ∪ (compOf F₁ small ∩ RF'.R) :=
              hset ▸ hm
            rcases Finset.mem_union.mp hm' with h1 | h2
            · exact le_trans (min_le_left _ _) (Finset.min'_le _ _ h1)
            · exact le_trans (min_le_right _ _) (Finset.min'_le _ _ h2)
          · refine le_min ?_ ?_
            · exact Finset.min'_le _ _ (hset ▸ Finset.mem_union_left _ (Finset.min'_mem _ hbigf))
            · exact Finset.min'_le _ _ (hset ▸ Finset.mem_union_right _ (Finset.min'_mem _ hsmallf))
        · rw [holdBig, holdSm]
          have hset : compOf F₀ big ∩ R_old = (compOf F₁ big ∩ R_old) ∪ (compOf F₁ small ∩ R_old) := by
            rw [hcompF0_big, ← hcomp_union, Finset.union_inter_distrib_right]
          by_cases hbo : (compOf F₁ big ∩ R_old).Nonempty
          · have hPo : (compOf F₀ big ∩ R_old).Nonempty := by
              obtain ⟨z, hz⟩ := hbo; exact ⟨z, hset ▸ Finset.mem_union_left _ hz⟩
            have hmin_eq : (compOf F₀ big ∩ R_old).min' hPo = (compOf F₁ big ∩ R_old).min' hbo := by
              have h1 := Finset.mem_inter.mp (Finset.min'_mem _ hPo)
              have h2 := Finset.mem_inter.mp (Finset.min'_mem _ hbo)
              have h2' : (compOf F₁ big ∩ R_old).min' hbo ∈ compOf F₀ big :=
                (Finset.mem_inter.mp (hset ▸ Finset.mem_union_left _ (Finset.min'_mem _ hbo))).1
              exact hSep₀ _ h1.2 _ h2.2 (connected_trans (connected_symm (mem_compOf_iff.mp h1.1).2) (mem_compOf_iff.mp h2').2)
            dsimp only [F₁] at hbo hmin_eq
            simp [hbo, hPo, hmin_eq]
          · by_cases hso : (compOf F₁ small ∩ R_old).Nonempty
            · have hPo : (compOf F₀ big ∩ R_old).Nonempty := by
                obtain ⟨z, hz⟩ := hso; exact ⟨z, hset ▸ Finset.mem_union_right _ hz⟩
              have hmin_eq : (compOf F₀ big ∩ R_old).min' hPo = (compOf F₁ small ∩ R_old).min' hso := by
                have h1 := Finset.mem_inter.mp (Finset.min'_mem _ hPo)
                have h2 := Finset.mem_inter.mp (Finset.min'_mem _ hso)
                have h2' : (compOf F₁ small ∩ R_old).min' hso ∈ compOf F₀ big :=
                  (Finset.mem_inter.mp (hset ▸ Finset.mem_union_right _ (Finset.min'_mem _ hso))).1
                exact hSep₀ _ h1.2 _ h2.2 (connected_trans (connected_symm (mem_compOf_iff.mp h1.1).2) (mem_compOf_iff.mp h2').2)
              dsimp only [F₁] at hbo hso hmin_eq
              simp only [hbo, hso, hPo, ↓reduceDIte, ne_eq, not_true_eq_false, ↓reduceIte, hmin_eq]
            · have hPo : ¬ (compOf F₀ big ∩ R_old).Nonempty := by
                rintro ⟨z, hz⟩; rw [hset, Finset.mem_union] at hz
                rcases hz with h1 | h2
                · exact hbo ⟨z, h1⟩
                · exact hso ⟨z, h2⟩
              dsimp only [F₁] at hbo hso
              simp only [hbo, hso, hPo, ↓reduceDIte, ne_eq, not_true_eq_false, ↓reduceIte]
      · have hrs : r ≠ small := fun h => by subst r; rw [Function.update_self] at hpar; exact hbig_ne_small hpar
        rw [Function.update_of_ne hrs] at hpar
        simp only [Function.update_of_ne hrb'] at hact ⊢
        have hr_notAB : r ∉ A ∪ B := fun hrAB => by
          rcases Finset.mem_union.mp hrAB with hrA | hrB
          · have heq := hU.hRootUnique r hr ra hraR hact hpar hraAct hraPar (connected_trans (connected_symm (mem_compOf_iff.mp hrA).2) ha_ra)
            rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hrb' heq
            · exact hrs heq
          · have heq := hU.hRootUnique r hr rb hrbR hact hpar hrbAct hrbPar (connected_trans (connected_symm (mem_compOf_iff.mp hrB).2) hb_rb)
            rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hrs heq
            · exact hrb' heq
        rw [hOther r (hV₀.symm ▸ hRF'.2.2.1 hr) hr_notAB]
        exact hU.hRootMeta r hr hact hpar
    · intro r₁ hr₁ r₂ hr₂ ha₁ hp₁ ha₂ hp₂ hconn; dsimp only at ha₁ hp₁ ha₂ hp₂
      have hne_s : ∀ r, r ∈ RF'.R → Function.update U.par small big r = r → r ≠ small := fun r _ hp hs => by
        subst r; rw [Function.update_self] at hp; exact hbig_ne_small hp
      have hs1 := hne_s r₁ hr₁ hp₁; have hs2 := hne_s r₂ hr₂ hp₂
      rw [Function.update_of_ne hs1] at hp₁; rw [Function.update_of_ne hs2] at hp₂
      have ha1' : 1 ≤ U.sz r₁ := by
        by_cases h : r₁ = big
        · exact h ▸ hbigAct
        · rwa [Function.update_of_ne h] at ha₁
      have ha2' : 1 ≤ U.sz r₂ := by
        by_cases h : r₂ = big
        · exact h ▸ hbigAct
        · rwa [Function.update_of_ne h] at ha₂
      have hmem_AB : ∀ r, r ∈ RF'.R → 1 ≤ U.sz r → U.par r = r → r ≠ small → r ∈ A ∪ B → r = big := fun r hr ha hp hs hrAB => by
        rcases Finset.mem_union.mp hrAB with hrA | hrB
        · have heq := hU.hRootUnique r hr ra hraR ha hp hraAct hraPar (connected_trans (connected_symm (mem_compOf_iff.mp hrA).2) ha_ra)
          rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact heq
          · exact absurd heq hs
        · have heq := hU.hRootUnique r hr rb hrbR ha hp hrbAct hrbPar (connected_trans (connected_symm (mem_compOf_iff.mp hrB).2) hb_rb)
          rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact absurd heq hs
          · exact heq
      by_cases h1 : r₁ ∈ A ∪ B
      · have hb1 := hmem_AB r₁ hr₁ ha1' hp₁ hs1 h1
        have h2 : r₂ ∈ A ∪ B := by
          rw [← hcompF0_big, ← hb1]; exact mem_compOf_iff.mpr ⟨hV₀.symm ▸ hRF'.2.2.1 hr₂, hconn⟩
        exact hb1.trans (hmem_AB r₂ hr₂ ha2' hp₂ hs2 h2).symm
      · have hcomp1 : compOf F₀ r₁ = compOf F₁ r₁ := hOther r₁ (hV₀.symm ▸ hRF'.2.2.1 hr₁) h1
        have hr2_in : r₂ ∈ compOf F₁ r₁ := by
          rw [← hcomp1]; exact mem_compOf_iff.mpr ⟨hV₀.symm ▸ hRF'.2.2.1 hr₂, hconn⟩
        exact hU.hRootUnique r₁ hr₁ r₂ hr₂ ha1' hp₁ ha2' hp₂ (mem_compOf_iff.mp hr2_in).2
  refine ⟨hne, hpair_eq, ?_⟩
  by_cases hge : U.sz ra ≥ U.sz rb
  · simp only [ufUnion, hge, ↓reduceIte]
    exact hunion_symm ra rb (Or.inl ⟨rfl, rfl⟩) hge
  · simp only [ufUnion, hge, ↓reduceIte]
    exact hunion_symm rb ra (Or.inr ⟨rfl, rfl⟩) (by omega)

/-! ## 4. Input-split and release-list bridge to `canonStepSplits` -/

/-- `canonRoots F₀ R_old final = R_old` whenever `⟨F₀, R_old⟩` is already a rooted spanning forest. -/
lemma canonRoots_self_of_rsf {G : MGraph} {RF₀ : RootedForest} {final : Finset ℕ}
    (hRF₀ : RF₀.IsRootedSpanningForestOf G) :
    canonRoots RF₀.F RF₀.R final = RF₀.R := by
  ext r
  simp only [canonRoots, Finset.mem_image]
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨v, hvF, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨rt, ⟨hrt, hc⟩, _⟩ := hRF₀.2.2.2.1 v (hRF₀.2.1 ▸ hvF)
    have ho : (compOf RF₀.F v ∩ RF₀.R).Nonempty :=
      ⟨rt, Finset.mem_inter.mpr ⟨mem_compOf_iff.mpr ⟨hRF₀.2.1.symm ▸ hRF₀.2.2.1 hrt, hc⟩, hrt⟩⟩
    simp only [canonPick, ho, ↓reduceDIte]
    exact (Finset.mem_inter.mp (Finset.min'_mem _ ho)).2
  · intro hr
    have hrF : r ∈ RF₀.F.V := hRF₀.2.1.symm ▸ hRF₀.2.2.1 hr
    refine ⟨compOf RF₀.F r, compOf_mem_components hrF, ?_⟩
    have ho : (compOf RF₀.F r ∩ RF₀.R).Nonempty :=
      ⟨r, Finset.mem_inter.mpr ⟨self_mem_compOf hrF, hr⟩⟩
    simp only [canonPick, ho, ↓reduceDIte]
    have hm := Finset.mem_inter.mp (Finset.min'_mem _ ho)
    have h1 := root_eq_of_mem_R hRF₀ hm.2
    have h2 := root_eq_of_mem_R hRF₀ hr
    exact h1.symm.trans ((root_eq_of_connected hRF₀ (hRF₀.2.2.1 hm.2) (hRF₀.2.2.1 hr)
      (connected_symm (mem_compOf_iff.mp hm.1).2)).trans h2)

/-- Input-split query for `.delete e` (`e ∈ RF₀.F.E`) at `F_mid = eraseForestEdge RF₀.F e`:
`ufPair U ra rb` equals `(RF₀.root (RF₀.F.tail e), newRoot (canonRoots F_mid RF₀.R RF'.R) RF₀.R)`. -/
theorem revUFInv_input_delete {G : MGraph} {RF₀ RF' : RootedForest} {U : RevUFState} {e ra rb : ℕ}
    (hRF₀ : RF₀.IsRootedSpanningForestOf G)
    (hRF' : RF'.IsRootedSpanningForestOf (G.applyUpdate (.delete e)))
    (he : e ∈ RF₀.F.E) (hFsub : (eraseForestEdge RF₀.F e).IsSubgraph RF'.F)
    (hOld : RF₀.R ⊆ RF'.R)
    (hU : RevUFInv (eraseForestEdge RF₀.F e) RF' RF₀.R U)
    (hraR : ra ∈ RF'.R) (hraAct : 1 ≤ U.sz ra) (hraPar : U.par ra = ra)
    (hraConn : (eraseForestEdge RF₀.F e).Connected (RF'.root (RF₀.F.tail e)) ra)
    (hrbR : rb ∈ RF'.R) (hrbAct : 1 ≤ U.sz rb) (hrbPar : U.par rb = rb)
    (hrbConn : (eraseForestEdge RF₀.F e).Connected (RF'.root (RF₀.F.head e)) rb) :
    ufPair U ra rb =
      (RF₀.root (RF₀.F.tail e), newRoot (canonRoots (eraseForestEdge RF₀.F e) RF₀.R RF'.R) RF₀.R) := by
  have hSep₀ : ∀ r ∈ RF₀.R, ∀ s ∈ RF₀.R, RF₀.F.Connected r s → r = s := fun r hr s hs hc =>
    (root_eq_of_mem_R hRF₀ hr).symm.trans
      ((root_eq_of_connected hRF₀ (hRF₀.2.2.1 hr) (hRF₀.2.2.1 hs) hc).trans (root_eq_of_mem_R hRF₀ hs))
  have hRF'G : RF'.IsRootedSpanningForestOf G := by
    refine ⟨hRF'.1, hRF'.2.1, hRF'.2.2.1, hRF'.2.2.2.1, hRF'.2.2.2.2.1,
      fun f hf => Finset.mem_of_mem_erase (hRF'.2.2.2.2.2.1 hf), hRF'.2.2.2.2.2.2⟩
  have hpair := (revUFInv_union_edge hRF₀.1 hRF₀.2.1 hRF₀.2.2.2.2 he hFsub hRF'G hOld hSep₀ hU
    hraR hraAct hraPar hraConn hrbR hrbAct hrbPar hrbConn).2.1
  have hself : canonRoots RF₀.F RF₀.R RF'.R = RF₀.R := canonRoots_self_of_rsf hRF₀
  rw [hself] at hpair
  exact hpair

/-- Input-split query for `.split v v' At Ah` at `F_mid = RF₀.F.applyUpdate (.split v v' At Ah)`:
`ufPair U ra rb` equals `(RF₀.root v, newRoot (canonRoots F_mid RF₀.R RF'.R) RF₀.R)`. -/
theorem revUFInv_input_split {G : MGraph} {RF₀ RF' : RootedForest} {U : RevUFState}
    {v v' ra rb : ℕ} {At Ah : Finset ℕ}
    (hRF₀ : RF₀.IsRootedSpanningForestOf G)
    (hv : v ∈ G.V) (hv' : v' ∉ G.V)
    (hRF' : RF'.IsRootedSpanningForestOf (G.applyUpdate (.split v v' At Ah)))
    (hFsub : (RF₀.F.applyUpdate (.split v v' At Ah)).IsSubgraph RF'.F)
    (hOld : RF₀.R ⊆ RF'.R)
    (hU : RevUFInv (RF₀.F.applyUpdate (.split v v' At Ah)) RF' RF₀.R U)
    (hraR : ra ∈ RF'.R) (hraAct : 1 ≤ U.sz ra) (hraPar : U.par ra = ra)
    (hraConn : (RF₀.F.applyUpdate (.split v v' At Ah)).Connected (RF'.root v) ra)
    (hrbR : rb ∈ RF'.R) (hrbAct : 1 ≤ U.sz rb) (hrbPar : U.par rb = rb)
    (hrbConn : (RF₀.F.applyUpdate (.split v v' At Ah)).Connected (RF'.root v') rb) :
    ufPair U ra rb =
      (RF₀.root v,
        newRoot (canonRoots (RF₀.F.applyUpdate (.split v v' At Ah)) RF₀.R RF'.R) RF₀.R) := by
  classical
  set F₁ := RF₀.F.applyUpdate (.split v v' At Ah)
  set G' := G.applyUpdate (.split v v' At Ah)
  have hvF : v ∈ RF₀.F.V := hRF₀.2.1.symm ▸ hv
  have hv'F : v' ∉ RF₀.F.V := fun h => hv' (hRF₀.2.1 ▸ h)
  have hvG' : v ∈ G'.V := Finset.mem_insert_of_mem hv
  have hv'G' : v' ∈ G'.V := Finset.mem_insert_self _ _
  have hF₁V : F₁.V = G'.V := by
    change insert v' RF₀.F.V = insert v' G.V; rw [hRF₀.2.1]
  have hv_ra : F₁.Connected v ra :=
    connected_trans (connected_of_subgraph hFsub (root_mem_R hRF' hvG').2) hraConn
  have hv'_rb : F₁.Connected v' rb :=
    connected_trans (connected_of_subgraph hFsub (root_mem_R hRF' hv'G').2) hrbConn
  set A := compOf F₁ v; set B := compOf F₁ v'
  have hA_eq : compOf F₁ ra = A := compOf_eq_of_connected (connected_symm hv_ra)
  have hB_eq : compOf F₁ rb = B := compOf_eq_of_connected (connected_symm hv'_rb)
  obtain ⟨hDisj, hMemIff, hOther⟩ := applySplit_compOf_split hRF₀.1 hvF hv'F At Ah
  have hra_in_A : ra ∈ A := mem_compOf_iff.mpr ⟨hF₁V.symm ▸ hRF'.2.2.1 hraR, hv_ra⟩
  have hrb_in_B : rb ∈ B := mem_compOf_iff.mpr ⟨hF₁V.symm ▸ hRF'.2.2.1 hrbR, hv'_rb⟩
  have hAf : (A ∩ RF'.R).Nonempty := ⟨ra, Finset.mem_inter.mpr ⟨hra_in_A, hraR⟩⟩
  have hBf : (B ∩ RF'.R).Nonempty := ⟨rb, Finset.mem_inter.mpr ⟨hrb_in_B, hrbR⟩⟩
  have hAtMostOne : ∀ r ∈ (A ∪ B) ∩ RF₀.R, ∀ s ∈ (A ∪ B) ∩ RF₀.R, r = s := fun r hr s hs => by
    have hrO := (Finset.mem_inter.mp hr).2; have hsO := (Finset.mem_inter.mp hs).2
    have hrC := (hMemIff r (hRF₀.2.1.symm ▸ hRF₀.2.2.1 hrO)).mp (Finset.mem_inter.mp hr).1
    have hsC := (hMemIff s (hRF₀.2.1.symm ▸ hRF₀.2.2.1 hsO)).mp (Finset.mem_inter.mp hs).1
    have hconn : RF₀.F.Connected r s :=
      connected_trans (connected_symm (mem_compOf_iff.mp hrC).2) (mem_compOf_iff.mp hsC).2
    exact (root_eq_of_mem_R hRF₀ hrO).symm.trans
      ((root_eq_of_connected hRF₀ (hRF₀.2.2.1 hrO) (hRF₀.2.2.1 hsO) hconn).trans (root_eq_of_mem_R hRF₀ hsO))
  obtain ⟨_, hminA, holdA⟩ := hU.hRootMeta ra hraR hraAct hraPar
  obtain ⟨_, hminB, holdB⟩ := hU.hRootMeta rb hrbR hrbAct hrbPar
  rw [hA_eq] at hminA holdA; rw [hB_eq] at hminB holdB
  have hpair_msp : ufPair U ra rb = (canonPick RF₀.R RF'.R (A ∪ B),
      if canonPick RF₀.R RF'.R A = canonPick RF₀.R RF'.R (A ∪ B) then
        canonPick RF₀.R RF'.R B else canonPick RF₀.R RF'.R A) := by
    have hmsp := mergeSplitPair_eq_canon hDisj hAf hBf hOld hAtMostOne
    dsimp only at hmsp
    rw [← hmsp]; dsimp only [ufPair]
    rw [hminA hAf, hminB hBf, holdA, holdB]
    have hopt : ∀ (S : Finset ℕ),
        (if (if h : S.Nonempty then S.min' h + 1 else 0) = 0 then none
         else some ((if h : S.Nonempty then S.min' h + 1 else 0) - 1)) =
        (if h : S.Nonempty then some (S.min' h) else none) := fun S => by
      by_cases h : S.Nonempty <;> simp [h]
    rw [hopt (A ∩ RF₀.R), hopt (B ∩ RF₀.R)]
  rw [hpair_msp]
  set r0 := RF₀.root v
  have hr0_R : r0 ∈ RF₀.R := (root_mem_R hRF₀ hv).1
  have hr0_AB : r0 ∈ A ∪ B :=
    (hMemIff r0 (hRF₀.2.1.symm ▸ hRF₀.2.2.1 hr0_R)).mpr
      (mem_compOf_iff.mpr ⟨hRF₀.2.1.symm ▸ hRF₀.2.2.1 hr0_R, (root_mem_R hRF₀ hv).2⟩)
  have hPo : ((A ∪ B) ∩ RF₀.R).Nonempty := ⟨r0, Finset.mem_inter.mpr ⟨hr0_AB, hr0_R⟩⟩
  have hpP_eq : canonPick RF₀.R RF'.R (A ∪ B) = r0 := by
    simp only [canonPick, hPo, ↓reduceDIte]
    exact hAtMostOne _ (Finset.min'_mem _ hPo) r0 (Finset.mem_inter.mpr ⟨hr0_AB, hr0_R⟩)
  rw [hpP_eq]
  set pA := canonPick RF₀.R RF'.R A
  set pB := canonPick RF₀.R RF'.R B
  set fresh := if pA = r0 then pB else pA
  have hr0_split : (pA = r0 ∧ fresh = pB ∧ pB ∈ B ∧ pB ∉ RF₀.R) ∨
      (pB = r0 ∧ fresh = pA ∧ pA ∈ A ∧ pA ∉ RF₀.R) := by
    rcases Finset.mem_union.mp hr0_AB with hrA | hrB
    · left
      have hAo : (A ∩ RF₀.R).Nonempty := ⟨r0, Finset.mem_inter.mpr ⟨hrA, hr0_R⟩⟩
      have hBo : ¬ (B ∩ RF₀.R).Nonempty := fun ⟨s, hs⟩ => by
        have h1 := hAtMostOne r0 (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hrA, hr0_R⟩)
          s (Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_inter.mp hs).1, (Finset.mem_inter.mp hs).2⟩)
        exact Finset.disjoint_left.mp hDisj hrA (h1 ▸ (Finset.mem_inter.mp hs).1)
      have hpA : pA = r0 := by
        simp only [pA, canonPick, hAo, ↓reduceDIte]
        have hm := Finset.mem_inter.mp (Finset.min'_mem _ hAo)
        exact hAtMostOne _ (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hm.1, hm.2⟩) r0
          (Finset.mem_inter.mpr ⟨hr0_AB, hr0_R⟩)
      have hpB_in : pB ∈ B := by
        simp only [pB, canonPick, hBo, hBf, ↓reduceDIte]
        exact (Finset.mem_inter.mp (Finset.min'_mem _ hBf)).1
      exact ⟨hpA, by simp [fresh, hpA], hpB_in, fun h => hBo ⟨pB, Finset.mem_inter.mpr ⟨hpB_in, h⟩⟩⟩
    · right
      have hBo : (B ∩ RF₀.R).Nonempty := ⟨r0, Finset.mem_inter.mpr ⟨hrB, hr0_R⟩⟩
      have hAo : ¬ (A ∩ RF₀.R).Nonempty := fun ⟨s, hs⟩ => by
        have h1 := hAtMostOne r0 (Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hrB, hr0_R⟩)
          s (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hs).1, (Finset.mem_inter.mp hs).2⟩)
        exact Finset.disjoint_left.mp hDisj (h1 ▸ (Finset.mem_inter.mp hs).1) hrB
      have hpB : pB = r0 := by
        simp only [pB, canonPick, hBo, ↓reduceDIte]
        have hm := Finset.mem_inter.mp (Finset.min'_mem _ hBo)
        exact hAtMostOne _ (Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hm.1, hm.2⟩) r0
          (Finset.mem_inter.mpr ⟨hr0_AB, hr0_R⟩)
      have hpA_in : pA ∈ A := by
        simp only [pA, canonPick, hAo, hAf, ↓reduceDIte]
        exact (Finset.mem_inter.mp (Finset.min'_mem _ hAf)).1
      have hpA_ne : pA ≠ r0 := fun h => Finset.disjoint_left.mp hDisj hpA_in (h ▸ hrB)
      exact ⟨hpB, by simp [fresh, hpA_ne], hpA_in, fun h => hAo ⟨pA, Finset.mem_inter.mpr ⟨hpA_in, h⟩⟩⟩
  have hfresh_not_R₀ : fresh ∉ RF₀.R := by
    rcases hr0_split with ⟨_, hf, _, hn⟩ | ⟨_, hf, _, hn⟩ <;> exact hf ▸ hn
  have hR₁_ins : canonRoots F₁ RF₀.R RF'.R = insert fresh RF₀.R := by
    have hself := canonRoots_self_of_rsf (final := RF'.R) hRF₀
    ext r
    simp only [canonRoots, Finset.mem_image, Finset.mem_insert]
    constructor
    · rintro ⟨C, hC, rfl⟩
      obtain ⟨x, hxF₁, rfl⟩ := Finset.mem_image.mp hC
      by_cases hxAB : x ∈ A ∪ B
      · rcases Finset.mem_union.mp hxAB with hxA | hxB
        · have hce : compOf F₁ x = A := compOf_eq_of_connected (connected_symm (mem_compOf_iff.mp hxA).2)
          rw [hce]
          rcases hr0_split with ⟨hA0, _, _, _⟩ | ⟨_, hf, _, _⟩
          · right; change pA ∈ RF₀.R; rw [hA0]; exact hr0_R
          · left; exact hf.symm
        · have hce : compOf F₁ x = B := compOf_eq_of_connected (connected_symm (mem_compOf_iff.mp hxB).2)
          rw [hce]
          rcases hr0_split with ⟨_, hf, _, _⟩ | ⟨hB0, _, _, _⟩
          · left; exact hf.symm
          · right; change pB ∈ RF₀.R; rw [hB0]; exact hr0_R
      · have hxv' : x ≠ v' := fun h => hxAB (Finset.mem_union_right _ (h ▸ self_mem_compOf (hF₁V.symm ▸ hv'G')))
        have hxF₀ : x ∈ RF₀.F.V := by
          have : x ∈ insert v' RF₀.F.V := hxF₁
          exact (Finset.mem_insert.mp this).resolve_left hxv'
        right; rw [← hOther x hxF₀ hxAB]
        have hmem : canonPick RF₀.R RF'.R (compOf RF₀.F x) ∈ canonRoots RF₀.F RF₀.R RF'.R :=
          Finset.mem_image_of_mem _ (compOf_mem_components hxF₀)
        rwa [hself] at hmem
    · rintro (rfl | hrR₀)
      · rcases hr0_split with ⟨_, hf, _, _⟩ | ⟨_, hf, _, _⟩
        · exact ⟨B, compOf_mem_components (hF₁V.symm ▸ hv'G'), hf.symm⟩
        · exact ⟨A, compOf_mem_components (hF₁V.symm ▸ hvG'), hf.symm⟩
      · have hrF₀ : r ∈ RF₀.F.V := hRF₀.2.1.symm ▸ hRF₀.2.2.1 hrR₀
        by_cases hrAB : r ∈ A ∪ B
        · have hreq : r = r0 := hAtMostOne r (Finset.mem_inter.mpr ⟨hrAB, hrR₀⟩) r0 (Finset.mem_inter.mpr ⟨hr0_AB, hr0_R⟩)
          subst hreq
          rcases hr0_split with ⟨hA0, _, _, _⟩ | ⟨hB0, _, _, _⟩
          · exact ⟨A, compOf_mem_components (hF₁V.symm ▸ hvG'), hA0⟩
          · exact ⟨B, compOf_mem_components (hF₁V.symm ▸ hv'G'), hB0⟩
        · have hrC : canonPick RF₀.R RF'.R (compOf RF₀.F r) = r := by
            have ho : (compOf RF₀.F r ∩ RF₀.R).Nonempty := ⟨r, Finset.mem_inter.mpr ⟨self_mem_compOf hrF₀, hrR₀⟩⟩
            simp only [canonPick, ho, ↓reduceDIte]
            have hm := Finset.mem_inter.mp (Finset.min'_mem _ ho)
            exact (root_eq_of_mem_R hRF₀ hm.2).symm.trans
              ((root_eq_of_connected hRF₀ (hRF₀.2.2.1 hm.2) (hRF₀.2.2.1 hrR₀)
                (connected_symm (mem_compOf_iff.mp hm.1).2)).trans (root_eq_of_mem_R hRF₀ hrR₀))
          exact ⟨compOf F₁ r, compOf_mem_components (by change r ∈ insert v' RF₀.F.V; exact Finset.mem_insert_of_mem hrF₀),
            by rw [← hOther r hrF₀ hrAB]; exact hrC⟩
  exact Prod.ext rfl (newRoot_eq hR₁_ins hfresh_not_R₀).symm

/-- Every `i`-th entry of `releasesSplitEntries final.R L₀ D` (where `L₀.F.R = canonRoots F_mid old final.R`
and `D` is a nodup list of edges in `F_mid.E \ final.F.E`) equals the canonical cut entry of `D[i]`
on `F_i = (D.take i).foldl eraseForestEdge F_mid` with root set `canonRoots F_i old final.R`. -/
theorem releasesSplitEntries_getElem {G F_mid : MGraph} {final : RootedForest} {old : Finset ℕ}
    {L₀ : LSF} {D : List ℕ}
    (hF_mid : F_mid.IsForest) (hV_mid : F_mid.V = G.V) (hF_midG : G.IsSubgraph F_mid)
    (hsub : F_mid.IsSubgraph final.F) (hfinal : final.IsRootedSpanningForestOf G)
    (hOld : old ⊆ final.R)
    (hSep : ∀ r ∈ old, ∀ s ∈ old, F_mid.Connected r s → r = s)
    (hL₀F : L₀.F.F = F_mid) (hL₀R : L₀.F.R = canonRoots F_mid old final.R)
    (hD_nd : D.Nodup) (hD_sub : ∀ e ∈ D, e ∈ F_mid.E ∧ e ∉ final.F.E) :
    ∀ i (hi : i < D.length),
      let F_i := (D.take i).foldl eraseForestEdge F_mid
      let F_i1 := eraseForestEdge F_i D[i]
      let R_i := canonRoots F_i old final.R
      let R_i1 := canonRoots F_i1 R_i final.R
      (releasesSplitEntries final.R L₀ D)[i]'(by rw [releasesSplitEntries_length]; exact hi) =
        ⟨true, D[i], (RootedForest.mk F_i R_i).root (F_i.tail D[i]), newRoot R_i1 R_i⟩ := by
  induction D generalizing F_mid L₀ with
  | nil => intro i hi; simp at hi
  | cons e rest ih =>
    intro i hi
    have he_mid : e ∈ F_mid.E := (hD_sub e (List.mem_cons_self ..)).1
    have he_not_fin : e ∉ final.F.E := (hD_sub e (List.mem_cons_self ..)).2
    have hK : (eraseForestEdge F_mid e).IsForest := isForest_eraseEdge hF_mid e
    have hsub01 : F_mid.IsSubgraph (eraseForestEdge F_mid e) := eraseForestEdge_subgraph F_mid e
    have hKG : G.IsSubgraph (eraseForestEdge F_mid e) :=
      ⟨hsub01.1.trans hF_midG.1, hsub01.2.1.trans hF_midG.2.1, fun f hf =>
        ⟨(hsub01.2.2 f hf).1.trans (hF_midG.2.2 f (hsub01.2.1 hf)).1,
         (hsub01.2.2 f hf).2.trans (hF_midG.2.2 f (hsub01.2.1 hf)).2⟩⟩
    have hKsub : (eraseForestEdge F_mid e).IsSubgraph final.F :=
      ⟨hsub.1, fun f hf => Finset.mem_erase.mpr ⟨fun h => he_not_fin (h ▸ hf), hsub.2.1 hf⟩, hsub.2.2⟩
    have hKsep : ∀ r ∈ old, ∀ s ∈ old, (eraseForestEdge F_mid e).Connected r s → r = s :=
      fun r hr s hs hc => hSep r hr s hs (connected_of_subgraph hsub01 hc)
    have hR1_eq : canonRoots (eraseForestEdge F_mid e) L₀.F.R final.R =
        canonRoots (eraseForestEdge F_mid e) old final.R := by
      rw [hL₀R]
      exact canonRoots_idem_of_subgraph hF_mid hV_mid hF_midG hK hV_mid hKG hsub01 hKsub hfinal hOld hSep
    cases i with
    | zero =>
      simp only [releasesSplitEntries, List.getElem_cons_zero, List.take_zero, List.foldl_nil]
      have hLF : L₀.F = RootedForest.mk F_mid (canonRoots F_mid old final.R) := by
        cases h : L₀.F; simp only [h] at hL₀F hL₀R; subst hL₀F hL₀R; rfl
      simp only [hLF]
    | succ i =>
      rw [List.nodup_cons] at hD_nd
      simp only [releasesSplitEntries, List.getElem_cons_succ, List.take_succ_cons, List.foldl_cons]
      have hrest_sub : ∀ f ∈ rest, f ∈ (eraseForestEdge F_mid e).E ∧ f ∉ final.F.E := fun f hf =>
        ⟨Finset.mem_erase.mpr ⟨fun hfe => hD_nd.1 (hfe ▸ hf), (hD_sub f (List.mem_cons_of_mem _ hf)).1⟩,
         (hD_sub f (List.mem_cons_of_mem _ hf)).2⟩
      have hih := ih (L₀ := ⟨L₀.T, ⟨eraseForestEdge F_mid e, canonRoots (eraseForestEdge F_mid e) L₀.F.R final.R⟩, L₀.wstr⟩)
        hK hV_mid hKG hKsub hKsep rfl hR1_eq hD_nd.2 hrest_sub i (Nat.lt_of_succ_lt_succ hi)
      have hL1 : (⟨L₀.T, ⟨eraseForestEdge L₀.F.F e, canonRoots (eraseForestEdge L₀.F.F e) L₀.F.R final.R⟩, L₀.wstr⟩ : LSF) =
          ⟨L₀.T, ⟨eraseForestEdge F_mid e, canonRoots (eraseForestEdge F_mid e) L₀.F.R final.R⟩, L₀.wstr⟩ := by
        rw [hL₀F]
      have hget : (releasesSplitEntries final.R
          ⟨L₀.T, ⟨eraseForestEdge L₀.F.F e, canonRoots (eraseForestEdge L₀.F.F e) L₀.F.R final.R⟩, L₀.wstr⟩ rest)[i]'(by
            rw [releasesSplitEntries_length]; exact Nat.lt_of_succ_lt_succ hi) =
          (releasesSplitEntries final.R
          ⟨L₀.T, ⟨eraseForestEdge F_mid e, canonRoots (eraseForestEdge F_mid e) L₀.F.R final.R⟩, L₀.wstr⟩ rest)[i]'(by
            rw [releasesSplitEntries_length]; exact Nat.lt_of_succ_lt_succ hi) := by
        simp only [hL1]
      exact hget.trans hih

end

end MinCostFlow.SparseCore.Program



