module

public import WordRAM.Contract
public import MinCostFlow.ExpanderDecomp.OneShotProgLayout
public import MinCostFlow.ExpanderDecomp.OneShotProgStepD
public import MinCostFlow.ExpanderDecomp.ProgCloud
import Mathlib.Tactic.Linarith

/-!
# Standalone Procedure Contract for `OneShot` Step B and Space Base

States the Word-RAM `Contract` specification for Step B of `OneShot` (`oneShotStepBContract`),
together with its non-vacuity witness (`oneShotStepBContract_pre_example`) and the uniform
graph-size space factor `coreSpaceBase M r` shared across `OneShot` and `Core`:

* `coreSpaceBase M r := (2048 * LParam M * (NOf M r) ^ r + 3) ^ 5`: constant across recursion
  levels `q ≤ r`, upper-bounding both `(G.n + 3) ^ 4` (for `ProgStepCSpec.stepCSpace` and
  `stepCLeftoverSpace`), `(e + 3) ^ 5` (for `outerPortGraphSpace`), and `cloudExpanderSpace`.
* `oneShotStepBContract`: block cut-matching game and complement injection (`OneShotStepB.lean`)
  for `2 ≤ q ≤ r`, parameterized by the recursive `coreOn` time/space budgets `(Tprev, Sprev)` at
  level `q - 1`.
* `stepCTimeConst` and `stepCSpaceConst`: fixed constant factors absorbing `stepCContract`,
  `stepCLeftoverContract`, `cloudExpanderContract`, and `edgeColor17Contract` into the universal
  `OneShot` and `Core` envelopes.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Space Base and Step B / Step C Envelopes -/

/-- Level-independent polynomial space base `(2048 * L * N ^ r + 3) ^ 5` covering `(G.n + 3) ^ 4`,
`cloudExpanderSpace`, and `outerPortGraphSpace` at every recursion level `q ≤ r`. -/
def coreSpaceBase (M r : ℕ) : ℕ :=
  (2048 * LParam M * (NOf M r) ^ r + 3) ^ 5

/-- Heap advance bound for `OneShot` Step B at level `q`, given per-call space `Sprev` for
`coreOn` at level `q - 1`. -/
def oneShotStepBSpace (S_B M r q Sprev : ℕ) : ℕ :=
  100 * NOf M r * LParam M * Sprev +
    S_B * coreSpaceBase M r * (NOf M r) ^ (q + 1) * (LParam M) ^ 8

/-- Step-count bound for `OneShot` Step B at level `q`, given per-call cost `Tprev` for `coreOn`
at level `q - 1`. -/
def oneShotStepBCost (K_B N L q Tprev : ℕ) : ℕ :=
  100 * N * L * Tprev + K_B * N ^ (q + 1) * L ^ 8

/-- Constant coefficient for one `routerCallCost` call at `C_route = 80`, matching `CoreCost.lean`. -/
def stepCRouterConst : ℕ :=
  240 * 1024 * ParamConfig.d0 * ParamConfig.R0

/-- Constant factor absorbing `stepCContract`, `stepCLeftoverContract`, `cloudExpanderContract`,
and `edgeColor17Contract` step counts into `K_C * N ^ (q + 1) * L ^ 8`. -/
def stepCTimeConst (C_stepC C_left : ℕ) : ℕ :=
  (C_stepC + C_left + 1) * (20 * stepCRouterConst + 10000) + cloudExpanderCost 1

/-- Constant factor absorbing `stepCSpace`, `stepCLeftoverSpace`, `cloudExpanderSpace`, and
Step C scratch buffers into `S_C * coreSpaceBase M r * N ^ (q + 1) * L ^ 8`. -/
def stepCSpaceConst (C_sp : ℕ) : ℕ :=
  (C_sp + 1) * (20 * stepCRouterConst + 10000)

/-! ## 2. Step B Contract (`oneShotStepBContract`) -/

/-- Standalone Word-RAM contract for Step B of `OneShot` (`2 ≤ q ≤ r`).
`args = [q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, fAddr, outAddr, h]`.
On a router cut, writes `CoreOutAt mem' outAddr (.cut U)` with `RouteCutSpec G X 100 z U`.
Otherwise sets `mem' outAddr = 1`, `mem' (outAddr + 1) = |F_B|`, writes `EdgesAt mem' fAddr F_B`
for `F_B = callsFakeEdges callsB` (`callsB.length ≤ 49 * L + 2`, every block expanding by
`1 / (2 * P (q - 1))`), restores `locAddr`, preserves memory below `h` outside `fAddr` and
`outAddr`, and returns `h' ∈ [h, h + oneShotStepBSpace]` with `ZeroFrom mem' h'`. -/
noncomputable def oneShotStepBContract (cfg : ParamConfig) (M r q w K_B S_B Tprev Sprev : ℕ) :
    Contract where
  pre args mem :=
    let cp := coreParamsOf cfg M r
    ∃ (gAddr k xAddr b nBlocks z pAddr locAddr fAddr outAddr h : ℕ)
      (G : Graph) (X : Finset ℕ),
      args = [q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, fAddr, outAddr, h] ∧
      4 ≤ cfg.a ∧ r ≤ ell M ∧ 2 ≤ q ∧ q ≤ r ∧
      CoreParamsAt mem pAddr cp r ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      G.n ≤ 2048 * LParam M * (NOf M r) ^ r ∧
      VertsAt mem xAddr k X ∧
      X ⊆ Finset.range G.n ∧
      (∀ e ∈ G.inside X, e.1 ≠ e.2) ∧
      (∀ v ∈ X, G.degIn X v ≤ cp.Δ) ∧
      G.m ≤ 2 * cp.Δ * k ∧
      cp.N ^ (q - 1) / 2 ≤ k ∧ k ≤ cp.N ^ q ∧
      b = cp.N ^ (q - 1) / 2 ∧
      nBlocks = numFullBlocks (X.sort (· ≤ ·)) b ∧
      z = k / cp.D q ∧
      (∀ u < G.n, mem (locAddr + u) = 0) ∧
      gAddr + 2 + 2 * G.m ≤ h ∧
      xAddr + k ≤ h ∧
      pAddr + coreParamsSize r ≤ h ∧
      locAddr + G.n ≤ h ∧
      fAddr + 2 * k ≤ h ∧
      outAddr + 2 + k ≤ h ∧
      DisjointRange locAddr G.n gAddr (2 + 2 * G.m) ∧
      DisjointRange locAddr G.n xAddr k ∧
      DisjointRange locAddr G.n pAddr (coreParamsSize r) ∧
      DisjointRange locAddr G.n fAddr (2 * k) ∧
      DisjointRange locAddr G.n outAddr (2 + k) ∧
      DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m) ∧
      DisjointRange outAddr (2 + k) xAddr k ∧
      DisjointRange outAddr (2 + k) pAddr (coreParamsSize r) ∧
      DisjointRange outAddr (2 + k) fAddr (2 * k) ∧
      DisjointRange fAddr (2 * k) gAddr (2 + 2 * G.m) ∧
      DisjointRange fAddr (2 * k) xAddr k ∧
      DisjointRange fAddr (2 * k) pAddr (coreParamsSize r) ∧
      ZeroFrom mem h ∧
      h + oneShotStepBSpace S_B M r q Sprev < 2 ^ w
  post args mem v mem' :=
    let cp := coreParamsOf cfg M r
    ∀ (gAddr k xAddr b nBlocks z pAddr locAddr fAddr outAddr h : ℕ)
      (G : Graph) (X : Finset ℕ),
      args = [q, gAddr, k, xAddr, b, nBlocks, z, pAddr, locAddr, fAddr, outAddr, h] →
      4 ≤ cfg.a → r ≤ ell M → 2 ≤ q → q ≤ r →
      CoreParamsAt mem pAddr cp r →
      GraphAt mem gAddr G →
      G.IsValid →
      G.n ≤ 2048 * LParam M * (NOf M r) ^ r →
      VertsAt mem xAddr k X →
      X ⊆ Finset.range G.n →
      (∀ e ∈ G.inside X, e.1 ≠ e.2) →
      (∀ v ∈ X, G.degIn X v ≤ cp.Δ) →
      G.m ≤ 2 * cp.Δ * k →
      cp.N ^ (q - 1) / 2 ≤ k → k ≤ cp.N ^ q →
      b = cp.N ^ (q - 1) / 2 →
      nBlocks = numFullBlocks (X.sort (· ≤ ·)) b →
      z = k / cp.D q →
      (∀ u < G.n, mem (locAddr + u) = 0) →
      gAddr + 2 + 2 * G.m ≤ h →
      xAddr + k ≤ h →
      pAddr + coreParamsSize r ≤ h →
      locAddr + G.n ≤ h →
      fAddr + 2 * k ≤ h →
      outAddr + 2 + k ≤ h →
      DisjointRange locAddr G.n gAddr (2 + 2 * G.m) →
      DisjointRange locAddr G.n xAddr k →
      DisjointRange locAddr G.n pAddr (coreParamsSize r) →
      DisjointRange locAddr G.n fAddr (2 * k) →
      DisjointRange locAddr G.n outAddr (2 + k) →
      DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m) →
      DisjointRange outAddr (2 + k) xAddr k →
      DisjointRange outAddr (2 + k) pAddr (coreParamsSize r) →
      DisjointRange outAddr (2 + k) fAddr (2 * k) →
      DisjointRange fAddr (2 * k) gAddr (2 + 2 * G.m) →
      DisjointRange fAddr (2 * k) xAddr k →
      DisjointRange fAddr (2 * k) pAddr (coreParamsSize r) →
      ZeroFrom mem h →
      h + oneShotStepBSpace S_B M r q Sprev < 2 ^ w →
      ((mem' outAddr = 0 ∧
          ∃ U : Finset ℕ, CoreOutAt mem' outAddr (.cut U) ∧ RouteCutSpec G X 100 z U) ∨
        (mem' outAddr = 1 ∧
          ∃ callsB : List RoutedCall,
            callsB.length ≤ 49 * cp.L + 2 ∧
            (∀ c ∈ callsB, c.Valid G X (routeCong cp.Δ 100 cp.L) z) ∧
            (∀ i < nBlocks, (Graph.mk G.n (callsWitnessEdges callsB)).IsExpansionExpanderOn
              (blockSet (X.sort (· ≤ ·)) b i) (1 / (2 * (cp.P (q - 1) : ℝ)))) ∧
            mem' (outAddr + 1) = (callsFakeEdges callsB).length ∧
            EdgesAt mem' fAddr (callsFakeEdges callsB))) ∧
      h ≤ v ∧ v ≤ h + oneShotStepBSpace S_B M r q Sprev ∧
      ZeroFrom mem' v ∧
      (∀ u < G.n, mem' (locAddr + u) = 0) ∧
      (∀ a < h, (a < fAddr ∨ fAddr + 2 * k ≤ a) → (a < outAddr ∨ outAddr + 2 + k ≤ a) →
        mem' a = mem a)
  cost _ _ := oneShotStepBCost K_B (NOf M r) (LParam M) q Tprev

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 3. Non-Vacuity Witness for `oneShotStepBContract` -/

private noncomputable def paramsMemAt (pAddr : ℕ) (cp : CoreParams) (r : ℕ) (a : ℕ) : ℕ :=
  if a = pAddr then cp.N
  else if a = pAddr + 1 then cp.L
  else if a = pAddr + 2 then cp.Δ
  else if a = pAddr + 3 then r
  else if pAddr + 4 ≤ a ∧ a ≤ pAddr + 4 + r then cp.P (a - (pAddr + 4))
  else if pAddr + 5 + r ≤ a ∧ a ≤ pAddr + 5 + 2 * r then cp.D (a - (pAddr + 5 + r))
  else if pAddr + 6 + 2 * r ≤ a ∧ a ≤ pAddr + 6 + 3 * r then cp.N ^ (a - (pAddr + 6 + 2 * r))
  else 0

private lemma coreParamsAt_paramsMemAt (pAddr : ℕ) (cp : CoreParams) (r : ℕ) :
    CoreParamsAt (paramsMemAt pAddr cp r) pAddr cp r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [paramsMemAt]
  · simp [paramsMemAt]
  · simp [paramsMemAt]
  · simp [paramsMemAt]
  · intro j hj
    unfold paramsMemAt
    have h1 : pAddr + 4 + j ≠ pAddr := by omega
    have h2 : pAddr + 4 + j ≠ pAddr + 1 := by omega
    have h3 : pAddr + 4 + j ≠ pAddr + 2 := by omega
    have h4 : pAddr + 4 + j ≠ pAddr + 3 := by omega
    have h5 : pAddr + 4 ≤ pAddr + 4 + j ∧ pAddr + 4 + j ≤ pAddr + 4 + r := by omega
    simp only [h1, h2, h3, h4, h5, ↓reduceIte, and_self]
    congr 1; omega
  · intro j hj
    unfold paramsMemAt
    have h1 : pAddr + 5 + r + j ≠ pAddr := by omega
    have h2 : pAddr + 5 + r + j ≠ pAddr + 1 := by omega
    have h3 : pAddr + 5 + r + j ≠ pAddr + 2 := by omega
    have h4 : pAddr + 5 + r + j ≠ pAddr + 3 := by omega
    have h5 : ¬ (pAddr + 4 ≤ pAddr + 5 + r + j ∧ pAddr + 5 + r + j ≤ pAddr + 4 + r) := by omega
    have h6 : pAddr + 5 + r ≤ pAddr + 5 + r + j ∧ pAddr + 5 + r + j ≤ pAddr + 5 + 2 * r := by omega
    simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte, and_self]
    congr 1; omega
  · intro j hj
    unfold paramsMemAt
    have h1 : pAddr + 6 + 2 * r + j ≠ pAddr := by omega
    have h2 : pAddr + 6 + 2 * r + j ≠ pAddr + 1 := by omega
    have h3 : pAddr + 6 + 2 * r + j ≠ pAddr + 2 := by omega
    have h4 : pAddr + 6 + 2 * r + j ≠ pAddr + 3 := by omega
    have h5 : ¬ (pAddr + 4 ≤ pAddr + 6 + 2 * r + j ∧ pAddr + 6 + 2 * r + j ≤ pAddr + 4 + r) := by omega
    have h6 : ¬ (pAddr + 5 + r ≤ pAddr + 6 + 2 * r + j ∧ pAddr + 6 + 2 * r + j ≤ pAddr + 5 + 2 * r) := by omega
    have h7 : pAddr + 6 + 2 * r ≤ pAddr + 6 + 2 * r + j ∧ pAddr + 6 + 2 * r + j ≤ pAddr + 6 + 3 * r := by omega
    simp only [h1, h2, h3, h4, h5, h6, h7, ↓reduceIte, and_self]
    congr 1; omega

/-- Non-vacuity witness for `oneShotStepBContract`: concrete 4-vertex edgeless graph at
`M = 1, r = 2, q = 2`, `cfg = ParamConfig.default`. -/
theorem oneShotStepBContract_pre_example :
    ∃ w args mem, (∀ a ∈ args, a < 2 ^ w) ∧
      (oneShotStepBContract ParamConfig.default 1 2 2 w 1 1 0 0).pre args mem := by
  set cp := coreParamsOf ParamConfig.default 1 2
  have hell : ell 1 = 2 := by unfold ell; decide
  have hN : NOf 1 2 = 4 := by unfold NOf ceilDiv; rw [hell]; decide
  have hL : LParam 1 = 8 := by unfold LParam; rw [hell]
  have hcpN : cp.N = 4 := hN
  let G : Graph := ⟨4, []⟩
  let X : Finset ℕ := Finset.range 4
  let b : ℕ := cp.N ^ (2 - 1) / 2
  have hb : b = 2 := by simp [b, hcpN]
  have hsort : X.sort (· ≤ ·) = List.range 4 := sort_range_eq_list_range 4
  let nBlocks : ℕ := numFullBlocks (X.sort (· ≤ ·)) b
  let z : ℕ := 4 / cp.D 2
  let mem : ℕ → ℕ := fun a =>
    if a = 0 then 4
    else if a = 1 then 0
    else if 10 ≤ a ∧ a < 14 then a - 10
    else if 20 ≤ a ∧ a < 33 then paramsMemAt 20 cp 2 a
    else 0
  let w : ℕ := 160
  let args : List ℕ := [2, 0, 4, 10, b, nBlocks, z, 20, 40, 50, 60, 100]
  have hnb : nBlocks = 2 := by simp [nBlocks, numFullBlocks, hsort, hb]
  have hargs_w : ∀ a ∈ args, a < 2 ^ w := by
    intro a ha
    simp only [args, hb, hnb, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  refine ⟨w, args, mem, hargs_w, 0, 4, 10, b, nBlocks, z, 20, 40, 50, 60, 100, G, X,
    rfl, by decide, by rw [hell], by omega, by omega, ?_, ?_,
    fun e he => by simp [G] at he,
    by simp only [G]; rw [hL, hN]; decide, ?_, Finset.Subset.refl _,
    fun e he => by simp [G, Graph.inside] at he,
    fun v _ => by simp [G, Graph.degIn, Graph.inside],
    by simp [G, Graph.m],
    by change cp.N ^ (2 - 1) / 2 ≤ 4; rw [hcpN]; decide,
    by change 4 ≤ cp.N ^ 2; rw [hcpN]; decide, rfl, rfl, rfl,
    fun u hu => by simp [G] at hu; simp only [mem]; split_ifs <;> omega,
    by simp [G, Graph.m], by omega, by unfold coreParamsSize; omega, by simp [G], by omega, by omega,
    Or.inr (by simp [G, Graph.m]), Or.inr (by omega), Or.inr (by unfold coreParamsSize; omega),
    Or.inl (by simp [G]), Or.inl (by simp [G]),
    Or.inr (by simp [G, Graph.m]), Or.inr (by omega), Or.inr (by unfold coreParamsSize; omega),
    Or.inr (by omega), Or.inr (by simp [G, Graph.m]), Or.inr (by omega),
    Or.inr (by unfold coreParamsSize; omega),
    fun a ha => by simp only [mem]; split_ifs <;> omega, ?_⟩
  · have hpm := coreParamsAt_paramsMemAt 20 cp 2
    have hagree : ∀ a, 20 ≤ a → a < 33 → mem a = paramsMemAt 20 cp 2 a := fun a h1 h2 => by
      simp only [mem]; split_ifs <;> omega
    refine ⟨by rw [hagree 20 (by omega) (by omega)]; exact hpm.1,
      by rw [hagree 21 (by omega) (by omega)]; exact hpm.2.1,
      by rw [hagree 22 (by omega) (by omega)]; exact hpm.2.2.1,
      by rw [hagree 23 (by omega) (by omega)]; exact hpm.2.2.2.1,
      fun j hj => by rw [hagree (20 + 4 + j) (by omega) (by omega)]; exact hpm.2.2.2.2.1 j hj,
      fun j hj => by rw [hagree (20 + 5 + 2 + j) (by omega) (by omega)]; exact hpm.2.2.2.2.2.1 j hj,
      fun j hj => by rw [hagree (20 + 6 + 2 * 2 + j) (by omega) (by omega)]; exact hpm.2.2.2.2.2.2 j hj⟩
  · intro i hi
    rcases i with _ | _ | i <;> simp [G, Graph.encode, Graph.m, mem] at hi ⊢
  · refine ⟨by simp [X], ?_⟩
    rw [hsort]
    intro i hi
    simp only [List.length_range] at hi
    rw [List.getElem_range]
    simp only [mem]
    split_ifs <;> omega
  · unfold oneShotStepBSpace coreSpaceBase
    rw [hN, hL]
    decide

end MinCostFlow.ExpanderDecomp
