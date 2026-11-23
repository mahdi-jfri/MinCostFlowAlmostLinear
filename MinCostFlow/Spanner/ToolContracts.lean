module

public import MinCostFlow.Spanner.PathDSContract
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Word-RAM Tool Contracts for Algorithm 4 (`Sparsify`)

This file defines the Word-RAM contracts and bridge theorems for `ConstructExpander` and
`Decompose`, re-exporting `PathDSContract.lean` (`PathDS`) and bundling all three into
`SpannerToolImpl` (**Algorithm 4**, page 42; *A Deterministic Almost-Linear Time Algorithm for
Minimum-Cost Flow*, arXiv:2309.16629v1):

1. `ConstructExpanderImpl` / `constructExpanderContract` (**Theorem 8.4**, page 40):
   constructs a weighted expander on `n > 1` vertices from positive natural-number weights `wList`
   at `[wAddr, …, wAddr + n)` and writes `GraphAt mem' h W` starting at `h`. Factor-2 integer
   ceiling rounding (`w v ↦ Nat.ceil (w v)`) converts any implementation (`c_deg_int`, e.g. `18`)
   to a global `ConstructExpanderTool` (`c_deg = 2 * c_deg_int`, e.g. `36`) and
   `ConstructExpanderCost` (`K_ce = 2 * impl.K_ce`).
2. `DecomposeImpl` / `decomposeContract` (**Theorem 8.5**, page 41):
   partitions a valid loopless multigraph `GraphAt mem gAddr G` into levels `0, …, ℓ` and sorted
   nontrivial components `DecomposeOutAt mem' h ℓ phiNum phiDen level rawComps`, yielding
   `DecomposeTool`, `DecomposeMonotone`, and `DecomposeCost`.
3. `PathDSImpl` / `pathDSDataStructure` (**Theorem 8.6**, page 41, via `PathDSContract.lean`):
   yielding `PathDSTool`, `PathDSMonotone`, and `PathDSCost`.
4. `SpannerToolImpl` bundling all three into `spannerTools_of_impl` and `spannerToolCosts_of_impl`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM
open MinCostFlow.Cited

/-! ## 1. `ConstructExpander` Word-RAM Contract -/

/-- Parameterized Word-RAM contract for `ConstructExpander(n, wAddr, h)`. -/
noncomputable def constructExpanderHeapContract (phiNum phiDen c_deg_int : ℕ) (K_ce : ℝ)
    (cw : ℕ) (space : ℕ → ℕ → ℕ) (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem =>
      ∃ (n wAddr h : ℕ) (wList : List ℕ),
        args = [n, wAddr, h] ∧
        1 < n ∧
        wAddr + n ≤ h ∧
        ListAt mem wAddr wList ∧
        wList.length = n ∧
        (∀ (v : ℕ) (hv : v < wList.length), 1 ≤ wList[v]) ∧
        cw * (Nat.log 2 (n + wList.sum + 2) + 1) ≤ w)
    (fun args mem mem' =>
      ∃ (n wAddr h : ℕ) (wList : List ℕ) (W : Cited.Graph),
        args = [n, wAddr, h] ∧
        ListAt mem wAddr wList ∧
        wList.length = n ∧
        GraphAt mem' h W ∧
        W.n = n ∧
        W.IsValid ∧
        W.IsConductanceExpanderOn W.verts ((phiNum : ℝ) / (phiDen : ℝ)) ∧
        ∀ (v : ℕ) (hv : v < wList.length),
          (wList[v] : ℝ) ≤ (W.deg v : ℝ) ∧
          (W.deg v : ℝ) ≤ (c_deg_int : ℝ) * (wList[v] : ℝ))
    (fun args mem =>
      let n := args.getD 0 0
      let wAddr := args.getD 1 0
      let wSum := ((List.range n).map fun v => mem (wAddr + v)).sum
      Nat.ceil (K_ce * ((n : ℝ) + (wSum : ℝ))))
    (fun args mem =>
      let n := args.getD 0 0
      let wAddr := args.getD 1 0
      let wSum := ((List.range n).map fun v => mem (wAddr + v)).sum
      space n wSum)
  { C with post := fun args mem v mem' =>
      C.post args mem v mem' ∧
      ∃ W : Cited.Graph, GraphAt mem' (heapArg args) W ∧
        heapArg args + (2 + 2 * W.m) ≤ v }

/-- Implementation witness for `ConstructExpander` (**Theorem 8.4**, page 40).
Uses positive integer weights `wList` stored via `ListAt mem wAddr wList` on call
`args = [n, wAddr, h]`, returning heap pointer `v ≥ h + 2 + 2 * W.m` and writing `GraphAt mem' h W`.
Both `phiNum, phiDen` (`1 ≤ phiNum ≤ phiDen`) are stored as concrete naturals so `Sparsify`'s
Word-RAM program can load `(phiNum, phiDen)` into `Task3` without real arithmetic. -/
structure ConstructExpanderImpl where
  /-- Rational conductance numerator `1 ≤ phiNum`. -/
  phiNum : ℕ
  /-- Rational conductance denominator `phiNum ≤ phiDen`. -/
  phiDen : ℕ
  /-- Integer-weight degree upper multiplier `c_deg_int` (e.g. `18` from Theorem 8.4). -/
  c_deg_int : ℕ
  /-- Cost multiplier `K_ce ≥ 0` in `⌈K_ce · (n + ∑ w)⌉`. -/
  K_ce : ℝ
  /-- Word-size multiplier `cw ≥ 1` requiring `cw · (Nat.log 2 (n + ∑ w + 2) + 1) ≤ w`. -/
  cw : ℕ
  /-- Heap space bound as a function of `(n, ∑ w)`. -/
  space : ℕ → ℕ → ℕ
  /-- Polynomial space multiplier `≥ 1` and degree. -/
  C_space : ℕ
  c_space : ℕ
  hphi_pos : 1 ≤ phiNum
  hphi_le : phiNum ≤ phiDen
  hc_deg_int : 1 ≤ c_deg_int
  hK_ce : 0 ≤ K_ce
  hcw_pos : 1 ≤ cw
  hC_space : 1 ≤ C_space
  hspace_le : ∀ n wSum, space n wSum ≤ C_space * (n + wSum + 2) ^ c_space
  /-- Procedure module placed at index `b` (`fn = b`). -/
  procs : ℕ → List Stmt
  hprocs_nonempty : ∀ b, 0 < (procs b).length
  spec : ∀ w (p : WordRAM.Program) b, p.HasAt b (procs b) →
    MeetsContract w p b (constructExpanderHeapContract phiNum phiDen c_deg_int K_ce cw space w)

/-- Effective conductance `φ_Const = phiNum / phiDen ∈ (0, 1]`. -/
noncomputable def ConstructExpanderImpl.φ_Const (impl : ConstructExpanderImpl) : ℝ :=
  (impl.phiNum : ℝ) / (impl.phiDen : ℝ)

lemma ConstructExpanderImpl.hφ_Const_pos (impl : ConstructExpanderImpl) :
    0 < impl.φ_Const := by
  unfold ConstructExpanderImpl.φ_Const
  have h1 : (0 : ℝ) < (impl.phiNum : ℝ) := by exact_mod_cast impl.hphi_pos
  have h2 : (0 : ℝ) < (impl.phiDen : ℝ) := by
    exact_mod_cast lt_of_lt_of_le impl.hphi_pos impl.hphi_le
  exact div_pos h1 h2

lemma ConstructExpanderImpl.hφ_Const_le (impl : ConstructExpanderImpl) :
    impl.φ_Const ≤ 1 := by
  unfold ConstructExpanderImpl.φ_Const
  have h2 : (0 : ℝ) < (impl.phiDen : ℝ) := by
    exact_mod_cast lt_of_lt_of_le impl.hphi_pos impl.hphi_le
  rw [div_le_one h2]
  exact_mod_cast impl.hphi_le

/-- The exact Word-RAM contract for `ConstructExpanderImpl` at word size `w`. -/
noncomputable def constructExpanderContract (impl : ConstructExpanderImpl) (w : ℕ) : Contract :=
  constructExpanderHeapContract impl.phiNum impl.phiDen impl.c_deg_int impl.K_ce
    impl.cw impl.space w

theorem ConstructExpanderImpl.meets {impl : ConstructExpanderImpl} {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (impl.procs b)) :
    MeetsContract w p b (constructExpanderContract impl w) :=
  impl.spec w p b hp

lemma constructExpander_run_exists (impl : ConstructExpanderImpl) (n : ℕ) (w : ℕ → ℝ)
    (hn : 1 < n) (hw : ∀ v < n, 1 ≤ w v) :
    ∃ W : Cited.Graph,
      W.n = n ∧ W.IsValid ∧ W.IsConductanceExpanderOn W.verts impl.φ_Const ∧
      ∀ v < n, (Nat.ceil (w v) : ℝ) ≤ (W.deg v : ℝ) ∧
        (W.deg v : ℝ) ≤ (impl.c_deg_int : ℝ) * (Nat.ceil (w v) : ℝ) := by
  classical
  let wList : List ℕ := (List.range n).map fun v => Nat.ceil (w v)
  have hlen : wList.length = n := by simp [wList]
  have hwList_ge : ∀ (v : ℕ) (hv : v < wList.length), 1 ≤ wList[v] := by
    intro v hv
    dsimp only [wList] at hv ⊢
    rw [List.getElem_map, List.getElem_range]
    exact Nat.one_le_ceil_iff.mpr (by linarith [hw v (by simpa [List.length_map, List.length_range] using hv)])
  let mem₀ : ℕ → ℕ := fun i => wList.getD i 0
  let w0 : ℕ := max (impl.cw * (Nat.log 2 (n + wList.sum + 2) + 1))
    (n + wList.sum + impl.space n wList.sum + 2)
  have hw0_cw : impl.cw * (Nat.log 2 (n + wList.sum + 2) + 1) ≤ w0 := le_max_left _ _
  have hbound_le : n + wList.sum + impl.space n wList.sum + 2 ≤ w0 := le_max_right _ _
  have hn_lt : n < 2 ^ w0 := nat_lt_two_pow_of_succ_le (by omega)
  have hheap_lt : n + impl.space n wList.sum < 2 ^ w0 := nat_lt_two_pow_of_succ_le (by omega)
  let p₀ : Program := ⟨impl.procs 0⟩
  have hHas : p₀.HasAt 0 (impl.procs 0) := hasAt_mk_self _
  have hList : ListAt mem₀ 0 wList := listAt_getD
  have hZero : ZeroFrom mem₀ n := by dsimp only [mem₀]; simpa [hlen] using (zeroFrom_getD (xs := wList))
  have hSumEq : ((List.range n).map fun v => mem₀ (0 + v)).sum = wList.sum := by
    simpa [hlen] using listAt_range_sum_eq hList
  have hwords : ∀ a ∈ ([n, 0, n] : List ℕ), a < 2 ^ w0 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hn_lt
    · exact Nat.pow_pos (by decide)
    · exact hn_lt
  have hpre : (constructExpanderContract impl w0).pre [n, 0, n] mem₀ := by
    refine ⟨⟨n, 0, n, wList, rfl, hn, by omega, hList, hlen, hwList_ge, hw0_cw⟩, hZero, ?_⟩
    change n + impl.space n ((List.range n).map fun v => mem₀ (0 + v)).sum < 2 ^ w0
    rw [hSumEq]
    exact hheap_lt
  obtain ⟨_, _, _, st', _, _, hpost, _⟩ :=
    impl.meets hHas [n, 0, n] mem₀ 0 (fun _ => false) hwords hpre
  rcases hpost.1.2.2.2.2 with ⟨n', wAddr', h', wList', W, heq, hList', hlen', hW, hWn, hWval, hWexp, hWdeg⟩
  simp only [List.cons.injEq, and_true] at heq
  rcases heq with ⟨hn_eq, hw_eq, hh_eq⟩
  have hlist_eq : wList' = wList := by
    apply List.ext_getElem
    · omega
    · intro i hi1 hi2
      have ha := hList i hi2
      have hb := hList' i hi1
      rw [← hw_eq] at hb
      rw [← ha, ← hb]
  refine ⟨W, hWn.trans hn_eq.symm, hWval, hWexp, fun v hv => ?_⟩
  have hv' : v < wList'.length := by omega
  have hdv := hWdeg v hv'
  have hget : wList'[v] = Nat.ceil (w v) := by
    have : wList'[v] = wList[v]'(by omega) := by simp [hlist_eq]
    rw [this]
    simp [wList]
  simpa [hget] using hdv

open Classical in
noncomputable def ceConstruct (impl : ConstructExpanderImpl) (n : ℕ) (w : ℕ → ℝ) :
    Cited.Graph :=
  if h : 1 < n ∧ ∀ v < n, 1 ≤ w v
  then Classical.choose (constructExpander_run_exists impl n w h.1 h.2)
  else ⟨n, []⟩

/-- Converts a `ConstructExpanderImpl` into a mathematical `ConstructExpanderTool` (`Tools.lean`)
using ceiling weight rounding (`w v ↦ ⌈w v⌉₊`), which scales `c_deg` by at most `2`
(`c_deg = 2 * impl.c_deg_int`, e.g. `18 ↦ 36`). -/
noncomputable def constructExpanderTool_of_impl (impl : ConstructExpanderImpl) :
    ConstructExpanderTool where
  φ_Const := impl.φ_Const
  c_deg := 2 * (impl.c_deg_int : ℝ)
  construct n w := ceConstruct impl n w
  hφ_pos := impl.hφ_Const_pos
  hφ_le := impl.hφ_Const_le
  hc_deg := by
    have h1 : (1 : ℝ) ≤ (impl.c_deg_int : ℝ) := by exact_mod_cast impl.hc_deg_int
    linarith
  construct_spec n w hn hw := by
    classical
    have hcond : 1 < n ∧ ∀ v < n, 1 ≤ w v := ⟨hn, hw⟩
    dsimp only [ceConstruct]
    split_ifs
    have hspec := Classical.choose_spec (constructExpander_run_exists impl n w hn hw)
    rcases hspec with ⟨hWn, hWval, hWexp, hWdeg⟩
    refine ⟨hWn, hWval, hWexp, fun v hv => ?_⟩
    have h1 := (hWdeg v hv).1
    have h2 := (hWdeg v hv).2
    have hlo : w v ≤ (Nat.ceil (w v) : ℝ) := Nat.le_ceil (w v)
    have hhi : (Nat.ceil (w v) : ℝ) ≤ 2 * w v := real_ceil_le_two_mul (hw v hv)
    have hc_nn : (0 : ℝ) ≤ (impl.c_deg_int : ℝ) := Nat.cast_nonneg _
    refine ⟨le_trans hlo h1, le_trans h2 ?_⟩
    nlinarith

/-- Extracts `ConstructExpanderCost` from `ConstructExpanderImpl` with factor-2 constant
`K_ce = 2 * impl.K_ce`. -/
noncomputable def constructExpanderCost_of_impl (impl : ConstructExpanderImpl) :
    ConstructExpanderCost where
  K_ce := 2 * impl.K_ce
  hK_ce := by linarith [impl.hK_ce]

theorem constructExpander_cost_le (impl : ConstructExpanderImpl) (n : ℕ) (w : ℕ → ℝ)
    (hw : ∀ v < n, 1 ≤ w v) :
    Nat.ceil (impl.K_ce * ((n : ℝ) + (((List.range n).map fun v => Nat.ceil (w v)).sum : ℝ))) ≤
      (constructExpanderCost_of_impl impl).callCost n (∑ v ∈ Finset.range n, w v) := by
  dsimp only [ConstructExpanderCost.callCost, constructExpanderCost_of_impl]
  apply Nat.ceil_mono
  have hsum := real_sum_ceil_le_two_mul n w hw
  have hK : 0 ≤ impl.K_ce := impl.hK_ce
  have hsum_nn : 0 ≤ ∑ v ∈ Finset.range n, w v :=
    Finset.sum_nonneg fun v hv => le_trans zero_le_one (hw v (Finset.mem_range.mp hv))
  nlinarith

/-! ## 2. `Decompose` Word-RAM Contract -/

/-- Mathematical specification satisfied by a `Decompose(G)` output `(d, φ)` for `c_ℓ`
(**Theorem 8.5**, page 41). -/
def DecomposeProp (c_ℓ : ℝ) (G : Cited.Graph) (d : DecomposeOutput) (φ : ℝ) : Prop :=
  (d.ℓ : ℝ) ≤ c_ℓ * ((Nat.log 2 (G.m + 2) : ℝ) + 1) ∧
  (∀ j < G.m, d.level j ≤ d.ℓ) ∧
  (∀ i ≤ d.ℓ, (d.graphAt G i).m ≤ 2 ^ i * G.n) ∧
  ∀ i, 0 < i → i ≤ d.ℓ →
    (d.comps i).Pairwise Disjoint ∧
    (∀ X ∈ d.comps i, X ⊆ G.verts ∧ 2 ≤ X.card ∧
      (d.graphAt G i).IsConductanceExpanderOn X φ ∧
      (∀ x ∈ X, φ * (2 ^ i : ℝ) ≤ ((d.graphAt G i).degIn X x : ℝ)) ∧
      ∀ e ∈ (d.graphAt G i).edges, e.1 ∈ X ↔ e.2 ∈ X) ∧
    ∀ e ∈ (d.graphAt G i).edges, ∃ X ∈ d.comps i, e.1 ∈ X ∧ e.2 ∈ X

/-- Parameterized Word-RAM contract for `Decompose(gAddr, h)`. -/
noncomputable def decomposeHeapContract (c_ℓ K_dec : ℝ) (decFactor φ_lb : ℕ → ℝ)
    (maxPhiDen : ℕ → ℕ) (cw : ℕ) (space : ℕ → ℕ → ℕ) (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem =>
      ∃ (gAddr h : ℕ) (G : Cited.Graph),
        args = [gAddr, h] ∧
        gAddr + G.encode.length ≤ h ∧
        GraphAt mem gAddr G ∧
        G.IsValid ∧
        G.IsLoopless ∧
        cw * (Nat.log 2 (G.n + G.m + maxPhiDen G.m + 2) + 1) ≤ w)
    (fun args mem mem' =>
      ∃ (gAddr h : ℕ) (G : Cited.Graph) (d_ℓ phiNum phiDen : ℕ)
          (level : List ℕ) (rawComps : List (ℕ × List ℕ)),
        args = [gAddr, h] ∧
        GraphAt mem gAddr G ∧
        DecomposeOutAt mem' h d_ℓ phiNum phiDen level rawComps ∧
        level.length = G.m ∧
        1 ≤ phiNum ∧
        phiNum ≤ phiDen ∧
        phiDen ≤ maxPhiDen G.m ∧
        φ_lb G.m ≤ (phiNum : ℝ) / (phiDen : ℝ) ∧
        rawComps.Pairwise (fun a b => a.1 ≤ b.1) ∧
        (∀ c ∈ rawComps, 1 ≤ c.1 ∧ c.1 ≤ d_ℓ ∧ c.2.Pairwise (· < ·) ∧ 2 ≤ c.2.length) ∧
        DecomposeProp c_ℓ G (mkDecomposeOutput d_ℓ level rawComps)
          ((phiNum : ℝ) / (phiDen : ℝ)))
    (fun args mem =>
      let G := Cited.readGraph mem (args.getD 0 0)
      Nat.ceil (K_dec * ((G.m : ℝ) * decFactor G.m + 1)))
    (fun args mem =>
      let G := Cited.readGraph mem (args.getD 0 0)
      space G.n G.m)
  { C with post := fun args mem v mem' =>
      C.post args mem v mem' ∧
      ∃ (d_ℓ phiNum phiDen : ℕ) (level : List ℕ) (rawComps : List (ℕ × List ℕ)),
        DecomposeOutAt mem' (heapArg args) d_ℓ phiNum phiDen level rawComps ∧
        level.length = (Cited.readGraph mem (args.getD 0 0)).m ∧
        heapArg args + (Decompose.encode d_ℓ phiNum phiDen level rawComps).length ≤ v }

/-- Subpolynomial `exp(c * log(m + 2)^{2/3} * log(log(m + 2) + 2))` factor matching Theorem B.1 / 8.5. -/
noncomputable def decomposeSubpoly (c : ℝ) (m : ℕ) : ℝ :=
  Real.exp (c * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) * Real.log (Real.log ((m : ℝ) + 2) + 2))

/-- Implementation witness for `Decompose` (**Theorem 8.5**, page 41).
Takes `args = [gAddr, h]` with `GraphAt mem gAddr G` (`gAddr + G.encode.length ≤ h`, `G.IsValid`,
`G.IsLoopless`) and writes `DecomposeOutAt mem' h ℓ phiNum phiDen level rawComps` returning
`v ≥ h + (Decompose.encode ℓ phiNum phiDen level rawComps).length`. -/
structure DecomposeImpl where
  /-- Level multiplier `c_ℓ ≥ 1` in `ℓ ≤ c_ℓ · (log₂(m + 2) + 1)`. -/
  c_ℓ : ℝ
  /-- Cost multiplier `K_dec ≥ 0` in `⌈K_dec · (m · decFactor m + 1)⌉`. -/
  K_dec : ℝ
  /-- Subpolynomial per-edge cost factor `decFactor m ≥ 1`, monotone in `m`. -/
  decFactor : ℕ → ℝ
  /-- Monotone antitone lower bound `φ_lb m ≤ φ_dec G` (`0 < φ_lb m ≤ 1`). -/
  φ_lb : ℕ → ℝ
  /-- Upper bound `phiDen ≤ maxPhiDen G.m` on the returned denominator (`≥ 1`). -/
  maxPhiDen : ℕ → ℕ
  C_phi : ℕ
  c_phi : ℕ
  /-- Word-size multiplier `cw ≥ 1`. -/
  cw : ℕ
  /-- Heap space bound as a function of `(G.n, G.m)`. -/
  space : ℕ → ℕ → ℕ
  C_space : ℕ
  c_space : ℕ
  hc_ℓ : 1 ≤ c_ℓ
  hK_dec : 0 ≤ K_dec
  hdec_ge : ∀ m, 1 ≤ decFactor m
  hdec_mono : ∀ ⦃m₁ m₂ : ℕ⦄, m₁ ≤ m₂ → decFactor m₁ ≤ decFactor m₂
  hφ_lb_pos : ∀ m, 0 < φ_lb m
  hφ_lb_le : ∀ m, φ_lb m ≤ 1
  hφ_lb_anti : ∀ ⦃m₁ m₂ : ℕ⦄, m₁ ≤ m₂ → φ_lb m₂ ≤ φ_lb m₁
  hmaxPhiDen_pos : ∀ m, 1 ≤ maxPhiDen m
  hC_phi : 1 ≤ C_phi
  hmaxPhiDen_le : ∀ m, maxPhiDen m ≤ C_phi * (m + 2) ^ c_phi
  hcw_pos : 1 ≤ cw
  hC_space : 1 ≤ C_space
  hspace_le : ∀ n m, space n m ≤ C_space * (n + m + 2) ^ c_space
  procs : ℕ → List Stmt
  hprocs_nonempty : ∀ b, 0 < (procs b).length
  spec : ∀ w (p : WordRAM.Program) b, p.HasAt b (procs b) →
    MeetsContract w p b (decomposeHeapContract c_ℓ K_dec decFactor φ_lb maxPhiDen cw space w)

/-- Subpolynomial bound `1 / φ_lb m ≤ invPhiC · decomposeSubpoly invPhiExp m` on the inverse
conductance of `Decompose` (**Theorem 8.5**). It is kept apart from `DecomposeImpl` so that the
implementation in `Expander/DecomposeProg.lean` does not need to supply it. -/
structure DecomposeImpl.InvPhiBound (impl : DecomposeImpl) where
  invPhiC : ℝ
  invPhiExp : ℝ
  hinvPhiC : 0 < invPhiC
  hinvPhiExp : 0 ≤ invPhiExp
  hinvPhi_le : ∀ m, 1 / impl.φ_lb m ≤ invPhiC * decomposeSubpoly invPhiExp m

/-- The exact Word-RAM contract for `DecomposeImpl` at word size `w`. -/
noncomputable def decomposeContract (impl : DecomposeImpl) (w : ℕ) : Contract :=
  decomposeHeapContract impl.c_ℓ impl.K_dec impl.decFactor impl.φ_lb impl.maxPhiDen
    impl.cw impl.space w

theorem DecomposeImpl.meets {impl : DecomposeImpl} {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b (impl.procs b)) :
    MeetsContract w p b (decomposeContract impl w) :=
  impl.spec w p b hp

lemma decompose_run_exists (impl : DecomposeImpl) (G : Cited.Graph)
    (hV : G.IsValid) (hL : G.IsLoopless) :
    ∃ (d : DecomposeOutput) (phiNum phiDen : ℕ),
      1 ≤ phiNum ∧ phiNum ≤ phiDen ∧ phiDen ≤ impl.maxPhiDen G.m ∧
      impl.φ_lb G.m ≤ (phiNum : ℝ) / (phiDen : ℝ) ∧
      DecomposeProp impl.c_ℓ G d ((phiNum : ℝ) / (phiDen : ℝ)) := by
  classical
  let enc := G.encode
  have henc_len : enc.length = 2 + 2 * G.m := graph_encode_length G
  let h0 := enc.length
  let mem₀ : ℕ → ℕ := fun i => enc.getD i 0
  let w0 : ℕ := max (impl.cw * (Nat.log 2 (G.n + G.m + impl.maxPhiDen G.m + 2) + 1))
    (G.n + G.m + h0 + impl.space G.n G.m + 2)
  have hw0_cw : impl.cw * (Nat.log 2 (G.n + G.m + impl.maxPhiDen G.m + 2) + 1) ≤ w0 :=
    le_max_left _ _
  have hbound_le : G.n + G.m + h0 + impl.space G.n G.m + 2 ≤ w0 := le_max_right _ _
  have hh0_lt : h0 < 2 ^ w0 := nat_lt_two_pow_of_succ_le (by omega)
  have hheap_lt : h0 + impl.space G.n G.m < 2 ^ w0 := nat_lt_two_pow_of_succ_le (by omega)
  let p₀ : Program := ⟨impl.procs 0⟩
  have hHas : p₀.HasAt 0 (impl.procs 0) := hasAt_mk_self _
  have hG : GraphAt mem₀ 0 G := listAt_getD
  have hRead : Cited.readGraph mem₀ 0 = G := graphAt_iff_readGraph.mp hG
  have hZero : ZeroFrom mem₀ h0 := zeroFrom_getD
  have hwords : ∀ a ∈ ([0, h0] : List ℕ), a < 2 ^ w0 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact Nat.pow_pos (by decide)
    · exact hh0_lt
  have hpre : (decomposeContract impl w0).pre [0, h0] mem₀ := by
    refine ⟨⟨0, h0, G, rfl, by dsimp only [h0, enc]; omega, hG, hV, hL, hw0_cw⟩, hZero, ?_⟩
    change h0 + impl.space (Cited.readGraph mem₀ 0).n (Cited.readGraph mem₀ 0).m < 2 ^ w0
    rw [hRead]
    exact hheap_lt
  obtain ⟨_, _, _, st', _, _, hpost, _⟩ :=
    impl.meets hHas [0, h0] mem₀ 0 (fun _ => false) hwords hpre
  rcases hpost.1.2.2.2.2 with
    ⟨gAddr', h', G', d_ℓ, phiNum, phiDen, level, rawComps, heq, hG', _, _, hpn, hpd, hmax, hlb, _, _, hprop⟩
  simp only [List.cons.injEq, and_true] at heq
  rcases heq with ⟨hg_eq, hh_eq⟩
  have hGeq : G' = G := by
    have hr1 : Cited.readGraph mem₀ gAddr' = G' := graphAt_iff_readGraph.mp hG'
    rw [← hg_eq, hRead] at hr1
    exact hr1.symm
  exact ⟨mkDecomposeOutput d_ℓ level rawComps, phiNum, phiDen, hpn, hpd, hGeq ▸ hmax,
    hGeq ▸ hlb, hGeq ▸ hprop⟩

open Classical in
noncomputable def decomposePair (impl : DecomposeImpl) (G : Cited.Graph) :
    DecomposeOutput × ℝ :=
  if h : G.IsValid ∧ G.IsLoopless
  then
    let d := Classical.choose (decompose_run_exists impl G h.1 h.2)
    let phiNum := Classical.choose (Classical.choose_spec (decompose_run_exists impl G h.1 h.2))
    let phiDen := Classical.choose
      (Classical.choose_spec (Classical.choose_spec (decompose_run_exists impl G h.1 h.2)))
    (d, (phiNum : ℝ) / (phiDen : ℝ))
  else ({ ℓ := 0, level := fun _ => 0, comps := fun _ => [] }, 1)

/-- Converts a `DecomposeImpl` into a mathematical `DecomposeTool` (`Tools.lean`). -/
noncomputable def decomposeTool_of_impl (impl : DecomposeImpl) : DecomposeTool where
  c_ℓ := impl.c_ℓ
  φ_dec G := (decomposePair impl G).2
  decompose G := (decomposePair impl G).1
  hc_ℓ := impl.hc_ℓ
  hφ_pos G hV hL := by
    classical
    have hcond : G.IsValid ∧ G.IsLoopless := ⟨hV, hL⟩
    dsimp only [decomposePair]
    split_ifs
    have hsp := Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (decompose_run_exists impl G hV hL)))
    have h1 : (0 : ℝ) < ((Classical.choose
        (Classical.choose_spec (decompose_run_exists impl G hV hL)) : ℕ) : ℝ) := by
      exact_mod_cast hsp.1
    have h2 : (0 : ℝ) < ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec (decompose_run_exists impl G hV hL))) : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hsp.1 hsp.2.1
    exact div_pos h1 h2
  hφ_le G hV hL := by
    classical
    have hcond : G.IsValid ∧ G.IsLoopless := ⟨hV, hL⟩
    dsimp only [decomposePair]
    split_ifs
    have hsp := Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (decompose_run_exists impl G hV hL)))
    have h2 : (0 : ℝ) < ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec (decompose_run_exists impl G hV hL))) : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hsp.1 hsp.2.1
    rw [div_le_one h2]
    exact_mod_cast hsp.2.1
  decompose_spec G hV hL := by
    classical
    have hcond : G.IsValid ∧ G.IsLoopless := ⟨hV, hL⟩
    dsimp only [decomposePair]
    split_ifs
    have hsp := Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (decompose_run_exists impl G hV hL)))
    exact hsp.2.2.2.2

/-- Extracts `DecomposeMonotone` from `DecomposeImpl`. -/
noncomputable def decomposeMonotone_of_impl (impl : DecomposeImpl) :
    DecomposeMonotone (decomposeTool_of_impl impl) where
  φ_lb := impl.φ_lb
  hφ_lb_pos := impl.hφ_lb_pos
  hφ_lb_le := impl.hφ_lb_le
  hφ_lb_anti := impl.hφ_lb_anti
  hφ_dec_ge G hV hL := by
    classical
    have hcond : G.IsValid ∧ G.IsLoopless := ⟨hV, hL⟩
    dsimp only [decomposeTool_of_impl, decomposePair]
    split_ifs
    have hsp := Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (decompose_run_exists impl G hV hL)))
    exact hsp.2.2.2.1

/-- Extracts `DecomposeCost` from `DecomposeImpl` with factor `2 * impl.K_dec`. -/
noncomputable def decomposeCost_of_impl (impl : DecomposeImpl) : DecomposeCost where
  K_dec := 2 * impl.K_dec
  decFactor := impl.decFactor
  hK_dec := by linarith [impl.hK_dec]
  hdec_ge := impl.hdec_ge
  hdec_mono := impl.hdec_mono

theorem decompose_cost_le (impl : DecomposeImpl) {m : ℕ} (hm : 1 ≤ m) :
    Nat.ceil (impl.K_dec * ((m : ℝ) * impl.decFactor m + 1)) ≤
      (decomposeCost_of_impl impl).callCost m := by
  dsimp only [DecomposeCost.callCost, decomposeCost_of_impl]
  apply Nat.ceil_mono
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hdf : 1 ≤ impl.decFactor m := impl.hdec_ge m
  have h1 : (1 : ℝ) ≤ (m : ℝ) * impl.decFactor m := by nlinarith
  nlinarith [impl.hK_dec]

/-! ## 3. Bundled Tool Implementation Package -/

/-- Complete Word-RAM tool implementations for `Sparsify`. -/
structure SpannerToolImpl where
  constructExpander : ConstructExpanderImpl
  decompose : DecomposeImpl
  pathDS : PathDSImpl

/-- Extracts `SpannerTools` (`Tools.lean`) from `SpannerToolImpl`. -/
noncomputable def spannerTools_of_impl (impl : SpannerToolImpl) : SpannerTools where
  constructExpander := constructExpanderTool_of_impl impl.constructExpander
  decompose := decomposeTool_of_impl impl.decompose
  pathDS := pathDSTool_of_impl impl.pathDS

/-- Extracts `SpannerToolCosts` (`ToolCosts.lean`) from `SpannerToolImpl`. -/
noncomputable def spannerToolCosts_of_impl (impl : SpannerToolImpl) : SpannerToolCosts where
  constructExpander := constructExpanderCost_of_impl impl.constructExpander
  decompose := decomposeCost_of_impl impl.decompose
  pathDS := pathDSCost_of_impl impl.pathDS

end MinCostFlow.Spanner
