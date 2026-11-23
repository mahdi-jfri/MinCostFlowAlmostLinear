module

public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Spanner.ToolCosts
public import MinCostFlow.Spanner.Runtime
public import MinCostFlow.Statement.Cited.ChuzhoySaranurak
public import WordRAM.DataStructure
public import WordRAM.Layout

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Word-RAM `PathDS` Data-Structure Contract (Theorem 8.6)

This file defines the Word-RAM `WordRAM.DataStructure PathDSAbsState` specification for `PathDS`
(**Theorem 8.6**, page 41; *A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow*,
arXiv:2309.16629v1) and proves that any Word-RAM implementation `PathDSImpl` yields:

* `pathDSTool_of_impl : PathDSTool` (`Tools.lean`), using unit-numerator rounding
  `φ_in ↦ 1 / Nat.ceil (1 / φ_in)` and tracking an explicit `G.m`-step heap budget across
  all `Delete` and `GetPath` calls;
* `pathDSMonotone_of_impl : PathDSMonotone` (`Runtime.lean`);
* `pathDSCost_of_impl : PathDSCost` (`ToolCosts.lean`), together with `pathDS_init_del_cost_le`
  and `pathDS_query_cost_le`.

Also provides small shared Word-RAM canonical-memory helpers used by `ToolContracts.lean`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM
open MinCostFlow.Cited

/-! ## Shared Word-RAM canonical memory and ceiling helpers -/

lemma listAt_getD {xs : List ℕ} :
    ListAt (fun i => xs.getD i 0) 0 xs := by
  intro i hi
  dsimp only
  rw [Nat.zero_add, List.getD_eq_getElem _ _ hi]

lemma zeroFrom_getD {xs : List ℕ} :
    ZeroFrom (fun i => xs.getD i 0) xs.length := by
  intro a ha
  exact List.getD_eq_default xs 0 ha

lemma graphAt_iff_readGraph {mem : ℕ → ℕ} {a : ℕ} {G : Cited.Graph} :
    GraphAt mem a G ↔ Cited.readGraph mem a = G := by
  constructor
  · intro h
    cases G with
    | mk n edges =>
      dsimp only [Cited.readGraph]
      have hn : mem a = n := graphAt_n h
      have hm : mem (a + 1) = edges.length := graphAt_m h
      congr 1
      apply List.ext_getElem
      · rw [List.length_map, List.length_range, hm]
      · intro j hj1 hj2
        rw [List.length_map, List.length_range, hm] at hj1
        rw [List.getElem_map, List.getElem_range]
        ext
        · exact graphAt_edge_fst h hj2
        · exact graphAt_edge_snd h hj2
  · intro h
    rw [← h]
    exact graphAt_of_cells rfl (by simp [Cited.readGraph, Graph.m]) fun j hj => by
      simp [Cited.readGraph]

lemma hasAt_mk_self (stmts : List Stmt) :
    (⟨stmts⟩ : WordRAM.Program).HasAt 0 stmts := by
  intro i hi
  simp [List.getElem?_eq_getElem hi]

lemma nat_lt_two_pow_succ (x : ℕ) : x < 2 ^ (x + 1) :=
  lt_of_lt_of_le (Nat.lt_succ_self x) (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))

lemma nat_lt_two_pow_of_succ_le {x w : ℕ} (h : x + 1 ≤ w) : x < 2 ^ w :=
  lt_of_lt_of_le (nat_lt_two_pow_succ x) (Nat.pow_le_pow_right (by decide) h)

lemma real_ceil_le_two_mul {x : ℝ} (hx : 1 ≤ x) :
    (Nat.ceil x : ℝ) ≤ 2 * x := by
  have hceil : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  linarith

lemma real_sum_ceil_le_two_mul (n : ℕ) (w : ℕ → ℝ) (hw : ∀ v < n, 1 ≤ w v) :
    (((List.range n).map fun v => Nat.ceil (w v)).sum : ℝ) ≤
      2 * ∑ v ∈ Finset.range n, w v := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hw_pref : ∀ v < n, 1 ≤ w v := fun v hv => hw v (Nat.lt_succ_of_lt hv)
    have hwn := hw n (Nat.lt_succ_self n)
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      Finset.sum_range_succ, Nat.cast_add]
    have hceil_n := real_ceil_le_two_mul hwn
    linarith [ih hw_pref]

lemma nat_le_ceil_of_cast_le {k : ℕ} {r : ℝ} (h : (k : ℝ) ≤ r) : k ≤ Nat.ceil r :=
  Nat.cast_le.mp (le_trans h (Nat.le_ceil r))

lemma listAt_range_sum_eq {mem : ℕ → ℕ} {a : ℕ} {xs : List ℕ}
    (hxs : ListAt mem a xs) :
    ((List.range xs.length).map fun v => mem (a + v)).sum = xs.sum := by
  have hmap : (List.range xs.length).map (fun v => mem (a + v)) = xs := by
    apply List.ext_getElem
    · simp
    · intro i hi1 _
      simp only [List.length_map, List.length_range] at hi1
      simp only [List.getElem_map, List.getElem_range]
      exact hxs i hi1
  rw [hmap]

/-! ## `PathDS` Word-RAM Data-Structure Contract -/

/-- Abstract mathematical state of `PathDS` (**Theorem 8.6**, page 41) carried across Word-RAM
`init`, `op 0` (`Delete`), and `op 1` (`GetPath`) operations. -/
structure PathDSAbsState where
  phiNum : ℕ
  phiDen : ℕ
  M : ℕ
  G : Cited.Graph
  Vhat : Finset ℕ
  deleted : Finset ℕ

/-- Rational initial conductance `φ_in = phiNum / phiDen`. -/
noncomputable def PathDSAbsState.φ_in (s : PathDSAbsState) : ℝ :=
  (s.phiNum : ℝ) / (s.phiDen : ℝ)

/-- Exact integer ceiling `⌈b / a⌉₊ = (b + a - 1) / a` matching `Nat.ceil (1 / ((a : ℝ) / (b : ℝ)))`. -/
lemma nat_ceil_div_eq {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Nat.ceil (1 / ((a : ℝ) / (b : ℝ))) = (b + a - 1) / a := by
  have ha0 : 0 < a := ha
  set k := (b + a - 1) / a
  have hk_pos : 1 ≤ k := Nat.div_pos (by omega) ha0
  have h1 : k * a ≤ b + a - 1 := Nat.div_mul_le_self (b + a - 1) a
  have h2 : b + a - 1 < k * a + a := by
    have hlt := Nat.lt_div_mul_add ha0 (a := b + a - 1)
    dsimp only [k]
    nlinarith
  have hlo : ((k - 1 : ℕ) : ℝ) < (b : ℝ) / (a : ℝ) := by
    rw [lt_div_iff₀ (by exact_mod_cast ha0)]
    have hnat : (k - 1) * a < b := by
      have : k * a = (k - 1) * a + a := by
        calc k * a = (k - 1 + 1) * a := by rw [Nat.sub_add_cancel hk_pos]
          _ = (k - 1) * a + a := by ring
      omega
    exact_mod_cast hnat
  have hhi : (b : ℝ) / (a : ℝ) ≤ (k : ℝ) := by
    rw [div_le_iff₀ (by exact_mod_cast ha0)]
    exact_mod_cast (by omega : b ≤ k * a)
  rw [one_div_div]
  exact Nat.ceil_eq_iff (by omega : k ≠ 0) |>.mpr ⟨hlo, hhi⟩

/-- Parameter and resource bundle for a Word-RAM `PathDS` implementation (`WordRAM.DataStructure`),
parameterized by exact integer-valued bounds `(phiOutDen, gExp, gDel)` on `(d = ⌈1 / φ_in⌉₊, M)`
computed by `boundsProcs` in `O(log(d + M + 2) + 1)` Word-RAM steps, and by the time bound
`gQuery ≥ gExp` of one `Delete` or `GetPath`.

`gExp` bounds the length of the returned paths (`γ_ExpPath` of Theorem 8.6, page 41). `gQuery`
bounds the time of one operation (`γ_query`). The two differ on clusters below the conductance of
[CS21], where `GetPath` falls back to a search over the cluster (see "Where the proof departs
from the paper", Theorem 8.6, in the README). -/
structure PathDSParams where
  phiOutDen : ℕ → ℕ → ℕ
  gExp : ℕ → ℕ → ℕ
  gDel : ℕ → ℕ → ℕ
  gQuery : ℕ → ℕ → ℕ
  hphiOutDen_ge : ∀ d M, 1 ≤ d → max 2 d ≤ phiOutDen d M
  hgExp_ge : ∀ d M, 1 ≤ d → phiOutDen d M ≤ gExp d M
  hgDel_ge : ∀ d M, 1 ≤ d → 1 ≤ gDel d M
  hphiOutDen_mono : ∀ ⦃d₁ d₂ M₁ M₂ : ℕ⦄, 1 ≤ d₁ → d₁ ≤ d₂ → M₁ ≤ M₂ →
    phiOutDen d₁ M₁ ≤ phiOutDen d₂ M₂
  hgExp_mono : ∀ ⦃d₁ d₂ M₁ M₂ : ℕ⦄, 1 ≤ d₁ → d₁ ≤ d₂ → M₁ ≤ M₂ →
    gExp d₁ M₁ ≤ gExp d₂ M₂
  hgDel_mono : ∀ ⦃d₁ d₂ M₁ M₂ : ℕ⦄, 1 ≤ d₁ → d₁ ≤ d₂ → M₁ ≤ M₂ →
    gDel d₁ M₁ ≤ gDel d₂ M₂
  hgQuery_ge : ∀ d M, 1 ≤ d → gExp d M ≤ gQuery d M
  hgQuery_mono : ∀ ⦃d₁ d₂ M₁ M₂ : ℕ⦄, 1 ≤ d₁ → d₁ ≤ d₂ → M₁ ≤ M₂ →
    gQuery d₁ M₁ ≤ gQuery d₂ M₂
  /-- Polynomial upper bounds on the query time and the deletion factor. With `hgExp_ge` and
  `hgQuery_ge` they also bound `phiOutDen` and `gExp` (`PathDSParams.poly_bounds`). The caller
  needs them to show that these numbers fit in words of `O(log(d + M))` bits. -/
  hpoly : ∃ C k : ℕ, ∀ d M, 1 ≤ d →
    gQuery d M ≤ C * (d + M + 2) ^ k ∧ gDel d M ≤ C * (d + M + 2) ^ k
  K_init : ℝ
  K_del : ℝ
  K_query : ℝ
  hK_init : 0 ≤ K_init
  hK_del : 0 ≤ K_del
  hK_query : 0 ≤ K_query
  K_bounds : ℕ
  cw : ℕ
  hcw_pos : 1 ≤ cw
  boundsSpace : ℕ → ℕ → ℕ
  initSpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  delSpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  querySpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  C_space : ℕ
  c_space : ℕ
  hC_space : 1 ≤ C_space
  hboundsSpace_le : ∀ d M, boundsSpace d M ≤ C_space * (d + M + 2) ^ c_space
  hinitSpace_le : ∀ phiNum phiDen n m M, 1 ≤ phiNum → phiNum ≤ phiDen →
    initSpace phiNum phiDen n m M ≤
      C_space * (phiDen + n + m + M + gExp ((phiDen + phiNum - 1) / phiNum) M + 2) ^ c_space
  hdelSpace_le : ∀ phiNum phiDen n m M, 1 ≤ phiNum → phiNum ≤ phiDen →
    delSpace phiNum phiDen n m M ≤
      C_space * (phiDen + n + m + M + gExp ((phiDen + phiNum - 1) / phiNum) M + 2) ^ c_space
  hquerySpace_le : ∀ phiNum phiDen n m M, 1 ≤ phiNum → phiNum ≤ phiDen →
    querySpace phiNum phiDen n m M ≤
      C_space * (phiDen + n + m + M + gExp ((phiDen + phiNum - 1) / phiNum) M + 2) ^ c_space

/-- Polynomial upper bounds on all four parameters of `PathDSParams`. -/
theorem PathDSParams.poly_bounds (p : PathDSParams) :
    ∃ C k : ℕ, ∀ d M, 1 ≤ d →
      p.phiOutDen d M ≤ C * (d + M + 2) ^ k ∧ p.gExp d M ≤ C * (d + M + 2) ^ k ∧
      p.gDel d M ≤ C * (d + M + 2) ^ k ∧ p.gQuery d M ≤ C * (d + M + 2) ^ k := by
  obtain ⟨C, k, h⟩ := p.hpoly
  refine ⟨C, k, fun d M hd => ?_⟩
  obtain ⟨hq, hdel⟩ := h d M hd
  have h1 := p.hgExp_ge d M hd
  have h2 := p.hgQuery_ge d M hd
  exact ⟨by omega, by omega, hdel, hq⟩

noncomputable def PathDSParams.φ_out (p : PathDSParams) (φ_in : ℝ) (M : ℕ) : ℝ :=
  1 / (p.phiOutDen (Nat.ceil (1 / φ_in)) M : ℝ)

noncomputable def PathDSParams.γ_ExpPath (p : PathDSParams) (φ_in : ℝ) (M : ℕ) : ℝ :=
  (p.gExp (Nat.ceil (1 / φ_in)) M : ℝ)

noncomputable def PathDSParams.γ_del (p : PathDSParams) (φ_in : ℝ) (M : ℕ) : ℝ :=
  (p.gDel (Nat.ceil (1 / φ_in)) M : ℝ)

/-- Time bound `γ_query` of one `Delete` or `GetPath`, at `d = ⌈1 / φ_in⌉₊`. -/
noncomputable def PathDSParams.γ_query (p : PathDSParams) (φ_in : ℝ) (M : ℕ) : ℝ :=
  (p.gQuery (Nat.ceil (1 / φ_in)) M : ℝ)

lemma PathDSParams.hφ_out_pos (p : PathDSParams) (φ_in : ℝ) (M : ℕ) (hφ : 0 < φ_in) :
    0 < p.φ_out φ_in M := by
  have hd : 1 ≤ Nat.ceil (1 / φ_in) := Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ)
  have hge := p.hphiOutDen_ge _ M hd
  have hpos : (0 : ℝ) < (p.phiOutDen (Nat.ceil (1 / φ_in)) M : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < max 2 (Nat.ceil (1 / φ_in))) hge
  exact div_pos one_pos hpos

lemma PathDSParams.hφ_out_le (p : PathDSParams) (φ_in : ℝ) (M : ℕ) (hφ : 0 < φ_in) :
    p.φ_out φ_in M ≤ φ_in := by
  have hd : 1 ≤ Nat.ceil (1 / φ_in) := Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ)
  have hge : Nat.ceil (1 / φ_in) ≤ p.phiOutDen (Nat.ceil (1 / φ_in)) M :=
    le_trans (le_max_right _ _) (p.hphiOutDen_ge _ M hd)
  have h1 : 1 / φ_in ≤ (p.phiOutDen (Nat.ceil (1 / φ_in)) M : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hge)
  calc 1 / (p.phiOutDen (Nat.ceil (1 / φ_in)) M : ℝ)
      ≤ 1 / (1 / φ_in) := one_div_le_one_div_of_le (div_pos one_pos hφ) h1
    _ = φ_in := one_div_one_div φ_in

lemma PathDSParams.hφ_out_half (p : PathDSParams) (φ_in : ℝ) (M : ℕ) (hφ : 0 < φ_in) :
    p.φ_out φ_in M ≤ 1 / 2 := by
  have hd : 1 ≤ Nat.ceil (1 / φ_in) := Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ)
  have hge : 2 ≤ p.phiOutDen (Nat.ceil (1 / φ_in)) M :=
    le_trans (le_max_left _ _) (p.hphiOutDen_ge _ M hd)
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hge)

lemma PathDSParams.hγ_ExpPath_ge (p : PathDSParams) (φ_in : ℝ) (M : ℕ) (hφ : 0 < φ_in) :
    1 / p.φ_out φ_in M ≤ p.γ_ExpPath φ_in M := by
  have hd : 1 ≤ Nat.ceil (1 / φ_in) := Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ)
  unfold PathDSParams.φ_out PathDSParams.γ_ExpPath
  rw [one_div_one_div]
  exact_mod_cast p.hgExp_ge _ M hd

lemma PathDSParams.hγ_query_ge (p : PathDSParams) (φ_in : ℝ) (M : ℕ) (hφ : 0 < φ_in) :
    p.γ_ExpPath φ_in M ≤ p.γ_query φ_in M := by
  have hd : 1 ≤ Nat.ceil (1 / φ_in) := Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ)
  unfold PathDSParams.γ_ExpPath PathDSParams.γ_query
  exact_mod_cast p.hgQuery_ge _ M hd

lemma PathDSParams.one_le_γ_ExpPath (p : PathDSParams) (φ_in : ℝ) (M : ℕ) (hφ : 0 < φ_in) :
    1 ≤ p.γ_ExpPath φ_in M := by
  have hd : 1 ≤ Nat.ceil (1 / φ_in) := Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ)
  have h2 : 2 ≤ p.gExp (Nat.ceil (1 / φ_in)) M :=
    le_trans (le_trans (le_max_left 2 _) (p.hphiOutDen_ge _ M hd)) (p.hgExp_ge _ M hd)
  unfold PathDSParams.γ_ExpPath
  exact_mod_cast le_trans (by norm_num) h2

lemma PathDSParams.hγ_del_ge (p : PathDSParams) (φ_in : ℝ) (M : ℕ) (hφ : 0 < φ_in) :
    1 ≤ p.γ_del φ_in M := by
  have hd : 1 ≤ Nat.ceil (1 / φ_in) := Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ)
  unfold PathDSParams.γ_del
  exact_mod_cast p.hgDel_ge _ M hd

lemma PathDSParams.hφ_out_mono (p : PathDSParams) {φ₁ φ₂ : ℝ} {M₁ M₂ : ℕ}
    (h1 : 0 < φ₁) (h12 : φ₁ ≤ φ₂) (_ : φ₂ ≤ 1) (hM : M₁ ≤ M₂) :
    p.φ_out φ₁ M₂ ≤ p.φ_out φ₂ M₁ := by
  have hd2 : 1 ≤ Nat.ceil (1 / φ₂) :=
    Nat.one_le_ceil_iff.mpr (div_pos one_pos (lt_of_lt_of_le h1 h12))
  have hd12 : Nat.ceil (1 / φ₂) ≤ Nat.ceil (1 / φ₁) :=
    Nat.ceil_mono (one_div_le_one_div_of_le h1 h12)
  have hden := p.hphiOutDen_mono hd2 hd12 hM
  have hpos : (0 : ℝ) < (p.phiOutDen (Nat.ceil (1 / φ₂)) M₁ : ℝ) := by
    have := le_trans (le_max_left 2 _) (p.hphiOutDen_ge _ M₁ hd2)
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) this
  exact one_div_le_one_div_of_le hpos (by exact_mod_cast hden)

lemma PathDSParams.hγ_ExpPath_mono (p : PathDSParams) {φ₁ φ₂ : ℝ} {M₁ M₂ : ℕ}
    (h1 : 0 < φ₁) (h12 : φ₁ ≤ φ₂) (_ : φ₂ ≤ 1) (hM : M₁ ≤ M₂) :
    p.γ_ExpPath φ₂ M₁ ≤ p.γ_ExpPath φ₁ M₂ := by
  have hd2 : 1 ≤ Nat.ceil (1 / φ₂) :=
    Nat.one_le_ceil_iff.mpr (div_pos one_pos (lt_of_lt_of_le h1 h12))
  have hd12 : Nat.ceil (1 / φ₂) ≤ Nat.ceil (1 / φ₁) :=
    Nat.ceil_mono (one_div_le_one_div_of_le h1 h12)
  unfold PathDSParams.γ_ExpPath
  exact_mod_cast p.hgExp_mono hd2 hd12 hM

lemma PathDSParams.hγ_del_mono (p : PathDSParams) {φ₁ φ₂ : ℝ} {M₁ M₂ : ℕ}
    (h1 : 0 < φ₁) (h12 : φ₁ ≤ φ₂) (_ : φ₂ ≤ 1) (hM : M₁ ≤ M₂) :
    p.γ_del φ₂ M₁ ≤ p.γ_del φ₁ M₂ := by
  have hd2 : 1 ≤ Nat.ceil (1 / φ₂) :=
    Nat.one_le_ceil_iff.mpr (div_pos one_pos (lt_of_lt_of_le h1 h12))
  have hd12 : Nat.ceil (1 / φ₂) ≤ Nat.ceil (1 / φ₁) :=
    Nat.ceil_mono (one_div_le_one_div_of_le h1 h12)
  unfold PathDSParams.γ_del
  exact_mod_cast p.hgDel_mono hd2 hd12 hM

lemma PathDSParams.hγ_query_mono (p : PathDSParams) {φ₁ φ₂ : ℝ} {M₁ M₂ : ℕ}
    (h1 : 0 < φ₁) (h12 : φ₁ ≤ φ₂) (_ : φ₂ ≤ 1) (hM : M₁ ≤ M₂) :
    p.γ_query φ₂ M₁ ≤ p.γ_query φ₁ M₂ := by
  have hd2 : 1 ≤ Nat.ceil (1 / φ₂) :=
    Nat.one_le_ceil_iff.mpr (div_pos one_pos (lt_of_lt_of_le h1 h12))
  have hd12 : Nat.ceil (1 / φ₂) ≤ Nat.ceil (1 / φ₁) :=
    Nat.ceil_mono (one_div_le_one_div_of_le h1 h12)
  unfold PathDSParams.γ_query
  exact_mod_cast p.hgQuery_mono hd2 hd12 hM

/-- State invariant carried by `PathDS` across `init`, `Delete` (`op 0`), and `GetPath` (`op 1`). -/
def PathDSAbsState.Valid (p : PathDSParams) (s : PathDSAbsState) : Prop :=
  1 ≤ s.phiNum ∧
  s.phiNum ≤ s.phiDen ∧
  s.G.IsValid ∧
  1 ≤ s.G.m ∧
  s.G.m ≤ s.M ∧
  (∀ v < s.G.n, 1 ≤ s.G.deg v) ∧
  s.G.IsConductanceExpanderOn s.G.verts s.φ_in ∧
  s.Vhat ⊆ s.G.verts ∧
  s.deleted ⊆ Finset.range s.G.m ∧
  (s.G.vol s.Vhat : ℝ) ≤
    p.γ_del s.φ_in s.M * (s.deleted.card : ℝ) / p.φ_out s.φ_in s.M

/-- Word-RAM `WordRAM.DataStructure PathDSAbsState` specification for `PathDS`
(`init` at `[gAddr, phiNum, phiDen, M, h]`, `op 0` at `[b, e, h]`, `op 1` at `[b, u, v, h]`).
Initialization costs `⌈K_init · m · γ_ExpPath⌉`. Each `Delete` and `GetPath` costs
`⌈K · γ_query⌉` amortized, and each returned path has at most `γ_ExpPath` edges. -/
noncomputable def pathDSDataStructure (p : PathDSParams) (w : ℕ) :
    DataStructure PathDSAbsState where
  initPre args mem :=
    ∃ (gAddr phiNum phiDen M h : ℕ) (G : Cited.Graph),
      args = [gAddr, phiNum, phiDen, M, h] ∧
      gAddr + G.encode.length ≤ h ∧
      GraphAt mem gAddr G ∧
      1 ≤ phiNum ∧
      phiNum ≤ phiDen ∧
      G.IsValid ∧
      1 ≤ G.m ∧
      G.m ≤ M ∧
      (∀ v < G.n, 1 ≤ G.deg v) ∧
      G.IsConductanceExpanderOn G.verts ((phiNum : ℝ) / (phiDen : ℝ)) ∧
      p.cw * (Nat.log 2 (G.n + G.m + phiDen + M +
        Nat.ceil (p.γ_ExpPath ((phiNum : ℝ) / (phiDen : ℝ)) M) + 2) + 1) ≤ w
  initPost args mem s _ :=
    ∃ (gAddr phiNum phiDen M h : ℕ) (G : Cited.Graph),
      args = [gAddr, phiNum, phiDen, M, h] ∧
      GraphAt mem gAddr G ∧
      s.phiNum = phiNum ∧
      s.phiDen = phiDen ∧
      s.M = M ∧
      s.G = G ∧
      s.Vhat = ∅ ∧
      s.deleted = ∅ ∧
      s.Valid p
  initCost args mem :=
    let G := Cited.readGraph mem (args.getD 0 0)
    let φ := ((args.getD 1 0 : ℕ) : ℝ) / ((args.getD 2 0 : ℕ) : ℝ)
    Nat.ceil (p.K_init * (G.m : ℝ) * p.γ_ExpPath φ (args.getD 3 0))
  initSpace args mem :=
    let G := Cited.readGraph mem (args.getD 0 0)
    p.initSpace (args.getD 1 0) (args.getD 2 0) G.n G.m (args.getD 3 0)
  pre i s args _ :=
    match i with
    | 0 =>
      ∃ b e h : ℕ,
        args = [b, e, h] ∧
        s.Valid p ∧
        e < s.G.m ∧
        e ∉ s.deleted ∧
        p.cw * (Nat.log 2 (s.G.n + s.G.m + s.phiDen + s.M +
          Nat.ceil (p.γ_ExpPath s.φ_in s.M) + 2) + 1) ≤ w
    | 1 =>
      ∃ b u v h : ℕ,
        args = [b, u, v, h] ∧
        s.Valid p ∧
        u ∈ s.G.verts \ s.Vhat ∧
        v ∈ s.G.verts \ s.Vhat ∧
        p.cw * (Nat.log 2 (s.G.n + s.G.m + s.phiDen + s.M +
          Nat.ceil (p.γ_ExpPath s.φ_in s.M) + 2) + 1) ≤ w
    | _ => False
  post i s args _ s' mem' :=
    match i with
    | 0 =>
      ∃ b e h : ℕ,
        args = [b, e, h] ∧
        s'.phiNum = s.phiNum ∧
        s'.phiDen = s.phiDen ∧
        s'.M = s.M ∧
        s'.G = s.G ∧
        s'.deleted = insert e s.deleted ∧
        s.Vhat ⊆ s'.Vhat ∧
        s'.Valid p ∧
        ∃ L : List ℕ, SeqAt mem' h L ∧ L.Nodup ∧ L.toFinset = s'.Vhat \ s.Vhat
    | 1 =>
      ∃ b u v h : ℕ,
        args = [b, u, v, h] ∧
        s' = s ∧
        ∃ P : Walk,
          WalkAt mem' h P ∧
          P.IsWalk s.G u v ∧
          P.verts.Nodup ∧
          (∀ e ∈ P.edges, e ∉ s.deleted) ∧
          (∀ x ∈ P.verts, x ∉ s.Vhat) ∧
          (P.edges.length : ℝ) ≤ p.γ_ExpPath s.φ_in s.M
    | _ => False
  cost i s _ _ :=
    match i with
    | 0 => Nat.ceil (p.K_del * p.γ_query s.φ_in s.M)
    | 1 => Nat.ceil (p.K_query * p.γ_query s.φ_in s.M)
    | _ => 0
  space i s _ _ :=
    match i with
    | 0 => p.delSpace s.phiNum s.phiDen s.G.n s.G.m s.M
    | 1 => p.querySpace s.phiNum s.phiDen s.G.n s.G.m s.M
    | _ => 0

/-- Deterministic Word-RAM contract for `boundsProc(d, M, h)` computing `[phiOutDen d M, gExp d M, gDel d M]`. -/
def pathDSBoundsContract (p : PathDSParams) (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ =>
      ∃ d M h : ℕ,
        args = [d, M, h] ∧
        1 ≤ d ∧
        p.cw * (Nat.log 2 (d + M + p.gExp d M + p.gDel d M + 2) + 1) ≤ w)
    (fun args _ mem' =>
      ∃ d M h : ℕ,
        args = [d, M, h] ∧
        ListAt mem' h [p.phiOutDen d M, p.gExp d M, p.gDel d M])
    (fun args _ => p.K_bounds * (Nat.log 2 (args.getD 0 0 + args.getD 1 0 + 2) + 1))
    (fun args _ => p.boundsSpace (args.getD 0 0) (args.getD 1 0))
  { C with post := fun args mem v mem' =>
      C.post args mem v mem' ∧ heapArg args + 3 ≤ v }

/-- Complete Word-RAM implementation witness for `PathDS`:
data structure (`init = b`, `op 0 = b + 1`, `op 1 = b + 2`) together with a deterministic
(`Stmt.NoRand`) parameter evaluator `boundsProcs` (`fn = bB`). -/
structure PathDSImpl where
  params : PathDSParams
  R : DSRep PathDSAbsState
  procs : ℕ → List Stmt
  hprocs_len : ∀ b, 3 ≤ (procs b).length
  spec : ∀ w (p : WordRAM.Program) b, p.HasAt b (procs b) →
    R.Implements w p b (fun i => b + 1 + i) (pathDSDataStructure params w)
  boundsProcs : ℕ → List Stmt
  hbounds_nonempty : ∀ b, 0 < (boundsProcs b).length
  hbounds_noRand : ∀ b, ∀ s ∈ boundsProcs b, s.NoRand
  boundsSpec : ∀ w (p : WordRAM.Program) b, p.HasAt b (boundsProcs b) →
    MeetsContract w p b (pathDSBoundsContract params w)

noncomputable def roundPhi (φ_in : ℝ) : ℝ :=
  1 / (Nat.ceil (1 / φ_in) : ℝ)

lemma roundPhi_pos {φ_in : ℝ} (hφ : 0 < φ_in) : 0 < roundPhi φ_in := by
  unfold roundPhi
  have h1 : 0 < 1 / φ_in := div_pos one_pos hφ
  have h2 : (1 : ℝ) ≤ (Nat.ceil (1 / φ_in) : ℝ) := by
    exact_mod_cast Nat.one_le_ceil_iff.mpr h1
  exact div_pos one_pos (by linarith)

lemma roundPhi_le {φ_in : ℝ} (hφ : 0 < φ_in) : roundPhi φ_in ≤ φ_in := by
  unfold roundPhi
  have hceil : 1 / φ_in ≤ (Nat.ceil (1 / φ_in) : ℝ) := Nat.le_ceil _
  have h1 : 0 < 1 / φ_in := div_pos one_pos hφ
  calc 1 / (Nat.ceil (1 / φ_in) : ℝ)
      ≤ 1 / (1 / φ_in) := one_div_le_one_div_of_le h1 hceil
    _ = φ_in := one_div_one_div φ_in

lemma roundPhi_le_one {φ_in : ℝ} (hφ : 0 < φ_in) : roundPhi φ_in ≤ 1 := by
  unfold roundPhi
  have h1 : (1 : ℝ) ≤ (Nat.ceil (1 / φ_in) : ℝ) := by
    exact_mod_cast Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ)
  exact div_le_one_of_le₀ h1 (by positivity)

lemma roundPhi_mono {φ₁ φ₂ : ℝ} (h1 : 0 < φ₁) (h12 : φ₁ ≤ φ₂) :
    roundPhi φ₁ ≤ roundPhi φ₂ := by
  unfold roundPhi
  have hinv : 1 / φ₂ ≤ 1 / φ₁ := one_div_le_one_div_of_le h1 h12
  have hceil : Nat.ceil (1 / φ₂) ≤ Nat.ceil (1 / φ₁) := Nat.ceil_mono hinv
  have hpos : (0 : ℝ) < (Nat.ceil (1 / φ₂) : ℝ) := by
    exact_mod_cast Nat.one_le_ceil_iff.mpr (div_pos one_pos (lt_of_lt_of_le h1 h12))
  exact one_div_le_one_div_of_le hpos (by exact_mod_cast hceil)

private lemma isConductanceExpanderOn_of_le {G : Cited.Graph} {X : Finset ℕ} {φ₁ φ₂ : ℝ}
    (h : φ₁ ≤ φ₂) (hexp : G.IsConductanceExpanderOn X φ₂) :
    G.IsConductanceExpanderOn X φ₁ := by
  intro S hS hneS hneqS
  have h2 := hexp S hS hneS hneqS
  have hmin_nn : 0 ≤ min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ) := by positivity
  exact le_trans (mul_le_mul_of_nonneg_right h hmin_nn) h2

/-- Live concrete Word-RAM state stored inside `pathDSTool_of_impl.State`. -/
structure RawLiveDSState (impl : PathDSImpl) where
  abs : PathDSAbsState
  w : ℕ
  b : ℕ
  hInit : ℕ
  h : ℕ
  mem : ℕ → ℕ
  x : impl.R.τ
  hval : abs.Valid impl.params
  hphi1 : abs.phiNum = 1
  hrep : impl.R.rep b abs x mem
  hzero : ZeroFrom mem h
  hfoot : ∀ a, impl.R.foot b x a → a < h
  hh_le : h ≤ hInit + impl.params.initSpace 1 abs.phiDen abs.G.n abs.G.m abs.M +
    abs.deleted.card * impl.params.delSpace 1 abs.phiDen abs.G.n abs.G.m abs.M
  hb_le : b ≤ h
  hw_heap : hInit + impl.params.initSpace 1 abs.phiDen abs.G.n abs.G.m abs.M +
    (abs.G.m + 1) * impl.params.delSpace 1 abs.phiDen abs.G.n abs.G.m abs.M +
    impl.params.querySpace 1 abs.phiDen abs.G.n abs.G.m abs.M + 2 ≤ w
  hw_vals : abs.G.n + abs.G.m + abs.phiDen + abs.M +
    Nat.ceil (impl.params.γ_ExpPath abs.φ_in abs.M) + 2 ≤ w
  hw_cw : impl.params.cw * (Nat.log 2 (abs.G.n + abs.G.m + abs.phiDen + abs.M +
    Nat.ceil (impl.params.γ_ExpPath abs.φ_in abs.M) + 2) + 1) ≤ w

lemma liveDS_init_exists (impl : PathDSImpl) (φ_in : ℝ) (M : ℕ) (G : Cited.Graph)
    (hφ_pos : 0 < φ_in) (_ : φ_in ≤ 1) (hG : G.IsValid)
    (hm_pos : 1 ≤ G.m) (hm_le : G.m ≤ M)
    (hdeg : ∀ v < G.n, 1 ≤ G.deg v)
    (hexp : G.IsConductanceExpanderOn G.verts φ_in) :
    ∃ st : RawLiveDSState impl,
      st.abs.G = G ∧ st.abs.M = M ∧ st.abs.phiDen = Nat.ceil (1 / φ_in) ∧
      st.abs.Vhat = ∅ ∧ st.abs.deleted = ∅ := by
  classical
  let phiDen : ℕ := Nat.ceil (1 / φ_in)
  have hphiDen_pos : 1 ≤ phiDen := Nat.one_le_ceil_iff.mpr (div_pos one_pos hφ_pos)
  have hround_eq : (1 : ℝ) / (phiDen : ℝ) = roundPhi φ_in := rfl
  have hexp_round : G.IsConductanceExpanderOn G.verts ((1 : ℝ) / (phiDen : ℝ)) :=
    isConductanceExpanderOn_of_le (hround_eq ▸ roundPhi_le hφ_pos) hexp
  let hInit := G.encode.length
  let mem₀ : ℕ → ℕ := fun i => G.encode.getD i 0
  let iSpace := impl.params.initSpace 1 phiDen G.n G.m M
  let dSpace := impl.params.delSpace 1 phiDen G.n G.m M
  let qSpace := impl.params.querySpace 1 phiDen G.n G.m M
  let γN := Nat.ceil (impl.params.γ_ExpPath ((1 : ℝ) / (phiDen : ℝ)) M)
  let w0 : ℕ := max
    (hInit + iSpace + (G.m + 1) * dSpace + qSpace + 2)
    (max (G.n + G.m + phiDen + M + γN + 2)
      (impl.params.cw * (Nat.log 2 (G.n + G.m + phiDen + M + γN + 2) + 1)))
  have hw_heap : hInit + iSpace + (G.m + 1) * dSpace + qSpace + 2 ≤ w0 := le_max_left _ _
  have hw_vals : G.n + G.m + phiDen + M + γN + 2 ≤ w0 := le_trans (le_max_left _ _) (le_max_right _ _)
  have hw_cw : impl.params.cw * (Nat.log 2 (G.n + G.m + phiDen + M + γN + 2) + 1) ≤ w0 :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hwords : ∀ a ∈ ([0, 1, phiDen, M, hInit] : List ℕ), a < 2 ^ w0 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact Nat.pow_pos (by decide)
    · exact nat_lt_two_pow_of_succ_le (by omega)
    · exact nat_lt_two_pow_of_succ_le (by omega)
    · exact nat_lt_two_pow_of_succ_le (by omega)
    · exact nat_lt_two_pow_of_succ_le (by omega)
  have hG0 : GraphAt mem₀ 0 G := listAt_getD
  have hRead0 : Cited.readGraph mem₀ 0 = G := graphAt_iff_readGraph.mp hG0
  let p₀ : Program := ⟨impl.procs 0⟩
  have hHas : p₀.HasAt 0 (impl.procs 0) := hasAt_mk_self _
  have hImpl := impl.spec w0 p₀ 0 hHas
  have hinitPre : (pathDSDataStructure impl.params w0).initPre [0, 1, phiDen, M, hInit] mem₀ :=
    ⟨0, 1, phiDen, M, hInit, G, rfl, by dsimp only [hInit]; omega, hG0, le_rfl, hphiDen_pos, hG,
      hm_pos, hm_le, hdeg, by simpa using hexp_round, by simpa [γN] using hw_cw⟩
  have hZero0 : ZeroFrom mem₀ hInit := zeroFrom_getD
  have hInitSpaceLt : hInit + (pathDSDataStructure impl.params w0).initSpace
      [0, 1, phiDen, M, hInit] mem₀ < 2 ^ w0 := by
    change hInit + impl.params.initSpace 1 phiDen (Cited.readGraph mem₀ 0).n
      (Cited.readGraph mem₀ 0).m M < 2 ^ w0
    rw [hRead0]
    exact nat_lt_two_pow_of_succ_le (by dsimp only [iSpace] at hw_heap; omega)
  obtain ⟨_, _, o, st', _, _, s', x', hrep', hinitPost', hresp', _⟩ :=
    hImpl.2.1 [0, 1, phiDen, M, hInit] mem₀ 0 (fun _ => false) hwords hinitPre hZero0 hInitSpaceLt
  rcases hinitPost' with ⟨gA, pn, pd, MM, hh, GG, heq, hGG, hspn, hspd, hsM, hsG, hsV, hsD, hsVal⟩
  simp only [List.cons.injEq, and_true] at heq
  rcases heq with ⟨ha1, ha2, ha3, ha4, ha5⟩
  have hGG_eq : GG = G := by
    have hr := graphAt_iff_readGraph.mp hGG
    rw [← ha1, hRead0] at hr
    exact hr.symm
  have hs_phiNum : s'.phiNum = 1 := by rw [hspn, ← ha2]
  have hs_phiDen : s'.phiDen = phiDen := by rw [hspd, ← ha3]
  have hs_M : s'.M = M := by rw [hsM, ← ha4]
  have hs_G : s'.G = G := hsG.trans hGG_eq
  have hφin_eq : s'.φ_in = (1 : ℝ) / (phiDen : ℝ) := by
    simp [PathDSAbsState.φ_in, hs_phiNum, hs_phiDen]
  rcases hresp' with ⟨hb_le', h_le, hzero', _, hfoot'⟩
  have h_le' : o.value ≤ hInit + iSpace + s'.deleted.card * dSpace := by
    have hsp_eq : (pathDSDataStructure impl.params w0).initSpace
        [0, 1, phiDen, M, hInit] mem₀ = iSpace := by
      change impl.params.initSpace 1 phiDen (Cited.readGraph mem₀ 0).n
        (Cited.readGraph mem₀ 0).m M = iSpace
      rw [hRead0]
    rw [hsp_eq] at h_le
    simp only [hsD, Finset.card_empty, Nat.zero_mul, Nat.add_zero]
    exact h_le
  refine ⟨{
    abs := s'
    w := w0
    b := hInit
    hInit := hInit
    h := o.value
    mem := st'.mem
    x := x'
    hval := hsVal
    hphi1 := hs_phiNum
    hrep := hrep'
    hzero := hzero'
    hfoot := fun a ha => by
      rcases hfoot' a ha with hfalse | ⟨_, halt⟩
      · exact False.elim hfalse
      · exact halt
    hh_le := by simpa [hs_phiDen, hs_M, hs_G] using h_le'
    hb_le := hb_le'
    hw_heap := by simpa [hs_phiDen, hs_M, hs_G] using hw_heap
    hw_vals := by simpa [hs_phiDen, hs_M, hs_G, hφin_eq, γN] using hw_vals
    hw_cw := by simpa [hs_phiDen, hs_M, hs_G, hφin_eq, γN] using hw_cw },
    hs_G, hs_M, hs_phiDen, hsV, hsD⟩

lemma liveDS_delete_exists (impl : PathDSImpl) (st : RawLiveDSState impl) (e : ℕ)
    (he_m : e < st.abs.G.m) (he_not : e ∉ st.abs.deleted) :
    ∃ st' : RawLiveDSState impl,
      st'.abs.G = st.abs.G ∧ st'.abs.M = st.abs.M ∧ st'.abs.phiDen = st.abs.phiDen ∧
      st'.abs.deleted = insert e st.abs.deleted ∧
      st.abs.Vhat ⊆ st'.abs.Vhat ∧ st'.abs.Vhat ⊆ st.abs.G.verts := by
  classical
  let p₀ : Program := ⟨impl.procs 0⟩
  have hHas : p₀.HasAt 0 (impl.procs 0) := hasAt_mk_self _
  have hImpl := impl.spec st.w p₀ 0 hHas
  have hcard_le : st.abs.deleted.card ≤ st.abs.G.m := by
    have := Finset.card_le_card st.hval.2.2.2.2.2.2.2.2.1
    simpa using this
  let iSpace := impl.params.initSpace 1 st.abs.phiDen st.abs.G.n st.abs.G.m st.abs.M
  let dSpace := impl.params.delSpace 1 st.abs.phiDen st.abs.G.n st.abs.G.m st.abs.M
  have hmul_card : st.abs.deleted.card * dSpace ≤ st.abs.G.m * dSpace :=
    Nat.mul_le_mul_right dSpace hcard_le
  have hh_lt : st.h < 2 ^ st.w := by
    have hsucc : st.h + 1 ≤ st.w := by
      have hh := st.hh_le
      have hwh := st.hw_heap
      have hd_le : st.abs.G.m * dSpace ≤ (st.abs.G.m + 1) * dSpace :=
        Nat.mul_le_mul_right dSpace (Nat.le_succ _)
      dsimp only [iSpace, dSpace] at hmul_card hd_le
      omega
    exact nat_lt_two_pow_of_succ_le hsucc
  have hb_lt : st.b < 2 ^ st.w := lt_of_le_of_lt st.hb_le hh_lt
  have he_lt : e < 2 ^ st.w :=
    nat_lt_two_pow_of_succ_le (by have := st.hw_vals; omega)
  have hwords : ∀ a ∈ ([st.b, e, st.h] : List ℕ), a < 2 ^ st.w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact hb_lt
    · exact he_lt
    · exact hh_lt
  have hpre : (pathDSDataStructure impl.params st.w).pre 0 st.abs [st.b, e, st.h] st.mem :=
    ⟨st.b, e, st.h, rfl, st.hval, he_m, he_not, st.hw_cw⟩
  have hSpaceLt : st.h + (pathDSDataStructure impl.params st.w).space
      0 st.abs [st.b, e, st.h] st.mem < 2 ^ st.w := by
    change st.h + impl.params.delSpace st.abs.phiNum st.abs.phiDen st.abs.G.n st.abs.G.m st.abs.M <
      2 ^ st.w
    rw [st.hphi1]
    have hsum_le : st.h + dSpace + 1 ≤ st.w := by
      have hh := st.hh_le
      have hwh := st.hw_heap
      have : (st.abs.deleted.card + 1) * dSpace ≤ (st.abs.G.m + 1) * dSpace :=
        Nat.mul_le_mul_right dSpace (Nat.add_le_add_right hcard_le 1)
      have hadd : st.abs.deleted.card * dSpace + dSpace = (st.abs.deleted.card + 1) * dSpace := by
        ring
      dsimp only [iSpace, dSpace] at this hadd
      omega
    exact nat_lt_two_pow_of_succ_le hsum_le
  obtain ⟨_, _, o, st', _, _, s', x', hrep', hpost', hresp', _⟩ :=
    hImpl.2.2 0 st.b st.abs st.x [st.b, e, st.h] st.mem 0 (fun _ => false) hwords
      rfl st.hrep hpre st.hfoot st.hzero hSpaceLt
  rcases hpost' with ⟨b', e', h', heq, hspn, hspd, hsM, hsG, hsdel, hVsub, hsVal, _⟩
  simp only [List.cons.injEq, and_true] at heq
  rcases heq with ⟨hb_eq, he_eq, hh_eq⟩
  have hφ_eq : s'.phiNum = 1 := by rw [hspn, st.hphi1]
  have h_del_eq : s'.deleted = insert e st.abs.deleted := by rw [hsdel, ← he_eq]
  have hcard_ins : s'.deleted.card = st.abs.deleted.card + 1 := by
    rw [h_del_eq, Finset.card_insert_of_notMem he_not]
  rcases hresp' with ⟨hle_h, h_le, hzero', _, hfoot'⟩
  have h_le' : o.value ≤ st.hInit + iSpace + s'.deleted.card * dSpace := by
    have hsp_eq : (pathDSDataStructure impl.params st.w).space 0 st.abs [st.b, e, st.h] st.mem =
        dSpace := by
      change impl.params.delSpace st.abs.phiNum st.abs.phiDen st.abs.G.n st.abs.G.m st.abs.M = _
      rw [st.hphi1]
    rw [hsp_eq] at h_le
    simp only [heapArg, List.getLastD_cons, List.getLastD_nil] at h_le
    have hmul_eq : s'.deleted.card * dSpace = st.abs.deleted.card * dSpace + dSpace := by
      rw [hcard_ins]; ring
    have hh := st.hh_le
    dsimp only [iSpace, dSpace] at hh h_le hmul_eq ⊢
    omega
  refine ⟨{
    abs := s'
    w := st.w
    b := st.b
    hInit := st.hInit
    h := o.value
    mem := st'.mem
    x := x'
    hval := hsVal
    hphi1 := hφ_eq
    hrep := hrep'
    hzero := hzero'
    hfoot := fun a ha => by
      rcases hfoot' a ha with hold | ⟨_, halt⟩
      · exact lt_of_lt_of_le (st.hfoot a hold) hle_h
      · exact halt
    hh_le := by simpa [hspd, hsM, hsG, iSpace, dSpace] using h_le'
    hb_le := le_trans st.hb_le hle_h
    hw_heap := by simpa [hspd, hsM, hsG] using st.hw_heap
    hw_vals := by
      have hφin : s'.φ_in = st.abs.φ_in := by
        simp [PathDSAbsState.φ_in, hspn, hspd]
      simpa [hspd, hsM, hsG, hφin] using st.hw_vals
    hw_cw := by
      have hφin : s'.φ_in = st.abs.φ_in := by
        simp [PathDSAbsState.φ_in, hspn, hspd]
      simpa [hspd, hsM, hsG, hφin] using st.hw_cw },
    hsG, hsM, hspd, h_del_eq, hVsub, hsG ▸ hsVal.2.2.2.2.2.2.2.1⟩

lemma liveDS_getPath_exists (impl : PathDSImpl) (st : RawLiveDSState impl) (u v : ℕ)
    (hu : u ∈ st.abs.G.verts \ st.abs.Vhat) (hv : v ∈ st.abs.G.verts \ st.abs.Vhat) :
    ∃ P : Walk,
      P.IsWalk st.abs.G u v ∧ P.verts.Nodup ∧
      (∀ e ∈ P.edges, e ∉ st.abs.deleted) ∧
      (∀ x ∈ P.verts, x ∉ st.abs.Vhat) ∧
      (P.edges.length : ℝ) ≤ impl.params.γ_ExpPath st.abs.φ_in st.abs.M := by
  classical
  let p₀ : Program := ⟨impl.procs 0⟩
  have hHas : p₀.HasAt 0 (impl.procs 0) := hasAt_mk_self _
  have hImpl := impl.spec st.w p₀ 0 hHas
  have hcard_le : st.abs.deleted.card ≤ st.abs.G.m := by
    have := Finset.card_le_card st.hval.2.2.2.2.2.2.2.2.1
    simpa using this
  have hh_lt : st.h < 2 ^ st.w := by
    have hsucc : st.h + 1 ≤ st.w := by
      have hh := st.hh_le
      have hwh := st.hw_heap
      have hm1 : st.abs.deleted.card *
          impl.params.delSpace 1 st.abs.phiDen st.abs.G.n st.abs.G.m st.abs.M ≤
          (st.abs.G.m + 1) *
            impl.params.delSpace 1 st.abs.phiDen st.abs.G.n st.abs.G.m st.abs.M :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    exact nat_lt_two_pow_of_succ_le hsucc
  have hu_n : u < st.abs.G.n := Finset.mem_range.mp (Finset.mem_sdiff.mp hu).1
  have hv_n : v < st.abs.G.n := Finset.mem_range.mp (Finset.mem_sdiff.mp hv).1
  have hu_lt : u < 2 ^ st.w :=
    nat_lt_two_pow_of_succ_le (by have := st.hw_vals; omega)
  have hv_lt : v < 2 ^ st.w :=
    nat_lt_two_pow_of_succ_le (by have := st.hw_vals; omega)
  have hb_lt : st.b < 2 ^ st.w := lt_of_le_of_lt st.hb_le hh_lt
  have hwords : ∀ a ∈ ([st.b, u, v, st.h] : List ℕ), a < 2 ^ st.w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hpre : (pathDSDataStructure impl.params st.w).pre 1 st.abs [st.b, u, v, st.h] st.mem :=
    ⟨st.b, u, v, st.h, rfl, st.hval, hu, hv, st.hw_cw⟩
  have hSpaceLt : st.h + (pathDSDataStructure impl.params st.w).space
      1 st.abs [st.b, u, v, st.h] st.mem < 2 ^ st.w := by
    change st.h + impl.params.querySpace st.abs.phiNum st.abs.phiDen st.abs.G.n st.abs.G.m st.abs.M <
      2 ^ st.w
    rw [st.hphi1]
    have hsum_le : st.h + impl.params.querySpace 1 st.abs.phiDen st.abs.G.n st.abs.G.m st.abs.M + 1 ≤
        st.w := by
      have hh := st.hh_le
      have hwh := st.hw_heap
      have : st.abs.deleted.card * impl.params.delSpace 1 st.abs.phiDen st.abs.G.n st.abs.G.m st.abs.M ≤
          (st.abs.G.m + 1) * impl.params.delSpace 1 st.abs.phiDen st.abs.G.n st.abs.G.m st.abs.M :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    exact nat_lt_two_pow_of_succ_le hsum_le
  obtain ⟨_, _, _, _, _, _, _, _, _, hpost', _, _⟩ :=
    hImpl.2.2 1 st.b st.abs st.x [st.b, u, v, st.h] st.mem 0 (fun _ => false) hwords
      rfl st.hrep hpre st.hfoot st.hzero hSpaceLt
  rcases hpost' with ⟨b', u', v', h', heq, _, P, _, hPw, hPn, hPdel, hPv, hPlen⟩
  simp only [List.cons.injEq, and_true] at heq
  rcases heq with ⟨_, hu_eq, hv_eq, _⟩
  rw [← hu_eq, ← hv_eq] at hPw
  exact ⟨P, hPw, hPn, hPdel, hPv, hPlen⟩

open Classical in
noncomputable def liveInit (impl : PathDSImpl) (φ_in : ℝ) (M : ℕ) (G : Cited.Graph) :
    Option (RawLiveDSState impl) :=
  if h : 0 < φ_in ∧ φ_in ≤ 1 ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
      (∀ v < G.n, 1 ≤ G.deg v) ∧ G.IsConductanceExpanderOn G.verts φ_in
  then some (Classical.choose (liveDS_init_exists impl φ_in M G
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2))
  else none

open Classical in
noncomputable def liveDelete (impl : PathDSImpl) (s : Option (RawLiveDSState impl))
    (e : ℕ) : Option (RawLiveDSState impl) × Finset ℕ :=
  match s with
  | none => (none, ∅)
  | some st =>
    if h : e < st.abs.G.m ∧ e ∉ st.abs.deleted
    then
      let st' := Classical.choose (liveDS_delete_exists impl st e h.1 h.2)
      (some st', st'.abs.Vhat \ st.abs.Vhat)
    else (some st, ∅)

open Classical in
noncomputable def liveGetPath (impl : PathDSImpl) (s : Option (RawLiveDSState impl))
    (u v : ℕ) : Walk :=
  match s with
  | none => Walk.empty
  | some st =>
    if h : u ∈ st.abs.G.verts \ st.abs.Vhat ∧ v ∈ st.abs.G.verts \ st.abs.Vhat
    then Classical.choose (liveDS_getPath_exists impl st u v h.1 h.2)
    else Walk.empty

/-- Converts a `PathDSImpl` into a mathematical `PathDSTool` (`Tools.lean`) via
`φ_in ↦ 1 / ⌈1 / φ_in⌉₊`. -/
noncomputable def pathDSTool_of_impl (impl : PathDSImpl) : PathDSTool where
  State := Option (RawLiveDSState impl)
  φ_out φ_in M := impl.params.φ_out (roundPhi φ_in) M
  γ_ExpPath φ_in M := impl.params.γ_ExpPath (roundPhi φ_in) M
  γ_query φ_in M := impl.params.γ_query (roundPhi φ_in) M
  γ_del φ_in M := impl.params.γ_del (roundPhi φ_in) M
  init φ_in M G := liveInit impl φ_in M G
  Vhat s := match s with | none => ∅ | some st => st.abs.Vhat
  deleted s := match s with | none => ∅ | some st => st.abs.deleted
  delete s e := liveDelete impl s e
  getPath s u v := liveGetPath impl s u v
  Inv φ_in M G s :=
    ∃ st, s = some st ∧ st.abs.G = G ∧ st.abs.M = M ∧ st.abs.phiDen = Nat.ceil (1 / φ_in)
  hφ_pos φ_in M hφ := impl.params.hφ_out_pos (roundPhi φ_in) M (roundPhi_pos hφ)
  hφ_le φ_in M hφ :=
    le_trans (impl.params.hφ_out_le _ M (roundPhi_pos hφ)) (roundPhi_le hφ)
  hφ_half φ_in M hφ := impl.params.hφ_out_half _ M (roundPhi_pos hφ)
  hγ_ExpPath_ge φ_in M hφ := impl.params.hγ_ExpPath_ge (roundPhi φ_in) M (roundPhi_pos hφ)
  hγ_query_ge φ_in M hφ := impl.params.hγ_query_ge (roundPhi φ_in) M (roundPhi_pos hφ)
  hγ_del_ge φ_in M hφ := impl.params.hγ_del_ge (roundPhi φ_in) M (roundPhi_pos hφ)
  init_inv φ_in M G hφ hle hG hm_pos hm_le hdeg hexp := by
    classical
    have hcond : 0 < φ_in ∧ φ_in ≤ 1 ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
        (∀ v < G.n, 1 ≤ G.deg v) ∧ G.IsConductanceExpanderOn G.verts φ_in :=
      ⟨hφ, hle, hG, hm_pos, hm_le, hdeg, hexp⟩
    dsimp only [liveInit]
    split_ifs
    have hsp := Classical.choose_spec (liveDS_init_exists impl φ_in M G hφ hle hG hm_pos hm_le hdeg hexp)
    exact ⟨_, rfl, hsp.1, hsp.2.1, hsp.2.2.1⟩
  init_Vhat φ_in M G hφ hle hG hm_pos hm_le hdeg hexp := by
    classical
    have hcond : 0 < φ_in ∧ φ_in ≤ 1 ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
        (∀ v < G.n, 1 ≤ G.deg v) ∧ G.IsConductanceExpanderOn G.verts φ_in :=
      ⟨hφ, hle, hG, hm_pos, hm_le, hdeg, hexp⟩
    dsimp only [liveInit]
    split_ifs
    exact (Classical.choose_spec (liveDS_init_exists impl φ_in M G hφ hle hG hm_pos hm_le hdeg hexp)).2.2.2.1
  init_deleted φ_in M G hφ hle hG hm_pos hm_le hdeg hexp := by
    classical
    have hcond : 0 < φ_in ∧ φ_in ≤ 1 ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
        (∀ v < G.n, 1 ≤ G.deg v) ∧ G.IsConductanceExpanderOn G.verts φ_in :=
      ⟨hφ, hle, hG, hm_pos, hm_le, hdeg, hexp⟩
    dsimp only [liveInit]
    split_ifs
    exact (Classical.choose_spec (liveDS_init_exists impl φ_in M G hφ hle hG hm_pos hm_le hdeg hexp)).2.2.2.2
  delete_spec φ_in M G s e _ _ _ _ _ _ _ hinv he_m he_not := by
    classical
    rcases hinv with ⟨st, rfl, hstG, hstM, hstDen⟩
    have he' : e < st.abs.G.m ∧ e ∉ st.abs.deleted := ⟨hstG ▸ he_m, he_not⟩
    dsimp only [liveDelete]
    split_ifs
    set st' := Classical.choose (liveDS_delete_exists impl st e he'.1 he'.2)
    have hsp := Classical.choose_spec (liveDS_delete_exists impl st e he'.1 he'.2)
    have hst'G : st'.abs.G = G := hsp.1.trans hstG
    have hst'M : st'.abs.M = M := hsp.2.1.trans hstM
    have hst'Den : st'.abs.phiDen = Nat.ceil (1 / φ_in) := hsp.2.2.1.trans hstDen
    have hvol := st'.hval.2.2.2.2.2.2.2.2.2
    have hφin_eq : st'.abs.φ_in = roundPhi φ_in := by
      simp [PathDSAbsState.φ_in, st'.hphi1, hst'Den, roundPhi]
    rw [hst'G, hst'M, hφin_eq] at hvol
    exact ⟨⟨st', rfl, hst'G, hst'M, hst'Den⟩, hsp.2.2.2.1, hsp.2.2.2.2.1,
      hstG ▸ hsp.2.2.2.2.2, rfl, hvol⟩
  getPath_spec φ_in M G s u v _ _ _ _ _ _ _ hinv hu hv := by
    classical
    rcases hinv with ⟨st, rfl, hstG, hstM, hstDen⟩
    have huv : u ∈ st.abs.G.verts \ st.abs.Vhat ∧ v ∈ st.abs.G.verts \ st.abs.Vhat := by
      rw [hstG]; exact ⟨hu, hv⟩
    dsimp only [liveGetPath]
    split_ifs
    have hsp := Classical.choose_spec (liveDS_getPath_exists impl st u v huv.1 huv.2)
    have hφin_eq : st.abs.φ_in = roundPhi φ_in := by
      simp [PathDSAbsState.φ_in, st.hphi1, hstDen, roundPhi]
    exact ⟨hstG ▸ hsp.1, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1,
      by rw [← hφin_eq, ← hstM]; exact hsp.2.2.2.2⟩

/-- Extracts `PathDSMonotone` from `PathDSImpl`. -/
theorem pathDSMonotone_of_impl (impl : PathDSImpl) :
    PathDSMonotone (pathDSTool_of_impl impl) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro φ₁ φ₂ M₁ M₂ h1 h12 h2 hM
    exact impl.params.hφ_out_mono (roundPhi_pos h1) (roundPhi_mono h1 h12)
      (le_trans (roundPhi_le (lt_of_lt_of_le h1 h12)) h2) hM
  · intro φ₁ φ₂ M₁ M₂ h1 h12 h2 hM
    exact impl.params.hγ_ExpPath_mono (roundPhi_pos h1) (roundPhi_mono h1 h12)
      (le_trans (roundPhi_le (lt_of_lt_of_le h1 h12)) h2) hM
  · intro φ₁ φ₂ M₁ M₂ h1 h12 h2 hM
    exact impl.params.hγ_query_mono (roundPhi_pos h1) (roundPhi_mono h1 h12)
      (le_trans (roundPhi_le (lt_of_lt_of_le h1 h12)) h2) hM
  · intro φ₁ φ₂ M₁ M₂ h1 h12 h2 hM
    exact impl.params.hγ_del_mono (roundPhi_pos h1) (roundPhi_mono h1 h12)
      (le_trans (roundPhi_le (lt_of_lt_of_le h1 h12)) h2) hM

/-- Extracts `PathDSCost` from `PathDSImpl` (`K_dsUpdate = K_init + K_del + 2`, `K_dsQuery = K_query`). -/
noncomputable def pathDSCost_of_impl (impl : PathDSImpl) : PathDSCost where
  K_dsUpdate := impl.params.K_init + impl.params.K_del + 2
  K_dsQuery := impl.params.K_query
  hK_dsUpdate := by linarith [impl.params.hK_init, impl.params.hK_del]
  hK_dsQuery := impl.params.hK_query

/-- The initialization charge and `t ≤ m` deletion charges of `pathDSDataStructure` together fit
in `PathDSCost.updateCost m γ_query`: initialization is charged with `γ_ExpPath ≤ γ_query`. -/
theorem pathDS_init_del_cost_le (impl : PathDSImpl) {φ_in : ℝ} {M m t : ℕ}
    (hφ : 0 < φ_in) (hm : 1 ≤ m) (ht : t ≤ m) :
    Nat.ceil (impl.params.K_init * (m : ℝ) * impl.params.γ_ExpPath (roundPhi φ_in) M) +
      t * Nat.ceil (impl.params.K_del * impl.params.γ_query (roundPhi φ_in) M) ≤
      (pathDSCost_of_impl impl).updateCost m
        ((pathDSTool_of_impl impl).γ_query φ_in M) := by
  apply nat_le_ceil_of_cast_le
  set γE := impl.params.γ_ExpPath (roundPhi φ_in) M
  set γ := impl.params.γ_query (roundPhi φ_in) M
  have h1_le_γE : 1 ≤ γE := impl.params.one_le_γ_ExpPath _ M (roundPhi_pos hφ)
  have hγE_le : γE ≤ γ := impl.params.hγ_query_ge _ M (roundPhi_pos hφ)
  have h1_le_γ : 1 ≤ γ := le_trans h1_le_γE hγE_le
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have ht_le : (t : ℝ) ≤ (m : ℝ) := by exact_mod_cast ht
  have hKi : 0 ≤ impl.params.K_init := impl.params.hK_init
  have hKd : 0 ≤ impl.params.K_del := impl.params.hK_del
  have hnn_i : 0 ≤ impl.params.K_init * (m : ℝ) * γE := by positivity
  have hnn_d : 0 ≤ impl.params.K_del * γ := by positivity
  have hc_i : (Nat.ceil (impl.params.K_init * (m : ℝ) * γE) : ℝ) ≤
      impl.params.K_init * (m : ℝ) * γE + 1 := (Nat.ceil_lt_add_one hnn_i).le
  have hc_d : (Nat.ceil (impl.params.K_del * γ) : ℝ) ≤
      impl.params.K_del * γ + 1 := (Nat.ceil_lt_add_one hnn_d).le
  have hiE : impl.params.K_init * (m : ℝ) * γE ≤ impl.params.K_init * (m : ℝ) * γ :=
    mul_le_mul_of_nonneg_left hγE_le (by positivity)
  have h1_le_mγ : 1 ≤ (m : ℝ) * γ := by nlinarith
  have hm_le_mγ : (m : ℝ) ≤ (m : ℝ) * γ := le_mul_of_one_le_right (Nat.cast_nonneg m) h1_le_γ
  have hm_add : (m : ℝ) * (impl.params.K_del * γ + 1) ≤
      (m : ℝ) * (impl.params.K_del * γ) + (m : ℝ) * γ := by
    rw [mul_add, mul_one]
    linarith
  dsimp only [pathDSCost_of_impl, pathDSTool_of_impl]
  push_cast
  calc (Nat.ceil (impl.params.K_init * (m : ℝ) * γE) : ℝ) +
        (t : ℝ) * (Nat.ceil (impl.params.K_del * γ) : ℝ)
      ≤ (impl.params.K_init * (m : ℝ) * γE + 1) + (m : ℝ) * (impl.params.K_del * γ + 1) := by
          gcongr
    _ ≤ (impl.params.K_init * (m : ℝ) * γ + (m : ℝ) * γ) +
          ((m : ℝ) * (impl.params.K_del * γ) + (m : ℝ) * γ) := by
          linarith
    _ = (impl.params.K_init + impl.params.K_del + 2) * (m : ℝ) * γ := by ring

/-- The `GetPath` charge of `pathDSDataStructure` is `PathDSCost.queryCost γ_query`. -/
theorem pathDS_query_cost_le (impl : PathDSImpl) (φ_in : ℝ) (M : ℕ) :
    Nat.ceil (impl.params.K_query * impl.params.γ_query (roundPhi φ_in) M) ≤
      (pathDSCost_of_impl impl).queryCost ((pathDSTool_of_impl impl).γ_query φ_in M) :=
  le_rfl

end MinCostFlow.Spanner
