module

public import MinCostFlow.Statement.Cited.ChuzhoySaranurak
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Expander.PathDSBounds
public import MinCostFlow.Expander.PathDSProg.FallbackCost
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public import MinCostFlow.Expander.DecrementalPaths
public import MinCostFlow.Expander.FallbackPruning
public import MinCostFlow.Expander.GraphHelpers
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 8.6 as a `PathDSTool`: Parameters and the `[CS21]` Steps

This file holds the first part of the material of `PathDS.lean`, split off to keep files small:
the parameters of the tool, the abstract state, and the initialization and deletion steps in
`[CS21]` mode. `PathDS.lean` gives the overview.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner WordRAM

@[expose] public section

/-- Effective conductance `φ_out` for `PathDSTool`: `min φ_in (min (1/2) (csPhi Kγ c (3*M)))`. -/
noncomputable def csPhiOut (Kγ c : ℕ) (φ_in : ℝ) (M : ℕ) : ℝ :=
  min φ_in (min (1 / 2 : ℝ) (Cited.csPhi Kγ c (3 * M)))

/-- Path length bound `γ_ExpPath` for `PathDSTool`. -/
noncomputable def csGammaExpPath (Kγ c : ℕ) (K : ℝ) (φ_in : ℝ) (M : ℕ) : ℝ :=
  max ((Cited.csGamma Kγ (3 * M) : ℝ) ^ (max K 1 * (qOf M : ℝ)))
    (25 * (Real.log (2 * (M : ℝ) + 2) + 1) / csPhiOut Kγ c φ_in M)

/-- Time bound `γ_query` of one `Delete` or `GetPath` for `PathDSTool`: the path length bound
`csGammaExpPath` plus the time `fbCostBound ⌈1 / φ_in⌉` of the fallback, which prunes and searches
clusters below the conductance of [CS21]. -/
noncomputable def csGammaQuery (Kγ c : ℕ) (K : ℝ) (φ_in : ℝ) (M : ℕ) : ℝ :=
  csGammaExpPath Kγ c K φ_in M + (PathDSProg.fbCostBound (Nat.ceil (1 / φ_in)) : ℝ)

/-- Volume deletion factor `γ_del` for `PathDSTool`. -/
noncomputable def csGammaDel (K : ℝ) : ℝ :=
  max (max K 1) 7

end

@[expose] public section

lemma csPhi_pos (Kγ c m : ℕ) (hc : 1 ≤ c) : 0 < Cited.csPhi Kγ c m := by
  unfold Cited.csPhi Cited.csGamma
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  positivity

lemma csPhiOut_pos (Kγ c : ℕ) (hc : 1 ≤ c) {φ_in : ℝ} (hφ : 0 < φ_in) (M : ℕ) :
    0 < csPhiOut Kγ c φ_in M := by
  dsimp only [csPhiOut]
  exact lt_min hφ (lt_min (by norm_num) (csPhi_pos Kγ c (3 * M) hc))

lemma csPhiOut_le_csPhi_m {Kγ c : ℕ} (hc : 1 ≤ c) (φ_in : ℝ) {m M : ℕ} (hmM : m ≤ M) :
    csPhiOut Kγ c φ_in M ≤ Cited.csPhi Kγ c (3 * m) := by
  dsimp only [csPhiOut]
  exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (csPhi_anti_m hc (by omega : 3 * m ≤ 3 * M)))

def csProgram (mk : ℕ → List Stmt) : Program :=
  ⟨mk 0⟩

lemma csProgram_hasAt (mk : ℕ → List Stmt) : (csProgram mk).HasAt 0 (mk 0) := by
  intro i hi
  simp [csProgram, hi]

lemma flatMap_pairs_getD_even (es : List (ℕ × ℕ)) :
    ∀ j < es.length, (es.flatMap fun e => [e.1, e.2]).getD (2 * j) 0 = (es.getD j (0, 0)).1 := by
  induction es with
  | nil => intro j hj; simp at hj
  | cons p ps ih =>
    intro j hj
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.length_cons] at hj
      have h2 : 2 * (j' + 1) = (2 * j') + 2 := by omega
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, h2,
        List.getD_cons_succ]
      exact ih j' (by omega)

lemma flatMap_pairs_getD_odd (es : List (ℕ × ℕ)) :
    ∀ j < es.length, (es.flatMap fun e => [e.1, e.2]).getD (2 * j + 1) 0 = (es.getD j (0, 0)).2 := by
  induction es with
  | nil => intro j hj; simp at hj
  | cons p ps ih =>
    intro j hj
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.length_cons] at hj
      have h2 : 2 * (j' + 1) + 1 = (2 * j' + 1) + 2 := by omega
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, h2,
        List.getD_cons_succ]
      exact ih j' (by omega)

private lemma edges_eq_map_range (L : List (ℕ × ℕ)) :
    ((List.range L.length).map fun j => L.getD j (0, 0)) = L := by
  induction L with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getD_cons_zero]
    congr 1

lemma readGraph_initMem_zero (G : Cited.Graph) :
    Cited.readGraph (WordRAM.initMem G.encode) 0 = G := by
  unfold Cited.readGraph WordRAM.initMem Cited.Graph.encode
  have hn : (G.n :: G.m :: G.edges.flatMap fun e => [e.1, e.2]).getD 0 0 = G.n := rfl
  have hm : (G.n :: G.m :: G.edges.flatMap fun e => [e.1, e.2]).getD (0 + 1) 0 = G.m := rfl
  have hedges : ((List.range G.m).map fun j =>
      ((G.n :: G.m :: G.edges.flatMap fun e => [e.1, e.2]).getD (0 + 2 + 2 * j) 0,
       (G.n :: G.m :: G.edges.flatMap fun e => [e.1, e.2]).getD (0 + 3 + 2 * j) 0)) =
      G.edges := by
    have hcon : ((List.range G.m).map fun j =>
        ((G.n :: G.m :: G.edges.flatMap fun e => [e.1, e.2]).getD (0 + 2 + 2 * j) 0,
         (G.n :: G.m :: G.edges.flatMap fun e => [e.1, e.2]).getD (0 + 3 + 2 * j) 0)) =
        ((List.range G.m).map fun j => G.edges.getD j (0, 0)) := by
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      have ha1 : 0 + 2 + 2 * j = (2 * j) + 2 := by omega
      have ha2 : 0 + 3 + 2 * j = (2 * j + 1) + 2 := by omega
      rw [ha1, ha2]
      simp only [List.getD_cons_succ]
      exact Prod.ext (flatMap_pairs_getD_even G.edges j hj) (flatMap_pairs_getD_odd G.edges j hj)
    rw [hcon]
    exact edges_eq_map_range G.edges
  rw [hn, hm, hedges]

lemma zeroFrom_initMem (l : List ℕ) : WordRAM.ZeroFrom (WordRAM.initMem l) l.length := by
  intro a ha
  unfold WordRAM.initMem
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ha]
  rfl

noncomputable def csWordSize (Kγ cw : ℕ) (K : ℝ) (M : ℕ) (G : Cited.Graph) : ℕ :=
  let G_s := subdivGraph G
  let H_bound := G_s.encode.length + (G.m + 2) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) +
    Cited.csQuery Kγ K G_s.m (qOf M) + G_s.n + 3 * G.m + qOf M + 4
  max (cw * (Nat.log 2 (G_s.n + G_s.m + 2) + 1)) (Nat.log 2 H_bound + 1)

lemma lt_two_pow_csWordSize (Kγ cw : ℕ) (K : ℝ) (M : ℕ) (G : Cited.Graph) :
    (subdivGraph G).encode.length +
      (G.m + 2) * Cited.csTotal Kγ K (subdivGraph G).n (subdivGraph G).m (qOf M) +
      Cited.csQuery Kγ K (subdivGraph G).m (qOf M) + (subdivGraph G).n + 3 * G.m + qOf M + 4 <
      2 ^ csWordSize Kγ cw K M G := by
  dsimp only [csWordSize]
  set G_s := subdivGraph G
  set H_bound := G_s.encode.length + (G.m + 2) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) +
    Cited.csQuery Kγ K G_s.m (qOf M) + G_s.n + 3 * G.m + qOf M + 4
  have h1 : H_bound < 2 ^ (Nat.log 2 H_bound + 1) := Nat.lt_pow_succ_log_self (by norm_num) H_bound
  have h2 : 2 ^ (Nat.log 2 H_bound + 1) ≤
      2 ^ max (cw * (Nat.log 2 (G_s.n + G_s.m + 2) + 1)) (Nat.log 2 H_bound + 1) :=
    Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  exact lt_of_lt_of_le h1 h2

lemma csWordSize_ge_cw (Kγ cw : ℕ) (K : ℝ) (M : ℕ) (G : Cited.Graph) :
    cw * (Nat.log 2 ((subdivGraph G).n + (subdivGraph G).m + 2) + 1) ≤ csWordSize Kγ cw K M G :=
  le_max_left _ _

inductive PDSState (τ : Type) : Type
  | cs (φ_in : ℝ) (M : ℕ) (G : Cited.Graph) (w h₀ h : ℕ)
      (s : Cited.PrunedExpander) (x : τ) (mem : ℕ → ℕ)
      (delList : List ℕ) (overBudget : Bool) (VhatSet : Finset ℕ) : PDSState τ
  | fb (φ_in : ℝ) (M : ℕ) (G : Cited.Graph) (del S : Finset ℕ) : PDSState τ

def pdsVhat {τ : Type} : PDSState τ → Finset ℕ
  | .cs _ _ _ _ _ _ _ _ _ _ _ VhatSet => VhatSet
  | .fb _ _ _ _ S => S

def pdsDeleted {τ : Type} : PDSState τ → Finset ℕ
  | .cs _ _ _ _ _ _ _ _ _ delList _ _ => delList.toFinset
  | .fb _ _ _ del _ => del

def CSStateInv (Kγ c : ℕ) (K : ℝ) (cw : ℕ) (R : DSRep Cited.PrunedExpander)
    (φ_in : ℝ) (M : ℕ) (G : Cited.Graph) :
    ℕ → ℕ → ℕ → Cited.PrunedExpander → R.τ → (ℕ → ℕ) → List ℕ → Bool → Finset ℕ → Prop
  | w, h₀, h, s, x, mem, delList, overBudget, VhatSet =>
    0 < φ_in ∧ G.IsValid ∧ 1 ≤ G.m ∧ G.m ≤ M ∧
    10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in ∧
    s.G = subdivGraph G ∧
    s.q = qOf M ∧
    delList.Nodup ∧
    (∀ j ∈ delList, j < G.m) ∧
    w = csWordSize Kγ cw K M G ∧
    h₀ = (subdivGraph G).encode.length ∧
    WordRAM.ZeroFrom mem h ∧
    (∀ a, R.foot h₀ x a → a < h) ∧
    h ≤ h₀ + (delList.length + 1) * Cited.csTotal Kγ K s.G.n s.G.m s.q ∧
    R.rep h₀ s x mem ∧
    Cited.PrunedExpander.Good K (Cited.csPhi Kγ c s.G.m) s ∧
    (if overBudget then
      Cited.csPhi Kγ c (3 * G.m) * ((3 * G.m : ℕ) : ℝ) / 10 < (delList.length : ℝ) ∧
      VhatSet = G.verts
    else
      s.deleted = subdivDel delList ∧
      ((s.deleted.length : ℕ) : ℝ) ≤ Cited.csPhi Kγ c s.G.m * (s.G.m : ℝ) / 10 ∧
      VhatSet = projSet G.n s.S)

def PDSInv (Kγ c : ℕ) (K : ℝ) (cw : ℕ) (R : DSRep Cited.PrunedExpander)
    (φ_in : ℝ) (M : ℕ) (G : Cited.Graph) : PDSState R.τ → Prop
  | .cs φ_in' M' G' w h₀ h s x mem delList overBudget VhatSet =>
    φ_in' = φ_in ∧ M' = M ∧ G' = G ∧
    CSStateInv Kγ c K cw R φ_in M G w h₀ h s x mem delList overBudget VhatSet
  | .fb φ_in' M' G' del S =>
    φ_in' = φ_in ∧ M' = M ∧ G' = G ∧
    φ_in < 10 * Cited.csPhi Kγ c (3 * G.m) ∧
    FallbackInv φ_in G del S ∧ del ⊆ Finset.range G.m

lemma nodup_subset_range_length_le {l : List ℕ} {n : ℕ} (hnd : l.Nodup)
    (hsub : ∀ j ∈ l, j < n) : l.length ≤ n := by
  have h1 : l.toFinset ⊆ Finset.range n := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_range.mpr (hsub x hx)
  rw [← List.toFinset_card_of_nodup hnd]
  exact le_trans (Finset.card_le_card h1) (by simp)

lemma cs_init_empty_S {G : Cited.Graph} (hV : G.IsValid)
    (hiso : ∀ v < G.n, 1 ≤ G.deg v) {s : Cited.PrunedExpander}
    (hsG : s.G = subdivGraph G) (hsdel : s.deleted = [])
    {K φ : ℝ} (hgood : Cited.PrunedExpander.Good K φ s) : s.S = ∅ := by
  rcases hgood with ⟨hSV, hvol, _⟩
  rw [hsdel] at hvol
  simp only [List.length_nil, Nat.cast_zero, mul_zero, zero_div] at hvol
  have hS0 : s.G.vol s.S = 0 := by
    by_contra hpos
    have : (1 : ℝ) ≤ (s.G.vol s.S : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hpos
    linarith
  have hisoS : ∀ v < (subdivGraph G).n, 1 ≤ (subdivGraph G).deg v := subdivGraph_no_isolated hV hiso
  ext v
  simp only [Finset.notMem_empty, iff_false]
  intro hv
  have hv_lt : v < s.G.n := Finset.mem_range.mp (hSV hv)
  have hv_deg : 1 ≤ s.G.deg v := by
    rw [hsG]
    exact hisoS v (hsG ▸ hv_lt)
  have hle : s.G.deg v ≤ s.G.vol s.S :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
  omega

lemma mem_subdivDel_iff (delList : List ℕ) (e : ℕ) :
    3 * e + 1 ∈ subdivDel delList ↔ e ∈ delList := by
  simp only [subdivDel, List.mem_map]
  constructor
  · rintro ⟨j, hj, heq⟩
    have : j = e := by omega
    subst this; exact hj
  · intro he
    exact ⟨e, he, rfl⟩

noncomputable def csInitState {Kγ c : ℕ} (K : ℝ) (cw : ℕ)
    (mk : ℕ → List Stmt) (R : DSRep Cited.PrunedExpander)
    (hImpl : ∀ w b (p : Program), p.HasAt b (mk b) →
      R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w))
    (φ_in : ℝ) (M : ℕ) (G : Cited.Graph)
    (hφ : 0 < φ_in) (hφ1 : φ_in ≤ 1) (hV : G.IsValid) (hm : 1 ≤ G.m) (hmM : G.m ≤ M)
    (hiso : ∀ v < G.n, 1 ≤ G.deg v) (hexp : G.IsConductanceExpanderOn G.verts φ_in)
    (hcs : 10 * Cited.csPhi Kγ c (3 * G.m) ≤ φ_in) :
    { st : PDSState R.τ //
      PDSInv Kγ c K cw R φ_in M G st ∧ pdsVhat st = ∅ ∧ pdsDeleted st = ∅ } := by
  set G_s := subdivGraph G
  set w := csWordSize Kγ cw K M G
  set h₀ := G_s.encode.length
  set args := [0, qOf M, h₀]
  set mem := WordRAM.initMem G_s.encode
  have hR := (hImpl w 0 (csProgram mk) (csProgram_hasAt mk)).2.1
  have hpre : (Cited.prunedExpanderDS Kγ c K cw w).initPre args mem := by
    have hrG : Cited.readGraph mem (args.getD 0 0) = G_s := readGraph_initMem_zero G_s
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, qOf_ge_two M, ?_⟩
    · rw [hrG]; exact subdivGraph_isValid hV
    · rw [hrG]; exact subdivGraph_isSimple hV
    · rw [hrG, show G_s.m = 3 * G.m from subdivGraph_m G]; omega
    · rw [hrG]; exact subdivGraph_no_isolated hV hiso
    · rw [hrG]
      have hexp10 : G_s.IsConductanceExpanderOn G_s.verts (φ_in / 10) :=
        subdivGraph_expander hV hφ.le hφ1 hexp
      have hle : Cited.csPhi Kγ c G_s.m ≤ φ_in / 10 := by
        rw [show G_s.m = 3 * G.m from subdivGraph_m G]
        linarith
      exact isConductanceExpanderOn_mono hle hexp10
    · rw [hrG]; exact csWordSize_ge_cw Kγ cw K M G
  have hH_lt : G_s.encode.length +
      (G.m + 2) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) +
      Cited.csQuery Kγ K G_s.m (qOf M) + G_s.n + 3 * G.m + qOf M + 4 < 2 ^ w :=
    lt_two_pow_csWordSize Kγ cw K M G
  have hargs_w : ∀ a ∈ args, a < 2 ^ w := by
    intro a ha
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  have hzf : ZeroFrom mem (heapArg args) := by
    change ZeroFrom (WordRAM.initMem G_s.encode) h₀
    exact zeroFrom_initMem G_s.encode
  have hspace_w : heapArg args + (Cited.prunedExpanderDS Kγ c K cw w).initSpace args mem < 2 ^ w := by
    have hmul : Cited.csTotal Kγ K G_s.n G_s.m (qOf M) ≤
        (G.m + 2) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hheap_eq : heapArg args = h₀ := rfl
    have hspace_eq : (Cited.prunedExpanderDS Kγ c K cw w).initSpace args mem =
        Cited.csTotal Kγ K G_s.n G_s.m (qOf M) := by
      change Cited.csTotal Kγ K (Cited.readGraph mem (args.getD 0 0)).n
        (Cited.readGraph mem (args.getD 0 0)).m (args.getD 1 0) = _
      rw [show Cited.readGraph mem (args.getD 0 0) = G_s from readGraph_initMem_zero G_s]
      rfl
    omega
  have hrun := hR args mem 0 (fun _ => false) hargs_w hpre hzf hspace_w
  let body := Classical.choose hrun
  have hbody := Classical.choose_spec hrun
  let o := Classical.choose hbody.2
  have ho := Classical.choose_spec hbody.2
  let st' := Classical.choose ho
  have hst' := Classical.choose_spec ho
  let cost := Classical.choose hst'
  have hcost := Classical.choose_spec hst'
  let s' := Classical.choose hcost.2
  have hs' := Classical.choose_spec hcost.2
  let x' := Classical.choose hs'
  have hx' := Classical.choose_spec hs'
  rcases hx' with ⟨hrep, hpost, hresp, _⟩
  rcases hpost with ⟨hs'G, hs'q, hs'del, hgood⟩
  have hrG : Cited.readGraph mem (args.getD 0 0) = G_s := readGraph_initMem_zero G_s
  rw [hrG] at hs'G
  have hS_empty : s'.S = ∅ := cs_init_empty_S hV hiso hs'G hs'del hgood
  have hVhat_empty : projSet G.n s'.S = ∅ := by simp [projSet, hS_empty]
  have hzero_del : ((s'.deleted.length : ℕ) : ℝ) ≤
      Cited.csPhi Kγ c s'.G.m * (s'.G.m : ℝ) / 10 := by
    rw [hs'del]
    simp only [List.length_nil, Nat.cast_zero]
    unfold Cited.csPhi Cited.csGamma
    positivity
  have hresp_h : h₀ ≤ o.value ∧ o.value ≤ h₀ + Cited.csTotal Kγ K G_s.n G_s.m (qOf M) ∧
      ZeroFrom st'.mem o.value ∧ ∀ a, R.foot h₀ x' a → h₀ ≤ a ∧ a < o.value := by
    have hinitSpace_eq : (Cited.prunedExpanderDS Kγ c K cw w).initSpace args mem =
        Cited.csTotal Kγ K G_s.n G_s.m (qOf M) := by
      change Cited.csTotal Kγ K (Cited.readGraph mem (args.getD 0 0)).n
        (Cited.readGraph mem (args.getD 0 0)).m (args.getD 1 0) = _
      rw [hrG]
      rfl
    have h2 : o.value ≤ h₀ + Cited.csTotal Kγ K G_s.n G_s.m (qOf M) := by
      have h2' := hresp.2.1
      change o.value ≤ h₀ + (Cited.prunedExpanderDS Kγ c K cw w).initSpace args mem at h2'
      rw [hinitSpace_eq] at h2'
      exact h2'
    refine ⟨hresp.1, h2, hresp.2.2.1, fun a ha => ?_⟩
    rcases hresp.2.2.2.2 a ha with hFalse | hrange
    · exact False.elim hFalse
    · exact hrange
  change R.rep h₀ s' x' st'.mem at hrep
  have hs'G_eq : s'.G = G_s := hs'G
  have hs'q_eq : s'.q = qOf M := hs'q
  refine ⟨.cs φ_in M G w h₀ o.value s' x' st'.mem [] false (projSet G.n s'.S), ?_, hVhat_empty, rfl⟩
  refine ⟨rfl, rfl, rfl, hφ, hV, hm, hmM, hcs, hs'G_eq, hs'q_eq, List.nodup_nil, by simp, rfl, rfl,
    hresp_h.2.2.1, fun a ha => (hresp_h.2.2.2 a ha).2, ?_, hrep, hgood, ?_⟩
  · simp only [List.length_nil, Nat.zero_add, one_mul]
    rw [hs'G_eq, hs'q_eq]
    exact hresp_h.2.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by rw [hs'del]; rfl, hzero_del, trivial⟩

noncomputable def csDeleteState {Kγ c : ℕ} (hc : 1 ≤ c) (K : ℝ) (cw : ℕ)
    (mk : ℕ → List Stmt) (R : DSRep Cited.PrunedExpander)
    (hImpl : ∀ w b (p : Program), p.HasAt b (mk b) →
      R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w))
    (φ_in : ℝ) (M : ℕ) (G : Cited.Graph) (w h₀ h : ℕ) (s_cs : Cited.PrunedExpander)
    (x : R.τ) (mem : ℕ → ℕ) (delList : List ℕ) (VhatSet : Finset ℕ) (e : ℕ)
    (hinv : CSStateInv Kγ c K cw R φ_in M G w h₀ h s_cs x mem delList false VhatSet)
    (he_lt : e < G.m) (he_nd : e ∉ delList)
    (hbud : ((delList.length + 1 : ℕ) : ℝ) ≤ Cited.csPhi Kγ c s_cs.G.m * (s_cs.G.m : ℝ) / 10) :
    { p : PDSState R.τ × Finset ℕ //
      PDSInv Kγ c K cw R φ_in M G p.1 ∧
      pdsDeleted p.1 = insert e delList.toFinset ∧
      VhatSet ⊆ pdsVhat p.1 ∧
      pdsVhat p.1 ⊆ G.verts ∧
      p.2 = pdsVhat p.1 \ VhatSet ∧
      (G.vol (pdsVhat p.1) : ℝ) ≤
        csGammaDel K * ((insert e delList.toFinset).card : ℝ) / csPhiOut Kγ c φ_in M } := by
  classical
  rcases hinv with ⟨hφ, hV, hm1, hmM, hcs, hsG, hsq, hdel_nd, hdel_lt, hw_eq, hh₀_eq, hzf,
    hfoot, hh_le, hrep, hgood, hbranch⟩
  simp only [Bool.false_eq_true, ↓reduceIte] at hbranch
  rcases hbranch with ⟨hsdel, _, hVhat_eq⟩
  have hlen_lt : delList.length < G.m := by
    have hnd' : (e :: delList).Nodup := List.nodup_cons.mpr ⟨he_nd, hdel_nd⟩
    have hsub' : ∀ j ∈ e :: delList, j < G.m := by
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj'
      · exact he_lt
      · exact hdel_lt j hj'
    have hle := nodup_subset_range_length_le hnd' hsub'
    simp only [List.length_cons] at hle
    omega
  set G_s := subdivGraph G
  have hH_lt : G_s.encode.length +
      (G.m + 2) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) +
      Cited.csQuery Kγ K G_s.m (qOf M) + G_s.n + 3 * G.m + qOf M + 4 < 2 ^ w := by
    rw [hw_eq]
    exact lt_two_pow_csWordSize Kγ cw K M G
  have hw_cw : cw * (Nat.log 2 (G_s.n + G_s.m + 2) + 1) ≤ w := by
    rw [hw_eq]
    exact csWordSize_ge_cw Kγ cw K M G
  set args := [h₀, 3 * e + 1, h]
  have hpre : (Cited.prunedExpanderDS Kγ c K cw w).pre 0 s_cs args mem := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · rw [hsG]; exact hw_cw
    · change 3 * e + 1 < s_cs.G.m
      rw [hsG, show G_s.m = 3 * G.m from subdivGraph_m G]; omega
    · change 3 * e + 1 ∉ s_cs.deleted
      rw [hsdel, mem_subdivDel_iff]; exact he_nd
    · rw [hsdel, subdivDel, List.length_map]; exact hbud
  have hargs_w : ∀ a ∈ args, a < 2 ^ w := by
    intro a ha
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at ha
    have hh_bound : h ≤ G_s.encode.length + G.m * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) := by
      have : delList.length + 1 ≤ G.m := by omega
      have hmul : (delList.length + 1) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) ≤
          G.m * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) :=
        Nat.mul_le_mul_right _ this
      rw [hh₀_eq, hsG, hsq] at hh_le
      omega
    have hm_le : G.m * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) ≤
        (G.m + 2) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) :=
      Nat.mul_le_mul_right _ (by omega)
    rcases ha with rfl | rfl | rfl <;> omega
  have hspace_w : heapArg args + (Cited.prunedExpanderDS Kγ c K cw w).space 0 s_cs args mem < 2 ^ w := by
    change h + Cited.csTotal Kγ K s_cs.G.n s_cs.G.m s_cs.q < 2 ^ w
    rw [hsG, hsq]
    have hh_bound : h ≤ G_s.encode.length + G.m * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) := by
      have : delList.length + 1 ≤ G.m := by omega
      have hmul : (delList.length + 1) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) ≤
          G.m * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) :=
        Nat.mul_le_mul_right _ this
      rw [hh₀_eq, hsG, hsq] at hh_le
      omega
    have hm_le : (G.m + 1) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) ≤
        (G.m + 2) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) :=
      Nat.mul_le_mul_right _ (by omega)
    have hadd : G.m * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) + Cited.csTotal Kγ K G_s.n G_s.m (qOf M) =
        (G.m + 1) * Cited.csTotal Kγ K G_s.n G_s.m (qOf M) := by ring
    omega
  have hR := (hImpl w 0 (csProgram mk) (csProgram_hasAt mk)).2.2 0 h₀ s_cs x args mem 0
    (fun _ => false) hargs_w rfl hrep hpre hfoot hzf hspace_w
  let body := Classical.choose hR
  have hbody := Classical.choose_spec hR
  let o := Classical.choose hbody.2
  have ho := Classical.choose_spec hbody.2
  let st' := Classical.choose ho
  have hst' := Classical.choose_spec ho
  let cost := Classical.choose hst'
  have hcost := Classical.choose_spec hst'
  let s' := Classical.choose hcost.2
  have hs' := Classical.choose_spec hcost.2
  let x' := Classical.choose hs'
  have hx' := Classical.choose_spec hs'
  rcases hx' with ⟨hrep', hpost', hresp', _⟩
  rcases hpost' with ⟨hs'G, hs'q, hs'del, hS_sub, hgood', _⟩
  set delList' := delList ++ [e]
  have hs'G_sub : s'.G = G_s := hs'G.trans hsG
  have hs'q_eq : s'.q = qOf M := hs'q.trans hsq
  have hs'del_eq : s'.deleted = subdivDel delList' := by
    rw [hs'del, hsdel]
    simp [delList', subdivDel, args]
  have hdel'_nd : delList'.Nodup := by
    rw [List.nodup_append]
    exact ⟨hdel_nd, List.nodup_singleton e, fun x hx y hy hxy => by
      simp only [List.mem_singleton] at hy
      subst hxy hy
      exact he_nd hx⟩
  have hdel'_lt : ∀ j ∈ delList', j < G.m := by
    intro j hj
    rw [List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact hdel_lt j hj
    · exact he_lt
  have hdel'_fin : delList'.toFinset = insert e delList.toFinset := by
    ext j
    simp [delList']
  have hbud' : ((s'.deleted.length : ℕ) : ℝ) ≤ Cited.csPhi Kγ c s'.G.m * (s'.G.m : ℝ) / 10 := by
    rw [hs'del_eq, hs'G_sub, subdivDel, List.length_map, List.length_append, List.length_singleton]
    rw [hsG] at hbud
    exact hbud
  have hresp'_foot : ∀ a, R.foot h₀ x' a → a < o.value := by
    intro a ha
    rcases hresp'.2.2.2.2 a ha with ha_old | ⟨_, ha_lt⟩
    · exact lt_of_lt_of_le (hfoot a ha_old) hresp'.1
    · exact ha_lt
  have hh'_le : o.value ≤ h₀ + (delList'.length + 1) * Cited.csTotal Kγ K s'.G.n s'.G.m s'.q := by
    have h1 := hresp'.2.1
    change o.value ≤ h + Cited.csTotal Kγ K s_cs.G.n s_cs.G.m s_cs.q at h1
    rw [hs'G, hs'q]
    have hlen' : delList'.length = delList.length + 1 := by simp [delList']
    rw [hlen']
    have hsum : (delList.length + 1 + 1) * Cited.csTotal Kγ K s_cs.G.n s_cs.G.m s_cs.q =
        (delList.length + 1) * Cited.csTotal Kγ K s_cs.G.n s_cs.G.m s_cs.q +
          Cited.csTotal Kγ K s_cs.G.n s_cs.G.m s_cs.q := by ring
    omega
  set Vhat' := projSet G.n s'.S
  have hVhat_sub : VhatSet ⊆ Vhat' := by
    rw [hVhat_eq]
    intro v hv
    dsimp only [Vhat']
    rw [projSet, Finset.mem_filter] at hv ⊢
    exact ⟨hS_sub hv.1, hv.2⟩
  have hVhat'_sub : Vhat' ⊆ G.verts := (projSet_spec hV s'.S).1
  have hvol_le : (G.vol Vhat' : ℝ) ≤
      csGammaDel K * ((insert e delList.toFinset).card : ℝ) / csPhiOut Kγ c φ_in M := by
    have hvol1 : (G.vol Vhat' : ℝ) ≤ (G_s.vol s'.S : ℝ) := by
      exact_mod_cast (projSet_spec hV s'.S).2
    have hvol2 : (G_s.vol s'.S : ℝ) ≤ K * (s'.deleted.length : ℝ) / Cited.csPhi Kγ c (3 * G.m) := by
      have hg := hgood'.2.1
      rw [hs'G_sub, hsG, show G_s.m = 3 * G.m from subdivGraph_m G] at hg
      exact hg
    have hlen_card : s'.deleted.length = (insert e delList.toFinset).card := by
      have h1 : s'.deleted.length = delList'.length := by rw [hs'del_eq, subdivDel, List.length_map]
      rw [h1, ← hdel'_fin, List.toFinset_card_of_nodup hdel'_nd]
    have hcard_nn : (0 : ℝ) ≤ ((insert e delList.toFinset).card : ℝ) := Nat.cast_nonneg _
    have hφc_pos : 0 < Cited.csPhi Kγ c (3 * G.m) := csPhi_pos Kγ c (3 * G.m) hc
    have hφout_pos : 0 < csPhiOut Kγ c φ_in M := csPhiOut_pos Kγ c hc hφ M
    have hφout_le : csPhiOut Kγ c φ_in M ≤ Cited.csPhi Kγ c (3 * G.m) :=
      csPhiOut_le_csPhi_m hc φ_in hmM
    have hK_le : K * ((insert e delList.toFinset).card : ℝ) ≤
        csGammaDel K * ((insert e delList.toFinset).card : ℝ) := by
      have : K ≤ csGammaDel K := le_trans (le_max_left K 1) (le_max_left _ 7)
      exact mul_le_mul_of_nonneg_right this hcard_nn
    have hdiv1 : K * ((insert e delList.toFinset).card : ℝ) / Cited.csPhi Kγ c (3 * G.m) ≤
        csGammaDel K * ((insert e delList.toFinset).card : ℝ) / Cited.csPhi Kγ c (3 * G.m) :=
      div_le_div_of_nonneg_right hK_le hφc_pos.le
    have hγ_nn : 0 ≤ csGammaDel K * ((insert e delList.toFinset).card : ℝ) := by
      have : 0 ≤ csGammaDel K := le_trans (by norm_num) (le_max_right _ 7)
      exact mul_nonneg this hcard_nn
    have hdiv2 : csGammaDel K * ((insert e delList.toFinset).card : ℝ) / Cited.csPhi Kγ c (3 * G.m) ≤
        csGammaDel K * ((insert e delList.toFinset).card : ℝ) / csPhiOut Kγ c φ_in M :=
      div_le_div_of_nonneg_left hγ_nn hφout_pos hφout_le
    rw [hlen_card] at hvol2
    exact le_trans (le_trans hvol1 hvol2) (le_trans hdiv1 hdiv2)
  refine ⟨(.cs φ_in M G w h₀ o.value s' x' st'.mem delList' false Vhat', Vhat' \ VhatSet),
    ?_, hdel'_fin, hVhat_sub, hVhat'_sub, rfl, hvol_le⟩
  refine ⟨rfl, rfl, rfl, hφ, hV, hm1, hmM, hcs, hs'G_sub, hs'q_eq, hdel'_nd, hdel'_lt,
    hw_eq, hh₀_eq, hresp'.2.2.1, hresp'_foot, hh'_le, hrep', ?_, ?_⟩
  · rwa [hs'G_sub, ← hsG]
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨hs'del_eq, hbud', rfl⟩


end

end MinCostFlow.Expander
