module

public import MinCostFlow.SparseCore.Program.LSFWindowBuild
public import MinCostFlow.SparseCore.Program.LSFWindowReloc
public import MinCostFlow.SparseCore.Program.LSFWindowRepack
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import WordRAM.Tactic

/-!
# Host Canonical LSF Window Initializer (`LSFWindowProc`)

Assembles the deterministic relocatable module `lsfWindowProcs` (and standalone `lsfWindowModule`)
whose entry procedure `lsfWindowInitProc` (index `0`) initializes `k_nat` dynamic LSF copies for
`(G₀, ℓ₀)` by:
1. Building the canonical guest memory image at host offset `heap` via `buildCanonGuestProc`.
2. Executing the relocated `lemma55Module` inside `[heap, heap + 2 ^ w')` via
   `canonicalLSF_relocated_run`, producing the exact states `canonicalLSFInitWithH h ... j`.
3. Sparsely repacking all `k_nat` guest handles into fresh zeroed host memory starting at
   `heap + r.endHeap` with host capacities `(vCap_host, eCap_host, L_w_host)` via
   `repackOneLSFProc`, writing the resulting host handles into `handlesOut[0 .. k_nat - 1]`.

Total deterministic time is bounded by
`(2 * (lemma55Module Q_AN c_AN K_AN h).regBound + 10) * lemma55Cost ...`,
with a constant completely independent of the input and zero dependence on `vCap_host` or
`eCap_host`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM WordRAM.Link MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
open MinCostFlow.DynSpanner.Program MinCostFlow.WideWord MinCostFlow.Num

/-! ## Procedure and module definitions -/

def lsfWindowIdxInit : ℕ := 0

/-- Host entry procedure for the canonical LSF window initializer.
Args: `[g0Ptr, lenArr, L_in, P_fp, k_nat, L_w_host, vCap_host, eCap_host, handlesOut, heap]`
(registers `0 .. 9`). Returns the new host heap end pointer `endHeap`. -/
def lsfWindowInitProc (bBuildTop bRepOne bLog bReloc R_Q rhoConstLog : ℕ) : Stmt :=
  -- 1. Build canonical guest memory image at host offset `heap` (r9)
  .call 10 bBuildTop [.reg 0, .reg 1, .reg 2, .reg 9] ;;
  -- 2. Read canonical dimensions from guest DynGraph header at r9
  .assign 10 (.load (.bin .add (.reg 9) (.const dgVCapOff))) ;;
  .assign 11 (.load (.bin .add (.reg 9) (.const dgECapOff))) ;;
  .assign 12 (.load (.bin .add (.reg 9) (.const dgNOff))) ;;
  -- 3. Compute canonical guest pointers (canonLenArr, canonHandlesOut, canonHeap)
  .assign 13 (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 10)))
    (.bin .mul (.const 9) (.reg 11))) ;;
  .assign 14 (.bin .add (.reg 13) (.bin .mul (.reg 11) (.reg 2))) ;;
  .assign 15 (.bin .add (.reg 14) (.reg 4)) ;;
  -- 4. Compute canonLw K_AN L_in n0 k_nat
  .call 16 bLog [.bin .add (.reg 4) (.const 1)] ;;
  .call 17 bLog [.bin .add (.reg 12) (.const 2)] ;;
  .call 17 bLog [.bin .add (.reg 17) (.const 2)] ;;
  .assign 16 (.bin .add (.bin .add (.bin .add (.bin .add (.reg 2) (.const rhoConstLog))
    (.reg 16)) (.bin .mul (.const 6) (.reg 17))) (.const 8)) ;;
  -- 5. Invoke relocated `lemma55Module` entry at bReloc + 1
  .call 18 (bReloc + 1)
    ([.const 0, .reg 13, .reg 2, .reg 3, .reg 4, .reg 16, .reg 10, .reg 11, .reg 14, .reg 15] ++
      List.replicate (R_Q - 10) (.const 0) ++ [.reg 9, .const 0]) ;;
  -- 6. Sparsely repack all k_nat guest handles into fresh zeroed host memory from heap + r.endHeap
  .assign 19 (.bin .add (.reg 9) (.reg 18)) ;;
  .assign 20 (.bin .add (.reg 9) (.reg 14)) ;;
  forRange 21 (.const 0) (.reg 4)
    (.assign 22 (.load (.bin .add (.reg 20) (.reg 21))) ;;
     .store (.bin .add (.reg 8) (.reg 21)) (.reg 19) ;;
     .call 19 bRepOne [.reg 9, .reg 22, .reg 19, .reg 6, .reg 7, .reg 5]) ;;
  -- 7. Return host heap end pointer
  .ret (.reg 19)

lemma lsfWindowInitProc_noRand (bBuildTop bRepOne bLog bReloc R_Q rhoConstLog : ℕ) :
    (lsfWindowInitProc bBuildTop bRepOne bLog bReloc R_Q rhoConstLog).NoRand := by
  simp [lsfWindowInitProc, forRange, forUp, Stmt.NoRand]

/-- Full relocatable procedure list for the canonical LSF window initializer starting at index `b`. -/
noncomputable def lsfWindowProcs (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (b h : ℕ) : List Stmt :=
  [lsfWindowInitProc (b + 13) (b + 20) (b + 3) (b + 20)
      (lemma55Module Q_AN c_AN K_AN h).regBound
      (Nat.log 2 (lemma55RhoConst K_AN + 1)),
   memCopyStmt,
   memFillStmt,
   log2Stmt] ++
  sortProcs (b + 4) ++
  canonBuildProcs (b + 8) (b + 4) (b + 1) (b + 2) ++
  repackProcs (b + 14) (b + 1) (b + 3) ++
  lemma55RelocProcs Q_AN c_AN K_AN (b + 20) h

lemma lsfWindowProcs_length (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (b h : ℕ) :
    (lsfWindowProcs Q_AN c_AN K_AN b h).length =
      21 + (lemma55Module Q_AN c_AN K_AN h).procs.length := by
  unfold lsfWindowProcs
  simp only [List.length_append, List.length_cons, List.length_nil,
    sortProcs_length, canonBuildProcs_length, repackProcs_length, lemma55RelocProcs_length]

lemma lsfWindowProcs_noRand (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (b h : ℕ) :
    ∀ s ∈ lsfWindowProcs Q_AN c_AN K_AN b h, s.NoRand := by
  intro s hs
  unfold lsfWindowProcs at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with ((((rfl | rfl | rfl | rfl) | hS) | hB) | hR) | hL
  · exact lsfWindowInitProc_noRand _ _ _ _ _ _
  · exact memCopyStmt_noRand
  · exact memFillStmt_noRand
  · exact log2Stmt_noRand
  · exact sortProcs_noRand _ _ hS
  · exact canonBuildProcs_noRand _ _ _ _ _ hB
  · exact repackProcs_noRand _ _ _ _ hR
  · exact lemma55RelocProcs_noRand _ _ _ _ _ _ hL

/-- Standalone deterministic Word-RAM module for the canonical LSF window initializer. -/
noncomputable def lsfWindowModule (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (h : ℕ) : Program :=
  ⟨lsfWindowProcs Q_AN c_AN K_AN 0 h⟩

lemma lsfWindowModule_isDeterministic (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (h : ℕ) :
    (lsfWindowModule Q_AN c_AN K_AN h).IsDeterministic :=
  lsfWindowProcs_noRand Q_AN c_AN K_AN 0 h

/-! ## Space and cost budgets -/

/-- Host heap space above `heap` consumed by `lsfWindowInitProc`: guest window `[heap, heap + 2^w')`
plus `k_nat` repacked host `LSFRep` handles. -/
noncomputable def lsfWindowSpace (Q_AN : Program) (K_AN : ℝ) (c_AN h L_in L_w_host P_fp k_nat
    vCap_host eCap_host : ℕ) (G₀ : MGraph) : ℕ :=
  max (2 ^ canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k_nat)
    (canonHandlesOut G₀ L_in + max G₀.n G₀.m + 1) +
    k_nat * lsfStaticSize vCap_host eCap_host G₀.n G₀.n L_w_host + 1

/-- Deterministic step bound for `lsfWindowInitProc`: an input-free constant times `lemma55Cost`
at `canonLw`, completely independent of `vCap_host`, `eCap_host`, and `L_w_host`. -/
noncomputable def lsfWindowCost (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (h L_in P_fp k_nat n0 m0 : ℕ) : ℕ :=
  (2 * (lemma55Module Q_AN c_AN K_AN h).regBound + 10) *
    lemma55Cost Q_AN c_AN K_AN h L_in (canonLw K_AN L_in n0 k_nat) P_fp k_nat n0 m0

/-! ## Structural and arithmetic helpers -/

private lemma hasAt_append_left {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt b xs := fun i hi => by
  have h1 := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at h1

private lemma hasAt_append_right {p : Program} {b : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) : p.HasAt (b + xs.length) ys := fun i hi => by
  have h1 := h (xs.length + i) (by simp; omega)
  rw [List.getElem_append_right (Nat.le_add_right _ _)] at h1
  simpa [Nat.add_assoc] using h1

lemma hasAt_lsfWindow_split {p Q_AN : Program} {c_AN b h : ℕ} {K_AN : ℝ}
    (hp : p.HasAt b (lsfWindowProcs Q_AN c_AN K_AN b h)) :
    p.procs[b + 0]? = some (lsfWindowInitProc (b + 13) (b + 20) (b + 3) (b + 20)
      (lemma55Module Q_AN c_AN K_AN h).regBound (Nat.log 2 (lemma55RhoConst K_AN + 1))) ∧
    p.procs[b + 1]? = some memCopyStmt ∧
    p.procs[b + 2]? = some memFillStmt ∧
    p.procs[b + 3]? = some log2Stmt ∧
    p.HasAt (b + 4) (sortProcs (b + 4)) ∧
    p.HasAt (b + 8) (canonBuildProcs (b + 8) (b + 4) (b + 1) (b + 2)) ∧
    p.HasAt (b + 14) (repackProcs (b + 14) (b + 1) (b + 3)) ∧
    p.HasAt (b + 21) (lemma55RelocProcs Q_AN c_AN K_AN (b + 20) h) := by
  unfold lsfWindowProcs at hp
  have h1 := hasAt_append_left hp
  have hL := hasAt_append_right hp
  have h2 := hasAt_append_left h1
  have hR := hasAt_append_right h1
  have h3 := hasAt_append_left h2
  have hB := hasAt_append_right h2
  have h0 := hasAt_append_left h3
  have hS := hasAt_append_right h3
  have hlen0 : ([lsfWindowInitProc (b + 13) (b + 20) (b + 3) (b + 20)
      (lemma55Module Q_AN c_AN K_AN h).regBound (Nat.log 2 (lemma55RhoConst K_AN + 1)),
      memCopyStmt, memFillStmt, log2Stmt]).length = 4 := rfl
  have hlen3 : ([lsfWindowInitProc (b + 13) (b + 20) (b + 3) (b + 20)
      (lemma55Module Q_AN c_AN K_AN h).regBound (Nat.log 2 (lemma55RhoConst K_AN + 1)),
      memCopyStmt, memFillStmt, log2Stmt] ++ sortProcs (b + 4)).length = 8 := by
    simp [sortProcs_length]
  have hlen2 : ([lsfWindowInitProc (b + 13) (b + 20) (b + 3) (b + 20)
      (lemma55Module Q_AN c_AN K_AN h).regBound (Nat.log 2 (lemma55RhoConst K_AN + 1)),
      memCopyStmt, memFillStmt, log2Stmt] ++ sortProcs (b + 4) ++
      canonBuildProcs (b + 8) (b + 4) (b + 1) (b + 2)).length = 14 := by
    simp [sortProcs_length, canonBuildProcs_length]
  have hlen1 : ([lsfWindowInitProc (b + 13) (b + 20) (b + 3) (b + 20)
      (lemma55Module Q_AN c_AN K_AN h).regBound (Nat.log 2 (lemma55RhoConst K_AN + 1)),
      memCopyStmt, memFillStmt, log2Stmt] ++ sortProcs (b + 4) ++
      canonBuildProcs (b + 8) (b + 4) (b + 1) (b + 2) ++
      repackProcs (b + 14) (b + 1) (b + 3)).length = 21 := by
    simp [sortProcs_length, canonBuildProcs_length, repackProcs_length]
  rw [hlen0] at hS; rw [hlen3] at hB; rw [hlen2] at hR; rw [hlen1] at hL
  exact ⟨h0.get (i := 0) (by simp), h0.get (i := 1) (by simp),
    h0.get (i := 2) (by simp), h0.get (i := 3) (by simp), hS, hB, hR, hL⟩

lemma evalArgs_append {w : ℕ} {st : State} (es₁ es₂ : List Expr)
    {vs₁ vs₂ : List ℕ}
    (h₁ : evalArgs w st es₁ = some vs₁) (h₂ : evalArgs w st es₂ = some vs₂) :
    evalArgs w st (es₁ ++ es₂) = some (vs₁ ++ vs₂) := by
  induction es₁ generalizing vs₁ with
  | nil =>
    simp only [evalArgs, Option.some.injEq] at h₁
    subst h₁; simpa
  | cons e es ih =>
    simp only [List.cons_append, evalArgs] at h₁ ⊢
    cases he : e.eval w st with
    | none => simp [he] at h₁
    | some v =>
      simp only [he] at h₁ ⊢
      cases htl : evalArgs w st es with
      | none => simp [htl] at h₁
      | some vs =>
        simp only [htl, Option.some.injEq] at h₁
        subst h₁
        rw [ih htl]; rfl

lemma evalArgs_replicate_const_zero {w : ℕ} {st : State} (hw : 0 < 2 ^ w) (m : ℕ) :
    evalArgs w st (List.replicate m (.const 0)) = some (List.replicate m 0) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [List.replicate_succ, evalArgs, Expr.eval, hw, ↓reduceIte, ih]

lemma argsSize_append (es₁ es₂ : List Expr) :
    argsSize (es₁ ++ es₂) = argsSize es₁ + argsSize es₂ := by
  induction es₁ with
  | nil => simp [argsSize]
  | cons e es ih => simp [argsSize, ih, Nat.add_assoc]

lemma argsSize_replicate_const_zero (m : ℕ) :
    argsSize (List.replicate m (.const 0)) = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, Expr.size, ih]; omega

lemma lsfStaticSize_mono_tM {vCap eCap n0 tM L_w : ℕ} (htM : tM ≤ n0) :
    lsfStaticSize vCap eCap n0 tM L_w ≤ lsfStaticSize vCap eCap n0 n0 L_w := by
  unfold lsfStaticSize tBlockSize dynGraphSize; omega

lemma lsfWindow_total_cost_le {Q_AN : Program} {c_AN h L_in P_fp k_nat n0 m0 : ℕ}
    {K_AN : ℝ} (hh : 1 ≤ h) (hk : 1 ≤ k_nat) :
    let R_Q := (lemma55Module Q_AN c_AN K_AN h).regBound
    let L_w_g := canonLw K_AN L_in n0 k_nat
    let C55 := lemma55Cost Q_AN c_AN K_AN h L_in L_w_g P_fp k_nat n0 m0
    buildCanonGuestCost n0 m0 L_in + (R_Q + 6) * C55 +
      k_nat * (repackOneLSFCost n0 m0 L_w_g + 120) +
      (2 * R_Q + 40 * Nat.log 2 (k_nat + 1) + 40 * Nat.log 2 (n0 + 2) + 400) ≤
      lsfWindowCost Q_AN c_AN K_AN h L_in P_fp k_nat n0 m0 := by
  intro R_Q L_w_g C55
  set F := lsfOverhead Q_AN c_AN K_AN n0 m0 L_in L_w_g h
  set initC := lsfInitCostFactor * Nat.ceil (((m0 + n0 + 1 : ℕ) : ℝ) * F)
  have hF1 : 1 ≤ F := lsfOverhead_ge_one Q_AN c_AN K_AN n0 m0 L_in L_w_g h hh
  obtain ⟨hF_lsst, hF_log4, hF_Lw2, _⟩ := lsfOverhead_bounds Q_AN c_AN K_AN n0 m0 L_in L_w_g h hh
  set L_sim := WideWord.lsstLSimMin c_AN n0 (2 * m0) L_in h
  have hLsim_le_F : (L_sim : ℝ) ≤ F := by
    have hLsim_sq : (L_sim : ℝ) ^ 2 ≤ lsstOverheadFactorH Q_AN c_AN K_AN n0 (2 * m0) L_in h := by
      dsimp only [lsstOverheadFactorH]
      have h1L : 1 ≤ L_sim := le_trans (by dsimp [WideWord.kWidthOf]; omega) (le_max_left _ _)
      have hpow2 : 2 ≤ 2 ^ (L_sim * h) := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (L_sim * h) := Nat.pow_le_pow_right (by decide) (Nat.mul_pos h1L hh)
      have hwf := logLog_add_weightFactor_nonneg n0 _ hpow2
      have hK1 : (0 : ℝ) ≤ max K_AN 1 := le_trans (by norm_num) (le_max_right K_AN 1)
      have hterm : (0 : ℝ) ≤ (WideWord.simScale Q_AN : ℝ) * (L_sim : ℝ) *
          (WideWord.w'Max c_AN n0 (2 * m0) L_in h : ℝ) *
          (max K_AN 1 * (Cited.logLogFactor n0 + Cited.weightFactor n0 (2 ^ (L_sim * h))) + 1) :=
        mul_nonneg (by positivity) (by linarith [mul_nonneg hK1 hwf])
      linarith
    have h1L : (1 : ℝ) ≤ (L_sim : ℝ) := by
      have : 1 ≤ L_sim := le_trans (by dsimp [WideWord.kWidthOf]; omega) (le_max_left _ _)
      exact_mod_cast this
    have hle_sq : (L_sim : ℝ) ≤ (L_sim : ℝ) ^ 2 := by nlinarith
    linarith
  have hLin_le_F : (L_in : ℝ) ≤ F := by
    have h1 : L_in ≤ L_sim := le_trans (by dsimp [WideWord.kWidthOf]; omega) (le_max_left _ _)
    exact le_trans (by exact_mod_cast h1) hLsim_le_F
  have hlogm_le_F : ((Nat.log 2 (m0 + 1) + 1 : ℕ) : ℝ) ≤ F := by
    have h1 : Nat.log 2 (m0 + 1) + 1 ≤ L_sim := by
      have hmono : Nat.log 2 (m0 + 1) ≤ Nat.log 2 (4 * (2 * m0) + 2) :=
        Nat.log_mono_right (by omega)
      have hkw : Nat.log 2 (4 * (2 * m0) + 2) + 1 ≤ WideWord.kWidthOf (2 * m0) L_in := by
        dsimp [WideWord.kWidthOf]; omega
      exact le_trans (Nat.add_le_add_right hmono 1) (le_trans hkw (le_max_left _ _))
    exact le_trans (by exact_mod_cast h1) hLsim_le_F
  have hlogn_le_F : ((Nat.log 2 (n0 + 2) + 1 : ℕ) : ℝ) ≤ F := by
    have h1 : (1 : ℝ) ≤ ((Nat.log 2 (n0 + 2) + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    have h2 : ((Nat.log 2 (n0 + 2) + 1 : ℕ) : ℝ) ≤ ((Nat.log 2 (n0 + 2) + 1 : ℕ) : ℝ) ^ 4 :=
      le_self_pow₀ h1 (by decide)
    linarith
  have hauxlog_le_F : ((auxLogCap n0 : ℕ) : ℝ) ≤ F := by
    have h1 : auxLogCap n0 ≤ Nat.log 2 (n0 + 2) + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1
    exact le_trans (by exact_mod_cast h1) hlogn_le_F
  have hLw_le_F : (L_w_g : ℝ) ≤ F := by
    have h1 : (1 : ℝ) ≤ (L_w_g : ℝ) := by
      have : 1 ≤ L_w_g := by dsimp [L_w_g, canonLw]; omega
      exact_mod_cast this
    have h2 : (L_w_g : ℝ) ≤ (L_w_g : ℝ) ^ 2 := le_self_pow₀ h1 (by decide)
    linarith
  have hbuild_le : buildCanonGuestCost n0 m0 L_in ≤ initC := by
    have hceil : (((m0 + n0 + 1 : ℕ) : ℝ) * F) ≤ (Nat.ceil (((m0 + n0 + 1 : ℕ) : ℝ) * F) : ℝ) :=
      Nat.le_ceil _
    have hreal : (buildCanonGuestCost n0 m0 L_in : ℝ) ≤ (initC : ℝ) := by
      have hlogn1 : ((Nat.log 2 (n0 + 1) + 1 : ℕ) : ℝ) ≤ F := hauxlog_le_F
      have hm_nn : (0 : ℝ) ≤ (m0 : ℝ) := by positivity
      have hn_nn : (0 : ℝ) ≤ (n0 : ℝ) := by positivity
      have hmF : (m0 : ℝ) ≤ (m0 : ℝ) * F := le_mul_of_one_le_right hm_nn hF1
      have hnF : (n0 : ℝ) ≤ (n0 : ℝ) * F := le_mul_of_one_le_right hn_nn hF1
      have h1 : (n0 : ℝ) * ((Nat.log 2 (n0 + 1) + 1 : ℕ) : ℝ) ≤ (n0 : ℝ) * F :=
        mul_le_mul_of_nonneg_left hlogn1 hn_nn
      have h2 : (m0 : ℝ) * ((Nat.log 2 (m0 + 1) + 1 : ℕ) : ℝ) ≤ (m0 : ℝ) * F :=
        mul_le_mul_of_nonneg_left hlogm_le_F hm_nn
      have h3 : (m0 : ℝ) * (L_in : ℝ) ≤ (m0 : ℝ) * F :=
        mul_le_mul_of_nonneg_left hLin_le_F hm_nn
      have hsum : (m0 : ℝ) * F + (n0 : ℝ) * F + F = ((m0 + n0 + 1 : ℕ) : ℝ) * F := by
        push_cast; ring
      dsimp only [buildCanonGuestCost, initC, lsfInitCostFactor]
      push_cast at h1 h2 hsum hceil ⊢
      linarith
    exact_mod_cast hreal
  have hrep_le : repackOneLSFCost n0 m0 L_w_g + 120 ≤ initC := by
    have hceil : (((m0 + n0 + 1 : ℕ) : ℝ) * F) ≤ (Nat.ceil (((m0 + n0 + 1 : ℕ) : ℝ) * F) : ℝ) :=
      Nat.le_ceil _
    have hreal : ((repackOneLSFCost n0 m0 L_w_g + 120 : ℕ) : ℝ) ≤ (initC : ℝ) := by
      have hm_nn : (0 : ℝ) ≤ (m0 : ℝ) := by positivity
      have hn_nn : (0 : ℝ) ≤ (n0 : ℝ) := by positivity
      have hmF : (m0 : ℝ) ≤ (m0 : ℝ) * F := le_mul_of_one_le_right hm_nn hF1
      have hnF : (n0 : ℝ) ≤ (n0 : ℝ) * F := le_mul_of_one_le_right hn_nn hF1
      have h1 : (n0 : ℝ) * ((auxLogCap n0 : ℕ) : ℝ) ≤ (n0 : ℝ) * F :=
        mul_le_mul_of_nonneg_left hauxlog_le_F hn_nn
      have h2 : (m0 : ℝ) * (L_w_g : ℝ) ≤ (m0 : ℝ) * F :=
        mul_le_mul_of_nonneg_left hLw_le_F hm_nn
      have hsum : (m0 : ℝ) * F + (n0 : ℝ) * F + F = ((m0 + n0 + 1 : ℕ) : ℝ) * F := by
        push_cast; ring
      dsimp only [repackOneLSFCost, initC, lsfInitCostFactor]
      push_cast at h1 h2 hsum hceil ⊢
      linarith
    exact_mod_cast hreal
  have hC55_ge_init : k_nat * initC + 200 * k_nat + 20 * Nat.log 2 (n0 + 2) + 1000 ≤ C55 := by
    have hC55_eq : C55 = k_nat * (initC + m0 * (mwuEdgeStepCost L_in L_w_g P_fp + 80) + 200) +
        500 * L_w_g * L_w_g + 800 * L_w_g + 20 * Nat.log 2 (n0 + 2) + 30 * m0 + 1000 := rfl
    have h1 : k_nat * initC + 200 * k_nat ≤
        k_nat * (initC + m0 * (mwuEdgeStepCost L_in L_w_g P_fp + 80) + 200) := by
      have hmul : k_nat * (initC + 200) ≤
          k_nat * (initC + m0 * (mwuEdgeStepCost L_in L_w_g P_fp + 80) + 200) :=
        Nat.mul_le_mul_left k_nat (by omega)
      have hdist : k_nat * (initC + 200) = k_nat * initC + 200 * k_nat := by ring
      omega
    omega
  have hinit_le_C55 : initC ≤ C55 := by
    have : 1 * initC ≤ k_nat * initC := Nat.mul_le_mul_right initC hk
    omega
  have hk_rep_le_C55 : k_nat * (repackOneLSFCost n0 m0 L_w_g + 120) ≤ C55 := by
    have : k_nat * (repackOneLSFCost n0 m0 L_w_g + 120) ≤ k_nat * initC :=
      Nat.mul_le_mul_left k_nat hrep_le
    omega
  have hlogk_le : Nat.log 2 (k_nat + 1) ≤ k_nat := by
    have hlt := Nat.log_lt_self 2 (by omega : k_nat + 1 ≠ 0)
    omega
  have h2R_le : 2 * R_Q ≤ R_Q * C55 := by
    have : 2 ≤ C55 := by omega
    exact le_trans (by omega) (Nat.mul_le_mul_left R_Q this)
  have htail_le : 40 * Nat.log 2 (k_nat + 1) + 40 * Nat.log 2 (n0 + 2) + 400 ≤ 2 * C55 := by omega
  have hgoal_eq : lsfWindowCost Q_AN c_AN K_AN h L_in P_fp k_nat n0 m0 =
      (R_Q + 6) * C55 + R_Q * C55 + 4 * C55 := by
    dsimp only [lsfWindowCost, R_Q, C55, L_w_g]; ring
  rw [hgoal_eq]
  linarith

/-! ## Step 6: Sparse handle-repacking loop -/

/-- Deterministic host base addresses for the `k_nat` repacked handles starting at `startDst`. -/
def hostHandleAddr (startDst vCap_h eCap_h n0 L_w_h : ℕ) (tM_fn : ℕ → ℕ) : ℕ → ℕ
  | 0 => startDst
  | j + 1 => hostHandleAddr startDst vCap_h eCap_h n0 L_w_h tM_fn j +
      lsfStaticSize vCap_h eCap_h n0 (tM_fn j) L_w_h

lemma hostHandleAddr_mono {startDst vCap_h eCap_h n0 L_w_h : ℕ} {tM_fn : ℕ → ℕ}
    {i j : ℕ} (hij : i ≤ j) :
    hostHandleAddr startDst vCap_h eCap_h n0 L_w_h tM_fn i ≤
      hostHandleAddr startDst vCap_h eCap_h n0 L_w_h tM_fn j := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (Nat.le_add_right _ _)

lemma hostHandleAddr_le_mul {startDst vCap_h eCap_h n0 L_w_h k_nat : ℕ} {tM_fn : ℕ → ℕ}
    (htM : ∀ j, j < k_nat → tM_fn j ≤ n0) :
    ∀ i ≤ k_nat, hostHandleAddr startDst vCap_h eCap_h n0 L_w_h tM_fn i ≤
      startDst + i * lsfStaticSize vCap_h eCap_h n0 n0 L_w_h := by
  intro i hi
  induction i with
  | zero => simp [hostHandleAddr]
  | succ i ih =>
    have hi_le : i ≤ k_nat := by omega
    have h1 := ih hi_le
    have h2 : lsfStaticSize vCap_h eCap_h n0 (tM_fn i) L_w_h ≤
        lsfStaticSize vCap_h eCap_h n0 n0 L_w_h :=
      lsfStaticSize_mono_tM (htM i hi)
    change hostHandleAddr startDst vCap_h eCap_h n0 L_w_h tM_fn i +
        lsfStaticSize vCap_h eCap_h n0 (tM_fn i) L_w_h ≤ _
    rw [Nat.succ_mul]
    omega

set_option maxHeartbeats 600000 in
lemma lsfWindow_repackLoop {w h bRep bCopy bLog : ℕ} {p : Program}
    {mem2 : ℕ → ℕ} {heap rEnd guestHndBase handlesOut k_nat L_w_h vCap_h eCap_h n0 m0 L_w_g : ℕ}
    {S : ℕ → LSFState} {x_g : ℕ → LSFConcrete} {hs_g : ℕ → ℕ}
    (hw : 20 < 2 ^ w)
    (hRep : p.HasAt bRep (repackProcs bRep bCopy bLog))
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hLog : MeetsContract w p bLog log2Contract)
    (hk_w : k_nat < 2 ^ w)
    (hhnd_le : handlesOut + k_nat ≤ heap)
    (hghnd_ge : heap ≤ guestHndBase)
    (hghnd_le : guestHndBase + k_nat ≤ heap + rEnd)
    (hLwh_w : L_w_h < 2 ^ w)
    (hend_w : heap + rEnd + k_nat * lsfStaticSize vCap_h eCap_h n0 n0 L_w_h < 2 ^ w)
    (hz2 : ZeroFrom mem2 (heap + rEnd))
    (hMemW2 : ∀ a, heap ≤ a → a < heap + rEnd → mem2 a < 2 ^ w)
    (hguest : ∀ j < k_nat,
      mem2 (guestHndBase + j) = hs_g j ∧
      (LSFRep h).rep (hs_g j) (S j) (x_g j) (fun a => mem2 (heap + a)) ∧
      (S j).G.V = (S j).T₀.V ∧ (S j).G.m ≤ m0 ∧
      (x_g j).vCap ≤ vCap_h ∧ (x_g j).eCap ≤ eCap_h ∧ (x_g j).L_w = L_w_g ∧
      L_w_g ≤ L_w_h ∧ (x_g j).n0 = n0 ∧ (x_g j).m0 = m0 ∧ (x_g j).tM ≤ n0 ∧
      (x_g j).endAddr (hs_g j) ≤ rEnd) :
    let hAddr := hostHandleAddr (heap + rEnd) vCap_h eCap_h n0 L_w_h (fun j => (x_g j).tM)
    let x_h : ℕ → LSFConcrete := fun j => { x_g j with vCap := vCap_h, eCap := eCap_h, L_w := L_w_h }
    Triple w p
      (fun st => st.regs 4 = k_nat ∧ st.regs 5 = L_w_h ∧ st.regs 6 = vCap_h ∧
        st.regs 7 = eCap_h ∧ st.regs 8 = handlesOut ∧ st.regs 9 = heap ∧
        st.regs 19 = heap + rEnd ∧ st.regs 20 = guestHndBase ∧ st.mem = mem2)
      (forRange 21 (.const 0) (.reg 4)
        (.assign 22 (.load (.bin .add (.reg 20) (.reg 21))) ;;
         .store (.bin .add (.reg 8) (.reg 21)) (.reg 19) ;;
         .call 19 (bRep + 6) [.reg 9, .reg 22, .reg 19, .reg 6, .reg 7, .reg 5]))
      (normalPost fun st =>
        st.regs 19 = hAddr k_nat ∧
        ZeroFrom st.mem (hAddr k_nat) ∧
        (∀ z < heap, (z < handlesOut ∨ handlesOut + k_nat ≤ z) → st.mem z = mem2 z) ∧
        (∀ j < k_nat, st.mem (handlesOut + j) = hAddr j ∧
          (LSFRep h).rep (hAddr j) (S j) (x_h j) st.mem))
      (fun _ => k_nat * (repackOneLSFCost n0 m0 L_w_g + 60) + 10) := by
  intro hAddr x_h
  have hpOne : p.procs[bRep + 6]? =
      some (repackOneLSFProc bLog (bRep + 0) (bRep + 1) (bRep + 2) (bRep + 3) (bRep + 4) (bRep + 5)) :=
    hRep.get (i := 6) (by rw [repackProcs_length]; decide)
  have htM_le : ∀ j < k_nat, (x_g j).tM ≤ n0 := fun j hj => (hguest j hj).2.2.2.2.2.2.2.2.2.2.1
  let LInv : ℕ → State → Prop := fun i st =>
    st.regs 4 = k_nat ∧ st.regs 5 = L_w_h ∧ st.regs 6 = vCap_h ∧
    st.regs 7 = eCap_h ∧ st.regs 8 = handlesOut ∧ st.regs 9 = heap ∧
    st.regs 19 = hAddr i ∧ st.regs 20 = guestHndBase ∧ st.regs 21 = i ∧
    ZeroFrom st.mem (hAddr i) ∧
    (∀ a, heap ≤ a → a < heap + rEnd → st.mem a = mem2 a) ∧
    (∀ z < heap, (z < handlesOut ∨ handlesOut + i ≤ z) → st.mem z = mem2 z) ∧
    (∀ j < i, st.mem (handlesOut + j) = hAddr j ∧
      (LSFRep h).rep (hAddr j) (S j) (x_h j) st.mem)
  have hloop : Triple w p
      (fun st => st.regs 4 = k_nat ∧ st.regs 5 = L_w_h ∧ st.regs 6 = vCap_h ∧
        st.regs 7 = eCap_h ∧ st.regs 8 = handlesOut ∧ st.regs 9 = heap ∧
        st.regs 19 = heap + rEnd ∧ st.regs 20 = guestHndBase ∧ st.mem = mem2)
      (forRange 21 (.const 0) (.reg 4)
        (.assign 22 (.load (.bin .add (.reg 20) (.reg 21))) ;;
         .store (.bin .add (.reg 8) (.reg 21)) (.reg 19) ;;
         .call 19 (bRep + 6) [.reg 9, .reg 22, .reg 19, .reg 6, .reg 7, .reg 5]))
      (normalPost (LInv k_nat))
      (fun _ => (k_nat - 0) * (repackOneLSFCost n0 m0 L_w_g + 50 + (Expr.reg 4).size + 8) +
        ((Expr.const 0).size + (Expr.reg 4).size + 5)) := by
    refine Triple.forRange_const (Inv := LInv) (repackOneLSFCost n0 m0 L_w_g + 50) 0 k_nat (Nat.zero_le _)
      (by omega) (fun _ => by omega)
      (fun st hst => by
        rcases hst with ⟨q4, q5, q6, q7, q8, q9, q19, q20, hmeq⟩
        exact ⟨by eval_expr, q4, q5, q6, q7, q8, q9, q19, q20, by simp,
          by rw [hmeq]; exact hz2, fun _ _ _ => by rw [hmeq],
          fun _ _ _ => by rw [hmeq], fun _ hj => by omega⟩)
      (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h4 := hi.1; eval_expr)
      (fun i _ hilt st ω' hi => by
        rcases hi with ⟨q4, q5, q6, q7, q8, q9, q19, q20, q21, hz_i, hgw_i, hlo_i, hdone_i⟩
        obtain ⟨hhnd_g, hrep_g, hGV_eq, hGm_le, hvCap_le, heCap_le, hLwg_eq, hLw_le,
          hn0_eq, hm0_eq, htM_i, hend_g⟩ := hguest i hilt
        have haddr_ge : heap + rEnd ≤ hAddr i := hostHandleAddr_mono (Nat.zero_le i)
        have haddr_next : hAddr (i + 1) =
            lsfEndAddr (hAddr i) vCap_h eCap_h (x_g i).n0 (x_g i).tM L_w_h := by
          dsimp only [hAddr, hostHandleAddr, lsfEndAddr]; rw [hn0_eq]
        have haddr_next_lt : hAddr (i + 1) < 2 ^ w := by
          have hmul_le : (i + 1) * lsfStaticSize vCap_h eCap_h n0 n0 L_w_h ≤
              k_nat * lsfStaticSize vCap_h eCap_h n0 n0 L_w_h :=
            Nat.mul_le_mul_right _ hilt
          exact lt_of_le_of_lt (hostHandleAddr_le_mul htM_le (i + 1) hilt) (by omega)
        have haddr_i_lt : hAddr i < 2 ^ w :=
          lt_of_le_of_lt (hostHandleAddr_mono (Nat.le_succ i)) haddr_next_lt
        have hgh_lt : guestHndBase + i < 2 ^ w := by omega
        have hgh_mem : st.mem (guestHndBase + i) = hs_g i := by
          rw [hgw_i _ (by omega) (by omega)]; exact hhnd_g
        have hhsg_w : hs_g i < 2 ^ w := by
          have : hs_g i < (x_g i).endAddr (hs_g i) := by
            have := lsfHdr_lt_end (hs_g i) (x_g i).vCap (x_g i).eCap (x_g i).n0 (x_g i).tM (x_g i).L_w
            dsimp only [LSFConcrete.endAddr]
            unfold lsfHdrSize at this; omega
          omega
        change ∃ o st' c, Runs w p ω' _ ⟨st.mem, st.regs, st.pos⟩ o st' c ∧ _
        refine runs_start_le ?_
        refine runs_seq_assign_flat (v := hs_g i) (by eval_expr) ?_
        refine runs_seq_store_flat (x := handlesOut + i) (v := hAddr i)
          (by simp [Expr.eval, BinOp.eval, q8, q21, show handlesOut + i < 2 ^ w by omega])
          (by simp [Expr.eval, q19]) ?_
        set mem_s := Function.update st.mem (handlesOut + i) (hAddr i)
        have hmem_s_gw : ∀ a, heap ≤ a → a < heap + rEnd → mem_s a = mem2 a := fun a ha1 ha2 => by
          dsimp only [mem_s]; rw [Function.update_of_ne (by omega)]; exact hgw_i a ha1 ha2
        have hrep_s : (LSFRep h).rep (hs_g i) (S i) (x_g i) (fun a => mem_s (heap + a)) :=
          (lsfRep_local h (hs_g i) (S i) (x_g i) (fun a => mem2 (heap + a))
            (fun a => mem_s (heap + a)) fun a ha => by
              have ha2 : a < rEnd := lt_of_lt_of_le ha.2 hend_g
              exact (hmem_s_gw (heap + a) (Nat.le_add_right _ _) (by omega)).symm).1 hrep_g
        have hmemW_s : ∀ a, heap + hs_g i ≤ a → a < heap + (x_g i).endAddr (hs_g i) →
            mem_s a < 2 ^ w := fun a ha1 ha2 => by
          rw [hmem_s_gw a (by omega) (by omega)]; exact hMemW2 a (by omega) (by omega)
        have hzero_s : ∀ a, hAddr i ≤ a →
            a < lsfEndAddr (hAddr i) vCap_h eCap_h (x_g i).n0 (x_g i).tM L_w_h →
            mem_s a = 0 := fun a ha1 _ => by
          dsimp only [mem_s]; rw [Function.update_of_ne (by omega)]; exact hz_i a ha1
        obtain ⟨st_r, c_r, hrun_r, hrep_r, hfr_r, hc_r⟩ :=
          repackOneLSFProc_runs (p := p) (w := w) (h := h) (ω := ω') (pos := st.pos)
            hw hRep hCopy hLog hmemW_s hrep_s hGV_eq (by omega) hvCap_le heCap_le
            (by rw [hLwg_eq]; exact hLw_le) (by omega) (by rw [← haddr_next]; exact haddr_next_lt)
            hLwh_w (by omega) hzero_s
        refine ⟨.normal, ⟨st_r.mem, Function.update (Function.update st.regs 22 (hs_g i)) 19
          (lsfEndAddr (hAddr i) vCap_h eCap_h (x_g i).n0 (x_g i).tM L_w_h), st_r.pos⟩,
          argsSize [.reg 9, .reg 22, .reg 19, .reg 6, .reg 7, .reg 5] + c_r + 1,
          runs_call_iff.mpr ⟨[heap, hs_g i, hAddr i, vCap_h, eCap_h, L_w_h], _,
            .returned (lsfEndAddr (hAddr i) vCap_h eCap_h (x_g i).n0 (x_g i).tM L_w_h),
            st_r, c_r, by eval_expr, hpOne, hrun_r, rfl, rfl, rfl⟩, ?_,
          by simp [argsSize, Expr.size, hn0_eq, hm0_eq, hLwg_eq] at hc_r ⊢; omega⟩
        rw [← haddr_next]
        refine ⟨⟨by simp [q4], by simp [q5], by simp [q6], by simp [q7], by simp [q8],
          by simp [q9], by simp, by simp [q20], by simp, ?_, ?_, ?_, ?_⟩, by simp [q21]⟩
        · intro z hz
          have hstep_le : hAddr i ≤ hAddr (i + 1) := hostHandleAddr_mono (Nat.le_succ i)
          rw [hfr_r z (Or.inr (by rw [← haddr_next]; exact hz))]
          dsimp only [mem_s]
          rw [Function.update_of_ne (by omega)]
          exact hz_i z (le_trans hstep_le hz)
        · intro a ha1 ha2
          rw [hfr_r a (Or.inl (by omega))]
          exact hmem_s_gw a ha1 ha2
        · intro z hz hne
          rw [hfr_r z (Or.inl (by omega))]
          dsimp only [mem_s]
          rw [Function.update_of_ne (by omega)]
          exact hlo_i z hz (Or.elim hne Or.inl (fun h => Or.inr (by omega)))
        · intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
          · have hfr_hnd : st_r.mem (handlesOut + j) = st.mem (handlesOut + j) := by
              rw [hfr_r _ (Or.inl (by omega))]
              dsimp only [mem_s]; rw [Function.update_of_ne (by omega)]
            have hhj_le : (x_h j).endAddr (hAddr j) ≤ hAddr i := by
              have h1 : (x_h j).endAddr (hAddr j) = hAddr (j + 1) := by
                dsimp only [LSFConcrete.endAddr, x_h, hAddr, hostHandleAddr, lsfEndAddr]
                rw [(hguest j (lt_trans hj' hilt)).2.2.2.2.2.2.2.2.1]
              rw [h1]; exact hostHandleAddr_mono hj'
            refine ⟨hfr_hnd.trans (hdone_i j hj').1, ?_⟩
            exact (lsfRep_local h (hAddr j) (S j) (x_h j) st.mem st_r.mem fun a ha => by
              have ha_lt : a < hAddr i := lt_of_lt_of_le ha.2 hhj_le
              have ha_ge : heap ≤ a := le_trans (le_trans (Nat.le_add_right _ _)
                (hostHandleAddr_mono (Nat.zero_le j))) ha.1
              rw [hfr_r a (Or.inl ha_lt)]
              dsimp only [mem_s]; rw [Function.update_of_ne (by omega)]).1 (hdone_i j hj').2
          · refine ⟨?_, hrep_r⟩
            rw [hfr_r _ (Or.inl (by omega))]
            dsimp only [mem_s]; exact Function.update_self _ _ _)
  exact Triple.conseq hloop (fun _ h => h) (fun o st h => by
    cases o with
    | normal => exact ⟨h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩
    | returned _ => exact h.elim) (fun _ => by
      simp only [Nat.sub_zero, Expr.size]
      have h1 : k_nat * (repackOneLSFCost n0 m0 L_w_g + 50 + 1 + 8) ≤
          k_nat * (repackOneLSFCost n0 m0 L_w_g + 60) :=
        Nat.mul_le_mul_left k_nat (by omega)
      omega)

end MinCostFlow.SparseCore.Program
