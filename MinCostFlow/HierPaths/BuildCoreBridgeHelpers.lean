module

public import MinCostFlow.HierPaths.BuildProgContracts
public import MinCostFlow.HierPaths.BuildProgTags
public import MinCostFlow.ExpanderDecomp.CoreOuter
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Core Bridge: Counterexamples, Minimal Contract Relaxation, and Helper Procedures

Compares `CoreOuter.coreAdapterContract` (`MinCostFlow/ExpanderDecomp/CoreOuter.lean`) with
`BuildProgContracts.ProvidesCore` (`MinCostFlow/HierPaths/BuildProgContracts.lean`).

1. **Three counterexamples** show why `coreAdapterContract` cannot meet `ProvidesCore` with a
   uniform time multiplier `K`, a uniform space function `sC : ℕ → ℕ`, and unconstrained `r`:
   * `coreAdapter_fails_r_gt_ell`: at `M = 0, r = 2, q = 1, G = ⟨2, []⟩`, `CoreProcContract.pre`
     holds while `coreAdapterContract.pre` is unsatisfiable (`r > ell M`).
   * `coreAdapterSpace_exceeds_uniform_sC`: for every `sC : ℕ → ℕ` and `C_sp ≥ 1`, at
     `M = sC 2, r = 1, q = 1, G = ⟨2, []⟩`, `sC G.encode.length < coreAdapterSpace`.
   * `coreAdapterSpace_exceeds_const_K_cost`: for every constant `K : ℕ` and `C_sp ≥ 1`, at
     `M = K, r = 1, q = 1, G = ⟨2, []⟩`, `K * (coreAdapterCost + |G| + 1) < coreAdapterSpace`,
     so zeroing the adapter's bump-allocated scratch `[h', v2)` to restore
     `v = h + (coreResultWords res).length ∧ ZeroFrom mem' v` cannot fit in constant-`K` time.
2. **Smallest contract relaxation (`CoreProcBumpContract` / `ProvidesCoreBump`)**: adds `r ≤ ell M`,
   lets `sC` depend on `(M, r)` (`coreBridgeSpace`), and relaxes `v = h + (coreResultWords res).length`
   to `h + (coreResultWords res).length ≤ v` (matching `buildLevelContract` and `coreAdapterContract`).
3. **Helper procedures**:
   * `coreBridgeLevelProc`: computes `coreLevel M r n` from `[M, r, n]` without modifying memory
     in `O(ell M + r)` steps.
   * `coreBridgePackProc`: converts `CoreOutAt mem outAddr res` into sorted
     `ListAt mem' h (coreResultWords res)` via `O(n)` bitmap counting sort.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-! ## 1. Three Counterexamples Between `coreAdapterContract` and `ProvidesCore` -/

/-- **Counterexample (`coreHeapContract` does not ask `r ≤ ell M`):**
At `M = 0` (`ell 0 = 1`), `r = 2`, `q = 1`, `G = ⟨2, []⟩`, `coreHeapContract.pre` holds for
suitable `w, sC`, whereas `coreAdapterContract 0 2 ...` has an unsatisfiable precondition. -/
theorem coreAdapter_fails_r_gt_ell (K C_core C_sp w : ℕ) (coreCost : ℕ → Graph → ℕ)
    (sC : ℕ → ℕ) (hw : 2 + sC 2 < 2 ^ w) :
    let G : Graph := ⟨2, []⟩
    (coreHeapContract w K 0 2 coreCost sC 1 G).pre [1, 0, 0, 2, 2] (initMem G.encode) ∧
      ∀ args mem, ¬ (coreAdapterContract 0 2 coreCost C_core C_sp w).pre args mem := by
  intro G
  have hEnc : G.encode.length = 2 := by simp [G, Graph.encode]
  refine ⟨?_, ?_⟩
  · refine ⟨⟨0, 2, rfl,
        fun i hi => by simp [initMem, hi],
        by omega, by decide,
        fun _ h => by simp [G] at h,
        fun _ h => by simp [G] at h,
        by have := four_le_NOf 0 2; simp [G]; omega,
        fun _ _ => by simp [G, Graph.deg, Graph.degIn, Graph.inside]⟩,
      fun a ha => by
        have ha2 : 2 ≤ a := by simpa [heapArg] using ha
        simp [initMem, List.getElem?_eq_none (show G.encode.length ≤ a by omega)],
      by simp only [heapArg, List.getLastD, hEnc]; exact hw⟩
  · intro args mem hpre
    rcases hpre with ⟨_, _, _, _, _, _, _, _, hrl, _⟩
    have hell : ell 0 = 1 := by decide
    omega

/-- **Counterexample (uniform `sC : ℕ → ℕ` independent of `(M, r)`):**
For every `sC : ℕ → ℕ` and `C_sp ≥ 1`, at `M = sC 2`, `r = 1`, `q = 1`, `G = ⟨2, []⟩`,
`sC G.encode.length` is strictly smaller than `coreAdapterSpace`. -/
theorem coreAdapterSpace_exceeds_uniform_sC (sC : ℕ → ℕ) {C_sp : ℕ} (hC : 1 ≤ C_sp) :
    let M := sC 2
    let G : Graph := ⟨2, []⟩
    sC G.encode.length < coreAdapterSpace C_sp M 1 G.n (coreAdapterCost M 1 1 G) := by
  intro M G
  have hN : 2 * M + 2 ≤ NOf M 1 := by
    simpa [pow_one] using two_mul_add_two_le_NOf_pow (M := M) (r := 1) le_rfl
  have hL : 4 ≤ LParam M := four_le_LParam M
  have hbase : NOf M 1 ≤ coreSpaceBase M 1 := by
    unfold coreSpaceBase
    have h1 : NOf M 1 ≤ 2048 * LParam M * (NOf M 1) ^ 1 + 3 := by
      simp only [pow_one]; nlinarith
    exact le_trans h1 (Nat.le_self_pow (by decide) _)
  have hsp : coreSpaceBase M 1 ≤ coreAdapterSpace C_sp M 1 G.n (coreAdapterCost M 1 1 G) := by
    unfold coreAdapterSpace
    have h1 : coreSpaceBase M 1 ≤ coreSpaceBase M 1 * (coreAdapterCost M 1 1 G + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    exact le_trans (by omega) (Nat.le_mul_of_pos_left _ hC)
  have hlen : G.encode.length = 2 := by simp [G, Graph.encode]
  rw [hlen]
  omega

/-- **Counterexample (zeroing bump-allocated scratch exceeds constant-`K` cost):**
For every constant `K : ℕ` and `C_sp ≥ 1`, at `M = K`, `r = 1`, `q = 1`, `G = ⟨2, []⟩`,
the core contract's total time budget `K * (coreAdapterCost + |G| + 1)` is strictly smaller than
`coreAdapterSpace` (the size of the scratch region `[h', v2)` that `coreAdapterContract` may leave
nonzero). -/
theorem coreAdapterSpace_exceeds_const_K_cost (K : ℕ) {C_sp : ℕ} (hC : 1 ≤ C_sp) :
    let M := K
    let G : Graph := ⟨2, []⟩
    K * (coreAdapterCost M 1 1 G + G.encode.length + 1) <
      coreAdapterSpace C_sp M 1 G.n (coreAdapterCost M 1 1 G) := by
  intro M G
  set cc := coreAdapterCost M 1 1 G
  have hN4 : 4 ≤ NOf M 1 := four_le_NOf M 1
  have hN : 2 * M + 2 ≤ NOf M 1 := by
    simpa [pow_one] using two_mul_add_two_le_NOf_pow (M := M) (r := 1) le_rfl
  have hL : 4 ≤ LParam M := four_le_LParam M
  have hW1 : 1 ≤ WParam ParamConfig.default M := by unfold WParam; omega
  have hcc_pos : 1 ≤ cc := by
    unfold cc coreAdapterCost
    exact Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) (Nat.pow_pos (by omega))) (Nat.pow_pos hW1)
  have hbase_gt : 4 * K < coreSpaceBase M 1 := by
    unfold coreSpaceBase
    have h1 : 4 * K < 2048 * LParam M * (NOf M 1) ^ 1 + 3 := by
      simp only [pow_one]; nlinarith
    exact lt_of_lt_of_le h1 (Nat.le_self_pow (by decide) _)
  have hlen : G.encode.length = 2 := by simp [G, Graph.encode]
  rw [hlen]
  have h1 : K * (cc + 2 + 1) ≤ 4 * K * (cc + 1) := by nlinarith
  have h2 : 4 * K * (cc + 1) < coreSpaceBase M 1 * (cc + 1) :=
    Nat.mul_lt_mul_of_pos_right hbase_gt (Nat.succ_pos cc)
  have h3 : coreSpaceBase M 1 * (cc + 1) ≤ coreAdapterSpace C_sp M 1 G.n cc := by
    unfold coreAdapterSpace
    exact le_trans (by omega) (Nat.le_mul_of_pos_left _ hC)
  omega

/-! ## 2. Minimal Contract Relaxation (`CoreProcBumpContract`) and Set / Cost Helpers -/

/-- Minimal relaxation of `CoreProcContract` that matches `coreAdapterContract`'s bump-heap
discipline: adds `r ≤ ell M` and relaxes `v = h + (coreResultWords res).length` to
`h + (coreResultWords res).length ≤ v`. -/
def CoreProcBumpContract (w K M r : ℕ) (coreCost : ℕ → Graph → ℕ) (sC : ℕ → ℕ)
    (q : ℕ) (G : Graph) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ (gAddr h : ℕ), args = [q, gAddr, M, r, h] ∧ GraphAt mem gAddr G ∧
      gAddr + G.encode.length ≤ h ∧ q ≤ r ∧ r ≤ ell M ∧ G.IsValid ∧ G.IsLoopless ∧
      G.n ≤ (NOf M r) ^ q ∧ ∀ v < G.n, G.deg v ≤ deltaParam M)
    (fun _ _ _ => True)
    (fun _ _ => K * (coreCost q G + G.encode.length + 1))
    (fun _ _ => sC G.encode.length)
  { C with post := fun args mem v mem' =>
      C.post args mem v mem' ∧
        ∃ (gAddr h : ℕ) (res : CoreResult), args = [q, gAddr, M, r, h] ∧
          ListAt mem' h (coreResultWords res) ∧ h + (coreResultWords res).length ≤ v ∧
          CoreOutcomeSpec ParamConfig.default M q G res }

/-- Bump-heap counterpart of `ProvidesCore`: every valid call `(q, G)` with `r ≤ ell M` writes a
certified `coreResultWords res` at `h`, returns `v ≥ h + (coreResultWords res).length` with
`ZeroFrom mem' v`, and runs within `K * (coreCost q G + G.encode.length + 1)` steps. -/
def ProvidesCoreBump (w K M r : ℕ) (coreCost : ℕ → Graph → ℕ) (sC : ℕ → ℕ)
    (p : Program) (f : ℕ) : Prop :=
  ∀ q G, MeetsContract w p f (CoreProcBumpContract w K M r coreCost sC q G)

/-- Scratch space envelope for the core bridge at parameters `(C_sp, M, r)`: covers the
`6 + 3 * G.n` packing region, intermediate word bounds `2 * (NOf M r) ^ (r + 1)`, and
`coreAdapterSpace` for every graph `G` with `G.n ≤ (NOf M r) ^ r`. -/
def coreBridgeSpace (C_sp M r _gLen : ℕ) : ℕ :=
  6 + 3 * (NOf M r) ^ r + 2 * (NOf M r) ^ (r + 1) +
    coreAdapterSpace C_sp M r ((NOf M r) ^ r)
      ((NOf M r) ^ (r + 2) * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10)) + 40

/-- `coreAdapterSpace` is monotone in `n` and `ccost`. -/
lemma coreAdapterSpace_mono {C_sp M r n₁ n₂ c₁ c₂ : ℕ} (hn : n₁ ≤ n₂) (hc : c₁ ≤ c₂) :
    coreAdapterSpace C_sp M r n₁ c₁ ≤ coreAdapterSpace C_sp M r n₂ c₂ := by
  unfold coreAdapterSpace
  apply Nat.mul_le_mul_left
  have h1 : coreSpaceBase M r * (c₁ + 1) ≤ coreSpaceBase M r * (c₂ + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (n₁ + 3) ^ 5 ≤ (n₂ + 3) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  omega

/-- For any `q ≤ r` and `G.n ≤ (NOf M r) ^ q`, the packing prefix plus `coreAdapterSpace` fits
inside `coreBridgeSpace C_sp M r gLen`. -/
lemma coreAdapterSpace_le_coreBridgeSpace {C_sp M r q gLen : ℕ} {G : Graph}
    (hqr : q ≤ r) (hn : G.n ≤ (NOf M r) ^ q) :
    6 + 3 * G.n + coreAdapterSpace C_sp M r G.n (coreAdapterCost M r q G) + 20 ≤
      coreBridgeSpace C_sp M r gLen := by
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hn_r : G.n ≤ (NOf M r) ^ r := le_trans hn (Nat.pow_le_pow_right hN1 hqr)
  have hcc : coreAdapterCost M r q G ≤
      (NOf M r) ^ (r + 2) * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) := by
    unfold coreAdapterCost
    have hpow : G.n * (NOf M r) ^ 2 ≤ (NOf M r) ^ (r + 2) := by
      rw [pow_add]; exact Nat.mul_le_mul_right _ hn_r
    exact Nat.mul_le_mul_right _ hpow
  have hsp := coreAdapterSpace_mono (C_sp := C_sp) (M := M) (r := r) hn_r hcc
  unfold coreBridgeSpace
  omega

/-- Extract the underlying vertex set from a `CoreResult`. -/
def coreResultSet : CoreResult → Finset ℕ
  | .cut U => U
  | .expander S => S

/-- `coreResultWords res` is the 4-word header `[0, 1, 1 + |U|, tag]` followed by `finsetWords U`. -/
lemma coreResultWords_eq_header_append (res : CoreResult) :
    coreResultWords res =
      [0, 1, 1 + (coreResultSet res).card, coreTag res] ++ finsetWords (coreResultSet res) := by
  cases res with
  | cut U =>
    simp [coreResultWords, coreResultSet, coreTag, layoutList, csrList, csrOffsets, csrData,
      List.range_succ, finsetWords]
  | expander S =>
    simp [coreResultWords, coreResultSet, coreTag, layoutList, csrList, csrOffsets, csrData,
      List.range_succ, finsetWords]

/-- Filtering `List.range n` by membership in `U ⊆ Finset.range n` produces `finsetWords U`. -/
lemma range_filter_eq_finsetWords {n : ℕ} {U : Finset ℕ} (hU : U ⊆ Finset.range n) :
    (List.range n).filter (fun v => decide (v ∈ U)) = finsetWords U := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact (List.pairwise_lt_range.imp fun h => Nat.le_of_lt h).filter _
  · exact Finset.pairwise_sort ..
  · have hnd : ((List.range n).filter (fun v => decide (v ∈ U))).Nodup :=
      List.nodup_range.filter _
    apply (List.perm_ext_iff_of_nodup hnd (Finset.sort_nodup ..)).mpr
    intro v
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, Finset.mem_sort]
    exact ⟨fun h => h.2, fun hv => ⟨Finset.mem_range.mp (hU hv), hv⟩⟩

/-- When `G.n ≤ 1`, `.expander G.verts` trivially satisfies `CoreOutcomeSpec` for every `(M, q)`. -/
lemma coreOutcomeSpec_expander_verts_le_one {M q : ℕ} {G : Graph} (hn : G.n ≤ 1) :
    CoreOutcomeSpec ParamConfig.default M q G (.expander G.verts) := by
  refine ⟨Finset.Subset.refl _, ?_, ?_⟩
  · simp [Graph.verts]; omega
  · intro A hA hne hneX
    have hGcard : G.verts.card ≤ 1 := by simpa [Graph.verts] using hn
    have hA1 : 1 ≤ A.card := Finset.card_pos.mpr hne
    exact False.elim (hneX (Finset.eq_of_subset_of_card_le hA (by omega)))

/-- `CoreOutcomeSpec` is monotone in the level `q` (since `1 / P_q` is decreasing in `q`). -/
lemma coreOutcomeSpec_mono_q {M q' q : ℕ} {G : Graph} {res : CoreResult}
    (hq : q' ≤ q) (h : CoreOutcomeSpec ParamConfig.default M q' G res) :
    CoreOutcomeSpec ParamConfig.default M q G res := by
  cases res with
  | cut U => exact h
  | expander S =>
    exact ⟨h.1, h.2.1, isExpansionExpanderOn_mono (inv_PParam_le_of_le ParamConfig.default M hq) h.2.2⟩

/-! ## 3. Helper Procedure 1: Computing `coreLevel M r n` (`coreBridgeLevelProc`) -/

/-- Deterministic Word-RAM procedure taking `[M, r, n]` (with `1 ≤ r ≤ ell M`, `2 ≤ n ≤ (NOf M r)^r`)
and returning `coreLevel M r n = Nat.clog (NOf M r) n` without modifying memory. -/
def coreBridgeLevelProc : Stmt :=
  -- Stage 1: reg 4 := ell M
  .assign 3 (.bin .add (.bin .mul (.const 2) (.reg 0)) (.const 2)) ;;
  .assign 4 (.const 0) ;;
  .assign 5 (.const 1) ;;
  .loop (.bin .lt (.reg 5) (.reg 3))
    (.assign 5 (.bin .mul (.const 2) (.reg 5)) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1))) ;;
  -- Stage 2: reg 7 := NOf M r = 2 ^ max 2 (ceilDiv (ell M) r)
  .assign 6 (.bin .div (.bin .sub (.bin .add (.reg 4) (.reg 1)) (.const 1)) (.reg 1)) ;;
  .cond (.bin .lt (.reg 6) (.const 2)) (.assign 6 (.const 2)) .nop ;;
  .assign 7 (.const 1) ;;
  forRange 8 (.const 0) (.reg 6)
    (.assign 7 (.bin .mul (.const 2) (.reg 7))) ;;
  -- Stage 3: reg 9 := Nat.clog (reg 7) (reg 2)
  .assign 9 (.const 0) ;;
  .assign 10 (.const 1) ;;
  .loop (.bin .lt (.reg 10) (.reg 2))
    (.assign 10 (.bin .mul (.reg 10) (.reg 7)) ;;
     .assign 9 (.bin .add (.reg 9) (.const 1))) ;;
  .ret (.reg 9)

theorem coreBridgeLevelProc_noRand : coreBridgeLevelProc.NoRand := by
  simp [coreBridgeLevelProc, forRange, forUp, Stmt.NoRand]

/-- Step bound for `coreBridgeLevelProc`. -/
def coreBridgeLevelCost (M r : ℕ) : ℕ :=
  80 * (ell M + r) + 120

/-- Contract for `coreBridgeLevelProc`: computes `coreLevel M r n` without modifying memory. -/
def coreBridgeLevelContract (w : ℕ) : Contract where
  pre args _ :=
    ∃ M r n : ℕ,
      args = [M, r, n] ∧
      1 ≤ r ∧ r ≤ ell M ∧
      2 ≤ n ∧ n ≤ (NOf M r) ^ r ∧
      4 * M + 16 < 2 ^ w ∧
      NOf M r * n + 16 < 2 ^ w
  post args mem v mem' :=
    v = coreLevel (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) ∧ mem' = mem
  cost args _ :=
    coreBridgeLevelCost (args.getD 0 0) (args.getD 1 0)

private lemma ell_loop_bridge {w M r n : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hw : 4 * M + 16 < 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = M ∧ st.regs 1 = r ∧ st.regs 2 = n ∧
        st.regs 3 = 2 * M + 2 ∧ st.regs 4 = 0 ∧ st.regs 5 = 1 ∧ st.mem = mem₀)
      (.loop (.bin .lt (.reg 5) (.reg 3))
        (.assign 5 (.bin .mul (.const 2) (.reg 5)) ;;
         .assign 4 (.bin .add (.reg 4) (.const 1))))
      (normalPost fun st' =>
        st'.regs 0 = M ∧ st'.regs 1 = r ∧ st'.regs 2 = n ∧
        st'.regs 4 = ell M ∧ st'.mem = mem₀)
      (fun _ => 25 * (ell M + 1)) := by
  set E := ell M
  have hlt1 : 1 < 2 ^ w := by omega
  have hlt2 : 2 < 2 ^ w := by omega
  have hloop := Triple.loop_const_normal (w := w) (p := p)
    (e := .bin .lt (.reg 5) (.reg 3))
    (body := .assign 5 (.bin .mul (.const 2) (.reg 5)) ;;
      .assign 4 (.bin .add (.reg 4) (.const 1)))
    (Inv := fun st => st.regs 0 = M ∧ st.regs 1 = r ∧ st.regs 2 = n ∧
      st.regs 3 = 2 * M + 2 ∧ st.regs 4 ≤ E ∧ st.regs 5 = 2 ^ st.regs 4 ∧ st.mem = mem₀)
    (Q := fun st' => st'.regs 0 = M ∧ st'.regs 1 = r ∧ st'.regs 2 = n ∧
      st'.regs 4 = E ∧ st'.mem = mem₀)
    (fun st => E - st.regs 4)
    (fun st => if 2 ^ st.regs 4 < 2 * M + 2 then 1 else 0)
    10
    (fun st ⟨_, _, _, h3, _, h5, _⟩ => by
      by_cases hlt : 2 ^ st.regs 4 < 2 * M + 2
      · simp [Expr.eval, BinOp.eval, h5, h3, hlt, hlt1]
      · simp [Expr.eval, BinOp.eval, h5, h3, hlt])
    (fun st ⟨h0, h1, h2, _, h4le, _, hmem⟩ hcond => by
      have hge : 2 * M + 2 ≤ 2 ^ st.regs 4 := by
        by_contra hlt; have hlt' : 2 ^ st.regs 4 < 2 * M + 2 := Nat.lt_of_not_le hlt
        simp [hlt'] at hcond
      have hclog : E ≤ st.regs 4 := Nat.clog_le_of_le_pow hge
      exact ⟨h0, h1, h2, by omega, hmem⟩)
    (fun st ⟨h0, h1, h2, h3, h4le, h5, hmem⟩ hcond => by
      have hpow_lt : 2 ^ st.regs 4 < 2 * M + 2 := by
        by_contra h; simp [h] at hcond
      have hlt : st.regs 4 < E := by
        by_contra hge
        have h4eq : st.regs 4 = E := by omega
        have hpow_ge : 2 * M + 2 ≤ 2 ^ E := Nat.le_pow_clog (by decide) (2 * M + 2)
        rw [h4eq] at hpow_lt; omega
      have hmul_lt : 2 * 2 ^ st.regs 4 < 2 ^ w := by omega
      have h4_lt : st.regs 4 + 1 < 2 ^ w := by
        have : st.regs 4 < 2 ^ st.regs 4 := Nat.lt_pow_self one_lt_two; omega
      intro s ω hs; subst s
      set st1 : State := { st with regs := Function.update st.regs 5 (2 * 2 ^ st.regs 4) }
      set st2 : State := { st1 with regs := Function.update st1.regs 4 (st.regs 4 + 1) }
      have hs1 : Runs w p ω (.assign 5 (.bin .mul (.const 2) (.reg 5))) st .normal st1 4 := by
        rw [runs_assign_iff]
        exact ⟨2 * 2 ^ st.regs 4, by simp [Expr.eval, BinOp.eval, h5, hlt2, hmul_lt],
          rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1))) st1 .normal st2 4 := by
        rw [runs_assign_iff]
        have h4' : st1.regs 4 = st.regs 4 := by simp [st1]
        exact ⟨st.regs 4 + 1, by simp [Expr.eval, BinOp.eval, h4', h4_lt, hlt1],
          rfl, rfl, by simp [Expr.size]⟩
      refine ⟨.normal, st2, 9, runs_seq_iff.mpr (Or.inr ⟨st1, 4, 4, hs1, hs2, rfl⟩), ?_, Nat.le_succ 9⟩
      exact ⟨⟨by simp [st2, st1, h0], by simp [st2, st1, h1], by simp [st2, st1, h2],
        by simp [st2, st1, h3], by simp [st2]; omega,
        by simp [st2, st1, Nat.pow_succ'], by simp [st2, st1, hmem]⟩, by simp [st2]; omega⟩)
  exact hloop.conseq
    (fun st ⟨h0, h1, h2, h3, h4, h5, hmem⟩ =>
      ⟨h0, h1, h2, h3, by rw [h4]; exact Nat.zero_le E, by simp [h4, h5], hmem⟩)
    (fun _ _ h => h)
    (fun st ⟨_, _, _, _, h4, _, _⟩ => by simp [Expr.size, h4]; omega)

private lemma pow2_loop_bridge {w M r n e : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (h2w : 2 < 2 ^ w) (he_w : e + 1 < 2 ^ w) (hpow_w : 2 ^ e < 2 ^ w) :
    Triple w p
      (fun st => st.regs 0 = M ∧ st.regs 1 = r ∧ st.regs 2 = n ∧
        st.regs 6 = e ∧ st.regs 7 = 1 ∧ st.mem = mem₀)
      (forRange 8 (.const 0) (.reg 6) (.assign 7 (.bin .mul (.const 2) (.reg 7))))
      (normalPost fun st' =>
        st'.regs 2 = n ∧ st'.regs 7 = 2 ^ e ∧ st'.mem = mem₀)
      (fun _ => 20 * (e + 1)) := by
  have hlt1 : 1 < 2 ^ w := by omega
  have hlt2 : 2 < 2 ^ w := h2w
  have hloop := Triple.forRange_const (p := p) (r := 8) (lo := .const 0) (hi := .reg 6)
    (body := .assign 7 (.bin .mul (.const 2) (.reg 7)))
    (P := fun st => st.regs 0 = M ∧ st.regs 1 = r ∧ st.regs 2 = n ∧
      st.regs 6 = e ∧ st.regs 7 = 1 ∧ st.mem = mem₀)
    (Inv := fun i st => st.regs 2 = n ∧ st.regs 6 = e ∧ st.regs 7 = 2 ^ i ∧
      st.regs 8 = i ∧ st.mem = mem₀)
    5 0 e (Nat.zero_le e) hlt1 (fun _ => by omega)
    (fun st ⟨_, _, h2, h6, h7, hm⟩ => ⟨by eval_expr, by simp [h2], by simp [h6], by simp [h7], by simp, hm⟩)
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by have h6 : st.regs 6 = e := hi.2.1; eval_expr)
    (fun i _ hilt => by
      intro st ω ⟨h2, h6, h7, h8, hm⟩
      have hmul : 2 * 2 ^ i < 2 ^ w := by
        have : 2 ^ (i + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) hilt
        rw [Nat.pow_succ'] at this; omega
      set st' : State := { st with regs := Function.update st.regs 7 (2 * 2 ^ i) }
      refine ⟨.normal, st', 4, ?_, ?_, Nat.le_succ 4⟩
      · rw [runs_assign_iff]
        exact ⟨2 * 2 ^ i, by simp [Expr.eval, BinOp.eval, h7, hlt2, hmul], rfl, rfl, by simp [Expr.size]⟩
      · exact ⟨⟨by simp [st', h2], by simp [st', h6], by simp [st', Nat.pow_succ'],
          by simp [st'], hm⟩, by simp [st', h8]⟩)
  exact hloop.conseq (fun _ h => h)
    (fun o st' h => by cases o with | returned _ => exact False.elim h | normal => exact ⟨h.1, h.2.2.1, h.2.2.2.2⟩)
    (fun _ _ => by simp [Expr.size]; omega)

private lemma clog_loop_bridge {w N n : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hN : 2 ≤ N) (hw : N * n + 16 < 2 ^ w) :
    Triple w p
      (fun st => st.regs 2 = n ∧ st.regs 7 = N ∧ st.regs 9 = 0 ∧ st.regs 10 = 1 ∧ st.mem = mem₀)
      (.loop (.bin .lt (.reg 10) (.reg 2))
        (.assign 10 (.bin .mul (.reg 10) (.reg 7)) ;;
         .assign 9 (.bin .add (.reg 9) (.const 1))))
      (normalPost fun st' => st'.regs 9 = Nat.clog N n ∧ st'.mem = mem₀)
      (fun _ => 25 * (Nat.clog N n + 1)) := by
  set Q := Nat.clog N n
  have hlt1 : 1 < 2 ^ w := by omega
  have hloop := Triple.loop_const_normal (w := w) (p := p)
    (e := .bin .lt (.reg 10) (.reg 2))
    (body := .assign 10 (.bin .mul (.reg 10) (.reg 7)) ;;
      .assign 9 (.bin .add (.reg 9) (.const 1)))
    (Inv := fun st => st.regs 2 = n ∧ st.regs 7 = N ∧ st.regs 9 ≤ Q ∧
      st.regs 10 = N ^ st.regs 9 ∧ st.mem = mem₀)
    (Q := fun st' => st'.regs 9 = Q ∧ st'.mem = mem₀)
    (fun st => Q - st.regs 9)
    (fun st => if N ^ st.regs 9 < n then 1 else 0)
    10
    (fun st ⟨h2, _, _, h10, _⟩ => by
      by_cases hlt : N ^ st.regs 9 < n
      · simp [Expr.eval, BinOp.eval, h10, h2, hlt, hlt1]
      · simp [Expr.eval, BinOp.eval, h10, h2, hlt])
    (fun st ⟨_, _, h9le, _, hmem⟩ hcond => by
      have hge : n ≤ N ^ st.regs 9 := by
        by_contra hlt; have hlt' : N ^ st.regs 9 < n := Nat.lt_of_not_le hlt
        simp [hlt'] at hcond
      have hclog : Q ≤ st.regs 9 := Nat.clog_le_of_le_pow hge
      exact ⟨by omega, hmem⟩)
    (fun st ⟨h2, h7, h9le, h10, hmem⟩ hcond => by
      have hpow_lt : N ^ st.regs 9 < n := by by_contra h; simp [h] at hcond
      have hlt : st.regs 9 < Q := by
        by_contra hge
        have h9eq : st.regs 9 = Q := by omega
        have hpow_ge : n ≤ N ^ Q := Nat.le_pow_clog (by omega) n
        rw [h9eq] at hpow_lt; omega
      have hmul_lt : N ^ st.regs 9 * N < 2 ^ w := by
        have : N ^ st.regs 9 * N ≤ n * N := Nat.mul_le_mul_right N (le_of_lt hpow_lt)
        rw [Nat.mul_comm n N] at this; omega
      have h9_lt : st.regs 9 + 1 < 2 ^ w := by
        have : st.regs 9 < N ^ st.regs 9 := Nat.lt_pow_self (by omega)
        have : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
        omega
      intro s ω hs; subst s
      set st1 : State := { st with regs := Function.update st.regs 10 (N ^ st.regs 9 * N) }
      set st2 : State := { st1 with regs := Function.update st1.regs 9 (st.regs 9 + 1) }
      have hs1 : Runs w p ω (.assign 10 (.bin .mul (.reg 10) (.reg 7))) st .normal st1 4 := by
        rw [runs_assign_iff]
        exact ⟨N ^ st.regs 9 * N, by simp [Expr.eval, BinOp.eval, h10, h7, hmul_lt],
          rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w p ω (.assign 9 (.bin .add (.reg 9) (.const 1))) st1 .normal st2 4 := by
        rw [runs_assign_iff]
        have h9' : st1.regs 9 = st.regs 9 := by simp [st1]
        exact ⟨st.regs 9 + 1, by simp [Expr.eval, BinOp.eval, h9', h9_lt, hlt1],
          rfl, rfl, by simp [Expr.size]⟩
      refine ⟨.normal, st2, 9, runs_seq_iff.mpr (Or.inr ⟨st1, 4, 4, hs1, hs2, rfl⟩), ?_, Nat.le_succ 9⟩
      exact ⟨⟨by simp [st2, st1, h2], by simp [st2, st1, h7], by simp [st2]; omega,
        by simp [st2, st1, Nat.pow_succ], by simp [st2, st1, hmem]⟩, by simp [st2]; omega⟩)
  exact hloop.conseq
    (fun st ⟨h2, h7, h9, h10, hmem⟩ =>
      ⟨h2, h7, by rw [h9]; exact Nat.zero_le Q, by simp [h9, h10], hmem⟩)
    (fun _ _ h => h)
    (fun st ⟨_, _, h9, _, _⟩ => by simp [Expr.size, h9]; omega)

theorem coreBridgeLevelProc_meetsContract {w f : ℕ} {p : Program}
    (hf : p.procs[f]? = some coreBridgeLevelProc) :
    MeetsContract w p f (coreBridgeLevelContract w) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨M, r, n, rfl, hr1, hrl, hn2, hnr, hwM, hwNn⟩
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have hE1 : 1 ≤ ell M := one_le_ell M
  have hE_lt : ell M < 2 ^ ell M := Nat.lt_pow_self one_lt_two
  have h2E : 2 ^ ell M < 4 * M + 4 := by
    have hpred : 2 ^ (ell M - 1) < 2 * M + 2 :=
      Nat.pow_pred_clog_lt_self (b := 2) (by decide) (show 1 < 2 * M + 2 by omega)
    have hpow : 2 ^ ell M = 2 * 2 ^ (ell M - 1) := by
      have : ell M = (ell M - 1) + 1 := by omega
      conv_lhs => rw [this, Nat.pow_succ']
    omega
  have hcd_le : ceilDiv (ell M) r ≤ ell M := by
    unfold ceilDiv
    have h1 : ell M + r - 1 < r * (ell M + 1) := by
      have : ell M ≤ r * ell M := Nat.le_mul_of_pos_left _ hr1
      have : r * (ell M + 1) = r * ell M + r := by ring
      omega
    have := Nat.div_lt_of_lt_mul h1; omega
  set e := max 2 (ceilDiv (ell M) r)
  have hN_eq : 2 ^ e = NOf M r := rfl
  have hN4 : 4 ≤ NOf M r := four_le_NOf M r
  have hN_w : NOf M r < 2 ^ w := by
    have : NOf M r ≤ NOf M r * n := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have he_le : e ≤ ell M + 2 := by omega
  have hclog_le : Nat.clog (NOf M r) n ≤ r := coreLevel_le hnr
  refine runs_start_le ?_
  unfold coreBridgeLevelProc
  -- Stage 1
  refine runs_seq_assign_le (v := 2 * M + 2)
    (by simp [Expr.eval, BinOp.eval, startState, h2w, (by omega : 2 * M < 2 ^ w),
          (by omega : 2 * M + 2 < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := 1) (by simp [Expr.eval, h1w]) ?_
  refine runs_seq_triple_le (ell_loop_bridge (M := M) (r := r) (n := n) p mem hwM)
    ⟨by simp [startState], by simp [startState], by simp [startState],
      by simp, by simp, by simp, rfl⟩ ?_
  intro st1 ⟨h1_0, h1_1, h1_2, h1_4, h1_m⟩
  -- Stage 2: reg 6 := ceilDiv (ell M) r, then max with 2
  have hE_le : ell M ≤ 2 * M + 2 := Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self one_lt_two))
  have hEr_w : ell M + r < 2 ^ w := by omega
  have hEr1_w : ell M + r - 1 < 2 ^ w := by omega
  have hcd_w : (ell M + r - 1) / r < 2 ^ w := by
    have : (ell M + r - 1) / r = ceilDiv (ell M) r := rfl
    omega
  refine runs_seq_assign_le (v := ceilDiv (ell M) r)
    (by
      simp [Expr.eval, BinOp.eval, h1_4, h1_1, h1w, hEr_w, hEr1_w, hcd_w, ceilDiv]) ?_
  refine runs_seq_cond_le (v := if ceilDiv (ell M) r < 2 then 1 else 0)
    (by
      by_cases hlt : ceilDiv (ell M) r < 2
      · simp [Expr.eval, BinOp.eval, h2w, h1w, hlt]
      · simp [Expr.eval, BinOp.eval, h2w, hlt]) ?_ ?_
  · intro hcond
    have hlt : ceilDiv (ell M) r < 2 := by
      by_contra h; simp [h] at hcond
    have he_eq : e = 2 := by omega
    refine runs_seq_assign_le (v := e) (by simp [Expr.eval, he_eq, h2w]) ?_
    refine runs_seq_assign_le (v := 1) (by simp [Expr.eval, h1w]) ?_
    refine runs_seq_triple_le (pow2_loop_bridge (M := M) (r := r) (n := n) (e := e) p mem
        h2w (by omega) (by rw [hN_eq]; exact hN_w))
      ⟨by simp [h1_0], by simp [h1_1], by simp [h1_2], by simp, by simp, h1_m⟩ ?_
    intro st2 ⟨h2_2, h2_7, h2_m⟩
    refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := 1) (by simp [Expr.eval, h1w]) ?_
    refine runs_seq_triple_le (clog_loop_bridge (N := NOf M r) (n := n) p mem (by omega) hwNn)
      ⟨by simp [h2_2], by simp [h2_7, hN_eq], by simp, by simp, h2_m⟩ ?_
    intro st3 ⟨h3_9, h3_m⟩
    refine runs_ret_le (Expr.eval_reg_of_eq h3_9) ?_ ?_
    · simp [coreBridgeLevelContract, coreLevel, Outcome.value, h3_m]
    · simp only [coreBridgeLevelContract, coreBridgeLevelCost, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size]
      omega
  · intro hcond
    have hge : 2 ≤ ceilDiv (ell M) r := by
      by_contra h; have : ceilDiv (ell M) r < 2 := by omega
      simp [this] at hcond
    have he_eq : e = ceilDiv (ell M) r := by omega
    refine runs_seq_nop_le ?_
    refine runs_seq_assign_le (v := 1) (by simp [Expr.eval, h1w]) ?_
    refine runs_seq_triple_le (pow2_loop_bridge (M := M) (r := r) (n := n) (e := e) p mem
        h2w (by omega) (by rw [hN_eq]; exact hN_w))
      ⟨by simp [h1_0], by simp [h1_1], by simp [h1_2], by simp [he_eq], by simp, h1_m⟩ ?_
    intro st2 ⟨h2_2, h2_7, h2_m⟩
    refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
    refine runs_seq_assign_le (v := 1) (by simp [Expr.eval, h1w]) ?_
    refine runs_seq_triple_le (clog_loop_bridge (N := NOf M r) (n := n) p mem (by omega) hwNn)
      ⟨by simp [h2_2], by simp [h2_7, hN_eq], by simp, by simp, h2_m⟩ ?_
    intro st3 ⟨h3_9, h3_m⟩
    refine runs_ret_le (Expr.eval_reg_of_eq h3_9) ?_ ?_
    · simp [coreBridgeLevelContract, coreLevel, Outcome.value, h3_m]
    · simp only [coreBridgeLevelContract, coreBridgeLevelCost, List.getD_cons_zero,
        List.getD_cons_succ, Expr.size]
      omega

/-! ## 4. Helper Procedure 2: Sorting & Packing `CoreOutAt` (`coreBridgePackProc`) -/

/-- Deterministic Word-RAM procedure taking `[n, h, outAddr]` (with `outAddr = h + 4 + 2 * n`,
zeroed `[h, outAddr)`, and `CoreOutAt mem outAddr res` for a subset of `Finset.range n`).
Writes `ListAt mem' h (coreResultWords res)` via `O(n)` bitmap counting sort, never modifies
memory outside `[h, outAddr)`, and returns `h + (coreResultWords res).length`. -/
def coreBridgePackProc : Stmt :=
  .assign 3 (.load (.reg 2)) ;;
  .assign 4 (.load (.bin .add (.reg 2) (.const 1))) ;;
  .store (.reg 1) (.const 0) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.const 1) ;;
  .store (.bin .add (.reg 1) (.const 2)) (.bin .add (.const 1) (.reg 4)) ;;
  .store (.bin .add (.reg 1) (.const 3)) (.reg 3) ;;
  .assign 5 (.bin .add (.bin .add (.reg 1) (.const 4)) (.reg 0)) ;;
  .assign 6 (.bin .add (.reg 1) (.const 4)) ;;
  forRange 7 (.const 0) (.reg 4)
    (.assign 8 (.load (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 7))) ;;
     .store (.bin .add (.reg 5) (.reg 8)) (.const 1)) ;;
  forRange 7 (.const 0) (.reg 0)
    (.assign 8 (.load (.bin .add (.reg 5) (.reg 7))) ;;
     .cond (.reg 8)
       (.store (.reg 6) (.reg 7) ;;
        .assign 6 (.bin .add (.reg 6) (.const 1)))
       .nop) ;;
  .ret (.reg 6)

theorem coreBridgePackProc_noRand : coreBridgePackProc.NoRand := by
  simp [coreBridgePackProc, forRange, forUp, Stmt.NoRand]

/-- Contract for `coreBridgePackProc`: converts `CoreOutAt mem outAddr res` into sorted
`ListAt mem' h (coreResultWords res)` in `O(n)` steps without touching memory outside
`[h, outAddr)`. -/
def coreBridgePackContract (w : ℕ) (res : CoreResult) : Contract where
  pre args mem :=
    ∃ n h outAddr : ℕ,
      args = [n, h, outAddr] ∧
      1 ≤ n ∧
      outAddr = h + 4 + 2 * n ∧
      h + 6 + 3 * n < 2 ^ w ∧
      CoreOutAt mem outAddr res ∧
      coreResultSet res ⊆ Finset.range n ∧
      (∀ a, h ≤ a → a < outAddr → mem a = 0)
  post args mem v mem' :=
    ∃ n h outAddr : ℕ,
      args = [n, h, outAddr] ∧
      ListAt mem' h (coreResultWords res) ∧
      v = h + (coreResultWords res).length ∧
      (∀ a, a < h ∨ outAddr ≤ a → mem' a = mem a)
  cost args _ :=
    60 * args.getD 0 0 + 90

private lemma pack_mark_loop {w n h outAddr tag : ℕ} {L : List ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hOut : outAddr = h + 4 + 2 * n)
    (hw : h + 6 + 3 * n < 2 ^ w)
    (hLmem : ∀ j (hj : j < L.length), mem₀ (outAddr + 2 + j) = L[j]'hj)
    (hLlt : ∀ x ∈ L, x < n)
    (hLen : L.length ≤ n)
    (hBm0 : ∀ v < n, mem₀ (h + 4 + n + v) = 0) :
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = h ∧ st.regs 2 = outAddr ∧
        st.regs 3 = tag ∧ st.regs 4 = L.length ∧ st.regs 5 = h + 4 + n ∧
        st.regs 6 = h + 4 ∧ st.mem = mem₀)
      (forRange 7 (.const 0) (.reg 4)
        (.assign 8 (.load (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 7))) ;;
         .store (.bin .add (.reg 5) (.reg 8)) (.const 1)))
      (normalPost fun st' =>
        st'.regs 0 = n ∧ st'.regs 1 = h ∧ st'.regs 5 = h + 4 + n ∧ st'.regs 6 = h + 4 ∧
        (∀ v < n, st'.mem (h + 4 + n + v) = if v ∈ L then 1 else 0) ∧
        (∀ a, a < h + 4 + n ∨ outAddr ≤ a → st'.mem a = mem₀ a))
      (fun _ => 25 * (L.length + 1)) := by
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 4)
    (body := .assign 8 (.load (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 7))) ;;
      .store (.bin .add (.reg 5) (.reg 8)) (.const 1))
    (P := fun st => st.regs 0 = n ∧ st.regs 1 = h ∧ st.regs 2 = outAddr ∧
      st.regs 3 = tag ∧ st.regs 4 = L.length ∧ st.regs 5 = h + 4 + n ∧
      st.regs 6 = h + 4 ∧ st.mem = mem₀)
    (Inv := fun i st =>
      st.regs 0 = n ∧ st.regs 1 = h ∧ st.regs 2 = outAddr ∧
      st.regs 4 = L.length ∧ st.regs 5 = h + 4 + n ∧ st.regs 6 = h + 4 ∧ st.regs 7 = i ∧
      (∀ v < n, st.mem (h + 4 + n + v) = if v ∈ L.take i then 1 else 0) ∧
      (∀ a, a < h + 4 + n ∨ outAddr ≤ a → st.mem a = mem₀ a))
    14 0 L.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st ⟨h0, h1, h2, _, h4, h5, h6, hm⟩ =>
      ⟨by eval_expr, by simp [h0], by simp [h1], by simp [h2], by simp [h4],
        by simp [h5], by simp [h6], by simp,
        fun v hv => by rw [hm, hBm0 v hv]; simp,
        fun a _ => by rw [hm]⟩)
    (fun _ st _ _ hi => hi.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h4 : st.regs 4 = L.length := hi.2.2.2.1; eval_expr)
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h2, h4, h5, h6, h7, hbm, hfr⟩
      set x := L[i]'hilt
      have hx_lt : x < n := hLlt x (List.getElem_mem hilt)
      have hread : st.mem (outAddr + 2 + i) = x := by
        rw [hfr (outAddr + 2 + i) (Or.inr (by omega))]
        exact hLmem i hilt
      set st1 : State := { st with regs := Function.update st.regs 8 x }
      set st2 : State := { st1 with mem := Function.update st1.mem (h + 4 + n + x) 1 }
      have hs1 : Runs w p ω (.assign 8 (.load (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 7))))
          st .normal st1 7 := by
        rw [runs_assign_iff]
        exact ⟨x, by
          simp [Expr.eval, BinOp.eval, h2, h7, h2w,
            (by omega : outAddr + 2 < 2 ^ w), (by omega : outAddr + 2 + i < 2 ^ w), hread],
          rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w p ω (.store (.bin .add (.reg 5) (.reg 8)) (.const 1)) st1 .normal st2 5 := by
        rw [runs_store_iff]
        exact ⟨h + 4 + n + x, 1,
          by simp [Expr.eval, BinOp.eval, st1, h5, (by omega : h + 4 + n + x < 2 ^ w)],
          by simp [Expr.eval, h1w], rfl, rfl, by simp [Expr.size]⟩
      refine ⟨.normal, st2, 13, runs_seq_iff.mpr (Or.inr ⟨st1, 7, 5, hs1, hs2, rfl⟩), ?_, by dsimp only; omega⟩
      refine ⟨⟨by simp [st2, st1, h0], by simp [st2, st1, h1], by simp [st2, st1, h2],
        by simp [st2, st1, h4], by simp [st2, st1, h5], by simp [st2, st1, h6],
        by simp [st2, st1], ?_, ?_⟩, by simp [st2, st1, h7]⟩
      · intro v hv
        rw [List.take_add_one, List.getElem?_eq_getElem hilt]
        simp only [Option.toList_some, List.mem_append, List.mem_singleton]
        by_cases hvx : v = x
        · subst hvx; simp [st2, x]
        · have hne : h + 4 + n + v ≠ h + 4 + n + x := by omega
          have hvx' : v ≠ L[i] := hvx
          have hupd : st2.mem (h + 4 + n + v) = st.mem (h + 4 + n + v) :=
            Function.update_of_ne hne 1 st.mem
          rw [hupd, hbm v hv]; simp [hvx']
      · intro a ha
        have hne : a ≠ h + 4 + n + x := by omega
        exact (Function.update_of_ne hne 1 st.mem).trans (hfr a ha))
  exact hloop.conseq (fun _ h => h)
    (fun o st' h => by
      cases o with
      | returned _ => exact False.elim h
      | normal =>
        refine ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_, h.2.2.2.2.2.2.2.2⟩
        intro v hv
        simpa [List.take_length] using h.2.2.2.2.2.2.2.1 v hv)
    (fun _ _ => by simp [Expr.size]; omega)

private lemma pack_scan_loop {w n h outAddr : ℕ} {U : Finset ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hOut : outAddr = h + 4 + 2 * n)
    (hw : h + 6 + 3 * n < 2 ^ w)
    (hBm : ∀ v < n, mem₀ (h + 4 + n + v) = if v ∈ U then 1 else 0) :
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = h ∧ st.regs 5 = h + 4 + n ∧
        st.regs 6 = h + 4 ∧ st.mem = mem₀)
      (forRange 7 (.const 0) (.reg 0)
        (.assign 8 (.load (.bin .add (.reg 5) (.reg 7))) ;;
         .cond (.reg 8)
           (.store (.reg 6) (.reg 7) ;;
            .assign 6 (.bin .add (.reg 6) (.const 1)))
           .nop))
      (normalPost fun st' =>
        let xs := (List.range n).filter (fun v => decide (v ∈ U))
        st'.regs 6 = h + 4 + xs.length ∧
        ListAt st'.mem (h + 4) xs ∧
        (∀ a, a < h + 4 ∨ h + 4 + n ≤ a → st'.mem a = mem₀ a))
      (fun _ => 25 * (n + 1)) := by
  have h1w : 1 < 2 ^ w := by omega
  let pref : ℕ → List ℕ := fun i => (List.range i).filter (fun v => decide (v ∈ U))
  have hpref_len : ∀ i, (pref i).length ≤ i := fun i =>
    le_trans (List.length_filter_le _ _) (by simp)
  have hloop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 0)
    (body := .assign 8 (.load (.bin .add (.reg 5) (.reg 7))) ;;
      .cond (.reg 8)
        (.store (.reg 6) (.reg 7) ;;
         .assign 6 (.bin .add (.reg 6) (.const 1)))
        .nop)
    (P := fun st => st.regs 0 = n ∧ st.regs 1 = h ∧ st.regs 5 = h + 4 + n ∧
      st.regs 6 = h + 4 ∧ st.mem = mem₀)
    (Inv := fun i st =>
      st.regs 0 = n ∧ st.regs 1 = h ∧ st.regs 5 = h + 4 + n ∧
      st.regs 6 = h + 4 + (pref i).length ∧ st.regs 7 = i ∧
      ListAt st.mem (h + 4) (pref i) ∧
      (∀ a, a < h + 4 ∨ h + 4 + n ≤ a → st.mem a = mem₀ a))
    16 0 n (Nat.zero_le n) h1w (fun _ => by omega)
    (fun st ⟨h0, h1, h5, h6, hm⟩ =>
      ⟨by eval_expr, by simp [h0], by simp [h1], by simp [h5], by simp [h6, pref],
        by simp, by intro j hj; simp [pref] at hj, fun a _ => by rw [hm]⟩)
    (fun _ st _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by have h0 : st.regs 0 = n := hi.1; eval_expr)
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h5, h6, h7, hlist, hfr⟩
      have hread : st.mem (h + 4 + n + i) = if i ∈ U then 1 else 0 := by
        rw [hfr (h + 4 + n + i) (Or.inr (by omega)), hBm i hilt]
      have hplen : (pref i).length ≤ i := hpref_len i
      set st1 : State := { st with regs := Function.update st.regs 8 (if i ∈ U then 1 else 0) }
      have hs1 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 5) (.reg 7)))) st .normal st1 5 := by
        rw [runs_assign_iff]
        exact ⟨if i ∈ U then 1 else 0,
          by simp [Expr.eval, BinOp.eval, h5, h7, (by omega : h + 4 + n + i < 2 ^ w), hread],
          rfl, rfl, by simp [Expr.size]⟩
      by_cases hiU : i ∈ U
      · have hpref_succ : pref (i + 1) = pref i ++ [i] := by
          simp [pref, List.range_succ, List.filter_append, hiU]
        set dst := h + 4 + (pref i).length
        set st2 : State := { st1 with mem := Function.update st1.mem dst i }
        set st3 : State := { st2 with regs := Function.update st2.regs 6 (dst + 1) }
        have hs2 : Runs w p ω (.store (.reg 6) (.reg 7)) st1 .normal st2 3 := by
          rw [runs_store_iff]
          exact ⟨dst, i, by simp [Expr.eval, st1, h6], by simp [Expr.eval, st1, h7],
            rfl, rfl, by simp [Expr.size]⟩
        have hs3 : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 1))) st2 .normal st3 4 := by
          rw [runs_assign_iff]
          exact ⟨dst + 1,
            by simp [Expr.eval, BinOp.eval, st2, st1, h6, h1w, (by omega : dst + 1 < 2 ^ w)],
            rfl, rfl, by simp [Expr.size]⟩
        have hcond : Runs w p ω
            (.cond (.reg 8) (.store (.reg 6) (.reg 7) ;; .assign 6 (.bin .add (.reg 6) (.const 1))) .nop)
            st1 .normal st3 10 := by
          rw [runs_cond_iff]
          exact ⟨1, 8, by simp [Expr.eval, st1, hiU],
            by simpa using runs_seq_iff.mpr (Or.inr ⟨st2, 3, 4, hs2, hs3, rfl⟩),
            by simp [Expr.size]⟩
        refine ⟨.normal, st3, 16, runs_seq_iff.mpr (Or.inr ⟨st1, 5, 10, hs1, hcond, rfl⟩), ?_, le_rfl⟩
        refine ⟨⟨by simp [st3, st2, st1, h0], by simp [st3, st2, st1, h1],
          by simp [st3, st2, st1, h5], by simp [st3, dst, hpref_succ]; omega,
          by simp [st3, st2, st1], ?_, ?_⟩, by simp [st3, st2, st1, h7]⟩
        · rw [hpref_succ]
          intro j hj
          rw [List.length_append, List.length_singleton] at hj
          by_cases hltj : j < (pref i).length
          · rw [List.getElem_append_left hltj]
            have hne : h + 4 + j ≠ dst := by omega
            exact (Function.update_of_ne hne i st.mem).trans (hlist j hltj)
          · have hjeq : j = (pref i).length := by omega
            subst hjeq
            rw [List.getElem_append_right le_rfl]
            simp [st3, st2, dst]
        · intro a ha
          have hne : a ≠ dst := by omega
          exact (Function.update_of_ne hne i st.mem).trans (hfr a ha)
      · have hpref_succ : pref (i + 1) = pref i := by
          simp [pref, List.range_succ, List.filter_append, hiU]
        have hcond : Runs w p ω
            (.cond (.reg 8) (.store (.reg 6) (.reg 7) ;; .assign 6 (.bin .add (.reg 6) (.const 1))) .nop)
            st1 .normal st1 3 := by
          rw [runs_cond_iff]
          exact ⟨0, 1, by simp [Expr.eval, st1, hiU],
            by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
            by simp [Expr.size]⟩
        refine ⟨.normal, st1, 9, runs_seq_iff.mpr (Or.inr ⟨st1, 5, 3, hs1, hcond, rfl⟩), ?_, by dsimp only; omega⟩
        exact ⟨⟨by simp [st1, h0], by simp [st1, h1], by simp [st1, h5],
          by simp [st1, h6, hpref_succ], by simp [st1],
          by rw [hpref_succ]; exact hlist, hfr⟩, by simp [st1, h7]⟩)
  exact hloop.conseq (fun _ h => h)
    (fun o st' h => by
      cases o with
      | returned _ => exact False.elim h
      | normal => exact ⟨h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩)
    (fun _ _ => by simp [Expr.size]; omega)

theorem coreBridgePackProc_meetsContract {w f : ℕ} {res : CoreResult} {p : Program}
    (hf : p.procs[f]? = some coreBridgePackProc) :
    MeetsContract w p f (coreBridgePackContract w res) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨n, h, outAddr, rfl, hn1, hOut, hw, hCoreOut, hSub, hZero⟩
  set U := coreResultSet res
  have hExtract : mem outAddr = coreTag res ∧
      ∃ L : List ℕ, L.Nodup ∧ L.toFinset = U ∧ mem (outAddr + 1) = L.length ∧
        ListAt mem (outAddr + 2) L := by
    cases res with
    | cut S => exact hCoreOut
    | expander S => exact hCoreOut
  rcases hExtract with ⟨hTagMem, L, hLnd, hLfin, hLenMem, hLlist⟩
  have hLenCard : L.length = U.card := by
    rw [← hLfin, List.toFinset_card_of_nodup hLnd]
  have hLenLe : L.length ≤ n := by
    rw [hLenCard]
    have := Finset.card_le_card hSub
    simpa using this
  have hLlt : ∀ x ∈ L, x < n := fun x hx =>
    Finset.mem_range.mp (hSub (hLfin ▸ List.mem_toFinset.mpr hx))
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold coreBridgePackProc
  -- Load tag and len
  refine runs_seq_assign_le (v := coreTag res)
    (by simp [Expr.eval, startState, hTagMem]) ?_
  refine runs_seq_assign_le (v := L.length)
    (by simp [Expr.eval, BinOp.eval, startState, h1w, (by omega : outAddr + 1 < 2 ^ w), hLenMem]) ?_
  -- Store 4-word header at h .. h + 3
  refine runs_seq_store_le (x := h) (v := 0)
    (by simp [Expr.eval, startState]) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  refine runs_seq_store_le (x := h + 1) (v := 1)
    (by simp [Expr.eval, BinOp.eval, startState, h1w, (by omega : h + 1 < 2 ^ w)])
    (by simp [Expr.eval, h1w]) ?_
  refine runs_seq_store_le (x := h + 2) (v := 1 + L.length)
    (by simp [Expr.eval, BinOp.eval, startState, h2w, (by omega : h + 2 < 2 ^ w)])
    (by simp [Expr.eval, BinOp.eval, h1w, (by omega : 1 + L.length < 2 ^ w)]) ?_
  refine runs_seq_store_le (x := h + 3) (v := coreTag res)
    (by simp [Expr.eval, BinOp.eval, startState, h3w, (by omega : h + 3 < 2 ^ w)])
    (by simp [Expr.eval]) ?_
  -- Set bm = h + 4 + n, dst = h + 4
  refine runs_seq_assign_le (v := h + 4 + n)
    (by simp [Expr.eval, BinOp.eval, startState, h4w, (by omega : h + 4 < 2 ^ w),
          (by omega : h + 4 + n < 2 ^ w)]) ?_
  refine runs_seq_assign_le (v := h + 4)
    (by simp [Expr.eval, BinOp.eval, startState, h4w, (by omega : h + 4 < 2 ^ w)]) ?_
  set mem1 : ℕ → ℕ :=
    Function.update (Function.update (Function.update (Function.update mem h 0) (h + 1) 1)
      (h + 2) (1 + L.length)) (h + 3) (coreTag res)
  have hmem1_eq : ∀ a, a < h ∨ h + 4 ≤ a → mem1 a = mem a := fun a ha => by
    simp [mem1, Function.update_of_ne (by omega : a ≠ h + 3),
      Function.update_of_ne (by omega : a ≠ h + 2),
      Function.update_of_ne (by omega : a ≠ h + 1),
      Function.update_of_ne (by omega : a ≠ h)]
  have hmem1_hdr : mem1 h = 0 ∧ mem1 (h + 1) = 1 ∧ mem1 (h + 2) = 1 + U.card ∧
      mem1 (h + 3) = coreTag res := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [mem1, hLenCard]
  -- Loop 1: mark bitmap
  refine runs_seq_triple_le
    (pack_mark_loop (w := w) (n := n) (h := h) (outAddr := outAddr) (tag := coreTag res) (L := L)
      p mem1 hOut hw
      (fun j hj => by rw [hmem1_eq _ (Or.inr (by omega))]; exact hLlist j hj)
      hLlt hLenLe
      (fun v hv => by rw [hmem1_eq _ (Or.inr (by omega))]; exact hZero _ (by omega) (by omega)))
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp, by simp, by simp,
      by simp, rfl⟩ ?_
  intro st2 ⟨h2_0, h2_1, h2_5, h2_6, h2_bm, h2_fr⟩
  have h2_bmU : ∀ v < n, st2.mem (h + 4 + n + v) = if v ∈ U then 1 else 0 := fun v hv => by
    rw [h2_bm v hv]
    by_cases hvL : v ∈ L
    · have hvU : v ∈ U := hLfin ▸ List.mem_toFinset.mpr hvL
      simp [hvL, hvU]
    · have hvU : v ∉ U := fun hU => hvL (List.mem_toFinset.mp (hLfin.symm ▸ hU))
      simp [hvL, hvU]
  -- Loop 2: scan bitmap into sorted list at h + 4
  refine runs_seq_triple_le
    (pack_scan_loop (w := w) (n := n) (h := h) (outAddr := outAddr) (U := U) p st2.mem hOut hw h2_bmU)
    ⟨h2_0, h2_1, h2_5, h2_6, rfl⟩ ?_
  intro st3 ⟨h3_6, h3_list, h3_fr⟩
  have hxs_eq : (List.range n).filter (fun v => decide (v ∈ U)) = finsetWords U :=
    range_filter_eq_finsetWords hSub
  have h3_list' : ListAt st3.mem (h + 4) (finsetWords U) := by
    rwa [hxs_eq] at h3_list
  have hxs_len : ((List.range n).filter (fun v => decide (v ∈ U))).length = U.card := by
    rw [hxs_eq, finsetWords, Finset.length_sort]
  have hResLen : (coreResultWords res).length = 4 + U.card := by
    rw [coreResultWords_eq_header_append, List.length_append]
    simp [finsetWords, U]
  refine runs_ret_le (Expr.eval_reg_of_eq h3_6) ?_ ?_
  · refine ⟨n, h, outAddr, rfl, ?_, ?_, ?_⟩
    · rw [coreResultWords_eq_header_append]
      intro j hj
      have hj' : j < 4 + U.card := by
        simp only [List.length_append, List.length_cons, List.length_nil, finsetWords,
          Finset.length_sort] at hj
        change j < 4 + (coreResultSet res).card
        omega
      by_cases hj4 : j < 4
      · rw [List.getElem_append_left (by simpa using hj4)]
        have hmem_j : st3.mem (h + j) = mem1 (h + j) := by
          rw [h3_fr _ (Or.inl (by omega)), h2_fr _ (Or.inl (by omega))]
        rw [hmem_j]
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
        · simpa using hmem1_hdr.1
        · simpa using hmem1_hdr.2.1
        · simpa using hmem1_hdr.2.2.1
        · simpa using hmem1_hdr.2.2.2
      · rw [List.getElem_append_right (by simpa using (show 4 ≤ j by omega))]
        have hidx : j - 4 < (finsetWords U).length := by
          rw [finsetWords, Finset.length_sort]; omega
        have hget := h3_list' (j - 4) hidx
        have haddr : h + 4 + (j - 4) = h + j := by omega
        rw [haddr] at hget
        simpa using hget
    · simp only [Outcome.value, hResLen, hxs_len]; omega
    · intro a ha
      rcases ha with ha | ha
      · rw [h3_fr a (Or.inl (by omega)), h2_fr a (Or.inl (by omega)), hmem1_eq a (Or.inl ha)]
      · rw [h3_fr a (Or.inr (by omega)), h2_fr a (Or.inr ha), hmem1_eq a (Or.inr (by omega))]
  · simp only [coreBridgePackContract, List.getD_cons_zero, Expr.size]
    omega

end MinCostFlow.HierPaths
