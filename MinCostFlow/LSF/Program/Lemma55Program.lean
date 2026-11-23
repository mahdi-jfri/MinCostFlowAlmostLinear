module

public import MinCostFlow.LSF.Program.Lemma55Outer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Deterministic Word-RAM Program for Lemma 5.5 (`Lemma55Program`)

Completes the relocatable execution theorem `lemma55Program_runs` and the unconditional end-to-end
realization `lemma55Program_from_cited` of **Lemma 5.5** (`arXiv:2309.16629v1`, page 17 and
Appendix A.2, pages 48–49) for every limb width `h ≥ 1`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  MinCostFlow.Num

@[expose] public section

/-! ## Main Theorem: `lemma55Program_runs` and `lemma55Program_from_cited` -/

private lemma runs_seq_assign_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr} {s₂ : Stmt}
    {m : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ} {Q : Outcome → State → Prop} {acc B v : ℕ}
    (he : e.eval w ⟨m, regs, pos⟩ = some v)
    (h₂ : ∃ o st' c, Runs w p ω s₂ ⟨m, Function.update regs r v, pos⟩ o st' c ∧
      Q o st' ∧ acc + e.size + 2 + c ≤ B) :
    ∃ o st' c, Runs w p ω (.assign r e ;; s₂) ⟨m, regs, pos⟩ o st' c ∧ Q o st' ∧ acc + c ≤ B :=
  runs_seq_assign_le he h₂

private lemma runs_seq_store_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr} {s₂ : Stmt}
    {m : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ} {Q : Outcome → State → Prop} {acc B x v : ℕ}
    (ha : a.eval w ⟨m, regs, pos⟩ = some x) (he : e.eval w ⟨m, regs, pos⟩ = some v)
    (h₂ : ∃ o st' c, Runs w p ω s₂ ⟨Function.update m x v, regs, pos⟩ o st' c ∧
      Q o st' ∧ acc + a.size + e.size + 2 + c ≤ B) :
    ∃ o st' c, Runs w p ω (.store a e ;; s₂) ⟨m, regs, pos⟩ o st' c ∧ Q o st' ∧ acc + c ≤ B :=
  runs_seq_store_le ha he h₂

set_option maxHeartbeats 800000 in
open Classical in
/-- Relocatable execution theorem for **Lemma 5.5** (`arXiv:2309.16629v1`, page 17 and Appendix A.2,
pages 48–49): for any host program containing `lemma55ModuleProcs` at index `b`, entry `b + 0`
initializes `k_nat` dynamic LSF copies via approximate multiplicative weights, writes their
pairwise-disjoint handles into `handlesOut[0 .. k_nat - 1]`, and guarantees the full Lemma 5.5
dynamic invariants and `O(log⁶(n₀ + 2) log(m₀ + 2))` average stretch for every valid batch
sequence `Us`. -/
theorem lemma55Program_runs {w h q c_AN b g0Ptr lenArr L_in P_fp k_nat L_w vCap eCap
    handlesOut heap vCap0 eCap0 : ℕ}
    {p Q_AN : Program} {K_AN : ℝ} {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hp : p.HasAt b (lemma55ModuleProcs Q_AN c_AN K_AN b h))
    (hQ : ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
      (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
      ∃ out cost,
        RunsTo (wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
          G_a.IsSpanningTree out ∧
          G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
          (cost : ℝ) ≤ K_AN * (G_a.m + 1) *
            (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight))
    (hc : 1 ≤ c_AN) (hh : 1 ≤ h) (hw : 3 * h + 2 ≤ w)
    (hLin1 : 1 ≤ L_in) (hLin_le : L_in ≤ L_w) (hk : 1 ≤ k_nat)
    (hdiv : h ∣ P_fp) (hq_P : q + 11 ≤ P_fp) (hk_q : 8 * k_nat ≤ 2 ^ q)
    (hP_Lin : P_fp + 6 ≤ h * L_in)
    (hm_Lin : 32 * (G₀.E.card + 1) * 2 ^ P_fp < 2 ^ (h * L_in - 1))
    (h2P_ltw : 2 * P_fp + 9 < 2 ^ w)
    (hHld_ltw : 3 * (4 * k_nat * (hldDepthBound G₀.n + 1)) < 2 ^ w)
    (hrho_cap : lemma55RhoNat K_AN G₀.n k_nat < 2 ^ (h * (L_w - L_in)))
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hvCap_le : vCap0 ≤ vCap) (heCap_le : eCap0 ≤ eCap) (heCap1 : 1 ≤ eCap)
    (hℓ₀_mem : ∀ e ∈ G₀.E, Valid mem (lenArr + e * L_in) h L_in ∧
      fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e)
    (hg0_le : g0Ptr + dynGraphSize vCap0 eCap0 ≤ heap)
    (hlen_le : lenArr + eCap0 * L_in ≤ heap)
    (hhnd_le : handlesOut + k_nat ≤ heap)
    (hhnd_g0 : handlesOut + k_nat ≤ g0Ptr ∨ g0Ptr + dynGraphSize vCap0 eCap0 ≤ handlesOut)
    (hhnd_len : handlesOut + k_nat ≤ lenArr ∨ lenArr + eCap0 * L_in ≤ handlesOut)
    (hz : ZeroFrom mem heap)
    (hsp : heap + lemma55Space Q_AN K_AN c_AN h L_in L_w P_fp k_nat vCap eCap G₀.n G₀.m < 2 ^ w) :
    let K₀ := lemma54K0 (4 * max K_AN 1 + 5) (5 / 4) (defaultK_sigma K_AN : ℝ)
    let K := (16 + 4 * (40960 : ℝ)) * K₀ + 128
    ∃ body, p.procs[b + lemma55IdxInit]? = some body ∧
      ∃ (endHeap : ℕ) (st' : State) (c : ℕ) (S₀ : ℕ → LSFState) (x₀ : ℕ → LSFConcrete) (hs : ℕ → ℕ),
        Runs w p ω body
          (startState [g0Ptr, lenArr, L_in, P_fp, k_nat, L_w, vCap, eCap, handlesOut, heap] mem pos)
          (.returned endHeap) st' c ∧
        heap ≤ endHeap ∧
        endHeap ≤ heap + lemma55Space Q_AN K_AN c_AN h L_in L_w P_fp k_nat vCap eCap G₀.n G₀.m ∧
        ZeroFrom st'.mem endHeap ∧
        (∀ z < heap, (z < handlesOut ∨ handlesOut + k_nat ≤ z) → st'.mem z = mem z) ∧
        (∀ j < k_nat, st'.mem (handlesOut + j) = hs j ∧
          (LSFRep h).rep (hs j) (S₀ j) (x₀ j) st'.mem ∧
          ∀ a, (LSFRep h).foot (hs j) (x₀ j) a → heap ≤ a ∧ a < endHeap) ∧
        c ≤ lemma55Cost Q_AN c_AN K_AN h L_in L_w P_fp k_nat G₀.n G₀.m ∧
        (∀ (Us : List (List Update)), BatchesIsValid G₀ Us →
          ∀ (ℓ : ℕ → ℝ),
            (∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e) →
            (∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
              e ∉ batchesInserted Us → ℓ e = ℓ₀ e) →
            let G := Us.foldl MGraph.applyBatch G₀
            let qUpd := totalUpdates Us
            let S : ℕ → LSFState := fun j => applyLSFBatches (S₀ j) Us
            (∀ j < k_nat,
              (S j).G = G ∧
              (S j).insertedEdges = batchesInserted Us ∧
              (S j).RF.F.E ⊆ (S₀ j).RF.F.E ∧
              G.IsSubgraph (S j).RF.F ∧
              (S j).T.IsSubgraph (S j).RF.F ∧
              (∀ e ∈ (S j).insertedEdges, (S j).wstr e = 1) ∧
              (∀ e ∈ G.E, e ∉ (S j).insertedEdges → (S j).wstr e = (S₀ j).wstr e) ∧
              ((components (S₀ j).RF.F).card : ℝ) ≤
                (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
                  else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
                  K * ((G₀.E.card : ℝ) / (k_nat : ℝ)) ∧
              ((components (S j).RF.F).card : ℝ) ≤ ((components (S₀ j).RF.F).card : ℝ) +
                K * (qUpd : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
              (S j).lsf.Holds G ℓ (K * (k_nat : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6) ∧
              ((S j).W_init.card : ℝ) ≤
                6 + (if ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v then 1
                  else ((components G₀).card : ℝ) * K * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) +
                  K * ((G₀.E.card : ℝ) / (k_nat : ℝ)) ∧
              (S j).W_init.biUnion (inducedEdges (S₀ j).RF.F) = (S₀ j).RF.F.E ∧
              (∀ W₁ ∈ (S j).W_init, ∀ W₂ ∈ (S j).W_init, W₁ ≠ W₂ →
                Disjoint (inducedEdges (S₀ j).RF.F W₁) (inducedEdges (S₀ j).RF.F W₂)) ∧
              boundary (S j).W_init ⊆ (S j).R ∧
              ∀ W ∈ (S j).W_init, PathConvex (S j).T₀ W ∧ W ⊆ G.V ∧
                (pieceBoundary (S j).W_init W).card ≤ 1 ∧
                (G.vol (W \ (S j).R) : ℝ) ≤ K * (k_nat : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) ∧
            ∀ e ∈ G.E,
              ∑ j ∈ Finset.range k_nat, ((1 : ℝ) / (k_nat : ℝ)) * (S j).wstr e ≤
                K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.E.card : ℝ) + 2)) := by
  intro K₀ K
  obtain ⟨hpInit, hpWLoop, hpStep, hpBuildRho, hpEmit, hpLsf, hpDiv, hpExp, hpMul⟩ :=
    lemma55HasAt_split hp
  obtain ⟨hpShared, hpC1⟩ := hasAt_lsf_utils_and_c1 hpLsf
  have h2w_16 : 16 ≤ 2 ^ w := by
    have : 2 ^ 5 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hUtils := lsfHasAt_utils hpShared
  have hCopy : MeetsContract w p (lsfBaseUtils (lemma55BaseLsf b) + idxUtilMemCopy) (memCopyContract w) :=
    memCopy_meetsContract hw1 (hUtils.get (i := idxUtilMemCopy) (by rw [utilsProcs_length]; decide))
  have hFill : MeetsContract w p (lsfBaseUtils (lemma55BaseLsf b) + idxUtilMemFill) (memFillContract w) :=
    memFill_meetsContract hw1 (hUtils.get (i := idxUtilMemFill) (by rw [utilsProcs_length]; decide))
  have hLog : MeetsContract w p (lsfBaseUtils (lemma55BaseLsf b) + idxUtilLog2) log2Contract :=
    log2_meetsContract hw2 (hUtils.get (i := idxUtilLog2) (by rw [utilsProcs_length]; decide))
  have hEmit : MeetsContract w p (b + 4) (emitNatContract w (lemma55RhoConst K_AN) h) :=
    emitNat_meetsContract hpEmit
  have hAcc : MeetsContract w p (lsfBaseC1 Q_AN (lemma55BaseLsf b) + 0) (uAccContract w h) :=
    uAcc_meetsContract hh (by omega) (hpC1.get (i := 0) (by rw [lsfProcsC1_length]; decide))
  have hLoad : MeetsContract w p (lsfBaseC1 Q_AN (lemma55BaseLsf b) + 1) (uLoadWordContract w h) :=
    uLoadWord_meetsContract (by omega) (hpC1.get (i := 1) (by rw [lsfProcsC1_length]; decide))
  have hMulU : MeetsContract w p (lsfBaseC1 Q_AN (lemma55BaseLsf b) + 2) (uMulContract w h) :=
    uMul_meetsContract hAcc (by omega) (hpC1.get (i := 2) (by rw [lsfProcsC1_length]; decide))
  have hDiv : MeetsContract w p (lemma55BaseDiv Q_AN b) (fixedDivideContract w h) :=
    fixedDivide_meetsContract hh hw hpDiv
  have hExp : MeetsContract w p (lemma55BaseExp Q_AN b) (positiveExponentialContract w h q) :=
    positiveExponential_meetsContract hh hw hpExp
  have hMul : MeetsContract w p (lemma55BaseMul Q_AN b) (fixedMultiplyContract w h) :=
    fixedMultiply_meetsContract hh (by omega) hpMul
  refine ⟨_, hpInit, ?_⟩
  set wtArr := heap
  set onePtr := wtArr + eCap * L_in
  set rhoPtr := onePtr + L_w
  set wtEnd := rhoPtr + L_w
  set pL := P_fp / h
  have hpL_mul : h * pL = P_fp := Nat.mul_div_cancel' hdiv
  have hpL_lt_Lin : pL < L_in := by
    by_contra hge
    have : h * L_in ≤ h * pL := Nat.mul_le_mul_left h (by omega)
    omega
  have hpL_le_Lw : pL ≤ L_w := by omega
  have hrho_fit : 2 * (lemma55RhoNat K_AN G₀.n k_nat * 2 ^ P_fp) < capacity h L_w := by
    rw [capacity_eq_two_pow]
    have h1 : lemma55RhoNat K_AN G₀.n k_nat * 2 ^ P_fp < 2 ^ (h * (L_w - L_in)) * 2 ^ P_fp :=
      Nat.mul_lt_mul_of_pos_right hrho_cap (by positivity)
    have h2 : 2 * (2 ^ (h * (L_w - L_in)) * 2 ^ P_fp) = 2 ^ (h * (L_w - L_in) + P_fp + 1) := by
      rw [← pow_add, pow_succ]; ring
    have hexp : h * (L_w - L_in) + P_fp + 1 ≤ h * L_w := by
      have : h * (L_w - L_in) + h * L_in = h * L_w := by rw [← Nat.mul_add, Nat.sub_add_cancel hLin_le]
      omega
    have h3 : 2 ^ (h * (L_w - L_in) + P_fp + 1) ≤ 2 ^ (h * L_w) := Nat.pow_le_pow_right (by decide) hexp
    omega
  have hsp_exp : wtEnd + k_nat * (lsfStaticSize vCap eCap G₀.n G₀.n L_w + 2 * (eCap * L_w) +
      lsstSpace Q_AN K_AN G₀.n (2 * G₀.m) (lsstLSimMin c_AN G₀.n (2 * G₀.m) L_in h) h +
      200 * (G₀.n + G₀.m + 1) * (L_w + lsstLSimMin c_AN G₀.n (2 * G₀.m) L_in h + auxLogCap G₀.n + 20) + 1000) +
      max (4 * L_w) (mwuEdgeStepSpace L_in L_w P_fp) + 1 < 2 ^ w := by
    dsimp only [lemma55Space] at hsp
    have : wtEnd = heap + eCap * L_in + 2 * L_w := by omega
    omega
  have hn0_ltw : G₀.n + 2 < 2 ^ w := by
    have := (dynGraph_card_le hdg0).1
    have : G₀.n ≤ vCap0 := this
    dsimp [dynGraphSize] at hg0_le; omega
  have hh_ltw : h < 2 ^ w := by
    have : 2 ^ (3 * h + 2) ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    have : h < 2 ^ h := Nat.lt_two_pow_self
    have : 2 ^ h ≤ 2 ^ (3 * h + 2) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hgn_m : mem (g0Ptr + dgNOff) = G₀.n := hdg0.2.2.2.2.2.1
  -- Build the main execution (using `ℓ₀_mem := memArrayReal mem lenArr G₀ h L_in P_fp`)
  let ℓ₀_mem := memArrayReal mem lenArr G₀ h L_in P_fp
  suffices hrun_all : ∃ (endHeap : ℕ) (st' : State) (c : ℕ) (v' : ℕ → ℕ → ℝ) (S₀ : ℕ → LSFState) (x₀ : ℕ → LSFConcrete) (hs : ℕ → ℕ),
      Runs w p ω (lemma55InitProc (b + 3) (lemma55BaseLsf b + lsfIdxInit) (b + 1) h)
        (startState [g0Ptr, lenArr, L_in, P_fp, k_nat, L_w, vCap, eCap, handlesOut, heap] mem pos)
        (.returned endHeap) st' c ∧
      heap ≤ endHeap ∧
      endHeap ≤ heap + lemma55Space Q_AN K_AN c_AN h L_in L_w P_fp k_nat vCap eCap G₀.n G₀.m ∧
      ZeroFrom st'.mem endHeap ∧
      (∀ z < heap, (z < handlesOut ∨ handlesOut + k_nat ≤ z) → st'.mem z = mem z) ∧
      (∀ e ∈ G₀.E, v' 0 e = 1) ∧
      (∀ i ≤ k_nat, ∀ e ∈ G₀.E, 0 < v' i e) ∧
      (∀ i < k_nat, ∃ T_raw C_reps W_T,
        ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4)
          (defaultThreshNat K_AN G₀.n k_nat : ℝ) (defaultK_sigma K_AN : ℝ)
          G₀ ℓ₀_mem (v' i) (k_nat : ℝ) T_raw (S₀ i).r₀ C_reps (S₀ i).π W_T ∧
        S₀ i = initLSFWith G₀ ℓ₀_mem (v' i) (k_nat : ℝ) T_raw (S₀ i).r₀ C_reps (S₀ i).π W_T
          (defaultThreshNat K_AN G₀.n k_nat : ℝ)) ∧
      (∀ i < k_nat, ∀ e ∈ G₀.E,
        (1 - 1 / (4 * (k_nat : ℝ))) * v' i e * Real.exp ((S₀ i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ)) ≤
          v' (i + 1) e ∧
        v' (i + 1) e ≤
          (1 + 1 / (4 * (k_nat : ℝ))) * v' i e * Real.exp ((S₀ i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ))) ∧
      (∀ j < k_nat, st'.mem (handlesOut + j) = hs j ∧
        (LSFRep h).rep (hs j) (S₀ j) (x₀ j) st'.mem ∧
        ∀ a, (LSFRep h).foot (hs j) (x₀ j) a → heap ≤ a ∧ a < endHeap) ∧
      c ≤ lemma55Cost Q_AN c_AN K_AN h L_in L_w P_fp k_nat G₀.n G₀.m by
    rcases hrun_all with ⟨endHeap, st', c, v', S₀, x₀, hs, hrun, hhe1, hhe2, hz', hfr',
      hv0', hv_pos', hinit', hv_step', hhnd', hc'⟩
    refine ⟨endHeap, st', c, S₀, x₀, hs, hrun, hhe1, hhe2, hz', hfr', hhnd', hc', ?_⟩
    intro Us hUs ℓ hℓ hℓ_orig
    obtain ⟨_, hρ_ge, hρ_le⟩ := lemma55Rho_bounds K_AN G₀.n hk
    have hℓ_mem_pos : ∀ e ∈ G₀.E, 0 < ℓ₀_mem e := fun e he => by
      dsimp only [ℓ₀_mem]; rw [memArrayReal_eq he, (hℓ₀_mem e he).2.1]; exact (hℓ₀_mem e he).2.2
    have hℓ_orig_mem : ∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
        e ∉ batchesInserted Us → ℓ e = ℓ₀_mem e := fun e he heG hni => by
      dsimp only [ℓ₀_mem]; rw [memArrayReal_eq he, (hℓ₀_mem e he).2.1]
      exact hℓ_orig e he heG hni
    have h55 := (lemma_5_5_approx (4 * max K_AN 1 + 5) (5 / 4) (defaultK_sigma K_AN : ℝ) 40960
      (by norm_num)).2 G₀ hG₀ hV₀ ℓ₀_mem hℓ_mem_pos k_nat hk
      (lemma55RhoNat K_AN G₀.n k_nat : ℝ) (1 / (4 * (k_nat : ℝ)))
      hρ_ge hρ_le (by positivity) le_rfl v' S₀ hv0' hv_pos'
      (fun j hj => by
        obtain ⟨T_raw, C_reps, W_T, hpv, hSe⟩ := hinit' j hj
        exact ⟨T_raw, (S₀ j).r₀, C_reps, (S₀ j).π, W_T, (defaultThreshNat K_AN G₀.n k_nat : ℝ), hpv, hSe⟩)
      hv_step' Us hUs ℓ hℓ hℓ_orig_mem
    exact h55
  -- Run `lemma55InitProc` step by step
  suffices hmain : ∃ o st' c,
      Runs w p ω (lemma55InitProc (b + 3) (lemma55BaseLsf b + lsfIdxInit) (b + 1) h)
        (startState [g0Ptr, lenArr, L_in, P_fp, k_nat, L_w, vCap, eCap, handlesOut, heap] mem pos)
        o st' c ∧
      (∃ (endHeap : ℕ) (v' : ℕ → ℕ → ℝ) (S₀ : ℕ → LSFState) (x₀ : ℕ → LSFConcrete) (hs : ℕ → ℕ),
        o = .returned endHeap ∧
        heap ≤ endHeap ∧
        endHeap ≤ heap + lemma55Space Q_AN K_AN c_AN h L_in L_w P_fp k_nat vCap eCap G₀.n G₀.m ∧
        ZeroFrom st'.mem endHeap ∧
        (∀ z < heap, (z < handlesOut ∨ handlesOut + k_nat ≤ z) → st'.mem z = mem z) ∧
        (∀ e ∈ G₀.E, v' 0 e = 1) ∧
        (∀ i ≤ k_nat, ∀ e ∈ G₀.E, 0 < v' i e) ∧
        (∀ i < k_nat, ∃ T_raw C_reps W_T,
          ValidLSFParams (4 * max K_AN 1 + 5) (5 / 4)
            (defaultThreshNat K_AN G₀.n k_nat : ℝ) (defaultK_sigma K_AN : ℝ)
            G₀ ℓ₀_mem (v' i) (k_nat : ℝ) T_raw (S₀ i).r₀ C_reps (S₀ i).π W_T ∧
          S₀ i = initLSFWith G₀ ℓ₀_mem (v' i) (k_nat : ℝ) T_raw (S₀ i).r₀ C_reps (S₀ i).π W_T
            (defaultThreshNat K_AN G₀.n k_nat : ℝ)) ∧
        (∀ i < k_nat, ∀ e ∈ G₀.E,
          (1 - 1 / (4 * (k_nat : ℝ))) * v' i e * Real.exp ((S₀ i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ)) ≤
            v' (i + 1) e ∧
          v' (i + 1) e ≤
            (1 + 1 / (4 * (k_nat : ℝ))) * v' i e * Real.exp ((S₀ i).wstr e / (lemma55RhoNat K_AN G₀.n k_nat : ℝ))) ∧
        (∀ j < k_nat, st'.mem (handlesOut + j) = hs j ∧
          (LSFRep h).rep (hs j) (S₀ j) (x₀ j) st'.mem ∧
          ∀ a, (LSFRep h).foot (hs j) (x₀ j) a → heap ≤ a ∧ a < endHeap)) ∧
      0 + c ≤ lemma55Cost Q_AN c_AN K_AN h L_in L_w P_fp k_nat G₀.n G₀.m by
    rcases hmain with ⟨_, st', c, hrun, ⟨endHeap, v', S₀, x₀, hs, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hc⟩
    exact ⟨endHeap, st', c, v', S₀, x₀, hs, hrun, h1, h2, h3, h4, h5, h6, h7, h8, h9, by omega⟩
  let r0 := (startState [g0Ptr, lenArr, L_in, P_fp, k_nat, L_w, vCap, eCap, handlesOut, heap] mem pos).regs
  have hr0 : r0 0 = g0Ptr := by simp [r0, startState]
  have hr1 : r0 1 = lenArr := by simp [r0, startState]
  have hr2 : r0 2 = L_in := by simp [r0, startState]
  have hr3 : r0 3 = P_fp := by simp [r0, startState]
  have hr4 : r0 4 = k_nat := by simp [r0, startState]
  have hr5 : r0 5 = L_w := by simp [r0, startState]
  have hr6 : r0 6 = vCap := by simp [r0, startState]
  have hr7 : r0 7 = eCap := by simp [r0, startState]
  have hr8 : r0 8 = handlesOut := by simp [r0, startState]
  have hr9 : r0 9 = heap := by simp [r0, startState]
  change ∃ o st' c, Runs w p ω (lemma55InitProc (b + 3) (lemma55BaseLsf b + lsfIdxInit) (b + 1) h)
    ⟨mem, r0, pos⟩ o st' c ∧ _ ∧ _
  dsimp only [lemma55InitProc]
  refine runs_seq_assign_flat (v := wtArr) (by simp [Expr.eval, hr9, wtArr]) ?_
  refine runs_seq_assign_flat (v := onePtr)
    (by simp [Expr.eval, BinOp.eval, hr7, hr2, wtArr, onePtr,
        show eCap * L_in < 2 ^ w by omega, show heap + eCap * L_in < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := rhoPtr)
    (by simp [Expr.eval, BinOp.eval, hr5, onePtr, rhoPtr, show onePtr + L_w < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := wtEnd)
    (by simp [Expr.eval, BinOp.eval, hr5, rhoPtr, wtEnd, show rhoPtr + L_w < 2 ^ w by omega]) ?_
  refine runs_seq_assign_flat (v := pL)
    (by simp [Expr.eval, BinOp.eval, hr3, hh_ltw, pL, show P_fp / h < 2 ^ w by omega]) ?_
  refine runs_seq_store_flat (x := onePtr + pL) (v := 1)
    (by simp [Expr.eval, BinOp.eval, show onePtr + pL < 2 ^ w by omega])
    (by simp [Expr.eval, show 1 < 2 ^ w by omega]) ?_
  let memOne := Function.update mem (onePtr + pL) 1
  have hgn_m1 : memOne (g0Ptr + dgNOff) = G₀.n := by
    have hlt_h : g0Ptr + dgNOff < heap := by dsimp [dgNOff, dynGraphSize] at hg0_le ⊢; omega
    have hlt : g0Ptr + dgNOff < onePtr + pL :=
      Nat.lt_of_lt_of_le hlt_h (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
    dsimp only [memOne]; rw [Function.update_of_ne (Nat.ne_of_lt hlt)]
    exact hgn_m
  refine runs_seq_assign_flat (v := G₀.n)
    (Expr.eval_load_of_eq (by
      have : g0Ptr + dgNOff < 2 ^ w := by dsimp [dgNOff, dynGraphSize] at hg0_le ⊢; omega
      simp [Expr.eval, BinOp.eval, hr0, show dgNOff < 2 ^ w by dsimp [dgNOff]; omega, this]) hgn_m1) ?_
  -- Call buildRhoFp
  obtain ⟨stRho, cRho, hrunRho, hv_rho, hint_rho, hscr_zero, hfr_rho, hcRho⟩ :=
    buildRhoFp_runs (p := p) (ω := ω) (mem := memOne) (pos := pos)
      (dst := rhoPtr) (scratch := wtEnd)
      hh hw hk hdiv hpL_le_Lw hrho_fit hn0_ltw
      (by have : 1 ≤ hldDepthBound G₀.n + 1 := Nat.succ_pos _; nlinarith)
      (by dsimp only [rhoPtr, wtEnd] at hsp_exp ⊢; omega)
      (by have : 4 * L_w ≤ max (4 * L_w) (mwuEdgeStepSpace L_in L_w P_fp) := le_max_left _ _; omega)
      (Or.inl le_rfl) hLog hEmit hLoad hMulU hFill
  let rPre := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update r0 10 wtArr) 11 onePtr) 12 rhoPtr) 13 wtEnd) 14 pL) 15 G₀.n
  have hcall_rho : Runs w p ω
      (.call 16 (b + 3) [.reg 12, .reg 15, .reg 4, .reg 5, .reg 14, .reg 13])
      ⟨memOne, rPre, pos⟩ .normal
      { mem := stRho.mem,
        regs := Function.update rPre 16 0,
        pos := stRho.pos }
      (argsSize [.reg 12, .reg 15, .reg 4, .reg 5, .reg 14, .reg 13] + cRho + 1) := by
    rw [runs_call_iff]
    exact ⟨[rhoPtr, G₀.n, k_nat, L_w, pL, wtEnd],
      buildRhoFpProc (lsfBaseUtils (lemma55BaseLsf b) + idxUtilLog2) (b + 4)
        (lsfBaseC1 Q_AN (lemma55BaseLsf b) + 1) (lsfBaseC1 Q_AN (lemma55BaseLsf b) + 2)
        (lsfBaseUtils (lemma55BaseLsf b) + idxUtilMemFill),
      .returned 0, stRho, cRho,
      by simp [evalArgs, Expr.eval, rPre, hr4, hr5], hpBuildRho, hrunRho, rfl, rfl, rfl⟩
  refine runs_seq_of_runs' hcall_rho ?_
  -- Initialize wtArr to v₀ ≡ 1 on active edges of G₀
  obtain ⟨eL, heL_len, heL_nd, heL_mem, heL_at, _⟩ := hdg0.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hm0_le : G₀.m ≤ eCap0 := (dynGraph_card_le hdg0).2
  have hg0_rho : ∀ a, g0Ptr ≤ a → a < g0Ptr + dynGraphSize vCap0 eCap0 → stRho.mem a = mem a := by
    intro a ha1 ha2
    rw [hfr_rho a (Or.inl (by omega)) (Or.inl (by omega))]
    dsimp only [memOne]
    exact Function.update_of_ne
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by omega : a < onePtr) (Nat.le_add_right onePtr pL))) 1 mem
  have hvCap0_rho : stRho.mem (g0Ptr + dgVCapOff) = vCap0 :=
    (hg0_rho _ (Nat.le_add_right _ _) (by dsimp [dgVCapOff, dynGraphSize]; omega)).trans hdg0.2.2.2.1
  have heCap0_rho : stRho.mem (g0Ptr + dgECapOff) = eCap0 :=
    (hg0_rho _ (Nat.le_add_right _ _) (by dsimp [dgECapOff, dynGraphSize]; omega)).trans hdg0.2.2.2.2.1
  have hm0_rho : stRho.mem (g0Ptr + dgMOff) = G₀.m :=
    (hg0_rho _ (Nat.le_add_right _ _) (by dsimp [dgMOff, dynGraphSize]; omega)).trans hdg0.2.2.2.2.2.2.1
  set eListPtr := dgEListBase g0Ptr vCap0 eCap0
  have heL_end : eListPtr + G₀.m ≤ g0Ptr + dynGraphSize vCap0 eCap0 := by
    dsimp [eListPtr, dgEListBase, dynGraphSize]; omega
  have heL_lt_rho : ∀ i < G₀.m, stRho.mem (eListPtr + i) < eCap := by
    intro i hi
    have hiL : i < eL.length := by rw [heL_len]; exact hi
    have h1 : stRho.mem (eListPtr + i) = eL[i] :=
      (hg0_rho _ (by dsimp [eListPtr, dgEListBase]; omega) (by omega)).trans (heL_at i hiL)
    rw [h1]
    exact lt_of_lt_of_le (hdg0.2.2.1 _ ((heL_mem _).mp (List.getElem_mem hiL))) heCap_le
  have hdg0_ltw : g0Ptr + dynGraphSize vCap0 eCap0 < 2 ^ w := by omega
  have hdg0_sz : dynGraphSize vCap0 eCap0 = 4 + 7 * vCap0 + 9 * eCap0 := rfl
  refine runs_seq_assign_flat (v := vCap0)
    (Expr.eval_load_of_eq (by
      simp [Expr.eval, BinOp.eval, rPre, hr0, dgVCapOff, show g0Ptr < 2 ^ w by omega]) hvCap0_rho) ?_
  refine runs_seq_assign_flat (v := eCap0)
    (Expr.eval_load_of_eq (by
      simp [Expr.eval, BinOp.eval, rPre, hr0, dgECapOff, show 1 < 2 ^ w by omega,
        show g0Ptr + 1 < 2 ^ w by omega]) heCap0_rho) ?_
  refine runs_seq_assign_flat (v := G₀.m)
    (Expr.eval_load_of_eq (by
      simp [Expr.eval, BinOp.eval, rPre, hr0, dgMOff, show 3 < 2 ^ w by omega,
        show g0Ptr + 3 < 2 ^ w by omega]) hm0_rho) ?_
  refine runs_seq_assign_flat (v := eListPtr)
    (by
      simp [Expr.eval, BinOp.eval, rPre, hr0, eListPtr, dgEListBase,
        show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
        show g0Ptr + 4 < 2 ^ w by omega, show 7 * vCap0 < 2 ^ w by omega,
        show g0Ptr + 4 + 7 * vCap0 < 2 ^ w by omega,
        show g0Ptr + 4 + 7 * vCap0 + eCap0 < 2 ^ w by omega]) ?_
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_
  have hwt_zero_rho : ∀ e < eCap, ∀ t < L_in, stRho.mem (wtArr + e * L_in + t) = 0 := by
    intro e he t ht
    have hm1 : (e + 1) * L_in ≤ eCap * L_in := Nat.mul_le_mul_right L_in (by omega)
    have ha1 : e * L_in + L_in = (e + 1) * L_in := by ring
    rw [hfr_rho _ (Or.inl (by omega)) (Or.inl (by omega))]
    dsimp only [memOne]
    rw [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by omega : wtArr + e * L_in + t < onePtr) (Nat.le_add_right _ _)))]
    exact hz _ (by omega)
  refine runs_seq_of_exists'
    (initWtLoop_runs (mem0 := stRho.mem) (p := p) (ω := ω) (eCap := eCap)
      h2w_16 hpL_lt_Lin (by omega) (by omega) heL_lt_rho 0 (Nat.zero_le _) _
      (by simp [rPre, hr2]) (by simp [rPre]) (by simp [rPre]) (by simp) (by simp) (by simp)
      (fun _ _ => rfl) (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (fun e he _ t ht => hwt_zero_rho e he t ht)) ?_
  intro stWt cWt ⟨hloWt, hfrWt, hinvWt, hcWt⟩
  -- Check initial state for mwuOuterLoop_runs
  have hwt_mem_eq_mem : ∀ z < wtEnd, (z < wtArr ∨ wtArr + eCap * L_in ≤ z) →
      (z < rhoPtr ∨ rhoPtr + L_w ≤ z) → z ≠ onePtr + pL → stWt.mem z = mem z := fun z hzw h1 h2 h3 => by
    rw [hfrWt z h1, hfr_rho z h2 (Or.inl hzw)]
    dsimp only [memOne]; rw [Function.update_of_ne h3]
  have hdg_wt : DynGraphAt stWt.mem g0Ptr vCap0 eCap0 G₀ :=
    hdg0.of_agree fun a ha1 ha2 => hwt_mem_eq_mem a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by omega : a < onePtr) (Nat.le_add_right _ _)))
  have hℓ_wt : ∀ e ∈ G₀.E, Valid stWt.mem (lenArr + e * L_in) h L_in ∧
      fixVal stWt.mem (lenArr + e * L_in) h L_in P_fp = ℓ₀_mem e ∧ 0 < ℓ₀_mem e := by
    intro e he
    have he_cap : e < eCap0 := hdg0.2.2.1 e he
    have he_mul : (e + 1) * L_in ≤ eCap0 * L_in := Nat.mul_le_mul_right L_in (by omega)
    have he_add : e * L_in + L_in = (e + 1) * L_in := by ring
    have heCap_mul : eCap0 * L_in ≤ eCap * L_in := Nat.mul_le_mul_right L_in heCap_le
    have hag : ∀ t < L_in, stWt.mem (lenArr + e * L_in + t) = mem (lenArr + e * L_in + t) := fun t ht =>
      hwt_mem_eq_mem _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by omega : lenArr + e * L_in + t < onePtr) (Nat.le_add_right _ _)))
    obtain ⟨hv0e, hfx0e, hpos0e⟩ := hℓ₀_mem e he
    refine ⟨fun t ht => by rw [hag t ht]; exact hv0e t ht, ?_, ?_⟩
    · dsimp only [ℓ₀_mem]; rw [memArrayReal_eq he]; unfold fixVal; rw [intVal_congr hag]
    · dsimp only [ℓ₀_mem]; rw [memArrayReal_eq he, hfx0e]; exact hpos0e
  have hℓ_wt_eq : ℓ₀_mem = memArrayReal stWt.mem lenArr G₀ h L_in P_fp := by
    funext e
    by_cases he : e ∈ G₀.E
    · rw [memArrayReal_eq he, (hℓ_wt e he).2.1]
    · dsimp only [ℓ₀_mem]; unfold memArrayReal; simp [he]
  have hone_wt : Valid stWt.mem onePtr h L_w ∧ intVal stWt.mem onePtr h L_w = (2 : ℤ) ^ P_fp := by
    have h1 := lemma55_one_limbs (mem := stWt.mem) (a := onePtr) (h := h) (L := L_w) (P_fp := P_fp)
      hh hdiv (by have : h * L_in ≤ h * L_w := Nat.mul_le_mul_left h hLin_le; omega) (fun i hi => by
        rw [hfrWt (onePtr + i) (Or.inr (by omega)), hfr_rho (onePtr + i) (Or.inl (by omega)) (Or.inl (by omega))]
        dsimp only [memOne]
        by_cases hip : i = pL
        · subst hip; rw [Function.update_self, ite_eq_left rfl]
        · rw [Function.update_of_ne (by omega), ite_eq_right hip]; exact hz _ (by omega))
    exact ⟨h1.1, h1.2.1⟩
  have hrho_wt : Valid stWt.mem rhoPtr h L_w ∧
      intVal stWt.mem rhoPtr h L_w = (lemma55RhoNat K_AN G₀.n k_nat : ℤ) * (2 : ℤ) ^ P_fp := by
    have hag : ∀ i < L_w, stWt.mem (rhoPtr + i) = stRho.mem (rhoPtr + i) := fun i hi =>
      hfrWt _ (Or.inr (by omega))
    exact ⟨fun i hi => by rw [hag i hi]; exact hv_rho i hi, (intVal_congr hag).trans hint_rho⟩
  have hz_wt : ZeroFrom stWt.mem wtEnd := by
    intro z hz'
    rw [hfrWt z (Or.inr (by omega))]
    by_cases hlt : z < wtEnd + 4 * L_w
    · have := hscr_zero (z - wtEnd) (by omega)
      rwa [show wtEnd + (z - wtEnd) = z by omega] at this
    · rw [hfr_rho z (Or.inr (by omega)) (Or.inr (by omega))]
      dsimp only [memOne]; rw [Function.update_of_ne (by omega)]
      exact hz z (by omega)
  have hwt0_ok : ∀ e ∈ G₀.E, Valid stWt.mem (wtArr + e * L_in) h L_in ∧
      fixVal stWt.mem (wtArr + e * L_in) h L_in P_fp = 1 := by
    intro e he
    obtain ⟨i, hiL, rfl⟩ := List.mem_iff_getElem.mp ((heL_mem e).mpr he)
    have hi_m : i < G₀.m := by rw [← heL_len]; exact hiL
    have hme : stRho.mem (eListPtr + i) = eL[i] :=
      (hg0_rho _ (by dsimp [eListPtr, dgEListBase]; omega) (by omega)).trans (heL_at i hiL)
    have h1 := lemma55_one_limbs (mem := stWt.mem) (a := wtArr + eL[i] * L_in) (h := h) (L := L_in) (P_fp := P_fp)
      hh hdiv (by omega) (fun t ht => by rw [← hme]; exact hinvWt i hi_m t ht)
    exact ⟨h1.1, h1.2.2⟩
  -- Run the k_nat-round MWU loop
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_
  have hstWt_r : stWt.regs 0 = g0Ptr ∧ stWt.regs 1 = lenArr ∧ stWt.regs 2 = L_in ∧
      stWt.regs 3 = P_fp ∧ stWt.regs 4 = k_nat ∧ stWt.regs 5 = L_w ∧ stWt.regs 6 = vCap ∧
      stWt.regs 7 = eCap ∧ stWt.regs 8 = handlesOut ∧ stWt.regs 10 = wtArr ∧
      stWt.regs 11 = onePtr ∧ stWt.regs 12 = rhoPtr ∧ stWt.regs 13 = wtEnd := by
    refine ⟨(hloWt 0 (by decide)).trans (by simp [rPre, hr0]),
      (hloWt 1 (by decide)).trans (by simp [rPre, hr1]),
      (hloWt 2 (by decide)).trans (by simp [rPre, hr2]),
      (hloWt 3 (by decide)).trans (by simp [rPre, hr3]),
      (hloWt 4 (by decide)).trans (by simp [rPre, hr4]),
      (hloWt 5 (by decide)).trans (by simp [rPre, hr5]),
      (hloWt 6 (by decide)).trans (by simp [rPre, hr6]),
      (hloWt 7 (by decide)).trans (by simp [rPre, hr7]),
      (hloWt 8 (by decide)).trans (by simp [rPre, hr8]),
      (hloWt 10 (by decide)).trans (by simp [rPre]),
      (hloWt 11 (by decide)).trans (by simp [rPre]),
      (hloWt 12 (by decide)).trans (by simp [rPre]),
      (hloWt 13 (by decide)).trans (by simp [rPre])⟩
  rcases hstWt_r with ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w10, w11, w12, w13⟩
  let dummyS : LSFState :=
    { G₀ := G₀, G := G₀, k := 1, v := fun _ => 1, T₀ := G₀, r₀ := 0, π := fun _ => 0, R₀_init := ∅,
      R₀_base := ∅, T_cur := G₀, isolatedVerts := ∅, origVert := id, insertedEdges := ∅,
      numUpdates := 0, wstr := fun _ => 1, W_init := ∅ }
  let dummyX : LSFConcrete :=
    { vCap := 0, eCap := 0, n0 := 0, m0 := 0, tM := 0, h := h, P_fp := 0, L_in := 0, L_w := 0,
      k_nat := 1, tOrigList := [], vList := [], t0Parent := fun _ => 0,
      t0ParentTreeIdx := fun _ => 0, t0Depth := fun _ => 0, thParent := fun _ => 0,
      upV := fun _ _ => 0, upMinIdx := fun _ _ => 0, rList := [], compId := fun _ => 0,
      compRoot := fun _ => 0, compSize := fun _ => 0, activeCids := ∅ }
  obtain ⟨stEnd, cOut, endHeap, v', S₀, x₀, hs, hrunOut, h13_end, hwe_end, hend_le, hz_end, hfr_end,
    hv0', hv_pos', hinit', hv_step', hhnd', hcOut⟩ :=
    mwuOuterLoop_runs (p := p) (ω := ω) (mem0 := stWt.mem) (bLsf := lemma55BaseLsf b)
      (bWeightsLoop := b + 1) (bEdgeStep := b + 2) (bDiv := lemma55BaseDiv Q_AN b)
      (bExp := lemma55BaseExp Q_AN b) (bMul := lemma55BaseMul Q_AN b)
      (bCopy := lsfBaseUtils (lemma55BaseLsf b) + idxUtilMemCopy)
      (bFill := lsfBaseUtils (lemma55BaseLsf b) + idxUtilMemFill)
      hc hh hw hLin1 hLin_le hk hdiv hq_P hk_q hP_Lin hm_Lin h2P_ltw hHld_ltw hrho_cap
      hG₀ hV₀ hdg_wt hvCap_le heCap_le heCap1 hℓ_wt hℓ_wt_eq
      hg0_le hlen_le hhnd_le hhnd_g0 hhnd_len rfl rfl rfl hsp
      hone_wt.1 hone_wt.2 hrho_wt.1 hrho_wt.2
      hpLsf hQ hpWLoop hpStep hDiv hExp hMul hCopy hFill
      0 (Nat.zero_le _) { stWt with regs := Function.update stWt.regs 16 0 } wtEnd
      (fun _ => memArrayReal stWt.mem wtArr G₀ h L_in P_fp)
      (fun _ => dummyS) (fun _ => dummyX) (fun _ => 0)
      (by simp [w0]) (by simp [w1]) (by simp [w2]) (by simp [w3]) (by simp [w4])
      (by simp [w5]) (by simp [w6]) (by simp [w7]) (by simp [w8]) (by simp [w10])
      (by simp [w11, onePtr]) (by simp [w12, rhoPtr, onePtr]) (by simp [w13]) (by simp)
      le_rfl (by rw [Nat.zero_mul, Nat.add_zero]) hz_wt (fun _ _ _ _ => rfl)
      (fun e he => ⟨(hwt0_ok e he).1, (memArrayReal_eq he).symm⟩) rfl
      (fun e he => (memArrayReal_eq he).trans (hwt0_ok e he).2)
      (fun _ _ e he => by rw [memArrayReal_eq he, (hwt0_ok e he).2]; exact zero_lt_one)
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
  refine runs_seq_of_runs' hrunOut ?_
  refine runs_ret_le (v := endHeap) (by simp [Expr.eval, h13_end])
    ⟨endHeap, v', S₀, x₀, hs, rfl, by omega,
      by dsimp only [lemma55Space]; omega,
      hz_end,
      fun z hzh hzhnd => (hfr_end z hzh hzhnd).trans
        (hwt_mem_eq_mem z (by omega) (Or.inl hzh) (Or.inl (by omega))
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le (by omega : z < onePtr) (Nat.le_add_right _ _)))),
      hv0', hv_pos', hinit', hv_step',
      fun j hj => ⟨(hhnd' j hj).1, (hhnd' j hj).2.1,
        fun a ha => ⟨by have := (hhnd' j hj).2.2 a ha; omega, ((hhnd' j hj).2.2 a ha).2⟩⟩⟩ ?_
  rw [Nat.sub_zero] at hcOut hcWt
  dsimp only [lemma55Cost, argsSize, Expr.size]
  have h_k : k_nat * (lsfInitCostFactor *
      Nat.ceil (((G₀.m + G₀.n + 1 : ℕ) : ℝ) * lsfOverhead Q_AN c_AN K_AN G₀.n G₀.m L_in L_w h) +
      G₀.m * (mwuEdgeStepCost L_in L_w P_fp + 80) + 190) ≤
    k_nat * (lsfInitCostFactor *
      Nat.ceil (((G₀.m + G₀.n + 1 : ℕ) : ℝ) * lsfOverhead Q_AN c_AN K_AN G₀.n G₀.m L_in L_w h) +
      G₀.m * (mwuEdgeStepCost L_in L_w P_fp + 80) + 200) :=
    Nat.mul_le_mul_left k_nat (by omega)
  omega

/-- End-to-end unconditional Word-RAM realization of **Lemma 5.5** (`arXiv:2309.16629v1`, page 17
and Appendix A.2, pages 48–49) using the verified low-stretch spanning tree program
(`cited_c_pos_of_lsst`), working for every limb width `h ≥ 1` (in particular both `h = 1` and
`h = 4`). -/
theorem lemma55Program_from_cited (h : ℕ) :
    ∃ (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ),
      1 ≤ c_AN ∧
      (lemma55Module Q_AN c_AN K_AN h).IsDeterministic ∧
      (∀ (w q g0Ptr lenArr L_in P_fp k_nat L_w vCap eCap handlesOut heap vCap0 eCap0 : ℕ)
          (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
        1 ≤ h → 3 * h + 2 ≤ w →
        1 ≤ L_in → L_in ≤ L_w → 1 ≤ k_nat →
        h ∣ P_fp → q + 11 ≤ P_fp → 8 * k_nat ≤ 2 ^ q →
        P_fp + 6 ≤ h * L_in →
        32 * (G₀.E.card + 1) * 2 ^ P_fp < 2 ^ (h * L_in - 1) →
        2 * P_fp + 9 < 2 ^ w →
        3 * (4 * k_nat * (hldDepthBound G₀.n + 1)) < 2 ^ w →
        lemma55RhoNat K_AN G₀.n k_nat < 2 ^ (h * (L_w - L_in)) →
        G₀.IsValid → G₀.V.Nonempty →
        DynGraphAt mem g0Ptr vCap0 eCap0 G₀ →
        vCap0 ≤ vCap → eCap0 ≤ eCap → 1 ≤ eCap →
        (∀ e ∈ G₀.E, Valid mem (lenArr + e * L_in) h L_in ∧
          fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e) →
        g0Ptr + dynGraphSize vCap0 eCap0 ≤ heap →
        lenArr + eCap0 * L_in ≤ heap →
        handlesOut + k_nat ≤ heap →
        (handlesOut + k_nat ≤ g0Ptr ∨ g0Ptr + dynGraphSize vCap0 eCap0 ≤ handlesOut) →
        (handlesOut + k_nat ≤ lenArr ∨ lenArr + eCap0 * L_in ≤ handlesOut) →
        ZeroFrom mem heap →
        heap + lemma55Space Q_AN K_AN c_AN h L_in L_w P_fp k_nat vCap eCap G₀.n G₀.m < 2 ^ w →
        let K₀ := lemma54K0 (4 * max K_AN 1 + 5) (5 / 4) (defaultK_sigma K_AN : ℝ)
        let K := (16 + 4 * (40960 : ℝ)) * K₀ + 128
        ∃ body, (lemma55Module Q_AN c_AN K_AN h).procs[lemma55IdxInit]? = some body ∧
          ∃ (endHeap : ℕ) (st' : State) (c : ℕ) (S₀ : ℕ → LSFState) (x₀ : ℕ → LSFConcrete) (hs : ℕ → ℕ),
            Runs w (lemma55Module Q_AN c_AN K_AN h) ω body
              (startState [g0Ptr, lenArr, L_in, P_fp, k_nat, L_w, vCap, eCap, handlesOut, heap] mem pos)
              (.returned endHeap) st' c ∧
            heap ≤ endHeap ∧
            endHeap ≤ heap + lemma55Space Q_AN K_AN c_AN h L_in L_w P_fp k_nat vCap eCap G₀.n G₀.m ∧
            ZeroFrom st'.mem endHeap ∧
            (∀ z < heap, (z < handlesOut ∨ handlesOut + k_nat ≤ z) → st'.mem z = mem z) ∧
            (∀ j < k_nat, st'.mem (handlesOut + j) = hs j ∧
              (LSFRep h).rep (hs j) (S₀ j) (x₀ j) st'.mem ∧
              ∀ a, (LSFRep h).foot (hs j) (x₀ j) a → heap ≤ a ∧ a < endHeap) ∧
            c ≤ lemma55Cost Q_AN c_AN K_AN h L_in L_w P_fp k_nat G₀.n G₀.m ∧
            (∀ (Us : List (List Update)), BatchesIsValid G₀ Us →
              ∀ (ℓ : ℕ → ℝ),
                (∀ e ∈ (Us.foldl MGraph.applyBatch G₀).E, 0 < ℓ e) →
                (∀ e ∈ G₀.E, e ∈ (Us.foldl MGraph.applyBatch G₀).E →
                  e ∉ batchesInserted Us → ℓ e = ℓ₀ e) →
                let G := Us.foldl MGraph.applyBatch G₀
                let S : ℕ → LSFState := fun j => applyLSFBatches (S₀ j) Us
                (∀ j < k_nat, (S j).lsf.Holds G ℓ (K * (k_nat : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 6)) ∧
                ∀ e ∈ G.E,
                  ∑ j ∈ Finset.range k_nat, ((1 : ℝ) / (k_nat : ℝ)) * (S j).wstr e ≤
                    K * (Real.log ((G₀.n : ℝ) + 2)) ^ 6 * Real.log ((G₀.E.card : ℝ) + 2))) := by
  obtain ⟨Q_AN, c_AN, K_AN, hc_pos, hQ⟩ := cited_c_pos_of_lsst
  have hp0 : (lemma55Module Q_AN c_AN K_AN h).HasAt 0 (lemma55ModuleProcs Q_AN c_AN K_AN 0 h) := by
    intro i hi; simp [lemma55Module, hi]
  refine ⟨Q_AN, c_AN, K_AN, hc_pos, lemma55Module_isDeterministic Q_AN c_AN K_AN h, ?_⟩
  intro w q g0Ptr lenArr L_in P_fp k_nat L_w vCap eCap handlesOut heap vCap0 eCap0
    G₀ ℓ₀ mem pos ω hh hw hLin1 hLin_le hk hdiv hq_P hk_q hP_Lin hm_Lin h2P_ltw hHld_ltw
    hrho_cap hG₀ hV₀ hdg0 hvCap_le heCap_le heCap1 hℓ₀_mem hg0_le hlen_le hhnd_le hhnd_g0
    hhnd_len hz hsp
  obtain ⟨body, hbody, endHeap, st', c, S₀, x₀, hs, hrun, hhe1, hhe2, hz', hfr', hhnd', hc', h55⟩ :=
    lemma55Program_runs pos ω hp0 hQ hc_pos hh hw hLin1 hLin_le hk hdiv hq_P hk_q hP_Lin hm_Lin
      h2P_ltw hHld_ltw hrho_cap hG₀ hV₀ hdg0 hvCap_le heCap_le heCap1 hℓ₀_mem hg0_le hlen_le
      hhnd_le hhnd_g0 hhnd_len hz hsp
  refine ⟨body, by simpa only [Nat.zero_add] using hbody,
    endHeap, st', c, S₀, x₀, hs, hrun, hhe1, hhe2, hz', hfr', hhnd', hc', ?_⟩
  intro Us hUs ℓ hℓ hℓ_orig
  obtain ⟨hper, havg⟩ := h55 Us hUs ℓ hℓ hℓ_orig
  exact ⟨fun j hj => (hper j hj).2.2.2.2.2.2.2.2.2.1, havg⟩

end

end MinCostFlow.LSF.Program
