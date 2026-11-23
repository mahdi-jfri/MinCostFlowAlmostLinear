module

public import MinCostFlow.SparseCore.SparseCoreRecourse
import MinCostFlow.DynSpanner.WalkCount

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Walk-flow helpers and single-step backward stability for `sparseCoreTool`

Provides the walk-flow helpers, `BucketStepDisjoint`, `nonCanceling_off_S_of_bucketStepDisjoint`,
and the single-step backward preservation lemmas (`weakHidden_step_backward_core`,
`weakHidden_step_backward`) used by `SparseCoreStability.lean`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## 1. Walk-flow, disjoint-component, and clause-3 gap helpers -/

private lemma abs_walkFlow_le_length (P : List (ℕ × Bool)) (e' : ℕ) :
    |walkFlow P e'| ≤ (P.length : ℝ) := by
  induction P with
  | nil => simp [walkFlow]
  | cons x xs ih =>
    unfold walkFlow at ih ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have hx : |if x.1 = e' then (if x.2 then (1 : ℝ) else -1) else 0| ≤ 1 := by
      split_ifs <;> norm_num
    linarith [abs_add_le (if x.1 = e' then (if x.2 then (1 : ℝ) else -1) else 0)
      (xs.map fun y => if y.1 = e' then (if y.2 then (1 : ℝ) else -1) else 0).sum]

private lemma isWalk_walkEdges_sub {H : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : H.IsWalk u v P) : walkEdges P ⊆ H.E := by
  induction hW with
  | nil _ => simp [walkEdges]
  | cons he _ _ ih =>
    intro x hx
    simp only [walkEdges, List.map_cons, List.toFinset_cons, Finset.mem_insert] at hx ⊢
    rcases hx with rfl | hx'
    · exact he
    · exact ih hx'

private lemma batchPrefixLen_le_flatten (Us : List (List Update)) (t : ℕ) :
    batchPrefixLen Us t ≤ Us.flatten.length := by
  induction Us generalizing t with
  | nil => simp [batchPrefixLen]
  | cons u us ih =>
    cases t with
    | zero => simp [batchPrefixLen]
    | succ t =>
      simp only [batchPrefixLen, List.take_succ_cons, List.flatten_cons, List.length_append]
      exact Nat.add_le_add_left (ih t) _

private lemma mem_comp_eq_of_mem_ts_and_compG {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {cs₀ cs : CompLSFState} (hI : CompLSFInv C_lsst ℓ₀ cs) (hG₀_eq : cs.G₀ = cs₀.G₀)
    {C₁ C₂ : Finset ℕ} (hC₁ : C₁ ∈ components cs₀.G₀) (hC₂ : C₂ ∈ components cs₀.G₀)
    {ts₁ : TildeState} (hT₁ : TildeInv (cs₀.compSt C₁) (cs.compSt C₁) ts₁)
    (hDisj₁ : Disjoint ts₁.C.E (cs.compSt C₁).insertedEdges)
    {e : ℕ} (he₁ : e ∈ ts₁.C.E) (he₂ : e ∈ (cs.compSt C₂).G.E) :
    C₁ = C₂ := by
  by_contra hne
  have hC₁' := hG₀_eq ▸ hC₁
  have hC₂' := hG₀_eq ▸ hC₂
  have heG₁ : e ∈ (cs.compSt C₁).G.E := (Finset.mem_sdiff.mp (hT₁.hCE_sub he₁)).1
  have hnotIns : e ∉ (cs.compSt C₁).insertedEdges := Finset.disjoint_left.mp hDisj₁ he₁
  have hnotCross : e ∉ cs.crossEdges := hI.hNonIns_notCross C₁ hC₁' e heG₁ hnotIns
  have hend₁ := hI.hNonCross_ends C₁ hC₁' e heG₁ hnotCross
  have hend₂ := hI.hNonCross_ends C₂ hC₂' e he₂ hnotCross
  have hv₁ : (cs.compSt C₁).G.tail e ∈ (cs.compSt C₁).G.V :=
    ((hI.hCompLSF C₁ hC₁').1.hG_val e heG₁).1
  have hv₂ : (cs.compSt C₂).G.tail e ∈ (cs.compSt C₂).G.V :=
    ((hI.hCompLSF C₂ hC₂').1.hG_val e he₂).1
  rw [hend₁.1, ← hend₂.1] at hv₁
  exact Finset.disjoint_left.mp (hI.hV_disj C₁ hC₁' C₂ hC₂' hne) hv₁ hv₂

/-- Per-bucket `DynSpanner` step-disjointness (`Disjoint D H.E`) across positive levels. -/
def BucketStepDisjoint (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) : Prop :=
  ∀ j < k, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    let Hb₀ := initBucketGraph (cs₀.compSt C) (D.ℓ 0) b
    let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
      ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
    let Us := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
    let q_b := phaseBase (Hb₀.n + splitB) L
    ∀ m < Us.flatten.length, 0 < chooseLevel L q_b (m + 1) →
      Disjoint (runStepOut (L := L) Hb₀ q_b (sparsify M) Us.flatten m).D
        (runState (L := L) Hb₀ q_b (sparsify M) Us.flatten m).H.E

lemma initCompLSF_RF_cov
    {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst) {k : ℕ} (hk : 1 ≤ k) {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (j : ℕ) {C : Finset ℕ} (hC : C ∈ components (D.G 0)) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    (cs₀.compSt C).G = compGraph (D.G 0) C ∧
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E := by
  have hsp := initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC
  exact ⟨hsp.2.1, hsp.2.2⟩

lemma nonCanceling_off_S_of_bucketStepDisjoint
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst) (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hBSD : BucketStepDisjoint oracle C_lsst L sparsify k M N τ D) :
    ∀ t ≤ τ, ∀ j < k,
      let st := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      ∀ e ∈ (coreGraph (D.G t) st.cs.lsf).E, e ∉ st.S_cur.E →
        ∀ e' ∈ walkEdges (st.emb e), |walkFlow (st.emb e) e'| = 1 := by
  intro t ht j hj st e _ he_notS e' he'_w
  obtain ⟨hBase, _, hFlat⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  have hbt := hBase t ht
  have hEx : ∃ C ∈ st.activeComps, e ∈ (st.ts C).C.E := by
    by_contra hnone
    have hemb_nil : st.emb e = [] := by
      dsimp only [TreeCoreState.emb]; simp only [he_notS, ↓reduceIte, hnone, ↓reduceDIte]
    rw [hemb_nil, walkEdges] at he'_w; simp at he'_w
  let C := hEx.choose
  have hC_act : C ∈ st.activeComps := hEx.choose_spec.1
  have heC_ts : e ∈ (st.ts C).C.E := hEx.choose_spec.2
  have hC_comp : C ∈ components (D.G 0) := hbt.2.2.2.2.2.2.2.2.2.2.1.2 hC_act
  have hemb_eq : st.emb e = piTotal (st.dyn (C, st.origBucket e)) e := by
    dsimp only [TreeCoreState.emb]; simp only [he_notS, ↓reduceIte, hEx, ↓reduceDIte]; rfl
  rw [hemb_eq] at he'_w ⊢
  set cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
  set b := st.origBucket e
  set Hb₀ := initBucketGraph (cs₀.compSt C) (D.ℓ 0) b
  set splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
    ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
  set Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
  set q_b := phaseBase (Hb₀.n + splitB) L
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hS₀C_spec := initCompLSF_RF_cov hLSST hk hG₀ hℓ₀ j hC_comp
  have hHb := initBucketGraph_spec (hI₀.hCompLSF C hC_comp).1 hS₀C_spec.2 b
  have hHb_val : Hb₀.IsValid := hHb.1
  have hHb_m : Hb₀.m ≤ M := le_trans (le_trans hHb.2.2.2.2.2.2.2.1
    (by rw [hS₀C_spec.1]; exact compGraph_m_le)) hM
  have hq1 : 1 ≤ q_b := le_trans (by omega) (two_le_phaseBase (Hb₀.n + splitB) L)
  have hfb := hFlat C hC_comp b
  have hUs_len : Us_b.length = τ := by simp [Us_b, bucketBatchList]
  have htr := (batchTrace_spec hHb_val hL hq1 hHb_m hSp hfb.1 hfb.2.1).1 t (by rw [hUs_len]; exact ht)
  have hdynC := (hbt.2.2.2.2.2.2.2.2.2.2.2.2 C hC_comp).2.2.2.2 b
  have hdyn_eq : st.dyn (C, b) = runBatchState Hb₀ q_b (sparsify M) Us_b t := by
    simpa [cs₀, Hb₀, splitB, Us_b, q_b] using hdynC.2.2.2
  have heG : e ∈ (runState (L := L) Hb₀ q_b (sparsify M) Us_b.flatten (batchPrefixLen Us_b t)).G.E := by
    rw [← htr.1, ← hdyn_eq, hdynC.2.2.1, Finset.mem_filter]
    refine ⟨heC_ts, ?_⟩
    have hT0 := initTildeState_inv (hI₀.hCompLSF C hC_comp).1 hS₀C_spec.2
    have heG₀ : e ∈ (D.G 0).E :=
      (Finset.mem_sdiff.mp (compLSF_comp_sdiff_sub hI₀ hC_comp
        (hT0.hCE_sub ((hbt.2.2.2.2.2.2.2.2.2.2.2.2 C hC_comp).2.2.1 heC_ts)))).1
    dsimp only [b]; rw [hbt.2.2.2.2.1]; simp [coreLen, safeLen, heG₀]
  rw [hdyn_eq, htr.1] at he'_w ⊢
  exact piTotal_walkFlow_abs_eq_one_of_stepDisjoint hHb_val hL hq1 hHb_m hSp hfb.1 hfb.2.1
    (batchPrefixLen Us_b t) (batchPrefixLen_le_flatten Us_b t)
    (fun m hm hcl => hBSD j hj C hC_comp b m (lt_of_lt_of_le hm (batchPrefixLen_le_flatten Us_b t)) hcl)
    e heG e' he'_w

/-! ## 2. Backward step lemma and unconditional `WeakHiddenStable` items 1, 2, 4 -/

private lemma mem_buildUSReinsert_insEdges
    (cs_old : CompLSFState) (U : List Update) (cs_new : CompLSFState)
    (S_prev : MGraph) (targetE D_reins : Finset ℕ) {e : ℕ}
    (heT : e ∈ targetE)
    (hNoIns : ∀ u ∈ buildUSReinsert cs_old U cs_new S_prev targetE D_reins, ¬ u.Inserts e) :
    e ∈ ((S_prev.E ∩ targetE) \ batchDeletes U) \ D_reins := by
  by_contra hnot
  apply hNoIns (.insert e (cs_new.RF.root (cs_new.G.tail e)) (cs_new.RF.root (cs_new.G.head e)))
  · dsimp only [buildUSReinsert]
    simp only [List.mem_append, List.mem_map]
    right
    exact ⟨e, Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨heT, hnot⟩), rfl⟩
  · rfl

/-- Core single-step backward preservation helper for clause 3 of `WeakHiddenStable`,
parameterized over arbitrary `TreeCoreState` states `st_s, st_s1` whose `.cs, .ts, .activeComps,
.origBucket, .activeBuckets` agree with `treeRunSeq` at steps `s` and `s + 1` and whose bucket
spanners evolve via `stepTreeCoreAux`. -/
lemma weakHidden_step_backward_core
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) {s : ℕ} (hs_lt : s < τ)
    (st_s st_s1 : TreeCoreState L)
    (hst_step : st_s1 = (stepTreeCoreAux sparsify st_s (D.U (s + 1))).state)
    (_hm₀_s : st_s.m₀ = M)
    (hcs_s : st_s.cs = (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cs)
    (hcs_s1 : st_s1.cs = (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.cs)
    (hts_s : st_s.ts = (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.ts)
    (hts_s1 : st_s1.ts = (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.ts)
    (hact_s : st_s.activeComps = (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.activeComps)
    (hact_s1 : st_s1.activeComps = (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps)
    (horig_s : st_s.origBucket = (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.origBucket)
    (horig_s1 : st_s1.origBucket = (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.origBucket)
    (hactB_s : st_s.activeBuckets = (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.activeBuckets)
    (hS_sub_s : (coreGraph st_s.cs.G st_s.cs.lsf).IsSubgraph st_s.S_cur)
    (hS_E_s : st_s.S_cur.E =
      (st_s.activeComps.biUnion fun C => (st_s.activeBuckets C).biUnion fun b => (st_s.dyn (C, b)).H.E) ∪
        (st_s.activeComps.biUnion fun C => extraSet (st_s.cs.compSt C) (st_s.ts C)) ∪
        st_s.cs.crossEdges)
    (hS_E_s1 : st_s1.S_cur.E =
      (st_s1.activeComps.biUnion fun C => (st_s1.activeBuckets C).biUnion fun b => (st_s1.dyn (C, b)).H.E) ∪
        (st_s1.activeComps.biUnion fun C => extraSet (st_s1.cs.compSt C) (st_s1.ts C)) ∪
        st_s1.cs.crossEdges)
    (hDyn_G_s : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (st_s.ts C).C.IsSubgraph (st_s.dyn (C, b)).G ∧
      (st_s.dyn (C, b)).G.E = (st_s.ts C).C.E.filter (fun e => st_s.origBucket e = b) ∧
      (st_s.dyn (C, b)).G.IsSubgraph (st_s.dyn (C, b)).H)
    (hDyn_G_s1 : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (st_s1.dyn (C, b)).G.E = (st_s1.ts C).C.E.filter (fun e => st_s1.origBucket e = b) ∧
      (st_s1.dyn (C, b)).G.IsSubgraph (st_s1.dyn (C, b)).H ∧
      (piTotal (st_s1.dyn (C, b))).IsEmbedding (st_s1.dyn (C, b)).G (st_s1.dyn (C, b)).H)
    (hDyn_step : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let stepOut := (stepTreeCoreAux sparsify st_s (D.U (s + 1))).stepOut (C, b)
      stepOut = update (st_s.dyn (C, b)) ((stepTreeCoreAux sparsify st_s (D.U (s + 1))).U_b (C, b))
        (sparsify st_s.m₀) ∧
      stepOut.state = st_s1.dyn (C, b) ∧
      (∀ eG ∈ (st_s1.dyn (C, b)).G.E,
        ∀ eH ∈ walkEdges (piTotal (st_s1.dyn (C, b)) eG),
          eH ∉ stepOut.D → eH ∈ walkEdges (piTotal (st_s.dyn (C, b)) eG)) ∧
      (∀ eG ∈ (st_s1.dyn (C, b)).G.E, ∀ e' : ℕ,
        e' ∉ stepOut.D →
        walkCount (piTotal (st_s1.dyn (C, b)) eG) e' ≤ walkCount (piTotal (st_s.dyn (C, b)) eG) e'))
    {e' : ℕ}
    (he'_cur : e' ∈ st_s1.S_cur.E)
    (hNoIns : ∀ u ∈ (stepTreeCoreAux sparsify st_s (D.U (s + 1))).U_S, ¬ u.Inserts e') :
    e' ∈ st_s.S_cur.E ∧
    e' ∉ batchDeletes (D.U (s + 1)) ∧
    ∀ e ∈ (coreGraph (D.G (s + 1)) st_s1.cs.lsf).E, e' ∈ walkEdges (st_s1.emb e) →
      e ∈ (coreGraph (D.G s) st_s.cs.lsf).E ∧
      e' ∈ walkEdges (st_s.emb e) ∧
      walkCount (st_s1.emb e) e' ≤ walkCount (st_s.emb e) e' ∧
      (∀ u ∈ D.U (s + 1), ¬ u.Inserts e) := by
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  have hs_le : s ≤ τ := Nat.le_of_lt hs_lt
  have hs1_le : s + 1 ≤ τ := hs_lt
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  set cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
  set ts₀ := fun C => initTildeState (cs₀.compSt C)
  have hcs₀_G₀ : cs₀.G₀ = D.G 0 := rfl
  have hCov₀ : ∀ C ∈ components (D.G 0),
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E :=
    fun C hC => (initCompLSF_RF_cov hLSST hk hG₀ hℓ₀ j hC).2
  rcases hBase s hs_le with ⟨_, _, _, _, horig_base_s, hactB_base_s, _, hcs_base_s, hI_base_s, hG_base_s,
    hAct_base_s, _, hC_base_s⟩
  rcases hBase (s + 1) hs1_le with ⟨_, _, _, _, horig_base_s1, hactB_base_s1, _, hcs_base_s1, hI_base_s1,
    hG_base_s1, hAct_base_s1, _, hC_base_s1⟩
  have horig_s' : st_s.origBucket = fun e => bucketOf (coreLen cs₀.lsf (safeLen (D.G 0) (D.ℓ 0)) e) := by
    rw [horig_s]; exact horig_base_s
  have horig_s1' : st_s1.origBucket = fun e => bucketOf (coreLen cs₀.lsf (safeLen (D.G 0) (D.ℓ 0)) e) := by
    rw [horig_s1]; exact horig_base_s1
  have horig_on_ts0 : ∀ C ∈ components (D.G 0), ∀ x ∈ (ts₀ C).C.E,
      bucketOf (coreLen cs₀.lsf (safeLen (D.G 0) (D.ℓ 0)) x) =
        bucketOf (coreLen cs₀.lsf (D.ℓ 0) x) := by
    intro C hC x hx
    have hT0 := initTildeState_inv (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
    have hxG₀ : x ∈ (D.G 0).E :=
      (Finset.mem_sdiff.mp (compLSF_comp_sdiff_sub hI₀ (hcs₀_G₀ ▸ hC) (hT0.hCE_sub hx))).1
    simp [coreLen, safeLen, hxG₀]
  have hactB_s' : st_s.activeBuckets = fun C => (ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e)) := by
    rw [hactB_s]; exact hactB_base_s
  have hI_s : CompLSFInv C_lsst (D.ℓ 0) st_s.cs := hcs_s ▸ hI_base_s
  have hI_s1 : CompLSFInv C_lsst (D.ℓ 0) st_s1.cs := hcs_s1 ▸ hI_base_s1
  have hG_s : st_s.cs.G = D.G s := hcs_s ▸ hG_base_s
  have hG_s1 : st_s1.cs.G = D.G (s + 1) := hcs_s1 ▸ hG_base_s1
  have hAct_s : largeComps k (D.G 0) ⊆ st_s.activeComps ∧ st_s.activeComps ⊆ components (D.G 0) :=
    hact_s ▸ hAct_base_s
  have hAct_s1 : largeComps k (D.G 0) ⊆ st_s1.activeComps ∧ st_s1.activeComps ⊆ components (D.G 0) :=
    hact_s1 ▸ hAct_base_s1
  have hcs_seq_s : st_s.cs = compLSFBatch cs₀ (dynBatches D s).flatten := hcs_s ▸ hcs_base_s
  have hcs_seq_s1 : st_s1.cs = compLSFBatch cs₀ (dynBatches D (s + 1)).flatten := hcs_s1 ▸ hcs_base_s1
  have hC_props_s : ∀ C ∈ components (D.G 0),
      LSFDerivedFrom (cs₀.compSt C) (st_s.cs.compSt C) ∧
      TildeInv (cs₀.compSt C) (st_s.cs.compSt C) (st_s.ts C) ∧
      (st_s.ts C).C.E ⊆ (ts₀ C).C.E ∧
      Disjoint (st_s.ts C).C.E (st_s.cs.compSt C).insertedEdges := fun C hC => by
    have hp := hC_base_s C hC
    exact ⟨hcs_s ▸ hp.1, hcs_s ▸ hts_s ▸ hp.2.1, hts_s ▸ hp.2.2.1, hcs_s ▸ hts_s ▸ hp.2.2.2.1⟩
  have hC_props_s1 : ∀ C ∈ components (D.G 0),
      LSFDerivedFrom (cs₀.compSt C) (st_s1.cs.compSt C) ∧
      TildeInv (cs₀.compSt C) (st_s1.cs.compSt C) (st_s1.ts C) ∧
      (st_s1.ts C).C.E ⊆ (ts₀ C).C.E ∧
      Disjoint (st_s1.ts C).C.E (st_s1.cs.compSt C).insertedEdges := fun C hC => by
    have hp := hC_base_s1 C hC
    exact ⟨hcs_s1 ▸ hp.1, hcs_s1 ▸ hts_s1 ▸ hp.2.1, hts_s1 ▸ hp.2.2.1, hcs_s1 ▸ hts_s1 ▸ hp.2.2.2.1⟩
  have hG₀_s : st_s.cs.G₀ = cs₀.G₀ := by rw [hcs_seq_s, compLSFBatch_G₀]
  have hG₀_s1 : st_s1.cs.G₀ = cs₀.G₀ := by rw [hcs_seq_s1, compLSFBatch_G₀]
  set origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e)
  set actB : Finset ℕ → Finset ℤ := fun C => (ts₀ C).C.E.image origB
  have hactB_s1' : st_s1.activeBuckets = actB := by
    rw [hst_step]
    change st_s.activeBuckets = actB
    exact hactB_s'
  let targetE' := (st_s1.activeComps.biUnion fun C => (actB C).biUnion fun b => (st_s1.dyn (C, b)).H.E) ∪
    (st_s1.activeComps.biUnion fun C => extraSet (st_s1.cs.compSt C) (st_s1.ts C)) ∪
    st_s1.cs.crossEdges
  have hS_s1_E : st_s1.S_cur.E = targetE' := by rw [hS_E_s1, hactB_s1']
  set info := stepTreeCoreAux sparsify st_s (D.U (s + 1))
  have hcs1_eq : info.state.cs = st_s1.cs := by rw [← hst_step]
  have hts1_eq : info.state.ts = st_s1.ts := by rw [← hst_step]
  have hact1_eq : info.state.activeComps = st_s1.activeComps := by rw [← hst_step]
  have hdyn1_eq : info.state.dyn = st_s1.dyn := by rw [← hst_step]
  have hU_eq : info.U_S = buildUSReinsert st_s.cs (D.U (s + 1)) st_s1.cs st_s.S_cur targetE' info.D_total := by
    have hdyn_union :
        (st_s1.activeComps.biUnion fun C => (actB C).biUnion fun b => (st_s1.dyn (C, b)).H.E) =
          (info.state.activeComps.biUnion fun C =>
            (st_s.activeBuckets C).biUnion fun b => (info.stepOut (C, b)).state.H.E) := by
      rw [← hact1_eq, ← hactB_s']
      refine Finset.biUnion_congr rfl fun C hCA => Finset.biUnion_congr rfl fun b _ => ?_
      rw [(hDyn_step C (hAct_s1.2 (hact1_eq ▸ hCA)) b).2.1]
    have htarg_eq : targetE' =
        ((info.state.activeComps.biUnion fun C =>
            (st_s.activeBuckets C).biUnion fun b => (info.stepOut (C, b)).state.H.E) ∪
          (info.state.activeComps.biUnion fun C =>
            extraSet (info.state.cs.compSt C) (info.state.ts C)) ∪
          info.state.cs.crossEdges) := by
      dsimp only [targetE']
      rw [hdyn_union, ← hact1_eq, ← hcs1_eq, ← hts1_eq]
    rw [htarg_eq, ← hcs1_eq]
    rfl
  rw [hU_eq] at hNoIns
  have hkeep := mem_buildUSReinsert_insEdges st_s.cs (D.U (s + 1)) st_s1.cs st_s.S_cur
    targetE' info.D_total (hS_s1_E ▸ he'_cur) hNoIns
  rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_inter] at hkeep
  have he'_prev : e' ∈ st_s.S_cur.E := hkeep.1.1.1
  have he'_notDel : e' ∉ batchDeletes (D.U (s + 1)) := hkeep.1.2
  have he'_notD : e' ∉ info.D_total := hkeep.2
  refine ⟨he'_prev, he'_notDel, fun e heC1 hew1 => ?_⟩
  by_cases heS1 : e ∈ st_s1.S_cur.E
  · have hemb1 : st_s1.emb e = [(e, true)] := by
      dsimp only [TreeCoreState.emb]; simp only [heS1, ↓reduceIte]
    rw [hemb1] at hew1
    simp only [walkEdges, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_singleton] at hew1
    have he_eq : e = e' := hew1.symm
    subst he_eq
    have heC0 : e ∈ (coreGraph (D.G s) st_s.cs.lsf).E :=
      hG_s ▸ hS_sub_s.2.1 he'_prev
    have hemb0 : st_s.emb e = [(e, true)] := by
      dsimp only [TreeCoreState.emb]; simp only [he'_prev, ↓reduceIte]
    have hew0 : e ∈ walkEdges (st_s.emb e) := by
      rw [hemb0]; simp [walkEdges]
    have hwc_le : walkCount (st_s1.emb e) e ≤ walkCount (st_s.emb e) e := by
      rw [hemb1, hemb0]
    have heGs : e ∈ (D.G s).E := (Finset.mem_sdiff.mp heC0).1
    have hnoIns_e : ∀ u ∈ D.U (s + 1), ¬ u.Inserts e :=
      not_inserts_of_not_mem_batchDeletes (hcs_s ▸ (hStep s hs_lt).1) (hG_s ▸ heGs) he'_notDel
    exact ⟨heC0, hew0, hwc_le, hnoIns_e⟩
  · have hEx : ∃ C ∈ st_s1.activeComps, e ∈ (st_s1.ts C).C.E := by
      by_contra hnot
      have hew_nil : st_s1.emb e = [] := by
        dsimp only [TreeCoreState.emb]; simp only [heS1, ↓reduceIte, hnot, ↓reduceDIte]
      rw [hew_nil, walkEdges] at hew1
      simp at hew1
    let C := hEx.choose
    have hC_act1 : C ∈ st_s1.activeComps := hEx.choose_spec.1
    have heC_ts1 : e ∈ (st_s1.ts C).C.E := hEx.choose_spec.2
    have hC_comp : C ∈ components (D.G 0) := hAct_s1.2 hC_act1
    have hC_cs0 : C ∈ components cs₀.G₀ := hcs₀_G₀.symm ▸ hC_comp
    have he_ts0_mem : e ∈ (ts₀ C).C.E := (hC_props_s1 C hC_comp).2.2.1 heC_ts1
    have horig_e_eq : bucketOf (coreLen cs₀.lsf (safeLen (D.G 0) (D.ℓ 0)) e) = origB e :=
      horig_on_ts0 C hC_comp e he_ts0_mem
    have hemb1 : st_s1.emb e = piTotal (st_s1.dyn (C, origB e)) e := by
      dsimp only [TreeCoreState.emb]
      simp only [heS1, ↓reduceIte, hEx, ↓reduceDIte, horig_s1', horig_e_eq]
      rfl
    rw [hemb1] at hew1
    set b := origB e
    have hb_act : b ∈ actB C := Finset.mem_image_of_mem origB he_ts0_mem
    have heG1_b : e ∈ (st_s1.dyn (C, b)).G.E := by
      rw [(hDyn_G_s1 C hC_comp b).1, horig_s1']
      exact Finset.mem_filter.mpr ⟨heC_ts1, horig_e_eq⟩
    have hnotD_b : e' ∉ (info.stepOut (C, b)).D := by
      intro hmem
      apply he'_notD
      have hC_info : C ∈ info.state.activeComps := by rw [hact1_eq]; exact hC_act1
      dsimp only [info, stepTreeCoreAux]
      refine Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨C, hC_info,
        Finset.mem_biUnion.mpr ⟨b, hactB_s'.symm ▸ hb_act, hmem⟩⟩)
    have hDyn_cb := hDyn_step C hC_comp b
    have hew0_b : e' ∈ walkEdges (piTotal (st_s.dyn (C, b)) e) :=
      hDyn_cb.2.2.1 e heG1_b e' hew1 hnotD_b
    have he'H1 : e' ∈ (st_s1.dyn (C, b)).H.E :=
      isWalk_walkEdges_sub ((hDyn_G_s1 C hC_comp b).2.2.2 e heG1_b) hew1
    have he'G1_b : e' ∈ (st_s1.dyn (C, b)).G.E :=
      (hDyn_G_s1 C hC_comp b).2.1.2.1 he'H1
    have he'C_ts1 : e' ∈ (st_s1.ts C).C.E := by
      have hEq := (hDyn_G_s1 C hC_comp b).1
      rw [hEq, Finset.mem_filter] at he'G1_b
      exact he'G1_b.1
    have hUproj := compLSFBatch_compSt hI_s (hcs_s ▸ (hStep s hs_lt).1) (hG₀_s.symm ▸ hC_cs0)
    have hCE_sub_s : (st_s1.ts C).C.E ⊆ (st_s.ts C).C.E := by
      have hU_eq_proj : st_s1.ts C =
          (tildeStepBatch (st_s.cs.compSt C) (st_s.ts C)
            (projCompBatchG st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)))).2.1 := by
        rw [hst_step]; rfl
      have hsub := tildeStepBatch_CE_sub (hI₀.hCompLSF C (hcs₀_G₀ ▸ hC_comp)).1 (hCov₀ C hC_comp)
        (projCompBatchG st_s.cs.G (st_s.cs.compSt C).G (D.U (s + 1)))
        (hI_s.hCompLSF C (hG₀_s ▸ hC_comp)).1 (hC_props_s C hC_comp).1 hUproj.2.2.1
        (hC_props_s C hC_comp).2.1
      rwa [← hU_eq_proj] at hsub
    have he'C_ts0 : e' ∈ (st_s.ts C).C.E := hCE_sub_s he'C_ts1
    have heC_ts0 : e ∈ (st_s.ts C).C.E := hCE_sub_s heC_ts1
    have hC_act0 : C ∈ st_s.activeComps := by
      rw [hS_E_s, Finset.mem_union] at he'_prev
      rcases he'_prev with heB | heCr
      · rw [Finset.mem_union] at heB
        rcases heB with heDyn | heExt
        · rw [Finset.mem_biUnion] at heDyn
          rcases heDyn with ⟨C', hC'_act, hC'_b⟩
          rw [Finset.mem_biUnion] at hC'_b
          rcases hC'_b with ⟨b', _, he'H0⟩
          have hC'_comp := hAct_s.2 hC'_act
          have he'G0 : e' ∈ (st_s.cs.compSt C').G.E := by
            have h1 := (hDyn_G_s C' hC'_comp b').2.2.2.1 he'H0
            have h2 := (hDyn_G_s C' hC'_comp b').1.2.1 h1
            exact (Finset.mem_sdiff.mp ((hC_props_s C' hC'_comp).2.1.hCE_sub h2)).1
          have hEqC := mem_comp_eq_of_mem_ts_and_compG hI_s hG₀_s hC_cs0
            (hcs₀_G₀.symm ▸ hC'_comp) (hC_props_s C hC_comp).2.1 (hC_props_s C hC_comp).2.2.2 he'C_ts0 he'G0
          rwa [hEqC]
        · rw [Finset.mem_biUnion] at heExt
          rcases heExt with ⟨C', hC'_act, he'Ex⟩
          have hC'_comp := hAct_s.2 hC'_act
          have he'G0 : e' ∈ (st_s.cs.compSt C').G.E :=
            (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he'Ex).1).1
          have hEqC := mem_comp_eq_of_mem_ts_and_compG hI_s hG₀_s hC_cs0
            (hcs₀_G₀.symm ▸ hC'_comp) (hC_props_s C hC_comp).2.1 (hC_props_s C hC_comp).2.2.2 he'C_ts0 he'G0
          rwa [hEqC]
      · exfalso
        have he'G0 : e' ∈ (st_s.cs.compSt C).G.E :=
          (Finset.mem_sdiff.mp ((hC_props_s C hC_comp).2.1.hCE_sub he'C_ts0)).1
        have hnotIns : e' ∉ (st_s.cs.compSt C).insertedEdges :=
          Finset.disjoint_left.mp (hC_props_s C hC_comp).2.2.2 he'C_ts0
        exact hI_s.hNonIns_notCross C (hG₀_s ▸ hC_comp) e' he'G0 hnotIns heCr
    have heC0 : e ∈ (coreGraph (D.G s) st_s.cs.lsf).E := by
      rw [← hG_s, coreGraph, Finset.mem_sdiff]
      have heG0 : e ∈ (st_s.cs.compSt C).G.E :=
        (Finset.mem_sdiff.mp ((hC_props_s C hC_comp).2.1.hCE_sub heC_ts0)).1
      refine ⟨hI_s.hCE_sub C (hG₀_s ▸ hC_comp) heG0, ?_⟩
      intro heF
      change e ∈ (components st_s.cs.G₀).biUnion (fun C' => (st_s.cs.compSt C').RF.F.E) at heF
      rw [Finset.mem_biUnion] at heF
      rcases heF with ⟨C', hC', heFC'⟩
      have hC'_cs0 : C' ∈ components cs₀.G₀ := hG₀_s ▸ hC'
      have heG0' : e ∈ (st_s.cs.compSt C').G.E :=
        (lsfInv_to_RS (hI_s.hCompLSF C' hC').1).2.2.2.2.2.1 heFC'
      have hEqC := mem_comp_eq_of_mem_ts_and_compG hI_s hG₀_s hC_cs0
        hC'_cs0 (hC_props_s C hC_comp).2.1 (hC_props_s C hC_comp).2.2.2 heC_ts0 heG0'
      subst hEqC
      exact (Finset.mem_sdiff.mp ((hC_props_s C hC_comp).2.1.hCE_sub heC_ts0)).2 heFC'
    have he_not_S0 : e ∉ st_s.S_cur.E := by
      intro heS0
      rw [hS_E_s, Finset.mem_union] at heS0
      rcases heS0 with heB0 | heCr0
      · rw [Finset.mem_union] at heB0
        rcases heB0 with heDyn0 | heEx0
        · rw [Finset.mem_biUnion] at heDyn0
          rcases heDyn0 with ⟨C', hC'_act, hb'⟩
          rw [Finset.mem_biUnion] at hb'
          rcases hb' with ⟨b', _, heb'H⟩
          have hC'_comp := hAct_s.2 hC'_act
          have heb'G : e ∈ (st_s.dyn (C', b')).G.E :=
            (hDyn_G_s C' hC'_comp b').2.2.2.1 heb'H
          have heG_C' : e ∈ (st_s.cs.compSt C').G.E := by
            have h1 := (hDyn_G_s C' hC'_comp b').1.2.1 heb'G
            exact (Finset.mem_sdiff.mp ((hC_props_s C' hC'_comp).2.1.hCE_sub h1)).1
          have hEqC := mem_comp_eq_of_mem_ts_and_compG hI_s hG₀_s hC_cs0
            (hcs₀_G₀.symm ▸ hC'_comp) (hC_props_s C hC_comp).2.1 (hC_props_s C hC_comp).2.2.2 heC_ts0 heG_C'
          subst hEqC
          have hb'_eq : b' = b := by
            rw [(hDyn_G_s C hC_comp b').2.1, horig_s', Finset.mem_filter] at heb'G
            exact (heb'G.2.symm.trans horig_e_eq)
          subst hb'_eq
          have he_not_H1 : e ∉ (st_s1.dyn (C, b)).H.E := fun h =>
            heS1 (hS_s1_E ▸ Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_biUnion.mpr ⟨C, hC_act1, Finset.mem_biUnion.mpr ⟨b, hb_act, h⟩⟩)))
          have hstep_b : (info.stepOut (C, b)).state = st_s1.dyn (C, b) := hDyn_cb.2.1
          have hC_info : C ∈ info.state.activeComps := by rw [hact1_eq]; exact hC_act1
          apply he'_notD
          dsimp only [info, stepTreeCoreAux]
          refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨C, hC_info,
            Finset.mem_biUnion.mpr ⟨b, hactB_s'.symm ▸ hb_act,
              Finset.mem_biUnion.mpr ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨heb'H, ?_⟩, ?_⟩, ?_⟩⟩⟩)
          · change e ∈ (info.stepOut (C, b)).state.G.E; rw [hstep_b]; exact heG1_b
          · change e ∉ (info.stepOut (C, b)).state.H.E; rw [hstep_b]; exact he_not_H1
          · change e' ∈ walkEdges (piTotal (info.stepOut (C, b)).state e); rw [hstep_b]; exact hew1
        · rw [Finset.mem_biUnion] at heEx0
          rcases heEx0 with ⟨C', hC'_act, heEx0'⟩
          have hC'_comp := hAct_s.2 hC'_act
          have heG_C' : e ∈ (st_s.cs.compSt C').G.E :=
            (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp heEx0').1).1
          have hEqC := mem_comp_eq_of_mem_ts_and_compG hI_s hG₀_s hC_cs0
            (hcs₀_G₀.symm ▸ hC'_comp) (hC_props_s C hC_comp).2.1 (hC_props_s C hC_comp).2.2.2 heC_ts0 heG_C'
          subst hEqC
          exact (Finset.mem_sdiff.mp heEx0').2 heC_ts0
      · have heG0 : e ∈ (st_s.cs.compSt C).G.E :=
          (Finset.mem_sdiff.mp ((hC_props_s C hC_comp).2.1.hCE_sub heC_ts0)).1
        have hnotIns : e ∉ (st_s.cs.compSt C).insertedEdges :=
          Finset.disjoint_left.mp (hC_props_s C hC_comp).2.2.2 heC_ts0
        exact hI_s.hNonIns_notCross C (hG₀_s ▸ hC_comp) e heG0 hnotIns heCr0
    have hEx0 : ∃ C₀ ∈ st_s.activeComps, e ∈ (st_s.ts C₀).C.E := ⟨C, hC_act0, heC_ts0⟩
    have hCh_eq : hEx0.choose = C := by
      have hC0_comp := hAct_s.2 hEx0.choose_spec.1
      have heG0' : e ∈ (st_s.cs.compSt hEx0.choose).G.E :=
        (Finset.mem_sdiff.mp ((hC_props_s hEx0.choose hC0_comp).2.1.hCE_sub hEx0.choose_spec.2)).1
      exact (mem_comp_eq_of_mem_ts_and_compG hI_s hG₀_s hC_cs0
        (hcs₀_G₀.symm ▸ hC0_comp) (hC_props_s C hC_comp).2.1 (hC_props_s C hC_comp).2.2.2 heC_ts0 heG0').symm
    have hemb0 : st_s.emb e = piTotal (st_s.dyn (C, origB e)) e := by
      dsimp only [TreeCoreState.emb]
      simp only [he_not_S0, ↓reduceIte, hEx0, ↓reduceDIte, hCh_eq, horig_s', horig_e_eq]
      rfl
    have hew0 : e' ∈ walkEdges (st_s.emb e) := hemb0 ▸ hew0_b
    have hwc_le : walkCount (st_s1.emb e) e' ≤ walkCount (st_s.emb e) e' := by
      have hcnt := hDyn_cb.2.2.2 e heG1_b e' hnotD_b
      rw [← hemb1, ← hemb0] at hcnt
      exact hcnt
    have hnoIns_e : ∀ u ∈ D.U (s + 1), ¬ u.Inserts e := by
      intro u hu hins
      have he_app : e ∈ ((D.G s).applyBatch (D.U (s + 1))).E := by
        have hdv := (hD (s + 1) (Nat.succ_pos s) hs1_le).2
        simp only [Nat.add_sub_cancel] at hdv
        rw [← hdv, ← hG_s1]
        exact hI_s1.hCE_sub C (hG₀_s1 ▸ hC_comp)
          (Finset.mem_sdiff.mp ((hC_props_s1 C hC_comp).2.1.hCE_sub heC_ts1)).1
      have heG1_C : e ∈ (st_s1.cs.compSt C).G.E :=
        (Finset.mem_sdiff.mp ((hC_props_s1 C hC_comp).2.1.hCE_sub heC_ts1)).1
      have hins_edge : e ∈ batchesInserted (dynBatches D (s + 1)) := by
        rw [dynBatches_succ, batchesInserted, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact mem_foldl_updateInserted_of_mem_applyBatch_inserts he_app hu hins
      have hins_glob : e ∈ st_s1.cs.insertedGlobal := by
        rw [hcs_seq_s1, compLSFBatch_insertedGlobal, foldl_updateInserted_flatten]
        exact hins_edge
      exact Finset.disjoint_left.mp (hC_props_s1 C hC_comp).2.2.2 heC_ts1
        (hI_s1.hCE_ins C (hG₀_s1 ▸ hC_comp) e heG1_C hins_glob)
    exact ⟨heC0, hew0, hwc_le, hnoIns_e⟩

private lemma weakHidden_step_backward
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (j : ℕ) (hj : j < k) {s : ℕ} (hs_lt : s < τ)
    {e' : ℕ}
    (he'_cur : e' ∈ (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.S_cur.E)
    (hNoIns : ∀ u ∈ (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).2, ¬ u.Inserts e') :
    let st_s := (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
    let st_s1 := (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1
    e' ∈ st_s.S_cur.E ∧
    e' ∉ batchDeletes (D.U (s + 1)) ∧
    ∀ e ∈ (coreGraph (D.G (s + 1)) st_s1.cs.lsf).E, e' ∈ walkEdges (st_s1.emb e) →
      e ∈ (coreGraph (D.G s) st_s.cs.lsf).E ∧
      e' ∈ walkEdges (st_s.emb e) ∧
      walkCount (st_s1.emb e) e' ≤ walkCount (st_s.emb e) e' ∧
      (∀ u ∈ D.U (s + 1), ¬ u.Inserts e) := by
  intro st_s st_s1
  obtain ⟨hBase, _, hFlat⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  obtain ⟨_, hStage_all, hStep_full, _⟩ := treeRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  have hs_le : s ≤ τ := Nat.le_of_lt hs_lt
  have hs1_le : s + 1 ≤ τ := hs_lt
  have hS_s := hStage_all s hs_le
  have hS_s1 := hStage_all (s + 1) hs1_le
  have hSt_s1 := hStep_full (s + 1) (Nat.succ_pos s) hs1_le
  simp only [Nat.add_sub_cancel] at hSt_s1
  have hS_E_fn : ∀ r (hr : r ≤ τ),
      (treeRunSeq oracle C_lsst L sparsify k M N D j r).1.S_cur.E =
        ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.activeComps.biUnion fun C =>
          ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.activeBuckets C).biUnion fun b =>
            ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.dyn (C, b)).H.E) ∪
          ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.activeComps.biUnion fun C =>
            extraSet ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.cs.compSt C)
              ((treeRunSeq oracle C_lsst L sparsify k M N D j r).1.ts C)) ∪
          (treeRunSeq oracle C_lsst L sparsify k M N D j r).1.cs.crossEdges := by
    intro r hr
    have hb_actB := (hBase r hr).2.2.2.2.2.1
    simpa [hb_actB] using (hStage_all r hr).2.2.1
  have hm0 : st_s.m₀ = M := (hBase s hs_le).1
  refine weakHidden_step_backward_core oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD
    hN hThresh j hs_lt st_s st_s1 rfl hm0 rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hS_s.2.2.2.1 (hS_E_fn s hs_le) (hS_E_fn (s + 1) hs1_le)
    (fun C hC b => ⟨((hBase s hs_le).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.2.2 b |>.2.1,
      (((hBase s hs_le).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.2.2 b).2.2.1.trans
        (Finset.filter_congr fun x hx => by
          have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
          have hT0 := initTildeState_inv (hI₀.hCompLSF C hC).1 (initCompLSF_RF_cov hLSST hk hG₀ hℓ₀ j hC).2
          have hxG₀ : x ∈ (D.G 0).E :=
            (Finset.mem_sdiff.mp (compLSF_comp_sdiff_sub hI₀ hC
              (hT0.hCE_sub (((hBase s hs_le).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.1 hx)))).1
          rw [show st_s.origBucket x = _ from congrFun (hBase s hs_le).2.2.2.2.1 x]
          simp [coreLen, safeLen, hxG₀]),
      (hS_s.2.2.2.2.2.2.2 C hC b).1⟩)
    (fun C hC b => ⟨(((hBase (s + 1) hs1_le).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.2.2 b).2.2.1.trans
        (Finset.filter_congr fun x hx => by
          have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
          have hT0 := initTildeState_inv (hI₀.hCompLSF C hC).1 (initCompLSF_RF_cov hLSST hk hG₀ hℓ₀ j hC).2
          have hxG₀ : x ∈ (D.G 0).E :=
            (Finset.mem_sdiff.mp (compLSF_comp_sdiff_sub hI₀ hC
              (hT0.hCE_sub (((hBase (s + 1) hs1_le).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.1 hx)))).1
          rw [show st_s1.origBucket x = _ from congrFun (hBase (s + 1) hs1_le).2.2.2.2.1 x]
          simp [coreLen, safeLen, hxG₀]),
      (hS_s1.2.2.2.2.2.2.2 C hC b).1, (hS_s1.2.2.2.2.2.2.2 C hC b).2.2.2.1⟩)
    (fun C hC b => by
      have hSt_cb := hSt_s1.2.2.2.1 C hC b
      refine ⟨by simpa [hm0] using hSt_cb.1, hSt_cb.2.1, hSt_cb.2.2.2.2.2,
        fun eG heG1_b e' hnotD_b => ?_⟩
      set cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      set Hb₀ := initBucketGraph (cs₀.compSt C) (D.ℓ 0) b
      set splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
        ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
      set Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
      set q_b := phaseBase (Hb₀.n + splitB) L
      have hS₀C_spec := initCompLSF_RF_cov hLSST hk hG₀ hℓ₀ j hC
      have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
      have hHb := initBucketGraph_spec (hI₀.hCompLSF C hC).1 hS₀C_spec.2 b
      have hHb_val : Hb₀.IsValid := hHb.1
      have hHb_m : Hb₀.m ≤ M := le_trans (le_trans hHb.2.2.2.2.2.2.2.1
        (by rw [hS₀C_spec.1]; exact compGraph_m_le)) hM
      have hq1 : 1 ≤ q_b := le_trans (by omega) (two_le_phaseBase (Hb₀.n + splitB) L)
      have hfb := hFlat C hC b
      have hUs_len : Us_b.length = τ := by simp [Us_b, bucketBatchList]
      have hget : Us_b[s]? = some ((stepTreeCoreAux sparsify st_s (D.U (s + 1))).U_b (C, b)) :=
        bucketBatchList_getElem? oracle C_lsst L sparsify k M N τ D j C b hs_lt
      have hdyn_s : runBatchState Hb₀ q_b (sparsify M) Us_b s = st_s.dyn (C, b) :=
        (((hBase s hs_le).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.2.2 b).2.2.2.symm
      have hres_eq : runBatchStepOut Hb₀ q_b (sparsify M) Us_b s =
          (stepTreeCoreAux sparsify st_s (D.U (s + 1))).stepOut (C, b) := by
        dsimp only [DynSpanner.runBatchStepOut]
        rw [hget, hdyn_s]
        simpa [hm0] using hSt_cb.1.symm
      have hbt := DynSpanner.batchTrace_walkCount_le
        hHb_val hL hq1 hHb_m hSp hfb.1 hfb.2.1 s (hUs_len.symm ▸ hs_lt)
        ((stepTreeCoreAux sparsify st_s (D.U (s + 1))).U_b (C, b)) hget
      dsimp only at hbt
      rw [hres_eq, hdyn_s, hSt_cb.2.1] at hbt
      exact Nat.cast_le (α := ℝ).mpr (hbt eG heG1_b e' hnotD_b))
    he'_cur hNoIns


end

end MinCostFlow.SparseCore
