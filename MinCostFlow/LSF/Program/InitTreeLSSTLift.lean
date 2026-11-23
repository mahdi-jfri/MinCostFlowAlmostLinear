module

public import MinCostFlow.LSF.Program.InitTreeLSSTLiftBase
public import MinCostFlow.LSF.Program.InitTreeLSSTOps
import MinCostFlow.LSF.Program.Layout
import MinCostFlow.LSF.Theorem22Aux
import MinCostFlow.LSF.ModelWith
import Mathlib.Tactic

/-!
# Pure graph isomorphism and LSST tree lifting (`InitTreeLSSTLift`)

Connects the Word-RAM `[AN19]` tree output `decodedTree` on the weighted-copy multigraph
`copyIndexedGraph` to a valid spanning tree `T_raw` and projection `T₀ = projectTree G₀ v T_raw`
for `MinCostFlow.LSF.ValidLSFParams`, handling both `m0 = 0` and `1 ≤ m0` uniformly:

* `copyList`, `copyIndexedGraph`: flat explicit enumeration of copies `(e, k)` of edges in `G₀`.
* `zeroPositions` and `zeroPositions_card_ge`: non-colliding bridge slot extraction from the
  collision bitset `[usedBridgePtr, usedBridgePtr + 2 * m0 + n0)`.
* `isLSST_of_iso`: invariance of `MinCostFlow.LSF.IsLSST` under vertex and edge bijections.
* `lsst_decode_lift`: constructs `T_raw` and characterizes `T₀ = projectTree G₀ v T_raw` from
  `LSSTPost`.
* Monotonicity of `lsstLSimMin`, `lsstSpace`, and `lsstCost` in the copy count `M_copies ≤ 2 * m0`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM
open MinCostFlow
open MinCostFlow.WideWord
open MinCostFlow.LSF

@[expose] public section

/-! ## Lifting `LSSTPost` output to `T_raw` and `T₀` -/

private lemma nodup_of_toFinset_card_eq {α : Type*} [DecidableEq α] :
    ∀ {l : List α}, l.toFinset.card = l.length → l.Nodup
  | [], _ => .nil
  | x :: xs, hc => by
    by_cases hx : x ∈ xs
    · have h1 : (x :: xs).toFinset = xs.toFinset := by
        ext y; simp [hx, eq_comm]
      have := List.toFinset_card_le xs
      simp only [h1, List.length_cons] at hc
      omega
    · have h1 : (x :: xs).toFinset = insert x xs.toFinset := List.toFinset_cons
      rw [h1, Finset.card_insert_of_notMem (by simp [hx]), List.length_cons] at hc
      exact List.nodup_cons.mpr ⟨hx, nodup_of_toFinset_card_eq (by omega)⟩

private lemma idxOf_getElem_lt {α : Type*} [DecidableEq α] {xs : List α} (hnd : xs.Nodup)
    {i : ℕ} (hi : i < xs.length) : xs.idxOf (xs[i]'hi) = i :=
  (List.Nodup.getElem_inj hnd).mp
    (List.getElem_idxOf (List.idxOf_lt_length_of_mem (List.getElem_mem hi)))

/-- Lifts the Word-RAM `lsstFrontierProc` output `LSSTPost` and `initMarkBridges` collision table
into a concrete `T_raw` (valid for `ValidLSFParams` in both `m0 = 0` and `1 ≤ m0`) and explicit
endpoint characterization of `T₀ := projectTree G₀ v T_raw`. -/
theorem lsst_decode_lift {K_AN : ℝ} {G₀ : MGraph} {ℓ₀ v : ℕ → ℝ} {P_fp : ℕ}
    {vList eList : List ℕ} {mult : ℕ → ℕ}
    {outOrigPtr outBridgePtr outHdrPtr lsstHeap usedBridgePtr eCap : ℕ}
    {mem₀ mem₁ : ℕ → ℕ}
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hv : ∀ e ∈ G₀.E, 0 < v e)
    (hvLen : vList.length = G₀.n) (hvNd : vList.Nodup) (hvMem : ∀ u, u ∈ vList ↔ u ∈ G₀.V)
    (heLen : eList.length = G₀.E.card) (heNd : eList.Nodup) (heMem : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (hmult : ∀ j < G₀.E.card, mult j = edgeMult G₀ v (eList.getD j 0))
    (heCap : ∀ e ∈ G₀.E, e < eCap)
    (hlsst : LSSTPost K_AN (copyIndexedGraph G₀ vList eList mult)
      (fun _ => (2 : ℝ)⁻¹ ^ P_fp)
      (fun q => ℓ₀ ((copyList eList mult G₀.E.card).getD q (0, 0)).1)
      outOrigPtr outBridgePtr outHdrPtr lsstHeap mem₀ (.returned 0) mem₁)
    (hmark : ∀ z < 2 * G₀.E.card + G₀.n,
      (mem₁ (usedBridgePtr + z) = 1 ↔
        ∃ j' < G₀.E.card, ∃ k < mult j', eList.getD j' 0 + copyMod G₀ * (k + 1) = eCap + z) ∧
      (mem₁ (usedBridgePtr + z) = 0 ∨ mem₁ (usedBridgePtr + z) = 1)) :
    let G_idx := copyIndexedGraph G₀ vList eList mult
    let cl := copyList eList mult G₀.E.card
    let zeros := zeroPositions mem₁ usedBridgePtr (2 * G₀.E.card + G₀.n)
    ∃ (origEdges : List ℕ) (bridgePairs : List (ℕ × ℕ)),
      mem₁ outHdrPtr = origEdges.length ∧
      mem₁ (outHdrPtr + 1) = bridgePairs.length ∧
      origEdges.length ≤ G₀.n ∧
      bridgePairs.length ≤ G₀.n ∧
      origEdges.Nodup ∧
      origEdges.length + bridgePairs.length = G₀.n - 1 ∧
      (∀ q ∈ origEdges, q < cl.length) ∧
      (∀ i₁ (hi₁ : i₁ < origEdges.length) i₂ (hi₂ : i₂ < origEdges.length),
        (cl.getD (origEdges[i₁]'hi₁) (0, 0)).1 = (cl.getD (origEdges[i₂]'hi₂) (0, 0)).1 → i₁ = i₂) ∧
      (∀ q ∈ origEdges, let e := (cl.getD q (0, 0)).1; e ∈ G₀.E ∧ G₀.tail e ≠ G₀.head e) ∧
      (∀ p ∈ bridgePairs, p.1 < G₀.n ∧ p.2 < G₀.n) ∧
      bridgePairs.length ≤ zeros.length ∧
      ListAt mem₁ outOrigPtr origEdges ∧
      ListAt mem₁ outBridgePtr (bridgePairs.flatMap fun p => [p.1, p.2]) ∧
      ∃ T_raw : MGraph,
        IsLSST (if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
          (if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1)
          (fun _ => 1)
          ((4 * max K_AN 1 + 5) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw ∧
        let T₀ := projectTree G₀ v T_raw
        let origIds := origEdges.map fun q => (cl.getD q (0, 0)).1
        let brIds := (zeros.take bridgePairs.length).map fun z => eCap + z
        T₀.V = G₀.V ∧
        T₀.E = (origIds ++ brIds).toFinset ∧
        (∀ i (hi : i < origIds.length),
          T₀.tail (origIds[i]'hi) = G₀.tail (origIds[i]'hi) ∧
          T₀.head (origIds[i]'hi) = G₀.head (origIds[i]'hi)) ∧
        (∀ k (hk : k < brIds.length),
          T₀.tail (brIds[k]'hk) = vList.getD ((bridgePairs.getD k (0, 0)).1) 0 ∧
          T₀.head (brIds[k]'hk) = vList.getD ((bridgePairs.getD k (0, 0)).2) 0) := by
  intro G_idx cl zeros
  rcases hlsst with ⟨origEdges, bridgePairs, _, hhdr0, hhdr1, ho_le, hb_le, ho_lt, hsum_le,
    ho_at, hb_at, hdec_lsst, _⟩
  let T_dec := decodedTree G_idx.n G_idx.m G_idx.tail G_idx.head origEdges bridgePairs
  have hcl_len : cl.length = G_idx.m := rfl
  have hn1 : 1 ≤ G₀.n := Finset.card_pos.mpr hV₀
  have hT_dec_st : T_dec.IsSpanningTreeOn (Finset.range G₀.n) := hdec_lsst.1
  have hT_dec_V : T_dec.V = Finset.range G₀.n := hT_dec_st.2.1
  have hV_ge_card : G₀.n ≤ T_dec.E.card + 1 := by
    have hV_ne : T_dec.V.Nonempty := by rw [hT_dec_V]; exact ⟨0, Finset.mem_range.mpr hn1⟩
    have hc := connected_card_ge T_dec.E.card T_dec le_rfl hT_dec_st.1.1 hV_ne
      fun u hu v hv => hT_dec_st.2.2 u (hT_dec_V ▸ hu) v (hT_dec_V ▸ hv)
    simpa [MGraph.n, hT_dec_V, Finset.card_range] using hc
  have hbr_part : ((List.range bridgePairs.length).toFinset.image (fun k => G_idx.m + k)).card =
      bridgePairs.length := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega),
      List.toFinset_card_of_nodup List.nodup_range, List.length_range]
  have hT_dec_card_le : T_dec.E.card ≤ origEdges.toFinset.card + bridgePairs.length := by
    dsimp only [T_dec, decodedTree]
    calc (origEdges.toFinset ∪ (List.range bridgePairs.length).toFinset.image (fun k => G_idx.m + k)).card
        ≤ origEdges.toFinset.card +
            ((List.range bridgePairs.length).toFinset.image (fun k => G_idx.m + k)).card :=
          Finset.card_union_le _ _
      _ = origEdges.toFinset.card + bridgePairs.length := by rw [hbr_part]
  have hsum_le' : origEdges.length + bridgePairs.length ≤ G₀.n - 1 := hsum_le
  have hlen_sum_eq : origEdges.length + bridgePairs.length = G₀.n - 1 := by
    have := List.toFinset_card_le origEdges
    omega
  have ho_card_eq : origEdges.toFinset.card = origEdges.length := by
    have := List.toFinset_card_le origEdges
    omega
  have ho_nd : origEdges.Nodup := nodup_of_toFinset_card_eq ho_card_eq
  have ho_cl : ∀ q ∈ origEdges, q < cl.length := ho_lt
  have hbr_valid : ∀ p ∈ bridgePairs, p.1 < G₀.n ∧ p.2 < G₀.n := by
    intro p hp
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hp
    have hfk : G_idx.m + k ∈ T_dec.E := by
      dsimp only [T_dec, decodedTree]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (List.mem_toFinset.mpr (List.mem_range.mpr hk)))
    have hv := hT_dec_st.1.1 _ hfk
    rw [hT_dec_V, Finset.mem_range, Finset.mem_range] at hv
    have ht_eq : T_dec.tail (G_idx.m + k) = p.1 := by
      dsimp only [T_dec, decodedTree]
      rw [ite_eq_right (by omega : ¬ G_idx.m + k < G_idx.m), Nat.add_sub_cancel_left,
        List.getD_eq_getElem _ _ hk, hget]
    have hh_eq : T_dec.head (G_idx.m + k) = p.2 := by
      dsimp only [T_dec, decodedTree]
      rw [ite_eq_right (by omega : ¬ G_idx.m + k < G_idx.m), Nat.add_sub_cancel_left,
        List.getD_eq_getElem _ _ hk, hget]
    rwa [ht_eq, hh_eq] at hv
  have hsum_mult : (List.map mult (List.range G₀.E.card)).sum ≤ 2 * G₀.E.card :=
    edgeMult_sum_le_two_mul hv heLen heNd heMem hmult
  have hzeros_ge : G₀.n ≤ zeros.length :=
    zeroPositions_card_ge hsum_mult hmark
  have hbr_le_zeros : bridgePairs.length ≤ zeros.length := by omega
  have horig_e_mem : ∀ q ∈ origEdges, (cl.getD q (0, 0)).1 ∈ G₀.E := by
    intro q hq
    have hq_lt := ho_cl q hq
    obtain ⟨j, hj, _, _, _, hgq⟩ := exists_coords_of_lt_copyList eList mult hq_lt
    rw [List.getD_eq_getElem _ _ hq_lt, hgq, List.getD_eq_getElem _ _ (by omega)]
    exact (heMem _).mp (List.getElem_mem _)
  have hno_loop : ∀ q ∈ origEdges, G₀.tail (cl.getD q (0, 0)).1 ≠ G₀.head (cl.getD q (0, 0)).1 := by
    intro q hq hEq
    have hq_lt : q < G_idx.m := ho_cl q hq
    have hq_T : q ∈ T_dec.E := Finset.mem_union_left _ (List.mem_toFinset.mpr hq)
    have hth : T_dec.tail q = T_dec.head q := by
      dsimp only [T_dec, decodedTree]
      rw [ite_eq_left hq_lt, ite_eq_left hq_lt]
      dsimp only [G_idx, copyIndexedGraph]
      rw [hEq]
    have hW : T_dec.IsWalk (T_dec.head q) (T_dec.head q) [(q, true)] :=
      .cons hq_T (by simp [MGraph.src, hth])
        (by simpa [MGraph.dst] using MGraph.IsWalk.nil (T_dec.head q))
    exact hT_dec_st.1.2 [(q, true)] ⟨by simp, by simp, T_dec.head q, hW⟩
  have hno_par : ∀ i₁ (hi₁ : i₁ < origEdges.length) i₂ (hi₂ : i₂ < origEdges.length),
      (cl.getD (origEdges[i₁]'hi₁) (0, 0)).1 =
        (cl.getD (origEdges[i₂]'hi₂) (0, 0)).1 → i₁ = i₂ := by
    intro i₁ hi₁ i₂ hi₂ hEq
    by_contra hne
    let q₁ := origEdges[i₁]'hi₁
    let q₂ := origEdges[i₂]'hi₂
    have hq₁_ne : q₁ ≠ q₂ := fun h => hne ((ho_nd.getElem_inj_iff).mp h)
    have hq₁_lt : q₁ < G_idx.m := ho_cl q₁ (List.getElem_mem hi₁)
    have hq₂_lt : q₂ < G_idx.m := ho_cl q₂ (List.getElem_mem hi₂)
    have hq₁_T : q₁ ∈ T_dec.E := Finset.mem_union_left _ (List.mem_toFinset.mpr (List.getElem_mem hi₁))
    have hq₂_T : q₂ ∈ T_dec.E := Finset.mem_union_left _ (List.mem_toFinset.mpr (List.getElem_mem hi₂))
    have ht_eq : T_dec.tail q₁ = T_dec.tail q₂ := by
      dsimp only [T_dec, decodedTree]
      rw [ite_eq_left hq₁_lt, ite_eq_left hq₂_lt]
      dsimp only [G_idx, copyIndexedGraph]
      rw [hEq]
    have hh_eq : T_dec.head q₁ = T_dec.head q₂ := by
      dsimp only [T_dec, decodedTree]
      rw [ite_eq_left hq₁_lt, ite_eq_left hq₂_lt]
      dsimp only [G_idx, copyIndexedGraph]
      rw [hEq]
    have hW : T_dec.IsWalk (T_dec.tail q₁) (T_dec.tail q₁) [(q₁, true), (q₂, false)] :=
      .cons hq₁_T (by simp [MGraph.src])
        (.cons hq₂_T (by simp [MGraph.src, MGraph.dst, hh_eq])
          (by simpa [MGraph.dst, ht_eq] using MGraph.IsWalk.nil (T_dec.tail q₁)))
    exact hT_dec_st.1.2 [(q₁, true), (q₂, false)] ⟨by simp, by simp [hq₁_ne], T_dec.tail q₁, hW⟩
  -- Unscale `v_copy ≡ 2 ^ (-P_fp)` in `hdec_lsst` to uniform weight `1`
  have hdec_unit : IsLSST G_idx.toMGraph
      (fun q => ℓ₀ ((cl.getD q (0, 0)).1)) (fun _ => 1)
      ((4 * max K_AN 1 + 5) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_dec := by
    have hc_pos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ P_fp := by positivity
    refine isLSST_smul_weights (G := G_idx.toMGraph) (T := T_dec)
      (ℓ := fun q => ℓ₀ (cl.getD q (0, 0)).1) (v := fun _ => 1) (c := (2 : ℝ)⁻¹ ^ P_fp)
      hc_pos ?_
    have hmul1 : (fun _ : ℕ => ((2 : ℝ)⁻¹ ^ P_fp) * 1) = fun _ => (2 : ℝ)⁻¹ ^ P_fp := by
      funext _; ring
    rw [hmul1]
    exact hdec_lsst
  -- Construct `T_raw` uniformly, splitting into `m0 = 0` (`G₀.E = ∅`) and `1 ≤ m0` (`G₀.E.Nonempty`)
  let origIds := origEdges.map fun q => (cl.getD q (0, 0)).1
  let zPrefix := zeros.take bridgePairs.length
  have hzPrefix_len : zPrefix.length = bridgePairs.length := List.length_take_of_le hbr_le_zeros
  have hzPrefix_nd : zPrefix.Nodup := (zeroPositions_nodup _ _ _).take
  let brIds := zPrefix.map fun z => eCap + z
  have hbrIds_len : brIds.length = bridgePairs.length := by simp [brIds, hzPrefix_len]
  have hG_idx_val : G_idx.Valid := copyIndexedGraph_valid hG₀ hV₀ hvLen hvMem heLen heMem
  have hG_idx_Mval : G_idx.toMGraph.IsValid := IndexedGraph.toMGraph_isValid hG_idx_val
  have hv_bij_mem : ∀ i ∈ G_idx.toMGraph.V, vList.getD i 0 ∈ G₀.V ∧
      vList.idxOf (vList.getD i 0) = i := by
    intro i hi
    simp only [IndexedGraph.toMGraph, Finset.mem_range, G_idx, copyIndexedGraph] at hi
    have hi_len : i < vList.length := by omega
    rw [List.getD_eq_getElem _ _ hi_len]
    exact ⟨(hvMem _).mp (List.getElem_mem hi_len), idxOf_getElem_lt hvNd hi_len⟩
  have hv_bij_inv : ∀ u ∈ G₀.V, vList.idxOf u ∈ G_idx.toMGraph.V ∧
      vList.getD (vList.idxOf u) 0 = u := by
    intro u hu
    have huL : u ∈ vList := (hvMem u).mpr hu
    have hi_len : vList.idxOf u < vList.length := List.idxOf_lt_length_of_mem huL
    refine ⟨?_, ?_⟩
    · simp only [IndexedGraph.toMGraph, Finset.mem_range, G_idx, copyIndexedGraph]; omega
    · rw [List.getD_eq_getElem _ _ hi_len, List.getElem_idxOf hi_len]
  refine ⟨origEdges, bridgePairs, hhdr0, hhdr1, ho_le, hb_le, ho_nd, hlen_sum_eq, ho_cl, hno_par,
    fun q hq => ⟨horig_e_mem q hq, hno_loop q hq⟩, hbr_valid, hbr_le_zeros, ho_at, hb_at, ?_⟩
  by_cases hE_ne : G₀.E.Nonempty
  · -- Non-empty graph case (`1 ≤ m0`): map `q ∈ origEdges` to `copyId (copyMod G₀) e k ∈ G_v.E`,
    -- and bridge `k` to `(eCap + zeros[k]) - copyMod G₀ ∉ G_v.E`.
    have hmPos : 0 < G₀.E.card := Finset.card_pos.mpr hE_ne
    have hcm_le : copyMod G₀ ≤ eCap := by
      have hePos : 0 < eCap := by
        obtain ⟨e₀, he₀⟩ := hE_ne
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) (heCap e₀ he₀)
      exact Nat.succ_le_of_lt ((Finset.sup_lt_iff hePos).mpr heCap)
    let G_v := weightedCopyGraph G₀ v
    let ℓ_v := weightedCopyLen G₀ ℓ₀
    let M := copyMod G₀
    let σE : ℕ → ℕ := fun f =>
      if f < G_idx.m then
        let pk := cl.getD f (0, 0)
        copyId M pk.1 pk.2
      else
        (eCap + zPrefix.getD (f - G_idx.m) 0) - M
    let σE_inv : ℕ → ℕ := fun f' =>
      if f' ∈ G_v.E then
        let e := origEdge M f'
        (List.map mult (List.range (eList.idxOf e))).sum + f' / M
      else
        G_idx.m + zPrefix.idxOf (f' + M - eCap)
    have hzPrefix_nGv : ∀ z ∈ zPrefix, eCap + z - M ∉ G_v.E := by
      intro z hz hmem_gv
      have hz0 : z ∈ zeros := List.mem_of_mem_take hz
      rw [mem_zeroPositions_iff] at hz0
      rw [mem_weightedCopyGraph_E_iff hE_ne] at hmem_gv
      obtain ⟨e, heG, k, hk_lt, heq⟩ := hmem_gv
      have heL := (heMem e).mpr heG
      let j := eList.idxOf e
      have hj_lt : j < G₀.E.card := by rw [← heLen]; exact List.idxOf_lt_length_of_mem heL
      have hj_eq : eList.getD j 0 = e := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_idxOf (by omega)
      have hk_mult : k < mult j := by rw [hmult j hj_lt, hj_eq]; exact hk_lt
      have heq' : e + M * (k + 1) = eCap + z := by
        have hsum_eq : copyId M e k = eCap + z - M := heq
        dsimp only [copyId] at hsum_eq
        have hle_sum : M ≤ eCap + z := hcm_le.trans (Nat.le_add_right _ _)
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have h1 : mem₁ (usedBridgePtr + z) = 1 :=
        (hmark z hz0.1).1.mpr ⟨j, hj_lt, k, hk_mult, by rw [hj_eq]; exact heq'⟩
      omega
    have hσE_G : ∀ q ∈ G_idx.toMGraph.E, σE q ∈ G_v.E ∧ σE_inv (σE q) = q ∧
        G_v.tail (σE q) = vList.getD (G_idx.toMGraph.tail q) 0 ∧
        G_v.head (σE q) = vList.getD (G_idx.toMGraph.head q) 0 ∧
        ℓ_v (σE q) = ℓ₀ (cl.getD q (0, 0)).1 ∧ (1 : ℝ) = (1 : ℝ) := by
      intro q hq
      have hq_lt : q < G_idx.m := by simpa [G_idx, IndexedGraph.toMGraph] using hq
      obtain ⟨j, hj, k, hk, hq_eq, hget_q⟩ := exists_coords_of_lt_copyList eList mult hq_lt
      have hpk : cl.getD q (0, 0) = (eList.getD j 0, k) := by
        rw [List.getD_eq_getElem _ _ hq_lt, hget_q]
      have he_eq : eList.getD j 0 = eList[j]'(by omega) := List.getD_eq_getElem _ _ (by omega)
      have heG : eList[j]'(by omega) ∈ G₀.E := (heMem _).mp (List.getElem_mem _)
      have hk_em : k < edgeMult G₀ v (eList[j]'(by omega)) := by
        have := hmult j hj; rw [he_eq] at this; omega
      have hσ_eq : σE q = copyId M (eList[j]'(by omega)) k := by
        dsimp only [σE]; rw [ite_eq_left hq_lt, hpk, he_eq]
      have hmem_gv : σE q ∈ G_v.E := by
        rw [hσ_eq]; exact (mem_weightedCopyGraph_E_iff hE_ne).mpr ⟨_, heG, k, hk_em, rfl⟩
      have hdiv : copyId M (eList[j]'(by omega)) k / M = k := by
        dsimp only [copyId]
        rw [Nat.add_mul_div_left _ _ (copyMod_pos G₀), Nat.div_eq_of_lt (lt_copyMod heG), zero_add]
      have hinv : σE_inv (σE q) = q := by
        dsimp only [σE_inv]
        rw [ite_eq_left hmem_gv, hσ_eq, origEdge_copyId heG, idxOf_getElem_lt heNd (by omega), hdiv]
        exact hq_eq.symm
      have htail : G_v.tail (σE q) = vList.getD (G_idx.toMGraph.tail q) 0 := by
        rw [hσ_eq]
        dsimp only [G_v, G_idx, IndexedGraph.toMGraph, copyIndexedGraph]
        rw [weightedCopyGraph_tail_copyId hE_ne heG, hpk, he_eq,
          (hv_bij_inv _ (hG₀ _ heG).1).2]
      have hhead : G_v.head (σE q) = vList.getD (G_idx.toMGraph.head q) 0 := by
        rw [hσ_eq]
        dsimp only [G_v, G_idx, IndexedGraph.toMGraph, copyIndexedGraph]
        rw [weightedCopyGraph_head_copyId hE_ne heG, hpk, he_eq,
          (hv_bij_inv _ (hG₀ _ heG).2).2]
      have hℓ_eq : ℓ_v (σE q) = ℓ₀ (cl.getD q (0, 0)).1 := by
        dsimp only [ℓ_v, weightedCopyLen]
        rw [hσ_eq, origEdge_copyId heG, hpk, he_eq]
      exact ⟨hmem_gv, hinv, htail, hhead, hℓ_eq, rfl⟩
    have hσE_Ginv : ∀ e' ∈ G_v.E, σE_inv e' ∈ G_idx.toMGraph.E ∧ σE (σE_inv e') = e' := by
      intro e' he'
      obtain ⟨e, heG, k, hk_lt, heq⟩ := (mem_weightedCopyGraph_E_iff hE_ne).mp he'
      have heL := (heMem e).mpr heG
      let j := eList.idxOf e
      have hj_lt : j < G₀.E.card := by rw [← heLen]; exact List.idxOf_lt_length_of_mem heL
      have he_eq : eList.getD j 0 = e := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_idxOf (by omega)
      have hk_mult : k < mult j := by rw [hmult j hj_lt, he_eq]; exact hk_lt
      have hdiv : copyId M e k / M = k := by
        dsimp only [copyId]
        rw [Nat.add_mul_div_left _ _ (copyMod_pos G₀), Nat.div_eq_of_lt (lt_copyMod heG), zero_add]
      have hq_lt := getElem_copyList eList mult hj_lt hk_mult
      have hq_lt_m : (List.map mult (List.range j)).sum + k < G_idx.m := hq_lt.1
      have hinv_eq : σE_inv e' = (List.map mult (List.range j)).sum + k := by
        dsimp only [σE_inv]
        rw [ite_eq_left he', ← heq, origEdge_copyId heG, hdiv]
      refine ⟨?_, ?_⟩
      · simp only [IndexedGraph.toMGraph, Finset.mem_range, G_idx, copyIndexedGraph, hinv_eq]
        exact hq_lt.1
      · dsimp only [σE]
        rw [hinv_eq, ite_eq_left hq_lt_m, List.getD_eq_getElem _ _ hq_lt.1, hq_lt.2, he_eq, heq]
    let T_raw : MGraph :=
      { V := G₀.V
        E := T_dec.E.image σE
        tail := fun f =>
          if f ∈ G_v.E then G₀.tail (origEdge M f)
          else vList.getD ((bridgePairs.getD (zPrefix.idxOf (f + M - eCap)) (0, 0)).1) 0
        head := fun f =>
          if f ∈ G_v.E then G₀.head (origEdge M f)
          else vList.getD ((bridgePairs.getD (zPrefix.idxOf (f + M - eCap)) (0, 0)).2) 0 }
    have hT_raw_val : T_raw.IsValid := by
      intro f' hf'
      obtain ⟨f, hfT, rfl⟩ := Finset.mem_image.mp hf'
      dsimp only [T_dec, decodedTree] at hfT
      rcases Finset.mem_union.mp hfT with hfO | hfB
      · have hf_mem := List.mem_toFinset.mp hfO
        have hf_lt : f < G_idx.m := ho_cl f hf_mem
        have hfG : f ∈ G_idx.toMGraph.E := by simpa [G_idx, IndexedGraph.toMGraph] using hf_lt
        have hg := hσE_G f hfG
        have horig := weightedCopyGraph_origEdge_mem hE_ne hg.1
        dsimp only [T_raw]
        simp only [ite_eq_left hg.1]
        exact hG₀ _ horig.1
      · rw [Finset.mem_image] at hfB
        rcases hfB with ⟨k, hk, rfl⟩
        have hk_lt : k < bridgePairs.length := by simpa using List.mem_range.mp (List.mem_toFinset.mp hk)
        have hnot : ¬ G_idx.m + k < G_idx.m := by omega
        have hk_zp : k < zPrefix.length := by omega
        have hσ_eq : σE (G_idx.m + k) = eCap + zPrefix[k] - M := by
          dsimp only [σE]
          rw [ite_eq_right hnot, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hk_zp]
        have hnGv : σE (G_idx.m + k) ∉ G_v.E := by
          rw [hσ_eq]; exact hzPrefix_nGv _ (List.getElem_mem hk_zp)
        have hidx_eq : zPrefix.idxOf (σE (G_idx.m + k) + M - eCap) = k := by
          rw [hσ_eq]
          have hadd : eCap + zPrefix[k] - M + M - eCap = zPrefix[k] := by omega
          rw [hadd, idxOf_getElem_lt hzPrefix_nd hk_zp]
        dsimp only [T_raw]
        simp only [ite_eq_right hnGv, hidx_eq, List.getD_eq_getElem _ _ hk_lt]
        have hbp := hbr_valid _ (List.getElem_mem hk_lt)
        rw [List.getD_eq_getElem _ _ (by omega : bridgePairs[k].1 < vList.length),
            List.getD_eq_getElem _ _ (by omega : bridgePairs[k].2 < vList.length)]
        exact ⟨(hvMem _).mp (List.getElem_mem _), (hvMem _).mp (List.getElem_mem _)⟩
    have hσE_T : ∀ f ∈ T_dec.E, σE f ∈ T_raw.E ∧ σE_inv (σE f) = f ∧
        T_raw.tail (σE f) = vList.getD (T_dec.tail f) 0 ∧
        T_raw.head (σE f) = vList.getD (T_dec.head f) 0 ∧
        (f ∈ G_idx.toMGraph.E ↔ σE f ∈ G_v.E) := by
      intro f hfT
      have hmem_raw : σE f ∈ T_raw.E := Finset.mem_image_of_mem _ hfT
      dsimp only [T_dec, decodedTree] at hfT
      rcases Finset.mem_union.mp hfT with hfO | hfB
      · have hf_mem := List.mem_toFinset.mp hfO
        have hf_lt : f < G_idx.m := ho_cl f hf_mem
        have hfG : f ∈ G_idx.toMGraph.E := by simpa [G_idx, IndexedGraph.toMGraph] using hf_lt
        have hg := hσE_G f hfG
        have horig := weightedCopyGraph_origEdge_mem hE_ne hg.1
        have htail_raw : T_raw.tail (σE f) = vList.getD (T_dec.tail f) 0 := by
          dsimp only [T_raw, T_dec, decodedTree]
          rw [ite_eq_left hg.1, ite_eq_left hf_lt, ← horig.2.1, hg.2.2.1]
          rfl
        have hhead_raw : T_raw.head (σE f) = vList.getD (T_dec.head f) 0 := by
          dsimp only [T_raw, T_dec, decodedTree]
          rw [ite_eq_left hg.1, ite_eq_left hf_lt, ← horig.2.2, hg.2.2.2.1]
          rfl
        exact ⟨hmem_raw, hg.2.1, htail_raw, hhead_raw, iff_of_true hfG hg.1⟩
      · rw [Finset.mem_image] at hfB
        rcases hfB with ⟨k, hk, rfl⟩
        have hk_lt : k < bridgePairs.length := by simpa using List.mem_range.mp (List.mem_toFinset.mp hk)
        have hnot : ¬ G_idx.m + k < G_idx.m := by omega
        have hk_zp : k < zPrefix.length := by omega
        have hσ_eq : σE (G_idx.m + k) = eCap + zPrefix[k] - M := by
          dsimp only [σE]
          rw [ite_eq_right hnot, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hk_zp]
        have hnGv : σE (G_idx.m + k) ∉ G_v.E := by
          rw [hσ_eq]; exact hzPrefix_nGv _ (List.getElem_mem hk_zp)
        have hidx_eq : zPrefix.idxOf (σE (G_idx.m + k) + M - eCap) = k := by
          rw [hσ_eq]
          have hadd : eCap + zPrefix[k] - M + M - eCap = zPrefix[k] := by omega
          rw [hadd, idxOf_getElem_lt hzPrefix_nd hk_zp]
        have hinv_eq : σE_inv (σE (G_idx.m + k)) = G_idx.m + k := by
          dsimp only [σE_inv]; rw [ite_eq_right hnGv, hidx_eq]
        have hf_nG : G_idx.m + k ∉ G_idx.toMGraph.E := by
          simp only [IndexedGraph.toMGraph, Finset.mem_range]; omega
        have htail_raw : T_raw.tail (σE (G_idx.m + k)) = vList.getD (T_dec.tail (G_idx.m + k)) 0 := by
          dsimp only [T_raw, T_dec, decodedTree]
          rw [ite_eq_right hnGv, hidx_eq, ite_eq_right hnot, Nat.add_sub_cancel_left]
        have hhead_raw : T_raw.head (σE (G_idx.m + k)) = vList.getD (T_dec.head (G_idx.m + k)) 0 := by
          dsimp only [T_raw, T_dec, decodedTree]
          rw [ite_eq_right hnGv, hidx_eq, ite_eq_right hnot, Nat.add_sub_cancel_left]
        exact ⟨hmem_raw, hinv_eq, htail_raw, hhead_raw, iff_of_false hf_nG hnGv⟩
    have hσE_Tinv : ∀ f' ∈ T_raw.E, σE_inv f' ∈ T_dec.E ∧ σE (σE_inv f') = f' := by
      intro f' hf'
      obtain ⟨f, hfT, rfl⟩ := Finset.mem_image.mp hf'
      have ht := hσE_T f hfT
      exact ⟨ht.2.1.symm ▸ hfT, congrArg σE ht.2.1⟩
    have hT_raw_lsst : IsLSST G_v ℓ_v (fun _ => 1)
        ((4 * max K_AN 1 + 5) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw := by
      have hG_v_V : G_v.V = G₀.V := weightedCopyGraph_V G₀ v
      have hT_raw_V : T_raw.V = G_v.V := hG_v_V.symm
      exact isLSST_of_iso (σV := fun i => vList.getD i 0) (σV_inv := vList.idxOf)
        (σE := σE) (σE_inv := σE_inv)
        hT_dec_V hT_raw_V hG_idx_Mval (weightedCopyGraph_isValid hG₀ v)
        hT_dec_st.1.1 hT_raw_val
        (fun i hi => by have := hv_bij_mem i hi; exact ⟨hG_v_V ▸ this.1, this.2⟩)
        (fun u hu => hv_bij_inv u (hG_v_V ▸ hu))
        hσE_G hσE_Ginv hσE_T hσE_Tinv hdec_unit
    let T₀ := projectTree G₀ v T_raw
    have hT₀_V : T₀.V = G₀.V := by
      dsimp only [T₀, projectTree]; rw [ite_eq_left hE_ne]
    have hT₀_E : T₀.E = (origIds ++ brIds).toFinset := by
      dsimp only [T₀, projectTree]
      rw [ite_eq_left hE_ne]
      ext f'
      simp only [origIds, brIds, Finset.mem_image, List.mem_toFinset, List.mem_append, List.mem_map]
      constructor
      · rintro ⟨f_raw, hf_raw, rfl⟩
        obtain ⟨f, hfT, rfl⟩ := Finset.mem_image.mp hf_raw
        dsimp only [T_dec, decodedTree] at hfT
        rcases Finset.mem_union.mp hfT with hfO | hfB
        · have hf_mem := List.mem_toFinset.mp hfO
          have hf_lt : f < G_idx.m := ho_cl f hf_mem
          have hfG : f ∈ G_idx.toMGraph.E := by simpa [G_idx, IndexedGraph.toMGraph] using hf_lt
          have hg := hσE_G f hfG
          have horig := weightedCopyGraph_origEdge_mem hE_ne hg.1
          have hproj_eq : projectEdge G₀ v (σE f) = origEdge M (σE f) := by
            dsimp only [projectEdge]; exact ite_eq_left hg.1
          left
          refine ⟨f, hf_mem, ?_⟩
          rw [hproj_eq]
          dsimp only [σE]
          rw [ite_eq_left hf_lt]
          exact (origEdge_copyId (horig_e_mem f hf_mem)).symm
        · rw [Finset.mem_image] at hfB
          rcases hfB with ⟨k, hk, rfl⟩
          have hk_lt : k < bridgePairs.length := by simpa using List.mem_range.mp (List.mem_toFinset.mp hk)
          have hnot : ¬ G_idx.m + k < G_idx.m := by omega
          have hk_zp : k < zPrefix.length := by omega
          have hσ_eq : σE (G_idx.m + k) = eCap + zPrefix[k] - M := by
            dsimp only [σE]; rw [ite_eq_right hnot, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hk_zp]
          have hnGv : σE (G_idx.m + k) ∉ G_v.E := by
            rw [hσ_eq]; exact hzPrefix_nGv _ (List.getElem_mem hk_zp)
          have hproj_eq : projectEdge G₀ v (σE (G_idx.m + k)) = eCap + zPrefix[k] := by
            dsimp only [projectEdge]; rw [ite_eq_right hnGv, hσ_eq]; omega
          right
          refine ⟨zPrefix[k], List.getElem_mem hk_zp, hproj_eq.symm⟩
      · rintro (⟨q, hqO, rfl⟩ | ⟨z, hzP, rfl⟩)
        · have hq_lt : q < G_idx.m := ho_cl q hqO
          have hqG : q ∈ G_idx.toMGraph.E := by simpa [G_idx, IndexedGraph.toMGraph] using hq_lt
          have hg := hσE_G q hqG
          have hqT : q ∈ T_dec.E := Finset.mem_union_left _ (List.mem_toFinset.mpr hqO)
          refine ⟨σE q, Finset.mem_image_of_mem _ hqT, ?_⟩
          dsimp only [projectEdge]
          rw [ite_eq_left hg.1]
          dsimp only [σE]
          rw [ite_eq_left hq_lt]
          exact origEdge_copyId (horig_e_mem q hqO)
        · obtain ⟨k, hk_zp, rfl⟩ := List.mem_iff_getElem.mp hzP
          have hk_lt : k < bridgePairs.length := by omega
          have hfT : G_idx.m + k ∈ T_dec.E := by
            dsimp only [T_dec, decodedTree]
            exact Finset.mem_union_right _ (Finset.mem_image_of_mem _
              (List.mem_toFinset.mpr (List.mem_range.mpr hk_lt)))
          have hnot : ¬ G_idx.m + k < G_idx.m := by omega
          have hσ_eq : σE (G_idx.m + k) = eCap + zPrefix[k] - M := by
            dsimp only [σE]; rw [ite_eq_right hnot, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hk_zp]
          have hnGv : σE (G_idx.m + k) ∉ G_v.E := by
            rw [hσ_eq]; exact hzPrefix_nGv _ (List.getElem_mem hk_zp)
          refine ⟨σE (G_idx.m + k), Finset.mem_image_of_mem _ hfT, ?_⟩
          dsimp only [projectEdge]
          rw [ite_eq_right hnGv, hσ_eq]
          omega
    have hT₀_orig : ∀ i (hi : i < origIds.length),
        T₀.tail (origIds[i]'hi) = G₀.tail (origIds[i]'hi) ∧
        T₀.head (origIds[i]'hi) = G₀.head (origIds[i]'hi) := by
      intro i hi
      have hiO : i < origEdges.length := by simpa [origIds] using hi
      have heG : origIds[i]'hi ∈ G₀.E := by
        simpa [origIds] using horig_e_mem _ (List.getElem_mem hiO)
      dsimp only [T₀, projectTree]
      rw [ite_eq_left hE_ne]
      dsimp only
      simp [ite_eq_left heG]
    have hT₀_br : ∀ k (hk : k < brIds.length),
        T₀.tail (brIds[k]'hk) = vList.getD ((bridgePairs.getD k (0, 0)).1) 0 ∧
        T₀.head (brIds[k]'hk) = vList.getD ((bridgePairs.getD k (0, 0)).2) 0 := by
      intro k hk
      have hk_zp : k < zPrefix.length := by simpa [brIds] using hk
      have hbr_eq : brIds[k]'hk = eCap + zPrefix[k] := by simp [brIds]
      have hnG : brIds[k]'hk ∉ G₀.E := by
        intro hmem; exact Nat.not_lt_of_ge (by rw [hbr_eq]; exact Nat.le_add_right _ _) (heCap _ hmem)
      have hnGv : brIds[k]'hk - M ∉ G_v.E := by
        rw [hbr_eq]; exact hzPrefix_nGv _ (List.getElem_mem hk_zp)
      have hidx : zPrefix.idxOf (brIds[k]'hk - M + M - eCap) = k := by
        rw [hbr_eq]
        have hadd : eCap + zPrefix[k] - M + M - eCap = zPrefix[k] := by omega
        rw [hadd, idxOf_getElem_lt hzPrefix_nd hk_zp]
      dsimp only [T₀, projectTree]
      rw [ite_eq_left hE_ne]
      dsimp only [T_raw]
      have hnGv' : brIds[k]'hk - copyMod G₀ ∉ G_v.E := hnGv
      have hidx' : zPrefix.idxOf (brIds[k]'hk - copyMod G₀ + copyMod G₀ - eCap) = k := hidx
      have hidx'' : zPrefix.idxOf (brIds[k]'hk - copyMod G₀ + M - eCap) = k := hidx
      simp only [ite_eq_right hnG, ite_eq_right hnGv', hidx'', and_self]
    refine ⟨T_raw, ?_, hT₀_V, hT₀_E, hT₀_orig, hT₀_br⟩
    simpa [ite_eq_left hE_ne] using hT_raw_lsst
  · -- Empty graph case (`m0 = 0`): `origEdges = []`, `projectTree G₀ v T_raw = T_raw`.
    have hG_E_empty : G₀.E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE_ne
    have hcl_zero : cl.length = 0 := by simp [cl, hG_E_empty, copyList_length]
    have horig_nil : origEdges = [] := by
      cases origEdges with
      | nil => rfl
      | cons q _ => exact absurd (ho_cl q (by simp)) (by omega)
    let σE : ℕ → ℕ := fun k => eCap + zPrefix.getD k 0
    let σE_inv : ℕ → ℕ := fun f' => zPrefix.idxOf (f' - eCap)
    let T_raw : MGraph :=
      { V := G₀.V
        E := brIds.toFinset
        tail := fun f => vList.getD ((bridgePairs.getD (zPrefix.idxOf (f - eCap)) (0, 0)).1) 0
        head := fun f => vList.getD ((bridgePairs.getD (zPrefix.idxOf (f - eCap)) (0, 0)).2) 0 }
    have hT_raw_val : T_raw.IsValid := by
      intro f' hf'
      rw [List.mem_toFinset] at hf'
      obtain ⟨z, hzP, rfl⟩ := List.mem_map.mp hf'
      obtain ⟨k, hk_zp, rfl⟩ := List.mem_iff_getElem.mp hzP
      have hk_lt : k < bridgePairs.length := by omega
      have hidx : zPrefix.idxOf (eCap + zPrefix[k] - eCap) = k := by
        rw [Nat.add_sub_cancel_left]; exact idxOf_getElem_lt hzPrefix_nd hk_zp
      dsimp only [T_raw]
      simp only [hidx, List.getD_eq_getElem _ _ hk_lt]
      have hbp := hbr_valid _ (List.getElem_mem hk_lt)
      rw [List.getD_eq_getElem _ _ (by omega : bridgePairs[k].1 < vList.length),
          List.getD_eq_getElem _ _ (by omega : bridgePairs[k].2 < vList.length)]
      exact ⟨(hvMem _).mp (List.getElem_mem _), (hvMem _).mp (List.getElem_mem _)⟩
    have hG_idx_E0 : G_idx.toMGraph.E = ∅ := by
      ext x; simp [G_idx, IndexedGraph.toMGraph, copyIndexedGraph, hG_E_empty, copyList_zero]
    have hT_dec_E : T_dec.E = (Finset.range bridgePairs.length) := by
      dsimp only [T_dec, decodedTree, G_idx, copyIndexedGraph]
      rw [horig_nil, hcl_zero, List.toFinset_nil, Finset.empty_union]
      ext k
      simp only [Finset.mem_image, List.mem_toFinset, List.mem_range, Finset.mem_range, zero_add]
      constructor
      · rintro ⟨a, ha, rfl⟩; exact ha
      · intro ha; exact ⟨k, ha, rfl⟩
    have hσE_T : ∀ f ∈ T_dec.E, σE f ∈ T_raw.E ∧ σE_inv (σE f) = f ∧
        T_raw.tail (σE f) = vList.getD (T_dec.tail f) 0 ∧
        T_raw.head (σE f) = vList.getD (T_dec.head f) 0 ∧
        (f ∈ G_idx.toMGraph.E ↔ σE f ∈ G₀.E) := by
      intro k hk
      rw [hT_dec_E, Finset.mem_range] at hk
      have hk_zp : k < zPrefix.length := by omega
      have hσ_eq : σE k = eCap + zPrefix[k] := by
        dsimp only [σE]; rw [List.getD_eq_getElem _ _ hk_zp]
      have hmem : σE k ∈ T_raw.E := by
        dsimp only [T_raw]; rw [List.mem_toFinset, hσ_eq]
        exact List.mem_map.mpr ⟨_, List.getElem_mem hk_zp, rfl⟩
      have hidx : zPrefix.idxOf (σE k - eCap) = k := by
        rw [hσ_eq, Nat.add_sub_cancel_left]; exact idxOf_getElem_lt hzPrefix_nd hk_zp
      have hnot_m : ¬ k < G_idx.m := by rw [← hcl_len, hcl_zero]; omega
      have htail : T_raw.tail (σE k) = vList.getD (T_dec.tail k) 0 := by
        dsimp only [T_raw, T_dec, decodedTree]
        rw [hidx, ite_eq_right hnot_m, show G_idx.m = 0 from hcl_zero, Nat.sub_zero]
      have hhead : T_raw.head (σE k) = vList.getD (T_dec.head k) 0 := by
        dsimp only [T_raw, T_dec, decodedTree]
        rw [hidx, ite_eq_right hnot_m, show G_idx.m = 0 from hcl_zero, Nat.sub_zero]
      have hfG : (k ∈ G_idx.toMGraph.E ↔ σE k ∈ G₀.E) := by
        simp [hG_idx_E0, hG_E_empty]
      exact ⟨hmem, hidx, htail, hhead, hfG⟩
    have hσE_Tinv : ∀ f' ∈ T_raw.E, σE_inv f' ∈ T_dec.E ∧ σE (σE_inv f') = f' := by
      intro f' hf'
      dsimp only [T_raw] at hf'
      rw [List.mem_toFinset] at hf'
      obtain ⟨z, hzP, rfl⟩ := List.mem_map.mp hf'
      obtain ⟨k, hk_zp, rfl⟩ := List.mem_iff_getElem.mp hzP
      have hidx : zPrefix.idxOf (eCap + zPrefix[k] - eCap) = k := by
        rw [Nat.add_sub_cancel_left]; exact idxOf_getElem_lt hzPrefix_nd hk_zp
      refine ⟨?_, ?_⟩
      · dsimp only [σE_inv]; rw [hT_dec_E, Finset.mem_range, hidx]; omega
      · dsimp only [σE, σE_inv]; rw [hidx, List.getD_eq_getElem _ _ hk_zp]
    have hT_raw_lsst : IsLSST G₀ (fun _ => 1) (fun _ => 1)
        ((4 * max K_AN 1 + 5) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2) T_raw := by
      exact isLSST_of_iso (G₁ := G_idx.toMGraph) (G₂ := G₀) (T₁ := T_dec) (T₂ := T_raw)
        (ℓ₁ := fun q => ℓ₀ (cl.getD q (0, 0)).1) (ℓ₂ := fun _ => 1)
        (v₁ := fun _ => 1) (v₂ := fun _ => 1)
        (σV := fun i => vList.getD i 0) (σV_inv := vList.idxOf)
        (σE := σE) (σE_inv := σE_inv)
        hT_dec_V rfl hG_idx_Mval hG₀ hT_dec_st.1.1 hT_raw_val
        hv_bij_mem hv_bij_inv
        (fun e he => absurd he (by simp [hG_idx_E0]))
        (fun e' he' => absurd he' (by simp [hG_E_empty]))
        hσE_T hσE_Tinv hdec_unit
    have hT₀_eq : projectTree G₀ v T_raw = T_raw := ite_eq_right hE_ne
    refine ⟨T_raw, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [ite_eq_right hE_ne] using hT_raw_lsst
    · rw [hT₀_eq]
    · rw [hT₀_eq]; simp [T_raw, origIds, brIds, zPrefix, horig_nil, List.map_take]
    · intro i hi
      simp [horig_nil] at hi
    · intro k hk
      rw [hT₀_eq]
      have hk_zp : k < zPrefix.length := by
        have hk' := hk
        simp only [brIds, List.length_map] at hk'
        exact hk'
      have hbr_eq : brIds[k]'hk = eCap + zPrefix[k] := by simp [brIds]
      have hidx : zPrefix.idxOf (brIds[k]'hk - eCap) = k := by
        rw [hbr_eq, Nat.add_sub_cancel_left]; exact idxOf_getElem_lt hzPrefix_nd hk_zp
      refine ⟨?_, ?_⟩
      · show vList.getD ((bridgePairs.getD (zPrefix.idxOf (brIds[k]'hk - eCap)) (0, 0)).1) 0 = _
        rw [hidx]
      · show vList.getD ((bridgePairs.getD (zPrefix.idxOf (brIds[k]'hk - eCap)) (0, 0)).2) 0 = _
        rw [hidx]

/-! ## Monotonicity of LSST parameter and resource bounds in `m` -/

lemma w'Max_mono_m {c_AN n m₁ m₂ L h : ℕ} (hm : m₁ ≤ m₂) :
    w'Max c_AN n m₁ L h ≤ w'Max c_AN n m₂ L h := by
  dsimp only [w'Max]
  have hlog : Nat.log 2 (6 + 16 * m₁) ≤ Nat.log 2 (6 + 16 * m₂) := Nat.log_mono_right (by omega)
  have hk : kWidthOf m₁ L ≤ kWidthOf m₂ L := kWidthOf_mono hm
  exact Nat.mul_le_mul_left _ (by nlinarith)

lemma lsstLSimMin_mono_m {c_AN n m₁ m₂ L h : ℕ} (hm : m₁ ≤ m₂) :
    lsstLSimMin c_AN n m₁ L h ≤ lsstLSimMin c_AN n m₂ L h :=
  max_le_max (kWidthOf_mono hm) (w'Max_mono_m hm)

lemma anCostBound_mono_m {K_AN : ℝ} {n m₁ m₂ L_sim h : ℕ} (hL : 1 ≤ L_sim) (hh : 1 ≤ h)
    (hm : m₁ ≤ m₂) :
    anCostBound K_AN n m₁ L_sim h ≤ anCostBound K_AN n m₂ L_sim h := by
  dsimp only [anCostBound]
  have hW : 2 ≤ 2 ^ (L_sim * h) := by
    have hpos : 1 ≤ L_sim * h := Nat.mul_pos hL hh
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (L_sim * h) := Nat.pow_le_pow_right (by norm_num) hpos
  have hwf_nn : 0 ≤ Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h)) :=
    logLog_add_weightFactor_nonneg n (2 ^ (L_sim * h)) hW
  have hm_r : (↑(4 * m₁) + 1 : ℝ) ≤ (↑(4 * m₂) + 1 : ℝ) := by exact_mod_cast (by omega : 4 * m₁ + 1 ≤ 4 * m₂ + 1)
  have hK0 : 0 ≤ max K_AN 0 := le_max_right _ _
  have hmul : max K_AN 0 * (↑(4 * m₁) + 1) *
        (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) ≤
      max K_AN 0 * (↑(4 * m₂) + 1) *
        (Cited.logLogFactor n + Cited.weightFactor n (2 ^ (L_sim * h))) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm_r hK0) hwf_nn
  exact Nat.ceil_mono hmul

lemma lsstSpace_mono_m {Q_AN : Program} {K_AN : ℝ} {n m₁ m₂ L_sim h : ℕ}
    (hL : 1 ≤ L_sim) (hh : 1 ≤ h) (hm : m₁ ≤ m₂) :
    lsstSpace Q_AN K_AN n m₁ L_sim h ≤ lsstSpace Q_AN K_AN n m₂ L_sim h := by
  have hc : anCostBound K_AN n m₁ L_sim h ≤ anCostBound K_AN n m₂ L_sim h :=
    anCostBound_mono_m hL hh hm
  dsimp only [lsstSpace, weightsSpace, simDecodeSpace]
  have h1 : m₁ * L_sim ≤ m₂ * L_sim := Nat.mul_le_mul_right _ hm
  have h2 : (2 + 3 * (4 * m₁)) * L_sim ≤ (2 + 3 * (4 * m₂)) * L_sim :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : m₁ * (18 * L_sim + 2 * Num.integerDivideSpace (2 * L_sim)) ≤
      m₂ * (18 * L_sim + 2 * Num.integerDivideSpace (2 * L_sim)) := Nat.mul_le_mul_right _ hm
  have h4 : (2 * m₁) * L_sim ≤ (2 * m₂) * L_sim := Nat.mul_le_mul_right _ (by omega)
  have h5 : (2 + 3 * (4 * m₁)) * (L_sim * 2 ^ h + L_sim) ≤
      (2 + 3 * (4 * m₂)) * (L_sim * 2 ^ h + L_sim) := Nat.mul_le_mul_right _ (by omega)
  have h6 : simScale Q_AN * L_sim * 2 ^ h * (anCostBound K_AN n m₁ L_sim h + (2 + 3 * (4 * m₁)) + 1) ≤
      simScale Q_AN * L_sim * 2 ^ h * (anCostBound K_AN n m₂ L_sim h + (2 + 3 * (4 * m₂)) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h7 : (1 + 2 * m₁) * L_sim ≤ (1 + 2 * m₂) * L_sim := Nat.mul_le_mul_right _ (by omega)
  omega

end

end MinCostFlow.LSF.Program
