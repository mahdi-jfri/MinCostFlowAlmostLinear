module

public import MinCostFlow.HierPaths.BuildTopNumbers
public import MinCostFlow.HierPaths.BuildTopRootCompact
public import MinCostFlow.HierPaths.BuildTopDriverRun
public import MinCostFlow.HierPaths.BuildTopScheduledGraphs
import MinCostFlow.HierPaths.BuildTopSums

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Depth recursion invariant, space envelope, and initialization

Defines `BuildLevelSpacePoly`, proves `depthOf_le_ell_two_pow` (discharging `r ≤ ell M`
at every top-level level call), defines the depth-loop invariant `BuildTopRecInv`
tracking bump-heap growth `heap ≤ heap₀ + i * (2^x * spaceBound + 2^x)`, and proves
that the invariant holds immediately after `buildTopPrepare`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp
open scoped BigOperators

/-- Space envelope for a level procedure meeting `ProvidesBuildLevel`.
Permits polynomial dependence on the graph/level parameters and on
`WParam ParamConfig.default M ^ (10 * r ^ 2 + 10)` whenever `r ≤ ell M`. -/
def BuildLevelSpacePoly
    (space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (Cs cs : ℕ) : Prop :=
  ∀ G s k M r Δ L L' bh, r ≤ ell M →
    space G s k M r Δ L L' bh ≤
      Cs * (G.n + G.m + s + k + M + r + Δ + L + L' + bh +
        (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) + 2) ^ cs

/-- Per-depth driver cost rate. -/
def buildTopRate (K x m d i : ℕ) : ℕ :=
  2 ^ x * (buildTopDepthFactor K x m d i + 311)

/-- Every top-level call to the level builder satisfies `r = depthOf m ≤ ell (2 ^ x)`. -/
theorem depthOf_le_ell_two_pow {m : ℕ} (hm : 1 ≤ m) :
    depthOf m ≤ ell (2 ^ Nat.clog 2 (2 * m)) := by
  set x := Nat.clog 2 (2 * m)
  have hx1 : 1 ≤ x := by
    have hlt : 0 < Nat.clog 2 (2 * m) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
    omega
  have h2m : 2 * m ≤ 2 ^ x := Nat.le_pow_clog (by decide) (2 * m)
  have hxOf : xOf m ≤ x + 3 := by
    unfold xOf
    rw [Nat.clog_le_iff_le_pow (by decide)]
    have hpow : 2 ^ (x + 3) = 8 * 2 ^ x := by rw [pow_add]; ring
    omega
  have hcube : x + 3 ≤ (x + 1) ^ 3 := by
    have hpow3 : (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by ring
    nlinarith
  have hcr : depthOf m ≤ x + 1 := ceilRoot_le (hxOf.trans hcube)
  exact hcr.trans (ell_two_pow x).1

/-- Depth-loop invariant connecting prepared root memory through certified replies. -/
structure BuildTopRecInv (r x b D m d spaceBound : ℕ) (root : Graph) (memPrep : ℕ → ℕ)
    (i heap : ℕ) (mem : ℕ → ℕ) : Prop where
  frame : ∀ y < buildTopPrepareTable r x + 13 * D, mem y = memPrep y
  zero : ZeroFrom mem heap
  heap_lo : buildTopPrepareHeap r x D ≤ heap
  heap_hi : heap ≤ buildTopPrepareHeap r x D + i * (2 ^ x * spaceBound + 2 ^ x)
  replies : ∃ (reply : ℕ → ℕ → BuildLevelData) (replyAddr : ℕ → ℕ → ℕ)
      (curDir : ℕ) (curAddr : ℕ → ℕ),
    (∀ j < i, ∀ g < numGroups x b j,
      mem (buildTopScheduleReplies (buildTopPrepareTable r x) D x j + g) = replyAddr j g ∧
      buildTopPrepareHeap r x D ≤ replyAddr j g ∧
      replyAddr j g + ((reply j g).encode (branching x b j)).length ≤ heap ∧
      ListAt mem (replyAddr j g) ((reply j g).encode (branching x b j)) ∧
      (reply j g).Good ((buildTopHierarchy x b root reply).host j g)
        (g * groupSize x b j) (groupSize x b (j + 1)) (branching x b j)
        (2 ^ x) (depthOf m) (49 * (x + 1) + 2) (x + 1) (x + 1) (buildTopBh x m d j)) ∧
    mem (buildTopSchedulePointer (buildTopPrepareTable r x) D i) = curDir ∧
    (i = 0 → curDir = r + 2 ^ x) ∧
    (0 < i → buildTopPrepareHeap r x D ≤ curDir) ∧
    curDir + numGroups x b i ≤ heap ∧
    (∀ g < numGroups x b i,
      let Hg := (buildTopHierarchy x b root reply).host i g
      mem (curDir + g) = curAddr g ∧
      (i = 0 → curAddr g + Hg.encode.length ≤ r) ∧
      (0 < i → buildTopPrepareHeap r x D ≤ curAddr g ∧ curAddr g + Hg.encode.length ≤ heap) ∧
      GraphAt mem (curAddr g) Hg ∧
      Hg.n = 2 ^ x ∧ Hg.IsValid ∧ Hg.IsLoopless ∧
      (∀ e ∈ Hg.edges, e.1 ∈ members x b i g ∧ e.2 ∈ members x b i g) ∧
      (∀ v ∈ members x b i g, Hg.deg v ≤ 49 * (x + 1) + 2) ∧
      (i < D → ∃ β : ℝ, 0 < β ∧ Hg.IsExpansionExpanderOn (members x b i g) β ∧
        max 2 (2 / β) ≤ (buildTopBh x m d i : ℝ)))

lemma range_slice_finsetWords {mem : ℕ → ℕ} {r P start s k : ℕ}
    (ht : ListAt mem r (List.range P)) (hle : start + s * k ≤ P) :
    ListAt mem (r + start) (finsetWords (buildLevelVerts start s k)) := by
  rw [buildTopLevelWords_eq]
  intro j hj
  have hlen : (List.range' start (s * k)).length = s * k := List.length_range'
  have hj' : j < s * k := hlen ▸ hj
  have hmem := ht (start + j) (by simp; omega)
  rw [List.getElem_range] at hmem
  rw [List.getElem_range']
  simpa [Nat.add_assoc] using hmem

lemma buildTopHierarchy_host_congr {x b : ℕ} {root : Graph}
    {reply reply' : ℕ → ℕ → BuildLevelData} {i : ℕ}
    (h : ∀ j < i, ∀ g, reply' j g = reply j g) :
    ∀ j ≤ i, ∀ g,
      (buildTopHierarchy x b root reply').host j g = (buildTopHierarchy x b root reply).host j g := by
  intro j hj g
  cases j with
  | zero => rfl
  | succ j =>
    simp only [buildTopHierarchy]
    split_ifs
    · rw [h j (by omega)]
    · rfl

lemma rec_members_subset_range (x b j g : ℕ) (hg : g < numGroups x b j) :
    members x b j g ⊆ Finset.range (2 ^ x) := by
  intro v hv
  rw [members, Finset.mem_Ico] at hv
  rw [Finset.mem_range]
  have h1 : (g + 1) * groupSize x b j ≤ numGroups x b j * groupSize x b j :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hg)
  rw [numGroups_mul_groupSize] at h1
  omega

lemma gs_le_pow (x b j : ℕ) : groupSize x b j ≤ 2 ^ x :=
  Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)

lemma groupSize_even_or_one (x b j : ℕ) :
    groupSize x b j = 1 ∨ groupSize x b j % 2 = 0 := by
  unfold groupSize
  cases h : x - min x (j * b) with
  | zero => left; simp
  | succ k => right; rw [pow_succ]; omega

lemma branching_ge_two_of_lt_leafDepth {x b j : ℕ} (hb : 0 < b) (hj : j < leafDepth x b) :
    2 ≤ branching x b j := by
  have hgs := one_lt_groupSize_of_lt_leafDepth hb hj
  have htb : j * b < x := by
    by_contra hge
    have : groupSize x b j = 1 := by
      unfold groupSize; rw [Nat.min_eq_left (by omega), Nat.sub_self, pow_zero]
    omega
  have hle : x - min x ((j + 1) * b) ≤ x - min x (j * b) := by
    have : j * b ≤ (j + 1) * b := Nat.mul_le_mul_right b (Nat.le_succ j)
    omega
  have hbr : branching x b j = 2 ^ (min x ((j + 1) * b) - min x (j * b)) := by
    unfold branching groupSize
    rw [Nat.pow_div hle (by decide)]
    congr 1; omega
  have hpos : 1 ≤ min x ((j + 1) * b) - min x (j * b) := by
    have : (j + 1) * b = j * b + b := by ring
    omega
  rw [hbr]
  simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hpos

lemma groupSize_le_N_pow (x b j m : ℕ) :
    groupSize x b j ≤ (NOf (2 ^ x) (depthOf m)) ^ (depthOf m) := by
  have hgs : groupSize x b j ≤ 2 ^ x := gs_le_pow x b j
  have hle : 2 ^ x ≤ (NOf (2 ^ x) (depthOf m)) ^ (depthOf m) := by
    unfold NOf
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    have hr : 1 ≤ depthOf m := le_trans (by decide) (two_le_depthOf m)
    have hdp : 0 < depthOf m := by omega
    have hell := (ell_two_pow x).1
    have hcd : ell (2 ^ x) ≤ ceilDiv (ell (2 ^ x)) (depthOf m) * depthOf m := by
      unfold ceilDiv
      have h1 := Nat.div_add_mod (ell (2 ^ x) + depthOf m - 1) (depthOf m)
      have h2 := Nat.mod_lt (ell (2 ^ x) + depthOf m - 1) hdp
      rw [Nat.mul_comm]
      generalize depthOf m * ((ell (2 ^ x) + depthOf m - 1) / depthOf m) = P at *
      omega
    have hmax : ceilDiv (ell (2 ^ x)) (depthOf m) * depthOf m ≤
        max 2 (ceilDiv (ell (2 ^ x)) (depthOf m)) * depthOf m :=
      Nat.mul_le_mul_right _ (le_max_right _ _)
    omega
  exact hgs.trans hle

lemma four_nine_le_delta (x : ℕ) : 49 * (x + 1) ≤ deltaParam (2 ^ x) := by
  have hell := (ell_two_pow x).1
  unfold deltaParam tParam LParam
  omega

lemma groupSize_lt_two_pow_succ (x b j : ℕ) :
    groupSize x b j < 2 ^ (x + 1) := by
  have hgs := gs_le_pow x b j
  have hpos : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  rw [pow_succ]; omega

lemma root_expansion_bh {G : Graph} {phiNum phiDen : ℕ}
    (h1 : 1 ≤ phiNum) (h2 : phiNum ≤ phiDen) (hG : G.IsValid) (hm : 1 ≤ G.m)
    (hcond : G.IsConductanceExpanderOn G.verts ((phiNum : ℝ) / (phiDen : ℝ))) :
    let x := Nat.clog 2 (2 * G.m)
    let b := buildTopBranch x G.m
    ∃ β : ℝ, 0 < β ∧ (hostGraph cloud G).IsExpansionExpanderOn (members x b 0 0) β ∧
      max 2 (2 / β) ≤ ((100 * dOf phiNum phiDen : ℕ) : ℝ) := by
  dsimp only
  set φ : ℝ := (phiNum : ℝ) / (phiDen : ℝ)
  obtain ⟨hφ, hd1, hφd⟩ := dOf_spec h1 h2
  obtain ⟨_, hhs, _, _, _⟩ := buildTop_x_facts hG hm
  obtain ⟨⟨hn, _, _, _⟩, _, _, _, _, hexp, _, _, _, _, _⟩ := lemma_2 hG hm hφ hcond
  have hmem_eq : members (Nat.clog 2 (2 * G.m)) (buildTopBranch (Nat.clog 2 (2 * G.m)) G.m) 0 0 =
      (hostGraph ExplicitExpander.explicitGraph G).verts := by
    unfold members groupSize Graph.verts
    rw [hn, ← hhs]
    simp
  refine ⟨min φ 1 / 50, by positivity, ?_, ?_⟩
  · rw [hostGraph_cloud_eq_explicit G, hmem_eq]
    exact hexp
  · have hmin : (1 : ℝ) / (dOf phiNum phiDen : ℝ) ≤ min φ 1 := by
      refine le_min hφd ?_
      have hdR : (1 : ℝ) ≤ (dOf phiNum phiDen : ℝ) := by exact_mod_cast hd1
      exact div_le_one_of_le₀ hdR (by positivity)
    have h50 : (2 : ℝ) / (min φ 1 / 50) ≤ ((100 * dOf phiNum phiDen : ℕ) : ℝ) := by
      have hd_pos : (0 : ℝ) < (dOf phiNum phiDen : ℝ) := by exact_mod_cast hd1
      have hmin_pos : (0 : ℝ) < min φ 1 := by positivity
      rw [div_div_eq_mul_div, div_le_iff₀ hmin_pos]
      push_cast
      have hmul : (1 : ℝ) ≤ (dOf phiNum phiDen : ℝ) * min φ 1 := by
        rwa [div_le_iff₀ hd_pos, mul_comm] at hmin
      nlinarith
    have h2le : (2 : ℝ) ≤ ((100 * dOf phiNum phiDen : ℕ) : ℝ) := by
      exact_mod_cast (show 2 ≤ 100 * dOf phiNum phiDen by omega)
    exact max_le h2le h50

lemma inner_expansion_bh (M r : ℕ) :
    let β : ℝ := 1 / (2 * (PParam ParamConfig.default M r : ℝ))
    0 < β ∧ max 2 (2 / β) ≤ ((4 * PParam ParamConfig.default M r : ℕ) : ℝ) := by
  have hP1 : 1 ≤ PParam ParamConfig.default M r := one_le_PParam ParamConfig.default M r
  have hPR : (1 : ℝ) ≤ (PParam ParamConfig.default M r : ℝ) := by exact_mod_cast hP1
  refine ⟨by positivity, ?_⟩
  have hdiv : (2 : ℝ) / (1 / (2 * (PParam ParamConfig.default M r : ℝ))) =
      4 * (PParam ParamConfig.default M r : ℝ) := by field_simp; ring
  rw [hdiv]
  push_cast
  exact max_le (by linarith) le_rfl

lemma reply_host_encode_end {a k c : ℕ} {D : BuildLevelData} (hc : c < k) :
    buildTopChildAddr a k c D + (D.host c).encode.length ≤ a + (D.encode k).length := by
  have hsec0 := initCSRAddr_le_end (addr := a + 4) (k := k)
    (f := fun j => (D.host j).encode) (i := c + 1) (Nat.succ_le_of_lt hc)
  rw [initCSRAddr_succ] at hsec0
  have houter := initCSRAddr_le_end (addr := a) (k := 3)
    (f := fun idx => (buildTopReplySections D k).getD idx []) (i := 1) (by decide)
  rw [initCSRAddr_succ] at houter
  have h0 : initCSRAddr a 3 (fun idx => (buildTopReplySections D k).getD idx []) 0 = a + 4 := by
    simp [initCSRAddr, initCSRPrefix]
  have henc : csrList 3 (fun idx => (buildTopReplySections D k).getD idx []) = D.encode k := rfl
  rw [h0, henc] at houter
  change a + 4 + (csrList k fun j => (D.host j).encode).length ≤ a + (D.encode k).length at houter
  have hca : buildTopChildAddr a k c D = initCSRAddr (a + 4) k (fun j => (D.host j).encode) c := rfl
  omega

/-- Initial invariant holds right after `buildTopPrepare_compact_meetsContract`. -/
theorem buildTopRecInv_init {G : Graph} {h r phiNum phiDen spaceBound : ℕ} {memPrep : ℕ → ℕ}
    (h1 : 1 ≤ phiNum) (h2 : phiNum ≤ phiDen) (hG : G.IsValid) (hm : 1 ≤ G.m)
    (hcond : G.IsConductanceExpanderOn G.verts ((phiNum : ℝ) / (phiDen : ℝ)))
    (hreq : r = h + buildTopRootWorkspace G.n G.m)
    (hGraphAt : GraphAt memPrep (buildTopRootGraphAddr h G.n G.m) (hostGraph cloud G))
    (hDir0 : memPrep (r + 2 ^ Nat.clog 2 (2 * G.m)) = buildTopRootGraphAddr h G.n G.m)
    (hPtr0 : memPrep (buildTopSchedulePointer (buildTopPrepareTable r (Nat.clog 2 (2 * G.m)))
      (leafDepth (Nat.clog 2 (2 * G.m)) (buildTopBranch (Nat.clog 2 (2 * G.m)) G.m)) 0) =
      r + 2 ^ Nat.clog 2 (2 * G.m))
    (hZero : ZeroFrom memPrep (buildTopPrepareHeap r (Nat.clog 2 (2 * G.m))
      (leafDepth (Nat.clog 2 (2 * G.m)) (buildTopBranch (Nat.clog 2 (2 * G.m)) G.m)))) :
    let x := Nat.clog 2 (2 * G.m)
    let b := buildTopBranch x G.m
    let D := leafDepth x b
    BuildTopRecInv r x b D G.m (dOf phiNum phiDen) spaceBound (hostGraph cloud G) memPrep
      0 (buildTopPrepareHeap r x D) memPrep := by
  dsimp only
  set x := Nat.clog 2 (2 * G.m)
  set b := buildTopBranch x G.m
  set D := leafDepth x b
  set d := dOf phiNum phiDen
  set root := hostGraph cloud G
  obtain ⟨hpc, hhs, hxpos, _, _⟩ := buildTop_x_facts hG hm
  obtain ⟨hφ, _, _⟩ := dOf_spec h1 h2
  obtain ⟨⟨hn, _, _, _⟩, hval, hloop, hdeg, _, _, _, _, _, _, _⟩ := lemma_2 hG hm hφ hcond
  have hroot_eq : root = hostGraph ExplicitExpander.explicitGraph G := hostGraph_cloud_eq_explicit G
  have hGraphEnd : buildTopRootGraphAddr h G.n G.m + root.encode.length ≤ r := by
    have hE := graph_encode_length root
    have hmIn : 1 ≤ (G.inside G.verts).length := by rw [inside_verts_length hG]; exact hm
    have hh : root.m ≤ 12 * G.m := by
      have h1' := hostGraph_m_le (G := G) isCloudExpander_cloud hmIn
      rw [inside_verts_length hG] at h1'
      exact h1'
    rw [hreq]; unfold buildTopRootWorkspace buildTopRootGraphAddr buildTopRootOwnersAddr buildTopRootLoc
    omega
  have hDirLe : r + 2 ^ x + numGroups x b 0 ≤ buildTopPrepareHeap r x D := by
    simp only [numGroups, zero_mul, Nat.min_zero, pow_zero]
    unfold buildTopPrepareHeap buildTopPrepareTable buildTopScheduleEnd buildTopScheduleReplies
      buildTopSchedulePointer
    omega
  refine ⟨fun _ _ => rfl, hZero, le_rfl, by simp,
    fun _ _ => ⟨fun _ => ⟨0, []⟩, fun _ _ => [], fun _ _ => []⟩,
    fun _ _ => 0, r + 2 ^ x, fun _ => buildTopRootGraphAddr h G.n G.m,
    fun _ hj => absurd hj (Nat.not_lt_zero _), hPtr0, fun _ => rfl, fun h0 => absurd h0 (by decide),
    hDirLe, ?_⟩
  intro g hg
  have hg0 : g = 0 := by simpa [numGroups] using hg
  subst g
  have hhost0 : (buildTopHierarchy x b root
      (fun _ _ => ⟨fun _ => ⟨0, []⟩, fun _ _ => [], fun _ _ => []⟩)).host 0 0 = root := by
    simp [buildTopHierarchy]
  rw [hhost0]
  have hn_root : root.n = 2 ^ x := by rw [hroot_eq, hn, ← hhs]
  have hval_root : root.IsValid := hroot_eq ▸ hval
  have hloop_root : root.IsLoopless := hroot_eq ▸ hloop
  refine ⟨by simpa using hDir0, fun _ => hGraphEnd, fun h0 => absurd h0 (by decide),
    hGraphAt, hn_root, hval_root, hloop_root, ?_, ?_, fun _ => root_expansion_bh h1 h2 hG hm hcond⟩
  · intro e he
    have hv := hval_root e he
    rw [hn_root] at hv
    simp [members, groupSize, hv.1, hv.2]
  · intro v _
    have hv := (hroot_eq ▸ hdeg) v
    omega

end MinCostFlow.HierPaths

end
