module

public import MinCostFlow.HierPaths.BuildTopRecBase
import MinCostFlow.HierPaths.BuildTopSums

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Running the depth recursion from the prepared compact root

Connects the state produced by `buildTopPrepare` (with the compact zero-heap root)
to `buildTopDriver_runs`. At each depth `i < leafDepth x b`, the invariant supplies
the parent graphs, verifies all preconditions of `buildLevelContract` (including
`depthOf m ≤ ell (2 ^ x)`, degree, expansion, `HostPre`, and `BuildLevelSpacePoly`),
and collects the certified parent replies into `buildTopHierarchy`.

When the loop finishes at `i = leafDepth x b`, the replies satisfy `buildTopRepliesGood`,
so the assembled hierarchy produces a `Good` `StaticData` meeting `SpecRest`, all reply
blocks remain intact in memory below the returned bump-heap pointer `tail`, `tail` is
bounded by `heap₀ + D * (2 ^ x * spaceBound + 2 ^ x)`, and the total driver cost is
bounded by `O((K + 1) * G.m * Γ)`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp
open scoped BigOperators

private lemma rangeCost_zero_le_mul_rec {f : ℕ → ℕ} {n B : ℕ}
    (h : ∀ i < n, f i ≤ B) : rangeCost f 0 n ≤ n * B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append,
      ← rangeCost_zero_eq_range, List.map_singleton, List.sum_singleton, Nat.succ_mul]
    exact Nat.add_le_add (ih fun i hi => h i (Nat.lt_succ_of_lt hi)) (h n (Nat.lt_succ_self n))

private lemma rec_work_le {K x b m d i g : ℕ} {Hg : Graph}
    (hb_eq : buildTopBranch x m = b)
    (hg : g < numGroups x b i)
    (hn_g : Hg.n = 2 ^ x) (hloop_g : Hg.IsLoopless)
    (hsupp_g : ∀ e ∈ Hg.edges, e.1 ∈ members x b i g ∧ e.2 ∈ members x b i g)
    (hdeg_g : ∀ v ∈ members x b i g, Hg.deg v ≤ 49 * (x + 1) + 2) :
    buildLevelCost K Hg (groupSize x b (i + 1)) (branching x b i) (2 ^ x) (depthOf m)
      (49 * (x + 1) + 2) (x + 1) (x + 1) (buildTopBh x m d i) + 24 ≤
    groupSize x b i * buildTopDepthFactor K x m d i := by
  subst hb_eq
  have hmem_sub := rec_members_subset_range x (buildTopBranch x m) i g hg
  have ⟨_, hm_g⟩ := buildTop_hostPre_and_m hn_g hmem_sub hloop_g (by omega) hdeg_g hsupp_g
  rw [card_members] at hm_g
  have hsk : groupSize x (buildTopBranch x m) (i + 1) * branching x (buildTopBranch x m) i =
      groupSize x (buildTopBranch x m) i := by
    rw [Nat.mul_comm, ← groupSize_eq_mul_branching]
  have hm_sk : Hg.m ≤ (49 * (x + 1) + 2) *
      (groupSize x (buildTopBranch x m) (i + 1) * branching x (buildTopBranch x m) i) :=
    hsk.symm ▸ hm_g
  have hlc := buildTopLevelCost_le (K := K) (s := groupSize x (buildTopBranch x m) (i + 1))
    (k := branching x (buildTopBranch x m) i)
    (M := 2 ^ x) (r := depthOf m) (Δ := 49 * (x + 1) + 2) (L := x + 1) (L' := x + 1)
    (bh := buildTopBh x m d i) (E := 49 * (x + 1) + 2)
    groupSize_pos branching_pos hm_sk
  rw [hsk] at hlc
  exact hlc

private lemma rec_work_le_no24 {K x b m d i g : ℕ} {Hg : Graph}
    (hb_eq : buildTopBranch x m = b)
    (hg : g < numGroups x b i)
    (hn_g : Hg.n = 2 ^ x) (hloop_g : Hg.IsLoopless)
    (hsupp_g : ∀ e ∈ Hg.edges, e.1 ∈ members x b i g ∧ e.2 ∈ members x b i g)
    (hdeg_g : ∀ v ∈ members x b i g, Hg.deg v ≤ 49 * (x + 1) + 2) :
    buildLevelCost K Hg (groupSize x b (i + 1)) (branching x b i) (2 ^ x) (depthOf m)
      (49 * (x + 1) + 2) (x + 1) (x + 1) (buildTopBh x m d i) ≤
    groupSize x b i * buildTopDepthFactor K x m d i :=
  (Nat.le_add_right _ 24).trans (rec_work_le hb_eq hg hn_g hloop_g hsupp_g hdeg_g)

private lemma buildTopScheduledDepth_denominator (table D r x b m d i dir : ℕ)
    (addr : ℕ → ℕ) (graphs : ℕ → Graph) :
    (buildTopScheduledDepth table D r x b m d i dir addr graphs).denominator =
      buildTopBh x m d i := by
  cases i with
  | zero => simp only [buildTopScheduledDepth, buildTopDepthPlayer, buildTopBh, ↓reduceIte]
  | succ i' =>
    simp only [buildTopScheduledDepth, buildTopDepthPlayer, buildTopBh, Nat.succ_ne_zero, ↓reduceIte]

private lemma rec_step_next {w K r x b D m d spaceBound i curHeap v curDir : ℕ}
    {root : Graph} {memPrep mem m' : ℕ → ℕ}
    {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {curAddr : ℕ → ℕ}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hbpos : 0 < b) (hi : i < D) (hD_eq : D = leafDepth x b)
    (hFrame : ∀ y < buildTopPrepareTable r x + 13 * D, mem y = memPrep y)
    (hHeapLo : buildTopPrepareHeap r x D ≤ curHeap)
    (hHeapHi : curHeap ≤ buildTopPrepareHeap r x D + i * (2 ^ x * spaceBound + 2 ^ x))
    (hPrevReplies : ∀ j < i, ∀ g < numGroups x b j,
      mem (buildTopScheduleReplies (buildTopPrepareTable r x) D x j + g) = replyAddr j g ∧
      buildTopPrepareHeap r x D ≤ replyAddr j g ∧
      replyAddr j g + ((reply j g).encode (branching x b j)).length ≤ curHeap ∧
      ListAt mem (replyAddr j g) ((reply j g).encode (branching x b j)) ∧
      (reply j g).Good ((buildTopHierarchy x b root reply).host j g)
        (g * groupSize x b j) (groupSize x b (j + 1)) (branching x b j)
        (2 ^ x) (depthOf m) (49 * (x + 1) + 2) (x + 1) (x + 1) (buildTopBh x m d j))
    (hCurN : ∀ g < numGroups x b i, ((buildTopHierarchy x b root reply).host i g).n = 2 ^ x)
    (hSpSum :
      let DI := buildTopScheduledDepth (buildTopPrepareTable r x) D r x b m d i curDir curAddr
        (fun g => (buildTopHierarchy x b root reply).host i g)
      rangeCost (DI.spaceStep space) 0 DI.count + DI.count * DI.branch ≤
        2 ^ x * spaceBound + 2 ^ x)
    (hPost :
      let DI := buildTopScheduledDepth (buildTopPrepareTable r x) D r x b m d i curDir curAddr
        (fun g => (buildTopHierarchy x b root reply).host i g)
      (DI.advanceContract w K space).post
        (DI.args curHeap ++ [buildTopSchedulePointer (buildTopPrepareTable r x) D (i + 1)])
        mem v m') :
    BuildTopRecInv r x b D m d spaceBound root memPrep (i + 1) v m' := by
  let table := buildTopPrepareTable r x
  let heap₀ := buildTopPrepareHeap r x D
  let DI := buildTopScheduledDepth (buildTopPrepareTable r x) D r x b m d i curDir curAddr
    (fun g => (buildTopHierarchy x b root reply).host i g)
  have hDI_rd : DI.replyDir = buildTopScheduleReplies table D x i := rfl
  have hDI_br : DI.branch = branching x b i := rfl
  have hDI_cnt : DI.count = numGroups x b i := rfl
  have hDI_bh : DI.denominator = buildTopBh x m d i :=
    buildTopScheduledDepth_denominator _ _ _ _ _ _ _ _ _ _ _
  have hEndLe : buildTopScheduleEnd table D x ≤ heap₀ := by
    change buildTopScheduleEnd (buildTopPrepareTable r x) D x ≤ buildTopPrepareHeap r x D
    unfold buildTopPrepareHeap; omega
  have hDisj := buildTopSchedule_disjoint (table := table) (n := D) (x := x) (b := b) hi
  have hFrameStep := buildTopAdvance_scheduleFrame (b := b) (D := DI) hi rfl
    (hEndLe.trans hHeapLo) hPost
  obtain ⟨hHeapMono, hPrevDirKeep, nextDir, nextAddr, nextReply, hDirGe, hv_eq,
    hPtrNext, hReplyAt, hChildDir⟩ :=
    buildTopAdvance_scheduleLink (b := b) (D := DI) hi rfl (hEndLe.trans hHeapLo) hPost
  obtain ⟨h', out', dir', heArgs, _, hDirHi, hv_eq', _, hZ', hAdvFrame, _⟩ := hPost
  have hh' : h' = curHeap := by
    have e := congrArg (fun ws : List ℕ => ws.getD 12 0) heArgs
    simp only [BuildTopDepthInput.args, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero] at e
    exact e.symm
  have hout' : out' = buildTopSchedulePointer table D (i + 1) := by
    have e := congrArg (fun ws : List ℕ => ws.getD 13 0) heArgs
    simp only [BuildTopDepthInput.args, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero] at e
    exact e.symm
  subst h' out'
  have hdir_eq : dir' = nextDir := Nat.add_right_cancel (hv_eq'.symm.trans hv_eq)
  rw [hdir_eq] at hDirHi
  have hv_hi : v ≤ heap₀ + (i + 1) * (2 ^ x * spaceBound + 2 ^ x) := by
    rw [Nat.succ_mul, ← Nat.add_assoc, hv_eq]
    calc nextDir + DI.count * DI.branch
      _ ≤ curHeap + rangeCost (DI.spaceStep space) 0 DI.count + DI.count * DI.branch :=
            Nat.add_le_add_right hDirHi _
      _ = curHeap + (rangeCost (DI.spaceStep space) 0 DI.count + DI.count * DI.branch) :=
            Nat.add_assoc _ _ _
      _ ≤ (heap₀ + i * (2 ^ x * spaceBound + 2 ^ x)) + (2 ^ x * spaceBound + 2 ^ x) :=
            Nat.add_le_add hHeapHi hSpSum
  let reply' : ℕ → ℕ → BuildLevelData := fun j g => if j = i then nextReply g else reply j g
  let replyAddr' : ℕ → ℕ → ℕ := fun j g => if j = i then nextAddr g else replyAddr j g
  have hHostCon := buildTopHierarchy_host_congr (x := x) (b := b) (root := root)
    (reply := reply) (reply' := reply') (i := i) (fun j hj g => by simp [reply', Nat.ne_of_lt hj])
  let k := branching x b i
  have hkpos : 0 < k := branching_pos
  have hng_succ : numGroups x b (i + 1) = DI.count * DI.branch := by
    rw [hDI_cnt, hDI_br]; exact numGroups_succ x b i
  let nextCurAddr : ℕ → ℕ := fun g =>
    buildTopChildAddr (nextAddr (g / k)) k (g % k) (nextReply (g / k))
  refine ⟨fun y hy => (hFrameStep y hy).trans (hFrame y hy), hZ', hHeapLo.trans hHeapMono, hv_hi,
    reply', replyAddr', nextDir, nextCurAddr, ?_, hPtrNext, fun h0 => absurd h0 (Nat.succ_ne_zero _),
    fun _ => hHeapLo.trans hDirGe, by rw [hv_eq, hng_succ], ?_⟩
  · intro j hj g hg
    by_cases hji : j = i
    · subst j
      obtain ⟨hDirG, hAddrLo, hAddrHi, hListAt, hGoodG⟩ := hReplyAt g hg
      have hstart_g : DI.start g = g * groupSize x b i := by
        unfold BuildTopDepthInput.start
        change g * (groupSize x b (i + 1) * branching x b i) = _
        rw [Nat.mul_comm (groupSize x b (i + 1)), ← groupSize_eq_mul_branching]
      rw [hDI_rd] at hDirG
      rw [hDI_br] at hAddrHi hListAt
      rw [hstart_g, hDI_bh, hDI_br] at hGoodG
      have hGood' : (nextReply g).Good ((buildTopHierarchy x b root reply').host i g)
          (g * groupSize x b i) (groupSize x b (i + 1)) (branching x b i)
          (2 ^ x) (depthOf m) (49 * (x + 1) + 2) (x + 1) (x + 1) (buildTopBh x m d i) := by
        rw [hHostCon i le_rfl g]
        exact hGoodG
      refine ⟨by simp only [replyAddr', ↓reduceIte]; exact hDirG,
        by simp only [replyAddr', ↓reduceIte]; exact hHeapLo.trans hAddrLo,
        by simp only [reply', replyAddr', ↓reduceIte]; exact hAddrHi.trans (hv_eq ▸ Nat.le_add_right _ _),
        by simp only [reply', replyAddr', ↓reduceIte]; exact hListAt,
        by simp only [reply', ↓reduceIte]; exact hGood'⟩
    · have hjlt : j < i := by omega
      obtain ⟨hDirG, hAddrLo, hAddrHi, hListAt, hGoodG⟩ := hPrevReplies j hjlt g hg
      have hDirM' : m' (buildTopScheduleReplies table D x j + g) = replyAddr j g :=
        (hPrevDirKeep j hjlt g hg).trans hDirG
      have hListM' : ListAt m' (replyAddr j g) ((reply j g).encode (branching x b j)) := by
        intro u hu
        have hlt_cur : replyAddr j g + u < curHeap := by omega
        have hne_out : replyAddr j g + u ≠ buildTopSchedulePointer table D (i + 1) := by omega
        have hnot_rep : replyAddr j g + u < DI.replyDir ∨ DI.replyDir + DI.count ≤ replyAddr j g + u :=
          Or.inr (by rw [hDI_rd, hDI_cnt]; omega)
        exact (hAdvFrame _ hlt_cur hne_out hnot_rep).trans (hListAt u hu)
      have hGood' : (reply j g).Good ((buildTopHierarchy x b root reply').host j g)
          (g * groupSize x b j) (groupSize x b (j + 1)) (branching x b j)
          (2 ^ x) (depthOf m) (49 * (x + 1) + 2) (x + 1) (x + 1) (buildTopBh x m d j) := by
        rw [hHostCon j hjlt.le g]
        exact hGoodG
      refine ⟨by simp only [replyAddr', hji, ↓reduceIte]; exact hDirM',
        by simp only [replyAddr', hji, ↓reduceIte]; exact hAddrLo,
        by simp only [reply', replyAddr', hji, ↓reduceIte]; exact hAddrHi.trans hHeapMono,
        by simp only [reply', replyAddr', hji, ↓reduceIte]; exact hListM',
        by simp only [reply', hji, ↓reduceIte]; exact hGood'⟩
  · intro g hg
    have hg' : g < DI.count * k := hng_succ ▸ hg
    have hpar : g / k < DI.count := (Nat.div_lt_iff_lt_mul hkpos).mpr hg'
    have hloc : g % k < k := Nat.mod_lt g hkpos
    obtain ⟨_, hAddrLo, hAddrHi, hListAt, hGoodP⟩ := hReplyAt (g / k) hpar
    have hHostEq : (buildTopHierarchy x b root reply').host (i + 1) g =
        (nextReply (g / k)).host (g % k) := by
      simp only [buildTopHierarchy, ite_eq_left hg, reply', parentGroup, k, ↓reduceIte]
    have hGAt_g : GraphAt m' (nextCurAddr g) ((nextReply (g / k)).host (g % k)) :=
      buildTopChildAddr_graphAt hListAt hloc
    have hAddrG_lo : nextAddr (g / k) ≤ nextCurAddr g := by
      unfold nextCurAddr buildTopChildAddr; omega
    have hAddrG_hi : nextCurAddr g + ((nextReply (g / k)).host (g % k)).encode.length ≤
        nextAddr (g / k) + ((nextReply (g / k)).encode k).length :=
      reply_host_encode_end hloc
    obtain ⟨hn_c, hval_c, hloop_c, hsupp_c, hdeg_c, _, hexp_c⟩ := hGoodP.graph (g % k) hloc
    have hn_p : ((buildTopHierarchy x b root reply).host i (g / k)).n = 2 ^ x := hCurN (g / k) hpar
    have hchild_eq : buildLevelChild (DI.start (g / k)) DI.childSize (g % k) =
        members x b (i + 1) g := by
      have hstart_p : DI.start (g / k) = (g / k) * groupSize x b i := by
        unfold BuildTopDepthInput.start
        change (g / k) * (groupSize x b (i + 1) * k) = _
        rw [Nat.mul_comm (groupSize x b (i + 1)), ← groupSize_eq_mul_branching]
      rw [hstart_p, show DI.childSize = groupSize x b (i + 1) from rfl, buildTopLevelChild_eq]
      exact congrArg (members x b (i + 1)) (buildTopChild_decompose x b i g)
    rw [hchild_eq] at hsupp_c hdeg_c hexp_c
    rw [hHostEq]
    refine ⟨hChildDir g hg', fun h0 => absurd h0 (Nat.succ_ne_zero _),
      fun _ => ⟨(hHeapLo.trans hAddrLo).trans hAddrG_lo,
        (hAddrG_hi.trans hAddrHi).trans (hv_eq ▸ Nat.le_add_right _ _)⟩,
      hGAt_g, hn_c.trans hn_p, hval_c, hloop_c, hsupp_c, hdeg_c, ?_⟩
    intro hi1
    have hgs1 : 1 < groupSize x b (i + 1) := one_lt_groupSize_of_lt_leafDepth hbpos (hD_eq ▸ hi1)
    obtain ⟨hβpos, hβbh⟩ := inner_expansion_bh (2 ^ x) (depthOf m)
    exact ⟨1 / (2 * (PParam ParamConfig.default (2 ^ x) (depthOf m) : ℝ)),
      hβpos, hexp_c hgs1, hβbh⟩

private lemma rec_step_ready
    {w K r x b D m d i curHeap spaceBound : ℕ}
    {root : Graph} {memPrep mem : ℕ → ℕ}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (hb_eq : buildTopBranch x m = b) (hbpos : 0 < b) (hD_eq : D = leafDepth x b) (hi : i < D)
    (hRank : depthOf m ≤ ell (2 ^ x))
    (h1w : 1 < 2 ^ w)
    (hTerms : ListAt memPrep r (List.range (2 ^ x)))
    (hRows : let table := buildTopPrepareTable r x
      ∀ j < D, ∀ dir addr graphs, ListAt memPrep (table + 13 * j)
        ((buildTopScheduledDepth table D r x b m d j dir addr graphs).scheduleWords
          (buildTopSchedulePointer table D j) (buildTopSchedulePointer table D (j + 1))))
    (hSpace : ∀ (H : Graph) (s k bh : ℕ), H.n = 2 ^ x →
      H.m ≤ (49 * (x + 1) + 2) * 2 ^ x → s ≤ 2 ^ x → k ≤ 2 ^ x →
      bh ≤ max (100 * d) (4 * PParam ParamConfig.default (2 ^ x) (depthOf m)) →
      space H s k (2 ^ x) (depthOf m) (49 * (x + 1) + 2) (x + 1) (x + 1) bh ≤ spaceBound)
    (hRoom : buildTopPrepareHeap r x D + D * (2 ^ x * spaceBound + 2 ^ x) + spaceBound < 2 ^ w)
    (hWordsBase : 100 * d < 2 ^ w ∧
      4 * PParam ParamConfig.default (2 ^ x) (depthOf m) < 2 ^ w ∧
      depthOf m < 2 ^ w ∧ 49 * (x + 1) + 2 < 2 ^ w)
    (hInv : BuildTopRecInv r x b D m d spaceBound root memPrep i curHeap mem) :
    let table := buildTopPrepareTable r x
    ∃ DI : BuildTopDepthInput,
      ListAt mem (table + 13 * i)
        (DI.scheduleWords (buildTopSchedulePointer table D i)
          (buildTopSchedulePointer table D (i + 1))) ∧
      mem (buildTopSchedulePointer table D i) = DI.graphDir ∧
      (∀ v ∈ DI.args curHeap ++ [buildTopSchedulePointer table D (i + 1)], v < 2 ^ w) ∧
      (DI.advanceContract w K space).pre
        (DI.args curHeap ++ [buildTopSchedulePointer table D (i + 1)]) mem ∧
      (DI.advanceContract w K space).cost
        (DI.args curHeap ++ [buildTopSchedulePointer table D (i + 1)]) mem + 62 ≤
        buildTopRate K x m d i ∧
      ∀ v m', (DI.advanceContract w K space).post
        (DI.args curHeap ++ [buildTopSchedulePointer table D (i + 1)]) mem v m' →
        BuildTopRecInv r x b D m d spaceBound root memPrep (i + 1) v m' := by
  dsimp only
  set table := buildTopPrepareTable r x
  set heap₀ := buildTopPrepareHeap r x D
  obtain ⟨hFrame, hZ, hHeapLo, hHeapHi, reply, replyAddr, curDir, curAddr,
    hPrevReplies, hPtrCur, hDirZ, hDirPos, hDirLe, hCurGraphs⟩ := hInv
  let DI := buildTopScheduledDepth table D r x b m d i curDir curAddr
    (fun g => (buildTopHierarchy x b root reply).host i g)
  have hbr_ge2 : 2 ≤ branching x b i := branching_ge_two_of_lt_leafDepth hbpos (hD_eq ▸ hi)
  have hbr_le_gs : branching x b i ≤ groupSize x b i := by
    have := groupSize_eq_mul_branching (x := x) (b := b) (j := i)
    have hpos := groupSize_pos (x := x) (b := b) (j := i + 1)
    nlinarith
  have hDI_gd : DI.graphDir = curDir := rfl
  have hDI_rd : DI.replyDir = buildTopScheduleReplies table D x i := rfl
  have hDI_tb : DI.termBase = r := rfl
  have hDI_br : DI.branch = branching x b i := rfl
  have hDI_cnt : DI.count = numGroups x b i := rfl
  have hDI_bh : DI.denominator = buildTopBh x m d i :=
    buildTopScheduledDepth_denominator _ _ _ _ _ _ _ _ _ _ _
  have hWork_le : ∀ g < DI.count, DI.work K g ≤ groupSize x b i * buildTopDepthFactor K x m d i := by
    intro g hg
    obtain ⟨_, _, _, _, hn_g, _, hloop_g, hsupp_g, hdeg_g, _⟩ := hCurGraphs g hg
    have hwork_eq : DI.work K g = buildLevelCost K ((buildTopHierarchy x b root reply).host i g)
        (groupSize x b (i + 1)) (branching x b i) (2 ^ x) (depthOf m)
        (49 * (x + 1) + 2) (x + 1) (x + 1) (buildTopBh x m d i) := by
      dsimp only [BuildTopDepthInput.work, DI, buildTopScheduledDepth, buildTopDepthPlayer]
      exact congrArg (buildLevelCost K ((buildTopHierarchy x b root reply).host i g)
        (groupSize x b (i + 1)) (branching x b i) (2 ^ x) (depthOf m)
        (49 * (x + 1) + 2) (x + 1) (x + 1)) hDI_bh
    rw [hwork_eq]
    exact rec_work_le_no24 hb_eq hg hn_g hloop_g hsupp_g hdeg_g
  have hStepBound : rangeCost (fun g => DI.work K g + 60) 0 DI.count + 9 * DI.count + 20 +
      100 * (DI.count * DI.branch) + 122 ≤ buildTopRate K x m d i :=
    buildTopDriverStepCost_le x b i K DI (buildTopDepthFactor K x m d i)
      rfl hbr_le_gs hWork_le
  have hStepCost : (DI.advanceContract w K space).cost
      (DI.args curHeap ++ [buildTopSchedulePointer table D (i + 1)]) mem + 62 ≤
      buildTopRate K x m d i := by
    dsimp only [BuildTopDepthInput.advanceContract, BuildTopDepthInput.contract]
    exact hStepBound
  have hSpEach : ∀ g < DI.count, DI.spaceStep space g ≤ spaceBound := by
    intro g hg
    obtain ⟨_, _, _, _, hn_g, _, hloop_g, hsupp_g, hdeg_g, _⟩ := hCurGraphs g hg
    have hmem_sub := rec_members_subset_range x b i g hg
    have ⟨_, hm_g⟩ := buildTop_hostPre_and_m hn_g hmem_sub hloop_g (by omega) hdeg_g hsupp_g
    rw [card_members] at hm_g
    dsimp only [BuildTopDepthInput.spaceStep]
    rw [hDI_bh]
    apply hSpace _ _ _ _ hn_g
    · exact hm_g.trans (Nat.mul_le_mul_left _ (gs_le_pow x b i))
    · exact gs_le_pow x b (i + 1)
    · exact hbr_le_gs.trans (gs_le_pow x b i)
    · cases i with
      | zero => exact le_max_left _ _
      | succ _ => exact le_max_right _ _
  have hRC_sp : rangeCost (DI.spaceStep space) 0 DI.count ≤ 2 ^ x * spaceBound := by
    calc rangeCost (DI.spaceStep space) 0 DI.count
        ≤ DI.count * spaceBound := rangeCost_zero_le_mul_rec hSpEach
      _ ≤ 2 ^ x * spaceBound := Nat.mul_le_mul_right _ (buildTopSchedule_replySpan x b i)
  have hNextCnt : DI.count * DI.branch ≤ 2 ^ x := by
    have hng : DI.count * DI.branch = numGroups x b (i + 1) := by
      rw [hDI_cnt, hDI_br]; exact (numGroups_succ x b i).symm
    rw [hng]; exact buildTopSchedule_replySpan x b (i + 1)
  have hSpSum : rangeCost (DI.spaceStep space) 0 DI.count + DI.count * DI.branch ≤
      2 ^ x * spaceBound + 2 ^ x := Nat.add_le_add hRC_sp hNextCnt
  have hMulStep : (i + 1) * (2 ^ x * spaceBound + 2 ^ x) ≤ D * (2 ^ x * spaceBound + 2 ^ x) :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hMulStep
  have hCurSpace : curHeap + rangeCost (DI.spaceStep space) 0 DI.count + spaceBound < 2 ^ w := by
    omega
  have hCurAdv : curHeap + rangeCost (DI.spaceStep space) 0 DI.count + DI.count * DI.branch < 2 ^ w := by
    omega
  have hCurHeapW : curHeap < 2 ^ w := lt_of_le_of_lt (by omega) hCurSpace
  have hDisj := buildTopSchedule_disjoint (table := table) (n := D) (x := x) (b := b) hi
  have hEndLe : buildTopScheduleEnd table D x ≤ heap₀ := by
    change buildTopScheduleEnd (buildTopPrepareTable r x) D x ≤ buildTopPrepareHeap r x D
    unfold buildTopPrepareHeap; omega
  have hTableLeEnd : table ≤ buildTopScheduleEnd table D x := by
    unfold buildTopScheduleEnd buildTopScheduleReplies buildTopSchedulePointer; omega
  have hrP_lt_table : r + 2 ^ x < table := by
    change r + 2 ^ x < buildTopPrepareTable r x
    unfold buildTopPrepareTable; omega
  have h2xw : 2 ^ x < 2 ^ w := by
    have : 2 ^ x ≤ table := by change 2 ^ x ≤ buildTopPrepareTable r x; unfold buildTopPrepareTable; omega
    omega
  have hRow_m : ListAt mem (table + 13 * i)
      (DI.scheduleWords (buildTopSchedulePointer table D i)
        (buildTopSchedulePointer table D (i + 1))) := by
    intro j hj
    have hj13 : j < 13 := by simpa [BuildTopDepthInput.scheduleWords] using hj
    rw [hFrame (table + 13 * i + j) (by omega)]
    exact hRows i hi curDir curAddr (fun g => (buildTopHierarchy x b root reply).host i g) j hj
  have hTerms_m : ListAt mem r (List.range (2 ^ x)) := by
    intro j hj
    have hjP : j < 2 ^ x := by simpa using hj
    rw [hFrame (r + j) (by omega)]
    exact hTerms j hj
  have hOut_lt : buildTopSchedulePointer table D (i + 1) < curHeap := by omega
  have hOut_skip : buildTopSchedulePointer table D (i + 1) < DI.replyDir ∨
      DI.replyDir + DI.count ≤ buildTopSchedulePointer table D (i + 1) :=
    Or.inl (hDI_rd ▸ hDisj.2.2.1)
  have hArgsW : ∀ v ∈ DI.args curHeap ++ [buildTopSchedulePointer table D (i + 1)], v < 2 ^ w := by
    intro v hv
    simp only [BuildTopDepthInput.args, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    rcases hv with (h | h | h | h | h | h | h | h | h | h | h | h | h) | h <;> rw [h]
    · rw [hDI_gd]; exact lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ _) hDirLe) hCurHeapW
    · rw [hDI_rd]; omega
    · rw [hDI_tb]
      exact (lt_of_le_of_lt (Nat.le_add_right r (2 ^ x))
        (hrP_lt_table.trans_le (hTableLeEnd.trans (hEndLe.trans hHeapLo)))).trans hCurHeapW
    · exact (gs_le_pow x b (i + 1)).trans_lt h2xw
    · exact (hbr_le_gs.trans (gs_le_pow x b i)).trans_lt h2xw
    · exact (buildTopSchedule_replySpan x b i).trans_lt h2xw
    · exact h2xw
    · exact hWordsBase.2.2.1
    · exact hWordsBase.2.2.2
    · exact (by omega : x + 1 < 2 ^ w)
    · exact (by omega : x + 1 < 2 ^ w)
    · rw [hDI_bh]; cases i <;> [exact hWordsBase.1; exact hWordsBase.2.1]
    · exact hCurHeapW
    · omega
  have hGraphDisj : DI.graphDir + DI.count ≤ DI.replyDir ∨
      DI.replyDir + DI.count ≤ DI.graphDir := by
    rw [hDI_gd, hDI_rd, hDI_cnt]
    cases i with
    | zero =>
      left
      have h0 := hDirZ rfl
      have hng0 : numGroups x b 0 = 1 := by simp [numGroups]
      have htable_le : table ≤ buildTopScheduleReplies table D x 0 := by
        unfold buildTopScheduleReplies buildTopSchedulePointer; omega
      omega
    | succ i' =>
      right
      have hpos := hDirPos (Nat.succ_pos i')
      omega
  have hParentReady : ∀ g < DI.count, DI.parentReady w K curHeap g space mem := by
    intro g hg
    obtain ⟨hAddr, hEndZ, hEndPos, hGAt, hn_g, hval_g, hloop_g, hsupp_g, hdeg_g, hexp_g⟩ :=
      hCurGraphs g hg
    have hmem_sub := rec_members_subset_range x b i g hg
    have ⟨hHostPre, hm_g⟩ := buildTop_hostPre_and_m hn_g hmem_sub hloop_g (by omega) hdeg_g hsupp_g
    rw [card_members] at hm_g
    have hstart_eq : DI.start g = g * groupSize x b i := by
      unfold BuildTopDepthInput.start
      change g * (groupSize x b (i + 1) * branching x b i) = _
      rw [Nat.mul_comm (groupSize x b (i + 1)), ← groupSize_eq_mul_branching]
    have hverts_eq : buildLevelVerts (DI.start g) DI.childSize DI.branch = members x b i g := by
      rw [hstart_eq]; exact buildTopLevelVerts_eq x b i g
    have hsk_le : DI.start g + DI.childSize * DI.branch ≤ 2 ^ x := by
      rw [hstart_eq]
      change g * groupSize x b i + groupSize x b (i + 1) * branching x b i ≤ 2 ^ x
      rw [Nat.mul_comm (groupSize x b (i + 1)), ← groupSize_eq_mul_branching]
      have h1' : (g + 1) * groupSize x b i ≤ numGroups x b i * groupSize x b i :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hg)
      rw [numGroups_mul_groupSize, Nat.add_mul, Nat.one_mul] at h1'
      exact h1'
    have hGa_le : curAddr g + ((buildTopHierarchy x b root reply).host i g).encode.length ≤ curHeap := by
      cases i with
      | zero => exact (hEndZ rfl).trans (by omega)
      | succ i' => exact (hEndPos (Nat.succ_pos i')).2
    have hSp_le : DI.spaceStep space g ≤ spaceBound := hSpEach g hg
    have hDI_ga : DI.graphAddr g = curAddr g := rfl
    have hDI_g : DI.graph g = (buildTopHierarchy x b root reply).host i g := rfl
    have hSp_lt : curHeap + rangeCost (DI.spaceStep space) 0 DI.count +
        space (DI.graph g) DI.childSize DI.branch
          DI.scale DI.rank DI.degree DI.pathLog DI.coreLog DI.denominator < 2 ^ w :=
      lt_of_le_of_lt (Nat.add_le_add_left hSp_le _) hCurSpace
    have hSp_lt0 : curHeap + space (DI.graph g) DI.childSize DI.branch
        DI.scale DI.rank DI.degree DI.pathLog DI.coreLog DI.denominator < 2 ^ w :=
      lt_of_le_of_lt (by omega) hSp_lt
    have hCallWords : ∀ v ∈ DI.callArgs g curHeap, v < 2 ^ w := by
      intro v hv
      simp only [BuildTopDepthInput.callArgs, buildLevelArgs, List.mem_cons, List.not_mem_nil,
        or_false] at hv
      rcases hv with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
      · rw [hDI_ga]; omega
      · exact hArgsW _ (by simp [BuildTopDepthInput.args])
      · have : DI.start g ≤ 2 ^ x := by omega
        exact lt_of_le_of_lt this h2xw
      · exact hArgsW _ (by simp [BuildTopDepthInput.args])
      · exact hArgsW _ (by simp [BuildTopDepthInput.args])
      · exact hArgsW _ (by simp [BuildTopDepthInput.args])
      · exact hArgsW _ (by simp [BuildTopDepthInput.args])
      · exact hArgsW _ (by simp [BuildTopDepthInput.args])
      · exact hArgsW _ (by simp [BuildTopDepthInput.args])
      · exact hArgsW _ (by simp [BuildTopDepthInput.args])
      · exact hArgsW _ (by simp [BuildTopDepthInput.args])
      · exact hCurHeapW
    refine ⟨hCallWords, ?_, ?_, ?_, hSp_lt⟩
    · refine ⟨curAddr g, r, curHeap, rfl, by omega, ⟨⟨curAddr g, r + DI.start g, curHeap, rfl,
        hGAt, range_slice_finsetWords hTerms_m hsk_le, hGa_le, ?_,
        hval_g, hverts_eq ▸ hHostPre, hbr_ge2, groupSize_pos,
        groupSize_even_or_one x b (i + 1), groupSize_le_N_pow x b (i + 1) m,
        hRank, four_nine_le_delta x, groupSize_lt_two_pow_succ x b (i + 1), ?_⟩,
        hZ, ?_⟩⟩
      · rw [buildTopLevelWords_eq, List.length_range']; omega
      · rw [hverts_eq, hDI_bh]; exact hexp_g hi
      · dsimp only [buildLevelArgs, heapArg, List.getLastD]; exact hSp_lt0
    · intro y hy1 hy2
      rw [hDI_ga] at hy1 hy2
      rw [hDI_g] at hy2
      rw [hDI_rd, hDI_cnt]
      cases i with
      | zero =>
        left
        have h0 := hEndZ rfl
        have : r < buildTopScheduleReplies table D x 0 := by
          unfold buildTopScheduleReplies buildTopSchedulePointer table buildTopPrepareTable; omega
        omega
      | succ i' =>
        right
        have hpos := (hEndPos (Nat.succ_pos i')).1
        omega
    · intro y hy1 hy2
      left
      rw [hDI_rd]
      have : r + 2 ^ x < buildTopScheduleReplies table D x i := by
        unfold buildTopScheduleReplies buildTopSchedulePointer table buildTopPrepareTable; omega
      omega
  have hAdvPre : (DI.advanceContract w K space).pre
      (DI.args curHeap ++ [buildTopSchedulePointer table D (i + 1)]) mem := by
    refine ⟨curHeap, buildTopSchedulePointer table D (i + 1), rfl,
      ⟨curHeap, rfl, ?_, ?_, by omega, h1w, hZ, by rw [hDI_rd, hDI_cnt]; omega,
        by rw [hDI_gd, hDI_cnt]; exact hDirLe, hGraphDisj,
        fun g hg => (hCurGraphs g hg).1, hParentReady⟩,
      branching_pos, hOut_lt, hOut_skip, hCurAdv⟩
    · have : DI.childSize * DI.branch = groupSize x b i := by
        change groupSize x b (i + 1) * branching x b i = _
        rw [Nat.mul_comm, ← groupSize_eq_mul_branching]
      rw [this]
      exact (gs_le_pow x b i).trans_lt h2xw
    · exact (buildTopSchedule_replySpan x b i).trans_lt h2xw
  refine ⟨DI, hRow_m, hPtrCur, hArgsW, hAdvPre, hStepCost, ?_⟩
  intro v m' hPost
  exact rec_step_next hbpos hi hD_eq hFrame hHeapLo hHeapHi hPrevReplies
    (fun g hg => (hCurGraphs g hg).2.2.2.2.1) hSpSum hPost

/-- Run `buildTopDriver advance` starting from the prepared compact root state. -/
theorem buildTopDriver_from_prepare
    {w K advance h r phiNum phiDen pos spaceBound : ℕ} {p : Program} {G : Graph}
    {memPrep : ℕ → ℕ}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} (ω : ℕ → Bool)
    (h1 : 1 ≤ phiNum) (h2 : phiNum ≤ phiDen) (hG : G.IsValid) (hm : 1 ≤ G.m)
    (hcond : G.IsConductanceExpanderOn G.verts ((phiNum : ℝ) / (phiDen : ℝ)))
    (hreq : r = h + buildTopRootWorkspace G.n G.m)
    (hGraphAt : GraphAt memPrep (buildTopRootGraphAddr h G.n G.m) (hostGraph cloud G))
    (hDir0 : memPrep (r + 2 ^ Nat.clog 2 (2 * G.m)) = buildTopRootGraphAddr h G.n G.m)
    (hPtr0 : memPrep (buildTopSchedulePointer (buildTopPrepareTable r (Nat.clog 2 (2 * G.m)))
      (leafDepth (Nat.clog 2 (2 * G.m)) (buildTopBranch (Nat.clog 2 (2 * G.m)) G.m)) 0) =
      r + 2 ^ Nat.clog 2 (2 * G.m))
    (hTerms : ListAt memPrep r (List.range (2 ^ Nat.clog 2 (2 * G.m))))
    (hRows : let x := Nat.clog 2 (2 * G.m)
      let b := buildTopBranch x G.m
      let D := leafDepth x b
      let table := buildTopPrepareTable r x
      ∀ j < D, ∀ dir addr graphs, ListAt memPrep (table + 13 * j)
        ((buildTopScheduledDepth table D r x b G.m (dOf phiNum phiDen) j dir addr graphs).scheduleWords
          (buildTopSchedulePointer table D j) (buildTopSchedulePointer table D (j + 1))))
    (hZero : ZeroFrom memPrep (buildTopPrepareHeap r (Nat.clog 2 (2 * G.m))
      (leafDepth (Nat.clog 2 (2 * G.m)) (buildTopBranch (Nat.clog 2 (2 * G.m)) G.m))))
    (ha : ∀ D : BuildTopDepthInput, MeetsContract w p advance (D.advanceContract w K space))
    (hSpace : let x := Nat.clog 2 (2 * G.m)
      ∀ (H : Graph) (s k bh : ℕ), H.n = 2 ^ x →
        H.m ≤ (49 * (x + 1) + 2) * 2 ^ x → s ≤ 2 ^ x → k ≤ 2 ^ x →
        bh ≤ max (100 * dOf phiNum phiDen) (4 * PParam ParamConfig.default (2 ^ x) (depthOf G.m)) →
        space H s k (2 ^ x) (depthOf G.m) (49 * (x + 1) + 2) (x + 1) (x + 1) bh ≤ spaceBound)
    (hRoom : let x := Nat.clog 2 (2 * G.m)
      let b := buildTopBranch x G.m
      let D := leafDepth x b
      buildTopPrepareHeap r x D + D * (2 ^ x * spaceBound + 2 ^ x) + spaceBound < 2 ^ w)
    (hWordsBase : let x := Nat.clog 2 (2 * G.m)
      100 * dOf phiNum phiDen < 2 ^ w ∧
      4 * PParam ParamConfig.default (2 ^ x) (depthOf G.m) < 2 ^ w ∧
      depthOf G.m < 2 ^ w ∧ 49 * (x + 1) + 2 < 2 ^ w) :
    let x := Nat.clog 2 (2 * G.m)
    let b := buildTopBranch x G.m
    let D := leafDepth x b
    let d := dOf phiNum phiDen
    let table := buildTopPrepareTable r x
    let heap₀ := buildTopPrepareHeap r x D
    ∃ tail t c,
      Runs w p ω (buildTopDriver advance) (startState [table, D, heap₀] memPrep pos)
        (.returned tail) t c ∧
      BuildTopRecInv r x b D G.m d spaceBound (hostGraph cloud G) memPrep D tail t.mem ∧
      c ≤ (∑ i ∈ Finset.range D, buildTopRate K x G.m d i) + 9 * D + 12 := by
  dsimp only
  set x := Nat.clog 2 (2 * G.m)
  set b := buildTopBranch x G.m
  set D := leafDepth x b
  set d := dOf phiNum phiDen
  set table := buildTopPrepareTable r x
  set heap₀ := buildTopPrepareHeap r x D
  set root := hostGraph cloud G
  obtain ⟨_, _, hxpos, _, hxX⟩ := buildTop_x_facts hG hm
  have hbpos : 0 < b := buildTopBranch_pos hxpos
  have hD_le_h : D ≤ depthOf G.m := leafDepth_buildTopBranch_le hxpos hxX
  have hRank : depthOf G.m ≤ ell (2 ^ x) := depthOf_le_ell_two_pow hm
  have h1w : 1 < 2 ^ w := by omega
  have hDw : D < 2 ^ w := hD_le_h.trans_lt hWordsBase.2.2.1
  have hTableLeHeap : table + 13 * D ≤ heap₀ := by
    change buildTopPrepareTable r x + 13 * D ≤ buildTopPrepareHeap r x D
    unfold buildTopPrepareHeap buildTopScheduleEnd buildTopScheduleReplies buildTopSchedulePointer
    omega
  have hRoom' : heap₀ + D * (2 ^ x * spaceBound + 2 ^ x) + spaceBound < 2 ^ w := hRoom
  have hTableRoom : table + 13 * D < 2 ^ w :=
    lt_of_le_of_lt (hTableLeHeap.trans (Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _))) hRoom'
  have hinit := buildTopRecInv_init (spaceBound := spaceBound) h1 h2 hG hm hcond hreq hGraphAt
    hDir0 hPtr0 hZero
  have hdrv := buildTopDriver_runs (w := w) (K := K) (advance := advance) (table := table)
    (count := D) (heap := heap₀) (pos := pos) (p := p) (mem := memPrep)
    (inCell := buildTopSchedulePointer table D)
    (outCell := fun i => buildTopSchedulePointer table D (i + 1))
    (rate := buildTopRate K x G.m d)
    (space := space)
    (I := BuildTopRecInv r x b D G.m d spaceBound root memPrep)
    ω hDw h1w hTableRoom hinit ha
    (fun i hi curHeap m hInv => rec_step_ready rfl hbpos rfl hi hRank h1w hTerms hRows hSpace
      hRoom hWordsBase hInv)
  obtain ⟨tail, t, c, hrun, hInv, hcost⟩ := hdrv
  have hrc : rangeCost (buildTopRate K x G.m d) 0 D =
      ∑ i ∈ Finset.range D, buildTopRate K x G.m d i := by
    rw [rangeCost_zero_eq_range]; rfl
  rw [hrc] at hcost
  exact ⟨tail, t, c, hrun, hInv, hcost⟩

/-- Extract the completed replies, reply directory entries, and `buildTopRepliesGood` witness
from the final recursion invariant `BuildTopRecInv ... D tail mem`. -/
theorem buildTopRecInv_final
    {r x b D m d spaceBound tail : ℕ} {root : Graph} {memPrep mem : ℕ → ℕ}
    (hb : 0 < b) (hD : D = leafDepth x b)
    (hInv : BuildTopRecInv r x b D m d spaceBound root memPrep D tail mem) :
    (∀ y < buildTopPrepareTable r x + 13 * D, mem y = memPrep y) ∧
    ZeroFrom mem tail ∧
    buildTopPrepareHeap r x D ≤ tail ∧
    tail ≤ buildTopPrepareHeap r x D + D * (2 ^ x * spaceBound + 2 ^ x) ∧
    ∃ (reply : ℕ → ℕ → BuildLevelData) (replyAddr : ℕ → ℕ → ℕ),
      buildTopRepliesGood x b root reply (2 ^ x) (depthOf m) (49 * (x + 1) + 2)
        (x + 1) (x + 1) (buildTopBh x m d) ∧
      (∀ j < D, ∀ g < numGroups x b j,
        mem (buildTopScheduleReplies (buildTopPrepareTable r x) D x j + g) = replyAddr j g ∧
        buildTopPrepareHeap r x D ≤ replyAddr j g ∧
        replyAddr j g + ((reply j g).encode (branching x b j)).length ≤ tail ∧
        ListAt mem (replyAddr j g) ((reply j g).encode (branching x b j))) := by
  obtain ⟨hFrame, hZ, hHeapLo, hHeapHi, reply, replyAddr, _, _, hPrev, _, _, _, _, _⟩ := hInv
  refine ⟨hFrame, hZ, hHeapLo, hHeapHi, reply, replyAddr, ?_, ?_⟩
  · intro j g hj hg
    have hjlt : j < D := by
      rw [hD]
      have hjb : j * b < x := by
        by_contra hge
        have : groupSize x b j = 1 := by
          unfold groupSize; rw [Nat.min_eq_left (by omega), Nat.sub_self, pow_zero]
        omega
      have hle : x ≤ leafDepth x b * b := by
        unfold leafDepth
        have : (x + b - 1) / b * b + (x + b - 1) % b = x + b - 1 := by
          rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
        have hmod : (x + b - 1) % b < b := Nat.mod_lt _ hb
        omega
      exact Nat.lt_of_mul_lt_mul_right (lt_of_lt_of_le hjb hle)
    exact (hPrev j hjlt g hg).2.2.2.2
  · intro j hj g hg
    obtain ⟨h1, h2, h3, h4, _⟩ := hPrev j hj g hg
    exact ⟨h1, h2, h3, h4⟩

end MinCostFlow.HierPaths

end
