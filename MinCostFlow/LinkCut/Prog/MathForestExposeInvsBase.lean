module

public import MinCostFlow.LinkCut.Prog.MathForestExposeSafe

/-!
# The expose invariant bundle under splay and detach

Defines `LctExposeInvs` and shows that it is kept by a splay (`LctExposeInvs.of_splay`) and by
the detach step of expose (`LctExposeInvs.of_detach`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section ExposeInvsDefs

/-- Full Word-RAM forest representation invariant preserved at every stage of `exposeBody` and
`lctRerootBody`. -/
structure LctExposeInvs (w h L P b n : ℕ) (freeEdges : List ℕ) (edgeMap : List (ℕ × ForestEdge))
    (trees : List AuxTree) (mem : ℕ → ℕ) : Prop where
  hdrN : mem (b + LCT_HDR_N) = n
  hdrCap : mem (b + LCT_HDR_CAP) = lctCap n
  hdrL : mem (b + LCT_HDR_L) = L
  hdrP : mem (b + LCT_HDR_P) = P
  sf : SplayForestOk w h L mem (lctNodesBase b) (lctCap n) trees
  freeChain : FreeSlotChain mem (lctNodesBase b) (mem (b + LCT_HDR_FREE)) freeEdges
  freeNodeOk : ∀ ed ∈ freeEdges, n + 1 ≤ ed ∧ ed ≤ lctCap n ∧
    AuxTree.node ed .leaf .leaf ∈ trees ∧
    nodeField mem (lctNodesBase b) ed OFF_PPAR = 0 ∧
    nodeField mem (lctNodesBase b) ed OFF_ISV = 0 ∧
    nodeField mem (lctNodesBase b) ed OFF_HASE = 0
  vertexOk : VertexNodeOk mem (lctNodesBase b) n
  edgeOk : ActiveEdgeNodeOk mem (lctNodesBase b) h L P n trees edgeMap
  auxPathOk : LctAuxPathOk mem (lctNodesBase b) n freeEdges trees
  subdivOk : LctSubdivOk mem (lctNodesBase b) n freeEdges edgeMap

theorem LctExposeInvs.ppar_le_cap {w h L P b n : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {trees : List AuxTree} {mem : ℕ → ℕ}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap trees mem) :
    ∀ s ∈ trees, nodeField mem (lctNodesBase b) s.rootId OFF_PPAR ≤ lctCap n := by
  intro s hs
  rcases (hi.auxPathOk s hs).2.1 with h0 | ⟨_, hle, _⟩
  · omega
  · exact hle

theorem freeSlotChain_agree_of_eu {mem₀ mem₁ : ℕ → ℕ} {nb : ℕ} {fs : List ℕ} {hd : ℕ}
    (hfree : FreeSlotChain mem₀ nb hd fs)
    (heu : ∀ ed ∈ fs, nodeField mem₁ nb ed OFF_EU = nodeField mem₀ nb ed OFF_EU) :
    FreeSlotChain mem₁ nb hd fs := by
  induction fs generalizing hd with
  | nil => simpa [FreeSlotChain] using hfree
  | cons a as ih =>
      rcases hfree with ⟨rfl, hrest⟩
      refine ⟨rfl, ?_⟩
      rw [heu _ (by simp)]
      exact ih hrest fun ed hed => heu ed (by simp [hed])

theorem lctSubdivOk_of_par_eq {mem₀ mem₁ : ℕ → ℕ} {nb n : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)}
    (hsub : LctSubdivOk mem₀ nb n freeEdges edgeMap)
    (hpar : ∀ u, lctAuxParent mem₁ nb (lctCap n) u = lctAuxParent mem₀ nb (lctCap n) u) :
    LctSubdivOk mem₁ nb n freeEdges edgeMap := by
  rcases hsub with ⟨h1, h2, h3, h4⟩
  have hiter : ∀ k q, iterParent (lctAuxParent mem₁ nb (lctCap n)) k q =
      iterParent (lctAuxParent mem₀ nb (lctCap n)) k q := by
    intro k; induction k with
    | zero => intro q; rfl
    | succ k ih => intro q; simp only [iterParent, hpar, ih]
  refine ⟨fun u hu1 hu2 => by rw [hiter]; exact h1 u hu1 hu2,
    fun ed hed => by simp only [hpar]; exact h2 ed hed,
    fun v hv => by simpa [hpar] using h3 v hv,
    fun p hp => by simpa [hpar] using h4 p hp⟩

end ExposeInvsDefs

section SplayPreservation

theorem lctAux_splay_pure {w h L : ℕ} {mem₀ mem₁ : ℕ → ℕ} {nb cap : ℕ}
    {trees₀ rest : List AuxTree} {t t' : AuxTree}
    (hok₀ : SplayForestOk w h L mem₀ nb cap trees₀)
    (ht_perm : trees₀.Perm (t :: rest))
    (hpp_le₀ : ∀ s ∈ trees₀, nodeField mem₀ nb s.rootId OFF_PPAR ≤ cap)
    (hok₁ : SplayForestOk w h L mem₁ nb cap (t' :: rest))
    (hev : t'.evalInorder (revFlag mem₁ nb) false = t.evalInorder (revFlag mem₀ nb) false)
    (hpp : nodeField mem₁ nb t'.rootId OFF_PPAR = nodeField mem₀ nb t.rootId OFF_PPAR)
    (hout : ∀ u ≤ cap, u ∉ t.toList → ∀ off < NODE_STRIDE,
      nodeField mem₁ nb u off = nodeField mem₀ nb u off) :
    (∀ s ∈ rest,
      nodeField mem₁ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₁ nb) false = s.evalInorder (revFlag mem₀ nb) false) ∧
    (∀ u, lctAuxParent mem₁ nb cap u = lctAuxParent mem₀ nb cap u) ∧
    (∀ z, lctRepSize mem₁ nb cap z = lctRepSize mem₀ nb cap z) ∧
    (∀ z, lctVSize mem₁ nb cap z = lctVSize mem₀ nb cap z) ∧
    lctHeavyCount mem₁ nb cap = lctHeavyCount mem₀ nb cap := by
  have hok₀' := splayForestOk_of_perm ht_perm hok₀
  have hnd_all₀ : ((t :: rest).flatMap AuxTree.toList).Nodup :=
    hok₀'.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  rw [List.flatMap_cons, List.nodup_append] at hnd_all₀
  have hrest_agree : ∀ s ∈ rest,
      nodeField mem₁ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₁ nb) false = s.evalInorder (revFlag mem₀ nb) false := by
    intro s hs
    have hdisj_s : ∀ u ∈ s.toList, u ≤ cap ∧ u ∉ t.toList := fun u hu => by
      have hb := (hok₀'.trees_ok s (by simp [hs])).2.2.nodup_perm_mem hu
      have hnin : u ∉ t.toList := fun hm =>
        hnd_all₀.2.2 u hm u (List.mem_flatMap.2 ⟨s, hs, hu⟩) rfl
      exact ⟨hb.2, hnin⟩
    refine ⟨?_, ?_⟩
    · have hs_ne := (hok₀'.trees_ok s (by simp [hs])).1
      have hm := AuxTree.rootId_mem_toList hs_ne
      exact hout s.rootId (hdisj_s _ hm).1 (hdisj_s _ hm).2 OFF_PPAR (by decide)
    · apply AuxTree.evalInorder_agree
      intro u hu
      have hd := hdisj_s u hu
      simp only [revFlag, hout u hd.1 hd.2 OFF_REV (by decide)]
  have hpp_le₀' : ∀ s ∈ t :: rest, nodeField mem₀ nb s.rootId OFF_PPAR ≤ cap :=
    fun s hs => hpp_le₀ s (ht_perm.symm.mem_iff.1 hs)
  have hpp_le₁ : ∀ s ∈ t' :: rest, nodeField mem₁ nb s.rootId OFF_PPAR ≤ cap := by
    intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs_rest
    · rw [hpp]; exact hpp_le₀' t (by simp)
    · rw [(hrest_agree s hs_rest).1]; exact hpp_le₀' s (by simp [hs_rest])
  have hpar_eq : ∀ u, lctAuxParent mem₁ nb cap u = lctAuxParent mem₀ nb cap u := by
    intro u
    rw [lctAuxParent_mem_iff_of_trees hok₁ hpp_le₁ u,
        lctAuxParent_mem_iff_of_trees hok₀' hpp_le₀' u]
    have htail_eq :
        rest.findSome? (fun s =>
          let seq := s.evalInorder (revFlag mem₁ nb) false
          if u ∈ seq then some (listParentFrom (nodeField mem₁ nb s.rootId OFF_PPAR) seq u) else none) =
        rest.findSome? (fun s =>
          let seq := s.evalInorder (revFlag mem₀ nb) false
          if u ∈ seq then some (listParentFrom (nodeField mem₀ nb s.rootId OFF_PPAR) seq u) else none) := by
      apply findSome?_congr_left
      intro s hs
      rcases hrest_agree s hs with ⟨hp_s, hev_s⟩
      simp only [hp_s, hev_s]
    by_cases hu : u ∈ t.evalInorder (revFlag mem₀ nb) false
    · have hu1 : u ∈ t'.evalInorder (revFlag mem₁ nb) false := by rw [hev]; exact hu
      rw [findSome?_cons_if hu1, findSome?_cons_if hu]
      simp only [hev, hpp]
    · have hu1 : u ∉ t'.evalInorder (revFlag mem₁ nb) false := by rw [hev]; exact hu
      rw [findSome?_cons_if_neg hu1, findSome?_cons_if_neg hu, htail_eq]
  have hrep_eq : ∀ z, lctRepSize mem₁ nb cap z = lctRepSize mem₀ nb cap z := by
    intro z
    simp only [lctRepSize]; congr 1; apply List.filter_congr; intro u _
    have hiter : ∀ k q, iterParent (lctAuxParent mem₁ nb cap) k q =
        iterParent (lctAuxParent mem₀ nb cap) k q := by
      intro k; induction k with
      | zero => intro q; rfl
      | succ k ih => intro q; simp only [iterParent, hpar_eq, ih]
    simp only [reachesIn, hiter]
  have hperm₀ := hok₀'.auxRootIds_perm
  have hperm₁ := hok₁.auxRootIds_perm
  have hdcs_t : dashedChildSize mem₁ nb cap t'.rootId = dashedChildSize mem₀ nb cap t.rootId := by
    have htree1 : lctTreeSeq mem₁ nb cap t'.rootId = t'.evalInorder (revFlag mem₁ nb) false :=
      hok₁.lctTreeSeq_eq (by simp)
    have htree0 : lctTreeSeq mem₀ nb cap t.rootId = t.evalInorder (revFlag mem₀ nb) false :=
      hok₀'.lctTreeSeq_eq (by simp)
    simp only [dashedChildSize, htree1, htree0, hev]
    cases t.evalInorder (revFlag mem₀ nb) false with
    | nil => rfl
    | cons hd tl => simp [hrep_eq]
  have hvs_eq : ∀ z, lctVSize mem₁ nb cap z = lctVSize mem₀ nb cap z := by
    intro z
    let contrib := fun mem q =>
      if nodeField mem nb q OFF_PPAR = z then dashedChildSize mem nb cap q else 0
    have hsf : ∀ mem (rs : List ℕ),
        ((rs.filter fun q => decide (nodeField mem nb q OFF_PPAR = z)).map
          fun q => dashedChildSize mem nb cap q).sum = (rs.map (contrib mem)).sum := fun mem rs => by
      simpa [contrib, decide_eq_true_eq] using
        list_filter_map_sum_ite rs (fun q => decide (nodeField mem nb q OFF_PPAR = z))
          (dashedChildSize mem nb cap)
    simp only [lctVSize, hsf]
    rw [(hperm₁.map (contrib mem₁)).sum_eq, (hperm₀.map (contrib mem₀)).sum_eq]
    have htail : (rest.map AuxTree.rootId).map (contrib mem₁) =
        (rest.map AuxTree.rootId).map (contrib mem₀) := by
      simp only [List.map_map]; apply List.map_congr_left; intro s hs
      rcases hrest_agree s hs with ⟨hp_s, hev_s⟩
      have hts : lctTreeSeq mem₁ nb cap s.rootId = lctTreeSeq mem₀ nb cap s.rootId := by
        rw [hok₁.lctTreeSeq_eq (by simp [hs]), hok₀'.lctTreeSeq_eq (by simp [hs]), hev_s]
      have hdcs : dashedChildSize mem₁ nb cap s.rootId = dashedChildSize mem₀ nb cap s.rootId := by
        simp only [dashedChildSize, hts]
        cases lctTreeSeq mem₀ nb cap s.rootId with
        | nil => rfl
        | cons hd _ => simp [hrep_eq]
      simp [contrib, hp_s, hdcs]
    have hhd : contrib mem₁ t'.rootId = contrib mem₀ t.rootId := by
      dsimp only [contrib]; rw [hpp, hdcs_t]
    simp only [List.map_cons, List.sum_cons, hhd, htail]
  have hheavy_eq : lctHeavyCount mem₁ nb cap = lctHeavyCount mem₀ nb cap := by
    let hflag := fun mem q => if isHeavyRoot mem nb cap q then 1 else 0
    have hsf : ∀ mem (rs : List ℕ),
        (rs.filter (fun q => isHeavyRoot mem nb cap q)).length = (rs.map (hflag mem)).sum :=
      fun mem rs => list_filter_length_ite rs (isHeavyRoot mem nb cap)
    simp only [lctHeavyCount, hsf]
    rw [(hperm₁.map (hflag mem₁)).sum_eq, (hperm₀.map (hflag mem₀)).sum_eq]
    have htail : (rest.map AuxTree.rootId).map (hflag mem₁) =
        (rest.map AuxTree.rootId).map (hflag mem₀) := by
      simp only [List.map_map]; apply List.map_congr_left; intro s hs
      rcases hrest_agree s hs with ⟨hp_s, hev_s⟩
      have hts : lctTreeSeq mem₁ nb cap s.rootId = lctTreeSeq mem₀ nb cap s.rootId := by
        rw [hok₁.lctTreeSeq_eq (by simp [hs]), hok₀'.lctTreeSeq_eq (by simp [hs]), hev_s]
      have hhs : isHeavyRoot mem₁ nb cap s.rootId = isHeavyRoot mem₀ nb cap s.rootId := by
        simp only [isHeavyRoot, hp_s, hts]
        cases lctTreeSeq mem₀ nb cap s.rootId with
        | nil => rfl
        | cons hd _ => simp [hrep_eq]
      simp only [Function.comp_def, hflag, hhs]
    have hhd_heavy : hflag mem₁ t'.rootId = hflag mem₀ t.rootId := by
      have hts1 : lctTreeSeq mem₁ nb cap t'.rootId = t'.evalInorder (revFlag mem₁ nb) false :=
        hok₁.lctTreeSeq_eq (by simp)
      have hts0 : lctTreeSeq mem₀ nb cap t.rootId = t.evalInorder (revFlag mem₀ nb) false :=
        hok₀'.lctTreeSeq_eq (by simp)
      have hhs : isHeavyRoot mem₁ nb cap t'.rootId = isHeavyRoot mem₀ nb cap t.rootId := by
        simp only [isHeavyRoot, hpp, hts1, hts0, hev]
        cases t.evalInorder (revFlag mem₀ nb) false with
        | nil => rfl
        | cons hd _ => simp [hrep_eq]
      simp only [hflag, hhs]
    simp only [List.map_cons, List.sum_cons, hhd_heavy, htail]
  exact ⟨hrest_agree, hpar_eq, hrep_eq, hvs_eq, hheavy_eq⟩

theorem LctExposeInvs.of_splay {w h L P b n : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {trees₀ rest : List AuxTree}
    {t t' : AuxTree} {mem₀ mem₁ : ℕ → ℕ}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap trees₀ mem₀)
    (ht_perm : trees₀.Perm (t :: rest))
    (hx_mem : t.rootId ∉ freeEdges)
    (hok₁ : SplayForestOk w h L mem₁ (lctNodesBase b) (lctCap n) (t' :: rest))
    (hev : t'.evalInorder (revFlag mem₁ (lctNodesBase b)) false =
      t.evalInorder (revFlag mem₀ (lctNodesBase b)) false)
    (hsteps : evalMemSteps mem₁ (lctNodesBase b) h L t' false 0 =
      evalMemSteps mem₀ (lctNodesBase b) h L t false 0)
    (ht_perm_nodes : t'.toList.Perm t.toList)
    (hpp : nodeField mem₁ (lctNodesBase b) t'.rootId OFF_PPAR =
      nodeField mem₀ (lctNodesBase b) t.rootId OFF_PPAR)
    (hout : ∀ u ≤ lctCap n, u ∉ t.toList → ∀ off < NODE_STRIDE,
      nodeField mem₁ (lctNodesBase b) u off = nodeField mem₀ (lctNodesBase b) u off)
    (hstat : ∀ u ≤ lctCap n, ∀ off, IsStaticPayloadOff off →
      nodeField mem₁ (lctNodesBase b) u off = nodeField mem₀ (lctNodesBase b) u off)
    (hfr : LctFrame (lctNodesBase b + NODE_STRIDE)
      (lctNodesBase b + NODE_STRIDE * (lctCap n + 1)) (lctNodesBase b - 1) mem₀ mem₁) :
    LctExposeInvs w h L P b n freeEdges edgeMap (t' :: rest) mem₁ ∧
    (∀ u, lctAuxParent mem₁ (lctNodesBase b) (lctCap n) u =
      lctAuxParent mem₀ (lctNodesBase b) (lctCap n) u) ∧
    (∀ z, lctRepSize mem₁ (lctNodesBase b) (lctCap n) z =
      lctRepSize mem₀ (lctNodesBase b) (lctCap n) z) ∧
    (∀ z, lctVSize mem₁ (lctNodesBase b) (lctCap n) z =
      lctVSize mem₀ (lctNodesBase b) (lctCap n) z) ∧
    lctHeavyCount mem₁ (lctNodesBase b) (lctCap n) =
      lctHeavyCount mem₀ (lctNodesBase b) (lctCap n) := by
  let nb := lctNodesBase b
  let cap := lctCap n
  have hhdr := lctFrame_hdr_eq hfr
  rcases lctAux_splay_pure hi.sf ht_perm hi.ppar_le_cap hok₁ hev hpp hout with
    ⟨hrest_agree, hpar_eq, hrep_eq, hvs_eq, hheavy_eq⟩
  have hok₀' := splayForestOk_of_perm ht_perm hi.sf
  have hnd_all₀ : ((t :: rest).flatMap AuxTree.toList).Nodup :=
    hok₀'.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  rw [List.flatMap_cons, List.nodup_append] at hnd_all₀
  have hfree_not_t : ∀ ed ∈ freeEdges, ed ∉ t.toList := fun ed hed hmem => by
    rcases hi.freeNodeOk ed hed with ⟨_, _, htree, _, _, _⟩
    have hts : (AuxTree.node ed .leaf .leaf) ∈ t :: rest := ht_perm.mem_iff.1 htree
    simp only [List.mem_cons] at hts
    rcases hts with heq | hrest
    · exact absurd (congrArg AuxTree.rootId heq.symm ▸ hed) hx_mem
    · exact hnd_all₀.2.2 ed hmem ed (List.mem_flatMap.2 ⟨_, hrest, by simp [AuxTree.toList]⟩) rfl
  have hfreeChain₁ : FreeSlotChain mem₁ nb (mem₁ (b + LCT_HDR_FREE)) freeEdges := by
    rw [hhdr.2.2.1]
    exact freeSlotChain_agree_of_eu hi.freeChain fun ed hed =>
      hstat ed (hi.freeNodeOk ed hed).2.1 OFF_EU (by simp [IsStaticPayloadOff])
  have hfreeNode₁ : ∀ ed ∈ freeEdges, n + 1 ≤ ed ∧ ed ≤ cap ∧
      AuxTree.node ed .leaf .leaf ∈ t' :: rest ∧
      nodeField mem₁ nb ed OFF_PPAR = 0 ∧
      nodeField mem₁ nb ed OFF_ISV = 0 ∧
      nodeField mem₁ nb ed OFF_HASE = 0 := by
    intro ed hed
    rcases hi.freeNodeOk ed hed with ⟨h1, h2, htr, hpp_ed, hisv, hhe⟩
    have htr_rest : AuxTree.node ed .leaf .leaf ∈ rest := by
      have hmem := ht_perm.mem_iff.1 htr
      simp only [List.mem_cons] at hmem
      rcases hmem with heq | hrest
      · exact absurd (congrArg AuxTree.rootId heq.symm ▸ hed) hx_mem
      · exact hrest
    have hnin := hfree_not_t ed hed
    refine ⟨h1, h2, List.mem_cons_of_mem _ htr_rest, ?_, ?_, ?_⟩
    · rw [hout ed h2 hnin OFF_PPAR (by decide)]; exact hpp_ed
    · rw [hstat ed h2 OFF_ISV (by simp [IsStaticPayloadOff])]; exact hisv
    · rw [hstat ed h2 OFF_HASE (by simp [IsStaticPayloadOff])]; exact hhe
  have hvert₁ : VertexNodeOk mem₁ nb n := by
    intro v hv
    have hcap_def : lctCap n = 2 * n := rfl
    have hv_le : v + 1 ≤ cap := by dsimp only [cap]; omega
    refine ⟨?_, ?_⟩
    · rw [hstat (v + 1) hv_le OFF_ISV (by simp [IsStaticPayloadOff])]; exact (hi.vertexOk v hv).1
    · rw [hstat (v + 1) hv_le OFF_HASE (by simp [IsStaticPayloadOff])]; exact (hi.vertexOk v hv).2
  have hheap : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nb - 1) → mem₁ a = mem₀ a :=
    fun a ha1 ha2 => hfr.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩)
  have hedge₁ : ActiveEdgeNodeOk mem₁ nb h L P n (t' :: rest) edgeMap := by
    intro p hp
    rcases hi.edgeOk p hp with ⟨h1, h2, hisv, hhe, heid, heu, hev_f, s_old, hs_old_mem,
      hed_in, st_old, hst_mem, hmatch, hdir_ok⟩
    have hs_old_perm := ht_perm.mem_iff.1 hs_old_mem
    refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hstat p.1 h2 OFF_ISV (by simp [IsStaticPayloadOff])]; exact hisv
    · rw [hstat p.1 h2 OFF_HASE (by simp [IsStaticPayloadOff])]; exact hhe
    · rw [hstat p.1 h2 OFF_EID (by simp [IsStaticPayloadOff])]; exact heid
    · rw [hstat p.1 h2 OFF_EU (by simp [IsStaticPayloadOff])]; exact heu
    · rw [hstat p.1 h2 OFF_EV (by simp [IsStaticPayloadOff])]; exact hev_f
    · simp only [List.mem_cons] at hs_old_perm
      rcases hs_old_perm with rfl | hs_rest
      · refine ⟨t', by simp, ht_perm_nodes.symm.mem_iff.1 hed_in, st_old, ?_, hmatch, ?_⟩
        · rw [hsteps]; exact hst_mem
        · simpa [nb, cap, hpar_eq] using hdir_ok
      · have hs_rest_ok : s_old ∈ rest := hs_rest
        have hs_nd := list_nodup_of_flatMap_nodup hnd_all₀.2.1 hs_rest_ok
        have hdisj : ∀ u ∈ s_old.toList, u ≤ cap ∧ u ∉ t.toList := fun u hu =>
          ⟨(hok₀'.trees_ok s_old (by simp [hs_rest_ok])).2.2.nodup_perm_mem hu |>.2,
            fun hm => hnd_all₀.2.2 u hm u (List.mem_flatMap.2 ⟨s_old, hs_rest_ok, hu⟩) rfl⟩
        have hsteps_rest : evalMemSteps mem₁ nb h L s_old false 0 =
            evalMemSteps mem₀ nb h L s_old false 0 := by
          apply evalMemSteps_agree_of_nonStruct (hok₀'.trees_ok s_old (by simp [hs_rest_ok])).2.2 hs_nd
          · intro u hu off hoff _
            have hd := hdisj u hu
            exact hout u hd.1 hd.2 off hoff
          · exact hheap
        refine ⟨s_old, List.mem_cons_of_mem _ hs_rest_ok, hed_in, st_old, ?_, hmatch, ?_⟩
        · rw [hsteps_rest]; exact hst_mem
        · simpa [nb, cap, hpar_eq] using hdir_ok
  have haux₁ : LctAuxPathOk mem₁ nb n freeEdges (t' :: rest) := by
    intro s hs
    simp only [List.mem_cons] at hs
    rcases hs with rfl | hs_rest
    · have h0 := hi.auxPathOk t (ht_perm.symm.mem_iff.1 (by simp))
      dsimp only at h0 ⊢
      rw [hev, hpp]
      rcases h0 with ⟨hne, hpp_ok, (⟨hed, _, _⟩ | ⟨v, hv, hlast⟩)⟩
      · exact absurd hed hx_mem
      · exact ⟨hne, hpp_ok, Or.inr ⟨v, hv, hlast⟩⟩
    · have h0 := hi.auxPathOk s (ht_perm.symm.mem_iff.1 (by simp [hs_rest]))
      rcases hrest_agree s hs_rest with ⟨hp_s, hev_s⟩
      dsimp only at h0 ⊢
      rw [hp_s, hev_s]
      exact h0
  have hsub₁ := lctSubdivOk_of_par_eq hi.subdivOk hpar_eq
  refine ⟨⟨hhdr.1.trans hi.hdrN, hhdr.2.1.trans hi.hdrCap, hhdr.2.2.2.1.trans hi.hdrL,
    hhdr.2.2.2.2.trans hi.hdrP, hok₁, hfreeChain₁, hfreeNode₁, hvert₁, hedge₁, haux₁, hsub₁⟩,
    hpar_eq, hrep_eq, hvs_eq, hheavy_eq⟩

end SplayPreservation

section DetachAndSplicePreservation

theorem LctExposeInvs.of_detach {w h L P b n v : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {l r : AuxTree} {rest : List AuxTree}
    {mem₀ mem₁ : ℕ → ℕ}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (.node (v + 1) l r :: rest) mem₀)
    (hv : v < n)
    (hrev0 : nodeField mem₀ (lctNodesBase b) (v + 1) OFF_REV = 0)
    (hht0 : nodeField mem₀ (lctNodesBase b) (v + 1) OFF_HAS_TAG = 0)
    (hhp₁ : mem₁ (lctNodesBase b - 1) < 2 ^ w)
    (hpp : nodeField mem₁ (lctNodesBase b) (v + 1) OFF_PPAR =
      nodeField mem₀ (lctNodesBase b) (v + 1) OFF_PPAR)
    (htree_x : TreeMemMatch w h L mem₁ (lctNodesBase b) (lctCap n) (.node (v + 1) l .leaf) 0
      (nodeField mem₁ (lctNodesBase b) (v + 1) OFF_PPAR))
    (hl_fields : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
      nodeField mem₁ (lctNodesBase b) u off = nodeField mem₀ (lctNodesBase b) u off)
    (hnonAgg_x : ∀ off < NODE_STRIDE,
      off ≠ OFF_VCNT → off ≠ OFF_CSUM_FWD → off ≠ OFF_CSUM_BWD →
      off ≠ OFF_MIN1_HAS → off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN1_FIRST → off ≠ OFF_MIN1_LAST →
      off ≠ OFF_MIN2_HAS → off ≠ OFF_MIN2_VAL → off ≠ OFF_MIN2_FIRST → off ≠ OFF_MIN2_LAST →
      off ≠ OFF_RIGHT →
      nodeField mem₁ (lctNodesBase b) (v + 1) off = nodeField mem₀ (lctNodesBase b) (v + 1) off)
    (hl : ∀ u ≤ lctCap n, u ∉ (AuxTree.node (v + 1) l .leaf).toList → ∀ off < NODE_STRIDE,
      (r ≠ .leaf → u = r.rootId → off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR) →
      nodeField mem₁ (lctNodesBase b) u off = nodeField mem₀ (lctNodesBase b) u off)
    (hr_par : r ≠ .leaf → nodeField mem₁ (lctNodesBase b) r.rootId OFF_PARENT = 0)
    (hr_pp : r ≠ .leaf → nodeField mem₁ (lctNodesBase b) r.rootId OFF_PPAR = v + 1)
    (hfr : LctFrame (lctNodesBase b + NODE_STRIDE)
      (lctNodesBase b + NODE_STRIDE * (lctCap n + 1)) (lctNodesBase b - 1) mem₀ mem₁) :
    let x := v + 1
    let nb := lctNodesBase b
    let cap := lctCap n
    let trees₁ := if r = .leaf then .node x l .leaf :: rest else .node x l .leaf :: r :: rest
    LctExposeInvs w h L P b n freeEdges edgeMap trees₁ mem₁ ∧
    (∀ u, lctAuxParent mem₁ nb cap u = lctAuxParent mem₀ nb cap u) ∧
    (∀ z, lctRepSize mem₁ nb cap z = lctRepSize mem₀ nb cap z) ∧
    (∀ y, lctVSize mem₁ nb cap y =
      if y = x then lctVSize mem₀ nb cap x + (if r = .leaf then 0 else r.treeSize (lctVSize mem₀ nb cap))
      else lctVSize mem₀ nb cap y) ∧
    splayMemPhi (K_SPLAY_STEP L) mem₁ nb cap (lctVSize mem₁ nb cap) =
      splayMemPhi (K_SPLAY_STEP L) mem₀ nb cap (lctVSize mem₀ nb cap) ∧
    lctHeavyCount mem₁ nb cap ≤ lctHeavyCount mem₀ nb cap +
      (if r = .leaf then 0 else 1) ∧
    (AuxTree.node x l .leaf).treeSize (lctVSize mem₁ nb cap) =
      (AuxTree.node x l r).treeSize (lctVSize mem₀ nb cap) := by
  intro x nb cap trees₁
  have hsf_rep : SplayForestOk w h L mem₁ nb cap trees₁ ∧
      (∀ s ∈ rest, nodeField mem₁ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
        s.evalInorder (revFlag mem₁ nb) false = s.evalInorder (revFlag mem₀ nb) false) ∧
      (∀ rc rl rr, r = .node rc rl rr →
        nodeField mem₁ nb rc OFF_PPAR = x ∧
        r.evalInorder (revFlag mem₁ nb) false = r.evalInorder (revFlag mem₀ nb) false) := by
    cases r with
    | leaf =>
        rcases splayForestOk_reparent_detach hi.sf hhp₁ hpp htree_x hl hr_par hr_pp hfr with
          ⟨hsf1, hra, _⟩
        exact ⟨by simpa [trees₁] using hsf1, hra, fun _ _ _ h => by cases h⟩
    | node rc rl rr =>
        rcases splayForestOk_reparent_detach hi.sf hhp₁ hpp htree_x hl hr_par hr_pp hfr with
          ⟨hsf1, hra, hrg⟩
        exact ⟨by simpa [trees₁] using hsf1, hra, by rintro _ _ _ ⟨rfl⟩; exact hrg⟩
  rcases hsf_rep with ⟨hsf₁, hrest_agree, hr_agree⟩
  have hhdr := lctFrame_hdr_eq hfr
  have hnd_all₀ : ((AuxTree.node x l r :: rest).flatMap AuxTree.toList).Nodup :=
    hi.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  rw [List.flatMap_cons, List.nodup_append] at hnd_all₀
  have hx_nd₀ := hnd_all₀.1
  have hx_tok := hi.sf.trees_ok (.node x l r) (by simp [x])
  have hrev1 : nodeField mem₁ nb x OFF_REV = 0 := by
    rw [hnonAgg_x OFF_REV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hrev0
  have hht1 : nodeField mem₁ nb x OFF_HAS_TAG = 0 := by
    rw [hnonAgg_x OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hht0
  have hx_eval : (AuxTree.node x l .leaf).evalInorder (revFlag mem₁ nb) false =
      l.evalInorder (revFlag mem₀ nb) false ++ [x] := by
    have hrev_x1 : revFlag mem₁ nb x = false := by simp [revFlag, nb, x, hrev1]
    have hl_eq : l.evalInorder (revFlag mem₁ nb) false = l.evalInorder (revFlag mem₀ nb) false := by
      apply AuxTree.evalInorder_agree
      intro u hu; simp only [revFlag, nb, hl_fields u hu OFF_REV (by decide)]
    simp only [AuxTree.evalInorder, hrev_x1, hl_eq, List.append_nil]
  have hpp_le₀ : nodeField mem₀ nb x OFF_PPAR ≤ cap ∧
      ∀ s ∈ rest, nodeField mem₀ nb s.rootId OFF_PPAR ≤ cap :=
    ⟨hi.ppar_le_cap (.node x l r) (by simp [x]), fun s hs => hi.ppar_le_cap s (by simp [hs])⟩
  have hpure : (∀ u, lctAuxParent mem₁ nb cap u = lctAuxParent mem₀ nb cap u) ∧
      (∀ z, lctRepSize mem₁ nb cap z = lctRepSize mem₀ nb cap z) ∧
      (∀ y, lctVSize mem₁ nb cap y =
        if y = x then lctVSize mem₀ nb cap x + (if r = .leaf then 0 else r.treeSize (lctVSize mem₀ nb cap))
        else lctVSize mem₀ nb cap y) ∧
      splayMemPhi (K_SPLAY_STEP L) mem₁ nb cap (lctVSize mem₁ nb cap) =
        splayMemPhi (K_SPLAY_STEP L) mem₀ nb cap (lctVSize mem₀ nb cap) ∧
      lctHeavyCount mem₁ nb cap ≤ lctHeavyCount mem₀ nb cap + (if r = .leaf then 0 else 1) := by
    cases r with
    | leaf =>
        have hsf1 : SplayForestOk w h L mem₁ nb cap (.node x l .leaf :: rest) := by
          simpa [trees₁] using hsf₁
        have he := lctAux_detach_pure hi.sf hi.subdivOk.1 hpp_le₀ hrev0 hsf1 hrest_agree hpp hx_eval trivial
        exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, by
          have h := he.2.2.2.2
          dsimp only [nb, cap] at h ⊢
          simp only [↓reduceIte]
          exact Nat.le_of_eq (by simpa using h)⟩
    | node rc rl rr =>
        have hsf1 : SplayForestOk w h L mem₁ nb cap (.node x l .leaf :: .node rc rl rr :: rest) := by
          simpa [trees₁] using hsf₁
        have he := lctAux_detach_pure hi.sf hi.subdivOk.1 hpp_le₀ hrev0 hsf1 hrest_agree hpp hx_eval
          (hr_agree rc rl rr rfl)
        exact ⟨he.1, he.2.1, he.2.2.1, he.2.2.2.1, by
          have h := he.2.2.2.2
          have hnot : (AuxTree.node rc rl rr = AuxTree.leaf) = False := by simp
          dsimp only [nb, cap] at h ⊢
          simp only [hnot, ↓reduceIte]
          have h' : lctHeavyCount mem₁ (lctNodesBase b) (lctCap n) =
              lctHeavyCount mem₀ (lctNodesBase b) (lctCap n) +
                (if isHeavyRoot mem₁ (lctNodesBase b) (lctCap n) rc = true then 1 else 0) := by
            simpa using h
          split_ifs at h' <;> omega⟩
  rcases hpure with ⟨hpar_eq, hrep_eq, hvs_eq, hphi_eq, hheavy_le⟩
  have hx_nin_free : x ∉ freeEdges := fun hxm => by
    have := (hi.freeNodeOk x hxm).1; omega
  have hfree_not_x : ∀ ed ∈ freeEdges, ed ∉ (AuxTree.node x l r).toList := fun ed hed hmem => by
    rcases hi.freeNodeOk ed hed with ⟨_, _, htr, _, _, _⟩
    simp only [List.mem_cons] at htr
    rcases htr with h_eq | hrest
    · have hed_eq : ed = v + 1 := by injection h_eq
      dsimp only [x] at hx_nin_free; exact hx_nin_free (hed_eq ▸ hed)
    · exact hnd_all₀.2.2 ed hmem ed (List.mem_flatMap.2 ⟨_, hrest, by simp [AuxTree.toList]⟩) rfl
  have hfreeChain₁ : FreeSlotChain mem₁ nb (mem₁ (b + LCT_HDR_FREE)) freeEdges := by
    rw [hhdr.2.2.1]
    exact freeSlotChain_agree_of_eu hi.freeChain fun ed hed => by
      have he_ok := hi.freeNodeOk ed hed
      have hnin_xl : ed ∉ (AuxTree.node x l .leaf).toList := fun hm =>
        hfree_not_x ed hed (by
          simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hm ⊢
          rcases hm with (hl' | rfl) | hleaf
          · exact Or.inl (Or.inl hl')
          · exact Or.inl (Or.inr rfl)
          · simp at hleaf)
      have hne_r : r ≠ .leaf → ed ≠ r.rootId := fun hr heq => by
        rw [heq] at hed
        exact hfree_not_x r.rootId hed (by simp [AuxTree.toList, AuxTree.rootId_mem_toList hr])
      exact hl ed he_ok.2.1 hnin_xl OFF_EU (by decide) (fun hr heq => absurd heq (hne_r hr))
  have hfreeNode₁ : ∀ ed ∈ freeEdges, n + 1 ≤ ed ∧ ed ≤ cap ∧
      AuxTree.node ed .leaf .leaf ∈ trees₁ ∧
      nodeField mem₁ nb ed OFF_PPAR = 0 ∧
      nodeField mem₁ nb ed OFF_ISV = 0 ∧
      nodeField mem₁ nb ed OFF_HASE = 0 := by
    intro ed hed
    rcases hi.freeNodeOk ed hed with ⟨h1, h2, htr, hpp_ed, hisv, hhe⟩
    have htr_rest : AuxTree.node ed .leaf .leaf ∈ rest := by
      simp only [List.mem_cons] at htr
      rcases htr with heq | hrest
      · have hed_eq : ed = v + 1 := by injection heq
        dsimp only [x] at hx_nin_free; exact absurd (hed_eq ▸ hed) hx_nin_free
      · exact hrest
    have htr₁ : AuxTree.node ed .leaf .leaf ∈ trees₁ := by cases r <;> simp [trees₁, htr_rest]
    have hnin_xl : ed ∉ (AuxTree.node x l .leaf).toList := fun hm =>
      hfree_not_x ed hed (by
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hm ⊢
        rcases hm with (hl' | rfl) | hleaf
        · exact Or.inl (Or.inl hl')
        · exact Or.inl (Or.inr rfl)
        · simp at hleaf)
    have hne_r : r ≠ .leaf → ed ≠ r.rootId := fun hr heq => by
      rw [heq] at hed
      exact hfree_not_x r.rootId hed (by simp [AuxTree.toList, AuxTree.rootId_mem_toList hr])
    refine ⟨h1, h2, htr₁, ?_, ?_, ?_⟩
    · rw [hl ed h2 hnin_xl OFF_PPAR (by decide) (fun hr heq => absurd heq (hne_r hr))]; exact hpp_ed
    · rw [hl ed h2 hnin_xl OFF_ISV (by decide) (fun hr heq => absurd heq (hne_r hr))]; exact hisv
    · rw [hl ed h2 hnin_xl OFF_HASE (by decide) (fun hr heq => absurd heq (hne_r hr))]; exact hhe
  have hheap : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nb - 1) → mem₁ a = mem₀ a :=
    fun a ha1 ha2 => hfr.2.2.2.2.2 a (Or.inr ⟨ha1, ha2⟩)
  have hvert₁ : VertexNodeOk mem₁ nb n := by
    intro u hu
    have hcap_def : lctCap n = 2 * n := rfl
    have hu_le : u + 1 ≤ cap := by dsimp only [cap]; omega
    have hof : ∀ off, (off = OFF_ISV ∨ off = OFF_HASE) →
        nodeField mem₁ nb (u + 1) off = nodeField mem₀ nb (u + 1) off := by
      intro off hoff
      by_cases hux : u + 1 = x
      · rw [hux]
        rcases hoff with rfl | rfl <;>
          exact hnonAgg_x _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · by_cases hu_l : u + 1 ∈ l.toList
        · rcases hoff with rfl | rfl <;> exact hl_fields _ hu_l _ (by decide)
        · have hnin : u + 1 ∉ (AuxTree.node x l .leaf).toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton]
            rintro ((h | h) | h) <;> simp_all
          exact hl (u + 1) hu_le hnin off (by rcases hoff with rfl | rfl <;> decide)
            (fun _ _ => by rcases hoff with rfl | rfl <;> exact ⟨by decide, by decide⟩)
    exact ⟨by rw [hof OFF_ISV (Or.inl rfl)]; exact (hi.vertexOk u hu).1,
      by rw [hof OFF_HASE (Or.inr rfl)]; exact (hi.vertexOk u hu).2⟩
  have hl_steps : evalMemSteps mem₁ nb h L l false 0 = evalMemSteps mem₀ nb h L l false 0 :=
    evalMemSteps_agree_of_nonStruct hx_tok.2.2.children_match.1 (auxTree_nodup_left hx_nd₀)
      (fun u hu off hoff _ => hl_fields u hu off hoff) hheap false 0
  have hown_x : nodeOwnRawStep mem₁ nb h L x = nodeOwnRawStep mem₀ nb h L x :=
    nodeOwnRawStep_agree_of_nonAgg hx_tok.2.2 (fun off hlt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 _ _ =>
      hnonAgg_x off hlt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12) hheap
  have hr_steps : evalMemSteps mem₁ nb h L r false 0 = evalMemSteps mem₀ nb h L r false 0 := by
    have hdisj_xl_r : ∀ a ∈ (AuxTree.node x l .leaf).toList, ∀ b ∈ r.toList, a ≠ b := by
      intro a ha b hb
      have hx_nd' := hx_nd₀
      rw [AuxTree.toList, List.nodup_append] at hx_nd'
      exact hx_nd'.2.2 a (by simpa [AuxTree.toList] using ha) b hb
    exact evalMemSteps_agree_of_nonStruct hx_tok.2.2.children_match.2 (auxTree_nodup_right hx_nd₀)
      (fun u hu off hoff hne => hl u (hx_tok.2.2.children_match.2.nodup_perm_mem hu).2
        (fun hm => hdisj_xl_r u hm u hu rfl) off hoff (fun _ h => hne h))
      hheap false 0
  have hsplit₀ : evalMemSteps mem₀ nb h L (.node x l r) false 0 =
      evalMemSteps mem₀ nb h L l false 0 ++
        ((nodeOwnRawStep mem₀ nb h L x).map (fun s => s.addDeltaMod h L 0)).toList ++
        evalMemSteps mem₀ nb h L r false 0 :=
    evalMemSteps_split_of_root_zero (by simp [nb, x, revFlag, hrev0]) hht0
  have hsplit₁ : evalMemSteps mem₁ nb h L (.node x l .leaf) false 0 =
      evalMemSteps mem₀ nb h L l false 0 ++
        ((nodeOwnRawStep mem₀ nb h L x).map (fun s => s.addDeltaMod h L 0)).toList := by
    rw [evalMemSteps_split_of_root_zero (by simp [revFlag, hrev1]) hht1, hl_steps, hown_x]
    simp [evalMemSteps]
  have hedge₁ : ActiveEdgeNodeOk mem₁ nb h L P n trees₁ edgeMap := by
    intro q hq
    rcases hi.edgeOk q hq with ⟨h1, h2, hisv, hhe, heid, heu, hev_f, s_old, hs_old_mem,
      hed_in, st_old, hst_mem, hmatch, hdir_ok⟩
    have hst_id : st_old.nodeId = q.1 := hmatch.1
    have hq_fields : ∀ off, (off = OFF_ISV ∨ off = OFF_HASE ∨ off = OFF_EID ∨
        off = OFF_EU ∨ off = OFF_EV) →
        nodeField mem₁ nb q.1 off = nodeField mem₀ nb q.1 off := by
      intro off hoff
      by_cases hqx : q.1 = x
      · rw [hqx]
        rcases hoff with rfl | rfl | rfl | rfl | rfl <;>
          exact hnonAgg_x _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      · by_cases hql : q.1 ∈ l.toList
        · rcases hoff with rfl | rfl | rfl | rfl | rfl <;> exact hl_fields _ hql _ (by decide)
        · have hnin : q.1 ∉ (AuxTree.node x l .leaf).toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton]
            rintro ((h | h) | h)
            · exact hql h
            · exact hqx h
            · simp at h
          exact hl q.1 h2 hnin off (by rcases hoff with rfl | rfl | rfl | rfl | rfl <;> decide)
            (fun _ _ => by rcases hoff with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
    refine ⟨h1, h2,
      by rw [hq_fields OFF_ISV (Or.inl rfl)]; exact hisv,
      by rw [hq_fields OFF_HASE (Or.inr (Or.inl rfl))]; exact hhe,
      by rw [hq_fields OFF_EID (Or.inr (Or.inr (Or.inl rfl)))]; exact heid,
      by rw [hq_fields OFF_EU (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact heu,
      by rw [hq_fields OFF_EV (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact hev_f, ?_⟩
    simp only [List.mem_cons] at hs_old_mem
    rcases hs_old_mem with rfl | hs_rest
    · rw [hsplit₀, List.mem_append] at hst_mem
      rcases hst_mem with hsl_x | hsr
      · have hsl_1 : st_old ∈ evalMemSteps mem₁ nb h L (.node x l .leaf) false 0 := by
          rw [hsplit₁]; exact hsl_x
        have hmem_t1 : AuxTree.node x l .leaf ∈ trees₁ := by cases r <;> simp [trees₁]
        refine ⟨.node x l .leaf, hmem_t1, hst_id ▸ evalMemSteps_nodeId_mem_toList hsl_1, st_old,
          hsl_1, hmatch, by simpa [nb, cap, hpar_eq] using hdir_ok⟩
      · cases hr_eq : r with
        | leaf => subst hr_eq; simp [evalMemSteps] at hsr
        | node rc rl rr =>
            have hsr' : st_old ∈ evalMemSteps mem₀ nb h L (AuxTree.node rc rl rr) false 0 := by
              rw [hr_eq] at hsr; exact hsr
            have hed_in_r : q.1 ∈ (AuxTree.node rc rl rr).toList :=
              hst_id ▸ evalMemSteps_nodeId_mem_toList hsr'
            have hmem_t1 : AuxTree.node rc rl rr ∈ trees₁ := by simp [trees₁, hr_eq]
            refine ⟨.node rc rl rr, hmem_t1, hed_in_r, st_old, ?_, hmatch, ?_⟩
            · rw [← hr_eq, hr_steps]; exact hsr
            · simpa [nb, cap, hpar_eq] using hdir_ok
    · have hdisj_s : ∀ u ∈ s_old.toList, u ≤ cap ∧ u ∉ (AuxTree.node x l r).toList := fun u hu =>
        ⟨(hi.sf.trees_ok s_old (by simp [hs_rest])).2.2.nodup_perm_mem hu |>.2,
         fun hm => hnd_all₀.2.2 u hm u (List.mem_flatMap.2 ⟨s_old, hs_rest, hu⟩) rfl⟩
      have hs_nd := list_nodup_of_flatMap_nodup hnd_all₀.2.1 hs_rest
      have hsteps_rest : evalMemSteps mem₁ nb h L s_old false 0 =
          evalMemSteps mem₀ nb h L s_old false 0 := by
        apply evalMemSteps_agree_of_nonStruct (hi.sf.trees_ok s_old (by simp [hs_rest])).2.2 hs_nd
        · intro u hu off hoff _
          have hd := hdisj_s u hu
          have hnr : r ≠ .leaf → u ≠ r.rootId := fun hr heq => by
            rw [heq] at hd
            exact hd.2 (by simp [AuxTree.toList, AuxTree.rootId_mem_toList hr])
          have hnx : u ∉ (AuxTree.node x l .leaf).toList := fun hm => hd.2 (by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hm ⊢
            rcases hm with (hl' | rfl) | hleaf
            · exact Or.inl (Or.inl hl')
            · exact Or.inl (Or.inr rfl)
            · simp at hleaf)
          exact hl u hd.1 hnx off hoff (fun hr heq => absurd heq (hnr hr))
        · exact hheap
      have hmem_t1 : s_old ∈ trees₁ := by cases r <;> simp [trees₁, hs_rest]
      refine ⟨s_old, hmem_t1, hed_in, st_old, ?_, hmatch, ?_⟩
      · rw [hsteps_rest]; exact hst_mem
      · simpa [nb, cap, hpar_eq] using hdir_ok
  have haux₁ : LctAuxPathOk mem₁ nb n freeEdges trees₁ := by
    have hok_xl : let seq := (AuxTree.node x l .leaf).evalInorder (revFlag mem₁ nb) false
        let pp_x := nodeField mem₁ nb x OFF_PPAR
        seq ≠ [] ∧ (pp_x = 0 ∨ (1 ≤ pp_x ∧ pp_x ≤ cap ∧ pp_x ∉ freeEdges)) ∧
        ((x ∈ freeEdges ∧ AuxTree.node x l .leaf = .node x .leaf .leaf ∧ pp_x = 0) ∨
          (∃ u, u < n ∧ seq.getLast? = some (u + 1))) := by
      have h0 := hi.auxPathOk (.node x l r) (by simp [x])
      dsimp only at h0 ⊢
      rw [hx_eval, hpp]
      exact ⟨by simp, h0.2.1, Or.inr ⟨v, hv, by simp [x]⟩⟩
    cases hr_eq : r with
    | leaf =>
        intro s hs
        simp only [trees₁, hr_eq, ↓reduceIte, List.mem_cons] at hs
        rcases hs with rfl | hs_rest
        · exact hok_xl
        · have h0 := hi.auxPathOk s (by simp [hs_rest])
          rcases hrest_agree s hs_rest with ⟨hp_s, hev_s⟩
          dsimp only at h0 ⊢; rw [hp_s, hev_s]; exact h0
    | node rc rl rr =>
        intro s hs
        have hnot : (AuxTree.node rc rl rr = AuxTree.leaf) = False := by simp
        simp only [trees₁, hr_eq, hnot, ↓reduceIte, List.mem_cons] at hs
        rcases hs with rfl | rfl | hs_rest
        · exact hok_xl
        · have h0 := hi.auxPathOk (.node x l r) (by simp [x])
          have hrev_x0 : revFlag mem₀ nb x = false := by simp [revFlag, nb, x, hrev0]
          have hseq0 : (AuxTree.node x l (.node rc rl rr)).evalInorder (revFlag mem₀ nb) false =
              (l.evalInorder (revFlag mem₀ nb) false ++ [x]) ++
              (AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false := by
            simp [AuxTree.evalInorder, hrev_x0]
          have hr_ne : AuxTree.node rc rl rr ≠ .leaf := by simp
          have hseq_r_ne : (AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false ≠ [] :=
            auxTree_eval_ne_nil_of_ne_leaf hr_ne
          have hlast_eq : ((AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false).getLast? =
              ((AuxTree.node x l (.node rc rl rr)).evalInorder (revFlag mem₀ nb) false).getLast? := by
            rw [hseq0, List.getLast?_append_of_ne_nil _ hseq_r_ne]
          have hcap_def : lctCap n = 2 * n := rfl
          have hx_le : x ≤ cap := by dsimp only [x, cap]; omega
          have hrg := hr_agree rc rl rr hr_eq
          rw [hr_eq] at h0 hrg
          dsimp only at h0 ⊢
          simp only [auxTree_rootId_node]
          rw [hrg.1, hrg.2]
          refine ⟨by simpa [hr_eq] using hseq_r_ne, Or.inr ⟨by omega, hx_le, hx_nin_free⟩, ?_⟩
          rcases h0.2.2 with ⟨hx_in, _⟩ | ⟨u, hu, hlast⟩
          · exact absurd hx_in hx_nin_free
          · exact Or.inr ⟨u, hu, hlast_eq.trans (by simpa [hr_eq] using hlast)⟩
        · have h0 := hi.auxPathOk s (by simp [hs_rest])
          rcases hrest_agree s hs_rest with ⟨hp_s, hev_s⟩
          dsimp only at h0 ⊢; rw [hp_s, hev_s]; exact h0
  have hsub₁ := lctSubdivOk_of_par_eq hi.subdivOk hpar_eq
  have htop_sz : (AuxTree.node x l .leaf).treeSize (lctVSize mem₁ nb cap) =
      (AuxTree.node x l r).treeSize (lctVSize mem₀ nb cap) := by
    have hl_sz : l.treeSize (lctVSize mem₁ nb cap) = l.treeSize (lctVSize mem₀ nb cap) := by
      rw [AuxTree.treeSize_eq_sum, AuxTree.treeSize_eq_sum]
      congr 1; apply List.map_congr_left
      intro u hu
      have hux : u ≠ x := fun h => auxTree_nodup_id_nin_left hx_nd₀ (h ▸ hu)
      simp only [hvs_eq u, hux, ↓reduceIte]
    cases r with
    | leaf => simp [AuxTree.treeSize, hl_sz, hvs_eq x]
    | node rc rl rr =>
        simp [AuxTree.treeSize, hl_sz, hvs_eq x]; omega
  refine ⟨⟨hhdr.1.trans hi.hdrN, hhdr.2.1.trans hi.hdrCap, hhdr.2.2.2.1.trans hi.hdrL,
    hhdr.2.2.2.2.trans hi.hdrP, hsf₁, hfreeChain₁, hfreeNode₁, hvert₁, hedge₁, haux₁, hsub₁⟩,
    hpar_eq, hrep_eq, hvs_eq, hphi_eq, hheavy_le, htop_sz⟩

end DetachAndSplicePreservation
end MinCostFlow.LinkCut.Prog
end
