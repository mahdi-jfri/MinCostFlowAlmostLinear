module

public import MinCostFlow.LinkCut.PathProg.WrapUpdate
public import MinCostFlow.LinkCut.PathTree.NumCut
public import MinCostFlow.LinkCut.PathProg.NumFit

/-!
# The numbers of find-ready fit

Find-ready descends from a ready root, pushing the lazy flags of every node it visits, and then
exposes the node it stops at. This file shows that every number these steps compute fits in
`K` limbs (`findOk_of`).

The descent is handled by a general lemma (`descendOk_of`): if every push of a node of the tree
fits, and a push keeps this property, then the descent fits. It follows the proof of
`descend_spec`: the descent only enters a child whose summary is ready, so it never leaves the
tree. For the path payload the property is the bound `TreeB`, which a push keeps
(`pushDown_treeB`). The expose after the descent starts from the pushed state, which differs from
the original state only by pushes along the path to the node, so its numbers fit for the same
reasons as those of an expose of the original state.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.Path SplayState

variable {α σ τ : Type*}

/-- The descent from the root of a subtree fits, if every push of a node of `M` fits from a good
state and keeps the state good. -/
theorem descendOk_of {P : LctPayload α σ τ} (hL : P.Laws) {rs : σ → Bool} {rv : α → Bool}
    (hR : ReadyLaw P rs rv) {ok : PayloadOk α σ τ} {M : List ℕ}
    {Good : SplayState α σ τ → Prop}
    (hok : ∀ D, Good D → ∀ z ∈ M, PushDownOk ok P D z)
    (hgood : ∀ D, Good D → ∀ z ∈ M, Good (pushDown P D z)) :
    ∀ (c : AuxTree) (D : SplayState α σ τ) (rp k : ℕ), c ≠ .leaf → c.toList.Nodup →
      SubtreeInv P D rp c → rs (D.nodes c.rootId).sum = true → c.countNodes ≤ k →
      (∀ z ∈ c.toList, z ∈ M) → Good D → DescendOk ok P rs rv D k c.rootId
  | .leaf, _, _, _, hc, _, _, _, _, _, _ => absurd rfl hc
  | .node x l r, D, rp, k, _, hnd, hsub, hrs, hk, hM, hG => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp [AuxTree.countNodes] at hk; omega⟩
    rcases AuxTree.nodup_node_unfold hnd with ⟨hl_nd, hx_nl, hr_nd, hx_nr, hdisj⟩
    have hsum := hsub.2.2.2.2.2.2.1
    have hxM : x ∈ M := hM x (by simp [AuxTree.toList])
    rcases pushDown_root_preserves hL hnd hsub with ⟨hsub1, hrev1, htag1, -, hev1, -⟩
    set D1 := pushDown P D x with hD1
    have hG1 : Good D1 := hgood D hG x hxM
    set l' := if (D.nodes x).rev then l.revRoot else l with hl'
    set r' := if (D.nodes x).rev then r.revRoot else r with hr'
    have hpl : l'.toList.Perm l.toList := by
      rw [hl']; split_ifs
      · exact revRoot_toList_perm l
      · exact List.Perm.refl _
    have hpr : r'.toList.Perm r.toList := by
      rw [hr']; split_ifs
      · exact revRoot_toList_perm r
      · exact List.Perm.refl _
    have hcnt_l : l'.countNodes = l.countNodes := by
      rw [← AuxTree.length_toList, ← AuxTree.length_toList, hpl.length_eq]
    have hcnt_r : r'.countNodes = r.countNodes := by
      rw [← AuxTree.length_toList, ← AuxTree.length_toList, hpr.length_eq]
    obtain ⟨-, hleft1, hright1, -, -, -, -, hsl, hsr⟩ := hsub1
    have hev : evalPairs P D (.node x l r) false P.idTag =
        evalPairs P D1 l' false P.idTag ++ [(x, (D1.nodes x).val)] ++
          evalPairs P D1 r' false P.idTag := by
      rw [← hev1]
      simp [evalPairs, hrev1, htag1, hL.compTag_id_left, hL.actVal_id]
    have hM_l : ∀ z ∈ l'.toList, z ∈ M := fun z hz => hM z (by
      simp [AuxTree.toList, hpl.mem_iff.mp hz])
    have hM_r : ∀ z ∈ r'.toList, z ∈ M := fun z hz => hM z (by
      simp [AuxTree.toList, hpr.mem_iff.mp hz])
    have hsum_child : ∀ {c : AuxTree}, SubtreeInv P D1 x c → c ≠ .leaf →
        (D1.nodes c.rootId).sum = P.listSummary (evalPairs P D1 c false P.idTag) := by
      intro c hc hne
      cases c with
      | leaf => exact absurd rfl hne
      | node id a b => exact hc.2.2.2.2.2.2.1
    have hroot0 : ∀ {c : AuxTree}, SubtreeInv P D1 x c → (c.rootId = 0 ↔ c = .leaf) := by
      intro c hc
      cases c with
      | leaf => simp [AuxTree.rootId]
      | node id a b => simp [AuxTree.rootId, hc.1]
    have hk_l : l'.countNodes ≤ k := by simp [AuxTree.countNodes] at hk; omega
    have hk_r : r'.countNodes ≤ k := by simp [AuxTree.countNodes] at hk; omega
    have hnd_l : l'.toList.Nodup := hpl.nodup_iff.mpr hl_nd
    have hnd_r : r'.toList.Nodup := hpr.nodup_iff.mpr hr_nd
    have hdo : DescendOk ok P rs rv D (k + 1) x = (PushDownOk ok P D x ∧
        (if (D1.nodes x).left ≠ 0 ∧ rs (D1.nodes (D1.nodes x).left).sum = true then
          DescendOk ok P rs rv D1 k (D1.nodes x).left
        else if rv (D1.nodes x).val = true then True
        else DescendOk ok P rs rv D1 k (D1.nodes x).right)) := rfl
    simp only [AuxTree.rootId]
    rw [hdo, hleft1, hright1]
    refine ⟨hok D hG x hxM, ?_⟩
    split_ifs with hgl hgv
    · have hne : l' ≠ .leaf := fun h => hgl.1 ((hroot0 hsl).mpr h)
      exact descendOk_of hL hR hok hgood l' D1 x k hne hnd_l hsl hgl.2 hk_l hM_l hG1
    · have hready : ∃ p ∈ evalPairs P D1 r' false P.idTag, rv p.2 = true := by
        have h0 := (hR _).mp (hsum ▸ hrs)
        rw [hev] at h0
        obtain ⟨p, hp, hpv⟩ := h0
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with (hp | rfl) | hp
        · exfalso
          have hne : l' ≠ .leaf := by
            intro h; rw [h] at hp; simp [evalPairs] at hp
          apply hgl
          refine ⟨fun h => hne ((hroot0 hsl).mp h), ?_⟩
          rw [hsum_child hsl hne, hR]
          exact ⟨p, hp, hpv⟩
        · exact absurd hpv hgv
        · exact ⟨p, hp, hpv⟩
      have hne : r' ≠ .leaf := by
        intro h; rw [h] at hready; simp [evalPairs] at hready
      have hrs_r : rs (D1.nodes r'.rootId).sum = true := by
        rw [hsum_child hsr hne, hR]; exact hready
      exact descendOk_of hL hR hok hgood r' D1 x k hne hnd_r hsr hrs_r hk_r hM_r hG1

/-- A push of a node of a bounded tree keeps the bounds. -/
theorem pushDown_treeB {s : SplayState (Option PathEdgeValue) PathSummary PathTag} {t : AuxTree}
    {k : ℕ} {V R : ℤ} (hT : TreeB s t k V R) {x : ℕ} (hx : x ∈ t.toList) :
    TreeB (pushDown pathPayload s x) (pushDownTree s x t) k V R ∧
      (pushDownTree s x t).toList.Perm t.toList := by
  obtain ⟨hinv, hperm, -, -, hpath, -, -, -, -, -, -, hev⟩ :=
    pushDown_preserves_TreeInv pathPayload_laws hT.inv hx
  have hk : (pushDownTree s x t).countNodes ≤ k := by
    rw [countNodes_perm hperm]; exact hT.size
  refine ⟨⟨hinv, hev ▸ hT.val, fun y hy => ?_, hk⟩, hperm⟩
  have hy' := hperm.mem_iff.mp hy
  rw [charge_eq_route hinv hy hk]
  unfold route
  rw [hpath y]
  refine (pathTagRouteMagnitude_pushDown_le hT.inv.nodup hT.inv.sub hx hy').trans ?_
  have := hT.chg y hy'
  rwa [charge_eq_route hT.inv hy' hT.size] at this

/-- The numbers of find-ready fit, for every stack. -/
theorem findOk_of {s : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees free depth) (hF : FreeShape s free) {h L : ℕ}
    (hh : 0 < h) (hfits : pathTreeFits h L s) (hlog : Nat.log 2 (2 * s.n + 1) ≤ h * L) :
    ∀ R : List ℕ, FindOk (pathOk h (treeLimbs L)) pathPayload pathRs pathRv s R := by
  have C := numCtx_of_log (n := s.n) hh hlog
  have hB := forestB_of_fits W hfits
  intro R
  induction R with
  | nil => trivial
  | cons x R ih =>
    show (if ValidG pathRs s.n s.splay x then _ else _)
    split_ifs with hv
    swap
    · exact ih
    have hv' : ValidRoot s x := hv
    obtain ⟨t, ht, rfl⟩ := validRoot_root W hF hv'
    have hT := forestB_treeB W hB ht
    have hrs : pathRs (s.splay.nodes t.rootId).sum = true := hv'.2.2.2.1
    have hne := W.treesNonEmpty t ht
    have hcnt : t.countNodes ≤ 2 * s.n + 1 := by
      have := hT.size; omega
    refine ⟨?_, ?_⟩
    · refine descendOk_of pathPayload_laws pathReadyLaw (M := t.toList)
        (Good := fun D => ∃ t', TreeB D t' (2 * s.n + 1) (valBound h L s.n) (chgBound h L s.n) ∧
          ∀ z ∈ t.toList, z ∈ t'.toList) ?_ ?_ t s.splay 0 (2 * s.n + 1) hne hT.inv.nodup
        hT.inv.sub hrs hcnt (fun z h => h) ⟨t, hT, fun z h => h⟩
      · rintro D ⟨t', hT', hsub⟩ z hz
        exact pushDownOk_tree C hT' (hsub z hz)
      · rintro D ⟨t', hT', hsub⟩ z hz
        obtain ⟨hT'', hperm⟩ := pushDown_treeB hT' (hsub z hz)
        exact ⟨_, hT'', fun y hy => hperm.mem_iff.mpr (hsub y hy)⟩
    · -- The expose after the descent.
      set F := 2 * s.n + 1 with hFdef
      rcases hd : descend pathPayload pathRs pathRv s.splay F t.rootId with ⟨D', y⟩
      obtain ⟨hyt, -, -, hD', hsplay, hpp, -⟩ :=
        descend_root pathPayload_laws pathReadyLaw hT.inv hne hrs hcnt hd
      have hst : descState pathPayload pathRs pathRv s t.rootId = { s with splay := D' } := by
        unfold descState; rw [hd]
      have hnode : descNode pathPayload pathRs pathRv s t.rootId = y := by
        unfold descNode; rw [hd]
      rw [hst, hnode]
      have hya : y ∈ trees.flatMap AuxTree.toList := List.mem_flatMap.mpr ⟨t, ht, hyt⟩
      obtain ⟨hE1, hE2, hE3, hE4⟩ := (expose_num W hB C hya).1
      have hstart : exposeStart pathPayload { s with splay := D' } y = exposeStart pathPayload s y := by
        unfold exposeStart
        simp only
        rw [hsplay]
      refine ⟨fun hy0 => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · have hyd : t.depthOf y < F := by
          have := depthOf_lt_countNodes hyt; omega
        obtain ⟨t₁, hT₁, hperm₁, -⟩ := pushPath_treeB hT hyt hyd
        have hyd₁ : t₁.depthOf y < F := by
          have := depthOf_lt_countNodes (hperm₁.mem_iff.mpr hyt)
          have := countNodes_perm hperm₁
          omega
        show PushPathOk (pathOk h (treeLimbs L)) pathPayload D' F y
        rw [hD']
        exact pushPathOk_tree C hT₁ F y (hperm₁.mem_iff.mpr hyt) hyd₁
      · show SplayLoopOk (pathOk h (treeLimbs L)) pathPayload (pushPath pathPayload D' F y) F y
        rw [hpp, hD']
        exact (hE1 hy0).2
      · show DetachRightOk (pathOk h (treeLimbs L)) pathPayload (splay pathPayload D' F y) y
        rw [hsplay]; exact hE2
      · rw [hstart]; exact hE3
      · rw [hstart]; exact hE4

theorem treeLimbs_pos (L : ℕ) : 0 < treeLimbs L := by unfold treeLimbs; omega

theorem findLoop_n_fh (s : PathTreeState) :
    ∀ R : List ℕ, (findLoop pathPayload pathRs pathRv s R).1.n = s.n ∧
      (findLoop pathPayload pathRs pathRv s R).1.freeHead = s.freeHead
  | [] => ⟨rfl, rfl⟩
  | x :: R => by
    unfold findLoop
    split_ifs
    · exact ⟨by rw [lctExpose_n]; rfl, by rw [lctExpose_freeHead]; rfl⟩
    · exact findLoop_n_fh s R

section Width

variable {w h b0 : ℕ} {p : Program} (L : ℕ) (hh : 0 < h) (hw : 2 * h + 2 ≤ w)
  (hp : p.HasAt b0 (pathTreeBodies h b0))

/-- The run of the find-ready wrapper, on the stack `S` of the arena. -/
theorem findWrap_runs (ω : ℕ → Bool) {b heap pos : ℕ} {mem : ℕ → ℕ} {s : PathTreeState}
    {S : List ℕ} (hA : ArenaAt h L b s S mem) (hP : PtrOk (2 * s.n) s.splay)
    (hend : arenaEnd b s.n L ≤ heap) (hroom : heap + 1 + treeSpace L < 2 ^ w)
    (hz : ZeroFrom mem heap) (hn : 2 * s.n + 1 < 2 ^ w)
    (hok : FindOk (pathOk h (treeLimbs L)) pathPayload pathRs pathRv s S.reverse) :
    ∃ o st' c, Runs w p ω (findWrap b0) (startState [b, heap] mem pos) o st' c ∧
      (o.value = heap + 1 ∧
        ArenaAt h L b (findLoop pathPayload pathRs pathRv s S.reverse).1
          (findLoop pathPayload pathRs pathRv s S.reverse).2.1 st'.mem ∧
        OpFrame b s.n L heap (heap + 1) mem st'.mem ∧
        st'.mem heap = (findLoop pathPayload pathRs pathRv s S.reverse).2.2) ∧
      c ≤ findCost (stepsAt (treeLimbs L) hh hw hp)
        (testsAt (treeLimbs L) hh hw hp (treeLimbs_pos L)) s S.reverse + 60 := by
  have hK := treeLimbs_pos L
  have h16 := sixteen_le hh hw
  have hnb := nb_lt_end b s.n L
  have hb4 : b + 4 < 2 ^ w := by unfold arenaNb at hnb; omega
  have hbh : b + 8 ≤ heap := by unfold arenaNb at hnb; omega
  have hn1 := hA.hn
  have hn4 := hA.hnb
  have hz1 : ZeroFrom mem (heap + 1) := fun a ha => hz a (by omega)
  have hheap := heapOk_arena (h := h) (b := b) (n := s.n) (L := L) (by omega) (by omega) hz1 h16
  have hproc : p.procs[b0 + Ix.gfind]? = some (findReadyBody (b0 + Ix.gfind) (b0 + Ix.desc)
      (b0 + Ix.expose) (b0 + Ix.sumT) (b0 + Ix.pop)) := core_at hp 50 (by decide)
  obtain ⟨hfn, hffh⟩ := findLoop_n_fh s S.reverse
  apply runs_start_le
  unfold findWrap
  rw [startState]
  refine runs_seq_callBody_le (vs := [arenaNb b s.n, 2 * s.n + 1, heap + 1]) hproc
    (by eval_expr)
    (R := fun v' m₁ c₁ => (v' = (findLoop pathPayload pathRs pathRv s S.reverse).2.2 ∧
        ArenaAt h L b (findLoop pathPayload pathRs pathRv s S.reverse).1
          (findLoop pathPayload pathRs pathRv s S.reverse).2.1 m₁.mem ∧
        OpFrame b s.n L (heap + 1) (heap + 1) mem m₁.mem) ∧
      c₁ ≤ findCost (stepsAt (treeLimbs L) hh hw hp) (testsAt (treeLimbs L) hh hw hp hK) s S.reverse) ?_ ?_
  · have hI : IdxAt mem (arenaNb b s.n) (2 * s.n) S.reverse.reverse := by
      rw [List.reverse_reverse]; exact hA.idx
    obtain ⟨o, st', c, hr, ⟨hov, hnd, hfr, hI'⟩, hc⟩ :=
      findReadyBody_runs (findAt (treeLimbs L) hh hw hp hK) ω hP hn (nb_room b s.n) S.reverse pos hA.nodes
        hheap hI hok
    have hfh : st'.mem b = (findLoop pathPayload pathRs pathRv s S.reverse).1.freeHead := by
      rw [fh_frame (by omega) hfr.2, hA.fh, hffh]
    obtain ⟨hA', hout⟩ := arena_of_frame hA (by omega) hfn hnd hI' hfh
      fun a ha hr hi _ => hfr.2 a ha hr hi
    exact ⟨o, st', c, hr, ⟨hov, hA', hfr.1, hout⟩, by omega⟩
  rintro v' m₁ c₁ ⟨⟨hv', hA1, hF1⟩, hc₁⟩
  refine runs_seq_store_named_le (x := heap) (v := v') (by eval_expr) (by eval_expr)
    fun M₂ hM₂ => ?_
  simp only at hM₂
  wram_step
  · refine ⟨rfl, ?_, ⟨fun a ha => ?_, fun a ha hout => ?_⟩, ?_⟩
    · refine hA1.congr fun a h1 h2 => ?_
      rw [hfn] at h2
      dsimp only; simp only [hM₂, Function.update_apply]; rw [ite_eq_right (by omega)]
    · dsimp only; simp only [hM₂, Function.update_apply]; rw [ite_eq_right (by omega)]
      exact hF1.1 a ha
    · dsimp only; simp only [hM₂, Function.update_apply]; rw [ite_eq_right (by omega)]
      exact hF1.2 a (by omega) hout
    · simp [hM₂, hv']
  · simp only [hdr, fuelExpr, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
      argsSize_cons, argsSize_nil] at *
    omega

end Width

end MinCostFlow.LinkCut.PathProg
