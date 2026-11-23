module

public import MinCostFlow.LinkCut.Prog.MathForestBasic

/-!
# Expose and reroot bodies, and pure structural helpers

Defines `exposePhase1DetachStmt`, `exposeIterSpliceStmt`, `exposeBody`, `lctRerootBody` and
their costs, and the first pure lemmas about parents and splices of auxiliary trees.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section ExposeAndRerootDefs

/-- Conservative amortized coefficient for `exposeBody`: `140000 * (L + 1) * (log(n+2) + 1)`. -/
def C_EXPOSE_OP (L : ℕ) : ℕ :=
  140000 * (L + 1)

/-- Phase 1 post-splay block of `expose`: detaches `right[x]` if nonzero (`parent[rc] := 0`,
`ppar[rc] := x`, `right[x] := 0`, `pull(nb, x)`) and initializes `reg 5 := x`, `reg 6 := ppar[x]`.
Expects `reg 0 = nb`, `reg 1 = x` (`x ≠ 0`). -/
def exposePhase1DetachStmt (sp : SplayProcs) : Stmt :=
  Stmt.assign 2 (nodePtrExpr 0 1) ;;
  Stmt.assign 3 (fieldLoadExpr 2 OFF_RIGHT) ;;
  Stmt.cond (.reg 3)
    (Stmt.assign 4 (nodePtrExpr 0 3) ;;
     Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.const 0) ;;
     Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.reg 1) ;;
     Stmt.store (fieldAddrExpr 2 OFF_RIGHT) (.const 0) ;;
     Stmt.call 10 sp.pull [.reg 0, .reg 1])
    Stmt.nop ;;
  Stmt.assign 5 (.reg 1) ;;
  Stmt.assign 6 (fieldLoadExpr 2 OFF_PPAR)

/-- Loop-body splice block executed after `splay(nb, pp)`: detaches `right[pp]` if nonzero,
attaches `y` (`reg 5`) as `right[pp]`, calls `pull(nb, pp)`, and advances `y := pp`,
`pp := ppar[pp]`. Expects `reg 0 = nb`, `reg 1 = x`, `reg 5 = y`, `reg 6 = pp` (`pp ≠ 0`). -/
def exposeIterSpliceStmt (sp : SplayProcs) : Stmt :=
  Stmt.assign 7 (nodePtrExpr 0 6) ;;
  Stmt.assign 3 (fieldLoadExpr 7 OFF_RIGHT) ;;
  Stmt.cond (.reg 3)
    (Stmt.assign 4 (nodePtrExpr 0 3) ;;
     Stmt.store (fieldAddrExpr 4 OFF_PARENT) (.const 0) ;;
     Stmt.store (fieldAddrExpr 4 OFF_PPAR) (.reg 6))
    Stmt.nop ;;
  Stmt.store (fieldAddrExpr 7 OFF_RIGHT) (.reg 5) ;;
  Stmt.assign 8 (nodePtrExpr 0 5) ;;
  Stmt.store (fieldAddrExpr 8 OFF_PARENT) (.reg 6) ;;
  Stmt.store (fieldAddrExpr 8 OFF_PPAR) (.const 0) ;;
  Stmt.call 10 sp.pull [.reg 0, .reg 6] ;;
  Stmt.assign 5 (.reg 6) ;;
  Stmt.assign 6 (fieldLoadExpr 7 OFF_PPAR)

/-- `expose(nb, x)`: exposes the path from `x` (`v + 1`) to the component root into a single
preferred splay tree rooted at `x` (`OFF_RIGHT = 0`, `OFF_PPAR = 0`, `OFF_REV = 0`) and returns `x`. -/
def exposeBody (sp : SplayProcs) : Stmt :=
  Stmt.cond (.reg 1)
    (Stmt.call 10 sp.splay [.reg 0, .reg 1] ;;
     exposePhase1DetachStmt sp ;;
     Stmt.loop (.reg 6)
       (Stmt.call 10 sp.splay [.reg 0, .reg 6] ;;
        exposeIterSpliceStmt sp) ;;
     Stmt.call 10 sp.splay [.reg 0, .reg 1] ;;
     Stmt.ret (.reg 1))
    (Stmt.ret (.const 0))

/-- `reroot(nb, x)`: exposes `x` and flips its lazy reversal bit via `sp.revNode`, making `x`
the component root in `lctAuxParent` (`OFF_PPAR = 0`, `head? = some x`). -/
def lctRerootBody (lp : LctProcs) : Stmt :=
  Stmt.call 2 lp.expose [.reg 0, .reg 1] ;;
  Stmt.call 2 lp.splay.revNode [.reg 0, .reg 1] ;;
  Stmt.ret (.const 0)

theorem exposeBody_noRand (sp : SplayProcs) : (exposeBody sp).NoRand := by
  simp [exposeBody, exposePhase1DetachStmt, exposeIterSpliceStmt, nodePtrExpr, fieldLoadExpr,
    fieldAddrExpr, Stmt.NoRand]

theorem lctRerootBody_noRand (lp : LctProcs) : (lctRerootBody lp).NoRand := by
  simp [lctRerootBody, Stmt.NoRand]

end ExposeAndRerootDefs

section PureStructuralHelpers

theorem auxTree_nodup_left {id : ℕ} {l r : AuxTree}
    (h : (AuxTree.node id l r).toList.Nodup) : l.toList.Nodup := by
  simp only [AuxTree.toList, List.nodup_append, List.nodup_cons] at h
  exact h.1.1

theorem auxTree_nodup_right {id : ℕ} {l r : AuxTree}
    (h : (AuxTree.node id l r).toList.Nodup) : r.toList.Nodup := by
  simp only [AuxTree.toList, List.nodup_append, List.nodup_cons] at h
  exact h.2.1

theorem auxTree_nodup_id_nin_left {id : ℕ} {l r : AuxTree}
    (h : (AuxTree.node id l r).toList.Nodup) : id ∉ l.toList := by
  simp only [AuxTree.toList, List.nodup_append, List.nodup_cons] at h
  intro hm; exact h.1.2.2 id hm id (List.mem_singleton.2 rfl) rfl

theorem auxTree_nodup_id_nin_right {id : ℕ} {l r : AuxTree}
    (h : (AuxTree.node id l r).toList.Nodup) : id ∉ r.toList := by
  simp only [AuxTree.toList, List.nodup_append, List.nodup_cons] at h
  intro hm; exact h.2.2 id (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))) id hm rfl

theorem auxTree_eval_ne_nil_of_ne_leaf {rev : ℕ → Bool} {t : AuxTree} (hne : t ≠ .leaf) :
    t.evalInorder rev false ≠ [] := by
  cases t with
  | leaf => exact absurd rfl hne
  | node id l r =>
      cases rev id <;> simp [AuxTree.evalInorder]

theorem auxTree_treePhi_congr {v₁ v₂ : ℕ → ℕ} {t : AuxTree}
    (h : ∀ u ∈ t.toList, v₁ u = v₂ u) : t.treePhi v₁ = t.treePhi v₂ := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
      have hl : l.treePhi v₁ = l.treePhi v₂ :=
        ihl fun u hu => h u (by simp [AuxTree.toList, hu])
      have hr : r.treePhi v₁ = r.treePhi v₂ :=
        ihr fun u hu => h u (by simp [AuxTree.toList, hu])
      have hid : v₁ id = v₂ id := h id (by simp [AuxTree.toList])
      have hsz : (AuxTree.node id l r).treeSize v₁ = (AuxTree.node id l r).treeSize v₂ := by
        rw [AuxTree.treeSize_eq_sum, AuxTree.treeSize_eq_sum]
        congr 1; exact List.map_congr_left fun u hu => congrArg (1 + ·) (h u hu)
      simp only [AuxTree.treePhi, AuxTree.rank, hsz, hl, hr]

theorem nat_log2_two_mul_le {a b : ℕ} (ha : 1 ≤ a) (hle : 2 * a ≤ b) :
    Nat.log 2 a + 1 ≤ Nat.log 2 b := by
  have hpow : 2 ^ (Nat.log 2 a + 1) ≤ b := by
    rw [Nat.pow_succ, Nat.mul_comm]
    exact le_trans (Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))) hle
  exact Nat.le_log_of_pow_le (by decide) hpow

theorem list_sum_two_mem_le {α : Type*} {L : List α} (hnd : L.Nodup) (f : α → ℕ)
    {a b : α} (ha : a ∈ L) (hb : b ∈ L) (hne : a ≠ b) :
    f a + f b ≤ (L.map f).sum := by
  induction L with
  | nil => simp at ha
  | cons hd tl ih =>
      rw [List.nodup_cons] at hnd
      simp only [List.mem_cons] at ha hb
      simp only [List.map_cons, List.sum_cons]
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hne
      · have hle : f b ≤ (tl.map f).sum :=
          List.le_sum_of_mem (List.mem_map.2 ⟨b, hb, rfl⟩)
        omega
      · have hle : f a ≤ (tl.map f).sum :=
          List.le_sum_of_mem (List.mem_map.2 ⟨a, ha, rfl⟩)
        omega
      · have := ih hnd.2 ha hb; omega

private theorem findSome?_eq_at_unique {α β : Type*} {L : List α} {f : α → Option β} {a : α}
    (ha : a ∈ L) (hfa : f a ≠ none)
    (huniq : ∀ a₁ ∈ L, ∀ a₂ ∈ L, a₁ ≠ a₂ → f a₁ ≠ none → f a₂ ≠ none → False) :
    L.findSome? f = f a := by
  induction L with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with hxa | ha_xs
      · cases hfx : f x with
        | none => exact absurd (by simpa [hxa] using hfx) hfa
        | some b => simp [List.findSome?, hfx, hxa]
      · by_cases hxa : x = a
        · cases hfx : f x with
          | none => exact absurd (by simpa [hxa] using hfx) hfa
          | some b => simp [List.findSome?, ← hxa, hfx]
        · cases hfx : f x with
          | none =>
              simp only [List.findSome?, hfx]
              exact ih ha_xs fun u hu v hv huv hfu hfv =>
                huniq u (by simp [hu]) v (by simp [hv]) huv hfu hfv
          | some b =>
              exfalso
              exact huniq x (by simp) a (by simp [ha_xs]) hxa (by simp [hfx]) hfa

private theorem findSome?_eq_of_perm_unique {α β : Type*} {L₁ L₂ : List α} {f : α → Option β}
    (hp : L₁.Perm L₂) (hex : ∃ a ∈ L₁, f a ≠ none)
    (huniq : ∀ a₁ ∈ L₁, ∀ a₂ ∈ L₁, a₁ ≠ a₂ → f a₁ ≠ none → f a₂ ≠ none → False) :
    L₁.findSome? f = L₂.findSome? f := by
  rcases hex with ⟨a, ha, hfa⟩
  have hL1 := findSome?_eq_at_unique ha hfa huniq
  have huniq2 : ∀ a₁ ∈ L₂, ∀ a₂ ∈ L₂, a₁ ≠ a₂ → f a₁ ≠ none → f a₂ ≠ none → False :=
    fun a₁ h1 a₂ h2 => huniq a₁ (hp.symm.mem_iff.1 h1) a₂ (hp.symm.mem_iff.1 h2)
  have hL2 := findSome?_eq_at_unique (hp.mem_iff.1 ha) hfa huniq2
  exact hL1.trans hL2.symm

theorem findSome?_congr_left {α β : Type*} {L : List α} {f₁ f₂ : α → Option β}
    (h : ∀ x ∈ L, f₁ x = f₂ x) : L.findSome? f₁ = L.findSome? f₂ := by
  induction L with
  | nil => rfl
  | cons a as ih =>
      simp only [List.findSome?, h a (by simp)]
      cases f₂ a with
      | none => exact ih fun x hx => h x (by simp [hx])
      | some _ => rfl

theorem findSome?_map_rootId {ts : List AuxTree} {g : ℕ → Option ℕ} :
    (ts.map AuxTree.rootId).findSome? g = ts.findSome? (fun s => g s.rootId) := by
  induction ts with
  | nil => rfl
  | cons s ss ih =>
      simp only [List.map_cons, List.findSome?]
      cases g s.rootId <;> [exact ih; rfl]

theorem findSome?_cons_if {mem : ℕ → ℕ} {nb u : ℕ} {t : AuxTree} {rest : List AuxTree}
    (ht : u ∈ t.evalInorder (revFlag mem nb) false) :
    ((t :: rest).findSome? fun s =>
      let seq := s.evalInorder (revFlag mem nb) false
      if u ∈ seq then some (listParentFrom (nodeField mem nb s.rootId OFF_PPAR) seq u) else none) =
    some (listParentFrom (nodeField mem nb t.rootId OFF_PPAR) (t.evalInorder (revFlag mem nb) false) u) := by
  simp only [List.findSome?, ht, ↓reduceIte]

theorem findSome?_cons_if_neg {mem : ℕ → ℕ} {nb u : ℕ} {t : AuxTree} {rest : List AuxTree}
    (ht : u ∉ t.evalInorder (revFlag mem nb) false) :
    ((t :: rest).findSome? fun s =>
      let seq := s.evalInorder (revFlag mem nb) false
      if u ∈ seq then some (listParentFrom (nodeField mem nb s.rootId OFF_PPAR) seq u) else none) =
    (rest.findSome? fun s =>
      let seq := s.evalInorder (revFlag mem nb) false
      if u ∈ seq then some (listParentFrom (nodeField mem nb s.rootId OFF_PPAR) seq u) else none) := by
  simp only [List.findSome?, ht, ↓reduceIte]

theorem auxTree_rootId_node (id : ℕ) (l r : AuxTree) :
    (AuxTree.node id l r).rootId = id := rfl

theorem list_filter_map_sum_ite {α : Type*} (L : List α) (p : α → Bool) (f : α → ℕ) :
    ((L.filter p).map f).sum = (L.map fun r => if p r = true then f r else 0).sum := by
  induction L with
  | nil => rfl
  | cons a as ih =>
      cases h : p a <;> simp [h, ih]

theorem list_filter_length_ite {α : Type*} (L : List α) (p : α → Bool) :
    (L.filter p).length = (L.map fun r => if p r then 1 else 0).sum := by
  induction L with
  | nil => rfl
  | cons a as ih =>
      cases h : p a <;> simp [h, ih, Nat.add_comm]

theorem list_nodup_of_flatMap_nodup {ts : List AuxTree}
    (hnd : (ts.flatMap AuxTree.toList).Nodup) {t : AuxTree} (ht : t ∈ ts) :
    t.toList.Nodup := by
  induction ts with
  | nil => simp at ht
  | cons a as ih =>
      rw [List.flatMap_cons, List.nodup_append] at hnd
      rcases List.mem_cons.1 ht with rfl | ht'
      · exact hnd.1
      · exact ih hnd.2.1 ht'

theorem listParentFrom_append_eq {prev last u : ℕ} {xs ys : List ℕ}
    (hlast : xs.getLast? = some last) (hdisj : ∀ a ∈ xs, ∀ b ∈ ys, a ≠ b) :
    listParentFrom prev (xs ++ ys) u =
      if u ∈ xs then listParentFrom prev xs u else listParentFrom last ys u := by
  induction xs generalizing prev with
  | nil => simp at hlast
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp only [Option.some.injEq, List.getLast?_singleton] at hlast
          subst last
          simp only [List.cons_append, List.nil_append, listParentFrom, List.mem_singleton]
          split_ifs with hu <;> rfl
      | cons x' xs' =>
          have hlast' : (x' :: xs').getLast? = some last := by
            simpa [List.getLast?_cons_cons] using hlast
          have hdisj' : ∀ a ∈ x' :: xs', ∀ b ∈ ys, a ≠ b := fun a ha b hb =>
            hdisj a (by simp [ha]) b hb
          have hx_not_ys : ∀ b ∈ ys, x ≠ b := fun b hb => hdisj x (by simp) b hb
          simp only [List.cons_append, listParentFrom]
          by_cases hux : u = x
          · subst hux
            simp [List.mem_cons]
          · simp only [hux, ↓reduceIte, List.mem_cons, false_or]
            simpa only [List.cons_append, listParentFrom, List.mem_cons] using ih hlast' hdisj' (prev := x)

private theorem lct_trees_disjoint_of_flatMap_nodup {trees : List AuxTree}
    (hnd : (trees.flatMap AuxTree.toList).Nodup) :
    ∀ {s₁ s₂ : AuxTree}, s₁ ∈ trees → s₂ ∈ trees → s₁ ≠ s₂ →
      ∀ u ∈ s₁.toList, u ∉ s₂.toList := by
  induction trees with
  | nil => intro s₁ s₂ h; simp at h
  | cons a as ih =>
      rw [List.flatMap_cons, List.nodup_append] at hnd
      rcases hnd with ⟨_, has_nd, hdisj⟩
      intro s₁ s₂ hs₁ hs₂ hne u hu₁ hu₂
      simp only [List.mem_cons] at hs₁ hs₂
      rcases hs₁ with rfl | hs₁' <;> rcases hs₂ with rfl | hs₂'
      · exact hne rfl
      · exact hdisj u hu₁ u (List.mem_flatMap.2 ⟨s₂, hs₂', hu₂⟩) rfl
      · exact hdisj u hu₂ u (List.mem_flatMap.2 ⟨s₁, hs₁', hu₁⟩) rfl
      · exact ih has_nd hs₁' hs₂' hne u hu₁ hu₂

/-- `SplayForestOk` is invariant under permutations of the tree list `trees`. -/
theorem splayForestOk_of_perm {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {trees₁ trees₂ : List AuxTree} (hp : trees₁.Perm trees₂)
    (hok : SplayForestOk w h L mem nb cap trees₁) :
    SplayForestOk w h L mem nb cap trees₂ := by
  rcases hok with ⟨h1, h2, h3, h4, h5, h6, h7, h8, hperm, htok⟩
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, fun t ht => htok t (hp.mem_iff.2 ht)⟩
  exact (hp.symm.flatMap (fun _ _ => List.Perm.refl _)).trans hperm

/-- `LctAuxPathOk` is invariant under permutations of the tree list `trees`. -/
theorem lctAuxPathOk_of_perm {mem : ℕ → ℕ} {nb n : ℕ} {freeEdges : List ℕ}
    {trees₁ trees₂ : List AuxTree} (hp : trees₁.Perm trees₂)
    (hax : LctAuxPathOk mem nb n freeEdges trees₁) :
    LctAuxPathOk mem nb n freeEdges trees₂ :=
  fun t ht => hax t (hp.mem_iff.2 ht)

/-- Direct formula for `lctAuxParent` as a `findSome?` over `trees`. -/
theorem lctAuxParent_mem_iff_of_trees {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {trees : List AuxTree} (hok : SplayForestOk w h L mem nb cap trees)
    (hpp_le : ∀ s ∈ trees, nodeField mem nb s.rootId OFF_PPAR ≤ cap)
    (u : ℕ) :
    lctAuxParent mem nb cap u =
      match trees.findSome? (fun s =>
          let seq := s.evalInorder (revFlag mem nb) false
          if u ∈ seq then some (listParentFrom (nodeField mem nb s.rootId OFF_PPAR) seq u) else none) with
      | some p => p
      | none => 0 := by
  let g := fun r => treeParentEntry mem nb cap r u
  have hroot_perm : (auxRootIds mem nb cap).Perm (trees.map AuxTree.rootId) :=
    hok.auxRootIds_perm
  have hnd_all : (trees.flatMap AuxTree.toList).Nodup :=
    hok.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hdisj_seqs : ∀ s₁ s₂, s₁ ∈ trees → s₂ ∈ trees → s₁ ≠ s₂ →
      u ∈ s₁.evalInorder (revFlag mem nb) false →
      u ∈ s₂.evalInorder (revFlag mem nb) false → False := by
    intro s₁ s₂ hs₁ hs₂ hne hu₁ hu₂
    have hm₁ := (s₁.evalInorder_perm (revFlag mem nb) false).mem_iff.1 hu₁
    have hm₂ := (s₂.evalInorder_perm (revFlag mem nb) false).mem_iff.1 hu₂
    exact lct_trees_disjoint_of_flatMap_nodup hnd_all hs₁ hs₂ hne u hm₁ hm₂
  have hfind_perm : (auxRootIds mem nb cap).findSome? g =
      (trees.map AuxTree.rootId).findSome? g := by
    by_cases hex : ∃ a ∈ auxRootIds mem nb cap, g a ≠ none
    · apply findSome?_eq_of_perm_unique hroot_perm hex
      intro r₁ hr₁ r₂ hr₂ hr_ne h1 h2
      rcases List.mem_map.1 (hroot_perm.mem_iff.1 hr₁) with ⟨s₁, hs₁, rfl⟩
      rcases List.mem_map.1 (hroot_perm.mem_iff.1 hr₂) with ⟨s₂, hs₂, rfl⟩
      simp only [g, treeParentEntry, hok.lctTreeSeq_eq hs₁, hok.lctTreeSeq_eq hs₂] at h1 h2
      by_cases hu₁ : u ∈ s₁.evalInorder (revFlag mem nb) false
      · by_cases hu₂ : u ∈ s₂.evalInorder (revFlag mem nb) false
        · exact hdisj_seqs s₁ s₂ hs₁ hs₂ (fun h => hr_ne (congrArg AuxTree.rootId h)) hu₁ hu₂
        · simp [hu₂] at h2
      · simp [hu₁] at h1
    · have h1_none : (auxRootIds mem nb cap).findSome? g = none := by
        rw [List.findSome?_eq_none_iff]
        intro a ha
        by_contra hne
        exact hex ⟨a, ha, hne⟩
      have h2_none : (trees.map AuxTree.rootId).findSome? g = none := by
        rw [List.findSome?_eq_none_iff]
        intro a ha
        by_contra hne
        exact hex ⟨a, hroot_perm.symm.mem_iff.1 ha, hne⟩
      exact h1_none.trans h2_none.symm
  have hmap_find : (trees.map AuxTree.rootId).findSome? g =
      trees.findSome? (fun s => g s.rootId) :=
    findSome?_map_rootId
  have htree_find : trees.findSome? (fun s => g s.rootId) =
      trees.findSome? (fun s =>
        let seq := s.evalInorder (revFlag mem nb) false
        if u ∈ seq then some (listParentFrom (nodeField mem nb s.rootId OFF_PPAR) seq u) else none) := by
    apply findSome?_congr_left
    intro s hs
    simp only [g, treeParentEntry, hok.lctTreeSeq_eq hs, hpp_le s hs, ↓reduceIte]
  rw [lctAuxParent, hfind_perm, hmap_find, htree_find]
  rfl

/-- In an acyclic forest, `ppar[t.rootId]` cannot belong to `t.toList`. -/
theorem lct_cycleFree_ppar_notin {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ} {trees : List AuxTree}
    (hok : SplayForestOk w h L mem nb cap trees)
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent (lctAuxParent mem nb cap) cap u = 0)
    (hpp_le : ∀ s ∈ trees, nodeField mem nb s.rootId OFF_PPAR ≤ cap)
    {t : AuxTree} (ht : t ∈ trees) :
    nodeField mem nb t.rootId OFF_PPAR ∉ t.toList := by
  intro hpp_mem
  let seq := t.evalInorder (revFlag mem nb) false
  let par := lctAuxParent mem nb cap
  have hpp_seq : nodeField mem nb t.rootId OFF_PPAR ∈ seq :=
    (t.evalInorder_perm (revFlag mem nb) false).symm.mem_iff.1 hpp_mem
  have hseq_eq : lctTreeSeq mem nb cap t.rootId = seq := hok.lctTreeSeq_eq ht
  rcases List.getElem_of_mem hpp_seq with ⟨idx, hidx, hidx_eq⟩
  have hwalk : ∀ d, d ≤ idx → iterParent par d seq[idx] = seq[idx - d] := by
    intro d
    induction d with
    | zero => intro _; simp [iterParent]
    | succ d ih =>
        intro hd
        have hd0 : d ≤ idx := by omega
        have hlt_len : idx - d < seq.length := by omega
        have hpar_step : par seq[idx - d] = seq[idx - (d + 1)] := by
          have hp := lctAuxParent_of_tree hok hpp_le ht (idx - d) (hseq_eq.symm ▸ hlt_len)
          simp only [hseq_eq] at hp
          have hnz : idx - d ≠ 0 := by omega
          simp only [hnz, ↓reduceIte] at hp
          have him : idx - d - 1 < seq.length := by omega
          have hget : seq[idx - d - 1]! = seq[idx - d - 1] := by
            simp [getElem!_def, List.getElem?_eq_getElem him]
          rw [hget] at hp
          simpa [Nat.sub_sub] using hp
        calc
          iterParent par (d + 1) seq[idx]
            = par (iterParent par d seq[idx]) := iterParent_succ_right par d seq[idx]
          _ = par seq[idx - d] := by rw [ih hd0]
          _ = seq[idx - (d + 1)] := hpar_step
  have h0_lt : 0 < seq.length := by omega
  have hhead_par : par seq[0] = nodeField mem nb t.rootId OFF_PPAR := by
    have hp := lctAuxParent_of_tree hok hpp_le ht 0 (hseq_eq.symm ▸ h0_lt)
    simp only [hseq_eq] at hp
    exact hp
  have hcyc : iterParent par (idx + 1) (nodeField mem nb t.rootId OFF_PPAR) =
      nodeField mem nb t.rootId OFF_PPAR := by
    calc
      iterParent par (idx + 1) (nodeField mem nb t.rootId OFF_PPAR)
        = par (iterParent par idx seq[idx]) := by
          rw [← hidx_eq]; exact iterParent_succ_right par idx seq[idx]
      _ = par seq[0] := by rw [hwalk idx (le_refl idx)]; simp
      _ = nodeField mem nb t.rootId OFF_PPAR := hhead_par
  have hpp_b := (hok.trees_ok t ht).2.2.nodup_perm_mem hpp_mem
  have hcyc_cap : iterParent par cap (nodeField mem nb t.rootId OFF_PPAR) = 0 :=
    hacyc _ hpp_b.1 hpp_b.2
  have hmul : iterParent par (cap * (idx + 1)) (nodeField mem nb t.rootId OFF_PPAR) =
      nodeField mem nb t.rootId OFF_PPAR := by
    simpa [Nat.mul_comm] using iterParent_mul_cycle hcyc cap
  have hpow0 : iterParent par (cap * (idx + 1)) (nodeField mem nb t.rootId OFF_PPAR) = 0 := by
    let q := nodeField mem nb t.rootId OFF_PPAR
    change iterParent par (cap * (idx + 1)) q = 0
    have hp0 : par 0 = 0 := lctAuxParent_zero mem nb cap
    have hm1 : ∀ k, iterParent par (cap * (k + 1)) q = 0 := by
      intro k
      induction k with
      | zero => simpa using hcyc_cap
      | succ k ih =>
          rw [Nat.mul_succ, iterParent_add, ih]
          exact iterParent_zero_fixed hp0 cap
    exact hm1 idx
  rw [hmul] at hpow0
  omega

/-- Monotonicity of `lctRepSize` down `lctAuxParent`: any node in `seq[k ..]` has
`lctRepSize` at most `lctRepSize` of `seq[0]`. -/
theorem lctRepSize_ge_of_tree_idx {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {trees : List AuxTree} (hok : SplayForestOk w h L mem nb cap trees)
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent (lctAuxParent mem nb cap) cap u = 0)
    (hpp_le : ∀ s ∈ trees, nodeField mem nb s.rootId OFF_PPAR ≤ cap)
    {t : AuxTree} (ht : t ∈ trees) :
    ∀ k (hk : k < (lctTreeSeq mem nb cap t.rootId).length),
      lctRepSize mem nb cap (lctTreeSeq mem nb cap t.rootId)[k] ≤
        lctRepSize mem nb cap ((lctTreeSeq mem nb cap t.rootId)[0]'(by omega)) := by
  have hpar_le : ∀ x, 1 ≤ x → x ≤ cap → lctAuxParent mem nb cap x ≤ cap :=
    fun x _ _ => lctAuxParent_le_cap mem nb cap x
  have hseq_perm : (lctTreeSeq mem nb cap t.rootId).Perm t.toList := by
    rw [hok.lctTreeSeq_eq ht]; exact t.evalInorder_perm _ _
  intro k hk
  induction k with
  | zero => exact le_rfl
  | succ m ih =>
      have hm_lt : m < (lctTreeSeq mem nb cap t.rootId).length := by omega
      have h_prev := ih hm_lt
      have hm_b := (hok.trees_ok t ht).2.2.nodup_perm_mem (hseq_perm.mem_iff.1 (List.getElem_mem hm_lt))
      have hm1_b := (hok.trees_ok t ht).2.2.nodup_perm_mem (hseq_perm.mem_iff.1 (List.getElem_mem hk))
      have hpar_m1 : lctAuxParent mem nb cap (lctTreeSeq mem nb cap t.rootId)[m + 1] =
          (lctTreeSeq mem nb cap t.rootId)[m] := by
        have hp := lctAuxParent_of_tree hok hpp_le ht (m + 1) hk
        have hget : (lctTreeSeq mem nb cap t.rootId)[m]! = (lctTreeSeq mem nb cap t.rootId)[m] := by
          simp [getElem!_def, List.getElem?_eq_getElem hm_lt]
        simpa [hget] using hp
      rw [lctRepSize_eq_one_add_sum mem nb cap (lctTreeSeq mem nb cap t.rootId)[m]
        hpar_le hacyc hm_b.1 hm_b.2] at h_prev
      have hm1_in_cs : (lctTreeSeq mem nb cap t.rootId)[m + 1] ∈ ((List.range cap).map (· + 1)).filter
          (fun c => decide (lctAuxParent mem nb cap c = (lctTreeSeq mem nb cap t.rootId)[m])) := by
        simp only [List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
        exact ⟨⟨(lctTreeSeq mem nb cap t.rootId)[m + 1] - 1, by omega, by omega⟩, hpar_m1⟩
      have hle_sum : lctRepSize mem nb cap (lctTreeSeq mem nb cap t.rootId)[m + 1] ≤
          ((((List.range cap).map (· + 1)).filter
            (fun c => decide (lctAuxParent mem nb cap c =
              (lctTreeSeq mem nb cap t.rootId)[m]))).map (lctRepSize mem nb cap)).sum :=
        List.le_sum_of_mem (List.mem_map.2 ⟨(lctTreeSeq mem nb cap t.rootId)[m + 1], hm1_in_cs, rfl⟩)
      omega

/-- On `t = .node x l r`, detaching `r` (`right[x] := 0`, `ppar[r.root] := x`, `parent[r.root] := 0`)
preserves `lctAuxParent`, `lctRepSize`, and `splayMemPhi`, and increases `lctHeavyCount` by at most `1`. -/
theorem lctAux_detach_pure {w h L : ℕ} {mem₀ mem₁ : ℕ → ℕ} {nb cap x : ℕ}
    {l r : AuxTree} {rest : List AuxTree}
    (hok₀ : SplayForestOk w h L mem₀ nb cap (.node x l r :: rest))
    (hacyc₀ : ∀ u, 1 ≤ u → u ≤ cap → iterParent (lctAuxParent mem₀ nb cap) cap u = 0)
    (hpp_le₀ : nodeField mem₀ nb x OFF_PPAR ≤ cap ∧
      ∀ s ∈ rest, nodeField mem₀ nb s.rootId OFF_PPAR ≤ cap)
    (hrev0 : nodeField mem₀ nb x OFF_REV = 0)
    (hok₁ : SplayForestOk w h L mem₁ nb cap
      (match r with | .leaf => .node x l .leaf :: rest | .node _ _ _ => .node x l .leaf :: r :: rest))
    (hrest_agree : ∀ s ∈ rest,
      nodeField mem₁ nb s.rootId OFF_PPAR = nodeField mem₀ nb s.rootId OFF_PPAR ∧
      s.evalInorder (revFlag mem₁ nb) false = s.evalInorder (revFlag mem₀ nb) false)
    (hx_pp : nodeField mem₁ nb x OFF_PPAR = nodeField mem₀ nb x OFF_PPAR)
    (hx_eval : (AuxTree.node x l .leaf).evalInorder (revFlag mem₁ nb) false =
      l.evalInorder (revFlag mem₀ nb) false ++ [x])
    (hr_agree : match r with
      | .leaf => True
      | .node rc _ _ =>
          nodeField mem₁ nb rc OFF_PPAR = x ∧
          r.evalInorder (revFlag mem₁ nb) false = r.evalInorder (revFlag mem₀ nb) false) :
    (∀ u, lctAuxParent mem₁ nb cap u = lctAuxParent mem₀ nb cap u) ∧
    (∀ z, lctRepSize mem₁ nb cap z = lctRepSize mem₀ nb cap z) ∧
    (∀ y, lctVSize mem₁ nb cap y =
      if y = x then lctVSize mem₀ nb cap x + (if r = .leaf then 0 else r.treeSize (lctVSize mem₀ nb cap))
      else lctVSize mem₀ nb cap y) ∧
    splayMemPhi (K_SPLAY_STEP L) mem₁ nb cap (lctVSize mem₁ nb cap) =
      splayMemPhi (K_SPLAY_STEP L) mem₀ nb cap (lctVSize mem₀ nb cap) ∧
    lctHeavyCount mem₁ nb cap =
      lctHeavyCount mem₀ nb cap +
        (match r with
         | .leaf => 0
         | .node rc _ _ => if isHeavyRoot mem₁ nb cap rc then 1 else 0) := by
  have hnd_all₀ : ((AuxTree.node x l r :: rest).flatMap AuxTree.toList).Nodup :=
    hok₀.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  rw [List.flatMap_cons, List.nodup_append] at hnd_all₀
  have hx_nd₀ : (AuxTree.node x l r).toList.Nodup := hnd_all₀.1
  have hdisj_t_rest : ∀ a ∈ (AuxTree.node x l r).toList, ∀ b ∈ rest.flatMap AuxTree.toList, a ≠ b :=
    hnd_all₀.2.2
  have hx_b : 1 ≤ x ∧ x ≤ cap :=
    (hok₀.trees_ok (.node x l r) (by simp)).2.2.nodup_perm_mem (by simp [AuxTree.toList])
  have hrev_x0 : revFlag mem₀ nb x = false := by simp [revFlag, hrev0]
  have hx_seq₀ : (AuxTree.node x l r).evalInorder (revFlag mem₀ nb) false =
      (l.evalInorder (revFlag mem₀ nb) false ++ [x]) ++ r.evalInorder (revFlag mem₀ nb) false := by
    simp [AuxTree.evalInorder, hrev_x0]
  have hpp_le₁ : ∀ s ∈ (match r with
        | .leaf => AuxTree.node x l .leaf :: rest
        | .node _ _ _ => AuxTree.node x l .leaf :: r :: rest),
      nodeField mem₁ nb s.rootId OFF_PPAR ≤ cap := by
    cases r with
    | leaf =>
        intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs_rest
        · simpa [AuxTree.rootId, hx_pp] using hpp_le₀.1
        · rw [(hrest_agree s hs_rest).1]; exact hpp_le₀.2 s hs_rest
    | node rc rl rr =>
        intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | rfl | hs_rest
        · simpa [AuxTree.rootId, hx_pp] using hpp_le₀.1
        · simp only [AuxTree.rootId, hr_agree.1]; exact hx_b.2
        · rw [(hrest_agree s hs_rest).1]; exact hpp_le₀.2 s hs_rest
  have hpar_eq : ∀ u, lctAuxParent mem₁ nb cap u = lctAuxParent mem₀ nb cap u := by
    intro u
    rw [lctAuxParent_mem_iff_of_trees hok₁ hpp_le₁ u,
        lctAuxParent_mem_iff_of_trees hok₀ (fun s hs => by
          simp only [List.mem_cons] at hs
          rcases hs with rfl | hs_rest <;> [exact hpp_le₀.1; exact hpp_le₀.2 s hs_rest]) u]
    have htail_eq :
        rest.findSome? (fun s =>
          let seq := s.evalInorder (revFlag mem₁ nb) false
          if u ∈ seq then some (listParentFrom (nodeField mem₁ nb s.rootId OFF_PPAR) seq u) else none) =
        rest.findSome? (fun s =>
          let seq := s.evalInorder (revFlag mem₀ nb) false
          if u ∈ seq then some (listParentFrom (nodeField mem₀ nb s.rootId OFF_PPAR) seq u) else none) := by
      apply findSome?_congr_left
      intro s hs
      rcases hrest_agree s hs with ⟨hpp_s, hseq_s⟩
      simp only [hpp_s, hseq_s]
    cases r with
    | leaf =>
        have hx_seq₀' : (AuxTree.node x l .leaf).evalInorder (revFlag mem₀ nb) false =
            l.evalInorder (revFlag mem₀ nb) false ++ [x] := by
          simp [AuxTree.evalInorder, hrev_x0]
        by_cases hu : u ∈ l.evalInorder (revFlag mem₀ nb) false ++ [x]
        · have hu1 : u ∈ (AuxTree.node x l .leaf).evalInorder (revFlag mem₁ nb) false := by
            rw [hx_eval]; exact hu
          have hu0 : u ∈ (AuxTree.node x l .leaf).evalInorder (revFlag mem₀ nb) false := by
            rw [hx_seq₀']; exact hu
          rw [findSome?_cons_if hu1, findSome?_cons_if hu0]
          simp only [auxTree_rootId_node, hx_pp, hx_eval, hx_seq₀']
        · have hu1 : u ∉ (AuxTree.node x l .leaf).evalInorder (revFlag mem₁ nb) false := by
            rw [hx_eval]; exact hu
          have hu0 : u ∉ (AuxTree.node x l .leaf).evalInorder (revFlag mem₀ nb) false := by
            rw [hx_seq₀']; exact hu
          rw [findSome?_cons_if_neg hu1, findSome?_cons_if_neg hu0, htail_eq]
    | node rc rl rr =>
        let seqL := l.evalInorder (revFlag mem₀ nb) false ++ [x]
        let seqR := (AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false
        have hdisj_LR : ∀ a ∈ seqL, ∀ b ∈ seqR, a ≠ b := by
          intro a ha b hb
          have ha' : a ∈ l.toList ++ [x] := by
            simp only [seqL, List.mem_append, List.mem_singleton] at ha
            simp only [List.mem_append, List.mem_singleton]
            rcases ha with hl | rfl
            · exact Or.inl ((l.evalInorder_perm _ _).mem_iff.1 hl)
            · exact Or.inr rfl
          have hb' : b ∈ (AuxTree.node rc rl rr).toList :=
            ((AuxTree.node rc rl rr).evalInorder_perm (revFlag mem₀ nb) false).mem_iff.1 hb
          have hx_nd' := hx_nd₀
          rw [AuxTree.toList, List.nodup_append] at hx_nd'
          exact hx_nd'.2.2 a ha' b hb'
        have hlastL : seqL.getLast? = some x := by simp [seqL]
        have happ := listParentFrom_append_eq (prev := nodeField mem₀ nb x OFF_PPAR)
          (u := u) hlastL hdisj_LR
        dsimp only [seqL, seqR] at happ
        by_cases huL : u ∈ l.evalInorder (revFlag mem₀ nb) false ++ [x]
        · have hu1 : u ∈ (AuxTree.node x l .leaf).evalInorder (revFlag mem₁ nb) false := by
            rw [hx_eval]; exact huL
          have hu0 : u ∈ (AuxTree.node x l (AuxTree.node rc rl rr)).evalInorder (revFlag mem₀ nb) false := by
            rw [hx_seq₀]; exact List.mem_append.2 (Or.inl huL)
          rw [findSome?_cons_if hu1, findSome?_cons_if hu0]
          simp only [auxTree_rootId_node, hx_pp, hx_eval, hx_seq₀, happ, huL, ↓reduceIte]
        · by_cases huR : u ∈ (AuxTree.node rc rl rr).evalInorder (revFlag mem₀ nb) false
          · have hu1 : u ∉ (AuxTree.node x l .leaf).evalInorder (revFlag mem₁ nb) false := by
              rw [hx_eval]; exact huL
            have hu2 : u ∈ (AuxTree.node rc rl rr).evalInorder (revFlag mem₁ nb) false := by
              rw [hr_agree.2]; exact huR
            have hu0 : u ∈ (AuxTree.node x l (AuxTree.node rc rl rr)).evalInorder (revFlag mem₀ nb) false := by
              rw [hx_seq₀]; exact List.mem_append.2 (Or.inr huR)
            rw [findSome?_cons_if_neg hu1, findSome?_cons_if hu2, findSome?_cons_if hu0]
            simp only [auxTree_rootId_node, hr_agree.1, hr_agree.2, hx_seq₀, happ, huL, ↓reduceIte]
          · have hu1 : u ∉ (AuxTree.node x l .leaf).evalInorder (revFlag mem₁ nb) false := by
              rw [hx_eval]; exact huL
            have hu2 : u ∉ (AuxTree.node rc rl rr).evalInorder (revFlag mem₁ nb) false := by
              rw [hr_agree.2]; exact huR
            have hu0 : u ∉ (AuxTree.node x l (AuxTree.node rc rl rr)).evalInorder (revFlag mem₀ nb) false := by
              rw [hx_seq₀, List.mem_append]; rintro (h | h) <;> contradiction
            rw [findSome?_cons_if_neg hu1, findSome?_cons_if_neg hu2, findSome?_cons_if_neg hu0, htail_eq]
  have hrep_eq : ∀ z, lctRepSize mem₁ nb cap z = lctRepSize mem₀ nb cap z := by
    intro z
    simp only [lctRepSize]
    congr 1
    apply List.filter_congr
    intro u _
    have hiter : ∀ k q, iterParent (lctAuxParent mem₁ nb cap) k q =
        iterParent (lctAuxParent mem₀ nb cap) k q := by
      intro k; induction k with
      | zero => intro q; rfl
      | succ k ih => intro q; simp only [iterParent, hpar_eq, ih]
    simp only [reachesIn, hiter]
  have hacyc₁ : ∀ u, 1 ≤ u → u ≤ cap → iterParent (lctAuxParent mem₁ nb cap) cap u = 0 := by
    intro u hu1 hu2
    have hiter : ∀ k q, iterParent (lctAuxParent mem₁ nb cap) k q =
        iterParent (lctAuxParent mem₀ nb cap) k q := by
      intro k; induction k with
      | zero => intro q; rfl
      | succ k ih => intro q; simp only [iterParent, hpar_eq, ih]
    rw [hiter]; exact hacyc₀ u hu1 hu2
  have hx_seq_eq₁ : lctTreeSeq mem₁ nb cap x = l.evalInorder (revFlag mem₀ nb) false ++ [x] := by
    have heq := hok₁.lctTreeSeq_eq (t := AuxTree.node x l .leaf) (by cases r <;> simp)
    simpa [AuxTree.rootId, hx_eval] using heq
  have hx_seq_eq₀ : lctTreeSeq mem₀ nb cap x =
      (l.evalInorder (revFlag mem₀ nb) false ++ [x]) ++ r.evalInorder (revFlag mem₀ nb) false := by
    have heq := hok₀.lctTreeSeq_eq (t := AuxTree.node x l r) (by simp)
    simpa [AuxTree.rootId, hx_seq₀] using heq
  have hdcs_x : dashedChildSize mem₁ nb cap x = dashedChildSize mem₀ nb cap x := by
    simp only [dashedChildSize, hx_seq_eq₁, hx_seq_eq₀]
    cases l.evalInorder (revFlag mem₀ nb) false <;> simp [hrep_eq]
  have hheavy_x : isHeavyRoot mem₁ nb cap x = isHeavyRoot mem₀ nb cap x := by
    simp only [isHeavyRoot, hx_pp, hx_seq_eq₁, hx_seq_eq₀]
    cases l.evalInorder (revFlag mem₀ nb) false <;> simp [hrep_eq]
  have hperm₀ := hok₀.auxRootIds_perm
  have hperm₁ := hok₁.auxRootIds_perm
  have hy_ne_x : ∀ z, z ≠ x → lctVSize mem₁ nb cap z = lctVSize mem₀ nb cap z := by
    intro z hzx
    let contribZ := fun mem q =>
      if nodeField mem nb q OFF_PPAR = z then dashedChildSize mem nb cap q else 0
    have hsf : ∀ mem (rs : List ℕ),
        ((rs.filter fun q => decide (nodeField mem nb q OFF_PPAR = z)).map
          fun q => dashedChildSize mem nb cap q).sum = (rs.map (contribZ mem)).sum := fun mem rs => by
      simpa [contribZ, decide_eq_true_eq] using
        list_filter_map_sum_ite rs (fun q => decide (nodeField mem nb q OFF_PPAR = z))
          (dashedChildSize mem nb cap)
    simp only [lctVSize, hsf]
    rw [(hperm₁.map (contribZ mem₁)).sum_eq, (hperm₀.map (contribZ mem₀)).sum_eq]
    have htailZ : (rest.map AuxTree.rootId).map (contribZ mem₁) =
        (rest.map AuxTree.rootId).map (contribZ mem₀) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro s hs
      rcases hrest_agree s hs with ⟨hpp_s, hseq_s⟩
      have htree_eq : lctTreeSeq mem₁ nb cap s.rootId = lctTreeSeq mem₀ nb cap s.rootId := by
        rw [hok₁.lctTreeSeq_eq (by cases r <;> simp [hs]), hok₀.lctTreeSeq_eq (by simp [hs]), hseq_s]
      have hdcs_s : dashedChildSize mem₁ nb cap s.rootId = dashedChildSize mem₀ nb cap s.rootId := by
        simp only [dashedChildSize, htree_eq]
        cases lctTreeSeq mem₀ nb cap s.rootId with
        | nil => rfl
        | cons hd _ => simp [hrep_eq]
      simp [contribZ, hpp_s, hdcs_s]
    have hc_x : contribZ mem₁ x = contribZ mem₀ x := by simp [contribZ, hx_pp, hdcs_x]
    cases r with
    | leaf =>
        simp only [List.map_cons, AuxTree.rootId, List.sum_cons]
        rw [hc_x, htailZ]
    | node rc rl rr =>
        simp only [List.map_cons, AuxTree.rootId, List.sum_cons]
        have hc_rc : contribZ mem₁ rc = 0 := by simp [contribZ, hr_agree.1, hzx.symm]
        rw [hc_x, hc_rc, htailZ, Nat.zero_add]
  have hvs_eq : ∀ y, lctVSize mem₁ nb cap y =
      if y = x then lctVSize mem₀ nb cap x + (if r = .leaf then 0 else r.treeSize (lctVSize mem₀ nb cap))
      else lctVSize mem₀ nb cap y := by
    intro y
    by_cases hyx : y = x
    · subst y
      simp only [↓reduceIte]
      let contribX := fun mem q =>
        if nodeField mem nb q OFF_PPAR = x then dashedChildSize mem nb cap q else 0
      have hsf : ∀ mem (rs : List ℕ),
          ((rs.filter fun q => decide (nodeField mem nb q OFF_PPAR = x)).map
            fun q => dashedChildSize mem nb cap q).sum = (rs.map (contribX mem)).sum := fun mem rs => by
        simpa [contribX, decide_eq_true_eq] using
          list_filter_map_sum_ite rs (fun q => decide (nodeField mem nb q OFF_PPAR = x))
            (dashedChildSize mem nb cap)
      simp only [lctVSize, hsf]
      rw [(hperm₁.map (contribX mem₁)).sum_eq, (hperm₀.map (contribX mem₀)).sum_eq]
      have htailX : (rest.map AuxTree.rootId).map (contribX mem₁) =
          (rest.map AuxTree.rootId).map (contribX mem₀) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro s hs
        rcases hrest_agree s hs with ⟨hpp_s, hseq_s⟩
        have htree_eq : lctTreeSeq mem₁ nb cap s.rootId = lctTreeSeq mem₀ nb cap s.rootId := by
          rw [hok₁.lctTreeSeq_eq (by cases r <;> simp [hs]), hok₀.lctTreeSeq_eq (by simp [hs]), hseq_s]
        have hdcs_s : dashedChildSize mem₁ nb cap s.rootId = dashedChildSize mem₀ nb cap s.rootId := by
          simp only [dashedChildSize, htree_eq]
          cases lctTreeSeq mem₀ nb cap s.rootId with
          | nil => rfl
          | cons hd _ => simp [hrep_eq]
        simp [contribX, hpp_s, hdcs_s]
      have hc_x : contribX mem₁ x = contribX mem₀ x := by
        dsimp only [contribX]; rw [hx_pp, hdcs_x]
      cases r with
      | leaf =>
          simp only [↓reduceIte, Nat.add_zero, List.map_cons, AuxTree.rootId, List.sum_cons]
          rw [hc_x, htailX]
      | node rc rl rr =>
          have hnot : (AuxTree.node rc rl rr = AuxTree.leaf) = False := by simp
          simp only [hnot, ↓reduceIte, List.map_cons, AuxTree.rootId, List.sum_cons]
          have hne₁ : ∀ s ∈ (AuxTree.node x l .leaf :: AuxTree.node rc rl rr :: rest),
              lctTreeSeq mem₁ nb cap s.rootId ≠ [] := fun s hs => by
            rw [hok₁.lctTreeSeq_eq hs]
            exact auxTree_eval_ne_nil_of_ne_leaf (hok₁.trees_ok s hs).1
          have hrc_sz : dashedChildSize mem₁ nb cap rc =
              (AuxTree.node rc rl rr).treeSize (lctVSize mem₁ nb cap) := by
            have htree := treeSize_lctVSize_eq_repSize hok₁ hacyc₁ hpp_le₁ hne₁
              (t := AuxTree.node rc rl rr) (by simp)
            simp only [AuxTree.rootId] at htree
            cases hcons : lctTreeSeq mem₁ nb cap rc with
            | nil => exact absurd hcons (by simpa [AuxTree.rootId] using hne₁ (.node rc rl rr) (by simp))
            | cons hd tl =>
                simp only [dashedChildSize, hcons]
                simpa [hcons] using htree.symm
          have hx_nin_r : x ∉ (AuxTree.node rc rl rr).toList := auxTree_nodup_id_nin_right hx_nd₀
          have hrc_sz₀ : (AuxTree.node rc rl rr).treeSize (lctVSize mem₁ nb cap) =
              (AuxTree.node rc rl rr).treeSize (lctVSize mem₀ nb cap) := by
            rw [AuxTree.treeSize_eq_sum, AuxTree.treeSize_eq_sum]
            congr 1; apply List.map_congr_left
            intro u hu; exact congrArg (1 + ·) (hy_ne_x u (fun h => hx_nin_r (h ▸ hu)))
          have hc_rc : contribX mem₁ rc = (AuxTree.node rc rl rr).treeSize (lctVSize mem₀ nb cap) := by
            simp only [contribX, hr_agree.1, ↓reduceIte, hrc_sz, hrc_sz₀]
          rw [hc_x, hc_rc, htailX]; omega
    · simp only [hyx, ↓reduceIte]; exact hy_ne_x y hyx
  have hphi_eq : splayMemPhi (K_SPLAY_STEP L) mem₁ nb cap (lctVSize mem₁ nb cap) =
      splayMemPhi (K_SPLAY_STEP L) mem₀ nb cap (lctVSize mem₀ nb cap) := by
    rw [splayMemPhi_eq_sum hok₁, splayMemPhi_eq_sum hok₀]
    have hv_rest : ∀ s ∈ rest, s.treePhi (lctVSize mem₁ nb cap) = s.treePhi (lctVSize mem₀ nb cap) :=
      fun s hs => auxTree_treePhi_congr fun u hu => by
        have hx_nin_s : x ∉ s.toList := fun hm =>
          hdisj_t_rest x (by simp [AuxTree.toList]) x (List.mem_flatMap.2 ⟨s, hs, hm⟩) rfl
        have hux : u ≠ x := fun h => hx_nin_s (h ▸ hu)
        simp [hvs_eq u, hux]
    have hl_nin_x : x ∉ l.toList := auxTree_nodup_id_nin_left hx_nd₀
    have hl_phi : l.treePhi (lctVSize mem₁ nb cap) = l.treePhi (lctVSize mem₀ nb cap) :=
      auxTree_treePhi_congr fun u hu => by simp [hvs_eq u, show u ≠ x from fun h => hl_nin_x (h ▸ hu)]
    have hl_sz : l.treeSize (lctVSize mem₁ nb cap) = l.treeSize (lctVSize mem₀ nb cap) := by
      rw [AuxTree.treeSize_eq_sum, AuxTree.treeSize_eq_sum]
      congr 1; apply List.map_congr_left
      intro u hu; simp [hvs_eq u, show u ≠ x from fun h => hl_nin_x (h ▸ hu)]
    have hsum_rest : (rest.map (AuxTree.treePhi (lctVSize mem₁ nb cap))).sum =
        (rest.map (AuxTree.treePhi (lctVSize mem₀ nb cap))).sum :=
      congrArg List.sum (List.map_congr_left hv_rest)
    cases r with
    | leaf =>
        simp only [List.map_cons, List.sum_cons, AuxTree.treePhi, AuxTree.rank, AuxTree.treeSize,
          Nat.add_zero]
        have hx0 : lctVSize mem₁ nb cap x = lctVSize mem₀ nb cap x := by simp [hvs_eq x]
        rw [hl_phi, hl_sz, hx0, hsum_rest]
    | node rc rl rr =>
        have hr_nin_x : x ∉ (AuxTree.node rc rl rr).toList := auxTree_nodup_id_nin_right hx_nd₀
        have hr_phi : (AuxTree.node rc rl rr).treePhi (lctVSize mem₁ nb cap) =
            (AuxTree.node rc rl rr).treePhi (lctVSize mem₀ nb cap) :=
          auxTree_treePhi_congr fun u hu => by simp [hvs_eq u, show u ≠ x from fun h => hr_nin_x (h ▸ hu)]
        have htop_sz : (AuxTree.node x l .leaf).treeSize (lctVSize mem₁ nb cap) =
            (AuxTree.node x l (AuxTree.node rc rl rr)).treeSize (lctVSize mem₀ nb cap) := by
          simp only [AuxTree.treeSize, hl_sz, hvs_eq x]
          have hnot : (AuxTree.node rc rl rr = AuxTree.leaf) = False := by simp
          simp only [hnot, ↓reduceIte]; omega
        simp only [List.map_cons, List.sum_cons]
        have htop_phi : (AuxTree.node x l .leaf).treePhi (lctVSize mem₁ nb cap) =
            (AuxTree.node x l (AuxTree.node rc rl rr)).rank (lctVSize mem₀ nb cap) +
              l.treePhi (lctVSize mem₀ nb cap) := by
          simp only [AuxTree.treePhi, AuxTree.rank, htop_sz, hl_phi, Nat.add_zero]
        rw [htop_phi, hr_phi, hsum_rest]
        simp only [AuxTree.treePhi, AuxTree.rank]
        ring
  have hheavy_eq : lctHeavyCount mem₁ nb cap =
      lctHeavyCount mem₀ nb cap +
        (match r with
         | .leaf => 0
         | .node rc _ _ => if isHeavyRoot mem₁ nb cap rc then 1 else 0) := by
    let hflag := fun mem q => if isHeavyRoot mem nb cap q then 1 else 0
    have hsf : ∀ mem (rs : List ℕ),
        (rs.filter (fun q => isHeavyRoot mem nb cap q)).length = (rs.map (hflag mem)).sum :=
      fun mem rs => list_filter_length_ite rs (isHeavyRoot mem nb cap)
    simp only [lctHeavyCount, hsf]
    rw [(hperm₁.map (hflag mem₁)).sum_eq, (hperm₀.map (hflag mem₀)).sum_eq]
    have htail : (rest.map AuxTree.rootId).map (hflag mem₁) =
        (rest.map AuxTree.rootId).map (hflag mem₀) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro s hs
      rcases hrest_agree s hs with ⟨hpp_s, hseq_s⟩
      have htree_eq : lctTreeSeq mem₁ nb cap s.rootId = lctTreeSeq mem₀ nb cap s.rootId := by
        rw [hok₁.lctTreeSeq_eq (by cases r <;> simp [hs]), hok₀.lctTreeSeq_eq (by simp [hs]), hseq_s]
      have hhs : isHeavyRoot mem₁ nb cap s.rootId = isHeavyRoot mem₀ nb cap s.rootId := by
        simp only [isHeavyRoot, hpp_s, htree_eq]
        cases lctTreeSeq mem₀ nb cap s.rootId with
        | nil => rfl
        | cons hd _ => simp [hrep_eq]
      simp only [Function.comp_def, hflag, hhs]
    have hhx : hflag mem₁ x = hflag mem₀ x := by simp only [hflag, hheavy_x]
    cases r with
    | leaf =>
        simp only [List.map_cons, AuxTree.rootId, List.sum_cons]
        rw [hhx, htail, Nat.add_zero]
    | node rc rl rr =>
        simp only [List.map_cons, AuxTree.rootId, List.sum_cons]
        rw [hhx, htail]
        dsimp only [hflag]
        omega
  refine ⟨hpar_eq, hrep_eq, hvs_eq, hphi_eq, ?_⟩
  cases r <;> exact hheavy_eq

end PureStructuralHelpers
end MinCostFlow.LinkCut.Prog
end
