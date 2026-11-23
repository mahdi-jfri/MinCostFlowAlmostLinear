module

public import MinCostFlow.LinkCut.Prog.MathForestFraming
import Mathlib.Data.List.Perm.Basic

/-!
# Represented subtree size, tree rank, and global potential bounds

Relates pure-memory auxiliary tree structure (`lctAuxParent`, `lctRepSize`, `lctVSize`)
to `AuxTree.treeSize`, `AuxTree.rank`, and `lctPhi` under `SplayForestOk` and `LctMemRep`:
- `SplayForestOk.auxRootIds_perm`, `SplayForestOk.lctTreeSeq_eq`
- `lctAuxParent_of_tree`, `lctRepSize_eq_one_add_sum`, `treeSize_lctVSize_eq_repSize`
- `LctMemRep.tree_size_le_cap`, `LctMemRep.tree_rank_le_log`, `LctMemRep.lctPhi_le_bound`
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section SplayForestProjections

theorem SplayForestOk.perm {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ} {trees : List AuxTree}
    (hok : SplayForestOk w h L mem nb cap trees) :
    (trees.flatMap AuxTree.toList).Perm ((List.range cap).map (· + 1)) :=
  hok.2.2.2.2.2.2.2.2.1

theorem SplayForestOk.trees_ok {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ} {trees : List AuxTree}
    (hok : SplayForestOk w h L mem nb cap trees) :
    ∀ t ∈ trees, t ≠ .leaf ∧ nodeField mem nb t.rootId OFF_PPAR < 2 ^ w ∧
      TreeMemMatch w h L mem nb cap t 0 (nodeField mem nb t.rootId OFF_PPAR) :=
  hok.2.2.2.2.2.2.2.2.2

theorem TreeMemMatch.root_bounds {w h L : ℕ} {mem : ℕ → ℕ} {nb cap x p pp : ℕ}
    {l r : AuxTree} (ht : TreeMemMatch w h L mem nb cap (.node x l r) p pp) :
    1 ≤ x ∧ x ≤ cap :=
  ⟨ht.1, ht.2.1⟩

theorem TreeMemMatch.parent_eq {w h L : ℕ} {mem : ℕ → ℕ} {nb cap x p pp : ℕ}
    {l r : AuxTree} (ht : TreeMemMatch w h L mem nb cap (.node x l r) p pp) :
    nodeField mem nb x OFF_PARENT = p :=
  ht.2.2.2.2.1

theorem TreeMemMatch.children_match {w h L : ℕ} {mem : ℕ → ℕ} {nb cap x p pp : ℕ}
    {l r : AuxTree} (ht : TreeMemMatch w h L mem nb cap (.node x l r) p pp) :
    TreeMemMatch w h L mem nb cap l x 0 ∧ TreeMemMatch w h L mem nb cap r x 0 :=
  ⟨ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   ht.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem AuxTree.treeSize_eq_sum (vSize : ℕ → ℕ) (t : AuxTree) :
    t.treeSize vSize = (t.toList.map (fun y => 1 + vSize y)).sum := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
      simp only [AuxTree.treeSize, AuxTree.toList, List.map_append, List.map_cons,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, ihl, ihr]
      omega

theorem AuxTree.treeSize_eq_sum_evalInorder (rev : ℕ → Bool) (vSize : ℕ → ℕ) (t : AuxTree) :
    t.treeSize vSize = ((t.evalInorder rev false).map (fun y => 1 + vSize y)).sum := by
  rw [AuxTree.treeSize_eq_sum, ((t.evalInorder_perm rev false).map (fun y => 1 + vSize y)).sum_eq]

theorem mem_nodup_of_flatMap_nodup {trees : List AuxTree}
    (hnd : (trees.flatMap AuxTree.toList).Nodup) {s : AuxTree} (hs : s ∈ trees) :
    s.toList.Nodup := by
  induction trees with
  | nil => contradiction
  | cons a rest ih =>
      rw [List.flatMap_cons, List.nodup_append] at hnd
      rcases List.mem_cons.1 hs with rfl | hs'
      · exact hnd.1
      · exact ih hnd.2.1 hs'

theorem unique_tree_of_mem {trees : List AuxTree}
    (hnd : (trees.flatMap AuxTree.toList).Nodup)
    {s t : AuxTree} (hs : s ∈ trees) (ht : t ∈ trees) {x : ℕ}
    (hx : x ∈ s.toList) (hy : x ∈ t.toList) : s = t := by
  induction trees with
  | nil => contradiction
  | cons a rest ih =>
      rw [List.flatMap_cons, List.nodup_append] at hnd
      rcases List.mem_cons.1 hs with rfl | hs' <;> rcases List.mem_cons.1 ht with rfl | ht'
      · rfl
      · exact absurd (List.mem_flatMap.2 ⟨t, ht', hy⟩) fun hm => hnd.2.2 _ hx _ hm rfl
      · exact absurd (List.mem_flatMap.2 ⟨s, hs', hx⟩) fun hm => hnd.2.2 _ hy _ hm rfl
      · exact ih hnd.2.1 hs' ht'

private theorem list_nodup_flatMap_disjoint_roots {trees : List AuxTree}
    (hnd : (trees.flatMap AuxTree.toList).Nodup) (hne : ∀ t ∈ trees, t ≠ .leaf) :
    (trees.map AuxTree.rootId).Nodup := by
  induction trees with
  | nil => simp
  | cons a ts ih =>
      simp only [List.flatMap_cons, List.nodup_append] at hnd
      rcases hnd with ⟨_, hts_nd, hdisj⟩
      have ha_mem := AuxTree.rootId_mem_toList (hne a (by simp))
      simp only [List.map_cons, List.nodup_cons, List.mem_map]
      refine ⟨?_, ih hts_nd (fun t ht => hne t (by simp [ht]))⟩
      rintro ⟨t, ht, hrt⟩
      have ht_mem : t.rootId ∈ ts.flatMap AuxTree.toList :=
        List.mem_flatMap.2 ⟨t, ht, AuxTree.rootId_mem_toList (hne t (by simp [ht]))⟩
      rw [hrt] at ht_mem
      exact hdisj a.rootId ha_mem a.rootId ht_mem rfl

theorem SplayForestOk.auxRootIds_perm {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {trees : List AuxTree} (hok : SplayForestOk w h L mem nb cap trees) :
    (auxRootIds mem nb cap).Perm (trees.map AuxTree.rootId) := by
  have hperm := hok.perm
  have hts := hok.trees_ok
  have hnd_all : (trees.flatMap AuxTree.toList).Nodup :=
    hperm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hne : ∀ t ∈ trees, t ≠ .leaf := fun t ht => (hts t ht).1
  have hmap_nd := list_nodup_flatMap_disjoint_roots hnd_all hne
  have hnonzero_sub : ∀ s p pp, TreeMemMatch w h L mem nb cap s p pp →
      1 ≤ p → ∀ u ∈ s.toList, nodeField mem nb u OFF_PARENT ≠ 0 := by
    intro s
    induction s with
    | leaf => intro _ _ _ _ _ hu; simp [AuxTree.toList] at hu
    | node y sl sr ihsl ihsr =>
        intro p pp hmy hp u hu
        have hy1 := hmy.root_bounds.1
        have hyp := hmy.parent_eq
        have ⟨hsl, hsr⟩ := hmy.children_match
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
        rcases hu with (hul | rfl) | hur
        · exact ihsl y 0 hsl (by omega) u hul
        · omega
        · exact ihsr y 0 hsr (by omega) u hur
  have hroot_iff : ∀ r, r ∈ auxRootIds mem nb cap ↔ r ∈ trees.map AuxTree.rootId := by
    intro r
    simp only [auxRootIds, List.mem_filter, List.mem_map, decide_eq_true_eq]
    constructor
    · rintro ⟨hr_range, hpar0⟩
      have hmem : r ∈ trees.flatMap AuxTree.toList := hperm.symm.mem_iff.1 (List.mem_map.2 hr_range)
      rcases List.mem_flatMap.1 hmem with ⟨t, ht_in, hr_in⟩
      rcases hts t ht_in with ⟨ht_ne, _, hmatch⟩
      cases t with
      | leaf => exact absurd rfl ht_ne
      | node u l rchild =>
          have hu1 := hmatch.root_bounds.1
          have ⟨hml, hmr⟩ := hmatch.children_match
          simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hr_in
          rcases hr_in with (hrl | rfl) | hrr
          · exact absurd hpar0 (hnonzero_sub l u 0 hml (by omega) r hrl)
          · exact ⟨_, ht_in, rfl⟩
          · exact absurd hpar0 (hnonzero_sub rchild u 0 hmr (by omega) r hrr)
    · rintro ⟨t, ht_in, rfl⟩
      rcases hts t ht_in with ⟨ht_ne, _, hmatch⟩
      cases t with
      | leaf => exact absurd rfl ht_ne
      | node u _ _ =>
          have hmem_t : u ∈ trees.flatMap AuxTree.toList :=
            List.mem_flatMap.2 ⟨_, ht_in, by simp [AuxTree.toList]⟩
          have hrange := hperm.mem_iff.1 hmem_t
          exact ⟨List.mem_map.1 hrange, hmatch.parent_eq⟩
  have haux_nd : (auxRootIds mem nb cap).Nodup :=
    (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)).filter _
  exact (List.perm_ext_iff_of_nodup haux_nd hmap_nd).2 hroot_iff

theorem SplayForestOk.lctTreeSeq_eq {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {trees : List AuxTree} (hok : SplayForestOk w h L mem nb cap trees)
    {t : AuxTree} (ht : t ∈ trees) :
    lctTreeSeq mem nb cap t.rootId = t.evalInorder (revFlag mem nb) false := by
  have hperm := hok.perm
  have hts := hok.trees_ok
  have hsub : t.toList.length ≤ (trees.flatMap AuxTree.toList).length := by
    suffices hgo : ∀ l : List AuxTree, t ∈ l → t.toList.length ≤ (l.flatMap AuxTree.toList).length from
      hgo trees ht
    intro l hl
    induction l with
    | nil => contradiction
    | cons a as ih =>
        simp only [List.flatMap_cons, List.length_append]
        rcases List.mem_cons.1 hl with rfl | has
        · omega
        · have := ih has; omega
  rw [t.length_toList, hperm.length_eq, List.length_map, List.length_range] at hsub
  simp only [lctTreeSeq, (hts t ht).2.2.readAuxTree_eq hsub]

end SplayForestProjections

section ParentAndRepSize

theorem lctAuxParent_zero (mem : ℕ → ℕ) (nb cap : ℕ) :
    lctAuxParent mem nb cap 0 = 0 := by
  have h0_notin : ∀ r ∈ auxRootIds mem nb cap, 0 ∉ lctTreeSeq mem nb cap r := by
    intro r _ h0
    have hperm := (readAuxTree mem nb cap cap r).evalInorder_perm (revFlag mem nb) false
    have hb := readAuxTree_nodes_bounds (hperm.mem_iff.1 h0)
    omega
  have hnone : (auxRootIds mem nb cap).findSome? (fun r => treeParentEntry mem nb cap r 0) = none := by
    rw [List.findSome?_eq_none_iff]
    intro r hr
    simp [treeParentEntry, h0_notin r hr]
  simp [lctAuxParent, hnone]

theorem listParentFrom_le {prev : ℕ} {xs : List ℕ} {u cap : ℕ}
    (hp : prev ≤ cap) (hxs : ∀ z ∈ xs, z ≤ cap) :
    listParentFrom prev xs u ≤ cap := by
  induction xs generalizing prev with
  | nil => simp [listParentFrom]
  | cons y ys ih =>
      simp only [listParentFrom]
      split_ifs
      · exact hp
      · exact ih (hxs y (by simp)) (fun z hz => hxs z (by simp [hz]))

theorem lctAuxParent_le_cap (mem : ℕ → ℕ) (nb cap u : ℕ) :
    lctAuxParent mem nb cap u ≤ cap := by
  dsimp only [lctAuxParent]
  split
  · rename_i p hfs
    rcases List.findSome?_eq_some_iff.1 hfs with ⟨_, r, _, _, hsome, _⟩
    simp only [treeParentEntry] at hsome
    split_ifs at hsome with hin hle
    · injection hsome with hp_eq
      rw [← hp_eq]
      exact listParentFrom_le hle fun z hz =>
        (readAuxTree_nodes_bounds ((AuxTree.evalInorder_perm _ _ _).mem_iff.1 hz)).2
    · injection hsome with hp_eq
      rw [← hp_eq]
      exact listParentFrom_le (Nat.zero_le _) fun z hz =>
        (readAuxTree_nodes_bounds ((AuxTree.evalInorder_perm _ _ _).mem_iff.1 hz)).2
  · omega

theorem iterParent_add (par : ℕ → ℕ) (a b u : ℕ) :
    iterParent par (a + b) u = iterParent par b (iterParent par a u) := by
  induction a generalizing u with
  | zero => simp [iterParent]
  | succ a ih => rw [Nat.succ_add]; exact ih (par u)

theorem iterParent_succ_right (par : ℕ → ℕ) (k u : ℕ) :
    iterParent par (k + 1) u = par (iterParent par k u) := by
  simpa [Nat.add_comm, iterParent] using iterParent_add par k 1 u

theorem iterParent_zero_fixed {par : ℕ → ℕ} (hp0 : par 0 = 0) (k : ℕ) :
    iterParent par k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [iterParent, hp0] using ih

theorem iterParent_ge_zero {par : ℕ → ℕ} (hp0 : par 0 = 0) {cap u k : ℕ}
    (hcap : iterParent par cap u = 0) (hk : cap ≤ k) :
    iterParent par k u = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [iterParent_add, hcap, iterParent_zero_fixed hp0]

theorem iterParent_mul_cycle {par : ℕ → ℕ} {d y : ℕ} (hc : iterParent par d y = y) (m : ℕ) :
    iterParent par (m * d) y = y := by
  induction m with
  | zero => simp [iterParent]
  | succ m ih => rw [Nat.succ_mul, iterParent_add, ih, hc]

theorem iterParent_no_cycle {par : ℕ → ℕ} (hp0 : par 0 = 0) {cap : ℕ}
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent par cap u = 0)
    {y d : ℕ} (hy1 : 1 ≤ y) (hy2 : y ≤ cap) (hd : 1 ≤ d) :
    iterParent par d y ≠ y := by
  intro hc
  have hm := iterParent_mul_cycle hc cap
  have hge : cap ≤ cap * d := Nat.le_mul_of_pos_right cap hd
  have h0 := iterParent_ge_zero hp0 (hacyc y hy1 hy2) hge
  omega

theorem iterParent_le_cap {par : ℕ → ℕ} {cap : ℕ} (hp0 : par 0 = 0)
    (hle : ∀ x, 1 ≤ x → x ≤ cap → par x ≤ cap)
    {u : ℕ} (hu : u ≤ cap) (k : ℕ) :
    iterParent par k u ≤ cap := by
  induction k generalizing u with
  | zero => exact hu
  | succ k ih =>
      simp only [iterParent]
      apply ih
      cases u with
      | zero => simp [hp0]
      | succ u' => exact hle (u' + 1) (by omega) hu

private theorem reachesIn_iff_self_or_child {par : ℕ → ℕ} {cap : ℕ}
    (hp0 : par 0 = 0) (hle : ∀ x, 1 ≤ x → x ≤ cap → par x ≤ cap)
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent par cap u = 0)
    {u y : ℕ} (hu1 : 1 ≤ u) (hu2 : u ≤ cap) (hy1 : 1 ≤ y) (hy2 : y ≤ cap) :
    reachesIn par cap u y = true ↔
      u = y ∨ ∃ c ∈ (List.range cap).map (· + 1),
        par c = y ∧ reachesIn par cap u c = true := by
  simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨_, ⟨k, hk_lt, hk_eq⟩⟩
    cases k with
    | zero => exact Or.inl (by simpa [iterParent] using hk_eq)
    | succ m =>
        let c := iterParent par m u
        have hpc : par c = y := by simpa [c, iterParent_succ_right] using hk_eq
        have hc0 : c ≠ 0 := by intro h0; rw [h0, hp0] at hpc; omega
        have hc_le : c ≤ cap := iterParent_le_cap hp0 hle hu2 m
        refine Or.inr ⟨c, List.mem_map.2 ⟨c - 1, List.mem_range.2 (by omega), by omega⟩, hpc,
          by omega, ⟨m, by omega, rfl⟩⟩
  · rintro (rfl | ⟨c, _, hpc, ⟨_, ⟨k, hk_lt, hk_eq⟩⟩⟩)
    · exact ⟨by omega, ⟨0, by omega, rfl⟩⟩
    · refine ⟨by omega, ?_⟩
      have hk_lt_cap : k + 1 < cap := by
        by_contra hge
        have hk_cap : k + 1 = cap := by omega
        have hc := hacyc u hu1 hu2
        rw [← hk_cap, iterParent_succ_right, hk_eq, hpc] at hc
        omega
      exact ⟨k + 1, hk_lt_cap, by rw [iterParent_succ_right, hk_eq, hpc]⟩

private theorem list_length_filter_disjoint_sum {α β : Type*} (L : List α)
    (cs : List β) (hnd : cs.Nodup) (p : α → Bool) (q : β → α → Bool)
    (hc_disj : ∀ b₁ ∈ cs, ∀ b₂ ∈ cs, b₁ ≠ b₂ → ∀ a ∈ L, ¬ (q b₁ a = true ∧ q b₂ a = true))
    (hc_sub : ∀ b ∈ cs, ∀ a ∈ L, q b a = true → p a = true)
    (hcover : ∀ a ∈ L, p a = true → ∃ b ∈ cs, q b a = true) :
    (L.filter p).length = (cs.map (fun b => (L.filter (q b)).length)).sum := by
  induction L with
  | nil =>
      simp only [List.filter_nil, List.length_nil]
      symm
      rw [List.sum_eq_zero_iff]
      intro n hn
      rcases List.mem_map.1 hn with ⟨b, _, rfl⟩
      simp
  | cons a as ih =>
      have ih' := ih
        (fun b₁ hb₁ b₂ hb₂ hne x hx => hc_disj b₁ hb₁ b₂ hb₂ hne x (by simp [hx]))
        (fun b hb x hx => hc_sub b hb x (by simp [hx]))
        (fun x hx => hcover x (by simp [hx]))
      by_cases hp : p a = true
      · rcases hcover a (by simp) hp with ⟨b₀, hb₀, hq₀⟩
        have hnone : ∀ b ∈ cs, b ≠ b₀ → q b a = false := by
          intro b hb hne
          by_contra hf
          exact hc_disj b hb b₀ hb₀ hne a (by simp) ⟨Bool.eq_true_of_not_eq_false hf, hq₀⟩
        have hsum_step :
            (cs.map (fun b => ((a :: as).filter (q b)).length)).sum =
            1 + (cs.map (fun b => (as.filter (q b)).length)).sum := by
          clear ih ih' hc_sub hcover hp
          induction cs with
          | nil => simp at hb₀
          | cons c rest ihcs =>
              rw [List.nodup_cons] at hnd
              rcases hnd with ⟨hc_notin, hrest_nd⟩
              simp only [List.mem_cons] at hb₀
              rcases hb₀ with rfl | hb₀_rest
              · have hc_eq : ((a :: as).filter (q b₀)).length = (as.filter (q b₀)).length + 1 := by
                  simp [hq₀]
                have hrest_eq : rest.map (fun b => ((a :: as).filter (q b)).length) =
                    rest.map (fun b => (as.filter (q b)).length) :=
                  List.map_congr_left fun b hb => by
                    simp [hnone b (by simp [hb]) (fun h => hc_notin (h ▸ hb))]
                simp only [List.map_cons, List.sum_cons, hc_eq, hrest_eq]; omega
              · have hne : c ≠ b₀ := fun h => by subst h; exact hc_notin hb₀_rest
                have hc_eq : ((a :: as).filter (q c)).length = (as.filter (q c)).length := by
                  simp [hnone c (by simp) hne]
                have ihres := ihcs hrest_nd
                  (fun b₁ hb₁ b₂ hb₂ hne x hx => hc_disj b₁ (by simp [hb₁]) b₂ (by simp [hb₂]) hne x hx)
                  hb₀_rest (fun b hb h => hnone b (by simp [hb]) h)
                simp only [List.map_cons, List.sum_cons, hc_eq, ihres]; omega
        simp [hp, ih', hsum_step]; omega
      · have hp_f : p a = false := Bool.eq_false_iff.2 hp
        have hqf_all : ∀ b ∈ cs, q b a = false := fun b hb => by
          by_contra ht
          exact hp (hc_sub b hb a (by simp) (Bool.eq_true_of_not_eq_false ht))
        have hmap_eq : cs.map (fun b => ((a :: as).filter (q b)).length) =
            cs.map (fun b => (as.filter (q b)).length) :=
          List.map_congr_left fun b hb => by simp [hqf_all b hb]
        simp [hp_f, hmap_eq, ih']

theorem lctRepSize_eq_one_add_sum (mem : ℕ → ℕ) (nb cap y : ℕ)
    (hle : ∀ x, 1 ≤ x → x ≤ cap → lctAuxParent mem nb cap x ≤ cap)
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent (lctAuxParent mem nb cap) cap u = 0)
    (hy1 : 1 ≤ y) (hy2 : y ≤ cap) :
    lctRepSize mem nb cap y =
      1 + ((((List.range cap).map (· + 1)).filter
        (fun c => decide (lctAuxParent mem nb cap c = y))).map
          (lctRepSize mem nb cap)).sum := by
  let par := lctAuxParent mem nb cap
  have hp0 : par 0 = 0 := lctAuxParent_zero mem nb cap
  let all := (List.range cap).map (· + 1)
  let cs := all.filter (fun c => decide (par c = y))
  have hall_nd : all.Nodup := List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)
  have hcs_nd : cs.Nodup := hall_nd.filter _
  have hy_in_all : y ∈ all := List.mem_map.2 ⟨y - 1, List.mem_range.2 (by omega), by omega⟩
  have hy_reaches : reachesIn par cap y y = true := by
    simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
    exact ⟨by omega, ⟨0, by omega, rfl⟩⟩
  let allNoY := all.filter (fun u => decide (u ≠ y))
  have hfilter_y_split :
      (all.filter (fun u => reachesIn par cap u y)).length =
      1 + (allNoY.filter (fun u => reachesIn par cap u y)).length := by
    clear cs hcs_nd
    suffices h : ∀ (L : List ℕ), L.Nodup → y ∈ L → reachesIn par cap y y = true →
        (L.filter (fun u => reachesIn par cap u y)).length =
        1 + ((L.filter (fun u => decide (u ≠ y))).filter (fun u => reachesIn par cap u y)).length from
      h all hall_nd hy_in_all hy_reaches
    intro L hnd hyL hyr
    induction L with
    | nil => simp at hyL
    | cons a as ih =>
        rw [List.nodup_cons] at hnd
        simp only [List.mem_cons] at hyL
        rcases hyL with rfl | hy_as
        · have hy_notin : y ∉ as := hnd.1
          have hsub : as.filter (fun u => decide (u ≠ y)) = as :=
            List.filter_eq_self.2 fun z hz => decide_eq_true (fun heq => hy_notin (heq ▸ hz))
          simp only [List.filter_cons, hyr, ↓reduceIte, ne_eq, not_true_eq_false, decide_false,
            Bool.false_eq_true, hsub, List.length_cons]
          omega
        · have hdt : decide (a ≠ y) = true := decide_eq_true (fun h => hnd.1 (h ▸ hy_as))
          simp only [List.filter_cons, hdt, ↓reduceIte]
          by_cases hreach : reachesIn par cap a y = true
          · simp only [hreach, ↓reduceIte, List.length_cons, ih hnd.2 hy_as]; omega
          · have hrf : reachesIn par cap a y = false := Bool.eq_false_iff.2 hreach
            simp only [hrf, Bool.false_eq_true, ↓reduceIte, ih hnd.2 hy_as]
  have hc_disj : ∀ c₁ ∈ cs, ∀ c₂ ∈ cs, c₁ ≠ c₂ → ∀ u ∈ allNoY,
      ¬ (reachesIn par cap u c₁ = true ∧ reachesIn par cap u c₂ = true) := by
    intro c₁ hc₁ c₂ hc₂ hne u _ ⟨hr1, hr2⟩
    simp only [cs, List.mem_filter, decide_eq_true_eq] at hc₁ hc₂
    simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
      at hr1 hr2
    rcases hr1 with ⟨_, k₁, _, hk₁⟩
    rcases hr2 with ⟨_, k₂, _, hk₂⟩
    have hc_cycle : ∀ {a b ka kb}, ka ≤ kb → a ≠ b → par a = y → par b = y →
        iterParent par ka u = a → iterParent par kb u = b → False := by
      intro a b ka kb hle_k hne_ab hpa hpb hia hib
      obtain ⟨d, hd_eq⟩ := Nat.exists_eq_add_of_le hle_k
      rw [hd_eq, iterParent_add, hia] at hib
      cases d with
      | zero => exact hne_ab (by simpa [iterParent] using hib)
      | succ d' =>
          have h1 : iterParent par (d' + 1) y = y := by
            rw [iterParent_succ_right, show iterParent par d' y = b by
              simpa [iterParent, hpa] using hib, hpb]
          exact iterParent_no_cycle hp0 hacyc hy1 hy2 (by omega) h1
    rcases Nat.le_total k₁ k₂ with h12 | h21
    · exact hc_cycle h12 hne hc₁.2 hc₂.2 hk₁ hk₂
    · exact hc_cycle h21 hne.symm hc₂.2 hc₁.2 hk₂ hk₁
  have hc_sub : ∀ c ∈ cs, ∀ u ∈ allNoY, reachesIn par cap u c = true →
      reachesIn par cap u y = true := by
    intro c hc u hu hrc
    simp only [allNoY, List.mem_filter, all, List.mem_map, List.mem_range, decide_eq_true_eq] at hu
    rcases hu with ⟨⟨x, _, rfl⟩, _⟩
    simp only [cs, List.mem_filter, decide_eq_true_eq] at hc
    exact (reachesIn_iff_self_or_child hp0 hle hacyc (by omega) (by omega) hy1 hy2).2
      (Or.inr ⟨c, hc.1, hc.2, hrc⟩)
  have hcover : ∀ u ∈ allNoY, reachesIn par cap u y = true →
      ∃ c ∈ cs, reachesIn par cap u c = true := by
    intro u hu hry
    simp only [allNoY, List.mem_filter, all, List.mem_map, List.mem_range, decide_eq_true_eq] at hu
    rcases hu with ⟨⟨x, _, rfl⟩, hne⟩
    have hiff := (reachesIn_iff_self_or_child hp0 hle hacyc (by omega) (by omega) hy1 hy2).1 hry
    rcases hiff with heq | ⟨c, hc_mem, hpc, hrc⟩
    · exact False.elim (hne heq)
    · exact ⟨c, List.mem_filter.2 ⟨hc_mem, decide_eq_true hpc⟩, hrc⟩
  have hlen := list_length_filter_disjoint_sum allNoY cs hcs_nd
    (fun u => reachesIn par cap u y) (fun c u => reachesIn par cap u c) hc_disj hc_sub hcover
  have hcs_filter : ∀ c ∈ cs,
      (allNoY.filter (fun u => reachesIn par cap u c)).length =
      (all.filter (fun u => reachesIn par cap u c)).length := by
    intro c hc
    have hpc : par c = y := of_decide_eq_true (List.mem_filter.1 hc).2
    have hnot_y : reachesIn par cap y c = false := by
      by_contra ht
      have hrt := Bool.eq_true_of_not_eq_false ht
      simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range] at hrt
      rcases hrt with ⟨_, k, _, hk⟩
      exact iterParent_no_cycle (d := k + 1) hp0 hacyc hy1 hy2 (by omega)
        (by rw [iterParent_succ_right, hk, hpc])
    clear hc_disj hc_sub hcover hlen hfilter_y_split
    have hcomm : allNoY.filter (fun u => reachesIn par cap u c) =
        (all.filter (fun u => reachesIn par cap u c)).filter (fun u => decide (u ≠ y)) := by
      dsimp only [allNoY]
      rw [List.filter_filter, List.filter_filter]
      exact List.filter_congr fun u _ => Bool.and_comm _ _
    rw [hcomm]
    apply congrArg List.length
    apply List.filter_eq_self.2
    intro u hu
    rw [List.mem_filter] at hu
    simp only [decide_eq_true_eq]
    intro heq
    rw [← heq, hu.2] at hnot_y
    exact absurd hnot_y (by decide)
  have hmap_len :
      cs.map (fun c => (allNoY.filter (fun u => reachesIn par cap u c)).length) =
      cs.map (lctRepSize mem nb cap) :=
    List.map_congr_left hcs_filter
  rw [lctRepSize, hfilter_y_split, hlen, hmap_len]

theorem listParentFrom_eq_of_mem {prev : ℕ} {xs : List ℕ} (hnd : xs.Nodup) :
    ∀ i (hi : i < xs.length),
      listParentFrom prev xs xs[i] = if i = 0 then prev else xs[i - 1]! := by
  induction xs generalizing prev with
  | nil => intro i hi; simp at hi
  | cons a as ih =>
      rw [List.nodup_cons] at hnd
      intro i hi
      cases i with
      | zero => simp [listParentFrom]
      | succ j =>
          have hj_lt : j < as.length := by simpa using hi
          have ha_ne : as[j] ≠ a := fun heq => hnd.1 (heq ▸ List.getElem_mem hj_lt)
          simp only [List.getElem_cons_succ, listParentFrom, ha_ne, ↓reduceIte]
          rw [ih hnd.2 (prev := a) j hj_lt]
          cases j <;> simp

theorem lctAuxParent_of_tree {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ} {trees : List AuxTree}
    (hok : SplayForestOk w h L mem nb cap trees)
    (hpp_le : ∀ t ∈ trees, nodeField mem nb t.rootId OFF_PPAR ≤ cap)
    {t : AuxTree} (ht : t ∈ trees) :
    let seq := lctTreeSeq mem nb cap t.rootId
    ∀ i (hi : i < seq.length),
      lctAuxParent mem nb cap seq[i] =
        if i = 0 then nodeField mem nb t.rootId OFF_PPAR else seq[i - 1]! := by
  intro seq i hi
  have hts_eq : seq = t.evalInorder (revFlag mem nb) false := hok.lctTreeSeq_eq ht
  have hnd_all : (trees.flatMap AuxTree.toList).Nodup :=
    hok.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hseq_nd : seq.Nodup := by
    rw [hts_eq]
    exact (t.evalInorder_perm (revFlag mem nb) false).nodup_iff.2
      (mem_nodup_of_flatMap_nodup hnd_all ht)
  have hu_mem : seq[i] ∈ seq := List.getElem_mem hi
  have hu_t : seq[i] ∈ t.toList := by
    have hu_ev : seq[i] ∈ t.evalInorder (revFlag mem nb) false := by rw [← hts_eq]; exact hu_mem
    exact (t.evalInorder_perm (revFlag mem nb) false).mem_iff.1 hu_ev
  have hr_mem : t.rootId ∈ auxRootIds mem nb cap :=
    hok.auxRootIds_perm.mem_iff.2 (List.mem_map.2 ⟨t, ht, rfl⟩)
  have hfind : (auxRootIds mem nb cap).findSome? (fun r => treeParentEntry mem nb cap r seq[i]) =
      treeParentEntry mem nb cap t.rootId seq[i] := by
    have hother : ∀ r ∈ auxRootIds mem nb cap, r ≠ t.rootId →
        treeParentEntry mem nb cap r seq[i] = none := by
      intro r hr hne
      rcases List.mem_map.1 (hok.auxRootIds_perm.mem_iff.1 hr) with ⟨s, hs, hrs⟩
      have hst : s ≠ t := fun h => hne (by rw [← hrs, h])
      have hnot_seq : seq[i] ∉ lctTreeSeq mem nb cap r := by
        rw [← hrs, hok.lctTreeSeq_eq hs]
        intro hm
        have hm_s := (s.evalInorder_perm (revFlag mem nb) false).mem_iff.1 hm
        exact hst (unique_tree_of_mem hnd_all hs ht hm_s hu_t)
      simp [treeParentEntry, hnot_seq]
    have haux_nd : (auxRootIds mem nb cap).Nodup :=
      (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)).filter _
    have hu_mem' : seq[i] ∈ lctTreeSeq mem nb cap t.rootId := hu_mem
    have go : ∀ rs : List ℕ, rs.Nodup → t.rootId ∈ rs →
        (∀ r ∈ rs, r ≠ t.rootId → treeParentEntry mem nb cap r seq[i] = none) →
        rs.findSome? (fun r => treeParentEntry mem nb cap r seq[i]) =
          treeParentEntry mem nb cap t.rootId seq[i] := by
      intro rs hnd_rs hmem_rs hother_rs
      induction rs with
      | nil => simp at hmem_rs
      | cons r rs ih =>
          rw [List.nodup_cons] at hnd_rs
          simp only [List.mem_cons] at hmem_rs
          rcases hmem_rs with rfl | hr_rs
          · simp only [List.findSome?, treeParentEntry, hu_mem', ↓reduceIte]
          · have hne : r ≠ t.rootId := fun h => hnd_rs.1 (h ▸ hr_rs)
            simp only [List.findSome?, hother_rs r (by simp) hne]
            exact ih hnd_rs.2 hr_rs (fun r' hr' => hother_rs r' (by simp [hr']))
    exact go _ haux_nd hr_mem hother
  have hpp := hpp_le t ht
  have hu_mem' : seq[i] ∈ lctTreeSeq mem nb cap t.rootId := hu_mem
  rw [lctAuxParent, hfind]
  dsimp only [treeParentEntry]
  simp only [hu_mem', hpp, ↓reduceIte]
  exact listParentFrom_eq_of_mem hseq_nd i hi

theorem treeSize_lctVSize_eq_repSize {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    {trees : List AuxTree} (hok : SplayForestOk w h L mem nb cap trees)
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent (lctAuxParent mem nb cap) cap u = 0)
    (hpp_le : ∀ t ∈ trees, nodeField mem nb t.rootId OFF_PPAR ≤ cap)
    (hne : ∀ t ∈ trees, lctTreeSeq mem nb cap t.rootId ≠ [])
    {t : AuxTree} (ht : t ∈ trees) :
    t.treeSize (lctVSize mem nb cap) =
      lctRepSize mem nb cap ((lctTreeSeq mem nb cap t.rootId).head (hne t ht)) := by
  let par := lctAuxParent mem nb cap
  have hnd_all : (trees.flatMap AuxTree.toList).Nodup :=
    hok.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hpar_le_cap : ∀ x, 1 ≤ x → x ≤ cap → par x ≤ cap :=
    fun x _ _ => lctAuxParent_le_cap mem nb cap x
  have hall_nd : ((List.range cap).map (· + 1)).Nodup :=
    List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)
  have hroot_tree : ∀ r ∈ auxRootIds mem nb cap, ∃ s ∈ trees, s.rootId = r := by
    intro r hr
    rcases List.mem_map.1 (hok.auxRootIds_perm.mem_iff.1 hr) with ⟨s, hs, hrs⟩
    exact ⟨s, hs, hrs⟩
  let seq := lctTreeSeq mem nb cap t.rootId
  have hseq_perm_t : seq.Perm t.toList := by
    dsimp only [seq]; rw [hok.lctTreeSeq_eq ht]; exact t.evalInorder_perm _ _
  have hseq_nd : seq.Nodup :=
    hseq_perm_t.nodup_iff.2 (mem_nodup_of_flatMap_nodup hnd_all ht)
  have hhead_inj : ∀ r₁ ∈ auxRootIds mem nb cap, ∀ r₂ ∈ auxRootIds mem nb cap,
      r₁ ≠ r₂ → ∀ h1 : lctTreeSeq mem nb cap r₁ ≠ [], ∀ h2 : lctTreeSeq mem nb cap r₂ ≠ [],
      (lctTreeSeq mem nb cap r₁).head h1 ≠ (lctTreeSeq mem nb cap r₂).head h2 := by
    intro r₁ hr₁ r₂ hr₂ hr_ne h1 h2 hhd_eq
    rcases hroot_tree r₁ hr₁ with ⟨s₁, hs₁, rfl⟩
    rcases hroot_tree r₂ hr₂ with ⟨s₂, hs₂, rfl⟩
    have hm₁ : ((lctTreeSeq mem nb cap s₁.rootId).head h1) ∈ s₁.toList := by
      have hm_ev : (lctTreeSeq mem nb cap s₁.rootId).head h1 ∈
          s₁.evalInorder (revFlag mem nb) false := by
        rw [← hok.lctTreeSeq_eq hs₁]; exact List.head_mem h1
      exact (s₁.evalInorder_perm (revFlag mem nb) false).mem_iff.1 hm_ev
    have hm₂ : ((lctTreeSeq mem nb cap s₂.rootId).head h2) ∈ s₂.toList := by
      have hm_ev : (lctTreeSeq mem nb cap s₂.rootId).head h2 ∈
          s₂.evalInorder (revFlag mem nb) false := by
        rw [← hok.lctTreeSeq_eq hs₂]; exact List.head_mem h2
      exact (s₂.evalInorder_perm (revFlag mem nb) false).mem_iff.1 hm_ev
    have hs_eq : s₁ = s₂ := unique_tree_of_mem hnd_all hs₁ hs₂ (hhd_eq ▸ hm₁) hm₂
    exact hr_ne (congrArg AuxTree.rootId hs_eq)
  have haux_nd : (auxRootIds mem nb cap).Nodup := hall_nd.filter _
  have hnode_step : ∀ j (hj : j < seq.length),
      lctRepSize mem nb cap seq[j] =
        (1 + lctVSize mem nb cap seq[j]) +
          (if _h : j + 1 < seq.length then lctRepSize mem nb cap seq[j + 1] else 0) := by
    intro j hj
    let y := seq[j]
    have hy_t : y ∈ t.toList := hseq_perm_t.mem_iff.1 (List.getElem_mem hj)
    have hy_b := (hok.trees_ok t ht).2.2.nodup_perm_mem hy_t
    have hy_eq := lctRepSize_eq_one_add_sum mem nb cap y hpar_le_cap hacyc hy_b.1 hy_b.2
    let cs := ((List.range cap).map (· + 1)).filter (fun c => decide (par c = y))
    let rlist := (auxRootIds mem nb cap).filter (fun r => decide (nodeField mem nb r OFF_PPAR = y))
    let dashedHeads := rlist.map (fun r =>
      match lctTreeSeq mem nb cap r with
      | [] => 0
      | hd :: _ => hd)
    have hdashed_sum : (dashedHeads.map (lctRepSize mem nb cap)).sum = lctVSize mem nb cap y := by
      simp only [dashedHeads, lctVSize, rlist, List.map_map]
      congr 1
      apply List.map_congr_left
      intro r hr
      rcases hroot_tree r (List.mem_filter.1 hr).1 with ⟨s, hs, rfl⟩
      rcases List.ne_nil_iff_exists_cons.1 (hne s hs) with ⟨hd, tl, hcons⟩
      simp [dashedChildSize, hcons]
    have hcs_nd : cs.Nodup := hall_nd.filter _
    have hrlist_nd : rlist.Nodup := haux_nd.filter _
    have hdh_nd : dashedHeads.Nodup := by
      rw [List.nodup_map_iff_inj_on hrlist_nd]
      intro r₁ hr₁ r₂ hr₂ heq
      by_contra hne_r
      have hr₁' := (List.mem_filter.1 hr₁).1
      have hr₂' := (List.mem_filter.1 hr₂).1
      rcases hroot_tree r₁ hr₁' with ⟨s₁, hs₁, rfl⟩
      rcases hroot_tree r₂ hr₂' with ⟨s₂, hs₂, rfl⟩
      have h1 := hne s₁ hs₁
      have h2 := hne s₂ hs₂
      rcases List.ne_nil_iff_exists_cons.1 h1 with ⟨a₁, l₁, ha₁⟩
      rcases List.ne_nil_iff_exists_cons.1 h2 with ⟨a₂, l₂, ha₂⟩
      exact hhead_inj s₁.rootId hr₁' s₂.rootId hr₂' hne_r h1 h2 (by simpa [ha₁, ha₂] using heq)
    have hdh_iff : ∀ c, c ∈ dashedHeads ↔
        ∃ r ∈ auxRootIds mem nb cap, nodeField mem nb r OFF_PPAR = y ∧
          ∃ (h : lctTreeSeq mem nb cap r ≠ []), c = (lctTreeSeq mem nb cap r).head h := by
      intro c
      simp only [dashedHeads, List.mem_map, rlist, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨r, ⟨hr, hpp⟩, hmatch⟩
        rcases hroot_tree r hr with ⟨s, hs, rfl⟩
        have hne_s := hne s hs
        rcases List.ne_nil_iff_exists_cons.1 hne_s with ⟨a, l, ha⟩
        exact ⟨s.rootId, hr, hpp, hne_s, by simpa [ha] using hmatch.symm⟩
      · rintro ⟨r, hr, hpp, hne_r, rfl⟩
        rcases List.ne_nil_iff_exists_cons.1 hne_r with ⟨a, l, ha⟩
        exact ⟨r, ⟨hr, hpp⟩, by simp [ha]⟩
    have hcs_iff : ∀ c, c ∈ cs ↔
        c ∈ dashedHeads ∨ (∃ (hj1 : j + 1 < seq.length), c = seq[j + 1]) := by
      intro c
      simp only [cs, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hpar_c⟩
        have hc_range : x + 1 ∈ (List.range cap).map (· + 1) :=
          List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩
        rcases List.mem_flatMap.1 (hok.perm.symm.mem_iff.1 hc_range) with ⟨s, hs, hcs_in⟩
        have hcs_seq : x + 1 ∈ lctTreeSeq mem nb cap s.rootId := by
          rw [hok.lctTreeSeq_eq hs]
          exact ((s.evalInorder_perm (revFlag mem nb) false).symm.mem_iff.1 hcs_in)
        rcases List.getElem_of_mem hcs_seq with ⟨idx, hidx, hidx_eq⟩
        have hpar_idx := lctAuxParent_of_tree hok hpp_le hs idx hidx
        rw [hidx_eq, show lctAuxParent mem nb cap (x + 1) = y from hpar_c] at hpar_idx
        cases idx with
        | zero =>
            left; rw [hdh_iff]
            have hr_in := hok.auxRootIds_perm.mem_iff.2 (List.mem_map.2 ⟨s, hs, rfl⟩)
            have hne_s := hne s hs
            refine ⟨s.rootId, hr_in, hpar_idx.symm, hne_s, ?_⟩
            rw [← hidx_eq]
            rcases List.ne_nil_iff_exists_cons.1 hne_s with ⟨a, l, ha⟩
            simp [ha]
        | succ k =>
            right
            simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hpar_idx
            have hk_lt : k < (lctTreeSeq mem nb cap s.rootId).length := by omega
            have hk_eq_val : (lctTreeSeq mem nb cap s.rootId)[k]! =
                (lctTreeSeq mem nb cap s.rootId)[k] := by
              simp [getElem!_def, List.getElem?_eq_getElem hk_lt]
            rw [hk_eq_val] at hpar_idx
            have hy_in_s : y ∈ s.toList := by
              rw [hpar_idx]
              have hm : (lctTreeSeq mem nb cap s.rootId)[k] ∈
                  s.evalInorder (revFlag mem nb) false := by
                rw [← hok.lctTreeSeq_eq hs]; exact List.getElem_mem hk_lt
              exact (s.evalInorder_perm (revFlag mem nb) false).mem_iff.1 hm
            have hst_eq : s = t := unique_tree_of_mem hnd_all hs ht hy_in_s hy_t
            subst hst_eq
            have hk_eq_j : k = j := (List.Nodup.getElem_inj_iff hseq_nd).1
              (by simpa [seq, y] using hpar_idx.symm)
            subst hk_eq_j
            exact ⟨hidx, by simpa [seq] using hidx_eq.symm⟩
      · rintro (hc_dh | ⟨hj1, rfl⟩)
        · rw [hdh_iff] at hc_dh
          rcases hc_dh with ⟨r, _, hpp, hne_r, rfl⟩
          rcases hroot_tree r (by assumption) with ⟨s, hs, rfl⟩
          have hm_ev : (lctTreeSeq mem nb cap s.rootId).head hne_r ∈
              s.evalInorder (revFlag mem nb) false := by
            rw [← hok.lctTreeSeq_eq hs]; exact List.head_mem hne_r
          have hb := (hok.trees_ok s hs).2.2.nodup_perm_mem
            ((s.evalInorder_perm (revFlag mem nb) false).mem_iff.1 hm_ev)
          have hpar0 := lctAuxParent_of_tree hok hpp_le hs 0 (List.length_pos_of_ne_nil hne_r)
          simp only [↓reduceIte, ← List.head_eq_getElem hne_r] at hpar0
          exact ⟨⟨(lctTreeSeq mem nb cap s.rootId).head hne_r - 1, by omega, by omega⟩,
            hpar0.trans hpp⟩
        · have hj1_t : seq[j + 1] ∈ t.toList := hseq_perm_t.mem_iff.1 (List.getElem_mem hj1)
          have hb := (hok.trees_ok t ht).2.2.nodup_perm_mem hj1_t
          have hpar1 := lctAuxParent_of_tree hok hpp_le ht (j + 1) hj1
          simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at hpar1
          exact ⟨⟨seq[j + 1] - 1, by omega, by omega⟩, by simpa [seq, y, hj] using hpar1⟩
    by_cases hj1 : j + 1 < seq.length
    · have hnotin_dh : seq[j + 1] ∉ dashedHeads := by
        intro hc_dh
        rw [hdh_iff] at hc_dh
        rcases hc_dh with ⟨r, _, _, hne_r, hhd⟩
        rcases hroot_tree r (by assumption) with ⟨s, hs, rfl⟩
        have hm_s : seq[j + 1] ∈ s.toList := by
          have hm1 : seq[j + 1] ∈ lctTreeSeq mem nb cap s.rootId := by
            rw [hhd]; exact List.head_mem hne_r
          rw [hok.lctTreeSeq_eq hs] at hm1
          exact (s.evalInorder_perm (revFlag mem nb) false).mem_iff.1 hm1
        have hst : s = t := unique_tree_of_mem hnd_all hs ht hm_s
          (hseq_perm_t.mem_iff.1 (List.getElem_mem hj1))
        subst hst
        have hne_0 : (0 : ℕ) ≠ j + 1 := Nat.zero_ne_add_one j
        exact hne_0 ((List.Nodup.getElem_inj_iff hseq_nd).1
          ((List.head_eq_getElem hne_r).symm.trans hhd.symm))
      have hcs_perm : cs.Perm (seq[j + 1] :: dashedHeads) :=
        (List.perm_ext_iff_of_nodup hcs_nd (List.nodup_cons.2 ⟨hnotin_dh, hdh_nd⟩)).2 fun c => by
          rw [hcs_iff c, List.mem_cons]
          exact ⟨fun h => h.elim Or.inr fun ⟨_, he⟩ => Or.inl he,
            fun h => h.elim (fun he => Or.inr ⟨hj1, he⟩) Or.inl⟩
      have hsum_eq : (cs.map (lctRepSize mem nb cap)).sum =
          lctRepSize mem nb cap seq[j + 1] + lctVSize mem nb cap y := by
        rw [(hcs_perm.map _).sum_eq, List.map_cons, List.sum_cons, hdashed_sum]
      simp only [hj1, ↓reduceDIte]
      change lctRepSize mem nb cap y = 1 + (cs.map (lctRepSize mem nb cap)).sum at hy_eq
      change lctRepSize mem nb cap y =
        1 + lctVSize mem nb cap y + lctRepSize mem nb cap seq[j + 1]
      rw [hy_eq, hsum_eq]; omega
    · have hcs_perm : cs.Perm dashedHeads :=
        (List.perm_ext_iff_of_nodup hcs_nd hdh_nd).2 fun c => by
          rw [hcs_iff c]
          exact ⟨fun h => h.elim id fun ⟨hbad, _⟩ => absurd hbad hj1, Or.inl⟩
      have hsum_eq : (cs.map (lctRepSize mem nb cap)).sum = lctVSize mem nb cap y := by
        rw [(hcs_perm.map _).sum_eq, hdashed_sum]
      simp only [hj1, ↓reduceDIte]
      change lctRepSize mem nb cap y = 1 + (cs.map (lctRepSize mem nb cap)).sum at hy_eq
      change lctRepSize mem nb cap y = 1 + lctVSize mem nb cap y + 0
      rw [hy_eq, hsum_eq]; omega
  have hfold : ∀ j, j ≤ seq.length →
      ((seq.drop j).map (fun y => 1 + lctVSize mem nb cap y)).sum =
      if _h : j < seq.length then lctRepSize mem nb cap seq[j] else 0 := by
    intro j hj
    have go : ∀ k, j + k = seq.length →
        ((seq.drop j).map (fun y => 1 + lctVSize mem nb cap y)).sum =
        if _h : j < seq.length then lctRepSize mem nb cap seq[j] else 0 := by
      intro k hk
      induction k generalizing j with
      | zero => simp [show j = seq.length by omega]
      | succ k ih =>
          have hj_lt : j < seq.length := by omega
          rw [List.drop_eq_getElem_cons hj_lt, List.map_cons, List.sum_cons, ih (j + 1) (by omega) (by omega)]
          simp only [hj_lt, ↓reduceDIte]
          exact (hnode_step j hj_lt).symm
    exact go (seq.length - j) (by omega)
  have h0 := hfold 0 (Nat.zero_le _)
  have hpos : 0 < seq.length := List.length_pos_of_ne_nil (hne t ht)
  simp only [List.drop_zero, hpos, ↓reduceDIte] at h0
  rw [← List.head_eq_getElem (hne t ht)] at h0
  rw [AuxTree.treeSize_eq_sum_evalInorder (revFlag mem nb) (lctVSize mem nb cap) t,
    ← hok.lctTreeSeq_eq ht]
  exact h0

end ParentAndRepSize

section PotentialAndRankBounds

private theorem log_lctCap_add_two_le (n : ℕ) :
    Nat.log 2 (lctCap n + 2) ≤ Nat.log 2 (n + 2) + 1 := by
  have hlt : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n + 2)
  have hlt2 : lctCap n + 2 < 2 ^ (Nat.log 2 (n + 2) + 2) := by
    have h2 : 2 ^ (Nat.log 2 (n + 2) + 2) = 2 * 2 ^ (Nat.log 2 (n + 2) + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    unfold lctCap
    omega
  exact Nat.lt_succ_iff.1 ((Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega)).2 hlt2)

/-- Every auxiliary tree `t ∈ x.trees` has `lctVSize`-weighted size at most `lctCap F.n`. -/
theorem treeSize_le_cap_of_invs {w h L : ℕ} {mem : ℕ → ℕ} {nb n : ℕ}
    {freeEdges : List ℕ} {trees : List AuxTree}
    (hsf : SplayForestOk w h L mem nb (lctCap n) trees)
    (hacyc : ∀ u, 1 ≤ u → u ≤ lctCap n → iterParent (lctAuxParent mem nb (lctCap n)) (lctCap n) u = 0)
    (haux : LctAuxPathOk mem nb n freeEdges trees)
    {t : AuxTree} (ht : t ∈ trees) :
    t.treeSize (lctVSize mem nb (lctCap n)) ≤ lctCap n := by
  have hpp_le : ∀ s ∈ trees, nodeField mem nb s.rootId OFF_PPAR ≤ lctCap n := by
    intro s hs
    rcases (haux s hs).2.1 with h0 | ⟨_, hle, _⟩ <;> omega
  have hne : ∀ s ∈ trees, lctTreeSeq mem nb (lctCap n) s.rootId ≠ [] := fun s hs => by
    rw [hsf.lctTreeSeq_eq hs]; exact (haux s hs).1
  rw [treeSize_lctVSize_eq_repSize hsf hacyc hpp_le hne ht]
  have hfilt : (((List.range (lctCap n)).map (· + 1)).filter
      (fun u => reachesIn (lctAuxParent mem nb (lctCap n)) (lctCap n) u
        ((lctTreeSeq mem nb (lctCap n) t.rootId).head (hne t ht)))).length ≤
      ((List.range (lctCap n)).map (· + 1)).length :=
    List.length_filter_le _ _
  simpa [lctRepSize, List.length_map, List.length_range] using hfilt

/-- Rank of any auxiliary tree in a represented forest is at most `Nat.log 2 (n + 2) + 1`. -/
theorem treeRank_le_log_of_invs {w h L : ℕ} {mem : ℕ → ℕ} {nb n : ℕ}
    {freeEdges : List ℕ} {trees : List AuxTree}
    (hsf : SplayForestOk w h L mem nb (lctCap n) trees)
    (hacyc : ∀ u, 1 ≤ u → u ≤ lctCap n → iterParent (lctAuxParent mem nb (lctCap n)) (lctCap n) u = 0)
    (haux : LctAuxPathOk mem nb n freeEdges trees)
    {t : AuxTree} (ht : t ∈ trees) :
    t.rank (lctVSize mem nb (lctCap n)) ≤ Nat.log 2 (n + 2) + 1 := by
  have hsz := treeSize_le_cap_of_invs hsf hacyc haux ht
  have hrk : t.rank (lctVSize mem nb (lctCap n)) ≤ Nat.log 2 (lctCap n + 2) := by
    unfold AuxTree.rank
    exact Nat.log_mono_right (by omega)
  exact le_trans hrk (log_lctCap_add_two_le n)

/-- Global potential `lctPhi` is bounded by `O((L + 1) * n * log(n + 2))`. -/
theorem lctPhi_le_bound_of_invs {w h L : ℕ} {mem : ℕ → ℕ} {b n : ℕ}
    {freeEdges : List ℕ} {trees : List AuxTree}
    (hsf : SplayForestOk w h L mem (lctNodesBase b) (lctCap n) trees)
    (hacyc : ∀ u, 1 ≤ u → u ≤ lctCap n →
      iterParent (lctAuxParent mem (lctNodesBase b) (lctCap n)) (lctCap n) u = 0)
    (haux : LctAuxPathOk mem (lctNodesBase b) n freeEdges trees) :
    lctPhi L mem b n ≤ 2 * (K_SPLAY_STEP L + C_HEAVY L) * n * (Nat.log 2 (n + 2) + 1) := by
  have hsz : ∀ t ∈ trees, t.treeSize (lctVSize mem (lctNodesBase b) (lctCap n)) ≤ lctCap n :=
    fun t ht => treeSize_le_cap_of_invs hsf hacyc haux ht
  have hsplay_le := splayMemPhi_le (K := K_SPLAY_STEP L) hsf hsz
  have hheavy_le : lctHeavyCount mem (lctNodesBase b) (lctCap n) ≤ lctCap n := by
    unfold lctHeavyCount auxRootIds
    have h1 := List.length_filter_le
      (fun r => isHeavyRoot mem (lctNodesBase b) (lctCap n) r)
      (((List.range (lctCap n)).map (· + 1)).filter
        (fun r => decide (nodeField mem (lctNodesBase b) r OFF_PARENT = 0)))
    have h2 := List.length_filter_le
      (fun r => decide (nodeField mem (lctNodesBase b) r OFF_PARENT = 0))
      ((List.range (lctCap n)).map (· + 1))
    simp only [List.length_map, List.length_range] at h2
    omega
  have hcap_le : lctCap n ≤ 2 * n := le_rfl
  have hlog_le : Nat.log 2 (lctCap n + 2) ≤ Nat.log 2 (n + 2) + 1 :=
    log_lctCap_add_two_le n
  unfold lctPhi
  have h1 : splayMemPhi (K_SPLAY_STEP L) mem (lctNodesBase b) (lctCap n)
      (lctVSize mem (lctNodesBase b) (lctCap n)) ≤
      2 * K_SPLAY_STEP L * n * (Nat.log 2 (n + 2) + 1) := by
    calc
      splayMemPhi (K_SPLAY_STEP L) mem (lctNodesBase b) (lctCap n)
          (lctVSize mem (lctNodesBase b) (lctCap n))
        ≤ K_SPLAY_STEP L * lctCap n * Nat.log 2 (lctCap n + 2) := hsplay_le
      _ ≤ K_SPLAY_STEP L * (2 * n) * (Nat.log 2 (n + 2) + 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hcap_le) hlog_le
      _ = 2 * K_SPLAY_STEP L * n * (Nat.log 2 (n + 2) + 1) := by ring
  have h2 : C_HEAVY L * lctHeavyCount mem (lctNodesBase b) (lctCap n) ≤
      2 * C_HEAVY L * n * (Nat.log 2 (n + 2) + 1) := by
    calc
      C_HEAVY L * lctHeavyCount mem (lctNodesBase b) (lctCap n)
        ≤ C_HEAVY L * (2 * n) := Nat.mul_le_mul_left _ (le_trans hheavy_le hcap_le)
      _ = 2 * C_HEAVY L * n * 1 := by ring
      _ ≤ 2 * C_HEAVY L * n * (Nat.log 2 (n + 2) + 1) :=
            Nat.mul_le_mul_left _ (Nat.succ_pos _)
  have hsum : 2 * K_SPLAY_STEP L * n * (Nat.log 2 (n + 2) + 1) +
      2 * C_HEAVY L * n * (Nat.log 2 (n + 2) + 1) =
      2 * (K_SPLAY_STEP L + C_HEAVY L) * n * (Nat.log 2 (n + 2) + 1) := by ring
  rw [← hsum]
  exact Nat.add_le_add h1 h2

end PotentialAndRankBounds

end MinCostFlow.LinkCut.Prog
