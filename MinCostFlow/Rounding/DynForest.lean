module

public import MinCostFlow.Rounding.Forest
import Mathlib.Data.List.Perm.Basic

/-!
# Dynamic forest specification (`DynForest`) and operation lemmas

This file completes the mathematical properties of `MathForest` (`pathAdd`, `pathSum`, `pathMin`,
`cut`, and `SameState` congruence), defines the abstract dynamic-forest interface `DynForest`
(data only) together with its specification predicate `DynForest.IsSpec`, and constructs the
canonical computable instance `mathDynForest : DynForest` satisfying `DynForest.IsSpec`.
-/

@[expose] public section

namespace MinCostFlow.Rounding

namespace MathForest

private theorem eq_of_eid_eq {es : List ForestEdge} (hnd : (es.map ForestEdge.eid).Nodup)
    {e₁ e₂ : ForestEdge} (h₁ : e₁ ∈ es) (h₂ : e₂ ∈ es) (heid : e₁.eid = e₂.eid) :
    e₁ = e₂ := by
  induction es with
  | nil => simp at h₁
  | cons z zs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h₁ with h1 | h₁ <;>
      rcases List.mem_cons.mp h₂ with h2 | h₂
    · exact h1.trans h2.symm
    · exact absurd (h1 ▸ heid ▸ List.mem_map_of_mem h₂) hnd.1
    · exact absurd (h2 ▸ heid.symm ▸ List.mem_map_of_mem h₁) hnd.1
    · exact ih hnd.2 h₁ h₂

theorem pathAdd_rawEdges (F : MathForest) (u v : ℕ) (δ : ℚ) :
    (F.pathAdd u v δ).rawEdges = F.rawEdges := by
  unfold pathAdd rawEdges
  cases findSteps F.edges u v with
  | none => rfl
  | some steps =>
    simp only [List.map_map, Function.comp_def, List.map_inj_left]
    intro a _
    unfold applyStepsDelta
    cases steps.find? fun s => s.edge.eid == a.eid with
    | none => rfl
    | some s => simp

theorem pathAdd_edges_length (F : MathForest) (u v : ℕ) (δ : ℚ) :
    (F.pathAdd u v δ).edges.length = F.edges.length := by
  unfold pathAdd
  cases findSteps F.edges u v with
  | none => rfl
  | some _ => simp

theorem pathAdd_valid {F : MathForest} (hV : F.Valid) (u v : ℕ) (δ : ℚ) :
    (F.pathAdd u v δ).Valid := by
  unfold pathAdd
  cases hfs : findSteps F.edges u v with
  | none => exact hV
  | some steps =>
    have apply_eid : ∀ e, (applyStepsDelta steps δ e).eid = e.eid := fun e => by
      unfold applyStepsDelta
      cases steps.find? fun s => s.edge.eid == e.eid with
      | none => rfl
      | some s => simp
    have apply_u : ∀ e, (applyStepsDelta steps δ e).u = e.u := fun e => by
      unfold applyStepsDelta
      cases steps.find? fun s => s.edge.eid == e.eid with
      | none => rfl
      | some s => simp
    have apply_v : ∀ e, (applyStepsDelta steps δ e).v = e.v := fun e => by
      unfold applyStepsDelta
      cases steps.find? fun s => s.edge.eid == e.eid with
      | none => rfl
      | some s => simp
    refine ⟨?_, ?_, ?_⟩
    · intro e' he'
      rw [List.mem_map] at he'
      obtain ⟨e, he, rfl⟩ := he'
      rw [apply_u, apply_v]
      exact hV.1 e he
    · have hmap : ((F.edges.map (applyStepsDelta steps δ)).map ForestEdge.eid) =
          F.edges.map ForestEdge.eid := by
        simp [List.map_map, Function.comp_def, apply_eid]
      rw [hmap]
      exact hV.2.1
    · have hraw : (F.edges.map (applyStepsDelta steps δ)).map ForestEdge.toRaw = F.rawEdges := by
        simpa only [pathAdd, rawEdges, hfs] using pathAdd_rawEdges F u v δ
      change IsAcyclic ((F.edges.map (applyStepsDelta steps δ)).map ForestEdge.toRaw)
      rw [hraw]
      exact hV.2.2

theorem pathAdd_sameComp (F : MathForest) (u v : ℕ) (δ : ℚ) (a b : ℕ) :
    (F.pathAdd u v δ).SameComp a b ↔ F.SameComp a b := by
  simp only [SameComp, pathAdd_rawEdges]

theorem applyStepsDelta_of_mem {F : MathForest} (hV : F.Valid)
    {u v : ℕ} {steps : List PathStep} (hfs : findSteps F.edges u v = some steps)
    (δ : ℚ) {s : PathStep} (hs : s ∈ steps) :
    applyStepsDelta steps δ s.edge = s.edge.addFlow s.fwd δ := by
  obtain ⟨hw, hnd⟩ := findSteps_sound hV.2.1 hfs
  have hnd_eid : (steps.map (fun t => t.edge.eid)).Nodup := by
    have hmem : ∀ t ∈ steps, t.edge ∈ F.edges := hw.mem_edges
    clear hfs hw hs
    induction steps with
    | nil => simp
    | cons x xs ih =>
      rw [List.map_cons, List.nodup_cons] at hnd ⊢
      refine ⟨fun hm => ?_, ih hnd.2 (fun t ht => hmem t (List.mem_cons_of_mem _ ht))⟩
      rw [List.mem_map] at hm
      obtain ⟨t, ht, heid⟩ := hm
      have hx_in := hmem x List.mem_cons_self
      have ht_in := hmem t (List.mem_cons_of_mem _ ht)
      have heq_edge : t.edge = x.edge := eq_of_eid_eq hV.2.1 ht_in hx_in heid
      exact hnd.1 (List.mem_map.mpr ⟨t, ht, by simp [PathStep.toRaw, heq_edge]⟩)
  have hfind : steps.find? (fun t => t.edge.eid == s.edge.eid) = some s := by
    clear hfs hw hnd
    induction steps with
    | nil => simp at hs
    | cons x xs ih =>
      rw [List.map_cons, List.nodup_cons] at hnd_eid
      simp only [List.find?]
      rcases List.mem_cons.mp hs with rfl | hs_tail
      · simp
      · have hne : x.edge.eid ≠ s.edge.eid := fun h =>
          hnd_eid.1 (h ▸ List.mem_map_of_mem hs_tail)
        have hbeq : (x.edge.eid == s.edge.eid) = false := beq_eq_false_iff_ne.mpr hne
        rw [hbeq]
        exact ih hs_tail hnd_eid.2
  simp [applyStepsDelta, hfind]

theorem applyStepsDelta_of_not_mem {F : MathForest} (hV : F.Valid)
    {u v : ℕ} {steps : List PathStep} (hfs : findSteps F.edges u v = some steps)
    (δ : ℚ) {e : ForestEdge} (he : e ∈ F.edges) (hnot : ∀ s ∈ steps, s.edge ≠ e) :
    applyStepsDelta steps δ e = e := by
  obtain ⟨hw, _⟩ := findSteps_sound hV.2.1 hfs
  have hnone : steps.find? (fun s => s.edge.eid == e.eid) = none := by
    rw [List.find?_eq_none]
    intro s hs
    simp only [beq_iff_eq]
    intro heq
    have hseq : s.edge = e := eq_of_eid_eq hV.2.1 (hw.mem_edges s hs) he heq
    exact hnot s hs hseq
  simp [applyStepsDelta, hnone]

theorem pathSum_reverse {F : MathForest} (hV : F.Valid) (u v : ℕ) :
    F.pathSum v u = -F.pathSum u v := by
  unfold pathSum
  cases hfs : findSteps F.edges u v with
  | none =>
    cases hrev : findSteps F.edges v u with
    | none => simp
    | some steps' =>
      have hfs' := findSteps_reverse hV hrev
      simp only [List.map_reverse] at hfs'
      rw [hfs] at hfs'
      simp at hfs'
  | some steps =>
    rw [findSteps_reverse hV hfs]
    exact stepsCost_reverse_flip steps

theorem pathMin_eq_none_iff {F : MathForest} (hV : F.Valid) {a b : ℕ}
    (hconn : F.SameComp a b) :
    F.pathMin a b = none ↔ a = b := by
  unfold pathMin
  obtain ⟨steps, hfs, hw, _⟩ := findSteps_some_of_sameComp hV hconn
  rw [hfs]
  simp only [Option.bind_some, stepsMinHit_eq_none_iff]
  constructor
  · intro hnil
    subst hnil
    exact IsStepWalk.nil_iff.mp hw
  · rintro rfl
    rw [findSteps_self] at hfs
    exact (Option.some.inj hfs).symm

private theorem filter_length_add_one {α : Type*} {l : List α} {p : α → Bool} {x : α}
    (hnd : l.Nodup) (hx : x ∈ l) (hpx : p x = false)
    (hother : ∀ y ∈ l, y ≠ x → p y = true) :
    (l.filter p).length + 1 = l.length := by
  induction l with
  | nil => simp at hx
  | cons z zs ih =>
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with rfl | hx_zs
    · have hfz : zs.filter p = zs := List.filter_eq_self.mpr fun y hy =>
        hother y (List.mem_cons_of_mem _ hy) (fun heq => hnd.1 (heq ▸ hy))
      simp [hpx, hfz]
    · have hne : z ≠ x := fun heq => hnd.1 (heq ▸ hx_zs)
      have hpz : p z = true := hother z List.mem_cons_self hne
      have ih' := ih hnd.2 hx_zs (fun y hy hyx => hother y (List.mem_cons_of_mem _ hy) hyx)
      simp [hpz]
      omega

/-- Cutting the edge returned by `pathMin a b` splits the simple path `a → b` cleanly into
the `a → hit.x` prefix and `hit.y → b` suffix, disconnecting `a` from `b`. -/
theorem cut_of_pathMin {F : MathForest} (hV : F.Valid) {a b : ℕ}
    {steps : List PathStep} (hfs : findSteps F.edges a b = some steps)
    {hit : PathHit} (hmin : stepsMinHit steps = some hit) :
    let F' := F.cut hit.x hit.y
    ∃ pre s post,
      steps = pre ++ s :: post ∧ s.toHit = hit ∧
      (∀ t ∈ pre, hit.avail < t.dirAvail) ∧
      (∀ t ∈ post, hit.avail ≤ t.dirAvail) ∧
      F'.Valid ∧
      (∀ e ∈ F'.edges, e ∈ F.edges ∧ e.eid ≠ hit.eid) ∧
      (∀ e ∈ F.edges, e.eid ≠ hit.eid → e ∈ F'.edges) ∧
      F'.edges.length + 1 = F.edges.length ∧
      findSteps F'.edges a hit.x = some pre ∧
      findSteps F'.edges hit.y b = some post ∧
      F'.SameComp a hit.x ∧ F'.SameComp hit.y b ∧ ¬ F'.SameComp a b := by
  intro F'
  obtain ⟨pre, s, post, hsplit, hs_hit, hpre_avail, hpost_avail⟩ := stepsMinHit_spec hmin
  obtain ⟨hw, hnd⟩ := findSteps_sound hV.2.1 hfs
  have hV' : F'.Valid := F.cut_valid hV hit.x hit.y
  have hs_in_steps : s ∈ steps := by rw [hsplit]; simp
  have hs_mem : s.edge ∈ F.edges := hw.mem_edges s hs_in_steps
  have hs_eid : s.edge.eid = hit.eid := by rw [← hs_hit]; rfl
  have hs_conn : (s.edge.u = hit.x ∧ s.edge.v = hit.y) ∨ (s.edge.u = hit.y ∧ s.edge.v = hit.x) := by
    have hx : hit.x = s.src := by rw [← hs_hit]; rfl
    have hy : hit.y = s.dst := by rw [← hs_hit]; rfl
    rw [hx, hy]
    rcases s with ⟨se, (_ | _)⟩ <;> simp [PathStep.src, PathStep.dst]
  have hp_cut : ∀ e ∈ F.edges,
      (!((e.u == hit.x && e.v == hit.y) || (e.u == hit.y && e.v == hit.x))) = true ↔
      e.eid ≠ hit.eid := by
    intro e he
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
      ne_eq]
    constructor
    · intro h heid
      have he_eq : e = s.edge := eq_of_eid_eq hV.2.1 he hs_mem (heid.trans hs_eid.symm)
      subst he_eq
      rcases hs_conn with ⟨hux, hvy⟩ | ⟨huy, hvx⟩
      · rcases h.1 with h1 | h2
        · exact h1 hux
        · exact h2 hvy
      · rcases h.2 with h1 | h2
        · exact h1 huy
        · exact h2 hvx
    · intro hne
      have he_ne_s : e ≠ s.edge := fun h => hne (h ▸ hs_eid)
      have hraw_ne : e.toRaw ≠ s.edge.toRaw := fun h =>
        he_ne_s (eq_of_eid_eq hV.2.1 he hs_mem (congrArg RawEdge.eid h))
      have hnp := hV.2.2.no_parallel (List.mem_map_of_mem he) (List.mem_map_of_mem hs_mem) hraw_ne
      constructor
      · by_cases hux : e.u = hit.x
        · right
          intro hvy
          apply hnp
          rcases hs_conn with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · exact Or.inl ⟨hux.trans hx.symm, hvy.trans hy.symm⟩
          · exact Or.inr ⟨hux.trans hy.symm, hvy.trans hx.symm⟩
        · exact Or.inl hux
      · by_cases huy : e.u = hit.y
        · right
          intro hvx
          apply hnp
          rcases hs_conn with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · exact Or.inr ⟨huy.trans hy.symm, hvx.trans hx.symm⟩
          · exact Or.inl ⟨huy.trans hx.symm, hvx.trans hy.symm⟩
        · exact Or.inl huy
  have hmem_F' : ∀ e, e ∈ F'.edges ↔ e ∈ F.edges ∧ e.eid ≠ hit.eid := by
    intro e
    simp only [F', cut, List.mem_filter]
    constructor
    · rintro ⟨he, hpred⟩
      exact ⟨he, (hp_cut e he).mp hpred⟩
    · rintro ⟨he, hne⟩
      exact ⟨he, (hp_cut e he).mpr hne⟩
  have hlen' : F'.edges.length + 1 = F.edges.length := by
    apply filter_length_add_one (hV.2.1.of_map _) hs_mem
    · by_contra htrue
      simp only [Bool.not_eq_false] at htrue
      exact ((hp_cut s.edge hs_mem).mp htrue) hs_eid
    · intro y hy hy_ne
      exact (hp_cut y hy).mpr (fun heid =>
        hy_ne (eq_of_eid_eq hV.2.1 hy hs_mem (heid.trans hs_eid.symm)))
  have hw_split := hw
  rw [hsplit] at hw_split
  obtain ⟨x', hpre_w, hrest_w⟩ := hw_split.split_append
  obtain ⟨hx_eq, hpost_w⟩ := hrest_w.src_dst_cons
  have hx' : x' = hit.x := by rw [← hx_eq, ← hs_hit]; rfl
  have hy' : s.dst = hit.y := by rw [← hs_hit]; rfl
  rw [hx'] at hpre_w
  rw [hy'] at hpost_w
  have hnd_split := hnd
  rw [hsplit, List.map_append, List.map_cons] at hnd_split
  have hraw_splits := hV.2.2.cut_splits (edges' := F'.rawEdges) s.edge.toRaw
    (fun z hz => by
      unfold rawEdges at hz ⊢
      rw [List.mem_map] at hz ⊢
      obtain ⟨e, he, rfl⟩ := hz
      exact ⟨e, (hmem_F' e).mp he |>.1, rfl⟩)
    (fun z hz hze => by
      unfold rawEdges at hz
      rw [List.mem_map] at hz
      obtain ⟨e, he, rfl⟩ := hz
      exact ((hmem_F' e).mp he).2 ((congrArg RawEdge.eid hze).trans hs_eid))
    (fun z hz hzne => by
      unfold rawEdges at hz ⊢
      rw [List.mem_map] at hz ⊢
      obtain ⟨e, he, rfl⟩ := hz
      refine ⟨e, (hmem_F' e).mpr ⟨he, fun heid => hzne ?_⟩, rfl⟩
      have he_eq := eq_of_eid_eq hV.2.1 he hs_mem (heid.trans hs_eid.symm)
      rw [he_eq])
    (by
      have := hw.to_isWalk
      rw [hsplit, List.map_append, List.map_cons] at this
      exact this)
    hnd_split
  obtain ⟨_, _, _, _, hnd_pre, _, hnd_post, hdisc⟩ := hraw_splits
  have hpre_mem : ∀ t ∈ pre, t.edge ∈ F'.edges := by
    intro t ht
    refine (hmem_F' t.edge).mpr ⟨hpre_w.mem_edges t ht, fun heid => ?_⟩
    have hm : s.edge.toRaw ∈ pre.map PathStep.toRaw := by
      have ht_raw : t.edge.toRaw ∈ pre.map PathStep.toRaw := List.mem_map_of_mem ht
      have heq := eq_of_eid_eq hV.2.1 (hpre_w.mem_edges t ht) hs_mem (heid.trans hs_eid.symm)
      exact heq ▸ ht_raw
    exact List.disjoint_of_nodup_append hnd_split hm List.mem_cons_self
  have hpost_mem : ∀ t ∈ post, t.edge ∈ F'.edges := by
    intro t ht
    refine (hmem_F' t.edge).mpr ⟨hpost_w.mem_edges t ht, fun heid => ?_⟩
    have hm : s.edge.toRaw ∈ post.map PathStep.toRaw := by
      have ht_raw : t.edge.toRaw ∈ post.map PathStep.toRaw := List.mem_map_of_mem ht
      have heq := eq_of_eid_eq hV.2.1 (hpost_w.mem_edges t ht) hs_mem (heid.trans hs_eid.symm)
      exact heq ▸ ht_raw
    exact (List.nodup_cons.mp hnd_split.of_append_right).1 hm
  have hpre_w' : IsStepWalk F'.edges a hit.x pre := hpre_w.mono_of_mem hpre_mem
  have hpost_w' : IsStepWalk F'.edges hit.y b post := hpost_w.mono_of_mem hpost_mem
  refine ⟨pre, s, post, hsplit, hs_hit, hpre_avail, hpost_avail, hV',
    fun e he => (hmem_F' e).mp he, fun e he hne => (hmem_F' e).mpr ⟨he, hne⟩,
    hlen',
    findSteps_eq_of_isStepWalk hV' hpre_w' hnd_pre,
    findSteps_eq_of_isStepWalk hV' hpost_w' hnd_post,
    ⟨_, hpre_w'.to_isWalk⟩, ⟨_, hpost_w'.to_isWalk⟩,
    fun ⟨q, hq⟩ => hdisc q hq⟩

theorem SameState.link {F₁ F₂ : MathForest} (h : F₁.SameState F₂) (e : ForestEdge) :
    (F₁.link e).SameState (F₂.link e) :=
  ⟨h.1, h.2.cons e⟩

theorem SameState.cut {F₁ F₂ : MathForest} (h : F₁.SameState F₂) (x y : ℕ) :
    (F₁.cut x y).SameState (F₂.cut x y) :=
  ⟨h.1, h.2.filter _⟩

theorem SameState.pathSum_eq {F₁ F₂ : MathForest} (h : F₁.SameState F₂) (hV : F₁.Valid)
    (u v : ℕ) : F₁.pathSum u v = F₂.pathSum u v := by
  simp only [pathSum, h.findSteps_eq hV u v]

theorem SameState.pathMin_eq {F₁ F₂ : MathForest} (h : F₁.SameState F₂) (hV : F₁.Valid)
    (u v : ℕ) : F₁.pathMin u v = F₂.pathMin u v := by
  simp only [pathMin, h.findSteps_eq hV u v]

theorem SameState.pathAdd {F₁ F₂ : MathForest} (h : F₁.SameState F₂) (hV : F₁.Valid)
    (u v : ℕ) (δ : ℚ) : (F₁.pathAdd u v δ).SameState (F₂.pathAdd u v δ) := by
  unfold MathForest.pathAdd
  rw [h.findSteps_eq hV u v]
  cases findSteps F₂.edges u v with
  | none => exact h
  | some steps => exact ⟨h.1, h.2.map _⟩

end MathForest

/-- Abstract dynamic-forest interface with the operations of Kang–Payor Section 2.1 (`Link`, `Cut`,
`FindRoot`, `PathAdd`, `PathMin`, `PathSum`). Contains only data and operations; its correctness
specification is `DynForest.IsSpec`. -/
structure DynForest where
  State : Type
  Inv : State → Prop
  toForest : State → MathForest
  init : ℕ → State
  findRoot : State → ℕ → ℕ
  link : State → ForestEdge → State
  cut : State → ℕ → ℕ → State
  pathAdd : State → ℕ → ℕ → ℚ → State
  pathMin : State → ℕ → ℕ → Option PathHit
  pathSum : State → ℕ → ℕ → ℤ

/-- Correctness specification of a `DynForest` in terms of `MathForest` (Kang–Payor Section 2.1):
every operation preserves `Inv` and updates `toForest` up to edge permutation (`SameState`) as
specified by `MathForest`. -/
def DynForest.IsSpec (D : DynForest) : Prop :=
  (∀ n, D.Inv (D.init n) ∧ (D.toForest (D.init n)).SameState (MathForest.empty n)) ∧
  (∀ st, D.Inv st → (D.toForest st).Valid) ∧
  (∀ st v, D.Inv st → v < (D.toForest st).n →
    D.findRoot st v < (D.toForest st).n ∧
    ∀ u < (D.toForest st).n,
      D.findRoot st u = D.findRoot st v ↔ (D.toForest st).SameComp u v) ∧
  (∀ st e, D.Inv st → e.u < (D.toForest st).n → e.v < (D.toForest st).n →
    ¬ (D.toForest st).SameComp e.u e.v → (∀ e' ∈ (D.toForest st).edges, e'.eid ≠ e.eid) →
    D.Inv (D.link st e) ∧ (D.toForest (D.link st e)).SameState ((D.toForest st).link e)) ∧
  (∀ st x y, D.Inv st →
    D.Inv (D.cut st x y) ∧ (D.toForest (D.cut st x y)).SameState ((D.toForest st).cut x y)) ∧
  (∀ st u v δ, D.Inv st → (D.toForest st).SameComp u v →
    D.Inv (D.pathAdd st u v δ) ∧
    (D.toForest (D.pathAdd st u v δ)).SameState ((D.toForest st).pathAdd u v δ)) ∧
  (∀ st u v, D.Inv st → (D.toForest st).SameComp u v →
    D.pathMin st u v = (D.toForest st).pathMin u v) ∧
  (∀ st u v, D.Inv st → (D.toForest st).SameComp u v →
    D.pathSum st u v = (D.toForest st).pathSum u v)

/-- Canonical computable `DynForest` backed directly by `MathForest`. -/
def mathDynForest : DynForest where
  State := MathForest
  Inv := MathForest.Valid
  toForest := id
  init := MathForest.empty
  findRoot := MathForest.findRoot
  link := MathForest.link
  cut := MathForest.cut
  pathAdd := MathForest.pathAdd
  pathMin := MathForest.pathMin
  pathSum := MathForest.pathSum

theorem mathDynForest_isSpec : mathDynForest.IsSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨MathForest.empty_valid n, MathForest.SameState.refl _⟩
  · intro st hst
    exact hst
  · intro st v hst hv
    exact ⟨MathForest.findRoot_lt hst hv, fun u hu => MathForest.findRoot_eq_iff hst hu hv⟩
  · intro st e hst hu hv hdisc heid
    exact ⟨MathForest.link_valid hst hu hv hdisc heid, MathForest.SameState.refl _⟩
  · intro st x y hst
    exact ⟨MathForest.cut_valid hst x y, MathForest.SameState.refl _⟩
  · intro st u v δ hst _
    exact ⟨MathForest.pathAdd_valid hst u v δ, MathForest.SameState.refl _⟩
  · intro st u v _ _
    rfl
  · intro st u v _ _
    rfl

end MinCostFlow.Rounding
