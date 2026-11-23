module

public import MinCostFlow.LinkCut.Prog.MathForestLinkSetup

/-!
# Path Analysis and Disconnection Proofs for `cut`

Provides path-structure analysis for `OFF_VCNT = 2` (`vcnt_eq_two_path`), no-op proofs when `cut`
leaves the forest unchanged (`cut_eq_self_of_bad_args`, `cut_eq_self_of_vcnt_ne_two`,
`cut_eq_self_of_ne_endpoints`), the splayed tree shape before edge removal (`cut_splayed_ed_shape`),
and `cut_edgeMap_perm_filter`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section CutPathAnalysis

private lemma cut_filter_false_iff {e : ForestEdge} {x y : ℕ}
    (hf : ¬ ((!(e.u == x && e.v == y || e.u == y && e.v == x)) = true)) :
    (e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x) := by
  cases hb : (e.u == x && e.v == y || e.u == y && e.v == x)
  · exact absurd (by simp [hb]) hf
  · simpa [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] using hb

private lemma cut_getElem!_eq {α : Type*} [Inhabited α] (l : List α) {i : ℕ} (hi : i < l.length) :
    l[i]! = l[i] := by
  simp [getElem!_def, List.getElem?_eq_getElem hi]

private lemma cut_getElem_zero_of_head? (l : List ℕ) (h0 : 0 < l.length) {a : ℕ}
    (hh : l.head? = some a) : l[0] = a := by
  cases l with
  | nil => simp at h0
  | cons x xs => simp only [List.head?_cons, Option.some.injEq] at hh; exact hh

private lemma cut_fst_inj_of_nodup : ∀ (l : List (ℕ × ForestEdge)), (l.map Prod.fst).Nodup →
    ∀ {a : ℕ} {e₁ e₂ : ForestEdge}, (a, e₁) ∈ l → (a, e₂) ∈ l → e₁ = e₂ := by
  intro l hnd a e₁ e₂ h1 h2
  induction l with
  | nil => simp at h1
  | cons p tl ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 h1 with h1eq | h1' <;> rcases List.mem_cons.1 h2 with h2eq | h2'
      · exact (Prod.mk.inj (h1eq.trans h2eq.symm)).2
      · subst h1eq
        exact absurd (List.mem_map.2 ⟨(a, e₂), h2', rfl⟩) hnd.1
      · subst h2eq
        exact absurd (List.mem_map.2 ⟨(a, e₁), h1', rfl⟩) hnd.1
      · exact ih hnd.2 h1' h2'

private lemma cut_isStepWalk_nil_eq {edges : List ForestEdge} {a b : ℕ}
    (hw : IsStepWalk edges a b []) : a = b := by
  match hw with
  | .nil _ => rfl

private lemma evalMemSteps_mem_props {mem : ℕ → ℕ} {nb h L : ℕ} :
    ∀ (t : AuxTree) (b : Bool) (δ : ℤ) {r : RawStep},
      r ∈ evalMemSteps mem nb h L t b δ →
      r.nodeId ∈ t.toList ∧ nodeField mem nb r.nodeId OFF_HASE ≠ 0 ∧
        r.eid = nodeField mem nb r.nodeId OFF_EID := by
  intro t
  induction t with
  | leaf =>
      intro b δ r hr
      simp [evalMemSteps] at hr
  | node id l r ih_l ih_r =>
      intro b δ step hs
      have hown : ∀ {b' : Bool} {s : RawStep},
          s ∈ (Option.map (fun s0 => RawStep.addDeltaMod h L (if b' = true then s0.flip else s0) δ)
            (nodeOwnRawStep mem nb h L id)).toList →
          s.nodeId = id ∧ nodeField mem nb id OFF_HASE ≠ 0 ∧ s.eid = nodeField mem nb id OFF_EID := by
        intro b' s hs_own
        simp only [nodeOwnRawStep] at hs_own
        by_cases h0 : nodeField mem nb id OFF_HASE = 0
        · simp [h0] at hs_own
        · simp only [h0, ite_false, Option.map_some, Option.toList_some, List.mem_singleton] at hs_own
          have hs_eq := hs_own.symm
          have heq1 : ∀ s0 : RawStep, (RawStep.addDeltaMod h L s0 δ).nodeId = s0.nodeId := fun s0 => by
            unfold RawStep.addDeltaMod; split_ifs <;> rfl
          have heq2 : ∀ s0 : RawStep, (RawStep.addDeltaMod h L s0 δ).eid = s0.eid := fun s0 => by
            unfold RawStep.addDeltaMod; split_ifs <;> rfl
          have heq3 : ∀ s0 : RawStep,
              (if b' = true then s0.flip else s0).nodeId = s0.nodeId ∧
              (if b' = true then s0.flip else s0).eid = s0.eid := fun s0 => by
            cases b' <;> simp [RawStep.flip]
          rw [← hs_eq, heq1, heq2, (heq3 _).1, (heq3 _).2]
          exact ⟨rfl, h0, rfl⟩
      have hs' : step ∈
          (if b = true then evalMemSteps mem nb h L r (b ^^ revFlag mem nb id)
              (δ + if b = true then -nodeTagInt mem nb h L id else nodeTagInt mem nb h L id) ++
            (Option.map (fun s => RawStep.addDeltaMod h L (if b = true then s.flip else s) δ)
              (nodeOwnRawStep mem nb h L id)).toList ++
            evalMemSteps mem nb h L l (b ^^ revFlag mem nb id)
              (δ + if b = true then -nodeTagInt mem nb h L id else nodeTagInt mem nb h L id)
          else evalMemSteps mem nb h L l (b ^^ revFlag mem nb id)
              (δ + if b = true then -nodeTagInt mem nb h L id else nodeTagInt mem nb h L id) ++
            (Option.map (fun s => RawStep.addDeltaMod h L (if b = true then s.flip else s) δ)
              (nodeOwnRawStep mem nb h L id)).toList ++
            evalMemSteps mem nb h L r (b ^^ revFlag mem nb id)
              (δ + if b = true then -nodeTagInt mem nb h L id else nodeTagInt mem nb h L id)) := hs
      cases hb : b
      · simp only [hb, Bool.false_eq_true, ite_false, List.mem_append] at hs'
        rcases hs' with (h1 | h1) | h1
        · have res := ih_l _ _ h1
          exact ⟨by simp [AuxTree.toList, res.1], res.2.1, res.2.2⟩
        · rcases hown (b' := false) (by simpa [hb] using h1) with ⟨hid, hh, he⟩
          exact ⟨by simp [AuxTree.toList, hid], by simpa [hid] using hh, by simpa [hid] using he⟩
        · have res := ih_r _ _ h1
          exact ⟨by simp [AuxTree.toList, res.1], res.2.1, res.2.2⟩
      · simp only [hb, ite_true, List.mem_append] at hs'
        rcases hs' with (h1 | h1) | h1
        · have res := ih_r _ _ h1
          exact ⟨by simp [AuxTree.toList, res.1], res.2.1, res.2.2⟩
        · rcases hown (b' := true) (by simpa [hb] using h1) with ⟨hid, hh, he⟩
          exact ⟨by simp [AuxTree.toList, hid], by simpa [hid] using hh, by simpa [hid] using he⟩
        · have res := ih_l _ _ h1
          exact ⟨by simp [AuxTree.toList, res.1], res.2.1, res.2.2⟩

private lemma listVcnt_sum_filter {mem : ℕ → ℕ} {nb : ℕ} :
    ∀ {xs : List ℕ},
      (∀ u ∈ xs,
        (nodeField mem nb u OFF_ISV = 1 ∧ nodeField mem nb u OFF_HASE = 0) ∨
        (nodeField mem nb u OFF_ISV = 0 ∧ nodeField mem nb u OFF_HASE = 1)) →
      listVcnt mem nb xs = (xs.filter (fun u => decide (nodeField mem nb u OFF_ISV ≠ 0))).length ∧
      listVcnt mem nb xs + (xs.filter (fun u => decide (nodeField mem nb u OFF_HASE ≠ 0))).length =
        xs.length := by
  intro xs hxs
  induction xs with
  | nil => simp [listVcnt]
  | cons a tl ih =>
      have ha := hxs a List.mem_cons_self
      have htl := ih (fun u hu => hxs u (List.mem_cons_of_mem _ hu))
      have hv_eq : listVcnt mem nb (a :: tl) = nodeField mem nb a OFF_ISV + listVcnt mem nb tl := rfl
      rw [hv_eq]
      rcases ha with ⟨hisv, hhase⟩ | ⟨hisv, hhase⟩
      · have hf1 : (a :: tl).filter (fun u => decide (nodeField mem nb u OFF_ISV ≠ 0)) =
            a :: tl.filter (fun u => decide (nodeField mem nb u OFF_ISV ≠ 0)) :=
          List.filter_cons_of_pos (by simp [hisv])
        have hf2 : (a :: tl).filter (fun u => decide (nodeField mem nb u OFF_HASE ≠ 0)) =
            tl.filter (fun u => decide (nodeField mem nb u OFF_HASE ≠ 0)) :=
          List.filter_cons_of_neg (by simp [hhase])
        rw [hf1, hf2, List.length_cons, List.length_cons, hisv, htl.1]
        omega
      · have hf1 : (a :: tl).filter (fun u => decide (nodeField mem nb u OFF_ISV ≠ 0)) =
            tl.filter (fun u => decide (nodeField mem nb u OFF_ISV ≠ 0)) :=
          List.filter_cons_of_neg (by simp [hisv])
        have hf2 : (a :: tl).filter (fun u => decide (nodeField mem nb u OFF_HASE ≠ 0)) =
            a :: tl.filter (fun u => decide (nodeField mem nb u OFF_HASE ≠ 0)) :=
          List.filter_cons_of_pos (by simp [hhase])
        rw [hf1, hf2, List.length_cons, List.length_cons, hisv, htl.1]
        omega

private lemma isStep_of_edge_endpoints {edges : List ForestEdge} {e : ForestEdge}
    (he : e ∈ edges) {x y : ℕ} (hxy : (e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x)) :
    IsStepWalk edges x y [{ edge := e, fwd := decide (e.u = x) }] := by
  by_cases hux : e.u = x
  · have hvy : e.v = y := by
      rcases hxy with ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact h2.trans (hux.symm.trans h1)
    rw [decide_eq_true hux]
    exact IsStepWalk.fwd he hux (by rw [hvy]; exact IsStepWalk.nil y)
  · rcases hxy with ⟨h1, _⟩ | ⟨hvy, hux'⟩
    · exact absurd h1 hux
    · rw [decide_eq_false hux]
      exact IsStepWalk.bwd he hux' (by rw [hvy]; exact IsStepWalk.nil y)

/-- Two edges in a valid `MathForest` connecting the same unordered vertex pair are equal. -/
theorem eq_edge_of_endpoints {F : MathForest} (hV : F.Valid) {e₁ e₂ : ForestEdge}
    (h1 : e₁ ∈ F.edges) (h2 : e₂ ∈ F.edges) {x y : ℕ}
    (hxy1 : (e₁.u = x ∧ e₁.v = y) ∨ (e₁.u = y ∧ e₁.v = x))
    (hxy2 : (e₂.u = x ∧ e₂.v = y) ∨ (e₂.u = y ∧ e₂.v = x)) :
    e₁ = e₂ := by
  have hw1 := isStep_of_edge_endpoints h1 hxy1
  have hw2 := isStep_of_edge_endpoints h2 hxy2
  have hf1 := MathForest.findSteps_eq_of_isStepWalk hV hw1 (List.nodup_singleton _)
  have hf2 := MathForest.findSteps_eq_of_isStepWalk hV hw2 (List.nodup_singleton _)
  have heq : ([{ edge := e₁, fwd := decide (e₁.u = x) }] : List PathStep) =
      [{ edge := e₂, fwd := decide (e₂.u = x) }] := Option.some.inj (hf1.symm.trans hf2)
  have hhd := congrArg List.head? heq
  simp only [List.head?_cons, Option.some.injEq] at hhd
  exact congrArg PathStep.edge hhd

/-- When `x ≥ F.n ∨ y ≥ F.n ∨ x = y` on a valid forest, `F.cut x y = F`. -/
theorem cut_eq_self_of_bad_args {F : MathForest} (hV : F.Valid) {x y : ℕ}
    (hbad : F.n ≤ x ∨ F.n ≤ y ∨ x = y) : F.cut x y = F := by
  suffices h : F.edges.filter (fun e => !(e.u == x && e.v == y || e.u == y && e.v == x)) = F.edges by
    have hcut : F.cut x y = ⟨F.n, F.edges.filter (fun e => !(e.u == x && e.v == y || e.u == y && e.v == x))⟩ := rfl
    rw [hcut, h]
  rw [List.filter_eq_self]
  intro e he
  rcases hV.1 e he with ⟨hu, hv⟩
  by_contra hf
  have hf' := cut_filter_false_iff hf
  rcases hbad with hx | hy | hxy
  · rcases hf' with ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega
  · rcases hf' with ⟨_, h2⟩ | ⟨h1, _⟩ <;> omega
  · subst hxy
    rcases hf' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    · have hwalk := isStep_of_edge_endpoints he (Or.inl ⟨rfl, h2.trans h1.symm⟩)
      have hc := hV.2.2 e.u [e.toRaw] hwalk.to_isWalk (List.nodup_singleton _)
      simp at hc

private lemma list_length_ge_three_of_distinct {l : List ℕ} {a b c : ℕ}
    (ha : a ∈ l) (hb : b ∈ l) (hc : c ∈ l) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ l.length := by
  have hnd : ([a, b, c] : List ℕ).Nodup := by simp [hab, hac, hbc]
  have hsub : [a, b, c] ⊆ l := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  simpa using hnd.length_le_of_subset hsub

private lemma cut_mem_pair_of {u x y a b : ℕ} (hu1 : 1 ≤ u)
    (hf : a = x ∧ b = y ∨ a = y ∧ b = x) (hpe : a = u - 1 ∨ b = u - 1) :
    u = x + 1 ∨ u = y + 1 := by
  omega

private lemma seq_head_getLast_eq_singleton {α : Type*} {l : List α} (hnd : l.Nodup)
    {a : α} (hh : l.head? = some a) (hl : l.getLast? = some a) : l = [a] := by
  cases l with
  | nil => simp at hh
  | cons x xs =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      cases xs with
      | nil => rfl
      | cons y ys =>
          have hlast : (x :: y :: ys).getLast (by simp) = x := by
            rw [List.getLast?_eq_some_getLast (by simp)] at hl
            exact Option.some.inj hl
          have hmem : (x :: y :: ys).getLast (by simp) ∈ y :: ys := by
            have := List.getLast_mem (l := y :: ys) (by simp)
            simp [List.getLast_cons (by simp : (y :: ys) ≠ [])]
          rw [hlast] at hmem
          rw [List.nodup_cons] at hnd
          exact absurd hmem hnd.1

private lemma seq_len_three_of_head_last_mid {α : Type*} {l : List α} {a m b : α}
    (hlen : l.length = 3) (hh : l.head? = some a) (hl : l.getLast? = some b)
    (hm : m ∈ l) (hma : m ≠ a) (hmb : m ≠ b) : l = [a, m, b] := by
  rcases l with _ | ⟨x₀, _ | ⟨x₁, _ | ⟨x₂, _ | xs⟩⟩⟩ <;> simp at hlen
  simp only [List.head?_cons, Option.some.injEq] at hh
  have hl' : ([x₀, x₁, x₂] : List α).getLast? = some x₂ := rfl
  rw [hl] at hl'
  injection hl' with hx₂
  subst hh hx₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · exact absurd rfl hma
  · rfl
  · exact absurd rfl hmb

private lemma cut_eq_of_eid_eq {es : List ForestEdge} (hnd : (es.map ForestEdge.eid).Nodup)
    {e₁ e₂ : ForestEdge} (h1 : e₁ ∈ es) (h2 : e₂ ∈ es) (heid : e₁.eid = e₂.eid) : e₁ = e₂ := by
  induction es with
  | nil => simp at h1
  | cons a tl ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.1 h1 with rfl | h1' <;> rcases List.mem_cons.1 h2 with rfl | h2'
      · rfl
      · exact absurd (by rw [heid]; exact List.mem_map_of_mem h2') hnd.1
      · exact absurd (by rw [← heid]; exact List.mem_map_of_mem h1') hnd.1
      · exact ih hnd.2 h1' h2'

private lemma cut_forAll2_nodeIds_edges {w h L P b n a₀ b₀ : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {trees : List AuxTree} {mem : ℕ → ℕ} {F : MathForest}
    {t : AuxTree} {steps : List PathStep}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap trees mem)
    (ht : t ∈ trees) (hV : F.Valid)
    (hperme : (edgeMap.map Prod.snd).Perm F.edges)
    (hslots : (edgeMap.map Prod.fst ++ freeEdges).Perm ((List.range n).map (n + 1 + ·)))
    (hw : IsStepWalk F.edges a₀ b₀ steps)
    (hf2 : List.Forall₂ (fun r s => ∃ ed, stepMatchesEdge P ed s.edge r ∧ s.fwd = r.fwd)
      (evalMemSteps mem (lctNodesBase b) h L t false 0) steps) :
    ∀ i (hi_lt : i < steps.length),
      ∃ r ∈ evalMemSteps mem (lctNodesBase b) h L t false 0,
        (r.nodeId, steps[i].edge) ∈ edgeMap ∧
        r.nodeId ∈ AuxTree.evalInorder (revFlag mem (lctNodesBase b)) t false := by
  intro i hi_lt
  have hlen := hf2.length_eq
  have hi_l : i < (evalMemSteps mem (lctNodesBase b) h L t false 0).length := hlen ▸ hi_lt
  set rs := evalMemSteps mem (lctNodesBase b) h L t false 0
  have hrel := (List.forall₂_iff_get.1 hf2).2 i hi_l hi_lt
  rcases hrel with ⟨ed', hmatch, _⟩
  have hr_mem : rs[i] ∈ evalMemSteps mem (lctNodesBase b) h L t false 0 := List.getElem_mem hi_l
  rcases evalMemSteps_mem_props t false 0 hr_mem with ⟨ht_mem, hhase, heid_eq⟩
  have hflat_mem : rs[i].nodeId ∈ trees.flatMap AuxTree.toList := List.mem_flatMap.2 ⟨t, ht, ht_mem⟩
  have hr_range : rs[i].nodeId ∈ List.map (fun x => x + 1) (List.range (lctCap n)) :=
    hi.sf.perm.subset hflat_mem
  rcases List.mem_map.1 hr_range with ⟨k, hk_lt, hk_eq⟩
  have hk_lt' : k < lctCap n := List.mem_range.1 hk_lt
  have hn_lt_nid : n + 1 ≤ rs[i].nodeId := by
    by_contra hlt
    have hk_v : rs[i].nodeId - 1 < n := by omega
    have hv_ok := hi.vertexOk (rs[i].nodeId - 1) hk_v
    have hpos : 1 ≤ rs[i].nodeId := by omega
    have hsucc : rs[i].nodeId - 1 + 1 = rs[i].nodeId := by omega
    rw [hsucc] at hv_ok
    exact hhase hv_ok.2
  have hn_free : rs[i].nodeId ∉ freeEdges := fun hfr =>
    hhase (hi.freeNodeOk rs[i].nodeId hfr).2.2.2.2.2
  have hslot_mem : rs[i].nodeId ∈ edgeMap.map Prod.fst ++ freeEdges := by
    refine hslots.symm.subset ?_
    refine List.mem_map.2 ⟨rs[i].nodeId - (n + 1), List.mem_range.2 ?_, by omega⟩
    unfold lctCap at hk_lt'; omega
  rcases List.mem_append.1 hslot_mem with hem | hfr
  · rcases List.mem_map.1 hem with ⟨p, hp_em, hp_fst⟩
    have hp_ok := hi.edgeOk p hp_em
    have hpe_F : p.2 ∈ F.edges := hperme.subset (List.mem_map_of_mem hp_em)
    have hstep_F : steps[i].edge ∈ F.edges := hw.mem_edges steps[i] (List.getElem_mem hi_lt)
    have heid_p : p.2.eid = steps[i].edge.eid := by
      have h1 : nodeField mem (lctNodesBase b) p.1 OFF_EID = p.2.eid := hp_ok.2.2.2.2.1
      have h2 : (rs.get ⟨i, hi_l⟩).eid = (steps.get ⟨i, hi_lt⟩).edge.eid := hmatch.2.1
      change rs[i].eid = steps[i].edge.eid at h2
      rw [hp_fst, ← heid_eq, h2] at h1
      exact h1.symm
    have hp_eq : p.2 = steps[i].edge := cut_eq_of_eid_eq hV.2.1 hpe_F hstep_F heid_p
    refine ⟨rs[i], hr_mem, ?_, (AuxTree.evalInorder_perm (revFlag mem (lctNodesBase b)) t false).mem_iff.2 ht_mem⟩
    rw [← hp_fst, ← hp_eq]
    exact hp_em
  · exact absurd hfr hn_free

private lemma isStepWalk_cons_spec {edges : List ForestEdge} {a b : ℕ} {s : PathStep}
    {rest : List PathStep} (hw : IsStepWalk edges a b (s :: rest)) :
    s.edge ∈ edges ∧ PathStep.src s = a ∧ IsStepWalk edges (PathStep.dst s) b rest ∧
      ((s.edge.u = a ∧ s.edge.v = PathStep.dst s) ∨ (s.edge.v = a ∧ s.edge.u = PathStep.dst s)) := by
  match hw with
  | .fwd h1 h2 hrest => exact ⟨h1, by simp [PathStep.src, h2], hrest, Or.inl ⟨h2, rfl⟩⟩
  | .bwd h1 h2 hrest => exact ⟨h1, by simp [PathStep.src, h2], hrest, Or.inr ⟨h2, rfl⟩⟩

private lemma isStepWalk_mid_props {edges : List ForestEdge} {z y : ℕ} {s₁ s₂ : PathStep}
    {rest : List PathStep} (hw : IsStepWalk edges z y (s₁ :: s₂ :: rest)) :
    PathStep.src s₁ = z ∧ PathStep.dst s₁ = PathStep.src s₂ ∧
      ((s₁.edge.u = z ∧ s₁.edge.v = PathStep.dst s₁) ∨ (s₁.edge.v = z ∧ s₁.edge.u = PathStep.dst s₁)) ∧
      ((s₂.edge.u = PathStep.dst s₁ ∧ s₂.edge.v = PathStep.dst s₂) ∨
        (s₂.edge.v = PathStep.dst s₁ ∧ s₂.edge.u = PathStep.dst s₂)) ∧
      IsStepWalk edges (PathStep.dst s₁) y (s₂ :: rest) := by
  rcases isStepWalk_cons_spec hw with ⟨_, hs1, hrest, hend1⟩
  rcases isStepWalk_cons_spec hrest with ⟨_, hs2, _, hend2⟩
  exact ⟨hs1, hs2.symm, hend1, hend2, hrest⟩

/-- When `t₂ = .node (y + 1) l₂ .leaf` is top-level exposed (`OFF_PPAR = 0`), ends at `y + 1`,
and has `OFF_VCNT = 2`, the exposed path in memory must be `[z + 1, ed, y + 1]` for a unique
neighbor `z < n` (`z ≠ y`) and active edge `(ed, e) ∈ edgeMap` with `ed = OFF_MIN1_FIRST`. -/
theorem vcnt_eq_two_path {w h L P b n y : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {l₂ : AuxTree} {rest₂ : List AuxTree} {mem : ℕ → ℕ}
    {F : MathForest} {x₂ : LctConc}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (.node (y + 1) l₂ .leaf :: rest₂) mem)
    (hrep : LctMemRep w h L P b F x₂ mem)
    (hperme : (edgeMap.map Prod.snd).Perm F.edges)
    (hslots : (edgeMap.map Prod.fst ++ freeEdges).Perm ((List.range n).map (n + 1 + ·)))
    (ht₂_x : AuxTree.node (y + 1) l₂ .leaf ∈ x₂.trees)
    (hy : y < n) (hFn : F.n = n)
    (hpp_y : nodeField mem (lctNodesBase b) (y + 1) OFF_PPAR = 0)
    (hlast_y : (AuxTree.evalInorder (revFlag mem (lctNodesBase b)) (.node (y + 1) l₂ .leaf) false).getLast? =
      some (y + 1))
    (hvcnt : nodeField mem (lctNodesBase b) (y + 1) OFF_VCNT = 2) :
    ∃ z e s,
      z < n ∧ z ≠ y ∧
      nodeField mem (lctNodesBase b) (y + 1) OFF_MIN1_FIRST ∈
        (AuxTree.node (y + 1) l₂ .leaf).toList ∧
      (nodeField mem (lctNodesBase b) (y + 1) OFF_MIN1_FIRST, e) ∈ edgeMap ∧ e ∈ F.edges ∧
      ((e.u = z ∧ e.v = y) ∨ (e.u = y ∧ e.v = z)) ∧
      nodeField mem (lctNodesBase b) (y + 1) OFF_MIN1_HAS = 1 ∧
      AuxTree.evalInorder (revFlag mem (lctNodesBase b)) (.node (y + 1) l₂ .leaf) false =
        [z + 1, nodeField mem (lctNodesBase b) (y + 1) OFF_MIN1_FIRST, y + 1] ∧
      findSteps F.edges z y = some [s] ∧ s.edge = e := by
  let nb := lctNodesBase b
  let t₂ := AuxTree.node (y + 1) l₂ .leaf
  let seq := AuxTree.evalInorder (revFlag mem nb) t₂ false
  have ht₂_mem : t₂ ∈ AuxTree.node (y + 1) l₂ .leaf :: rest₂ := List.mem_cons_self
  have htm : TreeMemMatch w h L mem nb (lctCap n) t₂ 0 (nodeField mem nb (y + 1) OFF_PPAR) :=
    (hi.sf.trees_ok t₂ ht₂_mem).2.2
  have hvcnt_eq : nodeField mem nb (y + 1) OFF_VCNT = listVcnt mem nb seq :=
    (htm.rootAggs hi.sf.2.2.2.2.2.2.2.1).1
  have hlist_vcnt : listVcnt mem nb seq = 2 := by rw [← hvcnt_eq]; exact hvcnt
  have hnd_all := hi.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hseq_perm : seq.Perm t₂.toList := AuxTree.evalInorder_perm (revFlag mem nb) t₂ false
  have hseq_nd : seq.Nodup := by
    rw [List.flatMap_cons, List.nodup_append] at hnd_all
    exact hseq_perm.nodup_iff.2 hnd_all.1
  have hnode_class : ∀ u ∈ seq,
      (u ≤ n ∧ nodeField mem nb u OFF_ISV = 1 ∧ nodeField mem nb u OFF_HASE = 0) ∨
      (n + 1 ≤ u ∧ u ∉ freeEdges ∧ ∃ p ∈ edgeMap, p.1 = u ∧
        nodeField mem nb u OFF_ISV = 0 ∧ nodeField mem nb u OFF_HASE = 1) := by
    intro u hu
    have hu_t2 : u ∈ t₂.toList := hseq_perm.subset hu
    have hu_flat : u ∈ (AuxTree.node (y + 1) l₂ .leaf :: rest₂).flatMap AuxTree.toList :=
      List.mem_flatMap.2 ⟨t₂, ht₂_mem, hu_t2⟩
    have hu_rng : u ∈ List.map (fun k => k + 1) (List.range (lctCap n)) :=
      hi.sf.perm.subset hu_flat
    rcases List.mem_map.1 hu_rng with ⟨k, hk_lt, rfl⟩
    have hk_lt' : k < lctCap n := List.mem_range.1 hk_lt
    by_cases hkn : k < n
    · have hv_ok := hi.vertexOk k hkn
      exact Or.inl ⟨by omega, hv_ok.1, hv_ok.2⟩
    · have hu_nfree : k + 1 ∉ freeEdges := fun hfr => by
        have hf_ok := hi.freeNodeOk (k + 1) hfr
        have heq_t : AuxTree.node (k + 1) .leaf .leaf = t₂ :=
          unique_tree_of_mem hnd_all hf_ok.2.2.1 ht₂_mem (by simp [AuxTree.toList]) hu_t2
        have hroot := congrArg AuxTree.rootId heq_t
        dsimp [AuxTree.rootId, t₂] at hroot
        omega
      have hslot : k + 1 ∈ edgeMap.map Prod.fst ++ freeEdges := by
        refine hslots.symm.subset (List.mem_map.2 ⟨k - n, List.mem_range.2 ?_, by omega⟩)
        unfold lctCap at hk_lt'; omega
      rcases List.mem_append.1 hslot with hem | hfr
      · rcases List.mem_map.1 hem with ⟨p, hp_em, hp_fst⟩
        have he_ok := hi.edgeOk p hp_em
        refine Or.inr ⟨by omega, hu_nfree, p, hp_em, hp_fst, ?_, ?_⟩
        · rw [← hp_fst]; exact he_ok.2.2.1
        · rw [← hp_fst]; exact he_ok.2.2.2.1
      · exact absurd hfr hu_nfree
  have hseq_sum := listVcnt_sum_filter (mem := mem) (nb := nb) (xs := seq) (fun u hu => by
    rcases hnode_class u hu with ⟨_, h1, h2⟩ | ⟨_, _, _, _, _, h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩)
  have hne_seq : seq ≠ [] := (hi.auxPathOk t₂ ht₂_mem).1
  have hpp_le : ∀ s ∈ (AuxTree.node (y + 1) l₂ AuxTree.leaf :: rest₂),
      nodeField mem nb s.rootId OFF_PPAR ≤ lctCap n := fun s hs => by
    dsimp only [nb]
    rcases (hi.auxPathOk s hs).2.1 with h0 | ⟨_, h2, _⟩ <;> omega
  have hpar_seq_idx : ∀ i (hi_lt : i < seq.length),
      lctAuxParent mem nb (lctCap n) seq[i] =
        if i = 0 then nodeField mem nb t₂.rootId OFF_PPAR else seq[i - 1]! := by
    have htree_seq : lctTreeSeq mem (lctNodesBase b) (lctCap n) t₂.rootId = seq :=
      hi.sf.lctTreeSeq_eq ht₂_mem
    have hpar := lctAuxParent_of_tree hi.sf hpp_le ht₂_mem
    simpa [nb, htree_seq] using hpar
  cases hseq_eq : seq with
  | nil => exact absurd hseq_eq hne_seq
  | cons h₀ tl =>
      have hh0_mem : h₀ ∈ seq := hseq_eq ▸ List.mem_cons_self
      have hpar_h0 : lctAuxParent mem nb (lctCap n) h₀ = 0 := by
        have h0 := hpar_seq_idx 0 (by rw [hseq_eq]; simp)
        simp only [hseq_eq, List.getElem_cons_zero, ite_true] at h0
        rw [h0]; exact hpp_y
      have hz_range : h₀ ≤ n ∧ 1 ≤ h₀ := by
        rcases hnode_class h₀ hh0_mem with ⟨h1, _⟩ | ⟨_, _, p, hp_em, rfl, _⟩
        · have hmem_flat : h₀ ∈ (AuxTree.node (y + 1) l₂ .leaf :: rest₂).flatMap AuxTree.toList :=
            List.mem_flatMap.2 ⟨t₂, ht₂_mem, hseq_perm.subset hh0_mem⟩
          have hu_rng : h₀ ∈ List.map (fun k => k + 1) (List.range (lctCap n)) :=
            hi.sf.perm.subset hmem_flat
          rcases List.mem_map.1 hu_rng with ⟨k, _, rfl⟩
          exact ⟨h1, by omega⟩
        · exfalso
          dsimp only [nb] at hpar_h0
          rcases hi.subdivOk.2.2.2 p hp_em with ⟨hp1, _⟩ | ⟨hp1, _⟩ <;> omega
      let z := h₀ - 1
      have hz_lt : z < n := by omega
      have hz_add : z + 1 = h₀ := by omega
      have hhead_z : seq.head? = some (z + 1) := by
        rw [hseq_eq]; simp [hz_add]
      have hne_zy : z ≠ y := by
        intro hzy
        subst hzy
        have hsing : seq = [z + 1] := seq_head_getLast_eq_singleton hseq_nd hhead_z hlast_y
        have h1 : listVcnt mem nb [z + 1] = 1 := by
          dsimp only [nb]
          simp [listVcnt, (hi.vertexOk z hz_lt).1]
        rw [hsing] at hlist_vcnt
        omega
      rcases hrep.pathTree_isStepWalk ht₂_x (hFn ▸ hz_lt) (hFn ▸ hy) hpp_y hhead_z hlast_y with
        ⟨steps, hfs, hw_z, hnd_steps, hf2⟩
      rcases hrep.pathMin_eq ht₂_x (hFn ▸ hz_lt) (hFn ▸ hy) hne_zy hpp_y hhead_z hlast_y with
        ⟨_, rmin, _, _, hm1_has, hm1_first, hrmin_toList, _, _, _⟩
      dsimp only [AuxTree.rootId] at hm1_has hm1_first
      have hsteps_ne : steps ≠ [] := by
        intro hemp; subst hemp
        exact hne_zy (cut_isStepWalk_nil_eq hw_z)
      have hsteps_not_ge2 : ¬ (2 ≤ steps.length) := by
        intro hge2
        rcases steps with _ | ⟨s₁, _ | ⟨s₂, rest_s⟩⟩
        · simp at hge2
        · simp at hge2
        · have hmid := isStepWalk_mid_props hw_z
          let m := s₁.dst
          rcases cut_forAll2_nodeIds_edges hi ht₂_mem hrep.valid hperme hslots hw_z hf2
              0 (by simp) with ⟨r₁, _, hr1_em, hr1_seq⟩
          rcases cut_forAll2_nodeIds_edges hi ht₂_mem hrep.valid hperme hslots hw_z hf2
              1 (by simp) with ⟨r₂, _, hr2_em, hr2_seq⟩
          have hnd_em : (edgeMap.map Prod.fst).Nodup :=
            (hslots.nodup_iff.2 (List.nodup_range.map (fun _ _ h => by omega))).of_append_left
          have hr_ne : r₁.nodeId ≠ r₂.nodeId := fun heq => by
            have he12 : s₁.edge = s₂.edge := cut_fst_inj_of_nodup edgeMap hnd_em hr1_em (heq ▸ hr2_em)
            rw [List.map_cons, List.map_cons, List.nodup_cons] at hnd_steps
            apply hnd_steps.1
            have hraw : s₁.toRaw = s₂.toRaw := by simp [PathStep.toRaw, he12]
            exact hraw ▸ List.mem_cons_self
          have he_bds := hrep.valid.1 s₁.edge (hw_z.mem_edges s₁ List.mem_cons_self)
          have hm_lt_n : m < n := by
            dsimp only [m]
            rcases hmid.2.2.1 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
          have hm_ne_z : m ≠ z := fun hmz => by
            rcases hmid.2.2.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have hwalk1 := isStep_of_edge_endpoints (hw_z.mem_edges s₁ List.mem_cons_self)
                (Or.inl ⟨h1, h2.trans hmz⟩)
              have hc := hrep.valid.2.2 z _ hwalk1.to_isWalk (List.nodup_singleton _)
              simp at hc
            · have hwalk1 := isStep_of_edge_endpoints (hw_z.mem_edges s₁ List.mem_cons_self)
                (Or.inr ⟨h2.trans hmz, h1⟩)
              have hc := hrep.valid.2.2 z _ hwalk1.to_isWalk (List.nodup_singleton _)
              simp at hc
          have hm_ne_y : m ≠ y := fun hmy => by
            have hw_tail : IsStepWalk F.edges y y (s₂ :: rest_s) := by
              simpa [m, hmy] using hmid.2.2.2.2
            have hnd_tail : ((s₂ :: rest_s).map PathStep.toRaw).Nodup := by
              rw [List.map_cons, List.nodup_cons] at hnd_steps
              exact hnd_steps.2
            have hc := hrep.valid.2.2 y _ hw_tail.to_isWalk hnd_tail
            simp at hc
          have hm_mem_seq : m + 1 ∈ seq := by
            have hsub1 := hi.subdivOk.2.2.2 (r₁.nodeId, s₁.edge) hr1_em
            have hsub2 := hi.subdivOk.2.2.2 (r₂.nodeId, s₂.edge) hr2_em
            have hchoice : lctAuxParent mem nb (lctCap n) r₁.nodeId = m + 1 ∨
                lctAuxParent mem nb (lctCap n) r₂.nodeId = m + 1 := by
              dsimp only [nb, m] at hsub1 hsub2 ⊢
              have hor1 : lctAuxParent mem (lctNodesBase b) (lctCap n) r₁.nodeId = s₁.dst + 1 ∨
                  lctAuxParent mem (lctNodesBase b) (lctCap n) (s₁.dst + 1) = r₁.nodeId := by
                rcases hmid.2.2.1 with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rcases hsub1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
                · exact Or.inr (by rw [← h2]; exact hb)
                · exact Or.inl (by rw [← h2]; exact ha)
                · exact Or.inl (by rw [← h2]; exact ha)
                · exact Or.inr (by rw [← h2]; exact hb)
              have hor2 : lctAuxParent mem (lctNodesBase b) (lctCap n) r₂.nodeId = s₁.dst + 1 ∨
                  lctAuxParent mem (lctNodesBase b) (lctCap n) (s₁.dst + 1) = r₂.nodeId := by
                rcases hmid.2.2.2.1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases hsub2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
                · exact Or.inl (by rw [← h1]; exact ha)
                · exact Or.inr (by rw [← h1]; exact hb)
                · exact Or.inr (by rw [← h1]; exact hb)
                · exact Or.inl (by rw [← h1]; exact ha)
              rcases hor1 with h1 | h1
              · exact Or.inl h1
              · rcases hor2 with h2 | h2
                · exact Or.inr h2
                · exact absurd (h1.symm.trans h2) hr_ne
            have hmem_of_par_seq : ∀ {w : ℕ}, w ∈ seq → lctAuxParent mem nb (lctCap n) w = m + 1 →
                m + 1 ∈ seq := by
              intro w hw_seq hw_par
              rcases List.getElem_of_mem hw_seq with ⟨i, hi_lt, rfl⟩
              have hi_pos : 0 < i := by
                by_contra h0
                have hiz : i = 0 := by omega
                subst hiz
                have hzero := hpar_seq_idx 0 hi_lt
                simp only [ite_true] at hzero
                dsimp only [nb, t₂, AuxTree.rootId] at hzero
                rw [hpp_y] at hzero
                have h0' : m + 1 = 0 := hw_par.symm.trans hzero
                omega
              have hp_idx := hpar_seq_idx i hi_lt
              have hne0 : i ≠ 0 := by omega
              simp only [hne0, ite_false] at hp_idx
              have hprev : i - 1 < seq.length := by omega
              rw [cut_getElem!_eq seq hprev, hw_par] at hp_idx
              rw [hp_idx]
              exact List.getElem_mem hprev
            rcases hchoice with h1 | h2
            · exact hmem_of_par_seq hr1_seq h1
            · exact hmem_of_par_seq hr2_seq h2
          have hz_mem_seq : z + 1 ∈ seq := by rw [hseq_eq, hz_add]; exact List.mem_cons_self
          have hy_mem_seq : y + 1 ∈ seq := hseq_perm.symm.subset (by simp [t₂, AuxTree.toList])
          have hm_isv : nodeField mem nb (m + 1) OFF_ISV = 1 := (hi.vertexOk m hm_lt_n).1
          have hz_isv : nodeField mem nb (z + 1) OFF_ISV = 1 := (hi.vertexOk z hz_lt).1
          have hy_isv : nodeField mem nb (y + 1) OFF_ISV = 1 := (hi.vertexOk y hy).1
          have hge3 := list_length_ge_three_of_distinct
            (l := seq.filter (fun u => decide (nodeField mem nb u OFF_ISV ≠ 0)))
            (a := z + 1) (b := m + 1) (c := y + 1)
            (List.mem_filter.2 ⟨hz_mem_seq, by simp [hz_isv]⟩)
            (List.mem_filter.2 ⟨hm_mem_seq, by simp [hm_isv]⟩)
            (List.mem_filter.2 ⟨hy_mem_seq, by simp [hy_isv]⟩)
            (by omega) (by omega) (by omega)
          have hsum1 := hseq_sum.1
          rw [hlist_vcnt] at hsum1
          omega
      rcases steps with _ | ⟨s, _ | ⟨s', tl_s⟩⟩
      · exact absurd rfl hsteps_ne
      · have hw1 : IsStepWalk F.edges z y [s] := hw_z
        have hed_mem_t2 : nodeField mem nb (y + 1) OFF_MIN1_FIRST ∈ t₂.toList := by
          rw [hm1_first]; exact hrmin_toList
        have he_end : (s.edge.u = z ∧ s.edge.v = y) ∨ (s.edge.u = y ∧ s.edge.v = z) := by
          rcases isStepWalk_cons_spec hw1 with ⟨_, hsrc, hrest, hend⟩
          have hdst : s.dst = y := cut_isStepWalk_nil_eq hrest
          rw [hdst] at hend
          rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h2, h1⟩
        have hs_eval_len : (evalMemSteps mem nb h L t₂ false 0).length = 1 := hf2.length_eq
        have hr_ex := cut_forAll2_nodeIds_edges hi ht₂_mem hrep.valid hperme hslots hw1 hf2 0 (by simp)
        rcases hr_ex with ⟨r0, hr0_mem, hr0_em, hr0_seq⟩
        have hrs_sing : evalMemSteps mem nb h L t₂ false 0 = [r0] := by
          cases hms : evalMemSteps mem nb h L t₂ false 0 with
          | nil => simp [hms] at hs_eval_len
          | cons a tl' =>
              simp only [hms, List.length_cons] at hs_eval_len
              have htl_nil : tl' = [] := List.length_eq_zero_iff.1 (by omega)
              subst htl_nil
              rw [hms, List.mem_singleton] at hr0_mem
              rw [hr0_mem]
        have hrmin_eq : rmin = r0 := by
          have := ‹rmin ∈ evalMemSteps mem nb h L t₂ false 0›
          rw [hrs_sing, List.mem_singleton] at this
          exact this
        have hlen_seq : seq.length = 3 := by
          have hmap := congrArg List.length (evalMemSteps_map_nodeId mem nb h L t₂ false 0)
          rw [List.length_map, hs_eval_len] at hmap
          have hsum2 : listVcnt mem nb seq +
              (seq.filter (fun u => decide (nodeField mem nb u OFF_HASE ≠ 0))).length = seq.length :=
            hseq_sum.2
          dsimp only [seq] at hsum2
          rw [hlist_vcnt, ← hmap] at hsum2
          exact hsum2.symm
        have hed_eq_r0 : nodeField mem nb (y + 1) OFF_MIN1_FIRST = r0.nodeId := by
          rw [hm1_first, hrmin_eq]
        have hseq_full : seq = [z + 1, r0.nodeId, y + 1] := by
          have hne1 : r0.nodeId ≠ z + 1 := by
            have := hi.edgeOk (r0.nodeId, s.edge) hr0_em
            omega
          have hne2 : r0.nodeId ≠ y + 1 := by
            have := hi.edgeOk (r0.nodeId, s.edge) hr0_em
            omega
          exact seq_len_three_of_head_last_mid hlen_seq hhead_z hlast_y hr0_seq hne1 hne2
        refine ⟨z, s.edge, s, hz_lt, hne_zy, hed_mem_t2, ?_,
          hw1.mem_edges s List.mem_cons_self, he_end, hm1_has, ?_, hfs, rfl⟩
        · rw [hed_eq_r0]; exact hr0_em
        · rw [hed_eq_r0]; exact hseq_full
      · exact absurd (by simp : 2 ≤ (s :: s' :: tl_s).length) hsteps_not_ge2

/-- When `vcnt ≠ 2` after `reroot x ;; expose y`, no direct edge connects `x` and `y`, so
`F.cut x y = F`. -/
theorem cut_eq_self_of_vcnt_ne_two {w h L P b n x y : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {l₂ : AuxTree} {rest₂ : List AuxTree} {mem : ℕ → ℕ}
    {F : MathForest} {x₂ : LctConc}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (.node (y + 1) l₂ .leaf :: rest₂) mem)
    (hrep : LctMemRep w h L P b F x₂ mem)
    (hperme : (edgeMap.map Prod.snd).Perm F.edges)
    (hslots : (edgeMap.map Prod.fst ++ freeEdges).Perm ((List.range n).map (n + 1 + ·)))
    (ht₂_x : AuxTree.node (y + 1) l₂ .leaf ∈ x₂.trees)
    (hx : x < n) (hy : y < n) (hne : x ≠ y) (hFn : F.n = n)
    (hpp_y : nodeField mem (lctNodesBase b) (y + 1) OFF_PPAR = 0)
    (hsame_head : F.SameComp x y →
      (AuxTree.evalInorder (revFlag mem (lctNodesBase b)) (.node (y + 1) l₂ .leaf) false).head? =
        some (x + 1))
    (hlast_y : (AuxTree.evalInorder (revFlag mem (lctNodesBase b)) (.node (y + 1) l₂ .leaf) false).getLast? =
      some (y + 1))
    (hvcnt : nodeField mem (lctNodesBase b) (y + 1) OFF_VCNT ≠ 2) :
    F.cut x y = F := by
  suffices h : F.edges.filter (fun e => !(e.u == x && e.v == y || e.u == y && e.v == x)) = F.edges by
    have hcut : F.cut x y = ⟨F.n, F.edges.filter (fun e => !(e.u == x && e.v == y || e.u == y && e.v == x))⟩ := rfl
    rw [hcut, h]
  rw [List.filter_eq_self]
  intro e he
  by_contra hf
  have hf' := cut_filter_false_iff hf
  let nb := lctNodesBase b
  let t₂ := AuxTree.node (y + 1) l₂ .leaf
  let seq := AuxTree.evalInorder (revFlag mem nb) t₂ false
  have ht₂_mem : t₂ ∈ AuxTree.node (y + 1) l₂ .leaf :: rest₂ := List.mem_cons_self
  have hwalk1 : IsStepWalk F.edges x y [{ edge := e, fwd := decide (e.u = x) }] :=
    isStep_of_edge_endpoints he hf'
  have hsc : F.SameComp x y := ⟨[e.toRaw], hwalk1.to_isWalk⟩
  have hhead : seq.head? = some (x + 1) := hsame_head hsc
  rcases hrep.pathTree_isStepWalk ht₂_x (hFn ▸ hx) (hFn ▸ hy) hpp_y hhead hlast_y with
    ⟨steps, hfs, _, _, hf2⟩
  have hfs1 := MathForest.findSteps_eq_of_isStepWalk hrep.valid hwalk1 (List.nodup_singleton _)
  have hsteps_sing : steps = [{ edge := e, fwd := decide (e.u = x) }] :=
    Option.some.inj (hfs.symm.trans hfs1)
  have hsteps_len : steps.length = 1 := by rw [hsteps_sing]; rfl
  have htm : TreeMemMatch w h L mem nb (lctCap n) t₂ 0 (nodeField mem nb (y + 1) OFF_PPAR) :=
    (hi.sf.trees_ok t₂ ht₂_mem).2.2
  have hvcnt_eq : nodeField mem nb (y + 1) OFF_VCNT = listVcnt mem nb seq :=
    (htm.rootAggs hi.sf.2.2.2.2.2.2.2.1).1
  have hnd_all := hi.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hseq_perm : seq.Perm t₂.toList := AuxTree.evalInorder_perm (revFlag mem nb) t₂ false
  have hnode_class : ∀ u ∈ seq,
      (u ≤ n ∧ nodeField mem nb u OFF_ISV = 1 ∧ nodeField mem nb u OFF_HASE = 0) ∨
      (n + 1 ≤ u ∧ nodeField mem nb u OFF_ISV = 0 ∧ nodeField mem nb u OFF_HASE = 1) := by
    intro u hu
    have hu_t2 := hseq_perm.subset hu
    have hu_flat : u ∈ (AuxTree.node (y + 1) l₂ .leaf :: rest₂).flatMap AuxTree.toList :=
      List.mem_flatMap.2 ⟨t₂, ht₂_mem, hu_t2⟩
    have hu_rng := hi.sf.perm.subset hu_flat
    rcases List.mem_map.1 hu_rng with ⟨k, hk_lt, rfl⟩
    have hk_lt' := List.mem_range.1 hk_lt
    by_cases hkn : k < n
    · have hv := hi.vertexOk k hkn; exact Or.inl ⟨by omega, hv.1, hv.2⟩
    · have hu_nfree : k + 1 ∉ freeEdges := fun hfr => by
        have hf_ok := hi.freeNodeOk (k + 1) hfr
        have heq_t := unique_tree_of_mem hnd_all hf_ok.2.2.1 ht₂_mem
          (by simp [AuxTree.toList]) hu_t2
        have hroot := congrArg AuxTree.rootId heq_t
        dsimp [AuxTree.rootId, t₂] at hroot; omega
      have hslot : k + 1 ∈ edgeMap.map Prod.fst ++ freeEdges := by
        refine hslots.symm.subset (List.mem_map.2 ⟨k - n, List.mem_range.2 ?_, by omega⟩)
        unfold lctCap at hk_lt'; omega
      rcases List.mem_append.1 hslot with hem | hfr
      · rcases List.mem_map.1 hem with ⟨p, hp_em, hp_fst⟩
        have he_ok := hi.edgeOk p hp_em
        rw [← hp_fst]; exact Or.inr ⟨by omega, he_ok.2.2.1, he_ok.2.2.2.1⟩
      · exact absurd hfr hu_nfree
  have hseq_sum := listVcnt_sum_filter (mem := mem) (nb := nb) (xs := seq) (fun u hu => by
    rcases hnode_class u hu with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> [exact Or.inl ⟨h1, h2⟩; exact Or.inr ⟨h1, h2⟩])
  have hr_ex := cut_forAll2_nodeIds_edges hi ht₂_mem hrep.valid hperme hslots
    (hsteps_sing ▸ hwalk1) hf2 0 (by rw [hsteps_sing]; simp)
  rcases hr_ex with ⟨r0, hr0_mem, hr0_em, _⟩
  have hfil_hase : seq.filter (fun u => decide (nodeField mem nb u OFF_HASE ≠ 0)) = [r0.nodeId] := by
    have hmap_eq := evalMemSteps_map_nodeId mem nb h L t₂ false 0
    have helen : (evalMemSteps mem nb h L t₂ false 0).length = 1 := by
      rw [hf2.length_eq, hsteps_len]
    cases hms : evalMemSteps mem nb h L t₂ false 0 with
    | nil => simp [hms] at helen
    | cons r₀ tl' =>
        simp only [hms, List.length_cons] at helen
        have htl_nil : tl' = [] := List.length_eq_zero_iff.1 (by omega)
        subst htl_nil
        rw [hms, List.mem_singleton] at hr0_mem
        dsimp only [seq]
        rw [← hmap_eq, hms, ← hr0_mem]; rfl
  have hpp_le : ∀ s ∈ (AuxTree.node (y + 1) l₂ AuxTree.leaf :: rest₂),
      nodeField mem nb s.rootId OFF_PPAR ≤ lctCap n := fun s hs => by
    dsimp only [nb]
    rcases (hi.auxPathOk s hs).2.1 with h0 | ⟨_, h2, _⟩ <;> omega
  have htree_seq : lctTreeSeq mem nb (lctCap n) t₂.rootId = seq :=
    hi.sf.lctTreeSeq_eq ht₂_mem
  have hpar_seq_idx := lctAuxParent_of_tree hi.sf hpp_le ht₂_mem
  rw [htree_seq] at hpar_seq_idx
  have hsub_isv : ∀ u ∈ seq.filter (fun u => decide (nodeField mem nb u OFF_ISV ≠ 0)),
      u ∈ [x + 1, y + 1] := by
    intro u hu
    rcases List.mem_filter.1 hu with ⟨hu_seq, hu_isv⟩
    rcases hnode_class u hu_seq with ⟨hu_n, _⟩ | ⟨_, h0, _⟩
    · have hu1 : 1 ≤ u := by
        have hu_flat : u ∈ (AuxTree.node (y + 1) l₂ .leaf :: rest₂).flatMap AuxTree.toList :=
          List.mem_flatMap.2 ⟨t₂, ht₂_mem, hseq_perm.subset hu_seq⟩
        rcases List.mem_map.1 (hi.sf.perm.subset hu_flat) with ⟨k, _, rfl⟩; omega
      rcases List.getElem_of_mem hu_seq with ⟨i, hi_lt, hiu⟩
      by_cases hi0 : i = 0
      · subst hi0
        rw [← hiu, cut_getElem_zero_of_head? seq hi_lt hhead]; simp
      · have hpi := hpar_seq_idx i hi_lt
        simp only [hi0, ite_false] at hpi
        have hprev_lt : i - 1 < seq.length := by omega
        rw [cut_getElem!_eq seq hprev_lt, hiu] at hpi
        have hprev_mem : seq[i - 1] ∈ seq := List.getElem_mem hprev_lt
        have hv_lt : u - 1 < n :=
          lt_of_lt_of_le (Nat.sub_one_lt (Nat.one_le_iff_ne_zero.1 hu1)) hu_n
        have hsubv := hi.subdivOk.2.2.1 (u - 1) hv_lt
        have hv1 : u - 1 + 1 = u := Nat.sub_add_cancel hu1
        rw [hv1] at hsubv
        rcases hsubv with h0 | ⟨p, hp_em, hpe, hpp⟩
        · have hprev_pos : 1 ≤ seq[i - 1] := by
            have hp_flat : seq[i - 1] ∈ (AuxTree.node (y + 1) l₂ .leaf :: rest₂).flatMap AuxTree.toList :=
              List.mem_flatMap.2 ⟨t₂, ht₂_mem, hseq_perm.subset hprev_mem⟩
            rcases List.mem_map.1 (hi.sf.perm.subset hp_flat) with ⟨k, _, hk⟩
            rw [← hk]; exact Nat.succ_pos k
          have h0' : seq[i - 1] = 0 := hpi.symm.trans h0
          exact absurd h0' (Nat.one_le_iff_ne_zero.1 hprev_pos)
        · have hp1_mem : p.1 ∈ seq := by rw [← hpp, hpi]; exact hprev_mem
          have hp1_hase : nodeField mem nb p.1 OFF_HASE = 1 := (hi.edgeOk p hp_em).2.2.2.1
          have hp1_flt : p.1 ∈ [r0.nodeId] := by
            rw [← hfil_hase]
            exact List.mem_filter.2 ⟨hp1_mem, by simp [hp1_hase]⟩
          rw [List.mem_singleton] at hp1_flt
          have hnd_em : (edgeMap.map Prod.fst).Nodup :=
            (hslots.nodup_iff.2 (List.nodup_range.map (fun _ _ h => by omega))).of_append_left
          have hstep0 : steps[0] = { edge := e, fwd := decide (e.u = x) } := by
            simp [hsteps_sing]
          have hp_e : p.2 = e := by
            rw [hstep0] at hr0_em
            exact cut_fst_inj_of_nodup edgeMap hnd_em (hp1_flt ▸ hp_em) hr0_em
          rw [hp_e] at hpe
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact cut_mem_pair_of hu1 hf' hpe
    · simp [h0] at hu_isv
  have hflt_nd : (seq.filter (fun u => decide (nodeField mem nb u OFF_ISV ≠ 0))).Nodup := by
    have hnd_t2 : t₂.toList.Nodup := by
      rw [List.flatMap_cons, List.nodup_append] at hnd_all
      exact hnd_all.1
    exact (hseq_perm.nodup_iff.2 hnd_t2).filter _
  have hx_isv : nodeField mem nb (x + 1) OFF_ISV = 1 := (hi.vertexOk x hx).1
  have hy_isv : nodeField mem nb (y + 1) OFF_ISV = 1 := (hi.vertexOk y hy).1
  have hx_mem_flt : x + 1 ∈ seq.filter (fun u => decide (nodeField mem nb u OFF_ISV ≠ 0)) :=
    List.mem_filter.2 ⟨List.mem_of_head? hhead, by simp [hx_isv]⟩
  have hy_mem_flt : y + 1 ∈ seq.filter (fun u => decide (nodeField mem nb u OFF_ISV ≠ 0)) :=
    List.mem_filter.2 ⟨hseq_perm.symm.subset (by simp [t₂, AuxTree.toList]), by simp [hy_isv]⟩
  have hxy_perm : (seq.filter (fun u => decide (nodeField mem nb u OFF_ISV ≠ 0))).Perm [x + 1, y + 1] := by
    have hnd2 : ([x + 1, y + 1] : List ℕ).Nodup := by simp [hne]
    refine (List.perm_ext_iff_of_nodup hflt_nd hnd2).2 fun u => ?_
    refine ⟨fun hu => hsub_isv u hu, fun hu => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> [exact hx_mem_flt; exact hy_mem_flt]
  have hvc2 : nodeField mem nb (y + 1) OFF_VCNT = 2 := by
    rw [hvcnt_eq, hseq_sum.1, hxy_perm.length_eq]; rfl
  exact hvcnt hvc2

/-- When `vcnt = 2` returns an edge `(ed, e)` whose endpoints differ from `{x, y}`, no direct
edge connects `x` and `y`, so `F.cut x y = F`. -/
theorem cut_eq_self_of_ne_endpoints {b x y z : ℕ} {l₂ : AuxTree} {mem : ℕ → ℕ}
    {F : MathForest} {e : ForestEdge}
    (hsame_head : F.SameComp x y →
      (AuxTree.evalInorder (revFlag mem (lctNodesBase b)) (.node (y + 1) l₂ .leaf) false).head? =
        some (x + 1))
    (hseq_eq : AuxTree.evalInorder (revFlag mem (lctNodesBase b)) (.node (y + 1) l₂ .leaf) false =
      [z + 1, nodeField mem (lctNodesBase b) (y + 1) OFF_MIN1_FIRST, y + 1])
    (hne_ep : ¬ ((e.u = x ∧ e.v = y) ∨ (e.u = y ∧ e.v = x)))
    (he_end : (e.u = z ∧ e.v = y) ∨ (e.u = y ∧ e.v = z)) :
    F.cut x y = F := by
  suffices h : F.edges.filter (fun e' => !(e'.u == x && e'.v == y || e'.u == y && e'.v == x)) = F.edges by
    have hcut : F.cut x y = ⟨F.n, F.edges.filter (fun e' => !(e'.u == x && e'.v == y || e'.u == y && e'.v == x))⟩ := rfl
    rw [hcut, h]
  rw [List.filter_eq_self]
  intro e' he'
  by_contra hf
  have hf' := cut_filter_false_iff hf
  have hwalk1 := isStep_of_edge_endpoints he' hf'
  have hsc : F.SameComp x y := ⟨[e'.toRaw], hwalk1.to_isWalk⟩
  have hhead := hsame_head hsc
  rw [hseq_eq] at hhead
  simp only [List.head?_cons, Option.some.injEq] at hhead
  have hxz : z = x := by omega
  subst hxz
  exact hne_ep he_end

/-- After `splay ed` on the `[x + 1, ed, y + 1]` tree, the splayed tree has shape
`.node ed (.node (x + 1) .leaf .leaf) (.node (y + 1) .leaf .leaf)`. -/
theorem cut_splayed_ed_shape {w h L P b n x y ed : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {t_ed' : AuxTree} {rest : List AuxTree} {mem : ℕ → ℕ}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (t_ed' :: rest) mem)
    (hroot : t_ed'.rootId = ed)
    (hrev : revFlag mem (lctNodesBase b) ed = false)
    (hev : AuxTree.evalInorder (revFlag mem (lctNodesBase b)) t_ed' false = [x + 1, ed, y + 1])
    (hpp : nodeField mem (lctNodesBase b) ed OFF_PPAR = 0) :
    t_ed' = .node ed (.node (x + 1) .leaf .leaf) (.node (y + 1) .leaf .leaf) ∧
      nodeField mem (lctNodesBase b) (x + 1) OFF_PPAR = 0 ∧
      nodeField mem (lctNodesBase b) (y + 1) OFF_PPAR = 0 ∧
      lctAuxParent mem (lctNodesBase b) (lctCap n) (x + 1) = 0 := by
  have htok := hi.sf.trees_ok t_ed' List.mem_cons_self
  cases ht : t_ed' with
  | leaf => exact absurd ht htok.1
  | node rid l r =>
      have hrid : rid = ed := by rw [ht] at hroot; exact hroot
      subst rid
      have hnd_all := hi.sf.perm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
      have hnd_t : ((l.toList ++ [ed]) ++ r.toList).Nodup := by
        rw [ht, List.flatMap_cons, List.nodup_append] at hnd_all
        exact hnd_all.1
      have hnd_app := List.nodup_append.1 hnd_t
      have hnd_l := List.nodup_append.1 hnd_app.1
      have hed_nl : ed ∉ AuxTree.evalInorder (revFlag mem (lctNodesBase b)) l false := fun hm =>
        hnd_l.2.2 ed ((AuxTree.evalInorder_perm (revFlag mem (lctNodesBase b)) l false).subset hm)
          ed List.mem_cons_self rfl
      have hed_nr : ed ∉ AuxTree.evalInorder (revFlag mem (lctNodesBase b)) r false := fun hm =>
        hnd_app.2.2 ed (by simp) ed
          ((AuxTree.evalInorder_perm (revFlag mem (lctNodesBase b)) r false).subset hm) rfl
      have hev' : AuxTree.evalInorder (revFlag mem (lctNodesBase b)) l false ++ [ed] ++
          AuxTree.evalInorder (revFlag mem (lctNodesBase b)) r false = [x + 1, ed, y + 1] := by
        simpa [ht, AuxTree.evalInorder, hrev] using hev
      have hsplit : AuxTree.evalInorder (revFlag mem (lctNodesBase b)) l false = [x + 1] ∧
          AuxTree.evalInorder (revFlag mem (lctNodesBase b)) r false = [y + 1] := by
        rcases hxs : AuxTree.evalInorder (revFlag mem (lctNodesBase b)) l false with
          _ | ⟨a, _ | ⟨a', _ | ⟨a'', xs''⟩⟩⟩
        · simp only [hxs, List.nil_append, List.cons_append] at hev'
          injection hev' with _ hzs
          exact absurd (hzs ▸ List.mem_cons_self) hed_nr
        · simp only [hxs, List.cons_append, List.nil_append] at hev'
          injection hev' with ha1 htail
          injection htail with _ hzs
          exact ⟨congrArg (· :: []) ha1, hzs⟩
        · simp only [hxs, List.cons_append, List.nil_append] at hev'
          injection hev' with _ htail
          injection htail with ha' _
          exact absurd (ha'.symm ▸ (by simp [hxs])) hed_nl
        · exfalso
          have hlen := congrArg List.length hev'
          rw [hxs] at hlen
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen
          omega
      have hl_sing : l = .node (x + 1) .leaf .leaf := by
        have hperm_l := AuxTree.evalInorder_perm (revFlag mem (lctNodesBase b)) l false
        rw [hsplit.1] at hperm_l
        cases hl_eq : l with
        | leaf => simp [hl_eq, AuxTree.toList] at hperm_l
        | node lx ll lr =>
            have hll := hperm_l.length_eq
            simp [hl_eq, AuxTree.toList] at hll
            have hll0 : ll = .leaf := by
              cases ll with
              | leaf => rfl
              | node => simp [AuxTree.toList] at hll; omega
            have hlr0 : lr = .leaf := by
              cases lr with
              | leaf => rfl
              | node => simp [AuxTree.toList] at hll; omega
            subst hll0 hlr0
            simp only [hl_eq, AuxTree.toList, List.nil_append, List.cons_append,
              List.perm_singleton, List.cons.injEq, and_true] at hperm_l
            simp [hperm_l]
      have hr_sing : r = .node (y + 1) .leaf .leaf := by
        have hperm_r := AuxTree.evalInorder_perm (revFlag mem (lctNodesBase b)) r false
        rw [hsplit.2] at hperm_r
        cases hr_eq : r with
        | leaf => simp [hr_eq, AuxTree.toList] at hperm_r
        | node rx rl rr =>
            have hrl := hperm_r.length_eq
            simp [hr_eq, AuxTree.toList] at hrl
            have hrl0 : rl = .leaf := by
              cases rl with
              | leaf => rfl
              | node => simp [AuxTree.toList] at hrl; omega
            have hrr0 : rr = .leaf := by
              cases rr with
              | leaf => rfl
              | node => simp [AuxTree.toList] at hrl; omega
            subst hrl0 hrr0
            simp only [hr_eq, AuxTree.toList, List.nil_append, List.cons_append,
              List.perm_singleton, List.cons.injEq, and_true] at hperm_r
            simp [hperm_r]
      have hed_eq : t_ed' = .node ed (.node (x + 1) .leaf .leaf) (.node (y + 1) .leaf .leaf) :=
        ht.trans (by simp [hl_sing, hr_sing])
      have htm_ed := htok.2.2
      rw [hed_eq] at htm_ed
      have hch := TreeMemMatch.children_match htm_ed
      have hpx : nodeField mem (lctNodesBase b) (x + 1) OFF_PPAR = 0 := by
        have h1 := hch.1; rw [TreeMemMatch.eq_2] at h1; exact h1.2.2.2.2.2.1
      have hpy : nodeField mem (lctNodesBase b) (y + 1) OFF_PPAR = 0 := by
        have h2 := hch.2; rw [TreeMemMatch.eq_2] at h2; exact h2.2.2.2.2.2.1
      have hpp_le : ∀ s ∈ (t_ed' :: rest), nodeField mem (lctNodesBase b) s.rootId OFF_PPAR ≤ lctCap n :=
        fun s hs => by rcases (hi.auxPathOk s hs).2.1 with h0 | ⟨_, h2, _⟩ <;> omega
      have htree_seq : lctTreeSeq mem (lctNodesBase b) (lctCap n) ed = [x + 1, ed, y + 1] := by
        have hsq := hi.sf.lctTreeSeq_eq (t := t_ed') List.mem_cons_self
        rw [hroot] at hsq
        exact hsq.trans hev
      have hpar_x : lctAuxParent mem (lctNodesBase b) (lctCap n) (x + 1) = 0 := by
        have hp0 := lctAuxParent_of_tree hi.sf hpp_le List.mem_cons_self 0 (by rw [hroot, htree_seq]; simp)
        simpa [hroot, htree_seq, hpp] using hp0
      exact ⟨by rw [← ht]; exact hed_eq, hpx, hpy, hpar_x⟩

end CutPathAnalysis

/-- Removing one key `(ed, e)` from a nodup-key association list leaves a list whose cons with
`(ed, e)` is a permutation of the original list. -/
theorem cut_edgeMap_perm_filter {ed : ℕ} {e : ForestEdge} :
    ∀ {l : List (ℕ × ForestEdge)}, (l.map Prod.fst).Nodup → (ed, e) ∈ l →
      l.Perm ((ed, e) :: l.filter (fun p => decide (p.1 ≠ ed))) := by
  intro l hnd hm
  induction l with
  | nil => simp at hm
  | cons p tl ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      have hflt_of : (ed ∉ tl.map Prod.fst) → tl.filter (fun q => decide (q.1 ≠ ed)) = tl := by
        intro hnin
        rw [List.filter_eq_self]
        intro q hq
        simp only [ne_eq, decide_eq_true_eq]
        intro hq_eq
        exact hnin (hq_eq ▸ List.mem_map_of_mem (f := Prod.fst) hq)
      by_cases hp : p.1 = ed
      · have hpe : p = (ed, e) := by
          rcases List.mem_cons.1 hm with h | hm_tl
          · exact h.symm
          · exact absurd (hp ▸ List.mem_map.2 ⟨(ed, e), hm_tl, rfl⟩) hnd.1
        subst hpe
        have hf := hflt_of hnd.1
        rw [List.filter_cons_of_neg (by simp), hf]
      · have hm_tl : (ed, e) ∈ tl := by
          rcases List.mem_cons.1 hm with h | h
          · exact absurd (by rw [← h]) hp
          · exact h
        have hih := ih hnd.2 hm_tl
        rw [List.filter_cons_of_pos (by simpa using hp)]
        exact (hih.cons p).trans (List.Perm.swap (ed, e) p _)

end MinCostFlow.LinkCut.Prog
