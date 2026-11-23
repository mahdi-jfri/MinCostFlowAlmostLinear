module

public import MinCostFlow.LinkCut.Prog.MathForestQueries

/-!
# Invariant Preservation for `pathAdd`

Helper lemmas and invariant preservation proofs (`pathAdd_stepsShiftFit`, `pathAdd_applyTag_invs`,
`pathAdd_safeMem_weaken`) for the Word-RAM `pathAdd` operation on `MathForest`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section PathAddInvariants

private lemma applyStepsDelta_eid (steps : List PathStep) (δ : ℚ) (e : ForestEdge) :
    (MathForest.applyStepsDelta steps δ e).eid = e.eid := by
  dsimp only [MathForest.applyStepsDelta]
  cases steps.find? (fun s => s.edge.eid == e.eid) with
  | none => rfl
  | some s => cases hs : s.fwd <;> simp [ForestEdge.addFlow, hs]

private lemma applyStepsDelta_u (steps : List PathStep) (δ : ℚ) (e : ForestEdge) :
    (MathForest.applyStepsDelta steps δ e).u = e.u := by
  dsimp only [MathForest.applyStepsDelta]
  cases steps.find? (fun s => s.edge.eid == e.eid) with
  | none => rfl
  | some s => cases hs : s.fwd <;> simp [ForestEdge.addFlow, hs]

private lemma applyStepsDelta_v (steps : List PathStep) (δ : ℚ) (e : ForestEdge) :
    (MathForest.applyStepsDelta steps δ e).v = e.v := by
  dsimp only [MathForest.applyStepsDelta]
  cases steps.find? (fun s => s.edge.eid == e.eid) with
  | none => rfl
  | some s => cases hs : s.fwd <;> simp [ForestEdge.addFlow, hs]

private lemma fits_of_isFixedFit_div {h L P : ℕ} {k : ℤ}
    (hf : IsFixedFit h L P ((k : ℚ) / (2 : ℚ) ^ P)) : Fits h L k := by
  rcases hf with ⟨k', hk', hq⟩
  have h2P : (2 : ℚ) ^ P ≠ 0 := by positivity
  have hkq : (k : ℚ) = (k' : ℚ) := by
    have := congrArg (· * (2 : ℚ) ^ P) hq
    simpa [div_mul_cancel₀ _ h2P] using this
  exact Int.cast_inj.1 hkq ▸ hk'

private lemma stepMatchesEdge_addDelta {P ed : ℕ} {e : ForestEdge} {r : RawStep}
    {d : ℤ} {δ : ℚ} (hδ : (d : ℚ) / (2 : ℚ) ^ P = δ)
    (hm : stepMatchesEdge P ed e r) :
    stepMatchesEdge P ed (e.addFlow r.fwd δ) (r.addDelta d) := by
  rcases hm with ⟨hn, heid, heu, hev, hcost, hfl, haf, hab⟩
  cases hfwd : r.fwd <;>
    simp only [RawStep.addDelta, ForestEdge.addFlow, stepMatchesEdge, hfwd, Bool.false_eq_true,
      ↓reduceIte]
  · refine ⟨hn, heid, heu, hev, hcost, ?_, ?_, ?_⟩
    · rw [← hfl, ← hδ]; push_cast; ring
    · rw [← haf, ← hδ]; push_cast; ring
    · rw [← hab, ← hδ]; push_cast; ring
  · refine ⟨hn, heid, heu, hev, hcost, ?_, ?_, ?_⟩
    · rw [← hfl, ← hδ]; push_cast; ring
    · rw [← haf, ← hδ]; push_cast; ring
    · rw [← hab, ← hδ]; push_cast; ring

private lemma isStepWalk_subset {edges : List ForestEdge} {a b : ℕ} {steps : List PathStep}
    (hw : IsStepWalk edges a b steps) : ∀ s ∈ steps, s.edge ∈ edges := by
  intro s hs
  induction hw with
  | nil _ => simp at hs
  | fwd he _ _ ih => rcases List.mem_cons.1 hs with rfl | hs' <;> [exact he; exact ih hs']
  | bwd he _ _ ih => rcases List.mem_cons.1 hs with rfl | hs' <;> [exact he; exact ih hs']

private lemma steps_nodup_eid {edges : List ForestEdge} {a b : ℕ} {steps : List PathStep}
    (hnd_edges : (edges.map ForestEdge.eid).Nodup)
    (hw : IsStepWalk edges a b steps)
    (hnd_raw : (steps.map PathStep.toRaw).Nodup) :
    (steps.map fun s => s.edge.eid).Nodup := by
  have hsub := isStepWalk_subset hw
  clear hw
  induction steps with
  | nil => exact List.nodup_nil
  | cons s xs ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd_raw ⊢
      refine ⟨?_, ih hnd_raw.2 (fun x hx => hsub x (List.mem_cons_of_mem _ hx))⟩
      intro hmem
      rcases List.mem_map.1 hmem with ⟨x, hx_in, hxeid⟩
      have he1 := hsub s List.mem_cons_self
      have he2 := hsub x (List.mem_cons_of_mem _ hx_in)
      have hinj : ∀ e₁ ∈ edges, ∀ e₂ ∈ edges, e₁.eid = e₂.eid → e₁ = e₂ :=
        (List.nodup_map_iff_inj_on hnd_edges.of_map).1 hnd_edges
      have hseq : x.edge = s.edge := hinj x.edge he2 s.edge he1 hxeid
      have hraw : x.toRaw = s.toRaw := by simp [PathStep.toRaw, hseq]
      exact hnd_raw.1 (hraw ▸ List.mem_map_of_mem hx_in)

private lemma evalMemSteps_hase_nz_and_eid {mem : ℕ → ℕ} {nb h L : ℕ} {t : AuxTree} {f : Bool} {δ : ℤ}
    {r : RawStep} (hr : r ∈ evalMemSteps mem nb h L t f δ) :
    nodeField mem nb r.nodeId OFF_HASE ≠ 0 ∧ r.eid = nodeField mem nb r.nodeId OFF_EID := by
  induction t generalizing f δ with
  | leaf => simp [evalMemSteps] at hr
  | node x l r' ihl ihr =>
      cases f <;>
        simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, List.mem_append,
          Option.mem_toList] at hr
      · rcases hr with (h | hr0) | h
        · exact ihl h
        · cases hown : nodeOwnRawStep mem nb h L x with
          | none => simp [hown] at hr0
          | some r0 =>
              simp only [hown, Option.map_some, Option.some.injEq] at hr0
              subst hr0
              by_cases h0 : nodeField mem nb x OFF_HASE = 0
              · simp [nodeOwnRawStep, h0] at hown
              · simp only [nodeOwnRawStep, h0, ↓reduceIte, Option.some.injEq] at hown
                have hfields : r0.nodeId = x ∧ r0.eid = nodeField mem nb x OFF_EID := by
                  rw [← hown]; exact ⟨rfl, rfl⟩
                cases hfwd : r0.fwd <;>
                  simp [RawStep.addDeltaMod, hfwd, hfields.1, hfields.2, h0]
        · exact ihr h
      · rcases hr with (h | hr0) | h
        · exact ihr h
        · cases hown : nodeOwnRawStep mem nb h L x with
          | none => simp [hown] at hr0
          | some r0 =>
              simp only [hown, Option.map_some, Option.some.injEq] at hr0
              subst hr0
              by_cases h0 : nodeField mem nb x OFF_HASE = 0
              · simp [nodeOwnRawStep, h0] at hown
              · simp only [nodeOwnRawStep, h0, ↓reduceIte, Option.some.injEq] at hown
                have hfields : r0.nodeId = x ∧ r0.eid = nodeField mem nb x OFF_EID := by
                  rw [← hown]; exact ⟨rfl, rfl⟩
                cases hfwd : r0.fwd <;>
                  simp [RawStep.addDeltaMod, RawStep.flip, hfwd, hfields.1, hfields.2, h0]
        · exact ihl h

private lemma list_take_cons_drop {α : Type*} (l : List α) (k : ℕ) (hk : k < l.length) :
    l.take k ++ l[k] :: l.drop (k + 1) = l := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
      cases k with
      | zero => simp
      | succ k' =>
          simp only [List.take_succ_cons, List.drop_succ_cons, List.getElem_cons_succ, List.cons_append]
          congr 1
          exact ih k' (by simpa using hk)

private lemma steps_find?_eq_some_of_nodup {steps : List PathStep}
    (hnd : (steps.map fun s => s.edge.eid).Nodup)
    {k : ℕ} (hk : k < steps.length) {eid : ℕ} (heid : (steps[k]'hk).edge.eid = eid) :
    steps.find? (fun q => q.edge.eid == eid) = some (steps[k]'hk) :=
  List.find?_eq_some_iff_append.2 ⟨by simp [heid], steps.take k, steps.drop (k + 1),
    (list_take_cons_drop steps k hk).symm, fun q hq => by
      rcases List.getElem_of_mem hq with ⟨j, hj, rfl⟩
      have hlen_take : (steps.take k).length ≤ k := List.length_take_le k steps
      have hj_k : j < k := lt_of_lt_of_le hj hlen_take
      have hj_lt : j < steps.length := lt_trans hj_k hk
      have hne : (steps.take k)[j].edge.eid ≠ eid := fun heq => by
        rw [List.getElem_take] at heq
        have hmap_eq : (steps.map (·.edge.eid))[j]'(by simp [hj_lt]) =
            (steps.map (·.edge.eid))[k]'(by simp [hk]) := by
          simp only [List.getElem_map]
          exact heq.trans heid.symm
        have hjk := (List.Nodup.getElem_inj_iff hnd).1 hmap_eq
        omega
      simpa using hne⟩

theorem pathAdd_stepsShiftFit {w h L P b n u v : ℕ} {F : MathForest}
    {l₂ : AuxTree} {rest₂ : List AuxTree} {x₂ : LctConc}
    {mem_in : ℕ → ℕ} {d : ℤ} {δ : ℚ}
    (hu : u < n) (hv : v < n) (hval : F.Valid) (hFn : F.n = n)
    (hrep : LctMemRep w h L P b F x₂ mem_in)
    (hx₂ : x₂.trees = .node (v + 1) l₂ .leaf :: rest₂)
    (hfit_F : ∀ e ∈ (F.pathAdd u v δ).edges, EdgeFits h L P e)
    (hδ : (d : ℚ) / (2 : ℚ) ^ P = δ)
    (hpp0 : nodeField mem_in (lctNodesBase b) (v + 1) OFF_PPAR = 0)
    (hhead : ((AuxTree.node (v + 1) l₂ .leaf).evalInorder (revFlag mem_in (lctNodesBase b)) false).head? = some (u + 1))
    (hlast : ((AuxTree.node (v + 1) l₂ .leaf).evalInorder (revFlag mem_in (lctNodesBase b)) false).getLast? = some (v + 1)) :
    ∃ steps,
      findSteps F.edges u v = some steps ∧
      IsStepWalk F.edges u v steps ∧
      (steps.map PathStep.toRaw).Nodup ∧
      List.Forall₂ (fun r s => ∃ ed, stepMatchesEdge P ed s.edge r ∧ s.fwd = r.fwd)
        (evalMemSteps mem_in (lctNodesBase b) h L (.node (v + 1) l₂ .leaf) false 0) steps ∧
      StepsShiftFit h L (evalMemSteps mem_in (lctNodesBase b) h L (.node (v + 1) l₂ .leaf) false 0) d := by
  let nb := lctNodesBase b
  let t₂ := AuxTree.node (v + 1) l₂ .leaf
  have ht2_mem : t₂ ∈ x₂.trees := by rw [hx₂]; exact List.mem_cons_self
  rcases hrep.pathTree_isStepWalk ht2_mem (hFn ▸ hu) (hFn ▸ hv) hpp0 hhead hlast with
    ⟨steps, hfs, hw, hnd_raw, hfor⟩
  have hsteps_eid_nd : (steps.map fun s => s.edge.eid).Nodup :=
    steps_nodup_eid hval.2.1 hw hnd_raw
  have hfit_steps : StepsShiftFit h L (evalMemSteps mem_in nb h L t₂ false 0) d := by
    intro r hr
    rcases (List.forall₂_iff_get.1 hfor) with ⟨hlen, hget⟩
    rcases List.getElem_of_mem hr with ⟨k, hk, hr_eq⟩
    have hk_st : k < steps.length := hlen ▸ hk
    rcases hget k hk hk_st with ⟨ed', hm', hfwd'⟩
    dsimp only [nb, t₂] at hr_eq
    simp only [List.get_eq_getElem] at hm' hfwd'
    rw [show (evalMemSteps mem_in (lctNodesBase b) h L (.node (v + 1) l₂ .leaf) false 0)[k] = r
      from hr_eq] at hm' hfwd'
    set s := steps[k]'hk_st
    have hs_mem : s ∈ steps := List.getElem_mem _
    have hs_in_F : s.edge ∈ F.edges := isStepWalk_subset hw s hs_mem
    have hfind_s : steps.find? (fun q => q.edge.eid == s.edge.eid) = some s :=
      steps_find?_eq_some_of_nodup hsteps_eid_nd hk_st rfl
    have happ_eq : MathForest.applyStepsDelta steps δ s.edge = s.edge.addFlow s.fwd δ := by
      simp [MathForest.applyStepsDelta, hfind_s]
    have hnew_edge_in : s.edge.addFlow s.fwd δ ∈ (F.pathAdd u v δ).edges := by
      rw [← happ_eq]
      simp only [MathForest.pathAdd, hfs]
      exact List.mem_map_of_mem hs_in_F
    have hfits0 := hrep.edgeFits s.edge hs_in_F
    have hfits1 := hfit_F _ hnew_edge_in
    have hm'_fl := hm'.2.2.2.2.2.1
    have hm'_af := hm'.2.2.2.2.2.2.1
    have hm'_ab := hm'.2.2.2.2.2.2.2
    have hr_fl := fits_of_isFixedFit_div (hm'_fl.symm ▸ hfits0.2.1)
    have hr_af := fits_of_isFixedFit_div (hm'_af.symm ▸ hfits0.2.2.1)
    have hr_ab := fits_of_isFixedFit_div (hm'_ab.symm ▸ hfits0.2.2.2)
    refine ⟨hr_fl, hr_af, hr_ab, ?_, ?_, ?_⟩
    · cases hf : r.fwd <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · have hsf : s.fwd = false := hfwd'.trans hf
        have hq : ((r.flow - d : ℤ) : ℚ) / (2 : ℚ) ^ P = (s.edge.addFlow s.fwd δ).flow := by
          simp only [ForestEdge.addFlow, hsf, Bool.false_eq_true, ↓reduceIte, ← hm'_fl, ← hδ]
          push_cast; ring
        exact fits_of_isFixedFit_div (hq.symm ▸ hfits1.2.1)
      · have hsf : s.fwd = true := hfwd'.trans hf
        have hq : ((r.flow + d : ℤ) : ℚ) / (2 : ℚ) ^ P = (s.edge.addFlow s.fwd δ).flow := by
          simp only [ForestEdge.addFlow, hsf, ↓reduceIte, ← hm'_fl, ← hδ]
          push_cast; ring
        exact fits_of_isFixedFit_div (hq.symm ▸ hfits1.2.1)
    · cases hf : r.fwd <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · have hsf : s.fwd = false := hfwd'.trans hf
        have hq : ((r.availFwd + d : ℤ) : ℚ) / (2 : ℚ) ^ P = (s.edge.addFlow s.fwd δ).availFwd := by
          simp only [ForestEdge.addFlow, hsf, Bool.false_eq_true, ↓reduceIte, ← hm'_af, ← hδ]
          push_cast; ring
        exact fits_of_isFixedFit_div (hq.symm ▸ hfits1.2.2.1)
      · have hsf : s.fwd = true := hfwd'.trans hf
        have hq : ((r.availFwd - d : ℤ) : ℚ) / (2 : ℚ) ^ P = (s.edge.addFlow s.fwd δ).availFwd := by
          simp only [ForestEdge.addFlow, hsf, ↓reduceIte, ← hm'_af, ← hδ]
          push_cast; ring
        exact fits_of_isFixedFit_div (hq.symm ▸ hfits1.2.2.1)
    · cases hf : r.fwd <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · have hsf : s.fwd = false := hfwd'.trans hf
        have hq : ((r.availBwd - d : ℤ) : ℚ) / (2 : ℚ) ^ P = (s.edge.addFlow s.fwd δ).availBwd := by
          simp only [ForestEdge.addFlow, hsf, Bool.false_eq_true, ↓reduceIte, ← hm'_ab, ← hδ]
          push_cast; ring
        exact fits_of_isFixedFit_div (hq.symm ▸ hfits1.2.2.2)
      · have hsf : s.fwd = true := hfwd'.trans hf
        have hq : ((r.availBwd + d : ℤ) : ℚ) / (2 : ℚ) ^ P = (s.edge.addFlow s.fwd δ).availBwd := by
          simp only [ForestEdge.addFlow, hsf, ↓reduceIte, ← hm'_ab, ← hδ]
          push_cast; ring
        exact fits_of_isFixedFit_div (hq.symm ▸ hfits1.2.2.2)
  exact ⟨steps, hfs, hw, hnd_raw, hfor, hfit_steps⟩

theorem pathAdd_applyTag_invs {w h L P b n u v : ℕ} {F : MathForest}
    {freeEdges : List ℕ} {edgeMap : List (ℕ × ForestEdge)} {l₂ : AuxTree} {rest₂ : List AuxTree}
    {mem_in mem_tag : ℕ → ℕ} {d : ℤ} {δ : ℚ}
    (hv : v < n) (hval : F.Valid)
    (hed_perm : (edgeMap.map Prod.snd).Perm F.edges)
    (hslots : (edgeMap.map Prod.fst ++ freeEdges).Perm ((List.range n).map (n + 1 + ·)))
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap (.node (v + 1) l₂ .leaf :: rest₂) mem_in)
    (hδ : (d : ℚ) / (2 : ℚ) ^ P = δ)
    (hle : mem_in (lctNodesBase b - 1) ≤ mem_tag (lctNodesBase b - 1))
    (hhp_w : mem_tag (lctNodesBase b - 1) < 2 ^ w)
    (ht_tag : TreeMemMatch w h L mem_tag (lctNodesBase b) (lctCap n) (.node (v + 1) l₂ .leaf) 0
      (nodeField mem_in (lctNodesBase b) (v + 1) OFF_PPAR))
    (hsteps_tag : evalMemSteps mem_tag (lctNodesBase b) h L (.node (v + 1) l₂ .leaf) false 0 =
      (evalMemSteps mem_in (lctNodesBase b) h L (.node (v + 1) l₂ .leaf) false 0).map (·.addDelta d))
    (hf1 : ∀ z ≤ lctCap n, ∀ off < NODE_STRIDE,
      off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
      off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL →
      off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
      nodeField mem_tag (lctNodesBase b) z off = nodeField mem_in (lctNodesBase b) z off)
    (hf2 : ∀ addr, addr < lctNodesBase b + NODE_STRIDE * (v + 1) ∨
        lctNodesBase b + NODE_STRIDE * (v + 1) + NODE_STRIDE ≤ addr →
      addr ≠ lctNodesBase b - 1 → addr < mem_in (lctNodesBase b - 1) →
      mem_tag addr = mem_in addr)
    (hfr : LctFrame (lctNodesBase b + NODE_STRIDE) (lctNodesBase b + NODE_STRIDE * (lctCap n + 1))
      (lctNodesBase b - 1) mem_in mem_tag)
    (steps : List PathStep)
    (hw : IsStepWalk F.edges u v steps) (hnd_raw : (steps.map PathStep.toRaw).Nodup)
    (hfor : List.Forall₂ (fun r s => ∃ ed, stepMatchesEdge P ed s.edge r ∧ s.fwd = r.fwd)
      (evalMemSteps mem_in (lctNodesBase b) h L (.node (v + 1) l₂ .leaf) false 0) steps) :
    LctExposeInvs w h L P b n freeEdges
      (edgeMap.map fun q => (q.1, MathForest.applyStepsDelta steps δ q.2))
      (.node (v + 1) l₂ .leaf :: rest₂) mem_tag ∧
    lctPhi L mem_tag b n = lctPhi L mem_in b n := by
  let nb := lctNodesBase b
  let cap := lctCap n
  let t₂ := AuxTree.node (v + 1) l₂ .leaf
  have hsteps_eid_nd : (steps.map fun s => s.edge.eid).Nodup :=
    steps_nodup_eid hval.2.1 hw hnd_raw
  have hed_inj_F : ∀ e₁ ∈ F.edges, ∀ e₂ ∈ F.edges, e₁.eid = e₂.eid → e₁ = e₂ :=
    (List.nodup_map_iff_inj_on hval.2.1.of_map).1 hval.2.1
  have hnb_pos : 6 ≤ nb := by unfold nb lctNodesBase LCT_HDR_SIZE; omega
  have hmem_arena_lt : nb + NODE_STRIDE * (cap + 1) ≤ mem_in (nb - 1) := hi.sf.2.2.2.1
  have hhdr_lt_in : ∀ k < 5, b + k < mem_in (nb - 1) ∧ b + k < nb + NODE_STRIDE * (v + 1) ∧ b + k ≠ nb - 1 := by
    intro k hk
    have hnb_eq : nb = b + 6 := rfl
    have h1 : b + k < nb + NODE_STRIDE * (v + 1) := by unfold NODE_STRIDE; omega
    have h2 : b + k < nb + NODE_STRIDE * (cap + 1) := by
      have : 1 ≤ cap + 1 := Nat.succ_pos _
      have : NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) := Nat.le_mul_of_pos_right _ this
      omega
    exact ⟨lt_of_lt_of_le h2 hmem_arena_lt, h1, by omega⟩
  have hhdrN' : mem_tag (b + LCT_HDR_N) = n := by
    have hb0 := hhdr_lt_in LCT_HDR_N (by unfold LCT_HDR_N; decide)
    exact (hf2 _ (Or.inl hb0.2.1) hb0.2.2 hb0.1).trans hi.hdrN
  have hhdrCap' : mem_tag (b + LCT_HDR_CAP) = lctCap n := by
    have hb1 := hhdr_lt_in LCT_HDR_CAP (by unfold LCT_HDR_CAP; decide)
    exact (hf2 _ (Or.inl hb1.2.1) hb1.2.2 hb1.1).trans hi.hdrCap
  have hhdrL' : mem_tag (b + LCT_HDR_L) = L := by
    have hb3 := hhdr_lt_in LCT_HDR_L (by unfold LCT_HDR_L; decide)
    exact (hf2 _ (Or.inl hb3.2.1) hb3.2.2 hb3.1).trans hi.hdrL
  have hhdrP' : mem_tag (b + LCT_HDR_P) = P := by
    have hb4 := hhdr_lt_in LCT_HDR_P (by unfold LCT_HDR_P; decide)
    exact (hf2 _ (Or.inl hb4.2.1) hb4.2.2 hb4.1).trans hi.hdrP
  have hnd_all : ((t₂ :: rest₂).flatMap AuxTree.toList).Nodup :=
    (SplayForestOk.perm hi.sf).nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hv_mem_t2 : v + 1 ∈ t₂.toList := by simp [t₂, AuxTree.toList]
  have hrest_ne_v1 : ∀ s ∈ rest₂, ∀ z ∈ s.toList, z ≠ v + 1 := by
    intro s hs z hz heq
    rw [List.flatMap_cons, List.nodup_append] at hnd_all
    exact hnd_all.2.2 (v + 1) hv_mem_t2 (v + 1) (List.mem_flatMap.2 ⟨s, hs, heq ▸ hz⟩) rfl
  have hrest_fields : ∀ s ∈ rest₂, ∀ z ∈ s.toList, ∀ off < NODE_STRIDE,
      nodeField mem_tag nb z off = nodeField mem_in nb z off := by
    intro s hs z hz off hoff
    have hzb := (SplayForestOk.trees_ok hi.sf s (by simp [hs])).2.2.nodup_perm_mem hz
    have hne := hrest_ne_v1 s hs z hz
    have had_disj : nb + NODE_STRIDE * z + off < nb + NODE_STRIDE * (v + 1) ∨
        nb + NODE_STRIDE * (v + 1) + NODE_STRIDE ≤ nb + NODE_STRIDE * z + off := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · left
        have hle : z + 1 ≤ v + 1 := hlt
        have hm : NODE_STRIDE * (z + 1) ≤ NODE_STRIDE * (v + 1) := Nat.mul_le_mul_left _ hle
        unfold NODE_STRIDE at hoff ⊢
        linarith
      · right
        have hle : v + 1 + 1 ≤ z := hgt
        have hm : NODE_STRIDE * (v + 1 + 1) ≤ NODE_STRIDE * z := Nat.mul_le_mul_left _ hle
        unfold NODE_STRIDE at hoff ⊢
        linarith
    have had_lt_arena : nb + NODE_STRIDE * z + off < nb + NODE_STRIDE * (cap + 1) := by
      have hm : NODE_STRIDE * (z + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
      unfold NODE_STRIDE at hoff ⊢
      linarith
    exact hf2 _ had_disj (by omega) (lt_of_lt_of_le had_lt_arena hmem_arena_lt)
  have hheap_in : ∀ a, nb + NODE_STRIDE * (cap + 1) ≤ a → a < mem_in (nb - 1) →
      mem_tag a = mem_in a := by
    intro a ha1 ha2
    have hdisj : nb + NODE_STRIDE * (v + 1) + NODE_STRIDE ≤ a := by
      have hv1_le : v + 1 + 1 ≤ cap + 1 := by dsimp only [cap, lctCap]; omega
      have hm : NODE_STRIDE * (v + 1 + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ hv1_le
      unfold NODE_STRIDE at ha1 ⊢; linarith
    exact hf2 a (Or.inr hdisj) (by omega) ha2
  have hsf' : SplayForestOk w h L mem_tag nb cap (t₂ :: rest₂) := by
    refine ⟨hi.sf.1, hi.sf.2.1, hi.sf.2.2.1, le_trans hmem_arena_lt hle, ?_, hhp_w,
      hfr.2.2.2.2.1, ?_, hi.sf.2.2.2.2.2.2.2.2.1, ?_⟩
    · simpa [nb, lctNodesBase, LCT_HDR_L, LCT_HDR_SIZE] using hhdrL'
    · intro off hoff
      have hl := hfr.2.2.2.2.2 (nb + off) (Or.inl ⟨by unfold NODE_STRIDE at hoff ⊢; omega, by omega⟩)
      rw [hl]
      exact hi.sf.2.2.2.2.2.2.2.1 off hoff
    · intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs_rest
      · refine ⟨(hi.sf.trees_ok t₂ (by simp [t₂])).1, ?_, ?_⟩
        · have hpp_eq : nodeField mem_tag nb (v + 1) OFF_PPAR = nodeField mem_in nb (v + 1) OFF_PPAR :=
            hf1 (v + 1) (by dsimp only [cap, lctCap]; omega) _ (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          simpa [t₂, AuxTree.rootId, hpp_eq] using (hi.sf.trees_ok t₂ (by simp [t₂])).2.1
        · have hpp_eq : nodeField mem_tag nb (v + 1) OFF_PPAR = nodeField mem_in nb (v + 1) OFF_PPAR :=
            hf1 (v + 1) (by dsimp only [cap, lctCap]; omega) _ (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          simpa [t₂, AuxTree.rootId, hpp_eq] using ht_tag
      · have hs_ok := hi.sf.trees_ok s (by simp [hs_rest])
        have hrf := hrest_fields s hs_rest s.rootId (AuxTree.rootId_mem_toList hs_ok.1) OFF_PPAR (by decide)
        refine ⟨hs_ok.1, by rw [hrf]; exact hs_ok.2.1, ?_⟩
        rw [hrf]
        exact memAgree_treeMemMatch_of_nodeList hs_ok.2.2 (hrest_fields s hs_rest) hle hheap_in
  have hstruct_eq : ∀ z ≤ cap, ∀ off,
      (off = OFF_LEFT ∨ off = OFF_RIGHT ∨ off = OFF_PARENT ∨ off = OFF_PPAR ∨
       off = OFF_REV ∨ off = OFF_ISV ∨ off = OFF_HASE ∨ off = OFF_VCNT ∨
       off = OFF_EID ∨ off = OFF_EU ∨ off = OFF_EV ∨ off = OFF_DIR ∨
       off = OFF_COST_FWD ∨ off = OFF_COST_BWD) →
      nodeField mem_tag nb z off = nodeField mem_in nb z off := by
    intro z hz off hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hf1 z hz _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  have hfree_hd : mem_tag (b + LCT_HDR_FREE) = mem_in (b + LCT_HDR_FREE) := by
    have hb2 := hhdr_lt_in LCT_HDR_FREE (by unfold LCT_HDR_FREE; decide)
    exact hf2 _ (Or.inl hb2.2.1) hb2.2.2 hb2.1
  have hfreeChain' : FreeSlotChain mem_tag nb (mem_tag (b + LCT_HDR_FREE)) freeEdges := by
    rw [hfree_hd]
    refine freeSlotChain_agree_of_eu hi.freeChain fun ed hed => ?_
    have hed_le := (hi.freeNodeOk ed hed).2.1
    exact hstruct_eq ed hed_le OFF_EU (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)
  have hfreeNode' : ∀ ed ∈ freeEdges, n + 1 ≤ ed ∧ ed ≤ cap ∧
      AuxTree.node ed .leaf .leaf ∈ t₂ :: rest₂ ∧
      nodeField mem_tag nb ed OFF_PPAR = 0 ∧ nodeField mem_tag nb ed OFF_ISV = 0 ∧
      nodeField mem_tag nb ed OFF_HASE = 0 := fun ed hed => by
    rcases hi.freeNodeOk ed hed with ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
    · rw [hstruct_eq ed h2 OFF_PPAR (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)]; exact h4
    · rw [hstruct_eq ed h2 OFF_ISV (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)]; exact h5
    · rw [hstruct_eq ed h2 OFF_HASE (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)]; exact h6
  have hvok' : VertexNodeOk mem_tag nb n := fun k hk => by
    have hk_cap : k + 1 ≤ cap := by dsimp only [cap, lctCap]; omega
    dsimp only [VertexNodeOk] at *
    rw [hstruct_eq (k + 1) hk_cap OFF_ISV (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl),
      hstruct_eq (k + 1) hk_cap OFF_HASE (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)]
    exact hi.vertexOk k hk
  have hread_eq : ∀ z, readAuxTree mem_tag nb cap cap z = readAuxTree mem_in nb cap cap z := fun z => by
    have hgo : ∀ fuel q, readAuxTree mem_tag nb cap fuel q = readAuxTree mem_in nb cap fuel q := by
      intro fuel
      induction fuel with
      | zero => intro q; cases q <;> simp [readAuxTree]
      | succ f ih =>
          intro q
          cases q with
          | zero => simp [readAuxTree]
          | succ q' =>
              simp only [readAuxTree]
              split_ifs with hq
              · rw [hstruct_eq (q' + 1) hq OFF_LEFT (Or.inl rfl),
                  hstruct_eq (q' + 1) hq OFF_RIGHT (Or.inr (Or.inl rfl)), ih, ih]
              · rfl
    exact hgo cap z
  have haux_roots_eq : auxRootIds mem_tag nb cap = auxRootIds mem_in nb cap := by
    unfold auxRootIds
    apply List.filter_congr
    intro r hr
    simp only [List.mem_map, List.mem_range] at hr
    rcases hr with ⟨y, hy, rfl⟩
    simp [hstruct_eq (y + 1) (by omega) OFF_PARENT (Or.inr <| Or.inr <| Or.inl rfl)]
  have hpar_eq : ∀ z, lctAuxParent mem_tag nb cap z = lctAuxParent mem_in nb cap z := fun z => by
    unfold lctAuxParent
    rw [haux_roots_eq]
    have hte : ∀ r ∈ auxRootIds mem_in nb cap,
        treeParentEntry mem_tag nb cap r z = treeParentEntry mem_in nb cap r z := fun r hr => by
      unfold auxRootIds at hr
      simp only [List.mem_filter, List.mem_map, List.mem_range] at hr
      rcases hr with ⟨⟨y, hy, rfl⟩, _⟩
      have hpp_eq := hstruct_eq (y + 1) (by omega) OFF_PPAR (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)
      have hseq_eq : lctTreeSeq mem_tag nb cap (y + 1) = lctTreeSeq mem_in nb cap (y + 1) := by
        unfold lctTreeSeq; rw [hread_eq (y + 1)]
        apply AuxTree.evalInorder_agree; intro q hq
        simp [revFlag, hstruct_eq q (readAuxTree_nodes_bounds hq).2 OFF_REV
          (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)]
      simp only [treeParentEntry, hseq_eq, hpp_eq]
    have hf_congr : ∀ {α β} {l : List α} {f g : α → Option β},
        (∀ a ∈ l, f a = g a) → l.findSome? f = l.findSome? g := by
      intro α β l f g hfg
      induction l with
      | nil => rfl
      | cons x xs ih =>
          rw [List.findSome?_cons, List.findSome?_cons, hfg x List.mem_cons_self]
          cases g x with
          | none => exact ih (fun a ha => hfg a (List.mem_cons_of_mem _ ha))
          | some _ => rfl
    rw [hf_congr hte]
  have haux_seq_eq : ∀ s ∈ t₂ :: rest₂,
      s.evalInorder (revFlag mem_tag nb) false = s.evalInorder (revFlag mem_in nb) false := fun s hs => by
    apply AuxTree.evalInorder_agree
    intro q hq
    have hqb := (SplayForestOk.trees_ok hi.sf s hs).2.2.nodup_perm_mem hq
    simp [revFlag, hstruct_eq q hqb.2 OFF_REV (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)]
  have hauxPath' : LctAuxPathOk mem_tag nb n freeEdges (t₂ :: rest₂) := fun s hs => by
    rcases hi.auxPathOk s hs with ⟨h1, h2, h3⟩
    have hs_ok := (SplayForestOk.trees_ok hi.sf s hs)
    have hrb := hs_ok.2.2.nodup_perm_mem (AuxTree.rootId_mem_toList hs_ok.1)
    have hpp_s := hstruct_eq s.rootId hrb.2 OFF_PPAR (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)
    refine ⟨?_, ?_, ?_⟩
    · simpa [haux_seq_eq s hs] using h1
    · simpa [hpp_s] using h2
    · simpa [hpp_s, haux_seq_eq s hs] using h3
  have hsubdiv' : LctSubdivOk mem_tag nb n freeEdges
      (edgeMap.map fun q => (q.1, MathForest.applyStepsDelta steps δ q.2)) := by
    have hsub1 := lctSubdivOk_of_par_eq hi.subdivOk hpar_eq
    rcases hsub1 with ⟨hs1, hs2, hs3, hs4⟩
    refine ⟨hs1, hs2, ?_, ?_⟩
    · intro k hk
      rcases hs3 k hk with h0 | ⟨p, hp_in, hp_uv, hp_par⟩
      · exact Or.inl h0
      · exact Or.inr ⟨(p.1, MathForest.applyStepsDelta steps δ p.2), List.mem_map_of_mem hp_in,
          by simpa [applyStepsDelta_u, applyStepsDelta_v] using hp_uv, hp_par⟩
    · intro q hq
      rcases List.mem_map.1 hq with ⟨p, hp_in, rfl⟩
      simpa [applyStepsDelta_u, applyStepsDelta_v] using hs4 p hp_in
  have hedgeMap_fst_nd : (edgeMap.map Prod.fst).Nodup := by
    have hp := hslots.nodup_iff.2 ((List.nodup_range).map (fun a b h => by omega))
    exact (List.nodup_append.1 hp).1
  have hedge_unique : ∀ p₁ ∈ edgeMap, ∀ p₂ ∈ edgeMap, p₁.1 = p₂.1 → p₁ = p₂ :=
    (List.nodup_map_iff_inj_on hedgeMap_fst_nd.of_map).1 hedgeMap_fst_nd
  have heid_edge_nd : (edgeMap.map fun p => p.2.eid).Nodup := by
    have hp := (hed_perm.map ForestEdge.eid).nodup_iff.2 hval.2.1
    simpa [List.map_map, Function.comp_def] using hp
  have heid_unique : ∀ p₁ ∈ edgeMap, ∀ p₂ ∈ edgeMap, p₁.2.eid = p₂.2.eid → p₁ = p₂ :=
    (List.nodup_map_iff_inj_on hedgeMap_fst_nd.of_map).1 heid_edge_nd
  have hslot_bd : ∀ p ∈ edgeMap, n + 1 ≤ p.1 ∧ p.1 ≤ cap := fun p hp => by
    have hm := hslots.mem_iff.1 (List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩))
    rcases List.mem_map.1 hm with ⟨i, hi_rg, hei⟩
    rw [List.mem_range] at hi_rg; dsimp only [cap, lctCap]; omega
  have hedge' : ActiveEdgeNodeOk mem_tag nb h L P n (t₂ :: rest₂)
      (edgeMap.map fun q => (q.1, MathForest.applyStepsDelta steps δ q.2)) := by
    intro q hq
    rcases List.mem_map.1 hq with ⟨p, hp_in, rfl⟩
    rcases hi.edgeOk p hp_in with
      ⟨hnp1, hpc, hisv, hhase, heid, heu, hev, t', ht', hed_t', r', hr'_mem, hmatch', hor'⟩
    have hpar_ed : lctAuxParent mem_tag nb cap p.1 = lctAuxParent mem_in nb cap p.1 := hpar_eq p.1
    have hpar_u : lctAuxParent mem_tag nb cap (p.2.u + 1) = lctAuxParent mem_in nb cap (p.2.u + 1) :=
      hpar_eq _
    have hpar_v : lctAuxParent mem_tag nb cap (p.2.v + 1) = lctAuxParent mem_in nb cap (p.2.v + 1) :=
      hpar_eq _
    refine ⟨hnp1, hpc,
      (hstruct_eq p.1 hpc OFF_ISV (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)).trans hisv,
      (hstruct_eq p.1 hpc OFF_HASE (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)).trans hhase,
      by simp [applyStepsDelta_eid,
        (hstruct_eq p.1 hpc OFF_EID (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)).trans heid],
      by simp [applyStepsDelta_u,
        (hstruct_eq p.1 hpc OFF_EU (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)).trans heu],
      by simp [applyStepsDelta_v,
        (hstruct_eq p.1 hpc OFF_EV (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)).trans hev],
      ?_⟩
    have hp_fun : lctAuxParent mem_tag nb cap = lctAuxParent mem_in nb cap := funext hpar_eq
    have hp_fun' : lctAuxParent mem_tag (lctNodesBase b) (lctCap n) =
        lctAuxParent mem_in (lctNodesBase b) (lctCap n) := hp_fun
    simp only [List.mem_cons] at ht'
    rcases ht' with rfl | ht'_rest
    · refine ⟨t₂, by simp [t₂], hed_t', r'.addDelta d, ?_, ?_, ?_⟩
      · rw [hsteps_tag]; exact List.mem_map_of_mem hr'_mem
      · rcases (List.forall₂_iff_get.1 hfor) with ⟨hlen, hget⟩
        rcases List.getElem_of_mem hr'_mem with ⟨k, hk, hr'_eq⟩
        have hk_st : k < steps.length := hlen ▸ hk
        rcases hget k hk hk_st with ⟨ed'', hm'', hfwd''⟩
        dsimp only [List.get_eq_getElem] at hm'' hfwd''
        rw [show (evalMemSteps mem_in (lctNodesBase b) h L (.node (v + 1) l₂ .leaf) false 0)[k] = r'
          from hr'_eq] at hm'' hfwd''
        set s := steps[k]'hk_st
        have hfind_s : steps.find? (fun q => q.edge.eid == p.2.eid) = some s :=
          steps_find?_eq_some_of_nodup hsteps_eid_nd hk_st (by rw [← hm''.2.1, hmatch'.2.1])
        have happ : MathForest.applyStepsDelta steps δ p.2 = p.2.addFlow r'.fwd δ := by
          dsimp only [MathForest.applyStepsDelta]
          rw [show steps.find? (fun s => s.edge.eid == p.2.eid) = some s from hfind_s]
          dsimp only
          rw [hfwd'']
        rw [happ]
        exact stepMatchesEdge_addDelta hδ hmatch'
      · have hfwd_add : (r'.addDelta d).fwd = r'.fwd := by
          cases hrf : r'.fwd <;> simp [RawStep.addDelta, hrf]
        rw [hfwd_add]
        have hpar_ed' : lctAuxParent mem_tag (lctNodesBase b) (lctCap n) p.1 =
            lctAuxParent mem_in (lctNodesBase b) (lctCap n) p.1 := congrFun hp_fun' _
        have hpar_u' : lctAuxParent mem_tag (lctNodesBase b) (lctCap n) (p.2.u + 1) =
            lctAuxParent mem_in (lctNodesBase b) (lctCap n) (p.2.u + 1) := congrFun hp_fun' _
        have hpar_v' : lctAuxParent mem_tag (lctNodesBase b) (lctCap n) (p.2.v + 1) =
            lctAuxParent mem_in (lctNodesBase b) (lctCap n) (p.2.v + 1) := congrFun hp_fun' _
        have hpar_ed'' : lctAuxParent mem_tag nb cap p.1 =
            lctAuxParent mem_in (lctNodesBase b) (lctCap n) p.1 := hpar_ed'
        have hpar_u'' : lctAuxParent mem_tag nb cap (p.2.u + 1) =
            lctAuxParent mem_in (lctNodesBase b) (lctCap n) (p.2.u + 1) := hpar_u'
        have hpar_v'' : lctAuxParent mem_tag nb cap (p.2.v + 1) =
            lctAuxParent mem_in (lctNodesBase b) (lctCap n) (p.2.v + 1) := hpar_v'
        rw [applyStepsDelta_u, applyStepsDelta_v, hpar_ed'', hpar_u'', hpar_v'']
        exact hor'
    · refine ⟨t', by simp [ht'_rest], hed_t', r', ?_, ?_, ?_⟩
      · have hptrs : ∀ z ∈ t'.toList, ∀ off ∈ ptrOffs,
            let ptr := nodeField mem_in nb z off
            ptr = 0 ∨ ∀ i < L, mem_tag (ptr + i) = mem_in (ptr + i) := fun z hz off hoff => by
          have hz_ok := (SplayForestOk.trees_ok hi.sf t' (by simp [ht'_rest])).2.2
          have hpb := treeMemMatch_ptr_bounds hz_ok hz hoff
          rcases hpb with h0 | ⟨hlo, hhi⟩
          · exact Or.inl h0
          · refine Or.inr fun i hi_lt => ?_
            dsimp only [nb, cap] at hlo hhi hheap_in ⊢
            have ha1 : lctNodesBase b + NODE_STRIDE * (lctCap n + 1) ≤
                nodeField mem_in (lctNodesBase b) z off + i :=
              Nat.le_trans hlo (Nat.le_add_right _ _)
            have ha2 : nodeField mem_in (lctNodesBase b) z off + i < mem_in (lctNodesBase b - 1) := by
              omega
            exact hheap_in _ ha1 ha2
        rw [evalMemSteps_agree_ptrs ((SplayForestOk.trees_ok hi.sf t' (by simp [ht'_rest])).2.2)
          (hrest_fields t' ht'_rest) hptrs false 0]
        exact hr'_mem
      · have hno_step : ∀ s ∈ steps, s.edge.eid ≠ p.2.eid := fun s hs heid_eq => by
          rcases List.getElem_of_mem hs with ⟨k, hk, rfl⟩
          rcases (List.forall₂_iff_get.1 hfor) with ⟨hlen, hget⟩
          have hk_ev : k < (evalMemSteps mem_in (lctNodesBase b) h L (.node (v + 1) l₂ .leaf) false 0).length :=
            hlen.symm ▸ hk
          rcases hget k hk_ev hk with ⟨ed'', hm'', _⟩
          have hrk_in : (evalMemSteps mem_in (lctNodesBase b) h L (.node (v + 1) l₂ .leaf) false 0)[k]'hk_ev ∈
              evalMemSteps mem_in (lctNodesBase b) h L (.node (v + 1) l₂ .leaf) false 0 :=
            List.getElem_mem _
          have hk_t2 : ed'' ∈ t₂.toList := by
            have := evalMemSteps_nodeId_mem_toList hrk_in
            dsimp only [List.get_eq_getElem] at hm''
            simpa [t₂, hm''.1] using this
          have hrk_meta := evalMemSteps_hase_nz_and_eid hrk_in
          dsimp only [List.get_eq_getElem] at hm''
          rw [hm''.1] at hrk_meta
          have hed_b := (SplayForestOk.trees_ok hi.sf t₂ (by simp [t₂])).2.2.nodup_perm_mem hk_t2
          rcases hed_b with ⟨hed_b1, hed_b2⟩
          unfold lctCap at hed_b2
          have hnot_v : ¬ ed'' ≤ n := by
            intro hle_n
            have hv0 := (hi.vertexOk (ed'' - 1) (by omega)).2
            rw [show ed'' - 1 + 1 = ed'' by omega] at hv0
            exact hrk_meta.1 hv0
          have hnot_f : ed'' ∉ freeEdges := fun hf =>
            hrk_meta.1 (hi.freeNodeOk ed'' hf).2.2.2.2.2
          have hdiff : ed'' - (n + 1) < n := by omega
          have hsum_ed : n + 1 + (ed'' - (n + 1)) = ed'' := by omega
          have hsl := hslots.symm.mem_iff.1 (List.mem_map.2 ⟨ed'' - (n + 1),
            List.mem_range.2 hdiff, hsum_ed⟩)
          rcases List.mem_append.1 hsl with hmap | hfr
          · rcases List.mem_map.1 hmap with ⟨p₀, hp0_in, hp0_1⟩
            have hp0_ok := hi.edgeOk p₀ hp0_in
            have hpeid_eq : p₀.2.eid = p.2.eid := by
              rw [← hp0_ok.2.2.2.2.1, hp0_1, ← hrk_meta.2, hm''.2.1, heid_eq]
            have hp_eq := heid_unique p₀ hp0_in p hp_in hpeid_eq
            subst hp_eq
            rw [List.flatMap_cons, List.nodup_append] at hnd_all
            have hed_rest : p₀.1 ∈ rest₂.flatMap AuxTree.toList :=
              List.mem_flatMap.2 ⟨t', ht'_rest, hed_t'⟩
            exact hnd_all.2.2 p₀.1 (hp0_1 ▸ hk_t2) p₀.1 hed_rest rfl
          · exact hnot_f hfr
        have hfind_none : steps.find? (fun q => q.edge.eid == p.2.eid) = none :=
          List.find?_eq_none.2 fun s hs heq => hno_step s hs (beq_iff_eq.1 heq)
        simpa [MathForest.applyStepsDelta, hfind_none] using hmatch'
      · have hpar_ed'' : lctAuxParent mem_tag nb cap p.1 =
            lctAuxParent mem_in (lctNodesBase b) (lctCap n) p.1 := congrFun hp_fun' _
        have hpar_u'' : lctAuxParent mem_tag nb cap (p.2.u + 1) =
            lctAuxParent mem_in (lctNodesBase b) (lctCap n) (p.2.u + 1) := congrFun hp_fun' _
        have hpar_v'' : lctAuxParent mem_tag nb cap (p.2.v + 1) =
            lctAuxParent mem_in (lctNodesBase b) (lctCap n) (p.2.v + 1) := congrFun hp_fun' _
        rw [applyStepsDelta_u, applyStepsDelta_v, hpar_ed'', hpar_u'', hpar_v'']
        exact hor'
  have hrep_sz_eq : ∀ y, lctRepSize mem_tag nb cap y = lctRepSize mem_in nb cap y := fun y => by
    unfold lctRepSize; congr 1; apply List.filter_congr; intro u _
    have hp_fun : lctAuxParent mem_tag nb cap = lctAuxParent mem_in nb cap := funext hpar_eq
    simp [reachesIn, hp_fun]
  have htreeSeq_eq : ∀ r, lctTreeSeq mem_tag nb cap r = lctTreeSeq mem_in nb cap r := fun r => by
    unfold lctTreeSeq; rw [hread_eq r]
    apply AuxTree.evalInorder_agree; intro q hq
    simp [revFlag, hstruct_eq q (readAuxTree_nodes_bounds hq).2 OFF_REV
      (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)]
  have hvsize_eq : ∀ y, lctVSize mem_tag nb cap y = lctVSize mem_in nb cap y := fun y => by
    unfold lctVSize; rw [haux_roots_eq]
    have hfilt : (auxRootIds mem_in nb cap).filter (fun r => decide (nodeField mem_tag nb r OFF_PPAR = y)) =
        (auxRootIds mem_in nb cap).filter (fun r => decide (nodeField mem_in nb r OFF_PPAR = y)) :=
      List.filter_congr fun r hr => by
        have hrb : r ≤ cap := by
          unfold auxRootIds at hr; simp only [List.mem_filter, List.mem_map, List.mem_range] at hr
          rcases hr with ⟨⟨z, hz, rfl⟩, _⟩; omega
        simp [hstruct_eq r hrb OFF_PPAR (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl)]
    rw [hfilt]; congr 1; apply List.map_congr_left; intro r _
    simp [dashedChildSize, htreeSeq_eq r, hrep_sz_eq]
  have hheavy_eq : lctHeavyCount mem_tag nb cap = lctHeavyCount mem_in nb cap := by
    unfold lctHeavyCount; rw [haux_roots_eq]; congr 1; apply List.filter_congr; intro r hr
    have hrb : r ≤ cap := by
      unfold auxRootIds at hr; simp only [List.mem_filter, List.mem_map, List.mem_range] at hr
      rcases hr with ⟨⟨z, hz, rfl⟩, _⟩; omega
    simp only [isHeavyRoot, hstruct_eq r hrb OFF_PPAR (Or.inr <| Or.inr <| Or.inr <| Or.inl rfl),
      htreeSeq_eq r]
    cases lctTreeSeq mem_in nb cap r with
    | nil => simp
    | cons hd _ => simp [hrep_sz_eq]
  have hphi_eq : lctPhi L mem_tag b n = lctPhi L mem_in b n := by
    unfold lctPhi
    change splayMemPhi (K_SPLAY_STEP L) mem_tag nb cap (lctVSize mem_tag nb cap) +
        C_HEAVY L * lctHeavyCount mem_tag nb cap =
      splayMemPhi (K_SPLAY_STEP L) mem_in nb cap (lctVSize mem_in nb cap) +
        C_HEAVY L * lctHeavyCount mem_in nb cap
    rw [hheavy_eq]
    congr 1
    have hvs_fn : lctVSize mem_tag nb cap = lctVSize mem_in nb cap := funext hvsize_eq
    rw [hvs_fn]
    unfold splayMemPhi
    rw [haux_roots_eq]
    congr 2; apply List.map_congr_left; intro r _; rw [hread_eq r]
  exact ⟨⟨hhdrN', hhdrCap', hhdrL', hhdrP', hsf', hfreeChain', hfreeNode', hvok', hedge',
      hauxPath', hsubdiv'⟩, hphi_eq⟩

theorem pathAdd_safeMem_weaken {L b nb cap hp_caller : ℕ} {mem₀ mem_cp mem_st : ℕ → ℕ}
    (hnb : nb = lctNodesBase b) (hnb_eq : nb - 1 = b + LCT_HDR_HP)
    (harena_hp : lctArenaHi b cap ≤ hp_caller)
    (hcp_out : ∀ a, a < hp_caller ∨ hp_caller + L ≤ a → mem_cp a = mem₀ a)
    (hsafe : SafeMem (Function.update mem_cp (nb - 1) (hp_caller + L)) nb cap (hp_caller + L) mem_st) :
    SafeMem (Function.update mem₀ (nb - 1) hp_caller) nb cap hp_caller mem_st := by
  let mem_base := Function.update mem₀ (nb - 1) hp_caller
  let mem₁ := Function.update mem_cp (nb - 1) (hp_caller + L)
  have hpos : 1 ≤ nb := by rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE; omega
  have hlt_arena : nb - 1 < nb + NODE_STRIDE * (cap + 1) := by
    have hmul : NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    unfold NODE_STRIDE at hmul; omega
  have hnb1_lt_hp : nb - 1 < hp_caller := by
    have : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller := by simpa [lctArenaHi, hnb] using harena_hp
    omega
  refine ⟨le_trans (Nat.le_add_right _ _) hsafe.1, ?_, hsafe.2.2.1, ?_⟩
  · intro a ha
    have ha_ne : a ≠ nb - 1 := by
      rcases ha with hl | ⟨hl, _⟩ | ⟨hl, _⟩
      · omega
      · omega
      · exact ne_of_gt (lt_of_lt_of_le hlt_arena hl)
    have ha' : a < nb - 1 ∨ (nb ≤ a ∧ a < nb + NODE_STRIDE) ∨
        (nb + NODE_STRIDE * (cap + 1) ≤ a ∧ a < hp_caller + L) := by
      rcases ha with hl | hl | ⟨hl, hr⟩
      · exact Or.inl hl
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr ⟨hl, lt_of_lt_of_le hr (Nat.le_add_right _ _)⟩)
    rw [hsafe.2.1 a ha']
    rw [Function.update_of_ne ha_ne, Function.update_of_ne ha_ne]
    rcases ha with hl | ⟨_, hr⟩ | ⟨_, hr⟩
    · exact hcp_out a (Or.inl (lt_trans hl hnb1_lt_hp))
    · have hle_arena : nb + NODE_STRIDE ≤ nb + NODE_STRIDE * (cap + 1) :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_right NODE_STRIDE (Nat.succ_pos cap)) nb
      have harena_le : nb + NODE_STRIDE * (cap + 1) ≤ hp_caller := by
        simpa [lctArenaHi, hnb] using harena_hp
      exact hcp_out a (Or.inl (lt_of_lt_of_le hr (le_trans hle_arena harena_le)))
    · exact hcp_out a (Or.inl hr)
  · intro x off hx1 hx2 hoff
    rcases hsafe.2.2.2 x off hx1 hx2 hoff with hp0 | hp_hi | ⟨y, off', hy1, hy2, hoff', hy_eq⟩
    · exact Or.inl hp0
    · exact Or.inr (Or.inl (le_trans (Nat.le_add_right _ _) hp_hi))
    · refine Or.inr (Or.inr ⟨y, off', hy1, hy2, hoff', ?_⟩)
      have hy_addr : nb + NODE_STRIDE * y + off' < nb + NODE_STRIDE * (cap + 1) := by
        have : off' < NODE_STRIDE := ptrOffs_lt_stride hoff'
        have : NODE_STRIDE * y + off' < NODE_STRIDE * (cap + 1) := by
          have := Nat.mul_le_mul_left NODE_STRIDE (by omega : y + 1 ≤ cap + 1)
          rw [Nat.mul_add, Nat.mul_one] at this; omega
        omega
      have hle_y : nb ≤ nb + NODE_STRIDE * y + off' :=
        Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
      have hne_y : nb + NODE_STRIDE * y + off' ≠ nb - 1 := by omega
      have hlt_hp_y : nb + NODE_STRIDE * y + off' < hp_caller :=
        lt_of_lt_of_le hy_addr (by simpa [lctArenaHi, hnb] using harena_hp)
      rw [hy_eq]
      dsimp only [nodeField]
      rw [Function.update_of_ne hne_y, Function.update_of_ne hne_y, hcp_out _ (Or.inl hlt_hp_y)]

end PathAddInvariants

end MinCostFlow.LinkCut.Prog
