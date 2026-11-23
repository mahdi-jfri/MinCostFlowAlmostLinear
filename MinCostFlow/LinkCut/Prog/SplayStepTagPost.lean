module

public import MinCostFlow.LinkCut.Prog.SplayStepTagBlocks

namespace MinCostFlow.LinkCut.Prog

/-!
Pure post-state memory, frame, tag, aggregate, and tree-matching lemmas for `applyTagBody`.
-/

open WordRAM MinCostFlow.Num

@[expose] public section

theorem nodeHeapStepMem_node_ne {nodesBase cap x hp₀ hp₁ : ℕ} {mem₀ mem₁ : ℕ → ℕ}
    (nhs : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) hp₀ hp₁ mem₀ mem₁)
    {u off : ℕ} (hu : u ≤ cap) (hux : u ≠ x) (hoff : off < NODE_STRIDE) :
    nodeField mem₁ nodesBase u off = nodeField mem₀ nodesBase u off := by
  apply nhs.2.2.1
  · have hm : NODE_STRIDE * u ≤ NODE_STRIDE * cap := Nat.mul_le_mul_left NODE_STRIDE hu
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · intro off' hoff' hEq
    rcases lt_or_gt_of_ne hux with hlt | hgt
    · have hm := Nat.mul_le_mul_left NODE_STRIDE (by omega : u + 1 ≤ x)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
    · have hm := Nat.mul_le_mul_left NODE_STRIDE (by omega : x + 1 ≤ u)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega

theorem applyTagBody_post_frame_children {w h L nodesBase cap x hp₈ : ℕ}
    {l r : AuxTree} {mem₀ mem₈ mem₉ : ℕ → ℕ}
    (hnb : 3 ≤ nodesBase)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hz : ZeroFrom mem₀ (mem₀ (nodesBase - 1)))
    (hx1 : 1 ≤ x)
    (hl_m : TreeMemMatch w h L mem₀ nodesBase cap l x 0)
    (hr_m : TreeMemMatch w h L mem₀ nodesBase cap r x 0)
    (hx_l : x ∉ l.toList) (hx_r : x ∉ r.toList)
    (nhs : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) (mem₀ (nodesBase - 1)) hp₈ mem₀ mem₈)
    (hm9_hp : mem₉ (nodesBase - 1) = hp₈)
    (hm9_ne : ∀ a, a ≠ nodesBase - 1 → mem₉ a = mem₈ a) :
    (∀ u ≤ cap, u ≠ x → ∀ off < NODE_STRIDE,
      nodeField mem₉ nodesBase u off = nodeField mem₀ nodesBase u off) ∧
    (∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nodesBase - 1) → mem₉ a = mem₀ a) ∧
    LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₀ mem₉ ∧
    TreeMemMatch w h L mem₉ nodesBase cap l x 0 ∧
    TreeMemMatch w h L mem₉ nodesBase cap r x 0 ∧
    (∀ fl d1, evalMemSteps mem₉ nodesBase h L l fl d1 = evalMemSteps mem₀ nodesBase h L l fl d1) ∧
    (∀ fl d1, evalMemSteps mem₉ nodesBase h L r fl d1 = evalMemSteps mem₀ nodesBase h L r fl d1) := by
  have hm9_ge : ∀ a, nodesBase ≤ a → mem₉ a = mem₈ a := fun a ha => hm9_ne a (by omega)
  have hmem9_node_ne : ∀ u ≤ cap, u ≠ x → ∀ off < NODE_STRIDE,
      nodeField mem₉ nodesBase u off = nodeField mem₀ nodesBase u off := by
    intro u hu hux off hoff
    have hnf9 : nodeField mem₉ nodesBase u off = nodeField mem₈ nodesBase u off := hm9_ge _ (by omega)
    rw [hnf9]
    exact nodeHeapStepMem_node_ne nhs hu hux hoff
  have hheap9 : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nodesBase - 1) →
      mem₉ a = mem₀ a := fun a ha1 ha2 => by
    have hle : nodesBase ≤ nodesBase + NODE_STRIDE * (cap + 1) := by omega
    rw [hm9_ge a (Nat.le_trans hle ha1)]
    exact nhs.2.2.2 a ha1 ha2
  have hframe9 : LctFrame (nodesBase + NODE_STRIDE) (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase - 1) mem₀ mem₉ := by
    have hnb1 : nodesBase - 1 < hp₈ := by
      have hna : nodesBase ≤ nodesBase + NODE_STRIDE * (cap + 1) := by omega
      exact lt_of_lt_of_le (by omega) (Nat.le_trans hna (Nat.le_trans harena nhs.1))
    refine ⟨by dsimp only [NODE_STRIDE]; omega, harena, by rw [hm9_hp]; exact nhs.1, hz,
      by rw [hm9_hp]; exact fun a ha => by rw [hm9_ne a (by omega)]; exact nhs.2.1 a ha, ?_⟩
    intro i hi
    rcases hi with ⟨hlo, hne⟩ | ⟨hge, hlt⟩
    · rw [hm9_ne i hne]
      apply nhs.2.2.1
      · have hm := Nat.mul_le_mul_left NODE_STRIDE (by omega : 1 ≤ cap + 1)
        rw [Nat.mul_one] at hm
        omega
      · intro off _ hEq
        have hm := Nat.mul_le_mul_left NODE_STRIDE hx1
        rw [Nat.mul_one] at hm
        omega
    · exact hheap9 i hge hlt
  have hl_m' : TreeMemMatch w h L mem₉ nodesBase cap l x 0 :=
    memAgree_treeMemMatch_of_nodeList hl_m
      (fun u hu off hoff => hmem9_node_ne u (hl_m.nodup_perm_mem hu).2 (fun h => hx_l (h ▸ hu)) off hoff)
      (by rw [hm9_hp]; exact nhs.1) hheap9
  have hr_m' : TreeMemMatch w h L mem₉ nodesBase cap r x 0 :=
    memAgree_treeMemMatch_of_nodeList hr_m
      (fun u hu off hoff => hmem9_node_ne u (hr_m.nodup_perm_mem hu).2 (fun h => hx_r (h ▸ hu)) off hoff)
      (by rw [hm9_hp]; exact nhs.1) hheap9
  have hl_steps_eq : ∀ fl d1, evalMemSteps mem₉ nodesBase h L l fl d1 = evalMemSteps mem₀ nodesBase h L l fl d1 :=
    fun fl d1 => evalMemSteps_agree hl_m
      (fun u hu off hoff => hmem9_node_ne u (hl_m.nodup_perm_mem hu).2 (fun h => hx_l (h ▸ hu)) off hoff) hheap9 fl d1
  have hr_steps_eq : ∀ fl d1, evalMemSteps mem₉ nodesBase h L r fl d1 = evalMemSteps mem₀ nodesBase h L r fl d1 :=
    fun fl d1 => evalMemSteps_agree hr_m
      (fun u hu off hoff => hmem9_node_ne u (hr_m.nodup_perm_mem hu).2 (fun h => hx_r (h ▸ hu)) off hoff) hheap9 fl d1
  exact ⟨hmem9_node_ne, hheap9, hframe9, hl_m', hr_m', hl_steps_eq, hr_steps_eq⟩

theorem applyTagBody_post_own_eq {h L nodesBase cap x tPtr tNeg hp₅ : ℕ}
    {l r : AuxTree} {mem₀ mem₅ mem₉ : ℕ → ℕ} {d : ℤ}
    (hhe : nodeField mem₀ nodesBase x OFF_HASE ≤ 1)
    (he1 : nodeField mem₀ nodesBase x OFF_HASE = 1 →
      NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L
        (nodeField mem₀ nodesBase x OFF_FLOW_PTR) ∧
      NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L
        (nodeField mem₀ nodesBase x OFF_AF_PTR) ∧
      NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L
        (nodeField mem₀ nodesBase x OFF_AB_PTR) ∧
      NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L
        (nodeField mem₀ nodesBase x OFF_COST_FWD) ∧
      NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L
        (nodeField mem₀ nodesBase x OFF_COST_BWD) ∧
      intVal mem₀ (nodeField mem₀ nodesBase x OFF_COST_BWD) h L =
        wrap h L (-intVal mem₀ (nodeField mem₀ nodesBase x OFF_COST_FWD) h L))
    (hfit_own0 : ∀ s, nodeOwnRawStep mem₀ nodesBase h L x = some s →
      Fits h L s.flow ∧ Fits h L s.availFwd ∧ Fits h L s.availBwd)
    (hdmod : d % (capacity h L : ℤ) =
      (if tNeg = 0 then intVal mem₀ tPtr h L else -intVal mem₀ tPtr h L) % (capacity h L : ℤ))
    (hfit : StepsShiftFit h L (evalMemSteps mem₀ nodesBase h L (.node x l r) false 0) d)
    (nhs5 : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) (mem₀ (nodesBase - 1)) hp₅ mem₀ mem₅)
    (hstep_agree_x : ∀ off < NODE_STRIDE,
      off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL → off ≠ OFF_HAS_TAG →
      off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
      mem₉ (nodesBase + NODE_STRIDE * x + off) = mem₅ (nodesBase + NODE_STRIDE * x + off))
    (hhp_ag : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < hp₅ → mem₉ a = mem₅ a)
    (hmem9_hase : mem₉ (nodesBase + NODE_STRIDE * x + OFF_HASE) =
      mem₀ (nodesBase + NODE_STRIDE * x + OFF_HASE))
    (hmem5_cost : mem₅ (nodesBase + NODE_STRIDE * x + OFF_COST_FWD) =
      mem₀ (nodesBase + NODE_STRIDE * x + OFF_COST_FWD) ∧
      mem₅ (nodesBase + NODE_STRIDE * x + OFF_COST_BWD) =
      mem₀ (nodesBase + NODE_STRIDE * x + OFF_COST_BWD))
    (hhe5_post : nodeField mem₀ nodesBase x OFF_HASE = 1 →
      ∃ s₀, nodeOwnRawStep mem₀ nodesBase h L x = some s₀ ∧
        NumPtrOk mem₅ (nodesBase + NODE_STRIDE * (cap + 1)) hp₅ h L
          (mem₅ (nodesBase + NODE_STRIDE * x + OFF_AF_PTR)) ∧
        NumPtrOk mem₅ (nodesBase + NODE_STRIDE * (cap + 1)) hp₅ h L
          (mem₅ (nodesBase + NODE_STRIDE * x + OFF_AB_PTR)) ∧
        NumPtrOk mem₅ (nodesBase + NODE_STRIDE * (cap + 1)) hp₅ h L
          (mem₅ (nodesBase + NODE_STRIDE * x + OFF_FLOW_PTR)) ∧
        nodeOwnRawStep mem₅ nodesBase h L x =
          some (s₀.addDeltaMod h L (if tNeg = 0 then intVal mem₀ tPtr h L else -intVal mem₀ tPtr h L))) :
    ((nodeOwnRawStep mem₉ nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList =
      (((nodeOwnRawStep mem₀ nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList).map
        (fun q => q.addDelta d) := by
  let steps := evalMemSteps mem₀ nodesBase h L (.node x l r) false 0
  by_cases hhe0 : nodeField mem₀ nodesBase x OFF_HASE = 0
  · have hhe0' : nodeField mem₉ nodesBase x OFF_HASE = 0 := by
      dsimp only [nodeField] at hhe0 ⊢
      rw [hmem9_hase, hhe0]
    simp [nodeOwnRawStep, hhe0, hhe0']
  · have hhe1 : nodeField mem₀ nodesBase x OFF_HASE = 1 := by omega
    rcases hhe5_post hhe1 with ⟨s₀, hs₀_eq, haf5, hab5, hfl5, hs5_eq⟩
    have hfit₀ := hfit_own0 s₀ hs₀_eq
    have hs₀_mod0 : s₀.addDeltaMod h L 0 = s₀ := RawStep.addDeltaMod_zero hfit₀.1 hfit₀.2.1 hfit₀.2.2
    have hs₀_in : s₀ ∈ steps := by
      simp [steps, evalMemSteps, hs₀_eq, hs₀_mod0]
    have hfit_s₀ := hfit s₀ hs₀_in
    have hδ_s₀ : s₀.addDeltaMod h L (if tNeg = 0 then intVal mem₀ tPtr h L else -intVal mem₀ tPtr h L) =
        s₀.addDelta d := by
      have hlist := stepsShiftFit_map_addDeltaMod_eq (h := h) (L := L) (steps := [s₀])
        (fun q hq => by simp at hq; subst hq; exact hfit_s₀) hdmod.symm
      simpa using hlist
    have hfit_sd : Fits h L (s₀.addDelta d).flow ∧ Fits h L (s₀.addDelta d).availFwd ∧
        Fits h L (s₀.addDelta d).availBwd := by
      cases hf : s₀.fwd <;> simp only [RawStep.addDelta, hf, ↓reduceIte, Bool.false_eq_true] at hfit_s₀ ⊢ <;>
        exact ⟨hfit_s₀.2.2.2.1, hfit_s₀.2.2.2.2.1, hfit_s₀.2.2.2.2.2⟩
    have hown9 : nodeOwnRawStep mem₉ nodesBase h L x = some (s₀.addDelta d) := by
      rw [← hδ_s₀, ← hs5_eq]
      rcases he1 hhe1 with ⟨_, _, _, pcf, pcb, _⟩
      have hz9 := hstep_agree_x OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      by_cases hz5 : mem₅ (nodesBase + NODE_STRIDE * x + OFF_HASE) = 0
      · have hnone : nodeOwnRawStep mem₅ nodesBase h L x = none := by
          simp [nodeOwnRawStep, nodeField, hz5]
        rw [hnone] at hs5_eq
        cases hs5_eq
      · have hnz9 : nodeField mem₉ nodesBase x OFF_HASE ≠ 0 := by
          dsimp only [nodeField]; rw [hz9]; exact hz5
        have hnz5 : nodeField mem₅ nodesBase x OFF_HASE ≠ 0 := hz5
        dsimp only [nodeOwnRawStep]
        rw [ite_eq_right hnz9, ite_eq_right hnz5]
        let hnf_eq : ∀ off < NODE_STRIDE,
            off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL → off ≠ OFF_HAS_TAG →
            off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
            nodeField mem₉ nodesBase x off = nodeField mem₅ nodesBase x off :=
          hstep_agree_x
        have hfl_eq9 := hnf_eq OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have haf_eq9 := hnf_eq OFF_AF_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hab_eq9 := hnf_eq OFF_AB_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hcf_eq9 := hnf_eq OFF_COST_FWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hcb_eq9 := hnf_eq OFF_COST_BWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hdir_eq9 := hnf_eq OFF_DIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have heid_eq9 := hnf_eq OFF_EID (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have heu_eq9 := hnf_eq OFF_EU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have hev_eq9 := hnf_eq OFF_EV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        have pcf5 := nodeHeapStepMem_numPtrOk nhs5 pcf
        have pcb5 := nodeHeapStepMem_numPtrOk nhs5 pcb
        dsimp only [nodeField] at pcf5 pcb5
        rw [hdir_eq9, heid_eq9, heu_eq9, hev_eq9, hfl_eq9, haf_eq9, hab_eq9, hcf_eq9, hcb_eq9]
        dsimp only [nodeField]
        rw [hmem5_cost.1, hmem5_cost.2,
          intVal_agree_heap hhp_ag hfl5.2.1 hfl5.2.2.1,
          intVal_agree_heap hhp_ag haf5.2.1 haf5.2.2.1,
          intVal_agree_heap hhp_ag hab5.2.1 hab5.2.2.1,
          intVal_agree_heap hhp_ag pcf5.2.1 pcf5.2.2.1,
          intVal_agree_heap hhp_ag pcb5.2.1 pcb5.2.2.1]
    simp [hs₀_eq, hs₀_mod0, hown9, RawStep.addDeltaMod_zero hfit_sd.1 hfit_sd.2.1 hfit_sd.2.2]

theorem applyTagBody_post_tag_steps {w h L nodesBase cap x tPtr tNeg hp₇ hp₈ : ℕ}
    {l r : AuxTree} {mem₀ mem₇ mem₈ mem₉ : ℕ → ℕ} {d : ℤ}
    (hnb : 3 ≤ nodesBase)
    (h0 : SlotZeroOk mem₀ nodesBase)
    (hht : nodeField mem₀ nodesBase x OFF_HAS_TAG ≤ 1)
    (htn : nodeField mem₀ nodesBase x OFF_TAG_NEG ≤ 1)
    (htag1 : nodeField mem₀ nodesBase x OFF_HAS_TAG = 1 →
      NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L
        (nodeField mem₀ nodesBase x OFF_TAG_PTR) ∧
      ((l ≠ .leaf ∧ nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS = 1) ∨
       (r ≠ .leaf ∧ nodeField mem₀ nodesBase r.rootId OFF_MIN1_HAS = 1)) ∧
      ∃ d₀ : ℤ, d₀ % (capacity h L : ℤ) = nodeTagInt mem₀ nodesBase h L x % (capacity h L : ℤ) ∧
        StepsShiftFit h L
          (evalMemSteps mem₀ nodesBase h L l (revFlag mem₀ nodesBase x) 0 ++
           evalMemSteps mem₀ nodesBase h L r (revFlag mem₀ nodesBase x) 0) d₀)
    (htag0 : nodeField mem₀ nodesBase x OFF_HAS_TAG = 0 →
      nodeField mem₀ nodesBase x OFF_TAG_PTR = 0 ∧
      nodeField mem₀ nodesBase x OFF_TAG_NEG = 0)
    (hl_m : TreeMemMatch w h L mem₀ nodesBase cap l x 0)
    (hr_m : TreeMemMatch w h L mem₀ nodesBase cap r x 0)
    (hx_l : x ∉ l.toList) (hx_r : x ∉ r.toList)
    (htNeg : tNeg ≤ 1)
    (htPtr : NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L tPtr)
    (hdmod : d % (capacity h L : ℤ) =
      (if tNeg = 0 then intVal mem₀ tPtr h L else -intVal mem₀ tPtr h L) % (capacity h L : ℤ))
    (hfit : StepsShiftFit h L (evalMemSteps mem₀ nodesBase h L (.node x l r) false 0) d)
    (hm9_ne : ∀ a, a ≠ nodesBase - 1 → mem₉ a = mem₈ a)
    (hheap9 : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nodesBase - 1) → mem₉ a = mem₀ a)
    (hmem9_node_ne : ∀ u ≤ cap, u ≠ x → ∀ off < NODE_STRIDE,
      nodeField mem₉ nodesBase u off = nodeField mem₀ nodesBase u off)
    (hmem7_node_le : ∀ u ≤ cap, u ≠ x → ∀ off < NODE_STRIDE,
      nodeField mem₇ nodesBase u off = nodeField mem₀ nodesBase u off)
    (h0_m1_7 : mem₇ (nodesBase + OFF_MIN1_HAS) = 0)
    (hmem7_oth_x : ∀ off < NODE_STRIDE, off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
      off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL →
      mem₇ (nodesBase + NODE_STRIDE * x + off) = mem₀ (nodesBase + NODE_STRIDE * x + off))
    (nhs567 : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) (mem₀ (nodesBase - 1)) hp₇ mem₀ mem₇)
    (hl_steps_eq : ∀ fl d1, evalMemSteps mem₉ nodesBase h L l fl d1 = evalMemSteps mem₀ nodesBase h L l fl d1)
    (hr_steps_eq : ∀ fl d1, evalMemSteps mem₉ nodesBase h L r fl d1 = evalMemSteps mem₀ nodesBase h L r fl d1)
    (hown_eq : ((nodeOwnRawStep mem₉ nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList =
      (((nodeOwnRawStep mem₀ nodesBase h L x).map (fun s => s.addDeltaMod h L 0)).toList).map
        (fun q => q.addDelta d))
    (h8_zero : nodeField mem₇ nodesBase l.rootId OFF_MIN1_HAS +
        nodeField mem₇ nodesBase r.rootId OFF_MIN1_HAS = 0 →
      (∀ off < NODE_STRIDE, mem₈ (nodesBase + NODE_STRIDE * x + off) =
        mem₇ (nodesBase + NODE_STRIDE * x + off)) ∧ hp₈ = hp₇)
    (h8_nz : nodeField mem₇ nodesBase l.rootId OFF_MIN1_HAS +
        nodeField mem₇ nodesBase r.rootId OFF_MIN1_HAS ≠ 0 →
      nodeField mem₈ nodesBase x OFF_HAS_TAG = 1 ∧
      NumPtrOk mem₈ (nodesBase + NODE_STRIDE * (cap + 1)) hp₈ h L
        (nodeField mem₈ nodesBase x OFF_TAG_PTR) ∧
      nodeField mem₈ nodesBase x OFF_TAG_NEG =
        (if mem₇ (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) = 0 then tNeg
         else mem₇ (nodesBase + NODE_STRIDE * x + OFF_TAG_NEG)) ∧
      (mem₇ (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) = 0 →
        nodeField mem₈ nodesBase x OFF_TAG_PTR = tPtr) ∧
      (mem₇ (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) ≠ 0 →
        intVal mem₈ (nodeField mem₈ nodesBase x OFF_TAG_PTR) h L =
          wrap h L (if mem₇ (nodesBase + NODE_STRIDE * x + OFF_TAG_NEG) = tNeg
            then intVal mem₇ (mem₇ (nodesBase + NODE_STRIDE * x + OFF_TAG_PTR)) h L +
              intVal mem₇ tPtr h L
            else intVal mem₇ (mem₇ (nodesBase + NODE_STRIDE * x + OFF_TAG_PTR)) h L -
              intVal mem₇ tPtr h L)))
    (hmem9_rev : mem₉ (nodesBase + NODE_STRIDE * x + OFF_REV) =
      mem₀ (nodesBase + NODE_STRIDE * x + OFF_REV)) :
    (nodeField mem₉ nodesBase x OFF_HAS_TAG = 1 →
      NumPtrOk mem₉ (nodesBase + NODE_STRIDE * (cap + 1)) hp₈ h L
        (nodeField mem₉ nodesBase x OFF_TAG_PTR) ∧
      ((l ≠ .leaf ∧ nodeField mem₉ nodesBase l.rootId OFF_MIN1_HAS = 1) ∨
       (r ≠ .leaf ∧ nodeField mem₉ nodesBase r.rootId OFF_MIN1_HAS = 1)) ∧
      ∃ d' : ℤ, d' % (capacity h L : ℤ) = nodeTagInt mem₉ nodesBase h L x % (capacity h L : ℤ) ∧
        StepsShiftFit h L
          (evalMemSteps mem₉ nodesBase h L l (revFlag mem₉ nodesBase x) 0 ++
           evalMemSteps mem₉ nodesBase h L r (revFlag mem₉ nodesBase x) 0) d') ∧
    (nodeField mem₉ nodesBase x OFF_HAS_TAG = 0 →
      nodeField mem₉ nodesBase x OFF_TAG_PTR = 0 ∧
      nodeField mem₉ nodesBase x OFF_TAG_NEG = 0) ∧
    evalMemSteps mem₉ nodesBase h L (.node x l r) false 0 =
      (evalMemSteps mem₀ nodesBase h L (.node x l r) false 0).map (fun q => q.addDelta d) := by
  let ptr := nodesBase + NODE_STRIDE * x
  let arenaHi := nodesBase + NODE_STRIDE * (cap + 1)
  let rv := revFlag mem₀ nodesBase x
  have hm9_ge : ∀ a, nodesBase ≤ a → mem₉ a = mem₈ a := fun a ha => hm9_ne a (by omega)
  have hnf9 : ∀ u off, nodeField mem₉ nodesBase u off = nodeField mem₈ nodesBase u off :=
    fun u off => hm9_ge _ (by omega)
  have hrv_eq : revFlag mem₉ nodesBase x = rv := by
    simp only [rv, revFlag]
    rw [show nodeField mem₉ nodesBase x OFF_REV = nodeField mem₀ nodesBase x OFF_REV from hmem9_rev]
  have hch_m1_eq_l : nodeField mem₇ nodesBase l.rootId OFF_MIN1_HAS =
      nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS := by
    cases l with
    | leaf => simp [AuxTree.rootId, nodeField, h0_m1_7, h0 OFF_MIN1_HAS (by decide)]
    | node lx _ _ =>
        exact hmem7_node_le lx hl_m.2.1 (fun h => hx_l (h ▸ by simp [AuxTree.toList])) OFF_MIN1_HAS (by decide)
  have hch_m1_eq_r : nodeField mem₇ nodesBase r.rootId OFF_MIN1_HAS =
      nodeField mem₀ nodesBase r.rootId OFF_MIN1_HAS := by
    cases r with
    | leaf => simp [AuxTree.rootId, nodeField, h0_m1_7, h0 OFF_MIN1_HAS (by decide)]
    | node rx _ _ =>
        exact hmem7_node_le rx hr_m.2.1 (fun h => hx_r (h ▸ by simp [AuxTree.toList])) OFF_MIN1_HAS (by decide)
  by_cases hcz : nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS +
      nodeField mem₀ nodesBase r.rootId OFF_MIN1_HAS = 0
  · have hcz7 : nodeField mem₇ nodesBase l.rootId OFF_MIN1_HAS +
        nodeField mem₇ nodesBase r.rootId OFF_MIN1_HAS = 0 := by rw [hch_m1_eq_l, hch_m1_eq_r]; exact hcz
    rcases h8_zero hcz7 with ⟨hm87, _⟩
    have hl0 : l = .leaf ∨ nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS = 0 := by
      cases l with | leaf => exact Or.inl rfl | node _ _ _ => exact Or.inr (by omega)
    have hr0 : r = .leaf ∨ nodeField mem₀ nodesBase r.rootId OFF_MIN1_HAS = 0 := by
      cases r with | leaf => exact Or.inl rfl | node _ _ _ => exact Or.inr (by omega)
    have hht0 : nodeField mem₀ nodesBase x OFF_HAS_TAG = 0 := by
      by_contra hne
      have hht1 : nodeField mem₀ nodesBase x OFF_HAS_TAG = 1 := by omega
      (rcases (htag1 hht1).2.1 with ⟨hlne, hlm⟩ | ⟨hrne, hrm⟩ <;>
        [rcases hl0 with rfl | h0'; rcases hr0 with rfl | h0']) <;>
        first | contradiction | omega
    rcases htag0 hht0 with ⟨hpt0, htn0⟩
    have hht9 : nodeField mem₉ nodesBase x OFF_HAS_TAG = 0 := by
      rw [hnf9]; dsimp only [nodeField]
      rw [hm87 OFF_HAS_TAG (by decide),
        hmem7_oth_x OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hht0
    have hpt9 : nodeField mem₉ nodesBase x OFF_TAG_PTR = 0 := by
      rw [hnf9]; dsimp only [nodeField]
      rw [hm87 OFF_TAG_PTR (by decide),
        hmem7_oth_x OFF_TAG_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hpt0
    have htn9 : nodeField mem₉ nodesBase x OFF_TAG_NEG = 0 := by
      rw [hnf9]; dsimp only [nodeField]
      rw [hm87 OFF_TAG_NEG (by decide),
        hmem7_oth_x OFF_TAG_NEG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact htn0
    refine ⟨fun h1 => by rw [hht9] at h1; omega, fun _ => ⟨hpt9, htn9⟩, ?_⟩
    have hl_nil := treeMemMatch_child_steps_nil hl_m hl0
    have hr_nil := treeMemMatch_child_steps_nil hr_m hr0
    simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.false_xor,
      hl_steps_eq, hr_steps_eq, hl_nil, hr_nil, List.nil_append, List.append_nil, hown_eq]
  · have hcnz7 : nodeField mem₇ nodesBase l.rootId OFF_MIN1_HAS +
        nodeField mem₇ nodesBase r.rootId OFF_MIN1_HAS ≠ 0 := by rw [hch_m1_eq_l, hch_m1_eq_r]; exact hcz
    rcases h8_nz hcnz7 with ⟨hht8, hpt8_ok, htn8, hpt8_0, hpt8_1⟩
    have hch9 : (l ≠ .leaf ∧ nodeField mem₉ nodesBase l.rootId OFF_MIN1_HAS = 1) ∨
        (r ≠ .leaf ∧ nodeField mem₉ nodesBase r.rootId OFF_MIN1_HAS = 1) := by
      have hl_le : nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS ≤ 1 :=
        treeMemMatch_min1Has_le hl_m (h0 OFF_MIN1_HAS (by decide))
      have hr_le : nodeField mem₀ nodesBase r.rootId OFF_MIN1_HAS ≤ 1 :=
        treeMemMatch_min1Has_le hr_m (h0 OFF_MIN1_HAS (by decide))
      by_cases hlz : nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS = 0
      · right
        have hr1 : nodeField mem₀ nodesBase r.rootId OFF_MIN1_HAS = 1 := by omega
        have hrne : r ≠ .leaf := fun h => by
          subst h; simp [AuxTree.rootId, nodeField, h0 OFF_MIN1_HAS (by decide)] at hr1
        cases r with
        | leaf => exact (hrne rfl).elim
        | node rx _ _ =>
            refine ⟨hrne, ?_⟩
            dsimp only [AuxTree.rootId] at hr1 ⊢
            rw [hmem9_node_ne rx hr_m.2.1 (fun h => hx_r (h ▸ by simp [AuxTree.toList])) OFF_MIN1_HAS (by decide)]
            exact hr1
      · left
        have hl1 : nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS = 1 := by omega
        have hlne : l ≠ .leaf := fun h => by
          subst h; simp [AuxTree.rootId, nodeField, h0 OFF_MIN1_HAS (by decide)] at hl1
        cases l with
        | leaf => exact (hlne rfl).elim
        | node lx _ _ =>
            refine ⟨hlne, ?_⟩
            dsimp only [AuxTree.rootId] at hl1 ⊢
            rw [hmem9_node_ne lx hl_m.2.1 (fun h => hx_l (h ▸ by simp [AuxTree.toList])) OFF_MIN1_HAS (by decide)]
            exact hl1
    have hht9 : nodeField mem₉ nodesBase x OFF_HAS_TAG = 1 := by rw [hnf9]; exact hht8
    have hpt9_ok : NumPtrOk mem₉ arenaHi hp₈ h L (nodeField mem₉ nodesBase x OFF_TAG_PTR) := by
      rw [hnf9]
      rcases hpt8_ok with ⟨o1, olo, ohi, oval⟩
      exact ⟨o1, olo, ohi, fun i hi => by rw [hm9_ge _ (by omega)]; exact oval i hi⟩
    have ht_ag9 : intVal mem₉ tPtr h L = intVal mem₀ tPtr h L :=
      intVal_agree_heap hheap9 htPtr.2.1 htPtr.2.2.1
    have ht7_ag : intVal mem₇ tPtr h L = intVal mem₀ tPtr h L :=
      intVal_agree_heap nhs567.2.2.2 htPtr.2.1 htPtr.2.2.1
    by_cases hht0 : mem₀ (ptr + OFF_HAS_TAG) = 0
    · have hht70 : mem₇ (ptr + OFF_HAS_TAG) = 0 := by
        rw [hmem7_oth_x OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hht0
      have htag_int0 : nodeTagInt mem₀ nodesBase h L x = 0 := by simp [nodeTagInt, nodeField, ptr, hht0]
      have hpt9_eq : nodeField mem₉ nodesBase x OFF_TAG_PTR = tPtr := by
        rw [hnf9]; exact hpt8_0 hht70
      have htn9_eq : nodeField mem₉ nodesBase x OFF_TAG_NEG = tNeg := by
        dsimp only [ptr] at hht70
        simp only [hnf9, htn8, hht70, ↓reduceIte]
      have hd_mod9 : d % (capacity h L : ℤ) = nodeTagInt mem₉ nodesBase h L x % (capacity h L : ℤ) := by
        simp only [nodeTagInt, hht9, Nat.one_ne_zero, ↓reduceIte, htn9_eq, optIntVal, hpt9_eq]
        rw [ite_eq_right htPtr.1, ht_ag9]
        exact hdmod
      have hfit_ch : StepsShiftFit h L
          (evalMemSteps mem₉ nodesBase h L l rv 0 ++ evalMemSteps mem₉ nodesBase h L r rv 0) d := by
        rw [hl_steps_eq, hr_steps_eq]
        intro s₀ hs₀
        apply hfit
        simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.false_xor, zero_add,
          htag_int0, List.mem_append] at hs₀ ⊢
        rcases hs₀ with hs₀ | hs₀
        · exact Or.inl (Or.inl hs₀)
        · exact Or.inr hs₀
      refine ⟨fun _ => ⟨hpt9_ok, hch9, d, hd_mod9, by simpa [rv, hrv_eq] using hfit_ch⟩,
        fun h0' => by rw [hht9] at h0'; omega, ?_⟩
      have hl_map : evalMemSteps mem₉ nodesBase h L l rv (0 + nodeTagInt mem₉ nodesBase h L x) =
          (evalMemSteps mem₀ nodesBase h L l rv (0 + nodeTagInt mem₀ nodesBase h L x)).map
            (fun q => q.addDelta d) := by
        rw [hl_steps_eq, htag_int0, zero_add, zero_add, ← add_zero (nodeTagInt mem₉ nodesBase h L x),
          evalMemSteps_addDeltaMod hl_m rv _ 0]
        exact stepsShiftFit_map_addDeltaMod_eq
          (fun q hq => hfit_ch q (by rw [hl_steps_eq]; exact List.mem_append_left _ hq)) hd_mod9.symm
      have hr_map : evalMemSteps mem₉ nodesBase h L r rv (0 + nodeTagInt mem₉ nodesBase h L x) =
          (evalMemSteps mem₀ nodesBase h L r rv (0 + nodeTagInt mem₀ nodesBase h L x)).map
            (fun q => q.addDelta d) := by
        rw [hr_steps_eq, htag_int0, zero_add, zero_add, ← add_zero (nodeTagInt mem₉ nodesBase h L x),
          evalMemSteps_addDeltaMod hr_m rv _ 0]
        exact stepsShiftFit_map_addDeltaMod_eq
          (fun q hq => hfit_ch q (by rw [hr_steps_eq]; exact List.mem_append_right _ hq)) hd_mod9.symm
      simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.false_xor, List.map_append, hrv_eq]
      rw [hl_map, hown_eq, hr_map]
    · have hht1 : nodeField mem₀ nodesBase x OFF_HAS_TAG = 1 := by dsimp [nodeField, ptr] at hht hht0 ⊢; omega
      have hht71 : mem₇ (ptr + OFF_HAS_TAG) = 1 := by
        rw [hmem7_oth_x OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hht1
      rcases htag1 hht1 with ⟨pt₀, _, d₀, hd₀_mod, hfit₀⟩
      have htn7_eq : mem₇ (ptr + OFF_TAG_NEG) = mem₀ (ptr + OFF_TAG_NEG) :=
        hmem7_oth_x OFF_TAG_NEG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have htp7_eq : mem₇ (ptr + OFF_TAG_PTR) = mem₀ (ptr + OFF_TAG_PTR) :=
        hmem7_oth_x OFF_TAG_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have htp7_ag : intVal mem₇ (mem₀ (ptr + OFF_TAG_PTR)) h L =
          intVal mem₀ (mem₀ (ptr + OFF_TAG_PTR)) h L :=
        intVal_agree_heap nhs567.2.2.2 pt₀.2.1 pt₀.2.2.1
      have htp9_val : intVal mem₉ (nodeField mem₉ nodesBase x OFF_TAG_PTR) h L =
          wrap h L (if mem₀ (ptr + OFF_TAG_NEG) = tNeg
            then intVal mem₀ (mem₀ (ptr + OFF_TAG_PTR)) h L + intVal mem₀ tPtr h L
            else intVal mem₀ (mem₀ (ptr + OFF_TAG_PTR)) h L - intVal mem₀ tPtr h L) := by
        rw [hnf9]
        rcases hpt8_ok with ⟨_, olo, ohi, _⟩
        rw [intVal_agree_heap (fun a ha1 ha2 => hm9_ge a (by omega)) olo ohi]
        rw [hpt8_1 (by dsimp only [ptr] at hht71; rw [hht71]; decide), htn7_eq, htp7_eq, htp7_ag, ht7_ag]
      have hht7nz : mem₇ (ptr + OFF_HAS_TAG) ≠ 0 := by rw [hht71]; decide
      have htn9_eq : nodeField mem₉ nodesBase x OFF_TAG_NEG = mem₀ (ptr + OFF_TAG_NEG) := by
        rw [hnf9, htn8, ite_eq_right hht7nz, htn7_eq]
      have hnt0_eq : nodeTagInt mem₀ nodesBase h L x =
          (if mem₀ (ptr + OFF_TAG_NEG) = 0 then intVal mem₀ (mem₀ (ptr + OFF_TAG_PTR)) h L
           else -intVal mem₀ (mem₀ (ptr + OFF_TAG_PTR)) h L) := by
        simp only [nodeTagInt, hht1, Nat.one_ne_zero, ↓reduceIte, optIntVal, ite_eq_right pt₀.1]
        rfl
      have hnt9_eq : nodeTagInt mem₉ nodesBase h L x =
          (if mem₀ (ptr + OFF_TAG_NEG) = 0 then intVal mem₉ (nodeField mem₉ nodesBase x OFF_TAG_PTR) h L
           else -intVal mem₉ (nodeField mem₉ nodesBase x OFF_TAG_PTR) h L) := by
        simp only [nodeTagInt, hht9, Nat.one_ne_zero, ↓reduceIte, htn9_eq, optIntVal, ite_eq_right hpt9_ok.1]
      have hd_mod9 : (d₀ + d) % (capacity h L : ℤ) = nodeTagInt mem₉ nodesBase h L x % (capacity h L : ℤ) := by
        rw [hnt9_eq, htp9_val]
        have hd₀' : d₀ % (capacity h L : ℤ) = nodeTagInt mem₀ nodesBase h L x % (capacity h L : ℤ) := hd₀_mod
        rw [hnt0_eq] at hd₀'
        have neg_emod_congr : ∀ a b : ℤ, a % (capacity h L : ℤ) = b % (capacity h L : ℤ) →
            (-a) % (capacity h L : ℤ) = (-b) % (capacity h L : ℤ) := fun a b hab => by
          simp only [Int.neg_emod, Int.dvd_iff_emod_eq_zero, hab]
        have wrap_neg_emod : ∀ z : ℤ, (-wrap h L z) % (capacity h L : ℤ) = (-z) % (capacity h L : ℤ) :=
          fun z => neg_emod_congr _ _ (wrap_emod h L z)
        have mod_add : ∀ {a₁ a₂ b₁ b₂ : ℤ},
            a₁ % (capacity h L : ℤ) = b₁ % (capacity h L : ℤ) →
            a₂ % (capacity h L : ℤ) = b₂ % (capacity h L : ℤ) →
            (a₁ + a₂) % (capacity h L : ℤ) = (b₁ + b₂) % (capacity h L : ℤ) := fun h1 h2 => by
          rw [Int.add_emod, h1, h2, ← Int.add_emod]
        have htn_le : mem₀ (ptr + OFF_TAG_NEG) ≤ 1 := htn
        by_cases htnz : mem₀ (ptr + OFF_TAG_NEG) = 0 <;> by_cases htneg0 : tNeg = 0
        · simp only [htnz, htneg0, ↓reduceIte] at hd₀' hdmod ⊢
          exact (mod_add hd₀' hdmod).trans (wrap_emod h L _).symm
        · have htneg1 : tNeg = 1 := by omega
          simp only [htnz, htneg1, ↓reduceIte, Nat.one_ne_zero] at hd₀' hdmod ⊢
          exact (mod_add hd₀' hdmod).trans (by rw [← sub_eq_add_neg]; exact (wrap_emod h L _).symm)
        · have htn1 : mem₀ (ptr + OFF_TAG_NEG) = 1 := by omega
          simp only [htn1, htneg0, ↓reduceIte, Nat.one_ne_zero] at hd₀' hdmod ⊢
          exact (mod_add hd₀' hdmod).trans (by
            rw [wrap_neg_emod,
              show -intVal mem₀ (mem₀ (ptr + OFF_TAG_PTR)) h L + intVal mem₀ tPtr h L =
                -(intVal mem₀ (mem₀ (ptr + OFF_TAG_PTR)) h L - intVal mem₀ tPtr h L) by ring])
        · have htn1 : mem₀ (ptr + OFF_TAG_NEG) = 1 := by omega
          have htneg1 : tNeg = 1 := by omega
          simp only [htn1, htneg1, ↓reduceIte, Nat.one_ne_zero] at hd₀' hdmod ⊢
          exact (mod_add hd₀' hdmod).trans (by
            rw [wrap_neg_emod,
              show -intVal mem₀ (mem₀ (ptr + OFF_TAG_PTR)) h L + -intVal mem₀ tPtr h L =
                -(intVal mem₀ (mem₀ (ptr + OFF_TAG_PTR)) h L + intVal mem₀ tPtr h L) by ring])
      have hl0_map : evalMemSteps mem₀ nodesBase h L l rv (0 + nodeTagInt mem₀ nodesBase h L x) =
          (evalMemSteps mem₀ nodesBase h L l rv 0).map (fun q => q.addDelta d₀) := by
        rw [zero_add, ← add_zero (nodeTagInt mem₀ nodesBase h L x), evalMemSteps_addDeltaMod hl_m rv _ 0]
        exact stepsShiftFit_map_addDeltaMod_eq
          (fun q hq => hfit₀ q (List.mem_append_left _ hq)) (by simpa [rv] using hd₀_mod.symm)
      have hr0_map : evalMemSteps mem₀ nodesBase h L r rv (0 + nodeTagInt mem₀ nodesBase h L x) =
          (evalMemSteps mem₀ nodesBase h L r rv 0).map (fun q => q.addDelta d₀) := by
        rw [zero_add, ← add_zero (nodeTagInt mem₀ nodesBase h L x), evalMemSteps_addDeltaMod hr_m rv _ 0]
        exact stepsShiftFit_map_addDeltaMod_eq
          (fun q hq => hfit₀ q (List.mem_append_right _ hq)) (by simpa [rv] using hd₀_mod.symm)
      have hfit_comp : StepsShiftFit h L
          ((evalMemSteps mem₀ nodesBase h L l rv 0 ++
            evalMemSteps mem₀ nodesBase h L r rv 0).map (fun q => q.addDelta d₀)) d := by
        intro q hq
        apply hfit
        rw [List.map_append, ← hl0_map, ← hr0_map, List.mem_append] at hq
        simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.false_xor, List.mem_append]
        rcases hq with hq | hq
        · exact Or.inl (Or.inl hq)
        · exact Or.inr hq
      have hfit_ch : StepsShiftFit h L
          (evalMemSteps mem₉ nodesBase h L l rv 0 ++ evalMemSteps mem₉ nodesBase h L r rv 0) (d₀ + d) := by
        rw [hl_steps_eq, hr_steps_eq]
        exact stepsShiftFit_compose (by simpa [rv] using hfit₀) hfit_comp
      refine ⟨fun _ => ⟨hpt9_ok, hch9, d₀ + d, hd_mod9, by simpa [rv, hrv_eq] using hfit_ch⟩,
        fun h0' => by rw [hht9] at h0'; omega, ?_⟩
      have hl_map : evalMemSteps mem₉ nodesBase h L l rv (0 + nodeTagInt mem₉ nodesBase h L x) =
          (evalMemSteps mem₀ nodesBase h L l rv (0 + nodeTagInt mem₀ nodesBase h L x)).map
            (fun q => q.addDelta d) := by
        rw [hl_steps_eq, zero_add, ← add_zero (nodeTagInt mem₉ nodesBase h L x),
          evalMemSteps_addDeltaMod hl_m rv _ 0]
        have hm1 := stepsShiftFit_map_addDeltaMod_eq
          (fun q hq => hfit_ch q (by rw [hl_steps_eq]; exact List.mem_append_left _ hq)) hd_mod9.symm
        rw [hm1, hl0_map, List.map_map]
        apply List.map_congr_left
        intro q _
        exact (addDelta_addDelta q d₀ d).symm
      have hr_map : evalMemSteps mem₉ nodesBase h L r rv (0 + nodeTagInt mem₉ nodesBase h L x) =
          (evalMemSteps mem₀ nodesBase h L r rv (0 + nodeTagInt mem₀ nodesBase h L x)).map
            (fun q => q.addDelta d) := by
        rw [hr_steps_eq, zero_add, ← add_zero (nodeTagInt mem₉ nodesBase h L x),
          evalMemSteps_addDeltaMod hr_m rv _ 0]
        have hm1 := stepsShiftFit_map_addDeltaMod_eq
          (fun q hq => hfit_ch q (by rw [hr_steps_eq]; exact List.mem_append_right _ hq)) hd_mod9.symm
        rw [hm1, hr0_map, List.map_map]
        apply List.map_congr_left
        intro q _
        exact (addDelta_addDelta q d₀ d).symm
      simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.false_xor, List.map_append, hrv_eq]
      rw [hl_map, hown_eq, hr_map]

theorem applyTagBody_post_min_vals {h L nodesBase cap x tPtr tNeg hp₅ hp₆ hp₇ hp₈ out_m1 out_m2 : ℕ}
    {l r : AuxTree} {mem₀ mem₅ mem₆ mem₇ mem₈ mem₉ : ℕ → ℕ} {d : ℤ}
    (hm9_ge : ∀ a, nodesBase ≤ a → mem₉ a = mem₈ a)
    (h5_m1_eq : mem₅ (nodesBase + NODE_STRIDE * x + OFF_MIN1_VAL) =
      mem₀ (nodesBase + NODE_STRIDE * x + OFF_MIN1_VAL))
    (hm2_6_eq : mem₆ (nodesBase + NODE_STRIDE * x + OFF_MIN2_VAL) =
      mem₀ (nodesBase + NODE_STRIDE * x + OFF_MIN2_VAL))
    (h7_lo : hp₆ ≤ hp₇) (h8_lo : hp₇ ≤ hp₈)
    (nhs5 : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) (mem₀ (nodesBase - 1)) hp₅ mem₀ mem₅)
    (nhs56 : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) (mem₀ (nodesBase - 1)) hp₆ mem₀ mem₆)
    (nhs7 : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) hp₆ hp₇ mem₆ mem₇)
    (nhs8 : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) hp₇ hp₈ mem₇ mem₈)
    (hout_m1_ok : NumPtrOk mem₆ (nodesBase + NODE_STRIDE * (cap + 1)) hp₆ h L out_m1)
    (hout_m2_ok : NumPtrOk mem₇ (nodesBase + NODE_STRIDE * (cap + 1)) hp₇ h L out_m2)
    (hint6 : intVal mem₆ out_m1 h L = wrap h L
      (if tNeg = 0 then intVal mem₅ (mem₅ (nodesBase + NODE_STRIDE * x + OFF_MIN1_VAL)) h L - intVal mem₅ tPtr h L
       else intVal mem₅ (mem₅ (nodesBase + NODE_STRIDE * x + OFF_MIN1_VAL)) h L + intVal mem₅ tPtr h L))
    (hint7 : intVal mem₇ out_m2 h L = wrap h L
      (if 1 - tNeg = 0 then intVal mem₆ (mem₆ (nodesBase + NODE_STRIDE * x + OFF_MIN2_VAL)) h L - intVal mem₆ tPtr h L
       else intVal mem₆ (mem₆ (nodesBase + NODE_STRIDE * x + OFF_MIN2_VAL)) h L + intVal mem₆ tPtr h L))
    (htNeg : tNeg ≤ 1)
    (htPtr : NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L tPtr)
    (hm1_one : nodeField mem₀ nodesBase x OFF_MIN1_HAS = 1)
    (hm2h : nodeField mem₀ nodesBase x OFF_MIN2_HAS = nodeField mem₀ nodesBase x OFF_MIN1_HAS)
    (pm1 : NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L
      (mem₀ (nodesBase + NODE_STRIDE * x + OFF_MIN1_VAL)))
    (pm2 : NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L
      (mem₀ (nodesBase + NODE_STRIDE * x + OFF_MIN2_VAL)))
    (hdmod : d % (capacity h L : ℤ) =
      (if tNeg = 0 then intVal mem₀ tPtr h L else -intVal mem₀ tPtr h L) % (capacity h L : ℤ))
    (hagg1 : nodeIntMinAgg1 mem₀ nodesBase h L x =
      listIntMinAgg ((evalMemSteps mem₀ nodesBase h L (.node x l r) false 0).map fun s => (s.nodeId, s.dirAvail)))
    (hagg2 : nodeIntMinAgg2 mem₀ nodesBase h L x =
      listIntMinAgg ((evalMemSteps mem₀ nodesBase h L (.node x l r) false 0).map fun s => (s.nodeId, s.flip.dirAvail)))
    (hfit : StepsShiftFit h L (evalMemSteps mem₀ nodesBase h L (.node x l r) false 0) d) :
    intVal mem₉ out_m1 h L = intVal mem₀ (mem₀ (nodesBase + NODE_STRIDE * x + OFF_MIN1_VAL)) h L - d ∧
    intVal mem₉ out_m2 h L = intVal mem₀ (mem₀ (nodesBase + NODE_STRIDE * x + OFF_MIN2_VAL)) h L + d := by
  let ptr := nodesBase + NODE_STRIDE * x
  let arenaHi := nodesBase + NODE_STRIDE * (cap + 1)
  let steps := evalMemSteps mem₀ nodesBase h L (.node x l r) false 0
  have hm1_val9 : intVal mem₉ out_m1 h L = intVal mem₀ (mem₀ (ptr + OFF_MIN1_VAL)) h L - d := by
    have hagr : intVal mem₉ out_m1 h L = intVal mem₆ out_m1 h L := by
      rw [intVal_agree_heap (fun a ha1 ha2 => hm9_ge a (by omega))
        hout_m1_ok.2.1 (le_trans hout_m1_ok.2.2.1 (le_trans h7_lo h8_lo))]
      exact intVal_agree_heap
        (fun a ha1 ha2 => (nhs8.2.2.2 a ha1 (lt_of_lt_of_le ha2 h7_lo)).trans (nhs7.2.2.2 a ha1 ha2))
        hout_m1_ok.2.1 hout_m1_ok.2.2.1
    rw [hagr, hint6, h5_m1_eq,
      intVal_agree_heap nhs5.2.2.2 pm1.2.1 pm1.2.2.1, intVal_agree_heap nhs5.2.2.2 htPtr.2.1 htPtr.2.2.1]
    have hhas1 : (listIntMinAgg (steps.map fun s => (s.nodeId, s.dirAvail))).has = true := by
      rw [← hagg1]; simp [nodeIntMinAgg1, hm1_one]
    rcases listIntMinAgg_mem hhas1 with ⟨p₁, hp₁, hvp₁⟩
    rw [List.mem_map] at hp₁
    rcases hp₁ with ⟨s₁, hs₁, rfl⟩
    have heqv : (listIntMinAgg (steps.map fun s => (s.nodeId, s.dirAvail))).val =
        intVal mem₀ (mem₀ (ptr + OFF_MIN1_VAL)) h L := by
      rw [← hagg1]; simp [nodeIntMinAgg1, nodeField, optIntVal, ptr, pm1.1]
    have hfit₁ : Fits h L (intVal mem₀ (mem₀ (ptr + OFF_MIN1_VAL)) h L - d) := by
      rw [← heqv, hvp₁]
      rcases hfit s₁ hs₁ with ⟨_, _, _, _, hafd, habd⟩
      cases hf : s₁.fwd <;> simp only [RawStep.dirAvail, hf, Bool.false_eq_true, ↓reduceIte] at hafd habd ⊢ <;> assumption
    have hmod_sub : ((if tNeg = 0 then intVal mem₀ (mem₀ (ptr + OFF_MIN1_VAL)) h L - intVal mem₀ tPtr h L
        else intVal mem₀ (mem₀ (ptr + OFF_MIN1_VAL)) h L + intVal mem₀ tPtr h L) : ℤ) % (capacity h L : ℤ) =
        (intVal mem₀ (mem₀ (ptr + OFF_MIN1_VAL)) h L - d) % (capacity h L : ℤ) := by
      by_cases ht0 : tNeg = 0
      · simp only [ht0, ↓reduceIte] at hdmod ⊢
        rw [Int.sub_emod, ← hdmod, ← Int.sub_emod]
      · simp only [ht0, ↓reduceIte] at hdmod ⊢
        rw [show intVal mem₀ (mem₀ (ptr + OFF_MIN1_VAL)) h L + intVal mem₀ tPtr h L =
          intVal mem₀ (mem₀ (ptr + OFF_MIN1_VAL)) h L - (-intVal mem₀ tPtr h L) by ring]
        rw [Int.sub_emod, ← hdmod, ← Int.sub_emod]
    rw [wrap_congr hmod_sub, wrap_of_fits hfit₁]
  have hm2_val9 : intVal mem₉ out_m2 h L = intVal mem₀ (mem₀ (ptr + OFF_MIN2_VAL)) h L + d := by
    have hagr : intVal mem₉ out_m2 h L = intVal mem₇ out_m2 h L := by
      rw [intVal_agree_heap (fun a ha1 ha2 => hm9_ge a (by omega))
        hout_m2_ok.2.1 (le_trans hout_m2_ok.2.2.1 h8_lo)]
      exact intVal_agree_heap nhs8.2.2.2 hout_m2_ok.2.1 hout_m2_ok.2.2.1
    rw [hagr, hint7, hm2_6_eq,
      intVal_agree_heap nhs56.2.2.2 pm2.2.1 pm2.2.2.1, intVal_agree_heap nhs56.2.2.2 htPtr.2.1 htPtr.2.2.1]
    have hhas2 : (listIntMinAgg (steps.map fun s => (s.nodeId, s.flip.dirAvail))).has = true := by
      rw [← hagg2]; simp [nodeIntMinAgg2, hm2h, hm1_one]
    rcases listIntMinAgg_mem hhas2 with ⟨p₂, hp₂, hvp₂⟩
    rw [List.mem_map] at hp₂
    rcases hp₂ with ⟨s₂, hs₂, rfl⟩
    have heqv : (listIntMinAgg (steps.map fun s => (s.nodeId, s.flip.dirAvail))).val =
        intVal mem₀ (mem₀ (ptr + OFF_MIN2_VAL)) h L := by
      rw [← hagg2]; simp [nodeIntMinAgg2, nodeField, optIntVal, ptr, pm2.1]
    have hfit₂ : Fits h L (intVal mem₀ (mem₀ (ptr + OFF_MIN2_VAL)) h L + d) := by
      rw [← heqv, hvp₂]
      rcases hfit s₂ hs₂ with ⟨_, _, _, _, hafd, habd⟩
      cases hf : s₂.fwd <;> simp only [RawStep.flip, RawStep.dirAvail, hf, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ↓reduceIte] at hafd habd ⊢ <;> assumption
    have hmod_add : ((if (1 - tNeg) = 0 then intVal mem₀ (mem₀ (ptr + OFF_MIN2_VAL)) h L - intVal mem₀ tPtr h L
        else intVal mem₀ (mem₀ (ptr + OFF_MIN2_VAL)) h L + intVal mem₀ tPtr h L) : ℤ) % (capacity h L : ℤ) =
        (intVal mem₀ (mem₀ (ptr + OFF_MIN2_VAL)) h L + d) % (capacity h L : ℤ) := by
      by_cases ht0 : tNeg = 0
      · simp only [ht0, ↓reduceIte, tsub_zero, Nat.one_ne_zero] at hdmod ⊢
        rw [Int.add_emod, ← hdmod, ← Int.add_emod]
      · have ht1 : tNeg = 1 := by omega
        simp only [ht1, tsub_self, ↓reduceIte, Nat.one_ne_zero] at hdmod ⊢
        rw [sub_eq_add_neg, Int.add_emod, ← hdmod, ← Int.add_emod]
    rw [wrap_congr hmod_add, wrap_of_fits hfit₂]
  exact ⟨hm1_val9, hm2_val9⟩

theorem applyTagBody_post_treeMemMatch {w h L nodesBase cap parId pp x tPtr tNeg hp₅ hp₆ hp₇ hp₈ out_m1 out_m2 : ℕ}
    {l r : AuxTree} {mem₀ mem₅ mem₆ mem₇ mem₈ mem₉ : ℕ → ℕ} {d : ℤ}
    (hnb : 3 ≤ nodesBase)
    (h0 : SlotZeroOk mem₀ nodesBase)
    (htx : TreeMemMatch w h L mem₀ nodesBase cap (.node x l r) parId pp)
    (hx_l : x ∉ l.toList) (hx_r : x ∉ r.toList)
    (htNeg : tNeg ≤ 1)
    (h6_lo : hp₅ ≤ hp₆) (h7_lo : hp₆ ≤ hp₇) (h8_lo : hp₇ ≤ hp₈)
    (hm9_hp : mem₉ (nodesBase - 1) = hp₈)
    (hm9_ne : ∀ a, a ≠ nodesBase - 1 → mem₉ a = mem₈ a)
    (nhs5 : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) (mem₀ (nodesBase - 1)) hp₅ mem₀ mem₅)
    (nhs6 : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) hp₅ hp₆ mem₅ mem₆)
    (nhs7 : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) hp₆ hp₇ mem₆ mem₇)
    (nhs8 : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) hp₇ hp₈ mem₇ mem₈)
    (nhs5678 : NodeHeapStepMem (nodesBase + NODE_STRIDE * (cap + 1))
      (nodesBase + NODE_STRIDE * x) (mem₀ (nodesBase - 1)) hp₈ mem₀ mem₈)
    (hmem6_oth : ∀ off < NODE_STRIDE, off ≠ OFF_MIN1_VAL →
      mem₆ (nodesBase + NODE_STRIDE * x + off) = mem₅ (nodesBase + NODE_STRIDE * x + off))
    (hmem7_oth : ∀ off < NODE_STRIDE, off ≠ OFF_MIN2_VAL →
      mem₇ (nodesBase + NODE_STRIDE * x + off) = mem₆ (nodesBase + NODE_STRIDE * x + off))
    (hmem8_oth : ∀ off < NODE_STRIDE, off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
      mem₈ (nodesBase + NODE_STRIDE * x + off) = mem₇ (nodesBase + NODE_STRIDE * x + off))
    (hmem9_oth_x : ∀ off < NODE_STRIDE, off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
      off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL → off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR →
      off ≠ OFF_TAG_NEG →
      mem₉ (nodesBase + NODE_STRIDE * x + off) = mem₀ (nodesBase + NODE_STRIDE * x + off))
    (hmem7_oth_x : ∀ off < NODE_STRIDE, off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
      off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL →
      mem₇ (nodesBase + NODE_STRIDE * x + off) = mem₀ (nodesBase + NODE_STRIDE * x + off))
    (hmem9_node_ne : ∀ u ≤ cap, u ≠ x → ∀ off < NODE_STRIDE,
      nodeField mem₉ nodesBase u off = nodeField mem₀ nodesBase u off)
    (hmem7_node_le : ∀ u ≤ cap, u ≠ x → ∀ off < NODE_STRIDE,
      nodeField mem₇ nodesBase u off = nodeField mem₀ nodesBase u off)
    (h0_m1_7 : mem₇ (nodesBase + OFF_MIN1_HAS) = 0)
    (hheap9 : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nodesBase - 1) → mem₉ a = mem₀ a)
    (hhe5_zero : mem₀ (nodesBase + NODE_STRIDE * x + OFF_HASE) = 0 →
      ∀ off < NODE_STRIDE, mem₅ (nodesBase + NODE_STRIDE * x + off) = mem₀ (nodesBase + NODE_STRIDE * x + off))
    (hhe5_post : nodeField mem₀ nodesBase x OFF_HASE = 1 →
      ∃ s₀, nodeOwnRawStep mem₀ nodesBase h L x = some s₀ ∧
        NumPtrOk mem₅ (nodesBase + NODE_STRIDE * (cap + 1)) hp₅ h L
          (mem₅ (nodesBase + NODE_STRIDE * x + OFF_AF_PTR)) ∧
        NumPtrOk mem₅ (nodesBase + NODE_STRIDE * (cap + 1)) hp₅ h L
          (mem₅ (nodesBase + NODE_STRIDE * x + OFF_AB_PTR)) ∧
        NumPtrOk mem₅ (nodesBase + NODE_STRIDE * (cap + 1)) hp₅ h L
          (mem₅ (nodesBase + NODE_STRIDE * x + OFF_FLOW_PTR)) ∧
        nodeOwnRawStep mem₅ nodesBase h L x =
          some (s₀.addDeltaMod h L (if tNeg = 0 then intVal mem₀ tPtr h L else -intVal mem₀ tPtr h L)))
    (h8_zero : nodeField mem₇ nodesBase l.rootId OFF_MIN1_HAS +
        nodeField mem₇ nodesBase r.rootId OFF_MIN1_HAS = 0 →
      (∀ off < NODE_STRIDE, mem₈ (nodesBase + NODE_STRIDE * x + off) =
        mem₇ (nodesBase + NODE_STRIDE * x + off)) ∧ hp₈ = hp₇)
    (h8_nz : nodeField mem₇ nodesBase l.rootId OFF_MIN1_HAS +
        nodeField mem₇ nodesBase r.rootId OFF_MIN1_HAS ≠ 0 →
      nodeField mem₈ nodesBase x OFF_HAS_TAG = 1 ∧
      NumPtrOk mem₈ (nodesBase + NODE_STRIDE * (cap + 1)) hp₈ h L
        (nodeField mem₈ nodesBase x OFF_TAG_PTR) ∧
      nodeField mem₈ nodesBase x OFF_TAG_NEG =
        (if mem₇ (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) = 0 then tNeg
         else mem₇ (nodesBase + NODE_STRIDE * x + OFF_TAG_NEG)) ∧
      (mem₇ (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) = 0 →
        nodeField mem₈ nodesBase x OFF_TAG_PTR = tPtr) ∧
      (mem₇ (nodesBase + NODE_STRIDE * x + OFF_HAS_TAG) ≠ 0 →
        intVal mem₈ (nodeField mem₈ nodesBase x OFF_TAG_PTR) h L =
          wrap h L (if mem₇ (nodesBase + NODE_STRIDE * x + OFF_TAG_NEG) = tNeg
            then intVal mem₇ (mem₇ (nodesBase + NODE_STRIDE * x + OFF_TAG_PTR)) h L +
              intVal mem₇ tPtr h L
            else intVal mem₇ (mem₇ (nodesBase + NODE_STRIDE * x + OFF_TAG_PTR)) h L -
              intVal mem₇ tPtr h L)))
    (hm1_val_eq : mem₉ (nodesBase + NODE_STRIDE * x + OFF_MIN1_VAL) = out_m1)
    (hm2_val_eq : mem₉ (nodesBase + NODE_STRIDE * x + OFF_MIN2_VAL) = out_m2)
    (hout_m1_ok : NumPtrOk mem₆ (nodesBase + NODE_STRIDE * (cap + 1)) hp₆ h L out_m1)
    (hout_m2_ok : NumPtrOk mem₇ (nodesBase + NODE_STRIDE * (cap + 1)) hp₇ h L out_m2)
    (hm1_val9 : intVal mem₉ out_m1 h L = intVal mem₀ (mem₀ (nodesBase + NODE_STRIDE * x + OFF_MIN1_VAL)) h L - d)
    (hm2_val9 : intVal mem₉ out_m2 h L = intVal mem₀ (mem₀ (nodesBase + NODE_STRIDE * x + OFF_MIN2_VAL)) h L + d)
    (hm1_one : nodeField mem₀ nodesBase x OFF_MIN1_HAS = 1)
    (hl_m' : TreeMemMatch w h L mem₉ nodesBase cap l x 0)
    (hr_m' : TreeMemMatch w h L mem₉ nodesBase cap r x 0)
    (htag_and_steps :
      (nodeField mem₉ nodesBase x OFF_HAS_TAG = 1 →
        NumPtrOk mem₉ (nodesBase + NODE_STRIDE * (cap + 1)) hp₈ h L
          (nodeField mem₉ nodesBase x OFF_TAG_PTR) ∧
        ((l ≠ .leaf ∧ nodeField mem₉ nodesBase l.rootId OFF_MIN1_HAS = 1) ∨
         (r ≠ .leaf ∧ nodeField mem₉ nodesBase r.rootId OFF_MIN1_HAS = 1)) ∧
        ∃ d' : ℤ, d' % (capacity h L : ℤ) = nodeTagInt mem₉ nodesBase h L x % (capacity h L : ℤ) ∧
          StepsShiftFit h L
            (evalMemSteps mem₉ nodesBase h L l (revFlag mem₉ nodesBase x) 0 ++
             evalMemSteps mem₉ nodesBase h L r (revFlag mem₉ nodesBase x) 0) d') ∧
      (nodeField mem₉ nodesBase x OFF_HAS_TAG = 0 →
        nodeField mem₉ nodesBase x OFF_TAG_PTR = 0 ∧
        nodeField mem₉ nodesBase x OFF_TAG_NEG = 0) ∧
      evalMemSteps mem₉ nodesBase h L (.node x l r) false 0 =
        (evalMemSteps mem₀ nodesBase h L (.node x l r) false 0).map (fun q => q.addDelta d)) :
    TreeMemMatch w h L mem₉ nodesBase cap (.node x l r) parId pp ∧
    (∀ u ≤ cap, ∀ off < NODE_STRIDE,
      off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
      off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL →
      off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
      nodeField mem₉ nodesBase u off = nodeField mem₀ nodesBase u off) ∧
    (∀ addr, addr < nodesBase + NODE_STRIDE * (AuxTree.node x l r).rootId ∨
        nodesBase + NODE_STRIDE * (AuxTree.node x l r).rootId + NODE_STRIDE ≤ addr →
      addr ≠ nodesBase - 1 → addr < mem₀ (nodesBase - 1) →
      mem₉ addr = mem₀ addr) := by
  let ptr := nodesBase + NODE_STRIDE * x
  let arenaHi := nodesBase + NODE_STRIDE * (cap + 1)
  let steps := evalMemSteps mem₀ nodesBase h L (.node x l r) false 0
  have hm9_ge : ∀ a, nodesBase ≤ a → mem₉ a = mem₈ a := fun a ha => hm9_ne a (by omega)
  have hnf9 : ∀ u off, nodeField mem₉ nodesBase u off = nodeField mem₈ nodesBase u off :=
    fun u off => hm9_ge _ (by omega)
  have hm1_ok9 : NumPtrOk mem₉ arenaHi hp₈ h L out_m1 := by
    have h68 : hp₆ ≤ hp₈ := le_trans h7_lo h8_lo
    have := numPtrOk_congr h68
      (fun a ha1 ha2 => (nhs8.2.2.2 a ha1 (lt_of_lt_of_le ha2 h7_lo)).trans (nhs7.2.2.2 a ha1 ha2))
      hout_m1_ok
    rcases this with ⟨o1, olo, ohi, oval⟩
    exact ⟨o1, olo, ohi, fun i hi => by rw [hm9_ge _ (by omega)]; exact oval i hi⟩
  have hm2_ok9 : NumPtrOk mem₉ arenaHi hp₈ h L out_m2 := by
    have := numPtrOk_congr h8_lo (fun a ha1 ha2 => nhs8.2.2.2 a ha1 ha2) hout_m2_ok
    rcases this with ⟨o1, olo, ohi, oval⟩
    exact ⟨o1, olo, ohi, fun i hi => by rw [hm9_ge _ (by omega)]; exact oval i hi⟩
  have htx' := htx
  rcases htx with ⟨hx1, hx2, hL, hR, hP, hPP, hrev, hiv, hhe, hsum, hdir, hht, htn,
    heu, hev, heid, he1, he0, hcf, hcb, _, _, hm1h, hm2h, hm1_1, _,
    hagg, hl_m, hr_m⟩
  rcases hm1_1 hm1_one with ⟨pm1, pm2, hm1_f, hm1_l, hm2_f, hm2_l⟩
  have hch_m1_eq_l : nodeField mem₇ nodesBase l.rootId OFF_MIN1_HAS =
      nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS := by
    cases l with
    | leaf => simp [AuxTree.rootId, nodeField, h0_m1_7, h0 OFF_MIN1_HAS (by decide)]
    | node lx _ _ =>
        exact hmem7_node_le lx hl_m.2.1 (fun h => hx_l (h ▸ by simp [AuxTree.toList])) OFF_MIN1_HAS (by decide)
  have hch_m1_eq_r : nodeField mem₇ nodesBase r.rootId OFF_MIN1_HAS =
      nodeField mem₀ nodesBase r.rootId OFF_MIN1_HAS := by
    cases r with
    | leaf => simp [AuxTree.rootId, nodeField, h0_m1_7, h0 OFF_MIN1_HAS (by decide)]
    | node rx _ _ =>
        exact hmem7_node_le rx hr_m.2.1 (fun h => hx_r (h ▸ by simp [AuxTree.toList])) OFF_MIN1_HAS (by decide)
  let hnf9_oth_x : ∀ off < NODE_STRIDE, off ≠ OFF_AF_PTR → off ≠ OFF_AB_PTR → off ≠ OFF_FLOW_PTR →
      off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL → off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR →
      off ≠ OFF_TAG_NEG →
      nodeField mem₉ nodesBase x off = nodeField mem₀ nodesBase x off := hmem9_oth_x
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [TreeMemMatch]
    rw [hm9_hp]
    refine ⟨hx1, hx2,
      by rw [hnf9_oth_x OFF_LEFT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hL,
      by rw [hnf9_oth_x OFF_RIGHT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hR,
      by rw [hnf9_oth_x OFF_PARENT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hP,
      by rw [hnf9_oth_x OFF_PPAR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hPP,
      by rw [hnf9_oth_x OFF_REV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hrev,
      by rw [hnf9_oth_x OFF_ISV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hiv,
      by rw [hnf9_oth_x OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hhe,
      by rw [hnf9_oth_x OFF_ISV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hnf9_oth_x OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hsum,
      by rw [hnf9_oth_x OFF_DIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hdir,
      ?_, ?_,
      by rw [hnf9_oth_x OFF_EU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact heu,
      by rw [hnf9_oth_x OFF_EV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hev,
      by rw [hnf9_oth_x OFF_EID (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact heid,
      ?_, ?_,
      by rw [hnf9_oth_x OFF_CSUM_FWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
         exact optNumPtrOk_congr nhs5678.1 hheap9 hcf,
      by rw [hnf9_oth_x OFF_CSUM_BWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
         exact optNumPtrOk_congr nhs5678.1 hheap9 hcb,
      htag_and_steps.1, htag_and_steps.2.1,
      by rw [hnf9_oth_x OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm1h,
      by rw [hnf9_oth_x OFF_MIN2_HAS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hnf9_oth_x OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm2h,
      ?_, ?_, ?_, hl_m', hr_m'⟩
    · by_cases hcz : nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS + nodeField mem₀ nodesBase r.rootId OFF_MIN1_HAS = 0
      · have hcz7 : nodeField mem₇ nodesBase l.rootId OFF_MIN1_HAS +
            nodeField mem₇ nodesBase r.rootId OFF_MIN1_HAS = 0 := by rw [hch_m1_eq_l, hch_m1_eq_r]; exact hcz
        rw [hnf9]; dsimp only [nodeField]
        rw [(h8_zero hcz7).1 _ (by decide),
          hmem7_oth_x OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact hht
      · rw [hnf9, (h8_nz (by rw [hch_m1_eq_l, hch_m1_eq_r]; exact hcz)).1]
    · by_cases hcz : nodeField mem₀ nodesBase l.rootId OFF_MIN1_HAS + nodeField mem₀ nodesBase r.rootId OFF_MIN1_HAS = 0
      · have hcz7 : nodeField mem₇ nodesBase l.rootId OFF_MIN1_HAS +
            nodeField mem₇ nodesBase r.rootId OFF_MIN1_HAS = 0 := by rw [hch_m1_eq_l, hch_m1_eq_r]; exact hcz
        rw [hnf9]; dsimp only [nodeField]
        rw [(h8_zero hcz7).1 _ (by decide),
          hmem7_oth_x OFF_TAG_NEG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact htn
      · rw [hnf9, (h8_nz (by rw [hch_m1_eq_l, hch_m1_eq_r]; exact hcz)).2.2.1]
        split_ifs
        · exact htNeg
        · rw [hmem7_oth_x OFF_TAG_NEG (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact htn
    · intro hhe1
      rw [hnf9_oth_x OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at hhe1
      rcases hhe5_post hhe1 with ⟨_, _, haf5, hab5, hfl5, _⟩
      rcases he1 hhe1 with ⟨_, _, _, pcf, pcb, hcost_wrap⟩
      have hagr59 : ∀ a, arenaHi ≤ a → a < hp₅ → mem₉ a = mem₅ a := fun a ha1 ha2 => by
        rw [hm9_ge a (by omega)]
        exact (nhs8.2.2.2 a ha1 (by omega)).trans ((nhs7.2.2.2 a ha1 (by omega)).trans (nhs6.2.2.2 a ha1 ha2))
      have lift59 : ∀ p, NumPtrOk mem₅ arenaHi hp₅ h L p → NumPtrOk mem₉ arenaHi hp₈ h L p :=
        fun p hp => numPtrOk_congr (by omega) hagr59 hp
      have hfl_eq9 := (hm9_ge _ (by omega)).trans ((hmem8_oth OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide)).trans
        ((hmem7_oth OFF_FLOW_PTR (by decide) (by decide)).trans (hmem6_oth OFF_FLOW_PTR (by decide) (by decide))))
      have haf_eq9 := (hm9_ge _ (by omega)).trans ((hmem8_oth OFF_AF_PTR (by decide) (by decide) (by decide) (by decide)).trans
        ((hmem7_oth OFF_AF_PTR (by decide) (by decide)).trans (hmem6_oth OFF_AF_PTR (by decide) (by decide))))
      have hab_eq9 := (hm9_ge _ (by omega)).trans ((hmem8_oth OFF_AB_PTR (by decide) (by decide) (by decide) (by decide)).trans
        ((hmem7_oth OFF_AB_PTR (by decide) (by decide)).trans (hmem6_oth OFF_AB_PTR (by decide) (by decide))))
      have hcf_eq9 := hmem9_oth_x OFF_COST_FWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      have hcb_eq9 := hmem9_oth_x OFF_COST_BWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      refine ⟨by dsimp [nodeField]; rw [hfl_eq9]; exact lift59 _ hfl5,
        by dsimp [nodeField]; rw [haf_eq9]; exact lift59 _ haf5,
        by dsimp [nodeField]; rw [hab_eq9]; exact lift59 _ hab5,
        by dsimp [nodeField]; rw [hcf_eq9]; exact numPtrOk_congr nhs5678.1 hheap9 pcf,
        by dsimp [nodeField]; rw [hcb_eq9]; exact numPtrOk_congr nhs5678.1 hheap9 pcb,
        ?_⟩
      dsimp only [nodeField] at pcf pcb ⊢
      rw [hcb_eq9, hcf_eq9, intVal_agree_heap hheap9 pcb.2.1 pcb.2.2.1, intVal_agree_heap hheap9 pcf.2.1 pcf.2.2.1]
      exact hcost_wrap
    · intro hhe0
      rw [hnf9_oth_x OFF_HASE (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at hhe0
      rcases he0 hhe0 with ⟨hd0, hfl0, haf0, hab0, hcf0, hcb0⟩
      have h5_id := hhe5_zero hhe0
      have hsame0 : ∀ off < NODE_STRIDE, off ≠ OFF_MIN1_VAL → off ≠ OFF_MIN2_VAL →
          off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
          mem₉ (ptr + off) = mem₀ (ptr + off) := fun off hoff h1 h2 h3 h4 h5 => by
        rw [hm9_ge _ (by omega), hmem8_oth off hoff h3 h4 h5, hmem7_oth off hoff h2, hmem6_oth off hoff h1, h5_id off hoff]
      dsimp only [nodeField]
      rw [hsame0 OFF_DIR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hsame0 OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hsame0 OFF_AF_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hsame0 OFF_AB_PTR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hsame0 OFF_COST_FWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hsame0 OFF_COST_BWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact ⟨hd0, hfl0, haf0, hab0, hcf0, hcb0⟩
    · intro _
      dsimp only [nodeField]
      rw [hm1_val_eq, hm2_val_eq]
      exact ⟨hm1_ok9, hm2_ok9,
        by rw [hmem9_oth_x OFF_MIN1_FIRST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm1_f,
        by rw [hmem9_oth_x OFF_MIN1_LAST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm1_l,
        by rw [hmem9_oth_x OFF_MIN2_FIRST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm2_f,
        by rw [hmem9_oth_x OFF_MIN2_LAST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm2_l⟩
    · intro hm10
      rw [hnf9_oth_x OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] at hm10
      rw [hm1_one] at hm10; cases hm10
    · rw [htag_and_steps.2.2]
      rcases hagg with ⟨hvc, hsf, hsb, hmiff, hm1, hm2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hnf9_oth_x OFF_VCNT (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        have hev_eq : (AuxTree.node x l r).evalInorder (revFlag mem₉ nodesBase) false =
            (AuxTree.node x l r).evalInorder (revFlag mem₀ nodesBase) false := by
          apply evalInorder_agree_of_list
          intro u hu
          by_cases hux : u = x
          · subst hux; exact hnf9_oth_x OFF_REV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          · rw [hmem9_node_ne u (htx'.nodup_perm_mem hu).2 hux OFF_REV (by decide)]
        rw [hev_eq, hvc]
        apply listVcnt_agree_of_mem
        intro u hu
        have hum := ((AuxTree.node x l r).evalInorder_perm (revFlag mem₀ nodesBase) false).mem_iff.1 hu
        by_cases hux : u = x
        · subst hux; exact (hnf9_oth_x OFF_ISV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).symm
        · exact (hmem9_node_ne u (htx'.nodup_perm_mem hum).2 hux OFF_ISV (by decide)).symm
      · rw [hnf9_oth_x OFF_CSUM_FWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          optIntVal_agree_heap hheap9 hcf, hsf]
        congr 1
        simp [listRawCost, List.map_map, Function.comp_def, RawStep.signedCost_addDelta]
      · rw [hnf9_oth_x OFF_CSUM_BWD (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          optIntVal_agree_heap hheap9 hcb, hsb]
        congr 1; congr 1
        simp [listRawCost, List.map_map, Function.comp_def, RawStep.signedCost_addDelta]
      · rw [hnf9_oth_x OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [hmiff, List.map_eq_nil_iff]
      · dsimp only [nodeIntMinAgg1]
        have hm1_val_nf : nodeField mem₉ nodesBase x OFF_MIN1_VAL = out_m1 := hm1_val_eq
        rw [hnf9_oth_x OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hnf9_oth_x OFF_MIN1_FIRST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hnf9_oth_x OFF_MIN1_LAST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hm1_val_nf, show optIntVal mem₉ h L out_m1 = intVal mem₉ out_m1 h L by simp [optIntVal, hm1_ok9.1],
          hm1_val9]
        have hsh := listIntMinAgg_shift (steps.map fun s => (s.nodeId, s.dirAvail)) d
        dsimp only [steps] at hsh
        rw [← hm1] at hsh
        have hm1_val0 : intVal mem₀ (mem₀ (ptr + OFF_MIN1_VAL)) h L = (nodeIntMinAgg1 mem₀ nodesBase h L x).val := by
          simp only [nodeIntMinAgg1, optIntVal, ite_eq_right pm1.1]; rfl
        have hnid : ∀ (s : RawStep), (s.addDelta d).nodeId = s.nodeId := fun s => by
          cases hf : s.fwd <;> simp [RawStep.addDelta, hf]
        rw [List.map_map] at hsh ⊢
        simp only [Function.comp_def] at hsh
        simp only [Function.comp_def, RawStep.dirAvail_addDelta, hnid]
        rw [hm1_val0, hsh]
        simp [nodeIntMinAgg1, nodeField, show mem₀ (nodesBase + NODE_STRIDE * x + OFF_MIN1_HAS) = 1 from hm1_one]
      · dsimp only [nodeIntMinAgg2]
        have hm2_val_nf : nodeField mem₉ nodesBase x OFF_MIN2_VAL = out_m2 := hm2_val_eq
        rw [hnf9_oth_x OFF_MIN2_HAS (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hnf9_oth_x OFF_MIN2_FIRST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hnf9_oth_x OFF_MIN2_LAST (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hm2_val_nf, show optIntVal mem₉ h L out_m2 = intVal mem₉ out_m2 h L by simp [optIntVal, hm2_ok9.1],
          hm2_val9]
        have hsh := listIntMinAgg_shift (steps.map fun s => (s.nodeId, s.flip.dirAvail)) (-d)
        dsimp only [steps] at hsh
        rw [← hm2] at hsh
        have hm2_val0 : intVal mem₀ (mem₀ (ptr + OFF_MIN2_VAL)) h L = (nodeIntMinAgg2 mem₀ nodesBase h L x).val := by
          simp only [nodeIntMinAgg2, optIntVal, ite_eq_right pm2.1]; rfl
        have hnid : ∀ (s : RawStep), (s.addDelta d).nodeId = s.nodeId := fun s => by
          cases hf : s.fwd <;> simp [RawStep.addDelta, hf]
        rw [List.map_map] at hsh ⊢
        simp only [Function.comp_def] at hsh
        simp only [Function.comp_def, RawStep.dirAvail_flip_addDelta, hnid,
          show ∀ a : ℤ, a + d = a - -d from fun a => (sub_neg_eq_add a d).symm]
        rw [hm2_val0, hsh]
        simp [nodeIntMinAgg2, nodeField, show mem₀ (nodesBase + NODE_STRIDE * x + OFF_MIN2_HAS) = 1 from
          (show nodeField mem₀ nodesBase x OFF_MIN2_HAS = 1 from hm2h.trans hm1_one), sub_neg_eq_add]
  · intro u hu off hoff h1 h2 h3 h4 h5 h6 h7 h8
    by_cases hux : u = x
    · subst hux; exact hmem9_oth_x off hoff h1 h2 h3 h4 h5 h6 h7 h8
    · exact hmem9_node_ne u hu hux off hoff
  · intro addr haddr hne hlt
    rw [hm9_ne addr hne]
    by_cases ha_hi : addr < arenaHi
    · apply nhs5678.2.2.1 addr ha_hi
      intro off _ heq
      dsimp only [AuxTree.rootId] at haddr
      rcases haddr with h1 | h2 <;> omega
    · exact nhs5678.2.2.2 addr (by omega) hlt

end

end MinCostFlow.LinkCut.Prog
