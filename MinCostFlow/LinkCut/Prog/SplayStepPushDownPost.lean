module

public import MinCostFlow.LinkCut.Prog.SplayStepRev
public import MinCostFlow.LinkCut.Prog.SplayStepTag

namespace MinCostFlow.LinkCut.Prog

/-!
Pure post-state correctness lemmas for `pushDownBody`:
- node-index / slot disjointness and shift-fit helpers,
- `pushDownPhase1_post`: restoring `TreeMemMatch` and preserving `evalMemSteps` after
  pushing `OFF_REV` from `x` down to `l` and `r`,
- `pushDownPhase2_post`: restoring `TreeMemMatch` and preserving `evalMemSteps` after
  pushing `OFF_HAS_TAG` from `x` down to `l₁` and `r₁`.
-/

open WordRAM MinCostFlow.Num

@[expose] public section

theorem eq_one_of_le_one_ne_zero {a : ℕ} (hle : a ≤ 1) (hne : a ≠ 0) : a = 1 :=
  Nat.le_antisymm hle (Nat.one_le_iff_ne_zero.mpr hne)

theorem nodup_node_split {x : ℕ} {l r : AuxTree}
    (hnd : (AuxTree.node x l r).toList.Nodup) :
    l.toList.Nodup ∧ r.toList.Nodup ∧ x ∉ l.toList ∧ x ∉ r.toList ∧
      List.Disjoint l.toList r.toList := by
  simp only [AuxTree.toList, List.nodup_append, List.nodup_cons, List.mem_append,
    List.mem_singleton] at hnd
  rcases hnd with ⟨⟨hl_nd, _, hx_l⟩, hr_nd, hdisj⟩
  refine ⟨hl_nd, hr_nd, fun hl => hx_l x hl x rfl rfl,
    fun hr => hdisj x (Or.inr rfl) x hr rfl,
    fun u hul hur => hdisj u (Or.inl hul) u hur rfl⟩

theorem nodeId_ne_rootId_of_not_mem {u : ℕ} {q : AuxTree}
    (hu_pos : 1 ≤ u) (hu_nin : u ∉ q.toList) : u ≠ q.rootId := by
  cases q with
  | leaf =>
      simp only [AuxTree.rootId]
      omega
  | node cid _ _ =>
      intro heq
      simp only [AuxTree.rootId] at heq
      subst heq
      exact hu_nin (by simp [AuxTree.toList])

theorem nodeField_addr_ne_slot {nodesBase u qId off : ℕ}
    (hne : u ≠ qId) (hoff : off < NODE_STRIDE) :
    nodesBase + NODE_STRIDE * u + off < nodesBase + NODE_STRIDE * qId ∨
    nodesBase + NODE_STRIDE * qId + NODE_STRIDE ≤ nodesBase + NODE_STRIDE * u + off := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have hmul : NODE_STRIDE * (u + 1) ≤ NODE_STRIDE * qId := Nat.mul_le_mul_left NODE_STRIDE h
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  · right
    have hmul : NODE_STRIDE * (qId + 1) ≤ NODE_STRIDE * u := Nat.mul_le_mul_left NODE_STRIDE h
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

theorem nodeField_eq_of_outside_slot {mem₀ mem₁ : ℕ → ℕ} {nodesBase u qId off : ℕ}
    (hne : u ≠ qId) (hoff : off < NODE_STRIDE)
    (hout : ∀ addr, addr < nodesBase + NODE_STRIDE * qId ∨
      nodesBase + NODE_STRIDE * qId + NODE_STRIDE ≤ addr → mem₁ addr = mem₀ addr) :
    nodeField mem₁ nodesBase u off = nodeField mem₀ nodesBase u off :=
  hout (nodesBase + NODE_STRIDE * u + off) (nodeField_addr_ne_slot hne hoff)

theorem nodeField_eq_of_outside_slot_lt_hp {mem₀ mem₁ : ℕ → ℕ}
    {nodesBase cap u qId off : ℕ}
    (hu : u ≤ cap) (hne : u ≠ qId) (hoff : off < NODE_STRIDE)
    (harena : nodesBase + NODE_STRIDE * (cap + 1) ≤ mem₀ (nodesBase - 1))
    (hnb : 3 ≤ nodesBase)
    (hout : ∀ addr, addr < nodesBase + NODE_STRIDE * qId ∨
      nodesBase + NODE_STRIDE * qId + NODE_STRIDE ≤ addr →
      addr ≠ nodesBase - 1 → addr < mem₀ (nodesBase - 1) → mem₁ addr = mem₀ addr) :
    nodeField mem₁ nodesBase u off = nodeField mem₀ nodesBase u off := by
  have hlt_arena : nodesBase + NODE_STRIDE * u + off < nodesBase + NODE_STRIDE * (cap + 1) := by
    have hmul := Nat.mul_le_mul_left NODE_STRIDE hu
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hne_hdr : nodesBase + NODE_STRIDE * u + off ≠ nodesBase - 1 := by omega
  exact hout (nodesBase + NODE_STRIDE * u + off)
    (nodeField_addr_ne_slot hne hoff) hne_hdr (lt_of_lt_of_le hlt_arena harena)

theorem stepsShiftFit_append {h L : ℕ} {xs ys : List RawStep} {d : ℤ} :
    StepsShiftFit h L (xs ++ ys) d ↔ StepsShiftFit h L xs d ∧ StepsShiftFit h L ys d := by
  constructor
  · intro hxy
    exact ⟨fun s hs => hxy s (List.mem_append_left ys hs),
      fun s hs => hxy s (List.mem_append_right xs hs)⟩
  · rintro ⟨hx, hy⟩ s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hx s hs
    · exact hy s hs

theorem pushDownPhase1_post {w h L nodesBase cap x parId pp : ℕ}
    {mem₀ mem₁ : ℕ → ℕ} {l r : AuxTree}
    (ht : TreeMemMatch w h L mem₀ nodesBase cap (.node x l r) parId pp)
    (hrev1 : nodeField mem₀ nodesBase x OFF_REV ≠ 0)
    (hm_l : TreeMemMatch w h L mem₁ nodesBase cap l.revRoot x 0)
    (hm_r : TreeMemMatch w h L mem₁ nodesBase cap r.revRoot x 0)
    (hsteps_l : evalMemSteps mem₁ nodesBase h L l.revRoot false 0 =
      (evalMemSteps mem₀ nodesBase h L l false 0).reverse.map RawStep.flip)
    (hsteps_r : evalMemSteps mem₁ nodesBase h L r.revRoot false 0 =
      (evalMemSteps mem₀ nodesBase h L r false 0).reverse.map RawStep.flip)
    (heval_l : l.revRoot.evalInorder (revFlag mem₁ nodesBase) false =
      (l.evalInorder (revFlag mem₀ nodesBase) false).reverse)
    (heval_r : r.revRoot.evalInorder (revFlag mem₁ nodesBase) false =
      (r.evalInorder (revFlag mem₀ nodesBase) false).reverse)
    (hx_rev : nodeField mem₁ nodesBase x OFF_REV = 0)
    (hx_other : ∀ off < NODE_STRIDE, off ≠ OFF_REV →
      nodeField mem₁ nodesBase x off = nodeField mem₀ nodesBase x off)
    (hisv : ∀ u ∈ (AuxTree.node x l r).toList,
      nodeField mem₁ nodesBase u OFF_ISV = nodeField mem₀ nodesBase u OFF_ISV)
    (hhp : mem₁ (nodesBase - 1) = mem₀ (nodesBase - 1))
    (hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₀ (nodesBase - 1) →
      mem₁ a = mem₀ a) :
    TreeMemMatch w h L mem₁ nodesBase cap (.node x l.revRoot r.revRoot) parId pp ∧
    evalMemSteps mem₁ nodesBase h L (.node x l.revRoot r.revRoot) false 0 =
      evalMemSteps mem₀ nodesBase h L (.node x l r) false 0 ∧
    (AuxTree.node x l.revRoot r.revRoot).evalInorder (revFlag mem₁ nodesBase) false =
      (AuxTree.node x l r).evalInorder (revFlag mem₀ nodesBase) false ∧
    revFlag mem₁ nodesBase x = false := by
  rcases ht with ⟨hx1, hx2, hL, hR, hP, hPP, hr, hiv, hhe, hsum, hdir, hht, htn,
    heu, hev, heid, he1, he0, hcf, hcb, htag1, htag0, hm1h, hm2h, hm1_1, hm1_0,
    hagg, hl_m, hr_m⟩
  have hr_eq1 : nodeField mem₀ nodesBase x OFF_REV = 1 :=
    eq_one_of_le_one_ne_zero hr hrev1
  have hrev0 : revFlag mem₀ nodesBase x = true := by simp [revFlag, hr_eq1]
  have hrev1' : revFlag mem₁ nodesBase x = false := by simp [revFlag, hx_rev]
  have htag_x : nodeTagInt mem₁ nodesBase h L x = nodeTagInt mem₀ nodesBase h L x := by
    simp only [nodeTagInt, hx_other OFF_HAS_TAG (by decide) (by decide),
      hx_other OFF_TAG_NEG (by decide) (by decide), hx_other OFF_TAG_PTR (by decide) (by decide)]
    by_cases hht0 : nodeField mem₀ nodesBase x OFF_HAS_TAG = 0
    · simp [hht0]
    · have hht1 : nodeField mem₀ nodesBase x OFF_HAS_TAG = 1 :=
        eq_one_of_le_one_ne_zero hht hht0
      rcases (htag1 hht1).1 with ⟨_, hlo, hhi, hval⟩
      have heq_t : optIntVal mem₁ h L (nodeField mem₀ nodesBase x OFF_TAG_PTR) =
          optIntVal mem₀ h L (nodeField mem₀ nodesBase x OFF_TAG_PTR) :=
        optIntVal_agree_heap hheap (Or.inr ⟨hlo, hhi, hval⟩)
      simp only [hht0, ↓reduceIte, heq_t]
  have hown_x : nodeOwnRawStep mem₁ nodesBase h L x = nodeOwnRawStep mem₀ nodesBase h L x := by
    simp only [nodeOwnRawStep, hx_other OFF_HASE (by decide) (by decide)]
    by_cases hhe0 : nodeField mem₀ nodesBase x OFF_HASE = 0
    · simp [hhe0]
    · have hhe1 : nodeField mem₀ nodesBase x OFF_HASE = 1 :=
        eq_one_of_le_one_ne_zero hhe hhe0
      rcases he1 hhe1 with ⟨hf_ok, haf_ok, hab_ok, hcf_ok, hcb_ok, _⟩
      have heq_f : intVal mem₁ (nodeField mem₁ nodesBase x OFF_FLOW_PTR) h L =
          intVal mem₀ (nodeField mem₀ nodesBase x OFF_FLOW_PTR) h L := by
        rw [hx_other OFF_FLOW_PTR (by decide) (by decide)]
        exact intVal_agree_heap hheap hf_ok.2.1 hf_ok.2.2.1
      have heq_af : intVal mem₁ (nodeField mem₁ nodesBase x OFF_AF_PTR) h L =
          intVal mem₀ (nodeField mem₀ nodesBase x OFF_AF_PTR) h L := by
        rw [hx_other OFF_AF_PTR (by decide) (by decide)]
        exact intVal_agree_heap hheap haf_ok.2.1 haf_ok.2.2.1
      have heq_ab : intVal mem₁ (nodeField mem₁ nodesBase x OFF_AB_PTR) h L =
          intVal mem₀ (nodeField mem₀ nodesBase x OFF_AB_PTR) h L := by
        rw [hx_other OFF_AB_PTR (by decide) (by decide)]
        exact intVal_agree_heap hheap hab_ok.2.1 hab_ok.2.2.1
      have heq_cf : intVal mem₁ (nodeField mem₁ nodesBase x OFF_COST_FWD) h L =
          intVal mem₀ (nodeField mem₀ nodesBase x OFF_COST_FWD) h L := by
        rw [hx_other OFF_COST_FWD (by decide) (by decide)]
        exact intVal_agree_heap hheap hcf_ok.2.1 hcf_ok.2.2.1
      have heq_cb : intVal mem₁ (nodeField mem₁ nodesBase x OFF_COST_BWD) h L =
          intVal mem₀ (nodeField mem₀ nodesBase x OFF_COST_BWD) h L := by
        rw [hx_other OFF_COST_BWD (by decide) (by decide)]
        exact intVal_agree_heap hheap hcb_ok.2.1 hcb_ok.2.2.1
      simp only [hhe0, ↓reduceIte, hx_other OFF_DIR (by decide) (by decide),
        hx_other OFF_EID (by decide) (by decide), hx_other OFF_EU (by decide) (by decide),
        hx_other OFF_EV (by decide) (by decide), heq_f, heq_af, heq_ab, heq_cf, heq_cb]
  have hl_true_eq : evalMemSteps mem₁ nodesBase h L l.revRoot false 0 =
      evalMemSteps mem₀ nodesBase h L l true 0 := by
    rw [hsteps_l]
    simpa using (evalMemSteps_true_eq hl_m 0).symm
  have hr_true_eq : evalMemSteps mem₁ nodesBase h L r.revRoot false 0 =
      evalMemSteps mem₀ nodesBase h L r true 0 := by
    rw [hsteps_r]
    simpa using (evalMemSteps_true_eq hr_m 0).symm
  have hsteps_eq :
      evalMemSteps mem₁ nodesBase h L (.node x l.revRoot r.revRoot) false 0 =
        evalMemSteps mem₀ nodesBase h L (.node x l r) false 0 := by
    have hl_δ : evalMemSteps mem₁ nodesBase h L l.revRoot false (nodeTagInt mem₁ nodesBase h L x) =
        evalMemSteps mem₀ nodesBase h L l true (nodeTagInt mem₀ nodesBase h L x) := by
      rw [← add_zero (nodeTagInt mem₁ nodesBase h L x),
        evalMemSteps_addDeltaMod hm_l false _ 0, hl_true_eq, htag_x,
        ← evalMemSteps_addDeltaMod hl_m true (nodeTagInt mem₀ nodesBase h L x) 0, add_zero]
    have hr_δ : evalMemSteps mem₁ nodesBase h L r.revRoot false (nodeTagInt mem₁ nodesBase h L x) =
        evalMemSteps mem₀ nodesBase h L r true (nodeTagInt mem₀ nodesBase h L x) := by
      rw [← add_zero (nodeTagInt mem₁ nodesBase h L x),
        evalMemSteps_addDeltaMod hm_r false _ 0, hr_true_eq, htag_x,
        ← evalMemSteps_addDeltaMod hr_m true (nodeTagInt mem₀ nodesBase h L x) 0, add_zero]
    simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.false_xor, hrev1', hrev0,
      hown_x, zero_add]
    rw [hl_δ, hr_δ]
  have heval_eq :
      (AuxTree.node x l.revRoot r.revRoot).evalInorder (revFlag mem₁ nodesBase) false =
        (AuxTree.node x l r).evalInorder (revFlag mem₀ nodesBase) false := by
    simp only [AuxTree.evalInorder, hrev1', hrev0, heval_l, heval_r, AuxTree.evalInorder_true]
  refine ⟨?_, hsteps_eq, heval_eq, hrev1'⟩
  have he_lt : mem₀ (nodesBase - 1) ≤ mem₁ (nodesBase - 1) := by rw [hhp]
  have hL' : nodeField mem₁ nodesBase x OFF_LEFT = l.revRoot.rootId := by
    rw [hx_other OFF_LEFT (by decide) (by decide), AuxTree.revRoot_rootId, hL]
  have hR' : nodeField mem₁ nodesBase x OFF_RIGHT = r.revRoot.rootId := by
    rw [hx_other OFF_RIGHT (by decide) (by decide), AuxTree.revRoot_rootId, hR]
  have hm_hp : ∀ ptr, NumPtrOk mem₀ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₀ (nodesBase - 1)) h L ptr →
      NumPtrOk mem₁ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₁ (nodesBase - 1)) h L ptr :=
    fun ptr hp_ok => numPtrOk_congr he_lt hheap hp_ok
  refine ⟨hx1, hx2, hL', hR',
    (hx_other OFF_PARENT (by decide) (by decide)).trans hP,
    (hx_other OFF_PPAR (by decide) (by decide)).trans hPP,
    by rw [hx_rev]; exact Nat.zero_le 1,
    by rw [hx_other OFF_ISV (by decide) (by decide)]; exact hiv,
    by rw [hx_other OFF_HASE (by decide) (by decide)]; exact hhe,
    by rw [hx_other OFF_ISV (by decide) (by decide), hx_other OFF_HASE (by decide) (by decide)]; exact hsum,
    by rw [hx_other OFF_DIR (by decide) (by decide)]; exact hdir,
    by rw [hx_other OFF_HAS_TAG (by decide) (by decide)]; exact hht,
    by rw [hx_other OFF_TAG_NEG (by decide) (by decide)]; exact htn,
    by rw [hx_other OFF_EU (by decide) (by decide)]; exact heu,
    by rw [hx_other OFF_EV (by decide) (by decide)]; exact hev,
    by rw [hx_other OFF_EID (by decide) (by decide)]; exact heid,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm_l, hm_r⟩
  · intro hhe1
    rw [hx_other OFF_HASE (by decide) (by decide)] at hhe1
    rcases he1 hhe1 with ⟨hf_ok, haf_ok, hab_ok, hcf_ok, hcb_ok, hcb_eq⟩
    rw [hx_other OFF_FLOW_PTR (by decide) (by decide), hx_other OFF_AF_PTR (by decide) (by decide),
      hx_other OFF_AB_PTR (by decide) (by decide), hx_other OFF_COST_FWD (by decide) (by decide),
      hx_other OFF_COST_BWD (by decide) (by decide)]
    refine ⟨hm_hp _ hf_ok, hm_hp _ haf_ok, hm_hp _ hab_ok, hm_hp _ hcf_ok, hm_hp _ hcb_ok, ?_⟩
    rw [intVal_agree_heap hheap hcb_ok.2.1 hcb_ok.2.2.1,
      intVal_agree_heap hheap hcf_ok.2.1 hcf_ok.2.2.1]
    exact hcb_eq
  · intro hhe0
    rw [hx_other OFF_HASE (by decide) (by decide)] at hhe0
    rw [hx_other OFF_DIR (by decide) (by decide), hx_other OFF_FLOW_PTR (by decide) (by decide),
      hx_other OFF_AF_PTR (by decide) (by decide), hx_other OFF_AB_PTR (by decide) (by decide),
      hx_other OFF_COST_FWD (by decide) (by decide), hx_other OFF_COST_BWD (by decide) (by decide)]
    exact he0 hhe0
  · rw [hx_other OFF_CSUM_FWD (by decide) (by decide)]
    exact optNumPtrOk_congr he_lt hheap hcf
  · rw [hx_other OFF_CSUM_BWD (by decide) (by decide)]
    exact optNumPtrOk_congr he_lt hheap hcb
  · intro hht1
    rw [hx_other OFF_HAS_TAG (by decide) (by decide)] at hht1
    rcases htag1 hht1 with ⟨htp_ok, hch, d, hdmod, hfit⟩
    rw [hx_other OFF_TAG_PTR (by decide) (by decide)]
    refine ⟨hm_hp _ htp_ok, ?_, d, ?_, ?_⟩
    · rcases hch with ⟨hl_ne, hl_m1⟩ | ⟨hr_ne, hr_m1⟩
      · left
        have hnil0 : evalMemSteps mem₀ nodesBase h L l false 0 ≠ [] :=
          (TreeMemMatch.min1Has_iff_evalSteps_ne_nil hl_m).mp ⟨hl_ne, hl_m1⟩
        have hnil1 : evalMemSteps mem₁ nodesBase h L l.revRoot false 0 ≠ [] := by
          rw [hsteps_l]; simp [hnil0]
        exact (TreeMemMatch.min1Has_iff_evalSteps_ne_nil hm_l).mpr hnil1
      · right
        have hnil0 : evalMemSteps mem₀ nodesBase h L r false 0 ≠ [] :=
          (TreeMemMatch.min1Has_iff_evalSteps_ne_nil hr_m).mp ⟨hr_ne, hr_m1⟩
        have hnil1 : evalMemSteps mem₁ nodesBase h L r.revRoot false 0 ≠ [] := by
          rw [hsteps_r]; simp [hnil0]
        exact (TreeMemMatch.min1Has_iff_evalSteps_ne_nil hm_r).mpr hnil1
    · rw [htag_x]; exact hdmod
    · rwa [hrev1', hl_true_eq, hr_true_eq, ← hrev0]
  · intro hht0
    rw [hx_other OFF_HAS_TAG (by decide) (by decide)] at hht0
    rw [hx_other OFF_TAG_PTR (by decide) (by decide), hx_other OFF_TAG_NEG (by decide) (by decide)]
    exact htag0 hht0
  · rw [hx_other OFF_MIN1_HAS (by decide) (by decide)]; exact hm1h
  · rw [hx_other OFF_MIN2_HAS (by decide) (by decide), hx_other OFF_MIN1_HAS (by decide) (by decide)]; exact hm2h
  · intro hm1
    rw [hx_other OFF_MIN1_HAS (by decide) (by decide)] at hm1
    rcases hm1_1 hm1 with ⟨hm1v, hm2v, h1f, h1l, h2f, h2l⟩
    rw [hx_other OFF_MIN1_VAL (by decide) (by decide), hx_other OFF_MIN2_VAL (by decide) (by decide),
      hx_other OFF_MIN1_FIRST (by decide) (by decide), hx_other OFF_MIN1_LAST (by decide) (by decide),
      hx_other OFF_MIN2_FIRST (by decide) (by decide), hx_other OFF_MIN2_LAST (by decide) (by decide)]
    exact ⟨hm_hp _ hm1v, hm_hp _ hm2v, h1f, h1l, h2f, h2l⟩
  · intro hm0
    rw [hx_other OFF_MIN1_HAS (by decide) (by decide)] at hm0
    rw [hx_other OFF_MIN1_VAL (by decide) (by decide), hx_other OFF_MIN1_FIRST (by decide) (by decide),
      hx_other OFF_MIN1_LAST (by decide) (by decide), hx_other OFF_MIN2_VAL (by decide) (by decide),
      hx_other OFF_MIN2_FIRST (by decide) (by decide), hx_other OFF_MIN2_LAST (by decide) (by decide)]
    exact hm1_0 hm0
  · dsimp only
    rcases hagg with ⟨hvcnt, hcsf, hcsb, hne_iff, hagg1, hagg2⟩
    have hvcnt_eq : listVcnt mem₁ nodesBase ((AuxTree.node x l r).evalInorder (revFlag mem₀ nodesBase) false) =
        listVcnt mem₀ nodesBase ((AuxTree.node x l r).evalInorder (revFlag mem₀ nodesBase) false) :=
      listVcnt_agree_of_mem fun u hu =>
        hisv u ((AuxTree.evalInorder_perm _ _ _).mem_iff.1 hu)
    rw [heval_eq, hsteps_eq, hvcnt_eq, hx_other OFF_VCNT (by decide) (by decide),
      hx_other OFF_MIN1_HAS (by decide) (by decide)]
    have hcsf_eq : optIntVal mem₁ h L (nodeField mem₁ nodesBase x OFF_CSUM_FWD) =
        optIntVal mem₀ h L (nodeField mem₀ nodesBase x OFF_CSUM_FWD) := by
      rw [hx_other OFF_CSUM_FWD (by decide) (by decide)]
      exact optIntVal_agree_heap hheap hcf
    have hcsb_eq : optIntVal mem₁ h L (nodeField mem₁ nodesBase x OFF_CSUM_BWD) =
        optIntVal mem₀ h L (nodeField mem₀ nodesBase x OFF_CSUM_BWD) := by
      rw [hx_other OFF_CSUM_BWD (by decide) (by decide)]
      exact optIntVal_agree_heap hheap hcb
    have hagg1_eq : nodeIntMinAgg1 mem₁ nodesBase h L x = nodeIntMinAgg1 mem₀ nodesBase h L x := by
      simp only [nodeIntMinAgg1, hx_other OFF_MIN1_HAS (by decide) (by decide),
        hx_other OFF_MIN1_VAL (by decide) (by decide),
        hx_other OFF_MIN1_FIRST (by decide) (by decide),
        hx_other OFF_MIN1_LAST (by decide) (by decide)]
      by_cases hm1z : nodeField mem₀ nodesBase x OFF_MIN1_HAS = 0
      · obtain ⟨hm1v, _⟩ := hm1_0 hm1z
        simp [optIntVal, hm1v]
      · have hm1_one : nodeField mem₀ nodesBase x OFF_MIN1_HAS = 1 :=
          eq_one_of_le_one_ne_zero hm1h hm1z
        obtain ⟨hm1v, _⟩ := hm1_1 hm1_one
        simp [optIntVal_agree_heap hheap (Or.inr ⟨hm1v.2.1, hm1v.2.2.1, hm1v.2.2.2⟩)]
    have hagg2_eq : nodeIntMinAgg2 mem₁ nodesBase h L x = nodeIntMinAgg2 mem₀ nodesBase h L x := by
      simp only [nodeIntMinAgg2, hx_other OFF_MIN2_HAS (by decide) (by decide),
        hx_other OFF_MIN2_VAL (by decide) (by decide),
        hx_other OFF_MIN2_FIRST (by decide) (by decide),
        hx_other OFF_MIN2_LAST (by decide) (by decide)]
      by_cases hm2z : nodeField mem₀ nodesBase x OFF_MIN1_HAS = 0
      · have hm2v := (hm1_0 hm2z).2.2.2.1
        simp [optIntVal, hm2v]
      · have hm1_one : nodeField mem₀ nodesBase x OFF_MIN1_HAS = 1 :=
          eq_one_of_le_one_ne_zero hm1h hm2z
        obtain ⟨_, hm2v, _⟩ := hm1_1 hm1_one
        simp [optIntVal_agree_heap hheap (Or.inr ⟨hm2v.2.1, hm2v.2.2.1, hm2v.2.2.2⟩)]
    refine ⟨hvcnt, ?_, ?_, hne_iff, ?_, ?_⟩
    · rw [hcsf_eq]; exact hcsf
    · rw [hcsb_eq]; exact hcsb
    · rw [hagg1_eq]; exact hagg1
    · rw [hagg2_eq]; exact hagg2

theorem pushDownPhase2_post {w h L nodesBase cap x parId pp : ℕ}
    {mem₁ mem₄ : ℕ → ℕ} {l₁ r₁ : AuxTree} {d : ℤ}
    (ht : TreeMemMatch w h L mem₁ nodesBase cap (.node x l₁ r₁) parId pp)
    (hrev1 : revFlag mem₁ nodesBase x = false)
    (hdmod : d % (capacity h L : ℤ) = nodeTagInt mem₁ nodesBase h L x % (capacity h L : ℤ))
    (hfit_l : StepsShiftFit h L (evalMemSteps mem₁ nodesBase h L l₁ false 0) d)
    (hfit_r : StepsShiftFit h L (evalMemSteps mem₁ nodesBase h L r₁ false 0) d)
    (hm_l : TreeMemMatch w h L mem₄ nodesBase cap l₁ x 0)
    (hm_r : TreeMemMatch w h L mem₄ nodesBase cap r₁ x 0)
    (hsteps_l : evalMemSteps mem₄ nodesBase h L l₁ false 0 =
      (evalMemSteps mem₁ nodesBase h L l₁ false 0).map (fun q => q.addDelta d))
    (hsteps_r : evalMemSteps mem₄ nodesBase h L r₁ false 0 =
      (evalMemSteps mem₁ nodesBase h L r₁ false 0).map (fun q => q.addDelta d))
    (hx_ht : nodeField mem₄ nodesBase x OFF_HAS_TAG = 0)
    (hx_tp : nodeField mem₄ nodesBase x OFF_TAG_PTR = 0)
    (hx_tn : nodeField mem₄ nodesBase x OFF_TAG_NEG = 0)
    (hx_other : ∀ off < NODE_STRIDE, off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
      nodeField mem₄ nodesBase x off = nodeField mem₁ nodesBase x off)
    (hisv : ∀ u ∈ (AuxTree.node x l₁ r₁).toList,
      nodeField mem₄ nodesBase u OFF_ISV = nodeField mem₁ nodesBase u OFF_ISV)
    (hrev_eq : ∀ u ∈ (AuxTree.node x l₁ r₁).toList,
      nodeField mem₄ nodesBase u OFF_REV = nodeField mem₁ nodesBase u OFF_REV)
    (hhp : mem₁ (nodesBase - 1) ≤ mem₄ (nodesBase - 1))
    (hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₁ (nodesBase - 1) →
      mem₄ a = mem₁ a) :
    TreeMemMatch w h L mem₄ nodesBase cap (.node x l₁ r₁) parId pp ∧
    evalMemSteps mem₄ nodesBase h L (.node x l₁ r₁) false 0 =
      evalMemSteps mem₁ nodesBase h L (.node x l₁ r₁) false 0 ∧
    (AuxTree.node x l₁ r₁).evalInorder (revFlag mem₄ nodesBase) false =
      (AuxTree.node x l₁ r₁).evalInorder (revFlag mem₁ nodesBase) false := by
  rcases ht with ⟨hx1, hx2, hL, hR, hP, hPP, hr, hiv, hhe, hsum, hdir, _, _,
    heu, hev, heid, he1, he0, hcf, hcb, _, _, hm1h, hm2h, hm1_1, hm1_0,
    hagg, hl_m, hr_m⟩
  have hx_f : ∀ off, off < NODE_STRIDE → off ≠ OFF_HAS_TAG → off ≠ OFF_TAG_PTR → off ≠ OFF_TAG_NEG →
      nodeField mem₄ nodesBase x off = nodeField mem₁ nodesBase x off := hx_other
  have hrev4 : revFlag mem₄ nodesBase x = false := by
    simp only [revFlag, hrev_eq x (by simp [AuxTree.toList])]
    exact hrev1
  have htag4 : nodeTagInt mem₄ nodesBase h L x = 0 := by
    simp [nodeTagInt, hx_ht]
  have hown_x : nodeOwnRawStep mem₄ nodesBase h L x = nodeOwnRawStep mem₁ nodesBase h L x := by
    simp only [nodeOwnRawStep, hx_f OFF_HASE (by decide) (by decide) (by decide) (by decide)]
    by_cases hhe0 : nodeField mem₁ nodesBase x OFF_HASE = 0
    · simp [hhe0]
    · have hhe1 : nodeField mem₁ nodesBase x OFF_HASE = 1 :=
        eq_one_of_le_one_ne_zero hhe hhe0
      rcases he1 hhe1 with ⟨hf_ok, haf_ok, hab_ok, hcf_ok, hcb_ok, _⟩
      have heq_f : intVal mem₄ (nodeField mem₄ nodesBase x OFF_FLOW_PTR) h L =
          intVal mem₁ (nodeField mem₁ nodesBase x OFF_FLOW_PTR) h L := by
        rw [hx_f OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide)]
        exact intVal_agree_heap hheap hf_ok.2.1 hf_ok.2.2.1
      have heq_af : intVal mem₄ (nodeField mem₄ nodesBase x OFF_AF_PTR) h L =
          intVal mem₁ (nodeField mem₁ nodesBase x OFF_AF_PTR) h L := by
        rw [hx_f OFF_AF_PTR (by decide) (by decide) (by decide) (by decide)]
        exact intVal_agree_heap hheap haf_ok.2.1 haf_ok.2.2.1
      have heq_ab : intVal mem₄ (nodeField mem₄ nodesBase x OFF_AB_PTR) h L =
          intVal mem₁ (nodeField mem₁ nodesBase x OFF_AB_PTR) h L := by
        rw [hx_f OFF_AB_PTR (by decide) (by decide) (by decide) (by decide)]
        exact intVal_agree_heap hheap hab_ok.2.1 hab_ok.2.2.1
      have heq_cf : intVal mem₄ (nodeField mem₄ nodesBase x OFF_COST_FWD) h L =
          intVal mem₁ (nodeField mem₁ nodesBase x OFF_COST_FWD) h L := by
        rw [hx_f OFF_COST_FWD (by decide) (by decide) (by decide) (by decide)]
        exact intVal_agree_heap hheap hcf_ok.2.1 hcf_ok.2.2.1
      have heq_cb : intVal mem₄ (nodeField mem₄ nodesBase x OFF_COST_BWD) h L =
          intVal mem₁ (nodeField mem₁ nodesBase x OFF_COST_BWD) h L := by
        rw [hx_f OFF_COST_BWD (by decide) (by decide) (by decide) (by decide)]
        exact intVal_agree_heap hheap hcb_ok.2.1 hcb_ok.2.2.1
      simp only [hhe0, ↓reduceIte,
        hx_f OFF_DIR (by decide) (by decide) (by decide) (by decide),
        hx_f OFF_EID (by decide) (by decide) (by decide) (by decide),
        hx_f OFF_EU (by decide) (by decide) (by decide) (by decide),
        hx_f OFF_EV (by decide) (by decide) (by decide) (by decide),
        heq_f, heq_af, heq_ab, heq_cf, heq_cb]
  have hsteps_l_eq :
      evalMemSteps mem₄ nodesBase h L l₁ false 0 =
        evalMemSteps mem₁ nodesBase h L l₁ false (nodeTagInt mem₁ nodesBase h L x) := by
    rw [hsteps_l, ← stepsShiftFit_map_addDeltaMod_eq hfit_l hdmod.symm,
      ← evalMemSteps_addDeltaMod hl_m false (nodeTagInt mem₁ nodesBase h L x) 0, add_zero]
  have hsteps_r_eq :
      evalMemSteps mem₄ nodesBase h L r₁ false 0 =
        evalMemSteps mem₁ nodesBase h L r₁ false (nodeTagInt mem₁ nodesBase h L x) := by
    rw [hsteps_r, ← stepsShiftFit_map_addDeltaMod_eq hfit_r hdmod.symm,
      ← evalMemSteps_addDeltaMod hr_m false (nodeTagInt mem₁ nodesBase h L x) 0, add_zero]
  have hsteps_eq :
      evalMemSteps mem₄ nodesBase h L (.node x l₁ r₁) false 0 =
        evalMemSteps mem₁ nodesBase h L (.node x l₁ r₁) false 0 := by
    simp only [evalMemSteps, Bool.false_eq_true, ↓reduceIte, Bool.false_xor,
      hrev4, hrev1, htag4, hown_x, zero_add]
    rw [hsteps_l_eq, hsteps_r_eq]
  have heval_eq :
      (AuxTree.node x l₁ r₁).evalInorder (revFlag mem₄ nodesBase) false =
        (AuxTree.node x l₁ r₁).evalInorder (revFlag mem₁ nodesBase) false :=
    evalInorder_agree_of_list hrev_eq false
  refine ⟨?_, hsteps_eq, heval_eq⟩
  have hm_hp : ∀ ptr, NumPtrOk mem₁ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₁ (nodesBase - 1)) h L ptr →
      NumPtrOk mem₄ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₄ (nodesBase - 1)) h L ptr :=
    fun ptr hp_ok => numPtrOk_congr hhp hheap hp_ok
  refine ⟨hx1, hx2,
    (hx_f OFF_LEFT (by decide) (by decide) (by decide) (by decide)).trans hL,
    (hx_f OFF_RIGHT (by decide) (by decide) (by decide) (by decide)).trans hR,
    (hx_f OFF_PARENT (by decide) (by decide) (by decide) (by decide)).trans hP,
    (hx_f OFF_PPAR (by decide) (by decide) (by decide) (by decide)).trans hPP,
    by rw [hx_f OFF_REV (by decide) (by decide) (by decide) (by decide)]; exact hr,
    by rw [hx_f OFF_ISV (by decide) (by decide) (by decide) (by decide)]; exact hiv,
    by rw [hx_f OFF_HASE (by decide) (by decide) (by decide) (by decide)]; exact hhe,
    by rw [hx_f OFF_ISV (by decide) (by decide) (by decide) (by decide),
           hx_f OFF_HASE (by decide) (by decide) (by decide) (by decide)]; exact hsum,
    by rw [hx_f OFF_DIR (by decide) (by decide) (by decide) (by decide)]; exact hdir,
    by rw [hx_ht]; exact Nat.zero_le 1,
    by rw [hx_tn]; exact Nat.zero_le 1,
    by rw [hx_f OFF_EU (by decide) (by decide) (by decide) (by decide)]; exact heu,
    by rw [hx_f OFF_EV (by decide) (by decide) (by decide) (by decide)]; exact hev,
    by rw [hx_f OFF_EID (by decide) (by decide) (by decide) (by decide)]; exact heid,
    ?_, ?_, ?_, ?_, fun h => absurd h (by rw [hx_ht]; exact Nat.zero_ne_one),
    fun _ => ⟨hx_tp, hx_tn⟩,
    ?_, ?_, ?_, ?_, ?_, hm_l, hm_r⟩
  · intro hhe1
    rw [hx_f OFF_HASE (by decide) (by decide) (by decide) (by decide)] at hhe1
    rcases he1 hhe1 with ⟨hf_ok, haf_ok, hab_ok, hcf_ok, hcb_ok, hcb_eq⟩
    rw [hx_f OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_AF_PTR (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_AB_PTR (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_COST_FWD (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_COST_BWD (by decide) (by decide) (by decide) (by decide)]
    refine ⟨hm_hp _ hf_ok, hm_hp _ haf_ok, hm_hp _ hab_ok, hm_hp _ hcf_ok, hm_hp _ hcb_ok, ?_⟩
    rw [intVal_agree_heap hheap hcb_ok.2.1 hcb_ok.2.2.1,
      intVal_agree_heap hheap hcf_ok.2.1 hcf_ok.2.2.1]
    exact hcb_eq
  · intro hhe0
    rw [hx_f OFF_HASE (by decide) (by decide) (by decide) (by decide)] at hhe0
    rw [hx_f OFF_DIR (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_AF_PTR (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_AB_PTR (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_COST_FWD (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_COST_BWD (by decide) (by decide) (by decide) (by decide)]
    exact he0 hhe0
  · rw [hx_f OFF_CSUM_FWD (by decide) (by decide) (by decide) (by decide)]
    exact optNumPtrOk_congr hhp hheap hcf
  · rw [hx_f OFF_CSUM_BWD (by decide) (by decide) (by decide) (by decide)]
    exact optNumPtrOk_congr hhp hheap hcb
  · rw [hx_f OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide)]; exact hm1h
  · rw [hx_f OFF_MIN2_HAS (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide)]; exact hm2h
  · intro hm1
    rw [hx_f OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide)] at hm1
    rcases hm1_1 hm1 with ⟨hm1v, hm2v, h1f, h1l, h2f, h2l⟩
    rw [hx_f OFF_MIN1_VAL (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN2_VAL (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN1_FIRST (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN1_LAST (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN2_FIRST (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN2_LAST (by decide) (by decide) (by decide) (by decide)]
    exact ⟨hm_hp _ hm1v, hm_hp _ hm2v, h1f, h1l, h2f, h2l⟩
  · intro hm0
    rw [hx_f OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide)] at hm0
    rw [hx_f OFF_MIN1_VAL (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN1_FIRST (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN1_LAST (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN2_VAL (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN2_FIRST (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN2_LAST (by decide) (by decide) (by decide) (by decide)]
    exact hm1_0 hm0
  · dsimp only
    rcases hagg with ⟨hvcnt, hcsf, hcsb, hne_iff, hagg1, hagg2⟩
    have hvcnt_eq : listVcnt mem₄ nodesBase ((AuxTree.node x l₁ r₁).evalInorder (revFlag mem₁ nodesBase) false) =
        listVcnt mem₁ nodesBase ((AuxTree.node x l₁ r₁).evalInorder (revFlag mem₁ nodesBase) false) :=
      listVcnt_agree_of_mem fun u hu =>
        hisv u ((AuxTree.evalInorder_perm _ _ _).mem_iff.1 hu)
    rw [heval_eq, hsteps_eq, hvcnt_eq,
      hx_f OFF_VCNT (by decide) (by decide) (by decide) (by decide),
      hx_f OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide)]
    have hcsf_eq : optIntVal mem₄ h L (nodeField mem₄ nodesBase x OFF_CSUM_FWD) =
        optIntVal mem₁ h L (nodeField mem₁ nodesBase x OFF_CSUM_FWD) := by
      rw [hx_f OFF_CSUM_FWD (by decide) (by decide) (by decide) (by decide)]
      exact optIntVal_agree_heap hheap hcf
    have hcsb_eq : optIntVal mem₄ h L (nodeField mem₄ nodesBase x OFF_CSUM_BWD) =
        optIntVal mem₁ h L (nodeField mem₁ nodesBase x OFF_CSUM_BWD) := by
      rw [hx_f OFF_CSUM_BWD (by decide) (by decide) (by decide) (by decide)]
      exact optIntVal_agree_heap hheap hcb
    have hagg1_eq : nodeIntMinAgg1 mem₄ nodesBase h L x = nodeIntMinAgg1 mem₁ nodesBase h L x := by
      simp only [nodeIntMinAgg1,
        hx_f OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide),
        hx_f OFF_MIN1_VAL (by decide) (by decide) (by decide) (by decide),
        hx_f OFF_MIN1_FIRST (by decide) (by decide) (by decide) (by decide),
        hx_f OFF_MIN1_LAST (by decide) (by decide) (by decide) (by decide)]
      by_cases hm1z : nodeField mem₁ nodesBase x OFF_MIN1_HAS = 0
      · obtain ⟨hm1v, _⟩ := hm1_0 hm1z
        simp [optIntVal, hm1v]
      · have hm1_one : nodeField mem₁ nodesBase x OFF_MIN1_HAS = 1 :=
          eq_one_of_le_one_ne_zero hm1h hm1z
        obtain ⟨hm1v, _⟩ := hm1_1 hm1_one
        simp [optIntVal_agree_heap hheap (Or.inr ⟨hm1v.2.1, hm1v.2.2.1, hm1v.2.2.2⟩)]
    have hagg2_eq : nodeIntMinAgg2 mem₄ nodesBase h L x = nodeIntMinAgg2 mem₁ nodesBase h L x := by
      simp only [nodeIntMinAgg2,
        hx_f OFF_MIN2_HAS (by decide) (by decide) (by decide) (by decide),
        hx_f OFF_MIN2_VAL (by decide) (by decide) (by decide) (by decide),
        hx_f OFF_MIN2_FIRST (by decide) (by decide) (by decide) (by decide),
        hx_f OFF_MIN2_LAST (by decide) (by decide) (by decide) (by decide)]
      by_cases hm2z : nodeField mem₁ nodesBase x OFF_MIN1_HAS = 0
      · have hm2v := (hm1_0 hm2z).2.2.2.1
        simp [optIntVal, hm2v]
      · have hm1_one : nodeField mem₁ nodesBase x OFF_MIN1_HAS = 1 :=
          eq_one_of_le_one_ne_zero hm1h hm2z
        obtain ⟨_, hm2v, _⟩ := hm1_1 hm1_one
        simp [optIntVal_agree_heap hheap (Or.inr ⟨hm2v.2.1, hm2v.2.2.1, hm2v.2.2.2⟩)]
    refine ⟨hvcnt, ?_, ?_, hne_iff, ?_, ?_⟩
    · rw [hcsf_eq]; exact hcsf
    · rw [hcsb_eq]; exact hcsb
    · rw [hagg1_eq]; exact hagg1
    · rw [hagg2_eq]; exact hagg2

end

end MinCostFlow.LinkCut.Prog
