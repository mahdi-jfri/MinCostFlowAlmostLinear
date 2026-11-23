module

public import MinCostFlow.LinkCut.Prog.SplayMemDecode

/-!
This file defines the memory-level representation invariant `SplayForestOk` connecting
Word-RAM memory at `[nodesBase, mem (nodesBase - 1))` (a fixed-stride node arena
followed by an append-only `MinCostFlow.Num` bump heap) with lists of `AuxTree` skeletons.

Each active edge node carries pointers to immutable `L`-limb `Num` blocks storing
canonical flow, forward/backward availabilities, signed cost, and any lazy path-add tag,
and each node maintains subtree `vcnt`, forward/backward cost sums, and directional path
minimum aggregates.
-/

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num

@[expose] public section

theorem intVal_agree_heap {mem₁ mem₂ : ℕ → ℕ} {arenaHi hp h L ptr : ℕ}
    (hag : ∀ a, arenaHi ≤ a → a < hp → mem₂ a = mem₁ a)
    (hlo : arenaHi ≤ ptr) (hhi : ptr + L ≤ hp) :
    intVal mem₂ ptr h L = intVal mem₁ ptr h L :=
  intVal_congr fun i hi => hag (ptr + i) (by omega) (by omega)

theorem optIntVal_agree_heap {mem₁ mem₂ : ℕ → ℕ} {arenaHi hp h L ptr : ℕ}
    (hag : ∀ a, arenaHi ≤ a → a < hp → mem₂ a = mem₁ a)
    (hok : OptNumPtrOk mem₁ arenaHi hp h L ptr) :
    optIntVal mem₂ h L ptr = optIntVal mem₁ h L ptr := by
  rcases hok with rfl | ⟨hlo, hhi, _⟩
  · simp [optIntVal]
  · by_cases hpz : ptr = 0
    · simp [optIntVal, hpz]
    · simp only [optIntVal, hpz, ↓reduceIte]
      exact intVal_agree_heap hag hlo hhi

theorem memAgree_slotZeroOk {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap : ℕ}
    (hag : MemAgreeOn nodesBase (nodesBase + NODE_STRIDE * (cap + 1)) mem₁ mem₂)
    (h0 : SlotZeroOk mem₁ nodesBase) : SlotZeroOk mem₂ nodesBase := by
  intro off hoff
  rw [← hag (nodesBase + off) (by omega) (by unfold NODE_STRIDE at *; omega)]
  exact h0 off hoff

theorem listVcnt_agree_of_mem {mem₁ mem₂ : ℕ → ℕ} {nodesBase : ℕ} {seq : List ℕ}
    (h : ∀ u ∈ seq, nodeField mem₂ nodesBase u OFF_ISV = nodeField mem₁ nodesBase u OFF_ISV) :
    listVcnt mem₂ nodesBase seq = listVcnt mem₁ nodesBase seq := by
  induction seq with
  | nil => rfl
  | cons u us ih =>
      simp only [listVcnt, h u (by simp), ih (fun v hv => h v (by simp [hv]))]

theorem evalInorder_agree_of_list {mem₁ mem₂ : ℕ → ℕ} {nodesBase : ℕ} {t : AuxTree}
    (h : ∀ u ∈ t.toList, nodeField mem₂ nodesBase u OFF_REV = nodeField mem₁ nodesBase u OFF_REV)
    (b : Bool) :
    t.evalInorder (revFlag mem₂ nodesBase) b = t.evalInorder (revFlag mem₁ nodesBase) b := by
  induction t generalizing b with
  | leaf => rfl
  | node y l r ihl ihr =>
      have hy : revFlag mem₂ nodesBase y = revFlag mem₁ nodesBase y := by
        simp [revFlag, h y (by simp [AuxTree.toList])]
      have hl := ihl (fun u hu => h u (by simp [AuxTree.toList, hu]))
      have hr := ihr (fun u hu => h u (by simp [AuxTree.toList, hu]))
      cases b <;> simp only [AuxTree.evalInorder, hy, hl, hr]

/-- If `mem₂` agrees with `mem₁` on all node fields of `t` and all existing heap words `[arenaHi, hp₁)`,
then `evalMemSteps` produces identical step lists on `t`. -/
theorem evalMemSteps_agree {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p pp : ℕ}
    (ht : TreeMemMatch w h L mem₁ nodesBase cap t p pp)
    (hfields : ∀ u ∈ t.toList, ∀ off < NODE_STRIDE,
      nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off)
    (hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₁ (nodesBase - 1) →
      mem₂ a = mem₁ a)
    (flipAcc : Bool) (δAcc : ℤ) :
    evalMemSteps mem₂ nodesBase h L t flipAcc δAcc =
      evalMemSteps mem₁ nodesBase h L t flipAcc δAcc := by
  induction t generalizing p pp flipAcc δAcc with
  | leaf => rfl
  | node x l r ihl ihr =>
      have hf_x : ∀ off < NODE_STRIDE, nodeField mem₂ nodesBase x off = nodeField mem₁ nodesBase x off :=
        hfields x (by simp [AuxTree.toList])
      rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        he1, he0, hcf, hcb, htag1, htag0, _, _, _, _, _, hl, hr⟩
      have hown : nodeOwnRawStep mem₂ nodesBase h L x = nodeOwnRawStep mem₁ nodesBase h L x := by
        simp only [nodeOwnRawStep, hf_x OFF_HASE (by decide)]
        by_cases hhe : nodeField mem₁ nodesBase x OFF_HASE = 0
        · simp [hhe]
        · have hhe1 : nodeField mem₁ nodesBase x OFF_HASE = 1 := by omega
          rcases he1 hhe1 with ⟨hf_ok, haf_ok, hab_ok, hcf_ok, hcb_ok, _⟩
          have heq_f : intVal mem₂ (nodeField mem₂ nodesBase x OFF_FLOW_PTR) h L =
              intVal mem₁ (nodeField mem₁ nodesBase x OFF_FLOW_PTR) h L := by
            rw [hf_x OFF_FLOW_PTR (by decide)]
            exact intVal_agree_heap hheap hf_ok.2.1 hf_ok.2.2.1
          have heq_af : intVal mem₂ (nodeField mem₂ nodesBase x OFF_AF_PTR) h L =
              intVal mem₁ (nodeField mem₁ nodesBase x OFF_AF_PTR) h L := by
            rw [hf_x OFF_AF_PTR (by decide)]
            exact intVal_agree_heap hheap haf_ok.2.1 haf_ok.2.2.1
          have heq_ab : intVal mem₂ (nodeField mem₂ nodesBase x OFF_AB_PTR) h L =
              intVal mem₁ (nodeField mem₁ nodesBase x OFF_AB_PTR) h L := by
            rw [hf_x OFF_AB_PTR (by decide)]
            exact intVal_agree_heap hheap hab_ok.2.1 hab_ok.2.2.1
          have heq_cf : intVal mem₂ (nodeField mem₂ nodesBase x OFF_COST_FWD) h L =
              intVal mem₁ (nodeField mem₁ nodesBase x OFF_COST_FWD) h L := by
            rw [hf_x OFF_COST_FWD (by decide)]
            exact intVal_agree_heap hheap hcf_ok.2.1 hcf_ok.2.2.1
          have heq_cb : intVal mem₂ (nodeField mem₂ nodesBase x OFF_COST_BWD) h L =
              intVal mem₁ (nodeField mem₁ nodesBase x OFF_COST_BWD) h L := by
            rw [hf_x OFF_COST_BWD (by decide)]
            exact intVal_agree_heap hheap hcb_ok.2.1 hcb_ok.2.2.1
          simp only [hhe, ↓reduceIte, hf_x OFF_DIR (by decide), hf_x OFF_EID (by decide),
            hf_x OFF_EU (by decide), hf_x OFF_EV (by decide), heq_f, heq_af, heq_ab, heq_cf, heq_cb]
      have htag : nodeTagInt mem₂ nodesBase h L x = nodeTagInt mem₁ nodesBase h L x := by
        simp only [nodeTagInt, hf_x OFF_HAS_TAG (by decide)]
        by_cases hht : nodeField mem₁ nodesBase x OFF_HAS_TAG = 0
        · simp [hht]
        · have hht1 : nodeField mem₁ nodesBase x OFF_HAS_TAG = 1 := by omega
          rcases (htag1 hht1).1 with ⟨_, hlo, hhi, _⟩
          have heq_t : optIntVal mem₂ h L (nodeField mem₂ nodesBase x OFF_TAG_PTR) =
              optIntVal mem₁ h L (nodeField mem₁ nodesBase x OFF_TAG_PTR) := by
            rw [hf_x OFF_TAG_PTR (by decide)]
            exact optIntVal_agree_heap hheap (Or.inr ⟨hlo, hhi, (htag1 hht1).1.2.2.2⟩)
          simp only [hht, ↓reduceIte, hf_x OFF_TAG_NEG (by decide), heq_t]
      have hrev : revFlag mem₂ nodesBase x = revFlag mem₁ nodesBase x := by
        simp [revFlag, hf_x OFF_REV (by decide)]
      have hl_eq := ihl hl (fun u hu => hfields u (by simp [AuxTree.toList, hu]))
      have hr_eq := ihr hr (fun u hu => hfields u (by simp [AuxTree.toList, hu]))
      cases flipAcc <;> simp only [evalMemSteps, hown, htag, hrev, hl_eq, hr_eq]

/-- If `mem₂` agrees with `mem₁` on all node fields of `t` and all existing heap words `[arenaHi, hp₁)`,
with `hp₁ ≤ hp₂`, then `TreeMemMatch` transfers from `mem₁` to `mem₂`. -/
theorem memAgree_treeMemMatch_of_nodeList {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p pp : ℕ}
    (ht : TreeMemMatch w h L mem₁ nodesBase cap t p pp)
    (hfields : ∀ u ∈ t.toList, ∀ off < NODE_STRIDE,
      nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off)
    (hhp : mem₁ (nodesBase - 1) ≤ mem₂ (nodesBase - 1))
    (hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₁ (nodesBase - 1) →
      mem₂ a = mem₁ a) :
    TreeMemMatch w h L mem₂ nodesBase cap t p pp := by
  induction t generalizing p pp with
  | leaf => trivial
  | node x l r ihl ihr =>
      have hfl : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
          nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off :=
        fun u hu => hfields u (by simp [AuxTree.toList, hu])
      have hfr : ∀ u ∈ r.toList, ∀ off < NODE_STRIDE,
          nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off :=
        fun u hu => hfields u (by simp [AuxTree.toList, hu])
      have hfx : ∀ off < NODE_STRIDE,
          nodeField mem₂ nodesBase x off = nodeField mem₁ nodesBase x off :=
        hfields x (by simp [AuxTree.toList])
      have hsteps_eq := evalMemSteps_agree ht hfields hheap false 0
      have hseq_eq : (AuxTree.node x l r).evalInorder (revFlag mem₂ nodesBase) false =
          (AuxTree.node x l r).evalInorder (revFlag mem₁ nodesBase) false :=
        evalInorder_agree_of_list (fun u hu => hfields u hu OFF_REV (by decide)) false
      rcases ht with ⟨hx1, hx2, hL, hR, hP, hPP, hr, hiv, hhe, hsum, hdir, hht, htn,
        heu, hev, heid, he1, he0, hcf, hcb, htag1, htag0, hm1h, hm2h, hm1_1, hm1_0,
        hagg, hl, hr'⟩
      have hrev_x : revFlag mem₂ nodesBase x = revFlag mem₁ nodesBase x := by
        simp [revFlag, hfx OFF_REV (by decide)]
      have hl_steps := evalMemSteps_agree hl hfl hheap (revFlag mem₁ nodesBase x) 0
      have hr_steps := evalMemSteps_agree hr' hfr hheap (revFlag mem₁ nodesBase x) 0
      have hseq_vcnt : listVcnt mem₂ nodesBase ((AuxTree.node x l r).evalInorder (revFlag mem₁ nodesBase) false) =
          listVcnt mem₁ nodesBase ((AuxTree.node x l r).evalInorder (revFlag mem₁ nodesBase) false) := by
        apply listVcnt_agree_of_mem
        intro u hu
        have hu_t : u ∈ (AuxTree.node x l r).toList :=
          ((AuxTree.node x l r).evalInorder_perm (revFlag mem₁ nodesBase) false).mem_iff.mp hu
        exact hfields u hu_t OFF_ISV (by decide)
      refine ⟨hx1, hx2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ihl hl hfl, ihr hr' hfr⟩
      · simpa [hfx OFF_LEFT (by decide)] using hL
      · simpa [hfx OFF_RIGHT (by decide)] using hR
      · simpa [hfx OFF_PARENT (by decide)] using hP
      · simpa [hfx OFF_PPAR (by decide)] using hPP
      · simpa [hfx OFF_REV (by decide)] using hr
      · simpa [hfx OFF_ISV (by decide)] using hiv
      · simpa [hfx OFF_HASE (by decide)] using hhe
      · simpa [hfx OFF_ISV (by decide), hfx OFF_HASE (by decide)] using hsum
      · simpa [hfx OFF_DIR (by decide)] using hdir
      · simpa [hfx OFF_HAS_TAG (by decide)] using hht
      · simpa [hfx OFF_TAG_NEG (by decide)] using htn
      · simpa [hfx OFF_EU (by decide)] using heu
      · simpa [hfx OFF_EV (by decide)] using hev
      · simpa [hfx OFF_EID (by decide)] using heid
      · intro hhe1
        rw [hfx OFF_HASE (by decide)] at hhe1
        rcases he1 hhe1 with ⟨pf, paf, pab, pcf, pcb, hcb_eq⟩
        rw [hfx OFF_FLOW_PTR (by decide), hfx OFF_AF_PTR (by decide), hfx OFF_AB_PTR (by decide),
          hfx OFF_COST_FWD (by decide), hfx OFF_COST_BWD (by decide)]
        refine ⟨numPtrOk_congr hhp hheap pf, numPtrOk_congr hhp hheap paf,
          numPtrOk_congr hhp hheap pab, numPtrOk_congr hhp hheap pcf,
          numPtrOk_congr hhp hheap pcb, ?_⟩
        rw [intVal_agree_heap hheap pcf.2.1 pcf.2.2.1, intVal_agree_heap hheap pcb.2.1 pcb.2.2.1, hcb_eq]
      · intro hhe0
        rw [hfx OFF_HASE (by decide)] at hhe0
        rw [hfx OFF_DIR (by decide), hfx OFF_FLOW_PTR (by decide), hfx OFF_AF_PTR (by decide),
          hfx OFF_AB_PTR (by decide), hfx OFF_COST_FWD (by decide), hfx OFF_COST_BWD (by decide)]
        exact he0 hhe0
      · rw [hfx OFF_CSUM_FWD (by decide)]
        exact optNumPtrOk_congr hhp hheap hcf
      · rw [hfx OFF_CSUM_BWD (by decide)]
        exact optNumPtrOk_congr hhp hheap hcb
      · intro hht1
        rw [hfx OFF_HAS_TAG (by decide)] at hht1
        rcases htag1 hht1 with ⟨pt, hch, d, hdmod, hfit⟩
        refine ⟨by rw [hfx OFF_TAG_PTR (by decide)]; exact numPtrOk_congr hhp hheap pt, ?_, d, ?_, ?_⟩
        · rcases hch with ⟨hne, hml⟩ | ⟨hne, hmr⟩
          · left; refine ⟨hne, ?_⟩
            have hr_in : l.rootId ∈ l.toList := by cases l with | leaf => exact absurd rfl hne | node _ _ _ => simp [AuxTree.rootId, AuxTree.toList]
            rw [hfl _ hr_in OFF_MIN1_HAS (by decide)]; exact hml
          · right; refine ⟨hne, ?_⟩
            have hr_in : r.rootId ∈ r.toList := by cases r with | leaf => exact absurd rfl hne | node _ _ _ => simp [AuxTree.rootId, AuxTree.toList]
            rw [hfr _ hr_in OFF_MIN1_HAS (by decide)]; exact hmr
        · have htag_eq : nodeTagInt mem₂ nodesBase h L x = nodeTagInt mem₁ nodesBase h L x := by
            simp only [nodeTagInt, hfx OFF_HAS_TAG (by decide), hfx OFF_TAG_NEG (by decide),
              hfx OFF_TAG_PTR (by decide), show nodeField mem₁ nodesBase x OFF_HAS_TAG ≠ 0 by omega, ↓reduceIte]
            rw [optIntVal_agree_heap hheap (Or.inr ⟨pt.2.1, pt.2.2.1, pt.2.2.2⟩)]
          rwa [htag_eq]
        · rwa [hrev_x, hl_steps, hr_steps]
      · intro hht0
        rw [hfx OFF_HAS_TAG (by decide)] at hht0
        rw [hfx OFF_TAG_PTR (by decide), hfx OFF_TAG_NEG (by decide)]
        exact htag0 hht0
      · simpa [hfx OFF_MIN1_HAS (by decide)] using hm1h
      · simpa [hfx OFF_MIN1_HAS (by decide), hfx OFF_MIN2_HAS (by decide)] using hm2h
      · intro hm11
        rw [hfx OFF_MIN1_HAS (by decide)] at hm11
        rcases hm1_1 hm11 with ⟨p1, p2, hf1, hl1, hf2, hl2⟩
        rw [hfx OFF_MIN1_VAL (by decide), hfx OFF_MIN2_VAL (by decide),
          hfx OFF_MIN1_FIRST (by decide), hfx OFF_MIN1_LAST (by decide),
          hfx OFF_MIN2_FIRST (by decide), hfx OFF_MIN2_LAST (by decide)]
        exact ⟨numPtrOk_congr hhp hheap p1, numPtrOk_congr hhp hheap p2, hf1, hl1, hf2, hl2⟩
      · intro hm10
        rw [hfx OFF_MIN1_HAS (by decide)] at hm10
        rw [hfx OFF_MIN1_VAL (by decide), hfx OFF_MIN1_FIRST (by decide), hfx OFF_MIN1_LAST (by decide),
          hfx OFF_MIN2_VAL (by decide), hfx OFF_MIN2_FIRST (by decide), hfx OFF_MIN2_LAST (by decide)]
        exact hm1_0 hm10
      · dsimp only
        rw [hseq_eq, hsteps_eq]
        rcases hagg with ⟨hvc, hsf, hsb, hmiff, hm1, hm2⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hfx OFF_VCNT (by decide), hvc, hseq_vcnt]
        · rw [hfx OFF_CSUM_FWD (by decide), optIntVal_agree_heap hheap hcf, hsf]
        · rw [hfx OFF_CSUM_BWD (by decide), optIntVal_agree_heap hheap hcb, hsb]
        · rw [hfx OFF_MIN1_HAS (by decide)]; exact hmiff
        · simp only [nodeIntMinAgg1, hfx OFF_MIN1_HAS (by decide), hfx OFF_MIN1_VAL (by decide),
            hfx OFF_MIN1_FIRST (by decide), hfx OFF_MIN1_LAST (by decide)]
          have hval_eq : optIntVal mem₂ h L (nodeField mem₁ nodesBase x OFF_MIN1_VAL) =
              optIntVal mem₁ h L (nodeField mem₁ nodesBase x OFF_MIN1_VAL) := by
            by_cases hm11 : nodeField mem₁ nodesBase x OFF_MIN1_HAS = 1
            · rcases hm1_1 hm11 with ⟨p1, _⟩
              exact optIntVal_agree_heap hheap (Or.inr ⟨p1.2.1, p1.2.2.1, p1.2.2.2⟩)
            · have hm10 : nodeField mem₁ nodesBase x OFF_MIN1_HAS = 0 := by omega
              rw [(hm1_0 hm10).1]; simp [optIntVal]
          rw [hval_eq]; exact hm1
        · simp only [nodeIntMinAgg2, hfx OFF_MIN2_HAS (by decide), hfx OFF_MIN2_VAL (by decide),
            hfx OFF_MIN2_FIRST (by decide), hfx OFF_MIN2_LAST (by decide)]
          have hval_eq : optIntVal mem₂ h L (nodeField mem₁ nodesBase x OFF_MIN2_VAL) =
              optIntVal mem₁ h L (nodeField mem₁ nodesBase x OFF_MIN2_VAL) := by
            by_cases hm11 : nodeField mem₁ nodesBase x OFF_MIN1_HAS = 1
            · rcases hm1_1 hm11 with ⟨_, p2, _⟩
              exact optIntVal_agree_heap hheap (Or.inr ⟨p2.2.1, p2.2.2.1, p2.2.2.2⟩)
            · have hm10 : nodeField mem₁ nodesBase x OFF_MIN1_HAS = 0 := by omega
              rw [(hm1_0 hm10).2.2.2.1]; simp [optIntVal]
          rw [hval_eq]; exact hm2

theorem memAgree_treeMemMatch {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap : ℕ}
    (hag_arena : MemAgreeOn nodesBase (nodesBase + NODE_STRIDE * (cap + 1)) mem₁ mem₂)
    (hhp : mem₁ (nodesBase - 1) ≤ mem₂ (nodesBase - 1))
    (hheap : ∀ a, nodesBase + NODE_STRIDE * (cap + 1) ≤ a → a < mem₁ (nodesBase - 1) →
      mem₂ a = mem₁ a)
    {t : AuxTree} {p pp : ℕ} (ht : TreeMemMatch w h L mem₁ nodesBase cap t p pp) :
    TreeMemMatch w h L mem₂ nodesBase cap t p pp := by
  refine memAgree_treeMemMatch_of_nodeList ht ?_ hhp hheap
  intro u hu off hoff
  rcases ht.nodup_perm_mem hu with ⟨hu1, hu2⟩
  symm
  apply hag_arena _ (by omega)
  have : NODE_STRIDE * u + off < NODE_STRIDE * (cap + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    have := Nat.mul_le_mul_left NODE_STRIDE hu2
    omega
  omega

/-- `readAuxTree` depends only on memory in `[nodesBase, nodesBase + NODE_STRIDE * (cap + 1))`. -/
theorem readAuxTree_agree {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap fuel x : ℕ}
    (hag : MemAgreeOn nodesBase (nodesBase + NODE_STRIDE * (cap + 1)) mem₁ mem₂) :
    readAuxTree mem₁ nodesBase cap fuel x = readAuxTree mem₂ nodesBase cap fuel x := by
  induction fuel generalizing x with
  | zero => cases x <;> rfl
  | succ f ih =>
      cases x with
      | zero => rfl
      | succ x' =>
          simp only [readAuxTree]
          by_cases hxle : x' + 1 ≤ cap
          · have hf0 : nodeField mem₁ nodesBase (x' + 1) OFF_LEFT =
                nodeField mem₂ nodesBase (x' + 1) OFF_LEFT :=
              hag _ (by omega) (by
                have := Nat.mul_le_mul_left NODE_STRIDE hxle
                unfold NODE_STRIDE OFF_LEFT at *; omega)
            have hf1 : nodeField mem₁ nodesBase (x' + 1) OFF_RIGHT =
                nodeField mem₂ nodesBase (x' + 1) OFF_RIGHT :=
              hag _ (by omega) (by
                have := Nat.mul_le_mul_left NODE_STRIDE hxle
                unfold NODE_STRIDE OFF_RIGHT at *; omega)
            simp only [hxle, ↓reduceIte, hf0, hf1, ih]
          · simp [hxle]

private theorem nodup_flatMap_disjoint_root {trees : List AuxTree}
    (hnodup : (trees.flatMap AuxTree.toList).Nodup)
    (hne : ∀ t ∈ trees, t ≠ .leaf) :
    (trees.map AuxTree.rootId).Nodup ∧
      ∀ t₁ ∈ trees, ∀ t₂ ∈ trees, t₁.rootId ∈ t₂.toList → t₁ = t₂ := by
  induction trees with
  | nil => simp
  | cons a ts ih =>
      simp only [List.flatMap_cons, List.nodup_append] at hnodup
      rcases hnodup with ⟨ha_nd, hts_nd, hdisj⟩
      have hne_a : a ≠ .leaf := hne a (by simp)
      have hne_ts : ∀ t ∈ ts, t ≠ .leaf := fun t ht => hne t (by simp [ht])
      rcases ih hts_nd hne_ts with ⟨hmap_ts, huniq_ts⟩
      have hroot_mem : ∀ s : AuxTree, s ≠ .leaf → s.rootId ∈ s.toList := by
        intro s hs; cases s with
        | leaf => exact absurd rfl hs
        | node rt _ _ => simp [AuxTree.rootId, AuxTree.toList]
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons, List.mem_map]
        refine ⟨?_, hmap_ts⟩
        rintro ⟨t, ht, hrt⟩
        have hm := hroot_mem t (hne_ts t ht)
        have hmem_bind : t.rootId ∈ ts.flatMap AuxTree.toList :=
          List.mem_flatMap.2 ⟨t, ht, hm⟩
        have ha_mem : a.rootId ∈ a.toList := hroot_mem a hne_a
        rw [hrt] at hmem_bind
        exact hdisj a.rootId ha_mem a.rootId hmem_bind rfl
      · intro t₁ ht₁ t₂ ht₂ hmem
        simp only [List.mem_cons] at ht₁ ht₂
        rcases ht₁ with rfl | ht₁ <;> rcases ht₂ with rfl | ht₂
        · rfl
        · exfalso
          have h1 := hroot_mem t₁ hne_a
          have h2 : t₁.rootId ∈ ts.flatMap AuxTree.toList := List.mem_flatMap.2 ⟨t₂, ht₂, hmem⟩
          exact hdisj t₁.rootId h1 t₁.rootId h2 rfl
        · exfalso
          have h1 : t₁.rootId ∈ ts.flatMap AuxTree.toList :=
            List.mem_flatMap.2 ⟨t₁, ht₁, hroot_mem t₁ (hne_ts t₁ ht₁)⟩
          exact hdisj t₁.rootId hmem t₁.rootId h1 rfl
        · exact huniq_ts t₁ ht₁ t₂ ht₂ hmem

private theorem toList_length_le_flatMap (t : AuxTree) (trees : List AuxTree) (ht : t ∈ trees) :
    t.toList.length ≤ (trees.flatMap AuxTree.toList).length := by
  induction trees with
  | nil => contradiction
  | cons a as ih =>
      simp only [List.flatMap_cons, List.length_append]
      rcases List.mem_cons.1 ht with rfl | htas
      · omega
      · have := ih htas; omega

private theorem sum_toList_length_eq_flatMap (trees : List AuxTree) :
    (trees.map (fun t => t.toList.length)).sum = (trees.flatMap AuxTree.toList).length := by
  induction trees with
  | nil => simp
  | cons t ts ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons, List.length_append, ih]

/-- For a valid `SplayForestOk`, `auxRootIds` is a permutation of `trees.map AuxTree.rootId`,
so `splayMemPhi` equals `K * (trees.map (AuxTree.treePhi vSize)).sum`. -/
theorem splayMemPhi_eq_sum {K w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap : ℕ}
    {trees : List AuxTree} {vSize : ℕ → ℕ}
    (hok : SplayForestOk w h L mem nodesBase cap trees) :
    splayMemPhi K mem nodesBase cap vSize = K * (trees.map (AuxTree.treePhi vSize)).sum := by
  rcases hok with ⟨_, _, _, _, _, _, _, _, hperm, htrees⟩
  have hnodup_all : (trees.flatMap AuxTree.toList).Nodup :=
    hperm.nodup_iff.2 (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h))
  have hne : ∀ t ∈ trees, t ≠ .leaf := fun t ht => (htrees t ht).1
  rcases nodup_flatMap_disjoint_root hnodup_all hne with ⟨hmap_nd, _⟩
  have hnonzero_sub : ∀ s p pp, TreeMemMatch w h L mem nodesBase cap s p pp →
      1 ≤ p → ∀ u ∈ s.toList, nodeField mem nodesBase u OFF_PARENT ≠ 0 := by
    intro s
    induction s with
    | leaf => intro _ _ _ _ _ hu; simp [AuxTree.toList] at hu
    | node y sl sr ihsl ihsr =>
        intro p pp hmy hp u hu
        rcases hmy with ⟨_, _, _, _, hyp, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, hsl, hsr⟩
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
        rcases hu with (hul | rfl) | hur
        · exact ihsl y 0 hsl (by omega) u hul
        · omega
        · exact ihsr y 0 hsr (by omega) u hur
  have hroot_iff : ∀ r, r ∈ auxRootIds mem nodesBase cap ↔ r ∈ trees.map AuxTree.rootId := by
    intro r
    simp only [auxRootIds, List.mem_filter, List.mem_map, decide_eq_true_eq]
    constructor
    · rintro ⟨hr_range, hpar0⟩
      have hmem : r ∈ trees.flatMap AuxTree.toList := hperm.symm.mem_iff.1 (List.mem_map.2 hr_range)
      rw [List.mem_flatMap] at hmem
      rcases hmem with ⟨t, ht_in, hr_in⟩
      rcases htrees t ht_in with ⟨ht_ne, _, hmatch⟩
      cases t with
      | leaf => exact absurd rfl ht_ne
      | node u l rchild =>
          rcases hmatch with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
            _, _, _, _, _, _, _, _, _, _, _, hml, hmr⟩
          simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hr_in
          rcases hr_in with (hrl | rfl) | hrr
          · exact absurd hpar0 (hnonzero_sub l u 0 hml (by omega) r hrl)
          · exact ⟨_, ht_in, rfl⟩
          · exact absurd hpar0 (hnonzero_sub rchild u 0 hmr (by omega) r hrr)
    · rintro ⟨t, ht_in, rfl⟩
      rcases htrees t ht_in with ⟨ht_ne, _, hmatch⟩
      cases t with
      | leaf => exact absurd rfl ht_ne
      | node u l rchild =>
          have hmem_t : u ∈ trees.flatMap AuxTree.toList :=
            List.mem_flatMap.2 ⟨_, ht_in, by simp [AuxTree.toList]⟩
          have hrange := hperm.mem_iff.1 hmem_t
          rcases hmatch with ⟨_, _, _, _, hpar, _⟩
          exact ⟨List.mem_map.1 hrange, hpar⟩
  have haux_nd : (auxRootIds mem nodesBase cap).Nodup :=
    (List.nodup_range.map (fun _ _ h => Nat.succ_inj.1 h)).filter _
  have hroot_perm : (auxRootIds mem nodesBase cap).Perm (trees.map AuxTree.rootId) :=
    (List.perm_ext_iff_of_nodup haux_nd hmap_nd).2 hroot_iff
  have hcount_le : ∀ t ∈ trees, t.countNodes ≤ cap := by
    intro t ht
    have hsub := toList_length_le_flatMap t trees ht
    rw [t.length_toList, hperm.length_eq, List.length_map, List.length_range] at hsub
    exact hsub
  have hmap_eq : trees.map (fun t => (readAuxTree mem nodesBase cap cap t.rootId).treePhi vSize) =
      trees.map (AuxTree.treePhi vSize) := by
    apply List.map_congr_left
    intro t ht
    rw [(htrees t ht).2.2.readAuxTree_eq (hcount_le t ht)]
  have hsum_perm :
      ((auxRootIds mem nodesBase cap).map fun r =>
        (readAuxTree mem nodesBase cap cap r).treePhi vSize).sum =
      (trees.map (AuxTree.treePhi vSize)).sum := by
    have hp := (hroot_perm.map (fun r => (readAuxTree mem nodesBase cap cap r).treePhi vSize)).sum_eq
    rw [hp, List.map_map]
    exact congrArg List.sum hmap_eq
  simp only [splayMemPhi, hsum_perm]

/-- Framing: `splayMemPhi` depends only on `[nodesBase, nodesBase + NODE_STRIDE * (cap + 1))`
when the external weight functions `vSize₁, vSize₂` agree on `1 .. cap`. -/
theorem splayMemPhi_agree {K : ℕ} {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap : ℕ}
    {vSize₁ vSize₂ : ℕ → ℕ}
    (hag : MemAgreeOn nodesBase (nodesBase + NODE_STRIDE * (cap + 1)) mem₁ mem₂)
    (hvs : ∀ y, 1 ≤ y → y ≤ cap → vSize₁ y = vSize₂ y) :
    splayMemPhi K mem₁ nodesBase cap vSize₁ = splayMemPhi K mem₂ nodesBase cap vSize₂ := by
  have hroots : auxRootIds mem₁ nodesBase cap = auxRootIds mem₂ nodesBase cap := by
    simp only [auxRootIds]
    apply List.filter_congr
    intro r hr
    simp only [List.mem_map, List.mem_range] at hr
    rcases hr with ⟨x, hx, rfl⟩
    have hpar : nodeField mem₁ nodesBase (x + 1) OFF_PARENT =
        nodeField mem₂ nodesBase (x + 1) OFF_PARENT := by
      apply hag _ (by omega)
      have := Nat.mul_le_mul_left NODE_STRIDE (by omega : x + 1 ≤ cap)
      unfold NODE_STRIDE OFF_PARENT at *; omega
    simp [hpar]
  have htree_vs : ∀ fuel x,
      (∀ y ∈ (readAuxTree mem₁ nodesBase cap fuel x).toList, 1 ≤ y ∧ y ≤ cap) →
      (readAuxTree mem₁ nodesBase cap fuel x).treePhi vSize₁ =
      (readAuxTree mem₁ nodesBase cap fuel x).treePhi vSize₂ := by
    intro fuel
    induction fuel with
    | zero => intro x _; cases x <;> rfl
    | succ f ih =>
        intro x hb
        cases x with
        | zero => rfl
        | succ x' =>
            by_cases hx : x' + 1 ≤ cap
            · simp only [readAuxTree, hx, ↓reduceIte]
              have hts : ∀ (s : AuxTree), (∀ y ∈ s.toList, 1 ≤ y ∧ y ≤ cap) →
                  s.treeSize vSize₁ = s.treeSize vSize₂ := by
                intro s hs
                induction s with
                | leaf => rfl
                | node y sl sr ihl ihr =>
                    have hy := hs y (by simp [AuxTree.toList])
                    simp only [AuxTree.treeSize,
                      ihl (fun u hu => hs u (by simp [AuxTree.toList, hu])),
                      ihr (fun u hu => hs u (by simp [AuxTree.toList, hu])),
                      hvs y hy.1 hy.2]
              have hfull := hb
              simp only [readAuxTree, hx, ↓reduceIte] at hfull
              have hsl : ∀ y ∈ (readAuxTree mem₁ nodesBase cap f
                  (nodeField mem₁ nodesBase (x' + 1) OFF_LEFT)).toList, 1 ≤ y ∧ y ≤ cap :=
                fun y hy => hfull y (by simp [AuxTree.toList, hy])
              have hsr : ∀ y ∈ (readAuxTree mem₁ nodesBase cap f
                  (nodeField mem₁ nodesBase (x' + 1) OFF_RIGHT)).toList, 1 ≤ y ∧ y ≤ cap :=
                fun y hy => hfull y (by simp [AuxTree.toList, hy])
              simp only [AuxTree.treePhi, AuxTree.rank, hts _ hfull, ih _ hsl, ih _ hsr]
            · simp only [readAuxTree, hx, ↓reduceIte]; rfl
  have hbound : ∀ fuel x y,
      y ∈ (readAuxTree mem₁ nodesBase cap fuel x).toList → 1 ≤ y ∧ y ≤ cap := by
    intro fuel
    induction fuel with
    | zero =>
        intro x y hy
        cases x <;> simp [readAuxTree, AuxTree.toList] at hy
    | succ f ih =>
        intro x y hy
        cases x with
        | zero => simp [readAuxTree, AuxTree.toList] at hy
        | succ x' =>
            by_cases hx : x' + 1 ≤ cap
            · simp only [readAuxTree, hx, ↓reduceIte, AuxTree.toList,
                List.mem_append, List.mem_singleton] at hy
              rcases hy with (hyl | rfl) | hyr
              · exact ih _ y hyl
              · exact ⟨by omega, hx⟩
              · exact ih _ y hyr
            · simp [readAuxTree, hx, AuxTree.toList] at hy
  simp only [splayMemPhi, hroots]
  congr 2
  apply List.map_congr_left
  intro r _
  rw [← readAuxTree_agree hag (fuel := cap) (x := r)]
  exact htree_vs cap r (fun y hy => hbound cap r y hy)

/-- Potential upper bound: `splayMemPhi K mem nodesBase cap vSize ≤ K * cap * Nat.log 2 (maxSize + 2)`
whenever every auxiliary tree satisfies `t.treeSize vSize ≤ maxSize`. -/
theorem splayMemPhi_le {K w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap maxSize : ℕ}
    {trees : List AuxTree} {vSize : ℕ → ℕ}
    (hok : SplayForestOk w h L mem nodesBase cap trees)
    (hsize : ∀ t ∈ trees, t.treeSize vSize ≤ maxSize) :
    splayMemPhi K mem nodesBase cap vSize ≤ K * cap * Nat.log 2 (maxSize + 2) := by
  rw [splayMemPhi_eq_sum hok]
  rcases hok with ⟨_, _, _, _, _, _, _, _, hperm, htrees⟩
  have hsum_phi : (trees.map (AuxTree.treePhi vSize)).sum ≤
      (trees.map AuxTree.countNodes).sum * Nat.log 2 (maxSize + 2) := by
    clear hperm htrees
    induction trees with
    | nil => simp
    | cons t ts ih =>
        have h1 : t.treePhi vSize ≤ t.countNodes * Nat.log 2 (maxSize + 2) :=
          Nat.le_trans (t.treePhi_le vSize)
            (Nat.mul_le_mul_left _ (Nat.log_mono_right (Nat.add_le_add_right (hsize t (by simp)) 2)))
        have h2 := ih (fun s hs => hsize s (by simp [hs]))
        simp only [List.map_cons, List.sum_cons, Nat.add_mul]
        exact Nat.add_le_add h1 h2
  have hcount_sum : (trees.map AuxTree.countNodes).sum = cap := by
    have hl := sum_toList_length_eq_flatMap trees
    have hcongr : trees.map AuxTree.countNodes = trees.map (fun t => t.toList.length) :=
      List.map_congr_left (fun t _ => t.length_toList.symm)
    rw [hcongr, hl, hperm.length_eq, List.length_map, List.length_range]
  rw [hcount_sum] at hsum_phi
  calc
    K * (trees.map (AuxTree.treePhi vSize)).sum
      ≤ K * (cap * Nat.log 2 (maxSize + 2)) := Nat.mul_le_mul_left K hsum_phi
    _ = K * cap * Nat.log 2 (maxSize + 2) := (Nat.mul_assoc K cap _).symm

end

end MinCostFlow.LinkCut.Prog
