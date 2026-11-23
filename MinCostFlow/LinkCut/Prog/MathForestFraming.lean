module

public import MinCostFlow.LinkCut.Prog.MathForestDefs
import Mathlib.Data.List.Perm.Basic

/-!
# Memory framing and `DSRep.Local` for `MathForest` Link-Cut representation

Proves invariance of node fields, auxiliary-tree sequences, `lctAuxParent`, `lctVSize`,
`lctHeavyCount`, `lctPhi`, `evalMemSteps`, `TreeMemMatch`, and full `lctDSRep_local`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section FramingAndLocal

theorem lctFoot_arena {b : ℕ} {x : LctConc}
    {a : ℕ} (hlo : b ≤ a) (hhi : a < lctArenaHi b (lctCap x.n)) :
    lctFoot b x a :=
  Or.inl ⟨hlo, hhi⟩

theorem ptrOffs_lt_stride {off : ℕ} (hoff : off ∈ ptrOffs) : off < NODE_STRIDE := by
  rcases (by simpa [ptrOffs] using hoff :
    off = OFF_FLOW_PTR ∨ off = OFF_AF_PTR ∨ off = OFF_AB_PTR ∨ off = OFF_COST_FWD ∨
    off = OFF_COST_BWD ∨ off = OFF_CSUM_FWD ∨ off = OFF_CSUM_BWD ∨ off = OFF_TAG_PTR ∨
    off = OFF_MIN1_VAL ∨ off = OFF_MIN2_VAL) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  decide

theorem AuxTree.rootId_mem_toList {t : AuxTree} (hne : t ≠ .leaf) : t.rootId ∈ t.toList := by
  cases t with
  | leaf => exact absurd rfl hne
  | node id _ _ => simp [AuxTree.rootId, AuxTree.toList]

theorem nodeField_agree_of_memAgree {b nb cap : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hnb : nb = lctNodesBase b)
    (hag : MemAgreeOn b (lctArenaHi b cap) mem₁ mem₂)
    {u : ℕ} (hu : u ≤ cap) {off : ℕ} (hoff : off < NODE_STRIDE) :
    nodeField mem₂ nb u off = nodeField mem₁ nb u off := by
  symm
  apply hag
  · unfold lctNodesBase at hnb; omega
  · unfold lctArenaHi; rw [← hnb]
    have hmul : NODE_STRIDE * u + off < NODE_STRIDE * (cap + 1) := by
      have : NODE_STRIDE * u ≤ NODE_STRIDE * cap := Nat.mul_le_mul_left _ hu
      rw [Nat.mul_add, Nat.mul_one]
      omega
    omega

theorem readAuxTree_nodes_bounds {mem : ℕ → ℕ} {nb cap fuel x u : ℕ}
    (hu : u ∈ (readAuxTree mem nb cap fuel x).toList) : 1 ≤ u ∧ u ≤ cap := by
  induction fuel generalizing x with
  | zero => cases x <;> simp [readAuxTree, AuxTree.toList] at hu
  | succ f ih =>
      cases x with
      | zero => simp [readAuxTree, AuxTree.toList] at hu
      | succ x' =>
          simp only [readAuxTree] at hu
          split_ifs at hu with hx
          · simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
            rcases hu with (hul | rfl) | hur
            · exact ih hul
            · exact ⟨by omega, hx⟩
            · exact ih hur
          · simp [AuxTree.toList] at hu

theorem freeSlotChain_agree {mem₁ mem₂ : ℕ → ℕ} {nb : ℕ} {hd : ℕ} {free : List ℕ}
    (hnb : ∀ ed ∈ free, nodeField mem₁ nb ed OFF_EU = nodeField mem₂ nb ed OFF_EU) :
    FreeSlotChain mem₁ nb hd free ↔ FreeSlotChain mem₂ nb hd free := by
  induction free generalizing hd with
  | nil => simp [FreeSlotChain]
  | cons ed rest ih =>
      simp only [FreeSlotChain]
      have heu := hnb ed (by simp)
      have ihr := ih (fun e he => hnb e (by simp [he])) (hd := nodeField mem₁ nb ed OFF_EU)
      constructor
      · rintro ⟨rfl, hrest⟩
        refine ⟨rfl, ?_⟩
        rw [← heu]
        exact ihr.mp hrest
      · rintro ⟨rfl, hrest⟩
        refine ⟨rfl, ?_⟩
        apply ihr.mpr
        rw [heu]
        exact hrest

private theorem hag_nodeField {mem₁ mem₂ : ℕ → ℕ} {nb cap : ℕ}
    (hag : MemAgreeOn nb (nb + NODE_STRIDE * (cap + 1)) mem₁ mem₂)
    (u off : ℕ) (hu : u ≤ cap) (hoff : off < NODE_STRIDE) :
    nodeField mem₂ nb u off = nodeField mem₁ nb u off := by
  symm
  apply hag
  · omega
  · have : NODE_STRIDE * u ≤ NODE_STRIDE * cap := Nat.mul_le_mul_left _ hu
    rw [Nat.mul_add, Nat.mul_one]
    omega

private theorem mem_auxRootIds_bounds {mem : ℕ → ℕ} {nb cap r : ℕ}
    (hr : r ∈ auxRootIds mem nb cap) : r ≤ cap := by
  unfold auxRootIds at hr
  simp only [List.mem_filter, List.mem_map, List.mem_range] at hr
  rcases hr with ⟨⟨x, hx, rfl⟩, _⟩
  omega

theorem lctTreeSeq_agree {mem₁ mem₂ : ℕ → ℕ} {nb cap r : ℕ}
    (hag : MemAgreeOn nb (nb + NODE_STRIDE * (cap + 1)) mem₁ mem₂) :
    lctTreeSeq mem₂ nb cap r = lctTreeSeq mem₁ nb cap r := by
  unfold lctTreeSeq
  rw [readAuxTree_agree hag]
  apply AuxTree.evalInorder_agree
  intro u hu
  simp [revFlag, hag_nodeField hag u OFF_REV (readAuxTree_nodes_bounds hu).2 (by decide)]

theorem auxRootIds_agree {mem₁ mem₂ : ℕ → ℕ} {nb cap : ℕ}
    (hag : MemAgreeOn nb (nb + NODE_STRIDE * (cap + 1)) mem₁ mem₂) :
    auxRootIds mem₂ nb cap = auxRootIds mem₁ nb cap := by
  unfold auxRootIds
  apply List.filter_congr
  intro r hr
  simp only [List.mem_map, List.mem_range] at hr
  rcases hr with ⟨x, hx, rfl⟩
  simp [hag_nodeField hag (x + 1) OFF_PARENT (by omega) (by decide)]

theorem lctAuxParent_agree {mem₁ mem₂ : ℕ → ℕ} {nb cap : ℕ}
    (hag : MemAgreeOn nb (nb + NODE_STRIDE * (cap + 1)) mem₁ mem₂) (u : ℕ) :
    lctAuxParent mem₂ nb cap u = lctAuxParent mem₁ nb cap u := by
  unfold lctAuxParent
  rw [auxRootIds_agree hag]
  have htree : ∀ r ∈ auxRootIds mem₁ nb cap,
      treeParentEntry mem₂ nb cap r u = treeParentEntry mem₁ nb cap r u := by
    intro r hr
    simp only [treeParentEntry, lctTreeSeq_agree hag,
      hag_nodeField hag r OFF_PPAR (mem_auxRootIds_bounds hr) (by decide)]
  have go : ∀ rs : List ℕ, (∀ r ∈ rs, treeParentEntry mem₂ nb cap r u = treeParentEntry mem₁ nb cap r u) →
      rs.findSome? (fun r => treeParentEntry mem₂ nb cap r u) =
      rs.findSome? (fun r => treeParentEntry mem₁ nb cap r u) := by
    intro rs hrs
    induction rs with
    | nil => simp
    | cons r rs ih =>
        simp only [List.findSome?]
        rw [hrs r (by simp), ih (fun r' hr' => hrs r' (by simp [hr']))]
  rw [go _ htree]

theorem lctRepSize_agree {mem₁ mem₂ : ℕ → ℕ} {nb cap : ℕ}
    (hag : MemAgreeOn nb (nb + NODE_STRIDE * (cap + 1)) mem₁ mem₂) (y : ℕ) :
    lctRepSize mem₂ nb cap y = lctRepSize mem₁ nb cap y := by
  unfold lctRepSize
  congr 1
  apply List.filter_congr
  intro u _
  have hpar : lctAuxParent mem₂ nb cap = lctAuxParent mem₁ nb cap := funext (lctAuxParent_agree hag)
  simp [reachesIn, hpar]

theorem lctVSize_agree {mem₁ mem₂ : ℕ → ℕ} {nb cap : ℕ}
    (hag : MemAgreeOn nb (nb + NODE_STRIDE * (cap + 1)) mem₁ mem₂) (y : ℕ) :
    lctVSize mem₂ nb cap y = lctVSize mem₁ nb cap y := by
  unfold lctVSize
  rw [auxRootIds_agree hag]
  have hfilt : (auxRootIds mem₁ nb cap).filter (fun r => decide (nodeField mem₂ nb r OFF_PPAR = y)) =
      (auxRootIds mem₁ nb cap).filter (fun r => decide (nodeField mem₁ nb r OFF_PPAR = y)) :=
    List.filter_congr fun r hr => by
      simp [hag_nodeField hag r OFF_PPAR (mem_auxRootIds_bounds hr) (by decide)]
  rw [hfilt]
  congr 1
  apply List.map_congr_left
  intro r _
  simp [dashedChildSize, lctTreeSeq_agree hag, lctRepSize_agree hag]

theorem lctHeavyCount_agree {mem₁ mem₂ : ℕ → ℕ} {nb cap : ℕ}
    (hag : MemAgreeOn nb (nb + NODE_STRIDE * (cap + 1)) mem₁ mem₂) :
    lctHeavyCount mem₂ nb cap = lctHeavyCount mem₁ nb cap := by
  unfold lctHeavyCount
  rw [auxRootIds_agree hag]
  congr 1
  apply List.filter_congr
  intro r hr
  simp only [isHeavyRoot, hag_nodeField hag r OFF_PPAR (mem_auxRootIds_bounds hr) (by decide),
    lctTreeSeq_agree hag]
  cases lctTreeSeq mem₁ nb cap r with
  | nil => simp
  | cons hd _ => simp [lctRepSize_agree hag]

theorem lctPhi_agree {L : ℕ} {mem₁ mem₂ : ℕ → ℕ} {b n : ℕ}
    (hag : MemAgreeOn (lctNodesBase b) (lctArenaHi b (lctCap n)) mem₁ mem₂) :
    lctPhi L mem₂ b n = lctPhi L mem₁ b n := by
  have hag' : MemAgreeOn (lctNodesBase b) (lctNodesBase b + NODE_STRIDE * (lctCap n + 1)) mem₁ mem₂ := by
    simpa [lctArenaHi] using hag
  have hag_symm : MemAgreeOn (lctNodesBase b) (lctNodesBase b + NODE_STRIDE * (lctCap n + 1)) mem₂ mem₁ :=
    fun a ha1 ha2 => (hag' a ha1 ha2).symm
  unfold lctPhi
  have hs := splayMemPhi_agree (K := K_SPLAY_STEP L) hag_symm (fun y _ _ => lctVSize_agree hag' y)
  have hh := lctHeavyCount_agree hag'
  rw [hs, hh]

private theorem numPtrOk_agree_ptr {mem₁ mem₂ : ℕ → ℕ} {arenaHi hp h L ptr : ℕ}
    (hblk : ∀ i < L, mem₂ (ptr + i) = mem₁ (ptr + i))
    (hok : NumPtrOk mem₁ arenaHi hp h L ptr) :
    NumPtrOk mem₂ arenaHi hp h L ptr :=
  ⟨hok.1, hok.2.1, hok.2.2.1, valid_agree_block hblk hok.2.2.2⟩

private theorem optIntVal_agree_ptr {mem₁ mem₂ : ℕ → ℕ} {h L ptr : ℕ}
    (hpt : ptr = 0 ∨ ∀ i < L, mem₂ (ptr + i) = mem₁ (ptr + i)) :
    optIntVal mem₂ h L ptr = optIntVal mem₁ h L ptr := by
  rcases hpt with rfl | hblk
  · simp [optIntVal]
  · by_cases hp : ptr = 0
    · simp [optIntVal, hp]
    · simp only [optIntVal, hp, ↓reduceIte]
      exact intVal_agree_block hblk

private theorem optNumPtrOk_agree_ptr {mem₁ mem₂ : ℕ → ℕ} {arenaHi hp h L ptr : ℕ}
    (hpt : ptr = 0 ∨ ∀ i < L, mem₂ (ptr + i) = mem₁ (ptr + i))
    (hok : OptNumPtrOk mem₁ arenaHi hp h L ptr) :
    OptNumPtrOk mem₂ arenaHi hp h L ptr := by
  rcases hok with rfl | ⟨h1, h2, hval⟩
  · exact Or.inl rfl
  · rcases hpt with h0 | hblk
    · subst h0; exact Or.inl rfl
    · exact Or.inr ⟨h1, h2, valid_agree_block hblk hval⟩

private theorem nodeOwnRawStep_agree_ptrs {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap x p pp : ℕ}
    {l r : AuxTree}
    (ht : TreeMemMatch w h L mem₁ nodesBase cap (.node x l r) p pp)
    (hf_x : ∀ off < NODE_STRIDE, nodeField mem₂ nodesBase x off = nodeField mem₁ nodesBase x off)
    (hp_x : ∀ off ∈ ptrOffs,
      let ptr := nodeField mem₁ nodesBase x off
      ptr = 0 ∨ ∀ i < L, mem₂ (ptr + i) = mem₁ (ptr + i)) :
    nodeOwnRawStep mem₂ nodesBase h L x = nodeOwnRawStep mem₁ nodesBase h L x := by
  rcases ht with ⟨_, _, _, _, _, _, _, _, hhe_le, _, _, _, _, _, _, _, he1, _⟩
  simp only [nodeOwnRawStep, hf_x OFF_HASE (by decide)]
  by_cases hhe : nodeField mem₁ nodesBase x OFF_HASE = 0
  · simp [hhe]
  · have hhe1 : nodeField mem₁ nodesBase x OFF_HASE = 1 := by omega
    rcases he1 hhe1 with ⟨hf_ok, haf_ok, hab_ok, hcf_ok, hcb_ok, _⟩
    have heq_of : ∀ {off}, off ∈ ptrOffs →
        NumPtrOk mem₁ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₁ (nodesBase - 1)) h L
          (nodeField mem₁ nodesBase x off) →
        intVal mem₂ (nodeField mem₂ nodesBase x off) h L =
          intVal mem₁ (nodeField mem₁ nodesBase x off) h L := fun hoff hn => by
      rw [hf_x _ (ptrOffs_lt_stride hoff)]
      exact intVal_agree_block ((hp_x _ hoff).resolve_left hn.1)
    simp only [hhe, ↓reduceIte, hf_x OFF_DIR (by decide), hf_x OFF_EID (by decide),
      hf_x OFF_EU (by decide), hf_x OFF_EV (by decide),
      heq_of (by simp [ptrOffs]) hf_ok, heq_of (by simp [ptrOffs]) haf_ok,
      heq_of (by simp [ptrOffs]) hab_ok, heq_of (by simp [ptrOffs]) hcf_ok,
      heq_of (by simp [ptrOffs]) hcb_ok]

theorem evalMemSteps_agree_ptrs {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p pp : ℕ}
    (ht : TreeMemMatch w h L mem₁ nodesBase cap t p pp)
    (hfields : ∀ u ∈ t.toList, ∀ off < NODE_STRIDE,
      nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off)
    (hptrs : ∀ u ∈ t.toList, ∀ off ∈ ptrOffs,
      let ptr := nodeField mem₁ nodesBase u off
      ptr = 0 ∨ ∀ i < L, mem₂ (ptr + i) = mem₁ (ptr + i))
    (flipAcc : Bool) (δAcc : ℤ) :
    evalMemSteps mem₂ nodesBase h L t flipAcc δAcc =
      evalMemSteps mem₁ nodesBase h L t flipAcc δAcc := by
  induction t generalizing p pp flipAcc δAcc with
  | leaf => rfl
  | node x l r ihl ihr =>
      have hx_t : x ∈ (AuxTree.node x l r).toList := by simp [AuxTree.toList]
      have hf_x := hfields x hx_t
      have hp_x := hptrs x hx_t
      have hown := nodeOwnRawStep_agree_ptrs ht hf_x hp_x
      rcases ht with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      have htag : nodeTagInt mem₂ nodesBase h L x = nodeTagInt mem₁ nodesBase h L x := by
        simp only [nodeTagInt, hf_x OFF_HAS_TAG (by decide)]
        by_cases hht : nodeField mem₁ nodesBase x OFF_HAS_TAG = 0
        · simp [hht]
        · rw [hf_x OFF_TAG_PTR (by decide), hf_x OFF_TAG_NEG (by decide),
            optIntVal_agree_ptr (hp_x OFF_TAG_PTR (by simp [ptrOffs]))]
      have hrev : revFlag mem₂ nodesBase x = revFlag mem₁ nodesBase x := by
        simp [revFlag, hf_x OFF_REV (by decide)]
      have hl_eq := ihl hl (fun u hu => hfields u (by simp [AuxTree.toList, hu]))
        (fun u hu => hptrs u (by simp [AuxTree.toList, hu]))
      have hr_eq := ihr hr (fun u hu => hfields u (by simp [AuxTree.toList, hu]))
        (fun u hu => hptrs u (by simp [AuxTree.toList, hu]))
      cases flipAcc <;> simp only [evalMemSteps, hown, htag, hrev, hl_eq, hr_eq]

theorem memAgree_treeMemMatch_of_ptrs {w h L : ℕ} {mem₁ mem₂ : ℕ → ℕ} {nodesBase cap : ℕ}
    {t : AuxTree} {p pp : ℕ}
    (ht : TreeMemMatch w h L mem₁ nodesBase cap t p pp)
    (hhp : mem₂ (nodesBase - 1) = mem₁ (nodesBase - 1))
    (hfields : ∀ u ∈ t.toList, ∀ off < NODE_STRIDE,
      nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off)
    (hptrs : ∀ u ∈ t.toList, ∀ off ∈ ptrOffs,
      let ptr := nodeField mem₁ nodesBase u off
      ptr = 0 ∨ ∀ i < L, mem₂ (ptr + i) = mem₁ (ptr + i)) :
    TreeMemMatch w h L mem₂ nodesBase cap t p pp := by
  induction t generalizing p pp with
  | leaf => trivial
  | node x l r ihl ihr =>
      have hx_t : x ∈ (AuxTree.node x l r).toList := by simp [AuxTree.toList]
      have hf_x := hfields x hx_t
      have hp_x := hptrs x hx_t
      have hfl : ∀ u ∈ l.toList, ∀ off < NODE_STRIDE,
          nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off :=
        fun u hu => hfields u (by simp [AuxTree.toList, hu])
      have hfr : ∀ u ∈ r.toList, ∀ off < NODE_STRIDE,
          nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off :=
        fun u hu => hfields u (by simp [AuxTree.toList, hu])
      have hpl : ∀ u ∈ l.toList, ∀ off ∈ ptrOffs,
          let ptr := nodeField mem₁ nodesBase u off
          ptr = 0 ∨ ∀ i < L, mem₂ (ptr + i) = mem₁ (ptr + i) :=
        fun u hu => hptrs u (by simp [AuxTree.toList, hu])
      have hpr : ∀ u ∈ r.toList, ∀ off ∈ ptrOffs,
          let ptr := nodeField mem₁ nodesBase u off
          ptr = 0 ∨ ∀ i < L, mem₂ (ptr + i) = mem₁ (ptr + i) :=
        fun u hu => hptrs u (by simp [AuxTree.toList, hu])
      have hsteps_eq := evalMemSteps_agree_ptrs ht hfields hptrs false 0
      have hseq_eq : (AuxTree.node x l r).evalInorder (revFlag mem₂ nodesBase) false =
          (AuxTree.node x l r).evalInorder (revFlag mem₁ nodesBase) false :=
        evalInorder_agree_of_list (fun u hu => hfields u hu OFF_REV (by decide)) false
      rcases ht with ⟨hx1, hx2, hL, hR, hP, hPP, hr, hiv, hhe, hsum, hdir, hht, htn,
        heu, hev, heid, he1, he0, hcf, hcb, htag1, htag0, hm1h, hm2h, hm1_1, hm1_0,
        hagg, hl, hr'⟩
      have hrev_x : revFlag mem₂ nodesBase x = revFlag mem₁ nodesBase x := by
        simp [revFlag, hf_x OFF_REV (by decide)]
      have hl_steps := evalMemSteps_agree_ptrs hl hfl hpl (revFlag mem₁ nodesBase x) 0
      have hr_steps := evalMemSteps_agree_ptrs hr' hfr hpr (revFlag mem₁ nodesBase x) 0
      have hseq_vcnt : listVcnt mem₂ nodesBase ((AuxTree.node x l r).evalInorder (revFlag mem₁ nodesBase) false) =
          listVcnt mem₁ nodesBase ((AuxTree.node x l r).evalInorder (revFlag mem₁ nodesBase) false) := by
        apply listVcnt_agree_of_mem
        intro u hu
        have hu_t : u ∈ (AuxTree.node x l r).toList :=
          ((AuxTree.node x l r).evalInorder_perm (revFlag mem₁ nodesBase) false).mem_iff.mp hu
        exact hfields u hu_t OFF_ISV (by decide)
      have hnz : ∀ {ptr}, NumPtrOk mem₁ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₁ (nodesBase - 1)) h L ptr →
          ptr ≠ 0 := by
        intro ptr hn
        have hpos : 0 < nodesBase + NODE_STRIDE * (cap + 1) := by unfold NODE_STRIDE; omega
        have := hn.1; omega
      have hnum_off : ∀ off ∈ ptrOffs,
          NumPtrOk mem₁ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₁ (nodesBase - 1)) h L
            (nodeField mem₁ nodesBase x off) →
          NumPtrOk mem₂ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₂ (nodesBase - 1)) h L
            (nodeField mem₂ nodesBase x off) := by
        intro off hoff hn
        rw [hf_x off (ptrOffs_lt_stride hoff), hhp]
        exact numPtrOk_agree_ptr ((hp_x off hoff).resolve_left (hnz hn)) hn
      have hopt_num_off : ∀ off ∈ ptrOffs,
          OptNumPtrOk mem₁ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₁ (nodesBase - 1)) h L
            (nodeField mem₁ nodesBase x off) →
          OptNumPtrOk mem₂ (nodesBase + NODE_STRIDE * (cap + 1)) (mem₂ (nodesBase - 1)) h L
            (nodeField mem₂ nodesBase x off) := by
        intro off hoff hn
        rcases hn with h0 | ⟨h1, h2, hv⟩
        · rw [hf_x off (ptrOffs_lt_stride hoff)]; exact Or.inl h0
        · rw [hf_x off (ptrOffs_lt_stride hoff), hhp]
          by_cases hpz : nodeField mem₁ nodesBase x off = 0
          · exact Or.inl hpz
          · exact Or.inr ⟨h1, h2, valid_agree_block ((hp_x off hoff).resolve_left hpz) hv⟩
      refine ⟨hx1, hx2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ihl hl hfl hpl, ihr hr' hfr hpr⟩
      · rw [hf_x OFF_LEFT (by decide)]; exact hL
      · rw [hf_x OFF_RIGHT (by decide)]; exact hR
      · rw [hf_x OFF_PARENT (by decide)]; exact hP
      · rw [hf_x OFF_PPAR (by decide)]; exact hPP
      · rw [hf_x OFF_REV (by decide)]; exact hr
      · rw [hf_x OFF_ISV (by decide)]; exact hiv
      · rw [hf_x OFF_HASE (by decide)]; exact hhe
      · rw [hf_x OFF_ISV (by decide), hf_x OFF_HASE (by decide)]; exact hsum
      · rw [hf_x OFF_DIR (by decide)]; exact hdir
      · rw [hf_x OFF_HAS_TAG (by decide)]; exact hht
      · rw [hf_x OFF_TAG_NEG (by decide)]; exact htn
      · rw [hf_x OFF_EU (by decide)]; exact heu
      · rw [hf_x OFF_EV (by decide)]; exact hev
      · rw [hf_x OFF_EID (by decide)]; exact heid
      · intro hhe1
        rw [hf_x OFF_HASE (by decide)] at hhe1
        rcases he1 hhe1 with ⟨hf, haf, hab, hcf', hcb', hwrap⟩
        refine ⟨hnum_off OFF_FLOW_PTR (by simp [ptrOffs]) hf,
          hnum_off OFF_AF_PTR (by simp [ptrOffs]) haf,
          hnum_off OFF_AB_PTR (by simp [ptrOffs]) hab,
          hnum_off OFF_COST_FWD (by simp [ptrOffs]) hcf',
          hnum_off OFF_COST_BWD (by simp [ptrOffs]) hcb', ?_⟩
        rw [hf_x OFF_COST_BWD (by decide), hf_x OFF_COST_FWD (by decide)]
        rw [intVal_agree_block ((hp_x OFF_COST_BWD (by simp [ptrOffs])).resolve_left (hnz hcb'))]
        rw [intVal_agree_block ((hp_x OFF_COST_FWD (by simp [ptrOffs])).resolve_left (hnz hcf'))]
        exact hwrap
      · intro hhe0
        rw [hf_x OFF_HASE (by decide)] at hhe0
        rcases he0 hhe0 with ⟨hd, hf, haf, hab, hcf', hcb'⟩
        rw [hf_x OFF_DIR (by decide), hf_x OFF_FLOW_PTR (by decide),
          hf_x OFF_AF_PTR (by decide), hf_x OFF_AB_PTR (by decide),
          hf_x OFF_COST_FWD (by decide), hf_x OFF_COST_BWD (by decide)]
        exact ⟨hd, hf, haf, hab, hcf', hcb'⟩
      · exact hopt_num_off OFF_CSUM_FWD (by simp [ptrOffs]) hcf
      · exact hopt_num_off OFF_CSUM_BWD (by simp [ptrOffs]) hcb
      · intro hht1
        rw [hf_x OFF_HAS_TAG (by decide)] at hht1
        rcases htag1 hht1 with ⟨htok, hch, d, hmod, hfit⟩
        refine ⟨hnum_off OFF_TAG_PTR (by simp [ptrOffs]) htok, ?_, d, ?_, ?_⟩
        · rcases hch with ⟨hl_ne, hlm⟩ | ⟨hr_ne, hrm⟩
          · exact Or.inl ⟨hl_ne, by
              rw [hfl l.rootId (by cases l <;> simp_all [AuxTree.rootId, AuxTree.toList]) OFF_MIN1_HAS (by decide)]
              exact hlm⟩
          · exact Or.inr ⟨hr_ne, by
              rw [hfr r.rootId (by cases r <;> simp_all [AuxTree.rootId, AuxTree.toList]) OFF_MIN1_HAS (by decide)]
              exact hrm⟩
        · simp only [nodeTagInt, hf_x OFF_HAS_TAG (by decide), hht1, hf_x OFF_TAG_NEG (by decide),
            hf_x OFF_TAG_PTR (by decide),
            optIntVal_agree_ptr (hp_x OFF_TAG_PTR (by simp [ptrOffs]))] at hmod ⊢
          exact hmod
        · rw [hrev_x, hl_steps, hr_steps]; exact hfit
      · intro hht0
        rw [hf_x OFF_HAS_TAG (by decide)] at hht0
        rcases htag0 hht0 with ⟨hp0, hn0⟩
        rw [hf_x OFF_TAG_PTR (by decide), hf_x OFF_TAG_NEG (by decide)]
        exact ⟨hp0, hn0⟩
      · rw [hf_x OFF_MIN1_HAS (by decide)]; exact hm1h
      · rw [hf_x OFF_MIN2_HAS (by decide), hf_x OFF_MIN1_HAS (by decide)]; exact hm2h
      · intro hm11
        rw [hf_x OFF_MIN1_HAS (by decide)] at hm11
        rcases hm1_1 hm11 with ⟨hv1, hv2, hf1, hl1, hf2, hl2⟩
        refine ⟨hnum_off OFF_MIN1_VAL (by simp [ptrOffs]) hv1,
          hnum_off OFF_MIN2_VAL (by simp [ptrOffs]) hv2, ?_, ?_, ?_, ?_⟩
        · rw [hf_x OFF_MIN1_FIRST (by decide)]; exact hf1
        · rw [hf_x OFF_MIN1_LAST (by decide)]; exact hl1
        · rw [hf_x OFF_MIN2_FIRST (by decide)]; exact hf2
        · rw [hf_x OFF_MIN2_LAST (by decide)]; exact hl2
      · intro hm10
        rw [hf_x OFF_MIN1_HAS (by decide)] at hm10
        rcases hm1_0 hm10 with ⟨a, b', c, d, e, f⟩
        rw [hf_x OFF_MIN1_VAL (by decide), hf_x OFF_MIN1_FIRST (by decide),
          hf_x OFF_MIN1_LAST (by decide), hf_x OFF_MIN2_VAL (by decide),
          hf_x OFF_MIN2_FIRST (by decide), hf_x OFF_MIN2_LAST (by decide)]
        exact ⟨a, b', c, d, e, f⟩
      · dsimp only
        rw [hseq_eq, hsteps_eq, hseq_vcnt]
        rcases hagg with ⟨hvc, hsf, hsb, hm1_iff, hagg1, hagg2⟩
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hf_x OFF_VCNT (by decide)]; exact hvc
        · rw [hf_x OFF_CSUM_FWD (by decide),
            optIntVal_agree_ptr (hp_x OFF_CSUM_FWD (by simp [ptrOffs]))]; exact hsf
        · rw [hf_x OFF_CSUM_BWD (by decide),
            optIntVal_agree_ptr (hp_x OFF_CSUM_BWD (by simp [ptrOffs]))]; exact hsb
        · rw [hf_x OFF_MIN1_HAS (by decide)]; exact hm1_iff
        · simp only [nodeIntMinAgg1, hf_x OFF_MIN1_HAS (by decide), hf_x OFF_MIN1_VAL (by decide),
            hf_x OFF_MIN1_FIRST (by decide), hf_x OFF_MIN1_LAST (by decide),
            optIntVal_agree_ptr (hp_x OFF_MIN1_VAL (by simp [ptrOffs]))]
          exact hagg1
        · simp only [nodeIntMinAgg2, hf_x OFF_MIN2_HAS (by decide), hf_x OFF_MIN2_VAL (by decide),
            hf_x OFF_MIN2_FIRST (by decide), hf_x OFF_MIN2_LAST (by decide),
            optIntVal_agree_ptr (hp_x OFF_MIN2_VAL (by simp [ptrOffs]))]
          exact hagg2

/-- `lctDSRep w h L P` satisfies `DSRep.Local`: representation and potential depend
only on the cells in `lctFoot b x`. -/
theorem lctDSRep_local (w h L P : ℕ) : (lctDSRep w h L P).Local := by
  intro b F x mem₁ mem₂ hag_foot
  refine ⟨?_, ?_⟩
  · intro hrep
    rcases hrep with ⟨hh_pos, hwh, hval, hfits, hxn, hhi_arena, hhi_pos, hhi_foot,
      hreg_bounds, hn, hcap, hL_eq, hP_eq, hhp_lo, hhp_hi, hhp_w,
      hedge_snd, hedge_all, hfc, hfree_ok, hslot0, hperm_trees, htrees_ok,
      hv_ok, hae_ok, haux_ok, hsub_ok, hptr_foot⟩
    have hag_full : MemAgreeOn b (lctArenaHi b (lctCap F.n)) mem₁ mem₂ := fun a ha1 ha2 =>
      hag_foot a (lctFoot_arena ha1 (by rw [hxn]; exact ha2))
    have hag_nb : MemAgreeOn (lctNodesBase b) (lctArenaHi b (lctCap F.n)) mem₁ mem₂ :=
      fun a ha1 ha2 => hag_full a (by unfold lctNodesBase at ha1; omega) ha2
    have hnb_arena : MemAgreeOn (lctNodesBase b)
        (lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1)) mem₁ mem₂ := by
      simpa [lctArenaHi] using hag_nb
    have hhdr : ∀ off < LCT_HDR_SIZE, mem₂ (b + off) = mem₁ (b + off) := by
      intro off hoff
      symm
      apply hag_full
      · omega
      · unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE at *; omega
    have hfield : ∀ u ≤ lctCap F.n, ∀ off < NODE_STRIDE,
        nodeField mem₂ (lctNodesBase b) u off = nodeField mem₁ (lctNodesBase b) u off :=
      fun u hu off hoff =>
        nodeField_agree_of_memAgree rfl hag_full hu hoff
    have hptrs_all : ∀ u ≤ lctCap F.n, ∀ off ∈ ptrOffs,
        let ptr := nodeField mem₁ (lctNodesBase b) u off
        ptr = 0 ∨ ∀ i < L, mem₂ (ptr + i) = mem₁ (ptr + i) := by
      intro u hu off hoff
      rcases hptr_foot u (hxn ▸ hu) off hoff with h0 | ⟨_, _, hpf⟩
      · exact Or.inl h0
      · refine Or.inr fun i hi => ?_
        have hlt : i < max 1 L := lt_of_lt_of_le hi (le_max_right 1 L)
        exact (hag_foot (nodeField mem₁ (lctNodesBase b) u off + i)
          (hpf _ (by omega) (by omega))).symm
    have hhp_eq : mem₂ (lctNodesBase b - 1) = mem₁ (lctNodesBase b - 1) := by
      have : lctNodesBase b - 1 = b + LCT_HDR_HP := by
        unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_HP; omega
      rw [this]
      exact hhdr LCT_HDR_HP (by unfold LCT_HDR_HP LCT_HDR_SIZE; omega)
    have hhp_b5 : mem₂ (b + LCT_HDR_HP) = mem₁ (b + LCT_HDR_HP) :=
      hhdr LCT_HDR_HP (by unfold LCT_HDR_HP LCT_HDR_SIZE; omega)
    have hpar_eq : ∀ u, lctAuxParent mem₂ (lctNodesBase b) (lctCap F.n) u =
        lctAuxParent mem₁ (lctNodesBase b) (lctCap F.n) u :=
      lctAuxParent_agree hnb_arena
    have ht_mem_le : ∀ {t : AuxTree}, t ∈ x.trees → ∀ u ∈ t.toList, u ≤ lctCap F.n := by
      intro t ht u hu
      have hm := hperm_trees.mem_iff.1 (List.mem_flatMap.2 ⟨t, ht, hu⟩)
      rcases List.mem_map.1 hm with ⟨y, hy, rfl⟩
      rw [List.mem_range] at hy
      omega
    refine ⟨hh_pos, hwh, hval, hfits, hxn, hhi_arena, hhi_pos, hhi_foot, hreg_bounds,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hedge_snd, hedge_all, ?_, ?_, ?_, hperm_trees, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hhdr LCT_HDR_N (by unfold LCT_HDR_N LCT_HDR_SIZE; omega)]; exact hn
    · rw [hhdr LCT_HDR_CAP (by unfold LCT_HDR_CAP LCT_HDR_SIZE; omega)]; exact hcap
    · rw [hhdr LCT_HDR_L (by unfold LCT_HDR_L LCT_HDR_SIZE; omega)]; exact hL_eq
    · rw [hhdr LCT_HDR_P (by unfold LCT_HDR_P LCT_HDR_SIZE; omega)]; exact hP_eq
    · rw [hhp_b5]; exact hhp_lo
    · rw [hhp_b5]; exact hhp_hi
    · rw [hhp_b5]; exact hhp_w
    · rw [hhdr LCT_HDR_FREE (by unfold LCT_HDR_FREE LCT_HDR_SIZE; omega)]
      refine (freeSlotChain_agree (fun ed hed => ?_)).mp hfc
      have hed_le : ed ≤ lctCap F.n := (hfree_ok ed hed).2.1
      exact (hfield ed hed_le OFF_EU (by decide)).symm
    · intro ed hed
      rcases hfree_ok ed hed with ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨h1, h2, h3, by rw [hfield ed h2 OFF_PPAR (by decide)]; exact h4,
        by rw [hfield ed h2 OFF_ISV (by decide)]; exact h5,
        by rw [hfield ed h2 OFF_HASE (by decide)]; exact h6⟩
    · intro off hoff
      exact (hfield 0 (Nat.zero_le _) off hoff).trans (hslot0 off hoff)
    · intro t ht
      rcases htrees_ok t ht with ⟨hne, hppw, htm⟩
      have hrt : t.rootId ≤ lctCap F.n :=
        ht_mem_le ht t.rootId (AuxTree.rootId_mem_toList hne)
      refine ⟨hne, by rw [hfield t.rootId hrt OFF_PPAR (by decide)]; exact hppw, ?_⟩
      rw [hfield t.rootId hrt OFF_PPAR (by decide)]
      exact memAgree_treeMemMatch_of_ptrs htm hhp_eq
        (fun u hu off hoff => hfield u (ht_mem_le ht u hu) off hoff)
        (fun u hu off hoff => hptrs_all u (ht_mem_le ht u hu) off hoff)
    · intro v hv
      rcases hv_ok v hv with ⟨hiv, hhe⟩
      have hule : v + 1 ≤ lctCap F.n := by unfold lctCap; omega
      exact ⟨by rw [hfield (v + 1) hule OFF_ISV (by decide)]; exact hiv,
        by rw [hfield (v + 1) hule OFF_HASE (by decide)]; exact hhe⟩
    · intro p hp
      rcases hae_ok p hp with ⟨h1, h2, hisv, hhe, heid, heu, hev, t, ht, hed_t, s, hs_mem, hsm, hor⟩
      refine ⟨h1, h2,
        by rw [hfield p.1 h2 OFF_ISV (by decide)]; exact hisv,
        by rw [hfield p.1 h2 OFF_HASE (by decide)]; exact hhe,
        by rw [hfield p.1 h2 OFF_EID (by decide)]; exact heid,
        by rw [hfield p.1 h2 OFF_EU (by decide)]; exact heu,
        by rw [hfield p.1 h2 OFF_EV (by decide)]; exact hev,
        t, ht, hed_t, s, ?_, hsm, ?_⟩
      · have htm := (htrees_ok t ht).2.2
        rw [evalMemSteps_agree_ptrs htm
          (fun u hu off hoff => hfield u (ht_mem_le ht u hu) off hoff)
          (fun u hu off hoff => hptrs_all u (ht_mem_le ht u hu) off hoff) false 0]
        exact hs_mem
      · simpa only [hpar_eq] using hor
    · intro t ht
      rcases haux_ok t ht with ⟨hne_s, hpp_s, hlast_s⟩
      have hrt : t.rootId ≤ lctCap F.n :=
        ht_mem_le ht t.rootId (AuxTree.rootId_mem_toList (htrees_ok t ht).1)
      have hrev_t : t.evalInorder (revFlag mem₂ (lctNodesBase b)) false =
          t.evalInorder (revFlag mem₁ (lctNodesBase b)) false := by
        apply evalInorder_agree_of_list
        intro u hu
        exact hfield u (ht_mem_le ht u hu) OFF_REV (by decide)
      rw [hrev_t, hfield t.rootId hrt OFF_PPAR (by decide)]
      exact ⟨hne_s, hpp_s, hlast_s⟩
    · rcases hsub_ok with ⟨h1, h2, h3, h4⟩
      have hiter : ∀ k u,
          iterParent (lctAuxParent mem₂ (lctNodesBase b) (lctCap F.n)) k u =
          iterParent (lctAuxParent mem₁ (lctNodesBase b) (lctCap F.n)) k u := by
        intro k
        induction k with
        | zero => intro u; rfl
        | succ k ih => intro u; simp only [iterParent, hpar_eq, ih]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro u hu1 hu2; rw [hiter]; exact h1 u hu1 hu2
      · intro ed hed; rw [hpar_eq]; exact h2 ed hed
      · intro v hv; rw [hpar_eq]; exact h3 v hv
      · intro p hp; simp only [hpar_eq]; exact h4 p hp
    · intro u hu off hoff
      have hu' : u ≤ lctCap F.n := hxn ▸ hu
      rw [hfield u hu' off (ptrOffs_lt_stride hoff), hhp_eq]
      exact hptr_foot u hu off hoff
  · symm
    apply lctPhi_agree
    intro a ha1 ha2
    exact hag_foot a (lctFoot_arena (by unfold lctNodesBase at ha1; omega) ha2)

end FramingAndLocal

end MinCostFlow.LinkCut.Prog

