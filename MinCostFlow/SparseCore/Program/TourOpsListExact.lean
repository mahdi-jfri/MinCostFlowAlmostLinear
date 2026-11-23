module

public import MinCostFlow.SparseCore.Program.TourSplayListZero
public import MinCostFlow.SparseCore.Program.OutTourInterface
import Mathlib.Tactic

/-!
# Exact-space `listMarked` (`1 + |out|`, zero footprint growth)

Provides `tourOp_listMarked_exact_runs` for `tourOpListBody C.splay.loop C.listMark0 14` with
exact space `h + 1 + |out| < 2 ^ w`, returning `o.value = h + 1 + |out|`, preserving `ZeroFrom`
from `o.value`, writing below `h` only inside `tourFoot`, never growing `tourFoot`, and matching
the exact shape of `AsmBrTourListAt` (including `handle_foot`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Zero-scratch listing procedures installed in `p`, extending `TourSplayQueryProcs`. -/
structure TourListExactProcs (w : ℕ) (p : Program) extends TourSplayQueryProcs w p where
  walk0 : ℕ
  walk0_body : p.procs[walk0]? = some tourWalk0Body
  descMark0 : ℕ
  descMark0_body : p.procs[descMark0]? = some tourDescMark0Body
  join0 : ℕ
  join0_body : p.procs[join0]? = some (tourJoinBody walk0 splay.loop attachLeft)
  findFirstMark0 : ℕ
  findFirstMark0_body : p.procs[findFirstMark0]? =
    some (tourFindFirstBody descMark0 markTests.sumTest splay.loop)
  listMark0 : ℕ
  listMark0_body : p.procs[listMark0]? =
    some (tourListReadyBody findFirstMark0 detachRight join0)

/-- The handle `b` of `tourRep` always lies in its footprint (`AsmBrTourListAt.handle_foot`). -/
theorem tourFoot_handle (R_ord : DSRep (ℕ → List End)) (vCap eCap b : ℕ)
    (x : TourConcrete R_ord.τ) :
    tourFoot R_ord vCap eCap b x b :=
  Or.inl ⟨le_refl _, by simp [ordHandleOf, tourFixedSize]⟩

private theorem endListAt_of_listMark0 {mem mem' : ℕ → ℕ} {keyBase outPtr : ℕ}
    {ready : List ℕ} {keyOf : ℕ → ℕ}
    (hlen : mem' outPtr = ready.length)
    (helem : ∀ i < ready.length, mem' (outPtr + 1 + i) = mem (keyBase + ready.getD i 0))
    (hkey : ∀ u ∈ ready, mem (keyBase + u) = keyOf u) :
    EndListAt mem' outPtr (ready.map fun u => endOfKey (keyOf u)) := by
  refine ⟨by simpa using hlen, fun i hi => ?_⟩
  simp only [List.length_map] at hi
  rw [helem i hi]
  have hmem : ready.getD i 0 ∈ ready := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  rw [hkey _ hmem]
  have hget : (ready.map fun u => endOfKey (keyOf u)).getD i (0, true) =
      endOfKey (keyOf (ready.getD i 0)) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
  rw [hget, endKey_endOfKey']

/-- Exact-space Op 9 (`listMarked [b, r, heap]`): requires only `heap + 1 + |out| < 2 ^ w`
(no extra headroom and no separate word-size assumptions beyond `foot < heap < 2 ^ w`), returns
`o.value = heap + 1 + |out|`, keeps `ZeroFrom` from `o.value`, writes `< heap` only inside
`tourFoot`, does not grow `tourFoot`, and pays `TOUR_QUERY_MUL * (|out| + 1) * ordStoreLog eCap`. -/
theorem tourOp_listMarked_exact_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b r heap pos : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourListExactProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hr_lt : r < vCap)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap)
    (hroom : heap + 1 + (tourMarkedList s r).length < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpListBody C.splay.loop C.listMark0 14)
        (startState [b, r, heap] mem pos) o st' c ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        EndListAt st'.mem heap (tourMarkedList s r) ∧
        o.value = heap + 1 + (tourMarkedList s r).length ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < heap, ¬ tourFoot R_ord vCap eCap b x a → st'.mem a = mem a) ∧
        (∀ a, tourFoot R_ord vCap eCap b x' a → tourFoot R_ord vCap eCap b x a) ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * ((tourMarkedList s r).length + 1) * ordStoreLog eCap +
            (tourRep R_ord vCap eCap).phi b x mem := by
  set out := tourMarkedList s r
  have hord_le : ordHandleOf b vCap eCap ≤ heap := h.fixed_le_heap hfoot
  have hwide : 16 ≤ 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hw : vCap + 2 * eCap + 4 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hisr_lt : isRootBase b vCap + r < 2 ^ w := by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  have hfe_lt : firstEndBase b + r < 2 ^ w := by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  have hhdr := h.header
  set s0 : State := startState [b, r, heap] mem pos
  set r1 := Function.update s0.regs 3 (isRootBase b vCap)
  set isr := if r ∈ s.rf.R then 1 else 0
  set r2 := Function.update r1 4 isr
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 3) (rBase := 0) (off := HDR_IS_ROOT)
    (b := b) (val := isRootBase b vCap) (st := s0) (by simp [s0, startState])
    (by simp [HDR_IS_ROOT]; omega) (by simp [HDR_IS_ROOT]; omega) hhdr.2.2.2.2.2.1
  have ha2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 3) (rIdx := 1)
    (base := isRootBase b vCap) (idx := r) (val := isr) (st := ⟨mem, r1, pos⟩)
    (by simp [r1]) (by simp [r1, s0, startState]) hisr_lt (h.isRoot_mem r hr_lt)
  have hout_nil : (r ∉ s.rf.R ∨ s.ord r = []) → out = [] := by
    rintro (hnR | hnil)
    · simp only [out, tourMarkedList, coreTour, h.valid.compat.forest, ↓reduceDIte, hnR, ↓reduceIte, List.filter_nil]
    · simp only [out, tourMarkedList, coreTour, h.valid.compat.forest, ↓reduceDIte, hnil]
      split_ifs
      · rw [ordTourBlocks.eq_def]; rfl
      · rfl
  have hempty : ∀ (regs : ℕ → ℕ) (lpos : ℕ), regs 2 = heap → out = [] →
      ∃ st' c, c ≤ 20 ∧
        Runs w p ω (.store (.reg 2) (.const 0) ;; .ret (.bin .add (.reg 2) (.const 1)))
          ⟨mem, regs, lpos⟩ (.returned (heap + 1)) st' c ∧
        (tourRep R_ord vCap eCap).rep b s x st'.mem ∧
        EndListAt st'.mem heap out ∧
        heap + 1 = heap + 1 + out.length ∧
        ZeroFrom st'.mem (heap + 1) ∧
        (∀ a < heap, ¬ tourFoot R_ord vCap eCap b x a → st'.mem a = mem a) ∧
        (∀ a, tourFoot R_ord vCap eCap b x a → tourFoot R_ord vCap eCap b x a) ∧
        (tourRep R_ord vCap eCap).phi b x st'.mem = (tourRep R_ord vCap eCap).phi b x mem := by
    intro regs lpos hr2 hout0
    set M' := Function.update mem heap 0
    have hMeq : M' = mem := by
      funext a; by_cases ha : a = heap
      · rw [ha]; simp [M', (hzero heap le_rfl).symm]
      · simp [M', ha]
    have hst : Runs w p ω (.store (.reg 2) (.const 0)) ⟨mem, regs, lpos⟩ .normal ⟨M', regs, lpos⟩ 3 :=
      runs_store_iff.mpr ⟨heap, 0, by simp [Expr.eval, hr2], by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
    have hrt := runs_ret_reg_add1 (w := w) (p := p) (ω := ω) (st := ⟨M', regs, lpos⟩) (r := 2) (v := heap)
      hr2 (by omega) (by omega)
    refine ⟨⟨M', regs, lpos⟩, 8, by omega, tour_runs_seq_normal hst hrt, by simpa [tourRep, hMeq] using h,
      by simp [EndListAt, hout0, M'], by simp [hout0],
      by rw [hMeq]; exact fun a ha => hzero a (by omega),
      by rw [hMeq]; exact fun _ _ _ => rfl, fun _ ha => ha, by simp [hMeq]⟩
  unfold tourOpListBody
  set body2 : Stmt :=
    .assign 5 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
    .assign 6 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
    .assign 7 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
    .call 8 C.splay.loop [.reg 5, .reg 4, .reg 6, .reg 2] ;;
    .assign 8 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 17) (.reg 4))) (.const 14))) ;;
    .assign 9 (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 8)) ;;
    .call 10 C.listMark0 [.reg 5, .reg 4, .reg 6, .reg 7, .reg 2, .reg 9] ;;
    .ret (.reg 9)
  set body1 : Stmt :=
    .assign 3 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
    .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
    .cond (.bin .eq (.reg 4) (.const 0))
      (.store (.reg 2) (.const 0) ;; .ret (.bin .add (.reg 2) (.const 1)))
      body2
  by_cases hrR : r ∈ s.rf.R
  · have hisr1 : isr = 1 := by simp [isr, hrR]
    set r3 := Function.update r2 3 (firstEndBase b)
    set fe := match (s.ord r).head? with | none => 0 | some e => x.nodeOf (endKey e)
    set r4 := Function.update r3 4 fe
    have ha3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 3) (rBase := 0) (off := HDR_FIRST_END)
      (b := b) (val := firstEndBase b) (st := ⟨mem, r2, pos⟩) (by simp [r2, r1, s0, startState])
      (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END]; omega) hhdr.2.2.2.2.1
    have ha4 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 3) (rIdx := 1)
      (base := firstEndBase b) (idx := r) (val := fe) (st := ⟨mem, r3, pos⟩)
      (by simp [r3]) (by simp [r3, r2, r1, s0, startState]) hfe_lt (h.firstEnd_mem r hr_lt)
    cases ho : s.ord r with
    | nil =>
      have hfe0 : fe = 0 := by simp [fe, ho]
      obtain ⟨st', c_e, hce, hrun_e, hrep_e, hout_e, hval_e, hz_e, hfr_e, hft_e, hphi_e⟩ :=
        hempty r4 pos (by simp [r4, r3, r2, r1, s0, startState]) (hout_nil (Or.inr ho))
      have hc2 := tour_runs_cond_true (e := .bin .eq (.reg 4) (.const 0)) (v := 1) (st := ⟨mem, r4, pos⟩)
        (s₂ := body2)
        (by simp [Expr.eval, r4, hfe0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)])
        (by omega) hrun_e
      have hc1 := tour_runs_cond_false (e := .bin .eq (.reg 4) (.const 0)) (st := ⟨mem, r2, pos⟩)
        (s₁ := .store (.reg 2) (.const 0) ;; .ret (.bin .add (.reg 2) (.const 1)))
        (by simp [Expr.eval, r2, hisr1, BinOp.eval, (by omega : 0 < 2 ^ w)])
        (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4 hc2))
      refine ⟨.returned (heap + 1), st', _, tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 hc1),
        x, hrep_e, hout_e, hval_e, hz_e, hfr_e, hft_e, ?_⟩
      rw [hphi_e]; have htl : 1 ≤ ordStoreLog eCap := by simp [ordStoreLog]
      have h100 : 100 ≤ TOUR_QUERY_MUL * (out.length + 1) * ordStoreLog eCap := by
        have h1 : 1 ≤ (out.length + 1) * ordStoreLog eCap := Nat.mul_pos (by omega) htl
        calc 100 ≤ TOUR_QUERY_MUL * 1 := by simp [TOUR_QUERY_MUL]
          _ ≤ TOUR_QUERY_MUL * ((out.length + 1) * ordStoreLog eCap) := Nat.mul_le_mul_left _ h1
          _ = TOUR_QUERY_MUL * (out.length + 1) * ordStoreLog eCap := by ring
      simp only [Expr.size] at hce ⊢; omega
    | cons e0 es0 =>
      have he0_mem : e0 ∈ s.ord r := by rw [ho]; simp
      obtain ⟨_, _, _, _, hfe_pos, hfe_le, _, t, rest, hct, hperm, ht_map, hfe_in⟩ :=
        h.mem_compTree_of_active he0_mem
      have hrr : s.rf.root r = r := h.valid.root_eq_of_mem (h.valid.roots_sub hrR) hrR (connected_refl _ r)
      rw [hrr] at hct ht_map
      have hfe_eq : fe = x.nodeOf (endKey e0) := by simp [fe, ho]
      have hfe_nz : fe ≠ 0 := by omega
      have hfe_cap : fe ≤ x.numNodes := by omega
      have hfe_t : fe ∈ t.toList := by rwa [hfe_eq]
      have hf_perm : TourForestInv x.numNodes x.st ([] ++ t :: rest) := (h.forestInv.perm hperm).1
      have hfuel : x.numNodes < 2 * eCap + 2 := by have := h.numNodes_le; omega
      have hfuelW : 2 * eCap + 2 < 2 ^ w := by omega
      have hdep : t.depthOf fe < 2 * eCap + 2 :=
        lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hfe_t)
          (le_of_lt (lt_of_le_of_lt (hf_perm.countNodes_le (by simp)) hfuel))
      have hrec_le : tourLayout.nodeAddr (nodesBase b vCap eCap) (x.numNodes + 1) ≤ heap := by
        have := h.numNodes_le
        simp [nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
      have hheap0 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes heap 0 mem :=
        ⟨hrec_le, by omega, hzero, hwide⟩
      obtain ⟨t₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, _, hcost₁⟩ :=
        tourSplayLoop_runs_amort (pos := pos) C.toTourSplayCoreProcs ω h.nodesAt hf_perm (h.valsOk hw)
          hfe_t hdep hfuelW hheap0
      set s₁ := SplayState.splay tourPayload x.st (2 * eCap + 2) fe
      obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf_perm hfe_t hdep
      have hout_eq : (t.toList.filter fun u => (x.st.nodes u).val.isMarked).map (fun u => endOfKey (x.keyOf u)) = out := by
        dsimp only [out]
        rw [← fullTour_filter_marked_eq_tourMarkedList h.valid hrR, ← ht_map, List.filter_map]
        congr 1; refine List.filter_congr fun u hu => ?_
        have hu_in := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, hperm.mem_iff.mpr (by simp), hu⟩)
        have hu_ft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
          rw [← ht_map]; exact List.mem_map_of_mem hu
        obtain ⟨v, hv, _⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hu_ft
        rw [h.val_active u hu_in.1 hu_in.2 ⟨v, hv⟩]; rfl
      have hready_eq : (t₁.toList.filter fun u => (s₁.nodes u).val.isMarked) =
          (t.toList.filter fun u => (x.st.nodes u).val.isMarked) := by
        rw [hlist₁]
        refine List.filter_congr fun u hu => ?_
        rw [hval_sp u (hf_perm.mem_inCap (t := t) (by simp) hu).2]
      have hcnt_mem : st₁.mem (nodesBase b vCap eCap + 17 * fe + 14) = out.length := by
        have h14 : st₁.mem (nodesBase b vCap eCap + 17 * fe + 14) = (s₁.nodes fe).sum.markCnt := by
          simpa [nodeAddr, tourLayout_offSum, tourLayout_stride] using (hn₁ fe hfe_cap).2.2.2.2.2.2.2.1.2.2.1
        rw [h14, ← hroot₁, hinv₁.sum_markCnt (by simp), hready_eq, ← hout_eq, List.length_map]
      set splayHeap := heap + 1 + out.length
      have hheap1 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes splayHeap 0 st₁.mem :=
        ⟨le_trans hheap0.rec_le (by omega), by omega, fun a ha => hfr₁.1 a (by omega), hwide⟩
      have hkey_disj : ∀ u ≤ x.numNodes, keyOfNodeBase b vCap eCap + u < splayHeap ∧
          ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes (keyOfNodeBase b vCap eCap + u) := fun u hu =>
        ⟨by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega,
         not_inRecords_of_lt_nodesBase (by have := h.numNodes_le; simp [keyOfNodeBase, nodesBase]; omega)⟩
      have hout_rec : ∀ i ≤ ((optList (some t₁)).filter fun u => (s₁.nodes u).val.isMarked).length,
          ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes (heap + i) := fun i _ =>
        not_inRecords_of_ge_ordHandle_of_le h.numNodes_le (by omega)
      have hout_key : ∀ u ≤ x.numNodes, ∀ i ≤ ((optList (some t₁)).filter fun u => (s₁.nodes u).val.isMarked).length,
          heap + i ≠ keyOfNodeBase b vCap eCap + u := fun u hu i _ => by
        have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
      have hout_heap : heap + 1 + ((optList (some t₁)).filter fun u => (s₁.nodes u).val.isMarked).length ≤ splayHeap := by
        simp only [optList, Option.elim, hready_eq, ← hout_eq, List.length_map, splayHeap]; omega
      obtain ⟨t₂?, s₂, o₂, st₂, c₂, hrun₂, _, hn₂, hinv₂, _, hlist₂, hval₂, _,
        hlen₂, helem₂, hzero₂, hfr₂, hcost₂⟩ :=
        tourListMark0Body_runs (pos := st₁.pos) C.toTourSplayQueryProcs C.walk0_body C.descMark0_body
          C.join0_body C.findFirstMark0_body ω hn₁ (by simpa [optTrees] using hinv₁) hvals₁
          hfuel hfuelW hheap1 hkey_disj hout_rec hout_key hout_heap
      cases t₂? with
      | none =>
        have hne_l : t.toList ≠ [] := List.ne_nil_of_mem hfe_t
        simp [optList, hlist₁] at hlist₂; exact absurd hlist₂ hne_l
      | some t₂ =>
        have hlist₂' : t₂.toList = t.toList := by simpa [optList, hlist₁] using hlist₂
        have hval_all : ∀ u ≤ x.numNodes, (s₂.nodes u).val = (x.st.nodes u).val := fun u hu =>
          (hval₂ u hu).trans (hval_sp u hu)
        have hagree_all : ∀ a < heap, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a →
            st₂.mem a = mem a := fun a ha hnr => by
          rw [hfr₂ a (by omega) hnr (fun i _ => by omega), hfr₁.2 a ha hnr]
        obtain ⟨hrep', hphi_ord, hphi_perm, hfoot_eq⟩ :=
          h.replace_compTree_same_list hLoc hfoot hrR hperm hct hlist₂' hn₂
            (by simpa [optTrees] using hinv₂) hval_all hagree_all
        set x' : TourConcrete R_ord.τ :=
          { x with st := s₂, trees := t₂ :: rest, compTree := Function.update x.compTree r (some t₂) }
        set r5 := Function.update r4 5 (nodesBase b vCap eCap)
        set r6 := Function.update r5 6 (2 * eCap + 2)
        set r7 := Function.update r6 7 (keyOfNodeBase b vCap eCap)
        set s_sp : State := { st₁ with regs := Function.update r7 8 o₁.value }
        set r8 := Function.update s_sp.regs 8 out.length
        set r9 := Function.update r8 9 splayHeap
        set s_ls : State := { st₂ with regs := Function.update r9 10 o₂.value }
        have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_NODES_BASE)
          (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem, r4, pos⟩) (by simp [r4, r3, r2, r1, s0, startState])
          (by simp [HDR_NODES_BASE]; omega) (by simp [HDR_NODES_BASE]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
        have ha6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_FUEL)
          (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r5, pos⟩) (by simp [r5, r4, r3, r2, r1, s0, startState])
          (by simp [HDR_FUEL]; omega) (by simp [HDR_FUEL]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have ha7 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_KEY_OF_NODE)
          (b := b) (val := keyOfNodeBase b vCap eCap) (st := ⟨mem, r6, pos⟩) (by simp [r6, r5, r4, r3, r2, r1, s0, startState])
          (by simp [HDR_KEY_OF_NODE]; omega) (by simp [HDR_KEY_OF_NODE]; omega) hhdr.2.2.2.2.2.2.2.2.1
        have hcall_sp := runs_call_regs4 8 5 4 6 2 (st := ⟨mem, r7, pos⟩) C.splay.loop_body
          (by simp [r7, r6, r5]) (by simp [r7, r6, r5, r4]) (by simp [r7, r6]) (by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState]) hrun₁
        have hAfe : nodesBase b vCap eCap + 17 * fe + 17 ≤ heap := by
          simpa [nodeAddr, tourLayout_stride] using hheap0.addr_lt hfe_cap
        have ha8 : Runs w p ω (.assign 8 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 17) (.reg 4))) (.const 14))))
            s_sp .normal ⟨st₁.mem, r8, st₁.pos⟩ 9 :=
          runs_assign_iff.mpr ⟨out.length, by
            simp [Expr.eval, s_sp, r7, r6, r5, r4, BinOp.eval, hcnt_mem, (by omega : 17 < 2 ^ w),
              (by omega : 17 * fe < 2 ^ w), (by omega : nodesBase b vCap eCap + 17 * fe < 2 ^ w),
              (by omega : 14 < 2 ^ w), (by omega : nodesBase b vCap eCap + 17 * fe + 14 < 2 ^ w)], rfl, rfl, rfl⟩
        have ha9 : Runs w p ω (.assign 9 (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 8)))
            ⟨st₁.mem, r8, st₁.pos⟩ .normal ⟨st₁.mem, r9, st₁.pos⟩ 6 :=
          runs_assign_iff.mpr ⟨splayHeap, by
            simp [Expr.eval, r8, s_sp, r7, r6, r5, r4, r3, r2, r1, s0, startState, BinOp.eval, splayHeap,
              (by omega : 1 < 2 ^ w), (by omega : heap + 1 < 2 ^ w), (by omega : heap + 1 + out.length < 2 ^ w)], rfl, rfl, rfl⟩
        have hcall_ls := runs_call_regs6 10 5 4 6 7 2 9 (st := ⟨st₁.mem, r9, st₁.pos⟩) C.listMark0_body
          (by simp [r9, r8, s_sp, r7, r6, r5])
          (by simp [r9, r8, s_sp, r7, r6, r5, r4, optRoot, hroot₁])
          (by simp [r9, r8, s_sp, r7, r6]) (by simp [r9, r8, s_sp, r7])
          (by simp [r9, r8, s_sp, r7, r6, r5, r4, r3, r2, r1, s0, startState])
          (by simp [r9]) hrun₂
        have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s_ls) (r := 9) (v := splayHeap) (by simp [s_ls, r9])
        have hbody := tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7
          (tour_runs_seq_normal hcall_sp (tour_runs_seq_normal ha8 (tour_runs_seq_normal ha9 (tour_runs_seq_normal hcall_ls hret))))))
        have hc2 := tour_runs_cond_false (e := .bin .eq (.reg 4) (.const 0)) (st := ⟨mem, r4, pos⟩)
          (s₁ := .store (.reg 2) (.const 0) ;; .ret (.bin .add (.reg 2) (.const 1)))
          (by simp [Expr.eval, r4, hfe_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]) hbody
        have hc1 := tour_runs_cond_false (e := .bin .eq (.reg 4) (.const 0)) (st := ⟨mem, r2, pos⟩)
          (s₁ := .store (.reg 2) (.const 0) ;; .ret (.bin .add (.reg 2) (.const 1)))
          (by simp [Expr.eval, r2, hisr1, BinOp.eval, (by omega : 0 < 2 ^ w)])
          (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4 hc2))
        have hend : EndListAt st₂.mem heap out := by
          rw [← hout_eq, ← hready_eq]
          refine endListAt_of_listMark0 hlen₂ helem₂ fun u hu => ?_
          have hu_t : u ∈ t.toList := by rw [← hlist₁]; exact (List.mem_filter.mp hu).1
          have hu_in := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, hperm.mem_iff.mpr (by simp), hu_t⟩)
          have hkr := hfr₁.2 (keyOfNodeBase b vCap eCap + u)
            (by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
            (not_inRecords_of_lt_nodesBase (by have := h.numNodes_le; simp [keyOfNodeBase, nodesBase]; omega))
          rw [hkr]; exact (h.keyOf_mem u hu_in.1 hu_in.2).1
        refine ⟨.returned splayHeap, s_ls, _, tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 hc1),
          x', hrep', hend, rfl, hzero₂, fun a ha hnf => ?_, fun a ha => (hfoot_eq a).mp ha, ?_⟩
        · refine hagree_all a ha fun hrec => hnf (Or.inl ?_)
          have hlr := inRecords_lt_ordHandle_of_le h.numNodes_le hrec
          exact ⟨by simp [nodesBase] at hlr; omega, hlr.2⟩
        · have hlog : Nat.log 2 (x.numNodes + 2) + 1 ≤ 2 * ordStoreLog eCap := by
            simpa [ordStoreLog, tourLog] using tourLog_of_le h.numNodes_le
          have hlen_r : ((optList (some t₁)).filter fun u => (s₁.nodes u).val.isMarked).length = out.length := by
            simp only [optList, Option.elim, hready_eq, ← hout_eq, List.length_map]
          rw [hlen_r] at hcost₂
          have htl : 1 ≤ ordStoreLog eCap := by simp [ordStoreLog]
          have hlog_mul1 : TOUR_SPLAY_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) ≤
              (TOUR_SPLAY_AMORT * 2) * ordStoreLog eCap := by
            calc TOUR_SPLAY_AMORT * (Nat.log 2 (x.numNodes + 2) + 1)
                ≤ TOUR_SPLAY_AMORT * (2 * ordStoreLog eCap) := Nat.mul_le_mul_left TOUR_SPLAY_AMORT hlog
              _ = (TOUR_SPLAY_AMORT * 2) * ordStoreLog eCap := by ring
          have hlog_mul2 : (out.length + 1) * TOUR_LIST_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) ≤
              (TOUR_LIST_AMORT * 2) * (out.length + 1) * ordStoreLog eCap := by
            have h1 := Nat.mul_le_mul_left ((out.length + 1) * TOUR_LIST_AMORT) hlog
            calc (out.length + 1) * TOUR_LIST_AMORT * (Nat.log 2 (x.numNodes + 2) + 1)
                ≤ (out.length + 1) * TOUR_LIST_AMORT * (2 * ordStoreLog eCap) := h1
              _ = (TOUR_LIST_AMORT * 2) * (out.length + 1) * ordStoreLog eCap := by ring
          have hlog_sub : (TOUR_SPLAY_AMORT * 2) * ordStoreLog eCap ≤
              (TOUR_SPLAY_AMORT * 2) * (out.length + 1) * ordStoreLog eCap := by
            have h1 : 1 ≤ out.length + 1 := by omega
            calc (TOUR_SPLAY_AMORT * 2) * ordStoreLog eCap
                = (TOUR_SPLAY_AMORT * 2) * 1 * ordStoreLog eCap := by ring
              _ ≤ (TOUR_SPLAY_AMORT * 2) * (out.length + 1) * ordStoreLog eCap :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
          have h100 : 100 ≤ 100 * (out.length + 1) * ordStoreLog eCap := by
            have h1 : 1 ≤ (out.length + 1) * ordStoreLog eCap := Nat.mul_pos (by omega) htl
            calc 100 = 100 * 1 := by ring
              _ ≤ 100 * ((out.length + 1) * ordStoreLog eCap) := Nat.mul_le_mul_left 100 h1
              _ = 100 * (out.length + 1) * ordStoreLog eCap := by ring
          have htot_eq : TOUR_QUERY_MUL * (out.length + 1) * ordStoreLog eCap =
              (TOUR_SPLAY_AMORT * 2) * (out.length + 1) * ordStoreLog eCap +
              (TOUR_LIST_AMORT * 2) * (out.length + 1) * ordStoreLog eCap +
              100 * (out.length + 1) * ordStoreLog eCap +
              39900 * (out.length + 1) * ordStoreLog eCap := by
            simp only [TOUR_QUERY_MUL, TOUR_SPLAY_AMORT, TOUR_LIST_AMORT]; ring
          dsimp only [tourRep, tourPhi, x']
          rw [hphi_ord, hphi_perm]
          simp only [optTrees, Option.toList, List.nil_append, List.cons_append, Expr.size,
            TOUR_PHI_MULT] at hcost₁ hcost₂ ⊢
          omega
  · have hisr0 : isr = 0 := by simp [isr, hrR]
    obtain ⟨st', c_e, hce, hrun_e, hrep_e, hout_e, hval_e, hz_e, hfr_e, hft_e, hphi_e⟩ :=
      hempty r2 pos (by simp [r2, r1, s0, startState]) (hout_nil (Or.inl hrR))
    have hc1 := tour_runs_cond_true (e := .bin .eq (.reg 4) (.const 0)) (v := 1) (st := ⟨mem, r2, pos⟩)
      (s₂ := body1)
      (by simp [Expr.eval, r2, hisr0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)])
      (by omega) hrun_e
    refine ⟨.returned (heap + 1), st', _, tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 hc1),
      x, hrep_e, hout_e, hval_e, hz_e, hfr_e, hft_e, ?_⟩
    rw [hphi_e]; have htl : 1 ≤ ordStoreLog eCap := by simp [ordStoreLog]
    have h100 : 100 ≤ TOUR_QUERY_MUL * (out.length + 1) * ordStoreLog eCap := by
      have h1 : 1 ≤ (out.length + 1) * ordStoreLog eCap := Nat.mul_pos (by omega) htl
      calc 100 ≤ TOUR_QUERY_MUL * 1 := by simp [TOUR_QUERY_MUL]
        _ ≤ TOUR_QUERY_MUL * ((out.length + 1) * ordStoreLog eCap) := Nat.mul_le_mul_left _ h1
        _ = TOUR_QUERY_MUL * (out.length + 1) * ordStoreLog eCap := by ring
    simp only [Expr.size] at hce ⊢; omega

/-- Compatibility corollary: `tourOpListBody C.splay.loop C.listMark0 14` also satisfies `Respects`
with space `1 + |out|` (and hence any larger space such as `3 + |out|`). -/
theorem tourOp_listMarked_exact_respects {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b r heap pos space : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourListExactProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hr_lt : r < vCap)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap)
    (hspace : 1 + (tourMarkedList s r).length ≤ space)
    (hroom : heap + space < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpListBody C.splay.loop C.listMark0 14)
        (startState [b, r, heap] mem pos) o st' c ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        EndListAt st'.mem heap (tourMarkedList s r) ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap
          space mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * ((tourMarkedList s r).length + 1) * tourLog eCap +
            (tourRep R_ord vCap eCap).phi b x mem := by
  obtain ⟨o, st', c, hrun, x', hrep', hend, hval, hz, hfr, hft, hcost⟩ :=
    tourOp_listMarked_exact_runs hLoc C ω h hr_lt hfoot hzero (by omega)
  refine ⟨o, st', c, hrun, x', hrep', hend,
    ⟨by omega, by omega, hz, hfr, fun a ha => Or.inl (hft a ha)⟩, ?_⟩
  simpa [ordStoreLog, tourLog] using hcost

end MinCostFlow.SparseCore.Program
