module

public import MinCostFlow.SparseCore.Program.TourOpsHelper
import Mathlib.Tactic

/-!
# List query operations (`listTour`, `listMarked`)

Implements and verifies Ops `4` (`listTour`) and `9` (`listMarked`) of `tourContract` via the
unified WordRAM procedure `tourOpListBody`, running in `O((|out| + 1) · tourLog eCap)` amortized
time with `3 + |out|` cells of heap headroom (`h' = heap + 1 + |out|`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Amortized per-`tourLog eCap` constant covering every query operation (Ops 4, 5, 6, 8, 9, 10). -/
def TOUR_QUERY_MUL : ℕ := 700000

/-- Unified WordRAM body for Op 4 (`listTour`, `sumOff = 13`, `listProc = listOpen`) and Op 9
(`listMarked`, `sumOff = 14`, `listProc = listMark`). Args: `[b, r, heap]`. -/
def tourOpListBody (splayProc listProc sumOff : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const HDR_IS_ROOT))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .cond (.bin .eq (.reg 4) (.const 0))
    (.store (.reg 2) (.const 0) ;; .ret (.bin .add (.reg 2) (.const 1)))
    (.assign 3 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
     .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
     .cond (.bin .eq (.reg 4) (.const 0))
       (.store (.reg 2) (.const 0) ;; .ret (.bin .add (.reg 2) (.const 1)))
       (.assign 5 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
        .assign 6 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
        .assign 7 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
        .call 8 splayProc [.reg 5, .reg 4, .reg 6, .reg 2] ;;
        .assign 8 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 17) (.reg 4))) (.const sumOff))) ;;
        .assign 9 (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 8)) ;;
        .call 10 listProc [.reg 5, .reg 4, .reg 6, .reg 7, .reg 2, .reg 9] ;;
        .ret (.reg 9)))

theorem tourOpListBody_noRand (sP lP sumOff : ℕ) :
    (tourOpListBody sP lP sumOff).NoRand := by
  simp [tourOpListBody, Stmt.NoRand]

private theorem endListAt_of_listReady {mem mem' : ℕ → ℕ} {keyBase outPtr : ℕ}
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

private theorem tourOpListBody_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b r heap pos sumOff dp fp listP : ℕ} {p : Program}
    {rs : TourSum → Bool} {rv : TourVal → Bool} {out : List End}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p)
    (T : ReadyTests w p tourLayout rs rv) (hTc : T.cost = TOUR_TEST_COST)
    (hR : ReadyLaw tourPayload rs rv)
    (hdp : p.procs[dp]? = some (descendBody dp C.lazy.pushDown T.sumTest T.valTest))
    (hfp : p.procs[fp]? = some (tourFindFirstBody dp T.sumTest C.splay.splay))
    (hlp : p.procs[listP]? = some (tourListReadyBody fp C.detachRight C.join))
    (hsumOff : sumOff < 16)
    (hsum_read : ∀ (cap : ℕ) (st : SplayState TourVal TourSum Unit) (M : ℕ → ℕ) (t : AuxTree) (rest : List AuxTree) (u : ℕ),
      tourLayout.NodesAt M (nodesBase b vCap eCap) cap st →
      TourForestInv cap st (t :: rest) → t.rootId = u → u ≤ cap →
      M (nodesBase b vCap eCap + 17 * u + sumOff) = (t.toList.filter fun z => rv (st.nodes z).val).length)
    (ω : ℕ → Bool) {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hr_lt : r < vCap) (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + (3 + out.length) < 2 ^ w)
    (hout_nil : (r ∉ s.rf.R ∨ s.ord r = []) → out = [])
    (hout_some : ∀ t, r ∈ s.rf.R → x.compTree r = some t → t ∈ x.trees →
      t.toList.map (fun id => endOfKey (x.keyOf id)) = fullTour s.ord s.rf.F h.valid.compat.forest r →
      (t.toList.filter fun u => rv (x.st.nodes u).val).map (fun u => endOfKey (x.keyOf u)) = out) :
    ∃ o st' c, Runs w p ω (tourOpListBody C.splay.splay listP sumOff)
        (startState [b, r, heap] mem pos) o st' c ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        EndListAt st'.mem heap out ∧
        o.value = heap + 1 + out.length ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap
          (3 + out.length) mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * (out.length + 1) * tourLog eCap +
            (tourRep R_ord vCap eCap).phi b x mem := by
  have hord_le : ordHandleOf b vCap eCap ≤ heap := h.fixed_le_heap hfoot
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
  have hempty : ∀ (regs : ℕ → ℕ) (lpos : ℕ), regs 2 = heap → out = [] →
      ∃ st' c, c ≤ 20 ∧
        Runs w p ω (.store (.reg 2) (.const 0) ;; .ret (.bin .add (.reg 2) (.const 1)))
          ⟨mem, regs, lpos⟩ (.returned (heap + 1)) st' c ∧
        (tourRep R_ord vCap eCap).rep b s x st'.mem ∧
        EndListAt st'.mem heap out ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap
          (3 + out.length) mem (heap + 1) b x st'.mem ∧
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
      by simp [EndListAt, hout0, M'], ?_, by simp [hMeq]⟩
    refine ⟨by omega, by omega, by rw [hMeq]; exact fun a ha => hzero a (by omega),
      by rw [hMeq]; exact fun _ _ _ => rfl, fun _ ha => Or.inl ha⟩
  unfold tourOpListBody
  set body2 : Stmt :=
    .assign 5 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
    .assign 6 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
    .assign 7 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
    .call 8 C.splay.splay [.reg 5, .reg 4, .reg 6, .reg 2] ;;
    .assign 8 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 17) (.reg 4))) (.const sumOff))) ;;
    .assign 9 (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 8)) ;;
    .call 10 listP [.reg 5, .reg 4, .reg 6, .reg 7, .reg 2, .reg 9] ;;
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
      obtain ⟨st', c_e, hce, hrun_e, hrep_e, hout_e, hresp_e, hphi_e⟩ :=
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
        x, hrep_e, hout_e, by simp [Outcome.value, hout_nil (Or.inr ho)], hresp_e, ?_⟩
      rw [hphi_e]; have htl : 1 ≤ tourLog eCap := by simp [tourLog]
      have h100 : 100 ≤ TOUR_QUERY_MUL * (out.length + 1) * tourLog eCap := by
        have h1 : 1 ≤ (out.length + 1) * tourLog eCap := Nat.mul_pos (by omega) htl
        calc 100 ≤ TOUR_QUERY_MUL * 1 := by simp [TOUR_QUERY_MUL]
          _ ≤ TOUR_QUERY_MUL * ((out.length + 1) * tourLog eCap) := Nat.mul_le_mul_left _ h1
          _ = TOUR_QUERY_MUL * (out.length + 1) * tourLog eCap := by ring
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
      have hheap0 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes heap 2 mem :=
        h.heapOk hfoot hzero (by omega) hwide
      obtain ⟨t₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, _, hcost₁⟩ :=
        tourSplay_runs_amort (pos := pos) C.toTourSplayCoreProcs ω h.nodesAt hf_perm (h.valsOk hw)
          hfe_t hdep hfuelW hheap0
      set s₁ := SplayState.splay tourPayload x.st (2 * eCap + 2) fe
      obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf_perm hfe_t hdep
      have hout_eq := hout_some t hrR hct (hperm.mem_iff.mpr (by simp)) ht_map
      have hready_eq : (t₁.toList.filter fun u => rv (s₁.nodes u).val) =
          (t.toList.filter fun u => rv (x.st.nodes u).val) := by
        rw [hlist₁]
        refine List.filter_congr fun u hu => ?_
        rw [hval_sp u (hf_perm.mem_inCap (t := t) (by simp) hu).2]
      have hcnt_mem : st₁.mem (nodesBase b vCap eCap + 17 * fe + sumOff) = out.length := by
        rw [hsum_read x.numNodes s₁ st₁.mem t₁ rest fe hn₁ hinv₁ hroot₁ hfe_cap, hready_eq, ← hout_eq, List.length_map]
      set splayHeap := heap + 1 + out.length
      have hheap1 : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes splayHeap 2 st₁.mem :=
        ⟨le_trans hheap0.rec_le (by omega), by omega, fun a ha => hfr₁.1 a (by omega), hwide⟩
      have hkey_disj : ∀ u ≤ x.numNodes, keyOfNodeBase b vCap eCap + u < splayHeap ∧
          ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes (keyOfNodeBase b vCap eCap + u) := fun u hu =>
        ⟨by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega,
         not_inRecords_of_lt_nodesBase (by have := h.numNodes_le; simp [keyOfNodeBase, nodesBase]; omega)⟩
      have hout_rec : ∀ i ≤ ((optList (some t₁)).filter fun u => rv (s₁.nodes u).val).length,
          ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes (heap + i) := fun i _ =>
        not_inRecords_of_ge_ordHandle_of_le h.numNodes_le (by omega)
      have hout_key : ∀ u ≤ x.numNodes, ∀ i ≤ ((optList (some t₁)).filter fun u => rv (s₁.nodes u).val).length,
          heap + i ≠ keyOfNodeBase b vCap eCap + u := fun u hu i _ => by
        have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
      have hout_heap : heap + 1 + ((optList (some t₁)).filter fun u => rv (s₁.nodes u).val).length ≤ splayHeap := by
        simp only [optList, Option.elim, hready_eq, ← hout_eq, List.length_map, splayHeap]; omega
      obtain ⟨t₂?, s₂, o₂, st₂, c₂, hrun₂, _, hn₂, hinv₂, _, hlist₂, hval₂, _,
        hlen₂, helem₂, hzero₂, hfr₂, hcost₂⟩ :=
        tourListReadyBody_runs (pos := st₁.pos) C T hTc hR hdp hfp ω hn₁
          (by simpa [optTrees] using hinv₁) hvals₁ hfuel hfuelW hheap1 hkey_disj hout_rec hout_key hout_heap
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
        have hcall_sp := runs_call_regs4 8 5 4 6 2 (st := ⟨mem, r7, pos⟩) C.splay.splay_body
          (by simp [r7, r6, r5]) (by simp [r7, r6, r5, r4]) (by simp [r7, r6]) (by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState]) hrun₁
        have hAfe : nodesBase b vCap eCap + 17 * fe + 17 ≤ heap := by
          simpa [nodeAddr, tourLayout_stride] using hheap0.addr_lt hfe_cap
        have ha8 : Runs w p ω (.assign 8 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 17) (.reg 4))) (.const sumOff))))
            s_sp .normal ⟨st₁.mem, r8, st₁.pos⟩ 9 :=
          runs_assign_iff.mpr ⟨out.length, by
            simp [Expr.eval, s_sp, r7, r6, r5, r4, BinOp.eval, hcnt_mem, (by omega : 17 < 2 ^ w),
              (by omega : 17 * fe < 2 ^ w), (by omega : nodesBase b vCap eCap + 17 * fe < 2 ^ w),
              (by omega : sumOff < 2 ^ w), (by omega : nodesBase b vCap eCap + 17 * fe + sumOff < 2 ^ w)], rfl, rfl, rfl⟩
        have ha9 : Runs w p ω (.assign 9 (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 8)))
            ⟨st₁.mem, r8, st₁.pos⟩ .normal ⟨st₁.mem, r9, st₁.pos⟩ 6 :=
          runs_assign_iff.mpr ⟨splayHeap, by
            simp [Expr.eval, r8, s_sp, r7, r6, r5, r4, r3, r2, r1, s0, startState, BinOp.eval, splayHeap,
              (by omega : 1 < 2 ^ w), (by omega : heap + 1 < 2 ^ w), (by omega : heap + 1 + out.length < 2 ^ w)], rfl, rfl, rfl⟩
        have hcall_ls := runs_call_regs6 10 5 4 6 7 2 9 (st := ⟨st₁.mem, r9, st₁.pos⟩) hlp
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
          refine endListAt_of_listReady hlen₂ helem₂ fun u hu => ?_
          have hu_t : u ∈ t.toList := by rw [← hlist₁]; exact (List.mem_filter.mp hu).1
          have hu_in := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, hperm.mem_iff.mpr (by simp), hu_t⟩)
          have hkr := hfr₁.2 (keyOfNodeBase b vCap eCap + u)
            (by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega)
            (not_inRecords_of_lt_nodesBase (by have := h.numNodes_le; simp [keyOfNodeBase, nodesBase]; omega))
          rw [hkr]; exact (h.keyOf_mem u hu_in.1 hu_in.2).1
        have hresp : (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap
            (3 + out.length) mem splayHeap b x' st₂.mem := by
          refine ⟨by omega, by omega, hzero₂, fun a ha hnf => ?_, fun a ha => Or.inl ((hfoot_eq a).mp ha)⟩
          refine hagree_all a ha fun hrec => hnf (Or.inl ?_)
          have hlr := inRecords_lt_ordHandle_of_le h.numNodes_le hrec
          exact ⟨by simp [nodesBase] at hlr; omega, hlr.2⟩
        refine ⟨.returned splayHeap, s_ls, _, tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 hc1),
          x', hrep', hend, rfl, hresp, ?_⟩
        have hlog := tourLog_of_le h.numNodes_le
        have hlen_r : ((optList (some t₁)).filter fun u => rv (s₁.nodes u).val).length = out.length := by
          simp only [optList, Option.elim, hready_eq, ← hout_eq, List.length_map]
        rw [hlen_r] at hcost₂
        have htl : 1 ≤ tourLog eCap := by simp [tourLog]
        have hlog_mul1 : TOUR_SPLAY_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) ≤
            (TOUR_SPLAY_AMORT * 2) * tourLog eCap := by
          calc TOUR_SPLAY_AMORT * (Nat.log 2 (x.numNodes + 2) + 1)
              ≤ TOUR_SPLAY_AMORT * (2 * tourLog eCap) := Nat.mul_le_mul_left TOUR_SPLAY_AMORT hlog
            _ = (TOUR_SPLAY_AMORT * 2) * tourLog eCap := by ring
        have hlog_mul2 : (out.length + 1) * TOUR_LIST_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) ≤
            (TOUR_LIST_AMORT * 2) * (out.length + 1) * tourLog eCap := by
          have h1 := Nat.mul_le_mul_left ((out.length + 1) * TOUR_LIST_AMORT) hlog
          calc (out.length + 1) * TOUR_LIST_AMORT * (Nat.log 2 (x.numNodes + 2) + 1)
              ≤ (out.length + 1) * TOUR_LIST_AMORT * (2 * tourLog eCap) := h1
            _ = (TOUR_LIST_AMORT * 2) * (out.length + 1) * tourLog eCap := by ring
        have hlog_sub : (TOUR_SPLAY_AMORT * 2) * tourLog eCap ≤
            (TOUR_SPLAY_AMORT * 2) * (out.length + 1) * tourLog eCap := by
          have h1 : 1 ≤ out.length + 1 := by omega
          calc (TOUR_SPLAY_AMORT * 2) * tourLog eCap
              = (TOUR_SPLAY_AMORT * 2) * 1 * tourLog eCap := by ring
            _ ≤ (TOUR_SPLAY_AMORT * 2) * (out.length + 1) * tourLog eCap :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
        have h100 : 100 ≤ 100 * (out.length + 1) * tourLog eCap := by
          have h1 : 1 ≤ (out.length + 1) * tourLog eCap := Nat.mul_pos (by omega) htl
          calc 100 = 100 * 1 := by ring
            _ ≤ 100 * ((out.length + 1) * tourLog eCap) := Nat.mul_le_mul_left 100 h1
            _ = 100 * (out.length + 1) * tourLog eCap := by ring
        have htot_eq : TOUR_QUERY_MUL * (out.length + 1) * tourLog eCap =
            (TOUR_SPLAY_AMORT * 2) * (out.length + 1) * tourLog eCap +
            (TOUR_LIST_AMORT * 2) * (out.length + 1) * tourLog eCap +
            100 * (out.length + 1) * tourLog eCap +
            39900 * (out.length + 1) * tourLog eCap := by
          simp only [TOUR_QUERY_MUL, TOUR_SPLAY_AMORT, TOUR_LIST_AMORT]; ring
        dsimp only [tourRep, tourPhi, x']
        rw [hphi_ord, hphi_perm]
        simp only [optTrees, Option.toList, List.nil_append, List.cons_append, Expr.size,
          TOUR_PHI_MULT] at hcost₁ hcost₂ ⊢
        omega
  · have hisr0 : isr = 0 := by simp [isr, hrR]
    obtain ⟨st', c_e, hce, hrun_e, hrep_e, hout_e, hresp_e, hphi_e⟩ :=
      hempty r2 pos (by simp [r2, r1, s0, startState]) (hout_nil (Or.inl hrR))
    have hc1 := tour_runs_cond_true (e := .bin .eq (.reg 4) (.const 0)) (v := 1) (st := ⟨mem, r2, pos⟩)
      (s₂ := body1)
      (by simp [Expr.eval, r2, hisr0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)])
      (by omega) hrun_e
    refine ⟨.returned (heap + 1), st', _, tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 hc1),
      x, hrep_e, hout_e, by simp [Outcome.value, hout_nil (Or.inl hrR)], hresp_e, ?_⟩
    rw [hphi_e]; have htl : 1 ≤ tourLog eCap := by simp [tourLog]
    have h100 : 100 ≤ TOUR_QUERY_MUL * (out.length + 1) * tourLog eCap := by
      have h1 : 1 ≤ (out.length + 1) * tourLog eCap := Nat.mul_pos (by omega) htl
      calc 100 ≤ TOUR_QUERY_MUL * 1 := by simp [TOUR_QUERY_MUL]
        _ ≤ TOUR_QUERY_MUL * ((out.length + 1) * tourLog eCap) := Nat.mul_le_mul_left _ h1
        _ = TOUR_QUERY_MUL * (out.length + 1) * tourLog eCap := by ring
    simp only [Expr.size] at hce ⊢; omega

/-- Op 4 (`listTour [b, r, heap]`): verified amortized run theorem. -/
theorem tourOp_listTour_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b r heap pos : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hr_lt : r < vCap) (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap)
    (hroom : heap + (3 + (coreTour s.ord s.rf r).length) < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpListBody C.splay.splay C.listOpen 13)
        (startState [b, r, heap] mem pos) o st' c ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        EndListAt st'.mem heap (coreTour s.ord s.rf r) ∧
        o.value = heap + 1 + (coreTour s.ord s.rf r).length ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap
          (3 + (coreTour s.ord s.rf r).length) mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * ((coreTour s.ord s.rf r).length + 1) * tourLog eCap +
            (tourRep R_ord vCap eCap).phi b x mem := by
  refine tourOpListBody_runs hLoc C C.openTests C.openTests_cost tourOpen_readyLaw
    C.openDesc_body C.findFirstOpen_body C.listOpen_body (by decide) ?_ ω h hr_lt hw hwide
    hfoot hzero hroom ?_ ?_
  · intro _ st M t rest u hN hF hroot hu
    have h13 : M (nodesBase b vCap eCap + 17 * u + 13) = (st.nodes u).sum.openCnt := by
      simpa [nodeAddr, tourLayout_offSum, tourLayout_stride] using (hN u hu).2.2.2.2.2.2.2.1.2.1
    rw [h13, ← hroot, hF.sum_openCnt (by simp)]; rfl
  · rintro (hnR | hnil)
    · simp only [coreTour, h.valid.compat.forest, ↓reduceDIte, hnR, ↓reduceIte]
    · simp only [coreTour, h.valid.compat.forest, ↓reduceDIte, hnil]
      split_ifs
      · rw [ordTourBlocks.eq_def]; rfl
      · rfl
  · intro t hrR _ ht_mem ht_map
    rw [← fullTour_filter_open s.ord h.valid.compat.forest hrR, ← ht_map, List.filter_map]
    congr 1; refine List.filter_congr fun u hu => ?_
    have hu_in := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hu⟩)
    have hu_ft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
      rw [← ht_map]; exact List.mem_map_of_mem hu
    obtain ⟨v, hv, _⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hu_ft
    rw [tourOpenRv, h.val_active u hu_in.1 hu_in.2 ⟨v, hv⟩]; rfl

/-- Op 9 (`listMarked [b, r, heap]`): verified amortized run theorem. -/
theorem tourOp_listMarked_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b r heap pos : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hr_lt : r < vCap) (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap)
    (hroom : heap + (3 + (tourMarkedList s r).length) < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpListBody C.splay.splay C.listMark 14)
        (startState [b, r, heap] mem pos) o st' c ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        EndListAt st'.mem heap (tourMarkedList s r) ∧
        o.value = heap + 1 + (tourMarkedList s r).length ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap
          (3 + (tourMarkedList s r).length) mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * ((tourMarkedList s r).length + 1) * tourLog eCap +
            (tourRep R_ord vCap eCap).phi b x mem := by
  refine tourOpListBody_runs hLoc C C.markTests C.markTests_cost tourMark_readyLaw
    C.markDesc_body C.findFirstMark_body C.listMark_body (by decide) ?_ ω h hr_lt hw hwide
    hfoot hzero hroom ?_ ?_
  · intro _ st M t rest u hN hF hroot hu
    have h14 : M (nodesBase b vCap eCap + 17 * u + 14) = (st.nodes u).sum.markCnt := by
      simpa [nodeAddr, tourLayout_offSum, tourLayout_stride] using (hN u hu).2.2.2.2.2.2.2.1.2.2.1
    rw [h14, ← hroot, hF.sum_markCnt (by simp)]; rfl
  · rintro (hnR | hnil)
    · simp only [tourMarkedList, coreTour, h.valid.compat.forest, ↓reduceDIte, hnR, ↓reduceIte, List.filter_nil]
    · simp only [tourMarkedList, coreTour, h.valid.compat.forest, ↓reduceDIte, hnil]
      split_ifs
      · rw [ordTourBlocks.eq_def]; rfl
      · rfl
  · intro t hrR _ ht_mem ht_map
    rw [← fullTour_filter_marked_eq_tourMarkedList h.valid hrR, ← ht_map, List.filter_map]
    congr 1; refine List.filter_congr fun u hu => ?_
    have hu_in := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hu⟩)
    have hu_ft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
      rw [← ht_map]; exact List.mem_map_of_mem hu
    obtain ⟨v, hv, _⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hu_ft
    rw [tourMarkRv, h.val_active u hu_in.1 hu_in.2 ⟨v, hv⟩]; rfl

end MinCostFlow.SparseCore.Program
