module

public import MinCostFlow.SparseCore.Program.TourOpsQuery
import Mathlib.Tactic

/-!
# First-marked query operation (`firstMarked`, Op 11)

Implements and verifies Op `11` (`firstMarked [b, r, heap]`) of `tourContract`: at any vertex
`r < vCap`, writes `0` at `heap` when `tourMarkedList s r = []` and `1 + endKey y` when
`(tourMarkedList s r).head? = some y`, returning `heap + 1` in `O(tourLog eCap)` amortized time
with `3` words of heap headroom. Matches `OutTourAt.firstMarked_runs`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Op 11 (`firstMarked`): args `[b, r, heap]`. Writes `0` or `1 + endKey y` at `heap` and
returns `heap + 1`. -/
def tourOpFirstMarkedBody (splayProc findFirstMarkProc : ℕ) : Stmt :=
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
        .call 8 findFirstMarkProc [.reg 5, .reg 4, .reg 6, .reg 2] ;;
        .cond (.bin .eq (.reg 8) (.const 0))
          (.store (.reg 2) (.const 0))
          (.store (.reg 2) (.bin .add (.const 1) (.load (.bin .add (.reg 7) (.reg 8))))) ;;
        .ret (.bin .add (.reg 2) (.const 1))))

theorem tourOpFirstMarkedBody_noRand (sP fmP : ℕ) :
    (tourOpFirstMarkedBody sP fmP).NoRand := by
  simp [tourOpFirstMarkedBody, Stmt.NoRand]

private theorem find?_eq_head?_filter {α : Type*} (p : α → Bool) :
    ∀ xs : List α, xs.find? p = (xs.filter p).head?
  | [] => rfl
  | a :: as => by
    cases h : p a with
    | true => simp only [List.find?, List.filter, h, List.head?_cons]
    | false => simp only [List.find?, List.filter, h]; exact find?_eq_head?_filter p as

/-- Verified amortized run theorem for Op `11` (`firstMarked`). -/
theorem tourOp_firstMarked_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b r heap pos dp fp : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayQueryProcs w p)
    (T : ReadyTests w p tourLayout tourMarkRs tourMarkRv) (hTc : T.cost = TOUR_TEST_COST)
    (hdp : p.procs[dp]? = some (descendBody dp C.lazy.pushDown T.sumTest T.valTest))
    (hfp : p.procs[fp]? = some (tourFindFirstBody dp T.sumTest C.splay.splay))
    (ω : ℕ → Bool) {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hr_lt : r < vCap) (hw : vCap + 2 * eCap + 4 < 2 ^ w) (hwide : 16 ≤ 2 ^ w)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 3 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpFirstMarkedBody C.splay.splay fp)
        (startState [b, r, heap] mem pos) o st' c ∧
      o.value = heap + 1 ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        st'.mem heap = (match (tourMarkedList s r).head? with
          | none => 0
          | some y => 1 + endKey y) ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 3
          mem o.value b x' st'.mem ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
  have hord_le : ordHandleOf b vCap eCap ≤ heap := h.fixed_le_heap hfoot
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hisr_lt : isRootBase b vCap + r < 2 ^ w := by
    simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  have hfe_lt : firstEndBase b + r < 2 ^ w := by
    simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
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
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hempty : ∀ (regs : ℕ → ℕ) (lpos : ℕ), regs 2 = heap → tourMarkedList s r = [] →
      ∃ st' c, c ≤ 20 ∧ st'.mem = mem ∧
        Runs w p ω (.store (.reg 2) (.const 0) ;; .ret (.bin .add (.reg 2) (.const 1)))
          ⟨mem, regs, lpos⟩ (.returned (heap + 1)) st' c ∧
        (tourRep R_ord vCap eCap).rep b s x st'.mem ∧
        st'.mem heap = 0 ∧
        (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 3
          mem (heap + 1) b x st'.mem := by
    intro regs lpos hreg2 hnil
    set mem1 := Function.update mem heap 0
    have hm1_eq : mem1 = mem := by
      funext a; by_cases ha : a = heap
      · subst ha; dsimp only [mem1]; rw [Function.update_self, hzero a (le_refl _)]
      · dsimp only [mem1]; rw [Function.update_of_ne ha]
    have hst : Runs w p ω (.store (.reg 2) (.const 0)) ⟨mem, regs, lpos⟩ .normal ⟨mem1, regs, lpos⟩ 3 :=
      runs_store_iff.mpr ⟨heap, 0, by simp [Expr.eval, hreg2], by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
    have hret : Runs w p ω (.ret (.bin .add (.reg 2) (.const 1))) ⟨mem1, regs, lpos⟩ (.returned (heap + 1))
        ⟨mem1, regs, lpos⟩ 4 :=
      runs_ret_iff.mpr ⟨heap + 1, by simp [Expr.eval, hreg2, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : heap + 1 < 2 ^ w)],
        rfl, rfl, rfl⟩
    refine ⟨⟨mem1, regs, lpos⟩, _, by omega, hm1_eq, tour_runs_seq_normal hst hret,
      hm1_eq ▸ h, by simp [mem1], ⟨by omega, by omega,
        fun a ha => by rw [hm1_eq]; exact hzero a (by omega),
        fun a _ _ => by rw [hm1_eq], fun _ ha => Or.inl ha⟩⟩
  by_cases hrR : r ∈ s.rf.R
  · have hisr1 : isr = 1 := by simp [isr, hrR]
    have hcond1 : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r2, pos⟩ = some 0 := by
      simp [Expr.eval, r2, hisr1, BinOp.eval, (by omega : 0 < 2 ^ w)]
    set r3 := Function.update r2 3 (firstEndBase b)
    set fe := match (s.ord r).head? with | none => 0 | some e => x.nodeOf (endKey e)
    set r4 := Function.update r3 4 fe
    have ha3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 3) (rBase := 0) (off := HDR_FIRST_END)
      (b := b) (val := firstEndBase b) (st := ⟨mem, r2, pos⟩)
      (by simp [r2, r1, s0, startState]) (by simp [HDR_FIRST_END]; omega) (by simp [HDR_FIRST_END]; omega)
      hhdr.2.2.2.2.1
    have ha4 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 3) (rIdx := 1)
      (base := firstEndBase b) (idx := r) (val := fe) (st := ⟨mem, r3, pos⟩)
      (by simp [r3]) (by simp [r3, r2, r1, s0, startState]) hfe_lt (h.firstEnd_mem r hr_lt)
    by_cases hord_nil : s.ord r = []
    · have hfe0 : fe = 0 := by simp [fe, hord_nil]
      have hcond2 : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r4, pos⟩ = some 1 := by
        simp [Expr.eval, r4, hfe0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
      have hml_nil : tourMarkedList s r = [] := by
        rw [← fullTour_filter_marked_eq_tourMarkedList h.valid hrR,
          (fullTour_eq_nil_iff h.valid.compat r).mpr hord_nil]; rfl
      obtain ⟨st', c', hc', hst'_mem, hrun_e, hrep', hmem', hresp'⟩ :=
        hempty r4 pos (by simp [r4, r3, r2, r1, s0, startState]) hml_nil
      have hfull : Runs w p ω (tourOpFirstMarkedBody C.splay.splay fp)
          (startState [b, r, heap] mem pos) (.returned (heap + 1)) st' _ :=
        tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2
          (tour_runs_cond_false hcond1 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
            (tour_runs_cond_true hcond2 (by omega) hrun_e)))))
      refine ⟨.returned (heap + 1), st', _, hfull, rfl, x, hrep', by simp [hml_nil, hmem'], hresp', ?_⟩
      rw [hst'_mem]; clear * - hc' htl; simp only [Expr.size, TOUR_QUERY_MUL] at *; omega
    · -- `r ∈ s.rf.R` and `s.ord r ≠ []`
      obtain ⟨a0, ha0⟩ : ∃ a0, (s.ord r).head? = some a0 :=
        Option.isSome_iff_exists.mp (by cases ho : s.ord r <;> simp_all)
      have ha0_mem : a0 ∈ s.ord r := List.mem_of_head? ha0
      have ha0_lt : endKey a0 < 2 * eCap := by
        have := h.valid.ordWithin.2.2 r a0 ha0_mem; simp only [endKey]; cases a0.2 <;> simp <;> omega
      have hfe_eq : fe = x.nodeOf (endKey a0) := by simp [fe, ha0]
      have hfe_nz : fe ≠ 0 := hfe_eq ▸ (h.active_end r hr_lt a0 ha0_mem).1
      have hft_ne : fullTour s.ord s.rf.F h.valid.compat.forest r ≠ [] :=
        fun h0 => hord_nil ((fullTour_eq_nil_iff h.valid.compat r).mp h0)
      obtain ⟨t, ht_eq, ht_mem, ht_map⟩ := h.comp_some r hrR hft_ne
      have hperm : x.trees.Perm (t :: x.trees.erase t) := List.perm_cons_erase ht_mem
      set rest := x.trees.erase t
      have hf_perm : TourForestInv x.numNodes x.st ([] ++ t :: rest) := (h.forestInv.perm hperm).1
      have hfe_mem : fe ∈ t.toList := by
        have ha0_ft : a0 ∈ fullTour s.ord s.rf.F h.valid.compat.forest r :=
          ((fullTour_spec h.valid.compat r).2 a0).mpr ⟨r, ha0_mem, connected_refl _ r⟩
        rw [← ht_map] at ha0_ft
        obtain ⟨u, hu, hue⟩ := List.mem_map.mp ha0_ft
        have hu_in := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hu⟩)
        have hku : x.keyOf u = endKey a0 := by rw [← hue, endKey_endOfKey']
        have hueq : u = fe := by rw [hfe_eq, ← hku, (h.keyOf_mem u hu_in.1 hu_in.2).2.2]
        exact hueq ▸ hu
      have hdep : t.depthOf fe < 2 * eCap + 2 :=
        lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hfe_mem)
          (le_trans (hf_perm.countNodes_le (by simp)) (by have := h.numNodes_le; omega))
      have hheap : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes heap 2 mem :=
        h.heapOk hfoot hzero (by omega) hwide
      -- Splay `fe` to root of `t`, then run `tourFindFirstBody`
      obtain ⟨t₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, _, hcost₁⟩ :=
        tourSplay_runs_amort (pos := pos) C.toTourSplayCoreProcs ω h.nodesAt hf_perm (h.valsOk hw)
          hfe_mem hdep (by omega) hheap
      set s₁ := SplayState.splay tourPayload x.st (2 * eCap + 2) fe
      have hinv₁' : TourForestInv x.numNodes s₁ (optTrees (some t₁) ++ rest) := by simpa [optTrees] using hinv₁
      have hheap₁ : HeapOk tourLayout w (nodesBase b vCap eCap) x.numNodes heap 2 st₁.mem :=
        ⟨hheap.rec_le, hheap.room, hfr₁.1, hheap.wide⟩
      obtain ⟨y, t₂?, s₂, o₂, st₂, c₂, hrun₂, hv₂, hn₂, hfr₂, hinv₂, _, hlist₂, hval₂, _, hfind₂, hcost₂⟩ :=
        tourFindFirstBody_runs (pos := st₁.pos) (fuel := 2 * eCap + 2) C T hTc tourMark_readyLaw hdp ω hn₁ hinv₁' hvals₁
          (by have := h.numNodes_le; omega) (by omega) hheap₁
      cases ht₂c : t₂? with
      | none =>
        rw [ht₂c] at hlist₂
        have : t₁.toList = [] := by simpa [optList] using hlist₂.symm
        cases t₁ <;> simp [AuxTree.toList] at hne₁ this
      | some t₂ =>
        rw [ht₂c] at hinv₂ hlist₂ hfind₂ hcost₂
        have hlist_eq : t₂.toList = t.toList := by simpa [optList] using hlist₂.trans hlist₁
        obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf_perm hfe_mem hdep
        have hval_all : ∀ u ≤ x.numNodes, (s₂.nodes u).val = (x.st.nodes u).val := fun u hu => by
          rw [hval₂ u hu, hval_sp u hu]
        -- Relate `t₁.toList.find?` to `(tourMarkedList s r).head?`
        have hmark_filter : (t.toList.filter fun u => (x.st.nodes u).val.isMarked).map
            (fun u => endOfKey (x.keyOf u)) = tourMarkedList s r := by
          rw [← fullTour_filter_marked_eq_tourMarkedList h.valid hrR, ← ht_map, List.filter_map]
          congr 1
          refine List.filter_congr fun u hu => ?_
          have hu_in := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hu⟩)
          have hu_ft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
            rw [← ht_map]; exact List.mem_map_of_mem hu
          obtain ⟨v', hv', _⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hu_ft
          rw [h.val_active u hu_in.1 hu_in.2 ⟨v', hv'⟩]; rfl
        have hfind_eq : ((t₁.toList.find? fun u => (s₁.nodes u).val.isMarked).map
            fun u => endOfKey (x.keyOf u)) = (tourMarkedList s r).head? := by
          rw [← hmark_filter, List.head?_map, ← find?_eq_head?_filter, hlist₁]
          congr 1
          refine list_find?_congr fun u hu => ?_
          rw [hval_sp u (hf_perm.mem_inCap (by simp) hu).2]
        -- Build updated concrete state `x'` (only `st` and `trees`/`compTree` changed)
        have hfr12 : TreeFrame tourLayout (nodesBase b vCap eCap) x.numNodes heap mem st₂.mem := hfr₁.trans hfr₂
        have hinv₂' : TourForestInv x.numNodes s₂ (t₂ :: rest) := by simpa [optTrees] using hinv₂
        obtain ⟨hrep_s2, hord_phi, hphi_eq, hfoot_x'⟩ :=
          h.replace_compTree_same_list hLoc hfoot hrR hperm ht_eq hlist_eq hn₂ hinv₂' hval_all hfr12.2
        set x' : TourConcrete R_ord.τ :=
          { x with st := s₂, trees := t₂ :: rest, compTree := Function.update x.compTree r (some t₂) }
        have hcond2 : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r4, pos⟩ = some 0 := by
          simp [Expr.eval, r4, hfe_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
        set r5 := Function.update r4 5 (nodesBase b vCap eCap)
        set r6 := Function.update r5 6 (2 * eCap + 2)
        set r7 := Function.update r6 7 (keyOfNodeBase b vCap eCap)
        have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_NODES_BASE)
          (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem, r4, pos⟩)
          (by simp [r4, r3, r2, r1, s0, startState]) (by simp [HDR_NODES_BASE]; omega)
          (by simp [HDR_NODES_BASE]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
        have ha6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_FUEL)
          (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r5, pos⟩)
          (by simp [r5, r4, r3, r2, r1, s0, startState]) (by simp [HDR_FUEL]; omega)
          (by simp [HDR_FUEL]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have ha7 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_KEY_OF_NODE)
          (b := b) (val := keyOfNodeBase b vCap eCap) (st := ⟨mem, r6, pos⟩)
          (by simp [r6, r5, r4, r3, r2, r1, s0, startState]) (by simp [HDR_KEY_OF_NODE]; omega)
          (by simp [HDR_KEY_OF_NODE]; omega) hhdr.2.2.2.2.2.2.2.2.1
        set st1_c : State := { st₁ with regs := Function.update r7 8 o₁.value }
        set st2_c : State := { st₂ with regs := Function.update st1_c.regs 8 o₂.value }
        have hc1 := runs_call_regs4 8 5 4 6 2 (st := ⟨mem, r7, pos⟩) C.splay.splay_body
          (by simp [r7, r6, r5]) (by simp [r7, r6, r5, r4]) (by simp [r7, r6])
          (by simp [r7, r6, r5, r4, r3, r2, r1, s0, startState]) hrun₁
        have hrun₂' : Runs w p ω (tourFindFirstBody dp T.sumTest C.splay.splay)
            (startState [nodesBase b vCap eCap, fe, 2 * eCap + 2, heap] st₁.mem st₁.pos) o₂ st₂ c₂ := by
          simpa [optRoot, hroot₁] using hrun₂
        have hc2 := runs_call_regs4 8 5 4 6 2 (st := st1_c) hfp
          (by simp [st1_c, r7, r6, r5]) (by simp [st1_c, r7, r6, r5, r4])
          (by simp [st1_c, r7, r6]) (by simp [st1_c, r7, r6, r5, r4, r3, r2, r1, s0, startState]) hrun₂'
        have hlog : Nat.log 2 (x.numNodes + 2) + 1 ≤ 2 * tourLog eCap := tourLog_of_le h.numNodes_le
        have hcost_fin : ∀ cTail, cTail ≤ 100 →
            cTail + c₁ + c₂ + (tourRep R_ord vCap eCap).phi b x' st₂.mem ≤
              TOUR_QUERY_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
          intro cTail hcTail
          have hmul : (TOUR_SPLAY_AMORT + TOUR_FIND_AMORT) * (Nat.log 2 (x.numNodes + 2) + 1) ≤
              (TOUR_SPLAY_AMORT + TOUR_FIND_AMORT) * (2 * tourLog eCap) := Nat.mul_le_mul_left _ hlog
          simp only [tourRep, tourPhi, x']
          rw [hord_phi, hphi_eq]
          simp only [optTrees, Option.toList, List.cons_append, List.nil_append] at hcost₁ hcost₂
          clear * - hcost₁ hcost₂ hcTail hmul htl
          simp only [TOUR_PHI_MULT, TOUR_SPLAY_AMORT, TOUR_FIND_AMORT, TOUR_QUERY_MUL] at *
          omega
        -- Split on whether `find?` returned `none` (`y = 0`) or `some y₀` (`y = y₀ ≠ 0`)
        cases hfn : t₁.toList.find? (fun u => (s₁.nodes u).val.isMarked) with
        | none =>
          have hml_head : (tourMarkedList s r).head? = none := by rw [← hfind_eq, hfn]; rfl
          have hy0 : y = 0 := by simp [optList, tourMarkRv, hfn] at hfind₂; exact hfind₂.1
          have hcond3 : (Expr.bin .eq (.reg 8) (.const 0)).eval w st2_c = some 1 := by
            simp [Expr.eval, st2_c, hv₂, hy0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
          set memF := Function.update st₂.mem heap 0
          have hmemF_eq : memF = st₂.mem := by
            funext a; by_cases ha : a = heap
            · subst ha; dsimp only [memF]; rw [Function.update_self, hfr12.1 a (le_refl _)]
            · dsimp only [memF]; rw [Function.update_of_ne ha]
          have hstF : Runs w p ω (.store (.reg 2) (.const 0)) st2_c .normal { st2_c with mem := memF } 3 :=
            runs_store_iff.mpr ⟨heap, 0,
              by simp [Expr.eval, st2_c, st1_c, r7, r6, r5, r4, r3, r2, r1, s0, startState],
              by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
          have hretF : Runs w p ω (.ret (.bin .add (.reg 2) (.const 1))) { st2_c with mem := memF }
              (.returned (heap + 1)) { st2_c with mem := memF } 4 :=
            runs_ret_iff.mpr ⟨heap + 1,
              by simp [Expr.eval, st2_c, st1_c, r7, r6, r5, r4, r3, r2, r1, s0, startState,
                BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : heap + 1 < 2 ^ w)], rfl, rfl, rfl⟩
          have hfull : Runs w p ω (tourOpFirstMarkedBody C.splay.splay fp)
              (startState [b, r, heap] mem pos) (.returned (heap + 1)) { st2_c with mem := memF } _ :=
            tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2
              (tour_runs_cond_false hcond1 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
                (tour_runs_cond_false hcond2 (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7
                  (tour_runs_seq_normal hc1 (tour_runs_seq_normal hc2
                    (tour_runs_seq_normal (tour_runs_cond_true hcond3 (by omega) hstF) hretF)))))))))))
          have hresp : (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 3
              mem (heap + 1) b x' memF := by
            rw [hmemF_eq]
            refine ⟨by omega, by omega, fun a ha => hfr12.1 a (by omega), fun a ha hnf => ?_, fun a ha => Or.inl ha⟩
            refine hfr12.2 a ha fun hrec => hnf (Or.inl ?_)
            have h1 := inRecords_lt_ordHandle_of_le h.numNodes_le hrec; simp [nodesBase] at h1; exact ⟨by omega, h1.2⟩
          refine ⟨.returned (heap + 1), { st2_c with mem := memF }, _, hfull, rfl, x',
            hmemF_eq ▸ hrep_s2, by simp [hml_head, memF], hresp, ?_⟩
          have hc := hcost_fin 100 (le_refl _)
          rw [hmemF_eq]
          clear * - hc; simp only [Expr.size] at *; omega
        | some y₀ =>
          have hml_head : (tourMarkedList s r).head? = some (endOfKey (x.keyOf y₀)) := by
            rw [← hfind_eq, hfn]; rfl
          have hy_eq : y = y₀ := by simp [optList, tourMarkRv, hfn] at hfind₂; exact hfind₂.1
          have hy_mem_t : y ∈ t.toList := by
            rw [hy_eq, ← hlist₁]; exact List.mem_of_find?_eq_some hfn
          have hy_in : 1 ≤ y ∧ y ≤ x.numNodes :=
            (h.nodes_exact y).mp (List.mem_flatMap.mpr ⟨t, ht_mem, hy_mem_t⟩)
          have hkm := h.keyOf_mem y hy_in.1 hy_in.2
          have hy_nz : y ≠ 0 := by omega
          have hcond3 : (Expr.bin .eq (.reg 8) (.const 0)).eval w st2_c = some 0 := by
            simp [Expr.eval, st2_c, hv₂, hy_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
          have hkey_addr : keyOfNodeBase b vCap eCap + y < 2 ^ w := by
            have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
          have hm2_key : st₂.mem (keyOfNodeBase b vCap eCap + y) = x.keyOf y := by
            have hnr : ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes (keyOfNodeBase b vCap eCap + y) := fun hrec => by
              have h1 := (inRecords_lt_ordHandle_of_le h.numNodes_le hrec).1; have := h.numNodes_le
              simp only [keyOfNodeBase, nodesBase] at h1; omega
            rw [hfr12.2 _ (by have := h.numNodes_le; simp [keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) hnr]
            exact hkm.1
          set memF := Function.update st₂.mem heap (1 + x.keyOf y)
          have hstF : Runs w p ω (.store (.reg 2) (.bin .add (.const 1) (.load (.bin .add (.reg 7) (.reg 8)))))
              st2_c .normal { st2_c with mem := memF } _ :=
            runs_store_iff.mpr ⟨heap, 1 + x.keyOf y,
              by simp [Expr.eval, st2_c, st1_c, r7, r6, r5, r4, r3, r2, r1, s0, startState],
              by simp [Expr.eval, st2_c, st1_c, r7, hv₂, BinOp.eval, hkey_addr, hm2_key,
                (by omega : 1 < 2 ^ w), (by omega : 1 + x.keyOf y < 2 ^ w)], rfl, rfl, rfl⟩
          have hretF : Runs w p ω (.ret (.bin .add (.reg 2) (.const 1))) { st2_c with mem := memF }
              (.returned (heap + 1)) { st2_c with mem := memF } 4 :=
            runs_ret_iff.mpr ⟨heap + 1,
              by simp [Expr.eval, st2_c, st1_c, r7, r6, r5, r4, r3, r2, r1, s0, startState,
                BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : heap + 1 < 2 ^ w)], rfl, rfl, rfl⟩
          have hfull : Runs w p ω (tourOpFirstMarkedBody C.splay.splay fp)
              (startState [b, r, heap] mem pos) (.returned (heap + 1)) { st2_c with mem := memF } _ :=
            tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2
              (tour_runs_cond_false hcond1 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
                (tour_runs_cond_false hcond2 (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7
                  (tour_runs_seq_normal hc1 (tour_runs_seq_normal hc2
                    (tour_runs_seq_normal (tour_runs_cond_false hcond3 hstF) hretF)))))))))))
          have hrepF : (tourRep R_ord vCap eCap).rep b s x' memF :=
            (tourRep_local hLoc vCap eCap b s x' st₂.mem memF fun a ha => by
              have hlt : a < heap := hfoot a ((hfoot_x' a).mp ha)
              exact (Function.update_of_ne (by omega) _ _).symm).1 hrep_s2
          have hphiF : (tourRep R_ord vCap eCap).phi b x' memF = (tourRep R_ord vCap eCap).phi b x' st₂.mem :=
            ((tourRep_local hLoc vCap eCap b s x' st₂.mem memF fun a ha => by
              have hlt : a < heap := hfoot a ((hfoot_x' a).mp ha)
              exact (Function.update_of_ne (by omega) _ _).symm).2).symm
          have hresp : (tourRep R_ord vCap eCap).Respects ((tourRep R_ord vCap eCap).foot b x) heap 3
              mem (heap + 1) b x' memF := by
            refine ⟨by omega, by omega,
              fun a ha => by rw [show memF a = st₂.mem a from Function.update_of_ne (by omega) _ _]; exact hfr12.1 a (by omega),
              fun a ha hnf => by
                rw [show memF a = st₂.mem a from Function.update_of_ne (by omega) _ _]
                refine hfr12.2 a ha fun hrec => hnf (Or.inl ?_)
                have h1 := inRecords_lt_ordHandle_of_le h.numNodes_le hrec; simp [nodesBase] at h1; exact ⟨by omega, h1.2⟩,
              fun a ha => Or.inl ha⟩
          refine ⟨.returned (heap + 1), { st2_c with mem := memF }, _, hfull, rfl, x', hrepF,
            by simp [hml_head, memF, hy_eq, endKey_endOfKey'], hresp, ?_⟩
          rw [hphiF]
          have hc := hcost_fin 100 (le_refl _)
          clear * - hc; simp only [Expr.size] at *; omega
  · -- `r ∉ s.rf.R`: `tourMarkedList s r = []`
    have hisr0 : isr = 0 := by simp [isr, hrR]
    have hcond1 : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r2, pos⟩ = some 1 := by
      simp [Expr.eval, r2, hisr0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
    have hml_nil : tourMarkedList s r = [] := by simp [tourMarkedList, coreTour, hrR]
    obtain ⟨st', c', hc', hst'_mem, hrun_e, hrep', hmem', hresp'⟩ :=
      hempty r2 pos (by simp [r2, r1, s0, startState]) hml_nil
    have hfull : Runs w p ω (tourOpFirstMarkedBody C.splay.splay fp)
        (startState [b, r, heap] mem pos) (.returned (heap + 1)) st' _ :=
      tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_cond_true hcond1 (by omega) hrun_e))
    refine ⟨.returned (heap + 1), st', _, hfull, rfl, x, hrep', by simp [hml_nil, hmem'], hresp', ?_⟩
    rw [hst'_mem]; clear * - hc' htl; simp only [Expr.size, TOUR_QUERY_MUL] at *; omega

end MinCostFlow.SparseCore.Program
