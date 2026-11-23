module

public import MinCostFlow.SparseCore.Program.TourOpsListExact
import Mathlib.Tactic

/-!
# Exact-space length and owner queries (`lenCoreTour`, `rootOfExact`, `vertOwner`)

Implements and verifies three exact-space (`1` word, zero footprint growth) query operations:
- `tourOpLenBody` (Op `12`, `lenCoreTour [b, r, heap]`): writes `(coreTour s.ord s.rf r).length`
  at `heap` and returns `heap + 1`, in amortized cost `≤ TOUR_QUERY_MUL * tourLog eCap` using
  zero-scratch `splayLoop`.
- `tourOpRootOfExactBody` (exact-space Op `10`, core-tour owner `[b, keyX, heap]`): writes
  `s.rf.root (ordSrc s.ord (endOfKey keyX))` at `heap` and returns `heap + 1`, in amortized cost
  `≤ TOUR_QUERY_MUL * tourLog eCap` using zero-scratch `splayLoop`.
- `tourOpVertOwnerBody` (Op `13`, `vertOwner [b, keyX, heap]`): writes
  `ordSrc s.ord (endOfKey keyX)` at `heap` and returns `heap + 1`, in worst-case `O(1)` time
  (`≤ 60` steps) via `endOwner` and `vertOfSlot`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## WordRAM bodies -/

/-- Op `12` (`lenCoreTour`): args `[b, r, heap]`. Writes `(coreTour s.ord s.rf r).length` at
`heap` and returns `heap + 1` with zero splay scratch. -/
def tourOpLenBody (splayLoopProc : ℕ) : Stmt :=
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
        .call 7 splayLoopProc [.reg 5, .reg 4, .reg 6, .reg 2] ;;
        .assign 7 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 17) (.reg 4))) (.const 13))) ;;
        .store (.reg 2) (.reg 7) ;;
        .ret (.bin .add (.reg 2) (.const 1))))

/-- Exact-space core-tour owner query (`rootOf` / `owner`): args `[b, keyX, heap]`. Writes
`s.rf.root (ordSrc s.ord (endOfKey keyX))` at `heap` and returns `heap + 1` with zero scratch. -/
def tourOpRootOfExactBody (splayLoopProc : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const HDR_NODE_OF_END))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const HDR_NODES_BASE))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const HDR_FUEL))) ;;
  .call 7 splayLoopProc [.reg 5, .reg 4, .reg 6, .reg 2] ;;
  .assign 7 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 17) (.reg 4))) (.const 15))) ;;
  .store (.reg 2) (.bin .sub (.reg 7) (.const 1)) ;;
  .ret (.bin .add (.reg 2) (.const 1))

/-- Op `13` (`vertOwner`): args `[b, keyX, heap]`. Writes `ordSrc s.ord (endOfKey keyX)` at
`heap` and returns `heap + 1` in `O(1)` time. -/
def tourOpVertOwnerBody : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const HDR_END_OWNER))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .assign 4 (.bin .sub (.reg 4) (.const 1)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const HDR_NEXT_ARR))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const HDR_ECAP))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const HDR_VCAP))) ;;
  .assign 5 (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 6))) (.reg 7)) ;;
  .assign 6 (.load (.bin .add (.reg 5) (.reg 4))) ;;
  .cond (.reg 6)
    (.assign 6 (.bin .sub (.reg 6) (.const 1)))
    (.assign 6 (.reg 4)) ;;
  .store (.reg 2) (.reg 6) ;;
  .ret (.bin .add (.reg 2) (.const 1))

theorem tourOpsLenOwner_noRand (slP : ℕ) :
    (tourOpLenBody slP).NoRand ∧
    (tourOpRootOfExactBody slP).NoRand ∧
    tourOpVertOwnerBody.NoRand := by
  simp [tourOpLenBody, tourOpRootOfExactBody, tourOpVertOwnerBody, Stmt.NoRand]

/-! ## Verified run theorems -/

/-- Exact-space Op `12` (`lenCoreTour [b, r, heap]`): writes `(coreTour s.ord s.rf r).length` at
`heap`, returns `heap + 1`, never grows `tourFoot`, and pays `≤ TOUR_QUERY_MUL * tourLog eCap`. -/
theorem tourOp_len_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b r heap pos : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayCoreProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hr_lt : r < vCap)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 1 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpLenBody C.splay.loop)
        (startState [b, r, heap] mem pos) o st' c ∧
      o.value = heap + 1 ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        st'.mem heap = (coreTour s.ord s.rf r).length ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < heap, ¬tourFoot R_ord vCap eCap b x a → st'.mem a = mem a) ∧
        (∀ a, tourFoot R_ord vCap eCap b x' a → tourFoot R_ord vCap eCap b x a) ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
  classical
  have hord_le : ordHandleOf b vCap eCap ≤ heap := h.fixed_le_heap hfoot
  have hwide : 16 ≤ 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hw : vCap + 2 * eCap + 4 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hisr_lt : isRootBase b vCap + r < 2 ^ w := by simp [isRootBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  have hfe_lt : firstEndBase b + r < 2 ^ w := by simp [firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hlog : Nat.log 2 (x.numNodes + 2) + 1 ≤ 2 * tourLog eCap := tourLog_of_le h.numNodes_le
  have hhdr := h.header
  set s0 : State := startState [b, r, heap] mem pos
  set r1 := Function.update s0.regs 3 (isRootBase b vCap)
  set isr := if r ∈ s.rf.R then 1 else 0
  set r2 := Function.update r1 4 isr
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 3) (rBase := 0) (off := HDR_IS_ROOT)
    (b := b) (val := isRootBase b vCap) (st := s0) (by simp [s0, startState])
    (by simp only [HDR_IS_ROOT]; omega) (by simp only [HDR_IS_ROOT]; omega) hhdr.2.2.2.2.2.1
  have ha2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 3) (rIdx := 1)
    (base := isRootBase b vCap) (idx := r) (val := isr) (st := ⟨mem, r1, pos⟩)
    (by simp [r1]) (by simp [r1, s0, startState]) hisr_lt (h.isRoot_mem r hr_lt)
  by_cases hrR : r ∈ s.rf.R
  · have hisr1 : isr = 1 := by simp [isr, hrR]
    have hc_isr : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r2, pos⟩ = some 0 := by
      simp [Expr.eval, r2, hisr1, BinOp.eval, (by omega : 0 < 2 ^ w)]
    set fe := mem (firstEndBase b + r)
    set r3 := Function.update r2 3 (firstEndBase b)
    set r4 := Function.update r3 4 fe
    have ha3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 3) (rBase := 0) (off := HDR_FIRST_END)
      (b := b) (val := firstEndBase b) (st := ⟨mem, r2, pos⟩) (by simp [r2, r1, s0, startState])
      (by simp only [HDR_FIRST_END]; omega) (by simp only [HDR_FIRST_END]; omega) hhdr.2.2.2.2.1
    have ha4 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 3) (rIdx := 1)
      (base := firstEndBase b) (idx := r) (val := fe) (st := ⟨mem, r3, pos⟩)
      (by simp [r3]) (by simp [r3, r2, r1, s0, startState]) hfe_lt rfl
    cases hord_r : s.ord r with
    | nil =>
      have hfe0 : fe = 0 := by simp [fe, h.firstEnd_mem r hr_lt, hord_r]
      have hct0 : coreTour s.ord s.rf r = [] := by
        rw [← fullTour_filter_open s.ord h.valid.compat.forest hrR, (fullTour_eq_nil_iff h.valid.compat r).mpr hord_r]; rfl
      have hc_fe : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r4, pos⟩ = some 1 := by
        simp [Expr.eval, r4, hfe0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
      set m1 := Function.update mem heap 0
      have hst : Runs w p ω (.store (.reg 2) (.const 0)) ⟨mem, r4, pos⟩ .normal ⟨m1, r4, pos⟩ 3 :=
        runs_store_iff.mpr ⟨heap, 0, by simp [Expr.eval, r4, r3, r2, r1, s0, startState],
          by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
      have hret : Runs w p ω (.ret (.bin .add (.reg 2) (.const 1))) ⟨m1, r4, pos⟩ (.returned (heap + 1)) ⟨m1, r4, pos⟩ 4 :=
        runs_ret_iff.mpr ⟨heap + 1, by simp [Expr.eval, r4, r3, r2, r1, s0, startState, BinOp.eval,
          (by omega : 1 < 2 ^ w), hroom], rfl, rfl, rfl⟩
      have hloc := (tourRep_local hLoc vCap eCap) b s x mem m1 fun a ha =>
        (Function.update_of_ne (Nat.ne_of_lt (hfoot a ha)) _ _).symm
      refine ⟨.returned (heap + 1), ⟨m1, r4, pos⟩, _,
        tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_cond_false hc_isr
          (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4 (tour_runs_cond_true hc_fe (by omega) (tour_runs_seq_normal hst hret)))))),
        rfl, x, hloc.1 h, by simp [m1, hct0],
        fun a ha => by dsimp only [m1]; rw [Function.update_of_ne (by simp only [Outcome.value] at ha; omega)]; exact hzero a (by simp only [Outcome.value] at ha; omega),
        fun a ha _ => Function.update_of_ne (Nat.ne_of_lt ha) _ _, fun _ ha => ha, ?_⟩
      rw [← hloc.2]; clear * - htl; simp only [Expr.size, TOUR_QUERY_MUL]; nlinarith
    | cons aHead aTail =>
      have hhead : (s.ord r).head? = some aHead := by simp [hord_r]
      have haHead_mem : aHead ∈ s.ord r := by simp [hord_r]
      have hfe_eq : fe = x.nodeOf (endKey aHead) := by simp [fe, h.firstEnd_mem r hr_lt, hhead]
      obtain ⟨_, _, _, _, hfe1, hfe_le, _, t, rest, hct_r, hperm_r, ht_map, hfe_t⟩ :=
        h.mem_compTree_of_active haHead_mem
      have hrr : s.rf.root r = r := h.valid.root_eq_of_mem (h.valid.roots_sub hrR) hrR (connected_refl _ _)
      rw [hrr] at hct_r ht_map
      have hfe_nz : fe ≠ 0 := by omega
      have hc_fe : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r4, pos⟩ = some 0 := by
        simp [Expr.eval, r4, hfe_nz, BinOp.eval, (by omega : 0 < 2 ^ w)]
      set r5 := Function.update r4 5 (nodesBase b vCap eCap)
      set r6 := Function.update r5 6 (2 * eCap + 2)
      have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_NODES_BASE)
        (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem, r4, pos⟩) (by simp [r4, r3, r2, r1, s0, startState])
        (by simp only [HDR_NODES_BASE]; omega) (by simp only [HDR_NODES_BASE]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
      have ha6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_FUEL)
        (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r5, pos⟩) (by simp [r5, r4, r3, r2, r1, s0, startState])
        (by simp only [HDR_FUEL]; omega) (by simp only [HDR_FUEL]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hinv0 : TourForestInv x.numNodes x.st (t :: rest) := (h.forestInv.perm hperm_r).1
      have hfe_dep : t.depthOf fe < 2 * eCap + 2 :=
        lt_of_lt_of_le (auxTree_depthOf_lt_countNodes (hfe_eq ▸ hfe_t))
          (le_trans (hinv0.countNodes_le (t := t) (by simp)) (by have := h.numNodes_le; omega))
      have hrec_le : tourLayout.nodeAddr (nodesBase b vCap eCap) (x.numNodes + 1) ≤ heap := by
        have := h.numNodes_le; simp [NodeLayout.nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
      obtain ⟨t', oS, stS, cS, hrunS, hnS, hfrS, hinvS, _, _, ht'_root, ht'_list, _, hcS⟩ :=
        tourSplayLoop_runs_amort (pre := []) (post := rest) (pos := pos) C ω
          h.nodesAt hinv0 (h.valsOk hw) (hfe_eq ▸ hfe_t) hfe_dep (by omega) ⟨hrec_le, by omega, hzero, hwide⟩
      obtain ⟨_, _, _, _, _, _, hvalS, _⟩ := tourSplay_preserves (pre := []) (post := rest) hinv0 (hfe_eq ▸ hfe_t) hfe_dep
      have hcallS := runs_call_regs4 7 5 4 6 2 (st := ⟨mem, r6, pos⟩) C.splay.loop_body
        (by simp [r6, r5]) (by simp [r6, r5, r4]) (by simp [r6]) (by simp [r6, r5, r4, r3, r2, r1, s0, startState]) hrunS
      set r7 := Function.update r6 7 oS.value
      set sS := SplayState.splay tourPayload x.st (2 * eCap + 2) fe
      have hfe_cap : fe ≤ x.numNodes := by omega
      have hopen_mem : stS.mem (nodesBase b vCap eCap + 17 * fe + 13) = (sS.nodes fe).sum.openCnt := by
        have hnd := hnS fe hfe_cap
        have hoff : tourLayout.offSum = 12 := rfl
        simpa [NodeLayout.nodeAddr, tourLayout_stride, hoff, Nat.add_assoc] using hnd.2.2.2.2.2.2.2.1.2.1
      have hlen_eq : (sS.nodes fe).sum.openCnt = (coreTour s.ord s.rf r).length := by
        rw [← ht'_root, hinvS.sum_openCnt (t := t') (by simp), ← fullTour_filter_open s.ord h.valid.compat.forest hrR,
          ← ht_map, ← ht'_list, List.filter_map, List.length_map]
        congr 1; refine List.filter_congr fun u hu => ?_
        have hu_t : u ∈ t.toList := by rwa [← ht'_list]
        have hu_in := (h.nodes_exact u).mp (List.mem_flatMap.mpr ⟨t, hperm_r.mem_iff.mpr (by simp), hu_t⟩)
        have hft : endOfKey (x.keyOf u) ∈ fullTour s.ord s.rf.F h.valid.compat.forest r := by
          rw [← ht_map]; exact List.mem_map_of_mem hu_t
        obtain ⟨w', hw', _⟩ := ((fullTour_spec h.valid.compat r).2 _).mp hft
        rw [hvalS u hu_in.2, h.val_active u hu_in.1 hu_in.2 ⟨w', hw'⟩]; rfl
      have hAt : nodesBase b vCap eCap + 17 * fe + 13 < 2 ^ w := by
        have := hrec_le; simp [NodeLayout.nodeAddr, tourLayout_stride] at this; omega
      set ans := (coreTour s.ord s.rf r).length
      set r8 := Function.update r7 7 ans
      set m1 := Function.update stS.mem heap ans
      have ha7 : Runs w p ω (.assign 7 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 17) (.reg 4))) (.const 13))))
          { stS with regs := r7 } .normal { stS with regs := r8 } 9 :=
        runs_assign_iff.mpr ⟨ans, by
          simp [Expr.eval, r7, r6, r5, r4, BinOp.eval, (by omega : 17 < 2 ^ w), (by omega : 17 * fe < 2 ^ w),
            (by omega : nodesBase b vCap eCap + 17 * fe < 2 ^ w), (by omega : 13 < 2 ^ w), hAt, hopen_mem, hlen_eq, ans],
          rfl, rfl, rfl⟩
      have hst : Runs w p ω (.store (.reg 2) (.reg 7)) { stS with regs := r8 } .normal { stS with mem := m1, regs := r8 } 3 :=
        runs_store_iff.mpr ⟨heap, ans, by simp [Expr.eval, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState],
          by simp [Expr.eval, r8], rfl, rfl, rfl⟩
      have hret : Runs w p ω (.ret (.bin .add (.reg 2) (.const 1))) { stS with mem := m1, regs := r8 }
          (.returned (heap + 1)) { stS with mem := m1, regs := r8 } 4 :=
        runs_ret_iff.mpr ⟨heap + 1, by simp [Expr.eval, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState, BinOp.eval,
          (by omega : 1 < 2 ^ w), hroom], rfl, rfl, rfl⟩
      have hn1 : tourLayout.NodesAt m1 (nodesBase b vCap eCap) x.numNodes sS :=
        NodesAt.congr tourLayout hnS fun a ha =>
          Function.update_of_ne (Nat.ne_of_lt (lt_of_lt_of_le (inRecords_lt_ordHandle_of_le h.numNodes_le ha).2 hord_le)) _ _
      have hagree1 : ∀ a < heap, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a → m1 a = mem a :=
        fun a ha hnr => by dsimp only [m1]; rw [Function.update_of_ne (Nat.ne_of_lt ha)]; exact hfrS.2 a ha hnr
      obtain ⟨hrep1, hphi_ord, hphi_perm, hfoot_eq⟩ :=
        h.replace_compTree_same_list hLoc hfoot hrR hperm_r hct_r ht'_list hn1
          (by simpa using hinvS) (fun u hu => hvalS u hu) hagree1
      refine ⟨.returned (heap + 1), { stS with mem := m1, regs := r8 }, _,
        tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_cond_false hc_isr
          (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4 (tour_runs_cond_false hc_fe
            (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal hcallS
              (tour_runs_seq_normal ha7 (tour_runs_seq_normal hst hret)))))))))),
        rfl, _, hrep1, by simp [m1, ans],
        fun a ha => by dsimp only [m1]; rw [Function.update_of_ne (by simp only [Outcome.value] at ha; omega)]; exact hfrS.1 a (by simp only [Outcome.value] at ha; omega),
        fun a ha hnf => hagree1 a ha fun hin => hnf (Or.inl ⟨by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hin).1; simp [nodesBase] at this ⊢; omega,
          (inRecords_lt_ordHandle_of_le h.numNodes_le hin).2⟩),
        fun a ha => (hfoot_eq a).mp ha, ?_⟩
      simp only [List.nil_append] at hcS
      have hS' : cS + TOUR_PHI_MULT * forestPhi (t' :: rest) ≤
          TOUR_PHI_MULT * forestPhi (t :: rest) + TOUR_SPLAY_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) := by
        clear * - hcS; omega
      dsimp only [tourRep, tourPhi] at hphi_ord ⊢
      rw [hphi_perm, ← hphi_ord]
      have hlog_mul : TOUR_SPLAY_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) ≤ TOUR_SPLAY_AMORT * (2 * tourLog eCap) :=
        Nat.mul_le_mul_left _ hlog
      clear * - hS' hlog_mul htl
      simp only [Expr.size, TOUR_SPLAY_AMORT, TOUR_QUERY_MUL] at *
      nlinarith
  · have hisr0 : isr = 0 := by simp [isr, hrR]
    have hct0 : coreTour s.ord s.rf r = [] := by simp [coreTour, hrR]
    have hc_isr : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r2, pos⟩ = some 1 := by
      simp [Expr.eval, r2, hisr0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
    set m1 := Function.update mem heap 0
    have hst : Runs w p ω (.store (.reg 2) (.const 0)) ⟨mem, r2, pos⟩ .normal ⟨m1, r2, pos⟩ 3 :=
      runs_store_iff.mpr ⟨heap, 0, by simp [Expr.eval, r2, r1, s0, startState],
        by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
    have hret : Runs w p ω (.ret (.bin .add (.reg 2) (.const 1))) ⟨m1, r2, pos⟩ (.returned (heap + 1)) ⟨m1, r2, pos⟩ 4 :=
      runs_ret_iff.mpr ⟨heap + 1, by simp [Expr.eval, r2, r1, s0, startState, BinOp.eval,
        (by omega : 1 < 2 ^ w), hroom], rfl, rfl, rfl⟩
    have hloc := (tourRep_local hLoc vCap eCap) b s x mem m1 fun a ha =>
      (Function.update_of_ne (Nat.ne_of_lt (hfoot a ha)) _ _).symm
    refine ⟨.returned (heap + 1), ⟨m1, r2, pos⟩, _,
      tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_cond_true hc_isr (by omega) (tour_runs_seq_normal hst hret))),
      rfl, x, hloc.1 h, by simp [m1, hct0],
      fun a ha => by dsimp only [m1]; rw [Function.update_of_ne (by simp only [Outcome.value] at ha; omega)]; exact hzero a (by simp only [Outcome.value] at ha; omega),
      fun a ha _ => Function.update_of_ne (Nat.ne_of_lt ha) _ _, fun _ ha => ha, ?_⟩
    rw [← hloc.2]; clear * - htl; simp only [Expr.size, TOUR_QUERY_MUL]; nlinarith

/-- Exact-space core-tour owner (`rootOfExact [b, keyX, heap]`): writes
`s.rf.root (ordSrc s.ord (endOfKey keyX))` at `heap`, returns `heap + 1`, never grows `tourFoot`,
and pays `≤ TOUR_QUERY_MUL * tourLog eCap`. -/
theorem tourOp_rootOf_exact_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b keyX heap pos : ℕ} {p : Program}
    (hLoc : R_ord.Local) (C : TourSplayCoreProcs w p) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hact : ∃ u, endOfKey keyX ∈ s.ord u)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 1 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (tourOpRootOfExactBody C.splay.loop)
        (startState [b, keyX, heap] mem pos) o st' c ∧
      o.value = heap + 1 ∧
      ∃ x', (tourRep R_ord vCap eCap).rep b s x' st'.mem ∧
        st'.mem heap = s.rf.root (ordSrc s.ord (endOfKey keyX)) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < heap, ¬tourFoot R_ord vCap eCap b x a → st'.mem a = mem a) ∧
        (∀ a, tourFoot R_ord vCap eCap b x' a → tourFoot R_ord vCap eCap b x a) ∧
        c + (tourRep R_ord vCap eCap).phi b x' st'.mem ≤
          TOUR_QUERY_MUL * tourLog eCap + (tourRep R_ord vCap eCap).phi b x mem := by
  classical
  obtain ⟨v, hxv⟩ := hact
  have hord_le : ordHandleOf b vCap eCap ≤ heap := h.fixed_le_heap hfoot
  have hwide : 16 ≤ 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hw : vCap + 2 * eCap + 4 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have htl : 1 ≤ tourLog eCap := by simp [tourLog]
  have hlog : Nat.log 2 (x.numNodes + 2) + 1 ≤ 2 * tourLog eCap := tourLog_of_le h.numNodes_le
  have hhdr := h.header
  obtain ⟨_, hrR, hrLt, hkx_lt, hu1, hu_le, _, t, rest, hct_r, hperm_r, ht_map, hu_t⟩ :=
    h.mem_compTree_of_active hxv
  rw [endKey_endOfKey'] at hkx_lt hu1 hu_le hu_t
  set r := s.rf.root v
  set u := x.nodeOf keyX
  have hsrc : ordSrc s.ord (endOfKey keyX) = v := h.valid.compat.ordSrc_eq hxv
  set s0 : State := startState [b, keyX, heap] mem pos
  set r1 := Function.update s0.regs 3 (nodeOfEndBase b vCap)
  set r2 := Function.update r1 4 u
  set r3 := Function.update r2 5 (nodesBase b vCap eCap)
  set r4 := Function.update r3 6 (2 * eCap + 2)
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 3) (rBase := 0) (off := HDR_NODE_OF_END)
    (b := b) (val := nodeOfEndBase b vCap) (st := s0) (by simp [s0, startState])
    (by simp only [HDR_NODE_OF_END]; omega) (by simp only [HDR_NODE_OF_END]; omega) hhdr.2.2.2.2.2.2.1
  have ha2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 3) (rIdx := 1)
    (base := nodeOfEndBase b vCap) (idx := keyX) (val := u) (st := ⟨mem, r1, pos⟩)
    (by simp [r1]) (by simp [r1, s0, startState])
    (by simp [nodeOfEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) (h.nodeOf_mem keyX hkx_lt).1
  have ha3 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_NODES_BASE)
    (b := b) (val := nodesBase b vCap eCap) (st := ⟨mem, r2, pos⟩) (by simp [r2, r1, s0, startState])
    (by simp only [HDR_NODES_BASE]; omega) (by simp only [HDR_NODES_BASE]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ha4 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_FUEL)
    (b := b) (val := 2 * eCap + 2) (st := ⟨mem, r3, pos⟩) (by simp [r3, r2, r1, s0, startState])
    (by simp only [HDR_FUEL]; omega) (by simp only [HDR_FUEL]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hinv0 : TourForestInv x.numNodes x.st (t :: rest) := (h.forestInv.perm hperm_r).1
  have hu_dep : t.depthOf u < 2 * eCap + 2 :=
    lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hu_t) (le_trans (hinv0.countNodes_le (t := t) (by simp)) (by have := h.numNodes_le; omega))
  have hrec_le : tourLayout.nodeAddr (nodesBase b vCap eCap) (x.numNodes + 1) ≤ heap := by
    have := h.numNodes_le; simp [NodeLayout.nodeAddr, tourLayout_stride, nodesBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega
  obtain ⟨t', oS, stS, cS, hrunS, hnS, hfrS, hinvS, _, _, ht'_root, ht'_list, _, hcS⟩ :=
    tourSplayLoop_runs_amort (pre := []) (post := rest) (pos := pos) C ω
      h.nodesAt hinv0 (h.valsOk hw) hu_t hu_dep (by omega) ⟨hrec_le, by omega, hzero, hwide⟩
  obtain ⟨_, _, _, _, _, _, hvalS, _⟩ := tourSplay_preserves (pre := []) (post := rest) hinv0 hu_t hu_dep
  have hcallS := runs_call_regs4 7 5 4 6 2 (st := ⟨mem, r4, pos⟩) C.splay.loop_body
    (by simp [r4, r3]) (by simp [r4, r3, r2]) (by simp [r4]) (by simp [r4, r3, r2, r1, s0, startState]) hrunS
  set r5 := Function.update r4 7 oS.value
  set sS := SplayState.splay tourPayload x.st (2 * eCap + 2) u
  have hu_cap : u ≤ x.numNodes := hu_le
  have hrt_mem : stS.mem (nodesBase b vCap eCap + 17 * u + 15) = (sS.nodes u).sum.rootTag := by
    have hnd := hnS u hu_cap
    have hoff : tourLayout.offSum = 12 := rfl
    simpa [NodeLayout.nodeAddr, tourLayout_stride, hoff, Nat.add_assoc] using hnd.2.2.2.2.2.2.2.1.2.2.2
  have hrt_eq : (sS.nodes u).sum.rootTag = r + 1 := by
    rw [← ht'_root, hinvS.sum_rootTag (t := t') (by simp)]
    have hmap_eq : t'.toList.map (fun id => (sS.nodes id).val.rootTag) =
        t.toList.map (fun id => (x.st.nodes id).val.rootTag) := by
      rw [ht'_list]; refine List.map_congr_left fun id hid => ?_
      rw [hvalS id (hinv0.mem_inCap (t := t) (by simp) hid).2]
    rw [hmap_eq]
    exact h.rootTag_foldr_eq_succ hrR (hperm_r.mem_iff.mpr (by simp)) ht_map
      (List.ne_nil_of_mem hu_t)
  have hAt : nodesBase b vCap eCap + 17 * u + 15 < 2 ^ w := by
    have := hrec_le; simp [NodeLayout.nodeAddr, tourLayout_stride] at this; omega
  set r6 := Function.update r5 7 (r + 1)
  set m1 := Function.update stS.mem heap r
  have ha7 : Runs w p ω (.assign 7 (.load (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 17) (.reg 4))) (.const 15))))
      { stS with regs := r5 } .normal { stS with regs := r6 } 9 :=
    runs_assign_iff.mpr ⟨r + 1, by
      simp [Expr.eval, r5, r4, r3, r2, BinOp.eval, (by omega : 17 < 2 ^ w), (by omega : 17 * u < 2 ^ w),
        (by omega : nodesBase b vCap eCap + 17 * u < 2 ^ w), (by omega : 15 < 2 ^ w), hAt, hrt_mem, hrt_eq],
      rfl, rfl, rfl⟩
  have hst : Runs w p ω (.store (.reg 2) (.bin .sub (.reg 7) (.const 1))) { stS with regs := r6 } .normal
      { stS with mem := m1, regs := r6 } 5 :=
    runs_store_iff.mpr ⟨heap, r, by simp [Expr.eval, r6, r5, r4, r3, r2, r1, s0, startState],
      by simp [Expr.eval, r6, BinOp.eval, (by omega : 1 < 2 ^ w), (by omega : r < 2 ^ w)], rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.bin .add (.reg 2) (.const 1))) { stS with mem := m1, regs := r6 }
      (.returned (heap + 1)) { stS with mem := m1, regs := r6 } 4 :=
    runs_ret_iff.mpr ⟨heap + 1, by simp [Expr.eval, r6, r5, r4, r3, r2, r1, s0, startState, BinOp.eval,
      (by omega : 1 < 2 ^ w), hroom], rfl, rfl, rfl⟩
  have hn1 : tourLayout.NodesAt m1 (nodesBase b vCap eCap) x.numNodes sS :=
    NodesAt.congr tourLayout hnS fun a ha =>
      Function.update_of_ne (Nat.ne_of_lt (lt_of_lt_of_le (inRecords_lt_ordHandle_of_le h.numNodes_le ha).2 hord_le)) _ _
  have hagree1 : ∀ a < heap, ¬tourLayout.InRecords (nodesBase b vCap eCap) x.numNodes a → m1 a = mem a :=
    fun a ha hnr => by dsimp only [m1]; rw [Function.update_of_ne (Nat.ne_of_lt ha)]; exact hfrS.2 a ha hnr
  obtain ⟨hrep1, hphi_ord, hphi_perm, hfoot_eq⟩ :=
    h.replace_compTree_same_list hLoc hfoot hrR hperm_r hct_r ht'_list hn1
      (by simpa using hinvS) (fun z hz => hvalS z hz) hagree1
  refine ⟨.returned (heap + 1), { stS with mem := m1, regs := r6 }, _,
    tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
      (tour_runs_seq_normal hcallS (tour_runs_seq_normal ha7 (tour_runs_seq_normal hst hret)))))),
    rfl, _, hrep1, by simp [m1, hsrc, r],
    fun a ha => by dsimp only [m1]; rw [Function.update_of_ne (by simp only [Outcome.value] at ha; omega)]; exact hfrS.1 a (by simp only [Outcome.value] at ha; omega),
    fun a ha hnf => hagree1 a ha fun hin => hnf (Or.inl ⟨by have := (inRecords_lt_ordHandle_of_le h.numNodes_le hin).1; simp [nodesBase] at this ⊢; omega,
      (inRecords_lt_ordHandle_of_le h.numNodes_le hin).2⟩),
    fun a ha => (hfoot_eq a).mp ha, ?_⟩
  simp only [List.nil_append] at hcS
  have hS' : cS + TOUR_PHI_MULT * forestPhi (t' :: rest) ≤
      TOUR_PHI_MULT * forestPhi (t :: rest) + TOUR_SPLAY_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) := by
    clear * - hcS; omega
  dsimp only [tourRep, tourPhi] at hphi_ord ⊢
  rw [hphi_perm, ← hphi_ord]
  have hlog_mul : TOUR_SPLAY_AMORT * (Nat.log 2 (x.numNodes + 2) + 1) ≤ TOUR_SPLAY_AMORT * (2 * tourLog eCap) :=
    Nat.mul_le_mul_left _ hlog
  clear * - hS' hlog_mul htl
  simp only [TOUR_SPLAY_AMORT, TOUR_QUERY_MUL] at *
  nlinarith

/-- Exact-space `O(1)` vertex-owner query (`vertOwner [b, keyX, heap]`): writes
`ordSrc s.ord (endOfKey keyX)` at `heap`, returns `heap + 1`, never modifies `tourFoot`, and pays
`≤ 80` steps (independent of `vCap`, `eCap`, and `heap`). -/
theorem tourOp_vertOwner_runs {R_ord : DSRep (ℕ → List End)}
    {w vCap eCap b keyX heap pos : ℕ} {p : Program}
    (hLoc : R_ord.Local) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete R_ord.τ} {mem : ℕ → ℕ}
    (h : TourRepAt R_ord vCap eCap b s x mem)
    (hact : ∃ v, endOfKey keyX ∈ s.ord v)
    (hfoot : ∀ a, tourFoot R_ord vCap eCap b x a → a < heap)
    (hzero : ZeroFrom mem heap) (hroom : heap + 1 < 2 ^ w) :
    ∃ o st' c, Runs w p ω tourOpVertOwnerBody
        (startState [b, keyX, heap] mem pos) o st' c ∧
      o.value = heap + 1 ∧
      (tourRep R_ord vCap eCap).rep b s x st'.mem ∧
      st'.mem heap = ordSrc s.ord (endOfKey keyX) ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < heap, ¬tourFoot R_ord vCap eCap b x a → st'.mem a = mem a) ∧
      c + (tourRep R_ord vCap eCap).phi b x st'.mem ≤
        80 + (tourRep R_ord vCap eCap).phi b x mem := by
  obtain ⟨v, hxv⟩ := hact
  have hord_le : ordHandleOf b vCap eCap ≤ heap := h.fixed_le_heap hfoot
  have hb_lt : b + 16 < 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
  have hvLt : v < vCap := by
    by_contra hge; have := h.valid.ordWithin.2.1 v (Nat.le_of_not_lt hge); rw [this] at hxv; simp at hxv
  have hkx_lt : keyX < 2 * eCap := by
    have h1 := h.valid.ordWithin.2.2 v _ hxv
    have h2 : endKey (endOfKey keyX) < 2 * eCap := by
      simp only [endKey]; cases (endOfKey keyX).2 <;> simp <;> omega
    rwa [endKey_endOfKey'] at h2
  have hsrc : ordSrc s.ord (endOfKey keyX) = v := h.valid.compat.ordSrc_eq hxv
  have heo : mem (endOwnerBase b vCap eCap + keyX) = x.slotOf v + 1 := by
    simpa [endKey_endOfKey'] using (h.active_end v hvLt (endOfKey keyX) hxv).2
  set sl := x.slotOf v
  have hsl_lt : sl < vCap := (h.slot_bij v hvLt).1
  have hv_sl : x.vertOf sl = v := (h.slot_bij v hvLt).2.1
  set raw := mem (vertOfSlotBase b vCap eCap + sl)
  have hdec : decodeSlot raw sl = v := (h.vertOf_mem sl hsl_lt).trans hv_sl
  have hhdr := h.header
  set s0 : State := startState [b, keyX, heap] mem pos
  set r1 := Function.update s0.regs 3 (endOwnerBase b vCap eCap)
  set r2 := Function.update r1 4 (sl + 1)
  set r3 := Function.update r2 4 sl
  set r4 := Function.update r3 5 (nextArrBase b vCap eCap)
  set r5 := Function.update r4 6 eCap
  set r6 := Function.update r5 7 vCap
  set r7 := Function.update r6 5 (vertOfSlotBase b vCap eCap)
  set r8 := Function.update r7 6 raw
  set r9 := Function.update r8 6 v
  set m1 := Function.update mem heap v
  have hvos_eq : nextArrBase b vCap eCap + 2 * eCap + vCap = vertOfSlotBase b vCap eCap := by
    simp [nextArrBase, vertOfSlotBase]; omega
  have ha1 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 3) (rBase := 0) (off := HDR_END_OWNER)
    (b := b) (val := endOwnerBase b vCap eCap) (st := s0) (by simp [s0, startState])
    (by simp only [HDR_END_OWNER]; omega) (by simp only [HDR_END_OWNER]; omega) hhdr.2.2.2.2.2.2.2.1
  have ha2 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 4) (rBase := 3) (rIdx := 1)
    (base := endOwnerBase b vCap eCap) (idx := keyX) (val := sl + 1) (st := ⟨mem, r1, pos⟩)
    (by simp [r1]) (by simp [r1, s0, startState])
    (by simp [endOwnerBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) heo
  have ha3 : Runs w p ω (.assign 4 (.bin .sub (.reg 4) (.const 1))) ⟨mem, r2, pos⟩ .normal ⟨mem, r3, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨sl, by simp [Expr.eval, r2, BinOp.eval, (by simp [ordHandleOf, tourFixedSize] at hord_le; omega : 1 < 2 ^ w),
      (by simp [ordHandleOf, tourFixedSize] at hord_le; omega : sl < 2 ^ w)], rfl, rfl, rfl⟩
  have ha4 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 5) (rBase := 0) (off := HDR_NEXT_ARR)
    (b := b) (val := nextArrBase b vCap eCap) (st := ⟨mem, r3, pos⟩) (by simp [r3, r2, r1, s0, startState])
    (by simp only [HDR_NEXT_ARR]; omega) (by simp only [HDR_NEXT_ARR]; omega) hhdr.2.2.2.2.2.2.2.2.2.2.2.1
  have ha5 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 0) (off := HDR_ECAP)
    (b := b) (val := eCap) (st := ⟨mem, r4, pos⟩) (by simp [r4, r3, r2, r1, s0, startState])
    (by simp only [HDR_ECAP]; omega) (by simp only [HDR_ECAP]; omega) hhdr.2.1
  have ha6 := runs_load_const_off (w := w) (p := p) (ω := ω) (dst := 7) (rBase := 0) (off := HDR_VCAP)
    (b := b) (val := vCap) (st := ⟨mem, r5, pos⟩) (by simp [r5, r4, r3, r2, r1, s0, startState])
    (by simp only [HDR_VCAP]; omega) (by simp only [HDR_VCAP]; omega) hhdr.1
  have ha7 : Runs w p ω (.assign 5 (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 6))) (.reg 7)))
      ⟨mem, r6, pos⟩ .normal ⟨mem, r7, pos⟩ 8 :=
    runs_assign_iff.mpr ⟨vertOfSlotBase b vCap eCap, by
      simp [Expr.eval, r6, r5, r4, BinOp.eval,
        (by simp [ordHandleOf, tourFixedSize] at hord_le; omega : 2 < 2 ^ w),
        (by simp [ordHandleOf, tourFixedSize] at hord_le; omega : 2 * eCap < 2 ^ w),
        (by simp [nextArrBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : nextArrBase b vCap eCap + 2 * eCap < 2 ^ w),
        hvos_eq, (by simp [vertOfSlotBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega : vertOfSlotBase b vCap eCap < 2 ^ w)],
      rfl, rfl, rfl⟩
  have ha8 := runs_load_reg_off (w := w) (p := p) (ω := ω) (dst := 6) (rBase := 5) (rIdx := 4)
    (base := vertOfSlotBase b vCap eCap) (idx := sl) (val := raw) (st := ⟨mem, r7, pos⟩)
    (by simp [r7]) (by simp [r7, r6, r5, r4, r3])
    (by simp [vertOfSlotBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega) rfl
  have hcond_dec : ∃ cD, cD ≤ 6 ∧ Runs w p ω (.cond (.reg 6) (.assign 6 (.bin .sub (.reg 6) (.const 1))) (.assign 6 (.reg 4)))
      ⟨mem, r8, pos⟩ .normal ⟨mem, r9, pos⟩ cD := by
    by_cases hr0 : raw = 0
    · have hveq : sl = v := by simpa [decodeSlot, hr0] using hdec
      have hc : (Expr.reg 6).eval w ⟨mem, r8, pos⟩ = some 0 := by simp [Expr.eval, r8, hr0]
      have ha : Runs w p ω (.assign 6 (.reg 4)) ⟨mem, r8, pos⟩ .normal ⟨mem, r9, pos⟩ 2 :=
        runs_assign_iff.mpr ⟨v, by simp [Expr.eval, r8, r7, r6, r5, r4, r3, hveq], rfl, rfl, rfl⟩
      exact ⟨_, by simp [Expr.size], tour_runs_cond_false hc ha⟩
    · have hveq : raw - 1 = v := by simpa [decodeSlot, hr0] using hdec
      have hc : (Expr.reg 6).eval w ⟨mem, r8, pos⟩ = some raw := by simp [Expr.eval, r8]
      have ha : Runs w p ω (.assign 6 (.bin .sub (.reg 6) (.const 1))) ⟨mem, r8, pos⟩ .normal ⟨mem, r9, pos⟩ 4 :=
        runs_assign_iff.mpr ⟨v, by simp [Expr.eval, r8, BinOp.eval, (by simp [ordHandleOf, tourFixedSize] at hord_le; omega : 1 < 2 ^ w),
          hveq, (by simp [ordHandleOf, tourFixedSize] at hord_le; omega : v < 2 ^ w)], rfl, rfl, rfl⟩
      exact ⟨_, by simp [Expr.size], tour_runs_cond_true hc hr0 ha⟩
  obtain ⟨cD, hcD, hrunD⟩ := hcond_dec
  have hst : Runs w p ω (.store (.reg 2) (.reg 6)) ⟨mem, r9, pos⟩ .normal ⟨m1, r9, pos⟩ 3 :=
    runs_store_iff.mpr ⟨heap, v, by simp [Expr.eval, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState],
      by simp [Expr.eval, r9], rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.bin .add (.reg 2) (.const 1))) ⟨m1, r9, pos⟩ (.returned (heap + 1)) ⟨m1, r9, pos⟩ 4 :=
    runs_ret_iff.mpr ⟨heap + 1, by simp [Expr.eval, r9, r8, r7, r6, r5, r4, r3, r2, r1, s0, startState, BinOp.eval,
      (by simp [ordHandleOf, tourFixedSize] at hord_le; omega : 1 < 2 ^ w), hroom], rfl, rfl, rfl⟩
  have hloc := (tourRep_local hLoc vCap eCap) b s x mem m1 fun a ha =>
    (Function.update_of_ne (Nat.ne_of_lt (hfoot a ha)) _ _).symm
  refine ⟨.returned (heap + 1), ⟨m1, r9, pos⟩, _,
    tour_runs_seq_normal ha1 (tour_runs_seq_normal ha2 (tour_runs_seq_normal ha3 (tour_runs_seq_normal ha4
      (tour_runs_seq_normal ha5 (tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8
        (tour_runs_seq_normal hrunD (tour_runs_seq_normal hst hret))))))))),
    rfl, hloc.1 h, by simp [m1, hsrc],
    fun a ha => by dsimp only [m1]; rw [Function.update_of_ne (by simp only [Outcome.value] at ha; omega)]; exact hzero a (by simp only [Outcome.value] at ha; omega),
    fun a ha _ => Function.update_of_ne (Nat.ne_of_lt ha) _ _, ?_⟩
  dsimp only; rw [hloc.2]; clear * - hcD; omega

end MinCostFlow.SparseCore.Program
