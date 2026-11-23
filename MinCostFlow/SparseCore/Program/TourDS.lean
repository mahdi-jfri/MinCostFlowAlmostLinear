module

public import MinCostFlow.SparseCore.Program.TourProcs
import Mathlib.Tactic

/-!
# Core Rotation Tour Data Structure Assembly (`DSRep.Implements`)

Assembles the verified 94-procedure deterministic WordRAM implementation (`tourProcs b`) of the
core rotation tour data structure (`tourContract`, piece P2):
* `tourMul`: input-independent cost multiplier covering initialization and all 14 operations.
* `tourAlloc`: linear heap space allocation with zero dependence on `heap`
  (`tourFixedSize vCap eCap + ordArenaSize vCap eCap + 3` for `init`; `tourOp0Space words =
  12 * words + 12` for Op `0`).
* `tourDS_implements`: `(tourDSRep vCap eCap).Local` and `(tourDSRep vCap eCap).Implements`
  against `tourContract vCap eCap tourMul tourAlloc` for any program containing `tourProcs b`.
* `tourDS_nonvacuous`: concrete witness `⟨tourProcs 0⟩` showing determinism and satisfiability of
  all initialization preconditions.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.DynSpanner.Program
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Universal cost constant, linear space allocation, and concrete representation -/

/-- Universal input-independent cost multiplier covering `init` and all 14 operations of
`tourContract`. -/
def tourMul : ℕ :=
  max (TOUR_INIT_BASE_MUL + ordStoreMul)
    (max (TOUR_OP0_MUL + 6 * ordStoreMul)
      (max TOUR_CUTLINK_MUL (max TOUR_FOREST_MUL TOUR_QUERY_MUL)))

/-- Linear heap allocation for `tourContract` (`14` = `init`, `0` = `applyEdits`), with zero
dependence on `heap`. -/
def tourAlloc (i : ℕ) (args : List ℕ) : ℕ :=
  match i with
  | 14 => tourFixedSize (args.getD 0 0) (args.getD 1 0) +
            ordArenaSize (args.getD 0 0) (args.getD 1 0) + 3
  | 0 => tourOp0Space (args.getD 2 0)
  | _ => 0

/-- Concrete `DSRep TourAbs` backed by `ordStoreRep vCap eCap`. -/
def tourDSRep (vCap eCap : ℕ) : DSRep TourAbs :=
  tourRep (ordStoreRep vCap eCap) vCap eCap

theorem tourDS_local (vCap eCap : ℕ) : (tourDSRep vCap eCap).Local :=
  tourRep_local (ordStoreRep_local vCap eCap) vCap eCap

theorem tourMul_ge_init : TOUR_INIT_BASE_MUL + ordStoreMul ≤ tourMul :=
  le_max_left _ _

theorem tourMul_ge_op0 : TOUR_OP0_MUL + 6 * ordStoreMul ≤ tourMul :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem tourMul_ge_cutlink : TOUR_CUTLINK_MUL ≤ tourMul :=
  le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

theorem tourMul_ge_forest : TOUR_FOREST_MUL ≤ tourMul :=
  le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))

theorem tourMul_ge_query : TOUR_QUERY_MUL ≤ tourMul :=
  le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))

theorem tourMul_ge_80 : 80 ≤ tourMul :=
  le_trans (by unfold TOUR_QUERY_MUL; omega) tourMul_ge_query

theorem tourDS_wide_of_foot {vCap eCap handle heap sp w : ℕ}
    {s : TourAbs} {x : TourConcrete OrdStoreState} {mem : ℕ → ℕ}
    (h : TourRepAt (ordStoreRep vCap eCap) vCap eCap handle s x mem)
    (hfoot : ∀ a, tourFoot (ordStoreRep vCap eCap) vCap eCap handle x a → a < heap)
    (hsp : heap + sp < 2 ^ w) :
    vCap + 2 * eCap + 4 < 2 ^ w ∧ 18 ≤ 2 ^ w := by
  have hle := h.fixed_le_heap hfoot
  simp only [ordHandleOf, tourFixedSize] at hle
  omega

/-! ## Main `DSRep.Implements` theorem for `tourContract` -/

/-- `tourProcs b` deterministically implements `tourContract vCap eCap tourMul tourAlloc` with
local representation `tourDSRep vCap eCap` and linear space allocation `tourAlloc`. -/
theorem tourDS_implements (w vCap eCap : ℕ) (p : Program) (b : ℕ)
    (hp : HasTourProcs p b) (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) :
    (tourDSRep vCap eCap).Local ∧
    (tourDSRep vCap eCap).Implements w p (tourInit b) (tourOp b)
      (tourContract vCap eCap tourMul tourAlloc) := by
  have hloc := tourDS_local vCap eCap
  have hOrd := ordStore_implements_cap w vCap eCap p b hp.toOrdStore hw
  refine ⟨hloc, hloc, ?_, ?_⟩
  · -- Initialization (`tourInit b = b + 93`)
    intro args mem pos ω _ hpre hz hsp
    rcases hpre with ⟨ordPtr, fePtr, rsPtr, heap, ordWords, rfl, hOrdAt, hOrdLe, hFeLe, hRsLe,
      hFeNd, hRsNd, hValid⟩
    have hha : heapArg [vCap, eCap, ordPtr, fePtr, rsPtr, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
    have hsp' : heap + (tourFixedSize vCap eCap + ordArenaSize vCap eCap + 3) < 2 ^ w := by
      simp only [tourContract, tourAlloc, hha, List.getD_cons_zero, List.getD_cons_succ] at hsp
      exact hsp
    have hwide : 16 ≤ 2 ^ w := by simp only [tourFixedSize, ordArenaSize] at hsp'; omega
    let C := hp.toSplayQuery (w := w) hwide
    obtain ⟨o, st', c, x', hrun, hrep', hresp', hcost⟩ :=
      tourInitBody_runs (pos := pos) (ordInit := ordStoreInit b) (ordOp := ordStoreOp b)
        (stage1Proc := b + 78) (rootOfProc := b + 89) (linkProc := b + 81)
        (lsProc := b + 77) (chRootProc := b + 82)
        C hOrd.2 (le_refl _)
        hp.stage1_body hp.op10_body hp.linkSplice_body hp.op2_body hp.op3_body
        ω hOrdAt hOrdLe hFeLe hRsLe hFeNd hRsNd hValid (by rw [hha] at hz; exact hz) hsp'
    refine ⟨_, hp.init_body, o, st', c, hrun, _, x',
      by simp only [tourDSRep, hha]; exact hrep', rfl,
      by simp only [tourContract, tourAlloc, tourDSRep, hha, List.getD_cons_zero, List.getD_cons_succ]; exact hresp', ?_⟩
    simp only [tourContract, tourDSRep, hha, List.getD_cons_zero, List.getD_cons_succ]
    have hmono := Nat.mul_le_mul_right (tourLog eCap)
      (Nat.mul_le_mul_right (1 + ordRecordsWords (readOrdRecordsAt mem ordPtr) + mem fePtr + mem rsPtr)
        tourMul_ge_init)
    omega
  · -- Operations 0 .. 13 (`tourOp b i = b + 79 + i`)
    intro i handle s x args mem pos ω _ hhead hrep hpre hfoot hz hsp
    change TourRepAt (ordStoreRep vCap eCap) vCap eCap handle s x mem at hrep
    change ∀ a, tourFoot (ordStoreRep vCap eCap) vCap eCap handle x a → a < heapArg args at hfoot
    match i with
    | 0 =>
      rcases hpre with ⟨h0, edits, words, heap, rfl, hEdAt, hEdLe, hEdVal⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, edits, words, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + tourOp0Space words < 2 ^ w := by
        simp only [tourContract, tourAlloc, List.getD_cons_zero, List.getD_cons_succ] at hsp; exact hsp
      have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let E := hp.toEditProcs (w := w) (by omega)
      obtain ⟨o, st', c, hrun, x', hrep', hresp', hcost⟩ :=
        tourOp_applyEdits_runs (pos := pos) (ordInit := ordStoreInit b) (ordOp := ordStoreOp b)
          E hOrd.2 rfl rfl (fun _ _ _ _ => le_refl _) ω hrep hEdAt hEdLe hEdVal hw1 hw2
          hfoot hz hsp'
      refine ⟨_, hp.op0_body, o, st', c, hrun, _, x', hrep',
        by simp only [tourContract, List.getD_cons_zero, List.getD_cons_succ],
        by simp only [tourContract, tourAlloc, tourDSRep, hha, List.getD_cons_zero, List.getD_cons_succ]; exact hresp', ?_⟩
      simp only [tourContract, tourDSRep, List.getD_cons_zero, List.getD_cons_succ]
      have hmono := Nat.mul_le_mul_right (tourLog eCap)
        (Nat.mul_le_mul_right (words + 1) tourMul_ge_op0)
      omega
    | 1 =>
      rcases hpre with ⟨h0, e, newRoot, heap, rfl, heE, hnrLt, hnrV, hnrNotR, huniq'⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, e, newRoot, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + 2 < 2 ^ w := hsp
      have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let C := hp.toSplayQuery (w := w) (by omega)
      obtain ⟨o, st', c, hrun, x', hrep', hresp', hcost⟩ :=
        tourOp_cut_runs (pos := pos) (csProc := b + 76) hOrd.1 C hp.cutSplit_body ω
          hrep heE hnrLt hnrV hnrNotR huniq' hw1 (by omega) hfoot hz hsp'
      refine ⟨_, hp.op1_body, o, st', c, hrun, _, x', hrep',
        by simp only [tourContract, List.getD_cons_zero, List.getD_cons_succ],
        by simp only [tourContract, tourDSRep, hha]; exact hresp', ?_⟩
      simp only [tourContract, tourDSRep]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_cutlink
      omega
    | 2 =>
      rcases hpre with ⟨h0, e, dropRoot, heap, rfl, heLt, heNotE, ⟨u, hxu⟩, ⟨v, hyv⟩, hnc, hdrop⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, e, dropRoot, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + 2 < 2 ^ w := hsp
      have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let C := hp.toSplayQuery (w := w) (by omega)
      obtain ⟨o, st', c, hrun, _, x', hrep', hresp', hcost⟩ :=
        tourOp_link_runs (pos := pos) (lsProc := b + 77) hOrd.1 C hp.linkSplice_body ω
          hrep heLt heNotE hxu hyv hnc hdrop hw1 (by omega) hfoot hz hsp'
      refine ⟨_, hp.op2_body, o, st', c, hrun, _, x', hrep',
        by simp only [tourContract, List.getD_cons_zero, List.getD_cons_succ],
        by simp only [tourContract, tourDSRep, hha]; exact hresp', ?_⟩
      simp only [tourContract, tourDSRep]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_cutlink
      omega
    | 3 =>
      rcases hpre with ⟨h0, oldRoot, newRoot, heap, rfl, holdR, hnrLt, hnrV, hconn⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, oldRoot, newRoot, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + 2 < 2 ^ w := hsp
      have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let C := hp.toSplayQuery (w := w) (by omega)
      obtain ⟨o, st', c, hrun, _, x', hrep', hresp', hcost⟩ :=
        tourOp_changeRoot_runs (pos := pos) hOrd.1 C ω hrep holdR hnrLt hnrV hconn hw1 (by omega)
          hfoot hz hsp'
      refine ⟨_, hp.op3_body, o, st', c, hrun, _, x', hrep',
        by simp only [tourContract, List.getD_cons_zero, List.getD_cons_succ],
        by simp only [tourContract, tourDSRep, hha]; exact hresp', ?_⟩
      simp only [tourContract, tourDSRep]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_forest
      omega
    | 4 =>
      rcases hpre with ⟨h0, r, heap, rfl, hrLt⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, r, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + (3 + (coreTour s.ord s.rf r).length) < 2 ^ w := by
        simp only [tourContract, List.getD_cons_zero, List.getD_cons_succ] at hsp; exact hsp
      have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let C := hp.toSplayQuery (w := w) (by omega)
      obtain ⟨o, st', c, hrun, x', hrep', hlist', _, hresp', hcost⟩ :=
        tourOp_listTour_runs (pos := pos) hOrd.1 C ω hrep hrLt hw1 (by omega) hfoot hz hsp'
      refine ⟨_, hp.op4_body, o, st', c, hrun, s, x', hrep',
        ⟨rfl, by simp only [List.getD_cons_zero, List.getD_cons_succ]; exact hlist'⟩,
        by simp only [tourContract, tourDSRep, hha, List.getD_cons_zero, List.getD_cons_succ]; exact hresp', ?_⟩
      simp only [tourContract, tourDSRep, List.getD_cons_zero, List.getD_cons_succ]
      have hmono := Nat.mul_le_mul_right (tourLog eCap)
        (Nat.mul_le_mul_right ((coreTour s.ord s.rf r).length + 1) tourMul_ge_query)
      omega
    | 5 =>
      rcases hpre with ⟨h0, keyX, keyY, heap, rfl, ⟨vx, hmx⟩, hox, ⟨vy, hmy⟩, _⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, keyX, keyY, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + 3 < 2 ^ w := hsp
      have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let C := hp.toSplayQuery (w := w) (by omega)
      obtain ⟨o, st', c, hrun, x', hrep', hans, hresp', hcost⟩ :=
        tourOp_adjacent_runs (pos := pos) hOrd.1 C ω hrep hmx hox hmy hw1 (by omega)
          hfoot hz hsp'
      refine ⟨_, hp.op5_body, o, st', c, hrun, s, x', hrep',
        ⟨rfl, by exact hans⟩,
        by simp only [tourContract, tourDSRep, hha]; exact hresp', ?_⟩
      simp only [tourContract, tourDSRep]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      omega
    | 6 =>
      rcases hpre with ⟨h0, keyX, heap, rfl, ⟨vx, hmx⟩, hox⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, keyX, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + 3 < 2 ^ w := hsp
      have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let C := hp.toSplayQuery (w := w) (by omega)
      obtain ⟨o, st', c, hrun, x', hrep', hans, hresp', hcost⟩ :=
        tourOp_nextOpen_runs (pos := pos) hOrd.1 C ω hrep hmx hox hw1 (by omega)
          hfoot hz hsp'
      refine ⟨_, hp.op6_body, o, st', c, hrun, s, x', hrep',
        ⟨rfl, by exact hans⟩,
        by simp only [tourContract, tourDSRep, hha]; exact hresp', ?_⟩
      simp only [tourContract, tourDSRep]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      omega
    | 7 =>
      rcases hpre with ⟨h0, keyX, flag, heap, rfl, ⟨vx, hmx⟩, hox, hfl⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, keyX, flag, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + 2 < 2 ^ w := hsp
      have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let C := hp.toSplayQuery (w := w) (by omega)
      obtain ⟨o, st', c, hrun, _, x', hrep', hresp', hcost⟩ :=
        tourOp_setMark_runs (pos := pos) hOrd.1 C ω hrep hmx hox hfl hw1 (by omega)
          hfoot hz hsp'
      refine ⟨_, hp.op7_body, o, st', c, hrun, _, x', hrep',
        by simp only [tourContract, List.getD_cons_zero, List.getD_cons_succ],
        by simp only [tourContract, tourDSRep, hha]; exact hresp', ?_⟩
      simp only [tourContract, tourDSRep]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_forest
      omega
    | 8 =>
      rcases hpre with ⟨h0, keyX, heap, rfl, ⟨vx, hmx⟩⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, keyX, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + 3 < 2 ^ w := hsp
      have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let C := hp.toSplayQuery (w := w) (by omega)
      obtain ⟨o, st', c, hrun, _, x', hrep', hans, hresp', hcost⟩ :=
        tourOp_nextMarked_runs (pos := pos) hOrd.1 C ω hrep hmx hw1 (by omega)
          hfoot hz hsp'
      refine ⟨_, hp.op8_body, o, st', c, hrun, s, x', hrep',
        ⟨rfl, by exact hans⟩,
        by simp only [tourContract, tourDSRep, hha]; exact hresp', ?_⟩
      simp only [tourContract, tourDSRep]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      omega
    | 9 =>
      rcases hpre with ⟨h0, r, heap, rfl, hrLt⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, r, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      simp only [tourContract, List.getD_cons_zero, List.getD_cons_succ] at hsp
      have hsp' : heap + 1 + (tourMarkedList s r).length < 2 ^ w := by omega
      have ⟨_, hw2⟩ := tourDS_wide_of_foot hrep hfoot (by omega : heap + 1 < 2 ^ w)
      let C := hp.toListExact (w := w) (by omega)
      obtain ⟨o, st', c, hrun, x', hrep', hlist', hval', hz', hfr', hft', hcost⟩ :=
        tourOp_listMarked_exact_runs (pos := pos) hOrd.1 C ω hrep hrLt hfoot hz hsp'
      refine ⟨_, hp.op9_body, o, st', c, hrun, s, x', hrep',
        ⟨rfl, by exact hlist'⟩,
        ⟨by rw [hha, hval']; omega,
         by simp only [tourContract, hha, hval', List.getD_cons_zero, List.getD_cons_succ]; omega,
         hz', fun a ha hnf => hfr' a (by rw [hha] at ha; exact ha) hnf,
         fun a ha => Or.inl (hft' a ha)⟩, ?_⟩
      simp only [tourContract, tourDSRep, List.getD_cons_zero, List.getD_cons_succ]
      rw [ordStoreLog_eq_tourLog] at hcost
      have hmono := Nat.mul_le_mul_right (tourLog eCap)
        (Nat.mul_le_mul_right ((tourMarkedList s r).length + 1) tourMul_ge_query)
      omega
    | 10 =>
      rcases hpre with ⟨h0, keyX, heap, rfl, hact⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, keyX, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + 1 < 2 ^ w := hsp
      have ⟨_, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let C := hp.toSplayCore (w := w) (by omega)
      obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hz', hfr', hft', hcost⟩ :=
        tourOp_rootOf_exact_runs (pos := pos) hOrd.1 C ω hrep hact hfoot hz hsp'
      refine ⟨_, hp.op10_body, o, st', c, hrun, s, x', hrep',
        ⟨rfl, by exact hans⟩,
        ⟨by rw [hha, hval']; omega,
         by simp only [tourContract, hha, hval']; omega,
         hz', fun a ha hnf => hfr' a (by rw [hha] at ha; exact ha) hnf,
         fun a ha => Or.inl (hft' a ha)⟩, ?_⟩
      simp only [tourContract, tourDSRep]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      omega
    | 11 =>
      rcases hpre with ⟨h0, r, heap, rfl, hrLt⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, r, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + 3 < 2 ^ w := hsp
      have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let C := hp.toSplayQuery (w := w) (by omega)
      obtain ⟨o, st', c, hrun, _, x', hrep', hans, hresp', hcost⟩ :=
        tourOp_firstMarked_runs (pos := pos) hOrd.1 C C.markTests C.markTests_cost
          C.markDesc_body C.findFirstMark_body ω hrep hrLt hw1 (by omega) hfoot hz hsp'
      refine ⟨_, hp.op11_body, o, st', c, hrun, s, x', hrep',
        ⟨rfl, by exact hans⟩,
        by simp only [tourContract, tourDSRep, hha]; exact hresp', ?_⟩
      simp only [tourContract, tourDSRep]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      omega
    | 12 =>
      rcases hpre with ⟨h0, r, heap, rfl, hrLt⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, r, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + 1 < 2 ^ w := hsp
      have ⟨_, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp'
      let C := hp.toSplayCore (w := w) (by omega)
      obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hz', hfr', hft', hcost⟩ :=
        tourOp_len_runs (pos := pos) hOrd.1 C ω hrep hrLt hfoot hz hsp'
      refine ⟨_, hp.op12_body, o, st', c, hrun, s, x', hrep',
        ⟨rfl, by exact hans⟩,
        ⟨by rw [hha, hval']; omega,
         by simp only [tourContract, hha, hval']; omega,
         hz', fun a ha hnf => hfr' a (by rw [hha] at ha; exact ha) hnf,
         fun a ha => Or.inl (hft' a ha)⟩, ?_⟩
      simp only [tourContract, tourDSRep]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      omega
    | 13 =>
      rcases hpre with ⟨h0, keyX, heap, rfl, hact⟩
      have hh : h0 = handle := by simpa using hhead
      subst h0
      have hha : heapArg [handle, keyX, heap] = heap := by simp only [heapArg, List.getLastD_cons, List.getLastD_nil]
      rw [hha] at hfoot hz hsp
      have hsp' : heap + 1 < 2 ^ w := hsp
      obtain ⟨o, st', c, hrun, hval', hrep', hans, hz', hfr', hcost⟩ :=
        tourOp_vertOwner_runs (pos := pos) hOrd.1 ω hrep hact hfoot hz hsp'
      refine ⟨_, hp.op13_body, o, st', c, hrun, s, x, hrep',
        ⟨rfl, by exact hans⟩,
        ⟨by rw [hha, hval']; omega,
         by simp only [tourContract, hha, hval']; omega,
         hz', fun a ha hnf => hfr' a (by rw [hha] at ha; exact ha) hnf,
         fun a ha => Or.inl ha⟩, ?_⟩
      simp only [tourContract, tourDSRep]
      have h80 := tourMul_ge_80
      omega
    | i + 14 => exact False.elim hpre

/-! ## Concrete non-vacuity witness -/

/-- Non-vacuity of `tourDS_implements`: the standalone deterministic program `⟨tourProcs 0⟩`
satisfies `HasTourProcs`, `Stmt.NoRand`, and every initialization precondition of
`tourContract vCap eCap tourMul tourAlloc` on the empty 1-vertex forest. -/
theorem tourDS_nonvacuous {w vCap eCap : ℕ} (hv : 0 < vCap)
    (_hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (hsp : 4 + (tourFixedSize vCap eCap + ordArenaSize vCap eCap + 3) < 2 ^ w) :
    let p : Program := ⟨tourProcs 0⟩
    let mem : ℕ → ℕ := fun a =>
      if a = 0 then 0 else if a = 1 then 0 else if a = 2 then 1 else if a = 3 then 0 else 0
    let args : List ℕ := [vCap, eCap, 0, 1, 2, 4]
    HasTourProcs p 0 ∧
    (∀ s ∈ p.procs, s.NoRand) ∧
    (∀ a ∈ args, a < 2 ^ w) ∧
    (tourContract vCap eCap tourMul tourAlloc).initPre args mem ∧
    ZeroFrom mem (heapArg args) ∧
    heapArg args + (tourContract vCap eCap tourMul tourAlloc).initSpace args mem < 2 ^ w := by
  intro p mem args
  refine ⟨fun i hi => by simp [p], tourProcs_noRand 0, ?_,
    tourContract_initPre_nonempty hv, ?_, ?_⟩
  · intro a ha
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at ha
    have hv_lt : vCap < 2 ^ w := by simp only [tourFixedSize, ordArenaSize] at hsp; omega
    have he_lt : eCap < 2 ^ w := by simp only [tourFixedSize, ordArenaSize] at hsp; omega
    have h4 : 4 < 2 ^ w := by omega
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · intro a ha
    simp only [args, heapArg, List.getLastD_cons, List.getLastD_nil] at ha
    simp [mem, show a ≠ 0 by omega, show a ≠ 1 by omega, show a ≠ 2 by omega]
  · simpa [tourContract, tourAlloc, args, heapArg] using hsp

end MinCostFlow.SparseCore.Program
