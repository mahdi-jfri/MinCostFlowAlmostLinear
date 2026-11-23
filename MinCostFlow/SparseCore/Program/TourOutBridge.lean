module

public import MinCostFlow.SparseCore.Program.TourDS
public import MinCostFlow.SparseCore.Program.AssemblyBranchOrdDefs
import Mathlib.Tactic

/-!
# Bridge to `OutTourAt`, `AsmBrTourListAt`, and Exact-Space Downstream Queries

Projects `tourDSRep vCap eCap` to `tourOutRep vCap eCap : DSRep OutTourAbs` and proves:
* `tourDS_outTourAt`: `tourProcs b` implements `OutTourAt tourOutSpec w vCap eCap p`
  (`OutTourInterface.lean`) for downstream piece P7 with exact `listSpace len = 1 + len` and
  `querySpace = 3`.
* `tourDS_listMarked_exact` and `tourDS_asmBrTourListAt`: exact-space (`1 + |out|`)
  zero-footprint-growth `listMarked` over `tourOutRep`, directly instantiating `AsmBrTourListAt`
  (`AssemblyBranchOrdDefs.lean`) for downstream piece P9.
* `tourDS_lenCoreTour_exact`, `tourDS_rootOf_exact`, `tourDS_vertOwner_exact`: exact-space
  (`1` word) length, root-owner, and `O(1)` vertex-owner query corollaries.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF
  MinCostFlow.DynSpanner.Program
  MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Cyclic search equivalence between `fullTour` and `coreTour` -/

private theorem find?_filter_of_imp {α : Type*} {p q : α → Bool}
    (himp : ∀ z, q z = true → p z = true) :
    ∀ L : List α, (L.filter p).find? q = L.find? q
  | [] => rfl
  | a :: as => by
    cases hqa : q a with
    | true =>
      have hpa : p a = true := himp a hqa
      simp [hpa, hqa]
    | false =>
      cases hpa : p a with
      | true => simp [hpa, hqa, find?_filter_of_imp himp as]
      | false => simp [hpa, hqa, find?_filter_of_imp himp as]

private theorem takeWhile_append_of_not_mem {α : Type*} [BEq α] [LawfulBEq α]
    {x : α} {l₁ l₂ : List α} (hnot : x ∉ l₁) :
    (l₁ ++ x :: l₂).takeWhile (· != x) = l₁ := by
  induction l₁ with
  | nil => simp
  | cons a as ih =>
    have hax : a ≠ x := fun h => hnot (h ▸ List.mem_cons_self)
    have has : x ∉ as := fun h => hnot (List.mem_cons_of_mem _ h)
    have hb : (a != x) = true := bne_iff_ne.mpr hax
    simp [List.cons_append, hb, ih has]

private theorem tourOut_idxOf_append_cons {α : Type*} [BEq α] [LawfulBEq α]
    {x : α} {l₁ l₂ : List α} (hnot : x ∉ l₁) :
    (l₁ ++ x :: l₂).idxOf x = l₁.length := by
  induction l₁ with
  | nil => simp
  | cons a as ih =>
    have hax : a ≠ x := fun h => hnot (h ▸ List.mem_cons_self)
    have has : x ∉ as := fun h => hnot (List.mem_cons_of_mem _ h)
    simp [List.cons_append, List.idxOf_cons_ne _ hax, ih has]

theorem coreTour_mem_info {vCap eCap v : ℕ} {s : TourAbs} {x : End}
    (hv : TourValid vCap eCap s) (hx : x ∈ coreTour s.ord s.rf v) :
    v ∈ s.rf.R ∧ x.1 ∉ s.rf.F.E ∧ (∃ u, x ∈ s.ord u) ∧ s.rf.root (ordSrc s.ord x) = v := by
  have hvR : v ∈ s.rf.R := by
    by_contra hnr
    simp [coreTour, hv.compat.forest, hnr] at hx
  have hct := fullTour_filter_open s.ord hv.compat.forest hvR
  rw [← hct, List.mem_filter] at hx
  have hxOpen : x.1 ∉ s.rf.F.E := by simpa using hx.2
  obtain ⟨u, hxu, hconn⟩ := ((fullTour_spec hv.compat v).2 x).mp hx.1
  have huV : u ∈ s.rf.F.V := hv.compat.vert u (List.ne_nil_of_mem hxu)
  have hroot : s.rf.root (ordSrc s.ord x) = v := by
    rw [hv.compat.ordSrc_eq hxu]
    exact hv.root_eq_of_mem huV hvR (connected_symm hconn)
  exact ⟨hvR, hxOpen, ⟨u, hxu⟩, hroot⟩

theorem tourNextMarked_eq_outNextMarked {vCap eCap v : ℕ} {s : TourAbs} {x : End}
    (hv : TourValid vCap eCap s) (hx : x ∈ coreTour s.ord s.rf v) :
    open Classical in
    tourNextMarked s x =
      (afterEnd x (coreTour s.ord s.rf v) ++ [x]).find? fun z => decide (z ∈ s.marked) := by
  classical
  obtain ⟨hvR, hxOpen, _, hroot⟩ := coreTour_mem_info hv hx
  set F := fullTour s.ord s.rf.F hv.compat.forest v
  have hnd : F.Nodup := (fullTour_spec hv.compat v).1
  have hct : coreTour s.ord s.rf v = F.filter (fun z => decide (z.1 ∉ s.rf.F.E)) :=
    (fullTour_filter_open s.ord hv.compat.forest hvR).symm
  have hxF : x ∈ F := by rw [hct, List.mem_filter] at hx; exact hx.1
  obtain ⟨l₁, l₂, hFeq⟩ := List.append_of_mem hxF
  have hx_not_l1 : x ∉ l₁ := by
    rw [hFeq, List.nodup_append] at hnd
    exact fun h => hnd.2.2 x h x List.mem_cons_self rfl
  have hrot_tail : (rotateToList x F).tail = l₂ ++ l₁ := by
    simp [rotateToList, hFeq, tourOut_idxOf_append_cons hx_not_l1]
  have hp_x : decide (x.1 ∉ s.rf.F.E) = true := decide_eq_true hxOpen
  have hafter : afterEnd x (F.filter fun z => decide (z.1 ∉ s.rf.F.E)) =
      (l₂ ++ l₁).filter (fun z => decide (z.1 ∉ s.rf.F.E)) := by
    have hfilt : F.filter (fun z => decide (z.1 ∉ s.rf.F.E)) =
        l₁.filter (fun z => decide (z.1 ∉ s.rf.F.E)) ++
          x :: l₂.filter (fun z => decide (z.1 ∉ s.rf.F.E)) := by
      rw [hFeq, List.filter_append, List.filter_cons, hp_x]; rfl
    have hnot_f : x ∉ l₁.filter (fun z => decide (z.1 ∉ s.rf.F.E)) := fun h =>
      hx_not_l1 (List.mem_filter.mp h).1
    rw [hfilt, afterEnd, takeWhile_append_of_not_mem hnot_f, List.drop_append]
    simp [List.filter_append]
  have himp : ∀ z, decide (z ∈ s.marked) = true → decide (z.1 ∉ s.rf.F.E) = true := fun z hz =>
    decide_eq_true (hv.marked_open z (of_decide_eq_true hz)).2
  have hfx : (l₂ ++ l₁ ++ [x]).filter (fun z => decide (z.1 ∉ s.rf.F.E)) =
      (l₂ ++ l₁).filter (fun z => decide (z.1 ∉ s.rf.F.E)) ++ [x] := by
    simp [List.filter_append, hxOpen]
  simp only [tourNextMarked, hv.compat.forest, ↓reduceDIte, hroot, hct]
  rw [hrot_tail, hafter, ← hfx, find?_filter_of_imp himp]

/-! ## `tourOutRep` and `OutTourAt` bridge -/

/-- Projection of `tourDSRep vCap eCap` to `OutTourAbs` (`OutTourInterface.lean`). -/
def tourOutRep (vCap eCap : ℕ) : DSRep OutTourAbs where
  τ := TourAbs × TourConcrete OrdStoreState
  rep b s tx mem :=
    TourRepAt (ordStoreRep vCap eCap) vCap eCap b tx.1 tx.2 mem ∧
    (∀ r, s.cord r = coreTour tx.1.ord tx.1.rf r) ∧
    s.marked = tx.1.marked
  phi b tx mem := (tourDSRep vCap eCap).phi b tx.2 mem
  foot b tx a := (tourDSRep vCap eCap).foot b tx.2 a

theorem tourOutRep_local (vCap eCap : ℕ) : (tourOutRep vCap eCap).Local := by
  intro b s tx mem mem' hagree
  have hloc := tourDS_local vCap eCap b tx.1 tx.2 mem mem' hagree
  exact ⟨fun ⟨hrep, hcord, hmk⟩ => ⟨hloc.1 hrep, hcord, hmk⟩, hloc.2⟩

/-- The handle `tourH` always belongs to `(tourOutRep vCap eCap).foot tourH tx`
(`AsmBrTourListAt.handle_foot`). -/
theorem tourOutRep_handle_foot (vCap eCap tourH : ℕ) (tx : (tourOutRep vCap eCap).τ) :
    (tourOutRep vCap eCap).foot tourH tx tourH :=
  tourFoot_handle (ordStoreRep vCap eCap) vCap eCap tourH tx.2

/-- Input-independent specification constants of `tourDS_outTourAt`: exact `listSpace len = 1 + len`
and `querySpace = 3`. -/
def tourOutSpec : OutTourSpec where
  mul := tourMul
  querySpace := 3
  listSpace len := 1 + len
  querySpace_ge := by decide
  listSpace_ge _ := le_refl _
  listSpace_mono _ _ hab := by omega

/-- `tourProcs b` meets the four-operation `OutTourAt` interface (`OutTourInterface.lean`) on
`tourOutRep vCap eCap` with exact `listSpace len = 1 + len`. -/
def tourDS_outTourAt (w vCap eCap : ℕ) (p : Program) (b : ℕ)
    (hp : HasTourProcs p b) :
    OutTourAt tourOutSpec w vCap eCap p
      (tourOp b 8) (tourOp b 7) (tourOp b 11) (tourOp b 9) where
  rep := tourOutRep vCap eCap
  rep_local := tourOutRep_local vCap eCap
  nextMarked_runs := fun tourH key v h s tx mem pos ω _ _ _ _ _ hmem hrep hfoot hz hsp => by
    rcases tx with ⟨sFull, xFull⟩
    rcases hrep with ⟨hR, hcord, hmk⟩
    have hmem' : endOfKey key ∈ coreTour sFull.ord sFull.rf v := hcord v ▸ hmem
    obtain ⟨_, _, ⟨u, hxu⟩, _⟩ := coreTour_mem_info hR.valid hmem'
    have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp
    let C := hp.toSplayQuery (w := w) (by omega)
    obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hresp', hcost⟩ :=
      tourOp_nextMarked_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hxu hw1 (by omega)
        hfoot hz hsp
    have hnm_eq := tourNextMarked_eq_outNextMarked hR.valid hmem'
    refine ⟨_, hp.op8_body, o, st', c, ⟨sFull, x'⟩, hrun,
      ⟨hrep', hcord, hmk⟩, ?_, by omega, hresp', ?_⟩
    · rw [hans, hnm_eq]
      simp only [OutTourAbs.nextMarked, hcord v, hmk]
      cases (afterEnd (endOfKey key) (coreTour sFull.ord sFull.rf v) ++ [endOfKey key]).find?
        (fun z => decide (z ∈ sFull.marked)) <;> rfl
    · rw [ordStoreLog_eq_tourLog]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      dsimp only [tourOutRep, tourDSRep, tourOutSpec] at hcost ⊢
      omega
  setMark_runs := fun tourH key flag v h s tx mem pos ω _ _ _ hfl _ _ hmem hrep hfoot hz hsp => by
    rcases tx with ⟨sFull, xFull⟩
    rcases hrep with ⟨hR, hcord, hmk⟩
    have hmem' : endOfKey key ∈ coreTour sFull.ord sFull.rf v := hcord v ▸ hmem
    obtain ⟨_, hopen, ⟨u, hxu⟩, _⟩ := coreTour_mem_info hR.valid hmem'
    have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp
    let C := hp.toSplayQuery (w := w) (by omega)
    obtain ⟨o, st', c, hrun, _, x', hrep', hresp', hcost⟩ :=
      tourOp_setMark_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hxu hopen hfl
        hw1 (by omega) hfoot hz (by dsimp only [tourOutSpec] at hsp; omega)
    have hcord' : ∀ r, (s.setMark (endOfKey key) flag).cord r =
        coreTour (tourSetMark sFull (endOfKey key) flag).ord
          (tourSetMark sFull (endOfKey key) flag).rf r := fun r => by
      simp only [OutTourAbs.setMark, tourSetMark]
      split_ifs <;> exact hcord r
    have hmk' : (s.setMark (endOfKey key) flag).marked =
        (tourSetMark sFull (endOfKey key) flag).marked := by
      simp only [OutTourAbs.setMark, tourSetMark, hmk]
      split_ifs <;> rfl
    refine ⟨_, hp.op7_body, o, st', c, ⟨tourSetMark sFull (endOfKey key) flag, x'⟩,
      hrun, ⟨hrep', hcord', hmk'⟩,
      ⟨hresp'.1, le_trans hresp'.2.1 (by dsimp only [tourOutSpec]; omega),
       hresp'.2.2.1, hresp'.2.2.2.1, hresp'.2.2.2.2⟩, ?_⟩
    rw [ordStoreLog_eq_tourLog]
    have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_forest
    dsimp only [tourOutRep, tourDSRep, tourOutSpec] at hcost ⊢
    omega
  firstMarked_runs := fun tourH r h s tx mem pos ω _ hrLt _ hrep hfoot hz hsp => by
    rcases tx with ⟨sFull, xFull⟩
    rcases hrep with ⟨hR, hcord, hmk⟩
    have ⟨hw1, hw2⟩ := tourDS_wide_of_foot hR hfoot hsp
    let C := hp.toSplayQuery (w := w) (by omega)
    obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hresp', hcost⟩ :=
      tourOp_firstMarked_runs (pos := pos) (ordStoreRep_local vCap eCap) C C.markTests
        C.markTests_cost C.markDesc_body C.findFirstMark_body ω hR hrLt hw1 (by omega)
        hfoot hz hsp
    have hml : s.markedList r = tourMarkedList sFull r := by
      simp only [OutTourAbs.markedList, tourMarkedList, hcord r, hmk]
    refine ⟨_, hp.op11_body, o, st', c, ⟨sFull, x'⟩, hrun,
      ⟨hrep', hcord, hmk⟩, ?_, by omega, hresp', ?_⟩
    · rw [hans, hml]; cases (tourMarkedList sFull r).head? <;> rfl
    · rw [ordStoreLog_eq_tourLog]
      have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
      dsimp only [tourOutRep, tourDSRep, tourOutSpec] at hcost ⊢
      omega
  listMarked_runs := fun tourH r h s tx mem pos ω _ hrLt _ hrep hfoot hz hsp => by
    rcases tx with ⟨sFull, xFull⟩
    rcases hrep with ⟨hR, hcord, hmk⟩
    have hml : s.markedList r = tourMarkedList sFull r := by
      simp only [OutTourAbs.markedList, tourMarkedList, hcord r, hmk]
    have hsp' : h + 1 + (tourMarkedList sFull r).length < 2 ^ w := by
      dsimp only [tourOutSpec] at hsp; rw [← hml]; omega
    have ⟨_, hw2⟩ := tourDS_wide_of_foot hR hfoot (by omega : h + 1 < 2 ^ w)
    let C := hp.toListExact (w := w) (by omega)
    obtain ⟨o, st', c, hrun, x', hrep', hlist', hval', hz', hfr', hft', hcost⟩ :=
      tourOp_listMarked_exact_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hrLt
        hfoot hz hsp'
    refine ⟨_, hp.op9_body, o, st', c, ⟨sFull, x'⟩, hrun,
      ⟨hrep', hcord, hmk⟩, by rwa [hml], by rw [hval', hml],
      ⟨by omega, by dsimp only [tourOutSpec] at hval' ⊢; rw [hval', hml]; omega,
       hz', hfr', fun a ha => Or.inl (hft' a ha)⟩, ?_⟩
    rw [hml]
    have hmono := Nat.mul_le_mul_right (ordStoreLog eCap)
      (Nat.mul_le_mul_right ((tourMarkedList sFull r).length + 1) tourMul_ge_query)
    dsimp only [tourOutRep, tourDSRep, tourOutSpec] at hcost ⊢
    omega

/-! ## Exact-space downstream query corollaries -/

/-- Exact-space `listMarked` theorem over `tourOutRep` (`tourOp b 9`), matching every requirement
of `AsmBrTourListAt` (exact `o.value = h + 1 + |out|`, `ZeroFrom`, zero footprint growth, cost
`≤ tourMul * (|out| + 1) * ordStoreLog eCap`). -/
theorem tourDS_listMarked_exact {w vCap eCap b tourH r h pos : ℕ} {p : Program}
    (hp : HasTourProcs p b) (ω : ℕ → Bool)
    {s : OutTourAbs} {tx : (tourOutRep vCap eCap).τ} {mem : ℕ → ℕ}
    (hrLt : r < vCap)
    (hrep : (tourOutRep vCap eCap).rep tourH s tx mem)
    (hfoot : ∀ a, (tourOutRep vCap eCap).foot tourH tx a → a < h)
    (hz : ZeroFrom mem h)
    (hroom : h + 1 + (s.markedList r).length < 2 ^ w) :
    ∃ body, p.procs[tourOp b 9]? = some body ∧ ∃ o st' c tx',
      Runs w p ω body (startState [tourH, r, h] mem pos) o st' c ∧
      (tourOutRep vCap eCap).rep tourH s tx' st'.mem ∧
      EndListAt st'.mem h (s.markedList r) ∧
      o.value = h + 1 + (s.markedList r).length ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ (tourOutRep vCap eCap).foot tourH tx a → st'.mem a = mem a) ∧
      (∀ a, (tourOutRep vCap eCap).foot tourH tx' a → (tourOutRep vCap eCap).foot tourH tx a) ∧
      c + (tourOutRep vCap eCap).phi tourH tx' st'.mem ≤
        tourMul * ((s.markedList r).length + 1) * ordStoreLog eCap +
          (tourOutRep vCap eCap).phi tourH tx mem := by
  rcases tx with ⟨sFull, xFull⟩
  rcases hrep with ⟨hR, hcord, hmk⟩
  have hml : s.markedList r = tourMarkedList sFull r := by
    simp only [OutTourAbs.markedList, tourMarkedList, hcord r, hmk]
  have hsp' : h + 1 + (tourMarkedList sFull r).length < 2 ^ w := by rw [← hml]; exact hroom
  have ⟨_, hw2⟩ := tourDS_wide_of_foot hR hfoot (by omega : h + 1 < 2 ^ w)
  let C := hp.toListExact (w := w) (by omega)
  obtain ⟨o, st', c, hrun, x', hrep', hlist', hval', hz', hfr', hft', hcost⟩ :=
    tourOp_listMarked_exact_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hrLt
      hfoot hz hsp'
  refine ⟨_, hp.op9_body, o, st', c, ⟨sFull, x'⟩, hrun,
    ⟨hrep', hcord, hmk⟩, by rwa [hml], by rw [hval', hml], hz', hfr', hft', ?_⟩
  rw [hml]
  have hmono := Nat.mul_le_mul_right (ordStoreLog eCap)
    (Nat.mul_le_mul_right ((tourMarkedList sFull r).length + 1) tourMul_ge_query)
  dsimp only [tourOutRep, tourDSRep] at hcost ⊢
  omega

/-- `tourProcs b` (`tourOp b 9`) directly instantiates `AsmBrTourListAt`
(`AssemblyBranchOrdDefs.lean`) on `tourOutRep` with multiplier `tourMul`. -/
theorem tourDS_asmBrTourListAt (w b : ℕ) (p : Program) (hp : HasTourProcs p b) :
    AsmBrTourListAt tourOutRep w p (tourOp b 9) tourMul where
  handle_foot vCap eCap tourH tx := tourOutRep_handle_foot vCap eCap tourH tx
  runs _ _ _ _ _ _ _ _ _ ω _ hrLt _ hrep hfoot hz hroom :=
    tourDS_listMarked_exact hp ω hrLt hrep hfoot hz hroom

/-- Exact-space `lenCoreTour` theorem over `tourOutRep` (`tourOp b 12`): requires only
`h + 1 < 2 ^ w`, writes `(s.cord r).length` at `h`, returns `h + 1`, and never grows `foot`. -/
theorem tourDS_lenCoreTour_exact {w vCap eCap b tourH r h pos : ℕ} {p : Program}
    (hp : HasTourProcs p b) (ω : ℕ → Bool)
    {s : OutTourAbs} {tx : (tourOutRep vCap eCap).τ} {mem : ℕ → ℕ}
    (hrLt : r < vCap)
    (hrep : (tourOutRep vCap eCap).rep tourH s tx mem)
    (hfoot : ∀ a, (tourOutRep vCap eCap).foot tourH tx a → a < h)
    (hz : ZeroFrom mem h) (hroom : h + 1 < 2 ^ w) :
    ∃ body, p.procs[tourOp b 12]? = some body ∧ ∃ o st' c tx',
      Runs w p ω body (startState [tourH, r, h] mem pos) o st' c ∧
      (tourOutRep vCap eCap).rep tourH s tx' st'.mem ∧
      st'.mem h = (s.cord r).length ∧
      o.value = h + 1 ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ (tourOutRep vCap eCap).foot tourH tx a → st'.mem a = mem a) ∧
      (∀ a, (tourOutRep vCap eCap).foot tourH tx' a → (tourOutRep vCap eCap).foot tourH tx a) ∧
      c + (tourOutRep vCap eCap).phi tourH tx' st'.mem ≤
        tourMul * ordStoreLog eCap + (tourOutRep vCap eCap).phi tourH tx mem := by
  rcases tx with ⟨sFull, xFull⟩
  rcases hrep with ⟨hR, hcord, hmk⟩
  have ⟨_, hw2⟩ := tourDS_wide_of_foot hR hfoot hroom
  let C := hp.toSplayCore (w := w) (by omega)
  obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hz', hfr', hft', hcost⟩ :=
    tourOp_len_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hrLt hfoot hz hroom
  refine ⟨_, hp.op12_body, o, st', c, ⟨sFull, x'⟩, hrun,
    ⟨hrep', hcord, hmk⟩, by rw [hans, hcord r], hval', hz', hfr', hft', ?_⟩
  rw [ordStoreLog_eq_tourLog]
  have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
  dsimp only [tourOutRep, tourDSRep] at hcost ⊢
  omega

/-- Exact-space `rootOf` theorem over `tourOutRep` (`tourOp b 10`): for `endOfKey key ∈ s.cord r`,
requires only `h + 1 < 2 ^ w`, writes `r` at `h`, returns `h + 1`, and never grows `foot`. -/
theorem tourDS_rootOf_exact {w vCap eCap b tourH key r h pos : ℕ} {p : Program}
    (hp : HasTourProcs p b) (ω : ℕ → Bool)
    {s : OutTourAbs} {tx : (tourOutRep vCap eCap).τ} {mem : ℕ → ℕ}
    (hmem : endOfKey key ∈ s.cord r)
    (hrep : (tourOutRep vCap eCap).rep tourH s tx mem)
    (hfoot : ∀ a, (tourOutRep vCap eCap).foot tourH tx a → a < h)
    (hz : ZeroFrom mem h) (hroom : h + 1 < 2 ^ w) :
    ∃ body, p.procs[tourOp b 10]? = some body ∧ ∃ o st' c tx',
      Runs w p ω body (startState [tourH, key, h] mem pos) o st' c ∧
      (tourOutRep vCap eCap).rep tourH s tx' st'.mem ∧
      st'.mem h = r ∧
      o.value = h + 1 ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ (tourOutRep vCap eCap).foot tourH tx a → st'.mem a = mem a) ∧
      (∀ a, (tourOutRep vCap eCap).foot tourH tx' a → (tourOutRep vCap eCap).foot tourH tx a) ∧
      c + (tourOutRep vCap eCap).phi tourH tx' st'.mem ≤
        tourMul * ordStoreLog eCap + (tourOutRep vCap eCap).phi tourH tx mem := by
  rcases tx with ⟨sFull, xFull⟩
  rcases hrep with ⟨hR, hcord, hmk⟩
  obtain ⟨_, _, hact, hroot⟩ := coreTour_mem_info hR.valid (hcord r ▸ hmem)
  have ⟨_, hw2⟩ := tourDS_wide_of_foot hR hfoot hroom
  let C := hp.toSplayCore (w := w) (by omega)
  obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hz', hfr', hft', hcost⟩ :=
    tourOp_rootOf_exact_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hR hact hfoot hz hroom
  refine ⟨_, hp.op10_body, o, st', c, ⟨sFull, x'⟩, hrun,
    ⟨hrep', hcord, hmk⟩, by rw [hans, hroot], hval', hz', hfr', hft', ?_⟩
  rw [ordStoreLog_eq_tourLog]
  have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
  dsimp only [tourOutRep, tourDSRep] at hcost ⊢
  omega

/-- Exact-space `O(1)` `vertOwner` theorem over `tourDSRep` (`tourOp b 13`): requires only
`h + 1 < 2 ^ w`, writes `ordSrc s.ord (endOfKey key)` at `h`, returns `h + 1`, never modifies
`foot`, and runs in worst-case `≤ 80` steps. -/
theorem tourDS_vertOwner_exact {w vCap eCap b tourH key h pos : ℕ} {p : Program}
    (hp : HasTourProcs p b) (ω : ℕ → Bool)
    {s : TourAbs} {x : TourConcrete OrdStoreState} {mem : ℕ → ℕ}
    (hact : ∃ u, endOfKey key ∈ s.ord u)
    (hrep : (tourDSRep vCap eCap).rep tourH s x mem)
    (hfoot : ∀ a, (tourDSRep vCap eCap).foot tourH x a → a < h)
    (hz : ZeroFrom mem h) (hroom : h + 1 < 2 ^ w) :
    ∃ body, p.procs[tourOp b 13]? = some body ∧ ∃ o st' c,
      Runs w p ω body (startState [tourH, key, h] mem pos) o st' c ∧
      (tourDSRep vCap eCap).rep tourH s x st'.mem ∧
      st'.mem h = ordSrc s.ord (endOfKey key) ∧
      o.value = h + 1 ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ (tourDSRep vCap eCap).foot tourH x a → st'.mem a = mem a) ∧
      c + (tourDSRep vCap eCap).phi tourH x st'.mem ≤
        80 + (tourDSRep vCap eCap).phi tourH x mem := by
  obtain ⟨o, st', c, hrun, hval', hrep', hans, hz', hfr', hcost⟩ :=
    tourOp_vertOwner_runs (pos := pos) (ordStoreRep_local vCap eCap) ω hrep hact hfoot hz hroom
  exact ⟨_, hp.op13_body, o, st', c, hrun, hrep', hans, hval', hz', hfr', hcost⟩

end MinCostFlow.SparseCore.Program
