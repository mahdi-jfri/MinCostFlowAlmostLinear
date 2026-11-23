module

public import MinCostFlow.SparseCore.Program.OrdStoreInit
public import MinCostFlow.SparseCore.Program.OrdStoreEdit
public import MinCostFlow.SparseCore.Program.OrdStoreList
public import MinCostFlow.SparseCore.Program.OrdStoreNext
import Mathlib.Tactic

/-!
# Order Store Data Structure Assembly (`DSRep.Implements`)

This file assembles the 19 deterministic Word-RAM procedures of the order store into
`ordStoreProcs b` and proves that they implement `ordStoreCapContract` with:
* constant factor `ordStoreMul := 32000` (free of the input),
* space allocation `ordStoreAlloc` (`ordArenaSize vCap eCap` for `init`, `3 * words + 2` for `edit`),
* representation `ordStoreRep vCap eCap` (satisfying `DSRep.Local`),
* determinism (`ordStoreProcs_noRand`), and
* non-vacuity (`ordStore_nonvacuous`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState MinCostFlow.DynSpanner.Program

/-- The 19 deterministic procedures of the order store, relocated to start at index `b`. -/
def ordStoreProcs (b : ℕ) : List Stmt :=
  [ ordRotateBody,
    ordSplayStepBody (b + 0),
    ordSplayBody (b + 1),
    ordSplayRootBody (b + 2),
    ordSiftDownBody (b + 4),
    ordHeapSortBody (b + 4),
    ordWalkExtremeBody (b + 2),
    ordJoinBody (b + 6),
    ordUnlinkBody (b + 2) (b + 7),
    ordAllocBody,
    ordFreeTreeBody,
    ordDropEdgeBody (b + 8) (b + 10),
    ordInsertBeforeBody (b + 9) (b + 3) (b + 7),
    ordRotateToBody (b + 3) (b + 7),
    ordMoveEndsBody (b + 3) (b + 5) (b + 8) (b + 7) (b + 10),
    ordStoreInitBody,
    ordStoreEditBody (b + 11) (b + 12) (b + 13) (b + 14),
    ordStoreListBody,
    ordStoreNextBody (b + 3) ]

/-- Program `p` contains the 19 order-store procedures starting at procedure index `b`. -/
def HasOrdStoreProcs (p : Program) (b : ℕ) : Prop :=
  ∀ i < (ordStoreProcs b).length, p.procs[b + i]? = (ordStoreProcs b)[i]?

/-- Procedure index of initialization `[vCap, eCap, ord, heap]` inside `ordStoreProcs b`. -/
def ordStoreInit (b : ℕ) : ℕ := b + 15

/-- Procedure index of operation `i` (`0` = edit, `1` = list, `2` = next) inside
`ordStoreProcs b`. -/
def ordStoreOp (b i : ℕ) : ℕ :=
  match i with
  | 0 => b + 16
  | 1 => b + 17
  | _ => b + 18

/-- Universal cost constant (independent of the input). -/
def ordStoreMul : ℕ := 32000

/-- Scratch and arena space bound for `ordStoreCapContract`. -/
def ordStoreAlloc (i : ℕ) (args : List ℕ) : ℕ :=
  match i with
  | 3 => ordArenaSize (args.getD 0 0) (args.getD 1 0)
  | 0 => 3 * args.getD 2 0 + 2
  | _ => 0

/-- Every procedure of `ordStoreProcs b` is deterministic (`Stmt.NoRand`). -/
theorem ordStoreProcs_noRand (b : ℕ) : ∀ s ∈ ordStoreProcs b, s.NoRand := by
  intro s hs
  simp only [ordStoreProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact ordRotateBody_noRand
  · exact ordSplayStepBody_noRand _
  · exact ordSplayBody_noRand _
  · exact ordSplayRootBody_noRand _
  · exact ordSiftDownBody_noRand _
  · exact ordHeapSortBody_noRand _
  · exact ordWalkExtremeBody_noRand _
  · exact ordJoinBody_noRand _
  · exact ordUnlinkBody_noRand _ _
  · exact ordAllocBody_noRand
  · exact ordFreeTreeBody_noRand
  · exact ordDropEdgeBody_noRand _ _
  · exact ordInsertBeforeBody_noRand _ _ _
  · exact ordRotateToBody_noRand _ _
  · exact ordMoveEndsBody_noRand _ _ _ _ _
  · exact ordStoreInitBody_noRand
  · exact ordStoreEditBody_noRand _ _ _ _
  · exact ordStoreListBody_noRand
  · exact ordStoreNextBody_noRand _

/-- Concrete representation of the order store with capacities `(vCap, eCap)`. -/
def ordStoreRep (vCap eCap : ℕ) : DSRep (ℕ → List End) where
  τ := OrdStoreState
  rep b ord S mem := OrdInv ord S ∧ OrdArenaAt b S mem ∧ S.vCap = vCap ∧ S.eCap = eCap
  phi _ S _ := ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S
  foot b _ a := ordFoot b vCap eCap a

theorem ordStoreRep_local (vCap eCap : ℕ) : (ordStoreRep vCap eCap).Local := by
  intro b s S mem mem' hagree
  refine ⟨fun ⟨hinv, harena, hv, he⟩ => ⟨hinv, ?_, hv, he⟩, rfl⟩
  exact harena.congr hinv.next_le fun a ha =>
    (hagree a (by rwa [hv, he] at ha)).symm

private theorem foot_below_imp_arena_le {b vCap eCap heap : ℕ}
    (h : ∀ a, ordFoot b vCap eCap a → a < heap) :
    b + ordArenaSize vCap eCap ≤ heap := by
  have hpos : 0 < ordArenaSize vCap eCap := by unfold ordArenaSize; omega
  have ha : ordFoot b vCap eCap (b + ordArenaSize vCap eCap - 1) := by
    unfold ordFoot; omega
  have hlt := h (b + ordArenaSize vCap eCap - 1) ha
  omega

/-- Concrete implementation theorem: `ordStoreProcs b` implements `ordStoreCapContract` with
`ordStoreRep vCap eCap`, constant `ordStoreMul`, and space bound `ordStoreAlloc`. -/
theorem ordStore_implements_cap (w vCap eCap : ℕ) (p : Program) (b : ℕ)
    (hp : HasOrdStoreProcs p b) (_hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) :
    (ordStoreRep vCap eCap).Local ∧
    (ordStoreRep vCap eCap).Implements w p (ordStoreInit b) (ordStoreOp b)
      (ordStoreCapContract vCap eCap ordStoreMul ordStoreAlloc) := by
  have hloc := ordStoreRep_local vCap eCap
  have hproc : ∀ i < 19, p.procs[b + i]? = (ordStoreProcs b)[i]? := fun i hi => hp i hi
  have h0 : p.procs[b + 0]? = some ordRotateBody := hproc 0 (by decide)
  have h1 : p.procs[b + 1]? = some (ordSplayStepBody (b + 0)) := hproc 1 (by decide)
  have h2 : p.procs[b + 2]? = some (ordSplayBody (b + 1)) := hproc 2 (by decide)
  have h3 : p.procs[b + 3]? = some (ordSplayRootBody (b + 2)) := hproc 3 (by decide)
  have h4 : p.procs[b + 4]? = some (ordSiftDownBody (b + 4)) := hproc 4 (by decide)
  have h5 : p.procs[b + 5]? = some (ordHeapSortBody (b + 4)) := hproc 5 (by decide)
  have h6 : p.procs[b + 6]? = some (ordWalkExtremeBody (b + 2)) := hproc 6 (by decide)
  have h7 : p.procs[b + 7]? = some (ordJoinBody (b + 6)) := hproc 7 (by decide)
  have h8 : p.procs[b + 8]? = some (ordUnlinkBody (b + 2) (b + 7)) := hproc 8 (by decide)
  have h9 : p.procs[b + 9]? = some ordAllocBody := hproc 9 (by decide)
  have h10 : p.procs[b + 10]? = some ordFreeTreeBody := hproc 10 (by decide)
  have h11 : p.procs[b + 11]? = some (ordDropEdgeBody (b + 8) (b + 10)) := hproc 11 (by decide)
  have h12 : p.procs[b + 12]? = some (ordInsertBeforeBody (b + 9) (b + 3) (b + 7)) := hproc 12 (by decide)
  have h13 : p.procs[b + 13]? = some (ordRotateToBody (b + 3) (b + 7)) := hproc 13 (by decide)
  have h14 : p.procs[b + 14]? = some (ordMoveEndsBody (b + 3) (b + 5) (b + 8) (b + 7) (b + 10)) :=
    hproc 14 (by decide)
  have h15 : p.procs[b + 15]? = some ordStoreInitBody := hproc 15 (by decide)
  have h16 : p.procs[b + 16]? = some (ordStoreEditBody (b + 11) (b + 12) (b + 13) (b + 14)) :=
    hproc 16 (by decide)
  have h17 : p.procs[b + 17]? = some ordStoreListBody := hproc 17 (by decide)
  have h18 : p.procs[b + 18]? = some (ordStoreNextBody (b + 3)) := hproc 18 (by decide)
  refine ⟨hloc, hloc, ?_, ?_⟩
  · -- Initialization
    intro args mem pos ω _ hpre hz hsp
    rcases hpre with ⟨ordPtr, heap, words, rfl, hord, hord_le, huniq⟩
    have hheap : heapArg [vCap, eCap, ordPtr, heap] = heap := by simp [heapArg]
    have hsp' : heap + ordArenaSize vCap eCap < 2 ^ w := by
      simpa [ordStoreCapContract, ordStoreAlloc, hheap] using hsp
    have hz' : ZeroFrom mem heap := by simpa [hheap] using hz
    obtain ⟨o, st', c, hrun, hval, S', hinv', harena', hv', he', hz', hlt', hcost⟩ :=
      ordStoreInitBody_runs (p := p) ω hord hord_le huniq hz' hsp' (pos := pos)
    refine ⟨ordStoreInitBody, h15, o, st', c, hrun, readOrd mem ordPtr, S',
      ⟨by simpa [hheap] using hinv', by simpa [hheap] using harena', hv', he'⟩,
      by simp [ordStoreCapContract],
      ⟨by simp [hheap, hval], by simp [ordStoreCapContract, ordStoreAlloc, hheap, hval],
       by simpa [hval] using hz', fun a ha _ => hlt' a (by simpa [hheap] using ha),
       fun a ha => Or.inr (by simp only [ordStoreRep, ordFoot, hheap, hval] at ha ⊢; exact ha)⟩, ?_⟩
    simp only [ordStoreCapContract, ordStoreRep, List.getD_cons_succ, List.getD_cons_zero]
    have hmul : ORD_INIT_MUL * (1 + ordRecordsWords (readOrdRecordsAt mem ordPtr)) * ordStoreLog eCap ≤
        ordStoreMul * (1 + ordRecordsWords (readOrdRecordsAt mem ordPtr)) * ordStoreLog eCap :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by unfold ORD_INIT_MUL ordStoreMul; omega))
    omega
  · -- Operations 0 (edit), 1 (list), 2 (next)
    intro i handle s S args mem pos ω _ hhead ⟨hinv, harena, hvS, heS⟩ hpre hfoot hz hsp
    match i with
    | 0 =>
      rcases hpre with ⟨h0', edits, words, heap, rfl, hedits, hedits_le, hwithin, huniq_all⟩
      have hh : h0' = handle := by simpa using hhead
      subst h0'
      have hheap : heapArg [handle, edits, words, heap] = heap := by simp [heapArg]
      have hfoot' : handle + ordArenaSize S.vCap S.eCap ≤ heap := by
        rw [hvS, heS]; exact foot_below_imp_arena_le fun a ha => by simpa [hheap] using hfoot a ha
      have hz' : ZeroFrom mem heap := by simpa [hheap] using hz
      have hsp' : heap + (3 * words + 2) < 2 ^ w := by
        simpa [ordStoreCapContract, ordStoreAlloc, hheap] using hsp
      obtain ⟨o, st', c, hrun, hval, S', hinv', harena', hfr', hv', he', hcost⟩ :=
        ordStoreEditBody_runs h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 ω
          hinv harena hedits hedits_le (by rw [hvS, heS]; exact hwithin)
          (by rw [hvS, heS]; exact huniq_all) hfoot' hz' hsp' (pos := pos)
      refine ⟨ordStoreEditBody (b + 11) (b + 12) (b + 13) (b + 14), h16, o, st', c, hrun,
        applyOrdEdits s (readOrdEdits mem edits), S',
        ⟨hinv', harena', hv'.trans hvS, he'.trans heS⟩,
        by simp [ordStoreCapContract],
        ⟨by simp [hheap, hval], by simp [ordStoreCapContract, ordStoreAlloc, hheap, hval],
         by simpa [hval] using hfr'.1,
         fun a ha hnf => hfr'.2 a (by simpa [hheap] using ha) (by rw [hvS, heS]; exact hnf),
         fun a ha => Or.inl ha⟩, ?_⟩
      simp only [ordStoreCapContract, ordStoreRep, List.getD_cons_succ, List.getD_cons_zero]
      rw [heS] at hcost
      unfold ORD_EDIT_MUL at hcost; unfold ordStoreMul
      omega
    | 1 =>
      rcases hpre with ⟨h0', v, heap, rfl, hv⟩
      have hh : h0' = handle := by simpa using hhead
      subst h0'
      have hheap : heapArg [handle, v, heap] = heap := by simp [heapArg]
      have hfoot' : handle + ordArenaSize S.vCap S.eCap ≤ heap := by
        rw [hvS, heS]; exact foot_below_imp_arena_le fun a ha => by simpa [hheap] using hfoot a ha
      have hz' : ZeroFrom mem heap := by simpa [hheap] using hz
      have hsp' : heap + (1 + (s v).length) < 2 ^ w := by
        simpa [ordStoreCapContract, hheap] using hsp
      obtain ⟨o, st', c, hrun, hval, harena', hlist', hz', hlt', hcost⟩ :=
        ordStoreListBody_runs (p := p) ω hinv harena (by rw [hvS]; exact hv) hfoot' hz' hsp' (pos := pos)
      refine ⟨ordStoreListBody, h17, o, st', c, hrun, s, S,
        ⟨hinv, harena', hvS, heS⟩,
        ⟨rfl, by simpa [ordStoreCapContract] using hlist'⟩,
        ⟨by simp [hheap, hval]; omega, by simp [ordStoreCapContract, hheap, hval]; omega,
         by simpa [hval] using hz',
         fun a ha _ => hlt' a (by simpa [hheap] using ha),
         fun a ha => Or.inl ha⟩, ?_⟩
      simp only [ordStoreCapContract, ordStoreRep, List.getD_cons_succ, List.getD_cons_zero]
      have hmul : ORD_LIST_MUL * ((s v).length + 1) ≤ ordStoreMul * ((s v).length + 1) :=
        Nat.mul_le_mul_right _ (by unfold ORD_LIST_MUL ordStoreMul; omega)
      omega
    | 2 =>
      rcases hpre with ⟨h0', v, key, heap, rfl, hv, hkey_mem⟩
      have hh : h0' = handle := by simpa using hhead
      subst h0'
      have hheap : heapArg [handle, v, key, heap] = heap := by simp [heapArg]
      have hfoot' : handle + ordArenaSize S.vCap S.eCap ≤ heap := by
        rw [hvS, heS]; exact foot_below_imp_arena_le fun a ha => by simpa [hheap] using hfoot a ha
      have hz' : ZeroFrom mem heap := by simpa [hheap] using hz
      have hsp' : heap + 1 < 2 ^ w := by
        simpa [ordStoreCapContract, hheap] using hsp
      obtain ⟨o, st', c, hrun, hval, S', hinv', harena', hv', he', hnext', hz', hlt', hcost⟩ :=
        ordStoreNextBody_runs h0 h1 h2 h3 ω hinv harena (by rw [hvS]; exact hv) hkey_mem
          hfoot' hz' hsp' (pos := pos)
      refine ⟨ordStoreNextBody (b + 3), h18, o, st', c, hrun, s, S',
        ⟨hinv', harena', hv'.trans hvS, he'.trans heS⟩,
        ⟨rfl, by simpa [ordStoreCapContract] using hnext'⟩,
        ⟨by simp [hheap, hval], by simp [ordStoreCapContract, hheap, hval],
         by simpa [hval] using hz',
         fun a ha hnf => hlt' a (by simpa [hheap] using ha) (by rw [hvS, heS]; exact hnf),
         fun a ha => Or.inl ha⟩, ?_⟩
      simp only [ordStoreCapContract, ordStoreRep]
      rw [heS] at hcost
      have hmul : ORD_NEXT_MUL * ordStoreLog eCap ≤ ordStoreMul * ordStoreLog eCap :=
        Nat.mul_le_mul_right _ (by unfold ORD_NEXT_MUL ordStoreMul; omega)
      omega
    | i + 3 => exact False.elim hpre

/-- Signature matching `sig_ordStore_implements` (with `ordStoreCapContract`). -/
theorem ordStore_implements :
    ∃ (mul : ℕ) (allocation : ℕ → List ℕ → ℕ), ∀ (w vCap eCap : ℕ) (p : Program) (b : ℕ),
      HasOrdStoreProcs p b → (vCap + eCap + 2) ^ 2 < 2 ^ w →
      ∃ R : DSRep (ℕ → List End), R.Local ∧
        R.Implements w p (ordStoreInit b) (ordStoreOp b)
          (ordStoreCapContract vCap eCap mul allocation) :=
  ⟨ordStoreMul, ordStoreAlloc, fun w vCap eCap p b hp hw =>
    ⟨ordStoreRep vCap eCap, ordStore_implements_cap w vCap eCap p b hp hw⟩⟩

/-- Non-vacuity witness: for any `w, vCap, eCap` with `1 + ordArenaSize vCap eCap < 2 ^ w`,
the standalone deterministic program `⟨ordStoreProcs 0⟩` satisfies `HasOrdStoreProcs`,
`Stmt.NoRand` for every procedure, and all initialization hypotheses of `ordStoreCapContract`
on the all-zero memory with `args = [vCap, eCap, 0, 1]`. -/
theorem ordStore_nonvacuous (w vCap eCap : ℕ) (hw : 1 + ordArenaSize vCap eCap < 2 ^ w) :
    let p : Program := ⟨ordStoreProcs 0⟩
    let D := ordStoreCapContract vCap eCap ordStoreMul ordStoreAlloc
    let args := [vCap, eCap, 0, 1]
    let mem : ℕ → ℕ := fun _ => 0
    HasOrdStoreProcs p 0 ∧
      (∀ s ∈ p.procs, s.NoRand) ∧
      (∀ a ∈ args, a < 2 ^ w) ∧
      D.initPre args mem ∧
      ZeroFrom mem (heapArg args) ∧
      heapArg args + D.initSpace args mem < 2 ^ w := by
  have hsz : 16 + vCap + 18 * eCap = ordArenaSize vCap eCap := rfl
  refine ⟨fun i hi => by simp [hi], ordStoreProcs_noRand 0, ?_, ?_, fun _ _ => rfl, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  · refine ⟨0, 1, 1, rfl, ?_, by omega, ?_⟩
    · refine ⟨by simp [readOrdRecordsAt, readOrdRecords], by funext u; rfl,
        by simp [readOrdRecordsAt, readOrdRecords, ordRecordsWords]⟩
    · refine ⟨⟨fun _ => List.nodup_nil, fun _ _ => rfl, fun _ _ h => by simp [readOrd, readOrdRecordsAt, readOrdRecords, ordOfRecords] at h⟩,
        fun _ _ _ h => by simp [readOrd, readOrdRecordsAt, readOrdRecords, ordOfRecords] at h⟩
  · simpa [ordStoreCapContract, ordStoreAlloc, heapArg] using hw

end MinCostFlow.SparseCore.Program
