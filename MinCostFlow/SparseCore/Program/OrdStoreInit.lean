module

public import MinCostFlow.SparseCore.Program.OrdStoreInitStep
import Mathlib.Tactic

/-!
# Order Store Initialization Procedure (`init`)

This file implements and verifies `ordStoreInitBody` on `[vCap, eCap, ordPtr, heap]`:
* writes the 8-word arena header (`vCap`, `eCap`, `vr`, `en`, `nb`, `nextNode`, `freeHead = 0`, `0`)
  at `heap`,
* loops over the `mem ordPtr` records of `OrdListAt mem ordPtr (readOrd mem ordPtr) words`,
  building a left-leaning spine for each non-empty vertex list via `ordInitInnerLoop`, setting
  its root's `ppar := v + 1` and `vRoot[v] := root`,
* writes the final `nextNode` at `heap + 5` and returns `heap + ordArenaSize vCap eCap`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState MinCostFlow.DynSpanner.Program

def ORD_INIT_MUL : ℕ := 2000

/-- Outer loop of `ordStoreInit`: reads `r7` vertex records starting at `r8`. -/
def ordInitOuterLoop : Stmt :=
  .loop (.bin .lt (.reg 10) (.reg 7))
    (.assign 11 (.load (.reg 8)) ;;
     .assign 12 (.load (.bin .add (.reg 8) (.const 1))) ;;
     .assign 8 (.bin .add (.reg 8) (.const 2)) ;;
     .cond (.reg 12)
       (.assign 13 (.const 0) ;;
        .assign 14 (.const 0) ;;
        ordInitInnerLoop ;;
        .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 8) (.reg 13))) (.const 3))
          (.bin .add (.reg 11) (.const 1)) ;;
        .store (.bin .add (.reg 4) (.reg 11)) (.reg 13))
       .nop ;;
     .assign 8 (.bin .add (.reg 8) (.reg 12)) ;;
     .assign 10 (.bin .add (.reg 10) (.const 1)))

/-- Header setup prefix of `ordStoreInit`. -/
def ordInitHeaderStmt : Stmt :=
  .assign 4 (.bin .add (.reg 3) (.const 8)) ;;
  .assign 5 (.bin .add (.reg 4) (.reg 0)) ;;
  .assign 6 (.bin .add (.reg 5) (.bin .add (.reg 1) (.reg 1))) ;;
  .store (.reg 3) (.reg 0) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 1) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.reg 4) ;;
  .store (.bin .add (.reg 3) (.const 3)) (.reg 5) ;;
  .store (.bin .add (.reg 3) (.const 4)) (.reg 6) ;;
  .assign 7 (.load (.reg 2)) ;;
  .assign 8 (.bin .add (.reg 2) (.const 1)) ;;
  .assign 9 (.const 0) ;;
  .assign 10 (.const 0)

/-- `ordStoreInit` on `[vCap, eCap, ordPtr, heap]`. -/
def ordStoreInitBody : Stmt :=
  ordInitHeaderStmt ;;
  ordInitOuterLoop ;;
  .store (.bin .add (.reg 3) (.const 5)) (.reg 9) ;;
  .assign 17 (.bin .add (.reg 6) (.bin .mul (.const 8) (.bin .add (.bin .add (.reg 1) (.reg 1)) (.const 1)))) ;;
  .ret (.reg 17)

theorem ordStoreInitBody_noRand : ordStoreInitBody.NoRand := by
  simp [ordStoreInitBody, ordInitHeaderStmt, ordInitOuterLoop, ordInitInnerLoop_noRand, Stmt.NoRand]

/-! ### Helper 1: header setup prefix -/

private theorem ordInitHeader_runs
    {w vCap eCap ordPtr heap words pos : ℕ} {p : Program} (ω : ℕ → Bool) {mem : ℕ → ℕ}
    (hord : OrdListAt mem ordPtr (readOrd mem ordPtr) words)
    (hord_le : ordPtr + words ≤ heap)
    (hz : ZeroFrom mem heap) (hw : heap + ordArenaSize vCap eCap < 2 ^ w) :
    ∃ stH cH,
      Runs w p ω ordInitHeaderStmt (startState [vCap, eCap, ordPtr, heap] mem pos) .normal stH cH ∧
      stH.regs 1 = eCap ∧ stH.regs 3 = heap ∧ stH.regs 4 = ordVRootBase heap ∧
      stH.regs 5 = ordENodeBase heap vCap ∧ stH.regs 6 = ordNodesBase heap vCap eCap ∧
      stH.regs 7 = mem ordPtr ∧ stH.regs 8 = ordPtr + 1 ∧ stH.regs 9 = 0 ∧ stH.regs 10 = 0 ∧
      stH.mem heap = vCap ∧ stH.mem (heap + 1) = eCap ∧ stH.mem (heap + 2) = ordVRootBase heap ∧
      stH.mem (heap + 3) = ordENodeBase heap vCap ∧ stH.mem (heap + 4) = ordNodesBase heap vCap eCap ∧
      (∀ a ≥ heap + 5, stH.mem a = 0) ∧ (∀ a < heap, stH.mem a = mem a) ∧ cH ≤ 120 := by
  have hw' : heap + (16 + vCap + 18 * eCap) < 2 ^ w := hw
  have hwords_pos : 1 ≤ words := by have := hord.2.2; omega
  set vr := ordVRootBase heap with hvr_def
  set en := ordENodeBase heap vCap with hen_def
  set nb := ordNodesBase heap vCap eCap with hnb_def
  have hvr_eq : vr = heap + 8 := rfl
  have hen_eq : en = heap + 8 + vCap := by rw [hen_def]; unfold ordENodeBase; omega
  have hnb_eq : nb = heap + 8 + vCap + 2 * eCap := by rw [hnb_def]; unfold ordNodesBase; omega
  set st0 : State := startState [vCap, eCap, ordPtr, heap] mem pos
  have ha4 : Runs w p ω (.assign 4 (.bin .add (.reg 3) (.const 8))) st0 .normal
      { st0 with regs := Function.update st0.regs 4 vr } _ :=
    runs_assign_iff.mpr ⟨vr, Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st0, startState]))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  set st1 : State := { st0 with regs := Function.update st0.regs 4 vr }
  have ha5 : Runs w p ω (.assign 5 (.bin .add (.reg 4) (.reg 0))) st1 .normal
      { st1 with regs := Function.update st1.regs 5 en } _ :=
    runs_assign_iff.mpr ⟨en, Expr.eval_add (Expr.eval_reg_of_eq (v := vr) (by simp [st1]))
      (Expr.eval_reg_of_eq (v := vCap) (by simp [st1, st0, startState])) (by omega), rfl, rfl, rfl⟩
  set st2 : State := { st1 with regs := Function.update st1.regs 5 en }
  have ha6 : Runs w p ω (.assign 6 (.bin .add (.reg 5) (.bin .add (.reg 1) (.reg 1)))) st2 .normal
      { st2 with regs := Function.update st2.regs 6 nb } _ :=
    runs_assign_iff.mpr ⟨nb, by
      have he : (Expr.bin .add (.reg 5) (.bin .add (.reg 1) (.reg 1))).eval w st2 = some (en + (eCap + eCap)) :=
        Expr.eval_add (Expr.eval_reg_of_eq (v := en) (by simp [st2]))
          (Expr.eval_add (Expr.eval_reg_of_eq (v := eCap) (by simp [st2, st1, st0, startState]))
            (Expr.eval_reg_of_eq (v := eCap) (by simp [st2, st1, st0, startState])) (by omega)) (by omega)
      rwa [show en + (eCap + eCap) = nb by omega] at he, rfl, rfl, rfl⟩
  set st3 : State := { st2 with regs := Function.update st2.regs 6 nb }
  have hs0 : Runs w p ω (.store (.reg 3) (.reg 0)) st3 .normal
      { st3 with mem := Function.update mem heap vCap } _ :=
    runs_store_iff.mpr ⟨heap, vCap, Expr.eval_reg_of_eq (by simp [st3, st2, st1, st0, startState]),
      Expr.eval_reg_of_eq (by simp [st3, st2, st1, st0, startState]), rfl, rfl, rfl⟩
  set m1 := Function.update mem heap vCap
  set st4 : State := { st3 with mem := m1 }
  have hs1 : Runs w p ω (.store (.bin .add (.reg 3) (.const 1)) (.reg 1)) st4 .normal
      { st4 with mem := Function.update m1 (heap + 1) eCap } _ :=
    runs_store_iff.mpr ⟨heap + 1, eCap, Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st4, st3, st2, st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega), Expr.eval_reg_of_eq (by simp [st4, st3, st2, st1, st0, startState]), rfl, rfl, rfl⟩
  set m2 := Function.update m1 (heap + 1) eCap
  set st5 : State := { st4 with mem := m2 }
  have hs2 : Runs w p ω (.store (.bin .add (.reg 3) (.const 2)) (.reg 4)) st5 .normal
      { st5 with mem := Function.update m2 (heap + 2) vr } _ :=
    runs_store_iff.mpr ⟨heap + 2, vr, Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st5, st4, st3, st2, st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega), Expr.eval_reg_of_eq (by simp [st5, st4, st3, st2, st1]), rfl, rfl, rfl⟩
  set m3 := Function.update m2 (heap + 2) vr
  set st6 : State := { st5 with mem := m3 }
  have hs3 : Runs w p ω (.store (.bin .add (.reg 3) (.const 3)) (.reg 5)) st6 .normal
      { st6 with mem := Function.update m3 (heap + 3) en } _ :=
    runs_store_iff.mpr ⟨heap + 3, en, Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st6, st5, st4, st3, st2, st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega), Expr.eval_reg_of_eq (by simp [st6, st5, st4, st3, st2]), rfl, rfl, rfl⟩
  set m4 := Function.update m3 (heap + 3) en
  set st7 : State := { st6 with mem := m4 }
  have hs4 : Runs w p ω (.store (.bin .add (.reg 3) (.const 4)) (.reg 6)) st7 .normal
      { st7 with mem := Function.update m4 (heap + 4) nb } _ :=
    runs_store_iff.mpr ⟨heap + 4, nb, Expr.eval_add (Expr.eval_reg_of_eq (v := heap) (by simp [st7, st6, st5, st4, st3, st2, st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega), Expr.eval_reg_of_eq (by simp [st7, st6, st5, st4, st3]), rfl, rfl, rfl⟩
  set m5 := Function.update m4 (heap + 4) nb
  set st8 : State := { st7 with mem := m5 }
  have hm5_lt : ∀ a < heap, m5 a = mem a := fun a ha => by
    dsimp only [m5, m4, m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hm5_ge5 : ∀ a ≥ heap + 5, m5 a = 0 := fun a ha => by
    dsimp only [m5, m4, m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hz a (by omega)
  have ha7 : Runs w p ω (.assign 7 (.load (.reg 2))) st8 .normal
      { st8 with regs := Function.update st8.regs 7 (mem ordPtr) } _ :=
    runs_assign_iff.mpr ⟨mem ordPtr, Expr.eval_load_of_eq
      (Expr.eval_reg_of_eq (v := ordPtr) (by simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState]))
      (hm5_lt ordPtr (by omega)), rfl, rfl, rfl⟩
  set st9 : State := { st8 with regs := Function.update st8.regs 7 (mem ordPtr) }
  have ha8 : Runs w p ω (.assign 8 (.bin .add (.reg 2) (.const 1))) st9 .normal
      { st9 with regs := Function.update st9.regs 8 (ordPtr + 1) } _ :=
    runs_assign_iff.mpr ⟨ordPtr + 1, Expr.eval_add
      (Expr.eval_reg_of_eq (v := ordPtr) (by simp [st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState]))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  set st10 : State := { st9 with regs := Function.update st9.regs 8 (ordPtr + 1) }
  have ha9 : Runs w p ω (.assign 9 (.const 0)) st10 .normal
      { st10 with regs := Function.update st10.regs 9 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set st11 : State := { st10 with regs := Function.update st10.regs 9 0 }
  have ha10 : Runs w p ω (.assign 10 (.const 0)) st11 .normal
      { st11 with regs := Function.update st11.regs 10 0 } _ :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set st12 : State := { st11 with regs := Function.update st11.regs 10 0 }
  refine ⟨st12, _, ord_runs_seq_normal ha4 (ord_runs_seq_normal ha5 (ord_runs_seq_normal ha6
    (ord_runs_seq_normal hs0 (ord_runs_seq_normal hs1 (ord_runs_seq_normal hs2
      (ord_runs_seq_normal hs3 (ord_runs_seq_normal hs4 (ord_runs_seq_normal ha7
        (ord_runs_seq_normal ha8 (ord_runs_seq_normal ha9 ha10)))))))))),
    by simp [st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
    by simp [st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState],
    by simp [st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, hvr_def],
    by simp [st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, hen_def],
    by simp [st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, hnb_def],
    by simp [st12, st11, st10, st9], by simp [st12, st11, st10],
    by simp [st12, st11], by simp [st12],
    by dsimp only [st12, st11, st10, st9, st8, m5, m4, m3, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
    by dsimp only [st12, st11, st10, st9, st8, m5, m4, m3, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
    by dsimp only [st12, st11, st10, st9, st8, m5, m4, m3, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self, hvr_def],
    by dsimp only [st12, st11, st10, st9, st8, m5, m4, m3, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_self, hen_def],
    by dsimp only [st12, st11, st10, st9, st8, m5]; rw [Function.update_self, hnb_def],
    hm5_ge5, hm5_lt, by simp [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]⟩

/-! ### Helper 2: outer record loop -/

private theorem ordInitOuterLoop_runs
    {w vCap eCap ordPtr heap : ℕ} {p : Program} (ω : ℕ → Bool) {mem : ℕ → ℕ}
    (huniq : OrdUniqueWithin vCap eCap (readOrd mem ordPtr))
    (hcnt_w : mem ordPtr < 2 ^ w)
    (hw : heap + ordArenaSize vCap eCap < 2 ^ w) :
    ∀ rem (i ptr : ℕ) (st : State) (S : OrdStoreState) (curOrd : ℕ → List End),
      i + rem = mem ordPtr →
      (let remRecs := readOrdRecords mem rem ptr; (remRecs.map Prod.fst).Nodup) →
      ptr + ordRecordsWords (readOrdRecords mem rem ptr) ≤ heap →
      S.nextNode + ((readOrdRecords mem rem ptr).map fun r => r.2.length).sum ≤ 2 * eCap →
      (∀ v, curOrd v = [] ∨ ordOfRecords (readOrdRecords mem rem ptr) v = []) →
      (∀ v, (if curOrd v ≠ [] then curOrd v else ordOfRecords (readOrdRecords mem rem ptr) v) = readOrd mem ordPtr v) →
      OrdInv curOrd S → S.vCap = vCap → S.eCap = eCap → S.freeHead = 0 → S.freeList = [] →
      (∀ x, S.nextFree x = 0) →
      st.regs 1 = eCap → st.regs 3 = heap → st.regs 4 = ordVRootBase heap →
      st.regs 5 = ordENodeBase heap vCap → st.regs 6 = ordNodesBase heap vCap eCap →
      st.regs 7 = mem ordPtr → st.regs 8 = ptr → st.regs 9 = S.nextNode → st.regs 10 = i →
      st.mem heap = vCap ∧ st.mem (heap + 1) = eCap ∧ st.mem (heap + 2) = ordVRootBase heap ∧
        st.mem (heap + 3) = ordENodeBase heap vCap ∧ st.mem (heap + 4) = ordNodesBase heap vCap eCap ∧
        st.mem (heap + 6) = 0 →
      (∀ u < vCap, st.mem (ordVRootBase heap + u) = S.vRoot u) →
      (∀ k < 2 * eCap, st.mem (ordENodeBase heap vCap + k) = S.eNode k) →
      OrdNodesAt st.mem (ordNodesBase heap vCap eCap) S.nextNode S.splay (fun _ => 0) →
      (∀ u, S.nextNode < u → u ≤ 2 * eCap → ∀ o < 8, st.mem (ordNodesBase heap vCap eCap + 8 * u + o) = 0) →
      ZeroFrom st.mem (heap + ordArenaSize vCap eCap) →
      (∀ a < heap, st.mem a = mem a) →
      ∃ st' c, ∃ S' : OrdStoreState,
        Runs w p ω ordInitOuterLoop st .normal st' c ∧
        st'.regs 1 = eCap ∧ st'.regs 3 = heap ∧ st'.regs 6 = ordNodesBase heap vCap eCap ∧ st'.regs 9 = S'.nextNode ∧
        OrdInv (readOrd mem ordPtr) S' ∧
        S'.vCap = vCap ∧ S'.eCap = eCap ∧ S'.freeHead = 0 ∧ S'.freeList = [] ∧
        (∀ x, S'.nextFree x = 0) ∧
        st'.mem heap = vCap ∧ st'.mem (heap + 1) = eCap ∧ st'.mem (heap + 2) = ordVRootBase heap ∧
          st'.mem (heap + 3) = ordENodeBase heap vCap ∧ st'.mem (heap + 4) = ordNodesBase heap vCap eCap ∧
          st'.mem (heap + 6) = 0 ∧
        (∀ u < vCap, st'.mem (ordVRootBase heap + u) = S'.vRoot u) ∧
        (∀ k < 2 * eCap, st'.mem (ordENodeBase heap vCap + k) = S'.eNode k) ∧
        OrdNodesAt st'.mem (ordNodesBase heap vCap eCap) S'.nextNode S'.splay (fun _ => 0) ∧
        ZeroFrom st'.mem (heap + ordArenaSize vCap eCap) ∧
        (∀ a < heap, st'.mem a = mem a) ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S +
            1600 * ordRecordsWords (readOrdRecords mem rem ptr) * ordStoreLog eCap + 15 := by
  have hlog : 1 ≤ ordStoreLog eCap := ordStoreLog_pos eCap
  have hw' : heap + (16 + vCap + 18 * eCap) < 2 ^ w := hw
  intro rem
  induction rem with
  | zero =>
    intro i ptr st S curOrd hi _ _ _ _ hcomb hinv hvS heS hfhS hflS hnfS
      r1 r3 r4 r5 r6 r7 r8 r9 r10 hhdr hvr hen hn hznd hzout hlt
    have hi_eq : i = mem ordPtr := by omega
    subst hi_eq
    have hcond : (Expr.bin .lt (.reg 10) (.reg 7)).eval w st = some 0 :=
      Expr.eval_lt_false (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r7) (by omega) (by omega)
    have hord_eq : curOrd = readOrd mem ordPtr := by
      funext u; have := hcomb u
      simp only [readOrdRecords, ordOfRecords_nil] at this
      by_cases h : curOrd u = [] <;> simpa [h] using this
    refine ⟨st, _, S, ord_runs_loop_false hcond, r1, r3, r6, r9, hord_eq ▸ hinv,
      hvS, heS, hfhS, hflS, hnfS, hhdr.1, hhdr.2.1, hhdr.2.2.1, hhdr.2.2.2.1, hhdr.2.2.2.2.1, hhdr.2.2.2.2.2,
      hvr, hen, hn, hzout, hlt, by simp [Expr.size_bin, Expr.size_reg, readOrdRecords, ordRecordsWords]; omega⟩
  | succ rem ih =>
    intro i ptr st S curOrd hi hnd_r hptr_w hnn_le hdisj_ord hcomb hinv hvS heS hfhS hflS hnfS
      r1 r3 r4 r5 r6 r7 r8 r9 r10 hhdr hvr hen hn hznd hzout hlt
    have hcond : (Expr.bin .lt (.reg 10) (.reg 7)).eval w st = some 1 :=
      Expr.eval_lt_true (Expr.eval_reg_of_eq r10) (Expr.eval_reg_of_eq r7) (by omega) (by omega)
    set v := mem ptr with hv_def
    set len := mem (ptr + 1) with hlen_def
    set xs := (readList mem (ptr + 2) len).map endOfKey with hxs_def
    set tlRecs := readOrdRecords mem rem (ptr + 2 + len) with htl_def
    have hrem_eq : readOrdRecords mem (rem + 1) ptr = (v, xs) :: tlRecs := rfl
    have hwords_rec : ordRecordsWords (readOrdRecords mem (rem + 1) ptr) = 2 + len + ordRecordsWords tlRecs := by
      rw [hrem_eq]; simp [ordRecordsWords, hxs_def, readList_length]
    have hptr_tl : ptr + 2 + len + ordRecordsWords tlRecs ≤ heap := by
      rw [hwords_rec] at hptr_w; omega
    have hlen_sum : ((readOrdRecords mem (rem + 1) ptr).map fun r => r.2.length).sum =
        len + (tlRecs.map fun r => r.2.length).sum := by
      rw [hrem_eq]; simp [hxs_def, readList_length]
    have hnn_tl : S.nextNode + len + (tlRecs.map fun r => r.2.length).sum ≤ 2 * eCap := by
      rw [hlen_sum] at hnn_le; omega
    have hnd_cons : v ∉ tlRecs.map Prod.fst ∧ (tlRecs.map Prod.fst).Nodup := by
      dsimp only at hnd_r; rw [hrem_eq, List.map_cons, List.nodup_cons] at hnd_r; exact hnd_r
    have hord_hd : ordOfRecords (readOrdRecords mem (rem + 1) ptr) v = xs := by
      rw [hrem_eq]; simp [ordOfRecords]
    have hord_tl_v : ordOfRecords tlRecs v = [] := by
      unfold ordOfRecords
      cases hf : tlRecs.find? (fun p => p.1 == v) with
      | none => rfl
      | some q =>
        exfalso
        have hq : q.1 = v := by simpa using List.find?_some hf
        exact hnd_cons.1 (hq ▸ List.mem_map.mpr ⟨q, List.mem_of_find?_eq_some hf, rfl⟩)
    have hord_ne : ∀ u, u ≠ v → ordOfRecords (readOrdRecords mem (rem + 1) ptr) u = ordOfRecords tlRecs u := fun u hu => by
      rw [hrem_eq]; simp [ordOfRecords, beq_eq_false_iff_ne.mpr (Ne.symm hu)]
    have ha11 : Runs w p ω (.assign 11 (.load (.reg 8))) st .normal
        { st with regs := Function.update st.regs 11 v } _ :=
      runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r8) (hlt ptr (by omega)), rfl, rfl, rfl⟩
    set stA : State := { st with regs := Function.update st.regs 11 v }
    have ha12 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 8) (.const 1)))) stA .normal
        { stA with regs := Function.update stA.regs 12 len } _ :=
      runs_assign_iff.mpr ⟨len, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := ptr) (by simp [stA, r8]))
        (Expr.eval_const (by omega)) (by omega)) (hlt (ptr + 1) (by omega)), rfl, rfl, rfl⟩
    set stB : State := { stA with regs := Function.update stA.regs 12 len }
    have ha8' : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.const 2))) stB .normal
        { stB with regs := Function.update stB.regs 8 (ptr + 2) } _ :=
      runs_assign_iff.mpr ⟨ptr + 2, Expr.eval_add (Expr.eval_reg_of_eq (v := ptr) (by simp [stB, stA, r8]))
        (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
    set stC : State := { stB with regs := Function.update stB.regs 8 (ptr + 2) }
    have hrec : ∃ stD cD, ∃ S1 : OrdStoreState, ∃ curOrd1 : ℕ → List End,
        Runs w p ω
          (.cond (.reg 12)
            (.assign 13 (.const 0) ;;
             .assign 14 (.const 0) ;;
             ordInitInnerLoop ;;
             .store (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 8) (.reg 13))) (.const 3))
               (.bin .add (.reg 11) (.const 1)) ;;
             .store (.bin .add (.reg 4) (.reg 11)) (.reg 13))
            .nop) stC .normal stD cD ∧
        stD.regs 1 = eCap ∧ stD.regs 3 = heap ∧ stD.regs 4 = ordVRootBase heap ∧
        stD.regs 5 = ordENodeBase heap vCap ∧ stD.regs 6 = ordNodesBase heap vCap eCap ∧
        stD.regs 7 = mem ordPtr ∧ stD.regs 8 = ptr + 2 ∧ stD.regs 9 = S1.nextNode ∧
        stD.regs 10 = i ∧ stD.regs 12 = len ∧
        S1.nextNode = S.nextNode + len ∧
        (∀ u, curOrd1 u = [] ∨ ordOfRecords tlRecs u = []) ∧
        (∀ u, (if curOrd1 u ≠ [] then curOrd1 u else ordOfRecords tlRecs u) = readOrd mem ordPtr u) ∧
        OrdInv curOrd1 S1 ∧ S1.vCap = vCap ∧ S1.eCap = eCap ∧ S1.freeHead = 0 ∧ S1.freeList = [] ∧
        (∀ x, S1.nextFree x = 0) ∧
        stD.mem heap = vCap ∧ stD.mem (heap + 1) = eCap ∧ stD.mem (heap + 2) = ordVRootBase heap ∧
          stD.mem (heap + 3) = ordENodeBase heap vCap ∧ stD.mem (heap + 4) = ordNodesBase heap vCap eCap ∧
          stD.mem (heap + 6) = 0 ∧
        (∀ u < vCap, stD.mem (ordVRootBase heap + u) = S1.vRoot u) ∧
        (∀ k < 2 * eCap, stD.mem (ordENodeBase heap vCap + k) = S1.eNode k) ∧
        OrdNodesAt stD.mem (ordNodesBase heap vCap eCap) S1.nextNode S1.splay (fun _ => 0) ∧
        (∀ u, S1.nextNode < u → u ≤ 2 * eCap → ∀ o < 8, stD.mem (ordNodesBase heap vCap eCap + 8 * u + o) = 0) ∧
        ZeroFrom stD.mem (heap + ordArenaSize vCap eCap) ∧
        (∀ a < heap, stD.mem a = mem a) ∧
        cD + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S1 ≤
          ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S + (1450 * len + 100) * ordStoreLog eCap := by
      by_cases hlen0 : len = 0
      · have hc : (Expr.reg 12).eval w stC = some 0 := Expr.eval_reg_of_eq (by simp [stC, stB, hlen0])
        have hxs_nil : xs = [] := by simp [hxs_def, hlen0, readList]
        refine ⟨stC, _, S, curOrd, ord_runs_cond_false hc (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩),
          by simp [stC, stB, stA, r1], by simp [stC, stB, stA, r3], by simp [stC, stB, stA, r4],
          by simp [stC, stB, stA, r5], by simp [stC, stB, stA, r6], by simp [stC, stB, stA, r7],
          by simp [stC], by simp [stC, stB, stA, r9], by simp [stC, stB, stA, r10],
          by simp [stC, stB], by omega,
          fun u => by
            by_cases huv : u = v
            · subst huv; exact Or.inr hord_tl_v
            · rw [← hord_ne u huv]; exact hdisj_ord u,
          fun u => by
            by_cases huv : u = v
            · subst huv; have := hcomb v; rw [hord_hd, hxs_nil] at this; rw [hord_tl_v]; exact this
            · rw [← hord_ne u huv]; exact hcomb u,
          hinv, hvS, heS, hfhS, hflS, hnfS,
          hhdr.1, hhdr.2.1, hhdr.2.2.1, hhdr.2.2.2.1, hhdr.2.2.2.2.1, hhdr.2.2.2.2.2,
          hvr, hen, hn, hznd, hzout, hlt, by
            have := Nat.le_mul_of_pos_right (1450 * len + 100) hlog
            simp [Expr.size_reg]; omega⟩
      · have hlen_pos : 0 < len := Nat.pos_of_ne_zero hlen0
        have hc : (Expr.reg 12).eval w stC = some len := Expr.eval_reg_of_eq (by simp [stC, stB])
        have hxs_ne : xs ≠ [] := by intro h; have := congrArg List.length h; simp [hxs_def, readList_length] at this; omega
        have hcur_v : curOrd v = [] := by
          rcases hdisj_ord v with h | h; exact h; exfalso; rw [hord_hd] at h; exact hxs_ne h
        have hread_v : readOrd mem ordPtr v = (readList mem (ptr + 2) len).map endOfKey := by
          have := hcomb v; simp only [hcur_v, ne_eq, not_true_eq_false, ↓reduceIte, hord_hd] at this; exact this.symm
        obtain ⟨stD, cD, S1, curOrd1, hrunD, d1, d3, d4, d5, d6, d7, d8, d9, d10, d12,
          hnn1, hdisj1, hcomb1, hinv1, hv1, he1, hfh1, hfl1, hnf1,
          dh0, dh1, dh2, dh3, dh4, dh6, dvr, den, dn, dznd, dzout, dlt, hphiD⟩ :=
          ordInitNonEmpty_runs (p := p) ω (stC := stC) (tlRecs := tlRecs) (i := i) huniq hw hlen_pos (by omega)
            (by omega) hcur_v hord_tl_v hread_v
            (fun u hu => by rw [← hord_ne u hu]; exact hdisj_ord u)
            (fun u hu => by rw [← hord_ne u hu]; exact hcomb u)
            (fun u hu => by have := hcomb u; simp only [hu, ne_eq, not_false_eq_true, ↓reduceIte] at this; exact this)
            hinv hvS heS hfhS hflS
            (by simp [stC, stB, stA, r1]) (by simp [stC, stB, stA, r3]) (by simp [stC, stB, stA, r4])
            (by simp [stC, stB, stA, r5]) (by simp [stC, stB, stA, r6]) (by simp [stC, stB, stA, r7])
            (by simp [stC]) (by simp [stC, stB, stA, r9]) (by simp [stC, stB, stA, r10])
            (by simp [stC, stB, stA]) (by simp [stC, stB])
            hhdr hvr hen hn hznd hzout hlt
        refine ⟨stD, _, S1, curOrd1, ord_runs_cond_true hc hlen0 hrunD,
          d1, d3, d4, d5, d6, d7, d8, d9, d10, d12, hnn1, hdisj1, hcomb1, hinv1, hv1, he1, hfh1, hfl1, hnf1,
          dh0, dh1, dh2, dh3, dh4, dh6, dvr, den, dn, dznd, dzout, dlt, ?_⟩
        have h20 : 20 ≤ 20 * ordStoreLog eCap := Nat.le_mul_of_pos_right 20 hlog
        have hrhs : (1450 * len + 100) * ordStoreLog eCap =
            (1450 * len + 80) * ordStoreLog eCap + 20 * ordStoreLog eCap := by ring
        simp only [Expr.size_reg] at *
        omega
    obtain ⟨stD, cD, S1, curOrd1, hrunD, d1, d3, d4, d5, d6, d7, d8, d9, d10, d12,
      hnn1, hdisj1, hcomb1, hinv1, hv1, he1, hfh1, hfl1, hnf1,
      dh0, dh1, dh2, dh3, dh4, dh6, dvr, den, dn, dznd, dzout, dlt, hphiD⟩ := hrec
    have ha8'' : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.reg 12))) stD .normal
        { stD with regs := Function.update stD.regs 8 (ptr + 2 + len) } _ :=
      runs_assign_iff.mpr ⟨ptr + 2 + len, Expr.eval_add (Expr.eval_reg_of_eq d8) (Expr.eval_reg_of_eq d12) (by omega), rfl, rfl, rfl⟩
    set stE : State := { stD with regs := Function.update stD.regs 8 (ptr + 2 + len) }
    have ha10' : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) stE .normal
        { stE with regs := Function.update stE.regs 10 (i + 1) } _ :=
      runs_assign_iff.mpr ⟨i + 1, Expr.eval_add (Expr.eval_reg_of_eq (v := i) (by simp [stE, d10]))
        (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
    set stF0 : State := { stE with regs := Function.update stE.regs 10 (i + 1) }
    obtain ⟨stF, cF, SF, hrunF, f1, f3, f6, f9, hinvF, hvF, heF, hfhF, hflF, hnfF,
      fh0, fh1, fh2, fh3, fh4, fh6, fvr, fen, fn, fzout, flt, hphiF⟩ :=
      ih (i + 1) (ptr + 2 + len) stF0 S1 curOrd1 (by omega) hnd_cons.2 hptr_tl (by rw [← htl_def]; omega)
        hdisj1 hcomb1 hinv1 hv1 he1 hfh1 hfl1 hnf1
        (by simp [stF0, stE, d1]) (by simp [stF0, stE, d3]) (by simp [stF0, stE, d4])
        (by simp [stF0, stE, d5]) (by simp [stF0, stE, d6]) (by simp [stF0, stE, d7])
        (by simp [stF0, stE]) (by simp [stF0, stE, d9]) (by simp [stF0])
        ⟨dh0, dh1, dh2, dh3, dh4, dh6⟩ dvr den dn dznd dzout dlt
    refine ⟨stF, _, SF,
      ord_runs_loop_true hcond Nat.one_ne_zero
        (ord_runs_seq_normal ha11 (ord_runs_seq_normal ha12 (ord_runs_seq_normal ha8'
          (ord_runs_seq_normal hrunD (ord_runs_seq_normal ha8'' ha10'))))) hrunF,
      f1, f3, f6, f9, hinvF, hvF, heF, hfhF, hflF, hnfF,
      fh0, fh1, fh2, fh3, fh4, fh6, fvr, fen, fn, fzout, flt, ?_⟩
    rw [← htl_def] at hphiF
    have h1600 : 1600 * ordRecordsWords (readOrdRecords mem (rem + 1) ptr) * ordStoreLog eCap =
        1600 * (2 + len) * ordStoreLog eCap + 1600 * ordRecordsWords tlRecs * ordStoreLog eCap := by
      rw [hwords_rec]; ring
    have hrec_le : (1450 * len + 100) * ordStoreLog eCap + 50 ≤ 1600 * (2 + len) * ordStoreLog eCap := by
      have h1 : (1450 * len + 100) * ordStoreLog eCap + 50 * ordStoreLog eCap ≤
          1600 * (2 + len) * ordStoreLog eCap := by
        have : 1600 * (2 + len) * ordStoreLog eCap = (1600 * len + 3200) * ordStoreLog eCap := by ring
        have h2 : (1450 * len + 150) * ordStoreLog eCap ≤ (1600 * len + 3200) * ordStoreLog eCap :=
          Nat.mul_le_mul_right _ (by omega)
        linarith
      have h50 : 50 ≤ 50 * ordStoreLog eCap := Nat.le_mul_of_pos_right 50 hlog
      omega
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    omega

/-! ### Main `ordStoreInitBody` verification -/

theorem ordStoreInitBody_runs
    {w vCap eCap ordPtr heap words pos : ℕ} {p : Program} (ω : ℕ → Bool) {mem : ℕ → ℕ}
    (hord : OrdListAt mem ordPtr (readOrd mem ordPtr) words)
    (hord_le : ordPtr + words ≤ heap)
    (huniq : OrdUniqueWithin vCap eCap (readOrd mem ordPtr))
    (hz : ZeroFrom mem heap) (hw : heap + ordArenaSize vCap eCap < 2 ^ w) :
    ∃ o st' c, Runs w p ω ordStoreInitBody (startState [vCap, eCap, ordPtr, heap] mem pos) o st' c ∧
      o.value = heap + ordArenaSize vCap eCap ∧
      (∃ S' : OrdStoreState,
        OrdInv (readOrd mem ordPtr) S' ∧
        OrdArenaAt heap S' st'.mem ∧
        S'.vCap = vCap ∧ S'.eCap = eCap ∧
        ZeroFrom st'.mem (heap + ordArenaSize vCap eCap) ∧
        (∀ a < heap, st'.mem a = mem a) ∧
        c + ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S' ≤
          ORD_INIT_MUL * (1 + ordRecordsWords (readOrdRecordsAt mem ordPtr)) * ordStoreLog eCap) := by
  have hlog : 1 ≤ ordStoreLog eCap := ordStoreLog_pos eCap
  have hw' : heap + (16 + vCap + 18 * eCap) < 2 ^ w := hw
  set nb := ordNodesBase heap vCap eCap with hnb_def
  set recs := readOrdRecordsAt mem ordPtr with hrecs_def
  have hnb_eq : nb = heap + 8 + vCap + 2 * eCap := by rw [hnb_def]; unfold ordNodesBase; omega
  have hnb_exact : nb + 8 * (2 * eCap + 1) = heap + ordArenaSize vCap eCap := by
    rw [hnb_def]; unfold ordNodesBase ordArenaSize; omega
  have hwords_eq : words = 1 + ordRecordsWords recs := hord.2.2
  have hsum_le : (recs.map fun r => r.2.length).sum ≤ 2 * eCap :=
    ordRecords_sum_len_le hord.1 huniq
  obtain ⟨stH, cH, hrunH, hr1, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10,
    hh0, hh1, hh2, hh3, hh4, hge5, hltH, hcH⟩ :=
    ordInitHeader_runs (p := p) ω hord hord_le hz hw (pos := pos)
  set S0 : OrdStoreState :=
    { vCap := vCap, eCap := eCap, nextNode := 0, freeHead := 0,
      vRoot := fun _ => 0, eNode := fun _ => 0,
      splay := ⟨fun _ => ordNullNode⟩, nextFree := fun _ => 0,
      trees := fun _ => .leaf, freeList := [] }
  have hinv0 : OrdInv (fun _ => []) S0 :=
    { ord_unique := ⟨⟨fun _ => List.nodup_nil, fun _ _ => rfl, fun _ _ h => absurd h List.not_mem_nil⟩,
        fun _ _ _ h => absurd h List.not_mem_nil⟩
      next_le := Nat.zero_le _
      clean := fun _ => rfl
      null_node := rfl
      tree_inv := fun _ _ => ⟨List.nodup_nil, trivial⟩
      tree_out := fun _ _ => rfl
      vRoot_eq := fun _ _ => rfl
      root_ppar := fun _ _ h => absurd rfl h
      list_eq := fun _ _ => rfl
      disj_trees := fun _ _ _ _ h => absurd h List.not_mem_nil
      free_nodup := List.nodup_nil
      free_disj := fun _ _ _ h => absurd h List.not_mem_nil
      free_chain := rfl
      nodes_range := fun x => by simp [S0, AuxTree.toList]; omega
      key_lt := fun _ _ _ h => absurd h List.not_mem_nil
      eNode_spec := fun _ _ => Or.inl ⟨rfl, fun _ _ _ h => absurd h List.not_mem_nil⟩ }
  have hptr_init : ordPtr + 1 + ordRecordsWords (readOrdRecords mem (mem ordPtr) (ordPtr + 1)) ≤ heap := by
    rw [hrecs_def, readOrdRecordsAt] at hwords_eq; omega
  have hsum_init : S0.nextNode + ((readOrdRecords mem (mem ordPtr) (ordPtr + 1)).map fun r => r.2.length).sum ≤ 2 * eCap := by
    rw [hrecs_def, readOrdRecordsAt] at hsum_le; simpa [S0] using hsum_le
  have hcnt_w : mem ordPtr < 2 ^ w := by
    have h1 := ordRecordsWords_ge_two_mul recs
    have h2 : recs.length = mem ordPtr := readOrdRecords_length mem (mem ordPtr) (ordPtr + 1)
    omega
  obtain ⟨stO, cO, SF, hrunO, f1, f3, f6, f9, hinvF, hvF, heF, hfhF, hflF, hnfF,
    fh0, fh1, fh2, fh3, fh4, fh6, fvr, fen, fn, fzout, flt, hphiO⟩ :=
    ordInitOuterLoop_runs (p := p) ω huniq hcnt_w hw (mem ordPtr) 0 (ordPtr + 1) stH S0 (fun _ => [])
      (by omega) hord.1 hptr_init hsum_init
      (fun _ => Or.inl rfl) (fun _ => by simp [readOrd, readOrdRecordsAt])
      hinv0 rfl rfl rfl rfl (fun _ => rfl)
      hr1 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr10
      ⟨hh0, hh1, hh2, hh3, hh4, hge5 (heap + 6) (by omega)⟩
      (fun u _ => hge5 (ordVRootBase heap + u) (by unfold ordVRootBase; omega))
      (fun k _ => hge5 (ordENodeBase heap vCap + k) (by unfold ordENodeBase; omega))
      (fun u hu => by
        have hu0 : u = 0 := by dsimp only [S0] at hu; omega
        subst hu0; dsimp only [S0, ordNullNode, ordNodeAddr]
        exact ⟨hge5 (nb + 8 * 0) (by omega), hge5 (nb + 8 * 0 + 1) (by omega),
          hge5 (nb + 8 * 0 + 2) (by omega), hge5 (nb + 8 * 0 + 3) (by omega),
          hge5 (nb + 8 * 0 + 4) (by omega), hge5 (nb + 8 * 0 + 5) (by omega),
          hge5 (nb + 8 * 0 + 6) (by omega), hge5 (nb + 8 * 0 + 7) (by omega)⟩)
      (fun u _ _ o _ => hge5 (nb + 8 * u + o) (by omega))
      (fun a ha => hge5 a (by unfold ordArenaSize at ha; omega))
      hltH
  have hs5 : Runs w p ω (.store (.bin .add (.reg 3) (.const 5)) (.reg 9)) stO .normal
      { stO with mem := Function.update stO.mem (heap + 5) SF.nextNode } _ :=
    runs_store_iff.mpr ⟨heap + 5, SF.nextNode, Expr.eval_add (Expr.eval_reg_of_eq f3) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq f9, rfl, rfl, rfl⟩
  set stO1 : State := { stO with mem := Function.update stO.mem (heap + 5) SF.nextNode }
  have ha17 : Runs w p ω
      (.assign 17 (.bin .add (.reg 6) (.bin .mul (.const 8) (.bin .add (.bin .add (.reg 1) (.reg 1)) (.const 1))))) stO1 .normal
      { stO1 with regs := Function.update stO1.regs 17 (heap + ordArenaSize vCap eCap) } _ :=
    runs_assign_iff.mpr ⟨heap + ordArenaSize vCap eCap, by
      have he : (Expr.bin .add (.reg 6) (.bin .mul (.const 8) (.bin .add (.bin .add (.reg 1) (.reg 1)) (.const 1)))).eval w stO1 =
          some (nb + 8 * (eCap + eCap + 1)) :=
        Expr.eval_add (Expr.eval_reg_of_eq (v := nb) (by dsimp only [stO1]; rw [hnb_def]; exact f6))
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only [stO1]; exact f1))
              (Expr.eval_reg_of_eq (by dsimp only [stO1]; exact f1)) (by omega))
              (Expr.eval_const (by omega)) (by omega)) (by omega))
          (by omega)
      rwa [show nb + 8 * (eCap + eCap + 1) = heap + ordArenaSize vCap eCap by omega] at he, rfl, rfl, rfl⟩
  set stO2 : State := { stO1 with regs := Function.update stO1.regs 17 (heap + ordArenaSize vCap eCap) }
  have hret : Runs w p ω (.ret (.reg 17)) stO2 (.returned (heap + ordArenaSize vCap eCap)) stO2 _ :=
    runs_ret_iff.mpr ⟨heap + ordArenaSize vCap eCap, Expr.eval_reg_of_eq (by simp [stO2]), rfl, rfl, rfl⟩
  have hfull := ord_runs_seq_normal hrunH (ord_runs_seq_normal hrunO
    (ord_runs_seq_normal hs5 (ord_runs_seq_normal ha17 hret)))
  have harenaF : OrdArenaAt heap SF stO2.mem :=
    { hdr_vCap := by dsimp only [stO2, stO1]; rw [Function.update_of_ne (by omega), Nat.add_zero, fh0, hvF]
      hdr_eCap := by dsimp only [stO2, stO1]; rw [Function.update_of_ne (by omega), fh1, heF]
      hdr_vRoot := by dsimp only [stO2, stO1]; rw [Function.update_of_ne (by omega), fh2]
      hdr_eNode := by dsimp only [stO2, stO1]; rw [Function.update_of_ne (by omega), fh3, hvF]
      hdr_nodes := by dsimp only [stO2, stO1]; rw [Function.update_of_ne (by omega), fh4, hvF, heF]
      hdr_next := by dsimp only [stO2, stO1]; exact Function.update_self _ _ _
      hdr_free := by dsimp only [stO2, stO1]; rw [Function.update_of_ne (by omega), fh6, hfhF]
      vRoot_at := fun u hu => by
        dsimp only [stO2, stO1]; rw [Function.update_of_ne (by unfold ordVRootBase; omega)]
        exact fvr u (by omega)
      eNode_at := fun k hk => by
        dsimp only [stO2, stO1]; rw [hvF, Function.update_of_ne (by unfold ordENodeBase; omega)]
        exact fen k (by omega)
      nodes_at := by
        rw [hvF, heF]
        have hnf_eq : SF.nextFree = fun _ => 0 := funext hnfF
        rw [hnf_eq]
        exact OrdNodesAt.congr fn fun a ha => by
          dsimp only [stO2, stO1]; rw [Function.update_of_ne (by unfold InOrdNodes at ha; rw [← hnb_def] at ha; omega)] }
  have hphiS0 : ordPhi ORD_PHI_WEIGHT ORD_DEL_WEIGHT S0 = 0 := by
    simp [ordPhi, sumTreePhi, sumCountNodes, S0, AuxTree.treePhi, AuxTree.countNodes]
  refine ⟨.returned (heap + ordArenaSize vCap eCap), stO2, _, hfull, rfl, SF, hinvF, harenaF, hvF, heF,
    fun a ha => by dsimp only [stO2, stO1]; rw [Function.update_of_ne (by unfold ordArenaSize at ha; omega)]; exact fzout a ha,
    fun a ha => by dsimp only [stO2, stO1]; rw [Function.update_of_ne (by omega)]; exact flt a ha, ?_⟩
  rw [hphiS0, show readOrdRecords mem (mem ordPtr) (ordPtr + 1) = recs from rfl] at hphiO
  have hmul : ORD_INIT_MUL * (1 + ordRecordsWords recs) * ordStoreLog eCap =
      2000 * ordRecordsWords recs * ordStoreLog eCap + 2000 * ordStoreLog eCap := by
    unfold ORD_INIT_MUL; ring
  have h200 : 200 ≤ 2000 * ordStoreLog eCap := by
    have := Nat.le_mul_of_pos_right 2000 hlog; omega
  have h1600_le : 1600 * ordRecordsWords recs * ordStoreLog eCap ≤
      2000 * ordRecordsWords recs * ordStoreLog eCap :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const] at *
  omega

end MinCostFlow.SparseCore.Program
