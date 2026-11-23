module

public import MinCostFlow.SparseCore.Program.TourSplayOps
import Mathlib.Tactic

/-!
# Query, insert-before, and value-update WordRAM splay procedures

Builds and verifies on top of `TourSplayOps`:
- `tourInsertBeforeBody_runs`: splice singleton `x` immediately before `y` (`O(log cap)`);
- `tourFindFirstBody_runs`: find leftmost ready node in a tree and splay it to root (`O(log cap)`);
- `tourSetValNodeBody_runs`: splay `x` and update its `TourVal` (`O(log cap)`);
- `tourRootTagOfBody_runs`: splay `x` and return the component's `rootTag` summary (`O(log cap)`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Amortized constants and WordRAM bodies -/

/-- Amortized per-`log` cost constant for `tourFindFirstBody`, `tourSetValNodeBody`, and `tourRootTagOfBody`. -/
def TOUR_FIND_AMORT : ℕ := 90000

/-- Amortized per-`log` cost constant for `tourNextReadyBody`. -/
def TOUR_NEXT_AMORT : ℕ := 300000

/-- Amortized per-`(out + 1) * log` cost constant for `tourListReadyBody`. -/
def TOUR_LIST_AMORT : ℕ := 250000

/-- `tourFindFirst [nb, r, fuel, heap]`: find leftmost ready node in `r`'s tree and splay it to root,
or return `0` if `r = 0` or no ready node exists. -/
def tourFindFirstBody (descProc sumTestProc splayProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 4 (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))) ;;
     .call 5 sumTestProc [.reg 4] ;;
     .cond (.bin .eq (.reg 5) (.const 0)) (.ret (.const 0))
       (.call 6 descProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
        .call 7 splayProc [.reg 0, .reg 6, .reg 2, .reg 3] ;;
        .ret (.reg 6)))

/-- `tourNextReady [nb, x, fuel, heap]`: return the first ready node cyclically after `x` (wrapping
to `x` if `x` is the only ready node, or `0` if none), restoring the exact tree sequence. -/
def tourNextReadyBody (splayProc detachLeftProc detachRightProc joinProc findFirstProc
    sumTestProc valTestProc : ℕ) : Stmt :=
  .call 4 splayProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .assign 4 (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))) ;;
  .assign 5 (.load (.bin .add (.reg 4) (.const 1))) ;;
  .cond (.reg 5)
    (.call 6 sumTestProc [.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 5))] ;;
     .cond (.reg 6)
       (.call 7 detachRightProc [.reg 0, .reg 1, .reg 3] ;;
        .call 8 findFirstProc [.reg 0, .reg 7, .reg 2, .reg 3] ;;
        .call 9 joinProc [.reg 0, .reg 1, .reg 8, .reg 2, .reg 3] ;;
        .ret (.reg 8))
       .nop)
    .nop ;;
  .assign 5 (.load (.reg 4)) ;;
  .cond (.reg 5)
    (.call 6 sumTestProc [.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 5))] ;;
     .cond (.reg 6)
       (.call 7 detachLeftProc [.reg 0, .reg 1, .reg 3] ;;
        .call 8 findFirstProc [.reg 0, .reg 7, .reg 2, .reg 3] ;;
        .call 9 joinProc [.reg 0, .reg 8, .reg 1, .reg 2, .reg 3] ;;
        .ret (.reg 8))
       .nop)
    .nop ;;
  .call 6 valTestProc [.bin .add (.reg 4) (.const 6)] ;;
  .cond (.reg 6) (.ret (.reg 1)) (.ret (.const 0))

/-- `tourListReady [nb, r, fuel, keyBase, outPtr, splayHeap]`: write length and `keyBase[y]` for all
ready nodes `y` in `r`'s tree at `outPtr`, restoring the exact tree sequence and returning its root. -/
def tourListReadyBody (findFirstProc detachRightProc joinProc : ℕ) : Stmt :=
  .assign 6 (.const 0) ;;
  .assign 7 (.const 0) ;;
  .assign 8 (.reg 1) ;;
  .call 9 findFirstProc [.reg 0, .reg 8, .reg 2, .reg 5] ;;
  .loop (.reg 9)
    (.store (.bin .add (.bin .add (.reg 4) (.const 1)) (.reg 6))
        (.load (.bin .add (.reg 3) (.reg 9))) ;;
     .assign 6 (.bin .add (.reg 6) (.const 1)) ;;
     .call 10 detachRightProc [.reg 0, .reg 9, .reg 5] ;;
     .call 7 joinProc [.reg 0, .reg 7, .reg 9, .reg 2, .reg 5] ;;
     .assign 8 (.reg 10) ;;
     .call 9 findFirstProc [.reg 0, .reg 8, .reg 2, .reg 5]) ;;
  .call 10 joinProc [.reg 0, .reg 7, .reg 8, .reg 2, .reg 5] ;;
  .store (.reg 4) (.reg 6) ;;
  .ret (.reg 10)

/-- `tourSetValNode [nb, x, isOpen, isMarked, rootTag, fuel, heap]`: splay `x` and set its `TourVal`. -/
def tourSetValNodeBody (splayProc setValProc : ℕ) : Stmt :=
  .call 7 splayProc [.reg 0, .reg 1, .reg 5, .reg 6] ;;
  .call 7 setValProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 6] ;;
  .ret (.const 0)

/-- `tourRootTagOf [nb, x, fuel, heap]`: splay `x` and return the `rootTag` summary of `x`'s tree. -/
def tourRootTagOfBody (splayProc : ℕ) : Stmt :=
  .call 4 splayProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .ret (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))) (.const 15)))

theorem tourSplayQuery_bodies_noRand (dP sT vT sP dL dR jP fP svP : ℕ) :
    (tourFindFirstBody dP sT sP).NoRand ∧
    (tourNextReadyBody sP dL dR jP fP sT vT).NoRand ∧
    (tourListReadyBody fP dR jP).NoRand ∧
    (tourSetValNodeBody sP svP).NoRand ∧
    (tourRootTagOfBody sP).NoRand := by
  simp [tourFindFirstBody, tourNextReadyBody, tourListReadyBody, tourSetValNodeBody,
    tourRootTagOfBody, Stmt.NoRand]

/-- Full splay procedure bundle (core + sequence + query/update) installed in `p`. -/
structure TourSplayQueryProcs (w : ℕ) (p : Program) extends TourSplayOpsProcs w p where
  findFirstOpen : ℕ
  findFirstOpen_body : p.procs[findFirstOpen]? =
    some (tourFindFirstBody openDescProc openTests.sumTest splay.splay)
  findFirstMark : ℕ
  findFirstMark_body : p.procs[findFirstMark]? =
    some (tourFindFirstBody markDescProc markTests.sumTest splay.splay)
  nextOpen : ℕ
  nextOpen_body : p.procs[nextOpen]? =
    some (tourNextReadyBody splay.splay detachLeft detachRight join findFirstOpen
      openTests.sumTest openTests.valTest)
  nextMark : ℕ
  nextMark_body : p.procs[nextMark]? =
    some (tourNextReadyBody splay.splay detachLeft detachRight join findFirstMark
      markTests.sumTest markTests.valTest)
  listOpen : ℕ
  listOpen_body : p.procs[listOpen]? = some (tourListReadyBody findFirstOpen detachRight join)
  listMark : ℕ
  listMark_body : p.procs[listMark]? = some (tourListReadyBody findFirstMark detachRight join)
  setValNode : ℕ
  setValNode_body : p.procs[setValNode]? = some (tourSetValNodeBody splay.splay setVal)
  rootTagOf : ℕ
  rootTagOf_body : p.procs[rootTagOf]? = some (tourRootTagOfBody splay.splay)

/-! ## Helper lemmas -/

theorem list_find?_congr {α : Type*} {xs : List α} {p q : α → Bool}
    (h : ∀ x ∈ xs, p x = q x) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.find?_cons, h a (by simp)]
    cases q a
    · exact ih fun x hx => h x (by simp [hx])
    · rfl

theorem rs_iff_exists_rv {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} {t : AuxTree}
    {rs : TourSum → Bool} {rv : TourVal → Bool}
    (hR : ReadyLaw tourPayload rs rv)
    (hf : TourForestInv cap st trees) (ht : t ∈ trees) :
    rs (st.nodes t.rootId).sum = true ↔ ∃ u ∈ t.toList, rv (st.nodes u).val = true := by
  rw [hf.sum_eq ht, hR]
  simp only [List.mem_map, exists_exists_and_eq_and]

private theorem find?_eq_none_of_rs_false {cap : ℕ} {st : SplayState TourVal TourSum Unit}
    {trees : List AuxTree} {t : AuxTree}
    {rs : TourSum → Bool} {rv : TourVal → Bool}
    (hR : ReadyLaw tourPayload rs rv)
    (hf : TourForestInv cap st trees) (ht : t ∈ trees)
    (hfalse : rs (st.nodes t.rootId).sum = false) :
    t.toList.find? (fun u => rv (st.nodes u).val) = none := by
  rw [List.find?_eq_none]
  intro u hu hrv
  have htrue := (rs_iff_exists_rv hR hf ht).mpr ⟨u, hu, hrv⟩
  rw [hfalse] at htrue; exact Bool.false_ne_true htrue

private theorem eval_eq_zero_of_ne' {w r v : ℕ} {st : State} (hr : st.regs r = v)
    (hne : v ≠ 0) (hw : 1 < 2 ^ w) :
    (Expr.bin .eq (.reg r) (.const 0)).eval w st = some 0 := by
  simp [Expr.eval, hr, BinOp.eval, hne, Nat.pos_of_ne_zero (by omega : 2 ^ w ≠ 0)]

private theorem heapOk_of_frame' {nb cap heap sp : ℕ} {w : ℕ} {mem M : ℕ → ℕ}
    (hheap : HeapOk tourLayout w nb cap heap sp mem)
    (hfr : TreeFrame tourLayout nb cap heap mem M) :
    HeapOk tourLayout w nb cap heap sp M :=
  ⟨hheap.rec_le, hheap.room, hfr.1, hheap.wide⟩

private theorem heapOk_zero' {nb cap heap sp : ℕ} {w : ℕ} {mem : ℕ → ℕ}
    (hheap : HeapOk tourLayout w nb cap heap sp mem) :
    HeapOk tourLayout w nb cap heap 0 mem :=
  ⟨hheap.rec_le, by have := hheap.room; omega, hheap.zero, hheap.wide⟩

/-! ## Amortized run theorem for `tourInsertBeforeBody` -/

/-- Amortized run theorem for `tourInsertBeforeBody`: inserts singleton `AuxTree.node x .leaf .leaf`
immediately before `y` in `t`, yielding `t'` with `t'.rootId = y` and `t'.toList = P ++ x :: y :: Q`
(where `t.toList = P ++ y :: Q`). -/
theorem tourInsertBeforeBody_runs {w nb cap heap fuel x y pos : ℕ} {p : Program}
    (C : TourSplayOpsProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t : AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (AuxTree.node x .leaf .leaf :: t :: rest)) (hvals : TourValsOk w cap st)
    (hy : y ∈ t.toList) (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ t' s' o st' c P Q,
      Runs w p ω (tourInsertBeforeBody C.splay.splay C.detachLeft C.attachLeft)
        (startState [nb, x, y, fuel, heap] mem pos) o st' c ∧
      o.value = y ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (t' :: rest) ∧
      TourValsOk w cap s' ∧
      t' ≠ .leaf ∧ t'.rootId = y ∧
      t.toList = P ++ y :: Q ∧
      t'.toList = P ++ x :: y :: Q ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u, u ≠ x → u ∉ t.toList → s'.nodes u = st.nodes u) ∧
      c + TOUR_PHI_MULT * forestPhi (t' :: rest) ≤
        TOUR_PHI_MULT * forestPhi (AuxTree.node x .leaf .leaf :: t :: rest) +
          TOUR_SEQ_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have ht_mem : t ∈ AuxTree.node x .leaf .leaf :: t :: rest := by simp
  have hdep : t.depthOf y < fuel :=
    lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hy) (le_of_lt (lt_of_le_of_lt (hf.countNodes_le ht_mem) hfuel))
  have hf0 : TourForestInv cap st ([AuxTree.node x .leaf .leaf] ++ t :: rest) := hf
  obtain ⟨t₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, hout₁, hcost₁⟩ :=
    tourSplay_runs_amort (pos := pos) C.toTourSplayCoreProcs ω hnodes hf0 hvals hy hdep hfuelW hheap
  set s₁ := SplayState.splay tourPayload st fuel y
  cases ht₁c : t₁ with
  | leaf => exact absurd ht₁c hne₁
  | node yid L R =>
    have hyid : yid = y := by simpa [ht₁c, AuxTree.rootId] using hroot₁
    rcases hyid with rfl
    rw [ht₁c] at hinv₁ hlist₁ hcost₁
    have hy_cap : yid ≤ cap := (hinv₁.mem_inCap (t := AuxTree.node yid L R) (by simp) (by simp [AuxTree.toList])).2
    have hx_cap : x ≤ cap := (hinv₁.mem_inCap (t := AuxTree.node x .leaf .leaf) (by simp) (by simp [AuxTree.toList])).2
    have hsub₁ := (hinv₁.treesInv (AuxTree.node yid L R) (by simp)).sub
    obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hv₂, hn₂, hfr₂⟩, hc₂⟩ := tourDetachLeftBody_runs (pos := st₁.pos)
      C.toTourSplayCoreProcs ω hn₁ hinv₁.ptrOk hy_cap (heapOk_zero' (heapOk_of_frame' hheap hfr₁))
      (tourDetachLeft_sumOk hinv₁ hvals₁)
    obtain ⟨hinv₂, hout₂, hval₂, hphi₂⟩ := tourDetachLeft_preserves hinv₁
    set s₂ := tourDetachLeft s₁ yid
    have hvals₂ : TourValsOk w cap s₂ := ⟨hvals₁.1, fun u hu => by rw [hval₂ u hu]; exact hvals₁.2 u hu⟩
    have hv₂_eq : o₂.value = L.rootId := by simp only [hv₂, hsub₁.1, ↓reduceIte, hsub₁.2.1]
    cases hLc : L with
    | leaf =>
      have hL0 : o₂.value = 0 := by simpa [hLc, AuxTree.rootId] using hv₂_eq
      have hinv₂' : TourForestInv cap s₂ (AuxTree.node x .leaf .leaf :: AuxTree.node yid .leaf R :: rest) := by
        simpa [hLc] using hinv₂
      have hx_sub := (hinv₂'.treesInv (AuxTree.node x .leaf .leaf) (by simp)).sub
      have hx_rev := hinv₂'.noRev x hx_cap
      have hs₃_eq : tourAttachLeft s₂ x 0 = s₂ := by
        have hx_l0 : (s₂.nodes x).left = 0 := hx_sub.2.1
        have hx_r0 : (s₂.nodes x).right = 0 := hx_sub.2.2.1
        have hx_sz : (s₂.nodes x).sz = 1 := hx_sub.2.2.2.2.2.1
        have hx_sum : (s₂.nodes x).sum = tourPayload.single x (s₂.nodes x).val := by
          have hseq := hinv₂'.sum_eq (t := AuxTree.node x .leaf .leaf) (by simp)
          simpa [AuxTree.rootId, AuxTree.toList, LctPayload.listSummary, tourPayload] using hseq
        have hnd : (tourAttachLeft s₂ x 0).nodes = s₂.nodes := by
          funext u
          by_cases hux : u = x
          · subst hux
            simp only [tourAttachLeft, hx_sub.1, ↓reduceIte, pull, updateNode, setLeft]
            rw [hx_r0]; simp only [↓reduceIte, Nat.add_zero]
            cases hndu : s₂.nodes u with
            | mk l r p pp sz val sum tag rev =>
              rw [hndu] at hx_l0 hx_r0 hx_sz hx_sum
              simp only [SplayNode.mk.injEq, and_true, true_and]
              exact ⟨hx_l0.symm, hx_r0.symm, hx_sz.symm, by simpa [tourPayload] using hx_sum.symm⟩
          · simp [tourAttachLeft, hx_sub.1, pull, updateNode, setLeft, hux]
        cases hs3 : tourAttachLeft s₂ x 0
        cases hs2 : s₂
        rw [hs3, hs2] at hnd
        exact congrArg SplayState.mk hnd
      have hx_sumOk : x ≠ 0 → (tourOk w).sumOk (pullSum tourPayload
          (if (0 : ℕ) = 0 then s₂.setLeft x 0 else ((s₂.setLeft x 0).setPar 0 x).setPpar 0 0) x) := by
        intro hx0
        have heq : ((tourAttachLeft s₂ x 0).nodes x).sum = pullSum tourPayload (s₂.setLeft x 0) x := by
          simp only [tourAttachLeft, hx0, ↓reduceIte, pull, updateNode]; rfl
        simp only [↓reduceIte, ← heq, hs₃_eq]
        have hsb := hinv₂'.sum_bounds hvals₂ (by simp : AuxTree.node x .leaf .leaf ∈ _) x (by simp [AuxTree.toList])
        have hcnt := hinv₂'.countNodes_le (by simp : AuxTree.node x .leaf .leaf ∈ _)
        exact ⟨by have := hvals₂.1; omega, by have := hvals₂.1; omega, by have := hvals₂.1; omega, hsb.2.2.2⟩
      obtain ⟨o₃, st₃, c₃, hrun₃, ⟨hn₃, hfr₃⟩, hc₃⟩ := tourAttachLeftBody_runs (pos := st₂.pos)
        C.toTourSplayCoreProcs ω hn₂ hinv₂'.ptrOk hx_cap (Nat.zero_le _)
        (heapOk_zero' (heapOk_of_frame' hheap (hfr₁.trans hfr₂))) hx_sumOk
      rw [hs₃_eq] at hn₃
      obtain ⟨o₄, st₄, c₄, hrun₄, ⟨hn₄, hfr₄⟩, hc₄⟩ := tourAttachLeftBody_runs (pos := st₃.pos)
        C.toTourSplayCoreProcs ω hn₃ hinv₂'.ptrOk hy_cap hx_cap
        (heapOk_zero' (heapOk_of_frame' hheap (hfr₁.trans (hfr₂.trans hfr₃))))
        (tourAttachLeft_sumOk hinv₂' hvals₂)
      obtain ⟨hinv₄, hout₄, hval₄, hphi₄⟩ := tourAttachLeft_preserves hinv₂'
      obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf0 hy hdep
      have hval_all : ∀ u ≤ cap, ((tourAttachLeft s₂ yid x).nodes u).val = (st.nodes u).val := by
        intro u hu; exact (hval₄ u hu).trans ((hval₂ u hu).trans (hval_sp u hu))
      have hvals₄ : TourValsOk w cap (tourAttachLeft s₂ yid x) :=
        ⟨hvals.1, fun u hu => by rw [hval_all u hu]; exact hvals.2 u hu⟩
      have hbody_run : ∃ st_fin c_fin, st_fin.mem = st₄.mem ∧ c_fin ≤ c₁ + c₂ + c₃ + c₄ + 35 ∧
          Runs w p ω (tourInsertBeforeBody C.splay.splay C.detachLeft C.attachLeft)
            (startState [nb, x, yid, fuel, heap] mem pos) (.returned yid) st_fin c_fin := by
        unfold tourInsertBeforeBody; rw [startState]
        set s0 : State := ⟨mem, fun i => [nb, x, yid, fuel, heap].getD i 0, pos⟩
        set s1_st : State := { st₁ with regs := Function.update s0.regs 5 o₁.value }
        set s2_st : State := { st₂ with regs := Function.update s1_st.regs 5 o₂.value }
        set s3_st : State := { st₃ with regs := Function.update s2_st.regs 6 o₃.value }
        set s4_st : State := { st₄ with regs := Function.update s3_st.regs 6 o₄.value }
        have hc1 := runs_call_regs4 5 0 2 3 4 (st := s0) C.splay.splay_body (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) hrun₁
        have hc2 := runs_call_regs3 5 0 2 4 (st := s1_st) C.detachLeft_body (by simp [s1_st, s0]) (by simp [s1_st, s0]) (by simp [s1_st, s0]) hrun₂
        have hc3 := runs_call_regs4 6 0 1 5 4 (st := s2_st) C.attachLeft_body (by simp [s2_st, s1_st, s0]) (by simp [s2_st, s1_st, s0]) (by simp [s2_st, hL0]) (by simp [s2_st, s1_st, s0]) hrun₃
        have hc4 := runs_call_regs4 6 0 2 1 4 (st := s3_st) C.attachLeft_body (by simp [s3_st, s2_st, s1_st, s0]) (by simp [s3_st, s2_st, s1_st, s0]) (by simp [s3_st, s2_st, s1_st, s0]) (by simp [s3_st, s2_st, s1_st, s0]) hrun₄
        have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s4_st) (r := 2) (v := yid) (by simp [s4_st, s3_st, s2_st, s1_st, s0])
        exact ⟨s4_st, _, rfl, by omega, tour_runs_seq_normal hc1 (tour_runs_seq_normal hc2 (tour_runs_seq_normal hc3 (tour_runs_seq_normal hc4 hret)))⟩
      obtain ⟨st_fin, c_fin, hmem_fin, hcfin, hbody_run⟩ := hbody_run
      refine ⟨AuxTree.node yid (AuxTree.node x .leaf .leaf) R, tourAttachLeft s₂ yid x, .returned yid, st_fin, c_fin,
        [], R.toList, hbody_run, rfl, hmem_fin ▸ hn₄, hmem_fin ▸ (hfr₁.trans (hfr₂.trans (hfr₃.trans hfr₄))),
        hinv₄, hvals₄, by simp, rfl, by rw [← hlist₁, hLc]; simp [AuxTree.toList],
        by simp [AuxTree.toList], hval_all, ?_, ?_⟩
      · intro u hux hut
        have hu1 : u ∉ (AuxTree.node yid .leaf R).toList := by rwa [← hLc, hlist₁]
        have hu4 : u ∉ (AuxTree.node yid (AuxTree.node x .leaf .leaf) R).toList := by
          intro hm; apply hu1
          simp only [AuxTree.toList, List.nil_append, List.append_nil, List.mem_append, List.mem_singleton] at hm ⊢
          tauto
        exact (hout₄ u hu4).trans ((hout₂ u (by rwa [hLc])).trans (hout₁ u hut))
      · have hphi2' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₂
        have hphi4' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₄
        simp only [hLc, ↓reduceIte, List.nil_append, List.cons_append,
          TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_SEQ_AMORT] at hcost₁ hphi2' hphi4' hc₂ hc₃ hc₄ hcfin ⊢
        nlinarith
    | node lid lL lR =>
      set Lne := AuxTree.node lid lL lR
      have hLroot : o₂.value = Lne.rootId := by simpa [hLc] using hv₂_eq
      have hperm₂ : ([AuxTree.node x .leaf .leaf] ++ ([Lne] ++ [AuxTree.node yid .leaf R]) ++ rest).Perm
          (Lne :: AuxTree.node x .leaf .leaf :: AuxTree.node yid .leaf R :: rest) := by
        simp only [List.cons_append, List.nil_append]; exact List.Perm.swap _ _ _
      have hinv₂' : TourForestInv cap s₂ (Lne :: AuxTree.node x .leaf .leaf :: AuxTree.node yid .leaf R :: rest) :=
        ((by simpa [hLc, Lne] using hinv₂ : TourForestInv cap s₂ ([AuxTree.node x .leaf .leaf] ++ ([Lne] ++ [AuxTree.node yid .leaf R]) ++ rest)).perm hperm₂).1
      have hl_cap : Lne.rootId ≤ cap := (hinv₂'.mem_inCap (t := Lne) (by simp) (by simp [Lne, AuxTree.toList, AuxTree.rootId])).2
      obtain ⟨o₃, st₃, c₃, hrun₃, ⟨hn₃, hfr₃⟩, hc₃⟩ := tourAttachLeftBody_runs (pos := st₂.pos)
        C.toTourSplayCoreProcs ω hn₂ hinv₂'.ptrOk hx_cap hl_cap
        (heapOk_zero' (heapOk_of_frame' hheap (hfr₁.trans hfr₂))) (tourAttachLeft_sumOk hinv₂' hvals₂)
      obtain ⟨hinv₃, hout₃, hval₃, hphi₃⟩ := tourAttachLeft_preserves hinv₂'
      set s₃ := tourAttachLeft s₂ x Lne.rootId
      have hvals₃ : TourValsOk w cap s₃ := ⟨hvals₂.1, fun u hu => by rw [hval₃ u hu]; exact hvals₂.2 u hu⟩
      obtain ⟨o₄, st₄, c₄, hrun₄, ⟨hn₄, hfr₄⟩, hc₄⟩ := tourAttachLeftBody_runs (pos := st₃.pos)
        C.toTourSplayCoreProcs ω hn₃ hinv₃.ptrOk hy_cap hx_cap
        (heapOk_zero' (heapOk_of_frame' hheap (hfr₁.trans (hfr₂.trans hfr₃)))) (tourAttachLeft_sumOk hinv₃ hvals₃)
      obtain ⟨hinv₄, hout₄, hval₄, hphi₄⟩ := tourAttachLeft_preserves hinv₃
      set s₄ := tourAttachLeft s₃ yid x
      obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf0 hy hdep
      have hval_all : ∀ u ≤ cap, (s₄.nodes u).val = (st.nodes u).val := by
        intro u hu; exact (hval₄ u hu).trans ((hval₃ u hu).trans ((hval₂ u hu).trans (hval_sp u hu)))
      have hvals₄ : TourValsOk w cap s₄ := ⟨hvals.1, fun u hu => by rw [hval_all u hu]; exact hvals.2 u hu⟩
      have hbody_run : ∃ st_fin c_fin, st_fin.mem = st₄.mem ∧ c_fin ≤ c₁ + c₂ + c₃ + c₄ + 35 ∧
          Runs w p ω (tourInsertBeforeBody C.splay.splay C.detachLeft C.attachLeft)
            (startState [nb, x, yid, fuel, heap] mem pos) (.returned yid) st_fin c_fin := by
        unfold tourInsertBeforeBody; rw [startState]
        set s0 : State := ⟨mem, fun i => [nb, x, yid, fuel, heap].getD i 0, pos⟩
        set s1_st : State := { st₁ with regs := Function.update s0.regs 5 o₁.value }
        set s2_st : State := { st₂ with regs := Function.update s1_st.regs 5 o₂.value }
        set s3_st : State := { st₃ with regs := Function.update s2_st.regs 6 o₃.value }
        set s4_st : State := { st₄ with regs := Function.update s3_st.regs 6 o₄.value }
        have hc1 := runs_call_regs4 5 0 2 3 4 (st := s0) C.splay.splay_body (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) hrun₁
        have hc2 := runs_call_regs3 5 0 2 4 (st := s1_st) C.detachLeft_body (by simp [s1_st, s0]) (by simp [s1_st, s0]) (by simp [s1_st, s0]) hrun₂
        have hc3 := runs_call_regs4 6 0 1 5 4 (st := s2_st) C.attachLeft_body (by simp [s2_st, s1_st, s0]) (by simp [s2_st, s1_st, s0]) (by simp [s2_st, hLroot]) (by simp [s2_st, s1_st, s0]) hrun₃
        have hc4 := runs_call_regs4 6 0 2 1 4 (st := s3_st) C.attachLeft_body (by simp [s3_st, s2_st, s1_st, s0]) (by simp [s3_st, s2_st, s1_st, s0]) (by simp [s3_st, s2_st, s1_st, s0]) (by simp [s3_st, s2_st, s1_st, s0]) hrun₄
        have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s4_st) (r := 2) (v := yid) (by simp [s4_st, s3_st, s2_st, s1_st, s0])
        exact ⟨s4_st, _, rfl, by omega, tour_runs_seq_normal hc1 (tour_runs_seq_normal hc2 (tour_runs_seq_normal hc3 (tour_runs_seq_normal hc4 hret)))⟩
      obtain ⟨st_fin, c_fin, hmem_fin, hcfin, hbody_run⟩ := hbody_run
      refine ⟨AuxTree.node yid (AuxTree.node x Lne .leaf) R, s₄, .returned yid, st_fin, c_fin,
        Lne.toList, R.toList, hbody_run, rfl, hmem_fin ▸ hn₄, hmem_fin ▸ (hfr₁.trans (hfr₂.trans (hfr₃.trans hfr₄))),
        hinv₄, hvals₄, by simp, rfl, by rw [← hlist₁, hLc]; simp [Lne, AuxTree.toList],
        by simp [AuxTree.toList, List.append_assoc], hval_all, ?_, ?_⟩
      · intro u hux hut
        have hu1 : u ∉ (AuxTree.node yid Lne R).toList := by rwa [← hLc, hlist₁]
        have hu3 : u ∉ (AuxTree.node x Lne .leaf).toList := fun hm => by
          simp only [AuxTree.toList, List.append_nil, List.mem_append, List.mem_singleton] at hm
          rcases hm with hL | rfl; exact hu1 (by simp [AuxTree.toList, hL]); exact hux rfl
        have hu4 : u ∉ (AuxTree.node yid (AuxTree.node x Lne .leaf) R).toList := fun hm => by
          simp only [AuxTree.toList, List.append_nil, List.mem_append, List.mem_singleton] at hm
          rcases hm with ((hL | rfl) | rfl) | hR
          · exact hu1 (by simp [AuxTree.toList, hL])
          · exact hux rfl
          · exact hu1 (by simp [AuxTree.toList])
          · exact hu1 (by simp [AuxTree.toList, hR])
        exact (hout₄ u hu4).trans ((hout₃ u hu3).trans ((hout₂ u (by rwa [hLc])).trans (hout₁ u hut)))
      · have hphi2' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₂
        have hphi3' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₃
        have hphi4' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₄
        have hpeq2 := forestPhi_perm hperm₂
        simp only [hLc, reduceCtorEq, ↓reduceIte] at hphi2' hcost₁
        rw [← hpeq2] at hphi3'
        simp only [Lne, List.cons_append, List.nil_append, TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_SEQ_AMORT] at hcost₁ hphi2' hphi3' hphi4' hc₂ hc₃ hc₄ hcfin ⊢
        omega

/-! ## Amortized run theorems for `tourFindFirstBody`, `tourSetValNodeBody`, `tourRootTagOfBody` -/

/-- Running `tourFindFirstBody` on an optional tree `t?` returns `0` if `t?` is empty or has no
ready node, and otherwise returns the leftmost ready node `y` splayed to the root of `t'`. -/
theorem tourFindFirstBody_runs {w nb cap heap fuel pos dp : ℕ} {p : Program}
    {rs : TourSum → Bool} {rv : TourVal → Bool}
    (C : TourSplayQueryProcs w p) (T : ReadyTests w p tourLayout rs rv) (hTc : T.cost = TOUR_TEST_COST)
    (hR : ReadyLaw tourPayload rs rv)
    (hdp : p.procs[dp]? = some (descendBody dp C.lazy.pushDown T.sumTest T.valTest))
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t? : Option AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (optTrees t? ++ rest)) (hvals : TourValsOk w cap st)
    (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ y t'? s' o st' c,
      Runs w p ω (tourFindFirstBody dp T.sumTest C.splay.splay)
        (startState [nb, optRoot t?, fuel, heap] mem pos) o st' c ∧
      o.value = y ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (optTrees t'? ++ rest) ∧
      TourValsOk w cap s' ∧
      optList t'? = optList t? ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ optList t?, s'.nodes u = st.nodes u) ∧
      (match (optList t?).find? (fun u => rv (st.nodes u).val) with
        | none => y = 0 ∧ t'? = t? ∧ s' = st
        | some y₀ => y = y₀ ∧ ∃ t' L R, t'? = some t' ∧ t' = AuxTree.node y L R ∧
            (∀ u ∈ L.toList, rv (st.nodes u).val = false) ∧ rv (st.nodes y).val = true) ∧
      c + TOUR_PHI_MULT * forestPhi (optTrees t'? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (optTrees t? ++ rest) + TOUR_FIND_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hwide := hheap.wide; have hroom := hheap.room
  unfold tourFindFirstBody; rw [startState]
  cases t? with
  | none =>
    set st0 : State := ⟨mem, fun i => [nb, 0, fuel, heap].getD i 0, pos⟩
    have hc0 : (Expr.bin .eq (.reg 1) (.const 0)).eval w st0 = some 1 := by
      simp [Expr.eval, st0, BinOp.eval, Nat.pos_of_ne_zero (by omega : 2 ^ w ≠ 0), (by omega : 1 < 2 ^ w)]
    have hret : Runs w p ω (.ret (.const 0)) st0 (.returned 0) st0 _ :=
      runs_ret_iff.mpr ⟨_, by simp [st0]; eval_expr, rfl, rfl, rfl⟩
    refine ⟨0, none, st, .returned 0, st0, _,
      tour_runs_cond_true hc0 (by omega) hret, rfl, hnodes,
      TreeFrame.refl hheap.zero, hf, hvals, rfl, fun _ _ => rfl, fun _ _ => rfl,
      by simp [optList], by simp only [Expr.size, TOUR_FIND_AMORT]; omega⟩
  | some t =>
    have ht_mem : t ∈ optTrees (some t) ++ rest := by simp [optTrees]
    have ht_ne : t ≠ .leaf := hf.nonEmpty t ht_mem
    have hr_nz : t.rootId ≠ 0 := by
      cases t with | leaf => exact absurd rfl ht_ne | node _ _ _ => exact (hf.treesInv _ ht_mem).sub.1
    have hr_cap : t.rootId ≤ cap := (hf.mem_inCap ht_mem (AuxTree.rootId_mem ht_ne)).2
    have hAr : nb + 17 * t.rootId + 17 ≤ heap := by
      simpa [nodeAddr, tourLayout_stride] using hheap.addr_lt hr_cap
    have hsum_pre : (sumTestContract tourLayout rs w T.cost).pre [nb + 17 * t.rootId] mem :=
      ⟨nb + 17 * t.rootId, (st.nodes t.rootId).val, (st.nodes t.rootId).sum, rfl,
        by rw [tourLayout_stride]; omega, (hnodes t.rootId hr_cap).2.2.2.2.2.2.1,
        (hnodes t.rootId hr_cap).2.2.2.2.2.2.2.1⟩
    obtain ⟨b_st, hb_st, o_st, st_st, c_st, hrun_st, ⟨hmem_st, hval_st⟩, hc_st⟩ :=
      T.sum_ok [nb + 17 * t.rootId] mem pos ω (by simp; omega) hsum_pre
    have hval_st' : o_st.value = if rs (st.nodes t.rootId).sum then 1 else 0 :=
      hval_st (st.nodes t.rootId).sum (hnodes t.rootId hr_cap).2.2.2.2.2.2.2.1
    set r0 := fun i => [nb, t.rootId, fuel, heap].getD i 0
    set r1 := Function.update r0 4 (nb + 17 * t.rootId)
    have h17_lt : 17 * t.rootId < 2 ^ w := by omega
    have hnb17_lt : nb + 17 * t.rootId < 2 ^ w := by omega
    have hc0 := eval_eq_zero_of_ne' (w := w) (r := 1) (v := t.rootId)
      (st := ⟨mem, r0, pos⟩) (by simp [r0]) hr_nz (by omega)
    have hass : Runs w p ω (.assign 4 (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))))
        ⟨mem, r0, pos⟩ .normal ⟨mem, r1, pos⟩ _ :=
      runs_assign_iff.mpr ⟨nb + 17 * t.rootId, by simp [Expr.eval, r0, BinOp.eval, h17_lt, hnb17_lt, (by omega : 17 < 2 ^ w)], rfl, rfl, rfl⟩
    have hcall_st := tour_runs_call_of (r := 5) (args := [.reg 4]) (st := ⟨mem, r1, pos⟩) hb_st
      (by simp [evalArgs, Expr.eval, r1]) hrun_st
    cases hrs : rs (st.nodes t.rootId).sum with
    | false =>
      have hv0 : o_st.value = 0 := by simp [hval_st', hrs]
      have hfind_none : t.toList.find? (fun u => rv (st.nodes u).val) = none :=
        find?_eq_none_of_rs_false hR hf ht_mem hrs
      have hret0 := runs_ret_const (w := w) (p := p) (ω := ω) (v := 0) (st := ⟨st_st.mem, Function.update r1 5 o_st.value, st_st.pos⟩) (by omega)
      have hcond5 := tour_runs_cond_true (e := .bin .eq (.reg 5) (.const 0)) (v := 1)
        (s₁ := .ret (.const 0))
        (s₂ := (.call 6 dp [.reg 0, .reg 1, .reg 2, .reg 3] ;; .call 7 C.splay.splay [.reg 0, .reg 6, .reg 2, .reg 3] ;; .ret (.reg 6)))
        (by simp [Expr.eval, Function.update_self, hv0, BinOp.eval, Nat.pos_of_ne_zero (by omega : 2 ^ w ≠ 0), (by omega : 1 < 2 ^ w)])
        (by omega) hret0
      have hfull := tour_runs_cond_false (s₁ := .ret (.const 0)) hc0 (tour_runs_seq_normal hass (tour_runs_seq_normal hcall_st hcond5))
      refine ⟨0, some t, st, .returned 0, _, _, hfull, rfl, hmem_st ▸ hnodes,
        by rw [hmem_st]; exact TreeFrame.refl hheap.zero, hf, hvals, rfl, fun _ _ => rfl, fun _ _ => rfl,
        by simp [optList, hfind_none], ?_⟩
      simp only [sumTestContract, hTc, TOUR_TEST_COST] at hc_st
      simp only [argsSize, Expr.size, TOUR_FIND_AMORT] at hc_st ⊢; omega
    | true =>
      have hv1 : o_st.value = 1 := by simp [hval_st', hrs]
      have hcnt : t.countNodes < fuel := lt_of_le_of_lt (hf.countNodes_le ht_mem) hfuel
      have hf0 : TourForestInv cap st ([] ++ t :: rest) := by simpa [optTrees] using hf
      obtain ⟨y, t', o₁, st₁, c₁, o₂, st₂, c₂, hrun₁, hv₁, hrun₂, hn₂, hfr₂, hinv₂, hvals₂,
        hne', hroot', hlist', hfind', hout₂, hcost₂⟩ :=
        tourDescendSplay_cost_le (pos := st_st.pos) C.toTourSplayCoreProcs T hTc hR hdp ω
          (hmem_st ▸ hnodes) hf0 hvals hrs hcnt hfuelW (hmem_st ▸ hheap)
      set s' := SplayState.splay tourPayload st fuel y
      set st_b : State := ⟨st_st.mem, Function.update r1 5 o_st.value, st_st.pos⟩
      set st_d : State := { st₁ with regs := Function.update st_b.regs 6 o₁.value }
      set st_s : State := { st₂ with regs := Function.update st_d.regs 7 o₂.value }
      have hcall_d := runs_call_regs4 6 0 1 2 3 (st := st_b) hdp (by simp [st_b, r1, r0]) (by simp [st_b, r1, r0]) (by simp [st_b, r1, r0]) (by simp [st_b, r1, r0]) hrun₁
      have hcall_s := runs_call_regs4 7 0 6 2 3 (st := st_d) C.splay.splay_body (by simp [st_d, st_b, r1, r0]) (by simp [st_d, hv₁]) (by simp [st_d, st_b, r1, r0]) (by simp [st_d, st_b, r1, r0]) hrun₂
      have hret_y := runs_ret_reg (w := w) (p := p) (ω := ω) (st := st_s) (r := 6) (v := y) (by simp [st_s, st_d, hv₁])
      have hbranch := tour_runs_seq_normal hcall_d (tour_runs_seq_normal hcall_s hret_y)
      have hcond5 := tour_runs_cond_false (e := .bin .eq (.reg 5) (.const 0)) (s₁ := .ret (.const 0))
        (by simp [Expr.eval, st_b, Function.update_self, hv1, BinOp.eval, Nat.pos_of_ne_zero (by omega : 2 ^ w ≠ 0)]) hbranch
      have hfull := tour_runs_cond_false (s₁ := .ret (.const 0)) hc0 (tour_runs_seq_normal hass (tour_runs_seq_normal hcall_st hcond5))
      have hy_mem : y ∈ t.toList := List.mem_of_find?_eq_some hfind'
      have hdep_y : t.depthOf y < fuel := lt_trans (auxTree_depthOf_lt_countNodes hy_mem) hcnt
      obtain ⟨_, _, _, _, _, _, hval_eq, _⟩ := tourSplay_preserves hf0 hy_mem hdep_y
      refine ⟨y, some t', s', .returned y, _, _, hfull, rfl, hn₂, hmem_st ▸ hfr₂,
        by simpa [optTrees] using hinv₂, hvals₂, by simpa [optList] using hlist', hval_eq,
        by simpa [optList] using hout₂, ?_, ?_⟩
      · simp only [optList, Option.elim, hfind']
        refine ⟨trivial, t', ?_⟩
        cases ht'c : t' with
        | leaf => exact absurd ht'c hne'
        | node yid L R =>
          have hyid : yid = y := by simpa [ht'c, AuxTree.rootId] using hroot'
          rcases hyid with rfl
          refine ⟨L, R, rfl, rfl, ?_, List.find?_some (p := fun u => rv (st.nodes u).val) hfind'⟩
          intro u hu
          have ht_eq : t.toList = L.toList ++ yid :: R.toList := by rw [← hlist', ht'c]; simp [AuxTree.toList]
          rw [ht_eq] at hfind'
          cases hrv : rv (st.nodes u).val
          · rfl
          · exfalso
            obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp ((List.find?_isSome (p := fun u => rv (st.nodes u).val)).mpr ⟨u, hu, hrv⟩)
            have hfind_app : (L.toList ++ yid :: R.toList).find? (fun z => rv (st.nodes z).val) = some z := by
              rw [List.find?_append, hz]; rfl
            rw [hfind_app] at hfind'
            have hzy : z = yid := Option.some.inj hfind'
            have hz_mem : z ∈ L.toList := List.mem_of_find?_eq_some hz
            rw [hzy] at hz_mem
            have hnd' := (hinv₂.treesInv t' (by simp)).nodup; rw [ht'c] at hnd'
            exact (AuxTree.nodup_node_unfold hnd').2.1 hz_mem
      · simp only [sumTestContract, hTc, TOUR_TEST_COST] at hc_st
        simp only [optTrees, Option.toList, List.nil_append, List.cons_append,
          argsSize, Expr.size, TOUR_PHI_MULT, TOUR_SPLAY_AMORT, TOUR_FIND_AMORT] at hcost₂ hc_st ⊢
        omega

/-- Running `tourSetValNodeBody` splays `x` and overwrites its `TourVal`, keeping `t'.toList = t.toList`. -/
theorem tourSetValNodeBody_runs {w nb cap heap fuel x isOpen isMarked rootTag pos : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t : AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (t :: rest)) (hvals : TourValsOk w cap st)
    (hx : x ∈ t.toList) (hrtW : rootTag < 2 ^ w)
    (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ t' s' o st' c,
      let v : TourVal := ⟨0 < isOpen, 0 < isMarked, rootTag⟩
      Runs w p ω (tourSetValNodeBody C.splay.splay C.setVal)
        (startState [nb, x, isOpen, isMarked, rootTag, fuel, heap] mem pos) o st' c ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (t' :: rest) ∧
      TourValsOk w cap s' ∧
      t' ≠ .leaf ∧ t'.rootId = x ∧ t'.toList = t.toList ∧
      (s'.nodes x).val = v ∧
      (∀ u ≤ cap, u ≠ x → (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ t.toList, s'.nodes u = st.nodes u) ∧
      c + TOUR_PHI_MULT * forestPhi (t' :: rest) ≤
        TOUR_PHI_MULT * forestPhi (t :: rest) + TOUR_FIND_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hdep : t.depthOf x < fuel :=
    lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hx) (le_of_lt (lt_of_le_of_lt (hf.countNodes_le (by simp)) hfuel))
  have hf0 : TourForestInv cap st ([] ++ t :: rest) := hf
  obtain ⟨t₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, hout₁, hcost₁⟩ :=
    tourSplay_runs_amort (pos := pos) C.toTourSplayCoreProcs ω hnodes hf0 hvals hx hdep hfuelW hheap
  set s₁ := SplayState.splay tourPayload st fuel x
  cases ht₁c : t₁ with
  | leaf => exact absurd ht₁c hne₁
  | node xid L R =>
    have hxid : xid = x := by simpa [ht₁c, AuxTree.rootId] using hroot₁
    rcases hxid with rfl
    rw [ht₁c] at hinv₁ hlist₁ hcost₁
    have hx_cap : xid ≤ cap := (hinv₁.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList])).2
    set v : TourVal := ⟨0 < isOpen, 0 < isMarked, rootTag⟩
    obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hn₂, hfr₂⟩, hc₂⟩ := tourSetValBody_runs
      (isOpen := isOpen) (isMarked := isMarked) (rootTag := rootTag) (pos := st₁.pos)
      C.toTourSplayCoreProcs ω hn₁ hinv₁.ptrOk hx_cap
      ⟨hheap.rec_le, by have := hheap.room; omega, hfr₁.1, hheap.wide⟩
      (tourSetVal_sumOk (v := v) hinv₁ hvals₁ hrtW)
    obtain ⟨hinv₂, hvalx₂, hout₂⟩ := tourSetVal_preserves v hinv₁
    obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf0 hx hdep
    have hval_ne : ∀ u ≤ cap, u ≠ xid → ((tourSetVal s₁ xid v).nodes u).val = (st.nodes u).val := fun u hu hne => by
      rw [hout₂ u hne, hval_sp u hu]
    have hvals₂ : TourValsOk w cap (tourSetVal s₁ xid v) := ⟨hvals.1, fun u hu => by
      by_cases hux : u = xid
      · subst hux; rw [hvalx₂]; exact hrtW
      · rw [hval_ne u hu hux]; exact hvals.2 u hu⟩
    have hbody_run : ∃ st_fin c_fin, st_fin.mem = st₂.mem ∧ c_fin ≤ c₁ + c₂ + 25 ∧
        Runs w p ω (tourSetValNodeBody C.splay.splay C.setVal)
          (startState [nb, xid, isOpen, isMarked, rootTag, fuel, heap] mem pos) (.returned 0) st_fin c_fin := by
      unfold tourSetValNodeBody; rw [startState]
      set s0 : State := ⟨mem, fun i => [nb, xid, isOpen, isMarked, rootTag, fuel, heap].getD i 0, pos⟩
      set s1_st : State := { st₁ with regs := Function.update s0.regs 7 o₁.value }
      set s2_st : State := { st₂ with regs := Function.update s1_st.regs 7 o₂.value }
      have hc1 := runs_call_regs4 7 0 1 5 6 (st := s0) C.splay.splay_body (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) hrun₁
      have hc2 := runs_call_regs6 7 0 1 2 3 4 6 (st := s1_st) C.setVal_body (by simp [s1_st, s0]) (by simp [s1_st, s0]) (by simp [s1_st, s0]) (by simp [s1_st, s0]) (by simp [s1_st, s0]) (by simp [s1_st, s0]) hrun₂
      have hret := runs_ret_const (w := w) (p := p) (ω := ω) (st := s2_st) (v := 0) (by have := hheap.wide; omega)
      exact ⟨s2_st, _, rfl, by omega, tour_runs_seq_normal hc1 (tour_runs_seq_normal hc2 hret)⟩
    obtain ⟨st_fin, c_fin, hmem_fin, hcfin, hbody_run⟩ := hbody_run
    refine ⟨AuxTree.node xid L R, tourSetVal s₁ xid v, .returned 0, st_fin, c_fin, hbody_run, hmem_fin ▸ hn₂,
      hmem_fin ▸ (hfr₁.trans hfr₂), hinv₂, hvals₂, by simp, rfl, hlist₁, hvalx₂, hval_ne, ?_, ?_⟩
    · intro u hu; exact (hout₂ u (fun h => hu (h ▸ hx))).trans (hout₁ u hu)
    · simp only [List.nil_append, TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_FIND_AMORT] at hcost₁ hc₂ hcfin ⊢
      nlinarith

/-- Running `tourRootTagOfBody` splays `x` and returns `(s'.nodes x).sum.rootTag`, equal to the
fold of `rootTag` over `t.toList`. -/
theorem tourRootTagOfBody_runs {w nb cap heap fuel x pos : ℕ} {p : Program}
    (C : TourSplayQueryProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t : AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (t :: rest)) (hvals : TourValsOk w cap st)
    (hx : x ∈ t.toList) (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ t' s' o st' c,
      Runs w p ω (tourRootTagOfBody C.splay.splay)
        (startState [nb, x, fuel, heap] mem pos) o st' c ∧
      o.value = (t.toList.map fun u => (st.nodes u).val.rootTag).foldr max 0 ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (t' :: rest) ∧
      TourValsOk w cap s' ∧
      t' ≠ .leaf ∧ t'.rootId = x ∧ t'.toList = t.toList ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ t.toList, s'.nodes u = st.nodes u) ∧
      c + TOUR_PHI_MULT * forestPhi (t' :: rest) ≤
        TOUR_PHI_MULT * forestPhi (t :: rest) + TOUR_FIND_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hdep : t.depthOf x < fuel :=
    lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hx) (le_of_lt (lt_of_le_of_lt (hf.countNodes_le (by simp)) hfuel))
  have hf0 : TourForestInv cap st ([] ++ t :: rest) := hf
  obtain ⟨t₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, hout₁, hcost₁⟩ :=
    tourSplay_runs_amort (pos := pos) C.toTourSplayCoreProcs ω hnodes hf0 hvals hx hdep hfuelW hheap
  set s₁ := SplayState.splay tourPayload st fuel x
  have hx_cap : x ≤ cap := (hinv₁.mem_inCap (t := t₁) (by simp) (by rw [hlist₁]; exact hx)).2
  have hAx : nb + 17 * x + 17 ≤ heap := by simpa [nodeAddr, tourLayout_stride] using hheap.addr_lt hx_cap
  have hroom := hheap.room; have hwide := hheap.wide
  have hmem15 : st₁.mem (nb + 17 * x + 15) = (s₁.nodes x).sum.rootTag := by
    simpa [nodeAddr, tourLayout_offSum, tourLayout_stride] using (hn₁ x hx_cap).2.2.2.2.2.2.2.1.2.2.2
  obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf0 hx hdep
  have hrt_eq : (s₁.nodes x).sum.rootTag =
      (t.toList.map fun u => (st.nodes u).val.rootTag).foldr max 0 := by
    rw [← hroot₁, hinv₁.sum_rootTag (by simp), hlist₁]
    congr 1; refine List.map_congr_left fun u hu => ?_
    rw [hval_sp u (hf.mem_inCap (t := t) (by simp) hu).2]
  set s0 : State := ⟨mem, fun i => [nb, x, fuel, heap].getD i 0, pos⟩
  set st_r : State := { st₁ with regs := Function.update s0.regs 4 o₁.value }
  have hret : Runs w p ω (.ret (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))) (.const 15))))
      st_r (.returned (s₁.nodes x).sum.rootTag) st_r
      ((Expr.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))) (.const 15))).size + 1) := by
    refine runs_ret_iff.mpr ⟨_, ?_, rfl, rfl, rfl⟩
    simp only [Expr.eval, st_r, s0, Function.update_of_ne (by decide : (0 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (1 : ℕ) ≠ 4), List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, BinOp.eval,
      (by omega : 17 < 2 ^ w), (by omega : 17 * x < 2 ^ w),
      (by omega : nb + 17 * x < 2 ^ w), (by omega : 15 < 2 ^ w),
      (by omega : nb + 17 * x + 15 < 2 ^ w), ↓reduceIte, Option.map_some, hmem15]
  have hfull : ∃ c_fin, c_fin ≤ c₁ + 30 ∧
      Runs w p ω (tourRootTagOfBody C.splay.splay)
        (startState [nb, x, fuel, heap] mem pos) (.returned (s₁.nodes x).sum.rootTag) st_r c_fin := by
    unfold tourRootTagOfBody; rw [startState]
    have hc1 := runs_call_regs4 4 0 1 2 3 (st := s0) C.splay.splay_body (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) hrun₁
    exact ⟨_, by simp only [Expr.size]; omega, tour_runs_seq_normal hc1 hret⟩
  obtain ⟨c_fin, hcfin, hfull⟩ := hfull
  refine ⟨t₁, s₁, .returned (s₁.nodes x).sum.rootTag, st_r, c_fin, hfull, by simpa [Outcome.value] using hrt_eq,
    hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, hval_sp, hout₁, ?_⟩
  simp only [List.nil_append, TOUR_PHI_MULT, TOUR_SPLAY_AMORT, TOUR_FIND_AMORT] at hcost₁ ⊢
  omega

end MinCostFlow.SparseCore.Program
