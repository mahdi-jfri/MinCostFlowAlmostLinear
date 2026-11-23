module

public import MinCostFlow.SparseCore.Program.TourSplaySplice
public import MinCostFlow.SparseCore.Program.TourSplayOk
public import MinCostFlow.LinkCut.PathProg.SplayCost
import Mathlib.Tactic

/-!
# Core WordRAM splay procedures and amortized bounds for tour sequences

Implements and verifies the low-level WordRAM procedures on tour splay trees:
- `tourDetachLeftBody`, `tourDetachRightBody`, `tourAttachLeftBody`, `tourSetValBody`,
  `tourInitNodeBody` (all `O(1)` worst-case cost `≤ TOUR_SPLICE_COST`);
- Amortized run wrappers for `LinkCut.Gen.splayBody`, `leftmostWalkBody`, and `descendBody`
  against `TOUR_PHI_MULT * forestPhi trees`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

private theorem runs_cost_mono {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {P : Outcome → State → Prop} {k₁ k₂ b : ℕ}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ P o st' ∧ k₁ + c ≤ b) (hle : k₂ ≤ k₁) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ P o st' ∧ k₂ + c ≤ b := by
  obtain ⟨o, st', c, hrun, hp, hc⟩ := h
  exact ⟨o, st', c, hrun, hp, by omega⟩

/-! ## Concrete amortized constants -/

/-- Potential scaling factor paying for every `splay`, `leftmostWalk`, and `descend` step. -/
def TOUR_PHI_MULT : ℕ := 20000

/-- Worst-case cost bound on one `O(1)` tour splice or node-write procedure. -/
def TOUR_SPLICE_COST : ℕ := 500

/-- Amortized per-`log` cost constant for one splay or walk-and-splay step. -/
def TOUR_SPLAY_AMORT : ℕ := 80000

/-! ## Bundle of core `LinkCut.Gen` splay procedures -/

/-- The core `LinkCut.Gen` procedures needed by tour splay operations, at their indices in `p`. -/
structure TourSplayCoreProcs (w : ℕ) (p : Program) where
  steps : PayloadSteps w p tourPayload tourLayout (tourOk w)
  steps_cost : steps.cost = TOUR_PAYLOAD_COST
  steps_space : steps.space = 0
  lazy : LazyProcs w p tourPayload tourLayout (tourOk w) steps
  splay : SplayProcs lazy
  openTests : ReadyTests w p tourLayout tourOpenRs tourOpenRv
  openTests_cost : openTests.cost = TOUR_TEST_COST
  markTests : ReadyTests w p tourLayout tourMarkRs tourMarkRv
  markTests_cost : markTests.cost = TOUR_TEST_COST
  walkProc : ℕ
  walk_body : p.procs[walkProc]? = some (leftmostWalkBody walkProc lazy.pushDown)
  openDescProc : ℕ
  openDesc_body : p.procs[openDescProc]? =
    some (descendBody openDescProc lazy.pushDown openTests.sumTest openTests.valTest)
  markDescProc : ℕ
  markDesc_body : p.procs[markDescProc]? =
    some (descendBody markDescProc lazy.pushDown markTests.sumTest markTests.valTest)

theorem TourSplayCoreProcs.pushDownCost_eq {w : ℕ} {p : Program} (C : TourSplayCoreProcs w p) :
    pushDownCost C.steps = 2390 := by
  simp [pushDownCost, C.steps_cost, TOUR_PAYLOAD_COST, tourLayout]

theorem TourSplayCoreProcs.splayRate_eq {w : ℕ} {p : Program} (C : TourSplayCoreProcs w p) :
    splayRate C.steps = 9700 := by
  simp [splayRate, splayStepCost, rotateCost, pushDownCost, C.steps_cost, TOUR_PAYLOAD_COST,
    tourLayout]

theorem TourSplayCoreProcs.space_eq {w : ℕ} {p : Program} (C : TourSplayCoreProcs w p) :
    2 * tourLayout.tagW + C.steps.space = 2 := by
  simp [C.steps_space, tourLayout]

/-! ## WordRAM bodies for `tourDetachLeft`, `tourDetachRight`, `tourAttachLeft`, `tourSetVal`, `initNode` -/

/-- `tourDetachLeft [nb, x, heap]`: detach left child of `x`, pull `x`, return old left child. -/
def tourDetachLeftBody (pullProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 3 (recAddr 1) ;;
     .assign 4 (.load (.reg 3)) ;;
     .cond (.bin .eq (.reg 4) (.const 0)) (.ret (.const 0))
       (.store (.bin .add (recAddr 4) (.const 2)) (.const 0) ;;
        .store (.reg 3) (.const 0) ;;
        .call 5 pullProc [.reg 0, .reg 1, .reg 2] ;;
        .ret (.reg 4)))

/-- `tourDetachRight [nb, x, heap]`: detach right child of `x`, pull `x`, return old right child. -/
def tourDetachRightBody (pullProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 3 (recAddr 1) ;;
     .assign 4 (.load (.bin .add (.reg 3) (.const 1))) ;;
     .cond (.bin .eq (.reg 4) (.const 0)) (.ret (.const 0))
       (.store (.bin .add (recAddr 4) (.const 2)) (.const 0) ;;
        .store (.bin .add (.reg 3) (.const 1)) (.const 0) ;;
        .call 5 pullProc [.reg 0, .reg 1, .reg 2] ;;
        .ret (.reg 4)))

/-- `tourAttachLeft [nb, y, l, heap]`: attach `l` as left child of `y` (which has `left = 0`),
clear `ppar` on `l`, and pull `y`. -/
def tourAttachLeftBody (pullProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.store (recAddr 1) (.reg 2) ;;
     .cond (.reg 2)
       (.assign 4 (recAddr 2) ;;
        .store (.bin .add (.reg 4) (.const 2)) (.reg 1) ;;
        .store (.bin .add (.reg 4) (.const 3)) (.const 0))
       .nop ;;
     .call 5 pullProc [.reg 0, .reg 1, .reg 3] ;;
     .ret (.const 0))

/-- `tourSetVal [nb, x, isOpen, isMarked, rootTag, heap]`: overwrite `x`'s value fields and pull `x`. -/
def tourSetValBody (pullProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 6 (recAddr 1) ;;
     .store (.bin .add (.reg 6) (.const 9)) (.bin .lt (.const 0) (.reg 2)) ;;
     .store (.bin .add (.reg 6) (.const 10)) (.bin .lt (.const 0) (.reg 3)) ;;
     .store (.bin .add (.reg 6) (.const 11)) (.reg 4) ;;
     .call 7 pullProc [.reg 0, .reg 1, .reg 5] ;;
     .ret (.const 0))

/-- `tourInitNode [nb, x, isOpen, isMarked, rootTag]`: write a clean singleton record for node `x`
at `nb + 17 * x` directly (works even on an uninitialized zero slot). -/
def tourInitNodeBody : Stmt :=
  .assign 5 (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))) ;;
  .assign 6 (.bin .lt (.const 0) (.reg 2)) ;;
  .assign 7 (.bin .lt (.const 0) (.reg 3)) ;;
  .store (.reg 5) (.const 0) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.const 0) ;;
  .store (.bin .add (.reg 5) (.const 2)) (.const 0) ;;
  .store (.bin .add (.reg 5) (.const 3)) (.const 0) ;;
  .store (.bin .add (.reg 5) (.const 4)) (.const 1) ;;
  .store (.bin .add (.reg 5) (.const 5)) (.const 0) ;;
  .store (.bin .add (.reg 5) (.const 6)) (.const 17) ;;
  .store (.bin .add (.reg 5) (.const 7)) (.const 6) ;;
  .store (.bin .add (.reg 5) (.const 8)) (.const 1) ;;
  .store (.bin .add (.reg 5) (.const 9)) (.reg 6) ;;
  .store (.bin .add (.reg 5) (.const 10)) (.reg 7) ;;
  .store (.bin .add (.reg 5) (.const 11)) (.reg 4) ;;
  .store (.bin .add (.reg 5) (.const 12)) (.const 1) ;;
  .store (.bin .add (.reg 5) (.const 13)) (.reg 6) ;;
  .store (.bin .add (.reg 5) (.const 14)) (.reg 7) ;;
  .store (.bin .add (.reg 5) (.const 15)) (.reg 4) ;;
  .store (.bin .add (.reg 5) (.const 16)) (.const 0) ;;
  .ret (.const 0)

theorem tourSplayProg_bodies_noRand (pullProc : ℕ) :
    (tourDetachLeftBody pullProc).NoRand ∧
    (tourDetachRightBody pullProc).NoRand ∧
    (tourAttachLeftBody pullProc).NoRand ∧
    (tourSetValBody pullProc).NoRand ∧
    tourInitNodeBody.NoRand := by
  simp [tourDetachLeftBody, tourDetachRightBody, tourAttachLeftBody, tourSetValBody,
    tourInitNodeBody, recAddr, Stmt.NoRand]

/-! ## Run theorems for `tourDetachLeftBody`, `tourDetachRightBody`, `tourAttachLeftBody`, `tourSetValBody`, `tourInitNodeBody` -/

private theorem treeFrame_of_rec_write {nb cap heap x off v : ℕ} {mem M : ℕ → ℕ}
    (hx : x ≤ cap) (hoff : off < tourLayout.nodeStride)
    (hA : tourLayout.nodeAddr nb x + tourLayout.nodeStride ≤ heap)
    (hF : TreeFrame tourLayout nb cap heap mem M) :
    TreeFrame tourLayout nb cap heap mem (Function.update M (tourLayout.nodeAddr nb x + off) v) := by
  refine ⟨fun y hy => ?_, fun y hy hni => ?_⟩
  · rw [Function.update_of_ne (by omega)]; exact hF.1 y hy
  · rw [Function.update_of_ne ?_]; exact hF.2 y hy hni
    intro heq; apply hni; rw [heq]; exact inRecords_of_rec hx hoff

theorem tourDetachLeftBody_runs {w nb cap x heap pos : ℕ} {p : Program}
    (C : TourSplayCoreProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit}
    (hnodes : tourLayout.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk tourLayout w nb cap heap 0 mem)
    (hok : x ≠ 0 → (st.nodes x).left ≠ 0 →
      (tourOk w).sumOk (pullSum tourPayload ((st.setPar (st.nodes x).left 0).setLeft x 0) x)) :
    ∃ o st' c, Runs w p ω (tourDetachLeftBody C.splay.pull)
        (startState [nb, x, heap] mem pos) o st' c ∧
      (o.value = (if x = 0 then 0 else (st.nodes x).left) ∧
       tourLayout.NodesAt st'.mem nb cap (tourDetachLeft st x) ∧
       TreeFrame tourLayout nb cap heap mem st'.mem) ∧
      0 + c ≤ TOUR_SPLICE_COST := by
  have hroom := hheap.room; have hwide := hheap.wide; have hS := hheap.stride_lt
  have hS6 := tourLayout.stride_pos; have hrec := hheap.rec_le
  have hlt : ∀ y ≤ cap, nb + tourLayout.nodeStride * y + tourLayout.nodeStride ≤ heap := fun y hy => by
    simpa [nodeAddr] using hheap.addr_lt hy
  have hlc := (hptr x hx).1
  generalize hl : (st.nodes x).left = l at hlc hok
  have hAx := hlt x hx; have hAl := hlt l hlc
  unfold tourDetachLeftBody; rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simp [Outcome.value], by simpa [tourDetachLeft] using hnodes, TreeFrame.refl hheap.zero⟩
    · simp only [TOUR_SPLICE_COST]; wram_cost
  have hx0 : x ≠ 0 := hcond
  have hm0 : mem (nb + tourLayout.nodeStride * x) = l := by
    simpa [nodeAddr, OFF_LEFT, hl] using (hnodes x hx).1
  wram_step; try dsimp only
  wram_step; try dsimp only
  rw [hm0]
  wram_step
  · have hl0 : l = 0 := hcond
    wram_step
    · exact ⟨by simp [Outcome.value, hx0, hl0],
        by simpa [tourDetachLeft, hx0, hl, hl0] using hnodes, TreeFrame.refl hheap.zero⟩
    · simp only [TOUR_SPLICE_COST]; wram_cost
  have hl0 : l ≠ 0 := hcond
  have hheap0 : HeapOk tourLayout w nb cap heap C.steps.space mem :=
    ⟨hrec, by rw [C.steps_space]; omega, hheap.zero, hwide⟩
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₁ hM₁ => ?_
  have h₁ : tourLayout.NodesAt M₁ nb cap (st.setPar l 0) ∧ TreeFrame tourLayout nb cap heap mem M₁ := by
    rw [hM₁]; exact ⟨(hnodes.setPar tourLayout hlc), treeFrame_of_rec_write hlc (by decide) hAl (TreeFrame.refl hheap.zero)⟩
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₂ hM₂ => ?_
  have h₂ : tourLayout.NodesAt M₂ nb cap ((st.setPar l 0).setLeft x 0) ∧ TreeFrame tourLayout nb cap heap mem M₂ := by
    rw [hM₂]
    have ha : nb + tourLayout.nodeStride * x = tourLayout.nodeAddr nb x + OFF_LEFT := by simp [nodeAddr, OFF_LEFT]
    rw [ha]
    exact ⟨h₁.1.setLeft tourLayout hx, treeFrame_of_rec_write hx (by decide) hAx h₁.2⟩
  refine runs_seq_callBody_le C.splay.pull_body (by eval_expr)
    (R := fun _ st₃ c₃ => tourLayout.NodesAt st₃.mem nb cap (tourDetachLeft st x) ∧
      TreeFrame tourLayout nb cap heap mem st₃.mem ∧ c₃ ≤ C.steps.cost + 150) ?_ ?_
  · have hptr2 : PtrOk cap ((st.setPar l 0).setLeft x 0) :=
      (hptr.setPar hlc (Nat.zero_le _)).setLeft hx (Nat.zero_le _)
    obtain ⟨o, st', c, hrun, ⟨hn, hf⟩, hc⟩ := pullBody_runs C.steps ω h₂.1 hptr2 hx
      ⟨hrec, by rw [C.steps_space]; omega, h₂.2.1, hwide⟩ (fun _ => hok hx0 hl0)
    refine ⟨o, st', c, hrun, ?_, h₂.2.trans hf, by omega⟩
    have : tourDetachLeft st x = pull tourPayload ((st.setPar l 0).setLeft x 0) x := by
      simp [tourDetachLeft, hx0, hl, hl0]
    rw [this]; exact hn
  rintro - st₃ c₃ ⟨hn₃, hf₃, hc₃⟩
  wram_step
  · exact ⟨by simp [Outcome.value, hx0], hn₃, hf₃⟩
  · have := C.steps_cost; simp only [TOUR_SPLICE_COST, TOUR_PAYLOAD_COST] at *; wram_cost

theorem tourDetachRightBody_runs {w nb cap x heap pos : ℕ} {p : Program}
    (C : TourSplayCoreProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit}
    (hnodes : tourLayout.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk tourLayout w nb cap heap 0 mem)
    (hok : x ≠ 0 → (st.nodes x).right ≠ 0 →
      (tourOk w).sumOk (pullSum tourPayload ((st.setPar (st.nodes x).right 0).setRight x 0) x)) :
    ∃ o st' c, Runs w p ω (tourDetachRightBody C.splay.pull)
        (startState [nb, x, heap] mem pos) o st' c ∧
      (o.value = (if x = 0 then 0 else (st.nodes x).right) ∧
       tourLayout.NodesAt st'.mem nb cap (tourDetachRight st x) ∧
       TreeFrame tourLayout nb cap heap mem st'.mem) ∧
      0 + c ≤ TOUR_SPLICE_COST := by
  have hroom := hheap.room; have hwide := hheap.wide; have hS := hheap.stride_lt
  have hS6 := tourLayout.stride_pos; have hrec := hheap.rec_le
  have hlt : ∀ y ≤ cap, nb + tourLayout.nodeStride * y + tourLayout.nodeStride ≤ heap := fun y hy => by
    simpa [nodeAddr] using hheap.addr_lt hy
  have hrc := (hptr x hx).2.1
  generalize hr : (st.nodes x).right = r at hrc hok
  have hAx := hlt x hx; have hAr := hlt r hrc
  unfold tourDetachRightBody; rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simp [Outcome.value], by simpa [tourDetachRight] using hnodes, TreeFrame.refl hheap.zero⟩
    · simp only [TOUR_SPLICE_COST]; wram_cost
  have hx0 : x ≠ 0 := hcond
  have hm1 : mem (nb + tourLayout.nodeStride * x + 1) = r := by
    simpa [nodeAddr, OFF_RIGHT, hr] using (hnodes x hx).2.1
  wram_step; try dsimp only
  wram_step; try dsimp only
  rw [hm1]
  wram_step
  · have hr0 : r = 0 := hcond
    wram_step
    · exact ⟨by simp [Outcome.value, hx0, hr0],
        by simpa [tourDetachRight, hx0, hr, hr0] using hnodes, TreeFrame.refl hheap.zero⟩
    · simp only [TOUR_SPLICE_COST]; wram_cost
  have hr0 : r ≠ 0 := hcond
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₁ hM₁ => ?_
  have h₁ : tourLayout.NodesAt M₁ nb cap (st.setPar r 0) ∧ TreeFrame tourLayout nb cap heap mem M₁ := by
    rw [hM₁]; exact ⟨hnodes.setPar tourLayout hrc, treeFrame_of_rec_write hrc (by decide) hAr (TreeFrame.refl hheap.zero)⟩
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₂ hM₂ => ?_
  have h₂ : tourLayout.NodesAt M₂ nb cap ((st.setPar r 0).setRight x 0) ∧ TreeFrame tourLayout nb cap heap mem M₂ := by
    rw [hM₂]; exact ⟨h₁.1.setRight tourLayout hx, treeFrame_of_rec_write hx (by decide) hAx h₁.2⟩
  refine runs_seq_callBody_le C.splay.pull_body (by eval_expr)
    (R := fun _ st₃ c₃ => tourLayout.NodesAt st₃.mem nb cap (tourDetachRight st x) ∧
      TreeFrame tourLayout nb cap heap mem st₃.mem ∧ c₃ ≤ C.steps.cost + 150) ?_ ?_
  · have hptr2 : PtrOk cap ((st.setPar r 0).setRight x 0) :=
      (hptr.setPar hrc (Nat.zero_le _)).setRight hx (Nat.zero_le _)
    obtain ⟨o, st', c, hrun, ⟨hn, hf⟩, hc⟩ := pullBody_runs C.steps ω h₂.1 hptr2 hx
      ⟨hrec, by rw [C.steps_space]; omega, h₂.2.1, hwide⟩ (fun _ => hok hx0 hr0)
    refine ⟨o, st', c, hrun, ?_, h₂.2.trans hf, by omega⟩
    have : tourDetachRight st x = pull tourPayload ((st.setPar r 0).setRight x 0) x := by
      simp [tourDetachRight, hx0, hr, hr0]
    rw [this]; exact hn
  rintro - st₃ c₃ ⟨hn₃, hf₃, hc₃⟩
  wram_step
  · exact ⟨by simp [Outcome.value, hx0], hn₃, hf₃⟩
  · have := C.steps_cost; simp only [TOUR_SPLICE_COST, TOUR_PAYLOAD_COST] at *; wram_cost

theorem tourAttachLeftBody_runs {w nb cap y l heap pos : ℕ} {p : Program}
    (C : TourSplayCoreProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit}
    (hnodes : tourLayout.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hy : y ≤ cap) (hl : l ≤ cap)
    (hheap : HeapOk tourLayout w nb cap heap 0 mem)
    (hok : y ≠ 0 → (tourOk w).sumOk (pullSum tourPayload
      (if l = 0 then st.setLeft y l else ((st.setLeft y l).setPar l y).setPpar l 0) y)) :
    ∃ o st' c, Runs w p ω (tourAttachLeftBody C.splay.pull)
        (startState [nb, y, l, heap] mem pos) o st' c ∧
      (tourLayout.NodesAt st'.mem nb cap (tourAttachLeft st y l) ∧
       TreeFrame tourLayout nb cap heap mem st'.mem) ∧
      0 + c ≤ TOUR_SPLICE_COST := by
  have hroom := hheap.room; have hwide := hheap.wide; have hS := hheap.stride_lt
  have hS6 := tourLayout.stride_pos; have hrec := hheap.rec_le
  have hlt : ∀ z ≤ cap, nb + tourLayout.nodeStride * z + tourLayout.nodeStride ≤ heap := fun z hz => by
    simpa [nodeAddr] using hheap.addr_lt hz
  have hAy := hlt y hy; have hAl := hlt l hl
  have hylt : y < 2 ^ w := by have : y ≤ tourLayout.nodeStride * y := Nat.le_mul_of_pos_left y (by omega); omega
  have hllt : l < 2 ^ w := by have : l ≤ tourLayout.nodeStride * l := Nat.le_mul_of_pos_left l (by omega); omega
  unfold tourAttachLeftBody; rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simpa [tourAttachLeft] using hnodes, TreeFrame.refl hheap.zero⟩
    · simp only [TOUR_SPLICE_COST]; wram_cost
  have hy0 : y ≠ 0 := hcond
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₁ hM₁ => ?_
  have h₁ : tourLayout.NodesAt M₁ nb cap (st.setLeft y l) ∧ TreeFrame tourLayout nb cap heap mem M₁ := by
    rw [hM₁]
    have ha : nb + tourLayout.nodeStride * y = tourLayout.nodeAddr nb y + OFF_LEFT := by simp [nodeAddr, OFF_LEFT]
    rw [ha]
    exact ⟨hnodes.setLeft tourLayout hy, treeFrame_of_rec_write hy (by decide) hAy (TreeFrame.refl hheap.zero)⟩
  set stMid := if l = 0 then st.setLeft y l else ((st.setLeft y l).setPar l y).setPpar l 0
  have hptrMid : PtrOk cap stMid := by
    dsimp only [stMid]; split_ifs
    · exact hptr.setLeft hy hl
    · exact ((hptr.setLeft hy hl).setPar hl hy).setPpar hl (Nat.zero_le _)
  have hpull_cont : ∀ (M : ℕ → ℕ) (regs : ℕ → ℕ) (k : ℕ),
      regs 0 = nb → regs 1 = y → regs 3 = heap →
      tourLayout.NodesAt M nb cap stMid → TreeFrame tourLayout nb cap heap mem M → k ≤ 80 →
      ∃ o st' c, Runs w p ω (.call 5 C.splay.pull [.reg 0, .reg 1, .reg 3] ;; .ret (.const 0))
        ⟨M, regs, pos⟩ o st' c ∧
        (tourLayout.NodesAt st'.mem nb cap (tourAttachLeft st y l) ∧
         TreeFrame tourLayout nb cap heap mem st'.mem) ∧ k + c ≤ TOUR_SPLICE_COST := by
    intro M regs k hr0 hr1 hr3 hNM hFM hk
    refine runs_seq_callBody_le C.splay.pull_body (by eval_expr)
      (R := fun _ st' c' => tourLayout.NodesAt st'.mem nb cap (tourAttachLeft st y l) ∧
        TreeFrame tourLayout nb cap heap mem st'.mem ∧ c' ≤ C.steps.cost + 150) ?_ ?_
    · obtain ⟨o, st', c, hrun, ⟨hn, hf⟩, hc⟩ := pullBody_runs C.steps ω hNM hptrMid hy
        ⟨hrec, by rw [C.steps_space]; omega, hFM.1, hwide⟩ (fun _ => hok hy0)
      refine ⟨o, st', c, hrun, ?_, hFM.trans hf, by omega⟩
      have : tourAttachLeft st y l = pull tourPayload stMid y := by
        simp [tourAttachLeft, stMid, hy0]
      rw [this]; exact hn
    rintro - st' c' ⟨hn', hf', hc'⟩
    wram_step
    · exact ⟨hn', hf'⟩
    · have := C.steps_cost; simp only [TOUR_SPLICE_COST, TOUR_PAYLOAD_COST] at *; wram_cost
  refine runs_seq_cond_le (by eval_expr) (fun hl0 => ?_) (fun hl0 => ?_)
  · wram_step; wram_step; try dsimp only
    refine runs_seq_assoc_le ?_
    refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₂ hM₂ => ?_
    have h₂ : tourLayout.NodesAt M₂ nb cap ((st.setLeft y l).setPar l y) ∧ TreeFrame tourLayout nb cap heap mem M₂ := by
      rw [hM₂]; exact ⟨h₁.1.setPar tourLayout hl, treeFrame_of_rec_write hl (by decide) hAl h₁.2⟩
    refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₃ hM₃ => ?_
    have h₃ : tourLayout.NodesAt M₃ nb cap stMid ∧ TreeFrame tourLayout nb cap heap mem M₃ := by
      rw [hM₃]; simp only [stMid, hl0, ↓reduceIte]
      exact ⟨h₂.1.setPpar tourLayout hl, treeFrame_of_rec_write hl (by decide) hAl h₂.2⟩
    exact runs_cost_mono (hpull_cont M₃ _ 70 (by simp) (by simp) (by simp) h₃.1 h₃.2 (by omega))
      (by wram_cost)
  · refine runs_seq_nop_le ?_
    have hst1 : stMid = st.setLeft y l := by simp [stMid, hl0]
    exact runs_cost_mono (hpull_cont M₁ _ 40 (by simp) (by simp) (by simp) (hst1 ▸ h₁.1) h₁.2 (by omega))
      (by wram_cost)

theorem tourSetValBody_runs {w nb cap x isOpen isMarked rootTag heap pos : ℕ} {p : Program}
    (C : TourSplayCoreProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit}
    (hnodes : tourLayout.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk tourLayout w nb cap heap 0 mem)
    (hok : x ≠ 0 →
      (tourOk w).sumOk (pullSum tourPayload
        (st.updateNode x fun nd => { nd with val := ⟨0 < isOpen, 0 < isMarked, rootTag⟩ }) x)) :
    ∃ o st' c, Runs w p ω (tourSetValBody C.splay.pull)
        (startState [nb, x, isOpen, isMarked, rootTag, heap] mem pos) o st' c ∧
      (tourLayout.NodesAt st'.mem nb cap (tourSetVal st x ⟨0 < isOpen, 0 < isMarked, rootTag⟩) ∧
       TreeFrame tourLayout nb cap heap mem st'.mem) ∧
      0 + c ≤ TOUR_SPLICE_COST := by
  have hroom := hheap.room; have hwide := hheap.wide; have hS := hheap.stride_lt
  have hS6 := tourLayout.stride_pos; have hrec := hheap.rec_le
  have hAx : nb + tourLayout.nodeStride * x + tourLayout.nodeStride ≤ heap := by
    simpa [nodeAddr] using hheap.addr_lt hx
  have hstride : tourLayout.nodeStride = 17 := rfl
  unfold tourSetValBody; rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simpa [tourSetVal] using hnodes, TreeFrame.refl hheap.zero⟩
    · simp only [TOUR_SPLICE_COST]; wram_cost
  have hx0 : x ≠ 0 := hcond
  set v : TourVal := ⟨0 < isOpen, 0 < isMarked, rootTag⟩
  set st1 := st.updateNode x fun nd => { nd with val := v }
  wram_step; try dsimp only
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₁ hM₁ => ?_
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₂ hM₂ => ?_
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₃ hM₃ => ?_
  dsimp only at hM₁ hM₂ hM₃
  have hF3 : TreeFrame tourLayout nb cap heap mem M₃ := by
    rw [hM₃, hM₂, hM₁]
    exact treeFrame_of_rec_write hx (by rw [hstride]; omega) hAx
      (treeFrame_of_rec_write hx (by rw [hstride]; omega) hAx
        (treeFrame_of_rec_write hx (by rw [hstride]; omega) hAx (TreeFrame.refl hheap.zero)))
  have hN3 : tourLayout.NodesAt M₃ nb cap st1 := by
    have hM3_ne : ∀ a, a ≠ nb + tourLayout.nodeStride * x + 9 →
        a ≠ nb + tourLayout.nodeStride * x + 10 →
        a ≠ nb + tourLayout.nodeStride * x + 11 → M₃ a = mem a := fun a h9 h10 h11 => by
      rw [hM₃, hM₂, hM₁, Function.update_of_ne h11, Function.update_of_ne h10,
        Function.update_of_ne h9]
    refine hnodes.update tourLayout hx ?_ fun a ha => hM3_ne a (ha 9 (by rw [hstride]; omega))
      (ha 10 (by rw [hstride]; omega)) (ha 11 (by rw [hstride]; omega))
    obtain ⟨h0, h1, h2, h3, h4, h5, hv, hs, _⟩ := hnodes x hx
    refine ⟨(hM3_ne _ (by simp [nodeAddr, OFF_LEFT]) (by simp [nodeAddr, OFF_LEFT]) (by simp [nodeAddr, OFF_LEFT])).trans h0,
      (hM3_ne _ (by simp [nodeAddr, OFF_RIGHT]) (by simp [nodeAddr, OFF_RIGHT]) (by simp [nodeAddr, OFF_RIGHT])).trans h1,
      (hM3_ne _ (by simp [nodeAddr, OFF_PAR]) (by simp [nodeAddr, OFF_PAR]) (by simp [nodeAddr, OFF_PAR])).trans h2,
      (hM3_ne _ (by simp [nodeAddr, OFF_PPAR]) (by simp [nodeAddr, OFF_PPAR]) (by simp [nodeAddr, OFF_PPAR])).trans h3,
      (hM3_ne _ (by simp [nodeAddr, OFF_SZ]) (by simp [nodeAddr, OFF_SZ]) (by simp [nodeAddr, OFF_SZ])).trans h4,
      (hM3_ne _ (by simp [nodeAddr, OFF_REV]) (by simp [nodeAddr, OFF_REV]) (by simp [nodeAddr, OFF_REV])).trans h5,
      ?_, tourLayout.sum_congr _ _ _ _ hs fun i hi => hM3_ne _
        (by rw [tourLayout_offSum]; simp only [nodeAddr]; omega)
        (by rw [tourLayout_offSum]; simp only [nodeAddr]; omega)
        (by rw [tourLayout_offSum]; simp only [nodeAddr]; omega), trivial⟩
    refine ⟨(hM3_ne _ (by simp [nodeAddr, OFF_VAL]) (by simp [nodeAddr, OFF_VAL]) (by simp [nodeAddr, OFF_VAL])).trans hv.1,
      (hM3_ne _ (by simp [nodeAddr, OFF_VAL]) (by simp [nodeAddr, OFF_VAL]) (by simp [nodeAddr, OFF_VAL])).trans hv.2.1,
      (hM3_ne _ (by simp [nodeAddr, OFF_VAL]) (by simp [nodeAddr, OFF_VAL]) (by simp [nodeAddr, OFF_VAL])).trans hv.2.2.1,
      ?_, ?_, ?_⟩
    · rw [hM₃, hM₂, hM₁, show tourLayout.nodeAddr nb x + OFF_VAL + 3 = nb + tourLayout.nodeStride * x + 9 by simp [nodeAddr, OFF_VAL]]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      simp [v]
    · rw [hM₃, hM₂, hM₁, show tourLayout.nodeAddr nb x + OFF_VAL + 4 = nb + tourLayout.nodeStride * x + 10 by simp [nodeAddr, OFF_VAL]]
      rw [Function.update_of_ne (by omega), Function.update_self]
      simp [v]
    · rw [hM₃, hM₂, hM₁, show tourLayout.nodeAddr nb x + OFF_VAL + 5 = nb + tourLayout.nodeStride * x + 11 by simp [nodeAddr, OFF_VAL]]
      rw [Function.update_self]
  have hptr1 : PtrOk cap st1 := fun u hu => by
    by_cases hux : u = x
    · subst hux; simpa [st1] using hptr u hu
    · simpa [st1, updateNode, hux] using hptr u hu
  refine runs_seq_callBody_le C.splay.pull_body (by eval_expr)
    (R := fun _ st₄ c₄ => tourLayout.NodesAt st₄.mem nb cap (tourSetVal st x v) ∧
      TreeFrame tourLayout nb cap heap mem st₄.mem ∧ c₄ ≤ C.steps.cost + 150) ?_ ?_
  · obtain ⟨o, st', c, hrun, ⟨hn, hf⟩, hc⟩ := pullBody_runs C.steps ω hN3 hptr1 hx
      ⟨hrec, by rw [C.steps_space]; omega, hF3.1, hwide⟩ (fun _ => hok hx0)
    refine ⟨o, st', c, hrun, ?_, hF3.trans hf, by omega⟩
    have : tourSetVal st x v = pull tourPayload st1 x := by simp [tourSetVal, st1, hx0]
    rw [this]; exact hn
  rintro - st₄ c₄ ⟨hn₄, hf₄, hc₄⟩
  wram_step
  · exact ⟨hn₄, hf₄⟩
  · have := C.steps_cost; simp only [TOUR_SPLICE_COST, TOUR_PAYLOAD_COST] at *; wram_cost

theorem tourInitNodeBody_runs {w nb x isOpen isMarked rootTag pos : ℕ} {p : Program}
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    (hAx : nb + 17 * x + 17 < 2 ^ w) (hw : 18 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω tourInitNodeBody
        (startState [nb, x, isOpen, isMarked, rootTag] mem pos) o st' c ∧
      (tourLayout.NodeAt st'.mem nb x
        { left := 0, right := 0, par := 0, ppar := 0, sz := 1,
          val := ⟨0 < isOpen, 0 < isMarked, rootTag⟩,
          sum := tourPayload.single x ⟨0 < isOpen, 0 < isMarked, rootTag⟩,
          tag := (), rev := false } ∧
       ∀ a, (∀ i < 17, a ≠ nb + 17 * x + i) → st'.mem a = mem a) ∧
      0 + c ≤ TOUR_SPLICE_COST := by
  have h17 : 17 * x < 2 ^ w := by omega
  unfold tourInitNodeBody; rw [startState]
  wram_step; wram_step; wram_step
  wram_step; wram_step; wram_step; wram_step; wram_step
  wram_step; wram_step; wram_step; wram_step; wram_step
  wram_step; wram_step; wram_step; wram_step; wram_step
  wram_step; wram_step; wram_step
  · dsimp only
    set b := nb + 17 * x
    have hna : tourLayout.nodeAddr nb x = b := rfl
    refine ⟨?_, fun a ha => ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
      · rw [hna, OFF_LEFT]
        simp only [Nat.add_zero]
        repeat (rw [Function.update_of_ne (by omega)])
        rw [Function.update_self]
      · rw [hna, OFF_RIGHT]
        repeat (rw [Function.update_of_ne (by omega)])
        rw [Function.update_self]
      · rw [hna, OFF_PAR]
        repeat (rw [Function.update_of_ne (by omega)])
        rw [Function.update_self]
      · rw [hna, OFF_PPAR]
        repeat (rw [Function.update_of_ne (by omega)])
        rw [Function.update_self]
      · rw [hna, OFF_SZ]
        repeat (rw [Function.update_of_ne (by omega)])
        rw [Function.update_self]; rfl
      · rw [hna, OFF_REV]
        repeat (rw [Function.update_of_ne (by omega)])
        rw [Function.update_self]; rfl
      · rw [hna, OFF_VAL]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · repeat (rw [Function.update_of_ne (by omega)])
          rw [Function.update_self]
        · repeat (rw [Function.update_of_ne (by omega)])
          rw [Function.update_self]
        · repeat (rw [Function.update_of_ne (by omega)])
          rw [Function.update_self]
        · repeat (rw [Function.update_of_ne (by omega)])
          rw [Function.update_self]; simp
        · repeat (rw [Function.update_of_ne (by omega)])
          rw [Function.update_self]; simp
        · repeat (rw [Function.update_of_ne (by omega)])
          rw [Function.update_self]
      · rw [hna, tourLayout_offSum]
        dsimp only [tourLayout, tourPayload]
        refine ⟨?_, ?_, ?_, ?_⟩
        · repeat (rw [Function.update_of_ne (by omega)])
          rw [Function.update_self]
        · repeat (rw [Function.update_of_ne (by omega)])
          rw [Function.update_self]; simp
        · repeat (rw [Function.update_of_ne (by omega)])
          rw [Function.update_self]; simp
        · repeat (rw [Function.update_of_ne (by omega)])
          rw [Function.update_self]
    · have hne : ∀ i < 17, a ≠ b + i := ha
      rw [Function.update_of_ne (hne 16 (by omega)), Function.update_of_ne (hne 15 (by omega)),
        Function.update_of_ne (hne 14 (by omega)), Function.update_of_ne (hne 13 (by omega)),
        Function.update_of_ne (hne 12 (by omega)), Function.update_of_ne (hne 11 (by omega)),
        Function.update_of_ne (hne 10 (by omega)), Function.update_of_ne (hne 9 (by omega)),
        Function.update_of_ne (hne 8 (by omega)), Function.update_of_ne (hne 7 (by omega)),
        Function.update_of_ne (hne 6 (by omega)), Function.update_of_ne (hne 5 (by omega)),
        Function.update_of_ne (hne 4 (by omega)), Function.update_of_ne (hne 3 (by omega)),
        Function.update_of_ne (hne 2 (by omega)), Function.update_of_ne (hne 1 (by omega)),
        Function.update_of_ne (by simpa using hne 0 (by omega))]
  · simp only [TOUR_SPLICE_COST]; wram_cost

/-! ## Amortized run theorems for `splayBody`, `leftmostWalk + splay`, and `descend + splay` -/

theorem auxTree_depthOf_lt_countNodes : ∀ {t : AuxTree} {x : ℕ}, x ∈ t.toList →
    t.depthOf x < t.countNodes
  | .leaf, _, hx => by simp [AuxTree.toList] at hx
  | .node id l r, x, hx => by
    by_cases hxi : x = id
    · subst hxi; simp [AuxTree.depthOf, AuxTree.countNodes]
    · rw [AuxTree.depthOf.eq_2]; simp only [hxi, ↓reduceIte, AuxTree.countNodes]
      simp only [AuxTree.toList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (hxl | hxi') | hxr
      · have h1 := auxTree_depthOf_lt_countNodes hxl; simp only [hxl, ↓reduceIte]; omega
      · exact absurd hxi' hxi
      · by_cases hxl : x ∈ l.toList
        · have h1 := auxTree_depthOf_lt_countNodes hxl; simp only [hxl, ↓reduceIte]; omega
        · have h1 := auxTree_depthOf_lt_countNodes hxr; simp only [hxl, hxr, ↓reduceIte]; omega

/-- Running `splayBody` on `x ∈ t.toList` updates `st` and `trees` via `tourSplay_preserves`
with amortized cost `≤ TOUR_SPLAY_AMORT * (Nat.log 2 (cap + 2) + 1)`. -/
theorem tourSplay_runs_amort {w nb cap heap fuel x pos : ℕ} {p : Program}
    (C : TourSplayCoreProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {pre post : List AuxTree} {t : AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (pre ++ t :: post)) (hvals : TourValsOk w cap st)
    (hx : x ∈ t.toList) (hfuel : t.depthOf x < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ t' o st' c,
      let s' := SplayState.splay tourPayload st fuel x
      Runs w p ω (splayBody C.splay.pushPath C.splay.loop)
        (startState [nb, x, fuel, heap] mem pos) o st' c ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (pre ++ t' :: post) ∧
      TourValsOk w cap s' ∧
      t' ≠ .leaf ∧ t'.rootId = x ∧ t'.toList = t.toList ∧
      (∀ u ∉ t.toList, s'.nodes u = st.nodes u) ∧
      c + TOUR_PHI_MULT * forestPhi (pre ++ t' :: post) ≤
        TOUR_PHI_MULT * forestPhi (pre ++ t :: post) + TOUR_SPLAY_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have ht_mem : t ∈ pre ++ t :: post := by simp
  have hx_cap : x ≤ cap := (hf.mem_inCap ht_mem hx).2
  have hheap' : HeapOk tourLayout w nb cap heap (2 * tourLayout.tagW + C.steps.space) mem := by
    simpa [C.space_eq] using hheap
  obtain ⟨o, st', c, hrun, ⟨hn', hfr'⟩, hc⟩ := splayBody_runs C.splay ω hnodes hf.ptrOk hx_cap
    hheap' hfuelW (tourSplayOk_of_forest hf hvals hx)
  obtain ⟨t', hinv', hne', hroot', hlist', hout', hval', hphi'⟩ := tourSplay_preserves hf hx hfuel
  have hsc := splayCost_le tourPayload_laws C.steps (hf.treesInv t ht_mem) hx hfuel
  rw [splayDepth_eq_depthOf (hf.treesInv t ht_mem) hx hfuel, C.splayRate_eq] at hsc
  refine ⟨t', o, st', c, hrun, hn', hfr', hinv', ⟨hvals.1, fun u hu => by rw [hval' u hu]; exact hvals.2 u hu⟩,
    hne', hroot', hlist', hout', ?_⟩
  have h1 : c ≤ (t.depthOf x / 2 + 1) * 9700 := le_trans (by omega) hsc
  have h2 := Nat.mul_le_mul_left TOUR_PHI_MULT hphi'
  simp only [TOUR_PHI_MULT, TOUR_SPLAY_AMORT] at h2 ⊢
  nlinarith

/-- Running `leftmostWalkBody` followed by `splayBody` on a tree `t` brings the leftmost node `m`
(`t.toList.head? = some m`) to root with `left = 0` in amortized `O(log (cap + 2))` time. -/
theorem tourFindLeftmost_cost_le {w nb cap heap fuel pos : ℕ} {p : Program}
    (C : TourSplayCoreProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {pre post : List AuxTree} {t : AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (pre ++ t :: post)) (hvals : TourValsOk w cap st)
    (hfuel : t.countNodes < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ m t' o₁ st₁ c₁ o₂ st₂ c₂,
      let s' := SplayState.splay tourPayload st fuel m
      Runs w p ω (leftmostWalkBody C.walkProc C.lazy.pushDown)
        (startState [nb, t.rootId, fuel, heap] mem pos) o₁ st₁ c₁ ∧
      o₁.value = m ∧
      Runs w p ω (splayBody C.splay.pushPath C.splay.loop)
        (startState [nb, m, fuel, heap] st₁.mem st₁.pos) o₂ st₂ c₂ ∧
      tourLayout.NodesAt st₂.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st₂.mem ∧
      TourForestInv cap s' (pre ++ t' :: post) ∧
      TourValsOk w cap s' ∧
      t' ≠ .leaf ∧ t'.rootId = m ∧ (s'.nodes m).left = 0 ∧
      t'.toList = t.toList ∧ t.toList.head? = some m ∧
      (∀ u ∉ t.toList, s'.nodes u = st.nodes u) ∧
      c₁ + c₂ + TOUR_PHI_MULT * forestPhi (pre ++ t' :: post) ≤
        TOUR_PHI_MULT * forestPhi (pre ++ t :: post) + TOUR_SPLAY_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have ht_mem : t ∈ pre ++ t :: post := by simp
  have ht_ne : t ≠ .leaf := hf.nonEmpty t ht_mem
  have hr_cap : t.rootId ≤ cap := (hf.mem_inCap ht_mem (AuxTree.rootId_mem ht_ne)).2
  have hheap' : HeapOk tourLayout w nb cap heap (2 * tourLayout.tagW + C.steps.space) mem := by
    simpa [C.space_eq] using hheap
  obtain ⟨hw_st, hm_mem, hm_head, hw_steps⟩ := tourLeftmostWalk_spec (fuel := fuel) hf ht_mem (by omega)
  set m := (leftmostWalk tourPayload st fuel t.rootId).2
  obtain ⟨o₁, st₁, c₁, hrun₁, ⟨hv₁, hn₁, hfr₁⟩, hc₁⟩ := leftmostWalkBody_runs C.lazy C.walk_body ω
    fuel t.rootId pos hnodes hf.ptrOk hr_cap hheap' hfuelW
    (tourWalkOk_of_forest hf.ptrOk hf.noRev fuel t.rootId hr_cap)
  rw [hw_st] at hn₁
  have hm_cap : m ≤ cap := (hf.mem_inCap ht_mem hm_mem).2
  have hdep_lt : t.depthOf m < fuel := by
    have := auxTree_depthOf_lt_countNodes hm_mem; omega
  have hheap₁ : HeapOk tourLayout w nb cap heap (2 * tourLayout.tagW + C.steps.space) st₁.mem :=
    ⟨hheap.rec_le, hheap'.room, hfr₁.1, hheap.wide⟩
  obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hn₂, hfr₂⟩, hc₂⟩ := splayBody_runs (pos := st₁.pos) C.splay ω hn₁ hf.ptrOk hm_cap
    hheap₁ hfuelW (tourSplayOk_of_forest hf hvals hm_mem)
  obtain ⟨t', hinv', hne', hroot', hlist', hout', hval', hphi'⟩ := tourSplay_preserves hf hm_mem hdep_lt
  -- Prove `(s'.nodes m).left = 0` because `t'.toList = t.toList` starts with `m`!
  have hm_left0 : ((SplayState.splay tourPayload st fuel m).nodes m).left = 0 := by
    have ht'_inv := hinv'.treesInv t' (by simp)
    cases ht'c : t' with
    | leaf => exact absurd ht'c hne'
    | node rid l' r' =>
      have hrid : rid = m := by simpa [ht'c, AuxTree.rootId] using hroot'
      subst hrid
      rw [ht'c] at ht'_inv
      have hl_nil : l' = .leaf := by
        cases l' with
        | leaf => rfl
        | node lid lL lR =>
          exfalso
          have hnd' := ht'_inv.nodup
          have hm_nl : m ∉ (AuxTree.node lid lL lR).toList := (AuxTree.nodup_node_unfold hnd').2.1
          have hl_ne : (AuxTree.node lid lL lR).toList ≠ [] :=
            List.ne_nil_of_mem (AuxTree.rootId_mem (by simp))
          have hhd : t'.toList.head? = (AuxTree.node lid lL lR).toList.head? := by
            rw [ht'c, AuxTree.toList, List.append_assoc, List.head?_append_of_ne_nil _ hl_ne]
          rw [hlist', hm_head] at hhd
          exact hm_nl (List.mem_of_head? hhd.symm)
      simpa [hl_nil, AuxTree.rootId] using ht'_inv.sub.2.1
  have hsc := splayCost_le tourPayload_laws C.steps (hf.treesInv t ht_mem) hm_mem hdep_lt
  rw [splayDepth_eq_depthOf (hf.treesInv t ht_mem) hm_mem hdep_lt, C.splayRate_eq] at hsc
  rw [C.pushDownCost_eq, hw_steps] at hc₁
  refine ⟨m, t', o₁, st₁, c₁, o₂, st₂, c₂, hrun₁, hv₁, hrun₂, hn₂, hfr₁.trans hfr₂, hinv',
    ⟨hvals.1, fun u hu => by rw [hval' u hu]; exact hvals.2 u hu⟩,
    hne', hroot', hm_left0, hlist', hm_head, hout', ?_⟩
  have hd_le : t.depthOf m + 1 + 1 ≤ 2 * (t.depthOf m / 2) + 3 := by omega
  have h1 : c₁ ≤ (2 * (t.depthOf m / 2) + 3) * (2390 + 80) := le_trans (by omega) (Nat.mul_le_mul_right _ hd_le)
  have h2 : c₂ ≤ (t.depthOf m / 2 + 1) * 9700 := le_trans (by omega) hsc
  have h3 := Nat.mul_le_mul_left TOUR_PHI_MULT hphi'
  simp only [TOUR_PHI_MULT, TOUR_SPLAY_AMORT] at h3 ⊢
  nlinarith

/-- Running `descendBody` followed by `splayBody` on a tree `t` whose root summary is ready
returns the **exact first** ready node `y` in `t.toList` and brings `y` to root in amortized
`O(log (cap + 2))` time. -/
theorem tourDescendSplay_cost_le {w nb cap heap fuel pos dp : ℕ} {p : Program}
    {rs : TourSum → Bool} {rv : TourVal → Bool}
    (C : TourSplayCoreProcs w p) (T : ReadyTests w p tourLayout rs rv) (hTc : T.cost = TOUR_TEST_COST)
    (hR : ReadyLaw tourPayload rs rv)
    (hdp : p.procs[dp]? = some (descendBody dp C.lazy.pushDown T.sumTest T.valTest))
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {pre post : List AuxTree} {t : AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (pre ++ t :: post)) (hvals : TourValsOk w cap st)
    (hrs : rs (st.nodes t.rootId).sum = true)
    (hfuel : t.countNodes < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ y t' o₁ st₁ c₁ o₂ st₂ c₂,
      let s' := SplayState.splay tourPayload st fuel y
      Runs w p ω (descendBody dp C.lazy.pushDown T.sumTest T.valTest)
        (startState [nb, t.rootId, fuel, heap] mem pos) o₁ st₁ c₁ ∧
      o₁.value = y ∧
      Runs w p ω (splayBody C.splay.pushPath C.splay.loop)
        (startState [nb, y, fuel, heap] st₁.mem st₁.pos) o₂ st₂ c₂ ∧
      tourLayout.NodesAt st₂.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st₂.mem ∧
      TourForestInv cap s' (pre ++ t' :: post) ∧
      TourValsOk w cap s' ∧
      t' ≠ .leaf ∧ t'.rootId = y ∧ t'.toList = t.toList ∧
      t.toList.find? (fun u => rv (st.nodes u).val) = some y ∧
      (∀ u ∉ t.toList, s'.nodes u = st.nodes u) ∧
      c₁ + c₂ + TOUR_PHI_MULT * forestPhi (pre ++ t' :: post) ≤
        TOUR_PHI_MULT * forestPhi (pre ++ t :: post) + TOUR_SPLAY_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have ht_mem : t ∈ pre ++ t :: post := by simp
  have ht_ne : t ≠ .leaf := hf.nonEmpty t ht_mem
  have hr_cap : t.rootId ≤ cap := (hf.mem_inCap ht_mem (AuxTree.rootId_mem ht_ne)).2
  have hheap' : HeapOk tourLayout w nb cap heap (2 * tourLayout.tagW + C.steps.space) mem := by
    simpa [C.space_eq] using hheap
  obtain ⟨hd_st, hy_mem, hy_find, hd_steps⟩ := tourDescend_first (fuel := fuel) hR hf ht_mem hrs (by omega)
  set y := (descend tourPayload rs rv st fuel t.rootId).2
  obtain ⟨o₁, st₁, c₁, hrun₁, ⟨hv₁, hn₁, hfr₁⟩, hc₁⟩ := descendBody_runs C.lazy T hdp ω
    fuel t.rootId pos hnodes hf.ptrOk hr_cap hheap' hfuelW
    (tourDescendOk_of_forest hf.ptrOk hf.noRev fuel t.rootId hr_cap)
  rw [hd_st] at hn₁
  have hy_cap : y ≤ cap := (hf.mem_inCap ht_mem hy_mem).2
  have hdep_lt : t.depthOf y < fuel := by
    have := auxTree_depthOf_lt_countNodes hy_mem; omega
  have hheap₁ : HeapOk tourLayout w nb cap heap (2 * tourLayout.tagW + C.steps.space) st₁.mem :=
    ⟨hheap.rec_le, hheap'.room, hfr₁.1, hheap.wide⟩
  obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hn₂, hfr₂⟩, hc₂⟩ := splayBody_runs (pos := st₁.pos) C.splay ω hn₁ hf.ptrOk hy_cap
    hheap₁ hfuelW (tourSplayOk_of_forest hf hvals hy_mem)
  obtain ⟨t', hinv', hne', hroot', hlist', hout', hval', hphi'⟩ := tourSplay_preserves hf hy_mem hdep_lt
  have hsc := splayCost_le tourPayload_laws C.steps (hf.treesInv t ht_mem) hy_mem hdep_lt
  rw [splayDepth_eq_depthOf (hf.treesInv t ht_mem) hy_mem hdep_lt, C.splayRate_eq] at hsc
  rw [C.pushDownCost_eq, hTc, TOUR_TEST_COST, hd_steps] at hc₁
  refine ⟨y, t', o₁, st₁, c₁, o₂, st₂, c₂, hrun₁, hv₁, hrun₂, hn₂, hfr₁.trans hfr₂, hinv',
    ⟨hvals.1, fun u hu => by rw [hval' u hu]; exact hvals.2 u hu⟩,
    hne', hroot', hlist', hy_find, hout', ?_⟩
  have hd_le : t.depthOf y + 1 + 1 ≤ 2 * (t.depthOf y / 2) + 3 := by omega
  have h1 : c₁ ≤ (2 * (t.depthOf y / 2) + 3) * (2390 + 2 * 20 + 120) := le_trans (by omega) (Nat.mul_le_mul_right _ hd_le)
  have h2 : c₂ ≤ (t.depthOf y / 2 + 1) * 9700 := le_trans (by omega) hsc
  have h3 := Nat.mul_le_mul_left TOUR_PHI_MULT hphi'
  simp only [TOUR_PHI_MULT, TOUR_SPLAY_AMORT] at h3 ⊢
  nlinarith

end MinCostFlow.SparseCore.Program
