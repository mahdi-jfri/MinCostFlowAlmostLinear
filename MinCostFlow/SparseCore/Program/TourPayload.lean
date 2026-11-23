module

public import MinCostFlow.LinkCut.Gen.Descend
import WordRAM.Tactic

/-!
# Splay-sequence payload for Euler-tour trees

Each node in an Euler-tour splay tree represents one live edge end and stores `TourVal`:
* `isOpen : Bool` (`true` iff the end is not a forest edge),
* `isMarked : Bool` (`true` iff the end belongs to the user-maintained marked subset), and
* `rootTag : ℕ` (`r + 1` on the unique `firstEnd[r]` node of component root `r`, else `0`).

Its segment summary `TourSum` keeps exact subtree counts `(sz, openCnt, markCnt)` (combined by
addition) and `rootTag` (combined by `max`). Because `+` and `max` are commutative, associative,
and unital, `tourPayload` satisfies `LctPayload.Laws` with trivial reversal and `Unit` tags
(`tourPayload_laws`).

We also define the 17-word `NodeLayout` (`tourLayout`), its five constant-time WordRAM payload
procedures (`tourPayloadSteps`), and the two `ReadyTests` instances for descending to the leftmost
open or marked node (`tourOpenReadyTests`, `tourMarkReadyTests`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
open MinCostFlow.LinkCut.Gen.NodeLayout

/-! ## Algebraic payload and laws -/

/-- Node value for an Euler-tour splay tree node. -/
structure TourVal where
  isOpen : Bool
  isMarked : Bool
  rootTag : ℕ
  deriving DecidableEq

/-- Segment summary for an Euler-tour splay tree subtree. -/
structure TourSum where
  sz : ℕ
  openCnt : ℕ
  markCnt : ℕ
  rootTag : ℕ
  deriving DecidableEq

/-- The commutative splay-sequence payload for Euler tours (no lazy tags, identity reversal). -/
def tourPayload : LctPayload TourVal TourSum Unit where
  empty := ⟨0, 0, 0, 0⟩
  single _ v := ⟨1, if v.isOpen then 1 else 0, if v.isMarked then 1 else 0, v.rootTag⟩
  combine a b := ⟨a.sz + b.sz, a.openCnt + b.openCnt, a.markCnt + b.markCnt, max a.rootTag b.rootTag⟩
  revVal := id
  revSum := id
  idTag := ()
  isIdTag _ := true
  compTag _ _ := ()
  actVal _ := id
  actSum _ := id
  revTag := id

theorem tourPayload_laws : tourPayload.Laws where
  combine_empty_left s := by cases s; simp [tourPayload]
  combine_empty_right s := by cases s; simp [tourPayload]
  combine_assoc a b c := by
    cases a; cases b; cases c
    simp [tourPayload, Nat.add_assoc, max_assoc]
  revVal_revVal _ := rfl
  revSum_revSum _ := rfl
  revTag_revTag _ := rfl
  revSum_empty := rfl
  revSum_single _ _ := rfl
  revSum_combine a b := by
    cases a; cases b
    simp [tourPayload, Nat.add_comm, max_comm]
  actVal_id _ := rfl
  actSum_id _ := rfl
  actVal_comp _ _ _ := rfl
  actSum_comp _ _ _ := rfl
  compTag_id_left _ := rfl
  compTag_id_right _ := rfl
  compTag_assoc _ _ _ := rfl
  actSum_empty _ := rfl
  actSum_single _ _ _ := rfl
  actSum_combine _ _ _ := rfl
  revTag_id := rfl
  revTag_comp _ _ := rfl
  revVal_actVal _ _ := rfl
  revSum_actSum _ _ := rfl
  isIdTag_id := rfl
  isIdTag_eq _ _ := rfl

/-! ## Ready tests for open and marked ends -/

def tourOpenRs (s : TourSum) : Bool := decide (0 < s.openCnt)
def tourOpenRv (v : TourVal) : Bool := v.isOpen

def tourMarkRs (s : TourSum) : Bool := decide (0 < s.markCnt)
def tourMarkRv (v : TourVal) : Bool := v.isMarked

/-- Summary counts of `listSummary tourPayload` equal the list length and filtered counts. -/
theorem tourPayload_listSummary_sz (ps : List (ℕ × TourVal)) :
    (tourPayload.listSummary ps).sz = ps.length := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    rw [LctPayload.listSummary_cons]
    change 1 + (tourPayload.listSummary rest).sz = rest.length + 1
    omega

theorem tourPayload_listSummary_openCnt (ps : List (ℕ × TourVal)) :
    (tourPayload.listSummary ps).openCnt = (ps.filter fun p => p.2.isOpen).length := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    rw [LctPayload.listSummary_cons]
    change (if p.2.isOpen then 1 else 0) + (tourPayload.listSummary rest).openCnt = _
    rw [ih, List.filter_cons]
    cases p.2.isOpen <;> (simp; try omega)

theorem tourPayload_listSummary_markCnt (ps : List (ℕ × TourVal)) :
    (tourPayload.listSummary ps).markCnt = (ps.filter fun p => p.2.isMarked).length := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    rw [LctPayload.listSummary_cons]
    change (if p.2.isMarked then 1 else 0) + (tourPayload.listSummary rest).markCnt = _
    rw [ih, List.filter_cons]
    cases p.2.isMarked <;> (simp; try omega)

theorem tourPayload_listSummary_rootTag (ps : List (ℕ × TourVal)) :
    (tourPayload.listSummary ps).rootTag = (ps.map fun p => p.2.rootTag).foldr max 0 := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    rw [LctPayload.listSummary_cons]
    change max p.2.rootTag (tourPayload.listSummary rest).rootTag = _
    rw [ih]; rfl

theorem tourOpen_readyLaw : ReadyLaw tourPayload tourOpenRs tourOpenRv := by
  intro ps
  simp only [tourOpenRs, tourOpenRv, decide_eq_true_eq, tourPayload_listSummary_openCnt,
    List.length_pos_iff_exists_mem, List.mem_filter]

theorem tourMark_readyLaw : ReadyLaw tourPayload tourMarkRs tourMarkRv := by
  intro ps
  simp only [tourMarkRs, tourMarkRv, decide_eq_true_eq, tourPayload_listSummary_markCnt,
    List.length_pos_iff_exists_mem, List.mem_filter]

/-! ## Memory layout (`nodeStride = 17`) -/

/-- 17-word node layout: 6 control words, 6 value words (`[17, 6, 1, isOpen, isMarked, rootTag]`),
4 summary words (`[sz, openCnt, markCnt, rootTag]`), and 1 unused tag word. -/
def tourLayout : NodeLayout TourVal TourSum Unit where
  valW := 6
  sumW := 4
  tagW := 1
  ValAt m a v :=
    m a = 17 ∧ m (a + 1) = 6 ∧ m (a + 2) = 1 ∧
    m (a + 3) = (if v.isOpen then 1 else 0) ∧
    m (a + 4) = (if v.isMarked then 1 else 0) ∧
    m (a + 5) = v.rootTag
  SumAt m a s :=
    m a = s.sz ∧ m (a + 1) = s.openCnt ∧ m (a + 2) = s.markCnt ∧ m (a + 3) = s.rootTag
  TagAt _ _ _ := True
  val_move m m' a b v hv hag := by
    refine ⟨(hag 0 (by omega)).trans hv.1, (hag 1 (by omega)).trans hv.2.1,
      (hag 2 (by omega)).trans hv.2.2.1, (hag 3 (by omega)).trans hv.2.2.2.1,
      (hag 4 (by omega)).trans hv.2.2.2.2.1, (hag 5 (by omega)).trans hv.2.2.2.2.2⟩
  sum_move m m' a b s hs hag := by
    refine ⟨(hag 0 (by omega)).trans hs.1, (hag 1 (by omega)).trans hs.2.1,
      (hag 2 (by omega)).trans hs.2.2.1, (hag 3 (by omega)).trans hs.2.2.2⟩
  tag_move _ _ _ _ _ _ _ := trivial
  val_hdr m a v hv := ⟨hv.1, hv.2.1, hv.2.2.1⟩
  val_three := by decide

theorem tourLayout_stride : tourLayout.nodeStride = 17 := rfl
theorem tourLayout_offSum : tourLayout.offSum = 12 := rfl
theorem tourLayout_offTag : tourLayout.offTag = 16 := rfl

/-- Representability predicate for `TourVal` and `TourSum` at word size `w`. -/
def tourOk (w : ℕ) : PayloadOk TourVal TourSum Unit where
  valOk v := v.rootTag < 2 ^ w
  sumOk s := s.sz < 2 ^ w ∧ s.openCnt < 2 ^ w ∧ s.markCnt < 2 ^ w ∧ s.rootTag < 2 ^ w
  tagOk _ := True

/-! ## WordRAM payload procedures -/

def tourRevBody : Stmt := .ret (.const 0)
def tourActBody : Stmt := .ret (.const 0)
def tourIsIdBody : Stmt := .ret (.const 1)
def tourSetIdBody : Stmt := .ret (.const 0)

/-- `pull [x, a, l, r, heap]`: recompute the 4-word summary at `a + 12 .. a + 15`. -/
def tourPullBody : Stmt :=
  .assign 8 (.const 1) ;;
  .assign 9 (.load (.bin .add (.reg 1) (.const 9))) ;;
  .assign 10 (.load (.bin .add (.reg 1) (.const 10))) ;;
  .assign 11 (.load (.bin .add (.reg 1) (.const 11))) ;;
  .cond (.reg 2)
    (.assign 8 (.bin .add (.reg 8) (.load (.bin .add (.reg 2) (.const 12)))) ;;
     .assign 9 (.bin .add (.reg 9) (.load (.bin .add (.reg 2) (.const 13)))) ;;
     .assign 10 (.bin .add (.reg 10) (.load (.bin .add (.reg 2) (.const 14)))) ;;
     .assign 12 (.load (.bin .add (.reg 2) (.const 15))) ;;
     .cond (.bin .lt (.reg 11) (.reg 12)) (.assign 11 (.reg 12)) .nop)
    .nop ;;
  .cond (.reg 3)
    (.assign 8 (.bin .add (.reg 8) (.load (.bin .add (.reg 3) (.const 12)))) ;;
     .assign 9 (.bin .add (.reg 9) (.load (.bin .add (.reg 3) (.const 13)))) ;;
     .assign 10 (.bin .add (.reg 10) (.load (.bin .add (.reg 3) (.const 14)))) ;;
     .assign 12 (.load (.bin .add (.reg 3) (.const 15))) ;;
     .cond (.bin .lt (.reg 11) (.reg 12)) (.assign 11 (.reg 12)) .nop)
    .nop ;;
  .store (.bin .add (.reg 1) (.const 12)) (.reg 8) ;;
  .store (.bin .add (.reg 1) (.const 13)) (.reg 9) ;;
  .store (.bin .add (.reg 1) (.const 14)) (.reg 10) ;;
  .store (.bin .add (.reg 1) (.const 15)) (.reg 11) ;;
  .ret (.const 0)

/-- `openSumTest [a]`: return `1` iff `mem (a + 13) > 0`. -/
def tourOpenSumTestBody : Stmt :=
  .ret (.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const 13))))

/-- `openValTest [a]`: return `1` iff `mem (a + 3) > 0`. -/
def tourOpenValTestBody : Stmt :=
  .ret (.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const 3))))

/-- `markSumTest [a]`: return `1` iff `mem (a + 14) > 0`. -/
def tourMarkSumTestBody : Stmt :=
  .ret (.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const 14))))

/-- `markValTest [a]`: return `1` iff `mem (a + 4) > 0`. -/
def tourMarkValTestBody : Stmt :=
  .ret (.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const 4))))

/-- Constant bound on the cost of any `TourPayload` procedure. -/
def TOUR_PAYLOAD_COST : ℕ := 250
def TOUR_TEST_COST : ℕ := 20

theorem tourPayload_bodies_noRand :
    tourRevBody.NoRand ∧ tourActBody.NoRand ∧ tourPullBody.NoRand ∧
    tourIsIdBody.NoRand ∧ tourSetIdBody.NoRand ∧
    tourOpenSumTestBody.NoRand ∧ tourOpenValTestBody.NoRand ∧
    tourMarkSumTestBody.NoRand ∧ tourMarkValTestBody.NoRand := by
  simp [tourRevBody, tourActBody, tourPullBody, tourIsIdBody, tourSetIdBody,
    tourOpenSumTestBody, tourOpenValTestBody, tourMarkSumTestBody, tourMarkValTestBody,
    Stmt.NoRand]

/-! ## Correctness of the payload procedures -/

theorem tourRev_meets {w : ℕ} {p : Program} {idx : ℕ} (hget : p.procs[idx]? = some tourRevBody) :
    MeetsContract w p idx (revContract tourPayload tourLayout (tourOk w) w TOUR_PAYLOAD_COST 0) := by
  intro args mem pos ω hW ⟨hpre, hz, hroom⟩
  obtain ⟨a, heap, rfl, _, _, _, _, _, _, _, _, _, _⟩ := hpre
  refine ⟨tourRevBody, hget, .returned 0, startState [a, heap] mem pos, 2,
    runs_ret_iff.mpr ⟨0, Expr.eval_const (Nat.two_pow_pos w), rfl, rfl, rfl⟩, ?_,
    by dsimp only [revContract, payloadContract, TOUR_PAYLOAD_COST]; omega⟩
  exact ⟨hz, fun _ _ _ => rfl, fun v s t hv hs ht => ⟨hv, hs, ht⟩⟩

theorem tourAct_meets {w : ℕ} {p : Program} {idx : ℕ} (hget : p.procs[idx]? = some tourActBody) :
    MeetsContract w p idx (actContract tourPayload tourLayout (tourOk w) w TOUR_PAYLOAD_COST 0) := by
  intro args mem pos ω hW ⟨hpre, hz, hroom⟩
  obtain ⟨b, a, heap, rfl, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hpre
  refine ⟨tourActBody, hget, .returned 0, startState [b, a, heap] mem pos, 2,
    runs_ret_iff.mpr ⟨0, Expr.eval_const (Nat.two_pow_pos w), rfl, rfl, rfl⟩, ?_,
    by dsimp only [actContract, payloadContract, TOUR_PAYLOAD_COST]; omega⟩
  exact ⟨hz, fun _ _ _ => rfl, fun t0 v s t _ hv hs ht => ⟨hv, hs, ht⟩⟩

theorem tourIsId_meets {w : ℕ} {p : Program} {idx : ℕ} (hget : p.procs[idx]? = some tourIsIdBody)
    (hw : 1 < 2 ^ w) :
    MeetsContract w p idx (isIdContract tourPayload tourLayout w TOUR_PAYLOAD_COST 0) := by
  intro args mem pos ω hW ⟨hpre, hz, hroom⟩
  obtain ⟨a, heap, rfl, _, _, _⟩ := hpre
  refine ⟨tourIsIdBody, hget, .returned 1, startState [a, heap] mem pos, 2,
    runs_ret_iff.mpr ⟨1, Expr.eval_const hw, rfl, rfl, rfl⟩, ?_,
    by dsimp only [isIdContract, payloadContract, TOUR_PAYLOAD_COST]; omega⟩
  exact ⟨hz, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem tourSetId_meets {w : ℕ} {p : Program} {idx : ℕ}
    (hget : p.procs[idx]? = some tourSetIdBody) :
    MeetsContract w p idx (setIdContract tourPayload tourLayout w TOUR_PAYLOAD_COST 0) := by
  intro args mem pos ω hW ⟨hpre, hz, hroom⟩
  obtain ⟨a, heap, rfl, _, _⟩ := hpre
  refine ⟨tourSetIdBody, hget, .returned 0, startState [a, heap] mem pos, 2,
    runs_ret_iff.mpr ⟨0, Expr.eval_const (Nat.two_pow_pos w), rfl, rfl, rfl⟩, ?_,
    by dsimp only [setIdContract, payloadContract, TOUR_PAYLOAD_COST]; omega⟩
  exact ⟨hz, fun _ _ _ => rfl, fun _ hv => hv, fun _ hs => hs, trivial⟩

private theorem sum_child_bounds {w x : ℕ} {v : TourVal} {sl sr : TourSum}
    (hok : (tourOk w).sumOk (tourPayload.combine sl (tourPayload.combine (tourPayload.single x v) sr))) :
    1 + sl.sz < 2 ^ w ∧
    (if v.isOpen then 1 else 0) + sl.openCnt < 2 ^ w ∧
    (if v.isMarked then 1 else 0) + sl.markCnt < 2 ^ w ∧
    1 + sl.sz + sr.sz < 2 ^ w ∧
    (if v.isOpen then 1 else 0) + sl.openCnt + sr.openCnt < 2 ^ w ∧
    (if v.isMarked then 1 else 0) + sl.markCnt + sr.markCnt < 2 ^ w ∧
    v.rootTag < 2 ^ w ∧ sl.rootTag < 2 ^ w ∧ sr.rootTag < 2 ^ w ∧
    max v.rootTag sl.rootTag < 2 ^ w ∧
    max (max v.rootTag sl.rootTag) sr.rootTag < 2 ^ w := by
  simp only [tourOk, tourPayload] at hok
  obtain ⟨h1, h2, h3, h4⟩ := hok
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega⟩

private theorem runs_cost_mono {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {Q : Outcome → State → Prop} {k₁ k₂ T : ℕ}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k₁ + c ≤ T) (hle : k₂ ≤ k₁) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k₂ + c ≤ T := by
  rcases h with ⟨o, st', c, h1, h2, h3⟩
  exact ⟨o, st', c, h1, h2, by omega⟩

theorem tourPull_meets {w : ℕ} {p : Program} {idx : ℕ} (hget : p.procs[idx]? = some tourPullBody)
    (hw : 16 ≤ 2 ^ w) :
    MeetsContract w p idx (pullContract tourPayload tourLayout (tourOk w) w TOUR_PAYLOAD_COST 0) := by
  intro args mem pos ω hW ⟨hpre, hz, hroom⟩
  obtain ⟨x, a, l, r, heap, rfl, ha_h, hl_h, hr_h, v, sl, sr, hv, hsl, hsr, hok⟩ := hpre
  have hheap_lt : heap < 2 ^ w := by
    have : heapArg [x, a, l, r, heap] = heap := rfl
    rw [this] at hroom; omega
  have ha17 : a + 17 ≤ heap := ha_h
  have hl17 : l + 17 ≤ heap := hl_h
  have hr17 : r + 17 ≤ heap := hr_h
  have hcb := sum_child_bounds (x := x) hok
  have hv_open : mem (a + 9) = if v.isOpen then 1 else 0 := by simpa [OFF_VAL] using hv.2.2.2.1
  have hv_mark : mem (a + 10) = if v.isMarked then 1 else 0 := by simpa [OFF_VAL] using hv.2.2.2.2.1
  have hv_root : mem (a + 11) = v.rootTag := by simpa [OFF_VAL] using hv.2.2.2.2.2
  have hsl_cases : (l = 0 ∧ sl = ⟨0, 0, 0, 0⟩) ∨
      (l ≠ 0 ∧ mem (l + 12) = sl.sz ∧ mem (l + 13) = sl.openCnt ∧
       mem (l + 14) = sl.markCnt ∧ mem (l + 15) = sl.rootTag) := by
    rcases hsl with ⟨rfl, rfl⟩ | ⟨hl0, hs⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨hl0, by simpa [tourLayout_offSum] using hs.1,
        by simpa [tourLayout_offSum] using hs.2.1,
        by simpa [tourLayout_offSum] using hs.2.2.1,
        by simpa [tourLayout_offSum] using hs.2.2.2⟩
  have hsr_cases : (r = 0 ∧ sr = ⟨0, 0, 0, 0⟩) ∨
      (r ≠ 0 ∧ mem (r + 12) = sr.sz ∧ mem (r + 13) = sr.openCnt ∧
       mem (r + 14) = sr.markCnt ∧ mem (r + 15) = sr.rootTag) := by
    rcases hsr with ⟨rfl, rfl⟩ | ⟨hr0, hs⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨hr0, by simpa [tourLayout_offSum] using hs.1,
        by simpa [tourLayout_offSum] using hs.2.1,
        by simpa [tourLayout_offSum] using hs.2.2.1,
        by simpa [tourLayout_offSum] using hs.2.2.2⟩
  refine ⟨tourPullBody, hget, ?_⟩
  suffices h : ∃ o st' c, Runs w p ω tourPullBody (startState [x, a, l, r, heap] mem pos) o st' c ∧
    (ZeroFrom st'.mem heap ∧ (∀ y < heap, ¬ tourLayout.PayCell a y → st'.mem y = mem y) ∧
      ∀ v' sl' sr', tourLayout.ValAt mem (a + OFF_VAL) v' →
        ChildSumAt tourPayload tourLayout mem l sl' →
        ChildSumAt tourPayload tourLayout mem r sr' →
        tourLayout.ValAt st'.mem (a + OFF_VAL) v' ∧
        tourLayout.SumAt st'.mem (a + tourLayout.offSum)
          (tourPayload.combine sl' (tourPayload.combine (tourPayload.single x v') sr')) ∧
        ∀ t, tourLayout.TagAt mem (a + tourLayout.offTag) t →
          tourLayout.TagAt st'.mem (a + tourLayout.offTag) t) ∧
    0 + c ≤ TOUR_PAYLOAD_COST by
    rcases h with ⟨o, st', c, h1, h2, h3⟩
    exact ⟨o, st', c, h1, h2, by dsimp only [pullContract, payloadContract, TOUR_PAYLOAD_COST] at h3 ⊢; omega⟩
  unfold tourPullBody
  rw [startState]
  -- Initial 4 assignments
  wram_step; wram_step; rw [hv_open]
  wram_step; rw [hv_mark]
  wram_step; rw [hv_root]
  -- Left-child conditional
  set sz1 := 1 + sl.sz
  set op1 := (if v.isOpen then 1 else 0) + sl.openCnt
  set mk1 := (if v.isMarked then 1 else 0) + sl.markCnt
  set rt1 := max v.rootTag sl.rootTag
  have hleft_cont : ∀ (regs1 : ℕ → ℕ) (c1 : ℕ),
      regs1 1 = a → regs1 3 = r → regs1 8 = sz1 → regs1 9 = op1 → regs1 10 = mk1 →
      regs1 11 = rt1 → c1 ≤ 100 →
      ∃ o st' c, Runs w p ω
        (.cond (.reg 3)
          (.assign 8 (.bin .add (.reg 8) (.load (.bin .add (.reg 3) (.const 12)))) ;;
           .assign 9 (.bin .add (.reg 9) (.load (.bin .add (.reg 3) (.const 13)))) ;;
           .assign 10 (.bin .add (.reg 10) (.load (.bin .add (.reg 3) (.const 14)))) ;;
           .assign 12 (.load (.bin .add (.reg 3) (.const 15))) ;;
           .cond (.bin .lt (.reg 11) (.reg 12)) (.assign 11 (.reg 12)) .nop)
          .nop ;;
         .store (.bin .add (.reg 1) (.const 12)) (.reg 8) ;;
         .store (.bin .add (.reg 1) (.const 13)) (.reg 9) ;;
         .store (.bin .add (.reg 1) (.const 14)) (.reg 10) ;;
         .store (.bin .add (.reg 1) (.const 15)) (.reg 11) ;;
         .ret (.const 0))
        ⟨mem, regs1, pos⟩ o st' c ∧
        (ZeroFrom st'.mem heap ∧ (∀ y < heap, ¬ tourLayout.PayCell a y → st'.mem y = mem y) ∧
          ∀ v' sl' sr', tourLayout.ValAt mem (a + OFF_VAL) v' →
            ChildSumAt tourPayload tourLayout mem l sl' →
            ChildSumAt tourPayload tourLayout mem r sr' →
            tourLayout.ValAt st'.mem (a + OFF_VAL) v' ∧
            tourLayout.SumAt st'.mem (a + tourLayout.offSum)
              (tourPayload.combine sl' (tourPayload.combine (tourPayload.single x v') sr')) ∧
            ∀ t, tourLayout.TagAt mem (a + tourLayout.offTag) t →
              tourLayout.TagAt st'.mem (a + tourLayout.offTag) t) ∧
        c1 + c ≤ TOUR_PAYLOAD_COST := by
    intro regs1 c1 hr1 hr3 hr8 hr9 hr10 hr11 hc1
    set sz2 := sz1 + sr.sz
    set op2 := op1 + sr.openCnt
    set mk2 := mk1 + sr.markCnt
    set rt2 := max rt1 sr.rootTag
    have hfin : ∀ (regs2 : ℕ → ℕ) (c2 : ℕ),
        regs2 1 = a → regs2 8 = sz2 → regs2 9 = op2 → regs2 10 = mk2 → regs2 11 = rt2 →
        c2 ≤ 180 →
        ∃ o st' c, Runs w p ω
          (.store (.bin .add (.reg 1) (.const 12)) (.reg 8) ;;
           .store (.bin .add (.reg 1) (.const 13)) (.reg 9) ;;
           .store (.bin .add (.reg 1) (.const 14)) (.reg 10) ;;
           .store (.bin .add (.reg 1) (.const 15)) (.reg 11) ;;
           .ret (.const 0))
          ⟨mem, regs2, pos⟩ o st' c ∧
          (ZeroFrom st'.mem heap ∧ (∀ y < heap, ¬ tourLayout.PayCell a y → st'.mem y = mem y) ∧
            ∀ v' sl' sr', tourLayout.ValAt mem (a + OFF_VAL) v' →
              ChildSumAt tourPayload tourLayout mem l sl' →
              ChildSumAt tourPayload tourLayout mem r sr' →
              tourLayout.ValAt st'.mem (a + OFF_VAL) v' ∧
              tourLayout.SumAt st'.mem (a + tourLayout.offSum)
                (tourPayload.combine sl' (tourPayload.combine (tourPayload.single x v') sr')) ∧
              ∀ t, tourLayout.TagAt mem (a + tourLayout.offTag) t →
                tourLayout.TagAt st'.mem (a + tourLayout.offTag) t) ∧
          c2 + c ≤ TOUR_PAYLOAD_COST := by
      intro regs2 c2 hr1' hr8' hr9' hr10' hr11' hc2
      wram_step; wram_step; wram_step; wram_step; wram_step
      · dsimp only
        refine ⟨?_, ?_, ?_⟩
        · intro y hy
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hz y hy
        · intro y hy hnot
          have hne : y ≠ a + 12 ∧ y ≠ a + 13 ∧ y ≠ a + 14 ∧ y ≠ a + 15 := by
            refine ⟨fun h => hnot ⟨by unfold OFF_VAL; omega, by rw [tourLayout_stride]; omega⟩,
              fun h => hnot ⟨by unfold OFF_VAL; omega, by rw [tourLayout_stride]; omega⟩,
              fun h => hnot ⟨by unfold OFF_VAL; omega, by rw [tourLayout_stride]; omega⟩,
              fun h => hnot ⟨by unfold OFF_VAL; omega, by rw [tourLayout_stride]; omega⟩⟩
          rw [Function.update_of_ne hne.2.2.2, Function.update_of_ne hne.2.2.1,
            Function.update_of_ne hne.2.1, Function.update_of_ne hne.1]
        · intro v' sl' sr' hv' hsl' hsr'
          have hv_eq : v' = v := by
            have h1 : (if v'.isOpen then 1 else 0) = (if v.isOpen then 1 else 0) :=
              hv'.2.2.2.1.symm.trans hv.2.2.2.1
            have h2 : (if v'.isMarked then 1 else 0) = (if v.isMarked then 1 else 0) :=
              hv'.2.2.2.2.1.symm.trans hv.2.2.2.2.1
            have h3 : v'.rootTag = v.rootTag := hv'.2.2.2.2.2.symm.trans hv.2.2.2.2.2
            cases v; cases v'
            simp only [TourVal.mk.injEq] at *
            refine ⟨?_, ?_, h3⟩
            · revert h1; cases ‹Bool› <;> cases ‹Bool› <;> simp
            · revert h2; cases ‹Bool› <;> cases ‹Bool› <;> simp
          have hsl_eq : sl' = sl := by
            rcases hsl with ⟨rfl, rfl⟩ | ⟨hl0, hs1⟩ <;> rcases hsl' with ⟨h0, rfl⟩ | ⟨hl0', hs2⟩
            · rfl
            · exact absurd rfl hl0'
            · exact absurd h0 hl0
            · cases sl; cases sl'
              simp only [TourSum.mk.injEq]
              exact ⟨hs2.1.symm.trans hs1.1, hs2.2.1.symm.trans hs1.2.1,
                hs2.2.2.1.symm.trans hs1.2.2.1, hs2.2.2.2.symm.trans hs1.2.2.2⟩
          have hsr_eq : sr' = sr := by
            rcases hsr with ⟨rfl, rfl⟩ | ⟨hr0, hs1⟩ <;> rcases hsr' with ⟨h0, rfl⟩ | ⟨hr0', hs2⟩
            · rfl
            · exact absurd rfl hr0'
            · exact absurd h0 hr0
            · cases sr; cases sr'
              simp only [TourSum.mk.injEq]
              exact ⟨hs2.1.symm.trans hs1.1, hs2.2.1.symm.trans hs1.2.1,
                hs2.2.2.1.symm.trans hs1.2.2.1, hs2.2.2.2.symm.trans hs1.2.2.2⟩
          subst hv_eq; subst hsl_eq; subst hsr_eq
          refine ⟨tourLayout.val_congr _ _ _ _ hv fun i hi => ?_, ?_, fun _ _ => trivial⟩
          · dsimp only [tourLayout] at hi
            rw [Function.update_of_ne (by unfold OFF_VAL; omega),
              Function.update_of_ne (by unfold OFF_VAL; omega),
              Function.update_of_ne (by unfold OFF_VAL; omega),
              Function.update_of_ne (by unfold OFF_VAL; omega)]
          · rw [tourLayout_offSum]
            dsimp only [tourLayout, tourPayload]
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_self]
              simp only [sz2, sz1]; omega
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_self]
              simp only [op2, op1]; omega
            · rw [Function.update_of_ne (by omega), Function.update_self]
              simp only [mk2, mk1]; omega
            · rw [Function.update_self]
              simp only [rt2, rt1]; omega
      · simp only [TOUR_PAYLOAD_COST]; wram_cost
    refine runs_seq_cond_le (Expr.eval_reg_of_eq hr3) (fun hr0 => ?_) (fun hr0 => ?_)
    · rcases hsr_cases with ⟨rfl, _⟩ | ⟨_, hr12, hr13, hr14, hr15⟩
      · exact absurd rfl hr0
      · have hrb : regs1 3 + 12 < 2 ^ w ∧ regs1 3 + 13 < 2 ^ w ∧ regs1 3 + 14 < 2 ^ w ∧
            regs1 3 + 15 < 2 ^ w ∧ regs1 8 + mem (regs1 3 + 12) < 2 ^ w ∧
            regs1 9 + mem (regs1 3 + 13) < 2 ^ w ∧ regs1 10 + mem (regs1 3 + 14) < 2 ^ w := by
          rw [hr3, hr8, hr9, hr10, hr12, hr13, hr14]; omega
        wram_step; wram_step; rw [hr12]
        wram_step; wram_step; try rw [hr3]; rw [hr13]
        wram_step; wram_step; try rw [hr3]; rw [hr14]
        wram_step; wram_step; try rw [hr3]; rw [hr15]
        refine runs_seq_cond_le (by eval_expr) (fun hlt => ?_) (fun hlt => ?_)
        · have hlt' : rt1 < sr.rootTag := by by_contra h; simp [h] at hlt
          wram_step
          exact runs_cost_mono
            (hfin _ (c1 + 70) (by simp [hr1]) (by simp [sz2]) (by simp [hr9, op2])
              (by simp [hr10, mk2]) (by simp [rt2, Nat.max_eq_right (Nat.le_of_lt hlt')]) (by omega))
            (by wram_cost)
        · have hge : sr.rootTag ≤ rt1 := by by_contra h; simp [show rt1 < sr.rootTag by omega] at hlt
          refine runs_seq_nop_le ?_
          exact runs_cost_mono
            (hfin _ (c1 + 70) (by simp [hr1]) (by simp [sz2]) (by simp [hr9, op2])
              (by simp [hr10, mk2]) (by simp [hr11, rt2, Nat.max_eq_left hge]) (by omega))
            (by wram_cost)
    · rcases hsr_cases with ⟨_, rfl⟩ | ⟨hrne, _⟩
      · refine runs_seq_nop_le ?_
        exact runs_cost_mono
          (hfin _ (c1 + 10) hr1 (by simp [hr8, sz2]) (by simp [hr9, op2])
            (by simp [hr10, mk2]) (by simp [hr11, rt2]) (by omega))
          (by wram_cost)
      · exact absurd hr0 hrne
  refine runs_seq_cond_le (by eval_expr) (fun hl0 => ?_) (fun hl0 => ?_)
  · rcases hsl_cases with ⟨rfl, _⟩ | ⟨_, hl12, hl13, hl14, hl15⟩
    · exact absurd rfl hl0
    · wram_step; wram_step; rw [hl12]
      wram_step; wram_step; rw [hl13]
      wram_step; wram_step; rw [hl14]
      wram_step; wram_step; rw [hl15]
      refine runs_seq_cond_le (by eval_expr) (fun hlt => ?_) (fun hlt => ?_)
      · have hlt' : v.rootTag < sl.rootTag := by by_contra h; simp [h] at hlt
        wram_step
        exact runs_cost_mono
          (hleft_cont _ 95 (by simp) (by simp) (by simp [sz1])
            (by simp [op1]) (by simp [mk1]) (by simp [rt1, Nat.max_eq_right (Nat.le_of_lt hlt')]) (by omega))
          (by wram_cost)
      · have hge : sl.rootTag ≤ v.rootTag := by by_contra h; simp [show v.rootTag < sl.rootTag by omega] at hlt
        refine runs_seq_nop_le ?_
        exact runs_cost_mono
          (hleft_cont _ 95 (by simp) (by simp) (by simp [sz1])
            (by simp [op1]) (by simp [mk1]) (by simp [rt1, Nat.max_eq_left hge]) (by omega))
          (by wram_cost)
  · rcases hsl_cases with ⟨_, rfl⟩ | ⟨hlne, _⟩
    · refine runs_seq_nop_le ?_
      exact runs_cost_mono
        (hleft_cont _ 40 (by simp) (by simp) (by simp [sz1])
          (by simp [op1]) (by simp [mk1]) (by simp [rt1]) (by omega))
        (by wram_cost)
    · exact absurd hl0 hlne

/-- `PayloadSteps` instance for `tourPayload` and `tourLayout`. -/
def tourPayloadSteps {w : ℕ} {p : Program} {rIdx aIdx pIdx iIdx sIdx : ℕ}
    (hw : 16 ≤ 2 ^ w)
    (hr : p.procs[rIdx]? = some tourRevBody)
    (ha : p.procs[aIdx]? = some tourActBody)
    (hp : p.procs[pIdx]? = some tourPullBody)
    (hi : p.procs[iIdx]? = some tourIsIdBody)
    (hs : p.procs[sIdx]? = some tourSetIdBody) :
    PayloadSteps w p tourPayload tourLayout (tourOk w) where
  rev := rIdx
  act := aIdx
  pull := pIdx
  isId := iIdx
  setId := sIdx
  cost := TOUR_PAYLOAD_COST
  space := 0
  rev_ok := tourRev_meets hr
  act_ok := tourAct_meets ha
  pull_ok := tourPull_meets hp hw
  isId_ok := tourIsId_meets hi (by omega)
  setId_ok := tourSetId_meets hs

/-! ## Correctness of the `ReadyTests` procedures -/

theorem tourOpenSumTest_meets {w : ℕ} {p : Program} {idx : ℕ} (hw : 16 ≤ 2 ^ w)
    (hget : p.procs[idx]? = some tourOpenSumTestBody) :
    MeetsContract w p idx (sumTestContract tourLayout tourOpenRs w TOUR_TEST_COST) := by
  intro args mem pos ω hW hpre
  obtain ⟨a, v, s, rfl, ha17, _, hs⟩ := hpre
  have h13 : a + 13 < 2 ^ w := by rw [tourLayout_stride] at ha17; omega
  have hm : mem (a + 13) = s.openCnt := by simpa [tourLayout_offSum] using hs.2.1
  have hev : (Expr.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const 13)))).eval w
      (startState [a] mem pos) = some (if 0 < mem (a + 13) then 1 else 0) := by
    rw [startState]; eval_expr
  rw [hm] at hev
  refine ⟨tourOpenSumTestBody, hget, .returned _, startState [a] mem pos, _,
    runs_ret_iff.mpr ⟨_, hev, rfl, rfl, rfl⟩, ⟨rfl, fun s' hs' => ?_⟩,
    by dsimp only [sumTestContract, TOUR_TEST_COST, Expr.size]; omega⟩
  have heq : s'.openCnt = s.openCnt := hs'.2.1.symm.trans hs.2.1
  simp [Outcome.value, tourOpenRs, heq]

theorem tourOpenValTest_meets {w : ℕ} {p : Program} {idx : ℕ} (hw : 16 ≤ 2 ^ w)
    (hget : p.procs[idx]? = some tourOpenValTestBody) :
    MeetsContract w p idx (valTestContract tourLayout tourOpenRv w TOUR_TEST_COST) := by
  intro args mem pos ω hW hpre
  obtain ⟨a, v, rfl, ha6, hv⟩ := hpre
  have h3 : a + 3 < 2 ^ w := by simp [tourLayout] at ha6; omega
  have hm : mem (a + 3) = if v.isOpen then 1 else 0 := hv.2.2.2.1
  have hev : (Expr.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const 3)))).eval w
      (startState [a] mem pos) = some (if 0 < mem (a + 3) then 1 else 0) := by
    rw [startState]; eval_expr
  rw [hm] at hev
  refine ⟨tourOpenValTestBody, hget, .returned _, startState [a] mem pos, _,
    runs_ret_iff.mpr ⟨_, hev, rfl, rfl, rfl⟩, ⟨rfl, fun v' hv' => ?_⟩,
    by dsimp only [valTestContract, TOUR_TEST_COST, Expr.size]; omega⟩
  have h1 : (if v'.isOpen then 1 else 0) = (if v.isOpen then 1 else 0) :=
    hv'.2.2.2.1.symm.trans hv.2.2.2.1
  cases hv1 : v.isOpen <;> cases hv2 : v'.isOpen <;> simp_all [Outcome.value, tourOpenRv]

theorem tourMarkSumTest_meets {w : ℕ} {p : Program} {idx : ℕ} (hw : 16 ≤ 2 ^ w)
    (hget : p.procs[idx]? = some tourMarkSumTestBody) :
    MeetsContract w p idx (sumTestContract tourLayout tourMarkRs w TOUR_TEST_COST) := by
  intro args mem pos ω hW hpre
  obtain ⟨a, v, s, rfl, ha17, _, hs⟩ := hpre
  have h14 : a + 14 < 2 ^ w := by rw [tourLayout_stride] at ha17; omega
  have hm : mem (a + 14) = s.markCnt := by simpa [tourLayout_offSum] using hs.2.2.1
  have hev : (Expr.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const 14)))).eval w
      (startState [a] mem pos) = some (if 0 < mem (a + 14) then 1 else 0) := by
    rw [startState]; eval_expr
  rw [hm] at hev
  refine ⟨tourMarkSumTestBody, hget, .returned _, startState [a] mem pos, _,
    runs_ret_iff.mpr ⟨_, hev, rfl, rfl, rfl⟩, ⟨rfl, fun s' hs' => ?_⟩,
    by dsimp only [sumTestContract, TOUR_TEST_COST, Expr.size]; omega⟩
  have heq : s'.markCnt = s.markCnt := hs'.2.2.1.symm.trans hs.2.2.1
  simp [Outcome.value, tourMarkRs, heq]

theorem tourMarkValTest_meets {w : ℕ} {p : Program} {idx : ℕ} (hw : 16 ≤ 2 ^ w)
    (hget : p.procs[idx]? = some tourMarkValTestBody) :
    MeetsContract w p idx (valTestContract tourLayout tourMarkRv w TOUR_TEST_COST) := by
  intro args mem pos ω hW hpre
  obtain ⟨a, v, rfl, ha6, hv⟩ := hpre
  have h4 : a + 4 < 2 ^ w := by simp [tourLayout] at ha6; omega
  have hm : mem (a + 4) = if v.isMarked then 1 else 0 := hv.2.2.2.2.1
  have hev : (Expr.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const 4)))).eval w
      (startState [a] mem pos) = some (if 0 < mem (a + 4) then 1 else 0) := by
    rw [startState]; eval_expr
  rw [hm] at hev
  refine ⟨tourMarkValTestBody, hget, .returned _, startState [a] mem pos, _,
    runs_ret_iff.mpr ⟨_, hev, rfl, rfl, rfl⟩, ⟨rfl, fun v' hv' => ?_⟩,
    by dsimp only [valTestContract, TOUR_TEST_COST, Expr.size]; omega⟩
  have h1 : (if v'.isMarked then 1 else 0) = (if v.isMarked then 1 else 0) :=
    hv'.2.2.2.2.1.symm.trans hv.2.2.2.2.1
  cases hv1 : v.isMarked <;> cases hv2 : v'.isMarked <;> simp_all [Outcome.value, tourMarkRv]

def tourOpenReadyTests {w : ℕ} {p : Program} {sIdx vIdx : ℕ} (hw : 16 ≤ 2 ^ w)
    (hs : p.procs[sIdx]? = some tourOpenSumTestBody)
    (hv : p.procs[vIdx]? = some tourOpenValTestBody) :
    ReadyTests w p tourLayout tourOpenRs tourOpenRv where
  sumTest := sIdx
  valTest := vIdx
  cost := TOUR_TEST_COST
  sum_ok := tourOpenSumTest_meets hw hs
  val_ok := tourOpenValTest_meets hw hv

def tourMarkReadyTests {w : ℕ} {p : Program} {sIdx vIdx : ℕ} (hw : 16 ≤ 2 ^ w)
    (hs : p.procs[sIdx]? = some tourMarkSumTestBody)
    (hv : p.procs[vIdx]? = some tourMarkValTestBody) :
    ReadyTests w p tourLayout tourMarkRs tourMarkRv where
  sumTest := sIdx
  valTest := vIdx
  cost := TOUR_TEST_COST
  sum_ok := tourMarkSumTest_meets hw hs
  val_ok := tourMarkValTest_meets hw hv

end MinCostFlow.SparseCore.Program
