module

public import MinCostFlow.MinRatio.DetectEmit
public import MinCostFlow.MinRatio.DetectLoopInvariant
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Writing Detect reports in reserved memory

Definition 4.5 (page 14) returns a contiguous list of detected edges.
The search and reset calls in the proof of Theorem 5.1 (pages 29–30)
can allocate memory while the list is being written. Reserve the
answer block below that workspace. These contracts verify the same
append and header procedures for that placement.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Append to a reserved report. The result is the next list cursor. -/
def detectEmitReservedContract (w report heap : ℕ) (written : List ℕ) : Contract where
  pre args mem := ∃ inv name cursor, args = [inv, name, cursor] ∧
    cursor = report + written.length ∧ inv + name < cursor ∧ cursor < heap ∧
    heap < 2 ^ w ∧ mem (inv + name) < 2 ^ w ∧ ListAt mem report written ∧ ZeroFrom mem heap
  post args mem ret mem' :=
    ret = args.getD 2 0 + 1 ∧
    ListAt mem' report (written ++ [mem (args.getD 0 0 + args.getD 1 0)]) ∧
    (∀ x, x ≠ args.getD 2 0 → mem' x = mem x) ∧ ZeroFrom mem' heap
  cost _ _ := 12

/-- Write the header below the true heap and return the answer's end. -/
def detectFinishReservedContract (w heap : ℕ) (reported : List ℕ) : Contract where
  pre args mem := ∃ a, args = [a, reported.length] ∧ a + 1 + reported.length ≤ heap ∧
    heap < 2 ^ w ∧ reported.Nodup ∧ ListAt mem (a + 1) reported ∧ ZeroFrom mem heap
  post args mem ret mem' :=
    ret = args.getD 0 0 + 1 + reported.length ∧
    DetectAt mem' (args.getD 0 0) reported.toFinset ∧
    (∀ x, x ≠ args.getD 0 0 → mem' x = mem x) ∧ ZeroFrom mem' heap
  cost _ _ := 10

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine

/-- One append writes only its cursor cell, even with workspace above it. -/
theorem detectEmitReserved_meetsContract {w entry report heap : ℕ} {p : Program}
    (written : List ℕ) (hp : p.HasAt entry [detectEmitBody]) :
    MeetsContract w p entry (detectEmitReservedContract w report heap written) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨inv, name, cursor, rfl, hcursor, hname, hbound, hheap, hval, hlist, hz⟩ := hpre
  have haddr : inv + name < 2 ^ w := by omega
  have hroom : cursor + 1 < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold detectEmitBody
  refine runs_seq_store_le (x := cursor) (v := mem (inv + name)) (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (v := cursor + 1) (by eval_expr) ?_ ?_
  · have hframe : ∀ x ≠ cursor,
        Function.update mem cursor (mem (inv + name)) x = mem x :=
      fun x hx => Function.update_of_ne hx _ _
    refine ⟨rfl, ?_, hframe, fun x hx => (hframe x (by omega)).trans (hz x hx)⟩
    rw [hcursor]
    exact hlist.snoc _
  · change 11 ≤ 12
    decide

/-- Writing the count leaves any later allocations intact. -/
theorem detectFinishReserved_meetsContract {w entry heap : ℕ} {p : Program}
    (reported : List ℕ) (hp : p.HasAt entry [detectFinishBody]) :
    MeetsContract w p entry (detectFinishReservedContract w heap reported) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, rfl, hbound, hheap, hnd, hlist, hz⟩ := hpre
  have hword : 1 < 2 ^ w := by omega
  have hret : a + 1 + reported.length < 2 ^ w := by omega
  apply runs_start_le
  unfold detectFinishBody
  wram_run
  · have hframe : ∀ x ≠ a, Function.update mem a reported.length x = mem x :=
      fun x hx => Function.update_of_ne hx _ _
    refine ⟨rfl, ⟨reported, hnd, rfl, ?_, ?_⟩,
      hframe, fun x hx => (hframe x (by omega)).trans (hz x hx)⟩
    · change Function.update mem a reported.length a = reported.length
      exact Function.update_self _ _ _
    · intro i hi
      change Function.update mem a reported.length (a + 1 + i) = reported[i]
      exact (hframe _ (by omega)).trans (hlist i hi)
  · simp only [detectFinishReservedContract]
    wram_cost

/-- Write the report header while retaining the heap returned by the
search and reset operations. -/
def detectFinishKeepHeapBody (finish : ℕ) : Stmt :=
  .call 3 finish [.reg 0, .reg 1] ;;
  .ret (.reg 2)

/-- The reserved answer is finalized and the active heap is returned. -/
@[expose] def detectFinishKeepHeapContract (w heap : ℕ) (reported : List ℕ) : Contract where
  pre args mem := ∃ base, args = [base, reported.length, heap] ∧
    (detectFinishReservedContract w heap reported).pre [base, reported.length] mem
  post args mem ret mem' := ret = heap ∧
    (detectFinishReservedContract w heap reported).post [args.getD 0 0, reported.length]
      mem (args.getD 0 0 + 1 + reported.length) mem'
  cost _ _ := 16

/-- Header finalization and heap return use no random statements. -/
theorem detectFinishKeepHeapBody_noRand (finish : ℕ) :
    (detectFinishKeepHeapBody finish).NoRand := by
  simp [detectFinishKeepHeapBody, Stmt.NoRand]

/-- The header call preserves the live tree workspace by returning the
current heap rather than the end of the report. -/
theorem detectFinishKeepHeap_meetsContract {w entry finish heap : ℕ} {p : Program}
    (reported : List ℕ) (hp : p.HasAt entry [detectFinishKeepHeapBody finish])
    (hf : MeetsContract w p finish (detectFinishReservedContract w heap reported)) :
    MeetsContract w p entry (detectFinishKeepHeapContract w heap reported) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base, rfl, hfinish⟩ := hpre
  have hb := hwords base (by simp)
  have hn := hwords reported.length (by simp)
  have hh := hwords heap (by simp)
  apply runs_start_le
  unfold detectFinishKeepHeapBody
  refine runs_seq_call_le hf (vs := [base, reported.length]) (by eval_expr)
    (by wram_words) hfinish ?_
  intro answerEnd out pos' hpost
  have hend : answerEnd = base + 1 + reported.length := hpost.1
  refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
  · exact ⟨rfl, hend ▸ hpost⟩
  · simp [detectFinishKeepHeapContract, detectFinishReservedContract, argsSize, Expr.size]

/-- Reserve a header and one cell per possible reported edge by
advancing the heap over an already zero region. -/
def detectReserveBody : Stmt :=
  .ret (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 1))

/-- The reserve occupies the interval beginning at the incoming heap. -/
def detectReserveContract (w : ℕ) : Contract where
  pre args mem := ∃ base capacity, args = [base, capacity] ∧
    base + 1 + capacity < 2 ^ w ∧ ZeroFrom mem base
  post args mem ret mem' :=
    ret = args.getD 0 0 + 1 + args.getD 1 0 ∧ mem' = mem ∧
    ZeroFrom mem' ret
  cost _ _ := 6

/-- Reserving the report is deterministic and takes constant time,
including when the graph has no live edges. -/
theorem detectReserve_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.HasAt entry [detectReserveBody]) :
    MeetsContract w p entry (detectReserveContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base, capacity, rfl, hroom, hz⟩ := hpre
  have hb := hwords base (by simp)
  have hc := hwords capacity (by simp)
  have hone : 1 < 2 ^ w := by
    have hbase : base + 1 + capacity ≥ 1 := by omega
    exact hbase.trans_lt hroom
  have hnext : base + 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold detectReserveBody
  refine runs_ret_le (v := base + 1 + capacity) (by eval_expr) ?_ ?_
  · refine ⟨rfl, rfl, ?_⟩
    intro x hx
    change base + 1 + capacity ≤ x at hx
    exact hz x (by omega)
  · simp [detectReserveContract, Expr.size]

/-- Advancing the heap contains no random statements. -/
theorem detectReserveBody_noRand : detectReserveBody.NoRand := by
  simp [detectReserveBody, Stmt.NoRand]

/-- Each fresh report fits in a reserve with one slot per live edge.
The reserve starts at the first list cell after the header. -/
theorem detectReserved_cursor_lt {cfg : Alg2Config} (s : Alg2State cfg)
    {reported : List ℕ} {edge report heap : ℕ}
    (hnd : reported.Nodup) (hsub : reported.toFinset ⊆ (algorithm2_detect cfg s).1)
    (he : edge ∈ (algorithm2_detect cfg s).1 \ reported.toFinset)
    (hreserve : report + s.extG.E.card ≤ heap) : report + reported.length < heap := by
  obtain ⟨hready, hnew⟩ := Finset.mem_sdiff.mp he
  have hstrict : reported.toFinset ⊂ (algorithm2_detect cfg s).1 :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hnew (heq ▸ hready)⟩
  have hcard := Finset.card_lt_card hstrict
  rw [List.toFinset_card_of_nodup hnd] at hcard
  have hle : (algorithm2_detect cfg s).1.card ≤ s.extG.E.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

/-- The reserved header write gives the IPM postcondition when the
reporting search is exhausted. -/
theorem detectFinishReserved_of_exhausted {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    {G : MGraph} {m handle base heap ret : ℕ} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ}
    {s : (algorithm2_dsWithFailureWith cfg κ).State} {mem mem' : ℕ → ℕ} {reported : List ℕ}
    (hfit : MinRatioStateFits (algorithm2_dsWithFailureWith cfg κ) G F.fmt.limbBits F.limbs F.fmt.precision s)
    (hε : 0 < cfg.ε) (hsub : reported.toFinset ⊆ (algorithm2_detect cfg s).1)
    (hstop : ∀ e ∈ s.extG.E, ¬ cfg.ε ≤ s.extℓ e * resetReported s.detectAccum reported.toFinset e)
    (hout : (detectFinishReservedContract w heap reported).post [base, reported.length] mem ret mem') :
    (minRatioMachineContract F (algorithm2_dsWithFailureWith cfg κ) G m κ α rate allocation).post
      2 s [handle, base] mem (algorithm2_detect cfg s).2 mem' ∧
    resetReported s.detectAccum reported.toFinset = (algorithm2_detect cfg s).2.detectAccum := by
  obtain ⟨heq, hreset⟩ := detect_exhausted s hε hsub hstop
  have hreport : DetectAt mem' base reported.toFinset := hout.2.1
  rw [heq] at hreport
  exact ⟨⟨rfl, hreport, hfit⟩, hreset⟩

/-- Exhaustion and the live-heap return give both the IPM Detect
postcondition and the heap pointer for the caller's next operation. -/
theorem detectFinishKeepHeap_of_exhausted {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    {G : MGraph} {m handle base heap ret : ℕ} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ}
    {s : (algorithm2_dsWithFailureWith cfg κ).State} {mem out : ℕ → ℕ} {reported : List ℕ}
    (hfit : MinRatioStateFits (algorithm2_dsWithFailureWith cfg κ) G F.fmt.limbBits F.limbs F.fmt.precision s)
    (hε : 0 < cfg.ε) (hsub : reported.toFinset ⊆ (algorithm2_detect cfg s).1)
    (hstop : ∀ e ∈ s.extG.E, ¬ cfg.ε ≤ s.extℓ e * resetReported s.detectAccum reported.toFinset e)
    (hp : (detectFinishKeepHeapContract w heap reported).post [base, reported.length, heap] mem ret out) :
    ret = heap ∧
    (minRatioMachineContract F (algorithm2_dsWithFailureWith cfg κ) G m κ α rate allocation).post
      2 s [handle, base] mem (algorithm2_detect cfg s).2 out ∧
    resetReported s.detectAccum reported.toFinset = (algorithm2_detect cfg s).2.detectAccum := by
  exact ⟨hp.1, detectFinishReserved_of_exhausted F cfg hfit hε hsub hstop hp.2⟩

end MinCostFlow.MinRatio
