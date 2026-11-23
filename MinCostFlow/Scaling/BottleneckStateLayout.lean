module

public import MinCostFlow.Scaling.BottleneckSearch
public import MinCostFlow.Scaling.SolverOutputLayout
import WordRAM.Memory
public import WordRAM.Entry

/-!
# Stored states of the bottleneck binary search

Each immutable state uses five words: the interval's lower and upper
endpoints, a best-result flag, its threshold, and its unsigned-flow pointer.
A zero flag represents no successful test. A nonzero flag retains the
exact integral flow of the last successful threshold test.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The five header words and the optional referenced best-flow array. -/
def BottleneckStateAt {J : Circulation} (mem : ℕ → ℕ) (base : ℕ) (s : BottleneckState J) : Prop :=
  mem base=s.lower ∧ mem (base+1)=s.upper ∧
    match s.best with
    | none => mem (base+2)=0
    | some (threshold,flow) => mem (base+2)=1 ∧ mem (base+3)=threshold ∧
        J.readSolverFlow mem (mem (base+4))=flow

/-- A fresh five-word header represents a state with no best result. -/
theorem bottleneckStateAt_of_header_none {J : Circulation} {mem : ℕ → ℕ}
    {base lower upper unusedThreshold unusedPtr : ℕ}
    (hat : ListAt mem base [lower,upper,0,unusedThreshold,unusedPtr]) :
    BottleneckStateAt mem base (⟨lower,upper,none⟩ : BottleneckState J) := by
  exact ⟨hat 0 (by change 0<5; decide),hat 1 (by change 1<5; decide),hat 2 (by change 2<5; decide)⟩

/-- A fresh header and its exact referenced flow represent a successful
search state, with no further correctness condition on that state. -/
theorem bottleneckStateAt_of_header_some {J : Circulation} {mem : ℕ → ℕ}
    {base lower upper threshold ptr : ℕ} {flow : Fin J.m → ℤ}
    (hat : ListAt mem base [lower,upper,1,threshold,ptr])
    (hread : J.readSolverFlow mem ptr=flow) :
    BottleneckStateAt mem base (⟨lower,upper,some (threshold,flow)⟩ : BottleneckState J) := by
  refine ⟨hat 0 (by change 0<5; decide),hat 1 (by change 1<5; decide),
    hat 2 (by change 2<5; decide),hat 3 (by change 3<5; decide),?_⟩
  have hp : mem (base+4)=ptr := hat 4 (by change 4<5; decide)
  rw [hp]
  exact hread

/-- Initial search state has the full candidate interval and no best flow. -/
theorem bottleneckStateAt_initial (J : Circulation) :
    BottleneckStateAt (initMem [0,J.m,0,0,0]) 0
      (⟨0,J.m,none⟩ : BottleneckState J) := by
  exact ⟨rfl,rfl,rfl⟩

/-- A stored successful state exposes the exact unsigned best-flow table. -/
theorem BottleneckStateAt.best_table {J : Circulation} {mem : ℕ → ℕ} {base : ℕ}
    {s : BottleneckState J} (hat : BottleneckStateAt mem base s)
    {threshold : ℕ} {flow : Fin J.m → ℤ} (hbest : s.best=some (threshold,flow)) :
    mem (base+2)=1 ∧ mem (base+3)=threshold ∧
      ListAt mem (mem (base+4)) (List.ofFn (fun e => (flow e).toNat)) := by
  obtain ⟨_,_,h⟩ := hat
  rw [hbest] at h
  exact ⟨h.1,h.2.1,solverOutput_listAt J h.2.2⟩

/-- Extending fresh memory preserves a state whose header and referenced
flow both lie below the preserved prefix. -/
theorem BottleneckStateAt.of_agree_below {J : Circulation} {mem mem' : ℕ → ℕ}
    {base bound : ℕ} {s : BottleneckState J} (hat : BottleneckStateAt mem base s)
    (hheader : base+5 ≤ bound)
    (hflow : ∀ threshold flow,s.best=some (threshold,flow) → mem (base+4)+J.m ≤ bound)
    (hagree : ∀ x<bound,mem' x=mem x) : BottleneckStateAt mem' base s := by
  obtain ⟨hl,hu,hbest⟩ := hat
  refine ⟨(hagree base (by omega)).trans hl,(hagree (base+1) (by omega)).trans hu,?_⟩
  cases heq : s.best with
  | none =>
    rw [heq] at hbest
    exact (hagree (base+2) (by omega)).trans hbest
  | some pair =>
    obtain ⟨threshold,flow⟩ := pair
    rw [heq] at hbest
    obtain ⟨hflag,hthreshold,hread⟩ := hbest
    refine ⟨(hagree (base+2) (by omega)).trans hflag,
      (hagree (base+3) (by omega)).trans hthreshold,?_⟩
    rw [hagree (base+4) (by omega)]
    have hb := hflow threshold flow heq
    funext e
    have hr := congrFun hread e
    change (mem' (mem (base+4)+e.val) : ℤ)=flow e
    change (mem (mem (base+4)+e.val) : ℤ)=flow e at hr
    rw [hagree (mem (base+4)+e.val) (by have hi := e.isLt; omega)]
    exact hr

/-- Every state with no best flow has an explicit five-word representation. -/
theorem exists_bottleneckStateAt_none (J : Circulation) (lower upper : ℕ) :
    ∃ mem,BottleneckStateAt mem 0 (⟨lower,upper,none⟩ : BottleneckState J) := by
  exact ⟨initMem [lower,upper,0,0,0],rfl,rfl,rfl⟩

/-- Every state retaining a nonnegative integral flow has a concrete header
and contiguous unsigned array, so the representation imposes no algorithmic
correctness hypothesis. -/
theorem exists_bottleneckStateAt_some (J : Circulation) (lower upper threshold : ℕ)
    (flow : Fin J.m → ℤ) (hf : ∀ e,0≤flow e) :
    ∃ mem,BottleneckStateAt mem 0 (⟨lower,upper,some (threshold,flow)⟩ : BottleneckState J) := by
  let words := [lower,upper,1,threshold,5]++List.ofFn (fun e => (flow e).toNat)
  have hstored := listAt_append.mp (listAt_initMem words)
  have hheader := hstored.1
  have hflow : ListAt (initMem words) 5 (List.ofFn (fun e => (flow e).toNat)) := by
    simpa only [List.length_cons,List.length_nil,Nat.zero_add] using hstored.2
  refine ⟨initMem words,?_,?_,?_,?_,?_⟩
  · exact hheader 0 (by change 0<5; decide)
  · exact hheader 1 (by change 1<5; decide)
  · exact hheader 2 (by change 2<5; decide)
  · exact hheader 3 (by change 3<5; decide)
  · have hptr : initMem words (0+4)=5 := hheader 4 (by change 4<5; decide)
    rw [hptr]
    funext e
    have h := hflow e.val (by simpa only [List.length_ofFn] using e.isLt)
    rw [List.getElem_ofFn] at h
    change ((initMem words (5+e.val) : ℕ) : ℤ)=flow e
    rw [h]
    exact Int.toNat_of_nonneg (hf e)

end MinCostFlow.Scaling.Machine
