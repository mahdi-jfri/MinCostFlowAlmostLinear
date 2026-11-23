module

public import MinCostFlow.Scaling.InputLayout
public import MinCostFlow.Scaling.CallLoop
import WordRAM.Entry

/-!
# Encoded model answers and their internal pointer header

A failed model result is written as `[0]`. A successful result is written
as `1` followed by the statement's canonical integer pairs in original
edge order. A two-word internal header records the answer address and
length so that the final entry procedure can copy precisely those words
to address zero. The header relation contains only stored data and bounds.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Serialize a model result in exactly the answer format of `Instance`. -/
def scalingAnswerWords {m : ℕ} (result : Option (Fin m → ℤ)) : List ℕ :=
  match result with
  | none => [0]
  | some f => 1::(List.finRange m).flatMap (fun e => encodeInt (f e))

/-- The internal header holds an answer pointer and its exact word length. -/
def ScalingAnswerAt (mem : ℕ → ℕ) (header bound : ℕ) (answer : List ℕ) : Prop :=
  header+2≤bound ∧ ∃ ptr,ListAt mem header [ptr,answer.length] ∧
    ptr+answer.length≤bound ∧ ListAt mem ptr answer

/-- Every successful model answer has exactly one tag and two words per edge. -/
theorem scalingAnswerWords_some_length {m : ℕ} (f : Fin m → ℤ) :
    (scalingAnswerWords (some f)).length=1+2*m := by
  simp only [scalingAnswerWords,List.length_cons,←List.flatMap_map,←List.ofFn_eq_map,
    integers_encode_length,List.length_ofFn]
  omega

/-- Correctness of a model result implies correctness of its exact encoded
answer against the fixed problem statement. -/
theorem scalingAnswerWords_correct (I : Instance) (result : Option (Fin I.m → ℤ))
    (hgood : ∀ f,result=some f → I.IsMinCostFlow (fun e => (f e : ℝ)))
    (hbad : result=none → ∀ f,¬I.IsFeasible f) :
    I.IsCorrectAnswer (scalingAnswerWords result) := by
  cases result with
  | none => exact Or.inl ⟨rfl,hbad rfl⟩
  | some f => exact Or.inr ⟨f,hgood f rfl,rfl⟩

/-- Preserving every old cell up to the representation bound preserves
both the pointer header and the complete encoded answer. -/
theorem ScalingAnswerAt.of_agree_below {mem mem' : ℕ → ℕ} {header bound bound' : ℕ}
    {answer : List ℕ} (hat : ScalingAnswerAt mem header bound answer)
    (hb : bound≤bound') (hframe : ∀ x<bound,mem' x=mem x) :
    ScalingAnswerAt mem' header bound' answer := by
  obtain ⟨hhead,ptr,hptr,hend,hanswer⟩ := hat
  refine ⟨hhead.trans hb,ptr,hptr.of_agree_below (h₀ := bound) ?_ hframe,
    hend.trans hb,hanswer.of_agree_below hend hframe⟩
  change header+2≤bound
  exact hhead

/-- Every answer list has a simultaneous concrete array and pointer-header
representation in canonical consecutive memory. -/
theorem exists_scalingAnswerAt (answer : List ℕ) :
    ScalingAnswerAt (initMem (answer++[0,answer.length])) answer.length (answer.length+2) answer := by
  have hat := listAt_append.mp (listAt_initMem (answer++[0,answer.length]))
  exact ⟨le_rfl,0,by simpa only [Nat.zero_add] using hat.2,by omega,hat.1⟩

end MinCostFlow.Scaling.Machine
