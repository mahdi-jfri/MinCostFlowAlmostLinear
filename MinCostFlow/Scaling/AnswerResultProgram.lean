module

public import MinCostFlow.Scaling.ScalingAnswerLayout
public import MinCostFlow.Scaling.FlowAnswerProgram
public import MinCostFlow.Scaling.WordPairProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Writing answers with their internal pointer headers

Reuse the already proved success and failure serializers, then append a
two-word pointer/length header. Both branches therefore return the same
internal layout, while their actual answer words remain exactly those
specified by `Instance.IsCorrectAnswer`. All input cells are preserved.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Argument `[heap]`: write `[0]`, then its pointer and length. -/
def infeasibleResultBody (answer pair : ℕ) : Stmt :=
  .call 1 answer [.reg 0] ;;
  .call 2 pair [.reg 0,.const 1,.reg 1] ;;
  .ret (.reg 2)

/-- Failure serializer and two-word pointer writer. -/
def infeasibleResultModule (b : ℕ) : List Stmt :=
  [infeasibleResultBody (b+1) (b+2),infeasibleAnswerBody,wordPairBody]

/-- A failed model answer, including its internal header, allocates three cells. -/
def infeasibleResultContract (w : ℕ) : Contract :=
  let H := heapContract w (fun args _ => ∃ heap,args=[heap])
    (fun _ _ _ => True)
    (fun _ _ => 50) (fun _ _ => 3)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+3 ∧
      ScalingAnswerAt mem' (ret-2) ret [0] }

/-- Arguments `[signedFlow,count,heap]`: write the successful answer,
then the pointer and length of its complete tagged encoding. -/
def flowResultBody (answer pair : ℕ) : Stmt :=
  .call 3 answer [.reg 0,.reg 1,.reg 2] ;;
  .call 4 pair [.reg 2,.bin .add (.const 1) (.bin .mul (.const 2) (.reg 1)),.reg 3] ;;
  .ret (.reg 4)

/-- Successful serializer, shared word copy, and pointer-header writer. -/
def flowResultModule (b : ℕ) : List Stmt :=
  flowResultBody (b+1) (b+3) :: (flowAnswerModule (b+1) ++ wordPairModule)

/-- The exact successful model answer and its two-word internal header. -/
def flowResultContract (w : ℕ) {m : ℕ} (f : Fin m → ℤ) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ flow heap,args=[flow,m,heap] ∧ SignedTableAt mem flow f ∧ flow+2*m≤heap ∧ 2<2^w)
    (fun _ _ _ => True)
    (fun _ _ => 40*m+150) (fun _ _ => 3+2*m)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+3+2*m ∧
      ScalingAnswerAt mem' (ret-2) ret (scalingAnswerWords (some f)) }

/-- Both answer-header modules contain no random instruction. -/
theorem infeasibleResultModule_noRand (b : ℕ) : ∀ body∈infeasibleResultModule b,body.NoRand := by
  intro body hb
  simp only [infeasibleResultModule,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl
  · simp only [infeasibleResultBody,Stmt.NoRand,and_self]
  · exact infeasibleAnswerBody_noRand
  · exact wordPairBody_noRand

/-- Successful answer-header writing contains no random instruction. -/
theorem flowResultModule_noRand (b : ℕ) : ∀ body∈flowResultModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [flowResultBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact flowAnswerModule_noRand _ body hb
    · have he : body=wordPairBody := by simpa only [wordPairModule,List.mem_singleton] using hb
      subst body
      exact wordPairBody_noRand

/-- Writing the failure payload and pointer header computes the common
answer layout with exact allocation and constant cost. -/
theorem infeasibleResult_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (infeasibleResultModule b)) :
    MeetsContract w p b (infeasibleResultContract w) := by
  have ht : p.HasAt (b+1) ([infeasibleAnswerBody]++wordPairModule) := hasAt_tail hp
  have hkA := infeasibleAnswer_meetsContract (w := w) (hasAt_append_left ht)
  have hkH := wordPair_meetsContract (w := w) (hasAt_append_right ht)
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨heap,rfl⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+3<2^w at hs
  have hh : heap<2^w := by omega
  have h1 : 1<2^w := by omega
  apply runs_start_le
  unfold infeasibleResultBody
  refine runs_seq_call_le hkA (vs := [heap]) (by eval_expr) (by wram_words)
    ⟨⟨heap,rfl⟩,hz,by change heap+1<2^w; omega⟩ ?_
  intro next memA posA hpostA
  obtain ⟨⟨_,_,hframeA,hzA,hanswer⟩,hnext⟩ := hpostA
  change next=heap+1 at hnext
  change ListAt memA heap [0] at hanswer
  change (∀ x<heap,memA x=mem x) at hframeA
  change ZeroFrom memA next at hzA
  have hn : next<2^w := by omega
  refine runs_seq_call_le hkH (vs := [heap,1,next]) (by eval_expr) (by wram_words)
    ⟨⟨heap,1,next,rfl⟩,hzA,by change next+2<2^w; omega⟩ ?_
  intro out memH posH hpostH
  obtain ⟨⟨_,_,hframeH,hzH,hheader⟩,hout⟩ := hpostH
  change out=next+2 at hout
  change ListAt memH next [heap,1] at hheader
  change (∀ x<next,memH x=memA x) at hframeH
  change ZeroFrom memH out at hzH
  have how : out<2^w := by omega
  refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
  · change (heap≤out ∧ out≤heap+3 ∧ (∀ x<heap,memH x=mem x) ∧ ZeroFrom memH out ∧
      True) ∧ out=heap+3 ∧ ScalingAnswerAt memH (out-2) out [0]
    refine ⟨⟨by omega,by omega,?_,hzH,trivial⟩,by omega,?_⟩
    · intro x hx
      exact (hframeH x (by omega)).trans (hframeA x hx)
    · refine ⟨by omega,heap,?_,by change heap+1≤out; omega,?_⟩
      · have he : out-2=next := by omega
        rwa [he]
      · exact hanswer.of_agree_below (by change heap+1≤next; omega) hframeH
  · simp only [infeasibleResultContract,infeasibleAnswerContract,wordPairContract,heapContract,
      argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_const]
    omega

/-- Writing the successful payload and pointer header computes the exact
model answer, preserving sources and leaving a fresh zero tail. -/
theorem flowResult_meetsContract {w b m : ℕ} {p : Program}
    (hp : p.HasAt b (flowResultModule b)) (f : Fin m → ℤ) :
    MeetsContract w p b (flowResultContract w f) := by
  have ht : p.HasAt (b+1) (flowAnswerModule (b+1)++wordPairModule) := hasAt_tail hp
  have hH : p.HasAt (b+3) wordPairModule := hasAt_append_right ht
  have hkA := flowAnswer_meetsContract (w := w) (hasAt_append_left ht) f
  have hkH := wordPair_meetsContract (w := w) hH
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨flow,heap,rfl,hflow,hflowEnd,h2⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(3+2*m)<2^w at hs
  have hf : flow<2^w := by omega
  have hm : m<2^w := by omega
  have hh : heap<2^w := by omega
  have h2m : 2*m<2^w := by omega
  have hlen : 1+2*m<2^w := by omega
  apply runs_start_le
  unfold flowResultBody
  refine runs_seq_call_le hkA (vs := [flow,m,heap]) (by eval_expr) (by wram_words)
    ⟨⟨flow,heap,rfl,hflow,hflowEnd,h2⟩,hz,by change heap+(1+2*m)<2^w; omega⟩ ?_
  intro next memA posA hpostA
  obtain ⟨⟨_,_,hframeA,hzA,hanswer⟩,hnext⟩ := hpostA
  change next=heap+1+2*m at hnext
  change ListAt memA heap (scalingAnswerWords (some f)) at hanswer
  change (∀ x<heap,memA x=mem x) at hframeA
  change ZeroFrom memA next at hzA
  have hn : next<2^w := by omega
  refine runs_seq_call_le hkH (vs := [heap,1+2*m,next]) (by eval_expr) (by wram_words)
    ⟨⟨heap,1+2*m,next,rfl⟩,hzA,by change next+2<2^w; omega⟩ ?_
  intro out memH posH hpostH
  obtain ⟨⟨_,_,hframeH,hzH,hheader⟩,hout⟩ := hpostH
  change out=next+2 at hout
  change ListAt memH next [heap,1+2*m] at hheader
  change (∀ x<next,memH x=memA x) at hframeH
  change ZeroFrom memH out at hzH
  have how : out<2^w := by omega
  refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
  · change (heap≤out ∧ out≤heap+(3+2*m) ∧ (∀ x<heap,memH x=mem x) ∧ ZeroFrom memH out ∧
      True) ∧ out=heap+3+2*m ∧ ScalingAnswerAt memH (out-2) out (scalingAnswerWords (some f))
    refine ⟨⟨by omega,by omega,?_,hzH,trivial⟩,by omega,?_⟩
    · intro x hx
      exact (hframeH x (by omega)).trans (hframeA x hx)
    · refine ⟨by omega,heap,?_,?_,hanswer.of_agree_below ?_ hframeH⟩
      · have he : out-2=next := by omega
        rw [he,scalingAnswerWords_some_length]
        exact hheader
      · rw [scalingAnswerWords_some_length]; omega
      · rw [scalingAnswerWords_some_length]; omega
  · simp only [flowResultContract,flowAnswerContract,wordPairContract,heapContract,argsSize_cons,argsSize_nil,
      Expr.size_bin,Expr.size_reg,Expr.size_const]
    omega

/-- The failure writer's complete entry premises hold in zero memory. -/
theorem exists_infeasibleResult_pre :
    (∀ x∈[0],x<2^3) ∧ (infeasibleResultContract 3).pre [0] (fun _ => 0) := by
  exact ⟨by intro x hx; have he : x=0 := List.mem_singleton.mp hx; subst x; decide,
    ⟨0,rfl⟩,fun _ _ => rfl,by decide⟩

/-- Every signed flow has simultaneous successful-answer writing premises
in canonical source memory at a finite width. -/
theorem exists_flowResult_pre {m : ℕ} (f : Fin m → ℤ) :
    ∃ w,(∀ x∈[0,m,2*m],x<2^w) ∧
      (flowResultContract w f).pre [0,m,2*m] (initMem ((List.ofFn f).flatMap encodeInt)) := by
  let M := ((List.ofFn f).map Int.natAbs).foldr max 0
  let w := M+4*m+9
  have hw : M+4*m+9<2^w := Nat.lt_two_pow_self
  refine ⟨w,?_,⟨0,2*m,rfl,signedTableAt_of_listAt _ _ _ (listAt_initMem _),by omega,by omega⟩,?_,?_⟩
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · change ZeroFrom (initMem ((List.ofFn f).flatMap encodeInt)) (2*m)
    simpa only [integers_encode_length,List.length_ofFn] using zeroFrom_initMem ((List.ofFn f).flatMap encodeInt)
  · change 2*m+(3+2*m)<2^w
    omega

end MinCostFlow.Scaling.Machine
