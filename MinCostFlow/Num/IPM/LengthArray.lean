module

public import MinCostFlow.Num.IPM.LengthArrayLoop
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Allocating the IPM length vector

Reserve consecutive output blocks and one guard block, then evaluate the
edges using the length scan. All original input memory is preserved. The
result is a vector approximation to the exact IPM lengths.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[lower,flow,upper,alpha,one,m,L,P,E,heap]`. -/
def lengthArrayBody (loop : ℕ) : Stmt :=
  .call 10 loop [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,
    .bin .add (.reg 9) (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 6))] ;;
  .ret (.reg 10)

/-- The allocating entry and its closed scan module. -/
def lengthArrayModule (b h : ℕ) : List Stmt :=
  [lengthArrayBody (b+1)] ++ lengthArrayLoopModule (b+1) h

/-- Allocation for the output vector, guard block, and scalar workspaces. -/
def lengthArraySpace (m L P E : ℕ) := (m+1)*L+m*lengthSpace L P E

/-- Explicit cost for the whole vector. -/
def lengthArrayCost (m L P E : ℕ) := m*(lengthCost L P E+17*L+100)+60

/-- Output edge `i` is at `heap+iL`. Uniform precision and range conditions
are exactly those of the scalar length procedure. -/
def lengthArrayContract (w h q : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ lo f up a one m L P E heap,args=[lo,f,up,a,one,m,L,P,E,heap] ∧ h∣P ∧
      q+4*E+41≤P ∧ P+4*E+20≤h*L ∧ 2*P+9<2^w ∧
      lo+m*L≤heap ∧ f+m*L≤heap ∧ up+m*L≤heap ∧ a+L≤heap ∧ one+L≤heap ∧
      (∀i<m,EdgeData mem (lo+i*L) (f+i*L) (up+i*L) a one h L P E))
    (fun _ _ _ => True)
    (fun args _ => lengthArrayCost (args.getD 5 0) (args.getD 6 0) (args.getD 7 0) (args.getD 8 0))
    (fun args _ => lengthArraySpace (args.getD 5 0) (args.getD 6 0) (args.getD 7 0) (args.getD 8 0))
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
      (∀i<args.getD 5 0,Valid mem' (heapArg args+i*args.getD 6 0) h (args.getD 6 0) ∧
        MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q)
          (fixVal mem' (heapArg args+i*args.getD 6 0) h (args.getD 6 0) (args.getD 7 0))
          (arrayLength mem (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0)
            h (args.getD 6 0) (args.getD 7 0) i))}

/-- Length-vector allocation and evaluation are deterministic. -/
theorem lengthArrayModule_noRand (b h : ℕ) : ∀ s∈lengthArrayModule b h,s.NoRand := by
  intro s hs
  simp only [lengthArrayModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hl
  · simp [lengthArrayBody,Stmt.NoRand]
  · exact lengthArrayLoopModule_noRand _ _ _ hl

set_option maxRecDepth 16384 in
/-- The whole length array meets its coordinatewise approximation contract,
preserving the original heap prefix and returning a fresh zero suffix. -/
theorem lengthArray_meetsContract {w h b q : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (lengthArrayModule b h)) :
    MeetsContract w p b (lengthArrayContract w h q) := by
  have hl := hasAt_append_right hp
  change p.HasAt (b+1) _ at hl
  have hlc := lengthArrayLoop_meetsContract (q:=q) hh hw hl
  have hw1 : 1<2^w := lt_of_lt_of_le (by decide : 1<2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨lo,f,up,a,one,m,L,P,E,heap,rfl,hP,hprec,hwidth,hPw,hlo,hf,hup,ha,ho,hdata⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+lengthArraySpace m L P E<2^w at hbound
  have hlow : lo<2^w := hwords lo (by simp)
  have hfw : f<2^w := hwords f (by simp)
  have hupw : up<2^w := hwords up (by simp)
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have hmw : m<2^w := hwords m (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPword : P<2^w := hwords P (by simp)
  have hEw : E<2^w := hwords E (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hm1w : m+1<2^w := by
    have hLpos : 0<L := by nlinarith only [hwidth]
    have ht : m+1≤(m+1)*L := Nat.le_mul_of_pos_right _ hLpos
    unfold lengthArraySpace at hbound
    omega
  have hreservew : (m+1)*L<2^w := by unfold lengthArraySpace at hbound; omega
  have hnextw : heap+(m+1)*L<2^w := by unfold lengthArraySpace at hbound; omega
  apply runs_start_le
  unfold lengthArrayBody
  refine runs_seq_call_le hlc (vs:=[lo,f,up,a,one,m,L,P,E,heap,heap+(m+1)*L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,_,_,_,_,_,_,_,rfl,hP,hprec,hwidth,hPw,hlo,hf,hup,ha,ho,le_rfl,hdata⟩,
      hz.mono (h':=heap+(m+1)*L) (by omega),by change heap+(m+1)*L+m*lengthSpace L P E<2^w; simpa only [lengthArraySpace,Nat.add_assoc] using hbound⟩
  · intro v mem₁ pos₁ hp₁
    rcases hp₁ with ⟨hl₁,hh₁,hz₁,fr₁,hvalues₁⟩
    change heap+(m+1)*L≤v at hl₁
    change v≤heap+(m+1)*L+m*lengthSpace L P E at hh₁
    change (∀z<heap,mem₁ z=mem z) at fr₁
    have hvw : v<2^w := by unfold lengthArraySpace at hbound; omega
    refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
    · change (heap≤v ∧ v≤heap+lengthArraySpace m L P E ∧ (∀z<heap,mem₁ z=mem z) ∧ ZeroFrom mem₁ v ∧ True) ∧ _
      exact ⟨⟨by omega,by unfold lengthArraySpace; omega,fr₁,hz₁,trivial⟩,hvalues₁⟩
    · simp only [lengthArrayContract,lengthArrayLoopContract,heapContract,lengthArrayCost,
        List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,argsSize_cons,argsSize_nil]
      omega

/-- Instance decoding equations turn the output contract into the IPM's
vector approximation statement for all edges at once. -/
theorem lengthArray_output (I : Instance) (f : Fin I.m→ℝ)
    {w h q lo fp up ap one L P E heap v : ℕ} {mem mem' : ℕ→ℕ} {a : ℝ}
    (hout : (lengthArrayContract w h q).post [lo,fp,up,ap,one,I.m,L,P,E,heap] mem v mem')
    (hlo : ∀e : Fin I.m,fixVal mem (lo+e.val*L) h L P=(I.edge e).lower)
    (hf : ∀e : Fin I.m,fixVal mem (fp+e.val*L) h L P=f e)
    (hup : ∀e : Fin I.m,fixVal mem (up+e.val*L) h L P=(I.edge e).upper)
    (ha : fixVal mem ap h L P=a) :
    MinCostFlow.IPM.VectorApprox (1+1/(2:ℝ)^q)
      (fun e : Fin I.m => fixVal mem' (heap+e.val*L) h L P) (MinCostFlow.IPM.lengths I a f) := by
  intro e
  have he := (hout.2 e.val e.isLt).2
  change MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q) (fixVal mem' (heap+e.val*L) h L P)
    (arrayLength mem lo fp up ap h L P e.val) at he
  simp only [arrayLength,hlo e,hf e,hup e,ha] at he
  exact he

end MinCostFlow.Num.IPM
