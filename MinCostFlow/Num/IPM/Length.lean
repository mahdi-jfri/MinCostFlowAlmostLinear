module

public import MinCostFlow.Num.IPM.Slacks
public import MinCostFlow.Num.IPM.LengthFromSlacks
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Computing one edge length from its flow and bounds

We subtract the flow from the upper capacity and the lower capacity from
the flow, then evaluate the sum of powers. Thus the final error concerns
the original stored edge data, as in Definition 4.2 of Chen et al. (page 24).
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[lower,flow,upper,alpha,one,L,P,E,heap]`. -/
def lengthBody (slacks length : ℕ) : Stmt :=
  .call 9 slacks [.reg 0,.reg 1,.reg 2,.reg 5,.reg 6,.reg 8] ;;
  .call 10 length [.bin .add (.reg 8) (.reg 5),
    .bin .add (.reg 8) (.bin .mul (.const 3) (.reg 5)),
    .reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 9] ;;
  .ret (.reg 10)

/-- Exact slack computation followed by length evaluation. -/
def lengthModule (b h : ℕ) : List Stmt :=
  [lengthBody (b+1) (b+7)] ++ (slacksModule (b+1) h ++ lengthFromSlacksModule (b+7) h)

/-- Space for both exact slacks and the length evaluation. -/
def lengthSpace (L P E : ℕ) := 4*L+lengthFromSlacksSpace L P E

/-- Explicit polynomial cost for one complete edge-length calculation. -/
def lengthCost (L P E : ℕ) := 148*L+lengthFromSlacksCost L P E+300

/-- The complete per-edge length contract. The alpha block is any number in
`[0,1]`; using the representable alpha requires no change to the procedure. -/
def lengthContract (w h q : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ lo f up a one L P E heap,args=[lo,f,up,a,one,L,P,E,heap] ∧ h∣P ∧
      q+4*E+41≤P ∧ P+4*E+20≤h*L ∧ 2*P+9<2^w ∧
      lo+L≤heap ∧ f+L≤heap ∧ up+L≤heap ∧ a+L≤heap ∧ one+L≤heap ∧
      Valid mem lo h L ∧ Valid mem f h L ∧ Valid mem up h L ∧ Valid mem a h L ∧ Valid mem one h L ∧
      intVal mem one h L=(2:ℤ)^P ∧
      1/(2:ℝ)^E≤fixVal mem up h L P-fixVal mem f h L P ∧
      fixVal mem up h L P-fixVal mem f h L P≤(2:ℝ)^E ∧
      1/(2:ℝ)^E≤fixVal mem f h L P-fixVal mem lo h L P ∧
      fixVal mem f h L P-fixVal mem lo h L P≤(2:ℝ)^E ∧
      0≤fixVal mem a h L P ∧ fixVal mem a h L P≤1)
    (fun _ _ _ => True)
    (fun args _ => lengthCost (args.getD 5 0) (args.getD 6 0) (args.getD 7 0))
    (fun args _ => lengthSpace (args.getD 5 0) (args.getD 6 0) (args.getD 7 0))
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
      Valid mem' (v-args.getD 5 0) h (args.getD 5 0) ∧
      (MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q)
        (fixVal mem' (v-args.getD 5 0) h (args.getD 5 0) (args.getD 6 0))
        ((Real.rpow (fixVal mem (args.getD 2 0) h (args.getD 5 0) (args.getD 6 0)-
          fixVal mem (args.getD 1 0) h (args.getD 5 0) (args.getD 6 0))
          (-1-fixVal mem (args.getD 3 0) h (args.getD 5 0) (args.getD 6 0)))+
        (Real.rpow (fixVal mem (args.getD 1 0) h (args.getD 5 0) (args.getD 6 0)-
          fixVal mem (args.getD 0 0) h (args.getD 5 0) (args.getD 6 0))
          (-1-fixVal mem (args.getD 3 0) h (args.getD 5 0) (args.getD 6 0))))) }

/-- The complete length module is deterministic. -/
theorem lengthModule_noRand (b h : ℕ) : ∀ s∈lengthModule b h,s.NoRand := by
  intro s hs
  simp only [lengthModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hs | hl
  · simp [lengthBody,Stmt.NoRand]
  · exact slacksModule_noRand _ _ _ hs
  · exact lengthFromSlacksModule_noRand _ _ _ hl

set_option maxRecDepth 8192 in
/-- The returned fixed-point block approximates the exact length formed from
the original flow and capacities. The cost and space bounds cover all calls. -/
theorem length_meetsContract {w h b q : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w) (hp : p.HasAt b (lengthModule b h)) :
    MeetsContract w p b (lengthContract w h q) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hs := hasAt_append_left ht
  have hl := hasAt_append_right ht
  change p.HasAt (b+7) _ at hl
  have hsc := slacks_meetsContract hh (show 2*h+2≤w by omega) hs
  have hlc := lengthFromSlacks_meetsContract (q:=q) hh hw hl
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨lo,f,up,a,one,L,P,E,heap,rfl,hP,hprec,hwidth,hPw,hlo,hf,hup,ha,ho,hvlo,hvf,hvup,hva,hvo,hone,hul,huh,hdl,hdh,ha0,ha1⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+lengthSpace L P E<2^w at hbound
  have hspace0 : 0≤lengthFromSlacksSpace L P E := Nat.zero_le _
  have hlow : lo<2^w := hwords lo (by simp)
  have hfw : f<2^w := hwords f (by simp)
  have hupw : up<2^w := hwords up (by simp)
  have haw : a<2^w := hwords a (by simp)
  have how : one<2^w := hwords one (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPword : P<2^w := hwords P (by simp)
  have hEword : E<2^w := hwords E (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hU0 : 0≤fixVal mem up h L P-fixVal mem f h L P := le_trans (by positivity) hul
  have hD0 : 0≤fixVal mem f h L P-fixVal mem lo h L P := le_trans (by positivity) hdl
  apply runs_start_le
  unfold lengthBody
  refine runs_seq_call_le hsc (vs:=[lo,f,up,L,P,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨_,_,_,_,_,E,_,rfl,by omega,hlo,hf,hup,hvlo,hvf,hvup,
      by simpa only [startState,abs_of_nonneg hU0] using huh,
      by simpa only [startState,abs_of_nonneg hD0] using hdh⟩,hz,
      by change heap+4*L<2^w; unfold lengthSpace at hbound; omega⟩
  · intro v₁ mem₁ pos₁ hp₁
    rcases hp₁ with ⟨he₁,hl₁,hh₁,fr₁,hz₁,hvu₁,hvd₁,hu₁,hd₁⟩
    change v₁=heap+4*L at he₁
    change (∀ z<heap,mem₁ z=mem z) at fr₁
    change Valid mem₁ (heap+L) h L at hvu₁
    change Valid mem₁ (heap+3*L) h L at hvd₁
    change fixVal mem₁ (heap+L) h L P=fixVal mem up h L P-fixVal mem f h L P at hu₁
    change fixVal mem₁ (heap+3*L) h L P=fixVal mem f h L P-fixVal mem lo h L P at hd₁
    have hafix := fixVal_frozen (h:=h) (P:=P) fr₁ ha
    have honeval := value_frozen (h:=h) fr₁ ho
    have hv₁w : v₁<2^w := by unfold lengthSpace at hbound; omega
    have hUword : heap+L<2^w := by omega
    have h3Lword : 3*L<2^w := by omega
    have hDword : heap+3*L<2^w := by omega
    refine runs_seq_call_le hlc (vs:=[heap+L,heap+3*L,a,one,L,P,E,v₁]) (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨⟨_,_,_,_,_,_,_,_,rfl,hP,hprec,hwidth,hPw,by omega,by omega,by omega,by omega,
        hvu₁,hvd₁,valid_frozen fr₁ ha hva,valid_frozen fr₁ ho hvo,honeval.trans hone,?_,?_,?_,?_,?_,?_⟩,
        hz₁,by change v₁+lengthFromSlacksSpace L P E<2^w; unfold lengthSpace at hbound; omega⟩
      · rw [hu₁]; exact hul
      · rw [hu₁]; exact huh
      · rw [hd₁]; exact hdl
      · rw [hd₁]; exact hdh
      · rw [hafix]; exact ha0
      · rw [hafix]; exact ha1
    · intro v mem₂ pos₂ hp₂
      rcases hp₂ with ⟨⟨hl₂,hh₂,fr₂,hz₂,_⟩,hv₂,herr₂⟩
      change v₁≤v at hl₂
      change v≤v₁+lengthFromSlacksSpace L P E at hh₂
      change (∀ z<v₁,mem₂ z=mem₁ z) at fr₂
      change Valid mem₂ (v-L) h L at hv₂
      change MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q) (fixVal mem₂ (v-L) h L P)
        (Real.rpow (fixVal mem₁ (heap+L) h L P) (-1-fixVal mem₁ a h L P)+
         Real.rpow (fixVal mem₁ (heap+3*L) h L P) (-1-fixVal mem₁ a h L P)) at herr₂
      rw [hu₁,hd₁,hafix] at herr₂
      have hvw : v<2^w := by unfold lengthSpace at hbound; omega
      refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
      · change (heap≤v ∧ v≤heap+lengthSpace L P E ∧ (∀ z<heap,mem₂ z=mem z) ∧ ZeroFrom mem₂ v ∧ True) ∧
          Valid mem₂ (v-L) h L ∧
          (MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q) (fixVal mem₂ (v-L) h L P)
            (Real.rpow (fixVal mem up h L P-fixVal mem f h L P) (-1-fixVal mem a h L P)+
             Real.rpow (fixVal mem f h L P-fixVal mem lo h L P) (-1-fixVal mem a h L P)))
        refine ⟨⟨by omega,?_,?_,hz₂,trivial⟩,hv₂,herr₂⟩
        · unfold lengthSpace; omega
        · intro z hz
          rw [fr₂ z (by omega),fr₁ z hz]
      · simp only [lengthContract,slacksContract,lengthFromSlacksContract,heapContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_const,Expr.size_bin,
          argsSize_cons,argsSize_nil,lengthCost]
        omega

/-- The length contract is directly usable with an instance and flow:
only the decoding equations for the four input blocks are needed. -/
theorem length_output (I : Instance) (f : Fin I.m→ℝ) (e : Fin I.m)
    {w h q lo fp up ap one L P E heap v : ℕ} {mem mem' : ℕ→ℕ} {a : ℝ}
    (hout : (lengthContract w h q).post [lo,fp,up,ap,one,L,P,E,heap] mem v mem')
    (hlo : fixVal mem lo h L P=(I.edge e).lower)
    (hf : fixVal mem fp h L P=f e)
    (hup : fixVal mem up h L P=(I.edge e).upper)
    (ha : fixVal mem ap h L P=a) :
    MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q) (fixVal mem' (v-L) h L P)
      (MinCostFlow.IPM.lengths I a f e) := by
  have he := hout.2.2
  change MinCostFlow.IPM.ScalarApprox (1+1/(2:ℝ)^q) (fixVal mem' (v-L) h L P)
    (Real.rpow (fixVal mem up h L P-fixVal mem fp h L P) (-1-fixVal mem ap h L P)+
     Real.rpow (fixVal mem fp h L P-fixVal mem lo h L P) (-1-fixVal mem ap h L P)) at he
  rw [hlo,hf,hup,ha] at he
  exact he

end MinCostFlow.Num.IPM
