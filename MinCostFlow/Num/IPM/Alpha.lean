module

public import MinCostFlow.Num.IPM.AlphaFacts
public import MinCostFlow.Num.IPM.AlphaStorageFacts
public import MinCostFlow.Num.IPM.BitLength
public import MinCostFlow.Num.IPM.CeilingLog
public import WordRAM.Layout
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Computing the representable IPM exponent

Count the bits of the two word inputs, take the ceiling binary logarithm of
one thousand times their sum, and store that exponent followed by the dyadic
fixed-point value. The latter has one set bit, so writing it needs one store
into fresh-zero memory. Cost is linear in the two binary input lengths.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[m,U,L,P,heap]`. The output header at `heap` is `k`, followed
by the `L`-limb fixed-point block for `2⁻ᵏ`. -/
def alphaBody (bits clog h : ℕ) : Stmt :=
  .call 5 bits [.reg 0] ;;
  .call 6 bits [.reg 1] ;;
  .call 7 clog [.bin .mul (.const 1000) (.bin .add (.reg 5) (.reg 6))] ;;
  .store (.reg 4) (.reg 7) ;;
  .store (.bin .add (.bin .add (.reg 4) (.const 1))
      (.bin .div (.bin .sub (.reg 3) (.reg 7)) (.const h)))
    (.bin .shiftLeft (.const 1) (.bin .mod (.bin .sub (.reg 3) (.reg 7)) (.const h))) ;;
  .ret (.bin .add (.bin .add (.reg 4) (.reg 2)) (.const 1))

/-- The dyadic exponent entry and its two word scans. -/
def alphaModule (b h : ℕ) : List Stmt :=
  [alphaBody (b+1) (b+2) h] ++ (bitLengthModule (b+1) ++ ceilingLogModule (b+2))

/-- Allocate a one-word exponent header and an `L`-limb dyadic block. Precision
covers the chosen exponent, with two spare signed bits. The threshold plus
one must fit in a word for the rounded-halving scan. -/
def alphaContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m U L P heap,args=[m,U,L,P,heap] ∧ 2≤m*U ∧
      alphaExponent m U≤P ∧ P+2≤h*L ∧ alphaScale m U+1<2^w)
    (fun args _ mem' =>
      mem' (heapArg args)=alphaExponent (args.getD 0 0) (args.getD 1 0) ∧
      Valid mem' (heapArg args+1) h (args.getD 2 0) ∧
      fixVal mem' (heapArg args+1) h (args.getD 2 0) (args.getD 3 0)=
        alphaPrime (args.getD 0 0) (args.getD 1 0))
    (fun args _ => 20000*((args.getD 0 0).size+(args.getD 1 0).size+1))
    (fun args _ => args.getD 2 0+1)
  { C with post := fun args mem v mem' =>
    v=heapArg args+(args.getD 2 0+1) ∧ C.post args mem v mem' }

/-- The exponent procedure and its word scans are deterministic. -/
theorem alphaModule_noRand (b h : ℕ) : ∀ s∈alphaModule b h,s.NoRand := by
  intro s hs
  simp only [alphaModule,List.mem_append,List.mem_singleton] at hs
  rcases hs with rfl | hb | hc
  · simp [alphaBody,Stmt.NoRand]
  · exact bitLengthModule_noRand _ _ hb
  · exact ceilingLogModule_noRand _ _ hc

/-- The entry computes the least covering exponent and its exact dyadic value
within the common heap discipline and the stated linear bit-length cost. -/
theorem alpha_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0<h) (hw : 2*h+2≤w) (hp : p.HasAt b (alphaModule b h)) :
    MeetsContract w p b (alphaContract w h) := by
  have ht := hasAt_append_right hp
  change p.HasAt (b+1) _ at ht
  have hb := hasAt_append_left ht
  have hc := hasAt_append_right ht
  change p.HasAt (b+2) _ at hc
  have hbase := base_lt_word hw
  have hw2 : 2<2^w := by
    have hw4 : 4≤w := by omega
    exact lt_of_lt_of_le (by decide : 2<2^4) (Nat.pow_le_pow_right (by decide) hw4)
  have hbC := bitLength_meetsContract hw2 hb
  have hcC := ceilingLog_meetsContract hw2 hc
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨m,U,L,P,heap,rfl,h2,hkP,hwidth,hD⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap+(L+1)<2^w at hbound
  have hm : 0<m := Nat.pos_of_ne_zero (by intro he; simp only [he,zero_mul] at h2; omega)
  have hbm := Nat.size_pos.mpr hm
  have hDw : 1000*(m.size+U.size)+1<2^w := hD
  have h1000w : 1000<2^w := by omega
  have hsumw : m.size+U.size<2^w := by omega
  have hmw : m<2^w := hwords m (by simp)
  have hUw : U<2^w := hwords U (by simp)
  have hLw : L<2^w := hwords L (by simp)
  have hPw : P<2^w := hwords P (by simp)
  have hheapw : heap<2^w := hwords heap (by simp)
  have hhw : h<2^w := by
    have hhbound : h<2^h := Nat.lt_two_pow_self
    exact lt_trans hhbound hbase
  apply runs_start_le
  unfold alphaBody
  refine runs_seq_call_le hbC (vs:=[m]) (by eval_expr) (by wram_words) ⟨_,rfl⟩ ?_
  intro bm mem₁ pos₁ hp₁
  rcases hp₁ with ⟨hmem₁,hbm₁⟩
  change mem₁=mem at hmem₁
  subst mem₁
  change bm=m.size at hbm₁
  subst bm
  have hbmw : m.size<2^w := by omega
  refine runs_seq_call_le hbC (vs:=[U]) (by eval_expr) (by wram_words) ⟨_,rfl⟩ ?_
  intro bU mem₂ pos₂ hp₂
  rcases hp₂ with ⟨hmem₂,hbU₂⟩
  change mem₂=mem at hmem₂
  subst mem₂
  change bU=U.size at hbU₂
  subst bU
  have hbUw : U.size<2^w := by omega
  have hscaleW : 1000*(m.size+U.size)<2^w := by omega
  refine runs_seq_call_le hcC (vs:=[1000*(m.size+U.size)]) (by eval_expr) (by wram_words)
    ⟨_,rfl,hDw⟩ ?_
  intro k mem₃ pos₃ hp₃
  rcases hp₃ with ⟨hmem₃,hk₃⟩
  change mem₃=mem at hmem₃
  subst mem₃
  change k=alphaExponent m U at hk₃
  subst k
  have hkD : alphaExponent m U≤alphaScale m U := ceilingLog_le_value _
  have hkw : alphaExponent m U<2^w := lt_of_le_of_lt hkD (by exact hscaleW)
  have hminusw : P-alphaExponent m U<2^w := by omega
  have hj : (P-alphaExponent m U)/h<L :=
    (Nat.div_lt_iff_lt_mul hh).mpr (by
      have hs : P-alphaExponent m U<h*L := by omega
      simpa only [mul_comm] using hs)
  have hq0 : 0≤(P-alphaExponent m U)/h := Nat.zero_le _
  have hqw : (P-alphaExponent m U)/h<2^w := by omega
  have hmod : (P-alphaExponent m U)%h<h := Nat.mod_lt _ hh
  have hmodw : (P-alphaExponent m U)%h<2^w := by omega
  have hd : 2^((P-alphaExponent m U)%h)<base h := Nat.pow_lt_pow_right (by decide) hmod
  have hdw : 2^((P-alphaExponent m U)%h)<2^w := lt_trans hd hbase
  have hslot : heap+1+(P-alphaExponent m U)/h<2^w := by omega
  have hnext : heap+1<2^w := by omega
  have hend : heap+L+1<2^w := by omega
  have hheapL : heap+L<2^w := by omega
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (v:=heap+L+1) (by eval_expr) ?_ ?_
  · simp only [Nat.shiftLeft_eq,one_mul]
    change heap+L+1=heap+(L+1) ∧ heap≤heap+L+1 ∧ heap+L+1≤heap+(L+1) ∧
      (∀ z<heap,Function.update (Function.update mem heap (alphaExponent m U))
        (heap+1+(P-alphaExponent m U)/h) (2^((P-alphaExponent m U)%h)) z=mem z) ∧
      ZeroFrom (Function.update (Function.update mem heap (alphaExponent m U))
        (heap+1+(P-alphaExponent m U)/h) (2^((P-alphaExponent m U)%h))) (heap+L+1) ∧
      Function.update (Function.update mem heap (alphaExponent m U))
        (heap+1+(P-alphaExponent m U)/h) (2^((P-alphaExponent m U)%h)) heap=alphaExponent m U ∧
      Valid (Function.update (Function.update mem heap (alphaExponent m U))
        (heap+1+(P-alphaExponent m U)/h) (2^((P-alphaExponent m U)%h))) (heap+1) h L ∧
      fixVal (Function.update (Function.update mem heap (alphaExponent m U))
        (heap+1+(P-alphaExponent m U)/h) (2^((P-alphaExponent m U)%h))) (heap+1) h L P=alphaPrime m U
    have hpoint : ∀ i<L,Function.update (Function.update mem heap (alphaExponent m U))
        (heap+1+(P-alphaExponent m U)/h) (2^((P-alphaExponent m U)%h)) (heap+1+i)=
          if i=(P-alphaExponent m U)/h then 2^((P-alphaExponent m U)%h) else 0 := by
      intro i hi
      by_cases he : i=(P-alphaExponent m U)/h
      · subst i
        simp only [Function.update_self,ite_true]
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),hz _ (by omega),ite_eq_right he]
    obtain ⟨hvalid,hvalue⟩ := alphaBlock_spec hh hkP hwidth hpoint
    refine ⟨by omega,by omega,by omega,?_,?_,?_,hvalid,hvalue⟩
    · intro z hz
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    · have hzbase : ZeroFrom (Function.update mem heap (alphaExponent m U)) (heap+L+1) :=
        (hz.update_head (alphaExponent m U)).mono (by omega)
      exact hzbase.update_lt (v:=2^((P-alphaExponent m U)%h)) (by omega)
    · rw [Function.update_of_ne (by omega),Function.update_self]
  · have hkD' : Nat.clog 2 (1000*(m.size+U.size))≤1000*(m.size+U.size) := hkD
    simp only [alphaContract,heapContract,bitLengthContract,ceilingLogContract,
      List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,Expr.size_const,
      argsSize_cons,argsSize_nil]
    omega

/-- The machine output satisfies the analytic comparison needed by the IPM. -/
theorem alpha_output_bounds {w h L P heap v : ℕ} {mem mem' : ℕ→ℕ}
    (I : Instance) (U : ℕ) (h2 : 2≤I.m*U)
    (hpost : (alphaContract w h).post [I.m,U,L,P,heap] mem v mem') :
    MinCostFlow.IPM.alpha I (U:ℝ)/10≤fixVal mem' (heap+1) h L P ∧
    fixVal mem' (heap+1) h L P≤MinCostFlow.IPM.alpha I (U:ℝ) := by
  have hv := hpost.2.2.2.2.2.2.2
  change fixVal mem' (heap+1) h L P=alphaPrime I.m U at hv
  rw [hv]
  exact alphaPrime_bounds I U h2

end MinCostFlow.Num.IPM
