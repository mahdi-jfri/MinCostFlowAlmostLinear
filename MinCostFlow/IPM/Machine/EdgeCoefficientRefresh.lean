module

public import MinCostFlow.IPM.Machine.ScalarCoefficientRefresh
public import MinCostFlow.IPM.Machine.ScalarLengthFrame
public import MinCostFlow.IPM.Machine.StoreCoefficients
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Refreshing one reported edge in the coefficient tables

Reserve a guard block, compute both scalar coefficients, then copy them
into the two stored tables. The guard ensures that both computed blocks
lie above the old tables even when a numerical contract only bounds its
returned heap. Only the two table entries change below the incoming heap.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,cost,residual,lower,flow,upper,alpha,one,L,P,E,lengthDestination,gradientDestination,heap]`. -/
def edgeCoefficientRefreshBody (refresh store : ℕ) : Stmt :=
  .call 14 refresh [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,
    .reg 8,.reg 9,.reg 10,.bin .add (.reg 13) (.reg 8)] ;;
  .call 15 store [.load (.bin .sub (.reg 14) (.const 1)),
    .bin .sub (.bin .sub (.reg 14) (.const 1)) (.reg 8),
    .reg 11,.reg 12,.reg 8,.reg 14] ;;
  .ret (.reg 14)

/-- Scalar computation followed by the two table copies. -/
def edgeCoefficientRefreshModule (b h : ℕ) : List Stmt :=
  let s := b+1+(scalarCoefficientRefreshModule (b+1) h).length
  [edgeCoefficientRefreshBody (b+1) s] ++
    (scalarCoefficientRefreshModule (b+1) h ++ storeCoefficientsModule s)

/-- One reported edge is refreshed using the original stored inputs. The
only writes below the old heap are the two disjoint coefficient entries. -/
def edgeCoefficientRefreshContract (w h q K : ℕ) : Contract where
  pre args mem := (∃ m c r lo f up a one L P E ld gd heap,
    args=[m,c,r,lo,f,up,a,one,L,P,E,ld,gd,heap] ∧
    ld+L≤heap ∧ gd+L≤heap ∧ (ld+L≤gd ∨ gd+L≤ld) ∧
    (Num.IPM.lengthContract w h q).pre [lo,f,up,a,one,L,P,E,heap] mem ∧
    (Num.IPM.gradientContract w h q K).pre [m,c,r,lo,f,up,a,one,L,P,E,heap] mem) ∧
    heapArg args+args.getD 8 0+Num.IPM.lengthSpace (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+
      Num.IPM.gradientSpace (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+1<2^w
  post args mem v mem' := heapArg args≤v ∧
    v≤heapArg args+args.getD 8 0+
      Num.IPM.lengthSpace (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+
      Num.IPM.gradientSpace (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+1 ∧
    ZeroFrom mem' v ∧
    (∀ z<heapArg args,(z<args.getD 11 0 ∨ args.getD 11 0+args.getD 8 0≤z) →
      (z<args.getD 12 0 ∨ args.getD 12 0+args.getD 8 0≤z) → mem' z=mem z) ∧
    Num.Valid mem' (args.getD 11 0) h (args.getD 8 0) ∧
    ScalarApprox (1+1/(2:ℝ)^q)
      (Num.fixVal mem' (args.getD 11 0) h (args.getD 8 0) (args.getD 9 0))
      (Num.IPM.arrayLength mem (args.getD 3 0) (args.getD 4 0) (args.getD 5 0)
        (args.getD 6 0) h (args.getD 8 0) (args.getD 9 0) 0) ∧
    Num.Valid mem' (args.getD 12 0) h (args.getD 8 0) ∧
    |Num.fixVal mem' (args.getD 12 0) h (args.getD 8 0) (args.getD 9 0)-
      Num.IPM.arrayGradient mem (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)
        (args.getD 3 0) (args.getD 4 0) (args.getD 5 0) (args.getD 6 0) h
        (args.getD 8 0) (args.getD 9 0) 0|≤
      (1/(2:ℝ)^q)*Num.IPM.arrayLength mem (args.getD 3 0) (args.getD 4 0)
        (args.getD 5 0) (args.getD 6 0) h (args.getD 8 0) (args.getD 9 0) 0
  cost args _ := Num.IPM.lengthCost (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+
    Num.IPM.gradientCost (args.getD 8 0) (args.getD 9 0) (args.getD 10 0)+34*args.getD 8 0+500

/-- The complete one-edge refresh is deterministic. -/
theorem edgeCoefficientRefreshModule_noRand (b h : ℕ) :
    ∀ body∈edgeCoefficientRefreshModule b h,body.NoRand := by
  intro body hb
  simp only [edgeCoefficientRefreshModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb | hb
  · simp [edgeCoefficientRefreshBody,Stmt.NoRand]
  · exact scalarCoefficientRefreshModule_noRand _ _ _ hb
  · exact storeCoefficientsModule_noRand _ _ hb

/-- Actual scalar computation and table writes refresh both coefficients
with explicit cost, scratch space, and the frame outside their entries. -/
theorem edgeCoefficientRefresh_meetsContract {w h b q K : ℕ} {p : Program}
    (hh : 0<h) (hw : 3*h+2≤w)
    (hp : p.HasAt b (edgeCoefficientRefreshModule b h)) :
    MeetsContract w p b (edgeCoefficientRefreshContract w h q K) := by
  have ht := Num.hasAt_append_right hp
  have hc : p.HasAt (b+1) (scalarCoefficientRefreshModule (b+1) h) := Num.hasAt_append_left ht
  have hs := Num.hasAt_append_right ht
  have hcalc := scalarCoefficientRefresh_meetsContract (q:=q) (K:=K) hh hw hc
  have hw1 : 1<2^w := lt_of_lt_of_le (by decide : 1<2^1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hstore := storeCoefficients_meetsContract (h:=h) hw1 hs
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,c,r,lo,f,up,a,one,L,P,E,ld,gd,heap,rfl,hld,hgd,hdis,hpreL,hpreG⟩,hspace⟩ := hpre
  change heap+L+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+1<2^w at hspace
  have hz : ZeroFrom mem heap := hpreL.2.1
  have hframeId : ∀ x<heap,mem x=mem x := fun _ _ => rfl
  have hlenNext := length_pre_frozen hpreL hframeId (by omega : heap≤heap+L)
    (hz.mono (by omega)) (by omega : heap+L+Num.IPM.lengthSpace L P E<2^w)
  have hgradNext := gradient_pre_frozen hpreG hframeId (by omega : heap≤heap+L)
    (hz.mono (by omega)) (by omega : heap+L+Num.IPM.gradientSpace L P E<2^w)
  have hheapw : heap+L<2^w := by omega
  apply runs_start_le
  unfold edgeCoefficientRefreshBody
  refine runs_seq_call_le hcalc (vs:=[m,c,r,lo,f,up,a,one,L,P,E,heap+L]) (by eval_expr) ?_ ?_ ?_
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | rfl
    all_goals first | exact hx ▸ hwords _ (by simp) | exact hheapw
  · exact ⟨⟨m,c,r,lo,f,up,a,one,L,P,E,heap+L,rfl,by omega,hlenNext,hgradNext⟩,hspace⟩
  · intro v0 mem0 pos0 hp0
    obtain ⟨hlo0,hhi0,hframe0,hfresh0,hvl,hl,hvg,hg,hptrLo,hptrEnd,hgradLo⟩ := hp0
    change heap+L≤v0 at hlo0
    change v0≤heap+L+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+1 at hhi0
    change ∀ x<heap+L,mem0 x=mem x at hframe0
    change Num.Valid mem0 (mem0 (v0-1)) h L at hvl
    change Num.Valid mem0 (v0-1-L) h L at hvg
    change heap+L-L≤mem0 (v0-1) at hptrLo
    change mem0 (v0-1)+L≤v0-1 at hptrEnd
    change heap+L≤v0-1 at hgradLo
    have hv0w : v0<2^w := by omega
    have hptrw : mem0 (v0-1)<2^w := by omega
    have hgradw : v0-1-L<2^w := by omega
    refine runs_seq_call_le hstore
      (vs:=[mem0 (v0-1),v0-1-L,ld,gd,L,v0]) (by eval_expr) ?_ ?_ ?_
    · intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hptrw
      · exact hgradw
      · exact hwords _ (by simp)
      · exact hwords _ (by simp)
      · exact hwords _ (by simp)
      · exact hv0w
    · exact ⟨mem0 (v0-1),v0-1-L,ld,gd,L,v0,rfl,
        by omega,by omega,by omega,by omega,hv0w,
        Or.inr (by omega),Or.inr (by omega),Or.inr (by omega),hdis,hvl,hvg,hfresh0⟩
    · intro v1 mem1 pos1 hp1
      obtain ⟨hv1,hfresh1,hframe1,hvl1,hvalL,hvg1,hvalG⟩ := hp1
      change v1=v0 at hv1
      change ∀ z,(z<ld ∨ ld+L≤z) → (z<gd ∨ gd+L≤z) → mem1 z=mem0 z at hframe1
      change Num.intVal mem1 ld h L=Num.intVal mem0 (mem0 (v0-1)) h L at hvalL
      change Num.intVal mem1 gd h L=Num.intVal mem0 (v0-1-L) h L at hvalG
      change ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem0 (mem0 (v0-1)) h L P)
        (Num.IPM.arrayLength mem lo f up a h L P 0) at hl
      change |Num.fixVal mem0 (v0-1-L) h L P-Num.IPM.arrayGradient mem m c r lo f up a h L P 0|≤
        (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo f up a h L P 0 at hg
      refine runs_ret_le (v:=v0) (by eval_expr) ?_ ?_
      · change heap≤v0 ∧ v0≤heap+L+Num.IPM.lengthSpace L P E+Num.IPM.gradientSpace L P E+1 ∧
          ZeroFrom mem1 v0 ∧
          (∀ z<heap,(z<ld ∨ ld+L≤z) → (z<gd ∨ gd+L≤z) → mem1 z=mem z) ∧
          Num.Valid mem1 ld h L ∧ ScalarApprox (1+1/(2:ℝ)^q) (Num.fixVal mem1 ld h L P)
            (Num.IPM.arrayLength mem lo f up a h L P 0) ∧ Num.Valid mem1 gd h L ∧
          |Num.fixVal mem1 gd h L P-Num.IPM.arrayGradient mem m c r lo f up a h L P 0|≤
            (1/(2:ℝ)^q)*Num.IPM.arrayLength mem lo f up a h L P 0
        refine ⟨by omega,hhi0,hv1 ▸ hfresh1,?_,hvl1,?_,hvg1,?_⟩
        · intro z hz h0 h1
          exact (hframe1 z h0 h1).trans (hframe0 z (by omega))
        · have he : Num.fixVal mem1 ld h L P=Num.fixVal mem0 (mem0 (v0-1)) h L P := by
            unfold Num.fixVal
            rw [hvalL]
          rw [he]; exact hl
        · have he : Num.fixVal mem1 gd h L P=Num.fixVal mem0 (v0-1-L) h L P := by
            unfold Num.fixVal
            rw [hvalG]
          rw [he]; exact hg
      · simp only [edgeCoefficientRefreshContract,scalarCoefficientRefreshContract,storeCoefficientsContract,
          List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
          Expr.size_const,Expr.size_load,argsSize_cons,argsSize_nil]
        omega

end MinCostFlow.IPM.Machine
