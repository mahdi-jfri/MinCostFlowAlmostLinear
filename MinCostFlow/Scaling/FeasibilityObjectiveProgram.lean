module

public import MinCostFlow.Scaling.IntegerObjectiveProgram
public import MinCostFlow.Scaling.DemandMassProgram
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Testing the exact feasibility objective threshold

The first circulation solve in the general-flow reduction succeeds when
its integer objective equals minus the total artificial capacity. Compute
the demand mass and the objective with the proved scans. Comparing their
canonical sign and magnitude words then returns exactly this equality's
indicator. In particular, mass zero uses the canonical zero sign.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[graph,unsignedFlow,signedDemands,vertexCount,heap]`. -/
def feasibilityObjectiveBody (mass objective : ℕ) : Stmt :=
  .call 5 mass [.reg 2,.reg 3] ;;
  .call 6 objective [.reg 0,.reg 1,.reg 4] ;;
  .assign 7 (.bin .sub (.reg 6) (.const 2)) ;;
  .cond (.bin .eq (.load (.reg 7)) (.bin .lt (.const 0) (.reg 5)))
    (.cond (.bin .eq (.load (.bin .add (.reg 7) (.const 1))) (.reg 5))
      (.ret (.const 1)) (.ret (.const 0)))
    (.ret (.const 0))

/-- The threshold entry, mass scan, and complete objective scan. -/
def feasibilityObjectiveModule (b : ℕ) : List Stmt :=
  feasibilityObjectiveBody (b+1) (b+2) ::
    (demandMassModule (b+1) ++ integerObjectiveModule (b+2))

/-- Exact integer equality test, preserving every source cell. -/
def feasibilityObjectiveContract (w : ℕ) (J : Circulation) (f : Fin J.m → ℕ)
    {n : ℕ} (d : Fin n → ℤ) : Contract where
  pre args mem := ∃ graph flow demands heap,args=[graph,flow,demands,n,heap] ∧
    ListAt mem graph J.solverWords ∧ ListAt mem flow (List.ofFn f) ∧ SignedTableAt mem demands d ∧
    graph+J.solverWords.length≤heap ∧ flow+J.m≤heap ∧ demands+2*n≤heap ∧
    (∀ x∈J.solverWords,x<2^w) ∧ (∀ e,f e<2^w) ∧
    objectiveScanMass J f (List.finRange J.m)<2^w ∧
    ((List.ofFn d).map Int.natAbs).sum<2^w ∧ 8<2^w ∧
    ZeroFrom mem heap ∧ heap+(4*J.m+2)<2^w
  post args mem ret mem' :=
    ret=(if J.integerObjective (fun e => (f e : ℤ)) = -(((List.ofFn d).map Int.natAbs).sum : ℤ) then 1 else 0) ∧
    ZeroFrom mem' (heapArg args+4*J.m+2) ∧ ∀ x<heapArg args,mem' x=mem x
  cost _ _ := 500*J.m+40*n+400

/-- The exact feasibility threshold test uses no random instruction. -/
theorem feasibilityObjectiveModule_noRand (b : ℕ) : ∀ body∈feasibilityObjectiveModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [feasibilityObjectiveBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hb | hb
    · exact demandMassModule_noRand _ body hb
    · exact integerObjectiveModule_noRand _ body hb

private theorem negative_mass_encoding (z : ℤ) (mass : ℕ) :
    ((if z<0 then 1 else 0 : ℕ)=(if 0<mass then 1 else 0) ∧ z.natAbs=mass) ↔ z=-(mass : ℤ) := by
  cases z <;> by_cases hm : 0<mass
  all_goals simp_all
  all_goals omega

/-- The objective and demand scans, followed by the canonical pair test,
compute exactly the feasibility branch condition with linear total cost. -/
theorem feasibilityObjective_meetsContract {w b n : ℕ} {p : Program}
    (hp : p.HasAt b (feasibilityObjectiveModule b)) (J : Circulation) (f : Fin J.m → ℕ)
    (d : Fin n → ℤ) : MeetsContract w p b (feasibilityObjectiveContract w J f d) := by
  have ht := hasAt_tail hp
  have hM := hasAt_append_left ht
  have hO : p.HasAt (b+2) (integerObjectiveModule (b+2)) := hasAt_append_right ht
  have hkM := demandMass_meetsContract (w := w) hM (List.ofFn d)
  have hkO := integerObjective_meetsContract (w := w) hO J f
  let z := J.integerObjective (fun e => (f e : ℤ))
  let total := ((List.ofFn d).map Int.natAbs).sum
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨graph,flow,demands,heap,rfl,hgraph,hflow,hd,hge,hfe,hde,hinput,hf,hobj,hmass,h8,hz,hs⟩ := hpre
  have hh : heap<2^w := by omega
  have hg : graph<2^w := by rw [J.solverWords_length] at hge; omega
  have hfl : flow<2^w := by omega
  have hdm : demands<2^w := by omega
  have hn : n<2^w := by omega
  have htotal : total<2^w := hmass
  apply runs_start_le
  unfold feasibilityObjectiveBody
  refine runs_seq_call_le hkM (vs := [demands,n]) (by eval_expr) (by wram_words) ?_ ?_
  · refine ⟨demands,by rw [List.length_ofFn],hd.listAt,?_,hmass,by omega⟩
    rw [List.length_ofFn]; omega
  · intro mass memM posM hpostM
    obtain ⟨hmemM,hmassEq⟩ := hpostM
    change memM=mem at hmemM
    change mass=total at hmassEq
    subst memM
    have hmassWord : mass<2^w := by omega
    refine runs_seq_call_le hkO (vs := [graph,flow,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨graph,flow,heap,rfl,hgraph,hflow,hge,hfe,hinput,hf,hobj,h8⟩,hz,hs⟩
    · intro out memO posO hpostO
      obtain ⟨⟨_,_,hframe,hzO,_⟩,hout,hvalue⟩ := hpostO
      change out=heap+4*J.m+2 at hout
      change ListAt memO (out-2) (encodeInt z) at hvalue
      change (∀ x<heap,memO x=mem x) at hframe
      change ZeroFrom memO out at hzO
      have how : out<2^w := by omega
      have hptr : out-2<2^w := by omega
      have hptr1 : out-2+1<2^w := by omega
      have hsign : memO (out-2)=(if z<0 then 1 else 0) := hvalue 0 (by change 0<2; omega)
      have hmag : memO (out-2+1)=z.natAbs := hvalue 1 (by change 1<2; omega)
      refine runs_seq_assign_le (v := out-2) (by eval_expr) ?_
      wram_step
      · have hsignEq : (if z<0 then 1 else 0 : ℕ)=(if 0<total then 1 else 0) := by
          simpa only [hsign,hmassEq] using hcond
        wram_step
        · have heq : z=-(total : ℤ) := (negative_mass_encoding z total).mp ⟨hsignEq,by simpa only [hmag,hmassEq] using hcond⟩
          refine runs_ret_le (v := 1) (by eval_expr) ?_ ?_
          · change 1=(if z=-(total : ℤ) then 1 else 0) ∧
              ZeroFrom memO (heap+4*J.m+2) ∧ ∀ x<heap,memO x=mem x
            exact ⟨by simp only [heq,↓reduceIte],by simpa only [hout] using hzO,hframe⟩
          · simp only [feasibilityObjectiveContract,integerObjectiveContract,demandMassContract,heapContract,
              List.length_ofFn,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
            omega
        · have hne : z≠-(total : ℤ) := by
            intro heq
            have h := (negative_mass_encoding z total).mpr heq
            exact hcond (by simpa only [hmag,hmassEq] using h.2)
          refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
          · change 0=(if z=-(total : ℤ) then 1 else 0) ∧
              ZeroFrom memO (heap+4*J.m+2) ∧ ∀ x<heap,memO x=mem x
            exact ⟨by simp only [hne,↓reduceIte],by simpa only [hout] using hzO,hframe⟩
          · simp only [feasibilityObjectiveContract,integerObjectiveContract,demandMassContract,heapContract,
              List.length_ofFn,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
            omega
      · have hne : z≠-(total : ℤ) := by
          intro heq
          have h := (negative_mass_encoding z total).mpr heq
          exact hcond (by simpa only [hsign,hmassEq] using h.1)
        refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
        · change 0=(if z=-(total : ℤ) then 1 else 0) ∧
            ZeroFrom memO (heap+4*J.m+2) ∧ ∀ x<heap,memO x=mem x
          exact ⟨by simp only [hne,↓reduceIte],by simpa only [hout] using hzO,hframe⟩
        · simp only [feasibilityObjectiveContract,integerObjectiveContract,demandMassContract,heapContract,
            List.length_ofFn,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
          omega

end MinCostFlow.Scaling.Machine
