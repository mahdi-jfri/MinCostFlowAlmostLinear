module

public import MinCostFlow.Scaling.ObjectiveScanFacts
public import MinCostFlow.Scaling.SignedScaleProgram
public import MinCostFlow.Scaling.SignedAddProgram
public import MinCostFlow.Scaling.SolverContract
import MinCostFlow.Scaling.InputLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# A machine scan for integer objectives

Read each edge's signed cost and unsigned flow. Recursively sum the
remaining edges, multiply the current cost by its flow, and add the two
signed values. A sum of absolute products bounds all arithmetic. Each edge
uses four fresh words and constant time.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[records,flows,count,heap]`. -/
def objectiveScanBody (self scale add : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0))
    (.call 4 scale [.const 0,.const 0,.const 0,.reg 3] ;; .ret (.reg 4))
    (.assign 4 (.load (.bin .add (.reg 0) (.const 3))) ;;
     .assign 5 (.load (.bin .add (.reg 0) (.const 4))) ;;
     .assign 6 (.load (.reg 1)) ;;
     .call 7 self [.bin .add (.reg 0) (.const 5),.bin .add (.reg 1) (.const 1),
       .bin .sub (.reg 2) (.const 1),.reg 3] ;;
     .call 8 scale [.reg 4,.reg 5,.reg 6,.reg 7] ;;
     .call 9 add [.load (.reg 7),.load (.bin .add (.reg 7) (.const 1)),
       .load (.bin .sub (.reg 7) (.const 2)),.load (.bin .sub (.reg 7) (.const 1)),.reg 8] ;;
     .ret (.reg 9))

/-- The scan, exact signed multiplication, and exact signed addition. -/
def objectiveScanModule (b : ℕ) : List Stmt :=
  objectiveScanBody b (b+1) (b+3) :: (signedScaleModule (b+1) ++ signedAddModule (b+3))

/-- The result occupies the final two words before the returned heap. -/
def objectiveScanContract (w : ℕ) (J : Circulation) (f : Fin J.m → ℕ)
    (es : List (Fin J.m)) : Contract :=
  let H := heapContract w
    (fun args mem => ∃ a flow heap,args=[a,flow,es.length,heap] ∧
      ListAt mem a (es.flatMap J.solverEdgeWords) ∧ ListAt mem flow (es.map f) ∧
      a+5*es.length ≤ heap ∧ flow+es.length ≤ heap ∧
      (∀ e ∈ es,(J.cost e).natAbs<2^w ∧ f e<2^w) ∧
      objectiveScanMass J f es<2^w ∧ 8<2^w)
    (fun _ _ _ => True) (fun _ _ => 500*es.length+150) (fun _ _ => 4*es.length+2)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧
      ret=heapArg args+4*es.length+2 ∧
      ListAt mem' (ret-2) (encodeInt (objectiveScan J f es)) }

/-- All objective scan procedures are deterministic. -/
theorem objectiveScanModule_noRand (b : ℕ) : ∀ body ∈ objectiveScanModule b,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [objectiveScanBody,Stmt.NoRand,and_self]
  · rcases List.mem_append.mp hb with hs | ha
    · exact signedScaleModule_noRand _ body hs
    · exact signedAddModule_noRand _ body ha

/-- The scan computes the exact signed integer objective over an ordered
edge list, preserves the source arrays, and has linear cost and allocation. -/
theorem objectiveScan_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (objectiveScanModule b)) (J : Circulation) (f : Fin J.m → ℕ)
    (es : List (Fin J.m)) : MeetsContract w p b (objectiveScanContract w J f es) := by
  have hscale := hasAt_append_left (hasAt_tail hp)
  have hadd : p.HasAt (b+3) (signedAddModule (b+3)) := by
    simpa only [signedScaleModule,List.length_cons,List.length_nil,Nat.add_assoc] using
      hasAt_append_right (hasAt_tail hp)
  induction es with
  | nil =>
    have hk := signedScale_meetsContract (w := w) hscale 0 0
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,flow,heap,rfl,_,_,_,_,_,_,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+2<2^w at hs
    have hh : heap<2^w := by omega
    have hzword : 0<2^w := by omega
    apply runs_start_le
    unfold objectiveScanBody
    wram_step
    · refine runs_seq_call_le hk (vs := [0,0,0,heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨heap,rfl,by simp⟩,hz,hs⟩
      · intro ret memR posR hpost
        obtain ⟨⟨hlo,hhi,hframe,hzR,hat⟩,hret⟩ := hpost
        change ret=heap+2 at hret
        have hr : ret<2^w := by omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · change (heap≤ret ∧ ret≤heap+2 ∧ (∀ x<heap,memR x=mem x) ∧ ZeroFrom memR ret ∧ True) ∧
            ret=heap+2 ∧ ListAt memR (ret-2) (encodeInt (objectiveScan J f []))
          refine ⟨⟨hlo,hhi,hframe,hzR,True.intro⟩,hret,?_⟩
          change ListAt memR heap (encodeInt (0*(0 : ℤ))) at hat
          simpa only [hret,Nat.add_sub_cancel,objectiveScan,List.map_nil,List.sum_nil,Int.zero_mul] using hat
        · simp only [objectiveScanContract,signedScaleContract,heapContract,List.length_nil,
            Nat.mul_zero,Nat.zero_add,Expr.size_bin,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil]
          omega
    · simp at hcond
  | cons e es ih =>
    have hkM := signedScale_meetsContract (w := w) hscale (J.cost e) (f e)
    have hkA := signedAdd_meetsContract (w := w) hadd (J.cost e*(f e : ℤ)) (objectiveScan J f es)
    apply meetsContract_of_runs hp.head
    intro args mem pos ω hwords hpre
    obtain ⟨⟨a,flow,heap,rfl,hat,hflow,hend,hfend,hvalues,hbudget,hw⟩,hz,hs⟩ := hpre
    change ZeroFrom mem heap at hz
    change heap+(4*(e::es).length+2)<2^w at hs
    obtain ⟨hhead,htail⟩ := listAt_append.mp hat
    change ListAt mem a (J.solverEdgeWords e) at hhead
    change ListAt mem (a+5) (es.flatMap J.solverEdgeWords) at htail
    obtain ⟨hflowhead,hflowtail⟩ := listAt_cons.mp hflow
    have hsigncell : mem (a+3)=(if J.cost e<0 then 1 else 0) := by
      have h := hhead 3 (by change 3<5; decide)
      simpa only [Circulation.solverEdgeWords,List.getElem_cons_succ,List.getElem_cons_zero] using h
    have hmagcell : mem (a+4)=(J.cost e).natAbs := by
      have h := hhead 4 (by change 4<5; decide)
      simpa only [Circulation.solverEdgeWords,List.getElem_cons_succ,List.getElem_cons_zero] using h
    have hcost := (hvalues e List.mem_cons_self).1
    have hflowword := (hvalues e List.mem_cons_self).2
    rw [objectiveScanMass_cons] at hbudget
    have hprod : (J.cost e).natAbs*f e<2^w := by omega
    have hsum : (J.cost e*(f e : ℤ)).natAbs+(objectiveScan J f es).natAbs<2^w := by
      have htailBound := objectiveScan_natAbs_le J f es
      simp only [Int.natAbs_mul,Int.natAbs_natCast]
      omega
    simp only [List.length_cons] at hs hend hfend
    have hh : heap<2^w := by omega
    have ha3 : a+3<2^w := by omega
    have ha4 : a+4<2^w := by omega
    have ha5 : a+5<2^w := by omega
    have hfw : flow<2^w := by omega
    have hfw1 : flow+1<2^w := by omega
    have htailLen : es.length<2^w := by omega
    have hsignword : (if J.cost e<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
    apply runs_start_le
    unfold objectiveScanBody
    wram_step
    · simp at hcond
    · refine runs_seq_assign_le (v := if J.cost e<0 then 1 else 0) (by eval_expr) ?_
      refine runs_seq_assign_le (v := (J.cost e).natAbs) (by eval_expr) ?_
      refine runs_seq_assign_le (v := f e) (by eval_expr) ?_
      refine runs_seq_call_le ih (vs := [a+5,flow+1,es.length,heap]) (by
        have heq : (e::es).length-1=es.length := rfl
        rw [←heq]
        eval_expr) (by wram_words) ?_ ?_
      · refine ⟨⟨a+5,flow+1,heap,rfl,htail,hflowtail,by omega,by omega,
          (fun e' he' => hvalues e' (List.mem_cons_of_mem e he')),by omega,hw⟩,hz,?_⟩
        change heap+(4*es.length+2)<2^w
        omega
      · intro tailEnd memT posT hpostT
        obtain ⟨⟨_,_,hframeT,hzT,_⟩,htailEnd,htailValue⟩ := hpostT
        change tailEnd=heap+4*es.length+2 at htailEnd
        change ZeroFrom memT tailEnd at hzT
        change (∀ x<heap,memT x=mem x) at hframeT
        change ListAt memT (tailEnd-2) (encodeInt (objectiveScan J f es)) at htailValue
        have htw : tailEnd<2^w := by omega
        have ht2 : tailEnd+2<2^w := by omega
        refine runs_seq_call_le hkM (vs := [if J.cost e<0 then 1 else 0,(J.cost e).natAbs,f e,tailEnd])
          (by eval_expr) (by wram_words) ⟨⟨tailEnd,rfl,hprod⟩,hzT,ht2⟩ ?_
        intro productEnd memM posM hpostM
        obtain ⟨⟨_,_,hframeM,hzM,hproduct⟩,hproductEnd⟩ := hpostM
        change productEnd=tailEnd+2 at hproductEnd
        change ZeroFrom memM productEnd at hzM
        change (∀ x<tailEnd,memM x=memT x) at hframeM
        change ListAt memM tailEnd (encodeInt (J.cost e*(f e : ℤ))) at hproduct
        have htailValueM := htailValue.of_agree_below (h₀ := tailEnd)
          (by simp only [encodeInt_length]; omega) hframeM
        obtain ⟨hpSign,hpMag⟩ := listAt_cons.mp hproduct
        obtain ⟨hpMag,_⟩ := listAt_cons.mp hpMag
        obtain ⟨htSign,htMag⟩ := listAt_cons.mp htailValueM
        obtain ⟨htMag,_⟩ := listAt_cons.mp htMag
        have hmword : productEnd<2^w := by omega
        have htsub : tailEnd-2<2^w := by omega
        have htsub1 : tailEnd-1<2^w := by omega
        have hp1 : tailEnd+1<2^w := by omega
        have hpmag : (J.cost e*(f e : ℤ)).natAbs<2^w := by simp only [Int.natAbs_mul,Int.natAbs_natCast]; exact hprod
        have htmag : (objectiveScan J f es).natAbs<2^w := by omega
        have hpsword : (if J.cost e*(f e : ℤ)<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
        have htsword : (if objectiveScan J f es<0 then 1 else 0 : ℕ)<2^w := by split <;> omega
        have htMag' : memM (tailEnd-1)=(objectiveScan J f es).natAbs := by
          have heq : tailEnd-2+1=tailEnd-1 := by omega
          rw [←heq]; exact htMag
        refine runs_seq_call_le hkA (vs := [if J.cost e*(f e : ℤ)<0 then 1 else 0,
          (J.cost e*(f e : ℤ)).natAbs,if objectiveScan J f es<0 then 1 else 0,
          (objectiveScan J f es).natAbs,productEnd]) (by
            eval_expr
            all_goals apply Expr.memAt_of_eq
            all_goals first
              | simpa only [htailEnd] using hpSign
              | simpa only [htailEnd] using hpMag
              | simpa only [htailEnd] using htSign
              | simpa only [htailEnd] using htMag') (by wram_words)
          ⟨⟨productEnd,rfl,hsum⟩,hzM,by change productEnd+2<2^w; omega⟩ ?_
        intro ret memR posR hpostR
        obtain ⟨⟨_,_,hframeR,hzR,hresult⟩,hret⟩ := hpostR
        change ret=productEnd+2 at hret
        change ZeroFrom memR ret at hzR
        change (∀ x<productEnd,memR x=memM x) at hframeR
        change ListAt memR productEnd (encodeInt (J.cost e*(f e : ℤ)+objectiveScan J f es)) at hresult
        have hr : ret<2^w := by omega
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · change (heap≤ret ∧ ret≤heap+(4*(e::es).length+2) ∧ (∀ x<heap,memR x=mem x) ∧
            ZeroFrom memR ret ∧ True) ∧ ret=heap+4*(e::es).length+2 ∧ ListAt memR (ret-2) (encodeInt (objectiveScan J f (e::es)))
          refine ⟨⟨by omega,by simp only [List.length_cons]; omega,?_,hzR,True.intro⟩,
            by rw [hret,hproductEnd,htailEnd]; simp only [List.length_cons]; omega,?_⟩
          · intro x hx
            exact (hframeR x (by omega)).trans ((hframeM x (by omega)).trans (hframeT x hx))
          · rw [objectiveScan_cons]
            have heq : ret-2=productEnd := by omega
            rw [heq]
            exact hresult
        · simp only [objectiveScanContract,signedScaleContract,signedAddContract,heapContract,
            List.length_cons,Expr.size_bin,Expr.size_reg,Expr.size_const,Expr.size_load,argsSize_cons,argsSize_nil]
          omega

end MinCostFlow.Scaling.Machine
