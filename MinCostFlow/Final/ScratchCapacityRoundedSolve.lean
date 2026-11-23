module

public import MinCostFlow.Final.ScratchZeroSolve
public import MinCostFlow.Scaling.CapacityRoundedSolveProgram
import MinCostFlow.Scaling.SolverOutputLayout
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.ClearExclamation

/-!
# Rounded capacity solves with polynomial scratch

The zero case writes a zero flow. For a positive scale, the program solves
the clipped circulation with the selected scratch and restores capacity units.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM Scaling Scaling.Machine

/-- Entry, zero fill, shared arithmetic, graph construction, exact solve,
and unsigned multiplication back to original capacity units. -/
def scratchCapacityRoundedSolveModule (solver : Program) (f b c d : ℕ) : List Stmt :=
  let scale := b+11+(scratchZeroSolveModule solver f (b+11) c d).length
  capacityRoundedSolveBody (b+1) (b+2) (b+3) (b+4) (b+11) scale ::
    wordFillBody (b+1) :: capacityPowerBody :: capacityUnitBody ::
      (capacityScaledGraphModule (b+4) ++ scratchZeroSolveModule solver f (b+11) c d ++ unsignedScaleModule scale)

/-- The local clipping product fits. Guest space is needed only for a
positive magnitude. The returned flow is exactly the model value. -/
def scratchCapacityRoundedSolveContract (w : ℕ) (solver : Program) (f : ℕ) (T S : ℕ → ℕ → ℕ) (c d : ℕ)
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (J : Circulation) (B : ℕ) : Contract :=
  let K := J.scaledRoundedInstance B
  let g := wordSize (scratchWordMultiplier c d) K.positiveInstance.solverWords
  let space := if B = 0 then J.m else 5+12*J.m+2^g
  let H := heapContract w
    (fun args mem => ∃ a heap,args = [a,B,heap] ∧ ListAt mem a J.solverWords ∧
      a+J.solverWords.length ≤ heap ∧ (∀ x ∈ J.solverWords,x < 2^w) ∧
      0 < J.m ∧ B*J.m^20 < 2^w ∧ (B = 0 ∨ 2^(g+1)+2 ≤ 2^w) ∧ 8 < 2^w)
    (fun _ _ _ => True)
    (fun _ _ => if B = 0 then 40*J.m+100 else
      (solver.regBound+6)*T (J.n+1) J.m+80*K.positiveInstance.solverWords.length+
        40*g+solver.regBound+680*J.m+1600)
    (fun _ _ => space)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret = heapArg args+space ∧
      ListAt mem' (ret-J.m) (List.ofFn
        (fun e => ((J.solveCapacityRoundedModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) B).value e).toNat)) }

/-- The entire rounded solve contains no random instruction when its solver is deterministic. -/
theorem scratchCapacityRoundedSolveModule_noRand (solver : Program) (f b c d : ℕ) (hdet : solver.IsDeterministic) :
    ∀ body ∈ scratchCapacityRoundedSolveModule solver f b c d,body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [capacityRoundedSolveBody,Stmt.NoRand,and_self]
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact wordFillBody_noRand _
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact capacityPowerBody_noRand
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact capacityUnitBody_noRand
        · rcases List.mem_append.mp hb with hb | hb
          · rcases List.mem_append.mp hb with hb | hb
            · exact capacityScaledGraphModule_noRand _ body hb
            · exact scratchZeroSolveModule_noRand solver f _ c d hdet body hb
          · have he : body = unsignedScaleBody (b+11+(scratchZeroSolveModule solver f (b+11) c d).length) := by
              simpa only [unsignedScaleModule,List.mem_singleton] using hb
            subst body
            exact unsignedScaleBody_noRand _

private theorem capacityRoundedSolve_source_eval {w : ℕ} {st : State} {heap count : ℕ}
    (hh : st.regs 7 = heap) (hc : st.regs 3 = count) (hheap : heap < 2^w) :
    Expr.eval w st (.bin .sub (.reg 7) (.reg 3)) = some (heap-count) := by eval_expr

private theorem capacityRoundedSolve_scale_args {w : ℕ} {st : State} {src count unit heap : ℕ}
    (hs : st.regs 8 = src) (hc : st.regs 3 = count)
    (hu : st.regs 5 = unit) (hh : st.regs 7 = heap) :
    evalArgs w st [.reg 8,.reg 3,.reg 5,.reg 7] = some [src,count,unit,heap] := by eval_expr

private theorem capacityRoundedSolve_scale_words {src count unit heap limit : ℕ}
    (hs : src < limit) (hc : count < limit) (hu : unit < limit) (hh : heap < limit) :
    ∀ x ∈ [src,count,unit,heap],x < limit := by
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> assumption

set_option maxHeartbeats 400000 in
/-- Positive-capacity rounding, its exact solve, and rescaling compute
exactly `solveCapacityRoundedModel.value`, including its zero-magnitude branch. -/
theorem scratchCapacityRoundedSolve_meetsContract {w b : ℕ} {p solver : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ} {c d : ℕ}
    (hproc : ∀ J : Circulation, MeetsContract (wordSize (scratchWordMultiplier c d) J.solverWords)
      solver f (compressedSolverContract (wordSize (scratchWordMultiplier c d) J.solverWords) T S))
    (hS : ∀ n m, S n m ≤ c * (n + m + 2)^d)
    (hdet : solver.IsDeterministic) (hp : p.HasAt b (scratchCapacityRoundedSolveModule solver f b c d))
    (J : Circulation) (hnGraph : J.n ≤ 2*J.m) (B : ℕ) (hc : J.CostsBounded (J.m^10)) :
    MeetsContract w p b (scratchCapacityRoundedSolveContract w solver f T S c d hproc J B) := by
  let K := J.scaledRoundedInstance B
  let g := wordSize (scratchWordMultiplier c d) K.positiveInstance.solverWords
  have hKm : K.m = J.m := rfl
  let unit := capacityUnit J.m B
  let delta := Circulation.solveWithZeroCapacities ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) K
  have htail := hasAt_tail hp
  have hfill : p.HasAt (b+1) (wordFillModule (b+1)) := by
    intro i hi
    have hi0 : i=0 := by change i<1 at hi; omega
    subst i
    simpa only [wordFillModule,List.getElem_cons_zero,Nat.add_zero] using htail.head
  have hpower : p.HasAt (b+2) capacityPowerModule := by
    intro i hi
    have hi0 : i=0 := by change i<1 at hi; omega
    subst i
    simpa only [capacityPowerModule,List.getElem_cons_zero,Nat.add_zero,Nat.add_assoc] using (hasAt_tail htail).head
  have hunit : p.HasAt (b+3) capacityUnitModule := by
    intro i hi
    have hi0 : i=0 := by change i<1 at hi; omega
    subst i
    simpa only [capacityUnitModule,List.getElem_cons_zero,Nat.add_zero,Nat.add_assoc] using (hasAt_tail (hasAt_tail htail)).head
  have hmodules := hasAt_tail (hasAt_tail (hasAt_tail htail))
  have hleft := hasAt_append_left hmodules
  have hgraph : p.HasAt (b+4) (capacityScaledGraphModule (b+4)) := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using hasAt_append_left hleft
  have hsolve : p.HasAt (b+11) (scratchZeroSolveModule solver f (b+11) c d) := by
    have h := hasAt_append_right hleft
    have hl : (capacityScaledGraphModule (b+4)).length = 7 := rfl
    simpa only [hl,Nat.add_assoc,Nat.reduceAdd] using h
  have hscale : p.HasAt (b+11+(scratchZeroSolveModule solver f (b+11) c d).length)
      (unsignedScaleModule (b+11+(scratchZeroSolveModule solver f (b+11) c d).length)) := by
    have h := hasAt_append_right hmodules
    rw [List.length_append] at h
    have hl : (capacityScaledGraphModule (b+4)).length = 7 := rfl
    have hidx : b+1+1+1+1+(7+(scratchZeroSolveModule solver f (b+11) c d).length) =
        b+11+(scratchZeroSolveModule solver f (b+11) c d).length := by omega
    simpa only [hl,hidx] using h
  have hkF := wordFill_meetsContract (w := w) hfill J.m 0
  have hkP := capacityPower_meetsContract (w := w) hpower J.m
  have hkU := capacityUnit_meetsContract (w := w) hunit J.m B
  have hkG := capacityScaledGraph_meetsContract (w := w) hgraph J B
  have hkA := unsignedScale_meetsContract (w := w) hscale unit (List.ofFn (fun e => (delta e).toNat))
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,heap,rfl,hat,hend,hinput,hmpos,hproduct,hguest,hw⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+(if B=0 then J.m else 5+12*J.m+2^g) < 2^w at hs
  have hm : J.m < 2^w := hinput _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hB : B < 2^w := hwords _ (by simp)
  have hregion0 : 0 < 2^g := Nat.two_pow_pos g
  have hh : heap < 2^w := by split_ifs at hs <;> omega
  have ha1 : a+1 < 2^w := by rw [J.solverWords_length] at hend; omega
  have hM := (solver_header_at J hat).2
  apply runs_start_le
  unfold capacityRoundedSolveBody
  refine runs_seq_assign_le (v := J.m) (by clear! solver T K g delta hinput hc; eval_expr) ?_
  wram_step
  · have hBzero : B=0 := by simpa only [startState,Function.update_of_ne (by decide : 1 ≠ 3),List.getD_cons_succ,List.getD_cons_zero] using hcond
    have hs0 : heap+J.m < 2^w := by simpa only [hBzero,↓reduceIte] using hs
    refine runs_seq_call_le hkF (vs := [J.m,0,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨heap,rfl,by omega,by omega⟩,hz,hs0⟩
    · intro ret memF posF hpostF
      obtain ⟨⟨_,_,hframeF,hzF,hatF⟩,hret⟩ := hpostF
      change ret=heap+J.m at hret
      change (∀ x < heap,memF x = mem x) at hframeF
      change ZeroFrom memF ret at hzF
      change ListAt memF heap (List.replicate J.m 0) at hatF
      have hr : ret < 2^w := by omega
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change (heap ≤ ret ∧ ret ≤ heap+(if B=0 then J.m else 5+12*J.m+2^g) ∧
          (∀ x < heap,memF x = mem x) ∧ ZeroFrom memF ret ∧ True) ∧
          ret=heap+(if B=0 then J.m else 5+12*J.m+2^g) ∧ ListAt memF (ret-J.m) _
        simp only [hBzero,↓reduceIte,Circulation.solveCapacityRoundedModel,
          Int.toNat_zero,List.ofFn_const]
        refine ⟨⟨by omega,by omega,hframeF,hzF,True.intro⟩,hret,?_⟩
        have heq : ret-J.m=heap := by omega
        simpa only [heq] using hatF
      · simp only [scratchCapacityRoundedSolveContract,hBzero,↓reduceIte,heapContract,wordFillContract,
          Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil]
        omega
  · have hBne : B≠0 := by simpa only [startState,Function.update_of_ne (by decide : 1 ≠ 3),List.getD_cons_succ,List.getD_cons_zero] using hcond
    have hBpos : 0 < B := Nat.pos_of_ne_zero hBne
    have hspace : heap+(5+12*J.m+2^g) < 2^w := by simpa only [hBne,↓reduceIte] using hs
    have hregion : 0 < 2^g := Nat.two_pow_pos g
    have hpow : J.m^20 < 2^w := by
      have hh' : J.m^20 ≤ B*J.m^20 := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (J.m^20) (Nat.succ_le_of_lt hBpos)
      exact hh'.trans_lt hproduct
    have hunitWord : unit < 2^w := (capacityUnit_le J.m B hmpos hBpos).trans_lt hB
    have hguest' : 2^(g+1)+2 ≤ 2^w := hguest.resolve_left hBne
    have hcaps : ∀ e,K.capacity e ≤ K.m^40 := fun e => scaledCapacity_le J.m B (J.capacity e) hmpos hBpos
    have hcost : K.CostsBounded (K.m^10) := hc
    have hkS := compressedZeroSolve_meetsContract (w := w) hproc hdet K hnGraph hcost hcaps (hS _ _) hsolve
    have hopt : K.Optimal (fun e => (delta e : ℝ)) := by
      apply Circulation.solveWithZeroCapacities_of_optimal
      exact compressedCanonicalSolverAt_optimal _ solver f T S (hproc _) _
    have hnonneg : ∀ e,0 ≤ delta e := fun e => Int.cast_nonneg_iff.mp (hopt.1.2 e).1
    have hnatBound : ∀ e,(delta e).toNat ≤ K.capacity e := by
      intro e
      have hb : delta e ≤ (K.capacity e : ℤ) := Int.cast_le.mp (by simpa only [Int.cast_natCast] using (hopt.1.2 e).2)
      simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hb
    have hvalues : ∀ x ∈ List.ofFn (fun e => (delta e).toNat),x < 2^w ∧ unit*x < 2^w := by
      intro x hx
      obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hx
      have hu : J.capacity e < 2^w := hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
      have hcap : K.capacity e ≤ J.capacity e := (min_le_left _ _).trans (Nat.div_le_self _ _)
      have hmul : unit*(delta e).toNat ≤ J.capacity e := by
        apply (Nat.mul_le_mul_left unit (hnatBound e)).trans
        exact roundedCapacity_le J.m B (J.capacity e)
      exact ⟨((hnatBound e).trans hcap).trans_lt hu,hmul.trans_lt hu⟩
    have hKinput : ∀ x ∈ K.solverWords,x < 2^w := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hinput _ List.mem_cons_self
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hm
      obtain ⟨e,_,hx⟩ := List.mem_flatMap.mp hx
      rw [capacityScaled_edgeWords] at hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
      · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
      · exact ((min_le_left _ _).trans (Nat.div_le_self _ _)).trans_lt
          (hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords])))
      · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
      · exact hinput _ (J.solverEdgeWord_mem e (by simp [Circulation.solverEdgeWords]))
    have hresult : (List.ofFn (fun e => (delta e).toNat)).map (fun x => unit*x) =
        List.ofFn (fun e => ((J.solveCapacityRoundedModel ((fun K : Circulation => compressedCanonicalSolverAt
    (wordSize (scratchWordMultiplier c d) K.solverWords) solver f T S (hproc K) K)) B).value e).toNat) := by
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext e
      simp only [Function.comp_apply,Circulation.solveCapacityRoundedModel,hBne,↓reduceIte]
      change unit*(delta e).toNat = ((unit : ℤ)*delta e).toNat
      rw [Int.toNat_mul (Int.natCast_nonneg unit) (hnonneg e),Int.toNat_natCast]
    refine runs_seq_call_le hkP (vs := [J.m]) (by eval_expr) (by wram_words) ⟨rfl,hpow⟩ ?_
    intro power memP posP hpostP
    obtain ⟨hmemP,hpowerEq⟩ := hpostP
    subst memP
    subst power
    refine runs_seq_call_le hkU (vs := [J.m^20,B]) (by eval_expr) (by wram_words) ⟨rfl,hmpos,hBpos,hB⟩ ?_
    intro unitValue memU posU hpostU
    obtain ⟨hmemU,hunitEq⟩ := hpostU
    subst memU
    subst unitValue
    refine runs_seq_call_le hkG (vs := [a,B,heap]) (by eval_expr) hwords ?_ ?_
    · exact ⟨⟨a,heap,rfl,hat,hend,hinput,hmpos,hBpos,hproduct,hw⟩,hz,
        by change heap+(2+5*J.m) < 2^w; omega⟩
    · intro solveHeap memG posG hpostG
      obtain ⟨⟨_,_,hframeG,hzG,hatG⟩,hsolveHeap⟩ := hpostG
      change solveHeap=heap+2+5*J.m at hsolveHeap
      change (∀ x < heap,memG x = mem x) at hframeG
      change ZeroFrom memG solveHeap at hzG
      change ListAt memG heap K.solverWords at hatG
      have hsolveWord : solveHeap < 2^w := by omega
      refine runs_seq_call_le hkS (vs := [heap,solveHeap]) (by clear! solver T K g delta hinput hc; eval_expr)
        (by wram_words) ?_ ?_
      · refine ⟨⟨heap,solveHeap,rfl,hatG,?_,hKinput,hguest'⟩,hzG,?_⟩
        · rw [K.solverWords_length]
          change heap+(2+5*J.m) ≤ solveHeap
          omega
        · change solveHeap+(3+6*J.m+2^g) < 2^w
          omega
      · intro scaleHeap memS posS hpostS
        obtain ⟨⟨_,_,hframeS,hzS,hread⟩,hscaleHeap⟩ := hpostS
        change scaleHeap=solveHeap+3+6*J.m+2^g at hscaleHeap
        change (∀ x < solveHeap,memS x = memG x) at hframeS
        change ZeroFrom memS scaleHeap at hzS
        change K.readSolverFlow memS (solveHeap+3+5*J.m+2^g)=delta at hread
        have htable := solverOutput_listAt K hread
        have hscaleWord : scaleHeap < 2^w := by omega
        have hsourceWord : solveHeap+3+5*J.m+2^g < 2^w := by omega
        have hsource : scaleHeap-J.m=solveHeap+3+5*J.m+2^g := by omega
        refine runs_seq_assign_le (v := solveHeap+3+5*J.m+2^g) ?_ ?_
        · rw [← hsource]
          exact capacityRoundedSolve_source_eval (by rfl) (by rfl) hscaleWord
        · refine runs_seq_call_le hkA (vs := [solveHeap+3+5*J.m+2^g,J.m,unit,scaleHeap])
            (capacityRoundedSolve_scale_args (by rfl) (by rfl) (by rfl) (by rfl)) ?_ ?_ ?_
          · exact capacityRoundedSolve_scale_words hsourceWord hm hunitWord hscaleWord
          · refine ⟨⟨solveHeap+3+5*J.m+2^g,scaleHeap,by simp only [List.length_ofFn,hKm],htable,?_,hvalues,by omega⟩,hzS,?_⟩
            · rw [List.length_ofFn]
              change solveHeap+3+5*J.m+2^g+J.m ≤ scaleHeap
              omega
            · change scaleHeap+(List.ofFn (fun e => (delta e).toNat)).length < 2^w
              rw [List.length_ofFn]
              omega
          · intro ret memA posA hpostA
            obtain ⟨⟨_,_,hframeA,hzA,hatA⟩,hret⟩ := hpostA
            change ret=scaleHeap+(List.ofFn (fun e => (delta e).toNat)).length at hret
            rw [List.length_ofFn] at hret
            change (∀ x < scaleHeap,memA x = memS x) at hframeA
            change ZeroFrom memA ret at hzA
            change ListAt memA scaleHeap ((List.ofFn (fun e => (delta e).toNat)).map (fun x => unit*x)) at hatA
            rw [hresult] at hatA
            have hr : ret < 2^w := by omega
            refine runs_ret_le (v := ret) (by clear! solver T K g delta hinput hc; eval_expr) ?_ ?_
            · change (heap ≤ ret ∧ ret ≤ heap+(if B=0 then J.m else 5+12*J.m+2^g) ∧
                (∀ x < heap,memA x = mem x) ∧ ZeroFrom memA ret ∧ True) ∧
                ret=heap+(if B=0 then J.m else 5+12*J.m+2^g) ∧ ListAt memA (ret-J.m) _
              simp only [hBne,↓reduceIte]
              refine ⟨⟨by omega,by omega,?_,hzA,True.intro⟩,by omega,?_⟩
              · intro x hx
                exact (hframeA x (by omega)).trans ((hframeS x (by omega)).trans (hframeG x hx))
              · have heq : ret-J.m=scaleHeap := by omega
                simpa only [heq] using hatA
            · simp only [scratchCapacityRoundedSolveContract,hBne,↓reduceIte,heapContract,capacityPowerContract,
                capacityUnitContract,capacityScaledGraphContract,compressedZeroSolveContract,unsignedScaleContract,
                List.length_ofFn,argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
              change _ ≤ (solver.regBound+6)*T (J.n+1) J.m+80*K.positiveInstance.solverWords.length+
                40*g+solver.regBound+680*J.m+1600
              dsimp only [K,g]
              omega

end MinCostFlow.Final
