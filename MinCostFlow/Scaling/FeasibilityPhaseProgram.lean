module

public import MinCostFlow.Scaling.FeasibilityPhaseContract
import MinCostFlow.Scaling.FeasibilityPhaseFacts
import MinCostFlow.Scaling.PrunedScalingProgram
import MinCostFlow.Scaling.PrunedScalingOutputBounds
import MinCostFlow.Scaling.CirculationLayout
import MinCostFlow.Scaling.ModulePlacement
import Mathlib.Tactic.Ring
import WordRAM.Tactic

/-!
# Executing the full feasibility phase

Build the auxiliary circulation once and retain its shifted graph and
demand table. The exact pruned scaling output supplies nonnegative flow
coordinates. Copying their magnitudes and testing the objective yields
precisely the branch condition in the counted general-flow reduction.
The final header keeps that branch and the two arrays for the next phase.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem eleven_fits {w : ℕ} (h : 8<2^w) : 11<2^w := by
  have hw : 4≤w := by
    by_contra hn
    have hp : 2^w≤2^3 := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num only [Nat.reducePow] at hp
    omega
  exact (show 11<2^4 by decide).trans_le (Nat.pow_le_pow_right (by decide) hw)

/-- The complete first-solve phase returns the model's exact feasibility
flow and objective branch, with its counted scaling call and linear
additional machine work. -/
theorem feasibilityPhase_meetsContract {w b : ℕ} {p solver : Program} {entry : ℕ} {T : ℕ → ℕ → ℕ}
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hdet : solver.IsDeterministic) (hmono : SolverTimeMonotone T)
    (hp : p.HasAt b (feasibilityPhaseModule solver entry b)) (I : Instance) (hv : I.IsValid) (C U : ℕ) :
    MeetsContract w p b (feasibilityPhaseContract w solver entry T hproc I hv C U) := by
  let solve := b+1+(buildFeasibilityModule (b+1)).length
  let copy := solve+(prunedScalingModule solver entry solve).length
  let test := copy+1
  let header := test+(feasibilityObjectiveModule test).length
  let P := FlowReduction.buildFeasibilityInstance I hv
  let J := FlowReduction.shiftedGraph I hv
  let d := FlowReduction.buildShiftedDemands I hv
  let B := FlowReduction.scalingCapacityBudget I U
  let g := (Circulation.invokePruned
    (fun K => costCapacityModel (canonicalSolver solver entry T hproc) K C B) P).value
  let flag := if P.integerObjective g = -(J.demandMass (FlowReduction.shiftedDemand I) : ℤ) then 1 else 0
  have hPm : P.m=I.m+(I.n+I.n) := rfl
  have ht : p.HasAt (b+1) (buildFeasibilityModule (b+1) ++ (prunedScalingModule solver entry solve ++
      (magnitudeCopyModule copy ++ (feasibilityObjectiveModule test ++ costHeaderModule)))) := hasAt_tail hp
  have hbuild := hasAt_append_left ht
  have htS : p.HasAt solve (prunedScalingModule solver entry solve ++
      (magnitudeCopyModule copy ++ (feasibilityObjectiveModule test ++ costHeaderModule))) := hasAt_append_right ht
  have hsolve := hasAt_append_left htS
  have htC : p.HasAt copy (magnitudeCopyModule copy ++
      (feasibilityObjectiveModule test ++ costHeaderModule)) := hasAt_append_right htS
  have hcopy := hasAt_append_left htC
  have htT : p.HasAt test (feasibilityObjectiveModule test ++ costHeaderModule) := hasAt_append_right htC
  have htest := hasAt_append_left htT
  have hheader : p.HasAt header costHeaderModule := hasAt_append_right htT
  have hkB := buildFeasibility_meetsContract (w := w) hbuild I hv U
  have hkS := prunedScaling_meetsContract (w := w) hproc hdet hmono hsolve P C B
  have hkC := magnitudeCopy_meetsContract (w := w) hcopy (List.ofFn g)
  have hkT := feasibilityObjective_meetsContract (w := w) htest P (fun e => (g e).toNat) d
  have hkH := costHeader_meetsContract (w := w) hheader
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,heap,rfl,hinputAt,hinputEnd,horder,hd,hl,hu,hinput,hPinput,hC,h8,hbudget,hBword,hdMassWord,hObjWord,hz,hs⟩ := hpre
  have hlFin : ∀ e : Fin I.m,(I.edge e).lower.natAbs≤U := fun e => hl _ (List.getElem_mem e.isLt)
  have huFin : ∀ e : Fin I.m,(I.edge e).upper.natAbs≤U := fun e => hu _ (List.getElem_mem e.isLt)
  have hPC : P.CostsBounded C := fun e => (buildFeasibility_costs_le_one I hv e).trans hC
  have hcap := FlowReduction.buildFeasibilityInstance_capacity_le I hv U hd hlFin huFin
  have hBpos : 1≤B := by unfold B FlowReduction.scalingCapacityBudget; omega
  have hg := prunedScalingModel_output_bounds solver entry T hproc P C B hPC hcap hBpos
  have hg0 : ∀ e,0≤g e := fun e => (hg e).1
  have hgNat : ∀ e,(g e).toNat≤B := by
    intro e
    exact (Int.toNat_le_toNat (hg e).2).trans (by simpa only [Int.toNat_natCast] using hcap e)
  have hgAbs : ∀ e,(g e).natAbs<2^w := by
    intro e
    have he := congrArg Int.natAbs (Int.toNat_of_nonneg (hg0 e))
    simp only [Int.natAbs_natCast] at he
    rw [←he]
    exact (hgNat e).trans_lt hBword
  have hdMass : ((List.ofFn d).map Int.natAbs).sum<2^w :=
    (shiftedDemands_mass_le I hv U hd hlFin).trans_lt hdMassWord
  have hObj : objectiveScanMass P (fun e => (g e).toNat) (List.finRange P.m)<2^w :=
    (feasibilityObjective_mass_le solver entry T hproc I hv C U hC hd hlFin huFin).trans_lt hObjWord
  have hcast : (fun e => ((g e).toNat : ℤ))=g := by
    funext e
    exact Int.toNat_of_nonneg (hg0 e)
  have hflag : (if P.integerObjective (fun e => ((g e).toNat : ℤ)) =
      -(((List.ofFn d).map Int.natAbs).sum : ℤ) then 1 else 0)=flag := by
    rw [hcast,←demandMass_eq_magnitude_sum J d]
    dsimp only [d]
    simp only [FlowReduction.buildShiftedDemands_eq,flag]
  have hsNum := hs
  change heap+(4+16*I.m+12*I.n+prunedScalingSpace P C B+P.m+4*P.m+2+3)<2^w at hsNum
  have hlength := instance_encode_length I hv
  have hCword : C<2^w := hwords C (by simp)
  have hUword : U<2^w := hwords U (by simp)
  have hh : heap<2^w := by omega
  have ha : a<2^w := by rw [hlength] at hinputEnd; omega
  have ha1 : a+1<2^w := by rw [hlength] at hinputEnd; omega
  have hn : I.n<2^w := by omega
  have hm : I.m<2^w := by omega
  have h11 : 11<2^w := eleven_fits h8
  have h11m : 11*I.m<2^w := by omega
  have h2n : 2*I.n<2^w := by omega
  have h5m : 5*I.m<2^w := by omega
  have hh2 : heap+2<2^w := by omega
  have hPptr : heap+2+11*I.m+2*I.n<2^w := by omega
  have hDptr : heap+2+5*I.m<2^w := by omega
  have hpartial : heap+2+11*I.m<2^w := by omega
  have hnHead := (instance_header_at I mem a hinputAt).1
  have hmHead := (instance_header_at I mem a hinputAt).2
  apply runs_start_le
  unfold feasibilityPhaseBody
  refine runs_seq_assign_le (v := I.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := I.m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap+2+11*I.m+2*I.n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := heap+2+5*I.m) (by eval_expr) ?_
  refine runs_seq_call_le hkB (vs := [a,heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨a,heap,rfl,hinputAt,hinputEnd,horder,hd,hl,hu,hbudget,hinput,h8⟩,hz,
      by change heap+(4+16*I.m+12*I.n)<2^w; omega⟩
  · intro buildEnd memB posB hpostB
    obtain ⟨⟨_,_,hframeB,hzB,hPgraph⟩,hbuildEnd,hJgraph,hDtable⟩ := hpostB
    change buildEnd=heap+4+16*I.m+12*I.n at hbuildEnd
    change ListAt memB (heap+2+11*I.m+2*I.n) P.solverWords at hPgraph
    change ListAt memB heap J.solverWords at hJgraph
    change SignedTableAt memB (heap+2+5*I.m) d at hDtable
    change (∀ x<heap,memB x=mem x) at hframeB
    change ZeroFrom memB buildEnd at hzB
    have hbword : buildEnd<2^w := by omega
    have hm1 : I.m+1<2^w := by omega
    have htwom1 : 2*(I.m+1)<2^w := by omega
    have hprod : 2*(I.m+1)*U<2^w := by
      have he : 2*(I.m+1)*U=(2*I.m+2)*U := by ring
      rwa [he]
    refine runs_seq_assign_le (v := B) ?_ ?_
    · change Expr.eval w _ _=some (2*(I.m+1)*U+1)
      eval_expr
    · refine runs_seq_call_le hkS (vs := [heap+2+11*I.m+2*I.n,C,B,buildEnd]) (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨heap+2+11*I.m+2*I.n,buildEnd,rfl,hPgraph,?_,hPinput,h8,hPC,hcap,hBpos,hzB,?_⟩
        · rw [P.solverWords_length,hPm]; omega
        · omega
      · intro signedEnd memS posS hpostS
        obtain ⟨hloS,hhiS,hflowS,hzS,hframeS⟩ := hpostS
        change buildEnd≤signedEnd at hloS
        change signedEnd≤buildEnd+prunedScalingSpace P C B at hhiS
        change SignedTableAt memS (signedEnd-2*P.m) g at hflowS
        change (∀ x<buildEnd,memS x=memB x) at hframeS
        have hsword : signedEnd<2^w := by omega
        have hPgraphS := hPgraph.of_agree_below (h₀ := buildEnd)
          (by rw [P.solverWords_length,hPm]; omega) hframeS
        have hPmCell := (solver_header_at P hPgraphS).2
        have hPptr1 : heap+2+11*I.m+2*I.n+1<2^w := by omega
        have hpm : P.m<2^w := by omega
        have h2pm : 2*P.m<2^w := by rw [hPm]; omega
        have hflowptr : signedEnd-2*P.m<2^w := by omega
        have hflowsignedend : 2*P.m≤signedEnd := by rw [hPm]; omega
        refine runs_seq_assign_le (v := P.m) (by eval_expr) ?_
        refine runs_seq_call_le hkC (vs := [signedEnd-2*P.m,P.m,signedEnd]) (by eval_expr) (by wram_words) ?_ ?_
        · refine ⟨⟨signedEnd-2*P.m,signedEnd,by rw [List.length_ofFn],hflowS.listAt,?_,?_,by omega⟩,hzS,?_⟩
          · rw [List.length_ofFn]; omega
          · intro z hz
            obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hz
            exact hgAbs e
          · change signedEnd+(List.ofFn g).length<2^w
            rw [List.length_ofFn]; omega
        · intro unsignedEnd memC posC hpostC
          obtain ⟨⟨_,_,hframeC,hzC,hflowC⟩,hunsignedEnd⟩ := hpostC
          change unsignedEnd=signedEnd+(List.ofFn g).length at hunsignedEnd
          rw [List.length_ofFn] at hunsignedEnd
          change ListAt memC signedEnd ((List.ofFn g).map Int.natAbs) at hflowC
          rw [nonnegative_magnitudes_eq_unsigned g hg0] at hflowC
          change (∀ x<signedEnd,memC x=memS x) at hframeC
          change ZeroFrom memC unsignedEnd at hzC
          have huword : unsignedEnd<2^w := by omega
          have hPgraphC := hPgraphS.of_agree_below (h₀ := signedEnd)
            (by rw [P.solverWords_length,hPm]; omega) hframeC
          have hDtableC := (hDtable.of_agree_below (by omega)
            hframeS).of_agree_below (by omega) hframeC
          refine runs_seq_call_le hkT (vs := [heap+2+11*I.m+2*I.n,signedEnd,heap+2+5*I.m,I.n,unsignedEnd])
            (by eval_expr) (by wram_words) ?_ ?_
          · refine ⟨heap+2+11*I.m+2*I.n,signedEnd,heap+2+5*I.m,unsignedEnd,rfl,hPgraphC,hflowC,hDtableC,
              ?_,by omega,by omega,hPinput,fun e => (hgNat e).trans_lt hBword,hObj,hdMass,h8,hzC,?_⟩
            · rw [P.solverWords_length,hPm]; omega
            · omega
          · intro answer memT posT hpostT
            obtain ⟨hanswer,hzT,hframeT⟩ := hpostT
            change answer=(if P.integerObjective (fun e => ((g e).toNat : ℤ))=
              -(((List.ofFn d).map Int.natAbs).sum : ℤ) then 1 else 0) at hanswer
            rw [hflag] at hanswer
            change ZeroFrom memT (unsignedEnd+4*P.m+2) at hzT
            change (∀ x<unsignedEnd,memT x=memC x) at hframeT
            have haWord : answer<2^w := by rw [hanswer]; unfold flag; split <;> omega
            have h4pm : 4*P.m<2^w := by omega
            have hu4 : unsignedEnd+4*P.m<2^w := by omega
            have htword : unsignedEnd+4*P.m+2<2^w := by omega
            refine runs_seq_assign_le (v := unsignedEnd+4*P.m+2) (by eval_expr) ?_
            refine runs_seq_call_le hkH (vs := [answer,signedEnd,heap,unsignedEnd+4*P.m+2])
              (by eval_expr) (by wram_words) ⟨rfl,hzT,by change unsignedEnd+4*P.m+2+3<2^w; omega⟩ ?_
            intro out memH posH hpostH
            obtain ⟨⟨_,_,hframeH,hzH,hheaderH⟩,hout⟩ := hpostH
            change out=unsignedEnd+4*P.m+2+3 at hout
            change (∀ x<unsignedEnd+4*P.m+2,memH x=memT x) at hframeH
            change ZeroFrom memH out at hzH
            change ListAt memH (unsignedEnd+4*P.m+2) [answer,signedEnd,heap] at hheaderH
            have how : out<2^w := by omega
            refine runs_ret_le (v := out) (by eval_expr) ?_ ?_
            · change heap+2+5*I.m≤out ∧ out≤heap+feasibilityPhaseSpace I hv C U ∧
                ∃ flow,flow+P.m≤out ∧ ListAt memH flow (List.ofFn (fun e => (g e).toNat)) ∧
                  ListAt memH (out-3) [flag,flow,heap] ∧ ListAt memH heap J.solverWords ∧
                  ZeroFrom memH out ∧ ∀ x<heap,memH x=mem x
              refine ⟨by omega,?_,signedEnd,by omega,?_,?_,?_,hzH,?_⟩
              · change out≤heap+(4+16*I.m+12*I.n+prunedScalingSpace P C B+P.m+4*P.m+2+3)
                omega
              · apply (hflowC.of_agree_below (h₀ := unsignedEnd) ?_ hframeT).of_agree_below
                  (h₀ := unsignedEnd+4*P.m+2) ?_ hframeH
                all_goals rw [List.length_ofFn]; omega
              · have he : out-3=unsignedEnd+4*P.m+2 := by omega
                rw [he,←hanswer]; exact hheaderH
              · apply (((hJgraph.of_agree_below (h₀ := buildEnd) ?_ hframeS).of_agree_below
                  (h₀ := signedEnd) ?_ hframeC).of_agree_below (h₀ := unsignedEnd) ?_ hframeT).of_agree_below
                    (h₀ := unsignedEnd+4*P.m+2) ?_ hframeH
                all_goals rw [J.solverWords_length]; change heap+(2+5*I.m)≤_; omega
              · intro x hx
                exact (hframeH x (by omega)).trans ((hframeT x (by omega)).trans
                  ((hframeC x (by omega)).trans ((hframeS x (by omega)).trans (hframeB x hx))))
            · simp only [feasibilityPhaseContract,buildFeasibilityContract,magnitudeCopyContract,
                feasibilityObjectiveContract,costHeaderContract,heapContract,List.length_ofFn,
                argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_load,Expr.size_reg,Expr.size_const]
              have hc : (prunedScalingContract w solver entry T hproc P C B).cost
                  [heap+2+11*I.m+2*I.n,C,B,buildEnd] memB=
                  (prunedScalingContract w solver entry T hproc P C B).cost [] (fun _ => 0) := rfl
              change _≤(prunedScalingContract w solver entry T hproc P C B).cost [] (fun _ => 0)+4000*(I.m+I.n+1)
              rw [hc,hPm]
              omega

end MinCostFlow.Scaling.Machine
