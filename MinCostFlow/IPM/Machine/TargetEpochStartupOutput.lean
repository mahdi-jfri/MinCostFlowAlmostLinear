module

public import MinCostFlow.IPM.Machine.EpochStartupHandoff
public import MinCostFlow.IPM.Machine.TargetEpochStartupAccepts
public import MinCostFlow.IPM.Machine.TargetEpochStatic
import MinCostFlow.IPM.Machine.ReportedTableLayout

/-!
# Exact startup data on both sides of the target

The copied flow stays fixed through startup. Its two views and the
original tables justify the cache and the guard checks. On promised
targets the checked coefficient ranges always accept.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 400000 in
/-- Decode the startup before interpreting its verdict. The lower
target path may reject, while a promised target supplies the full
scan's acceptance from the actual initialized coefficients. -/
theorem targetEpoch_startup_output_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (tp qp base rp fp heap initEnd bit : ℕ)
    (mem initialized named started : ℕ → ℕ) (target normalization r : ℝ)
    (hfixed : TargetFixedInputs F I old tp qp fp target normalization (Num.IPM.alphaPrime I.m U) mem)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hN : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hB : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named (initEnd+I.m+3) started)
    (hList : ListAt started initEnd (List.range I.m)) (hFrame : ∀ z<heap,started z=mem z)
    (hScan : let L := old.next F I base rp fp heap initEnd
      (coefficientRangeListContract w F.fmt.limbBits).post
        [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] started bit started)
    (hbaseEnd : base+I.m*F.limbs≤fp) (hrEnd : rp+F.limbs≤fp) (hfEnd : fp+I.m*F.limbs≤heap)
    (hflow : TargetStageFlow F I old.exponent fp heap mem)
    (hbase : epochVector F I mem base=epochVector F I mem fp)
    (hsource : epochSourcesAt F I (old.next F I base rp fp heap initEnd) (Num.IPM.alphaPrime I.m U) r mem)
    (hres : residual I target (epochVector F I mem fp)=r) (hr : 1/4<r)
    (hfmt : F.rangeExponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (ha0 : 0≤Num.IPM.alphaPrime I.m U) (ha1 : Num.IPM.alphaPrime I.m U≤1) :
    let L := old.next F I base rp fp heap initEnd
    let f := epochVector F I mem fp
    let s := A.init (namedInstance I)
      (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (TargetStagePromise I U target f → bit=1) ∧
      epochVector F I started L.base=f ∧ epochVector F I started L.flow=f ∧
      epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r started ∧
      (∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
        L.cost L.residual L.alpha L.lengths L.gradient e started) := by
  dsimp only
  let L := old.next F I base rp fp heap initEnd
  let f := epochVector F I mem fp
  let s := A.init (namedInstance I)
    (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
  have hfp : fp≤heap := (Nat.le_add_right _ _).trans hfEnd
  have ha : ∀ p∈[base,old.cost,old.lower,old.upper],p+I.m*F.limbs≤fp := by
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | h
    · exact hbaseEnd
    · exact hfixed.arrays p h
  have hs : ∀ p∈[rp,old.alpha,old.one,old.slackMin,old.slackMax],p+F.limbs≤fp := by
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | h
    · exact hrEnd
    · exact hfixed.scalars p (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
        tauto)
  have hEqual : ∀ j<I.m,Num.fixVal mem (fp+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
    intro j hj
    exact congrFun hbase.symm ⟨j,hj⟩
  have hInside : ∀ j<I.m,Num.fixVal mem (old.lower+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
      Num.fixVal mem (fp+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (old.upper+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
    intro j hj
    let e : Fin I.m := ⟨j,hj⟩
    change epochVector F I mem old.lower e<f e ∧ f e<epochVector F I mem old.upper e
    rw [show epochVector F I mem old.lower e=(I.edge e).lower from (hfixed.lower e).2,
      show epochVector F I mem old.upper e=(I.edge e).upper from (hfixed.upper e).2]
    exact hflow.inside e
  have hcache : ∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e started :=
    epochStartup_initial_cache_upTo F A I κ α Ψ eps hA hI rate allocation R old base rp fp heap initEnd
      mem initialized named started hOut hN hB ha hs hfEnd (fun j hj => (hflow.2.2 ⟨j,hj⟩).1) hEqual hInside
  have hSource := hsource.frozen (fun z hz => hFrame z (hz.trans_le hfp)) ha ⟨hrEnd,hs old.alpha (by simp)⟩
  have hfixed' := hfixed.frozen (fun z hz => hFrame z (hz.trans_le hfp)) le_rfl
  have hbase' : epochVector F I started L.base=f := by
    funext e
    exact (Num.IPM.fixVal_frozen hFrame
      ((reported_entry_end base F.limbs e.val I.m e.isLt).trans (hbaseEnd.trans hfp))).trans (congrFun hbase e)
  have hflow' : epochVector F I started L.flow=f := by
    funext e
    exact Num.IPM.fixVal_frozen hFrame ((reported_entry_end fp F.limbs e.val I.m e.isLt).trans hfEnd)
  refine ⟨?_,hbase',hflow',hSource,hcache⟩
  intro hp
  exact targetEpoch_startup_accepts F A I U q L s target r started bit hfmt hSource
    (hflow'.symm ▸ hres) hr hm hU hsize hnums hFlo ha0 ha1
    (hflow'.symm ▸ hflow.inside) (hflow'.symm ▸ hflow.2.1.1)
    hList hfixed'.gradientMin hfixed'.gradientMax hfixed'.lengthMin hcache hScan (hflow'.symm ▸ hp)

/-- Decode the startup before interpreting its verdict. The lower
target path may reject, while a promised target supplies the full
scan's acceptance from the actual initialized coefficients. -/
theorem targetEpoch_startup_output {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (tp qp base rp fp heap initEnd bit : ℕ)
    (mem initialized named started : ℕ → ℕ) (target normalization r : ℝ)
    (hfixed : TargetFixedInputs F I old tp qp fp target normalization (Num.IPM.alphaPrime I.m U) mem)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hN : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hB : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named (initEnd+I.m+3) started)
    (hList : ListAt started initEnd (List.range I.m)) (hFrame : ∀ z<heap,started z=mem z)
    (hScan : let L := old.next F I base rp fp heap initEnd
      (coefficientRangeListContract w F.fmt.limbBits).post
        [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] started bit started)
    (hbaseEnd : base+I.m*F.limbs≤fp) (hrEnd : rp+F.limbs≤fp) (hfEnd : fp+I.m*F.limbs≤heap)
    (hflow : TargetStageFlow F I old.exponent fp heap mem)
    (hbase : epochVector F I mem base=epochVector F I mem fp)
    (hsource : epochSourcesAt F I (old.next F I base rp fp heap initEnd) (Num.IPM.alphaPrime I.m U) r mem)
    (hres : residual I target (epochVector F I mem fp)=r) (hr : 1/4<r)
    (hfmt : F.rangeExponent=ipmRangeExponent I.m U)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (ha0 : 0≤Num.IPM.alphaPrime I.m U) (ha1 : Num.IPM.alphaPrime I.m U≤1) :
    let L := old.next F I base rp fp heap initEnd
    let f := epochVector F I mem fp
    let s := A.init (namedInstance I)
      (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (TargetStagePromise I U target f → bit=1) ∧
      epochVector F I started L.base=f ∧ epochVector F I started L.flow=f ∧
      epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r started ∧
      (∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
        L.cost L.residual L.alpha L.lengths L.gradient e started) :=
  targetEpoch_startup_output_upTo F A I U κ α Ψ eps (hA.upTo I.m I.n) hI rate allocation R old
    tp qp base rp fp heap initEnd bit mem initialized named started target normalization r
    hfixed hOut hN hB hList hFrame hScan hbaseEnd hrEnd hfEnd hflow hbase hsource hres hr hfmt
    hm hU hsize hnums hFlo ha0 ha1

/-- Decode the startup before interpreting its verdict. The lower
target path may reject, while a promised target supplies the full
scan's acceptance from the actual initialized coefficients. -/
theorem targetEpoch_startup_output_at_range_upTo_on {w q K : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n) (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (tp qp base rp fp heap initEnd bit : ℕ)
    (mem initialized named started : ℕ → ℕ) (target normalization r : ℝ)
    (hfixed : TargetFixedInputs F I old tp qp fp target normalization (Num.IPM.alphaPrime I.m U) mem)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hN : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hB : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named (initEnd+I.m+3) started)
    (hList : ListAt started initEnd (List.range I.m)) (hFrame : ∀ z<heap,started z=mem z)
    (hScan : let L := old.next F I base rp fp heap initEnd
      (coefficientRangeListContract w F.fmt.limbBits).post
        [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] started bit started)
    (hbaseEnd : base+I.m*F.limbs≤fp) (hrEnd : rp+F.limbs≤fp) (hfEnd : fp+I.m*F.limbs≤heap)
    (hflow : TargetStageFlow F I old.exponent fp heap mem)
    (hbase : epochVector F I mem base=epochVector F I mem fp)
    (hsource : epochSourcesAt F I (old.next F I base rp fp heap initEnd) (Num.IPM.alphaPrime I.m U) r mem)
    (hres : residual I target (epochVector F I mem fp)=r) (hr : 1/4<r)
    (hfmt : ipmRangeExponent I.m U≤F.rangeExponent)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (ha0 : 0≤Num.IPM.alphaPrime I.m U) (ha1 : Num.IPM.alphaPrime I.m U≤1) :
    let L := old.next F I base rp fp heap initEnd
    let f := epochVector F I mem fp
    let s := A.init (namedInstance I)
      (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (TargetStagePromise I U target f → bit=1) ∧
      epochVector F I started L.base=f ∧ epochVector F I started L.flow=f ∧
      epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r started ∧
      (bit=1 → ∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
        L.cost L.residual L.alpha L.lengths L.gradient e started) := by
  dsimp only
  let L := old.next F I base rp fp heap initEnd
  let f := epochVector F I mem fp
  let s := A.init (namedInstance I)
    (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
  have hfp : fp≤heap := (Nat.le_add_right _ _).trans hfEnd
  have ha : ∀ p∈[base,old.cost,old.lower,old.upper],p+I.m*F.limbs≤fp := by
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | h
    · exact hbaseEnd
    · exact hfixed.arrays p h
  have hs : ∀ p∈[rp,old.alpha,old.one,old.slackMin,old.slackMax],p+F.limbs≤fp := by
    intro p hp
    rw [List.mem_cons] at hp
    rcases hp with rfl | h
    · exact hrEnd
    · exact hfixed.scalars p (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
        tauto)
  have hEqual : ∀ j<I.m,Num.fixVal mem (fp+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
    intro j hj
    exact congrFun hbase.symm ⟨j,hj⟩
  have hInside : ∀ j<I.m,Num.fixVal mem (old.lower+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
      Num.fixVal mem (fp+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (old.upper+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
    intro j hj
    let e : Fin I.m := ⟨j,hj⟩
    change epochVector F I mem old.lower e<f e ∧ f e<epochVector F I mem old.upper e
    rw [show epochVector F I mem old.lower e=(I.edge e).lower from (hfixed.lower e).2,
      show epochVector F I mem old.upper e=(I.edge e).upper from (hfixed.upper e).2]
    exact hflow.inside e
  have hcache := epochStartup_initial_cache_upTo_on F A I κ α Ψ eps hA hI rate allocation R old base rp fp heap
    initEnd mem initialized named started hOut hN hB ha hs hfEnd (fun j hj => (hflow.2.2 ⟨j,hj⟩).1) hEqual hInside
  -- The scan test reads only the coefficient part of the cache. That part holds for
  -- every structure, so we use a copy of `A` whose Query is zero, whose cache needs
  -- no range for the lengths.
  let A0 : MinRatioDataStructureWithFailure := { A with query := fun _ _ => 0 }
  have hcache0 := epochStartup_initial_cache_of_query F A I κ α rate allocation R old base rp fp heap initEnd
    mem initialized named started hOut hN hB ha hs hfEnd (fun j hj => (hflow.2.2 ⟨j,hj⟩).1) hEqual hInside
    A0 s (fun _ _ => rfl)
  have hSource := hsource.frozen (fun z hz => hFrame z (hz.trans_le hfp)) ha ⟨hrEnd,hs old.alpha (by simp)⟩
  have hfixed' := hfixed.frozen (fun z hz => hFrame z (hz.trans_le hfp)) le_rfl
  have hbase' : epochVector F I started L.base=f := by
    funext e
    exact (Num.IPM.fixVal_frozen hFrame
      ((reported_entry_end base F.limbs e.val I.m e.isLt).trans (hbaseEnd.trans hfp))).trans (congrFun hbase e)
  have hflow' : epochVector F I started L.flow=f := by
    funext e
    exact Num.IPM.fixVal_frozen hFrame ((reported_entry_end fp F.limbs e.val I.m e.isLt).trans hfEnd)
  refine ⟨?_,hbase',hflow',hSource,fun hb => hcache (hP _ ?_)⟩
  swap
  · exact epochStartup_lengthsWithin F I L hList hfixed'.lengthMin hfixed'.gradientMin hfixed'.gradientMax
      (hb ▸ hScan)
  intro hp
  exact targetEpoch_startup_accepts_at_range F A0 I U q L s target r started bit hfmt hSource
    (hflow'.symm ▸ hres) hr hm hU hsize hnums hFlo ha0 ha1
    (hflow'.symm ▸ hflow.inside) (hflow'.symm ▸ hflow.2.1.1)
    hList hfixed'.gradientMin hfixed'.gradientMax hfixed'.lengthMin hcache0 hScan (hflow'.symm ▸ hp)

/-- Decode the startup before interpreting its verdict. The lower
target path may reject, while a promised target supplies the full
scan's acceptance from the actual initialized coefficients. -/
theorem targetEpoch_startup_output_at_range_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (tp qp base rp fp heap initEnd bit : ℕ)
    (mem initialized named started : ℕ → ℕ) (target normalization r : ℝ)
    (hfixed : TargetFixedInputs F I old tp qp fp target normalization (Num.IPM.alphaPrime I.m U) mem)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hN : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hB : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named (initEnd+I.m+3) started)
    (hList : ListAt started initEnd (List.range I.m)) (hFrame : ∀ z<heap,started z=mem z)
    (hScan : let L := old.next F I base rp fp heap initEnd
      (coefficientRangeListContract w F.fmt.limbBits).post
        [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] started bit started)
    (hbaseEnd : base+I.m*F.limbs≤fp) (hrEnd : rp+F.limbs≤fp) (hfEnd : fp+I.m*F.limbs≤heap)
    (hflow : TargetStageFlow F I old.exponent fp heap mem)
    (hbase : epochVector F I mem base=epochVector F I mem fp)
    (hsource : epochSourcesAt F I (old.next F I base rp fp heap initEnd) (Num.IPM.alphaPrime I.m U) r mem)
    (hres : residual I target (epochVector F I mem fp)=r) (hr : 1/4<r)
    (hfmt : ipmRangeExponent I.m U≤F.rangeExponent)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (ha0 : 0≤Num.IPM.alphaPrime I.m U) (ha1 : Num.IPM.alphaPrime I.m U≤1) :
    let L := old.next F I base rp fp heap initEnd
    let f := epochVector F I mem fp
    let s := A.init (namedInstance I)
      (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (TargetStagePromise I U target f → bit=1) ∧
      epochVector F I started L.base=f ∧ epochVector F I started L.flow=f ∧
      epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r started ∧
      (bit=1 → ∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
        L.cost L.residual L.alpha L.lengths L.gradient e started) :=
  targetEpoch_startup_output_at_range_upTo_on F A I U κ α Ψ eps (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _)
    hI rate allocation R old tp qp base rp fp heap initEnd bit mem initialized named started target
    normalization r hfixed hOut hN hB hList hFrame hScan hbaseEnd hrEnd hfEnd hflow hbase hsource hres
    hr hfmt hm hU hsize hnums hFlo ha0 ha1

end MinCostFlow.IPM.Machine
