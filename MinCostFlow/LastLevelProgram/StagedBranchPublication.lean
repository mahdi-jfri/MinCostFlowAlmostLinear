module

public import MinCostFlow.LastLevelProgram.StagedOutputLayout
public import MinCostFlow.LastLevelProgram.Denominator
public import MinCostFlow.LastLevelProgram.StagedGuestWeights
import MinCostFlow.LastLevelProgram.StretchEncoding
public import MinCostFlow.LastLevelProgram.UnitWeights
public import MinCostFlow.LastLevelProgram.RoundLoop
public import MinCostFlow.LastLevelProgram.GuestSimulationWidth
public import MinCostFlow.LastLevelProgram.GuestFormatSetup
public import MinCostFlow.LastLevelProgram.ScaleWord
public import WordRAM.CopyWords
import Mathlib.Tactic

/-!
# Publishing a staged branch

Definition 5.8 (pages 19–20) publishes each rebuilt branch after the numeric pass.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num WideWord SparseCore

/-- Use the numeric cursor for the unit block, then build and publish
the branch. Register fifty-four holds the new allocation end. -/
def stagedBranchAppendBody (unit restore init scatter publish : ℕ) : Stmt :=
  .seq (stagedAfterRoundUnitBody unit)
    (.seq (stagedBranchGraphBody restore init) (stagedBranchOutputBody scatter publish))

/-- The unit allocation provides a fresh record cursor and leaves the
verified stretches and weights available below it. -/
theorem stagedBranchAppend_runs {w h unit restore init scatter publish : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (L P heap : ℕ)
    (hcall : MeetsContract w p unit (denominatorContract w h))
    (hL : st.regs 55 = L) (hP : st.regs 23 = P) (hheap : st.regs 16 = heap)
    (hw : 1 < 2^w) (hPword : P < 2^w)
    {B : ℝ} (hB : 1 ≤ B) (hwidth : 2 * (2 : ℝ)^P * B < capacity h L)
    (hz : ZeroFrom st.mem heap) (hroom : heap+2*L < 2^w)
    {Q : State → Prop} (graphCost outputCost : ℕ)
    (hnext : ∀ ready : State,
      ready.regs 60 = heap+L → ready.regs 16 = heap+2*L →
      Valid ready.mem (heap+L) h L → fixVal ready.mem (heap+L) h L P = 1 →
      (∀ a < heap, ready.mem a = st.mem a) → ZeroFrom ready.mem (heap+2*L) →
      (∀ r, r ≠ 16 → r ≠ 60 → r ≠ 67 → ready.regs r = st.regs r) →
      ∃ mid cg, Runs w p ω (stagedBranchGraphBody restore init) ready .normal mid cg ∧
        cg ≤ graphCost ∧
        ∃ out co, Runs w p ω (stagedBranchOutputBody scatter publish) mid .normal out co ∧
          Q out ∧ co ≤ outputCost) :
    ∃ out cost, Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
      st .normal out cost ∧ Q out ∧ cost ≤ 56*L+77+graphCost+outputCost := by
  obtain ⟨ready,cu,hu,hptr,hr,hv,hvOne,hprefix,hz',hregs,hcu⟩ :=
    stagedAfterRoundUnit_runs (ω := ω) st L P heap hcall hL hP hheap hw hPword hB hwidth hz hroom
  obtain ⟨mid,cg,hg,hcg,out,co,ho,hQ,hco⟩ :=
    hnext ready hptr hr hv hvOne hprefix hz' hregs
  have hgo := runs_seq_iff.mpr (Or.inr ⟨mid,cg,co,hg,ho,rfl⟩)
  exact ⟨out,cu+(cg+co+1)+1,runs_seq_iff.mpr (Or.inr ⟨ready,cu,_,hu,hgo,rfl⟩),
    hQ,by omega⟩

/-- Return the end of the published branch to the outer rebuild loop. -/
def stagedBranchAppendReturn (unit restore init scatter publish : ℕ) : Stmt :=
  .seq (stagedBranchAppendBody unit restore init scatter publish) (.ret (.reg 54))

/-- The outer loop can use the returned allocation end as its next
cursor. The return leaves the complete branch readout in memory. -/
theorem stagedBranchAppendReturn_runs {w unit restore init scatter publish : ℕ}
    {p : Program} {ω : ℕ → Bool} (st ready : State) (cost next : ℕ)
    (hr : Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
      st .normal ready cost)
    (hn : ready.regs 54 = next) :
    Runs w p ω (stagedBranchAppendReturn unit restore init scatter publish)
      st (.returned next) ready (cost+3) := by
  have hret : Runs w p ω (.ret (.reg 54)) ready (.returned next) ready 2 :=
    runs_ret_iff.mpr ⟨next,congrArg some hn,rfl,rfl,rfl⟩
  exact runs_seq_iff.mpr (Or.inr ⟨ready,cost,2,hr,hret,rfl⟩)

/-- Store the next weight base after the branch and return the word
after it. The loop can recover the base from its cursor alone. -/
def stagedRoundWeightCursor : Stmt :=
  .seq (.store (.reg 54) (.reg 38))
    (.ret (.bin .add (.reg 54) (.const 1)))

/-- The cursor word preserves the entire published collection and
keeps the tail beyond the returned cursor fresh. -/
theorem stagedRoundWeightCursor_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (stop weights : ℕ)
    (hs : st.regs 54 = stop) (hw : st.regs 38 = weights)
    (hroom : stop+1 < 2^w) (hzero : ZeroFrom st.mem stop) :
    ∃ out, Runs w p ω stagedRoundWeightCursor st (.returned (stop+1)) out 8 ∧
      out.mem = Function.update st.mem stop weights ∧ out.mem stop = weights ∧ (∀ a < stop, out.mem a = st.mem a) ∧
      ZeroFrom out.mem (stop+1) := by
  let out := {st with mem := Function.update st.mem stop weights}
  have hstore : Runs w p ω (.store (.reg 54) (.reg 38)) st .normal out 3 :=
    runs_store_iff.mpr ⟨stop,weights,congrArg some hs,congrArg some hw,rfl,rfl,rfl⟩
  have hret : Runs w p ω (.ret (.bin .add (.reg 54) (.const 1))) out
      (.returned (stop+1)) out 4 := by
    apply runs_ret_iff.mpr
    have h1 : 1 < 2^w := by omega
    exact ⟨stop+1,by simp [Expr.eval,BinOp.eval,out,hs,h1,hroom],rfl,rfl,rfl⟩
  refine ⟨out,runs_seq_iff.mpr (Or.inr ⟨out,3,4,hstore,hret,rfl⟩),rfl,by simp [out],?_,?_⟩
  · intro a ha
    exact Function.update_of_ne (ne_of_lt ha) ..
  · intro a ha
    exact (Function.update_of_ne (ne_of_gt (by omega : stop < a)) ..).trans
      (hzero a (by omega))

/-- Writing the cursor descriptor after all next-round weights leaves their
fixed-point values readable through the returned cursor. -/
theorem stagedRoundWeightCursor_values {mem out : ℕ → ℕ} {stop dst stride L h P m : ℕ}
    (weight : ℕ → ℝ) (hptr : out stop = dst)
    (hframe : ∀ a < stop, out a = mem a)
    (hspan : dst+(m-1)*stride+L ≤ stop)
    (hvalues : ∀ i < m, Valid mem (dst+i*stride) h L ∧
      fixVal mem (dst+i*stride) h L P = weight i) :
    ∀ i < m, Valid out (out ((stop+1)-1)+i*stride) h L ∧
      fixVal out (out ((stop+1)-1)+i*stride) h L P = weight i := by
  intro i hi
  rw [Nat.add_sub_cancel, hptr]
  obtain ⟨hv,hw⟩ := hvalues i hi
  have hmul := Nat.mul_le_mul_right stride (show i ≤ m-1 by omega)
  have hagree j (hj : j < L) : out (dst+i*stride+j) = mem (dst+i*stride+j) :=
    hframe _ (by omega)
  exact ⟨fun j hj => (hagree j hj).trans_lt (hv j hj),
    by simpa only [fixVal,intVal_congr hagree] using hw⟩

/-- The cursor's compact weight table represents the next model iterate
on the named representative edges. -/
theorem stagedRoundWeightCursor_model {mem out : ℕ → ℕ} {stop dst stride L h P j : ℕ}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hptr : out stop = dst) (hframe : ∀ a < stop, out a = mem a)
    (hspan : dst+(H.m-1)*stride+L ≤ stop)
    (hvalues : ∀ i < H.m, Valid mem (dst+i*stride) h L ∧
      fixVal mem (dst+i*stride) h L P = weights P ρ query (j+1) (edgeName H i)) :
    ∀ e ∈ H.E, Valid out (out ((stop+1)-1)+edgeIndex H e*stride) h L ∧
      fixVal out (out ((stop+1)-1)+edgeIndex H e*stride) h L P =
        weights P ρ query (j+1) e := by
  intro e he
  obtain ⟨hi,hn⟩ := edgeIndex_live he
  simpa only [hn] using stagedRoundWeightCursor_values
    (fun i => weights P ρ query (j+1) (edgeName H i)) hptr hframe hspan hvalues
    (edgeIndex H e) hi

/-- Staging, numeric work, branch append, and the cursor write preserve
the incoming allocation except for the selected branch pointer. -/
theorem stagedPublishedRound_frame {mem staged numeric appended : ℕ → ℕ}
    {cursor numericEnd slot stop : ℕ}
    (hcursor : cursor ≤ numericEnd) (hstop : numericEnd ≤ stop)
    (hstage : ∀ a < cursor, staged a = mem a)
    (hnumeric : ∀ a < cursor, numeric a = staged a)
    (happend : ∀ a < numericEnd, a ≠ slot → appended a = numeric a)
    (weights : ℕ) :
    ∀ a < cursor, a ≠ slot → (Function.update appended stop weights) a = mem a := by
  intro a ha hne
  rw [Function.update_of_ne (show a ≠ stop by omega), happend a (ha.trans_le hcursor) hne,
    hnumeric a ha, hstage a ha]

/-- The numeric allocation and subsequent cursor publication expose the
updated weights at the stride expected by the next round. -/
theorem stagedNumericWeights_atCursor {mem appended out : ℕ → ℕ} {stop start slot L h P j : ℕ}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hm : 0 < H.m) (hstop : start+H.m*narrowWeightSpace L ≤ stop)
    (hptr : out stop = start+narrowWeightSpace L-L)
    (hslot : slot < start)
    (happend : ∀ a < start+H.m*narrowWeightSpace L, a ≠ slot → appended a = mem a)
    (hframe : ∀ a < stop, out a = appended a)
    (hvalues : ∀ i < H.m, Valid mem (roundWeightAddr start L i) h L ∧
      fixVal mem (roundWeightAddr start L i) h L P = weights P ρ query (j+1) (edgeName H i)) :
    ∀ e ∈ H.E,
      Valid out (out ((stop+1)-1)+edgeIndex H e*narrowWeightSpace L) h L ∧
      fixVal out (out ((stop+1)-1)+edgeIndex H e*narrowWeightSpace L) h L P =
        weights P ρ query (j+1) e := by
  apply stagedRoundWeightCursor_model H ρ query hptr hframe
  · rwa [stagedNumericOutput_lastWeightEnd start H.m L hm]
  · intro i hi
    obtain ⟨hv,hvalue⟩ := hvalues i hi
    have hend' : roundWeightAddr start L i+L ≤ start+H.m*narrowWeightSpace L := by
      rw [stagedWeightAddr_eq]
      have hl : L ≤ narrowWeightSpace L := by unfold narrowWeightSpace widenWeightSpace; omega
      have hmul := Nat.mul_le_mul_right (narrowWeightSpace L) (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hmul
      omega
    have hagree k (hk : k < L) : appended (roundWeightAddr start L i+k) =
        mem (roundWeightAddr start L i+k) :=
      happend _ (by omega) (by
        rw [stagedWeightAddr_eq]
        have hl : L ≤ narrowWeightSpace L := by unfold narrowWeightSpace widenWeightSpace; omega
        omega)
    rw [← stagedWeightAddr_eq]
    exact ⟨fun k hk => (hagree k hk).trans_lt (hv k hk),
      by simpa only [fixVal,intVal_congr hagree] using hvalue⟩

/-- The final descriptor write supplies the memory facts consumed by the
collection loop and its next weight query. -/
theorem stagedPublishedRound_memory
    {mem staged numeric appended : ℕ → ℕ}
    {cursor start collection count stop vCap eCap h L P caller j : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hm : 0 < H.m) (hj : j < count) (htable : collection+1+count ≤ cursor)
    (hprefix : CollectionPrefix mem collection count j cursor vCap eCap h L caller E branches)
    (hstart : cursor ≤ start)
    (hstop : start+H.m*narrowWeightSpace L ≤ stop)
    (hstage : ∀ a < cursor, staged a = mem a)
    (hnumeric : ∀ a < cursor, numeric a = staged a)
    (happend : ∀ a < start+H.m*narrowWeightSpace L, a ≠ collection+1+j → appended a = numeric a)
    (hzero : ZeroFrom appended stop)
    (hspan : BranchWithin appended (appended (collection+1+j)) (collection+1+count) stop vCap eCap L E)
    (hbranch : MinRatio.LSFAt appended (appended (collection+1+j)) vCap eCap h L caller E (branches j))
    (hvalues : ∀ i < H.m, Valid numeric (roundWeightAddr start L i) h L ∧
      fixVal numeric (roundWeightAddr start L i) h L P = weights P ρ query (j+1) (edgeName H i)) :
    let out := Function.update appended stop (start+narrowWeightSpace L-L)
    cursor < stop+1 ∧
    out ((stop+1)-1) = start+narrowWeightSpace L-L ∧
    out ((stop+1)-1)+(H.m-1)*narrowWeightSpace L+L ≤ (stop+1)-1 ∧
    ZeroFrom out (stop+1) ∧
    (∀ a < cursor, a ≠ collection+1+j → out a = mem a) ∧
    (∀ a < collection, out a = mem a) ∧
    CollectionPrefix out collection count (j+1) (stop+1) vCap eCap h L caller E branches ∧
    ∀ e ∈ H.E,
      Valid out (out ((stop+1)-1)+edgeIndex H e*narrowWeightSpace L) h L ∧
      fixVal out (out ((stop+1)-1)+edgeIndex H e*narrowWeightSpace L) h L P = weights P ρ query (j+1) e := by
  intro out
  have hkeep a (ha : a < stop) : out a = appended a := Function.update_of_ne (ne_of_lt ha) ..
  have hframe := stagedPublishedRound_frame (by omega) hstop hstage hnumeric happend
    (start+narrowWeightSpace L-L)
  have hnew := publishedBranch_cursorWrite (value := start+narrowWeightSpace L-L)
    (by omega) hspan hbranch
  have hbelow a (ha : a < collection) : out a = mem a :=
    hframe a (by omega) (by omega)
  have hptr : out ((stop+1)-1) = start+narrowWeightSpace L-L := by
    rw [Nat.add_sub_cancel]
    exact Function.update_self ..
  have hweightEnd : out ((stop+1)-1)+(H.m-1)*narrowWeightSpace L+L ≤ (stop+1)-1 := by
    rw [hptr,stagedNumericOutput_lastWeightEnd start H.m L hm,Nat.add_sub_cancel]
    exact hstop
  refine ⟨by omega,hptr,hweightEnd,?_,hframe,hbelow,
    collectionPrefix_succ hprefix hj (by omega) htable hframe hnew,?_⟩
  · intro a ha
    exact (Function.update_of_ne (by omega : a ≠ stop) ..).trans (hzero a (by omega))
  · exact stagedNumericWeights_atCursor H ρ query hm hstop (Function.update_self ..)
      (by omega) happend hkeep hvalues

/-- Fill the initial host table, then publish its pointer after the
reserved weight slots so the first round can use the ordinary cursor. -/
def stagedInitialWeightsBody (fill : ℕ) : Stmt :=
  .seq (.call 71 fill [.reg 60,.reg 16,.reg 55,.reg 32,.reg 1])
    (.seq (.assign 38 (.reg 16))
      (.seq (.assign 54 (.bin .add (.reg 16) (.bin .mul (.reg 1) (.reg 32))))
        stagedRoundWeightCursor))

/-- The initial table supplies unit weights and a fresh cursor of the
same shape returned by each completed round. -/
theorem stagedInitialWeights_runs {w h P fill : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (unit dst L stride m : ℕ)
    (hu : st.regs 60 = unit) (hd : st.regs 16 = dst) (hL : st.regs 55 = L)
    (hs : st.regs 32 = stride) (hm : st.regs 1 = m)
    (hc : MeetsContract w p fill (stridedUnitWeightContract w h P))
    (hwords : ∀ a ∈ [unit,dst,L,stride,m], a < 2^w)
    (hpre : (stridedUnitWeightContract w h P).pre [unit,dst,L,stride,m] st.mem)
    (hzero : ZeroFrom st.mem dst) (hfit : dst+m*stride+1 < 2^w) :
    let stop := dst+m*stride
    ∃ out cost, Runs w p ω (stagedInitialWeightsBody fill) st (.returned (stop+1)) out cost ∧
      out.mem stop = dst ∧ ZeroFrom out.mem (stop+1) ∧
      (∀ a < dst, out.mem a = st.mem a) ∧
      (∀ i < m, Valid out.mem (dst+i*stride) h L ∧ fixVal out.mem (dst+i*stride) h L P = 1) ∧
      cost ≤ (17*L+27)*m+35 := by
  intro stop
  have hargs : evalArgs w st [.reg 60,.reg 16,.reg 55,.reg 32,.reg 1] =
      some [unit,dst,L,stride,m] := by simp [evalArgs,Expr.eval,hu,hd,hL,hs,hm]
  obtain ⟨mid,c,ret,hr,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 71) hc hargs hwords hpre ω
  obtain ⟨u,d,l,s,n,he,_,hvals,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
  let setBase := {mid with regs := Function.update mid.regs 38 dst}
  let ready := {setBase with regs := Function.update setBase.regs 54 stop}
  have hb : Runs w p ω (.assign 38 (.reg 16)) mid .normal setBase 2 :=
    runs_assign_iff.mpr ⟨dst,congrArg some ((hregs _ (by decide)).trans hd),rfl,rfl,rfl⟩
  have he' : Runs w p ω (.assign 54 (.bin .add (.reg 16) (.bin .mul (.reg 1) (.reg 32))))
      setBase .normal ready 6 := by
    have hr16 := (hregs 16 (by decide)).trans hd
    have hr1 := (hregs 1 (by decide)).trans hm
    have hr32 := (hregs 32 (by decide)).trans hs
    have hstop : dst+m*stride < 2^w := Nat.lt_of_succ_lt hfit
    have hmul : m*stride < 2^w := (Nat.le_add_left _ _).trans_lt hstop
    exact runs_assign_iff.mpr ⟨stop,
      by simp [Expr.eval,BinOp.eval,setBase,Function.update,hr16,hr1,hr32,hmul,hstop,stop],
      rfl,rfl,rfl⟩
  have hz : ZeroFrom ready.mem stop := fun a ha =>
    (hframe a (Or.inr ha)).trans (hzero a ((Nat.le_add_right _ _).trans ha))
  obtain ⟨out,hret,_,hptr,hkeep,hfresh⟩ :=
    stagedRoundWeightCursor_runs (p := p) (ω := ω) ready stop dst
      (by simp [ready]) (by simp [ready,setBase,Function.update]) hfit hz
  have htail := runs_seq_iff.mpr (Or.inr ⟨ready,6,8,he',hret,rfl⟩)
  have hmid := runs_seq_iff.mpr (Or.inr ⟨setBase,2,15,hb,htail,rfl⟩)
  change c ≤ 5+((17*L+27)*m+10)+1 at hcost
  refine ⟨out,c+19,runs_seq_iff.mpr (Or.inr ⟨mid,c,18,hr,hmid,rfl⟩),hptr,hfresh,?_,?_,by omega⟩
  · intro a ha
    exact (hkeep a (ha.trans_le (Nat.le_add_right _ _))).trans (hframe a (Or.inl ha))
  · intro i hi
    obtain ⟨_,_,_,_,_,he,_,hstride,_⟩ := hpre
    simp only [List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
    have hbnd := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hbnd
    have hcell (k : ℕ) (hk : k < L) :
        out.mem (dst+i*stride+k) = mid.mem (dst+i*stride+k) :=
      hkeep _ (by dsimp [stop]; omega)
    obtain ⟨hv,hval⟩ := hvals i hi
    refine ⟨fun k hk => (hcell k hk).trans_lt (hv k hk),?_⟩
    simpa only [fixVal,intVal_congr hcell] using hval

/-- Allocate and fill the first weight table from a fresh heap. -/
def stagedInitialWeightSetup (unit fill : ℕ) : Stmt :=
  .seq (stagedAfterRoundUnitBody unit) (stagedInitialWeightsBody fill)

/-- Initialization leaves the first round with unit weights, a pointer
at the preceding cell, and a fresh staging cursor. -/
theorem stagedInitialWeightSetup_runs {w h unit fill : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (L P heap stride m : ℕ)
    (hunit : MeetsContract w p unit (denominatorContract w h))
    (hfill : MeetsContract w p fill (stridedUnitWeightContract w h P))
    (hL : st.regs 55 = L) (hP : st.regs 23 = P) (hheap : st.regs 16 = heap)
    (hs : st.regs 32 = stride) (hm : st.regs 1 = m)
    (hw : 1 < 2^w) (hpword : P < 2^w) (hsword : stride < 2^w) (hmword : m < 2^w)
    (hstride : L ≤ stride) {B : ℝ} (hB : 1 ≤ B)
    (hwidth : 2*(2 : ℝ)^P*B < capacity h L) (hz : ZeroFrom st.mem heap)
    (hfit : heap+2*L+m*stride+1 < 2^w) :
    let dst := heap+2*L
    let stop := dst+m*stride
    ∃ out cost, Runs w p ω (stagedInitialWeightSetup unit fill) st (.returned (stop+1)) out cost ∧
      out.mem stop = dst ∧ ZeroFrom out.mem (stop+1) ∧
      (∀ a < heap, out.mem a = st.mem a) ∧
      (∀ i < m, Valid out.mem (dst+i*stride) h L ∧ fixVal out.mem (dst+i*stride) h L P = 1) ∧
      cost ≤ (17*L+27)*m+56*L+111 := by
  intro dst stop
  have hr : dst < 2^w := by dsimp [dst]; omega
  obtain ⟨ready,cu,hu,hptr,hcur,hv,hone,hframe,hzero,hregs,hcu⟩ :=
    stagedAfterRoundUnit_runs (ω := ω) st L P heap hunit hL hP hheap hw hpword hB hwidth hz hr
  have hwords : ∀ a ∈ [heap+L,dst,L,stride,m], a < 2^w := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> dsimp [dst] at * <;> omega
  have hpre : (stridedUnitWeightContract w h P).pre [heap+L,dst,L,stride,m] ready.mem :=
    ⟨heap+L,dst,L,stride,m,rfl,hw,hstride,by dsimp [dst]; omega,
      by dsimp [dst]; omega,hv,hone⟩
  obtain ⟨out,cw,hrun,hbase,hfresh,hkeep,hvals,hcw⟩ :=
    stagedInitialWeights_runs (ω := ω) ready (heap+L) dst L stride m
      hptr hcur ((hregs _ (by decide) (by decide) (by decide)).trans hL)
      ((hregs _ (by decide) (by decide) (by decide)).trans hs)
      ((hregs _ (by decide) (by decide) (by decide)).trans hm)
      hfill hwords hpre hzero hfit
  exact ⟨out,cu+cw+1,runs_seq_iff.mpr (Or.inr ⟨ready,cu,cw,hu,hrun,rfl⟩),
    hbase,hfresh,fun a ha => (hkeep a (ha.trans_le (Nat.le_add_right _ _))).trans (hframe a ha),
    hvals,by omega⟩

/-- Call the initial weight setup after reserving the collection
header. The returned cursor is ready for the loop's first call. -/
def stagedInitialWeightContract (w h P : ℕ) (B : ℝ) : Contract where
  pre args mem := ∃ L heap stride m,
    args.getD 55 0 = L ∧ args.getD 23 0 = P ∧ args.getD 16 0 = heap ∧
    args.getD 32 0 = stride ∧ args.getD 1 0 = m ∧
    1 < 2^w ∧ P < 2^w ∧ stride < 2^w ∧ m < 2^w ∧ L ≤ stride ∧
    1 ≤ B ∧ 2*(2 : ℝ)^P*B < capacity h L ∧ ZeroFrom mem heap ∧
    heap+2*L+m*stride+1 < 2^w
  post args mem ret out :=
    let L := args.getD 55 0
    let heap := args.getD 16 0
    let stride := args.getD 32 0
    let m := args.getD 1 0
    let dst := heap+2*L
    let stop := dst+m*stride
    ret = stop+1 ∧ out stop = dst ∧ ZeroFrom out ret ∧
    (∀ a < heap, out a = mem a) ∧
    ∀ i < m, Valid out (dst+i*stride) h L ∧ fixVal out (dst+i*stride) h L P = 1
  cost args _ := (17*args.getD 55 0+27)*args.getD 1 0+56*args.getD 55 0+111

/-- Install the initial weight setup as a procedure returning the
cursor the collection controller stores in register zero. -/
theorem stagedInitialWeightSetup_meetsContract {w h P entry unit fill : ℕ}
    {p : Program} (B : ℝ)
    (he : p.procs[entry]? = some (stagedInitialWeightSetup unit fill))
    (hu : MeetsContract w p unit (denominatorContract w h))
    (hf : MeetsContract w p fill (stridedUnitWeightContract w h P)) :
    MeetsContract w p entry (stagedInitialWeightContract w h P B) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨L,heap,stride,m,hL,hP,hheap,hs,hm,hw,hpw,hsw,hmw,hstride,hB,hwidth,hz,hfit⟩ := hpre
  obtain ⟨out,cost,hr,hptr,hfresh,hkeep,hvals,hcost⟩ :=
    stagedInitialWeightSetup_runs (ω := ω) (startState args mem pos) L P heap stride m hu hf
      hL hP hheap hs hm hw hpw hsw hmw hstride hB hwidth hz hfit
  refine ⟨.returned (heap+2*L+m*stride+1),out,cost,hr,?_,?_⟩
  · simpa only [stagedInitialWeightContract,hL,hheap,hs,hm,Outcome.value,startState] using
      And.intro (rfl : heap+2*L+m*stride+1 = heap+2*L+m*stride+1) (And.intro hptr (And.intro hfresh (And.intro hkeep hvals)))
  · simpa only [stagedInitialWeightContract,hL,hm] using hcost

/-- Read the saved weight base using only the current allocation cursor. -/
def stagedRoundWeightBase (cursor : Expr) : Expr :=
  .load (.bin .sub cursor (.const 1))

/-- The weight pointer stored by the round is the value passed to the
next round when its cursor is one word past the pointer slot. -/
theorem stagedRoundWeightBase_eval {w : ℕ} {st : State} {cursor : Expr}
    (stop weights : ℕ) (hc : cursor.eval w st = some (stop+1))
    (hmem : st.mem stop = weights) (hfit : stop+1 < 2^w) :
    (stagedRoundWeightBase cursor).eval w st = some weights := by
  have h1 : 1 < 2^w := by omega
  have hs : stop < 2^w := by omega
  simp [stagedRoundWeightBase,Expr.eval,BinOp.eval,hc,hmem,h1,hs]

/-- Read the saved weight pointer into both consumers of the next
round. Register sixty-eight holds the incoming allocation cursor. -/
def loadStagedRoundWeights : Stmt :=
  .seq (.assign 8 (stagedRoundWeightBase (.reg 68))) (.assign 31 (.reg 8))

/-- The guest converter and the host update read the same weight table.
Loading the pointer preserves the cursor and all input memory. -/
theorem loadStagedRoundWeights_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (stop weights : ℕ)
    (hc : st.regs 68 = stop+1) (hm : st.mem stop = weights) (hfit : stop+1 < 2^w) :
    ∃ out, Runs w p ω loadStagedRoundWeights st .normal out 8 ∧
      out.regs 8 = weights ∧ out.regs 31 = weights ∧ out.mem = st.mem ∧
      ∀ r, r ≠ 8 → r ≠ 31 → out.regs r = st.regs r := by
  let mid := {st with regs := Function.update st.regs 8 weights}
  let out := {mid with regs := Function.update mid.regs 31 weights}
  have he := stagedRoundWeightBase_eval stop weights (cursor := .reg 68) (congrArg some hc) hm hfit
  have hfirst : Runs w p ω (.assign 8 (stagedRoundWeightBase (.reg 68))) st .normal mid 5 :=
    runs_assign_iff.mpr ⟨weights,he,rfl,rfl,rfl⟩
  have hnext : Runs w p ω (.assign 31 (.reg 8)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨weights,by simp [Expr.eval,mid],rfl,rfl,rfl⟩
  refine ⟨out,runs_seq_iff.mpr (Or.inr ⟨mid,5,2,hfirst,hnext,rfl⟩),
    by simp [out,mid,Function.update],by simp [out],rfl,?_⟩
  intro r h8 h31
  simp [out,mid,Function.update,h8,h31]

/-- Copy the fixed endpoints and guest lengths to the incoming cursor.
The guest weight converter will fill the next part of that workspace. -/
def stageNextGuestPrefix (copy : ℕ) : Stmt :=
  let offsets := canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)
  .seq (.assign 5 (.reg 68))
    (.call 70 copy [.reg 69,.reg 5,offsets.getD 5 (.const 0)])

/-- Staging leaves the persistent graph, current weights, and remaining
fresh memory outside the copied prefix unchanged. -/
theorem stageNextGuestPrefix_runs {w copy : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (L sim src cursor : ℕ)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hn : st.regs 0 = G.n) (hm : st.regs 1 = G.m) (hL : st.regs 2 = L)
    (hs : st.regs 3 = sim) (hsrc : st.regs 69 = src) (hcur : st.regs 68 = cursor)
    (hw : 1 < 2^w) (hguest : queryHeap G L < 2^w)
    (hsep : src+queryWeights G L ≤ cursor) (hroom : cursor+queryWeights G L < 2^w) :
    ∃ out cost, Runs w p ω (stageNextGuestPrefix copy) st .normal out cost ∧
      out.regs 5 = cursor ∧ out.regs 70 = 0 ∧ (∀ r, r ≠ 5 → r ≠ 70 → out.regs r = st.regs r) ∧
      (∀ i < queryWeights G L, out.mem (cursor+i) = st.mem (src+i)) ∧
      (∀ a, a < cursor ∨ cursor+queryWeights G L ≤ a → out.mem a = st.mem a) ∧
      cost ≤ argsSize [.reg 69,.reg 5,
        (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)] +
        17*queryWeights G L+14 := by
  let mid := {st with regs := Function.update st.regs 5 cursor}
  have hmid (r : ℕ) (hr : r ≠ 5) : mid.regs r = st.regs r := Function.update_of_ne hr ..
  have hset : mid.regs 5 = cursor := by simp [mid]
  have ha : Runs w p ω (.assign 5 (.reg 68)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨cursor,congrArg some hcur,rfl,rfl,rfl⟩
  have hargs := canonicalGuestArgsExpr_eval (w := w) (st := mid) G L sim
    (n := .reg 0) (m := .reg 1) (limbs := .reg 2) (sim := .reg 3)
    (congrArg some ((hmid _ (by decide)).trans hn))
    (congrArg some ((hmid _ (by decide)).trans hm))
    (congrArg some ((hmid _ (by decide)).trans hL))
    (congrArg some ((hmid _ (by decide)).trans hs)) hguest
  let es : List Expr := [.reg 69,.reg 5,
    (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)]
  have he : evalArgs w mid es = some [src,cursor,queryWeights G L] := by
    have hlen : ((canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5
      (.const 0)).eval w mid = some (queryWeights G L) := evalArgs_getD hargs 5
    simp only [es,evalArgs,Expr.eval,(hmid 69 (by decide)).trans hsrc,hset,hlen]
  have hwords : ∀ a ∈ [src,cursor,queryWeights G L], a < 2^w := by
    intro a h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl <;> omega
  obtain ⟨out,cost,ret,hr,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 70) hc he hwords
      ⟨src,cursor,queryWeights G L,rfl,hw,by omega,hroom.le,Or.inr hsep⟩ ω
  obtain ⟨s,d,l,heq,hzero,hcopy,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at heq
  obtain ⟨rfl,rfl,rfl⟩ := heq
  change cost ≤ argsSize es+(17*queryWeights G L+10)+1 at hcost
  refine ⟨out,2+cost+1,runs_seq_iff.mpr (Or.inr ⟨mid,2,cost,ha,hr,rfl⟩),
    (hregs _ (by decide)).trans hset,hret.trans hzero,fun r h5 h70 => (hregs r h70).trans (hmid r h5),hcopy,hframe,?_⟩
  change 2+cost+1 ≤ argsSize es+17*queryWeights G L+14
  omega

/-- Copying the prefix transfers its indexed endpoints and encoded
lengths to the fresh guest workspace. -/
theorem stagedGuestPrefix_arrays (G : MGraph) (L src dst : ℕ)
    (len : ℕ → ℤ) (mem out : ℕ → ℕ)
    (hcopy : ∀ i < queryWeights G L, out (dst+i) = mem (src+i))
    (ht : ∀ i < G.m, mem (src+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, mem (src+(G.m+i)) = (indexedGraph G).head i)
    (hlen : ∀ i < G.m, ListAt mem (src+queryLengths G+i*L)
      (encodeLimbs 1 L (len (edgeName G i)))) :
    (∀ i < G.m, out (dst+i) = (indexedGraph G).tail i) ∧
    (∀ i < G.m, out (dst+(G.m+i)) = (indexedGraph G).head i) ∧
    (∀ i < G.m, ListAt out (dst+queryLengths G+i*L)
      (encodeLimbs 1 L (len (edgeName G i)))) := by
  have hb : 2*G.m ≤ queryWeights G L := by
    unfold queryWeights queryLengths
    omega
  refine ⟨fun i hi => (hcopy i (by omega)).trans (ht i hi),
    fun i hi => (hcopy (G.m+i) (by omega)).trans (hh i hi),?_⟩
  intro i hi k hk
  have hkL : k < L := by simpa using hk
  have hm := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hm
  have hidx : queryLengths G+i*L+k < queryWeights G L := by
    unfold queryWeights
    omega
  have h := (hcopy _ hidx).trans (show mem (src+(queryLengths G+i*L+k)) = _ from by
    simpa only [← Nat.add_assoc] using hlen i hi k hk)
  simpa only [← Nat.add_assoc] using h

/-- Collection header and weight initialization write above the persistent
guest prefix, so the first round can read its endpoints and length blocks. -/
theorem stagedGuestPrefix_of_agreeBelow (G : MGraph) (L src : ℕ)
    (len : ℕ → ℤ) (mem out : ℕ → ℕ)
    (hframe : ∀ a < src+queryWeights G L, out a = mem a)
    (hends : ∀ i < G.m, mem (src+i) = (indexedGraph G).tail i ∧
      mem (src+(G.m+i)) = (indexedGraph G).head i)
    (hlen : ∀ i < G.m, ListAt mem (src+queryLengths G+i*L)
      (encodeLimbs 1 L (len (edgeName G i)))) :
    (∀ i < G.m, out (src+i) = (indexedGraph G).tail i) ∧
    (∀ i < G.m, out (src+(G.m+i)) = (indexedGraph G).head i) ∧
    (∀ i < G.m, ListAt out (src+queryLengths G+i*L)
      (encodeLimbs 1 L (len (edgeName G i)))) :=
  stagedGuestPrefix_arrays G L src src len mem out
    (fun i hi => hframe (src+i) (Nat.add_lt_add_left hi _))
    (fun i hi => (hends i hi).1) (fun i hi => (hends i hi).2) hlen

/-- Updating a branch pointer in the collection table leaves the
persistent guest prefix below it readable in the next round. -/
theorem stagedGuestPrefix_afterRound (G : MGraph) (L src collection slot cursor : ℕ)
    (len : ℕ → ℤ) (mem out : ℕ → ℕ)
    (hprefix : src+queryWeights G L ≤ collection)
    (hslot : collection ≤ slot) (hcursor : collection ≤ cursor)
    (hframe : ∀ a < cursor, a ≠ slot → out a = mem a)
    (hends : ∀ i < G.m, mem (src+i) = (indexedGraph G).tail i ∧
      mem (src+(G.m+i)) = (indexedGraph G).head i)
    (hlen : ∀ i < G.m, ListAt mem (src+queryLengths G+i*L)
      (encodeLimbs 1 L (len (edgeName G i)))) :
    (∀ i < G.m, out (src+i) = (indexedGraph G).tail i) ∧
    (∀ i < G.m, out (src+(G.m+i)) = (indexedGraph G).head i) ∧
    (∀ i < G.m, ListAt out (src+queryLengths G+i*L)
      (encodeLimbs 1 L (len (edgeName G i)))) :=
  stagedGuestPrefix_of_agreeBelow G L src len mem out
    (fun a ha => hframe a (by omega) (by omega)) hends hlen

/-- Stage the live query, run a numeric pass, prepare its output layout,
and append the branch before returning the next cursor. -/
def stagedPublishedRoundWith (copy unit restore init scatter publish : ℕ)
    (numeric layout : Stmt) : Stmt :=
  .seq (.seq loadStagedRoundWeights (stageNextGuestPrefix copy))
    (.seq numeric (.seq layout
      (.seq (stagedBranchAppendBody unit restore init scatter publish) stagedRoundWeightCursor)))

/-- Run one staged round and return the end of its published branch.
Pass the guest arguments and the runtime host limb count to the selector. -/
def stagedPublishedRoundBody
    (select dedup copy pack packWeights prepare adjacency numeric unit restore init scatter publish :
      ℕ) : Stmt :=
  stagedPublishedRoundWith copy unit restore init scatter publish
    (stagedRebuildRoundBody select dedup copy pack packWeights prepare adjacency numeric
      convertedGuestCallArgs) installStagedOutputLayout

/-- Link the numeric run, output address setup, and branch append to the
callable round interface. The loop receives the branch end as its cursor. -/
theorem stagedPublishedRoundWith_meetsContract
    {w entry copy unit restore init scatter publish : ℕ} {numeric layout : Stmt} {p : Program}
    (he : p.procs[entry]? = some
      (stagedPublishedRoundWith copy unit restore init scatter publish numeric layout))
    (C : Contract) (G : MGraph) (L sim src : ℕ)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hstage : ∀ args mem pos stop, C.pre args mem →
      let st := startState args mem pos
      st.regs 68 = stop+1 →
      st.regs 0 = G.n ∧ st.regs 1 = G.m ∧ st.regs 2 = L ∧ st.regs 3 = sim ∧
      st.regs 69 = src ∧ 1 < 2^w ∧ queryHeap G L < 2^w ∧
      src+queryWeights G L ≤ stop+1 ∧ stop+1+queryWeights G L < 2^w)
    (hload : ∀ args mem pos, C.pre args mem → ∃ stop weights,
      (startState args mem pos).regs 68 = stop+1 ∧ mem stop = weights ∧ stop+1 < 2^w)
    (hrun : ∀ args mem pos ω, (∀ x ∈ args, x < 2^w) → C.pre args mem →
      ∀ staged inputWeights cursor, (startState args mem pos).regs 68 = cursor →
        mem (cursor-1) = inputWeights → staged.regs 5 = cursor →
        staged.regs 8 = inputWeights → staged.regs 31 = inputWeights → staged.regs 70 = 0 →
        (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
          staged.regs r = (startState args mem pos).regs r) →
        (∀ i < queryWeights G L, staged.mem (cursor+i) = mem (src+i)) →
        (∀ a, a < cursor ∨ cursor+queryWeights G L ≤ a → staged.mem a = mem a) →
      ∃ mid ready out cn cl cb stop weights,
        Runs w p ω
          numeric
          staged .normal mid cn ∧
        Runs w p ω layout mid .normal ready cl ∧
        Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
          ready .normal out cb ∧
        out.regs 54 = stop ∧ out.regs 38 = weights ∧ stop+1 < 2^w ∧
        ZeroFrom out.mem stop ∧
        C.post args mem (stop+1) (Function.update out.mem stop weights) ∧
        cn+cl+cb+21+17*queryWeights G L+14+
          argsSize [.reg 69,.reg 5,
            (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)]
          ≤ C.cost args mem) :
    MeetsContract w p entry C := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨incoming,inputWeights,hcursor,hweight,hinFit⟩ := hload args mem pos hpre
  obtain ⟨loaded,hloaded,hg,hh,hinput,hregs⟩ :=
    loadStagedRoundWeights_runs (p := p) (ω := ω) (startState args mem pos)
      incoming inputWeights hcursor hweight hinFit
  obtain ⟨hn',hm',hL',hs',hsrc',hw',hguest,hsep,hfit⟩ := hstage args mem pos incoming hpre hcursor
  obtain ⟨staged,cs,hst,hstaging,h70,hsregs,hcopied,hframe,hcs⟩ :=
    stageNextGuestPrefix_runs (ω := ω) loaded G L sim src (incoming+1) hcopy
      ((hregs _ (by decide) (by decide)).trans hn')
      ((hregs _ (by decide) (by decide)).trans hm')
      ((hregs _ (by decide) (by decide)).trans hL')
      ((hregs _ (by decide) (by decide)).trans hs')
      ((hregs _ (by decide) (by decide)).trans hsrc')
      ((hregs _ (by decide) (by decide)).trans hcursor) hw' hguest hsep hfit
  obtain ⟨mid,ready,out,cn,cl,cb,stop,weights,hn,hl,hb,hs,hw,hroom,hz,hpost,hcost⟩ :=
    hrun args mem pos ω hwords hpre staged inputWeights (incoming+1) hcursor
      (by simpa only [Nat.add_sub_cancel] using hweight) hstaging
      ((hsregs _ (by decide) (by decide)).trans hg)
      ((hsregs _ (by decide) (by decide)).trans hh) h70
      (fun r h5 h8 h31 h70 => (hsregs r h5 h70).trans (hregs r h8 h31))
      (by simpa only [hinput,startState] using hcopied) (by simpa only [hinput,startState] using hframe)
  obtain ⟨final,hret,hmem,_,_,_⟩ :=
    stagedRoundWeightCursor_runs (p := p) (ω := ω) out stop weights hs hw hroom hz
  have happend := runs_seq_iff.mpr (Or.inr ⟨out,cb,8,hb,hret,rfl⟩)
  have hout := runs_seq_iff.mpr (Or.inr ⟨ready,cl,cb+9,hl,happend,rfl⟩)
  have hround := runs_seq_iff.mpr (Or.inr ⟨mid,cn,cl+(cb+9)+1,hn,hout,rfl⟩)
  have hsetup := runs_seq_iff.mpr (Or.inr ⟨loaded,8,cs,hloaded,hst,rfl⟩)
  exact ⟨.returned (stop+1),final,(8+cs+1)+(cn+(cl+(cb+9)+1)+1)+1,
    runs_seq_iff.mpr (Or.inr ⟨staged,8+cs+1,_,hsetup,hround,rfl⟩),hmem.symm ▸ hpost,by omega⟩

/-- Link the numeric run, output address setup, and branch append to the
callable round interface. The loop receives the branch end as its cursor. -/
theorem stagedPublishedRound_meetsContract
    {w entry select dedup copy pack packWeights prepare adjacency numeric
      unit restore init scatter publish : ℕ} {p : Program}
    (he : p.procs[entry]? = some
      (stagedPublishedRoundBody select dedup copy pack packWeights prepare adjacency numeric
        unit restore init scatter publish))
    (C : Contract) (G : MGraph) (L sim src : ℕ)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hstage : ∀ args mem pos stop, C.pre args mem →
      let st := startState args mem pos
      st.regs 68 = stop+1 →
      st.regs 0 = G.n ∧ st.regs 1 = G.m ∧ st.regs 2 = L ∧ st.regs 3 = sim ∧
      st.regs 69 = src ∧ 1 < 2^w ∧ queryHeap G L < 2^w ∧
      src+queryWeights G L ≤ stop+1 ∧ stop+1+queryWeights G L < 2^w)
    (hload : ∀ args mem pos, C.pre args mem → ∃ stop weights,
      (startState args mem pos).regs 68 = stop+1 ∧ mem stop = weights ∧ stop+1 < 2^w)
    (hrun : ∀ args mem pos ω, (∀ x ∈ args, x < 2^w) → C.pre args mem →
      ∀ staged inputWeights cursor, (startState args mem pos).regs 68 = cursor →
        mem (cursor-1) = inputWeights → staged.regs 5 = cursor →
        staged.regs 8 = inputWeights → staged.regs 31 = inputWeights →
        (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
          staged.regs r = (startState args mem pos).regs r) →
        (∀ i < queryWeights G L, staged.mem (cursor+i) = mem (src+i)) →
        (∀ a, a < cursor ∨ cursor+queryWeights G L ≤ a → staged.mem a = mem a) →
      ∃ mid ready out cn cl cb stop weights,
        Runs w p ω
          (stagedRebuildRoundBody select dedup copy pack packWeights prepare adjacency numeric
            convertedGuestCallArgs)
          staged .normal mid cn ∧
        Runs w p ω installStagedOutputLayout mid .normal ready cl ∧
        Runs w p ω (stagedBranchAppendBody unit restore init scatter publish)
          ready .normal out cb ∧
        out.regs 54 = stop ∧ out.regs 38 = weights ∧ stop+1 < 2^w ∧
        ZeroFrom out.mem stop ∧
        C.post args mem (stop+1) (Function.update out.mem stop weights) ∧
        cn+cl+cb+21+17*queryWeights G L+14+
          argsSize [.reg 69,.reg 5,
            (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)]
          ≤ C.cost args mem) :
    MeetsContract w p entry C :=
  stagedPublishedRoundWith_meetsContract he C G L sim src hcopy hstage hload (fun args mem pos ω hwords hpre staged weight cursor hc hw h5 h8 h31 _ =>
    hrun args mem pos ω hwords hpre staged weight cursor hc hw h5 h8 h31)

end MinCostFlow.LastLevelProgram
