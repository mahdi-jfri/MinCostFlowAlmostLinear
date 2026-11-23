module

public import MinCostFlow.LastLevelProgram.StagedBranchAppend
public import MinCostFlow.LastLevelProgram.StagedWideInputs
public import MinCostFlow.LastLevelProgram.CanonicalModel
import MinCostFlow.DynSpanner.Program.DynGraphInit
import Mathlib.Data.Nat.Size

/-!
# Running the staged collection loop

The controller for Definition 5.8 (pages 19–20) links the rounds and publishes the collection.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num SparseCore Scaling.Machine DynSpanner.Program

/-- Link weight initialization and final publication around the installed
round loop. The loop uses the same cursor invariant at entry and exit. -/
theorem stagedControllerAtStride_runs
    {w init weights round copy vCap eCap h L P caller base count handle bound loopCost step stride : ℕ}
    {p : Program} {ω : ℕ → Bool} {E : Finset ℕ} {branches : ℕ → LSF}
    (st : State) (H : MGraph) (ρ B : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hi : MeetsContract w p init (initCollectionContract w))
    (hweights : MeetsContract w p weights (stagedInitialWeightContract w h P B))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h1 : st.regs 1 = count) (h3 : st.regs 3 = base) (h151 : st.regs 151 = handle)
    (hm : st.regs 73 = H.m) (hP : st.regs 95 = P)
    (hs : st.regs 104 = stride) (hstride : L ≤ stride) (hL : st.regs 127 = L)
    (hregs : ∀ r, st.regs r < 2^w) (hw : 1 < 2^w) (hmPos : 0 < H.m)
    (hB : 1 ≤ B) (hwidth : 2*(2 : ℝ)^P*B < capacity h L)
    (hz : ZeroFrom st.mem base) (hfit : bound < 2^w) (hsep : handle+1+count ≤ base)
    (hinitEnd : base+1+count+2*L+H.m*stride+1+count*step ≤ bound)
    (hloop :
      let Inv := stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query st.mem
      Triple w p (fun ready => (Inv 0 ready ∧ ready.regs 0+count*step ≤ bound) ∧ ∀ r, ready.regs r < 2^w)
        (lastLevelRoundsBody round publishedRoundArgs)
        (normalPost (Inv count)) (fun _ => loopCost)) :
    ∃ o out cost, Runs w p ω (rebuildCollectionThen init weights round
        initialWeightControllerArgs publishedRoundArgs (publishRuntimeCollection copy)) st o out cost ∧
      (∃ limit, o = .returned limit ∧ handle+1+count ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem handle count count limit vCap eCap h L caller E branches ∧
        ZeroFrom out.mem limit ∧ (∀ a < handle, out.mem a = st.mem a)) ∧
      cost ≤ argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+loopCost+
        (17*(count+1)+19)+17 := by
  apply stagedCollectionThen_runs st base count L stride H.m loopCost
    (17*(count+1)+19) B (publishRuntimeCollection copy) _ _ _
    hi hweights h3 h1 hm hP hs hL hregs hw hstride hB hwidth hz
    (show base+1+count+2*L+H.m*stride+1 < 2^w by omega) _ hloop
    (stagedRoundStateAtStride_publish H ρ query st.mem hcopy hw hsep hfit)
  intro next out pos dst stop hnext hptr hzero hcount hframe hunit
  dsimp only [dst,stop] at hnext hptr hunit
  have hn : next ≤ bound := by omega
  refine ⟨⟨stagedRoundStateAtStride_initial st out pos h1 h3 h151 hmPos hstride hnext
    (by simpa only [hnext,Nat.add_sub_cancel] using hptr) hn hzero hframe hcount hunit, ?_⟩, ?_⟩
  · simpa only [Function.update_self, hnext] using hinitEnd
  · intro r
    by_cases hr : r = 0
    · subst r
      simpa [Function.update] using hn.trans_lt hfit
    · simpa only [Function.update_of_ne hr] using hregs r

/-- Keep the prepared registers available to every round after initial
weight setup changes the cursor. -/
theorem stagedControllerAtStride_fixedRegisters_runs
    {w init weights round copy vCap eCap h L P caller base count handle bound loopCost step stride : ℕ}
    {p : Program} {ω : ℕ → Bool} {E : Finset ℕ} {branches : ℕ → LSF}
    (st : State) (H : MGraph) (ρ B : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hi : MeetsContract w p init (initCollectionContract w))
    (hweights : MeetsContract w p weights (stagedInitialWeightContract w h P B))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h1 : st.regs 1 = count) (h3 : st.regs 3 = base) (h151 : st.regs 151 = handle)
    (hm : st.regs 73 = H.m) (hP : st.regs 95 = P)
    (hs : st.regs 104 = stride) (hstride : L ≤ stride) (hL : st.regs 127 = L)
    (hregs : ∀ r, st.regs r < 2^w) (hw : 1 < 2^w) (hmPos : 0 < H.m)
    (hB : 1 ≤ B) (hwidth : 2*(2 : ℝ)^P*B < capacity h L)
    (hz : ZeroFrom st.mem base) (hfit : bound < 2^w) (hsep : handle+1+count ≤ base)
    (hinitEnd : base+1+count+2*L+H.m*stride+1+count*step ≤ bound)
    (hloop :
      let Inv := stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query st.mem
      Triple w p (fun ready => (Inv 0 ready ∧ ready.regs 0+count*step ≤ bound) ∧
        (∀ r, ready.regs r < 2^w) ∧ ∀ r, 4 ≤ r → ready.regs r = st.regs r)
        (lastLevelRoundsBody round publishedRoundArgs)
        (normalPost (Inv count)) (fun _ => loopCost)) :
    ∃ o out cost, Runs w p ω (rebuildCollectionThen init weights round
        initialWeightControllerArgs publishedRoundArgs (publishRuntimeCollection copy)) st o out cost ∧
      (∃ limit, o = .returned limit ∧ handle+1+count ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem handle count count limit vCap eCap h L caller E branches ∧
        ZeroFrom out.mem limit ∧ (∀ a < handle, out.mem a = st.mem a)) ∧
      cost ≤ argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+loopCost+
        (17*(count+1)+19)+17 := by
  apply stagedCollectionThen_runs st base count L stride H.m loopCost
    (17*(count+1)+19) B (publishRuntimeCollection copy) _ _ _
    hi hweights h3 h1 hm hP hs hL hregs hw hstride hB hwidth hz
    (show base+1+count+2*L+H.m*stride+1 < 2^w by omega) _ hloop
    (stagedRoundStateAtStride_publish H ρ query st.mem hcopy hw hsep hfit)
  intro next out pos dst stop hnext hptr hzero hcount hframe hunit
  dsimp only [dst,stop] at hnext hptr hunit
  have hn : next ≤ bound := by omega
  refine ⟨⟨stagedRoundStateAtStride_initial st out pos h1 h3 h151 hmPos hstride hnext
    (by simpa only [hnext,Nat.add_sub_cancel] using hptr) hn hzero hframe hcount hunit, ?_⟩, ?_, ?_⟩
  · simpa only [Function.update_self, hnext] using hinitEnd
  · intro r
    by_cases hr : r = 0
    · subst r
      simpa [Function.update] using hn.trans_lt hfit
    · simpa only [Function.update_of_ne hr] using hregs r

  · intro r hr
    exact Function.update_of_ne (show r ≠ 0 by omega) _ _

/-- Link weight initialization and final publication around the installed
round loop. The loop uses the same cursor invariant at entry and exit. -/
theorem stagedController_runs
    {w init weights round copy vCap eCap h L P caller base count handle bound loopCost step : ℕ}
    {p : Program} {ω : ℕ → Bool} {E : Finset ℕ} {branches : ℕ → LSF}
    (st : State) (H : MGraph) (ρ B : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ)
    (hi : MeetsContract w p init (initCollectionContract w))
    (hweights : MeetsContract w p weights (stagedInitialWeightContract w h P B))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (h1 : st.regs 1 = count) (h3 : st.regs 3 = base) (h151 : st.regs 151 = handle)
    (hm : st.regs 73 = H.m) (hP : st.regs 95 = P)
    (hs : st.regs 104 = narrowWeightSpace L) (hL : st.regs 127 = L)
    (hregs : ∀ r, st.regs r < 2^w) (hw : 1 < 2^w) (hmPos : 0 < H.m)
    (hB : 1 ≤ B) (hwidth : 2*(2 : ℝ)^P*B < capacity h L)
    (hz : ZeroFrom st.mem base) (hfit : bound < 2^w) (hsep : handle+1+count ≤ base)
    (hinitEnd : base+1+count+2*L+H.m*narrowWeightSpace L+1+count*step ≤ bound)
    (hloop :
      let Inv := stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query st.mem
      Triple w p (fun ready => (Inv 0 ready ∧ ready.regs 0+count*step ≤ bound) ∧ ∀ r, ready.regs r < 2^w)
        (lastLevelRoundsBody round publishedRoundArgs)
        (normalPost (Inv count)) (fun _ => loopCost)) :
    ∃ o out cost, Runs w p ω (rebuildCollectionThen init weights round
        initialWeightControllerArgs publishedRoundArgs (publishRuntimeCollection copy)) st o out cost ∧
      (∃ limit, o = .returned limit ∧ handle+1+count ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem handle count count limit vCap eCap h L caller E branches ∧
        ZeroFrom out.mem limit ∧ (∀ a < handle, out.mem a = st.mem a)) ∧
      cost ≤ argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+loopCost+
        (17*(count+1)+19)+17 :=
  stagedControllerAtStride_runs st H ρ B query hi hweights hcopy h1 h3 h151 hm hP hs
    (by unfold narrowWeightSpace; omega) hL hregs hw hmPos hB hwidth hz hfit hsep hinitEnd hloop

/-- Start the staged controller after guest format selection. The final setup
installs the branch count and weight stride while retaining the handle. -/
theorem stagedPreparedController_runs
    {w init weights round copy vCap eCap h L P caller guestL sim src handle bound loopCost step : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (ℓ : ℕ → ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C ρ B : ℝ)
    (query : (ℕ → ℝ) → ℕ → ℝ)
    (hi : MeetsContract w p init (initCollectionContract w))
    (hweights : MeetsContract w p weights (stagedInitialWeightContract w h P B))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hnl : (nonLoopEdges G).Nonempty) (hw : 1 < 2^w)
    (hL : st.regs 127 = L) (hP : st.regs 95 = P) (h151 : st.regs 151 = handle)
    (hguestL : st.regs 74 = guestL) (hsim : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hstride : narrowWeightSpace L < 2^w) (hfit : bound < 2^w)
    (hB : 1 ≤ B) (hwidth : 2*(2 : ℝ)^P*B < capacity h L) :
    let H := representativeGraph G ℓ
    let base := src+queryWeights H guestL
    let s := (fixedPointLastLevelTool oracle C).build G ℓ
    let Inv := stagedRoundState H vCap eCap h L P caller base s.1 handle bound G.E s.2 ρ query st.mem
    st.regs 72 = H.n → st.regs 73 = H.m → 0 < H.m → queryHeap H guestL < 2^w →
    handle+1+s.1 ≤ base → ZeroFrom st.mem base →
    base+1+s.1+2*L+H.m*narrowWeightSpace L+1+s.1*step ≤ bound →
    (∀ r, st.regs r < 2^w) →
    Triple w p (fun ready => (Inv 0 ready ∧ ready.regs 0+s.1*step ≤ bound) ∧ ∀ r, ready.regs r < 2^w)
        (lastLevelRoundsBody round publishedRoundArgs)
      (normalPost (Inv s.1)) (fun _ => loopCost) →
    ∃ o out cost, Runs w p ω (stagedPreparedCollectionThen init weights round
        (publishRuntimeCollection copy)) st o out cost ∧
      (∃ limit, o = .returned limit ∧ handle+1+s.1 ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem handle s.1 s.1 limit vCap eCap h L caller G.E s.2 ∧
        ZeroFrom out.mem limit ∧ (∀ a < handle, out.mem a = st.mem a)) ∧
      cost ≤ 2*(narrowWeightSpaceExpr (.reg 127)).size+collectionHeaderAddress.size+17+
        (argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+loopCost+
          (17*(s.1+1)+19)+17) := by
  intro H base s Inv hn hm hmPos hheap hsep hz hinitEnd hwords hloop
  have hbaseFit : base < 2^w := by omega
  apply stagedPreparedCollectionThen_runs st oracle C G ℓ L P guestL sim src _
    (publishRuntimeCollection copy) _ hnl hL hP hstride hn hm hguestL hsim hsrc hheap hbaseFit
  intro ready h1 h3 h81 h82 h91 h104 hmem hkeep
  change ready.regs 1 = s.1 at h1
  change ready.regs 3 = base at h3
  have hPFit := hwords 95
  have hLFit := hwords 127
  rw [hP] at hPFit
  rw [hL] at hLFit
  have hrwords (r : ℕ) : ready.regs r < 2^w := by
    by_cases hr : r ∈ ([1,3,81,82,91,104] : List ℕ)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rw [h1] | rw [h3] | rw [h81] | rw [h82] | rw [h91] | rw [h104]
      all_goals omega
    · rw [hkeep r hr]
      exact hwords r
  obtain ⟨o,out,cost,hr,⟨limit,hret,hlo,hhi,hprefix,hzero,hframe⟩,hc⟩ :=
    stagedController_runs (ω := ω) ready H ρ B query hi hweights hcopy h1 h3
    ((hkeep 151 (by decide)).trans h151) ((hkeep 73 (by decide)).trans hm)
    ((hkeep 95 (by decide)).trans hP) h104 ((hkeep 127 (by decide)).trans hL)
    hrwords hw hmPos hB hwidth (hmem.symm ▸ hz) hfit hsep hinitEnd
      (by simpa only [hmem,Inv] using hloop)
  exact ⟨o,out,cost,hr,⟨limit,hret,hlo,hhi,hprefix,hzero,fun a ha =>
    (hframe a ha).trans (congrFun hmem a)⟩,hc⟩


/-- Start the staged controller after guest format selection. The final setup
installs the branch count and weight stride while retaining the handle. -/
theorem stagedCompactPreparedController_runs
    {w init weights round copy vCap eCap h L P caller guestL sim src handle bound loopCost step : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (ℓ : ℕ → ℝ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C ρ B : ℝ)
    (query : (ℕ → ℝ) → ℕ → ℝ)
    (hi : MeetsContract w p init (initCollectionContract w))
    (hweights : MeetsContract w p weights (stagedInitialWeightContract w h P B))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hnl : (nonLoopEdges G).Nonempty) (hw : 1 < 2^w)
    (hL : st.regs 127 = L) (hP : st.regs 95 = P) (h151 : st.regs 151 = handle)
    (hguestL : st.regs 74 = guestL) (hsim : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hfit : bound < 2^w)
    (hB : 1 ≤ B) (hwidth : 2*(2 : ℝ)^P*B < capacity h L) :
    let H := representativeGraph G ℓ
    let base := src+queryWeights H guestL
    let s := (fixedPointLastLevelTool oracle C).build G ℓ
    let Inv := stagedRoundStateAtStride H vCap eCap h L P caller base s.1 handle bound L G.E s.2 ρ query st.mem
    st.regs 72 = H.n → st.regs 73 = H.m → 0 < H.m → queryHeap H guestL < 2^w →
    handle+1+s.1 ≤ base → ZeroFrom st.mem base →
    base+1+s.1+2*L+H.m*L+1+s.1*step ≤ bound →
    (∀ r, st.regs r < 2^w) →
    (∀ prepared : State, prepared.regs 81 = L → prepared.regs 82 = P →
      prepared.regs 91 = L → prepared.regs 104 = L →
      (∀ r, r ∉ ([1,3,81,82,91,104] : List ℕ) → prepared.regs r = st.regs r) →
      Triple w p
        (fun ready => (Inv 0 ready ∧ ready.regs 0+s.1*step ≤ bound) ∧
          (∀ r, ready.regs r < 2^w) ∧ ∀ r, 4 ≤ r → ready.regs r = prepared.regs r)
        (lastLevelRoundsBody round publishedRoundArgs)
        (normalPost (Inv s.1)) (fun _ => loopCost)) →
    ∃ o out cost, Runs w p ω (stagedCompactCollectionThen init weights round copy) st o out cost ∧
      (∃ limit, o = .returned limit ∧ handle+1+s.1 ≤ limit ∧ limit ≤ bound ∧
        CollectionPrefix out.mem handle s.1 s.1 limit vCap eCap h L caller G.E s.2 ∧
        ZeroFrom out.mem limit ∧ (∀ a < handle, out.mem a = st.mem a)) ∧
      cost ≤ collectionHeaderAddress.size+20+
        (argsSize initialWeightControllerArgs+((17*L+27)*H.m+56*L+111)+loopCost+
          (17*(s.1+1)+19)+17) := by
  intro H base s Inv hn hm hmPos hheap hsep hz hinitEnd hwords hloop
  have hbaseFit : base < 2^w := by omega
  obtain ⟨ready,setupCost,hsetup,h1,h3,h81,h82,h91,h104,hmem,hkeep,hsc⟩ :=
    finishCompactCollectionSetup_runs (p := p) (ω := ω) st oracle C G ℓ L P guestL sim src
      hnl hL hP hn hm hguestL hsim hsrc hheap hbaseFit
  change ready.regs 1 = s.1 at h1
  change ready.regs 3 = base at h3
  have hPFit := hwords 95
  have hLFit := hwords 127
  rw [hP] at hPFit
  rw [hL] at hLFit
  have hrwords (r : ℕ) : ready.regs r < 2^w := by
    by_cases hr : r ∈ ([1,3,81,82,91,104] : List ℕ)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rw [h1] | rw [h3] | rw [h81] | rw [h82] | rw [h91] | rw [h104]
      all_goals omega
    · rw [hkeep r hr]
      exact hwords r
  obtain ⟨o,out,cost,hr,⟨limit,hret,hlo,hhi,hprefix,hzero,hframe⟩,hc⟩ :=
    stagedControllerAtStride_fixedRegisters_runs (ω := ω) ready H ρ B query hi hweights hcopy h1 h3
    ((hkeep 151 (by decide)).trans h151) ((hkeep 73 (by decide)).trans hm)
    ((hkeep 95 (by decide)).trans hP) h104 le_rfl ((hkeep 127 (by decide)).trans hL)
    hrwords hw hmPos hB hwidth (hmem.symm ▸ hz) hfit hsep hinitEnd
      (by simpa only [hmem,Inv] using hloop ready h81 h82 h91 h104 hkeep)
  exact ⟨o,out,setupCost+cost+1,runs_seq_iff.mpr (Or.inr ⟨ready,setupCost,cost,hsetup,hr,rfl⟩),
    ⟨limit,hret,hlo,hhi,hprefix,hzero,fun a ha =>
      (hframe a ha).trans (congrFun hmem a)⟩,by omega⟩

/-- The fixed integer installed in the controller yields the update scale
and grid of the graph-canonical model. -/
theorem canonicalController_scale (K fallback : ℝ) (H : MGraph) (d : ℕ)
    (hd : d = graphCanonicalIntegerConstant K fallback) :
    (integerScale d H : ℝ) = roundedScale (graphCanonicalConstant K fallback) H ∧
      (2*integerScale d H).size = weightPrecision (graphCanonicalConstant K fallback) H := by
  rw [hd,graphCanonicalIntegerConstant_eq]
  exact ⟨rfl,rfl⟩

/-- Updating the cursor and loop index leaves all other round arguments
unchanged and maintains word-sized arguments for the next call. -/
theorem stagedController_nextWords {w next j pos : ℕ} (st : State) (out : ℕ → ℕ)
    (hwords : ∀ r, st.regs r < 2^w) (hnext : next < 2^w) (hj : j+1 < 2^w) :
    let s : State := ⟨out,Function.update (Function.update st.regs 0 next) 2 (j+1),pos⟩
    (∀ r, s.regs r < 2^w) ∧ ∀ r, r ≠ 0 → r ≠ 2 → s.regs r = st.regs r := by
  intro s
  have hkeep r (h0 : r ≠ 0) (h2 : r ≠ 2) : s.regs r = st.regs r := by
    simp [s,Function.update_of_ne h0,Function.update_of_ne h2]
  refine ⟨?_,hkeep⟩
  intro r
  by_cases h0 : r = 0
  · subst r
    simpa [s,Function.update] using hnext
  by_cases h2 : r = 2
  · subst r
    simpa [s,Function.update] using hj
  rw [hkeep r h0 h2]
  exact hwords r

/-- The staged loop keeps all argument words in range. Each round needs
only its precondition and the proof that its postcondition advances the invariant. -/
theorem stagedControllerRounds_words
    {w entry vCap eCap h L P caller base count handle bound budget : ℕ}
    {p : Program} {E : Finset ℕ} {branches : ℕ → LSF}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ)
    (hw : 1 < 2^w) (hcount : count < 2^w) (hbound : bound < 2^w) :
    let Inv := stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem
    (∀ j < count, ∀ st, Inv j st → st.regs 2 = j →
      let args := (List.range 70).map (st.regs ∘ roundControllerRegister)
      ∃ C : Contract, MeetsContract w p entry C ∧ C.pre args st.mem ∧ C.cost args st.mem ≤ budget ∧
        ∀ ret out pos, C.post args st.mem ret out →
          Inv (j+1) ⟨out,Function.update (Function.update st.regs 0 ret) 2 (j+1),pos⟩) →
    Triple w p (fun st => Inv 0 st ∧ ∀ r, st.regs r < 2^w)
      (lastLevelRoundsBody entry publishedRoundArgs) (normalPost (Inv count))
      (fun _ => (argsSize publishedRoundArgs+budget+10)*count+7) := by
  intro Inv hstep
  let J := fun j (st : State) => Inv j st ∧ ∀ r, st.regs r < 2^w
  have hloop := lastLevelRounds_triple (p := p) (entry := entry) (args := publishedRoundArgs)
    count budget J hw hcount
    (fun st hs => by
      refine ⟨stagedRoundState_resetIndex hs.1,?_⟩
      intro r
      by_cases hr : r = 2
      · subst r
        simp [show 0 < 2^w by omega]
      · simpa only [Function.update_of_ne hr] using hs.2 r)
    (fun _ _ hs => hs.1.1)
    (fun j hj st hs hidx => by
      obtain ⟨C,hc,hpre,hcost,hpost⟩ := hstep j hj st hs.1 hidx
      refine ⟨C,_,hc,publishedRoundArgs_eval w st,?_,hpre,hcost,?_⟩
      · intro a ha
        obtain ⟨r,_,rfl⟩ := List.mem_map.mp ha
        exact hs.2 _
      · intro ret out pos hr
        have hn := hpost ret out pos hr
        have hret : ret ≤ bound := by
          have h := hn.2.2.2.2.1
          simpa [Function.update] using h
        exact ⟨hn,(stagedController_nextWords st out hs.2 (hret.trans_lt hbound) (by omega)).1⟩)
  refine hloop.conseq (fun _ hs => hs) ?_ (fun _ _ => le_rfl)
  intro o st hs
  cases o with
  | normal => exact hs.1
  | returned _ => exact hs

/-- The controller's call words expose the packed graph, simulation width,
and incoming weight descriptor in the round procedure. -/
theorem stagedController_roundEntry {w vCap eCap h L P caller base count handle bound guestL sim src j stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st : State) (pos : ℕ)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem j st)
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hbase : src+queryWeights H guestL = base)
    (hfit : bound+queryWeights H guestL < 2^w) :
    let entered := startState ((List.range 70).map (st.regs ∘ roundControllerRegister)) st.mem pos
    let stop := st.regs 0-1
    entered.regs 0 = H.n ∧ entered.regs 1 = H.m ∧ entered.regs 2 = guestL ∧
    entered.regs 3 = sim ∧ entered.regs 69 = src ∧ entered.regs 68 = stop+1 ∧
    src+queryWeights H guestL ≤ stop+1 ∧ stop+1+queryWeights H guestL < 2^w := by
  intro entered stop
  have hc := (publishedRoundArgs_startState st st.mem pos).2.2
  obtain ⟨_,_,_,hle,hbound,_⟩ := hs
  have hc' : entered.regs 68 = st.regs 0 := hc
  have hcursor : st.regs 0 = stop+1 := by dsimp [stop]; omega
  refine ⟨?_,?_,?_,?_,?_,hc'.trans hcursor,?_,?_⟩
  · simpa [entered,startState,roundControllerRegister,List.getD] using hn
  · simpa [entered,startState,roundControllerRegister,List.getD] using hm
  · simpa [entered,startState,roundControllerRegister,List.getD] using hguest
  · simpa [entered,startState,roundControllerRegister,List.getD] using hsim
  · simpa [entered,startState,roundControllerRegister,List.getD] using hsrc
  · omega
  · omega

/-- The incoming cursor is positive and its preceding word points to the
current weights. The loader sees the same descriptor as the invariant. -/
theorem stagedController_roundDescriptor {w vCap eCap h L P caller base count handle bound j stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st : State) (pos : ℕ)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem j st)
    (hfit : bound < 2^w) :
    ∃ stop weight,
      (startState ((List.range 70).map (st.regs ∘ roundControllerRegister)) st.mem pos).regs 68 =
        stop+1 ∧ st.mem stop = weight ∧ stop+1 < 2^w ∧ weight ≤ stop := by
  obtain ⟨_,_,_,hspan,hbound,_,_,_,hweight,_⟩ := hs
  have hc := (publishedRoundArgs_startState st st.mem pos).2.2
  exact ⟨st.regs 0-1,st.mem (st.regs 0-1),hc.trans (by omega),rfl,by omega,by omega⟩

/-- A round contract fixes the current controller arguments and advances
the invariant at every return position. -/
@[expose] def stagedControllerRoundContract (st : State) (Inv : State → Prop) (j budget : ℕ) : Contract where
  pre args mem := args = (List.range 70).map (st.regs ∘ roundControllerRegister) ∧ mem = st.mem
  post _ _ ret out := ∀ pos,
    Inv ⟨out,Function.update (Function.update st.regs 0 ret) 2 (j+1),pos⟩
  cost _ _ := budget

/-- A linked round contract at each reachable state suffices for the
word-sized controller loop. -/
theorem stagedControllerRounds_linked
    {w entry vCap eCap h L P caller base count handle bound budget : ℕ}
    {p : Program} {E : Finset ℕ} {branches : ℕ → LSF}
    (H : MGraph) (ρ : ℝ) (query : (ℕ → ℝ) → ℕ → ℝ) (mem : ℕ → ℕ)
    (hw : 1 < 2^w) (hcount : count < 2^w) (hbound : bound < 2^w) :
    let Inv := stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem
    (∀ j < count, ∀ st, Inv j st → st.regs 2 = j →
      MeetsContract w p entry (stagedControllerRoundContract st (Inv (j+1)) j budget)) →
    Triple w p (fun st => Inv 0 st ∧ ∀ r, st.regs r < 2^w)
      (lastLevelRoundsBody entry publishedRoundArgs) (normalPost (Inv count))
      (fun _ => (argsSize publishedRoundArgs+budget+10)*count+7) := by
  intro Inv hstep
  apply stagedControllerRounds_words H ρ query mem hw hcount hbound
  intro j hj st hs hidx
  exact ⟨_,hstep j hj st hs hidx,⟨rfl,rfl⟩,le_rfl,fun _ _ pos hp => hp pos⟩

/-- The round contract's precondition supplies both read-only setup
premises of the published-round linking theorem. -/
theorem stagedControllerRoundContract_setup
    {w vCap eCap h L P caller base count handle bound guestL sim src j budget stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st : State) (Next : State → Prop)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem j st)
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hbase : src+queryWeights H guestL = base) (hw : 1 < 2^w)
    (hheap : queryHeap H guestL < 2^w) (hfit : bound+queryWeights H guestL < 2^w) :
    let C := stagedControllerRoundContract st Next j budget
    (∀ args input pos stop, C.pre args input →
      let entered := startState args input pos
      entered.regs 68 = stop+1 →
      entered.regs 0 = H.n ∧ entered.regs 1 = H.m ∧ entered.regs 2 = guestL ∧
      entered.regs 3 = sim ∧ entered.regs 69 = src ∧ 1 < 2^w ∧ queryHeap H guestL < 2^w ∧
      src+queryWeights H guestL ≤ stop+1 ∧ stop+1+queryWeights H guestL < 2^w) ∧
    (∀ args input pos, C.pre args input → ∃ stop weight,
      (startState args input pos).regs 68 = stop+1 ∧ input stop = weight ∧ stop+1 < 2^w) := by
  intro C
  constructor
  · rintro args input pos stop ⟨rfl,rfl⟩ entered hcursor
    obtain ⟨h0,h1,h2,h3,h69,h68,hsep,hroom⟩ :=
      stagedController_roundEntry st pos hs hn hm hguest hsim hsrc hbase hfit
    change entered.regs 68 = st.regs 0-1+1 at h68
    exact ⟨h0,h1,h2,h3,h69,hw,hheap,by omega,by omega⟩
  · rintro args input pos ⟨rfl,rfl⟩
    obtain ⟨stop,weight,hcursor,hread,hroom,_⟩ :=
      stagedController_roundDescriptor st pos hs (show bound < 2^w by omega)
    exact ⟨stop,weight,hcursor,hread,hroom⟩

/-- Link the installed published round at a reachable controller state.
Its premise is the numeric run and branch append on the
staged input. -/
theorem stagedControllerRound_link
    {w entry select dedup copy pack packWeights prepare adjacency numeric unit restore init scatter publish
      vCap eCap h L P caller base count handle bound guestL sim src j budget : ℕ}
    {p : Program} {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ}
    {query : (ℕ → ℝ) → ℕ → ℝ} {mem : ℕ → ℕ} (st : State) (Next : State → Prop)
    (hs : stagedRoundState H vCap eCap h L P caller base count handle bound E branches ρ query mem j st)
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim) (hsrc : st.regs 141 = src)
    (hbase : src+queryWeights H guestL = base) (hw : 1 < 2^w)
    (hheap : queryHeap H guestL < 2^w) (hfit : bound+queryWeights H guestL < 2^w)
    (he : p.procs[entry]? = some
      (stagedPublishedRoundBody select dedup copy pack packWeights prepare adjacency numeric
        unit restore init scatter publish))
    (hcopy : MeetsContract w p copy (copyWordsContract w)) :
    let C := stagedControllerRoundContract st Next j budget
    (∀ args mem pos ω, (∀ x ∈ args, x < 2^w) → C.pre args mem →
      ∀ staged, staged.regs 5 = st.regs 0 →
        staged.regs 8 = st.mem (st.regs 0-1) → staged.regs 31 = st.mem (st.regs 0-1) →
        (∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
          staged.regs r = (startState args mem pos).regs r) →
        (∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = mem (src+i)) →
        (∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a → staged.mem a = mem a) →
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
        cn+cl+cb+21+17*queryWeights H guestL+14+
          argsSize [.reg 69,.reg 5,
            (canonicalGuestArgsExpr (.reg 0) (.reg 1) (.reg 2) (.reg 3)).getD 5 (.const 0)]
          ≤ C.cost args mem) →
    MeetsContract w p entry C := by
  intro C hrun
  obtain ⟨hstage,hload⟩ :=
    stagedControllerRoundContract_setup (budget := budget) st Next hs hn hm hguest hsim hsrc
      hbase hw hheap hfit
  apply stagedPublishedRound_meetsContract he C H guestL sim src hcopy hstage hload
  intro args input pos ω hwords hpre staged inputWeights cursor hcursor hweight h5 h8 h31 hkeep hcopied hframe
  have hpre' := hpre
  change args = _ ∧ input = st.mem at hpre'
  obtain ⟨rfl,rfl⟩ := hpre'
  have hc := (publishedRoundArgs_startState st st.mem pos).2.2
  have heq : cursor = st.regs 0 := hcursor.symm.trans hc
  rw [heq] at h5 hweight hcopied hframe
  rw [← hweight] at h8 h31
  exact hrun _ _ pos ω hwords hpre staged h5 h8 h31 hkeep hcopied hframe

/-- Guest staging writes above the incoming cursor. The numeric pass
therefore reads the same model weights by compact edge index. -/
theorem stagedController_stagedWeights
    {vCap eCap h L P caller base count handle bound j stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st : State) (staged : State)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem j st)
    (hframe : ∀ a < st.regs 0, staged.mem a = st.mem a) :
    let src := st.mem (st.regs 0-1)
    src+(H.m-1)*stride+L ≤ st.regs 0 ∧
    ∀ i < H.m, Valid staged.mem (src+i*stride) h L ∧
      fixVal staged.mem (src+i*stride) h L P = weights P ρ query j (edgeName H i) := by
  intro src
  obtain ⟨_,_,_,_,_,_,_,_,hend,hweight⟩ := hs
  change src+(H.m-1)*stride+L ≤ st.regs 0-1 at hend
  refine ⟨by omega,?_⟩
  intro i hi
  obtain ⟨hv,he⟩ := hweight (edgeName H i) (edgeName_mem hi)
  rw [edgeIndex_name hi] at hv he
  change Valid st.mem (src+i*stride) h L at hv
  change fixVal st.mem (src+i*stride) h L P = _ at he
  have hmul := Nat.mul_le_mul_right stride (show i ≤ H.m-1 by omega)
  have hagree k (hk : k < L) : staged.mem (src+i*stride+k) = st.mem (src+i*stride+k) :=
    hframe _ (by omega)
  exact ⟨fun k hk => (hagree k hk).trans_lt (hv k hk),
    by simpa only [fixVal,intVal_congr hagree] using he⟩

/-- The copied guest prefix and the retained host blocks give the numeric
round both its indexed graph and its current model weights. -/
theorem stagedController_numericInput
    {vCap eCap h L P caller base count handle bound j src guestL stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged : State) (len : ℕ → ℤ)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem j st)
    (hcopy : ∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = st.mem (src+i))
    (hframe : ∀ a < st.regs 0, staged.mem a = st.mem a)
    (ht : ∀ i < H.m, st.mem (src+i) = (indexedGraph H).tail i)
    (hh : ∀ i < H.m, st.mem (src+(H.m+i)) = (indexedGraph H).head i)
    (hlen : ∀ i < H.m, ListAt st.mem (src+queryLengths H+i*guestL)
      (encodeLimbs 1 guestL (len (edgeName H i)))) :
    let cursor := st.regs 0
    let weight := st.mem (cursor-1)
    (∀ i < H.m, staged.mem (cursor+i) = (indexedGraph H).tail i) ∧
    (∀ i < H.m, staged.mem (cursor+(H.m+i)) = (indexedGraph H).head i) ∧
    (∀ i < H.m, ListAt staged.mem (cursor+queryLengths H+i*guestL)
      (encodeLimbs 1 guestL (len (edgeName H i)))) ∧
    weight+(H.m-1)*stride+L ≤ cursor ∧
    ∀ i < H.m, Valid staged.mem (weight+i*stride) h L ∧
      fixVal staged.mem (weight+i*stride) h L P = weights P ρ query j (edgeName H i) := by
  obtain ⟨ht',hh',hl'⟩ :=
    stagedGuestPrefix_arrays H guestL src (st.regs 0) len st.mem staged.mem hcopy ht hh hlen
  exact ⟨ht',hh',hl',stagedController_stagedWeights st staged hs hframe⟩

/-- The round invariant only refers to the initializer's memory below
the collection base, so either of two memories that agree below the
base can serve as the reference memory. -/
theorem stagedRoundStateAtStride_input_congr
    {H : MGraph} {vCap eCap h L P caller base count handle bound stride j : ℕ}
    {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem mem' : ℕ → ℕ} {st : State}
    (hframe : ∀ a < base, mem' a = mem a) :
    stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride
        E branches ρ query mem' j st ↔
      stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride
        E branches ρ query mem j st := by
  unfold stagedRoundStateAtStride
  constructor
  · rintro ⟨h1,h3,h151,hbase,hcursor,hzero,hmem,hcollection,hspan,hweights⟩
    exact ⟨h1,h3,h151,hbase,hcursor,hzero,
      fun a ha => (hmem a ha).trans (hframe a ha),hcollection,hspan,hweights⟩
  · rintro ⟨h1,h3,h151,hbase,hcursor,hzero,hmem,hcollection,hspan,hweights⟩
    exact ⟨h1,h3,h151,hbase,hcursor,hzero,
      fun a ha => (hmem a ha).trans (hframe a ha).symm,hcollection,hspan,hweights⟩

end MinCostFlow.LastLevelProgram
