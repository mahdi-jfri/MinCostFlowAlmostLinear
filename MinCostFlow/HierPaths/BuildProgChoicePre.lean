module

public import MinCostFlow.HierPaths.BuildProgChoiceGeom

/-!
# Preconditions for a round with certified choices

The stored graphs supply the core's input at each active index. The certified
sets and the disjoint intervals supply the router's input. Its matchings fit
the fixed graph slots independently of the chosen replies.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Uniform address and cost budgets for one running iteration. -/
structure ChoiceRoundBudget (w tailBudget : ℕ) (D : ChoiceLoopData) (heap : ℕ)
    (sts : ℕ → ChildState) : Prop where
  heapWord : heap < 2^w
  core : ∀ i < (D.round sts).jobs.count,
    heap + rangeCost (scanStepSpace D.base.coreSpace (D.round sts).jobs D.base.childSize) 0 i +
      D.base.coreSpace ((D.round sts).jobs.graph i).encode.length + 3*D.base.childSize < 2^w
  chosen : ∀ (answer : ℕ → CoreResult) (bump : ℕ → ℕ),
    (∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
      (D.round sts).q ((D.round sts).jobs.graph i) (answer i)) →
    (D.round sts).ValidBump answer bump →
    let B := (D.round sts).withReplies answer bump
    let A := D.atHeap heap
    B.routeReply A +
      (B.verts.card + 1) * routerSpaceUpTo B.routeSpace B.host.n B.host.encode.length
        (pairsWords B.pairs).length (B.Δ + B.L + max 2 B.verts.card) < 2^w ∧
    (∀ rBump, B.ValidRouteBump rBump → (B.withRouteBump rBump).record A + 2 + B.jobs.count < 2^w) ∧
    buildOneRoundTailCost w B ≤ tailBudget

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- All requests use valid terminal pairs, including an empty batch. -/
theorem ChoiceGameHyp.routerPre {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    (h : ChoiceGameHyp D β bh) {sts : ℕ → ChildState} {answer : ℕ → CoreResult} {bump : ℕ → ℕ}
    (hCert : ∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
      (D.round sts).q ((D.round sts).jobs.graph i) (answer i)) :
    let B := (D.round sts).withReplies answer bump
    RouterPre B.host B.verts B.pairs B.Δ B.L := by
  let B := (D.round sts).withReplies answer bump
  let s := D.base.childSize
  let ans := answerByChild D.count sts answer
  let cs := choiceRequesting s D.count D.offset sts ans
  let req := fun c => (choiceRequest s (D.offset c) (sts c) (ans c)).getD (∅,∅)
  have hPair : ValidTerminalPairs D.base.verts (cs.map req) := by
    refine validTerminalPairs_of_children (List.nodup_range.filter _)
      (fun c hc => (h.children.2.1 c (mem_choiceRequesting.mp hc).1).1)
      (fun a ha b hb hab => h.children.2.2 a (mem_choiceRequesting.mp ha).1 b
        (mem_choiceRequesting.mp hb).1 hab) ?_
    intro c hc
    obtain ⟨hck,ha,U,hU⟩ := mem_choiceRequesting.mp hc
    have hReq : choiceRequest s (D.offset c) (sts c) (ans c) = some
        (shiftSet (D.offset c) (bisectOf s U),shiftSet (D.offset c) (Finset.range s \ bisectOf s U)) :=
      by simp [choiceRequest,ha,hU]
    have hh := choiceRequest_props h.even (D.certify_children hCert c hck ha) hReq
    have h' : req c = (shiftSet (D.offset c) (bisectOf s U),
        shiftSet (D.offset c) (Finset.range s \ bisectOf s U)) := by simp [req,hReq]
    rw [h']
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.le⟩
  obtain ⟨ha,hb,hc,hd,he,hf⟩ := h.host
  refine ⟨ha,hb,hc,hd,he,hf,?_⟩
  change ValidTerminalPairs D.base.verts B.pairs
  rw [show B.pairs = ((D.round sts).withReplies answer).pairs from rfl, D.pairs_eq]
  exact hPair

/-- The router returns a match for every nonempty chosen batch, and the last
denominator fits the prescribed path bound. -/
theorem ChoiceGameHyp.matched {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    (h : ChoiceGameHyp D β bh) {sts : ℕ → ChildState} {answer : ℕ → CoreResult} {bump : ℕ → ℕ}
    (hCert : ∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
      (D.round sts).q ((D.round sts).jobs.graph i) (answer i))
    (hne : ((D.round sts).withReplies answer bump).indices.isEmpty = false) :
    let B := (D.round sts).withReplies answer bump
    ∃ Ms emb, B.result.1 = .matched Ms emb ∧
      RouteMatchedSpec B.host B.verts B.pairs B.Δ B.L B.result.2 0 Ms emb ∧
      (∀ i (hi : i < B.pairs.length), (Ms.getD i []).length = (B.pairs[i]'hi).1.card) ∧
      B.result.2 ≤ bh := by
  let B := (D.round sts).withReplies answer bump
  have hp : 1 ≤ B.pairs.length := by
    rw [show B.pairs.length = B.indices.length from length_batchJobPairs ..]
    exact List.length_pos_iff.mpr (fun he => (Bool.eq_false_iff.mp hne) (List.isEmpty_iff.mpr he))
  obtain ⟨_,hex⟩ := exists_lemma_1 h.router
  obtain ⟨⟨ms,em,he,hs,hN⟩,_,hBh,_,_⟩ :=
    hex B.host B.verts B.pairs B.Δ B.L (h.routerPre hCert) hp β h.positive h.expansion
  have hLast : (B.result.2:ℝ) ≤ (bh:ℝ) := hBh.trans h.denominator
  exact ⟨ms,em,he,hs,hN,by exact_mod_cast hLast⟩

private theorem chosenCorePrefixBound {D : ChoiceLoopData} {sts : ℕ → ChildState}
    {answer : ℕ → CoreResult} {bump : ℕ → ℕ}
    (hBump : (D.round sts).ValidBump answer bump)
    (heap : ℕ) :
    let B := (D.round sts).withReplies answer bump
    ∀ i ≤ B.jobs.count,
      B.jobs.prepPrefix B.core B.q heap i ≤
        heap + rangeCost (scanStepSpace B.coreSpace B.jobs B.childSize) 0 i := by
  let B := (D.round sts).withReplies answer bump
  change ∀ i ≤ B.jobs.count, B.jobs.prepPrefix B.core B.q heap i ≤ _
  intro i hi
  induction i with
  | zero => simp [BuildGameJobs.prepPrefix, rangeCost]
  | succ i ih =>
    have hj : i < B.jobs.count := Nat.lt_of_succ_le hi
    have hPrev := ih hj.le
    have hAns : B.jobs.answer B.core B.q i = answer i := rfl
    have hn : (B.jobs.graph i).n = B.childSize := rfl
    have hStep : preparedChildEnd 0 B.childSize (answer i) + bump i ≤
        scanStepSpace B.coreSpace B.jobs B.childSize i := hBump i hj
    have hRange : rangeCost (scanStepSpace B.coreSpace B.jobs B.childSize) 0 (i + 1) =
        rangeCost (scanStepSpace B.coreSpace B.jobs B.childSize) 0 i +
          scanStepSpace B.coreSpace B.jobs B.childSize i := by
      unfold rangeCost
      rw [Nat.sub_zero, Nat.sub_zero, List.range'_concat]
      simp
    have hPrep : preparedChildEnd (B.jobs.prepPrefix B.core B.q heap i) B.childSize (answer i) =
        B.jobs.prepPrefix B.core B.q heap i + preparedChildEnd 0 B.childSize (answer i) := by
      cases answer i <;> simp only [preparedChildEnd] <;> omega
    change B.jobs.prepPrefix B.core B.q heap (i+1) ≤
      heap + rangeCost (scanStepSpace B.coreSpace B.jobs B.childSize) 0 (i+1)
    rw [hRange]
    simp only [BuildGameJobs.prepPrefix, BuildGameJobs.bumpSize, hAns, hn]
    change preparedChildEnd (B.jobs.prepPrefix B.core B.q heap i) B.childSize (answer i) + bump i ≤ _
    rw [hPrep]
    dsimp only [B] at hStep hPrev ⊢
    omega

/-- The slot bound equals the graph encoding length after the append,
with the fixed child address added. -/
theorem applyBatch_cap_eq {B : BuildRoundData} {Ms : List (List (ℕ × ℕ))}
    {emb : ℕ → List ℕ} (i : ℕ) :
    let A := B.applyData Ms emb
    A.cap i = A.addr i + (appendGameMatching (A.graph i) (A.offset i) (Ms.getD i [])).encode.length := by
  let A := B.applyData Ms emb
  change A.cap i = _
  rw [buildGraph_encode_length]
  have he : (appendGameMatching (A.graph i) (A.offset i) (Ms.getD i [])).m =
      (A.graph i).m + (A.row i).count := by
    simp [appendGameMatching,Graph.m,ApplyBatchData.row,matchingWalkRow,A,BuildRoundData.applyData]
  rw [he]
  simp [ApplyBatchData.cap,Nat.add_assoc,A]

/-- Applying a row keeps the child's new graph within its reservation. -/
theorem ChoiceGameHyp.matchedCap {D : ChoiceLoopData} {β : ℝ} {bh w t heap i : ℕ}
    {initial mem : ℕ → ℕ} {sts : ℕ → ChildState} {answer : ℕ → CoreResult} {bump : ℕ → ℕ}
    (h : ChoiceGameHyp D β bh) (hTrace : ChoiceLoopTrace w D initial t heap sts mem)
    (ht : t < D.limit)
    (hCert : ∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
      (D.round sts).q ((D.round sts).jobs.graph i) (answer i))
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hne : ((D.round sts).withReplies answer bump).indices.isEmpty = false)
    (hRes : ((D.round sts).withReplies answer bump).result.1 = .matched Ms emb) (hi : i < Ms.length) :
    let B := (D.round sts).withReplies answer bump
    let A := B.applyData Ms emb
    A.cap i ≤ A.addr i + D.geometry.slotWords := by
  let B := (D.round sts).withReplies answer bump
  let A := B.applyData Ms emb
  let c := D.active sts (A.child i)
  have hRows := D.matchedRows hCert h.router h.host h.positive h.expansion h.denominator h.children h.even hne hRes
  obtain ⟨hc,_,hg⟩ := hRows.2 i hi
  let wk := fun j => erase B.host.edges ((matchingWalkRow Ms emb i).u j) ((matchingWalkRow Ms emb i).raw j)
  have hGraph := D.graph_of_row (answer := answer) (emb := emb) wk hg
  have hRun : CertifiedGame D.base.route D.base.host D.base.verts D.base.M D.base.r D.base.Δ D.base.L
      D.base.childSize D.count D.offset (t+1) (D.next sts answer) :=
    CertifiedGame.step hTrace.certified _ (D.certify_children hCert)
  obtain ⟨hInv,_⟩ := hRun.invariant h.router h.host h.positive h.expansion h.denominator
    h.children h.even (coreLevel_le h.coreSize)
  have hEnc := (gameGraph_bounds_of_inv (hInv c hc)).2.2.1
  have hLength : (gameGraph D.base.childSize (D.next sts answer c)).encode.length ≤ D.geometry.slotWords :=
    hEnc.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by
      change t+1 ≤ D.limit+1
      omega)) _)
  change A.cap i ≤ A.addr i + D.geometry.slotWords
  have he : A.cap i = A.addr i + (appendGameMatching (A.graph i) (A.offset i) (Ms.getD i [])).encode.length :=
    applyBatch_cap_eq i
  rw [he]
  have hh : appendGameMatching (A.graph i) (A.offset i) (Ms.getD i []) =
      gameGraph D.base.childSize (D.next sts answer c) := hGraph
  rw [hh]
  exact Nat.add_le_add_left hLength _

private theorem choiceRoundFit {w tailBudget t heap : ℕ} {D : ChoiceLoopData} {β : ℝ}
    {bh : ℕ} {sts : ℕ → ChildState} {initial mem : ℕ → ℕ}
    (h : ChoiceGameHyp D β bh) (hL : GameFixedLayout w D.geometry)
    (hM : ChoiceGameMemory D heap sts mem) (ht : t < D.limit)
    (hTrace : ChoiceLoopTrace w D initial t heap sts mem)
    (hRoom : ChoiceRoundBudget w tailBudget D heap sts)
    {ans : ℕ → CoreResult} {bump : ℕ → ℕ} {rBump : ℕ}
    (hCert : ∀ i < (D.round sts).jobs.count, CoreOutcomeSpec ParamConfig.default D.base.M
      (D.round sts).q ((D.round sts).jobs.graph i) (ans i))
    (hBump : (D.round sts).ValidBump ans bump)
    (hRBump : ((D.round sts).withReplies ans bump).ValidRouteBump rBump) :
    BuildRoundFit w ((D.round sts).withReplies ans bump rBump) (D.atHeap heap) mem := by
  let B := (D.round sts).withReplies ans bump rBump
  let A := D.atHeap heap
  have hn : B.jobs.count ≤ D.count := D.active_le sts
  have hO := hL.offsets
  have hG := hL.graphs
  have hD := hL.directory
  have hS := hL.saved
  have hHeap : A.replies + B.jobs.count + 1 ≤ A.heap := by
    have hr := hL.replies
    have hm := hM.heap
    change D.addrs.replies + D.count + 1 ≤ D.addrs.heap at hr
    change D.addrs.replies + B.jobs.count + 1 ≤ heap
    omega
  have hBits : 1 < 2^w := by have := hL.bits; omega
  obtain ⟨hRt,hRecordAll,_⟩ := hRoom.chosen ans bump hCert hBump
  have hRecord : B.record A + 2 + B.jobs.count < 2^w := hRecordAll rBump hRBump
  have hHost : A.host + B.host.encode.length ≤ A.replies := by
    have hh := hL.host
    change D.addrs.host + D.base.host.encode.length ≤ D.directory at hh
    change D.directory + D.limit ≤ D.saved at hD
    change D.saved + D.count ≤ D.addrs.graphs at hS
    change D.addrs.graphs + D.count ≤ D.addrs.offsets at hG
    change D.addrs.offsets + D.count ≤ D.addrs.replies at hO
    change D.addrs.host + D.base.host.encode.length ≤ D.addrs.replies
    omega
  have hVerts : A.verts + (finsetWords B.verts).length ≤ A.replies := by
    have hh := hL.verts
    change D.addrs.verts + (finsetWords D.base.verts).length ≤ D.directory at hh
    change D.directory + D.limit ≤ D.saved at hD
    change D.saved + D.count ≤ D.addrs.graphs at hS
    change D.addrs.graphs + D.count ≤ D.addrs.offsets at hG
    change D.addrs.offsets + D.count ≤ D.addrs.replies at hO
    change D.addrs.verts + (finsetWords D.base.verts).length ≤ D.addrs.replies
    omega
  have hGO : A.graphs + B.jobs.count ≤ A.offsets := (Nat.add_le_add_left hn _).trans hG
  have hOO : A.offsets + B.jobs.count ≤ A.replies := (Nat.add_le_add_left hn _).trans hO
  have hGOL : A.graphs + B.jobs.count ≤ A.replies := hGO.trans (Nat.le_of_add_right_le hOO)
  refine ⟨?_,hM.host,h.valid,hM.verts,hHost,hVerts,h.routerPre hCert,hL.bits,hRt,?_,
    fun _ _ => rfl,?_,?_,?_,?_⟩
  · refine ⟨A.graphs,A.offsets,A.heap,A.replies,rfl,hGOL,hOO,hHeap,hBits,hRoom.heapWord,
      coreLevel_le h.coreSize,hM.zero,hM.graphs,hM.offsets,?_⟩
    intro i hi
    have hp := chosenCorePrefixBound hBump heap i hi.le
    have hW := hRoom.core i hi
    refine ⟨h.jobFacts hL hM ht hTrace hi,?_⟩
    change B.jobs.prepPrefix B.core B.q heap i + B.coreSpace (B.jobs.graph i).encode.length +
      3*B.childSize < 2^w
    exact (Nat.add_le_add_right (Nat.add_le_add_right hp _) _).trans_lt hW
  · change 2*(D.base.childSize/2) = D.base.childSize
    have he := h.even
    omega
  · intro i hi U he
    have hh := hCert i hi
    change ans i = .cut U at he
    rw [he] at hh
    exact hh.1
  · intro i hi
    have hs := (hL.slots _ (D.active_mem hi).1).1
    have hb : A.offsets + B.jobs.count ≤ B.jobs.addr i := (Nat.add_le_add_left hn _).trans hs
    exact ⟨hGO.trans (Nat.le_of_add_right_le hb),hb⟩
  · intro hne
    obtain ⟨Ms,emb,_,_,_,hb⟩ := h.matched hCert hne
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)).trans h.path
  · intro Ms emb hne he
    let Q := B.applyData Ms emb
    obtain ⟨hRows,hChild⟩ :=
      D.matchedRows hCert h.router h.host h.positive h.expansion h.denominator h.children h.even hne he
    have hC (i : ℕ) (hi : i < Ms.length) : D.active sts (Q.child i) < D.count := (hChild i hi).1
    have hCap (i : ℕ) (hi : i < Ms.length) : Q.cap i ≤ Q.addr i+D.geometry.slotWords :=
      h.matchedCap hTrace ht hCert hne he hi
    refine ⟨⟨?_,?_,?_,?_⟩,?_,?_⟩
    · intro i hi
      have hSlot := (hL.slots _ (hC i hi)).1
      have hHost := hL.host
      have hLen := buildGraph_encode_length D.base.host
      change D.addrs.host + D.base.host.encode.length ≤ D.directory at hHost
      change D.directory+D.limit ≤ D.saved at hD
      change D.saved+D.count ≤ D.addrs.graphs at hS
      change D.addrs.graphs+D.count ≤ D.addrs.offsets at hG
      change D.addrs.offsets+D.count ≤ D.childAddr (D.active sts (Q.child i)) at hSlot
      change D.addrs.host+2+2*D.base.host.m ≤ D.childAddr (D.active sts (Q.child i))
      omega
    · intro i hi
      exact (hCap i hi).trans (hL.slots _ (hC i hi)).2
    · intro i hi j hj hij
      have hN : B.indices.Nodup := List.nodup_range.filter _
      have hIdx (i : ℕ) (hi : i < Ms.length) : Q.child i < B.jobs.count := by
        have h' : i < B.indices.length := hRows ▸ hi
        have hM : Q.child i ∈ B.indices := by
          change B.indices.getD i 0 ∈ B.indices
          rw [List.getD_eq_getElem _ _ h']
          exact List.getElem_mem h'
        exact (mem_batchJobIndices.mp hM).1
      have hcNe : D.active sts (Q.child i) ≠ D.active sts (Q.child j) := by
        intro hEq
        have he' := D.active_inj sts (hIdx i hi) (hIdx j hj) hEq
        change B.indices.getD i 0 = B.indices.getD j 0 at he'
        rw [List.getD_eq_getElem _ _ (hRows ▸ hi),List.getD_eq_getElem _ _ (hRows ▸ hj)] at he'
        exact hij ((hN.getElem_inj_iff).mp he')
      obtain hh | hh := hL.slotsApart _ (hC i hi) _ (hC j hj) hcNe
      · exact Or.inl ((hCap i hi).trans hh)
      · exact Or.inr ((hCap j hj).trans hh)
    · intro i hi
      exact (Nat.le_add_right _ _).trans_lt (hL.offsetWords _ (hC i hi))
    · intro i hi e he'
      have ht' : e ∈ Ms[i] := by
        rwa [List.getD_eq_getElem _ _ hi] at he'
      obtain ⟨h₁,h₂⟩ := (hChild i hi).2.1 e ht'
      have hs₁ := mem_shiftSet_iff.mp h₁
      have hs₂ := mem_shiftSet_iff.mp h₂
      have hW : D.offset (D.active sts (Q.child i)) + D.base.childSize < 2^w :=
        hL.offsetWords _ (hC i hi)
      have hL₁ := hs₁.1
      have hL₂ := hs₂.1
      have hU₁ := Finset.mem_range.mp hs₁.2
      have hU₂ := Finset.mem_range.mp hs₂.2
      change D.offset (D.active sts (Q.child i)) ≤ e.1 at hL₁
      change D.offset (D.active sts (Q.child i)) ≤ e.2 at hL₂
      change e.1 - D.offset (D.active sts (Q.child i)) < D.base.childSize at hU₁
      change e.2 - D.offset (D.active sts (Q.child i)) < D.base.childSize at hU₂
      change D.offset (D.active sts (Q.child i)) ≤ e.1 ∧
        D.offset (D.active sts (Q.child i)) ≤ e.2 ∧ e.1 < 2^w ∧ e.2 < 2^w
      omega
    · change B.record A + 2 + B.jobs.count < 2^w at hRecord
      have hh : B.record A = Q.cursor (B.routedEnd A + 4 + Ms.flatten.length + B.pathBound + 1+B.host.n)
          Ms.length := by
        change B.result.1 = .matched Ms emb at he
        change B.indices.isEmpty = false at hne
        simp only [BuildRoundData.record,hne,Bool.false_eq_true,ite_false,he]
        rfl
      rw [hh] at hRecord
      change Q.cursor (B.routedEnd A + 4 + Ms.flatten.length + B.pathBound + 1+B.host.n) Ms.length < 2^w
      omega

/-- A certified history, the stored graph invariant, and the arena budgets give
the precondition of the actual game step. -/
theorem choiceStep_pre_of_memory {w tailBudget t heap : ℕ} {D : ChoiceLoopData} {β : ℝ}
    {bh : ℕ} {sts : ℕ → ChildState} {initial mem : ℕ → ℕ}
    (h : ChoiceGameHyp D β bh) (hL : GameFixedLayout w D.geometry)
    (hM : ChoiceGameMemory D heap sts mem) (ht : t < D.limit)
    (hTrace : ChoiceLoopTrace w D initial t heap sts mem)
    (hRoom : ChoiceRoundBudget w tailBudget D heap sts)
    (hn : 0 < (D.round sts).jobs.count) :
    let B := D.round sts
    let A := D.atHeap heap
    (buildStepChoiceContract w tailBudget B A D.first D.saved (D.active sts)).pre
      (B.stepArgs A D.first D.saved) mem := by
  let B := D.round sts
  let A := D.atHeap heap
  have hGeom := choiceLoop_stepLayout hL hM.heap hn
  have hGO := hGeom.graphsBelow
  have hOO := hGeom.offsetsBelow
  have hR := hGeom.tableBelow
  refine ⟨rfl,⟨rfl,?_,?_⟩,hGeom,?_⟩
  · refine ⟨A.graphs,A.offsets,A.heap,A.replies,rfl,hGO.trans (Nat.le_of_add_right_le hOO),hOO,hR,
      by have := hL.bits; omega,hRoom.heapWord,coreLevel_le h.coreSize,h.rankLe,hM.zero,hM.graphs,hM.offsets,?_⟩
    intro i hi
    exact ⟨h.jobFacts hL hM ht hTrace hi,rfl,hRoom.core i hi⟩
  · intro ans bump hCert hBump
    exact ⟨fun rBump hRB => choiceRoundFit h hL hM ht hTrace hRoom hCert hBump hRB,
      (hRoom.chosen ans bump hCert hBump).2.2⟩
  · intro ans bump rBump hCert hBump hRB
    exact (hRoom.chosen ans bump hCert hBump).2.1 rBump hRB

end MinCostFlow.HierPaths
