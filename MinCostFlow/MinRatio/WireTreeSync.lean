module

public import MinCostFlow.MinRatio.WireTreeSyncBase
public import MinCostFlow.MinRatio.PathSlotBind
public import MinCostFlow.MinRatio.TreeEditEndpoints
public import MinCostFlow.Num.IsNegative
import MinCostFlow.LinkCut.PathProg.Implements
import WordRAM.Tactic

/-!
# Shared path-tree synchronization: program, invariant, and step wrapper (`WireTreeSync`)

Defines `wireTreeSyncLoop` (applying a packed `TreeEditDifference oldF.E newF.E edits` to the
solver's Section 6 link-cut path tree and edge tables), its static context `WireSyncCtx`, loop
invariant `WireSyncInv`, and the common decode/wrap helper `wireSync_step_wrap`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program

/-! ### Machine program and space/cost bounds -/

/-- Deletion branch of one tree-sync iteration. -/
@[expose] def wireTreeSyncDelete (readTree cutTree canonCopy isNeg : ℕ) : Stmt :=
  .assign 17 (.reg 3) ;;
  .assign 15 (.load (.bin .add (.reg 19) (.reg 8))) ;;
  .call 3 readTree [.reg 0, .reg 15, .reg 17] ;;
  .assign 14 (.bin .add (.reg 3) (.bin .add (.const 2) (.bin .mul (.const 4) (.reg 2)))) ;;
  .assign 15 (.bin .add (.reg 14) (.bin .add (.const 2) (.bin .mul (.const 4) (.reg 2)))) ;;
  .call 3 canonCopy [.reg 17, .reg 14, .reg 2, .reg 15] ;;
  .store (.bin .add (.reg 22) (.reg 8)) (.reg 14) ;;
  .store (.bin .add (.reg 19) (.reg 8)) (.const 0) ;;
  .call 3 cutTree [.reg 0, .reg 12, .reg 13, .reg 3] ;;
  .call 15 isNeg [.bin .add (.bin .add (.reg 14) (.const 2)) (.bin .mul (.const 3) (.reg 2)),
    .reg 2] ;;
  .cond (.reg 15) .nop
    (.cond (.load (.bin .add (.reg 26) (.reg 8))) .nop
      (.store (.bin .add (.reg 26) (.reg 8)) (.const 1) ;;
       .assign 16 (.load (.bin .add (.reg 1) (.const 11))) ;;
       .store (.bin .add (.reg 25) (.reg 16)) (.reg 8) ;;
       .store (.bin .add (.reg 1) (.const 11)) (.bin .add (.reg 16) (.const 1))))

/-- Insertion branch of one tree-sync iteration. -/
@[expose] def wireTreeSyncInsert (linkTree bind : ℕ) : Stmt :=
  .assign 17 (.reg 3) ;;
  .assign 14 (.load (.bin .add (.reg 22) (.reg 8))) ;;
  .call 3 linkTree [.reg 0, .reg 12, .reg 13, .reg 14, .reg 17] ;;
  .assign 15 (.load (.reg 17)) ;;
  .call 3 bind [.reg 19, .reg 20, .reg 8, .reg 15, .reg 3] ;;
  .store (.bin .add (.reg 24) (.reg 15)) (.load (.bin .add (.reg 23) (.reg 8)))

/-- One iteration of the packed tree-sync loop: decode `[tag, e]` at `reg 6`, resolve root-graph
endpoints into `reg 12, 13`, dispatch delete or insert, and advance `reg 6` and `reg 18`. -/
@[expose] def wireTreeSyncStep (readTree cutTree linkTree bind canonCopy isNeg : ℕ) : Stmt :=
  .assign 7 (.load (.reg 6)) ;;
  .assign 8 (.load (.bin .add (.reg 6) (.const 1))) ;;
  .assign 12 (.bin .add (.load (.bin .add (.reg 11) (.load (.bin .add (.reg 9) (.reg 8))))) (.const 1)) ;;
  .assign 13 (.bin .add (.load (.bin .add (.reg 11) (.load (.bin .add (.reg 10) (.reg 8))))) (.const 1)) ;;
  .cond (.reg 7)
    (wireTreeSyncInsert linkTree bind)
    (wireTreeSyncDelete readTree cutTree canonCopy isNeg) ;;
  .assign 6 (.bin .add (.reg 6) (.const 2)) ;;
  .assign 18 (.bin .sub (.reg 18) (.const 1))

/-- Loop applying all `reg 18` packed tree edits starting at `reg 6`. -/
@[expose] def wireTreeSyncLoop (readTree cutTree linkTree bind canonCopy isNeg : ℕ) : Stmt :=
  .loop (.reg 18) (wireTreeSyncStep readTree cutTree linkTree bind canonCopy isNeg)

theorem wireTreeSyncLoop_noRand (readTree cutTree linkTree bind canonCopy isNeg : ℕ) :
    (wireTreeSyncLoop readTree cutTree linkTree bind canonCopy isNeg).NoRand := by
  simp [wireTreeSyncLoop, wireTreeSyncStep, wireTreeSyncDelete, wireTreeSyncInsert, Stmt.NoRand]

/-- Worst-case heap words consumed per tree edit in `wireTreeSyncLoop`. -/
@[expose] def wireTreeSyncEditSpace (L : ℕ) : ℕ :=
  40 * LinkCut.PathProg.treeLimbs L + 10 * L + 210

/-- Worst-case amortized cost (including potential increase `drainUnit` on off-ready push)
per tree edit in `wireTreeSyncLoop`. -/
@[expose] def wireTreeSyncEditCost (L drainUnit : ℕ) : ℕ :=
  50 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) + 160 * L + drainUnit + 500

/-! ### Shared helper lemmas -/

theorem wire_fits_of_two_mul_abs_lt {h L : ℕ} {x : ℤ} (hx : 2 * |x| < (Num.capacity h L : ℤ)) :
    Num.Fits h L x := by
  have h1 : |2 * x| < (Num.capacity h L : ℤ) := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℤ) ≤ 2)]; exact hx
  rw [abs_lt] at h1
  exact ⟨by omega, h1.2⟩

theorem offReadyInv_push {mem : ℕ → ℕ} {cnt offReadyList inOffReady intCap e : ℕ}
    (hoff : OffReadyInv mem cnt offReadyList inOffReady intCap)
    (heCap : e < intCap) (he0 : mem (inOffReady + e) = 0)
    (hdisj : ∀ j < intCap, ∀ k < intCap, offReadyList + j ≠ inOffReady + k) :
    cnt < intCap ∧
    OffReadyInv
      (Function.update (Function.update mem (inOffReady + e) 1) (offReadyList + cnt) e)
      (cnt + 1) offReadyList inOffReady intCap := by
  obtain ⟨hcntLe, hmemL, hdist, hbits, hrev⟩ := hoff
  have hcntLt : cnt < intCap := by
    have hinj : Set.InjOn (fun j => mem (offReadyList + j)) (Finset.range cnt : Set ℕ) := by
      intro a ha b hb hab
      by_contra hne
      exact hdist a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb) hne hab
    have hsub : (Finset.range cnt).image (fun j => mem (offReadyList + j)) ⊆
        (Finset.range intCap).erase e := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hj' := Finset.mem_range.mp hj
      refine Finset.mem_erase.mpr ⟨fun hEq => ?_, Finset.mem_range.mpr (hmemL j hj').1⟩
      have h1 := (hmemL j hj').2; rw [hEq, he0] at h1; omega
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj, Finset.card_range,
      Finset.card_erase_of_mem (Finset.mem_range.mpr heCap), Finset.card_range] at hcard
    omega
  let m' := Function.update (Function.update mem (inOffReady + e) 1) (offReadyList + cnt) e
  have hm'_in (k : ℕ) (hk : k < intCap) :
      m' (inOffReady + k) = if k = e then 1 else mem (inOffReady + k) := by
    dsimp only [m']
    rw [Function.update_of_ne (Ne.symm (hdisj cnt hcntLt k hk))]
    by_cases hke : k = e
    · subst hke; simp
    · rw [Function.update_of_ne (by omega), ite_eq_right hke]
  have hm'_list (j : ℕ) (hj : j < cnt + 1) :
      m' (offReadyList + j) = if j = cnt then e else mem (offReadyList + j) := by
    dsimp only [m']
    by_cases hjc : j = cnt
    · subst hjc; simp
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (hdisj j (by omega) e heCap),
        ite_eq_right hjc]
  change cnt < intCap ∧ OffReadyInv m' (cnt + 1) offReadyList inOffReady intCap
  refine ⟨hcntLt, by omega, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hm'_list j hj]
    split_ifs with hjc
    · exact ⟨heCap, by rw [hm'_in e heCap, ite_eq_left rfl]⟩
    · have hlt := (hmemL j (by omega)).1
      refine ⟨hlt, ?_⟩; rw [hm'_in _ hlt]; split_ifs
      · rfl
      · exact (hmemL j (by omega)).2
  · intro j₁ hj₁ j₂ hj₂ hne
    rw [hm'_list j₁ hj₁, hm'_list j₂ hj₂]
    split_ifs with h1 h2
    · exact (hne (h1.trans h2.symm)).elim
    · intro hEq; have h1' := (hmemL j₂ (by omega)).2; rw [← hEq, he0] at h1'; omega
    · intro hEq; have h2' := (hmemL j₁ (by omega)).2; rw [hEq, he0] at h2'; omega
    · exact hdist j₁ (by omega) j₂ (by omega) hne
  · intro k hk
    rw [hm'_in k hk]; split_ifs
    · exact Or.inr rfl
    · exact hbits k hk
  · intro k hk h1
    rw [hm'_in k hk] at h1
    split_ifs at h1 with hke
    · subst hke; exact ⟨cnt, by omega, by rw [hm'_list cnt (by omega), ite_eq_left rfl]⟩
    · obtain ⟨j, hj, hje⟩ := hrev k hk h1
      exact ⟨j, by omega, by rw [hm'_list j (by omega), ite_eq_right (by omega)]; exact hje⟩

theorem pathTreeBudget_le_of_log {L n : ℕ} (hlog : Nat.log 2 (2 * n + 1) ≤ 4 * L) :
    pathTreeBudget LinkCut.PathProg.pathC L n ≤
      25 * (LinkCut.PathProg.pathC * (L + 1) ^ 2) * (4 * L + 1) := by
  unfold pathTreeBudget
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1)

theorem namedSlots_congr_slot {s : PathTreeState} {trees : List AuxTree} {G : MGraph}
    {slot₁ slot₂ name₁ name₂ : ℕ → ℕ}
    (h : TreeEditNamedSlots s trees G slot₁ name₁)
    (hs : ∀ e ∈ G.E, slot₂ e = slot₁ e)
    (hn : ∀ sl ∈ trees.flatMap AuxTree.toList, isEdgeSlot s.n sl → name₂ sl = name₁ sl) :
    TreeEditNamedSlots s trees G slot₂ name₂ := by
  refine ⟨fun e he => ?_, fun sl hsl his => ?_, fun e he => ?_⟩
  · obtain ⟨hact, his, hnm⟩ := h.forward e he
    rw [hs e he]; exact ⟨hact, his, (hn _ hact his).trans hnm⟩
  · rw [hn sl hsl his]
    obtain ⟨heG, hse⟩ := h.inverse sl hsl his
    exact ⟨heG, (hs _ heG).trans hse⟩
  · rw [hs e he]; exact h.endpoints e he

theorem liveAccounts_congr_slot {s : PathTreeState} {trees : List AuxTree} {G : MGraph}
    {slot₁ slot₂ : ℕ → ℕ} {acc : ℕ → PathEdgeValue}
    (h : TreeEditLiveAccounts s trees G slot₁ acc) (hs : ∀ e ∈ G.E, slot₂ e = slot₁ e) :
    TreeEditLiveAccounts s trees G slot₂ acc := fun e he => by
  rw [hs e he]; exact h e he

/-! ### Static context and loop invariant -/

/-- Static premises shared across all iterations of `wireTreeSyncLoop`. -/
structure WireSyncCtx (w L drainUnit : ℕ) (cfg : Alg2Config)
    (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T))
    (p : Program) (fmt : Num.Format w)
    (initTree : ℕ) (opTree : ℕ → ℕ) (bind canonCopy isNeg : ℕ)
    (root editPtr heap0 : ℕ) (memStart : ℕ → ℕ)
    (G0 oldF newF : MGraph) (edits : List TreeChange)
    (tok : SolverToken cfg L Rcore) (canonVal : ℕ → PathEdgeValue) (B R : ℤ) : Prop where
  fmtBits : fmt.limbBits = 4
  treeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
    (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L))
  bindOk : MeetsContract w p bind (pathSlotBindContract w)
  canonOk : ∀ v, MeetsContract w p canonCopy (wireCanonCopyContract w v)
  isNegOk : MeetsContract w p isNeg (Num.isNegativeContract w 4)
  diff : TreeEditDifference oldF.E newF.E edits
  editsAt : TreeEditsAt memStart editPtr edits
  editsEnd : editPtr + 2 * edits.length ≤ heap0
  editsTag0 : ∀ a, editPtr ≤ a → a < editPtr + 2 * edits.length → tok.tag a = 0 ∧ a ≠ root + 11
  rootGraph : DynGraphAt memStart tok.rootGraph G0.n tok.rootECap G0
  oldSub : oldF.E ⊆ G0.E
  newSub : newF.E ⊆ G0.E
  newForest : newF.IsForest
  oldEnds : ∀ f ∈ oldF.E, G0.tail f = oldF.tail f ∧ G0.head f = oldF.head f
  newEnds : ∀ f ∈ newF.E, G0.tail f = newF.tail f ∧ G0.head f = newF.head f
  capE : ∀ ei ∈ G0.E, ei < tok.intCap
  vtxE : ∀ ei ∈ G0.E, G0.tail ei < G0.n ∧ G0.head ei < G0.n
  canonProp : ∀ ei ∈ G0.E, (canonVal ei).forward = true ∧
    |(canonVal ei).gradient| ≤ B ∧ |(canonVal ei).length| ≤ B ∧
    |(canonVal ei).flow| ≤ B ∧ |(canonVal ei).detector| ≤ B
  tags : (∀ a, tok.tag a ≠ 0 → a < heap0) ∧
    (∀ j < 16, tok.tag (root + j) = 1) ∧
    (∀ j < tok.intCap, tok.tag (tok.slots + j) = 9) ∧
    (∀ j < 2 * G0.n, tok.tag (tok.names + j) = 10) ∧
    (∀ j < 2 * G0.n, tok.tag (tok.slotThresholds + j) = 11) ∧
    (∀ j < tok.intCap, tok.tag (tok.edgeThresholds + j) = 12) ∧
    (∀ j < tok.intCap, tok.tag (tok.edgeRecords + j) = 13) ∧
    (∀ j < tok.intCap, tok.tag (tok.offReadyList + j) = 14) ∧
    (∀ j < tok.intCap, tok.tag (tok.inOffReady + j) = 15) ∧
    (∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a →
      tok.tag a = 16) ∧
    (∀ ei ∈ G0.E, ei ∉ oldF.E → ∀ j < 2 + 4 * L, tok.tag (memStart (tok.edgeRecords + ei) + j) = 18) ∧
    (∀ a, tok.rootGraph ≤ a → a < tok.rootGraph + dynGraphSize G0.n tok.rootECap → tok.tag a = 20)
  treeHeapLt : tok.treeHeap < 2 ^ w
  nW : 2 * G0.n + 1 < 2 ^ w
  logW : Nat.log 2 (2 * G0.n + 1) ≤ 4 * L
  capT : 2 * ((2 * G0.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ)
  hw11 : 11 < 2 ^ w
  room : heap0 + edits.length * wireTreeSyncEditSpace L < 2 ^ w

/-- State invariant of `wireTreeSyncLoop` after applying `done` edits with `rem` remaining. -/
@[expose] def WireSyncInv {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (root editPtr heap0 : ℕ) (memStart : ℕ → ℕ)
    (G0 oldF _newF : MGraph) (edits : List TreeChange)
    (tok : SolverToken cfg L Rcore) (canonVal : ℕ → PathEdgeValue) (B R : ℤ)
    (done rem : List TreeChange)
    (curTree : PathTreeState)
    (curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ)
    (curHeap curOffCnt : ℕ) (st : State) : Prop :=
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let curE := applyTreeChanges oldF.E done
  done ++ rem = edits ∧
  st.regs 0 = tok.treeHeap ∧ st.regs 1 = root ∧ st.regs 2 = L ∧
  st.regs 3 = curHeap ∧ st.regs 6 = editPtr + 2 * done.length ∧
  st.regs 18 = rem.length ∧
  st.regs 9 = dgETailSlotBase tok.rootGraph G0.n tok.rootECap ∧
  st.regs 10 = dgEHeadSlotBase tok.rootGraph G0.n tok.rootECap ∧
  st.regs 11 = dgIntToExtBase tok.rootGraph G0.n ∧
  st.regs 19 = tok.slots ∧ st.regs 20 = tok.names ∧ st.regs 22 = tok.edgeRecords ∧
  st.regs 23 = tok.edgeThresholds ∧ st.regs 24 = tok.slotThresholds ∧
  st.regs 25 = tok.offReadyList ∧ st.regs 26 = tok.inOffReady ∧
  heap0 ≤ curHeap ∧ curHeap ≤ heap0 + done.length * wireTreeSyncEditSpace L ∧
  ZeroFrom st.mem curHeap ∧
  (∀ a, Rtree.foot tok.treeHeap curTreeTok a →
    Rtree.foot tok.treeHeap tok.treeTok a ∨ (heap0 ≤ a ∧ a < curHeap)) ∧
  (∀ a < heap0, a ≠ root + 11 → tok.tag a ≠ 9 → tok.tag a ≠ 10 → tok.tag a ≠ 11 →
    tok.tag a ≠ 13 → tok.tag a ≠ 14 → tok.tag a ≠ 15 → tok.tag a ≠ 16 →
    st.mem a = memStart a) ∧
  curTree.n = G0.n ∧
  (∃ curTrees curFree curDepth,
    LctInvWith pathPayload curTree curTrees curFree curDepth ∧
    PathTreeNumericInv curTree curTrees B R ∧
    TreeEditNamedSlots curTree curTrees { G0 with E := curE }
      (fun ei => st.mem (tok.slots + ei)) (fun sl => st.mem (tok.names + sl)) ∧
    TreeEditLiveAccounts curTree curTrees { G0 with E := curE }
      (fun ei => st.mem (tok.slots + ei)) canonVal) ∧
  Rtree.rep tok.treeHeap curTree curTreeTok st.mem ∧
  (∀ ei ∈ curE, st.mem (tok.slotThresholds + st.mem (tok.slots + ei)) =
    st.mem (tok.edgeThresholds + ei)) ∧
  (∀ ei ∈ G0.E, ei ∉ curE → st.mem (tok.slots + ei) = 0) ∧
  (∀ ei ∈ G0.E, ei ∉ curE →
    PathEdgeAt st.mem (st.mem (tok.edgeRecords + ei)) 4 L (some (canonVal ei))) ∧
  (∀ ei ∈ G0.E, ei ∉ curE → 0 ≤ (canonVal ei).detector →
    st.mem (tok.inOffReady + ei) = 1) ∧
  (∀ ei ∈ G0.E, ei ∉ curE →
    (ei ∈ oldF.E →
      heap0 ≤ st.mem (tok.edgeRecords + ei) ∧
      st.mem (tok.edgeRecords + ei) + (2 + 4 * L) ≤ curHeap ∧
      ∀ a, st.mem (tok.edgeRecords + ei) ≤ a →
        a < st.mem (tok.edgeRecords + ei) + (2 + 4 * L) →
        ¬ Rtree.foot tok.treeHeap curTreeTok a) ∧
    (ei ∉ oldF.E → st.mem (tok.edgeRecords + ei) = memStart (tok.edgeRecords + ei))) ∧
  (∀ e₁ ∈ G0.E, ∀ e₂ ∈ G0.E, e₁ ≠ e₂ → e₁ ∉ curE → e₂ ∉ curE →
    st.mem (tok.edgeRecords + e₁) + (2 + 4 * L) ≤ st.mem (tok.edgeRecords + e₂) ∨
    st.mem (tok.edgeRecords + e₂) + (2 + 4 * L) ≤ st.mem (tok.edgeRecords + e₁)) ∧
  st.mem (root + 11) = curOffCnt ∧
  OffReadyInv st.mem curOffCnt tok.offReadyList tok.inOffReady tok.intCap

/-! ### Prefix/suffix helpers -/

theorem wireSync_curE_sub_G0 {G0 oldF newF : MGraph} {edits done rem : List TreeChange}
    (hdiff : TreeEditDifference oldF.E newF.E edits) (happ : done ++ rem = edits)
    (holdSub : oldF.E ⊆ G0.E) (hnewSub : newF.E ⊆ G0.E) :
    applyTreeChanges oldF.E done ⊆ G0.E := by
  intro f hf
  by_cases hfo : f ∈ oldF.E
  · exact holdSub hfo
  · have haux : ∀ (ds : List TreeChange) (E : Finset ℕ),
        f ∈ applyTreeChanges E ds → f ∈ E ∨ TreeChange.insert f ∈ ds := by
      intro ds; induction ds with
      | nil => intro E h; exact Or.inl h
      | cons d tl ih =>
        intro E h; cases d with
        | delete x =>
          rcases ih _ h with h' | h'
          · exact Or.inl (Finset.mem_erase.mp h').2
          · exact Or.inr (List.mem_cons_of_mem _ h')
        | insert x =>
          rcases ih _ h with h' | h'
          · rcases Finset.mem_insert.mp h' with rfl | h''
            · exact Or.inr List.mem_cons_self
            · exact Or.inl h''
          · exact Or.inr (List.mem_cons_of_mem _ h')
    rcases haux done oldF.E hf with h' | hins
    · exact (hfo h').elim
    · exact hnewSub (Finset.mem_sdiff.mp
        (hdiff.insert_mem_sdiff (happ ▸ List.mem_append_left _ hins))).1

theorem wireSync_step_wrap {w L drainUnit : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {p : Program} {ω : ℕ → Bool} {fmt : Num.Format w}
    {initTree : ℕ} {opTree : ℕ → ℕ} {bind canonCopy isNeg : ℕ}
    {root editPtr heap0 : ℕ} {memStart : ℕ → ℕ}
    {G0 oldF newF : MGraph} {edits done rem : List TreeChange} {ch : TreeChange}
    {tok : SolverToken cfg L Rcore} {canonVal : ℕ → PathEdgeValue} {B R : ℤ}
    {curTree : PathTreeState}
    {curTreeTok : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {curHeap curOffCnt tagVal e : ℕ} {st mid : State} {cBranch : ℕ}
    (ctx : WireSyncCtx w L drainUnit cfg Rcore p fmt initTree opTree bind canonCopy isNeg
      root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R)
    (hinv : WireSyncInv root editPtr heap0 memStart G0 oldF newF edits tok canonVal B R
      done (ch :: rem) curTree curTreeTok curHeap curOffCnt st)
    (htw : treeEditWords ch = [tagVal, e]) (heG : e ∈ G0.E)
    (hbr :
      let s1 := { st with regs := Function.update st.regs 7 tagVal }
      let s2 := { s1 with regs := Function.update s1.regs 8 e }
      let s3 := { s2 with regs := Function.update s2.regs 12 (G0.tail e + 1) }
      let s4 := { s3 with regs := Function.update s3.regs 13 (G0.head e + 1) }
      Runs w p ω (if tagVal = 0 then wireTreeSyncDelete (opTree 4) (opTree 1) canonCopy isNeg
        else wireTreeSyncInsert (opTree 0) bind) s4 .normal mid cBranch)
    (h6m : mid.regs 6 = editPtr + 2 * done.length) (h18m : mid.regs 18 = rem.length + 1) :
    let out := { mid with regs := Function.update (Function.update mid.regs 6
      (editPtr + 2 * (done.length + 1))) 18 rem.length }
    Runs w p ω (wireTreeSyncStep (opTree 4) (opTree 1) (opTree 0) bind canonCopy isNeg)
      st .normal out (cBranch + 44) := by
  obtain ⟨happ, _, _, _, _, hr6, _, hr9, hr10, hr11, _, _, _, _, _, _, _, _, _, _, _, hFrame, _⟩ := hinv
  have hlenEq : done.length + (rem.length + 1) = edits.length := by
    have := congrArg List.length happ; simp at this; omega
  have hw1 : 1 < 2 ^ w := by have := ctx.hw11; omega
  have hw2 : 2 < 2 ^ w := by have := ctx.hw11; omega
  have htagLt {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap0 := ctx.tags.1 a (ht ▸ hv)
  have hwordsCur : ListAt st.mem (editPtr + 2 * done.length) [tagVal, e] := by
    have hsplit : edits.flatMap treeEditWords =
        done.flatMap treeEditWords ++ treeEditWords ch ++ rem.flatMap treeEditWords := by
      rw [← happ, List.flatMap_append, List.flatMap_cons, List.append_assoc]
    have hat := ctx.editsAt; rw [TreeEditsAt, hsplit] at hat
    have h2 := (listAt_append.mp (listAt_append.mp hat).1).2
    rw [treeEditWords_length, htw] at h2
    refine h2.congr fun a ha1 ha2 => ?_
    have hEd := ctx.editsTag0 a (by omega) (by simp at ha2; omega)
    exact hFrame a (by have := ctx.editsEnd; simp at ha2; omega) hEd.2
      (by rw [hEd.1]; decide) (by rw [hEd.1]; decide) (by rw [hEd.1]; decide)
      (by rw [hEd.1]; decide) (by rw [hEd.1]; decide) (by rw [hEd.1]; decide) (by rw [hEd.1]; decide)
  have hDG : DynGraphAt st.mem tok.rootGraph G0.n tok.rootECap G0 :=
    ctx.rootGraph.of_agree fun a ha1 ha2 => by
      have ht20 := ctx.tags.2.2.2.2.2.2.2.2.2.2.2 a ha1 ha2
      have hneR : a ≠ root + 11 := fun he => by rw [he, ctx.tags.2.1 11 (by omega)] at ht20; omega
      exact hFrame a (htagLt ht20 (by decide)) hneR (by rw [ht20]; decide)
        (by rw [ht20]; decide) (by rw [ht20]; decide) (by rw [ht20]; decide)
        (by rw [ht20]; decide) (by rw [ht20]; decide) (by rw [ht20]; decide)
  have hDGroom : tok.rootGraph + dynGraphSize G0.n tok.rootECap ≤ 2 ^ w := by
    have hsz : 0 < dynGraphSize G0.n tok.rootECap := by unfold dynGraphSize; omega
    have hlast := htagLt (ctx.tags.2.2.2.2.2.2.2.2.2.2.2
      (tok.rootGraph + dynGraphSize G0.n tok.rootECap - 1) (by omega) (by omega)) (by decide)
    have := ctx.room; omega
  have ht0 : st.mem (editPtr + 2 * done.length) = tagVal := by simpa using hwordsCur 0 (by simp)
  have he1 : st.mem (editPtr + 2 * done.length + 1) = e := hwordsCur 1 (by simp)
  have haddr1 : editPtr + 2 * done.length + 1 < 2 ^ w := by have := ctx.editsEnd; have := ctx.room; omega
  have hEp := TreeEditEndpointAt.of_graph hDG heG
  have htailSlotW : dgETailSlotBase tok.rootGraph G0.n tok.rootECap + e < 2 ^ w := by
    simp only [dgETailSlotBase, dynGraphSize] at hDGroom ⊢; have := hEp.edgeBound; omega
  have hheadSlotW : dgEHeadSlotBase tok.rootGraph G0.n tok.rootECap + e < 2 ^ w := by
    simp only [dgEHeadSlotBase, dynGraphSize] at hDGroom ⊢; have := hEp.edgeBound; omega
  have htailInvW : dgIntToExtBase tok.rootGraph G0.n +
      st.mem (dgETailSlotBase tok.rootGraph G0.n tok.rootECap + e) < 2 ^ w := by
    simp only [dgIntToExtBase, dynGraphSize] at hDGroom ⊢; have := hEp.tailSlotBound; omega
  have hheadInvW : dgIntToExtBase tok.rootGraph G0.n +
      st.mem (dgEHeadSlotBase tok.rootGraph G0.n tok.rootECap + e) < 2 ^ w := by
    simp only [dgIntToExtBase, dynGraphSize] at hDGroom ⊢; have := hEp.headSlotBound; omega
  have hu1W : G0.tail e + 1 < 2 ^ w := by have := (ctx.vtxE e heG).1; have := ctx.nW; omega
  have hv1W : G0.head e + 1 < 2 ^ w := by have := (ctx.vtxE e heG).2; have := ctx.nW; omega
  let s1 := { st with regs := Function.update st.regs 7 tagVal }
  let s2 := { s1 with regs := Function.update s1.regs 8 e }
  let s3 := { s2 with regs := Function.update s2.regs 12 (G0.tail e + 1) }
  let s4 := { s3 with regs := Function.update s3.regs 13 (G0.head e + 1) }
  have r1 : Runs w p ω (.assign 7 (.load (.reg 6))) st .normal s1 3 :=
    runs_assign_iff.mpr ⟨tagVal, by simp [Expr.eval, hr6, ht0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 6) (.const 1)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨e, by simp [Expr.eval, BinOp.eval, s1, hr6, hw1, haddr1, he1], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 12 (.bin .add (.load (.bin .add (.reg 11)
      (.load (.bin .add (.reg 9) (.reg 8))))) (.const 1))) s2 .normal s3 10 :=
    runs_assign_iff.mpr ⟨G0.tail e + 1, by
      simp [Expr.eval, BinOp.eval, s2, s1, hr9, hr11, htailSlotW, htailInvW, hEp.tailName, hw1, hu1W],
      rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 13 (.bin .add (.load (.bin .add (.reg 11)
      (.load (.bin .add (.reg 10) (.reg 8))))) (.const 1))) s3 .normal s4 10 :=
    runs_assign_iff.mpr ⟨G0.head e + 1, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, hr10, hr11, hheadSlotW, hheadInvW, hEp.headName, hw1, hv1W],
      rfl, rfl, rfl⟩
  have rCond : Runs w p ω (.cond (.reg 7) (wireTreeSyncInsert (opTree 0) bind)
      (wireTreeSyncDelete (opTree 4) (opTree 1) canonCopy isNeg)) s4 .normal mid (cBranch + 2) :=
    runs_cond_iff.mpr ⟨tagVal, cBranch, by simp [Expr.eval, s4, s3, s2, s1], hbr, by simp [Expr.size]; omega⟩
  let mid1 := { mid with regs := Function.update mid.regs 6 (editPtr + 2 * (done.length + 1)) }
  let out := { mid with regs := Function.update (Function.update mid.regs 6
    (editPtr + 2 * (done.length + 1))) 18 rem.length }
  have h6W : editPtr + 2 * (done.length + 1) < 2 ^ w := by have := ctx.editsEnd; have := ctx.room; omega
  have h18W : rem.length < 2 ^ w := by have := ctx.editsEnd; have := ctx.room; omega
  have rA : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 2))) mid .normal mid1 4 :=
    runs_assign_iff.mpr ⟨editPtr + 2 * (done.length + 1), by
      simp [Expr.eval, BinOp.eval, h6m, hw2, show editPtr + 2 * done.length + 2 =
        editPtr + 2 * (done.length + 1) by omega, h6W], rfl, rfl, rfl⟩
  have rB : Runs w p ω (.assign 18 (.bin .sub (.reg 18) (.const 1))) mid1 .normal out 4 :=
    runs_assign_iff.mpr ⟨rem.length, by simp [Expr.eval, BinOp.eval, mid1, h18m, hw1, h18W], rfl, rfl, rfl⟩
  unfold wireTreeSyncStep
  exact runs_seq_iff.mpr (Or.inr ⟨s1, 3, cBranch + 40, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 5, cBranch + 34, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 10, cBranch + 23, r3,
        runs_seq_iff.mpr (Or.inr ⟨s4, 10, cBranch + 12, r4,
          runs_seq_iff.mpr (Or.inr ⟨mid, cBranch + 2, 9, rCond,
            runs_seq_iff.mpr (Or.inr ⟨mid1, 4, 4, rA, rB, rfl⟩), by omega⟩), by omega⟩),
        by omega⟩), by omega⟩), by omega⟩)

end MinCostFlow.MinRatio
