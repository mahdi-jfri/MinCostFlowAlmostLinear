module

public import MinCostFlow.HierPaths.BuildProgGameSchedule

/-!
# Player inputs along the scheduled game

The child-game invariant gives valid graphs for the core. The disjoint
child intervals give disjoint router requests. By the round bound every
child has a saved set when the loop reaches its limit.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The combinatorial hypotheses of the child game at one parent. -/
structure BuildGamePlayerBounds (S : BuildGameSchedule) (cfg : ParamConfig)
    (β : ℝ) (bh : ℕ) : Prop where
  router : IsMatchingPlayer S.base.route S.base.routeCost
  core : IsCorePlayer cfg S.base.M S.base.r S.base.core S.base.coreCost
  host : HostPre S.base.host S.base.verts S.base.Δ S.base.L
  positive : 0 < β
  expansion : S.base.host.IsExpansionExpanderOn S.base.verts β
  bh : max 2 (2 / β) ≤ (bh : ℝ)
  children : IsChildren S.base.verts (fun c => shiftSet (S.offset c)
    (Finset.range S.base.childSize)) S.count S.base.childSize
  even : S.base.childSize % 2 = 0
  coreSize : S.base.childSize ≤ (NOf S.base.M S.base.r) ^ S.base.r
  coreDegree : 49 * S.L' ≤ deltaParam S.base.M
  sizeLog : S.base.childSize < 2 ^ S.L'

/-- Each active table entry names a child without a saved set. -/
theorem BuildGameSchedule.child_active {S : BuildGameSchedule} {t i : ℕ}
    (hi : i < (S.round t).jobs.count) :
    S.child t i < S.count ∧ (S.states t (S.child t i)).saved = none := by
  let l := activeChildren S.count (S.states t)
  have hi' : i < l.length := hi
  have hm : S.child t i ∈ l := by
    change l.getD i 0 ∈ l
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem _
  simpa [l,activeChildren] using hm

/-- The schedule stops by the round bound of Lemma 3. -/
theorem BuildGamePlayerBounds.saved {S : BuildGameSchedule} {cfg : ParamConfig} {β : ℝ} {bh : ℕ}
    (h : BuildGamePlayerBounds S cfg β bh) :
    ∀ c < S.count, ∃ C, (S.states S.data.limit c).saved = some C :=
  gameRun_saved h.router h.host h.positive h.expansion h.bh h.core h.children
    h.even h.coreSize h.coreDegree h.sizeLog

/-- A core call in a scheduled round receives a valid instance and returns
a set with the promised meaning. -/
theorem BuildGamePlayerBounds.coreOutcome {S : BuildGameSchedule} {cfg : ParamConfig} {β : ℝ} {bh : ℕ}
    (h : BuildGamePlayerBounds S cfg β bh) {t i : ℕ} (ht : t < S.data.limit)
    (hi : i < (S.round t).jobs.count) :
    let B := S.round t
    CoreOutcomeSpec cfg B.M B.r (B.jobs.graph i) (B.jobs.answer B.core B.q i) := by
  have ht' : t ≤ 49 * S.L' := by change t < 49*S.L'+1 at ht; omega
  obtain ⟨hinv,_⟩ := gameRun_inv h.router h.host h.positive h.expansion h.bh h.core h.children
    h.even h.coreSize h.coreDegree t (by omega)
  exact coreSpec_of_inv h.core h.coreSize h.coreDegree ht' (hinv _ (S.child_active hi).1)

/-- For every round, the terminal pair family meets the router's input conditions. -/
theorem BuildGamePlayerBounds.routerPre {S : BuildGameSchedule} {cfg : ParamConfig} {β : ℝ} {bh : ℕ}
    (h : BuildGamePlayerBounds S cfg β bh) {t : ℕ} (ht : t < S.data.limit) :
    let B := S.round t
    RouterPre B.host B.verts B.pairs B.Δ B.L := by
  let s := S.base.childSize
  let core := S.base.core
  let M := S.base.M
  let r := S.base.r
  let sts := S.states t
  let cs := requesting core M r s S.count S.offset sts
  let req := fun c => (request core M r s (S.offset c) (sts c)).getD (∅,∅)
  have ht' : t ≤ 49 * S.L' := by change t < 49*S.L'+1 at ht; omega
  obtain ⟨hinv,_⟩ := gameRun_inv h.router h.host h.positive h.expansion h.bh h.core h.children
    h.even h.coreSize h.coreDegree t (by omega)
  obtain ⟨hnd,hmem⟩ := requesting_spec core M r s S.count S.offset sts
  have hValid : ValidTerminalPairs S.base.verts (cs.map req) := by
    refine validTerminalPairs_of_children hnd
      (fun c hc => (h.children.2.1 c ((hmem c).mp hc).1).1)
      (fun a ha b hb hab => h.children.2.2 a ((hmem a).mp ha).1 b ((hmem b).mp hb).1 hab) ?_
    intro c hc
    obtain ⟨hck,hsome⟩ := (hmem c).mp hc
    obtain ⟨pair,hReq⟩ := Option.isSome_iff_exists.mp hsome
    have he : req c = pair := by simp [req,hReq]
    rw [he]
    exact request_props h.core h.even h.coreSize h.coreDegree ht' (hinv c hck) hReq
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := h.host
  refine ⟨h₁,h₂,h₃,h₄,h₅,h₆,?_⟩
  change ValidTerminalPairs S.base.verts
    (batchJobPairs (modelGameJobs s S.count S.offset S.childAddr sts) core (coreLevel M r s) s)
  rw [modelGameJobs_pairs]
  exact hValid

/-- A nonempty application batch has one matching row per cut index. -/
theorem BuildGamePlayerBounds.rows {S : BuildGameSchedule} {cfg : ParamConfig} {β : ℝ} {bh : ℕ}
    (h : BuildGamePlayerBounds S cfg β bh) {t : ℕ} (ht : t < S.data.limit)
    (hne : (S.round t).indices ≠ []) {Ms emb} (hm : (S.round t).result.1 = .matched Ms emb) :
    Ms.length = (S.round t).indices.length := by
  let B := S.round t
  have hl : B.pairs.length = B.indices.length := length_batchJobPairs ..
  have hp : 1 ≤ B.pairs.length := by
    rw [hl]
    exact List.length_pos_iff.mpr hne
  obtain ⟨_,hex⟩ := exists_lemma_1 h.router
  obtain ⟨⟨ms,em,he,hs,_⟩,_⟩ := hex B.host B.verts B.pairs B.Δ B.L
    (h.routerPre ht) hp β h.positive h.expansion
  change B.result.1 = .matched ms em at he
  change B.result.1 = .matched Ms emb at hm
  rw [hm] at he
  cases he
  exact hs.1.trans hl

end MinCostFlow.HierPaths
