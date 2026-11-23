module

public import MinCostFlow.Spanner.ProgTask2InitJ0Proof
public import MinCostFlow.Spanner.ProgTask2RoundMath
public import MinCostFlow.Spanner.ProgWordRAMPot

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Bridge from `t2InitJ0_triple` to `initEmb0`, `vcongNumPure`, and `T2StepInv` -/

/-- Dynamic embedding table invariant at `embWJAddr` with walk heap `[arenaLo, arenaPtr)`. -/
def EmbInv (mem : ℕ → ℕ) (embWJAddr mW arenaLo arenaPtr : ℕ) (emb : ℕ → Option Walk) : Prop :=
  ∀ eW < mW,
    match emb eW with
    | some P => arenaLo ≤ mem (embWJAddr + eW) ∧
        mem (embWJAddr + eW) + P.encode.length ≤ arenaPtr ∧
        WalkAt mem (mem (embWJAddr + eW)) P
    | none => mem (embWJAddr + eW) = 0

lemma t2_embInv_of_initJ0 {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ mem : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {arena0 : ℕ}
    (hEmb : InitJ0EmbUpTo mem inp.embWJAddr arena0 ctx.wd.j0Edges.length ctx.wd.W.m inp.J
      ctx.wd.j0Edges) :
    EmbInv mem inp.embWJAddr ctx.wd.W.m arena0 (arena0 + 5 * ctx.wd.j0Edges.length)
      (initEmb0 ctx.wInp) := by
  intro eW heW
  have heq_J : ctx.wInp.prep.J = inp.J := ctx.hWInpJ
  have heq_j0 : ctx.wInp.prep.j0Edges = ctx.wd.j0Edges := rfl
  by_cases hlt : eW < ctx.wd.j0Edges.length
  · have hlt' : eW < ctx.wInp.prep.j0Edges.length := hlt
    have h1 := (hEmb eW heW).1 hlt
    have hlen : (t2J0Walk inp.J (ctx.wd.j0Edges.getD eW 0)).encode.length = 5 := by
      simp [walk_encode_length, t2J0Walk]
    have hwalk_eq : initEmb0 ctx.wInp eW = some (t2J0Walk inp.J (ctx.wd.j0Edges.getD eW 0)) := by
      simp only [initEmb0, t2J0Walk, heq_J, heq_j0, hlt, ↓reduceIte]
    rw [hwalk_eq]
    dsimp only
    rw [h1.1, hlen]
    refine ⟨Nat.le_add_right _ _, by omega, ?_⟩
    simpa [h1.1] using h1.2
  · have hge : ctx.wd.j0Edges.length ≤ eW := Nat.le_of_not_lt hlt
    have hnone : initEmb0 ctx.wInp eW = none := by
      simp only [initEmb0, heq_j0, hlt, ↓reduceIte]
    rw [hnone]
    exact (hEmb eW heW).2 hge

lemma j0VcongUpTo_eq_vcongNumPure {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (wWNum : ℕ → ℕ) :
    ∀ x, j0VcongUpTo ctx.wd wWNum inp.embJH ctx.wd.j0Edges.length x =
      vcongNumPure ctx.wd inp.J inp.embJH wWNum (initEmb0 ctx.wInp) x := by
  intro x
  have hj0_le : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by
    rw [ctx.hw_okW.W_m_eq]; exact Nat.le_add_right _ _
  have hembJHW := ctx.hembJHW
  unfold vcongNumPure j0VcongUpTo
  rw [← Finset.sum_range_add_sum_Ico _ hj0_le]
  have htail : ∑ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      (if x ∈ (compose inp.J inp.embJH (partialToWalk (initEmb0 ctx.wInp)) eW).verts
       then wWNum eW else 0) = 0 := by
    refine Finset.sum_eq_zero fun eW heW => ?_
    have hge : ctx.wInp.prep.j0Edges.length ≤ eW := (Finset.mem_Ico.mp heW).1
    have hnone : initEmb0 ctx.wInp eW = none := by simp [initEmb0, not_lt.mpr hge]
    have hpw : partialToWalk (initEmb0 ctx.wInp) eW = Walk.empty := by simp [partialToWalk, hnone]
    simp [compose, hpw, composeAux, Walk.empty]
  rw [htail, add_zero]
  refine Finset.sum_congr rfl fun eW heW => ?_
  have hj0 : eW < ctx.wInp.prep.j0Edges.length := Finset.mem_range.mp heW
  have hj0_eq : ctx.wd.j0Edges = ctx.wInp.prep.j0Edges := rfl
  have he_nl : ctx.wd.j0Edges.getD eW 0 < inp.J.m ∧
      (inp.J.edges.getD (ctx.wd.j0Edges.getD eW 0) (0, 0)).1 ≠
        (inp.J.edges.getD (ctx.wd.j0Edges.getD eW 0) (0, 0)).2 := by
    have h0 := mkW_j0_nonloop ctx.hstat hj0
    simpa only [ctx.hWInpJ, hj0_eq] using h0
  have he_lt : (inp.J.edges.getD (ctx.wd.j0Edges.getD eW 0) (0, 0)).2 < inp.J.n := by
    have hm : ctx.wd.j0Edges.getD eW 0 < inp.J.edges.length := he_nl.1
    rw [List.getD_eq_getElem _ _ hm]
    exact (ctx.hJ _ (List.getElem_mem hm)).2
  have he_eq : partialToWalk (initEmb0 ctx.wInp) eW =
      { verts := [(inp.J.edges.getD (ctx.wd.j0Edges.getD eW 0) (0, 0)).1,
                  (inp.J.edges.getD (ctx.wd.j0Edges.getD eW 0) (0, 0)).2],
        edges := [ctx.wd.j0Edges.getD eW 0] } := by
    simp only [partialToWalk, initEmb0, hj0, ↓reduceIte, ctx.hWInpJ, hj0_eq]; rfl
  have hmem_iff := compose_nonloop_mem_verts_iff ctx.hembJH
    [(inp.J.edges.getD (ctx.wd.j0Edges.getD eW 0) (0, 0)).1,
     (inp.J.edges.getD (ctx.wd.j0Edges.getD eW 0) (0, 0)).2]
    [ctx.wd.j0Edges.getD eW 0] (by simp)
    (fun _ h => by simp only [List.mem_singleton] at h; rw [h]; exact he_nl)
    (fun i hi => by
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0; left; simp)
    rfl rfl he_lt x
  have he_verts : x ∈ (compose inp.J inp.embJH (partialToWalk (initEmb0 ctx.wInp)) eW).verts ↔
      x ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts := by
    change x ∈ (composeAux inp.J inp.embJH (partialToWalk (initEmb0 ctx.wInp) eW).verts
      (partialToWalk (initEmb0 ctx.wInp) eW).edges).verts ↔ _
    rw [he_eq]
    simpa using hmem_iff
  simp only [he_verts]

private lemma composeAux_congr {J₁ J₂ : Graph} {emb₁ emb₂ : ℕ → Walk}
    (hJe : J₁.edges = J₂.edges) :
    ∀ (vs es : List ℕ), (∀ e ∈ es, emb₁ e = emb₂ e) →
      composeAux J₁ emb₁ vs es = composeAux J₂ emb₂ vs es
  | vs, [], _ => by cases vs with
    | nil => rfl
    | cons _ vs' => cases vs' <;> simp [composeAux]
  | [], _ :: _, _ => rfl
  | [_], _ :: _, _ => rfl
  | _ :: v :: vs, e :: es, he => by
    have he1 := he e List.mem_cons_self
    have ih := composeAux_congr hJe (v :: vs) es fun e' he' => he e' (List.mem_cons_of_mem e he')
    simp only [composeAux, hJe, he1, ih]

lemma t2InitJ0_to_pure_inv {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ mem : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) {arena0 : ℕ}
    (_hStat : ctx.StaticOutAt mem₀)
    (hVc : ∀ x < inp.H'.n,
      mem (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        j0VcongUpTo ctx.wd (fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i))
          inp.embJH ctx.wd.j0Edges.length x)
    (hEmb : InitJ0EmbUpTo mem inp.embWJAddr arena0 ctx.wd.j0Edges.length ctx.wd.W.m inp.J
      ctx.wd.j0Edges) :
    let wWNum := fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i)
    let emb0 := initEmb0 ctx.wInp
    IsPartialEmbedding ctx.wd.W inp.J emb0 ∧
    (∀ eW < ctx.wd.j0Edges.length, (emb0 eW).isSome = true) ∧
    (∀ eW < ctx.wd.W.m, ((partialToWalk emb0 eW).edges.length : ℝ) ≤ ctx.wd.γ_ExpPath) ∧
    (∀ x < inp.H'.n,
      mem (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        vcongNumPure ctx.wd inp.J inp.embJH wWNum emb0 x ∧
      vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk emb0)) x ≤
        ((0 : ℝ) + 1 / 2) * ctx.wd.τ₁) ∧
    volWRemPure ctx.wd emb0 ≤ ctx.wd.c_deg * (inp.J.m : ℝ) ∧
    (unembeddedSetPure ctx.wd emb0).card = ctx.wd.W.m - ctx.wd.j0Edges.length ∧
    EmbInv mem inp.embWJAddr ctx.wd.W.m arena0 (arena0 + 5 * ctx.wd.j0Edges.length) emb0 := by
  intro wWNum emb0
  have hpure := t2Init_pure_inv ctx.hstat ctx.hw_okW ctx.hws ctx.hembJHW
  have hcomp_eq : ∀ eW < ctx.wd.W.m, compose inp.J inp.embJH (partialToWalk emb0) eW =
      compose ctx.wInp.prep.J ctx.wInp.embJH (partialToWalk emb0) eW := by
    intro eW heW
    unfold compose
    refine composeAux_congr (congrArg Graph.edges ctx.hWInpJ.symm) _ _ fun e he => ?_
    cases h0 : emb0 eW with
    | none => simp [partialToWalk, h0, Walk.empty] at he
    | some P =>
      have hw := (ctx.hWInpJ ▸ hpure.1).2 eW heW P h0
      rw [partialToWalk, h0] at he
      have hm : e < inp.J.m := hw.2.2.elim (fun h => by simp [h.2.1] at he) (fun h => h.2.2.2.2.1 e he)
      exact (ctx.hWInpEmb e hm).symm
  refine ⟨ctx.hWInpJ ▸ hpure.1, hpure.2.1, hpure.2.2.1, fun x hx => ?_, ?_, ?_,
    t2_embInv_of_initJ0 ctx hEmb⟩
  · refine ⟨?_, ?_⟩
    · rw [hVc x hx]; exact j0VcongUpTo_eq_vcongNumPure ctx wWNum x
    · have hv := hpure.2.2.2 x (ctx.hWInpH'.symm ▸ hx)
      have hvcong_eq : vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk emb0)) x =
          vcongAt ctx.wd.W ctx.wd.wW (compose ctx.wInp.prep.J ctx.wInp.embJH (partialToWalk emb0)) x := by
        unfold vcongAt
        rw [Finset.sum_filter, Finset.sum_filter]
        refine Finset.sum_congr rfl fun eW heW => ?_
        rw [hcomp_eq eW (Finset.mem_range.mp heW)]
      rw [hvcong_eq]
      exact hv
  · exact ctx.hWInpJ ▸ volWRemPure_init_le ctx.hstat ctx.hw_okW ctx.hws emb0 hpure.2.1
  · have hj0_le : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by
      rw [ctx.hw_okW.W_m_eq]; exact Nat.le_add_right _ _
    have hset : unembeddedSetPure ctx.wd emb0 =
        Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m := by
      ext eW
      simp only [unembeddedSetPure, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
        Option.isNone_iff_eq_none]
      constructor
      · intro ⟨hm, hn⟩
        refine ⟨?_, hm⟩
        by_contra hlt
        have hs := hpure.2.1 eW (lt_of_not_ge hlt)
        rw [Option.isSome_iff_ne_none] at hs; exact hs hn
      · intro ⟨hge, hm⟩
        have hge' : ¬ eW < ctx.wInp.prep.j0Edges.length := Nat.not_lt.mpr hge
        exact ⟨hm, by simp [emb0, initEmb0, hge']⟩
    rw [hset, Nat.card_Ico]

/-! ## Task 2 ghost state, round potential, and Word-RAM invariant `T2StepInv` -/

/-- Ghost state tracked across rounds and steps of `task2Body`. -/
structure T2Ghost (pds : PathDSImpl) where
  η₁ : ℕ
  emb : ℕ → Option Walk
  emb_prev : ℕ → Option Walk
  states : ℕ → PathDSAbsState
  reps : ℕ → pds.R.τ
  drained : Finset ℕ
  procVerts : Finset ℕ
  queue : List ℕ
  initCountJ : ℕ
  initEdgesJ : ℕ
  getPathCountJ : ℕ
  deleteCountJ : ℕ
  prevDelCountJ : ℕ
  vcongUpdates : ℕ
  innerIters1 : ℕ
  arenaPtr : ℕ
  queryId : ℕ
  hCur : ℕ

/-- Fixed static data allocated in `[inp.v1 + 32, dsBaseAddr)` before round 1. -/
structure T2StaticData {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) where
  nodesEnd : ℕ
  L_inc : ℕ → List (ℕ × ℕ)
  hNodes_lo : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ≤ nodesEnd
  hNodes_hi : nodesEnd ≤ inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length + 3 * inp.embVertSum
  hL_sum : ∑ x ∈ Finset.range inp.H'.n, (L_inc x).length ≤ inp.embVertSum

noncomputable abbrev T2StaticData.dsBaseAddr {impl : SpannerToolImpl} {inp : Task2Input}
    {mem₀ : ℕ → ℕ} {w : ℕ} {ctx : T2Ctx impl inp mem₀ w} (stc : T2StaticData ctx) : ℕ :=
  stc.nodesEnd + ctx.wd.W.m * (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5)

lemma T2StaticData.dsBaseAddr_le_cap {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {ctx : T2Ctx impl inp mem₀ w} (stc : T2StaticData ctx) :
    stc.dsBaseAddr ≤ Task2Input.staticEndCap impl inp := by
  have hmW : ctx.wd.W.m ≤ Task1Input.mwCap impl inp.J := ctx.hmW_le
  have hK : ctx.wd.comps.length ≤ inp.J.m := ctx.hK_le
  have hγ : ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params ≤
      Task2Input.gammaExpCap impl inp.J := by
    have hcaps := ctx.hWInpJ ▸ task2_scalars_le_caps ctx.hstat ctx.hφ_lb
    exact hcaps.1
  have hn_mono : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ≤
      inp.nodesAddr (Task1Input.mwCap impl inp.J) inp.J.m := by
    unfold Task2Input.nodesAddr Task2Input.queueAddr Task2Input.eWVertStampAddr
      Task2Input.procStampAddr Task2Input.vcongNumAddr Task2Input.vHeadAddr
      Task2Input.vhatStampAddr Task2Input.compEdgeDelRoundAddr Task2Input.vhatOffsetAddr
      Task2Input.compEdgeBaseAddr Task2Input.dsHandlesAddr Task2Input.embWJAddr
    omega
  have hmul : ctx.wd.W.m * (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) ≤
      Task1Input.mwCap impl inp.J * (2 * Task2Input.gammaExpCap impl inp.J + 5) :=
    Nat.mul_le_mul hmW (by omega)
  dsimp only [T2StaticData.dsBaseAddr, Task2Input.staticEndCap]
  linarith [stc.hNodes_hi, hn_mono, hmul]

def t2KNodeStep : ℕ := 45
def t2KVhatStep : ℕ := 32

noncomputable def t2KDelPlusHdr (pds : PathDSParams) (phiNum phiDen M : ℕ) : ℕ :=
  ⌈pds.K_del * pds.γ_query ((phiNum : ℝ) / (phiDen : ℝ)) M⌉₊ + 100

noncomputable def t2UndelRem {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (g : T2Ghost impl.pathDS) : ℕ :=
  ∑ ci ∈ Finset.range ctx.wd.comps.length,
    ((ctx.wd.comps.getD ci defaultCompInfo).J_sub.m -
      ((Finset.range (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m).filter
        (· ∈ (g.states ci).deleted)).card)

noncomputable def t2VhatRem {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (g : T2Ghost impl.pathDS) : ℕ :=
  ∑ ci ∈ Finset.range ctx.wd.comps.length,
    ((ctx.wd.comps.getD ci defaultCompInfo).J_sub.n -
      ((Finset.range (ctx.wd.comps.getD ci defaultCompInfo).J_sub.n).filter
        (· ∈ (g.states ci).Vhat)).card)

def t2NodeRem {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (_ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData _ctx) (g : T2Ghost impl.pathDS) : ℕ :=
  ∑ x ∈ (Finset.range inp.H'.n).filter (· ∉ g.drained), (stc.L_inc x).length

noncomputable def t2StepPhi {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (g : T2Ghost impl.pathDS)
    (mem : ℕ → ℕ) : ℕ :=
  t2RoundPhi impl.pathDS
    (t2KDelPlusHdr impl.pathDS.params ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
      ctx.wd.J0_strip.m)
    t2KVhatStep t2KNodeStep (inp.dsHandlesAddr ctx.wd.W.m) ctx.wd.comps.length
    (t2UndelRem ctx g) (t2VhatRem ctx g) (t2NodeRem ctx stc g) g.reps mem

/-- Full machine + mathematical invariant active between `t2MiddleEdge` / `t2DrainQueue` calls
inside round `g.η₁` (`1 ≤ g.η₁ ≤ eta1Bound wd inp.J`). -/
structure T2StepInv {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (g : T2Ghost impl.pathDS)
    (mem : ℕ → ℕ) : Prop where
  agr_pre : ∀ a < inp.v1, mem a = mem₀ a
  h0 : mem inp.v1 = inp.embWJAddr
  h1 : mem (inp.v1 + 1) = g.η₁
  hη_pos : 1 ≤ g.η₁
  hη_bd : g.η₁ ≤ eta1Bound ctx.wd inp.J
  h2 : mem (inp.v1 + 2) = g.initCountJ
  hInitC : g.initCountJ = g.η₁ * ctx.wd.comps.length
  h3 : mem (inp.v1 + 3) = g.initEdgesJ
  hInitE : g.initEdgesJ = g.η₁ * (ctx.wd.comps.map fun c => c.J_sub.m).sum
  h4 : mem (inp.v1 + 4) = g.getPathCountJ
  hGetC : g.getPathCountJ + (unembeddedSetPure ctx.wd g.emb).card =
    ctx.wd.W.m - ctx.wd.j0Edges.length
  h5 : mem (inp.v1 + 5) = g.deleteCountJ
  hDelEq : g.deleteCountJ = g.prevDelCountJ +
    ∑ ci ∈ Finset.range ctx.wd.comps.length, (g.states ci).deleted.card
  hPrevDel : g.prevDelCountJ ≤ (g.η₁ - 1) * inp.J.m
  h6 : mem (inp.v1 + 6) = g.vcongUpdates
  hVcUpd : (g.vcongUpdates : ℝ) ≤
    (g.getPathCountJ : ℝ) * (ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1))
  h7 : mem (inp.v1 + 7) = g.innerIters1
  hInner : (g.innerIters1 + g.queue.length : ℝ) ≤
    (g.getPathCountJ : ℝ) * (ctx.wd.γ_ExpPath * ((length inp.J inp.embJH : ℝ) + 1))
  h8 : mem (inp.v1 + 8) = ctx.wd.W.m
  h9 : mem (inp.v1 + 9) = inp.H'.n
  h10 : mem (inp.v1 + 10) = ctx.wd.comps.length
  h12 : mem (inp.v1 + 12) = inp.embJHAddr
  h13 : mem (inp.v1 + 13) = ctx.wInp.prep.h
  h14 : mem (inp.v1 + 14) = ctx.wInp.h
  h15 : mem (inp.v1 + 15) = inp.dsHandlesAddr ctx.wd.W.m
  h16 : mem (inp.v1 + 16) = inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length
  h17 : mem (inp.v1 + 17) = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length
  h18 : mem (inp.v1 + 18) = inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length
  h19 : mem (inp.v1 + 19) = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length
  h20 : mem (inp.v1 + 20) = inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length
  h21 : mem (inp.v1 + 21) = inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length
  h22 : mem (inp.v1 + 22) = inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length
  h23 : mem (inp.v1 + 23) = inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length
  h24 : mem (inp.v1 + 24) = inp.queueAddr ctx.wd.W.m ctx.wd.comps.length
  h25 : mem (inp.v1 + 25) = g.arenaPtr
  h26 : mem (inp.v1 + 26) = g.queryId
  hQid : g.queryId = ctx.wd.j0Edges.length + g.getPathCountJ
  h27 : mem (inp.v1 + 27) = g.queue.length
  h28 : mem (inp.v1 + 28) = g.η₁ * ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
    ctx.wInp.prep.phiDen_dec
  h29 : mem (inp.v1 + 29) = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params *
    ctx.wInp.prep.phiDen_dec
  h30 : mem (inp.v1 + 30) = (unembeddedSetPure ctx.wd g.emb).card
  h31 : mem (inp.v1 + 31) = ctx.wInp.prep.phiDen_dec
  hCeb : ∀ ci < ctx.wd.comps.length,
    mem (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ci) = compEdgeBase ctx.wd ci
  hVho : ∀ ci < ctx.wd.comps.length,
    mem (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci) = vhatBase ctx.wd ci
  hInc : ∀ x < inp.H'.n,
    IncChainBound mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd
      (mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x)) (stc.L_inc x) ∧
    (∀ p ∈ stc.L_inc x, ∃ (hp : p.1 < ctx.wd.comps.length),
      p.2 < (ctx.wd.comps[p.1]'hp).J_sub.m ∧
      x ∈ (inp.embJH ((ctx.wd.comps[p.1]'hp).jSubOrigEdges.getD p.2 0)).verts) ∧
    (∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (b : ℕ), b < (ctx.wd.comps[ci]'hci).J_sub.m →
      x ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts → (ci, b) ∈ stc.L_inc x)
  hEmb : EmbInv mem inp.embWJAddr ctx.wd.W.m stc.nodesEnd g.arenaPtr g.emb
  hAr_le : g.arenaPtr ≤ stc.nodesEnd +
    (ctx.wd.j0Edges.length + g.getPathCountJ) *
      (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5)
  hDS : DSArrayAt impl.pathDS ctx.wd.comps ctx.wInp.prep.phiNum_dec ctx.wInp.prep.phiDen_dec
    ctx.wd.J0_strip.m w stc.dsBaseAddr (inp.dsHandlesAddr ctx.wd.W.m) g.hCur mem
    ctx.wd.comps.length g.states g.reps
  hDelR : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (b : ℕ), b < (ctx.wd.comps[ci]'hci).J_sub.m →
    mem (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci + b) ≤
      g.η₁ ∧
    (mem (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci + b) =
      g.η₁ ↔ b ∈ (g.states ci).deleted)
  hVhatS : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (y : ℕ), y < (ctx.wd.comps[ci]'hci).J_sub.n →
    mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + y) ≤ g.η₁ ∧
    (mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + y) = g.η₁ ↔
      y ∈ (g.states ci).Vhat)
  hDelSub : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (b : ℕ), b ∈ (g.states ci).deleted →
    b < (ctx.wd.comps[ci]'hci).J_sub.m ∧
    ∃ x ∈ g.procVerts, x ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts
  hVc : ∀ x < inp.H'.n,
    mem (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) =
      vcongNumPure ctx.wd inp.J inp.embJH (fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i)) g.emb x
  hEwSt : ∀ x < inp.H'.n,
    mem (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) ≤ g.queryId
  hProcS : ∀ x < inp.H'.n,
    mem (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x) ≤ g.η₁ ∧
    (mem (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x) = g.η₁ ↔ x ∈ g.procVerts)
  hProcSub : ∀ x ∈ g.procVerts, x < inp.H'.n ∧
    (g.η₁ : ℝ) * ctx.wd.τ₁ ≤
      vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk g.emb)) x
  hQ_nd : g.queue.Nodup
  hQ_sub : ∀ x ∈ g.queue, x < inp.H'.n ∧ x ∈ g.procVerts ∧ x ∉ g.drained
  hDr_sub : g.drained ⊆ g.procVerts
  hQ_mem : ∀ x ∈ g.procVerts, x ∈ g.queue ↔ x ∉ g.drained
  hQ_at : ∀ (i : ℕ) (hi : i < g.queue.length),
    mem (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length + i) = g.queue[i]'hi
  hDr_del : ∀ x ∈ g.drained, x < inp.H'.n →
    ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (b : ℕ), b < (ctx.wd.comps[ci]'hci).J_sub.m →
      x ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts →
      b ∈ (g.states ci).deleted
  hPart : IsPartialEmbedding ctx.wd.W inp.J g.emb
  hMono : ∀ eW < ctx.wd.W.m, g.emb_prev eW = none ∨ g.emb eW = g.emb_prev eW
  hj0 : ∀ eW < ctx.wd.j0Edges.length, (g.emb eW).isSome = true
  hELen : ∀ eW < ctx.wd.W.m, ((partialToWalk g.emb eW).edges.length : ℝ) ≤ ctx.wd.γ_ExpPath
  hVc_prev : ∀ x < inp.H'.n,
    vcongAt ctx.wd.W ctx.wd.wW (compose inp.J inp.embJH (partialToWalk g.emb_prev)) x ≤
      (((g.η₁ - 1 : ℕ) : ℝ) + 1 / 2) * ctx.wd.τ₁
  hVol_prev : volWRemPure ctx.wd g.emb_prev ≤
    (2 * ctx.wd.c_deg / (2 * ctx.wd.c_deg + 1)) ^ (g.η₁ - 1) * (ctx.wd.c_deg * (inp.J.m : ℝ))
  hHCur_le : g.hCur ≤ stc.dsBaseAddr +
    (g.initCountJ + g.deleteCountJ + g.getPathCountJ) * t2DsOne impl inp.J

lemma T2StepInv.hCur_le_maxHeap {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {ctx : T2Ctx impl inp mem₀ w} {stc : T2StaticData ctx} {g : T2Ghost impl.pathDS}
    {mem : ℕ → ℕ} (h : T2StepInv ctx stc g mem) :
    g.hCur ≤ Task2Input.maxHeapEnd impl inp := by
  have hmW := ctx.hmW_le
  have hK := ctx.hK_le
  have hη₁ : 1 ≤ g.η₁ := h.hη_pos
  have hdel_cur : ∑ ci ∈ Finset.range ctx.wd.comps.length, (g.states ci).deleted.card ≤ inp.J.m := by
    let delImg : ℕ → Finset ℕ := fun ci =>
      ((Finset.range (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m).filter (· ∈ (g.states ci).deleted)).image
        (fun b => (ctx.wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)
    have hsub_j : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (b : ℕ),
        b ∈ (g.states ci).deleted → b ∈ Finset.range (ctx.wd.comps[ci]'hci).J_sub.m := fun ci hci b hb =>
      Finset.mem_range.mpr (h.hDelSub ci hci b hb).1
    have hcard_eq : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length),
        (g.states ci).deleted.card = (delImg ci).card := fun ci hci => by
      have hget : ctx.wd.comps.getD ci defaultCompInfo = ctx.wd.comps[ci]'hci :=
        List.getD_eq_getElem _ _ hci
      have hf : (g.states ci).deleted =
          (Finset.range (ctx.wd.comps[ci]'hci).J_sub.m).filter (· ∈ (g.states ci).deleted) := by
        ext b; simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨fun hb => ⟨Finset.mem_range.mp (hsub_j ci hci b hb), hb⟩, fun hb => hb.2⟩
      rw [hf]; dsimp only [delImg]; rw [hget]; symm
      refine Finset.card_image_of_injOn fun a ha b hb hab => ?_
      have ha_m := (Finset.mem_filter.mp ha).1; have hb_m := (Finset.mem_filter.mp hb).1
      rw [Finset.mem_range] at ha_m hb_m
      have hpr := (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [List.getD_eq_getElem _ _ (by rw [hpr.1]; exact ha_m),
          List.getD_eq_getElem _ _ (by rw [hpr.1]; exact hb_m)] at hab
      exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hpr.2.1)
        (a₁ := ⟨a, by rw [hpr.1]; exact ha_m⟩) (a₂ := ⟨b, by rw [hpr.1]; exact hb_m⟩) hab)
    have hsum_eq : ∑ ci ∈ Finset.range ctx.wd.comps.length, (g.states ci).deleted.card =
        ((Finset.range ctx.wd.comps.length).biUnion fun ci =>
          if ci < ctx.wd.comps.length then delImg ci else ∅).card := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun ci hci => ?_
        have hci' := Finset.mem_range.mp hci
        simp only [hci', ↓reduceIte, hcard_eq ci hci']
      · intro c1 h1 c2 h2 hne
        change Disjoint _ _
        have h1' := Finset.mem_range.mp h1; have h2' := Finset.mem_range.mp h2
        simp only [h1', h2', ↓reduceIte, Finset.disjoint_left]
        intro j hj1 hj2
        rcases Finset.mem_image.mp hj1 with ⟨a, ha, rfl⟩
        rcases Finset.mem_image.mp hj2 with ⟨b, hb, hab⟩
        have hget1 : ctx.wd.comps.getD c1 defaultCompInfo = ctx.wd.comps[c1]'h1' :=
          List.getD_eq_getElem _ _ h1'
        have hget2 : ctx.wd.comps.getD c2 defaultCompInfo = ctx.wd.comps[c2]'h2' :=
          List.getD_eq_getElem _ _ h2'
        rw [hget1] at ha hab; rw [hget2] at hb hab
        have ha_m := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have hb_m := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        have hp1 := (ctx.hw_okW.comp_props c1 h1').2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have hp2 := (ctx.hw_okW.comp_props c2 h2').2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have h1m : ctx.wd.comps[c1].jSubOrigEdges.getD a 0 ∈ ctx.wd.comps[c1].jSubOrigEdges.toFinset := by
          rw [List.mem_toFinset, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
        have h2m : ctx.wd.comps[c2].jSubOrigEdges.getD b 0 ∈ ctx.wd.comps[c2].jSubOrigEdges.toFinset := by
          rw [List.mem_toFinset, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
        rw [← hab] at h1m
        exact Finset.disjoint_left.mp (ctx.hw_okW.comp_disjoint c1 c2 h1' h2' hne) h1m h2m
    have hsub_J : ((Finset.range ctx.wd.comps.length).biUnion fun ci =>
        if ci < ctx.wd.comps.length then delImg ci else ∅) ⊆ Finset.range inp.J.m := by
      intro j hj
      rcases Finset.mem_biUnion.mp hj with ⟨ci, hci_r, hjci⟩
      have hci := Finset.mem_range.mp hci_r
      simp only [hci, ↓reduceIte] at hjci
      rcases Finset.mem_image.mp hjci with ⟨b, hb, rfl⟩
      have hget : ctx.wd.comps.getD ci defaultCompInfo = ctx.wd.comps[ci]'hci :=
        List.getD_eq_getElem _ _ hci
      dsimp only [delImg] at *; rw [hget] at hb ⊢
      have hb_m := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      have hp := (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [Finset.mem_range, ← ctx.hWInpJ, List.getD_eq_getElem _ _ (by omega)]
      exact hp.2.2.1 _ (List.getElem_mem _)
    rw [hsum_eq]
    exact (Finset.card_le_card hsub_J).trans_eq (Finset.card_range inp.J.m)
  have hdel_tot : g.deleteCountJ ≤ g.η₁ * inp.J.m := by
    rw [h.hDelEq]
    have hmul : (g.η₁ - 1) * inp.J.m + inp.J.m = g.η₁ * inp.J.m := by
      calc (g.η₁ - 1) * inp.J.m + inp.J.m = (g.η₁ - 1 + 1) * inp.J.m := by ring
        _ = g.η₁ * inp.J.m := by rw [Nat.sub_add_cancel hη₁]
    linarith [h.hPrevDel, hdel_cur]
  have hη₁_cap : eta1Bound ctx.wd inp.J ≤ Task2Input.eta1Cap impl inp.J :=
    ctx.hWInpJ ▸ task2_eta1Bound_le_cap ctx.hstat ctx.hφ_lb
  have hinit_le : g.initCountJ ≤ Task2Input.eta1Cap impl inp.J * inp.J.m := by
    rw [h.hInitC]; exact Nat.mul_le_mul (le_trans h.hη_bd hη₁_cap) hK
  have hdel_le : g.deleteCountJ ≤ Task2Input.eta1Cap impl inp.J * inp.J.m :=
    le_trans hdel_tot (Nat.mul_le_mul_right _ (le_trans h.hη_bd hη₁_cap))
  have hgp_le : g.getPathCountJ ≤ Task1Input.mwCap impl inp.J := by
    have : g.getPathCountJ ≤ ctx.wd.W.m := by have := h.hGetC; omega
    exact le_trans this hmW
  have hds : (g.initCountJ + g.deleteCountJ + g.getPathCountJ) * t2DsOne impl inp.J ≤
      Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
        Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
        Task1Input.mwCap impl inp.J * t2DsOne impl inp.J := by
    have hs := Nat.mul_le_mul_right (t2DsOne impl inp.J) (show g.initCountJ + g.deleteCountJ + g.getPathCountJ ≤
      Task2Input.eta1Cap impl inp.J * inp.J.m + Task2Input.eta1Cap impl inp.J * inp.J.m +
        Task1Input.mwCap impl inp.J by omega)
    simpa only [Nat.add_mul] using hs
  have hstc := stc.dsBaseAddr_le_cap
  unfold Task2Input.maxHeapEnd
  change g.hCur ≤ Task2Input.staticEndCap impl inp +
    Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
    Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
    Task1Input.mwCap impl inp.J * t2DsOne impl inp.J
  linarith [h.hHCur_le]

end MinCostFlow.Spanner
