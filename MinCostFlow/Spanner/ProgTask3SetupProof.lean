module

public import MinCostFlow.Spanner.ProgTask3DSOps

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# Static Layout, Outer Invariant, and Setup / Init-Embedding Proofs for Task 3

Defines `T3Layout`, `T3StaticMem`, `T3OuterInv`, potential `t3EcongPhi`, read-only accessors
into the Task 1 / `witnessPrep` / `buildWitness` tables, `t3InitEmb_ptriple` (`selfBase + 1`),
and `t3Setup_ptriple` (the setup prefix of `task3Body` through calling `t3InitEmbBody`).
-/

/-- Memory offsets of all Task 3 arrays allocated starting at `inp.v2 + t3HdrSize`. -/
structure T3Layout where
  base : ℕ
  embJWAddr : ℕ
  dsHandlesAddr : ℕ
  econgCountAddr : ℕ
  wDelStampAddr : ℕ
  queueAddr : ℕ
  vhatOffsetAddr : ℕ
  vhatStampAddr : ℕ
  staticEnd : ℕ

noncomputable def T3Layout.ofCtx {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) : T3Layout :=
  let base := inp.v2
  let K := ctx.wd.comps.length
  let Wm := ctx.wd.W.m
  let vhatSum := (ctx.wd.comps.map fun c => c.W_sub.n).sum
  let embJWAddr := base + t3HdrSize
  let dsHandlesAddr := embJWAddr + inp.J.m
  let econgCountAddr := dsHandlesAddr + K
  let wDelStampAddr := econgCountAddr + Wm
  let queueAddr := wDelStampAddr + Wm
  let vhatOffsetAddr := queueAddr + Wm
  let vhatStampAddr := vhatOffsetAddr + K
  let staticEnd := vhatStampAddr + vhatSum
  { base, embJWAddr, dsHandlesAddr, econgCountAddr, wDelStampAddr, queueAddr,
    vhatOffsetAddr, vhatStampAddr, staticEnd }

lemma T3Layout.bounds {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) :
    let lay := T3Layout.ofCtx ctx
    lay.base = inp.v2 ∧
    lay.embJWAddr = lay.base + t3HdrSize ∧
    lay.dsHandlesAddr = lay.embJWAddr + inp.J.m ∧
    lay.econgCountAddr = lay.dsHandlesAddr + ctx.wd.comps.length ∧
    lay.wDelStampAddr = lay.econgCountAddr + ctx.wd.W.m ∧
    lay.queueAddr = lay.wDelStampAddr + ctx.wd.W.m ∧
    lay.vhatOffsetAddr = lay.queueAddr + ctx.wd.W.m ∧
    lay.vhatStampAddr = lay.vhatOffsetAddr + ctx.wd.comps.length ∧
    lay.staticEnd = lay.vhatStampAddr + (ctx.wd.comps.map fun c => c.W_sub.n).sum ∧
    lay.staticEnd ≤ Task3Input.staticEndCap impl inp ∧
    Task3Input.staticEndCap impl inp ≤ Task3Input.maxHeapEnd impl inp ∧
    lay.staticEnd + 3 < 2 ^ w := by
  have hK := ctx.hK_le
  have hmW := ctx.hmW_le
  have hvh := ctx.hvhatSum_le
  have hwb := ctx.hwokW.2.2
  have hcap : (T3Layout.ofCtx ctx).staticEnd ≤ Task3Input.staticEndCap impl inp := by
    simp only [T3Layout.ofCtx, Task3Input.staticEndCap]; omega
  have hmax : Task3Input.staticEndCap impl inp ≤ Task3Input.maxHeapEnd impl inp := by
    simp only [Task3Input.maxHeapEnd]; omega
  have hlt_w : (T3Layout.ofCtx ctx).staticEnd + 3 < 2 ^ w := by
    have : Task3Input.maxHeapEnd impl inp + 3 ≤ Task3Input.maxWordBound impl inp := le_max_left _ _
    omega
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcap, hmax, hlt_w⟩

/-- Agreement below `inp.v2` together with all immutable Task 3 header slots and `vhatOffset`. -/
def T3StaticMem {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (mem : ℕ → ℕ) : Prop :=
  (∀ x < inp.v2, mem x = mem₀ x) ∧
  mem (lay.base + t3OffEmbJW) = lay.embJWAddr ∧
  mem (lay.base + t3OffJAddr) = inp.jAddr ∧
  mem (lay.base + t3OffT1Addr) = inp.t1OutAddr ∧
  mem (lay.base + t3OffJm) = inp.J.m ∧
  mem (lay.base + t3OffWm) = ctx.wd.W.m ∧
  mem (lay.base + t3OffK) = ctx.wd.comps.length ∧
  mem (lay.base + t3OffPrepH) = ctx.wInp.prep.h ∧
  mem (lay.base + t3OffWInpH) = ctx.wInp.h ∧
  mem (lay.base + t3OffAComps) = ctx.wInp.prep.aComps ∧
  mem (lay.base + t3OffACompExt) = ctx.memT1 (ctx.wInp.h + 12) ∧
  mem (lay.base + t3OffWAddr) = ctx.memT1 (ctx.wInp.h + 13) ∧
  mem (lay.base + t3OffWWNum) = ctx.memT1 (ctx.wInp.h + 14) ∧
  mem (lay.base + t3OffWSrc) = ctx.memT1 (ctx.wInp.h + 15) ∧
  mem (lay.base + t3OffJSrc) = ctx.memT1 (ctx.wInp.h + 16) ∧
  mem (lay.base + t3OffTau2) = ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params ∧
  mem (lay.base + t3OffPhiDen) = ctx.wInp.prep.phiDen_dec ∧
  mem (lay.base + t3OffMw) = ctx.wd.M_W ∧
  mem (lay.base + t3OffPhiNumC) = impl.constructExpander.phiNum ∧
  mem (lay.base + t3OffPhiDenC) = impl.constructExpander.phiDen ∧
  mem (lay.base + t3OffDsHdl) = lay.dsHandlesAddr ∧
  mem (lay.base + t3OffECnt) = lay.econgCountAddr ∧
  mem (lay.base + t3OffWDel) = lay.wDelStampAddr ∧
  mem (lay.base + t3OffQueue) = lay.queueAddr ∧
  mem (lay.base + t3OffVOff) = lay.vhatOffsetAddr ∧
  mem (lay.base + t3OffVStmp) = lay.vhatStampAddr ∧
  (∀ ci < ctx.wd.comps.length, mem (lay.vhatOffsetAddr + ci) = vhatBaseW ctx.wd ci)

lemma T3StaticMem.mono {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {ctx : T3Ctx impl inp mem₀ w} {lay : T3Layout} {mem mem' : ℕ → ℕ}
    (hs : T3StaticMem ctx lay mem)
    (hbelow : ∀ x < inp.v2, mem' x = mem x)
    (hhdr : ∀ i < t3HdrSize, i ≠ t3OffEta2 → i ≠ t3OffGetPath → i ≠ t3OffDel →
      i ≠ t3OffEcongUpd → i ≠ t3OffHCur → i ≠ t3OffNextU → i ≠ t3OffCont →
      mem' (lay.base + i) = mem (lay.base + i))
    (hvoff : ∀ ci < ctx.wd.comps.length, mem' (lay.vhatOffsetAddr + ci) = mem (lay.vhatOffsetAddr + ci)) :
    T3StaticMem ctx lay mem' := by
  rcases hs with ⟨ha, h0, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvo⟩
  refine ⟨fun x hx => (hbelow x hx).trans (ha x hx), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hhdr t3OffEmbJW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0
  · exact (hhdr t3OffJAddr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h6
  · exact (hhdr t3OffT1Addr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h7
  · exact (hhdr t3OffJm (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
  · exact (hhdr t3OffWm (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h9
  · exact (hhdr t3OffK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10
  · exact (hhdr t3OffPrepH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h11
  · exact (hhdr t3OffWInpH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12
  · exact (hhdr t3OffAComps (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13
  · exact (hhdr t3OffACompExt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14
  · exact (hhdr t3OffWAddr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h15
  · exact (hhdr t3OffWWNum (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16
  · exact (hhdr t3OffWSrc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17
  · exact (hhdr t3OffJSrc (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h18
  · exact (hhdr t3OffTau2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19
  · exact (hhdr t3OffPhiDen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20
  · exact (hhdr t3OffMw (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h21
  · exact (hhdr t3OffPhiNumC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22
  · exact (hhdr t3OffPhiDenC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23
  · exact (hhdr t3OffDsHdl (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24
  · exact (hhdr t3OffECnt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h25
  · exact (hhdr t3OffWDel (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h26
  · exact (hhdr t3OffQueue (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h27
  · exact (hhdr t3OffVOff (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28
  · exact (hhdr t3OffVStmp (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h29
  · exact fun ci hci => (hvoff ci hci).trans (hvo ci hci)

lemma T3StaticMem.of_agree_ds {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {ctx : T3Ctx impl inp mem₀ w} {lay : T3Layout} (hlay : lay = T3Layout.ofCtx ctx) {mem mem' : ℕ → ℕ}
    (hs : T3StaticMem ctx lay mem)
    (hag : ∀ a < lay.vhatStampAddr, mem' a = mem a) :
    T3StaticMem ctx lay mem' := by
  subst hlay
  have hb := T3Layout.bounds ctx
  exact hs.mono (fun x hx => hag x (by omega))
    (fun i hi _ _ _ _ _ _ _ => hag _ (by omega))
    (fun ci hci => hag _ (by omega))

namespace T3Ctx

lemma outAt {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) :
    ctx.wInp.OutputAt impl.constructExpander impl.pathDS.params
      (fun x => if x < ctx.wInp.h then ctx.memT1 x else ctx.memPre x) ctx.memT1 ctx.v1 ctx.wd :=
  ctx.hOut ctx.memPre

lemma comps_len_eq {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) :
    ctx.wd.comps.length = ctx.wInp.prep.rawComps.length :=
  ctx.wInp.buildCompsFrom_length _ _ _ ctx.hws.1

lemma lt_v1_of_t1 {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) :
    ctx.wInp.prep.h + 8 ≤ ctx.wInp.prep.hEnd ∧
      ctx.wInp.prep.hEnd ≤ ctx.wInp.h ∧ ctx.wInp.h + 20 ≤ ctx.v1 ∧
      inp.t1OutAddr + 6 ≤ ctx.wInp.prep.h := by
  have h1 := ctx.hPrepEnd
  have h2 := ctx.hv1_lo
  have h3 := ctx.hStat.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdec4 : 4 ≤ (Decompose.encode ctx.wInp.prep.d_ℓ ctx.wInp.prep.phiNum_dec
      ctx.wInp.prep.phiDen_dec ctx.wInp.prep.level ctx.wInp.prep.rawComps).length := by
    unfold Decompose.encode
    simp only [List.length_cons, List.length_append]
    omega
  have := ctx.hJ0Addr; have := ctx.hNlAddr; have := ctx.hDecAddr
  have := ctx.wInp.prep.hBlocksStart_eq
  have := ctx.wInp.prep.cJSubPtr_zero
  have := ctx.wInp.prep.cJSubPtr_le_hEnd (Nat.zero_le _)
  simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps,
    PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead] at *
  omega

lemma read_lt_v1 {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) {mem : ℕ → ℕ}
    (hbelow : ∀ x < inp.v2, mem x = mem₀ x) {x : ℕ} (hx : x < ctx.v1) :
    mem x = ctx.memT1 x :=
  (hbelow x (lt_of_lt_of_le hx ctx.hv1_le)).trans (ctx.hT1Agr x hx)

lemma read_j_graphAt {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) {mem : ℕ → ℕ} (hbelow : ∀ x < inp.v2, mem x = mem₀ x) :
    GraphAt mem inp.jAddr inp.J :=
  ctx.hJ_at.of_agree_below
    (le_trans ctx.hJ_lt_t1 (by have := ctx.lt_v1_of_t1; omega))
    (fun k hk => hbelow k (lt_of_lt_of_le hk ctx.hv1_le))

lemma read_out_fields {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) {mem : ℕ → ℕ} (hbelow : ∀ x < inp.v2, mem x = mem₀ x) :
    let aExt := ctx.memT1 (ctx.wInp.h + 12)
    let wAddr := ctx.memT1 (ctx.wInp.h + 13)
    let wWNum := ctx.memT1 (ctx.wInp.h + 14)
    let wSrc := ctx.memT1 (ctx.wInp.h + 15)
    let jSrc := ctx.memT1 (ctx.wInp.h + 16)
    mem (inp.t1OutAddr + 4) = ctx.wInp.prep.h ∧
    mem (inp.t1OutAddr + 5) = ctx.wInp.h ∧
    mem ctx.wInp.prep.h = ctx.wInp.prep.j0Edges.length ∧
    mem (ctx.wInp.prep.h + 2) = ctx.wd.comps.length ∧
    mem (ctx.wInp.prep.h + 3) = ctx.wInp.prep.aComps ∧
    mem ctx.wInp.h = ctx.wd.M_W ∧
    mem (ctx.wInp.h + 11) = ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params ∧
    mem (ctx.wInp.h + 12) = aExt ∧
    mem (ctx.wInp.h + 13) = wAddr ∧
    mem (ctx.wInp.h + 14) = wWNum ∧
    mem (ctx.wInp.h + 15) = wSrc ∧
    mem (ctx.wInp.h + 16) = jSrc ∧
    mem (ctx.wInp.h + 18) = ctx.wInp.prep.phiDen_dec ∧
    CompExtAt mem aExt ctx.wInp.prep.phiNum_dec wAddr ctx.wd.comps ∧
    GraphAt mem wAddr ctx.wd.W ∧
    (∀ eW < ctx.wd.W.m, (mem (wWNum + eW) : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ) = ctx.wd.wW eW ∧
      1 ≤ mem (wWNum + eW) ∧ mem (wWNum + eW) ≤ maxDeg inp.J * ctx.wInp.prep.phiDen_dec) ∧
    WSourcesAt mem wSrc ctx.wd.wSources ∧
    JSourcesAt mem jSrc ctx.wd.jSources ∧
    ctx.wInp.h + 20 ≤ aExt ∧
    aExt + 6 * ctx.wd.comps.length ≤ wAddr ∧
    wAddr + (2 + 2 * ctx.wd.W.m) = wWNum ∧
    wSrc = wWNum + ctx.wd.W.m ∧
    jSrc = wSrc + 3 * ctx.wd.W.m ∧
    ctx.v1 = jSrc + 3 * inp.J.m := by
  have hlt := ctx.lt_v1_of_t1
  have ho := ctx.outAt
  have hsc := ctx.wInp.mkWitnessData_scalars impl.constructExpander impl.pathDS.params ctx.WSubs ctx.hStat
  rcases ho with ⟨_, _, _, _, hmw, _, _, _, _, _, _, _, _, _, _, htau2, _, hpd, _,
    halo, haw, hwn, hws_eq, hjs_eq, hv1_eq, hce, hWg, hww, hws_at, hjs_at⟩
  have hm_eq := ctx.hWInpJ ▸ hv1_eq
  have hagr : ∀ x < ctx.v1, mem x = ctx.memT1 x := fun x hx => ctx.read_lt_v1 hbelow hx
  have hce' : CompExtAt mem (ctx.memT1 (ctx.wInp.h + 12)) ctx.wInp.prep.phiNum_dec
      (ctx.memT1 (ctx.wInp.h + 13)) ctx.wd.comps := by
    intro ci hci
    have hc := hce ci hci
    have hptr : ctx.memT1 (ctx.memT1 (ctx.wInp.h + 12) + 6 * ci + 1) =
        mem (ctx.memT1 (ctx.wInp.h + 12) + 6 * ci + 1) :=
      (hagr _ (by omega)).symm
    refine ⟨(hagr _ (by omega)).trans hc.1, (hagr _ (by omega)).trans hc.2.1,
      (hagr _ (by omega)).trans hc.2.2.1, (hagr _ (by omega)).trans hc.2.2.2.1,
      (hagr _ (by omega)).trans hc.2.2.2.2.1, ?_, hptr ▸ hc.2.2.2.2.2.2.1, hptr ▸ hc.2.2.2.2.2.2.2⟩
    have hg := hc.2.2.2.2.2.1.of_agree_below (a := ctx.memT1 (ctx.memT1 (ctx.wInp.h + 12) + 6 * ci + 1))
      (bound := ctx.v1) (mem' := mem) (by rw [graph_encode_length]; omega) hagr
    rwa [hptr] at hg
  have hWg' : GraphAt mem (ctx.memT1 (ctx.wInp.h + 13)) ctx.wd.W :=
    hWg.of_agree_below (by rw [graph_encode_length]; omega) hagr
  have hww' : ∀ eW < ctx.wd.W.m,
      (mem (ctx.memT1 (ctx.wInp.h + 14) + eW) : ℝ) / (ctx.wInp.prep.phiDen_dec : ℝ) = ctx.wd.wW eW ∧
      1 ≤ mem (ctx.memT1 (ctx.wInp.h + 14) + eW) ∧
      mem (ctx.memT1 (ctx.wInp.h + 14) + eW) ≤ maxDeg inp.J * ctx.wInp.prep.phiDen_dec := by
    intro eW heW
    have hdiv := (hww eW heW).1
    have h1 := (hww eW heW).2
    have hagree : mem (ctx.memT1 (ctx.wInp.h + 14) + eW) = ctx.memT1 (ctx.memT1 (ctx.wInp.h + 14) + eW) :=
      hagr _ (by omega)
    rw [hagree]
    have hmax := ctx.hWInpJ ▸ mkW_wW_le_maxDeg ctx.hStat ctx.hw_okW ctx.hws heW
    have hpd_pos : (0 : ℝ) < (ctx.wInp.prep.phiDen_dec : ℝ) := by
      have := ctx.hStat.2.2.2.2.2.2.2.2.1
      have := ctx.hStat.2.2.2.2.2.2.2.2.2.1
      exact_mod_cast (by omega : 0 < ctx.wInp.prep.phiDen_dec)
    have hle_r : (ctx.memT1 (ctx.memT1 (ctx.wInp.h + 14) + eW) : ℝ) ≤
        (maxDeg inp.J : ℝ) * (ctx.wInp.prep.phiDen_dec : ℝ) := by
      calc (ctx.memT1 (ctx.memT1 (ctx.wInp.h + 14) + eW) : ℝ)
          = ((ctx.memT1 (ctx.memT1 (ctx.wInp.h + 14) + eW) : ℝ) / ctx.wInp.prep.phiDen_dec) *
              ctx.wInp.prep.phiDen_dec := by field_simp
        _ = ctx.wd.wW eW * ctx.wInp.prep.phiDen_dec := by rw [hdiv]
        _ ≤ (maxDeg inp.J : ℝ) * ctx.wInp.prep.phiDen_dec := mul_le_mul_of_nonneg_right hmax (le_of_lt hpd_pos)
    have hle_n : ctx.memT1 (ctx.memT1 (ctx.wInp.h + 14) + eW) ≤ maxDeg inp.J * ctx.wInp.prep.phiDen_dec := by
      exact_mod_cast hle_r
    exact ⟨hdiv, h1, hle_n⟩
  have hws' : WSourcesAt mem (ctx.memT1 (ctx.wInp.h + 15)) ctx.wd.wSources := by
    intro i hi
    have hw := hws_at i hi
    have hlen : ctx.wd.wSources.length = ctx.wd.W.m := by
      have hwm := ctx.hw_okW.W_m_eq
      change (List.map WEdgeSource.fromJ0 ctx.wInp.prep.j0Edges ++
        List.flatMap (fun x => List.map (fun eL => WEdgeSource.fromComp x.2 eL)
          (List.range x.1.W_sub.m)) (ctx.wd.comps.zipIdx 0)).length = ctx.wd.W.m
      rw [List.length_append, List.length_map, List.length_flatMap]
      have hmap : (List.map (fun x : CompInfo × ℕ =>
          (List.map (fun eL => WEdgeSource.fromComp x.2 eL) (List.range x.1.W_sub.m)).length)
          (ctx.wd.comps.zipIdx 0)) = List.map (fun c : CompInfo => c.W_sub.m) ctx.wd.comps := by
        refine List.ext_getElem (by simp) fun j hj1 hj2 => ?_
        simp
      rw [hmap]
      change ctx.wInp.prep.j0Edges.length + (List.map (fun c : CompInfo => c.W_sub.m) ctx.wd.comps).sum = ctx.wd.W.m
      exact hwm.symm
    cases hws_eq' : ctx.wd.wSources[i] <;> rw [hws_eq'] at hw
    · exact ⟨(hagr _ (by omega)).trans hw.1, (hagr _ (by omega)).trans hw.2.1, (hagr _ (by omega)).trans hw.2.2⟩
    · exact ⟨(hagr _ (by omega)).trans hw.1, (hagr _ (by omega)).trans hw.2.1, (hagr _ (by omega)).trans hw.2.2⟩
  have hjs' : JSourcesAt mem (ctx.memT1 (ctx.wInp.h + 16)) ctx.wd.jSources := by
    intro i hi
    have hj := hjs_at i hi
    have hlen : ctx.wd.jSources.length = inp.J.m := by
      dsimp only [T3Ctx.wd, WitnessCoreInput.mkWitnessData]
      rw [List.length_map, List.length_range, ctx.hWInpJ]
    cases hjs_eq' : ctx.wd.jSources[i] <;> rw [hjs_eq'] at hj
    · exact ⟨(hagr _ (by omega)).trans hj.1, (hagr _ (by omega)).trans hj.2.1, (hagr _ (by omega)).trans hj.2.2⟩
    · exact ⟨(hagr _ (by omega)).trans hj.1, (hagr _ (by omega)).trans hj.2.1, (hagr _ (by omega)).trans hj.2.2⟩
    · exact ⟨(hagr _ (by omega)).trans hj.1, (hagr _ (by omega)).trans hj.2.1, (hagr _ (by omega)).trans hj.2.2⟩
  refine ⟨(hagr _ (by omega)).trans ctx.hSlot4, (hagr _ (by omega)).trans ctx.hSlot5,
    (hagr _ (by omega)).trans ctx.hPrepSt.2.1, ?_, (hagr _ (by omega)).trans ctx.hPrepSt.2.2.2.2.1,
    (hagr _ (by omega)).trans (hmw.trans hsc.1.symm), (hagr _ (by omega)).trans htau2,
    hagr _ (by omega), hagr _ (by omega), hagr _ (by omega), hagr _ (by omega),
    hagr _ (by omega), (hagr _ (by omega)).trans hpd, hce', hWg', hww', hws', hjs',
    halo, haw, hwn.symm, hws_eq, hjs_eq, hm_eq⟩
  · rw [ctx.comps_len_eq]; exact (hagr _ (by omega)).trans ctx.hPrepSt.2.2.2.1

lemma read_comp_prep {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) {mem : ℕ → ℕ} (hbelow : ∀ x < inp.v2, mem x = mem₀ x)
    {ci : ℕ} (hci : ci < ctx.wd.comps.length) :
    let c := ctx.wd.comps[ci]
    mem (ctx.wInp.prep.aComps + 7 * ci + 2) = ctx.wInp.prep.cVertsPtr ci ∧
    mem (ctx.wInp.prep.aComps + 7 * ci + 3) = ctx.wInp.prep.cJSubPtr ci ∧
    ListAt mem (ctx.wInp.prep.cVertsPtr ci) c.verts ∧
    GraphAt mem (ctx.wInp.prep.cJSubPtr ci) c.J_sub ∧
    ctx.wInp.prep.aComps + 7 * ctx.wd.comps.length ≤ ctx.wInp.prep.hEnd ∧
    ctx.wInp.prep.cVertsPtr ci + c.verts.length ≤ ctx.wInp.prep.h ∧
    ctx.wInp.prep.cJSubPtr ci + c.J_sub.encode.length ≤ ctx.wInp.prep.hEnd := by
  have hlt := ctx.lt_v1_of_t1
  have hagr : ∀ x < ctx.v1, mem x = ctx.memT1 x := fun x hx => ctx.read_lt_v1 hbelow hx
  have hci_r : ci < ctx.wInp.prep.rawComps.length := ctx.comps_len_eq ▸ hci
  have hgf := ctx.wInp.buildCompsFrom_getElem_full ctx.wInp.prep.j0Edges.length
    ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1 ci hci_r
  have hcd := ctx.hCompsDone ci hci_r
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci_r, Option.getD_some] at hcd
  have hrec := rawComps_recordAt ctx.hStat.toValid_zeroTail (mem := ctx.memT1) (fun x hx => by simp [hx]) hci_r
  have hrc_props := ctx.hStat.2.2.2.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem hci_r)
  have hverts_eq : vertsOf ctx.wInp.prep.rawComps[ci].2.toFinset = ctx.wInp.prep.rawComps[ci].2 :=
    vertsOf_toFinset_of_pairwise_lt hrc_props.2.2.1
  have hc_verts : ctx.wd.comps[ci].verts = ctx.wInp.prep.rawComps[ci].2 :=
    hgf.2.2.1.trans hverts_eq
  have hc_jsub : ctx.wd.comps[ci].J_sub = ctx.wInp.prep.cJSub ctx.wInp.prep.rawComps[ci] := hgf.2.2.2.1
  have hsum_le : ((ctx.wInp.prep.rawComps.take ci).map fun p => 2 + p.2.length).sum +
      (2 + ctx.wInp.prep.rawComps[ci].2.length) ≤
      (ctx.wInp.prep.rawComps.map fun p => 2 + p.2.length).sum := by
    have hsp : ctx.wInp.prep.rawComps = ctx.wInp.prep.rawComps.take ci ++
        ctx.wInp.prep.rawComps[ci] :: ctx.wInp.prep.rawComps.drop (ci + 1) := by
      rw [← List.drop_eq_getElem_cons hci_r, List.take_append_drop]
    conv_rhs => rw [hsp]
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    omega
  have hvp_bd : ctx.wInp.prep.cVertsPtr ci + ctx.wInp.prep.rawComps[ci].2.length ≤ ctx.wInp.prep.h := by
    have hfm : ∀ xs : List (ℕ × List ℕ), (xs.flatMap compRecord).length =
        (xs.map fun p => 2 + p.2.length).sum := fun xs => by
      induction xs with
      | nil => rfl
      | cons p ps ih => simp only [List.flatMap_cons, List.length_append, compRecord,
          List.length_cons, List.map_cons, List.sum_cons, ih]; omega
    have hdec_len : (Decompose.encode ctx.wInp.prep.d_ℓ ctx.wInp.prep.phiNum_dec
        ctx.wInp.prep.phiDen_dec ctx.wInp.prep.level ctx.wInp.prep.rawComps).length =
        4 + ctx.wInp.prep.J0_strip.m +
          (ctx.wInp.prep.rawComps.map fun p => 2 + p.2.length).sum := by
      unfold Decompose.encode
      simp only [List.length_cons, List.length_append, List.length_nil, hfm, ctx.hStat.2.2.2.2.2.2.2.1]
      omega
    have h17 := ctx.hStat.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simp only [PrepInput.cVertsPtr] at *; omega
  have haComps_bd : ctx.wInp.prep.aComps + 7 * ctx.wInp.prep.rawComps.length ≤ ctx.wInp.prep.hEnd := by
    have := ctx.wInp.prep.hBlocksStart_eq
    have := ctx.wInp.prep.cJSubPtr_zero
    have := ctx.wInp.prep.cJSubPtr_le_hEnd (Nat.zero_le _)
    simp only [PrepInput.aVLoc, PrepInput.aVComp] at *; omega
  have hcJSub_bd : ctx.wInp.prep.cJSubPtr ci +
      (ctx.wInp.prep.cJSub ctx.wInp.prep.rawComps[ci]).encode.length ≤ ctx.wInp.prep.hEnd := by
    have hsucc := ctx.wInp.prep.cJSubPtr_succ hci_r
    have hle := ctx.wInp.prep.cJSubPtr_le_hEnd (show ci + 1 ≤ ctx.wInp.prep.rawComps.length by omega)
    rw [graph_encode_length]
    simp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr,
      List.getD_eq_getElem _ _ hci_r] at hsucc
    omega
  have hrec_list : ListAt mem (ctx.wInp.prep.cVertsPtr ci) ctx.wInp.prep.rawComps[ci].2 :=
    hrec.2.2.of_agree_below hvp_bd (fun k hk => hagr k (by omega))
  refine ⟨(hagr _ (by omega)).trans hcd.2.2.1, (hagr _ (by omega)).trans hcd.2.2.2.1, ?_, ?_,
    ctx.comps_len_eq ▸ haComps_bd, by rw [hc_verts]; exact hvp_bd, by rw [hc_jsub]; exact hcJSub_bd⟩
  · rw [hc_verts]; exact hrec_list
  · rw [hc_jsub]
    exact hcd.2.2.2.2.2.2.2.1.of_agree_below hcJSub_bd (fun k hk => hagr k (by omega))

lemma jSubOrig_of_inComp {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) :
    ∀ eJ < inp.J.m, ∀ ci jL,
      ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jL →
      ∃ hci : ci < ctx.wd.comps.length, ctx.wd.comps[ci].jSubOrigEdges.getD jL 0 = eJ := by
  intro eJ heJ ci jL hsrc
  have heJ' : eJ < ctx.wInp.prep.J.m := ctx.hWInpJ.symm ▸ heJ
  have hs := mkW_jSources_spec ctx.hStat ctx.hw_okW ctx.hws heJ'
  have hs2 := hs.2
  dsimp only [T3Ctx.wd] at hsrc
  rw [hsrc] at hs2
  rcases hs2 with ⟨hci, hj, hget, _⟩
  exact ⟨hci, by change (ctx.wInp.mkWitnessData impl.constructExpander impl.pathDS.params ctx.WSubs).comps[ci].jSubOrigEdges.getD jL 0 = eJ; rw [List.getD_eq_getElem _ _ hj]; exact hget⟩

end T3Ctx

/-- Persistent potential: uncommitted congestion counts on component edges `eW ∈ Ico j0Len W.m`. -/
noncomputable def t3EcongPhi {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (mem : ℕ → ℕ) : ℕ :=
  ∑ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
    (mem (lay.econgCountAddr + eW) - mem (lay.wDelStampAddr + eW))

/-- Ghost state bundled across outer Task 3 rounds (`η_cur`). -/
structure T3OuterData where
  emb : ℕ → Option Walk
  getPathCnt : ℕ
  delCnt : ℕ
  econgUpd : ℕ
  hCur : ℕ

/-- Outer-loop state invariant holding before and after each Task 3 round (`η_cur`) for data `d`. -/
structure T3OuterAt {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (η_cur : ℕ) (d : T3OuterData)
    (st : State) (Φ : ℕ) : Prop where
  reg0 : st.regs 0 = inp.jAddr
  reg1 : st.regs 1 = inp.t1OutAddr
  reg2 : st.regs 2 = inp.v2
  staticMem : T3StaticMem ctx lay st.mem
  hCur_lo : lay.staticEnd ≤ d.hCur
  hCur_bd : d.hCur ≤ Task3Input.staticEndCap impl inp + 5 * inp.J.m +
    (η_cur * inp.J.m + d.getPathCnt + d.delCnt) * Task3Input.dsOneW impl inp.J +
    d.getPathCnt * (2 * impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J) + 3)
  zero_from : WordRAM.ZeroFrom st.mem d.hCur
  eta2_eq : st.mem (lay.base + t3OffEta2) = η_cur
  getPath_eq : st.mem (lay.base + t3OffGetPath) = d.getPathCnt
  del_eq : st.mem (lay.base + t3OffDel) = d.delCnt
  econgUpd_eq : st.mem (lay.base + t3OffEcongUpd) = d.econgUpd
  hCur_eq : st.mem (lay.base + t3OffHCur) = d.hCur
  cont_eq : st.mem (lay.base + t3OffCont) =
    if (unembeddedSet2Pure inp.J d.emb).Nonempty then 1 else 0
  emb_part : IsPartialEmbedding inp.J ctx.wd.W d.emb
  emb_j0_cov : ∀ eJ < inp.J.m,
    (ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.isLoop ∨
      ∃ eW, ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW) →
    (d.emb eJ).isSome = true
  emb_nodup : ∀ eJ < inp.J.m, ∀ P, d.emb eJ = some P → P.edges.Nodup
  emb_len_W : ∀ eJ < inp.J.m, (partialToWalk d.emb eJ).edges.length ≤
    impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J)
  emb_len_real : ∀ eJ < inp.J.m, ((partialToWalk d.emb eJ).edges.length : ℝ) ≤ ctx.wd.γ_ExpPath
  emb_mem : ∀ eJ < inp.J.m, match d.emb eJ with
    | none => st.mem (lay.embJWAddr + eJ) = 0
    | some P => lay.staticEnd ≤ st.mem (lay.embJWAddr + eJ) ∧
        st.mem (lay.embJWAddr + eJ) + P.encode.length ≤ d.hCur ∧
        WalkAt st.mem (st.mem (lay.embJWAddr + eJ)) P
  econg_cnt_eq : ∀ eW < ctx.wd.W.m,
    st.mem (lay.econgCountAddr + eW) =
      {eJ ∈ Finset.range inp.J.m | eW ∈ (partialToWalk d.emb eJ).edges}.card
  econg_le_round : ∀ eW < ctx.wd.W.m,
    econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk d.emb) eW ≤ ((η_cur : ℝ) + 1 / 2) * ctx.wd.τ₂
  econg_j0_le : ∀ eW < ctx.wd.j0Edges.length,
    econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk d.emb) eW ≤ ctx.wd.τ₂ / 2
  wdel_j0 : ∀ eW < ctx.wd.j0Edges.length, st.mem (lay.wDelStampAddr + eW) = 0
  wdel_comp : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
    st.mem (lay.wDelStampAddr + eW) ≤ η_cur ∧
    st.mem (lay.wDelStampAddr + eW) ≤ st.mem (lay.econgCountAddr + eW)
  vhat_stmp_le : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length), ∀ v < ctx.wd.comps[ci].W_sub.n,
    st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) ≤ η_cur
  getPath_cnt_le : d.getPathCnt ≤ inp.J.m - (unembeddedSet2Pure inp.J d.emb).card
  econgUpd_sum : d.econgUpd = ∑ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
    st.mem (lay.econgCountAddr + eW)
  econgUpd_bound : (d.econgUpd : ℝ) ≤ (d.getPathCnt : ℝ) * ctx.wd.γ_ExpPath
  econgUpd_W : d.econgUpd ≤ d.getPathCnt *
    impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J)
  del_le_econgUpd : d.delCnt ≤ d.econgUpd
  geom : 3 ^ η_cur * (unembeddedSet2Pure inp.J d.emb).card ≤ 2 ^ η_cur * inp.J.m
  phi_eq : Φ = (⌈impl.pathDS.params.K_del *
      (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander)
        (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 140) * t3EcongPhi ctx lay st.mem

/-- Prop-valued outer invariant for `task3Body`. -/
def T3OuterInv {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (η_cur : ℕ) (st : State) (Φ : ℕ) : Prop :=
  ∃ d : T3OuterData, T3OuterAt ctx lay η_cur d st Φ

/-! ## CPS sequencing helpers for straight-line Task 3 code -/

lemma t3_assign_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {s : Stmt} {mem regs : ℕ → ℕ} {pos v k T : ℕ} {Q : Outcome → State → ℕ → Prop}
    (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (hrest : ∃ o stF c_s Φ', Runs w p ω s ⟨mem, Function.update regs r v, pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k + e.size + 2) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq (.assign r e) s) ⟨mem, regs, pos⟩ o stF c_tot ∧
      Q o stF Φ' ∧ k + c_tot + Φ' ≤ T := by
  obtain ⟨o, stF, c_s, Φ', hr_s, hq, hc⟩ := hrest
  exact ⟨o, stF, (e.size + 1) + c_s + 1, Φ',
    runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, c_s,
      runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr_s, rfl⟩), hq, by omega⟩

lemma t3_store_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {ea ev : Expr}
    {s : Stmt} {mem regs : ℕ → ℕ} {pos addr v k T : ℕ} {Q : Outcome → State → ℕ → Prop}
    (ha : ea.eval w ⟨mem, regs, pos⟩ = some addr) (he : ev.eval w ⟨mem, regs, pos⟩ = some v)
    (hrest : ∃ o stF c_s Φ', Runs w p ω s ⟨Function.update mem addr v, regs, pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k + ea.size + ev.size + 2) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq (.store ea ev) s) ⟨mem, regs, pos⟩ o stF c_tot ∧
      Q o stF Φ' ∧ k + c_tot + Φ' ≤ T := by
  obtain ⟨o, stF, c_s, Φ', hr_s, hq, hc⟩ := hrest
  exact ⟨o, stF, (ea.size + ev.size + 1) + c_s + 1, Φ',
    runs_seq_iff.mpr (Or.inr ⟨_, ea.size + ev.size + 1, c_s,
      runs_store_iff.mpr ⟨addr, v, ha, he, rfl, rfl, rfl⟩, hr_s, rfl⟩), hq, by omega⟩

lemma t3_ld_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem regs : ℕ → ℕ} {pos rd rs off base v k T : ℕ} {s : Stmt}
    {Q : Outcome → State → ℕ → Prop}
    (hr : regs rs = base) (hoff : off < 2 ^ w) (hadd : base + off < 2 ^ w)
    (hm : mem (base + off) = v)
    (hrest : ∃ o stF c_s Φ', Runs w p ω s ⟨mem, Function.update regs rd v, pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k + (t3Ld (.reg rs) (.const off)).size + 2) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq (.assign rd (t3Ld (.reg rs) (.const off))) s)
      ⟨mem, regs, pos⟩ o stF c_tot ∧ Q o stF Φ' ∧ k + c_tot + Φ' ≤ T :=
  t3_assign_cps (hm ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr) (Expr.eval_const hoff) hadd)) hrest

lemma t3_st_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem regs : ℕ → ℕ} {pos rs off rv base val k T : ℕ} {s : Stmt}
    {Q : Outcome → State → ℕ → Prop}
    (hrs : regs rs = base) (hoff : off < 2 ^ w) (hadd : base + off < 2 ^ w)
    (hrv : regs rv = val)
    (hrest : ∃ o stF c_s Φ', Runs w p ω s ⟨Function.update mem (base + off) val, regs, pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k + (t3Add (.reg rs) (.const off)).size + (Expr.reg rv).size + 2) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq (t3St (.reg rs) (.const off) (.reg rv)) s)
      ⟨mem, regs, pos⟩ o stF c_tot ∧ Q o stF Φ' ∧ k + c_tot + Φ' ≤ T :=
  t3_store_cps (Expr.eval_add (Expr.eval_reg_of_eq hrs) (Expr.eval_const hoff) hadd)
    (Expr.eval_reg_of_eq hrv) hrest

lemma t3_const_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem regs : ℕ → ℕ} {pos r val k T : ℕ} {s : Stmt} {Q : Outcome → State → ℕ → Prop}
    (hv : val < 2 ^ w)
    (hrest : ∃ o stF c_s Φ', Runs w p ω s ⟨mem, Function.update regs r val, pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k + 3) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq (.assign r (.const val)) s) ⟨mem, regs, pos⟩ o stF c_tot ∧
      Q o stF Φ' ∧ k + c_tot + Φ' ≤ T :=
  t3_assign_cps (Expr.eval_const hv) (by simpa [Expr.size] using hrest)

lemma t3_st_const_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem regs : ℕ → ℕ} {pos rs off base val k T : ℕ} {s : Stmt}
    {Q : Outcome → State → ℕ → Prop}
    (hrs : regs rs = base) (hoff : off < 2 ^ w) (hadd : base + off < 2 ^ w) (hv : val < 2 ^ w)
    (hrest : ∃ o stF c_s Φ', Runs w p ω s ⟨Function.update mem (base + off) val, regs, pos⟩ o stF c_s ∧
      Q o stF Φ' ∧ (k + (t3Add (.reg rs) (.const off)).size + 3) + c_s + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq (t3St (.reg rs) (.const off) (.const val)) s)
      ⟨mem, regs, pos⟩ o stF c_tot ∧ Q o stF Φ' ∧ k + c_tot + Φ' ≤ T :=
  t3_store_cps (Expr.eval_add (Expr.eval_reg_of_eq hrs) (Expr.eval_const hoff) hadd)
    (Expr.eval_const hv) (by simpa [Expr.size] using hrest)

lemma t3_end_ret_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem regs : ℕ → ℕ} {pos : ℕ} {e : Expr} {v Φ' k T : ℕ}
    {Q : Outcome → State → ℕ → Prop}
    (hev : e.eval w ⟨mem, regs, pos⟩ = some v)
    (hq : Q (.returned v) ⟨mem, regs, pos⟩ Φ') (hk : k + e.size + 1 + Φ' ≤ T) :
    ∃ o stF c_tot Φ'', Runs w p ω (.ret e) ⟨mem, regs, pos⟩ o stF c_tot ∧
      Q o stF Φ'' ∧ k + c_tot + Φ'' ≤ T :=
  ⟨.returned v, ⟨mem, regs, pos⟩, e.size + 1, Φ',
    runs_ret_iff.mpr ⟨v, hev, rfl, rfl, rfl⟩, hq, by omega⟩

lemma t3_seq_stmt_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt}
    {st st₁ : State} {c₁ b₁ k T : ℕ} {Q : Outcome → State → ℕ → Prop}
    (h₁ : Runs w p ω s₁ st .normal st₁ c₁) (hle : c₁ ≤ b₁)
    (h₂ : ∃ o stF c₂ Φ', Runs w p ω s₂ st₁ o stF c₂ ∧ Q o stF Φ' ∧ (k + b₁ + 1) + c₂ + Φ' ≤ T) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq s₁ s₂) st o stF c_tot ∧ Q o stF Φ' ∧ k + c_tot + Φ' ≤ T := by
  obtain ⟨o, stF, c₂, Φ', hr₂, hq, hc⟩ := h₂
  exact ⟨o, stF, c₁ + c₂ + 1, Φ', runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, hr₂, rfl⟩), hq, by omega⟩

lemma t3_seq_pot_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt}
    {st st₁ : State} {c₁ b₁ Φ₀ Φ₁ k T : ℕ} {Q : Outcome → State → ℕ → Prop}
    (h₁ : Runs w p ω s₁ st .normal st₁ c₁) (hc₁ : c₁ + Φ₁ ≤ b₁ + Φ₀)
    (h₂ : ∃ o stF c₂ Φ', Runs w p ω s₂ st₁ o stF c₂ ∧ Q o stF Φ' ∧ (k + b₁ + 1) + c₂ + Φ' ≤ T + Φ₁) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq s₁ s₂) st o stF c_tot ∧ Q o stF Φ' ∧ k + c_tot + Φ' ≤ T + Φ₀ := by
  obtain ⟨o, stF, c₂, Φ', hr₂, hq, hc⟩ := h₂
  exact ⟨o, stF, c₁ + c₂ + 1, Φ', runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, hr₂, rfl⟩), hq, by omega⟩

lemma t3_ptriple_of_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt}
    {st : State} {cost Φ : ℕ} {Q : Outcome → State → ℕ → Prop}
    (h : ∃ o stF c_tot Φ', Runs w p ω s st o stF c_tot ∧ Q o stF Φ' ∧ 0 + c_tot + Φ' ≤ cost + Φ) :
    ∃ o st' c Φ', Runs w p ω s st o st' c ∧ Q o st' Φ' ∧ c + Φ' ≤ cost + Φ := by
  obtain ⟨o, stF, c_tot, Φ', hr, hq, hc⟩ := h
  exact ⟨o, stF, c_tot, Φ', hr, hq, by omega⟩

lemma t3_normal_ptriple_cps {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ : Stmt} {st : State} {b₁ Φ₀ k T : ℕ}
    {P : State → ℕ → Prop} {Inv : State → ℕ → Prop} {cost : State → ℕ}
    {Q : Outcome → State → ℕ → Prop}
    (ht : PTriple w p P s₁ (pNormalPost Inv) cost)
    (hp : P st Φ₀) (hc : cost st ≤ b₁)
    (hrest : ∀ st₁ Φ₁, Inv st₁ Φ₁ → ∃ o stF c₂ Φ',
      Runs w p ω s₂ st₁ o stF c₂ ∧ Q o stF Φ' ∧ (k + b₁ + 1) + c₂ + Φ' ≤ T + Φ₁) :
    ∃ o stF c_tot Φ', Runs w p ω (.seq s₁ s₂) st o stF c_tot ∧
      Q o stF Φ' ∧ k + c_tot + Φ' ≤ T + Φ₀ := by
  obtain ⟨o₁, st₁, c₁, Φ₁, hr₁, hq₁, hc₁⟩ := ht st Φ₀ ω hp
  cases o₁ with
  | returned _ => exact False.elim hq₁
  | normal =>
    obtain ⟨o, stF, c₂, Φ', hr₂, hq, hc₂⟩ := hrest st₁ Φ₁ hq₁
    exact ⟨o, stF, c₁ + c₂ + 1, Φ',
      runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), hq, by omega⟩

end MinCostFlow.Spanner
