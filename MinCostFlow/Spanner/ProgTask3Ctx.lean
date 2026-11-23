module

public import MinCostFlow.Spanner.ProgTask3
public import MinCostFlow.Spanner.ProgTask2Ctx
public import MinCostFlow.Spanner.ProgTask3RoundMath

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# Context and Scalar Bounds for Word-RAM Task 3

Unpacks `Task3Input.Valid` into `T3Ctx`, defines `vhatBaseW` (the prefix-sum base offset into
`vhatStamp` indexed by `W_sub.n`), and proves `T3Ctx.hds_bounds` bounding all Task 3 PathDS
space, word-width, and scalar parameters against the Task 3/Task 1 caps.
-/

/-- Prefix-sum base index in `vhatStamp` for component `ci` using `W_sub.n`. -/
def vhatBaseW (wd : WitnessData) (ci : ℕ) : ℕ :=
  ((wd.comps.take ci).map fun c => c.W_sub.n).sum

lemma vhatBaseW_mono {wd : WitnessData} {ci₁ ci₂ : ℕ} (h : ci₁ ≤ ci₂) :
    vhatBaseW wd ci₁ ≤ vhatBaseW wd ci₂ := by
  have h1 : wd.comps.take ci₁ <+: wd.comps.take ci₂ :=
    List.take_prefix_take_left h
  rcases h1 with ⟨rest, hEq⟩
  dsimp only [vhatBaseW]
  rw [← hEq, List.map_append, List.sum_append]
  omega

lemma vhatBaseW_add_le {wd : WitnessData} {ci : ℕ} (hci : ci < wd.comps.length) :
    vhatBaseW wd ci + wd.comps[ci].W_sub.n = vhatBaseW wd (ci + 1) := by
  dsimp only [vhatBaseW]
  rw [List.take_add_one, List.getElem?_eq_getElem hci, Option.toList_some,
    List.map_append, List.sum_append]
  simp

lemma vhatBaseW_le_sum {wd : WitnessData} {ci : ℕ} :
    vhatBaseW wd ci ≤ (wd.comps.map fun c => c.W_sub.n).sum := by
  have h1 : wd.comps.take ci <+: wd.comps := List.take_prefix _ _
  rcases h1 with ⟨rest, hEq⟩
  dsimp only [vhatBaseW]
  conv_rhs => rw [← hEq, List.map_append, List.sum_append]
  omega

lemma vhatBaseW_inj {wd : WitnessData} {ci₁ ci₂ v₁ v₂ : ℕ}
    (h1 : ci₁ < wd.comps.length) (h2 : ci₂ < wd.comps.length)
    (hv1 : v₁ < wd.comps[ci₁].W_sub.n) (hv2 : v₂ < wd.comps[ci₂].W_sub.n)
    (heq : vhatBaseW wd ci₁ + v₁ = vhatBaseW wd ci₂ + v₂) :
    ci₁ = ci₂ ∧ v₁ = v₂ := by
  by_cases hlt : ci₁ = ci₂
  · subst hlt; exact ⟨rfl, by omega⟩
  · exfalso
    rcases Nat.lt_or_gt_of_ne hlt with h | h
    · have ha := vhatBaseW_add_le h1
      have hm := vhatBaseW_mono (wd := wd) (show ci₁ + 1 ≤ ci₂ by omega)
      omega
    · have ha := vhatBaseW_add_le h2
      have hm := vhatBaseW_mono (wd := wd) (show ci₂ + 1 ≤ ci₁ by omega)
      omega

/-- Unpacked immutable context for a valid Word-RAM Task 3 invocation. -/
structure T3Ctx (impl : SpannerToolImpl) (inp : Task3Input) (mem₀ : ℕ → ℕ) (w : ℕ) where
  wInp : WitnessCoreInput
  WSubs : List Graph
  memPre : ℕ → ℕ
  memT1 : ℕ → ℕ
  v1 : ℕ
  hT1Agr : ∀ x < v1, mem₀ x = memT1 x
  hv1_le : v1 ≤ inp.v2
  hz2 : ZeroFrom mem₀ inp.v2
  hJvalid : inp.J.IsValid
  hJ_at : GraphAt mem₀ inp.jAddr inp.J
  hJ_lt_t1 : inp.jAddr + inp.J.encode.length ≤ inp.t1OutAddr
  hT1 : Task1OutAt impl inp.jAddr inp.t1OutAddr inp.H' inp.J inp.embJH memPre memT1 v1 w
  hwokW : Task3Input.WordWidthOK impl inp w
  hWInpH' : wInp.H' = inp.H'
  hWInpEmb : ∀ e < inp.J.m, wInp.embJH e = inp.embJH e
  hWInpJ : wInp.prep.J = inp.J
  hWInpJAddr : wInp.prep.jAddr = inp.jAddr
  hStatsAddr : wInp.statsAddr = inp.t1OutAddr + 6
  hJ0Addr : wInp.prep.j0Addr = inp.t1OutAddr + 6 + 3 + inp.J.n + 2 * inp.H'.n
  hNlAddr : wInp.prep.nlAddr = wInp.prep.j0Addr + 2 + 2 * inp.J.m
  hDecAddr : wInp.prep.decAddr = wInp.prep.nlAddr + wInp.prep.J0_strip.m
  hCell : wInp.prep.c_ℓ = impl.decompose.c_ℓ
  hT1MemAgr : ∀ x < inp.t1OutAddr, memT1 x = memPre x
  hT1Zf : ZeroFrom memT1 v1
  hv1_lo : wInp.h + 20 ≤ v1
  hv1_hi : v1 ≤ wInp.maxHeapEnd impl.constructExpander impl.pathDS.params
  hSlot0 : memT1 inp.t1OutAddr = wInp.statsAddr
  hSlot1 : memT1 (inp.t1OutAddr + 1) = wInp.prep.j0Addr
  hSlot2 : memT1 (inp.t1OutAddr + 2) = wInp.prep.nlAddr
  hSlot3 : memT1 (inp.t1OutAddr + 3) = wInp.prep.decAddr
  hSlot4 : memT1 (inp.t1OutAddr + 4) = wInp.prep.h
  hSlot5 : memT1 (inp.t1OutAddr + 5) = wInp.h
  hMaxDeg : memT1 wInp.statsAddr = maxDeg inp.J
  hLenJH : memT1 (wInp.statsAddr + 1) = length inp.J inp.embJH
  hVcong : memT1 (wInp.statsAddr + 2) = vcongNat inp.J inp.H' inp.embJH
  hPrepSt : PrepStaticState wInp.prep memT1 memT1
  hCompsDone : CompsDoneUpTo wInp.prep memT1 wInp.prep.rawComps.length
  hStat : wInp.prep.StaticValid memT1 w
  hws : wInp.ValidWSubs impl.constructExpander WSubs
  hφ_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤ ↑wInp.prep.phiNum_dec / ↑wInp.prep.phiDen_dec
  hφ_max : wInp.prep.phiDen_dec ≤ impl.decompose.maxPhiDen wInp.prep.J0_strip.m
  hOut : ∀ (mp : ℕ → ℕ), wInp.OutputAt impl.constructExpander impl.pathDS.params
    (fun x => if x < wInp.h then memT1 x else mp x) memT1 v1
    (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs)
  hw_ok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
    WitnessOK tools inp.H' inp.J inp.embJH (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs)
  hPrepEnd : wInp.prep.hEnd ≤ wInp.h

/-- Extract `T3Ctx` cleanly from `Task3Input.Valid` via `Classical.choose`. -/
noncomputable def t3CtxOfValid {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid impl mem₀ w) : T3Ctx impl inp mem₀ w :=
  let hExPre := hv.2.2.2.1
  let memPre := Classical.choose hExPre
  let hExT1 := Classical.choose_spec hExPre
  let memT1 := Classical.choose hExT1
  let hExV1 := Classical.choose_spec hExT1
  let v1 := Classical.choose hExV1
  let hBlock := Classical.choose_spec hExV1
  let hT1 := hBlock.2.2.2
  let wInp := Classical.choose hT1
  let hExWSubs := Classical.choose_spec hT1
  let WSubs := Classical.choose hExWSubs
  let hp := Classical.choose_spec hExWSubs
  { wInp := wInp
    WSubs := WSubs
    memPre := memPre
    memT1 := memT1
    v1 := v1
    hT1Agr := hBlock.1
    hv1_le := hBlock.2.1
    hz2 := hBlock.2.2.1
    hJvalid := hv.1
    hJ_at := hv.2.1
    hJ_lt_t1 := hv.2.2.1
    hT1 := hT1
    hwokW := hv.2.2.2.2
    hWInpH' := hp.1
    hWInpEmb := hp.2.1
    hWInpJ := hp.2.2.1
    hWInpJAddr := hp.2.2.2.1
    hStatsAddr := hp.2.2.2.2.1
    hJ0Addr := hp.2.2.2.2.2.1
    hNlAddr := hp.2.2.2.2.2.2.1
    hDecAddr := hp.2.2.2.2.2.2.2.1
    hCell := hp.2.2.2.2.2.2.2.2.1
    hT1MemAgr := hp.2.2.2.2.2.2.2.2.2.1
    hT1Zf := hp.2.2.2.2.2.2.2.2.2.2.1
    hv1_lo := hp.2.2.2.2.2.2.2.2.2.2.2.1
    hv1_hi := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
    hSlot0 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hSlot1 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hSlot2 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hSlot3 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hSlot4 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hSlot5 := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hMaxDeg := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hLenJH := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hVcong := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hPrepSt := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hCompsDone := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hStat := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hws := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hφ_lb := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hφ_max := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hOut := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hw_ok := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hPrepEnd := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 }

namespace T3Ctx

noncomputable def wd {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) : WitnessData :=
  ctx.wInp.mkWitnessData impl.constructExpander impl.pathDS.params ctx.WSubs

lemma hw_okW {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) :
    WitnessOK (exists_localSpannerTools 0 0).some ctx.wInp.H' ctx.wInp.prep.J ctx.wInp.embJH ctx.wd := by
  have h := ctx.hw_ok (exists_localSpannerTools 0 0).some
  rw [ctx.hWInpH', ctx.hWInpJ]
  rcases h with ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22⟩
  exact ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22⟩

lemma hmW_le {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) : ctx.wd.W.m ≤ Task1Input.mwCap impl inp.J :=
  ctx.hWInpJ ▸ task2_wd_W_m_le_mwCap ctx.hStat ctx.hw_okW ctx.hws ctx.hφ_lb

lemma hmw_int_le {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) :
    ctx.wInp.mwInt impl.constructExpander ≤ Task1Input.mwCap impl inp.J :=
  ctx.hWInpJ ▸ task2_mw_le_cap ctx.hStat ctx.hφ_lb

lemma hK_le {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) : ctx.wd.comps.length ≤ inp.J.m :=
  ctx.hWInpJ ▸ t2_comps_len_le_J ctx.hStat ctx.hw_okW ctx.hws

private lemma list_sum_map_eq {α : Type*} {l : List α} {f g : α → ℕ}
    (h : ∀ (i : ℕ) (hi : i < l.length), f l[i] = g l[i]) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [h0, ih (fun i hi => h (i + 1) (by simp; omega))]

private lemma list_length_le_sum_map {α : Type*} {l : List α} {f : α → ℕ}
    (h : ∀ (i : ℕ) (hi : i < l.length), 1 ≤ f l[i]) : l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    have ih' := ih (fun i hi => h (i + 1) (by simp; omega))
    omega

lemma hK_le_Wm {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) : ctx.wd.comps.length ≤ ctx.wd.W.m := by
  have h := ctx.hw_okW.W_m_eq
  have hm : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length), 1 ≤ ctx.wd.comps[ci].W_sub.m :=
    fun ci hci => (ctx.hw_okW.comp_props ci hci).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h1 := list_length_le_sum_map (l := ctx.wd.comps) (f := fun (c : CompInfo) => c.W_sub.m) hm
  omega

lemma hvhatSum_le {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) : (ctx.wd.comps.map fun c => c.W_sub.n).sum ≤ 2 * inp.J.m := by
  have h1 := t2_vhatSum_le ctx.hStat ctx.hw_okW ctx.hws
  have hc : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length),
      ctx.wd.comps[ci].W_sub.n = ctx.wd.comps[ci].J_sub.n := by
    intro ci hci
    have hp := ctx.hw_okW.comp_props ci hci
    rw [hp.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.1]
  have h2 : (ctx.wd.comps.map fun c => c.W_sub.n).sum = (ctx.wd.comps.map fun c => c.J_sub.n).sum :=
    list_sum_map_eq hc
  rw [h2, ← ctx.hWInpJ]
  exact h1

lemma hsum_Wm_le {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) :
    (ctx.wd.comps.map fun c => c.W_sub.m).sum ≤ Task1Input.mwCap impl inp.J := by
  have heq := ctx.hw_okW.W_m_eq
  have hm := ctx.hmW_le
  omega

lemma htau2_le_cap {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) :
    ctx.wInp.tau2Int impl.constructExpander impl.pathDS.params ≤ Task1Input.tau2Cap impl inp.J := by
  have hsc := ctx.hWInpJ ▸ task2_scalars_le_caps ctx.hStat ctx.hφ_lb
  unfold WitnessCoreInput.tau2Int Task1Input.tau2Cap
  have h1 : ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params ≤ Task1Input.gammaExpCap impl inp.J := by
    change _ ≤ Task2Input.gammaExpCap impl inp.J
    exact hsc.1
  have h2 : ctx.wInp.γDelInt impl.constructExpander impl.pathDS.params ≤ Task1Input.gammaDelCap impl inp.J := hsc.2.1
  have h3 : ctx.wInp.phiDsDenInt impl.constructExpander impl.pathDS.params ≤ Task1Input.phiDsDenCap impl inp.J := hsc.2.2
  exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

lemma hds_bounds {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) :
    let wd := ctx.wd
    let ce := impl.constructExpander
    let p := impl.pathDS.params
    let mw := Task1Input.mwCap impl inp.J
    let dW := WitnessCoreInput.dWInt ce
    let γW := p.gExp dW mw
    let γWq := p.gQuery dW mw
    let dsOne := Task3Input.dsOneW impl inp.J
    (∀ (ci : ℕ) (hci : ci < wd.comps.length),
      let c := wd.comps[ci]
      p.initSpace ce.phiNum ce.phiDen c.W_sub.n c.W_sub.m wd.M_W ≤ dsOne ∧
      p.delSpace ce.phiNum ce.phiDen c.W_sub.n c.W_sub.m wd.M_W ≤ dsOne ∧
      p.querySpace ce.phiNum ce.phiDen c.W_sub.n c.W_sub.m wd.M_W ≤ dsOne ∧
      p.cw * (Nat.log 2 (c.W_sub.n + c.W_sub.m + ce.phiDen + wd.M_W +
        ⌈p.γ_ExpPath wd.φ_Const wd.M_W⌉₊ + 2) + 1) ≤ w ∧
      ⌈p.K_init * ↑c.W_sub.m * p.γ_ExpPath wd.φ_Const wd.M_W⌉₊ ≤ c.W_sub.m * ⌈p.K_init * ↑γW⌉₊) ∧
    ⌈p.K_del * p.γ_query wd.φ_Const wd.M_W⌉₊ ≤ ⌈p.K_del * ↑γWq⌉₊ ∧
    ⌈p.K_query * p.γ_query wd.φ_Const wd.M_W⌉₊ ≤ ⌈p.K_query * ↑γWq⌉₊ ∧
    ⌈p.γ_ExpPath wd.φ_Const wd.M_W⌉₊ ≤ γW ∧
    p.γ_ExpPath wd.φ_Const wd.M_W ≤ wd.γ_ExpPath ∧
    wd.M_W ≤ mw ∧
    (ctx.wInp.tau2Int ce p : ℝ) = wd.τ₂ := by
  intro wd ce p mw dW γW γWq dsOne
  have hsc := ctx.wInp.mkWitnessData_scalars ce p ctx.WSubs ctx.hStat
  have hMW_eq : wd.M_W = ctx.wInp.mwInt ce := hsc.1
  have hMW_le : wd.M_W ≤ mw := hMW_eq ▸ ctx.hmw_int_le
  have hdW_pos : 1 ≤ dW := Nat.div_pos (by have := ce.hphi_pos; have := ce.hphi_le; omega) ce.hphi_pos
  have hdW_eq : ⌈1 / wd.φ_Const⌉₊ = dW := (WitnessCoreInput.dWInt_eq ce).symm
  have hγW_eq : p.γ_ExpPath wd.φ_Const wd.M_W = ↑(p.gExp dW wd.M_W) := by
    unfold PathDSParams.γ_ExpPath; rw [hdW_eq]
  have hγ_mono : p.gExp dW wd.M_W ≤ γW := p.hgExp_mono hdW_pos le_rfl hMW_le
  have hceilγ : ⌈p.γ_ExpPath wd.φ_Const wd.M_W⌉₊ ≤ γW := by
    rw [hγW_eq, Nat.ceil_natCast]; exact hγ_mono
  have hγ_le_wd : p.γ_ExpPath wd.φ_Const wd.M_W ≤ wd.γ_ExpPath := by
    rw [hγW_eq]
    have hge : ctx.wd.γ_ExpPath = ↑(ctx.wInp.γExpInt ce p) := hsc.2.2.1
    change ↑(p.gExp dW wd.M_W) ≤ ctx.wd.γ_ExpPath
    rw [hge]
    unfold WitnessCoreInput.γExpInt
    rw [← hMW_eq]
    exact_mod_cast le_max_right _ _
  have hγWq_le : p.γ_query wd.φ_Const wd.M_W ≤ ↑γWq := by
    unfold PathDSParams.γ_query; rw [hdW_eq]
    exact_mod_cast p.hgQuery_mono hdW_pos le_rfl hMW_le
  have hKdel : ⌈p.K_del * p.γ_query wd.φ_Const wd.M_W⌉₊ ≤ ⌈p.K_del * ↑γWq⌉₊ :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_left hγWq_le p.hK_del)
  have hKquery : ⌈p.K_query * p.γ_query wd.φ_Const wd.M_W⌉₊ ≤ ⌈p.K_query * ↑γWq⌉₊ :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_left hγWq_le p.hK_query)
  refine ⟨fun ci hci => ?_, hKdel, hKquery, hceilγ, hγ_le_wd, hMW_le, hsc.2.2.2.2.1.symm⟩
  set c := wd.comps[ci]
  have hcprops := ctx.hw_okW.comp_props ci hci
  have hcWn : c.W_sub.n = c.X.card := hcprops.2.2.2.2.2.2.2.2.2.2.2.1
  have hcWval : c.W_sub.IsValid := hcprops.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcWm_le : c.W_sub.m ≤ wd.M_W := hcprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcWdeg : ∀ k < c.X.card, 1 ≤ c.W_sub.deg k := hcprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcWn_le_2m : c.W_sub.n ≤ 2 * c.W_sub.m := by
    have hvol := vol_verts_eq_two_mul_m hcWval
    have h1 : c.W_sub.n ≤ ∑ k ∈ Finset.range c.W_sub.n, c.W_sub.deg k := by
      calc c.W_sub.n = ∑ _ ∈ Finset.range c.W_sub.n, 1 := by simp
        _ ≤ ∑ k ∈ Finset.range c.W_sub.n, c.W_sub.deg k :=
            Finset.sum_le_sum fun k hk => hcWdeg k (hcWn ▸ Finset.mem_range.mp hk)
    have h2 : ∑ k ∈ Finset.range c.W_sub.n, c.W_sub.deg k = c.W_sub.vol c.W_sub.verts := by
      unfold Graph.vol Graph.volIn Graph.deg Graph.verts; rfl
    omega
  have hcWn_2mw : c.W_sub.n ≤ 2 * mw := by omega
  have hcWm_mw : c.W_sub.m ≤ mw := by omega
  have hsum_le : ce.phiDen + c.W_sub.n + c.W_sub.m + wd.M_W + p.gExp dW wd.M_W + 2 ≤
      ce.phiDen + 4 * mw + γW + 2 := by omega
  have hdW_ce : (ce.phiDen + ce.phiNum - 1) / ce.phiNum = dW := rfl
  have hsum_le' : ce.phiDen + c.W_sub.n + c.W_sub.m + wd.M_W +
      p.gExp ((ce.phiDen + ce.phiNum - 1) / ce.phiNum) wd.M_W + 2 ≤ ce.phiDen + 4 * mw + γW + 2 := by
    rw [hdW_ce]; exact hsum_le
  have hinit : p.initSpace ce.phiNum ce.phiDen c.W_sub.n c.W_sub.m wd.M_W ≤ dsOne :=
    (p.hinitSpace_le ce.phiNum ce.phiDen c.W_sub.n c.W_sub.m wd.M_W ce.hphi_pos ce.hphi_le).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum_le' _))
  have hdel : p.delSpace ce.phiNum ce.phiDen c.W_sub.n c.W_sub.m wd.M_W ≤ dsOne :=
    (p.hdelSpace_le ce.phiNum ce.phiDen c.W_sub.n c.W_sub.m wd.M_W ce.hphi_pos ce.hphi_le).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum_le' _))
  have hq : p.querySpace ce.phiNum ce.phiDen c.W_sub.n c.W_sub.m wd.M_W ≤ dsOne :=
    (p.hquerySpace_le ce.phiNum ce.phiDen c.W_sub.n c.W_sub.m wd.M_W ce.hphi_pos ce.hphi_le).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum_le' _))
  have hlog : Nat.log 2 (c.W_sub.n + c.W_sub.m + ce.phiDen + wd.M_W +
      ⌈p.γ_ExpPath wd.φ_Const wd.M_W⌉₊ + 2) ≤
      Nat.log 2 (ce.phiDen + 4 * mw + γW + 2) :=
    Nat.log_mono_right (by omega)
  have hcw : p.cw * (Nat.log 2 (c.W_sub.n + c.W_sub.m + ce.phiDen + wd.M_W +
      ⌈p.γ_ExpPath wd.φ_Const wd.M_W⌉₊ + 2) + 1) ≤ w :=
    le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1)) ctx.hwokW.2.1
  have hki : ⌈p.K_init * ↑c.W_sub.m * p.γ_ExpPath wd.φ_Const wd.M_W⌉₊ ≤ c.W_sub.m * ⌈p.K_init * ↑γW⌉₊ := by
    refine Nat.ceil_le.mpr ?_
    have h1 : p.K_init * p.γ_ExpPath wd.φ_Const wd.M_W ≤ ↑⌈p.K_init * ↑γW⌉₊ := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ p.hK_init) (Nat.le_ceil _)
      rw [hγW_eq]; exact_mod_cast hγ_mono
    calc p.K_init * ↑c.W_sub.m * p.γ_ExpPath wd.φ_Const wd.M_W
        = ↑c.W_sub.m * (p.K_init * p.γ_ExpPath wd.φ_Const wd.M_W) := by ring
      _ ≤ ↑c.W_sub.m * ↑⌈p.K_init * ↑γW⌉₊ := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = ↑(c.W_sub.m * ⌈p.K_init * ↑γW⌉₊) := by push_cast; ring
  exact ⟨hinit, hdel, hq, hcw, hki⟩

end T3Ctx

end MinCostFlow.Spanner