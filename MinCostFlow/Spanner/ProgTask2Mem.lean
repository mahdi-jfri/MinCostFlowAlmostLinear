module

public import MinCostFlow.Spanner.ProgTask2
public import MinCostFlow.Spanner.ProgTask2RoundMath
public import MinCostFlow.Spanner.ProgWordRAMPot

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Task 2 address, DS space/cost, incidence list, and multi-DS invariants -/

lemma t2_comps_len_le_J {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs) :
    (inp.mkWitnessData ce pds WSubs).comps.length ≤ inp.prep.J.m := by
  have h1 : (inp.mkWitnessData ce pds WSubs).comps.length ≤
      ((inp.mkWitnessData ce pds WSubs).comps.map fun c => c.J_sub.m).sum := by
    have haux : ∀ n, n ≤ (inp.mkWitnessData ce pds WSubs).comps.length →
        n ≤ (((inp.mkWitnessData ce pds WSubs).comps.take n).map fun c => c.J_sub.m).sum := by
      intro n hn
      induction n with
      | zero => simp
      | succ k ih =>
        have hk : k < (inp.mkWitnessData ce pds WSubs).comps.length := by omega
        have hpos : 1 ≤ (inp.mkWitnessData ce pds WSubs).comps[k].J_sub.m :=
          (hok.comp_props k hk).2.2.2.2.2.2.2.1
        rw [List.take_add_one, List.getElem?_eq_getElem hk]
        simp only [Option.toList_some, List.map_append, List.map_singleton, List.sum_append,
          List.sum_singleton]
        have := ih (by omega)
        omega
    simpa using haux (inp.mkWitnessData ce pds WSubs).comps.length (le_refl _)
  exact le_trans h1 (le_trans (Nat.le_add_left _ _) (mkW_sum_comp_j_m_le_J hs hok hws))

lemma t2_vhatSum_le {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some inp.H' inp.prep.J inp.embJH
      (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs) :
    ((inp.mkWitnessData ce pds WSubs).comps.map fun c => c.J_sub.n).sum ≤ 2 * inp.prep.J.m := by
  have h1 : ((inp.mkWitnessData ce pds WSubs).comps.map fun c => c.J_sub.n).sum ≤
      2 * ((inp.mkWitnessData ce pds WSubs).comps.map fun c => c.J_sub.m).sum := by
    have haux : ∀ n, n ≤ (inp.mkWitnessData ce pds WSubs).comps.length →
        (((inp.mkWitnessData ce pds WSubs).comps.take n).map fun c => c.J_sub.n).sum ≤
          2 * (((inp.mkWitnessData ce pds WSubs).comps.take n).map fun c => c.J_sub.m).sum := by
      intro n hn
      induction n with
      | zero => simp
      | succ k ih =>
        have hk : k < (inp.mkWitnessData ce pds WSubs).comps.length := by omega
        have hprops := hok.comp_props k hk
        set c := (inp.mkWitnessData ce pds WSubs).comps[k]
        have hJn : c.J_sub.n = c.X.card := hprops.2.2.2.2.2.1
        have hJvalid : c.J_sub.IsValid := hprops.2.2.2.2.2.2.1
        have hdeg : ∀ v < c.X.card, 1 ≤ c.J_sub.deg v := hprops.2.2.2.2.2.2.2.2.2.1
        have h2m : c.J_sub.n ≤ 2 * c.J_sub.m := by
          have hvol := vol_verts_eq_two_mul_m hJvalid
          have hsum_ge : c.X.card ≤ ∑ v ∈ Finset.range c.X.card, c.J_sub.deg v := by
            calc c.X.card = ∑ _v ∈ Finset.range c.X.card, 1 := by simp
              _ ≤ ∑ v ∈ Finset.range c.X.card, c.J_sub.deg v :=
                  Finset.sum_le_sum fun v hv => hdeg v (Finset.mem_range.mp hv)
          have hsum_eq : ∑ v ∈ Finset.range c.X.card, c.J_sub.deg v = 2 * c.J_sub.m := by
            rw [← hvol]; unfold Graph.vol Graph.volIn Graph.deg; rw [Graph.verts, hJn]
          omega
        rw [List.take_add_one, List.getElem?_eq_getElem hk]
        simp only [Option.toList_some, List.map_append, List.map_singleton, List.sum_append,
          List.sum_singleton]
        have := ih (by omega)
        dsimp only [c] at h2m
        omega
    simpa using haux (inp.mkWitnessData ce pds WSubs).comps.length (le_refl _)
  have h2 := le_trans (Nat.le_add_left _ _) (mkW_sum_comp_j_m_le_J hs hok hws)
  omega

def compEdgeBase (wd : WitnessData) (ci : ℕ) : ℕ :=
  ((wd.comps.take ci).map fun c => c.J_sub.m).sum

def vhatBase (wd : WitnessData) (ci : ℕ) : ℕ :=
  ((wd.comps.take ci).map fun c => c.J_sub.n).sum

lemma compEdgeBase_mono {wd : WitnessData} {ci₁ ci₂ : ℕ} (h : ci₁ ≤ ci₂) :
    compEdgeBase wd ci₁ ≤ compEdgeBase wd ci₂ := by
  unfold compEdgeBase
  have hsplit : wd.comps.take ci₂ = wd.comps.take ci₁ ++ (wd.comps.drop ci₁).take (ci₂ - ci₁) := by
    conv_lhs => rw [show ci₂ = ci₁ + (ci₂ - ci₁) by omega, List.take_add]
  rw [hsplit, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

lemma compEdgeBase_add_le {wd : WitnessData} {ci : ℕ} (hci : ci < wd.comps.length) :
    compEdgeBase wd ci + wd.comps[ci].J_sub.m = compEdgeBase wd (ci + 1) := by
  unfold compEdgeBase
  rw [List.take_add_one, List.getElem?_eq_getElem hci, Option.toList_some,
    List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]

lemma compEdgeBase_le_sum {wd : WitnessData} {ci : ℕ} (hci : ci ≤ wd.comps.length) :
    compEdgeBase wd ci ≤ (wd.comps.map fun c => c.J_sub.m).sum := by
  have := compEdgeBase_mono (wd := wd) hci
  simpa [compEdgeBase] using this

lemma compEdgeBase_inj {wd : WitnessData} {ci₁ ci₂ b₁ b₂ : ℕ}
    (hc₁ : ci₁ < wd.comps.length) (hc₂ : ci₂ < wd.comps.length)
    (hb₁ : b₁ < wd.comps[ci₁].J_sub.m) (hb₂ : b₂ < wd.comps[ci₂].J_sub.m)
    (heq : compEdgeBase wd ci₁ + b₁ = compEdgeBase wd ci₂ + b₂) :
    ci₁ = ci₂ ∧ b₁ = b₂ := by
  rcases Nat.lt_trichotomy ci₁ ci₂ with hlt | rfl | hgt
  · have h1 := compEdgeBase_add_le hc₁
    have h2 := compEdgeBase_mono (wd := wd) (show ci₁ + 1 ≤ ci₂ by omega)
    omega
  · exact ⟨rfl, by omega⟩
  · have h1 := compEdgeBase_add_le hc₂
    have h2 := compEdgeBase_mono (wd := wd) (show ci₂ + 1 ≤ ci₁ by omega)
    omega

lemma vhatBase_mono {wd : WitnessData} {ci₁ ci₂ : ℕ} (h : ci₁ ≤ ci₂) :
    vhatBase wd ci₁ ≤ vhatBase wd ci₂ := by
  unfold vhatBase
  have hsplit : wd.comps.take ci₂ = wd.comps.take ci₁ ++ (wd.comps.drop ci₁).take (ci₂ - ci₁) := by
    conv_lhs => rw [show ci₂ = ci₁ + (ci₂ - ci₁) by omega, List.take_add]
  rw [hsplit, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

lemma vhatBase_add_le {wd : WitnessData} {ci : ℕ} (hci : ci < wd.comps.length) :
    vhatBase wd ci + wd.comps[ci].J_sub.n = vhatBase wd (ci + 1) := by
  unfold vhatBase
  rw [List.take_add_one, List.getElem?_eq_getElem hci, Option.toList_some,
    List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]

lemma vhatBase_le_sum {wd : WitnessData} {ci : ℕ} (hci : ci ≤ wd.comps.length) :
    vhatBase wd ci ≤ (wd.comps.map fun c => c.J_sub.n).sum := by
  have := vhatBase_mono (wd := wd) hci
  simpa [vhatBase] using this

lemma vhatBase_inj {wd : WitnessData} {ci₁ ci₂ v₁ v₂ : ℕ}
    (hc₁ : ci₁ < wd.comps.length) (hc₂ : ci₂ < wd.comps.length)
    (hv₁ : v₁ < wd.comps[ci₁].J_sub.n) (hv₂ : v₂ < wd.comps[ci₂].J_sub.n)
    (heq : vhatBase wd ci₁ + v₁ = vhatBase wd ci₂ + v₂) :
    ci₁ = ci₂ ∧ v₁ = v₂ := by
  rcases Nat.lt_trichotomy ci₁ ci₂ with hlt | rfl | hgt
  · have h1 := vhatBase_add_le hc₁
    have h2 := vhatBase_mono (wd := wd) (show ci₁ + 1 ≤ ci₂ by omega)
    omega
  · exact ⟨rfl, by omega⟩
  · have h1 := vhatBase_add_le hc₂
    have h2 := vhatBase_mono (wd := wd) (show ci₂ + 1 ≤ ci₁ by omega)
    omega

noncomputable def t2DsOne (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  let m0 := (stripLoops J).m
  let pdCap := Task1Input.phiDenCap impl J
  let dJ := Task1Input.dJCap impl J
  impl.pathDS.params.C_space * (pdCap + J.n + m0 + m0 + impl.pathDS.params.gExp dJ m0 + 2) ^
    impl.pathDS.params.c_space

lemma t2_ds_bounds {impl : SpannerToolImpl} {t2i : Task2Input} {wInp : WitnessCoreInput}
    {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hJ_eq : wInp.prep.J = t2i.J)
    (hs : wInp.prep.StaticValid mem w)
    (hok : WitnessOK (exists_localSpannerTools 0 0).some wInp.H' wInp.prep.J wInp.embJH
      (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs))
    (hφ_cap : wInp.prep.phiDen_dec ≤ impl.decompose.maxPhiDen wInp.prep.J0_strip.m)
    (hφ_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤
      (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec)
    (hww : t2i.WordWidthOK impl w) :
    let wd := wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs
    let p := impl.pathDS.params
    let dsOne := t2DsOne impl t2i.J
    let dJ := Task1Input.dJCap impl t2i.J
    let m0 := (stripLoops t2i.J).m
    let γJ := p.gExp dJ m0
    let γJq := p.gQuery dJ m0
    (∀ ci (hci : ci < wd.comps.length),
      let c := wd.comps[ci]
      p.initSpace wInp.prep.phiNum_dec wInp.prep.phiDen_dec c.J_sub.n c.J_sub.m wd.J0_strip.m ≤ dsOne ∧
      p.delSpace wInp.prep.phiNum_dec wInp.prep.phiDen_dec c.J_sub.n c.J_sub.m wd.J0_strip.m ≤ dsOne ∧
      p.querySpace wInp.prep.phiNum_dec wInp.prep.phiDen_dec c.J_sub.n c.J_sub.m wd.J0_strip.m ≤ dsOne ∧
      p.cw * (Nat.log 2 (c.J_sub.n + c.J_sub.m + wInp.prep.phiDen_dec + wd.J0_strip.m +
        ⌈p.γ_ExpPath wd.φ_dec wd.J0_strip.m⌉₊ + 2) + 1) ≤ w ∧
      ⌈p.K_init * ↑c.J_sub.m * p.γ_ExpPath wd.φ_dec wd.J0_strip.m⌉₊ ≤ c.J_sub.m * ⌈p.K_init * ↑γJ⌉₊) ∧
    ⌈p.K_del * p.γ_query wd.φ_dec wd.J0_strip.m⌉₊ ≤ ⌈p.K_del * ↑γJq⌉₊ ∧
    ⌈p.K_query * p.γ_query wd.φ_dec wd.J0_strip.m⌉₊ ≤ ⌈p.K_query * ↑γJq⌉₊ ∧
    wd.J0_strip.m = m0 ∧
    1 ≤ wInp.prep.phiNum_dec ∧ wInp.prep.phiNum_dec ≤ wInp.prep.phiDen_dec ∧
    p.γ_del wd.φ_dec wd.J0_strip.m ≤ wd.γ_del ∧
    wd.φ_ds ≤ p.φ_out wd.φ_dec wd.J0_strip.m ∧
    ⌈p.γ_ExpPath wd.φ_dec wd.J0_strip.m⌉₊ ≤ γJ ∧
    p.γ_ExpPath wd.φ_dec wd.J0_strip.m ≤ ↑(wInp.γExpInt impl.constructExpander p) := by
  intro wd p dsOne dJ m0 γJ γJq
  have hφNum : 1 ≤ wInp.prep.phiNum_dec := hs.2.2.2.2.2.2.2.2.1
  have hφLe : wInp.prep.phiNum_dec ≤ wInp.prep.phiDen_dec := hs.2.2.2.2.2.2.2.2.2.1
  have hJ0_eq : wd.J0_strip = stripLoops t2i.J := by
    change wInp.prep.J0_strip = stripLoops t2i.J
    rw [hs.2.2.1, hJ_eq]
  have hm0_eq : wd.J0_strip.m = m0 := by rw [hJ0_eq]
  have hpd_le : wInp.prep.phiDen_dec ≤ Task1Input.phiDenCap impl t2i.J := by
    rw [← hJ_eq]; exact task2_phiDen_le_cap hs hφ_cap
  have hdJ_le : wInp.dJInt ≤ dJ := by
    change wInp.dJInt ≤ Task1Input.dJCap impl t2i.J
    rw [← hJ_eq]; exact task2_dJ_le_cap hs hφ_lb
  have hdJ_pos : 1 ≤ wInp.dJInt := by
    unfold WitnessCoreInput.dJInt
    exact Nat.div_pos (by omega) hφNum
  have hceil_dJ : ⌈1 / wd.φ_dec⌉₊ = wInp.dJInt := by
    change ⌈1 / ((wInp.prep.phiNum_dec : ℝ) / (wInp.prep.phiDen_dec : ℝ))⌉₊ = wInp.dJInt
    exact (wInp.dJInt_eq hs).symm
  have hγ_ceil : ⌈p.γ_ExpPath wd.φ_dec wd.J0_strip.m⌉₊ ≤ γJ := by
    rw [PathDSParams.γ_ExpPath, hceil_dJ, hm0_eq, Nat.ceil_natCast]
    exact p.hgExp_mono hdJ_pos hdJ_le (le_refl _)
  have hγ_real : p.γ_ExpPath wd.φ_dec wd.J0_strip.m ≤ ↑γJ := by
    rw [PathDSParams.γ_ExpPath, hceil_dJ, hm0_eq]
    exact_mod_cast p.hgExp_mono hdJ_pos hdJ_le (le_refl _)
  have hγq_real : p.γ_query wd.φ_dec wd.J0_strip.m ≤ ↑γJq := by
    rw [PathDSParams.γ_query, hceil_dJ, hm0_eq]
    exact_mod_cast p.hgQuery_mono hdJ_pos hdJ_le (le_refl _)
  have hγ_le_expInt : p.γ_ExpPath wd.φ_dec wd.J0_strip.m ≤ ↑(wInp.γExpInt impl.constructExpander p) := by
    rw [PathDSParams.γ_ExpPath, hceil_dJ]
    exact_mod_cast le_max_left (p.gExp wInp.dJInt wInp.prep.J0_strip.m) _
  have hround_ceil : ⌈1 / roundPhi wd.φ_dec⌉₊ = wInp.dJInt := by
    rw [roundPhi, one_div_one_div, Nat.ceil_natCast, hceil_dJ]
  have hγD_le : p.γ_del wd.φ_dec wd.J0_strip.m ≤ wd.γ_del := by
    change _ ≤ max (p.γ_del (roundPhi wd.φ_dec) wd.J0_strip.m) _
    refine le_trans ?_ (le_max_left _ _)
    simp only [PathDSParams.γ_del, hceil_dJ, hround_ceil]; exact le_refl _
  have hφds_le : wd.φ_ds ≤ p.φ_out wd.φ_dec wd.J0_strip.m := by
    change min (p.φ_out (roundPhi wd.φ_dec) wd.J0_strip.m) _ ≤ _
    refine le_trans (min_le_left _ _) ?_
    simp only [PathDSParams.φ_out, hceil_dJ, hround_ceil]; exact le_refl _
  have hceil_div_le : (wInp.prep.phiDen_dec + wInp.prep.phiNum_dec - 1) / wInp.prep.phiNum_dec ≤ dJ := hdJ_le
  have hg_dJ_le : p.gExp wInp.dJInt m0 ≤ γJ :=
    p.hgExp_mono hdJ_pos hceil_div_le (le_refl _)
  refine ⟨fun ci hci => ?_, ?_, ?_, hm0_eq, hφNum, hφLe, hγD_le, hφds_le, hγ_ceil, hγ_le_expInt⟩
  · set c := wd.comps[ci]
    have hp := hok.comp_props ci hci
    have hc_n : c.J_sub.n ≤ t2i.J.n := by
      rw [hp.2.2.2.2.2.1]
      calc c.X.card ≤ wInp.prep.J.verts.card := Finset.card_le_card (hJ_eq ▸ hp.2.2.1)
        _ = t2i.J.n := by simp [Graph.verts, hJ_eq]
    have hc_m : c.J_sub.m ≤ m0 := hm0_eq ▸ hp.2.2.2.2.2.2.2.2.1
    have hd_def : (wInp.prep.phiDen_dec + wInp.prep.phiNum_dec - 1) / wInp.prep.phiNum_dec = wInp.dJInt := rfl
    have hbase_le : wInp.prep.phiDen_dec + c.J_sub.n + c.J_sub.m + wd.J0_strip.m +
        p.gExp ((wInp.prep.phiDen_dec + wInp.prep.phiNum_dec - 1) / wInp.prep.phiNum_dec) wd.J0_strip.m + 2 ≤
        Task1Input.phiDenCap impl t2i.J + t2i.J.n + m0 + m0 + γJ + 2 := by
      rw [hd_def, hm0_eq]; omega
    have hpow := Nat.pow_le_pow_left hbase_le p.c_space
    have hm_pow := Nat.mul_le_mul_left p.C_space hpow
    refine ⟨le_trans (p.hinitSpace_le _ _ _ _ _ hφNum hφLe) hm_pow,
      le_trans (p.hdelSpace_le _ _ _ _ _ hφNum hφLe) hm_pow,
      le_trans (p.hquerySpace_le _ _ _ _ _ hφNum hφLe) hm_pow, ?_, ?_⟩
    · have hlog_le : Nat.log 2 (c.J_sub.n + c.J_sub.m + wInp.prep.phiDen_dec + wd.J0_strip.m +
          ⌈p.γ_ExpPath wd.φ_dec wd.J0_strip.m⌉₊ + 2) ≤
          Nat.log 2 (t2i.J.n + m0 + Task1Input.phiDenCap impl t2i.J + m0 + γJ + 2) :=
        Nat.log_mono_right (by omega)
      have hcw := hww.2.1
      have hmul := Nat.mul_le_mul_left p.cw (Nat.succ_le_succ hlog_le)
      exact le_trans hmul hcw
    · rw [Nat.ceil_le, Nat.cast_mul, mul_assoc]
      have hle1 : p.γ_ExpPath wd.φ_dec wd.J0_strip.m ≤ ↑γJ := hγ_real
      have hle2 : p.K_init * p.γ_ExpPath wd.φ_dec wd.J0_strip.m ≤ ↑⌈p.K_init * ↑γJ⌉₊ := by
        calc p.K_init * p.γ_ExpPath wd.φ_dec wd.J0_strip.m ≤ p.K_init * ↑γJ :=
            mul_le_mul_of_nonneg_left hle1 p.hK_init
          _ ≤ ↑⌈p.K_init * ↑γJ⌉₊ := Nat.le_ceil _
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left hle2 (Nat.cast_nonneg _)
  · exact Nat.ceil_mono (mul_le_mul_of_nonneg_left hγq_real p.hK_del)
  · exact Nat.ceil_mono (mul_le_mul_of_nonneg_left hγq_real p.hK_query)

/-! ## Incidence linked lists (`IncChainBound` and `IncListAt`) -/

inductive IncChainBound (mem : ℕ → ℕ) (lo hi : ℕ) : ℕ → List (ℕ × ℕ) → Prop where
  | nil : IncChainBound mem lo hi 0 []
  | cons {ptr ci b next rest} :
      lo ≤ ptr → ptr + 3 ≤ hi →
      mem ptr = ci → mem (ptr + 1) = b → mem (ptr + 2) = next →
      IncChainBound mem lo hi next rest →
      IncChainBound mem lo hi ptr ((ci, b) :: rest)

lemma IncChainBound.mono {mem mem' : ℕ → ℕ} {lo hi ptr : ℕ} {entries : List (ℕ × ℕ)}
    (hc : IncChainBound mem lo hi ptr entries)
    (heq : ∀ a, lo ≤ a → a < hi → mem' a = mem a) :
    IncChainBound mem' lo hi ptr entries := by
  induction hc with
  | nil => exact .nil
  | cons hlo hhi h0 h1 h2 _ ih =>
    exact .cons hlo hhi
      ((heq _ hlo (by omega)).trans h0)
      ((heq _ (by omega) (by omega)).trans h1)
      ((heq _ (by omega) (by omega)).trans h2)
      ih

lemma IncChainBound.weaken {mem : ℕ → ℕ} {lo hi lo' hi' ptr : ℕ} {entries : List (ℕ × ℕ)}
    (hc : IncChainBound mem lo hi ptr entries) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    IncChainBound mem lo' hi' ptr entries := by
  induction hc with
  | nil => exact .nil
  | cons ha hb h0 h1 h2 _ ih => exact .cons (by omega) (by omega) h0 h1 h2 ih

def IncListAt (mem : ℕ → ℕ) (vHeadAddr nH : ℕ) (comps : List CompInfo) (embJH : ℕ → Walk)
    (nodesAddr nodesEnd : ℕ) : Prop :=
  ∃ L : ℕ → List (ℕ × ℕ),
    (∀ x < nH,
      IncChainBound mem nodesAddr nodesEnd (mem (vHeadAddr + x)) (L x) ∧
      (∀ p ∈ L x, ∃ (hp : p.1 < comps.length), p.2 < comps[p.1].J_sub.m ∧
        x ∈ (embJH (comps[p.1].jSubOrigEdges.getD p.2 0)).verts) ∧
      (∀ ci (hci : ci < comps.length) b, b < comps[ci].J_sub.m →
        x ∈ (embJH (comps[ci].jSubOrigEdges.getD b 0)).verts → (ci, b) ∈ L x)) ∧
    (∑ x ∈ Finset.range nH, (L x).length) * 3 ≤ nodesEnd - nodesAddr

lemma IncListAt.mono {mem mem' : ℕ → ℕ} {vHeadAddr nH : ℕ} {comps : List CompInfo}
    {embJH : ℕ → Walk} {nodesAddr nodesEnd : ℕ}
    (h : IncListAt mem vHeadAddr nH comps embJH nodesAddr nodesEnd)
    (hHead : ∀ x < nH, mem' (vHeadAddr + x) = mem (vHeadAddr + x))
    (hNodes : ∀ a, nodesAddr ≤ a → a < nodesEnd → mem' a = mem a) :
    IncListAt mem' vHeadAddr nH comps embJH nodesAddr nodesEnd := by
  obtain ⟨L, hL, hsum⟩ := h
  refine ⟨L, fun x hx => ?_, hsum⟩
  obtain ⟨hc, hsub, hmem⟩ := hL x hx
  exact ⟨by rw [hHead x hx]; exact hc.mono hNodes, hsub, hmem⟩

/-! ## Multi-instance `DSArrayAt`, potential `dsTotalPhi`, and round potential `t2RoundPhi` -/

structure DSArrayAt (pdsImpl : PathDSImpl) (comps : List CompInfo) (phiNum phiDen M w : ℕ)
    (dsBaseAddr handlesAddr hCur : ℕ) (mem : ℕ → ℕ)
    (upTo : ℕ) (states : ℕ → PathDSAbsState) (reps : ℕ → pdsImpl.R.τ) : Prop where
  h_ge : dsBaseAddr ≤ hCur
  zero_from : WordRAM.ZeroFrom mem hCur
  at_ci : ∀ ci, ci < upTo →
    let handle := mem (handlesAddr + ci)
    dsBaseAddr ≤ handle ∧ handle ≤ hCur ∧
    pdsImpl.R.rep handle (states ci) (reps ci) mem ∧
    (∀ a, pdsImpl.R.foot handle (reps ci) a → dsBaseAddr ≤ a ∧ a < hCur) ∧
    (states ci).G = (comps.getD ci defaultCompInfo).J_sub ∧
    (states ci).phiNum = phiNum ∧
    (states ci).phiDen = phiDen ∧
    (states ci).M = M ∧
    PathDSAbsState.Valid pdsImpl.params (states ci)
  disjoint : ∀ ci₁, ci₁ < upTo → ∀ ci₂, ci₂ < upTo → ci₁ ≠ ci₂ →
    ∀ a, pdsImpl.R.foot (mem (handlesAddr + ci₁)) (reps ci₁) a →
      ¬ pdsImpl.R.foot (mem (handlesAddr + ci₂)) (reps ci₂) a

def dsTotalPhi (pdsImpl : PathDSImpl) (handlesAddr n : ℕ) (reps : ℕ → pdsImpl.R.τ)
    (mem : ℕ → ℕ) : ℕ :=
  ∑ ci ∈ Finset.range n, pdsImpl.R.phi (mem (handlesAddr + ci)) (reps ci) mem

lemma DSArrayAt.frame_range {pdsImpl : PathDSImpl} {comps : List CompInfo}
    {phiNum phiDen M w dsBaseAddr handlesAddr hCur upTo : ℕ}
    {mem mem' : ℕ → ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → pdsImpl.R.τ}
    (hLoc : pdsImpl.R.Local)
    (h : DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem upTo states reps)
    (hHdl : ∀ ci < upTo, mem' (handlesAddr + ci) = mem (handlesAddr + ci))
    (hDS : ∀ a, dsBaseAddr ≤ a → a < hCur → mem' a = mem a)
    (hZ : WordRAM.ZeroFrom mem' hCur) :
    DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem' upTo states reps ∧
    dsTotalPhi pdsImpl handlesAddr upTo reps mem' = dsTotalPhi pdsImpl handlesAddr upTo reps mem := by
  refine ⟨⟨h.h_ge, hZ, fun ci hci => ?_, fun c1 h1 c2 h2 hne a ha => ?_⟩, ?_⟩
  · have hci_at := h.at_ci ci hci
    have hft := fun a ha => (hDS a (hci_at.2.2.2.1 a ha).1 (hci_at.2.2.2.1 a ha).2).symm
    have hloc := hLoc (mem (handlesAddr + ci)) (states ci) (reps ci) mem mem' hft
    rw [hHdl ci hci]
    exact ⟨hci_at.1, hci_at.2.1, hloc.1 hci_at.2.2.1, hci_at.2.2.2.1, hci_at.2.2.2.2⟩
  · rw [hHdl c1 h1] at ha
    rw [hHdl c2 h2]
    exact h.disjoint c1 h1 c2 h2 hne a ha
  · unfold dsTotalPhi
    refine Finset.sum_congr rfl fun ci hci_r => ?_
    have hci := Finset.mem_range.mp hci_r
    have hci_at := h.at_ci ci hci
    have hft := fun a ha => (hDS a (hci_at.2.2.2.1 a ha).1 (hci_at.2.2.2.1 a ha).2).symm
    rw [hHdl ci hci]
    exact (hLoc (mem (handlesAddr + ci)) (states ci) (reps ci) mem mem' hft).2.symm

lemma DSArrayAt.frame_below {pdsImpl : PathDSImpl} {comps : List CompInfo}
    {phiNum phiDen M w dsBaseAddr handlesAddr hCur upTo : ℕ}
    {mem mem' : ℕ → ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → pdsImpl.R.τ}
    (hLoc : pdsImpl.R.Local)
    (h : DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem upTo states reps)
    (hHdl : ∀ ci < upTo, mem' (handlesAddr + ci) = mem (handlesAddr + ci))
    (hDS : ∀ a, dsBaseAddr ≤ a → mem' a = mem a) :
    DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem' upTo states reps ∧
    dsTotalPhi pdsImpl handlesAddr upTo reps mem' = dsTotalPhi pdsImpl handlesAddr upTo reps mem :=
  h.frame_range hLoc hHdl (fun a ha _ => hDS a ha) fun a ha => by
    rw [hDS a (le_trans h.h_ge ha)]; exact h.zero_from a ha

lemma DSArrayAt.step_init {p : Program} {pdsImpl : PathDSImpl} {comps : List CompInfo}
    {phiNum phiDen M w dsBaseAddr handlesAddr hCur upTo dsBase : ℕ}
    {mem : ℕ → ℕ} {states : ℕ → PathDSAbsState} {reps : ℕ → pdsImpl.R.τ}
    {gAddr : ℕ} {ω : ℕ → Bool} {pos : ℕ}
    (hSpec : pdsImpl.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure pdsImpl.params w))
    (hArr : DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr hCur mem upTo states reps)
    (hup : upTo < comps.length)
    (hHdl_lt : handlesAddr + comps.length ≤ dsBaseAddr)
    (hg_w : gAddr < 2 ^ w) (hp_w : phiNum < 2 ^ w) (hd_w : phiDen < 2 ^ w)
    (hM_w : M < 2 ^ w) (hh_w : hCur < 2 ^ w)
    (hga_le : gAddr + comps[upTo].J_sub.encode.length ≤ hCur)
    (hG_at : GraphAt mem gAddr comps[upTo].J_sub)
    (hφ1 : 1 ≤ phiNum) (hφ2 : phiNum ≤ phiDen)
    (hJval : comps[upTo].J_sub.IsValid)
    (hJm1 : 1 ≤ comps[upTo].J_sub.m) (hJmM : comps[upTo].J_sub.m ≤ M)
    (hdeg : ∀ v < comps[upTo].J_sub.n, 1 ≤ comps[upTo].J_sub.deg v)
    (hexp : comps[upTo].J_sub.IsConductanceExpanderOn comps[upTo].J_sub.verts (↑phiNum / ↑phiDen))
    (hcw : pdsImpl.params.cw * (Nat.log 2 (comps[upTo].J_sub.n + comps[upTo].J_sub.m + phiDen + M +
      ⌈pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M⌉₊ + 2) + 1) ≤ w)
    (hSpace_w : hCur + pdsImpl.params.initSpace phiNum phiDen comps[upTo].J_sub.n comps[upTo].J_sub.m M < 2 ^ w) :
    ∃ body o st' c s' x',
      p.procs[dsBase]? = some body ∧
      Runs w p ω body (startState [gAddr, phiNum, phiDen, M, hCur] mem pos) o st' c ∧
      o.value ≤ hCur + pdsImpl.params.initSpace phiNum phiDen comps[upTo].J_sub.n comps[upTo].J_sub.m M ∧
      hCur ≤ o.value ∧
      (∀ a < hCur, st'.mem a = mem a) ∧
      s'.Vhat = ∅ ∧ s'.deleted = ∅ ∧
      (let mem'' := Function.update st'.mem (handlesAddr + upTo) hCur
       let states' := Function.update states upTo s'
       let reps' := Function.update reps upTo x'
       DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr o.value mem'' (upTo + 1) states' reps' ∧
       c + dsTotalPhi pdsImpl handlesAddr (upTo + 1) reps' mem'' ≤
         ⌈pdsImpl.params.K_init * ↑comps[upTo].J_sub.m * pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M⌉₊ +
           dsTotalPhi pdsImpl handlesAddr upTo reps mem) := by
  have hArgs_w : ∀ a ∈ [gAddr, phiNum, phiDen, M, hCur], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hPre : (pathDSDataStructure pdsImpl.params w).initPre [gAddr, phiNum, phiDen, M, hCur] mem :=
    ⟨gAddr, phiNum, phiDen, M, hCur, comps[upTo].J_sub, rfl, hga_le, hG_at, hφ1, hφ2, hJval,
      hJm1, hJmM, hdeg, hexp, hcw⟩
  have hsp : (pathDSDataStructure pdsImpl.params w).initSpace [gAddr, phiNum, phiDen, M, hCur] mem =
      pdsImpl.params.initSpace phiNum phiDen comps[upTo].J_sub.n comps[upTo].J_sub.m M := by
    simp [pathDSDataStructure, graphAt_iff_readGraph.mp hG_at]
  have hcost : (pathDSDataStructure pdsImpl.params w).initCost [gAddr, phiNum, phiDen, M, hCur] mem =
      ⌈pdsImpl.params.K_init * ↑comps[upTo].J_sub.m * pdsImpl.params.γ_ExpPath (↑phiNum / ↑phiDen) M⌉₊ := by
    simp [pathDSDataStructure, graphAt_iff_readGraph.mp hG_at]
  have hlast : WordRAM.heapArg [gAddr, phiNum, phiDen, M, hCur] = hCur := rfl
  obtain ⟨body, hp, o, st', c, hr, s', x', hrep', hpost', hresp', hcost_le⟩ :=
    hSpec.2.1 [gAddr, phiNum, phiDen, M, hCur] mem pos ω hArgs_w hPre hArr.zero_from
      (by simpa [hlast, hsp] using hSpace_w)
  rcases hresp' with ⟨hge', hle', hz', hpres', hfoot'⟩
  rw [hlast] at hrep' hge' hle' hpres' hfoot' hcost_le
  rw [hsp] at hle'
  rcases hpost' with ⟨gAddr', phiNum', phiDen', M', h', G', heq_a, hG'_at, hsφn, hsφd, hsM, hsG, hsVh, hsDel, hsVal⟩
  simp only [List.cons.injEq, and_true] at heq_a
  rcases heq_a with ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hG'_eq : G' = comps[upTo].J_sub :=
    ((@graphAt_iff_readGraph mem gAddr G').mp hG'_at).symm.trans
      ((@graphAt_iff_readGraph mem gAddr _).mp hG_at)
  subst G'
  refine ⟨body, o, st', c, s', x', hp, hr, hle', hge', fun a ha => hpres' a ha (fun h => h),
    hsVh, hsDel, ?_⟩
  let mem'' := Function.update st'.mem (handlesAddr + upTo) hCur
  let states' := Function.update states upTo s'
  let reps' := Function.update reps upTo x'
  have hupd_lt_ds : handlesAddr + upTo < dsBaseAddr := by omega
  have hupd_lt_cur : handlesAddr + upTo < hCur := lt_of_lt_of_le hupd_lt_ds hArr.h_ge
  have hz'' : WordRAM.ZeroFrom mem'' o.value := fun a ha => by
    have hne : a ≠ handlesAddr + upTo := by omega
    dsimp only [mem'']; rw [Function.update_of_ne hne]; exact hz' a ha
  have h_below_mem'' : ∀ ci < upTo, mem'' (handlesAddr + ci) = mem (handlesAddr + ci) := by
    intro ci hci
    have hne : handlesAddr + ci ≠ handlesAddr + upTo := by omega
    have hlt_cur : handlesAddr + ci < hCur := lt_of_lt_of_le (by omega) hArr.h_ge
    dsimp only [mem'']; rw [Function.update_of_ne hne]
    exact hpres' _ hlt_cur (fun h => h)
  have h_foot_old : ∀ ci < upTo, ∀ a, pdsImpl.R.foot (mem (handlesAddr + ci)) (reps ci) a →
      mem'' a = mem a := by
    intro ci hci a ha
    have hbounds := (hArr.at_ci ci hci).2.2.2.1 a ha
    have hne : a ≠ handlesAddr + upTo := by omega
    dsimp only [mem'']; rw [Function.update_of_ne hne]
    exact hpres' a hbounds.2 (fun h => h)
  have h_foot_new : ∀ a, pdsImpl.R.foot hCur x' a → mem'' a = st'.mem a := by
    intro a ha
    rcases hfoot' a ha with hFalse | ⟨hle_a, _⟩
    · exact False.elim hFalse
    · have hne : a ≠ handlesAddr + upTo := by omega
      simp only [mem'', Function.update_of_ne hne]
  have hloc_new := hSpec.1 hCur s' x' st'.mem mem'' fun a ha => (h_foot_new a ha).symm
  have hArr'' : DSArrayAt pdsImpl comps phiNum phiDen M w dsBaseAddr handlesAddr o.value mem'' (upTo + 1) states' reps' := by
    refine ⟨le_trans hArr.h_ge hge', hz'', fun ci hci => ?_, fun c1 h1 c2 h2 hne a ha => ?_⟩
    · by_cases hlt : ci < upTo
      · have hold := hArr.at_ci ci hlt
        have hloc := hSpec.1 (mem (handlesAddr + ci)) (states ci) (reps ci) mem mem'' fun a ha =>
          (h_foot_old ci hlt a ha).symm
        simp only [states', reps', Function.update_of_ne (by omega : ci ≠ upTo)]
        rw [h_below_mem'' ci hlt]
        exact ⟨hold.1, le_trans hold.2.1 hge', hloc.1 hold.2.2.1,
          fun a ha => ⟨(hold.2.2.2.1 a ha).1, lt_of_lt_of_le (hold.2.2.2.1 a ha).2 hge'⟩, hold.2.2.2.2⟩
      · have hci_eq : ci = upTo := by omega
        subst ci
        simp only [mem'', states', reps', Function.update_self]
        refine ⟨hArr.h_ge, hge', hloc_new.1 hrep', fun a ha => ?_, ?_, hsφn, hsφd, hsM, hsVal⟩
        · rcases hfoot' a ha with hFalse | ⟨hle_a, hlt_a⟩
          · exact False.elim hFalse
          · exact ⟨le_trans hArr.h_ge hle_a, hlt_a⟩
        · rw [hG'_eq, List.getD_eq_getElem _ _ hup]
    · by_cases hc1_u : c1 = upTo
      · subst c1
        have hc2_lt : c2 < upTo := by omega
        simp only [reps', Function.update_self, Function.update_of_ne (by omega : c2 ≠ upTo)] at ha ⊢
        rw [show mem'' (handlesAddr + upTo) = hCur from by simp [mem'']] at ha
        rw [h_below_mem'' c2 hc2_lt]
        intro h2_f
        have h2_b := ((hArr.at_ci c2 hc2_lt).2.2.2.1 a h2_f).2
        rcases hfoot' a ha with hFalse | ⟨hle_a, _⟩
        · exact False.elim hFalse
        · omega
      · by_cases hc2_u : c2 = upTo
        · subst c2
          have hc1_lt : c1 < upTo := by omega
          simp only [reps', Function.update_self, Function.update_of_ne (by omega : c1 ≠ upTo)] at ha ⊢
          rw [show mem'' (handlesAddr + upTo) = hCur from by simp [mem'']]
          rw [h_below_mem'' c1 hc1_lt] at ha
          intro h2_f
          have h1_b := ((hArr.at_ci c1 hc1_lt).2.2.2.1 a ha).2
          rcases hfoot' a h2_f with hFalse | ⟨hle_a, _⟩
          · exact False.elim hFalse
          · omega
        · have hc1_lt : c1 < upTo := by omega
          have hc2_lt : c2 < upTo := by omega
          simp only [reps', Function.update_of_ne hc1_u, Function.update_of_ne hc2_u] at ha ⊢
          rw [h_below_mem'' c1 hc1_lt] at ha
          rw [h_below_mem'' c2 hc2_lt]
          exact hArr.disjoint c1 hc1_lt c2 hc2_lt hne a ha
  refine ⟨hArr'', ?_⟩
  have hphi_sum : dsTotalPhi pdsImpl handlesAddr (upTo + 1) reps' mem'' =
      dsTotalPhi pdsImpl handlesAddr upTo reps mem + pdsImpl.R.phi hCur x' st'.mem := by
    unfold dsTotalPhi
    rw [Finset.sum_range_succ]
    have hcongr : ∑ ci ∈ Finset.range upTo, pdsImpl.R.phi (mem'' (handlesAddr + ci)) (reps' ci) mem'' =
        ∑ ci ∈ Finset.range upTo, pdsImpl.R.phi (mem (handlesAddr + ci)) (reps ci) mem := by
      refine Finset.sum_congr rfl fun ci hci_r => ?_
      have hci := Finset.mem_range.mp hci_r
      simp only [reps', Function.update_of_ne (by omega : ci ≠ upTo)]
      rw [h_below_mem'' ci hci]
      exact (hSpec.1 (mem (handlesAddr + ci)) (states ci) (reps ci) mem mem'' fun a ha =>
        (h_foot_old ci hci a ha).symm).2.symm
    have hlast : pdsImpl.R.phi (mem'' (handlesAddr + upTo)) (reps' upTo) mem'' =
        pdsImpl.R.phi hCur x' st'.mem := by
      simp only [mem'', reps', Function.update_self]
      exact hloc_new.2.symm
    rw [hcongr, hlast]
  rw [hphi_sum, hcost] at *
  omega

end MinCostFlow.Spanner
