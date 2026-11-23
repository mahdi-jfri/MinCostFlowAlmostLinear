module

public import MinCostFlow.Spanner.ProgBuildWitnessAsmFinal

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-- Total Word-RAM step budget for `buildWitnessCoreBody`. -/
noncomputable def buildWitnessCoreCost (inp : WitnessCoreInput) (ce : ConstructExpanderImpl)
    (pds : PathDSParams) : ℕ :=
  phase01Cost inp ce pds + ceLoopCost inp ce + cePhase3Cost inp ce + 5

private lemma compInfo_ext {c₁ c₂ : CompInfo}
    (h1 : c₁.level = c₂.level) (h2 : c₁.X = c₂.X) (h3 : c₁.verts = c₂.verts)
    (h4 : c₁.J_sub = c₂.J_sub) (h5 : c₁.jSubOrigEdges = c₂.jSubOrigEdges)
    (h6 : c₁.W_sub = c₂.W_sub) (h7 : c₁.wStart = c₂.wStart) : c₁ = c₂ := by
  rcases c₁ with ⟨_, _, _, _, _, _, _⟩
  rcases c₂ with ⟨_, _, _, _, _, _, _⟩
  simp only at h1 h2 h3 h4 h5 h6 h7
  subst h1 h2 h3 h4 h5 h6 h7
  rfl

lemma listAt_inj {mem : ℕ → ℕ} {a : ℕ} {xs₁ xs₂ : List ℕ}
    (hlen : xs₁.length = xs₂.length) (h1 : ListAt mem a xs₁) (h2 : ListAt mem a xs₂) :
    xs₁ = xs₂ := by
  refine List.ext_getElem hlen fun i hi₁ hi₂ => ?_
  exact (h1 i hi₁).symm.trans (h2 i hi₂)

private lemma listAt_flatMap_pair_unique {mem : ℕ → ℕ} :
    ∀ (a : ℕ) (es₁ es₂ : List (ℕ × ℕ)),
      es₁.length = es₂.length →
      ListAt mem a (es₁.flatMap fun e => [e.1, e.2]) →
      ListAt mem a (es₂.flatMap fun e => [e.1, e.2]) →
      es₁ = es₂
  | _, [], [], _, _, _ => rfl
  | a, e₁ :: t₁, e₂ :: t₂, hlen, h1, h2 => by
    have hp0 : e₁.1 = e₂.1 := by
      have s1 := h1 0 (by simp)
      have s2 := h2 0 (by simp)
      simpa using s1.symm.trans s2
    have hp1 : e₁.2 = e₂.2 := by
      have s1 := h1 1 (by simp)
      have s2 := h2 1 (by simp)
      simpa using s1.symm.trans s2
    have heq : e₁ = e₂ := Prod.ext hp0 hp1
    have ht1 : ListAt mem (a + 2) (t₁.flatMap fun e => [e.1, e.2]) := by
      intro i hi
      have s := h1 (2 + i) (by simp only [List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil]; omega)
      simpa [Nat.add_comm 2 i, Nat.add_assoc, List.flatMap_cons] using s
    have ht2 : ListAt mem (a + 2) (t₂.flatMap fun e => [e.1, e.2]) := by
      intro i hi
      have s := h2 (2 + i) (by simp only [List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil]; omega)
      simpa [Nat.add_comm 2 i, Nat.add_assoc, List.flatMap_cons] using s
    have htail := listAt_flatMap_pair_unique (a + 2) t₁ t₂ (by simpa using hlen) ht1 ht2
    rw [heq, htail]

lemma graphAt_inj {mem : ℕ → ℕ} {a : ℕ} {G₁ G₂ : Graph}
    (h1 : GraphAt mem a G₁) (h2 : GraphAt mem a G₂) : G₁ = G₂ := by
  have hn : G₁.n = G₂.n := by
    have s1 := h1 0 (by simp [Graph.encode])
    have s2 := h2 0 (by simp [Graph.encode])
    simpa [Graph.encode] using s1.symm.trans s2
  have hm : G₁.m = G₂.m := by
    have s1 := h1 1 (by simp [Graph.encode])
    have s2 := h2 1 (by simp [Graph.encode])
    simpa [Graph.encode] using s1.symm.trans s2
  have hf1 : ListAt mem (a + 2) (G₁.edges.flatMap fun e => [e.1, e.2]) := by
    intro i hi
    have hlt1 : i + 2 < G₁.encode.length := by
      dsimp only [Graph.encode]
      rw [List.length_cons, List.length_cons]
      omega
    have s := h1 (i + 2) hlt1
    have s' : mem (a + (i + 2)) = (G₁.edges.flatMap fun e => [e.1, e.2])[i] := by
      simpa only [Graph.encode, List.cons_append, List.nil_append, List.getElem_cons_succ] using s
    rwa [show a + 2 + i = a + (i + 2) by omega]
  have hf2 : ListAt mem (a + 2) (G₂.edges.flatMap fun e => [e.1, e.2]) := by
    intro i hi
    have hlt2 : i + 2 < G₂.encode.length := by
      dsimp only [Graph.encode]
      rw [List.length_cons, List.length_cons]
      omega
    have s := h2 (i + 2) hlt2
    have s' : mem (a + (i + 2)) = (G₂.edges.flatMap fun e => [e.1, e.2])[i] := by
      simpa only [Graph.encode, List.cons_append, List.nil_append, List.getElem_cons_succ] using s
    rwa [show a + 2 + i = a + (i + 2) by omega]
  have hed : G₁.edges = G₂.edges := listAt_flatMap_pair_unique (a + 2) G₁.edges G₂.edges hm hf1 hf2
  cases G₁; cases G₂; simp_all

lemma listAt_flatMap_compRecord_unique {mem : ℕ → ℕ} :
    ∀ (a : ℕ) (cs₁ cs₂ : List (ℕ × List ℕ)),
      cs₁.length = cs₂.length →
      ListAt mem a (cs₁.flatMap compRecord) →
      ListAt mem a (cs₂.flatMap compRecord) →
      cs₁ = cs₂
  | _, [], [], _, _, _ => rfl
  | a, (l₁, vs₁) :: t₁, (l₂, vs₂) :: t₂, hlen, h1, h2 => by
    have hlen1 : 2 + vs₁.length = (compRecord (l₁, vs₁)).length := by
      simp [compRecord]; omega
    have hlen2 : 2 + vs₂.length = (compRecord (l₂, vs₂)).length := by
      simp [compRecord]; omega
    have hl : l₁ = l₂ := by
      have s1 := h1 0 (by simp [compRecord])
      have s2 := h2 0 (by simp [compRecord])
      simpa [compRecord] using s1.symm.trans s2
    have hvlen : vs₁.length = vs₂.length := by
      have s1 := h1 1 (by simp [compRecord])
      have s2 := h2 1 (by simp [compRecord])
      simpa [compRecord] using s1.symm.trans s2
    have hvs : vs₁ = vs₂ := by
      refine List.ext_getElem hvlen fun k hk₁ hk₂ => ?_
      have h1_lt : 2 + k < (compRecord (l₁, vs₁)).length := by rw [← hlen1]; omega
      have h2_lt : 2 + k < (compRecord (l₂, vs₂)).length := by rw [← hlen2]; omega
      have s1 := h1 (2 + k) (by rw [List.flatMap_cons, List.length_append]; omega)
      have s2 := h2 (2 + k) (by rw [List.flatMap_cons, List.length_append]; omega)
      simp only [List.flatMap_cons] at s1 s2
      rw [List.getElem_append_left h1_lt] at s1
      rw [List.getElem_append_left h2_lt] at s2
      have sc1 : (compRecord (l₁, vs₁))[2 + k]'h1_lt = vs₁[k] := by
        dsimp only [compRecord]; simp [Nat.add_comm 2 k]
      have sc2 : (compRecord (l₂, vs₂))[2 + k]'h2_lt = vs₂[k] := by
        dsimp only [compRecord]; simp [Nat.add_comm 2 k]
      rw [sc1] at s1; rw [sc2] at s2
      exact s1.symm.trans s2
    have ht1 : ListAt mem (a + (2 + vs₁.length)) (t₁.flatMap compRecord) := by
      intro i hi
      have hge1 : (compRecord (l₁, vs₁)).length ≤ (2 + vs₁.length) + i := by omega
      have s := h1 ((2 + vs₁.length) + i) (by
        rw [List.flatMap_cons, List.length_append, ← hlen1]; omega)
      simp only [List.flatMap_cons] at s
      rw [List.getElem_append_right hge1] at s
      have hidx : (t₁.flatMap compRecord)[(2 + vs₁.length) + i - (compRecord (l₁, vs₁)).length]'(by
          omega) = (t₁.flatMap compRecord)[i]'hi := by
        congr 1; omega
      rw [hidx] at s
      simpa [Nat.add_assoc] using s
    have ht2 : ListAt mem (a + (2 + vs₁.length)) (t₂.flatMap compRecord) := by
      intro i hi
      have hge2 : (compRecord (l₂, vs₂)).length ≤ (2 + vs₂.length) + i := by omega
      have s := h2 ((2 + vs₂.length) + i) (by
        rw [List.flatMap_cons, List.length_append, ← hlen2]; omega)
      simp only [List.flatMap_cons] at s
      rw [List.getElem_append_right hge2] at s
      have hidx : (t₂.flatMap compRecord)[(2 + vs₂.length) + i - (compRecord (l₂, vs₂)).length]'(by
          omega) = (t₂.flatMap compRecord)[i]'hi := by
        congr 1; omega
      rw [hidx, ← hvlen] at s
      simpa [Nat.add_assoc] using s
    have htail := listAt_flatMap_compRecord_unique (a + (2 + vs₁.length)) t₁ t₂
      (by simpa using hlen) ht1 ht2
    rw [hl, hvs, htail]

lemma listAt_decompose_flatMap {mem : ℕ → ℕ} {a ℓ pn pd m0 : ℕ}
    {lvl : List ℕ} {cs : List (ℕ × List ℕ)}
    (h : DecomposeOutAt mem a ℓ pn pd lvl cs) (hl : lvl.length = m0) :
    ListAt mem (a + 4 + m0) (cs.flatMap compRecord) := by
  intro i hi
  have hpref : ([ℓ, pn, pd] ++ lvl ++ [cs.length]).length = 4 + m0 := by
    simp [hl]; omega
  have hge : ([ℓ, pn, pd] ++ lvl ++ [cs.length]).length ≤ 4 + m0 + i := by omega
  have hlt : 4 + m0 + i < (Decompose.encode ℓ pn pd lvl cs).length := by
    simp only [Decompose.encode, List.length_append, List.length_cons, List.length_nil]
    omega
  have henc : Decompose.encode ℓ pn pd lvl cs =
      ([ℓ, pn, pd] ++ lvl ++ [cs.length]) ++ cs.flatMap compRecord := by
    simp [Decompose.encode, List.append_assoc]
  have s := h (4 + m0 + i) hlt
  have hs' : mem (a + (4 + m0 + i)) =
      (([ℓ, pn, pd] ++ lvl ++ [cs.length]) ++ cs.flatMap compRecord)[4 + m0 + i]'(by
        rw [← henc]; exact hlt) := by
    simpa [henc] using s
  rw [List.getElem_append_right hge] at hs'
  have hidx : (cs.flatMap compRecord)[4 + m0 + i - ([ℓ, pn, pd] ++ lvl ++ [cs.length]).length]'(by
      omega) = (cs.flatMap compRecord)[i]'hi := by
    congr 1; omega
  rw [hidx] at hs'
  simpa [Nat.add_assoc] using hs'

private lemma rangeCost_congr {f g : ℕ → ℕ} {n : ℕ}
    (hfg : ∀ i < n, f i = g i) : rangeCost f 0 n = rangeCost g 0 n := by
  induction n with
  | zero => simp [rangeCost]
  | succ n ih =>
    rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append]
    rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append]
    have hpre : (List.map f (List.range n)).sum = (List.map g (List.range n)).sum := by
      simpa [rangeCost_zero_eq_range] using ih (fun i hi => hfg i (Nat.lt_succ_of_lt hi))
    have hlast := hfg n (Nat.lt_succ_self n)
    simp [hpre, hlast]

private structure AgreedData (inp₁ inp₂ : WitnessCoreInput) (ce : ConstructExpanderImpl)
    (pds : PathDSParams) : Prop where
  hJ : inp₁.prep.J = inp₂.prep.J
  hJ0 : inp₁.prep.J0_strip = inp₂.prep.J0_strip
  hd_l : inp₁.prep.d_ℓ = inp₂.prep.d_ℓ
  hpn : inp₁.prep.phiNum_dec = inp₂.prep.phiNum_dec
  hpd : inp₁.prep.phiDen_dec = inp₂.prep.phiDen_dec
  hrc : inp₁.prep.rawComps = inp₂.prep.rawComps
  hj0 : inp₁.prep.j0Edges = inp₂.prep.j0Edges
  hcJSub : ∀ (ci : ℕ) (hci : ci < inp₁.prep.rawComps.length),
    inp₁.prep.cJSub inp₁.prep.rawComps[ci] =
      inp₂.prep.cJSub (inp₂.prep.rawComps[ci]'(by rw [← hrc]; exact hci))
  hcJOrig : ∀ (ci : ℕ) (hci : ci < inp₁.prep.rawComps.length),
    inp₁.prep.cJOrig inp₁.prep.rawComps[ci] =
      inp₂.prep.cJOrig (inp₂.prep.rawComps[ci]'(by rw [← hrc]; exact hci))
  hdJ : inp₁.dJInt = inp₂.dJInt
  hmw : inp₁.mwInt ce = inp₂.mwInt ce
  hphiDs : inp₁.phiDsDenInt ce pds = inp₂.phiDsDenInt ce pds
  hgExp : inp₁.γExpInt ce pds = inp₂.γExpInt ce pds
  hgDel : inp₁.γDelInt ce pds = inp₂.γDelInt ce pds
  htau2 : inp₁.tau2Int ce pds = inp₂.tau2Int ce pds
  htau1 : inp₁.tau1Int ce pds = inp₂.tau1Int ce pds
  hmaxEnd : inp₁.maxHeapEnd ce pds = inp₂.maxHeapEnd ce pds

private lemma valid_inputs_agree {inp₁ inp₂ : WitnessCoreInput}
    {ce : ConstructExpanderImpl} {pds : PathDSParams} {mem : ℕ → ℕ} {w : ℕ}
    (h1 : inp₁.Valid ce pds mem w) (h2 : inp₂.Valid ce pds mem w)
    (hj : inp₁.prep.jAddr = inp₂.prep.jAddr)
    (hs : inp₁.statsAddr = inp₂.statsAddr)
    (hd : inp₁.prep.decAddr = inp₂.prep.decAddr)
    (hhp : inp₁.prep.h = inp₂.prep.h)
    (hh : inp₁.h = inp₂.h) :
    AgreedData inp₁ inp₂ ce pds := by
  rcases h1 with ⟨_, _, hv1, _, _, _, hm_len1, hm_vc1, hst1, hcdt1, _⟩
  rcases h2 with ⟨_, _, hv2, _, _, _, hm_len2, hm_vc2, hst2, hcdt2, _⟩
  have hJ : inp₁.prep.J = inp₂.prep.J :=
    graphAt_inj hv1.2.1 (by rw [hj]; exact hv2.2.1)
  have hJ0 : inp₁.prep.J0_strip = inp₂.prep.J0_strip := by
    rw [hv1.2.2.1, hv2.2.2.1, hJ]
  have hdec1 := hv1.2.2.2.2.2.2.1
  have hdec2 := hv2.2.2.2.2.2.2.1
  have hd_l : inp₁.prep.d_ℓ = inp₂.prep.d_ℓ := by
    have s1 := hdec1 0 (by simp [Decompose.encode])
    have s2 := hdec2 0 (by simp [Decompose.encode])
    rw [hd] at s1
    simpa [Decompose.encode] using s1.symm.trans s2
  have hpn : inp₁.prep.phiNum_dec = inp₂.prep.phiNum_dec := by
    have s1 := hdec1 1 (by simp [Decompose.encode])
    have s2 := hdec2 1 (by simp [Decompose.encode])
    rw [hd] at s1
    simpa [Decompose.encode] using s1.symm.trans s2
  have hpd : inp₁.prep.phiDen_dec = inp₂.prep.phiDen_dec := by
    have s1 := hdec1 2 (by simp [Decompose.encode])
    have s2 := hdec2 2 (by simp [Decompose.encode])
    rw [hd] at s1
    simpa [Decompose.encode] using s1.symm.trans s2
  rcases hst1 with ⟨_, hj0len1, haJ0_1, hrlen1, _, _, _, _, _, hj0list1, _⟩
  rcases hst2 with ⟨_, hj0len2, haJ0_2, hrlen2, _, _, _, _, _, hj0list2, _⟩
  have hrlen : inp₁.prep.rawComps.length = inp₂.prep.rawComps.length := by
    rw [hhp] at hrlen1
    exact hrlen1.symm.trans hrlen2
  have hrec1 := listAt_decompose_flatMap hdec1 hv1.2.2.2.2.2.2.2.1
  have hl2 : inp₂.prep.level.length = inp₁.prep.J0_strip.m := by
    rw [hJ0]; exact hv2.2.2.2.2.2.2.2.1
  have hrec2 := listAt_decompose_flatMap hdec2 hl2
  rw [← hd] at hrec2
  have hrc : inp₁.prep.rawComps = inp₂.prep.rawComps :=
    listAt_flatMap_compRecord_unique (inp₁.prep.decAddr + 4 + inp₁.prep.J0_strip.m)
      inp₁.prep.rawComps inp₂.prep.rawComps hrlen hrec1 hrec2
  have hj0len : inp₁.prep.j0Edges.length = inp₂.prep.j0Edges.length := by
    rw [hhp] at hj0len1
    exact hj0len1.symm.trans hj0len2
  have haJ0 : inp₁.prep.aJ0Out = inp₂.prep.aJ0Out := by
    rw [hhp] at haJ0_1
    exact haJ0_1.symm.trans haJ0_2
  have hj0 : inp₁.prep.j0Edges = inp₂.prep.j0Edges :=
    listAt_inj hj0len hj0list1 (by rw [haJ0]; exact hj0list2)
  have hblk : inp₁.prep.hBlocksStart = inp₂.prep.hBlocksStart := by
    unfold PrepInput.hBlocksStart
    rw [hhp, hd_l, hJ0, hj0len, hrlen, hJ]
  have hstrong : ∀ (ci : ℕ) (hci : ci < inp₁.prep.rawComps.length),
      inp₁.prep.cJSub inp₁.prep.rawComps[ci] =
        inp₂.prep.cJSub (inp₂.prep.rawComps[ci]'(by rw [← hrc]; exact hci)) ∧
      inp₁.prep.cJOrig inp₁.prep.rawComps[ci] =
        inp₂.prep.cJOrig (inp₂.prep.rawComps[ci]'(by rw [← hrc]; exact hci)) := by
    intro ci
    induction ci using Nat.strong_induction_on with
    | h ci ih =>
      intro hci
      have hci2 : ci < inp₂.prep.rawComps.length := by rw [← hrc]; exact hci
      have hcsubPtr : inp₁.prep.cJSubPtr ci = inp₂.prep.cJSubPtr ci := by
        unfold PrepInput.cJSubPtr
        rw [hblk]
        congr 1
        have hlist : List.map (fun p => 2 + 3 * (inp₁.prep.cJSub p).m + p.2.length)
              (List.take ci inp₁.prep.rawComps) =
            List.map (fun p => 2 + 3 * (inp₂.prep.cJSub p).m + p.2.length)
              (List.take ci inp₂.prep.rawComps) := by
          refine List.ext_getElem (by simp [hrc]) fun j hj₁ hj₂ => ?_
          have hj_ci : j < ci := by
            simp only [List.length_map, List.length_take] at hj₁
            omega
          have hj1 : j < inp₁.prep.rawComps.length := lt_trans hj_ci hci
          have ihj := (ih j hj_ci hj1).1
          simp only [List.getElem_map, List.getElem_take]
          have hrc_j : inp₁.prep.rawComps[j] = inp₂.prep.rawComps[j] := by simp [hrc]
          rw [ihj, hrc_j]
        exact congrArg List.sum hlist
      have hc1 := hcdt1 ci hci
      have hc2 := hcdt2 ci hci2
      dsimp only at hc1 hc2
      rcases hc1 with ⟨_, _, _, _, _, _, _, hg1, ho1, _⟩
      rcases hc2 with ⟨_, _, _, _, _, _, _, hg2, ho2, _⟩
      have hjsub : inp₁.prep.cJSub inp₁.prep.rawComps[ci] =
          inp₂.prep.cJSub inp₂.prep.rawComps[ci] := by
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci,
          List.getElem?_eq_getElem hci2, Option.getD_some] at hg1 hg2
        rw [hcsubPtr] at hg1
        exact graphAt_inj hg1 hg2
      have hcJOrigPtr : inp₁.prep.cJOrigPtr ci = inp₂.prep.cJOrigPtr ci := by
        unfold PrepInput.cJOrigPtr
        rw [hcsubPtr]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hci,
          List.getElem?_eq_getElem hci2, Option.getD_some, hjsub]
      have hcj1 := cJOrig_props hv1 hci
      have hcj2 := cJOrig_props hv2 hci2
      have holen : (inp₁.prep.cJOrig inp₁.prep.rawComps[ci]).length =
          (inp₂.prep.cJOrig inp₂.prep.rawComps[ci]).length := by
        rw [hcj1.1, hcj2.1, hjsub]
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci,
        List.getElem?_eq_getElem hci2, Option.getD_some] at ho1 ho2
      rw [hcJOrigPtr] at ho1
      have hjorig := listAt_inj holen ho1 ho2
      exact ⟨hjsub, hjorig⟩
  have hdJ : inp₁.dJInt = inp₂.dJInt := by
    rw [WitnessCoreInput.dJInt_eq inp₁ hv1, WitnessCoreInput.dJInt_eq inp₂ hv2, hpn, hpd]
  have hmw : inp₁.mwInt ce = inp₂.mwInt ce := by
    rw [WitnessCoreInput.mwInt_eq inp₁ ce hv1, WitnessCoreInput.mwInt_eq inp₂ ce hv2, hJ0, hpn, hpd]
  have hphiDs : inp₁.phiDsDenInt ce pds = inp₂.phiDsDenInt ce pds := by
    unfold WitnessCoreInput.phiDsDenInt; rw [hdJ, hJ0, hmw]
  have hgExp : inp₁.γExpInt ce pds = inp₂.γExpInt ce pds := by
    unfold WitnessCoreInput.γExpInt; rw [hdJ, hJ0, hmw]
  have hgDel : inp₁.γDelInt ce pds = inp₂.γDelInt ce pds := by
    unfold WitnessCoreInput.γDelInt; rw [hdJ, hJ0, hmw]
  have htau2 : inp₁.tau2Int ce pds = inp₂.tau2Int ce pds := by
    unfold WitnessCoreInput.tau2Int; rw [hgExp, hgDel, hphiDs]
  have hlen_emb : length inp₁.prep.J inp₁.embJH = length inp₂.prep.J inp₂.embJH := by
    rw [hs] at hm_len1
    exact hm_len1.symm.trans hm_len2
  have hvcong_emb : vcongNat inp₁.prep.J inp₁.H' inp₁.embJH =
      vcongNat inp₂.prep.J inp₂.H' inp₂.embJH := by
    rw [hs] at hm_vc1
    exact hm_vc1.symm.trans hm_vc2
  have htau1 : inp₁.tau1Int ce pds = inp₂.tau1Int ce pds := by
    unfold WitnessCoreInput.tau1Int
    rw [htau2, hlen_emb, hvcong_emb, hJ]
  have hmaxEnd : inp₁.maxHeapEnd ce pds = inp₂.maxHeapEnd ce pds := by
    unfold WitnessCoreInput.maxHeapEnd
    rw [hh, hJ0, hdJ, hmw, hrc, hpd, hJ]
  exact ⟨hJ, hJ0, hd_l, hpn, hpd, hrc, hj0,
    fun ci hci => (hstrong ci hci).1, fun ci hci => (hstrong ci hci).2,
    hdJ, hmw, hphiDs, hgExp, hgDel, htau2, htau1, hmaxEnd⟩

private lemma valid_inputs_cost_and_out {inp₁ inp₂ : WitnessCoreInput}
    {ce : ConstructExpanderImpl} {pds : PathDSParams} {mem mem' : ℕ → ℕ} {w v : ℕ}
    (h1 : inp₁.Valid ce pds mem w) (h2 : inp₂.Valid ce pds mem w)
    (hj : inp₁.prep.jAddr = inp₂.prep.jAddr)
    (hs : inp₁.statsAddr = inp₂.statsAddr)
    (hd : inp₁.prep.decAddr = inp₂.prep.decAddr)
    (hhp : inp₁.prep.h = inp₂.prep.h)
    (hh : inp₁.h = inp₂.h) :
    buildWitnessCoreCost inp₁ ce pds = buildWitnessCoreCost inp₂ ce pds ∧
      (∀ WSubs, inp₁.ValidWSubs ce WSubs →
        inp₁.OutputAt ce pds mem mem' v (inp₁.mkWitnessData ce pds WSubs) →
        inp₂.ValidWSubs ce WSubs ∧
          inp₂.OutputAt ce pds mem mem' v (inp₂.mkWitnessData ce pds WSubs)) := by
  have hag := valid_inputs_agree h1 h2 hj hs hd hhp hh
  have hcompW : ∀ (ci : ℕ) (hci : ci < inp₁.prep.rawComps.length),
      inp₁.compWeights inp₁.prep.rawComps[ci] =
        inp₂.compWeights (inp₂.prep.rawComps[ci]'(by rw [← hag.hrc]; exact hci)) := by
    intro ci hci
    unfold WitnessCoreInput.compWeights
    dsimp only
    have hci2 : ci < inp₂.prep.rawComps.length := by rw [← hag.hrc]; exact hci
    have hrc_eq : inp₁.prep.rawComps[ci] = inp₂.prep.rawComps[ci] := by simp [hag.hrc]
    rw [hag.hcJSub ci hci, hag.hpn, hag.hpd, hrc_eq]
  have hcost : buildWitnessCoreCost inp₁ ce pds = buildWitnessCoreCost inp₂ ce pds := by
    have hstep : ∀ ci < inp₁.prep.rawComps.length, ceStepCost inp₁ ce ci = ceStepCost inp₂ ce ci := by
      intro ci hci
      have hci2 : ci < inp₂.prep.rawComps.length := by rw [← hag.hrc]; exact hci
      have hrc_eq : inp₁.prep.rawComps[ci] = inp₂.prep.rawComps[ci] := by simp [hag.hrc]
      have hcw_ci := hcompW ci hci
      unfold ceStepCost
      dsimp only
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hci,
        List.getElem?_eq_getElem hci2, Option.getD_some]
      rw [hcw_ci, hrc_eq]
    have hrc_sum : rangeCost (ceStepCost inp₁ ce) 0 inp₁.prep.rawComps.length =
        rangeCost (ceStepCost inp₂ ce) 0 inp₂.prep.rawComps.length := by
      rw [← congrArg List.length hag.hrc]
      exact rangeCost_congr hstep
    unfold buildWitnessCoreCost phase01Cost ceLoopCost cePhase3Cost
    rw [hrc_sum, hag.hJ0, hag.hdJ, hag.hmw, hag.hrc]
  refine ⟨hcost, ?_⟩
  intro WSubs hws hout
  have hws2 : inp₂.ValidWSubs ce WSubs := by
    refine ⟨by rw [← hag.hrc]; exact hws.1, fun ci hci => ?_⟩
    have hci1 : ci < inp₁.prep.rawComps.length := by rw [hag.hrc]; exact hci
    rcases hws.2 ci hci1 with ⟨hn, hv, hexp, hdeg⟩
    have hrc_eq : inp₂.prep.rawComps[ci] = inp₁.prep.rawComps[ci] := by simp [hag.hrc]
    have hcw_eq := (hcompW ci hci1).symm
    dsimp only
    refine ⟨by rw [hrc_eq]; exact hn, hv, hexp, fun k hk => ?_⟩
    have hk1 : k < inp₁.prep.rawComps[ci].2.length := by rw [← hrc_eq]; exact hk
    have hdk := hdeg k hk1
    have hopt := congrArg (·[k]?) hcw_eq
    have hkl2 : k < (inp₂.compWeights inp₂.prep.rawComps[ci]).length := by
      simp [WitnessCoreInput.compWeights]; exact hk
    have hkl1 : k < (inp₁.compWeights inp₁.prep.rawComps[ci]).length := by
      simp [WitnessCoreInput.compWeights]; exact hk1
    rw [List.getElem?_eq_getElem hkl2, List.getElem?_eq_getElem hkl1] at hopt
    have hget : (inp₂.compWeights inp₂.prep.rawComps[ci])[k]'hkl2 =
        (inp₁.compWeights inp₁.prep.rawComps[ci])[k]'hkl1 := Option.some.inj hopt
    simpa only [hget] using hdk
  have hcs_eq : inp₁.buildCompsFrom inp₁.prep.j0Edges.length inp₁.prep.rawComps WSubs =
      inp₂.buildCompsFrom inp₂.prep.j0Edges.length inp₂.prep.rawComps WSubs := by
    have hlen1 := WitnessCoreInput.buildCompsFrom_length inp₁ inp₁.prep.j0Edges.length
      inp₁.prep.rawComps WSubs hws.1
    have hlen2 := WitnessCoreInput.buildCompsFrom_length inp₂ inp₂.prep.j0Edges.length
      inp₂.prep.rawComps WSubs hws2.1
    refine List.ext_getElem (by rw [hlen1, hlen2, hag.hrc]) fun ci h1c h2c => ?_
    have hci1 : ci < inp₁.prep.rawComps.length := by rwa [← hlen1]
    have hci2 : ci < inp₂.prep.rawComps.length := by rw [← hag.hrc]; exact hci1
    have g1 := buildCompsFrom_getElem inp₁ inp₁.prep.j0Edges.length inp₁.prep.rawComps WSubs hws.1 ci hci1
    have g2 := buildCompsFrom_getElem inp₂ inp₂.prep.j0Edges.length inp₂.prep.rawComps WSubs hws2.1 ci hci2
    have hrc_eq : inp₁.prep.rawComps[ci] = inp₂.prep.rawComps[ci] := by simp [hag.hrc]
    have hj0_len : inp₁.prep.j0Edges.length = inp₂.prep.j0Edges.length := by rw [hag.hj0]
    refine compInfo_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [g1.2.2.1, g2.2.2.1, hrc_eq]
    · rw [g1.2.2.2.1, g2.2.2.2.1, hrc_eq]
    · rw [g1.2.2.2.2.1, g2.2.2.2.2.1, hrc_eq]
    · rw [g1.2.2.2.2.2.1, g2.2.2.2.2.2.1, hag.hcJSub ci hci1]
    · rw [g1.2.2.2.2.2.2.1, g2.2.2.2.2.2.2.1, hag.hcJOrig ci hci1]
    · rw [g1.2.1, g2.2.1]
    · rw [g1.1, g2.1, hj0_len]
  set wd₁ := inp₁.mkWitnessData ce pds WSubs
  set wd₂ := inp₂.mkWitnessData ce pds WSubs
  have hwd_comps : wd₁.comps = wd₂.comps := hcs_eq
  have hwd_W : wd₁.W = wd₂.W := by
    simp only [wd₁, wd₂, WitnessCoreInput.mkWitnessData]
    rw [hcs_eq, hag.hJ, hag.hj0]
  have hwd_wW : wd₁.wW = wd₂.wW := by
    funext e
    simp only [wd₁, wd₂, WitnessCoreInput.mkWitnessData, witnessWeight]
    rw [hcs_eq, hag.hpn, hag.hpd, hag.hj0]
  have hwd_wSrc : wd₁.wSources = wd₂.wSources := by
    simp only [wd₁, wd₂, WitnessCoreInput.mkWitnessData]
    rw [hcs_eq, hag.hj0]
  have hwd_jSrc : wd₁.jSources = wd₂.jSources := by
    simp only [wd₁, wd₂, WitnessCoreInput.mkWitnessData]
    rw [hcs_eq, hag.hj0, hag.hJ]
  refine ⟨hws2, ?_⟩
  rcases hout with ⟨hb, hzf, hle, hmax, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9,
    hm10, hm11, hm17, hm18, hm19, ha20, haext, hwnum, hwsrc, hjsrc, hjend, hcext, hgr, hww, hwsa, hjsa⟩
  refine ⟨by rw [← hh]; exact hb, hzf, by rw [← hh]; exact hle, by rw [← hag.hmaxEnd]; exact hmax,
    by rw [← hh, ← hag.hmw]; exact hm0, by rw [← hh, ← hag.hdJ, ← hag.hJ0]; exact hm1,
    by rw [← hh, ← hag.hdJ, ← hag.hJ0]; exact hm2, by rw [← hh, ← hag.hdJ, ← hag.hJ0]; exact hm3,
    by rw [← hh, ← hag.hmw]; exact hm4, by rw [← hh, ← hag.hmw]; exact hm5,
    by rw [← hh, ← hag.hmw]; exact hm6, by rw [← hh, ← hag.hphiDs]; exact hm7,
    by rw [← hh, ← hag.hgExp]; exact hm8, by rw [← hh, ← hag.hgDel]; exact hm9,
    by rw [← hh, ← hag.htau1]; exact hm10, by rw [← hh, ← hag.htau2]; exact hm11,
    by rw [← hh, ← hag.hpn]; exact hm17, by rw [← hh, ← hag.hpd]; exact hm18,
    by rw [← hh, ← hag.hJ0]; exact hm19, by rw [← hh]; exact ha20,
    by rw [← hh, ← hwd_comps]; exact haext,
    by rw [← hh, ← hwd_W]; exact hwnum,
    by rw [← hh, ← hwd_W]; exact hwsrc,
    by rw [← hh, ← hwd_W]; exact hjsrc,
    by rw [← hh, ← hag.hJ]; exact hjend,
    by rw [← hh, ← hag.hpn, ← hwd_comps]; exact hcext,
    by rw [← hh, ← hwd_W]; exact hgr,
    fun eW heW => by
      rw [← hwd_W] at heW
      have hw := hww eW heW
      rw [← hh, ← hag.hpd, ← hwd_wW]
      exact hw,
    by rw [← hh, ← hwd_wSrc]; exact hwsa,
    by rw [← hh, ← hwd_jSrc]; exact hjsa⟩

/-- Convert `AsmPost` plus `inp.h + 20 ≤ st.mem (inp.h + 12)` into `WitnessCoreInput.OutputAt`. -/
lemma asmPost_to_outputAt {w : ℕ} {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {mem₀ : ℕ → ℕ} {st : State}
    (hvalid : inp.Valid ce pds mem₀ w)
    (hpost : AsmPost inp ce pds mem₀ st)
    (ha20 : inp.h + 20 ≤ st.mem (inp.h + 12)) :
    ∃ WSubs, inp.ValidWSubs ce WSubs ∧
      inp.OutputAt ce pds mem₀ st.mem (st.regs 28) (inp.mkWitnessData ce pds WSubs) := by
  rcases hpost with ⟨aCompExt, wAddr, WSubs, hr28, hws, ha_ext, hmax_le, hbelow, hhdr0,
    hm12, hm13, hm14, hm15, hm16, hgraph, hw_j0, hw_comp, hws_at, hjs_at, hcomp_ext, hzf⟩
  set wd := inp.mkWitnessData ce pds WSubs
  have hclen : wd.comps.length = inp.prep.rawComps.length :=
    WitnessCoreInput.buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hv := hvalid.2.2.1
  have hpn1 : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have h_le_v : inp.h ≤ st.regs 28 := by
    have h1 : inp.h + 20 ≤ aCompExt := by rw [← hm12]; exact ha20
    have h2 : aCompExt ≤ wAddr := le_trans (Nat.le_add_right _ _) ha_ext
    have h3 : wAddr ≤ st.regs 28 := by rw [hr28]; omega
    omega
  refine ⟨WSubs, hws, hbelow, ?_, h_le_v, ?_, hhdr0.1, hhdr0.2.1, hhdr0.2.2.1, hhdr0.2.2.2.1,
    hhdr0.2.2.2.2.1, hhdr0.2.2.2.2.2.1, hhdr0.2.2.2.2.2.2.1, hhdr0.2.2.2.2.2.2.2.1,
    hhdr0.2.2.2.2.2.2.2.2.1, hhdr0.2.2.2.2.2.2.2.2.2.1, hhdr0.2.2.2.2.2.2.2.2.2.2.1,
    hhdr0.2.2.2.2.2.2.2.2.2.2.2.1, hhdr0.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hhdr0.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hhdr0.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    ha20, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr28]; exact hzf
  · rw [hr28]; exact hmax_le
  · rw [hm12, hm13, hclen]; exact ha_ext
  · rw [hm13, hm14]
  · rw [hm14, hm15]
  · rw [hm15, hm16]
  · rw [hr28, hm16]
  · rw [hm12, hm13]; exact hcomp_ext
  · rw [hm13]; exact hgraph
  · intro eW heW
    rw [hm14]
    rcases lt_or_ge eW inp.prep.j0Edges.length with heW_j0 | heW_comp
    · refine ⟨?_, ?_⟩
      · rw [hw_j0 eW heW_j0]
        exact (WitnessCoreInput.mkWitnessData_wW_j0 heW_j0).symm
      · rw [hw_j0 eW heW_j0]; exact hpn1
    · have haligned := WitnessCoreInput.buildCompsFrom_aligned inp inp.prep.j0Edges.length
        inp.prep.rawComps WSubs hws.1
      have hsum_m : (wd.comps.map fun c => c.W_sub.m).sum = (WSubs.map Graph.m).sum := by
        have hcongr : List.map (fun c => c.W_sub.m) wd.comps = List.map Graph.m WSubs := by
          refine List.ext_getElem (by rw [List.length_map, List.length_map, hclen, hws.1]) fun i hi1 hi2 => ?_
          have hi : i < inp.prep.rawComps.length := by rw [List.length_map, hclen] at hi1; exact hi1
          have hwi := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 i hi
          simp only [List.getElem_map]
          change ((inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs)[i]'(by
              rw [WitnessCoreInput.buildCompsFrom_length _ _ _ _ hws.1]; exact hi)).W_sub.m =
            (WSubs[i]'(by rw [hws.1]; exact hi)).m
          rw [hwi.2.1]
        exact congrArg List.sum hcongr
      have hwm_eq := mkWitnessData_W_m_eq_sum inp ce pds hws.1
      have heW_lt_sum : eW < inp.prep.j0Edges.length + (wd.comps.map fun c => c.W_sub.m).sum := by
        rw [hsum_m, ← hwm_eq]; exact heW
      rcases compsAligned_find_wStart haligned eW heW_comp heW_lt_sum with ⟨ci, hci_c, hws_le, hws_lt⟩
      have hws_le' : wd.comps[ci].wStart ≤ eW := hws_le
      have hws_lt' : eW < wd.comps[ci].wStart + wd.comps[ci].W_sub.m := hws_lt
      let eL := eW - wd.comps[ci].wStart
      have heL : eL < wd.comps[ci].W_sub.m := Nat.sub_lt_left_of_lt_add hws_le' hws_lt'
      have hwIdx : wd.comps[ci].wStart + eL = eW := Nat.add_sub_cancel' hws_le'
      have hgetd_ci : wd.comps.getD ci defaultCompInfo = wd.comps[ci] := by
        dsimp only [wd, WitnessCoreInput.mkWitnessData]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hci_c, Option.getD_some]
      have hmem_c := hw_comp ci hci_c eL (by rwa [hgetd_ci])
      rw [hgetd_ci, Nat.add_assoc, hwIdx] at hmem_c
      have hww := WitnessCoreInput.mkWitnessData_wW_comp hws hci_c heL
      dsimp only at hww
      rw [hwIdx] at hww
      refine ⟨?_, ?_⟩
      · rw [hmem_c, ← hww]
      · rw [hmem_c]
        exact Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hpn1) (Nat.pow_pos (by omega))
  · rw [hm15]; exact hws_at
  · rw [hm16]; exact hjs_at

/-- Full Hoare triple for `buildWitnessCoreBody`. -/
theorem buildWitnessCore_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pdsImpl : PathDSImpl} {ceBase boundsBase : ℕ}
    {mem₀ : ℕ → ℕ} {pos : ℕ}
    (hce : p.HasAt ceBase (ce.procs ceBase))
    (hbounds : p.HasAt boundsBase (pdsImpl.boundsProcs boundsBase))
    (hvalid : inp.Valid ce pdsImpl.params mem₀ w) :
    Triple w p
      (fun st => st = startState [inp.prep.jAddr, inp.statsAddr, inp.prep.decAddr, inp.prep.h, inp.h] mem₀ pos)
      (buildWitnessCoreBody ce.phiNum ce.phiDen ce.c_deg_int ceBase boundsBase)
      (retPost fun v st' =>
        ∃ WSubs, inp.ValidWSubs ce WSubs ∧
          inp.OutputAt ce pdsImpl.params mem₀ st'.mem v (inp.mkWitnessData ce pdsImpl.params WSubs))
      (fun _ => buildWitnessCoreCost inp ce pdsImpl.params) := by
  have hmax_w : inp.maxHeapEnd ce pdsImpl.params < 2 ^ w := (ce_word_bounds hvalid).2.1
  have hret : Triple w p
      (fun st => AsmPost inp ce pdsImpl.params mem₀ st ∧ inp.h + 20 ≤ st.mem (inp.h + 12))
      (Stmt.ret (.reg 28))
      (retPost fun v st' =>
        ∃ WSubs, inp.ValidWSubs ce WSubs ∧
          inp.OutputAt ce pdsImpl.params mem₀ st'.mem v (inp.mkWitnessData ce pdsImpl.params WSubs))
      (fun _ => 2) := by
    refine (Triple.ret (val := fun st => st.regs 28) ?_ ?_).mono_cost
      (fun _ _ => by simp [Expr.size])
    · intro st hp
      rcases hp.1 with ⟨_, _, _, hr28, _, _, hmax_le, _⟩
      exact ev_reg rfl (by rw [hr28]; exact lt_of_le_of_lt hmax_le hmax_w)
    · intro st hp
      exact asmPost_to_outputAt hvalid hp.1 hp.2
  have h34 := Triple.seq_normal_const (buildAssemble_triple hvalid) hret
  have h234 := Triple.seq_normal_const (buildCeLoop_triple hce hvalid) h34
  have h1234 := Triple.seq_normal_const (buildPhase01_triple (pos := pos) hbounds hvalid) h234
  exact h1234.mono_cost fun _ _ => by unfold buildWitnessCoreCost; omega

section Contract
open Classical

/-- Procedure contract for `buildWitnessCoreModule`. -/
noncomputable def buildWitnessCoreContract (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (w : ℕ) : Contract where
  pre := fun args mem =>
    ∃ inp : WitnessCoreInput,
      args = [inp.prep.jAddr, inp.statsAddr, inp.prep.decAddr, inp.prep.h, inp.h] ∧
      inp.Valid ce pds mem w
  post := fun args mem v mem' =>
    ∀ inp : WitnessCoreInput,
      args = [inp.prep.jAddr, inp.statsAddr, inp.prep.decAddr, inp.prep.h, inp.h] →
      inp.Valid ce pds mem w →
      ∃ WSubs, inp.ValidWSubs ce WSubs ∧
        inp.OutputAt ce pds mem mem' v (inp.mkWitnessData ce pds WSubs)
  cost := fun args mem =>
    if h : ∃ inp : WitnessCoreInput,
        args = [inp.prep.jAddr, inp.statsAddr, inp.prep.decAddr, inp.prep.h, inp.h] ∧
        inp.Valid ce pds mem w
    then buildWitnessCoreCost (Classical.choose h) ce pds
    else 0

/-- `buildWitnessCoreContract.cost` equals `buildWitnessCoreCost inp ce pds` on valid inputs. -/
lemma buildWitnessCoreContract_cost_eq {ce : ConstructExpanderImpl} {pds : PathDSParams} {w : ℕ}
    {inp : WitnessCoreInput} {mem : ℕ → ℕ} (hvalid : inp.Valid ce pds mem w) :
    (buildWitnessCoreContract ce pds w).cost
        [inp.prep.jAddr, inp.statsAddr, inp.prep.decAddr, inp.prep.h, inp.h] mem =
      buildWitnessCoreCost inp ce pds := by
  have hex : ∃ inp' : WitnessCoreInput,
      [inp.prep.jAddr, inp.statsAddr, inp.prep.decAddr, inp.prep.h, inp.h] =
        [inp'.prep.jAddr, inp'.statsAddr, inp'.prep.decAddr, inp'.prep.h, inp'.h] ∧
      inp'.Valid ce pds mem w := ⟨inp, rfl, hvalid⟩
  simp only [buildWitnessCoreContract, hex, ↓reduceDIte]
  have hspec := Classical.choose_spec hex
  have heq := List.cons.inj hspec.1
  have heq2 := List.cons.inj heq.2
  have heq3 := List.cons.inj heq2.2
  have heq4 := List.cons.inj heq3.2
  have heq5 := List.cons.inj heq4.2
  exact (valid_inputs_cost_and_out hspec.2 hvalid (mem' := mem) (v := 0)
    heq.1.symm heq2.1.symm heq3.1.symm heq4.1.symm heq5.1.symm).1

/-- Contract satisfaction theorem for `buildWitnessCoreModule`. -/
theorem buildWitnessCore_meetsContract {w : ℕ} {p : Program}
    {ce : ConstructExpanderImpl} {pdsImpl : PathDSImpl} {base ceBase boundsBase : ℕ}
    (hself : p.HasAt base (buildWitnessCoreModule ce.phiNum ce.phiDen ce.c_deg_int ceBase boundsBase))
    (hce : p.HasAt ceBase (ce.procs ceBase))
    (hbounds : p.HasAt boundsBase (pdsImpl.boundsProcs boundsBase)) :
    MeetsContract w p base (buildWitnessCoreContract ce pdsImpl.params w) := by
  intro args mem pos ω _ hpre
  rcases hpre with ⟨inp, rfl, hvalid⟩
  have hbody : p.procs[base]? =
      some (buildWitnessCoreBody ce.phiNum ce.phiDen ce.c_deg_int ceBase boundsBase) := by
    simpa [buildWitnessCoreModule] using hself 0 Nat.zero_lt_one
  refine ⟨_, hbody, ?_⟩
  rcases buildWitnessCore_triple hce hbounds hvalid (startState _ mem pos) ω rfl with
    ⟨o, st', c, hruns, hpost, hcost⟩
  cases o with
  | normal => exact False.elim hpost
  | returned v =>
    refine ⟨Outcome.returned v, st', c, hruns, ?_, ?_⟩
    · intro inp' hargs' hvalid'
      have heq := List.cons.inj hargs'
      have heq2 := List.cons.inj heq.2
      have heq3 := List.cons.inj heq2.2
      have heq4 := List.cons.inj heq3.2
      have heq5 := List.cons.inj heq4.2
      rcases hpost with ⟨WSubs, hws, hout⟩
      exact ⟨WSubs, (valid_inputs_cost_and_out hvalid hvalid' heq.1 heq2.1 heq3.1 heq4.1 heq5.1).2
        WSubs hws hout⟩
    · rw [buildWitnessCoreContract_cost_eq hvalid]
      exact hcost

end Contract

end MinCostFlow.Spanner
