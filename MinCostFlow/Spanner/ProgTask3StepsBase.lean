module

public import MinCostFlow.Spanner.ProgTask3SetupProof

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# Round Invariants and `t3DrainQueue` Verification for Task 3

Defines `T3RoundData`, potential `t3RoundPhi`, round-level invariant `T3RoundAt`, and
proves `t3DrainQueue_ptriple` (`selfBase + 2`).
-/

/-- Ghost state tracked across one Task 3 round (`r_cur = η_prev + 1`). -/
structure T3RoundData (pdsImpl : PathDSImpl) where
  emb : ℕ → Option Walk
  getPathCnt : ℕ
  delCnt : ℕ
  econgUpd : ℕ
  hCur : ℕ
  states : ℕ → PathDSAbsState
  reps : ℕ → pdsImpl.R.τ
  nextHasUnemb : ℕ

def T3RoundData.toOuter {pdsImpl : PathDSImpl} (d : T3RoundData pdsImpl) : T3OuterData where
  emb := d.emb
  getPathCnt := d.getPathCnt
  delCnt := d.delCnt
  econgUpd := d.econgUpd
  hCur := d.hCur

/-- Amortized weight per newly uncommitted congestion unit (pays `t3DrainQueue`). -/
noncomputable def t3KdelCost (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  ⌈impl.pathDS.params.K_del *
    (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl J) : ℝ)⌉₊ + 140

/-- Remaining non-isolated vertices across all `W_sub` expanders in the current round. -/
def t3VhatRem (wd : WitnessData) (states : ℕ → PathDSAbsState) : ℕ :=
  ∑ ci ∈ Finset.range wd.comps.length,
    ((Finset.range (wd.comps.getD ci defaultCompInfo).W_sub.n).filter
      (· ∉ (states ci).Vhat)).card

/-- Potential used during a Task 3 round (`r_cur`). -/
noncomputable def t3RoundPhi {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (d : T3RoundData impl.pathDS)
    (mem : ℕ → ℕ) : ℕ :=
  t3KdelCost impl inp.J * t3EcongPhi ctx lay mem +
    dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length d.reps mem +
    25 * t3VhatRem ctx.wd d.states

lemma t3VhatRem_le {wd : WitnessData} {states : ℕ → PathDSAbsState} {m : ℕ}
    (hvhat_sum : (wd.comps.map fun c => c.W_sub.n).sum ≤ 2 * m) :
    t3VhatRem wd states ≤ 2 * m := by
  unfold t3VhatRem
  calc ∑ ci ∈ Finset.range wd.comps.length,
        ((Finset.range (wd.comps.getD ci defaultCompInfo).W_sub.n).filter
          (· ∉ (states ci).Vhat)).card
      ≤ ∑ ci ∈ Finset.range wd.comps.length,
          (Finset.range (wd.comps.getD ci defaultCompInfo).W_sub.n).card :=
        Finset.sum_le_sum fun ci _ => Finset.card_le_card (Finset.filter_subset _ _)
    _ = ∑ ci ∈ Finset.range wd.comps.length, (wd.comps.getD ci defaultCompInfo).W_sub.n :=
        Finset.sum_congr rfl fun ci _ => Finset.card_range _
    _ = (wd.comps.map fun c => c.W_sub.n).sum := by
        induction wd.comps using List.reverseRecOn with
        | nil => simp
        | append_singleton l a ih =>
          simp only [List.length_append, List.length_singleton, Finset.sum_range_succ,
            List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
          have hget : (l ++ [a]).getD l.length defaultCompInfo = a := by simp
          rw [hget]
          have hcongr : ∑ x ∈ Finset.range l.length, ((l ++ [a]).getD x defaultCompInfo).W_sub.n =
              ∑ x ∈ Finset.range l.length, (l.getD x defaultCompInfo).W_sub.n := by
            refine Finset.sum_congr rfl fun x hx => ?_
            have hx' := Finset.mem_range.mp hx
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hx']
          rw [hcongr, ih]
    _ ≤ 2 * m := hvhat_sum

lemma t3VhatRem_update {wd : WitnessData} {states : ℕ → PathDSAbsState} {ci : ℕ}
    (hci : ci < wd.comps.length) {s' : PathDSAbsState} {L : List ℕ}
    (hsub_old : (states ci).Vhat ⊆ s'.Vhat)
    (hsub_new : s'.Vhat ⊆ Finset.range (wd.comps[ci]'hci).W_sub.n)
    (hL_nd : L.Nodup)
    (hL_fin : L.toFinset = s'.Vhat \ (states ci).Vhat) :
    t3VhatRem wd states = t3VhatRem wd (Function.update states ci s') + L.length := by
  unfold t3VhatRem
  have hci_fin : ci ∈ Finset.range wd.comps.length := Finset.mem_range.mpr hci
  rw [← Finset.add_sum_erase _ _ hci_fin, ← Finset.add_sum_erase _ _ hci_fin]
  have hrest :
      ∑ cj ∈ (Finset.range wd.comps.length).erase ci,
        ((Finset.range (wd.comps.getD cj defaultCompInfo).W_sub.n).filter
          (· ∉ (Function.update states ci s' cj).Vhat)).card =
      ∑ cj ∈ (Finset.range wd.comps.length).erase ci,
        ((Finset.range (wd.comps.getD cj defaultCompInfo).W_sub.n).filter
          (· ∉ (states cj).Vhat)).card := by
    refine Finset.sum_congr rfl fun cj hcj => ?_
    rw [Function.update_of_ne (Finset.mem_erase.mp hcj).1]
  rw [hrest, Function.update_self]
  set R := Finset.range (wd.comps.getD ci defaultCompInfo).W_sub.n
  have hR_eq : R = Finset.range (wd.comps[ci]'hci).W_sub.n := by
    dsimp only [R]; rw [List.getD_eq_getElem _ _ hci]
  have hsub_new' : s'.Vhat ⊆ R := hR_eq ▸ hsub_new
  have hA : R \ (states ci).Vhat = (R \ s'.Vhat) ∪ (s'.Vhat \ (states ci).Vhat) := by
    ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · intro ⟨hxR, hxno⟩
      by_cases h : x ∈ s'.Vhat
      · exact Or.inr ⟨h, hxno⟩
      · exact Or.inl ⟨hxR, h⟩
    · rintro (⟨hxR, hxno⟩ | ⟨hxs, hxno⟩)
      · exact ⟨hxR, fun hx => hxno (hsub_old hx)⟩
      · exact ⟨hsub_new' hxs, hxno⟩
  have hfilt1 : R.filter (· ∉ (states ci).Vhat) = R \ (states ci).Vhat := by ext x; simp [Finset.mem_sdiff]
  have hfilt2 : R.filter (· ∉ s'.Vhat) = R \ s'.Vhat := by ext x; simp [Finset.mem_sdiff]
  have hdisj : Disjoint (R \ s'.Vhat) (s'.Vhat \ (states ci).Vhat) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx1).2 (Finset.mem_sdiff.mp hx2).1
  have hL_card : L.length = (s'.Vhat \ (states ci).Vhat).card := by
    rw [← hL_fin, List.toFinset_card_of_nodup hL_nd]
  rw [hfilt1, hfilt2, hA, Finset.card_union_of_disjoint hdisj, hL_card]
  omega

lemma t3EcongPhi_frame {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) {mem mem' : ℕ → ℕ}
    (hcnt : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      mem' (lay.econgCountAddr + eW) = mem (lay.econgCountAddr + eW))
    (hdel : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      mem' (lay.wDelStampAddr + eW) = mem (lay.wDelStampAddr + eW)) :
    t3EcongPhi ctx lay mem' = t3EcongPhi ctx lay mem := by
  unfold t3EcongPhi
  refine Finset.sum_congr rfl fun eW heW => ?_
  rw [hcnt eW heW, hdel eW heW]

lemma t3_seqAt_nodup_add_le {mem : ℕ → ℕ} {hOld hNew : ℕ} {L : List ℕ}
    (hnd : L.Nodup) (hseq : WordRAM.SeqAt mem hOld L) (hz : WordRAM.ZeroFrom mem hNew)
    (hle : hOld ≤ hNew) :
    hOld + 1 + L.length ≤ hNew + 2 := by
  by_cases h0 : L.length = 0
  · rw [h0]; omega
  · let j := L.length - 1
    have hj : j < L.length := by omega
    by_cases hnz : L[j]'hj ≠ 0
    · have hmem : mem (hOld + 1 + j) ≠ 0 := by rw [listAt_getElem hseq.2 hj]; exact hnz
      have hlt : hOld + 1 + j < hNew := by
        by_contra hge
        exact hmem (hz _ (by omega))
      omega
    · push Not at hnz
      by_cases hj0 : j = 0
      · omega
      · have hj1 : j - 1 < L.length := by omega
        have hne : L[j - 1]'hj1 ≠ L[j]'hj := fun h => by
          have := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨j - 1, hj1⟩) (a₂ := ⟨j, hj⟩) h
          simp at this; omega
        have hnz1 : L[j - 1]'hj1 ≠ 0 := fun h => hne (h.trans hnz.symm)
        have hlt1 : hOld + 1 + (j - 1) < hNew := by
          by_contra hge
          have hmem : mem (hOld + 1 + (j - 1)) = L[j - 1]'hj1 := listAt_getElem hseq.2 hj1
          exact hnz1 (hmem ▸ hz _ (by omega))
        omega

lemma wSources_comp_of_Ico {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) {eW : ℕ}
    (heW_lo : ctx.wd.j0Edges.length ≤ eW) (heW_hi : eW < ctx.wd.W.m) :
    ∃ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (eL : ℕ),
      eL < ctx.wd.comps[ci].W_sub.m ∧
      ctx.wd.comps[ci].wStart + eL = eW ∧
      ctx.wd.wSources.length = ctx.wd.W.m ∧
      ctx.wd.wSources[eW]'(by
        have hwm := ctx.hw_okW.W_m_eq
        have hj0_len : ctx.wd.j0Edges.length = ctx.wInp.prep.j0Edges.length := rfl
        change eW < (List.map WEdgeSource.fromJ0 ctx.wInp.prep.j0Edges ++
          List.flatMap (fun x => List.map (fun eL => WEdgeSource.fromComp x.2 eL)
            (List.range x.1.W_sub.m)) (ctx.wd.comps.zipIdx 0)).length
        rw [List.length_append, List.length_map, List.length_flatMap]
        have hmap : (List.map (fun x : CompInfo × ℕ =>
            (List.map (fun eL => WEdgeSource.fromComp x.2 eL) (List.range x.1.W_sub.m)).length)
            (ctx.wd.comps.zipIdx 0)) = List.map (fun c : CompInfo => c.W_sub.m) ctx.wd.comps :=
          List.ext_getElem (by simp) fun j _ _ => by simp
        rw [hmap]
        change eW < ctx.wInp.prep.j0Edges.length + (List.map (fun c : CompInfo => c.W_sub.m) ctx.wd.comps).sum
        omega) = WEdgeSource.fromComp ci eL := by
  have hwm := ctx.hw_okW.W_m_eq
  have hj0_len : ctx.wd.j0Edges.length = ctx.wInp.prep.j0Edges.length := rfl
  have hj0_eq : ctx.wd.j0Edges = ctx.wInp.prep.j0Edges := rfl
  have heW_sum : eW < ctx.wInp.prep.j0Edges.length + (ctx.wd.comps.map fun c => c.W_sub.m).sum := by
    rw [hj0_eq] at heW_lo; omega
  rcases compsAligned_find_wStart ctx.hw_okW.aligned eW (hj0_eq ▸ heW_lo) heW_sum with
    ⟨ci, hci, hle, hlt⟩
  let eL := eW - ctx.wd.comps[ci].wStart
  have heL : eL < ctx.wd.comps[ci].W_sub.m := Nat.sub_lt_left_of_lt_add hle hlt
  have hflat := compsAligned_flatMap_wSources (base := 0) ctx.hw_okW.aligned ci hci eL heL
  rcases hflat with ⟨hidx_f, hval_f⟩
  have hlen : ctx.wd.wSources.length = ctx.wd.W.m := by
    change (List.map WEdgeSource.fromJ0 ctx.wInp.prep.j0Edges ++
      List.flatMap (fun x => List.map (fun eL => WEdgeSource.fromComp x.2 eL)
        (List.range x.1.W_sub.m)) (ctx.wd.comps.zipIdx 0)).length = ctx.wd.W.m
    rw [List.length_append, List.length_map, List.length_flatMap]
    have hmap : (List.map (fun x : CompInfo × ℕ =>
        (List.map (fun eL => WEdgeSource.fromComp x.2 eL) (List.range x.1.W_sub.m)).length)
        (ctx.wd.comps.zipIdx 0)) = List.map (fun c : CompInfo => c.W_sub.m) ctx.wd.comps :=
      List.ext_getElem (by simp) fun j _ _ => by simp
    rw [hmap]
    change ctx.wInp.prep.j0Edges.length + (List.map (fun c : CompInfo => c.W_sub.m) ctx.wd.comps).sum =
      ctx.wd.W.m
    exact hwm.symm
  have hsrc_eq : ctx.wd.wSources[eW]'(by omega) =
      (List.map WEdgeSource.fromJ0 ctx.wInp.prep.j0Edges ++
        List.flatMap (fun x => List.map (fun eL => WEdgeSource.fromComp x.2 eL)
          (List.range x.1.W_sub.m)) (ctx.wd.comps.zipIdx 0))[eW]'(by
            change eW < ctx.wd.wSources.length; omega) := rfl
  have hge_ws : ctx.wd.j0Edges.length ≤ ctx.wd.comps[ci].wStart :=
    compsAligned_wStart_ge ctx.hw_okW.aligned ctx.wd.comps[ci] (List.getElem_mem hci)
  have hsrc : ctx.wd.wSources[eW]'(by omega) = WEdgeSource.fromComp ci eL := by
    rw [hsrc_eq, List.getElem_append_right (by rw [List.length_map]; exact hj0_eq ▸ heW_lo)]
    simp only [List.length_map]
    have hdiff : eW - ctx.wInp.prep.j0Edges.length =
        (ctx.wd.comps[ci].wStart - ctx.wInp.prep.j0Edges.length) + eL := by
      dsimp only [eL]; omega
    calc (List.flatMap (fun x => List.map (fun eL => WEdgeSource.fromComp x.2 eL)
          (List.range x.1.W_sub.m)) (ctx.wd.comps.zipIdx 0))[eW - ctx.wInp.prep.j0Edges.length]'_ =
          (List.flatMap (fun x => List.map (fun eL => WEdgeSource.fromComp x.2 eL)
            (List.range x.1.W_sub.m)) (ctx.wd.comps.zipIdx 0))[
            ctx.wd.comps[ci].wStart - ctx.wInp.prep.j0Edges.length + eL]'hidx_f := by congr 1
      _ = WEdgeSource.fromComp (0 + ci) eL := hval_f
      _ = WEdgeSource.fromComp ci eL := by simp
  exact ⟨ci, hci, eL, heL, Nat.add_sub_cancel' hle, hlen, hsrc⟩

lemma wStart_add_inj {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) {ci₁ ci₂ eL₁ eL₂ : ℕ}
    (h1 : ci₁ < ctx.wd.comps.length) (h2 : ci₂ < ctx.wd.comps.length)
    (he1 : eL₁ < ctx.wd.comps[ci₁].W_sub.m) (he2 : eL₂ < ctx.wd.comps[ci₂].W_sub.m)
    (heq : ctx.wd.comps[ci₁].wStart + eL₁ = ctx.wd.comps[ci₂].wStart + eL₂) :
    ci₁ = ci₂ ∧ eL₁ = eL₂ := by
  by_cases hci : ci₁ = ci₂
  · subst hci; exact ⟨rfl, by omega⟩
  · exfalso
    rcases Nat.lt_or_gt_of_ne hci with hlt | hlt
    · have := compsAligned_adjacent ctx.hw_okW.aligned ci₁ ci₂ h1 h2 hlt; omega
    · have := compsAligned_adjacent ctx.hw_okW.aligned ci₂ ci₁ h2 h1 hlt; omega

/-- Complete invariant maintained across calls to `t3MiddleEdge` within round `rCur`. -/
structure T3RoundAt {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (rCur : ℕ)
    (d : T3RoundData impl.pathDS) (st : State) (Φ : ℕ) : Prop where
  rCur_pos : 1 ≤ rCur
  rCur_le : rCur ≤ eta2Bound inp.J
  staticMem : T3StaticMem ctx lay st.mem
  dsArr : DSArrayWAt impl.pathDS ctx.wd.comps impl.constructExpander.phiNum
    impl.constructExpander.phiDen ctx.wd.M_W w lay.staticEnd lay.dsHandlesAddr d.hCur
    st.mem ctx.wd.comps.length d.states d.reps
  hCur_lo : lay.staticEnd ≤ d.hCur
  hCur_bd : d.hCur ≤ Task3Input.staticEndCap impl inp + 5 * inp.J.m +
    (rCur * inp.J.m + d.getPathCnt + d.delCnt) * Task3Input.dsOneW impl inp.J +
    d.getPathCnt * (2 * impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J) + 3)
  zero_from : WordRAM.ZeroFrom st.mem d.hCur
  eta2_eq : st.mem (lay.base + t3OffEta2) + 1 = rCur
  getPath_eq : st.mem (lay.base + t3OffGetPath) = d.getPathCnt
  del_eq : st.mem (lay.base + t3OffDel) = d.delCnt
  econgUpd_eq : st.mem (lay.base + t3OffEcongUpd) = d.econgUpd
  hCur_eq : st.mem (lay.base + t3OffHCur) = d.hCur
  nextU_eq : st.mem (lay.base + t3OffNextU) = d.nextHasUnemb
  nextU_bin : d.nextHasUnemb = 0 ∨ d.nextHasUnemb = 1
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
        WalkAt st.mem (st.mem (lay.embJWAddr + eJ)) P ∧
        (∀ a, st.mem (lay.embJWAddr + eJ) ≤ a →
          a < st.mem (lay.embJWAddr + eJ) + P.encode.length →
          ∀ cj < ctx.wd.comps.length,
            ¬ impl.pathDS.R.foot (st.mem (lay.dsHandlesAddr + cj)) (d.reps cj) a)
  econg_cnt_eq : ∀ eW < ctx.wd.W.m,
    st.mem (lay.econgCountAddr + eW) =
      {eJ ∈ Finset.range inp.J.m | eW ∈ (partialToWalk d.emb eJ).edges}.card
  econg_le_round : ∀ eW < ctx.wd.W.m,
    econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk d.emb) eW ≤ ((rCur : ℝ) + 1 / 2) * ctx.wd.τ₂
  econg_j0_le : ∀ eW < ctx.wd.j0Edges.length,
    econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk d.emb) eW ≤ ctx.wd.τ₂ / 2
  wdel_j0 : ∀ eW < ctx.wd.j0Edges.length, st.mem (lay.wDelStampAddr + eW) = 0
  wdel_comp : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
    st.mem (lay.wDelStampAddr + eW) ≤ rCur ∧
    st.mem (lay.wDelStampAddr + eW) ≤ st.mem (lay.econgCountAddr + eW)
  wdel_thresh : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
    st.mem (lay.wDelStampAddr + eW) = rCur →
    (rCur : ℝ) * ctx.wd.τ₂ ≤ econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk d.emb) eW
  wdel_lt_econg : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
    st.mem (lay.wDelStampAddr + eW) < rCur →
    econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk d.emb) eW ≤ (rCur : ℝ) * ctx.wd.τ₂
  getPath_cnt_le : d.getPathCnt ≤ inp.J.m - (unembeddedSet2Pure inp.J d.emb).card
  econgUpd_sum : d.econgUpd = ∑ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
    st.mem (lay.econgCountAddr + eW)
  econgUpd_bound : (d.econgUpd : ℝ) ≤ (d.getPathCnt : ℝ) * ctx.wd.γ_ExpPath
  econgUpd_W : d.econgUpd ≤ d.getPathCnt *
    impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J)
  del_le_econgUpd : d.delCnt ≤ d.econgUpd
  del_iff : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (eL : ℕ),
    eL < ctx.wd.comps[ci].W_sub.m →
    (eL ∈ (d.states ci).deleted ↔
      st.mem (lay.wDelStampAddr + (ctx.wd.comps[ci].wStart + eL)) = rCur)
  vhat_stmp_eq : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (v : ℕ),
    v < ctx.wd.comps[ci].W_sub.n →
    (st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) = rCur ↔ v ∈ (d.states ci).Vhat)
  vhat_stmp_le : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (v : ℕ),
    v < ctx.wd.comps[ci].W_sub.n →
    st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) ≤ rCur
  phi_eq : Φ = t3RoundPhi ctx lay d st.mem

/-- Loop invariant for `t3DrainQueueBody` at queue index `0 ≤ qi ≤ Q.length`. -/
structure T3DrainQueueAt {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (rCur : ℕ)
    (Q : List ℕ) (g1 del0 eUpd1 : ℕ) (emb1 : ℕ → Option Walk) (nextU : ℕ) (qi : ℕ)
    (d : T3RoundData impl.pathDS) (st : State) (Φ : ℕ) : Prop where
  rCur_pos : 1 ≤ rCur
  rCur_le : rCur ≤ eta2Bound inp.J
  qi_le : qi ≤ Q.length
  Q_nd : Q.Nodup
  Q_len_le : Q.length ≤ impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
    (Task1Input.mwCap impl inp.J)
  g1_le : g1 ≤ inp.J.m
  del_le_eUpd : del0 + Q.length ≤ eUpd1
  eUpd_bound : (eUpd1 : ℝ) ≤ (g1 : ℝ) * ctx.wd.γ_ExpPath
  eUpd_W : eUpd1 ≤ g1 *
    impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J)
  queue_list : ListAt st.mem lay.queueAddr Q
  Q_valid : ∀ eW ∈ Q, ctx.wd.j0Edges.length ≤ eW ∧ eW < ctx.wd.W.m ∧
    st.mem (lay.wDelStampAddr + eW) = rCur
  d_emb : d.emb = emb1
  d_g : d.getPathCnt = g1
  d_del : d.delCnt = del0 + qi
  d_eUpd : d.econgUpd = eUpd1
  d_nextU : d.nextHasUnemb = nextU
  staticMem : T3StaticMem ctx lay st.mem
  dsArr : DSArrayWAt impl.pathDS ctx.wd.comps impl.constructExpander.phiNum
    impl.constructExpander.phiDen ctx.wd.M_W w lay.staticEnd lay.dsHandlesAddr d.hCur
    st.mem ctx.wd.comps.length d.states d.reps
  hCur_lo : lay.staticEnd ≤ d.hCur
  hCur_bd : d.hCur ≤ Task3Input.staticEndCap impl inp + 5 * inp.J.m +
    (rCur * inp.J.m + g1 + (del0 + qi)) * Task3Input.dsOneW impl inp.J +
    g1 * (2 * impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J) + 3)
  zero_from : WordRAM.ZeroFrom st.mem d.hCur
  eta2_eq : st.mem (lay.base + t3OffEta2) + 1 = rCur
  getPath_eq : st.mem (lay.base + t3OffGetPath) = g1
  del_eq : st.mem (lay.base + t3OffDel) = del0 + qi
  econgUpd_eq : st.mem (lay.base + t3OffEcongUpd) = eUpd1
  hCur_eq : st.mem (lay.base + t3OffHCur) = d.hCur
  nextU_eq : st.mem (lay.base + t3OffNextU) = nextU
  nextU_bin : nextU = 0 ∨ nextU = 1
  emb_part : IsPartialEmbedding inp.J ctx.wd.W emb1
  emb_j0_cov : ∀ eJ < inp.J.m,
    (ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.isLoop ∨
      ∃ eW, ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW) →
    (emb1 eJ).isSome = true
  emb_nodup : ∀ eJ < inp.J.m, ∀ P, emb1 eJ = some P → P.edges.Nodup
  emb_len_W : ∀ eJ < inp.J.m, (partialToWalk emb1 eJ).edges.length ≤
    impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander)
      (Task1Input.mwCap impl inp.J)
  emb_len_real : ∀ eJ < inp.J.m, ((partialToWalk emb1 eJ).edges.length : ℝ) ≤ ctx.wd.γ_ExpPath
  emb_mem : ∀ eJ < inp.J.m, match emb1 eJ with
    | none => st.mem (lay.embJWAddr + eJ) = 0
    | some P => lay.staticEnd ≤ st.mem (lay.embJWAddr + eJ) ∧
        st.mem (lay.embJWAddr + eJ) + P.encode.length ≤ d.hCur ∧
        WalkAt st.mem (st.mem (lay.embJWAddr + eJ)) P ∧
        (∀ a, st.mem (lay.embJWAddr + eJ) ≤ a →
          a < st.mem (lay.embJWAddr + eJ) + P.encode.length →
          ∀ cj < ctx.wd.comps.length,
            ¬ impl.pathDS.R.foot (st.mem (lay.dsHandlesAddr + cj)) (d.reps cj) a)
  econg_cnt_eq : ∀ eW < ctx.wd.W.m,
    st.mem (lay.econgCountAddr + eW) =
      {eJ ∈ Finset.range inp.J.m | eW ∈ (partialToWalk emb1 eJ).edges}.card
  econg_le_round : ∀ eW < ctx.wd.W.m,
    econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk emb1) eW ≤ ((rCur : ℝ) + 1 / 2) * ctx.wd.τ₂
  econg_j0_le : ∀ eW < ctx.wd.j0Edges.length,
    econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk emb1) eW ≤ ctx.wd.τ₂ / 2
  wdel_j0 : ∀ eW < ctx.wd.j0Edges.length, st.mem (lay.wDelStampAddr + eW) = 0
  wdel_comp : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
    st.mem (lay.wDelStampAddr + eW) ≤ rCur ∧
    st.mem (lay.wDelStampAddr + eW) ≤ st.mem (lay.econgCountAddr + eW)
  wdel_thresh : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
    st.mem (lay.wDelStampAddr + eW) = rCur →
    (rCur : ℝ) * ctx.wd.τ₂ ≤ econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk emb1) eW
  wdel_lt_econg : ∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
    st.mem (lay.wDelStampAddr + eW) < rCur →
    econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk emb1) eW ≤ (rCur : ℝ) * ctx.wd.τ₂
  econgUpd_sum : eUpd1 = ∑ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
    st.mem (lay.econgCountAddr + eW)
  getPath_cnt_le : g1 ≤ inp.J.m - (unembeddedSet2Pure inp.J emb1).card
  del_iff_drop : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (eL : ℕ),
    eL < ctx.wd.comps[ci].W_sub.m →
    (eL ∈ (d.states ci).deleted ↔
      st.mem (lay.wDelStampAddr + (ctx.wd.comps[ci].wStart + eL)) = rCur ∧
      (ctx.wd.comps[ci].wStart + eL) ∉ Q.drop qi)
  vhat_stmp_eq : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (v : ℕ),
    v < ctx.wd.comps[ci].W_sub.n →
    (st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) = rCur ↔ v ∈ (d.states ci).Vhat)
  vhat_stmp_le : ∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (v : ℕ),
    v < ctx.wd.comps[ci].W_sub.n →
    st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) ≤ rCur
  phi_eq : Φ = t3RoundPhi ctx lay d st.mem

lemma T3DrainQueueAt.toRoundAt {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {ctx : T3Ctx impl inp mem₀ w} {lay : T3Layout} {rCur : ℕ}
    {Q : List ℕ} {g1 del0 eUpd1 : ℕ} {emb1 : ℕ → Option Walk} {nextU : ℕ}
    {d : T3RoundData impl.pathDS} {st : State} {Φ : ℕ}
    (h : T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU Q.length d st Φ) :
    T3RoundAt ctx lay rCur d st Φ where
  rCur_pos := h.rCur_pos
  rCur_le := h.rCur_le
  staticMem := h.staticMem
  dsArr := h.dsArr
  hCur_lo := h.hCur_lo
  hCur_bd := by rw [h.d_g, h.d_del]; exact h.hCur_bd
  zero_from := h.zero_from
  eta2_eq := h.eta2_eq
  getPath_eq := h.d_g ▸ h.getPath_eq
  del_eq := h.d_del ▸ h.del_eq
  econgUpd_eq := h.d_eUpd ▸ h.econgUpd_eq
  hCur_eq := h.hCur_eq
  nextU_eq := h.d_nextU ▸ h.nextU_eq
  nextU_bin := h.d_nextU ▸ h.nextU_bin
  emb_part := h.d_emb ▸ h.emb_part
  emb_j0_cov := h.d_emb ▸ h.emb_j0_cov
  emb_nodup := h.d_emb ▸ h.emb_nodup
  emb_len_W := h.d_emb ▸ h.emb_len_W
  emb_len_real := h.d_emb ▸ h.emb_len_real
  emb_mem := h.d_emb ▸ h.emb_mem
  econg_cnt_eq := h.d_emb ▸ h.econg_cnt_eq
  econg_le_round := h.d_emb ▸ h.econg_le_round
  econg_j0_le := h.d_emb ▸ h.econg_j0_le
  wdel_j0 := h.wdel_j0
  wdel_comp := h.wdel_comp
  wdel_thresh := h.d_emb ▸ h.wdel_thresh
  wdel_lt_econg := h.d_emb ▸ h.wdel_lt_econg
  getPath_cnt_le := h.d_g ▸ h.d_emb ▸ h.getPath_cnt_le
  econgUpd_sum := h.d_eUpd ▸ h.econgUpd_sum
  econgUpd_bound := h.d_eUpd ▸ h.d_g ▸ h.eUpd_bound
  econgUpd_W := h.d_eUpd ▸ h.d_g ▸ h.eUpd_W
  del_le_econgUpd := by rw [h.d_del, h.d_eUpd]; exact h.del_le_eUpd
  del_iff := fun ci hci eL heL => by
    have hiff := h.del_iff_drop ci hci eL heL
    simp only [List.drop_length, List.not_mem_nil, not_false_eq_true, and_true] at hiff
    exact hiff
  vhat_stmp_eq := h.vhat_stmp_eq
  vhat_stmp_le := h.vhat_stmp_le
  phi_eq := h.phi_eq

lemma eta2Bound_le_maxHeapEnd (impl : SpannerToolImpl) (inp : Task3Input) :
    eta2Bound inp.J ≤ Task3Input.maxHeapEnd impl inp := by
  have hlog : Nat.log 2 (inp.J.m + 1) ≤ inp.J.m := by
    by_cases hm0 : inp.J.m = 0
    · simp [hm0]
    · exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow (by omega)
        (by
          have h1 : inp.J.m < 2 ^ inp.J.m := Nat.lt_two_pow_self
          have h2 : 2 ^ inp.J.m < 2 ^ (inp.J.m + 1) :=
            Nat.pow_lt_pow_right (by omega) (by omega)
          omega))
  have hη : eta2Bound inp.J ≤ 3 + 2 * inp.J.m := by
    unfold eta2Bound; omega
  have h32 : 32 + 5 * inp.J.m ≤ Task3Input.staticEndCap impl inp := by
    unfold Task3Input.staticEndCap t3HdrSize; omega
  have hcap : Task3Input.staticEndCap impl inp ≤ Task3Input.maxHeapEnd impl inp := by
    unfold Task3Input.maxHeapEnd
    exact le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
  omega

lemma T3DrainQueueAt.step_update {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {ctx : T3Ctx impl inp mem₀ w} {lay : T3Layout} (hlay : lay = T3Layout.ofCtx ctx)
    {rCur : ℕ} {Q : List ℕ} {g1 del0 eUpd1 : ℕ} {emb1 : ℕ → Option Walk} {nextU qi : ℕ}
    {d : T3RoundData impl.pathDS} {st stF : State} {Φ : ℕ}
    (hD : T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU qi d st Φ)
    (hqi : qi < Q.length) {ci : ℕ} (hci : ci < ctx.wd.comps.length) {eL : ℕ}
    (heL : eL < ctx.wd.comps[ci].W_sub.m) (hStart : ctx.wd.comps[ci].wStart + eL = Q[qi]'hqi)
    {hNext : ℕ} (hNext_lo : d.hCur ≤ hNext)
    (hNext_bd : hNext ≤ d.hCur + Task3Input.dsOneW impl inp.J)
    (hLoc : impl.pathDS.R.Local)
    (memDS : ℕ → ℕ) (hDS_below : ∀ a < lay.staticEnd, memDS a = st.mem a)
    {s' : PathDSAbsState} {x' : impl.pathDS.R.τ} {L : List ℕ}
    (hDS_pres : ∀ a < d.hCur, ¬ impl.pathDS.R.foot (st.mem (lay.dsHandlesAddr + ci)) (d.reps ci) a →
      memDS a = st.mem a)
    (hDS_foot_new : ∀ a, impl.pathDS.R.foot (st.mem (lay.dsHandlesAddr + ci)) x' a →
      impl.pathDS.R.foot (st.mem (lay.dsHandlesAddr + ci)) (d.reps ci) a ∨ (d.hCur ≤ a ∧ a < hNext))
    (hs'_G : s'.G = (d.states ci).G) (hs'_del : s'.deleted = insert eL (d.states ci).deleted)
    (hVhat_sub : (d.states ci).Vhat ⊆ s'.Vhat) (hL_nd : L.Nodup)
    (hL_fin : L.toFinset = s'.Vhat \ (d.states ci).Vhat)
    (hdsArrDS : DSArrayWAt impl.pathDS ctx.wd.comps impl.constructExpander.phiNum
      impl.constructExpander.phiDen ctx.wd.M_W w lay.staticEnd lay.dsHandlesAddr hNext memDS
      ctx.wd.comps.length (Function.update d.states ci s') (Function.update d.reps ci x'))
    (hmem_HCur : stF.mem (lay.base + t3OffHCur) = hNext)
    (hmem_Del : stF.mem (lay.base + t3OffDel) = del0 + qi + 1)
    (hmem_out : ∀ a, a ≠ lay.base + t3OffHCur → a ≠ lay.base + t3OffDel →
      (a < lay.vhatStampAddr + vhatBaseW ctx.wd ci ∨
        lay.vhatStampAddr + vhatBaseW ctx.wd ci + ctx.wd.comps[ci].W_sub.n ≤ a) →
      stF.mem a = memDS a)
    (hv_eq : ∀ v < ctx.wd.comps[ci].W_sub.n,
      (stF.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) = rCur ↔ v ∈ s'.Vhat))
    (hv_le : ∀ v < ctx.wd.comps[ci].W_sub.n,
      stF.mem (lay.vhatStampAddr + vhatBaseW ctx.wd ci + v) ≤ rCur) :
    let d' : T3RoundData impl.pathDS :=
      ⟨d.emb, d.getPathCnt, del0 + (qi + 1), d.econgUpd, hNext,
        Function.update d.states ci s', Function.update d.reps ci x', d.nextHasUnemb⟩
    T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU (qi + 1) d' stF
        (t3RoundPhi ctx lay d' stF.mem) ∧
      dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length d'.reps stF.mem =
        dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length d'.reps memDS ∧
      t3EcongPhi ctx lay stF.mem = t3EcongPhi ctx lay st.mem ∧
      t3VhatRem ctx.wd d.states = t3VhatRem ctx.wd d'.states + L.length := by
  intro d'
  have hb := T3Layout.bounds ctx
  unfold t3HdrSize at hb
  have hbase_le_end : lay.vhatStampAddr + vhatBaseW ctx.wd ci + ctx.wd.comps[ci].W_sub.n ≤
      lay.staticEnd := by
    have ha := vhatBaseW_add_le hci
    have hs := vhatBaseW_le_sum (wd := ctx.wd) (ci := ci + 1)
    subst hlay; omega
  have hmem_above : ∀ a, lay.staticEnd ≤ a → stF.mem a = memDS a := fun a ha =>
    hmem_out a (by unfold t3OffHCur; subst hlay; omega)
      (by unfold t3OffDel; subst hlay; omega) (Or.inr (by omega))
  have hmem_hdr : ∀ i < t3HdrSize, i ≠ t3OffHCur → i ≠ t3OffDel →
      stF.mem (lay.base + i) = st.mem (lay.base + i) := fun i hi h5 h3 => by
    unfold t3HdrSize at hi
    rw [hmem_out _ (by omega) (by omega) (Or.inl (by subst hlay; omega))]
    exact hDS_below _ (by subst hlay; omega)
  have hmem_voff : ∀ cj < ctx.wd.comps.length,
      stF.mem (lay.vhatOffsetAddr + cj) = st.mem (lay.vhatOffsetAddr + cj) := fun cj hcj => by
    rw [hmem_out _ (by unfold t3OffHCur; subst hlay; omega)
      (by unfold t3OffDel; subst hlay; omega) (Or.inl (by subst hlay; omega))]
    exact hDS_below _ (by subst hlay; omega)
  have hmem_below : ∀ x < inp.v2, stF.mem x = mem₀ x := fun x hx => by
    rw [hmem_out x (by unfold t3OffHCur; subst hlay; omega)
      (by unfold t3OffDel; subst hlay; omega) (Or.inl (by subst hlay; omega))]
    rw [hDS_below x (by subst hlay; omega)]
    exact hD.staticMem.1 x hx
  have hStatic' : T3StaticMem ctx lay stF.mem :=
    hD.staticMem.mono (fun x hx => by
      rw [hmem_out x (by unfold t3OffHCur; subst hlay; omega)
        (by unfold t3OffDel; subst hlay; omega) (Or.inl (by subst hlay; omega))]
      exact hDS_below x (by subst hlay; omega))
      (fun i hi _ _ h3 _ h5 _ _ => hmem_hdr i hi h5 h3) hmem_voff
  have hDS_frame := hdsArrDS.frame_below hLoc
    (fun cj hcj => hmem_out _ (by unfold t3OffHCur; subst hlay; omega)
      (by unfold t3OffDel; subst hlay; omega) (Or.inl (by subst hlay; omega)))
    (fun a ha1 ha2 => hmem_above a ha1)
    (fun a ha => hmem_above a (le_trans (le_trans hD.hCur_lo hNext_lo) ha))
  have hmem_arr : ∀ a, lay.embJWAddr ≤ a → a < lay.vhatStampAddr → stF.mem a = st.mem a :=
    fun a ha1 ha2 => by
      have ha_s : a < lay.staticEnd := by subst hlay; omega
      rw [hmem_out a (by unfold t3OffHCur; subst hlay; omega)
        (by unfold t3OffDel; subst hlay; omega) (Or.inl (by omega))]
      exact hDS_below a ha_s
  have hec_eq : t3EcongPhi ctx lay stF.mem = t3EcongPhi ctx lay st.mem :=
    t3EcongPhi_frame ctx lay
      (fun eW heW => hmem_arr _ (by subst hlay; exact le_trans (by omega) (Nat.le_add_right _ _))
        (by subst hlay; have := (Finset.mem_Ico.mp heW).2; omega))
      (fun eW heW => hmem_arr _ (by subst hlay; omega)
        (by subst hlay; have := (Finset.mem_Ico.mp heW).2; omega))
  have hs'_val : (d.states ci).Vhat ⊆ s'.Vhat ∧ s'.Vhat ⊆ Finset.range ctx.wd.comps[ci].W_sub.n := by
    refine ⟨hVhat_sub, ?_⟩
    have hm := hdsArrDS.at_ci ci hci
    rw [Function.update_self] at hm
    have hval := hm.2.2.2.2.2.2.2.2
    have hG_s := hm.2.2.2.2.1
    rw [List.getD_eq_getElem _ _ hci] at hG_s
    simpa [Graph.verts, hG_s] using hval.2.2.2.2.2.2.2.1
  have hvhat_drop : t3VhatRem ctx.wd d.states = t3VhatRem ctx.wd d'.states + L.length :=
    t3VhatRem_update hci hs'_val.1 hs'_val.2 hL_nd hL_fin
  have hQ_eq : ListAt stF.mem lay.queueAddr Q :=
    ListAt.congr hD.queue_list (by
      intro k hk1 hk2
      have hQ_sub : Q.toFinset ⊆ Finset.range ctx.wd.W.m := fun x hx =>
        Finset.mem_range.mpr (hD.Q_valid x (List.mem_toFinset.mp hx)).2.1
      have hQ_le_Wm : Q.length ≤ ctx.wd.W.m := by
        simpa [List.toFinset_card_of_nodup hD.Q_nd] using Finset.card_le_card hQ_sub
      exact hmem_arr k (by subst hlay; omega) (by subst hlay; omega))
  have hds_c1 := hD.dsArr
  refine ⟨⟨hD.rCur_pos, hD.rCur_le, by omega, hD.Q_nd, hD.Q_len_le, hD.g1_le, hD.del_le_eUpd,
    hD.eUpd_bound, hD.eUpd_W, hQ_eq, fun eW heW => by
      have hqv := hD.Q_valid eW heW
      exact ⟨hqv.1, hqv.2.1, (hmem_arr _ (by subst hlay; omega) (by subst hlay; omega)).trans hqv.2.2⟩,
    hD.d_emb, hD.d_g, rfl, hD.d_eUpd, hD.d_nextU, hStatic', hDS_frame.1,
    le_trans hD.hCur_lo hNext_lo, by
      have h1 := hD.hCur_bd
      have h2 := hNext_bd
      simp only [d']
      linarith [show (rCur * inp.J.m + g1 + (del0 + (qi + 1))) * Task3Input.dsOneW impl inp.J =
          (rCur * inp.J.m + g1 + (del0 + qi)) * Task3Input.dsOneW impl inp.J +
            Task3Input.dsOneW impl inp.J by ring],
    hDS_frame.1.zero_from,
    (by
      rw [hmem_out (lay.base + t3OffEta2) (by subst hlay; unfold t3OffEta2 t3OffHCur; omega)
        (by subst hlay; unfold t3OffEta2 t3OffDel; omega) (Or.inl (by subst hlay; unfold t3OffEta2; omega)),
        hDS_below _ (by subst hlay; unfold t3OffEta2; omega)]
      exact hD.eta2_eq),
    (hmem_out _ (by subst hlay; unfold t3OffGetPath t3OffHCur; omega)
      (by subst hlay; unfold t3OffGetPath t3OffDel; omega) (Or.inl (by subst hlay; unfold t3OffGetPath; omega))).trans
      ((hDS_below _ (by subst hlay; unfold t3OffGetPath; omega)).trans hD.getPath_eq),
    by rw [hmem_Del]; ring,
    (hmem_out _ (by subst hlay; unfold t3OffEcongUpd t3OffHCur; omega)
      (by subst hlay; unfold t3OffEcongUpd t3OffDel; omega) (Or.inl (by subst hlay; unfold t3OffEcongUpd; omega))).trans
      ((hDS_below _ (by subst hlay; unfold t3OffEcongUpd; omega)).trans hD.econgUpd_eq),
    hmem_HCur,
    (hmem_out _ (by subst hlay; unfold t3OffNextU t3OffHCur; omega)
      (by subst hlay; unfold t3OffNextU t3OffDel; omega) (Or.inl (by subst hlay; unfold t3OffNextU; omega))).trans
      ((hDS_below _ (by subst hlay; unfold t3OffNextU; omega)).trans hD.nextU_eq),
    hD.nextU_bin, hD.emb_part, hD.emb_j0_cov, hD.emb_nodup, hD.emb_len_W, hD.emb_len_real,
    fun eJ heJ => ?_, fun eW heW => ?_, hD.econg_le_round, hD.econg_j0_le,
    fun eW heW => ?_, fun eW heW => ?_, fun eW heW hst => ?_, fun eW heW hlt => ?_,
    ?_, hD.getPath_cnt_le, fun cj hcj eL' heL' => ?_, fun cj hcj v hv => ?_,
    fun cj hcj v hv => ?_, rfl⟩, hDS_frame.2, hec_eq, hvhat_drop⟩
  · have hem := hD.emb_mem eJ heJ
    have hp : stF.mem (lay.embJWAddr + eJ) = st.mem (lay.embJWAddr + eJ) :=
      hmem_arr _ (by subst hlay; omega) (by subst hlay; omega)
    cases he1 : emb1 eJ with
    | none => rw [he1] at hem; rw [hp]; exact hem
    | some P =>
      rw [he1] at hem
      have hptr := hp
      have hagr_P : ∀ k, st.mem (lay.embJWAddr + eJ) ≤ k →
          k < st.mem (lay.embJWAddr + eJ) + P.encode.length → stF.mem k = st.mem k := fun k hk1 hk2 => by
        have h1 : lay.staticEnd ≤ k := le_trans hem.1 hk1
        have h2 : k < d.hCur := lt_of_lt_of_le hk2 hem.2.1
        have hnf := hem.2.2.2 k hk1 hk2 ci hci
        exact (hmem_above k h1).trans (hDS_pres k h2 hnf)
      refine ⟨hptr ▸ hem.1, by rw [hptr]; exact le_trans hem.2.1 hNext_lo, ?_, ?_⟩
      · rw [hptr]; exact ListAt.congr hem.2.2.1 hagr_P
      · intro a ha1 ha2 cj hcj hf
        have hhdl_eq : stF.mem (lay.dsHandlesAddr + cj) = st.mem (lay.dsHandlesAddr + cj) :=
          hmem_arr _ (by subst hlay; omega) (by subst hlay; omega)
        rw [hptr] at ha1 ha2
        rw [hhdl_eq] at hf
        by_cases hcj_eq : cj = ci
        · subst hcj_eq
          dsimp only [d'] at hf
          rw [Function.update_self] at hf
          rcases hDS_foot_new a hf with hfold | ⟨hlo, _⟩
          · exact hem.2.2.2 a ha1 ha2 cj hci hfold
          · exact absurd hlo (not_le_of_gt (lt_of_lt_of_le ha2 hem.2.1))
        · dsimp only [d'] at hf
          rw [Function.update_of_ne hcj_eq] at hf
          exact hem.2.2.2 a ha1 ha2 cj hcj hf
  · rw [hmem_arr _ (by subst hlay; omega) (by subst hlay; omega)]
    exact hD.econg_cnt_eq eW heW
  · rw [hmem_arr _ (by subst hlay; dsimp only [T3Layout.ofCtx]; omega)
      (by subst hlay; dsimp only [T3Layout.ofCtx]; have := ctx.hw_okW.W_m_eq; omega)]
    exact hD.wdel_j0 eW heW
  · have he := Finset.mem_Ico.mp heW
    rw [hmem_arr _ (by subst hlay; omega) (by subst hlay; omega),
      hmem_arr _ (by subst hlay; omega) (by subst hlay; omega)]
    exact hD.wdel_comp eW heW
  · have he := Finset.mem_Ico.mp heW
    rw [hmem_arr _ (by subst hlay; omega) (by subst hlay; omega)] at hst
    exact hD.wdel_thresh eW heW hst
  · have he := Finset.mem_Ico.mp heW
    rw [hmem_arr _ (by subst hlay; omega) (by subst hlay; omega)] at hlt
    exact hD.wdel_lt_econg eW heW hlt
  · rw [hD.econgUpd_sum]
    refine Finset.sum_congr rfl fun eW heW => ?_
    have he := Finset.mem_Ico.mp heW
    rw [hmem_arr _ (by subst hlay; omega) (by subst hlay; omega)]
  · have hmem_wd : stF.mem (lay.wDelStampAddr + (ctx.wd.comps[cj].wStart + eL')) =
        st.mem (lay.wDelStampAddr + (ctx.wd.comps[cj].wStart + eL')) := by
      have hc := (ctx.hw_okW.comp_props cj hcj).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      exact hmem_arr _ (by subst hlay; omega) (by subst hlay; omega)
    rw [hmem_wd]
    by_cases hcj_eq : cj = ci
    · subst hcj_eq
      simp only [d', Function.update_self, hs'_del, Finset.mem_insert]
      rw [hD.del_iff_drop cj hcj eL' heL']
      by_cases heL'_eq : eL' = eL
      · subst heL'_eq
        rw [hStart]
        have hq_mem : Q[qi]'hqi ∈ Q := List.getElem_mem hqi
        have hq_st : st.mem (lay.wDelStampAddr + Q[qi]'hqi) = rCur := (hD.Q_valid _ hq_mem).2.2
        have hq_ndrop : Q[qi]'hqi ∉ Q.drop (qi + 1) := by
          intro hmem
          have hdup := hD.Q_nd
          have hcons : Q.drop qi = Q[qi]'hqi :: Q.drop (qi + 1) := List.drop_eq_getElem_cons hqi
          have hnd_drop : (Q.drop qi).Nodup := hdup.drop
          rw [hcons, List.nodup_cons] at hnd_drop
          exact hnd_drop.1 hmem
        simp [hq_st, hq_ndrop]
      · have hne : ctx.wd.comps[cj].wStart + eL' ≠ Q[qi]'hqi := by rw [← hStart]; omega
        have hcons : Q.drop qi = Q[qi]'hqi :: Q.drop (qi + 1) := List.drop_eq_getElem_cons hqi
        constructor
        · rintro (rfl | hmem)
          · exact absurd rfl heL'_eq
          · obtain ⟨hs, hndrop⟩ := hmem
            refine ⟨hs, fun hmem2 => hndrop (by rw [hcons]; exact List.mem_cons_of_mem _ hmem2)⟩
        · rintro ⟨hs, hndrop⟩
          right
          refine ⟨hs, fun hmem2 => ?_⟩
          rw [hcons, List.mem_cons] at hmem2
          rcases hmem2 with heq | hmem2
          · exact hne heq
          · exact hndrop hmem2
    · simp only [d', Function.update_of_ne hcj_eq]
      rw [hD.del_iff_drop cj hcj eL' heL']
      have hne : ctx.wd.comps[cj].wStart + eL' ≠ Q[qi]'hqi := by
        intro heq; rw [← hStart] at heq
        exact hcj_eq (wStart_add_inj ctx hcj hci heL' heL heq).1
      have hcons : Q.drop qi = Q[qi]'hqi :: Q.drop (qi + 1) := List.drop_eq_getElem_cons hqi
      constructor
      · rintro ⟨hs, hndrop⟩
        exact ⟨hs, fun hmem2 => hndrop (by rw [hcons]; exact List.mem_cons_of_mem _ hmem2)⟩
      · rintro ⟨hs, hndrop⟩
        refine ⟨hs, fun hmem2 => ?_⟩
        rw [hcons, List.mem_cons] at hmem2
        exact hmem2.elim (fun h => absurd h hne) hndrop
  · by_cases hcj_eq : cj = ci
    · subst hcj_eq; dsimp only [d']; rw [Function.update_self]; exact hv_eq v hv
    · have hadr : stF.mem (lay.vhatStampAddr + vhatBaseW ctx.wd cj + v) =
          st.mem (lay.vhatStampAddr + vhatBaseW ctx.wd cj + v) := by
        have hlt_s : lay.vhatStampAddr + vhatBaseW ctx.wd cj + v < lay.staticEnd := by
          have ha := vhatBaseW_add_le hcj
          have hs := vhatBaseW_le_sum (wd := ctx.wd) (ci := cj + 1)
          subst hlay; omega
        have hdisj : lay.vhatStampAddr + vhatBaseW ctx.wd cj + v < lay.vhatStampAddr + vhatBaseW ctx.wd ci ∨
            lay.vhatStampAddr + vhatBaseW ctx.wd ci + ctx.wd.comps[ci].W_sub.n ≤
              lay.vhatStampAddr + vhatBaseW ctx.wd cj + v := by
          rcases Nat.lt_or_gt_of_ne hcj_eq with hlt | hlt
          · left
            have ha := vhatBaseW_add_le hcj
            have hm := vhatBaseW_mono (wd := ctx.wd) (show cj + 1 ≤ ci by omega)
            omega
          · right
            have ha := vhatBaseW_add_le hci
            have hm := vhatBaseW_mono (wd := ctx.wd) (show ci + 1 ≤ cj by omega)
            omega
        rw [hmem_out _ (by subst hlay; unfold t3OffHCur; omega)
        (by subst hlay; unfold t3OffDel; omega) hdisj, hDS_below _ hlt_s]
      dsimp only [d']
      rw [Function.update_of_ne hcj_eq, hadr]
      exact hD.vhat_stmp_eq cj hcj v hv
  · by_cases hcj_eq : cj = ci
    · subst hcj_eq; exact hv_le v hv
    · have hlt_s : lay.vhatStampAddr + vhatBaseW ctx.wd cj + v < lay.staticEnd := by
        have ha := vhatBaseW_add_le hcj
        have hs := vhatBaseW_le_sum (wd := ctx.wd) (ci := cj + 1)
        subst hlay; omega
      have hdisj : lay.vhatStampAddr + vhatBaseW ctx.wd cj + v < lay.vhatStampAddr + vhatBaseW ctx.wd ci ∨
          lay.vhatStampAddr + vhatBaseW ctx.wd ci + ctx.wd.comps[ci].W_sub.n ≤
            lay.vhatStampAddr + vhatBaseW ctx.wd cj + v := by
        rcases Nat.lt_or_gt_of_ne hcj_eq with hlt | hlt
        · left
          have ha := vhatBaseW_add_le hcj
          have hm := vhatBaseW_mono (wd := ctx.wd) (show cj + 1 ≤ ci by omega)
          omega
        · right
          have ha := vhatBaseW_add_le hci
          have hm := vhatBaseW_mono (wd := ctx.wd) (show ci + 1 ≤ cj by omega)
          omega
      rw [hmem_out _ (by subst hlay; unfold t3OffHCur; omega)
        (by subst hlay; unfold t3OffDel; omega) hdisj, hDS_below _ hlt_s]
      exact hD.vhat_stmp_le cj hcj v hv

end MinCostFlow.Spanner

