module

public import MinCostFlow.Spanner.ProgTask3EdgeStepProof
public import MinCostFlow.Spanner.ProgTask3DrainProof

/-!
# Helper lemmas for the middle step of Task 3 (`t3MiddleEdge`)

The middle step of Task 3 asks the path data structure for a path in `W` for one unembedded
edge of `J`, writes the path to the heap, updates the congestion counters and drains the queue
of overloaded edges. This file proves the facts about memory, heap bounds and costs that the
triple `t3MiddleEdge_ptriple` (in `ProgTask3MiddleProof.lean`) uses. The main one is
`t3_middle_post_cps`: the last part of the step (store the walk header, move the heap pointer,
record the walk of the edge, and call the drain procedure when the queue is not empty)
restores the round invariant `T3RoundAt`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

lemma t3_walkAt_zeroFrom_le {G : Graph} {u v hOld hNew : ℕ} {P : Walk} {mem : ℕ → ℕ}
    (hWalk : WalkAt mem hOld P) (hP_wk : P.IsWalk G u v) (hne : u ≠ v) (hP_nd : P.verts.Nodup)
    (hZf : WordRAM.ZeroFrom mem hNew) (_hle : hOld ≤ hNew) :
    hOld + (1 + P.verts.length + P.edges.length) ≤ hNew := by
  have h1_le : 1 ≤ P.edges.length := by
    rcases hP_wk with ⟨_, _, ⟨_, he, huv⟩ | ⟨hnn, _⟩⟩
    · exact absurd huv hne
    · exact Nat.pos_of_ne_zero fun hz => hnn (List.eq_nil_of_length_eq_zero hz)
  have hwa := walkAt_iff.mp hWalk
  rcases Nat.eq_or_lt_of_le h1_le with heq1 | h2_le
  · have hlt : hOld + 1 + P.verts.length < hNew := by
      by_contra hge
      have hz := hZf (hOld + 1 + P.verts.length) (Nat.le_of_not_lt hge)
      rw [hwa.2.2.1, ← heq1] at hz; omega
    omega
  · have he_nd : P.edges.Nodup := t3_walk_edges_nodup_of_verts_nodup hP_wk hP_nd
    let j1 := P.edges.length - 2; let j2 := P.edges.length - 1
    have hj1 : j1 < P.edges.length := by omega
    have hj2 : j2 < P.edges.length := by omega
    have hdiff : P.edges[j1]'hj1 ≠ P.edges[j2]'hj2 := fun h => by
      have hinj := (List.nodup_iff_injective_getElem.mp he_nd) (a₁ := ⟨j1, hj1⟩) (a₂ := ⟨j2, hj2⟩) h
      simp only [Fin.mk.injEq, j1, j2] at hinj; omega
    have hnz : P.edges[j1]'hj1 ≠ 0 ∨ P.edges[j2]'hj2 ≠ 0 := by omega
    rcases hnz with hnz1 | hnz2
    · have hlt : hOld + 2 + P.verts.length + j1 < hNew := by
        by_contra hge; have hz := hZf _ (Nat.le_of_not_lt hge); rw [listAt_getElem hwa.2.2.2 hj1] at hz; exact hnz1 hz
      omega
    · have hlt : hOld + 2 + P.verts.length + j2 < hNew := by
        by_contra hge; have hz := hZf _ (Nat.le_of_not_lt hge); rw [listAt_getElem hwa.2.2.2 hj2] at hz; exact hnz2 hz
      omega

lemma t3_inComp_ne {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) {eJ ci jL : ℕ}
    (heJ : eJ < inp.J.m) (hsrc : ctx.wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inComp ci jL) :
    ∃ (hci : ci < ctx.wd.comps.length),
      let c := ctx.wd.comps[ci]'hci
      let e := c.J_sub.edges.getD jL (0, 0)
      jL < c.J_sub.m ∧ e.1 < c.W_sub.n ∧ e.2 < c.W_sub.n ∧ e.1 ≠ e.2 ∧
        c.jSubOrigEdges.getD jL 0 = eJ ∧
        inp.J.edges[eJ]'heJ = (c.verts.getD e.1 0, c.verts.getD e.2 0) := by
  have heJ' : eJ < ctx.wInp.prep.J.m := ctx.hWInpJ.symm ▸ heJ
  have hms := (mkW_jSources_spec ctx.hStat ctx.hw_okW ctx.hws heJ').2
  change match ctx.wd.jSources.getD eJ JEdgeSource.isLoop with
    | JEdgeSource.isLoop => _
    | JEdgeSource.inJ0 _ => _
    | JEdgeSource.inComp ci jL => ∃ (hci : ci < ctx.wd.comps.length) (hj : jL < ctx.wd.comps[ci].jSubOrigEdges.length),
        ctx.wd.comps[ci].jSubOrigEdges[jL]'hj = eJ ∧ jL < ctx.wd.comps[ci].J_sub.m ∧
        ctx.wInp.prep.J.edges[eJ]'heJ' =
          (ctx.wd.comps[ci].verts.getD (ctx.wd.comps[ci].J_sub.edges.getD jL (0, 0)).1 0,
           ctx.wd.comps[ci].verts.getD (ctx.wd.comps[ci].J_sub.edges.getD jL (0, 0)).2 0) at hms
  rw [hsrc] at hms
  rcases hms with ⟨hci, hj_orig, hOrig_eq, hjL_m, hJ_eq⟩
  have hcprops := ctx.hw_okW.comp_props ci hci
  have hcJn : ctx.wd.comps[ci].J_sub.n = ctx.wd.comps[ci].X.card := hcprops.2.2.2.2.2.1
  have hcJval : ctx.wd.comps[ci].J_sub.IsValid := hcprops.2.2.2.2.2.2.1
  have hcWn : ctx.wd.comps[ci].W_sub.n = ctx.wd.comps[ci].X.card := hcprops.2.2.2.2.2.2.2.2.2.2.2.1
  have hmem_e : ctx.wd.comps[ci].J_sub.edges.getD jL (0, 0) ∈ ctx.wd.comps[ci].J_sub.edges := by
    rw [List.getD_eq_getElem _ _ hjL_m]; exact List.getElem_mem hjL_m
  have huv_J := hcJval _ hmem_e
  have hnl := (mkW_comp_jOrig_nonloop ctx.hStat ctx.hws hci hj_orig).2
  have hOrig_d : ctx.wd.comps[ci].jSubOrigEdges.getD jL 0 = eJ := by
    rw [List.getD_eq_getElem _ _ hj_orig]; exact hOrig_eq
  have hne : (ctx.wd.comps[ci].J_sub.edges.getD jL (0, 0)).1 ≠
      (ctx.wd.comps[ci].J_sub.edges.getD jL (0, 0)).2 := by
    intro heq
    have hOrig_d' := hOrig_d; dsimp only [T3Ctx.wd] at hOrig_d'
    rw [hOrig_d', List.getD_eq_getElem _ _ heJ'] at hnl
    have h1 := congrArg Prod.fst hJ_eq; have h2 := congrArg Prod.snd hJ_eq
    dsimp only at h1 h2; rw [heq] at h1; exact hnl (h1.trans h2.symm)
  have hJ_edges : inp.J.edges[eJ]'heJ = (ctx.wInp.prep.J.edges[eJ]'heJ') := by
    have h : ∀ (A B : Graph), A = B → ∀ (hA : eJ < A.m) (hB : eJ < B.m), A.edges[eJ]'hA = B.edges[eJ]'hB := by
      rintro A _ rfl _ _; rfl
    exact h inp.J ctx.wInp.prep.J ctx.hWInpJ.symm heJ heJ'
  exact ⟨hci, hjL_m, by omega, by omega, hne, hOrig_d, hJ_edges.trans hJ_eq⟩

private lemma t3_middle_econg_j0_eq {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) {eJ ci : ℕ} (hci : ci < ctx.wd.comps.length)
    {uL vL : ℕ} {P : Walk} {emb : ℕ → Option Walk}
    (hunemb : emb eJ = none) (hP_wk : P.IsWalk ctx.wd.comps[ci].W_sub uL vL)
    {eW : ℕ} (heW : eW < ctx.wd.j0Edges.length) :
    econgAt inp.J (fun _ => 1) ctx.wd.wW
        (partialToWalk (Function.update emb eJ (some (liftWSubWalk ctx.wd.comps[ci] P)))) eW =
      econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk emb) eW := by
  have hnot : eW ∉ (liftWSubWalk ctx.wd.comps[ci] P).edges := fun hm =>
    Nat.not_lt_of_ge ((mkW_isWalk_liftWSubWalk ctx.hw_okW ctx.hws hci hP_wk).2.2.2 eW hm).1 heW
  simp only [econgAt, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine congrArg (fun s : Finset ℕ => (s.card : ℝ) / ctx.wd.wW eW) (Finset.ext fun j => ?_)
  simp only [Finset.mem_filter, Finset.mem_range]; refine and_congr_right fun _ => ?_
  by_cases hj : j = eJ
  · subst hj; simp [partialToWalk, hunemb, Walk.empty, hnot]
  · simp [partialToWalk, Function.update_of_ne hj]

private lemma t3_nodup_lt_le {L : List ℕ} {n : ℕ} (hnd : L.Nodup) (hlt : ∀ x ∈ L, x < n) : L.length ≤ n := by
  have h1 : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
  have h2 : L.toFinset ⊆ Finset.range n := fun x hx => Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
  simpa [h1, Finset.card_range] using Finset.card_le_card h2

lemma t3_walkAt_of_agree {m₁ m₂ : ℕ → ℕ} {a : ℕ} {P : Walk} (hW : WalkAt m₁ a P)
    (hag : ∀ x, a ≤ x → x < a + P.encode.length → m₂ x = m₁ x) : WalkAt m₂ a P := by
  have h := walkAt_iff.mp hW; have hlen := walk_encode_length P
  exact walkAt_iff.mpr ⟨(hag a (le_refl _) (by omega)).trans h.1,
    ListAt.congr h.2.1 (fun k hk1 hk2 => hag k (by omega) (by omega)),
    (hag (a + 1 + P.verts.length) (by omega) (by omega)).trans h.2.2.1,
    ListAt.congr h.2.2.2 (fun k hk1 hk2 => hag k (by omega) (by omega))⟩

lemma t3_middle_next_bd {staticEndCap m rCur g0 del0 dsOneW γW h0 hMid pv pe : ℕ}
    (hh0 : h0 ≤ staticEndCap + 5 * m + (rCur * m + g0 + del0) * dsOneW + g0 * (2 * γW + 3))
    (hMid_le : hMid ≤ h0 + dsOneW) (hp : 2 + pv + pe ≤ 2 * γW + 3) :
    hMid + (2 + pv + pe) ≤ staticEndCap + 5 * m + (rCur * m + (g0 + 1) + del0) * dsOneW +
      (g0 + 1) * (2 * γW + 3) := by
  have h1 : (rCur * m + (g0 + 1) + del0) * dsOneW = (rCur * m + g0 + del0) * dsOneW + dsOneW := by ring
  have h2 : (g0 + 1) * (2 * γW + 3) = g0 * (2 * γW + 3) + (2 * γW + 3) := by ring
  omega

private lemma t3_middle_heap_max {staticEndCap m eta2 g1 del1 Qlen dsOneW γW maxH hNext : ℕ}
    (hmax : maxH = staticEndCap + 5 * m + (eta2 * m + m + m * γW) * dsOneW + m * (2 * γW + 3))
    (hNext_bd : hNext ≤ staticEndCap + 5 * m + (eta2 * m + g1 + del1) * dsOneW + g1 * (2 * γW + 3))
    (hg1 : g1 ≤ m) (hdelQ : del1 + Qlen ≤ m * γW) : hNext + Qlen * dsOneW ≤ maxH := by
  have hm1 := Nat.mul_le_mul_right dsOneW (show eta2 * m + g1 + (del1 + Qlen) ≤ eta2 * m + m + m * γW by omega)
  have hm2 := Nat.mul_le_mul_right (2 * γW + 3) hg1
  have hadd : (eta2 * m + g1 + del1) * dsOneW + Qlen * dsOneW = (eta2 * m + g1 + (del1 + Qlen)) * dsOneW := by ring
  omega

lemma t3_middle_cost_arith {kQuery γW pLen pVert kDel Φ Φ_gp pre c_gp : ℕ}
    (hpre : pre ≤ 100) (hpv : pVert ≤ pLen + 1) (hpγ : pLen ≤ γW) (hgp : c_gp + Φ_gp ≤ kQuery + Φ) :
    pre + ((4 + c_gp + 1) + (pVert * 31 + pLen * 115 + (kDel + 140) * pLen + 180 + Φ_gp) + 1) ≤
      kQuery + γW * (kDel + 300) + 380 + Φ := by
  have hm1 := Nat.mul_le_mul_right (kDel + 286) hpγ; have hm2 := Nat.mul_le_mul_left γW (show kDel + 286 ≤ kDel + 300 by omega)
  have hexp : pLen * 31 + pLen * 115 + (kDel + 140) * pLen = pLen * (kDel + 286) := by ring
  omega

lemma t3_seq_normal_cps {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt} {st st₁ : State} {c₁ pre B C : ℕ}
    {Post : Outcome → State → ℕ → Prop} (h1 : Runs w p ω s₁ st .normal st₁ c₁)
    (h2 : ∃ o stF c₂ Φ', Runs w p ω s₂ st₁ o stF c₂ ∧ Post o stF Φ' ∧ 0 + c₂ + Φ' ≤ C) (hB : pre + (c₁ + C + 1) ≤ B) :
    ∃ o stF c Φ', Runs w p ω (s₁ ;; s₂) st o stF c ∧ Post o stF Φ' ∧ pre + c + Φ' ≤ B := by
  rcases h2 with ⟨o, stF, c₂, Φ', hr2, hq2, hc2⟩
  exact ⟨o, stF, c₁ + c₂ + 1, Φ', runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h1, hr2, rfl⟩), hq2, by omega⟩

private lemma t3RoundAt_with_regs {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {ctx : T3Ctx impl inp mem₀ w} {lay : T3Layout} {rCur : ℕ} {d : T3RoundData impl.pathDS}
    {m : ℕ → ℕ} {r₁ r₂ : ℕ → ℕ} {p₁ p₂ Φ : ℕ} (h : T3RoundAt ctx lay rCur d ⟨m, r₁, p₁⟩ Φ) :
    T3RoundAt ctx lay rCur d ⟨m, r₂, p₂⟩ Φ :=
  ⟨h.rCur_pos, h.rCur_le, h.staticMem, h.dsArr, h.hCur_lo, h.hCur_bd, h.zero_from, h.eta2_eq,
   h.getPath_eq, h.del_eq, h.econgUpd_eq, h.hCur_eq, h.nextU_eq, h.nextU_bin, h.emb_part,
   h.emb_j0_cov, h.emb_nodup, h.emb_len_W, h.emb_len_real, h.emb_mem, h.econg_cnt_eq,
   h.econg_le_round, h.econg_j0_le, h.wdel_j0, h.wdel_comp, h.wdel_thresh, h.wdel_lt_econg,
   h.getPath_cnt_le, h.econgUpd_sum, h.econgUpd_bound, h.econgUpd_W, h.del_le_econgUpd,
   h.del_iff, h.vhat_stmp_eq, h.vhat_stmp_le, h.phi_eq⟩

private lemma t3DrainQueueAt_with_regs {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    {ctx : T3Ctx impl inp mem₀ w} {lay : T3Layout} {rCur : ℕ} {Q : List ℕ} {g1 del0 eUpd1 : ℕ}
    {emb1 : ℕ → Option Walk} {nextU qi : ℕ} {d : T3RoundData impl.pathDS}
    {m : ℕ → ℕ} {r₁ r₂ : ℕ → ℕ} {p₁ p₂ Φ : ℕ}
    (h : T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU qi d ⟨m, r₁, p₁⟩ Φ) :
    T3DrainQueueAt ctx lay rCur Q g1 del0 eUpd1 emb1 nextU qi d ⟨m, r₂, p₂⟩ Φ :=
  ⟨h.rCur_pos, h.rCur_le, h.qi_le, h.Q_nd, h.Q_len_le, h.g1_le, h.del_le_eUpd, h.eUpd_bound,
   h.eUpd_W, h.queue_list, h.Q_valid, h.d_emb, h.d_g, h.d_del, h.d_eUpd, h.d_nextU, h.staticMem,
   h.dsArr, h.hCur_lo, h.hCur_bd, h.zero_from, h.eta2_eq, h.getPath_eq, h.del_eq, h.econgUpd_eq,
   h.hCur_eq, h.nextU_eq, h.nextU_bin, h.emb_part, h.emb_j0_cov, h.emb_nodup, h.emb_len_W,
   h.emb_len_real, h.emb_mem, h.econg_cnt_eq, h.econg_le_round, h.econg_j0_le, h.wdel_j0,
   h.wdel_comp, h.wdel_thresh, h.wdel_lt_econg, h.econgUpd_sum, h.getPath_cnt_le, h.del_iff_drop,
   h.vhat_stmp_eq, h.vhat_stmp_le, h.phi_eq⟩

lemma t3_middle_post_cps {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {selfBase dsBase rCur eJ ci : ℕ} (hci : ci < ctx.wd.comps.length)
    {hOld hMid : ℕ} {P : Walk} (d0 : T3RoundData impl.pathDS) (reps1 : ℕ → impl.pathDS.R.τ)
    (memStart regsInit : ℕ → ℕ)
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hdrain : p.procs[selfBase + 2]? = some (t3DrainQueueBody dsBase))
    (hLoc : impl.pathDS.R.Local) (heJ : eJ < inp.J.m) (hunemb : d0.emb eJ = none)
    {st₀ : State} {Φ₀ : ℕ} (hR : T3RoundAt ctx lay rCur d0 st₀ Φ₀) (hOld_lo : lay.staticEnd ≤ hOld)
    (hle_hm : hOld + (1 + P.verts.length + P.edges.length) ≤ hMid) (hMid_le_h0 : hMid ≤ d0.hCur + Task3Input.dsOneW impl inp.J)
    (hP_edges_le : P.edges.length ≤ impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J))
    (hP_len_r : (P.edges.length : ℝ) ≤ ctx.wd.γ_ExpPath)
    {uL vL : ℕ} (hP_wk : P.IsWalk ctx.wd.comps[ci].W_sub uL vL) (hP_nd : P.verts.Nodup)
    (hJ_edge : inp.J.edges[eJ]'heJ = (ctx.wd.comps[ci].verts.getD uL 0, ctx.wd.comps[ci].verts.getD vL 0))
    {mem_gp : ℕ → ℕ}
    (hdsArr_mid : DSArrayWAt impl.pathDS ctx.wd.comps impl.constructExpander.phiNum
      impl.constructExpander.phiDen ctx.wd.M_W w lay.staticEnd lay.dsHandlesAddr hMid mem_gp
      ctx.wd.comps.length d0.states reps1)
    (hOld_mem_gp : ∀ e' < inp.J.m, match d0.emb e' with
      | none => mem_gp (lay.embJWAddr + e') = 0
      | some P' => lay.staticEnd ≤ mem_gp (lay.embJWAddr + e') ∧ mem_gp (lay.embJWAddr + e') + P'.encode.length ≤ hMid ∧
          WalkAt mem_gp (mem_gp (lay.embJWAddr + e')) P' ∧
          ∀ a, mem_gp (lay.embJWAddr + e') ≤ a → a < mem_gp (lay.embJWAddr + e') + P'.encode.length →
            ∀ cj < ctx.wd.comps.length, ¬ impl.pathDS.R.foot (mem_gp (lay.dsHandlesAddr + cj)) (reps1 cj) a)
    {st : State} {Φ : ℕ} {ω : ℕ → Bool}
    (hES : T3EdgeStepInv ctx lay rCur eJ ci hci hOld hMid P d0 reps1 memStart regsInit P.edges.length st Φ)
    (hMemStart_gp : ∀ a < hMid, a ≠ lay.base + t3OffGetPath → memStart a = mem_gp a)
    (hMemStart_static : T3StaticMem ctx lay memStart)
    (hMemStart_hdr : memStart (lay.base + t3OffEta2) + 1 = rCur ∧
      memStart (lay.base + t3OffGetPath) = d0.getPathCnt + 1 ∧
      memStart (lay.base + t3OffDel) = d0.delCnt ∧ memStart (lay.base + t3OffNextU) = d0.nextHasUnemb)
    (hMemStart_verts : ∀ (i : ℕ) (hi : i < P.verts.length), memStart (hMid + 1 + i) = ctx.wd.comps[ci].verts.getD (P.verts[i]'hi) 0)
    (hMemStart_elen : memStart (hMid + 1 + P.verts.length) = P.edges.length)
    (hMemStart_zf : WordRAM.ZeroFrom memStart (hMid + 2 + P.verts.length))
    (hMemStart_wdel_j0 : ∀ eW < ctx.wd.j0Edges.length, memStart (lay.wDelStampAddr + eW) = 0)
    (hMemStart_vhat : (∀ (cj : ℕ) (hcj : cj < ctx.wd.comps.length), ∀ v < (ctx.wd.comps[cj]'hcj).W_sub.n,
        memStart (lay.vhatStampAddr + vhatBaseW ctx.wd cj + v) = rCur ↔ v ∈ (d0.states cj).Vhat) ∧
      ∀ (cj : ℕ) (hcj : cj < ctx.wd.comps.length), ∀ v < (ctx.wd.comps[cj]'hcj).W_sub.n,
        memStart (lay.vhatStampAddr + vhatBaseW ctx.wd cj + v) ≤ rCur)
    (hregs : st.regs 0 = lay.base ∧ st.regs 1 = rCur ∧ st.regs 2 = eJ ∧
      st.regs 13 = hMid ∧ st.regs 14 = P.verts.length ∧ st.regs 15 = P.edges.length) :
    let postStmt :=
      Stmt.seq (.store (.reg 13) (.reg 14))
        (Stmt.seq (t3St (.reg 0) (.const t3OffHCur) (t3Add (.reg 13) (t3Add (t3Add (.const 2) (.reg 14)) (.reg 15))))
          (Stmt.seq (.store (t3Add (t3Ld (.reg 0) (.const t3OffEmbJW)) (.reg 2)) (.reg 13))
            (Stmt.seq (.cond (t3Lt (.const 0) (.reg 18)) (.call 25 (selfBase + 2) [.reg 0, .reg 1, .reg 18]) .nop)
              (.ret (.const 0)))))
    ∃ o stF c Φ', Runs w p ω postStmt st o stF c ∧
      (o = .returned 0 ∧ ∃ d',
        T3RoundAt ctx lay rCur d' stF Φ' ∧ d'.getPathCnt = d0.getPathCnt + 1 ∧
        d'.econgUpd = d0.econgUpd + P.edges.length ∧
        (∀ cj < ctx.wd.comps.length, (d0.states cj).Vhat ⊆ (d'.states cj).Vhat) ∧
        (∀ e' < inp.J.m, e' ≠ eJ → d'.emb e' = d0.emb e') ∧
        d'.emb eJ = some (liftWSubWalk ctx.wd.comps[ci] P) ∧ d'.nextHasUnemb = d0.nextHasUnemb) ∧
      c + Φ' ≤ 40 + Φ := by
  intro postStmt
  have hb := T3Layout.bounds ctx; dsimp only at hb; rw [← hlay] at hb; unfold t3HdrSize at hb
  have hj0_le_Wm : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by simp [T3Ctx.wd, WitnessCoreInput.mkWitnessData, Graph.m]
  rcases hES.exists_Q with ⟨Q, hr18, hQk, hQnd, hQL, hQval, hCnt_eq, hEc_r, hWdc, hWdt, hWdlt, hUsum, hDQ, hΦ_eq⟩
  have hw1 : 1 < 2 ^ w := ctx.hwokW.1
  have hwb : Task3Input.maxWordBound impl inp < 2 ^ w := ctx.hwokW.2.2
  have hmax_lt_w : Task3Input.maxHeapEnd impl inp + 3 ≤ Task3Input.maxWordBound impl inp := le_max_left _ _
  have hPv_le : P.verts.length ≤ P.edges.length + 1 := by
    rcases hP_wk with ⟨_, _, ⟨hPv, hPe, _⟩ | ⟨_, hlen, _⟩⟩
    · rw [hPv, hPe]; simp
    · omega
  let γW := impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J)
  have hGpc_succ : d0.getPathCnt + 1 ≤ inp.J.m :=
    let _ : eJ ∈ unembeddedSet2Pure inp.J d0.emb := by simp [unembeddedSet2Pure, heJ, hunemb]
    by have := Finset.card_pos.mpr ⟨eJ, ‹_›⟩; have := hR.getPath_cnt_le; omega
  have hDel_add_Q : d0.delCnt + Q.length ≤ d0.econgUpd + P.edges.length := by have := hR.del_le_econgUpd; omega
  have heUpd_next_W : d0.econgUpd + P.edges.length ≤ (d0.getPathCnt + 1) * γW := by
    have := Nat.add_le_add hR.econgUpd_W hP_edges_le; simpa [Nat.succ_mul] using this
  have hPl_w := mkW_isWalk_liftWSubWalk ctx.hw_okW ctx.hws hci hP_wk
  have hQ_len_Wm : Q.length ≤ ctx.wd.W.m := t3_nodup_lt_le hQnd fun x hx => (hQval x hx).2.2.1
  have hPe_le_Wm : P.edges.length ≤ ctx.wd.W.m :=
    le_trans (le_of_eq hPl_w.2.1.symm)
      (t3_nodup_lt_le (hPl_w.2.2.1 hP_nd) fun eW hm => (hPl_w.2.2.2 eW hm).2)
  have hNext_bd : hMid + (2 + P.verts.length + P.edges.length) ≤
      Task3Input.staticEndCap impl inp + 5 * inp.J.m +
        (rCur * inp.J.m + (d0.getPathCnt + 1) + d0.delCnt) * Task3Input.dsOneW impl inp.J +
        (d0.getPathCnt + 1) * (2 * γW + 3) :=
    t3_middle_next_bd hR.hCur_bd hMid_le_h0 (by omega)
  have hNext_eta_bd : hMid + (2 + P.verts.length + P.edges.length) ≤
      Task3Input.staticEndCap impl inp + 5 * inp.J.m +
        (eta2Bound inp.J * inp.J.m + (d0.getPathCnt + 1) + d0.delCnt) * Task3Input.dsOneW impl inp.J +
        (d0.getPathCnt + 1) * (2 * γW + 3) := by
    have hr := Nat.mul_le_mul_right (Task3Input.dsOneW impl inp.J)
      (show rCur * inp.J.m + (d0.getPathCnt + 1) + d0.delCnt ≤ eta2Bound inp.J * inp.J.m + (d0.getPathCnt + 1) + d0.delCnt by
        have := Nat.mul_le_mul_right inp.J.m hR.rCur_le; omega)
    omega
  have hNext_le_max : hMid + (2 + P.verts.length + P.edges.length) + Q.length * Task3Input.dsOneW impl inp.J ≤
      Task3Input.maxHeapEnd impl inp :=
    t3_middle_heap_max rfl hNext_eta_bd hGpc_succ
      (le_trans hDel_add_Q (le_trans heUpd_next_W (Nat.mul_le_mul_right γW hGpc_succ)))
  let hNext := hMid + (2 + P.verts.length + P.edges.length)
  let m1 := Function.update st.mem hMid P.verts.length
  let m2 := Function.update m1 (lay.base + t3OffHCur) hNext
  let m3 := Function.update m2 (lay.embJWAddr + eJ) hMid
  have hMid_lo : lay.staticEnd ≤ hMid := le_trans hOld_lo (by omega)
  have hm3_arr : ∀ a, a ≠ lay.base + t3OffHCur → a ≠ lay.embJWAddr + eJ → a ≠ hMid → m3 a = st.mem a :=
    fun a h1 h2 h3 => by dsimp only [m3, m2, m1]; rw [Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h3]
  have hm3_static : T3StaticMem ctx lay m3 :=
    hMemStart_static.mono
      (fun x hx => (hm3_arr x (by unfold t3OffHCur; omega) (by omega) (by omega)).trans
        (hES.mem_agree x (by unfold t3OffEcongUpd; omega) (by omega) (by omega) (by omega) (by omega)))
      (fun i hi h1 h2 h3 h4 h5 h6 h7 => by
        have hi' : i < t3HdrSize := hi; unfold t3HdrSize at hi'
        exact (hm3_arr (lay.base + i) (fun h => h5 (Nat.add_left_cancel h)) (by omega) (by omega)).trans
          (hES.mem_agree (lay.base + i) (fun h => h4 (Nat.add_left_cancel h)) (by omega) (by omega) (by omega) (by omega)))
      (fun cj hcj => (hm3_arr _ (by unfold t3OffHCur; omega) (by omega) (by omega)).trans
        (hES.mem_agree _ (by unfold t3OffEcongUpd; omega) (by omega) (by omega) (by omega) (by omega)))
  have hm3_mid_agree : ∀ a < hMid, a ≠ lay.base + t3OffGetPath → a ≠ lay.base + t3OffHCur → a ≠ lay.embJWAddr + eJ →
      ¬ (lay.econgCountAddr ≤ a ∧ a < lay.econgCountAddr + ctx.wd.W.m) →
      ¬ (lay.wDelStampAddr ≤ a ∧ a < lay.wDelStampAddr + ctx.wd.W.m) →
      ¬ (lay.queueAddr ≤ a ∧ a < lay.queueAddr + P.edges.length) →
      a ≠ lay.base + t3OffEcongUpd → m3 a = mem_gp a := fun a ha hgp h1 h2 h3 h4 h5 h6 =>
    ((hm3_arr a h1 h2 (by omega)).trans (hES.mem_agree a h6 h3 h4 h5 (by omega))).trans (hMemStart_gp a ha hgp)
  have hm3_gp_below : ∀ a, lay.staticEnd ≤ a → a < hMid → m3 a = mem_gp a := fun a ha1 ha2 =>
    hm3_mid_agree a ha2 (by unfold t3OffGetPath; omega) (by unfold t3OffHCur; omega)
      (by omega) (by omega) (by omega) (by omega) (by unfold t3OffEcongUpd; omega)
  have hm3_hdl : ∀ cj < ctx.wd.comps.length, m3 (lay.dsHandlesAddr + cj) = mem_gp (lay.dsHandlesAddr + cj) :=
    fun cj hcj => hm3_mid_agree _ (by omega) (by unfold t3OffGetPath; omega)
      (by unfold t3OffHCur; omega) (by omega) (by omega) (by omega) (by omega)
      (by unfold t3OffEcongUpd; omega)
  have hm3_zf : WordRAM.ZeroFrom m3 hNext := fun a ha => by
    rw [hm3_arr a (by unfold t3OffHCur; omega) (by omega) (by omega),
      hES.mem_agree a (by unfold t3OffEcongUpd; omega) (by omega) (by omega) (by omega) (by omega)]
    exact hMemStart_zf a (by omega)
  have hds_m3 := hdsArr_mid.mono_hCur hLoc (Nat.le_add_right hMid _) hm3_hdl hm3_gp_below hm3_zf
  have hds_phi_m3 : dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 m3 =
      dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 st.mem := by
    unfold dsTotalPhi; refine Finset.sum_congr rfl fun cj hcj => ?_
    have hcj' := Finset.mem_range.mp hcj
    have hh_st := hm3_arr (lay.dsHandlesAddr + cj) (by unfold t3OffHCur; omega) (by omega) (by omega)
    have hh_gp : st.mem (lay.dsHandlesAddr + cj) = mem_gp (lay.dsHandlesAddr + cj) := hh_st.symm.trans (hm3_hdl cj hcj')
    rw [hh_st]
    refine (hLoc _ (d0.states cj) (reps1 cj) st.mem m3 fun a ha => ?_).2.symm
    have hab := (hdsArr_mid.at_ci cj hcj').2.2.2.1 a (hh_gp ▸ ha)
    exact (hm3_arr a (by unfold t3OffHCur; omega) (by omega) (by omega)).symm
  let P_lift := liftWSubWalk ctx.wd.comps[ci] P
  let P_lift0 := liftWSubWalk (ctx.wInp.mkWitnessData impl.constructExpander impl.pathDS.params ctx.WSubs).comps[ci] P
  have hPl_len : P_lift.edges.length = P.edges.length := hPl_w.2.1
  have hPl_eq : Walk.mk P_lift0.verts (List.take P.edges.length P_lift0.edges) = P_lift := by
    change Walk.mk P_lift.verts (List.take P.edges.length P_lift.edges) = P_lift
    cases hpl : P_lift with
    | mk vs es =>
      have hlen : es.length = P.edges.length := by change P_lift.edges.length = P.edges.length at hPl_len; rwa [hpl] at hPl_len
      dsimp only; rw [← hlen, List.take_length]
  let emb1 := Function.update d0.emb eJ (some P_lift)
  have hembk_eq : Function.update d0.emb eJ (some (Walk.mk P_lift0.verts (List.take P.edges.length P_lift0.edges))) = emb1 :=
    congrArg (Function.update d0.emb eJ) (congrArg some hPl_eq)
  have hWalk_m3 : WalkAt m3 hMid P_lift := by
    rw [walkAt_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : m3 hMid = m1 hMid := by dsimp only [m3, m2]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by unfold t3OffHCur; omega)]
      rw [this]; dsimp only [m1]; rw [Function.update_self]; simp [P_lift, liftWSubWalk]
    · intro i hi
      have hi' : i < P.verts.length := by simpa [P_lift, liftWSubWalk] using hi
      rw [hm3_arr (hMid + 1 + i) (by unfold t3OffHCur; omega) (by omega) (by omega),
        hES.mem_agree _ (by unfold t3OffEcongUpd; omega) (by omega) (by omega) (by omega) (by omega),
        hMemStart_verts i hi']
      simp [P_lift, liftWSubWalk]
    · have hvl : P_lift.verts.length = P.verts.length := by simp [P_lift, liftWSubWalk]
      rw [hvl, hm3_arr _ (by unfold t3OffHCur; omega) (by omega) (by omega),
        hES.mem_agree _ (by unfold t3OffEcongUpd; omega) (by omega) (by omega) (by omega) (by omega), hMemStart_elen]
      exact hPl_len.symm
    · intro i hi
      have hi' : i < P.edges.length := by rw [← hPl_len]; exact hi
      have hvl : P_lift.verts.length = P.verts.length := by simp [P_lift, liftWSubWalk]
      rw [hvl, hm3_arr _ (by unfold t3OffHCur; omega) (by omega) (by omega), hES.walk_edges_eq i hi' hi']
      simp [P_lift, liftWSubWalk]
  have hm3_arr_pre : ∀ a, lay.econgCountAddr ≤ a → a < lay.vhatOffsetAddr → m3 a = st.mem a :=
    fun a ha1 ha2 => hm3_arr a (by unfold t3OffHCur; omega) (by omega) (by omega)
  have hm3_ecPhi : t3EcongPhi ctx lay m3 = t3EcongPhi ctx lay st.mem :=
    t3EcongPhi_frame ctx lay
      (fun eW heW => hm3_arr_pre _ (Nat.le_add_right _ _) (by have := (Finset.mem_Ico.mp heW).2; omega))
      (fun eW heW => hm3_arr_pre _ (by omega) (by have := (Finset.mem_Ico.mp heW).2; omega))
  have hm3_hdr_eq : ∀ {off : ℕ}, off ≠ t3OffHCur → off ≠ t3OffEcongUpd → off < t3HdrSize →
      m3 (lay.base + off) = memStart (lay.base + off) := fun {off} hhc heu hoff => by
    unfold t3HdrSize at hoff
    exact (hm3_arr _ (by omega) (by omega) (by omega)).trans
      (hES.mem_agree _ (by omega) (by omega) (by omega) (by omega) (by omega))
  let d_mid : T3RoundData impl.pathDS :=
    ⟨emb1, d0.getPathCnt + 1, d0.delCnt, d0.econgUpd + P.edges.length, hNext, d0.states, reps1, d0.nextHasUnemb⟩
  let hSt3 : State := ⟨m3, st.regs, st.pos⟩
  have hD_mid : T3DrainQueueAt ctx lay rCur Q (d0.getPathCnt + 1) d0.delCnt (d0.econgUpd + P.edges.length)
      emb1 d0.nextHasUnemb 0 d_mid hSt3 (t3RoundPhi ctx lay d_mid m3) := by
    refine ⟨hR.rCur_pos, hR.rCur_le, Nat.zero_le _, hQnd, le_trans hQk hP_edges_le, hGpc_succ, hDel_add_Q,
      by have h1 := hR.econgUpd_bound; push_cast; linarith, heUpd_next_W,
      ListAt.congr hQL (fun k _ _ => hm3_arr_pre k (by omega) (by omega)),
      fun eW heW => let q := hQval eW heW; ⟨q.2.1, q.2.2.1, (hm3_arr_pre _ (by omega) (by omega)).trans q.2.2.2⟩,
      rfl, rfl, rfl, rfl, rfl, hm3_static, hds_m3.1, by dsimp only [d_mid, hNext]; omega, hNext_bd, hm3_zf, ?_, ?_, ?_, ?_, ?_, ?_,
      hR.nextU_bin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · dsimp only [hSt3]; rw [hm3_hdr_eq (by unfold t3OffEta2 t3OffHCur; decide) (by unfold t3OffEta2 t3OffEcongUpd; decide) (by unfold t3OffEta2 t3HdrSize; decide)]; exact hMemStart_hdr.1
    · dsimp only [hSt3]; rw [hm3_hdr_eq (by unfold t3OffGetPath t3OffHCur; decide) (by unfold t3OffGetPath t3OffEcongUpd; decide) (by unfold t3OffGetPath t3HdrSize; decide)]; exact hMemStart_hdr.2.1
    · dsimp only [hSt3]; rw [hm3_hdr_eq (by unfold t3OffDel t3OffHCur; decide) (by unfold t3OffDel t3OffEcongUpd; decide) (by unfold t3OffDel t3HdrSize; decide)]; exact hMemStart_hdr.2.2.1
    · exact (hm3_arr _ (by unfold t3OffEcongUpd t3OffHCur; omega) (by unfold t3OffEcongUpd; omega) (by unfold t3OffEcongUpd; omega)).trans hES.econgUpd_eq
    · dsimp only [hSt3, m3, m2]; rw [Function.update_of_ne (by unfold t3OffHCur; omega), Function.update_self]
    · dsimp only [hSt3]; rw [hm3_hdr_eq (by unfold t3OffNextU t3OffHCur; decide) (by unfold t3OffNextU t3OffEcongUpd; decide) (by unfold t3OffNextU t3HdrSize; decide)]; exact hMemStart_hdr.2.2.2
    · refine ⟨hR.emb_part.1, fun j hj Q' hQ' => ?_⟩; dsimp only [emb1] at hQ'
      by_cases hje : j = eJ
      · subst hje; rw [Function.update_self, Option.some.injEq] at hQ'; subst hQ'; exact hJ_edge ▸ hPl_w.1
      · rw [Function.update_of_ne hje] at hQ'; exact hR.emb_part.2 j hj Q' hQ'
    · intro e' he' hcase; dsimp only [emb1]; by_cases heq : e' = eJ
      · subst heq; simp
      · simp only [Function.update_of_ne heq]; exact hR.emb_j0_cov e' he' hcase
    · intro e' he' Q' hQ'; dsimp only [emb1] at hQ'; by_cases heq : e' = eJ
      · subst heq; rw [Function.update_self, Option.some.injEq] at hQ'; subst hQ'; exact hPl_w.2.2.1 hP_nd
      · rw [Function.update_of_ne heq] at hQ'; exact hR.emb_nodup e' he' Q' hQ'
    · intro e' he'; dsimp only [emb1]; by_cases heq : e' = eJ
      · subst heq; simpa [partialToWalk, hPl_len] using hP_edges_le
      · simpa [partialToWalk, Function.update_of_ne heq] using hR.emb_len_W e' he'
    · intro e' he'; dsimp only [emb1]; by_cases heq : e' = eJ
      · subst heq; simpa [partialToWalk, hPl_len] using hP_len_r
      · simpa [partialToWalk, Function.update_of_ne heq] using hR.emb_len_real e' he'
    · intro e' he'; by_cases heq : e' = eJ
      · subst heq; simp only [hSt3, emb1, Function.update_self]; rw [show m3 (lay.embJWAddr + e') = hMid from Function.update_self _ _ _]
        refine ⟨by omega, ?_, hWalk_m3, fun a ha1 ha2 cj hcj hft => ?_⟩
        · have hlen := walk_encode_length P_lift; have hvl : P_lift.verts.length = P.verts.length := by simp [P_lift, liftWSubWalk]
          rw [hlen, hvl, hPl_len]
        · rw [hm3_hdl cj hcj] at hft; have := (hdsArr_mid.at_ci cj hcj).2.2.2.1 a hft; omega
      · have hne_e : lay.embJWAddr + e' ≠ lay.embJWAddr + eJ := by omega
        have hm_e : m3 (lay.embJWAddr + e') = mem_gp (lay.embJWAddr + e') :=
          hm3_mid_agree _ (by omega) (by unfold t3OffGetPath; omega) (by unfold t3OffHCur; omega)
            hne_e (by omega) (by omega) (by omega) (by unfold t3OffEcongUpd; omega)
        have hOM := hOld_mem_gp e' he'; simp only [hSt3, emb1, Function.update_of_ne heq, hm_e]
        cases hde : d0.emb e' with
        | none => rw [hde] at hOM; exact hOM
        | some P' => rw [hde] at hOM; refine ⟨hOM.1, by dsimp only [d_mid, hNext]; omega,
            t3_walkAt_of_agree hOM.2.2.1 fun a ha1 ha2 => hm3_mid_agree a (by omega) (by unfold t3OffGetPath; omega)
              (by unfold t3OffHCur; omega) (by omega) (by omega) (by omega) (by omega) (by unfold t3OffEcongUpd; omega),
            fun a ha1 ha2 cj hcj => by rw [hm3_hdl cj hcj]; exact hOM.2.2.2 a ha1 ha2 cj hcj⟩
    · intro eW heW; exact (hm3_arr_pre _ (Nat.le_add_right _ _) (by omega)).trans (hembk_eq ▸ hCnt_eq eW heW)
    · intro eW heW; exact hembk_eq ▸ hEc_r eW heW
    · intro eW heW; rw [t3_middle_econg_j0_eq ctx hci hunemb hP_wk heW]; exact hR.econg_j0_le eW heW
    · intro eW heW; dsimp only [hSt3]; exact (hm3_arr _ (by unfold t3OffHCur; omega) (by omega) (by omega)).trans
        ((hES.wdel_j0 eW heW).trans (hMemStart_wdel_j0 eW heW))
    · intro eW heW; dsimp only [hSt3]; rw [hm3_arr_pre _ (by omega) (by have := (Finset.mem_Ico.mp heW).2; omega),
        hm3_arr_pre _ (Nat.le_add_right _ _) (by have := (Finset.mem_Ico.mp heW).2; omega)]; exact hWdc eW heW
    · intro eW heW hst'; dsimp only [hSt3] at hst' ⊢; rw [hm3_arr_pre _ (by omega) (by have := (Finset.mem_Ico.mp heW).2; omega)] at hst'; exact hembk_eq ▸ hWdt eW heW hst'
    · intro eW heW hlt'; dsimp only [hSt3] at hlt' ⊢; rw [hm3_arr_pre _ (by omega) (by have := (Finset.mem_Ico.mp heW).2; omega)] at hlt'; exact hembk_eq ▸ hWdlt eW heW hlt'
    · dsimp only [hSt3]; rw [hUsum]; exact Finset.sum_congr rfl fun eW heW => (hm3_arr_pre _ (Nat.le_add_right _ _) (by have := (Finset.mem_Ico.mp heW).2; omega)).symm
    · have hc := hR.getPath_cnt_le; have hmem : eJ ∈ unembeddedSet2Pure inp.J d0.emb := by simp [unembeddedSet2Pure, heJ, hunemb]
      have hS_le : (unembeddedSet2Pure inp.J d0.emb).card ≤ inp.J.m :=
        (Finset.card_le_card (Finset.filter_subset _ (Finset.range inp.J.m))).trans_eq (Finset.card_range _)
      have hsub : unembeddedSet2Pure inp.J emb1 = (unembeddedSet2Pure inp.J d0.emb).erase eJ := by
        ext j; simp only [unembeddedSet2Pure, Finset.mem_filter, Finset.mem_range, Finset.mem_erase, emb1]
        by_cases hj : j = eJ <;> simp [hj, Function.update_of_ne]
      rw [hsub, Finset.card_erase_of_mem hmem]; have := Finset.card_pos.mpr ⟨eJ, hmem⟩; omega
    · intro cj hcj eL heL; have hc_b := (ctx.hw_okW.comp_props cj hcj).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      dsimp only [hSt3]; rw [List.drop_zero, hm3_arr_pre (lay.wDelStampAddr + (ctx.wd.comps[cj].wStart + eL)) (by omega) (by omega)]; exact hDQ cj hcj eL heL
    · intro cj hcj v hv; have ha1 := vhatBaseW_add_le hcj; have hs := vhatBaseW_le_sum (wd := ctx.wd) (ci := cj + 1)
      dsimp only [hSt3]; rw [hm3_mid_agree (lay.vhatStampAddr + vhatBaseW ctx.wd cj + v) (by omega) (by unfold t3OffGetPath; omega)
        (by unfold t3OffHCur; omega) (by omega) (by omega) (by omega) (by omega) (by unfold t3OffEcongUpd; omega),
        ← hMemStart_gp (lay.vhatStampAddr + vhatBaseW ctx.wd cj + v) (by omega) (by unfold t3OffGetPath; omega)]; exact hMemStart_vhat.1 cj hcj v hv
    · intro cj hcj v hv; have ha1 := vhatBaseW_add_le hcj; have hs := vhatBaseW_le_sum (wd := ctx.wd) (ci := cj + 1)
      dsimp only [hSt3]; rw [hm3_mid_agree (lay.vhatStampAddr + vhatBaseW ctx.wd cj + v) (by omega) (by unfold t3OffGetPath; omega)
        (by unfold t3OffHCur; omega) (by omega) (by omega) (by omega) (by omega) (by unfold t3OffEcongUpd; omega),
        ← hMemStart_gp (lay.vhatStampAddr + vhatBaseW ctx.wd cj + v) (by omega) (by unfold t3OffGetPath; omega)]; exact hMemStart_vhat.2 cj hcj v hv
  have hPhi_split : Φ = t3RoundPhi ctx lay d_mid m3 + t3KdelCost impl inp.J * Q.length := by
    rw [hΦ_eq]; simp only [Nat.sub_self, add_zero, t3RoundPhi, hm3_ecPhi]; rw [hds_phi_m3]; dsimp only [d_mid]; ring
  have hcond : ∃ stF c Φ', Runs w p ω (.cond (t3Lt (.const 0) (.reg 18)) (.call 25 (selfBase + 2) [.reg 0, .reg 1, .reg 18]) .nop)
        hSt3 .normal stF c ∧ (∃ d', T3RoundAt ctx lay rCur d' stF Φ' ∧ d'.getPathCnt = d0.getPathCnt + 1 ∧
        d'.econgUpd = d0.econgUpd + P.edges.length ∧ (∀ cj < ctx.wd.comps.length, (d0.states cj).Vhat ⊆ (d'.states cj).Vhat) ∧
        (∀ e' < inp.J.m, e' ≠ eJ → d'.emb e' = d0.emb e') ∧ d'.emb eJ = some P_lift ∧ d'.nextHasUnemb = d0.nextHasUnemb) ∧
      c + Φ' ≤ 10 + Φ := by
    have hQLen_w : Q.length < 2 ^ w := by omega
    by_cases hqz : Q.length = 0
    · have hev0 : (t3Lt (.const 0) (.reg 18)).eval w hSt3 = some 0 := by
        have hlt := Expr.eval_lt_op (Expr.eval_const (by omega : 0 < 2 ^ w)) (Expr.eval_reg_of_eq hr18) hw1
        rwa [hqz, ite_eq_right_iff.mpr (by omega)] at hlt
      have hD_mid' := hD_mid; rw [← hqz] at hD_mid'
      refine ⟨hSt3, 5, t3RoundPhi ctx lay d_mid m3,
        runs_cond_iff.mpr ⟨0, 1, hev0, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size, t3Lt]⟩,
        ⟨d_mid, hD_mid'.toRoundAt, rfl, rfl, fun _ _ => Finset.Subset.rfl, fun _ _ heq => by dsimp only [d_mid, emb1]; rw [Function.update_of_ne heq], by simp [d_mid, emb1], rfl⟩,
        by rw [hPhi_split, hqz, mul_zero, add_zero]; omega⟩
    · have hqpos : 0 < Q.length := Nat.pos_of_ne_zero hqz
      have hev1 : (t3Lt (.const 0) (.reg 18)).eval w hSt3 = some 1 := by
        have hlt := Expr.eval_lt_op (Expr.eval_const (by omega : 0 < 2 ^ w)) (Expr.eval_reg_of_eq hr18) hw1
        rwa [ite_eq_left_iff.mpr (fun h => absurd hqpos h)] at hlt
      obtain ⟨o_dq, st_dq, c_dq, Φ_dq, hr_dq, hq_dq, hc_dq⟩ :=
        t3DrainQueue_ptriple ctx lay hlay hSpec hdrain (rCur := rCur) (Q := Q) (g1 := d0.getPathCnt + 1)
          (del0 := d0.delCnt) (eUpd1 := d0.econgUpd + P.edges.length) (emb1 := emb1) (nextU := d0.nextHasUnemb)
          (V0 := fun cj => (d0.states cj).Vhat) (startState [lay.base, rCur, Q.length] m3 st.pos) (t3RoundPhi ctx lay d_mid m3) ω
          ⟨d_mid, t3DrainQueueAt_with_regs hD_mid, fun _ _ => Finset.Subset.rfl, rfl, rfl, rfl⟩
      rcases hq_dq with ⟨d', hD', hV'⟩
      have hcall_dq : Runs w p ω (.call 25 (selfBase + 2) [.reg 0, .reg 1, .reg 18]) hSt3 .normal
          { st_dq with regs := Function.update hSt3.regs 25 o_dq.value } (3 + c_dq + 1) :=
        runs_call_iff.mpr ⟨[lay.base, rCur, Q.length], t3DrainQueueBody dsBase, o_dq, st_dq, c_dq,
          (by simp [evalArgs, hSt3, hregs.1, hregs.2.1, hr18, Expr.eval]), hdrain, hr_dq, rfl, rfl, by simp [argsSize]⟩
      have hkdel : Q.length * (⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 86) + 40 ≤ t3KdelCost impl inp.J * Q.length := by
        have hkd : t3KdelCost impl inp.J = ⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 140 := by unfold t3KdelCost; rfl
        have h54 : 40 ≤ 54 * Q.length := by omega
        have hmul : Q.length * (⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 86) + 54 * Q.length =
            (⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) : ℝ)⌉₊ + 140) * Q.length := by ring
        rw [hkd]; omega
      refine ⟨{ st_dq with regs := Function.update st.regs 25 o_dq.value }, 3 + (3 + c_dq + 1) + 1, Φ_dq,
        runs_cond_iff.mpr ⟨1, 3 + c_dq + 1, hev1, hcall_dq, by simp [Expr.size, t3Lt]⟩,
        ⟨d', t3RoundAt_with_regs hD'.toRoundAt, hD'.d_g, hD'.d_eUpd, hV', fun _ _ heq => by rw [hD'.d_emb]; dsimp only [emb1]; rw [Function.update_of_ne heq],
          by simp [hD'.d_emb, emb1], hD'.d_nextU⟩,
        by rw [hPhi_split]; have hsum := Nat.add_le_add_right (le_trans hc_dq (Nat.add_le_add_right hkdel _)) 10; omega⟩
  apply t3_ptriple_of_cps
  have hNext_w : hNext < 2 ^ w := by omega
  have hev_hNext : (t3Add (.reg 13) (t3Add (t3Add (.const 2) (.reg 14)) (.reg 15))).eval w ⟨m1, st.regs, st.pos⟩ = some hNext :=
    Expr.eval_add (Expr.eval_reg_of_eq hregs.2.2.2.1)
      (Expr.eval_add (Expr.eval_add (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hregs.2.2.2.2.1) (by omega))
        (Expr.eval_reg_of_eq hregs.2.2.2.2.2) (by omega)) hNext_w
  have hev_ejAddr : (t3Add (t3Ld (.reg 0) (.const t3OffEmbJW)) (.reg 2)).eval w ⟨m2, st.regs, st.pos⟩ = some (lay.embJWAddr + eJ) := by
    have hm2_ej : m2 (lay.base + t3OffEmbJW) = lay.embJWAddr := by
      have h1 : m2 (lay.base + t3OffEmbJW) = m1 (lay.base + t3OffEmbJW) := by dsimp only [m2]; rw [Function.update_of_ne (by unfold t3OffEmbJW t3OffHCur; omega)]
      have h2 : m1 (lay.base + t3OffEmbJW) = st.mem (lay.base + t3OffEmbJW) := by dsimp only [m1]; rw [Function.update_of_ne (by unfold t3OffEmbJW; omega)]
      rw [h1, h2, hES.mem_agree _ (by unfold t3OffEmbJW t3OffEcongUpd; omega) (by unfold t3OffEmbJW; omega) (by unfold t3OffEmbJW; omega) (by unfold t3OffEmbJW; omega) (by unfold t3OffEmbJW; omega)]
      exact hMemStart_static.2.1
    exact Expr.eval_add (hm2_ej ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hregs.1) (Expr.eval_const (by unfold t3OffEmbJW; omega)) (by unfold t3OffEmbJW; omega))) (Expr.eval_reg_of_eq hregs.2.2.1) (by omega)
  refine t3_store_cps (Expr.eval_reg_of_eq hregs.2.2.2.1) (Expr.eval_reg_of_eq hregs.2.2.2.2.1) ?_
  refine t3_store_cps (Expr.eval_add (Expr.eval_reg_of_eq hregs.1) (Expr.eval_const (by unfold t3OffHCur; omega)) (by unfold t3OffHCur; omega)) hev_hNext ?_
  refine t3_store_cps hev_ejAddr (Expr.eval_reg_of_eq hregs.2.2.2.1) ?_
  rcases hcond with ⟨stC, c_c, Φ', hr_c, hq_c, hc_c⟩
  refine ⟨.returned 0, stC, c_c + 2 + 1, Φ',
    runs_seq_iff.mpr (Or.inr ⟨stC, c_c, 2, hr_c, runs_ret_iff.mpr ⟨0, Expr.eval_const (by omega : 0 < 2 ^ w), rfl, rfl, rfl⟩, rfl⟩),
    ⟨rfl, hq_c⟩, ?_⟩
  simp only [Expr.size, t3Add, t3Ld]; omega


end MinCostFlow.Spanner
