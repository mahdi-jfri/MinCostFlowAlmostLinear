module

public import MinCostFlow.Spanner.ProgTask1Steps

/-!
# Verification and Contract Satisfaction for `task1Module`

This module finishes the proof of `task1Body_triple` (stage 5 `buildWitnessCore`, directory stores
at `[h, h + 6)`, and `ret`) and proves `task1_meetsContract`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

private structure HdrInvData (inp : Task1Input) (impl : SpannerToolImpl) (mem₀ : ℕ → ℕ) (w : ℕ)
    (k : ℕ) (st : State) where
  wInp : WitnessCoreInput
  WSubs : List Graph
  vEnd : ℕ
  hw_H' : wInp.H' = inp.H'
  hw_emb : wInp.embJH = inp.embJH
  hw_J : wInp.prep.J = inp.J
  hw_jAddr : wInp.prep.jAddr = inp.jAddr
  hw_stats : wInp.statsAddr = inp.h + 6
  hw_j0Addr : wInp.prep.j0Addr = inp.j0Addr
  hw_nlAddr : wInp.prep.nlAddr = inp.nlAddr
  hw_decAddr : wInp.prep.decAddr = inp.decAddr
  hw_cℓ : wInp.prep.c_ℓ = impl.decompose.c_ℓ
  h_below : ∀ x < inp.h, st.mem x = mem₀ x
  h_zf : ZeroFrom st.mem vEnd
  hv_ge20 : wInp.h + 20 ≤ vEnd
  hv_max : vEnd ≤ wInp.maxHeapEnd impl.constructExpander impl.pathDS.params
  hv_cap : vEnd ≤ inp.maxHeapEnd impl
  hv_w : vEnd < 2 ^ w
  h1w : 1 < 2 ^ w
  hs0 : st.mem wInp.statsAddr = maxDeg inp.J
  hs1 : st.mem (wInp.statsAddr + 1) = length inp.J inp.embJH
  hs2 : st.mem (wInp.statsAddr + 2) = vcongNat inp.J inp.H' inp.embJH
  h_static_state : PrepStaticState wInp.prep st.mem st.mem
  h_comps_done : CompsDoneUpTo wInp.prep st.mem wInp.prep.rawComps.length
  h_static_valid : wInp.prep.StaticValid st.mem w
  h_wsubs : wInp.ValidWSubs impl.constructExpander WSubs
  h_phi_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤
    (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec
  h_phi_cap : wInp.prep.phiDen_dec ≤ impl.decompose.maxPhiDen wInp.prep.J0_strip.m
  h_out : ∀ (memPre : ℕ → ℕ),
    wInp.OutputAt impl.constructExpander impl.pathDS.params
      (fun x => if x < wInp.h then st.mem x else memPre x) st.mem vEnd
      (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs)
  h_ok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
    WitnessOK tools inp.H' inp.J inp.embJH
      (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs)
  h_hend : wInp.prep.hEnd ≤ wInp.h
  hr3 : st.regs 3 = inp.h
  hr5 : st.regs 5 = wInp.statsAddr
  hr6 : st.regs 6 = wInp.prep.j0Addr
  hr8 : st.regs 8 = wInp.prep.nlAddr
  hr10 : st.regs 10 = wInp.prep.decAddr
  hr11 : st.regs 11 = wInp.prep.h
  hr12 : st.regs 12 = wInp.h
  hr13 : st.regs 13 = vEnd
  h_prep_ge : inp.h + 6 < wInp.prep.h
  h_h_ge : wInp.prep.h ≤ wInp.h
  h_jj_lt : wInp.prep.jAddr + wInp.prep.J.encode.length ≤ inp.h
  hm0 : 1 ≤ k → st.mem inp.h = wInp.statsAddr
  hm1 : 2 ≤ k → st.mem (inp.h + 1) = wInp.prep.j0Addr
  hm2 : 3 ≤ k → st.mem (inp.h + 2) = wInp.prep.nlAddr
  hm3 : 4 ≤ k → st.mem (inp.h + 3) = wInp.prep.decAddr
  hm4 : 5 ≤ k → st.mem (inp.h + 4) = wInp.prep.h
  hm5 : 6 ≤ k → st.mem (inp.h + 5) = wInp.h

private abbrev HdrInv (inp : Task1Input) (impl : SpannerToolImpl) (mem₀ : ℕ → ℕ) (w : ℕ)
    (k : ℕ) (st : State) : Prop :=
  Nonempty (HdrInvData inp impl mem₀ w k st)

private def hdrInv_update_reg14 {inp : Task1Input} {impl : SpannerToolImpl} {mem₀ : ℕ → ℕ}
    {w k : ℕ} {st : State} {val : ℕ} (hi : HdrInvData inp impl mem₀ w k st) :
    HdrInvData inp impl mem₀ w k { mem := st.mem, regs := Function.update st.regs 14 val, pos := st.pos } :=
  ⟨hi.wInp, hi.WSubs, hi.vEnd, hi.hw_H', hi.hw_emb, hi.hw_J, hi.hw_jAddr, hi.hw_stats,
    hi.hw_j0Addr, hi.hw_nlAddr, hi.hw_decAddr, hi.hw_cℓ, hi.h_below, hi.h_zf, hi.hv_ge20,
    hi.hv_max, hi.hv_cap, hi.hv_w, hi.h1w, hi.hs0, hi.hs1, hi.hs2, hi.h_static_state, hi.h_comps_done,
    hi.h_static_valid, hi.h_wsubs, hi.h_phi_lb, hi.h_phi_cap, hi.h_out, hi.h_ok, hi.h_hend,
    by simp [Function.update, hi.hr3], by simp [Function.update, hi.hr5],
    by simp [Function.update, hi.hr6], by simp [Function.update, hi.hr8],
    by simp [Function.update, hi.hr10], by simp [Function.update, hi.hr11],
    by simp [Function.update, hi.hr12], by simp [Function.update, hi.hr13],
    hi.h_prep_ge, hi.h_h_ge, hi.h_jj_lt,
    hi.hm0, hi.hm1, hi.hm2, hi.hm3, hi.hm4, hi.hm5⟩

private def hdrInv_step {inp : Task1Input} {impl : SpannerToolImpl} {mem₀ : ℕ → ℕ} {w : ℕ}
    {k k' : ℕ} {st : State} (hi : HdrInvData inp impl mem₀ w k st)
    {off val : ℕ} (hoff : off < 6) (hregs : ∀ x < inp.h, st.mem x = mem₀ x)
    (hm_k' :
      let mem' := Function.update st.mem (inp.h + off) val
      (1 ≤ k' → mem' inp.h = hi.wInp.statsAddr) ∧
      (2 ≤ k' → mem' (inp.h + 1) = hi.wInp.prep.j0Addr) ∧
      (3 ≤ k' → mem' (inp.h + 2) = hi.wInp.prep.nlAddr) ∧
      (4 ≤ k' → mem' (inp.h + 3) = hi.wInp.prep.decAddr) ∧
      (5 ≤ k' → mem' (inp.h + 4) = hi.wInp.prep.h) ∧
      (6 ≤ k' → mem' (inp.h + 5) = hi.wInp.h)) :
    let mem' := Function.update st.mem (inp.h + off) val
    HdrInvData inp impl mem₀ w k' { mem := mem', regs := st.regs, pos := st.pos } := by
  intro mem'
  have hne_mem : ∀ x, x ≠ inp.h + off → mem' x = st.mem x := fun x hx =>
    Function.update_of_ne hx val st.mem
  have hagree_out : ∀ x, x < inp.h ∨ inp.h + 6 ≤ x → mem' x = st.mem x := fun x hx =>
    hne_mem x (by omega)
  have hprep_lt : inp.h + 6 < hi.wInp.h := lt_of_lt_of_le hi.h_prep_ge hi.h_h_ge
  have hrange : ∀ x, hi.wInp.prep.h ≤ x → x < hi.wInp.prep.hEnd → mem' x = st.mem x := by
    intro x hx1 _; exact hagree_out x (Or.inr (by have := hi.h_prep_ge; omega))
  have ⟨hss, hcd⟩ := prepStatic_and_comps_of_agree_range hi.h_static_valid hi.h_static_state
    hi.h_comps_done hrange
  have hsv := prepStaticValid_of_agree_outside hi.h_static_valid
    (by rw [hi.hw_j0Addr]; unfold Task1Input.j0Addr; omega)
    (by rw [hi.hw_nlAddr]; unfold Task1Input.nlAddr Task1Input.j0Addr; omega)
    (by rw [hi.hw_decAddr]; unfold Task1Input.decAddr Task1Input.nlAddr Task1Input.j0Addr; omega)
    hagree_out hi.h_jj_lt
  have hout' : ∀ (memPre : ℕ → ℕ),
      hi.wInp.OutputAt impl.constructExpander impl.pathDS.params
        (fun x => if x < hi.wInp.h then mem' x else memPre x) mem' hi.vEnd
        (hi.wInp.mkWitnessData impl.constructExpander impl.pathDS.params hi.WSubs) := by
    intro memPre
    have hprev := hi.h_out memPre
    have hhi_mem : ∀ x, hi.wInp.h ≤ x → mem' x = st.mem x := fun x hx =>
      hagree_out x (Or.inr (by omega))
    rcases hprev with ⟨_, hzf, hv1, hv2, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h17, h18, h19,
      rest⟩
    refine ⟨fun x hx => by dsimp only; simp only [hx, ↓reduceIte],
      fun x hx => by rw [hhi_mem x (by omega)]; exact hzf x hx,
      hv1, hv2,
      by rw [hhi_mem _ le_rfl]; exact h0,
      by rw [hhi_mem _ (by omega)]; exact h1,
      by rw [hhi_mem _ (by omega)]; exact h2,
      by rw [hhi_mem _ (by omega)]; exact h3,
      by rw [hhi_mem _ (by omega)]; exact h4,
      by rw [hhi_mem _ (by omega)]; exact h5,
      by rw [hhi_mem _ (by omega)]; exact h6,
      by rw [hhi_mem _ (by omega)]; exact h7,
      by rw [hhi_mem _ (by omega)]; exact h8,
      by rw [hhi_mem _ (by omega)]; exact h9,
      by rw [hhi_mem _ (by omega)]; exact h10,
      by rw [hhi_mem _ (by omega)]; exact h11,
      by rw [hhi_mem _ (by omega)]; exact h17,
      by rw [hhi_mem _ (by omega)]; exact h18,
      by rw [hhi_mem _ (by omega)]; exact h19, ?_⟩
    dsimp only at rest ⊢
    rw [hhi_mem _ (by omega), hhi_mem _ (by omega), hhi_mem _ (by omega),
      hhi_mem _ (by omega), hhi_mem _ (by omega)]
    rcases rest with ⟨a1, a2, a3, a4, a5, a6, hc, hg, hw, hws, hjs⟩
    refine ⟨a1, a2, a3, a4, a5, a6, ?_, ?_, ?_, ?_, ?_⟩
    · intro kc hkc
      rcases hc kc hkc with ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩
      dsimp only
      have hwsub_ptr : mem' (st.mem (hi.wInp.h + 12) + 6 * kc + 1) =
          st.mem (st.mem (hi.wInp.h + 12) + 6 * kc + 1) := hhi_mem _ (by omega)
      rw [hwsub_ptr]
      refine ⟨by rw [hhi_mem _ (by omega)]; exact r1,
        by rw [hhi_mem _ (by omega)]; exact r2,
        by rw [hhi_mem _ (by omega)]; exact r3,
        by rw [hhi_mem _ (by omega)]; exact r4,
        by rw [hhi_mem _ (by omega)]; exact r5,
        ?_, r7, r8⟩
      intro i hi_g
      rw [hhi_mem _ (by omega)]
      exact r6 i hi_g
    · intro i hi_g; rw [hhi_mem _ (by omega)]; exact hg i hi_g
    · intro eW heW
      have hww := hw eW heW
      rwa [hhi_mem _ (by omega)]
    · intro eW heW
      have h := hws eW heW
      cases hsrc : (hi.wInp.mkWitnessData impl.constructExpander impl.pathDS.params hi.WSubs).wSources[eW] <;>
        simp only [hsrc] at h ⊢
      · exact ⟨by rw [hhi_mem _ (by omega)]; exact h.1,
          by rw [hhi_mem _ (by omega)]; exact h.2.1,
          by rw [hhi_mem _ (by omega)]; exact h.2.2⟩
      · exact ⟨by rw [hhi_mem _ (by omega)]; exact h.1,
          by rw [hhi_mem _ (by omega)]; exact h.2.1,
          by rw [hhi_mem _ (by omega)]; exact h.2.2⟩
    · intro eJ heJ
      have h := hjs eJ heJ
      cases hsrc : (hi.wInp.mkWitnessData impl.constructExpander impl.pathDS.params hi.WSubs).jSources[eJ] <;>
        simp only [hsrc] at h ⊢
      · exact ⟨by rw [hhi_mem _ (by omega)]; exact h.1,
          by rw [hhi_mem _ (by omega)]; exact h.2.1,
          by rw [hhi_mem _ (by omega)]; exact h.2.2⟩
      · exact ⟨by rw [hhi_mem _ (by omega)]; exact h.1,
          by rw [hhi_mem _ (by omega)]; exact h.2.1,
          by rw [hhi_mem _ (by omega)]; exact h.2.2⟩
      · exact ⟨by rw [hhi_mem _ (by omega)]; exact h.1,
          by rw [hhi_mem _ (by omega)]; exact h.2.1,
          by rw [hhi_mem _ (by omega)]; exact h.2.2⟩
  have hms := hm_k'
  refine ⟨hi.wInp, hi.WSubs, hi.vEnd, hi.hw_H', hi.hw_emb, hi.hw_J, hi.hw_jAddr, hi.hw_stats,
    hi.hw_j0Addr, hi.hw_nlAddr, hi.hw_decAddr, hi.hw_cℓ,
    fun x hx => by dsimp only; rw [hagree_out x (Or.inl hx)]; exact hregs x hx,
    fun x hx => by
      have := hi.hv_ge20
      dsimp only; rw [hagree_out x (Or.inr (by omega))]; exact hi.h_zf x hx,
    hi.hv_ge20, hi.hv_max, hi.hv_cap, hi.hv_w, hi.h1w,
    by dsimp only; rw [hagree_out _ (Or.inr (by rw [hi.hw_stats]))]; exact hi.hs0,
    by dsimp only; rw [hagree_out _ (Or.inr (by rw [hi.hw_stats]; omega))]; exact hi.hs1,
    by dsimp only; rw [hagree_out _ (Or.inr (by rw [hi.hw_stats]; omega))]; exact hi.hs2,
    hss, hcd, hsv, hi.h_wsubs, hi.h_phi_lb, hi.h_phi_cap, hout', hi.h_ok, hi.h_hend,
    hi.hr3, hi.hr5, hi.hr6, hi.hr8, hi.hr10, hi.hr11, hi.hr12, hi.hr13,
    hi.h_prep_ge, hi.h_h_ge, hi.h_jj_lt,
    hms.1, hms.2.1, hms.2.2.1, hms.2.2.2.1, hms.2.2.2.2.1, hms.2.2.2.2.2⟩

private lemma store_hdr_offset_seq {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task1Input} {mem₀ : ℕ → ℕ} (k k' off rVal : ℕ)
    (hoff : 1 ≤ off ∧ off < 6)
    (hstep : ∀ st (hi : HdrInvData inp impl mem₀ w k st),
      st.regs rVal < 2 ^ w ∧
      (let mem' := Function.update st.mem (inp.h + off) (st.regs rVal)
       (1 ≤ k' → mem' inp.h = hi.wInp.statsAddr) ∧
       (2 ≤ k' → mem' (inp.h + 1) = hi.wInp.prep.j0Addr) ∧
       (3 ≤ k' → mem' (inp.h + 2) = hi.wInp.prep.nlAddr) ∧
       (4 ≤ k' → mem' (inp.h + 3) = hi.wInp.prep.decAddr) ∧
       (5 ≤ k' → mem' (inp.h + 4) = hi.wInp.prep.h) ∧
       (6 ≤ k' → mem' (inp.h + 5) = hi.wInp.h)))
    {rest : Stmt} {Q : Outcome → State → Prop} {c : ℕ}
    (hrest : Triple w p (HdrInv inp impl mem₀ w k') rest Q (fun _ => c)) :
    Triple w p (HdrInv inp impl mem₀ w k)
      (Stmt.seq (Stmt.assign 14 (.bin .add (.reg 3) (.const off)))
        (Stmt.seq (Stmt.store (.reg 14) (.reg rVal)) rest))
      Q (fun _ => c + 10) := by
  have h1 : Triple w p (HdrInv inp impl mem₀ w k)
      (Stmt.assign 14 (.bin .add (.reg 3) (.const off)))
      (normalPost (fun st => HdrInv inp impl mem₀ w k st ∧ st.regs 14 = inp.h + off))
      (fun _ => 4) := by
    refine (Triple.assign (val := fun _ => inp.h + off) ?_ ?_).mono_cost
      fun _ _ => by simp [Expr.size]
    · intro st ⟨hi⟩
      have := hi.h_prep_ge; have := hi.h_h_ge; have := hi.hv_ge20; have := hi.hv_w
      have := hoff.1; have := hoff.2
      exact ev_add (ev_reg hi.hr3 (by omega)) (ev_const (by omega)) (by omega)
    · intro st ⟨hi⟩
      exact ⟨⟨hdrInv_update_reg14 hi⟩, by simp [Function.update]⟩
  have h2 : Triple w p (fun st => HdrInv inp impl mem₀ w k st ∧ st.regs 14 = inp.h + off)
      (Stmt.store (.reg 14) (.reg rVal))
      (normalPost (HdrInv inp impl mem₀ w k')) (fun _ => 3) := by
    refine (Triple.store (addr := fun _ => inp.h + off) (val := fun st => st.regs rVal) ?_ ?_ ?_).mono_cost
      fun _ _ => by simp [Expr.size]
    · intro st ⟨⟨hi⟩, hr14⟩
      have := hi.h_prep_ge; have := hi.h_h_ge; have := hi.hv_ge20; have := hi.hv_w; have := hoff.2
      exact ev_reg hr14 (by omega)
    · intro st ⟨⟨hi⟩, _⟩
      exact ev_reg rfl (hstep st hi).1
    · intro st ⟨⟨hi⟩, _⟩
      exact ⟨hdrInv_step hi hoff.2 hi.h_below (hstep st hi).2⟩
  have h23 := Triple.seq_normal_const h2 hrest
  have h123 := Triple.seq_normal_const h1 h23
  exact h123.mono_cost fun _ _ => by omega

private lemma step5_core_hdr_triple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task1Input} {mem₀ : ℕ → ℕ} {coreBase ceBase boundsBase : ℕ}
    (hcore : p.HasAt coreBase
      (buildWitnessCoreModule impl.constructExpander.phiNum impl.constructExpander.phiDen
        impl.constructExpander.c_deg_int ceBase boundsBase))
    (hce : p.HasAt ceBase (impl.constructExpander.procs ceBase))
    (hbounds : p.HasAt boundsBase (impl.pathDS.boundsProcs boundsBase)) :
    let m0 := (stripLoops inp.J).m
    let ce := impl.constructExpander
    let pds := impl.pathDS.params
    Triple w p
      (PrepDoneInv inp impl mem₀ w)
      (Stmt.seq (Stmt.call 13 coreBase [.reg 1, .reg 5, .reg 10, .reg 11, .reg 12]) <|
       Stmt.seq (Stmt.store (.reg 3) (.reg 5)) <|
       Stmt.seq (Stmt.assign 14 (.bin .add (.reg 3) (.const 1))) <|
       Stmt.seq (Stmt.store (.reg 14) (.reg 6)) <|
       Stmt.seq (Stmt.assign 14 (.bin .add (.reg 3) (.const 2))) <|
       Stmt.seq (Stmt.store (.reg 14) (.reg 8)) <|
       Stmt.seq (Stmt.assign 14 (.bin .add (.reg 3) (.const 3))) <|
       Stmt.seq (Stmt.store (.reg 14) (.reg 10)) <|
       Stmt.seq (Stmt.assign 14 (.bin .add (.reg 3) (.const 4))) <|
       Stmt.seq (Stmt.store (.reg 14) (.reg 11)) <|
       Stmt.seq (Stmt.assign 14 (.bin .add (.reg 3) (.const 5))) <|
       Stmt.seq (Stmt.store (.reg 14) (.reg 12)) <|
       Stmt.ret (.reg 13))
      (retPost fun v st' => Task1OutAt impl inp.jAddr inp.h inp.H' inp.J inp.embJH mem₀ st'.mem v w ∧
        v ≤ inp.maxHeapEnd impl)
      (fun _ =>
        (350 + pds.K_bounds * (Nat.log 2 (Task1Input.dJCap impl inp.J + m0 + 2) + 1) +
          pds.K_bounds * (Nat.log 2 (WitnessCoreInput.dWInt ce + Task1Input.mwCap impl inp.J + 2) + 1)) +
        (265 * m0 + 10 + (m0 + ⌈ce.K_ce * (4 * (m0 : ℝ) + 2 * (m0 : ℝ) / impl.decompose.φ_lb m0)⌉₊)) +
        (307 * m0 + 119 * Task1Input.mwCap impl inp.J + 120) + 70) := by
  have hcall : Triple w p (PrepDoneInv inp impl mem₀ w)
      (Stmt.call 13 coreBase [.reg 1, .reg 5, .reg 10, .reg 11, .reg 12])
      (normalPost (HdrInv inp impl mem₀ w 0))
      (fun _ => 5 + ((350 + impl.pathDS.params.K_bounds *
          (Nat.log 2 (Task1Input.dJCap impl inp.J + (stripLoops inp.J).m + 2) + 1) +
        impl.pathDS.params.K_bounds *
          (Nat.log 2 (WitnessCoreInput.dWInt impl.constructExpander + Task1Input.mwCap impl inp.J + 2) + 1)) +
        (265 * (stripLoops inp.J).m + 10 + ((stripLoops inp.J).m +
          ⌈impl.constructExpander.K_ce * (4 * ((stripLoops inp.J).m : ℝ) +
            2 * ((stripLoops inp.J).m : ℝ) / impl.decompose.φ_lb (stripLoops inp.J).m)⌉₊)) +
        (307 * (stripLoops inp.J).m + 119 * Task1Input.mwCap impl inp.J + 120) + 5) + 1) := by
    refine (Triple.call (buildWitnessCore_meetsContract hcore hce hbounds)
        (vs := fun st => [inp.jAddr, inp.h + 6, inp.decAddr, st.regs 11, st.regs 12])
        ?_ ?_ ?_ ?_).mono_cost ?_
    · intro st ⟨hp⟩
      have hb := task1_word_bounds hp.hv
      have h12_lt : st.regs 12 < 2 ^ w := by
        have hm1 : hp.wInp.maxHeapEnd impl.constructExpander impl.pathDS.params ≤
            hp.wInp.maxWordBound impl.constructExpander impl.pathDS.params := le_max_left _ _
        have hch : hp.wInp.h ≤ hp.wInp.maxHeapEnd impl.constructExpander impl.pathDS.params := by
          dsimp only [WitnessCoreInput.maxHeapEnd]; omega
        rw [hp.hr12]; exact lt_of_le_of_lt (le_trans hch hm1) hp.hw_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have h11_lt : st.regs 11 < 2 ^ w := by
        have := hp.hw_valid.2.2.2.1
        have hp_le_e : hp.wInp.prep.h ≤ hp.wInp.prep.hEnd := by
          unfold PrepInput.hEnd PrepInput.hBlocksStart; omega
        have hm1 : hp.wInp.maxHeapEnd impl.constructExpander impl.pathDS.params ≤
            hp.wInp.maxWordBound impl.constructExpander impl.pathDS.params := le_max_left _ _
        have hch : hp.wInp.h ≤ hp.wInp.maxHeapEnd impl.constructExpander impl.pathDS.params := by
          dsimp only [WitnessCoreInput.maxHeapEnd]; omega
        rw [hp.hr11]; exact lt_of_le_of_lt (le_trans (le_trans hp_le_e (le_trans this hch)) hm1)
          hp.hw_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      simp [evalArgs, ev_reg hp.hr1 hb.2.2.1, ev_reg hp.hr5 hb.2.2.2.2.2.2.1,
        ev_reg hp.hr10 hb.2.2.2.2.2.2.2.2.2.2.1, ev_reg rfl h11_lt, ev_reg rfl h12_lt]
    · intro st ⟨hp⟩ v hvm
      have hb := task1_word_bounds hp.hv
      have hm1 : hp.wInp.maxHeapEnd impl.constructExpander impl.pathDS.params ≤
          hp.wInp.maxWordBound impl.constructExpander impl.pathDS.params := le_max_left _ _
      have hch : hp.wInp.h ≤ hp.wInp.maxHeapEnd impl.constructExpander impl.pathDS.params := by
        dsimp only [WitnessCoreInput.maxHeapEnd]; omega
      have hww := hp.hw_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hp_le_e : hp.wInp.prep.h ≤ hp.wInp.prep.hEnd := by
        unfold PrepInput.hEnd PrepInput.hBlocksStart; omega
      have h11_lt : st.regs 11 < 2 ^ w := by rw [hp.hr11]; have := hp.hw_valid.2.2.2.1; omega
      have h12_lt : st.regs 12 < 2 ^ w := by rw [hp.hr12]; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvm
      rcases hvm with rfl | rfl | rfl | rfl | rfl <;> omega
    · intro st ⟨hp⟩
      exact ⟨hp.wInp, by rw [hp.hw_jAddr, hp.hw_stats, hp.hw_decAddr, hp.hr11, hp.hr12], hp.hw_valid⟩
    · intro st v mem' pos' ⟨hp⟩ hpost
      rcases hpost hp.wInp (by rw [hp.hw_jAddr, hp.hw_stats, hp.hw_decAddr, hp.hr11, hp.hr12])
        hp.hw_valid with ⟨WSubs, hws, hout⟩
      have hagree := hout.1
      have hcore_end : hp.wInp.prep.hEnd ≤ hp.wInp.h := hp.hw_valid.2.2.2.1
      have hp_lt_e : hp.wInp.prep.h + 9 ≤ hp.wInp.prep.hEnd := by
        unfold PrepInput.hEnd PrepInput.hBlocksStart; omega
      have hcore_h : hp.wInp.prep.h ≤ hp.wInp.h := by omega
      have hprep_ge : inp.h + 6 < hp.wInp.prep.h := by
        have := hp.hw_valid.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        rw [hp.hw_decAddr] at this
        unfold Task1Input.decAddr Task1Input.nlAddr Task1Input.j0Addr at this; omega
      have hv_ge20 : hp.wInp.h + 20 ≤ v := by
        have h_1 := hout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have h_2 := hout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have h_3 := hout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have h_4 := hout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have h_5 := hout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have h_6 := hout.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        omega
      have hv_max : v ≤ hp.wInp.maxHeapEnd impl.constructExpander impl.pathDS.params := hout.2.2.2.1
      have hv_w : v < 2 ^ w :=
        lt_of_le_of_lt (le_trans hv_max (le_max_left _ _)) hp.hw_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hbelow' : ∀ x < inp.h, mem' x = mem₀ x := fun x hx => by
        rw [hagree x (by omega), hp.h_below x hx]
      have ⟨hss, hcd⟩ := prepStatic_and_comps_of_agree_range hp.hw_valid.2.2.1 hp.h_static_state
        hp.h_comps_done (fun x _ hx => hagree x (lt_of_lt_of_le hx hcore_end))
      have hla : ∀ a xs, a + xs.length ≤ hp.wInp.prep.h →
          WordRAM.ListAt st.mem a xs → WordRAM.ListAt mem' a xs :=
        fun a xs hle h i hi' => by rw [hagree _ (lt_of_lt_of_le (by omega) hcore_h)]; exact h i hi'
      have hs0v := hp.hw_valid.2.2.1
      have hsv : hp.wInp.prep.StaticValid mem' w :=
        ⟨hs0v.1, hla _ _ hs0v.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hs0v.2.1,
          hs0v.2.2.1, hla _ _ hs0v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hs0v.2.2.2.1,
          hs0v.2.2.2.2.1, hla _ _ hs0v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hs0v.2.2.2.2.2.1,
          hla _ _ hs0v.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hs0v.2.2.2.2.2.2.1,
          hs0v.2.2.2.2.2.2.2⟩
      have hout' : ∀ (memPre : ℕ → ℕ),
          hp.wInp.OutputAt impl.constructExpander impl.pathDS.params
            (fun x => if x < hp.wInp.h then mem' x else memPre x) mem' v
            (hp.wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs) := by
        intro memPre
        refine ⟨fun x hx => by dsimp only; simp only [hx, ↓reduceIte],
          hout.2.1, hout.2.2.1, hout.2.2.2.1, hout.2.2.2.2⟩
      have hok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
          WitnessOK tools inp.H' inp.J inp.embJH
            (hp.wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs) := by
        intro N_max W_max tools
        have h := hp.wInp.mkWitnessData_ok tools hp.hw_valid hws
        rw [hp.hw_H', hp.hw_J] at h
        rcases h with ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
          f18, f19, f20, f21, f22⟩
        exact ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
          f18, f19, f20, f21, f22⟩
      exact ⟨⟨hp.wInp, WSubs, v, hp.hw_H', hp.hw_emb, hp.hw_J, hp.hw_jAddr, hp.hw_stats,
        hp.hw_j0Addr, hp.hw_nlAddr, hp.hw_decAddr, hp.hw_cℓ, hbelow', hout.2.1, hv_ge20, hv_max, le_trans hv_max hp.hw_maxEnd,
        hv_w, (task1_word_bounds hp.hv).1,
        by have h := hp.hw_valid.2.2.2.2.2.1; rw [hp.hw_J] at h; dsimp only
           rwa [hagree _ (by rw [hp.hw_stats]; omega)],
        by have h := hp.hw_valid.2.2.2.2.2.2.1; rw [hp.hw_J, hp.hw_emb] at h; dsimp only
           rwa [hagree _ (by rw [hp.hw_stats]; omega)],
        by have h := hp.hw_valid.2.2.2.2.2.2.2.1; rw [hp.hw_J, hp.hw_H', hp.hw_emb] at h; dsimp only
           rwa [hagree _ (by rw [hp.hw_stats]; omega)],
        hss, hcd, hsv, hws, hp.h_phi_lb, hp.h_phi_cap, hout', hok, hp.hw_valid.2.2.2.1,
        by dsimp only; rw [Function.update_of_ne (by decide)]; exact hp.hr3,
        by dsimp only; rw [Function.update_of_ne (by decide), hp.hr5, hp.hw_stats],
        by dsimp only; rw [Function.update_of_ne (by decide), hp.hr6, hp.hw_j0Addr],
        by dsimp only; rw [Function.update_of_ne (by decide), hp.hr8, hp.hw_nlAddr],
        by dsimp only; rw [Function.update_of_ne (by decide), hp.hr10, hp.hw_decAddr],
        by dsimp only; rw [Function.update_of_ne (by decide)]; exact hp.hr11,
        by dsimp only; rw [Function.update_of_ne (by decide)]; exact hp.hr12,
        by simp [Function.update],
        hprep_ge, hcore_h,
        by rw [hp.hw_jAddr, hp.hw_J]; exact hp.hv.2.2.2.2.2.2.2.2.1,
        fun h => by omega, fun h => by omega, fun h => by omega,
        fun h => by omega, fun h => by omega, fun h => by omega⟩⟩
    · intro st ⟨hp⟩
      have heq : [inp.jAddr, inp.h + 6, inp.decAddr, st.regs 11, st.regs 12] =
          [hp.wInp.prep.jAddr, hp.wInp.statsAddr, hp.wInp.prep.decAddr, hp.wInp.prep.h, hp.wInp.h] := by
        rw [hp.hw_jAddr, hp.hw_stats, hp.hw_decAddr, hp.hr11, hp.hr12]
      rw [heq, buildWitnessCoreContract_cost_eq hp.hw_valid]
      have hcl := hp.h_cost_le
      simp [argsSize, Expr.size]
      omega
  have hstore0 : Triple w p (HdrInv inp impl mem₀ w 0) (Stmt.store (.reg 3) (.reg 5))
      (normalPost (HdrInv inp impl mem₀ w 1)) (fun _ => 3) := by
    refine (Triple.store (addr := fun _ => inp.h) (val := fun st => st.regs 5) ?_ ?_ ?_).mono_cost
      fun _ _ => by simp [Expr.size]
    · intro st ⟨hi⟩
      have := hi.h_prep_ge; have := hi.h_h_ge
      exact ev_reg hi.hr3 (by have := hi.hv_ge20; have := hi.hv_w; omega)
    · intro st ⟨hi⟩
      have := hi.h_prep_ge; have := hi.h_h_ge
      exact ev_reg rfl (by rw [hi.hr5, hi.hw_stats]; have := hi.hv_ge20; have := hi.hv_w; omega)
    · intro st ⟨hi⟩
      have hsub : HdrInvData inp impl mem₀ w 1
          { mem := Function.update st.mem (inp.h + 0) (st.regs 5), regs := st.regs, pos := st.pos } :=
        hdrInv_step hi (off := 0) (by omega) hi.h_below
          ⟨fun _ => by rw [show inp.h + 0 = inp.h by omega, Function.update_self, hi.hr5],
           fun h => by omega, fun h => by omega, fun h => by omega, fun h => by omega,
           fun h => by omega⟩
      exact ⟨by simpa using hsub⟩
  have hret : Triple w p (HdrInv inp impl mem₀ w 6) (Stmt.ret (.reg 13))
      (retPost fun v st' => Task1OutAt impl inp.jAddr inp.h inp.H' inp.J inp.embJH mem₀ st'.mem v w ∧
        v ≤ inp.maxHeapEnd impl)
      (fun _ => 2) := by
    refine (Triple.ret (val := fun st => st.regs 13) ?_ ?_).mono_cost
      fun _ _ => by simp [Expr.size]
    · intro st ⟨hi⟩; exact ev_reg rfl (by rw [hi.hr13]; exact hi.hv_w)
    · intro st ⟨hi⟩
      refine ⟨⟨hi.wInp, hi.WSubs, hi.hw_H', fun e _ => congrFun hi.hw_emb e, hi.hw_J,
        hi.hw_jAddr, by rw [hi.hw_stats], by rw [hi.hw_j0Addr]; rfl,
        by rw [hi.hw_nlAddr, hi.hw_j0Addr]; rfl,
        by rw [hi.hw_decAddr, hi.hw_nlAddr, hi.h_static_valid.2.2.1, hi.hw_J]; rfl,
        hi.hw_cℓ, hi.h_below, by rw [hi.hr13]; exact hi.h_zf,
        by rw [hi.hr13]; exact hi.hv_ge20, by rw [hi.hr13]; exact hi.hv_max, hi.hm0 (by omega),
        hi.hm1 (by omega), hi.hm2 (by omega), hi.hm3 (by omega), hi.hm4 (by omega), hi.hm5 (by omega),
        hi.hs0, hi.hs1, hi.hs2, hi.h_static_state, hi.h_comps_done, hi.h_static_valid,
        hi.h_wsubs, hi.h_phi_lb, hi.h_phi_cap, fun memPre => by rw [hi.hr13]; exact hi.h_out memPre,
        fun tools => hi.h_ok tools, hi.h_hend⟩, by rw [hi.hr13]; exact hi.hv_cap⟩
  have h5r := store_hdr_offset_seq 5 6 5 12 ⟨by omega, by omega⟩ (fun st hi => by
    have := hi.h_h_ge
    have hb : st.regs 12 < 2 ^ w := by rw [hi.hr12]; have := hi.hv_ge20; have := hi.hv_w; omega
    refine ⟨hb, fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm0 (by omega),
      fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm1 (by omega),
      fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm2 (by omega),
      fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm3 (by omega),
      fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm4 (by omega),
      fun _ => by rw [Function.update_self, hi.hr12]⟩) hret
  have h4r := store_hdr_offset_seq 4 5 4 11 ⟨by omega, by omega⟩ (fun st hi => by
    have := hi.h_h_ge
    have hb : st.regs 11 < 2 ^ w := by rw [hi.hr11]; have := hi.hv_ge20; have := hi.hv_w; omega
    refine ⟨hb, fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm0 (by omega),
      fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm1 (by omega),
      fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm2 (by omega),
      fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm3 (by omega),
      fun _ => by rw [Function.update_self, hi.hr11], fun h => by omega⟩) h5r
  have h3r := store_hdr_offset_seq 3 4 3 10 ⟨by omega, by omega⟩ (fun st hi => by
    have := hi.h_static_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have := hi.h_h_ge
    have hb : st.regs 10 < 2 ^ w := by rw [hi.hr10]; have := hi.hv_ge20; have := hi.hv_w; omega
    refine ⟨hb, fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm0 (by omega),
      fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm1 (by omega),
      fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm2 (by omega),
      fun _ => by rw [Function.update_self, hi.hr10], fun h => by omega, fun h => by omega⟩) h4r
  have h2r := store_hdr_offset_seq 2 3 2 8 ⟨by omega, by omega⟩ (fun st hi => by
    have := hi.h_static_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have := hi.h_h_ge
    have hb : st.regs 8 < 2 ^ w := by rw [hi.hr8]; have := hi.hv_ge20; have := hi.hv_w; omega
    refine ⟨hb, fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm0 (by omega),
      fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm1 (by omega),
      fun _ => by rw [Function.update_self, hi.hr8], fun h => by omega, fun h => by omega,
      fun h => by omega⟩) h3r
  have h1r := store_hdr_offset_seq 1 2 1 6 ⟨by omega, by omega⟩ (fun st hi => by
    have := hi.h_static_valid.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have := hi.h_h_ge
    have hb : st.regs 6 < 2 ^ w := by rw [hi.hr6]; have := hi.hv_ge20; have := hi.hv_w; omega
    refine ⟨hb, fun _ => by rw [Function.update_of_ne (by omega)]; exact hi.hm0 (by omega),
      fun _ => by rw [Function.update_self, hi.hr6], fun h => by omega, fun h => by omega,
      fun h => by omega, fun h => by omega⟩) h2r
  have h01 := Triple.seq_normal_const hstore0 h1r
  have hcr := Triple.seq_normal_const hcall h01
  exact hcr.mono_cost fun _ _ => by omega

/-! ## 3. Full `task1Body_triple` and `task1_meetsContract` -/

private lemma runs_seq_assoc_rl {w : ℕ} {p : Program} {ω : ℕ → Bool} {a b t : Stmt}
    {st : State} {o : Outcome} {st' : State} {c : ℕ}
    (h : Runs w p ω ((a.seq b).seq t) st o st' c) :
    ∃ c' ≤ c, Runs w p ω (a.seq (b.seq t)) st o st' c' := by
  rcases runs_seq_iff.mp h with ⟨v, c₁, hr_ab, rfl, rfl⟩ | ⟨st₂, c₁, c_t, hr_ab, hr_t, rfl⟩
  · rcases runs_seq_iff.mp hr_ab with ⟨v', cₐ, hr_a, heq, rfl⟩ | ⟨st₁, cₐ, c_b, hr_a, hr_b, rfl⟩
    · cases heq
      exact ⟨cₐ + 1, by omega, runs_seq_iff.mpr (Or.inl ⟨v, cₐ, hr_a, rfl, rfl⟩)⟩
    · exact ⟨cₐ + (c_b + 1) + 1, by omega, runs_seq_iff.mpr (Or.inr ⟨st₁, cₐ, c_b + 1, hr_a,
        runs_seq_iff.mpr (Or.inl ⟨v, c_b, hr_b, rfl, rfl⟩), rfl⟩)⟩
  · rcases runs_seq_iff.mp hr_ab with ⟨v, cₐ, _, _, _⟩ | ⟨st₁, cₐ, c_b, hr_a, hr_b, rfl⟩
    · contradiction
    · exact ⟨cₐ + (c_b + c_t + 1) + 1, by omega, runs_seq_iff.mpr (Or.inr ⟨st₁, cₐ, c_b + c_t + 1,
        hr_a, runs_seq_iff.mpr (Or.inr ⟨st₂, c_b, c_t, hr_b, hr_t, rfl⟩), rfl⟩)⟩

private lemma runs_seq_congr_right {w : ℕ} {p : Program} {ω : ℕ → Bool} {a s₁ s₂ : Stmt}
    (hstep : ∀ st₁ o₁ st₁' c₁, Runs w p ω s₁ st₁ o₁ st₁' c₁ →
      ∃ c₁' ≤ c₁, Runs w p ω s₂ st₁ o₁ st₁' c₁')
    {st : State} {o : Outcome} {st' : State} {c : ℕ}
    (h : Runs w p ω (a.seq s₁) st o st' c) :
    ∃ c' ≤ c, Runs w p ω (a.seq s₂) st o st' c' := by
  rcases runs_seq_iff.mp h with ⟨v, c₁, hr_a, rfl, rfl⟩ | ⟨st₁, c₁, c₂, hr_a, hr_s, rfl⟩
  · exact ⟨c₁ + 1, le_rfl, runs_seq_iff.mpr (Or.inl ⟨v, c₁, hr_a, rfl, rfl⟩)⟩
  · obtain ⟨c₂', hc₂, hr_s'⟩ := hstep st₁ o st' c₂ hr_s
    exact ⟨c₁ + c₂' + 1, by omega, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂', hr_a, hr_s', rfl⟩)⟩

private lemma runs_task1Body_flatten {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {a1 a2 c1 b1 b2 b3 b4 b5 c2 d1 c3 rest : Stmt}
    {st : State} {o : Outcome} {st' : State} {c : ℕ}
    (h : Runs w p ω
      ((a1.seq (a2.seq c1)).seq
       ((b1.seq (b2.seq (b3.seq (b4.seq (b5.seq c2))))).seq
        ((d1.seq c3).seq rest))) st o st' c) :
    ∃ c' ≤ c, Runs w p ω
      (a1.seq (a2.seq (c1.seq (b1.seq (b2.seq (b3.seq (b4.seq (b5.seq (c2.seq (d1.seq (c3.seq rest)))))))))))
      st o st' c' := by
  have h1 : ∀ {st₁ o₁ st₁' c₁},
      Runs w p ω ((d1.seq c3).seq rest) st₁ o₁ st₁' c₁ →
      ∃ c' ≤ c₁, Runs w p ω (d1.seq (c3.seq rest)) st₁ o₁ st₁' c' :=
    fun hr => runs_seq_assoc_rl hr
  have h2 : ∀ {st₁ o₁ st₁' c₁},
      Runs w p ω ((b1.seq (b2.seq (b3.seq (b4.seq (b5.seq c2))))).seq ((d1.seq c3).seq rest))
        st₁ o₁ st₁' c₁ →
      ∃ c' ≤ c₁, Runs w p ω (b1.seq (b2.seq (b3.seq (b4.seq (b5.seq (c2.seq (d1.seq (c3.seq rest))))))))
        st₁ o₁ st₁' c' := by
    intro st₁ o₁ st₁' c₁ hr
    obtain ⟨c₂, hc₂, hr⟩ := runs_seq_assoc_rl hr
    obtain ⟨c₃, hc₃, hr⟩ := runs_seq_congr_right (fun _ _ _ _ => runs_seq_assoc_rl) hr
    obtain ⟨c₄, hc₄, hr⟩ := runs_seq_congr_right (fun _ _ _ _ =>
      runs_seq_congr_right fun _ _ _ _ => runs_seq_assoc_rl) hr
    obtain ⟨c₅, hc₅, hr⟩ := runs_seq_congr_right (fun _ _ _ _ =>
      runs_seq_congr_right fun _ _ _ _ =>
      runs_seq_congr_right fun _ _ _ _ => runs_seq_assoc_rl) hr
    obtain ⟨c₆, hc₆, hr⟩ := runs_seq_congr_right (fun _ _ _ _ =>
      runs_seq_congr_right fun _ _ _ _ =>
      runs_seq_congr_right fun _ _ _ _ =>
      runs_seq_congr_right fun _ _ _ _ => runs_seq_assoc_rl) hr
    obtain ⟨c₇, hc₇, hr⟩ := runs_seq_congr_right (fun _ _ _ _ =>
      runs_seq_congr_right fun _ _ _ _ =>
      runs_seq_congr_right fun _ _ _ _ =>
      runs_seq_congr_right fun _ _ _ _ =>
      runs_seq_congr_right fun _ _ _ _ => runs_seq_congr_right fun _ _ _ _ => h1) hr
    exact ⟨c₇, by omega, hr⟩
  obtain ⟨c₂, hc₂, hr⟩ := runs_seq_assoc_rl h
  obtain ⟨c₃, hc₃, hr⟩ := runs_seq_congr_right (fun _ _ _ _ => runs_seq_assoc_rl) hr
  obtain ⟨c₄, hc₄, hr⟩ := runs_seq_congr_right (fun _ _ _ _ =>
    runs_seq_congr_right fun _ _ _ _ => runs_seq_congr_right fun _ _ _ _ => h2) hr
  exact ⟨c₄, by omega, hr⟩

theorem task1Body_triple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task1Input} {mem₀ : ℕ → ℕ}
    {stripBase statsBase decBase prepBase coreBase ceBase boundsBase : ℕ}
    (hstrip : p.HasAt stripBase stripLoopsModule)
    (hstats : p.HasAt statsBase embJHStatsModule)
    (hdec : p.HasAt decBase (impl.decompose.procs decBase))
    (hprep : p.HasAt prepBase witnessPrepModule)
    (hcore : p.HasAt coreBase
      (buildWitnessCoreModule impl.constructExpander.phiNum impl.constructExpander.phiDen
        impl.constructExpander.c_deg_int ceBase boundsBase))
    (hce : p.HasAt ceBase (impl.constructExpander.procs ceBase))
    (hbounds : p.HasAt boundsBase (impl.pathDS.boundsProcs boundsBase)) :
    Triple w p
      (fun st => st.mem = mem₀ ∧ inp.Valid impl mem₀ w ∧
        st.regs 0 = inp.hAddr ∧ st.regs 1 = inp.jAddr ∧ st.regs 2 = inp.embJHAddr ∧ st.regs 3 = inp.h)
      (task1Body stripBase statsBase decBase prepBase coreBase)
      (retPost fun v st' => Task1OutAt impl inp.jAddr inp.h inp.H' inp.J inp.embJH mem₀ st'.mem v w ∧
        v ≤ inp.maxHeapEnd impl)
      (fun _ => task1StepCost impl inp.J (embVertSumMem mem₀ inp.jAddr inp.embJHAddr)) := by
  have h5 := step5_core_hdr_triple (w := w) (inp := inp) (mem₀ := mem₀) hcore hce hbounds
  have h45 := Triple.seq_normal_const (step4_prep_triple (inp := inp) (mem₀ := mem₀) hprep) h5
  have h345 := Triple.seq_normal_const (step3_dec_triple (inp := inp) (mem₀ := mem₀) hdec) h45
  have h2345 := Triple.seq_normal_const (step2_strip_triple (inp := inp) (mem₀ := mem₀) hstrip) h345
  have h12345 := Triple.seq_normal_const (step1_stats_triple (inp := inp) (mem₀ := mem₀) hstats) h2345
  intro st ω hpre
  obtain ⟨o, st', c, hr, hpost, hc⟩ := h12345 st ω hpre
  dsimp only at hc
  obtain ⟨c', hc', hr'⟩ := runs_task1Body_flatten hr
  refine ⟨o, st', c', hr', hpost, ?_⟩
  have hle : task1StepCost impl inp.J (embVertSumMem mem₀ inp.jAddr inp.embJHAddr) ≥ c' := by
    dsimp only [task1StepCost]
    omega
  exact hle

private lemma task1_inputs_agree {impl : SpannerToolImpl} {w : ℕ} {mem mem' : ℕ → ℕ} {v : ℕ}
    {inp₁ inp₂ : Task1Input}
    (h1 : inp₁.Valid impl mem w) (h2 : inp₂.Valid impl mem w)
    (hargs : [inp₁.hAddr, inp₁.jAddr, inp₁.embJHAddr, inp₁.h] =
      [inp₂.hAddr, inp₂.jAddr, inp₂.embJHAddr, inp₂.h]) :
    inp₁.hAddr = inp₂.hAddr ∧ inp₁.jAddr = inp₂.jAddr ∧ inp₁.embJHAddr = inp₂.embJHAddr ∧
    inp₁.h = inp₂.h ∧ inp₁.H' = inp₂.H' ∧ inp₁.J = inp₂.J ∧
    (∀ e < inp₁.J.m, inp₁.embJH e = inp₂.embJH e) ∧
    (Task1OutAt impl inp₁.jAddr inp₁.h inp₁.H' inp₁.J inp₁.embJH mem mem' v w →
      Task1OutAt impl inp₂.jAddr inp₂.h inp₂.H' inp₂.J inp₂.embJH mem mem' v w) := by
  have heq1 := List.cons.inj hargs
  have heq2 := List.cons.inj heq1.2
  have heq3 := List.cons.inj heq2.2
  have heq4 := List.cons.inj heq3.2
  rcases heq1 with ⟨hhA, _⟩
  rcases heq2 with ⟨hjA, _⟩
  rcases heq3 with ⟨heA, _⟩
  rcases heq4 with ⟨hh, _⟩
  have hH' : inp₁.H' = inp₂.H' := graphAt_inj h1.2.1 (hhA ▸ h2.2.1)
  have hJ : inp₁.J = inp₂.J := graphAt_inj h1.2.2.2.1 (hjA ▸ h2.2.2.2.1)
  have hemb : ∀ e < inp₁.J.m, inp₁.embJH e = inp₂.embJH e := by
    intro e he
    have he2 : e < inp₂.J.m := by rw [← hJ]; exact he
    have w1 := h1.2.2.2.2.2.1 e he
    have w2 := h2.2.2.2.2.2.1 e he2
    rw [← heA] at w2
    exact walkAt_inj w1 w2
  refine ⟨hhA, hjA, heA, hh, hH', hJ, hemb, ?_⟩
  intro hout
  rcases hout with ⟨wInp, WSubs, hwH, hwE, hwJ, hwj, hws, hj0, hnl, hdec, hcℓ,
    hbelow, hzf, hv20, hvmax, hm0, hm1, hm2, hm3, hm4, hm5, hs0, hs1, hs2,
    hss, hcd, hsv, hws_sub, hφ_lb, hpd_cap, hout_m, hok, hhend⟩
  have hlen_eq : length inp₁.J inp₁.embJH = length inp₂.J inp₂.embJH := by
    rw [← hJ]; exact length_congr_emb hemb
  have hvcong_eq : vcongNat inp₁.J inp₁.H' inp₁.embJH = vcongNat inp₂.J inp₂.H' inp₂.embJH := by
    rw [← hJ, ← hH']; exact vcongNat_congr_emb hemb
  refine ⟨wInp, WSubs, hwH.trans hH', fun e he => (hwE e (hJ ▸ he)).trans (hemb e (hJ ▸ he)),
    hwJ.trans hJ, hwj.trans hjA, hws.trans (by omega),
    hj0.trans (by rw [hh, hJ, hH']),
    hnl.trans (by rw [hJ]),
    hdec,
    hcℓ,
    hh ▸ hbelow, hzf, hv20, hvmax, hh ▸ hm0, hh ▸ hm1, hh ▸ hm2, hh ▸ hm3, hh ▸ hm4, hh ▸ hm5,
    by rw [← hJ]; exact hs0, by rw [← hlen_eq]; exact hs1, by rw [← hvcong_eq]; exact hs2,
    hss, hcd, hsv, hws_sub, hφ_lb, hpd_cap, hout_m, ?_, hhend⟩
  intro N_max W_max tools
  have hk := hok tools
  rw [hH', hJ] at hk
  rcases hk with ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
    f18, f19, f20, f21, f22⟩
  exact ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
    f18, f19, f20, f21, f22⟩

section Contract
open Classical

/-- `task1Contract.cost` equals `task1StepCost` on valid inputs. -/
lemma task1Contract_cost_eq {impl : SpannerToolImpl} {w : ℕ} {inp : Task1Input} {mem : ℕ → ℕ}
    (hv : inp.Valid impl mem w) :
    (task1Contract impl w).cost [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] mem =
      task1StepCost impl inp.J (embVertSumMem mem inp.jAddr inp.embJHAddr) := by
  have hex : ∃ inp' : Task1Input,
      [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] =
        [inp'.hAddr, inp'.jAddr, inp'.embJHAddr, inp'.h] ∧
      inp'.Valid impl mem w := ⟨inp, rfl, hv⟩
  simp only [task1Contract, hex, ↓reduceDIte]
  have hspec := Classical.choose_spec hex
  have hag := task1_inputs_agree (mem' := mem) (v := 0) hspec.2 hv hspec.1.symm
  rw [hag.2.1, hag.2.2.1, hag.2.2.2.2.2.1]

/-- Contract satisfaction theorem for `task1Module`. -/
theorem task1_meetsContract {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {base stripBase statsBase decBase prepBase coreBase ceBase boundsBase : ℕ}
    (hself : p.HasAt base (task1Module stripBase statsBase decBase prepBase coreBase))
    (hstrip : p.HasAt stripBase stripLoopsModule)
    (hstats : p.HasAt statsBase embJHStatsModule)
    (hdec : p.HasAt decBase (impl.decompose.procs decBase))
    (hprep : p.HasAt prepBase witnessPrepModule)
    (hcore : p.HasAt coreBase
      (buildWitnessCoreModule impl.constructExpander.phiNum impl.constructExpander.phiDen
        impl.constructExpander.c_deg_int ceBase boundsBase))
    (hce : p.HasAt ceBase (impl.constructExpander.procs ceBase))
    (hbounds : p.HasAt boundsBase (impl.pathDS.boundsProcs boundsBase)) :
    MeetsContract w p base (task1Contract impl w) := by
  intro args mem pos ω _ hpre
  rcases hpre with ⟨inp, rfl, hvalid⟩
  have hbody : p.procs[base]? = some (task1Body stripBase statsBase decBase prepBase coreBase) := by
    simpa [task1Module] using hself 0 Nat.zero_lt_one
  refine ⟨_, hbody, ?_⟩
  have htriple := task1Body_triple (w := w) (inp := inp) (mem₀ := mem)
    hstrip hstats hdec hprep hcore hce hbounds
  rcases htriple (startState [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] mem pos) ω
      ⟨rfl, hvalid, rfl, rfl, rfl, rfl⟩ with ⟨o, st', c, hruns, hpost, hcost⟩
  cases o with
  | normal => exact False.elim hpost
  | returned v =>
    refine ⟨Outcome.returned v, st', c, hruns, ?_, ?_⟩
    · intro inp' hargs' hvalid'
      obtain ⟨hout, hcap⟩ := hpost
      have hag := task1_inputs_agree (mem' := st'.mem) (v := v) hvalid hvalid' hargs'
      refine ⟨hag.2.2.2.2.2.2.2 hout, ?_⟩
      have hm : inp.maxHeapEnd impl = inp'.maxHeapEnd impl := by
        simp only [Task1Input.maxHeapEnd, Task1Input.coreHMax, Task1Input.prepHMax,
          Task1Input.decAddr, Task1Input.nlAddr, Task1Input.j0Addr, hag.2.2.2.1, hag.2.2.2.2.1,
          hag.2.2.2.2.2.1]
      rw [← hm]; exact hcap
    · rw [task1Contract_cost_eq hvalid]
      exact hcost

end Contract

end MinCostFlow.Spanner

