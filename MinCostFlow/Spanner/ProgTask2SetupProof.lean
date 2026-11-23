module

public import MinCostFlow.Spanner.ProgTask2SetupPreamble
public import MinCostFlow.Spanner.ProgTask2BuildInc
public import MinCostFlow.Spanner.ProgTask2InitJ0Proof
public import MinCostFlow.Spanner.ProgTask2InitMath

@[expose] public section

namespace MinCostFlow.Spanner
open WordRAM

private lemma t2Setup_init_mid_arrays {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) (db : DrainBounds ctx stc)
    {st_p st1 st2 stL : State} {e0 e8 e9 e10 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e29 e30 e31 : ℕ}
    (hmem_p : st_p.mem = t2SetupHdrMem mem₀ inp.v1 e0 e8 e9 e10 e12 e13 e14 e15 e16 e17 e18 e19 e20
      e21 e22 e23 e24 e29 e30 e31)
    (hfr1 : T2BuildIncFrame ctx st_p.mem st1.mem)
    (hfr2 : T2InitJ0Frame inp ctx.wd.W.m ctx.wd.comps.length stc.nodesEnd st1.mem st2.mem)
    (hsL : ∀ a, st2.mem a = stL.mem a)
    (hceb1 : ∀ ci < ctx.wd.comps.length, st1.mem (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ci) =
      compEdgeBase ctx.wd ci)
    (hvho1 : ∀ ci < ctx.wd.comps.length, st1.mem (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci) =
      vhatBase ctx.wd ci)
    (hL_inc : ∀ x < inp.H'.n,
      IncChainBound st1.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd
        (st1.mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x)) (stc.L_inc x) ∧
      (∀ q ∈ stc.L_inc x, ∃ (hp : q.1 < ctx.wd.comps.length), q.2 < (ctx.wd.comps[q.1]'hp).J_sub.m ∧
        x ∈ (inp.embJH ((ctx.wd.comps[q.1]'hp).jSubOrigEdges.getD q.2 0)).verts) ∧
      (∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (b : ℕ), b < (ctx.wd.comps[ci]'hci).J_sub.m →
        x ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts → (ci, b) ∈ stc.L_inc x)) :
    (∀ ci < ctx.wd.comps.length,
      stL.mem (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ci) = compEdgeBase ctx.wd ci) ∧
    (∀ ci < ctx.wd.comps.length,
      stL.mem (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci) = vhatBase ctx.wd ci) ∧
    (∀ ci (hci : ci < ctx.wd.comps.length) b, b < (ctx.wd.comps[ci]'hci).J_sub.m →
      stL.mem (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci + b) ≤ 0) ∧
    (∀ ci (hci : ci < ctx.wd.comps.length) y, y < (ctx.wd.comps[ci]'hci).J_sub.n →
      stL.mem (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + y) ≤ 0) ∧
    (∀ x < inp.H'.n, stL.mem (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x) ≤ 0) ∧
    (∀ x < inp.H'.n,
      IncChainBound stL.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd
        (stL.mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x)) (stc.L_inc x) ∧
      (∀ q ∈ stc.L_inc x, ∃ (hp : q.1 < ctx.wd.comps.length), q.2 < (ctx.wd.comps[q.1]'hp).J_sub.m ∧
        x ∈ (inp.embJH ((ctx.wd.comps[q.1]'hp).jSubOrigEdges.getD q.2 0)).verts) ∧
      (∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (b : ℕ), b < (ctx.wd.comps[ci]'hci).J_sub.m →
        x ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts → (ci, b) ∈ stc.L_inc x)) := by
  have _ := db.e_v1; have _ := db.e_emb; have _ := db.e_hdl; have _ := db.e_ceb; have _ := db.e_vho
  have _ := db.e_del; have _ := db.e_vh; have _ := db.e_vhd
  have _ := db.e_vc; have _ := db.e_ps; have _ := db.e_ew; have _ := db.e_q
  have _ := db.h_nlo
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ci hci
    exact (hsL _).symm.trans ((hfr2 _ (by omega) (by omega) (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (by omega)).trans (hceb1 ci hci))
  · intro ci hci
    exact (hsL _).symm.trans ((hfr2 _ (by omega) (by omega) (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (by omega)).trans (hvho1 ci hci))
  · intro ci hci b hb
    have hb_le := compEdgeBase_add_le hci
    have hb_sum : compEdgeBase ctx.wd (ci + 1) ≤ inp.J.m :=
      le_trans (compEdgeBase_le_sum (by omega))
        (le_trans (Nat.le_add_left _ _) (ctx.hWInpJ ▸ mkW_sum_comp_j_m_le_J ctx.hstat ctx.hw_okW ctx.hws))
    have ha1 := hfr2 (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci + b)
      (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)
    have ha2 := hfr1 (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length + compEdgeBase ctx.wd ci + b)
      (Or.inr (Or.inl ⟨by omega, by omega⟩))
    rw [← hsL, ha1, ha2, hmem_p, t2SetupHdrMem_outside (Or.inr (by omega)), ctx.hz0 _ (by omega)]
  · intro ci hci y hy
    have hv_le := vhatBase_add_le hci
    have hv_sum : vhatBase ctx.wd (ci + 1) ≤ 2 * inp.J.m :=
      le_trans (vhatBase_le_sum (by omega)) ctx.hvhatSum_le
    have ha1 := hfr2 (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + y)
      (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)
    have ha2 := hfr1 (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length + vhatBase ctx.wd ci + y)
      (Or.inr (Or.inl ⟨by omega, by omega⟩))
    rw [← hsL, ha1, ha2, hmem_p, t2SetupHdrMem_outside (Or.inr (by omega)), ctx.hz0 _ (by omega)]
  · intro x hx
    have ha1 := hfr2 (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x)
      (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (by omega)
    have ha2 := hfr1 (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + x)
      (Or.inr (Or.inr ⟨by omega, by omega⟩))
    rw [← hsL, ha1, ha2, hmem_p, t2SetupHdrMem_outside (Or.inr (by omega)), ctx.hz0 _ (by omega)]
  · intro x hx
    obtain ⟨hc, hsub, hmem_inc⟩ := hL_inc x hx
    have hhead : stL.mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        st1.mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x) := by
      rw [← hsL]
      exact hfr2 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)
    refine ⟨hhead ▸ hc.mono (fun a ha1 ha2 => ?_), hsub, hmem_inc⟩
    rw [← hsL]
    exact hfr2 a (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) ha2

private lemma t2Setup_build_loopState {w : ℕ} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    (db : DrainBounds ctx stc) {st_p st1 st2 s18 s17 stL : State}
    {hrp4 hrp10 hrp12 : ℕ}
    (hmem_p : st_p.mem = t2SetupHdrMem mem₀ inp.v1 inp.embWJAddr ctx.wd.W.m inp.H'.n ctx.wd.comps.length
      inp.embJHAddr ctx.wInp.prep.h ctx.wInp.h (inp.dsHandlesAddr ctx.wd.W.m)
      (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length)
      (ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec)
      (ctx.wd.W.m - ctx.wd.j0Edges.length) ctx.wInp.prep.phiDen_dec)
    (_hs18_mem : s18.mem = st1.mem)
    (hs17_mem : s17.mem = st2.mem)
    (hmL : stL.mem = s17.mem)
    (hregsL : ∀ r ≤ 20, r ≠ 19 → stL.regs r = s17.regs r)
    (hs17_r4 : s17.regs 4 = hrp4) (hs17_r10 : s17.regs 10 = hrp10)
    (hs17_r12 : s17.regs 12 = hrp12) (hs17_r18 : s17.regs 18 = stc.dsBaseAddr)
    (h4v : hrp4 = inp.v1) (h10v : hrp10 = ctx.wd.comps.length) (h12v : hrp12 = ctx.wd.W.m)
    (hr19 : stL.regs 19 = 1) (hr31 : stL.regs 31 = ctx.wInp.prep.aComps)
    (hr32 : stL.regs 32 = stL.mem (ctx.wInp.h + 12)) (hr33 : stL.regs 33 = ctx.wInp.prep.phiNum_dec)
    (hr34 : stL.regs 34 = ctx.wInp.prep.phiDen_dec) (hr35 : stL.regs 35 = ctx.wd.J0_strip.m)
    (hr36 : stL.regs 36 = inp.dsHandlesAddr ctx.wd.W.m)
    (hr37 : stL.regs 37 = inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr38 : stL.regs 38 = inp.embWJAddr)
    (hr39 : stL.regs 39 = inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (hr40 : stL.regs 40 = ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec)
    (hfr1 : T2BuildIncFrame ctx st_p.mem st1.mem)
    (hfr2 : T2InitJ0Frame inp ctx.wd.W.m ctx.wd.comps.length stc.nodesEnd st1.mem st2.mem)
    (hAgr1 : ∀ x < inp.v1, s18.mem x = mem₀ x)
    (hAgr2 : ∀ x < inp.v1, s17.mem x = mem₀ x)
    (hslot2 : ∀ k < 32, k ≠ 25 → k ≠ 26 → s17.mem (inp.v1 + k) = st_p.mem (inp.v1 + k))
    (hzero2 : ∀ k, (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 11 ∨ k = 27 ∨ k = 28) → s17.mem (inp.v1 + k) = 0)
    (hceb1 : ∀ ci < ctx.wd.comps.length, st1.mem (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ci) =
      compEdgeBase ctx.wd ci)
    (hvho1 : ∀ ci < ctx.wd.comps.length, st1.mem (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci) =
      vhatBase ctx.wd ci)
    (hL_inc : ∀ x < inp.H'.n,
      IncChainBound st1.mem (inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length) stc.nodesEnd
        (st1.mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x)) (stc.L_inc x) ∧
      (∀ q ∈ stc.L_inc x, ∃ (hp : q.1 < ctx.wd.comps.length), q.2 < (ctx.wd.comps[q.1]'hp).J_sub.m ∧
        x ∈ (inp.embJH ((ctx.wd.comps[q.1]'hp).jSubOrigEdges.getD q.2 0)).verts) ∧
      (∀ (ci : ℕ) (hci : ci < ctx.wd.comps.length) (b : ℕ), b < (ctx.wd.comps[ci]'hci).J_sub.m →
        x ∈ (inp.embJH ((ctx.wd.comps[ci]'hci).jSubOrigEdges.getD b 0)).verts → (ci, b) ∈ stc.L_inc x))
    (hzf2 : ZeroFrom st2.mem (stc.nodesEnd + 5 * ctx.wd.j0Edges.length))
    (hEmbUp : InitJ0EmbUpTo st2.mem inp.embWJAddr stc.nodesEnd ctx.wd.j0Edges.length ctx.wd.W.m inp.J ctx.wd.j0Edges)
    (hVc2 : ∀ x < inp.H'.n, st2.mem (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) =
      j0VcongUpTo ctx.wd (fun i => s18.mem (s18.mem (ctx.wInp.h + 14) + i)) inp.embJH ctx.wd.j0Edges.length x)
    (hEwSt2 : ∀ x < inp.H'.n, st2.mem (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) ≤ ctx.wd.j0Edges.length)
    (h25_2 : st2.mem (inp.v1 + 25) = stc.nodesEnd + 5 * ctx.wd.j0Edges.length)
    (h26_2 : st2.mem (inp.v1 + 26) = ctx.wd.j0Edges.length)
    (hj0_mW : ctx.wd.j0Edges.length ≤ ctx.wd.W.m)
    (_hv1_w : inp.v1 + 32 < 2 ^ w) :
    T2LoopState ctx stc 0 (initEmb0 ctx.wInp) (initEmb0 ctx.wInp) stc.dsBaseAddr
      (stc.nodesEnd + 5 * ctx.wd.j0Edges.length) 0 0 0 stL := by
  have hslots := t2SetupHdrMem_slots (mem₀ := mem₀) (v1 := inp.v1)
    (e0 := inp.embWJAddr) (e8 := ctx.wd.W.m) (e9 := inp.H'.n) (e10 := ctx.wd.comps.length)
    (e12 := inp.embJHAddr) (e13 := ctx.wInp.prep.h) (e14 := ctx.wInp.h)
    (e15 := inp.dsHandlesAddr ctx.wd.W.m)
    (e16 := inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length)
    (e17 := inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length)
    (e18 := inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length)
    (e19 := inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (e20 := inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length)
    (e21 := inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
    (e22 := inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (e23 := inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (e24 := inp.queueAddr ctx.wd.W.m ctx.wd.comps.length)
    (e29 := ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec)
    (e30 := ctx.wd.W.m - ctx.wd.j0Edges.length) (e31 := ctx.wInp.prep.phiDen_dec)
  have hVc2_mem0 : ∀ x < inp.H'.n,
      stL.mem (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        j0VcongUpTo ctx.wd (fun i => mem₀ (mem₀ (ctx.wInp.h + 14) + i))
          inp.embJH ctx.wd.j0Edges.length x := fun x hx => by
    rw [hmL, hs17_mem, hVc2 x hx]
    have hm_h14 : s18.mem (ctx.wInp.h + 14) = mem₀ (ctx.wInp.h + 14) :=
      hAgr1 _ (by have := ctx.hv20; omega)
    have hle_v1 := ctx.staticOutAt_init.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    refine Finset.sum_congr rfl fun eW heW => ?_
    have heW_lt : eW < ctx.wd.W.m := lt_of_lt_of_le (Finset.mem_range.mp heW) hj0_mW
    split_ifs
    · rw [hm_h14]; exact hAgr1 _ (by omega)
    · rfl
  have hpure := t2InitJ0_to_pure_inv ctx ctx.staticOutAt_init hVc2_mem0 (hmL ▸ hs17_mem ▸ hEmbUp)
  rcases hpure with ⟨hPart0, hj0_pure, hELen0, hVc0, hVol0, hCard0, hEmbInv0⟩
  have hcard_eq : (unembeddedSetPure ctx.wd (initEmb0 ctx.wInp)).card =
      ctx.wd.W.m - ctx.wd.j0Edges.length := hCard0
  have hsL : ∀ a, st2.mem a = stL.mem a := fun a => (hs17_mem ▸ hmL) ▸ rfl
  have h_ar_hi : stc.nodesEnd + 5 * ctx.wd.j0Edges.length ≤ stc.dsBaseAddr := by
    have hmul : 5 * ctx.wd.j0Edges.length ≤
        ctx.wd.W.m * (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) :=
      Nat.mul_le_mul (by omega) hj0_mW |>.trans_eq (Nat.mul_comm _ _)
    dsimp only [T2StaticData.dsBaseAddr]; exact Nat.add_le_add_left hmul stc.nodesEnd
  rcases t2Setup_init_mid_arrays ctx stc db hmem_p hfr1 hfr2 hsL hceb1 hvho1 hL_inc with
    ⟨hCebL, hVhoL, hDelR0, hVhatS0, hProcS0, hIncL⟩
  have hr_4 : stL.regs 4 = inp.v1 := (hregsL 4 (by omega) (by omega)).trans (hs17_r4.trans h4v)
  have hr_10 : stL.regs 10 = ctx.wd.comps.length := (hregsL 10 (by omega) (by omega)).trans (hs17_r10.trans h10v)
  have hr_12 : stL.regs 12 = ctx.wd.W.m := (hregsL 12 (by omega) (by omega)).trans (hs17_r12.trans h12v)
  have hr_18 : stL.regs 18 = stc.dsBaseAddr := (hregsL 18 (by omega) (by omega)).trans hs17_r18
  have h_slot : ∀ k < 32, k ≠ 25 → k ≠ 26 → stL.mem (inp.v1 + k) = st_p.mem (inp.v1 + k) := fun k hk h25 h26 =>
    (hsL (inp.v1 + k)).symm.trans (hs17_mem ▸ hslot2 k hk h25 h26)
  have h_z : ∀ k, (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 11 ∨ k = 27 ∨ k = 28) → stL.mem (inp.v1 + k) = 0 := fun k hk =>
    (hsL (inp.v1 + k)).symm.trans (hs17_mem ▸ hzero2 k hk)
  exact
    { hr4 := hr_4, hr10 := hr_10, hr12 := hr_12, hr18 := hr_18, hr19 := by simp [hr19]
      hr31 := hr31, hr32 := hr32, hr33 := hr33, hr34 := hr34, hr35 := hr35
      hr36 := hr36, hr37 := hr37, hr38 := hr38, hr39 := hr39, hr40 := hr40
      agr_pre := fun a ha => (hsL a).symm.trans (hs17_mem ▸ hAgr2 a ha)
      h_v1_slots := by
        simp only [Nat.zero_mul, hcard_eq, Nat.sub_self, Nat.add_zero]
        refine ⟨(h_slot 0 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.1),
          h_z 1 (by simp), h_z 2 (by simp), h_z 3 (by simp), h_z 4 (by simp),
          h_z 5 (by simp), h_z 6 (by simp), h_z 7 (by simp),
          (h_slot 8 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.1),
          (h_slot 9 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.1),
          (h_slot 10 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.1),
          (h_slot 12 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.1),
          (h_slot 13 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.1),
          (h_slot 14 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.1),
          (h_slot 15 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.1),
          (h_slot 16 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.1),
          (h_slot 17 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.2.1),
          (h_slot 18 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.2.2.1),
          (h_slot 19 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.2.2.2.1),
          (h_slot 20 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.2.2.2.2.1),
          (h_slot 21 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.1),
          (h_slot 22 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1),
          (h_slot 23 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1),
          (h_slot 24 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1),
          (hsL _).symm.trans h25_2, (hsL _).symm.trans h26_2,
          h_z 27 (by simp), h_z 28 (by simp),
          (h_slot 29 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1),
          (h_slot 30 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1),
          (h_slot 31 (by omega) (by omega) (by omega)).trans (hmem_p ▸ hslots.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)⟩
      hCeb := hCebL, hVho := hVhoL
      hDelR_le := hDelR0, hVhatS_le := hVhatS0, hProcS_le := hProcS0, hInc := hIncL
      hVc := fun x hx => (hVc0 x hx).1
      hEwSt := fun x hx => by
        have hle := hEwSt2 x hx
        rw [hmL, hs17_mem]
        simpa [hcard_eq] using hle
      hEmb := hEmbInv0
      hAr_lo := Nat.le_add_right _ _
      hAr_le := by
        simp only [hcard_eq, Nat.sub_self, Nat.add_zero]
        have hmul5 : 5 * ctx.wd.j0Edges.length ≤
            ctx.wd.j0Edges.length * (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) := by
          rw [Nat.mul_comm 5]
          exact Nat.mul_le_mul_left _ (by omega)
        exact Nat.add_le_add_left hmul5 stc.nodesEnd
      hGet_le := by rw [hcard_eq]
      hPart := hPart0
      hj0 := hj0_pure
      hELen := hELen0
      hVc_cur := fun x hx => by simpa using (hVc0 x hx).2
      hVol_cur := by simpa using hVol0
      hPrev_bd := fun _ => ⟨rfl, rfl, rfl, rfl⟩
      hDel_le := by simp
      hVcU_le := by simp [hcard_eq]
      hInn_le := by simp [hcard_eq]
      hCur_lo := le_refl _
      hCur_le := Nat.le_add_right _ _
      hzf := fun a ha => (hsL a).symm.trans (hzf2 a (le_trans h_ar_hi ha)) }

private def t2SetupMidStmt (selfBase : ℕ) (cont : Stmt) : Stmt :=
  Stmt.call 16 (selfBase + 1) [.reg 4, .reg 17] ;;
  Stmt.assign 18 (t2Add (.reg 16) (t2Mul (.reg 12) (t2Add (t2Mul (.const 2) (.reg 13)) (.const 5)))) ;;
  Stmt.call 17 (selfBase + 2) [.reg 4, .reg 1, .reg 16] ;;
  t2TailSetupStmt cont

private lemma t2InitJ0Frame_lt_v1 {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w nodesEnd : ℕ} {ctx : T2Ctx impl inp mem₀ w} {st1m st2m : ℕ → ℕ}
    (hfr2 : T2InitJ0Frame inp ctx.wd.W.m ctx.wd.comps.length nodesEnd st1m st2m)
    (hv1_emb : inp.v1 + 32 ≤ inp.embWJAddr)
    (hv1_vc : inp.v1 + 32 ≤ inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
    (hv1_ew : inp.v1 + 32 ≤ inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (hv1_n1 : inp.v1 + 32 ≤ nodesEnd)
    {x : ℕ} (hx : x < inp.v1) : st2m x = st1m x :=
  hfr2 x (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)

private lemma t2InitJ0Frame_slot {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w nodesEnd : ℕ} {ctx : T2Ctx impl inp mem₀ w} {st1m st2m : ℕ → ℕ}
    (hfr2 : T2InitJ0Frame inp ctx.wd.W.m ctx.wd.comps.length nodesEnd st1m st2m)
    (hv1_emb : inp.v1 + 32 ≤ inp.embWJAddr)
    (hv1_vc : inp.v1 + 32 ≤ inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
    (hv1_ew : inp.v1 + 32 ≤ inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (hv1_n1 : inp.v1 + 32 ≤ nodesEnd)
    {k : ℕ} (hk : k < 32) (h25 : k ≠ 25) (h26 : k ≠ 26) :
    st2m (inp.v1 + k) = st1m (inp.v1 + k) :=
  hfr2 (inp.v1 + k) (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)

private lemma t2Setup_mid_cost_arith {c1 c2 c_t c_f Jm j0 embSum : ℕ}
    (hc1 : c1 ≤ 55 * embSum + 105 * Jm + 70)
    (hc2 : c2 ≤ 110 * j0 + 45 * embSum + 80)
    (hct : c_t ≤ c_f + 65)
    (hj0 : j0 ≤ Jm) :
    (2 + c1 + 1) + (10 + ((3 + c2 + 1) + c_t + 1) + 1) + 1 ≤
      c_f + 215 * Jm + 100 * embSum + 240 := by
  omega

private lemma task2Setup_mid_runs {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} {selfBase : ℕ} (ctx : T2Ctx impl inp mem₀ w)
    (h1 : p.procs[selfBase + 1]? = some t2BuildIncBody)
    (h2 : p.procs[selfBase + 2]? = some t2InitJ0Body)
    (ω : ℕ → Bool) (st_p : State)
    (hmem_p : st_p.mem = t2SetupHdrMem mem₀ inp.v1 inp.embWJAddr ctx.wd.W.m inp.H'.n ctx.wd.comps.length
      inp.embJHAddr ctx.wInp.prep.h ctx.wInp.h (inp.dsHandlesAddr ctx.wd.W.m)
      (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
      (inp.queueAddr ctx.wd.W.m ctx.wd.comps.length)
      (ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec)
      (ctx.wd.W.m - ctx.wd.j0Edges.length) ctx.wInp.prep.phiDen_dec)
    (hrp1 : st_p.regs 1 = inp.jAddr)
    (hrp4 : st_p.regs 4 = inp.v1)
    (hrp5 : st_p.regs 5 = ctx.wInp.prep.h)
    (hrp6 : st_p.regs 6 = ctx.wInp.h)
    (hrp10 : st_p.regs 10 = ctx.wd.comps.length)
    (hrp12 : st_p.regs 12 = ctx.wd.W.m)
    (hrp13 : st_p.regs 13 = ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params)
    (hrp15 : st_p.regs 15 = ctx.wInp.prep.phiDen_dec)
    (hrp17 : st_p.regs 17 = inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length)
    (cont : Stmt) (Q : Outcome → State → ℕ → Prop)
    (hcont : ∀ (stc : T2StaticData ctx) (stL : State),
      T2LoopState ctx stc 0 (initEmb0 ctx.wInp) (initEmb0 ctx.wInp) stc.dsBaseAddr
        (stc.nodesEnd + 5 * ctx.wd.j0Edges.length) 0 0 0 stL →
      ∃ o stF c_cont, Runs w p ω cont stL o stF c_cont ∧ Q o stF c_cont) :
    ∃ o stF c_mid,
      Runs w p ω (t2SetupMidStmt selfBase cont) st_p o stF c_mid ∧
      ∃ c_cont, Q o stF c_cont ∧ c_mid ≤ c_cont + 215 * inp.J.m + 100 * inp.embVertSum + 240 := by
  have hb := t2SetupHdr_word_bounds ctx
  rcases hb with ⟨_, _, _ht1_v1, _, _, _, _, hv1_w, _, hj0_mW, _⟩
  have hslots := t2SetupHdrMem_slots (mem₀ := mem₀) (v1 := inp.v1)
    (e0 := inp.embWJAddr) (e8 := ctx.wd.W.m) (e9 := inp.H'.n) (e10 := ctx.wd.comps.length)
    (e12 := inp.embJHAddr) (e13 := ctx.wInp.prep.h) (e14 := ctx.wInp.h)
    (e15 := inp.dsHandlesAddr ctx.wd.W.m)
    (e16 := inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length)
    (e17 := inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length)
    (e18 := inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length)
    (e19 := inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (e20 := inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length)
    (e21 := inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
    (e22 := inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (e23 := inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length)
    (e24 := inp.queueAddr ctx.wd.W.m ctx.wd.comps.length)
    (e29 := ctx.wInp.tau1Int impl.constructExpander impl.pathDS.params * ctx.wInp.prep.phiDen_dec)
    (e30 := ctx.wd.W.m - ctx.wd.j0Edges.length) (e31 := ctx.wInp.prep.phiDen_dec)
  dsimp only at hslots
  rw [← hmem_p] at hslots
  rcases hslots with ⟨hs0, _hs8, _hs9, _hs10, hs12, hs13, hs14, hs15, hs16, hs17, _hs18, hs19,
    hs20, hs21, _hs22, hs23, _hs24, hs29, _hs30, _hs31⟩
  have hj0_le_J : ctx.wd.j0Edges.length ≤ inp.J.m := by
    have h1 := ctx.hWInpJ ▸ mkW_sum_comp_j_m_le_J ctx.hstat ctx.hw_okW ctx.hws
    change ctx.wd.j0Edges.length + (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ inp.J.m at h1
    exact le_trans (Nat.le_add_right _ _) h1
  have hAgr_p : ∀ x < inp.v1, st_p.mem x = mem₀ x := fun x hx =>
    hmem_p ▸ t2SetupHdrMem_outside (Or.inl hx)
  have hzf_p : ZeroFrom st_p.mem (inp.v1 + 32) := fun a ha => by
    rw [hmem_p, t2SetupHdrMem_outside (Or.inr ha)]
    exact ctx.hz0 a (le_trans (Nat.le_add_right _ 32) ha)
  have hBndInc := t2BuildInc_triple (p := p) ctx hAgr_p hs12 hs13 hs16 hs17 hs20 hzf_p
  obtain ⟨o1, st1, c1, hr1_run, ⟨nodesEnd, rfl, hne_lo, hne_hi, hzf1, hfr1, hceb1, hvho1, hInc1⟩, hc1⟩ :=
    hBndInc (startState [inp.v1, inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length] st_p.mem st_p.pos) ω ⟨rfl, rfl, rfl⟩
  rcases hInc1 with ⟨L_inc, hL_inc, hL_sum⟩
  let stc : T2StaticData ctx :=
    { nodesEnd := nodesEnd
      L_inc := L_inc
      hNodes_lo := hne_lo
      hNodes_hi := hne_hi
      hL_sum := by
        have h1 : (∑ x ∈ Finset.range inp.H'.n, (L_inc x).length) * 3 ≤ inp.embVertSum * 3 := by
          rw [Nat.mul_comm inp.embVertSum 3]
          exact le_trans hL_sum (Nat.sub_le_of_le_add (by rw [Nat.add_comm]; exact hne_hi))
        exact Nat.le_of_mul_le_mul_right h1 (by decide) }
  have db := drain_bounds ctx stc
  have hv1_emb : inp.v1 + 32 ≤ inp.embWJAddr := db.e_v1.le
  have hv1_hdl : inp.v1 + 32 ≤ inp.dsHandlesAddr ctx.wd.W.m :=
    le_trans hv1_emb (le_trans (Nat.le_add_right _ _) db.e_emb.le)
  have hv1_ceb : inp.v1 + 32 ≤ inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length :=
    le_trans hv1_hdl (le_trans (Nat.le_add_right _ _) db.e_hdl.le)
  have hv1_vho : inp.v1 + 32 ≤ inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length :=
    le_trans hv1_ceb (le_trans (Nat.le_add_right _ _) db.e_ceb.le)
  have hv1_del : inp.v1 + 32 ≤ inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length :=
    le_trans hv1_vho (le_trans (Nat.le_add_right _ _) db.e_vho.le)
  have hv1_vh : inp.v1 + 32 ≤ inp.vhatStampAddr ctx.wd.W.m ctx.wd.comps.length :=
    le_trans hv1_del (le_trans (Nat.le_add_right _ _) db.e_del.le)
  have hv1_vhd : inp.v1 + 32 ≤ inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length :=
    le_trans hv1_vh (le_trans (Nat.le_add_right _ _) db.e_vh.le)
  have hv1_vc : inp.v1 + 32 ≤ inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length :=
    le_trans hv1_vhd (le_trans (Nat.le_add_right _ _) db.e_vhd.le)
  have hv1_ps : inp.v1 + 32 ≤ inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length :=
    le_trans hv1_vc (le_trans (Nat.le_add_right _ _) db.e_vc.le)
  have hv1_ew : inp.v1 + 32 ≤ inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length :=
    le_trans hv1_ps (le_trans (Nat.le_add_right _ _) db.e_ps.le)
  have hemb_nds : inp.embWJAddr + ctx.wd.W.m ≤ stc.nodesEnd := by
    have h1 := le_trans db.e_emb.le (le_trans (Nat.le_add_right _ _) db.e_hdl.le)
    have h2 := le_trans h1 (le_trans (Nat.le_add_right _ _) db.e_ceb.le)
    have h3 := le_trans h2 (le_trans (Nat.le_add_right _ _) db.e_vho.le)
    have h4 := le_trans h3 (le_trans (Nat.le_add_right _ _) db.e_del.le)
    have h5 := le_trans h4 (le_trans (Nat.le_add_right _ _) db.e_vh.le)
    have h6 := le_trans h5 (le_trans (Nat.le_add_right _ _) db.e_vhd.le)
    have h7 := le_trans h6 (le_trans (Nat.le_add_right _ _) db.e_vc.le)
    have h8 := le_trans h7 (le_trans (Nat.le_add_right _ _) db.e_ps.le)
    have h9 := le_trans h8 (le_trans (Nat.le_add_right _ _) db.e_ew.le)
    have h10 := le_trans h9 (le_trans (Nat.le_add_right _ _) db.e_q.le)
    exact le_trans h10 db.h_nlo
  have hds_lt_w : stc.dsBaseAddr < 2 ^ w :=
    lt_of_le_of_lt (le_trans db.h_dsc (le_trans db.h_stc db.h_mhe)) db.h_mwb
  have hγ_w : 2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5 < 2 ^ w := by
    rcases Nat.eq_zero_or_pos ctx.wd.W.m with hm0 | hmpos
    · have hcap := ctx.hWInpJ ▸ task2_scalars_le_caps ctx.hstat ctx.hφ_lb
      have hγ1 := hcap.1
      have hmw1 : 1 ≤ Task1Input.mwCap impl inp.J := by
        unfold Task1Input.mwCap; omega
      have h2γ : 2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5 ≤
          2 * Task2Input.gammaExpCap impl inp.J + 5 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 hγ1) 5
      have hmul1 : 2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5 ≤
          Task1Input.mwCap impl inp.J * (2 * Task2Input.gammaExpCap impl inp.J + 5) :=
        le_trans h2γ (Nat.le_mul_of_pos_left _ hmw1)
      have hsc' : Task1Input.mwCap impl inp.J * (2 * Task2Input.gammaExpCap impl inp.J + 5) ≤
          Task2Input.staticEndCap impl inp := by
        unfold Task2Input.staticEndCap; exact Nat.le_add_left _ _
      exact lt_of_le_of_lt (le_trans hmul1 (le_trans hsc' (le_trans db.h_stc db.h_mhe))) db.h_mwb
    · have hmul_le : 2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5 ≤
          ctx.wd.W.m * (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) :=
        Nat.le_mul_of_pos_left _ hmpos
      have hds_sum : ctx.wd.W.m * (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) ≤
          stc.dsBaseAddr := Nat.le_add_left _ _
      exact lt_of_le_of_lt (le_trans hmul_le hds_sum) hds_lt_w
  have hmul_w : ctx.wd.W.m * (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_add_left _ _) hds_lt_w
  let s16 : State := { mem := st1.mem, regs := Function.update st_p.regs 16 nodesEnd, pos := st1.pos }
  have hr16_16 : s16.regs 16 = nodesEnd := by dsimp only [s16]; exact Function.update_self _ _ _
  have hr16_12 : s16.regs 12 = ctx.wd.W.m := by simp (disch := decide) only [s16, Function.update_of_ne, hrp12]
  have hr16_13 : s16.regs 13 = ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params := by
    simp (disch := decide) only [s16, Function.update_of_ne, hrp13]
  have hr_c16 : Runs w p ω (Stmt.call 16 (selfBase + 1) [.reg 4, .reg 17]) st_p .normal s16
      (argsSize [.reg 4, .reg 17] + c1 + 1) := by
    refine runs_call_iff.mpr ⟨[inp.v1, inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length],
      t2BuildIncBody, .returned nodesEnd, st1, c1, ?_, h1, hr1_run, rfl, rfl, rfl⟩
    simp [evalArgs, Expr.eval_reg_of_eq hrp4, Expr.eval_reg_of_eq hrp17]
  let s18 : State := { mem := st1.mem, regs := Function.update s16.regs 18 stc.dsBaseAddr, pos := st1.pos }
  have hr_a18 : Runs w p ω
      (Stmt.assign 18 (t2Add (.reg 16) (t2Mul (.reg 12) (t2Add (t2Mul (.const 2) (.reg 13)) (.const 5)))))
      s16 .normal s18 10 := by
    have he1 := Expr.eval_mul (Expr.eval_const (lt_of_le_of_lt (Nat.le_trans (by decide) (Nat.le_add_left _ _)) hγ_w))
      (Expr.eval_reg_of_eq hr16_13) (lt_of_le_of_lt (Nat.le_add_right _ 5) hγ_w)
    have he2 := Expr.eval_add he1 (Expr.eval_const (lt_of_le_of_lt
      (Nat.le_add_left 5 (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params)) hγ_w)) hγ_w
    have he3 := Expr.eval_mul (Expr.eval_reg_of_eq hr16_12) he2 hmul_w
    have he4 := Expr.eval_add (Expr.eval_reg_of_eq hr16_16) he3 hds_lt_w
    exact runs_assign_iff.mpr ⟨stc.dsBaseAddr, he4, rfl, rfl, by simp [Expr.size]⟩
  have hAgr1 : ∀ x < inp.v1, s18.mem x = mem₀ x := fun x hx =>
    (hfr1 x (Or.inl (lt_of_lt_of_le hx (le_trans (Nat.le_add_right inp.v1 32) hv1_ceb)))).trans (hAgr_p x hx)
  have hslot1 : ∀ k < 32, s18.mem (inp.v1 + k) = st_p.mem (inp.v1 + k) := fun k hk =>
    hfr1 (inp.v1 + k) (Or.inl (lt_of_lt_of_le (Nat.add_lt_add_left hk inp.v1) hv1_ceb))
  have hInitJ0 := t2InitJ0_triple (p := p) ctx hAgr1 (arena0 := nodesEnd)
    ((hslot1 0 (by decide)).trans hs0)
    ((hslot1 12 (by decide)).trans hs12)
    ((hslot1 13 (by decide)).trans hs13)
    ((hslot1 14 (by decide)).trans hs14)
    ((hslot1 21 (by decide)).trans hs21)
    ((hslot1 23 (by decide)).trans hs23)
    ctx.hJ_le hne_lo hne_hi hzf1
    (fun eW heW => by
      have heq := hfr1 (inp.embWJAddr + eW)
        (Or.inl (lt_of_lt_of_le (Nat.add_lt_add_left heW _)
          (le_trans db.e_emb.le (le_trans (Nat.le_add_right _ _) db.e_hdl.le))))
      change st1.mem (inp.embWJAddr + eW) = _ at heq
      rw [show s18.mem (inp.embWJAddr + eW) = st1.mem (inp.embWJAddr + eW) from rfl, heq, hmem_p,
        t2SetupHdrMem_outside (Or.inr (le_trans hv1_emb (Nat.le_add_right _ _)))]
      exact ctx.hz0 _ (le_trans (Nat.le_add_right _ 32) (le_trans hv1_emb (Nat.le_add_right _ _))))
    (fun x hx => by
      have h_vc_nds : inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x <
          inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length := by
        have h1 := Nat.add_lt_add_left hx (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length)
        exact lt_of_lt_of_le h1 (le_trans db.e_vc.le (le_trans (Nat.le_add_right _ _)
          (le_trans db.e_ps.le (le_trans (Nat.le_add_right _ _)
            (le_trans db.e_ew.le (le_trans (Nat.le_add_right _ _) db.e_q.le))))))
      have heq := hfr1 (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x)
        (Or.inr (Or.inr ⟨le_trans db.e_vhd.le (Nat.le_add_right _ _), h_vc_nds⟩))
      change st1.mem (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) = _ at heq
      change st1.mem (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) = _
      rw [heq, hmem_p, t2SetupHdrMem_outside (Or.inr (le_trans hv1_vc (Nat.le_add_right _ _)))]
      exact ctx.hz0 _ (le_trans (Nat.le_add_right _ 32) (le_trans hv1_vc (Nat.le_add_right _ _))))
    (fun x hx => by
      have h_lo : inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n ≤
          inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x :=
        le_trans db.e_vhd.le (le_trans (Nat.le_add_right _ _) (le_trans db.e_vc.le
          (le_trans (Nat.le_add_right _ _) (le_trans db.e_ps.le (Nat.le_add_right _ _)))))
      have h_hi : inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x <
          inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length :=
        lt_of_lt_of_le (Nat.add_lt_add_left hx _)
          (le_trans db.e_ew.le (le_trans (Nat.le_add_right _ _) db.e_q.le))
      have heq := hfr1 (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x)
        (Or.inr (Or.inr ⟨h_lo, h_hi⟩))
      change st1.mem (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) = _ at heq
      change st1.mem (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) = _
      rw [heq, hmem_p, t2SetupHdrMem_outside (Or.inr (le_trans hv1_ew (Nat.le_add_right _ _)))]
      exact ctx.hz0 _ (le_trans (Nat.le_add_right _ 32) (le_trans hv1_ew (Nat.le_add_right _ _))))
  obtain ⟨o2, st2, c2, hr2_run, ⟨ho2, hzf2, hfr2, hEmbUp, hVc2, hEwSt2, h25_2, h26_2⟩, hc2⟩ :=
    hInitJ0 (startState [inp.v1, inp.jAddr, nodesEnd] s18.mem s18.pos) ω ⟨rfl, rfl, rfl, rfl⟩
  subst ho2
  let s17 : State :=
    { mem := st2.mem, regs := Function.update s18.regs 17 (nodesEnd + 5 * ctx.wd.j0Edges.length), pos := st2.pos }
  have hs18_1 : s18.regs 1 = inp.jAddr := by
    simp (disch := decide) only [s18, s16, Function.update_of_ne, hrp1]
  have hs18_4 : s18.regs 4 = inp.v1 := by
    simp (disch := decide) only [s18, s16, Function.update_of_ne, hrp4]
  have hs18_5 : s18.regs 5 = ctx.wInp.prep.h := by
    simp (disch := decide) only [s18, s16, Function.update_of_ne, hrp5]
  have hs18_6 : s18.regs 6 = ctx.wInp.h := by
    simp (disch := decide) only [s18, s16, Function.update_of_ne, hrp6]
  have hs18_10 : s18.regs 10 = ctx.wd.comps.length := by
    simp (disch := decide) only [s18, s16, Function.update_of_ne, hrp10]
  have hs18_12 : s18.regs 12 = ctx.wd.W.m := by
    simp (disch := decide) only [s18, s16, Function.update_of_ne, hrp12]
  have hs18_15 : s18.regs 15 = ctx.wInp.prep.phiDen_dec := by
    simp (disch := decide) only [s18, s16, Function.update_of_ne, hrp15]
  have hs18_16 : s18.regs 16 = nodesEnd := by
    simp (disch := decide) only [s18, Function.update_of_ne, hr16_16]
  have hs18_18 : s18.regs 18 = stc.dsBaseAddr := by dsimp only [s18]; exact Function.update_self _ _ _
  have hs17_4 : s17.regs 4 = inp.v1 := by simp (disch := decide) only [s17, Function.update_of_ne, hs18_4]
  have hs17_5 : s17.regs 5 = ctx.wInp.prep.h := by simp (disch := decide) only [s17, Function.update_of_ne, hs18_5]
  have hs17_6 : s17.regs 6 = ctx.wInp.h := by simp (disch := decide) only [s17, Function.update_of_ne, hs18_6]
  have hs17_10 : s17.regs 10 = ctx.wd.comps.length := by simp (disch := decide) only [s17, Function.update_of_ne, hs18_10]
  have hs17_12 : s17.regs 12 = ctx.wd.W.m := by simp (disch := decide) only [s17, Function.update_of_ne, hs18_12]
  have hs17_15 : s17.regs 15 = ctx.wInp.prep.phiDen_dec := by simp (disch := decide) only [s17, Function.update_of_ne, hs18_15]
  have hs17_18 : s17.regs 18 = stc.dsBaseAddr := by simp (disch := decide) only [s17, Function.update_of_ne, hs18_18]
  have hr_c17 : Runs w p ω (Stmt.call 17 (selfBase + 2) [.reg 4, .reg 1, .reg 16]) s18 .normal s17
      (argsSize [.reg 4, .reg 1, .reg 16] + c2 + 1) := by
    refine runs_call_iff.mpr
      ⟨[inp.v1, inp.jAddr, nodesEnd], t2InitJ0Body, .returned (nodesEnd + 5 * ctx.wd.j0Edges.length),
        st2, c2, ?_, h2, hr2_run, rfl, rfl, rfl⟩
    simp [evalArgs, Expr.eval_reg_of_eq hs18_4, Expr.eval_reg_of_eq hs18_1, Expr.eval_reg_of_eq hs18_16]
  have hv1_n1 : inp.v1 + 32 ≤ nodesEnd := le_trans hv1_emb (le_trans (Nat.le_add_right _ _) hemb_nds)
  have hAgr2 : ∀ x < inp.v1, s17.mem x = mem₀ x := fun x hx =>
    (t2InitJ0Frame_lt_v1 hfr2 hv1_emb hv1_vc hv1_ew hv1_n1 hx).trans (hAgr1 x hx)
  have hst2 := ctx.agrees_preserves_static hAgr2
  have hslot2 : ∀ k < 32, k ≠ 25 → k ≠ 26 → s17.mem (inp.v1 + k) = st_p.mem (inp.v1 + k) :=
    fun k hk h25 h26 =>
      (t2InitJ0Frame_slot hfr2 hv1_emb hv1_vc hv1_ew hv1_n1 hk h25 h26).trans (hslot1 k hk)
  have hzero2 : ∀ k, (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
      k = 11 ∨ k = 27 ∨ k = 28) → s17.mem (inp.v1 + k) = 0 := fun k hk => by
    have hk_bounds : k < 32 ∧ k ≠ 25 ∧ k ≠ 26 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk_hdr : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨
        k = 11 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 := by
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [true_or, or_true]
    rw [hslot2 k hk_bounds.1 hk_bounds.2.1 hk_bounds.2.2, hmem_p,
      t2SetupHdrMem_zero_slots hk_hdr]
    exact ctx.hz0 _ (Nat.le_add_right _ _)
  have htail := task2_tail_setup_runs ctx s17 ω hst2.2.2.2.2.2.2.2 hst2.2.2.2.2.1
    ((hslot2 0 (by decide) (by decide) (by decide)).trans hs0)
    ((hslot2 15 (by decide) (by decide) (by decide)).trans hs15)
    ((hslot2 17 (by decide) (by decide) (by decide)).trans hs17)
    ((hslot2 19 (by decide) (by decide) (by decide)).trans hs19)
    ((hslot2 29 (by decide) (by decide) (by decide)).trans hs29)
    hs17_4 hs17_5 hs17_6 hs17_15
    cont (fun o stF c => ∃ c_cont, Q o stF c_cont ∧ c ≤ c_cont)
    (fun stL hmL _ hregsL hr19 hr31 hr32 hr33 hr34 hr35 hr36 hr37 hr38 hr39 hr40 => by
      have hLS := t2Setup_build_loopState ctx stc db hmem_p (s18 := s18) (s17 := s17) rfl rfl hmL hregsL
        hs17_4 hs17_10 hs17_12 hs17_18 rfl rfl rfl hr19 hr31 (hmL ▸ hr32) hr33 hr34 hr35 hr36 hr37
        hr38 hr39 hr40 hfr1 hfr2 hAgr1 hAgr2 hslot2 hzero2 hceb1 hvho1 hL_inc hzf2 hEmbUp
        hVc2 hEwSt2 h25_2 h26_2 hj0_mW hv1_w
      obtain ⟨o_f, st_f, c_f, hr_f, hq_f⟩ := hcont stc stL hLS
      exact ⟨o_f, st_f, c_f, hr_f, ⟨c_f, hq_f, le_refl _⟩⟩)
  obtain ⟨o_t, st_t, c_t, hr_t, ⟨_c_mid_f, ⟨c_f, hq_f, hcf_le⟩, hct_le⟩⟩ := htail
  refine ⟨o_t, st_t, (argsSize [.reg 4, .reg 17] + c1 + 1) +
      (10 + ((argsSize [.reg 4, .reg 1, .reg 16] + c2 + 1) + c_t + 1) + 1) + 1,
    ?_, ⟨c_f, hq_f, ?_⟩⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s16, _, _, hr_c16,
      runs_seq_iff.mpr (Or.inr ⟨s18, 10, _, hr_a18,
        runs_seq_iff.mpr (Or.inr ⟨s17, _, c_t, hr_c17, hr_t, rfl⟩), rfl⟩), rfl⟩)
  · have hargs1 : argsSize [.reg 4, .reg 17] = 2 := by simp [argsSize, Expr.size]
    have hargs2 : argsSize [.reg 4, .reg 1, .reg 16] = 3 := by simp [argsSize, Expr.size]
    rw [hargs1, hargs2]
    exact t2Setup_mid_cost_arith hc1 hc2 (le_trans hct_le (Nat.add_le_add_right hcf_le 65)) hj0_le_J

/-- Full setup phase of `task2Body` (`lines 1..57`, before `Stmt.loop (.reg 19)`):
builds header, incidence linked list, `J₀` embedding, and establishes initial `T2LoopState`. -/
lemma task2Setup_cps {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} {selfBase : ℕ} (ctx : T2Ctx impl inp mem₀ w)
    (h1 : p.procs[selfBase + 1]? = some t2BuildIncBody)
    (h2 : p.procs[selfBase + 2]? = some t2InitJ0Body)
    (st : State) (ω : ℕ → Bool)
    (hm : st.mem = mem₀)
    (hr0 : st.regs 0 = inp.hAddr) (hr1 : st.regs 1 = inp.jAddr)
    (hr2 : st.regs 2 = inp.embJHAddr) (hr3 : st.regs 3 = inp.t1OutAddr) (hr4 : st.regs 4 = inp.v1)
    (cont : Stmt) (Q : Outcome → State → ℕ → Prop)
    (hcont : ∀ (stc : T2StaticData ctx) (stL : State),
      T2LoopState ctx stc 0 (initEmb0 ctx.wInp) (initEmb0 ctx.wInp) stc.dsBaseAddr
        (stc.nodesEnd + 5 * ctx.wd.j0Edges.length) 0 0 0 stL →
      ∃ o stF c_cont, Runs w p ω cont stL o stF c_cont ∧ Q o stF c_cont) :
    ∃ o stF c_tot,
      Runs w p ω
        (t2PreambleStmt (
          Stmt.call 16 (selfBase + 1) [.reg 4, .reg 17] ;;
          Stmt.assign 18 (t2Add (.reg 16) (t2Mul (.reg 12) (t2Add (t2Mul (.const 2) (.reg 13)) (.const 5)))) ;;
          Stmt.call 17 (selfBase + 2) [.reg 4, .reg 1, .reg 16] ;;
          t2TailSetupStmt cont)) st o stF c_tot ∧
      ∃ c_cont, Q o stF c_cont ∧ c_tot ≤ c_cont + 215 * inp.J.m + 100 * inp.embVertSum + 500 := by
  obtain ⟨o, stF, c_pre, hr_pre, c_mid, ⟨c_f, hq_f, hc_post⟩, hc_pre⟩ :=
    t2_setup_preamble_runs ctx st ω hm hr0 hr1 hr2 hr3 hr4 (t2SetupMidStmt selfBase cont)
      (fun o stF c => ∃ c_cont, Q o stF c_cont ∧ c ≤ c_cont + 215 * inp.J.m + 100 * inp.embVertSum + 240)
      (fun st_p hmem_p hrp1 hrp4 hrp5 hrp6 hrp10 hrp12 hrp13 hrp15 hrp17 _ =>
        task2Setup_mid_runs ctx h1 h2 ω st_p hmem_p hrp1 hrp4 hrp5 hrp6 hrp10 hrp12 hrp13 hrp15 hrp17
          cont Q hcont)
  exact ⟨o, stF, c_pre, hr_pre, c_f, hq_f, by omega⟩

end MinCostFlow.Spanner
