module

public import MinCostFlow.Spanner.ProgTask2BuildIncTriple

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Task 2 `t2InitJ0Body` definitions, bounds, and inner loop step -/

/-- Exact walk assigned by `t2InitJ0` to `j0`-edge `jOrig`. -/
def t2J0Walk (J : Graph) (jOrig : ℕ) : Walk :=
  let p := J.edges.getD jOrig (0, 0)
  { verts := [p.1, p.2], edges := [jOrig] }

/-- Memory preservation frame for `t2InitJ0Body`: only `[v1 + 25, v1 + 27)`, `embWJ`,
`vcongNum`, `eWVertStamp`, and `[arena0, arenaEnd)` change. -/
def T2InitJ0Frame (inp : Task2Input) (mW K arena0 : ℕ) (mem₀ mem : ℕ → ℕ) : Prop :=
  ∀ a, a ≠ inp.v1 + 25 → a ≠ inp.v1 + 26 →
    (a < inp.embWJAddr ∨ inp.embWJAddr + mW ≤ a) →
    (a < inp.vcongNumAddr mW K ∨ inp.vcongNumAddr mW K + inp.H'.n ≤ a) →
    (a < inp.eWVertStampAddr mW K ∨ inp.eWVertStampAddr mW K + inp.H'.n ≤ a) →
    a < arena0 →
    mem a = mem₀ a

lemma t2InitJ0Frame_refl (inp : Task2Input) (mW K arena0 : ℕ) (mem : ℕ → ℕ) :
    T2InitJ0Frame inp mW K arena0 mem mem :=
  fun _ _ _ _ _ _ _ => rfl

lemma t2InitJ0Frame_upd_vcong {inp : Task2Input} {mW K arena0 x val : ℕ}
    {mem₀ mem : ℕ → ℕ} (h : T2InitJ0Frame inp mW K arena0 mem₀ mem) (hx : x < inp.H'.n) :
    T2InitJ0Frame inp mW K arena0 mem₀ (Function.update mem (inp.vcongNumAddr mW K + x) val) :=
  fun a h25 h26 he hv hs ha => by
    rw [Function.update_of_ne (by omega)]
    exact h a h25 h26 he hv hs ha

lemma t2InitJ0Frame_upd_stamp {inp : Task2Input} {mW K arena0 x val : ℕ}
    {mem₀ mem : ℕ → ℕ} (h : T2InitJ0Frame inp mW K arena0 mem₀ mem) (hx : x < inp.H'.n) :
    T2InitJ0Frame inp mW K arena0 mem₀ (Function.update mem (inp.eWVertStampAddr mW K + x) val) :=
  fun a h25 h26 he hv hs ha => by
    rw [Function.update_of_ne (by omega)]
    exact h a h25 h26 he hv hs ha

lemma t2InitJ0Frame_upd_embWJ {inp : Task2Input} {mW K arena0 eW val : ℕ}
    {mem₀ mem : ℕ → ℕ} (h : T2InitJ0Frame inp mW K arena0 mem₀ mem) (heW : eW < mW) :
    T2InitJ0Frame inp mW K arena0 mem₀ (Function.update mem (inp.embWJAddr + eW) val) :=
  fun a h25 h26 he hv hs ha => by
    rw [Function.update_of_ne (by omega)]
    exact h a h25 h26 he hv hs ha

lemma t2InitJ0Frame_upd_arena {inp : Task2Input} {mW K arena0 addr val : ℕ}
    {mem₀ mem : ℕ → ℕ} (h : T2InitJ0Frame inp mW K arena0 mem₀ mem) (haddr : arena0 ≤ addr) :
    T2InitJ0Frame inp mW K arena0 mem₀ (Function.update mem addr val) :=
  fun a h25 h26 he hv hs ha => by
    rw [Function.update_of_ne (by omega)]
    exact h a h25 h26 he hv hs ha

lemma t2InitJ0Frame_upd_v25 {inp : Task2Input} {mW K arena0 val : ℕ}
    {mem₀ mem : ℕ → ℕ} (h : T2InitJ0Frame inp mW K arena0 mem₀ mem) :
    T2InitJ0Frame inp mW K arena0 mem₀ (Function.update mem (inp.v1 + 25) val) :=
  fun a h25 h26 he hv hs ha => by
    rw [Function.update_of_ne h25]
    exact h a h25 h26 he hv hs ha

lemma t2InitJ0Frame_upd_v26 {inp : Task2Input} {mW K arena0 val : ℕ}
    {mem₀ mem : ℕ → ℕ} (h : T2InitJ0Frame inp mW K arena0 mem₀ mem) :
    T2InitJ0Frame inp mW K arena0 mem₀ (Function.update mem (inp.v1 + 26) val) :=
  fun a h25 h26 he hv hs ha => by
    rw [Function.update_of_ne h26]
    exact h a h25 h26 he hv hs ha

/-- Vertex-wise weight contribution from `j0`-edges `< upTo`. -/
def j0VcongUpTo (wd : WitnessData) (wWNum : ℕ → ℕ) (embJH : ℕ → Walk) (upTo x : ℕ) : ℕ :=
  ∑ eW ∈ Finset.range upTo,
    if x ∈ (embJH (wd.j0Edges.getD eW 0)).verts then wWNum eW else 0

/-- Partial `embWJ` predicate after processing `upTo ≤ j0Len` edges in `t2InitJ0`. -/
def InitJ0EmbUpTo (mem : ℕ → ℕ) (embWJAddr arena0 upTo mW : ℕ) (J : Graph)
    (j0Edges : List ℕ) : Prop :=
  ∀ eW < mW,
    (eW < upTo →
      mem (embWJAddr + eW) = arena0 + 5 * eW ∧
      WalkAt mem (arena0 + 5 * eW) (t2J0Walk J (j0Edges.getD eW 0))) ∧
    (upTo ≤ eW → mem (embWJAddr + eW) = 0)

lemma t2J0Walk_at {mem : ℕ → ℕ} {ptr u v jOrig : ℕ} {J : Graph}
    (hj : jOrig < J.m)
    (hu : u = (J.edges[jOrig]).1) (hv : v = (J.edges[jOrig]).2)
    (h0 : mem ptr = 2) (h1 : mem (ptr + 1) = u) (h2 : mem (ptr + 2) = v)
    (h3 : mem (ptr + 3) = 1) (h4 : mem (ptr + 4) = jOrig) :
    WalkAt mem ptr (t2J0Walk J jOrig) := by
  have hget : J.edges.getD jOrig (0, 0) = J.edges[jOrig] := List.getD_eq_getElem _ _ hj
  rw [walkAt_iff]
  simp only [t2J0Walk, hget, List.length_cons, List.length_nil, listAt_cons, listAt_nil]
  refine ⟨h0, ⟨by simpa [← hu] using h1, by simpa [← hv] using h2, trivial⟩, h3, ⟨h4, trivial⟩⟩

private lemma nodesAddr_mono_args (inp : Task2Input) {m₁ m₂ k₁ k₂ : ℕ}
    (hm : m₁ ≤ m₂) (hk : k₁ ≤ k₂) :
    inp.nodesAddr m₁ k₁ ≤ inp.nodesAddr m₂ k₂ := by
  simp only [Task2Input.nodesAddr, Task2Input.queueAddr, Task2Input.eWVertStampAddr,
    Task2Input.procStampAddr, Task2Input.vcongNumAddr, Task2Input.vHeadAddr,
    Task2Input.vhatStampAddr, Task2Input.compEdgeDelRoundAddr, Task2Input.vhatOffsetAddr,
    Task2Input.compEdgeBaseAddr, Task2Input.dsHandlesAddr, Task2Input.embWJAddr]
  omega

lemma t2_initJ0_bounds {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) {arena0 : ℕ}
    (_har_lo : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ≤ arena0)
    (har_hi : arena0 ≤ inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length + 3 * inp.embVertSum) :
    let mW := ctx.wd.W.m
    let K := ctx.wd.comps.length
    inp.v1 + 32 = inp.embWJAddr ∧
    inp.embWJAddr + mW = inp.dsHandlesAddr mW ∧
    inp.dsHandlesAddr mW + K = inp.compEdgeBaseAddr mW K ∧
    inp.compEdgeBaseAddr mW K + 2 * K = inp.compEdgeDelRoundAddr mW K ∧
    inp.compEdgeDelRoundAddr mW K ≤ inp.vHeadAddr mW K ∧
    inp.vHeadAddr mW K + inp.H'.n = inp.vcongNumAddr mW K ∧
    inp.vcongNumAddr mW K + inp.H'.n = inp.procStampAddr mW K ∧
    inp.procStampAddr mW K + inp.H'.n = inp.eWVertStampAddr mW K ∧
    inp.eWVertStampAddr mW K + inp.H'.n = inp.queueAddr mW K ∧
    inp.queueAddr mW K + inp.H'.n = inp.nodesAddr mW K ∧
    ctx.wd.j0Edges.length ≤ mW ∧
    arena0 + 5 * ctx.wd.j0Edges.length < 2 ^ w := by
  dsimp only
  have hmW : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by
    rw [ctx.hw_okW.W_m_eq]; exact Nat.le_add_right _ _
  have h1 : inp.v1 + 32 = inp.embWJAddr := rfl
  have h2 : inp.embWJAddr + ctx.wd.W.m = inp.dsHandlesAddr ctx.wd.W.m := rfl
  have h3 : inp.dsHandlesAddr ctx.wd.W.m + ctx.wd.comps.length =
      inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length := rfl
  have h4 : inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + 2 * ctx.wd.comps.length =
      inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length := by
    simp only [Task2Input.compEdgeDelRoundAddr, Task2Input.vhatOffsetAddr]; omega
  have h5 : inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length ≤
      inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length := by
    simp only [Task2Input.vHeadAddr, Task2Input.vhatStampAddr]; omega
  have h6 : inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n =
      inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length := rfl
  have h7 : inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n =
      inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length := rfl
  have h8 : inp.procStampAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n =
      inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length := rfl
  have h9 : inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n =
      inp.queueAddr ctx.wd.W.m ctx.wd.comps.length := rfl
  have h10 : inp.queueAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n =
      inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length := rfl
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hmW, ?_⟩
  have hnodes_le := nodesAddr_mono_args inp ctx.hmW_le ctx.hK_le
  have hmw_mul : 5 * ctx.wd.j0Edges.length ≤
      Task1Input.mwCap impl inp.J * (2 * Task2Input.gammaExpCap impl inp.J + 5) := by
    calc 5 * ctx.wd.j0Edges.length ≤ 5 * Task1Input.mwCap impl inp.J :=
          Nat.mul_le_mul_left 5 (le_trans hmW ctx.hmW_le)
      _ = Task1Input.mwCap impl inp.J * 5 := Nat.mul_comm _ _
      _ ≤ Task1Input.mwCap impl inp.J * (2 * Task2Input.gammaExpCap impl inp.J + 5) :=
          Nat.mul_le_mul_left _ (by omega)
  have hstatic_le : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length + 3 * inp.embVertSum +
      5 * ctx.wd.j0Edges.length ≤ Task2Input.staticEndCap impl inp := by
    unfold Task2Input.staticEndCap; dsimp only; omega
  have hmax_le : Task2Input.staticEndCap impl inp ≤ Task2Input.maxWordBound impl inp := by
    refine le_trans ?_ (le_max_left _ _)
    unfold Task2Input.maxHeapEnd; dsimp only; omega
  have hcap := ctx.hww.2.2
  omega

lemma t2_j0VertSum_le_embVertSum {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) :
    ∑ eW ∈ Finset.range ctx.wd.j0Edges.length,
      (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.length ≤ inp.embVertSum := by
  have hnd : ctx.wd.j0Edges.Nodup := ctx.hw_okW.j0_nodup
  have hlt : ∀ j ∈ ctx.wd.j0Edges, j < inp.J.m := by
    intro j hj; simpa [ctx.hWInpJ] using ctx.hw_okW.j0_lt j hj
  unfold Task2Input.embVertSum
  rw [← Finset.sum_image (f := fun eJ => (inp.embJH eJ).verts.length)
    (g := fun eW => ctx.wd.j0Edges.getD eW 0) (by
      intro a ha b hb hab
      have ha' := Finset.mem_range.mp ha
      have hb' := Finset.mem_range.mp hb
      dsimp only at hab
      rw [List.getD_eq_getElem _ _ ha', List.getD_eq_getElem _ _ hb'] at hab
      exact (hnd.getElem_inj_iff).mp hab)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
  intro j hj
  rcases Finset.mem_image.mp hj with ⟨eW, heW, rfl⟩
  have heW' := Finset.mem_range.mp heW
  rw [List.getD_eq_getElem _ _ heW']
  exact Finset.mem_range.mpr (hlt _ (List.getElem_mem heW'))

lemma t2_j0WNum_bound {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ memStart : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (hStat : ctx.StaticOutAt memStart)
    (hj0_pos : 0 < ctx.wd.j0Edges.length) :
    (∀ eW < ctx.wd.j0Edges.length,
      memStart (memStart (ctx.wInp.h + 14) + eW) ≤ Task1Input.phiDenCap impl inp.J) ∧
    ctx.wd.j0Edges.length * Task1Input.phiDenCap impl inp.J < 2 ^ w := by
  have hmW : ctx.wd.j0Edges.length ≤ ctx.wd.W.m := by
    rw [ctx.hw_okW.W_m_eq]; exact Nat.le_add_right _ _
  have hds := ctx.ds_bounds
  have hm0 : ctx.wInp.prep.J0_strip.m = (stripLoops inp.J).m := hds.2.2.2.1
  have hpd_cap : ctx.wInp.prep.phiDen_dec ≤ Task1Input.phiDenCap impl inp.J := by
    unfold Task1Input.phiDenCap
    rw [← hm0]
    exact ctx.hφ_cap
  have hper : ∀ eW < ctx.wd.j0Edges.length,
      memStart (memStart (ctx.wInp.h + 14) + eW) ≤ Task1Input.phiDenCap impl inp.J := by
    intro eW heW
    have heW_mW : eW < ctx.wd.W.m := lt_of_lt_of_le heW hmW
    have hw_eq := (hStat.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 eW heW_mW).1
    have hw_j0 : ctx.wd.wW eW = ctx.wd.φ_dec :=
      (mkW_W_edges_j0 (inp := ctx.wInp) (ce := impl.constructExpander)
        (pds := impl.pathDS.params) (WSubs := ctx.WSubs) heW).2.2
    rw [hw_j0] at hw_eq
    have hpd_pos : (0 : ℝ) < (ctx.wInp.prep.phiDen_dec : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hds.2.2.2.2.1 hds.2.2.2.2.2.1
    change (memStart (memStart (ctx.wInp.h + 14) + eW) : ℝ) / _ =
      (ctx.wInp.prep.phiNum_dec : ℝ) / _ at hw_eq
    have hnum_eq : memStart (memStart (ctx.wInp.h + 14) + eW) = ctx.wInp.prep.phiNum_dec := by
      exact_mod_cast (div_left_inj' hpd_pos.ne').mp hw_eq
    exact hnum_eq ▸ le_trans hds.2.2.2.2.2.1 hpd_cap
  refine ⟨hper, ?_⟩
  have hj0_m : ctx.wd.j0Edges.length ≤ inp.J.m := by
    have := mkW_sum_comp_j_m_le_J ctx.hstat ctx.hw_okW ctx.hws
    change ctx.wd.j0Edges.length + (ctx.wd.comps.map fun c => c.J_sub.m).sum ≤ ctx.wInp.prep.J.m at this
    rw [ctx.hWInpJ] at this; omega
  have h1deg : 1 ≤ maxDeg inp.J := by
    have h0 : 0 < inp.J.m := lt_of_lt_of_le hj0_pos hj0_m
    have hvol : inp.J.vol inp.J.verts = 2 * inp.J.m := vol_verts_eq_two_mul_m ctx.hJ
    by_contra hlt
    have hz : maxDeg inp.J = 0 := by omega
    have hsum0 : inp.J.vol inp.J.verts = 0 := by
      unfold Graph.vol Graph.volIn
      apply Finset.sum_eq_zero
      intro v hv
      have hdv : inp.J.deg v ≤ maxDeg inp.J := deg_le_maxDeg (Finset.mem_range.mp hv)
      change inp.J.deg v = 0; omega
    omega
  have hmw : ctx.wd.j0Edges.length ≤ Task1Input.mwCap impl inp.J := le_trans hmW ctx.hmW_le
  set mw := Task1Input.mwCap impl inp.J
  set md := maxDeg inp.J
  set pd := Task1Input.phiDenCap impl inp.J
  have hle_mw : ctx.wd.j0Edges.length * pd ≤ 2 * mw * md * pd + 2 := by
    have h1 : ctx.wd.j0Edges.length * pd ≤ mw * pd := Nat.mul_le_mul_right pd hmw
    have h2 : mw * pd ≤ (mw * md) * pd := Nat.mul_le_mul_right pd (Nat.le_mul_of_pos_right mw h1deg)
    have h3 : (mw * md) * pd ≤ 2 * (mw * md * pd) := Nat.le_mul_of_pos_left _ (by decide)
    have h4 : 2 * (mw * md * pd) = 2 * mw * md * pd := by ring
    omega
  have hwb : 2 * mw * md * pd + 2 ≤ Task2Input.maxWordBound impl inp := by
    refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_right _ _))
    exact Nat.le_add_left _ _
  exact lt_of_le_of_lt (le_trans hle_mw hwb) ctx.hww.2.2

/-- Inner loop invariant during processing of `j0`-edge `eW` up to walk vertex index `j`. -/
def T2InitJ0InnerInv {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (memStart : ℕ → ℕ)
    (arena0 eW : ℕ) (vcongBase : ℕ → ℕ) (j : ℕ) (walk : Walk) (st : State) : Prop :=
  let mW := ctx.wd.W.m
  let K := ctx.wd.comps.length
  let jOrig := ctx.wd.j0Edges.getD eW 0
  let wWNum := fun i => memStart (memStart (ctx.wInp.h + 14) + i)
  st.regs 0 = inp.v1 ∧
  st.regs 1 = inp.jAddr ∧
  st.regs 3 = ctx.wInp.prep.h ∧
  st.regs 4 = ctx.wd.j0Edges.length ∧
  st.regs 5 = ctx.wInp.prep.aJ0Out ∧
  st.regs 6 = inp.embWJAddr ∧
  st.regs 7 = ctx.wInp.h ∧
  st.regs 8 = memStart (ctx.wInp.h + 14) ∧
  st.regs 9 = inp.embJHAddr ∧
  st.regs 10 = inp.vcongNumAddr mW K ∧
  st.regs 11 = inp.eWVertStampAddr mW K ∧
  st.regs 12 = arena0 + 5 * (eW + 1) ∧
  st.regs 13 = eW ∧
  st.regs 14 = jOrig ∧
  st.regs 17 = eW + 1 ∧
  st.regs 18 = wWNum eW ∧
  st.regs 19 = memStart (inp.embJHAddr + jOrig) ∧
  st.regs 20 = walk.verts.length ∧
  ZeroFrom st.mem (arena0 + 5 * (eW + 1)) ∧
  T2InitJ0Frame inp mW K arena0 memStart st.mem ∧
  InitJ0EmbUpTo st.mem inp.embWJAddr arena0 (eW + 1) mW inp.J ctx.wd.j0Edges ∧
  (∀ x < inp.H'.n, st.mem (inp.vcongNumAddr mW K + x) =
    vcongBase x + (if x ∈ walk.verts.take j then wWNum eW else 0)) ∧
  (∀ x < inp.H'.n, st.mem (inp.eWVertStampAddr mW K + x) ≤ eW + 1 ∧
    (st.mem (inp.eWVertStampAddr mW K + x) = eW + 1 ↔ x ∈ walk.verts.take j))

/-- Outer loop invariant of `t2InitJ0Body` after `upTo ≤ j0Len` edges. -/
def T2InitJ0OuterInv {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) (memStart : ℕ → ℕ)
    (arena0 upTo : ℕ) (st : State) : Prop :=
  let mW := ctx.wd.W.m
  let K := ctx.wd.comps.length
  let wWNum := fun i => memStart (memStart (ctx.wInp.h + 14) + i)
  st.regs 0 = inp.v1 ∧
  st.regs 1 = inp.jAddr ∧
  st.regs 3 = ctx.wInp.prep.h ∧
  st.regs 4 = ctx.wd.j0Edges.length ∧
  st.regs 5 = ctx.wInp.prep.aJ0Out ∧
  st.regs 6 = inp.embWJAddr ∧
  st.regs 7 = ctx.wInp.h ∧
  st.regs 8 = memStart (ctx.wInp.h + 14) ∧
  st.regs 9 = inp.embJHAddr ∧
  st.regs 10 = inp.vcongNumAddr mW K ∧
  st.regs 11 = inp.eWVertStampAddr mW K ∧
  st.regs 12 = arena0 + 5 * upTo ∧
  ZeroFrom st.mem (arena0 + 5 * upTo) ∧
  T2InitJ0Frame inp mW K arena0 memStart st.mem ∧
  InitJ0EmbUpTo st.mem inp.embWJAddr arena0 upTo mW inp.J ctx.wd.j0Edges ∧
  (∀ x < inp.H'.n, st.mem (inp.vcongNumAddr mW K + x) = j0VcongUpTo ctx.wd wWNum inp.embJH upTo x) ∧
  (∀ x < inp.H'.n, st.mem (inp.eWVertStampAddr mW K + x) ≤ upTo)

lemma t2InitJ0_inner_step {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} {p : Program} (ctx : T2Ctx impl inp mem₀ w) {memStart : ℕ → ℕ}
    {arena0 eW j : ℕ} (heW : eW < ctx.wd.j0Edges.length)
    (hj : j < (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.length)
    (hEmb : EmbAt memStart inp.embJHAddr inp.J.m inp.embJH)
    (hEmbBnd : EmbBounded memStart inp.embJHAddr inp.J.m inp.embJH inp.t1OutAddr)
    (har_lo : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ≤ arena0)
    (har_hi : arena0 ≤ inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length + 3 * inp.embVertSum)
    (hVcongBnd : ∀ x < inp.H'.n,
      j0VcongUpTo ctx.wd (fun i => memStart (memStart (ctx.wInp.h + 14) + i)) inp.embJH eW x +
        memStart (memStart (ctx.wInp.h + 14) + eW) < 2 ^ w) :
    let jOrig := ctx.wd.j0Edges.getD eW 0
    let walk := inp.embJH jOrig
    let vcongBase := fun x =>
      j0VcongUpTo ctx.wd (fun i => memStart (memStart (ctx.wInp.h + 14) + i)) inp.embJH eW x
    Triple w p
      (fun st => T2InitJ0InnerInv ctx memStart arena0 eW vcongBase j walk st ∧ st.regs 21 = j)
      (Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;;
       Stmt.cond (t2Ne (t2Ld (.reg 11) (.reg 22)) (.reg 17)) (
         t2St (.reg 11) (.reg 22) (.reg 17) ;;
         t2St (.reg 10) (.reg 22) (t2Add (t2Ld (.reg 10) (.reg 22)) (.reg 18))
       ) Stmt.nop)
      (normalPost fun st₁ =>
        T2InitJ0InnerInv ctx memStart arena0 eW vcongBase (j + 1) walk
          { st₁ with regs := Function.update st₁.regs 21 (j + 1) } ∧ st₁.regs 21 = j)
      (fun _ => 36) := by
  intro jOrig walk vcongBase st ω ⟨hinv, hr21⟩
  rcases hinv with ⟨hr0, hr1, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13, hr14,
    hr17, hr18, hr19, hr20, hzf, hfr, hEmbWJ, hVcong, hStamp⟩
  dsimp only [jOrig, walk, vcongBase] at hj hr10 hr11 hr14 hr18 hr19 hr20 hzf hfr hEmbWJ hVcong hStamp hVcongBnd ⊢
  have hbnd := t2_initJ0_bounds ctx har_lo har_hi
  rcases hbnd with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, hmW, har_w⟩
  rcases t2_prep_chain_bounds ctx with ⟨hc1, hc2, hc3, hc4⟩
  have hW : 1 < 2 ^ w := ctx.hww.1
  have hjOrig_m : ctx.wd.j0Edges.getD eW 0 < inp.J.m := by
    have := ctx.hw_okW.j0_lt (ctx.wd.j0Edges.getD eW 0)
      (by rw [List.getD_eq_getElem _ _ heW]; exact List.getElem_mem heW)
    simpa [ctx.hWInpJ] using this
  have hemb_at := hEmb (ctx.wd.j0Edges.getD eW 0) hjOrig_m
  have hemb_bnd := hEmbBnd.2 (ctx.wd.j0Edges.getD eW 0) hjOrig_m
  have hdisj : inp.v1 < 2 ^ w := by omega
  have hptr_w : memStart (inp.embJHAddr + ctx.wd.j0Edges.getD eW 0) < 2 ^ w := by
    have := hEmbBnd.1; omega
  have hptr_bnd : memStart (inp.embJHAddr + ctx.wd.j0Edges.getD eW 0) +
      (2 + (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.length +
        (inp.embJH (ctx.wd.j0Edges.getD eW 0)).edges.length) ≤ inp.t1OutAddr := by
    simpa [walk_encode_length] using hemb_bnd
  have hj_w : 1 + j < 2 ^ w := by omega
  have hv_mem : (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts[j] ∈
      (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts := List.getElem_mem hj
  set x := (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts[j]
  have hx_nH : x < inp.H'.n :=
    Walk.isWalk_verts_lt ctx.hH' (ctx.hembJH.2 (ctx.wd.j0Edges.getD eW 0) hjOrig_m) x hv_mem
  have hx_w : x < 2 ^ w := by omega
  have heW1_w : eW + 1 < 2 ^ w := by omega
  have hx_st_addr : memStart (inp.embJHAddr + ctx.wd.j0Edges.getD eW 0) + (1 + j) < inp.v1 := by omega
  have hwalk_val : st.mem (memStart (inp.embJHAddr + ctx.wd.j0Edges.getD eW 0) + (1 + j)) = x := by
    rw [hfr _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)]
    have hwa := ((walkAt_iff.mp hemb_at).2.1)
    have hget := listAt_getElem hwa hj
    simpa only [Nat.add_assoc, jOrig] using hget.trans rfl
  suffices hres : ∃ o st' c, Runs w p ω
      (Stmt.assign 22 (t2Ld (.reg 19) (t2Add (.const 1) (.reg 21))) ;;
       Stmt.cond (t2Ne (t2Ld (.reg 11) (.reg 22)) (.reg 17)) (
         t2St (.reg 11) (.reg 22) (.reg 17) ;;
         t2St (.reg 10) (.reg 22) (t2Add (t2Ld (.reg 10) (.reg 22)) (.reg 18))
       ) Stmt.nop) st o st' c ∧
      normalPost (fun st₁ => T2InitJ0InnerInv ctx memStart arena0 eW
        (fun x => j0VcongUpTo ctx.wd (fun i => memStart (memStart (ctx.wInp.h + 14) + i)) inp.embJH eW x)
        (j + 1) (inp.embJH (ctx.wd.j0Edges.getD eW 0))
        { st₁ with regs := Function.update st₁.regs 21 (j + 1) } ∧ st₁.regs 21 = j) o st' ∧
      0 + c ≤ 36 by
    simpa only [Nat.zero_add] using hres
  refine runs_seq_assign_le (v := x)
    (ev_load (ev_add (ev_reg hr19 hptr_w) (ev_add (ev_const (w := w) hW) (ev_reg hr21 (by omega)) hj_w)
      (by omega)) hwalk_val hx_w) ?_
  set r22 := Function.update st.regs 22 x
  have hst_addr_w : inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x < 2 ^ w := by omega
  have hv_addr_w : inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x < 2 ^ w := by omega
  have hst_cur_w : st.mem (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) < 2 ^ w := by
    have := (hStamp x hx_nH).1; omega
  by_cases hst_eq : st.mem (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) = eW + 1
  · have hev : (t2Ne (t2Ld (.reg 11) (.reg 22)) (.reg 17)).eval w { st with regs := r22 } = some 0 :=
      ev_ne_f (ev_load (ev_add (ev_reg (r := 11) (by simp [r22, hr11]) (by omega))
        (ev_reg (r := 22) (by simp [r22]) hx_w) hst_addr_w) rfl hst_cur_w)
        (ev_reg (r := 17) (by simp [r22, hr17]) heW1_w) hst_eq hW
    refine ⟨.normal, { st with regs := r22 },
      (t2Ne (t2Ld (.reg 11) (.reg 22)) (.reg 17)).size + 1 + 1,
      runs_cond_iff.mpr ⟨0, 1, hev, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, ?_,
      by simp only [Expr.size]; omega⟩
    refine ⟨⟨by simp [r22, hr0], by simp [r22, hr1], by simp [r22, hr3], by simp [r22, hr4],
      by simp [r22, hr5], by simp [r22, hr6], by simp [r22, hr7], by simp [r22, hr8],
      by simp [r22, hr9], by simp [r22, hr10], by simp [r22, hr11], by simp [r22, hr12],
      by simp [r22, hr13], by simp [r22, hr14], by simp [r22, hr17], by simp [r22, hr18],
      by simp [r22, hr19], by simp [r22, hr20], hzf, hfr, hEmbWJ, ?_, ?_⟩, by simp [r22, hr21]⟩
    · have hx_take : x ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take j := (hStamp x hx_nH).2.mp hst_eq
      intro y hy
      rw [hVcong y hy]
      have hmem_iff : y ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take (j + 1) ↔
          y ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take j := by
        rw [List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton]
        exact ⟨fun h => h.elim id (fun hye => hye ▸ hx_take), fun h => Or.inl h⟩
      simp only [hmem_iff]
    · intro y hy
      have hx_take : x ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take j := (hStamp x hx_nH).2.mp hst_eq
      have hmem_iff : y ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take (j + 1) ↔
          y ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take j := by
        rw [List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton]
        exact ⟨fun h => h.elim id (fun hye => hye ▸ hx_take), fun h => Or.inl h⟩
      rw [hmem_iff]
      exact hStamp y hy
  · have hx_ntake : x ∉ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take j :=
      fun h => hst_eq ((hStamp x hx_nH).2.mpr h)
    have hev : (t2Ne (t2Ld (.reg 11) (.reg 22)) (.reg 17)).eval w { st with regs := r22 } = some 1 :=
      ev_ne_t (ev_load (ev_add (ev_reg (r := 11) (by simp [r22, hr11]) (by omega))
        (ev_reg (r := 22) (by simp [r22]) hx_w) hst_addr_w) rfl hst_cur_w)
        (ev_reg (r := 17) (by simp [r22, hr17]) heW1_w) hst_eq hW
    suffices hbr : ∃ o st' c₁, Runs w p ω
        (t2St (.reg 11) (.reg 22) (.reg 17) ;;
         t2St (.reg 10) (.reg 22) (t2Add (t2Ld (.reg 10) (.reg 22)) (.reg 18)))
        { st with regs := r22 } o st' c₁ ∧
        normalPost (fun st₁ => T2InitJ0InnerInv ctx memStart arena0 eW
          (fun x => j0VcongUpTo ctx.wd (fun i => memStart (memStart (ctx.wInp.h + 14) + i)) inp.embJH eW x)
          (j + 1) (inp.embJH (ctx.wd.j0Edges.getD eW 0))
          { st₁ with regs := Function.update st₁.regs 21 (j + 1) } ∧ st₁.regs 21 = j) o st' ∧
        0 + c₁ ≤ 18 by
      rcases hbr with ⟨o, st', c₁, hr, hq, hc⟩
      refine ⟨o, st', (t2Ne (t2Ld (.reg 11) (.reg 22)) (.reg 17)).size + c₁ + 1,
        runs_cond_iff.mpr ⟨1, c₁, hev, by simpa using hr, rfl⟩, hq,
        by simp only [Expr.size] at hc ⊢; omega⟩
    refine runs_seq_store_le (ev_add (ev_reg (r := 11) (by simp [r22, hr11]) (by omega))
      (ev_reg (r := 22) (by simp [r22]) hx_w) hst_addr_w)
      (ev_reg (r := 17) (by simp [r22, hr17]) heW1_w) ?_
    set m1 := Function.update st.mem (inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x) (eW + 1)
    have hm1_vc : m1 (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x) =
        j0VcongUpTo ctx.wd (fun i => memStart (memStart (ctx.wInp.h + 14) + i)) inp.embJH eW x := by
      simp only [m1, Function.update_of_ne (by omega :
        inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x ≠
        inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x)]
      rw [hVcong x hx_nH]; simp only [hx_ntake, ↓reduceIte, add_zero]
    have hvc_sum_w : j0VcongUpTo ctx.wd (fun i => memStart (memStart (ctx.wInp.h + 14) + i)) inp.embJH eW x +
        memStart (memStart (ctx.wInp.h + 14) + eW) < 2 ^ w := hVcongBnd x hx_nH
    have hm1_w : j0VcongUpTo ctx.wd (fun i => memStart (memStart (ctx.wInp.h + 14) + i)) inp.embJH eW x < 2 ^ w := by omega
    refine runs_store_le
      (ev_add (ev_reg (r := 10) (by simp [r22, hr10]) (by omega)) (ev_reg (r := 22) (by simp [r22]) hx_w)
        hv_addr_w)
      (ev_add (ev_load (ev_add (ev_reg (r := 10) (by simp [r22, hr10]) (by omega))
          (ev_reg (r := 22) (by simp [r22]) hx_w) hv_addr_w) hm1_vc hm1_w)
        (ev_reg (r := 18) (by simp [r22, hr18]) (by omega)) hvc_sum_w)
      ?_ (by simp only [Expr.size]; omega)
    set m2 := Function.update m1 (inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x)
      (j0VcongUpTo ctx.wd (fun i => memStart (memStart (ctx.wInp.h + 14) + i)) inp.embJH eW x +
        memStart (memStart (ctx.wInp.h + 14) + eW))
    have hm2_emb : InitJ0EmbUpTo m2 inp.embWJAddr arena0 (eW + 1) ctx.wd.W.m inp.J ctx.wd.j0Edges := by
      intro i hi
      refine ⟨fun hi1 => ?_, fun hi1 => ?_⟩
      · have hpi := (hEmbWJ i hi).1 hi1
        have ha1 : inp.embWJAddr + i ≠ inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x := by omega
        have ha2 : inp.embWJAddr + i ≠ inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x := by omega
        refine ⟨by simp [m2, m1, ha1, ha2, hpi.1], ?_⟩
        refine walkAt_of_agreeOutside (lo := 0) (hi := arena0) hpi.2 ?_ (Or.inr (by omega))
        intro p hp
        rcases hp with hp0 | hp_ar
        · exact False.elim (Nat.not_lt_zero _ hp0)
        · simp [m2, m1,
            Function.update_of_ne (by omega : p ≠ inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x),
            Function.update_of_ne (by omega : p ≠ inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x)]
      · simp [m2, m1, Function.update_of_ne (by omega : inp.embWJAddr + i ≠ inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x),
          Function.update_of_ne (by omega : inp.embWJAddr + i ≠ inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x),
          (hEmbWJ i hi).2 hi1]
    refine ⟨⟨by simp [r22, hr0], by simp [r22, hr1], by simp [r22, hr3], by simp [r22, hr4],
      by simp [r22, hr5], by simp [r22, hr6], by simp [r22, hr7], by simp [r22, hr8],
      by simp [r22, hr9], by simp [r22, hr10], by simp [r22, hr11], by simp [r22, hr12],
      by simp [r22, hr13], by simp [r22, hr14], by simp [r22, hr17], by simp [r22, hr18],
      by simp [r22, hr19], by simp [r22, hr20], ?_,
      t2InitJ0Frame_upd_vcong (t2InitJ0Frame_upd_stamp hfr hx_nH) hx_nH, hm2_emb, ?_, ?_⟩,
      by simp [r22, hr21]⟩
    · intro a ha
      simp only [m2, m1, Function.update_of_ne (by omega : a ≠ inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x),
        Function.update_of_ne (by omega : a ≠ inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x)]
      exact hzf a ha
    · intro y hy
      by_cases hyx : y = x
      · subst hyx
        have hmem : x ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take (j + 1) := by
          rw [List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton]
          exact Or.inr rfl
        simp only [m2, Function.update_self, hmem, ↓reduceIte]
      · simp only [m2, m1, Function.update_of_ne (by omega : inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + y ≠ inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x),
          Function.update_of_ne (by omega : inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + y ≠ inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x)]
        rw [hVcong y hy]
        have hmem_iff : y ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take (j + 1) ↔
            y ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take j := by
          rw [List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton]
          exact ⟨fun h => h.elim id (fun hye => absurd hye hyx), fun h => Or.inl h⟩
        simp only [hmem_iff]
    · intro y hy
      by_cases hyx : y = x
      · subst hyx
        have hmem : x ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take (j + 1) := by
          rw [List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton]
          exact Or.inr rfl
        simp only [m2, m1,
          Function.update_of_ne (by omega : inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x ≠ inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x),
          Function.update_self, hmem]
        exact ⟨le_refl _, trivial⟩
      · simp only [m2, m1, Function.update_of_ne (by omega : inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + y ≠ inp.vcongNumAddr ctx.wd.W.m ctx.wd.comps.length + x),
          Function.update_of_ne (by omega : inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + y ≠ inp.eWVertStampAddr ctx.wd.W.m ctx.wd.comps.length + x)]
        have hmem_iff : y ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take (j + 1) ↔
            y ∈ (inp.embJH (ctx.wd.j0Edges.getD eW 0)).verts.take j := by
          rw [List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton]
          exact ⟨fun h => h.elim id (fun hye => absurd hye hyx), fun h => Or.inl h⟩
        rw [hmem_iff]
        exact hStamp y hy

end MinCostFlow.Spanner
