module

public import MinCostFlow.Spanner.ProgTask2Ctx

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Small expression helpers and `t2BuildInc` incidence-list invariants -/

theorem ev_ne_t {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (hne : a ≠ b) (hw : 1 < 2 ^ w) :
    (t2Ne e₁ e₂).eval w st = some 1 :=
  ev_eq_t (ev_eq_f h₁ h₂ hne hw) (ev_const (Nat.zero_lt_of_lt hw)) rfl hw

theorem ev_ne_f {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (heq : a = b) (hw : 1 < 2 ^ w) :
    (t2Ne e₁ e₂).eval w st = some 0 :=
  ev_eq_f (ev_eq_t h₁ h₂ heq hw) (ev_const (Nat.zero_lt_of_lt hw)) Nat.one_ne_zero hw

theorem ev_le_t {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (hle : a ≤ b) (hw : 1 < 2 ^ w) :
    (t2Le e₁ e₂).eval w st = some 1 :=
  ev_eq_t (ev_lt_f h₂ h₁ hle hw) (ev_const (Nat.zero_lt_of_lt hw)) rfl hw

theorem ev_le_f {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (hlt : b < a) (hw : 1 < 2 ^ w) :
    (t2Le e₁ e₂).eval w st = some 0 :=
  ev_eq_f (ev_lt_t h₂ h₁ hlt hw) (ev_const (Nat.zero_lt_of_lt hw)) Nat.one_ne_zero hw

lemma t2_nodesAddr_le {impl : SpannerToolImpl} {inp : Task2Input} {mW K : ℕ}
    (hmW : mW ≤ Task1Input.mwCap impl inp.J) (hK : K ≤ inp.J.m) :
    inp.nodesAddr mW K ≤ inp.nodesAddr (Task1Input.mwCap impl inp.J) inp.J.m := by
  simp only [Task2Input.nodesAddr, Task2Input.queueAddr, Task2Input.eWVertStampAddr,
    Task2Input.procStampAddr, Task2Input.vcongNumAddr, Task2Input.vHeadAddr,
    Task2Input.vhatStampAddr, Task2Input.compEdgeDelRoundAddr, Task2Input.vhatOffsetAddr,
    Task2Input.compEdgeBaseAddr, Task2Input.dsHandlesAddr, Task2Input.embWJAddr]
  omega

lemma t2_nodesEnd_le_maxWord {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length + 3 * inp.embVertSum ≤ inp.maxWordBound impl := by
  have h1 := t2_nodesAddr_le ctx.hmW_le ctx.hK_le
  have h2 : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length + 3 * inp.embVertSum ≤
      inp.staticEndCap impl := by
    dsimp only [Task2Input.staticEndCap]; exact Nat.le_add_right_of_le (Nat.add_le_add_right h1 _)
  have h3 : inp.staticEndCap impl ≤ inp.maxHeapEnd impl := by
    dsimp only [Task2Input.maxHeapEnd]; omega
  have h4 : inp.maxHeapEnd impl ≤ inp.maxWordBound impl := by
    dsimp only [Task2Input.maxWordBound]; exact le_trans (Nat.le_add_right _ 3) (le_max_left _ _)
  omega

lemma t2_prep_cJSub_m_eq {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {ci : ℕ} (hci : ci < ctx.wd.comps.length) :
    let hci_r : ci < ctx.wInp.prep.rawComps.length := by
      have hlen := ctx.wInp.buildCompsFrom_length ctx.wInp.prep.j0Edges.length
        ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1
      simpa [T2Ctx.wd, WitnessCoreInput.mkWitnessData, hlen] using hci
    ctx.wd.comps[ci].J_sub = ctx.wInp.prep.cJSub ctx.wInp.prep.rawComps[ci] ∧
    ctx.wd.comps[ci].jSubOrigEdges = ctx.wInp.prep.cJOrig ctx.wInp.prep.rawComps[ci] ∧
    ctx.wd.comps[ci].X.card = ctx.wInp.prep.rawComps[ci].2.length := by
  have hlen := ctx.wInp.buildCompsFrom_length ctx.wInp.prep.j0Edges.length
    ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1
  have hci_r : ci < ctx.wInp.prep.rawComps.length := by
    simpa [T2Ctx.wd, WitnessCoreInput.mkWitnessData, hlen] using hci
  obtain ⟨_, hX, _, hJsub, hjOrig, _⟩ :=
    ctx.wInp.buildCompsFrom_getElem_full ctx.wInp.prep.j0Edges.length
      ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1 ci hci_r
  have hp := ctx.hstat.2.2.2.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem hci_r)
  have hcard : ctx.wd.comps[ci].X.card = ctx.wInp.prep.rawComps[ci].2.length :=
    (congrArg Finset.card hX).trans (List.toFinset_card_of_nodup (hp.2.2.1.imp fun {_ _} h => Nat.ne_of_lt h))
  exact ⟨hJsub, hjOrig, hcard⟩

lemma t2_prep_chain_bounds {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    inp.t1OutAddr + 6 ≤ ctx.wInp.prep.h ∧
    ctx.wInp.prep.h + 8 ≤ ctx.wInp.prep.aComps ∧
    ctx.wInp.prep.aComps + 7 * ctx.wd.comps.length ≤ ctx.wInp.prep.hEnd ∧
    ctx.wInp.prep.hEnd ≤ inp.v1 := by
  have hlen := ctx.wInp.buildCompsFrom_length ctx.wInp.prep.j0Edges.length
    ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1
  have hk_eq : ctx.wd.comps.length = ctx.wInp.prep.rawComps.length := hlen
  have h0 := ctx.wInp.prep.hBlocksStart_eq
  have h1 := ctx.wInp.prep.cJSubPtr_le_hEnd (Nat.zero_le _)
  have h2 : ctx.wInp.prep.hBlocksStart = ctx.wInp.prep.cJSubPtr 0 :=
    ctx.wInp.prep.cJSubPtr_zero.symm
  have hdec := ctx.hstat.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have := ctx.hw_j0Addr; have := ctx.hw_nlAddr; have := ctx.hw_decAddr
  have := ctx.hhend; have := ctx.hv20
  simp only [PrepInput.aVLoc, PrepInput.aVComp, PrepInput.aComps, PrepInput.aJ0Out,
    PrepInput.aEdgeNext, PrepInput.aLvlHead] at h0 ⊢
  omega

lemma t2_prep_comp_ptrs_le {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) {ci : ℕ} (hci : ci < ctx.wd.comps.length) :
    ctx.wInp.prep.aComps + 7 * ci + 6 < ctx.wInp.prep.hEnd ∧
    ctx.wInp.prep.cJOrigPtr ci + ctx.wd.comps[ci].J_sub.m ≤ ctx.wInp.prep.hEnd := by
  have hlen := ctx.wInp.buildCompsFrom_length ctx.wInp.prep.j0Edges.length
    ctx.wInp.prep.rawComps ctx.WSubs ctx.hws.1
  have hci_r : ci < ctx.wInp.prep.rawComps.length := by
    simpa [T2Ctx.wd, WitnessCoreInput.mkWitnessData, hlen] using hci
  have hc := t2_prep_chain_bounds ctx
  have hsucc : ctx.wInp.prep.cJSubPtr (ci + 1) ≤ ctx.wInp.prep.hEnd :=
    ctx.wInp.prep.cJSubPtr_le_hEnd (by omega)
  have hj_eq := (t2_prep_cJSub_m_eq ctx hci).1
  have hgetD : ctx.wInp.prep.rawComps.getD ci (0, []) = ctx.wInp.prep.rawComps[ci] :=
    List.getD_eq_getElem _ _ hci_r
  have hend : ctx.wInp.prep.cJSubPtr (ci + 1) =
      ctx.wInp.prep.cJOrigPtr ci + (ctx.wInp.prep.cJSub ctx.wInp.prep.rawComps[ci]).m +
        ctx.wInp.prep.rawComps[ci].2.length := by
    rw [ctx.wInp.prep.cJSubPtr_succ hci_r]
    simp only [PrepInput.cEndPtr, PrepInput.cDegPtr, PrepInput.cJOrigPtr, hgetD]
  exact ⟨by omega, by rw [hj_eq]; omega⟩

lemma t2_v1_le_compEdgeBase {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    inp.v1 + 32 ≤ inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length ∧
    inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ctx.wd.comps.length =
      inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length ∧
    inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ctx.wd.comps.length =
      inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length ∧
    inp.compEdgeDelRoundAddr ctx.wd.W.m ctx.wd.comps.length ≤
      inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length ∧
    inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + inp.H'.n ≤
      inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ∧
    2 * inp.J.m ≤ inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ∧
    inp.H'.n ≤ inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length := by
  dsimp only [Task2Input.nodesAddr, Task2Input.queueAddr, Task2Input.eWVertStampAddr,
    Task2Input.procStampAddr, Task2Input.vcongNumAddr, Task2Input.vHeadAddr,
    Task2Input.vhatStampAddr, Task2Input.compEdgeDelRoundAddr, Task2Input.vhatOffsetAddr,
    Task2Input.compEdgeBaseAddr, Task2Input.dsHandlesAddr, Task2Input.embWJAddr]
  exact ⟨by omega, rfl, rfl, by omega, by omega, by omega, by omega⟩

lemma IncChainBound.head_lt {mem : ℕ → ℕ} {lo hi ptr : ℕ} {L : List (ℕ × ℕ)}
    (hc : IncChainBound mem lo hi ptr L) : ptr = 0 ∨ ptr + 3 ≤ hi := by
  cases hc with
  | nil => exact Or.inl rfl
  | cons _ hhi => exact Or.inr hhi

/-- Partial vertex-to-component-edge incidence list invariant parametrized by covered `(ci, b, x)`. -/
def IncListForPairs (mem : ℕ → ℕ) (vHeadAddr nH : ℕ) (comps : List CompInfo)
    (embJH : ℕ → Walk) (nodesAddr nodesPtr : ℕ) (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ L : ℕ → List (ℕ × ℕ),
    (∀ x < nH,
      IncChainBound mem nodesAddr nodesPtr (mem (vHeadAddr + x)) (L x) ∧
      (∀ p ∈ L x, ∃ (hp : p.1 < comps.length), p.2 < comps[p.1].J_sub.m ∧
        x ∈ (embJH (comps[p.1].jSubOrigEdges.getD p.2 0)).verts) ∧
      (∀ ci (hci : ci < comps.length) b (_hb : b < comps[ci].J_sub.m),
        P ci b x → (ci, b) ∈ L x)) ∧
    (∑ x ∈ Finset.range nH, (L x).length) * 3 ≤ nodesPtr - nodesAddr

lemma incListForPairs_init {mem : ℕ → ℕ} {vHeadAddr nH : ℕ} {comps : List CompInfo}
    {embJH : ℕ → Walk} {nodesAddr : ℕ}
    (hzero : ∀ x < nH, mem (vHeadAddr + x) = 0) :
    IncListForPairs mem vHeadAddr nH comps embJH nodesAddr nodesAddr (fun _ _ _ => False) := by
  refine ⟨fun _ => [], fun x hx => ?_, by simp⟩
  refine ⟨?_, fun p hp => by simp at hp, fun _ _ _ _ hf => False.elim hf⟩
  rw [hzero x hx]; exact .nil

lemma incListForPairs_mono {mem mem' : ℕ → ℕ} {vHeadAddr nH : ℕ} {comps : List CompInfo}
    {embJH : ℕ → Walk} {nodesAddr nodesPtr : ℕ} {P Q : ℕ → ℕ → ℕ → Prop}
    (h : IncListForPairs mem vHeadAddr nH comps embJH nodesAddr nodesPtr P)
    (hHead : ∀ x < nH, mem' (vHeadAddr + x) = mem (vHeadAddr + x))
    (hNodes : ∀ a, nodesAddr ≤ a → a < nodesPtr → mem' a = mem a)
    (hQP : ∀ ci b x, Q ci b x → P ci b x) :
    IncListForPairs mem' vHeadAddr nH comps embJH nodesAddr nodesPtr Q := by
  obtain ⟨L, hL, hsum⟩ := h
  refine ⟨L, fun x hx => ?_, hsum⟩
  obtain ⟨hc, hsub, hmem⟩ := hL x hx
  exact ⟨by rw [hHead x hx]; exact hc.mono hNodes, hsub,
    fun ci hci b hb hq => hmem ci hci b hb (hQP ci b x hq)⟩

lemma incListForPairs_push {mem mem' : ℕ → ℕ} {vHeadAddr nH : ℕ} {comps : List CompInfo}
    {embJH : ℕ → Walk} {nodesAddr nodesPtr : ℕ} {P : ℕ → ℕ → ℕ → Prop}
    {ci₀ b₀ x₀ : ℕ} (hci₀ : ci₀ < comps.length) (hb₀ : b₀ < comps[ci₀].J_sub.m) (hx₀ : x₀ < nH)
    (hx_in : x₀ ∈ (embJH (comps[ci₀].jSubOrigEdges.getD b₀ 0)).verts)
    (hlo : nodesAddr ≤ nodesPtr)
    (hInc : IncListForPairs mem vHeadAddr nH comps embJH nodesAddr nodesPtr P)
    (hm_node0 : mem' nodesPtr = ci₀) (hm_node1 : mem' (nodesPtr + 1) = b₀)
    (hm_node2 : mem' (nodesPtr + 2) = mem (vHeadAddr + x₀))
    (hm_head0 : mem' (vHeadAddr + x₀) = nodesPtr)
    (hm_head_other : ∀ x < nH, x ≠ x₀ → mem' (vHeadAddr + x) = mem (vHeadAddr + x))
    (hm_nodes_old : ∀ a, nodesAddr ≤ a → a < nodesPtr → mem' a = mem a) :
    IncListForPairs mem' vHeadAddr nH comps embJH nodesAddr (nodesPtr + 3)
      (fun ci b x => P ci b x ∨ (ci = ci₀ ∧ b = b₀ ∧ x = x₀)) := by
  classical
  obtain ⟨L, hL, hsum⟩ := hInc
  let L' := Function.update L x₀ ((ci₀, b₀) :: L x₀)
  refine ⟨L', fun x hx => ?_, ?_⟩
  · obtain ⟨hc, hsub, hmem⟩ := hL x hx
    by_cases hxx₀ : x = x₀
    · subst hxx₀
      simp only [L', Function.update_self]
      refine ⟨?_, ?_, ?_⟩
      · rw [hm_head0]
        exact .cons hlo (le_refl _) hm_node0 hm_node1 hm_node2
          ((hc.mono hm_nodes_old).weaken (le_refl _) (by omega))
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hrest
        · exact ⟨hci₀, hb₀, hx_in⟩
        · exact hsub p hrest
      · intro ci hci b hb hor
        rcases hor with hp | ⟨rfl, rfl, _⟩
        · exact List.mem_cons_of_mem _ (hmem ci hci b hb hp)
        · exact List.mem_cons_self
    · simp only [L', Function.update_of_ne hxx₀]
      refine ⟨?_, hsub, fun ci hci b hb hor => ?_⟩
      · rw [hm_head_other x hx hxx₀]
        exact (hc.mono hm_nodes_old).weaken (le_refl _) (by omega)
      · rcases hor with hp | ⟨_, _, heq⟩
        · exact hmem ci hci b hb hp
        · exact False.elim (hxx₀ heq)
  · have hx₀_mem : x₀ ∈ Finset.range nH := Finset.mem_range.mpr hx₀
    have hsum_eq : ∑ x ∈ Finset.range nH, (L' x).length =
        (∑ x ∈ Finset.range nH, (L x).length) + 1 := by
      rw [← Finset.add_sum_erase (Finset.range nH) (fun x => (L' x).length) hx₀_mem,
          ← Finset.add_sum_erase (Finset.range nH) (fun x => (L x).length) hx₀_mem]
      have hrest : ∑ x ∈ (Finset.range nH).erase x₀, (L' x).length =
          ∑ x ∈ (Finset.range nH).erase x₀, (L x).length :=
        Finset.sum_congr rfl fun x hx => by
          dsimp only [L']; rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
      rw [hrest]; dsimp only [L']; rw [Function.update_self, List.length_cons]; omega
    omega

lemma incListForPairs_to_incListAt {mem : ℕ → ℕ} {vHeadAddr nH : ℕ} {comps : List CompInfo}
    {embJH : ℕ → Walk} {nodesAddr nodesEnd : ℕ}
    (h : IncListForPairs mem vHeadAddr nH comps embJH nodesAddr nodesEnd
      (fun ci b x => ∃ hci : ci < comps.length, b < comps[ci].J_sub.m ∧
        x ∈ (embJH (comps[ci].jSubOrigEdges.getD b 0)).verts)) :
    IncListAt mem vHeadAddr nH comps embJH nodesAddr nodesEnd := by
  obtain ⟨L, hL, hsum⟩ := h
  refine ⟨L, fun x hx => ?_, hsum⟩
  obtain ⟨hc, hsub, hmem⟩ := hL x hx
  exact ⟨hc, hsub, fun ci hci b hb hxin => hmem ci hci b hb ⟨hci, hb, hxin⟩⟩

/-- Disjoint memory frame preserved by `t2BuildIncBody`. -/
def T2BuildIncFrame {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (memStart mem : ℕ → ℕ) : Prop :=
  let mW := ctx.wd.W.m
  let K := ctx.wd.comps.length
  ∀ a, (a < inp.compEdgeBaseAddr mW K ∨
      (inp.compEdgeDelRoundAddr mW K ≤ a ∧ a < inp.vHeadAddr mW K) ∨
      (inp.vHeadAddr mW K + inp.H'.n ≤ a ∧ a < inp.nodesAddr mW K)) →
    mem a = memStart a

lemma t2BuildIncFrame_upd_compEdgeBase {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) {memStart mem : ℕ → ℕ} {ci v : ℕ}
    (h : T2BuildIncFrame ctx memStart mem) (hci : ci < ctx.wd.comps.length) :
    T2BuildIncFrame ctx memStart
      (Function.update mem (inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ci) v) := by
  intro a ha
  have hne : a ≠ inp.compEdgeBaseAddr ctx.wd.W.m ctx.wd.comps.length + ci := by
    have := t2_v1_le_compEdgeBase ctx; omega
  rw [Function.update_of_ne hne]; exact h a ha

lemma t2BuildIncFrame_upd_vhatOffset {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) {memStart mem : ℕ → ℕ} {ci v : ℕ}
    (h : T2BuildIncFrame ctx memStart mem) (hci : ci < ctx.wd.comps.length) :
    T2BuildIncFrame ctx memStart
      (Function.update mem (inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci) v) := by
  intro a ha
  have hne : a ≠ inp.vhatOffsetAddr ctx.wd.W.m ctx.wd.comps.length + ci := by
    have := t2_v1_le_compEdgeBase ctx; omega
  rw [Function.update_of_ne hne]; exact h a ha

lemma t2BuildIncFrame_upd_vHead {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) {memStart mem : ℕ → ℕ} {x v : ℕ}
    (h : T2BuildIncFrame ctx memStart mem) (hx : x < inp.H'.n) :
    T2BuildIncFrame ctx memStart
      (Function.update mem (inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x) v) := by
  intro a ha
  have hne : a ≠ inp.vHeadAddr ctx.wd.W.m ctx.wd.comps.length + x := by
    have := t2_v1_le_compEdgeBase ctx; omega
  rw [Function.update_of_ne hne]; exact h a ha

lemma t2BuildIncFrame_upd_node {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) {memStart mem : ℕ → ℕ} {ptr v : ℕ}
    (h : T2BuildIncFrame ctx memStart mem)
    (hptr : inp.nodesAddr ctx.wd.W.m ctx.wd.comps.length ≤ ptr) :
    T2BuildIncFrame ctx memStart (Function.update mem ptr v) := by
  intro a ha
  have hne : a ≠ ptr := by
    have := t2_v1_le_compEdgeBase ctx; omega
  rw [Function.update_of_ne hne]; exact h a ha

/-- Sum of `verts.length` over component prefix `0 .. ci - 1` and edge prefix `0 .. b - 1` of component `ci`. -/
def t2PrefixVerts (comps : List CompInfo) (embJH : ℕ → Walk) (ci b : ℕ) : ℕ :=
  (∑ c ∈ Finset.range ci,
    ∑ b' ∈ Finset.range (comps.getD c defaultCompInfo).J_sub.m,
      (embJH ((comps.getD c defaultCompInfo).jSubOrigEdges.getD b' 0)).verts.length) +
  ∑ b' ∈ Finset.range b,
    (embJH ((comps.getD ci defaultCompInfo).jSubOrigEdges.getD b' 0)).verts.length

lemma t2PrefixVerts_add_j {comps : List CompInfo} {embJH : ℕ → Walk}
    {ci b j : ℕ} (hci : ci < comps.length)
    (hj : j ≤ (embJH (comps[ci].jSubOrigEdges.getD b 0)).verts.length) :
    t2PrefixVerts comps embJH ci b + j ≤ t2PrefixVerts comps embJH ci (b + 1) := by
  simp only [t2PrefixVerts, Finset.sum_range_succ, List.getD_eq_getElem _ _ hci]
  omega

lemma t2PrefixVerts_comp_end {comps : List CompInfo} {embJH : ℕ → Walk}
    {ci : ℕ} (hci : ci < comps.length) :
    t2PrefixVerts comps embJH ci comps[ci].J_sub.m = t2PrefixVerts comps embJH (ci + 1) 0 := by
  simp only [t2PrefixVerts, Finset.sum_range_zero, add_zero, Finset.sum_range_succ,
    List.getD_eq_getElem _ _ hci]

lemma t2_inc_vertSum_le_ctx {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) :
    ∑ ci ∈ Finset.range ctx.wd.comps.length,
      ∑ b ∈ Finset.range (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m,
        (inp.embJH ((ctx.wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)).verts.length ≤
      inp.embVertSum := by
  have hv := t2_inc_vertSum_le ctx.hw_okW
  rw [ctx.hWInpJ] at hv
  have heq : ∑ ci ∈ Finset.range ctx.wd.comps.length,
        ∑ b ∈ Finset.range (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m,
          (inp.embJH ((ctx.wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)).verts.length =
      ∑ ci ∈ Finset.range ctx.wd.comps.length,
        ∑ b ∈ Finset.range (ctx.wd.comps.getD ci defaultCompInfo).J_sub.m,
          (ctx.wInp.embJH ((ctx.wd.comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)).verts.length := by
    refine Finset.sum_congr rfl fun ci hci_r => Finset.sum_congr rfl fun b hb_r => ?_
    have hci := Finset.mem_range.mp hci_r
    have hg : ctx.wd.comps.getD ci defaultCompInfo = ctx.wd.comps[ci] :=
      List.getD_eq_getElem _ _ hci
    have hb : b < ctx.wd.comps[ci].J_sub.m := by rw [← hg]; exact Finset.mem_range.mp hb_r
    have hprops := ctx.hw_okW.comp_props ci hci
    have ho : b < ctx.wd.comps[ci].jSubOrigEdges.length := by
      rw [hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact hb
    have heJ : (ctx.wd.comps[ci].jSubOrigEdges.getD b 0) < inp.J.m := by
      rw [List.getD_eq_getElem _ _ ho, ← ctx.hWInpJ]
      exact hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (List.getElem_mem ho)
    rw [hg, ctx.hWInpEmb _ heJ]
  have hrhs : ∑ eJ ∈ Finset.range inp.J.m, (ctx.wInp.embJH eJ).verts.length = inp.embVertSum :=
    Finset.sum_congr rfl fun eJ heJ =>
      congrArg (fun w => w.verts.length) (ctx.hWInpEmb eJ (Finset.mem_range.mp heJ))
  rw [hrhs] at hv; rw [heq]; exact hv

lemma t2PrefixVerts_le_embVertSum {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T2Ctx impl inp mem₀ w) {ci : ℕ} (hci : ci ≤ ctx.wd.comps.length) :
    t2PrefixVerts ctx.wd.comps inp.embJH ci 0 ≤ inp.embVertSum := by
  simp only [t2PrefixVerts, Finset.sum_range_zero, add_zero]
  have hsub : ∑ c ∈ Finset.range ci,
      ∑ b' ∈ Finset.range (ctx.wd.comps.getD c defaultCompInfo).J_sub.m,
        (inp.embJH ((ctx.wd.comps.getD c defaultCompInfo).jSubOrigEdges.getD b' 0)).verts.length ≤
      ∑ c ∈ Finset.range ctx.wd.comps.length, _ :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hci)
  exact le_trans hsub (t2_inc_vertSum_le_ctx ctx)

def t2DonePred (comps : List CompInfo) (embJH : ℕ → Walk)
    (ciBound bBound jBound : ℕ) (ci b x : ℕ) : Prop :=
  (ci < ciBound ∧ b < (comps.getD ci defaultCompInfo).J_sub.m ∧
    x ∈ (embJH ((comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)).verts) ∨
  (ci = ciBound ∧ b < bBound ∧
    x ∈ (embJH ((comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)).verts) ∨
  (ci = ciBound ∧ b = bBound ∧ ∃ j < jBound,
    (embJH ((comps.getD ci defaultCompInfo).jSubOrigEdges.getD b 0)).verts[j]? = some x)

lemma t2DonePred_succ_j {comps : List CompInfo} {embJH : ℕ → Walk}
    {ci b j ci' b' x x' : ℕ} (hci : ci < comps.length)
    (hj_val : (embJH (comps[ci].jSubOrigEdges.getD b 0)).verts[j]? = some x)
    (h : t2DonePred comps embJH ci b (j + 1) ci' b' x') :
    t2DonePred comps embJH ci b j ci' b' x' ∨ (ci' = ci ∧ b' = b ∧ x' = x) := by
  rcases h with h1 | h2 | ⟨rfl, rfl, k, hk, hvk⟩
  · exact Or.inl (Or.inl h1)
  · exact Or.inl (Or.inr (Or.inl h2))
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
    · exact Or.inl (Or.inr (Or.inr ⟨rfl, rfl, k, hlt, hvk⟩))
    · rw [List.getD_eq_getElem _ _ hci, hj_val, Option.some.injEq] at hvk
      exact Or.inr ⟨rfl, rfl, hvk.symm⟩

lemma t2DonePred_b_step {comps : List CompInfo} {embJH : ℕ → Walk} {ci b ci' b' x' : ℕ}
    (hci : ci < comps.length)
    (h : t2DonePred comps embJH ci (b + 1) 0 ci' b' x') :
    t2DonePred comps embJH ci b (embJH (comps[ci].jSubOrigEdges.getD b 0)).verts.length ci' b' x' := by
  rcases h with h1 | ⟨rfl, hb', hmem⟩ | ⟨rfl, _, k, hk, _⟩
  · exact Or.inl h1
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hb') with hlt | rfl
    · exact Or.inr (Or.inl ⟨rfl, hlt, hmem⟩)
    · have hg : comps.getD ci' defaultCompInfo = comps[ci'] := List.getD_eq_getElem _ _ hci
      rw [hg] at hmem
      obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hmem
      refine Or.inr (Or.inr ⟨rfl, rfl, j, hj, ?_⟩)
      rw [hg, List.getElem?_eq_getElem hj, hget]
  · omega

lemma t2DonePred_ci_step {comps : List CompInfo} {embJH : ℕ → Walk} {ci ci' b' x' : ℕ}
    (hci : ci < comps.length)
    (h : t2DonePred comps embJH (ci + 1) 0 0 ci' b' x') :
    t2DonePred comps embJH ci comps[ci].J_sub.m 0 ci' b' x' := by
  rcases h with ⟨hci', hb', hmem⟩ | ⟨rfl, hb', _⟩ | ⟨rfl, _, k, hk, _⟩
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hci') with hlt | rfl
    · exact Or.inl ⟨hlt, hb', hmem⟩
    · have hg : comps.getD ci' defaultCompInfo = comps[ci'] := List.getD_eq_getElem _ _ hci
      exact Or.inr (Or.inl ⟨rfl, by rwa [← hg], hmem⟩)
  · omega
  · omega

/-- Loop invariant for `t2BuildIncBody` covering outer (`ci`), middle (`b`), and inner (`j`) loops. -/
def T2IncInv {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (memStart : ℕ → ℕ)
    (writtenUpTo ci b j : ℕ) (st : State) : Prop :=
  let mW := ctx.wd.W.m
  let K := ctx.wd.comps.length
  let nodesAddr := inp.nodesAddr mW K
  st.regs 0 = inp.v1 ∧
  st.regs 2 = ctx.wInp.prep.h ∧
  st.regs 3 = K ∧
  st.regs 4 = ctx.wInp.prep.aComps ∧
  st.regs 5 = inp.compEdgeBaseAddr mW K ∧
  st.regs 6 = inp.vhatOffsetAddr mW K ∧
  st.regs 7 = inp.embJHAddr ∧
  st.regs 8 = inp.vHeadAddr mW K ∧
  st.regs 9 = compEdgeBase ctx.wd writtenUpTo ∧
  st.regs 10 = vhatBase ctx.wd writtenUpTo ∧
  nodesAddr ≤ st.regs 11 ∧
  st.regs 11 ≤ nodesAddr + 3 * (t2PrefixVerts ctx.wd.comps inp.embJH ci b + j) ∧
  ZeroFrom st.mem (st.regs 11) ∧
  T2BuildIncFrame ctx memStart st.mem ∧
  (∀ c < writtenUpTo,
    st.mem (inp.compEdgeBaseAddr mW K + c) = compEdgeBase ctx.wd c) ∧
  (∀ c < writtenUpTo,
    st.mem (inp.vhatOffsetAddr mW K + c) = vhatBase ctx.wd c) ∧
  IncListForPairs st.mem (inp.vHeadAddr mW K) inp.H'.n ctx.wd.comps inp.embJH nodesAddr
    (st.regs 11) (t2DonePred ctx.wd.comps inp.embJH ci b j)

end MinCostFlow.Spanner
