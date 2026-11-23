module

public import MinCostFlow.Spanner.ProgTask2SetupProof
public import MinCostFlow.Spanner.ProgTask2RoundProof

@[expose] public section

/-!
# Full Verification of `task2Module` Against `task2Contract`

Builds `T2Ctx` from `Task2Input.Valid`, proves the `Stmt.loop` invariant over rounds via
`PTriple.loop_inv`, `t2Round_bound_of_unembedded`, and `task2Round_triple`, verifies the epilogue
and `Task2OutAt`, proves contract uniqueness for `task2Contract`, and concludes
`task2_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM

private lemma finset_fold_max_real_le {α : Type*} (z b : ℝ) (f : α → ℝ) (s : Finset α)
    (hz : z ≤ b) (hf : ∀ x ∈ s, f x ≤ b) : Finset.fold max z f s ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hz
  | insert a s' ha ih =>
    rw [Finset.fold_insert ha]
    exact max_le (hf a (Finset.mem_insert_self a s')) (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

private lemma finset_fold_max_nat_cast_le {α : Type*} (b : ℝ) (f : α → ℕ) (s : Finset α)
    (hb : 0 ≤ b) (hf : ∀ x ∈ s, (f x : ℝ) ≤ b) : ((Finset.fold max (0 : ℕ) f s : ℕ) : ℝ) ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hb
  | insert a s' ha ih =>
    rw [Finset.fold_insert ha, Nat.cast_max]
    exact max_le (hf a (Finset.mem_insert_self a s')) (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

private lemma t2_composeAux_congr {B B' : Cited.Graph} {f f' : ℕ → Walk}
    {vs es : List ℕ} (hB : B = B') (hf : ∀ e ∈ es, f e = f' e) :
    composeAux B f vs es = composeAux B' f' vs es := by
  subst hB
  induction vs generalizing es with
  | nil =>
    rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ h _ => by cases h)]
    rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ h _ => by cases h)]
  | cons u rest ih =>
    cases rest with
    | nil =>
      rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ h _ => by cases h)]
      rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ h _ => by cases h)]
    | cons v vs' =>
      cases es with
      | nil =>
        rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ _ h => by cases h)]
        rw [composeAux.eq_2 _ _ _ _ (fun _ _ _ _ _ _ h => by cases h)]
      | cons j js =>
        rw [composeAux.eq_1, composeAux.eq_1, hf j List.mem_cons_self,
          ih (fun e he => hf e (List.mem_cons_of_mem j he))]

/-- Constructs `T2Ctx` from `Task2Input.Valid`. -/
noncomputable def t2CtxOfValid {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid impl mem₀ w) : T2Ctx impl inp mem₀ w :=
  let hH' := hv.1
  let hgH' := hv.2.1
  let hJ := hv.2.2.1
  let hgJ := hv.2.2.2.1
  let hembJH := hv.2.2.2.2.1
  let hEmbAt := hv.2.2.2.2.2.1
  let hEmbBd := hv.2.2.2.2.2.2.1
  let hH'_le := hv.2.2.2.2.2.2.2.1
  let hJ_le := hv.2.2.2.2.2.2.2.2.1
  let hT1 := hv.2.2.2.2.2.2.2.2.2.1
  let hww := hv.2.2.2.2.2.2.2.2.2.2
  let ht1_spec := Classical.choose_spec hT1
  let wInp := Classical.choose ht1_spec
  let ht1_w := Classical.choose_spec ht1_spec
  let WSubs := Classical.choose ht1_w
  let hs := Classical.choose_spec ht1_w
  { wInp := wInp
    WSubs := WSubs
    hWInpH' := hs.1
    hWInpEmb := hs.2.1
    hWInpJ := hs.2.2.1
    hWInpJAddr := hs.2.2.2.1
    hH' := hH'
    hgH' := hgH'
    hJ := hJ
    hgJ := hgJ
    hembJH := hembJH
    hEmbAt := hEmbAt
    hEmbBd := hEmbBd
    hH'_le := hH'_le
    hJ_le := hJ_le
    ht1_0 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    ht1_1 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    ht1_2 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    ht1_3 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    ht1_4 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    ht1_5 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hw_j0Addr := hs.2.2.2.2.2.1
    hw_nlAddr := hs.2.2.2.2.2.2.1
    hw_decAddr := hs.2.2.2.2.2.2.2.1
    hpst := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hcdt := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hstat := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hws := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hφ_lb := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hφ_cap := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hout := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (fun _ => 0)
    hw_ok := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hhend := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    hz0 := hs.2.2.2.2.2.2.2.2.2.2.1
    hv20 := hs.2.2.2.2.2.2.2.2.2.2.2.1
    hww := hww }

structure T2LoopIdx where
  r_done : ℕ
  emb_prev : ℕ → Option Walk
  emb : ℕ → Option Walk
  hCur : ℕ
  arenaPtr : ℕ
  del0 : ℕ
  upd0 : ℕ
  inn0 : ℕ

noncomputable def t2RoundBound (impl : SpannerToolImpl) (inp : Task2Input) : ℕ :=
  let γJ := impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m
  inp.J.m * ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊ +
    inp.J.m * ⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊ +
    261 * inp.J.m + 69 * Task1Input.mwCap impl inp.J + 45 * inp.embVertSum + 60

/-- Verifies `Stmt.loop (.reg 19) (t2RoundBody selfBase dsBase)` from `r_done = 0`. -/
lemma t2Loop_ptriple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task2Input} {mem₀ : ℕ → ℕ} (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx)
    {selfBase dsBase : ℕ}
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (hp_mid : p.procs[selfBase + 3]? = some (t2MiddleEdgeBody dsBase (selfBase + 4)))
    (hp_drain : p.procs[selfBase + 4]? = some (t2DrainQueueBody dsBase)) :
    let a₀ : T2LoopIdx :=
      ⟨0, initEmb0 ctx.wInp, initEmb0 ctx.wInp, stc.dsBaseAddr,
        stc.nodesEnd + 5 * ctx.wd.j0Edges.length, 0, 0, 0⟩
    let B := t2RoundBound impl inp
    PTriple w p
      (fun st Φ =>
        T2LoopState ctx stc a₀.r_done a₀.emb_prev a₀.emb a₀.hCur a₀.arenaPtr a₀.del0 a₀.upd0 a₀.inn0 st ∧
          Φ = (unembeddedSetPure ctx.wd a₀.emb).card * t2EdgeBudget impl inp)
      (Stmt.loop (.reg 19) (t2RoundBody selfBase dsBase))
      (pNormalPost fun st' Φ' =>
        ∃ (a : T2LoopIdx),
          T2LoopState ctx stc a.r_done a.emb_prev a.emb a.hCur a.arenaPtr a.del0 a.upd0 a.inn0 st' ∧
          1 ≤ a.r_done ∧
          a.r_done ≤ eta1Bound ctx.wd inp.J ∧
          (unembeddedSetPure ctx.wd a.emb).card = 0 ∧
          Φ' = (unembeddedSetPure ctx.wd a.emb).card * t2EdgeBudget impl inp)
      (fun _ => eta1Bound ctx.wd inp.J * (B + 3) + 2) := by
  intro a₀ B
  let Inv : T2LoopIdx → State → ℕ → Prop := fun a st Φ =>
    T2LoopState ctx stc a.r_done a.emb_prev a.emb a.hCur a.arenaPtr a.del0 a.upd0 a.inn0 st ∧
      a.r_done ≤ eta1Bound ctx.wd inp.J ∧
      Φ = (unembeddedSetPure ctx.wd a.emb).card * t2EdgeBudget impl inp
  let Q : Outcome → State → ℕ → Prop := pNormalPost fun st' Φ' =>
    ∃ (a : T2LoopIdx),
      T2LoopState ctx stc a.r_done a.emb_prev a.emb a.hCur a.arenaPtr a.del0 a.upd0 a.inn0 st' ∧
      1 ≤ a.r_done ∧
      a.r_done ≤ eta1Bound ctx.wd inp.J ∧
      (unembeddedSetPure ctx.wd a.emb).card = 0 ∧
      Φ' = (unembeddedSetPure ctx.wd a.emb).card * t2EdgeBudget impl inp
  let m : T2LoopIdx → ℕ := fun a => eta1Bound ctx.wd inp.J - a.r_done
  let rem : T2LoopIdx → ℕ := fun a => (eta1Bound ctx.wd inp.J - a.r_done) * (B + 3) + 2
  have hloop := PTriple.loop_inv (w := w) (p := p) (e := .reg 19) (body := t2RoundBody selfBase dsBase)
    (Inv := Inv) (Q := Q) (m := m) (rem := rem) (condVal := fun st => st.regs 19)
    (fun _ st _ _ => Expr.eval_reg w 19 st)
    (fun a st Φ ⟨hLS, hEta, hΦ⟩ hcond0 => by
      have hcard0 : 1 ≤ a.r_done ∧ (unembeddedSetPure ctx.wd a.emb).card = 0 := by
        have hr19 := hLS.hr19
        rw [hcond0] at hr19
        by_cases hr0 : a.r_done = 0
        · simp [hr0] at hr19
        · simp [hr0] at hr19
          exact ⟨Nat.pos_of_ne_zero hr0, hr19.symm⟩
      exact ⟨⟨a, hLS, hcard0.1, hEta, hcard0.2, hΦ⟩, by dsimp only [rem, Expr.size]; omega⟩)
    (fun a st Φ ⟨hLS, hEta, hΦ⟩ hne => by
      have hEta_succ : a.r_done + 1 ≤ eta1Bound ctx.wd inp.J := by
        by_cases hr0 : a.r_done = 0
        · rw [hr0, Nat.zero_add]; unfold eta1Bound; exact Nat.le_add_right 1 _
        · have hcard_pos : (unembeddedSetPure ctx.wd a.emb).Nonempty := by
            have hr19 := hLS.hr19
            simp [hr0] at hr19
            exact Finset.card_pos.mp (Nat.pos_of_ne_zero (hr19 ▸ hne))
          have hvol := hLS.hVol_cur
          rw [← ctx.hWInpJ] at hvol
          have hlt := t2Round_bound_of_unembedded ctx.hw_okW ctx.hws hLS.hj0 hcard_pos hvol
          rw [ctx.hWInpJ] at hlt
          exact Nat.le_of_lt hlt
      refine ⟨B, ?_⟩
      have hround := task2Round_triple ctx stc hSpec hp_mid hp_drain
        a.r_done a.emb_prev a.emb a.hCur a.arenaPtr a.del0 a.upd0 a.inn0 hEta_succ
      intro s Φ' ω' ⟨rfl, rfl⟩
      obtain ⟨o_r, st_r, c_r, Φ_r, hr_r, hq_r, hc_r⟩ := hround s Φ' ω' ⟨hLS, hΦ⟩
      cases o_r with
      | returned _ => exact absurd hq_r (by simp)
      | normal =>
        rcases hq_r with ⟨emb', hCur', arenaPtr', del', upd', inn', hLS', hΦ_r⟩
        let a' : T2LoopIdx := ⟨a.r_done + 1, a.emb, emb', hCur', arenaPtr', del', upd', inn'⟩
        have hm_lt : m a' < m a := by dsimp only [m, a']; omega
        have hrem_le : (Expr.reg 19).size + B + rem a' + 1 ≤ rem a := by
          dsimp only [rem, a', Expr.size]
          have hsplit : eta1Bound ctx.wd inp.J - a.r_done =
              (eta1Bound ctx.wd inp.J - (a.r_done + 1)) + 1 := by omega
          rw [hsplit, Nat.add_mul, Nat.one_mul]
          omega
        exact ⟨.normal, st_r, c_r, Φ_r, hr_r, ⟨a', ⟨hLS', hEta_succ, hΦ_r⟩, hm_lt, hrem_le⟩, hc_r⟩)
    a₀
  refine PTriple.conseq hloop ?_ (fun o st' Φ' hq => hq) ?_
  · intro st Φ ⟨hLS, hΦ⟩; exact ⟨hLS, Nat.zero_le _, hΦ⟩
  · intro st Φ _; dsimp only [rem, a₀]; rw [Nat.sub_zero]

private lemma t2_final_heap_le {impl : SpannerToolImpl} {inp : Task2Input} {stcBase : ℕ}
    {r_done K del W_m : ℕ}
    (hBase : stcBase ≤ Task2Input.staticEndCap impl inp)
    (hEta : r_done ≤ Task2Input.eta1Cap impl inp.J) (hK : K ≤ inp.J.m)
    (hDel : del ≤ r_done * inp.J.m) (hW : W_m ≤ Task1Input.mwCap impl inp.J) :
    stcBase + (r_done * K + del + W_m) * t2DsOne impl inp.J ≤ Task2Input.maxHeapEnd impl inp := by
  have hk : r_done * K ≤ Task2Input.eta1Cap impl inp.J * inp.J.m := Nat.mul_le_mul hEta hK
  have hd : del ≤ Task2Input.eta1Cap impl inp.J * inp.J.m := le_trans hDel (Nat.mul_le_mul_right _ hEta)
  unfold Task2Input.maxHeapEnd
  change stcBase + (r_done * K + del + W_m) * t2DsOne impl inp.J ≤
    Task2Input.staticEndCap impl inp + Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
      Task2Input.eta1Cap impl inp.J * inp.J.m * t2DsOne impl inp.J +
      Task1Input.mwCap impl inp.J * t2DsOne impl inp.J
  nlinarith

/-- Builds `Task2OutAt` after storing `hCur` at `inp.v1 + 11` and exiting the round loop. -/
lemma t2Exit_to_task2OutAt {impl : SpannerToolImpl} {inp : Task2Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T2Ctx impl inp mem₀ w) (stc : T2StaticData ctx) {r_done : ℕ}
    {emb_prev emb : ℕ → Option Walk} {hCur arenaPtr del upd inn : ℕ} {st : State}
    (hLS : T2LoopState ctx stc r_done emb_prev emb hCur arenaPtr del upd inn st)
    (h1_le : 1 ≤ r_done) (hEta : r_done ≤ eta1Bound ctx.wd inp.J)
    (hcard0 : (unembeddedSetPure ctx.wd emb).card = 0) :
    let mem' := Function.update st.mem (inp.v1 + 11) hCur
    Task2OutAt impl inp mem₀ mem' hCur w ∧ hCur ≤ Task2Input.maxHeapEnd impl inp := by
  intro mem'
  have db := drain_bounds ctx stc
  have hm := t2_maxWord_scalars ctx stc
  have hEtaCap : r_done ≤ Task2Input.eta1Cap impl inp.J :=
    le_trans hEta (t2_eta1Bound_le_eta1Cap ctx)
  have hCur_max : hCur ≤ Task2Input.maxHeapEnd impl inp := by
    have h1 := t2_final_heap_le (impl := impl) (inp := inp) db.h_dsc hEtaCap ctx.hK_le hLS.hDel_le ctx.hmW_le
    have h2 := hLS.hCur_le
    have hsub : ctx.wd.W.m - ctx.wd.j0Edges.length - (unembeddedSetPure ctx.wd emb).card ≤ ctx.wd.W.m := by
      omega
    have h3 : (r_done * ctx.wd.comps.length + del +
          (ctx.wd.W.m - ctx.wd.j0Edges.length - (unembeddedSetPure ctx.wd emb).card)) * t2DsOne impl inp.J ≤
        (r_done * ctx.wd.comps.length + del + ctx.wd.W.m) * t2DsOne impl inp.J :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_left hsub _)
    exact le_trans h2 (le_trans (Nat.add_le_add_left h3 _) h1)
  refine ⟨?_, hCur_max⟩
  have hAgr : ∀ x < inp.v1, mem' x = mem₀ x := fun x hx => by
    have hne : x ≠ inp.v1 + 11 := by omega
    simp only [mem', Function.update_of_ne hne]; exact hLS.agr_pre x hx
  have hStat := (ctx.agrees_preserves_static hAgr).2.2.2.2.2.2.1
  have hZf : ZeroFrom mem' hCur := fun a ha => by
    have hne : a ≠ inp.v1 + 11 := by have := hm.1; have := hLS.hCur_lo; omega
    simp only [mem', Function.update_of_ne hne]; exact hLS.hzf a ha
  have hall_emb : ∀ eW < ctx.wd.W.m, ∃ P, emb eW = some P := fun eW heW => by
    have hnot : eW ∉ unembeddedSetPure ctx.wd emb := by
      rw [Finset.card_eq_zero.mp hcard0]; exact Finset.notMem_empty _
    simp only [unembeddedSetPure, Finset.mem_filter, Finset.mem_range] at hnot
    cases he : emb eW with
    | none => exfalso; exact hnot ⟨heW, by simp [he]⟩
    | some P => exact ⟨P, rfl⟩
  have har_ds : arenaPtr ≤ stc.dsBaseAddr := by
    have hsum : ctx.wd.j0Edges.length + (ctx.wd.W.m - ctx.wd.j0Edges.length - (unembeddedSetPure ctx.wd emb).card) ≤
        ctx.wd.W.m := by
      have := ctx.hw_okW.W_m_eq; omega
    have hmul := Nat.mul_le_mul_right (2 * ctx.wInp.γExpInt impl.constructExpander impl.pathDS.params + 5) hsum
    have h1 := hLS.hAr_le
    dsimp only [T2StaticData.dsBaseAddr]
    exact le_trans h1 (Nat.add_le_add_left hmul _)
  have hEmbAt : EmbAt mem' inp.embWJAddr ctx.wd.W.m (partialToWalk emb) := by
    intro eW heW
    obtain ⟨P, heP⟩ := hall_emb eW heW
    have hinv := hLS.hEmb eW heW
    simp only [heP] at hinv
    rcases hinv with ⟨hlo, hhi, hwk⟩
    have hpt_eq : mem' (inp.embWJAddr + eW) = st.mem (inp.embWJAddr + eW) := by
      have hne : inp.embWJAddr + eW ≠ inp.v1 + 11 := by have := db.e_v1; omega
      simp [mem', Function.update_of_ne hne]
    rw [hpt_eq]
    simp only [partialToWalk, heP]
    intro i hi
    have hne : st.mem (inp.embWJAddr + eW) + i ≠ inp.v1 + 11 := by
      have := db.e_v1; have := db.e_emb; have := db.e_hdl; have := db.e_ceb; have := db.e_vho
      have := db.e_del; have := db.e_vh; have := db.e_vhd; have := db.e_vc; have := db.e_ps
      have := db.e_ew; have := db.e_q; have := db.h_nlo; omega
    simp only [mem', Function.update_of_ne hne]
    exact hwk i hi
  have hEmbBd : EmbBounded mem' inp.embWJAddr ctx.wd.W.m (partialToWalk emb) hCur := by
    refine ⟨?_, fun eW heW => ?_⟩
    · have : inp.embWJAddr + ctx.wd.W.m ≤ inp.dsHandlesAddr ctx.wd.W.m := by rw [← db.e_emb]
      have := hm.2.1; have := hLS.hCur_lo; omega
    · obtain ⟨P, heP⟩ := hall_emb eW heW
      have hinv := hLS.hEmb eW heW
      simp only [heP] at hinv
      have hpt_eq : mem' (inp.embWJAddr + eW) = st.mem (inp.embWJAddr + eW) := by
        have hne : inp.embWJAddr + eW ≠ inp.v1 + 11 := by have := db.e_v1; omega
        simp [mem', Function.update_of_ne hne]
      rw [hpt_eq]
      simp only [partialToWalk, heP]
      exact le_trans hinv.2.1 (le_trans har_ds hLS.hCur_lo)
  have hIsEmb : IsEmbedding ctx.wd.W inp.J (partialToWalk emb) := by
    refine ⟨hLS.hPart.1, fun eW heW => ?_⟩
    obtain ⟨P, heP⟩ := hall_emb eW heW
    simp only [partialToWalk, heP]
    exact hLS.hPart.2 eW heW P heP
  have hVcong : vcong ctx.wd.W inp.H' ctx.wd.wW (compose inp.J inp.embJH (partialToWalk emb)) ≤
      ((r_done : ℝ) + 1 / 2) * ctx.wd.τ₁ := by
    apply finset_fold_max_real_le
    · have hτ := ctx.hw_okW.τ₁_nonneg; positivity
    · intro x hx
      exact hLS.hVc_cur x (Finset.mem_range.mp hx)
  have hVcong_bd : vcong ctx.wd.W inp.H' ctx.wd.wW (compose inp.J inp.embJH (partialToWalk emb)) ≤
      ((eta1Bound ctx.wd inp.J : ℝ) + 1 / 2) * ctx.wd.τ₁ := by
    refine le_trans hVcong (mul_le_mul_of_nonneg_right ?_ ctx.hw_okW.τ₁_nonneg)
    have : (r_done : ℝ) ≤ (eta1Bound ctx.wd inp.J : ℝ) := by exact_mod_cast hEta
    linarith
  have hLen : (length ctx.wd.W (partialToWalk emb) : ℝ) ≤ ctx.wd.γ_ExpPath := by
    have hpos_φ := ctx.hw_okW.φ_ds_pos
    have hγ_nn : 0 ≤ ctx.wd.γ_ExpPath := le_trans (by positivity) ctx.hw_okW.γ_ExpPath_ge
    apply finset_fold_max_nat_cast_le _ _ _ hγ_nn
    intro eW heW
    exact hLS.hELen eW (Finset.mem_range.mp heW)
  have hslots := hLS.h_v1_slots
  have hslot_eq : ∀ k ≤ 10, mem' (inp.v1 + k) = st.mem (inp.v1 + k) := fun k hk => by
    simp only [mem', Function.update_of_ne (by omega : inp.v1 + k ≠ inp.v1 + 11)]
  have hslot_11 : mem' (inp.v1 + 11) = hCur := by simp only [mem', Function.update_self]
  refine ⟨ctx.wInp, ctx.WSubs, r_done, partialToWalk emb,
    r_done * ctx.wd.comps.length, r_done * (ctx.wd.comps.map fun c => c.J_sub.m).sum,
    ctx.wd.W.m - ctx.wd.j0Edges.length, del, upd, inn,
    ctx.hWInpH', ctx.hWInpEmb, ctx.hWInpJ, ctx.hWInpJAddr, hStat, ctx.hws, ctx.hw_ok,
    hAgr, hZf, le_trans hm.1 hLS.hCur_lo, hCur_max, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hslot_11, hEmbAt, hEmbBd, h1_le, hEta, hIsEmb, hVcong, hVcong_bd, hLen, rfl, rfl, rfl,
    hLS.hDel_le, by simpa [hcard0] using hLS.hVcU_le, by simpa [hcard0] using hLS.hInn_le,
    ctx.ht1_5, ctx.hout, ctx.ht1_3, ctx.hhend⟩
  · simpa [mem', Function.update_of_ne (by omega : inp.v1 ≠ inp.v1 + 11)] using hslots.1
  · exact (hslot_eq 1 (by decide)).trans hslots.2.1
  · exact (hslot_eq 2 (by decide)).trans hslots.2.2.1
  · exact (hslot_eq 3 (by decide)).trans hslots.2.2.2.1
  · simpa [hcard0] using (hslot_eq 4 (by decide)).trans hslots.2.2.2.2.1
  · exact (hslot_eq 5 (by decide)).trans hslots.2.2.2.2.2.1
  · exact (hslot_eq 6 (by decide)).trans hslots.2.2.2.2.2.2.1
  · exact (hslot_eq 7 (by decide)).trans hslots.2.2.2.2.2.2.2.1
  · exact (hslot_eq 8 (by decide)).trans hslots.2.2.2.2.2.2.2.2.1
  · exact (hslot_eq 9 (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.1
  · exact (hslot_eq 10 (by decide)).trans hslots.2.2.2.2.2.2.2.2.2.2.1

private lemma t2_total_cost_arith
    {eta etaCap m mw evs lenJH KinitGamma KdelGamma KqGamma gammaJ c_loop c_cont card0 : ℕ}
    (hEta : eta ≤ etaCap) (hCard : card0 ≤ mw)
    (hLoop : c_loop ≤
      eta * (m * KinitGamma + m * KdelGamma + 261 * m + 69 * mw + 45 * evs + 60 + 3) + 2 +
        card0 * (KqGamma + 200 * gammaJ * (lenJH + 1) + 600))
    (hCont : c_cont ≤ (c_loop + 5 + 2 + 1) + 1) :
    c_cont + (215 * m + 100 * evs + 500) ≤
      etaCap * (m * KinitGamma + m * KdelGamma + 400 * m + 100 * mw + 80 * evs + 250) +
        mw * (KqGamma + 200 * gammaJ * (lenJH + 1) + 600) +
        250 * m + 200 * evs + 600 := by
  have h1 : eta * (m * KinitGamma + m * KdelGamma + 261 * m + 69 * mw + 45 * evs + 63) ≤
      etaCap * (m * KinitGamma + m * KdelGamma + 400 * m + 100 * mw + 80 * evs + 250) :=
    Nat.mul_le_mul hEta (by omega)
  have h2 : card0 * (KqGamma + 200 * gammaJ * (lenJH + 1) + 600) ≤
      mw * (KqGamma + 200 * gammaJ * (lenJH + 1) + 600) :=
    Nat.mul_le_mul_right _ hCard
  nlinarith

/-- Runs `task2Body selfBase dsBase` for any valid `inp`, establishing `Task2OutAt` and the
`task2Cost` upper bound. -/
lemma task2Body_runs {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {selfBase dsBase : ℕ}
    (hHas : p.HasAt selfBase (task2Module selfBase dsBase))
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w))
    (inp : Task2Input) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hv : inp.Valid impl mem w) :
    ∃ o st' c,
      Runs w p ω (task2Body selfBase dsBase)
        (startState [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.t1OutAddr, inp.v1] mem pos) o st' c ∧
        Task2OutAt impl inp mem st'.mem o.value w ∧
        c ≤ task2Cost impl inp.J (length inp.J inp.embJH) inp.embVertSum := by
  have ctx := t2CtxOfValid hv
  have hp1 : p.procs[selfBase + 1]? = some t2BuildIncBody := hHas 1 (by simp [task2Module])
  have hp2 : p.procs[selfBase + 2]? = some t2InitJ0Body := hHas 2 (by simp [task2Module])
  have hp3 : p.procs[selfBase + 3]? = some (t2MiddleEdgeBody dsBase (selfBase + 4)) :=
    hHas 3 (by simp [task2Module])
  have hp4 : p.procs[selfBase + 4]? = some (t2DrainQueueBody dsBase) := hHas 4 (by simp [task2Module])
  let cont : Stmt := Stmt.loop (.reg 19) (t2RoundBody selfBase dsBase) ;;
    (t2St (.reg 4) (.const 11) (.reg 18) ;; Stmt.ret (.reg 18))
  have hbody_eq : task2Body selfBase dsBase =
      t2PreambleStmt
        (Stmt.call 16 (selfBase + 1) [.reg 4, .reg 17] ;;
         Stmt.assign 18 (t2Add (.reg 16) (t2Mul (.reg 12) (t2Add (t2Mul (.const 2) (.reg 13)) (.const 5)))) ;;
         Stmt.call 17 (selfBase + 2) [.reg 4, .reg 1, .reg 16] ;;
         t2TailSetupStmt cont) := rfl
  let st0 := startState [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.t1OutAddr, inp.v1] mem pos
  have hcps := task2Setup_cps ctx hp1 hp2 st0 ω rfl rfl rfl rfl rfl rfl cont
    (fun o stF c => Task2OutAt impl inp mem stF.mem o.value w ∧
      ∃ B_tail, c ≤ B_tail ∧
        B_tail + (215 * inp.J.m + 100 * inp.embVertSum + 500) ≤
          task2Cost impl inp.J (length inp.J inp.embJH) inp.embVertSum)
    (fun stc stL hLS => by
      have hloop := t2Loop_ptriple ctx stc hSpec hp3 hp4
      let Φ0 := (unembeddedSetPure ctx.wd (initEmb0 ctx.wInp)).card * t2EdgeBudget impl inp
      obtain ⟨o_l, st_l, c_l, Φ_l, hr_l, hq_l, hc_l⟩ := hloop stL Φ0 ω ⟨hLS, rfl⟩
      cases o_l with
      | returned _ => exact absurd hq_l (by simp)
      | normal =>
        rcases hq_l with ⟨a_f, hLS_f, h1_le, hEta_f, hcard0, hΦ_f⟩
        obtain ⟨hOut, hCur_max⟩ := t2Exit_to_task2OutAt ctx stc hLS_f h1_le hEta_f hcard0
        have hv1_w := (t2_maxWord_scalars ctx stc).2.2.2.1
        have hv1_11_w : inp.v1 + 11 < 2 ^ w := by omega
        have h11_w : 11 < 2 ^ w := by omega
        have hcur_w : a_f.hCur < 2 ^ w := by
          have hmx : Task2Input.maxHeapEnd impl inp ≤ Task2Input.maxWordBound impl inp := by
            unfold Task2Input.maxWordBound; exact le_trans (Nat.le_add_right _ 3) (le_max_left _ _)
          exact lt_of_le_of_lt (le_trans hCur_max hmx) ctx.hww.2.2
        have he_addr := Expr.eval_add (Expr.eval_reg_of_eq hLS_f.hr4) (Expr.eval_const h11_w) hv1_11_w
        have he_val := Expr.eval_reg_of_eq (w := w) hLS_f.hr18
        let st_st : State :=
          { mem := Function.update st_l.mem (inp.v1 + 11) a_f.hCur, regs := st_l.regs, pos := st_l.pos }
        have hr_st : Runs w p ω (t2St (.reg 4) (.const 11) (.reg 18)) st_l .normal st_st 5 :=
          runs_store_iff.mpr ⟨_, _, he_addr, he_val, rfl, rfl, rfl⟩
        have h18_st : st_st.regs 18 = a_f.hCur := hLS_f.hr18
        have hr_ret : Runs w p ω (Stmt.ret (.reg 18)) st_st (.returned a_f.hCur) st_st 2 :=
          runs_ret_iff.mpr ⟨_, Expr.eval_reg_of_eq h18_st, rfl, rfl, rfl⟩
        have hr_epi : Runs w p ω (t2St (.reg 4) (.const 11) (.reg 18) ;; Stmt.ret (.reg 18))
            st_l (.returned a_f.hCur) st_st (5 + 2 + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st_st, 5, 2, hr_st, hr_ret, rfl⟩)
        have hr_cont : Runs w p ω cont stL (.returned a_f.hCur) st_st (c_l + (5 + 2 + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨st_l, c_l, 5 + 2 + 1, hr_l, hr_epi, rfl⟩)
        have hcard_le : (unembeddedSetPure ctx.wd (initEmb0 ctx.wInp)).card ≤ Task1Input.mwCap impl inp.J := by
          have hc : (unembeddedSetPure ctx.wd (initEmb0 ctx.wInp)).card ≤ ctx.wd.W.m := by
            unfold unembeddedSetPure
            exact le_trans (Finset.card_filter_le _ _) (by simp)
          exact le_trans hc ctx.hmW_le
        refine ⟨.returned a_f.hCur, st_st, c_l + (5 + 2 + 1) + 1, hr_cont, hOut,
          (c_l + 5 + 2 + 1) + 1, by omega, ?_⟩
        dsimp only at hc_l
        have hc_l' : c_l ≤
            eta1Bound ctx.wd inp.J * (t2RoundBound impl inp + 3) + 2 +
              (unembeddedSetPure ctx.wd (initEmb0 ctx.wInp)).card * t2EdgeBudget impl inp := by
          omega
        unfold t2RoundBound t2EdgeBudget at hc_l'
        unfold task2Cost
        dsimp only at hc_l' ⊢
        set γJ := impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m
        exact t2_total_cost_arith
          (eta := eta1Bound ctx.wd inp.J) (etaCap := Task2Input.eta1Cap impl inp.J)
          (m := inp.J.m) (mw := Task1Input.mwCap impl inp.J) (evs := inp.embVertSum)
          (lenJH := length inp.J inp.embJH)
          (KinitGamma := ⌈impl.pathDS.params.K_init * (γJ : ℝ)⌉₊)
          (KdelGamma := ⌈impl.pathDS.params.K_del * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊)
          (KqGamma := ⌈impl.pathDS.params.K_query * (impl.pathDS.params.gQuery (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m : ℝ)⌉₊)
          (gammaJ := γJ)
          (c_loop := c_l) (c_cont := (c_l + 5 + 2 + 1) + 1)
          (card0 := (unembeddedSetPure ctx.wd (initEmb0 ctx.wInp)).card)
          (t2_eta1Bound_le_eta1Cap ctx) hcard_le hc_l' le_rfl)
  obtain ⟨o, stF, c_tot, hr_tot, c_cont, ⟨hOut, B_tail, hcc, htot⟩, hc_le⟩ := hcps
  rw [← hbody_eq] at hr_tot
  exact ⟨o, stF, c_tot, hr_tot, hOut, by omega⟩

private lemma task2_inputs_agree {impl : SpannerToolImpl} {mem : ℕ → ℕ} {w : ℕ}
    {inp₁ inp₂ : Task2Input}
    (hargs : [inp₁.hAddr, inp₁.jAddr, inp₁.embJHAddr, inp₁.t1OutAddr, inp₁.v1] =
      [inp₂.hAddr, inp₂.jAddr, inp₂.embJHAddr, inp₂.t1OutAddr, inp₂.v1])
    (hv₁ : inp₁.Valid impl mem w) (hv₂ : inp₂.Valid impl mem w) :
    inp₁.hAddr = inp₂.hAddr ∧ inp₁.jAddr = inp₂.jAddr ∧ inp₁.embJHAddr = inp₂.embJHAddr ∧
      inp₁.t1OutAddr = inp₂.t1OutAddr ∧ inp₁.v1 = inp₂.v1 ∧
      inp₁.H' = inp₂.H' ∧ inp₁.J = inp₂.J ∧
      ∀ e < inp₁.J.m, inp₁.embJH e = inp₂.embJH e := by
  simp only [List.cons.injEq, and_true] at hargs
  rcases hargs with ⟨hh, hj, he, ht, hv1⟩
  have hH' : inp₁.H' = inp₂.H' := by
    have g1 := graphAt_iff_readGraph.mp hv₁.2.1
    have g2 := graphAt_iff_readGraph.mp hv₂.2.1
    rw [← g1, ← g2, hh]
  have hJ : inp₁.J = inp₂.J := by
    have g1 := graphAt_iff_readGraph.mp hv₁.2.2.2.1
    have g2 := graphAt_iff_readGraph.mp hv₂.2.2.2.1
    rw [← g1, ← g2, hj]
  have hemb : ∀ e < inp₁.J.m, inp₁.embJH e = inp₂.embJH e := fun e hem => by
    have w1 := hv₁.2.2.2.2.2.1 e hem
    have w2 := hv₂.2.2.2.2.2.1 e (hJ ▸ hem)
    rw [← he] at w2
    exact walkAt_unique w1 w2
  exact ⟨hh, hj, he, ht, hv1, hH', hJ, hemb⟩

private lemma task2_outAt_congr {impl : SpannerToolImpl} {mem₀ mem' : ℕ → ℕ} {v2 w : ℕ}
    {inp₁ inp₂ : Task2Input}
    (hagree : inp₁.hAddr = inp₂.hAddr ∧ inp₁.jAddr = inp₂.jAddr ∧ inp₁.embJHAddr = inp₂.embJHAddr ∧
      inp₁.t1OutAddr = inp₂.t1OutAddr ∧ inp₁.v1 = inp₂.v1 ∧
      inp₁.H' = inp₂.H' ∧ inp₁.J = inp₂.J ∧
      ∀ e < inp₁.J.m, inp₁.embJH e = inp₂.embJH e)
    (hout : Task2OutAt impl inp₁ mem₀ mem' v2 w) :
    Task2OutAt impl inp₂ mem₀ mem' v2 w := by
  rcases hagree with ⟨_, hj, he, ht1, hv1, hH', hJ, hemb⟩
  rcases hout with ⟨wInp, WSubs, η₁, embWJ, ic, ie, gp, del, vc, inn,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41⟩
  have hevs : inp₁.embVertSum = inp₂.embVertSum := by
    unfold Task2Input.embVertSum
    rw [hJ]
    refine Finset.sum_congr rfl fun e he' => ?_
    rw [hemb e (hJ ▸ Finset.mem_range.mp he')]
  have hlen : length inp₁.J inp₁.embJH = length inp₂.J inp₂.embJH := by
    unfold length
    rw [hJ]
    exact Finset.fold_congr fun e he' => by rw [hemb e (hJ ▸ Finset.mem_range.mp he')]
  have hmax : Task2Input.maxHeapEnd impl inp₁ = Task2Input.maxHeapEnd impl inp₂ := by
    unfold Task2Input.maxHeapEnd Task2Input.staticEndCap Task2Input.nodesAddr Task2Input.queueAddr
      Task2Input.eWVertStampAddr Task2Input.procStampAddr Task2Input.vcongNumAddr Task2Input.vHeadAddr
      Task2Input.vhatStampAddr Task2Input.compEdgeDelRoundAddr Task2Input.vhatOffsetAddr
      Task2Input.compEdgeBaseAddr Task2Input.dsHandlesAddr Task2Input.embWJAddr
    rw [hJ, hH', hv1, hevs]
  have hcomp_eq : ∀ eW < (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs).W.m,
      compose inp₁.J inp₁.embJH embWJ eW = compose inp₂.J inp₂.embJH embWJ eW := fun eW heW => by
    unfold compose
    have hj_lt : ∀ e ∈ (embWJ eW).edges, e < inp₁.J.m := by
      intro e he
      rcases h28.2 eW heW with ⟨_, _, ⟨_, hpe, _⟩ | ⟨_, _, _, _, hedges, _⟩⟩
      · simp [hpe] at he
      · exact hedges e he
    exact t2_composeAux_congr hJ fun e he => hemb e (hj_lt e he)
  have hvcong_eq :
      vcong (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs).W inp₁.H'
          (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs).wW
          (compose inp₁.J inp₁.embJH embWJ) =
        vcong (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs).W inp₂.H'
          (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs).wW
          (compose inp₂.J inp₂.embJH embWJ) := by
    unfold vcong
    rw [hH']
    refine Finset.fold_congr fun x _ => ?_
    unfold vcongAt
    have hflt : (Finset.range (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs).W.m).filter
          (fun j => x ∈ (compose inp₁.J inp₁.embJH embWJ j).verts) =
        (Finset.range (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs).W.m).filter
          (fun j => x ∈ (compose inp₂.J inp₂.embJH embWJ j).verts) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun ⟨hj', hx⟩ => ⟨hj', hcomp_eq j hj' ▸ hx⟩,
        fun ⟨hj', hx⟩ => ⟨hj', (hcomp_eq j hj').symm ▸ hx⟩⟩
    rw [hflt]
  have hok' : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK tools inp₂.H' inp₂.J inp₂.embJH
        (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs) := fun tools => by
    have h := h7 tools
    rw [← hH', ← hJ]
    exact ⟨h.W_n, h.W_valid, h.W_m_eq, h.aligned, h.φ_dec_pos, h.φ_dec_le,
      h.φ_Const_pos, h.φ_Const_le, h.c_deg_ge, h.φ_ds_pos, h.φ_ds_le_dec, h.φ_ds_le_Const,
      h.φ_ds_half, h.γ_ExpPath_ge, h.γ_del_ge, h.τ₁_nonneg, h.τ₂_pos, h.j0_nodup, h.j0_lt,
      h.comp_props, h.comp_disjoint, h.comp_disjoint_j0⟩
  have hEmb2 : IsEmbedding (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs).W
      inp₂.J embWJ := by
    rw [← hJ]; exact h28
  have h_ewj : inp₁.embWJAddr = inp₂.embWJAddr := by
    unfold Task2Input.embWJAddr; rw [hv1]
  refine ⟨wInp, WSubs, η₁, embWJ, ic, ie, gp, del, vc, inn,
    hH' ▸ h1, fun e he' => (h2 e (hJ ▸ he')).trans (hemb e (hJ ▸ he')), hJ ▸ h3, hj ▸ h4, h5, h6, hok',
    hv1 ▸ h8, h9, hv1 ▸ h10, hmax ▸ h11, by rw [← hv1, ← h_ewj]; exact h12, hv1 ▸ h13, hv1 ▸ h14, hv1 ▸ h15,
    hv1 ▸ h16, hv1 ▸ h17, hv1 ▸ h18, hv1 ▸ h19, hv1 ▸ h20, hH' ▸ hv1 ▸ h21, hv1 ▸ h22, hv1 ▸ h23,
    by rw [← h_ewj]; exact h24, by rw [← h_ewj]; exact h25, h26, hJ ▸ h27, hEmb2,
    by rw [← hvcong_eq]; exact h29, by rw [← hvcong_eq, ← hJ]; exact h30, h31, h32,
    h33, h34, hJ ▸ h35, hlen ▸ h36, hlen ▸ h37, by rw [← ht1]; exact h38, hv1 ▸ h39, by rw [← ht1]; exact h40, h41⟩

/-- Top-level correctness theorem: `task2Module` implements `task2Contract`. -/
theorem task2_meetsContract {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {selfBase dsBase : ℕ}
    (hHas : p.HasAt selfBase (task2Module selfBase dsBase))
    (hSpec : impl.pathDS.R.Implements w p dsBase (fun i => dsBase + 1 + i)
      (pathDSDataStructure impl.pathDS.params w)) :
    MeetsContract w p selfBase (task2Contract impl w) := by
  intro args mem pos ω _ hpre
  rcases hpre with ⟨inp₀, rfl, hv₀⟩
  have hbody : p.procs[selfBase]? = some (task2Body selfBase dsBase) := hHas 0 (by simp [task2Module])
  obtain ⟨o, st', c, hruns, hout, hcost⟩ := task2Body_runs hHas hSpec inp₀ mem pos ω hv₀
  refine ⟨task2Body selfBase dsBase, hbody, o, st', c, hruns, ?_, ?_⟩
  · intro inp' hargs' hv'
    exact task2_outAt_congr (task2_inputs_agree hargs' hv₀ hv') hout
  · have h_ex : ∃ inp : Task2Input,
        [inp₀.hAddr, inp₀.jAddr, inp₀.embJHAddr, inp₀.t1OutAddr, inp₀.v1] =
          [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.t1OutAddr, inp.v1] ∧
        inp.Valid impl mem w := ⟨inp₀, rfl, hv₀⟩
    dsimp only [task2Contract]
    simp only [h_ex, ↓reduceDIte]
    let inp_c := Classical.choose h_ex
    have hc_spec := Classical.choose_spec h_ex
    have hag := task2_inputs_agree hc_spec.1 hv₀ hc_spec.2
    have hJ : inp₀.J = inp_c.J := hag.2.2.2.2.2.2.1
    have hevs : inp₀.embVertSum = inp_c.embVertSum := by
      unfold Task2Input.embVertSum
      rw [hJ]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [hag.2.2.2.2.2.2.2 e (hJ ▸ Finset.mem_range.mp he)]
    have hlen : length inp₀.J inp₀.embJH = length inp_c.J inp_c.embJH := by
      unfold length
      rw [hJ]
      exact Finset.fold_congr fun e he => by rw [hag.2.2.2.2.2.2.2 e (hJ ▸ Finset.mem_range.mp he)]
    rw [← hlen, ← hevs, ← hJ]
    exact hcost

end MinCostFlow.Spanner
