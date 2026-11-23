module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4Edge
public import MinCostFlow.SparseCore.Program.SpanReadout
public import MinCostFlow.DynSpanner.Program.DynSpannerDSLemmas

import WordRAM.Tactic

/-!
# The walks of the edges that leave a spanner, in Phase 4 (`AssemblyFirstStepP4ScanDleft`)

When the update of an old active slot drops an edge `e` from its spanner while `e` stays in the
slot's graph, `stepBundleTree` puts the edges of the new walk of `e` into the set `D_left`, which
is a part of `D_tot`. These walk edges need the same work as the edges of `D`: they go into
`inDtot`, they are marked, and they are pushed into both candidate lists `delSup` and `insSup`.

The program finds the dropped edges in the copy buffer of the slot. After the scans of `U_H` and
`R`, the copy buffer of an old active slot holds edges of the slot's new graph that are not in its
new spanner. Among them, the ones that were in the old output graph `OS` are exactly the dropped
edges: an edge of the slot's graph lies in the old output graph exactly when it lies in the old
spanner, and the scan of `U_H` copies every edge that the spanner deleted.

`asmFirstScanDleftStmt fEdge fWalk` takes `[gEPres, hEPres, ws, eCap, oldS, b]`: the presence
arrays of the slot's new graph and spanner, the workspace, the cap, the presence array of the old
output graph, and the handle `b` of the slot's spanner. For each edge `e` of the copy buffer whose
word in the old output graph is set, it reads the walk `piTotal` of `e` with `spanPiWalkPtrStmt`
(at `fWalk`) and calls the one-edge procedure `asmFirstP4EdgeStmt` (at `fEdge`) on each edge of
the walk. `asmFirstScanDleft_runs` proves that it turns the workspace `S` into
`S.copyBuf.foldl (p4StepDleft GE HE OS (piTotal (d.state P))) S`, keeps every cell outside the
workspace, and costs at most the sum of `p4DleftEdgeCost P d e` over the copy buffer, plus `30`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The work on one edge `e` of the copy buffer: when `e` is in the old output graph `OS`, every
edge of the walk `walk e` goes into `inDtot`, is marked, and is pushed into `delSup` and
`insSup`. -/
noncomputable def p4StepDleft (GE HE OS : Finset ℕ) (walk : ℕ → List (ℕ × Bool))
    (S : Phase4WS) (e : ℕ) : Phase4WS :=
  open Classical in
  if e ∈ OS then ((walk e).map Prod.fst).foldl (p4StepEdge GE HE true true true false) S else S

/-- A bound on the steps spent on one edge `e` of the copy buffer. -/
noncomputable def p4DleftEdgeCost (P : DSParams) (d : DSHist) (e : ℕ) : ℕ :=
  300 * (piTotal (d.state P) e).length + 65 * P.L + 250

/-- The loop over a walk, whose place is in register `10` and whose length is in register `11`:
the one-edge procedure on each edge of the walk. -/
def asmFirstDleftWalkLoop (fEdge : ℕ) : Stmt :=
  forRange 12 (.const 0) (.reg 11)
    (.assign 13 (.load (.bin .add (.bin .add (.reg 10) (.const 1))
      (.bin .mul (.const 2) (.reg 12)))) ;;
     .call 14 fEdge [.reg 0, .reg 1, .reg 2, .reg 3, .reg 13, .const 1, .const 1, .const 1,
       .const 0])

/-- The fetch of the walk of the edge in register `9` when its word in the old output graph
(register `4`) is set: the place of the walk goes into register `10` and its length into
register `11`. -/
def asmFirstDleftFetch (fWalk : ℕ) : Stmt :=
  .cond (.load (.bin .add (.reg 4) (.reg 9)))
    (.call 10 fWalk [.reg 5, .reg 9] ;; .assign 11 (.load (.reg 10)))
    .nop

/-- The loop body of `asmFirstScanDleftStmt` on the edge at place `i` (register `8`) of the copy
buffer. Register `6` holds the address of the length of the copy buffer. -/
def asmFirstScanDleftBody (fEdge fWalk : ℕ) : Stmt :=
  .assign 9 (.load (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 8))) ;;
  .assign 11 (.const 0) ;;
  asmFirstDleftFetch fWalk ;;
  asmFirstDleftWalkLoop fEdge

/-- **The scan of the walks of `D_left`**, `[gEPres, hEPres, ws, eCap, oldS, b]`. -/
def asmFirstScanDleftStmt (fEdge fWalk : ℕ) : Stmt :=
  .assign 6 (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 10) (.reg 3))) (.const 3)) ;;
  .assign 7 (.load (.reg 6)) ;;
  forRange 8 (.const 0) (.reg 7) (asmFirstScanDleftBody fEdge fWalk) ;;
  .ret (.const 0)

theorem asmFirstScanDleftStmt_noRand (fEdge fWalk : ℕ) :
    (asmFirstScanDleftStmt fEdge fWalk).NoRand := by
  simp [asmFirstScanDleftStmt, asmFirstScanDleftBody, asmFirstDleftFetch,
    asmFirstDleftWalkLoop, forRange, forUp, Stmt.NoRand]

end

/-! ## The copy buffer stays -/

public section

/-- The one-edge work without the copy flag keeps the copy buffer. -/
theorem p4StepEdge_copyBuf (GE HE : Finset ℕ) (fD fDel fIns : Bool) (S : Phase4WS) (e : ℕ) :
    (p4StepEdge GE HE fD fDel fIns false S e).copyBuf = S.copyBuf := by
  cases fD <;> cases fDel <;> cases fIns <;> simp [p4StepEdge, p4Mark]

theorem foldl_p4StepEdge_copyBuf (GE HE : Finset ℕ) (fD fDel fIns : Bool) (es : List ℕ)
    (S : Phase4WS) :
    (es.foldl (p4StepEdge GE HE fD fDel fIns false) S).copyBuf = S.copyBuf := by
  induction es generalizing S with
  | nil => rfl
  | cons e es ih => rw [List.foldl_cons, ih, p4StepEdge_copyBuf]

theorem foldl_p4StepDleft_copyBuf (GE HE OS : Finset ℕ) (walk : ℕ → List (ℕ × Bool))
    (es : List ℕ) (S : Phase4WS) :
    (es.foldl (p4StepDleft GE HE OS walk) S).copyBuf = S.copyBuf := by
  classical
  induction es generalizing S with
  | nil => rfl
  | cons e es ih =>
    rw [List.foldl_cons, ih]
    unfold p4StepDleft
    split_ifs
    · exact foldl_p4StepEdge_copyBuf GE HE true true true _ S
    · rfl

end

/-! ## Helpers -/

public section

/-- The representation of a spanner depends only on the words of its footprint. -/
theorem dsRepAt_of_agree {P : DSParams} {b : ℕ} {d : DSHist} {x : DynSpannerMeta P.L}
    {mem mem' : ℕ → ℕ} (h : DSRepAt P b d x mem)
    (hag : ∀ a, metaFoot b x a → mem' a = mem a) : DSRepAt P b d x mem' := by
  obtain ⟨hL, hV, hm, hE, hB, hds, hsp, hState, hRev, hgen⟩ := h
  have hgen' := (stepZero_fixed_lt b P.L P.vCap P.eCap).1 dsGenOff (by decide)
  have hgen_eq : mem' (b + dsGenOff) = mem (b + dsGenOff) :=
    hag _ (Or.inl ⟨hgen'.1, by rw [hState.1, hState.2.1]; exact hgen'.2⟩)
  exact ⟨hL, hV, hm, hE, hB, hds, hsp, dynSpannerStateAt_of_agree_foot hState hag, hRev,
    by rw [hgen_eq]; exact hgen⟩

end

private lemma copyBuf_length_le' {mem : ℕ → ℕ} {ws eCap : ℕ} {S : Phase4WS}
    (h : Phase4WSAt mem ws eCap S) : S.copyBuf.length ≤ eCap := by
  obtain ⟨-, -, -, -, -, -, -, hnd, hcb, -, -⟩ := h
  rw [← List.toFinset_card_of_nodup hnd]
  calc S.copyBuf.toFinset.card ≤ (Finset.range eCap).card :=
        Finset.card_le_card fun e he => Finset.mem_range.mpr (hcb e (List.mem_toFinset.mp he)).1
    _ = eCap := Finset.card_range eCap

private lemma rangeCost_getElem_eq_map_sum' (l : List ℕ) (f : ℕ → ℕ) :
    rangeCost (fun i => if hi : i < l.length then f (l[i]'hi) else 0) 0 l.length =
      (l.map f).sum := by
  have h : ∀ k (hk : k ≤ l.length),
      rangeCost (fun i => if hi : i < l.length then f (l[i]'hi) else 0) 0 k =
        ((l.take k).map f).sum := by
    intro k
    induction k with
    | zero => intro _; simp [rangeCost]
    | succ m ih =>
      intro hm
      have hmlt : m < l.length := by omega
      have hstep : rangeCost (fun i => if hi : i < l.length then f (l[i]'hi) else 0) 0 (m + 1) =
          rangeCost (fun i => if hi : i < l.length then f (l[i]'hi) else 0) 0 m +
            (if hi : m < l.length then f (l[m]'hi) else 0) := by
        simp only [rangeCost, Nat.sub_zero, List.range'_eq_map_range, List.range_succ,
          List.map_append, List.map_singleton, List.sum_append, List.sum_singleton, Nat.zero_add]
      rw [hstep, ih (by omega), dite_eq_left_of_eq_true (eq_true hmlt),
        List.take_succ_eq_append_getElem hmlt, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
  simpa using h l.length le_rfl

private lemma sum_map_add_nine_le (l : List ℕ) (f g : ℕ → ℕ) (h : ∀ e, f e + 9 ≤ g e) :
    (l.map f).sum + 9 * l.length ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h e
    omega

/-- A statement given by a lemma on its runs, at the start of a sequence. -/
private theorem runs_seq_block_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s : Stmt}
    {st : State} {B k T : ℕ} {Q : Outcome → State → Prop} {R : State → Prop}
    (h₁ : ∃ st₁ c₁, Runs w p ω s₁ st .normal st₁ c₁ ∧ R st₁ ∧ c₁ ≤ B)
    (hrest : ∀ st₁, R st₁ →
      ∃ o st' c, Runs w p ω s st₁ o st' c ∧ Q o st' ∧ (k + B + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s₁ s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨st₁, c₁, hr₁, hR, hc₁⟩ := h₁
  obtain ⟨o, st', c, hr, hq, hc⟩ := hrest st₁ hR
  exact ⟨o, st', c₁ + c + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c, hr₁, hr, rfl⟩), hq, by omega⟩

/-! ## The loop over a walk -/

set_option maxHeartbeats 1600000 in
/-- The loop over a walk with edges `es`, whose words lie outside the workspace: the one-edge
work with `fD`, `fDel` and `fIns` set, on each edge in turn. -/
private theorem dleftWalkLoop_runs {w fEdge fPush fMark gEPres hEPres ws eCap ret : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hfEdge : p.procs[fEdge]? = some (asmFirstP4EdgeStmt fPush fMark))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt)
    {GE HE : Finset ℕ} {es : List ℕ} {S : Phase4WS} {mem₀ : ℕ → ℕ} {st : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hr0 : st.regs 0 = gEPres) (hr1 : st.regs 1 = hEPres) (hr2 : st.regs 2 = ws)
    (hr3 : st.regs 3 = eCap) (hr10 : st.regs 10 = ret) (hr11 : st.regs 11 = es.length)
    (hW : Phase4WSAt st.mem ws eCap S)
    (hfr : ∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st.mem a = mem₀ a)
    (hGE : ∀ e < eCap, mem₀ (gEPres + e) = if e ∈ GE then 1 else 0)
    (hHE : ∀ e < eCap, mem₀ (hEPres + e) = if e ∈ HE then 1 else 0)
    (hes : ∀ j (hj : j < es.length), mem₀ (ret + 1 + 2 * j) = es[j])
    (hes_out : ∀ j < es.length, ret + 1 + 2 * j < ws ∨ ws + p4WsSize eCap ≤ ret + 1 + 2 * j)
    (hes_w : ∀ j < es.length, ret + 1 + 2 * j < 2 ^ w)
    (hesCap : ∀ e ∈ es, e < eCap)
    (hg_disj : gEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ gEPres)
    (hh_disj : hEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ hEPres)
    (hg_w : gEPres + eCap < 2 ^ w) (hh_w : hEPres + eCap < 2 ^ w)
    (hws_w : ws + p4WsSize eCap < 2 ^ w) :
    ∃ st' c, Runs w p ω (asmFirstDleftWalkLoop fEdge) st .normal st' c ∧
      (∀ r, r ≠ 12 → r ≠ 13 → r ≠ 14 → st'.regs r = st.regs r) ∧
      Phase4WSAt st'.mem ws eCap (es.foldl (p4StepEdge GE HE true true true false) S) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = mem₀ a) ∧
      c ≤ 300 * es.length + 10 := by
  classical
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun j st₁ =>
    (∀ r, r ≠ 12 → r ≠ 13 → r ≠ 14 → st₁.regs r = st.regs r) ∧ st₁.regs 12 = j ∧
    Phase4WSAt st₁.mem ws eCap ((es.take j).foldl (p4StepEdge GE HE true true true false) S) ∧
    (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st₁.mem a = mem₀ a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 12) (lo := .const 0) (hi := .reg 11)
    (body := .assign 13 (.load (.bin .add (.bin .add (.reg 10) (.const 1))
        (.bin .mul (.const 2) (.reg 12)))) ;;
      .call 14 fEdge [.reg 0, .reg 1, .reg 2, .reg 3, .reg 13, .const 1, .const 1, .const 1,
        .const 0])
    (P := fun st₁ => st₁ = st) (Inv := Inv) (fun _ => 290) 0 es.length (Nat.zero_le _) h1w
    (fun hlt => by have := hes_w (es.length - 1) (by omega); omega)
    (fun st₁ hst => by
      subst hst
      refine ⟨Expr.eval_const h0w, fun r h12 _ _ => by simp [h12], by simp, ?_, hfr⟩
      simpa using hW)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq
      ((hI.1 11 (by decide) (by decide) (by decide)).trans hr11))
    (fun j _ hj st₁ ω' hI => by
      obtain ⟨hregs, h12, hWj, hfrj⟩ := hI
      have hjw : ret + 1 + 2 * j < 2 ^ w := hes_w j hj
      have hm : st₁.mem (ret + 1 + 2 * j) = es[j] := (hfrj _ (hes_out j hj)).trans (hes j hj)
      have hecap : es[j] < eCap := hesCap _ (List.getElem_mem hj)
      have h0' : st₁.regs 0 = gEPres := (hregs 0 (by decide) (by decide) (by decide)).trans hr0
      have h1' : st₁.regs 1 = hEPres := (hregs 1 (by decide) (by decide) (by decide)).trans hr1
      have h2' : st₁.regs 2 = ws := (hregs 2 (by decide) (by decide) (by decide)).trans hr2
      have h3' : st₁.regs 3 = eCap := (hregs 3 (by decide) (by decide) (by decide)).trans hr3
      have h10' : st₁.regs 10 = ret :=
        (hregs 10 (by decide) (by decide) (by decide)).trans hr10
      have hEval : (Expr.load (.bin .add (.bin .add (.reg 10) (.const 1))
          (.bin .mul (.const 2) (.reg 12)))).eval w st₁ = some es[j] :=
        Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h10')
          (Expr.eval_const h1w) (by omega)) (Expr.eval_mul (Expr.eval_const h2w)
            (Expr.eval_reg_of_eq h12) (by omega)) (by omega)) hm
      obtain ⟨stE, cE, hrE, hWE, hfrE, hcE⟩ := asmFirstP4Edge_runs (fD := 1) (fDel := 1)
        (fIns := 1) (fCopy := 0) (pos := st₁.pos) (ω := ω') (e := es[j]) hfPush hfMark hw16 hWj
        (fun e he => (hfrj _ (by rcases hg_disj with h | h <;> omega)).trans (hGE e he))
        (fun e he => (hfrj _ (by rcases hh_disj with h | h <;> omega)).trans (hHE e he))
        hecap hg_disj hh_disj hg_w hh_w hws_w
      have hA : Runs w p ω' (.assign 13 (.load (.bin .add (.bin .add (.reg 10) (.const 1))
          (.bin .mul (.const 2) (.reg 12))))) st₁ .normal
          { st₁ with regs := Function.update st₁.regs 13 es[j] } 9 :=
        runs_assign_iff.mpr ⟨es[j], hEval, rfl, rfl, rfl⟩
      have hargs : evalArgs w { st₁ with regs := Function.update st₁.regs 13 es[j] }
          [.reg 0, .reg 1, .reg 2, .reg 3, .reg 13, .const 1, .const 1, .const 1, .const 0] =
          some [gEPres, hEPres, ws, eCap, es[j], 1, 1, 1, 0] := by
        simp [evalArgs, Expr.eval, h0', h1', h2', h3', h1w, h0w]
      refine ⟨.normal, _, _, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hA,
          runs_call_iff.mpr ⟨_, _, _, _, _, hargs, hfEdge, hrE, rfl, rfl, rfl⟩, rfl⟩),
        ⟨⟨fun r h12' h13' h14' => ?_, by simp, ?_, fun a ha => (hfrE a ha).trans (hfrj a ha)⟩,
          by simp [h12]⟩, by simp only [argsSize, Expr.size]; omega⟩
      · simp only [Function.update_apply, h12', h13', h14', ↓reduceIte]
        exact hregs r h12' h13' h14'
      · rw [List.take_succ_eq_append_getElem hj, List.foldl_append]
        simpa using hWE)
  obtain ⟨o, st', c, hr, hpost, hc⟩ := hloop st ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    obtain ⟨hregs, -, hW', hfr'⟩ := hpost
    rw [List.take_length] at hW'
    refine ⟨st', c, hr, hregs, hW', hfr', ?_⟩
    have hrc : rangeCost (fun _ => 290) 0 es.length = 290 * es.length := by
      simp [rangeCost, Nat.mul_comm]
    simp only [hrc, Expr.size, Nat.sub_zero] at hc
    omega

/-! ## The fetch of a walk -/

/-- When the word of `e` in the old output graph is `1`, the fetch reads the walk of `e`: the
memory stays, register `10` points to the walk, and register `11` holds its length. -/
private theorem dleftFetch_runs {P : DSParams} {fWalk oldS b e : ℕ} {p : Program}
    {ω : ℕ → Bool} {d : DSHist} {x : DynSpannerMeta P.L} {st : State}
    (hfWalk : MeetsContract P.w p fWalk (spanPiWalkPtrContract P b e d x))
    (hw16 : 16 ≤ 2 ^ P.w)
    (hr4 : st.regs 4 = oldS) (hr5 : st.regs 5 = b) (hr9 : st.regs 9 = e)
    (hos : st.mem (oldS + e) = 1) (ho_w : oldS + e < 2 ^ P.w)
    (hRep : DSRepAt P b d x st.mem) (heG : e ∈ (d.state P).G.E)
    (hFix : b + dsFixedSize P.L P.vCap P.eCap < 2 ^ P.w)
    (hHeapW : ∀ a, heapFoot x a → a < 2 ^ P.w) (he_w : e < 2 ^ P.w) :
    ∃ st₁ c₁, Runs P.w p ω (asmFirstDleftFetch fWalk) st .normal st₁ c₁ ∧
      st₁.mem = st.mem ∧ (∀ r, r ≠ 10 → r ≠ 11 → st₁.regs r = st.regs r) ∧
      st₁.regs 11 = (piTotal (d.state P) e).length ∧
      MWalkAt st.mem (st₁.regs 10) (piTotal (d.state P) e) ∧
      RangeInHeapFoot x (st₁.regs 10)
        (st₁.regs 10 + (mWalkEncode (piTotal (d.state P) e)).length) ∧
      c₁ ≤ spanPiWalkPtrCost P.L + 20 := by
  have hb_w : b < 2 ^ P.w := by omega
  have hargs : evalArgs P.w st [.reg 5, .reg 9] = some [b, e] := by
    simp [evalArgs, Expr.eval, hr5, hr9]
  have hwords : ∀ v ∈ [b, e], v < 2 ^ P.w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hb_w
    · exact he_w
  obtain ⟨stc, cc, v, hrc, ⟨hmem, hwalk, hrange⟩, hv, hother, hcc⟩ :=
    runs_call_of_meetsContract (r := 10) hfWalk hargs hwords
      ⟨rfl, hw16, hRep, heG, hFix, hHeapW⟩ ω
  have hA : Runs P.w p ω (.assign 11 (.load (.reg 10))) stc .normal
      { stc with regs := Function.update stc.regs 11 (piTotal (d.state P) e).length } 3 :=
    runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq (Expr.eval_reg_of_eq hv)
      (MWalkAt_head hwalk), rfl, rfl, rfl⟩
  have hseq := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrc, hA, rfl⟩)
  have hcond : (Expr.load (.bin .add (.reg 4) (.reg 9))).eval P.w st = some 1 :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr4) (Expr.eval_reg_of_eq hr9)
      ho_w) hos
  refine ⟨{ stc with regs := Function.update stc.regs 11 (piTotal (d.state P) e).length }, _,
    runs_cond_iff.mpr ⟨1, _, hcond, by simpa using hseq, rfl⟩, hmem,
    fun r h10 h11 => ?_, by simp, ?_, ?_, ?_⟩
  · simp only [Function.update_apply, h11, ↓reduceIte]
    exact hother r h10
  · simp only [Function.update_apply, show (10 : ℕ) ≠ 11 by decide, ↓reduceIte, hv]
    rw [← hmem]; exact hwalk
  · simp only [Function.update_apply, show (10 : ℕ) ≠ 11 by decide, ↓reduceIte, hv]
    exact hrange
  · simp only [spanPiWalkPtrContract, argsSize, Expr.size] at hcc
    simp only [Expr.size]
    omega

/-! ## One edge of the copy buffer -/

set_option maxHeartbeats 1600000 in
/-- One pass of the loop body of `asmFirstScanDleftStmt`, on the edge at place `i` of the copy
buffer. The workspace `T` has the copy buffer of `S`. -/
private theorem scanDleftBody_runs {P : DSParams}
    {fEdge fPush fMark fWalk gEPres hEPres ws eCap oldS b i : ℕ} {p : Program} {ω : ℕ → Bool}
    (hfEdge : p.procs[fEdge]? = some (asmFirstP4EdgeStmt fPush fMark))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt)
    {d : DSHist} {x : DynSpannerMeta P.L}
    (hfWalk : ∀ e, MeetsContract P.w p fWalk (spanPiWalkPtrContract P b e d x))
    {GE HE OS : Finset ℕ} {S T : Phase4WS} {mem₀ : ℕ → ℕ} {st : State}
    (hw16 : 16 ≤ 2 ^ P.w)
    (hr0 : st.regs 0 = gEPres) (hr1 : st.regs 1 = hEPres) (hr2 : st.regs 2 = ws)
    (hr3 : st.regs 3 = eCap) (hr4 : st.regs 4 = oldS) (hr5 : st.regs 5 = b)
    (hr6 : st.regs 6 = ws + 10 * eCap + 3) (hr8 : st.regs 8 = i)
    (hi : i < S.copyBuf.length)
    (hW : Phase4WSAt st.mem ws eCap T) (hT : T.copyBuf = S.copyBuf)
    (hfr : ∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st.mem a = mem₀ a)
    (hGE : ∀ e < eCap, mem₀ (gEPres + e) = if e ∈ GE then 1 else 0)
    (hHE : ∀ e < eCap, mem₀ (hEPres + e) = if e ∈ HE then 1 else 0)
    (hOS : ∀ e < eCap, mem₀ (oldS + e) = if e ∈ OS then 1 else 0)
    (hRep : DSRepAt P b d x mem₀)
    (hFix : b + dsFixedSize P.L P.vCap P.eCap < 2 ^ P.w)
    (hHeapW : ∀ a, heapFoot x a → a < 2 ^ P.w)
    (hFootDisj : ∀ a, metaFoot b x a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hCopyG : S.copyBuf[i] ∈ OS → S.copyBuf[i] ∈ (d.state P).G.E)
    (hWalkCap : S.copyBuf[i] ∈ OS → ∀ q ∈ piTotal (d.state P) S.copyBuf[i], q.1 < eCap)
    (hg_disj : gEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ gEPres)
    (hh_disj : hEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ hEPres)
    (ho_disj : oldS + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ oldS)
    (hg_w : gEPres + eCap < 2 ^ P.w) (hh_w : hEPres + eCap < 2 ^ P.w)
    (ho_w : oldS + eCap < 2 ^ P.w) (hws_w : ws + p4WsSize eCap < 2 ^ P.w) :
    ∃ st' c, Runs P.w p ω (asmFirstScanDleftBody fEdge fWalk) st .normal st' c ∧
      (∀ r, r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → st'.regs r = st.regs r) ∧
      Phase4WSAt st'.mem ws eCap (p4StepDleft GE HE OS (piTotal (d.state P)) T S.copyBuf[i]) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = mem₀ a) ∧
      c + 9 ≤ p4DleftEdgeCost P d S.copyBuf[i] := by
  classical
  unfold asmFirstScanDleftBody
  have h0w : 0 < 2 ^ P.w := by omega
  have h1w : 1 < 2 ^ P.w := by omega
  have hws' : ws + 11 * eCap + 4 < 2 ^ P.w := by simp only [p4WsSize] at hws_w; omega
  set e := S.copyBuf[i] with he_def
  have hcbLen : T.copyBuf.length ≤ eCap := copyBuf_length_le' hW
  rw [hT] at hcbLen
  have heCap : e < eCap := (hW.2.2.2.2.2.2.2.2.1 e (hT ▸ List.getElem_mem hi)).1
  have hL : ListAt st.mem (p4CopyBuf ws eCap) S.copyBuf := hT ▸ hW.2.2.2.2.2.2.2.2.2.2
  have hme : st.mem (ws + 10 * eCap + 3 + 1 + i) = e := by
    have h := hL i hi
    simp only [p4CopyBuf] at h
    rw [show ws + 10 * eCap + 3 + 1 + i = ws + 10 * eCap + 4 + i by omega, h]
  -- The load of the edge into register `9` and the reset of register `11`.
  have hA9 : Runs P.w p ω (.assign 9 (.load (.bin .add (.bin .add (.reg 6) (.const 1))
      (.reg 8)))) st .normal { st with regs := Function.update st.regs 9 e } 7 :=
    runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
      (Expr.eval_reg_of_eq hr6) (Expr.eval_const h1w) (by omega)) (Expr.eval_reg_of_eq hr8)
      (by omega)) hme, rfl, rfl, rfl⟩
  set st₉ : State := { st with regs := Function.update st.regs 9 e } with hst₉
  have hA11 : Runs P.w p ω (.assign 11 (.const 0)) st₉ .normal
      { st₉ with regs := Function.update st₉.regs 11 0 } 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  set stB : State := { st₉ with regs := Function.update st₉.regs 11 0 } with hstB
  have hB : ∀ r, r ≠ 9 → r ≠ 11 → stB.regs r = st.regs r := fun r h9 h11 => by
    simp [hstB, hst₉, h9, h11]
  have hB9 : stB.regs 9 = e := by simp [hstB, hst₉]
  have hB11 : stB.regs 11 = 0 := by simp [hstB]
  have hos : stB.mem (oldS + e) = if e ∈ OS then 1 else 0 :=
    (hfr _ (by rcases ho_disj with h | h <;> omega)).trans (hOS e heCap)
  by_cases hcase : e ∈ OS
  · -- The edge was in the old output graph: read its walk and work on its edges.
    have hos1 : stB.mem (oldS + e) = 1 := by rw [hos]; simp [hcase]
    have hRepB : DSRepAt P b d x stB.mem :=
      dsRepAt_of_agree hRep (fun a ha => hfr a (hFootDisj a ha))
    obtain ⟨stF, cF, hrF, hmF, hregF, hF11, hwalk, hrange, hcF⟩ :=
      dleftFetch_runs (ω := ω) (hfWalk e) hw16
        ((hB 4 (by decide) (by decide)).trans hr4) ((hB 5 (by decide) (by decide)).trans hr5)
        hB9 hos1 (by omega) hRepB (hCopyG hcase) hFix hHeapW (by omega)
    set W := piTotal (d.state P) e with hW_def
    set ret := stF.regs 10 with hret
    have hheap : ∀ a, ret ≤ a → a < ret + (1 + 2 * W.length) → heapFoot x a := by
      intro a h1 h2
      exact hrange a h1 (by rw [mWalkEncode_length]; exact h2)
    have hout : ∀ j < W.length, ret + 1 + 2 * j < ws ∨ ws + p4WsSize eCap ≤ ret + 1 + 2 * j :=
      fun j hj => hFootDisj _ (Or.inr (hheap _ (by omega) (by omega)))
    have hesw : ∀ j < W.length, ret + 1 + 2 * j < 2 ^ P.w :=
      fun j hj => hHeapW _ (hheap _ (by omega) (by omega))
    have hes : ∀ j (hj : j < (W.map Prod.fst).length),
        mem₀ (ret + 1 + 2 * j) = (W.map Prod.fst)[j] := by
      intro j hj
      rw [List.length_map] at hj
      rw [← hfr _ (hout j hj), List.getElem_map]
      exact MWalkAt_step_edge hwalk hj
    have hesCap : ∀ e' ∈ W.map Prod.fst, e' < eCap := by
      intro e' he'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he'
      exact hWalkCap hcase q hq
    obtain ⟨stL, cL, hrL, hregL, hWL, hfrL, hcL⟩ := dleftWalkLoop_runs (ω := ω)
      (GE := GE) (HE := HE) (es := W.map Prod.fst) (S := T) (mem₀ := mem₀) (ret := ret)
      hfEdge hfPush hfMark hw16
      ((hregF 0 (by decide) (by decide)).trans ((hB 0 (by decide) (by decide)).trans hr0))
      ((hregF 1 (by decide) (by decide)).trans ((hB 1 (by decide) (by decide)).trans hr1))
      ((hregF 2 (by decide) (by decide)).trans ((hB 2 (by decide) (by decide)).trans hr2))
      ((hregF 3 (by decide) (by decide)).trans ((hB 3 (by decide) (by decide)).trans hr3))
      rfl (by rw [hF11, List.length_map])
      (by rw [hmF]; exact hW) (fun a ha => by rw [hmF]; exact hfr a ha) hGE hHE hes
      (by simpa using hout) (by simpa using hesw) hesCap hg_disj hh_disj hg_w hh_w hws_w
    refine ⟨stL, _, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hA9,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hA11,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrF, hrL, rfl⟩), rfl⟩), rfl⟩),
      fun r h9 h10 h11 h12 h13 h14 => ?_, ?_, hfrL, ?_⟩
    · rw [hregL r h12 h13 h14, hregF r h10 h11]
      exact hB r h9 h11
    · simpa [p4StepDleft, hcase] using hWL
    · simp only [List.length_map] at hcL
      simp only [p4DleftEdgeCost, spanPiWalkPtrCost] at hcF ⊢
      rw [← hW_def]
      omega
  · -- The edge was not in the old output graph: nothing to do.
    have hos0 : stB.mem (oldS + e) = 0 := by rw [hos]; simp [hcase]
    have hcond : (Expr.load (.bin .add (.reg 4) (.reg 9))).eval P.w stB = some 0 :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq
        ((hB 4 (by decide) (by decide)).trans hr4)) (Expr.eval_reg_of_eq hB9) (by omega)) hos0
    have hrF : Runs P.w p ω (asmFirstDleftFetch fWalk) stB .normal stB 6 :=
      runs_cond_iff.mpr ⟨0, 1, hcond, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    obtain ⟨stL, cL, hrL, hregL, hWL, hfrL, hcL⟩ := dleftWalkLoop_runs (ω := ω)
      (GE := GE) (HE := HE) (es := []) (S := T) (mem₀ := mem₀) (ret := stB.regs 10)
      hfEdge hfPush hfMark hw16
      ((hB 0 (by decide) (by decide)).trans hr0) ((hB 1 (by decide) (by decide)).trans hr1)
      ((hB 2 (by decide) (by decide)).trans hr2) ((hB 3 (by decide) (by decide)).trans hr3)
      rfl (by simpa using hB11) hW hfr hGE hHE (fun j hj => absurd hj (by simp))
      (fun j hj => absurd hj (by simp)) (fun j hj => absurd hj (by simp)) (by simp)
      hg_disj hh_disj hg_w hh_w hws_w
    refine ⟨stL, _, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hA9,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hA11,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrF, hrL, rfl⟩), rfl⟩), rfl⟩),
      fun r h9 _ h11 h12 h13 h14 => (hregL r h12 h13 h14).trans (hB r h9 h11), ?_, hfrL, ?_⟩
    · simpa [p4StepDleft, hcase] using hWL
    · simp only [List.length_nil] at hcL
      simp only [p4DleftEdgeCost]
      omega

/-! ## The run -/

public section

set_option maxHeartbeats 1600000 in
/-- **The scan of the walks of `D_left`.** From the workspace `S`, with the presence arrays of the
slot's new graph `GE`, of its new spanner `HE` and of the old output graph `OS`, and the spanner of
the slot at handle `b`, all outside the workspace, `asmFirstScanDleftStmt` leaves the workspace
`S.copyBuf.foldl (p4StepDleft GE HE OS (piTotal (d.state P))) S`, keeps every cell outside the
workspace, and costs at most the sum of `p4DleftEdgeCost P d e` over the copy buffer, plus `30`.
The walks are read only for the copied edges in `OS`, so only these edges must lie in the
spanner's graph and have walks with edges below `eCap`. -/
theorem asmFirstScanDleft_runs {P : DSParams}
    {fEdge fPush fMark bRead gEPres hEPres ws eCap oldS b pos : ℕ} {p : Program}
    (hfEdge : p.procs[fEdge]? = some (asmFirstP4EdgeStmt fPush fMark))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt)
    (hread : p.HasAt bRead spanReadoutProcs)
    {GE HE OS : Finset ℕ} {d : DSHist} {x : DynSpannerMeta P.L} {S : Phase4WS}
    {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ P.w)
    (hW : Phase4WSAt mem₀ ws eCap S)
    (hGE : ∀ e < eCap, mem₀ (gEPres + e) = if e ∈ GE then 1 else 0)
    (hHE : ∀ e < eCap, mem₀ (hEPres + e) = if e ∈ HE then 1 else 0)
    (hOS : ∀ e < eCap, mem₀ (oldS + e) = if e ∈ OS then 1 else 0)
    (hRep : DSRepAt P b d x mem₀)
    (hFix : b + dsFixedSize P.L P.vCap P.eCap < 2 ^ P.w)
    (hHeapW : ∀ a, heapFoot x a → a < 2 ^ P.w)
    (hFootDisj : ∀ a, metaFoot b x a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hCopyG : ∀ e ∈ S.copyBuf, e ∈ OS → e ∈ (d.state P).G.E)
    (hWalkCap : ∀ e ∈ S.copyBuf, e ∈ OS → ∀ q ∈ piTotal (d.state P) e, q.1 < eCap)
    (hg_disj : gEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ gEPres)
    (hh_disj : hEPres + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ hEPres)
    (ho_disj : oldS + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ oldS)
    (hg_w : gEPres + eCap < 2 ^ P.w) (hh_w : hEPres + eCap < 2 ^ P.w)
    (ho_w : oldS + eCap < 2 ^ P.w) (hws_w : ws + p4WsSize eCap < 2 ^ P.w) :
    ∃ st' cost,
      Runs P.w p ω (asmFirstScanDleftStmt fEdge (bRead + spanReadIdxPiWalkPtr))
        (startState [gEPres, hEPres, ws, eCap, oldS, b] mem₀ pos) (.returned 0) st' cost ∧
      Phase4WSAt st'.mem ws eCap
        (S.copyBuf.foldl (p4StepDleft GE HE OS (piTotal (d.state P))) S) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = mem₀ a) ∧
      cost ≤ (S.copyBuf.map (p4DleftEdgeCost P d)).sum + 30 := by
  classical
  have h0w : 0 < 2 ^ P.w := by omega
  have h1w : 1 < 2 ^ P.w := by omega
  have hws' : ws + 11 * eCap + 4 < 2 ^ P.w := by simp only [p4WsSize] at hws_w; omega
  have hcbLen : S.copyBuf.length ≤ eCap := copyBuf_length_le' hW
  have hcl : mem₀ (ws + 10 * eCap + 3) = S.copyBuf.length := by
    have h := hW.2.2.2.2.2.2.2.2.2.1
    simpa only [p4CopyLen] using h
  set s0 := startState [gEPres, hEPres, ws, eCap, oldS, b] mem₀ pos with hs0
  set s1 : State := { s0 with regs := Function.update s0.regs 6 (ws + 10 * eCap + 3) } with hs1
  set s2 : State := { s1 with regs := Function.update s1.regs 7 S.copyBuf.length } with hs2
  have hA6 : Runs P.w p ω (.assign 6 (.bin .add (.bin .add (.reg 2)
      (.bin .mul (.const 10) (.reg 3))) (.const 3))) s0 .normal s1 8 :=
    runs_assign_iff.mpr ⟨_, Expr.eval_add (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [s0, startState])) (Expr.eval_mul (Expr.eval_const
        (by omega)) (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega)) (by omega))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have hA7 : Runs P.w p ω (.assign 7 (.load (.reg 6))) s1 .normal s2 3 :=
    runs_assign_iff.mpr ⟨_, Expr.eval_load_of_eq
      (Expr.eval_reg_of_eq (v := ws + 10 * eCap + 3) (by simp [s1]))
      (by simpa [s1, s0, startState] using hcl), rfl, rfl, rfl⟩
  have hs2r : ∀ r, s2.regs r = if r = 7 then S.copyBuf.length else
      if r = 6 then ws + 10 * eCap + 3 else s0.regs r := fun r => by
    simp only [hs2, hs1, Function.update_apply]
  have hs2mem : s2.mem = mem₀ := by simp [s2, s1, s0, startState]
  let stepC : ℕ → ℕ := fun i =>
    if hi : i < S.copyBuf.length then p4DleftEdgeCost P d (S.copyBuf[i]'hi) - 9 else 0
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ r, r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 →
      st.regs r = s2.regs r) ∧ st.regs 8 = i ∧
    Phase4WSAt st.mem ws eCap
      ((S.copyBuf.take i).foldl (p4StepDleft GE HE OS (piTotal (d.state P))) S) ∧
    (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st.mem a = mem₀ a)
  have hloop := Triple.forRange_le (w := P.w) (p := p) (r := 8) (lo := .const 0) (hi := .reg 7)
    (body := asmFirstScanDleftBody fEdge (bRead + spanReadIdxPiWalkPtr))
    (P := fun st => st = s2) (Inv := Inv) stepC 0 S.copyBuf.length (Nat.zero_le _) h1w
    (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨Expr.eval_const h0w, fun r h8 _ _ _ _ _ _ => by simp [h8], by simp, ?_,
        fun a _ => by simp [hs2mem]⟩
      simpa [hs2mem] using hW)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.1 7 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans (by simp [hs2r])))
    (fun i _ hi st ω' hI => by
      obtain ⟨hregs, h8, hWi, hfri⟩ := hI
      have hfix : ∀ r, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 →
          r ≠ 14 → st.regs r = s0.regs r := fun r h6 h7 h8 h9 h10 h11 h12 h13 h14 => by
        rw [hregs r h8 h9 h10 h11 h12 h13 h14, hs2r]; simp [h6, h7]
      have hgo := fun r (h : r < 6) => hfix r (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      obtain ⟨st', c, hr, hregs', hW', hfr', hc⟩ := scanDleftBody_runs (ω := ω') (i := i)
        (GE := GE) (HE := HE) (OS := OS) (S := S)
        (T := (S.copyBuf.take i).foldl (p4StepDleft GE HE OS (piTotal (d.state P))) S)
        (mem₀ := mem₀) hfEdge hfPush hfMark
        (fun e => spanPiWalkPtr_meetsContract (P := P) (b := b) (e := e) (s := d) (x := x) hread)
        hw16 ((hgo 0 (by decide)).trans (by simp [s0, startState]))
        ((hgo 1 (by decide)).trans (by simp [s0, startState]))
        ((hgo 2 (by decide)).trans (by simp [s0, startState]))
        ((hgo 3 (by decide)).trans (by simp [s0, startState]))
        ((hgo 4 (by decide)).trans (by simp [s0, startState]))
        ((hgo 5 (by decide)).trans (by simp [s0, startState]))
        ((hregs 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans (by simp [hs2r])) h8 hi hWi
        (foldl_p4StepDleft_copyBuf GE HE OS _ _ S) hfri hGE hHE hOS hRep hFix hHeapW hFootDisj
        (hCopyG _ (List.getElem_mem hi)) (hWalkCap _ (List.getElem_mem hi))
        hg_disj hh_disj ho_disj hg_w hh_w ho_w hws_w
      refine ⟨.normal, st', c, hr, ⟨⟨fun r h8' h9 h10 h11 h12 h13 h14 => ?_, by simp, ?_,
        hfr'⟩, (hregs' 8 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide)).trans h8⟩, ?_⟩
      · show Function.update st'.regs 8 (i + 1) r = s2.regs r
        rw [Function.update_of_ne h8', hregs' r h9 h10 h11 h12 h13 h14]
        exact hregs r h8' h9 h10 h11 h12 h13 h14
      · rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
        simpa using hW'
      · show c ≤ stepC i
        simp only [stepC, hi, ↓reduceDIte]
        omega)
  have key : ∃ o st' c, Runs P.w p ω (asmFirstScanDleftStmt fEdge (bRead + spanReadIdxPiWalkPtr))
      s0 o st' c ∧
      (o = .returned 0 ∧
        Phase4WSAt st'.mem ws eCap
          (S.copyBuf.foldl (p4StepDleft GE HE OS (piTotal (d.state P))) S) ∧
        (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = mem₀ a)) ∧
      0 + c ≤ (S.copyBuf.map (p4DleftEdgeCost P d)).sum + 30 := by
    unfold asmFirstScanDleftStmt
    refine runs_seq_block_le (R := fun st => st = s1) ⟨s1, 8, hA6, rfl, le_rfl⟩ ?_
    rintro _ rfl
    refine runs_seq_block_le (R := fun st => st = s2) ⟨s2, 3, hA7, rfl, le_rfl⟩ ?_
    rintro _ rfl
    refine runs_seq_triple_le hloop rfl ?_
    rintro st₁ ⟨-, -, hWf, hfrf⟩
    rw [List.take_length] at hWf
    refine ⟨.returned 0, st₁, 2, runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩,
      ⟨rfl, hWf, hfrf⟩, ?_⟩
    have hrc : rangeCost stepC 0 S.copyBuf.length =
        (S.copyBuf.map fun e => p4DleftEdgeCost P d e - 9).sum :=
      rangeCost_getElem_eq_map_sum' S.copyBuf (fun e => p4DleftEdgeCost P d e - 9)
    have hsum := sum_map_add_nine_le S.copyBuf (fun e => p4DleftEdgeCost P d e - 9)
      (p4DleftEdgeCost P d) (fun e => by simp only [p4DleftEdgeCost]; omega)
    rw [hrc]
    simp only [Expr.size, Nat.sub_zero]
    omega
  obtain ⟨o, st', c, hr, ⟨rfl, hWf, hfrf⟩, hc⟩ := key
  exact ⟨st', c, hr, hWf, hfrf, by omega⟩

end

end MinCostFlow.SparseCore.Program
