module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4LoopDefs
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSlotScanNew

import WordRAM.Tactic

/-!
# Phase 4 on one new slot (`AssemblyFirstStepP4New`)

Phase 2 makes a new spanner for each pair that becomes active. Phase 4 must then mark the edges
of its graph in the workspace and write the walks of its edges into the embedding table. The
procedure `asmFirstP4NewStmt fScanNew fCopy`, with arguments `[spanTbl, slot, ws, eCap, embH, h]`,
does this for one new slot. It reads the handle of the slot from the table of the spanners, runs
the scan of the edge list of the slot's graph (`asmFirstScanNewSlotStmt`), which marks every
edge and puts the edges that are not in the spanner into the copy buffer, and then copies the
walks of the edges of the copy buffer into the embedding table (`asmFirstCopySlotListStmt`).

`asmFirstP4New_runs` gives `P4NewPost`. The edge list of the graph is known only up to order, so
the post names it. Its cost is at most `p4NewWork`, which depends only on the model: the copy
buffer holds distinct edges of the graph that are not in the spanner (`p4StepNew_copyBuf`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

/-! ## The procedure and what it leaves -/

@[expose] public section

/-- The two calls of `asmFirstP4NewStmt`: the scan of the edge list of the graph (at
`gEPres + eCap'`, with its length at `b + 9`), then the copy of the walks of the copy buffer. -/
def asmFirstP4NewTail (fScanNew fCopy : ℕ) : Stmt :=
  .call 14 fScanNew [.bin .add (.reg 11) (.reg 10), .load (.bin .add (.reg 8) (.const 9)),
    .reg 12, .reg 2, .reg 3] ;;
  .call 14 fCopy [.reg 4, .reg 0, .reg 1, .bin .add (.reg 13) (.const 1), .load (.reg 13),
    .reg 5] ;;
  .ret (.reg 14)

/-- **Phase 4 on one new slot**, `[spanTbl, slot, ws, eCap, embH, h]`. Registers `8` to `13` hold
the handle `b` of the slot, the caps of its spanner, the places of the presence arrays of its
graph and of its spanner, and the place of the length of the copy buffer. -/
def asmFirstP4NewStmt (fScanNew fCopy : ℕ) : Stmt :=
  .assign 8 (.load (.bin .add (.reg 0) (.reg 1))) ;;
  .assign 9 (.load (.bin .add (.reg 8) (.const 3))) ;;
  .assign 10 (.load (.bin .add (.reg 8) (.const 4))) ;;
  .assign 11 (.bin .add (.reg 8) (.bin .add (.const 10) (.bin .mul (.const 7) (.reg 9)))) ;;
  .assign 12 (.bin .add (.reg 11) (.bin .add (.const 4) (.bin .add (.bin .mul (.const 7) (.reg 9))
    (.bin .mul (.const 9) (.reg 10))))) ;;
  .assign 13 (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 10) (.reg 3))) (.const 3)) ;;
  asmFirstP4NewTail fScanNew fCopy

/-- The steps of Phase 4 on a new slot `s` with history `d`: the scan of the edges of its graph
and the copy of the walks of the edges that are not in its spanner. -/
noncomputable def p4NewWork (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (s : ℕ)
    (d : DSHist) : ℕ :=
  135 * (d.state P).G.E.card +
    142 * ((d.state P).G.E \ (d.state P).H.E).sum
      (fun e => Read.walkWords (slotWalk P S6 s e) + (if d.Us = [] then 0 else P.L) + 2) + 400

/-- What Phase 4 leaves on the new slot `s`, whose history is `d`. There is a list `gL` of the
edges of the graph of `d`, such that the workspace holds `S` after the scan of `gL`
(`p4StepNew`), the embedding table holds the walks of the edges of the copy buffer, the heap
pointer grows by their words, the spanners are kept, and so are the cells below `h` outside the
table and the workspace. The cost is at most `p4NewWork`. -/
def P4NewPost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl s ws eCap embH h : ℕ) (d : DSHist)
    (S : Phase4WS) (v : EmbView) (y : EmbConc) (mem₀ : ℕ → ℕ) (o : Outcome) (st' : State) :
    Prop :=
  ∃ gL : List ℕ, gL.Nodup ∧ gL.toFinset = (d.state P).G.E ∧
    o = .returned (h + slotListWalkWords P S6 s
      (gL.foldl (p4StepNew (d.state P).H.E) { S with copyBuf := [] }).copyBuf) ∧
    Phase4WSAt st'.mem ws eCap (gL.foldl (p4StepNew (d.state P).H.E) { S with copyBuf := [] }) ∧
    (∃ y', (embRep eCap).rep embH (v.apply (slotChange P S6 s
        (gL.foldl (p4StepNew (d.state P).H.E) { S with copyBuf := [] }).copyBuf)) y' st'.mem ∧
      ∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨
        (h ≤ a ∧ a < h + slotListWalkWords P S6 s
          (gL.foldl (p4StepNew (d.state P).H.E) { S with copyBuf := [] }).copyBuf)) ∧
    (bucketSpannerRep P cap).rep spanTbl S6 x6 st'.mem ∧
    ZeroFrom st'.mem (h + slotListWalkWords P S6 s
      (gL.foldl (p4StepNew (d.state P).H.E) { S with copyBuf := [] }).copyBuf) ∧
    ∀ a < h, ¬ embFoot eCap embH y a → (a < ws ∨ ws + p4WsSize eCap ≤ a) → st'.mem a = mem₀ a

end

public section

theorem asmFirstP4NewStmt_noRand (fScanNew fCopy : ℕ) :
    (asmFirstP4NewStmt fScanNew fCopy).NoRand := by
  simp [asmFirstP4NewStmt, asmFirstP4NewTail, Stmt.NoRand]

/-- The copy buffer after the scan of a new slot has no repeated edge, and its edges are edges of
the list that are not in `HE`, since the scan starts with an empty buffer and every push checks
the seen flags (`pushCopy`). -/
theorem p4StepNew_copyBuf (HE : Finset ℕ) (gL : List ℕ) (S : Phase4WS) :
    (gL.foldl (p4StepNew HE) { S with copyBuf := [] }).copyBuf.Nodup ∧
      ∀ e ∈ (gL.foldl (p4StepNew HE) { S with copyBuf := [] }).copyBuf, e ∈ gL ∧ e ∉ HE := by
  classical
  let Q : Phase4WS → Prop := fun T => CopyBufOK T ∧ ∀ e ∈ T.copyBuf, e ∈ gL ∧ e ∉ HE
  have hstep : ∀ T e, e ∈ gL → Q T → Q (p4StepNew HE T e) := by
    intro T e he hT
    have hQ : ∀ T' : Phase4WS, T'.copyBuf = T.copyBuf → T'.seenCopy = T.seenCopy → Q T' :=
      fun T' hc hs' => ⟨copyBufOK_of_eq hT.1 hc hs', by rw [hc]; exact hT.2⟩
    have key : ∀ T1 : Phase4WS, T1.copyBuf = T.copyBuf → T1.seenCopy = T.seenCopy →
        Q (if e ∉ HE then pushCopy T1 e else T1) := by
      intro T1 hc1 hs1
      by_cases hc : e ∈ HE
      · simp only [hc, not_true_eq_false, ↓reduceIte]; exact hQ T1 hc1 hs1
      · simp only [hc, not_false_eq_true, ↓reduceIte]
        refine ⟨copyBufOK_pushCopy (hQ T1 hc1 hs1).1 e, fun x hx => ?_⟩
        rcases mem_pushCopy_copyBuf hx with h | rfl
        · exact (hQ T1 hc1 hs1).2 x h
        · exact ⟨he, hc⟩
    refine key _ ?_ ?_ <;> rfl
  have h := foldl_keeps_mem Q _ gL hstep { S with copyBuf := [] }
    ⟨⟨List.nodup_nil, fun _ h => by simp at h⟩, fun _ h => by simp at h⟩
  exact ⟨h.1.1, h.2⟩

end

/-! ## The run -/

/-- A call whose body is given by a run, at the start of a sequence. -/
private theorem runs_seq_callRuns_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
    {args : List Expr} {s : Stmt} {st : State} {vs : List ℕ} {body : Stmt} {k T : ℕ}
    {Q : Outcome → State → Prop}
    (hargs : evalArgs w st args = some vs) (hb : p.procs[f]? = some body) {o₁ : Outcome}
    {st₁ : State} {c₁ : ℕ} (h₁ : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s { st₁ with regs := Function.update st.regs r o₁.value }
      o st' c₂ ∧ Q o st' ∧ (k + argsSize args + c₁ + 2) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest
  exact ⟨o, st', (argsSize args + c₁ + 1) + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, c₂,
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hb, h₁, rfl, rfl, rfl⟩, hr₂, rfl⟩), hq,
    by omega⟩

set_option maxHeartbeats 1600000 in
/-- The two calls of Phase 4 on one new slot, from a state whose registers hold the arguments,
the handle `b` of the slot (register `8`), the edge cap of its spanner (register `10`), the
places of the presence arrays of its graph and of its spanner (registers `11` and `12`) and the
place of the length of the copy buffer (register `13`). -/
private theorem p4NewTail_runs {P : DSParams} {cap : ℕ} {fScanNew fCopy fPush bRead bCopy : ℕ}
    {p : Program}
    (hfN : p.procs[fScanNew]? = some (asmFirstScanNewSlotStmt fPush))
    (hfC : p.procs[fCopy]? = some (asmFirstCopySlotListStmt bCopy (bRead + spanReadIdxPiWalkPtr)))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hcopy : p.HasAt bCopy [copyWords]) (hread : p.HasAt bRead spanReadoutProcs)
    {spanTbl s ws eCap embH h b : ℕ} {S6 : BucketSpannerState cap}
    {x6 : BucketSpannerMeta P.L cap} (hs : s < cap) {d : DSHist} (hSj : S6 ⟨s, hs⟩ = some d)
    {m : DSHist × DynSpannerMeta P.L} (hxm : x6.slots ⟨s, hs⟩ = some (b, m))
    {S : Phase4WS} {v : EmbView} {y : EmbConc} {st : State} {ω : ℕ → Bool} {k T : ℕ}
    (hw16 : 16 ≤ 2 ^ P.w)
    (hr0 : st.regs 0 = spanTbl) (hr1 : st.regs 1 = s) (hr2 : st.regs 2 = ws)
    (hr3 : st.regs 3 = eCap) (hr4 : st.regs 4 = embH) (hr5 : st.regs 5 = h)
    (hr8 : st.regs 8 = b) (hr10 : st.regs 10 = P.eCap)
    (hr11 : st.regs 11 = dgEPresBase (dsGPtr b) P.vCap)
    (hr12 : st.regs 12 = dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap)
    (hr13 : st.regs 13 = ws + 10 * eCap + 3)
    (hW : Phase4WSAt st.mem ws eCap S)
    (hS6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 st.mem)
    (hEmb : (embRep eCap).rep embH v y st.mem)
    (hGcap : ∀ e ∈ (d.state P).G.E, e < eCap) (heCap : eCap ≤ P.eCap)
    (hWsH : ws + p4WsSize eCap ≤ h)
    (hSpanF : ∀ a, bucketFoot spanTbl x6 a → a < h)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < h)
    (hSpanWs : ∀ a, bucketFoot spanTbl x6 a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hEmbWs : ∀ a, embFoot eCap embH y a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanTbl x6 a)
    (hz : ZeroFrom st.mem h)
    (hsp : h + (d.state P).G.E.sum (fun e => Read.walkWords (slotWalk P S6 s e)) < 2 ^ P.w)
    (hT : k + (p4NewWork P S6 s d - 60) ≤ T) :
    ∃ o st' c, Runs P.w p ω (asmFirstP4NewTail fScanNew fCopy) st o st' c ∧
      P4NewPost P S6 x6 spanTbl s ws eCap embH h d S v y st.mem o st' ∧ k + c ≤ T := by
  classical
  have h0w : 0 < 2 ^ P.w := by omega
  have h1w : 1 < 2 ^ P.w := by omega
  have hsz : p4WsSize eCap = 11 * eCap + 4 := rfl
  -- The spanner of the slot and the places of its arrays.
  have hslot := hS6.1 ⟨s, hs⟩
  rw [hSj, hxm] at hslot
  obtain ⟨-, ⟨-, hdsRep, -⟩, -⟩ := hslot
  have hState := hdsRep.2.2.2.2.2.2.2.1
  have hvc : m.2.vCap = P.vCap := hState.1
  have hec : m.2.eCap = P.eCap := hState.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hDG, hDH, -⟩ := hState
  have hfixH : b + dsFixedSize P.L P.vCap P.eCap ≤ h := slot_fixedSize_le_h hS6 hSj hxm hSpanF
  have hhW : h < 2 ^ P.w := by omega
  have hB := embRefresh_fixedBounds (b := b) (L := P.L) (vCap := P.vCap) (eCap := P.eCap)
  have hhP_le : dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + P.eCap ≤
      b + dsFixedSize P.L P.vCap P.eCap := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hgP : dgEPresBase (dsGPtr b) P.vCap = b + 10 + 7 * P.vCap := by
    simp only [dgEPresBase, dsGPtr, dsHdrSize]
  have hhP : dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap =
      dgEPresBase (dsGPtr b) P.vCap + (4 + 7 * P.vCap + 9 * P.eCap) := by
    simp only [dgEPresBase, dsHPtr, dsGPtr, dsHdrSize, dynGraphSize]; omega
  have hgL_eq : dgEListBase (dsGPtr b) P.vCap P.eCap = dgEPresBase (dsGPtr b) P.vCap + P.eCap := by
    simp only [dgEListBase, dgEPresBase]
  have hm_eq : dsGPtr b + dgMOff = b + 9 := by simp only [dsGPtr, dsHdrSize, dgMOff]
  have hfixFoot : ∀ a, b ≤ a → a < b + dsFixedSize P.L P.vCap P.eCap → bucketFoot spanTbl x6 a :=
    fun a h1 h2 => Or.inr ⟨⟨s, hs⟩, b, m, hxm, Or.inl ⟨h1, by rw [hvc, hec]; exact h2⟩⟩
  have hfixWs : b + dsFixedSize P.L P.vCap P.eCap ≤ ws ∨ ws + p4WsSize eCap ≤ b :=
    block_avoid (by omega) (by omega)
      (fun i hi => hSpanWs _ (hfixFoot _ (by omega) (by omega)))
  -- The edge list of the graph.
  obtain ⟨gL, hgLlen, hgLnd, hgLmem, hgLat, -⟩ := hDG.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmM : st.mem (b + 9) = gL.length := by rw [← hm_eq, hgLlen]; exact hDG.2.2.2.2.2.2.1
  have hgLE : gL.toFinset = (d.state P).G.E := by ext e; simp [hgLmem]
  have hgL_le : gL.length ≤ P.eCap := by
    rw [← List.toFinset_card_of_nodup hgLnd]
    calc gL.toFinset.card ≤ (Finset.range P.eCap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr
            (hDG.2.2.1 e ((hgLmem e).mp (List.mem_toFinset.mp he)))
      _ = P.eCap := Finset.card_range _
  have hg_disj : dgEPresBase (dsGPtr b) P.vCap + P.eCap + gL.length ≤ ws ∨
      ws + p4WsSize eCap ≤ dgEPresBase (dsGPtr b) P.vCap + P.eCap := by
    rcases hfixWs with h' | h'
    · left; omega
    · right; omega
  have hh_disj : dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + eCap ≤ ws ∨
      ws + p4WsSize eCap ≤ dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap := by
    rcases hfixWs with h' | h'
    · left; omega
    · right; omega
  have hg_w : dgEPresBase (dsGPtr b) P.vCap + P.eCap + gL.length < 2 ^ P.w := by omega
  have hh_w : dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + eCap < 2 ^ P.w := by omega
  have hws_w : ws + p4WsSize eCap < 2 ^ P.w := by omega
  have hHE : ∀ e < eCap, st.mem (dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + e) =
      if e ∈ (d.state P).H.E then 1 else 0 :=
    fun e he => hDH.2.2.2.2.2.2.2.2.2.2.2.1 e (by omega)
  have hGL : ListAt st.mem (dgEPresBase (dsGPtr b) P.vCap + P.eCap) gL := by
    rw [← hgL_eq]; exact hgLat
  -- The scan of the edge list.
  obtain ⟨st₁, c₁, hr₁, hW₁, hfr₁, hc₁⟩ := asmFirstScanNewSlot_runs (pos := st.pos) (ω := ω)
    (HE := (d.state P).H.E) (S₀ := S) hfPush hw16 hW hGL
    (fun e he => hGcap e ((hgLmem e).mp he)) hHE hg_disj hh_disj hg_w hh_w hws_w
  have hM₁ : ∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st₁.mem a = st.mem a := hfr₁
  -- The copy of the walks.
  have hcb := p4StepNew_copyBuf (d.state P).H.E gL S
  set eL := (gL.foldl (p4StepNew (d.state P).H.E) { S with copyBuf := [] }).copyBuf with heL
  have heL_len : eL.length ≤ eCap := phase4WSAt_copyBuf_length_le hW₁
  have hcl₁ : st₁.mem (ws + 10 * eCap + 3) = eL.length := hW₁.2.2.2.2.2.2.2.2.2.1
  have heL_at : ListAt st₁.mem (ws + 10 * eCap + 3 + 1) eL := by
    intro i hi
    have h' := hW₁.2.2.2.2.2.2.2.2.2.2 i hi
    simp only [p4CopyBuf] at h'
    rw [show ws + 10 * eCap + 3 + 1 + i = ws + 10 * eCap + 4 + i by omega]
    exact h'
  have heL_sub : ∀ e ∈ eL, e ∈ (d.state P).G.E ∧ e < eCap := fun e he =>
    ⟨(hgLmem e).mp (hcb.2 e he).1, hGcap e ((hgLmem e).mp (hcb.2 e he).1)⟩
  have hS6₁ : (bucketSpannerRep P cap).rep spanTbl S6 x6 st₁.mem :=
    (bucketSpannerRep_local P cap spanTbl S6 x6 st.mem st₁.mem
      (fun a ha => (hM₁ a (hSpanWs a ha)).symm)).1 hS6
  have hEmb₁ : (embRep eCap).rep embH v y st₁.mem :=
    (embRep_local eCap embH v y st.mem st₁.mem (fun a ha => (hM₁ a (hEmbWs a ha)).symm)).1 hEmb
  have hz₁ : ZeroFrom st₁.mem h := fun a ha => (hM₁ a (Or.inr (by omega))).trans (hz a ha)
  have hwords : slotListWalkWords P S6 s eL ≤
      (d.state P).G.E.sum (fun e => Read.walkWords (slotWalk P S6 s e)) :=
    slotListWalkWords_le_sum P S6 s hcb.1 (fun e he => (heL_sub e he).1)
  obtain ⟨o₂, st₂, c₂, y', hr₂, hEmb₂, hov, hz₂, hfr₂, hfoot₂, hc₂⟩ :=
    asmFirstCopySlotList_runs (eListPtr := ws + 10 * eCap + 3 + 1) (pos := st₁.pos) (ω := ω)
      hcopy hread hs hSj hw16 hEmb₁ hS6₁ heL_at (by omega) heL_sub hEmbF hSpanF hDisj
      (fun a h1 h2 hf => by rcases hEmbWs a hf with h' | h' <;> omega) hz₁ (by omega)
  -- The work on the copy buffer is at most the work on the edges not in the spanner.
  have hwork : slotListCopyWork P S6 s d eL ≤ ((d.state P).G.E \ (d.state P).H.E).sum
      (fun e => Read.walkWords (slotWalk P S6 s e) + (if d.Us = [] then 0 else P.L) + 2) :=
    list_sum_le_finset_sum _ hcb.1 (fun e he => Finset.mem_sdiff.mpr
      ⟨(heL_sub e he).1, (hcb.2 e he).2⟩)
  have hb9 : b + 9 < 2 ^ P.w := by
    have := hB.2.2.2.2.2.2.2.2.2.2.2.1; rw [hm_eq] at this; omega
  have hcard : gL.length = (d.state P).G.E.card := by
    rw [← hgLE, List.toFinset_card_of_nodup hgLnd]
  -- The runs of the calls.
  unfold asmFirstP4NewTail
  refine runs_seq_callRuns_le (by eval_expr) hfN hr₁ ?_
  refine runs_seq_callRuns_le (by eval_expr) hfC hr₂ ?_
  wram_step
  · have hin : ∀ a, ws ≤ a → a < ws + p4WsSize eCap → st₂.mem a = st₁.mem a := fun a h1 h2 =>
      hfr₂ a (by omega) (fun hf => by rcases hEmbWs a hf with h' | h' <;> omega)
    refine ⟨gL, hgLnd, hgLE, by rw [hov], phase4WSAt_of_agree hW₁ hin, ⟨y', hEmb₂, ?_⟩, ?_, ?_,
      ?_⟩
    · rw [← hov]; exact hfoot₂
    · exact (bucketSpannerRep_local P cap spanTbl S6 x6 st₁.mem st₂.mem
        (fun a ha => (hfr₂ a (hSpanF a ha) (fun hf => hDisj a hf ha)).symm)).1 hS6₁
    · rw [← hov]; exact hz₂
    · intro a ha hne hout
      exact (hfr₂ a ha hne).trans (hM₁ a hout)
  · unfold p4NewWork at hT
    wram_cost

public section

set_option maxHeartbeats 1600000 in
/-- **Phase 4 on one new slot.** The slot `s` of the spanners at `spanTbl` holds the history `d`,
whose graph has its edges below `eCap`. The spanners and the embedding at `embH` lie below the
heap pointer `h` and outside the workspace at `ws`, which lies below `h`, and they are apart.
There is room for the walks of all edges of the graph. Then `asmFirstP4NewStmt` ends in
`P4NewPost` and costs at most `p4NewWork`. -/
theorem asmFirstP4New_runs {P : DSParams} {cap : ℕ} {fScanNew fCopy fPush bRead bCopy : ℕ}
    {p : Program}
    (hfN : p.procs[fScanNew]? = some (asmFirstScanNewSlotStmt fPush))
    (hfC : p.procs[fCopy]? = some (asmFirstCopySlotListStmt bCopy (bRead + spanReadIdxPiWalkPtr)))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hcopy : p.HasAt bCopy [copyWords]) (hread : p.HasAt bRead spanReadoutProcs)
    {spanTbl s ws eCap embH h pos : ℕ} {S6 : BucketSpannerState cap}
    {x6 : BucketSpannerMeta P.L cap} (hs : s < cap) {d : DSHist} (hSj : S6 ⟨s, hs⟩ = some d)
    {S : Phase4WS} {v : EmbView} {y : EmbConc} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ P.w)
    (hW : Phase4WSAt mem₀ ws eCap S)
    (hS6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem₀)
    (hEmb : (embRep eCap).rep embH v y mem₀)
    (hGcap : ∀ e ∈ (d.state P).G.E, e < eCap) (heCap : eCap ≤ P.eCap)
    (hWsH : ws + p4WsSize eCap ≤ h)
    (hSpanF : ∀ a, bucketFoot spanTbl x6 a → a < h)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < h)
    (hSpanWs : ∀ a, bucketFoot spanTbl x6 a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hEmbWs : ∀ a, embFoot eCap embH y a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanTbl x6 a)
    (hz : ZeroFrom mem₀ h)
    (hsp : h + (d.state P).G.E.sum (fun e => Read.walkWords (slotWalk P S6 s e)) < 2 ^ P.w) :
    ∃ o st' c, Runs P.w p ω (asmFirstP4NewStmt fScanNew fCopy)
        (startState [spanTbl, s, ws, eCap, embH, h] mem₀ pos) o st' c ∧
      P4NewPost P S6 x6 spanTbl s ws eCap embH h d S v y mem₀ o st' ∧
      c ≤ p4NewWork P S6 s d := by
  classical
  have h0w : 0 < 2 ^ P.w := by omega
  have h1w : 1 < 2 ^ P.w := by omega
  have hslot := hS6.1 ⟨s, hs⟩
  rw [hSj] at hslot
  rcases hxm : x6.slots ⟨s, hs⟩ with _ | ⟨b, m⟩
  · rw [hxm] at hslot; exact False.elim hslot
  rw [hxm] at hslot
  obtain ⟨hmb, ⟨-, hdsRep, -⟩, -⟩ := hslot
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmV, hmE, -⟩ := hdsRep.2.2.2.2.2.2.2.1
  have hfixH : b + dsFixedSize P.L P.vCap P.eCap ≤ h := slot_fixedSize_le_h hS6 hSj hxm hSpanF
  have hhW : h < 2 ^ P.w := by omega
  have hB := embRefresh_fixedBounds (b := b) (L := P.L) (vCap := P.vCap) (eCap := P.eCap)
  have hhP_le : dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + P.eCap ≤
      b + dsFixedSize P.L P.vCap P.eCap := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hhP : dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap =
      b + (10 + 7 * P.vCap) + (4 + (7 * P.vCap + 9 * P.eCap)) := by
    simp only [dgEPresBase, dsHPtr, dsGPtr, dsHdrSize, dynGraphSize]; omega
  have hbig : b + (10 + 7 * P.vCap) + (4 + (7 * P.vCap + 9 * P.eCap)) + P.eCap < 2 ^ P.w := by
    omega
  have hspan_lt : spanTbl + s < h := hSpanF _ (Or.inl ⟨by omega, by omega⟩)
  have hws_w : ws + 10 * eCap + 3 < 2 ^ P.w := by simp only [p4WsSize] at hWsH; omega
  set s0 := startState [spanTbl, s, ws, eCap, embH, h] mem₀ pos with hs0
  have hs0_0 : s0.regs 0 = spanTbl := by simp [s0, startState]
  have hs0_1 : s0.regs 1 = s := by simp [s0, startState]
  have hs0_2 : s0.regs 2 = ws := by simp [s0, startState]
  have hs0_3 : s0.regs 3 = eCap := by simp [s0, startState]
  have hm_b : s0.mem (spanTbl + s) = b := hmb
  have hm_v : s0.mem (b + 3) = P.vCap := hmV
  have hm_e : s0.mem (b + 4) = P.eCap := hmE
  have hm_v' : s0.mem (s0.mem (spanTbl + s) + 3) = P.vCap := by rw [hm_b]; exact hm_v
  have hm_e' : s0.mem (s0.mem (spanTbl + s) + 4) = P.eCap := by rw [hm_b]; exact hm_e
  have key : ∃ o st' c, Runs P.w p ω (asmFirstP4NewStmt fScanNew fCopy) s0 o st' c ∧
      P4NewPost P S6 x6 spanTbl s ws eCap embH h d S v y mem₀ o st' ∧
      0 + c ≤ p4NewWork P S6 s d := by
    unfold asmFirstP4NewStmt
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    refine p4NewTail_runs hfN hfC hfPush hcopy hread hs hSj hxm hw16
      (by simp [hs0_0]) (by simp [hs0_1]) (by simp [hs0_2]) (by simp [hs0_3])
      (by simp [s0, startState]) (by simp [s0, startState]) (by simp [hm_b])
      (by simp [hm_b, hm_e])
      (by simp only [dgEPresBase, dsGPtr, dsHdrSize]; simp [hm_b, hm_v]; omega)
      (by simp [hhP, hm_b, hm_v, hm_e])
      (by simp [hs0_2, hs0_3])
      hW hS6 hEmb hGcap heCap hWsH hSpanF hEmbF hSpanWs hEmbWs hDisj hz hsp ?_
    unfold p4NewWork
    wram_cost
  obtain ⟨o, st', c, hr, hq, hc⟩ := key
  exact ⟨o, st', c, hr, hq, by omega⟩

end

end MinCostFlow.SparseCore.Program
