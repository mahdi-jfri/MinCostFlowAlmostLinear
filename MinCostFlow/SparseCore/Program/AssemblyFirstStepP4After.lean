module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4TaskDefs
public import MinCostFlow.SparseCore.Program.SpanBucketInit
public import MinCostFlow.SparseCore.Program.ReadEmbOps

import WordRAM.Tactic

/-!
# The run of the work after the update of one slot (`AssemblyFirstStepP4After`)

`asmFirstP4After_runs` proves what `asmFirstP4AfterStmt` does (see
`AssemblyFirstStepP4TaskDefs.lean`). The slot's spanner has just taken its batch, and the header
of its outputs `U_H`, `D` and `R` lies at `hOut`, after the workspace. The procedure reads the
handle of the slot from the table of the spanners, empties the copy buffer, runs the scans of
`U_H`, `D`, `R` and of the walks of `D_left`, and copies the walks of the copied edges into the
embedding. The result is `P4AfterPost`.

The proof has two parts. `p4AfterTail_runs` runs the five calls from any state whose registers
hold the handle, the presence arrays and the place of the copy buffer. The main lemma runs the
seven statements before the calls and then uses `p4AfterTail_runs`. In both, every scan writes
only the workspace, and all the data the next call reads (the spanners, the embedding, the
outputs, the old output graph) lies outside the workspace, so it is kept.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

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

/-- Each cell of a block that lies on one side of the workspace is outside the workspace. -/
private theorem out_of_block {ws k x n : ℕ} (hx : x + n ≤ ws ∨ ws + k ≤ x) :
    ∀ i < n, x + i < ws ∨ ws + k ≤ x + i := by
  intro i hi
  rcases hx with hx | hx <;> omega

set_option maxHeartbeats 1600000 in
/-- The five calls of the work after the update, from a state whose registers hold the arguments,
the handle `b` of the slot (register `8`), the places of the presence arrays of its graph and of
its spanner (registers `11` and `12`) and the place of the length of the copy buffer (register
`13`), and whose memory agrees with `mem₀` outside the workspace and holds the workspace `S` with
an empty copy buffer. -/
private theorem p4AfterTail_runs {P : DSParams} {cap : ℕ}
    {fScanUH fScanD fScanR fDleft fCopy fEdge fPush fMark bRead bCopy : ℕ} {p : Program}
    (hfUH : p.procs[fScanUH]? = some (asmFirstScanSlotUHStmt fEdge))
    (hfD : p.procs[fScanD]? = some (asmFirstScanSlotDStmt fPush fMark))
    (hfR : p.procs[fScanR]? = some (asmFirstScanSlotRStmt fPush))
    (hfDl : p.procs[fDleft]? = some (asmFirstScanDleftStmt fEdge (bRead + spanReadIdxPiWalkPtr)))
    (hfC : p.procs[fCopy]? = some (asmFirstCopySlotListStmt bCopy (bRead + spanReadIdxPiWalkPtr)))
    (hfEdge : p.procs[fEdge]? = some (asmFirstP4EdgeStmt fPush fMark))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt)
    (hcopy : p.HasAt bCopy [copyWords]) (hread : p.HasAt bRead spanReadoutProcs)
    {spanTbl s hOut ws eCap oldS embH h b : ℕ} {S6 : BucketSpannerState cap}
    {x6 : BucketSpannerMeta P.L cap} (hs : s < cap) {d : DSHist} (hSj : S6 ⟨s, hs⟩ = some d)
    {m : DSHist × DynSpannerMeta P.L} (hxm : x6.slots ⟨s, hs⟩ = some (b, m))
    {OS : Finset ℕ} {S : Phase4WS} {v : EmbView} {y : EmbConc}
    {uhPtr uhWords dPtr rPtr : ℕ} {UH : List Update} {Hb : MGraph} {dL rL : List ℕ}
    {mem₀ : ℕ → ℕ} {st : State} {ω : ℕ → Bool} {k T : ℕ}
    (hw16 : 16 ≤ 2 ^ P.w)
    (hr0 : st.regs 0 = spanTbl) (hr1 : st.regs 1 = s) (hr2 : st.regs 2 = hOut)
    (hr3 : st.regs 3 = ws) (hr4 : st.regs 4 = eCap) (hr5 : st.regs 5 = oldS)
    (hr6 : st.regs 6 = embH) (hr7 : st.regs 7 = h) (hr8 : st.regs 8 = b)
    (hr11 : st.regs 11 = dgEPresBase (dsGPtr b) P.vCap)
    (hr12 : st.regs 12 = dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap)
    (hr13 : st.regs 13 = ws + 10 * eCap + 3)
    (hst : ∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st.mem a = mem₀ a)
    (hW : Phase4WSAt st.mem ws eCap { S with copyBuf := [] })
    (hS6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem₀)
    (hEmb : (embRep eCap).rep embH v y mem₀)
    (hOS : ∀ e < eCap, mem₀ (oldS + e) = if e ∈ OS then 1 else 0)
    (hm0 : mem₀ hOut = uhPtr) (hm3 : mem₀ (hOut + 3) = dPtr)
    (hm4 : mem₀ (hOut + 4) = dL.length) (hm5 : mem₀ (hOut + 5) = rPtr)
    (hm6 : mem₀ (hOut + 6) = rL.length)
    (hBat : BatchAt mem₀ uhPtr Hb UH uhWords) (hDL : ListAt mem₀ dPtr dL)
    (hRL : ListAt mem₀ rPtr rL)
    (hPl1 : hOut + 7 ≤ dPtr) (hPl2 : dPtr + dL.length = rPtr) (hPl3 : rPtr + rL.length = uhPtr)
    (hPl4 : uhPtr + uhWords < 2 ^ P.w)
    (hUHcap : ∀ u ∈ UH, UpdEdgeBelow eCap u) (hDcap : ∀ e ∈ dL, e < eCap)
    (hRcap : ∀ e ∈ rL, e < eCap) (heCap : eCap ≤ P.eCap)
    (hWalkCap : ∀ e ∈ (d.state P).G.E, ∀ q ∈ piTotal (d.state P) e, q.1 < eCap)
    (hOutWs : ws + p4WsSize eCap ≤ hOut) (hWsH : ws + p4WsSize eCap ≤ h)
    (hSpanF : ∀ a, bucketFoot spanTbl x6 a → a < h)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < h)
    (hSpanWs : ∀ a, bucketFoot spanTbl x6 a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hEmbWs : ∀ a, embFoot eCap embH y a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanTbl x6 a)
    (ho_disj : oldS + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ oldS) (ho_w : oldS + eCap < 2 ^ P.w)
    (hz : ZeroFrom mem₀ h)
    (hsp : h + slotListWalkWords P S6 s (p4TaskScan P d OS UH dL rL S).copyBuf < 2 ^ P.w)
    (hT : k + (340 * UH.length + 170 * dL.length + 135 * rL.length +
      ((p4TaskScan P d OS UH dL rL S).copyBuf.map (p4DleftEdgeCost P d)).sum +
      142 * slotListCopyWork P S6 s d (p4TaskScan P d OS UH dL rL S).copyBuf + 400) ≤ T) :
    ∃ o st' c, Runs P.w p ω (asmFirstP4AfterTail fScanUH fScanD fScanR fDleft fCopy) st o st' c ∧
      P4AfterPost P S6 x6 spanTbl s ws eCap embH h d OS UH dL rL S v y mem₀ o st' ∧
      k + c ≤ T := by
  classical
  have h0w : 0 < 2 ^ P.w := by omega
  have h1w : 1 < 2 ^ P.w := by omega
  have hsz : p4WsSize eCap = 11 * eCap + 4 := rfl
  -- The spanner of the slot and the places of its presence arrays.
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
  have hfixPos : 1 < dsFixedSize P.L P.vCap P.eCap := by
    have := hB.1; have h1 : dsTOff = 1 := rfl; omega
  have hgP : dgEPresBase (dsGPtr b) P.vCap = b + 10 + 7 * P.vCap := by
    simp only [dgEPresBase, dsGPtr, dsHdrSize]
  have hhP : dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap =
      dgEPresBase (dsGPtr b) P.vCap + (4 + 7 * P.vCap + 9 * P.eCap) := by
    simp only [dgEPresBase, dsHPtr, dsGPtr, dsHdrSize, dynGraphSize]; omega
  have hfixFoot : ∀ a, b ≤ a → a < b + dsFixedSize P.L P.vCap P.eCap → bucketFoot spanTbl x6 a :=
    fun a h1 h2 => Or.inr ⟨⟨s, hs⟩, b, m, hxm, Or.inl ⟨h1, by rw [hvc, hec]; exact h2⟩⟩
  have hfixWs : b + dsFixedSize P.L P.vCap P.eCap ≤ ws ∨ ws + p4WsSize eCap ≤ b :=
    block_avoid (by omega) (by omega)
      (fun i hi => hSpanWs _ (hfixFoot _ (by omega) (by omega)))
  have hg_disj : dgEPresBase (dsGPtr b) P.vCap + eCap ≤ ws ∨
      ws + p4WsSize eCap ≤ dgEPresBase (dsGPtr b) P.vCap := by
    rcases hfixWs with h' | h'
    · left; omega
    · right; omega
  have hh_disj : dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + eCap ≤ ws ∨
      ws + p4WsSize eCap ≤ dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap := by
    rcases hfixWs with h' | h'
    · left; omega
    · right; omega
  have hg_w : dgEPresBase (dsGPtr b) P.vCap + eCap < 2 ^ P.w := by omega
  have hh_w : dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + eCap < 2 ^ P.w := by omega
  have hws_w : ws + p4WsSize eCap < 2 ^ P.w := by omega
  have hGE₀ : ∀ e < eCap, mem₀ (dgEPresBase (dsGPtr b) P.vCap + e) =
      if e ∈ (d.state P).G.E then 1 else 0 :=
    fun e he => hDG.2.2.2.2.2.2.2.2.2.2.2.1 e (by omega)
  have hHE₀ : ∀ e < eCap, mem₀ (dgEPresBase (dsHPtr b P.vCap P.eCap) P.vCap + e) =
      if e ∈ (d.state P).H.E then 1 else 0 :=
    fun e he => hDH.2.2.2.2.2.2.2.2.2.2.2.1 e (by omega)
  -- The scan of `U_H`.
  have hBat₀ : BatchAt st.mem uhPtr Hb UH uhWords :=
    hBat.of_agree (fun i hi => hst _ (Or.inr (by omega)))
  have hm0' : st.mem hOut = uhPtr := (hst _ (Or.inr (by omega))).trans hm0
  obtain ⟨st₁, c₁, hr₁, hW₁, hfr₁, hc₁⟩ := asmFirstScanSlotUH_runs (isOld := 1) (oldS := oldS)
    (pos := st.pos) (ω := ω) (GE := (d.state P).G.E) (HE := (d.state P).H.E) (OS := OS)
    hfEdge hfPush hfMark hw16 hW
    (fun e he => (hst _ (out_of_block hg_disj e he)).trans (hGE₀ e he))
    (fun e he => (hst _ (out_of_block hh_disj e he)).trans (hHE₀ e he))
    (fun e he => (hst _ (out_of_block ho_disj e he)).trans (hOS e he))
    hBat₀ hUHcap hg_disj hh_disj ho_disj (Or.inr (by omega)) hg_w hh_w ho_w hPl4 hws_w
  rw [show decide ((1 : ℕ) ≠ 0) = true from rfl] at hW₁
  have hM₁ : ∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st₁.mem a = mem₀ a :=
    fun a ha => (hfr₁ a ha).trans (hst a ha)
  -- The scan of `D`.
  have hm3₁ : st₁.mem (hOut + 3) = dPtr := (hM₁ _ (Or.inr (by omega))).trans hm3
  have hm4₁ : st₁.mem (hOut + 4) = dL.length := (hM₁ _ (Or.inr (by omega))).trans hm4
  obtain ⟨st₂, c₂, hr₂, hW₂, hfr₂, hc₂⟩ := asmFirstScanSlotD_runs (pos := st₁.pos) (ω := ω)
    (GE := (d.state P).G.E) (HE := (d.state P).H.E) (dL := dL) hfPush hfMark hw16 hW₁
    (fun e he => (hM₁ _ (out_of_block hg_disj e he)).trans (hGE₀ e he))
    (fun e he => (hM₁ _ (out_of_block hh_disj e he)).trans (hHE₀ e he))
    (fun i hi => (hM₁ _ (Or.inr (by omega))).trans (hDL i hi)) hDcap hg_disj hh_disj
    (Or.inr (by omega)) hg_w hh_w (by omega) hws_w
  have hM₂ : ∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st₂.mem a = mem₀ a :=
    fun a ha => (hfr₂ a ha).trans (hM₁ a ha)
  -- The scan of `R`.
  have hm5₂ : st₂.mem (hOut + 5) = rPtr := (hM₂ _ (Or.inr (by omega))).trans hm5
  have hm6₂ : st₂.mem (hOut + 6) = rL.length := (hM₂ _ (Or.inr (by omega))).trans hm6
  obtain ⟨st₃, c₃, hr₃, hW₃, hfr₃, hc₃⟩ := asmFirstScanSlotR_runs (isOldN := 1) (pos := st₂.pos)
    (ω := ω) (GE := (d.state P).G.E) (HE := (d.state P).H.E) (rL := rL) hfPush hw16 hW₂
    (fun e he => (hM₂ _ (out_of_block hg_disj e he)).trans (hGE₀ e he))
    (fun e he => (hM₂ _ (out_of_block hh_disj e he)).trans (hHE₀ e he))
    (fun i hi => (hM₂ _ (Or.inr (by omega))).trans (hRL i hi)) hRcap hg_disj hh_disj
    (Or.inr (by omega)) hg_w hh_w (by omega) hws_w
  rw [show decide ((1 : ℕ) ≠ 0) = true from rfl] at hW₃
  have hW₃' : Phase4WSAt st₃.mem ws eCap (p4TaskScan P d OS UH dL rL S) := hW₃
  have hM₃ : ∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st₃.mem a = mem₀ a :=
    fun a ha => (hfr₃ a ha).trans (hM₂ a ha)
  -- The scan of the walks of `D_left`.
  have hFootWs : ∀ a, metaFoot b m.2 a → a < ws ∨ ws + p4WsSize eCap ≤ a :=
    fun a ha => hSpanWs a (Or.inr ⟨⟨s, hs⟩, b, m, hxm, ha⟩)
  have hRep₃ : DSRepAt P b d m.2 st₃.mem :=
    dsRepAt_of_agree hdsRep (fun a ha => hM₃ a (hFootWs a ha))
  obtain ⟨st₄, c₄, hr₄, hW₄, hfr₄, hc₄⟩ := asmFirstScanDleft_runs (pos := st₃.pos) (ω := ω)
    (GE := (d.state P).G.E) (HE := (d.state P).H.E) (OS := OS) (S := p4TaskScan P d OS UH dL rL S)
    hfEdge hfPush hfMark hread hw16 hW₃'
    (fun e he => (hM₃ _ (out_of_block hg_disj e he)).trans (hGE₀ e he))
    (fun e he => (hM₃ _ (out_of_block hh_disj e he)).trans (hHE₀ e he))
    (fun e he => (hM₃ _ (out_of_block ho_disj e he)).trans (hOS e he))
    hRep₃ (by omega)
    (fun a ha => lt_trans (hSpanF a (Or.inr ⟨⟨s, hs⟩, b, m, hxm, Or.inr ha⟩)) hhW) hFootWs
    (fun e he _ => mem_p4TaskScan_copyBuf he)
    (fun e he _ => hWalkCap e (mem_p4TaskScan_copyBuf he))
    hg_disj hh_disj ho_disj hg_w hh_w ho_w hws_w
  have hW₄' : Phase4WSAt st₄.mem ws eCap (p4TaskWS P d OS UH dL rL S) := hW₄
  have hM₄ : ∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st₄.mem a = mem₀ a :=
    fun a ha => (hfr₄ a ha).trans (hM₃ a ha)
  -- The copy of the walks.
  have hcb := p4TaskWS_copyBuf P d OS UH dL rL S
  have heL_len : (p4TaskScan P d OS UH dL rL S).copyBuf.length ≤ eCap := by
    rw [← hcb]; exact phase4WSAt_copyBuf_length_le hW₄'
  have hcl₄ : st₄.mem (ws + 10 * eCap + 3) = (p4TaskScan P d OS UH dL rL S).copyBuf.length := by
    rw [← hcb]; exact hW₄'.2.2.2.2.2.2.2.2.2.1
  have heL_at : ListAt st₄.mem (ws + 10 * eCap + 3 + 1) (p4TaskScan P d OS UH dL rL S).copyBuf := by
    intro i hi
    have h' := hW₄'.2.2.2.2.2.2.2.2.2.2 i (by rw [hcb]; exact hi)
    simp only [p4CopyBuf, hcb] at h'
    rw [show ws + 10 * eCap + 3 + 1 + i = ws + 10 * eCap + 4 + i by omega]
    exact h'
  have heL_sub : ∀ e ∈ (p4TaskScan P d OS UH dL rL S).copyBuf,
      e ∈ (d.state P).G.E ∧ e < eCap := fun e he =>
    ⟨mem_p4TaskScan_copyBuf he, (hW₃'.2.2.2.2.2.2.2.2.1 e he).1⟩
  have hS6₄ : (bucketSpannerRep P cap).rep spanTbl S6 x6 st₄.mem :=
    (bucketSpannerRep_local P cap spanTbl S6 x6 mem₀ st₄.mem
      (fun a ha => (hM₄ a (hSpanWs a ha)).symm)).1 hS6
  have hEmb₄ : (embRep eCap).rep embH v y st₄.mem :=
    (embRep_local eCap embH v y mem₀ st₄.mem (fun a ha => (hM₄ a (hEmbWs a ha)).symm)).1 hEmb
  have hz₄ : ZeroFrom st₄.mem h := fun a ha => (hM₄ a (Or.inr (by omega))).trans (hz a ha)
  obtain ⟨o₅, st₅, c₅, y', hr₅, hEmb₅, hov, hz₅, hfr₅, hfoot₅, hc₅⟩ :=
    asmFirstCopySlotList_runs (eListPtr := ws + 10 * eCap + 3 + 1) (pos := st₄.pos) (ω := ω)
      hcopy hread hs hSj hw16 hEmb₄ hS6₄ heL_at (by omega) heL_sub hEmbF hSpanF hDisj
      (fun a h1 h2 hf => by rcases hEmbWs a hf with h' | h' <;> omega) hz₄ hsp
  -- The runs of the calls.
  unfold asmFirstP4AfterTail
  refine runs_seq_callRuns_le (by eval_expr) hfUH hr₁ ?_
  refine runs_seq_callRuns_le (by eval_expr) hfD hr₂ ?_
  refine runs_seq_callRuns_le (by eval_expr) hfR hr₃ ?_
  refine runs_seq_callRuns_le (by eval_expr) hfDl hr₄ ?_
  refine runs_seq_callRuns_le (by eval_expr) hfC hr₅ ?_
  wram_step
  · have hin : ∀ a, ws ≤ a → a < ws + p4WsSize eCap → st₅.mem a = st₄.mem a := fun a h1 h2 =>
      hfr₅ a (by omega) (fun hf => by rcases hEmbWs a hf with h' | h' <;> omega)
    refine ⟨by rw [hov], phase4WSAt_of_agree hW₄' hin, ⟨y', hEmb₅, ?_⟩, ?_, ?_, ?_⟩
    · rw [← hov]; exact hfoot₅
    · exact (bucketSpannerRep_local P cap spanTbl S6 x6 st₄.mem st₅.mem
        (fun a ha => (hfr₅ a (hSpanF a ha) (fun hf => hDisj a hf ha)).symm)).1 hS6₄
    · rw [← hov]; exact hz₅
    · intro a ha hne hout
      exact (hfr₅ a ha hne).trans (hM₄ a hout)
  · wram_cost

public section

set_option maxHeartbeats 1600000 in
/-- **The work after the update of one slot.** The slot `s` of the spanners at `spanTbl` has the
new history `d`, and the header of the outputs `U_H`, `D`, `R` of its update lies at `hOut`, after
the workspace, with the lists placed as `DSUpdatePost` says. The spanners, the embedding at `embH`
and the presence array of the old output graph `OS` at `oldS` lie outside the workspace, and the
spanners and the embedding lie below the heap pointer `h`. Then `asmFirstP4AfterStmt` ends in
`P4AfterPost` and costs at most `340 |U_H| + 170 |D| + 135 |R|`, plus the cost of the walks of
`D_left` and of the copy of the walks of the copied edges, plus `500`. -/
theorem asmFirstP4After_runs {P : DSParams} {cap : ℕ}
    {fScanUH fScanD fScanR fDleft fCopy fEdge fPush fMark bRead bCopy : ℕ} {p : Program}
    (hfUH : p.procs[fScanUH]? = some (asmFirstScanSlotUHStmt fEdge))
    (hfD : p.procs[fScanD]? = some (asmFirstScanSlotDStmt fPush fMark))
    (hfR : p.procs[fScanR]? = some (asmFirstScanSlotRStmt fPush))
    (hfDl : p.procs[fDleft]? = some (asmFirstScanDleftStmt fEdge (bRead + spanReadIdxPiWalkPtr)))
    (hfC : p.procs[fCopy]? = some (asmFirstCopySlotListStmt bCopy (bRead + spanReadIdxPiWalkPtr)))
    (hfEdge : p.procs[fEdge]? = some (asmFirstP4EdgeStmt fPush fMark))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hfMark : p.procs[fMark]? = some asmFirstMarkSlotEdgeStmt)
    (hcopy : p.HasAt bCopy [copyWords]) (hread : p.HasAt bRead spanReadoutProcs)
    {spanTbl s hOut ws eCap oldS embH h pos : ℕ} {S6 : BucketSpannerState cap}
    {x6 : BucketSpannerMeta P.L cap} (hs : s < cap) {d : DSHist} (hSj : S6 ⟨s, hs⟩ = some d)
    {OS : Finset ℕ} {S : Phase4WS} {v : EmbView} {y : EmbConc}
    {uhPtr uhWords dPtr rPtr : ℕ} {UH : List Update} {Hb : MGraph} {dL rL : List ℕ}
    {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ P.w)
    (hW : Phase4WSAt mem₀ ws eCap S)
    (hS6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem₀)
    (hEmb : (embRep eCap).rep embH v y mem₀)
    (hOS : ∀ e < eCap, mem₀ (oldS + e) = if e ∈ OS then 1 else 0)
    (hm0 : mem₀ hOut = uhPtr) (hm3 : mem₀ (hOut + 3) = dPtr)
    (hm4 : mem₀ (hOut + 4) = dL.length) (hm5 : mem₀ (hOut + 5) = rPtr)
    (hm6 : mem₀ (hOut + 6) = rL.length)
    (hBat : BatchAt mem₀ uhPtr Hb UH uhWords) (hDL : ListAt mem₀ dPtr dL)
    (hRL : ListAt mem₀ rPtr rL)
    (hPl1 : hOut + 7 ≤ dPtr) (hPl2 : dPtr + dL.length = rPtr) (hPl3 : rPtr + rL.length = uhPtr)
    (hPl4 : uhPtr + uhWords < 2 ^ P.w)
    (hUHcap : ∀ u ∈ UH, UpdEdgeBelow eCap u) (hDcap : ∀ e ∈ dL, e < eCap)
    (hRcap : ∀ e ∈ rL, e < eCap) (heCap : eCap ≤ P.eCap)
    (hWalkCap : ∀ e ∈ (d.state P).G.E, ∀ q ∈ piTotal (d.state P) e, q.1 < eCap)
    (hOutWs : ws + p4WsSize eCap ≤ hOut) (hWsH : ws + p4WsSize eCap ≤ h)
    (hSpanF : ∀ a, bucketFoot spanTbl x6 a → a < h)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < h)
    (hSpanWs : ∀ a, bucketFoot spanTbl x6 a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hEmbWs : ∀ a, embFoot eCap embH y a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanTbl x6 a)
    (ho_disj : oldS + eCap ≤ ws ∨ ws + p4WsSize eCap ≤ oldS) (ho_w : oldS + eCap < 2 ^ P.w)
    (hz : ZeroFrom mem₀ h)
    (hsp : h + slotListWalkWords P S6 s (p4TaskScan P d OS UH dL rL S).copyBuf < 2 ^ P.w) :
    ∃ o st' c, Runs P.w p ω (asmFirstP4AfterStmt fScanUH fScanD fScanR fDleft fCopy)
        (startState [spanTbl, s, hOut, ws, eCap, oldS, embH, h] mem₀ pos) o st' c ∧
      P4AfterPost P S6 x6 spanTbl s ws eCap embH h d OS UH dL rL S v y mem₀ o st' ∧
      c ≤ 340 * UH.length + 170 * dL.length + 135 * rL.length +
        ((p4TaskScan P d OS UH dL rL S).copyBuf.map (p4DleftEdgeCost P d)).sum +
        142 * slotListCopyWork P S6 s d (p4TaskScan P d OS UH dL rL S).copyBuf + 500 := by
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
  set s0 := startState [spanTbl, s, hOut, ws, eCap, oldS, embH, h] mem₀ pos with hs0
  have hs0_0 : s0.regs 0 = spanTbl := by simp [s0, startState]
  have hs0_1 : s0.regs 1 = s := by simp [s0, startState]
  have hs0_3 : s0.regs 3 = ws := by simp [s0, startState]
  have hs0_4 : s0.regs 4 = eCap := by simp [s0, startState]
  have hm_b : s0.mem (spanTbl + s) = b := hmb
  have hm_v : s0.mem (b + 3) = P.vCap := hmV
  have hm_e : s0.mem (b + 4) = P.eCap := hmE
  have hm_v' : s0.mem (s0.mem (spanTbl + s) + 3) = P.vCap := by rw [hm_b]; exact hm_v
  have hm_e' : s0.mem (s0.mem (spanTbl + s) + 4) = P.eCap := by rw [hm_b]; exact hm_e
  have key : ∃ o st' c, Runs P.w p ω (asmFirstP4AfterStmt fScanUH fScanD fScanR fDleft fCopy)
      s0 o st' c ∧ P4AfterPost P S6 x6 spanTbl s ws eCap embH h d OS UH dL rL S v y mem₀ o st' ∧
      0 + c ≤ 340 * UH.length + 170 * dL.length + 135 * rL.length +
        ((p4TaskScan P d OS UH dL rL S).copyBuf.map (p4DleftEdgeCost P d)).sum +
        142 * slotListCopyWork P S6 s d (p4TaskScan P d OS UH dL rL S).copyBuf + 500 := by
    unfold asmFirstP4AfterStmt
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    wram_step
    refine p4AfterTail_runs hfUH hfD hfR hfDl hfC hfEdge hfPush hfMark hcopy hread hs hSj hxm hw16
      (by simp [hs0_0]) (by simp [s0, startState]) (by simp [s0, startState])
      (by simp [hs0_3]) (by simp [hs0_4]) (by simp [s0, startState]) (by simp [s0, startState])
      (by simp [s0, startState]) (by simp [hm_b])
      (by simp only [dgEPresBase, dsGPtr, dsHdrSize]; simp [hm_b, hm_v]; omega)
      (by simp [hhP, hm_b, hm_v, hm_e])
      (by simp [hs0_3, hs0_4])
      (fun a ha => by
        simp only [Function.update_apply]
        split_ifs with hc
        · simp only [p4WsSize] at ha; omega
        · rfl)
      (phase4WSAt_resetCopy hW) hS6 hEmb hOS hm0 hm3 hm4 hm5 hm6 hBat hDL hRL hPl1 hPl2 hPl3
      hPl4 hUHcap hDcap hRcap heCap hWalkCap hOutWs hWsH hSpanF hEmbF hSpanWs hEmbWs hDisj
      ho_disj ho_w hz hsp ?_
    wram_cost
  obtain ⟨o, st', c, hr, hq, hc⟩ := key
  exact ⟨o, st', c, hr, hq, by omega⟩

end

end MinCostFlow.SparseCore.Program
