module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepP4New

import WordRAM.Tactic

/-!
# The loop over the new slots of Phase 4 (`AssemblyFirstStepP4NewLoop`)

Phase 2 gives the new spanners the slots `lo, lo + 1, …, hi - 1`. The loop
`asmFirstP4NewLoopStmt fNew`, with arguments `[spanTbl, ws, eCap, embH, lo, hi, h]`, runs Phase 4
on each of these slots (`asmFirstP4NewStmt`, `AssemblyFirstStepP4New.lean`) with the current heap
pointer, and returns the last heap pointer.

`asmFirstP4NewLoop_runs` gives `P4NewLoopPost`: the workspace and the embedding table after the
slots (`p4NewStep`, with the edge list of the graph of each slot in a list `qs`), the spanners,
which are kept, the heap pointer, the frame, the footprint of the table, and the cost, at most
`p4NewPay` per slot.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read

/-! ## The procedure, the model and what the loop leaves -/

@[expose] public section

/-- **The loop over the new slots of Phase 4**, `[spanTbl, ws, eCap, embH, lo, hi, h]`. Register
`7` is the slot and register `6` the heap pointer. -/
def asmFirstP4NewLoopStmt (fNew : ℕ) : Stmt :=
  forRange 7 (.reg 4) (.reg 5) (.call 6 fNew [.reg 0, .reg 7, .reg 1, .reg 2, .reg 3, .reg 6]) ;;
  .ret (.reg 6)

/-- What Phase 4 on the new slot `q.1`, whose edge list is `q.2`, does to the workspace and to the
embedding table. -/
noncomputable def p4NewStep (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (A : Phase4WS × EmbView) (q : ℕ × List ℕ) : Phase4WS × EmbView :=
  if hs : q.1 < cap then
    match S6 ⟨q.1, hs⟩ with
    | some d =>
      (q.2.foldl (p4StepNew (d.state P).H.E) { A.1 with copyBuf := [] },
       A.2.apply (slotChange P S6 q.1
         (q.2.foldl (p4StepNew (d.state P).H.E) { A.1 with copyBuf := [] }).copyBuf))
    | none => A
  else A

/-- The cost bound of Phase 4 on the new slot `s`. -/
noncomputable def p4NewPay (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (s : ℕ) : ℕ :=
  if hs : s < cap then
    match S6 ⟨s, hs⟩ with
    | some d => p4NewWork P S6 s d
    | none => 0
  else 0

/-- The space of Phase 4 on the new slot `s`: the words of the walks of all edges of its graph. -/
noncomputable def p4NewSpace (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap) (s : ℕ) :
    ℕ :=
  if hs : s < cap then
    match S6 ⟨s, hs⟩ with
    | some d => (d.state P).G.E.sum (fun e => Read.walkWords (slotWalk P S6 s e))
    | none => 0
  else 0

/-- What the loop over the new slots `[lo, hi)` leaves, from the memory `mem₀`, the spanners `S6`
(meta `x6`), the workspace `S` and the embedding table `v` (concrete data `y`). There are edge
lists `qs` of the graphs of the slots, one entry per slot, and a concrete table `y'`, such that
the memory holds the workspace and the table after the slots (`p4NewStep`) and keeps the
spanners. The heap pointer grows by at most the space of the slots, the loop keeps the free cells
below `h₀` (`P4Free`), the footprint of the table grows only above `h₀`, and it stays apart from
the spanners. -/
def P4NewLoopPost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl ws eCap embH lo hi h₀ : ℕ) (S : Phase4WS)
    (v : EmbView) (y : EmbConc) (mem₀ : ℕ → ℕ) (o : Outcome) (st' : State) (c : ℕ) : Prop :=
  ∃ (qs : List (ℕ × List ℕ)) (y' : EmbConc),
    qs.map Prod.fst = List.range' lo (hi - lo) ∧
    (∀ q ∈ qs, ∀ (hs : q.1 < cap) (d : DSHist), S6 ⟨q.1, hs⟩ = some d →
      q.2.Nodup ∧ q.2.toFinset = (d.state P).G.E) ∧
    Phase4WSAt st'.mem ws eCap (qs.foldl (p4NewStep P S6) (S, v)).1 ∧
    (embRep eCap).rep embH (qs.foldl (p4NewStep P S6) (S, v)).2 y' st'.mem ∧
    (bucketSpannerRep P cap).rep spanTbl S6 x6 st'.mem ∧
    h₀ ≤ o.value ∧ o.value ≤ h₀ + rangeCost (p4NewSpace P S6) lo hi ∧
    ZeroFrom st'.mem o.value ∧
    (∀ a < h₀, P4Free spanTbl x6 eCap embH y ws a → st'.mem a = mem₀ a) ∧
    (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (h₀ ≤ a ∧ a < o.value)) ∧
    (∀ a, embFoot eCap embH y' a → ¬ bucketFoot spanTbl x6 a) ∧
    c ≤ rangeCost (fun s => p4NewPay P S6 s + 20) lo hi + 9 * (hi - lo) + 10

end

public section

theorem asmFirstP4NewLoopStmt_noRand (fNew : ℕ) : (asmFirstP4NewLoopStmt fNew).NoRand := by
  simp [asmFirstP4NewLoopStmt, forRange, forUp, Stmt.NoRand]

theorem p4NewStep_of (P : DSParams) {cap : ℕ} {S6 : BucketSpannerState cap} {s : ℕ}
    (hs : s < cap) {d : DSHist} (hd : S6 ⟨s, hs⟩ = some d) (A : Phase4WS × EmbView)
    (gL : List ℕ) :
    p4NewStep P S6 A (s, gL) =
      (gL.foldl (p4StepNew (d.state P).H.E) { A.1 with copyBuf := [] },
       A.2.apply (slotChange P S6 s
         (gL.foldl (p4StepNew (d.state P).H.E) { A.1 with copyBuf := [] }).copyBuf)) := by
  simp only [p4NewStep, hs, ↓reduceDIte, hd]

theorem p4NewPay_of (P : DSParams) {cap : ℕ} {S6 : BucketSpannerState cap} {s : ℕ}
    (hs : s < cap) {d : DSHist} (hd : S6 ⟨s, hs⟩ = some d) :
    p4NewPay P S6 s = p4NewWork P S6 s d := by
  simp only [p4NewPay, hs, ↓reduceDIte, hd]

theorem p4NewSpace_of (P : DSParams) {cap : ℕ} {S6 : BucketSpannerState cap} {s : ℕ}
    (hs : s < cap) {d : DSHist} (hd : S6 ⟨s, hs⟩ = some d) :
    p4NewSpace P S6 s = (d.state P).G.E.sum (fun e => Read.walkWords (slotWalk P S6 s e)) := by
  simp only [p4NewSpace, hs, ↓reduceDIte, hd]

/-- A sum over `[lo, i + 1)` is the sum over `[lo, i)` plus the last term. -/
theorem rangeCost_succ_right (f : ℕ → ℕ) {lo i : ℕ} (h : lo ≤ i) :
    rangeCost f lo (i + 1) = rangeCost f lo i + f i := by
  unfold rangeCost
  rw [show i + 1 - lo = (i - lo) + 1 by omega, List.range'_concat, List.map_append,
    List.sum_append, List.map_singleton, List.sum_singleton, show lo + 1 * (i - lo) = i by omega]

/-- A sum over `[lo, i)` is at most the sum over `[lo, hi)` when `i ≤ hi`. -/
theorem rangeCost_le_right (f : ℕ → ℕ) {lo i hi : ℕ} (h₁ : lo ≤ i) (h₂ : i ≤ hi) :
    rangeCost f lo i ≤ rangeCost f lo hi := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₂
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [← Nat.add_assoc, rangeCost_succ_right f (by omega)]
    exact le_trans (ih (by omega)) (Nat.le_add_right _ _)

end

/-! ## The invariant of the loop -/

/-- The invariant before slot `i`, on the registers `R` and the memory `mem`. -/
private def P4NewInvAt (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl ws eCap embH lo hi h₀ : ℕ) (S : Phase4WS)
    (v : EmbView) (y : EmbConc) (mem₀ : ℕ → ℕ) (i : ℕ) (R mem : ℕ → ℕ) : Prop :=
  R 0 = spanTbl ∧ R 1 = ws ∧ R 2 = eCap ∧ R 3 = embH ∧ R 4 = lo ∧ R 5 = hi ∧ R 7 = i ∧
  h₀ ≤ R 6 ∧ R 6 ≤ h₀ + rangeCost (p4NewSpace P S6) lo i ∧ ZeroFrom mem (R 6) ∧
  (∀ a < h₀, P4Free spanTbl x6 eCap embH y ws a → mem a = mem₀ a) ∧
  ∃ (qs : List (ℕ × List ℕ)) (y' : EmbConc),
    qs.map Prod.fst = List.range' lo (i - lo) ∧
    (∀ q ∈ qs, ∀ (hs : q.1 < cap) (d : DSHist), S6 ⟨q.1, hs⟩ = some d →
      q.2.Nodup ∧ q.2.toFinset = (d.state P).G.E) ∧
    Phase4WSAt mem ws eCap (qs.foldl (p4NewStep P S6) (S, v)).1 ∧
    (embRep eCap).rep embH (qs.foldl (p4NewStep P S6) (S, v)).2 y' mem ∧
    (bucketSpannerRep P cap).rep spanTbl S6 x6 mem ∧
    (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (h₀ ≤ a ∧ a < R 6)) ∧
    (∀ a, embFoot eCap embH y' a → ¬ bucketFoot spanTbl x6 a)

/-- The invariant before slot `i`, on the state `st`. -/
private def P4NewInv (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (x6 : BucketSpannerMeta P.L cap) (spanTbl ws eCap embH lo hi h₀ : ℕ) (S : Phase4WS)
    (v : EmbView) (y : EmbConc) (mem₀ : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  P4NewInvAt P S6 x6 spanTbl ws eCap embH lo hi h₀ S v y mem₀ i st.regs st.mem

/-! ## The run of the loop -/

public section

set_option maxHeartbeats 2400000 in
/-- **The run of the loop over the new slots of Phase 4.** Each slot of `[lo, hi)` holds a history
whose graph has its edges below `eCap`. The spanners and the embedding at `embH` lie below the
heap pointer `h₀` and outside the workspace at `ws`, which lies below `h₀`, and they are apart.
There is room for the walks of all edges of the graphs. Then `asmFirstP4NewLoopStmt` ends in
`P4NewLoopPost`. -/
theorem asmFirstP4NewLoop_runs {P : DSParams} {cap : ℕ} {fNew fScanNew fCopy fPush bRead bCopy : ℕ}
    {p : Program}
    (hfNew : p.procs[fNew]? = some (asmFirstP4NewStmt fScanNew fCopy))
    (hfN : p.procs[fScanNew]? = some (asmFirstScanNewSlotStmt fPush))
    (hfC : p.procs[fCopy]? = some (asmFirstCopySlotListStmt bCopy (bRead + spanReadIdxPiWalkPtr)))
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    (hcopy : p.HasAt bCopy [copyWords]) (hread : p.HasAt bRead spanReadoutProcs)
    {spanTbl ws eCap embH lo hi h₀ pos : ℕ} {S6 : BucketSpannerState cap}
    {x6 : BucketSpannerMeta P.L cap} {S : Phase4WS} {v : EmbView} {y : EmbConc}
    {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ P.w) (hlo : lo ≤ hi) (hhiW : hi < 2 ^ P.w)
    (hslots : ∀ s, lo ≤ s → s < hi → ∃ (hs : s < cap) (d : DSHist), S6 ⟨s, hs⟩ = some d ∧
      ∀ e ∈ (d.state P).G.E, e < eCap)
    (hW : Phase4WSAt mem₀ ws eCap S)
    (hS6 : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem₀)
    (hEmb : (embRep eCap).rep embH v y mem₀)
    (heCap : eCap ≤ P.eCap)
    (hWsH : ws + p4WsSize eCap ≤ h₀)
    (hSpanF : ∀ a, bucketFoot spanTbl x6 a → a < h₀)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < h₀)
    (hSpanWs : ∀ a, bucketFoot spanTbl x6 a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hEmbWs : ∀ a, embFoot eCap embH y a → a < ws ∨ ws + p4WsSize eCap ≤ a)
    (hDisj : ∀ a, embFoot eCap embH y a → ¬ bucketFoot spanTbl x6 a)
    (hz : ZeroFrom mem₀ h₀)
    (hspace : h₀ + rangeCost (p4NewSpace P S6) lo hi < 2 ^ P.w) :
    ∃ o st' c, Runs P.w p ω (asmFirstP4NewLoopStmt fNew)
        (startState [spanTbl, ws, eCap, embH, lo, hi, h₀] mem₀ pos) o st' c ∧
      P4NewLoopPost P S6 x6 spanTbl ws eCap embH lo hi h₀ S v y mem₀ o st' c := by
  classical
  have hw1 : 1 < 2 ^ P.w := by omega
  -- One round of the loop.
  have hbody : ∀ i, lo ≤ i → i < hi →
      Triple P.w p (P4NewInv P S6 x6 spanTbl ws eCap embH lo hi h₀ S v y mem₀ i)
        (.call 6 fNew [.reg 0, .reg 7, .reg 1, .reg 2, .reg 3, .reg 6])
        (normalPost fun st₁ =>
          P4NewInv P S6 x6 spanTbl ws eCap embH lo hi h₀ S v y mem₀ (i + 1)
              { st₁ with regs := Function.update st₁.regs 7 (i + 1) } ∧
            st₁.regs 7 = i)
        (fun _ => p4NewPay P S6 i + 20) := by
    intro i hloi hih st ω' hInv
    obtain ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr7, hhp_lo, hhp_hi, hzhp, hfr, qs, yi, hqs, hqsOK,
      hWi, hEmbi, hrepi, hembfi, hdisji⟩ := hInv
    obtain ⟨hs, d, hd, hGcap⟩ := hslots i hloi hih
    have hsp_i := p4NewSpace_of P hs hd
    have hsum := rangeCost_succ_right (p4NewSpace P S6) hloi
    have hsle := rangeCost_le_right (p4NewSpace P S6) (i := i + 1) (Nat.le_succ_of_le hloi) hih
    have hembfi' : ∀ a, embFoot eCap embH yi a → a < st.regs 6 := fun a ha => by
      rcases hembfi a ha with h | ⟨-, h⟩
      · have := hEmbF a h; omega
      · exact h
    have hEmbWsi : ∀ a, embFoot eCap embH yi a → a < ws ∨ ws + p4WsSize eCap ≤ a :=
      fun a ha => by
        rcases hembfi a ha with h | ⟨h, -⟩
        · exact hEmbWs a h
        · right; omega
    obtain ⟨o₁, st₁, c₁, hrun₁, hpost₁, hc₁⟩ := asmFirstP4New_runs (spanTbl := spanTbl)
      (ws := ws) (eCap := eCap) (embH := embH) (h := st.regs 6) (pos := st.pos) (ω := ω')
      (S := (qs.foldl (p4NewStep P S6) (S, v)).1) (v := (qs.foldl (p4NewStep P S6) (S, v)).2)
      (y := yi) hfN hfC hfPush hcopy hread hs hd hw16 hWi hrepi hEmbi hGcap heCap (by omega)
      (fun a ha => by have := hSpanF a ha; omega) hembfi' hSpanWs hEmbWsi hdisji hzhp
      (by omega)
    obtain ⟨gL, hgLnd, hgLE, ho₁, hW₁, ⟨y₁, hEmb₁, hEmbFt₁⟩, hrep₁, hz₁, hfr₁⟩ := hpost₁
    have hcb := p4StepNew_copyBuf (d.state P).H.E gL (qs.foldl (p4NewStep P S6) (S, v)).1
    have hwords := slotListWalkWords_le_sum P S6 i hcb.1 (E := (d.state P).G.E)
      (fun e he => by rw [← hgLE]; exact List.mem_toFinset.mpr (hcb.2 e he).1)
    have hval : o₁.value = st.regs 6 + slotListWalkWords P S6 i
        (gL.foldl (p4StepNew (d.state P).H.E)
          { (qs.foldl (p4NewStep P S6) (S, v)).1 with copyBuf := [] }).copyBuf := by
      rw [ho₁]; rfl
    have hval_le : o₁.value ≤ st.regs 6 +
        (d.state P).G.E.sum (fun e => Read.walkWords (slotWalk P S6 i e)) := by
      rw [hval]; exact Nat.add_le_add_left hwords _
    rw [← hval] at hz₁ hEmbFt₁
    have heArgs : evalArgs P.w st [.reg 0, .reg 7, .reg 1, .reg 2, .reg 3, .reg 6] =
        some [spanTbl, i, ws, eCap, embH, st.regs 6] :=
      evalArgs_cons (Expr.eval_reg_of_eq hr0) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr7) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr1) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr2) <|
      evalArgs_cons (Expr.eval_reg_of_eq hr3) <|
      evalArgs_cons (Expr.eval_reg_of_eq rfl) <| evalArgs_nil _ _
    have hr_call : Runs P.w p ω' (.call 6 fNew [.reg 0, .reg 7, .reg 1, .reg 2, .reg 3, .reg 6])
        st .normal ⟨st₁.mem, Function.update st.regs 6 o₁.value, st₁.pos⟩
        (argsSize [.reg 0, .reg 7, .reg 1, .reg 2, .reg 3, .reg 6] + c₁ + 1) :=
      runs_call_iff.mpr ⟨_, _, o₁, st₁, c₁, heArgs, hfNew, hrun₁, rfl, rfl, rfl⟩
    have hcall_cost : argsSize [.reg 0, .reg 7, .reg 1, .reg 2, .reg 3, .reg 6] = 6 := by
      simp [argsSize, Expr.size]
    have hpay := p4NewPay_of P hs hd
    have hfold : (qs ++ [(i, gL)]).foldl (p4NewStep P S6) (S, v) =
        p4NewStep P S6 (qs.foldl (p4NewStep P S6) (S, v)) (i, gL) := by
      rw [List.foldl_append]; rfl
    have hstep := p4NewStep_of P hs hd (qs.foldl (p4NewStep P S6) (S, v)) gL
    refine ⟨.normal, _, _, hr_call, ⟨?_, by simp [hr7]⟩, ?_⟩
    · show P4NewInvAt P S6 x6 spanTbl ws eCap embH lo hi h₀ S v y mem₀ (i + 1)
        (Function.update (Function.update st.regs 6 o₁.value) 7 (i + 1)) st₁.mem
      have hR6 : Function.update (Function.update st.regs 6 o₁.value) 7 (i + 1) 6 = o₁.value := by
        simp
      rw [P4NewInvAt, hR6]
      refine ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
        by simp [hr5], by simp, by omega, by omega, hz₁, fun a ha hfa => ?_,
        qs ++ [(i, gL)], y₁, ?_, fun q hq => ?_, ?_, ?_, hrep₁, fun a ha => ?_,
        fun a ha hb => ?_⟩
      · have hne : ¬ embFoot eCap embH yi a := fun he => by
          rcases hembfi a he with h | ⟨h, -⟩
          · exact hfa.2.1 h
          · omega
        rw [hfr₁ a (by omega) hne hfa.2.2, hfr a ha hfa]
      · rw [List.map_append, hqs, show i + 1 - lo = (i - lo) + 1 by omega, List.range'_concat,
          show lo + 1 * (i - lo) = i by omega]
        rfl
      · rcases List.mem_append.mp hq with hq | hq
        · exact hqsOK q hq
        · simp only [List.mem_singleton] at hq
          subst hq
          intro hs' d₂ hd₂
          have hdd : d₂ = d := Option.some.inj (hd₂.symm.trans hd)
          subst hdd
          exact ⟨hgLnd, hgLE⟩
      · rw [hfold, hstep]; exact hW₁
      · rw [hfold, hstep]; exact hEmb₁
      · rcases hEmbFt₁ a ha with h | ⟨h, h'⟩
        · rcases hembfi a h with h | ⟨h, h'⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, by omega⟩
        · exact Or.inr ⟨by omega, h'⟩
      · rcases hEmbFt₁ a ha with he | ⟨he, -⟩
        · exact hdisji a he hb
        · have := hSpanF a hb; omega
    · simp only [hcall_cost, hpay]; omega
  -- The whole procedure: the loop, then `ret (reg 6)`.
  have hloop := Triple.forRange_le
    (P := fun st : State => st.mem = mem₀ ∧ st.regs 0 = spanTbl ∧ st.regs 1 = ws ∧
      st.regs 2 = eCap ∧ st.regs 3 = embH ∧ st.regs 4 = lo ∧ st.regs 5 = hi ∧ st.regs 6 = h₀)
    (Inv := P4NewInv P S6 x6 spanTbl ws eCap embH lo hi h₀ S v y mem₀)
    (fun i => p4NewPay P S6 i + 20) lo hi hlo hw1 (fun _ => hhiW)
    (fun st hst => by
      obtain ⟨hmem, hr0, hr1, hr2, hr3, hr4, hr5, hr6⟩ := hst
      refine ⟨Expr.eval_reg_of_eq hr4, ?_⟩
      show P4NewInvAt P S6 x6 spanTbl ws eCap embH lo hi h₀ S v y mem₀ lo
        (Function.update st.regs 7 lo) st.mem
      have hR6 : Function.update st.regs 7 lo 6 = h₀ := by simp [hr6]
      rw [hmem, P4NewInvAt, hR6]
      refine ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
        by simp [hr5], by simp, le_rfl, by simp, hz, fun a _ _ => rfl, [], y, by simp,
        fun q hq => absurd hq List.not_mem_nil, hW, hEmb, hS6, fun a ha => Or.inl ha, hDisj⟩)
    (fun i st _ _ hInv => hInv.2.2.2.2.2.2.1)
    (fun i st _ _ hInv => Expr.eval_reg_of_eq hInv.2.2.2.2.2.1)
    hbody
  obtain ⟨oL, stL, cL, hrunL, hpostL, hcL⟩ := hloop
    (startState [spanTbl, ws, eCap, embH, lo, hi, h₀] mem₀ pos) ω
    ⟨rfl, by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp [startState], by simp [startState]⟩
  cases oL with
  | returned _ => cases hpostL
  | normal =>
  obtain ⟨-, -, -, -, -, -, -, hloE, hhiE, hzE, hfrE, qs, y', hqs, hqsOK, hWE, hEmbE, hrepE,
    hembfE, hdisjE⟩ := hpostL
  have hr_ret : Runs P.w p ω (.ret (.reg 6)) stL (.returned (stL.regs 6)) stL
      ((Expr.reg 6).size + 1) :=
    runs_ret_iff.mpr ⟨stL.regs 6, Expr.eval_reg_of_eq rfl, rfl, rfl, rfl⟩
  have hr_full : Runs P.w p ω (asmFirstP4NewLoopStmt fNew)
      (startState [spanTbl, ws, eCap, embH, lo, hi, h₀] mem₀ pos)
      (.returned (stL.regs 6)) stL (cL + ((Expr.reg 6).size + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨stL, _, _, hrunL, hr_ret, rfl⟩)
  refine ⟨.returned (stL.regs 6), stL, _, hr_full, qs, y', hqs, hqsOK, hWE, hEmbE, hrepE,
    hloE, hhiE, hzE, hfrE, hembfE, hdisjE, ?_⟩
  simp only [Expr.size] at hcL ⊢
  omega

end

end MinCostFlow.SparseCore.Program
