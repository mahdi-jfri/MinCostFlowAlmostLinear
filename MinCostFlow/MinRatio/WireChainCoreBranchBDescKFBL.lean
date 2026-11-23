module

public import MinCostFlow.MinRatio.WireChainCoreSelOutSlotKFBL
public import MinCostFlow.MinRatio.WireCoreReadKFBL
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
import WordRAM.Tactic

/-!
# Op `2` and the descriptor copy in a Branch B level step (`WireChainCoreBranchBDescKFBL`)

At a level that `Update` does not rebuild, the select part reads the stretch tables of the new
forest of the active branch. Op `2` (the LSF readout) gives a 2-word descriptor of the two tables
at `mem (cur + 3)` and their width at `mem (cur + 4)`, where `cur` is the heap pointer of the call.
The descriptor words may lie in the footprint of the core, while the select part needs a
descriptor off the footprint. So right after op `2` the core copies the two base words to
`cur + 5` and `cur + 6`, just above the 5 words that op `2` may use. A base above `cur` becomes `0`
(`guardWord`); this can happen only when the edge set is empty, since every row ends at or below
`cur`.

This file gives that part, `wireBranchBReadDescStmt`, and its run lemma
`wireBranchBReadDescStmt_runs`. It uses `ordCoreReadLSFKFBLRows_runs`, which is
`ordCoreReadLSFKFBL_runs` (`WireCoreReadKFBL.lean`) together with the place of every row word:
in the new footprint or in the op-`2` output `[cur, ret)` (`SparseCoreReadoutFootAt.op2_runs`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- `SelOutTableAt` holds for a smaller footprint-or-region condition: a larger footprint and a
larger region. -/
theorem selOutTableAt_mono {w lo hi lo' hi' a Lw : ℕ} {F F' : ℕ → Prop} {mem : ℕ → ℕ}
    {E : Finset ℕ} (h : SelOutTableAt w F lo hi mem a Lw E) (hF : ∀ x, F x → F' x)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : SelOutTableAt w F' lo' hi' mem a Lw E :=
  ⟨h.1, fun e he => ⟨(h.2 e he).1.trans hhi, fun t ht => by
    rcases (h.2 e he).2 t ht with h1 | ⟨h1, h2⟩
    · exact Or.inl (hF _ h1)
    · exact Or.inr ⟨hlo.trans h1, h2.trans_le hhi⟩⟩⟩

section Execution

variable {w L depth k M N vCap eCap capExp : ℕ} {fmt : Num.Format w}
  {tool : SparseCoreRestartTool} {initialGraph : MGraph} {P : SparseCoreOrdParams}
  {allocation : ℕ → List ℕ → ℕ} {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ}

/-- `ordCoreReadLSFKFBL_runs` with the place of the rows of the two stretch tables: each row word
lies in the new footprint or in the op-`2` output `[heap, ret)`. -/
theorem ordCoreReadLSFKFBLRows_runs {branch handle graph heap : ℕ}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {st : State} {ω : ℕ → Bool}
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R p op)
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle)
    (hg : st.regs 6 = graph) (hp : st.regs 4 = heap)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hG : DynGraphAt st.mem graph vCap eCap a.G)
    (hgEnd : graph + dynGraphSize vCap eCap ≤ heap)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 5 < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (ordCoreReadLSFStmt (op 2)) st .normal out cost ∧ out.regs 5 = ret ∧
      R.rep handle a y out.mem ∧
      out.mem (heap + 4) ≤
        L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
      (∃ vc ec, LSFAt out.mem heap vc ec fmt.limbBits (out.mem (heap + 4)) fmt.precision a.G.E
        (tool.lsfs a.st branch)) ∧
      out.mem (heap + 3) + 2 ≤ heap ∧
      (∀ e ∈ a.G.E,
        out.mem (out.mem (heap + 3)) + e * out.mem (heap + 4) + out.mem (heap + 4) ≤ heap ∧
        ∀ t < out.mem (heap + 4),
          R.foot handle y (out.mem (out.mem (heap + 3)) + e * out.mem (heap + 4) + t) ∨
          (heap ≤ out.mem (out.mem (heap + 3)) + e * out.mem (heap + 4) + t ∧
            out.mem (out.mem (heap + 3)) + e * out.mem (heap + 4) + t < ret)) ∧
      (∀ e ∈ a.G.E,
        out.mem (out.mem (heap + 3) + 1) + e * out.mem (heap + 4) + out.mem (heap + 4) ≤ heap ∧
        ∀ t < out.mem (heap + 4),
          R.foot handle y (out.mem (out.mem (heap + 3) + 1) + e * out.mem (heap + 4) + t) ∨
          (heap ≤ out.mem (out.mem (heap + 3) + 1) + e * out.mem (heap + 4) + t ∧
            out.mem (out.mem (heap + 3) + 1) + e * out.mem (heap + 4) + t < ret)) ∧
      R.Respects (R.foot handle x) heap 5 st.mem ret handle y out.mem ∧
      cost + R.phi handle y out.mem ≤ P.readout + 5 + R.phi handle x st.mem ∧
      (∀ r ≠ 5, out.regs r = st.regs r) := by
  have hwords : ∀ v ∈ [handle, branch, graph, heap], v < 2 ^ w := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  obtain ⟨body, hbody, o, after, c, y, hrun, hrep', hpost, hrespect, hcost⟩ :=
    hFootAt.op2_runs handle a x [handle, branch, graph, heap] st.mem st.pos ω hwords rfl hrep
      ⟨hIn, handle, branch, graph, heap, rfl, hj, hG, hgEnd⟩ hfoot hz hroom
  obtain ⟨vc, ec, hLw, hlsf, -, -, hst, hnum, hden, _⟩ := hpost
  simp only [heapArg, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.getLastD_cons, List.getLastD_nil]
    at hLw hlsf hst hnum hden
  let out := { after with regs := Function.update st.regs 5 o.value }
  have hargs : evalArgs w st [.reg 3, .reg 2, .reg 6, .reg 4] =
      some [handle, branch, graph, heap] := by
    simp [evalArgs, Expr.eval, hh, hb, hg, hp]
  have hcall : Runs w p ω (ordCoreReadLSFStmt (op 2)) st .normal out (4 + c + 1) :=
    runs_call_iff.mpr ⟨_, body, o, after, c, hargs, hbody, hrun, rfl, rfl, rfl⟩
  refine ⟨out, o.value, 4 + c + 1, y, hcall, by simp [out], hrep', hLw, ⟨vc, ec, hlsf⟩, hst,
    hnum, hden, hrespect, ?_,
    fun r hr => Function.update_of_ne hr _ _⟩
  change c + R.phi handle y after.mem ≤ P.readout + R.phi handle x st.mem at hcost
  change _ + R.phi handle y after.mem ≤ _
  omega

/-- Op `2` at the heap pointer `cur = reg 4`, then the guarded copy of its two descriptor words to
`cur + 5` and `cur + 6`. Afterwards `reg 30` holds `cur`, `reg 31` the new descriptor `cur + 5`,
`reg 32` the width of the tables, and `reg 4` the next free word `cur + 7`. -/
@[expose] def wireBranchBReadDescStmt (readLSF : ℕ) : Stmt :=
  ordCoreReadLSFStmt readLSF ;;
  .assign 30 (.reg 4) ;;
  .assign 18 (.load (.bin .add (.reg 30) (.const 3))) ;;
  .assign 32 (.load (.bin .add (.reg 30) (.const 4))) ;;
  .assign 31 (.bin .add (.reg 30) (.const 5)) ;;
  .assign 4 (.bin .add (.reg 30) (.const 7)) ;;
  wireStretchDescCopyStmt 19 18 31 30

theorem wireBranchBReadDescStmt_noRand (readLSF : ℕ) :
    (wireBranchBReadDescStmt readLSF).NoRand := by
  simp [wireBranchBReadDescStmt, ordCoreReadLSFStmt, wireStretchDescCopyStmt,
    wireGuardCopyWordStmt, Stmt.NoRand]

set_option maxHeartbeats 800000 in
/-- One run of `wireBranchBReadDescStmt` under `SparseCoreReadoutFootAt`. The new descriptor at
`cur + 5` gives the stretch values of the active branch, and the rows of its two tables lie in the
new footprint or in the op-`2` output `[cur, ret)`, with `ret ≤ cur + 5`. Below `cur`, only the
footprint of the core may change. -/
theorem wireBranchBReadDescStmt_runs {branch handle graph cur : ℕ}
    {a : SparseCoreOrdAbs tool} {x : R.τ} {st : State} {ω : ℕ → Bool}
    (hLocal : R.Local)
    (hFootAt : SparseCoreReadoutFootAt fmt L depth tool initialGraph k M N vCap eCap capExp P
      allocation R p op)
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle)
    (hg : st.regs 6 = graph) (hp : st.regs 4 = cur)
    (hj : branch < k) (hw : k < 2 ^ w) (hhw : handle < 2 ^ w)
    (hG : DynGraphAt st.mem graph vCap eCap a.G)
    (hgEnd : graph + dynGraphSize vCap eCap ≤ cur)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < cur) (hz : ZeroFrom st.mem cur)
    (hroom : cur + 7 < 2 ^ w) :
    ∃ (out : State) (ret cost : ℕ) (y : R.τ),
      Runs w p ω (wireBranchBReadDescStmt (op 2)) st .normal out cost ∧
      cur ≤ ret ∧ ret ≤ cur + 5 ∧
      out.regs 4 = cur + 7 ∧ out.regs 30 = cur ∧ out.regs 31 = cur + 5 ∧
      out.regs 32 = out.mem (cur + 4) ∧
      (∀ r, r ≠ 4 → r ≠ 5 → r ≠ 18 → r ≠ 19 → r ≠ 30 → r ≠ 31 → r ≠ 32 →
        out.regs r = st.regs r) ∧
      R.rep handle a y out.mem ∧
      (∀ addr, R.foot handle y addr → R.foot handle x addr ∨ (cur ≤ addr ∧ addr < ret)) ∧
      ZeroFrom out.mem (cur + 7) ∧
      (∀ addr < cur, ¬ R.foot handle x addr → out.mem addr = st.mem addr) ∧
      out.mem (cur + 4) ≤
        L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
      StretchValuesAt out.mem (cur + 5) fmt.limbBits (out.mem (cur + 4)) fmt.precision a.G.E
        (tool.lsfs a.st branch).wstr ∧
      SelOutTableAt w (R.foot handle y) cur ret out.mem (cur + 5) (out.mem (cur + 4)) a.G.E ∧
      SelOutTableAt w (R.foot handle y) cur ret out.mem (cur + 5 + 1) (out.mem (cur + 4)) a.G.E ∧
      (∀ e ∈ a.G.E, out.mem (cur + 5) + e * out.mem (cur + 4) + out.mem (cur + 4) ≤ cur ∧
        out.mem (cur + 5 + 1) + e * out.mem (cur + 4) + out.mem (cur + 4) ≤ cur) ∧
      cost + R.phi handle y out.mem ≤ P.readout + 70 + R.phi handle x st.mem := by
  obtain ⟨s1, ret, c1, y, r1, hs1_5, hrep1, hLw1, ⟨vc, ec, hlsf1⟩, hst1, hnum1, hden1, hResp1,
      hc1, hregs1⟩ :=
    ordCoreReadLSFKFBLRows_runs hFootAt hb hh hg hp hj hw hhw hG hgEnd hrep hIn hfoot hz
      (by omega)
  obtain ⟨D, hD⟩ : ∃ v, s1.mem (cur + 3) = v := ⟨_, rfl⟩
  obtain ⟨Lw, hLwD⟩ : ∃ v, s1.mem (cur + 4) = v := ⟨_, rfl⟩
  rw [hD] at hst1
  rw [hD, hLwD] at hnum1 hden1
  rw [hLwD] at hLw1
  have hSV1 := hlsf1.2.2.2
  rw [hD, hLwD] at hSV1
  have hret1 : cur ≤ ret := hResp1.1
  have hret2 : ret ≤ cur + 5 := hResp1.2.1
  have h14 : s1.regs 4 = cur := (hregs1 4 (by decide)).trans hp
  -- the final memory
  let Mf : ℕ → ℕ := Function.update (Function.update s1.mem (cur + 5) (guardWord cur (s1.mem D)))
    (cur + 5 + 1) (guardWord cur (s1.mem (D + 1)))
  have hMf (a : ℕ) (h5 : a ≠ cur + 5) (h6 : a ≠ cur + 5 + 1) : Mf a = s1.mem a := by
    simp only [Mf, Function.update_of_ne h6, Function.update_of_ne h5]
  have hMf5 : Mf (cur + 5) = guardWord cur (s1.mem D) := by
    simp only [Mf, Function.update_of_ne (show cur + 5 ≠ cur + 5 + 1 by omega),
      Function.update_self]
  have hMf6 : Mf (cur + 5 + 1) = guardWord cur (s1.mem (D + 1)) := by
    simp only [Mf, Function.update_self]
  have hMf4 : Mf (cur + 4) = Lw := (hMf _ (by omega) (by omega)).trans hLwD
  have hNe0 : a.G.E.Nonempty → Mf (cur + 5) = s1.mem D := fun ⟨e, he⟩ => by
    rw [hMf5, guardWord_of_le]; have := (hnum1 e he).1; omega
  have hNe1 : a.G.E.Nonempty → Mf (cur + 5 + 1) = s1.mem (D + 1) := fun ⟨e, he⟩ => by
    rw [hMf6, guardWord_of_le]; have := (hden1 e he).1; omega
  have hFootY (addr : ℕ) (hf : R.foot handle y addr) : addr < cur + 5 := by
    rcases hResp1.2.2.2.2 addr hf with h0 | ⟨_, h2⟩
    · have := hfoot addr h0; omega
    · omega
  have hLoc := hLocal handle a y s1.mem Mf (fun addr hf => by
    have := hFootY addr hf; exact (hMf addr (by omega) (by omega)).symm)
  suffices hrun : ∃ o st' cost, Runs w p ω (wireBranchBReadDescStmt (op 2)) st o st' cost ∧
      (o = .normal ∧ st'.mem = Mf ∧ st'.regs 4 = cur + 7 ∧ st'.regs 30 = cur ∧
        st'.regs 31 = cur + 5 ∧ st'.regs 32 = Lw ∧
        (∀ r, r ≠ 4 → r ≠ 5 → r ≠ 18 → r ≠ 19 → r ≠ 30 → r ≠ 31 → r ≠ 32 →
          st'.regs r = st.regs r)) ∧
      0 + cost ≤ c1 + 60 by
    obtain ⟨o, ⟨mem', regs', pos'⟩, cost, hr, ⟨rfl, hmem, h4, h30, h31, h32, hkeep⟩, hcost⟩ :=
      hrun
    dsimp only at hmem h4 h30 h31 h32 hkeep
    subst hmem
    refine ⟨⟨Mf, regs', pos'⟩, ret, cost, y, hr, hret1, hret2, h4, h30, h31,
      by dsimp only; rw [hMf4]; exact h32,
      hkeep, hLoc.1 hrep1, hResp1.2.2.2.2,
      fun z hz => by
        show Mf z = 0
        rw [hMf z (by omega) (by omega)]; exact hResp1.2.2.1 z (by omega),
      fun z hz hnf => by
        show Mf z = st.mem z
        rw [hMf z (by omega) (by omega)]; exact hResp1.2.2.2.1 z hz hnf,
      by dsimp only; rw [hMf4]; exact hLw1, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only
    · rw [hMf4]
      exact stretchValuesAt_of_moved hSV1 (fun hE => ⟨hNe0 hE, hNe1 hE⟩)
        (fun e he t ht => hMf _ (by have := (hnum1 e he).1; omega)
          (by have := (hnum1 e he).1; omega))
        (fun e he t ht => hMf _ (by have := (hden1 e he).1; omega)
          (by have := (hden1 e he).1; omega))
    · rw [hMf4]
      refine ⟨by rw [hMf5]; have := guardWord_le cur (s1.mem D); omega, fun e he => ?_⟩
      rw [hNe0 ⟨e, he⟩]
      exact ⟨by have := (hnum1 e he).1; omega, (hnum1 e he).2⟩
    · rw [hMf4]
      refine ⟨by rw [hMf6]; have := guardWord_le cur (s1.mem (D + 1)); omega, fun e he => ?_⟩
      rw [hNe1 ⟨e, he⟩]
      exact ⟨by have := (hden1 e he).1; omega, (hden1 e he).2⟩
    · intro e he
      rw [hMf4, hNe0 ⟨e, he⟩, hNe1 ⟨e, he⟩]
      exact ⟨(hnum1 e he).1, (hden1 e he).1⟩
    · rw [← hLoc.2]; omega
  unfold wireBranchBReadDescStmt
  refine runs_seq_runs_le r1 ?_
  refine runs_seq_assign_le (v := cur) (by eval_expr) ?_
  refine runs_seq_assign_le (v := D) (by eval_expr) ?_
  refine runs_seq_assign_le (v := Lw) (by eval_expr) ?_
  refine runs_seq_assign_le (v := cur + 5) (by eval_expr) ?_
  refine runs_seq_assign_le (v := cur + 7) (by eval_expr) ?_
  refine ⟨.normal, _, 31, wireStretchDescCopyStmt_runs (a := D) (b := cur + 5) (cur := cur)
    (by omega) (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by omega)
    (by omega) (Or.inr (by omega)), ⟨rfl, rfl, by simp, by simp, by simp, by simp, ?_⟩, ?_⟩
  · intro r h4 h5 h18 h19 h30 h31 h32
    simp only [Function.update_apply, h4, h18, h19, h30, h31, h32, ↓reduceIte]
    exact (hregs1 r h5)
  · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega

end Execution

end MinCostFlow.MinRatio
