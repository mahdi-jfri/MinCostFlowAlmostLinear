module

public import MinCostFlow.SparseCore.Program.ReadRestart
public import MinCostFlow.DynSpanner.Program.DynGraphInit

import MinCostFlow.SparseCore.Program.SpanBucketInit

/-!
# The output graph `S₀` at the init of a branch (`AssemblyFirstInitS0`)

At the init, `S₀` has the roots of the forest as its vertices, and the edges of the spanner graphs
`H` of the active pairs, each at the roots of its ends. The restart of a branch rebuilds `S_cur`
in the same way: P10's restart (`readRestartStmt`) removes the edges of the listed spanners from
`S` and adds the edges of their `H` at their core ends, which it finds with P4's root query. So
the init uses that procedure on a graph with the roots and no edge:
1. it makes the graph with the roots and no edge (`dgInitFromLists`);
2. it writes a small record for P10's restart: at `h + 5` the address of the graph, at `h + 6`
   the address of `G`;
3. it calls P10's restart on all listed slots (`readRestart_core_runs`).
The word `h + 5` then holds the address of the output graph, so it can serve as the handle of the
output graph. `asmFirstInitS0_runs` proves the run. The link to `tr₀.S_cur` is in
`AssemblyFirstInitS0Model.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

@[expose] public section

/-- **`S₀` at the init**, `[b4, j, graph, spanTbl, n, slotsPtr, rootsPtr, nR, vCap, eCap, h]`:
1. store at `h + 5` the address `h + 7` of the output graph, and at `h + 6` the address `graph`;
2. make the output graph at `h + 7` with the `nR` roots listed at `rootsPtr` and no edge
   (`fLists`);
3. call P10's restart (`fRebuild`) on the record at `h`, the spanners at `spanTbl`, the `n` slots
   listed at `slotsPtr`, and P4's handle `b4` and branch `j`, with the heap after the graph;
4. return the heap pointer of the restart. -/
def asmFirstInitS0Body (fLists fRebuild : ℕ) : Stmt :=
  .store (.bin .add (.reg 10) (.const 5)) (.bin .add (.reg 10) (.const 7)) ;;
  .store (.bin .add (.reg 10) (.const 6)) (.reg 2) ;;
  .call 11 fLists
    [.bin .add (.reg 10) (.const 7), .reg 8, .reg 9, .reg 7, .reg 6, .const 0, .const 0] ;;
  .call 11 fRebuild [.reg 10, .reg 3, .reg 4, .reg 5, .reg 0, .reg 1,
    .bin .add (.bin .add (.reg 10) (.const 11))
      (.bin .add (.bin .mul (.const 7) (.reg 8)) (.bin .mul (.const 9) (.reg 9)))] ;;
  .ret (.reg 11)

/-- The graph with the vertices `V` and no edge. -/
def asmFirstInitEmptyOn (V : Finset ℕ) : MGraph :=
  { V := V, E := ∅, tail := fun _ => 0, head := fun _ => 0 }

/-- The view that P10's restart reads at the init: the input graph `G`, the LSF `lsf`, and the
graph of the roots `R` with no edge. -/
noncomputable def asmFirstInitView (G : MGraph) (lsf : MinCostFlow.LSF) (R : Finset ℕ) :
    ReadView :=
  ⟨G, lsf, asmFirstInitEmptyOn R, fun _ => 1, fun _ => 1⟩

end

public section

theorem asmFirstInitS0Body_noRand (fLists fRebuild : ℕ) :
    (asmFirstInitS0Body fLists fRebuild).NoRand := by
  simp [asmFirstInitS0Body, Stmt.NoRand]

/-- **The run of `S₀` at the init.** The slots listed at `slotsPtr` are active in the spanner
table `S6`, the `nR` roots at `rootsPtr` have no repeats and lie below `vCap`, `G` lies at `graph`,
P4 holds `s4`, and its root query gives the roots of `lsf` on `G`. All of this lies below `h`,
and memory from `h` on is zero. Then the procedure ends with `h + 5` holding `h + 7`, the graph
`((asmFirstInitView G lsf R).rebuild SP S6 slots).S` at `h + 7`, P4 kept, and memory below `h`
unchanged outside P4. The cost is that of P10's restart, plus `130` per root and `200`. -/
theorem asmFirstInitS0_runs {w vCap eCap cap : ℕ} {SP : DSParams} {p : Program}
    {bOps bEdge bSplit bBatch bLoop fRoot bSelf : ℕ} {Q : RootQueryAt w p fRoot}
    (hpOps : p.HasAt bOps dgOpsProcs) (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpLoop : p.HasAt bLoop (readLoopProcs bEdge))
    (hpSelf : p.HasAt bSelf (readRestartProcs bOps bEdge bLoop fRoot bSelf))
    {b4 j graph spanTbl slotsPtr rootsPtr h pos : ℕ} {slots roots : List ℕ} {G : MGraph}
    {lsf : MinCostFlow.LSF} {S6 : BucketSpannerState cap} {x6 : (bucketSpannerRep SP cap).τ}
    {s4 : Q.σ} {x4 : Q.R.τ} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hSPe : SP.eCap ≤ eCap)
    (hb4W : b4 < 2 ^ w) (hjW : j < 2 ^ w) (hspanW : spanTbl < 2 ^ w)
    (hrootsW : rootsPtr < 2 ^ w)
    (hlist : ListAt mem slotsPtr slots) (hlist_h : slotsPtr + slots.length ≤ h)
    (hact : ∀ s ∈ slots, ∃ hs : s < cap, (S6 ⟨s, hs⟩).isSome)
    (hroots : ListAt mem rootsPtr roots) (hroots_h : rootsPtr + roots.length ≤ h)
    (hrV : ∀ v ∈ roots, v < vCap)
    (hG : DynGraphAt mem graph vCap eCap G) (hgB : graph + dynGraphSize vCap eCap ≤ h)
    (hrep6 : (bucketSpannerRep SP cap).rep spanTbl S6 x6 mem)
    (hrep4 : Q.R.rep b4 s4 x4 mem)
    (hQok : ∀ u ∈ G.V, Q.ok s4 j u ∧ Q.root s4 j u = lsf.F.root u)
    (hfoot6 : ∀ a, (bucketSpannerRep SP cap).foot spanTbl x6 a → a < h)
    (hfoot4 : ∀ a, Q.R.foot b4 x4 a → a < h)
    (hdisj_G4 : ∀ a, graph ≤ a → a < graph + dynGraphSize vCap eCap → ¬ Q.R.foot b4 x4 a)
    (hdisj_64 : ∀ a, (bucketSpannerRep SP cap).foot spanTbl x6 a → ¬ Q.R.foot b4 x4 a)
    (hz : ZeroFrom mem h)
    (hroom : h + 7 + dynGraphSize vCap eCap + slots.length + 2 * rebuildSize SP S6 slots + 2 <
      2 ^ w) :
    ∃ o st' c x4', Runs w p ω (asmFirstInitS0Body (bBatch + dgIdxInitFromLists)
          (bSelf + readRestartIdxMain))
        (startState [b4, j, graph, spanTbl, slots.length, slotsPtr, rootsPtr, roots.length, vCap,
          eCap, h] mem pos) o st' c ∧
      st'.mem (h + 5) = h + 7 ∧
      DynGraphAt st'.mem (h + 7) vCap eCap
        ((asmFirstInitView G lsf roots.toFinset).rebuild SP S6 slots).S ∧
      Q.R.rep b4 s4 x4' st'.mem ∧
      h + 7 + dynGraphSize vCap eCap ≤ o.value ∧
      o.value ≤ h + 7 + dynGraphSize vCap eCap + slots.length + 2 * rebuildSize SP S6 slots ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ Q.R.foot b4 x4 a → st'.mem a = mem a) ∧
      (∀ a, Q.R.foot b4 x4' a → Q.R.foot b4 x4 a ∨ (h ≤ a ∧ a < o.value)) ∧
      c + Q.R.phi b4 x4' st'.mem ≤
        (800 + 2 * Q.cost) * (rebuildSize SP S6 slots + slots.length + 1) +
          130 * roots.length + 200 + Q.R.phi b4 x4 mem := by
  set n := slots.length with hn
  set nR := roots.length with hnR
  set hE := h + 7 + dynGraphSize vCap eCap with hhE
  have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hhW : h + 7 < 2 ^ w := by omega
  have hvW : vCap < 2 ^ w := by omega
  have heW : eCap < 2 ^ w := by omega
  have hnW : n < 2 ^ w := by omega
  have hslW : slotsPtr < 2 ^ w := by omega
  have hnRW : nR < 2 ^ w := by omega
  have hgW : graph < 2 ^ w := by omega
  set st0 := startState [b4, j, graph, spanTbl, n, slotsPtr, rootsPtr, nR, vCap, eCap, h] mem pos
    with hst0
  have r10 : st0.regs 10 = h := by simp [hst0, startState]
  -- Step 1: the two words of the record.
  set st1 : State := { st0 with mem := Function.update st0.mem (h + 5) (h + 7) } with hst1
  have q1 : Runs w p ω (.store (.bin .add (.reg 10) (.const 5)) (.bin .add (.reg 10) (.const 7)))
      st0 .normal st1 7 :=
    runs_store_iff.mpr ⟨h + 5, h + 7,
      Expr.eval_add (Expr.eval_reg_of_eq r10) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_add (Expr.eval_reg_of_eq r10) (Expr.eval_const (by omega)) (by omega),
      rfl, rfl, by simp [Expr.size]⟩
  set st2 : State := { st1 with mem := Function.update st1.mem (h + 6) graph } with hst2
  have q2 : Runs w p ω (.store (.bin .add (.reg 10) (.const 6)) (.reg 2)) st1 .normal st2 5 :=
    runs_store_iff.mpr ⟨h + 6, graph,
      Expr.eval_add (Expr.eval_reg_of_eq r10) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq (by simp [hst1, hst0, startState]), rfl, rfl, by simp [Expr.size]⟩
  have hm2 : ∀ a, a ≠ h + 5 → a ≠ h + 6 → st2.mem a = mem a := by
    intro a h5 h6
    simp [hst2, hst1, hst0, startState, Function.update_of_ne h5, Function.update_of_ne h6]
  have hm2lo : ∀ a < h, st2.mem a = mem a := fun a ha => hm2 a (by omega) (by omega)
  have hm25 : st2.mem (h + 5) = h + 7 := by simp [hst2, hst1]
  have hm26 : st2.mem (h + 6) = graph := by simp [hst2]
  -- Step 2: the graph of the roots.
  have hL := dgInitFromLists_meetsContract (w := w) (vCap := vCap) (eCap := eCap)
    (G := asmFirstInitEmptyOn roots.toFinset) (vL := roots) (eEdges := []) hpBatch hpEdge hpOps
  have hargsL : evalArgs w st2
      [.bin .add (.reg 10) (.const 7), .reg 8, .reg 9, .reg 7, .reg 6, .const 0, .const 0] =
      some [h + 7, vCap, eCap, nR, rootsPtr, 0, 0] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hst2, hst1, hst0, startState, hhW,
      show (7 : ℕ) < 2 ^ w by omega, show (0 : ℕ) < 2 ^ w by omega]
  obtain ⟨bodyL, hbL, oL, stL, cL, hrunL, hpostL, hcL⟩ :=
    hL [h + 7, vCap, eCap, nR, rootsPtr, 0, 0] st2.mem st2.pos ω
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      ⟨h + 7, nR, rootsPtr, 0, 0, rfl, hw16, by omega,
        fun a ha => by rw [hm2 a (by omega) (by omega)]; exact hz a (by omega),
        fun e he => by simp [asmFirstInitEmptyOn] at he,
        fun v hv => hrV v (by simpa [asmFirstInitEmptyOn] using hv),
        fun e he => by simp [asmFirstInitEmptyOn] at he,
        rfl, fun i hi => by rw [hm2lo _ (by omega)]; exact hroots i hi,
        fun v => by simp [asmFirstInitEmptyOn],
        fun i hi => by omega, rfl, by simp, fun i hi => by simp at hi,
        fun t ht => by simp at ht, fun e he => by simp [asmFirstInitEmptyOn] at he,
        fun i hi => by omega⟩
  obtain ⟨_, _, _, _, _, hEqL, _, hGL, hfrL, hzL⟩ := hpostL
  simp only [List.cons.injEq, true_and, and_true] at hEqL
  obtain ⟨rfl, -, -, -, -⟩ := hEqL
  set st3 : State := { stL with regs := Function.update st2.regs 11 oL.value } with hst3
  have hcall3 : Runs w p ω (.call 11 (bBatch + dgIdxInitFromLists)
      [.bin .add (.reg 10) (.const 7), .reg 8, .reg 9, .reg 7, .reg 6, .const 0, .const 0])
      st2 .normal st3
      (argsSize [.bin .add (.reg 10) (.const 7), .reg 8, .reg 9, .reg 7, .reg 6, .const 0,
        .const 0] + cL + 1) :=
    runs_call_iff.mpr ⟨_, bodyL, oL, stL, cL, hargsL, hbL, hrunL, rfl, rfl, rfl⟩
  have hm3 : ∀ a, (a < h + 7 ∨ hE ≤ a) → st3.mem a = st2.mem a := fun a ha =>
    hfrL a (by rcases ha with ha | ha <;> [exact Or.inl ha; exact Or.inr (by omega)])
  have hm3lo : ∀ a < h, st3.mem a = mem a := fun a ha => by
    rw [hm3 a (Or.inl (by omega)), hm2lo a ha]
  -- Step 3: P10's restart.
  have hkeep : ∀ a < h, mem a = st3.mem a := fun a ha => (hm3lo a ha).symm
  have hrep6' := ((bucketSpannerRep_local SP cap) spanTbl S6 x6 mem st3.mem
    fun a ha => hkeep a (hfoot6 a ha)).1 hrep6
  have hrep4' := (Q.R_local b4 s4 x4 mem st3.mem fun a ha => hkeep a (hfoot4 a ha)).1 hrep4
  have hphi4' := (Q.R_local b4 s4 x4 mem st3.mem fun a ha => hkeep a (hfoot4 a ha)).2
  have hG3 : DynGraphAt st3.mem graph vCap eCap G :=
    hG.of_agree fun a ha1 ha2 => (hkeep a (by omega)).symm
  have hSPI := readRestart_core_runs (cap := cap) (SP := SP) (Q := Q)
    hpOps hpEdge hpLoop hpSelf (r := h) (sPtr := h + 7) (gPtr := graph) (spanTbl := spanTbl)
    (slotsPtr := slotsPtr) (b4 := b4) (j := j) (h := hE) (slots := slots)
    (v := asmFirstInitView G lsf roots.toFinset) (S6 := S6) (x6 := x6) (s4 := s4) (x4 := x4)
    (mem := st3.mem) (pos := st3.pos) (ω := ω)
    hw16 hSPe (by omega) hspanW hnW hslW hb4W hjW
    (fun i hi => by rw [hm3lo _ (by omega)]; exact hlist i hi) (by omega) hact
    (by rw [hm3 _ (Or.inl (by omega))]; exact hm25)
    (by rw [hm3 _ (Or.inl (by omega))]; exact hm26)
    hGL hG3 (by omega) (by omega) (fun a ha1 ha2 => Or.inr (by omega)) hrep6' hrep4' hQok
    (fun a ha => by have := hfoot6 a ha; omega) (fun a ha => by have := hfoot4 a ha; omega)
    (fun a ha1 ha2 hf => by have := hfoot6 a hf; omega)
    (fun a ha1 ha2 hf => by have := hfoot4 a hf; omega) hdisj_G4 hdisj_64 hzL (by omega)
  obtain ⟨oR, stR, cR, x4', hrunR, hSR, hrep4R, hlo, hhi, hzR, hfrR, hftR, hcR⟩ := hSPI
  have hbR : p.procs[bSelf + readRestartIdxMain]? = some (readRestartStmt
      (bSelf + readRestartIdxCopy) (bSelf + readRestartIdxDel) (bSelf + readRestartIdxAdd)) :=
    hpSelf.get (i := readRestartIdxMain) (by simp [readRestartProcs, readRestartIdxMain])
  have hr3 : ∀ r, r ≠ 11 → st3.regs r = st0.regs r := by
    intro r hr
    simp [hst3, hst2, hst1, Function.update_of_ne hr]
  have r3_10 : st3.regs 10 = h := (hr3 10 (by decide)).trans r10
  have r3_8 : st3.regs 8 = vCap := (hr3 8 (by decide)).trans (by simp [hst0, startState])
  have r3_9 : st3.regs 9 = eCap := (hr3 9 (by decide)).trans (by simp [hst0, startState])
  have e1 : (Expr.bin .add (.reg 10) (.const 11)).eval w st3 = some (h + 11) :=
    Expr.eval_add (Expr.eval_reg_of_eq r3_10) (Expr.eval_const (by omega)) (by omega)
  have e2 : (Expr.bin .mul (.const 7) (.reg 8)).eval w st3 = some (7 * vCap) :=
    Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r3_8) (by omega)
  have e3 : (Expr.bin .mul (.const 9) (.reg 9)).eval w st3 = some (9 * eCap) :=
    Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r3_9) (by omega)
  have e4 := Expr.eval_add e2 e3 (by omega)
  have e5 := Expr.eval_add e1 e4 (by omega)
  have hE' : h + 11 + (7 * vCap + 9 * eCap) = hE := by omega
  rw [hE'] at e5
  have hargsR : evalArgs w st3 [.reg 10, .reg 3, .reg 4, .reg 5, .reg 0, .reg 1,
      .bin .add (.bin .add (.reg 10) (.const 11))
        (.bin .add (.bin .mul (.const 7) (.reg 8)) (.bin .mul (.const 9) (.reg 9)))] =
      some [h, spanTbl, n, slotsPtr, b4, j, hE] := by
    simp only [evalArgs, e5]
    simp [Expr.eval, hr3, hst0, startState]
  set st4 : State := { stR with regs := Function.update st3.regs 11 oR.value } with hst4
  have hcall4 : Runs w p ω (.call 11 (bSelf + readRestartIdxMain) [.reg 10, .reg 3, .reg 4,
      .reg 5, .reg 0, .reg 1, .bin .add (.bin .add (.reg 10) (.const 11))
        (.bin .add (.bin .mul (.const 7) (.reg 8)) (.bin .mul (.const 9) (.reg 9)))])
      st3 .normal st4
      (argsSize [.reg 10, .reg 3, .reg 4, .reg 5, .reg 0, .reg 1,
        .bin .add (.bin .add (.reg 10) (.const 11))
          (.bin .add (.bin .mul (.const 7) (.reg 8)) (.bin .mul (.const 9) (.reg 9)))] + cR + 1) :=
    runs_call_iff.mpr ⟨_, _, oR, stR, cR, hargsR, hbR, hrunR, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 11)) st4 (.returned oR.value) st4 2 :=
    runs_ret_iff.mpr ⟨_, by simp [Expr.eval, hst4], rfl, rfl, rfl⟩
  have t1 := runs_seq_iff.mpr (Or.inr ⟨st4, _, _, hcall4, hret, rfl⟩)
  have t2 := runs_seq_iff.mpr (Or.inr ⟨st3, _, _, hcall3, t1, rfl⟩)
  have t3 := runs_seq_iff.mpr (Or.inr ⟨st2, _, _, q2, t2, rfl⟩)
  have t4 := runs_seq_iff.mpr (Or.inr ⟨st1, _, _, q1, t3, rfl⟩)
  have hkR : ∀ a < h, ¬ Q.R.foot b4 x4 a → stR.mem a = st3.mem a := fun a ha hn' =>
    hfrR a (by omega) (Or.inl (by omega)) hn'
  refine ⟨_, _, _, x4', t4, ?_, hSR, hrep4R, hlo, hhi, hzR, ?_, ?_, ?_⟩
  · show stR.mem (h + 5) = h + 7
    rw [hfrR _ (by omega) (Or.inl (by omega)) (fun hf => by have := hfoot4 _ hf; omega),
      hm3 _ (Or.inl (by omega))]
    exact hm25
  · intro a ha hn'
    show stR.mem a = mem a
    rw [hkR a ha hn', hm3lo a ha]
  · intro a ha
    rcases hftR a ha with h4 | ⟨h1, h2⟩
    · exact Or.inl h4
    · exact Or.inr ⟨by omega, h2⟩
  · have hcL' : cL ≤ 130 * nR + 100 := by
      simpa [dgInitFromListsContract] using hcL
    rw [← hn] at hcR
    simp only [argsSize, Expr.size] at hcR ⊢
    show _ + Q.R.phi b4 x4' stR.mem ≤ _
    omega

end

end MinCostFlow.SparseCore.Program
