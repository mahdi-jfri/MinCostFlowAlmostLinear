module

public import MinCostFlow.SparseCore.Program.CompInitEdgefulInv
import WordRAM.Tactic

/-!
# Edgeful Component Initialization Step (`CompInitEdgeful`)

Proves `compInitEdgeful_runs`, verifying `compInitEdgefulStmt` (BFS discovery via
`compBfsCompProc`, subgraph `DynGraphAt` build via `dgInitFromLists`, and `k`-branch window
initialization via `W.initOff`) for a single unvisited edgeful component `C ∈ edgefulComps G₀`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- First half of `compInitEdgefulStmt`: BFS discovery, component metadata stores, and
`dgInitFromLists` for the component subgraph. -/
private def compInitEfPart1 (bBfs bDgInit : ℕ) : Stmt :=
  .call 41 bBfs [.reg 0, .reg 29, .reg 16, .reg 21, .reg 22, .reg 30, .reg 31,
    .reg 37, .reg 33, .bin .add (.reg 20) (.reg 33)] ;;
  .assign 42 (.load (.bin .add (.reg 20) (.reg 33))) ;;
  .store (.bin .add (.reg 17) (.reg 33)) (.const 1) ;;
  .store (.bin .add (.reg 18) (.reg 33)) (.reg 34) ;;
  .store (.bin .add (.reg 19) (.reg 33)) (.reg 41) ;;
  .call 43 bDgInit [.reg 32, .reg 6, .reg 7, .reg 41, .reg 30, .reg 42, .reg 31]

/-- Second half of `compInitEdgefulStmt`: `handlesOut`/`winHeap` calculation, `W.initOff` call,
and advancing `ec`/`c`. -/
private def compInitEfPart2 (bWinInit : ℕ) : Stmt :=
  .assign 44 (.bin .add (.reg 28) (.bin .mul (.reg 34) (.reg 4))) ;;
  .assign 45 (.bin .add (.reg 32) (.reg 36)) ;;
  .call 32 bWinInit [.reg 32, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7,
    .reg 44, .reg 45] ;;
  .assign 34 (.bin .add (.reg 34) (.const 1)) ;;
  .assign 33 (.bin .add (.reg 33) (.const 1))

private lemma runs_compInitEf_split {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {bBfs bDgInit bWinInit : ℕ} {st0 st1 st2 : State} {c1 c2 : ℕ}
    (h1 : Runs w p ω (compInitEfPart1 bBfs bDgInit) st0 .normal st1 c1)
    (h2 : Runs w p ω (compInitEfPart2 bWinInit) st1 .normal st2 c2) :
    Runs w p ω (compInitEdgefulStmt bBfs bDgInit bWinInit) st0 .normal st2 (c1 + c2 + 1) := by
  -- Reassociate the 6-stmt + 5-stmt sequential composition into the right-nested 11-stmt block.
  rcases runs_seq_iff.mp h1 with ⟨_, _, _, _, _⟩ | ⟨s1, d1, r1, hs1, hr1, hc1⟩
  · cases ‹Outcome.normal = _›
  rcases runs_seq_iff.mp hr1 with ⟨_, _, _, _, _⟩ | ⟨s2, d2, r2, hs2, hr2, hc2⟩
  · cases ‹Outcome.normal = _›
  rcases runs_seq_iff.mp hr2 with ⟨_, _, _, _, _⟩ | ⟨s3, d3, r3, hs3, hr3, hc3⟩
  · cases ‹Outcome.normal = _›
  rcases runs_seq_iff.mp hr3 with ⟨_, _, _, _, _⟩ | ⟨s4, d4, r4, hs4, hr4, hc4⟩
  · cases ‹Outcome.normal = _›
  rcases runs_seq_iff.mp hr4 with ⟨_, _, _, _, _⟩ | ⟨s5, d5, d6, hs5, hs6, hc5⟩
  · cases ‹Outcome.normal = _›
  exact runs_seq_iff.mpr (Or.inr ⟨s1, d1, d2 + d3 + d4 + d5 + d6 + c2 + 5, hs1,
    runs_seq_iff.mpr (Or.inr ⟨s2, d2, d3 + d4 + d5 + d6 + c2 + 4, hs2,
      runs_seq_iff.mpr (Or.inr ⟨s3, d3, d4 + d5 + d6 + c2 + 3, hs3,
        runs_seq_iff.mpr (Or.inr ⟨s4, d4, d5 + d6 + c2 + 2, hs4,
          runs_seq_iff.mpr (Or.inr ⟨s5, d5, d6 + c2 + 1, hs5,
            runs_seq_iff.mpr (Or.inr ⟨st1, d6, c2, hs6, h2, rfl⟩),
            by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩)

private lemma compInitEfPart1_runs {W : LSFWindowImpl} {w k : ℕ} {G₀ : MGraph} {p : Program}
    {mem0 : ℕ → ℕ} {ω : ℕ → Bool}
    (ctx : InitCtx W w k G₀ p mem0)
    {v curHeap iNext : ℕ} {comps : List (Finset ℕ)} {efIdx : List ℕ}
    {winH : ℕ → ℕ → ℕ} {winX : ℕ → ℕ → LSFConcrete} {st5 : State}
    (hvG : v ∈ G₀.V) (hvis : ¬ ∃ X ∈ comps, v ∈ X)
    (hc_lt0 : comps.length < ctx.vCap0)
    (hcur_dg_lt : curHeap + dynGraphSize ctx.vCap ctx.eCap < 2 ^ w)
    (hR5 : InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
      ctx.vCap0 G₀.n G₀.m st5.regs)
    (hr32 : st5.regs 32 = curHeap) (hr33 : st5.regs 33 = comps.length)
    (hr34 : st5.regs 34 = efIdx.length) (hr35 : st5.regs 35 = iNext) (hr37 : st5.regs 37 = v)
    (hInv : InitMemInv ctx st5.mem curHeap comps efIdx winH winX) :
    let C := compOf G₀ v
    let nC := (compGraph G₀ C).n
    let mC := (compGraph G₀ C).m
    ∃ st11 mBfs c1,
      Runs w p ω (compInitEfPart1 ctx.bBfs ctx.bDgInit) st5 .normal st11 c1 ∧
      InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
        ctx.vCap0 G₀.n G₀.m st11.regs ∧
      st11.regs 32 = curHeap ∧ st11.regs 33 = comps.length ∧
      st11.regs 34 = efIdx.length ∧ st11.regs 35 = iNext ∧
      mBfs (compM0Base ctx.b ctx.vCap + comps.length) = mC ∧
      (∀ u < ctx.vCap0, mBfs (compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + u) =
        if u ∈ comps.toFinset.biUnion id ∪ C then 1 else 0) ∧
      (∀ u ∈ C, mBfs (compVCompBase ctx.b + u) = comps.length) ∧
      (∀ u < ctx.vCap0, u ∉ C → mBfs (compVCompBase ctx.b + u) = st5.mem (compVCompBase ctx.b + u)) ∧
      (∀ e ∈ compEdgeSet G₀ C,
        mBfs (compEdgeC1Base ctx.b ctx.vCap + e) = comps.length ∧
        mBfs (compEdgeC2Base ctx.b ctx.vCap ctx.eCap + e) = comps.length) ∧
      (∀ e < ctx.eCap0, e ∉ compEdgeSet G₀ C →
        mBfs (compEdgeC1Base ctx.b ctx.vCap + e) = st5.mem (compEdgeC1Base ctx.b ctx.vCap + e) ∧
        mBfs (compEdgeC2Base ctx.b ctx.vCap ctx.eCap + e) = st5.mem (compEdgeC2Base ctx.b ctx.vCap ctx.eCap + e)) ∧
      (∀ a,
        (a < compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k ∨
          compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap0 ≤ a) →
        (a < compVCompBase ctx.b ∨ compVCompBase ctx.b + ctx.vCap0 ≤ a) →
        (a < compEdgeC1Base ctx.b ctx.vCap ∨ compEdgeC1Base ctx.b ctx.vCap + ctx.eCap0 ≤ a) →
        (a < compEdgeC2Base ctx.b ctx.vCap ctx.eCap ∨ compEdgeC2Base ctx.b ctx.vCap ctx.eCap + ctx.eCap0 ≤ a) →
        (a < compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap ∨
          compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap + nC ≤ a) →
        (a < compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap + G₀.n ∨
          compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k + ctx.vCap + G₀.n + 3 * mC ≤ a) →
        a ≠ compM0Base ctx.b ctx.vCap + comps.length → mBfs a = st5.mem a) ∧
      DynGraphAt st11.mem curHeap ctx.vCap ctx.eCap (compGraph G₀ C) ∧
      ZeroFrom st11.mem (curHeap + dynGraphSize ctx.vCap ctx.eCap) ∧
      (∀ a < curHeap, st11.mem a =
        Function.update
          (Function.update
            (Function.update mBfs (compEdgefulBase ctx.b ctx.vCap + comps.length) 1)
            (compEdgefulIdxBase ctx.b ctx.vCap + comps.length) efIdx.length)
          (compN0Base ctx.b ctx.vCap + comps.length) nC a) ∧
      c1 ≤ 230 * nC + 840 * mC + 326 := by
  classical
  dsimp only
  set C := compOf G₀ v
  set nC := (compGraph G₀ C).n
  set mC := (compGraph G₀ C).m
  set visBase := compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k
  set bfsQBase := visBase + ctx.vCap
  set compEdgesBase := bfsQBase + G₀.n
  have hw1 : 1 < 2 ^ w := by have := ctx.hw16; omega
  have hsp_lt := ctx.hsp_lt
  have hstat_lt : ctx.b + compStaticSize ctx.vCap ctx.eCap ctx.L_w < 2 ^ w := by
    dsimp [InitCtx.heap0, compTablesEnd, compHandlesBase] at hsp_lt; omega
  have hC_mem : C ∈ components G₀ := Finset.mem_image.mpr ⟨v, hvG, rfl⟩
  have hvC : v ∈ C := self_mem_compOf hvG
  have hC_not : C ∉ comps := fun hCm => hvis ⟨C, hCm, hvC⟩
  have hDisjC : ∀ X ∈ comps, Disjoint X C := fun X hX =>
    comp_disjoint_of_ne G₀ (hInv.2.2.2.2.2.1 X hX) hC_mem (fun h => hC_not (h ▸ hX))
  have hc_lt : comps.length < ctx.vCap := lt_of_lt_of_le hc_lt0 ctx.hvCap_le
  have hv_lt0 : v < ctx.vCap0 := ctx.hdg.2.1 v hvG
  have hv_lt : v < ctx.vCap := lt_of_lt_of_le hv_lt0 ctx.hvCap_le
  have hnC_le : nC ≤ G₀.n := compGraph_n_le hC_mem
  have hmC_le : mC ≤ G₀.m := compGraph_m_le
  set visSet : Finset ℕ := comps.toFinset.biUnion id
  have hvisSet_sub : visSet ⊆ G₀.V := fun u hu => by
    rcases Finset.mem_biUnion.mp hu with ⟨X, hX, huX⟩
    rcases Finset.mem_image.mp (hInv.2.2.2.2.2.1 X (List.mem_toFinset.mp hX)) with ⟨w', _, rfl⟩
    exact (mem_compOf_iff.mp huX).1
  have hvisSet_disj : Disjoint visSet C := by
    rw [Finset.disjoint_left]
    intro u hu huC
    rcases Finset.mem_biUnion.mp hu with ⟨X, hX, huX⟩
    exact Finset.disjoint_left.mp (hDisjC X (List.mem_toFinset.mp hX)) huX huC
  -- Region ordering
  have hB_vc : ctx.b + compHdrSize = compVCompBase ctx.b := rfl
  have hVC_ef : compVCompBase ctx.b + ctx.vCap = compEdgefulBase ctx.b ctx.vCap := rfl
  have hEF_efi : compEdgefulBase ctx.b ctx.vCap + ctx.vCap = compEdgefulIdxBase ctx.b ctx.vCap := rfl
  have hEFI_n0 : compEdgefulIdxBase ctx.b ctx.vCap + ctx.vCap = compN0Base ctx.b ctx.vCap := rfl
  have hN0_m0 : compN0Base ctx.b ctx.vCap + ctx.vCap = compM0Base ctx.b ctx.vCap := rfl
  have hM0_ec1 : compM0Base ctx.b ctx.vCap + ctx.vCap = compEdgeC1Base ctx.b ctx.vCap := rfl
  have hEC1_ec2 : compEdgeC1Base ctx.b ctx.vCap + ctx.eCap = compEdgeC2Base ctx.b ctx.vCap ctx.eCap := rfl
  have hEC2_vis : compEdgeC2Base ctx.b ctx.vCap ctx.eCap + ctx.eCap ≤ visBase := by
    dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compEdgeC2Base,
      compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase,
      compVCompBase, compHdrSize]; omega
  have hVis_h0 : visBase + ctx.vCap + G₀.n + 3 * G₀.m = ctx.heap0 := rfl
  have hch_ge : ctx.heap0 ≤ curHeap := hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hg0_le : ctx.g0Ptr + dynGraphSize ctx.vCap0 ctx.eCap0 ≤ ctx.b := ctx.hg0_le
  have hv_le : ctx.vCap0 ≤ ctx.vCap := ctx.hvCap_le
  have he_le : ctx.eCap0 ≤ ctx.eCap := ctx.heCap_le
  -- Step A: `compBfsCompProc` call
  have hdg_st5 : DynGraphAt st5.mem ctx.g0Ptr ctx.vCap0 ctx.eCap0 G₀ :=
    DynGraphAt.of_agree ctx.hdg fun a _ ha2 =>
      hInv.1 a (lt_of_lt_of_le ha2 hg0_le)
  have hBfsPre : (compBfsCompContract w ctx.vCap0 ctx.eCap0 G₀ C visSet).pre
      [ctx.g0Ptr, visBase, compVCompBase ctx.b, compEdgeC1Base ctx.b ctx.vCap,
       compEdgeC2Base ctx.b ctx.vCap ctx.eCap, bfsQBase, compEdgesBase, v,
       comps.length, compM0Base ctx.b ctx.vCap + comps.length] st5.mem := by
    refine ⟨ctx.g0Ptr, visBase, compVCompBase ctx.b, compEdgeC1Base ctx.b ctx.vCap,
      compEdgeC2Base ctx.b ctx.vCap ctx.eCap, bfsQBase, compEdgesBase, v,
      comps.length, compM0Base ctx.b ctx.vCap + comps.length,
      rfl, ctx.hw16, hdg_st5, hC_mem, hvC, hvisSet_sub, hvisSet_disj,
      fun u hu => by rw [hInv.2.2.2.2.2.2.2.2.2.1 u (lt_of_lt_of_le hu hv_le)]; simp [visSet],
      hc_lt0, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega),
      Or.inl (by omega), Or.inl (by omega), Or.inl (by omega),
      Or.inr (by omega), Or.inr (by omega), Or.inr (by omega),
      Or.inl (by omega), Or.inl (by omega), Or.inr (by omega),
      Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega),
      Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inr (by omega),
      Or.inl (by omega), Or.inl (by omega), Or.inr (by omega),
      Or.inl (by omega), Or.inr (by omega), Or.inr (by omega)⟩
  have hBfsArgs : ∀ a ∈ [ctx.g0Ptr, visBase, compVCompBase ctx.b, compEdgeC1Base ctx.b ctx.vCap,
      compEdgeC2Base ctx.b ctx.vCap ctx.eCap, bfsQBase, compEdgesBase, v,
      comps.length, compM0Base ctx.b ctx.vCap + comps.length], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ctx.hargs _ (by simp)
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  obtain ⟨bodyBfs, hBfs_get, oBfs, stBfs, cBfs, hBfs_run, hBfs_post, hBfs_cost⟩ :=
    compBfsComp_meetsContract ctx.hpBfs _ st5.mem st5.pos ω hBfsArgs hBfsPre
  rcases hBfs_post with ⟨g0', vis', vc', ec1', ec2', bq', ce', v0', c', m0', heqBfs, hBfs_ret,
    hBfs_m0, hBfs_vis, hBfs_vc, hBfs_vc_fr, hBfs_eC, hBfs_eC_fr,
    ⟨qL, hqL_len, hqL_nd, hqL_mem, hqL_at⟩,
    ⟨eL, heL_len, heL_nd, heL_at, heL_spec, heL_cov⟩, hBfs_fr⟩
  simp only [List.cons.injEq, and_true] at heqBfs
  rcases heqBfs with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  let st6 : State := { mem := stBfs.mem, regs := Function.update st5.regs 41 nC, pos := stBfs.pos }
  have hm0a_w : compM0Base ctx.b ctx.vCap + comps.length < 2 ^ w := hBfsArgs _ (by simp)
  have hcallBfs : Runs w p ω
      (.call 41 ctx.bBfs [.reg 0, .reg 29, .reg 16, .reg 21, .reg 22, .reg 30, .reg 31, .reg 37, .reg 33,
        .bin .add (.reg 20) (.reg 33)])
      st5 .normal st6 (12 + cBfs + 1) := by
    refine runs_call_iff.mpr ⟨_, bodyBfs, oBfs, stBfs, cBfs, ?_, hBfs_get, hBfs_run, rfl,
      by simp [st6, hBfs_ret, nC], by simp [argsSize, Expr.size]⟩
    simp [evalArgs, Expr.eval, BinOp.eval,
      hR5.r0, hR5.r29, hR5.r16, hR5.r21, hR5.r22, hR5.r30, hR5.r31, hr37, hr33, hR5.r20,
      visBase, bfsQBase, compEdgesBase, hm0a_w]
  -- Step B: load `mC`, store `edgeful[c] := 1`, `edgefulIdx[c] := ec`, `n0[c] := nC`
  let st7 : State := { st6 with regs := Function.update st6.regs 42 mC }
  let m8 := Function.update st7.mem (compEdgefulBase ctx.b ctx.vCap + comps.length) 1
  let m9 := Function.update m8 (compEdgefulIdxBase ctx.b ctx.vCap + comps.length) efIdx.length
  let m10 := Function.update m9 (compN0Base ctx.b ctx.vCap + comps.length) nC
  have hst7 : Runs w p ω (.assign 42 (.load (.bin .add (.reg 20) (.reg 33)))) st6 .normal st7 5 :=
    runs_assign_iff.mpr ⟨mC, Expr.eval_load_of_eq
      (by simp [st6, Expr.eval, BinOp.eval, hR5.r20, hr33, hm0a_w]) hBfs_m0,
      rfl, rfl, by simp [Expr.size]⟩
  have hst8 : Runs w p ω (.store (.bin .add (.reg 17) (.reg 33)) (.const 1)) st7 .normal { st7 with mem := m8 } 5 :=
    runs_store_iff.mpr ⟨compEdgefulBase ctx.b ctx.vCap + comps.length, 1,
      by simp [st7, st6, Expr.eval, BinOp.eval, hR5.r17, hr33,
        show compEdgefulBase ctx.b ctx.vCap + comps.length < 2 ^ w by omega],
      by simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
  have hst9 : Runs w p ω (.store (.bin .add (.reg 18) (.reg 33)) (.reg 34))
      { st7 with mem := m8 } .normal { st7 with mem := m9 } 5 :=
    runs_store_iff.mpr ⟨compEdgefulIdxBase ctx.b ctx.vCap + comps.length, efIdx.length,
      by simp [st7, st6, Expr.eval, BinOp.eval, hR5.r18, hr33,
        show compEdgefulIdxBase ctx.b ctx.vCap + comps.length < 2 ^ w by omega],
      by simp [st7, st6, Expr.eval, hr34], rfl, rfl, by simp [Expr.size]⟩
  have hst10 : Runs w p ω (.store (.bin .add (.reg 19) (.reg 33)) (.reg 41))
      { st7 with mem := m9 } .normal { st7 with mem := m10 } 5 :=
    runs_store_iff.mpr ⟨compN0Base ctx.b ctx.vCap + comps.length, nC,
      by simp [st7, st6, Expr.eval, BinOp.eval, hR5.r19, hr33,
        show compN0Base ctx.b ctx.vCap + comps.length < 2 ^ w by omega],
      by simp [st7, st6, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have hm10_bfs : ∀ a, a ≠ compEdgefulBase ctx.b ctx.vCap + comps.length →
      a ≠ compEdgefulIdxBase ctx.b ctx.vCap + comps.length →
      a ≠ compN0Base ctx.b ctx.vCap + comps.length → m10 a = stBfs.mem a := fun a h1 h2 h3 => by
    dsimp only [m10, m9, m8, st7, st6]
    rw [Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have hm10_ge : ∀ a, ctx.heap0 ≤ a → m10 a = st5.mem a := fun a ha =>
    (hm10_bfs a (by omega) (by omega) (by omega)).trans
    (hBfs_fr a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (by omega))
  -- Step C: `dgInitFromLists` call at `curHeap`
  have hDgPre : (dgInitFromListsContract w ctx.vCap ctx.eCap (compGraph G₀ C) qL eL).pre
      [curHeap, ctx.vCap, ctx.eCap, nC, bfsQBase, mC, compEdgesBase] m10 := by
    have hhz := hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    refine ⟨curHeap, nC, bfsQBase, mC, compEdgesBase, rfl, ctx.hw16, hcur_dg_lt,
      fun a ha => (hm10_ge a (le_trans hch_ge ha)).trans (hhz a ha),
      compGraph_isValid ctx.hG₀ hC_mem,
      fun u hu => lt_of_lt_of_le (ctx.hdg.2.1 u (by
        dsimp [compGraph] at hu; rcases Finset.mem_image.mp hC_mem with ⟨w', _, hEq⟩
        rw [← hEq] at hu; exact (mem_compOf_iff.mp hu).1)) hv_le,
      fun e he => lt_of_lt_of_le (ctx.hdg.2.2.1 e (Finset.filter_subset _ _ he)) he_le,
      hqL_len, fun idx hidx => (hm10_bfs _ (by omega) (by omega) (by omega)).trans (hqL_at idx hidx),
      hqL_mem, fun idx hidx => by omega, heL_len, heL_nd, fun idx hidx => by
        have h3 := heL_at idx hidx
        have hm3 : ∀ d < 3, m10 (compEdgesBase + (3 * idx + d)) = stBfs.mem (compEdgesBase + (3 * idx + d)) :=
          fun d hd => hm10_bfs _ (by omega) (by omega) (by omega)
        exact ⟨by simpa using (hm3 0 (by omega)).trans h3.1,
          by simpa [Nat.add_assoc] using (hm3 1 (by omega)).trans h3.2.1,
          by simpa [Nat.add_assoc] using (hm3 2 (by omega)).trans h3.2.2⟩,
      heL_spec, heL_cov, fun idx hidx => by omega⟩
  have hDgArgs : ∀ a ∈ [curHeap, ctx.vCap, ctx.eCap, nC, bfsQBase, mC, compEdgesBase], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · exact ctx.hargs _ (by simp)
    · exact ctx.hargs _ (by simp)
    · omega
    · omega
    · omega
    · omega
  obtain ⟨bodyDg, hDg_get, oDg, stDg, cDg, hDg_run, hDg_post, hDg_cost⟩ :=
    ctx.hpDg (compGraph G₀ C) qL eL _ m10 st7.pos ω hDgArgs hDgPre
  rcases hDg_post with ⟨gp', vl', vp', el', ep', heqDg, _, hDg_at, hDg_fr, hDg_zf⟩
  simp only [List.cons.injEq, and_true] at heqDg
  rcases heqDg with ⟨rfl, _, _, rfl, rfl, rfl, rfl⟩
  let st11 : State := { mem := stDg.mem, regs := Function.update st7.regs 43 oDg.value, pos := stDg.pos }
  have hcallDg : Runs w p ω
      (.call 43 ctx.bDgInit [.reg 32, .reg 6, .reg 7, .reg 41, .reg 30, .reg 42, .reg 31])
      { st7 with mem := m10 } .normal st11 (7 + cDg + 1) := by
    refine runs_call_iff.mpr ⟨_, bodyDg, oDg, stDg, cDg, ?_, hDg_get, hDg_run, rfl, rfl,
      by simp [argsSize, Expr.size]⟩
    simp [evalArgs, Expr.eval, st7, st6, hr32, hR5.r6, hR5.r7, hR5.r30, hR5.r31,
      bfsQBase, compEdgesBase, visBase]
  have hp1_run : Runs w p ω (compInitEfPart1 ctx.bBfs ctx.bDgInit) st5 .normal st11 (cBfs + cDg + 46) :=
    runs_seq_iff.mpr (Or.inr ⟨st6, 12 + cBfs + 1, cDg + 32, hcallBfs,
      runs_seq_iff.mpr (Or.inr ⟨st7, 5, cDg + 26, hst7,
        runs_seq_iff.mpr (Or.inr ⟨_, 5, cDg + 20, hst8,
          runs_seq_iff.mpr (Or.inr ⟨_, 5, cDg + 14, hst9,
            runs_seq_iff.mpr (Or.inr ⟨_, 5, 7 + cDg + 1, hst10, hcallDg, by omega⟩),
            by omega⟩), by omega⟩), by omega⟩), by omega⟩)
  have hR11 : InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
      ctx.vCap0 G₀.n G₀.m st11.regs :=
    ((hR5.update_mut (by omega)).update_mut (by omega)).update_mut (by omega)
  have hDg_cost' : cDg ≤ 130 * nC + 490 * mC + 100 := by
    simpa [dgInitFromListsContract] using hDg_cost
  have hBfs_cost' : cBfs ≤ 100 * nC + 350 * mC + 180 := by
    simpa [compBfsCompContract, nC, mC] using hBfs_cost
  exact ⟨st11, stBfs.mem, cBfs + cDg + 46, hp1_run, hR11,
    by simp [st11, st7, st6, hr32], by simp [st11, st7, st6, hr33],
    by simp [st11, st7, st6, hr34], by simp [st11, st7, st6, hr35],
    hBfs_m0, hBfs_vis, hBfs_vc, hBfs_vc_fr, hBfs_eC, hBfs_eC_fr, hBfs_fr,
    hDg_at, hDg_zf, fun a ha => hDg_fr a (Or.inl ha), by omega⟩

/-- Execution, invariant preservation, and cost bound for `compInitEdgefulStmt` on an unvisited
edgeful component `C = compOf G₀ v`. -/
lemma compInitEdgeful_runs {W : LSFWindowImpl} {w k : ℕ} {G₀ : MGraph} {p : Program}
    {mem0 : ℕ → ℕ} {ω : ℕ → Bool}
    (ctx : InitCtx W w k G₀ p mem0)
    {v curHeap iNext : ℕ} {comps : List (Finset ℕ)} {efIdx : List ℕ}
    {winH : ℕ → ℕ → ℕ} {winX : ℕ → ℕ → LSFConcrete} {st5 : State}
    (hvG : v ∈ G₀.V)
    (hvis : ¬ ∃ X ∈ comps, v ∈ X)
    (hmC_pos : 1 ≤ (compGraph G₀ (compOf G₀ v)).m)
    (hc_lt0 : comps.length < ctx.vCap0)
    (hR5 : InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
      ctx.vCap0 G₀.n G₀.m st5.regs)
    (hr32 : st5.regs 32 = curHeap) (hr33 : st5.regs 33 = comps.length)
    (hr34 : st5.regs 34 = efIdx.length) (hr35 : st5.regs 35 = iNext) (hr37 : st5.regs 37 = v)
    (hInv : InitMemInv ctx st5.mem curHeap comps efIdx winH winX) :
    let C := compOf G₀ v
    let nC := (compGraph G₀ C).n
    let mC := (compGraph G₀ C).m
    ∃ st16 endHeap winH' winX' c_ef,
      Runs w p ω (compInitEdgefulStmt ctx.bBfs ctx.bDgInit (ctx.bWin + W.initOff))
        st5 .normal st16 c_ef ∧
      InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
        ctx.vCap0 G₀.n G₀.m st16.regs ∧
      st16.regs 32 = endHeap ∧ st16.regs 33 = comps.length + 1 ∧
      st16.regs 34 = efIdx.length + 1 ∧ st16.regs 35 = iNext ∧
      InitMemInv ctx st16.mem endHeap (comps ++ [C]) (efIdx ++ [comps.length]) winH' winX' ∧
      c_ef ≤ W.winCost k ctx.L_w nC mC + 230 * nC + 840 * mC + 360 := by
  classical
  dsimp only
  set C := compOf G₀ v
  set nC := (compGraph G₀ C).n
  set mC := (compGraph G₀ C).m
  have hw1 : 1 < 2 ^ w := by have := ctx.hw16; omega
  have hsp_lt := ctx.hsp_lt
  have hstat_lt : ctx.b + compStaticSize ctx.vCap ctx.eCap ctx.L_w < 2 ^ w := by
    dsimp [InitCtx.heap0, compTablesEnd, compHandlesBase] at hsp_lt; omega
  have hC_mem : C ∈ components G₀ := Finset.mem_image.mpr ⟨v, hvG, rfl⟩
  have hvC : v ∈ C := self_mem_compOf hvG
  have hC_not : C ∉ comps := fun hCm => hvis ⟨C, hCm, hvC⟩
  have hC_ef : C ∈ edgefulComps G₀ := Finset.mem_filter.mpr ⟨hC_mem, hmC_pos⟩
  have hc_lt : comps.length < ctx.vCap := lt_of_lt_of_le hc_lt0 ctx.hvCap_le
  have hef_disj_C : C ∉ comps.toFinset.filter (fun X => 1 ≤ (compGraph G₀ X).m) := fun h =>
    hC_not (List.mem_toFinset.mp (Finset.mem_filter.mp h).1)
  have hef_sub : insert C (comps.toFinset.filter (fun X => 1 ≤ (compGraph G₀ X).m)) ⊆ edgefulComps G₀ := by
    intro X hX
    rcases Finset.mem_insert.mp hX with rfl | hX'
    · exact hC_ef
    · exact Finset.mem_filter.mpr ⟨hInv.2.2.2.2.2.1 X (List.mem_toFinset.mp (Finset.mem_filter.mp hX').1),
        (Finset.mem_filter.mp hX').2⟩
  have hcur_next_lt : curHeap + (dynGraphSize ctx.vCap ctx.eCap +
      W.winSpace k ctx.L_w ctx.vCap ctx.eCap nC mC) < 2 ^ w := by
    have hsum_le : (comps.toFinset.filter (fun X => 1 ≤ (compGraph G₀ X).m)).sum (fun X =>
        dynGraphSize ctx.vCap ctx.eCap +
          W.winSpace k ctx.L_w ctx.vCap ctx.eCap (compGraph G₀ X).n (compGraph G₀ X).m) +
        (dynGraphSize ctx.vCap ctx.eCap +
          W.winSpace k ctx.L_w ctx.vCap ctx.eCap nC mC) ≤
        (edgefulComps G₀).sum (fun X =>
          dynGraphSize ctx.vCap ctx.eCap +
            W.winSpace k ctx.L_w ctx.vCap ctx.eCap (compGraph G₀ X).n (compGraph G₀ X).m) := by
      rw [Nat.add_comm]
      have hins := Finset.sum_insert (f := fun X => dynGraphSize ctx.vCap ctx.eCap +
          W.winSpace k ctx.L_w ctx.vCap ctx.eCap (compGraph G₀ X).n (compGraph G₀ X).m) hef_disj_C
      rw [← hins]
      exact Finset.sum_le_sum_of_subset hef_sub
    have hch_le := hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    clear * - hsum_le hch_le hsp_lt
    omega
  have hec_lt_m0 : efIdx.length < G₀.m := by
    have h1 := init_numEdgeful_le hInv.2.2.2.2.1
      hInv.2.2.2.2.2.2.1 hInv.2.2.2.2.2.2.2.1 hInv.2.2.2.2.2.2.2.2.1
    have h2 : (insert C (comps.toFinset.filter (fun X => 1 ≤ (compGraph G₀ X).m))).sum
        (fun X => (compGraph G₀ X).m) ≤ G₀.m :=
      init_sum_m_le fun X hX => Finset.filter_subset _ _ (hef_sub hX)
    rw [Finset.sum_insert hef_disj_C] at h2
    change mC + _ ≤ G₀.m at h2; omega
  -- Part 1: BFS + metadata stores + `dgInitFromLists`
  obtain ⟨st11, mBfs, c1, hp1_run, hR11, hr11_32, hr11_33, hr11_34, hr11_35,
    hBfs_m0, hBfs_vis, hBfs_vc, hBfs_vc_fr, hBfs_eC, hBfs_eC_fr, hBfs_fr,
    hDg_at, hDg_zf, hDg_m10, hc1_le⟩ :=
    compInitEfPart1_runs (ω := ω) ctx hvG hvis hc_lt0 (by omega) hR5 hr32 hr33 hr34 hr35 hr37 hInv
  -- Part 2: `handlesOut`, `winHeap`, `W.initOff`, `ec++`, `c++`
  set handlesOut := compHandlesBase ctx.b ctx.vCap ctx.eCap ctx.L_w + efIdx.length * k
  set winHeap := curHeap + dynGraphSize ctx.vCap ctx.eCap
  have hch_ge : ctx.heap0 ≤ curHeap := hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hho_le : handlesOut + k ≤ ctx.heap0 := by
    have : (efIdx.length + 1) * k ≤ G₀.m * k := Nat.mul_le_mul_right k hec_lt_m0
    dsimp [handlesOut, InitCtx.heap0, compTablesEnd] at this ⊢; linarith
  have hho_w : handlesOut < 2 ^ w := by clear * - hho_le hsp_lt; omega
  have hwh_w : winHeap < 2 ^ w := by dsimp [winHeap]; clear * - hcur_next_lt; omega
  let st12 : State := { st11 with regs := Function.update st11.regs 44 handlesOut }
  let st13 : State := { st12 with regs := Function.update st12.regs 45 winHeap }
  have hst12 : Runs w p ω (.assign 44 (.bin .add (.reg 28) (.bin .mul (.reg 34) (.reg 4)))) st11 .normal st12 6 :=
    runs_assign_iff.mpr ⟨handlesOut,
      by simp [Expr.eval, BinOp.eval, hR11.r28, hr11_34, hR11.r4, handlesOut,
        show efIdx.length * k < 2 ^ w by dsimp [handlesOut] at hho_w; omega, hho_w],
      rfl, rfl, by simp [Expr.size]⟩
  have hst13 : Runs w p ω (.assign 45 (.bin .add (.reg 32) (.reg 36))) st12 .normal st13 4 :=
    runs_assign_iff.mpr ⟨winHeap,
      by simp [st12, Expr.eval, BinOp.eval, hr11_32, hR11.r36, winHeap, hwh_w],
      rfl, rfl, by simp [Expr.size]⟩
  have hst13_lt_b : ∀ a < ctx.b, st13.mem a = mem0 a := fun a ha => by
    have ha_ch : a < curHeap := by
      dsimp [InitCtx.heap0, compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hch_ge; omega
    have h1 := hDg_m10 a ha_ch
    have h2 : Function.update (Function.update (Function.update mBfs
        (compEdgefulBase ctx.b ctx.vCap + comps.length) 1)
        (compEdgefulIdxBase ctx.b ctx.vCap + comps.length) efIdx.length)
        (compN0Base ctx.b ctx.vCap + comps.length) nC a = mBfs a := by
      rw [Function.update_of_ne (by dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega),
        Function.update_of_ne (by dsimp [compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega),
        Function.update_of_ne (by dsimp [compEdgefulBase, compVCompBase, compHdrSize]; omega)]
    have h3 : mBfs a = st5.mem a := hBfs_fr a
      (Or.inl (by dsimp [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega))
      (Or.inl (by dsimp [compVCompBase, compHdrSize]; omega))
      (Or.inl (by dsimp [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega))
      (Or.inl (by dsimp [compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega))
      (Or.inl (by dsimp [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega))
      (Or.inl (by dsimp [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega))
      (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega)
    exact ((h1.trans h2).trans h3).trans (hInv.1 a ha)
  have hLen_st13 : ∀ e ∈ (compGraph G₀ C).E,
      Valid st13.mem (ctx.lenArr + e * W.L_in) W.h W.L_in ∧
      fixVal st13.mem (ctx.lenArr + e * W.L_in) W.h W.L_in W.P_fp = ctx.ell e ∧
      0 < ctx.ell e := fun e he => by
    have heG : e ∈ G₀.E := Finset.filter_subset _ _ he
    have he_lt : e < ctx.eCap := lt_of_lt_of_le (ctx.hdg.2.2.1 e heG) ctx.heCap_le
    have hagr : ∀ t < W.L_in, st13.mem (ctx.lenArr + e * W.L_in + t) = mem0 (ctx.lenArr + e * W.L_in + t) :=
      fun t ht => hst13_lt_b _ (by
        have : (e + 1) * W.L_in ≤ ctx.eCap * W.L_in := Nat.mul_le_mul_right _ he_lt
        have := ctx.hlen_le; nlinarith)
    obtain ⟨hV, hpos⟩ := ctx.hLen e heG
    have hell_eq : ctx.ell e = fixVal mem0 (ctx.lenArr + e * W.L_in) W.h W.L_in W.P_fp := by
      dsimp only [InitCtx.ell, safeLen, compReadLen]; simp [heG]
    have hV' : Valid st13.mem (ctx.lenArr + e * W.L_in) W.h W.L_in := fun t ht => by
      rw [hagr t ht]; exact hV t ht
    have hfv' : fixVal st13.mem (ctx.lenArr + e * W.L_in) W.h W.L_in W.P_fp =
        fixVal mem0 (ctx.lenArr + e * W.L_in) W.h W.L_in W.P_fp := by
      have huv : ∀ L a, (∀ t < L, st13.mem (a + t) = mem0 (a + t)) →
          unsignedVal st13.mem a W.h L = unsignedVal mem0 a W.h L := by
        intro L; induction L with
        | zero => intro _ _; rfl
        | succ L ih =>
          intro a ha
          simp only [unsignedVal]
          rw [show st13.mem a = mem0 a from by simpa using ha 0 (Nat.zero_lt_succ L),
            ih (a + 1) fun t ht => by
              rw [Nat.add_assoc, Nat.add_comm 1 t]; exact ha (t + 1) (by omega)]
      unfold fixVal intVal
      rw [huv W.L_in (ctx.lenArr + e * W.L_in) hagr]
    exact ⟨hV', hfv'.trans hell_eq.symm, hell_eq.symm ▸ hpos⟩
  have hWinArgs : ∀ a ∈ [curHeap, ctx.lenArr, W.L_in, W.P_fp, k, ctx.L_w, ctx.vCap, ctx.eCap,
      handlesOut, winHeap], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · clear * - hcur_next_lt; omega
    · exact ctx.hargs _ (by simp)
    · exact ctx.hargs _ (by simp)
    · exact ctx.hargs _ (by simp)
    · exact ctx.hargs _ (by simp)
    · exact ctx.hargs _ (by simp)
    · exact ctx.hargs _ (by simp)
    · exact ctx.hargs _ (by simp)
    · exact hho_w
    · exact hwh_w
  have hlen_le_wh : ctx.lenArr + ctx.eCap * W.L_in ≤ winHeap := by
    have := ctx.hlen_le
    dsimp [winHeap, InitCtx.heap0, compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hch_ge ⊢
    omega
  have hlen_le_ho : ctx.lenArr + ctx.eCap * W.L_in ≤ handlesOut := by
    have := ctx.hlen_le
    dsimp [handlesOut, compHandlesBase, compStaticSize, compHdrSize]; omega
  obtain ⟨bodyWin, hWin_get, endHeap, stWin, cWin, xWinC, hWinC, hWin_run, hend_ge, hend_le,
    hWin_zf, hWin_fr, hWin_j, hWin_disj, hWin_cost⟩ :=
    W.winInit_runs st13.pos ctx.hpWin ctx.hk ctx.hLw ctx.heCap (ctx.hWinPre C hC_ef)
      (compGraph_isValid ctx.hG₀ hC_mem) (compGraph_nonempty hC_mem) hmC_pos
      (compGraph_connected ctx.hG₀ hC_mem) hDg_at hLen_st13
      le_rfl hlen_le_wh (by clear * - hho_le hch_ge; omega)
      (Or.inl (by clear * - hho_le hch_ge; omega)) (Or.inr hlen_le_ho)
      hWinArgs hDg_zf (by dsimp only [nC, mC] at hcur_next_lt; clear * - hcur_next_lt; omega)
  let st14 : State := { mem := stWin.mem, regs := Function.update st13.regs 32 endHeap, pos := stWin.pos }
  let st15 : State := { st14 with regs := Function.update st14.regs 34 (efIdx.length + 1) }
  let st16 : State := { st15 with regs := Function.update st15.regs 33 (comps.length + 1) }
  have hcallWin : Runs w p ω
      (.call 32 (ctx.bWin + W.initOff) [.reg 32, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 44, .reg 45])
      st13 .normal st14 (10 + cWin + 1) := by
    refine runs_call_iff.mpr ⟨_, bodyWin, .returned endHeap, stWin, cWin, ?_, hWin_get, hWin_run,
      rfl, rfl, by simp [argsSize, Expr.size]⟩
    simp [evalArgs, Expr.eval, st13, st12,
      hr11_32, hR11.r1, hR11.r2, hR11.r3, hR11.r4, hR11.r5, hR11.r6, hR11.r7, winHeap]
  have hst15 : Runs w p ω (.assign 34 (.bin .add (.reg 34) (.const 1))) st14 .normal st15 4 :=
    runs_assign_iff.mpr ⟨efIdx.length + 1,
      by simp [st14, st13, st12, Expr.eval, BinOp.eval, hr11_34, hw1,
        show efIdx.length + 1 < 2 ^ w by dsimp [InitCtx.heap0] at hsp_lt; omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hst16 : Runs w p ω (.assign 33 (.bin .add (.reg 33) (.const 1))) st15 .normal st16 4 :=
    runs_assign_iff.mpr ⟨comps.length + 1,
      by simp [st15, st14, st13, st12, Expr.eval, BinOp.eval, hr11_33, hw1,
        show comps.length + 1 < 2 ^ w by dsimp [compStaticSize, compHdrSize] at hstat_lt; omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp2_run : Runs w p ω (compInitEfPart2 (ctx.bWin + W.initOff)) st11 .normal st16 (cWin + 33) :=
    runs_seq_iff.mpr (Or.inr ⟨st12, 6, cWin + 26, hst12,
      runs_seq_iff.mpr (Or.inr ⟨st13, 4, cWin + 21, hst13,
        runs_seq_iff.mpr (Or.inr ⟨st14, 10 + cWin + 1, 9, hcallWin,
          runs_seq_iff.mpr (Or.inr ⟨st15, 4, 4, hst15, hst16, by omega⟩), by omega⟩),
        by omega⟩), by omega⟩)
  have hef_blk := runs_compInitEf_split hp1_run hp2_run
  have hInv' := initMemInv_step_edgeful ctx hC_mem hC_not hmC_pos hc_lt hInv
    hBfs_m0 hBfs_vis hBfs_vc hBfs_vc_fr hBfs_eC hBfs_eC_fr hBfs_fr hend_ge hend_le hWin_zf hho_le
    (fun a ha hho => (hWin_fr a (by omega) hho).trans (hDg_m10 a ha))
    hWin_j hWin_disj
  have hR16 : InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
      ctx.vCap0 G₀.n G₀.m st16.regs :=
    ((((hR11.update_mut (by omega)).update_mut (by omega)).update_mut (by omega)).update_mut
      (by omega)).update_mut (by omega)
  exact ⟨st16, endHeap, _, _, c1 + (cWin + 33) + 1, hef_blk, hR16,
    by simp [st16, st15, st14], by simp [st16], by simp [st16, st15],
    by simp [st16, st15, st14, st13, st12, hr11_35], hInv',
    by dsimp only [nC, mC, C] at hc1_le hWin_cost ⊢; clear * - hc1_le hWin_cost; omega⟩

end

end MinCostFlow.SparseCore.Program
