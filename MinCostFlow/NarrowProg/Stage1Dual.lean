module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.Layouts
public import WordRAM.Module
public import WordRAM.Std.Array
public import MinCostFlow.Narrow.CostDefs
public import MinCostFlow.Narrow.Stage1Trace
public import MinCostFlow.NarrowProg.Stage1Defs
public import MinCostFlow.NarrowProg.Stage1DualWrite
public import MinCostFlow.NarrowProg.Stage1DualQ
public import MinCostFlow.NarrowProg.Stage1DualRouting
import WordRAM.Sep.Tactic
import WordRAM.Syntax

/-!
# Dual extraction procedure (`stage1DualExtract`, Part 4a)

Given a residual circulation `J` (`n' = J.n`, `mJ = J.m`, endpoints `(pResTail, pResHead)`,
costs `(pResCSign, pResCMag)`) and presence arrays `(pRho, pGCap)`, `stage1DualExtract`:
1. Writes `S.solverWords` at `pS = h` via `stage1WriteS`, where
   `S = (flagResidualGraph J fwd rev).shortestRoutingGraph`;
2. Writes `Qpos.solverWords` at `pQ = pR + S.m` via `stage1WriteQ`, where
   `Qpos = extractDualFromFlagsCall J fwd rev`;
3. Calls the bounded solver `solverIdx(pQ, hSol)` to obtain an optimal integral flow `d_dual`
   on `Qpos`;
4. Builds the routing flow `routing : Fin S.m → ℤ` at `pR = pS + S.solverWords.length` via
   `stage1BuildRouting`;
5. Calls `propagateLabels` (`propIdx`) on `(pS, pR, J.n, max h2 (hSol + Qpos.m))`;
6. Stores `pDy = h2' + 2` at `pDualOut` and returns `h3`, exposing
   `Assn.list pDy ((List.ofFn dy).flatMap encodeSignedPair)` with
   `dy = extractDualFromFlagsOfAnswer J fwd rev d_dual`.
-/

@[expose] public section

open WordRAM WordRAM.Sep WordRAM.Std MinCostFlow.Scaling MinCostFlow.Scaling.Machine
  MinCostFlow.Narrow MinCostFlow.NarrowProg

namespace MinCostFlow.NarrowProg.Stage1

attribute [local sep_len] List.length_ofFn List.length_replicate

/-- Extract the round's integral dual potential table `dy`, storing its pointer `pDy` at
`pDualOut` and returning the updated heap pointer `h3`. -/
wram_def stage1DualExtract (writeSIdx writeQIdx solverIdx buildRIdx propIdx : ℕ)
    (n', mJ, pResTail, pResHead, pResCSign, pResCMag, pRho, pGCap, pDualOut, h) {
  sm := 2 * mJ + n'
  pS := h
  pR := pS + 2 + 5 * sm
  pQ := pR + sm
  hSol := pQ + 2 + 10 * sm
  r := writeSIdx(n', mJ, pResTail, pResHead, pResCSign, pResCMag, pRho, pGCap, pS)
  r := writeQIdx(n', mJ, pResTail, pResHead, pResCSign, pResCMag, pRho, pGCap, pQ)
  h2 := solverIdx(pQ, hSol)
  r := buildRIdx(n', mJ, pRho, pGCap, hSol, pR)
  h2' := hSol + 2 * sm
  if h2' < h2 {
    h2' := h2
  }
  h3 := propIdx(pS, pR, n', h2')
  mem[pDualOut] := h2' + 2
  return h3
}

/-- Space budget of `stage1DualExtract` for a residual instance `J`. Matches `stage1DualSpace C S`
when `J.n = C.n` and `J.m = 2 * C.m`. -/
def stage1DualExtractSpace (J : Circulation) (S : ℕ → ℕ → ℕ) : ℕ :=
  let Sm := 2 * J.m + J.n
  let Qm := 2 * Sm
  (2 + 5 * Sm) + Sm + (2 + 5 * Qm) + Qm + S (J.n + 2) Qm + (5 + 5 * (J.n + 1) + 6 * Sm)

/-- Ghost input bundle for `stage1DualExtractSpec`. -/
structure Stage1DualIn where
  J : Circulation
  Cmax : ℕ
  rho : List ℕ
  gCap : List ℕ
  outOld : ℕ

/-- Specification of `stage1DualExtract`. -/
def stage1DualExtractSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Stage1DualIn where
  pre := fun g args =>
    ⨆ (pT : ℕ) (pH : ℕ) (pCS : ℕ) (pCM : ℕ) (pRho : ℕ) (pGCap : ℕ) (pDualOut : ℕ) (h : ℕ),
      ⌜args = [g.J.n, g.J.m, pT, pH, pCS, pCM, pRho, pGCap, pDualOut, h] ∧
        0 < g.J.n ∧ g.rho.length = g.J.m ∧ g.gCap.length = g.J.m ∧
        g.J.CostsBounded g.Cmax ∧
        g.Cmax ≤ (4 * g.J.m + 2 * g.J.n) ^ 10 ∧
        (2 * g.J.m + g.J.n + 1) * g.Cmax < 2 ^ w ∧
        8 < 2 ^ w ∧
        h + stage1DualExtractSpace g.J S < 2 ^ w⌝ *
      Assn.list pT (List.ofFn fun a : Fin g.J.m => (g.J.tail a).val) *
      Assn.list pH (List.ofFn fun a : Fin g.J.m => (g.J.head a).val) *
      Assn.list pCS (List.ofFn fun a : Fin g.J.m => if g.J.cost a < 0 then 1 else 0) *
      Assn.list pCM (List.ofFn fun a : Fin g.J.m => (g.J.cost a).natAbs) *
      Assn.list pRho g.rho *
      Assn.list pGCap g.gCap *
      Assn.list pDualOut [g.outOld] *
      Assn.free h (2 ^ w - h)
  post := fun g args h3 =>
    ⨆ (pT : ℕ) (pH : ℕ) (pCS : ℕ) (pCM : ℕ) (pRho : ℕ) (pGCap : ℕ) (pDualOut : ℕ) (h : ℕ)
      (pDy : ℕ)
      (d_dual : Fin (extractDualFromFlagsCall g.J (dualFwdFlags g.J g.rho) (dualRevFlags g.J g.gCap)).m → ℤ),
      let fwd := dualFwdFlags g.J g.rho
      let rev := dualRevFlags g.J g.gCap
      let Qpos := extractDualFromFlagsCall g.J fwd rev
      let dy := extractDualFromFlagsOfAnswer g.J fwd rev d_dual
      ⌜args = [g.J.n, g.J.m, pT, pH, pCS, pCM, pRho, pGCap, pDualOut, h] ∧
        h ≤ h3 ∧ h3 ≤ h + stage1DualExtractSpace g.J S ∧
        Qpos.Optimal (fun a => (d_dual a : ℝ))⌝ *
      Assn.list pT (List.ofFn fun a : Fin g.J.m => (g.J.tail a).val) *
      Assn.list pH (List.ofFn fun a : Fin g.J.m => (g.J.head a).val) *
      Assn.list pCS (List.ofFn fun a : Fin g.J.m => if g.J.cost a < 0 then 1 else 0) *
      Assn.list pCM (List.ofFn fun a : Fin g.J.m => (g.J.cost a).natAbs) *
      Assn.list pRho g.rho *
      Assn.list pGCap g.gCap *
      Assn.list pDualOut [pDy] *
      Assn.list pDy ((List.ofFn dy).flatMap encodeSignedPair) *
      Assn.free h3 (2 ^ w - h3)

private lemma fin_addCases_abs_le {m n : ℕ} {f : Fin m → ℤ} {g : Fin n → ℤ} {B : ℕ}
    (hf : ∀ i, (f i).natAbs ≤ B) (hg : ∀ j, (g j).natAbs ≤ B) (e : Fin (m + n)) :
    (@Fin.addCases m n (fun _ => ℤ) f g e).natAbs ≤ B := by
  by_cases h : e.val < m
  · have he : e = Fin.castAdd n ⟨e.val, h⟩ := by ext; rfl
    rw [he, Fin.addCases_left]; exact hf _
  · have h2 : e.val - m < n := by omega
    have he : e = Fin.natAdd m ⟨e.val - m, h2⟩ := by ext; simp [Fin.natAdd]; omega
    rw [he, Fin.addCases_right]; exact hg _

private theorem S_costsBounded (J : Circulation) (fwd rev : Fin J.m → Bool) (Cmax : ℕ)
    (hC : J.CostsBounded Cmax) :
    ∀ e, ((flagResidualGraph J fwd rev).shortestRoutingGraph.cost e).natAbs ≤ Cmax := by
  have hR : ∀ e, ((flagResidualGraph J fwd rev).cost e).natAbs ≤ Cmax :=
    fin_addCases_abs_le hC (fun i => by rw [Int.natAbs_neg]; exact hC i)
  intro e
  unfold Circulation.shortestRoutingGraph
  dsimp only
  exact fin_addCases_abs_le hR (fun _ => by simp) e

private theorem Qpos_costsBounded (J : Circulation) (fwd rev : Fin J.m → Bool) (Cmax : ℕ)
    (hC : J.CostsBounded Cmax) :
    (extractDualFromFlagsCall J fwd rev).CostsBounded Cmax := by
  apply Circulation.positiveInstance_costsBounded
  have hS := S_costsBounded J fwd rev Cmax hC
  exact fin_addCases_abs_le hS (fun e => by rw [Int.natAbs_neg]; exact hS e)

private theorem Qpos_caps_bounded (J : Circulation) (hn : 0 < J.n) (fwd rev : Fin J.m → Bool) :
    let Qpos := extractDualFromFlagsCall J fwd rev
    ∀ e, 1 ≤ Qpos.capacity e ∧ Qpos.capacity e ≤ Qpos.m ^ 40 := by
  intro Qpos e
  have hpos : 0 < Qpos.capacity e :=
    Circulation.positiveInstance_capacity_pos
      ((flagResidualGraph J fwd rev).shortestRoutingGraph.residual
        (flagResidualGraph J fwd rev).shortestRoutingStart) e
  refine ⟨by omega, ?_⟩
  have hle_n1 : Qpos.capacity e ≤ J.n + 1 := by
    dsimp only [Qpos, extractDualFromFlagsCall, Circulation.positiveInstance]
    split
    · omega
    · refine Fin.addCases (fun a => ?_) (fun a => ?_) e
      · refine Fin.addCases (fun e1 => ?_) (fun v => ?_) a
        · simp only [Circulation.shortestRoutingGraph,
            Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_left, sub_zero, Int.toNat_natCast]
          split <;> omega
        · simp only [Circulation.shortestRoutingGraph,
            Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_left, Fin.addCases_right]
          omega
      · refine Fin.addCases (fun e1 => ?_) (fun v => ?_) a
        · simp only [Circulation.shortestRoutingGraph,
            Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_right, Fin.addCases_left]
          omega
        · simp only [Circulation.shortestRoutingGraph,
            Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_right]
          omega
  have hn1_le_m : J.n + 1 ≤ Qpos.m := by
    change J.n + 1 ≤ ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n); omega
  have hm_pos : 1 ≤ Qpos.m := by omega
  have hm_le_pow : Qpos.m ≤ Qpos.m ^ 40 := by
    simpa using Nat.le_self_pow (by decide : 40 ≠ 0) Qpos.m
  omega

private theorem Qpos_solverWords_lt {w : ℕ} (J : Circulation) (hn : 0 < J.n)
    (fwd rev : Fin J.m → Bool) (Cmax : ℕ) (hC : J.CostsBounded Cmax)
    (hQm_lt : 4 * J.m + 2 * J.n < 2 ^ w) (hn2_lt : J.n + 2 < 2 ^ w) (hC_lt : Cmax < 2 ^ w) :
    ∀ x ∈ (extractDualFromFlagsCall J fwd rev).solverWords, x < 2 ^ w := by
  set Qpos := extractDualFromFlagsCall J fwd rev
  have hQc : Qpos.CostsBounded Cmax := Qpos_costsBounded J fwd rev Cmax hC
  have hQcap : ∀ e, Qpos.capacity e ≤ J.n + 1 := by
    intro e
    dsimp only [Qpos, extractDualFromFlagsCall, Circulation.positiveInstance]
    split
    · omega
    · refine Fin.addCases (fun a => ?_) (fun a => ?_) e
      · refine Fin.addCases (fun e1 => ?_) (fun v => ?_) a
        · simp only [Circulation.shortestRoutingGraph,
            Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_left, sub_zero, Int.toNat_natCast]
          split <;> omega
        · simp only [Circulation.shortestRoutingGraph,
            Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_left, Fin.addCases_right]
          omega
      · refine Fin.addCases (fun e1 => ?_) (fun v => ?_) a
        · simp only [Circulation.shortestRoutingGraph,
            Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_right, Fin.addCases_left]
          omega
        · simp only [Circulation.shortestRoutingGraph,
            Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_right]
          omega
  intro x hx
  unfold Circulation.solverWords at hx
  simp only [List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and] at hx
  rcases hx with rfl | rfl | ⟨e, he⟩
  · exact hn2_lt
  · change ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n) < 2 ^ w; omega
  · unfold Circulation.solverEdgeWords at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · have := (Qpos.tail e).isLt; change (Qpos.tail e).val < J.n + 2 at this; omega
    · have := (Qpos.head e).isLt; change (Qpos.head e).val < J.n + 2 at this; omega
    · have := hQcap e; omega
    · split_ifs <;> omega
    · have := hQc e; omega

private theorem dual_labels_split (n : ℕ) (labs : Fin (n + 1) → ℤ) :
    ((List.ofFn labs).flatMap encodeSignedPair) =
      ((List.ofFn fun v : Fin n => labs v.castSucc).flatMap encodeSignedPair) ++
        encodeSignedPair (labs (Fin.last n)) := by
  rw [List.ofFn_succ', List.concat_eq_append, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

private theorem dual_free_split {w h Sm Qm : ℕ} (hfit : h + (2 + 5 * Sm) + Sm + (2 + 5 * Qm) ≤ 2 ^ w) :
    Assn.free h (2 ^ w - h) =
      Assn.free h (2 + 5 * Sm) *
      Assn.free (h + 2 + 5 * Sm) Sm *
      Assn.free (h + 2 + 5 * Sm + Sm) (2 + 5 * Qm) *
      Assn.free (h + 2 + 5 * Sm + Sm + 2 + 5 * Qm) (2 ^ w - (h + 2 + 5 * Sm + Sm + 2 + 5 * Qm)) := by
  have hs1 : Assn.free h (2 ^ w - h) =
      Assn.free h (2 + 5 * Sm) * Assn.free (h + 2 + 5 * Sm) (2 ^ w - (h + 2 + 5 * Sm)) := by
    rw [show 2 ^ w - h = (2 + 5 * Sm) + (2 ^ w - (h + 2 + 5 * Sm)) by omega,
      Assn.free_add', show h + (2 + 5 * Sm) = h + 2 + 5 * Sm by omega]
  have hs2 : Assn.free (h + 2 + 5 * Sm) (2 ^ w - (h + 2 + 5 * Sm)) =
      Assn.free (h + 2 + 5 * Sm) Sm * Assn.free (h + 2 + 5 * Sm + Sm) (2 ^ w - (h + 2 + 5 * Sm + Sm)) := by
    rw [show 2 ^ w - (h + 2 + 5 * Sm) = Sm + (2 ^ w - (h + 2 + 5 * Sm + Sm)) by omega,
      Assn.free_add']
  have hs3 : Assn.free (h + 2 + 5 * Sm + Sm) (2 ^ w - (h + 2 + 5 * Sm + Sm)) =
      Assn.free (h + 2 + 5 * Sm + Sm) (2 + 5 * Qm) *
      Assn.free (h + 2 + 5 * Sm + Sm + 2 + 5 * Qm) (2 ^ w - (h + 2 + 5 * Sm + Sm + 2 + 5 * Qm)) := by
    rw [show 2 ^ w - (h + 2 + 5 * Sm + Sm) = (2 + 5 * Qm) + (2 ^ w - (h + 2 + 5 * Sm + Sm + 2 + 5 * Qm)) by omega,
      Assn.free_add', show h + 2 + 5 * Sm + Sm + (2 + 5 * Qm) = h + 2 + 5 * Sm + Sm + 2 + 5 * Qm by omega]
  rw [hs1, hs2, hs3]
  simp only [mul_assoc]

private def dualRO (J : Circulation) (rho gCap : List ℕ)
    (pT pH pCS pCM pRho pGCap : ℕ) : Assn :=
  Assn.list pT (List.ofFn fun a : Fin J.m => (J.tail a).val) *
  Assn.list pH (List.ofFn fun a : Fin J.m => (J.head a).val) *
  Assn.list pCS (List.ofFn fun a : Fin J.m => if J.cost a < 0 then 1 else 0) *
  Assn.list pCM (List.ofFn fun a : Fin J.m => (J.cost a).natAbs) *
  Assn.list pRho rho *
  Assn.list pGCap gCap

private theorem dualRO_eq (J : Circulation) (rho gCap : List ℕ) (pT pH pCS pCM pRho pGCap : ℕ) :
    Assn.list pT (List.ofFn fun a : Fin J.m => (J.tail a).val) *
    Assn.list pH (List.ofFn fun a : Fin J.m => (J.head a).val) *
    Assn.list pCS (List.ofFn fun a : Fin J.m => if J.cost a < 0 then 1 else 0) *
    Assn.list pCM (List.ofFn fun a : Fin J.m => (J.cost a).natAbs) *
    Assn.list pRho rho *
    Assn.list pGCap gCap =
    dualRO J rho gCap pT pH pCS pCM pRho pGCap := rfl

private theorem dual_prop_finish {w : ℕ} {p : Program} {propIdx : ℕ}
    {T_sol S_sol : ℕ → ℕ → ℕ}
    (hprop : Meets w p propIdx ((stage1PropLabelsSpec w).withCost fun x _ => 3000 * x.J.m + 800))
    {J S : Circulation} {Cmax : ℕ} {rho gCap : List ℕ} {outOld : ℕ}
    {pT pH pCS pCM pRho pGCap pDualOut h h2 base : ℕ}
    {rout : Fin S.m → ℤ} {rootS : Fin S.n} {mAll : ℕ → ℕ}
    {d_dual : Fin (extractDualFromFlagsCall J (dualFwdFlags J rho) (dualRevFlags J gCap)).m → ℤ}
    {c : ℤ}
    (hSn : S.n = J.n + 1) (hSm : S.m = 2 * J.m + J.n)
    (hroot : rootS.val = J.n)
    (hrout : ∀ e, 0 ≤ rout e ∧ (rout e).toNat < 2 ^ w)
    (hScost : ∀ e, (S.cost e).natAbs ≤ Cmax)
    (hCfit : (S.m + 1) * Cmax < 2 ^ w)
    (hw8 : 8 < 2 ^ w)
    (hfp_le : h + S.solverWords.length + S.m ≤ base)
    (hbase_fit : base + 5 + 5 * S.n + 6 * S.m < 2 ^ w)
    (hh_le : h ≤ base)
    (hsp_end : base + 3 + 5 * S.n + 6 * S.m ≤ h + stage1DualExtractSpace J S_sol)
    (hopt : (extractDualFromFlagsCall J (dualFwdFlags J rho) (dualRevFlags J gCap)).Optimal
      (fun a => (d_dual a : ℝ)))
    (hc : (3000 * S.m + 800 : ℤ) + 20 ≤ c)
    (hlab_tail : ∃ tailL : List ℕ,
      Assn.list (base + 2) ((List.ofFn (S.propagateLabels rout rootS).1.labels).flatMap encodeSignedPair) =
      Assn.list (base + 2) ((List.ofFn (extractDualFromFlagsOfAnswer J
        (dualFwdFlags J rho) (dualRevFlags J gCap) d_dual)).flatMap encodeSignedPair) *
      Assn.list (base + 2 + ((List.ofFn (extractDualFromFlagsOfAnswer J
        (dualFwdFlags J rho) (dualRevFlags J gCap) d_dual)).flatMap encodeSignedPair).length) tailL) :
    SE w p stage1DualExtract.vars
      [J.n, J.m, pT, pH, pCS, pCM, pRho, pGCap, pDualOut, h,
       2 * J.m + J.n, h, h + S.solverWords.length,
       h + S.solverWords.length + (2 * J.m + J.n),
       h + S.solverWords.length + (2 * J.m + J.n) + 2 + 10 * (2 * J.m + J.n),
       0, h2, base, 0]
      c
      [Assn.list pDualOut [outOld],
       Assn.list h S.solverWords,
       dualRO J rho gCap pT pH pCS pCM pRho pGCap,
       Assn.cells (Set.Ico (h + S.solverWords.length + S.m) base) mAll,
       Assn.free base (2 ^ w - base),
       Assn.list (h + S.solverWords.length) (List.ofFn fun e => (rout e).toNat)]
      (Stmt.call 18 propIdx [Expr.reg 11, Expr.reg 12, Expr.reg 0, Expr.reg 17] ;;
       Stmt.store (Expr.reg 8) (Expr.bin BinOp.add (Expr.reg 17) (Expr.const 2)) ;;
       Stmt.ret (Expr.reg 18))
      (fun o _ => ((stage1DualExtractSpec w S_sol).withCost fun g _ =>
        T_sol (g.J.n + 2) (4 * g.J.m + 2 * g.J.n) + 6800 * g.J.m + 3400 * g.J.n + 1400).post
        ⟨J, Cmax, rho, gCap, outOld⟩ [J.n, J.m, pT, pH, pCS, pCM, pRho, pGCap, pDualOut, h] o.value) := by
  sep_step from ⟨S, rout, rootS, Cmax, mAll⟩
  obtain ⟨tailL, hlab_split⟩ := hlab_tail
  sep_apply hlab_split
  sep_apply (dualRO_eq J rho gCap pT pH pCS pCM pRho pGCap).symm
  sep_step
  sep_run

theorem stage1DualExtract_meets {w : ℕ} {p : Program}
    {f writeSIdx writeQIdx solverIdx buildRIdx propIdx : ℕ}
    {T_sol S_sol : ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage1DualExtract writeSIdx writeQIdx solverIdx buildRIdx propIdx))
    (hws : Meets w p writeSIdx ((stage1WriteSSpec w).withCost fun g _ => 210 * g.J.m + 70 * g.J.n + 100))
    (hwq : Meets w p writeQIdx ((stage1WriteQSpec w).withCost fun g _ => 380 * g.J.m + 150 * g.J.n + 150))
    (hsol : Meets w p solverIdx ((stage1SolverSpec w S_sol).withCost fun K _ => T_sol K.n K.m))
    (hbr : Meets w p buildRIdx ((stage1BuildRoutingSpec w).withCost fun g _ => 110 * g.J.m + 60 * g.J.n + 80))
    (hprop : Meets w p propIdx ((stage1PropLabelsSpec w).withCost fun x _ => 3000 * x.J.m + 800)) :
    Meets w p f ((stage1DualExtractSpec w S_sol).withCost fun g _ =>
      T_sol (g.J.n + 2) (4 * g.J.m + 2 * g.J.n) + 6800 * g.J.m + 3400 * g.J.n + 1400) := by
  sep_enter g with hn_pos hrho hgcap hCbnd hCle hCfit hw8 hsp
  obtain ⟨J, Cmax, rho, gCap, outOld⟩ := g
  dsimp only at hn_pos hrho hgcap hCbnd hCle hCfit hw8 hsp ⊢
  set fwd := dualFwdFlags J rho
  set rev := dualRevFlags J gCap
  set S := (flagResidualGraph J fwd rev).shortestRoutingGraph
  set Qpos := extractDualFromFlagsCall J fwd rev
  have hSn : S.n = J.n + 1 := rfl
  have hSm : S.m = 2 * J.m + J.n := by change (J.m + J.m) + J.n = _; omega
  have hQn : Qpos.n = J.n + 2 := rfl
  have hQm : Qpos.m = 2 * S.m := by change ((J.m + J.m) + J.n) + ((J.m + J.m) + J.n) = _; omega
  have hQm' : Qpos.m = 4 * J.m + 2 * J.n := by omega
  have hSlen : S.solverWords.length = 2 + 5 * S.m := S.solverWords_length
  have hQlen : Qpos.solverWords.length = 2 + 5 * Qpos.m := Qpos.solverWords_length
  have hsp' : h + (2 + 5 * S.m) + S.m + (2 + 5 * Qpos.m) + Qpos.m +
      S_sol (J.n + 2) Qpos.m + (5 + 5 * (J.n + 1) + 6 * S.m) < 2 ^ w := by
    unfold stage1DualExtractSpace at hsp; dsimp only at hsp
    rw [show Qpos.m = 2 * (2 * J.m + J.n) by omega]; omega
  have hC_lt : Cmax < 2 ^ w := by
    have : 1 * Cmax ≤ (2 * J.m + J.n + 1) * Cmax := Nat.mul_le_mul_right Cmax (by omega)
    omega
  sep_apply dual_free_split (w := w) (h := h) (Sm := S.m) (Qm := Qpos.m) (by omega)
  iterate 5 sep_step
  try subst hsm
  try subst hpR
  try subst hpQ
  try subst hhSol
  have hSlen_eq : Assn.free h (2 + 5 * S.m) = Assn.free h S.solverWords.length := by rw [hSlen]
  have hQlen_eq : Assn.free (h + 2 + 5 * S.m + S.m) (2 + 5 * Qpos.m) =
      Assn.free (h + 2 + 5 * S.m + S.m) Qpos.solverWords.length := by rw [hQlen]
  sep_apply hSlen_eq
  sep_apply hQlen_eq
  have hS_fit : h + (flagResidualGraph J (dualFwdFlags J rho) (dualRevFlags J gCap)).shortestRoutingGraph.solverWords.length < 2 ^ w := by
    change h + S.solverWords.length < 2 ^ w; omega
  have hQ_fit : h + 2 + 5 * (2 * J.m + J.n) + (2 * J.m + J.n) +
      (extractDualFromFlagsCall J (dualFwdFlags J rho) (dualRevFlags J gCap)).solverWords.length < 2 ^ w := by
    change h + 2 + 5 * (2 * J.m + J.n) + (2 * J.m + J.n) + Qpos.solverWords.length < 2 ^ w; omega
  have hSol_fit : h + 2 + 5 * (2 * J.m + J.n) + (2 * J.m + J.n) +
      Qpos.solverWords.length + Qpos.m + S_sol Qpos.n Qpos.m < 2 ^ w := by
    rw [hQn]; omega
  sep_step from ⟨J, rho, gCap⟩
  sep_step from ⟨J, rho, gCap⟩
  have hQ_words := Qpos_solverWords_lt J hn_pos fwd rev Cmax hCbnd (by omega) (by omega) hC_lt
  have hQ_costs : Qpos.CostsBounded (Qpos.m ^ 10) := fun e =>
    le_trans (Qpos_costsBounded J fwd rev Cmax hCbnd e) (by rw [hQm']; exact hCle)
  have hQ_caps := Qpos_caps_bounded J hn_pos fwd rev
  sep_step from Qpos
  -- From `hsol`, `flow : List ℕ` has `flow.length = Qpos.m` and is optimal on `Qpos`.
  have hflow_len : flow.length = Qpos.m := by assumption
  have hflow_opt : Qpos.Optimal (fun e => ((flow.getD e.val 0 : ℕ) : ℝ)) := by assumption
  have hflow_vals : ∀ e : Fin Qpos.m, flow.getD e.val 0 ≤ Qpos.capacity e := by
    intro e
    have hfeas := hflow_opt.1.2 e
    have hle : ((flow.getD e.val 0 : ℕ) : ℝ) ≤ (Qpos.capacity e : ℝ) := hfeas.2
    exact_mod_cast hle
  have hflow_lt_w : ∀ x ∈ flow, x < 2 ^ w := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hiQ : i < Qpos.m := by omega
    have hle := hflow_vals ⟨i, hiQ⟩
    rw [List.getD_eq_getElem _ _ hi] at hle
    have hcap_le : Qpos.capacity ⟨i, hiQ⟩ ≤ J.n + 1 := by
      dsimp only [Qpos, extractDualFromFlagsCall, Circulation.positiveInstance]
      split
      · omega
      · refine Fin.addCases (fun a => ?_) (fun a => ?_) ⟨i, hiQ⟩
        · refine Fin.addCases (fun e1 => ?_) (fun v => ?_) a
          · simp only [Circulation.shortestRoutingGraph,
              Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_left, sub_zero, Int.toNat_natCast]
            split <;> omega
          · simp only [Circulation.shortestRoutingGraph,
              Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_left, Fin.addCases_right]
            omega
        · refine Fin.addCases (fun e1 => ?_) (fun v => ?_) a
          · simp only [Circulation.shortestRoutingGraph,
              Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_right, Fin.addCases_left]
            omega
          · simp only [Circulation.shortestRoutingGraph,
              Circulation.shortestRoutingStart, flagResidualGraph, Fin.addCases_right]
            omega
    omega
  have hdbnd : ∀ v : Fin J.n,
      flow.getD (S.m + 2 * J.m + v.val) 0 ≤ 1 + flow.getD (2 * J.m + v.val) 0 ∧
      1 + flow.getD (2 * J.m + v.val) 0 < 2 ^ w := by
    intro v
    have hrev_idx : S.m + 2 * J.m + v.val < Qpos.m := by omega
    have hfwd_idx : 2 * J.m + v.val < Qpos.m := by omega
    have hrev_le := hflow_vals ⟨S.m + 2 * J.m + v.val, hrev_idx⟩
    have hfwd_le := hflow_vals ⟨2 * J.m + v.val, hfwd_idx⟩
    dsimp only at hrev_le hfwd_le
    have hcap_rev : Qpos.capacity ⟨S.m + 2 * J.m + v.val, hrev_idx⟩ = 1 := by
      dsimp only [Qpos, extractDualFromFlagsCall, Circulation.positiveInstance,
        Circulation.residual, Circulation.shortestRoutingGraph, Circulation.shortestRoutingStart,
        flagResidualGraph]
      have h1 : (⟨S.m + 2 * J.m + v.val, hrev_idx⟩ : Fin (((J.m + J.m) + J.n) + ((J.m + J.m) + J.n))) =
          Fin.natAdd ((J.m + J.m) + J.n) (Fin.natAdd (J.m + J.m) v) := by
        ext; simp [Fin.natAdd]; omega
      rw [h1]
      simp only [Fin.addCases_right, Int.toNat_one, Nat.one_ne_zero, ↓reduceIte]
    have hcap_fwd : Qpos.capacity ⟨2 * J.m + v.val, hfwd_idx⟩ = J.n := by
      dsimp only [Qpos, extractDualFromFlagsCall, Circulation.positiveInstance,
        Circulation.residual, Circulation.shortestRoutingGraph, Circulation.shortestRoutingStart,
        flagResidualGraph]
      have h1 : (⟨2 * J.m + v.val, hfwd_idx⟩ : Fin (((J.m + J.m) + J.n) + ((J.m + J.m) + J.n))) =
          Fin.castAdd ((J.m + J.m) + J.n) (Fin.natAdd (J.m + J.m) v) := by
        ext; simp [Fin.natAdd]; omega
      rw [h1]
      simp only [Fin.addCases_left, Fin.addCases_right]
      have hne : J.n ≠ 0 := by omega
      simp [hne]
    rw [hcap_rev] at hrev_le
    rw [hcap_fwd] at hfwd_le
    omega
  sep_step from ⟨J, rho, gCap, flow⟩
  -- Fold untouched read-only inputs into `dualRO`
  sep_apply dualRO_eq J rho gCap pT pH pCS pCM pRho pGCap
  -- Merge `[pQ, max h2 (hSol + Qm))` into a single `Assn.cells (Set.Ico (pR + S.m) base) mPad`
  set hSol_addr := h + 2 + 5 * S.m + S.m + 2 + 10 * S.m
  set base := max h2 (hSol_addr + Qpos.m)
  have hmerge1 : Assn.list hSol_addr flow *
      Assn.cells (Set.Ico (hSol_addr + Qpos.m) base) m₁ =
      Assn.cells (Set.Ico hSol_addr base)
        (fun x => if x < hSol_addr + Qpos.m then flow.getD (x - hSol_addr) 0 else m₁ x) := by
    have hc := list_mul_cells_eq_cells (a := hSol_addr) (b := base) (l := flow) (m := m₁) (by omega)
    simpa only [hflow_len] using hc
  set mMid := fun x => if x < hSol_addr + Qpos.m then flow.getD (x - hSol_addr) 0 else m₁ x
  have hmerge2 : Assn.list (h + 2 + 5 * S.m + S.m) Qpos.solverWords *
      Assn.cells (Set.Ico hSol_addr base) mMid =
      Assn.cells (Set.Ico (h + 2 + 5 * S.m + S.m) base)
        (fun x => if x < hSol_addr then Qpos.solverWords.getD (x - (h + 2 + 5 * S.m + S.m)) 0 else mMid x) := by
    have hc := list_mul_cells_eq_cells (a := h + 2 + 5 * S.m + S.m) (b := base)
      (l := Qpos.solverWords) (m := mMid) (by omega)
    have hlenQ : h + 2 + 5 * S.m + S.m + Qpos.solverWords.length = hSol_addr := by omega
    simpa only [hlenQ] using hc
  sep_apply hmerge1
  sep_apply hmerge2
  set mAll := fun x => if x < hSol_addr then Qpos.solverWords.getD (x - (h + 2 + 5 * S.m + S.m)) 0 else mMid x
  have hfp_eq : h + 2 + 5 * S.m = h + S.solverWords.length := by rw [hSlen]; omega
  have hfp_eq' : h + 2 + 5 * (2 * J.m + J.n) = h + S.solverWords.length := by rw [← hSm]; exact hfp_eq
  have hfp_list : Assn.list (h + 2 + 5 * S.m)
      (List.ofFn fun e => (dualRoutingOfAnswer J fwd rev (fun a => (flow.getD a.val 0 : ℤ)) e).toNat) =
      Assn.list (h + S.solverWords.length)
      (List.ofFn fun e => (dualRoutingOfAnswer J fwd rev (fun a => (flow.getD a.val 0 : ℤ)) e).toNat) := by
    rw [hfp_eq]
  sep_apply hfp_list
  have hScost : ∀ e : Fin S.m, (S.cost e).natAbs ≤ Cmax := S_costsBounded J fwd rev Cmax hCbnd
  set rout : Fin S.m → ℤ := dualRoutingOfAnswer J fwd rev (fun a => (flow.getD a.val 0 : ℤ))
  have hrout_ok : ∀ e : Fin S.m, 0 ≤ rout e ∧ (rout e).toNat < 2 ^ w := by assumption
  set dy := extractDualFromFlagsOfAnswer J fwd rev (fun a => (flow.getD a.val 0 : ℤ))
  set rootS : Fin S.n := Fin.last J.n
  have hroot_val : rootS.val = J.n := rfl
  have hlab_tail : ∀ addr,
      ∃ tailL : List ℕ,
        Assn.list addr ((List.ofFn (S.propagateLabels rout rootS).1.labels).flatMap encodeSignedPair) =
        Assn.list addr ((List.ofFn dy).flatMap encodeSignedPair) *
        Assn.list (addr + ((List.ofFn dy).flatMap encodeSignedPair).length) tailL := by
    intro addr
    refine ⟨encodeSignedPair ((S.propagateLabels rout rootS).1.labels rootS), ?_⟩
    rw [dual_labels_split, Assn.list_append]; rfl
  -- Execute `h2' := hSol + 2 * sm; if h2' < h2 { h2' := h2 }`
  sep_step
  sep_step
  · -- `hSol + 2 * sm < h2`, so `base = h2`
    have hbase_eq : base = h2 := max_eq_left (by omega)
    have hcells_fp : Assn.cells (Set.Ico (h + 2 + 5 * S.m + S.m) base) mAll =
        Assn.cells (Set.Ico (h + S.solverWords.length + S.m) h2) mAll := by
      rw [hfp_eq, hbase_eq]
    have hfree_fp : Assn.free base (2 ^ w - base) = Assn.free h2 (2 ^ w - h2) := by
      rw [hbase_eq]
    sep_apply hcells_fp
    sep_apply hfree_fp
    sep_step
    rw [hfp_eq']
    have hsp_end : h2 + 3 + 5 * S.n + 6 * S.m ≤ h + stage1DualExtractSpace J S_sol := by
      unfold stage1DualExtractSpace; dsimp only
      have : Qpos.m = 2 * (2 * J.m + J.n) := by omega
      rw [hQn, this] at h_3; omega
    exact dual_prop_finish (T_sol := T_sol) (S := S) (base := h2) hprop hSn hSm hroot_val hrout_ok hScost
      (by rw [hSm]; exact hCfit) hw8 (by omega) (by rw [hQn] at h_3; omega) (by omega) hsp_end
      hflow_opt (by rw [hQn, hQm']; omega) (hlab_tail (h2 + 2))
  · -- `h2 ≤ hSol + 2 * sm`, so `base = hSol + 2 * sm`
    have hbase_eq : base = hSol_addr + Qpos.m := max_eq_right (by omega)
    have hcells_fp : Assn.cells (Set.Ico (h + 2 + 5 * S.m + S.m) base) mAll =
        Assn.cells (Set.Ico (h + S.solverWords.length + S.m) (hSol_addr + Qpos.m)) mAll := by
      rw [hfp_eq, hbase_eq]
    have hfree_fp : Assn.free base (2 ^ w - base) =
        Assn.free (hSol_addr + Qpos.m) (2 ^ w - (hSol_addr + Qpos.m)) := by
      rw [hbase_eq]
    sep_apply hcells_fp
    sep_apply hfree_fp
    sep_step
    have hh2'_eq : h2' = hSol_addr + Qpos.m := by omega
    rw [hh2'_eq, hfp_eq']
    have hsp_end : hSol_addr + Qpos.m + 3 + 5 * S.n + 6 * S.m ≤ h + stage1DualExtractSpace J S_sol := by
      unfold stage1DualExtractSpace; dsimp only
      have : Qpos.m = 2 * (2 * J.m + J.n) := by omega
      omega
    exact dual_prop_finish (T_sol := T_sol) (S := S) (base := hSol_addr + Qpos.m) hprop hSn hSm
      hroot_val hrout_ok hScost
      (by rw [hSm]; exact hCfit) hw8 (by omega) (by omega) (by omega) hsp_end
      hflow_opt (by rw [hQn, hQm']; omega) (hlab_tail (hSol_addr + Qpos.m + 2))

theorem stage1DualExtract_meetsO {w : ℕ} {p : Program}
    {f writeSIdx writeQIdx solverIdx buildRIdx propIdx : ℕ}
    {T_sol S_sol : ℕ → ℕ → ℕ}
    (hp : p.procs[f]? = some (stage1DualExtract writeSIdx writeQIdx solverIdx buildRIdx propIdx))
    (hws : Meets w p writeSIdx ((stage1WriteSSpec w).withCost fun g _ => 210 * g.J.m + 70 * g.J.n + 100))
    (hwq : Meets w p writeQIdx ((stage1WriteQSpec w).withCost fun g _ => 380 * g.J.m + 150 * g.J.n + 150))
    (hsol : Meets w p solverIdx ((stage1SolverSpec w S_sol).withCost fun K _ => T_sol K.n K.m))
    (hbr : Meets w p buildRIdx ((stage1BuildRoutingSpec w).withCost fun g _ => 110 * g.J.m + 60 * g.J.n + 80))
    (hprop : Meets w p propIdx ((stage1PropLabelsSpec w).withCost fun x _ => 3000 * x.J.m + 800)) :
    MeetsO w p f (stage1DualExtractSpec w S_sol) fun g _ =>
      T_sol (g.J.n + 2) (4 * g.J.m + 2 * g.J.n) + g.J.m + g.J.n + 1 :=
  MeetsO.of_meets (stage1DualExtract_meets hp hws hwq hsol hbr hprop) ⟨6800, fun _ => by
    dsimp only; omega⟩

/-- Polymorphic module bundling the pure-WordRAM dual-extraction helpers and `stage1DualExtract`
(parameterized by the bounded-solver and `propagateLabels` procedure indices). -/
def stage1DualMod {ι : Type}
    (dualName writeSName writeQEdgesName writeQName buildRName solverName propName : ι) :
    Module ι :=
  ⟨[(writeSName, fun _ => stage1WriteS),
    (writeQEdgesName, fun _ => stage1WriteQEdges),
    (writeQName, fun idx => stage1WriteQ (idx writeQEdgesName)),
    (buildRName, fun _ => stage1BuildRouting),
    (dualName, fun idx => stage1DualExtract (idx writeSName) (idx writeQName)
      (idx solverName) (idx buildRName) (idx propName))]⟩

theorem stage1DualMod_noRand {ι : Type}
    (dualName writeSName writeQEdgesName writeQName buildRName solverName propName : ι) :
    (stage1DualMod dualName writeSName writeQEdgesName writeQName buildRName
      solverName propName).NoRand := by
  wram_no_rand

end MinCostFlow.NarrowProg.Stage1
