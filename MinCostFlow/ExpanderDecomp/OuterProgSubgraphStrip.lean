module

public import MinCostFlow.ExpanderDecomp.OuterProgSubgraphBase
import Mathlib.Tactic.Linarith

/-!
# Verification of `stripIsolatedProc` (`OuterProgSubgraphStrip`)

Proves `stripIsolatedProc_spec` using the procedure definitions and shared mark/clear triples
from `OuterProgSubgraphBase.lean`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 6. Verification of `stripIsolatedProc` -/

private lemma hasEdge_iff_mem_edges (edges : List (ℕ × ℕ)) (v : ℕ) :
    (edges.any fun ed => decide (ed.1 = v) || decide (ed.2 = v)) = true ↔
      ∃ ed ∈ edges, ed.1 = v ∨ ed.2 = v := by
  simp [List.any_eq_true]

/-- Specification of `stripIsolatedProc`. -/
theorem stripIsolatedProc_spec {w : ℕ} {pProg : Program} {b : ℕ}
    (hp : pProg.HasAt b [stripIsolatedProc]) :
    MeetsContract w pProg b (stripIsolatedContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨n, k, vertsAddr, e, edgesAddr, locAddr, labelsAddr, nextLblAddr, outActAddr,
    verts, edges, rfl, hlenV, hndV, hv_lt, hlenE, hed_lt, hlistV, hedgesE, hloc0, hw, hdisj⟩
  rcases hw with ⟨hwV, hwE, hwLoc, hwLbl, hwNl, hwOut, hwNlK, hw16⟩
  rcases hdisj with ⟨hdLocV, hdLocE, hdLocLbl, hdLocNl, hdLocOut, hdLblV, hdLblE, hdLblNl,
    hdLblOut, hdOutV, hdOutE, hdOutNl, hdNlV, hdNlE⟩
  set nl₀ := mem nextLblAddr
  set hasEdge : ℕ → Bool := fun v => edges.any fun ed => decide (ed.1 = v) || decide (ed.2 = v)
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [stripIsolatedProc]
  -- Pass 1: mark edge endpoints in locAddr
  refine runs_seq_triple_le
    (markEdges_triple (w := w) (n := n) (e := e) (edgesAddr := edgesAddr) (locAddr := locAddr)
      (val := 1) (rE := 2) (rEdges := 3) (rLoc := 4) (rI := 8) (rU := 9) (rV := 10)
      pProg (startState _ mem pos) edges (by decide)
      (by simp [startState]) (by simp [startState]) (by simp [startState])
      hlenE hed_lt hedgesE hdLocE hwE hwLoc hw1 hw2) rfl ?_
  intro st1 ⟨h1_mark, h1_frame, h1_keep⟩
  have h1_loc_iff : ∀ u < n, st1.mem (locAddr + u) = if hasEdge u then 1 else 0 := by
    intro u hu
    by_cases h : hasEdge u = true
    · simp only [h, ↓reduceIte]
      rcases (hasEdge_iff_mem_edges edges u).mp h with ⟨ed, hed, rfl | rfl⟩
      · exact (h1_mark ed hed).1
      · exact (h1_mark ed hed).2
    · simp only [h, Bool.false_eq_true, ↓reduceIte]
      rw [h1_frame (locAddr + u) (fun ed hed => by
        constructor <;> intro heq <;> apply h <;> rw [hasEdge_iff_mem_edges]
        · exact ⟨ed, hed, Or.inl (by omega)⟩
        · exact ⟨ed, hed, Or.inr (by omega)⟩)]
      exact hloc0 u hu
  have h1_nl : st1.mem nextLblAddr = nl₀ := by
    rw [h1_frame nextLblAddr (fun ed hed => by
      have hl := hed_lt ed hed
      exact ⟨(disjointRange_ne hdLocNl (by omega) (by omega) (by omega) (by omega)).symm,
        (disjointRange_ne hdLocNl (by omega) (by omega) (by omega) (by omega)).symm⟩)]
    rfl
  have h1_r : ∀ r ≤ 7, st1.regs r = (startState [k, vertsAddr, e, edgesAddr, locAddr, labelsAddr,
      nextLblAddr, outActAddr] mem pos).regs r := fun r hr =>
    h1_keep r (by omega) (by omega) (by omega)
  -- r11 := mem[nextLblAddr]; r12 := 0
  refine runs_seq_assign_le (v := nl₀)
    (by simp [Expr.eval, h1_r 6 (by omega), startState, h1_nl, hwNl]) ?_
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  -- Pass 2: split verts into iso (labeled in labelsAddr) and act (written to outActAddr)
  let st2 : State := { st1 with regs := Function.update (Function.update st1.regs 11 nl₀) 12 0 }
  have h2_regs : ∀ r ≤ 7, st2.regs r = st1.regs r := fun r hr => by
    simp [st2, Function.update_of_ne (by omega : r ≠ 12), Function.update_of_ne (by omega : r ≠ 11)]
  have hpass2 := Triple.forRange_const (p := pProg) (r := 8) (lo := .const 0) (hi := .reg 0)
    (body :=
      .assign 9 (.load (.bin .add (.reg 1) (.reg 8))) ;;
      .assign 10 (.load (.bin .add (.reg 4) (.reg 9))) ;;
      .cond (.bin .eq (.reg 10) (.const 0))
        (.store (.bin .add (.reg 5) (.reg 9)) (.reg 11) ;;
         .assign 11 (.bin .add (.reg 11) (.const 1)))
        (.store (.bin .add (.reg 7) (.reg 12)) (.reg 9) ;;
         .assign 12 (.bin .add (.reg 12) (.const 1))))
    (P := fun s => s = st2)
    (Inv := fun i s =>
      let pfx := verts.take i
      let isoP := pfx.filter fun v => !hasEdge v
      let actP := pfx.filter hasEdge
      s.regs 8 = i ∧
      (∀ r ≤ 7, s.regs r = st1.regs r) ∧
      s.regs 11 = nl₀ + isoP.length ∧
      s.regs 12 = actP.length ∧
      ListAt s.mem outActAddr actP ∧
      (∀ u ∈ isoP, s.mem (labelsAddr + u) = nl₀ + isoP.idxOf u) ∧
      (∀ a, (∀ u ∈ isoP, a ≠ labelsAddr + u) → (a < outActAddr ∨ outActAddr + actP.length ≤ a) →
        s.mem a = st1.mem a))
    35 0 k (Nat.zero_le k) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 8), h2_regs r hr],
        by simp [st2], by simp [st2], fun i hi => by simp at hi, by simp, fun a _ _ => rfl⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hr0 : s.regs 0 = k := by rw [hi.2.1 0 (by omega), h1_r 0 (by omega)]; simp [startState]
      simp [Expr.eval, hr0])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hkr, hr11, hr12, hactL, hisoL, hfr⟩
      have hiLen : i < verts.length := by omega
      set v := verts[i]'hiLen
      have hv_in : v < n := hv_lt v (List.getElem_mem hiLen)
      have hv_not_pfx : v ∉ verts.take i := by
        intro hmem
        rcases List.mem_iff_getElem.mp hmem with ⟨j, hj, hjEq⟩
        rw [List.length_take, Nat.min_eq_left (by omega)] at hj
        rw [List.getElem_take] at hjEq
        have := (List.nodup_iff_injective_getElem.mp hndV) (a₁ := ⟨j, by omega⟩) (a₂ := ⟨i, hiLen⟩) hjEq
        simp at this; omega
      have hactLen_le : ((verts.take i).filter hasEdge).length ≤ i := by
        have := List.length_filter_le hasEdge (verts.take i)
        rw [List.length_take, Nat.min_eq_left (by omega)] at this; exact this
      have hisoLen_le : ((verts.take i).filter fun u => !hasEdge u).length ≤ i := by
        have := List.length_filter_le (fun u => !hasEdge u) (verts.take i)
        rw [List.length_take, Nat.min_eq_left (by omega)] at this; exact this
      have hvs_mem : s.mem (vertsAddr + i) = v := by
        rw [hfr (vertsAddr + i) (fun u hu =>
          (disjointRange_ne hdLblV (by omega) (by have := hv_lt u (List.mem_of_mem_take (List.mem_of_mem_filter hu)); omega)
            (by omega) (by omega)).symm)
          (Or.elim hdOutV (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        rw [h1_frame (vertsAddr + i) (fun ed hed => by
          have hl := hed_lt ed hed
          exact ⟨(disjointRange_ne hdLocV (by omega) (by omega) (by omega) (by omega)).symm,
            (disjointRange_ne hdLocV (by omega) (by omega) (by omega) (by omega)).symm⟩)]
        exact hlistV i hiLen
      have hloc_s : s.mem (locAddr + v) = if hasEdge v then 1 else 0 := by
        rw [hfr (locAddr + v) (fun u hu =>
          (disjointRange_ne hdLocLbl (by omega) (by omega) (by omega)
            (by have := hv_lt u (List.mem_of_mem_take (List.mem_of_mem_filter hu)); omega)))
          (Or.elim hdLocOut (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))]
        exact h1_loc_iff v hv_in
      have hr1 : s.regs 1 = vertsAddr := by rw [hkr 1 (by omega), h1_r 1 (by omega)]; simp [startState]
      have hr4 : s.regs 4 = locAddr := by rw [hkr 4 (by omega), h1_r 4 (by omega)]; simp [startState]
      have hr5 : s.regs 5 = labelsAddr := by rw [hkr 5 (by omega), h1_r 5 (by omega)]; simp [startState]
      have hr7 : s.regs 7 = outActAddr := by rw [hkr 7 (by omega), h1_r 7 (by omega)]; simp [startState]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := v)
        (by simp [Expr.eval, BinOp.eval, hr1, hiReg, (by omega : vertsAddr + i < 2 ^ w), hvs_mem]) ?_
      refine runs_seq_assign_le (v := if hasEdge v then 1 else 0)
        (by simp [Expr.eval, BinOp.eval, hr4, (by omega : locAddr + v < 2 ^ w), hloc_s]) ?_
      cases hhv : hasEdge v with
      | false =>
        let stA : State := { s with regs := Function.update (Function.update s.regs 9 v) 10 0 }
        have hA_regs : ∀ r, r ≠ 9 → r ≠ 10 → stA.regs r = s.regs r := fun r h9 h10 => by
          simp [stA, Function.update_of_ne h10, Function.update_of_ne h9]
        have hA_9 : stA.regs 9 = v := by simp [stA]
        have hA_10 : stA.regs 10 = 0 := by simp [stA]
        have hcond_ev : (Expr.bin .eq (.reg 10) (.const 0)).eval w stA = some 1 := by
          simp [Expr.eval, BinOp.eval, hA_10, hw1, (by omega : 0 < 2 ^ w)]
        let isoLen := ((verts.take i).filter fun u => !hasEdge u).length
        let memB := Function.update s.mem (labelsAddr + v) (nl₀ + isoLen)
        let stB : State := { stA with mem := memB }
        let stC : State := { stB with regs := Function.update stB.regs 11 (nl₀ + isoLen + 1) }
        have hs1 : Runs w pProg ω (.store (.bin .add (.reg 5) (.reg 9)) (.reg 11)) stA .normal stB 5 := by
          rw [runs_store_iff]
          exact ⟨labelsAddr + v, nl₀ + isoLen,
            by simp [Expr.eval, BinOp.eval, hA_regs 5 (by omega) (by omega), hr5, hA_9,
                 (by omega : labelsAddr + v < 2 ^ w)],
            by simp [Expr.eval, hA_regs 11 (by omega) (by omega), hr11, isoLen],
            rfl, rfl, by simp [Expr.size]⟩
        have hs2 : Runs w pProg ω (.assign 11 (.bin .add (.reg 11) (.const 1))) stB .normal stC 4 := by
          rw [runs_assign_iff]
          exact ⟨nl₀ + isoLen + 1,
            by simp [Expr.eval, BinOp.eval, stB, hA_regs 11 (by omega) (by omega), hr11, hw1, isoLen,
                 (by omega : nl₀ + isoLen + 1 < 2 ^ w)],
            rfl, rfl, by simp [Expr.size]⟩
        refine ⟨.normal, stC, 14, runs_cond_iff.mpr ⟨1, 10, hcond_ev, by
            simp only [one_ne_zero, ↓reduceIte]
            exact runs_seq_iff.mpr (Or.inr ⟨stB, 5, 4, hs1, hs2, rfl⟩),
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        have htake_iso : (verts.take (i + 1)).filter (fun u => !hasEdge u) =
            (verts.take i).filter (fun u => !hasEdge u) ++ [v] := by
          rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
          simp [v, hhv]
        have htake_act : (verts.take (i + 1)).filter hasEdge = (verts.take i).filter hasEdge := by
          rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
          simp [v, hhv]
        refine ⟨⟨by simp, fun r hr => by simp [stC, stB, Function.update_of_ne (by omega : r ≠ 8),
            Function.update_of_ne (by omega : r ≠ 11), hA_regs r (by omega) (by omega), hkr r hr],
          by simp [stC, htake_iso, isoLen]; omega,
          by simp [stC, stB, hA_regs 12 (by omega) (by omega), hr12, htake_act],
          ?_, ?_, ?_⟩, by simp [stC, stB, hA_regs 8 (by omega) (by omega), hiReg]⟩
        · rw [htake_act]
          intro j hj
          dsimp only [stC, stB, memB]
          rw [Function.update_of_ne (disjointRange_ne hdLblOut (by omega) (by omega) (by omega) (by omega)).symm]
          exact hactL j hj
        · intro u hu
          rw [htake_iso] at hu ⊢
          dsimp only [stC, stB, memB]
          rcases List.mem_append.mp hu with hu_old | hu_new
          · have hne : u ≠ v := fun heq => hv_not_pfx (heq ▸ List.mem_of_mem_filter hu_old)
            rw [Function.update_of_ne (by omega), List.idxOf_append_of_mem hu_old]
            exact hisoL u hu_old
          · simp only [List.mem_singleton] at hu_new
            subst hu_new
            have hnotm : v ∉ (verts.take i).filter (fun u => !hasEdge u) :=
              fun hm => hv_not_pfx (List.mem_of_mem_filter hm)
            rw [Function.update_self, List.idxOf_append_of_notMem hnotm]
            simp [isoLen]
        · intro a haIso haOut
          rw [htake_iso] at haIso; rw [htake_act] at haOut
          dsimp only [stC, stB, memB]
          rw [Function.update_of_ne (haIso v (by simp))]
          exact hfr a (fun u hu => haIso u (List.mem_append_left _ hu)) haOut
      | true =>
        let stA : State := { s with regs := Function.update (Function.update s.regs 9 v) 10 1 }
        have hA_regs : ∀ r, r ≠ 9 → r ≠ 10 → stA.regs r = s.regs r := fun r h9 h10 => by
          simp [stA, Function.update_of_ne h10, Function.update_of_ne h9]
        have hA_9 : stA.regs 9 = v := by simp [stA]
        have hA_10 : stA.regs 10 = 1 := by simp [stA]
        have hcond_ev : (Expr.bin .eq (.reg 10) (.const 0)).eval w stA = some 0 := by
          simp [Expr.eval, BinOp.eval, hA_10, (by omega : 0 < 2 ^ w)]
        let actLen := ((verts.take i).filter hasEdge).length
        let memB := Function.update s.mem (outActAddr + actLen) v
        let stB : State := { stA with mem := memB }
        let stC : State := { stB with regs := Function.update stB.regs 12 (actLen + 1) }
        have hs1 : Runs w pProg ω (.store (.bin .add (.reg 7) (.reg 12)) (.reg 9)) stA .normal stB 5 := by
          rw [runs_store_iff]
          exact ⟨outActAddr + actLen, v,
            by simp [Expr.eval, BinOp.eval, hA_regs 7 (by omega) (by omega), hr7,
                 hA_regs 12 (by omega) (by omega), hr12, actLen, (by omega : outActAddr + actLen < 2 ^ w)],
            by simp [Expr.eval, hA_9], rfl, rfl, by simp [Expr.size]⟩
        have hs2 : Runs w pProg ω (.assign 12 (.bin .add (.reg 12) (.const 1))) stB .normal stC 4 := by
          rw [runs_assign_iff]
          exact ⟨actLen + 1,
            by simp [Expr.eval, BinOp.eval, stB, hA_regs 12 (by omega) (by omega), hr12, hw1, actLen,
                 (by omega : actLen + 1 < 2 ^ w)],
            rfl, rfl, by simp [Expr.size]⟩
        refine ⟨.normal, stC, 14, runs_cond_iff.mpr ⟨0, 10, hcond_ev, by
            simp only [↓reduceIte]
            exact runs_seq_iff.mpr (Or.inr ⟨stB, 5, 4, hs1, hs2, rfl⟩),
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        have htake_iso : (verts.take (i + 1)).filter (fun u => !hasEdge u) =
            (verts.take i).filter (fun u => !hasEdge u) := by
          rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
          simp [v, hhv]
        have htake_act : (verts.take (i + 1)).filter hasEdge = (verts.take i).filter hasEdge ++ [v] := by
          rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
          simp [v, hhv]
        refine ⟨⟨by simp, fun r hr => by simp [stC, stB, Function.update_of_ne (by omega : r ≠ 8),
            Function.update_of_ne (by omega : r ≠ 12), hA_regs r (by omega) (by omega), hkr r hr],
          by simp [stC, stB, hA_regs 11 (by omega) (by omega), hr11, htake_iso],
          by simp [stC, htake_act, actLen],
          ?_, ?_, ?_⟩, by simp [stC, stB, hA_regs 8 (by omega) (by omega), hiReg]⟩
        · rw [htake_act]
          simpa [stC, stB, memB, actLen] using hactL.snoc v
        · intro u hu
          rw [htake_iso] at hu ⊢
          dsimp only [stC, stB, memB]
          have hu_lt : u < n := hv_lt u (List.mem_of_mem_take (List.mem_of_mem_filter hu))
          rw [Function.update_of_ne (disjointRange_ne hdLblOut (by omega) (by omega) (by omega) (by omega))]
          exact hisoL u hu
        · intro a haIso haOut
          rw [htake_iso] at haIso; rw [htake_act, List.length_append, List.length_singleton] at haOut
          dsimp only [stC, stB, memB]
          rw [Function.update_of_ne (by omega)]
          exact hfr a haIso (by omega))
  refine runs_seq_triple_le hpass2 rfl ?_
  intro st3 ⟨_, h3_kr, h3_11, h3_12, h3_actL, h3_isoL, h3_fr⟩
  have htakeV : verts.take k = verts := by rw [← hlenV, List.take_length]
  rw [htakeV] at h3_11 h3_12 h3_actL h3_isoL h3_fr
  -- Store mem[nextLblAddr] := r11
  refine runs_seq_store_le (x := nextLblAddr) (v := nl₀ + (verts.filter fun u => !hasEdge u).length)
    (by simp [Expr.eval, h3_kr 6 (by omega), h1_r 6 (by omega), startState])
    (by simp [Expr.eval, h3_11]) ?_
  -- Pass 3: clear locAddr over edges
  let st4 : State := { st3 with mem := Function.update st3.mem nextLblAddr (nl₀ + (verts.filter fun u => !hasEdge u).length) }
  have h4_edges : EdgesAt st4.mem edgesAddr edges := by
    intro j hj
    have h4_eq : ∀ a, edgesAddr ≤ a → a < edgesAddr + 2 * e → st4.mem a = mem a := fun a ha1 ha2 => by
      dsimp only [st4]
      rw [Function.update_of_ne (disjointRange_ne hdNlE (by omega) (by omega) ha1 ha2).symm]
      rw [h3_fr a (fun u hu =>
          (disjointRange_ne hdLblE (by omega) (by have := hv_lt u (List.mem_of_mem_filter hu); omega) ha1 ha2).symm)
        (by have hle : (verts.filter hasEdge).length ≤ k := by rw [← hlenV]; exact List.length_filter_le _ _
            exact Or.elim hdOutE (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
      exact h1_frame a fun ed hed => by
        have hl := hed_lt ed hed
        exact ⟨(disjointRange_ne hdLocE (by omega) (by omega) ha1 ha2).symm,
          (disjointRange_ne hdLocE (by omega) (by omega) ha1 ha2).symm⟩
    have hj' : j < e := by omega
    rw [h4_eq (edgesAddr + 2 * j) (by omega) (by omega),
      h4_eq (edgesAddr + 2 * j + 1) (by omega) (by omega)]
    exact hedgesE j hj
  refine runs_seq_triple_le
    (markEdges_triple (w := w) (n := n) (e := e) (edgesAddr := edgesAddr) (locAddr := locAddr)
      (val := 0) (rE := 2) (rEdges := 3) (rLoc := 4) (rI := 8) (rU := 9) (rV := 10)
      pProg st4 edges (by decide)
      (by simp [st4, h3_kr 2 (by omega), h1_r 2 (by omega), startState])
      (by simp [st4, h3_kr 3 (by omega), h1_r 3 (by omega), startState])
      (by simp [st4, h3_kr 4 (by omega), h1_r 4 (by omega), startState])
      hlenE hed_lt h4_edges hdLocE hwE hwLoc (by omega) hw2) rfl ?_
  intro st5 ⟨h5_clear, h5_frame, h5_keep⟩
  have h5_12 : st5.regs 12 = (verts.filter hasEdge).length := by
    rw [h5_keep 12 (by omega) (by omega) (by omega)]; exact h3_12
  refine runs_ret_le (v := (verts.filter hasEdge).length) (by simp [Expr.eval, h5_12]) ?_ ?_
  · dsimp only [stripIsolatedContract, Outcome.value, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    have hreadV : readList mem vertsAddr k = verts := by rw [← hlenV]; exact readList_eq_of_listAt hlistV
    have hreadE : readEdges mem edgesAddr e = edges := by rw [← hlenE]; exact readEdges_eq_of_edgesAt hedgesE
    rw [hreadV, hreadE]
    have hiso_eq : (CompactSubgraph.mk verts edges).stripIsolated.1 = verts.filter fun u => !hasEdge u := rfl
    have hact_eq : (CompactSubgraph.mk verts edges).stripIsolated.2.verts = verts.filter hasEdge := rfl
    rw [hiso_eq, hact_eq]
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · intro j hj
      have hj_k : j < k := by
        have := List.length_filter_le hasEdge verts; omega
      rw [h5_frame (outActAddr + j) (fun ed hed => by
        have hl := hed_lt ed hed
        exact ⟨(disjointRange_ne hdLocOut (by omega) (by omega) (by omega) (by omega)).symm,
          (disjointRange_ne hdLocOut (by omega) (by omega) (by omega) (by omega)).symm⟩)]
      dsimp only [st4]
      rw [Function.update_of_ne (disjointRange_ne hdOutNl (by omega) (by omega) (by omega) (by omega))]
      exact h3_actL j hj
    · rw [h5_frame nextLblAddr (fun ed hed => by
        have hl := hed_lt ed hed
        exact ⟨(disjointRange_ne hdLocNl (by omega) (by omega) (by omega) (by omega)).symm,
          (disjointRange_ne hdLocNl (by omega) (by omega) (by omega) (by omega)).symm⟩)]
      simp [st4, nl₀]
    · intro u hu
      have hu_lt : u < n := hv_lt u (List.mem_of_mem_filter hu)
      rw [h5_frame (labelsAddr + u) (fun ed hed => by
        have hl := hed_lt ed hed
        exact ⟨(disjointRange_ne hdLocLbl (by omega) (by omega) (by omega) (by omega)).symm,
          (disjointRange_ne hdLocLbl (by omega) (by omega) (by omega) (by omega)).symm⟩)]
      dsimp only [st4]
      rw [Function.update_of_ne (disjointRange_ne hdLblNl (by omega) (by omega) (by omega) (by omega))]
      exact h3_isoL u hu
    · intro a haIso haNl haOut
      by_cases hEd : ∃ ed ∈ edges, a = locAddr + ed.1 ∨ a = locAddr + ed.2
      · rcases hEd with ⟨ed, hed, rfl | rfl⟩
        · rw [(h5_clear ed hed).1, hloc0 ed.1 (hed_lt ed hed).1]
        · rw [(h5_clear ed hed).2, hloc0 ed.2 (hed_lt ed hed).2]
      · push Not at hEd
        rw [h5_frame a hEd]
        dsimp only [st4]
        rw [Function.update_of_ne haNl]
        have hle : (verts.filter hasEdge).length ≤ k := by rw [← hlenV]; exact List.length_filter_le _ _
        rw [h3_fr a haIso (by omega)]
        exact h1_frame a hEd
  · simp only [stripIsolatedContract, stripIsolatedCost, Expr.size, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    omega


end MinCostFlow.ExpanderDecomp
