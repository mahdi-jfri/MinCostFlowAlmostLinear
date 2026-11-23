module

public import MinCostFlow.ExpanderDecomp.OuterProgSubgraphBase
public import MinCostFlow.ExpanderDecomp.OuterProgSubgraphStrip
import Mathlib.Tactic.Linarith

/-!
# Verification of `restrictProc` and `setDiffProc` (`OuterProgSubgraphOps`)

Proves `restrictProc_spec` and `setDiffProc_spec` and re-exports `OuterProgSubgraphBase` and
`OuterProgSubgraphStrip`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 7. Verification of `restrictProc` and `setDiffProc` -/

/-- Specification of `restrictProc`. -/
theorem restrictProc_spec {w : ℕ} {pProg : Program} {b : ℕ}
    (hp : pProg.HasAt b [restrictProc]) :
    MeetsContract w pProg b (restrictContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨n, kS, sVertsAddr, e, edgesAddr, locAddr, outEdgesAddr, sVerts, edges, rfl,
    hlenS, hs_lt, hlenE, hed_lt, hlistS, hedgesE, hloc0, hwS, hwE, hwLoc, hwOut, hw16,
    hdLocS, hdLocE, hdLocOut, hdOutS, hdOutE⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  set inS : ℕ × ℕ → Bool := fun ed => decide (ed.1 ∈ sVerts.toFinset ∧ ed.2 ∈ sVerts.toFinset)
  refine runs_start_le ?_
  dsimp only [restrictProc]
  refine runs_seq_triple_le
    (markVerts_triple (w := w) (n := n) (len := kS) (listAddr := sVertsAddr) (locAddr := locAddr)
      (val := 1) (rLen := 0) (rList := 1) (rLoc := 4) (rI := 6) (rU := 7)
      pProg (startState _ mem pos) sVerts (by decide)
      (by simp [startState]) (by simp [startState]) (by simp [startState])
      hlenS hs_lt hlistS hdLocS hwS hwLoc hw1 hw1) rfl ?_
  intro st1 ⟨h1_mark, h1_frame, h1_keep⟩
  have h1_loc_iff : ∀ u < n, st1.mem (locAddr + u) = if u ∈ sVerts.toFinset then 1 else 0 := by
    intro u hu
    by_cases h : u ∈ sVerts.toFinset
    · simp only [h, ↓reduceIte]; exact h1_mark u (List.mem_toFinset.mp h)
    · simp only [h, ↓reduceIte]
      rw [h1_frame (locAddr + u) (fun v hv heq => h (List.mem_toFinset.mpr ((show u = v by omega) ▸ hv)))]
      exact hloc0 u hu
  have h1_r : ∀ r ≤ 5, st1.regs r = (startState [kS, sVertsAddr, e, edgesAddr, locAddr, outEdgesAddr] mem pos).regs r :=
    fun r hr => h1_keep r (by omega) (by omega)
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  let st2 : State := { st1 with regs := Function.update st1.regs 11 0 }
  have h2_regs : ∀ r ≤ 5, st2.regs r = st1.regs r := fun r hr => by
    simp [st2, Function.update_of_ne (by omega : r ≠ 11)]
  have hpass2 := Triple.forRange_const (p := pProg) (r := 6) (lo := .const 0) (hi := .reg 2)
    (body :=
      .assign 7 (.load (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 6)))) ;;
      .assign 8 (.load (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 6))) (.const 1))) ;;
      .assign 9 (.load (.bin .add (.reg 4) (.reg 7))) ;;
      .assign 10 (.load (.bin .add (.reg 4) (.reg 8))) ;;
      .cond (.bin .lt (.const 0) (.reg 9))
        (.cond (.bin .lt (.const 0) (.reg 10))
          (.store (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 11))) (.reg 7) ;;
           .store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 11))) (.const 1)) (.reg 8) ;;
           .assign 11 (.bin .add (.reg 11) (.const 1)))
          .nop)
        .nop)
    (P := fun s => s = st2)
    (Inv := fun i s =>
      let filt := (edges.take i).filter inS
      s.regs 6 = i ∧
      (∀ r ≤ 5, s.regs r = st1.regs r) ∧
      s.regs 11 = filt.length ∧
      EdgesAt s.mem outEdgesAddr filt ∧
      (∀ a, a < outEdgesAddr ∨ outEdgesAddr + 2 * filt.length ≤ a → s.mem a = st1.mem a))
    65 0 e (Nat.zero_le e) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 6), h2_regs r hr],
        by simp [st2], fun j hj => by simp at hj, fun a _ => rfl⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hr2 : s.regs 2 = e := by rw [hi.2.1 2 (by omega), h1_r 2 (by omega)]; simp [startState]
      simp [Expr.eval, hr2])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hkr, hr11, hedOut, hfr⟩
      have hiLen : i < edges.length := by omega
      set ed := edges[i]'hiLen
      have hed_n := hed_lt ed (List.getElem_mem hiLen)
      have hfilt_le : ((edges.take i).filter inS).length ≤ i := by
        have := List.length_filter_le inS (edges.take i)
        rw [List.length_take, Nat.min_eq_left (by omega)] at this; exact this
      have hmem_e1 : s.mem (edgesAddr + 2 * i) = ed.1 := by
        rw [hfr (edgesAddr + 2 * i) (Or.elim hdOutE (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        rw [h1_frame (edgesAddr + 2 * i) (fun u hu =>
          (disjointRange_ne hdLocE (by omega) (by have := hs_lt u hu; omega) (by omega) (by omega)).symm)]
        exact (hedgesE i hiLen).1
      have hmem_e2 : s.mem (edgesAddr + 2 * i + 1) = ed.2 := by
        rw [hfr (edgesAddr + 2 * i + 1) (Or.elim hdOutE (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        rw [h1_frame (edgesAddr + 2 * i + 1) (fun u hu =>
          (disjointRange_ne hdLocE (by omega) (by have := hs_lt u hu; omega) (by omega) (by omega)).symm)]
        exact (hedgesE i hiLen).2
      have hloc_u : s.mem (locAddr + ed.1) = if ed.1 ∈ sVerts.toFinset then 1 else 0 := by
        rw [hfr (locAddr + ed.1) (Or.elim hdLocOut (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))]
        exact h1_loc_iff ed.1 hed_n.1
      have hloc_v : s.mem (locAddr + ed.2) = if ed.2 ∈ sVerts.toFinset then 1 else 0 := by
        rw [hfr (locAddr + ed.2) (Or.elim hdLocOut (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))]
        exact h1_loc_iff ed.2 hed_n.2
      have hr3 : s.regs 3 = edgesAddr := by rw [hkr 3 (by omega), h1_r 3 (by omega)]; simp [startState]
      have hr4 : s.regs 4 = locAddr := by rw [hkr 4 (by omega), h1_r 4 (by omega)]; simp [startState]
      have hr5 : s.regs 5 = outEdgesAddr := by rw [hkr 5 (by omega), h1_r 5 (by omega)]; simp [startState]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := ed.1)
        (by simp [Expr.eval, BinOp.eval, hr3, hiReg, hw2, (by omega : 2 * i < 2 ^ w),
              (by omega : edgesAddr + 2 * i < 2 ^ w), hmem_e1]) ?_
      refine runs_seq_assign_le (v := ed.2)
        (by simp [Expr.eval, BinOp.eval, hr3, hiReg, hw1, hw2, (by omega : 2 * i < 2 ^ w),
              (by omega : edgesAddr + 2 * i < 2 ^ w),
              (by omega : edgesAddr + 2 * i + 1 < 2 ^ w), hmem_e2]) ?_
      refine runs_seq_assign_le (v := if ed.1 ∈ sVerts.toFinset then 1 else 0)
        (by simp [Expr.eval, BinOp.eval, hr4, (by omega : locAddr + ed.1 < 2 ^ w), hloc_u]) ?_
      refine runs_seq_assign_le (v := if ed.2 ∈ sVerts.toFinset then 1 else 0)
        (by simp [Expr.eval, BinOp.eval, hr4, (by omega : locAddr + ed.2 < 2 ^ w), hloc_v]) ?_
      let stA : State := { s with regs :=
        (Function.update (Function.update (Function.update (Function.update s.regs 7 ed.1) 8 ed.2)
          9 (if ed.1 ∈ sVerts.toFinset then 1 else 0)) 10 (if ed.2 ∈ sVerts.toFinset then 1 else 0)) }
      have hA_regs : ∀ r, r ≤ 6 ∨ r = 11 → stA.regs r = s.regs r := fun r hr => by
        simp [stA, Function.update_of_ne (by omega : r ≠ 10), Function.update_of_ne (by omega : r ≠ 9),
          Function.update_of_ne (by omega : r ≠ 8), Function.update_of_ne (by omega : r ≠ 7)]
      have hA_7 : stA.regs 7 = ed.1 := by simp [stA]
      have hA_8 : stA.regs 8 = ed.2 := by simp [stA]
      have hA_9 : stA.regs 9 = if ed.1 ∈ sVerts.toFinset then 1 else 0 := by simp [stA]
      have hA_10 : stA.regs 10 = if ed.2 ∈ sVerts.toFinset then 1 else 0 := by simp [stA]
      by_cases h1in : ed.1 ∈ sVerts.toFinset
      · by_cases h2in : ed.2 ∈ sVerts.toFinset
        · let cnt := ((edges.take i).filter inS).length
          have htake_eq : (edges.take (i + 1)).filter inS = (edges.take i).filter inS ++ [ed] := by
            rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
            simp only [List.filter_cons, List.filter_nil, ed, inS, h1in, h2in, and_self,
              decide_true, ↓reduceIte]
          let mem1 := Function.update s.mem (outEdgesAddr + 2 * cnt) ed.1
          let mem2 := Function.update mem1 (outEdgesAddr + 2 * cnt + 1) ed.2
          let stB1 : State := { stA with mem := mem1 }
          let stB2 : State := { stB1 with mem := mem2 }
          let stC : State := { stB2 with regs := Function.update stB2.regs 11 (cnt + 1) }
          have hs1 : Runs w pProg ω (.store (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 11))) (.reg 7))
              stA .normal stB1 7 := by
            rw [runs_store_iff]
            exact ⟨outEdgesAddr + 2 * cnt, ed.1,
              by simp [Expr.eval, BinOp.eval, hA_regs 5 (Or.inl (by omega)), hr5,
                   hA_regs 11 (Or.inr rfl), hr11, hw2, cnt, (by omega : 2 * cnt < 2 ^ w),
                   (by omega : outEdgesAddr + 2 * cnt < 2 ^ w)],
              by simp [Expr.eval, hA_7], rfl, rfl, by simp [Expr.size]⟩
          have hs2 : Runs w pProg ω (.store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 11))) (.const 1)) (.reg 8))
              stB1 .normal stB2 9 := by
            rw [runs_store_iff]
            exact ⟨outEdgesAddr + 2 * cnt + 1, ed.2,
              by simp [Expr.eval, BinOp.eval, stB1, hA_regs 5 (Or.inl (by omega)), hr5,
                   hA_regs 11 (Or.inr rfl), hr11, hw1, hw2, cnt, (by omega : 2 * cnt < 2 ^ w),
                   (by omega : outEdgesAddr + 2 * cnt < 2 ^ w),
                   (by omega : outEdgesAddr + 2 * cnt + 1 < 2 ^ w)],
              by simp [Expr.eval, stB1, hA_8], rfl, rfl, by simp [Expr.size]⟩
          have hs3 : Runs w pProg ω (.assign 11 (.bin .add (.reg 11) (.const 1)))
              stB2 .normal stC 4 := by
            rw [runs_assign_iff]
            exact ⟨cnt + 1,
              by simp [Expr.eval, BinOp.eval, stB2, stB1, hA_regs 11 (Or.inr rfl), hr11, hw1, cnt,
                   (by omega : cnt + 1 < 2 ^ w)],
              rfl, rfl, by simp [Expr.size]⟩
          let storeBody : Stmt :=
            .store (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 11))) (.reg 7) ;;
            .store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 11))) (.const 1)) (.reg 8) ;;
            .assign 11 (.bin .add (.reg 11) (.const 1))
          have hbody : Runs w pProg ω storeBody stA .normal stC 22 :=
            runs_seq_iff.mpr (Or.inr ⟨stB1, 7, 14, hs1, runs_seq_iff.mpr (Or.inr ⟨stB2, 9, 4, hs2, hs3, rfl⟩), rfl⟩)
          have hinner : Runs w pProg ω (.cond (.bin .lt (.const 0) (.reg 10)) storeBody .nop) stA .normal stC 26 :=
            runs_cond_iff.mpr ⟨1, 22, by simp [Expr.eval, BinOp.eval, hA_10, h2in, hw1, (by omega : 0 < 2 ^ w)],
              by simp only [one_ne_zero, ↓reduceIte]; exact hbody, by simp [Expr.size]⟩
          refine ⟨.normal, stC, 30, runs_cond_iff.mpr ⟨1, 26,
              by simp [Expr.eval, BinOp.eval, hA_9, h1in, hw1, (by omega : 0 < 2 ^ w)],
              by simp only [one_ne_zero, ↓reduceIte]; exact hinner, by simp [Expr.size]⟩,
            ?_, by simp [Expr.size]⟩
          refine ⟨⟨by simp, fun r hr => by simp [stC, stB2, stB1,
              Function.update_of_ne (by omega : r ≠ 6), Function.update_of_ne (by omega : r ≠ 11),
              hA_regs r (Or.inl (by omega)), hkr r hr],
            by simp [stC, htake_eq, cnt], ?_, ?_⟩,
            by simp [stC, stB2, stB1, hA_regs 6 (Or.inl (by omega)), hiReg]⟩
          · rw [htake_eq]
            intro j hj
            rw [List.length_append, List.length_singleton] at hj
            dsimp only [stC, stB2, stB1, mem2, mem1]
            by_cases hlt : j < cnt
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              simpa [List.getElem_append_left hlt] using hedOut j hlt
            · have hjeq : j = cnt := by omega
              subst hjeq
              refine ⟨?_, ?_⟩
              · rw [Function.update_of_ne (by omega : outEdgesAddr + 2 * cnt ≠ outEdgesAddr + 2 * cnt + 1),
                  Function.update_self]
                simp [List.getElem_append_right (le_refl cnt), cnt]
              · rw [Function.update_self]
                simp [List.getElem_append_right (le_refl cnt), cnt]
          · intro a ha
            rw [htake_eq, List.length_append, List.length_singleton] at ha
            dsimp only [stC, stB2, stB1, mem2, mem1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hfr a (by omega)
        · have htake_eq : (edges.take (i + 1)).filter inS = (edges.take i).filter inS := by
            rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
            simp only [List.filter_cons, List.filter_nil, ed, inS, h2in, and_false,
              decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
          let storeBody : Stmt :=
            .store (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 11))) (.reg 7) ;;
            .store (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 2) (.reg 11))) (.const 1)) (.reg 8) ;;
            .assign 11 (.bin .add (.reg 11) (.const 1))
          have hinner : Runs w pProg ω (.cond (.bin .lt (.const 0) (.reg 10)) storeBody .nop) stA .normal stA 5 :=
            runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, BinOp.eval, hA_10, h2in, (by omega : 0 < 2 ^ w)],
              by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
          refine ⟨.normal, stA, 9, runs_cond_iff.mpr ⟨1, 5,
              by simp [Expr.eval, BinOp.eval, hA_9, h1in, hw1, (by omega : 0 < 2 ^ w)],
              by simp only [one_ne_zero, ↓reduceIte]; exact hinner, by simp [Expr.size]⟩,
            ?_, by simp [Expr.size]⟩
          refine ⟨⟨by simp, fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 6),
              hA_regs r (Or.inl (by omega)), hkr r hr],
            by rw [htake_eq]; simp [hA_regs 11 (Or.inr rfl), hr11],
            by rw [htake_eq]; exact hedOut, by rw [htake_eq]; exact hfr⟩,
            by rw [hA_regs 6 (Or.inl (by omega)), hiReg]⟩
      · have htake_eq : (edges.take (i + 1)).filter inS = (edges.take i).filter inS := by
          rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
          simp only [List.filter_cons, List.filter_nil, ed, inS, h1in, false_and,
            decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
        refine ⟨.normal, stA, 5, runs_cond_iff.mpr ⟨0, 1,
            by simp [Expr.eval, BinOp.eval, hA_9, h1in, (by omega : 0 < 2 ^ w)],
            by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
          ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 6),
            hA_regs r (Or.inl (by omega)), hkr r hr],
          by rw [htake_eq]; simp [hA_regs 11 (Or.inr rfl), hr11],
          by rw [htake_eq]; exact hedOut, by rw [htake_eq]; exact hfr⟩,
          by rw [hA_regs 6 (Or.inl (by omega)), hiReg]⟩)
  refine runs_seq_triple_le hpass2 rfl ?_
  intro st3 ⟨_, h3_kr, h3_11, h3_edOut, h3_fr⟩
  have htakeE : edges.take e = edges := by rw [← hlenE, List.take_length]
  rw [htakeE] at h3_11 h3_edOut h3_fr
  have h3_sList : ListAt st3.mem sVertsAddr sVerts := by
    intro j hj
    have hle : (edges.filter inS).length ≤ e := by rw [← hlenE]; exact List.length_filter_le _ _
    rw [h3_fr (sVertsAddr + j) (Or.elim hdOutS (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
    rw [h1_frame (sVertsAddr + j) (fun u hu =>
      (disjointRange_ne hdLocS (by omega) (by have := hs_lt u hu; omega) (by omega) (by omega)).symm)]
    exact hlistS j hj
  refine runs_seq_triple_le
    (markVerts_triple (w := w) (n := n) (len := kS) (listAddr := sVertsAddr) (locAddr := locAddr)
      (val := 0) (rLen := 0) (rList := 1) (rLoc := 4) (rI := 6) (rU := 7)
      pProg st3 sVerts (by decide)
      (by rw [h3_kr 0 (by omega), h1_r 0 (by omega)]; simp [startState])
      (by rw [h3_kr 1 (by omega), h1_r 1 (by omega)]; simp [startState])
      (by rw [h3_kr 4 (by omega), h1_r 4 (by omega)]; simp [startState])
      hlenS hs_lt h3_sList hdLocS hwS hwLoc (by omega) hw1) rfl ?_
  intro st4 ⟨h4_clear, h4_frame, h4_keep⟩
  have h4_11 : st4.regs 11 = (edges.filter inS).length := by
    rw [h4_keep 11 (by omega) (by omega)]; exact h3_11
  refine runs_ret_le (v := (edges.filter inS).length) (by simp [Expr.eval, h4_11]) ?_ ?_
  · dsimp only [restrictContract, Outcome.value, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    have hreadS : readList mem sVertsAddr kS = sVerts := by rw [← hlenS]; exact readList_eq_of_listAt hlistS
    have hreadE : readEdges mem edgesAddr e = edges := by rw [← hlenE]; exact readEdges_eq_of_edgesAt hedgesE
    simp only [hreadS, hreadE]
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj
      have hj' : j < (edges.filter inS).length := hj
      have hj_e : j < e := by have := List.length_filter_le inS edges; omega
      have hne1 : ∀ u ∈ sVerts, outEdgesAddr + 2 * j ≠ locAddr + u := fun u hu =>
        (disjointRange_ne hdLocOut (by omega) (by have := hs_lt u hu; omega) (by omega) (by omega)).symm
      have hne2 : ∀ u ∈ sVerts, outEdgesAddr + 2 * j + 1 ≠ locAddr + u := fun u hu =>
        (disjointRange_ne hdLocOut (by omega) (by have := hs_lt u hu; omega) (by omega) (by omega)).symm
      rw [h4_frame _ hne1, h4_frame _ hne2]
      exact h3_edOut j hj'
    · intro a ha
      by_cases hmemS : ∃ u ∈ sVerts, a = locAddr + u
      · rcases hmemS with ⟨u, hu, rfl⟩
        rw [h4_clear u hu, hloc0 u (hs_lt u hu)]
      · push Not at hmemS
        rw [h4_frame a hmemS]
        have hle : (edges.filter inS).length ≤ e := by rw [← hlenE]; exact List.length_filter_le _ _
        rw [h3_fr a (by omega)]
        exact h1_frame a hmemS
  · simp only [restrictContract, restrictCost, Expr.size, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    omega

/-- Specification of `setDiffProc`. -/
theorem setDiffProc_spec {w : ℕ} {pProg : Program} {b : ℕ}
    (hp : pProg.HasAt b [setDiffProc]) :
    MeetsContract w pProg b (setDiffContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨n, k, vertsAddr, kR, rAddr, locAddr, outRestAddr, verts, rList, rfl,
    hlenV, hv_lt, hlenR, hr_lt, hlistV, hlistR, hloc0, hwV, hwR, hwLoc, hwOut, hw16,
    hdLocV, hdLocR, hdLocOut, hdOutV, hdOutR⟩
  have hw1 : 1 < 2 ^ w := by omega
  set notR : ℕ → Bool := fun u => decide (u ∉ rList.toFinset)
  refine runs_start_le ?_
  dsimp only [setDiffProc]
  refine runs_seq_triple_le
    (markVerts_triple (w := w) (n := n) (len := kR) (listAddr := rAddr) (locAddr := locAddr)
      (val := 1) (rLen := 2) (rList := 3) (rLoc := 4) (rI := 6) (rU := 7)
      pProg (startState _ mem pos) rList (by decide)
      (by simp [startState]) (by simp [startState]) (by simp [startState])
      hlenR hr_lt hlistR hdLocR hwR hwLoc hw1 hw1) rfl ?_
  intro st1 ⟨h1_mark, h1_frame, h1_keep⟩
  have h1_loc_iff : ∀ u < n, st1.mem (locAddr + u) = if u ∈ rList.toFinset then 1 else 0 := by
    intro u hu
    by_cases h : u ∈ rList.toFinset
    · simp only [h, ↓reduceIte]; exact h1_mark u (List.mem_toFinset.mp h)
    · simp only [h, ↓reduceIte]
      rw [h1_frame (locAddr + u) (fun v hv heq => h (List.mem_toFinset.mpr ((show u = v by omega) ▸ hv)))]
      exact hloc0 u hu
  have h1_r : ∀ r ≤ 5, st1.regs r = (startState [k, vertsAddr, kR, rAddr, locAddr, outRestAddr] mem pos).regs r :=
    fun r hr => h1_keep r (by omega) (by omega)
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  let st2 : State := { st1 with regs := Function.update st1.regs 9 0 }
  have h2_regs : ∀ r ≤ 5, st2.regs r = st1.regs r := fun r hr => by
    simp [st2, Function.update_of_ne (by omega : r ≠ 9)]
  have hpass2 := Triple.forRange_const (p := pProg) (r := 6) (lo := .const 0) (hi := .reg 0)
    (body :=
      .assign 7 (.load (.bin .add (.reg 1) (.reg 6))) ;;
      .assign 8 (.load (.bin .add (.reg 4) (.reg 7))) ;;
      .cond (.bin .eq (.reg 8) (.const 0))
        (.store (.bin .add (.reg 5) (.reg 9)) (.reg 7) ;;
         .assign 9 (.bin .add (.reg 9) (.const 1)))
        .nop)
    (P := fun s => s = st2)
    (Inv := fun i s =>
      let filt := (verts.take i).filter notR
      s.regs 6 = i ∧
      (∀ r ≤ 5, s.regs r = st1.regs r) ∧
      s.regs 9 = filt.length ∧
      ListAt s.mem outRestAddr filt ∧
      (∀ a, a < outRestAddr ∨ outRestAddr + filt.length ≤ a → s.mem a = st1.mem a))
    35 0 k (Nat.zero_le k) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 6), h2_regs r hr],
        by simp [st2], fun j hj => by simp at hj, fun a _ => rfl⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by
      have hr0 : s.regs 0 = k := by rw [hi.2.1 0 (by omega), h1_r 0 (by omega)]; simp [startState]
      simp [Expr.eval, hr0])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hkr, hr9, houtL, hfr⟩
      have hiLen : i < verts.length := by omega
      set v := verts[i]'hiLen
      have hv_n : v < n := hv_lt v (List.getElem_mem hiLen)
      have hfilt_le : ((verts.take i).filter notR).length ≤ i := by
        have := List.length_filter_le notR (verts.take i)
        rw [List.length_take, Nat.min_eq_left (by omega)] at this; exact this
      have hmem_v : s.mem (vertsAddr + i) = v := by
        rw [hfr (vertsAddr + i) (Or.elim hdOutV (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        rw [h1_frame (vertsAddr + i) (fun u hu =>
          (disjointRange_ne hdLocV (by omega) (by have := hr_lt u hu; omega) (by omega) (by omega)).symm)]
        exact hlistV i hiLen
      have hloc_v : s.mem (locAddr + v) = if v ∈ rList.toFinset then 1 else 0 := by
        rw [hfr (locAddr + v) (Or.elim hdLocOut (fun h => Or.inl (by omega)) (fun h => Or.inr (by omega)))]
        exact h1_loc_iff v hv_n
      have hr1 : s.regs 1 = vertsAddr := by rw [hkr 1 (by omega), h1_r 1 (by omega)]; simp [startState]
      have hr4 : s.regs 4 = locAddr := by rw [hkr 4 (by omega), h1_r 4 (by omega)]; simp [startState]
      have hr5 : s.regs 5 = outRestAddr := by rw [hkr 5 (by omega), h1_r 5 (by omega)]; simp [startState]
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := v)
        (by simp [Expr.eval, BinOp.eval, hr1, hiReg, (by omega : vertsAddr + i < 2 ^ w), hmem_v]) ?_
      refine runs_seq_assign_le (v := if v ∈ rList.toFinset then 1 else 0)
        (by simp [Expr.eval, BinOp.eval, hr4, (by omega : locAddr + v < 2 ^ w), hloc_v]) ?_
      let stA : State := { s with regs := Function.update (Function.update s.regs 7 v) 8 (if v ∈ rList.toFinset then 1 else 0) }
      have hA_regs : ∀ r, r ≤ 6 ∨ r = 9 → stA.regs r = s.regs r := fun r hr => by
        simp [stA, Function.update_of_ne (by omega : r ≠ 8), Function.update_of_ne (by omega : r ≠ 7)]
      have hA_7 : stA.regs 7 = v := by simp [stA]
      have hA_8 : stA.regs 8 = if v ∈ rList.toFinset then 1 else 0 := by simp [stA]
      by_cases hvin : v ∈ rList.toFinset
      · have htake_eq : (verts.take (i + 1)).filter notR = (verts.take i).filter notR := by
          rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
          simp only [List.filter_cons, List.filter_nil, v, notR, hvin, not_true_eq_false,
            decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
        refine ⟨.normal, stA, 5, runs_cond_iff.mpr ⟨0, 1,
            by simp [Expr.eval, BinOp.eval, hA_8, hvin, (by omega : 0 < 2 ^ w)],
            by simp only [↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
          ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, fun r hr => by simp [Function.update_of_ne (by omega : r ≠ 6),
            hA_regs r (Or.inl (by omega)), hkr r hr],
          by rw [htake_eq]; simp [hA_regs 9 (Or.inr rfl), hr9],
          by rw [htake_eq]; exact houtL, by rw [htake_eq]; exact hfr⟩,
          by rw [hA_regs 6 (Or.inl (by omega)), hiReg]⟩
      · let cnt := ((verts.take i).filter notR).length
        have htake_eq : (verts.take (i + 1)).filter notR = (verts.take i).filter notR ++ [v] := by
          rw [List.take_succ_eq_append_getElem hiLen, List.filter_append]
          simp only [List.filter_cons, List.filter_nil, v, notR, hvin, not_false_eq_true,
            decide_true, ↓reduceIte]
        set memB := Function.update s.mem (outRestAddr + cnt) v
        set stB : State := { stA with mem := memB }
        set stC : State := { stB with regs := Function.update stB.regs 9 (cnt + 1) }
        have hs1 : Runs w pProg ω (.store (.bin .add (.reg 5) (.reg 9)) (.reg 7)) stA .normal stB 5 := by
          rw [runs_store_iff]
          exact ⟨outRestAddr + cnt, v,
            by simp [Expr.eval, BinOp.eval, hA_regs 5 (Or.inl (by omega)), hr5,
                 hA_regs 9 (Or.inr rfl), hr9, cnt, (by omega : outRestAddr + cnt < 2 ^ w)],
            by simp [Expr.eval, hA_7], rfl, rfl, by simp [Expr.size]⟩
        have hs2 : Runs w pProg ω (.assign 9 (.bin .add (.reg 9) (.const 1))) stB .normal stC 4 := by
          rw [runs_assign_iff]
          exact ⟨cnt + 1,
            by simp [Expr.eval, BinOp.eval, stB, hA_regs 9 (Or.inr rfl), hr9, hw1, cnt,
                 (by omega : cnt + 1 < 2 ^ w)],
            rfl, rfl, by simp [Expr.size]⟩
        refine ⟨.normal, stC, 14, runs_cond_iff.mpr ⟨1, 10,
            by simp [Expr.eval, BinOp.eval, hA_8, hvin, hw1, (by omega : 0 < 2 ^ w)],
            by simp only [one_ne_zero, ↓reduceIte]
               exact runs_seq_iff.mpr (Or.inr ⟨stB, 5, 4, hs1, hs2, rfl⟩),
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, fun r hr => by simp [stC, stB, Function.update_of_ne (by omega : r ≠ 6),
            Function.update_of_ne (by omega : r ≠ 9), hA_regs r (Or.inl (by omega)), hkr r hr],
          by simp [stC, htake_eq, cnt], ?_, ?_⟩,
          by simp [stC, stB, hA_regs 6 (Or.inl (by omega)), hiReg]⟩
        · rw [htake_eq]; simpa [stC, stB, memB, cnt] using houtL.snoc v
        · intro a ha
          rw [htake_eq, List.length_append, List.length_singleton] at ha
          dsimp only [stC, stB, memB]
          rw [Function.update_of_ne (by omega)]
          exact hfr a (by omega))
  refine runs_seq_triple_le hpass2 rfl ?_
  intro st3 ⟨_, h3_kr, h3_9, h3_outL, h3_fr⟩
  have htakeV : verts.take k = verts := by rw [← hlenV, List.take_length]
  rw [htakeV] at h3_9 h3_outL h3_fr
  have h3_rList : ListAt st3.mem rAddr rList := by
    intro j hj
    have hle : (verts.filter notR).length ≤ k := by rw [← hlenV]; exact List.length_filter_le _ _
    rw [h3_fr (rAddr + j) (Or.elim hdOutR (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
    rw [h1_frame (rAddr + j) (fun u hu =>
      (disjointRange_ne hdLocR (by omega) (by have := hr_lt u hu; omega) (by omega) (by omega)).symm)]
    exact hlistR j hj
  refine runs_seq_triple_le
    (markVerts_triple (w := w) (n := n) (len := kR) (listAddr := rAddr) (locAddr := locAddr)
      (val := 0) (rLen := 2) (rList := 3) (rLoc := 4) (rI := 6) (rU := 7)
      pProg st3 rList (by decide)
      (by rw [h3_kr 2 (by omega), h1_r 2 (by omega)]; simp [startState])
      (by rw [h3_kr 3 (by omega), h1_r 3 (by omega)]; simp [startState])
      (by rw [h3_kr 4 (by omega), h1_r 4 (by omega)]; simp [startState])
      hlenR hr_lt h3_rList hdLocR hwR hwLoc (by omega) hw1) rfl ?_
  intro st4 ⟨h4_clear, h4_frame, h4_keep⟩
  have h4_9 : st4.regs 9 = (verts.filter notR).length := by
    rw [h4_keep 9 (by omega) (by omega)]; exact h3_9
  refine runs_ret_le (v := (verts.filter notR).length) (by simp [Expr.eval, h4_9]) ?_ ?_
  · dsimp only [setDiffContract, Outcome.value, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    have hreadV : readList mem vertsAddr k = verts := by rw [← hlenV]; exact readList_eq_of_listAt hlistV
    have hreadR : readList mem rAddr kR = rList := by rw [← hlenR]; exact readList_eq_of_listAt hlistR
    simp only [hreadV, hreadR]
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj
      have hj' : j < (verts.filter notR).length := hj
      have hj_k : j < k := by have := List.length_filter_le notR verts; omega
      rw [h4_frame (outRestAddr + j) (fun u hu =>
        (disjointRange_ne hdLocOut (by omega) (by have := hr_lt u hu; omega) (by omega) (by omega)).symm)]
      exact h3_outL j hj'
    · intro a ha
      by_cases hmemR : ∃ u ∈ rList, a = locAddr + u
      · rcases hmemR with ⟨u, hu, rfl⟩
        rw [h4_clear u hu, hloc0 u (hr_lt u hu)]
      · push Not at hmemR
        rw [h4_frame a hmemR]
        have hle : (verts.filter notR).length ≤ k := by rw [← hlenV]; exact List.length_filter_le _ _
        rw [h3_fr a (by omega)]
        exact h1_frame a hmemR
  · simp only [setDiffContract, setDiffCost, Expr.size, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    omega

end MinCostFlow.ExpanderDecomp
