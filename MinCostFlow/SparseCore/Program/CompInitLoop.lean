module

public import MinCostFlow.SparseCore.Program.CompInitEdgeful
import WordRAM.Tactic

/-!
# Outer Component-Discovery Loop Verification (`CompInitLoop`)

Proves `compInitLoop_runs`, verifying `compInitLoop` across all vertices of `G₀`:
* Visited vertices are skipped in `O(1)`.
* Unvisited isolated vertices (`incHead[extToInt[v]] = 0`) record `{v}` in `O(1)` with zero
  BFS/window calls.
* Unvisited edgeful vertices delegate to `compInitEdgeful_runs`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- Execution, invariant preservation, and exact cost bound of `compInitLoop`.
Isolated components (`m_C = 0`) pay only `O(1)` loop work and zero window cost. -/
theorem compInitLoop_runs {W : LSFWindowImpl} {w k : ℕ} {G₀ : MGraph} {p : Program}
    {mem0 : ℕ → ℕ} {ω : ℕ → Bool}
    (ctx : InitCtx W w k G₀ p mem0)
    (rem i : ℕ) (comps : List (Finset ℕ)) (efIdx : List ℕ)
    (winH : ℕ → ℕ → ℕ) (winX : ℕ → ℕ → LSFConcrete)
    (curHeap : ℕ) (st : State) :
    i ≤ G₀.n → G₀.n - i = rem →
    (∀ u ∈ ctx.vL.take i, ∃ C ∈ comps, u ∈ C) →
    InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
      ctx.vCap0 G₀.n G₀.m st.regs →
    st.regs 32 = curHeap → st.regs 33 = comps.length → st.regs 34 = efIdx.length → st.regs 35 = i →
    InitMemInv ctx st.mem curHeap comps efIdx winH winX →
    ∃ st' curHeap' comps' efIdx' winH' winX' c_loop,
      Runs w p ω (compInitLoop ctx.bBfs ctx.bDgInit (ctx.bWin + W.initOff)) st .normal st' c_loop ∧
      InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
        ctx.vCap0 G₀.n G₀.m st'.regs ∧
      st'.regs 32 = curHeap' ∧ st'.regs 33 = comps'.length ∧ st'.regs 34 = efIdx'.length ∧
      (∀ C, C ∈ components G₀ ↔ C ∈ comps') ∧
      InitMemInv ctx st'.mem curHeap' comps' efIdx' winH' winX' ∧
      c_loop ≤ 120 * rem +
        ((edgefulComps G₀) \ comps.toFinset).sum (fun C =>
          let nC := (compGraph G₀ C).n
          let mC := (compGraph G₀ C).m
          W.winCost k ctx.L_w nC mC + 250 * nC + 850 * mC + 450) + 6 := by
  classical
  have hw1 : 1 < 2 ^ w := by have := ctx.hw16; omega
  have hsp_lt := ctx.hsp_lt
  have hstat_lt : ctx.b + compStaticSize ctx.vCap ctx.eCap ctx.L_w < 2 ^ w := by
    dsimp [InitCtx.heap0, compTablesEnd, compHandlesBase] at hsp_lt; omega
  have hG₀_n_le : G₀.n ≤ ctx.vCap0 := by
    have hsub : G₀.V ⊆ Finset.range ctx.vCap0 := fun v hv => Finset.mem_range.mpr (ctx.hdg.2.1 v hv)
    simpa [MGraph.n] using Finset.card_le_card hsub
  have hg0_w : ctx.g0Ptr + dynGraphSize ctx.vCap0 ctx.eCap0 < 2 ^ w := by
    have := ctx.hg0_le; dsimp [compStaticSize, compGhostSize, compHdrSize] at hstat_lt; omega
  induction rem generalizing i comps efIdx winH winX curHeap st with
  | zero =>
    intro hi hrem hcov hR hr32 hr33 hr34 hr35 hInv
    have hieq : i = G₀.n := by omega
    subst hieq
    have hall : ∀ C, C ∈ components G₀ ↔ C ∈ comps := fun C =>
      ⟨fun hC => by
        obtain ⟨u, huC⟩ := compGraph_nonempty hC
        have huG : u ∈ G₀.V := by
          rcases Finset.mem_image.mp hC with ⟨w', _, rfl⟩; exact (mem_compOf_iff.mp huC).1
        have huTake : u ∈ ctx.vL.take G₀.n := by
          rw [← ctx.hvL_len, List.take_length]; exact (ctx.hvL_mem u).mpr huG
        obtain ⟨C', hC'm, huC'⟩ := hcov u huTake
        have hEq : C' = C := by
          by_contra hne
          exact Finset.disjoint_left.mp
            (comp_disjoint_of_ne G₀ (hInv.2.2.2.2.2.1 C' hC'm) hC hne) huC' huC
        exact hEq ▸ hC'm,
       hInv.2.2.2.2.2.1 C⟩
    refine ⟨st, curHeap, comps, efIdx, winH, winX, 4,
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hR.r11, hr35], rfl, rfl, by simp [Expr.size]⟩),
      hR, hr32, hr33, hr34, hall, hInv, by omega⟩
  | succ rem ih =>
    intro hi hrem hcov hR hr32 hr33 hr34 hr35 hInv
    have hilt : i < G₀.n := by omega
    have hilt_vL : i < ctx.vL.length := ctx.hvL_len.symm ▸ hilt
    set v := ctx.vL[i]
    have hvG : v ∈ G₀.V := (ctx.hvL_mem v).mp (List.getElem_mem hilt_vL)
    have hv_lt0 : v < ctx.vCap0 := ctx.hdg.2.1 v hvG
    have hv_lt : v < ctx.vCap := lt_of_lt_of_le hv_lt0 ctx.hvCap_le
    have hV_m : st.mem (dgVListBase ctx.g0Ptr ctx.vCap0 + i) = v :=
      (hInv.1 _ (by have hgl := ctx.hg0_le; dsimp [dgVListBase, dynGraphSize] at hgl ⊢; omega)).trans
        (ctx.hvL_at i hilt_vL)
    set visBase := compTablesEnd ctx.b ctx.vCap ctx.eCap ctx.L_w G₀.m k
    have hvis_v : st.mem (visBase + v) = if (∃ C ∈ comps, v ∈ C) then 1 else 0 :=
      hInv.2.2.2.2.2.2.2.2.2.1 v hv_lt
    let st1 : State := { st with regs := Function.update st.regs 37 v }
    let st2 : State := { st1 with regs := Function.update st1.regs 35 (i + 1) }
    let st3 : State := { st2 with regs := Function.update st2.regs 38 (if (∃ C ∈ comps, v ∈ C) then 1 else 0) }
    have hvL_w : dgVListBase ctx.g0Ptr ctx.vCap0 + i < 2 ^ w := by
      dsimp [dgVListBase, dynGraphSize] at hg0_w ⊢; omega
    have hvis_w : visBase + v < 2 ^ w := by dsimp [visBase, InitCtx.heap0] at hsp_lt ⊢; omega
    have hp1 : Runs w p ω (.assign 37 (.load (.bin .add (.reg 13) (.reg 35)))) st .normal st1 5 :=
      runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq
        (by simp [Expr.eval, BinOp.eval, hR.r13, hr35, hvL_w]) hV_m, rfl, rfl, by simp [Expr.size]⟩
    have hp2 : Runs w p ω (.assign 35 (.bin .add (.reg 35) (.const 1))) st1 .normal st2 4 :=
      runs_assign_iff.mpr ⟨i + 1,
        by simp [st1, Expr.eval, BinOp.eval, hr35, hw1, show i + 1 < 2 ^ w by dsimp [InitCtx.heap0] at hsp_lt; omega],
        rfl, rfl, by simp [Expr.size]⟩
    have hp3 : Runs w p ω (.assign 38 (.load (.bin .add (.reg 29) (.reg 37)))) st2 .normal st3 5 :=
      runs_assign_iff.mpr ⟨if (∃ C ∈ comps, v ∈ C) then 1 else 0,
        Expr.eval_load_of_eq (by simp [st2, st1, Expr.eval, BinOp.eval, hR.r29, visBase, hvis_w]) hvis_v,
        rfl, rfl, by simp [Expr.size]⟩
    have hR3 : InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
        ctx.vCap0 G₀.n G₀.m st3.regs :=
      ((hR.update_mut (by omega)).update_mut (by omega)).update_mut (by omega)
    set innerCond := Stmt.cond (.reg 40)
      (compInitEdgefulStmt ctx.bBfs ctx.bDgInit (ctx.bWin + W.initOff)) compInitIsoStmt
    set outerCond := Stmt.cond (.reg 38) .nop
      (.assign 39 (.load (.bin .add (.reg 14) (.reg 37))) ;;
       .assign 40 (.load (.bin .add (.reg 15) (.reg 39))) ;;
       innerCond)
    by_cases hvis : ∃ C ∈ comps, v ∈ C
    · have hcond : Runs w p ω outerCond st3 .normal st3 3 :=
        runs_cond_iff.mpr ⟨1, 1, by simp [st3, Expr.eval, hvis],
          by simpa using (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩ : Runs w p ω .nop st3 .normal st3 1),
          by simp [Expr.size]⟩
      have hbody : Runs w p ω
          (.assign 37 (.load (.bin .add (.reg 13) (.reg 35))) ;;
           .assign 35 (.bin .add (.reg 35) (.const 1)) ;;
           .assign 38 (.load (.bin .add (.reg 29) (.reg 37))) ;;
           outerCond) st .normal st3 20 :=
        runs_seq_iff.mpr (Or.inr ⟨st1, 5, 14, hp1,
          runs_seq_iff.mpr (Or.inr ⟨st2, 4, 9, hp2,
            runs_seq_iff.mpr (Or.inr ⟨st3, 5, 3, hp3, hcond, rfl⟩), rfl⟩), rfl⟩)
      have hcov' : ∀ u ∈ ctx.vL.take (i + 1), ∃ C ∈ comps, u ∈ C := fun u hu => by
        rw [List.take_succ_eq_append_getElem hilt_vL, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu1 | rfl
        · exact hcov u hu1
        · exact hvis
      obtain ⟨st', curHeap', comps', efIdx', winH', winX', c_rec, hrun_r, hR', hr32', hr33', hr34',
        hall', hInv', hcr⟩ := ih (i + 1) comps efIdx winH winX curHeap st3 (by omega) (by omega)
        hcov' hR3 (by simp [st3, st2, st1, hr32]) (by simp [st3, st2, st1, hr33])
        (by simp [st3, st2, st1, hr34]) (by simp [st3, st2]) hInv
      refine ⟨st', curHeap', comps', efIdx', winH', winX', 3 + 20 + c_rec + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st3, 20, c_rec,
          by simp [Expr.eval, BinOp.eval, hr35, hR.r11, hilt, hw1], by decide,
          hbody, hrun_r, by simp [Expr.size]⟩)),
        hR', hr32', hr33', hr34', hall', hInv', by omega⟩
    · set C := compOf G₀ v
      have hC_mem : C ∈ components G₀ := Finset.mem_image.mpr ⟨v, hvG, rfl⟩
      have hvC : v ∈ C := self_mem_compOf hvG
      have hC_not : C ∉ comps := fun hCm => hvis ⟨C, hCm, hvC⟩
      have hc_lt0 : comps.length < ctx.vCap0 := by
        have h1 : (comps ++ [C]).length ≤ G₀.n := init_numComps_le
          (List.nodup_append.mpr ⟨hInv.2.2.2.2.1, List.nodup_singleton _, fun x hx y hy => by
            simp only [List.mem_singleton] at hy; subst hy; exact fun h => hC_not (h ▸ hx)⟩)
          (fun X hX => by
            rcases List.mem_append.mp hX with h1 | h2
            · exact hInv.2.2.2.2.2.1 X h1
            · simp only [List.mem_singleton] at h2; exact h2 ▸ hC_mem)
        simp at h1; omega
      have hc_lt : comps.length < ctx.vCap := lt_of_lt_of_le hc_lt0 ctx.hvCap_le
      set sv := mem0 (dgExtToIntBase ctx.g0Ptr ctx.vCap0 + v)
      have hsv_lt0 : sv < ctx.vCap0 := ctx.hdg.2.1 sv (ctx.hdg.2.2.2.2.2.2.2.2.2.1 v hvG).1
      set ihd := mem0 (dgIncHeadBase ctx.g0Ptr ctx.vCap0 + sv)
      have hihd_w : ihd < 2 ^ w := by
        obtain ⟨incL, hincFull⟩ := ctx.hdg.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have hDLL := (hincFull sv hsv_lt0).1
        dsimp only [ihd]; rw [hDLL.2.2.1]
        cases hL : incL sv with
        | nil => simp
        | cons x xs =>
          have hx := hDLL.2.1 x (by rw [hL]; exact List.mem_cons_self)
          simp only
          have := hg0_w; dsimp [dynGraphSize] at this; omega
      have hsv_st : st3.mem (dgExtToIntBase ctx.g0Ptr ctx.vCap0 + v) = sv :=
        hInv.1 _ (by have hgl := ctx.hg0_le; dsimp [dgExtToIntBase, dynGraphSize] at hgl ⊢; omega)
      have hihd_st : st3.mem (dgIncHeadBase ctx.g0Ptr ctx.vCap0 + sv) = ihd :=
        hInv.1 _ (by have hgl := ctx.hg0_le; dsimp [dgIncHeadBase, dynGraphSize] at hgl ⊢; omega)
      let st4 : State := { st3 with regs := Function.update st3.regs 39 sv }
      let st5 : State := { st4 with regs := Function.update st4.regs 40 ihd }
      have hp4 : Runs w p ω (.assign 39 (.load (.bin .add (.reg 14) (.reg 37)))) st3 .normal st4 5 :=
        runs_assign_iff.mpr ⟨sv, Expr.eval_load_of_eq (by
          have : dgExtToIntBase ctx.g0Ptr ctx.vCap0 + v < 2 ^ w := by
            dsimp [dgExtToIntBase, dynGraphSize] at hg0_w ⊢; omega
          simp [st3, st2, st1, Expr.eval, BinOp.eval, hR.r14, this]) hsv_st,
          rfl, rfl, by simp [Expr.size]⟩
      have hp5 : Runs w p ω (.assign 40 (.load (.bin .add (.reg 15) (.reg 39)))) st4 .normal st5 5 :=
        runs_assign_iff.mpr ⟨ihd, Expr.eval_load_of_eq (by
          have : dgIncHeadBase ctx.g0Ptr ctx.vCap0 + sv < 2 ^ w := by
            dsimp [dgIncHeadBase, dynGraphSize] at hg0_w ⊢; omega
          simp [st4, st3, st2, st1, Expr.eval, BinOp.eval, hR.r15, this]) hihd_st,
          rfl, rfl, by simp [Expr.size]⟩
      have hR5 : InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
          ctx.vCap0 G₀.n G₀.m st5.regs :=
        (hR3.update_mut (by omega)).update_mut (by omega)
      by_cases hihd0 : ihd = 0
      · -- ISOLATED COMPONENT: `C = {v}`, `(compGraph G₀ C).m = 0`
        obtain ⟨hC_sing, hm0_C⟩ := (incHead_eq_zero_iff_iso ctx.hdg hvG).mp hihd0
        change C = {v} at hC_sing
        change (compGraph G₀ C).m = 0 at hm0_C
        let m1 := Function.update st5.mem (visBase + v) 1
        let m2 := Function.update m1 (compVCompBase ctx.b + v) comps.length
        let m3 := Function.update m2 (compEdgefulBase ctx.b ctx.vCap + comps.length) 0
        let m4 := Function.update m3 (compN0Base ctx.b ctx.vCap + comps.length) 1
        let m5 := Function.update m4 (compM0Base ctx.b ctx.vCap + comps.length) 0
        let r5 := Function.update st5.regs 33 (comps.length + 1)
        have hc_w : comps.length < 2 ^ w := by dsimp [compStaticSize, compGhostSize, compHdrSize] at hstat_lt; omega
        have hs1 : Runs w p ω (.store (.bin .add (.reg 29) (.reg 37)) (.const 1)) st5 .normal { st5 with mem := m1 } 5 :=
          runs_store_iff.mpr ⟨visBase + v, 1,
            by simp [st5, st4, st3, st2, st1, Expr.eval, BinOp.eval, hR.r29, visBase, hvis_w],
            by simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
        have hs2 : Runs w p ω (.store (.bin .add (.reg 16) (.reg 37)) (.reg 33))
            { st5 with mem := m1 } .normal { st5 with mem := m2 } 5 :=
          runs_store_iff.mpr ⟨compVCompBase ctx.b + v, comps.length,
            by simp [st5, st4, st3, st2, st1, Expr.eval, BinOp.eval, hR.r16,
                show compVCompBase ctx.b + v < 2 ^ w by dsimp [compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hstat_lt ⊢; omega],
            by simp [st5, st4, st3, st2, st1, Expr.eval, hr33], rfl, rfl, by simp [Expr.size]⟩
        have hs3 : Runs w p ω (.store (.bin .add (.reg 17) (.reg 33)) (.const 0))
            { st5 with mem := m2 } .normal { st5 with mem := m3 } 5 :=
          runs_store_iff.mpr ⟨compEdgefulBase ctx.b ctx.vCap + comps.length, 0,
            by simp [st5, st4, st3, st2, st1, Expr.eval, BinOp.eval, hR.r17, hr33,
                show compEdgefulBase ctx.b ctx.vCap + comps.length < 2 ^ w by
                  dsimp [compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hstat_lt ⊢; omega],
            by simp [Expr.eval, show (0 : ℕ) < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
        have hs4 : Runs w p ω (.store (.bin .add (.reg 19) (.reg 33)) (.const 1))
            { st5 with mem := m3 } .normal { st5 with mem := m4 } 5 :=
          runs_store_iff.mpr ⟨compN0Base ctx.b ctx.vCap + comps.length, 1,
            by simp [st5, st4, st3, st2, st1, Expr.eval, BinOp.eval, hR.r19, hr33,
                show compN0Base ctx.b ctx.vCap + comps.length < 2 ^ w by
                  dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hstat_lt ⊢; omega],
            by simp [Expr.eval, hw1], rfl, rfl, by simp [Expr.size]⟩
        have hs5 : Runs w p ω (.store (.bin .add (.reg 20) (.reg 33)) (.const 0))
            { st5 with mem := m4 } .normal { st5 with mem := m5 } 5 :=
          runs_store_iff.mpr ⟨compM0Base ctx.b ctx.vCap + comps.length, 0,
            by simp [st5, st4, st3, st2, st1, Expr.eval, BinOp.eval, hR.r20, hr33,
                show compM0Base ctx.b ctx.vCap + comps.length < 2 ^ w by
                  dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hstat_lt ⊢; omega],
            by simp [Expr.eval, show (0 : ℕ) < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
        have hs6 : Runs w p ω (.assign 33 (.bin .add (.reg 33) (.const 1)))
            { st5 with mem := m5 } .normal { mem := m5, regs := r5, pos := st5.pos } 4 :=
          runs_assign_iff.mpr ⟨comps.length + 1,
            by simp [st5, st4, st3, st2, st1, Expr.eval, BinOp.eval, hr33, hw1,
              show comps.length + 1 < 2 ^ w by dsimp [compStaticSize, compGhostSize, compHdrSize] at hstat_lt; omega],
            rfl, rfl, by simp [Expr.size]⟩
        have hiso_blk : Runs w p ω compInitIsoStmt st5 .normal { mem := m5, regs := r5, pos := st5.pos } 34 :=
          runs_seq_iff.mpr (Or.inr ⟨_, 5, 28, hs1,
            runs_seq_iff.mpr (Or.inr ⟨_, 5, 22, hs2,
              runs_seq_iff.mpr (Or.inr ⟨_, 5, 16, hs3,
                runs_seq_iff.mpr (Or.inr ⟨_, 5, 10, hs4,
                  runs_seq_iff.mpr (Or.inr ⟨_, 5, 4, hs5, hs6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
        have hcond2 : Runs w p ω innerCond st5 .normal { mem := m5, regs := r5, pos := st5.pos } 36 :=
          runs_cond_iff.mpr ⟨0, 34, by simp [st5, Expr.eval, hihd0], by simpa using hiso_blk, by simp [Expr.size]⟩
        have hcond1 : Runs w p ω outerCond st3 .normal { mem := m5, regs := r5, pos := st5.pos } 50 :=
          runs_cond_iff.mpr ⟨0, 48, by simp [st3, Expr.eval, hvis],
            by simpa using (runs_seq_iff.mpr (Or.inr ⟨st4, 5, 42, hp4,
              runs_seq_iff.mpr (Or.inr ⟨st5, 5, 36, hp5, hcond2, rfl⟩), rfl⟩) :
              Runs w p ω _ st3 .normal { mem := m5, regs := r5, pos := st5.pos } 48),
            by simp [Expr.size]⟩
        have hbody : Runs w p ω
            (.assign 37 (.load (.bin .add (.reg 13) (.reg 35))) ;;
             .assign 35 (.bin .add (.reg 35) (.const 1)) ;;
             .assign 38 (.load (.bin .add (.reg 29) (.reg 37))) ;;
             outerCond) st .normal { mem := m5, regs := r5, pos := st5.pos } 67 :=
          runs_seq_iff.mpr (Or.inr ⟨st1, 5, 61, hp1,
            runs_seq_iff.mpr (Or.inr ⟨st2, 4, 56, hp2,
              runs_seq_iff.mpr (Or.inr ⟨st3, 5, 50, hp3, hcond1, rfl⟩), rfl⟩), rfl⟩)
        have hm5_eq : ∀ a, a ≠ visBase + v → a ≠ compVCompBase ctx.b + v →
            a ≠ compEdgefulBase ctx.b ctx.vCap + comps.length →
            a ≠ compN0Base ctx.b ctx.vCap + comps.length →
            a ≠ compM0Base ctx.b ctx.vCap + comps.length →
            m5 a = st.mem a := fun a h1 h2 h3 h4 h5 => by
          dsimp only [m5, m4, m3, m2, m1, st5, st4, st3, st2, st1]
          rw [Function.update_of_ne h5, Function.update_of_ne h4, Function.update_of_ne h3,
            Function.update_of_ne h2, Function.update_of_ne h1]
        have h5_bounds : ∀ a, (a < ctx.b + compHdrSize ∨
            (compEdgeC1Base ctx.b ctx.vCap ≤ a ∧ a < visBase) ∨ ctx.heap0 ≤ a) →
            m5 a = st.mem a := fun a ha => hm5_eq a
          (by dsimp [visBase, InitCtx.heap0, compTablesEnd, compHandlesBase, compEdgeC1Base, compM0Base,
              compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
              compGhostSize, compHdrSize] at ha ⊢; omega)
          (by dsimp [visBase, InitCtx.heap0, compTablesEnd, compHandlesBase, compEdgeC1Base, compM0Base,
              compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
              compGhostSize, compHdrSize] at ha ⊢; omega)
          (by dsimp [visBase, InitCtx.heap0, compTablesEnd, compHandlesBase, compEdgeC1Base, compM0Base,
              compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
              compGhostSize, compHdrSize] at ha ⊢; omega)
          (by dsimp [visBase, InitCtx.heap0, compTablesEnd, compHandlesBase, compEdgeC1Base, compM0Base,
              compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
              compGhostSize, compHdrSize] at ha ⊢; omega)
          (by dsimp [visBase, InitCtx.heap0, compTablesEnd, compHandlesBase, compEdgeC1Base, compM0Base,
              compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
              compGhostSize, compHdrSize] at ha ⊢; omega)
        have hInv' : InitMemInv ctx m5 curHeap (comps ++ [C]) efIdx winH winX := by
          have hC_nd : (comps ++ [C]).Nodup := List.nodup_append.mpr
            ⟨hInv.2.2.2.2.1, List.nodup_singleton _, fun x hx y hy => by
              simp only [List.mem_singleton] at hy; subst hy; exact fun h => hC_not (h ▸ hx)⟩
          have hC_sub' : ∀ X ∈ comps ++ [C], X ∈ components G₀ := fun X hX => by
            rcases List.mem_append.mp hX with h1 | h2
            · exact hInv.2.2.2.2.2.1 X h1
            · simp only [List.mem_singleton] at h2; exact h2 ▸ hC_mem
          refine ⟨fun a ha => (h5_bounds a (Or.inl (by omega))).trans (hInv.1 a ha), ?_, ?_, ?_,
            hC_nd, hC_sub', hInv.2.2.2.2.2.2.1, fun idx hidx => by have := hInv.2.2.2.2.2.2.2.1 idx hidx; simp; omega,
            ?_, ?_, ?_, ?_, hInv.2.2.2.2.2.2.2.2.2.2.2.2.1, hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_, ?_⟩
          · rcases hInv.2.1 with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
              h15, h16, h17, h18, h19, h20⟩
            have hh : ∀ off < compHdrSize, m5 (ctx.b + off) = st.mem (ctx.b + off) := fun off hoff =>
              h5_bounds _ (Or.inl (by omega))
            exact ⟨(hh _ (by decide)).trans h0, (hh _ (by decide)).trans h1, (hh _ (by decide)).trans h2,
              (hh _ (by decide)).trans h3, (hh _ (by decide)).trans h4, (hh _ (by decide)).trans h5,
              (hh _ (by decide)).trans h6, (hh _ (by decide)).trans h7, (hh _ (by decide)).trans h8,
              (hh _ (by decide)).trans h9, (hh _ (by decide)).trans h10, (hh _ (by decide)).trans h11,
              (hh _ (by decide)).trans h12, (hh _ (by decide)).trans h13, (hh _ (by decide)).trans h14,
              (hh _ (by decide)).trans h15, (hh _ (by decide)).trans h16, (hh _ (by decide)).trans h17,
              (hh _ (by decide)).trans h18, (hh _ (by decide)).trans h19, (hh _ (by decide)).trans h20⟩
          · intro a ha1 ha2
            exact (h5_bounds a (Or.inr (Or.inl ⟨by dsimp [compIsCrossBase, compEdgeC2Base, compEdgeC1Base] at ha1 ⊢; omega,
              by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compOneLimbBase, compTouchMarkBase,
                compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base,
                compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize] at ha2 ⊢; omega⟩))).trans
              (hInv.2.2.1 a ha1 ha2)
          · have hOneEnd := compOneLimb_end_eq ctx.b ctx.vCap ctx.eCap ctx.L_w
            have hLw1 := ctx.hLw
            refine ⟨(h5_bounds _ (Or.inr (Or.inl ⟨by dsimp [compOneLimbBase, compTouchMarkBase, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base]; omega,
              by dsimp [visBase, compTablesEnd]; omega⟩))).trans hInv.2.2.2.1.1,
              fun t ht1 ht2 => (h5_bounds _ (Or.inr (Or.inl ⟨by dsimp [compOneLimbBase, compTouchMarkBase, compGhostBase, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base]; omega,
              by dsimp [visBase, compTablesEnd]; omega⟩))).trans (hInv.2.2.2.1.2 t ht1 ht2)⟩
          · intro idx hi
            simp only [List.length_append, List.length_singleton] at hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
            · rw [List.getElem_append_left hi']; exact hInv.2.2.2.2.2.2.2.2.1 idx hi'
            · simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
              exact ⟨fun h => by omega, fun h => by have := hInv.2.2.2.2.2.2.2.1 _ h; omega⟩
          · intro u hu
            by_cases huv : u = v
            · subst huv
              have : m5 (visBase + v) = 1 := by
                dsimp only [m5, m4, m3, m2, m1]
                rw [Function.update_of_ne (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega),
                  Function.update_of_ne (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega),
                  Function.update_of_ne (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega),
                  Function.update_of_ne (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compGhostSize, compHdrSize]; omega),
                  Function.update_self]
              rw [this]; simp [hvC]
            · have : m5 (visBase + u) = st.mem (visBase + u) := hm5_eq _ (by omega)
                (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compGhostSize, compHdrSize]; omega)
                (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega)
                (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega)
                (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega)
              rw [this, hInv.2.2.2.2.2.2.2.2.2.1 u hu]
              have huNotC : u ∉ C := by rw [hC_sing, Finset.mem_singleton]; exact huv
              simp [huNotC]
          · intro idx hi
            simp only [List.length_append, List.length_singleton] at hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
            · rw [List.getElem_append_left hi']
              have hprev := hInv.2.2.2.2.2.2.2.2.2.2.1 idx hi'
              refine ⟨fun u hu => ?_, ?_, ?_, ?_, fun e he => ?_⟩
              · have huv : u ≠ v := fun h => hvis ⟨comps[idx], List.getElem_mem hi', h ▸ hu⟩
                have hu_lt : u < ctx.vCap := lt_of_lt_of_le (ctx.hdg.2.1 u (by
                  rcases Finset.mem_image.mp (hInv.2.2.2.2.2.1 _ (List.getElem_mem hi')) with ⟨w', _, hEq⟩
                  rw [← hEq] at hu; exact (mem_compOf_iff.mp hu).1)) ctx.hvCap_le
                exact (hm5_eq _ (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compGhostSize, compHdrSize]; omega)
                  (by omega)
                  (by dsimp [compEdgefulBase, compVCompBase]; omega)
                  (by dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
                  (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)).trans (hprev.1 u hu)
              · exact (hm5_eq _ (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega)
                  (by dsimp [compEdgefulBase, compVCompBase]; omega) (by omega)
                  (by dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega)
                  (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega)).trans hprev.2.1
              · exact (hm5_eq _ (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega)
                  (by dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
                  (by dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega) (by omega)
                  (by dsimp [compM0Base, compN0Base]; omega)).trans hprev.2.2.1
              · exact (hm5_eq _ (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega)
                  (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
                  (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega)
                  (by dsimp [compM0Base, compN0Base]; omega) (by omega)).trans hprev.2.2.2.1
              · have he_lt : e < ctx.eCap := lt_of_lt_of_le (ctx.hdg.2.2.1 e (Finset.filter_subset _ _ he)) ctx.heCap_le
                exact ⟨(h5_bounds _ (Or.inr (Or.inl ⟨by omega, by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega⟩))).trans (hprev.2.2.2.2 e he).1,
                  (h5_bounds _ (Or.inr (Or.inl ⟨by dsimp [compEdgeC2Base]; omega, by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega⟩))).trans (hprev.2.2.2.2 e he).2⟩
            · simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
              refine ⟨fun u hu => ?_, ?_, ?_, ?_, fun e he => ?_⟩
              · rw [hC_sing, Finset.mem_singleton] at hu; subst hu
                dsimp only [m5, m4, m3, m2]
                rw [Function.update_of_ne (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega),
                  Function.update_of_ne (by dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega),
                  Function.update_of_ne (by dsimp [compEdgefulBase, compVCompBase]; omega),
                  Function.update_self]
              · simp only [hm0_C, Nat.not_le.mpr Nat.zero_lt_one, ↓reduceIte]
                dsimp only [m5, m4, m3]
                rw [Function.update_of_ne (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega),
                  Function.update_of_ne (by dsimp [compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega),
                  Function.update_self]
              · have hn1 : (compGraph G₀ C).n = 1 := by simp [compGraph, MGraph.n, hC_sing]
                rw [hn1]; dsimp only [m5, m4]
                rw [Function.update_of_ne (by dsimp [compM0Base, compN0Base]; omega), Function.update_self]
              · rw [hm0_C]; exact Function.update_self _ _ _
              · exfalso; have hpos : 0 < (compGraph G₀ C).m := Finset.card_pos.mpr ⟨e, he⟩; omega
          · intro r hr
            obtain ⟨hi, hefi, hwj⟩ := hInv.2.2.2.2.2.2.2.2.2.2.2.1 r hr
            refine ⟨by simp; omega, ?_, fun j hj => ?_⟩
            · exact (hm5_eq _ (by dsimp [visBase, compTablesEnd, compHandlesBase, compStaticSize, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compGhostSize, compHdrSize]; omega)
                (by dsimp [compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega)
                (by dsimp [compEdgefulIdxBase, compEdgefulBase]; omega)
                (by dsimp [compN0Base, compEdgefulIdxBase]; omega)
                (by dsimp [compM0Base, compN0Base, compEdgefulIdxBase]; omega)).trans hefi
            · obtain ⟨hm_h, hrep_j, hvj, hej, hLwj, hge_j, hle_j, hft_j⟩ := hwj j hj
              rw [List.getElem_append_left hi]
              have hidx_lt : r * k + j < G₀.m * k := by
                have hef_le := le_trans (init_numEdgeful_le hInv.2.2.2.2.1
                  hInv.2.2.2.2.2.2.1 hInv.2.2.2.2.2.2.2.1 hInv.2.2.2.2.2.2.2.2.1)
                  (init_sum_m_le fun X hX => hInv.2.2.2.2.2.1 X (List.mem_toFinset.mp (Finset.mem_filter.mp hX).1))
                calc r * k + j < r * k + k := Nat.add_lt_add_left hj _
                  _ = (r + 1) * k := by ring
                  _ ≤ G₀.m * k := Nat.mul_le_mul_right k (by omega)
              refine ⟨(h5_bounds _ (Or.inr (Or.inl ⟨by dsimp [compHandlesBase, compStaticSize, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega,
                by dsimp [visBase, compTablesEnd]; omega⟩))).trans hm_h, ?_, hvj, hej, hLwj, hge_j, hle_j, hft_j⟩
              exact ((lsfRep_local W.h _ _ _ _ _ fun a ha =>
                (h5_bounds a (Or.inr (Or.inr (hft_j a ha).1))).symm).1 hrep_j)
          · have hfilt_eq : ((comps ++ [C]).toFinset.filter fun X => 1 ≤ (compGraph G₀ X).m) =
                (comps.toFinset.filter fun X => 1 ≤ (compGraph G₀ X).m) := by
              ext X; simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
                Finset.mem_filter, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
              constructor
              · rintro ⟨h1 | rfl, hm⟩; exact ⟨h1, hm⟩; omega
              · rintro ⟨h1, hm⟩; exact ⟨Or.inl h1, hm⟩
            rw [hfilt_eq]; exact hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          · intro a ha
            exact (h5_bounds a (Or.inr (Or.inr (le_trans hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ha)))).trans
              (hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 a ha)
        have hcov' : ∀ u ∈ ctx.vL.take (i + 1), ∃ X ∈ comps ++ [C], u ∈ X := fun u hu => by
          rw [List.take_succ_eq_append_getElem hilt_vL, List.mem_append, List.mem_singleton] at hu
          rcases hu with hu1 | rfl
          · obtain ⟨X, hXm, huX⟩ := hcov u hu1; exact ⟨X, List.mem_append_left _ hXm, huX⟩
          · exact ⟨C, List.mem_append_right _ List.mem_cons_self, hvC⟩
        have hR5' : InitRegsOK ctx.g0Ptr ctx.lenArr W.L_in W.P_fp k ctx.L_w ctx.vCap ctx.eCap ctx.b
            ctx.vCap0 G₀.n G₀.m r5 := hR5.update_mut (by omega)
        obtain ⟨st', curHeap', comps', efIdx', winH', winX', c_rec, hrun_r, hR', hr32', hr33', hr34',
          hall', hInvF, hcr⟩ := ih (i + 1) (comps ++ [C]) efIdx winH winX curHeap
          { mem := m5, regs := r5, pos := st5.pos } (by omega) (by omega) hcov' hR5'
          (by simp [r5, st5, st4, st3, st2, st1, hr32]) (by simp [r5])
          (by simp [r5, st5, st4, st3, st2, st1, hr34]) (by simp [r5, st5, st4, st3, st2]) hInv'
        have hsdiff_eq : edgefulComps G₀ \ (comps ++ [C]).toFinset = edgefulComps G₀ \ comps.toFinset := by
          ext X; simp only [Finset.mem_sdiff, List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
            Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false, edgefulComps, Finset.mem_filter]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inl h)⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩; refine ⟨⟨h1, h2⟩, fun h => ?_⟩
            rcases h with h | rfl; exact h3 h; omega
        rw [hsdiff_eq] at hcr
        refine ⟨st', curHeap', comps', efIdx', winH', winX', 3 + 67 + c_rec + 1,
          runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, { mem := m5, regs := r5, pos := st5.pos }, 67, c_rec,
            by simp [Expr.eval, BinOp.eval, hr35, hR.r11, hilt, hw1], by decide,
            hbody, hrun_r, by simp [Expr.size]⟩)),
          hR', hr32', hr33', hr34', hall', hInvF, by omega⟩
      · -- EDGEFUL COMPONENT: delegate to `compInitEdgeful_runs`
        have hmC_pos : 1 ≤ (compGraph G₀ C).m := by
          by_contra hlt
          have hm0 : (compGraph G₀ C).m = 0 := by omega
          have hC1 : C.card = 1 := isoComp_card_eq_one ctx.hG₀ hC_mem hm0
          have hCsing : C = {v} := Finset.eq_singleton_iff_unique_mem.mpr
            ⟨hvC, fun x hx => by
              obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hC1
              have hvy : v = y := Finset.mem_singleton.mp (hy ▸ hvC)
              have hxy : x = y := Finset.mem_singleton.mp (hy ▸ hx)
              exact hxy.trans hvy.symm⟩
          exact hihd0 ((incHead_eq_zero_iff_iso ctx.hdg hvG).mpr ⟨hCsing, hm0⟩)
        obtain ⟨st16, endHeap, winH', winX', c_ef, hef_blk, hR16, hr32_16, hr33_16, hr34_16, hr35_16,
          hInv', hcef⟩ := compInitEdgeful_runs (ω := ω) (iNext := i + 1) ctx hvG hvis hmC_pos hc_lt0 hR5
          (by simp [st5, st4, st3, st2, st1, hr32]) (by simp [st5, st4, st3, st2, st1, hr33])
          (by simp [st5, st4, st3, st2, st1, hr34]) (by simp [st5, st4, st3, st2])
          (by simp [st5, st4, st3, st2, st1]) hInv
        have hcond2 : Runs w p ω innerCond st5 .normal st16 (c_ef + 2) :=
          runs_cond_iff.mpr ⟨ihd, c_ef, by simp [st5, Expr.eval],
            by simpa [hihd0] using hef_blk, by simp [Expr.size]; omega⟩
        have hcond1 : Runs w p ω outerCond st3 .normal st16 (c_ef + 16) :=
          runs_cond_iff.mpr ⟨0, c_ef + 14, by simp [st3, Expr.eval, hvis],
            by simpa using (runs_seq_iff.mpr (Or.inr ⟨st4, 5, c_ef + 8, hp4,
              runs_seq_iff.mpr (Or.inr ⟨st5, 5, c_ef + 2, hp5, hcond2, by omega⟩), by omega⟩) :
              Runs w p ω _ st3 .normal st16 (c_ef + 14)),
            by simp [Expr.size]; omega⟩
        have hbody : Runs w p ω
            (.assign 37 (.load (.bin .add (.reg 13) (.reg 35))) ;;
             .assign 35 (.bin .add (.reg 35) (.const 1)) ;;
             .assign 38 (.load (.bin .add (.reg 29) (.reg 37))) ;;
             outerCond) st .normal st16 (c_ef + 33) :=
          runs_seq_iff.mpr (Or.inr ⟨st1, 5, c_ef + 27, hp1,
            runs_seq_iff.mpr (Or.inr ⟨st2, 4, c_ef + 22, hp2,
              runs_seq_iff.mpr (Or.inr ⟨st3, 5, c_ef + 16, hp3, hcond1, by omega⟩), by omega⟩), by omega⟩)
        have hcov' : ∀ u ∈ ctx.vL.take (i + 1), ∃ X ∈ comps ++ [C], u ∈ X := fun u hu => by
          rw [List.take_succ_eq_append_getElem hilt_vL, List.mem_append, List.mem_singleton] at hu
          rcases hu with hu1 | rfl
          · obtain ⟨X, hXm, huX⟩ := hcov u hu1; exact ⟨X, List.mem_append_left _ hXm, huX⟩
          · exact ⟨C, List.mem_append_right _ List.mem_cons_self, hvC⟩
        obtain ⟨st', curHeap', comps', efIdx', winH_f, winX_f, c_rec, hrun_r, hR', hr32', hr33', hr34',
          hall', hInvF, hcr⟩ := ih (i + 1) (comps ++ [C]) (efIdx ++ [comps.length]) winH' winX' endHeap
          st16 (by omega) (by omega) hcov' hR16 hr32_16 (by simp [hr33_16]) (by simp [hr34_16]) hr35_16 hInv'
        have hC_ef : C ∈ edgefulComps G₀ := Finset.mem_filter.mpr ⟨hC_mem, hmC_pos⟩
        have hsdiff_eq : (edgefulComps G₀ \ comps.toFinset).erase C =
            edgefulComps G₀ \ (comps ++ [C]).toFinset := by
          ext X; simp only [Finset.mem_erase, Finset.mem_sdiff, List.toFinset_append, List.toFinset_cons,
            List.toFinset_nil, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
          tauto
        have hC_in_diff : C ∈ edgefulComps G₀ \ comps.toFinset :=
          Finset.mem_sdiff.mpr ⟨hC_ef, fun h => hC_not (List.mem_toFinset.mp h)⟩
        have hsum_split := Finset.add_sum_erase (edgefulComps G₀ \ comps.toFinset)
          (fun X => W.winCost k ctx.L_w (compGraph G₀ X).n (compGraph G₀ X).m +
            250 * (compGraph G₀ X).n + 850 * (compGraph G₀ X).m + 450) hC_in_diff
        rw [hsdiff_eq] at hsum_split
        refine ⟨st', curHeap', comps', efIdx', winH_f, winX_f, 3 + (c_ef + 33) + c_rec + 1,
          runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st16, c_ef + 33, c_rec,
            by simp [Expr.eval, BinOp.eval, hr35, hR.r11, hilt, hw1], by decide,
            hbody, hrun_r, by simp [Expr.size]⟩)),
          hR', hr32', hr33', hr34', hall', hInvF, by
            dsimp only at hcr ⊢
            change c_ef ≤ W.winCost k ctx.L_w (compGraph G₀ C).n (compGraph G₀ C).m +
              230 * (compGraph G₀ C).n + 840 * (compGraph G₀ C).m + 360 at hcef
            clear * - hcef hcr hsum_split
            omega⟩

end

end MinCostFlow.SparseCore.Program
