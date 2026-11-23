module

public import MinCostFlow.LSF.Program.InitScanComp
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Outer Scan & Visited-Array Clear Proofs for `initScanStmt` (`InitScanOuter`)

Proves:
* `initScan_outer_runs`: outer vertex scan discovering connected components via `bfsComp_runs`
  and recording component representatives in `repList` in `O(n₀ + m₀)` steps.
* `initScan_clear_runs`: clears `visB` back to zero in `O(n₀)` steps.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

lemma initScan_outer_runs {w g0Ptr vCap auxPtr logCap auxEnd vCap0 eCap0 : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {sb : ScanBases} {G₀ : MGraph}
    {vL : List ℕ} {mem₀ : ℕ → ℕ} {incL : ℕ → List ℕ}
    (hw1 : 1 < 2 ^ w) (hauxW : auxEnd < 2 ^ w)
    (hdg₀ : DynGraphAt mem₀ g0Ptr vCap0 eCap0 G₀)
    (hinc₀ : ∀ s < vCap0,
      IsDoublyLinkedList mem₀ (dgHePrevBase g0Ptr vCap0 eCap0)
        (dgHeNextBase g0Ptr vCap0 eCap0) (dgIncHeadBase g0Ptr vCap0 + s) (2 * eCap0) (incL s) ∧
      mem₀ (dgSlotDegBase g0Ptr vCap0 + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCap0 ∧ h / 2 ∈ G₀.E ∧
        (if h % 2 = 0 then mem₀ (dgETailSlotBase g0Ptr vCap0 eCap0 + h / 2)
         else mem₀ (dgEHeadSlotBase g0Ptr vCap0 eCap0 + h / 2)) = s)
    (hagree_dg : ∀ a < g0Ptr + dynGraphSize vCap0 eCap0, st.mem a = mem₀ a)
    (hvs : G₀.n ≤ vCap) (hvs0 : vCap0 ≤ vCap) (hn_pos : 1 ≤ G₀.n)
    (haux_lo : g0Ptr + dynGraphSize vCap0 eCap0 ≤ auxPtr)
    (hle_aux : auxPtr + auxHdrSize ≤ sb.qBufABase)
    (hdisj_qv : sb.qBufABase + vCap = sb.cRepsBase)
    (hdisj_cv : sb.cRepsBase + 2 * vCap = sb.visBBase)
    (hvis_bound : sb.visBBase + vCap ≤ auxEnd)
    (hsb_eq : sb.gExtToIntBase = dgExtToIntBase g0Ptr vCap0 ∧
      sb.gIntToExtBase = dgIntToExtBase g0Ptr vCap0 ∧
      sb.gIncHeadBase = dgIncHeadBase g0Ptr vCap0 ∧
      sb.gETailBase = dgETailSlotBase g0Ptr vCap0 eCap0 ∧
      sb.gEHeadBase = dgEHeadSlotBase g0Ptr vCap0 eCap0 ∧
      sb.gHeNextBase = dgHeNextBase g0Ptr vCap0 eCap0)
    (hb : ScanBaseRegs st g0Ptr vCap auxPtr logCap sb) (hn_eq : sb.n0 = G₀.n)
    (hr23_0 : st.regs 23 = 0)
    (hVL_len : vL.length = G₀.n) (_hVL_nd : vL.Nodup) (hVL_mem : ∀ v, v ∈ vL ↔ v ∈ G₀.V)
    (hVL_at : ListAt st.mem sb.vListBase vL)
    (hvlist_lo : sb.vListBase + G₀.n ≤ sb.qBufABase)
    (hvis0 : ∀ v < vCap, st.mem (sb.visBBase + v) = 0) :
    ∃ st' c, ∃ repList : List ℕ, Runs w p ω
      (forRange 22 (.const 0) (.reg 6)
        (.assign 24 (.load (.bin .add (.reg 8) (.reg 22))) ;;
         .cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 24))) (.const 0))
           (.store (.bin .add (.reg 13) (.reg 23)) (.reg 24) ;;
            .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
            .store (.bin .add (.reg 14) (.reg 24)) (.const 1) ;;
            .store (.reg 12) (.reg 24) ;;
            .assign 25 (.const 0) ;;
            .assign 26 (.const 1) ;;
            initScanBfsCompStmt)
           .nop)) st .normal st' c ∧
      ScanBaseRegs st' g0Ptr vCap auxPtr logCap sb ∧
      1 ≤ repList.length ∧ repList.length ≤ G₀.n ∧ repList.Nodup ∧
      st'.regs 23 = repList.length ∧
      repList.getD 0 0 = vL.getD 0 0 ∧
      ListAt st'.mem sb.cRepsBase repList ∧
      IsCompReps G₀ (vL.getD 0 0) repList.toFinset ∧
      (∀ z ∈ G₀.V, st'.mem (sb.visBBase + z) = 1) ∧
      (∀ z < vCap, z ∉ G₀.V → st'.mem (sb.visBBase + z) = 0) ∧
      (∀ a, a < sb.qBufABase ∨ (sb.cRepsBase + vCap ≤ a ∧ a < sb.visBBase) ∨
        sb.visBBase + vCap ≤ a → st'.mem a = st.mem a) ∧
      c ≤ 85 * G₀.n + 280 * G₀.m + 50 * G₀.n + 25 := by
  have hgnW : G₀.n < 2 ^ w := by omega
  let degCost : ℕ → ℕ := fun u => 140 * (incL (mem₀ (dgExtToIntBase g0Ptr vCap0 + u))).length + 50
  unfold forRange forUp
  set st0 : State := { mem := st.mem, regs := Function.update st.regs 22 0, pos := st.pos }
  have hb0 : ScanBaseRegs st0 g0Ptr vCap auxPtr logCap sb :=
    scanBaseRegs_upd hb 22 0 (by decide)
  have hr_init22 : Runs w p ω (.assign 22 (.const 0)) st .normal st0 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  let Inv : State → Prop := fun st_k => ∃ (i : ℕ) (preVis : Finset ℕ) (repList : List ℕ),
    i ≤ G₀.n ∧
    ScanBaseRegs st_k g0Ptr vCap auxPtr logCap sb ∧
    st_k.regs 22 = i ∧
    st_k.regs 23 = repList.length ∧
    repList.length ≤ i ∧
    preVis ⊆ G₀.V ∧
    (∀ a ∈ preVis, ∀ b, mgAdj G₀ a b → b ∈ preVis) ∧
    (∀ j < i, vL.getD j 0 ∈ preVis) ∧
    (repList.length = 0 ↔ i = 0) ∧
    (0 < i → repList.getD 0 0 = vL.getD 0 0) ∧
    repList.Nodup ∧
    (∀ r ∈ repList, r ∈ G₀.V) ∧
    (∀ r ∈ repList, r ∈ preVis) ∧
    (∀ r₁ ∈ repList, ∀ r₂ ∈ repList, r₁ ≠ r₂ → ¬ G₀.Connected r₁ r₂) ∧
    (∀ z ∈ preVis, ∃ r ∈ repList, G₀.Connected z r) ∧
    ListAt st_k.mem sb.cRepsBase repList ∧
    (∀ z ∈ G₀.V, st_k.mem (sb.visBBase + z) = if z ∈ preVis then 1 else 0) ∧
    (∀ z < vCap, z ∉ G₀.V → st_k.mem (sb.visBBase + z) = 0) ∧
    ∀ a, a < sb.qBufABase ∨ (sb.cRepsBase + vCap ≤ a ∧ a < sb.visBBase) ∨
      sb.visBBase + vCap ≤ a → st_k.mem a = st.mem a
  have hvlt0 := hdg₀.2.1
  let outerB : Stmt :=
    .assign 24 (.load (.bin .add (.reg 8) (.reg 22))) ;;
    .cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 24))) (.const 0))
      (.store (.bin .add (.reg 13) (.reg 23)) (.reg 24) ;;
       .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
       .store (.bin .add (.reg 14) (.reg 24)) (.const 1) ;;
       .store (.reg 12) (.reg 24) ;;
       .assign 25 (.const 0) ;;
       .assign 26 (.const 1) ;;
       initScanBfsCompStmt)
      .nop
  let body := outerB ;; .assign 22 (.bin .add (.reg 22) (.const 1))
  have hloop := Triple.loop_measure (w := w) (p := p) (e := .bin .lt (.reg 22) (.reg 6))
    (body := body) (Inv := Inv) (Q := normalPost (fun st_k => Inv st_k ∧ st_k.regs 22 = G₀.n))
    (m := fun st_k => G₀.n - st_k.regs 22)
    (rem := fun st_k => (G₀.n - st_k.regs 22) * 85 +
      (∑ u ∈ G₀.V.filter (fun z => st_k.mem (sb.visBBase + z) = 0), degCost u) + 12)
    (condVal := fun st_k => if st_k.regs 22 < G₀.n then 1 else 0)
    (fun st_k hInv => by
      rcases hInv with ⟨i, _, _, hi_le, hb_k, hr22, _⟩
      have h6 := hb_k.r6; rw [hn_eq] at h6
      have h22w : st_k.regs 22 < 2 ^ w := by omega
      eval_expr)
    (fun st_k hInv hv0 => by
      rcases hInv with ⟨i, preVis, repList, hi_le, hb_k, hr22, rest⟩
      have hge : G₀.n ≤ st_k.regs 22 := by
        by_contra hlt; simp [hlt] at hv0
      exact ⟨⟨⟨i, preVis, repList, hi_le, hb_k, hr22, rest⟩, by omega⟩, by dsimp [Expr.size]; omega⟩)
    (fun st_k hInv hv_ne => by
      rcases hInv with ⟨i, preVis, repList, hi_le, hb_k, hr22, hr23, hrep_le, hpre_sub,
        hpre_closed, hpref_vis, hrep0_iff, hrep0_eq, hrep_nd, hrep_V, hrep_pre, hrep_disc,
        hpre_reach, hrep_LA, hvis1, hvisOut, hfr_k⟩
      have hilt : i < G₀.n := by
        by_contra hge
        have : ¬ st_k.regs 22 < G₀.n := by omega
        simp [this] at hv_ne
      have hi_len : i < vL.length := hVL_len.symm ▸ hilt
      set u := vL[i]'hi_len
      have huV : u ∈ G₀.V := (hVL_mem u).mp (List.getElem_mem hi_len)
      have hu_cap : u < vCap := lt_of_lt_of_le (hvlt0 u huV) hvs0
      have hr8 : st_k.regs 8 = sb.vListBase := hb_k.r8
      have hr12 : st_k.regs 12 = sb.qBufABase := hb_k.r12
      have hr13 : st_k.regs 13 = sb.cRepsBase := hb_k.r13
      have hr14 : st_k.regs 14 = sb.visBBase := hb_k.r14
      have hu_w : u < 2 ^ w := by omega
      have hi_w : i < 2 ^ w := by omega
      have hi1_w : i + 1 < 2 ^ w := by omega
      have hvl_addrW : sb.vListBase + i < 2 ^ w := by omega
      have hvisB_w : sb.visBBase < 2 ^ w := by omega
      have hvis_addrW : sb.visBBase + u < 2 ^ w := by omega
      have hu_val : st_k.mem (sb.vListBase + i) = u := by
        rw [hfr_k _ (Or.inl (by omega))]
        exact hVL_at i hi_len
      by_cases hu_pre : u ∈ preVis
      · have hi_pos : 0 < i := by
          by_contra h0
          have hi0 : i = 0 := by omega
          subst hi0
          obtain ⟨r, hr, _⟩ := hpre_reach u hu_pre
          have hlen : repList.length = 0 := hrep0_iff.mpr rfl
          simp only [List.length_eq_zero_iff] at hlen
          simp [hlen] at hr
        refine ⟨25, fun s_0 ω' hs0 => ?_⟩
        subst s_0
        set st1 : State := { st_k with regs := Function.update st_k.regs 24 u }
        have hb1 := scanBaseRegs_upd hb_k 24 u (by decide)
        have hr14_1 : st1.regs 14 = sb.visBBase := hb1.r14
        have hr24_1 : st1.regs 24 = u := by simp [st1]
        have hm_vis : st1.mem (sb.visBBase + u) = 1 := by
          dsimp [st1]; simp [hvis1 u huV, hu_pre]
        have hcond_ev : Expr.eval w st1 (.bin .eq (.load (.bin .add (.reg 14) (.reg 24))) (.const 0)) =
            some 0 := by
          have h0w : 0 < 2 ^ w := by omega
          simp [Expr.eval, hr14_1, hr24_1, hvis_addrW, hm_vis, h0w]
        have hr_outerB : ∃ c1, Runs w p ω' outerB st_k .normal st1 c1 ∧ c1 ≤ 18 := by
          dsimp only [outerB]
          refine ⟨_, WordRAM.runs_seq_iff.mpr (Or.inr ⟨st1,
            (Expr.load (.bin .add (.reg 8) (.reg 22))).size + 1, _,
            runs_assign_iff.mpr ⟨u, by eval_expr, rfl, rfl, rfl⟩,
            WordRAM.runs_cond_iff.mpr ⟨0, 1, hcond_ev, by simp [runs_nop_iff], rfl⟩,
            rfl⟩), by simp [Expr.size]⟩
        obtain ⟨c1, hr1, hc1⟩ := hr_outerB
        set st2 : State := { st1 with regs := Function.update st1.regs 22 (i + 1) }
        have hr2 : Runs w p ω' (.assign 22 (.bin .add (.reg 22) (.const 1))) st1 .normal st2 4 :=
          runs_assign_iff.mpr ⟨i + 1, by
            have h22_1 : st1.regs 22 = i := by simp [st1, hr22]
            eval_expr, rfl, rfl, rfl⟩
        refine ⟨.normal, st2, c1 + 4 + 1,
          WordRAM.runs_seq_iff.mpr (Or.inr ⟨st1, c1, 4, hr1, hr2, rfl⟩), ?_,
          by dsimp only; omega⟩
        have hsum_eq : (∑ z ∈ G₀.V.filter (fun z => st_k.mem (sb.visBBase + z) = 0), degCost z) =
            ∑ z ∈ G₀.V.filter (fun z => st2.mem (sb.visBBase + z) = 0), degCost z := rfl
        refine ⟨⟨i + 1, preVis, repList, by omega,
            scanBaseRegs_upd hb1 22 (i + 1) (by decide), by simp [st2], by simp [st2, st1, hr23],
            by omega, hpre_sub, hpre_closed, fun j hj => by
              by_cases hji : j = i
              · subst j; rw [List.getD_eq_getElem _ _ hi_len]; exact hu_pre
              · exact hpref_vis j (by omega),
            ⟨fun h => by exfalso; have := hrep0_iff.mp h; omega, fun h => by omega⟩,
            fun _ => hrep0_eq hi_pos,
            hrep_nd, hrep_V, hrep_pre, hrep_disc, hpre_reach, hrep_LA, hvis1, hvisOut, hfr_k⟩,
          by simp [st2, hr22]; omega, ?_⟩
        dsimp only [Expr.size] at *
        rw [← hsum_eq]
        simp only [st2, st1, hr22, Function.update_self]
        have hmul85 : (G₀.n - i) * 85 = (G₀.n - (i + 1)) * 85 + 85 := by
          rw [show G₀.n - i = (G₀.n - (i + 1)) + 1 by omega]; ring
        omega
      · let C_u := compOf G₀ u
        let stepCost := (∑ v ∈ C_u, degCost v) + 60
        refine ⟨stepCost, fun s_0 ω' hs0 => ?_⟩
        subst s_0
        set st1 : State := { st_k with regs := Function.update st_k.regs 24 u }
        have hb1 := scanBaseRegs_upd hb_k 24 u (by decide)
        have hr12_1 : st1.regs 12 = sb.qBufABase := hb1.r12
        have hr13_1 : st1.regs 13 = sb.cRepsBase := hb1.r13
        have hr14_1 : st1.regs 14 = sb.visBBase := hb1.r14
        have hr23_1 : st1.regs 23 = repList.length := by simp [st1, hr23]
        have hr24_1 : st1.regs 24 = u := by simp [st1]
        have hm_vis : st1.mem (sb.visBBase + u) = 0 := by
          dsimp [st1]; simp [hvis1 u huV, hu_pre]
        have hcond_ev : Expr.eval w st1 (.bin .eq (.load (.bin .add (.reg 14) (.reg 24))) (.const 0)) =
            some 1 := by
          have h0w : 0 < 2 ^ w := by omega
          simp [Expr.eval, hr14_1, hr24_1, hvis_addrW, hm_vis, hw1, h0w]
        have hcrep_w : sb.cRepsBase < 2 ^ w := by omega
        have hqbuf_w : sb.qBufABase < 2 ^ w := by omega
        have hreplen_w : repList.length < 2 ^ w := by omega
        have hcrep_addrW : sb.cRepsBase + repList.length < 2 ^ w := by omega
        have hrep1W : repList.length + 1 < 2 ^ w := by omega
        have hqbuf_addrW : sb.qBufABase < 2 ^ w := by omega
        set mem_bfs := Function.update st1.mem (sb.cRepsBase + repList.length) u
        have hagree_bfs : ∀ a < g0Ptr + dynGraphSize vCap0 eCap0, mem_bfs a = mem₀ a := by
          intro a ha
          have ha_lt_q : a < sb.qBufABase := by omega
          have hne_c : a ≠ sb.cRepsBase + repList.length := by omega
          dsimp [mem_bfs, st1]
          rw [Function.update_of_ne hne_c, hfr_k a (Or.inl ha_lt_q), hagree_dg a ha]
        obtain ⟨hdg_bfs, hinc_bfs⟩ := dynGraphAt_and_inc_of_agree hdg₀ hinc₀ hagree_bfs
        set mem_vis := Function.update mem_bfs (sb.visBBase + u) 1
        set mem_q0 := Function.update mem_vis sb.qBufABase u
        set st_bfs0 : State := {
          mem := mem_q0,
          regs := Function.update (Function.update (Function.update st1.regs 23
            (repList.length + 1)) 25 0) 26 1,
          pos := st1.pos }
        have hb_bfs0 : ScanBaseRegs st_bfs0 g0Ptr vCap auxPtr logCap sb :=
          scanBaseRegs_upd (scanBaseRegs_upd (scanBaseRegs_upd (scanBaseRegs_updMem hb1 _)
            23 (repList.length + 1) (by decide)) 25 0 (by decide)) 26 1 (by decide)
        have hinv0_bfs : st_bfs0.regs 25 = 0 ∧ st_bfs0.regs 26 = 1 ∧
            memSlice st_bfs0.mem sb.qBufABase 1 = [u] ∧
            (∀ z ∈ G₀.V, st_bfs0.mem (sb.visBBase + z) = if z ∈ preVis ∨ z = u then 1 else 0) ∧
            (∀ z < vCap, z ∉ G₀.V → st_bfs0.mem (sb.visBBase + z) = 0) ∧
            ∀ a, a < sb.qBufABase ∨ (sb.qBufABase + vCap ≤ a ∧ a < sb.visBBase) ∨
              sb.visBBase + vCap ≤ a → st_bfs0.mem a = mem_bfs a := by
          refine ⟨by simp [st_bfs0], by simp [st_bfs0], ?_, ?_, ?_, ?_⟩
          · dsimp only [st_bfs0]
            rw [memSlice_one]
            simp [mem_q0]
          · intro z hzV
            dsimp only [st_bfs0, mem_q0, mem_vis, mem_bfs, st1]
            have hne_q : sb.visBBase + z ≠ sb.qBufABase := by omega
            rw [Function.update_of_ne hne_q]
            by_cases hzu : z = u
            · subst z; simp
            · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hvis1 z hzV]
              simp [hzu]
          · intro z hz hznot
            dsimp only [st_bfs0, mem_q0, mem_vis, mem_bfs, st1]
            have hzu : z ≠ u := fun h => hznot (h ▸ huV)
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hvisOut z hz hznot
          · intro a ha
            dsimp only [st_bfs0, mem_q0, mem_vis]
            have hne_q : a ≠ sb.qBufABase := by rcases ha with h | ⟨h1, h2⟩ | h <;> omega
            have hne_v : a ≠ sb.visBBase + u := by rcases ha with h | ⟨h1, h2⟩ | h <;> omega
            rw [Function.update_of_ne hne_q, Function.update_of_ne hne_v]
        obtain ⟨st_bfs, c_bfs, hr_bfs, hb_bfs, hr22_bfs, hr23_bfs, hvis1_bfs, hvisOut_bfs,
            hcomp_npre, hfr_bfs, hc_bfs⟩ :=
          bfsComp_runs (w := w) (startV := u) (ω := ω') hw1 hauxW hdg_bfs hinc_bfs
            hvs hvs0 haux_lo (by omega) (by omega) (by omega) hle_aux hsb_eq
            huV hpre_sub hpre_closed hu_pre hb_bfs0 hinv0_bfs
        have hr_true_branch : ∃ c_tb, Runs w p ω'
            (.store (.bin .add (.reg 13) (.reg 23)) (.reg 24) ;;
             .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
             .store (.bin .add (.reg 14) (.reg 24)) (.const 1) ;;
             .store (.reg 12) (.reg 24) ;;
             .assign 25 (.const 0) ;;
             .assign 26 (.const 1) ;;
             initScanBfsCompStmt) st1 .normal st_bfs c_tb ∧ c_tb = 27 + c_bfs := by
          refine ⟨_, WordRAM.runs_seq_iff.mpr (Or.inr ⟨_, 5, _,
            runs_store_iff.mpr ⟨sb.cRepsBase + repList.length, u, by eval_expr, by eval_expr, rfl, rfl, rfl⟩,
            WordRAM.runs_seq_iff.mpr (Or.inr ⟨_, 4, _,
              runs_assign_iff.mpr ⟨repList.length + 1, by eval_expr, rfl, rfl, rfl⟩,
              WordRAM.runs_seq_iff.mpr (Or.inr ⟨_, 5, _,
                runs_store_iff.mpr ⟨sb.visBBase + u, 1, by eval_expr, Expr.eval_const hw1, rfl, rfl, rfl⟩,
                WordRAM.runs_seq_iff.mpr (Or.inr ⟨_, 3, _,
                  runs_store_iff.mpr ⟨sb.qBufABase, u, by eval_expr, by eval_expr, rfl, rfl, rfl⟩,
                  WordRAM.runs_seq_iff.mpr (Or.inr ⟨_, 2, _,
                    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩,
                    WordRAM.runs_seq_iff.mpr (Or.inr ⟨_, 2, c_bfs,
                      runs_assign_iff.mpr ⟨1, Expr.eval_const hw1, rfl, rfl, rfl⟩,
                      by simpa [st_bfs0, mem_q0, mem_vis, mem_bfs, st1] using hr_bfs,
                      rfl⟩),
                    rfl⟩),
                  rfl⟩),
                rfl⟩),
              rfl⟩),
            rfl⟩), by ring⟩
        obtain ⟨c_tb, hr_tb, hc_tb⟩ := hr_true_branch
        have hc_bfs' : c_bfs ≤ (∑ v ∈ C_u, degCost v) + 15 := by
          refine le_trans hc_bfs (Nat.add_le_add_right (Finset.sum_le_sum fun v hv => ?_) _)
          dsimp only [degCost]
          have hvV : v ∈ G₀.V := (mem_compOf_iff.mp hv).1
          have hvt : mem_bfs (dgExtToIntBase g0Ptr vCap0 + v) =
              mem₀ (dgExtToIntBase g0Ptr vCap0 + v) := by
            refine hagree_bfs _ ?_
            have := hvlt0 v hvV
            dsimp [dgExtToIntBase, dynGraphSize]
            omega
          rw [hvt]
        have hr_outerB : ∃ c_out, Runs w p ω' outerB st_k .normal st_bfs c_out ∧
            c_out ≤ 40 + c_bfs := by
          dsimp only [outerB]
          refine ⟨_, WordRAM.runs_seq_iff.mpr (Or.inr ⟨st1,
            (Expr.load (.bin .add (.reg 8) (.reg 22))).size + 1, _,
            runs_assign_iff.mpr ⟨u, by eval_expr, rfl, rfl, rfl⟩,
            WordRAM.runs_cond_iff.mpr ⟨1, c_tb, hcond_ev, by simpa using hr_tb, rfl⟩,
            rfl⟩), ?_⟩
          simp only [Expr.size]
          omega
        obtain ⟨c_out, hr_outerB, hc_out⟩ := hr_outerB
        set st2 : State := { st_bfs with regs := Function.update st_bfs.regs 22 (i + 1) }
        have hr22_bfs' : st_bfs.regs 22 = i := by rw [hr22_bfs]; simp [st_bfs0, st1, hr22]
        have hr_inc : Runs w p ω' (.assign 22 (.bin .add (.reg 22) (.const 1))) st_bfs .normal st2 4 :=
          runs_assign_iff.mpr ⟨i + 1, by eval_expr, rfl, rfl, rfl⟩
        refine ⟨.normal, st2, c_out + 4 + 1,
          WordRAM.runs_seq_iff.mpr (Or.inr ⟨st_bfs, c_out, 4, hr_outerB, hr_inc, rfl⟩), ?_, ?_⟩
        · have hb2 : ScanBaseRegs st2 g0Ptr vCap auxPtr logCap sb :=
            scanBaseRegs_upd hb_bfs 22 (i + 1) (by decide)
          have hr22_2 : st2.regs 22 = i + 1 := by simp [st2]
          have hr23_2 : st2.regs 23 = (repList ++ [u]).length := by
            dsimp [st2]; rw [Function.update_of_ne (by decide), hr23_bfs]
            simp [st_bfs0, st1]
          have hmem2_eq : st2.mem = st_bfs.mem := rfl
          have hu_not_rep : u ∉ repList := fun huR => hu_pre (hrep_pre u huR)
          have hpre_eq_V : ∀ z ∈ preVis ∪ C_u, z ∈ G₀.V := fun z hz => by
            rcases Finset.mem_union.mp hz with h | h
            · exact hpre_sub h
            · exact (mem_compOf_iff.mp h).1
          have hdisc' : ∀ r₁ ∈ repList ++ [u], ∀ r₂ ∈ repList ++ [u], r₁ ≠ r₂ →
              ¬ G₀.Connected r₁ r₂ := by
            intro r₁ hr1 r₂ hr2 hne hc
            simp only [List.mem_append, List.mem_singleton] at hr1 hr2
            rcases hr1 with hr1 | rfl <;> rcases hr2 with hr2 | rfl
            · exact hrep_disc r₁ hr1 r₂ hr2 hne hc
            · exact hu_pre (reachable_in_closed_set hpre_closed (hrep_pre r₁ hr1) hc)
            · exact hu_pre (reachable_in_closed_set hpre_closed (hrep_pre r₂ hr2) (connected_symm hc))
            · exact hne rfl
          have hreach' : ∀ z ∈ preVis ∪ C_u, ∃ r ∈ repList ++ [u], G₀.Connected z r := by
            intro z hz
            rcases Finset.mem_union.mp hz with hz | hz
            · obtain ⟨r, hr, hzc⟩ := hpre_reach z hz
              exact ⟨r, List.mem_append_left _ hr, hzc⟩
            · exact ⟨u, List.mem_append_right _ List.mem_cons_self,
                connected_symm (mem_compOf_iff.mp hz).2⟩
          have hLA' : ListAt st2.mem sb.cRepsBase (repList ++ [u]) := by
            intro j hj
            rw [List.length_append, List.length_singleton] at hj
            have hfrj := hfr_bfs (sb.cRepsBase + j) (Or.inr (Or.inl ⟨by omega, by omega⟩))
            rw [hmem2_eq, hfrj]
            dsimp only [mem_bfs, st1]
            by_cases hjl : j = repList.length
            · subst j; simp [Function.update_self]
            · have hj_lt : j < repList.length := by omega
              rw [Function.update_of_ne (by omega), List.getElem_append_left hj_lt]
              exact hrep_LA j hj_lt
          have hvis1' : ∀ z ∈ G₀.V, st2.mem (sb.visBBase + z) =
              if z ∈ preVis ∪ C_u then 1 else 0 := hvis1_bfs
          have hfr' : ∀ a, a < sb.qBufABase ∨ (sb.cRepsBase + vCap ≤ a ∧ a < sb.visBBase) ∨
              sb.visBBase + vCap ≤ a → st2.mem a = st.mem a := by
            intro a ha
            rw [hmem2_eq, hfr_bfs a (by
              rcases ha with h | ⟨h1, h2⟩ | h
              · exact Or.inl h
              · exact Or.inr (Or.inl ⟨by omega, h2⟩)
              · exact Or.inr (Or.inr h))]
            dsimp only [mem_bfs, st1]
            have hne_c : a ≠ sb.cRepsBase + repList.length := by
              rcases ha with h | ⟨h1, h2⟩ | h <;> omega
            rw [Function.update_of_ne hne_c]
            exact hfr_k a ha
          have hu_filt_k : G₀.V.filter (fun z => st_k.mem (sb.visBBase + z) = 0) = G₀.V \ preVis := by
            ext z
            simp only [Finset.mem_filter, Finset.mem_sdiff, and_congr_right_iff]
            intro hzV
            rw [hvis1 z hzV]
            split_ifs <;> simp_all
          have hu_filt_2 : G₀.V.filter (fun z => st2.mem (sb.visBBase + z) = 0) =
              (G₀.V \ preVis) \ C_u := by
            ext z
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            constructor
            · rintro ⟨hzV, h0⟩
              simp only [hmem2_eq, hvis1_bfs z hzV, Finset.mem_union] at h0
              by_cases h : z ∈ preVis ∨ z ∈ C_u
              · have h' : z ∈ preVis ∨ z ∈ compOf G₀ u := h
                simp [h'] at h0
              · exact ⟨⟨hzV, fun hp => h (Or.inl hp)⟩, fun hc => h (Or.inr hc)⟩
            · rintro ⟨⟨hzV, hnp⟩, hnc⟩
              refine ⟨hzV, ?_⟩
              simp only [hmem2_eq, hvis1_bfs z hzV, Finset.mem_union, hnp]
              have hnc' : z ∉ compOf G₀ u := hnc
              simp [hnc']
          have hCu_sub : C_u ⊆ G₀.V \ preVis := fun z hz =>
            Finset.mem_sdiff.mpr ⟨(mem_compOf_iff.mp hz).1, hcomp_npre z hz⟩
          have hsum_split := Finset.sum_sdiff hCu_sub (f := degCost)
          refine ⟨⟨i + 1, preVis ∪ C_u, repList ++ [u], by omega, hb2, hr22_2, hr23_2, by simp; omega,
              hpre_eq_V, preVis_union_compOf_closed hdg₀.1 hpre_closed,
              fun j hj => by
                rw [Finset.mem_union]
                by_cases hji : j = i
                · subst j; right; rw [List.getD_eq_getElem _ _ hi_len]
                  exact mem_compOf_iff.mpr ⟨huV, connected_refl G₀ u⟩
                · left; exact hpref_vis j (by omega),
              by simp, fun _ => by
                by_cases hi0 : i = 0
                · subst hi0
                  have hrl : repList.length = 0 := hrep0_iff.mpr rfl
                  simp only [List.length_eq_zero_iff] at hrl
                  rw [hrl]
                  exact (List.getD_eq_getElem _ _ hi_len).symm
                · have hpos : 0 < repList.length := by
                    by_contra h0
                    have : repList.length = 0 := by omega
                    exact hi0 (hrep0_iff.mp this)
                  rcases List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hpos) with ⟨r0, rs, hrs⟩
                  have h0' := hrep0_eq (by omega)
                  rw [hrs] at h0' ⊢
                  simpa using h0',
              List.nodup_append.mpr ⟨hrep_nd, List.nodup_singleton _, fun a ha b hb => by
                simp only [List.mem_singleton] at hb; subst hb; intro hEq; subst hEq; exact hu_not_rep ha⟩,
              fun r hr => by
                simp only [List.mem_append, List.mem_singleton] at hr
                rcases hr with hr | rfl <;> [exact hrep_V r hr; exact huV],
              fun r hr => by
                rw [Finset.mem_union]
                simp only [List.mem_append, List.mem_singleton] at hr
                rcases hr with hr | rfl
                · left; exact hrep_pre r hr
                · right; exact mem_compOf_iff.mpr ⟨huV, connected_refl G₀ u⟩,
              hdisc', hreach', hLA', hvis1', hvisOut_bfs, hfr'⟩,
            by rw [hr22_2, hr22]; omega, ?_⟩
          rw [hu_filt_k, hu_filt_2, ← hsum_split, hr22_2, hr22]
          have hmul85 : (G₀.n - i) * 85 = (G₀.n - (i + 1)) * 85 + 85 := by
            rw [show G₀.n - i = (G₀.n - (i + 1)) + 1 by omega]; ring
          dsimp only [Expr.size, stepCost] at *
          omega
        · dsimp only [stepCost] at *
          omega)
  have hInv0 : Inv st0 := by
    refine ⟨0, ∅, [], Nat.zero_le _, hb0, by simp [st0], by simp [st0, hr23_0], by simp, Finset.empty_subset _,
      fun _ h => by simp at h, fun _ h => by omega, by simp, fun h => by omega,
      List.nodup_nil, fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ h => by simp at h, fun _ h => by simp at h,
      fun _ h => by simp at h, fun z _ => by simp [st0, hvis0 z (lt_of_lt_of_le (hvlt0 z ‹_›) hvs0)],
      fun z hz _ => by simp [st0, hvis0 z hz], fun _ _ => rfl⟩
  obtain ⟨o, st', c, hr, hpost, hc⟩ := hloop st0 ω hInv0
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨⟨i, preVis, repList, hi_le, hb', hr22', hr23', hrep_le, hpre_sub,
      hpre_closed, hpref_vis, hrep0_iff, hrep0_eq, hrep_nd, hrep_V, hrep_pre, hrep_disc,
      hpre_reach, hrep_LA, hvis1', hvisOut', hfr'⟩, hr22_gn⟩
    have hi_eq : i = G₀.n := by omega
    subst hi_eq
    have hpre_eq_V : preVis = G₀.V := by
      apply Finset.Subset.antisymm hpre_sub
      intro z hzV
      obtain ⟨j, hj_lt, hj_eq⟩ := List.mem_iff_getElem.mp ((hVL_mem z).mpr hzV)
      have hpv := hpref_vis j (hVL_len ▸ hj_lt)
      rwa [List.getD_eq_getElem _ _ hj_lt, hj_eq] at hpv
    have hpos_rep : 1 ≤ repList.length := by
      by_contra h0
      have hrl : repList.length = 0 := by omega
      have := hrep0_iff.mp hrl
      omega
    have hcomp_reps : IsCompReps G₀ (vL.getD 0 0) repList.toFinset := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [List.mem_toFinset, ← hrep0_eq hn_pos, List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      · intro r hr
        exact hrep_V r (List.mem_toFinset.mp hr)
      · refine Finset.card_le_card_of_injOn (compOf G₀) (fun r hr => by
          rw [components, Finset.mem_coe, Finset.mem_image]
          exact ⟨r, hrep_V r (List.mem_toFinset.mp hr), rfl⟩) (fun r₁ hr1 r₂ hr2 hEq => ?_)
        simp only [Finset.mem_coe, List.mem_toFinset] at hr1 hr2
        by_contra hne
        have hr2_in : r₂ ∈ compOf G₀ r₁ := by
          rw [hEq, mem_compOf_iff]
          exact ⟨hrep_V r₂ hr2, connected_refl G₀ r₂⟩
        exact hrep_disc r₁ hr1 r₂ hr2 hne (mem_compOf_iff.mp hr2_in).2
      · intro w' hw'
        have hwp : w' ∈ preVis := hpre_eq_V ▸ hw'
        obtain ⟨r, hr, hconn⟩ := hpre_reach w' hwp
        exact ⟨r, List.mem_toFinset.mpr hr, hconn⟩
    have hvis_final : ∀ z ∈ G₀.V, st'.mem (sb.visBBase + z) = 1 := fun z hz => by
      simp [hvis1' z hz, hpre_eq_V ▸ hz]
    have hsum_le : ∑ u ∈ G₀.V.filter (fun z => st0.mem (sb.visBBase + z) = 0), degCost u ≤
        280 * G₀.m + 50 * G₀.n := by
      have hsub : G₀.V.filter (fun z => st0.mem (sb.visBBase + z) = 0) ⊆ G₀.V :=
        Finset.filter_subset _ _
      calc ∑ u ∈ G₀.V.filter (fun z => st0.mem (sb.visBBase + z) = 0), degCost u
          ≤ ∑ u ∈ G₀.V, degCost u := Finset.sum_le_sum_of_subset hsub
        _ = 140 * (∑ u ∈ G₀.V, (incL (mem₀ (dgExtToIntBase g0Ptr vCap0 + u))).length) + 50 * G₀.n := by
            simp only [degCost, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
              Finset.mul_sum, MGraph.n]; ring
        _ ≤ 140 * (2 * G₀.m) + 50 * G₀.n := by
            gcongr; exact sum_incL_le_two_mul_m hdg₀ hinc₀
        _ = 280 * G₀.m + 50 * G₀.n := by ring
    refine ⟨st', 2 + c + 1, repList,
      WordRAM.runs_seq_iff.mpr (Or.inr ⟨st0, 2, c, hr_init22, hr, rfl⟩),
      hb', hpos_rep, hrep_le, hrep_nd, hr23',
      hrep0_eq hn_pos, hrep_LA, hcomp_reps, hvis_final, hvisOut', hfr', ?_⟩
    have hrem0 : st0.regs 22 = 0 := by simp [st0]
    dsimp only [Expr.size] at hc ⊢
    rw [hrem0] at hc
    omega

lemma initScan_clear_runs {w g0Ptr vCap auxPtr logCap auxEnd : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {sb : ScanBases} {G₀ : MGraph} {vL : List ℕ}
    (hw1 : 1 < 2 ^ w) (hauxW : auxEnd < 2 ^ w)
    (hvs0 : ∀ v ∈ G₀.V, v < vCap)
    (hVL_len : vL.length = G₀.n) (hVL_mem : ∀ v, v ∈ vL ↔ v ∈ G₀.V)
    (hVL_LA : ListAt st.mem sb.vListBase vL)
    (hvlist_lo : sb.vListBase + G₀.n ≤ sb.visBBase)
    (hvis_hi : sb.visBBase + vCap ≤ auxEnd)
    (hb : ScanBaseRegs st g0Ptr vCap auxPtr logCap sb) (hn_eq : sb.n0 = G₀.n)
    (hvisOut : ∀ v < vCap, v ∉ G₀.V → st.mem (sb.visBBase + v) = 0) :
    ∃ st' c, Runs w p ω
      (forRange 22 (.const 0) (.reg 6)
        (.assign 24 (.load (.bin .add (.reg 8) (.reg 22))) ;;
         .store (.bin .add (.reg 14) (.reg 24)) (.const 0))) st .normal st' c ∧
      ScanBaseRegs st' g0Ptr vCap auxPtr logCap sb ∧
      st'.regs 23 = st.regs 23 ∧
      (∀ v < vCap, st'.mem (sb.visBBase + v) = 0) ∧
      (∀ a, a < sb.visBBase ∨ sb.visBBase + vCap ≤ a → st'.mem a = st.mem a) ∧
      c ≤ 25 * G₀.n + 10 := by
  let Inv : ℕ → State → Prop := fun i st_k =>
    ScanBaseRegs st_k g0Ptr vCap auxPtr logCap sb ∧
    st_k.regs 22 = i ∧
    st_k.regs 23 = st.regs 23 ∧
    (∀ j < i, st_k.mem (sb.visBBase + vL.getD j 0) = 0) ∧
    (∀ v < vCap, v ∉ G₀.V → st_k.mem (sb.visBBase + v) = 0) ∧
    ∀ a, a < sb.visBBase ∨ sb.visBBase + vCap ≤ a → st_k.mem a = st.mem a
  have hgnW : G₀.n < 2 ^ w := by omega
  have hloop : Triple w p (fun s => s = st)
      (forRange 22 (.const 0) (.reg 6)
        (.assign 24 (.load (.bin .add (.reg 8) (.reg 22))) ;;
         .store (.bin .add (.reg 14) (.reg 24)) (.const 0)))
      (normalPost (Inv G₀.n)) (fun _ => (G₀.n - 0) * (15 + (.reg 6 : Expr).size + 8) + ((.const 0 : Expr).size + (.reg 6 : Expr).size + 5)) :=
    Triple.forRange_const (w := w) (p := p) (P := fun s => s = st)
      (r := 22) (lo := .const 0) (hi := .reg 6) (Inv := Inv) 15 0 G₀.n
      (Nat.zero_le G₀.n) hw1 (fun _ => hgnW)
      (fun st_0 hst0 => by
        subst hst0
        exact ⟨Expr.eval_const (by omega), scanBaseRegs_upd hb 22 0 (by decide), rfl, rfl,
          fun _ h => by omega, hvisOut, fun _ _ => rfl⟩)
      (fun i st_k _ _ hInv => hInv.2.1)
      (fun i st_k _ _ hInv => by have h6 := hInv.1.r6; rw [hn_eq] at h6; eval_expr)
      (fun i _ hilt st_k ω' hInv => by
      rcases hInv with ⟨hb_k, hr22, hr23, hcl_k, hvisOut_k, hfr_k⟩
      have hi_len : i < vL.length := hVL_len.symm ▸ hilt
      set u := vL[i]'hi_len
      have huV : u ∈ G₀.V := (hVL_mem u).mp (List.getElem_mem hi_len)
      have hu_cap : u < vCap := hvs0 u huV
      have hr8 : st_k.regs 8 = sb.vListBase := hb_k.r8
      have hr14 : st_k.regs 14 = sb.visBBase := hb_k.r14
      have huW : u < 2 ^ w := by omega
      have hvl_addrW : sb.vListBase + i < 2 ^ w := by omega
      have hvis_addrW : sb.visBBase + u < 2 ^ w := by omega
      have hu_val : st_k.mem (sb.vListBase + i) = u := by
        rw [hfr_k _ (Or.inl (by omega))]
        exact hVL_LA i hi_len
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := u) (by eval_expr) ?_
      refine runs_store_le (by eval_expr) (Expr.eval_const (by omega)) ?_ (by wram_cost)
      refine ⟨⟨scanBaseRegs_upd (scanBaseRegs_updMem (scanBaseRegs_upd hb_k 24 u (by decide)) _)
          22 (i + 1) (by decide),
        by simp, by simp [hr23], ?_, ?_, ?_⟩, by simp [hr22]⟩
      · intro j hj
        dsimp only
        by_cases hji : j = i
        · subst j
          rw [List.getD_eq_getElem _ _ hi_len]
          exact Function.update_self _ _ _
        · by_cases heq : sb.visBBase + vL.getD j 0 = sb.visBBase + u
          · rw [heq]; exact Function.update_self _ _ _
          · rw [Function.update_of_ne heq]; exact hcl_k j (by omega)
      · intro v hv hnotV
        dsimp only
        have hne : v ≠ u := fun h => hnotV (h ▸ huV)
        rw [Function.update_of_ne (by omega)]
        exact hvisOut_k v hv hnotV
      · intro a ha
        dsimp only
        have hne : a ≠ sb.visBBase + u := by rcases ha with h | h <;> omega
        rw [Function.update_of_ne hne]
        exact hfr_k a ha)
  obtain ⟨o, st', c, hr, hpost, hc⟩ := hloop st ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨hb', _, hr23', hcl', hvisOut', hfr'⟩
    refine ⟨st', c, hr, hb', hr23', fun v hv => ?_, hfr', ?_⟩
    · by_cases hvG : v ∈ G₀.V
      · obtain ⟨j, hj_lt, hj_eq⟩ := List.mem_iff_getElem.mp ((hVL_mem v).mpr hvG)
        have := hcl' j (hVL_len ▸ hj_lt)
        rwa [List.getD_eq_getElem _ _ hj_lt, hj_eq] at this
      · exact hvisOut' v hv hvG
    · dsimp [Expr.size] at hc
      omega

end

end MinCostFlow.LSF.Program
