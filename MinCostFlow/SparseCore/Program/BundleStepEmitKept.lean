module

public import MinCostFlow.SparseCore.Program.BundleStepEmitOneRun

/-!
# Phase 3 single-run tail and smaller-side split emission (`BundleStepEmitKept`)

Verifies `bundleStepEmitOneRunTailStmt`:
1. `bundleStepEmitKept_walk_runs`: walks `b`'s remaining DLL `L_b'` when `kept < moved`, writing
   kept tails to `batchPtr + writeOff + 5 + kt2` and kept heads to `hBuf + kh2`.
2. `bundleStepEmitOneRun_copyAndHdr_runs`: copies heads from `hBuf` to `batchPtr + writeOff + 5 + kt`,
   writes the 5-word header `[tag, b, nB, kt, kh]`, and updates `r21` and `r22`.
3. `bundleStepEmitOneRun_tail_runs`: chains the size updates, the `kept < moved` branch (tag `3` vs
   tag `2`), and `copyAndHdr`, proving `SmallUpdateAt` with `len = 5 + min L_b'.length xs.length`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

private lemma bundleStepEmitKept_walk_runs {w eCap prevBase nextBase p b batchPtr writeOff hBuf : ℕ}
    {pProg : Program} {ω : ℕ → Bool} {L : List ℕ} {st₀ : State}
    (hw16 : 16 ≤ 2 ^ w) (heCap_w : 2 * eCap < 2 ^ w)
    (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (hbat_w : batchPtr + writeOff + 5 + L.length < 2 ^ w)
    (hh_w : hBuf + L.length < 2 ^ w)
    (hbat_disj_next : batchPtr + writeOff + 5 + L.length ≤ nextBase ∨
      nextBase + 2 * eCap ≤ batchPtr + writeOff + 5)
    (hh_disj_next : hBuf + L.length ≤ nextBase ∨ nextBase + 2 * eCap ≤ hBuf)
    (hbat_disj_h : batchPtr + writeOff + 5 + L.length ≤ hBuf ∨
      hBuf + L.length ≤ batchPtr + writeOff + 5)
    (hdll : IsDoublyLinkedList st₀.mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L)
    (hr11 : st₀.regs 11 = nextBase) (hr20 : st₀.regs 20 = batchPtr) (hr21 : st₀.regs 21 = writeOff)
    (hr32 : st₀.regs 32 = hBuf) (hr33 : st₀.regs 33 = 0) (hr34 : st₀.regs 34 = 0)
    (hr35 : st₀.regs 35 = st₀.mem (bsHeadBase p + b)) :
    ∃ stW cW,
      Runs w pProg ω
        (.loop (.reg 35)
          (.assign 36 (.bin .sub (.reg 35) (.const 1)) ;;
           .cond (.bin .eq (.bin .mod (.reg 36) (.const 2)) (.const 0))
             (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
               (.bin .div (.reg 36) (.const 2)) ;;
              .assign 33 (.bin .add (.reg 33) (.const 1)))
             (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 36) (.const 2)) ;;
              .assign 34 (.bin .add (.reg 34) (.const 1))) ;;
           .assign 35 (.load (.bin .add (.reg 11) (.reg 36))))) st₀ .normal stW cW ∧
      (∀ r ≤ 32, stW.regs r = st₀.regs r) ∧
      stW.regs 33 = (keyTailEdges L).length ∧
      stW.regs 34 = (keyHeadEdges L).length ∧
      ListAt stW.mem (batchPtr + writeOff + 5) (keyTailEdges L) ∧
      ListAt stW.mem hBuf (keyHeadEdges L) ∧
      (∀ a, (a < batchPtr + writeOff + 5 ∨ batchPtr + writeOff + 5 + (keyTailEdges L).length ≤ a) →
        (a < hBuf ∨ hBuf + (keyHeadEdges L).length ≤ a) → stW.mem a = st₀.mem a) ∧
      cW ≤ 45 * L.length + 4 := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h5_w : 5 < 2 ^ w := by omega
  have hL_lt : ∀ k ∈ L, k < 2 * eCap := hdll.2.1
  let body : Stmt :=
    .assign 36 (.bin .sub (.reg 35) (.const 1)) ;;
    .cond (.bin .eq (.bin .mod (.reg 36) (.const 2)) (.const 0))
      (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
        (.bin .div (.reg 36) (.const 2)) ;;
       .assign 33 (.bin .add (.reg 33) (.const 1)))
      (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 36) (.const 2)) ;;
       .assign 34 (.bin .add (.reg 34) (.const 1))) ;;
    .assign 35 (.load (.bin .add (.reg 11) (.reg 36)))
  have hgo : ∀ rem i (hi : i ≤ L.length) (hrem : L.length - i = rem) (st : State),
      (∀ r ≤ 32, st.regs r = st₀.regs r) →
      st.regs 33 = (keyTailEdges (L.take i)).length →
      st.regs 34 = (keyHeadEdges (L.take i)).length →
      st.regs 35 = (if h : i < L.length then L[i]'h + 1 else 0) →
      ListAt st.mem (batchPtr + writeOff + 5) (keyTailEdges (L.take i)) →
      ListAt st.mem hBuf (keyHeadEdges (L.take i)) →
      (∀ a, (a < batchPtr + writeOff + 5 ∨ batchPtr + writeOff + 5 + (keyTailEdges (L.take i)).length ≤ a) →
        (a < hBuf ∨ hBuf + (keyHeadEdges (L.take i)).length ≤ a) → st.mem a = st₀.mem a) →
      ∃ stW cW,
        Runs w pProg ω (.loop (.reg 35) body) st .normal stW cW ∧
        (∀ r ≤ 32, stW.regs r = st₀.regs r) ∧
        stW.regs 33 = (keyTailEdges L).length ∧
        stW.regs 34 = (keyHeadEdges L).length ∧
        ListAt stW.mem (batchPtr + writeOff + 5) (keyTailEdges L) ∧
        ListAt stW.mem hBuf (keyHeadEdges L) ∧
        (∀ a, (a < batchPtr + writeOff + 5 ∨ batchPtr + writeOff + 5 + (keyTailEdges L).length ≤ a) →
          (a < hBuf ∨ hBuf + (keyHeadEdges L).length ≤ a) → stW.mem a = st₀.mem a) ∧
        cW ≤ 45 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro i hi hrem st hregs h33 h34 h35 hLt hLh hfr
      have hi_eq : i = L.length := by omega
      subst hi_eq
      rw [List.take_length] at h33 h34 hLt hLh hfr
      have h35_0 : st.regs 35 = 0 := by simpa using h35
      exact ⟨st, 2, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, h35_0], rfl, rfl, rfl⟩),
        hregs, h33, h34, hLt, hLh, hfr, by omega⟩
    | succ rem' ih =>
      intro i hi hrem st hregs h33 h34 h35 hLt hLh hfr
      have hi_lt : i < L.length := by omega
      set key := L[i]'hi_lt
      have hk_lt : key < 2 * eCap := hL_lt key (List.getElem_mem hi_lt)
      have h35_val : st.regs 35 = key + 1 := by simpa [hi_lt] using h35
      set kt := (keyTailEdges (L.take i)).length
      set kh := (keyHeadEdges (L.take i)).length
      have hkt_kh : kt + kh = i := by
        have := keyTailEdges_add_headEdges_length (L.take i)
        rw [List.length_take, Nat.min_eq_left (by omega)] at this; exact this
      have h11 : st.regs 11 = nextBase := (hregs 11 (by decide)).trans hr11
      have h20 : st.regs 20 = batchPtr := (hregs 20 (by decide)).trans hr20
      have h21 : st.regs 21 = writeOff := (hregs 21 (by decide)).trans hr21
      have h32 : st.regs 32 = hBuf := (hregs 32 (by decide)).trans hr32
      set st1 : State := { st with regs := Function.update st.regs 36 key }
      have ha36 : Runs w pProg ω (.assign 36 (.bin .sub (.reg 35) (.const 1))) st .normal st1 4 :=
        runs_assign_iff.mpr ⟨key, by
          simp [Expr.eval, BinOp.eval, h35_val, h1_w, show key < 2 ^ w by omega], rfl, rfl, rfl⟩
      have htake_s : L.take (i + 1) = L.take i ++ [key] := List.take_succ_eq_append_getElem hi_lt
      have hnext_val : st₀.mem (nextBase + key) = if h : i + 1 < L.length then L[i + 1]'h + 1 else 0 := by
        have hb := (hdll.2.2.2 i hi_lt).2
        by_cases hlt' : i + 1 < L.length
        · have hne : i + 1 ≠ L.length := by omega
          simp only [hne, ↓reduceIte, hlt', ↓reduceDIte] at hb ⊢
          rw [hb, List.getD_eq_getElem _ _ hlt']
        · have heq : i + 1 = L.length := by omega
          simp [heq, hb, key]
      have hstep_cond : ∃ st2 c2,
          Runs w pProg ω
            (.cond (.bin .eq (.bin .mod (.reg 36) (.const 2)) (.const 0))
              (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
                (.bin .div (.reg 36) (.const 2)) ;;
               .assign 33 (.bin .add (.reg 33) (.const 1)))
              (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 36) (.const 2)) ;;
               .assign 34 (.bin .add (.reg 34) (.const 1)))) st1 .normal st2 c2 ∧
          (∀ r ≤ 32, st2.regs r = st₀.regs r) ∧
          st2.regs 33 = (keyTailEdges (L.take (i + 1))).length ∧
          st2.regs 34 = (keyHeadEdges (L.take (i + 1))).length ∧
          st2.regs 36 = key ∧
          ListAt st2.mem (batchPtr + writeOff + 5) (keyTailEdges (L.take (i + 1))) ∧
          ListAt st2.mem hBuf (keyHeadEdges (L.take (i + 1))) ∧
          (∀ a, (a < batchPtr + writeOff + 5 ∨ batchPtr + writeOff + 5 + (keyTailEdges (L.take (i + 1))).length ≤ a) →
            (a < hBuf ∨ hBuf + (keyHeadEdges (L.take (i + 1))).length ≤ a) → st2.mem a = st₀.mem a) ∧
          c2 ≤ 28 := by
        by_cases heven : key % 2 = 0
        · have hkt_s : keyTailEdges (L.take (i + 1)) = keyTailEdges (L.take i) ++ [key / 2] := by
            simp [keyTailEdges, htake_s, heven]
          have hkh_s : keyHeadEdges (L.take (i + 1)) = keyHeadEdges (L.take i) := by
            simp [keyHeadEdges, htake_s, heven]
          set m2 := Function.update st.mem (batchPtr + writeOff + 5 + kt) (key / 2)
          set r33' := Function.update st1.regs 33 (kt + 1)
          have hst_t : Runs w pProg ω
              (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
                (.bin .div (.reg 36) (.const 2))) st1 .normal { st1 with mem := m2 } 11 :=
            runs_store_iff.mpr ⟨batchPtr + writeOff + 5 + kt, key / 2, by
              simp [Expr.eval, BinOp.eval, st1, h20, h21, h33, h5_w, kt,
                show batchPtr + writeOff < 2 ^ w by omega,
                show batchPtr + writeOff + 5 < 2 ^ w by omega,
                show batchPtr + writeOff + 5 + kt < 2 ^ w by omega],
              by simp [Expr.eval, BinOp.eval, st1, h2_w, show key / 2 < 2 ^ w by omega],
              rfl, rfl, by simp [Expr.size]⟩
          have ha33 : Runs w pProg ω (.assign 33 (.bin .add (.reg 33) (.const 1)))
              { st1 with mem := m2 } .normal { mem := m2, regs := r33', pos := st.pos } 4 :=
            runs_assign_iff.mpr ⟨kt + 1, by
              simp [Expr.eval, BinOp.eval, st1, h33, h1_w, kt, show kt + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
          refine ⟨{ mem := m2, regs := r33', pos := st.pos }, 5 + (11 + 4 + 1) + 1,
            runs_cond_iff.mpr ⟨1, 11 + 4 + 1, by
              simp [Expr.eval, BinOp.eval, st1, h2_w, h0_w, heven, h1_w],
              by simpa using bundle_runs_seq_normal hst_t ha33, by simp [Expr.size]⟩,
            fun r hr => by simp [r33', st1, show r ≠ 33 by omega, show r ≠ 36 by omega, hregs r hr],
            by simp [r33', hkt_s, kt], by simp [r33', st1, hkh_s, h34, kh], by simp [r33', st1],
            ?_, ?_, ?_, by omega⟩
          · rw [hkt_s]; intro q hq; simp only [List.length_append, List.length_singleton] at hq
            by_cases hql : q < kt
            · dsimp only [m2]; rw [Function.update_of_ne (by omega), List.getElem_append_left hql]
              exact hLt q hql
            · have hqeq : q = kt := by omega
              subst hqeq; simp [m2, kt]
          · rw [hkh_s]; intro q hq
            dsimp only [m2]; rw [Function.update_of_ne (by clear * - hbat_disj_h hkt_kh hi_lt hq; omega)]
            exact hLh q hq
          · intro a ha1 ha2; rw [hkt_s, List.length_append, List.length_singleton] at ha1; rw [hkh_s] at ha2
            dsimp only [m2]; rw [Function.update_of_ne (by omega)]
            exact hfr a (by omega) ha2
        · have h1 : key % 2 = 1 := by omega
          have hkt_s : keyTailEdges (L.take (i + 1)) = keyTailEdges (L.take i) := by
            simp [keyTailEdges, htake_s, h1]
          have hkh_s : keyHeadEdges (L.take (i + 1)) = keyHeadEdges (L.take i) ++ [key / 2] := by
            simp [keyHeadEdges, htake_s, h1]
          set m2 := Function.update st.mem (hBuf + kh) (key / 2)
          set r34' := Function.update st1.regs 34 (kh + 1)
          have hst_h : Runs w pProg ω
              (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 36) (.const 2)))
              st1 .normal { st1 with mem := m2 } 7 :=
            runs_store_iff.mpr ⟨hBuf + kh, key / 2, by
              simp [Expr.eval, BinOp.eval, st1, h32, h34, kh, show hBuf + kh < 2 ^ w by omega],
              by simp [Expr.eval, BinOp.eval, st1, h2_w, show key / 2 < 2 ^ w by omega],
              rfl, rfl, by simp [Expr.size]⟩
          have ha34 : Runs w pProg ω (.assign 34 (.bin .add (.reg 34) (.const 1)))
              { st1 with mem := m2 } .normal { mem := m2, regs := r34', pos := st.pos } 4 :=
            runs_assign_iff.mpr ⟨kh + 1, by
              simp [Expr.eval, BinOp.eval, st1, h34, h1_w, kh, show kh + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
          refine ⟨{ mem := m2, regs := r34', pos := st.pos }, 5 + (7 + 4 + 1) + 1,
            runs_cond_iff.mpr ⟨0, 7 + 4 + 1, by
              simp [Expr.eval, BinOp.eval, st1, h2_w, h0_w, h1, h1_w],
              by simpa using bundle_runs_seq_normal hst_h ha34, by simp [Expr.size]⟩,
            fun r hr => by simp [r34', st1, show r ≠ 34 by omega, show r ≠ 36 by omega, hregs r hr],
            by simp [r34', st1, hkt_s, h33, kt], by simp [r34', hkh_s, kh], by simp [r34', st1],
            ?_, ?_, ?_, by omega⟩
          · rw [hkt_s]; intro q hq
            dsimp only [m2]; rw [Function.update_of_ne (by clear * - hbat_disj_h hkt_kh hi_lt hq; omega)]
            exact hLt q hq
          · rw [hkh_s]; intro q hq; simp only [List.length_append, List.length_singleton] at hq
            by_cases hql : q < kh
            · dsimp only [m2]; rw [Function.update_of_ne (by omega), List.getElem_append_left hql]
              exact hLh q hql
            · have hqeq : q = kh := by omega
              subst hqeq; simp [m2, kh]
          · intro a ha1 ha2; rw [hkt_s] at ha1; rw [hkh_s, List.length_append, List.length_singleton] at ha2
            dsimp only [m2]; rw [Function.update_of_ne (by omega)]
            exact hfr a ha1 (by omega)
      obtain ⟨st2, c2, hrun2, hregs2, h33_2, h34_2, h36_2, hLt2, hLh2, hfr2, hc2⟩ := hstep_cond
      have hkt_kh_s : (keyTailEdges (L.take (i + 1))).length + (keyHeadEdges (L.take (i + 1))).length = i + 1 := by
        have := keyTailEdges_add_headEdges_length (L.take (i + 1))
        rw [List.length_take, Nat.min_eq_left (by omega)] at this; exact this
      have hm_next : st2.mem (nextBase + key) = if h : i + 1 < L.length then L[i + 1]'h + 1 else 0 := by
        rw [hfr2 (nextBase + key) (by clear * - hbat_disj_next hkt_kh_s hi_lt hk_lt; omega)
          (by clear * - hh_disj_next hkt_kh_s hi_lt hk_lt; omega)]
        exact hnext_val
      set nextVal := if h : i + 1 < L.length then L[i + 1]'h + 1 else 0
      set st3 : State := { st2 with regs := Function.update st2.regs 35 nextVal }
      have ha35 : Runs w pProg ω (.assign 35 (.load (.bin .add (.reg 11) (.reg 36)))) st2 .normal st3 5 :=
        runs_assign_iff.mpr ⟨nextVal, by
          simp [Expr.eval, BinOp.eval, (hregs2 11 (by decide)).trans hr11, h36_2,
            show nextBase + key < 2 ^ w by omega, hm_next, nextVal], rfl, rfl, rfl⟩
      have hbody_run : Runs w pProg ω body st .normal st3 (4 + (c2 + 5 + 1) + 1) :=
        bundle_runs_seq_normal ha36 (bundle_runs_seq_normal hrun2 ha35)
      obtain ⟨stW, cW, hrunW, hregsW, h33W, h34W, hLtW, hLhW, hfrW, hcW⟩ :=
        ih (i + 1) (by omega) (by omega) st3
          (fun r hr => by simp [st3, show r ≠ 35 by omega, hregs2 r hr])
          (by simp [st3, h33_2]) (by simp [st3, h34_2]) (by simp [st3, nextVal])
          hLt2 hLh2 hfr2
      refine ⟨stW, 1 + (4 + (c2 + 5 + 1) + 1) + cW + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨key + 1, st3, _, cW,
          by simp [Expr.eval, h35_val], Nat.succ_ne_zero key, hbody_run, hrunW, rfl⟩)),
        hregsW, h33W, h34W, hLtW, hLhW, hfrW, by omega⟩
  have hhd0 : st₀.regs 35 = if h : 0 < L.length then L[0]'h + 1 else 0 := by
    rw [hr35, hdll.2.2.1]
    cases L with
    | nil => simp
    | cons k ks => simp
  exact hgo L.length 0 (Nat.zero_le _) (Nat.sub_zero _) st₀ (fun _ _ => rfl)
    (by simpa [keyTailEdges] using hr33) (by simpa [keyHeadEdges] using hr34) hhd0
    (fun j hj => by simp [keyTailEdges] at hj) (fun j hj => by simp [keyHeadEdges] at hj)
    (fun _ _ _ => rfl)

private lemma bundleStepEmitOneRun_copyAndHdr_runs {w batchPtr writeOff updCnt b nB tag hBuf : ℕ}
    {pProg : Program} {ω : ℕ → Bool} {Lt Lh : List ℕ} {st₀ : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hbat_w : batchPtr + writeOff + 5 + (Lt.length + Lh.length) < 2 ^ w)
    (hupd_w : updCnt + 1 < 2 ^ w)
    (hh_w : hBuf + Lh.length < 2 ^ w)
    (hbat_disj_h : batchPtr + writeOff + 5 + (Lt.length + Lh.length) ≤ hBuf ∨
      hBuf + Lh.length ≤ batchPtr + writeOff)
    (hLt0 : ListAt st₀.mem (batchPtr + writeOff + 5) Lt)
    (hLh0 : ListAt st₀.mem hBuf Lh)
    (hr20 : st₀.regs 20 = batchPtr) (hr21 : st₀.regs 21 = writeOff) (hr22 : st₀.regs 22 = updCnt)
    (hr25 : st₀.regs 25 = b) (hr31 : st₀.regs 31 = nB) (hr32 : st₀.regs 32 = hBuf)
    (hr33 : st₀.regs 33 = Lt.length) (hr34 : st₀.regs 34 = Lh.length) (hr38 : st₀.regs 38 = tag) :
    ∃ stEnd cEnd,
      Runs w pProg ω
        (forRange 36 (.const 0) (.reg 34)
          (.store (.bin .add (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33)) (.reg 36))
            (.load (.bin .add (.reg 32) (.reg 36)))) ;;
         .store (.bin .add (.reg 20) (.reg 21)) (.reg 38) ;;
         .store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 1)) (.reg 25) ;;
         .store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 2)) (.reg 31) ;;
         .store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 3)) (.reg 33) ;;
         .store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 4)) (.reg 34) ;;
         .assign 21 (.bin .add (.bin .add (.bin .add (.reg 21) (.const 5)) (.reg 33)) (.reg 34)) ;;
         .assign 22 (.bin .add (.reg 22) (.const 1))) st₀ .normal stEnd cEnd ∧
      (∀ r ≤ 35, r ≠ 21 → r ≠ 22 → stEnd.regs r = st₀.regs r) ∧
      stEnd.regs 21 = writeOff + 5 + (Lt.length + Lh.length) ∧
      stEnd.regs 22 = updCnt + 1 ∧
      ListAt stEnd.mem (batchPtr + writeOff) ([tag, b, nB, Lt.length, Lh.length] ++ Lt ++ Lh) ∧
      (∀ a, (a < batchPtr + writeOff ∨ batchPtr + writeOff + 5 + (Lt.length + Lh.length) ≤ a) →
        stEnd.mem a = st₀.mem a) ∧
      cEnd ≤ 23 * Lh.length + 70 := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have h4_w : 4 < 2 ^ w := by omega
  have h5_w : 5 < 2 ^ w := by omega
  set kt := Lt.length
  set kh := Lh.length
  let copyBody : Stmt :=
    .store (.bin .add (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33)) (.reg 36))
      (.load (.bin .add (.reg 32) (.reg 36)))
  let copyInv : ℕ → Unit → State → Prop := fun j _ st =>
    (∀ r, r ≠ 36 → st.regs r = st₀.regs r) ∧ st.regs 36 = j ∧
    ListAt st.mem (batchPtr + writeOff + 5 + kt) (Lh.take j) ∧
    (∀ a, (a < batchPtr + writeOff + 5 + kt ∨ batchPtr + writeOff + 5 + kt + j ≤ a) → st.mem a = st₀.mem a)
  obtain ⟨stCp, cCp, _, hrunCp, ⟨hregsCp, _, hLhCp, hfrCp⟩, hcCp⟩ :=
    runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 36) (lo := .const 0) (hi := .reg 34)
      (body := copyBody) (fun _ _ => 0) copyInv (fun _ => 14) kh (by omega) (fun _ => by omega)
      (st₀ := st₀) (a₀ := ())
      ⟨by simp [Expr.eval, h0_w], ⟨fun r hr => by simp [hr], by simp,
        fun j hj => by simp at hj, fun _ _ => rfl⟩, rfl⟩
      (fun _ _ _ _ hI => hI.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, (hI.1 34 (by decide)).trans hr34])
      (fun j _ st hj ⟨hregsC, hr36C, hLhC, hfrC⟩ => by
        have hval_eq : st.mem (hBuf + j) = Lh[j]'hj := by
          rw [hfrC (hBuf + j) (by clear * - hbat_disj_h hj; omega)]; exact hLh0 j hj
        set st1 : State := { st with mem := Function.update st.mem (batchPtr + writeOff + 5 + kt + j) (Lh[j]'hj) }
        have hstC : Runs w pProg ω copyBody st .normal st1 14 :=
          runs_store_iff.mpr ⟨batchPtr + writeOff + 5 + kt + j, Lh[j]'hj, by
            simp [Expr.eval, BinOp.eval, (hregsC 20 (by decide)).trans hr20,
              (hregsC 21 (by decide)).trans hr21, (hregsC 33 (by decide)).trans hr33, hr36C, h5_w, kt,
              show batchPtr + writeOff < 2 ^ w by omega, show batchPtr + writeOff + 5 < 2 ^ w by omega,
              show batchPtr + writeOff + 5 + kt < 2 ^ w by omega,
              show batchPtr + writeOff + 5 + kt + j < 2 ^ w by omega],
            by simp [Expr.eval, BinOp.eval, (hregsC 32 (by decide)).trans hr32, hr36C,
              show hBuf + j < 2 ^ w by omega, hval_eq],
            rfl, rfl, by simp [Expr.size]⟩
        refine ⟨st1, 14, (), hstC, hr36C, ?_, rfl, by omega⟩
        refine ⟨fun r hr => by simp [st1, hr, hregsC r hr], by simp, ?_, ?_⟩
        · intro q hq
          rw [List.getElem_take]
          simp only [List.length_take] at hq
          by_cases hqj : q < j
          · dsimp only [st1]; rw [Function.update_of_ne (by omega)]
            have h := hLhC q (by simp; omega); rwa [List.getElem_take] at h
          · have hqeq : q = j := by omega
            simp [st1, hqeq]
        · intro a ha; dsimp only [st1]; rw [Function.update_of_ne (by omega)]; exact hfrC a (by omega))
  rw [List.take_length] at hLhCp
  have hrcCp : rangeCost (fun _ => 14) 0 kh = 14 * kh := by
    induction kh with
    | zero => simp [rangeCost]
    | succ m ih =>
      rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, ← rangeCost_zero_eq_range, ih]; ring
  simp only [Expr.size] at hcCp
  rw [hrcCp] at hcCp
  -- 5 header stores + r21 + r22
  have hCp20 : stCp.regs 20 = batchPtr := (hregsCp 20 (by decide)).trans hr20
  have hCp21 : stCp.regs 21 = writeOff := (hregsCp 21 (by decide)).trans hr21
  have hCp22 : stCp.regs 22 = updCnt := (hregsCp 22 (by decide)).trans hr22
  have hCp25 : stCp.regs 25 = b := (hregsCp 25 (by decide)).trans hr25
  have hCp31 : stCp.regs 31 = nB := (hregsCp 31 (by decide)).trans hr31
  have hCp33 : stCp.regs 33 = kt := (hregsCp 33 (by decide)).trans hr33
  have hCp34 : stCp.regs 34 = kh := (hregsCp 34 (by decide)).trans hr34
  have hCp38 : stCp.regs 38 = tag := (hregsCp 38 (by decide)).trans hr38
  let m1 := Function.update stCp.mem (batchPtr + writeOff) tag
  let m2 := Function.update m1 (batchPtr + writeOff + 1) b
  let m3 := Function.update m2 (batchPtr + writeOff + 2) nB
  let m4 := Function.update m3 (batchPtr + writeOff + 3) kt
  let m5 := Function.update m4 (batchPtr + writeOff + 4) kh
  let r21f := Function.update stCp.regs 21 (writeOff + 5 + (kt + kh))
  let r22f := Function.update r21f 22 (updCnt + 1)
  let stEnd : State := { mem := m5, regs := r22f, pos := stCp.pos }
  have hs1 : Runs w pProg ω (.store (.bin .add (.reg 20) (.reg 21)) (.reg 38))
      stCp .normal { stCp with mem := m1 } 5 :=
    runs_store_iff.mpr ⟨batchPtr + writeOff, tag,
      by simp [Expr.eval, BinOp.eval, hCp20, hCp21, show batchPtr + writeOff < 2 ^ w by omega],
      by simp [Expr.eval, hCp38], rfl, rfl, rfl⟩
  have hs2 : Runs w pProg ω (.store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 1)) (.reg 25))
      { stCp with mem := m1 } .normal { stCp with mem := m2 } 7 :=
    runs_store_iff.mpr ⟨batchPtr + writeOff + 1, b,
      by simp [Expr.eval, BinOp.eval, hCp20, hCp21, h1_w,
        show batchPtr + writeOff < 2 ^ w by omega, show batchPtr + writeOff + 1 < 2 ^ w by omega],
      by simp [Expr.eval, hCp25], rfl, rfl, by simp [Expr.size]⟩
  have hs3 : Runs w pProg ω (.store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 2)) (.reg 31))
      { stCp with mem := m2 } .normal { stCp with mem := m3 } 7 :=
    runs_store_iff.mpr ⟨batchPtr + writeOff + 2, nB,
      by simp [Expr.eval, BinOp.eval, hCp20, hCp21, h2_w,
        show batchPtr + writeOff < 2 ^ w by omega, show batchPtr + writeOff + 2 < 2 ^ w by omega],
      by simp [Expr.eval, hCp31], rfl, rfl, by simp [Expr.size]⟩
  have hs4 : Runs w pProg ω (.store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 3)) (.reg 33))
      { stCp with mem := m3 } .normal { stCp with mem := m4 } 7 :=
    runs_store_iff.mpr ⟨batchPtr + writeOff + 3, kt,
      by simp [Expr.eval, BinOp.eval, hCp20, hCp21, h3_w,
        show batchPtr + writeOff < 2 ^ w by omega, show batchPtr + writeOff + 3 < 2 ^ w by omega],
      by simp [Expr.eval, hCp33], rfl, rfl, by simp [Expr.size]⟩
  have hs5 : Runs w pProg ω (.store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 4)) (.reg 34))
      { stCp with mem := m4 } .normal { stCp with mem := m5 } 7 :=
    runs_store_iff.mpr ⟨batchPtr + writeOff + 4, kh,
      by simp [Expr.eval, BinOp.eval, hCp20, hCp21, h4_w,
        show batchPtr + writeOff < 2 ^ w by omega, show batchPtr + writeOff + 4 < 2 ^ w by omega],
      by simp [Expr.eval, hCp34], rfl, rfl, by simp [Expr.size]⟩
  have ha21 : Runs w pProg ω
      (.assign 21 (.bin .add (.bin .add (.bin .add (.reg 21) (.const 5)) (.reg 33)) (.reg 34)))
      { stCp with mem := m5 } .normal { mem := m5, regs := r21f, pos := stCp.pos } 8 :=
    runs_assign_iff.mpr ⟨writeOff + 5 + (kt + kh), by
      simp [Expr.eval, BinOp.eval, hCp21, hCp33, hCp34, h5_w,
        show writeOff + 5 < 2 ^ w by omega, show writeOff + 5 + kt < 2 ^ w by omega,
        show writeOff + 5 + kt + kh = writeOff + 5 + (kt + kh) by omega,
        show writeOff + 5 + (kt + kh) < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
  have ha22 : Runs w pProg ω (.assign 22 (.bin .add (.reg 22) (.const 1)))
      { mem := m5, regs := r21f, pos := stCp.pos } .normal stEnd 4 :=
    runs_assign_iff.mpr ⟨updCnt + 1, by
      simp [Expr.eval, BinOp.eval, r21f, hCp22, h1_w, hupd_w], rfl, rfl, rfl⟩
  have hm5_eq : ∀ a, (a < batchPtr + writeOff ∨ batchPtr + writeOff + 5 ≤ a) →
      stEnd.mem a = stCp.mem a := fun a ha => by
    dsimp only [stEnd, m5, m4, m3, m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  refine ⟨stEnd, _,
    bundle_runs_seq_normal hrunCp (bundle_runs_seq_normal hs1 (bundle_runs_seq_normal hs2
      (bundle_runs_seq_normal hs3 (bundle_runs_seq_normal hs4 (bundle_runs_seq_normal hs5
        (bundle_runs_seq_normal ha21 ha22)))))),
    fun r hr h21 h22 => by
      simp only [stEnd, r22f, r21f, Function.update_of_ne h22, Function.update_of_ne h21]
      exact hregsCp r (by omega),
    by simp [stEnd, r22f, r21f], by simp [stEnd, r22f], ?_,
    fun a ha => (hm5_eq a (by omega)).trans (hfrCp a (by omega)), by clear * - hcCp; omega⟩
  intro i hi
  simp only [List.length_append, List.length_cons, List.length_nil] at hi
  by_cases hi5 : i < 5
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
    interval_cases i <;> simp [stEnd, m5, m4, m3, m2, m1, Function.update_of_ne, kt, kh]
  · by_cases hit : i < 5 + kt
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      have haddr : batchPtr + writeOff + i = batchPtr + writeOff + 5 + (i - 5) := by omega
      rw [haddr, hm5_eq _ (Or.inr (by omega)), hfrCp _ (Or.inl (by omega))]
      simpa [kt] using hLt0 (i - 5) (by omega)
    · rw [List.getElem_append_right (by simp; omega)]
      have haddr : batchPtr + writeOff + i = batchPtr + writeOff + 5 + kt + (i - (5 + kt)) := by omega
      rw [haddr, hm5_eq _ (Or.inr (by omega))]
      convert hLhCp (i - (5 + kt)) (by omega) using 2
      simp [kt]; omega

/-- Full verification of `bundleStepEmitOneRunTailStmt`: updates `size[b]` and `size[nB]`, emits
tag `3` if `L_b'.length < xs.length` or tag `2` otherwise, producing `SmallUpdateAt` with length
`5 + min L_b'.length xs.length` and advancing `r4` by at most `2 * xs.length`. -/
theorem bundleStepEmitOneRun_tail_runs {w eCap p bunCap b nB batchPtr writeOff updCnt
    prevBase nextBase hCur : ℕ}
    {pProg : Program} {ω : ℕ → Bool}
    {B : BundleState} {xs : List End} {L_b0 L_b' : List ℕ} {stW : State}
    (hw16 : 16 ≤ 2 ^ w) (heCap_w : 2 * eCap < 2 ^ w)
    (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hbat_w : batchPtr + writeOff + 5 + xs.length < 2 ^ w)
    (hupd_w : updCnt + 1 < 2 ^ w)
    (hh_w : hCur + 2 * xs.length < 2 ^ w)
    (hL0_w : L_b0.length < 2 ^ w)
    (hV : B.vertices = Finset.range nB) (hb_lt : b < nB) (hnb_lt : nB < bunCap)
    (hbo_lt : ∀ x ∈ edgeEnds B.edges, B.bundleOf x < nB)
    (hxs_nd : xs.Nodup) (hxs_sub : ∀ x ∈ xs, x ∈ B.ends b)
    (hLbW_len : L_b'.length + xs.length = L_b0.length)
    (hLbW_mem : ∀ k, k ∈ L_b' ↔ endOfKey k ∈ B.ends b ∧ endOfKey k ∉ xs)
    (hbat_disj_blk : batchPtr + writeOff + 5 + xs.length ≤ p ∨
      p + bundleSlotBlockSize bunCap ≤ batchPtr + writeOff)
    (hbat_disj_next : batchPtr + writeOff + 5 + xs.length ≤ nextBase ∨
      nextBase + 2 * eCap ≤ batchPtr + writeOff)
    (hbat_disj_h : batchPtr + writeOff + 5 + xs.length ≤ hCur ∨
      hCur + 2 * xs.length ≤ batchPtr + writeOff)
    (hh_disj_blk : hCur + 2 * xs.length ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ hCur)
    (hh_disj_next : hCur + 2 * xs.length ≤ nextBase ∨ nextBase + 2 * eCap ≤ hCur)
    (hblk_prev : p + bundleSlotBlockSize bunCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ p)
    (hblk_next : p + bundleSlotBlockSize bunCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ p)
    (hdll_bW : IsDoublyLinkedList stW.mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L_b')
    (hsz_bW : stW.mem (bsSizeBase p bunCap + b) = L_b0.length)
    (hLtW : ListAt stW.mem (batchPtr + writeOff + 5) (runTailEdges xs))
    (hLhW : ListAt stW.mem hCur (runHeadEdges xs))
    (hr7W : stW.regs 7 = p) (hr8W : stW.regs 8 = bunCap) (hr11W : stW.regs 11 = nextBase)
    (hr20W : stW.regs 20 = batchPtr) (hr21W : stW.regs 21 = writeOff) (hr22W : stW.regs 22 = updCnt)
    (hr25W : stW.regs 25 = b) (hr31W : stW.regs 31 = nB) (hr32W : stW.regs 32 = hCur)
    (hr33W : stW.regs 33 = (runTailEdges xs).length)
    (hr34W : stW.regs 34 = (runHeadEdges xs).length) :
    let len := 5 + min L_b'.length xs.length
    ∃ stEnd cEnd hEnd,
      Runs w pProg ω bundleStepEmitOneRunTailStmt stW .normal stEnd cEnd ∧
      (∀ r ≤ 31, r ≠ 4 → r ≠ 21 → r ≠ 22 → stEnd.regs r = stW.regs r) ∧
      stEnd.regs 4 = hEnd ∧ hCur + (runHeadEdges xs).length ≤ hEnd ∧ hEnd ≤ hCur + 2 * xs.length ∧
      stEnd.regs 21 = writeOff + len ∧
      stEnd.regs 22 = updCnt + 1 ∧
      stEnd.mem (bsSizeBase p bunCap + b) = L_b0.length - xs.length ∧
      stEnd.mem (bsSizeBase p bunCap + nB) = xs.length ∧
      SmallUpdateAt stEnd.mem (batchPtr + writeOff) B.graph (oneRunUpdate b nB xs) len ∧
      (∀ a, a ≠ bsSizeBase p bunCap + nB → a ≠ bsSizeBase p bunCap + b →
        (a < batchPtr + writeOff ∨ batchPtr + writeOff + len ≤ a) →
        (a < hCur + (runHeadEdges xs).length ∨ hEnd ≤ a) →
        stEnd.mem a = stW.mem a) ∧
      cEnd ≤ 75 * xs.length + 140 := by
  intro len
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  set kt := (runTailEdges xs).length
  set kh := (runHeadEdges xs).length
  have hkt_kh : kt + kh = xs.length := runTailEdges_add_headEdges_length xs
  have hkept_eq : L_b0.length - xs.length = L_b'.length := by omega
  have hbat_b' : batchPtr + writeOff + 5 + xs.length ≤ p ∨ p + (3 + 6 * bunCap) ≤ batchPtr + writeOff := hbat_disj_blk
  have hh_b' : hCur + 2 * xs.length ≤ p ∨ p + (3 + 6 * bunCap) ≤ hCur := hh_disj_blk
  have hblk_p' : p + (3 + 6 * bunCap) ≤ prevBase ∨ prevBase + 2 * eCap ≤ p := hblk_prev
  have hblk_n' : p + (3 + 6 * bunCap) ≤ nextBase ∨ nextBase + 2 * eCap ≤ p := hblk_next
  -- Prefix: 5 statements (`r4`, `r36 = &size[b]`, `r37 = kept`, `size[b] := kept`, `size[nB] := moved`)
  let r4 := Function.update stW.regs 4 (hCur + kh)
  let r36 := Function.update r4 36 (bsSizeBase p bunCap + b)
  let r37 := Function.update r36 37 L_b'.length
  let m1 := Function.update stW.mem (bsSizeBase p bunCap + b) L_b'.length
  let m2 := Function.update m1 (bsSizeBase p bunCap + nB) xs.length
  let stP : State := { mem := m2, regs := r37, pos := stW.pos }
  have ha4 : Runs w pProg ω (.assign 4 (.bin .add (.reg 32) (.reg 34))) stW .normal { stW with regs := r4 } 4 :=
    runs_assign_iff.mpr ⟨hCur + kh, by simp [Expr.eval, BinOp.eval, hr32W, hr34W, kh, show hCur + kh < 2 ^ w by omega], rfl, rfl, rfl⟩
  have ha36 : Runs w pProg ω
      (.assign 36 (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 8)) (.reg 25)))
      { stW with regs := r4 } .normal { stW with regs := r36 } 8 :=
    runs_assign_iff.mpr ⟨bsSizeBase p bunCap + b, by
      simp [Expr.eval, BinOp.eval, r4, hr7W, hr8W, hr25W, h3_w, bsSizeBase,
        show p + 3 < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
        show p + 3 + bunCap < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
        show p + 3 + bunCap + b < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega],
      rfl, rfl, by simp [Expr.size]⟩
  have ha37 : Runs w pProg ω (.assign 37 (.bin .sub (.load (.reg 36)) (.bin .add (.reg 33) (.reg 34))))
      { stW with regs := r36 } .normal { stW with regs := r37 } 7 :=
    runs_assign_iff.mpr ⟨L_b'.length, by
      simp [Expr.eval, BinOp.eval, r36, r4, hr33W, hr34W, hsz_bW, kt, kh, hkt_kh, hkept_eq,
        show xs.length < 2 ^ w by omega, show L_b'.length < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hs1 : Runs w pProg ω (.store (.reg 36) (.reg 37))
      { stW with regs := r37 } .normal { mem := m1, regs := r37, pos := stW.pos } 3 :=
    runs_store_iff.mpr ⟨bsSizeBase p bunCap + b, L_b'.length,
      by simp [Expr.eval, r37, r36], by simp [Expr.eval, r37], rfl, rfl, rfl⟩
  have hs2 : Runs w pProg ω
      (.store (.bin .add (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 8)) (.reg 31))
        (.bin .add (.reg 33) (.reg 34)))
      { mem := m1, regs := r37, pos := stW.pos } .normal stP 11 :=
    runs_store_iff.mpr ⟨bsSizeBase p bunCap + nB, xs.length, by
      simp [Expr.eval, BinOp.eval, r37, r36, r4, hr7W, hr8W, hr31W, h3_w, bsSizeBase,
        show p + 3 < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
        show p + 3 + bunCap < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
        show p + 3 + bunCap + nB < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega],
      by simp [Expr.eval, BinOp.eval, r37, r36, r4, hr33W, hr34W, kt, kh, hkt_kh,
        show xs.length < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hm2_eq : ∀ a, a ≠ bsSizeBase p bunCap + nB → a ≠ bsSizeBase p bunCap + b →
      stP.mem a = stW.mem a := fun a h1 h2 => by
    dsimp only [stP, m2, m1]; rw [Function.update_of_ne h1, Function.update_of_ne h2]
  have hP_r : ∀ r ≤ 35, r ≠ 4 → stP.regs r = stW.regs r := fun r hr h4 => by
    simp [stP, r37, r36, r4, h4, show r ≠ 37 by omega, show r ≠ 36 by omega]
  -- Branch on `L_b'.length < xs.length`
  by_cases hlt : L_b'.length < xs.length
  · -- True branch: walk `b`'s DLL and emit tag 3 (`len = 5 + L_b'.length`)
    have hlen_eq : len = 5 + L_b'.length := by simp [len, Nat.min_eq_left (le_of_lt hlt)]
    have hdll_P : IsDoublyLinkedList stP.mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L_b' :=
      hdll_bW.of_agree
        (hm2_eq _ (by unfold bsHeadBase bsSizeBase; omega) (by unfold bsHeadBase bsSizeBase; omega))
        (fun k hk => hm2_eq _ (by have := hdll_bW.2.1 k hk; unfold bsSizeBase; clear * - hblk_p' this hnb_lt; omega)
          (by have := hdll_bW.2.1 k hk; unfold bsSizeBase; clear * - hblk_p' this hb_lt hnb_lt; omega))
        (fun k hk => hm2_eq _ (by have := hdll_bW.2.1 k hk; unfold bsSizeBase; clear * - hblk_n' this hnb_lt; omega)
          (by have := hdll_bW.2.1 k hk; unfold bsSizeBase; clear * - hblk_n' this hb_lt hnb_lt; omega))
    -- 4 assigns before walk
    let r32k := Function.update stP.regs 32 (hCur + kh)
    let r33k := Function.update r32k 33 0
    let r34k := Function.update r33k 34 0
    let r35k := Function.update r34k 35 (stP.mem (bsHeadBase p + b))
    let stK0 : State := { stP with regs := r35k }
    have ha32k : Runs w pProg ω (.assign 32 (.reg 4)) stP .normal { stP with regs := r32k } 2 :=
      runs_assign_iff.mpr ⟨hCur + kh, by simp [Expr.eval, stP, r37, r36, r4], rfl, rfl, rfl⟩
    have ha33k : Runs w pProg ω (.assign 33 (.const 0)) { stP with regs := r32k } .normal { stP with regs := r33k } 2 :=
      runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
    have ha34k : Runs w pProg ω (.assign 34 (.const 0)) { stP with regs := r33k } .normal { stP with regs := r34k } 2 :=
      runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
    have ha35k : Runs w pProg ω (.assign 35 (.load (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25))))
        { stP with regs := r34k } .normal stK0 7 :=
      runs_assign_iff.mpr ⟨stP.mem (bsHeadBase p + b), by
        simp [Expr.eval, BinOp.eval, r34k, r33k, r32k, hP_r 7 (by decide) (by decide), hr7W,
          hP_r 25 (by decide) (by decide), hr25W, h3_w, bsHeadBase,
          show p + 3 < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
          show p + 3 + b < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega],
        rfl, rfl, by simp [Expr.size]⟩
    obtain ⟨stKW, cKW, hrunKW, hregsKW, hr33KW, hr34KW, hLtKW, hLhKW, hfrKW, hcKW⟩ :=
      bundleStepEmitKept_walk_runs (pProg := pProg) (ω := ω) (L := L_b')
        (batchPtr := batchPtr) (writeOff := writeOff) (hBuf := hCur + kh) (st₀ := stK0)
        hw16 heCap_w hnext_w (by omega) (by omega)
        (by clear * - hbat_disj_next hlt; omega) (by clear * - hh_disj_next hlt hkt_kh; omega)
        (by clear * - hbat_disj_h hlt hkt_kh; omega) hdll_P
        (by simp [stK0, r35k, r34k, r33k, r32k, hP_r 11 (by decide) (by decide), hr11W])
        (by simp [stK0, r35k, r34k, r33k, r32k, hP_r 20 (by decide) (by decide), hr20W])
        (by simp [stK0, r35k, r34k, r33k, r32k, hP_r 21 (by decide) (by decide), hr21W])
        (by simp [stK0, r35k, r34k, r33k, r32k]) (by simp [stK0, r35k, r34k, r33k])
        (by simp [stK0, r35k, r34k]) (by simp [stK0, r35k])
    set kt2 := (keyTailEdges L_b').length
    set kh2 := (keyHeadEdges L_b').length
    have hkt2_kh2 : kt2 + kh2 = L_b'.length := keyTailEdges_add_headEdges_length L_b'
    let r4k := Function.update stKW.regs 4 (hCur + kh + kh2)
    let r38k := Function.update r4k 38 3
    let stK1 : State := { stKW with regs := r38k }
    have ha4k : Runs w pProg ω (.assign 4 (.bin .add (.reg 32) (.reg 34)))
        stKW .normal { stKW with regs := r4k } 4 :=
      runs_assign_iff.mpr ⟨hCur + kh + kh2, by
        simp [Expr.eval, BinOp.eval, hregsKW 32 (by decide), stK0, r35k, r34k, r33k, r32k, hr34KW,
          kh2, show hCur + kh + kh2 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have ha38k : Runs w pProg ω (.assign 38 (.const 3)) { stKW with regs := r4k } .normal stK1 2 :=
      runs_assign_iff.mpr ⟨3, by simp [Expr.eval, h3_w], rfl, rfl, rfl⟩
    have hthen_run :=
      bundle_runs_seq_normal ha32k (bundle_runs_seq_normal ha33k (bundle_runs_seq_normal ha34k
        (bundle_runs_seq_normal ha35k (bundle_runs_seq_normal hrunKW (bundle_runs_seq_normal ha4k ha38k)))))
    have hcond_run : ∀ sElse : Stmt, Runs w pProg ω (.cond (.bin .lt (.reg 37) (.bin .add (.reg 33) (.reg 34))) _ sElse)
        stP .normal stK1 (5 + (2 + (2 + (2 + (7 + (cKW + (4 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) := fun _ =>
      runs_cond_iff.mpr ⟨1, _, by
        simp [Expr.eval, BinOp.eval, stP, r37, r36, r4, hr33W, hr34W, kt, kh, hkt_kh, hlt,
          show xs.length < 2 ^ w by omega, h1_w],
        by simpa using hthen_run, by simp [Expr.size]⟩
    obtain ⟨stEnd, cCp, hrunCp, hregsEnd, hr21End, hr22End, hListEnd, hfrEnd, hcCp⟩ :=
      bundleStepEmitOneRun_copyAndHdr_runs (pProg := pProg) (ω := ω) (b := b) (nB := nB)
        (batchPtr := batchPtr) (writeOff := writeOff) (updCnt := updCnt)
        (Lt := keyTailEdges L_b') (Lh := keyHeadEdges L_b') (tag := 3) (hBuf := hCur + kh) (st₀ := stK1)
        hw16 (by omega) hupd_w (by omega) (by clear * - hbat_disj_h hlt hkt_kh hkt2_kh2; omega)
        hLtKW hLhKW
        (by simp [stK1, r38k, r4k, hregsKW 20 (by decide), stK0, r35k, r34k, r33k, r32k, hP_r 20 (by decide) (by decide), hr20W])
        (by simp [stK1, r38k, r4k, hregsKW 21 (by decide), stK0, r35k, r34k, r33k, r32k, hP_r 21 (by decide) (by decide), hr21W])
        (by simp [stK1, r38k, r4k, hregsKW 22 (by decide), stK0, r35k, r34k, r33k, r32k, hP_r 22 (by decide) (by decide), hr22W])
        (by simp [stK1, r38k, r4k, hregsKW 25 (by decide), stK0, r35k, r34k, r33k, r32k, hP_r 25 (by decide) (by decide), hr25W])
        (by simp [stK1, r38k, r4k, hregsKW 31 (by decide), stK0, r35k, r34k, r33k, r32k, hP_r 31 (by decide) (by decide), hr31W])
        (by simp [stK1, r38k, r4k, hregsKW 32 (by decide), stK0, r35k, r34k, r33k, r32k])
        (by simp [stK1, r38k, r4k, hr33KW, kt2]) (by simp [stK1, r38k, r4k, hr34KW, kh2]) (by simp [stK1, r38k])
    have hfull : Runs w pProg ω bundleStepEmitOneRunTailStmt stW .normal stEnd _ :=
      bundle_runs_seq_normal ha4 (bundle_runs_seq_normal ha36
        (bundle_runs_seq_normal ha37 (bundle_runs_seq_normal hs1 (bundle_runs_seq_normal hs2
          (bundle_runs_seq_normal (hcond_run _) hrunCp)))))
    refine ⟨stEnd, _, hCur + kh + kh2, hfull,
      fun r hr h4 h21 h22 => by
        rw [hregsEnd r (by omega) h21 h22]
        simp [stK1, r38k, r4k, h4, show r ≠ 38 by omega, hregsKW r (by omega), stK0,
          r35k, r34k, r33k, r32k, show r ≠ 35 by omega, show r ≠ 34 by omega, show r ≠ 33 by omega,
          show r ≠ 32 by omega, hP_r r (by omega) h4],
      by rw [hregsEnd 4 (by decide) (by decide) (by decide)]; simp [stK1, r38k, r4k],
      by omega, by omega, by rw [hr21End, hkt2_kh2, hlen_eq]; omega, hr22End,
      by rw [hfrEnd _ (by unfold bsSizeBase; clear * - hbat_b' hlt hb_lt hnb_lt hkt2_kh2; omega),
             hfrKW _ (by unfold bsSizeBase; clear * - hbat_b' hlt hb_lt hnb_lt hkt2_kh2; omega)
               (by unfold bsSizeBase; clear * - hh_b' hlt hb_lt hnb_lt hkt_kh hkt2_kh2; omega)]
         simp [stK0, stP, m2, m1, Function.update_of_ne (show bsSizeBase p bunCap + b ≠ bsSizeBase p bunCap + nB by unfold bsSizeBase; omega), hkept_eq],
      by rw [hfrEnd _ (by unfold bsSizeBase; clear * - hbat_b' hlt hnb_lt hkt2_kh2; omega),
             hfrKW _ (by unfold bsSizeBase; clear * - hbat_b' hlt hnb_lt hkt2_kh2; omega)
               (by unfold bsSizeBase; clear * - hh_b' hlt hnb_lt hkt_kh hkt2_kh2; omega)]
         simp [stK0, stP, m2],
      oneRunUpdate_smallUpdateAt_kept hV hb_lt hbo_lt hxs_nd hxs_sub hdll_bW.1 hLbW_mem hlt hListEnd,
      fun a ha1 ha2 haBat haH => by
        rw [hfrEnd a (by rw [hlen_eq] at haBat; clear * - haBat hkt2_kh2; omega),
            hfrKW a (by rw [hlen_eq] at haBat; clear * - haBat hkt2_kh2; omega)
              (by clear * - haH; omega)]
        exact hm2_eq a ha1 ha2,
      by clear * - hcKW hcCp hlt hkt2_kh2; omega⟩
  · -- False branch: keep moved buffers and emit tag 2 (`len = 5 + xs.length`)
    have hle : xs.length ≤ L_b'.length := by omega
    have hlen_eq : len = 5 + xs.length := by simp [len, Nat.min_eq_right hle]
    let stE0 : State := { stP with regs := Function.update stP.regs 38 2 }
    have ha38 : Runs w pProg ω (.assign 38 (.const 2)) stP .normal stE0 2 :=
      runs_assign_iff.mpr ⟨2, by simp [Expr.eval, h2_w], rfl, rfl, rfl⟩
    have hcond_run : ∀ sThen : Stmt, Runs w pProg ω (.cond (.bin .lt (.reg 37) (.bin .add (.reg 33) (.reg 34))) sThen (.assign 38 (.const 2)))
        stP .normal stE0 8 := fun _ =>
      runs_cond_iff.mpr ⟨0, 2, by
        simp [Expr.eval, BinOp.eval, stP, r37, r36, r4, hr33W, hr34W, kt, kh, hkt_kh, hlt,
          show xs.length < 2 ^ w by omega],
        by simpa using ha38, by simp [Expr.size]⟩
    have hLtP : ListAt stE0.mem (batchPtr + writeOff + 5) (runTailEdges xs) := fun i hi => by
      dsimp only [stE0]
      rw [hm2_eq _ (by unfold bsSizeBase; clear * - hbat_b' hkt_kh hi hnb_lt; omega)
        (by unfold bsSizeBase; clear * - hbat_b' hkt_kh hi hb_lt hnb_lt; omega)]
      exact hLtW i hi
    have hLhP : ListAt stE0.mem hCur (runHeadEdges xs) := fun i hi => by
      dsimp only [stE0]
      rw [hm2_eq _ (by unfold bsSizeBase; clear * - hh_b' hkt_kh hi hnb_lt; omega)
        (by unfold bsSizeBase; clear * - hh_b' hkt_kh hi hb_lt hnb_lt; omega)]
      exact hLhW i hi
    obtain ⟨stEnd, cCp, hrunCp, hregsEnd, hr21End, hr22End, hListEnd, hfrEnd, hcCp⟩ :=
      bundleStepEmitOneRun_copyAndHdr_runs (pProg := pProg) (ω := ω) (b := b) (nB := nB)
        (batchPtr := batchPtr) (writeOff := writeOff) (updCnt := updCnt)
        (Lt := runTailEdges xs) (Lh := runHeadEdges xs) (tag := 2) (hBuf := hCur) (st₀ := stE0)
        hw16 (by omega) hupd_w (by omega) (by clear * - hbat_disj_h hkt_kh; omega)
        hLtP hLhP
        (by simp [stE0, hP_r 20 (by decide) (by decide), hr20W])
        (by simp [stE0, hP_r 21 (by decide) (by decide), hr21W])
        (by simp [stE0, hP_r 22 (by decide) (by decide), hr22W])
        (by simp [stE0, hP_r 25 (by decide) (by decide), hr25W])
        (by simp [stE0, hP_r 31 (by decide) (by decide), hr31W])
        (by simp [stE0, hP_r 32 (by decide) (by decide), hr32W])
        (by simp [stE0, hP_r 33 (by decide) (by decide), hr33W, kt])
        (by simp [stE0, hP_r 34 (by decide) (by decide), hr34W, kh])
        (by simp [stE0])
    have hfull : Runs w pProg ω bundleStepEmitOneRunTailStmt stW .normal stEnd _ :=
      bundle_runs_seq_normal ha4 (bundle_runs_seq_normal ha36
        (bundle_runs_seq_normal ha37 (bundle_runs_seq_normal hs1 (bundle_runs_seq_normal hs2
          (bundle_runs_seq_normal (hcond_run _) hrunCp)))))
    refine ⟨stEnd, _, hCur + kh, hfull,
      fun r hr h4 h21 h22 => by
        rw [hregsEnd r (by omega) h21 h22]
        simp [stE0, show r ≠ 38 by omega, hP_r r (by omega) h4],
      by rw [hregsEnd 4 (by decide) (by decide) (by decide)]; simp [stE0, stP, r37, r36, r4],
      le_refl _, by omega, by rw [hr21End, hkt_kh, hlen_eq]; omega, hr22End,
      by rw [hfrEnd _ (by unfold bsSizeBase; clear * - hbat_b' hkt_kh hb_lt hnb_lt; omega)]
         simp [stE0, stP, m2, m1, Function.update_of_ne (show bsSizeBase p bunCap + b ≠ bsSizeBase p bunCap + nB by unfold bsSizeBase; omega), hkept_eq],
      by rw [hfrEnd _ (by unfold bsSizeBase; clear * - hbat_b' hkt_kh hnb_lt; omega)]
         simp [stE0, stP, m2],
      oneRunUpdate_smallUpdateAt_moved hV hb_lt hbo_lt hxs_nd hxs_sub hdll_bW.1 hLbW_mem hle hListEnd,
      fun a ha1 ha2 haBat _ => by
        rw [hfrEnd a (by rw [hlen_eq] at haBat; clear * - haBat hkt_kh; omega)]
        exact hm2_eq a ha1 ha2,
      by clear * - hcCp hkt_kh; omega⟩

end

end MinCostFlow.SparseCore.Program
