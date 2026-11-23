module

public import MinCostFlow.SparseCore.Program.BundleStepEmitModel

/-!
# Inner while-loop verification for one split run (`BundleStepEmitOneRun`)

Verifies `runs_while_oneRun`, the inner `.loop (.reg 35)` of `bundleStepEmitOneRunStmt` that
erases each end of one maximal same-vertex run `xs` from bundle `b`, pushes it onto fresh bundle
`nB`, updates `endBundle[key] := nB`, and separates tail edges into `batchPtr + writeOff + 5`
and head edges into `headBuf`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

lemma runs_while_oneRun {w eCap p bunCap b nB degB packArr batchPtr writeOff idx vCur
    prevBase nextBase endBundleBase headBuf : ℕ}
    {pProg : Program} {bDllPush bDllErase : ℕ} {ω : ℕ → Bool}
    {B : BundleState} {L_b0 : List ℕ} {xs : List End}
    (hpPush : pProg.HasAt bDllPush [bundleDllPushStmt])
    (hpErase : pProg.HasAt bDllErase [bundleDllEraseStmt])
    (hw16 : 16 ≤ 2 ^ w)
    (_heCap_w : 2 * eCap < 2 ^ w) (h2e_pos : 0 < 2 * eCap)
    (hpk_bound : (vCur + 1) * (2 * eCap) ≤ 2 ^ w)
    (hprev_w : prevBase + 2 * eCap < 2 ^ w) (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (heb_w : endBundleBase + 2 * eCap < 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hpack_w : packArr + degB < 2 ^ w)
    (hbat_w : batchPtr + writeOff + 5 + xs.length < 2 ^ w)
    (hh_w : headBuf + xs.length < 2 ^ w)
    (hb_lt : b < nB) (hnb_lt : nB < bunCap)
    (hidx_le : idx + xs.length ≤ degB)
    (hxs_nd : xs.Nodup) (hxs_sub : ∀ x ∈ xs, x ∈ B.ends b)
    (hE_lt : ∀ e ∈ B.edges, e < eCap)
    (_hL0_nd : L_b0.Nodup) (hL0_lt : ∀ k ∈ L_b0, k < 2 * eCap)
    (hL0_mem : ∀ k, k ∈ L_b0 ↔ endOfKey k ∈ B.ends b)
    (hprev_next : prevBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ prevBase)
    (hblk_prev : p + bundleSlotBlockSize bunCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ p)
    (hblk_next : p + bundleSlotBlockSize bunCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ p)
    (heb_prev : endBundleBase + 2 * eCap ≤ prevBase ∨ prevBase + 2 * eCap ≤ endBundleBase)
    (heb_next : endBundleBase + 2 * eCap ≤ nextBase ∨ nextBase + 2 * eCap ≤ endBundleBase)
    (heb_blk : endBundleBase + 2 * eCap ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ endBundleBase)
    (hpack_disj_blk : packArr + degB ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ packArr)
    (hpack_disj_prev : packArr + degB ≤ prevBase ∨ prevBase + 2 * eCap ≤ packArr)
    (hpack_disj_next : packArr + degB ≤ nextBase ∨ nextBase + 2 * eCap ≤ packArr)
    (hpack_disj_eb : packArr + degB ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ packArr)
    (hpack_disj_bat : packArr + degB ≤ batchPtr + writeOff + 5 ∨
      batchPtr + writeOff + 5 + xs.length ≤ packArr)
    (hpack_disj_h : packArr + degB ≤ headBuf ∨ headBuf + xs.length ≤ packArr)
    (hbat_disj_blk : batchPtr + writeOff + 5 + xs.length ≤ p ∨
      p + bundleSlotBlockSize bunCap ≤ batchPtr + writeOff + 5)
    (hbat_disj_prev : batchPtr + writeOff + 5 + xs.length ≤ prevBase ∨
      prevBase + 2 * eCap ≤ batchPtr + writeOff + 5)
    (hbat_disj_next : batchPtr + writeOff + 5 + xs.length ≤ nextBase ∨
      nextBase + 2 * eCap ≤ batchPtr + writeOff + 5)
    (hbat_disj_eb : batchPtr + writeOff + 5 + xs.length ≤ endBundleBase ∨
      endBundleBase + 2 * eCap ≤ batchPtr + writeOff + 5)
    (hbat_disj_h : batchPtr + writeOff + 5 + xs.length ≤ headBuf ∨
      headBuf + xs.length ≤ batchPtr + writeOff + 5)
    (hh_disj_blk : headBuf + xs.length ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ headBuf)
    (hh_disj_prev : headBuf + xs.length ≤ prevBase ∨ prevBase + 2 * eCap ≤ headBuf)
    (hh_disj_next : headBuf + xs.length ≤ nextBase ∨ nextBase + 2 * eCap ≤ headBuf)
    (hh_disj_eb : headBuf + xs.length ≤ endBundleBase ∨ endBundleBase + 2 * eCap ≤ headBuf)
    {st₀ : State}
    (hpack_in : ∀ t (ht : t < xs.length),
      st₀.mem (packArr + (idx + t)) = packEndKey eCap vCur (endKey xs[t]))
    (hpack_end : idx + xs.length < degB →
      st₀.mem (packArr + (idx + xs.length)) / (2 * eCap) ≠ vCur ∧
      st₀.mem (packArr + (idx + xs.length)) < 2 ^ w)
    (hdll_b0 : IsDoublyLinkedList st₀.mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L_b0)
    (hdll_n0 : IsDoublyLinkedList st₀.mem prevBase nextBase (bsHeadBase p + nB) (2 * eCap) [])
    (hr6 : st₀.regs 6 = 2 * eCap) (hr7 : st₀.regs 7 = p) (hr9 : st₀.regs 9 = endBundleBase)
    (hr10 : st₀.regs 10 = prevBase) (hr11 : st₀.regs 11 = nextBase)
    (hr20 : st₀.regs 20 = batchPtr) (hr21 : st₀.regs 21 = writeOff)
    (hr25 : st₀.regs 25 = b) (hr26 : st₀.regs 26 = degB) (hr27 : st₀.regs 27 = packArr)
    (hr29 : st₀.regs 29 = idx) (hr30 : st₀.regs 30 = vCur) (hr31 : st₀.regs 31 = nB)
    (hr32 : st₀.regs 32 = headBuf) (hr33 : st₀.regs 33 = 0) (hr34 : st₀.regs 34 = 0)
    (hr35 : st₀.regs 35 = 1) :
    ∃ stEnd cEnd L_b' L_new',
      Runs w pProg ω
        (.loop (.reg 35)
          (.cond (.bin .lt (.reg 29) (.reg 26))
            (.assign 36 (.load (.bin .add (.reg 27) (.reg 29))) ;;
             .cond (.bin .eq (.bin .div (.reg 36) (.reg 6)) (.reg 30))
               (.assign 37 (.bin .mod (.reg 36) (.reg 6)) ;;
                .call 38 bDllErase [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25), .reg 37] ;;
                .call 38 bDllPush [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 31), .reg 37] ;;
                .store (.bin .add (.reg 9) (.reg 37)) (.reg 31) ;;
                .cond (.bin .eq (.bin .mod (.reg 37) (.const 2)) (.const 0))
                  (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
                    (.bin .div (.reg 37) (.const 2)) ;;
                   .assign 33 (.bin .add (.reg 33) (.const 1)))
                  (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 37) (.const 2)) ;;
                   .assign 34 (.bin .add (.reg 34) (.const 1))) ;;
                .assign 29 (.bin .add (.reg 29) (.const 1)))
               (.assign 35 (.const 0)))
            (.assign 35 (.const 0))))
        st₀ .normal stEnd cEnd ∧
      (∀ r ≤ 32, r ≠ 29 → stEnd.regs r = st₀.regs r) ∧
      stEnd.regs 29 = idx + xs.length ∧
      stEnd.regs 33 = (runTailEdges xs).length ∧
      stEnd.regs 34 = (runHeadEdges xs).length ∧
      IsDoublyLinkedList stEnd.mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L_b' ∧
      L_b'.length + xs.length = L_b0.length ∧
      (∀ k, k ∈ L_b' ↔ endOfKey k ∈ B.ends b ∧ endOfKey k ∉ xs) ∧
      IsDoublyLinkedList stEnd.mem prevBase nextBase (bsHeadBase p + nB) (2 * eCap) L_new' ∧
      L_new'.length = xs.length ∧
      (∀ k, k ∈ L_new' ↔ endOfKey k ∈ xs) ∧
      ListAt stEnd.mem (batchPtr + writeOff + 5) (runTailEdges xs) ∧
      ListAt stEnd.mem headBuf (runHeadEdges xs) ∧
      (∀ x ∈ xs, stEnd.mem (endBundleBase + endKey x) = nB) ∧
      (∀ a, a ≠ bsHeadBase p + b → a ≠ bsHeadBase p + nB →
        (∀ k ∈ L_b0, a ≠ prevBase + k ∧ a ≠ nextBase + k) →
        (∀ x ∈ xs, a ≠ endBundleBase + endKey x) →
        (a < batchPtr + writeOff + 5 ∨ batchPtr + writeOff + 5 + (runTailEdges xs).length ≤ a) →
        (a < headBuf ∨ headBuf + (runHeadEdges xs).length ≤ a) →
        stEnd.mem a = st₀.mem a) ∧
      cEnd ≤ 200 * xs.length + 25 := by
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have h5_w : 5 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hp_w' : p + (3 + 6 * bunCap) < 2 ^ w := hp_w
  have hblk_p' : p + (3 + 6 * bunCap) ≤ prevBase ∨ prevBase + 2 * eCap ≤ p := hblk_prev
  have hblk_n' : p + (3 + 6 * bunCap) ≤ nextBase ∨ nextBase + 2 * eCap ≤ p := hblk_next
  have heb_b' : endBundleBase + 2 * eCap ≤ p ∨ p + (3 + 6 * bunCap) ≤ endBundleBase := heb_blk
  have hbat_b' : batchPtr + writeOff + 5 + xs.length ≤ p ∨ p + (3 + 6 * bunCap) ≤ batchPtr + writeOff + 5 := hbat_disj_blk
  have hh_b' : headBuf + xs.length ≤ p ∨ p + (3 + 6 * bunCap) ≤ headBuf := hh_disj_blk
  have hpack_b' : packArr + degB ≤ p ∨ p + (3 + 6 * bunCap) ≤ packArr := hpack_disj_blk
  have hxs_key_lt : ∀ x ∈ xs, endKey x < 2 * eCap := fun x hx => by
    have he := hE_lt x.1 ((BundleState.mem_ends B b x).mp (hxs_sub x hx)).1
    rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
  let loopStmt := Stmt.loop (.reg 35)
    (.cond (.bin .lt (.reg 29) (.reg 26))
      (.assign 36 (.load (.bin .add (.reg 27) (.reg 29))) ;;
       .cond (.bin .eq (.bin .div (.reg 36) (.reg 6)) (.reg 30))
         (.assign 37 (.bin .mod (.reg 36) (.reg 6)) ;;
          .call 38 bDllErase [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25), .reg 37] ;;
          .call 38 bDllPush [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 31), .reg 37] ;;
          .store (.bin .add (.reg 9) (.reg 37)) (.reg 31) ;;
          .cond (.bin .eq (.bin .mod (.reg 37) (.const 2)) (.const 0))
            (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
              (.bin .div (.reg 37) (.const 2)) ;;
             .assign 33 (.bin .add (.reg 33) (.const 1)))
            (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 37) (.const 2)) ;;
             .assign 34 (.bin .add (.reg 34) (.const 1))) ;;
          .assign 29 (.bin .add (.reg 29) (.const 1)))
         (.assign 35 (.const 0)))
      (.assign 35 (.const 0)))
  have hloop : ∀ d t (hd : t + d = xs.length) (st : State) (L_b L_new : List ℕ),
      (∀ r ≤ 32, r ≠ 29 → st.regs r = st₀.regs r) →
      st.regs 29 = idx + t →
      st.regs 33 = (runTailEdges (xs.take t)).length →
      st.regs 34 = (runHeadEdges (xs.take t)).length →
      st.regs 35 = 1 →
      IsDoublyLinkedList st.mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L_b →
      L_b.length + t = L_b0.length →
      (∀ k, k ∈ L_b ↔ endOfKey k ∈ B.ends b ∧ endOfKey k ∉ xs.take t) →
      IsDoublyLinkedList st.mem prevBase nextBase (bsHeadBase p + nB) (2 * eCap) L_new →
      L_new.length = t →
      (∀ k, k ∈ L_new ↔ endOfKey k ∈ xs.take t) →
      ListAt st.mem (batchPtr + writeOff + 5) (runTailEdges (xs.take t)) →
      ListAt st.mem headBuf (runHeadEdges (xs.take t)) →
      (∀ x ∈ xs.take t, st.mem (endBundleBase + endKey x) = nB) →
      (∀ a, a ≠ bsHeadBase p + b → a ≠ bsHeadBase p + nB →
        (∀ k ∈ L_b0, a ≠ prevBase + k ∧ a ≠ nextBase + k) →
        (∀ x ∈ xs.take t, a ≠ endBundleBase + endKey x) →
        (a < batchPtr + writeOff + 5 ∨ batchPtr + writeOff + 5 + (runTailEdges (xs.take t)).length ≤ a) →
        (a < headBuf ∨ headBuf + (runHeadEdges (xs.take t)).length ≤ a) →
        st.mem a = st₀.mem a) →
      ∃ stEnd cEnd L_b' L_new',
        Runs w pProg ω loopStmt st .normal stEnd cEnd ∧
        (∀ r ≤ 32, r ≠ 29 → stEnd.regs r = st₀.regs r) ∧
        stEnd.regs 29 = idx + xs.length ∧
        stEnd.regs 33 = (runTailEdges xs).length ∧
        stEnd.regs 34 = (runHeadEdges xs).length ∧
        IsDoublyLinkedList stEnd.mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L_b' ∧
        L_b'.length + xs.length = L_b0.length ∧
        (∀ k, k ∈ L_b' ↔ endOfKey k ∈ B.ends b ∧ endOfKey k ∉ xs) ∧
        IsDoublyLinkedList stEnd.mem prevBase nextBase (bsHeadBase p + nB) (2 * eCap) L_new' ∧
        L_new'.length = xs.length ∧
        (∀ k, k ∈ L_new' ↔ endOfKey k ∈ xs) ∧
        ListAt stEnd.mem (batchPtr + writeOff + 5) (runTailEdges xs) ∧
        ListAt stEnd.mem headBuf (runHeadEdges xs) ∧
        (∀ x ∈ xs, stEnd.mem (endBundleBase + endKey x) = nB) ∧
        (∀ a, a ≠ bsHeadBase p + b → a ≠ bsHeadBase p + nB →
          (∀ k ∈ L_b0, a ≠ prevBase + k ∧ a ≠ nextBase + k) →
          (∀ x ∈ xs, a ≠ endBundleBase + endKey x) →
          (a < batchPtr + writeOff + 5 ∨ batchPtr + writeOff + 5 + (runTailEdges xs).length ≤ a) →
          (a < headBuf ∨ headBuf + (runHeadEdges xs).length ≤ a) →
          stEnd.mem a = st₀.mem a) ∧
        cEnd ≤ 200 * d + 25 := by
    intro d
    induction d with
    | zero =>
      intro t hd st L_b L_new hregs hr29' hr33' hr34' hr35' hdll_b hLb_len hLb_mem
        hdll_n hLn_len hLn_mem hLt hLh heb hfr
      have hteq : t = xs.length := by omega
      subst hteq
      rw [List.take_length] at hr33' hr34' hLb_mem hLn_mem hLt hLh heb hfr
      have hlen_sum := runTailEdges_add_headEdges_length xs
      have hlt_le : (runTailEdges xs).length ≤ xs.length := by omega
      have hlh_le : (runHeadEdges xs).length ≤ xs.length := by omega
      set stZero : State := { st with regs := Function.update st.regs 35 0 }
      have hexit_loop : Runs w pProg ω loopStmt stZero .normal stZero 2 :=
        runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, stZero], rfl, rfl, by simp [Expr.size]⟩)
      have ha35 : Runs w pProg ω (.assign 35 (.const 0)) st .normal stZero 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
      by_cases hlt_deg : idx + xs.length < degB
      · obtain ⟨hdiv_ne, hpk_w⟩ := hpack_end hlt_deg
        have hmem_pk : st.mem (packArr + (idx + xs.length)) = st₀.mem (packArr + (idx + xs.length)) :=
          hfr _ (by unfold bsHeadBase; clear * - hpack_b' hlt_deg hb_lt hnb_lt; omega)
            (by unfold bsHeadBase; clear * - hpack_b' hlt_deg hnb_lt; omega)
            (fun k hk => ⟨by have := hL0_lt k hk; clear * - hpack_disj_prev hlt_deg this; omega,
                          by have := hL0_lt k hk; clear * - hpack_disj_next hlt_deg this; omega⟩)
            (fun x hx => by have := hxs_key_lt x hx; clear * - hpack_disj_eb hlt_deg this; omega)
            (by clear * - hpack_disj_bat hlt_deg hlt_le; omega)
            (by clear * - hpack_disj_h hlt_deg hlh_le; omega)
        set pk := st₀.mem (packArr + (idx + xs.length))
        set st36 : State := { st with regs := Function.update st.regs 36 pk }
        set stZ2 : State := { st36 with regs := Function.update st36.regs 35 0 }
        have ha36 : Runs w pProg ω (.assign 36 (.load (.bin .add (.reg 27) (.reg 29)))) st .normal st36 5 :=
          runs_assign_iff.mpr ⟨pk, by
            simp [Expr.eval, BinOp.eval, hregs 27 (by decide) (by decide), hr27, hr29',
              show packArr + (idx + xs.length) < 2 ^ w by omega, hmem_pk, pk], rfl, rfl, rfl⟩
        have hcond_eq : Expr.eval w st36 (.bin .eq (.bin .div (.reg 36) (.reg 6)) (.reg 30)) = some 0 := by
          have hr6s : st.regs 6 = 2 * eCap := (hregs 6 (by decide) (by decide)).trans hr6
          have hr30s : st.regs 30 = vCur := (hregs 30 (by decide) (by decide)).trans hr30
          have hdiv_w : pk / (2 * eCap) < 2 ^ w := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hpk_w
          simp [Expr.eval, BinOp.eval, st36, hr6s, hr30s, hdiv_w, hdiv_ne, h0_w]
        have ha35_2 : Runs w pProg ω (.assign 35 (.const 0)) st36 .normal stZ2 2 :=
          runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
        have hcond2 : ∀ sThen, Runs w pProg ω
            (.cond (.bin .eq (.bin .div (.reg 36) (.reg 6)) (.reg 30)) sThen (.assign 35 (.const 0)))
            st36 .normal stZ2 8 := fun _ =>
          runs_cond_iff.mpr ⟨0, 2, hcond_eq, by simpa using ha35_2, by simp [Expr.size]⟩
        have hcond1_e : Expr.eval w st (.bin .lt (.reg 29) (.reg 26)) = some 1 := by
          simp [Expr.eval, BinOp.eval, hr29', hregs 26 (by decide) (by decide), hr26, hlt_deg, h1_w]
        have hbody : ∀ sThen, Runs w pProg ω
            (.cond (.bin .lt (.reg 29) (.reg 26))
              (.assign 36 (.load (.bin .add (.reg 27) (.reg 29))) ;;
               .cond (.bin .eq (.bin .div (.reg 36) (.reg 6)) (.reg 30)) sThen (.assign 35 (.const 0)))
              (.assign 35 (.const 0))) st .normal stZ2 18 := fun sThen =>
          runs_cond_iff.mpr ⟨1, 14, hcond1_e, by simpa using bundle_runs_seq_normal ha36 (hcond2 sThen), by simp [Expr.size]⟩
        have hexit2 : Runs w pProg ω loopStmt stZ2 .normal stZ2 2 :=
          runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, stZ2], rfl, rfl, by simp [Expr.size]⟩)
        have hrun_l := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stZ2, 18, 2,
          by simp [Expr.eval, hr35'], by decide, hbody _, hexit2, rfl⟩))
        refine ⟨stZ2, _, L_b, L_new, hrun_l,
          fun r hr h29 => by simp [stZ2, st36, show r ≠ 35 by omega, show r ≠ 36 by omega, hregs r hr h29],
          by simp [stZ2, st36, hr29'], by simp [stZ2, st36, hr33'], by simp [stZ2, st36, hr34'],
          hdll_b, hLb_len, hLb_mem, hdll_n, hLn_len, hLn_mem, hLt, hLh, heb, hfr, by simp [Expr.size]⟩
      · have hcond1_e : Expr.eval w st (.bin .lt (.reg 29) (.reg 26)) = some 0 := by
          simp [Expr.eval, BinOp.eval, hr29', hregs 26 (by decide) (by decide), hr26, hlt_deg, h0_w]
        have hbody : ∀ sThen, Runs w pProg ω
            (.cond (.bin .lt (.reg 29) (.reg 26)) sThen (.assign 35 (.const 0)))
            st .normal stZero 6 := fun _ =>
          runs_cond_iff.mpr ⟨0, 2, hcond1_e, by simpa using ha35, by simp [Expr.size]⟩
        have hrun_l := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stZero, 6, 2,
          by simp [Expr.eval, hr35'], by decide, hbody _, hexit_loop, rfl⟩))
        refine ⟨stZero, _, L_b, L_new, hrun_l,
          fun r hr h29 => by simp [stZero, show r ≠ 35 by omega, hregs r hr h29],
          by simp [stZero, hr29'], by simp [stZero, hr33'], by simp [stZero, hr34'],
          hdll_b, hLb_len, hLb_mem, hdll_n, hLn_len, hLn_mem, hLt, hLh, heb, hfr, by simp [Expr.size]⟩
    | succ d ih =>
      intro t hd st L_b L_new hregs hr29' hr33' hr34' hr35' hdll_b hLb_len hLb_mem
        hdll_n hLn_len hLn_mem hLt hLh heb hfr
      have ht_lt : t < xs.length := by omega
      set x := xs[t]'ht_lt
      set key := endKey x
      have hx_mem : x ∈ xs := List.getElem_mem ht_lt
      have hx_B : x ∈ B.ends b := hxs_sub x hx_mem
      have hkey_lt : key < 2 * eCap := hxs_key_lt x hx_mem
      have hx_not_take : x ∉ xs.take t := fun hmem => by
        obtain ⟨j, hj, hxj⟩ := List.getElem_of_mem hmem
        simp only [List.length_take, Nat.min_eq_left (by omega : t ≤ xs.length)] at hj
        rw [List.getElem_take] at hxj
        have := hxs_nd.getElem_inj_iff.mp hxj; omega
      have hkey_in_Lb : key ∈ L_b := (hLb_mem key).mpr ⟨by rwa [bundle_endOfKey_endKey], by rwa [bundle_endOfKey_endKey]⟩
      have hkey_not_Ln : key ∉ L_new := fun h => hx_not_take (by simpa [key, bundle_endOfKey_endKey] using (hLn_mem key).mp h)
      have hLb_sub_L0 : ∀ k ∈ L_b, k ∈ L_b0 := fun k hk => (hL0_mem k).mpr ((hLb_mem k).mp hk).1
      have hLn_sub_L0 : ∀ k ∈ L_new, k ∈ L_b0 := fun k hk =>
        (hL0_mem k).mpr (hxs_sub _ (List.mem_of_mem_take ((hLn_mem k).mp hk)))
      have htake_sum := runTailEdges_add_headEdges_length (xs.take t)
      have htake_len : (xs.take t).length = t := by simp [Nat.min_eq_left (by omega : t ≤ xs.length)]
      have hlt_le : (runTailEdges (xs.take t)).length ≤ xs.length := by omega
      have hlh_le : (runHeadEdges (xs.take t)).length ≤ xs.length := by omega
      set pk := packEndKey eCap vCur key
      have hpk_eq : st.mem (packArr + (idx + t)) = pk := by
        rw [hfr _ (by unfold bsHeadBase; clear * - hpack_b' hidx_le ht_lt hb_lt hnb_lt; omega)
          (by unfold bsHeadBase; clear * - hpack_b' hidx_le ht_lt hnb_lt; omega)
          (fun k hk => ⟨by have := hL0_lt k hk; clear * - hpack_disj_prev hidx_le ht_lt this; omega,
                        by have := hL0_lt k hk; clear * - hpack_disj_next hidx_le ht_lt this; omega⟩)
          (fun y hy => by have := hxs_key_lt y (List.mem_of_mem_take hy); clear * - hpack_disj_eb hidx_le ht_lt this; omega)
          (by clear * - hpack_disj_bat hidx_le ht_lt hlt_le; omega)
          (by clear * - hpack_disj_h hidx_le ht_lt hlh_le; omega)]
        exact hpack_in t ht_lt
      have hpk_w : pk < 2 ^ w := by
        unfold pk packEndKey
        rw [Nat.add_mul, Nat.one_mul] at hpk_bound
        omega
      -- Step 1: assign 36, assign 37
      set st36 : State := { st with regs := Function.update st.regs 36 pk }
      set st37 : State := { st36 with regs := Function.update st36.regs 37 key }
      have ha36 : Runs w pProg ω (.assign 36 (.load (.bin .add (.reg 27) (.reg 29)))) st .normal st36 5 :=
        runs_assign_iff.mpr ⟨pk, by
          simp [Expr.eval, BinOp.eval, hregs 27 (by decide) (by decide), hr27, hr29',
            show packArr + (idx + t) < 2 ^ w by omega, hpk_eq], rfl, rfl, rfl⟩
      have ha37 : Runs w pProg ω (.assign 37 (.bin .mod (.reg 36) (.reg 6))) st36 .normal st37 4 :=
        runs_assign_iff.mpr ⟨key, by
          have hr6s : st.regs 6 = 2 * eCap := (hregs 6 (by decide) (by decide)).trans hr6
          simp [Expr.eval, BinOp.eval, st36, hr6s, pk, packEndKey_mod hkey_lt, show key < 2 ^ w by omega], rfl, rfl, rfl⟩
      -- Step 2: call bDllErase
      have hEr := bundleDllErase_meetsContract (w := w) (prevBase := prevBase) (nextBase := nextBase)
        (headAddr := bsHeadBase p + b) (cap := 2 * eCap) (key := key) (L := L_b) hpErase
        [prevBase, nextBase, bsHeadBase p + b, key] st37.mem st37.pos ω
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl <;> [omega; omega; (unfold bsHeadBase; omega); omega])
        ⟨rfl, hw16, hprev_w, hnext_w, hprev_next,
          by unfold bsHeadBase; clear * - hblk_p' hb_lt hnb_lt; omega,
          by unfold bsHeadBase; clear * - hblk_n' hb_lt hnb_lt; omega,
          hkey_in_Lb, hdll_b⟩
      obtain ⟨bodyEr, hbodyEr, oEr, stErRaw, cEr, hrunEr, ⟨hoEr, hdll_b1, _, _, hfrEr⟩, hcEr⟩ := hEr
      set stEr : State := { mem := stErRaw.mem, regs := Function.update st37.regs 38 0, pos := stErRaw.pos }
      have hcallEr : Runs w pProg ω
          (.call 38 bDllErase [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25), .reg 37])
          st37 .normal stEr (cEr + 9) := by
        have hargs : evalArgs w st37 [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25), .reg 37] =
            some [prevBase, nextBase, bsHeadBase p + b, key] := by
          have hr7s : st.regs 7 = p := (hregs 7 (by decide) (by decide)).trans hr7
          have hr10s : st.regs 10 = prevBase := (hregs 10 (by decide) (by decide)).trans hr10
          have hr11s : st.regs 11 = nextBase := (hregs 11 (by decide) (by decide)).trans hr11
          have hr25s : st.regs 25 = b := (hregs 25 (by decide) (by decide)).trans hr25
          simp [evalArgs, Expr.eval, BinOp.eval, st37, st36, hr7s, hr10s, hr11s, hr25s, h3_w, bsHeadBase,
            show p + 3 < 2 ^ w by omega, show p + 3 + b < 2 ^ w by omega]
        have hc : Runs w pProg ω
            (.call 38 bDllErase [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25), .reg 37])
            st37 .normal { mem := stErRaw.mem, regs := Function.update st37.regs 38 oEr.value, pos := stErRaw.pos }
            (argsSize [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25), .reg 37] + cEr + 1) :=
          runs_call_iff.mpr ⟨[prevBase, nextBase, bsHeadBase p + b, key], bodyEr, oEr, stErRaw, cEr,
            hargs, hbodyEr, hrunEr, rfl, rfl, rfl⟩
        simpa [argsSize, Expr.size, stEr, hoEr, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc
      -- Step 3: L_new is preserved across bDllErase
      have hLb_disj_Ln : ∀ k1 ∈ L_b, ∀ k2 ∈ L_new, k1 ≠ k2 := fun k1 h1 k2 h2 heq => by
        subst heq; exact ((hLb_mem k1).mp h1).2 ((hLn_mem k1).mp h2)
      have hdll_n1 : IsDoublyLinkedList stErRaw.mem prevBase nextBase (bsHeadBase p + nB) (2 * eCap) L_new := by
        refine hdll_n.of_agree ?_ ?_ ?_
        · exact hfrEr (bsHeadBase p + nB) (by unfold bsHeadBase; omega) fun k hk =>
            ⟨by have := hL0_lt k (hLb_sub_L0 k hk); unfold bsHeadBase; clear * - hblk_p' this hnb_lt; omega,
             by have := hL0_lt k (hLb_sub_L0 k hk); unfold bsHeadBase; clear * - hblk_n' this hnb_lt; omega⟩
        · intro k hk
          have hk_lt := hdll_n.2.1 k hk
          exact hfrEr (prevBase + k) (by unfold bsHeadBase; clear * - hblk_p' hk_lt hb_lt hnb_lt; omega) fun k' hk' =>
            ⟨by have := hLb_disj_Ln k' hk' k hk; omega,
             by have := hL0_lt k' (hLb_sub_L0 k' hk'); clear * - hprev_next hk_lt this; omega⟩
        · intro k hk
          have hk_lt := hdll_n.2.1 k hk
          exact hfrEr (nextBase + k) (by unfold bsHeadBase; clear * - hblk_n' hk_lt hb_lt hnb_lt; omega) fun k' hk' =>
            ⟨by have := hL0_lt k' (hLb_sub_L0 k' hk'); clear * - hprev_next hk_lt this; omega,
             by have := hLb_disj_Ln k' hk' k hk; omega⟩
      -- Step 4: call bDllPush onto b' = nB
      have hPu := bundleDllPush_meetsContract (w := w) (prevBase := prevBase) (nextBase := nextBase)
        (headAddr := bsHeadBase p + nB) (cap := 2 * eCap) (key := key) (L := L_new) hpPush
        [prevBase, nextBase, bsHeadBase p + nB, key] stErRaw.mem stErRaw.pos ω
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl <;> [omega; omega; (unfold bsHeadBase; omega); omega])
        ⟨rfl, hw16, hprev_w, hnext_w, hprev_next,
          by unfold bsHeadBase; clear * - hblk_p' hnb_lt; omega,
          by unfold bsHeadBase; clear * - hblk_n' hnb_lt; omega,
          hkey_lt, hkey_not_Ln, hdll_n1⟩
      obtain ⟨bodyPu, hbodyPu, oPu, stPuRaw, cPu, hrunPu, ⟨hoPu, hdll_n2, hfrPu⟩, hcPu⟩ := hPu
      set stPu : State := { mem := stPuRaw.mem, regs := Function.update stEr.regs 38 0, pos := stPuRaw.pos }
      have hcallPu : Runs w pProg ω
          (.call 38 bDllPush [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 31), .reg 37])
          stEr .normal stPu (cPu + 9) := by
        have hargs : evalArgs w stEr [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 31), .reg 37] =
            some [prevBase, nextBase, bsHeadBase p + nB, key] := by
          have hr7s : st.regs 7 = p := (hregs 7 (by decide) (by decide)).trans hr7
          have hr10s : st.regs 10 = prevBase := (hregs 10 (by decide) (by decide)).trans hr10
          have hr11s : st.regs 11 = nextBase := (hregs 11 (by decide) (by decide)).trans hr11
          have hr31s : st.regs 31 = nB := (hregs 31 (by decide) (by decide)).trans hr31
          simp [evalArgs, Expr.eval, BinOp.eval, stEr, st37, st36, hr7s, hr10s, hr11s, hr31s, h3_w, bsHeadBase,
            show p + 3 < 2 ^ w by omega, show p + 3 + nB < 2 ^ w by omega]
        have hc : Runs w pProg ω
            (.call 38 bDllPush [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 31), .reg 37])
            stEr .normal { mem := stPuRaw.mem, regs := Function.update stEr.regs 38 oPu.value, pos := stPuRaw.pos }
            (argsSize [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 31), .reg 37] + cPu + 1) :=
          runs_call_iff.mpr ⟨[prevBase, nextBase, bsHeadBase p + nB, key], bodyPu, oPu, stPuRaw, cPu,
            hargs, hbodyPu, hrunPu, rfl, rfl, rfl⟩
        simpa [argsSize, Expr.size, stPu, hoPu, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hc
      -- Step 5: store endBundle[key] := nB
      set stEB : State := { stPu with mem := Function.update stPuRaw.mem (endBundleBase + key) nB }
      have hstEB : Runs w pProg ω (.store (.bin .add (.reg 9) (.reg 37)) (.reg 31)) stPu .normal stEB 5 :=
        runs_store_iff.mpr ⟨endBundleBase + key, nB, by
          have hr9s : st.regs 9 = endBundleBase := (hregs 9 (by decide) (by decide)).trans hr9
          simp [Expr.eval, BinOp.eval, stPu, stEr, st37, st36, hr9s, show endBundleBase + key < 2 ^ w by omega],
          by have hr31s : st.regs 31 = nB := (hregs 31 (by decide) (by decide)).trans hr31
             simp [Expr.eval, stPu, stEr, st37, st36, hr31s], rfl, rfl, rfl⟩
      -- Step 6: cond (key % 2 == 0) write tail edge to batch or head edge to headBuf, then r29 := r29 + 1
      have htake_succ : xs.take (t + 1) = xs.take t ++ [x] := List.take_succ_eq_append_getElem ht_lt
      have hkey_div2 : key / 2 = x.1 := by
        rcases hxeq : x with ⟨ee, side⟩; cases side <;> (simp [key, hxeq, endKey]; try omega)
      have hkey_mod2 : key % 2 = if x.2 then 0 else 1 := by
        rcases hxeq : x with ⟨ee, side⟩; cases side <;> simp [key, hxeq, endKey]
      have hx1_w : x.1 < 2 ^ w := by
        have := hE_lt x.1 ((BundleState.mem_ends B b x).mp hx_B).1; omega
      have hbranch : ∃ stBr cBr,
          Runs w pProg ω
            (.cond (.bin .eq (.bin .mod (.reg 37) (.const 2)) (.const 0))
              (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
                (.bin .div (.reg 37) (.const 2)) ;;
               .assign 33 (.bin .add (.reg 33) (.const 1)))
              (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 37) (.const 2)) ;;
               .assign 34 (.bin .add (.reg 34) (.const 1))))
            stEB .normal stBr cBr ∧
          cBr ≤ 24 ∧
          (∀ r ≤ 32, stBr.regs r = stEB.regs r) ∧
          stBr.regs 33 = (runTailEdges (xs.take (t + 1))).length ∧
          stBr.regs 34 = (runHeadEdges (xs.take (t + 1))).length ∧
          stBr.regs 35 = 1 ∧
          ListAt stBr.mem (batchPtr + writeOff + 5) (runTailEdges (xs.take (t + 1))) ∧
          ListAt stBr.mem headBuf (runHeadEdges (xs.take (t + 1))) ∧
          (∀ a, (a < batchPtr + writeOff + 5 + (runTailEdges (xs.take t)).length ∨
              batchPtr + writeOff + 5 + (runTailEdges (xs.take (t + 1))).length ≤ a) →
            (a < headBuf + (runHeadEdges (xs.take t)).length ∨
              headBuf + (runHeadEdges (xs.take (t + 1))).length ≤ a) →
            stBr.mem a = stEB.mem a) := by
        have hr20' : stEB.regs 20 = batchPtr := by simp [stEB, stPu, stEr, st37, st36, hregs 20 (by decide) (by decide), hr20]
        have hr21' : stEB.regs 21 = writeOff := by simp [stEB, stPu, stEr, st37, st36, hregs 21 (by decide) (by decide), hr21]
        have hr32' : stEB.regs 32 = headBuf := by simp [stEB, stPu, stEr, st37, st36, hregs 32 (by decide) (by decide), hr32]
        have hr33e : stEB.regs 33 = (runTailEdges (xs.take t)).length := by simp [stEB, stPu, stEr, st37, st36, hr33']
        have hr34e : stEB.regs 34 = (runHeadEdges (xs.take t)).length := by simp [stEB, stPu, stEr, st37, st36, hr34']
        have hr35e : stEB.regs 35 = 1 := by simp [stEB, stPu, stEr, st37, st36, hr35']
        have hr37e : stEB.regs 37 = key := by simp [stEB, stPu, stEr, st37]
        have hEB_eq_st : ∀ a, a ≠ bsHeadBase p + b → a ≠ bsHeadBase p + nB →
            (∀ k ∈ L_b0, a ≠ prevBase + k ∧ a ≠ nextBase + k) → a ≠ endBundleBase + key →
            stEB.mem a = st.mem a := fun a h1 h2 h3 h4 => by
          dsimp only [stEB]
          rw [Function.update_of_ne h4]
          have hpu := hfrPu a h2 (h3 key (hL0_mem key |>.mpr (by rwa [bundle_endOfKey_endKey]))).1
            (h3 key (hL0_mem key |>.mpr (by rwa [bundle_endOfKey_endKey]))).2
            (fun y ys hy => (h3 y (hLn_sub_L0 y (hy ▸ List.mem_cons_self))).1)
          rw [hpu]
          exact hfrEr a h1 fun k hk => h3 k (hLb_sub_L0 k hk)
        by_cases hx2 : x.2 = true
        · have htail_eq : runTailEdges (xs.take (t + 1)) = runTailEdges (xs.take t) ++ [x.1] := by
            simp [htake_succ, runTailEdges, hx2]
          have hhead_eq : runHeadEdges (xs.take (t + 1)) = runHeadEdges (xs.take t) := by
            simp [htake_succ, runHeadEdges, hx2]
          have hcond_t : Expr.eval w stEB (.bin .eq (.bin .mod (.reg 37) (.const 2)) (.const 0)) = some 1 := by
            simp [Expr.eval, BinOp.eval, hr37e, hkey_mod2, hx2, h2_w, h0_w, h1_w]
          set kt := (runTailEdges (xs.take t)).length
          set stW : State := { stEB with mem := Function.update stEB.mem (batchPtr + writeOff + 5 + kt) x.1 }
          set stI : State := { stW with regs := Function.update stW.regs 33 (kt + 1) }
          have hstW : Runs w pProg ω
              (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
                (.bin .div (.reg 37) (.const 2))) stEB .normal stW 11 :=
            runs_store_iff.mpr ⟨batchPtr + writeOff + 5 + kt, x.1, by
              simp [Expr.eval, BinOp.eval, hr20', hr21', hr33e, h5_w, kt,
                show batchPtr + writeOff < 2 ^ w by omega,
                show batchPtr + writeOff + 5 < 2 ^ w by omega,
                show batchPtr + writeOff + 5 + kt < 2 ^ w by omega],
              by simp [Expr.eval, BinOp.eval, hr37e, h2_w, hkey_div2, hx1_w], rfl, rfl, by simp [Expr.size]⟩
          have ha33 : Runs w pProg ω (.assign 33 (.bin .add (.reg 33) (.const 1))) stW .normal stI 4 :=
            runs_assign_iff.mpr ⟨kt + 1, by
              simp [Expr.eval, BinOp.eval, stW, hr33e, h1_w, kt, show kt + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
          refine ⟨stI, 22, runs_cond_iff.mpr ⟨1, 16, hcond_t,
            by simpa using bundle_runs_seq_normal hstW ha33, by simp [Expr.size]⟩, by omega,
            fun r hr => by simp [stI, stW, show r ≠ 33 by omega],
            by simp [stI, htail_eq, kt], by simp [stI, stW, hr34e, hhead_eq],
            by simp [stI, stW, hr35e], ?_, ?_, ?_⟩
          · rw [htail_eq]; intro j hj
            simp only [List.length_append, List.length_singleton] at hj
            by_cases hjk : j < kt
            · rw [List.getElem_append_left hjk]
              dsimp only [stI, stW]; rw [Function.update_of_ne (by omega)]
              rw [hEB_eq_st _ (by unfold bsHeadBase; clear * - hbat_b' hjk hlt_le hb_lt hnb_lt; omega)
                (by unfold bsHeadBase; clear * - hbat_b' hjk hlt_le hnb_lt; omega)
                (fun k hk => ⟨by have := hL0_lt k hk; clear * - hbat_disj_prev hjk hlt_le this; omega,
                              by have := hL0_lt k hk; clear * - hbat_disj_next hjk hlt_le this; omega⟩)
                (by clear * - hbat_disj_eb hjk hlt_le hkey_lt; omega)]
              exact hLt j hjk
            · have hjeq : j = kt := by omega
              subst hjeq
              rw [List.getElem_append_right (le_refl _)]; simp [stI, stW, kt]
          · rw [hhead_eq]; intro j hj
            have hkt_lt : kt < xs.length := by omega
            dsimp only [stI, stW]; rw [Function.update_of_ne (by clear * - hbat_disj_h hj hlh_le hkt_lt; omega)]
            rw [hEB_eq_st _ (by unfold bsHeadBase; clear * - hh_b' hj hlh_le hb_lt hnb_lt; omega)
              (by unfold bsHeadBase; clear * - hh_b' hj hlh_le hnb_lt; omega)
              (fun k hk => ⟨by have := hL0_lt k hk; clear * - hh_disj_prev hj hlh_le this; omega,
                            by have := hL0_lt k hk; clear * - hh_disj_next hj hlh_le this; omega⟩)
              (by clear * - hh_disj_eb hj hlh_le hkey_lt; omega)]
            exact hLh j hj
          · intro a ha1 _
            rw [htail_eq, List.length_append, List.length_singleton] at ha1
            dsimp only [stI, stW]; rw [Function.update_of_ne (by omega)]
        · have hx2f : x.2 = false := Bool.eq_false_iff.mpr hx2
          have htail_eq : runTailEdges (xs.take (t + 1)) = runTailEdges (xs.take t) := by
            simp [htake_succ, runTailEdges, hx2f]
          have hhead_eq : runHeadEdges (xs.take (t + 1)) = runHeadEdges (xs.take t) ++ [x.1] := by
            simp [htake_succ, runHeadEdges, hx2f]
          have hcond_f : Expr.eval w stEB (.bin .eq (.bin .mod (.reg 37) (.const 2)) (.const 0)) = some 0 := by
            simp [Expr.eval, BinOp.eval, hr37e, hkey_mod2, hx2f, h2_w, h1_w, h0_w]
          set kh := (runHeadEdges (xs.take t)).length
          set stW : State := { stEB with mem := Function.update stEB.mem (headBuf + kh) x.1 }
          set stI : State := { stW with regs := Function.update stW.regs 34 (kh + 1) }
          have hstW : Runs w pProg ω
              (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 37) (.const 2))) stEB .normal stW 7 :=
            runs_store_iff.mpr ⟨headBuf + kh, x.1, by
              simp [Expr.eval, BinOp.eval, hr32', hr34e, kh, show headBuf + kh < 2 ^ w by omega],
              by simp [Expr.eval, BinOp.eval, hr37e, h2_w, hkey_div2, hx1_w], rfl, rfl, by simp [Expr.size]⟩
          have ha34 : Runs w pProg ω (.assign 34 (.bin .add (.reg 34) (.const 1))) stW .normal stI 4 :=
            runs_assign_iff.mpr ⟨kh + 1, by
              simp [Expr.eval, BinOp.eval, stW, hr34e, h1_w, kh, show kh + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
          refine ⟨stI, 18, runs_cond_iff.mpr ⟨0, 12, hcond_f,
            by simpa using bundle_runs_seq_normal hstW ha34, by simp [Expr.size]⟩, by omega,
            fun r hr => by simp [stI, stW, show r ≠ 34 by omega],
            by simp [stI, stW, hr33e, htail_eq], by simp [stI, hhead_eq, kh],
            by simp [stI, stW, hr35e], ?_, ?_, ?_⟩
          · rw [htail_eq]; intro j hj
            have hkh_lt : kh < xs.length := by omega
            dsimp only [stI, stW]; rw [Function.update_of_ne (by clear * - hbat_disj_h hj hlt_le hkh_lt; omega)]
            rw [hEB_eq_st _ (by unfold bsHeadBase; clear * - hbat_b' hj hlt_le hb_lt hnb_lt; omega)
              (by unfold bsHeadBase; clear * - hbat_b' hj hlt_le hnb_lt; omega)
              (fun k hk => ⟨by have := hL0_lt k hk; clear * - hbat_disj_prev hj hlt_le this; omega,
                            by have := hL0_lt k hk; clear * - hbat_disj_next hj hlt_le this; omega⟩)
              (by clear * - hbat_disj_eb hj hlt_le hkey_lt; omega)]
            exact hLt j hj
          · rw [hhead_eq]; intro j hj
            simp only [List.length_append, List.length_singleton] at hj
            by_cases hjk : j < kh
            · rw [List.getElem_append_left hjk]
              dsimp only [stI, stW]; rw [Function.update_of_ne (by omega)]
              rw [hEB_eq_st _ (by unfold bsHeadBase; clear * - hh_b' hjk hlh_le hb_lt hnb_lt; omega)
                (by unfold bsHeadBase; clear * - hh_b' hjk hlh_le hnb_lt; omega)
                (fun k hk => ⟨by have := hL0_lt k hk; clear * - hh_disj_prev hjk hlh_le this; omega,
                              by have := hL0_lt k hk; clear * - hh_disj_next hjk hlh_le this; omega⟩)
                (by clear * - hh_disj_eb hjk hlh_le hkey_lt; omega)]
              exact hLh j hjk
            · have hjeq : j = kh := by omega
              subst hjeq
              rw [List.getElem_append_right (le_refl _)]; simp [stI, stW, kh]
          · intro a _ ha2
            rw [hhead_eq, List.length_append, List.length_singleton] at ha2
            dsimp only [stI, stW]; rw [Function.update_of_ne (by omega)]
      obtain ⟨stBr, cBr, hrunBr, hcBr, hregsBr, hr33Br, hr34Br, hr35Br, hLtBr, hLhBr, hfrBr⟩ := hbranch
      set stNext : State := { stBr with regs := Function.update stBr.regs 29 (idx + (t + 1)) }
      have ha29 : Runs w pProg ω (.assign 29 (.bin .add (.reg 29) (.const 1))) stBr .normal stNext 4 :=
        runs_assign_iff.mpr ⟨idx + (t + 1), by
          have hr29b : stBr.regs 29 = idx + t := by
            rw [hregsBr 29 (by decide)]; simp [stEB, stPu, stEr, st37, st36, hr29']
          simp [Expr.eval, BinOp.eval, hr29b, h1_w, show idx + t + 1 = idx + (t + 1) by omega,
            show idx + (t + 1) < 2 ^ w by omega], rfl, rfl, rfl⟩
      -- Assemble one iteration run
      have hcond_eq1 : Expr.eval w st36 (.bin .eq (.bin .div (.reg 36) (.reg 6)) (.reg 30)) = some 1 := by
        have hr6s : st.regs 6 = 2 * eCap := (hregs 6 (by decide) (by decide)).trans hr6
        have hr30s : st.regs 30 = vCur := (hregs 30 (by decide) (by decide)).trans hr30
        have hv_w : vCur < 2 ^ w := by
          have := packEndKey_div hkey_lt (v := vCur); rw [← this]
          exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hpk_w
        simp [Expr.eval, BinOp.eval, st36, hr6s, hr30s, pk, packEndKey_div hkey_lt, hv_w, h1_w]
      have hcond_lt1 : Expr.eval w st (.bin .lt (.reg 29) (.reg 26)) = some 1 := by
        simp [Expr.eval, BinOp.eval, hr29', hregs 26 (by decide) (by decide), hr26,
          show idx + t < degB by omega, h1_w]
      have hinner_then := bundle_runs_seq_normal ha37 (bundle_runs_seq_normal hcallEr
        (bundle_runs_seq_normal hcallPu (bundle_runs_seq_normal hstEB
          (bundle_runs_seq_normal hrunBr ha29))))
      have hcond2 : Runs w pProg ω
          (.cond (.bin .eq (.bin .div (.reg 36) (.reg 6)) (.reg 30))
            (.assign 37 (.bin .mod (.reg 36) (.reg 6)) ;;
             .call 38 bDllErase [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25), .reg 37] ;;
             .call 38 bDllPush [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 31), .reg 37] ;;
             .store (.bin .add (.reg 9) (.reg 37)) (.reg 31) ;;
             .cond (.bin .eq (.bin .mod (.reg 37) (.const 2)) (.const 0))
               (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
                 (.bin .div (.reg 37) (.const 2)) ;;
                .assign 33 (.bin .add (.reg 33) (.const 1)))
               (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 37) (.const 2)) ;;
                .assign 34 (.bin .add (.reg 34) (.const 1))) ;;
             .assign 29 (.bin .add (.reg 29) (.const 1)))
            (.assign 35 (.const 0)))
          st36 .normal stNext _ :=
        runs_cond_iff.mpr ⟨1, _, hcond_eq1, by simpa using hinner_then, rfl⟩
      have hbody : Runs w pProg ω
          (.cond (.bin .lt (.reg 29) (.reg 26))
            (.assign 36 (.load (.bin .add (.reg 27) (.reg 29))) ;;
             .cond (.bin .eq (.bin .div (.reg 36) (.reg 6)) (.reg 30))
               (.assign 37 (.bin .mod (.reg 36) (.reg 6)) ;;
                .call 38 bDllErase [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25), .reg 37] ;;
                .call 38 bDllPush [.reg 10, .reg 11, .bin .add (.bin .add (.reg 7) (.const 3)) (.reg 31), .reg 37] ;;
                .store (.bin .add (.reg 9) (.reg 37)) (.reg 31) ;;
                .cond (.bin .eq (.bin .mod (.reg 37) (.const 2)) (.const 0))
                  (.store (.bin .add (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 5)) (.reg 33))
                    (.bin .div (.reg 37) (.const 2)) ;;
                   .assign 33 (.bin .add (.reg 33) (.const 1)))
                  (.store (.bin .add (.reg 32) (.reg 34)) (.bin .div (.reg 37) (.const 2)) ;;
                   .assign 34 (.bin .add (.reg 34) (.const 1))) ;;
                .assign 29 (.bin .add (.reg 29) (.const 1)))
               (.assign 35 (.const 0)))
            (.assign 35 (.const 0)))
          st .normal stNext _ :=
        runs_cond_iff.mpr ⟨1, _, hcond_lt1, by simpa using bundle_runs_seq_normal ha36 hcond2, rfl⟩
      -- Establish loop invariant at `t + 1`
      have htake1_len_le : (runTailEdges (xs.take (t + 1))).length ≤ xs.length ∧
          (runHeadEdges (xs.take (t + 1))).length ≤ xs.length := by
        have hs := runTailEdges_add_headEdges_length (xs.take (t + 1))
        have hl : (xs.take (t + 1)).length = t + 1 := by simp [Nat.min_eq_left (by omega : t + 1 ≤ xs.length)]
        omega
      have hBr_eq_EB_blk : ∀ a, (p ≤ a ∧ a < p + bundleSlotBlockSize bunCap) ∨
          (prevBase ≤ a ∧ a < prevBase + 2 * eCap) ∨ (nextBase ≤ a ∧ a < nextBase + 2 * eCap) ∨
          (endBundleBase ≤ a ∧ a < endBundleBase + 2 * eCap) → stBr.mem a = stEB.mem a := by
        intro a ha
        refine hfrBr a ?_ ?_
        · rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · unfold bundleSlotBlockSize at h2; clear * - hbat_b' h1 h2 htake1_len_le; omega
          · clear * - hbat_disj_prev h1 h2 htake1_len_le; omega
          · clear * - hbat_disj_next h1 h2 htake1_len_le; omega
          · clear * - hbat_disj_eb h1 h2 htake1_len_le; omega
        · rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · unfold bundleSlotBlockSize at h2; clear * - hh_b' h1 h2 htake1_len_le; omega
          · clear * - hh_disj_prev h1 h2 htake1_len_le; omega
          · clear * - hh_disj_next h1 h2 htake1_len_le; omega
          · clear * - hh_disj_eb h1 h2 htake1_len_le; omega
      have hdll_b_next : IsDoublyLinkedList stNext.mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) (L_b.erase key) := by
        refine hdll_b1.of_agree ?_ ?_ ?_
        · have h1 := hBr_eq_EB_blk (bsHeadBase p + b) (Or.inl ⟨by unfold bsHeadBase; omega,
            by unfold bsHeadBase bundleSlotBlockSize; omega⟩)
          have h2 : stEB.mem (bsHeadBase p + b) = stPuRaw.mem (bsHeadBase p + b) :=
            Function.update_of_ne (by unfold bsHeadBase; clear * - heb_b' hb_lt hnb_lt hkey_lt; omega) _ _
          have h3 : stPuRaw.mem (bsHeadBase p + b) = stErRaw.mem (bsHeadBase p + b) :=
            hfrPu (bsHeadBase p + b) (by unfold bsHeadBase; omega)
              (by unfold bsHeadBase; clear * - hblk_p' hb_lt hnb_lt hkey_lt; omega)
              (by unfold bsHeadBase; clear * - hblk_n' hb_lt hnb_lt hkey_lt; omega)
              (fun y _ hy => by have := hdll_n.2.1 y (hy ▸ List.mem_cons_self); unfold bsHeadBase; clear * - hblk_p' hb_lt hnb_lt this; omega)
          exact h1.trans (h2.trans h3)
        · intro k hk
          have hk_lt := hdll_b1.2.1 k hk
          have hkne : k ≠ key := fun h => hdll_b.1.mem_erase_iff.mp (h ▸ hk) |>.1 rfl
          have h1 := hBr_eq_EB_blk (prevBase + k) (Or.inr (Or.inl ⟨by omega, by omega⟩))
          have h2 : stEB.mem (prevBase + k) = stPuRaw.mem (prevBase + k) :=
            Function.update_of_ne (by clear * - heb_prev hk_lt hkey_lt; omega) _ _
          have h3 : stPuRaw.mem (prevBase + k) = stErRaw.mem (prevBase + k) :=
            hfrPu (prevBase + k) (by unfold bsHeadBase; clear * - hblk_p' hk_lt hnb_lt; omega)
              (by omega) (by clear * - hprev_next hk_lt hkey_lt; omega)
              (fun y _ hy => by have := hLb_disj_Ln k (List.mem_of_mem_erase hk) y (hy ▸ List.mem_cons_self); omega)
          exact h1.trans (h2.trans h3)
        · intro k hk
          have hk_lt := hdll_b1.2.1 k hk
          have hkne : k ≠ key := fun h => hdll_b.1.mem_erase_iff.mp (h ▸ hk) |>.1 rfl
          have h1 := hBr_eq_EB_blk (nextBase + k) (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
          have h2 : stEB.mem (nextBase + k) = stPuRaw.mem (nextBase + k) :=
            Function.update_of_ne (by clear * - heb_next hk_lt hkey_lt; omega) _ _
          have h3 : stPuRaw.mem (nextBase + k) = stErRaw.mem (nextBase + k) :=
            hfrPu (nextBase + k) (by unfold bsHeadBase; clear * - hblk_n' hk_lt hnb_lt; omega)
              (by clear * - hprev_next hk_lt hkey_lt; omega) (by omega)
              (fun y _ hy => by have := hdll_n.2.1 y (hy ▸ List.mem_cons_self); clear * - hprev_next hk_lt this; omega)
          exact h1.trans (h2.trans h3)
      have hdll_n_next : IsDoublyLinkedList stNext.mem prevBase nextBase (bsHeadBase p + nB) (2 * eCap) (key :: L_new) := by
        refine hdll_n2.of_agree ?_ ?_ ?_
        · have h1 := hBr_eq_EB_blk (bsHeadBase p + nB) (Or.inl ⟨by unfold bsHeadBase; omega,
            by unfold bsHeadBase bundleSlotBlockSize; omega⟩)
          have h2 : stEB.mem (bsHeadBase p + nB) = stPuRaw.mem (bsHeadBase p + nB) :=
            Function.update_of_ne (by unfold bsHeadBase; clear * - heb_b' hnb_lt hkey_lt; omega) _ _
          exact h1.trans h2
        · intro k hk
          have hk_lt := hdll_n2.2.1 k hk
          have h1 := hBr_eq_EB_blk (prevBase + k) (Or.inr (Or.inl ⟨by omega, by omega⟩))
          have h2 : stEB.mem (prevBase + k) = stPuRaw.mem (prevBase + k) :=
            Function.update_of_ne (by clear * - heb_prev hk_lt hkey_lt; omega) _ _
          exact h1.trans h2
        · intro k hk
          have hk_lt := hdll_n2.2.1 k hk
          have h1 := hBr_eq_EB_blk (nextBase + k) (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
          have h2 : stEB.mem (nextBase + k) = stPuRaw.mem (nextBase + k) :=
            Function.update_of_ne (by clear * - heb_next hk_lt hkey_lt; omega) _ _
          exact h1.trans h2
      obtain ⟨stEnd, cEnd, L_b', L_new', hrest, hregsE, hr29E, hr33E, hr34E, hdll_bE, hLbE_len,
        hLbE_mem, hdll_nE, hLnE_len, hLnE_mem, hLtE, hLhE, hebE, hfrE, hcEnd⟩ :=
        ih (t + 1) (by omega) stNext (L_b.erase key) (key :: L_new)
          (fun r hr h29 => by
            simp only [stNext, Function.update_of_ne h29]
            rw [hregsBr r hr]; simp [stEB, stPu, stEr, st37, st36, show r ≠ 38 by omega,
              show r ≠ 37 by omega, show r ≠ 36 by omega, hregs r hr h29])
          (by simp [stNext]) (by simp [stNext, hr33Br]) (by simp [stNext, hr34Br])
          (by simp [stNext, hr35Br])
          hdll_b_next
          (by have h1 := List.length_erase_of_mem hkey_in_Lb; have h2 := List.length_pos_of_mem hkey_in_Lb
              clear * - h1 h2 hLb_len; omega)
          (fun k => by
            rw [hdll_b.1.mem_erase_iff, hLb_mem, htake_succ, List.mem_append, List.mem_singleton]
            have hne_iff : k ≠ key ↔ endOfKey k ≠ x := ⟨fun h heq => h (by rw [← bundle_endKey_endOfKey k, heq]),
              fun h heq => h (by rw [heq, bundle_endOfKey_endKey])⟩
            rw [hne_iff]; clear * -; tauto)
          hdll_n_next (by simp [hLn_len])
          (fun k => by
            rw [List.mem_cons, hLn_mem, htake_succ, List.mem_append, List.mem_singleton]
            have heq_iff : k = key ↔ endOfKey k = x := ⟨fun h => by rw [h, bundle_endOfKey_endKey],
              fun h => by rw [← bundle_endKey_endOfKey k, h]⟩
            rw [heq_iff]; clear * -; tauto)
          hLtBr hLhBr
          (fun y hy => by
            rw [htake_succ, List.mem_append, List.mem_singleton] at hy
            have hy_lt := hxs_key_lt y (by rcases hy with hy | rfl; exact List.mem_of_mem_take hy; exact hx_mem)
            have h1 := hBr_eq_EB_blk (endBundleBase + endKey y) (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
            dsimp only [stNext]; rw [h1]
            rcases hy with hy | rfl
            · have hne : endKey y ≠ key := fun h => hx_not_take (by
                have := congrArg endOfKey h; simp only [key, bundle_endOfKey_endKey] at this; exact this ▸ hy)
              dsimp only [stEB]; rw [Function.update_of_ne (by omega)]
              have hpu := hfrPu (endBundleBase + endKey y) (by unfold bsHeadBase; clear * - heb_b' hy_lt hnb_lt; omega)
                (by clear * - heb_prev hy_lt hkey_lt; omega) (by clear * - heb_next hy_lt hkey_lt; omega)
                (fun z _ hz => by have := hdll_n.2.1 z (hz ▸ List.mem_cons_self); clear * - heb_prev hy_lt this; omega)
              rw [hpu, hfrEr _ (by unfold bsHeadBase; clear * - heb_b' hy_lt hb_lt hnb_lt; omega) fun k hk =>
                ⟨by have := hL0_lt k (hLb_sub_L0 k hk); clear * - heb_prev hy_lt this; omega,
                 by have := hL0_lt k (hLb_sub_L0 k hk); clear * - heb_next hy_lt this; omega⟩]
              exact heb y hy
            · simp [stEB, key])
          (fun a ha1 ha2 haL haEB haBat haH => by
            dsimp only [stNext]
            have h1 : stBr.mem a = stEB.mem a := hfrBr a (by
              rcases haBat with h | h
              · exact Or.inl (by omega)
              · exact Or.inr h) (by
              rcases haH with h | h
              · exact Or.inl (by omega)
              · exact Or.inr h)
            have ha_not_key : a ≠ endBundleBase + key := haEB x (by rw [htake_succ]; simp)
            have hkey_in_L0 : key ∈ L_b0 := (hL0_mem key).mpr (by rwa [bundle_endOfKey_endKey])
            rw [h1]; dsimp only [stEB]; rw [Function.update_of_ne ha_not_key]
            rw [hfrPu a ha2 (haL key hkey_in_L0).1 (haL key hkey_in_L0).2
              (fun y _ hy => (haL y (hLn_sub_L0 y (hy ▸ List.mem_cons_self))).1)]
            rw [hfrEr a ha1 fun k hk => haL k (hLb_sub_L0 k hk)]
            have hle_t : (runTailEdges (xs.take t)).length ≤ (runTailEdges (xs.take (t + 1))).length := by
              rw [htake_succ]; simp [runTailEdges]
            have hle_h : (runHeadEdges (xs.take t)).length ≤ (runHeadEdges (xs.take (t + 1))).length := by
              rw [htake_succ]; simp [runHeadEdges]
            exact hfr a ha1 ha2 haL (fun y hy => haEB y (by rw [htake_succ]; exact List.mem_append_left _ hy))
              (by rcases haBat with h | h; exact Or.inl h; exact Or.inr (by omega))
              (by rcases haH with h | h; exact Or.inl h; exact Or.inr (by omega)))
      have hrun_l := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stNext, _, cEnd,
        by simp [Expr.eval, hr35'], by decide, hbody, hrest, rfl⟩))
      refine ⟨stEnd, _, L_b', L_new', hrun_l, hregsE, hr29E, hr33E, hr34E, hdll_bE, hLbE_len,
        hLbE_mem, hdll_nE, hLnE_len, hLnE_mem, hLtE, hLhE, hebE, hfrE, ?_⟩
      simp only [Expr.size] at *
      dsimp only [bundleDllEraseContract, bundleDllPushContract] at hcEr hcPu
      omega
  exact hloop xs.length 0 (by omega) st₀ L_b0 [] (fun _ _ _ => rfl) (by omega)
    (by simp [hr33, runTailEdges]) (by simp [hr34, runHeadEdges]) hr35 hdll_b0 (by omega)
    (by simpa using hL0_mem) hdll_n0 rfl (by simp) (by intro j hj; simp [runTailEdges] at hj)
    (by intro j hj; simp [runHeadEdges] at hj) (by simp) (fun _ _ _ _ _ _ _ => rfl)

end

end MinCostFlow.SparseCore.Program
