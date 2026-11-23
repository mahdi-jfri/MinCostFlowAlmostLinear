module

public import MinCostFlow.Spanner.ProgSetup
import Mathlib.Tactic

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Procedure 3: `dedupListModule` (`O(len + 1)`) -/

/-- `dedupListBody` deduplicates `xs` at `[srcAddr, srcAddr + len)` into `[dstAddr, dstAddr + xs.dedup.length)`
(`args = [srcAddr, len, bound, dstAddr, h]`), matching `xs.dedup` exactly in `O(len + 1)` time. -/
def dedupListBody : Stmt :=
  .assign 5 (.bin .add (.reg 4) (.reg 1)) ;;
  .assign 6 (.reg 5) ;;
  forRange 7 (.const 0) (.reg 1) (
    .assign 11 (.bin .sub (.bin .sub (.reg 1) (.const 1)) (.reg 7)) ;;
    .assign 8 (.load (.bin .add (.reg 0) (.reg 11))) ;;
    .cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 8))) (.const 0)) (
      .store (.bin .add (.reg 6) (.reg 8)) (.const 1) ;;
      .assign 5 (.bin .sub (.reg 5) (.const 1)) ;;
      .store (.reg 5) (.reg 8)
    ) (.assign 8 (.const 0))
  ) ;;
  .assign 9 (.bin .sub (.reg 6) (.reg 5)) ;;
  forRange 10 (.const 0) (.reg 9) (
    .store (.bin .add (.reg 3) (.reg 10)) (.load (.bin .add (.reg 5) (.reg 10)))
  ) ;;
  .ret (.reg 9)

/-- Single-procedure module for `dedupList`. -/
def dedupListModule : List Stmt := [dedupListBody]

theorem dedupListBody_noRand : dedupListBody.NoRand := by
  simp [dedupListBody, forRange, forUp, Stmt.NoRand]

theorem dedupListModule_noRand : ∀ s ∈ dedupListModule, s.NoRand := by
  simp only [dedupListModule, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact dedupListBody_noRand

/-- Contract for `dedupList`: `args = [srcAddr, len, bound, dstAddr, h]`. -/
def dedupListContract (w : ℕ) : Contract where
  pre args mem := ∃ (srcAddr len bound dstAddr h : ℕ) (xs : List ℕ),
    args = [srcAddr, len, bound, dstAddr, h] ∧
    xs.length = len ∧
    ListAt mem srcAddr xs ∧
    (∀ x ∈ xs, x < bound) ∧
    1 < 2 ^ w ∧
    srcAddr + len ≤ h ∧
    dstAddr + len ≤ h ∧
    h + len + bound < 2 ^ w ∧
    ZeroFrom mem h
  post args mem v mem' := ∀ srcAddr len bound dstAddr h (xs : List ℕ),
    args = [srcAddr, len, bound, dstAddr, h] →
    xs.length = len → ListAt mem srcAddr xs →
      v = xs.dedup.length ∧
      ListAt mem' dstAddr xs.dedup ∧
      ZeroFrom mem' (h + len + bound) ∧
      (∀ x, x < dstAddr → mem' x = mem x) ∧
      (∀ x, dstAddr + xs.dedup.length ≤ x → x < h → mem' x = mem x)
  cost args _ := 115 * args.getD 1 0 + 55

private theorem list_dedup_cons {α : Type*} [DecidableEq α] (x : α) (ys : List α) :
    (x :: ys).dedup = if x ∈ ys then ys.dedup else x :: ys.dedup := by
  by_cases h : x ∈ ys
  · simp [List.dedup_cons_of_mem h, h]
  · simp [List.dedup_cons_of_notMem h, h]

private theorem list_dedup_length_le {α : Type*} [DecidableEq α] (xs : List α) :
    xs.dedup.length ≤ xs.length :=
  (List.dedup_sublist xs).length_le

private def dedupInv1 (srcAddr len bound dstAddr h : ℕ) (xs : List ℕ) (mem : ℕ → ℕ)
    (k : ℕ) (st : State) : Prop :=
  st.regs 0 = srcAddr ∧ st.regs 1 = len ∧ st.regs 2 = bound ∧ st.regs 3 = dstAddr ∧
  st.regs 4 = h ∧ st.regs 5 = (h + len) - (xs.drop (len - k)).dedup.length ∧
  st.regs 6 = h + len ∧ st.regs 7 = k ∧
  k ≤ len ∧
  (xs.drop (len - k)).dedup.length ≤ k ∧
  ListAt st.mem (st.regs 5) (xs.drop (len - k)).dedup ∧
  (∀ y < bound, st.mem (h + len + y) = if y ∈ xs.drop (len - k) then 1 else 0) ∧
  AgreeOutside st.mem mem h (h + len + bound) ∧
  ZeroFrom st.mem (h + len + bound)

private def dedupInv2 (len bound dstAddr h : ℕ) (xs : List ℕ) (mem : ℕ → ℕ)
    (t : ℕ) (st : State) : Prop :=
  st.regs 3 = dstAddr ∧ st.regs 5 = (h + len) - xs.dedup.length ∧
  st.regs 9 = xs.dedup.length ∧ st.regs 10 = t ∧
  t ≤ xs.dedup.length ∧
  ListAt st.mem ((h + len) - xs.dedup.length) xs.dedup ∧
  ListAt st.mem dstAddr (xs.dedup.take t) ∧
  AgreeOutside st.mem mem (min dstAddr h) (h + len + bound) ∧
  (∀ x, x < dstAddr → st.mem x = mem x) ∧
  (∀ x, dstAddr + t ≤ x → x < h → st.mem x = mem x) ∧
  ZeroFrom st.mem (h + len + bound)

private theorem dedupList_loop1_triple {w : ℕ} {p : Program}
    (srcAddr len bound dstAddr h : ℕ) (xs : List ℕ) (mem : ℕ → ℕ)
    (hlen : xs.length = len) (hxs : ListAt mem srcAddr xs) (hbound : ∀ x ∈ xs, x < bound)
    (hw1 : 1 < 2 ^ w) (hsrc_w : srcAddr < 2 ^ w) (hlen_w : len < 2 ^ w)
    (hsh : srcAddr + len ≤ h) (hhb : h + len + bound < 2 ^ w) (hz : ZeroFrom mem h) :
    Triple w p
      (fun st =>
        st.regs 0 = srcAddr ∧ st.regs 1 = len ∧ st.regs 2 = bound ∧ st.regs 3 = dstAddr ∧
        st.regs 4 = h ∧ st.regs 5 = h + len ∧ st.regs 6 = h + len ∧ st.mem = mem)
      (forRange 7 (.const 0) (.reg 1) (
        .assign 11 (.bin .sub (.bin .sub (.reg 1) (.const 1)) (.reg 7)) ;;
        .assign 8 (.load (.bin .add (.reg 0) (.reg 11))) ;;
        .cond (.bin .eq (.load (.bin .add (.reg 6) (.reg 8))) (.const 0)) (
          .store (.bin .add (.reg 6) (.reg 8)) (.const 1) ;;
          .assign 5 (.bin .sub (.reg 5) (.const 1)) ;;
          .store (.reg 5) (.reg 8)
        ) (.assign 8 (.const 0))
      ))
      (normalPost (dedupInv1 srcAddr len bound dstAddr h xs mem len))
      (fun _ => len * (70 + (Expr.reg 1).size + 8) + ((Expr.const 0).size + (Expr.reg 1).size + 5)) := by
  let seenBase := h + len
  let totalEnd := h + len + bound
  have hw0 : 0 < 2 ^ w := Nat.zero_lt_of_lt hw1
  have hseenBase_w : seenBase < 2 ^ w := by omega
  refine Triple.forRange_const (p := p) (w := w) (r := 7) (lo := .const 0) (hi := .reg 1)
    (Inv := dedupInv1 srcAddr len bound dstAddr h xs mem) 70 0 len (Nat.zero_le _) hw1 (fun _ => hlen_w)
    ?_ ?_ ?_ ?_
  · intro st hP
    rcases hP with ⟨r0, r1, r2, r3, r4, r5, r6, hmem⟩
    have hdrop_nil : xs.drop len = [] := List.drop_of_length_le (Nat.le_of_eq hlen)
    refine ⟨Expr.eval_const hw0, ⟨r0, r1, r2, r3, r4, ?_, r6,
      by simp [Function.update_self], Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [hdrop_nil, r5]
    · simp [hdrop_nil]
    · simp [hdrop_nil, listAt_nil]
    · intro y _; rw [hmem]; simp [hdrop_nil]; exact hz _ (by omega)
    · rw [hmem]; exact agreeOutside_refl _ _ _
    · rw [hmem]; exact fun x hx => hz x (by omega)
  · intro _ _ _ _ h; exact h.2.2.2.2.2.2.2.1
  · intro _ _ _ _ h; exact ev_reg h.2.1 hlen_w
  · intro k _ hk st ω hInv
    rcases hInv with ⟨r0, r1, r2, r3, r4, r5, r6, r7, hklen, hded_le, hlist_tail, hseen_tail, hag, hzt⟩
    let idx := len - 1 - k
    have hidx_lt : idx < xs.length := by omega
    let x := xs[idx]'hidx_lt
    let tail := xs.drop (len - k)
    have hdrop_next : xs.drop (len - (k + 1)) = x :: tail := by
      have hsub1 : len - (k + 1) = idx := by omega
      have hsub2 : idx + 1 = len - k := by omega
      have hcons := List.getElem_cons_drop (as := xs) (i := idx) hidx_lt
      simpa [x, tail, hsub1, hsub2] using hcons.symm
    have hx_bound : x < bound := hbound x (List.getElem_mem hidx_lt)
    have hx_w : x < 2 ^ w := by omega
    have hidx_w : idx < 2 ^ w := by omega
    have hlen1_w : len - 1 < 2 ^ w := by omega
    have ha_src_w : srcAddr + idx < 2 ^ w := by omega
    have ha_seen_w : seenBase + x < 2 ^ w := by dsimp only [seenBase]; omega
    have hxs_st : ListAt st.mem srcAddr xs := listAt_of_agreeOutside hxs hag (Or.inl (by omega))
    have hx_mem : st.mem (srcAddr + idx) = x := by simpa [x] using listAt_getElem hxs_st hidx_lt
    have hseen_x_w : st.mem (seenBase + x) < 2 ^ w := by
      rw [hseen_tail x hx_bound]; split_ifs <;> omega
    have hev_idx : (Expr.bin .sub (.bin .sub (.reg 1) (.const 1)) (.reg 7)).eval w st = some idx :=
      ev_sub (ev_sub (ev_reg r1 hlen_w) (ev_const hw1) (by omega) hlen1_w) (ev_reg r7 (by omega))
        (by omega) hidx_w
    let s1 : State := ⟨st.mem, Function.update st.regs 11 idx, st.pos⟩
    have hev_x : (Expr.load (.bin .add (.reg 0) (.reg 11))).eval w s1 = some x :=
      ev_load (ev_add (ev_reg (by simp [s1, r0]) hsrc_w) (ev_reg (by simp [s1]) hidx_w) ha_src_w) hx_mem hx_w
    let s2 : State := ⟨st.mem, Function.update s1.regs 8 x, st.pos⟩
    have ha_seen_s2 : (Expr.bin .add (.reg 6) (.reg 8)).eval w s2 = some (seenBase + x) :=
      ev_add (ev_reg (by simp [s2, s1, r6, seenBase]) hseenBase_w) (ev_reg (by simp [s2]) hx_w) ha_seen_w
    have hev_load_seen : (Expr.load (.bin .add (.reg 6) (.reg 8))).eval w s2 = some (st.mem (seenBase + x)) :=
      ev_load ha_seen_s2 rfl hseen_x_w
    apply runs_start_le
    refine runs_seq_assign_le hev_idx ?_
    refine runs_seq_assign_le hev_x ?_
    by_cases hx_mem_tail : x ∈ tail
    · have hload0 : st.mem (seenBase + x) = 1 := by
        rw [hseen_tail x hx_bound]; simpa [tail] using hx_mem_tail
      have hcond : (Expr.bin .eq (.load (.bin .add (.reg 6) (.reg 8))) (.const 0)).eval w s2 = some 0 :=
        ev_eq_f (by simpa [hload0] using hev_load_seen) (ev_const hw0) (by decide) hw1
      have hded_next : (xs.drop (len - (k + 1))).dedup = tail.dedup := by
        rw [hdrop_next, list_dedup_cons]; simp [hx_mem_tail]
      refine runs_cond_le hcond (fun h0 => absurd rfl h0) fun _ => ?_
      refine runs_assign_le (ev_const hw0) ?_ (by norm_num [Expr.size])
      · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, hag, hzt⟩, ?_⟩
        all_goals try dsimp only [s2, s1]
        · simp [r0]
        · simp [r1]
        · simp [r2]
        · simp [r3]
        · simp [r4]
        · rw [hded_next]; simpa [tail] using r5
        · simp [r6]
        · simp [Function.update_self]
        · rw [hded_next]; exact Nat.le_succ_of_le hded_le
        · rw [hded_next]
          have hr5_eq : Function.update (Function.update (Function.update (Function.update st.regs 11 idx) 8 x) 8 0) 7 (k + 1) 5 = st.regs 5 := by
            simp
          rw [hr5_eq]; exact hlist_tail
        · intro y hy
          rw [hseen_tail y hy, hdrop_next]
          by_cases hyx : y = x
          · subst hyx; simp [hx_mem_tail, tail]
          · simp [hyx, tail]
        · simp [r7]
    · have hload0 : st.mem (seenBase + x) = 0 := by
        rw [hseen_tail x hx_bound]; simpa [tail] using hx_mem_tail
      have hcond : (Expr.bin .eq (.load (.bin .add (.reg 6) (.reg 8))) (.const 0)).eval w s2 = some 1 :=
        ev_eq_t (by simpa [hload0] using hev_load_seen) (ev_const hw0) rfl hw1
      have hded_next : (xs.drop (len - (k + 1))).dedup = x :: tail.dedup := by
        rw [hdrop_next, list_dedup_cons]; simp [hx_mem_tail]
      have hlen_ded_next : (xs.drop (len - (k + 1))).dedup.length = tail.dedup.length + 1 := by
        rw [hded_next, List.length_cons]
      have hr5_ge_h1 : h + 1 ≤ st.regs 5 := by dsimp only [tail] at *; omega
      have hr5_pred : st.regs 5 - 1 = seenBase - (tail.dedup.length + 1) := by
        dsimp only [seenBase, tail] at *; omega
      have hr5_w : st.regs 5 < 2 ^ w := by omega
      have hr5_pred_w : st.regs 5 - 1 < 2 ^ w := by omega
      let m1 := Function.update st.mem (seenBase + x) 1
      let s3 : State := ⟨m1, s2.regs, st.pos⟩
      have hev_wp' : (Expr.bin .sub (.reg 5) (.const 1)).eval w s3 = some (st.regs 5 - 1) :=
        ev_sub (ev_reg (by simp [s3, s2, s1]) hr5_w) (ev_const hw1) (by omega) hr5_pred_w
      let s4 : State := ⟨m1, Function.update s2.regs 5 (st.regs 5 - 1), st.pos⟩
      let m2 := Function.update m1 (st.regs 5 - 1) x
      have hag_m1 : AgreeOutside m1 st.mem h totalEnd :=
        agreeOutside_update (lo := h) (hi := totalEnd)
          (by dsimp only [seenBase]; omega) (by dsimp only [seenBase, totalEnd]; omega)
      have hag_m2 : AgreeOutside m2 m1 h totalEnd :=
        agreeOutside_update (lo := h) (hi := totalEnd)
          (by omega) (by dsimp only [totalEnd]; omega)
      have hag_step : AgreeOutside m2 st.mem h totalEnd := agreeOutside_trans hag_m2 hag_m1 le_rfl le_rfl
      refine runs_cond_le hcond (fun _ => ?_) (fun h1 => absurd h1 (by decide))
      refine runs_seq_store_le ha_seen_s2 (ev_const hw1) ?_
      refine runs_seq_assign_le hev_wp' ?_
      refine runs_store_le (ev_reg (by simp [Function.update_self]) hr5_pred_w)
        (ev_reg (by simp) hx_w) ?_ (by norm_num [Expr.size])
      · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_,
          agreeOutside_trans hag_step hag le_rfl le_rfl,
          zeroFrom_of_agreeOutside hzt hag_step le_rfl⟩, ?_⟩
        all_goals try dsimp only [s4, s2, s1]
        · simp [r0]
        · simp [r1]
        · simp [r2]
        · simp [r3]
        · simp [r4]
        · rw [hlen_ded_next]; simp [Function.update_self]; exact hr5_pred
        · simp [r6]
        · simp [Function.update_self]
        · rw [hlen_ded_next]; omega
        · rw [hded_next]
          have hr5_eq' : Function.update (Function.update (Function.update (Function.update st.regs 11 idx) 8 x) 5 (st.regs 5 - 1)) 7 (k + 1) 5 = st.regs 5 - 1 := by
            simp
          rw [hr5_eq', listAt_cons]
          refine ⟨by change m2 (st.regs 5 - 1) = x; simp [m2, Function.update_self], ?_⟩
          have htail_adr : (st.regs 5 - 1) + 1 = st.regs 5 := by omega
          rw [htail_adr]
          refine listAt_of_congr hlist_tail fun i hi => ?_
          change m2 (st.regs 5 + i) = st.mem (st.regs 5 + i)
          dsimp only [m2, m1]
          rw [Function.update_of_ne (by omega : st.regs 5 + i ≠ st.regs 5 - 1),
              Function.update_of_ne (by dsimp only [seenBase, tail] at *; omega)]
        · intro y hy
          have hne_write : seenBase + y ≠ st.regs 5 - 1 := by dsimp only [seenBase] at *; omega
          rw [hdrop_next]
          change m2 (seenBase + y) = if y ∈ x :: tail then 1 else 0
          dsimp only [m2]; rw [Function.update_of_ne hne_write]
          by_cases hyx : y = x
          · subst hyx; simp [m1, Function.update_self]
          · dsimp only [m1]
            rw [Function.update_of_ne (by omega : seenBase + y ≠ seenBase + x), hseen_tail y hy]
            simp [hyx, tail]
        · simp [r7]

private theorem dedupList_loop2_triple {w : ℕ} {p : Program}
    (len bound dstAddr h : ℕ) (xs : List ℕ) (mem : ℕ → ℕ)
    (hlen : xs.length = len) (hbound : ∀ x ∈ xs, x < bound) (hw1 : 1 < 2 ^ w)
    (hdst_w : dstAddr < 2 ^ w) (hdh : dstAddr + len ≤ h) (hhb : h + len + bound < 2 ^ w) :
    Triple w p
      (fun st =>
        st.regs 3 = dstAddr ∧ st.regs 5 = (h + len) - xs.dedup.length ∧
        st.regs 9 = xs.dedup.length ∧
        ListAt st.mem ((h + len) - xs.dedup.length) xs.dedup ∧
        AgreeOutside st.mem mem h (h + len + bound) ∧
        ZeroFrom st.mem (h + len + bound))
      (forRange 10 (.const 0) (.reg 9) (
        .store (.bin .add (.reg 3) (.reg 10)) (.load (.bin .add (.reg 5) (.reg 10)))
      ))
      (normalPost (dedupInv2 len bound dstAddr h xs mem xs.dedup.length))
      (fun _ => xs.dedup.length * (25 + (Expr.reg 9).size + 8) + ((Expr.const 0).size + (Expr.reg 9).size + 5)) := by
  let seenBase := h + len
  let totalEnd := h + len + bound
  let keptLen := xs.dedup.length
  let writePtr := seenBase - keptLen
  have hw0 : 0 < 2 ^ w := Nat.zero_lt_of_lt hw1
  have hkept_le : keptLen ≤ len := by rw [← hlen]; exact list_dedup_length_le xs
  have hkept_w : keptLen < 2 ^ w := by omega
  have hwp_w : writePtr < 2 ^ w := by dsimp only [writePtr, seenBase]; omega
  refine Triple.forRange_const (p := p) (w := w) (r := 10) (lo := .const 0) (hi := .reg 9)
    (Inv := dedupInv2 len bound dstAddr h xs mem) 25 0 keptLen (Nat.zero_le _) hw1 (fun _ => hkept_w)
    ?_ ?_ ?_ ?_
  · intro st hP
    rcases hP with ⟨r3, r5, r9, hwp, hag, hzt⟩
    refine ⟨Expr.eval_const hw0, ⟨r3, r5, r9, by simp [Function.update_self], Nat.zero_le _,
      hwp, by simp [listAt_nil], agreeOutside_mono hag (min_le_right _ _) le_rfl,
      fun x hx => hag x (Or.inl (by omega)),
      fun x _ hx2 => hag x (Or.inl hx2), hzt⟩⟩
  · intro _ _ _ _ h; exact h.2.2.2.1
  · intro _ _ _ _ h; exact ev_reg h.2.2.1 hkept_w
  · intro t _ ht st ω hInv
    rcases hInv with ⟨r3, r5, r9, r10, htk, hwp, hdt, hag, hlt_d, hmid_dh, hzt⟩
    let val := xs.dedup[t]'ht
    have hval_mem : st.mem (writePtr + t) = val := listAt_getElem hwp ht
    have hval_in : val ∈ xs := List.mem_dedup.mp (List.getElem_mem ht)
    have hval_w : val < 2 ^ w := by have := hbound val hval_in; omega
    have ht_w : t < 2 ^ w := by omega
    have hadr_src_w : writePtr + t < 2 ^ w := by dsimp only [writePtr, seenBase]; omega
    have hadr_dst_w : dstAddr + t < 2 ^ w := by omega
    have ha_dst : (Expr.bin .add (.reg 3) (.reg 10)).eval w st = some (dstAddr + t) :=
      ev_add (ev_reg r3 hdst_w) (ev_reg r10 ht_w) hadr_dst_w
    have hv_load : (Expr.load (.bin .add (.reg 5) (.reg 10))).eval w st = some val :=
      ev_load (ev_add (ev_reg r5 hwp_w) (ev_reg r10 ht_w) hadr_src_w) hval_mem hval_w
    apply runs_start_le
    let mem' := Function.update st.mem (dstAddr + t) val
    refine ⟨.normal, ⟨mem', st.regs, st.pos⟩, _,
      runs_store_iff.mpr ⟨dstAddr + t, val, ha_dst, hv_load, rfl, rfl, rfl⟩,
      ?_, by norm_num [Expr.size]⟩
    have hag_step_tot : AgreeOutside mem' st.mem (min dstAddr h) totalEnd :=
      agreeOutside_update (lo := min dstAddr h) (hi := totalEnd)
        (le_trans (min_le_left _ _) (Nat.le_add_right _ _)) (by dsimp only [totalEnd]; omega)
    have hag_step_pt : AgreeOutside mem' st.mem (dstAddr + t) (dstAddr + t + 1) :=
      agreeOutside_update (lo := dstAddr + t) (hi := dstAddr + t + 1) le_rfl (by omega)
    have htake : xs.dedup.take (t + 1) = xs.dedup.take t ++ [val] := by
      rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some]
    refine ⟨⟨r3, r5, r9, by simp [Function.update_self], by omega, ?_, ?_,
      agreeOutside_trans hag_step_tot hag le_rfl le_rfl, ?_, ?_,
      zeroFrom_of_agreeOutside hzt hag_step_tot le_rfl⟩, r10⟩
    · exact listAt_of_agreeOutside hwp hag_step_pt (Or.inr (by omega))
    · rw [htake]
      have hdt_len : (xs.dedup.take t).length = t := List.length_take_of_le (le_of_lt ht)
      refine listAt_append_right_single (listAt_of_agreeOutside hdt hag_step_pt (Or.inl (by omega))) ?_
      rw [hdt_len]
      exact Function.update_self _ _ _
    · intro x hx; dsimp only [mem']; rw [Function.update_of_ne (by omega : x ≠ dstAddr + t)]; exact hlt_d x hx
    · intro x hx1 hx2; dsimp only [mem']; rw [Function.update_of_ne (by omega : x ≠ dstAddr + t)]; exact hmid_dh x (by omega) hx2

/-- `dedupListModule` meets `dedupListContract w` in `O(len + 1)` time. -/
theorem dedupList_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b dedupListModule) :
    MeetsContract w p b (dedupListContract w) := by
  refine meetsContract_of_triple hp.head ?_
  intro args mem pos hwords hpre
  dsimp only [dedupListContract] at hpre
  rcases hpre with ⟨srcAddr, len, bound, dstAddr, h, xs,
    rfl, hlen, hxs, hbound, hw1, hsh, hdh, hhb, hz⟩
  have hsrc_w : srcAddr < 2 ^ w := hwords srcAddr (by simp)
  have hlen_w : len < 2 ^ w := hwords len (by simp)
  have hdst_w : dstAddr < 2 ^ w := hwords dstAddr (by simp)
  have hh_w : h < 2 ^ w := hwords h (by simp)
  let seenBase := h + len
  let totalEnd := h + len + bound
  let keptLen := xs.dedup.length
  let writePtr := seenBase - keptLen
  have hseenBase_w : seenBase < 2 ^ w := by omega
  have hkept_le : keptLen ≤ len := by rw [← hlen]; exact list_dedup_length_le xs
  have hkept_w : keptLen < 2 ^ w := by omega
  have hwp_w : writePtr < 2 ^ w := by dsimp only [writePtr, seenBase]; omega
  have ht1 : Triple w p (fun st => st = startState [srcAddr, len, bound, dstAddr, h] mem pos)
      (.assign 5 (.bin .add (.reg 4) (.reg 1)))
      (normalPost fun st =>
        st.regs 0 = srcAddr ∧ st.regs 1 = len ∧ st.regs 2 = bound ∧ st.regs 3 = dstAddr ∧
        st.regs 4 = h ∧ st.regs 5 = h + len ∧ st.mem = mem)
      (fun _ => (Expr.bin .add (.reg 4) (.reg 1)).size + 1) := by
    refine Triple.assign (val := fun _ => seenBase) ?_ ?_
    · intro st hst; subst hst
      exact ev_add (ev_reg (by simp [startState]) hh_w) (ev_reg (by simp [startState]) hlen_w) hseenBase_w
    · intro st hst; subst hst; simp [startState, seenBase]
  have ht2 : Triple w p
      (fun st =>
        st.regs 0 = srcAddr ∧ st.regs 1 = len ∧ st.regs 2 = bound ∧ st.regs 3 = dstAddr ∧
        st.regs 4 = h ∧ st.regs 5 = h + len ∧ st.mem = mem)
      (.assign 6 (.reg 5))
      (normalPost fun st =>
        st.regs 0 = srcAddr ∧ st.regs 1 = len ∧ st.regs 2 = bound ∧ st.regs 3 = dstAddr ∧
        st.regs 4 = h ∧ st.regs 5 = h + len ∧ st.regs 6 = h + len ∧ st.mem = mem)
      (fun _ => (Expr.reg 5).size + 1) := by
    refine Triple.assign (val := fun _ => seenBase) ?_ ?_
    · intro st hP; exact ev_reg hP.2.2.2.2.2.1 hseenBase_w
    · intro st hP
      rcases hP with ⟨q0, q1, q2, q3, q4, q5, hm⟩
      refine ⟨by simp [q0], by simp [q1], by simp [q2], by simp [q3], by simp [q4],
        by simp [q5], by simp [seenBase], hm⟩
  have hfor1 := dedupList_loop1_triple (p := p) srcAddr len bound dstAddr h xs mem
    hlen hxs hbound hw1 hsrc_w hlen_w hsh hhb hz
  have hmid_assign : Triple w p (dedupInv1 srcAddr len bound dstAddr h xs mem len)
      (.assign 9 (.bin .sub (.reg 6) (.reg 5)))
      (normalPost fun st =>
        st.regs 3 = dstAddr ∧ st.regs 5 = (h + len) - xs.dedup.length ∧
        st.regs 9 = xs.dedup.length ∧
        ListAt st.mem ((h + len) - xs.dedup.length) xs.dedup ∧
        AgreeOutside st.mem mem h (h + len + bound) ∧
        ZeroFrom st.mem (h + len + bound))
      (fun _ => (Expr.bin .sub (.reg 6) (.reg 5)).size + 1) := by
    refine Triple.assign (val := fun _ => keptLen) ?_ ?_
    · intro st hInv
      rcases hInv with ⟨_, _, _, _, _, r5, r6, _⟩
      have hdrop0 : xs.drop (len - len) = xs := by simp
      have hq5' : st.regs 5 = writePtr := by simpa [writePtr, keptLen, seenBase, hdrop0] using r5
      have hsub : seenBase - writePtr = keptLen := by dsimp only [writePtr, seenBase]; omega
      rw [← hsub]
      exact ev_sub (ev_reg r6 hseenBase_w) (ev_reg hq5' hwp_w)
        (by dsimp only [writePtr, seenBase]; omega) (by rw [hsub]; exact hkept_w)
    · intro st hInv
      rcases hInv with ⟨_, _, _, q3, _, q5, q6, _, _, _, hlist1, _, hag1, hzt1⟩
      have hdrop0 : xs.drop (len - len) = xs := by simp
      have hq5' : st.regs 5 = writePtr := by simpa [writePtr, keptLen, seenBase, hdrop0] using q5
      have hlist1' : ListAt st.mem writePtr xs.dedup := by simpa [writePtr, keptLen, seenBase, hdrop0, hq5'] using hlist1
      exact ⟨by simp [q3], by simp [hq5', writePtr, seenBase, keptLen],
        by simp [Function.update_self, keptLen], hlist1', hag1, hzt1⟩
  have hfor2 := dedupList_loop2_triple (p := p) len bound dstAddr h xs mem
    hlen hbound hw1 hdst_w hdh hhb
  have hret : Triple w p (dedupInv2 len bound dstAddr h xs mem xs.dedup.length)
      (.ret (.reg 9))
      (retPost fun v st' => (dedupListContract w).post [srcAddr, len, bound, dstAddr, h] mem v st'.mem)
      (fun _ => (Expr.reg 9).size + 1) := by
    refine Triple.ret (val := fun _ => keptLen) ?_ ?_
    · intro st hInv; exact ev_reg hInv.2.2.1 hkept_w
    · intro st hInv s' l' b' d' h' xs' heq hl' hxs'
      simp only [List.cons.injEq, and_true] at heq
      rcases heq with ⟨rfl, rfl, rfl, rfl, rfl⟩
      have hxs_eq : xs' = xs := listAt_eq_of_length_eq (by rw [hl', hlen]) hxs' hxs
      subst hxs_eq
      rcases hInv with ⟨_, _, _, _, _, _, hdt, _, hlt_d, hmid_dh, hzt⟩
      exact ⟨rfl, by simpa [keptLen, List.take_length] using hdt, hzt, hlt_d, hmid_dh⟩
  have hall := Triple.seq_normal_const ht1
    (Triple.seq_normal_const ht2
      (Triple.seq_normal_const hfor1
        (Triple.seq_normal_const hmid_assign (Triple.seq_normal_const hfor2 hret))))
  refine (hall.strengthen_post fun o st hPost => by
    cases o with
    | normal => simp at hPost
    | returned v => exact hPost).mono_cost ?_
  intro _ _
  simp only [dedupListContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
  omega

end MinCostFlow.Spanner
