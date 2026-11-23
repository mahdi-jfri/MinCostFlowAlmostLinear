module

public import MinCostFlow.Spanner.ProgEmbStatsBase
import Mathlib.Tactic

/-!
# Embedding statistics program: second loop and contract satisfaction

Proves the inner and outer second-loop triples and `embJHStats_meetsContract` for
`embJHStatsModule`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

private theorem embJHStats_inner_triple {w : ℕ} {p : Program}
    (jAddr embJHAddr h e ptr : ℕ) (J H' : Graph) (embJH : ℕ → Walk) (bound : ℕ)
    (mem : ℕ → ℕ) (stB st_base : State) (he : e < J.m)
    (hEmb : EmbAt mem embJHAddr J.m embJH) (_hBound : EmbBounded mem embJHAddr J.m embJH bound)
    (hVerts_H : ∀ e0 < J.m, ∀ x ∈ (embJH e0).verts, x < H'.n) (hw1 : 1 < 2 ^ w)
    (hbh : bound ≤ h) (hbw : bound < 2 ^ w) (hm2w : 2 * J.m + 2 < 2 ^ w)
    (hh_w : h + 3 + J.n + 2 * H'.n < 2 ^ w) (hptr_eq : ptr = mem (embJHAddr + e))
    (hptr_bound : ptr + (2 + (embJH e).verts.length + (embJH e).edges.length) ≤ bound)
    (hstB_mem : stB.mem = st_base.mem)
    (hstB_r : stB.regs 0 = jAddr ∧ stB.regs 1 = embJHAddr ∧ stB.regs 2 = H'.n ∧
      stB.regs 3 = h ∧ stB.regs 4 = J.n ∧ stB.regs 5 = J.m ∧
      stB.regs 6 = h + 3 ∧ stB.regs 7 = h + 3 + J.n ∧ stB.regs 8 = h + 3 + J.n + H'.n ∧
      stB.regs 9 = maxDeg J ∧ stB.regs 10 = lenPrefix embJH (e + 1) ∧
      stB.regs 11 = ((Finset.range H'.n).fold max 0 fun x => vcPrefix embJH e 0 x) ∧
      stB.regs 12 = e ∧ stB.regs 13 = ptr ∧ stB.regs 14 = (embJH e).verts.length)
    (hbase_vc : ∀ x < H'.n, st_base.mem (h + 3 + J.n + x) = vcPrefix embJH e 0 x)
    (hbase_seen : ∀ x < H'.n, st_base.mem (h + 3 + J.n + H'.n + x) ≤ e)
    (hbase_ag : AgreeOutside st_base.mem mem (h + 3) (h + 3 + J.n + 2 * H'.n))
    (hbase_zf : ZeroFrom st_base.mem (h + 3 + J.n + 2 * H'.n)) :
    Triple w p (fun s => s = stB)
      (forRange 16 (.const 0) (.reg 14) (
        .assign 17 (.load (.bin .add (.reg 13) (.bin .add (.const 1) (.reg 16)))) ;;
        .assign 15 (.load (.bin .add (.reg 8) (.reg 17))) ;;
        .cond (.bin .eq (.bin .eq (.reg 15) (.bin .add (.reg 12) (.const 1))) (.const 0)) (
          .store (.bin .add (.reg 8) (.reg 17)) (.bin .add (.reg 12) (.const 1)) ;;
          .assign 15 (.bin .add (.load (.bin .add (.reg 7) (.reg 17))) (.const 1)) ;;
          .store (.bin .add (.reg 7) (.reg 17)) (.reg 15) ;;
          .cond (.bin .lt (.reg 11) (.reg 15)) (.assign 11 (.reg 15)) (.assign 15 (.const 0))
        ) (.assign 15 (.const 0))
      ))
      (normalPost (embStatsInnerInv jAddr embJHAddr h e ptr J H' embJH mem st_base.mem (embJH e).verts.length))
      (fun _ => (embJH e).verts.length * (80 + (Expr.reg 14).size + 8) + ((Expr.const 0).size + (Expr.reg 14).size + 5)) := by
  let degBase := h + 3
  let vcBase := h + 3 + J.n
  let seenBase := h + 3 + J.n + H'.n
  let totalEnd := h + 3 + J.n + 2 * H'.n
  let vlen := (embJH e).verts.length
  have hw0 : 0 < 2 ^ w := Nat.zero_lt_of_lt hw1
  have he_w : e < 2 ^ w := by omega
  have he1_w : e + 1 < 2 ^ w := by omega
  have hptr_w : ptr < 2 ^ w := by omega
  have hvlen_w : vlen < 2 ^ w := by omega
  have hvcBase_w : vcBase < 2 ^ w := by omega
  have hseenBase_w : seenBase < 2 ^ w := by omega
  have hwalk_mem : WalkAt mem ptr (embJH e) := by rw [hptr_eq]; exact hEmb e he
  have hwalk_base : WalkAt st_base.mem ptr (embJH e) :=
    walkAt_of_agreeOutside hwalk_mem hbase_ag (Or.inl (by omega))
  refine Triple.forRange_const (p := p) (w := w) (r := 16) (lo := .const 0)
    (hi := .reg 14) (Inv := embStatsInnerInv jAddr embJHAddr h e ptr J H' embJH mem st_base.mem)
    80 0 vlen (Nat.zero_le _) hw1 (fun _ => hvlen_w) ?_ ?_ ?_ ?_
  · intro s hs; subst hs
    rcases hstB_r with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩
    refine ⟨Expr.eval_const hw0, ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
      by simp [Function.update_self], Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro x hx; rw [hstB_mem]; exact hbase_vc x hx
    · intro x hx; have hle := hbase_seen x hx; rw [hstB_mem]
      constructor
      · intro h1; omega
      · rintro ⟨s0, hs0, _⟩; omega
    · intro x hx; rw [hstB_mem]; exact le_trans (hbase_seen x hx) (Nat.le_succ e)
    · rw [hstB_mem]; exact hbase_ag
    · rw [hstB_mem]; exact agreeOutside_refl _ _ _
    · rw [hstB_mem]; exact hbase_zf
  · intro _ _ _ _ h; exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · intro _ _ _ _ h; exact ev_reg h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hvlen_w
  · intro t _ ht s ω_in hI
    rcases hI with ⟨i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i16,
      htv, hvc_t, hseen_iff, hseen_le, hag_tot, hag_vc, hz_in⟩
    set x := (embJH e).verts.getD t 0
    have hx_mem_verts : x ∈ (embJH e).verts := by
      dsimp only [x]; rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht
    have hx_Hn : x < H'.n := hVerts_H e he x hx_mem_verts
    have hx_w : x < 2 ^ w := by omega
    have ht_w : t < 2 ^ w := by omega
    have h1t_w : 1 + t < 2 ^ w := by omega
    have ha_vt_w : ptr + (1 + t) < 2 ^ w := by omega
    have hverts_s : ListAt s.mem (ptr + 1) (embJH e).verts :=
      listAt_of_agreeOutside hwalk_base.verts_listAt hag_vc (Or.inl (by omega))
    have hx_mem : s.mem (ptr + (1 + t)) = x := by
      dsimp only [x]
      rw [← Nat.add_assoc, listAt_getElem hverts_s ht, List.getD_eq_getElem _ _ ht]
    have ha_seen_w : seenBase + x < 2 ^ w := by dsimp only [seenBase]; omega
    have ha_vc_w : vcBase + x < 2 ^ w := by dsimp only [vcBase]; omega
    have hseen_x_w : s.mem (seenBase + x) < 2 ^ w := by
      have := hseen_le x hx_Hn; dsimp only [seenBase]; omega
    have hev_x : (Expr.load (.bin .add (.reg 13) (.bin .add (.const 1) (.reg 16)))).eval w s = some x :=
      ev_load (ev_add (ev_reg i13 hptr_w) (ev_add (ev_const hw1) (ev_reg i16 ht_w) h1t_w) ha_vt_w)
        hx_mem hx_w
    let s0x : State := ⟨s.mem, Function.update s.regs 17 x, s.pos⟩
    have hev_sn : (Expr.load (.bin .add (.reg 8) (.reg 17))).eval w s0x = some (s.mem (seenBase + x)) :=
      ev_load (ev_add (ev_reg (by simp [s0x, i8]; rfl) hseenBase_w)
        (ev_reg (by simp [s0x]) hx_w) ha_seen_w) rfl hseen_x_w
    let s1 : State := ⟨s.mem, Function.update s0x.regs 15 (s.mem (seenBase + x)), s.pos⟩
    have hi12_1 : s1.regs 12 = e := by simp [s1, s0x, i12]
    have hi15_1 : s1.regs 15 = s.mem (seenBase + x) := by simp [s1]
    apply runs_start_le
    refine runs_seq_assign_le hev_x ?_
    refine runs_seq_assign_le hev_sn ?_
    by_cases hseen_now : s.mem (seenBase + x) = e + 1
    · have hprev_ex : ∃ s0 < t, (embJH e).verts.getD s0 0 = x := (hseen_iff x hx_Hn).mp hseen_now
      have hvc_eq : ∀ y, vcPrefix embJH e (t + 1) y = vcPrefix embJH e t y := by
        intro y; rw [vcPrefix_succ]
        by_cases hyx : y = x
        · subst hyx; simp only [hprev_ex, ↓reduceIte]
        · have hneq : (embJH e).verts.getD t 0 ≠ y := fun h => hyx (by simpa [x] using h.symm)
          simp only [List.getD] at hneq ⊢
          simp [hneq]
      have hcond : (Expr.bin .eq (.bin .eq (.reg 15) (.bin .add (.reg 12) (.const 1))) (.const 0)).eval w s1 = some 0 :=
        ev_eq_f (ev_eq_t (ev_reg hi15_1 hseen_x_w)
          (ev_add (ev_reg hi12_1 he_w) (ev_const hw1) he1_w) hseen_now hw1)
          (ev_const hw0) (by decide) hw1
      let s_out : State := ⟨s.mem, Function.update s1.regs 15 0, s.pos⟩
      refine ⟨.normal, s_out, _,
        runs_cond_iff.mpr ⟨0, _, hcond,
          runs_assign_iff.mpr ⟨0, ev_const hw0, rfl, rfl, rfl⟩, rfl⟩,
        ?_, by norm_num [Expr.size]⟩
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega,
        ?_, ?_, hseen_le, hag_tot, hag_vc, hz_in⟩, ?_⟩
      all_goals dsimp only [s_out, s1, s0x]
      · simp [i0]
      · simp [i1]
      · simp [i2]
      · simp [i3]
      · simp [i4]
      · simp [i5]
      · simp [i6]
      · simp [i7]
      · simp [i8]
      · simp [i9]
      · simp [i10]
      · simp [i11]; congr 1; ext y; exact (hvc_eq y).symm
      · simp [i12]
      · simp [i13]
      · simp [i14]
      · simp [Function.update_self]
      · intro y hy; rw [hvc_eq y]; exact hvc_t y hy
      · intro y hy
        rw [hseen_iff y hy]
        constructor
        · rintro ⟨s0, hs0, hsq⟩; exact ⟨s0, Nat.lt_succ_of_lt hs0, hsq⟩
        · rintro ⟨s0, hs0, hsq⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hs0 with hst | rfl
          · exact ⟨s0, hst, hsq⟩
          · have hyx : y = x := by simpa [x] using hsq.symm
            subst hyx; exact hprev_ex
      · simp [i16]
    · have hnot_ex : ¬ ∃ s0 < t, (embJH e).verts.getD s0 0 = x := by
        intro h; exact hseen_now ((hseen_iff x hx_Hn).mpr h)
      have hvc_eq : ∀ y, vcPrefix embJH e (t + 1) y =
          if y = x then vcPrefix embJH e t y + 1 else vcPrefix embJH e t y := by
        intro y; rw [vcPrefix_succ]
        by_cases hyx : y = x
        · subst hyx
          have hnow : (embJH e).verts.getD t 0 = x := rfl
          simp only [hnot_ex, hnow, ↓reduceIte]
        · have hneq : (embJH e).verts.getD t 0 ≠ y := fun h => hyx (by simpa [x] using h.symm)
          simp only [List.getD] at hneq ⊢
          simp [hyx, hneq]
      have hcond : (Expr.bin .eq (.bin .eq (.reg 15) (.bin .add (.reg 12) (.const 1))) (.const 0)).eval w s1 = some 1 :=
        ev_eq_t (ev_eq_f (ev_reg hi15_1 hseen_x_w)
          (ev_add (ev_reg hi12_1 he_w) (ev_const hw1) he1_w) hseen_now hw1)
          (ev_const hw0) rfl hw1
      have hvc_x_le : vcPrefix embJH e t x ≤ e + 1 := vcPrefix_le embJH e t x
      have hvc_x1_w : vcPrefix embJH e t x + 1 < 2 ^ w := by omega
      let m1 := Function.update s.mem (seenBase + x) (e + 1)
      let s1m : State := ⟨m1, s1.regs, s.pos⟩
      have ha_seen_s1 : (Expr.bin .add (.reg 8) (.reg 17)).eval w s1 = some (seenBase + x) :=
        ev_add (ev_reg (by simp [s1, s0x, i8]; rfl) hseenBase_w) (ev_reg (by simp [s1, s0x]) hx_w) ha_seen_w
      have he1_s1 : (Expr.bin .add (.reg 12) (.const 1)).eval w s1 = some (e + 1) :=
        ev_add (ev_reg hi12_1 he_w) (ev_const hw1) he1_w
      have hm1_vc : m1 (vcBase + x) = vcPrefix embJH e t x := by
        simp only [m1]
        rw [Function.update_of_ne (by dsimp only [vcBase, seenBase]; omega)]
        exact hvc_t x hx_Hn
      have hev_vc1 : (Expr.bin .add (.load (.bin .add (.reg 7) (.reg 17))) (.const 1)).eval w s1m =
          some (vcPrefix embJH e t x + 1) :=
        ev_add (ev_load (ev_add (ev_reg (by simp [s1m, s1, s0x, i7]; rfl) hvcBase_w)
          (ev_reg (by simp [s1m, s1, s0x]) hx_w) ha_vc_w) hm1_vc (by omega))
          (ev_const hw1) hvc_x1_w
      let s2 : State := ⟨m1, Function.update s1.regs 15 (vcPrefix embJH e t x + 1), s.pos⟩
      let m2 := Function.update m1 (vcBase + x) (vcPrefix embJH e t x + 1)
      let s2m : State := ⟨m2, s2.regs, s.pos⟩
      have ha_vc_s2 : (Expr.bin .add (.reg 7) (.reg 17)).eval w s2 = some (vcBase + x) :=
        ev_add (ev_reg (by simp [s2, s1, s0x, i7]; rfl) hvcBase_w) (ev_reg (by simp [s2, s1, s0x]) hx_w) ha_vc_w
      have hr11_s2m : s2m.regs 11 = s.regs 11 := by simp [s2m, s2, s1, s0x, i11]
      have hr15_s2m : s2m.regs 15 = vcPrefix embJH e t x + 1 := by simp [s2m, s2]
      have hr11_w : s.regs 11 < 2 ^ w := by
        have hle : s.regs 11 ≤ e + 1 := by
          rw [i11, Finset.fold_max_le]; exact ⟨Nat.zero_le _, fun y _ => vcPrefix_le embJH e t y⟩
        omega
      have hmax_next :
          (Finset.range H'.n).fold max 0 (vcPrefix embJH e (t + 1)) =
            max (s.regs 11) (vcPrefix embJH e t x + 1) := by
        rw [i11]
        calc (Finset.range H'.n).fold max 0 (vcPrefix embJH e (t + 1))
            = (Finset.range H'.n).fold max 0 (fun y => if y = x then vcPrefix embJH e t y + 1 else vcPrefix embJH e t y) := by
                congr 1; ext y; exact hvc_eq y
          _ = max ((Finset.range H'.n).fold max 0 (vcPrefix embJH e t)) (vcPrefix embJH e t x + 1) :=
                fold_max_update_add_one H'.n (vcPrefix embJH e t) x hx_Hn
      have hag_m1 : AgreeOutside m1 s.mem vcBase totalEnd :=
        agreeOutside_update (by dsimp only [vcBase, seenBase]; omega) (by dsimp only [seenBase, totalEnd]; omega)
      have hag_m2 : AgreeOutside m2 m1 vcBase totalEnd :=
        agreeOutside_update (by dsimp only [vcBase]; omega) (by dsimp only [vcBase, totalEnd]; omega)
      have hag_step_vc : AgreeOutside m2 s.mem vcBase totalEnd :=
        agreeOutside_trans hag_m2 hag_m1 le_rfl le_rfl
      have hag_tot2 : AgreeOutside m2 mem degBase totalEnd :=
        agreeOutside_trans hag_step_vc hag_tot (by dsimp only [degBase, vcBase]; omega) le_rfl
      have hag_vc2 : AgreeOutside m2 st_base.mem vcBase totalEnd :=
        agreeOutside_trans hag_step_vc hag_vc le_rfl le_rfl
      have hz2 : ZeroFrom m2 totalEnd := zeroFrom_of_agreeOutside hz_in hag_step_vc le_rfl
      have hm2_vc : ∀ y < H'.n, m2 (vcBase + y) = vcPrefix embJH e (t + 1) y := by
        intro y hy; rw [hvc_eq y]
        by_cases hyx : y = x
        · subst hyx; simp [m2, Function.update_self]
        · simp only [m2, hyx, ↓reduceIte]
          rw [Function.update_of_ne (by omega : vcBase + y ≠ vcBase + x)]
          simp only [m1]
          rw [Function.update_of_ne (by dsimp only [vcBase, seenBase]; omega)]
          exact hvc_t y hy
      have hm2_seen_iff : ∀ y < H'.n,
          (m2 (seenBase + y) = e + 1 ↔ ∃ s0 < t + 1, (embJH e).verts.getD s0 0 = y) := by
        intro y hy
        by_cases hyx : y = x
        · subst hyx
          have hm2_self : m2 (seenBase + x) = e + 1 := by
            simp only [m2, m1]
            rw [Function.update_of_ne (by dsimp only [seenBase, vcBase]; omega), Function.update_self]
          rw [hm2_self]
          exact ⟨fun _ => ⟨t, Nat.lt_succ_self t, rfl⟩, fun _ => rfl⟩
        · have hm2_other : m2 (seenBase + y) = s.mem (seenBase + y) := by
            simp only [m2, m1]
            rw [Function.update_of_ne (by dsimp only [seenBase, vcBase]; omega),
                Function.update_of_ne (by omega : seenBase + y ≠ seenBase + x)]
          rw [hm2_other, hseen_iff y hy]
          constructor
          · rintro ⟨s0, hs0, hsq⟩; exact ⟨s0, Nat.lt_succ_of_lt hs0, hsq⟩
          · rintro ⟨s0, hs0, hsq⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hs0 with hst | rfl
            · exact ⟨s0, hst, hsq⟩
            · exact False.elim (hyx (by simpa [x] using hsq.symm))
      have hm2_seen_le : ∀ y < H'.n, m2 (seenBase + y) ≤ e + 1 := by
        intro y hy
        by_cases hyx : y = x
        · subst hyx; simp only [m2, m1]
          rw [Function.update_of_ne (by dsimp only [seenBase, vcBase]; omega), Function.update_self]
        · simp only [m2, m1]
          rw [Function.update_of_ne (by dsimp only [seenBase, vcBase]; omega),
              Function.update_of_ne (by omega : seenBase + y ≠ seenBase + x)]
          exact hseen_le y hy
      by_cases hlt11 : s.regs 11 < vcPrefix embJH e t x + 1
      · have hev11 : (Expr.bin .lt (.reg 11) (.reg 15)).eval w s2m = some 1 :=
          ev_lt_t (ev_reg hr11_s2m hr11_w) (ev_reg hr15_s2m hvc_x1_w) hlt11 hw1
        refine runs_cond_le hcond (fun _ => ?_) (fun h1 => absurd h1 (by decide))
        refine runs_seq_store_le ha_seen_s1 he1_s1 ?_
        refine runs_seq_assign_le hev_vc1 ?_
        refine runs_seq_store_le ha_vc_s2 (ev_reg hr15_s2m hvc_x1_w) ?_
        refine runs_cond_le hev11 (fun _ => ?_) (fun h1 => absurd h1 (by decide))
        refine runs_assign_le (ev_reg hr15_s2m hvc_x1_w) ?_ (by norm_num [Expr.size])
        · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega,
            hm2_vc, hm2_seen_iff, hm2_seen_le, hag_tot2, hag_vc2, hz2⟩, ?_⟩
          all_goals try dsimp only [s2, s1, s0x]
          · simp [i0]
          · simp [i1]
          · simp [i2]
          · simp [i3]
          · simp [i4]
          · simp [i5]
          · simp [i6]
          · simp [i7]
          · simp [i8]
          · simp [i9]
          · simp [i10]
          · rw [hmax_next, max_eq_right (le_of_lt hlt11)]; simp [Function.update_self]
          · simp [i12]
          · simp [i13]
          · simp [i14]
          · simp [Function.update_self]
          · simp [i16]
      · have hev11 : (Expr.bin .lt (.reg 11) (.reg 15)).eval w s2m = some 0 :=
          ev_lt_f (ev_reg hr11_s2m hr11_w) (ev_reg hr15_s2m hvc_x1_w) (by omega) hw1
        refine runs_cond_le hcond (fun _ => ?_) (fun h1 => absurd h1 (by decide))
        refine runs_seq_store_le ha_seen_s1 he1_s1 ?_
        refine runs_seq_assign_le hev_vc1 ?_
        refine runs_seq_store_le ha_vc_s2 (ev_reg hr15_s2m hvc_x1_w) ?_
        refine runs_cond_le hev11 (fun h0 => absurd rfl h0) fun _ => ?_
        refine runs_assign_le (ev_const hw0) ?_ (by norm_num [Expr.size])
        · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega,
            hm2_vc, hm2_seen_iff, hm2_seen_le, hag_tot2, hag_vc2, hz2⟩, ?_⟩
          all_goals try dsimp only [s2, s1, s0x]
          · simp [i0]
          · simp [i1]
          · simp [i2]
          · simp [i3]
          · simp [i4]
          · simp [i5]
          · simp [i6]
          · simp [i7]
          · simp [i8]
          · simp [i9]
          · simp [i10]
          · rw [hmax_next, max_eq_left (by omega)]
            simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 16),
              Function.update_of_ne (by decide : (11 : ℕ) ≠ 15),
              Function.update_of_ne (by decide : (11 : ℕ) ≠ 17)]
          · simp [i12]
          · simp [i13]
          · simp [i14]
          · simp [Function.update_self]
          · simp [i16]

private theorem embJHStats_loop2_triple {w : ℕ} {p : Program}
    (jAddr embJHAddr h : ℕ) (J H' : Graph) (embJH : ℕ → Walk) (bound : ℕ) (mem : ℕ → ℕ)
    (hJvalid : J.IsValid) (hEmb : EmbAt mem embJHAddr J.m embJH)
    (hBound : EmbBounded mem embJHAddr J.m embJH bound)
    (hVerts_H : ∀ e < J.m, ∀ x ∈ (embJH e).verts, x < H'.n) (hw1 : 1 < 2 ^ w)
    (heAddr_w : embJHAddr < 2 ^ w) (hbh : bound ≤ h) (hbw : bound < 2 ^ w)
    (hm2w : 2 * J.m + 2 < 2 ^ w) (hh_w : h + 3 + J.n + 2 * H'.n < 2 ^ w) :
    Triple w p (embStatsInv1 jAddr embJHAddr h J H' mem J.m)
      (forRange 12 (.const 0) (.reg 5) (
        .assign 13 (.load (.bin .add (.reg 1) (.reg 12))) ;;
        .assign 14 (.load (.reg 13)) ;;
        .assign 15 (.load (.bin .add (.reg 13) (.bin .add (.const 1) (.reg 14)))) ;;
        .cond (.bin .lt (.reg 10) (.reg 15)) (.assign 10 (.reg 15)) (.assign 17 (.const 0)) ;;
        forRange 16 (.const 0) (.reg 14) (
          .assign 17 (.load (.bin .add (.reg 13) (.bin .add (.const 1) (.reg 16)))) ;;
          .assign 15 (.load (.bin .add (.reg 8) (.reg 17))) ;;
          .cond (.bin .eq (.bin .eq (.reg 15) (.bin .add (.reg 12) (.const 1))) (.const 0)) (
            .store (.bin .add (.reg 8) (.reg 17)) (.bin .add (.reg 12) (.const 1)) ;;
            .assign 15 (.bin .add (.load (.bin .add (.reg 7) (.reg 17))) (.const 1)) ;;
            .store (.bin .add (.reg 7) (.reg 17)) (.reg 15) ;;
            .cond (.bin .lt (.reg 11) (.reg 15)) (.assign 11 (.reg 15)) (.assign 15 (.const 0))
          ) (.assign 15 (.const 0))
        )
      ))
      (normalPost (embStatsInv2 jAddr embJHAddr h J H' embJH mem J.m))
      (fun _ => rangeCost (fun e => 110 * (embJH e).verts.length + 60) 0 J.m +
        (J.m - 0) * ((Expr.reg 5).size + 8) + ((Expr.const 0).size + (Expr.reg 5).size + 5)) := by
  have hw0 : 0 < 2 ^ w := Nat.zero_lt_of_lt hw1
  have hmJ_w : J.m < 2 ^ w := by omega
  refine Triple.forRange_le (p := p) (w := w) (r := 12) (lo := .const 0) (hi := .reg 5)
    (Inv := embStatsInv2 jAddr embJHAddr h J H' embJH mem)
    (fun e => 110 * (embJH e).verts.length + 60) 0 J.m (Nat.zero_le _) hw1 (fun _ => hmJ_w)
    (fun st hP => by
      rcases hP with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, _, _, hag1, hzvc⟩
      refine ⟨Expr.eval_const hw0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, ?_, ?_, ?_,
        by simp [Function.update_self], Nat.zero_le _, ?_, ?_, ?_, ?_⟩⟩
      · simp only [Function.update_of_ne (by decide : (9 : ℕ) ≠ 12)]
        rw [r9, maxDeg_eq_fold hJvalid]
      · simp only [Function.update_of_ne (by decide : (10 : ℕ) ≠ 12)]
        rw [r10]; unfold lenPrefix; simp
      · simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 12)]
        rw [r11]; simp [vcPrefix, Finset.fold_const]
      · intro x _; simp [vcPrefix]; exact hzvc _ (by omega)
      · intro x _; simp; exact hzvc _ (by omega)
      · exact agreeOutside_mono hag1 le_rfl (by omega)
      · exact fun x hx => hzvc x (by omega))
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => ev_reg h.2.2.2.2.2.1 hmJ_w) ?_
  intro e _ he st ω hInv
  rcases hInv with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, hem,
    hvc, hseen, hag, hztot⟩
  set ptr := mem (embJHAddr + e)
  set vlen := (embJH e).verts.length
  set elen := (embJH e).edges.length
  have he_w : e < 2 ^ w := by omega
  have hptr_eq : st.mem (embJHAddr + e) = ptr :=
    hag (embJHAddr + e) (Or.inl (by have := hBound.1; omega))
  have hwalk_mem : WalkAt mem ptr (embJH e) := hEmb e he
  have hptr_bound : ptr + (2 + vlen + elen) ≤ bound := by
    have hlen_w : (embJH e).encode.length = 2 + vlen + elen := walk_encode_length _
    have hb := hBound.2 e he
    change mem (embJHAddr + e) + (embJH e).encode.length ≤ bound at hb
    rwa [hlen_w] at hb
  have hwalk_st : WalkAt st.mem ptr (embJH e) := walkAt_of_agreeOutside hwalk_mem hag (Or.inl (by omega))
  have hptr_w : ptr < 2 ^ w := by omega
  have hvlen_w : vlen < 2 ^ w := by omega
  have helen_w : elen < 2 ^ w := by omega
  have h1v_w : 1 + vlen < 2 ^ w := by omega
  have hptr_vlen_w : ptr + (1 + vlen) < 2 ^ w := by omega
  have hmem_vlen : st.mem ptr = vlen := by simpa [vlen] using hwalk_st.verts_len
  have hmem_elen : st.mem (ptr + (1 + vlen)) = elen := by
    simpa [vlen, elen, Nat.add_assoc] using hwalk_st.edges_len
  have ha_ptr_w : embJHAddr + e < 2 ^ w := by have := hBound.1; omega
  have hev_ptr : (Expr.load (.bin .add (.reg 1) (.reg 12))).eval w st = some ptr :=
    ev_load (ev_add (ev_reg r1 heAddr_w) (ev_reg r12 he_w) ha_ptr_w) hptr_eq hptr_w
  let st_p : State := ⟨st.mem, Function.update st.regs 13 ptr, st.pos⟩
  have hev_vlen : (Expr.load (.reg 13)).eval w st_p = some vlen :=
    ev_load (ev_reg (by simp [st_p]) hptr_w) hmem_vlen hvlen_w
  let st_pv : State := ⟨st.mem, Function.update st_p.regs 14 vlen, st.pos⟩
  have hev_elen : (Expr.load (.bin .add (.reg 13) (.bin .add (.const 1) (.reg 14)))).eval w st_pv = some elen :=
    ev_load (ev_add (ev_reg (by simp [st_pv, st_p]) hptr_w)
      (ev_add (ev_const hw1) (ev_reg (by simp [st_pv]) hvlen_w) h1v_w) hptr_vlen_w) hmem_elen helen_w
  let stA0 : State := ⟨st.mem, Function.update st_pv.regs 15 elen, st.pos⟩
  have hr10_A0 : stA0.regs 10 = st.regs 10 := by simp [stA0, st_pv, st_p]
  have hr15_A0 : stA0.regs 15 = elen := by simp [stA0]
  have hr10_w : st.regs 10 < 2 ^ w := by
    have hle : st.regs 10 ≤ bound := by
      rw [r10]; unfold lenPrefix; rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun j hj => ?_⟩
      have hb := hBound.2 j (lt_trans (Finset.mem_range.mp hj) he)
      have hlen_j : (embJH j).encode.length = 2 + (embJH j).verts.length + (embJH j).edges.length :=
        walk_encode_length _
      omega
    omega
  apply runs_start_le
  refine runs_seq_assign_le hev_ptr ?_
  refine runs_seq_assign_le hev_vlen ?_
  refine runs_seq_assign_le hev_elen ?_
  have hcond_len_res :
      ∃ stB cB,
        Runs w p ω
          (.cond (.bin .lt (.reg 10) (.reg 15)) (.assign 10 (.reg 15)) (.assign 17 (.const 0)))
          stA0 .normal stB cB ∧
        cB ≤ 12 ∧ stB.pos = st.pos ∧ stB.mem = st.mem ∧
        stB.regs 0 = jAddr ∧ stB.regs 1 = embJHAddr ∧ stB.regs 2 = H'.n ∧ stB.regs 3 = h ∧
        stB.regs 4 = J.n ∧ stB.regs 5 = J.m ∧
        stB.regs 6 = h + 3 ∧ stB.regs 7 = h + 3 + J.n ∧ stB.regs 8 = h + 3 + J.n + H'.n ∧
        stB.regs 9 = maxDeg J ∧ stB.regs 10 = lenPrefix embJH (e + 1) ∧
        stB.regs 11 = st.regs 11 ∧ stB.regs 12 = e ∧
        stB.regs 13 = ptr ∧ stB.regs 14 = vlen := by
    by_cases hlt : st.regs 10 < elen
    · have hev : (Expr.bin .lt (.reg 10) (.reg 15)).eval w stA0 = some 1 :=
        ev_lt_t (ev_reg hr10_A0 hr10_w) (ev_reg hr15_A0 helen_w) hlt hw1
      refine ⟨⟨st.mem, Function.update stA0.regs 10 elen, st.pos⟩, _,
        runs_cond_iff.mpr ⟨1, _, hev,
          runs_assign_iff.mpr ⟨elen, ev_reg hr15_A0 helen_w, rfl, rfl, rfl⟩, rfl⟩,
        by norm_num [Expr.size], rfl, rfl,
        by simp [stA0, st_pv, st_p, r0], by simp [stA0, st_pv, st_p, r1],
        by simp [stA0, st_pv, st_p, r2], by simp [stA0, st_pv, st_p, r3],
        by simp [stA0, st_pv, st_p, r4], by simp [stA0, st_pv, st_p, r5],
        by simp [stA0, st_pv, st_p, r6], by simp [stA0, st_pv, st_p, r7],
        by simp [stA0, st_pv, st_p, r8], by simp [stA0, st_pv, st_p, r9], ?_,
        by simp [stA0, st_pv, st_p, r11], by simp [stA0, st_pv, st_p, r12],
        by simp [stA0, st_pv, st_p], by simp [stA0, st_pv]⟩
      rw [lenPrefix_succ, ← r10, max_eq_right (le_of_lt hlt)]; simp [Function.update_self]
    · have hev : (Expr.bin .lt (.reg 10) (.reg 15)).eval w stA0 = some 0 :=
        ev_lt_f (ev_reg hr10_A0 hr10_w) (ev_reg hr15_A0 helen_w) (by omega) hw1
      refine ⟨⟨st.mem, Function.update stA0.regs 17 0, st.pos⟩, _,
        runs_cond_iff.mpr ⟨0, _, hev,
          runs_assign_iff.mpr ⟨0, ev_const hw0, rfl, rfl, rfl⟩, rfl⟩,
        by norm_num [Expr.size], rfl, rfl,
        by simp [stA0, st_pv, st_p, r0], by simp [stA0, st_pv, st_p, r1],
        by simp [stA0, st_pv, st_p, r2], by simp [stA0, st_pv, st_p, r3],
        by simp [stA0, st_pv, st_p, r4], by simp [stA0, st_pv, st_p, r5],
        by simp [stA0, st_pv, st_p, r6], by simp [stA0, st_pv, st_p, r7],
        by simp [stA0, st_pv, st_p, r8], by simp [stA0, st_pv, st_p, r9], ?_,
        by simp [stA0, st_pv, st_p, r11], by simp [stA0, st_pv, st_p, r12],
        by simp [stA0, st_pv, st_p], by simp [stA0, st_pv]⟩
      rw [lenPrefix_succ, ← r10, max_eq_left (by omega)]
      simp only [Function.update_of_ne (by decide : (10 : ℕ) ≠ 17)]
      exact hr10_A0
  rcases hcond_len_res with ⟨stB, cB, hrunB, hcB, hpB, hmB, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩
  have hinner := embJHStats_inner_triple (p := p) jAddr embJHAddr h e ptr J H' embJH bound mem stB st
    he hEmb hBound hVerts_H hw1 hbh hbw hm2w hh_w rfl hptr_bound hmB
    ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11.trans r11, b12, b13, b14⟩ hvc hseen hag hztot
  rcases hinner stB ω rfl with ⟨o_in, stC, c_in, hrun_in, hq_in, hc_in⟩
  cases o_in with
  | returned u => exact False.elim hq_in
  | normal =>
    rcases hq_in with ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, _, _, _, _,
      hvcC, _, hseenC_le, hagC_tot, _, hzC⟩
    refine ⟨.normal, stC, cB + c_in + 1,
      runs_seq_iff.mpr (Or.inr ⟨stB, cB, c_in, hrunB, hrun_in, rfl⟩),
      ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega,
        ?_, hseenC_le, hagC_tot, hzC⟩, c12⟩, ?_⟩
    all_goals dsimp only
    · simp [c0]
    · simp [c1]
    · simp [c2]
    · simp [c3]
    · simp [c4]
    · simp [c5]
    · simp [c6]
    · simp [c7]
    · simp [c8]
    · simp [c9]
    · simp [c10]
    · simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 12)]
      rw [c11]; congr 1; ext x; exact vcPrefix_end embJH e x
    · simp [Function.update_self]
    · intro x hx; rw [← vcPrefix_end embJH e x]; exact hvcC x hx
    · simp only [Expr.size] at hc_in ⊢
      omega

/-- `embJHStatsModule` meets `embJHStatsContract w` in `O(J.m * (length J embJH + 1) + 1)` time. -/
theorem embJHStats_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b embJHStatsModule) :
    MeetsContract w p b (embJHStatsContract w) := by
  refine meetsContract_of_triple hp.head ?_
  intro args mem pos hwords hpre
  dsimp only [embJHStatsContract] at hpre
  rcases hpre with ⟨jAddr, embJHAddr, hnH, h, J, H', embJH, bound,
    rfl, rfl, hG, hJvalid, hEmb, hBound, hVerts_H, hw1, hjh, hbh, hbw, hm2w, hh_w, hz⟩
  have hw0 : 0 < 2 ^ w := Nat.zero_lt_of_lt hw1
  have hmJ_w : J.m < 2 ^ w := by omega
  have hJn_w : J.n < 2 ^ w := by omega
  have hHn_w : H'.n < 2 ^ w := by omega
  have hjAddr_w : jAddr < 2 ^ w := hwords jAddr (by simp)
  have heAddr_w : embJHAddr < 2 ^ w := hwords embJHAddr (by simp)
  have hh_w' : h < 2 ^ w := by omega
  let degBase := h + 3
  let vcBase := degBase + J.n
  let seenBase := vcBase + H'.n
  let totalEnd := h + 3 + J.n + 2 * H'.n
  have hdegBase_w : degBase < 2 ^ w := by omega
  have hvcBase_w : vcBase < 2 ^ w := by omega
  have hseenBase_w : seenBase < 2 ^ w := by omega
  have hload_n : mem jAddr = J.n := graphAt_n hG
  have hload_m : mem (jAddr + 1) = J.m := graphAt_m hG
  have hsetup : Triple w p (fun st => st = startState [jAddr, embJHAddr, H'.n, h] mem pos)
      embJHSetupStmt
      (normalPost fun st =>
        st.regs 0 = jAddr ∧ st.regs 1 = embJHAddr ∧ st.regs 2 = H'.n ∧ st.regs 3 = h ∧
        st.regs 4 = J.n ∧ st.regs 5 = J.m ∧
        st.regs 6 = h + 3 ∧ st.regs 7 = h + 3 + J.n ∧ st.regs 8 = h + 3 + J.n + H'.n ∧
        st.regs 9 = 0 ∧ st.regs 10 = 0 ∧ st.regs 11 = 0 ∧ st.mem = mem)
      (fun _ => 50) := by
    intro st ω hst; subst hst
    let s0 := startState [jAddr, embJHAddr, H'.n, h] mem pos
    have e4 : (Expr.load (.reg 0)).eval w s0 = some J.n :=
      ev_load (ev_reg (by simp [s0, startState]) hjAddr_w) hload_n hJn_w
    let s4 : State := ⟨mem, Function.update s0.regs 4 J.n, pos⟩
    have e5 : (Expr.load (.bin .add (.reg 0) (.const 1))).eval w s4 = some J.m :=
      ev_load (ev_add (ev_reg (by simp [s4, s0, startState]) hjAddr_w) (ev_const hw1) (by omega)) hload_m hmJ_w
    let s5 : State := ⟨mem, Function.update s4.regs 5 J.m, pos⟩
    have e6 : (Expr.bin .add (.reg 3) (.const 3)).eval w s5 = some degBase :=
      ev_add (ev_reg (by simp [s5, s4, s0, startState]) hh_w') (ev_const (by omega)) hdegBase_w
    let s6 : State := ⟨mem, Function.update s5.regs 6 degBase, pos⟩
    have e7 : (Expr.bin .add (.reg 6) (.reg 4)).eval w s6 = some vcBase :=
      ev_add (ev_reg (by simp [s6]) hdegBase_w) (ev_reg (by simp [s6, s5, s4]) hJn_w) hvcBase_w
    let s7 : State := ⟨mem, Function.update s6.regs 7 vcBase, pos⟩
    have e8 : (Expr.bin .add (.reg 7) (.reg 2)).eval w s7 = some seenBase :=
      ev_add (ev_reg (by simp [s7]) hvcBase_w) (ev_reg (by simp [s7, s6, s5, s4, s0, startState]) hHn_w) hseenBase_w
    let s8 : State := ⟨mem, Function.update s7.regs 8 seenBase, pos⟩
    let s9 : State := ⟨mem, Function.update s8.regs 9 0, pos⟩
    let s10 : State := ⟨mem, Function.update s9.regs 10 0, pos⟩
    apply runs_start_le
    refine runs_seq_assign_le e4 ?_
    refine runs_seq_assign_le e5 ?_
    refine runs_seq_assign_le e6 ?_
    refine runs_seq_assign_le e7 ?_
    refine runs_seq_assign_le e8 ?_
    refine runs_seq_assign_le (ev_const hw0) ?_
    refine runs_seq_assign_le (ev_const hw0) ?_
    refine ⟨.normal, ⟨mem, Function.update s10.regs 11 0, pos⟩, _,
      runs_assign_iff.mpr ⟨0, ev_const hw0, rfl, rfl, rfl⟩, ?_, by norm_num [Expr.size]⟩
    simp [s10, s9, s8, s7, s6, s5, s4, s0, startState, degBase, vcBase, seenBase, Nat.add_assoc]
  have hfor1 := embJHStats_loop1_triple (p := p) jAddr embJHAddr h J H' mem hG hJvalid hw1
    hjAddr_w hjh hHn_w hm2w hh_w hz
  have hfor2 := embJHStats_loop2_triple (p := p) jAddr embJHAddr h J H' embJH bound mem hJvalid
    hEmb hBound hVerts_H hw1 heAddr_w hbh hbw hm2w hh_w
  have hmaxDeg_w : maxDeg J < 2 ^ w := by
    rw [maxDeg_eq_fold hJvalid]
    have hle : (Finset.range J.n).fold max 0 (degPrefix J J.m) ≤ 2 * J.m := by
      rw [Finset.fold_max_le]; exact ⟨Nat.zero_le _, fun x _ => degPrefix_le J J.m x⟩
    omega
  have hlen_w : lenPrefix embJH J.m < 2 ^ w := by
    have hle : lenPrefix embJH J.m ≤ bound := by
      unfold lenPrefix; rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun e he => ?_⟩
      have hb := hBound.2 e (Finset.mem_range.mp he)
      have hlen_e : (embJH e).encode.length = 2 + (embJH e).verts.length + (embJH e).edges.length :=
        walk_encode_length _
      omega
    omega
  have hvcong_w : ((Finset.range H'.n).fold max 0 fun x => vcPrefix embJH J.m 0 x) < 2 ^ w := by
    have hle : ((Finset.range H'.n).fold max 0 fun x => vcPrefix embJH J.m 0 x) ≤ J.m + 1 := by
      rw [Finset.fold_max_le]; exact ⟨Nat.zero_le _, fun x _ => vcPrefix_le embJH J.m 0 x⟩
    omega
  have hs_a1 : Triple w p (embStatsInv2 jAddr embJHAddr h J H' embJH mem J.m)
      (.store (.reg 3) (.reg 9))
      (normalPost fun st =>
        st.regs 2 = H'.n ∧ st.regs 3 = h ∧ st.regs 8 = seenBase ∧
        st.regs 10 = lenPrefix embJH J.m ∧
        st.regs 11 = ((Finset.range H'.n).fold max 0 fun x => vcPrefix embJH J.m 0 x) ∧
        st.mem h = maxDeg J ∧ AgreeOutside st.mem mem h totalEnd ∧ ZeroFrom st.mem totalEnd)
      (fun _ => (Expr.reg 3).size + (Expr.reg 9).size + 1) := by
    refine Triple.store (addr := fun _ => h) (val := fun _ => maxDeg J) ?_ ?_ ?_
    · intro st hInv; exact ev_reg hInv.2.2.2.1 hh_w'
    · intro st hInv; exact ev_reg hInv.2.2.2.2.2.2.2.2.2.1 hmaxDeg_w
    · intro st hInv
      rcases hInv with ⟨_, _, r2, r3, _, _, _, _, r8, _, r10, r11, _, _, _, _, hag2, hz2⟩
      exact ⟨r2, r3, by simpa [seenBase, vcBase, degBase, Nat.add_assoc] using r8, r10, r11,
        by simp [Function.update_self],
        agreeOutside_trans (agreeOutside_update (lo := h) (hi := totalEnd) le_rfl (by omega))
          (agreeOutside_mono hag2 (by omega) le_rfl) le_rfl le_rfl,
        zeroFrom_of_agreeOutside hz2 (agreeOutside_update (lo := h) (hi := totalEnd) le_rfl (by omega)) (by omega)⟩
  have hs_a2 : Triple w p
      (fun st =>
        st.regs 2 = H'.n ∧ st.regs 3 = h ∧ st.regs 8 = seenBase ∧
        st.regs 10 = lenPrefix embJH J.m ∧
        st.regs 11 = ((Finset.range H'.n).fold max 0 fun x => vcPrefix embJH J.m 0 x) ∧
        st.mem h = maxDeg J ∧ AgreeOutside st.mem mem h totalEnd ∧ ZeroFrom st.mem totalEnd)
      (.store (.bin .add (.reg 3) (.const 1)) (.reg 10))
      (normalPost fun st =>
        st.regs 2 = H'.n ∧ st.regs 3 = h ∧ st.regs 8 = seenBase ∧
        st.regs 11 = ((Finset.range H'.n).fold max 0 fun x => vcPrefix embJH J.m 0 x) ∧
        st.mem h = maxDeg J ∧ st.mem (h + 1) = lenPrefix embJH J.m ∧
        AgreeOutside st.mem mem h totalEnd ∧ ZeroFrom st.mem totalEnd)
      (fun _ => (Expr.bin .add (.reg 3) (.const 1)).size + (Expr.reg 10).size + 1) := by
    refine Triple.store (addr := fun _ => h + 1) (val := fun _ => lenPrefix embJH J.m) ?_ ?_ ?_
    · intro st hP; exact ev_add (ev_reg hP.2.1 hh_w') (ev_const hw1) (by omega)
    · intro st hP; exact ev_reg hP.2.2.2.1 hlen_w
    · intro st hP
      rcases hP with ⟨r2, r3, r8, _, r11, hmh, hag, hz_s⟩
      exact ⟨r2, r3, r8, r11,
        by dsimp only; rw [Function.update_of_ne (by omega : h ≠ h + 1)]; exact hmh,
        by simp [Function.update_self],
        agreeOutside_trans (agreeOutside_update (lo := h) (hi := totalEnd) (by omega) (by omega))
          hag le_rfl le_rfl,
        zeroFrom_of_agreeOutside hz_s
          (agreeOutside_update (lo := h) (hi := totalEnd) (by omega) (by omega)) (by omega)⟩
  have hs_a3 : Triple w p
      (fun st =>
        st.regs 2 = H'.n ∧ st.regs 3 = h ∧ st.regs 8 = seenBase ∧
        st.regs 11 = ((Finset.range H'.n).fold max 0 fun x => vcPrefix embJH J.m 0 x) ∧
        st.mem h = maxDeg J ∧ st.mem (h + 1) = lenPrefix embJH J.m ∧
        AgreeOutside st.mem mem h totalEnd ∧ ZeroFrom st.mem totalEnd)
      (.store (.bin .add (.reg 3) (.const 2)) (.reg 11))
      (normalPost fun st =>
        st.regs 2 = H'.n ∧ st.regs 8 = seenBase ∧
        st.mem h = maxDeg J ∧ st.mem (h + 1) = lenPrefix embJH J.m ∧
        st.mem (h + 2) = ((Finset.range H'.n).fold max 0 fun x => vcPrefix embJH J.m 0 x) ∧
        AgreeOutside st.mem mem h totalEnd ∧ ZeroFrom st.mem totalEnd)
      (fun _ => (Expr.bin .add (.reg 3) (.const 2)).size + (Expr.reg 11).size + 1) := by
    refine Triple.store (addr := fun _ => h + 2)
      (val := fun _ => (Finset.range H'.n).fold max 0 fun x => vcPrefix embJH J.m 0 x) ?_ ?_ ?_
    · intro st hP; exact ev_add (ev_reg hP.2.1 hh_w') (ev_const (by omega)) (by omega)
    · intro st hP; exact ev_reg hP.2.2.2.1 hvcong_w
    · intro st hP
      rcases hP with ⟨r2, _, r8, _, hmh, hmh1, hag, hz_s⟩
      exact ⟨r2, r8,
        by dsimp only; rw [Function.update_of_ne (by omega : h ≠ h + 2)]; exact hmh,
        by dsimp only; rw [Function.update_of_ne (by omega : h + 1 ≠ h + 2)]; exact hmh1,
        by simp [Function.update_self],
        agreeOutside_trans (agreeOutside_update (lo := h) (hi := totalEnd) (by omega) (by omega))
          hag le_rfl le_rfl,
        zeroFrom_of_agreeOutside hz_s
          (agreeOutside_update (lo := h) (hi := totalEnd) (by omega) (by omega)) (by omega)⟩
  have hs_ret : Triple w p
      (fun st =>
        st.regs 2 = H'.n ∧ st.regs 8 = seenBase ∧
        st.mem h = maxDeg J ∧ st.mem (h + 1) = lenPrefix embJH J.m ∧
        st.mem (h + 2) = ((Finset.range H'.n).fold max 0 fun x => vcPrefix embJH J.m 0 x) ∧
        AgreeOutside st.mem mem h totalEnd ∧ ZeroFrom st.mem totalEnd)
      (.ret (.bin .add (.reg 8) (.reg 2)))
      (retPost fun v st' =>
        (embJHStatsContract w).post [jAddr, embJHAddr, H'.n, h] mem v st'.mem)
      (fun _ => (Expr.bin .add (.reg 8) (.reg 2)).size + 1) := by
    refine Triple.ret (val := fun _ => totalEnd) ?_ ?_
    · intro st hP
      have hsum : seenBase + H'.n = totalEnd := by omega
      rw [← hsum]
      exact ev_add (ev_reg hP.2.1 hseenBase_w) (ev_reg hP.1 hHn_w) (by omega)
    · intro st hP
      dsimp only [embJHStatsContract]
      intro j' e' hn' h' J' H'' emb' heq hne hG' hEmb'
      simp only [List.cons.injEq, and_true] at heq
      rcases heq with ⟨rfl, rfl, rfl, rfl⟩
      have hJ_eq : J' = J := graphAt_unique hG' hG
      subst hJ_eq
      have hH_eq : H''.n = H'.n := hne.symm
      have hemb_eq : ∀ e < J'.m, emb' e = embJH e := fun e he =>
        walkAt_unique (hEmb' e he) (hEmb e he)
      have hlen_emb_eq : length J' emb' = lenPrefix embJH J'.m := by
        unfold length lenPrefix
        refine le_antisymm ?_ ?_
        · rw [Finset.fold_max_le]; refine ⟨Nat.zero_le _, fun e he => ?_⟩
          rw [Finset.mem_range] at he; rw [hemb_eq e he, Finset.le_fold_max]
          exact Or.inr ⟨e, Finset.mem_range.mpr he, le_rfl⟩
        · rw [Finset.fold_max_le]; refine ⟨Nat.zero_le _, fun e he => ?_⟩
          rw [Finset.mem_range] at he; rw [← hemb_eq e he, Finset.le_fold_max]
          exact Or.inr ⟨e, Finset.mem_range.mpr he, le_rfl⟩
      have hvcong_emb_eq : vcongNat J' H'' emb' =
          (Finset.range H'.n).fold max 0 fun x => vcPrefix embJH J'.m 0 x := by
        simp only [vcongNat, vcPrefix, Nat.not_lt_zero, false_and, exists_false, ↓reduceIte,
          add_zero, hH_eq]
        congr 1; ext x; congr 1
        refine Finset.filter_congr fun eJ heJ => ?_
        rw [hemb_eq eJ (Finset.mem_range.mp heJ)]
      rcases hP with ⟨_, _, hmh, hmh1, hmh2, hag_f, hzf_f⟩
      exact ⟨by dsimp only [totalEnd]; omega, hmh, by rw [hlen_emb_eq]; exact hmh1,
        by rw [hvcong_emb_eq]; exact hmh2, by simpa [totalEnd, hH_eq] using hag_f,
        by simpa [totalEnd, hH_eq] using hzf_f⟩
  have hall := Triple.seq_normal_const hsetup
    (Triple.seq_normal_const hfor1
      (Triple.seq_normal_const hfor2
        (Triple.seq_normal_const hs_a1
          (Triple.seq_normal_const hs_a2
            (Triple.seq_normal_const hs_a3 hs_ret)))))
  refine (hall.strengthen_post fun o st hPost => by
    cases o with
    | normal => simp at hPost
    | returned v => exact hPost).mono_cost ?_
  intro _ _
  have hrc : rangeCost (fun e => 110 * (embJH e).verts.length + 60) 0 J.m =
      110 * embVertSumMem mem jAddr embJHAddr + 60 * J.m := by
    rw [rangeCost_add, rangeCost_const, Nat.sub_zero,
        show rangeCost (fun e => 110 * (embJH e).verts.length) 0 J.m =
          110 * ((List.range J.m).map fun e => (embJH e).verts.length).sum by
          rw [rangeCost_zero_eq_range, list_range_map_sum, ← Finset.mul_sum, list_range_map_sum],
        embVertSumMem_eq hG hEmb, list_range_map_sum, Nat.mul_comm J.m 60]
  simp only [embJHStatsContract, hload_m, hrc, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
  omega


end MinCostFlow.Spanner
