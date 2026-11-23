module

public import MinCostFlow.Spanner.ProgTask1Helpers

/-!
# Verification of Stages 1–4 of `task1Module`

This module proves the Hoare triples for `embJHStats`, `stripLoops`, `impl.decompose`, and
`witnessPrep` as invoked inside `task1Body`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

private lemma statsInv_update_78 {inp : Task1Input} {impl : SpannerToolImpl} {mem₀ : ℕ → ℕ}
    {w r val : ℕ} {st : State} (hr : r = 7 ∨ r = 8) (hs : StatsInv inp impl mem₀ w st) :
    StatsInv inp impl mem₀ w { mem := st.mem, regs := Function.update st.regs r val, pos := st.pos } :=
  ⟨hs.hv,
   by rcases hr with rfl | rfl <;> simp [Function.update, hs.hr0],
   by rcases hr with rfl | rfl <;> simp [Function.update, hs.hr1],
   by rcases hr with rfl | rfl <;> simp [Function.update, hs.hr2],
   by rcases hr with rfl | rfl <;> simp [Function.update, hs.hr3],
   by rcases hr with rfl | rfl <;> simp [Function.update, hs.hr4],
   by rcases hr with rfl | rfl <;> simp [Function.update, hs.hr5],
   by rcases hr with rfl | rfl <;> simp [Function.update, hs.hr6],
   hs.h_below, hs.h_hdr_zero, hs.h_zf, hs.hs0, hs.hs1, hs.hs2⟩

private lemma stripInv_update_10 {inp : Task1Input} {impl : SpannerToolImpl} {mem₀ : ℕ → ℕ}
    {w val : ℕ} {st : State} (hs : StripInv inp impl mem₀ w st) :
    StripInv inp impl mem₀ w { mem := st.mem, regs := Function.update st.regs 10 val, pos := st.pos } :=
  ⟨hs.hv,
   by simp [Function.update, hs.hr0], by simp [Function.update, hs.hr1],
   by simp [Function.update, hs.hr2], by simp [Function.update, hs.hr3],
   by simp [Function.update, hs.hr5], by simp [Function.update, hs.hr6],
   by simp [Function.update, hs.hr8], by simp [Function.update, hs.hr9],
   hs.h_below, hs.h_hdr_zero, hs.h_stats, hs.h_J0, hs.h_nl, hs.h_zf⟩

lemma step1_stats_triple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task1Input} {mem₀ : ℕ → ℕ} {statsBase : ℕ}
    (hstats : p.HasAt statsBase embJHStatsModule) :
    Triple w p
      (fun st => st.mem = mem₀ ∧ inp.Valid impl mem₀ w ∧
        st.regs 0 = inp.hAddr ∧ st.regs 1 = inp.jAddr ∧ st.regs 2 = inp.embJHAddr ∧ st.regs 3 = inp.h)
      (Stmt.seq (Stmt.assign 4 (.load (.reg 0))) <|
       Stmt.seq (Stmt.assign 5 (.bin .add (.reg 3) (.const 6))) <|
       Stmt.call 6 statsBase [.reg 1, .reg 2, .reg 4, .reg 5])
      (normalPost (StatsInv inp impl mem₀ w))
      (fun _ => 215 * inp.J.m + 120 * embVertSumMem mem₀ inp.jAddr inp.embJHAddr + 194) := by
  let P1 : State → Prop := fun st => st.mem = mem₀ ∧ inp.Valid impl mem₀ w ∧
    st.regs 0 = inp.hAddr ∧ st.regs 1 = inp.jAddr ∧ st.regs 2 = inp.embJHAddr ∧
    st.regs 3 = inp.h ∧ st.regs 4 = inp.H'.n
  let P2 : State → Prop := fun st => P1 st ∧ st.regs 5 = inp.h + 6
  have h1 : Triple w p
      (fun st => st.mem = mem₀ ∧ inp.Valid impl mem₀ w ∧
        st.regs 0 = inp.hAddr ∧ st.regs 1 = inp.jAddr ∧ st.regs 2 = inp.embJHAddr ∧ st.regs 3 = inp.h)
      (Stmt.assign 4 (.load (.reg 0))) (normalPost P1)
      (fun _ => (Expr.load (.reg 0)).size + 1) := by
    refine Triple.assign (val := fun _ => inp.H'.n) ?_ ?_
    · intro st ⟨hm, hv, hr0, _⟩
      have hb := task1_word_bounds hv
      have hH : st.mem inp.hAddr = inp.H'.n := by
        rw [hm]; simpa [Graph.encode] using hv.2.1 0 (by simp [Graph.encode])
      exact ev_load (ev_reg hr0 hb.2.1) hH hb.2.2.2.2.2.1
    · intro st ⟨hm, hv, hr0, hr1, hr2, hr3⟩
      refine ⟨hm, hv, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Function.update, hr0, hr1, hr2, hr3]
  have h2 : Triple w p P1
      (Stmt.assign 5 (.bin .add (.reg 3) (.const 6))) (normalPost P2)
      (fun _ => (Expr.bin .add (.reg 3) (.const 6)).size + 1) := by
    refine Triple.assign (val := fun _ => inp.h + 6) ?_ ?_
    · intro st ⟨_, hv, _, _, _, hr3, _⟩
      have hb := task1_word_bounds hv
      exact ev_add (ev_reg hr3 hb.2.2.2.2.1) (ev_const (by omega)) hb.2.2.2.2.2.2.1
    · intro st ⟨hm, hv, hr0, hr1, hr2, hr3, hr4⟩
      refine ⟨⟨hm, hv, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp [Function.update, hr0, hr1, hr2, hr3, hr4]
  have h3 : Triple w p P2
      (Stmt.call 6 statsBase [.reg 1, .reg 2, .reg 4, .reg 5])
      (normalPost (StatsInv inp impl mem₀ w))
      (fun _ => 215 * inp.J.m + 120 * embVertSumMem mem₀ inp.jAddr inp.embJHAddr + 185) := by
    refine (Triple.call (embJHStats_meetsContract hstats) (vs := fun _ =>
        [inp.jAddr, inp.embJHAddr, inp.H'.n, inp.h + 6]) ?_ ?_ ?_ ?_).mono_cost ?_
    · intro st ⟨⟨_, hv, _, hr1, hr2, _, hr4⟩, hr5⟩
      have hb := task1_word_bounds hv
      simp [evalArgs, ev_reg hr1 hb.2.2.1, ev_reg hr2 hb.2.2.2.1,
        ev_reg hr4 hb.2.2.2.2.2.1, ev_reg hr5 hb.2.2.2.2.2.2.1]
    · intro st ⟨⟨_, hv, _⟩, _⟩
      have hb := task1_word_bounds hv
      intro v hv_m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_m
      rcases hv_m with rfl | rfl | rfl | rfl <;> omega
    · intro st ⟨⟨hm, hv, _⟩, _⟩
      have hb := task1_word_bounds hv
      have hj_enc : inp.jAddr + (2 + 2 * inp.J.m) ≤ inp.h + 6 := by
        have hlen := graph_encode_length inp.J
        have := hv.2.2.2.2.2.2.2.2.1
        omega
      have hzf6 : ZeroFrom st.mem (inp.h + 6) := fun a ha => by
        rw [hm]; exact hv.2.2.2.2.2.2.2.2.2.1 a (by omega)
      have hb_h6 : EmbBounded st.mem inp.embJHAddr inp.J.m inp.embJH (inp.h + 6) := by
        rw [hm]
        exact ⟨by have := hv.2.2.2.2.2.2.1.1; omega, fun j hj => by
          have := hv.2.2.2.2.2.2.1.2 j hj; omega⟩
      refine ⟨inp.jAddr, inp.embJHAddr, inp.H'.n, inp.h + 6, inp.J, inp.H', inp.embJH, inp.h + 6,
        rfl, rfl, hm ▸ hv.2.2.2.1, hv.2.2.1, hm ▸ hv.2.2.2.2.2.1, hb_h6, ?_, hb.1,
        hj_enc, le_rfl, hb.2.2.2.2.2.2.1, ?_, hb.2.2.2.2.2.2.2.1, hzf6⟩
      · intro e he x hx
        exact (hv.2.2.2.2.1.2 e he).verts_lt hv.1 x hx
      · have hlen := graph_encode_length inp.J
        have := hv.2.2.2.2.2.2.2.2.1
        omega
    · intro st v mem' pos' ⟨⟨hm, hv, hr0, hr1, hr2, hr3, hr4⟩, hr5⟩ hpost
      have ⟨hv_eq, hm0, hm1, hm2, hagree, _⟩ :=
        hpost inp.jAddr inp.embJHAddr inp.H'.n (inp.h + 6) inp.J inp.H' inp.embJH
          rfl rfl (hm ▸ hv.2.2.2.1) (hm ▸ hv.2.2.2.2.2.1)
      have hj0_eq : v = inp.j0Addr := by dsimp only [Task1Input.j0Addr]; exact hv_eq
      refine ⟨hv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm0, hm1, hm2⟩
      · simp [Function.update, hr0]
      · simp [Function.update, hr1]
      · simp [Function.update, hr2]
      · simp [Function.update, hr3]
      · simp [Function.update, hr4]
      · simp [Function.update, hr5]
      · simp [Function.update, hj0_eq]
      · intro x hx; dsimp only; rw [hagree x (Or.inl (by omega)), hm]
      · intro x hx1 hx2
        dsimp only
        rw [hagree x (Or.inl hx2), hm]
        exact hv.2.2.2.2.2.2.2.2.2.1 x hx1
      · intro x hx
        dsimp only
        have hxj : inp.h + 6 + 3 + inp.J.n + 2 * inp.H'.n ≤ x := by
          unfold Task1Input.j0Addr at hx; omega
        rw [hagree x (Or.inr hxj), hm]
        have hx_ge : inp.h ≤ x := by omega
        exact hv.2.2.2.2.2.2.2.2.2.1 x hx_ge
    · intro st hpre
      have hm : st.mem (inp.jAddr + 1) = inp.J.m := by
        rw [hpre.1.1]; exact graphAt_m hpre.1.2.1.2.2.2.1
      have hvs : embVertSumMem st.mem inp.jAddr inp.embJHAddr =
          embVertSumMem mem₀ inp.jAddr inp.embJHAddr := by rw [hpre.1.1]
      simp [embJHStatsContract, argsSize, Expr.size, List.getD, hm, hvs]; omega
  exact (Triple.seq_normal_const h1 (Triple.seq_normal_const h2 h3)).mono_cost fun _ _ => by
    simp [Expr.size]; omega

lemma step2_strip_triple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task1Input} {mem₀ : ℕ → ℕ} {stripBase : ℕ}
    (hstrip : p.HasAt stripBase stripLoopsModule) :
    Triple w p
      (StatsInv inp impl mem₀ w)
      (Stmt.seq (Stmt.assign 7 (.bin .add (.reg 1) (.const 1))) <|
       Stmt.seq (Stmt.assign 7 (.load (.reg 7))) <|
       Stmt.seq (Stmt.assign 8 (.bin .mul (.const 2) (.reg 7))) <|
       Stmt.seq (Stmt.assign 8 (.bin .add (.reg 8) (.const 2))) <|
       Stmt.seq (Stmt.assign 8 (.bin .add (.reg 6) (.reg 8))) <|
       Stmt.call 9 stripBase [.reg 1, .reg 6, .reg 8])
      (normalPost (StripInv inp impl mem₀ w))
      (fun _ => 115 * inp.J.m + 83) := by
  have h1 : Triple w p (StatsInv inp impl mem₀ w)
      (Stmt.assign 7 (.bin .add (.reg 1) (.const 1)))
      (normalPost fun st => StatsInv inp impl mem₀ w st ∧ st.regs 7 = inp.jAddr + 1)
      (fun _ => (Expr.bin .add (.reg 1) (.const 1)).size + 1) := by
    refine Triple.assign (val := fun _ => inp.jAddr + 1) ?_ ?_
    · intro st hs
      have hb := task1_word_bounds hs.hv
      exact ev_add (ev_reg hs.hr1 hb.2.2.1) (ev_const hb.1) (by
        have := hs.hv.2.2.2.2.2.2.2.2.1; simp [Graph.encode] at this; omega)
    · intro st hs
      exact ⟨statsInv_update_78 (Or.inl rfl) hs, by simp [Function.update]⟩
  have h2 : Triple w p (fun st => StatsInv inp impl mem₀ w st ∧ st.regs 7 = inp.jAddr + 1)
      (Stmt.assign 7 (.load (.reg 7)))
      (normalPost fun st => StatsInv inp impl mem₀ w st ∧ st.regs 7 = inp.J.m)
      (fun _ => (Expr.load (.reg 7)).size + 1) := by
    refine Triple.assign (val := fun _ => inp.J.m) ?_ ?_
    · intro st ⟨hs, hr7⟩
      have hb := task1_word_bounds hs.hv
      have hm_lt : inp.jAddr + 1 < inp.h := by
        have := hs.hv.2.2.2.2.2.2.2.2.1; simp [Graph.encode] at this; omega
      have hmem : st.mem (inp.jAddr + 1) = inp.J.m := by
        rw [hs.h_below _ hm_lt]; exact graphAt_m hs.hv.2.2.2.1
      exact ev_load (ev_reg hr7 (by omega)) hmem (by omega)
    · intro st ⟨hs, _⟩
      exact ⟨statsInv_update_78 (Or.inl rfl) hs, by simp [Function.update]⟩
  have h3 : Triple w p (fun st => StatsInv inp impl mem₀ w st ∧ st.regs 7 = inp.J.m)
      (Stmt.assign 8 (.bin .mul (.const 2) (.reg 7)))
      (normalPost fun st => StatsInv inp impl mem₀ w st ∧ st.regs 8 = 2 * inp.J.m)
      (fun _ => (Expr.bin .mul (.const 2) (.reg 7)).size + 1) := by
    refine Triple.assign (val := fun _ => 2 * inp.J.m) ?_ ?_
    · intro st ⟨hs, hr7⟩
      have hb := task1_word_bounds hs.hv
      have hnl_gt : 2 * inp.J.m + 2 ≤ inp.nlAddr := by unfold Task1Input.nlAddr; omega
      exact ev_mul (ev_const (by omega)) (ev_reg hr7 (by omega)) (by omega)
    · intro st ⟨hs, _⟩
      exact ⟨statsInv_update_78 (Or.inr rfl) hs, by simp [Function.update]⟩
  have h4 : Triple w p (fun st => StatsInv inp impl mem₀ w st ∧ st.regs 8 = 2 * inp.J.m)
      (Stmt.assign 8 (.bin .add (.reg 8) (.const 2)))
      (normalPost fun st => StatsInv inp impl mem₀ w st ∧ st.regs 8 = 2 * inp.J.m + 2)
      (fun _ => (Expr.bin .add (.reg 8) (.const 2)).size + 1) := by
    refine Triple.assign (val := fun _ => 2 * inp.J.m + 2) ?_ ?_
    · intro st ⟨hs, hr8⟩
      have hb := task1_word_bounds hs.hv
      have hnl_gt : 2 * inp.J.m + 2 ≤ inp.nlAddr := by unfold Task1Input.nlAddr; omega
      exact ev_add (ev_reg hr8 (by omega)) (ev_const (by omega)) (by omega)
    · intro st ⟨hs, _⟩
      exact ⟨statsInv_update_78 (Or.inr rfl) hs, by simp [Function.update]⟩
  have h5 : Triple w p (fun st => StatsInv inp impl mem₀ w st ∧ st.regs 8 = 2 * inp.J.m + 2)
      (Stmt.assign 8 (.bin .add (.reg 6) (.reg 8)))
      (normalPost fun st => StatsInv inp impl mem₀ w st ∧ st.regs 8 = inp.nlAddr)
      (fun _ => (Expr.bin .add (.reg 6) (.reg 8)).size + 1) := by
    refine Triple.assign (val := fun _ => inp.j0Addr + (2 * inp.J.m + 2)) ?_ ?_
    · intro st ⟨hs, hr8⟩
      have hb := task1_word_bounds hs.hv
      have hsum : inp.j0Addr + (2 * inp.J.m + 2) = inp.nlAddr := by
        unfold Task1Input.nlAddr; omega
      exact ev_add (ev_reg hs.hr6 hb.2.2.2.2.2.2.2.1) (ev_reg hr8 (by unfold Task1Input.nlAddr at hb; omega))
        (by rw [hsum]; exact hb.2.2.2.2.2.2.2.2.1)
    · intro st ⟨hs, _⟩
      exact ⟨statsInv_update_78 (Or.inr rfl) hs, by
        simp [Function.update]; unfold Task1Input.nlAddr; omega⟩
  have h6 : Triple w p (fun st => StatsInv inp impl mem₀ w st ∧ st.regs 8 = inp.nlAddr)
      (Stmt.call 9 stripBase [.reg 1, .reg 6, .reg 8])
      (normalPost (StripInv inp impl mem₀ w))
      (fun _ => argsSize [.reg 1, .reg 6, .reg 8] + (115 * inp.J.m + 55) + 1) := by
    refine (Triple.call (stripLoops_meetsContract hstrip)
        (vs := fun _ => [inp.jAddr, inp.j0Addr, inp.nlAddr]) ?_ ?_ ?_ ?_).mono_cost ?_
    · intro st ⟨hs, hr8⟩
      have hb := task1_word_bounds hs.hv
      simp [evalArgs, ev_reg hs.hr1 hb.2.2.1, ev_reg hs.hr6 hb.2.2.2.2.2.2.2.1,
        ev_reg hr8 hb.2.2.2.2.2.2.2.2.1]
    · intro st ⟨hs, _⟩
      have hb := task1_word_bounds hs.hv
      intro v hvm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvm
      rcases hvm with rfl | rfl | rfl <;> omega
    · intro st ⟨hs, _⟩
      have hb := task1_word_bounds hs.hv
      have hJ_at : GraphAt st.mem inp.jAddr inp.J :=
        GraphAt.of_agree_below hs.hv.2.2.2.1 hs.hv.2.2.2.2.2.2.2.2.1 hs.h_below
      have hJ_enc_w : ∀ x ∈ inp.J.encode, x < 2 ^ w := hs.hv.2.2.2.2.2.2.2.2.2.2.2.1
      have hj_j0 : inp.jAddr + (2 + 2 * inp.J.m) ≤ inp.j0Addr := by
        have hlen := graph_encode_length inp.J
        have := hs.hv.2.2.2.2.2.2.2.2.1
        omega
      have hj0_nl : inp.j0Addr + (2 + 2 * inp.J.m) ≤ inp.nlAddr := by
        unfold Task1Input.nlAddr; omega
      exact ⟨inp.jAddr, inp.j0Addr, inp.nlAddr, inp.J, rfl, hJ_at, hJ_enc_w, hb.1,
        hj_j0, hj0_nl, hb.2.2.2.2.2.2.2.2.2.1⟩
    · intro st v mem' pos' ⟨hs, hr8⟩ hpost
      have hJ_at : GraphAt st.mem inp.jAddr inp.J :=
        GraphAt.of_agree_below hs.hv.2.2.2.1 hs.hv.2.2.2.2.2.2.2.2.1 hs.h_below
      have ⟨hv_eq, hJ0, hnl, hagree, _⟩ := hpost inp.jAddr inp.j0Addr inp.nlAddr inp.J rfl hJ_at
      have h0 : Function.update st.regs 9 v 0 = inp.hAddr := by simp [Function.update, hs.hr0]
      have h1' : Function.update st.regs 9 v 1 = inp.jAddr := by simp [Function.update, hs.hr1]
      have h2' : Function.update st.regs 9 v 2 = inp.embJHAddr := by simp [Function.update, hs.hr2]
      have h3' : Function.update st.regs 9 v 3 = inp.h := by simp [Function.update, hs.hr3]
      have h5' : Function.update st.regs 9 v 5 = inp.h + 6 := by simp [Function.update, hs.hr5]
      have h6' : Function.update st.regs 9 v 6 = inp.j0Addr := by simp [Function.update, hs.hr6]
      have h8' : Function.update st.regs 9 v 8 = inp.nlAddr := by simp [Function.update, hr8]
      have h9' : Function.update st.regs 9 v 9 = (stripLoops inp.J).m := by
        simp [Function.update, hv_eq]
      have hbelow' : ∀ x < inp.h, mem' x = mem₀ x := by
        intro x hx
        have hx_j0 : x < inp.j0Addr := lt_of_lt_of_le hx (by unfold Task1Input.j0Addr; omega)
        rw [hagree x (Or.inl hx_j0), hs.h_below x hx]
      have hhdr' : ∀ x, inp.h ≤ x → x < inp.h + 6 → mem' x = 0 := by
        intro x hx1 hx2
        have hx_j0 : x < inp.j0Addr := lt_of_lt_of_le hx2 (by unfold Task1Input.j0Addr; omega)
        rw [hagree x (Or.inl hx_j0)]
        exact hs.h_hdr_zero x hx1 hx2
      have hstats' : mem' (inp.h + 6) = maxDeg inp.J ∧
          mem' (inp.h + 6 + 1) = length inp.J inp.embJH ∧
          mem' (inp.h + 6 + 2) = vcongNat inp.J inp.H' inp.embJH := by
        have hst0 : inp.h + 6 < inp.j0Addr := by unfold Task1Input.j0Addr; omega
        have hst1 : inp.h + 6 + 1 < inp.j0Addr := by unfold Task1Input.j0Addr; omega
        have hst2 : inp.h + 6 + 2 < inp.j0Addr := by unfold Task1Input.j0Addr; omega
        rw [hagree _ (Or.inl hst0), hagree _ (Or.inl hst1), hagree _ (Or.inl hst2)]
        exact ⟨hs.hs0, hs.hs1, hs.hs2⟩
      have hzf' : ZeroFrom mem' inp.decAddr := by
        intro x hx
        have hxm : inp.nlAddr + (stripLoops inp.J).m ≤ x := by
          unfold Task1Input.decAddr at hx; exact hx
        rw [hagree x (Or.inr hxm)]
        have hj0_le_x : inp.j0Addr ≤ x := by unfold Task1Input.nlAddr at hxm; omega
        exact hs.h_zf x hj0_le_x
      exact ⟨hs.hv, h0, h1', h2', h3', h5', h6', h8', h9', hbelow', hhdr', hstats', hJ0, hnl, hzf'⟩
    · intro st ⟨hs, _⟩
      have hm_lt : inp.jAddr + 1 < inp.h := by
        have hlen := graph_encode_length inp.J
        have := hs.hv.2.2.2.2.2.2.2.2.1; omega
      have hmem : st.mem (inp.jAddr + 1) = inp.J.m := by
        rw [hs.h_below _ hm_lt]; exact graphAt_m hs.hv.2.2.2.1
      simp only [stripLoopsContract, List.getD, List.getElem?_cons_zero, Option.getD_some, hmem]
      exact le_rfl
  exact (Triple.seq_normal_const h1 (Triple.seq_normal_const h2 (Triple.seq_normal_const h3
    (Triple.seq_normal_const h4 (Triple.seq_normal_const h5 h6))))).mono_cost fun _ _ => by
    simp [Expr.size, argsSize]; omega

lemma step3_dec_triple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task1Input} {mem₀ : ℕ → ℕ} {decBase : ℕ}
    (hdec : p.HasAt decBase (impl.decompose.procs decBase)) :
    Triple w p
      (StripInv inp impl mem₀ w)
      (Stmt.seq (Stmt.assign 10 (.bin .add (.reg 8) (.reg 9))) <|
       Stmt.call 11 decBase [.reg 6, .reg 10])
      (normalPost (DecInv inp impl mem₀ w))
      (fun _ => ⌈impl.decompose.K_dec *
        (((stripLoops inp.J).m : ℝ) * impl.decompose.decFactor (stripLoops inp.J).m + 1)⌉₊ + 8) := by
  have h1 : Triple w p (StripInv inp impl mem₀ w)
      (Stmt.assign 10 (.bin .add (.reg 8) (.reg 9)))
      (normalPost fun st => StripInv inp impl mem₀ w st ∧ st.regs 10 = inp.decAddr)
      (fun _ => (Expr.bin .add (.reg 8) (.reg 9)).size + 1) := by
    refine Triple.assign (val := fun _ => inp.decAddr) ?_ ?_
    · intro st hs
      have hb := task1_word_bounds hs.hv
      exact ev_add (ev_reg hs.hr8 hb.2.2.2.2.2.2.2.2.1)
        (ev_reg hs.hr9 (by have := stripLoops_m_le inp.J; omega))
        (by unfold Task1Input.decAddr at hb; exact hb.2.2.2.2.2.2.2.2.2.2.1)
    · intro st hs
      exact ⟨stripInv_update_10 hs, by simp [Function.update, Task1Input.decAddr]⟩
  have h2 : Triple w p (fun st => StripInv inp impl mem₀ w st ∧ st.regs 10 = inp.decAddr)
      (Stmt.call 11 decBase [.reg 6, .reg 10])
      (normalPost (DecInv inp impl mem₀ w))
      (fun _ => argsSize [.reg 6, .reg 10] +
        ⌈impl.decompose.K_dec *
          (((stripLoops inp.J).m : ℝ) * impl.decompose.decFactor (stripLoops inp.J).m + 1)⌉₊ + 1) := by
    refine (Triple.call (impl.decompose.spec w p decBase hdec)
        (vs := fun _ => [inp.j0Addr, inp.decAddr]) ?_ ?_ ?_ ?_).mono_cost ?_
    · intro st ⟨hs, hr10⟩
      have hb := task1_word_bounds hs.hv
      simp [evalArgs, ev_reg hs.hr6 hb.2.2.2.2.2.2.2.1, ev_reg hr10 hb.2.2.2.2.2.2.2.2.2.2.1]
    · intro st ⟨hs, _⟩
      have hb := task1_word_bounds hs.hv
      intro v hvm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hvm
      rcases hvm with rfl | rfl <;> omega
    · intro st ⟨hs, _⟩
      have hb := task1_word_bounds hs.hv
      have hJ0_valid := stripLoops_isValid hs.hv.2.2.1
      have hJ0_loop := stripLoops_isLoopless inp.J
      have hcw_le : impl.decompose.cw * (Nat.log 2 ((stripLoops inp.J).n + (stripLoops inp.J).m +
          impl.decompose.maxPhiDen (stripLoops inp.J).m + 2) + 1) ≤ w :=
        hs.hv.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hj0_dec : inp.j0Addr + (stripLoops inp.J).encode.length ≤ inp.decAddr := by
        unfold Task1Input.decAddr; omega
      have hsp_lt : inp.decAddr + impl.decompose.space (stripLoops inp.J).n (stripLoops inp.J).m < 2 ^ w := by
        have hww := hs.hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have hmax1 : inp.maxHeapEnd impl ≤ inp.maxWordBound impl := le_max_left _ _
        have hmax2 : inp.coreHMax impl ≤ inp.maxHeapEnd impl := by
          dsimp only [Task1Input.maxHeapEnd]; omega
        have hmax3 : inp.prepHMax impl ≤ inp.coreHMax impl := by
          dsimp only [Task1Input.coreHMax]; omega
        have hpeq : inp.decAddr + impl.decompose.space inp.J.n (stripLoops inp.J).m = inp.prepHMax impl := rfl
        rw [show (stripLoops inp.J).n = inp.J.n from rfl, hpeq]
        omega
      refine ⟨⟨inp.j0Addr, inp.decAddr, stripLoops inp.J, rfl, hj0_dec, hs.h_J0, hJ0_valid,
        hJ0_loop, hcw_le⟩, hs.h_zf, ?_⟩
      dsimp only [WordRAM.heapArg]
      rw [show [inp.j0Addr, inp.decAddr].getLastD 0 = inp.decAddr from rfl]
      simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
      rw [graphAt_iff_readGraph.mp hs.h_J0]
      exact hsp_lt
    · intro st v mem' pos' ⟨hs, hr10⟩ hpost
      rcases hpost with ⟨⟨hv_ge, hv_le, hbelow_dec, hzf_v, gAddr, hArg, G, d_ℓ, phiNum, phiDen,
        level, rawComps, hargs_eq, hG_at, hdec_at, hlev_len, hpn, hpnd, hpd_cap, hφ_lb, hpw,
        hrc_props, hdp⟩, ⟨d_ℓ', phiNum', phiDen', level', rawComps', hdec_at', hlev_len', hdec_end'⟩⟩
      obtain ⟨rfl, rfl⟩ : gAddr = inp.j0Addr ∧ hArg = inp.decAddr := by
        simpa using hargs_eq.symm
      have hG_eq : G = stripLoops inp.J := graphAt_inj hG_at hs.h_J0
      subst hG_eq
      have hbelow_dec' : ∀ x < inp.decAddr, mem' x = st.mem x := by
        simpa [WordRAM.heapArg] using hbelow_dec
      have hv_ge' : inp.decAddr ≤ v := by simpa [WordRAM.heapArg] using hv_ge
      have hv_ub : v ≤ inp.prepHMax impl := by
        unfold Task1Input.prepHMax
        simpa [WordRAM.heapArg, List.getD, graphAt_iff_readGraph.mp hs.h_J0,
          show (stripLoops inp.J).n = inp.J.n from rfl] using hv_le
      have hlev_eq : level.length = level'.length :=
        hlev_len.trans (by simpa [WordRAM.heapArg, List.getD, graphAt_iff_readGraph.mp hs.h_J0] using hlev_len'.symm)
      have ⟨h1_eq, h2_eq, h3_eq, h4_eq, h5_eq⟩ := decomposeOutAt_inj hdec_at hdec_at' hlev_eq
      have hdec_enc_le : inp.decAddr + (Decompose.encode d_ℓ' phiNum' phiDen' level' rawComps').length ≤ v := by
        simpa [WordRAM.heapArg] using hdec_end'
      rw [← h1_eq, ← h2_eq, ← h3_eq, ← h4_eq, ← h5_eq] at hdec_enc_le
      have hbelow' : ∀ x < inp.h, mem' x = mem₀ x := by
        intro x hx
        have hxd : x < inp.decAddr := by
          unfold Task1Input.decAddr Task1Input.nlAddr Task1Input.j0Addr; omega
        rw [hbelow_dec' x hxd, hs.h_below x hx]
      have hhdr' : ∀ x, inp.h ≤ x → x < inp.h + 6 → mem' x = 0 := by
        intro x hx1 hx2
        have hxd : x < inp.decAddr := by
          unfold Task1Input.decAddr Task1Input.nlAddr Task1Input.j0Addr; omega
        rw [hbelow_dec' x hxd]
        exact hs.h_hdr_zero x hx1 hx2
      have hstats' : mem' (inp.h + 6) = maxDeg inp.J ∧
          mem' (inp.h + 6 + 1) = length inp.J inp.embJH ∧
          mem' (inp.h + 6 + 2) = vcongNat inp.J inp.H' inp.embJH := by
        have hstats_lt_dec : inp.h + 6 + 3 ≤ inp.decAddr := by
          unfold Task1Input.decAddr Task1Input.nlAddr Task1Input.j0Addr; omega
        rw [hbelow_dec' _ (by omega), hbelow_dec' _ (by omega), hbelow_dec' _ (by omega)]
        exact hs.h_stats
      have hJ_at' : GraphAt mem' inp.jAddr inp.J :=
        GraphAt.of_agree_below hs.hv.2.2.2.1 hs.hv.2.2.2.2.2.2.2.2.1 hbelow'
      have hJ0_at' : GraphAt mem' inp.j0Addr (stripLoops inp.J) :=
        GraphAt.of_agree_below hs.h_J0 (by
          have := (task1_word_bounds hs.hv).2.2.2.2.2.2.2.2.2.2.2.1
          unfold Task1Input.decAddr; omega) (fun k hk => hbelow_dec' k hk)
      have hnl_at' : ListAt mem' inp.nlAddr (nonloopIndices inp.J) := by
        intro i hi
        have hinl : inp.nlAddr + i < inp.decAddr := by
          have hlen : (nonloopIndices inp.J).length = (stripLoops inp.J).m := by
            simp [stripLoops, Graph.m]
          unfold Task1Input.decAddr; omega
        rw [hbelow_dec' _ hinl]
        exact hs.h_nl i hi
      let pInp : PrepInput :=
        ⟨inp.jAddr, inp.j0Addr, inp.nlAddr, inp.decAddr, v, inp.J, stripLoops inp.J,
          nonloopIndices inp.J, d_ℓ, phiNum, phiDen, level, rawComps, impl.decompose.c_ℓ⟩
      have hp_wb : v + 9 + d_ℓ + 16 * (stripLoops inp.J).m + 2 * inp.J.n < 2 ^ w := by
        have hdl_le : d_ℓ ≤ Task1Input.dLMax impl inp.J := by
          have hdp1 := hdp.1
          change (d_ℓ : ℝ) ≤ impl.decompose.c_ℓ * (Nat.log 2 ((stripLoops inp.J).m + 2) + 1) at hdp1
          exact Nat.le_floor hdp1
        have hmax1 : inp.maxHeapEnd impl ≤ inp.maxWordBound impl := le_max_left _ _
        have hmax2 : inp.coreHMax impl ≤ inp.maxHeapEnd impl := by
          dsimp only [Task1Input.maxHeapEnd]; omega
        have hc_def : inp.coreHMax impl = inp.prepHMax impl + 9 + Task1Input.dLMax impl inp.J +
            16 * (stripLoops inp.J).m + 2 * inp.J.n := rfl
        have hww := hs.hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        omega
      have hp_valid : pInp.Valid mem' w := by
        refine ⟨hs.hv.2.2.1, hJ_at', rfl, hJ0_at', rfl, hnl_at', hdec_at, hlev_len, hpn, hpnd,
          hpw, hrc_props, hdp, ?_, ?_, ?_, hdec_enc_le, hzf_v, (task1_word_bounds hs.hv).1, hp_wb⟩
        · dsimp only [pInp]; have := hs.hv.2.2.2.2.2.2.2.2.1
          unfold Task1Input.decAddr Task1Input.nlAddr Task1Input.j0Addr at *; omega
        · dsimp only [pInp]; have := (task1_word_bounds hs.hv).2.2.2.2.2.2.2.2.2.2.2.1
          unfold Task1Input.decAddr at *; omega
        · dsimp only [pInp]
          have hlen : (nonloopIndices inp.J).length = (stripLoops inp.J).m := by simp [stripLoops, Graph.m]
          unfold Task1Input.decAddr at hv_ge'; omega
      exact ⟨⟨hs.hv, pInp, rfl, rfl, rfl, rfl, rfl, rfl, hp_valid, hv_ge', hv_ub, hφ_lb, hpd_cap,
        by simp [Function.update, hs.hr1],
        by simp [Function.update, hs.hr3],
        by simp [Function.update, hs.hr5],
        by simp [Function.update, hs.hr6],
        by simp [Function.update, hs.hr8],
        by simp [Function.update, hr10],
        by simp [Function.update]; rfl,
        hbelow', hhdr', hstats'⟩⟩
    · intro st ⟨hs, _⟩
      dsimp only [decomposeContract, decomposeHeapContract, WordRAM.heapContract]
      rw [show ([inp.j0Addr, inp.decAddr].getD 0 0) = inp.j0Addr from rfl]
      rw [graphAt_iff_readGraph.mp hs.h_J0]
  exact (Triple.seq_normal_const h1 h2).mono_cost fun _ _ => by simp [Expr.size, argsSize]; omega

lemma step4_prep_triple {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {inp : Task1Input} {mem₀ : ℕ → ℕ} {prepBase : ℕ}
    (hprep : p.HasAt prepBase witnessPrepModule) :
    Triple w p
      (DecInv inp impl mem₀ w)
      (Stmt.call 12 prepBase [.reg 1, .reg 6, .reg 8, .reg 10, .reg 11])
      (normalPost (PrepDoneInv inp impl mem₀ w))
      (fun _ => 1200 * (stripLoops inp.J).m + 506) := by
  refine (Triple.call (witnessPrep_meetsContract hprep) (vs := fun st =>
      [inp.jAddr, inp.j0Addr, inp.nlAddr, inp.decAddr, st.regs 11])
      ?_ ?_ ?_ ?_).mono_cost ?_
  · intro st ⟨hd⟩
    have hb := task1_word_bounds hd.hv
    have h11 : st.regs 11 < 2 ^ w := by
      have hmax1 : inp.maxHeapEnd impl ≤ inp.maxWordBound impl := le_max_left _ _
      have hmax2 : inp.coreHMax impl ≤ inp.maxHeapEnd impl := by
        dsimp only [Task1Input.maxHeapEnd]; omega
      have hmax3 : inp.prepHMax impl ≤ inp.coreHMax impl := by
        dsimp only [Task1Input.coreHMax]; omega
      have hww := hd.hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [hd.hr11]; exact lt_of_le_of_lt hd.hp_h_le (by omega)
    simp [evalArgs, ev_reg hd.hr1 hb.2.2.1, ev_reg hd.hr6 hb.2.2.2.2.2.2.2.1,
      ev_reg hd.hr8 hb.2.2.2.2.2.2.2.2.1, ev_reg hd.hr10 hb.2.2.2.2.2.2.2.2.2.2.1,
      ev_reg rfl h11]
  · intro st ⟨hd⟩ v hvm
    have hb := task1_word_bounds hd.hv
    have hmax1 : inp.maxHeapEnd impl ≤ inp.maxWordBound impl := le_max_left _ _
    have hmax2 : inp.coreHMax impl ≤ inp.maxHeapEnd impl := by
      dsimp only [Task1Input.maxHeapEnd]; omega
    have hmax3 : inp.prepHMax impl ≤ inp.coreHMax impl := by
      dsimp only [Task1Input.coreHMax]; omega
    have hww := hd.hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have h11 : st.regs 11 < 2 ^ w := by rw [hd.hr11]; exact lt_of_le_of_lt hd.hp_h_le (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvm
    rcases hvm with rfl | rfl | rfl | rfl | rfl <;> omega
  · intro st ⟨hd⟩
    refine ⟨rfl, hd.pInp, hd.hp_jAddr, hd.hp_j0Addr, hd.hp_nlAddr, hd.hp_decAddr, hd.hr11.symm, hd.hp_valid⟩
  · intro st v mem' pos' ⟨hd⟩ hpost
    have ⟨hv_eq, hst_state, hdone, _, hzf_end⟩ := hpost hd.pInp hd.hp_jAddr hd.hp_j0Addr
      hd.hp_nlAddr hd.hp_decAddr hd.hr11.symm hd.hp_valid
    have hstatic_valid : hd.pInp.StaticValid mem' w :=
      hd.hp_valid.toStatic.of_agree_below hst_state.1
    have hstatic_self : PrepStaticState hd.pInp mem' mem' :=
      ⟨fun _ _ => rfl, hst_state.2.1, hst_state.2.2.1, hst_state.2.2.2.1, hst_state.2.2.2.2.1,
        hst_state.2.2.2.2.2.1, hst_state.2.2.2.2.2.2.1, hst_state.2.2.2.2.2.2.2.1,
        hst_state.2.2.2.2.2.2.2.2.1, hst_state.2.2.2.2.2.2.2.2.2.1,
        hst_state.2.2.2.2.2.2.2.2.2.2⟩
    let wInp : WitnessCoreInput := ⟨inp.H', inp.embJH, hd.pInp, inp.h + 6, v⟩
    have hcaps := WitnessCoreInput.caps_le (wInp := wInp) hd.hp_valid hd.hp_J rfl rfl hd.hp_cℓ
      rfl hd.h_phi_lb hd.h_phi_cap hd.hp_h_le
    have hw_cost := buildWitnessCoreCost_le_cap (wInp := wInp) hd.hp_valid hd.hp_J hcaps.1
      hcaps.2.1 hcaps.2.2.1 hd.h_phi_lb
    obtain ⟨hw_valid, hw_maxEnd⟩ : wInp.Valid impl.constructExpander impl.pathDS.params mem' w ∧
        wInp.maxHeapEnd impl.constructExpander impl.pathDS.params ≤ inp.maxHeapEnd impl := by
      have hm0_eq : hd.pInp.J0_strip.m = (stripLoops inp.J).m := congrArg Graph.m hcaps.1
      have hφ_le_cap : hd.pInp.phiDen_dec ≤ Task1Input.phiDenCap impl inp.J := by
        unfold Task1Input.phiDenCap; rw [← hm0_eq]; exact hd.h_phi_cap
      have hagree_p := hst_state.1
      have hstats_lt : inp.h + 6 + 3 ≤ v := by
        have hsb_end : hd.pInp.h ≤ hd.pInp.hEnd := by
          unfold PrepInput.hEnd PrepInput.hBlocksStart; omega
        have hde : inp.h + 6 + 3 ≤ inp.decAddr := by
          unfold Task1Input.decAddr Task1Input.nlAddr Task1Input.j0Addr; omega
        have hgd := hd.hp_h_ge
        rw [hv_eq]; omega
      have hstats_mem : mem' (inp.h + 6) = maxDeg inp.J ∧
          mem' (inp.h + 6 + 1) = length inp.J inp.embJH ∧
          mem' (inp.h + 6 + 2) = vcongNat inp.J inp.H' inp.embJH := by
        have hlt_h : inp.h + 6 + 2 < hd.pInp.h := by
          have := hd.hp_h_ge; unfold Task1Input.decAddr Task1Input.nlAddr Task1Input.j0Addr at *; omega
        rw [hagree_p _ (by omega), hagree_p _ (by omega), hagree_p _ (by omega)]
        exact hd.h_stats
      have hww := hd.hv.2.2.2.2.2.2.2.2.2.2
      have hcw_J : impl.pathDS.params.cw * (Nat.log 2 (wInp.dJInt + hd.pInp.J0_strip.m +
          impl.pathDS.params.gExp wInp.dJInt hd.pInp.J0_strip.m +
          impl.pathDS.params.gDel wInp.dJInt hd.pInp.J0_strip.m + 2) + 1) ≤ w := by
        have dJ1 : 1 ≤ wInp.dJInt := by
          have hpn : 1 ≤ hd.pInp.phiNum_dec := hd.hp_valid.2.2.2.2.2.2.2.2.1
          have hpnd : hd.pInp.phiNum_dec ≤ hd.pInp.phiDen_dec := hd.hp_valid.2.2.2.2.2.2.2.2.2.1
          dsimp only [WitnessCoreInput.dJInt, wInp]
          exact Nat.div_pos (by omega) hpn
        have hm0_le : hd.pInp.J0_strip.m ≤ (stripLoops inp.J).m := hm0_eq.le
        have hg1 := impl.pathDS.params.hgExp_mono dJ1 hcaps.2.1 hm0_le
        have hg2 := impl.pathDS.params.hgDel_mono dJ1 hcaps.2.1 hm0_le
        have hlog := Nat.log_mono_right (b := 2) (by rw [hm0_eq] at *; omega :
          wInp.dJInt + hd.pInp.J0_strip.m +
          impl.pathDS.params.gExp wInp.dJInt hd.pInp.J0_strip.m +
          impl.pathDS.params.gDel wInp.dJInt hd.pInp.J0_strip.m + 2 ≤
          Task1Input.dJCap impl inp.J + (stripLoops inp.J).m +
          impl.pathDS.params.gExp (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m +
          impl.pathDS.params.gDel (Task1Input.dJCap impl inp.J) (stripLoops inp.J).m + 2)
        have hm := Nat.mul_le_mul_left impl.pathDS.params.cw (Nat.add_le_add_right hlog 1)
        exact le_trans hm hww.2.2.2.1
      have hcw_W : impl.pathDS.params.cw * (Nat.log 2 (WitnessCoreInput.dWInt impl.constructExpander +
          wInp.mwInt impl.constructExpander +
          impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) (wInp.mwInt impl.constructExpander) +
          impl.pathDS.params.gDel (WitnessCoreInput.dWInt impl.constructExpander) (wInp.mwInt impl.constructExpander) + 2) + 1) ≤ w := by
        have dW1 : 1 ≤ WitnessCoreInput.dWInt impl.constructExpander := by
          dsimp only [WitnessCoreInput.dWInt]
          exact Nat.div_pos (by have := impl.constructExpander.hphi_le; have := impl.constructExpander.hphi_pos; omega)
            impl.constructExpander.hphi_pos
        have hg1 := impl.pathDS.params.hgExp_mono dW1 le_rfl hcaps.2.2.1
        have hg2 := impl.pathDS.params.hgDel_mono dW1 le_rfl hcaps.2.2.1
        have hlog := Nat.log_mono_right (b := 2) (by omega : WitnessCoreInput.dWInt impl.constructExpander +
          wInp.mwInt impl.constructExpander +
          impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) (wInp.mwInt impl.constructExpander) +
          impl.pathDS.params.gDel (WitnessCoreInput.dWInt impl.constructExpander) (wInp.mwInt impl.constructExpander) + 2 ≤
          WitnessCoreInput.dWInt impl.constructExpander + Task1Input.mwCap impl inp.J +
          impl.pathDS.params.gExp (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) +
          impl.pathDS.params.gDel (WitnessCoreInput.dWInt impl.constructExpander) (Task1Input.mwCap impl inp.J) + 2)
        have hm := Nat.mul_le_mul_left impl.pathDS.params.cw (Nat.add_le_add_right hlog 1)
        exact le_trans hm hww.2.2.2.2.1
      have hcw_ce : impl.constructExpander.cw *
          (Nat.log 2 (hd.pInp.J.n + 4 * hd.pInp.J0_strip.m * hd.pInp.phiDen_dec + 2) + 1) ≤ w := by
        have hmul : 4 * hd.pInp.J0_strip.m * hd.pInp.phiDen_dec ≤
            4 * (stripLoops inp.J).m * Task1Input.phiDenCap impl inp.J := by
          rw [hm0_eq]; exact Nat.mul_le_mul_left _ hφ_le_cap
        have hlog := Nat.log_mono_right (b := 2) (by rw [hd.hp_J]; omega :
          hd.pInp.J.n + 4 * hd.pInp.J0_strip.m * hd.pInp.phiDen_dec + 2 ≤
          inp.J.n + 4 * (stripLoops inp.J).m * Task1Input.phiDenCap impl inp.J + 2)
        have hm := Nat.mul_le_mul_left impl.constructExpander.cw (Nat.add_le_add_right hlog 1)
        exact le_trans hm hww.2.2.2.2.2.1
      have hsb_len : hd.pInp.rawComps.length ≤ (stripLoops inp.J).m :=
        hm0_eq ▸ (PrepInput.size_bounds hd.hp_valid).2.1
      have hmax_end_le : wInp.maxHeapEnd impl.constructExpander impl.pathDS.params ≤
          inp.maxHeapEnd impl := by
        have hcore_v : v ≤ inp.coreHMax impl := hv_eq ▸ hcaps.2.2.2.2.2
        have hb1 : impl.pathDS.params.boundsSpace wInp.dJInt hd.pInp.J0_strip.m ≤
            impl.pathDS.params.C_space * (Task1Input.dJCap impl inp.J + (stripLoops inp.J).m + 2) ^
              impl.pathDS.params.c_space := by
          refine le_trans (impl.pathDS.params.hboundsSpace_le _ _) ?_
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        have hb2 : impl.pathDS.params.boundsSpace (WitnessCoreInput.dWInt impl.constructExpander)
              (wInp.mwInt impl.constructExpander) ≤
            impl.pathDS.params.C_space * (WitnessCoreInput.dWInt impl.constructExpander +
              Task1Input.mwCap impl inp.J + 2) ^ impl.pathDS.params.c_space := by
          refine le_trans (impl.pathDS.params.hboundsSpace_le _ _) ?_
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        have hce_sp : hd.pInp.rawComps.length * impl.constructExpander.C_space *
              (hd.pInp.J.n + 4 * hd.pInp.J0_strip.m * hd.pInp.phiDen_dec + 2) ^
                impl.constructExpander.c_space ≤
            (stripLoops inp.J).m * impl.constructExpander.C_space *
              (inp.J.n + 4 * (stripLoops inp.J).m * Task1Input.phiDenCap impl inp.J + 2) ^
                impl.constructExpander.c_space := by
          have hmul1 := Nat.mul_le_mul_right impl.constructExpander.C_space hsb_len
          have hmul_phi : 4 * hd.pInp.J0_strip.m * hd.pInp.phiDen_dec ≤
              4 * (stripLoops inp.J).m * Task1Input.phiDenCap impl inp.J := by
            rw [hm0_eq]; exact Nat.mul_le_mul_left _ hφ_le_cap
          have hpow : (hd.pInp.J.n + 4 * hd.pInp.J0_strip.m * hd.pInp.phiDen_dec + 2) ^
                impl.constructExpander.c_space ≤
              (inp.J.n + 4 * (stripLoops inp.J).m * Task1Input.phiDenCap impl inp.J + 2) ^
                impl.constructExpander.c_space :=
            Nat.pow_le_pow_left (by rw [hd.hp_J]; omega) _
          exact Nat.mul_le_mul hmul1 hpow
        have hwm_le : hd.pInp.J0_strip.m + 2 * impl.constructExpander.c_deg_int *
              hd.pInp.J0_strip.m * hd.pInp.phiDen_dec ≤
            (stripLoops inp.J).m + 2 * impl.constructExpander.c_deg_int *
              (stripLoops inp.J).m * Task1Input.phiDenCap impl inp.J := by
          have h3 : 2 * impl.constructExpander.c_deg_int * hd.pInp.J0_strip.m * hd.pInp.phiDen_dec ≤
              2 * impl.constructExpander.c_deg_int * (stripLoops inp.J).m * Task1Input.phiDenCap impl inp.J := by
            rw [hm0_eq]; exact Nat.mul_le_mul_left _ hφ_le_cap
          omega
        dsimp only [WitnessCoreInput.maxHeapEnd, Task1Input.maxHeapEnd, wInp] at *
        rw [hd.hp_J, hm0_eq] at *
        omega
      have hmwb : wInp.maxWordBound impl.constructExpander impl.pathDS.params < 2 ^ w := by
        have hmwb_le : wInp.maxWordBound impl.constructExpander impl.pathDS.params ≤
            inp.maxWordBound impl := by
          dsimp only [WitnessCoreInput.maxWordBound, Task1Input.maxWordBound]
          refine max_le (le_trans hmax_end_le (le_max_left _ _)) (max_le ?_ ?_)
          · refine le_trans ?_ (le_trans (le_max_left _ _) (le_max_right _ _))
            dsimp only [wInp]
            rw [hm0_eq]
            have h1 := Nat.mul_le_mul_left (4 * ((stripLoops inp.J).m + 1)) hφ_le_cap
            have h2 := Nat.mul_le_mul_left (2 * impl.constructExpander.c_deg_int *
              ((stripLoops inp.J).m + 1)) hφ_le_cap
            omega
          · refine le_trans ?_ (le_trans (le_max_right _ _) (le_max_right _ _))
            have htau := hcaps.2.2.2.2.1
            dsimp only [wInp] at htau ⊢
            rw [hd.hp_J]
            have hm_le := Nat.mul_le_mul_right
              (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1)
              (Nat.mul_le_mul_right (length inp.J inp.embJH + 1) (Nat.mul_le_mul_left 2 htau))
            exact Nat.add_le_add_right hm_le 2
        exact lt_of_le_of_lt hmwb_le hww.2.2.2.2.2.2
      exact ⟨⟨hd.hv.1, by dsimp only [wInp]; rw [hd.hp_J]; exact hd.hv.2.2.2.2.1,
        hstatic_valid, hv_eq.symm ▸ le_rfl, hstats_lt,
        by rw [hd.hp_J]; exact hstats_mem.1, by rw [hd.hp_J]; exact hstats_mem.2.1,
        by rw [hd.hp_J]; exact hstats_mem.2.2, hstatic_self, hdone,
        by change ZeroFrom mem' v; rw [hv_eq]; exact hzf_end,
        hcw_J, hcw_W, hcw_ce, hmwb⟩, hmax_end_le⟩
    have hbelow' : ∀ x < inp.h, mem' x = mem₀ x := fun x hx => by
      have hx_p : x < hd.pInp.h := lt_of_lt_of_le hx (by
        have := hd.hp_h_ge; unfold Task1Input.decAddr Task1Input.nlAddr Task1Input.j0Addr at *; omega)
      rw [hst_state.1 x hx_p, hd.h_below x hx]
    have hhdr' : ∀ x, inp.h ≤ x → x < inp.h + 6 → mem' x = 0 := fun x hx1 hx2 => by
      have hx_p : x < hd.pInp.h := lt_of_lt_of_le hx2 (by
        have := hd.hp_h_ge; unfold Task1Input.decAddr Task1Input.nlAddr Task1Input.j0Addr at *; omega)
      rw [hst_state.1 x hx_p]
      exact hd.h_hdr_zero x hx1 hx2
    exact ⟨⟨hd.hv, wInp, rfl, rfl, rfl, hd.hp_jAddr, hd.hp_j0Addr, hd.hp_nlAddr, hd.hp_decAddr,
      hd.hp_J, hd.hp_cℓ, hw_valid, hw_maxEnd, hstatic_self, hdone, hd.h_phi_lb, hd.h_phi_cap, hw_cost,
      by simp [Function.update, hd.hr1],
      by simp [Function.update, hd.hr3],
      by simp [Function.update, hd.hr5],
      by simp [Function.update, hd.hr6],
      by simp [Function.update, hd.hr8],
      by simp [Function.update, hd.hr10],
      by simp [Function.update, hd.hr11]; rfl,
      by simp [Function.update]; rfl,
      hbelow', hhdr'⟩⟩
  · intro st ⟨hd⟩
    have hj0_m : st.mem (inp.j0Addr + 1) = (stripLoops inp.J).m := by
      have h := graphAt_m hd.hp_valid.2.2.2.1
      rw [hd.hp_valid.2.2.1, hd.hp_J, hd.hp_j0Addr] at h
      exact h
    dsimp only [witnessPrepContract, argsSize]
    simp [List.getD, hj0_m]; omega

end MinCostFlow.Spanner
