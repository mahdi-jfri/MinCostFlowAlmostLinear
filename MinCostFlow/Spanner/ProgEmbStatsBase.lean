module

public import MinCostFlow.Spanner.ProgSetup
import Mathlib.Tactic

/-!
# Embedding statistics program: definitions, invariants, and first loop

Defines `embJHSetupStmt`, `embJHStatsBody`, `embJHStatsModule`, and `embJHStatsContract`,
together with prefix-count helpers, loop invariants, and the first-loop triple
`embJHStats_loop1_triple`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Procedure 2: `embJHStatsModule` (`O(J.m * (length J embJH + 1) + 1)`) -/

/-- `embJHStatsBody` reads `[jAddr, embJHAddr, hnH, h]` (`ZeroFrom mem h`), writes
`[maxDeg J, length J embJH, vcongNat J H' embJH]` at `[h, h + 3)`, uses scratch `[h + 3, h + 3 + J.n + 2 * H'.n)`,
and returns `h + 3 + J.n + 2 * H'.n` in `O(J.m * (length J embJH + 1) + 1)` time. -/
def embJHSetupStmt : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 6 (.bin .add (.reg 3) (.const 3)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 4)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 2)) ;;
  .assign 9 (.const 0) ;;
  .assign 10 (.const 0) ;;
  .assign 11 (.const 0)

def embJHStatsBody : Stmt :=
  embJHSetupStmt ;;
  forRange 12 (.const 0) (.reg 5) (
    .assign 13 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 12))))) ;;
    .assign 14 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 12))))) ;;
    .assign 15 (.bin .add (.load (.bin .add (.reg 6) (.reg 13))) (.const 1)) ;;
    .store (.bin .add (.reg 6) (.reg 13)) (.reg 15) ;;
    .cond (.bin .lt (.reg 9) (.reg 15)) (.assign 9 (.reg 15)) (.assign 17 (.const 0)) ;;
    .assign 15 (.bin .add (.load (.bin .add (.reg 6) (.reg 14))) (.const 1)) ;;
    .store (.bin .add (.reg 6) (.reg 14)) (.reg 15) ;;
    .cond (.bin .lt (.reg 9) (.reg 15)) (.assign 9 (.reg 15)) (.assign 17 (.const 0))
  ) ;;
  forRange 12 (.const 0) (.reg 5) (
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
  ) ;;
  .store (.reg 3) (.reg 9) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 10) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.reg 11) ;;
  .ret (.bin .add (.reg 8) (.reg 2))

/-- Single-procedure module for `embJHStats`. -/
def embJHStatsModule : List Stmt := [embJHStatsBody]

theorem embJHStatsBody_noRand : embJHStatsBody.NoRand := by
  simp [embJHStatsBody, embJHSetupStmt, forRange, forUp, Stmt.NoRand]

theorem embJHStatsModule_noRand : ∀ s ∈ embJHStatsModule, s.NoRand := by
  simp only [embJHStatsModule, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact embJHStatsBody_noRand

/-- Contract for `embJHStats`: `args = [jAddr, embJHAddr, hnH, h]`. -/
def embJHStatsContract (w : ℕ) : Contract where
  pre args mem := ∃ (jAddr embJHAddr hnH h : ℕ) (J H' : Graph) (embJH : ℕ → Walk) (bound : ℕ),
    args = [jAddr, embJHAddr, hnH, h] ∧
    hnH = H'.n ∧
    GraphAt mem jAddr J ∧
    J.IsValid ∧
    EmbAt mem embJHAddr J.m embJH ∧
    EmbBounded mem embJHAddr J.m embJH bound ∧
    (∀ e < J.m, ∀ x ∈ (embJH e).verts, x < H'.n) ∧
    1 < 2 ^ w ∧
    jAddr + (2 + 2 * J.m) ≤ h ∧
    bound ≤ h ∧
    bound < 2 ^ w ∧
    2 * J.m + 2 < 2 ^ w ∧
    h + 3 + J.n + 2 * H'.n < 2 ^ w ∧
    ZeroFrom mem h
  post args mem v mem' := ∀ jAddr embJHAddr hnH h (J H' : Graph) (embJH : ℕ → Walk),
    args = [jAddr, embJHAddr, hnH, h] → hnH = H'.n →
    GraphAt mem jAddr J → EmbAt mem embJHAddr J.m embJH →
      v = h + 3 + J.n + 2 * H'.n ∧
      mem' h = maxDeg J ∧
      mem' (h + 1) = length J embJH ∧
      mem' (h + 2) = vcongNat J H' embJH ∧
      AgreeOutside mem' mem h (h + 3 + J.n + 2 * H'.n) ∧
      ZeroFrom mem' (h + 3 + J.n + 2 * H'.n)
  cost args mem := 215 * mem (args.getD 0 0 + 1) + 120 * embVertSumMem mem (args.getD 0 0) (args.getD 1 0) + 180

def degPrefix (J : Graph) (k x : ℕ) : ℕ :=
  ((List.range k).filter fun i => decide ((J.edges.getD i (0, 0)).1 = x)).length +
    ((List.range k).filter fun i => decide ((J.edges.getD i (0, 0)).2 = x)).length

private theorem degPrefix_succ (J : Graph) (k x : ℕ) :
    degPrefix J (k + 1) x =
      degPrefix J k x +
        (if (J.edges.getD k (0, 0)).1 = x then 1 else 0) +
        (if (J.edges.getD k (0, 0)).2 = x then 1 else 0) := by
  unfold degPrefix
  rw [List.range_succ, List.filter_append, List.filter_append, List.filter_cons,
      List.filter_cons, List.filter_nil, List.length_append, List.length_append]
  by_cases h1 : (J.edges[k]?.getD (0, 0)).1 = x <;>
    by_cases h2 : (J.edges[k]?.getD (0, 0)).2 = x <;>
    simp [List.getD, h1, h2] <;> omega

private theorem degPrefix_take (J : Graph) (k x : ℕ) (hk : k ≤ J.edges.length) :
    degPrefix J k x =
      ((J.edges.take k).filter fun e => decide (e.1 = x)).length +
        ((J.edges.take k).filter fun e => decide (e.2 = x)).length := by
  induction k with
  | zero => simp [degPrefix]
  | succ k ih =>
    have hke : k < J.edges.length := hk
    rw [degPrefix_succ, ih (Nat.le_of_lt hk), List.take_add_one,
        List.getElem?_eq_getElem hke, Option.toList_some,
        List.filter_append, List.filter_append, List.filter_cons, List.filter_cons,
        List.filter_nil, List.length_append, List.length_append]
    have hget : J.edges.getD k (0, 0) = J.edges[k]'hke := List.getD_eq_getElem _ _ hke
    rw [hget]
    by_cases h1 : (J.edges[k]'hke).1 = x <;> by_cases h2 : (J.edges[k]'hke).2 = x <;>
      simp [h1, h2] <;> omega

private theorem degPrefix_full {J : Graph} (hJ : J.IsValid) (x : ℕ) :
    degPrefix J J.m x = J.deg x := by
  have h := degPrefix_take J J.m x (le_refl _)
  have htake : J.edges.take J.m = J.edges := List.take_of_length_le (le_refl _)
  rw [htake] at h
  rw [h, Graph.deg, Graph.degIn, inside_verts_eq_edges hJ]

theorem degPrefix_le (J : Graph) (k x : ℕ) : degPrefix J k x ≤ 2 * k := by
  unfold degPrefix
  have h1 := List.length_filter_le (p := fun i => decide ((J.edges.getD i (0, 0)).1 = x)) (List.range k)
  have h2 := List.length_filter_le (p := fun i => decide ((J.edges.getD i (0, 0)).2 = x)) (List.range k)
  rw [List.length_range] at h1 h2
  omega

theorem maxDeg_eq_fold {J : Graph} (hJ : J.IsValid) :
    maxDeg J = (Finset.range J.n).fold max 0 (degPrefix J J.m) := by
  unfold maxDeg
  congr 1; ext x; exact (degPrefix_full hJ x).symm

def vcPrefix (embJH : ℕ → Walk) (e t x : ℕ) : ℕ :=
  ((Finset.range e).filter fun j => x ∈ (embJH j).verts).card +
    if ∃ s < t, (embJH e).verts.getD s 0 = x then 1 else 0

def lenPrefix (embJH : ℕ → Walk) (e : ℕ) : ℕ :=
  (Finset.range e).fold max 0 fun j => (embJH j).edges.length

theorem vcPrefix_succ (embJH : ℕ → Walk) (e t x : ℕ) :
    vcPrefix embJH e (t + 1) x =
      if ∃ s < t, (embJH e).verts.getD s 0 = x then vcPrefix embJH e t x
      else if (embJH e).verts.getD t 0 = x then vcPrefix embJH e t x + 1
      else vcPrefix embJH e t x := by
  unfold vcPrefix
  by_cases hprev : ∃ s < t, (embJH e).verts.getD s 0 = x
  · have hcur : ∃ s < t + 1, (embJH e).verts.getD s 0 = x := by
      rcases hprev with ⟨s, hs, hsq⟩; exact ⟨s, Nat.lt_succ_of_lt hs, hsq⟩
    simp only [hprev, hcur, ↓reduceIte]
  · by_cases hnow : (embJH e).verts.getD t 0 = x
    · have hcur : ∃ s < t + 1, (embJH e).verts.getD s 0 = x := ⟨t, Nat.lt_succ_self t, hnow⟩
      simp only [hprev, hnow, hcur, ↓reduceIte]
    · have hcur : ¬ ∃ s < t + 1, (embJH e).verts.getD s 0 = x := by
        rintro ⟨s, hs, hsq⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hst | rfl
        · exact hprev ⟨s, hst, hsq⟩
        · exact hnow hsq
      simp only [hprev, hnow, hcur, ↓reduceIte]

theorem vcPrefix_end (embJH : ℕ → Walk) (e x : ℕ) :
    vcPrefix embJH e (embJH e).verts.length x = vcPrefix embJH (e + 1) 0 x := by
  unfold vcPrefix
  have hmem : (∃ s < (embJH e).verts.length, (embJH e).verts.getD s 0 = x) ↔
      x ∈ (embJH e).verts := by
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [List.getD_eq_getElem _ _ hs]; exact List.getElem_mem hs
    · intro hx
      rcases List.mem_iff_getElem.mp hx with ⟨s, hs, rfl⟩
      exact ⟨s, hs, List.getD_eq_getElem _ _ hs⟩
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hx : x ∈ (embJH e).verts
  · have h1 : ∃ s < (embJH e).verts.length, (embJH e).verts.getD s 0 = x := hmem.mpr hx
    have hnot : e ∉ (Finset.range e).filter (fun j => x ∈ (embJH j).verts) := by simp
    simp only [h1, hx, ↓reduceIte, Finset.card_insert_of_notMem hnot]
    simp
  · have h1 : ¬ ∃ s < (embJH e).verts.length, (embJH e).verts.getD s 0 = x := fun h => hx (hmem.mp h)
    simp only [h1, hx, ↓reduceIte]
    simp

theorem vcPrefix_le (embJH : ℕ → Walk) (e t x : ℕ) : vcPrefix embJH e t x ≤ e + 1 := by
  unfold vcPrefix
  have h1 : ((Finset.range e).filter fun j => x ∈ (embJH j).verts).card ≤ e :=
    le_trans (Finset.card_filter_le _ _) (by simp)
  split_ifs <;> omega

theorem lenPrefix_succ (embJH : ℕ → Walk) (e : ℕ) :
    lenPrefix embJH (e + 1) = max (lenPrefix embJH e) (embJH e).edges.length := by
  unfold lenPrefix
  rw [Finset.range_add_one, Finset.fold_insert (by simp), max_comm]

def embStatsInv1 (jAddr embJHAddr h : ℕ) (J H' : Graph) (mem : ℕ → ℕ)
    (e : ℕ) (st : State) : Prop :=
  st.regs 0 = jAddr ∧ st.regs 1 = embJHAddr ∧ st.regs 2 = H'.n ∧ st.regs 3 = h ∧
  st.regs 4 = J.n ∧ st.regs 5 = J.m ∧
  st.regs 6 = h + 3 ∧ st.regs 7 = h + 3 + J.n ∧ st.regs 8 = h + 3 + J.n + H'.n ∧
  st.regs 9 = (Finset.range J.n).fold max 0 (degPrefix J e) ∧
  st.regs 10 = 0 ∧ st.regs 11 = 0 ∧ st.regs 12 = e ∧
  e ≤ J.m ∧
  (∀ x < J.n, st.mem (h + 3 + x) = degPrefix J e x) ∧
  AgreeOutside st.mem mem (h + 3) (h + 3 + J.n) ∧
  ZeroFrom st.mem (h + 3 + J.n)

def embStatsInnerInv (jAddr embJHAddr h e ptr : ℕ) (J H' : Graph)
    (embJH : ℕ → Walk) (mem mem_base : ℕ → ℕ) (t : ℕ) (s : State) : Prop :=
  s.regs 0 = jAddr ∧ s.regs 1 = embJHAddr ∧ s.regs 2 = H'.n ∧ s.regs 3 = h ∧
  s.regs 4 = J.n ∧ s.regs 5 = J.m ∧
  s.regs 6 = h + 3 ∧ s.regs 7 = h + 3 + J.n ∧ s.regs 8 = h + 3 + J.n + H'.n ∧
  s.regs 9 = maxDeg J ∧ s.regs 10 = lenPrefix embJH (e + 1) ∧
  s.regs 11 = ((Finset.range H'.n).fold max 0 fun x => vcPrefix embJH e t x) ∧
  s.regs 12 = e ∧ s.regs 13 = ptr ∧ s.regs 14 = (embJH e).verts.length ∧ s.regs 16 = t ∧
  t ≤ (embJH e).verts.length ∧
  (∀ x < H'.n, s.mem (h + 3 + J.n + x) = vcPrefix embJH e t x) ∧
  (∀ x < H'.n, (s.mem (h + 3 + J.n + H'.n + x) = e + 1 ↔ ∃ s0 < t, (embJH e).verts.getD s0 0 = x)) ∧
  (∀ x < H'.n, s.mem (h + 3 + J.n + H'.n + x) ≤ e + 1) ∧
  AgreeOutside s.mem mem (h + 3) (h + 3 + J.n + 2 * H'.n) ∧
  AgreeOutside s.mem mem_base (h + 3 + J.n) (h + 3 + J.n + 2 * H'.n) ∧
  ZeroFrom s.mem (h + 3 + J.n + 2 * H'.n)

def embStatsInv2 (jAddr embJHAddr h : ℕ) (J H' : Graph) (embJH : ℕ → Walk)
    (mem : ℕ → ℕ) (e : ℕ) (st : State) : Prop :=
  st.regs 0 = jAddr ∧ st.regs 1 = embJHAddr ∧ st.regs 2 = H'.n ∧ st.regs 3 = h ∧
  st.regs 4 = J.n ∧ st.regs 5 = J.m ∧
  st.regs 6 = h + 3 ∧ st.regs 7 = h + 3 + J.n ∧ st.regs 8 = h + 3 + J.n + H'.n ∧
  st.regs 9 = maxDeg J ∧ st.regs 10 = lenPrefix embJH e ∧
  st.regs 11 = ((Finset.range H'.n).fold max 0 fun x => vcPrefix embJH e 0 x) ∧
  st.regs 12 = e ∧
  e ≤ J.m ∧
  (∀ x < H'.n, st.mem (h + 3 + J.n + x) = vcPrefix embJH e 0 x) ∧
  (∀ x < H'.n, st.mem (h + 3 + J.n + H'.n + x) ≤ e) ∧
  AgreeOutside st.mem mem (h + 3) (h + 3 + J.n + 2 * H'.n) ∧
  ZeroFrom st.mem (h + 3 + J.n + 2 * H'.n)

theorem embJHStats_loop1_triple {w : ℕ} {p : Program}
    (jAddr embJHAddr h : ℕ) (J H' : Graph) (mem : ℕ → ℕ)
    (hG : GraphAt mem jAddr J) (hJvalid : J.IsValid) (hw1 : 1 < 2 ^ w)
    (hjAddr_w : jAddr < 2 ^ w) (hjh : jAddr + (2 + 2 * J.m) ≤ h)
    (_hHn_w : H'.n < 2 ^ w) (hm2w : 2 * J.m + 2 < 2 ^ w)
    (hh_w : h + 3 + J.n + 2 * H'.n < 2 ^ w) (hz : ZeroFrom mem h) :
    Triple w p
      (fun st =>
        st.regs 0 = jAddr ∧ st.regs 1 = embJHAddr ∧ st.regs 2 = H'.n ∧ st.regs 3 = h ∧
        st.regs 4 = J.n ∧ st.regs 5 = J.m ∧
        st.regs 6 = h + 3 ∧ st.regs 7 = h + 3 + J.n ∧ st.regs 8 = h + 3 + J.n + H'.n ∧
        st.regs 9 = 0 ∧ st.regs 10 = 0 ∧ st.regs 11 = 0 ∧ st.mem = mem)
      (forRange 12 (.const 0) (.reg 5) (
        .assign 13 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 12))))) ;;
        .assign 14 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 12))))) ;;
        .assign 15 (.bin .add (.load (.bin .add (.reg 6) (.reg 13))) (.const 1)) ;;
        .store (.bin .add (.reg 6) (.reg 13)) (.reg 15) ;;
        .cond (.bin .lt (.reg 9) (.reg 15)) (.assign 9 (.reg 15)) (.assign 17 (.const 0)) ;;
        .assign 15 (.bin .add (.load (.bin .add (.reg 6) (.reg 14))) (.const 1)) ;;
        .store (.bin .add (.reg 6) (.reg 14)) (.reg 15) ;;
        .cond (.bin .lt (.reg 9) (.reg 15)) (.assign 9 (.reg 15)) (.assign 17 (.const 0))
      ))
      (normalPost (embStatsInv1 jAddr embJHAddr h J H' mem J.m))
      (fun _ => J.m * (115 + (Expr.reg 5).size + 8) + ((Expr.const 0).size + (Expr.reg 5).size + 5)) := by
  let degBase := h + 3
  let vcBase := h + 3 + J.n
  have hw0 : 0 < 2 ^ w := Nat.zero_lt_of_lt hw1
  have hmJ_w : J.m < 2 ^ w := by omega
  have hdegBase_w : degBase < 2 ^ w := by omega
  refine Triple.forRange_const (p := p) (w := w) (r := 12) (lo := .const 0) (hi := .reg 5)
    (Inv := embStatsInv1 jAddr embJHAddr h J H' mem) 115 0 J.m (Nat.zero_le _) hw1 (fun _ => hmJ_w)
    (fun st hP => by
      rcases hP with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, hmem⟩
      refine ⟨Expr.eval_const hw0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, ?_, r10, r11,
        by simp [Function.update_self], Nat.zero_le _, ?_, ?_, ?_⟩⟩
      · dsimp only; rw [Function.update_of_ne (by decide : (9 : ℕ) ≠ 12), r9]
        unfold degPrefix; simp [Finset.fold_const]
      · intro x _; rw [hmem]; unfold degPrefix; simp; exact hz _ (by omega)
      · rw [hmem]; exact agreeOutside_refl _ _ _
      · rw [hmem]; exact fun x hx => hz x (by omega))
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => ev_reg h.2.2.2.2.2.1 hmJ_w) ?_
  intro e _ he st ω hInv
  rcases hInv with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, hem, hdeg, hag, hzv⟩
  set u := (J.edges.getD e (0, 0)).1
  set v := (J.edges.getD e (0, 0)).2
  have he_in_edges : J.edges.getD e (0, 0) ∈ J.edges := by
    rw [List.getD_eq_getElem _ _ he]; exact List.getElem_mem _
  obtain ⟨hu_n, hv_n⟩ := hJvalid _ he_in_edges
  have he_w : e < 2 ^ w := by omega
  have h2e_w : 2 * e < 2 ^ w := by omega
  have h2e2_w : 2 + 2 * e < 2 ^ w := by omega
  have h2e3_w : 3 + 2 * e < 2 ^ w := by omega
  have ha_u_w : jAddr + (2 + 2 * e) < 2 ^ w := by omega
  have ha_v_w : jAddr + (3 + 2 * e) < 2 ^ w := by omega
  have hG_st : GraphAt st.mem jAddr J := graphAt_of_agreeOutside hG hag (Or.inl (by omega))
  have hu_mem : st.mem (jAddr + (2 + 2 * e)) = u := graphAt_edge_fst_getD hG_st he
  have hv_mem : st.mem (jAddr + (3 + 2 * e)) = v := graphAt_edge_snd_getD hG_st he
  have hu_w : u < 2 ^ w := by omega
  have hv_w : v < 2 ^ w := by omega
  have hdu_le : degPrefix J e u ≤ 2 * e := degPrefix_le J e u
  have hdu1_w : degPrefix J e u + 1 < 2 ^ w := by omega
  have hdu_st : st.mem (degBase + u) = degPrefix J e u := hdeg u hu_n
  have hadr_du : degBase + u < 2 ^ w := by omega
  have hadr_dv : degBase + v < 2 ^ w := by omega
  have hev_u : (Expr.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 12))))).eval w st = some u :=
    ev_load (ev_add (ev_reg r0 hjAddr_w) (ev_add (ev_const (by omega))
      (ev_mul (ev_const (by omega)) (ev_reg r12 he_w) h2e_w) h2e2_w) ha_u_w) hu_mem hu_w
  let st_u : State := ⟨st.mem, Function.update st.regs 13 u, st.pos⟩
  have hev_v : (Expr.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 12))))).eval w st_u = some v :=
    ev_load (ev_add (ev_reg (by simp [st_u, r0]) hjAddr_w) (ev_add (ev_const (by omega))
      (ev_mul (ev_const (by omega)) (ev_reg (by simp [st_u, r12]) he_w) h2e_w) h2e3_w) ha_v_w) hv_mem hv_w
  let st_uv : State := ⟨st.mem, Function.update st_u.regs 14 v, st.pos⟩
  have hr6_uv : st_uv.regs 6 = degBase := by simp [st_uv, st_u, r6, degBase]
  have hr13_uv : st_uv.regs 13 = u := by simp [st_uv, st_u]
  have hev_d1 : (Expr.bin .add (.load (.bin .add (.reg 6) (.reg 13))) (.const 1)).eval w st_uv =
      some (degPrefix J e u + 1) :=
    ev_add (ev_load (ev_add (ev_reg hr6_uv hdegBase_w) (ev_reg hr13_uv hu_w) hadr_du)
      hdu_st (by omega)) (ev_const hw1) hdu1_w
  let regsA := Function.update st_uv.regs 15 (degPrefix J e u + 1)
  let st_a1 : State := ⟨st.mem, regsA, st.pos⟩
  have ha_du : (Expr.bin .add (.reg 6) (.reg 13)).eval w st_a1 = some (degBase + u) :=
    ev_add (ev_reg (by simp [st_a1, regsA, hr6_uv]) hdegBase_w)
      (ev_reg (by simp [st_a1, regsA, hr13_uv]) hu_w) hadr_du
  let mem1 := Function.update st.mem (degBase + u) (degPrefix J e u + 1)
  let st_m1 : State := ⟨mem1, regsA, st.pos⟩
  let f1 : ℕ → ℕ := fun x => if x = u then degPrefix J e x + 1 else degPrefix J e x
  have hf1_eq : ∀ x < J.n, mem1 (degBase + x) = f1 x := by
    intro x hx
    dsimp only [mem1, f1]
    by_cases hxu : x = u
    · subst hxu; simp [Function.update_self]
    · rw [Function.update_of_ne (by omega : degBase + x ≠ degBase + u)]
      simpa [degBase, hxu] using hdeg x hx
  have hmax1 : (Finset.range J.n).fold max 0 f1 = max (st.regs 9) (degPrefix J e u + 1) := by
    rw [r9]; exact fold_max_update_add_one J.n (degPrefix J e) u hu_n
  have hr9_m1 : st_m1.regs 9 = st.regs 9 := by simp [st_m1, regsA, st_uv, st_u]
  have hr15_m1 : st_m1.regs 15 = degPrefix J e u + 1 := by simp [st_m1, regsA]
  have hr9_w : st.regs 9 < 2 ^ w := by
    have hle : st.regs 9 ≤ 2 * e := by
      rw [r9, Finset.fold_max_le]; exact ⟨Nat.zero_le _, fun x _ => degPrefix_le J e x⟩
    omega
  apply runs_start_le
  refine runs_seq_assign_le hev_u ?_
  refine runs_seq_assign_le hev_v ?_
  refine runs_seq_assign_le hev_d1 ?_
  refine runs_seq_store_le ha_du (ev_reg hr15_m1 hdu1_w) ?_
  have hcond1_res :
      ∃ st1 c1,
        Runs w p ω
          (.cond (.bin .lt (.reg 9) (.reg 15)) (.assign 9 (.reg 15)) (.assign 17 (.const 0)))
          st_m1 .normal st1 c1 ∧
        c1 ≤ 12 ∧ st1.pos = st.pos ∧ st1.mem = mem1 ∧
        st1.regs 0 = jAddr ∧ st1.regs 1 = embJHAddr ∧ st1.regs 2 = H'.n ∧
        st1.regs 3 = h ∧ st1.regs 4 = J.n ∧ st1.regs 5 = J.m ∧
        st1.regs 6 = degBase ∧ st1.regs 7 = vcBase ∧ st1.regs 8 = vcBase + H'.n ∧
        st1.regs 9 = (Finset.range J.n).fold max 0 f1 ∧
        st1.regs 10 = 0 ∧ st1.regs 11 = 0 ∧ st1.regs 12 = e ∧
        st1.regs 13 = u ∧ st1.regs 14 = v := by
    by_cases hlt : st.regs 9 < degPrefix J e u + 1
    · have hev : (Expr.bin .lt (.reg 9) (.reg 15)).eval w st_m1 = some 1 :=
        ev_lt_t (ev_reg hr9_m1 hr9_w) (ev_reg hr15_m1 hdu1_w) hlt hw1
      refine ⟨⟨mem1, Function.update regsA 9 (degPrefix J e u + 1), st.pos⟩, _,
        runs_cond_iff.mpr ⟨1, _, hev,
          runs_assign_iff.mpr ⟨degPrefix J e u + 1, ev_reg hr15_m1 hdu1_w, rfl, rfl, rfl⟩, rfl⟩,
        by norm_num [Expr.size], rfl, rfl,
        by simp [regsA, st_uv, st_u, r0], by simp [regsA, st_uv, st_u, r1],
        by simp [regsA, st_uv, st_u, r2], by simp [regsA, st_uv, st_u, r3],
        by simp [regsA, st_uv, st_u, r4], by simp [regsA, st_uv, st_u, r5],
        by simp [regsA, st_uv, st_u, r6, degBase], by simp [regsA, st_uv, st_u, r7, vcBase],
        by simp [regsA, st_uv, st_u, r8, vcBase, Nat.add_assoc], ?_,
        by simp [regsA, st_uv, st_u, r10], by simp [regsA, st_uv, st_u, r11],
        by simp [regsA, st_uv, st_u, r12], by simp [regsA, st_uv, st_u], by simp [regsA, st_uv]⟩
      rw [hmax1, max_eq_right (le_of_lt hlt)]; simp [Function.update_self]
    · have hev : (Expr.bin .lt (.reg 9) (.reg 15)).eval w st_m1 = some 0 :=
        ev_lt_f (ev_reg hr9_m1 hr9_w) (ev_reg hr15_m1 hdu1_w) (by omega) hw1
      refine ⟨⟨mem1, Function.update regsA 17 0, st.pos⟩, _,
        runs_cond_iff.mpr ⟨0, _, hev,
          runs_assign_iff.mpr ⟨0, ev_const hw0, rfl, rfl, rfl⟩, rfl⟩,
        by norm_num [Expr.size], rfl, rfl,
        by simp [regsA, st_uv, st_u, r0], by simp [regsA, st_uv, st_u, r1],
        by simp [regsA, st_uv, st_u, r2], by simp [regsA, st_uv, st_u, r3],
        by simp [regsA, st_uv, st_u, r4], by simp [regsA, st_uv, st_u, r5],
        by simp [regsA, st_uv, st_u, r6, degBase], by simp [regsA, st_uv, st_u, r7, vcBase],
        by simp [regsA, st_uv, st_u, r8, vcBase, Nat.add_assoc], ?_,
        by simp [regsA, st_uv, st_u, r10], by simp [regsA, st_uv, st_u, r11],
        by simp [regsA, st_uv, st_u, r12], by simp [regsA, st_uv, st_u], by simp [regsA, st_uv]⟩
      rw [hmax1, max_eq_left (by omega)]
      simp only [Function.update_of_ne (by decide : (9 : ℕ) ≠ 17)]
      exact hr9_m1
  rcases hcond1_res with ⟨st1, c1, hrun1, hc1, hp1, hm1, c0, c1r, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩
  have hf1_le : f1 v + 1 ≤ 2 * (e + 1) := by
    have hdv_le : degPrefix J e v ≤ 2 * e := degPrefix_le J e v
    by_cases huv : v = u <;> simp [f1, huv] <;> omega
  have hf1_v_w : f1 v + 1 < 2 ^ w := by omega
  have hload_fv : st1.mem (degBase + v) = f1 v := by rw [hm1]; exact hf1_eq v hv_n
  let f2 : ℕ → ℕ := fun x => if x = v then f1 x + 1 else f1 x
  have hf2_eq_deg : ∀ x, f2 x = degPrefix J (e + 1) x := by
    intro x; rw [degPrefix_succ]
    have hu' : (J.edges.getD e (0, 0)).1 = u := rfl
    have hv' : (J.edges.getD e (0, 0)).2 = v := rfl
    rw [hu', hv']
    change (if x = v then (if x = u then degPrefix J e x + 1 else degPrefix J e x) + 1
      else if x = u then degPrefix J e x + 1 else degPrefix J e x) = _
    by_cases hxu : u = x <;> by_cases hxv : v = x <;>
      simp [hxu, hxv, Ne.symm]
  have hfold_f2 : (Finset.range J.n).fold max 0 f2 = (Finset.range J.n).fold max 0 (degPrefix J (e + 1)) := by
    congr 1; ext x; exact hf2_eq_deg x
  have hmax2 : (Finset.range J.n).fold max 0 (degPrefix J (e + 1)) = max (st1.regs 9) (f1 v + 1) := by
    rw [← hfold_f2]
    change (Finset.range J.n).fold max 0 (fun x => if x = v then f1 x + 1 else f1 x) = _
    rw [fold_max_update_add_one J.n f1 v hv_n, ← c9]
  let mem2 := Function.update st1.mem (degBase + v) (f1 v + 1)
  have hag_step : AgreeOutside mem2 st.mem degBase vcBase := by
    have ha1 : AgreeOutside st1.mem st.mem degBase vcBase := by
      rw [hm1]; exact agreeOutside_update (lo := degBase) (hi := vcBase) (by omega) (by omega)
    exact agreeOutside_trans (agreeOutside_update (lo := degBase) (hi := vcBase) (by omega) (by omega))
      ha1 le_rfl le_rfl
  have hag_all : AgreeOutside mem2 mem degBase vcBase := agreeOutside_trans hag_step hag le_rfl le_rfl
  have hmem2_deg : ∀ x < J.n, mem2 (degBase + x) = degPrefix J (e + 1) x := by
    intro x hx; rw [← hf2_eq_deg x]
    by_cases hxv : x = v
    · subst hxv; simp [mem2, f2, Function.update_self]
    · simp only [mem2, f2, hxv, ↓reduceIte]
      rw [Function.update_of_ne (by omega : degBase + x ≠ degBase + v), hm1]; exact hf1_eq x hx
  have hz_next : ZeroFrom mem2 vcBase :=
    zeroFrom_of_agreeOutside hzv hag_step le_rfl
  have hev_d2 : (Expr.bin .add (.load (.bin .add (.reg 6) (.reg 14))) (.const 1)).eval w st1 =
      some (f1 v + 1) :=
    ev_add (ev_load (ev_add (ev_reg c6 hdegBase_w) (ev_reg c14 hv_w) hadr_dv)
      hload_fv (by omega)) (ev_const hw1) hf1_v_w
  let st1a : State := ⟨st1.mem, Function.update st1.regs 15 (f1 v + 1), st1.pos⟩
  have ha_dv2 : (Expr.bin .add (.reg 6) (.reg 14)).eval w st1a = some (degBase + v) :=
    ev_add (ev_reg (by simp [st1a, c6]) hdegBase_w) (ev_reg (by simp [st1a, c14]) hv_w) hadr_dv
  let st1b : State := ⟨mem2, st1a.regs, st1.pos⟩
  have hc9_w : st1.regs 9 < 2 ^ w := by
    have hle : st1.regs 9 ≤ 2 * (e + 1) := by
      rw [c9, Finset.fold_max_le]; refine ⟨Nat.zero_le _, fun x _ => ?_⟩
      by_cases hxu : x = u <;> simp [f1, hxu] <;> (have := degPrefix_le J e x; omega)
    omega
  have htail_res :
      ∃ st2 c2,
        Runs w p ω
          (.assign 15 (.bin .add (.load (.bin .add (.reg 6) (.reg 14))) (.const 1)) ;;
           .store (.bin .add (.reg 6) (.reg 14)) (.reg 15) ;;
           .cond (.bin .lt (.reg 9) (.reg 15)) (.assign 9 (.reg 15)) (.assign 17 (.const 0)))
          st1 .normal st2 c2 ∧ c2 ≤ 35 ∧
        (embStatsInv1 jAddr embJHAddr h J H' mem (e + 1)
          { st2 with regs := Function.update st2.regs 12 (e + 1) } ∧ st2.regs 12 = e) := by
    by_cases hlt2 : st1.regs 9 < f1 v + 1
    · have hev2 : (Expr.bin .lt (.reg 9) (.reg 15)).eval w st1b = some 1 :=
        ev_lt_t (ev_reg (by simp [st1b, st1a]) hc9_w) (ev_reg (by simp [st1b, st1a]) hf1_v_w) hlt2 hw1
      let st2 : State := ⟨mem2, Function.update st1b.regs 9 (f1 v + 1), st1.pos⟩
      have hrun2 :
          Runs w p ω
            (.assign 15 (.bin .add (.load (.bin .add (.reg 6) (.reg 14))) (.const 1)) ;;
             .store (.bin .add (.reg 6) (.reg 14)) (.reg 15) ;;
             .cond (.bin .lt (.reg 9) (.reg 15)) (.assign 9 (.reg 15)) (.assign 17 (.const 0)))
            st1 .normal st2 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st1a, _, _,
          runs_assign_iff.mpr ⟨f1 v + 1, hev_d2, rfl, rfl, rfl⟩,
          runs_seq_iff.mpr (Or.inr ⟨st1b, _, _,
            runs_store_iff.mpr ⟨degBase + v, f1 v + 1, ha_dv2, ev_reg (by simp [st1a]) hf1_v_w, rfl, rfl, rfl⟩,
            runs_cond_iff.mpr ⟨1, _, hev2,
              runs_assign_iff.mpr ⟨f1 v + 1, ev_reg (by simp [st1b, st1a]) hf1_v_w, rfl, rfl, rfl⟩, rfl⟩,
            rfl⟩),
          rfl⟩)
      refine ⟨st2, _, hrun2, by norm_num [Expr.size], ?_⟩
      · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hmem2_deg, hag_all, hz_next⟩, ?_⟩
        all_goals dsimp only [st2, st1b, st1a]
        · simp [c0]
        · simp [c1r]
        · simp [c2]
        · simp [c3]
        · simp [c4]
        · simp [c5]
        · simp [c6, degBase]
        · simp [c7, vcBase]
        · simp [c8, vcBase, Nat.add_assoc]
        · rw [hmax2, max_eq_right (le_of_lt hlt2)]; simp [Function.update_self]
        · simp [c10]
        · simp [c11]
        · simp [Function.update_self]
        · simp [c12]
    · have hev2 : (Expr.bin .lt (.reg 9) (.reg 15)).eval w st1b = some 0 :=
        ev_lt_f (ev_reg (by simp [st1b, st1a]) hc9_w) (ev_reg (by simp [st1b, st1a]) hf1_v_w) (by omega) hw1
      let st2 : State := ⟨mem2, Function.update st1b.regs 17 0, st1.pos⟩
      have hrun2 :
          Runs w p ω
            (.assign 15 (.bin .add (.load (.bin .add (.reg 6) (.reg 14))) (.const 1)) ;;
             .store (.bin .add (.reg 6) (.reg 14)) (.reg 15) ;;
             .cond (.bin .lt (.reg 9) (.reg 15)) (.assign 9 (.reg 15)) (.assign 17 (.const 0)))
            st1 .normal st2 _ :=
        runs_seq_iff.mpr (Or.inr ⟨st1a, _, _,
          runs_assign_iff.mpr ⟨f1 v + 1, hev_d2, rfl, rfl, rfl⟩,
          runs_seq_iff.mpr (Or.inr ⟨st1b, _, _,
            runs_store_iff.mpr ⟨degBase + v, f1 v + 1, ha_dv2, ev_reg (by simp [st1a]) hf1_v_w, rfl, rfl, rfl⟩,
            runs_cond_iff.mpr ⟨0, _, hev2,
              runs_assign_iff.mpr ⟨0, ev_const hw0, rfl, rfl, rfl⟩, rfl⟩,
            rfl⟩),
          rfl⟩)
      refine ⟨st2, _, hrun2, by norm_num [Expr.size], ?_⟩
      · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hmem2_deg, hag_all, hz_next⟩, ?_⟩
        all_goals dsimp only [st2, st1b, st1a]
        · simp [c0]
        · simp [c1r]
        · simp [c2]
        · simp [c3]
        · simp [c4]
        · simp [c5]
        · simp [c6, degBase]
        · simp [c7, vcBase]
        · simp [c8, vcBase, Nat.add_assoc]
        · rw [hmax2, max_eq_left (by omega)]
          simp only [Function.update_of_ne (by decide : (9 : ℕ) ≠ 12),
            Function.update_of_ne (by decide : (9 : ℕ) ≠ 17),
            Function.update_of_ne (by decide : (9 : ℕ) ≠ 15)]
        · simp [c10]
        · simp [c11]
        · simp [Function.update_self]
        · simp [c12]
  rcases htail_res with ⟨st2, c2, hrun2, hc2, hq2⟩
  refine ⟨.normal, st2, c1 + c2 + 1,
    runs_seq_iff.mpr (Or.inr ⟨st1, c1, c2, hrun1, hrun2, rfl⟩), hq2,
    by simp only [Expr.size]; omega⟩


end MinCostFlow.Spanner
