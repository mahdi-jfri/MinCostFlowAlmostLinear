module

public import WordRAM.Logic
public import WordRAM.Tactic
public import Mathlib.Data.List.Basic

/-!
# Grouping items by a key (a counting sort)

Several steps of the program group items by a small key: the pairs of the input by their ends, the
arcs of a cluster by their tails. `csrB` does this by counting. The items are `0, …, M - 1`, item
`i` has key `f i = mem (TL + i) < NN`. At the end, `OFF + u` holds the number of items with key
below `u` (`offOf`), and the cells `ORD + offOf u, …` hold the items with key `u`, in increasing
order (`grp`). The cost is linear in `M + NN` (`csrB_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The items below `M` with key `u`, in increasing order. -/
def grp (f : ℕ → ℕ) (M u : ℕ) : List ℕ := (List.range M).filter (fun i => f i = u)

/-- The number of items below `M` with key below `u`. -/
def offOf (f : ℕ → ℕ) (M u : ℕ) : ℕ := ((List.range M).filter (fun i => f i < u)).length

section math

variable (f : ℕ → ℕ)

theorem grp_succ (M u : ℕ) : grp f (M + 1) u = grp f M u ++ (if f M = u then [M] else []) := by
  unfold grp
  rw [List.range_succ, List.filter_append]
  congr 1
  by_cases h : f M = u <;> simp [h]

theorem offOf_succ (M u : ℕ) : offOf f M (u + 1) = offOf f M u + (grp f M u).length := by
  unfold offOf grp
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.range_succ, List.filter_append, List.filter_append, List.filter_append,
      List.length_append, List.length_append, List.length_append, ih]
    simp only [List.filter_cons, List.filter_nil]
    split_ifs with ha hb hc hc' hb' hc'' <;>
      simp only [List.length_cons, List.length_nil, decide_eq_true_eq,
        decide_eq_false_iff_not] at * <;> omega

theorem offOf_mono {M u v : ℕ} (h : u ≤ v) : offOf f M u ≤ offOf f M v := by
  induction v with
  | zero => have : u = 0 := by omega
            subst this; exact le_rfl
  | succ v ih =>
    rcases Nat.lt_or_ge u (v + 1) with hl | hl
    · rw [offOf_succ]; have := ih (by omega); omega
    · have : u = v + 1 := by omega
      subst this; exact le_rfl

theorem offOf_all {M NN : ℕ} (h : ∀ i < M, f i < NN) : offOf f M NN = M := by
  unfold offOf
  rw [List.filter_eq_self.mpr fun i hi => by simpa using h i (List.mem_range.mp hi)]
  simp

theorem offOf_zero (M : ℕ) : offOf f M 0 = 0 := by simp [offOf]

theorem grp_length_succ (M u : ℕ) :
    (grp f (M + 1) u).length = (grp f M u).length + (if f M = u then 1 else 0) := by
  rw [grp_succ]; split_ifs <;> simp

/-- The ranges of two different keys do not meet. -/
theorem offOf_disj {M u v j k : ℕ} (huv : u ≠ v) (hj : j < (grp f M u).length)
    (hk : k < (grp f M v).length) : offOf f M u + j ≠ offOf f M v + k := by
  rcases Nat.lt_or_gt_of_ne huv with h | h
  · have := offOf_mono f (M := M) (show u + 1 ≤ v by omega)
    rw [offOf_succ] at this
    omega
  · have := offOf_mono f (M := M) (show v + 1 ≤ u by omega)
    rw [offOf_succ] at this
    omega

theorem grp_length_le (M M' u : ℕ) (h : M ≤ M') : (grp f M u).length ≤ (grp f M' u).length := by
  induction M' with
  | zero => have : M = 0 := by omega
            subst this; exact le_rfl
  | succ M' ih =>
    rcases Nat.lt_or_ge M (M' + 1) with hl | hl
    · rw [grp_length_succ]; have := ih (by omega); omega
    · have : M = M' + 1 := by omega
      subst this; exact le_rfl

end math

/-- `csrB`: `args = [TL, M, NN, OFF, CNT, ORD]`. -/
def csrB : Stmt :=
  .seq (forRange 6 (.const 0) (.reg 2) (.store (.bin .add (.reg 4) (.reg 6)) (.const 0)))
  (.seq (forRange 6 (.const 0) (.reg 1)
      (.seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 6))))
        (.store (.bin .add (.reg 4) (.reg 7))
          (.bin .add (.load (.bin .add (.reg 4) (.reg 7))) (.const 1)))))
  (.seq (.store (.reg 3) (.const 0))
  (.seq (forRange 6 (.const 0) (.reg 2)
      (.seq (.assign 7 (.load (.bin .add (.reg 3) (.reg 6))))
      (.seq (.store (.bin .add (.bin .add (.reg 3) (.reg 6)) (.const 1))
          (.bin .add (.reg 7) (.load (.bin .add (.reg 4) (.reg 6)))))
        (.store (.bin .add (.reg 4) (.reg 6)) (.reg 7)))))
  (.seq (forRange 6 (.const 0) (.reg 1)
      (.seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 6))))
      (.seq (.assign 8 (.load (.bin .add (.reg 4) (.reg 7))))
      (.seq (.store (.bin .add (.reg 5) (.reg 8)) (.reg 6))
        (.store (.bin .add (.reg 4) (.reg 7)) (.bin .add (.reg 8) (.const 1)))))))
  (.ret (.const 0))))))

theorem csrB_noRand : csrB.NoRand := by simp [csrB, forRange, forUp, Stmt.NoRand]

/-- The cells that `csrB` may change. -/
def csrOut (OFF CNT ORD NN M a : ℕ) : Prop :=
  (OFF ≤ a ∧ a ≤ OFF + NN) ∨ (CNT ≤ a ∧ a < CNT + NN) ∨ (ORD ≤ a ∧ a < ORD + M)

/-- The precondition of `csrB`. -/
def csrPre (w : ℕ) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ TL M NN OFF CNT ORD, args = [TL, M, NN, OFF, CNT, ORD] ∧
    (∀ i < M, mem (TL + i) < NN) ∧
    TL + M ≤ OFF ∧ OFF + NN + 1 ≤ CNT ∧ CNT + NN ≤ ORD ∧ ORD + M + NN + 2 < 2 ^ w

/-- The contract of `csrB`. -/
def csrC (w : ℕ) : Contract where
  pre := csrPre w
  post args mem _ mem' :=
    let TL := args.getD 0 0
    let M := args.getD 1 0
    let NN := args.getD 2 0
    let OFF := args.getD 3 0
    let CNT := args.getD 4 0
    let ORD := args.getD 5 0
    let f := fun i => mem (TL + i)
    (∀ u ≤ NN, mem' (OFF + u) = offOf f M u) ∧
    (∀ u < NN, ∀ j < (grp f M u).length, mem' (ORD + offOf f M u + j) = (grp f M u).getD j 0) ∧
    ∀ a, ¬ csrOut OFF CNT ORD NN M a → mem' a = mem a
  cost args _ := 100 * (args.getD 1 0 + args.getD 2 0 + 1)

theorem csrB_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [csrB]) :
    MeetsContract w p b (csrC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨TL, M, NN, OFF, CNT, ORD, rfl, hTL, h1, h2, h3, hw⟩ := hpre
  have hproc : p.procs[b]? = some csrB := hp 0 (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  set f : ℕ → ℕ := fun i => mem (TL + i) with hf
  -- the registers that never change
  let R : State → Prop := fun st => st.regs 0 = TL ∧ st.regs 1 = M ∧ st.regs 2 = NN ∧
    st.regs 3 = OFF ∧ st.regs 4 = CNT ∧ st.regs 5 = ORD
  have hR : ∀ st r v, R st → 6 ≤ r → R { st with regs := Function.update st.regs r v } := by
    intro st r v ⟨a0, a1, a2, a3, a4, a5⟩ hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)
  -- cells outside the output keep their values
  let Fr : (ℕ → ℕ) → Prop := fun M' => ∀ a, ¬ csrOut OFF CNT ORD NN M a → M' a = mem a
  have hTLkeep : ∀ M', Fr M' → ∀ i < M, M' (TL + i) = mem (TL + i) := fun M' h i hi =>
    h _ (by unfold csrOut; omega)
  -- loop A: clear the counters
  let IA : ℕ → State → Prop := fun i st => R st ∧ st.regs 6 = i ∧ Fr st.mem ∧
    (∀ u < i, st.mem (CNT + u) = 0)
  have hA := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.reg 4) (.reg 6)) (.const 0))
    (P := fun st => R st ∧ st.mem = mem) (Inv := IA) 6 0 NN (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun st ⟨hr, hm⟩ => ⟨by eval_expr, hR st 6 0 hr le_rfl, by simp, fun a _ => by simp [hm],
      fun u hu => absurd hu (by omega)⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.2.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h6, hfr, hz⟩ := hI
      obtain ⟨r0, r1, r2, r3, r4, r5⟩ := hr
      refine runs_start_le ?_
      wram_run
      · refine ⟨⟨hR _ 6 _ ⟨r0, r1, r2, r3, r4, r5⟩ le_rfl, by simp, fun a ha => ?_,
          fun u hu => ?_⟩, h6⟩
        · simp only [Function.update_apply]
          rw [if_neg (by unfold csrOut at ha; omega)]; exact hfr a ha
        · simp only [Function.update_apply]
          by_cases hui : u = i
          · subst hui; simp
          · rw [if_neg (by omega)]; exact hz u (by omega)
      · wram_cost)
  -- loop B: count the keys
  let IB : ℕ → State → Prop := fun i st => R st ∧ st.regs 6 = i ∧ Fr st.mem ∧
    (∀ u < NN, st.mem (CNT + u) = (grp f i u).length)
  have hB := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 1)
    (body := .seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 6))))
        (.store (.bin .add (.reg 4) (.reg 7))
          (.bin .add (.load (.bin .add (.reg 4) (.reg 7))) (.const 1))))
    (P := IA NN) (Inv := IB) 30 0 M (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hI => by
      obtain ⟨hr, -, hfr, hz⟩ := hI
      exact ⟨by eval_expr, hR st 6 0 hr le_rfl, by simp, hfr, fun u hu => by
        simpa [grp] using hz u hu⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h6, hfr, hc⟩ := hI
      obtain ⟨r0, r1, r2, r3, r4, r5⟩ := hr
      have hfi : st.mem (TL + i) = f i := hTLkeep _ hfr i hi
      have hfiN : f i < NN := hTL i hi
      have hcnt := hc (f i) hfiN
      have hle : (grp f i (f i)).length ≤ i := by
        have := List.length_filter_le (fun j => decide (f j = f i)) (List.range i)
        simpa [grp] using this
      have hb : st.mem (st.regs 4 + st.mem (TL + i)) + 1 < 2 ^ w := by
        rw [r4, hfi, hcnt]; omega
      refine runs_start_le ?_
      wram_run
      · simp only [r0, r4, h6, hfi, hcnt]
        refine ⟨⟨hR _ 6 _ (hR _ 7 _ ⟨r0, r1, r2, r3, r4, r5⟩ (by omega)) le_rfl, by simp,
          fun a ha => ?_, fun u hu => ?_⟩, by simp [h6]⟩
        · simp only [Function.update_apply]
          rw [if_neg (by unfold csrOut at ha; omega)]; exact hfr a ha
        · simp only [Function.update_apply]
          rw [grp_length_succ]
          by_cases hu' : f i = u
          · subst hu'
            simp
          · rw [if_neg (by omega), if_neg hu', hc u hu]; simp
      · wram_cost)
  -- loop C: prefix sums
  let IC : ℕ → State → Prop := fun u st => R st ∧ st.regs 6 = u ∧ Fr st.mem ∧
    (∀ x ≤ u, st.mem (OFF + x) = offOf f M x) ∧ (∀ x < u, st.mem (CNT + x) = offOf f M x) ∧
    (∀ x, u ≤ x → x < NN → st.mem (CNT + x) = (grp f M x).length)
  have hoffM : ∀ x, offOf f M x ≤ M := fun x => by
    unfold offOf
    have := List.length_filter_le (fun i => decide (f i < x)) (List.range M)
    simpa using this
  have hC := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 2)
    (body := .seq (.assign 7 (.load (.bin .add (.reg 3) (.reg 6))))
      (.seq (.store (.bin .add (.bin .add (.reg 3) (.reg 6)) (.const 1))
          (.bin .add (.reg 7) (.load (.bin .add (.reg 4) (.reg 6)))))
        (.store (.bin .add (.reg 4) (.reg 6)) (.reg 7))))
    (P := fun st => IB M st ∧ st.mem OFF = 0) (Inv := IC) 40 0 NN (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun st ⟨hI, h0⟩ => by
      obtain ⟨hr, -, hfr, hc⟩ := hI
      exact ⟨by eval_expr, hR st 6 0 hr le_rfl, by simp, hfr, fun x hx => by
        have : x = 0 := by omega
        subst this; simpa [offOf_zero] using h0, fun x hx => absurd hx (by omega),
        fun x _ hx => hc x hx⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.2.1; eval_expr)
    (fun u _ hu st ω hI => by
      obtain ⟨hr, h6, hfr, ho, hcl, hch⟩ := hI
      obtain ⟨r0, r1, r2, r3, r4, r5⟩ := hr
      have hou := ho u le_rfl
      have hcu := hch u le_rfl hu
      have hsucc := offOf_succ f M u
      have hb1 := hoffM (u + 1)
      have hb : st.mem (OFF + u) + st.mem (st.regs 4 + st.regs 6) < 2 ^ w := by
        rw [r4, h6, hou, hcu]; omega
      refine runs_start_le ?_
      wram_run
      · simp only [r3, r4, h6, hou, hcu]
        refine ⟨⟨hR _ 6 _ (hR _ 7 _ ⟨r0, r1, r2, r3, r4, r5⟩ (by omega)) le_rfl, by simp,
          fun a ha => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx1 hx2 => ?_⟩, by simp [h6]⟩
        · simp only [Function.update_apply]
          rw [if_neg (by unfold csrOut at ha; omega), if_neg (by unfold csrOut at ha; omega)]
          exact hfr a ha
        · simp only [Function.update_apply]
          rw [if_neg (by omega)]
          by_cases hxu : x = u + 1
          · subst hxu; rw [if_pos (by omega), hsucc]
          · rw [if_neg (by omega)]; exact ho x (by omega)
        · simp only [Function.update_apply]
          by_cases hxu : x = u
          · subst hxu; rw [if_pos rfl]
          · rw [if_neg (by omega), if_neg (by omega)]; exact hcl x (by omega)
        · simp only [Function.update_apply]
          rw [if_neg (by omega), if_neg (by omega)]; exact hch x (by omega) hx2
      · wram_cost)
  -- loop D: place each item at the next free slot of its key
  have hall : offOf f M NN = M := offOf_all f (fun i hi => hTL i hi)
  let ID : ℕ → State → Prop := fun i st => R st ∧ st.regs 6 = i ∧ Fr st.mem ∧
    (∀ x ≤ NN, st.mem (OFF + x) = offOf f M x) ∧
    (∀ u < NN, st.mem (CNT + u) = offOf f M u + (grp f i u).length) ∧
    (∀ u < NN, ∀ j < (grp f i u).length, st.mem (ORD + offOf f M u + j) = (grp f i u).getD j 0)
  have hD := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 1)
    (body := .seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 6))))
      (.seq (.assign 8 (.load (.bin .add (.reg 4) (.reg 7))))
      (.seq (.store (.bin .add (.reg 5) (.reg 8)) (.reg 6))
        (.store (.bin .add (.reg 4) (.reg 7)) (.bin .add (.reg 8) (.const 1))))))
    (P := IC NN) (Inv := ID) 40 0 M (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hI => by
      obtain ⟨hr, -, hfr, ho, hcl, -⟩ := hI
      exact ⟨by eval_expr, hR st 6 0 hr le_rfl, by simp, hfr, ho,
        fun u hu => by simpa [grp] using hcl u hu, fun u _ j hj => by simp [grp] at hj⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h6, hfr, ho, hc, hord⟩ := hI
      obtain ⟨r0, r1, r2, r3, r4, r5⟩ := hr
      have hfi : st.mem (TL + i) = f i := hTLkeep _ hfr i hi
      have hfiN : f i < NN := hTL i hi
      have hcnt := hc (f i) hfiN
      have hlen : (grp f i (f i)).length + 1 ≤ (grp f M (f i)).length := by
        have := grp_length_le f (i + 1) M (f i) (by omega)
        rw [grp_length_succ, if_pos rfl] at this; exact this
      have hsl : offOf f M (f i) + (grp f i (f i)).length < M := by
        have h1 := offOf_mono f (M := M) (show f i + 1 ≤ NN by omega)
        rw [offOf_succ, hall] at h1; omega
      have hb : st.mem (st.regs 4 + st.mem (TL + i)) + 1 < 2 ^ w := by
        rw [r4, hfi, hcnt]; omega
      have hb' : st.regs 5 + st.mem (st.regs 4 + st.mem (TL + i)) < 2 ^ w := by
        rw [r4, r5, hfi, hcnt]; omega
      refine runs_start_le ?_
      wram_run
      · simp only [r4, r5, hfi, hcnt]
        refine ⟨⟨by refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Function.update_apply, *], by simp, fun a ha => ?_, fun x hx => ?_, fun u hu => ?_,
          fun u hu j hj => ?_⟩, by simp [h6]⟩
        · simp only [Function.update_apply]
          rw [if_neg (by unfold csrOut at ha; omega), if_neg (by unfold csrOut at ha; omega)]
          exact hfr a ha
        · simp only [Function.update_apply]
          rw [if_neg (by omega), if_neg (by omega)]; exact ho x hx
        · simp only [Function.update_apply]
          rw [grp_length_succ]
          by_cases hu' : f i = u
          · subst hu'; simp; omega
          · rw [if_neg (by omega), if_neg (by omega), if_neg hu', hc u hu]; rfl
        · simp only [Function.update_apply]
          rw [if_neg (by omega)]
          by_cases hu' : f i = u
          · subst hu'
            rw [grp_succ, if_pos rfl] at hj ⊢
            simp only [List.length_append, List.length_singleton] at hj
            by_cases hjl : j = (grp f i (f i)).length
            · subst hjl; simp [Nat.add_assoc, h6]
            · have hjl' : j < (grp f i (f i)).length := by omega
              rw [if_neg (by omega), List.getD_append _ _ _ _ hjl']
              exact hord _ hu _ hjl'
          · rw [grp_succ, if_neg hu', List.append_nil] at hj ⊢
            have hne := offOf_disj f (M := M) (Ne.symm hu')
              (lt_of_lt_of_le hj (grp_length_le f i M u (by omega))) (show
                (grp f i (f i)).length < (grp f M (f i)).length by omega)
            rw [if_neg (by omega)]
            exact hord u hu j hj
      · wram_cost)
  refine ⟨csrB, hproc, ?_⟩
  dsimp only [csrB]
  refine runs_start_le ?_
  refine runs_seq_triple_le hA ?_ (fun stA hIA => ?_)
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  refine runs_seq_triple_le hB hIA (fun stB hIB => ?_)
  obtain ⟨⟨b0, b1, b2, b3, b4, b5⟩, b6, bfr, bc⟩ := hIB
  wram_step
  refine runs_seq_triple_le hC ⟨⟨⟨b0, b1, b2, b3, b4, b5⟩, b6, fun a ha => ?_, fun u hu => ?_⟩, ?_⟩
    (fun stC hIC => ?_)
  · simp only [Function.update_apply]
    rw [if_neg (by unfold csrOut at ha; omega)]; exact bfr a ha
  · simp only [Function.update_apply]
    rw [if_neg (by omega)]; exact bc u hu
  · simp [b3]
  refine runs_seq_triple_le hD hIC (fun stD hID => ?_)
  obtain ⟨-, -, dfr, dof, -, dord⟩ := hID
  refine runs_ret_le (by eval_expr) ⟨fun u hu => dof u hu, fun u hu j hj => ?_, dfr⟩ ?_
  · simpa [Nat.add_assoc] using dord u hu j hj
  · simp only [csrC, Expr.size, List.getD_cons_succ, List.getD_cons_zero]
    omega

end MinCostFlow.LowStretch
