module

public import MinCostFlow.SparseCore.Program.ReadEmbLoop

/-!
# The operations of the embedding table

This file proves the three operations of the embedding table (`ReadEmb.lean`) and puts them in
one statement, `embBranchAt`:
* the readout (`embReadStmt`) writes `ReadEmbOut` at `h` in `20` steps;
* the update (`embStepStmt`) leaves `v.apply X`, allocates at most `embChangeWords X` cells, and
  costs at most `50 · (embChangeWords X + 1)`;
* the initialization (`embInitStmt`) builds `EmbView.empty.apply X` at `h`, allocates at most
  `eCap + 2 + embChangeWords X` cells, and costs at most `50 · (embChangeWords X + 1)`.
The table needs no potential. The representation is local (`embRep_local`).
-/

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.DynSpanner.Program

public section

/-- The representation depends only on the cells of its footprint. -/
theorem embRep_local (eCap : ℕ) : (embRep eCap).Local := by
  intro r v y mem mem' hag
  refine ⟨fun ⟨hv, h0, h1, hE⟩ => ⟨hv, ?_, ?_, fun e he => ?_⟩, rfl⟩
  · rw [← hag r (Or.inl ⟨le_rfl, by omega⟩)]; exact h0
  · rw [← hag (r + 1) (Or.inl ⟨by omega, by omega⟩)]; exact h1
  · obtain ⟨hlt, hge, ht, hw⟩ := hE e he
    refine ⟨hlt, hge, ?_, ?_⟩
    · rw [← hag _ (Or.inl ⟨by omega, by omega⟩)]; exact ht
    · refine hw.of_agree fun x hx1 hx2 => (hag x (Or.inr ⟨e, hv ▸ he, hx1, ?_⟩)).symm
      simp only [walkWords]
      rw [hv]; omega

/-- The end of a call of the table: the run, the new representation, what it writes, the memory
it allocates, and its cost. -/
@[expose] def EmbCallEnds (eCap w : ℕ) (p : Program) (f : ℕ) (args : List ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) (r : ℕ) (y : EmbConc) (h : ℕ) (v' : EmbView)
    (out : (ℕ → ℕ) → Prop) (space cost : ℕ) : Prop :=
  ∃ body, p.procs[f]? = some body ∧ ∃ o st' c, ∃ y' : EmbConc,
    Runs w p ω body (startState args mem pos) o st' c ∧
    (embRep eCap).rep r v' y' st'.mem ∧ out st'.mem ∧
    h ≤ o.value ∧ o.value ≤ h + space ∧ ZeroFrom st'.mem o.value ∧
    (∀ a < h, ¬ embFoot eCap r y a → st'.mem a = mem a) ∧
    (∀ a, embFoot eCap r y' a → embFoot eCap r y a ∨ (h ≤ a ∧ a < o.value)) ∧
    c ≤ cost

/-- The three operations of the embedding table, with the procedures at `b`, `b + 1`, `b + 2`. -/
structure EmbBranchAt (eCap w : ℕ) (p : Program) (b : ℕ) : Prop where
  read : ∀ (r h : ℕ) (v : EmbView) (y : EmbConc) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
    r < 2 ^ w → h + 2 < 2 ^ w → (embRep eCap).rep r v y mem →
    (∀ a, embFoot eCap r y a → a < h) → ZeroFrom mem h →
    EmbCallEnds eCap w p b [r, h] mem pos ω r y h v (fun mem' => ReadEmbOut mem' h eCap v) 2 20
  step : ∀ (r a h : ℕ) (X : EmbChange) (v : EmbView) (y : EmbConc) (mem : ℕ → ℕ) (pos : ℕ)
      (ω : ℕ → Bool),
    (∀ x ∈ [r, a, X.length, h], x < 2 ^ w) → (embRep eCap).rep r v y mem →
    (∀ x, embFoot eCap r y x → x < h) → ZeroFrom mem h →
    EmbChangeAt mem a X → EmbInputAt mem (embFoot eCap r y) a eCap h X →
    h + embChangeWords X < 2 ^ w →
    EmbCallEnds eCap w p (b + 1) [r, a, X.length, h] mem pos ω r y h (v.apply X) (fun _ => True)
      (embChangeWords X) (50 * (embChangeWords X + 1))
  init : ∀ (a h : ℕ) (X : EmbChange) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
    (∀ x ∈ [eCap, a, X.length, h], x < 2 ^ w) → ZeroFrom mem h →
    EmbChangeAt mem a X → EmbInputAt mem (fun _ => False) a eCap h X →
    h + eCap + 2 + embChangeWords X < 2 ^ w →
    ∃ body, p.procs[b + 2]? = some body ∧ ∃ o st' c, ∃ y : EmbConc,
      Runs w p ω body (startState [eCap, a, X.length, h] mem pos) o st' c ∧
      (embRep eCap).rep h (EmbView.empty.apply X) y st'.mem ∧
      h ≤ o.value ∧ o.value ≤ h + (eCap + 2 + embChangeWords X) ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem a) ∧ (∀ a, embFoot eCap h y a → h ≤ a ∧ a < o.value) ∧
      c ≤ 50 * (embChangeWords X + 1)

private theorem embLoop_sum (X : EmbChange) :
    (X.map fun q => 17 * walkWords q.2 + 80).sum =
      17 * (X.map fun q => walkWords q.2).sum + 80 * X.length := by
  induction X with
  | nil => simp
  | cons x X ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

/-- The loop cost is at most `41` per word of the change list, plus `2`. -/
private theorem embLoop_cost_le (X : EmbChange) :
    (X.map fun q => 17 * walkWords q.2 + 80).sum + X.length * ((Expr.reg 6).size + 1) +
      (Expr.reg 6).size + 1 ≤ 41 * embChangeWords X + 2 := by
  have h := walkWords_sum_le X
  rw [embLoop_sum]
  simp only [Expr.size]
  omega

/-- The readout. -/
theorem embRead_ends {eCap w : ℕ} {p : Program} {f : ℕ} (hp : p.procs[f]? = some embReadStmt)
    {r h : ℕ} {v : EmbView} {y : EmbConc} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hr : r < 2 ^ w) (hh : h + 2 < 2 ^ w) (hrep : (embRep eCap).rep r v y mem)
    (hfoot : ∀ a, embFoot eCap r y a → a < h) (hz : ZeroFrom mem h) :
    EmbCallEnds eCap w p f [r, h] mem pos ω r y h v (fun mem' => ReadEmbOut mem' h eCap v) 2 20 := by
  obtain ⟨hv, h0, h1, hE⟩ := hrep
  have hr1 : r + 1 < h := hfoot _ (Or.inl ⟨by omega, by omega⟩)
  set m' := Function.update (Function.update mem h (r + 2)) (h + 1) eCap with hm'
  have hag : ∀ a, embFoot eCap r y a → mem a = m' a := fun a ha => by
    have := hfoot a ha
    simp only [hm', Function.update_apply, show a ≠ h + 1 by omega, show a ≠ h by omega,
      ite_false]
  have hrep' := ((embRep_local eCap) r v y mem m' hag).1 ⟨hv, h0, h1, hE⟩
  refine ⟨_, hp, ?_⟩
  have hrun : ∃ o st' c, Runs w p ω embReadStmt (startState [r, h] mem pos) o st' c ∧
      (o = .returned (h + 2) ∧ st'.mem = m') ∧ c ≤ 20 := by
    apply runs_start_le
    refine runs_seq_store_le (x := h) (v := r + 2)
      (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := r) (by simp [startState])) h0) ?_
    refine runs_seq_store_le (x := h + 1) (v := eCap)
      (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
        (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := r) (by simp [startState]))
        (Expr.eval_const (by omega)) (by omega)) (by
          simp only [startState, Function.update_apply, show r + 1 ≠ h by omega, ite_false]
          exact h1)) ?_
    refine runs_ret_le (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) ⟨rfl, by simp [hm', startState]⟩ ?_
    simp only [Expr.size]; omega
  obtain ⟨o, st', c, hrun, ⟨rfl, hmem⟩, hc⟩ := hrun
  refine ⟨_, st', c, y, hrun, hmem ▸ hrep', ?_, by simp [Outcome.value],
    by simp [Outcome.value], ?_, ?_, fun a ha => Or.inl ha, hc⟩
  · rw [hmem]
    refine ⟨by simp [hm'], fun e he => ?_⟩
    obtain ⟨hlt, _, ht, hw⟩ := hrep'.2.2.2 e he
    refine ⟨hlt, ?_⟩
    have hmh : m' h = r + 2 := by simp [hm']
    rw [hmh, ht]
    exact hv ▸ hw
  · intro a ha
    simp only [Outcome.value] at ha
    rw [hmem]
    simp only [hm', Function.update_apply, show a ≠ h + 1 by omega, show a ≠ h by omega,
      ite_false]
    exact hz a (by omega)
  · intro a ha hn
    rw [hmem]
    simp only [hm', Function.update_apply, show a ≠ h + 1 by omega, show a ≠ h by omega,
      ite_false]

/-- The table cells and the walks of a representation lie below `h` when its footprint does. -/
private theorem emb_below {eCap r h : ℕ} {y : EmbConc}
    (hfoot : ∀ x, embFoot eCap r y x → x < h) :
    r + 2 + eCap ≤ h ∧ ∀ e ∈ y.view.dom, y.ptr e + walkWords (y.view.emb e) ≤ h := by
  refine ⟨?_, fun e he => ?_⟩
  · have := hfoot (r + 1 + eCap) (Or.inl ⟨by omega, by omega⟩); omega
  · have := hfoot (y.ptr e + walkWords (y.view.emb e) - 1)
      (Or.inr ⟨e, he, by simp only [walkWords]; omega, by simp only [walkWords]; omega⟩)
    omega

/-- The update. -/
theorem embStep_ends {eCap w : ℕ} {p : Program} {f bCopy : ℕ}
    (hp : p.procs[f]? = some (embStepStmt bCopy))
    (hcopy : MeetsContract w p bCopy (copyWordsContract w))
    {r a h : ℕ} {X : EmbChange} {v : EmbView} {y : EmbConc} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool}
    (hargs : ∀ x ∈ [r, a, X.length, h], x < 2 ^ w) (hrep : (embRep eCap).rep r v y mem)
    (hfoot : ∀ x, embFoot eCap r y x → x < h) (hz : ZeroFrom mem h)
    (hX : EmbChangeAt mem a X) (hin : EmbInputAt mem (embFoot eCap r y) a eCap h X)
    (hlt : h + embChangeWords X < 2 ^ w) :
    EmbCallEnds eCap w p f [r, a, X.length, h] mem pos ω r y h (v.apply X) (fun _ => True)
      (embChangeWords X) (50 * (embChangeWords X + 1)) := by
  obtain ⟨hv, h0, h1, hE⟩ := hrep
  subst hv
  obtain ⟨htab, hold⟩ := emb_below hfoot
  have hin' : EmbInputAt mem (fun x => r ≤ x ∧ x < r + 2 + eCap) a eCap h X := by
    obtain ⟨h1', h2', h3'⟩ := hin
    exact ⟨h1', fun i hi hc => h2' i hi (Or.inl hc), fun i hi =>
      ⟨(h3' i hi).1, (h3' i hi).2.1, fun j hj hc => (h3' i hi).2.2 j hj (Or.inl hc)⟩⟩
  have hsum := walkWords_sum_le X
  have hloop := embLoop_triple (w := w) (p := p) hcopy (eCap := eCap) (r := r) (a := a) (lo := h)
    (hp0 := h) (mem₀ := mem) (v := y.view) (ptr := y.ptr) (X := X) (by omega) le_rfl htab hin'
    hX hold
  have hcost := embLoop_cost_le X
  refine ⟨_, hp, ?_⟩
  have hrun : ∃ o st' c, Runs w p ω (embStepStmt bCopy) (startState [r, a, X.length, h] mem pos)
      o st' c ∧ (o = .returned (X.foldl embConcStep (y.ptr, h)).2 ∧
        EmbLoopInv eCap r a h mem y.view y.ptr X [] st') ∧
      c ≤ 50 * (embChangeWords X + 1) := by
    apply runs_start_le
    dsimp only [embStepStmt]
    refine runs_seq_assign_le (v := r + 2) (Expr.eval_load_of_eq
      (Expr.eval_reg_of_eq (v := r) (by simp [startState])) h0) ?_
    refine runs_seq_assign_le (v := a) (Expr.eval_reg_of_eq (by simp [startState])) ?_
    refine runs_seq_assign_le (v := X.length) (Expr.eval_reg_of_eq (by simp [startState])) ?_
    refine runs_seq_assign_le (v := h) (Expr.eval_reg_of_eq (by simp [startState])) ?_
    refine runs_seq_triple_le hloop ?_ ?_
    · refine ⟨[], by simp, ?_, ?_, ?_, ?_, ?_, fun _ _ _ => rfl, ?_, ?_⟩
      all_goals try dsimp only
      · simp
      · simp
      · simp
      · simp
      · rw [EmbView.apply_nil]; exact ⟨h0, h1, hE⟩
      · simpa [startState] using hz
      · intro e he
        rw [EmbView.apply_nil] at he ⊢
        exact Or.inl ⟨rfl, rfl, he⟩
    · intro st hInv
      obtain ⟨pre, hpre, h4, h5, h6, h7, hrest⟩ := hInv
      rw [List.append_nil] at hpre
      subst hpre
      refine runs_ret_le (Expr.eval_reg_of_eq h7)
        ⟨rfl, pre, by simp, h4, h5, h6, h7, hrest⟩ ?_
      simp only [Expr.size]
      omega
  obtain ⟨o, st', c, hrun, ⟨rfl, hInv⟩, hc⟩ := hrun
  obtain ⟨pre, hpre, -, -, -, -, hrep', hfr, hz', hloc⟩ := hInv
  rw [List.append_nil] at hpre
  subst hpre
  have hH : (pre.foldl embConcStep (y.ptr, h)).2 = h + (pre.map fun p => walkWords p.2).sum := by
    rw [embConcStep_fold_snd]
  refine ⟨_, st', c, ⟨(pre.foldl embConcStep (y.ptr, h)).1, y.view.apply pre⟩, hrun,
    ⟨rfl, hrep'⟩, trivial, ?_, ?_, hz', ?_, ?_, hc⟩
  · simp only [Outcome.value]; omega
  · simp only [Outcome.value]; omega
  · intro x hx hn
    refine hfr x hx ?_
    simp only [embFoot, not_or, not_and, not_lt] at hn
    by_cases hxr : r ≤ x
    · exact Or.inr (hn.1 hxr)
    · exact Or.inl (by omega)
  · rintro x (hx | ⟨e, he, hx1, hx2⟩)
    · exact Or.inl (Or.inl hx)
    · simp only [Outcome.value]
      rcases hloc e he with ⟨hp', hem, hdom⟩ | ⟨hl1, hl2⟩
      · exact Or.inl (Or.inr ⟨e, hdom, hp' ▸ hx1, by simp only at hx2; rw [hp', hem] at hx2; exact hx2⟩)
      · exact Or.inr ⟨by simp only at hx1; omega, by simp only at hx2; omega⟩

/-- The initialization. -/
theorem embInit_ends {eCap w : ℕ} {p : Program} {f bCopy : ℕ}
    (hp : p.procs[f]? = some (embInitStmt bCopy))
    (hcopy : MeetsContract w p bCopy (copyWordsContract w))
    {a h : ℕ} {X : EmbChange} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hargs : ∀ x ∈ [eCap, a, X.length, h], x < 2 ^ w) (hz : ZeroFrom mem h)
    (hX : EmbChangeAt mem a X) (hin : EmbInputAt mem (fun _ => False) a eCap h X)
    (hlt : h + eCap + 2 + embChangeWords X < 2 ^ w) :
    ∃ body, p.procs[f]? = some body ∧ ∃ o st' c, ∃ y : EmbConc,
      Runs w p ω body (startState [eCap, a, X.length, h] mem pos) o st' c ∧
      (embRep eCap).rep h (EmbView.empty.apply X) y st'.mem ∧
      h ≤ o.value ∧ o.value ≤ h + (eCap + 2 + embChangeWords X) ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem a) ∧ (∀ a, embFoot eCap h y a → h ≤ a ∧ a < o.value) ∧
      c ≤ 50 * (embChangeWords X + 1) := by
  set m1 := Function.update (Function.update mem h (h + 2)) (h + 1) eCap with hm1
  have hm1_lo : ∀ x < h, m1 x = mem x := fun x hx => by
    simp only [hm1, Function.update_apply, show x ≠ h + 1 by omega, show x ≠ h by omega,
      ite_false]
  obtain ⟨hinA, -, hinE⟩ := hin
  have hin' : EmbInputAt m1 (fun x => h ≤ x ∧ x < h + 2 + eCap) a eCap h X := by
    refine ⟨hinA, fun i hi hc => by omega, fun i hi => ?_⟩
    obtain ⟨he, hw, -⟩ := hinE i hi
    rw [hm1_lo _ (by omega)]
    exact ⟨he, hw, fun j hj hc => by omega⟩
  have hX' : EmbChangeAt m1 a X :=
    hX.of_agree hinA (fun i hi => (hinE i hi).2.1) hm1_lo
  have hsum := walkWords_sum_le X
  have hloop := embLoop_triple (w := w) (p := p) hcopy (eCap := eCap) (r := h) (a := a) (lo := h)
    (hp0 := h + 2 + eCap) (mem₀ := m1) (v := EmbView.empty) (ptr := fun _ => 0) (X := X)
    (by omega) (by omega) le_rfl hin' hX' (fun e he => by simp [EmbView.empty] at he)
  have hcost := embLoop_cost_le X
  refine ⟨_, hp, ?_⟩
  have hrun : ∃ o st' c, Runs w p ω (embInitStmt bCopy) (startState [eCap, a, X.length, h] mem pos)
      o st' c ∧ (o = .returned (X.foldl embConcStep (fun _ => 0, h + 2 + eCap)).2 ∧
        EmbLoopInv eCap h a (h + 2 + eCap) m1 EmbView.empty (fun _ => 0) X [] st') ∧
      c ≤ 50 * (embChangeWords X + 1) := by
    apply runs_start_le
    dsimp only [embInitStmt]
    refine runs_seq_store_le (x := h) (v := h + 2) (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega))
        (by omega)) ?_
    refine runs_seq_store_le (x := h + 1) (v := eCap) (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp [startState])) ?_
    refine runs_seq_assign_le (v := h + 2) (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) (by omega)) ?_
    refine runs_seq_assign_le (v := a) (Expr.eval_reg_of_eq (by simp [startState])) ?_
    refine runs_seq_assign_le (v := X.length) (Expr.eval_reg_of_eq (by simp [startState])) ?_
    refine runs_seq_assign_le (v := h + 2 + eCap) (Expr.eval_add (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [startState])) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq (by simp [startState])) (by omega)) ?_
    refine runs_seq_triple_le hloop ?_ ?_
    · refine ⟨[], by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try dsimp only
      · simp
      · simp
      · simp
      · simp
      · rw [EmbView.apply_nil]
        refine ⟨by simp, by simp, ?_⟩
        intro e he; simp [EmbView.empty] at he
      · intro x _ _; simp [hm1, startState]
      · intro x hx
        simp only [List.foldl_nil] at hx
        simp only [startState, Function.update_apply, show x ≠ h + 1 by omega,
          show x ≠ h by omega, ite_false]
        exact hz x (by omega)
      · intro e he
        rw [EmbView.apply_nil] at he
        simp [EmbView.empty] at he
    · intro st hInv
      obtain ⟨pre, hpre, h4, h5, h6, h7, hrest⟩ := hInv
      rw [List.append_nil] at hpre
      subst hpre
      refine runs_ret_le (Expr.eval_reg_of_eq h7)
        ⟨rfl, pre, by simp, h4, h5, h6, h7, hrest⟩ ?_
      simp only [Expr.size]
      omega
  obtain ⟨o, st', c, hrun, ⟨rfl, hInv⟩, hc⟩ := hrun
  obtain ⟨pre, hpre, -, -, -, -, hrep', hfr, hz', hloc⟩ := hInv
  rw [List.append_nil] at hpre
  subst hpre
  have hH : (pre.foldl embConcStep (fun _ => 0, h + 2 + eCap)).2 =
      h + 2 + eCap + (pre.map fun p => walkWords p.2).sum := by
    rw [embConcStep_fold_snd]
  refine ⟨_, st', c, ⟨(pre.foldl embConcStep (fun _ => 0, h + 2 + eCap)).1,
    EmbView.empty.apply pre⟩, hrun, ⟨rfl, hrep'⟩, ?_, ?_, hz', ?_, ?_, hc⟩
  · simp only [Outcome.value]; omega
  · simp only [Outcome.value]; omega
  · intro x hx
    rw [hfr x (by omega) (Or.inl (by omega))]
    exact hm1_lo x hx
  · rintro x (hx | ⟨e, he, hx1, hx2⟩)
    · simp only [Outcome.value]; omega
    · simp only [Outcome.value]
      rcases hloc e he with ⟨-, -, hdom⟩ | ⟨hl1, hl2⟩
      · simp [EmbView.empty] at hdom
      · exact ⟨by simp only at hx1; omega, by simp only at hx2; omega⟩

/-- **The embedding table.** With the procedures `embProcs bCopy` at `b` and `copyWords` at
`bCopy`, the three operations meet `EmbBranchAt`, for every word size and name bound. -/
theorem embBranchAt {eCap w : ℕ} {p : Program} {b bCopy : ℕ} (hp : p.HasAt b (embProcs bCopy))
    (hcopy : p.HasAt bCopy [copyWords]) : EmbBranchAt eCap w p b where
  read r h v y mem pos ω hr hh hrep hfoot hz :=
    embRead_ends (by simpa [embProcs] using hp.get (i := 0) (by simp [embProcs])) hr hh hrep
      hfoot hz
  step r a h X v y mem pos ω hargs hrep hfoot hz hX hin hlt :=
    embStep_ends (hp.get (i := 1) (by simp [embProcs])) (copyWords_meetsContract hcopy) hargs
      hrep hfoot hz hX hin hlt
  init a h X mem pos ω hargs hz hX hin hlt :=
    embInit_ends (hp.get (i := 2) (by simp [embProcs])) (copyWords_meetsContract hcopy) hargs hz
      hX hin hlt

end

end MinCostFlow.SparseCore.Program.Read
