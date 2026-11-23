module

public import MinCostFlow.SparseCore.Program.OutStepIns

/-!
# The rotations of the output step, with the exact edit pointer

The last phase of the output step (`osRotPhase`) goes through the vertices `T₀` whose output
list may start at a new end. For each vertex `v` it asks the tour for the first marked end of
`v` (`firstMarked`) and, when there is one, writes the three-word edit `[4, v, key]`. Because a
vertex with an empty marked list writes no edit, the edit pointer advances by three words per
written edit, which the output step needs to bound the total edit words by five times their
encoding size.

This file proves that the phase runs with that exact edit pointer (`osRotPhaseW_runs`), writing
`outRotateEdits` of the marked lists of the tour while keeping the tour state, the stored graph,
and the batch.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program MinCostFlow.LowStretch

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ}
  {mem₀ : ℕ → ℕ} {S₀ G : MGraph} {U : List Update}

theorem outRotateEdits_append (t : ℕ → List End) (X Y : List ℕ) :
    outRotateEdits t (X ++ Y) = outRotateEdits t X ++ outRotateEdits t Y := by
  induction X with
  | nil => rfl
  | cons v X ih => simp only [List.cons_append, outRotateEdits, ih, List.append_assoc]

theorem outRotateEdits_singleton (t : ℕ → List End) (v : ℕ) :
    outRotateEdits t [v] = (match t v with | [] => [] | y :: _ => [.rotateTo v y]) :=
  List.append_nil _

theorem outRotateEdits_length_le (t : ℕ → List End) : ∀ X : List ℕ,
    (outRotateEdits t X).length ≤ X.length
  | [] => le_refl _
  | v :: X => by
    have ih := outRotateEdits_length_le t X
    simp only [outRotateEdits, List.length_append, List.length_cons]
    split <;> simp <;> omega

section Rot

variable (T A tx₀ mem₀ S₀ G U) in
/-- The state after `i` rotations, with potential `φ`. The edit pointer is `ep₀` plus three words
per `rotateTo` edit written so far. -/
def RotInvW (s : OutTourAbs) (E₀ : List OrdEdit) (bp ep₀ cur₀ : ℕ) (T₀ : List ℕ) (i φ : ℕ)
    (st : State) : Prop :=
  ∃ tx, SBase T A tx₀ mem₀ S₀ G U (E₀ ++ outRotateEdits s.markedList (T₀.take i)) bp
      (ep₀ + 3 * (outRotateEdits s.markedList (T₀.take i)).length) (st.regs 7) s tx st.mem ∧
    SRegs st A vCap eCap ∧ st.regs 14 = bp ∧
    st.regs 16 = ep₀ + 3 * (outRotateEdits s.markedList (T₀.take i)).length ∧
    st.regs 17 = U.length ∧ st.regs 18 = (E₀ ++ outRotateEdits s.markedList (T₀.take i)).length ∧
    st.regs 20 = i ∧ st.regs 26 = T₀.length ∧ i ≤ T₀.length ∧
    cur₀ ≤ st.regs 7 ∧ st.regs 7 ≤ cur₀ + i * S.querySpace ∧
    T.rep.phi A.tourH tx st.mem = φ

/-- **One rotation**, with the exact edit pointer. -/
theorem osRotIterW_runs (hC : SCtx T A tx₀) {s : OutTourAbs} {E₀ : List OrdEdit}
    {bp ep₀ cur₀ i φ : ℕ} {T₀ : List ℕ} {st : State}
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w) (htour : A.tourH < 2 ^ w)
    (hT : ListAt mem₀ (A.rotPtr + 1) T₀)
    (hfree : OutCellsFree A.rotPtr (1 + T₀.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a))
    (hTv : ∀ v ∈ T₀, v < vCap) (hml : ∀ v ∈ T₀, ∀ y ∈ s.markedList v, y.1 < eCap)
    (hbp : bp ≤ A.e0) (heR : ep₀ + 3 * T₀.length ≤ A.t0)
    (hroom : cur₀ + T₀.length * S.querySpace < 2 ^ w)
    (hI : RotInvW T A tx₀ mem₀ S₀ G U s E₀ bp ep₀ cur₀ T₀ i φ st) (hi : i < T₀.length) :
    ∃ st' c φ', Runs w p ω (osRotIter fm) st .normal st' c ∧
      RotInvW T A tx₀ mem₀ S₀ G U s E₀ bp ep₀ cur₀ T₀ (i + 1) φ' st' ∧
      c + φ' ≤ S.mul * ordStoreLog eCap + 100 + φ := by
  obtain ⟨tx, hB, hR, h14, h16, h17, h18, h20, h26, -, hc1, hc2, hphi⟩ := hI
  have hlen := outRotateEdits_length_le s.markedList (T₀.take i)
  rw [List.length_take, min_eq_left hi.le] at hlen
  generalize hep : ep₀ + 3 * (outRotateEdits s.markedList (T₀.take i)).length = ep at hB h16
  have hR' := hR
  obtain ⟨-, r1, -, -, -, r5, -, -, -, -, -, -, -, -, -, -⟩ := hR'
  have hq := S.querySpace_ge
  have hkey := rs_key_lt hw
  have hqi : i * S.querySpace + S.querySpace ≤ T₀.length * S.querySpace := by
    have := Nat.mul_le_mul_right S.querySpace (show i + 1 ≤ T₀.length by omega)
    rw [Nat.add_mul, one_mul] at this; exact this
  have hR0 : A.e0 = A.h + 4 + A.R := rfl
  have ht0e : A.t0 = A.e0 + A.R := rfl
  have hep1 := hB.2.2.2.2.2.2.2.2.2.2.1
  have hep2 := hB.2.2.2.2.2.2.2.2.2.2.2.1
  have hElen := hB.2.2.2.2.2.2.2.2.2.2.2.2.length_le
  obtain ⟨hfr1, hfr2⟩ := hfree
  set v := T₀[i] with hv_def
  have hv : v ∈ T₀ := List.getElem_mem hi
  have hvc := hTv v hv
  have hm1 : st.mem (A.rotPtr + 1 + i) = v := by
    rw [hB.mem_eq (by omega) (by have := hfr2 (1 + i) (by omega); rwa [show A.rotPtr + (1 + i) =
      A.rotPtr + 1 + i by omega] at this)]
    exact hT i hi
  obtain ⟨st₁, hr₁, hm₁, h21₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 21)
    (e := .load (.bin .add (.bin .add (.reg 5) (.const 1)) (.reg 20))) (st := st)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq r5)
      (Expr.eval_const (k := 1) (by omega)) (by omega)) (Expr.eval_reg_of_eq h20) (by omega)) hm1)
  have hB₁ : SBase T A tx₀ mem₀ S₀ G U (E₀ ++ outRotateEdits s.markedList (T₀.take i)) bp ep
      (st₁.regs 7) s tx st₁.mem := by rw [hm₁, ho₁ 7 (by omega)]; exact hB
  -- the query
  obtain ⟨st₂, c₂, tx₂, hr₂, hB₂, -, h29₂, ho₂, hc₂a, hc₂b, hcost₂⟩ := os_query (ω := ω)
    (argE := .reg 21) (dst := 29) hC hB₁ (by rw [ho₁ 1 (by omega), r1]) rfl
    (Expr.eval_reg_of_eq h21₁) (by omega) (by omega)
    (T.firstMarked_runs A.tourH v (st₁.regs 7) s tx st₁.mem st₁.pos ω htour hvc
      (by rw [ho₁ 7 (by omega)]; omega) hB₁.1 (hB₁.foot_lt_cur hC) hB₁.2.1
      (by rw [ho₁ 7 (by omega)]; omega))
  have hphi₁ : T.rep.phi A.tourH tx st₁.mem = φ := by rw [hm₁, hphi]
  have g7 : st₁.regs 7 = st.regs 7 := ho₁ 7 (by omega)
  have g : ∀ r, r ≠ 7 → r ≠ 8 → r ≠ 29 → r ≠ 21 → st₂.regs r = st.regs r := fun r a b c d => by
    rw [ho₂ r a b c, ho₁ r d]
  -- the edit, when there is a first marked end
  obtain ⟨st₃, c₃, hr₃, hB₃, hlen₃, h16₃, h18₃, hg₃, hc₃⟩ :
      ∃ st₃ c₃, Runs w p ω (.cond (.reg 29)
          (.seq (.store (.reg 16) (.const 4))
          (.seq (.store (.bin .add (.reg 16) (.const 1)) (.reg 21))
          (.seq (.store (.bin .add (.reg 16) (.const 2)) (.bin .sub (.reg 29) (.const 1)))
            (osBumpE (.const 3))))) .nop) st₂ .normal st₃ c₃ ∧
        SBase T A tx₀ mem₀ S₀ G U (E₀ ++ outRotateEdits s.markedList (T₀.take (i + 1))) bp
          (ep₀ + 3 * (outRotateEdits s.markedList (T₀.take (i + 1))).length)
          (st₂.regs 7) s tx₂ st₃.mem ∧
        (outRotateEdits s.markedList (T₀.take (i + 1))).length ≤
          (outRotateEdits s.markedList (T₀.take i)).length + 1 ∧
        st₃.regs 16 = ep₀ + 3 * (outRotateEdits s.markedList (T₀.take (i + 1))).length ∧
        st₃.regs 18 = (E₀ ++ outRotateEdits s.markedList (T₀.take (i + 1))).length ∧
        (∀ r, r ≠ 16 → r ≠ 18 → st₃.regs r = st₂.regs r) ∧
        c₃ + T.rep.phi A.tourH tx₂ st₃.mem ≤ 40 + T.rep.phi A.tourH tx₂ st₂.mem := by
    have htake : T₀.take (i + 1) = T₀.take i ++ [v] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
    rw [htake, outRotateEdits_append, outRotateEdits_singleton]
    cases hmv : s.markedList v with
    | nil =>
      have h29 : st₂.regs 29 = 0 := by rw [h29₂, hmv]; rfl
      refine ⟨st₂, _, step_cond_false (Expr.eval_reg_of_eq h29) step_nop, ?_, by simp,
        ?_, ?_, fun _ _ _ => rfl, by simp⟩
      · simpa [hep] using hB₂
      · rw [g 16 (by omega) (by omega) (by omega) (by omega), h16]; simp [hep]
      · rw [g 18 (by omega) (by omega) (by omega) (by omega), h18]; simp
    | cons y ys =>
      have hy : y ∈ s.markedList v := by rw [hmv]; exact List.mem_cons_self
      have hyc := hml v hv y hy
      have hky : endKey y < 2 * eCap := by
        obtain ⟨y1, y2⟩ := y
        cases y2 <;> simp [endKey] at hyc ⊢ <;> omega
      have h29 : st₂.regs 29 = 1 + endKey y := by rw [h29₂, hmv]; rfl
      have h16' : st₂.regs 16 = ep := by rw [g 16 (by omega) (by omega) (by omega) (by omega), h16]
      have h21' : st₂.regs 21 = v := by rw [ho₂ 21 (by omega) (by omega) (by omega), h21₁]
      obtain ⟨st₄, hr₄, hB₄, hp₄, hm₄, hg₄⟩ := os_store (p := p) (ω := ω) (a := .reg 16)
        (e := .const 4) hC hB₂ (Expr.eval_reg_of_eq h16') (Expr.eval_const (by omega))
        ⟨by omega, by omega, by omega, by omega⟩
      obtain ⟨st₅, hr₅, hB₅, hp₅, hm₅, hg₅⟩ := os_store (p := p) (ω := ω)
        (a := .bin .add (.reg 16) (.const 1)) (e := .reg 21) hC hB₄
        (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₄, h16'])) (Expr.eval_const (by omega))
          (by omega)) (Expr.eval_reg_of_eq (by rw [hg₄, h21']))
        ⟨by omega, by omega, by omega, by omega⟩
      obtain ⟨st₆, hr₆, hB₆, hp₆, hm₆, hg₆⟩ := os_store (p := p) (ω := ω)
        (a := .bin .add (.reg 16) (.const 2)) (e := .bin .sub (.reg 29) (.const 1)) hC hB₅
        (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₅, hg₄, h16'])) (Expr.eval_const (by omega))
          (by omega))
        (Expr.eval_sub (Expr.eval_reg_of_eq (by rw [hg₅, hg₄, h29])) (Expr.eval_const (by omega))
          (by omega))
        ⟨by omega, by omega, by omega, by omega⟩
      obtain ⟨st₇, hr₇, hm₇, h16₇, ho₇⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 16)
        (e := .bin .add (.reg 16) (.const 3)) (st := st₆)
        (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₆, hg₅, hg₄, h16']))
          (Expr.eval_const (by omega)) (by omega))
      have h18' : st₇.regs 18 = (E₀ ++ outRotateEdits s.markedList (T₀.take i)).length := by
        rw [ho₇ 18 (by omega), hg₆, hg₅, hg₄, g 18 (by omega) (by omega) (by omega) (by omega),
          h18]
      obtain ⟨st₈, hr₈, hm₈, h18₈, ho₈⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 18)
        (e := .bin .add (.reg 18) (.const 1)) (st := st₇)
        (Expr.eval_add (Expr.eval_reg_of_eq h18') (Expr.eval_const (by omega)) (by omega))
      have hd : decodeOrdEdit st₈.mem ep = (.rotateTo v y, 3) := by
        have := decodeOrdEdit_rotate (mem := st₈.mem) (a := ep) (v := v) (k := endKey y)
          (by rw [hm₈, hm₇, hm₆, hm₅, hm₄]; simp)
          (by rw [hm₈, hm₇, hm₆, hm₅]; simp)
          (by rw [hm₈, hm₇, hm₆]; simp)
        rwa [endOfKey_endKey] at this
      have hB₈ := (show SBase T A tx₀ mem₀ S₀ G U (E₀ ++ outRotateEdits s.markedList (T₀.take i))
          bp ep (st₂.regs 7) s tx₂ st₈.mem by rw [hm₈, hm₇]; exact hB₆).push_edit hd
        (by rw [hm₈, hm₇, hm₆, hm₅, hm₄]; simp) (by omega)
      have hlen' : (outRotateEdits s.markedList (T₀.take i) ++ [OrdEdit.rotateTo v y]).length =
          (outRotateEdits s.markedList (T₀.take i)).length + 1 := by simp
      refine ⟨st₈, _, step_cond_true (Expr.eval_reg_of_eq h29) (by omega)
        (runs_seq_normal hr₄ (runs_seq_normal hr₅ (runs_seq_normal hr₆
          (runs_seq_normal hr₇ hr₈)))), ?_, by simp, ?_, ?_, ?_, ?_⟩
      · rw [hlen', show ep₀ + 3 * ((outRotateEdits s.markedList (T₀.take i)).length + 1) =
          ep + 3 by omega]
        simpa [List.append_assoc] using hB₈
      · rw [ho₈ 16 (by omega), h16₇, hlen']; omega
      · rw [h18₈]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
      · intro r a b; rw [ho₈ r b, ho₇ r a, hg₆, hg₅, hg₄]
      · rw [hm₈, hm₇, hp₆, hp₅, hp₄]
        simp only [Expr.size_reg, Expr.size_bin, Expr.size_const]
        omega
  -- the last step
  have g20 : st₃.regs 20 = i := by
    rw [hg₃ 20 (by omega) (by omega), g 20 (by omega) (by omega) (by omega) (by omega), h20]
  obtain ⟨st₄, hr₄, hm₄, h20₄, ho₄⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 20)
    (e := .bin .add (.reg 20) (.const 1)) (st := st₃)
    (Expr.eval_add (Expr.eval_reg_of_eq g20) (Expr.eval_const (k := 1) (by omega)) (by omega))
  have hreg : ∀ r, r ≠ 7 → r ≠ 8 → r ≠ 29 → r ≠ 21 → r ≠ 16 → r ≠ 18 → r ≠ 20 →
      st₄.regs r = st.regs r := fun r a b c d e f g' => by
    rw [ho₄ r g', hg₃ r e f, g r a b c d]
  have g7₄ : st₄.regs 7 = st₂.regs 7 := by rw [ho₄ 7 (by omega), hg₃ 7 (by omega) (by omega)]
  refine ⟨st₄, _, T.rep.phi A.tourH tx₂ st₃.mem,
    runs_seq_normal hr₁ (runs_seq_normal hr₂ (runs_seq_normal hr₃ hr₄)),
    ⟨tx₂, ?_, hR.of_fixed fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_,
      by rw [hm₄]⟩, ?_⟩
  · rw [hm₄, g7₄]; exact hB₃
  · have : r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 29 ∧ r ≠ 21 ∧ r ≠ 16 ∧ r ≠ 18 ∧ r ≠ 20 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert hr <;> decide
    exact hreg r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2.1 this.2.2.2.2.2.1
      this.2.2.2.2.2.2
  · rw [hreg 14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h14]
  · rw [ho₄ 16 (by omega), h16₃]
  · rw [hreg 17 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h17]
  · rw [ho₄ 18 (by omega), h18₃]
  · rw [h20₄]
  · rw [hreg 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h26]
  · rw [g7₄]; rw [g7] at hc₂a; omega
  · rw [g7₄]; rw [g7] at hc₂b
    rw [Nat.add_mul, one_mul]; omega
  · simp only [Expr.size_reg, Expr.size_bin, Expr.size_const, Expr.size_load] at hcost₂ ⊢
    rw [hphi₁] at hcost₂
    omega

/-- **The rotations**, with the exact edit pointer. For the vertices `T₀`, the phase writes the
edits `outRotateEdits` of the marked lists of the tour after the edits `E₀`, three words each.
The tour state stays `s`. -/
theorem osRotPhaseW_runs (hC : SCtx T A tx₀) {s : OutTourAbs} {E₀ : List OrdEdit}
    {bp ep₀ cur₀ : ℕ} {T₀ : List ℕ} {st : State} {tx : T.rep.τ}
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w) (htour : A.tourH < 2 ^ w)
    (hcnt : mem₀ A.rotPtr = T₀.length) (hT : ListAt mem₀ (A.rotPtr + 1) T₀)
    (hfree : OutCellsFree A.rotPtr (1 + T₀.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a))
    (hTv : ∀ v ∈ T₀, v < vCap) (hml : ∀ v ∈ T₀, ∀ y ∈ s.markedList v, y.1 < eCap)
    (hbp : bp ≤ A.e0) (heR : ep₀ + 3 * T₀.length ≤ A.t0)
    (hroom : cur₀ + T₀.length * S.querySpace < 2 ^ w)
    (hB : SBase T A tx₀ mem₀ S₀ G U E₀ bp ep₀ cur₀ s tx st.mem)
    (hR : SRegs st A vCap eCap) (h7 : st.regs 7 = cur₀) (h14 : st.regs 14 = bp)
    (h16 : st.regs 16 = ep₀) (h17 : st.regs 17 = U.length) (h18 : st.regs 18 = E₀.length) :
    ∃ st' c, Runs w p ω (osRotPhase fm) st .normal st' c ∧
      ∃ φ', RotInvW T A tx₀ mem₀ S₀ G U s E₀ bp ep₀ cur₀ T₀ T₀.length φ' st' ∧
        c + φ' ≤ T₀.length * (S.mul * ordStoreLog eCap + 110) + 20 +
          T.rep.phi A.tourH tx st.mem := by
  have hkey := rs_key_lt hw
  have hR' := hR
  obtain ⟨-, -, -, -, -, r5, -, -, -, -, -, -, -, -, -, -⟩ := hR'
  have hfr := hfree
  obtain ⟨hfr1, hfr2⟩ := hfr
  obtain ⟨st₁, hr₁, hm₁, h20₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 20)
    (e := .const 0) (st := st) (Expr.eval_const (by omega))
  have hcnt' : st₁.mem A.rotPtr = T₀.length := by
    rw [hm₁, hB.mem_eq (by omega) (by simpa using hfr2 0 (by omega))]; exact hcnt
  obtain ⟨st₂, hr₂, hm₂, h26₂, ho₂⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 26)
    (e := .load (.reg 5)) (st := st₁)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by rw [ho₁ 5 (by omega), r5])) hcnt')
  have hI₀ : RotInvW T A tx₀ mem₀ S₀ G U s E₀ bp ep₀ cur₀ T₀ 0 (T.rep.phi A.tourH tx st.mem)
      st₂ := by
    refine ⟨tx, ?_, hR.of_fixed fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, h26₂,
      Nat.zero_le _, ?_, ?_, ?_⟩
    · have : st₂.regs 7 = cur₀ := by rw [ho₂ _ (by omega), ho₁ _ (by omega), h7]
      rw [hm₂, hm₁, this]; simpa [outRotateEdits] using hB
    · rw [ho₂ r (by rintro rfl; revert hr; decide), ho₁ r (by rintro rfl; revert hr; decide)]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h14]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h16]; simp [outRotateEdits]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h17]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h18]; simp [outRotateEdits]
    · rw [ho₂ _ (by omega), h20₁]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h7]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h7]; simp
    · rw [hm₂, hm₁]
  have hloop := runs_loop_amort (w := w) (p := p) (ω := ω) (e := .bin .lt (.reg 20) (.reg 26))
    (body := osRotIter fm)
    (Inv := fun a st => RotInvW T A tx₀ mem₀ S₀ G U s E₀ bp ep₀ cur₀ T₀ a.1 a.2 st)
    (Fin := fun o st r => o = .normal ∧ RotInvW T A tx₀ mem₀ S₀ G U s E₀ bp ep₀ cur₀ T₀
      T₀.length r st)
    (fun a => T₀.length - a.1)
    (fun a => (T₀.length - a.1) * (S.mul * ordStoreLog eCap + 110) + a.2 + 5)
    (condVal := fun st => if st.regs 20 < st.regs 26 then 1 else 0)
    (fun a st hI => Expr.eval_lt_op (Expr.eval_reg w 20 st) (Expr.eval_reg w 26 st) (by omega))
    ?_ ?_ (0, T.rep.phi A.tourH tx st.mem) st₂ hI₀
  · obtain ⟨o, st₃, c₃, hr₃, r, ⟨rfl, hI₃⟩, hc₃⟩ := hloop
    refine ⟨st₃, _, runs_seq_normal hr₁ (runs_seq_normal hr₂ hr₃), r, hI₃, ?_⟩
    simp only [Expr.size_reg, Expr.size_load, Expr.size_const, Nat.sub_zero] at hc₃ ⊢
    omega
  · rintro ⟨i, φ⟩ st hI hc
    have hI' := hI
    obtain ⟨-, -, -, -, -, -, -, h20', h26', hle, -⟩ := hI'
    have hin : i = T₀.length := by
      simp only [h20', h26'] at hc
      split_ifs at hc <;> omega
    subst hin
    refine ⟨φ, ⟨rfl, hI⟩, ?_⟩
    simp only [Expr.size_bin, Expr.size_reg, Nat.sub_self, Nat.zero_mul]; omega
  · rintro ⟨i, φ⟩ st hI hc
    have hI' := hI
    obtain ⟨-, -, -, -, -, -, -, h20', h26', -⟩ := hI'
    have hi : i < T₀.length := by
      simp only [h20', h26'] at hc
      split_ifs at hc with h
      · exact h
      · omega
    obtain ⟨st', c, φ', hr, hI'', hc'⟩ := osRotIterW_runs hC hw ht0 htour hT hfree hTv hml hbp
      heR hroom hI hi
    refine ⟨.normal, st', c, hr, (i + 1, φ'), hI'', by simp only; omega, ?_⟩
    simp only [Expr.size_reg, Expr.size_bin]
    have : T₀.length - i = (T₀.length - (i + 1)) + 1 := by omega
    rw [this, add_mul, one_mul]
    omega

end Rot

end MinCostFlow.SparseCore.Program
