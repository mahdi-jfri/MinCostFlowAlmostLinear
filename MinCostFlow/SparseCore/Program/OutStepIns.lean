module

public import MinCostFlow.SparseCore.Program.OutStepDel

/-!
# The insertions of the output step

The fourth phase of the output step (`osInsPhase`) goes through the entering edges `insL`. For
each edge `e` with new roots `tl e` and `hd e` it writes the batch record `[0, e, tl e, hd e]` and
applies it to the stored graph. Then for the tail end and then the head end of `e` it asks the
tour for the next marked end (`nextMarked`), writes the edit `[3, v, key, place]`, and marks the
end. This file proves that the phase runs (`osInsPhase_runs`).

The edits are stated with the answers of the tour (`insEditsTour`). That they are the edits
`outInsertEdits` of the model is a fact about the marks only; it is proved where the phases are
put together.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program MinCostFlow.LowStretch

/-! ## The model of the phase -/

/-- The tour state after marking both ends of `e`. -/
noncomputable def insTourStep (s : OutTourAbs) (e : ℕ) : OutTourAbs :=
  (s.setMark (e, true) 1).setMark (e, false) 1

/-- The tour state after marking the ends of the edges of `L`, in order. -/
noncomputable def insTourAfter (s : OutTourAbs) (L : List ℕ) : OutTourAbs :=
  L.foldl insTourStep s

/-- The two edits of an entering edge `e`, with the places that the tour gives. -/
noncomputable def insEditsOf (s : OutTourAbs) (tl hd : ℕ → ℕ) (e : ℕ) : List OrdEdit :=
  [.insertBefore (tl e) (e, true) (s.nextMarked (tl e) (e, true)),
    .insertBefore (hd e) (e, false) ((s.setMark (e, true) 1).nextMarked (hd e) (e, false))]

/-- The edits of the entering edges `L`, with the places that the tour gives. -/
noncomputable def insEditsTour (tl hd : ℕ → ℕ) : OutTourAbs → List ℕ → List OrdEdit
  | _, [] => []
  | s, e :: L => insEditsOf s tl hd e ++ insEditsTour tl hd (insTourStep s e) L

theorem insTourAfter_snoc (s : OutTourAbs) (L : List ℕ) (e : ℕ) :
    insTourAfter s (L ++ [e]) = insTourStep (insTourAfter s L) e := by
  simp [insTourAfter, List.foldl_append]

theorem insEditsTour_snoc (tl hd : ℕ → ℕ) (L : List ℕ) (e : ℕ) : ∀ s,
    insEditsTour tl hd s (L ++ [e]) = insEditsTour tl hd s L ++ insEditsOf (insTourAfter s L) tl hd e := by
  induction L with
  | nil => intro s; simp [insEditsTour, insTourAfter]
  | cons f L ih =>
    intro s
    simp only [List.cons_append, insEditsTour, ih, List.append_assoc]
    rfl

theorem insEditsTour_length (tl hd : ℕ → ℕ) (L : List ℕ) : ∀ s,
    (insEditsTour tl hd s L).length = 2 * L.length := by
  induction L with
  | nil => intro s; rfl
  | cons e L ih =>
    intro s
    simp only [insEditsTour, List.length_append, ih, insEditsOf, List.length_cons,
      List.length_nil]
    omega

theorem insTourAfter_cord (s : OutTourAbs) (L : List ℕ) : (insTourAfter s L).cord = s.cord := by
  induction L generalizing s with
  | nil => rfl
  | cons e L ih => exact ih (insTourStep s e)

/-- The word of an optional end decodes back to it. -/
theorem decode_optEndWord (o : Option End) :
    (if optEndWord o = 0 then none else some (endOfKey (optEndWord o - 1))) = o := by
  cases o with
  | none => rfl
  | some y => simp [optEndWord, endOfKey_endKey]

/-- A batch record takes at least two words, so there are at most as many records as words. -/
theorem batchBodyAt_length_le {mem : ℕ → ℕ} : ∀ {a : ℕ} {G : MGraph} {U : List Update}
    {words : ℕ}, BatchBodyAt mem a G U words → 2 * U.length ≤ words
  | _, _, [], _, _ => by simp
  | _, _, _ :: _, _, ⟨len, hle, hu, hB⟩ => by
    have := batchBodyAt_length_le hB
    have := hu.ge_two
    simp only [List.length_cons]
    omega

/-- Each record of the edits takes at least two words, so there are at most as many edits as
words. -/
theorem decodeOrdEdits_sum_ge (mem : ℕ → ℕ) : ∀ (n a : ℕ),
    2 * n ≤ ((decodeOrdEdits mem n a).2).sum
  | 0, _ => by simp [decodeOrdEdits]
  | n + 1, a => by
    have := decodeOrdEdits_sum_ge mem n (a + (decodeOrdEdit mem a).2)
    have h2 := decodeOrdEdit_words_ge_two mem a
    simp only [decodeOrdEdits, List.sum_cons]
    omega

theorem EditsBody.length_le {mem : ℕ → ℕ} {a : ℕ} {ds : List OrdEdit} {words : ℕ}
    (h : EditsBody mem a ds words) : 2 * ds.length ≤ words := by
  rw [← h.2.1]; exact decodeOrdEdits_sum_ge mem ds.length a

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ}
  {mem₀ : ℕ → ℕ} {S₀ G : MGraph} {U : List Update} {E : List OrdEdit} {bp ep cur : ℕ}
  {s : OutTourAbs} {tx : T.rep.τ}

/-! ## One end -/

/-- **One end of an entering edge**: the place from `nextMarked`, the edit, and the mark. The
expressions `vE` and `keyE` read registers that the steps do not change. -/
theorem osInsEnd_runs (hC : SCtx T A tx₀) {st : State} {vE keyE : Expr} {v key : ℕ}
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st.mem)
    (h1 : st.regs 1 = A.tourH) (h7 : st.regs 7 = cur) (h16 : st.regs 16 = ep)
    (h18 : st.regs 18 = E.length)
    (hval : ∀ st' : State, (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 16 → r ≠ 18 → r ≠ 29 →
      st'.regs r = st.regs r) → vE.eval w st' = some v ∧ keyE.eval w st' = some key)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (hkey : key < 2 * eCap) (hv : v < vCap)
    (hmem : endOfKey key ∈ s.cord v) (htour : A.tourH < 2 ^ w)
    (hep : ep + 4 ≤ A.t0) (ht0 : A.t0 < 2 ^ w)
    (hspace : cur + 2 * S.querySpace < 2 ^ w) :
    ∃ st' c tx', Runs w p ω (osInsEnd nm sm vE keyE) st .normal st' c ∧
      SBase T A tx₀ mem₀ S₀ G U
        (E ++ [.insertBefore v (endOfKey key) (s.nextMarked v (endOfKey key))]) bp (ep + 4)
        (st'.regs 7) (s.setMark (endOfKey key) 1) tx' st'.mem ∧
      st'.regs 16 = ep + 4 ∧ st'.regs 18 = E.length + 1 ∧
      (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 16 → r ≠ 18 → r ≠ 29 → st'.regs r = st.regs r) ∧
      cur ≤ st'.regs 7 ∧ st'.regs 7 ≤ cur + 2 * S.querySpace ∧
      c + T.rep.phi A.tourH tx' st'.mem ≤
        2 * (S.mul * ordStoreLog eCap) + keyE.size * 4 + vE.size + 60 +
          T.rep.phi A.tourH tx st.mem := by
  have hq := S.querySpace_ge
  have hkw := rs_key_lt hw
  have hR0 : A.e0 = A.h + 4 + A.R := rfl
  have ht0e : A.t0 = A.e0 + A.R := rfl
  have hep1 := hB.2.2.2.2.2.2.2.2.2.2.1
  have hbp2 := hB.2.2.2.2.2.2.2.2.1
  have hElen := hB.2.2.2.2.2.2.2.2.2.2.2.2.length_le
  obtain ⟨hv₀, hk₀⟩ := hval st (fun _ _ _ _ _ _ => rfl)
  -- the query
  obtain ⟨st₁, c₁, tx₁, hr₁, hB₁, -, h29₁, ho₁, hc₁a, hc₁b, hcost₁⟩ := os_query (ω := ω)
    (argE := keyE) (dst := 29) hC hB h1 h7 hk₀ (by omega) (by omega)
    (T.nextMarked_runs A.tourH key v cur s tx st.mem st.pos ω htour hkey (by omega) hv
      (by omega) hmem hB.1 (hB.foot_lt_cur hC) hB.2.1 (by omega))
  have hval₁ := hval st₁ fun r a b _ _ e => ho₁ r a b e
  set place := s.nextMarked v (endOfKey key) with hplace
  have g16 : st₁.regs 16 = ep := by rw [ho₁ 16 (by omega) (by omega) (by omega), h16]
  -- the edit `[3, v, key, place]`
  obtain ⟨st₂, hr₂, hB₂, hp₂, hm₂, hg₂⟩ := os_store (p := p) (ω := ω) (a := .reg 16)
    (e := .const 3) hC hB₁ (Expr.eval_reg_of_eq g16) (Expr.eval_const (by omega))
    ⟨by omega, by omega, by omega, by omega⟩
  have hval₂ := hval st₂ fun r a b _ _ e => by rw [hg₂]; exact ho₁ r a b e
  obtain ⟨st₃, hr₃, hB₃, hp₃, hm₃, hg₃⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 16) (.const 1)) (e := vE) hC hB₂
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₂, g16])) (Expr.eval_const (by omega))
      (by omega)) hval₂.1 ⟨by omega, by omega, by omega, by omega⟩
  have hval₃ := hval st₃ fun r a b _ _ e => by rw [hg₃, hg₂]; exact ho₁ r a b e
  obtain ⟨st₄, hr₄, hB₄, hp₄, hm₄, hg₄⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 16) (.const 2)) (e := keyE) hC hB₃
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₃, hg₂, g16])) (Expr.eval_const (by omega))
      (by omega)) hval₃.2 ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₅, hr₅, hB₅, hp₅, hm₅, hg₅⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 16) (.const 3)) (e := .reg 29) hC hB₄
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₄, hg₃, hg₂, g16])) (Expr.eval_const (by omega))
      (by omega)) (Expr.eval_reg_of_eq (by rw [hg₄, hg₃, hg₂, h29₁]))
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₆, hr₆, hm₆, h16₆, ho₆⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 16)
    (e := .bin .add (.reg 16) (.const 4)) (st := st₅)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₅, hg₄, hg₃, hg₂, g16]))
      (Expr.eval_const (by omega)) (by omega))
  have g18 : st₆.regs 18 = E.length := by
    rw [ho₆ 18 (by omega), hg₅, hg₄, hg₃, hg₂, ho₁ 18 (by omega) (by omega) (by omega), h18]
  obtain ⟨st₇, hr₇, hm₇, h18₇, ho₇⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 18)
    (e := .bin .add (.reg 18) (.const 1)) (st := st₆)
    (Expr.eval_add (Expr.eval_reg_of_eq g18) (Expr.eval_const (by omega)) (by omega))
  have hd : decodeOrdEdit st₇.mem ep = (.insertBefore v (endOfKey key) place, 4) := by
    have := decodeOrdEdit_insert (mem := st₇.mem) (a := ep) (v := v) (k := key)
      (y := optEndWord place)
      (by rw [hm₇, hm₆, hm₅, hm₄, hm₃, hm₂]
          simp [Function.update_of_ne (show ep ≠ ep + 3 by omega),
            Function.update_of_ne (show ep ≠ ep + 2 by omega),
            Function.update_of_ne (show ep ≠ ep + 1 by omega)])
      (by rw [hm₇, hm₆, hm₅, hm₄, hm₃]
          simp [Function.update_of_ne (show ep + 1 ≠ ep + 3 by omega),
            Function.update_of_ne (show ep + 1 ≠ ep + 2 by omega)])
      (by rw [hm₇, hm₆, hm₅, hm₄]
          simp [Function.update_of_ne (show ep + 2 ≠ ep + 3 by omega)])
      (by rw [hm₇, hm₆, hm₅]; simp)
    rwa [decode_optEndWord] at this
  have hB₇ := (show SBase T A tx₀ mem₀ S₀ G U E bp ep (st₁.regs 7) s tx₁ st₇.mem by
    rw [hm₇, hm₆]; exact hB₅).push_edit hd (by
      rw [hm₇, hm₆, hm₅, hm₄, hm₃, hm₂]
      simp [Function.update_of_ne (show ep ≠ ep + 3 by omega),
        Function.update_of_ne (show ep ≠ ep + 2 by omega),
        Function.update_of_ne (show ep ≠ ep + 1 by omega)]) (by omega)
  -- the mark
  have g7 : st₇.regs 7 = st₁.regs 7 := by rw [ho₇ 7 (by omega), ho₆ 7 (by omega), hg₅, hg₄, hg₃, hg₂]
  have hreg₇ : ∀ r, r ≠ 7 → r ≠ 8 → r ≠ 16 → r ≠ 18 → r ≠ 29 → st₇.regs r = st.regs r :=
    fun r a b c d e => by rw [ho₇ r d, ho₆ r c, hg₅, hg₄, hg₃, hg₂, ho₁ r a b e]
  obtain ⟨st₈, c₈, tx₈, hr₈, hB₈, -, ho₈, hc₈a, hc₈b, hcost₈⟩ := os_mark (ω := ω) (sm := sm)
    (flag := 1) (key := key) (v := v) (keyE := keyE) hC hB₇
    (by rw [hreg₇ 1 (by omega) (by omega) (by omega) (by omega) (by omega), h1]) g7
    (hval st₇ hreg₇).2 hkey (by omega) le_rfl hv hmem htour (by omega)
  refine ⟨st₈, _, tx₈, runs_seq_normal hr₁ (runs_seq_normal hr₂ (runs_seq_normal hr₃
    (runs_seq_normal hr₄ (runs_seq_normal hr₅ (runs_seq_normal (runs_seq_normal hr₆ hr₇) hr₈))))),
    hB₈, ?_, ?_, ?_, by omega, by omega, ?_⟩
  · rw [ho₈ 16 (by omega) (by omega), ho₇ 16 (by omega), h16₆]
  · rw [ho₈ 18 (by omega) (by omega), h18₇]
  · intro r a b c d e; rw [ho₈ r a b, hreg₇ r a b c d e]
  · have hphi₇ : T.rep.phi A.tourH tx₁ st₇.mem = T.rep.phi A.tourH tx₁ st₁.mem := by
      rw [hm₇, hm₆, hp₅, hp₄, hp₃, hp₂]
    rw [hphi₇] at hcost₈
    simp only [osBumpE, osQuery, Expr.size_reg, Expr.size_bin, Expr.size_const,
      Expr.size_load] at hcost₁ hcost₈ ⊢
    omega

/-! ## One insertion -/

section Ins

variable (T A tx₀ mem₀ S₀) in
/-- The state after `i` insertions, with potential `φ`, from the graph `G₀`, the batch `U₀`,
the edits `E₀` and the tour state `s₀`. -/
def OsInsInv (G₀ : MGraph) (U₀ : List Update) (E₀ : List OrdEdit) (s₀ : OutTourAbs)
    (insL : List ℕ) (tl hd : ℕ → ℕ) (bp₀ ep₀ cur₀ i φ : ℕ) (st : State) : Prop :=
  let I := (insL.take i).map fun e => Update.insert e (tl e) (hd e)
  ∃ tx, SBase T A tx₀ mem₀ S₀ (G₀.applyBatch I) (U₀ ++ I)
      (E₀ ++ insEditsTour tl hd s₀ (insL.take i)) (bp₀ + 4 * i) (ep₀ + 8 * i) (st.regs 7)
      (insTourAfter s₀ (insL.take i)) tx st.mem ∧
    SRegs st A vCap eCap ∧ st.regs 14 = bp₀ + 4 * i ∧ st.regs 16 = ep₀ + 8 * i ∧
    st.regs 17 = U₀.length + i ∧ st.regs 18 = E₀.length + 2 * i ∧
    st.regs 20 = i ∧ st.regs 26 = insL.length ∧ i ≤ insL.length ∧
    cur₀ ≤ st.regs 7 ∧ st.regs 7 ≤ cur₀ + 4 * i * S.querySpace ∧
    T.rep.phi A.tourH tx st.mem = φ

/-- **One insertion.** -/
theorem osInsIter_runs (hC : SCtx T A tx₀) {au : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    {G₀ : MGraph} {U₀ : List Update} {E₀ : List OrdEdit} {s₀ : OutTourAbs} {insL : List ℕ}
    {tl hd : ℕ → ℕ} {bp₀ ep₀ cur₀ i φ : ℕ} {st : State} (hG₀ : G₀ = S₀.applyBatch U₀)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w) (htour : A.tourH < 2 ^ w)
    (hins : OutInsAt mem₀ A.insPtr insL tl hd)
    (hfree : OutCellsFree A.insPtr (1 + 3 * insL.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a))
    (hval : ∀ j (hj : j < insL.length),
      (G₀.applyBatch ((insL.take j).map fun e => Update.insert e (tl e) (hd e))).UpdateIsValid
        (.insert insL[j] (tl insL[j]) (hd insL[j])))
    (hcap : ∀ e ∈ insL, e < eCap) (hends : ∀ e ∈ insL, tl e < vCap ∧ hd e < vCap)
    (hcord : ∀ e ∈ insL, (e, true) ∈ s₀.cord (tl e) ∧ (e, false) ∈ s₀.cord (hd e))
    (hbR : bp₀ + 4 * insL.length ≤ A.e0) (heR : ep₀ + 8 * insL.length ≤ A.t0)
    (hroom : cur₀ + 4 * insL.length * S.querySpace < 2 ^ w)
    (hI : OsInsInv T A tx₀ mem₀ S₀ G₀ U₀ E₀ s₀ insL tl hd bp₀ ep₀ cur₀ i φ st)
    (hi : i < insL.length) :
    ∃ st' c φ', Runs w p ω (osInsIter nm sm au) st .normal st' c ∧
      OsInsInv T A tx₀ mem₀ S₀ G₀ U₀ E₀ s₀ insL tl hd bp₀ ep₀ cur₀ (i + 1) φ' st' ∧
      c + φ' ≤ 4 * (S.mul * ordStoreLog eCap) + 3000 + φ := by
  obtain ⟨tx, hB, hR, h14, h16, h17, h18, h20, h26, -, hc1, hc2, hphi⟩ := hI
  have hR' := hR
  obtain ⟨r0, r1, -, -, r4, -, -, r10, -, -, -, -, -, -, -, -⟩ := hR'
  have hgh := hC.2.2.1
  have hq := S.querySpace_ge
  have hkey := rs_key_lt hw
  have hqi : 4 * i * S.querySpace + 4 * S.querySpace ≤ 4 * insL.length * S.querySpace := by
    have := Nat.mul_le_mul_right S.querySpace (show 4 * i + 4 ≤ 4 * insL.length by omega)
    rw [Nat.add_mul] at this; exact this
  have hR0 : A.e0 = A.h + 4 + A.R := rfl
  have ht0e : A.t0 = A.e0 + A.R := rfl
  have hbp1 := hB.2.2.2.2.2.2.2.1
  have hep1 := hB.2.2.2.2.2.2.2.2.2.2.1
  have hUlen := batchBodyAt_length_le hB.2.2.2.2.2.2.2.2.2.1
  set e := insL[i] with he_def
  have he : e ∈ insL := List.getElem_mem hi
  have hecap := hcap e he
  obtain ⟨htl, hhd⟩ := hends e he
  have h16w : 16 ≤ 2 ^ w := rs_sixteen_of_cap hw (by omega)
  obtain ⟨hfr1, hfr2⟩ := hfree
  obtain ⟨-, hins2⟩ := hins
  obtain ⟨hiE, hiT, hiH⟩ := hins2 i hi
  rw [List.getD_eq_getElem _ _ hi] at hiE hiT hiH
  have hrd : ∀ k, k < 3 → st.mem (A.insPtr + (k + 1) + 3 * i) = mem₀ (A.insPtr + (k + 1) + 3 * i) :=
    fun k hk => hB.mem_eq (by omega) (by
      have := hfr2 (k + 1 + 3 * i) (by omega)
      rwa [show A.insPtr + (k + 1 + 3 * i) = A.insPtr + (k + 1) + 3 * i by omega] at this)
  have hv1 : st.mem (A.insPtr + 1 + 3 * i) = e := (hrd 0 (by omega)).trans hiE
  have hv2 : st.mem (A.insPtr + 2 + 3 * i) = tl e := (hrd 1 (by omega)).trans hiT
  have hv3 : st.mem (A.insPtr + 3 + 3 * i) = hd e := (hrd 2 (by omega)).trans hiH
  have hvw : vCap + eCap + 2 < 2 ^ w := lt_of_le_of_lt (Nat.le_self_pow two_ne_zero _) hw
  have h3i : (Expr.bin .mul (.const 3) (.reg 20)).eval w st = some (3 * i) :=
    Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h20) (by omega)
  -- the three input words
  obtain ⟨st₁, hr₁, hm₁, h21₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 21)
    (e := .load (.bin .add (.bin .add (.reg 4) (.const 1)) (.bin .mul (.const 3) (.reg 20))))
    (st := st) (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq r4)
      (Expr.eval_const (by omega)) (by omega)) h3i (by omega)) hv1)
  have h3i₁ : (Expr.bin .mul (.const 3) (.reg 20)).eval w st₁ = some (3 * i) :=
    Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by rw [ho₁ 20 (by omega), h20]))
      (by omega)
  obtain ⟨st₂, hr₂, hm₂, h22₂, ho₂⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 22)
    (e := .load (.bin .add (.bin .add (.reg 4) (.const 2)) (.bin .mul (.const 3) (.reg 20))))
    (st := st₁) (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq
      (by rw [ho₁ 4 (by omega), r4])) (Expr.eval_const (by omega)) (by omega)) h3i₁ (by omega))
      (by rw [hm₁, hv2]))
  have h3i₂ : (Expr.bin .mul (.const 3) (.reg 20)).eval w st₂ = some (3 * i) :=
    Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by rw [ho₂ 20 (by omega),
      ho₁ 20 (by omega), h20])) (by omega)
  obtain ⟨st₃, hr₃, hm₃, h27₃, ho₃⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 27)
    (e := .load (.bin .add (.bin .add (.reg 4) (.const 3)) (.bin .mul (.const 3) (.reg 20))))
    (st := st₂) (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq
      (by rw [ho₂ 4 (by omega), ho₁ 4 (by omega), r4])) (Expr.eval_const (by omega)) (by omega))
      h3i₂ (by omega)) (by rw [hm₂, hm₁, hv3]))
  have g : ∀ r, r ≠ 21 → r ≠ 22 → r ≠ 27 → st₃.regs r = st.regs r := fun r a b c => by
    rw [ho₃ r c, ho₂ r b, ho₁ r a]
  have g21 : st₃.regs 21 = e := by rw [ho₃ 21 (by omega), ho₂ 21 (by omega), h21₁]
  have g22 : st₃.regs 22 = tl e := by rw [ho₃ 22 (by omega), h22₂]
  have g14 : st₃.regs 14 = bp₀ + 4 * i := by rw [g 14 (by omega) (by omega) (by omega), h14]
  set I := (insL.take i).map fun e => Update.insert e (tl e) (hd e) with hIdef
  have hIlen : I.length = i := by simp only [hIdef, List.length_map, List.length_take]; omega
  rw [List.length_append, hIlen] at hUlen
  have hB₃ : SBase T A tx₀ mem₀ S₀ (G₀.applyBatch I) (U₀ ++ I)
      (E₀ ++ insEditsTour tl hd s₀ (insL.take i)) (bp₀ + 4 * i) (ep₀ + 8 * i) (st.regs 7)
      (insTourAfter s₀ (insL.take i)) tx st₃.mem := by rw [hm₃, hm₂, hm₁]; exact hB
  -- the batch record `[0, e, tl e, hd e]`
  obtain ⟨st₄, hr₄, hB₄, hp₄, hm₄, hg₄⟩ := os_store (p := p) (ω := ω) (a := .reg 14)
    (e := .const 0) hC hB₃ (Expr.eval_reg_of_eq g14) (Expr.eval_const (by omega))
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₅, hr₅, hB₅, hp₅, hm₅, hg₅⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 1)) (e := .reg 21) hC hB₄
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₄, g14])) (Expr.eval_const (by omega))
      (by omega)) (Expr.eval_reg_of_eq (by rw [hg₄, g21])) ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₆, hr₆, hB₆, hp₆, hm₆, hg₆⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 2)) (e := .reg 22) hC hB₅
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₅, hg₄, g14])) (Expr.eval_const (by omega))
      (by omega)) (Expr.eval_reg_of_eq (by rw [hg₅, hg₄, g22]))
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₇, hr₇, hB₇, hp₇, hm₇, hg₇⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 3)) (e := .reg 27) hC hB₆
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₆, hg₅, hg₄, g14])) (Expr.eval_const (by omega))
      (by omega)) (Expr.eval_reg_of_eq (by rw [hg₆, hg₅, hg₄, h27₃]))
    ⟨by omega, by omega, by omega, by omega⟩
  have hu₇ : UpdateAt st₇.mem (bp₀ + 4 * i) (G₀.applyBatch I) (.insert e (tl e) (hd e)) 4 := by
    refine ⟨rfl, fun j hj => ?_⟩
    simp only [List.length_cons, List.length_nil] at hj
    rw [hm₇, hm₆, hm₅, hm₄]
    interval_cases j
    · simp only [Nat.add_zero]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]; rfl
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self]; rfl
    · rw [Function.update_of_ne (by omega), Function.update_self]; rfl
    · rw [Function.update_self]; rfl
  obtain ⟨st₈, c₈, hr₈, hB₈, hp₈, hfr₈, ho₈, hc₈⟩ := os_apply (ω := ω) hC hau hB₇
    (by rw [hg₇, hg₆, hg₅, hg₄, g 10 (by omega) (by omega) (by omega), r10])
    (by rw [hg₇, hg₆, hg₅, hg₄, g14]) hu₇ (hval i hi) hecap (by omega)
    (fun j hj => by
      rw [show j < 4 ↔ j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega] at hj
      rcases hj with rfl | rfl | rfl | rfl
      · rw [hu₇.2 0 (by simp)]; simp only [List.getElem_cons_zero]; omega
      · rw [hu₇.2 1 (by simp)]; simp only [List.getElem_cons_succ, List.getElem_cons_zero]; omega
      · rw [hu₇.2 2 (by simp)]; simp only [List.getElem_cons_succ, List.getElem_cons_zero]; omega
      · rw [hu₇.2 3 (by simp)]; simp only [List.getElem_cons_succ, List.getElem_cons_zero]; omega)
    h16w (by omega) (by omega)
  have hu₈ : UpdateAt st₈.mem (bp₀ + 4 * i) (G₀.applyBatch I) (.insert e (tl e) (hd e)) 4 :=
    UpdateAt.of_agree hu₇ (fun j _ => hfr₈ _ (Or.inr (by omega)))
  obtain ⟨st₉, hr₉, hm₉, h14₉, ho₉⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 14)
    (e := .bin .add (.reg 14) (.const 4)) (st := st₈)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₈ _ (by omega), hg₇, hg₆, hg₅, hg₄, g14]))
      (Expr.eval_const (by omega)) (by omega))
  obtain ⟨st₁₀, hr₁₀, hm₁₀, h17₁₀, ho₁₀⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 17)
    (e := .bin .add (.reg 17) (.const 1)) (st := st₉)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₉ _ (by omega), ho₈ _ (by omega), hg₇, hg₆,
      hg₅, hg₄, g 17 (by omega) (by omega) (by omega), h17]))
      (Expr.eval_const (by omega)) (by omega))
  have hB₁₀ := (show SBase T A tx₀ mem₀ S₀ ((G₀.applyBatch I).applyUpdate (.insert e (tl e) (hd e)))
      (U₀ ++ I) (E₀ ++ insEditsTour tl hd s₀ (insL.take i)) (bp₀ + 4 * i) (ep₀ + 8 * i)
      (st.regs 7) (insTourAfter s₀ (insL.take i)) tx st₁₀.mem by
    rw [hm₁₀, hm₉]; exact hB₈).push_batch
    (by rw [hm₁₀, hm₉, MinCostFlow.DynSpanner.applyBatch_append, ← hG₀]; exact hu₈) (by omega)
  -- registers before the two ends
  have hreg₁₀ : ∀ r, r ≠ 9 → r ≠ 14 → r ≠ 17 → r ≠ 21 → r ≠ 22 → r ≠ 27 →
      st₁₀.regs r = st.regs r := fun r a b c d e' f => by
    rw [ho₁₀ r c, ho₉ r b, ho₈ r a, hg₇, hg₆, hg₅, hg₄, g r d e' f]
  have g7₁₀ : st₁₀.regs 7 = st.regs 7 := hreg₁₀ 7 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have g21₁₀ : st₁₀.regs 21 = e := by rw [ho₁₀ 21 (by omega), ho₉ 21 (by omega),
    ho₈ 21 (by omega), hg₇, hg₆, hg₅, hg₄, g21]
  have g22₁₀ : st₁₀.regs 22 = tl e := by rw [ho₁₀ 22 (by omega), ho₉ 22 (by omega),
    ho₈ 22 (by omega), hg₇, hg₆, hg₅, hg₄, g22]
  have g27₁₀ : st₁₀.regs 27 = hd e := by rw [ho₁₀ 27 (by omega), ho₉ 27 (by omega),
    ho₈ 27 (by omega), hg₇, hg₆, hg₅, hg₄, h27₃]
  have hcordi : (insTourAfter s₀ (insL.take i)).cord = s₀.cord := insTourAfter_cord _ _
  -- the tail end
  obtain ⟨st₁₁, c₁₁, tx₁₁, hr₁₁, hB₁₁, h16₁₁, h18₁₁, ho₁₁, hcA1, hcA2, hcostA⟩ :=
    osInsEnd_runs (ω := ω) (nm := nm) (sm := sm) (vE := .reg 22) (keyE := osKey0) (v := tl e)
      (key := e + e) hC (by rw [g7₁₀]; exact hB₁₀)
      (by rw [hreg₁₀ 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r1]) rfl
      (by rw [hreg₁₀ 16 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h16])
      (by rw [hreg₁₀ 18 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h18]
          rw [List.length_append, insEditsTour_length, List.length_take, min_eq_left (by omega)])
      (fun st' h' => ⟨Expr.eval_reg_of_eq (by rw [h' 22 (by omega) (by omega) (by omega)
          (by omega) (by omega), g22₁₀]),
        Expr.eval_add (Expr.eval_reg_of_eq (by rw [h' 21 (by omega) (by omega) (by omega)
          (by omega) (by omega), g21₁₀])) (Expr.eval_reg_of_eq (by rw [h' 21 (by omega) (by omega)
          (by omega) (by omega) (by omega), g21₁₀])) (by omega)⟩)
      hw (by omega) htl (by rw [endOfKey_two_mul, hcordi]; exact (hcord e he).1) htour
      (by omega) ht0 (by omega)
  rw [endOfKey_two_mul] at hB₁₁
  have g21₁₁ : st₁₁.regs 21 = e := by
    rw [ho₁₁ 21 (by omega) (by omega) (by omega) (by omega) (by omega), g21₁₀]
  have g27₁₁ : st₁₁.regs 27 = hd e := by
    rw [ho₁₁ 27 (by omega) (by omega) (by omega) (by omega) (by omega), g27₁₀]
  -- the head end
  obtain ⟨st₁₂, c₁₂, tx₁₂, hr₁₂, hB₁₂, h16₁₂, h18₁₂, ho₁₂, hcB1, hcB2, hcostB⟩ :=
    osInsEnd_runs (ω := ω) (nm := nm) (sm := sm) (vE := .reg 27) (keyE := osKey1) (v := hd e)
      (key := e + e + 1) hC hB₁₁
      (by rw [ho₁₁ 1 (by omega) (by omega) (by omega) (by omega) (by omega),
        hreg₁₀ 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), r1]) rfl
      h16₁₁ (by rw [h18₁₁]; simp only [List.length_append, List.length_cons, List.length_nil])
      (fun st' h' => ⟨Expr.eval_reg_of_eq (by rw [h' 27 (by omega) (by omega) (by omega)
          (by omega) (by omega), g27₁₁]),
        Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by rw [h' 21 (by omega) (by omega)
          (by omega) (by omega) (by omega), g21₁₁])) (Expr.eval_reg_of_eq (by rw [h' 21 (by omega)
          (by omega) (by omega) (by omega) (by omega), g21₁₁])) (by omega))
          (Expr.eval_const (by omega)) (by omega)⟩)
      hw (by omega) hhd
      (by rw [endOfKey_two_mul_add_one]
          show (e, false) ∈ ((insTourAfter s₀ (insL.take i)).setMark (e, true) 1).cord (hd e)
          rw [show ((insTourAfter s₀ (insL.take i)).setMark (e, true) 1).cord =
            (insTourAfter s₀ (insL.take i)).cord from rfl, hcordi]
          exact (hcord e he).2) htour
      (by omega) ht0 (by omega)
  rw [endOfKey_two_mul_add_one] at hB₁₂
  -- the last step
  have g20 : st₁₂.regs 20 = i := by
    rw [ho₁₂ 20 (by omega) (by omega) (by omega) (by omega) (by omega),
      ho₁₁ 20 (by omega) (by omega) (by omega) (by omega) (by omega),
      hreg₁₀ 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h20]
  obtain ⟨st₁₃, hr₁₃, hm₁₃, h20₁₃, ho₁₃⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 20)
    (e := .bin .add (.reg 20) (.const 1)) (st := st₁₂)
    (Expr.eval_add (Expr.eval_reg_of_eq g20) (Expr.eval_const (k := 1) (by omega)) (by omega))
  have hreg : ∀ r, r ≠ 7 → r ≠ 8 → r ≠ 16 → r ≠ 18 → r ≠ 29 → r ≠ 20 → r ≠ 9 → r ≠ 14 →
      r ≠ 17 → r ≠ 21 → r ≠ 22 → r ≠ 27 → st₁₃.regs r = st.regs r :=
    fun r a b c d e' f g' h' k l m n => by
      rw [ho₁₃ r f, ho₁₂ r a b c d e', ho₁₁ r a b c d e', hreg₁₀ r g' h' k l m n]
  have htake : insL.take (i + 1) = insL.take i ++ [e] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl
  refine ⟨st₁₃, _, T.rep.phi A.tourH tx₁₂ st₁₂.mem,
    runs_seq_normal hr₁ (runs_seq_normal hr₂ (runs_seq_normal hr₃ (runs_seq_normal hr₄
      (runs_seq_normal hr₅ (runs_seq_normal hr₆ (runs_seq_normal hr₇ (runs_seq_normal hr₈
        (runs_seq_normal (runs_seq_normal hr₉ hr₁₀) (runs_seq_normal hr₁₁
          (runs_seq_normal hr₁₂ hr₁₃)))))))))),
    ⟨tx₁₂, ?_, hR.of_fixed fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_,
      by rw [hm₁₃]⟩, ?_⟩
  · rw [hm₁₃, ho₁₃ 7 (by omega), htake, insTourAfter_snoc, insEditsTour_snoc,
      show (insL.take i ++ [e]).map (fun e => Update.insert e (tl e) (hd e)) =
        I ++ [Update.insert e (tl e) (hd e)] by simp [hIdef],
      applyBatch_snoc, ← List.append_assoc,
      show bp₀ + 4 * (i + 1) = bp₀ + 4 * i + 4 by omega,
      show ep₀ + 8 * (i + 1) = ep₀ + 8 * i + 4 + 4 by omega]
    simpa [insEditsOf, insTourStep, List.append_assoc] using hB₁₂
  · have : r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 16 ∧ r ≠ 18 ∧ r ≠ 29 ∧ r ≠ 20 ∧ r ≠ 9 ∧ r ≠ 14 ∧ r ≠ 17 ∧
        r ≠ 21 ∧ r ≠ 22 ∧ r ≠ 27 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert hr <;> decide
    obtain ⟨a, b, c, d, e', f, g', h', k, l, m, n⟩ := this
    exact hreg r a b c d e' f g' h' k l m n
  · rw [ho₁₃ 14 (by omega), ho₁₂ 14 (by omega) (by omega) (by omega) (by omega) (by omega),
      ho₁₁ 14 (by omega) (by omega) (by omega) (by omega) (by omega), ho₁₀ 14 (by omega), h14₉]
    omega
  · rw [ho₁₃ 16 (by omega), h16₁₂]; omega
  · rw [ho₁₃ 17 (by omega), ho₁₂ 17 (by omega) (by omega) (by omega) (by omega) (by omega),
      ho₁₁ 17 (by omega) (by omega) (by omega) (by omega) (by omega), h17₁₀]
    omega
  · rw [ho₁₃ 18 (by omega), h18₁₂]
    simp only [List.length_append, List.length_cons, List.length_nil, insEditsTour_length,
      List.length_take]
    omega
  · rw [h20₁₃]
  · rw [hreg 26 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), h26]
  · rw [ho₁₃ 7 (by omega)]; rw [g7₁₀] at hcA1; omega
  · rw [ho₁₃ 7 (by omega)]; rw [g7₁₀] at hcA2
    have : cur₀ + 4 * (i + 1) * S.querySpace = cur₀ + 4 * i * S.querySpace + 4 * S.querySpace := by
      ring
    omega
  · have hphi₁₀ : T.rep.phi A.tourH tx st₁₀.mem = φ := by
      rw [hm₁₀, hm₉, hp₈, hp₇, hp₆, hp₅, hp₄, hm₃, hm₂, hm₁, hphi]
    rw [hphi₁₀] at hcostA
    simp only [osBumpB, osKey0, osKey1, Expr.size_reg, Expr.size_bin, Expr.size_const,
      Expr.size_load, argsSize] at hcostA hcostB hc₈ ⊢
    omega

/-- **The insertions.** For the entering edges `insL`, the phase writes the batch of their
insertions and the edits `insEditsTour`, applies the batch to the stored graph, and marks the
ends of the entering edges. -/
theorem osInsPhase_runs (hC : SCtx T A tx₀) {au : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    {G₀ : MGraph} {U₀ : List Update} {E₀ : List OrdEdit} {s₀ : OutTourAbs} {insL : List ℕ}
    {tl hd : ℕ → ℕ} {bp₀ ep₀ cur₀ : ℕ} {st : State} {tx : T.rep.τ}
    (hG₀ : G₀ = S₀.applyBatch U₀)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w) (htour : A.tourH < 2 ^ w)
    (hins : OutInsAt mem₀ A.insPtr insL tl hd)
    (hfree : OutCellsFree A.insPtr (1 + 3 * insL.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a))
    (hval : ∀ j (hj : j < insL.length),
      (G₀.applyBatch ((insL.take j).map fun e => Update.insert e (tl e) (hd e))).UpdateIsValid
        (.insert insL[j] (tl insL[j]) (hd insL[j])))
    (hcap : ∀ e ∈ insL, e < eCap) (hends : ∀ e ∈ insL, tl e < vCap ∧ hd e < vCap)
    (hcord : ∀ e ∈ insL, (e, true) ∈ s₀.cord (tl e) ∧ (e, false) ∈ s₀.cord (hd e))
    (hbR : bp₀ + 4 * insL.length ≤ A.e0) (heR : ep₀ + 8 * insL.length ≤ A.t0)
    (hroom : cur₀ + 4 * insL.length * S.querySpace < 2 ^ w)
    (hB : SBase T A tx₀ mem₀ S₀ G₀ U₀ E₀ bp₀ ep₀ cur₀ s₀ tx st.mem)
    (hR : SRegs st A vCap eCap) (h7 : st.regs 7 = cur₀) (h14 : st.regs 14 = bp₀)
    (h16 : st.regs 16 = ep₀) (h17 : st.regs 17 = U₀.length) (h18 : st.regs 18 = E₀.length) :
    ∃ st' c, Runs w p ω (osInsPhase nm sm au) st .normal st' c ∧
      ∃ φ', OsInsInv T A tx₀ mem₀ S₀ G₀ U₀ E₀ s₀ insL tl hd bp₀ ep₀ cur₀ insL.length φ' st' ∧
        c + φ' ≤ insL.length * (4 * (S.mul * ordStoreLog eCap) + 3100) + 20 +
          T.rep.phi A.tourH tx st.mem := by
  have hkey := rs_key_lt hw
  have hR' := hR
  obtain ⟨-, -, -, -, r4, -, -, -, -, -, -, -, -, -, -, -⟩ := hR'
  have hfr := hfree
  obtain ⟨hfr1, hfr2⟩ := hfr
  obtain ⟨st₁, hr₁, hm₁, h20₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 20)
    (e := .const 0) (st := st) (Expr.eval_const (by omega))
  have hcnt' : st₁.mem A.insPtr = insL.length := by
    rw [hm₁, hB.mem_eq (by omega) (by simpa using hfr2 0 (by omega))]; exact hins.1
  obtain ⟨st₂, hr₂, hm₂, h26₂, ho₂⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 26)
    (e := .load (.reg 4)) (st := st₁)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by rw [ho₁ 4 (by omega), r4])) hcnt')
  have hI₀ : OsInsInv T A tx₀ mem₀ S₀ G₀ U₀ E₀ s₀ insL tl hd bp₀ ep₀ cur₀ 0
      (T.rep.phi A.tourH tx st.mem) st₂ := by
    refine ⟨tx, ?_, hR.of_fixed fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, h26₂, Nat.zero_le _, ?_, ?_,
      ?_⟩
    · have : st₂.regs 7 = cur₀ := by rw [ho₂ _ (by omega), ho₁ _ (by omega), h7]
      rw [hm₂, hm₁, this]
      simpa [insEditsTour, insTourAfter, MGraph.applyBatch] using hB
    · rw [ho₂ r (by rintro rfl; revert hr; decide), ho₁ r (by rintro rfl; revert hr; decide)]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h14]; rfl
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h16]; rfl
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h17]; rfl
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h18]; rfl
    · rw [ho₂ _ (by omega), h20₁]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h7]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h7]; simp
    · rw [hm₂, hm₁]
  have hloop := runs_loop_amort (w := w) (p := p) (ω := ω) (e := .bin .lt (.reg 20) (.reg 26))
    (body := osInsIter nm sm au)
    (Inv := fun a st => OsInsInv T A tx₀ mem₀ S₀ G₀ U₀ E₀ s₀ insL tl hd bp₀ ep₀ cur₀ a.1 a.2 st)
    (Fin := fun o st r => o = .normal ∧
      OsInsInv T A tx₀ mem₀ S₀ G₀ U₀ E₀ s₀ insL tl hd bp₀ ep₀ cur₀ insL.length r st)
    (fun a => insL.length - a.1)
    (fun a => (insL.length - a.1) * (4 * (S.mul * ordStoreLog eCap) + 3100) + a.2 + 5)
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
    have hin : i = insL.length := by
      simp only [h20', h26'] at hc
      split_ifs at hc <;> omega
    subst hin
    refine ⟨φ, ⟨rfl, hI⟩, ?_⟩
    simp only [Expr.size_bin, Expr.size_reg, Nat.sub_self, Nat.zero_mul]; omega
  · rintro ⟨i, φ⟩ st hI hc
    have hI' := hI
    obtain ⟨-, -, -, -, -, -, -, h20', h26', -⟩ := hI'
    have hi : i < insL.length := by
      simp only [h20', h26'] at hc
      split_ifs at hc with h
      · exact h
      · omega
    obtain ⟨st', c, φ', hr, hI'', hc'⟩ := osInsIter_runs hC hau hG₀ hw ht0 htour hins hfree hval
      hcap hends hcord hbR heR hroom hI hi
    refine ⟨.normal, st', c, hr, (i + 1, φ'), hI'', by simp only; omega, ?_⟩
    simp only [Expr.size_reg, Expr.size_bin]
    have : insL.length - i = (insL.length - (i + 1)) + 1 := by omega
    rw [this, add_mul, one_mul]
    omega

end Ins

end MinCostFlow.SparseCore.Program
