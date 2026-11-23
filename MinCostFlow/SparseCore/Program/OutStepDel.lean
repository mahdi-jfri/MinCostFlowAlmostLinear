module

public import MinCostFlow.SparseCore.Program.OutStepCalls
public import MinCostFlow.SparseCore.Program.OutResetDel

/-!
# The deletions of the output step

The first phase of the output step (`osDelPhase`) goes through the leaving edges `delL`. For each
edge `e` it writes the batch record `[1, e]`, applies it to the stored graph, writes the edit
`[0, e]`, and unmarks the two ends of `e` when its flag is `1`. This file proves that the phase
runs (`osDelPhase_runs`): afterwards the stored graph is the old one without the edges of
`delL`, the batch region holds `delL.map Update.delete`, the edit region holds
`delL.map OrdEdit.dropEdge`, and the marked ends are the ends of the remaining edges.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program MinCostFlow.LowStretch

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ}
  {mem₀ : ℕ → ℕ} {S₀ G : MGraph} {U : List Update} {E : List OrdEdit} {bp ep cur : ℕ}
  {s : OutTourAbs} {tx : T.rep.τ}

/-- **A store** into a free cell of `[h, t0)`. -/
theorem os_store (hC : SCtx T A tx₀) {st : State} {a e : Expr} {x v : ℕ}
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st.mem)
    (ha : a.eval w st = some x) (he : e.eval w st = some v)
    (hx : A.h ≤ x ∧ x < A.t0 ∧ ¬ (A.h + 5 ≤ x ∧ x < bp) ∧ ¬ (A.e0 + 1 ≤ x ∧ x < ep)) :
    ∃ st', Runs w p ω (.store a e) st .normal st' (a.size + e.size + 1) ∧
      SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st'.mem ∧
      T.rep.phi A.tourH tx st'.mem = T.rep.phi A.tourH tx st.mem ∧
      st'.mem = Function.update st.mem x v ∧ st'.regs = st.regs := by
  obtain ⟨st', hr, hm, hrg⟩ := step_store (p := p) (ω := ω) ha he
  obtain ⟨hB', hphi⟩ := hB.of_store hC (v := v) hx
  exact ⟨st', hr, hm ▸ hB', hm ▸ hphi, hm, hrg⟩

/-- A word of the input below `h`, outside the stored graph and the start tour, still holds its
start value. -/
theorem SBase.mem_eq {mem : ℕ → ℕ} (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx mem) {a : ℕ}
    (ha : a < A.h) (hn : ¬ ((outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a)) :
    mem a = mem₀ a :=
  hB.2.2.2.2.1 a ha (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))

/-- The marks after unmarking both ends of an edge `e` whose ends are in the core lists. -/
theorem outMarksOf_unmark {s : OutTourAbs} {cord : ℕ → List End} {E : Finset ℕ} {e : ℕ}
    (h : OutMarksOf s cord E) :
    OutMarksOf ((s.setMark (e, true) 0).setMark (e, false) 0) cord (E.erase e) := by
  refine ⟨h.1, fun z => ?_⟩
  rw [mem_unmark_both, h.2 z, Finset.mem_erase]
  tauto

/-- The marks stay when the ends of `e` are in no core list. -/
theorem outMarksOf_erase_of_not_mem {s : OutTourAbs} {cord : ℕ → List End} {E : Finset ℕ}
    {e : ℕ} (h : OutMarksOf s cord E) (he : ∀ b v, (e, b) ∉ cord v) :
    OutMarksOf s cord (E.erase e) := by
  refine ⟨h.1, fun z => ?_⟩
  rw [h.2 z, Finset.mem_erase]
  constructor
  · rintro ⟨⟨v, hv⟩, hz⟩
    refine ⟨⟨v, hv⟩, fun hze => ?_, hz⟩
    obtain ⟨z1, z2⟩ := z
    simp only at hze
    subst hze
    exact he z2 v hv
  · rintro ⟨hv, -, hz⟩
    exact ⟨hv, hz⟩

/-- Deleting the edges of a list keeps the vertices and removes the edges of the list. -/
theorem applyBatch_dels_E (G : MGraph) : ∀ l : List ℕ,
    (G.applyBatch (l.map Update.delete)).E = G.E \ l.toFinset ∧
      (G.applyBatch (l.map Update.delete)).V = G.V
  | [] => by simp [MGraph.applyBatch]
  | e :: l => by
    obtain ⟨h1, h2⟩ := applyBatch_dels_E (G.applyUpdate (.delete e)) l
    refine ⟨?_, ?_⟩
    · show ((G.applyUpdate (.delete e)).applyBatch (l.map Update.delete)).E = _
      rw [h1]
      ext f
      simp [MGraph.applyUpdate]
      tauto
    · show ((G.applyUpdate (.delete e)).applyBatch (l.map Update.delete)).V = _
      rw [h2]; rfl

theorem applyBatch_snoc (G : MGraph) (U : List Update) (u : Update) :
    G.applyBatch (U ++ [u]) = (G.applyBatch U).applyUpdate u := by
  induction U generalizing G with
  | nil => rfl
  | cons v U ih => exact ih (G.applyUpdate v)

/-! ## One deletion -/

section Del

variable (T A tx₀ mem₀ S₀) in
/-- The state after `i` deletions, with potential `φ`. -/
def DelInv (cord : ℕ → List End) (E₀ : Finset ℕ) (delL : List ℕ) (cur₀ i φ : ℕ) (st : State) : Prop :=
  ∃ s tx, SBase T A tx₀ mem₀ S₀ (S₀.applyBatch ((delL.take i).map Update.delete))
      ((delL.take i).map Update.delete) ((delL.take i).map OrdEdit.dropEdge)
      (A.h + 5 + 2 * i) (A.e0 + 1 + 2 * i) (st.regs 7) s tx st.mem ∧
    SRegs st A vCap eCap ∧ st.regs 14 = A.h + 5 + 2 * i ∧ st.regs 16 = A.e0 + 1 + 2 * i ∧
    st.regs 17 = i ∧ st.regs 18 = i ∧ st.regs 20 = i ∧ st.regs 26 = delL.length ∧
    i ≤ delL.length ∧ OutMarksOf s cord (E₀ \ (delL.take i).toFinset) ∧
    cur₀ ≤ st.regs 7 ∧ st.regs 7 ≤ cur₀ + 2 * i * S.querySpace ∧
    T.rep.phi A.tourH tx st.mem = φ

/-- **One deletion.** -/
theorem osDelIter_runs (hC : SCtx T A tx₀) {au : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    {cord : ℕ → List End} {delL : List ℕ} {E' E₀ : Finset ℕ} {cur₀ i φ : ℕ} {st : State}
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w) (htour : A.tourH < 2 ^ w)
    (hdel : OutDelAt mem₀ A.delPtr delL E')
    (hfree : OutCellsFree A.delPtr (1 + 2 * delL.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a))
    (hnd : delL.Nodup) (hsub : ∀ e ∈ delL, e ∈ S₀.E) (hcap : ∀ e ∈ delL, e < eCap)
    (hflag1 : ∀ e ∈ delL, e ∈ E' → ∀ b, ∃ v < vCap, (e, b) ∈ cord v)
    (hflag0 : ∀ e ∈ delL, e ∉ E' → ∀ b v, (e, b) ∉ cord v)
    (heR : A.e0 + 1 + 2 * delL.length ≤ A.t0)
    (hroom : cur₀ + 2 * delL.length * S.querySpace < 2 ^ w)
    (hI : DelInv T A tx₀ mem₀ S₀ cord E₀ delL cur₀ i φ st) (hi : i < delL.length) :
    ∃ st' c φ', Runs w p ω (osDelIter sm au) st .normal st' c ∧
      DelInv T A tx₀ mem₀ S₀ cord E₀ delL cur₀ (i + 1) φ' st' ∧
      c + φ' ≤ 2 * (S.mul * ordStoreLog eCap) + 1600 + φ := by
  obtain ⟨s, tx, hB, hR, h14, h16, h17, h18, h20, h26, -, hmk, hc1, hc2, hphi⟩ := hI
  have hR' := hR
  obtain ⟨r0, r1, r2, -, -, -, r6, r10, -, -, -, -, -, -, -, -⟩ := hR'
  have hgh := hC.2.2.1
  have hq := S.querySpace_ge
  set e := delL[i] with he_def
  have he : e ∈ delL := List.getElem_mem hi
  have heE := hsub e he
  have hecap := hcap e he
  have hkey := rs_key_lt hw
  have h16w : 16 ≤ 2 ^ w := rs_sixteen_of_cap hw (by omega)
  have hR0 : A.e0 = A.h + 4 + A.R := rfl
  have ht0e : A.t0 = A.e0 + A.R := rfl
  obtain ⟨hfr1, hfr2⟩ := hfree
  obtain ⟨-, hdel2⟩ := hdel
  obtain ⟨hdE, hdF⟩ := hdel2 i hi
  rw [List.getD_eq_getElem _ _ hi] at hdE hdF
  -- the two input words
  have hm1 : st.mem (A.delPtr + 1 + (i + i)) = e := by
    rw [hB.mem_eq (by omega) (by have := hfr2 (1 + 2 * i) (by omega); rwa [show A.delPtr + (1 + 2 * i) =
      A.delPtr + 1 + (i + i) by omega] at this), show i + i = 2 * i by omega]
    exact hdE
  have hm2 : st.mem (A.delPtr + 2 + (i + i)) = if e ∈ E' then 1 else 0 := by
    rw [hB.mem_eq (by omega) (by have := hfr2 (2 + 2 * i) (by omega); rwa [show A.delPtr + (2 + 2 * i) =
      A.delPtr + 2 + (i + i) by omega] at this), show i + i = 2 * i by omega]
    exact hdF
  have hqi : 2 * i * S.querySpace + 2 * S.querySpace ≤ 2 * delL.length * S.querySpace := by
    have := Nat.mul_le_mul_right S.querySpace (show 2 * i + 2 ≤ 2 * delL.length by omega)
    rw [Nat.add_mul] at this; exact this
  have hii : (Expr.bin .add (.reg 20) (.reg 20)).eval w st = some (i + i) :=
    Expr.eval_add (Expr.eval_reg_of_eq h20) (Expr.eval_reg_of_eq h20) (by omega)
  obtain ⟨st₁, hr₁, hm₁, h21₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 21)
    (e := .load (.bin .add (.bin .add (.reg 2) (.const 1)) (.bin .add (.reg 20) (.reg 20))))
    (st := st)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq r2)
      (Expr.eval_const (k := 1) (by omega)) (by omega)) hii (by omega)) hm1)
  have hii₁ : (Expr.bin .add (.reg 20) (.reg 20)).eval w st₁ = some (i + i) :=
    Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₁ 20 (by omega), h20]))
      (Expr.eval_reg_of_eq (by rw [ho₁ 20 (by omega), h20])) (by omega)
  obtain ⟨st₂, hr₂, hm₂, h22₂, ho₂⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 22)
    (e := .load (.bin .add (.bin .add (.reg 2) (.const 2)) (.bin .add (.reg 20) (.reg 20))))
    (st := st₁)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq
      (by rw [ho₁ 2 (by omega), r2])) (Expr.eval_const (k := 2) (by omega)) (by omega)) hii₁ (by omega))
      (by rw [hm₁, hm2]))
  -- registers so far
  have g14₂ : st₂.regs 14 = A.h + 5 + 2 * i := by rw [ho₂ _ (by omega), ho₁ _ (by omega), h14]
  have g21₂ : st₂.regs 21 = e := by rw [ho₂ _ (by omega), h21₁]
  have hB₂ : SBase T A tx₀ mem₀ S₀ (S₀.applyBatch ((delL.take i).map Update.delete))
      ((delL.take i).map Update.delete) ((delL.take i).map OrdEdit.dropEdge)
      (A.h + 5 + 2 * i) (A.e0 + 1 + 2 * i) (st.regs 7) s tx st₂.mem := by rw [hm₂, hm₁]; exact hB
  -- the batch record `[1, e]`
  obtain ⟨st₃, hr₃, hB₃, hp₃, hm₃, hg₃⟩ := os_store (p := p) (ω := ω) (e := .const 1) hC hB₂
    (Expr.eval_reg_of_eq g14₂) (Expr.eval_const (by omega)) ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₄, hr₄, hB₄, hp₄, hm₄, hg₄⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 1)) (e := .reg 21) hC hB₃
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₃, g14₂])) (Expr.eval_const (by omega))
      (by omega)) (Expr.eval_reg_of_eq (by rw [hg₃, g21₂]))
    ⟨by omega, by omega, by omega, by omega⟩
  set G := S₀.applyBatch ((delL.take i).map Update.delete) with hG
  have hGE := applyBatch_dels_E S₀ (delL.take i)
  have heG : e ∈ G.E := by
    rw [hGE.1, Finset.mem_sdiff]
    refine ⟨heE, fun h => ?_⟩
    rw [List.mem_toFinset] at h
    obtain ⟨j, hj, hje⟩ := List.mem_take_iff_getElem.mp h
    have := (List.Nodup.getElem_inj_iff hnd).mp hje
    omega
  have hu₄ : UpdateAt st₄.mem (A.h + 5 + 2 * i) G (.delete e) 2 := by
    refine ⟨rfl, fun j hj => ?_⟩
    simp only [List.length_cons, List.length_nil] at hj
    rw [hm₄, hm₃]
    interval_cases j
    · simp only [Nat.add_zero]
      rw [Function.update_of_ne (by omega), Function.update_self]; rfl
    · rw [Function.update_self]; rfl
  obtain ⟨st₅, c₅, hr₅, hB₅, hp₅, hfr₅, ho₅, hc₅⟩ := os_apply (ω := ω) hC hau hB₄
    (by rw [hg₄, hg₃, ho₂ _ (by omega), ho₁ _ (by omega), r10])
    (by rw [hg₄, hg₃, g14₂]) hu₄ heG trivial (by omega)
    (fun j hj => by rw [show j < 2 ↔ j = 0 ∨ j = 1 by omega] at hj
                    rcases hj with rfl | rfl
                    · rw [hu₄.2 0 (by simp)]; simp only [List.getElem_cons_zero]; omega
                    · rw [hu₄.2 1 (by simp)]; simp only [List.getElem_cons_succ,
                        List.getElem_cons_zero]; omega)
    h16w (by omega) (by omega)
  have hu₅ : UpdateAt st₅.mem (A.h + 5 + 2 * i) G (.delete e) 2 :=
    UpdateAt.of_agree hu₄ (fun j _ => hfr₅ _ (Or.inr (by omega)))
  -- bump the batch pointer
  obtain ⟨st₆, hr₆, hm₆, h14₆, ho₆⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 14)
    (e := .bin .add (.reg 14) (.const 2)) (st := st₅)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₅ _ (by omega), hg₄, hg₃, g14₂]))
      (Expr.eval_const (by omega)) (by omega))
  obtain ⟨st₇, hr₇, hm₇, h17₇, ho₇⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 17)
    (e := .bin .add (.reg 17) (.const 1)) (st := st₆)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₆ _ (by omega), ho₅ _ (by omega), hg₄, hg₃,
      ho₂ _ (by omega), ho₁ _ (by omega), h17])) (Expr.eval_const (by omega)) (by omega))
  have hB₇ := (show SBase T A tx₀ mem₀ S₀ (G.applyUpdate (.delete e))
      ((delL.take i).map Update.delete) ((delL.take i).map OrdEdit.dropEdge)
      (A.h + 5 + 2 * i) (A.e0 + 1 + 2 * i) (st.regs 7) s tx st₇.mem by
    rw [hm₇, hm₆]; exact hB₅).push_batch (by rw [hm₇, hm₆]; exact hu₅) (by omega)
  -- the edit `[0, e]`
  have g16₇ : st₇.regs 16 = A.e0 + 1 + 2 * i := by
    rw [ho₇ _ (by omega), ho₆ _ (by omega), ho₅ _ (by omega), hg₄, hg₃, ho₂ _ (by omega),
      ho₁ _ (by omega), h16]
  have g21₇ : st₇.regs 21 = e := by
    rw [ho₇ _ (by omega), ho₆ _ (by omega), ho₅ _ (by omega), hg₄, hg₃, g21₂]
  obtain ⟨st₈, hr₈, hB₈, hp₈, hm₈, hg₈⟩ := os_store (p := p) (ω := ω) (e := .const 0) hC hB₇
    (Expr.eval_reg_of_eq g16₇) (Expr.eval_const (by omega)) ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₉, hr₉, hB₉, hp₉, hm₉, hg₉⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 16) (.const 1)) (e := .reg 21) hC hB₈
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₈, g16₇])) (Expr.eval_const (by omega))
      (by omega)) (Expr.eval_reg_of_eq (by rw [hg₈, g21₇]))
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₁₀, hr₁₀, hm₁₀, h16₁₀, ho₁₀⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 16)
    (e := .bin .add (.reg 16) (.const 2)) (st := st₉)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₉, hg₈, g16₇]))
      (Expr.eval_const (by omega)) (by omega))
  obtain ⟨st₁₁, hr₁₁, hm₁₁, h18₁₁, ho₁₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 18)
    (e := .bin .add (.reg 18) (.const 1)) (st := st₁₀)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₁₀ _ (by omega), hg₉, hg₈, ho₇ _ (by omega),
      ho₆ _ (by omega), ho₅ _ (by omega), hg₄, hg₃, ho₂ _ (by omega), ho₁ _ (by omega), h18]))
      (Expr.eval_const (by omega)) (by omega))
  have hd : decodeOrdEdit st₁₁.mem (A.e0 + 1 + 2 * i) = (.dropEdge e, 2) := by
    rw [hm₁₁, hm₁₀, hm₉, hm₈]
    exact decodeOrdEdit_drop (by simp [Function.update_of_ne (show A.e0 + 1 + 2 * i ≠
      A.e0 + 1 + 2 * i + 1 by omega)]) (by simp)
  have hB₁₁ := (show SBase T A tx₀ mem₀ S₀ (G.applyUpdate (.delete e))
      ((delL.take i).map Update.delete ++ [.delete e]) ((delL.take i).map OrdEdit.dropEdge)
      (A.h + 5 + 2 * i + 2) (A.e0 + 1 + 2 * i) (st.regs 7) s tx st₁₁.mem by
    rw [hm₁₁, hm₁₀]; exact hB₉).push_edit hd (by
      rw [hm₁₁, hm₁₀, hm₉, hm₈]; simp)
      (by omega)
  -- registers after the records
  have hreg₁₁ : ∀ r, r ≠ 7 → r ≠ 8 → st₁₁.regs r = if r = 14 then A.h + 5 + 2 * i + 2 else
      if r = 16 then A.e0 + 1 + 2 * i + 2 else if r = 17 then i + 1 else if r = 18 then i + 1 else
      if r = 21 then e else if r = 22 then (if e ∈ E' then 1 else 0) else
      if r = 9 then st₅.regs 9 else st.regs r := by
    intro r h7 h8
    by_cases a18 : r = 18
    · subst a18; rw [h18₁₁]; simp
    rw [ho₁₁ r a18]
    by_cases a16 : r = 16
    · subst a16; rw [h16₁₀]; simp
    rw [ho₁₀ r a16, hg₉, hg₈]
    by_cases a17 : r = 17
    · subst a17; rw [h17₇]; simp
    rw [ho₇ r a17]
    by_cases a14 : r = 14
    · subst a14; rw [h14₆]; simp
    rw [ho₆ r a14]
    by_cases a9 : r = 9
    · subst a9; simp
    rw [ho₅ r a9, hg₄, hg₃]
    by_cases a22 : r = 22
    · subst a22; rw [h22₂]; simp
    rw [ho₂ r a22]
    by_cases a21 : r = 21
    · subst a21; rw [h21₁]; simp
    rw [ho₁ r a21]
    simp [a14, a16, a17, a18, a21, a22, a9]
  have g7₁₁ : st₁₁.regs 7 = st.regs 7 := by
    rw [ho₁₁ _ (by omega), ho₁₀ _ (by omega), hg₉, hg₈, ho₇ _ (by omega), ho₆ _ (by omega),
      ho₅ _ (by omega), hg₄, hg₃, ho₂ _ (by omega), ho₁ _ (by omega)]
  have hphi₁₁ : T.rep.phi A.tourH tx st₁₁.mem = φ := by
    rw [hm₁₁, hm₁₀, hp₉, hp₈, hm₇, hm₆, hp₅, hp₄, hp₃, hm₂, hm₁, hphi]
  -- the marks
  have hE' : E₀ \ (delL.take (i + 1)).toFinset = (E₀ \ (delL.take i).toFinset).erase e := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.toFinset_append]
    ext f
    simp only [Finset.mem_sdiff, Finset.mem_union, List.mem_toFinset, List.mem_singleton,
      Finset.mem_erase, he_def]
    tauto
  -- the flag
  obtain ⟨st₁₃, c₁₂, s', tx', hr₁₂, hB₁₃, hreg₁₃, hmk', hcA, hcB, hcost₁₂⟩ :
      ∃ st₁₃ c₁₂ s' tx',
        Runs w p ω (.cond (.reg 22) (.seq (rsMark sm 0 osKey0) (rsMark sm 0 osKey1)) .nop) st₁₁
          .normal st₁₃ c₁₂ ∧
        SBase T A tx₀ mem₀ S₀ (G.applyUpdate (.delete e))
          ((delL.take i).map Update.delete ++ [.delete e])
          ((delL.take i).map OrdEdit.dropEdge ++ [.dropEdge e])
          (A.h + 5 + 2 * i + 2) (A.e0 + 1 + 2 * i + 2) (st₁₃.regs 7) s' tx' st₁₃.mem ∧
        (∀ r, r ≠ 7 → r ≠ 8 → st₁₃.regs r = st₁₁.regs r) ∧
        OutMarksOf s' cord (E₀ \ (delL.take (i + 1)).toFinset) ∧
        st.regs 7 ≤ st₁₃.regs 7 ∧ st₁₃.regs 7 ≤ st.regs 7 + 2 * S.querySpace ∧
        c₁₂ + T.rep.phi A.tourH tx' st₁₃.mem ≤ 2 * (S.mul * ordStoreLog eCap) + 30 + φ := by
    rw [hE']
    by_cases heE' : e ∈ E'
    · have h22 : st₁₁.regs 22 = 1 := by rw [hreg₁₁ 22 (by omega) (by omega)]; simp [heE']
      have h21 : st₁₁.regs 21 = e := by rw [hreg₁₁ 21 (by omega) (by omega)]; simp
      obtain ⟨v₀, hv₀, hx₀⟩ := hflag1 e he heE' true
      obtain ⟨v₁, hv₁, hx₁⟩ := hflag1 e he heE' false
      have hcord : s.cord = cord := hmk.1
      obtain ⟨st₁₂, c₁, tx₁, hrA, hBA, hkA, hoA, hA1, hA2, hcA⟩ := os_mark (ω := ω) (sm := sm)
        (flag := 0) (key := e + e) (v := v₀) (keyE := osKey0) hC hB₁₁
        (by rw [hreg₁₁ 1 (by omega) (by omega)]; simpa using r1) g7₁₁
        (Expr.eval_add (Expr.eval_reg_of_eq h21) (Expr.eval_reg_of_eq h21) (by omega))
        (by omega) (by omega) (by omega) hv₀ (by rw [endOfKey_two_mul, hcord]; exact hx₀) htour
        (by omega)
      rw [endOfKey_two_mul] at hBA
      have h21' : st₁₂.regs 21 = e := by rw [hoA 21 (by omega) (by omega), h21]
      obtain ⟨st₁₃, c₂, tx₂, hrB, hBB, hkB, hoB, hB1, hB2, hcB⟩ := os_mark (ω := ω) (sm := sm)
        (flag := 0) (key := e + e + 1) (v := v₁) (keyE := osKey1) hC hBA
        (by rw [hoA 1 (by omega) (by omega), hreg₁₁ 1 (by omega) (by omega)]; simpa using r1) rfl
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h21') (Expr.eval_reg_of_eq h21')
          (by omega)) (Expr.eval_const (by omega)) (by omega))
        (by omega) (by omega) (by omega) hv₁
        (by rw [endOfKey_two_mul_add_one]; show (e, false) ∈ (s.setMark (e, true) 0).cord v₁
            rw [show (s.setMark (e, true) 0).cord = s.cord from rfl, hcord]; exact hx₁) htour
        (by omega)
      rw [endOfKey_two_mul_add_one] at hBB
      refine ⟨st₁₃, _, _, tx₂, step_cond_true (Expr.eval_reg_of_eq h22) one_ne_zero
        (runs_seq_normal hrA hrB), hBB, fun r h7 h8 => by rw [hoB r h7 h8, hoA r h7 h8],
        outMarksOf_unmark hmk, by omega, by omega, ?_⟩
      simp only [osKey0, osKey1, Expr.size_reg, Expr.size_bin, Expr.size_const] at hcA hcB ⊢
      rw [hphi₁₁] at hcA
      omega
    · refine ⟨st₁₁, _, s, tx, step_cond_false (Expr.eval_reg_of_eq ?_) step_nop,
        by rw [g7₁₁]; exact hB₁₁, fun _ _ _ => rfl, outMarksOf_erase_of_not_mem hmk
          (hflag0 e he heE'), by omega, by omega, ?_⟩
      · rw [hreg₁₁ 22 (by omega) (by omega)]; simp [heE']
      · rw [hphi₁₁]; simp only [Expr.size_reg]; omega
  -- the last step
  have g20₁₃ : st₁₃.regs 20 = i := by
    rw [hreg₁₃ 20 (by omega) (by omega), hreg₁₁ 20 (by omega) (by omega)]; simpa using h20
  obtain ⟨st₁₄, hr₁₄, hm₁₄, h20₁₄, ho₁₄⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 20)
    (e := .bin .add (.reg 20) (.const 1)) (st := st₁₃)
    (Expr.eval_add (Expr.eval_reg_of_eq g20₁₃) (Expr.eval_const (k := 1) (by omega)) (by omega))
  have hreg : ∀ r, r ≠ 7 → r ≠ 8 → r ≠ 20 → st₁₄.regs r = st₁₁.regs r := fun r h7 h8 h20' => by
    rw [ho₁₄ r h20', hreg₁₃ r h7 h8]
  refine ⟨st₁₄, _, T.rep.phi A.tourH tx' st₁₃.mem,
    runs_seq_normal hr₁ (runs_seq_normal hr₂ (runs_seq_normal hr₃ (runs_seq_normal hr₄
      (runs_seq_normal hr₅ (runs_seq_normal (runs_seq_normal hr₆ hr₇) (runs_seq_normal hr₈
        (runs_seq_normal hr₉ (runs_seq_normal (runs_seq_normal hr₁₀ hr₁₁)
          (runs_seq_normal hr₁₂ hr₁₄))))))))), ⟨s', tx', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega,
    hmk', ?_, ?_, by rw [hm₁₄]⟩, ?_⟩
  · have h7 : st₁₄.regs 7 = st₁₃.regs 7 := ho₁₄ 7 (by omega)
    rw [hm₁₄, h7, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
    simp only [List.map_append, List.map_cons, List.map_nil, ← he_def]
    rw [show A.h + 5 + 2 * (i + 1) = A.h + 5 + 2 * i + 2
      by omega, show A.e0 + 1 + 2 * (i + 1) = A.e0 + 1 + 2 * i + 2 by omega,
      show S₀.applyBatch ((delL.take i).map Update.delete ++ [Update.delete e]) =
        G.applyUpdate (.delete e) from applyBatch_snoc _ _ _]
    exact hB₁₃
  · refine hR.of_fixed fun r hr => ?_
    have h7 : r ≠ 7 := by rintro rfl; revert hr; decide
    have h8 : r ≠ 8 := by rintro rfl; revert hr; decide
    have h20' : r ≠ 20 := by rintro rfl; revert hr; decide
    rw [hreg r h7 h8 h20', hreg₁₁ r h7 h8]
    have : r ≠ 14 ∧ r ≠ 16 ∧ r ≠ 17 ∧ r ≠ 18 ∧ r ≠ 21 ∧ r ≠ 22 ∧ r ≠ 9 := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> revert hr <;> decide
    simp [this]
  · rw [hreg 14 (by omega) (by omega) (by omega), hreg₁₁ 14 (by omega) (by omega)]; simp; omega
  · rw [hreg 16 (by omega) (by omega) (by omega), hreg₁₁ 16 (by omega) (by omega)]; simp; omega
  · rw [hreg 17 (by omega) (by omega) (by omega), hreg₁₁ 17 (by omega) (by omega)]; simp
  · rw [hreg 18 (by omega) (by omega) (by omega), hreg₁₁ 18 (by omega) (by omega)]; simp
  · rw [h20₁₄]
  · rw [hreg 26 (by omega) (by omega) (by omega), hreg₁₁ 26 (by omega) (by omega)]; simpa using h26
  · rw [ho₁₄ 7 (by omega)]; omega
  · rw [ho₁₄ 7 (by omega)]
    have : cur₀ + 2 * (i + 1) * S.querySpace = cur₀ + 2 * i * S.querySpace + 2 * S.querySpace := by
      ring
    omega
  · simp only [osBumpB, osBumpE, Expr.size_reg, Expr.size_bin, Expr.size_const, Expr.size_load]
    omega

/-- **The deletions.** From the frame with empty records, the phase writes the batch
`delL.map Update.delete` and the edits `delL.map OrdEdit.dropEdge`, applies the batch to the
stored graph, and unmarks the ends of the deleted edges. -/
theorem osDelPhase_runs (hC : SCtx T A tx₀) {au : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    {cord : ℕ → List End} {delL : List ℕ} {E' E₀ : Finset ℕ} {cur₀ : ℕ} {st : State}
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w) (htour : A.tourH < 2 ^ w)
    (hdel : OutDelAt mem₀ A.delPtr delL E')
    (hfree : OutCellsFree A.delPtr (1 + 2 * delL.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a))
    (hnd : delL.Nodup) (hsub : ∀ e ∈ delL, e ∈ S₀.E) (hcap : ∀ e ∈ delL, e < eCap)
    (hflag1 : ∀ e ∈ delL, e ∈ E' → ∀ b, ∃ v < vCap, (e, b) ∈ cord v)
    (hflag0 : ∀ e ∈ delL, e ∉ E' → ∀ b v, (e, b) ∉ cord v)
    (heR : A.e0 + 1 + 2 * delL.length ≤ A.t0)
    (hroom : cur₀ + 2 * delL.length * S.querySpace < 2 ^ w)
    (hB : SBase T A tx₀ mem₀ S₀ S₀ [] [] (A.h + 5) (A.e0 + 1) cur₀ s tx st.mem)
    (hR : SRegs st A vCap eCap) (h7 : st.regs 7 = cur₀) (h14 : st.regs 14 = A.h + 5)
    (h16 : st.regs 16 = A.e0 + 1) (h17 : st.regs 17 = 0) (h18 : st.regs 18 = 0)
    (hmk : OutMarksOf s cord E₀) :
    ∃ st' c, Runs w p ω (osDelPhase sm au) st .normal st' c ∧
      ∃ φ', DelInv T A tx₀ mem₀ S₀ cord E₀ delL cur₀ delL.length φ' st' ∧
        c + φ' ≤ delL.length * (2 * (S.mul * ordStoreLog eCap) + 1700) + 20 +
          T.rep.phi A.tourH tx st.mem := by
  have hR' := hR
  obtain ⟨-, -, r2, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hR'
  have hfr := hfree
  obtain ⟨hfr1, hfr2⟩ := hfr
  obtain ⟨st₁, hr₁, hm₁, h20₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 20)
    (e := .const 0) (st := st) (Expr.eval_const (by omega))
  have hcnt : st₁.mem A.delPtr = delL.length := by
    rw [hm₁, hB.mem_eq (by omega) (by simpa using hfr2 0 (by omega))]; exact hdel.1
  obtain ⟨st₂, hr₂, hm₂, h26₂, ho₂⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 26)
    (e := .load (.reg 2)) (st := st₁)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by rw [ho₁ 2 (by omega), r2])) hcnt)
  have hI₀ : DelInv T A tx₀ mem₀ S₀ cord E₀ delL cur₀ 0 (T.rep.phi A.tourH tx st.mem) st₂ := by
    refine ⟨s, tx, ?_, hR.of_fixed fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _, ?_, ?_,
      ?_, ?_⟩
    · have : st₂.regs 7 = cur₀ := by rw [ho₂ _ (by omega), ho₁ _ (by omega), h7]
      rw [hm₂, hm₁, this]; simpa [MGraph.applyBatch] using hB
    · rw [ho₂ r (by rintro rfl; revert hr; decide), ho₁ r (by rintro rfl; revert hr; decide)]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h14]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h16]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h17]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h18]
    · rw [ho₂ _ (by omega), h20₁]
    · exact h26₂
    · simpa using hmk
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h7]
    · rw [ho₂ _ (by omega), ho₁ _ (by omega), h7]; simp
    · rw [hm₂, hm₁]
  have hloop := runs_loop_amort (w := w) (p := p) (ω := ω) (e := .bin .lt (.reg 20) (.reg 26))
    (body := osDelIter sm au)
    (Inv := fun a st => DelInv T A tx₀ mem₀ S₀ cord E₀ delL cur₀ a.1 a.2 st)
    (Fin := fun o st r => o = .normal ∧ DelInv T A tx₀ mem₀ S₀ cord E₀ delL cur₀ delL.length r st)
    (fun a => delL.length - a.1)
    (fun a => (delL.length - a.1) * (2 * (S.mul * ordStoreLog eCap) + 1700) + a.2 + 5)
    (condVal := fun st => if st.regs 20 < st.regs 26 then 1 else 0)
    (fun a st hI => Expr.eval_lt_op (Expr.eval_reg w 20 st) (Expr.eval_reg w 26 st) (by omega))
    ?_ ?_ (0, T.rep.phi A.tourH tx st.mem) st₂ hI₀
  · obtain ⟨o, st₃, c₃, hr₃, r, ⟨rfl, hI₃⟩, hc₃⟩ := hloop
    refine ⟨st₃, _, runs_seq_normal hr₁ (runs_seq_normal hr₂ hr₃), r, hI₃, ?_⟩
    simp only [Expr.size_reg, Expr.size_load, Expr.size_const, Nat.sub_zero] at hc₃ ⊢
    omega
  · rintro ⟨i, φ⟩ st hI hc
    have hI' := hI
    obtain ⟨-, -, -, -, -, -, -, -, h20', h26', hle, -⟩ := hI'
    have hin : i = delL.length := by
      simp only [h20', h26'] at hc
      split_ifs at hc <;> omega
    subst hin
    exact ⟨φ, ⟨rfl, hI⟩, by simp only [Expr.size_bin, Expr.size_reg, Nat.sub_self, Nat.zero_mul]; omega⟩
  · rintro ⟨i, φ⟩ st hI hc
    have hI' := hI
    obtain ⟨-, -, -, -, -, -, -, -, h20', h26', -⟩ := hI'
    have hi : i < delL.length := by
      simp only [h20', h26'] at hc
      split_ifs at hc with h
      · exact h
      · omega
    obtain ⟨st', c, φ', hr, hI'', hc'⟩ := osDelIter_runs hC hau hw ht0 htour hdel hfree hnd hsub
      hcap hflag1 hflag0 heR hroom hI hi
    refine ⟨.normal, st', c, hr, (i + 1, φ'), hI'', by simp only; omega, ?_⟩
    simp only [Expr.size_reg, Expr.size_bin]
    have : delL.length - i = (delL.length - (i + 1)) + 1 := by omega
    rw [this, add_mul, one_mul]
    omega

end Del

end MinCostFlow.SparseCore.Program
