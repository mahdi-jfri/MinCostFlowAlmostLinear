module

public import WordRAM.Logic

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM

/-! ## Potential-carrying Hoare triples (`PTriple`) for amortized Word-RAM proofs -/

def PTriple (w : ℕ) (p : Program) (P : State → ℕ → Prop) (s : Stmt)
    (Q : Outcome → State → ℕ → Prop) (T : State → ℕ) : Prop :=
  ∀ st Φ ω, P st Φ →
    ∃ o st' c Φ', Runs w p ω s st o st' c ∧ Q o st' Φ' ∧ c + Φ' ≤ T st + Φ

abbrev pNormalPost (Q : State → ℕ → Prop) : Outcome → State → ℕ → Prop
  | .normal, st, Φ => Q st Φ
  | .returned _, _, _ => False

lemma PTriple.of_triple {w : ℕ} {p : Program} {P : State → ℕ → Prop} {s : Stmt}
    {Q : Outcome → State → ℕ → Prop} {T : State → ℕ}
    (h : ∀ Φ, Triple w p (fun st => P st Φ) s (fun o st' => Q o st' Φ) T) :
    PTriple w p P s Q T := fun st Φ ω hP => by
  obtain ⟨o, st', c, hr, hq, hc⟩ := h Φ st ω hP
  exact ⟨o, st', c, Φ, hr, hq, Nat.add_le_add_right hc Φ⟩

lemma PTriple.conseq {w : ℕ} {p : Program} {P P' : State → ℕ → Prop} {s : Stmt}
    {Q Q' : Outcome → State → ℕ → Prop} {T T' : State → ℕ}
    (h : PTriple w p P s Q T)
    (hP : ∀ st Φ, P' st Φ → P st Φ)
    (hQ : ∀ o st' Φ', Q o st' Φ' → Q' o st' Φ')
    (hT : ∀ st Φ, P' st Φ → T st ≤ T' st) :
    PTriple w p P' s Q' T' := fun st Φ ω hP' => by
  obtain ⟨o, st', c, Φ', hr, hq, hc⟩ := h st Φ ω (hP st Φ hP')
  exact ⟨o, st', c, Φ', hr, hQ o st' Φ' hq, le_trans hc (Nat.add_le_add_right (hT st Φ hP') Φ)⟩

lemma PTriple.to_triple {w : ℕ} {p : Program} {P : State → ℕ → Prop} {s : Stmt}
    {Q : Outcome → State → ℕ → Prop} {T : State → ℕ}
    (h : PTriple w p P s Q T) :
    Triple w p (fun st => ∃ Φ, P st Φ ∧ Φ = 0) s (fun o st' => ∃ Φ', Q o st' Φ') T :=
  fun st ω ⟨Φ, hP, h0⟩ => by
    obtain ⟨o, st', c, Φ', hr, hq, hc⟩ := h st Φ ω hP
    exact ⟨o, st', c, hr, ⟨Φ', hq⟩, by omega⟩

lemma PTriple.seq {w : ℕ} {p : Program} {P : State → ℕ → Prop} {s₁ s₂ : Stmt}
    {Q₁ Q : Outcome → State → ℕ → Prop} {T₁ T₂ T : State → ℕ}
    (h₁ : PTriple w p P s₁ Q₁ T₁)
    (h₂ : PTriple w p (Q₁ .normal) s₂ Q T₂)
    (hRet : ∀ u st' Φ', Q₁ (.returned u) st' Φ' → Q (.returned u) st' Φ')
    (hTRet : ∀ st Φ u st' Φ', P st Φ → Q₁ (.returned u) st' Φ' → T₁ st + 1 ≤ T st)
    (hT : ∀ st Φ st₁ Φ₁, P st Φ → Q₁ .normal st₁ Φ₁ → T₁ st + T₂ st₁ + 1 ≤ T st) :
    PTriple w p P (s₁ ;; s₂) Q T := fun st Φ ω hP => by
  obtain ⟨o₁, st₁, c₁, Φ₁, hr₁, hq₁, hc₁⟩ := h₁ st Φ ω hP
  cases o₁ with
  | returned u =>
    exact ⟨.returned u, st₁, c₁ + 1, Φ₁, runs_seq_iff.mpr (Or.inl ⟨u, c₁, hr₁, rfl, rfl⟩),
      hRet u st₁ Φ₁ hq₁, by have := hTRet st Φ u st₁ Φ₁ hP hq₁; omega⟩
  | normal =>
    obtain ⟨o₂, st₂, c₂, Φ₂, hr₂, hq₂, hc₂⟩ := h₂ st₁ Φ₁ ω hq₁
    exact ⟨o₂, st₂, c₁ + c₂ + 1, Φ₂,
      runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), hq₂,
      by have := hT st Φ st₁ Φ₁ hP hq₁; omega⟩

lemma PTriple.seq_normal {w : ℕ} {p : Program} {P Q₁ Q : State → ℕ → Prop} {s₁ s₂ : Stmt}
    {T₁ T₂ T : State → ℕ}
    (h₁ : PTriple w p P s₁ (pNormalPost Q₁) T₁)
    (h₂ : PTriple w p Q₁ s₂ (pNormalPost Q) T₂)
    (hT : ∀ st Φ st₁ Φ₁, P st Φ → Q₁ st₁ Φ₁ → T₁ st + T₂ st₁ + 1 ≤ T st) :
    PTriple w p P (s₁ ;; s₂) (pNormalPost Q) T :=
  h₁.seq h₂ (fun _ _ _ h => False.elim h) (fun _ _ _ _ _ _ h => False.elim h) hT

lemma PTriple.cond {w : ℕ} {p : Program} {P : State → ℕ → Prop} {e : Expr} {s₁ s₂ : Stmt}
    {condVal : State → ℕ} {Q : Outcome → State → ℕ → Prop} {T₁ T₂ : State → ℕ}
    (he : ∀ st Φ, P st Φ → Expr.eval w st e = some (condVal st))
    (hTrue : PTriple w p (fun st Φ => P st Φ ∧ condVal st ≠ 0) s₁ Q T₁)
    (hFalse : PTriple w p (fun st Φ => P st Φ ∧ condVal st = 0) s₂ Q T₂) :
    PTriple w p P (Stmt.cond e s₁ s₂) Q
      (fun st => e.size + (if condVal st = 0 then T₂ st else T₁ st) + 1) :=
  fun st Φ ω hP => by
    have hev := he st Φ hP
    by_cases hc : condVal st = 0
    · obtain ⟨o, st', c₁, Φ', hr, hq, hbound⟩ := hFalse st Φ ω ⟨hP, hc⟩
      refine ⟨o, st', e.size + c₁ + 1, Φ', runs_cond_iff.mpr ⟨0, c₁, hc ▸ hev, by simpa using hr, rfl⟩,
        hq, ?_⟩
      simp only [hc, ↓reduceIte]; omega
    · obtain ⟨o, st', c₁, Φ', hr, hq, hbound⟩ := hTrue st Φ ω ⟨hP, hc⟩
      refine ⟨o, st', e.size + c₁ + 1, Φ', runs_cond_iff.mpr ⟨condVal st, c₁, hev, by simpa [hc] using hr, rfl⟩,
        hq, ?_⟩
      simp only [hc, ↓reduceIte]; omega

lemma PTriple.loop_inv {w : ℕ} {p : Program} {α : Type*} {e : Expr} {body : Stmt}
    {Inv : α → State → ℕ → Prop} {Q : Outcome → State → ℕ → Prop}
    (m rem : α → ℕ) {condVal : State → ℕ}
    (he : ∀ a st Φ, Inv a st Φ → Expr.eval w st e = some (condVal st))
    (hDone : ∀ a st Φ, Inv a st Φ → condVal st = 0 → Q .normal st Φ ∧ e.size + 1 ≤ rem a)
    (hStep : ∀ a st Φ, Inv a st Φ → condVal st ≠ 0 → ∃ stepCost,
      PTriple w p (fun s Φ' => s = st ∧ Φ' = Φ) body
        (fun o s' Φ' => match o with
          | .returned u => Q (.returned u) s' Φ' ∧ e.size + stepCost + 1 ≤ rem a
          | .normal => ∃ a', Inv a' s' Φ' ∧ m a' < m a ∧ e.size + stepCost + rem a' + 1 ≤ rem a)
        (fun _ => stepCost)) :
    ∀ a₀, PTriple w p (Inv a₀) (Stmt.loop e body) Q (fun _ => rem a₀) := by
  have hAux : ∀ k a st Φ ω, m a ≤ k → Inv a st Φ →
      ∃ o st' c Φ', Runs w p ω (Stmt.loop e body) st o st' c ∧ Q o st' Φ' ∧ c + Φ' ≤ rem a + Φ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a st Φ ω hmk hInv
      have hev := he a st Φ hInv
      by_cases h0 : condVal st = 0
      · obtain ⟨hq, hrem⟩ := hDone a st Φ hInv h0
        exact ⟨.normal, st, e.size + 1, Φ,
          runs_loop_iff.mpr (Or.inl ⟨h0 ▸ hev, rfl, rfl, rfl⟩), hq, by omega⟩
      · obtain ⟨stepCost, hbody⟩ := hStep a st Φ hInv h0
        obtain ⟨o₁, st₁, c₁, Φ₁, hr₁, hq₁, hc₁⟩ := hbody st Φ ω ⟨rfl, rfl⟩
        cases o₁ with
        | returned u =>
          exact ⟨.returned u, st₁, e.size + c₁ + 1, Φ₁,
            runs_loop_iff.mpr (Or.inr (Or.inl ⟨condVal st, u, c₁, hev, h0, hr₁, rfl, rfl⟩)),
            hq₁.1, by dsimp only at hc₁; have := hq₁.2; omega⟩
        | normal =>
          rcases hq₁ with ⟨a', hInv', hm', hrem'⟩
          obtain ⟨o₂, st₂, c₂, Φ₂, hr₂, hq₂, hc₂⟩ :=
            ih (m a - 1) (by omega) a' st₁ Φ₁ ω (by omega) hInv'
          exact ⟨o₂, st₂, e.size + c₁ + c₂ + 1, Φ₂,
            runs_loop_iff.mpr (Or.inr (Or.inr ⟨condVal st, st₁, c₁, c₂, hev, h0, hr₁, hr₂, rfl⟩)),
            hq₂, by dsimp only at hc₁; omega⟩
  intro a₀ st Φ ω hInv
  exact hAux (m a₀) a₀ st Φ ω (le_refl _) hInv

lemma PTriple.forUp_le {w : ℕ} {p : Program} {r : ℕ} {hi : Expr} {body : Stmt}
    {Inv : ℕ → State → ℕ → Prop} (stepCost : ℕ → ℕ) (i₀ hiVal : ℕ)
    (hle : i₀ ≤ hiVal) (hw : 1 < 2 ^ w) (hhi_word : i₀ < hiVal → hiVal < 2 ^ w)
    (hreg : ∀ i st Φ, i₀ ≤ i → i ≤ hiVal → Inv i st Φ → st.regs r = i)
    (hhi : ∀ i st Φ, i₀ ≤ i → i ≤ hiVal → Inv i st Φ → Expr.eval w st hi = some hiVal)
    (hbody : ∀ i, i₀ ≤ i → i < hiVal →
      PTriple w p (Inv i) body
        (pNormalPost fun st₁ Φ₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) } Φ₁ ∧ st₁.regs r = i)
        (fun _ => stepCost i)) :
    PTriple w p (Inv i₀) (forUp r hi body) (pNormalPost (Inv hiVal))
      (fun _ => rangeCost stepCost i₀ hiVal + (hiVal - i₀) * (hi.size + 8) + (hi.size + 3)) := by
  let SInv : ℕ → State → ℕ → Prop := fun i st Φ => i₀ ≤ i ∧ i ≤ hiVal ∧ Inv i st Φ
  let rem : ℕ → ℕ := fun i => rangeCost stepCost i hiVal + (hiVal - i) * (hi.size + 8) + (hi.size + 3)
  let condVal : State → ℕ := fun st => if st.regs r < hiVal then 1 else 0
  have hloop := PTriple.loop_inv (w := w) (p := p) (e := .bin .lt (.reg r) hi)
    (body := body ;; .assign r (.bin .add (.reg r) (.const 1)))
    (Inv := SInv) (Q := pNormalPost (Inv hiVal)) (m := fun i => hiVal - i) (rem := rem)
    (condVal := condVal)
    (fun i st Φ h => by
      have hr : st.regs r = i := hreg i st Φ h.1 h.2.1 h.2.2
      have hhi' := hhi i st Φ h.1 h.2.1 h.2.2
      simpa only [condVal, hr] using Expr.eval_lt_op (Expr.eval_reg_of_eq hr) hhi' hw)
    (fun i st Φ h h0 => by
      have hr : st.regs r = i := hreg i st Φ h.1 h.2.1 h.2.2
      have hieq : i = hiVal := by
        simp only [condVal, hr] at h0; (split_ifs at h0 with hlt; omega)
      subst hieq
      refine ⟨h.2.2, ?_⟩
      simp only [rem, rangeCost_self, Nat.sub_self, Nat.zero_mul, zero_add, Expr.size]
      omega)
    (fun i st Φ h hne => by
      have hr : st.regs r = i := hreg i st Φ h.1 h.2.1 h.2.2
      have hilt : i < hiVal := by
        simp only [condVal, hr] at hne; split_ifs at hne with hlt
        · exact hlt
        · exact absurd rfl hne
      have hi1_w : i + 1 < 2 ^ w := lt_of_le_of_lt hilt (hhi_word (by omega))
      refine ⟨stepCost i + 5, ?_⟩
      intro s₀ Φ₀ ω ⟨hs₀, hΦ₀⟩
      rw [hs₀, hΦ₀] at *
      obtain ⟨o₁, st₁, c₁, Φ₁, hr₁, hq₁, hc₁⟩ := hbody i h.1 hilt st Φ ω h.2.2
      cases o₁ with
      | returned _ => exact False.elim hq₁
      | normal =>
        obtain ⟨hInv1, hr₁_r⟩ := hq₁
        have hev_add : Expr.eval w st₁ (.bin .add (.reg r) (.const 1)) = some (i + 1) :=
          Expr.eval_add (Expr.eval_reg_of_eq hr₁_r) (Expr.eval_const hw) hi1_w
        have hr_a : Runs w p ω (.assign r (.bin .add (.reg r) (.const 1))) st₁ .normal
            { st₁ with regs := Function.update st₁.regs r (i + 1) } 4 :=
          runs_assign_iff.mpr ⟨i + 1, hev_add, rfl, rfl, by simp [Expr.size]⟩
        refine ⟨.normal, { st₁ with regs := Function.update st₁.regs r (i + 1) },
          c₁ + 4 + 1, Φ₁, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, 4, hr₁, hr_a, rfl⟩),
          ⟨i + 1, ⟨by omega, hilt, hInv1⟩, by omega, ?_⟩, by dsimp only at hc₁ ⊢; omega⟩
        simp only [rem, rangeCost_step hilt, Expr.size,
          show hiVal - i = hiVal - (i + 1) + 1 by omega, Nat.add_one_mul]
        omega)
    i₀
  exact PTriple.conseq hloop (fun st Φ h => ⟨le_refl _, hle, h⟩) (fun _ _ _ h => h) (fun _ _ _ => le_refl _)

lemma PTriple.forRange_le {w : ℕ} {p : Program} {P : State → ℕ → Prop} {r : ℕ} {lo hi : Expr}
    {body : Stmt} {Inv : ℕ → State → ℕ → Prop} (stepCost : ℕ → ℕ) (loVal hiVal : ℕ)
    (hle : loVal ≤ hiVal) (hw : 1 < 2 ^ w) (hhi_word : loVal < hiVal → hiVal < 2 ^ w)
    (hInit : ∀ st Φ, P st Φ → Expr.eval w st lo = some loVal ∧
      Inv loVal { st with regs := Function.update st.regs r loVal } Φ)
    (hreg : ∀ i st Φ, loVal ≤ i → i ≤ hiVal → Inv i st Φ → st.regs r = i)
    (hhi : ∀ i st Φ, loVal ≤ i → i ≤ hiVal → Inv i st Φ → Expr.eval w st hi = some hiVal)
    (hbody : ∀ i, loVal ≤ i → i < hiVal →
      PTriple w p (Inv i) body
        (pNormalPost fun st₁ Φ₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) } Φ₁ ∧ st₁.regs r = i)
        (fun _ => stepCost i)) :
    PTriple w p P (forRange r lo hi body) (pNormalPost (Inv hiVal))
      (fun _ => rangeCost stepCost loVal hiVal + (hiVal - loVal) * (hi.size + 8) +
        (lo.size + hi.size + 5)) := by
  have hAssign : PTriple w p P (.assign r lo) (pNormalPost (Inv loVal)) (fun _ => lo.size + 1) :=
    fun st Φ ω hP => by
      obtain ⟨hev, hI⟩ := hInit st Φ hP
      exact ⟨.normal, { st with regs := Function.update st.regs r loVal }, lo.size + 1, Φ,
        runs_assign_iff.mpr ⟨loVal, hev, rfl, rfl, rfl⟩, hI, le_refl _⟩
  have hFor := PTriple.forUp_le stepCost loVal hiVal hle hw hhi_word hreg hhi hbody
  refine (hAssign.seq_normal hFor fun _ _ _ _ _ _ => ?_)
  omega

lemma PTriple.forRange_const {w : ℕ} {p : Program} {P : State → ℕ → Prop} {r : ℕ} {lo hi : Expr}
    {body : Stmt} {Inv : ℕ → State → ℕ → Prop} (stepBound loVal hiVal : ℕ)
    (hle : loVal ≤ hiVal) (hw : 1 < 2 ^ w) (hhi_word : loVal < hiVal → hiVal < 2 ^ w)
    (hInit : ∀ st Φ, P st Φ → Expr.eval w st lo = some loVal ∧
      Inv loVal { st with regs := Function.update st.regs r loVal } Φ)
    (hreg : ∀ i st Φ, loVal ≤ i → i ≤ hiVal → Inv i st Φ → st.regs r = i)
    (hhi : ∀ i st Φ, loVal ≤ i → i ≤ hiVal → Inv i st Φ → Expr.eval w st hi = some hiVal)
    (hbody : ∀ i, loVal ≤ i → i < hiVal →
      PTriple w p (Inv i) body
        (pNormalPost fun st₁ Φ₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) } Φ₁ ∧ st₁.regs r = i)
        (fun _ => stepBound)) :
    PTriple w p P (forRange r lo hi body) (pNormalPost (Inv hiVal))
      (fun _ => (hiVal - loVal) * (stepBound + hi.size + 8) + (lo.size + hi.size + 5)) := by
  have h := PTriple.forRange_le (fun _ => stepBound) loVal hiVal hle hw hhi_word hInit hreg hhi hbody
  exact PTriple.conseq h (fun _ _ h => h) (fun _ _ _ h => h) fun _ _ _ => by
    rw [rangeCost_const, ← Nat.mul_add, ← Nat.add_assoc stepBound]

lemma Triple.call_proc {w : ℕ} {p : Program} {r f : ℕ} {args : List Expr} {body : Stmt}
    {P : State → Prop} {Pb : State → Prop} {Qb : Outcome → State → Prop}
    {Tb : State → ℕ} {Q : Outcome → State → Prop} {T : State → ℕ}
    (hproc : p.procs[f]? = some body)
    (hbody : Triple w p Pb body Qb Tb)
    (hpre : ∀ st, P st → ∃ vs, evalArgs w st args = some vs ∧
      Pb (startState vs st.mem st.pos) ∧
      argsSize args + Tb (startState vs st.mem st.pos) + 1 ≤ T st)
    (hpost : ∀ st o₁ st₁, P st → Qb o₁ st₁ →
      Q .normal { st₁ with regs := Function.update st.regs r o₁.value }) :
    Triple w p P (.call r f args) Q T := fun st ω hP => by
  obtain ⟨vs, hargs, hPb, hcost⟩ := hpre st hP
  obtain ⟨o₁, st₁, c₁, hr₁, hqb, hc₁⟩ := hbody (startState vs st.mem st.pos) ω hPb
  refine ⟨.normal, { st₁ with regs := Function.update st.regs r o₁.value },
    argsSize args + c₁ + 1,
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hproc, hr₁, rfl, rfl, rfl⟩,
    hpost st o₁ st₁ hP hqb, by omega⟩

lemma PTriple.call_proc {w : ℕ} {p : Program} {r f : ℕ} {args : List Expr} {body : Stmt}
    {P : State → ℕ → Prop} {Pb : State → ℕ → Prop} {Qb : Outcome → State → ℕ → Prop}
    {Tb : State → ℕ} {Q : Outcome → State → ℕ → Prop} {T : State → ℕ}
    (hproc : p.procs[f]? = some body)
    (hbody : PTriple w p Pb body Qb Tb)
    (hpre : ∀ st Φ, P st Φ → ∃ vs, evalArgs w st args = some vs ∧
      Pb (startState vs st.mem st.pos) Φ ∧
      argsSize args + Tb (startState vs st.mem st.pos) + 1 ≤ T st)
    (hpost : ∀ st Φ o₁ st₁ Φ', P st Φ → Qb o₁ st₁ Φ' →
      Q .normal { st₁ with regs := Function.update st.regs r o₁.value } Φ') :
    PTriple w p P (.call r f args) Q T := fun st Φ ω hP => by
  obtain ⟨vs, hargs, hPb, hcost⟩ := hpre st Φ hP
  obtain ⟨o₁, st₁, c₁, Φ', hr₁, hqb, hc₁⟩ := hbody (startState vs st.mem st.pos) Φ ω hPb
  refine ⟨.normal, { st₁ with regs := Function.update st.regs r o₁.value },
    argsSize args + c₁ + 1, Φ',
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hproc, hr₁, rfl, rfl, rfl⟩,
    hpost st Φ o₁ st₁ Φ' hP hqb, by omega⟩

lemma rangeCost_zero_eq_sum (f : ℕ → ℕ) (n : ℕ) :
    rangeCost f 0 n = ∑ i ∈ Finset.range n, f i := by
  simp only [rangeCost, Nat.sub_zero, ← List.range_eq_range']
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      ih, Finset.sum_range_succ]

lemma rangeCost_le_sum (f g : ℕ → ℕ) (n : ℕ) (hle : ∀ i < n, f i ≤ g i) :
    rangeCost f 0 n ≤ ∑ i ∈ Finset.range n, g i := by
  rw [rangeCost_zero_eq_sum]
  exact Finset.sum_le_sum fun i hi => hle i (Finset.mem_range.mp hi)

/-- Loop induction rule allowing `body` cost to be paid directly out of potential drop `Φ - Φ₁`
together with `rem a - rem a'`. -/
lemma PTriple.loop_pot {w : ℕ} {p : Program} {α : Type*} {e : Expr} {body : Stmt}
    {Inv : α → State → ℕ → Prop} {Q : Outcome → State → ℕ → Prop}
    (m rem : α → ℕ) {condVal : State → ℕ}
    (he : ∀ a st Φ, Inv a st Φ → Expr.eval w st e = some (condVal st))
    (hDone : ∀ a st Φ, Inv a st Φ → condVal st = 0 → Q .normal st Φ ∧ e.size + 1 ≤ rem a)
    (hStep : ∀ a st Φ ω, Inv a st Φ → condVal st ≠ 0 →
      ∃ o₁ st₁ c₁ Φ₁, Runs w p ω body st o₁ st₁ c₁ ∧
        match o₁ with
        | .returned u => Q (.returned u) st₁ Φ₁ ∧ e.size + c₁ + Φ₁ + 1 ≤ rem a + Φ
        | .normal => ∃ a', Inv a' st₁ Φ₁ ∧ m a' < m a ∧
            e.size + c₁ + rem a' + Φ₁ + 1 ≤ rem a + Φ) :
    ∀ a₀, PTriple w p (Inv a₀) (Stmt.loop e body) Q (fun _ => rem a₀) := by
  have hAux : ∀ k a st Φ ω, m a ≤ k → Inv a st Φ →
      ∃ o st' c Φ', Runs w p ω (Stmt.loop e body) st o st' c ∧ Q o st' Φ' ∧ c + Φ' ≤ rem a + Φ := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a st Φ ω hmk hInv
      have hev := he a st Φ hInv
      by_cases h0 : condVal st = 0
      · obtain ⟨hq, hrem⟩ := hDone a st Φ hInv h0
        exact ⟨.normal, st, e.size + 1, Φ,
          runs_loop_iff.mpr (Or.inl ⟨h0 ▸ hev, rfl, rfl, rfl⟩), hq, by omega⟩
      · obtain ⟨o₁, st₁, c₁, Φ₁, hr₁, hq₁⟩ := hStep a st Φ ω hInv h0
        cases o₁ with
        | returned u =>
          exact ⟨.returned u, st₁, e.size + c₁ + 1, Φ₁,
            runs_loop_iff.mpr (Or.inr (Or.inl ⟨condVal st, u, c₁, hev, h0, hr₁, rfl, rfl⟩)),
            hq₁.1, by omega⟩
        | normal =>
          rcases hq₁ with ⟨a', hInv', hm', hrem'⟩
          obtain ⟨o₂, st₂, c₂, Φ₂, hr₂, hq₂, hc₂⟩ :=
            ih (m a - 1) (by omega) a' st₁ Φ₁ ω (by omega) hInv'
          exact ⟨o₂, st₂, e.size + c₁ + c₂ + 1, Φ₂,
            runs_loop_iff.mpr (Or.inr (Or.inr ⟨condVal st, st₁, c₁, c₂, hev, h0, hr₁, hr₂, rfl⟩)),
            hq₂, by omega⟩
  intro a₀ st Φ ω hInv
  exact hAux (m a₀) a₀ st Φ ω (le_refl _) hInv

end MinCostFlow.Spanner
