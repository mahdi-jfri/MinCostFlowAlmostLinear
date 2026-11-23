module

public import MinCostFlow.SparseCore.Program.EmbRefreshInner
public import MinCostFlow.SparseCore.Program.OutSpec

import WordRAM.Tactic

/-!
# Embedding-table entering-edge copy and shared helpers (`AssemblyFirstEmbCopyIns`)

Provides the shared `EmbRepAt` update and `EmbConc` packaging lemmas (`embUpdate_step`,
`embConc_of_inv`) together with the deterministic Word-RAM entering-edge embedding updater
`asmFirstCopyInsStmt` (`[embH, insPtr, h]`):
* scans `OutInsAt mem insPtr insL tl hd`,
* writes the 3-word self-walk `[1, e, 1]` at the heap pointer for each `e ∈ insL`,
* stores the pointer into `mem[embH + 2 + e]`,
* returns `h + 3 * insL.length` in `60 * insL.length + 30` time (`asmFirstCopyIns_runs`).

The companion per-slot selective walk copy `asmFirstCopySlotListStmt` is in
`AssemblyFirstEmbCopy.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-! ## Procedure and change list -/

@[expose] public section

/-- **Entering-edges embedding update**, `[embH, insPtr, h]`.
Scans `OutInsAt mem insPtr insL tl hd`, writes `[1, e, 1]` at `hp` for each `e ∈ insL`, sets
`mem[embH + 2 + e] := hp`, and returns `h + 3 * insL.length`. -/
def asmFirstCopyInsStmt : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.reg 1)) ;;
  .assign 5 (.reg 2) ;;
  forRange 6 (.const 0) (.reg 4)
    (.assign 7 (.load (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 3) (.reg 6)))) ;;
     .store (.reg 5) (.const 1) ;;
     .store (.bin .add (.reg 5) (.const 1)) (.reg 7) ;;
     .store (.bin .add (.reg 5) (.const 2)) (.const 1) ;;
     .store (.bin .add (.reg 3) (.reg 7)) (.reg 5) ;;
     .assign 5 (.bin .add (.reg 5) (.const 3))) ;;
  .ret (.reg 5)

/-- The `EmbChange` list setting every entering edge `e ∈ insL` to `[(e, true)]`. -/
def insSelfChange (insL : List ℕ) : EmbChange :=
  insL.map fun e => (e, [(e, true)])

end

/-! ## Determinism and shared embedding-update helpers -/

public section

theorem asmFirstCopyInsStmt_noRand : asmFirstCopyInsStmt.NoRand := by
  simp [asmFirstCopyInsStmt, forRange, forUp, Stmt.NoRand]

/-- Updates `EmbRepAt`, frame, `ZeroFrom`, and pointer locality after writing walk `W` of edge `e`
into `[H, H + walkWords W)` and pointing `embH + 2 + e` to `H`. -/
theorem embUpdate_step {eCap embH h₀ H e : ℕ} {mem₀ m_cur m_new : ℕ → ℕ}
    {vInit curV : EmbView} {ptrInit curPtr : ℕ → ℕ} {W : List (ℕ × Bool)}
    (htab : embH + 2 + eCap ≤ h₀) (hHge : h₀ ≤ H) (heCap : e < eCap)
    (hold : ∀ e' ∈ vInit.dom, ptrInit e' + Read.walkWords (vInit.emb e') ≤ h₀)
    (hrep : EmbRepAt eCap embH curV curPtr m_cur)
    (hfr : ∀ x < h₀, (x < embH + 2 ∨ embH + 2 + eCap ≤ x) → m_cur x = mem₀ x)
    (hz : ZeroFrom m_cur H)
    (hloc : ∀ e' ∈ curV.dom,
      (curPtr e' = ptrInit e' ∧ curV.emb e' = vInit.emb e' ∧ e' ∈ vInit.dom) ∨
      (h₀ ≤ curPtr e' ∧ curPtr e' + Read.walkWords (curV.emb e') ≤ H))
    (hwalk : MWalkAt m_new H W)
    (htab_e : m_new (embH + 2 + e) = H)
    (hout : ∀ x, x ≠ embH + 2 + e → (x < H ∨ H + Read.walkWords W ≤ x) → m_new x = m_cur x) :
    EmbRepAt eCap embH ⟨Function.update curV.emb e W, insert e curV.dom⟩
      (Function.update curPtr e H) m_new ∧
    (∀ x < h₀, (x < embH + 2 ∨ embH + 2 + eCap ≤ x) → m_new x = mem₀ x) ∧
    ZeroFrom m_new (H + Read.walkWords W) ∧
    ∀ e' ∈ insert e curV.dom,
      (Function.update curPtr e H e' = ptrInit e' ∧
        Function.update curV.emb e W e' = vInit.emb e' ∧ e' ∈ vInit.dom) ∨
      (h₀ ≤ Function.update curPtr e H e' ∧
        Function.update curPtr e H e' + Read.walkWords (Function.update curV.emb e W e') ≤
          H + Read.walkWords W) := by
  obtain ⟨hr0, hr1, hrE⟩ := hrep
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hout embH (by omega) (Or.inl (by omega))]; exact hr0
  · rw [hout (embH + 1) (by omega) (Or.inl (by omega))]; exact hr1
  · intro e' he'
    simp only [Finset.mem_insert] at he'
    by_cases hee : e' = e
    · subst hee
      simp only [Function.update_self]
      exact ⟨heCap, by omega, htab_e, hwalk⟩
    · have he'd : e' ∈ curV.dom := he'.resolve_left hee
      obtain ⟨hlt', hge', htab', hwk'⟩ := hrE e' he'd
      simp only [Function.update_of_ne hee]
      refine ⟨hlt', hge', ?_, ?_⟩
      · rw [hout (embH + 2 + e') (by omega) (Or.inl (by omega))]; exact htab'
      · have hbelow : curPtr e' + Read.walkWords (curV.emb e') ≤ H := by
          rcases hloc e' he'd with ⟨hp, hem, hdom⟩ | ⟨_, hle⟩
          · have := hold e' hdom; rw [hp, hem]; omega
          · exact hle
        refine hwk'.of_agree fun x hx1 hx2 => ?_
        simp only [Read.walkWords] at hbelow
        exact hout x (by omega) (Or.inl (by omega))
  · intro x hx hx'
    rw [hout x (by omega) (Or.inl (by omega))]
    exact hfr x hx hx'
  · intro x hx
    rw [hout x (by omega) (Or.inr hx)]
    exact hz x (by omega)
  · intro e' he'
    simp only [Finset.mem_insert] at he'
    by_cases hee : e' = e
    · subst hee; right; simp only [Function.update_self]; omega
    · have he'd : e' ∈ curV.dom := he'.resolve_left hee
      simp only [Function.update_of_ne hee]
      rcases hloc e' he'd with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, by omega⟩

/-- Packages `EmbRepAt`, frame, and pointer locality into `(embRep eCap).rep` and `embFoot` growth. -/
theorem embConc_of_inv {eCap embH h₀ hp : ℕ} {mem₀ mem' : ℕ → ℕ}
    {vInit curV : EmbView} {y : EmbConc} {curPtr : ℕ → ℕ}
    (hyV : y.view = vInit)
    (hrep : EmbRepAt eCap embH curV curPtr mem')
    (hfr : ∀ x < h₀, (x < embH + 2 ∨ embH + 2 + eCap ≤ x) → mem' x = mem₀ x)
    (hloc : ∀ e ∈ curV.dom,
      (curPtr e = y.ptr e ∧ curV.emb e = vInit.emb e ∧ e ∈ vInit.dom) ∨
      (h₀ ≤ curPtr e ∧ curPtr e + Read.walkWords (curV.emb e) ≤ hp)) :
    let y' : EmbConc := ⟨curPtr, curV⟩
    (embRep eCap).rep embH curV y' mem' ∧
    (∀ a < h₀, ¬ embFoot eCap embH y a → mem' a = mem₀ a) ∧
    (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (h₀ ≤ a ∧ a < hp)) := by
  refine ⟨⟨rfl, hrep⟩, ?_, ?_⟩
  · intro a ha hnf
    refine hfr a ha ?_
    simp only [embFoot, not_or, not_and, not_lt] at hnf
    by_cases hle : embH ≤ a
    · exact Or.inr (hnf.1 hle)
    · exact Or.inl (by omega)
  · rintro a (ha | ⟨e, he, ha1, ha2⟩)
    · exact Or.inl (Or.inl ha)
    · rcases hloc e he with ⟨hp', hemb', hdom0⟩ | ⟨hl1, hl2⟩
      · exact Or.inl (Or.inr ⟨e, hyV.symm ▸ hdom0, hp' ▸ ha1, by
          simp only at ha2; rw [hp', hemb'] at ha2; rw [hyV]; exact ha2⟩)
      · exact Or.inr ⟨by simp only at ha1; omega, by simp only at ha2; omega⟩

/-- Extracts the header/table upper bound and per-edge walk upper bounds from `embFoot < h`. -/
theorem embFoot_below_parts {eCap embH h : ℕ} {y : EmbConc}
    (hEmbF : ∀ a, embFoot eCap embH y a → a < h) :
    embH + 2 + eCap ≤ h ∧ ∀ e ∈ y.view.dom, y.ptr e + Read.walkWords (y.view.emb e) ≤ h := by
  refine ⟨?_, fun e he => ?_⟩
  · have hlt := hEmbF (embH + 1 + eCap) (Or.inl ⟨by omega, by omega⟩)
    omega
  · have hpos : 0 < Read.walkWords (y.view.emb e) := by simp [Read.walkWords]
    have hlt := hEmbF (y.ptr e + Read.walkWords (y.view.emb e) - 1)
      (Or.inr ⟨e, he, by omega, by omega⟩)
    omega

/-- **Verification of `asmFirstCopyInsStmt`**: writes `[(e, true)]` into the embedding table for
every entering edge `e ∈ insL` (`OutInsAt`), allocating exact space `3 * insL.length` and running
in `60 * insL.length + 30` time. -/
theorem asmFirstCopyIns_runs {w eCap embH insPtr h pos : ℕ} {p : Program}
    {v : EmbView} {y : EmbConc} {insL : List ℕ} {tl hd : ℕ → ℕ}
    {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hEmb : (embRep eCap).rep embH v y mem₀)
    (hIns : OutInsAt mem₀ insPtr insL tl hd)
    (hIns_le : insPtr + 1 + 3 * insL.length ≤ h)
    (hIns_cap : ∀ e ∈ insL, e < eCap)
    (hEmbF : ∀ a, embFoot eCap embH y a → a < h)
    (hDisj : ∀ a, insPtr ≤ a → a < insPtr + 1 + 3 * insL.length → ¬ embFoot eCap embH y a)
    (hz : ZeroFrom mem₀ h)
    (hsp : h + 3 * insL.length < 2 ^ w) :
    ∃ o st' c y',
      Runs w p ω asmFirstCopyInsStmt (startState [embH, insPtr, h] mem₀ pos) o st' c ∧
      (embRep eCap).rep embH (v.apply (insSelfChange insL)) y' st'.mem ∧
      o.value = h + 3 * insL.length ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ embFoot eCap embH y a → st'.mem a = mem₀ a) ∧
      (∀ a, embFoot eCap embH y' a → embFoot eCap embH y a ∨ (h ≤ a ∧ a < o.value)) ∧
      c ≤ 60 * insL.length + 30 := by
  obtain ⟨hv, hrep0⟩ := hEmb
  obtain ⟨htab, hold⟩ := embFoot_below_parts hEmbF
  have hold' : ∀ e' ∈ v.dom, y.ptr e' + Read.walkWords (v.emb e') ≤ h := by
    rw [← hv]; exact hold
  have hdisjTab : ∀ a, insPtr ≤ a → a < insPtr + 1 + 3 * insL.length →
      a < embH + 2 ∨ embH + 2 + eCap ≤ a := by
    intro a h1 h2
    by_contra hnot; push Not at hnot
    exact hDisj a h1 h2 (Or.inl ⟨by omega, hnot.2⟩)
  let Inv : ℕ → State → Prop := fun i st =>
    let pre := insSelfChange (insL.take i)
    let curV := v.apply pre
    let curS := pre.foldl embConcStep (y.ptr, h)
    st.regs 1 = insPtr ∧ st.regs 3 = embH + 2 ∧ st.regs 4 = insL.length ∧
    st.regs 5 = h + 3 * i ∧ st.regs 6 = i ∧ curS.2 = h + 3 * i ∧
    EmbRepAt eCap embH curV curS.1 st.mem ∧
    (∀ x < h, (x < embH + 2 ∨ embH + 2 + eCap ≤ x) → st.mem x = mem₀ x) ∧
    ZeroFrom st.mem (h + 3 * i) ∧
    ∀ e' ∈ curV.dom,
      (curS.1 e' = y.ptr e' ∧ curV.emb e' = v.emb e' ∧ e' ∈ v.dom) ∨
      (h ≤ curS.1 e' ∧ curS.1 e' + Read.walkWords (curV.emb e') ≤ h + 3 * i)
  have hbody : ∀ i < insL.length,
      Triple w p (Inv i)
        (.assign 7 (.load (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 3) (.reg 6)))) ;;
         .store (.reg 5) (.const 1) ;;
         .store (.bin .add (.reg 5) (.const 1)) (.reg 7) ;;
         .store (.bin .add (.reg 5) (.const 2)) (.const 1) ;;
         .store (.bin .add (.reg 3) (.reg 7)) (.reg 5) ;;
         .assign 5 (.bin .add (.reg 5) (.const 3)))
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 6 (i + 1) } ∧ st₁.regs 6 = i)
        (fun _ => 50) := by
    intro i hi st ω' hI
    obtain ⟨hr1, hr3, hr4, hr5, hr6, hhp, hrep, hfr, hzI, hloc⟩ := hI
    set e := insL[i]'hi
    have heCap : e < eCap := hIns_cap e (List.getElem_mem hi)
    have hme : st.mem (insPtr + 1 + 3 * i) = e := by
      rw [hfr _ (by omega) (hdisjTab _ (by omega) (by omega))]
      have := (hIns.2 i hi).1
      rwa [List.getD_eq_getElem _ _ hi] at this
    set H := h + 3 * i
    have hpre_succ : insSelfChange (insL.take (i + 1)) =
        insSelfChange (insL.take i) ++ [(e, [(e, true)])] := by
      unfold insSelfChange
      rw [List.take_succ_eq_append_getElem hi, List.map_append, List.map_singleton]
    have hfold_succ : (insSelfChange (insL.take i) ++ [(e, [(e, true)])]).foldl embConcStep (y.ptr, h) =
        (Function.update ((insSelfChange (insL.take i)).foldl embConcStep (y.ptr, h)).1 e H, H + 3) := by
      simp [List.foldl_append, embConcStep, hhp, H, Read.walkWords]
    have hview_succ : v.apply (insSelfChange (insL.take i) ++ [(e, [(e, true)])]) =
        ⟨Function.update (v.apply (insSelfChange (insL.take i))).emb e [(e, true)],
          insert e (v.apply (insSelfChange (insL.take i))).dom⟩ := by
      rw [EmbView.apply_append, EmbView.apply_singleton]
    have he7 : (Expr.load (.bin .add (.bin .add (.reg 1) (.const 1)) (.bin .mul (.const 3) (.reg 6)))).eval w st =
        some e :=
      Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr1) (Expr.eval_const (by omega)) (by omega))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr6) (by omega)) (by omega))
        hme
    set rA := Function.update st.regs 7 e
    set m1 := Function.update st.mem H 1
    set m2 := Function.update m1 (H + 1) e
    set m3 := Function.update m2 (H + 2) 1
    set m4 := Function.update m3 (embH + 2 + e) H
    set rB := Function.update rA 5 (H + 3)
    have hr7 : Runs w p ω' (.assign 7 _) st .normal ⟨st.mem, rA, st.pos⟩ _ :=
      runs_assign_iff.mpr ⟨e, he7, rfl, rfl, rfl⟩
    have hrS1 : Runs w p ω' (.store (.reg 5) (.const 1)) ⟨st.mem, rA, st.pos⟩ .normal ⟨m1, rA, st.pos⟩ _ :=
      runs_store_iff.mpr ⟨H, 1, Expr.eval_reg_of_eq (by simp [rA, hr5, H]), Expr.eval_const (by omega), rfl, rfl, rfl⟩
    have hrS2 : Runs w p ω' (.store (.bin .add (.reg 5) (.const 1)) (.reg 7)) ⟨m1, rA, st.pos⟩ .normal ⟨m2, rA, st.pos⟩ _ :=
      runs_store_iff.mpr ⟨H + 1, e,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr5, H])) (Expr.eval_const (by omega)) (by omega),
        Expr.eval_reg_of_eq (by simp [rA]), rfl, rfl, rfl⟩
    have hrS3 : Runs w p ω' (.store (.bin .add (.reg 5) (.const 2)) (.const 1)) ⟨m2, rA, st.pos⟩ .normal ⟨m3, rA, st.pos⟩ _ :=
      runs_store_iff.mpr ⟨H + 2, 1,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr5, H])) (Expr.eval_const (by omega)) (by omega),
        Expr.eval_const (by omega), rfl, rfl, rfl⟩
    have hrS4 : Runs w p ω' (.store (.bin .add (.reg 3) (.reg 7)) (.reg 5)) ⟨m3, rA, st.pos⟩ .normal ⟨m4, rA, st.pos⟩ _ :=
      runs_store_iff.mpr ⟨embH + 2 + e, H,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr3])) (Expr.eval_reg_of_eq (by simp [rA])) (by omega),
        Expr.eval_reg_of_eq (by simp [rA, hr5, H]), rfl, rfl, rfl⟩
    have hrA5 : Runs w p ω' (.assign 5 (.bin .add (.reg 5) (.const 3))) ⟨m4, rA, st.pos⟩ .normal ⟨m4, rB, st.pos⟩ _ :=
      runs_assign_iff.mpr ⟨H + 3,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr5, H])) (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
    have hrAll := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr7,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrS1,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrS2,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrS3,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrS4, hrA5, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have hm4_0 : m4 H = 1 := by simp [m4, m3, m2, m1, show H ≠ embH + 2 + e by omega]
    have hm4_1 : m4 (H + 1) = e := by simp [m4, m3, m2, show H + 1 ≠ embH + 2 + e by omega]
    have hm4_2 : m4 (H + 2) = 1 := by simp [m4, m3, show H + 2 ≠ embH + 2 + e by omega]
    have hm4_out : ∀ x, x ≠ embH + 2 + e → (x < H ∨ H + Read.walkWords [(e, true)] ≤ x) →
        m4 x = st.mem x := by
      intro x hx1 hx2
      have : Read.walkWords [(e, true)] = 3 := rfl
      rw [this] at hx2
      simp [m4, m3, m2, m1, hx1, show x ≠ H + 2 by omega, show x ≠ H + 1 by omega, show x ≠ H by omega]
    have hupd := embUpdate_step htab (by omega : h ≤ H) heCap hold' hrep hfr hzI hloc
      (mWalkAt_single_true hm4_0 hm4_1 hm4_2) (by simp [m4]) hm4_out
    refine ⟨.normal, _, _, hrAll, ⟨?_, by simp [rB, rA, hr6]⟩, by simp [Expr.size]⟩
    dsimp only [Inv]
    rw [hpre_succ, hview_succ, hfold_succ]
    have hH3 : H + 3 = h + 3 * (i + 1) := by omega
    have hW3 : Read.walkWords [(e, true)] = 3 := rfl
    rw [hW3, hH3] at hupd
    exact ⟨by simp [rB, rA, hr1], by simp [rB, rA, hr3], by simp [rB, rA, hr4],
      by simp [rB, hH3], by simp, hH3, hupd.1, hupd.2.1, hupd.2.2.1, hupd.2.2.2⟩
  have hloop := Triple.forRange_le
    (P := fun st => st.mem = mem₀ ∧ st.regs 1 = insPtr ∧ st.regs 3 = embH + 2 ∧
      st.regs 4 = insL.length ∧ st.regs 5 = h)
    (fun _ => 50) 0 insL.length (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st ⟨hm, hr1, hr3, hr4, hr5⟩ =>
      ⟨Expr.eval_const (by omega),
       ⟨by simp [hr1], by simp [hr3], by simp [hr4], by simp [hr5], by simp, by simp [insSelfChange],
        by simpa [insSelfChange, EmbView.apply, hm, ← hv] using hrep0, fun _ _ _ => by rw [hm],
        by simpa [hm] using hz, fun e he => Or.inl ⟨rfl, rfl, by simpa [insSelfChange, EmbView.apply] using he⟩⟩⟩)
    (fun i st _ _ hI => hI.2.2.2.2.1)
    (fun i st _ _ hI => Expr.eval_reg_of_eq hI.2.2.1)
    (fun i _ hi => hbody i hi)
  set st0 := startState [embH, insPtr, h] mem₀ pos
  set r1 := Function.update st0.regs 3 (embH + 2)
  set r2 := Function.update r1 4 insL.length
  set r3 := Function.update r2 5 h
  have hr_a3 : Runs w p ω (.assign 3 (.load (.reg 0))) st0 .normal ⟨mem₀, r1, pos⟩ _ :=
    runs_assign_iff.mpr ⟨embH + 2,
      Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [st0, startState])) hrep0.1, rfl, rfl, rfl⟩
  have hr_a4 : Runs w p ω (.assign 4 (.load (.reg 1))) ⟨mem₀, r1, pos⟩ .normal ⟨mem₀, r2, pos⟩ _ :=
    runs_assign_iff.mpr ⟨insL.length,
      Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [r1, st0, startState])) hIns.1, rfl, rfl, rfl⟩
  have hr_a5 : Runs w p ω (.assign 5 (.reg 2)) ⟨mem₀, r2, pos⟩ .normal ⟨mem₀, r3, pos⟩ _ :=
    runs_assign_iff.mpr ⟨h, Expr.eval_reg_of_eq (by simp [r2, r1, st0, startState]), rfl, rfl, rfl⟩
  obtain ⟨oL, stL, cL, hrL, hpostL, hcL⟩ := hloop ⟨mem₀, r3, pos⟩ ω
    ⟨rfl, by simp [r3, r2, r1, st0, startState], by simp [r3, r2, r1], by simp [r3, r2], by simp [r3]⟩
  cases oL with
  | returned _ => cases hpostL
  | normal =>
  obtain ⟨-, -, -, hr5L, -, -, hrepL, hfrL, hzL, hlocL⟩ := hpostL
  rw [List.take_length] at hrepL hlocL
  have hr_ret : Runs w p ω (.ret (.reg 5)) stL (.returned (h + 3 * insL.length)) stL _ :=
    runs_ret_iff.mpr ⟨h + 3 * insL.length, Expr.eval_reg_of_eq hr5L, rfl, rfl, rfl⟩
  have hr_full := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a3,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a4,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a5,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrL, hr_ret, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hpkg := embConc_of_inv hv hrepL hfrL hlocL
  refine ⟨.returned (h + 3 * insL.length), stL, _, _, hr_full, hpkg.1, rfl, hzL, hpkg.2.1, hpkg.2.2, ?_⟩
  have hrc : rangeCost (fun _ => 50) 0 insL.length = 50 * insL.length := by
    simp [rangeCost, Nat.mul_comm]
  dsimp only at hcL
  simp only [Expr.size, Nat.sub_zero, hrc] at hcL ⊢
  omega

end

end MinCostFlow.SparseCore.Program
