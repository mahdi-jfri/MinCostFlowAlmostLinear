module

public import MinCostFlow.SparseCore.Program.OutSmallSideSteps

/-!
# The walk of the helper `outSmallSide` on the machine

The walk of the helper runs while register `14` is on. At round `j` of the walk, registers `12`
and `13` hold the codes of the `j`-th marked ends of the two parts, and the heap has moved by at
most `2 + 2 j` queries (`SSLoopInv`). A round asks for the next marked end of the first part; if
it is the first marked end again, the first part has `j + 1` marked ends and is chosen.
Otherwise it asks the same for the second part. So the walk stops after `min l₁ l₂` rounds,
where `l₁` and `l₂` are the numbers of marked ends, with the side of the smaller part
(`ssLoop_runs`). Each round costs two tour queries, paid with the tour potential.

The two other straight parts of the helper are here too: the head, which writes the record
(`ssHead_runs`), and the start of the walk (`ssInit_runs`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LowStretch

/-- The side that the helper chooses: `0` when the first part has at most as many marked ends. -/
noncomputable def ssSide (s : OutTourAbs) (r₁ r₂ : ℕ) : ℕ :=
  if (s.markedList r₁).length ≤ (s.markedList r₂).length then 0 else 1

/-- The code of the `i`-th marked end equals the code of the first one exactly when `i = 0`. -/
theorem ss_code_eq_iff {M : List End} (hnd : M.Nodup) {i : ℕ} (hi : i < M.length)
    (h0 : 0 < M.length) : 1 + endKey M[i] = 1 + endKey M[0] ↔ i = 0 := by
  constructor
  · intro he
    have hk : endKey M[i] = endKey M[0] := by omega
    have : M[i] = M[0] := by
      have := congrArg endOfKey hk
      rwa [endOfKey_endKey, endOfKey_endKey] at this
    exact (List.Nodup.getElem_inj_iff hnd).mp this
  · rintro rfl; rfl

/-- The code of the first marked end of a nonempty list. -/
theorem optEndWord_head? {M : List End} (h0 : 0 < M.length) :
    optEndWord M.head? = 1 + endKey M[0] := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]; rfl

/-- The code of the first marked end is `0` exactly when there is none. -/
theorem optEndWord_head?_eq_zero {M : List End} : optEndWord M.head? = 0 ↔ M = [] := by
  cases M with
  | nil => simp [optEndWord]
  | cons y M => simp [optEndWord]

section Loop

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- The invariant of the walk at round `a.1`, with tour potential `a.2`. -/
def SSLoopInv (T : OutTourAt S w vCap eCap p nm sm fm lm) (tourH r₁ r₂ v v' last h : ℕ)
    (s : OutTourAbs) (tx₀ : T.rep.τ) (mem₀ : ℕ → ℕ) (a : ℕ × ℕ) (st : State) : Prop :=
  ∃ tx cur, SSFrame T tourH last h v v' s tx₀ mem₀ cur tx st.mem ∧
    T.rep.phi tourH tx st.mem = a.2 ∧ SSArgs st tourH r₁ r₂ v v' last h ∧ st.regs 7 = cur ∧
    st.regs 9 = optEndWord (s.markedList r₁).head? ∧
    st.regs 10 = optEndWord (s.markedList r₂).head? ∧
    cur ≤ h + 5 + (2 + 2 * a.1) * S.querySpace ∧
    ((st.regs 14 = 1 ∧ st.regs 11 = 0 ∧ ∃ (h₁ : a.1 < (s.markedList r₁).length)
        (h₂ : a.1 < (s.markedList r₂).length),
        st.regs 12 = 1 + endKey (s.markedList r₁)[a.1] ∧
        st.regs 13 = 1 + endKey (s.markedList r₂)[a.1]) ∨
      (st.regs 14 = 0 ∧ st.regs 11 = ssSide s r₁ r₂ ∧
        a.1 = min (s.markedList r₁).length (s.markedList r₂).length))

/-- **The walk.** From round `0` with potential `φ`, the loop ends at round `min l₁ l₂` with
register `14` off and the side in register `11`, at a cost that, with the final potential, is at
most `(2 · mul · log + 60) · (min l₁ l₂ + 1)` plus `φ`. -/
theorem ssLoop_runs (T : OutTourAt S w vCap eCap p nm sm fm lm) {tourH r₁ r₂ v v' last h : ℕ}
    {s : OutTourAbs} {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} (ω : ℕ → Bool)
    (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h)
    (hlast : last = 0 ∨ (last + 4 < h ∧ ¬ T.rep.foot tourH tx₀ (last + 4)))
    (hnd₁ : (s.cord r₁).Nodup) (hnd₂ : (s.cord r₂).Nodup)
    (hlt₁ : ∀ x ∈ s.markedList r₁, x.1 < eCap) (hlt₂ : ∀ x ∈ s.markedList r₂, x.1 < eCap)
    (htour : tourH < 2 ^ w) (hr₁ : r₁ < vCap) (hr₂ : r₂ < vCap) (hkey : 2 * eCap + 2 < 2 ^ w)
    (hspace : h + 5 + (2 * min (s.markedList r₁).length (s.markedList r₂).length + 2) *
      S.querySpace < 2 ^ w)
    (φ : ℕ) (st : State) (hI : SSLoopInv T tourH r₁ r₂ v v' last h s tx₀ mem₀ (0, φ) st) :
    ∃ o st' c, Runs w p ω (.loop (.reg 14) (ssWalkBody nm)) st o st' c ∧ ∃ r,
      (o = .normal ∧ SSLoopInv T tourH r₁ r₂ v v' last h s tx₀ mem₀
        (min (s.markedList r₁).length (s.markedList r₂).length, r) st' ∧ st'.regs 14 = 0) ∧
      c + r ≤ (2 * (S.mul * ordStoreLog eCap) + 60) *
        (min (s.markedList r₁).length (s.markedList r₂).length + 1) + φ := by
  set l₁ := (s.markedList r₁).length with hl₁
  set l₂ := (s.markedList r₂).length with hl₂
  set k := min l₁ l₂ with hk
  set X := S.mul * ordStoreLog eCap with hX
  set Cst := 2 * X + 60 with hCst
  have h1w : 1 < 2 ^ w := by omega
  have hrun := runs_loop_amort (w := w) (p := p) (ω := ω) (e := .reg 14) (body := ssWalkBody nm)
    (Inv := SSLoopInv T tourH r₁ r₂ v v' last h s tx₀ mem₀)
    (Fin := fun o st r => o = .normal ∧
      SSLoopInv T tourH r₁ r₂ v v' last h s tx₀ mem₀ (k, r) st ∧ st.regs 14 = 0)
    (fun a => k + 1 - a.1) (fun a => Cst * (k + 1 - a.1) + a.2) (condVal := fun st => st.regs 14)
    (fun a st _ => Expr.eval_reg w 14 st) ?_ ?_ (0, φ) st hI
  · obtain ⟨o, st', c, hr, r, hfin, hc⟩ := hrun
    exact ⟨o, st', c, hr, r, hfin, by simpa using hc⟩
  · -- the exit
    rintro ⟨j, φ'⟩ st hInv h14
    obtain ⟨tx, cur, hF, hphi, hA, h7, h9, h10, hcur, ⟨h14', -⟩ | ⟨-, h11, hj⟩⟩ := hInv
    · omega
    · dsimp only at hj
      subst hj
      refine ⟨φ', ⟨rfl, ⟨tx, cur, hF, hphi, hA, h7, h9, h10, hcur, Or.inr ⟨h14, h11, rfl⟩⟩,
        h14⟩, ?_⟩
      dsimp only
      rw [Nat.add_sub_cancel_left, Nat.mul_one]
      simp only [Expr.size_reg]
      omega
  · -- one round
    rintro ⟨j, φ'⟩ st hInv h14
    obtain ⟨tx, cur, hF, hphi, hA, h7, h9, h10, hcur, ⟨h14', h11, hj₁, hj₂, h12, h13⟩ |
      ⟨h14', -, -⟩⟩ := hInv
    swap
    · omega
    dsimp only at hj₁ hj₂ h12 h13 hcur hphi
    have hjk : j < k := by omega
    have hkm : Cst * (k + 1 - j) = Cst * (k + 1 - (j + 1)) + Cst := by
      rw [show k + 1 - j = (k + 1 - (j + 1)) + 1 by omega, Nat.mul_succ]
    have hqk : (2 + 2 * (j + 1)) * S.querySpace = (2 + 2 * j) * S.querySpace + 2 * S.querySpace :=
      by ring
    have hqk' : (2 * k + 2) * S.querySpace = (2 + 2 * j) * S.querySpace + 2 * S.querySpace +
        (2 * (k - (j + 1))) * S.querySpace := by
      rw [show 2 * k + 2 = (2 + 2 * j) + 2 + 2 * (k - (j + 1)) by omega]; ring
    have hsp1 : cur + S.querySpace < 2 ^ w := by omega
    -- the first part
    obtain ⟨st₁, c₁, tx₁, hr₁, hF₁, h12₁, hoth₁, hle₁, hge₁, hcost₁⟩ :=
      ssNext_step T st ω (src := 12) (r := r₁) (j := j) (by norm_num) (by norm_num) hfoot₀ hlast
        hF hA.1 h7 hj₁ h12 hnd₁ hlt₁ htour hr₁ hkey hsp1
    have h0₁ : 0 < l₁ := by omega
    have h9₁ : st₁.regs 9 = 1 + endKey (s.markedList r₁)[0] := by
      rw [hoth₁ 9 (by norm_num) (by norm_num) (by norm_num), h9, optEndWord_head? h0₁]
    have hA₁ : SSArgs st₁ tourH r₁ r₂ v v' last h :=
      hA.of_regs fun r hr => hoth₁ r (by omega) (by omega) (by omega)
    have heq₁ := ss_code_eq_iff (M := s.markedList r₁) (hnd₁.filter _)
      (Nat.mod_lt (j + 1) h0₁) h0₁
    by_cases hd₁ : j + 1 = l₁
    · -- the first part is done: it is the smaller one
      have hmod : (j + 1) % l₁ = 0 := by rw [hd₁, Nat.mod_self]
      have hev : (Expr.bin .eq (.reg 12) (.reg 9)).eval w st₁ = some 1 := by
        rw [Expr.eval_eq_op (Expr.eval_reg_of_eq h12₁) (Expr.eval_reg_of_eq h9₁) h1w,
          ite_eq_left (heq₁.mpr hmod)]
      have ha := runs_assign_of (w := w) (p := p) (ω := ω) (r := 14) (st := st₁)
        (Expr.eval_const (k := 0) (by omega))
      have hc : Runs w p ω (.cond (.bin .eq (.reg 12) (.reg 9)) (.assign 14 (.const 0))
          (.seq (ssQuery nm (.bin .sub (.reg 13) (.const 1)) 13)
            (.cond (.bin .eq (.reg 13) (.reg 10))
              (.seq (.assign 11 (.const 1)) (.assign 14 (.const 0))) .nop))) st₁ .normal
          { st₁ with regs := Function.update st₁.regs 14 0 } (3 + 2 + 1) :=
        runs_cond_iff.mpr ⟨1, 2, hev, by simpa using ha, rfl⟩
      refine ⟨.normal, _, _, runs_seq_normal hr₁ hc, ⟨j + 1, T.rep.phi tourH tx₁ st₁.mem⟩,
        ⟨tx₁, st₁.regs 7, hF₁, rfl, hA₁.of_regs fun r hr => by simp [Function.update_of_ne
          (show r ≠ 14 by omega)], by simp, ?_, ?_, ?_, Or.inr ⟨by simp, ?_, ?_⟩⟩, ?_, ?_⟩
      · simp only [Function.update_of_ne (show (9 : ℕ) ≠ 14 by norm_num)]
        rw [hoth₁ 9 (by norm_num) (by norm_num) (by norm_num), h9]
      · simp only [Function.update_of_ne (show (10 : ℕ) ≠ 14 by norm_num)]
        rw [hoth₁ 10 (by norm_num) (by norm_num) (by norm_num), h10]
      · dsimp only; omega
      · simp only [Function.update_of_ne (show (11 : ℕ) ≠ 14 by norm_num)]
        rw [hoth₁ 11 (by norm_num) (by norm_num) (by norm_num), h11, ssSide, ite_eq_left (by omega)]
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; simp only [Expr.size_reg]; omega
    · -- the first part goes on
      have hlt1 : j + 1 < l₁ := by omega
      have hmod : (j + 1) % (s.markedList r₁).length = j + 1 := Nat.mod_eq_of_lt hlt1
      have hev : (Expr.bin .eq (.reg 12) (.reg 9)).eval w st₁ = some 0 := by
        rw [Expr.eval_eq_op (Expr.eval_reg_of_eq h12₁) (Expr.eval_reg_of_eq h9₁) h1w,
          ite_eq_right (fun he => by have := heq₁.mp he; omega)]
      have hsp2 : st₁.regs 7 + S.querySpace < 2 ^ w := by omega
      have h13₁ : st₁.regs 13 = 1 + endKey (s.markedList r₂)[j] := by
        rw [hoth₁ 13 (by norm_num) (by norm_num) (by norm_num), h13]
      obtain ⟨st₂, c₂, tx₂, hr₂, hF₂, h13₂, hoth₂, hle₂, hge₂, hcost₂⟩ :=
        ssNext_step T st₁ ω (src := 13) (r := r₂) (j := j) (by norm_num) (by norm_num) hfoot₀
          hlast hF₁ hA₁.1 rfl hj₂ h13₁ hnd₂ hlt₂ htour hr₂ hkey hsp2
      have h0₂ : 0 < l₂ := by omega
      have h10₂ : st₂.regs 10 = 1 + endKey (s.markedList r₂)[0] := by
        rw [hoth₂ 10 (by norm_num) (by norm_num) (by norm_num),
          hoth₁ 10 (by norm_num) (by norm_num) (by norm_num), h10, optEndWord_head? h0₂]
      have hA₂ : SSArgs st₂ tourH r₁ r₂ v v' last h :=
        hA₁.of_regs fun r hr => hoth₂ r (by omega) (by omega) (by omega)
      have heq₂ := ss_code_eq_iff (M := s.markedList r₂) (hnd₂.filter _)
        (Nat.mod_lt (j + 1) h0₂) h0₂
      have h9₂ : st₂.regs 9 = optEndWord (s.markedList r₁).head? := by
        rw [hoth₂ 9 (by norm_num) (by norm_num) (by norm_num),
          hoth₁ 9 (by norm_num) (by norm_num) (by norm_num), h9]
      have h11₂ : st₂.regs 11 = 0 := by
        rw [hoth₂ 11 (by norm_num) (by norm_num) (by norm_num),
          hoth₁ 11 (by norm_num) (by norm_num) (by norm_num), h11]
      have h14₂ : st₂.regs 14 = 1 := by
        rw [hoth₂ 14 (by norm_num) (by norm_num) (by norm_num),
          hoth₁ 14 (by norm_num) (by norm_num) (by norm_num), h14']
      by_cases hd₂ : j + 1 = l₂
      · -- the second part is done first: it is the smaller one
        have hmod₂ : (j + 1) % l₂ = 0 := by rw [hd₂, Nat.mod_self]
        have hev₂ : (Expr.bin .eq (.reg 13) (.reg 10)).eval w st₂ = some 1 := by
          rw [Expr.eval_eq_op (Expr.eval_reg_of_eq h13₂) (Expr.eval_reg_of_eq h10₂) h1w,
            ite_eq_left (heq₂.mpr hmod₂)]
        have ha1 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 11) (st := st₂)
          (Expr.eval_const (k := 1) h1w)
        have ha2 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 14)
          (st := { st₂ with regs := Function.update st₂.regs 11 1 })
          (Expr.eval_const (k := 0) (by omega))
        have hc₂ : Runs w p ω (.cond (.bin .eq (.reg 13) (.reg 10))
            (.seq (.assign 11 (.const 1)) (.assign 14 (.const 0))) .nop) st₂ .normal
            { st₂ with regs := Function.update (Function.update st₂.regs 11 1) 14 0 }
            (3 + 5 + 1) :=
          runs_cond_iff.mpr ⟨1, 5, hev₂, by simpa using runs_seq_normal ha1 ha2, rfl⟩
        have hc : Runs w p ω (.cond (.bin .eq (.reg 12) (.reg 9)) (.assign 14 (.const 0))
            (.seq (ssQuery nm (.bin .sub (.reg 13) (.const 1)) 13)
              (.cond (.bin .eq (.reg 13) (.reg 10))
                (.seq (.assign 11 (.const 1)) (.assign 14 (.const 0))) .nop))) st₁ .normal
            { st₂ with regs := Function.update (Function.update st₂.regs 11 1) 14 0 }
            (3 + (c₂ + 9 + 1) + 1) :=
          runs_cond_iff.mpr ⟨0, _, hev, by simpa using runs_seq_normal hr₂ hc₂, rfl⟩
        refine ⟨.normal, _, _, runs_seq_normal hr₁ hc, ⟨j + 1, T.rep.phi tourH tx₂ st₂.mem⟩,
          ⟨tx₂, st₂.regs 7, hF₂, rfl, hA₂.of_regs fun r hr => by
            simp [Function.update_of_ne (show r ≠ 14 by omega),
              Function.update_of_ne (show r ≠ 11 by omega)], by simp, ?_, ?_, ?_,
            Or.inr ⟨by simp, ?_, ?_⟩⟩, ?_, ?_⟩
        · simp [h9₂]
        · show Function.update (Function.update st₂.regs 11 1) 14 0 10 = _
          rw [Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num),
            hoth₂ 10 (by norm_num) (by norm_num) (by norm_num),
            hoth₁ 10 (by norm_num) (by norm_num) (by norm_num), h10]
        · dsimp only; omega
        · simp [ssSide]; omega
        · dsimp only; omega
        · dsimp only; omega
        · dsimp only; simp only [Expr.size_reg]; omega
      · -- both parts go on
        have hlt2 : j + 1 < l₂ := by omega
        have hmod₂ : (j + 1) % (s.markedList r₂).length = j + 1 := Nat.mod_eq_of_lt hlt2
        have hev₂ : (Expr.bin .eq (.reg 13) (.reg 10)).eval w st₂ = some 0 := by
          rw [Expr.eval_eq_op (Expr.eval_reg_of_eq h13₂) (Expr.eval_reg_of_eq h10₂) h1w,
            ite_eq_right (fun he => by have := heq₂.mp he; omega)]
        have hc₂ : Runs w p ω (.cond (.bin .eq (.reg 13) (.reg 10))
            (.seq (.assign 11 (.const 1)) (.assign 14 (.const 0))) .nop) st₂ .normal st₂
            (3 + 1 + 1) :=
          runs_cond_iff.mpr ⟨0, 1, hev₂, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
        have hc : Runs w p ω (.cond (.bin .eq (.reg 12) (.reg 9)) (.assign 14 (.const 0))
            (.seq (ssQuery nm (.bin .sub (.reg 13) (.const 1)) 13)
              (.cond (.bin .eq (.reg 13) (.reg 10))
                (.seq (.assign 11 (.const 1)) (.assign 14 (.const 0))) .nop))) st₁ .normal
            st₂ (3 + (c₂ + 5 + 1) + 1) :=
          runs_cond_iff.mpr ⟨0, _, hev, by simpa using runs_seq_normal hr₂ hc₂, rfl⟩
        have h12₂ : st₂.regs 12 = 1 + endKey (s.markedList r₁)[j + 1] := by
          rw [hoth₂ 12 (by norm_num) (by norm_num) (by norm_num), h12₁]
          simp only [hmod]
        have h13₂' : st₂.regs 13 = 1 + endKey (s.markedList r₂)[j + 1] := by
          rw [h13₂]; simp only [hmod₂]
        refine ⟨.normal, _, _, runs_seq_normal hr₁ hc, ⟨j + 1, T.rep.phi tourH tx₂ st₂.mem⟩,
          ⟨tx₂, st₂.regs 7, hF₂, rfl, hA₂, rfl, h9₂, ?_, ?_,
            Or.inl ⟨h14₂, h11₂, hlt1, hlt2, h12₂, h13₂'⟩⟩, ?_, ?_⟩
        · rw [hoth₂ 10 (by norm_num) (by norm_num) (by norm_num),
            hoth₁ 10 (by norm_num) (by norm_num) (by norm_num), h10]
        · dsimp only; omega
        · dsimp only; omega
        · dsimp only; simp only [Expr.size_reg]; omega

end Loop

end MinCostFlow.SparseCore.Program
