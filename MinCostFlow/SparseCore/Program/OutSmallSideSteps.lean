module

public import MinCostFlow.SparseCore.Program.OutSmallSideProg

/-!
# The tour queries of the helper `outSmallSide`

The helper calls `firstMarked` twice and `nextMarked` at each round of its walk. This file shows
what one such call does inside the program (`ssFirst_step`, `ssNext_step`): it keeps the frame
`SSFrame`, writes the code of the answer in its register, keeps the other registers, moves the
heap pointer by at most the query space, and costs the tour bound plus a constant.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle

section Steps

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- The registers of the arguments `[tourH, r₁, r₂, v, v', last, h]`. -/
def SSArgs (st : State) (tourH r₁ r₂ v v' last h : ℕ) : Prop :=
  st.regs 0 = tourH ∧ st.regs 1 = r₁ ∧ st.regs 2 = r₂ ∧ st.regs 3 = v ∧ st.regs 4 = v' ∧
    st.regs 5 = last ∧ st.regs 6 = h

theorem SSArgs.of_regs {st st' : State} {tourH r₁ r₂ v v' last h : ℕ}
    (hA : SSArgs st tourH r₁ r₂ v v' last h) (hr : ∀ r, r < 7 → st'.regs r = st.regs r) :
    SSArgs st' tourH r₁ r₂ v v' last h := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hA
  exact ⟨(hr 0 (by omega)).trans h0, (hr 1 (by omega)).trans h1, (hr 2 (by omega)).trans h2,
    (hr 3 (by omega)).trans h3, (hr 4 (by omega)).trans h4, (hr 5 (by omega)).trans h5,
    (hr 6 (by omega)).trans h6⟩

/-- The footprint of the tour lies below the heap pointer of the frame. -/
theorem SSFrame.foot_lt {T : OutTourAt S w vCap eCap p nm sm fm lm} {tourH last h v v' : ℕ}
    {s : OutTourAbs} {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {cur : ℕ} {tx : T.rep.τ} {mem : ℕ → ℕ}
    (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h)
    (hF : SSFrame T tourH last h v v' s tx₀ mem₀ cur tx mem) :
    ∀ a, T.rep.foot tourH tx a → a < cur := by
  intro a ha
  rcases hF.2.2.2.1 a ha with ha | ⟨-, ha⟩
  · have := hfoot₀ a ha; have := hF.2.2.1; omega
  · exact ha

/-- **A `firstMarked` query** of the root in register `rr`, answered in register `dst`. -/
theorem ssFirst_step (T : OutTourAt S w vCap eCap p nm sm fm lm) {tourH last h v v' : ℕ}
    {s : OutTourAbs} {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {cur : ℕ} {tx : T.rep.τ} (st : State)
    (ω : ℕ → Bool) {rr dst r : ℕ} (hdst7 : dst ≠ 7) (hdst8 : dst ≠ 8)
    (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h)
    (hlast : last = 0 ∨ (last + 4 < h ∧ ¬ T.rep.foot tourH tx₀ (last + 4)))
    (hF : SSFrame T tourH last h v v' s tx₀ mem₀ cur tx st.mem)
    (h0 : st.regs 0 = tourH) (h7 : st.regs 7 = cur) (hrr : st.regs rr = r)
    (htour : tourH < 2 ^ w) (hr : r < vCap) (hspace : cur + S.querySpace < 2 ^ w) :
    ∃ st' c tx', Runs w p ω (ssQuery fm (.reg rr) dst) st .normal st' c ∧
      SSFrame T tourH last h v v' s tx₀ mem₀ (st'.regs 7) tx' st'.mem ∧
      st'.regs dst = optEndWord (s.markedList r).head? ∧
      (∀ r', r' ≠ 7 → r' ≠ 8 → r' ≠ dst → st'.regs r' = st.regs r') ∧
      cur + 1 ≤ st'.regs 7 ∧ st'.regs 7 ≤ cur + S.querySpace ∧
      c + T.rep.phi tourH tx' st'.mem ≤
        S.mul * ordStoreLog eCap + 11 + T.rep.phi tourH tx st.mem := by
  obtain ⟨body, hproc, o, st₁, c₁, tx', hrun, hrep', hout, hle, hresp, hcost⟩ :=
    T.firstMarked_runs tourH r cur s tx st.mem st.pos ω htour hr (by omega) hF.1
      (SSFrame.foot_lt hfoot₀ hF) hF.2.1 hspace
  obtain ⟨st', hrun', hmem, -, h7', hdst, hother⟩ :=
    ssQuery_runs (dst := dst) (argE := .reg rr) hdst7 hdst8 (Expr.eval_reg_of_eq hrr) hproc
      (by rw [h0, h7]; exact hrun)
  refine ⟨st', c₁ + (Expr.reg rr).size + 10, tx', hrun', ?_, ?_, hother, ?_, ?_, ?_⟩
  · rw [hmem, h7']
    exact SSFrame.respects hfoot₀ hlast hF hrep' hresp
  · rw [hdst, h7, hout]
  · rw [h7']; exact hle
  · rw [h7']; exact hresp.2.1
  · rw [hmem]; simp only [Expr.size_reg]; omega

/-- **A `nextMarked` query** from the `j`-th marked end of the root `r`, whose code is in
register `src`; the code of the next marked end goes to the same register. -/
theorem ssNext_step (T : OutTourAt S w vCap eCap p nm sm fm lm) {tourH last h v v' : ℕ}
    {s : OutTourAbs} {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {cur : ℕ} {tx : T.rep.τ} (st : State)
    (ω : ℕ → Bool) {src r j : ℕ} (hsrc7 : src ≠ 7) (hsrc8 : src ≠ 8)
    (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h)
    (hlast : last = 0 ∨ (last + 4 < h ∧ ¬ T.rep.foot tourH tx₀ (last + 4)))
    (hF : SSFrame T tourH last h v v' s tx₀ mem₀ cur tx st.mem)
    (h0 : st.regs 0 = tourH) (h7 : st.regs 7 = cur) (hj : j < (s.markedList r).length)
    (hsrc : st.regs src = 1 + endKey (s.markedList r)[j])
    (hnd : (s.cord r).Nodup) (hlt : ∀ x ∈ s.markedList r, x.1 < eCap)
    (htour : tourH < 2 ^ w) (hr : r < vCap) (hkey : 2 * eCap + 2 < 2 ^ w)
    (hspace : cur + S.querySpace < 2 ^ w) :
    ∃ st' c tx', Runs w p ω (ssQuery nm (.bin .sub (.reg src) (.const 1)) src) st .normal st' c ∧
      SSFrame T tourH last h v v' s tx₀ mem₀ (st'.regs 7) tx' st'.mem ∧
      st'.regs src = 1 + endKey ((s.markedList r)[(j + 1) % (s.markedList r).length]'
        (Nat.mod_lt _ (by omega))) ∧
      (∀ r', r' ≠ 7 → r' ≠ 8 → r' ≠ src → st'.regs r' = st.regs r') ∧
      cur + 1 ≤ st'.regs 7 ∧ st'.regs 7 ≤ cur + S.querySpace ∧
      c + T.rep.phi tourH tx' st'.mem ≤
        S.mul * ordStoreLog eCap + 13 + T.rep.phi tourH tx st.mem := by
  set x := (s.markedList r)[j] with hx
  have hxM : x ∈ s.markedList r := List.getElem_mem hj
  have hxe : x.1 < eCap := hlt x hxM
  have hkx : endKey x < 2 * eCap := endKey_lt_two_mul hxe
  have hxc : endOfKey (endKey x) ∈ s.cord r := by
    rw [endOfKey_endKey]; exact (List.mem_filter.mp hxM).1
  obtain ⟨body, hproc, o, st₁, c₁, tx', hrun, hrep', hout, hle, hresp, hcost⟩ :=
    T.nextMarked_runs tourH (endKey x) r cur s tx st.mem st.pos ω htour hkx (by omega) hr
      (by omega) hxc hF.1 (SSFrame.foot_lt hfoot₀ hF) hF.2.1 hspace
  have harg : (Expr.bin .sub (.reg src) (.const 1)).eval w st = some (endKey x) := by
    have := Expr.eval_sub (w := w) (st := st) (Expr.eval_reg_of_eq hsrc)
      (Expr.eval_const (k := 1) (by omega)) (by omega)
    rw [this]; congr 1; omega
  obtain ⟨st', hrun', hmem, -, h7', hdst, hother⟩ :=
    ssQuery_runs (dst := src) hsrc7 hsrc8 harg hproc (by rw [h0, h7]; exact hrun)
  refine ⟨st', _, tx', hrun', ?_, ?_, hother, ?_, ?_, ?_⟩
  · rw [hmem, h7']
    exact SSFrame.respects hfoot₀ hlast hF hrep' hresp
  · rw [hdst, h7, hout, endOfKey_endKey, hx, nextMarked_markedList s r hnd hj,
      List.getElem?_eq_getElem (Nat.mod_lt _ (by omega))]
    rfl
  · rw [h7']; exact hle
  · rw [h7']; exact hresp.2.1
  · rw [hmem]; simp only [Expr.size_bin, Expr.size_reg, Expr.size_const]; omega

end Steps

end MinCostFlow.SparseCore.Program
