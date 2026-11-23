module

public import MinCostFlow.SparseCore.Program.OutResetProg

/-!
# The reset `outReset`: the setup and the first loop

The setup reads the caps and computes the bases of the arrays that the two loops read
(`rsSetup_runs`). The first loop deletes the edges of the stored graph one by one, from the end of
its edge list, and unmarks the two ends of each (`rsDelLoop_runs`). After it, the stored graph has
no edge and no end is marked.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-! ## The registers -/

/-- The registers that the setup writes and the loops only read. -/
def RSRegs (st : State) (tourH g₂ g vCap eCap : ℕ) : Prop :=
  st.regs 1 = tourH ∧ st.regs 2 = g₂ ∧ st.regs 4 = g ∧ st.regs 10 = vCap ∧ st.regs 11 = eCap ∧
    st.regs 12 = g + 4 + 7 * vCap + 1 * eCap ∧ st.regs 14 = g₂ + 4 + 7 * vCap + 1 * eCap ∧
    st.regs 15 = g₂ + 4 + 4 * vCap + 0 * eCap ∧ st.regs 16 = g₂ + 4 + 7 * vCap + 3 * eCap ∧
    st.regs 17 = g₂ + 4 + 7 * vCap + 4 * eCap

theorem RSRegs.of_regs {st st' : State} {tourH g₂ g vCap eCap : ℕ}
    (hR : RSRegs st tourH g₂ g vCap eCap)
    (hr : ∀ r, r ≠ 5 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 13 → r ≠ 18 → r ≠ 19 →
      st'.regs r = st.regs r) :
    RSRegs st' tourH g₂ g vCap eCap := by
  obtain ⟨h1, h2, h4, h10, h11, h12, h14, h15, h16, h17⟩ := hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rwa [hr _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]

/-- A word size above `4` is at least `8`. -/
theorem rs_eight_le {w : ℕ} (h : 4 < 2 ^ w) : 8 ≤ 2 ^ w := by
  rcases Nat.lt_or_ge w 3 with hw | hw
  · interval_cases w <;> simp_all
  · calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw

/-- A word size above `8` is at least `16`. -/
theorem rs_sixteen_le {w : ℕ} (h : 8 < 2 ^ w) : 16 ≤ 2 ^ w := by
  rcases Nat.lt_or_ge w 4 with hw | hw
  · interval_cases w <;> simp_all
  · calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw

theorem rsBase_eval {w : ℕ} {st : State} {r a k₁ k₂ vCap eCap : ℕ} (hr : st.regs r = a)
    (h10 : st.regs 10 = vCap) (h11 : st.regs 11 = eCap) (hk₁ : k₁ < 2 ^ w) (hk₂ : k₂ < 2 ^ w)
    (hw : a + 4 + k₁ * vCap + k₂ * eCap < 2 ^ w) :
    (rsBase r k₁ k₂).eval w st = some (a + 4 + k₁ * vCap + k₂ * eCap) := by
  have h1 : k₁ * vCap < 2 ^ w := by omega
  have h2 : k₂ * eCap < 2 ^ w := by omega
  unfold rsBase
  exact Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr)
    (Expr.eval_const (by omega)) (by omega)) (Expr.eval_mul (Expr.eval_const hk₁)
      (Expr.eval_reg_of_eq h10) h1) (by omega))
    (Expr.eval_mul (Expr.eval_const hk₂) (Expr.eval_reg_of_eq h11) h2) (by omega)

/-- **The setup.** -/
theorem rsSetup_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {outH tourH g₂ h g vCap eCap : ℕ}
    (mem : ℕ → ℕ) (pos : ℕ) (hg : mem outH = g) (hv : mem g = vCap) (he : mem (g + 1) = eCap)
    (hw8 : 8 ≤ 2 ^ w) (hgw : g + dynGraphSize vCap eCap < 2 ^ w)
    (hg₂w : g₂ + dynGraphSize vCap eCap < 2 ^ w) :
    ∃ st c, Runs w p ω rsSetup (startState [outH, tourH, g₂, h] mem pos) .normal st c ∧
      st.mem = mem ∧ st.pos = pos ∧ RSRegs st tourH g₂ g vCap eCap ∧ st.regs 7 = h ∧
      c ≤ 90 := by
  unfold dynGraphSize at hgw hg₂w
  set st0 := startState [outH, tourH, g₂, h] mem pos with hst0
  have hb1 : 1 < 2 ^ w := by omega
  have a1 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 4) (st := st0)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (r := 0) (v := outH) rfl) hg)
  set st1 : State := { st0 with regs := Function.update st0.regs 4 g } with hst1
  have a2 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 7) (st := st1)
    (Expr.eval_reg_of_eq (r := 3) (v := h) rfl)
  set st2 : State := { st1 with regs := Function.update st1.regs 7 h } with hst2
  have a3 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 10) (st := st2)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (r := 4) (v := g) (by simp [hst2, hst1])) hv)
  set st3 : State := { st2 with regs := Function.update st2.regs 10 vCap } with hst3
  have a4 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 11) (st := st3)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (r := 4) (v := g)
      (by simp [hst3, hst2, hst1])) (Expr.eval_const (k := 1) hb1) (by omega)) he)
  set st4 : State := { st3 with regs := Function.update st3.regs 11 eCap } with hst4
  have h10 : st4.regs 10 = vCap := by simp [hst4, hst3]
  have h11 : st4.regs 11 = eCap := by simp [hst4]
  have h4 : st4.regs 4 = g := by simp [hst4, hst3, hst2, hst1]
  have h2 : st4.regs 2 = g₂ := by simp [hst4, hst3, hst2, hst1, hst0, startState]
  have a5 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 12) (st := st4)
    (rsBase_eval (k₁ := 7) (k₂ := 1) h4 h10 h11 (by omega) (by omega) (by omega))
  set st5 : State :=
    { st4 with regs := Function.update st4.regs 12 (g + 4 + 7 * vCap + 1 * eCap) } with hst5
  have a6 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 14) (st := st5)
    (rsBase_eval (k₁ := 7) (k₂ := 1) (r := 2) (a := g₂) (vCap := vCap) (eCap := eCap) (by simp [hst5, h2]) (by simp [hst5, h10])
      (by simp [hst5, h11]) (by omega) (by omega) (by omega))
  set st6 : State :=
    { st5 with regs := Function.update st5.regs 14 (g₂ + 4 + 7 * vCap + 1 * eCap) } with hst6
  have a7 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 15) (st := st6)
    (rsBase_eval (k₁ := 4) (k₂ := 0) (r := 2) (a := g₂) (vCap := vCap) (eCap := eCap) (by simp [hst6, hst5, h2])
      (by simp [hst6, hst5, h10]) (by simp [hst6, hst5, h11]) (by omega) (by omega) (by omega))
  set st7 : State :=
    { st6 with regs := Function.update st6.regs 15 (g₂ + 4 + 4 * vCap + 0 * eCap) } with hst7
  have a8 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 16) (st := st7)
    (rsBase_eval (k₁ := 7) (k₂ := 3) (r := 2) (a := g₂) (vCap := vCap) (eCap := eCap) (by simp [hst7, hst6, hst5, h2])
      (by simp [hst7, hst6, hst5, h10]) (by simp [hst7, hst6, hst5, h11]) (by omega) (by omega)
      (by omega))
  set st8 : State :=
    { st7 with regs := Function.update st7.regs 16 (g₂ + 4 + 7 * vCap + 3 * eCap) } with hst8
  have a9 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 17) (st := st8)
    (rsBase_eval (k₁ := 7) (k₂ := 4) (r := 2) (a := g₂) (vCap := vCap) (eCap := eCap) (by simp [hst8, hst7, hst6, hst5, h2])
      (by simp [hst8, hst7, hst6, hst5, h10]) (by simp [hst8, hst7, hst6, hst5, h11]) (by omega)
      (by omega) (by omega))
  refine ⟨_, _, runs_seq_normal a1 (runs_seq_normal a2 (runs_seq_normal a3 (runs_seq_normal a4
    (runs_seq_normal a5 (runs_seq_normal a6 (runs_seq_normal a7 (runs_seq_normal a8 a9))))))),
    rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hst8, hst7, hst6, hst5, hst4, hst3, hst2, hst1, hst0, startState]
  · simp [hst8, hst7, hst6, hst5, hst4, hst3, hst2]
  · simp only [rsBase, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load]
    omega

end MinCostFlow.SparseCore.Program

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-! ## The keys of the two ends of an edge -/

theorem endOfKey_two_mul (e : ℕ) : endOfKey (e + e) = (e, true) := by
  simpa [endKey, two_mul] using endOfKey_endKey (e, true)

/-- The keys of the ends of the edges below `eCap` are words. -/
theorem rs_key_lt {w vCap eCap : ℕ} (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) :
    2 * eCap + 2 < 2 ^ w := by
  have h2 : (eCap + 2) * (eCap + 2) ≤ (vCap + eCap + 2) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have h3 : 2 * eCap + 3 ≤ (eCap + 2) * (eCap + 2) := by nlinarith
  omega

theorem endOfKey_two_mul_add_one (e : ℕ) : endOfKey (e + e + 1) = (e, false) := by
  simpa [endKey, two_mul] using endOfKey_endKey (e, false)

/-- Unmarking both ends of `e` leaves exactly the marked ends of other edges. -/
theorem mem_unmark_both {s : OutTourAbs} {e : ℕ} {z : End} :
    z ∈ ((s.setMark (e, true) 0).setMark (e, false) 0).marked ↔ z ∈ s.marked ∧ z.1 ≠ e := by
  obtain ⟨z1, z2⟩ := z
  cases z2 <;> by_cases hz : z1 = e <;> simp [OutTourAbs.setMark, hz]

/-- Marking both ends of `e` adds exactly the two ends of `e`. -/
theorem mem_mark_both {s : OutTourAbs} {e : ℕ} {z : End} :
    z ∈ ((s.setMark (e, true) 1).setMark (e, false) 1).marked ↔ z ∈ s.marked ∨ z.1 = e := by
  obtain ⟨z1, z2⟩ := z
  cases z2 <;> by_cases hz : z1 = e <;> simp [OutTourAbs.setMark, hz]

/-- `16 ≤ 2 ^ w` as soon as there is an edge below `eCap`. -/
theorem rs_sixteen_of_cap {w vCap eCap : ℕ} (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w)
    (he : 0 < eCap) : 16 ≤ 2 ^ w := by
  have : 9 ≤ (vCap + eCap + 2) ^ 2 := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ (vCap + eCap + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact rs_sixteen_le (by omega)

/-! ## The first loop -/

section DelLoop

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- The invariant of the first loop at `(k, φ)`: the stored graph `G` has the vertices of `Sold`,
a part of its edges, and `k` edges; the marked ends are the ends of the edges of `G` in the
lists of the tour; the potential is `φ`; and the heap pointer has room for `k` more rounds. -/
def RS1Inv (T : OutTourAt S w vCap eCap p nm sm fm lm) (tourH g₂ g h : ℕ) (tx₀ : T.rep.τ)
    (mem₀ : ℕ → ℕ) (s₀ : OutTourAbs) (Sold : MGraph) (a : ℕ × ℕ) (st : State) : Prop :=
  ∃ (G : MGraph) (s : OutTourAbs) (tx : T.rep.τ),
    RSFrame T tourH g h tx₀ mem₀ (st.regs 7) s tx st.mem ∧ T.rep.phi tourH tx st.mem = a.2 ∧
    DynGraphAt st.mem g vCap eCap G ∧ G.V = Sold.V ∧ G.E ⊆ Sold.E ∧ G.m = a.1 ∧
    s.cord = s₀.cord ∧ (∀ z, z ∈ s.marked ↔ (∃ v, z ∈ s₀.cord v) ∧ z.1 ∈ G.E) ∧
    RSRegs st tourH g₂ g vCap eCap ∧
    st.regs 7 + 2 * a.1 * S.querySpace ≤ h + 2 * Sold.m * S.querySpace

/-- **One round of the first loop.** -/
theorem rsDelBody_step (T : OutTourAt S w vCap eCap p nm sm fm lm) {tourH g₂ g h : ℕ}
    {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {s₀ : OutTourAbs} {Sold : MGraph} (ω : ℕ → Bool)
    {dgb bOps : ℕ} (hp : p.HasAt dgb (dgEdgeProcs bOps)) (hpOps : p.HasAt bOps dgOpsProcs)
    (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h) (hgh : g + dynGraphSize vCap eCap ≤ h)
    (hdisj : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx₀ a)
    (hends : ∀ e ∈ Sold.E, ∀ t : Bool, ∃ v < vCap, (e, t) ∈ s₀.cord v)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (htour : tourH < 2 ^ w)
    (hgw : g + dynGraphSize vCap eCap < 2 ^ w)
    (hspace : h + 2 * Sold.m * S.querySpace < 2 ^ w)
    {k φ : ℕ} (st : State) (hI : RS1Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold (k, φ) st)
    (hk : k ≠ 0) :
    ∃ st' c, Runs w p ω (rsDelBody sm dgb) st .normal st' c ∧ ∃ φ',
      RS1Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold (k - 1, φ') st' ∧
      c + φ' ≤ 2 * (S.mul * ordStoreLog eCap) + 495 + φ := by
  obtain ⟨G, s, tx, hF, hphi, hG, hV, hsub, hm, hcord, hmarks, hR, hcur⟩ := hI
  dsimp only at hphi hm hcur
  have hq := S.querySpace_ge
  have hkey : 2 * eCap + 2 < 2 ^ w := rs_key_lt hw
  have hG' := hG
  obtain ⟨-, -, hElt, -, -, -, hmw, -, -, -, -, -, ⟨eL, heL_len, heL_nd, heL_mem, heL_at, -⟩,
    -, -⟩ := hG'
  have hmw' : st.mem (g + 3) = k := by rw [← hm]; simpa [dgMOff] using hmw
  have hk1 : k - 1 < eL.length := by rw [heL_len, hm]; omega
  set e := eL[k - 1] with he_def
  have heG : e ∈ G.E := (heL_mem e).mp (List.getElem_mem hk1)
  have heS : e ∈ Sold.E := hsub heG
  have helt : e < eCap := hElt e heG
  have hkle : k ≤ eCap := by
    rw [← hm]
    calc G.m = G.E.card := rfl
      _ ≤ (Finset.range eCap).card :=
        Finset.card_le_card fun x hx => Finset.mem_range.mpr (hElt x hx)
      _ = eCap := Finset.card_range _
  unfold dynGraphSize at hgw hgh
  have hkk : 2 * k * S.querySpace = 2 * (k - 1) * S.querySpace + 2 * S.querySpace := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  -- the edge
  have h4 : st.regs 4 = g := hR.2.2.1
  have h12 : st.regs 12 = g + 4 + 7 * vCap + 1 * eCap := hR.2.2.2.2.2.1
  have hcnt : rsCount.eval w st = some k :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h4)
      (Expr.eval_const (k := 3) (by omega)) (by omega)) hmw'
  have haddr : g + 4 + 7 * vCap + 1 * eCap + k - 1 = dgEListBase g vCap eCap + (k - 1) := by
    unfold dgEListBase; omega
  have ha5 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 5) (st := st)
    (Expr.eval_load_of_eq (v := e) (Expr.eval_sub (Expr.eval_add (Expr.eval_reg_of_eq h12) hcnt
      (by omega)) (Expr.eval_const (k := 1) (by omega)) (by omega))
      (by rw [haddr]; exact heL_at (k - 1) hk1))
  set st1 : State := { st with regs := Function.update st.regs 5 e } with hst1
  have hF1 : RSFrame T tourH g h tx₀ mem₀ (st1.regs 7) s tx st1.mem := hF
  -- unmark the end `(e, true)`
  obtain ⟨v₀, hv₀, hc₀⟩ := hends e heS true
  have h51 : st1.regs 5 = e := by simp [hst1]
  have hk0 : rsKey0.eval w st1 = some (e + e) :=
    Expr.eval_add (Expr.eval_reg_of_eq h51) (Expr.eval_reg_of_eq h51) (by omega)
  obtain ⟨st2, c2, tx2, hr2, hF2, hblk2, hreg2, hle2, hle2', hc2⟩ :=
    rsMark_step T st1 ω (flag := 0) (v := v₀) hfoot₀ (by unfold dynGraphSize; omega) hdisj hF1
      (by simp [hst1, hR.1]) rfl hk0 (by omega) (by omega) (by omega) hv₀
      (by rw [endOfKey_two_mul, hcord]; exact hc₀) htour (by simp [hst1]; omega)
  -- unmark the end `(e, false)`
  obtain ⟨v₁, hv₁, hc₁⟩ := hends e heS false
  have h52 : st2.regs 5 = e := by rw [hreg2 5 (by norm_num) (by norm_num)]; exact h51
  have hk1' : rsKey1.eval w st2 = some (e + e + 1) :=
    Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h52) (Expr.eval_reg_of_eq h52) (by omega))
      (Expr.eval_const (k := 1) (by omega)) (by omega)
  obtain ⟨st3, c3, tx3, hr3, hF3, hblk3, hreg3, hle3, hle3', hc3⟩ :=
    rsMark_step T st2 ω (flag := 0) (v := v₁) hfoot₀ (by unfold dynGraphSize; omega) hdisj hF2
      (by rw [hreg2 1 (by norm_num) (by norm_num)]; simp [hst1, hR.1]) rfl hk1' (by omega)
      (by omega) (by omega) hv₁
      (by rw [endOfKey_two_mul_add_one]; show _ ∈ s.cord v₁; rw [hcord]; exact hc₁) htour
      (by simp [hst1] at hle2'; omega)
  -- delete the edge
  have hG3 : DynGraphAt st3.mem g vCap eCap G :=
    DynGraphAt.of_agree hG fun a ha1 ha2 => by
      rw [hblk3 a ha1 ha2, hblk2 a ha1 ha2]
  have h43 : st3.regs 4 = g := by
    rw [hreg3 4 (by norm_num) (by norm_num), hreg2 4 (by norm_num) (by norm_num)]
    simp [hst1, h4]
  have h53 : st3.regs 5 = e := by rw [hreg3 5 (by norm_num) (by norm_num)]; exact h52
  obtain ⟨st4, c4, hr4, hG4, hF4, hphi4, hreg4, hc4⟩ :=
    rsDelete_step T st3 ω hp hpOps (G := G) (e := e) (by unfold dynGraphSize; omega) hdisj hF3
      hG3 h43 h53 (by omega) (rs_sixteen_of_cap hw (by omega)) (by unfold dynGraphSize; omega)
  rw [ite_eq_left heG] at hG4
  have h74 : st4.regs 7 = st3.regs 7 := hreg4 7 (by norm_num)
  refine ⟨st4, _, runs_seq_normal ha5 (runs_seq_normal hr2 (runs_seq_normal hr3 hr4)),
    T.rep.phi tourH tx3 st4.mem, ⟨G.applyUpdate (.delete e),
      ((s.setMark (endOfKey (e + e)) 0).setMark (endOfKey (e + e + 1)) 0), tx3,
      by rw [h74]; exact hF4, rfl,
    hG4, hV, fun x hx => hsub (Finset.mem_of_mem_erase hx), ?_, hcord, ?_, ?_, ?_⟩, ?_⟩
  · show (G.E.erase e).card = k - 1
    rw [Finset.card_erase_of_mem heG]; exact congrArg (· - 1) hm
  · intro z
    rw [endOfKey_two_mul, endOfKey_two_mul_add_one, mem_unmark_both, hmarks]
    show _ ↔ _ ∧ z.1 ∈ G.E.erase e
    rw [Finset.mem_erase]
    tauto
  · refine hR.of_regs fun r h5 h7 h8 h9 _ _ _ => ?_
    rw [hreg4 r h9, hreg3 r h7 h8, hreg2 r h7 h8]
    simp [hst1, Function.update_of_ne h5]
  · have h71 : st1.regs 7 = st.regs 7 := by simp [hst1]
    dsimp only
    omega
  · rw [hphi4]
    simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, rsCount, rsKey0,
      rsKey1] at hc2 hc3 ⊢
    have hphi1 : T.rep.phi tourH tx st1.mem = φ := hphi
    omega

/-- **The first loop.** From `k = Sold.m` edges it runs until the stored graph has no edge. -/
theorem rsDelLoop_runs (T : OutTourAt S w vCap eCap p nm sm fm lm) {tourH g₂ g h : ℕ}
    {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {s₀ : OutTourAbs} {Sold : MGraph} (ω : ℕ → Bool)
    {dgb bOps : ℕ} (hp : p.HasAt dgb (dgEdgeProcs bOps)) (hpOps : p.HasAt bOps dgOpsProcs)
    (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h) (hgh : g + dynGraphSize vCap eCap ≤ h)
    (hdisj : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx₀ a)
    (hends : ∀ e ∈ Sold.E, ∀ t : Bool, ∃ v < vCap, (e, t) ∈ s₀.cord v)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (htour : tourH < 2 ^ w)
    (hgw : g + dynGraphSize vCap eCap < 2 ^ w)
    (hspace : h + 2 * Sold.m * S.querySpace < 2 ^ w)
    (φ : ℕ) (st : State) (hI : RS1Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold (Sold.m, φ) st) :
    ∃ o st' c, Runs w p ω (.loop rsCount (rsDelBody sm dgb)) st o st' c ∧ ∃ r,
      (o = .normal ∧ RS1Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold (0, r) st') ∧
      c + r ≤ (2 * (S.mul * ordStoreLog eCap) + 500) * Sold.m + 10 + φ := by
  set Cst := 2 * (S.mul * ordStoreLog eCap) + 500 with hCst
  have hrun := MinCostFlow.LowStretch.runs_loop_amort (w := w) (p := p) (ω := ω) (e := rsCount)
    (body := rsDelBody sm dgb) (Inv := RS1Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold)
    (Fin := fun o st r => o = .normal ∧ RS1Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold (0, r) st)
    (fun a => a.1) (fun a => Cst * a.1 + 10 + a.2) (condVal := fun st => st.mem (g + 3))
    ?_ ?_ ?_ (Sold.m, φ) st hI
  · exact hrun
  · -- the condition reads the number of edges
    rintro ⟨k, φ'⟩ st hInv
    obtain ⟨G, s, tx, -, -, hG, -, -, -, -, -, hR, -⟩ := hInv
    have hm : st.mem (g + 3) = G.m := by simpa [dgMOff] using hG.2.2.2.2.2.2.1
    unfold dynGraphSize at hgw
    exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hR.2.2.1)
      (Expr.eval_const (k := 3) (by omega)) (by omega)) rfl
  · -- the exit
    rintro ⟨k, φ'⟩ st hInv h0
    obtain ⟨G, s, tx, hF, hphi, hG, hV, hsub, hm, hcord, hmarks, hR, hcur⟩ := hInv
    dsimp only at hm hphi hcur
    have hk : k = 0 := by
      rw [← hm, ← (by simpa [dgMOff] using hG.2.2.2.2.2.2.1 : st.mem (g + 3) = G.m)]; exact h0
    subst hk
    refine ⟨φ', ⟨rfl, G, s, tx, hF, hphi, hG, hV, hsub, hm, hcord, hmarks, hR, hcur⟩, ?_⟩
    simp only [rsCount, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
    omega
  · -- one round
    rintro ⟨k, φ'⟩ st hInv hne
    have hk : k ≠ 0 := by
      obtain ⟨G, s, tx, -, -, hG, -, -, hm, -, -, -, -⟩ := hInv
      dsimp only at hm
      rw [← hm, ← (by simpa [dgMOff] using hG.2.2.2.2.2.2.1 : st.mem (g + 3) = G.m)]; exact hne
    obtain ⟨st', c, hr, φ'', hI', hc⟩ :=
      rsDelBody_step T ω hp hpOps hfoot₀ hgh hdisj hends hw htour hgw hspace st hInv hk
    refine ⟨.normal, st', c, hr, (k - 1, φ''), hI', by dsimp only; omega, ?_⟩
    dsimp only
    have hkk : Cst * k = Cst * (k - 1) + Cst := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    simp only [rsCount, Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]
    omega

end DelLoop

end MinCostFlow.SparseCore.Program
