module

public import MinCostFlow.SparseCore.Program.OutResetDel

/-!
# The reset `outReset`: the second loop

The second loop reads the edges of the new graph `Snew` from the end of its edge list. For each
edge it reads the tail and the head (through the slot arrays and the table of external names of
the new graph), inserts the edge in the stored graph, and marks its two ends
(`rsInsBody_step`, `rsInsLoop_runs`). After it, the stored graph has the edges of `Snew` with
their ends, and the marked ends are the ends of these edges.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

section InsLoop

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- The invariant of the second loop at `(k, φ)`: the stored graph `G` has the vertices of
`Sold` and the edges of the edge list `eL₂` of `Snew` from place `k` on, with the ends they have
in `Snew`; the marked ends are the ends of the edges of `G`; register `13` holds `k`; the
potential is `φ`; and the heap pointer has room for `k` more rounds. -/
def RS2Inv (T : OutTourAt S w vCap eCap p nm sm fm lm) (tourH g₂ g h : ℕ) (tx₀ : T.rep.τ)
    (mem₀ : ℕ → ℕ) (s₀ : OutTourAbs) (Sold Snew : MGraph) (eL₂ : List ℕ) (a : ℕ × ℕ)
    (st : State) : Prop :=
  ∃ (G : MGraph) (s : OutTourAbs) (tx : T.rep.τ),
    RSFrame T tourH g h tx₀ mem₀ (st.regs 7) s tx st.mem ∧ T.rep.phi tourH tx st.mem = a.2 ∧
    DynGraphAt st.mem g vCap eCap G ∧ G.V = Sold.V ∧ (∀ e, e ∈ G.E ↔ e ∈ eL₂.drop a.1) ∧
    (∀ e ∈ G.E, G.tail e = Snew.tail e ∧ G.head e = Snew.head e) ∧
    s.cord = s₀.cord ∧ (∀ z, z ∈ s.marked ↔ (∃ v, z ∈ s₀.cord v) ∧ z.1 ∈ G.E) ∧
    RSRegs st tourH g₂ g vCap eCap ∧ st.regs 13 = a.1 ∧ a.1 ≤ eL₂.length ∧
    st.regs 7 + 2 * a.1 * S.querySpace ≤ h + 2 * Sold.m * S.querySpace + 2 * Snew.m * S.querySpace

/-- **One round of the second loop.** -/
theorem rsInsBody_step (T : OutTourAt S w vCap eCap p nm sm fm lm) {tourH g₂ g h : ℕ}
    {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {s₀ : OutTourAbs} {Sold Snew : MGraph} {eL₂ : List ℕ}
    (ω : ℕ → Bool) {dgb bOps : ℕ} (hp : p.HasAt dgb (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h) (hgh : g + dynGraphSize vCap eCap ≤ h)
    (hdisj : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx₀ a)
    (hS₂ : DynGraphAt mem₀ g₂ vCap eCap Snew) (hVeq : Snew.V = Sold.V)
    (heL_len : eL₂.length = Snew.m) (heL_nd : eL₂.Nodup) (heL_mem : ∀ e, e ∈ eL₂ ↔ e ∈ Snew.E)
    (heL_at : ListAt mem₀ (dgEListBase g₂ vCap eCap) eL₂)
    (hg₂blk : ∀ a, g₂ ≤ a → a < g₂ + dynGraphSize vCap eCap →
      a < h ∧ ¬ (g ≤ a ∧ a < g + dynGraphSize vCap eCap) ∧ ¬ T.rep.foot tourH tx₀ a)
    (hends : ∀ e ∈ Snew.E, ∀ t : Bool, ∃ v < vCap, (e, t) ∈ s₀.cord v)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (htour : tourH < 2 ^ w)
    (hgw : g + dynGraphSize vCap eCap < 2 ^ w) (hg₂w : g₂ + dynGraphSize vCap eCap < 2 ^ w)
    (hspace : h + 2 * Sold.m * S.querySpace + 2 * Snew.m * S.querySpace < 2 ^ w)
    {k φ : ℕ} (st : State)
    (hI : RS2Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold Snew eL₂ (k, φ) st) (hk : k ≠ 0) :
    ∃ st' c, Runs w p ω (rsInsBody sm dgb) st .normal st' c ∧ ∃ φ',
      RS2Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold Snew eL₂ (k - 1, φ') st' ∧
      c + φ' ≤ 2 * (S.mul * ordStoreLog eCap) + 515 + φ := by
  obtain ⟨G, s, tx, hF, hphi, hG, hV, hGE, hGends, hcord, hmarks, hR, h13, hkl, hcur⟩ := hI
  dsimp only at hphi hGE h13 hkl hcur
  have hq := S.querySpace_ge
  have hkey : 2 * eCap + 2 < 2 ^ w := rs_key_lt hw
  have hkk : 2 * k * S.querySpace = 2 * (k - 1) * S.querySpace + 2 * S.querySpace := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  -- the cells of the new graph keep their words
  have hkeep₂ : ∀ a, g₂ ≤ a → a < g₂ + dynGraphSize vCap eCap → st.mem a = mem₀ a := by
    intro a ha1 ha2
    obtain ⟨hah, hag, haf⟩ := hg₂blk a ha1 ha2
    exact hF.2.2.2.2 a hah hag haf
  obtain ⟨hval₂, hVlt₂, hElt₂, -, -, -, -, -, -, hext₂, -, -, -, hends₂, -⟩ := hS₂
  unfold dynGraphSize at hgw hgh hg₂w hkeep₂
  have hk1 : k - 1 < eL₂.length := by omega
  have hmle : Snew.m ≤ eCap :=
    calc Snew.m = Snew.E.card := rfl
      _ ≤ (Finset.range eCap).card :=
        Finset.card_le_card fun x hx => Finset.mem_range.mpr (hElt₂ x hx)
      _ = eCap := Finset.card_range _
  have hkle : k ≤ eCap := by omega
  set e := eL₂[k - 1] with he_def
  have heS : e ∈ Snew.E := (heL_mem e).mp (List.getElem_mem hk1)
  have helt : e < eCap := hElt₂ e heS
  have hnotG : e ∉ G.E := by
    rw [hGE]
    intro hd
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hd
    rw [List.getElem_drop] at hie
    have := (List.Nodup.getElem_inj_iff heL_nd).mp hie
    omega
  -- register `13`
  have ha13 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 13) (st := st)
    (Expr.eval_sub (Expr.eval_reg_of_eq h13) (Expr.eval_const (k := 1) (by omega)) (by omega))
  set st1 : State := { st with regs := Function.update st.regs 13 (k - 1) } with hst1
  -- the edge
  have h14 : st1.regs 14 = g₂ + 4 + 7 * vCap + 1 * eCap := by simp [hst1, hR.2.2.2.2.2.2.1]
  have headdr : st1.mem (g₂ + 4 + 7 * vCap + 1 * eCap + (k - 1)) = e := by
    show st.mem _ = _
    rw [hkeep₂ _ (by omega) (by omega)]
    have := heL_at (k - 1) hk1
    unfold dgEListBase at this
    rw [show g₂ + 4 + 7 * vCap + 1 * eCap + (k - 1) = g₂ + 4 + 7 * vCap + eCap + (k - 1) by
      omega]
    exact this
  have ha5 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 5) (st := st1)
    (Expr.eval_load_of_eq (v := e) (Expr.eval_add (Expr.eval_reg_of_eq h14)
      (Expr.eval_reg_of_eq (r := 13) (v := k - 1) (by simp [hst1])) (by omega)) headdr)
  set st2 : State := { st1 with regs := Function.update st1.regs 5 e } with hst2
  -- the tail
  have htV : Snew.tail e ∈ Snew.V := (hval₂ e heS).1
  have hhV : Snew.head e ∈ Snew.V := (hval₂ e heS).2
  obtain ⟨hslt, hslt'⟩ := hext₂ _ htV
  obtain ⟨hslh, hslh'⟩ := hext₂ _ hhV
  have hsltlt := hVlt₂ _ hslt
  have hslhlt := hVlt₂ _ hslh
  simp only [dgExtToIntBase, dgIntToExtBase] at hslt' hslh' hsltlt hslhlt
  have hte := (hends₂ e heS).1
  have hhe := (hends₂ e heS).2
  simp only [dgETailSlotBase, dgEHeadSlotBase, dgExtToIntBase] at hte hhe
  have h16 : st2.regs 16 = g₂ + 4 + 7 * vCap + 3 * eCap := by
    simp [hst2, hst1, hR.2.2.2.2.2.2.2.2.1]
  have h17 : st2.regs 17 = g₂ + 4 + 7 * vCap + 4 * eCap := by
    simp [hst2, hst1, hR.2.2.2.2.2.2.2.2.2]
  have h15 : st2.regs 15 = g₂ + 4 + 4 * vCap + 0 * eCap := by
    simp [hst2, hst1, hR.2.2.2.2.2.2.2.1]
  have h5 : st2.regs 5 = e := by simp [hst2]
  set sT := mem₀ (g₂ + 4 + 3 * vCap + Snew.tail e) with hsT
  set sH := mem₀ (g₂ + 4 + 3 * vCap + Snew.head e) with hsH
  have hld16 : st2.mem (g₂ + 4 + 7 * vCap + 3 * eCap + e) = sT := by
    show st.mem _ = _
    rw [hkeep₂ _ (by omega) (by omega), hte]
  have hld17 : st2.mem (g₂ + 4 + 7 * vCap + 4 * eCap + e) = sH := by
    show st.mem _ = _
    rw [hkeep₂ _ (by omega) (by omega), hhe]
  have hld15t : st2.mem (g₂ + 4 + 4 * vCap + 0 * eCap + sT) = Snew.tail e := by
    show st.mem _ = _
    rw [hkeep₂ _ (by omega) (by omega)]
    rw [← hslt']; congr 1; omega
  have hld15h : st2.mem (g₂ + 4 + 4 * vCap + 0 * eCap + sH) = Snew.head e := by
    show st.mem _ = _
    rw [hkeep₂ _ (by omega) (by omega)]
    rw [← hslh']; congr 1; omega
  have htlt : Snew.tail e < vCap := hVlt₂ _ htV
  have hhlt : Snew.head e < vCap := hVlt₂ _ hhV
  have ha18 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 18) (st := st2)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h15)
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h16) (Expr.eval_reg_of_eq h5)
        (by omega)) hld16) (by omega)) hld15t)
  set st3 : State := { st2 with regs := Function.update st2.regs 18 (Snew.tail e) } with hst3
  have ha19 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 19) (st := st3)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (r := 15) (by simp [hst3, h15]))
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (r := 17) (by simp [hst3, h17]))
        (Expr.eval_reg_of_eq (r := 5) (by simp [hst3, h5])) (by omega)) hld17) (by omega))
      hld15h)
  set st4 : State := { st3 with regs := Function.update st3.regs 19 (Snew.head e) } with hst4
  -- insert the edge
  have h74 : st4.regs 7 = st.regs 7 := by simp [hst4, hst3, hst2, hst1]
  have hF4 : RSFrame T tourH g h tx₀ mem₀ (st4.regs 7) s tx st4.mem := by rw [h74]; exact hF
  have hG4 : DynGraphAt st4.mem g vCap eCap G := hG
  have h44 : st4.regs 4 = g := by simp [hst4, hst3, hst2, hst1, hR.2.2.1]
  have h54 : st4.regs 5 = e := by simp [hst4, hst3, h5]
  have hw16 := rs_sixteen_of_cap hw (by omega)
  obtain ⟨st5, c5, hr5, hG5, hF5, hphi5, hreg5, hc5⟩ :=
    rsInsert_step T st4 ω hp hpOps (G := G) (e := e) (u := Snew.tail e) (v := Snew.head e)
      (by unfold dynGraphSize; omega) hdisj hF4 hG4 h44 h54 (by simp [hst4, hst3])
      (by simp [hst4]) (by rw [hV, ← hVeq]; exact htV) (by rw [hV, ← hVeq]; exact hhV)
      (by omega) (by omega) (by omega) hw16 (by unfold dynGraphSize; omega)
  rw [ite_eq_left ⟨helt, hnotG⟩] at hG5
  have h75 : st5.regs 7 = st4.regs 7 := hreg5 7 (by norm_num)
  -- mark the end `(e, true)`
  obtain ⟨v₀, hv₀, hc₀⟩ := hends e heS true
  have h55 : st5.regs 5 = e := by rw [hreg5 5 (by norm_num)]; exact h54
  have hk0 : rsKey0.eval w st5 = some (e + e) :=
    Expr.eval_add (Expr.eval_reg_of_eq h55) (Expr.eval_reg_of_eq h55) (by omega)
  have h15' : st5.regs 1 = tourH := by
    rw [hreg5 1 (by norm_num)]; simp [hst4, hst3, hst2, hst1, hR.1]
  obtain ⟨st6, c6, tx6, hr6, hF6, hblk6, hreg6, hle6, hle6', hc6⟩ :=
    rsMark_step T st5 ω (flag := 1) (v := v₀) hfoot₀ (by unfold dynGraphSize; omega) hdisj
      (by rw [h75]; exact hF5) h15' rfl hk0 (by omega) (by omega) le_rfl hv₀
      (by rw [endOfKey_two_mul, hcord]; exact hc₀) htour (by rw [h75, h74]; omega)
  -- mark the end `(e, false)`
  obtain ⟨v₁, hv₁, hc₁⟩ := hends e heS false
  have h56 : st6.regs 5 = e := by rw [hreg6 5 (by norm_num) (by norm_num)]; exact h55
  have hk1' : rsKey1.eval w st6 = some (e + e + 1) :=
    Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h56) (Expr.eval_reg_of_eq h56) (by omega))
      (Expr.eval_const (k := 1) (by omega)) (by omega)
  obtain ⟨st7, c7, tx7, hr7, hF7, hblk7, hreg7, hle7, hle7', hc7⟩ :=
    rsMark_step T st6 ω (flag := 1) (v := v₁) hfoot₀ (by unfold dynGraphSize; omega) hdisj hF6
      (by rw [hreg6 1 (by norm_num) (by norm_num)]; exact h15') rfl hk1' (by omega) (by omega)
      le_rfl hv₁ (by rw [endOfKey_two_mul_add_one]; show _ ∈ s.cord v₁; rw [hcord]; exact hc₁)
      htour (by rw [h75, h74] at hle6'; omega)
  have hG7 : DynGraphAt st7.mem g vCap eCap (G.applyUpdate (.insert e (Snew.tail e) (Snew.head e))) :=
    DynGraphAt.of_agree hG5 fun a ha1 ha2 => by rw [hblk7 a ha1 ha2, hblk6 a ha1 ha2]
  have hdrop : eL₂.drop (k - 1) = e :: eL₂.drop k := by
    rw [List.drop_eq_getElem_cons hk1, show k - 1 + 1 = k by omega]
  refine ⟨st7, _, runs_seq_normal ha13 (runs_seq_normal ha5 (runs_seq_normal ha18
    (runs_seq_normal ha19 (runs_seq_normal hr5 (runs_seq_normal hr6 hr7))))),
    T.rep.phi tourH tx7 st7.mem, ⟨G.applyUpdate (.insert e (Snew.tail e) (Snew.head e)),
      ((s.setMark (endOfKey (e + e)) 1).setMark (endOfKey (e + e + 1)) 1), tx7, hF7, rfl, hG7,
      hV, ?_, ?_, hcord, ?_, ?_, ?_, by dsimp only; omega, ?_⟩, ?_⟩
  · intro x
    show x ∈ insert e G.E ↔ _
    rw [Finset.mem_insert, hGE, hdrop, List.mem_cons]
  · intro x hx
    show Function.update G.tail e (Snew.tail e) x = _ ∧ Function.update G.head e (Snew.head e) x = _
    by_cases hxe : x = e
    · subst hxe; simp
    · rw [Function.update_of_ne hxe, Function.update_of_ne hxe]
      exact hGends x ((Finset.mem_insert.mp hx).resolve_left hxe)
  · intro z
    rw [endOfKey_two_mul, endOfKey_two_mul_add_one, mem_mark_both, hmarks]
    show _ ↔ _ ∧ z.1 ∈ insert e G.E
    rw [Finset.mem_insert]
    constructor
    · rintro (⟨hz, hzG⟩ | hze)
      · exact ⟨hz, Or.inr hzG⟩
      · obtain ⟨z1, z2⟩ := z
        dsimp only at hze
        obtain ⟨v, -, hv⟩ := hends e heS z2
        exact ⟨⟨v, by rw [hze]; exact hv⟩, Or.inl hze⟩
    · rintro ⟨hz, hze | hzG⟩
      · exact Or.inr hze
      · exact Or.inl ⟨hz, hzG⟩
  · refine hR.of_regs fun r h5' h7' h8' h9' h13' h18' h19' => ?_
    rw [hreg7 r h7' h8', hreg6 r h7' h8', hreg5 r h9']
    simp [hst4, hst3, hst2, hst1, Function.update_of_ne h5', Function.update_of_ne h13',
      Function.update_of_ne h18', Function.update_of_ne h19']
  · rw [hreg7 13 (by norm_num) (by norm_num), hreg6 13 (by norm_num) (by norm_num),
      hreg5 13 (by norm_num)]
    simp [hst4, hst3, hst2, hst1]
  · dsimp only
    rw [h75, h74] at hle6 hle6'
    omega
  · simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const, rsKey0,
      rsKey1] at hc6 hc7 ⊢
    have hphi4 : T.rep.phi tourH tx st4.mem = φ := hphi
    rw [hphi5, hphi4] at hc6
    omega

/-- **The second loop.** From `k = Snew.m` it runs until all edges of `Snew` are inserted. -/
theorem rsInsLoop_runs (T : OutTourAt S w vCap eCap p nm sm fm lm) {tourH g₂ g h : ℕ}
    {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {s₀ : OutTourAbs} {Sold Snew : MGraph} {eL₂ : List ℕ}
    (ω : ℕ → Bool) {dgb bOps : ℕ} (hp : p.HasAt dgb (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h) (hgh : g + dynGraphSize vCap eCap ≤ h)
    (hdisj : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx₀ a)
    (hS₂ : DynGraphAt mem₀ g₂ vCap eCap Snew) (hVeq : Snew.V = Sold.V)
    (heL_len : eL₂.length = Snew.m) (heL_nd : eL₂.Nodup) (heL_mem : ∀ e, e ∈ eL₂ ↔ e ∈ Snew.E)
    (heL_at : ListAt mem₀ (dgEListBase g₂ vCap eCap) eL₂)
    (hg₂blk : ∀ a, g₂ ≤ a → a < g₂ + dynGraphSize vCap eCap →
      a < h ∧ ¬ (g ≤ a ∧ a < g + dynGraphSize vCap eCap) ∧ ¬ T.rep.foot tourH tx₀ a)
    (hends : ∀ e ∈ Snew.E, ∀ t : Bool, ∃ v < vCap, (e, t) ∈ s₀.cord v)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (htour : tourH < 2 ^ w)
    (hgw : g + dynGraphSize vCap eCap < 2 ^ w) (hg₂w : g₂ + dynGraphSize vCap eCap < 2 ^ w)
    (hspace : h + 2 * Sold.m * S.querySpace + 2 * Snew.m * S.querySpace < 2 ^ w)
    (φ : ℕ) (st : State)
    (hI : RS2Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold Snew eL₂ (Snew.m, φ) st) :
    ∃ o st' c, Runs w p ω (.loop (.reg 13) (rsInsBody sm dgb)) st o st' c ∧ ∃ r,
      (o = .normal ∧ RS2Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold Snew eL₂ (0, r) st') ∧
      c + r ≤ (2 * (S.mul * ordStoreLog eCap) + 520) * Snew.m + 10 + φ := by
  set Cst := 2 * (S.mul * ordStoreLog eCap) + 520 with hCst
  have hrun := MinCostFlow.LowStretch.runs_loop_amort (w := w) (p := p) (ω := ω) (e := .reg 13)
    (body := rsInsBody sm dgb) (Inv := RS2Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold Snew eL₂)
    (Fin := fun o st r => o = .normal ∧ RS2Inv T tourH g₂ g h tx₀ mem₀ s₀ Sold Snew eL₂ (0, r) st)
    (fun a => a.1) (fun a => Cst * a.1 + 10 + a.2) (condVal := fun st => st.regs 13)
    (fun a st _ => Expr.eval_reg w 13 st) ?_ ?_ (Snew.m, φ) st hI
  · exact hrun
  · -- the exit
    rintro ⟨k, φ'⟩ st hInv h0
    obtain ⟨G, s, tx, hF, hphi, hG, hV, hGE, hGends, hcord, hmarks, hR, h13, hkl, hcur⟩ := hInv
    dsimp only at h13 hphi hGE hkl hcur h0
    have hk : k = 0 := by rw [← h13]; exact h0
    subst hk
    refine ⟨φ', ⟨rfl, G, s, tx, hF, hphi, hG, hV, hGE, hGends, hcord, hmarks, hR, h13, hkl, hcur⟩,
      ?_⟩
    simp only [Expr.size_reg]
    omega
  · -- one round
    rintro ⟨k, φ'⟩ st hInv hne
    have hk : k ≠ 0 := by
      have h13 := hInv.choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2.1
      dsimp only at h13 hne
      omega
    obtain ⟨st', c, hr, φ'', hI', hc⟩ :=
      rsInsBody_step T ω hp hpOps hfoot₀ hgh hdisj hS₂ hVeq heL_len heL_nd heL_mem heL_at hg₂blk
        hends hw htour hgw hg₂w hspace st hInv hk
    refine ⟨.normal, st', c, hr, (k - 1, φ''), hI', by dsimp only; omega, ?_⟩
    dsimp only
    have hkk : Cst * k = Cst * (k - 1) + Cst := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    simp only [Expr.size_reg]
    omega

end InsLoop

end MinCostFlow.SparseCore.Program
