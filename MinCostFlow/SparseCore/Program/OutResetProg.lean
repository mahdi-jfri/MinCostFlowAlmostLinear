module

public import MinCostFlow.SparseCore.Program.OutStepSpec
public import MinCostFlow.SparseCore.Program.OutSmallSideProg
public import MinCostFlow.DynSpanner.Program.DynGraphDelete
public import MinCostFlow.DynSpanner.Program.DynGraphInsert

/-!
# The reset `outReset`: program and steps

At a restart the output graph `S_cur` of a branch is rebuilt (piece P8, then piece P10 writes the
new graph). The reset makes the stored output graph equal to the new graph `Snew`, and makes the
marked ends of the tour equal to the ends of the edges of `Snew`. It does this in two loops. The
first loop takes the last edge of the stored graph, unmarks its two ends and deletes it, until no
edge is left. The second loop reads the edges of `Snew` one by one, inserts each with its tail
and its head, and marks its two ends. Each round costs two tour calls and one graph call, so the
cost is the number of edges of both graphs times the log factor.

This file gives the program (`outResetBody`), the frame that it keeps (`RSFrame`), and what one
mark call (`rsMark_step`) and one graph call (`rsDelete_step`, `rsInsert_step`) do inside it.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-! ## The program -/

/-- A `setMark` call with flag `flag` on the end with key `keyE`; the heap pointer in register
`7` moves past the cells of the call. -/
def rsMark (sm flag : ℕ) (keyE : Expr) : Stmt :=
  .seq (.call 8 sm [.reg 1, keyE, .const flag, .reg 7]) (.assign 7 (.reg 8))

/-- The key `2 e` of the end `(e, true)` of the edge in register `5`. -/
def rsKey0 : Expr := .bin .add (.reg 5) (.reg 5)

/-- The key `2 e + 1` of the end `(e, false)` of the edge in register `5`. -/
def rsKey1 : Expr := .bin .add (.bin .add (.reg 5) (.reg 5)) (.const 1)

/-- The address `a + 4 + k₁ vCap + k₂ eCap` for the graph address `a` in register `r`, with the
caps in registers `10` and `11`. -/
def rsBase (r k₁ k₂ : ℕ) : Expr :=
  .bin .add (.bin .add (.bin .add (.reg r) (.const 4)) (.bin .mul (.const k₁) (.reg 10)))
    (.bin .mul (.const k₂) (.reg 11))

/-- The setup: the graph address in register `4`, the heap pointer in `7`, and the bases of the
arrays of both graphs (edge list of the stored graph in `12`; edge list, external names, tail
slots and head slots of the new graph in `14`, `15`, `16` and `17`). The caps are read from the
header of the stored graph into registers `10` and `11`. -/
def rsSetup : Stmt :=
  .seq (.assign 4 (.load (.reg 0)))
    (.seq (.assign 7 (.reg 3))
      (.seq (.assign 10 (.load (.reg 4)))
        (.seq (.assign 11 (.load (.bin .add (.reg 4) (.const 1))))
          (.seq (.assign 12 (rsBase 4 7 1))
            (.seq (.assign 14 (rsBase 2 7 1))
              (.seq (.assign 15 (rsBase 2 4 0))
                (.seq (.assign 16 (rsBase 2 7 3)) (.assign 17 (rsBase 2 7 4)))))))))

/-- The number of edges of the stored graph. -/
def rsCount : Expr := .load (.bin .add (.reg 4) (.const 3))

/-- One round of the first loop: take the last edge of the stored graph, unmark its two ends
and delete it. -/
def rsDelBody (sm dgb : ℕ) : Stmt :=
  .seq (.assign 5 (.load (.bin .sub (.bin .add (.reg 12) rsCount) (.const 1))))
    (.seq (rsMark sm 0 rsKey0)
      (.seq (rsMark sm 0 rsKey1) (.call 9 (dgb + dgIdxDeleteEdge) [.reg 4, .reg 5])))

/-- One round of the second loop: take the edge of the new graph at place `r13 - 1`, insert it
with its tail and its head, and mark its two ends. -/
def rsInsBody (sm dgb : ℕ) : Stmt :=
  .seq (.assign 13 (.bin .sub (.reg 13) (.const 1)))
    (.seq (.assign 5 (.load (.bin .add (.reg 14) (.reg 13))))
      (.seq (.assign 18 (.load (.bin .add (.reg 15) (.load (.bin .add (.reg 16) (.reg 5))))))
        (.seq (.assign 19 (.load (.bin .add (.reg 15) (.load (.bin .add (.reg 17) (.reg 5))))))
          (.seq (.call 9 (dgb + dgIdxInsertEdge) [.reg 4, .reg 5, .reg 18, .reg 19])
            (.seq (rsMark sm 1 rsKey0) (rsMark sm 1 rsKey1))))))

/-- **The reset `outReset`** `[outH, tourH, g₂, h]`, for the tour procedure `sm` (`setMark`)
and the graph edge procedures at `dgb` (`dgEdgeProcs`). -/
def outResetBody (sm dgb : ℕ) : Stmt :=
  .seq rsSetup
    (.seq (.loop rsCount (rsDelBody sm dgb))
      (.seq (.assign 13 (.load (.bin .add (.reg 2) (.const 3))))
        (.seq (.loop (.reg 13) (rsInsBody sm dgb)) (.ret (.reg 7)))))

/-! ## The frame -/

section Frame

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- The frame that the reset keeps at heap `cur`, for the tour state `s` held by `tx` in memory
`mem`, from the start state `tx₀` in memory `mem₀`: the tour holds `s`, memory is zero from `cur`
on, the tour takes only old cells or new cells below `cur`, and the cells below `h` outside the
stored graph at `g` and outside the old tour are unchanged. -/
def RSFrame (T : OutTourAt S w vCap eCap p nm sm fm lm) (tourH g h : ℕ) (tx₀ : T.rep.τ)
    (mem₀ : ℕ → ℕ) (cur : ℕ) (s : OutTourAbs) (tx : T.rep.τ) (mem : ℕ → ℕ) : Prop :=
  T.rep.rep tourH s tx mem ∧ ZeroFrom mem cur ∧ h ≤ cur ∧
    (∀ a, T.rep.foot tourH tx a → T.rep.foot tourH tx₀ a ∨ (h ≤ a ∧ a < cur)) ∧
    (∀ a < h, ¬ (g ≤ a ∧ a < g + dynGraphSize vCap eCap) → ¬ T.rep.foot tourH tx₀ a →
      mem a = mem₀ a)

theorem RSFrame.foot_lt {T : OutTourAt S w vCap eCap p nm sm fm lm} {tourH g h : ℕ}
    {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {cur : ℕ} {s : OutTourAbs} {tx : T.rep.τ} {mem : ℕ → ℕ}
    (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h)
    (hF : RSFrame T tourH g h tx₀ mem₀ cur s tx mem) : ∀ a, T.rep.foot tourH tx a → a < cur := by
  intro a ha
  rcases hF.2.2.2.1 a ha with ha | ⟨-, ha⟩
  · have := hfoot₀ a ha; have := hF.2.2.1; omega
  · exact ha

/-- The cells of the stored graph are not in the footprint of the tour. -/
theorem RSFrame.not_foot {T : OutTourAt S w vCap eCap p nm sm fm lm} {tourH g h : ℕ}
    {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {cur : ℕ} {s : OutTourAbs} {tx : T.rep.τ} {mem : ℕ → ℕ}
    (hgh : g + dynGraphSize vCap eCap ≤ h)
    (hdisj : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx₀ a)
    (hF : RSFrame T tourH g h tx₀ mem₀ cur s tx mem) :
    ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx a := by
  intro a h1 h2 hf
  rcases hF.2.2.2.1 a hf with hf | ⟨h3, -⟩
  · exact hdisj a h1 h2 hf
  · omega

/-- A write that changes only cells of the stored graph keeps the frame and the potential. -/
theorem RSFrame.of_graph_write {T : OutTourAt S w vCap eCap p nm sm fm lm} {tourH g h : ℕ}
    {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {cur : ℕ} {s : OutTourAbs} {tx : T.rep.τ}
    {mem mem' : ℕ → ℕ} (hgh : g + dynGraphSize vCap eCap ≤ h)
    (hdisj : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx₀ a)
    (hF : RSFrame T tourH g h tx₀ mem₀ cur s tx mem)
    (hout : ∀ a, a < g ∨ g + dynGraphSize vCap eCap ≤ a → mem' a = mem a) :
    RSFrame T tourH g h tx₀ mem₀ cur s tx mem' ∧
      T.rep.phi tourH tx mem' = T.rep.phi tourH tx mem := by
  have hnf := RSFrame.not_foot hgh hdisj hF
  have hagree : ∀ a, T.rep.foot tourH tx a → mem a = mem' a := by
    intro a ha
    refine (hout a ?_).symm
    by_contra hc
    exact hnf a (by omega) (by omega) ha
  obtain ⟨hrepI, hphi⟩ := T.rep_local tourH s tx mem mem' hagree
  obtain ⟨hrep, hz, hcur, hft, hfr⟩ := hF
  refine ⟨⟨hrepI hrep, fun a ha => by rw [hout a (by omega)]; exact hz a ha, hcur, hft,
    fun a ha hn hn' => ?_⟩, hphi.symm⟩
  rw [hout a (by omega)]; exact hfr a ha hn hn'

end Frame

/-! ## One mark call -/

section Mark

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- **A `setMark` call** on the end with key `key`, from the program. It keeps the frame with the
end marked or unmarked, keeps the cells of the stored graph, keeps the registers other than `7`
and `8`, and moves the heap pointer by at most the query space. -/
theorem rsMark_step (T : OutTourAt S w vCap eCap p nm sm fm lm) {tourH g h : ℕ}
    {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {cur : ℕ} {s : OutTourAbs} {tx : T.rep.τ} (st : State)
    (ω : ℕ → Bool) {flag : ℕ} {keyE : Expr} {key v : ℕ}
    (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h) (hgh : g + dynGraphSize vCap eCap ≤ h)
    (hdisj : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx₀ a)
    (hF : RSFrame T tourH g h tx₀ mem₀ cur s tx st.mem)
    (h1 : st.regs 1 = tourH) (h7 : st.regs 7 = cur) (hkeyE : keyE.eval w st = some key)
    (hkey : key < 2 * eCap) (hkeyw : key < 2 ^ w) (hflag : flag ≤ 1) (hv : v < vCap)
    (hmem : endOfKey key ∈ s.cord v) (htour : tourH < 2 ^ w)
    (hspace : cur + S.querySpace < 2 ^ w) :
    ∃ st' c tx', Runs w p ω (rsMark sm flag keyE) st .normal st' c ∧
      RSFrame T tourH g h tx₀ mem₀ (st'.regs 7) (s.setMark (endOfKey key) flag) tx' st'.mem ∧
      (∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → st'.mem a = st.mem a) ∧
      (∀ r, r ≠ 7 → r ≠ 8 → st'.regs r = st.regs r) ∧
      cur ≤ st'.regs 7 ∧ st'.regs 7 ≤ cur + S.querySpace ∧
      c + T.rep.phi tourH tx' st'.mem ≤
        S.mul * ordStoreLog eCap + keyE.size + 9 + T.rep.phi tourH tx st.mem := by
  have hq := S.querySpace_ge
  have h1w : 1 < 2 ^ w := by omega
  obtain ⟨body, hproc, o, st₁, c₁, tx', hrun, hrep', hresp, hcost⟩ :=
    T.setMark_runs tourH key flag v cur s tx st.mem st.pos ω htour hkey hkeyw hflag hv
      (by omega) hmem hF.1 (RSFrame.foot_lt hfoot₀ hF) hF.2.1 hspace
  have hargs : evalArgs w st [.reg 1, keyE, .const flag, .reg 7] = some [tourH, key, flag, cur] :=
    evalArgs_cons (Expr.eval_reg_of_eq h1) (evalArgs_cons hkeyE
      (evalArgs_cons (Expr.eval_const (by omega)) (evalArgs_cons (Expr.eval_reg_of_eq h7)
        (evalArgs_nil w st))))
  have hcall := runs_call_of (r := 8) (ω := ω) hargs hproc hrun
  set st₂ : State := { st₁ with regs := Function.update st.regs 8 o.value } with hst₂
  have ha := runs_assign_of (w := w) (p := p) (ω := ω) (r := 7) (st := st₂)
    (Expr.eval_reg_of_eq (r := 8) (v := o.value) (by simp [hst₂]))
  obtain ⟨hle, hle', hz', hkeep, hft'⟩ := hresp
  obtain ⟨-, hz, hcur, hft, hfr⟩ := hF
  have hnf : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx a := by
    intro a ha1 ha2 hf
    rcases hft a hf with hf | ⟨h3, -⟩
    · exact hdisj a ha1 ha2 hf
    · omega
  -- a cell below `h` outside the old tour keeps its word
  have hkeepH : ∀ a, a < h → ¬ T.rep.foot tourH tx₀ a → st₁.mem a = st.mem a := by
    intro a ha hn
    refine hkeep a (by omega) fun hf => ?_
    rcases hft a hf with hf | ⟨h3, -⟩
    · exact hn hf
    · omega
  refine ⟨_, _, tx', runs_seq_normal hcall ha, ⟨hrep', by simpa using hz', by simp; omega,
    ?_, ?_⟩, ?_, ?_, by simpa using hle, by simpa using hle', ?_⟩
  · intro a ha
    rcases hft' a ha with ha | ⟨h3, h4⟩
    · rcases hft a ha with ha | ⟨h5, h6⟩
      · exact Or.inl ha
      · exact Or.inr ⟨h5, by simp; omega⟩
    · exact Or.inr ⟨by omega, by simpa using h4⟩
  · intro a ha hn hn'
    show st₁.mem a = _
    rw [hkeepH a ha hn']; exact hfr a ha hn hn'
  · intro a ha1 ha2
    show st₁.mem a = _
    exact hkeep a (by omega) (hnf a ha1 ha2)
  · intro r h7' h8'
    simp [hst₂, Function.update_of_ne h7', Function.update_of_ne h8']
  · show argsSize _ + c₁ + 1 + _ + 1 + T.rep.phi tourH tx' st₁.mem ≤ _
    simp only [argsSize, Expr.size_reg, Expr.size_const]
    omega

end Mark

/-! ## One graph call -/

section Graph

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- **A delete call** on the stored graph at register `4`, of the edge in register `5`. It
changes only the cells of the stored graph, so it keeps the frame and the potential. -/
theorem rsDelete_step (T : OutTourAt S w vCap eCap p nm sm fm lm) {tourH g h : ℕ}
    {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {cur : ℕ} {s : OutTourAbs} {tx : T.rep.τ} (st : State)
    (ω : ℕ → Bool) {dgb bOps : ℕ} (hp : p.HasAt dgb (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) {G : MGraph} {e : ℕ}
    (hgh : g + dynGraphSize vCap eCap ≤ h)
    (hdisj : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx₀ a)
    (hF : RSFrame T tourH g h tx₀ mem₀ cur s tx st.mem)
    (hG : DynGraphAt st.mem g vCap eCap G) (h4 : st.regs 4 = g) (h5 : st.regs 5 = e)
    (hew : e < 2 ^ w) (hw16 : 16 ≤ 2 ^ w) (hgw : g + dynGraphSize vCap eCap < 2 ^ w) :
    ∃ st' c, Runs w p ω (.call 9 (dgb + dgIdxDeleteEdge) [.reg 4, .reg 5]) st .normal st' c ∧
      DynGraphAt st'.mem g vCap eCap (if e ∈ G.E then G.applyUpdate (.delete e) else G) ∧
      RSFrame T tourH g h tx₀ mem₀ cur s tx st'.mem ∧
      T.rep.phi tourH tx st'.mem = T.rep.phi tourH tx st.mem ∧
      (∀ r, r ≠ 9 → st'.regs r = st.regs r) ∧ c ≤ 453 := by
  obtain ⟨body, hproc, o, st₁, c₁, hrun, hpost, hc⟩ :=
    dgDeleteEdge_meetsContract (w := w) (vCap := vCap) (eCap := eCap) (G := G) hp hpOps
      [g, e] st.mem st.pos ω (by simp; omega) ⟨g, e, rfl, hw16, hgw, hG⟩
  obtain ⟨g', e', hargs', -, hG', hout⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs'
  obtain ⟨rfl, rfl⟩ := hargs'
  have hargs : evalArgs w st [.reg 4, .reg 5] = some [_, _] :=
    evalArgs_cons (Expr.eval_reg_of_eq h4) (evalArgs_cons (Expr.eval_reg_of_eq h5)
      (evalArgs_nil w st))
  have hcall := runs_call_of (r := 9) (ω := ω) hargs hproc hrun
  obtain ⟨hF', hphi⟩ := RSFrame.of_graph_write hgh hdisj hF (fun a ha => hout a ha)
  refine ⟨_, _, hcall, hG', hF', hphi, fun r hr => by simp [Function.update_of_ne hr], ?_⟩
  simp only [argsSize, Expr.size_reg, dgDeleteEdgeContract] at hc ⊢
  omega

/-- **An insert call** on the stored graph at register `4`, of the edge in register `5` with the
tail in register `18` and the head in register `19`. -/
theorem rsInsert_step (T : OutTourAt S w vCap eCap p nm sm fm lm) {tourH g h : ℕ}
    {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {cur : ℕ} {s : OutTourAbs} {tx : T.rep.τ} (st : State)
    (ω : ℕ → Bool) {dgb bOps : ℕ} (hp : p.HasAt dgb (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs) {G : MGraph} {e u v : ℕ}
    (hgh : g + dynGraphSize vCap eCap ≤ h)
    (hdisj : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → ¬ T.rep.foot tourH tx₀ a)
    (hF : RSFrame T tourH g h tx₀ mem₀ cur s tx st.mem)
    (hG : DynGraphAt st.mem g vCap eCap G) (h4 : st.regs 4 = g) (h5 : st.regs 5 = e)
    (h18 : st.regs 18 = u) (h19 : st.regs 19 = v) (hu : u ∈ G.V) (hv : v ∈ G.V)
    (hew : e < 2 ^ w) (huw : u < 2 ^ w) (hvw : v < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hgw : g + dynGraphSize vCap eCap < 2 ^ w) :
    ∃ st' c, Runs w p ω (.call 9 (dgb + dgIdxInsertEdge) [.reg 4, .reg 5, .reg 18, .reg 19]) st
      .normal st' c ∧
      DynGraphAt st'.mem g vCap eCap
        (if e < eCap ∧ e ∉ G.E then G.applyUpdate (.insert e u v) else G) ∧
      RSFrame T tourH g h tx₀ mem₀ cur s tx st'.mem ∧
      T.rep.phi tourH tx st'.mem = T.rep.phi tourH tx st.mem ∧
      (∀ r, r ≠ 9 → st'.regs r = st.regs r) ∧ c ≤ 455 := by
  obtain ⟨body, hproc, o, st₁, c₁, hrun, hpost, hc⟩ :=
    dgInsertEdge_meetsContract (w := w) (vCap := vCap) (eCap := eCap) (G := G) hp hpOps
      [g, e, u, v] st.mem st.pos ω (by simp; omega) ⟨g, e, u, v, rfl, hw16, hgw, hu, hv, hG⟩
  obtain ⟨g', e', u', v', hargs', -, hG', hout⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs'
  have hargs : evalArgs w st [.reg 4, .reg 5, .reg 18, .reg 19] = some [_, _, _, _] :=
    evalArgs_cons (Expr.eval_reg_of_eq h4) (evalArgs_cons (Expr.eval_reg_of_eq h5)
      (evalArgs_cons (Expr.eval_reg_of_eq h18) (evalArgs_cons (Expr.eval_reg_of_eq h19)
        (evalArgs_nil w st))))
  have hcall := runs_call_of (r := 9) (ω := ω) hargs hproc hrun
  obtain ⟨hF', hphi⟩ := RSFrame.of_graph_write hgh hdisj hF (fun a ha => hout a ha)
  refine ⟨_, _, hcall, hG', hF', hphi, fun r hr => by simp [Function.update_of_ne hr], ?_⟩
  simp only [argsSize, Expr.size_reg, dgInsertEdgeContract] at hc ⊢
  omega

end Graph

end MinCostFlow.SparseCore.Program
