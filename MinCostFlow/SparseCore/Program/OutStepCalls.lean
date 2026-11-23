module

public import MinCostFlow.SparseCore.Program.OutStepFrame
public import MinCostFlow.SparseCore.Program.OutStepRun
public import MinCostFlow.DynSpanner.Program.DynGraphBatch

/-!
# The calls of the output step

The output step calls the tour (`setMark`, `nextMarked`, `firstMarked`), the stored graph
(`dgApplyUpdate`, `dgGetDeg`), and its two small procedures (the filter and the walk). This file
proves one lemma per kind of call: the call runs, keeps the frame `SBase` of `OutStepFrame.lean`,
and costs what the callee says.

* `os_mark`: a `setMark` call (`rsMark`).
* `os_query`: a tour query (`osQuery`), from the run of the query that the tour gives.
* `os_apply`: a `dgApplyUpdate` call on the record at register `14`.
* `os_deg`: a `dgGetDeg` call.
* `os_filter` and `os_walk`: the filter and the walk, which write into the free part of the two
  regions.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ}
  {mem₀ : ℕ → ℕ} {S₀ G : MGraph} {U : List Update} {E : List OrdEdit} {bp ep cur : ℕ}
  {s : OutTourAbs} {tx : T.rep.τ}

/-- A cell of the tour lies below the heap pointer. -/
theorem SBase.foot_lt_cur (hC : SCtx T A tx₀) {mem : ℕ → ℕ}
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx mem) :
    ∀ a, T.rep.foot A.tourH tx a → a < cur := by
  intro a ha
  have h1 := hB.2.2.1
  have : A.h ≤ A.t0 := by unfold OSArgs.t0; omega
  rcases hB.foot_lt hC ha with ⟨h2, -⟩ | ⟨-, h2⟩ <;> omega

/-! ## Tour calls -/

/-- **A `setMark` call** on the end with key `key`. -/
theorem os_mark (hC : SCtx T A tx₀) {st : State} {flag key v : ℕ} {keyE : Expr}
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st.mem)
    (h1 : st.regs 1 = A.tourH) (h7 : st.regs 7 = cur) (hkeyE : keyE.eval w st = some key)
    (hkey : key < 2 * eCap) (hkeyw : key < 2 ^ w) (hflag : flag ≤ 1) (hv : v < vCap)
    (hmem : endOfKey key ∈ s.cord v) (htour : A.tourH < 2 ^ w)
    (hspace : cur + S.querySpace < 2 ^ w) :
    ∃ st' c tx', Runs w p ω (rsMark sm flag keyE) st .normal st' c ∧
      SBase T A tx₀ mem₀ S₀ G U E bp ep (st'.regs 7) (s.setMark (endOfKey key) flag) tx'
        st'.mem ∧
      (∀ a, a < A.t0 → ¬ T.rep.foot A.tourH tx₀ a → st'.mem a = st.mem a) ∧
      (∀ r, r ≠ 7 → r ≠ 8 → st'.regs r = st.regs r) ∧
      cur ≤ st'.regs 7 ∧ st'.regs 7 ≤ cur + S.querySpace ∧
      c + T.rep.phi A.tourH tx' st'.mem ≤
        S.mul * ordStoreLog eCap + keyE.size + 9 + T.rep.phi A.tourH tx st.mem := by
  have hq := S.querySpace_ge
  obtain ⟨body, hproc, o, st₁, c₁, tx', hrun, hrep', hresp, hcost⟩ :=
    T.setMark_runs A.tourH key flag v cur s tx st.mem st.pos ω htour hkey hkeyw hflag hv
      (by omega) hmem hB.1 (hB.foot_lt_cur hC) hB.2.1 hspace
  have hargs : evalArgs w st [.reg 1, keyE, .const flag, .reg 7] = some [A.tourH, key, flag, cur] :=
    evalArgs_four (Expr.eval_reg_of_eq h1) hkeyE (Expr.eval_const (by omega))
      (Expr.eval_reg_of_eq h7)
  obtain ⟨st₂, hr₂, hm₂, h8₂, ho₂⟩ := step_call (r := 8) (ω := ω) hargs hproc hrun
  obtain ⟨st₃, hr₃, hm₃, h7₃, ho₃⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 7) (e := .reg 8)
    (st := st₂) (Expr.eval_reg_of_eq h8₂)
  have hresp' := hresp
  obtain ⟨hle, hle', -, -, -⟩ := hresp'
  obtain ⟨hB', hk⟩ := hB.of_tour hC hrep' hresp
  refine ⟨st₃, _, tx', runs_seq_normal hr₂ hr₃, ?_, ?_, ?_, by omega, by omega, ?_⟩
  · rw [hm₃, hm₂, h7₃]; exact hB'
  · intro a ha hn; rw [hm₃, hm₂]; exact hk a ha hn
  · intro r h7' h8'; rw [ho₃ r h7', ho₂ r h8']
  · rw [hm₃, hm₂]
    simp only [argsSize, Expr.size_reg, Expr.size_const] at hcost ⊢
    omega

/-- **A tour query** `[tourH, arg, cur]` at procedure `f`, from a run of the query that keeps
the tour as `s'` and writes the answer `ans` at `cur`. -/
theorem os_query (hC : SCtx T A tx₀) {st : State} {f arg dst ans : ℕ} {argE : Expr}
    {s' : OutTourAbs}
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st.mem)
    (h1 : st.regs 1 = A.tourH) (h7 : st.regs 7 = cur) (hargE : argE.eval w st = some arg)
    (hdst7 : dst ≠ 7) (hdst8 : dst ≠ 8)
    (hrun : ∃ body, p.procs[f]? = some body ∧ ∃ o st₁ c₁ tx',
      Runs w p ω body (startState [A.tourH, arg, cur] st.mem st.pos) o st₁ c₁ ∧
      T.rep.rep A.tourH s' tx' st₁.mem ∧ st₁.mem cur = ans ∧ cur + 1 ≤ o.value ∧
      T.rep.Respects (T.rep.foot A.tourH tx) cur S.querySpace st.mem o.value A.tourH tx'
        st₁.mem ∧
      c₁ + T.rep.phi A.tourH tx' st₁.mem ≤ S.mul * ordStoreLog eCap + T.rep.phi A.tourH tx st.mem) :
    ∃ st' c tx', Runs w p ω (osQuery f argE dst) st .normal st' c ∧
      SBase T A tx₀ mem₀ S₀ G U E bp ep (st'.regs 7) s' tx' st'.mem ∧
      (∀ a, a < A.t0 → ¬ T.rep.foot A.tourH tx₀ a → st'.mem a = st.mem a) ∧
      st'.regs dst = ans ∧
      (∀ r, r ≠ 7 → r ≠ 8 → r ≠ dst → st'.regs r = st.regs r) ∧
      cur + 1 ≤ st'.regs 7 ∧ st'.regs 7 ≤ cur + S.querySpace ∧
      c + T.rep.phi A.tourH tx' st'.mem ≤
        S.mul * ordStoreLog eCap + argE.size + 12 + T.rep.phi A.tourH tx st.mem := by
  obtain ⟨body, hproc, o, st₁, c₁, tx', hrun, hrep', hans, hcur1, hresp, hcost⟩ := hrun
  have hargs : evalArgs w st [.reg 1, argE, .reg 7] = some [A.tourH, arg, cur] :=
    evalArgs_three (Expr.eval_reg_of_eq h1) hargE (Expr.eval_reg_of_eq h7)
  obtain ⟨st₂, hr₂, hm₂, h8₂, ho₂⟩ := step_call (r := 8) (ω := ω) hargs hproc hrun
  obtain ⟨st₃, hr₃, hm₃, hd₃, ho₃⟩ := step_assign (w := w) (p := p) (ω := ω) (r := dst)
    (e := .load (.reg 7)) (st := st₂)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by rw [ho₂ 7 (by omega), h7])) (by rw [hm₂]))
  obtain ⟨st₄, hr₄, hm₄, h7₄, ho₄⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 7) (e := .reg 8)
    (st := st₃) (Expr.eval_reg_of_eq (by rw [ho₃ 8 (Ne.symm hdst8), h8₂]))
  have hresp' := hresp
  obtain ⟨hle, hle', -, -, -⟩ := hresp'
  obtain ⟨hB', hk⟩ := hB.of_tour hC hrep' hresp
  refine ⟨st₄, _, tx', runs_seq_normal hr₂ (runs_seq_normal hr₃ hr₄), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm₄, hm₃, hm₂, h7₄]; exact hB'
  · intro a ha hn; rw [hm₄, hm₃, hm₂]; exact hk a ha hn
  · rw [ho₄ dst hdst7, hd₃, hans]
  · intro r h7' h8' hd'; rw [ho₄ r h7', ho₃ r hd', ho₂ r h8']
  · rw [h7₄]; omega
  · rw [h7₄]; omega
  · rw [hm₄, hm₃, hm₂]
    simp only [argsSize, Expr.size_reg, Expr.size_load] at hcost ⊢
    omega

/-! ## Graph calls -/

/-- **A `dgApplyUpdate` call** on the record of `len` words at register `14`, which lies in the
batch region. -/
theorem os_apply (hC : SCtx T A tx₀) {au : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    {st : State} {u : Update} {len : ℕ}
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st.mem)
    (h10 : st.regs 10 = A.g) (h14 : st.regs 14 = bp)
    (hu : UpdateAt st.mem bp G u len) (hval : G.UpdateIsValid u)
    (hcap : UpdateWithinCaps vCap eCap u) (hle : bp + len ≤ A.e0)
    (hwords : ∀ i < len, st.mem (bp + i) < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hgw : A.g + dynGraphSize vCap eCap < 2 ^ w) (hbw : bp + len < 2 ^ w) :
    ∃ st' c, Runs w p ω (.call 9 au [.reg 10, .reg 14, .const 1]) st .normal st' c ∧
      SBase T A tx₀ mem₀ S₀ (G.applyUpdate u) U E bp ep cur s tx st'.mem ∧
      T.rep.phi A.tourH tx st'.mem = T.rep.phi A.tourH tx st.mem ∧
      (∀ a, a < A.g ∨ A.g + dynGraphSize vCap eCap ≤ a → st'.mem a = st.mem a) ∧
      (∀ r, r ≠ 9 → st'.regs r = st.regs r) ∧ c ≤ 640 * len + 5 := by
  have hgh := hC.2.2.1
  have hbpw : bp < 2 ^ w := by omega
  have hargs : evalArgs w st [.reg 10, .reg 14, .const 1] = some [A.g, bp, 1] :=
    evalArgs_three (Expr.eval_reg_of_eq h10) (Expr.eval_reg_of_eq h14)
      (Expr.eval_const (by omega))
  have hpre : (dgApplyUpdateContract w vCap eCap G G u len).pre [A.g, bp, 1] st.mem := by
    have hbp := hB.2.2.2.2.2.2.2.1
    refine ⟨A.g, bp, 1, rfl, hw16, hgw, hbw, fun i _ => Or.inr (by omega), hwords, hu, hval, hcap,
      hB.2.2.2.2.2.2.1, Or.inl ⟨one_ne_zero, rfl⟩⟩
  obtain ⟨st', c, v, hrun, hpost, -, ho, hc⟩ := runs_call_of_meetsContract (r := 9) (hau G G u len)
    hargs (by intro a ha; simp at ha; omega) hpre ω
  obtain ⟨g', u', ai, hargs', -, hG', hfr⟩ := hpost
  simp only [List.cons.injEq] at hargs'
  obtain ⟨rfl, rfl, rfl, -⟩ := hargs'
  simp only [dgBatchTarget, one_ne_zero, ite_false] at hG'
  obtain ⟨hB', hphi⟩ := hB.of_graph hC hG' hfr
  refine ⟨st', c, hrun, hB', hphi, hfr, ho, ?_⟩
  simp only [dgApplyUpdateContract, argsSize, Expr.size_reg, Expr.size_const, List.map,
    List.sum_cons, List.sum_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some, dgUpdateMemLen_eq hu] at hc
  omega

/-- **A `dgGetDeg` call** on the vertex in register `r`. -/
theorem os_deg {gd : ℕ} (hgd : ∀ G, MeetsContract w p gd (dgGetDegContract w vCap eCap G))
    {st : State} {dst r v : ℕ} (hG : DynGraphAt st.mem A.g vCap eCap G)
    (h10 : st.regs 10 = A.g) (hr : st.regs r = v) (hv : v ∈ G.V) (hw16 : 16 ≤ 2 ^ w)
    (hgw : A.g + dynGraphSize vCap eCap < 2 ^ w) :
    ∃ st' c, Runs w p ω (.call dst gd [.reg 10, .reg r]) st .normal st' c ∧
      st'.mem = st.mem ∧ st'.regs dst = G.deg v ∧ (∀ j, j ≠ dst → st'.regs j = st.regs j) ∧
      c ≤ 50 := by
  have hvw : v < 2 ^ w := by
    have := hG.2.1 v hv
    unfold dynGraphSize at hgw
    omega
  have hargs : evalArgs w st [.reg 10, .reg r] = some [A.g, v] :=
    evalArgs_two (Expr.eval_reg_of_eq h10) (Expr.eval_reg_of_eq hr)
  obtain ⟨st', c, ret, hrun, hpost, hret, ho, hc⟩ := runs_call_of_meetsContract (r := dst) (hgd G)
    hargs (by intro a ha; simp at ha; omega) ⟨A.g, v, rfl, hw16, hgw, hv, hG⟩ ω
  obtain ⟨g', v', hargs', hm, hdeg⟩ := hpost
  simp only [List.cons.injEq] at hargs'
  obtain ⟨rfl, rfl, -⟩ := hargs'
  refine ⟨st', c, hrun, hm, by rw [hret, hdeg], ho, ?_⟩
  simp only [dgGetDegContract, argsSize, Expr.size_reg, List.map, List.sum_cons,
    List.sum_nil] at hc
  omega

/-! ## The filter and the walk -/

/-- **A filter call** that writes into the free cells from `dst` on, in `[h, t0)` and after the
records. -/
theorem os_filter (hC : SCtx T A tx₀) {flt : ℕ} (hflt : p.procs[flt]? = some outFilterBody)
    {st : State} {r : ℕ} {args : List Expr} {src n par dst pb : ℕ} {K : List ℕ}
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st.mem)
    (hargs : evalArgs w st args = some [src, n, par, dst, pb])
    (hK : ListAt st.mem src K) (hn : K.length = n)
    (hw : ∀ k ∈ K, pb + k < 2 ^ w) (hsrc : src + n < 2 ^ w) (hdstw : dst + n < 2 ^ w)
    (h2w : 2 < 2 ^ w)
    (hdsrc : ∀ i < n, ∀ j < n, src + i ≠ dst + j)
    (hdpb : ∀ k ∈ K, ∀ j < n, pb + k / 2 ≠ dst + j)
    (hfree : ∀ j < n, A.h ≤ dst + j ∧ dst + j < A.t0 ∧ ¬ (A.h + 5 ≤ dst + j ∧ dst + j < bp) ∧
      ¬ (A.e0 + 1 ≤ dst + j ∧ dst + j < ep)) :
    ∃ st' c, Runs w p ω (.call r flt args) st .normal st' c ∧
      SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st'.mem ∧
      T.rep.phi A.tourH tx st'.mem = T.rep.phi A.tourH tx st.mem ∧
      ListAt st'.mem dst (keyFilterMem st.mem pb K par) ∧
      (∀ a, ¬ (dst ≤ a ∧ a < dst + n) → st'.mem a = st.mem a) ∧
      st'.regs r = (keyFilterMem st.mem pb K par).length ∧
      (∀ j, j ≠ r → st'.regs j = st.regs j) ∧ c ≤ argsSize args + 60 * (n + 1) + 1 := by
  obtain ⟨st₁, c₁, hrun, hL, hag, hc⟩ := outFilter_runs (p := p) (ω := ω) st.mem st.pos hK hn hw
    hsrc hdstw h2w hdsrc hdpb
  have hlen := keyFilterMem_length_le st.mem pb K par
  obtain ⟨st', hr, hm, hrr, ho⟩ := step_call (r := r) (ω := ω) hargs hflt hrun
  have hag' : ∀ a, ¬ (dst ≤ a ∧ a < dst + n) → st'.mem a = st.mem a := by
    intro a ha; rw [hm]; exact hag a (fun h => ha ⟨h.1, by omega⟩)
  obtain ⟨hB', hphi⟩ := hB.of_own hC (mem' := st'.mem) fun a ha => by
    refine hag' a fun ⟨h1, h2⟩ => ?_
    obtain ⟨f1, f2, f3, f4⟩ := hfree (a - dst) (by omega)
    rw [show dst + (a - dst) = a by omega] at f1 f2 f3 f4
    rcases ha with ha | ha | ha | ha <;> omega
  exact ⟨st', _, hr, hB', hphi, by rw [hm]; exact hL, hag', hrr, ho, by omega⟩

/-- **A walk call** that copies the list `L` into the free cells from `dst` on. -/
theorem os_walk (hC : SCtx T A tx₀) {wk : ℕ} (hwk : p.procs[wk]? = some outWalkBody)
    {st : State} {r : ℕ} {args : List Expr} {prevB nb head dst cap : ℕ} {L : List ℕ}
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st.mem)
    (hargs : evalArgs w st args = some [nb, head, dst])
    (hL : IsDoublyLinkedList st.mem prevB nb head cap L)
    (hw : ∀ x ∈ L, nb + x + 1 < 2 ^ w) (hdstw : dst + L.length < 2 ^ w) (h2w : 2 < 2 ^ w)
    (hdhead : ∀ j < L.length, head ≠ dst + j)
    (hdnb : ∀ x ∈ L, ∀ j < L.length, nb + x ≠ dst + j)
    (hfree : ∀ j < L.length, A.h ≤ dst + j ∧ dst + j < A.t0 ∧
      ¬ (A.h + 5 ≤ dst + j ∧ dst + j < bp) ∧ ¬ (A.e0 + 1 ≤ dst + j ∧ dst + j < ep)) :
    ∃ st' c, Runs w p ω (.call r wk args) st .normal st' c ∧
      SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st'.mem ∧
      T.rep.phi A.tourH tx st'.mem = T.rep.phi A.tourH tx st.mem ∧
      ListAt st'.mem dst L ∧
      (∀ a, ¬ (dst ≤ a ∧ a < dst + L.length) → st'.mem a = st.mem a) ∧
      st'.regs r = L.length ∧
      (∀ j, j ≠ r → st'.regs j = st.regs j) ∧ c ≤ argsSize args + 30 * (L.length + 1) + 1 := by
  obtain ⟨st₁, c₁, hrun, hL', hag, hc⟩ := outWalk_runs (p := p) (ω := ω) st.mem st.pos hL hw
    hdstw h2w hdhead hdnb
  obtain ⟨st', hr, hm, hrr, ho⟩ := step_call (r := r) (ω := ω) hargs hwk hrun
  have hag' : ∀ a, ¬ (dst ≤ a ∧ a < dst + L.length) → st'.mem a = st.mem a := by
    intro a ha; rw [hm]; exact hag a ha
  obtain ⟨hB', hphi⟩ := hB.of_own hC (mem' := st'.mem) fun a ha => by
    refine hag' a fun ⟨h1, h2⟩ => ?_
    obtain ⟨f1, f2, f3, f4⟩ := hfree (a - dst) (by omega)
    rw [show dst + (a - dst) = a by omega] at f1 f2 f3 f4
    rcases ha with ha | ha | ha | ha <;> omega
  exact ⟨st', _, hr, hB', hphi, by rw [hm]; exact hL', hag', hrr, ho, by omega⟩

end MinCostFlow.SparseCore.Program
