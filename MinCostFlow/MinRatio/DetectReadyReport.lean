module

public import MinCostFlow.MinRatio.DetectTreeReport
public import MinCostFlow.MinRatio.DetectReportArgs
public import MinCostFlow.MinRatio.DetectForestAccounts

/-!
# The successful branch of Detect

The proof of Theorem 5.1 (pages 29–30) reports a ready edge, resets
its account, and continues searching. This branch prepares the
report arguments, performs that update, and advances the cursor.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain LinkCut

/-- The ready slot is in register 3. Report it and advance the heap and cursor. -/
@[expose] def detectReadyReport (entry : ℕ) : Stmt :=
  detectReportArgs ;; detectTreeReportCall entry ;; detectReportAdvance

/-- The ready branch has no random statements. -/
theorem detectReadyReport_noRand (entry : ℕ) : (detectReadyReport entry).NoRand := by
  simp [detectReadyReport, detectReportArgs_noRand, detectTreeReportCall, detectReportAdvance, Stmt.NoRand]

/-- A successful Detect branch extends the report and updates the
tree, leaving the advanced registers and an amortized cost bound. -/
theorem detectReadyReport_runs {w L constant init handle names inv slot cursor src th heap
    prepare report entry table : ℕ}
    {fmt : Num.Format w} {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {s : PathTreeState} {x : R.τ} {edge : PathEdgeValue} {threshold : ℤ}
    (written : List ℕ)
    (hentry : p.procs[entry]? = some (detectTreeReportBody prepare (op 5)))
    (hregs : st.regs 0 = handle ∧ st.regs 6 = names ∧ st.regs 7 = inv ∧ st.regs 3 = slot ∧
      st.regs 8 = cursor ∧ st.regs 4 = src ∧ st.regs 10 = L ∧ st.regs 13 = heap ∧ st.regs 14 = table)
    (hth : st.mem (table + slot) = th) (htable : table + slot < 2 ^ w)
    (hadvance : cursor + 1 < 2 ^ w)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hp : MeetsContract w p prepare (detectSlotStepContract w fmt.limbBits report written edge threshold))
    (hw : ∀ a ∈ [handle, names, inv, slot, cursor, src, th, L, heap], a < 2 ^ w)
    (hpre : (detectSlotStepContract w fmt.limbBits report written edge threshold).pre
      [names, inv, slot, cursor, src, th, L, heap] st.mem)
    (hrep : R.rep handle s x st.mem) (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hcursor : ¬ R.foot handle x cursor)
    (hreport : ∀ a, report ≤ a → a < report + written.length + 1 → a < heap ∧ ¬ R.foot handle x a)
    (hwrite : ∀ mem', PathEdgeAt mem' heap fmt.limbBits L (some { edge with detector := -threshold }) →
      (pathTreeMachineContract fmt L constant allocation).pre 5 s
        [handle, slot, heap, heap + (2 + 4 * L)] mem')
    (hroom : heap + (2 + 4 * L) + allocation 5 s.n [handle, slot, heap, heap + (2 + 4 * L)] < 2 ^ w) :
    ∃ (ret cost : ℕ) (out : State) (y : R.τ),
      Runs w p ω (detectReadyReport entry) st .normal out cost ∧
      out.regs 1 = ret ∧ out.regs 8 = cursor + 1 ∧
      (∀ r, r ≠ 1 → r ≠ 8 → r ≠ 9 → r ≠ 11 → r ≠ 12 → out.regs r = st.regs r) ∧
      R.rep handle (pathTreeWrite s slot (some { edge with detector := -threshold })) y out.mem ∧
      ListAt out.mem report (written ++ [st.mem (inv + st.mem (names + slot))]) ∧
      ZeroFrom out.mem ret ∧ heap + (2 + 4 * L) ≤ ret ∧
      ret ≤ heap + (2 + 4 * L) + allocation 5 s.n [handle, slot, heap, heap + (2 + 4 * L)] ∧
      (∀ a < heap, ¬ R.foot handle x a → a ≠ cursor → out.mem a = st.mem a) ∧
      (∀ a, R.foot handle y a → R.foot handle x a ∨ (heap ≤ a ∧ a < ret)) ∧
      cost + R.phi handle y out.mem ≤
        pathTreeBudget constant L s.n + R.phi handle x st.mem + 87 * L + 189 := by
  obtain ⟨h₀, h₆, h₇, h₃, h₈, h₄, h₁₀, h₁₃, h₁₄⟩ := hregs
  obtain ⟨mid, hsetup, h₉, h₁₁, hmf, hmem, _⟩ :=
    detectReportArgs_runs (ω := ω) h₁₄ h₃ h₁₃ htable
  have hmregs := fun r h9 h11 => hmf r h9 h11
  have hregs' : mid.regs 0 = handle ∧ mid.regs 6 = names ∧ mid.regs 7 = inv ∧ mid.regs 3 = slot ∧
      mid.regs 8 = cursor ∧ mid.regs 4 = src ∧ mid.regs 9 = th ∧ mid.regs 10 = L ∧ mid.regs 11 = heap :=
    ⟨(hmregs 0 (by decide) (by decide)).trans h₀, (hmregs 6 (by decide) (by decide)).trans h₆,
      (hmregs 7 (by decide) (by decide)).trans h₇, (hmregs 3 (by decide) (by decide)).trans h₃,
      (hmregs 8 (by decide) (by decide)).trans h₈, (hmregs 4 (by decide) (by decide)).trans h₄,
      h₉.trans hth, (hmregs 10 (by decide) (by decide)).trans h₁₀, h₁₁⟩
  obtain ⟨ret, c, after, y, hcall, hheap, hregs₂, hy, hl, hz, hlo, hhi, hf, hft, hc⟩ :=
    detectTreeReport_call (ω := ω) written hentry hregs' himpl hp hw (by rwa [hmem])
      (by rwa [hmem]) hfoot hcursor hreport hwrite hroom
  have hcur := (hregs₂ 8 (by decide)).trans hregs'.2.2.2.2.1
  obtain ⟨out, hadv, hret, hcursor', hregs₃, hout, _⟩ :=
    detectReportAdvance_runs (ω := ω) hheap hcur hadvance
  refine ⟨ret, 8 + (c + 7 + 1) + 1, out, y, ?_, hret, hcursor', ?_, ?_, ?_, ?_, hlo, hhi, ?_, hft, ?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨mid, 8, _, hsetup,
      runs_seq_iff.mpr (Or.inr ⟨after, c, 7, hcall, hadv, rfl⟩), rfl⟩)
  · intro r h1 h8 h9 h11 h12
    exact (hregs₃ r h1 h8).trans ((hregs₂ r h12).trans (hmf r h9 h11))
  · rwa [hout]
  · rwa [hout, ← hmem]
  · rwa [hout]
  · rw [hout, ← hmem]
    exact hf
  · rw [hout, hmem] at *
    omega

/-- A successful machine report preserves the model accounts and consumes one pending edge. -/
theorem detectReadyReport_model_runs {cfg : Alg2Config} (model : Alg2State cfg) {w L constant init handle names inv slot cursor src th heap
    prepare report entry table : ℕ}
    {fmt : Num.Format w} {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op : ℕ → ℕ} {tree s : PathTreeState} {x : R.τ} {edge : PathEdgeValue} {threshold : ℤ}
    {trees : List AuxTree} {free : List ℕ} {depth slotOf : ℕ → ℕ} {P : ℕ}
    (written : List ℕ)
    (hi : LctInvWith pathPayload tree trees free depth)
    (ha : DetectForestAccounts model P slotOf written.toFinset tree trees)
    (hinj : Set.InjOn slotOf (model.extG.E : Set ℕ))
    (hcover : ∀ u, pathTreeReady tree u →
      ∃ e ∈ model.extG.E, slotOf e = u)
    (heps : 0 < cfg.ε) (hl : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hn : written.Nodup) (hs : written.toFinset ⊆ (algorithm2_detect cfg model).1)
    (hr : pathTreeReady tree slot)
    (hs' : s = lctExpose pathPayload (lctExpose pathPayload tree slot) slot)
    (hedge : ((lctExpose pathPayload tree slot).splay.nodes slot).val = some edge)
    (hname : ∀ e ∈ model.extG.E, slotOf e = slot → st.mem (inv + st.mem (names + slot)) = e)
    (hthreshold : threshold = detectorThreshold P cfg.ε
      (model.extℓ (st.mem (inv + st.mem (names + slot)))))
    (hentry : p.procs[entry]? = some (detectTreeReportBody prepare (op 5)))
    (hregs : st.regs 0 = handle ∧ st.regs 6 = names ∧ st.regs 7 = inv ∧ st.regs 3 = slot ∧
      st.regs 8 = cursor ∧ st.regs 4 = src ∧ st.regs 10 = L ∧ st.regs 13 = heap ∧ st.regs 14 = table)
    (hth : st.mem (table + slot) = th) (htable : table + slot < 2 ^ w)
    (hadvance : cursor + 1 < 2 ^ w)
    (himpl : R.Implements w p init op (pathTreeMachineContract fmt L constant allocation))
    (hp : MeetsContract w p prepare (detectSlotStepContract w fmt.limbBits report written edge threshold))
    (hw : ∀ a ∈ [handle, names, inv, slot, cursor, src, th, L, heap], a < 2 ^ w)
    (hpre : (detectSlotStepContract w fmt.limbBits report written edge threshold).pre
      [names, inv, slot, cursor, src, th, L, heap] st.mem)
    (hrep : R.rep handle s x st.mem) (hfoot : ∀ a, R.foot handle x a → a < heap)
    (hcursor : ¬ R.foot handle x cursor)
    (hreport : ∀ a, report ≤ a → a < report + written.length + 1 → a < heap ∧ ¬ R.foot handle x a)
    (hwrite : ∀ mem', PathEdgeAt mem' heap fmt.limbBits L (some { edge with detector := -threshold }) →
      (pathTreeMachineContract fmt L constant allocation).pre 5 s
        [handle, slot, heap, heap + (2 + 4 * L)] mem')
    (hroom : heap + (2 + 4 * L) + allocation 5 s.n [handle, slot, heap, heap + (2 + 4 * L)] < 2 ^ w) :
    let name := st.mem (inv + st.mem (names + slot))
    let updated := pathTreeWrite s slot (some { edge with detector := -threshold })
    ∃ trees', LctInvWith pathPayload updated trees' free depth ∧
      DetectForestAccounts model P slotOf (written ++ [name]).toFinset updated trees' ∧
      (∀ u, pathTreeReady updated u → ∃ e ∈ model.extG.E, slotOf e = u) ∧
      (written ++ [name]).Nodup ∧
      (written ++ [name]).toFinset ⊆ (algorithm2_detect cfg model).1 ∧
      ((algorithm2_detect cfg model).1 \ (written ++ [name]).toFinset).card + 1 =
        ((algorithm2_detect cfg model).1 \ written.toFinset).card ∧
    ∃ (ret cost : ℕ) (out : State) (y : R.τ),
      Runs w p ω (detectReadyReport entry) st .normal out cost ∧
      out.regs 1 = ret ∧ out.regs 8 = cursor + 1 ∧
      (∀ r, r ≠ 1 → r ≠ 8 → r ≠ 9 → r ≠ 11 → r ≠ 12 → out.regs r = st.regs r) ∧
      R.rep handle (pathTreeWrite s slot (some { edge with detector := -threshold })) y out.mem ∧
      ListAt out.mem report (written ++ [st.mem (inv + st.mem (names + slot))]) ∧
      ZeroFrom out.mem ret ∧ heap + (2 + 4 * L) ≤ ret ∧
      ret ≤ heap + (2 + 4 * L) + allocation 5 s.n [handle, slot, heap, heap + (2 + 4 * L)] ∧
      (∀ a < heap, ¬ R.foot handle x a → a ≠ cursor → out.mem a = st.mem a) ∧
      (∀ a, R.foot handle y a → R.foot handle x a ∨ (heap ≤ a ∧ a < ret)) ∧
      cost + R.phi handle y out.mem ≤
        pathTreeBudget constant L s.n + R.phi handle x st.mem + 87 * L + 189 := by
  dsimp only
  obtain ⟨name, hmem, hslot', hn', hm', hc', prior, hprior, trees', hi', ha'⟩ :=
    detectForestAccounts_ready_snoc model hi ha hinj hcover heps hl hn hs hr
  have heq := hname name hmem hslot'
  have hv' := Option.some.inj (hedge.symm.trans hprior)
  subst prior
  subst s
  rw [heq] at hthreshold ⊢
  rw [hthreshold]
  have hneg := neg_lt_zero.mpr (detectorThreshold_pos P cfg.ε (model.extℓ name) heps (hl name hmem))
  have hcover' := detect_ready_coverage_after_report hr hcover
    { edge with detector := -detectorThreshold P cfg.ε (model.extℓ name) } hneg
  exact ⟨trees', hi', ha', hcover', hn', hm', hc',
    by simpa only [heq, hthreshold] using
      (detectReadyReport_runs (ω := ω) written hentry hregs hth htable hadvance himpl hp hw hpre
        hrep hfoot hcursor hreport hwrite hroom)⟩

end MinCostFlow.MinRatio
