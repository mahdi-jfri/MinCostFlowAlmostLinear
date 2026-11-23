module

public import MinCostFlow.MinRatio.DetectLoopProgram

/-!
# One machine round of Detect

The proof of Theorem 5.1 (pages 29–30) repeats a tree search and
reset until no edge reaches its threshold. This file combines the
machine search and both branches and accounts for their costs.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain LinkCut IPM.Machine

/-- A round either completes the exact report or consumes one pending
edge. Its machine cost accounts for the tree potential in each case. -/
theorem DetectLoopState.round_runs {cfg : Alg2Config} {model : Alg2State cfg}
    {w L constant init handle base names inv table searchSpace readSpace prepare entry finish m : ℕ}
    (F : MinRatioFormat w) {G : MGraph} {κ α : ℝ}
    {rate : ℕ → ℕ} {outerSpace : ℕ → List ℕ → ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {R : DSRep PathTreeState}
    {op slotOf internalOf thresholdOf : ℕ → ℕ}
    (I : DetectLoopState model R handle base names inv table F.fmt.limbBits L F.fmt.precision
      slotOf internalOf thresholdOf st)
    (hL : L = F.limbs)
    (himpl : R.Implements w p init op (pathTreeMachineContract F.fmt L constant allocation))
    (h0 : st.regs 0 = handle) (h6 : st.regs 6 = names) (h7 : st.regs 7 = inv)
    (h10 : st.regs 10 = L) (h14 : st.regs 14 = table) (h17 : st.regs 17 = base)
    (h15 : st.regs 15 = searchSpace) (h16 : st.regs 16 = readSpace)
    (hh : handle < 2 ^ w) (hthree : 3 < 2 ^ w)
    (hinj : Set.InjOn slotOf (model.extG.E : Set ℕ))
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hwords : ∀ e ∈ model.extG.E, e < 2 ^ w)
    (hedge : ∀ e ∈ model.extG.E, isEdgeSlot I.tree.n (slotOf e))
    (hfit : MinRatioStateFits (algorithm2_dsWithFailureWith cfg κ) G F.fmt.limbBits F.limbs
      F.fmt.precision model)
    (hentry : p.procs[entry]? = some (detectTreeReportBody prepare (op 5)))
    (hprepare : ∀ value threshold, MeetsContract w p prepare
      (detectSlotStepContract w F.fmt.limbBits (base + 1) I.written value threshold))
    (hfinish : ∀ heap, MeetsContract w p finish (detectFinishKeepHeapContract w heap I.written))
    (hpre : (pathTreeMachineContract F.fmt L constant allocation).pre 6 I.tree
      [handle, st.regs 1] st.mem)
    (hspace : allocation 6 I.tree.n [handle, st.regs 1] ≤ searchSpace)
    (hrecord : 2 + 4 * L ≤ readSpace)
    (hread : ∀ slot mem, pathTreeReady I.tree slot →
      (pathTreeMachineContract F.fmt L constant allocation).pre 4
        (lctExpose pathPayload I.tree slot) [handle, slot, st.regs 1 + searchSpace] mem ∧
      allocation 4 I.tree.n [handle, slot, st.regs 1 + searchSpace] ≤ readSpace)
    (hroom : st.regs 1 + searchSpace + readSpace < 2 ^ w)
    (hwrite : ∀ slot value e mem', pathTreeReady I.tree slot → e ∈ model.extG.E → slotOf e = slot →
      ((lctExpose pathPayload I.tree slot).splay.nodes slot).val = some value →
      let heap := st.regs 1 + searchSpace + readSpace
      PathEdgeAt mem' heap F.fmt.limbBits L
        (some { value with detector := -detectorThreshold F.fmt.precision cfg.ε (model.extℓ e) }) →
      (pathTreeMachineContract F.fmt L constant allocation).pre 5
        (lctExpose pathPayload (lctExpose pathPayload I.tree slot) slot)
        [handle, slot, heap, heap + (2 + 4 * L)] mem')
    (hwriteRoom : ∀ slot, pathTreeReady I.tree slot →
      let heap := st.regs 1 + searchSpace + readSpace
      heap + (2 + 4 * L) + allocation 5 I.tree.n [handle, slot, heap, heap + (2 + 4 * L)] < 2 ^ w) :
    ∃ setup found out searchCost branchCost slot outcome,
      Runs w p ω detectWorkspaceArgs st .normal setup 9 ∧
      Runs w p ω (detectSearchRead (op 6) (op 4)) setup .normal found searchCost ∧
      found.regs 3 = slot ∧
      Runs w p ω (if slot = 0 then detectExhaustedBranch finish else detectReadyReport entry)
        found outcome out branchCost ∧
      match outcome with
      | .normal => ∃ J : DetectLoopState model R handle base names inv table F.fmt.limbBits L
          F.fmt.precision slotOf internalOf thresholdOf out,
          J.tree.n = I.tree.n ∧
          (∀ a < st.regs 1, ¬ R.foot handle I.token a → a ≠ st.regs 8 → out.mem a = st.mem a) ∧
          (∀ a, R.foot handle J.token a → R.foot handle I.token a ∨
            (st.regs 1 ≤ a ∧ a < out.regs 1)) ∧
          (let heap := st.regs 1 + searchSpace + readSpace
           out.regs 1 ≤ heap + (2 + 4 * L) +
             allocation 5 I.tree.n [handle, slot, heap, heap + (2 + 4 * L)]) ∧
          ((algorithm2_detect cfg model).1 \ J.written.toFinset).card + 1 =
            ((algorithm2_detect cfg model).1 \ I.written.toFinset).card ∧
          (∀ r ∈ [0, 6, 7, 10, 14, 15, 16, 17], out.regs r = st.regs r) ∧
          searchCost + branchCost + R.phi handle J.token out.mem ≤
            3 * pathTreeBudget constant L I.tree.n + R.phi handle I.token st.mem + 87 * L + 203
      | .returned heap => ∃ y,
          st.regs 1 ≤ heap ∧ heap ≤ st.regs 1 + searchSpace ∧
          ((algorithm2_detect cfg model).1 \ I.written.toFinset).card = 0 ∧
          (minRatioMachineContract F (algorithm2_dsWithFailureWith cfg κ) G m κ α rate outerSpace).post
            2 model [handle, base] found.mem (algorithm2_detect cfg model).2 out.mem ∧
          DetectForestAccounts (algorithm2_detect cfg model).2 F.fmt.precision
            slotOf ∅ I.tree I.trees ∧
          R.rep handle I.tree y out.mem ∧ ZeroFrom out.mem heap ∧
          (∀ a < st.regs 1, ¬ R.foot handle I.token a → a ≠ base → out.mem a = st.mem a) ∧
          (∀ a, R.foot handle y a → R.foot handle I.token a ∨ (st.regs 1 ≤ a ∧ a < heap)) ∧
          searchCost + branchCost + R.phi handle y out.mem ≤
            2 * pathTreeBudget constant L I.tree.n + R.phi handle I.token st.mem + 41 := by
  subst L
  obtain ⟨setup, found, tree, c, ret, slot, y, hs, hr, hslot, htop, hend, hsave, hy, hz,
    hlo, hframe, hfoot, hresult, hc⟩ :=
    I.search_runs (ω := ω) himpl h0 hh h15 h16 hpre hspace hroom hread
  by_cases hzero : slot = 0
  · obtain ⟨rfl, hret, hheap, hstop⟩ := (ite_eq_left hzero).mp hresult
    obtain ⟨hcount, out, d, hd, hm, ha, hrep, hphi, hzero', hframe', hfoot', hb⟩ :=
      I.finish_after_search (ω := ω) (m := m) (κ := κ) (α := α) (rate := rate) (allocation := outerSpace)
        F himpl.1 hfit (hfinish ret) ((hsave 17 (by decide) (by decide) (by decide)
          (by decide) (by decide)).trans h17) (hsave 8 (by decide) (by decide)
          (by decide) (by decide) (by decide)) hheap hlo (by omega) hz hframe hfoot hy hedge heps hlen hstop
    exact ⟨setup, found, out, c, d, slot, .returned ret, hs, hr, hslot,
      (by simpa only [hzero, ite_true] using hd), y, hlo, hret, hcount, hm, ha, hrep, hzero', hframe', hfoot', by omega⟩
  · obtain ⟨hready, rfl, _, _, hret, hval⟩ := (ite_eq_right hzero).mp hresult
    have saved (r : ℕ) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) (h5 : r ≠ 5)
        (h13 : r ≠ 13) := hsave r h2 h3 h4 h5 h13
    obtain ⟨out, d, hd, hout, J, hnJ, hframe', hfoot', hupper, hdec, hcost⟩ :=
      I.ready_after_search (ω := ω) hinj heps hlen hready rfl hval hentry
        ⟨(saved 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h0,
         (saved 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h6,
         (saved 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h7,
         hslot, saved 8 (by decide) (by decide) (by decide) (by decide) (by decide), htop,
         (saved 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h10, hend,
         (saved 14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14⟩
        himpl hprepare hh hthree hwords hy (hlo.trans hret) (Nat.add_le_add_left hrecord _)
        (fun a ha => hz a (hret.trans ha)) hframe
        (fun a ha => (hfoot a ha).imp_right fun h => ⟨h.1, h.2.trans_le hret⟩)
        (fun value e mem => hwrite slot value e mem hready) (hwriteRoom slot hready) hc
    refine ⟨setup, found, out, c, d, slot, .normal, hs, hr, hslot,
      (by simpa only [hzero, ite_false] using hd), J, hnJ, hframe', hfoot', hupper, hdec, ?_, hcost⟩
    intro r h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hout _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (hsave _ (by decide) (by decide) (by decide) (by decide) (by decide))

/-- The linked reporting loop returns the model report and charges
one ready round per pending edge, plus one exhausted round. The
per-state premises provide the linked calls' numeric and space bounds. -/
theorem DetectLoopState.loop_runs {cfg : Alg2Config} {model : Alg2State cfg}
    {w constant init handle base names inv table searchSpace readSpace writeSpace prepare entry finish m : ℕ}
    (F : MinRatioFormat w) {G : MGraph} {κ α : ℝ}
    {rate : ℕ → ℕ} {outerSpace : ℕ → List ℕ → ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} {R : DSRep PathTreeState}
    {allocation : ℕ → ℕ → List ℕ → ℕ}
    {op slotOf internalOf thresholdOf : ℕ → ℕ}
    (I : DetectLoopState model R handle base names inv table F.fmt.limbBits F.limbs
      F.fmt.precision slotOf internalOf thresholdOf st)
    (hw : 1 < 2 ^ w)
    (himpl : R.Implements w p init op (pathTreeMachineContract F.fmt F.limbs constant allocation))
    (h0 : st.regs 0 = handle) (h6 : st.regs 6 = names) (h7 : st.regs 7 = inv)
    (h10 : st.regs 10 = F.limbs) (h14 : st.regs 14 = table) (h17 : st.regs 17 = base)
    (h15 : st.regs 15 = searchSpace) (h16 : st.regs 16 = readSpace)
    (hh : handle < 2 ^ w) (hthree : 3 < 2 ^ w)
    (hinj : Set.InjOn slotOf (model.extG.E : Set ℕ))
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hwords : ∀ e ∈ model.extG.E, e < 2 ^ w)
    (hfit : MinRatioStateFits (algorithm2_dsWithFailureWith cfg κ) G F.fmt.limbBits F.limbs
      F.fmt.precision model)
    (hentry : p.procs[entry]? = some (detectTreeReportBody prepare (op 5)))
    (hprepare : ∀ written value threshold, MeetsContract w p prepare
      (detectSlotStepContract w F.fmt.limbBits (base + 1) written value threshold))
    (hfinish : ∀ written heap, MeetsContract w p finish (detectFinishKeepHeapContract w heap written))
    (hedge : ∀ e ∈ model.extG.E, isEdgeSlot I.tree.n (slotOf e))
    (htreeWord : 2 * I.tree.n + 1 < 2 ^ w)
    (htreeWidth : Nat.log 2 (2 * I.tree.n + 1) ≤ F.fmt.limbBits * F.limbs)
    (hcapacity : st.regs 1 + ((algorithm2_detect cfg model).1 \ I.written.toFinset).card *
      (searchSpace + readSpace + (2 + 4 * F.limbs) + writeSpace) + searchSpace + readSpace < 2 ^ w)
    (hbounds : ∀ current (J : DetectLoopState model R handle base names inv table
      F.fmt.limbBits F.limbs F.fmt.precision slotOf internalOf thresholdOf current),
      J.tree.n = I.tree.n →
      (pathTreeFits F.fmt.limbBits F.limbs J.tree) ∧
      (allocation 6 J.tree.n [handle, current.regs 1] ≤ searchSpace) ∧
      (2 + 4 * F.limbs ≤ readSpace) ∧
      (∀ slot, pathTreeReady J.tree slot →
      pathTreeFits F.fmt.limbBits F.limbs (lctExpose pathPayload J.tree slot) ∧
      pathTreeFits F.fmt.limbBits F.limbs (lctExpose pathPayload (lctExpose pathPayload J.tree slot) slot) ∧
      allocation 4 J.tree.n [handle, slot, current.regs 1 + searchSpace] ≤ readSpace) ∧
      (∀ slot value e, e ∈ model.extG.E → slotOf e = slot →
      ((lctExpose pathPayload J.tree slot).splay.nodes slot).val = some value →
      pathTreeFits F.fmt.limbBits F.limbs
        (pathTreeWrite (lctExpose pathPayload (lctExpose pathPayload J.tree slot) slot)
          slot (some { value with detector := -detectorThreshold F.fmt.precision cfg.ε (model.extℓ e) }))) ∧
      (∀ slot,
      let heap := current.regs 1 + searchSpace + readSpace
      allocation 5 J.tree.n [handle, slot, heap, heap + (2 + 4 * F.limbs)] ≤ writeSpace)) :
    let budget := pathTreeBudget constant F.limbs I.tree.n
    ∃ heap out cost tree trees y,
      Runs w p ω (detectLoopProgram (op 6) (op 4) entry finish) st (.returned heap) out cost ∧
      (minRatioMachineContract F (algorithm2_dsWithFailureWith cfg κ) G m κ α rate outerSpace).post
        2 model [handle, base] st.mem (algorithm2_detect cfg model).2 out.mem ∧
      DetectForestAccounts (algorithm2_detect cfg model).2 F.fmt.precision slotOf ∅ tree trees ∧
      R.rep handle tree y out.mem ∧ ZeroFrom out.mem heap ∧
      (∀ a < base, ¬ R.foot handle I.token a → out.mem a = st.mem a) ∧
      (∀ a, R.foot handle y a → a < base → R.foot handle I.token a) ∧
      base ≤ heap ∧ (∀ a, R.foot handle y a → a < heap) ∧
      heap ≤ st.regs 1 + ((algorithm2_detect cfg model).1 \ I.written.toFinset).card *
        (searchSpace + readSpace + (2 + 4 * F.limbs) + writeSpace) + searchSpace ∧
      cost + R.phi handle y out.mem ≤
        ((algorithm2_detect cfg model).1 \ I.written.toFinset).card *
          (3 * budget + 87 * F.limbs + 218) + 2 * budget + 56 + R.phi handle I.token st.mem := by
  dsimp only
  let budget := pathTreeBudget constant F.limbs I.tree.n
  let space := searchSpace + readSpace + (2 + 4 * F.limbs) + writeSpace
  let ceiling := st.regs 1 + ((algorithm2_detect cfg model).1 \ I.written.toFinset).card * space
  let Inv := fun remaining potential (current : State) =>
    ∃ J : DetectLoopState model R handle base names inv table F.fmt.limbBits F.limbs
      F.fmt.precision slotOf internalOf thresholdOf current,
      J.tree.n = I.tree.n ∧
      (∀ r ∈ [0, 6, 7, 10, 14, 15, 16, 17], current.regs r = st.regs r) ∧
      remaining = ((algorithm2_detect cfg model).1 \ J.written.toFinset).card ∧
      potential = R.phi handle J.token current.mem ∧
      current.regs 1 + remaining * space ≤ ceiling ∧
      (∀ a < base, ¬ R.foot handle I.token a → current.mem a = st.mem a) ∧
      (∀ a, R.foot handle J.token a → a < base → R.foot handle I.token a)
  let Done := fun heap potential (out : State) =>
    ∃ tree trees y,
      (minRatioMachineContract F (algorithm2_dsWithFailureWith cfg κ) G m κ α rate outerSpace).post
        2 model [handle, base] st.mem (algorithm2_detect cfg model).2 out.mem ∧
      DetectForestAccounts (algorithm2_detect cfg model).2 F.fmt.precision slotOf ∅ tree trees ∧
      R.rep handle tree y out.mem ∧ ZeroFrom out.mem heap ∧
      (∀ a < base, ¬ R.foot handle I.token a → out.mem a = st.mem a) ∧
      (∀ a, R.foot handle y a → a < base → R.foot handle I.token a) ∧
      base ≤ heap ∧ (∀ a, R.foot handle y a → a < heap) ∧
      heap ≤ ceiling + searchSpace ∧ potential = R.phi handle y out.mem
  obtain ⟨heap, out, c, phi, hrun, ⟨tree, trees, y, hm, ha, hrep, hz, hframe, hfoot, hlow, htreeEnd, hheap, hphi⟩, hcost⟩ :=
    detectLoopProgram_runs (p := p) (ω := ω) (Inv := Inv) (Done := Done)
      hw (3 * budget + 87 * F.limbs + 203) (2 * budget + 41) (fun remaining potential current hi => by
        obtain ⟨J, hn, hregs, rfl, rfl, hcapacityCurrent, hframe, hfoot⟩ := hi
        have hbase : base ≤ current.regs 1 := by have := J.reserve; omega
        have hwordCapacity : ceiling + searchSpace + readSpace < 2 ^ w := hcapacity
        have hcurrentWord : current.regs 1 +
            ((algorithm2_detect cfg model).1 \ J.written.toFinset).card * space +
            searchSpace + readSpace < 2 ^ w := by omega
        obtain ⟨hfitTree, hspace, hrecord, hread, hwrite, hwriteSpace⟩ := hbounds current J hn
        have hword : 2 * J.tree.n + 1 < 2 ^ w := hn.symm ▸ htreeWord
        have hwidth : Nat.log 2 (2 * J.tree.n + 1) ≤ F.fmt.limbBits * F.limbs := hn.symm ▸ htreeWidth
        have hpre : (pathTreeMachineContract F.fmt F.limbs constant allocation).pre 6 J.tree
            [handle, current.regs 1] current.mem :=
          ⟨⟨J.trees, J.free, J.depth, J.forestInv⟩, hfitTree, hword, hwidth, handle, current.regs 1,
            rfl, fun slot hs => (hread slot hs).1⟩
        obtain ⟨setup, found, out, c, d, slot, outcome, hs, hf, hr, hb, hp⟩ :=
          J.round_runs (ω := ω) (m := m) (κ := κ) (α := α) (rate := rate)
            (outerSpace := outerSpace) F rfl himpl
            ((hregs 0 (by decide)).trans h0) ((hregs 6 (by decide)).trans h6)
            ((hregs 7 (by decide)).trans h7) ((hregs 10 (by decide)).trans h10)
            ((hregs 14 (by decide)).trans h14) ((hregs 17 (by decide)).trans h17)
            ((hregs 15 (by decide)).trans h15) ((hregs 16 (by decide)).trans h16)
            hh hthree hinj heps hlen hwords (by rwa [hn]) hfit hentry
            (hprepare J.written) (hfinish J.written) hpre hspace hrecord
            (fun slot mem hs => by
              obtain ⟨hfirst, hsecond, ha⟩ := hread slot hs
              obtain ⟨trees, free, depth, hi, hactive⟩ :=
                (pathTree_expose_twice_value J.tree slot hs.2.1).1
              exact ⟨⟨⟨trees, free, depth, hi⟩, hfirst, hword, hwidth, handle, slot,
                current.regs 1 + searchSpace, rfl, ⟨trees, free, depth, hi, hactive⟩, hsecond⟩, ha⟩)
            (by omega) (fun slot value e mem hs he hslot hv hrecord' => by
              obtain ⟨trees, free, depth, hi, ha⟩ :=
                (pathTree_expose_twice_value J.tree slot hs.2.1).2.1
              exact detectTreeReset_pre ⟨trees, free, depth, hi⟩ (hread slot hs).2.1
                hword hwidth hs.1 ⟨trees, free, depth, hi, ha⟩ (Nat.le_refl _)
                hrecord' (hwrite slot value e he hslot hv)) (fun slot hs => by
              have hpos : 0 < ((algorithm2_detect cfg model).1 \ J.written.toFinset).card := by
                obtain ⟨e, he, eq⟩ := J.coverage slot hs
                obtain ⟨_, _, _, hp⟩ := detectForestAccounts_point model J.forestInv J.accounts he
                  (eq.symm ▸ hs.1) heps (hlen e he)
                exact Finset.card_pos.mpr ⟨e, hp.mp (eq.symm ▸ hs)⟩
              have hb := Nat.le_mul_of_pos_left space hpos
              have ha := hwriteSpace slot
              dsimp [space] at hb hcurrentWord
              omega)
        refine ⟨setup, found, out, c, d, slot, outcome, hs, hf, hr, hb, ?_⟩
        cases outcome with
        | normal =>
          obtain ⟨K, hn', hf, hft, hupper, hc, hreg, hcost⟩ := hp
          refine ⟨_, by omega, ⟨K, hn'.trans hn, fun r h => (hreg r h).trans (hregs r h),
            by omega, rfl, ?_, ?_, ?_⟩, ?_⟩
          · have ha := hwriteSpace slot
            dsimp only at hupper ha
            have hm : ((algorithm2_detect cfg model).1 \ J.written.toFinset).card =
                ((algorithm2_detect cfg model).1 \ J.written.toFinset).card - 1 + 1 := by omega
            rw [hm, Nat.add_mul, Nat.one_mul] at hcapacityCurrent
            dsimp [space] at *
            omega
          · intro a ha ho
            have hnc : a ≠ current.regs 8 := by rw [J.cursor]; omega
            exact (hf a (ha.trans_le hbase) (fun ht => ho (hfoot a ht ha)) hnc).trans
              (hframe a ha ho)
          · intro a ht ha
            rcases hft a ht with hold | ⟨hnew, _⟩
            · exact hfoot a hold ha
            · exact (Nat.not_le_of_lt (ha.trans_le hbase) hnew).elim
          rw [hn] at hcost
          dsimp [budget]
          omega
        | returned heap =>
          obtain ⟨y, hheapLo, hheapRound, hzero, hmodel, hacc, hrep, hz, hf, hft, hc⟩ := hp
          have hmodel' : (minRatioMachineContract F (algorithm2_dsWithFailureWith cfg κ) G
              m κ α rate outerSpace).post 2 model [handle, base] st.mem
              (algorithm2_detect cfg model).2 out.mem := hmodel
          refine ⟨_, hzero, ⟨J.tree, J.trees, y, hmodel', hacc, hrep, hz, ?_, ?_, hbase.trans hheapLo, ?_, by omega, rfl⟩, ?_⟩
          · intro a ha ho
            exact (hf a (ha.trans_le hbase) (fun ht => ho (hfoot a ht ha)) (ne_of_lt ha)).trans
              (hframe a ha ho)
          · intro a ht ha
            rcases hft a ht with hold | ⟨hnew, _⟩
            · exact hfoot a hold ha
            · exact (Nat.not_le_of_lt (ha.trans_le hbase) hnew).elim
          · intro a ht
            rcases hft a ht with hold | ⟨_, hnew⟩
            · exact (J.treeBound a hold).trans_le hheapLo
            · exact hnew
          · rw [hn] at hc
            dsimp [budget]
            omega) (st := st) (remaining := ((algorithm2_detect cfg model).1 \ I.written.toFinset).card)
      (potential := R.phi handle I.token st.mem) ⟨I, rfl, fun _ _ => rfl, rfl, rfl, Nat.le_refl _, fun _ _ _ => rfl, fun _ h _ => h⟩
  refine ⟨heap, out, c, tree, trees, y, hrun, hm, ha, hrep, hz, hframe, hfoot, hlow, htreeEnd, hheap, ?_⟩
  rw [hphi] at hcost
  simpa only [budget, Nat.add_assoc, Nat.reduceAdd] using hcost

end MinCostFlow.MinRatio
