module

public import MinCostFlow.HierPaths.BuildTopDepthInv

/-!
# Running the parent scan

The parent step preserves the previous replies, records the new reply,
and advances the heap by at most the work bound of that call.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited

private theorem rangeCost_zero_succ (f : ℕ → ℕ) (i : ℕ) :
    rangeCost f 0 (i + 1) = rangeCost f 0 i + f i := by
  simp [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append]

/-- Each parent is called once. The reply directory and the heap bound hold
for the entire depth. The caller supplies the level input bounds at each
parent and the word space for its call. -/
theorem buildTopDepthInput_runs {w K call h : ℕ} {p : Program}
    {D : BuildTopDepthInput} {mem : ℕ → ℕ} {pos : ℕ}
    {space : Graph → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (ω : ℕ → Bool)
    (hc : ∀ i < D.count, MeetsContract w p call (D.level w K space i))
    (hsk : D.childSize * D.branch < 2 ^ w) (hn : D.count < 2 ^ w)
    (hh : h < 2 ^ w) (h1 : 1 < 2 ^ w)
    (hz : ZeroFrom mem h)
    (hd : D.replyDir + D.count ≤ h)
    (hg : D.graphDir + D.count ≤ h)
    (hdisj : D.graphDir + D.count ≤ D.replyDir ∨ D.replyDir + D.count ≤ D.graphDir)
    (hread : ∀ i < D.count, mem (D.graphDir + i) = D.graphAddr i)
    (hready : ∀ i < D.count, ∀ st, D.state space h mem i st →
      (∀ v ∈ D.callArgs i (st.regs 12), v < 2 ^ w) ∧
      (D.level w K space i).pre (D.callArgs i (st.regs 12))
        (Function.update st.mem (D.replyDir + i) (st.regs 12))) :
    ∃ v t c, Runs w p ω (buildTopDepth call) (startState (D.args h) mem pos) (.returned v) t c ∧
      h ≤ v ∧ v ≤ h + rangeCost (D.spaceStep space) 0 D.count ∧
      ZeroFrom t.mem v ∧ D.frame h mem t.mem ∧ (∀ i < D.count, D.replyAt i h v t.mem) ∧
      c ≤ rangeCost (fun i => D.work K i + 60) 0 D.count + 9 * D.count + 20 := by
  let st := startState (D.args h) mem pos
  have hstart : D.state space h mem 0
      {st with regs := Function.update (Function.update st.regs 15 (D.childSize * D.branch)) 13 0} := by
    refine ⟨?_, by simp, by simp, ?_, ?_, ?_, ?_, fun i hi => (Nat.not_lt_zero _ hi).elim⟩
    · intro j hj
      change Function.update (Function.update st.regs 15 (D.childSize * D.branch)) 13 0 j = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rfl
    · simp [st, startState, BuildTopDepthInput.args]
    · simp [st, startState, BuildTopDepthInput.args, rangeCost_zero_eq_range]
    · simpa [st, startState, BuildTopDepthInput.args] using hz
    · intro a _ _
      rfl
  have hSteps : ∀ i < D.count, Triple w p (D.state space h mem i) (buildTopDepthBody call)
      (normalPost fun t => D.state space h mem (i + 1)
        {t with regs := Function.update t.regs 13 (i + 1)} ∧ t.regs 13 = i)
      (fun _ => D.work K i + 60) := by
    intro i hi u ω' hu
    obtain ⟨hw,hpre⟩ := hready i hi u hu
    obtain ⟨hreg,hidx,hsize,hlo,hhi,hzero,hframe,hrows⟩ := hu
    let a := u.regs 12
    have hread' : u.mem (D.graphDir+i) = D.graphAddr i :=
      (hframe _ (by omega) (by rcases hdisj with hd | hd <;> [left; right] <;> omega)).trans (hread i hi)
    have hstep := buildTopDepthBody_triple (st := u) (i := i) (gdir := D.graphDir) (out := D.replyDir)
      (base := D.termBase) (h := a) (ga := D.graphAddr i)
      (hc := hc i hi) (h0 := hreg 0 (by decide)) (h1 := hreg 1 (by decide))
      (h2 := hreg 2 (by decide)) (h3 := hreg 3 (by decide)) (h4 := hreg 4 (by decide))
      (h6 := hreg 6 (by decide)) (h7 := hreg 7 (by decide)) (h8 := hreg 8 (by decide))
      (h9 := hreg 9 (by decide)) (h10 := hreg 10 (by decide)) (h11 := hreg 11 (by decide))
      (h12 := rfl) hidx hsize hread' (by omega) (by omega) (by omega) (by omega) hw hpre
    obtain ⟨o,v,c,hr,hpost,hcost⟩ := hstep u ω' rfl
    refine ⟨o,v,c,hr,?_,hcost⟩
    cases o with
    | returned n => exact hpost.elim
    | normal =>
      obtain ⟨hreg',hdir,hp⟩ := hpost
      obtain ⟨⟨hlo', hhi', hf, hz', _⟩, ga', base', top', R, ha, hAt, hBound, hGood⟩ := hp
      have ht : top' = a := by
        have hh := congrArg (fun l : List ℕ => l.getD 11 0) ha
        simpa [buildLevelArgs, a] using hh.symm
      subst top'
      change a ≤ v.regs 12 at hlo'
      have hSp : v.regs 12 ≤ a + D.spaceStep space i := by
        simpa [heapArg, buildLevelArgs, BuildTopDepthInput.spaceStep, a] using hhi'
      have hf' (x : ℕ) (hx : x < a) :
          v.mem x = Function.update u.mem (D.replyDir + i) a x := hf x hx
      refine ⟨⟨?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro j hj
        change Function.update v.regs 13 (i + 1) j = _
        rw [Function.update_of_ne (by omega), hreg' j (by omega) (by omega), hreg j hj]
      · simpa using (hreg' 15 (by decide) (by decide)).trans hsize
      · change h ≤ v.regs 12
        exact hlo.trans hlo'
      · change v.regs 12 ≤ _
        rw [rangeCost_zero_succ]
        omega
      · exact hz'
      · intro x hx hskip
        exact (hf' x (hx.trans_le hlo)).trans
          ((Function.update_of_ne (by rcases hskip with hh | hh <;> omega) _ _).trans (hframe x hx hskip))
      · intro j hj
        by_cases he : j = i
        · subst j
          exact ⟨a, R, hdir, hlo, hBound, hAt, hGood⟩
        · obtain ⟨src, Q, ha, hs, hb, hAt', hG⟩ := hrows j (by omega)
          refine ⟨src, Q, ?_, hs, hb.trans hlo', ?_, hG⟩
          · exact (hf' _ (by omega)).trans ((Function.update_of_ne (by omega) _ _).trans ha)
          · intro l hl
            exact (hf' _ (by omega)).trans ((Function.update_of_ne (by omega) _ _).trans (hAt' l hl))
      · exact (hreg' 13 (by decide) (by decide)).trans hidx
  obtain ⟨v,t,c,hr,hfin,hv,hcost⟩ := buildTopDepth_runs
    (I := D.state space h mem) (cost := fun i => D.work K i + 60) ω
    (st := st) (s := D.childSize) (k := D.branch) (count := D.count)
    rfl rfl hsk hn h1 hstart (fun _ _ _ hi => hi.2.1)
    (fun _ _ _ hi => hi.1 5 (by decide)) hSteps
  obtain ⟨_, _, _, hLo, hHi, hZero, hFr, hReplies⟩ := hfin
  exact ⟨v, t, c, hr, hv.symm ▸ hLo, hv.symm ▸ hHi, hv.symm ▸ hZero, hFr,
    hv.symm ▸ hReplies, hcost⟩

end MinCostFlow.HierPaths

end
