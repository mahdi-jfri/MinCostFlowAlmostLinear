module

public import MinCostFlow.MinRatio.GraphRead
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# Helper loops for the live-list dynamic-graph copy (`GraphLiveCopyLoops`)

Defines `copyGraphLiveFromHeader` and its five straight-line / loop components
(`copyGraphLiveHeader`, `copyGraphLiveVBody`, `copyGraphLiveMid`, `copyGraphLiveEBody`,
`copyGraphLiveEnd`), and proves the execution lemmas for the vertex and edge loops.
Used by `MinCostFlow.MinRatio.GraphLiveCopy` to assemble `copyGraphLiveFromHeader_runs`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program

/-- Cost bound of `copyGraphLiveFromHeader` on a graph with `n` vertices and `m` edges. -/
def copyGraphLiveCost (n m : ℕ) : ℕ :=
  120 * n + 170 * m + 120

/-- Header initialization for `copyGraphLiveFromHeader`. -/
def copyGraphLiveHeader : Stmt :=
  .assign 10 (.load (.reg 6)) ;;
  .assign 11 (.load (.bin .add (.reg 6) (.const 1))) ;;
  .assign 8 (.load (.bin .add (.reg 6) (.const 2))) ;;
  .assign 9 (.load (.bin .add (.reg 6) (.const 3))) ;;
  .store (.reg 5) (.reg 10) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.reg 11) ;;
  .store (.bin .add (.reg 5) (.const 2)) (.reg 8) ;;
  .store (.bin .add (.reg 5) (.const 3)) (.reg 9) ;;
  .assign 63 (.bin .add (.reg 6) (.const 4)) ;;
  .assign 64 (.bin .add (.reg 5) (.const 4)) ;;
  .assign 12 (.const 0)

/-- Vertex-loop body copying one live vertex entry and its slot/incidence metadata. -/
def copyGraphLiveVBody : Stmt :=
  .assign 9 (.load (.bin .add (.bin .add (.reg 63) (.reg 10)) (.reg 12))) ;;
  .store (.bin .add (.bin .add (.reg 64) (.reg 10)) (.reg 12)) (.reg 9) ;;
  .store (.bin .add (.reg 64) (.reg 9)) (.const 1) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 2) (.reg 10))) (.reg 9)) (.reg 12) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 3) (.reg 10))) (.reg 9))
    (.load (.bin .add (.bin .add (.reg 63) (.bin .mul (.const 3) (.reg 10))) (.reg 9))) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 4) (.reg 10))) (.reg 9))
    (.load (.bin .add (.bin .add (.reg 63) (.bin .mul (.const 4) (.reg 10))) (.reg 9))) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 5) (.reg 10))) (.reg 9))
    (.load (.bin .add (.bin .add (.reg 63) (.bin .mul (.const 5) (.reg 10))) (.reg 9))) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 6) (.reg 10))) (.reg 9))
    (.load (.bin .add (.bin .add (.reg 63) (.bin .mul (.const 6) (.reg 10))) (.reg 9)))

/-- Transition between vertex loop and edge loop. -/
def copyGraphLiveMid : Stmt :=
  .assign 63 (.bin .add (.reg 63) (.bin .mul (.const 7) (.reg 10))) ;;
  .assign 64 (.bin .add (.reg 64) (.bin .mul (.const 7) (.reg 10))) ;;
  .assign 10 (.reg 11) ;;
  .assign 8 (.load (.bin .add (.reg 6) (.const 3))) ;;
  .assign 12 (.const 0)

/-- Edge-loop body copying one live edge entry and both of its half-edge links. -/
def copyGraphLiveEBody : Stmt :=
  .assign 9 (.load (.bin .add (.bin .add (.reg 63) (.reg 10)) (.reg 12))) ;;
  .store (.bin .add (.bin .add (.reg 64) (.reg 10)) (.reg 12)) (.reg 9) ;;
  .store (.bin .add (.reg 64) (.reg 9)) (.const 1) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 2) (.reg 10))) (.reg 9)) (.reg 12) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 3) (.reg 10))) (.reg 9))
    (.load (.bin .add (.bin .add (.reg 63) (.bin .mul (.const 3) (.reg 10))) (.reg 9))) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 4) (.reg 10))) (.reg 9))
    (.load (.bin .add (.bin .add (.reg 63) (.bin .mul (.const 4) (.reg 10))) (.reg 9))) ;;
  .assign 9 (.bin .mul (.const 2) (.reg 9)) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 5) (.reg 10))) (.reg 9))
    (.load (.bin .add (.bin .add (.reg 63) (.bin .mul (.const 5) (.reg 10))) (.reg 9))) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 7) (.reg 10))) (.reg 9))
    (.load (.bin .add (.bin .add (.reg 63) (.bin .mul (.const 7) (.reg 10))) (.reg 9))) ;;
  .assign 9 (.bin .add (.reg 9) (.const 1)) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 5) (.reg 10))) (.reg 9))
    (.load (.bin .add (.bin .add (.reg 63) (.bin .mul (.const 5) (.reg 10))) (.reg 9))) ;;
  .store (.bin .add (.bin .add (.reg 64) (.bin .mul (.const 7) (.reg 10))) (.reg 9))
    (.load (.bin .add (.bin .add (.reg 63) (.bin .mul (.const 7) (.reg 10))) (.reg 9)))

/-- Final pointer handoff (`reg 6 := heap`, `reg 5 := heap + dynGraphSize vc ec`). -/
def copyGraphLiveEnd : Stmt :=
  .assign 6 (.reg 5) ;;
  .assign 5 (.bin .add (.reg 64) (.bin .mul (.const 9) (.reg 10)))

/-- Copy the dynamic graph at `reg 6` into fresh zero memory at `reg 5` by walking only the live
vertex and edge lists. Returns `reg 6 = heap`, `reg 5 = heap + dynGraphSize vc ec`, using scratch
registers `{8, 9, 10, 11, 12, 63, 64}`. -/
def copyGraphLiveFromHeader : Stmt :=
  copyGraphLiveHeader ;;
  forUp 12 (.reg 8) copyGraphLiveVBody ;;
  copyGraphLiveMid ;;
  forUp 12 (.reg 8) copyGraphLiveEBody ;;
  copyGraphLiveEnd

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program

theorem copyGraphLiveFromHeader_noRand : copyGraphLiveFromHeader.NoRand := by
  simp [copyGraphLiveFromHeader, copyGraphLiveHeader, copyGraphLiveVBody, copyGraphLiveMid,
    copyGraphLiveEBody, copyGraphLiveEnd, forUp, Stmt.NoRand]

theorem graph_n_le_vCap {mem : ℕ → ℕ} {a vc ec : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vc ec G) : G.n ≤ vc := by
  have hsub : G.V ⊆ Finset.range vc := fun v hv => Finset.mem_range.mpr (hG.2.1 v hv)
  simpa [MGraph.n] using Finset.card_le_card hsub

theorem graph_m_le_eCap {mem : ℕ → ℕ} {a vc ec : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vc ec G) : G.m ≤ ec := by
  have hsub : G.E ⊆ Finset.range ec := fun e he => Finset.mem_range.mpr (hG.2.2.1 e he)
  simpa [MGraph.m] using Finset.card_le_card hsub

private theorem seq_store_step {w k T : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr} {s : Stmt}
    {st : State} {Q : Outcome → State → Prop} {addr val : ℕ}
    (ha : a.eval w st = some addr) (hv : e.eval w st = some val)
    (hrest : ∀ st', st' = { st with mem := Function.update st.mem addr val } →
      ∃ o st'' c, Runs w p ω s st' o st'' c ∧ Q o st'' ∧
        k + (a.size + e.size + 1) + 1 + c ≤ T) :
    ∃ o st'' c, Runs w p ω (.store a e ;; s) st o st'' c ∧ Q o st'' ∧ k + c ≤ T := by
  obtain ⟨o, st'', c, hr, hq, hc⟩ := hrest _ rfl
  exact ⟨o, st'', a.size + e.size + 1 + c + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, a.size + e.size + 1, c,
      runs_store_iff.mpr ⟨addr, val, ha, hv, rfl, rfl, rfl⟩, hr, rfl⟩),
    hq, by omega⟩

private theorem seq_assign_step {w k T r : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s : Stmt}
    {st : State} {Q : Outcome → State → Prop} {val : ℕ}
    (hv : e.eval w st = some val)
    (hrest : ∀ st', st' = { st with regs := Function.update st.regs r val } →
      ∃ o st'' c, Runs w p ω s st' o st'' c ∧ Q o st'' ∧ k + (e.size + 1) + 1 + c ≤ T) :
    ∃ o st'' c, Runs w p ω (.assign r e ;; s) st o st'' c ∧ Q o st'' ∧ k + c ≤ T := by
  obtain ⟨o, st'', c, hr, hq, hc⟩ := hrest _ rfl
  exact ⟨o, st'', e.size + 1 + c + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, c,
      runs_assign_iff.mpr ⟨val, hv, rfl, rfl, rfl⟩, hr, rfl⟩),
    hq, by omega⟩

private theorem copy_array_eval {w baseReg capReg idxReg base cap idx mult : ℕ} {st : State}
    (hb : st.regs baseReg = base) (hc : st.regs capReg = cap) (hi : st.regs idxReg = idx)
    (hm : mult < 2 ^ w) (h1 : mult * cap < 2 ^ w) (h2 : base + mult * cap < 2 ^ w)
    (h3 : base + mult * cap + idx < 2 ^ w) :
    (Expr.bin .add (.bin .add (.reg baseReg) (.bin .mul (.const mult) (.reg capReg)))
      (.reg idxReg)).eval w st = some (base + mult * cap + idx) := by
  simp [Expr.eval, BinOp.eval, hb, hc, hi, hm, h1, h2, h3]

private theorem copy_array_load {w baseReg capReg idxReg base cap idx mult val : ℕ} {st : State}
    (hb : st.regs baseReg = base) (hc : st.regs capReg = cap) (hi : st.regs idxReg = idx)
    (hm : mult < 2 ^ w) (h1 : mult * cap < 2 ^ w) (h2 : base + mult * cap < 2 ^ w)
    (h3 : base + mult * cap + idx < 2 ^ w)
    (hmem : st.mem (base + mult * cap + idx) = val) :
    (Expr.load (.bin .add (.bin .add (.reg baseReg) (.bin .mul (.const mult) (.reg capReg)))
      (.reg idxReg))).eval w st = some val :=
  Expr.eval_load_of_eq (copy_array_eval hb hc hi hm h1 h2 h3) hmem

/-- Loop invariant for the vertex copy loop. -/
@[expose] def vLoopInv (src heap vc ec : ℕ) (G : MGraph) (vL : List ℕ)
    (st0 : State) (mem1 : ℕ → ℕ) (i : ℕ) (s : State) : Prop :=
  s.regs 5 = heap ∧ s.regs 6 = src ∧ s.regs 10 = vc ∧ s.regs 11 = ec ∧ s.regs 8 = G.n ∧
  s.regs 63 = src + 4 ∧ s.regs 64 = heap + 4 ∧ s.regs 12 = i ∧ s.pos = st0.pos ∧
  (∀ r, r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 63 → r ≠ 64 → s.regs r = st0.regs r) ∧
  (∀ a, a < heap + 4 ∨ heap + 4 + 7 * vc ≤ a → s.mem a = mem1 a) ∧
  (∀ j (_ : j < i) (hjl : j < vL.length), s.mem (dgVListBase heap vc + j) = vL[j]'hjl) ∧
  (∀ v < vc, s.mem (dgVPresBase heap + v) = if ∃ j < i, ∃ hjl : j < vL.length, vL[j]'hjl = v then 1 else 0) ∧
  (∀ j (_ : j < i) (hjl : j < vL.length), s.mem (dgVPosBase heap vc + vL[j]'hjl) = j) ∧
  (∀ j (_ : j < i) (hjl : j < vL.length),
    s.mem (dgExtToIntBase heap vc + vL[j]'hjl) = st0.mem (dgExtToIntBase src vc + vL[j]'hjl)) ∧
  (∀ j (_ : j < i) (hjl : j < vL.length),
    s.mem (dgIntToExtBase heap vc + vL[j]'hjl) = st0.mem (dgIntToExtBase src vc + vL[j]'hjl)) ∧
  (∀ v < vc, s.mem (dgSlotDegBase heap vc + v) =
    if ∃ j < i, ∃ hjl : j < vL.length, vL[j]'hjl = v then st0.mem (dgSlotDegBase src vc + v) else 0) ∧
  (∀ v < vc, s.mem (dgIncHeadBase heap vc + v) =
    if ∃ j < i, ∃ hjl : j < vL.length, vL[j]'hjl = v then st0.mem (dgIncHeadBase src vc + v) else 0)

theorem copyGraphLiveVLoop_runs {w src heap vc ec : ℕ} {G : MGraph} {vL : List ℕ}
    {p : Program} {st0 st1 : State} {ω : ℕ → Bool}
    (hG : DynGraphAt st0.mem src vc ec G)
    (hvLen : vL.length = G.n) (hvNodup : vL.Nodup) (hvMem : ∀ v, v ∈ vL ↔ v ∈ G.V)
    (hvList : ListAt st0.mem (dgVListBase src vc) vL)
    (hdisj : src + dynGraphSize vc ec ≤ heap) (hword : heap + dynGraphSize vc ec < 2 ^ w)
    (hw : 9 < 2 ^ w)
    (hframe1 : ∀ a < heap, st1.mem a = st0.mem a)
    (hinit : vLoopInv src heap vc ec G vL st0 st1.mem 0 st1) :
    ∃ out c, Runs w p ω (forUp 12 (.reg 8) copyGraphLiveVBody) st1 .normal out c ∧
      vLoopInv src heap vc ec G vL st0 st1.mem G.n out ∧ c ≤ 120 * G.n + 5 := by
  have hsz : dynGraphSize vc ec = 4 + 7 * vc + 9 * ec := rfl
  have hGn : G.n ≤ vc := graph_n_le_vCap hG
  have htrip := Triple.forUp_le (w := w) (p := p) (r := 12) (hi := .reg 8)
    (body := copyGraphLiveVBody) (Inv := vLoopInv src heap vc ec G vL st0 st1.mem)
    (stepCost := fun _ => 111) (i₀ := 0) (hiVal := G.n)
    (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun i s _ _ hI => hI.2.2.2.2.2.2.2.1)
    (fun i s _ _ hI => by simp [Expr.eval, hI.2.2.2.2.1])
    (fun i _ hi s ω' hI => by
      rcases hI with ⟨hr5, hr6, hr10, hr11, hr8, hr63, hr64, hr12, hpos, hregs, hfr,
        hVL, hVP, hVPos, hE2I, hI2E, hDeg, hHead⟩
      have hil : i < vL.length := by omega
      set v := vL[i]'hil
      have hv_in : v ∈ G.V := (hvMem v).mp (List.getElem_mem hil)
      have hv_lt : v < vc := hG.2.1 v hv_in
      have hsrc (a : ℕ) (ha : a < heap) : s.mem a = st0.mem a := by
        rw [hfr a (by omega), hframe1 a ha]
      have hsrc_v : s.mem (src + 4 + vc + i) = v := (hsrc _ (by omega)).trans (hvList i hil)
      refine runs_start_le ?_
      dsimp only [copyGraphLiveVBody]
      refine seq_assign_step (val := v)
        (by simp [Expr.eval, BinOp.eval, hr63, hr10, hr12, hsrc_v,
          show src + 4 + vc < 2 ^ w by omega, show src + 4 + vc + i < 2 ^ w by omega]) ?_
      intro s1 hs1
      have h1r : s1.regs 63 = src + 4 ∧ s1.regs 64 = heap + 4 ∧ s1.regs 10 = vc ∧
          s1.regs 12 = i ∧ s1.regs 9 = v := by
        subst hs1; simp [Function.update_of_ne, hr63, hr64, hr10, hr12]
      have h1m : s1.mem = s.mem := by subst hs1; rfl
      refine seq_store_step (addr := heap + 4 + vc + i) (val := v)
        (by simp [Expr.eval, BinOp.eval, h1r, show heap + 4 + vc < 2 ^ w by omega,
          show heap + 4 + vc + i < 2 ^ w by omega])
        (by simp [Expr.eval, h1r]) ?_
      intro s2 hs2
      have h2r : s2.regs = s1.regs := by subst hs2; rfl
      have h2src (a : ℕ) (ha : a < heap) : s2.mem a = st0.mem a := by
        subst hs2; dsimp only; rw [Function.update_of_ne (by omega), h1m]; exact hsrc a ha
      refine seq_store_step (addr := heap + 4 + v) (val := 1)
        (by simp [Expr.eval, BinOp.eval, h2r, h1r, show heap + 4 + v < 2 ^ w by omega])
        (by simp [Expr.eval, show 1 < 2 ^ w by omega]) ?_
      intro s3 hs3
      have h3r : s3.regs = s1.regs := by subst hs3; exact h2r
      have h3src (a : ℕ) (ha : a < heap) : s3.mem a = st0.mem a := by
        subst hs3; dsimp only; rw [Function.update_of_ne (by omega)]; exact h2src a ha
      refine seq_store_step (addr := heap + 4 + 2 * vc + v) (val := i)
        (copy_array_eval (h3r ▸ h1r.2.1) (h3r ▸ h1r.2.2.1) (h3r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega))
        (by simp [Expr.eval, h3r, h1r]) ?_
      intro s4 hs4
      have h4r : s4.regs = s1.regs := by subst hs4; exact h3r
      have h4src (a : ℕ) (ha : a < heap) : s4.mem a = st0.mem a := by
        subst hs4; dsimp only; rw [Function.update_of_ne (by omega)]; exact h3src a ha
      refine seq_store_step (addr := heap + 4 + 3 * vc + v)
        (val := st0.mem (dgExtToIntBase src vc + v))
        (copy_array_eval (h4r ▸ h1r.2.1) (h4r ▸ h1r.2.2.1) (h4r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega))
        (copy_array_load (h4r ▸ h1r.1) (h4r ▸ h1r.2.2.1) (h4r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega) (h4src _ (by omega))) ?_
      intro s5 hs5
      have h5r : s5.regs = s1.regs := by subst hs5; exact h4r
      have h5src (a : ℕ) (ha : a < heap) : s5.mem a = st0.mem a := by
        subst hs5; dsimp only; rw [Function.update_of_ne (by omega)]; exact h4src a ha
      refine seq_store_step (addr := heap + 4 + 4 * vc + v)
        (val := st0.mem (dgIntToExtBase src vc + v))
        (copy_array_eval (h5r ▸ h1r.2.1) (h5r ▸ h1r.2.2.1) (h5r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega))
        (copy_array_load (h5r ▸ h1r.1) (h5r ▸ h1r.2.2.1) (h5r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega) (h5src _ (by omega))) ?_
      intro s6 hs6
      have h6r : s6.regs = s1.regs := by subst hs6; exact h5r
      have h6src (a : ℕ) (ha : a < heap) : s6.mem a = st0.mem a := by
        subst hs6; dsimp only; rw [Function.update_of_ne (by omega)]; exact h5src a ha
      refine seq_store_step (addr := heap + 4 + 5 * vc + v)
        (val := st0.mem (dgSlotDegBase src vc + v))
        (copy_array_eval (h6r ▸ h1r.2.1) (h6r ▸ h1r.2.2.1) (h6r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega))
        (copy_array_load (h6r ▸ h1r.1) (h6r ▸ h1r.2.2.1) (h6r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega) (h6src _ (by omega))) ?_
      intro s7 hs7
      have h7r : s7.regs = s1.regs := by subst hs7; exact h6r
      have h7src (a : ℕ) (ha : a < heap) : s7.mem a = st0.mem a := by
        subst hs7; dsimp only; rw [Function.update_of_ne (by omega)]; exact h6src a ha
      refine runs_store_le (x := heap + 4 + 6 * vc + v)
        (v := st0.mem (dgIncHeadBase src vc + v))
        (copy_array_eval (h7r ▸ h1r.2.1) (h7r ▸ h1r.2.2.1) (h7r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega))
        (copy_array_load (h7r ▸ h1r.1) (h7r ▸ h1r.2.2.1) (h7r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega) (h7src _ (by omega)))
        ?_ (by simp)
      set mF := Function.update s7.mem (heap + 4 + 6 * vc + v) (st0.mem (dgIncHeadBase src vc + v))
      have hmF_eq (a : ℕ) (h1 : a ≠ heap + 4 + vc + i) (h2 : a ≠ heap + 4 + v)
          (h3 : a ≠ heap + 4 + 2 * vc + v) (h4 : a ≠ heap + 4 + 3 * vc + v)
          (h5 : a ≠ heap + 4 + 4 * vc + v) (h6 : a ≠ heap + 4 + 5 * vc + v)
          (h7 : a ≠ heap + 4 + 6 * vc + v) : mF a = s.mem a := by
        simp only [mF, hs7, hs6, hs5, hs4, hs3, hs2, hs1, Function.update_of_ne h7,
          Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4,
          Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
      have hmF_vals :
          mF (heap + 4 + vc + i) = v ∧ mF (heap + 4 + v) = 1 ∧ mF (heap + 4 + 2 * vc + v) = i ∧
          mF (heap + 4 + 3 * vc + v) = st0.mem (dgExtToIntBase src vc + v) ∧
          mF (heap + 4 + 4 * vc + v) = st0.mem (dgIntToExtBase src vc + v) ∧
          mF (heap + 4 + 5 * vc + v) = st0.mem (dgSlotDegBase src vc + v) ∧
          mF (heap + 4 + 6 * vc + v) = st0.mem (dgIncHeadBase src vc + v) := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by simp [mF]⟩
        · simp only [mF, hs7, hs6, hs5, hs4, hs3, hs2,
            Function.update_of_ne (by omega : heap + 4 + vc + i ≠ heap + 4 + 6 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + vc + i ≠ heap + 4 + 5 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + vc + i ≠ heap + 4 + 4 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + vc + i ≠ heap + 4 + 3 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + vc + i ≠ heap + 4 + 2 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + vc + i ≠ heap + 4 + v),
            Function.update_self]
        · simp only [mF, hs7, hs6, hs5, hs4, hs3,
            Function.update_of_ne (by omega : heap + 4 + v ≠ heap + 4 + 6 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + v ≠ heap + 4 + 5 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + v ≠ heap + 4 + 4 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + v ≠ heap + 4 + 3 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + v ≠ heap + 4 + 2 * vc + v),
            Function.update_self]
        · simp only [mF, hs7, hs6, hs5, hs4,
            Function.update_of_ne (by omega : heap + 4 + 2 * vc + v ≠ heap + 4 + 6 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + 2 * vc + v ≠ heap + 4 + 5 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + 2 * vc + v ≠ heap + 4 + 4 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + 2 * vc + v ≠ heap + 4 + 3 * vc + v),
            Function.update_self]
        · simp only [mF, hs7, hs6, hs5,
            Function.update_of_ne (by omega : heap + 4 + 3 * vc + v ≠ heap + 4 + 6 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + 3 * vc + v ≠ heap + 4 + 5 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + 3 * vc + v ≠ heap + 4 + 4 * vc + v),
            Function.update_self]
        · simp only [mF, hs7, hs6,
            Function.update_of_ne (by omega : heap + 4 + 4 * vc + v ≠ heap + 4 + 6 * vc + v),
            Function.update_of_ne (by omega : heap + 4 + 4 * vc + v ≠ heap + 4 + 5 * vc + v),
            Function.update_self]
        · simp only [mF, hs7,
            Function.update_of_ne (by omega : heap + 4 + 5 * vc + v ≠ heap + 4 + 6 * vc + v),
            Function.update_self]
      have hposF : s7.pos = st0.pos := by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, hpos]
      have hregsF (r : ℕ) (h9 : r ≠ 9) : s7.regs r = s.regs r := by
        rw [h7r]; subst hs1; exact Function.update_of_ne h9 _ _
      have hne_v (j : ℕ) (hji : j ≠ i) (hjl : j < vL.length) : vL[j]'hjl ≠ v := fun heq =>
        hji (congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hvNodup)
          (a₁ := ⟨j, hjl⟩) (a₂ := ⟨i, hil⟩) heq))
      have hex_step (u : ℕ) (huv : u ≠ v) :
          (∃ j < i + 1, ∃ hjl : j < vL.length, vL[j]'hjl = u) ↔
          (∃ j < i, ∃ hjl : j < vL.length, vL[j]'hjl = u) :=
        ⟨fun ⟨j, hj, hjl, hjeq⟩ => ⟨j, by
            by_cases hji : j = i
            · subst hji; exact absurd hjeq.symm huv
            · omega, hjl, hjeq⟩,
          fun ⟨j, hj, hjl, hjeq⟩ => ⟨j, by omega, hjl, hjeq⟩⟩
      change vLoopInv src heap vc ec G vL st0 st1.mem (i + 1)
        { mem := mF, regs := Function.update s7.regs 12 (i + 1), pos := s7.pos } ∧ s7.regs 12 = i
      clear hs7 hs6 hs5 hs4 hs3 hs2 hs1
      refine ⟨⟨by simp [Function.update_of_ne, hregsF 5 (by decide), hr5],
        by simp [Function.update_of_ne, hregsF 6 (by decide), hr6],
        by simp [Function.update_of_ne, hregsF 10 (by decide), hr10],
        by simp [Function.update_of_ne, hregsF 11 (by decide), hr11],
        by simp [Function.update_of_ne, hregsF 8 (by decide), hr8],
        by simp [Function.update_of_ne, hregsF 63 (by decide), hr63],
        by simp [Function.update_of_ne, hregsF 64 (by decide), hr64],
        by simp, hposF,
        fun r h8 h9 h10 h11 h12 h63 h64 => by
          dsimp only; rw [Function.update_of_ne h12, hregsF r h9]; exact hregs r h8 h9 h10 h11 h12 h63 h64,
        fun a ha => (hmF_eq a (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)).trans (hfr a ha),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, (hregsF 12 (by decide)).trans hr12⟩
      · intro j hj hjl
        by_cases hji : j = i
        · subst hji; exact hmF_vals.1
        · exact (hmF_eq _ (by unfold dgVListBase; omega) (by unfold dgVListBase; omega)
            (by unfold dgVListBase; omega) (by unfold dgVListBase; omega) (by unfold dgVListBase; omega)
            (by unfold dgVListBase; omega) (by unfold dgVListBase; omega)).trans (hVL j (by omega) hjl)
      · intro u hu
        by_cases huv : u = v
        · subst huv
          simp only [show ∃ j < i + 1, ∃ hjl : j < vL.length, vL[j]'hjl = v from ⟨i, by omega, hil, rfl⟩,
            ↓reduceIte]; exact hmF_vals.2.1
        · dsimp only
          rw [hmF_eq _ (by unfold dgVPresBase; omega) (by unfold dgVPresBase; omega)
            (by unfold dgVPresBase; omega) (by unfold dgVPresBase; omega) (by unfold dgVPresBase; omega)
            (by unfold dgVPresBase; omega) (by unfold dgVPresBase; omega), hVP u hu]
          simp only [hex_step u huv]
      · intro j hj hjl
        have hvj : vL[j]'hjl < vc := hG.2.1 _ ((hvMem _).mp (List.getElem_mem hjl))
        by_cases hji : j = i
        · subst hji; exact hmF_vals.2.2.1
        · have hne := hne_v j hji hjl
          exact (hmF_eq _ (by unfold dgVPosBase; omega) (by unfold dgVPosBase; omega)
            (by unfold dgVPosBase; omega) (by unfold dgVPosBase; omega) (by unfold dgVPosBase; omega)
            (by unfold dgVPosBase; omega) (by unfold dgVPosBase; omega)).trans (hVPos j (by omega) hjl)
      · intro j hj hjl
        have hvj : vL[j]'hjl < vc := hG.2.1 _ ((hvMem _).mp (List.getElem_mem hjl))
        by_cases hji : j = i
        · subst hji; exact hmF_vals.2.2.2.1
        · have hne := hne_v j hji hjl
          exact (hmF_eq _ (by unfold dgExtToIntBase; omega) (by unfold dgExtToIntBase; omega)
            (by unfold dgExtToIntBase; omega) (by unfold dgExtToIntBase; omega) (by unfold dgExtToIntBase; omega)
            (by unfold dgExtToIntBase; omega) (by unfold dgExtToIntBase; omega)).trans (hE2I j (by omega) hjl)
      · intro j hj hjl
        have hvj : vL[j]'hjl < vc := hG.2.1 _ ((hvMem _).mp (List.getElem_mem hjl))
        by_cases hji : j = i
        · subst hji; exact hmF_vals.2.2.2.2.1
        · have hne := hne_v j hji hjl
          exact (hmF_eq _ (by unfold dgIntToExtBase; omega) (by unfold dgIntToExtBase; omega)
            (by unfold dgIntToExtBase; omega) (by unfold dgIntToExtBase; omega) (by unfold dgIntToExtBase; omega)
            (by unfold dgIntToExtBase; omega) (by unfold dgIntToExtBase; omega)).trans (hI2E j (by omega) hjl)
      · intro u hu
        by_cases huv : u = v
        · subst huv
          simp only [show ∃ j < i + 1, ∃ hjl : j < vL.length, vL[j]'hjl = v from ⟨i, by omega, hil, rfl⟩,
            ↓reduceIte]; exact hmF_vals.2.2.2.2.2.1
        · dsimp only
          rw [hmF_eq _ (by unfold dgSlotDegBase; omega) (by unfold dgSlotDegBase; omega)
            (by unfold dgSlotDegBase; omega) (by unfold dgSlotDegBase; omega) (by unfold dgSlotDegBase; omega)
            (by unfold dgSlotDegBase; omega) (by unfold dgSlotDegBase; omega), hDeg u hu]
          simp only [hex_step u huv]
      · intro u hu
        by_cases huv : u = v
        · subst huv
          simp only [show ∃ j < i + 1, ∃ hjl : j < vL.length, vL[j]'hjl = v from ⟨i, by omega, hil, rfl⟩,
            ↓reduceIte]; exact hmF_vals.2.2.2.2.2.2
        · dsimp only
          rw [hmF_eq _ (by unfold dgIncHeadBase; omega) (by unfold dgIncHeadBase; omega)
            (by unfold dgIncHeadBase; omega) (by unfold dgIncHeadBase; omega) (by unfold dgIncHeadBase; omega)
            (by unfold dgIncHeadBase; omega) (by unfold dgIncHeadBase; omega), hHead u hu]
          simp only [hex_step u huv])
  obtain ⟨o, out, c, hr, hq, hc⟩ := htrip st1 ω hinit
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    refine ⟨out, c, hr, hq, ?_⟩
    simp only [rangeCost_const, Nat.sub_zero, Expr.size_reg] at hc
    omega

/-- Loop invariant for the edge copy loop. -/
@[expose] def eLoopInv (src heap vc ec : ℕ) (G : MGraph) (eL : List ℕ)
    (st0 : State) (mem2 : ℕ → ℕ) (i : ℕ) (s : State) : Prop :=
  s.regs 5 = heap ∧ s.regs 6 = src ∧ s.regs 10 = ec ∧ s.regs 11 = ec ∧ s.regs 8 = G.m ∧
  s.regs 63 = src + 4 + 7 * vc ∧ s.regs 64 = heap + 4 + 7 * vc ∧ s.regs 12 = i ∧ s.pos = st0.pos ∧
  (∀ r, r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 63 → r ≠ 64 → s.regs r = st0.regs r) ∧
  (∀ a, a < heap + 4 + 7 * vc ∨ heap + dynGraphSize vc ec ≤ a → s.mem a = mem2 a) ∧
  (∀ j (_ : j < i) (hjl : j < eL.length), s.mem (dgEListBase heap vc ec + j) = eL[j]'hjl) ∧
  (∀ e < ec, s.mem (dgEPresBase heap vc + e) = if ∃ j < i, ∃ hjl : j < eL.length, eL[j]'hjl = e then 1 else 0) ∧
  (∀ j (_ : j < i) (hjl : j < eL.length), s.mem (dgEPosBase heap vc ec + eL[j]'hjl) = j) ∧
  (∀ j (_ : j < i) (hjl : j < eL.length),
    s.mem (dgETailSlotBase heap vc ec + eL[j]'hjl) = st0.mem (dgETailSlotBase src vc ec + eL[j]'hjl)) ∧
  (∀ j (_ : j < i) (hjl : j < eL.length),
    s.mem (dgEHeadSlotBase heap vc ec + eL[j]'hjl) = st0.mem (dgEHeadSlotBase src vc ec + eL[j]'hjl)) ∧
  (∀ j (_ : j < i) (hjl : j < eL.length),
    s.mem (dgHePrevBase heap vc ec + 2 * eL[j]'hjl) = st0.mem (dgHePrevBase src vc ec + 2 * eL[j]'hjl) ∧
    s.mem (dgHePrevBase heap vc ec + (2 * eL[j]'hjl + 1)) = st0.mem (dgHePrevBase src vc ec + (2 * eL[j]'hjl + 1))) ∧
  (∀ j (_ : j < i) (hjl : j < eL.length),
    s.mem (dgHeNextBase heap vc ec + 2 * eL[j]'hjl) = st0.mem (dgHeNextBase src vc ec + 2 * eL[j]'hjl) ∧
    s.mem (dgHeNextBase heap vc ec + (2 * eL[j]'hjl + 1)) = st0.mem (dgHeNextBase src vc ec + (2 * eL[j]'hjl + 1)))

theorem copyGraphLiveELoop_runs {w src heap vc ec : ℕ} {G : MGraph} {eL : List ℕ}
    {p : Program} {st0 st2 : State} {ω : ℕ → Bool}
    (hG : DynGraphAt st0.mem src vc ec G)
    (heLen : eL.length = G.m) (heNodup : eL.Nodup) (heMem : ∀ e, e ∈ eL ↔ e ∈ G.E)
    (heList : ListAt st0.mem (dgEListBase src vc ec) eL)
    (hdisj : src + dynGraphSize vc ec ≤ heap) (hword : heap + dynGraphSize vc ec < 2 ^ w)
    (hw : 9 < 2 ^ w)
    (hframe2 : ∀ a < heap, st2.mem a = st0.mem a)
    (hinit : eLoopInv src heap vc ec G eL st0 st2.mem 0 st2) :
    ∃ out c, Runs w p ω (forUp 12 (.reg 8) copyGraphLiveEBody) st2 .normal out c ∧
      eLoopInv src heap vc ec G eL st0 st2.mem G.m out ∧ c ≤ 170 * G.m + 5 := by
  have hsz : dynGraphSize vc ec = 4 + 7 * vc + 9 * ec := rfl
  have hGm : G.m ≤ ec := graph_m_le_eCap hG
  set sb := src + 4 + 7 * vc
  set db := heap + 4 + 7 * vc
  have htrip := Triple.forUp_le (w := w) (p := p) (r := 12) (hi := .reg 8)
    (body := copyGraphLiveEBody) (Inv := eLoopInv src heap vc ec G eL st0 st2.mem)
    (stepCost := fun _ => 161) (i₀ := 0) (hiVal := G.m)
    (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun i s _ _ hI => hI.2.2.2.2.2.2.2.1)
    (fun i s _ _ hI => by simp [Expr.eval, hI.2.2.2.2.1])
    (fun i _ hi s ω' hI => by
      rcases hI with ⟨hr5, hr6, hr10, hr11, hr8, hr63, hr64, hr12, hpos, hregs, hfr,
        hEL, hEP, hEPos, hTail, hHead, hPrev, hNext⟩
      have hil : i < eL.length := by omega
      set e := eL[i]'hil
      have he_in : e ∈ G.E := (heMem e).mp (List.getElem_mem hil)
      have he_lt : e < ec := hG.2.2.1 e he_in
      have hsrc (a : ℕ) (ha : a < heap) : s.mem a = st0.mem a := by
        rw [hfr a (by omega), hframe2 a ha]
      have hsrc_e : s.mem (sb + ec + i) = e := (hsrc _ (by omega)).trans (heList i hil)
      refine runs_start_le ?_
      dsimp only [copyGraphLiveEBody]
      refine seq_assign_step (val := e)
        (by simp [Expr.eval, BinOp.eval, hr63, hr10, hr12, hsrc_e, sb,
          show sb + ec < 2 ^ w by omega, show sb + ec + i < 2 ^ w by omega]) ?_
      intro s1 hs1
      have h1r : s1.regs 63 = sb ∧ s1.regs 64 = db ∧ s1.regs 10 = ec ∧
          s1.regs 12 = i ∧ s1.regs 9 = e := by
        subst hs1; simp [Function.update_of_ne, hr63, hr64, hr10, hr12, sb, db]
      have h1src (a : ℕ) (ha : a < heap) : s1.mem a = st0.mem a := by
        subst hs1; exact hsrc a ha
      refine seq_store_step (addr := db + ec + i) (val := e)
        (by simp [Expr.eval, BinOp.eval, h1r, show db + ec < 2 ^ w by omega,
          show db + ec + i < 2 ^ w by omega])
        (by simp [Expr.eval, h1r]) ?_
      intro s2 hs2
      have h2r : s2.regs = s1.regs := by subst hs2; rfl
      have h2src (a : ℕ) (ha : a < heap) : s2.mem a = st0.mem a := by
        subst hs2; dsimp only; rw [Function.update_of_ne (by dsimp [db]; omega)]; exact h1src a ha
      refine seq_store_step (addr := db + e) (val := 1)
        (by simp [Expr.eval, BinOp.eval, h2r, h1r, show db + e < 2 ^ w by omega])
        (by simp [Expr.eval, show 1 < 2 ^ w by omega]) ?_
      intro s3 hs3
      have h3r : s3.regs = s1.regs := by subst hs3; exact h2r
      have h3src (a : ℕ) (ha : a < heap) : s3.mem a = st0.mem a := by
        subst hs3; dsimp only; rw [Function.update_of_ne (by dsimp [db]; omega)]; exact h2src a ha
      refine seq_store_step (addr := db + 2 * ec + e) (val := i)
        (copy_array_eval (h3r ▸ h1r.2.1) (h3r ▸ h1r.2.2.1) (h3r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega))
        (by simp [Expr.eval, h3r, h1r]) ?_
      intro s4 hs4
      have h4r : s4.regs = s1.regs := by subst hs4; exact h3r
      have h4src (a : ℕ) (ha : a < heap) : s4.mem a = st0.mem a := by
        subst hs4; dsimp only; rw [Function.update_of_ne (by dsimp [db]; omega)]; exact h3src a ha
      refine seq_store_step (addr := db + 3 * ec + e)
        (val := st0.mem (dgETailSlotBase src vc ec + e))
        (copy_array_eval (h4r ▸ h1r.2.1) (h4r ▸ h1r.2.2.1) (h4r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega))
        (copy_array_load (h4r ▸ h1r.1) (h4r ▸ h1r.2.2.1) (h4r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega) (h4src _ (by omega))) ?_
      intro s5 hs5
      have h5r : s5.regs = s1.regs := by subst hs5; exact h4r
      have h5src (a : ℕ) (ha : a < heap) : s5.mem a = st0.mem a := by
        subst hs5; dsimp only; rw [Function.update_of_ne (by dsimp [db]; omega)]; exact h4src a ha
      refine seq_store_step (addr := db + 4 * ec + e)
        (val := st0.mem (dgEHeadSlotBase src vc ec + e))
        (copy_array_eval (h5r ▸ h1r.2.1) (h5r ▸ h1r.2.2.1) (h5r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega))
        (copy_array_load (h5r ▸ h1r.1) (h5r ▸ h1r.2.2.1) (h5r ▸ h1r.2.2.2.2)
          (by omega) (by omega) (by omega) (by omega) (h5src _ (by omega))) ?_
      intro s6 hs6
      have h6r : s6.regs = s1.regs := by subst hs6; exact h5r
      have h6src (a : ℕ) (ha : a < heap) : s6.mem a = st0.mem a := by
        subst hs6; dsimp only; rw [Function.update_of_ne (by dsimp [db]; omega)]; exact h5src a ha
      refine seq_assign_step (val := 2 * e)
        (by simp [Expr.eval, BinOp.eval, h6r, h1r, show 2 < 2 ^ w by omega,
          show 2 * e < 2 ^ w by omega]) ?_
      intro s7 hs7
      have h7r : s7.regs 63 = sb ∧ s7.regs 64 = db ∧ s7.regs 10 = ec ∧ s7.regs 9 = 2 * e := by
        subst hs7; simp [Function.update_of_ne, h6r, h1r]
      have h7src (a : ℕ) (ha : a < heap) : s7.mem a = st0.mem a := by
        subst hs7; exact h6src a ha
      refine seq_store_step (addr := db + 5 * ec + 2 * e)
        (val := st0.mem (dgHePrevBase src vc ec + 2 * e))
        (copy_array_eval h7r.2.1 h7r.2.2.1 h7r.2.2.2 (by omega) (by omega) (by omega) (by omega))
        (copy_array_load h7r.1 h7r.2.2.1 h7r.2.2.2
          (by omega) (by omega) (by omega) (by omega) (h7src _ (by omega))) ?_
      intro s8 hs8
      have h8r : s8.regs = s7.regs := by subst hs8; rfl
      have h8src (a : ℕ) (ha : a < heap) : s8.mem a = st0.mem a := by
        subst hs8; dsimp only; rw [Function.update_of_ne (by dsimp [db]; omega)]; exact h7src a ha
      refine seq_store_step (addr := db + 7 * ec + 2 * e)
        (val := st0.mem (dgHeNextBase src vc ec + 2 * e))
        (copy_array_eval (h8r ▸ h7r.2.1) (h8r ▸ h7r.2.2.1) (h8r ▸ h7r.2.2.2)
          (by omega) (by omega) (by omega) (by omega))
        (copy_array_load (h8r ▸ h7r.1) (h8r ▸ h7r.2.2.1) (h8r ▸ h7r.2.2.2)
          (by omega) (by omega) (by omega) (by omega) (h8src _ (by omega))) ?_
      intro s9 hs9
      have h9r : s9.regs = s7.regs := by subst hs9; exact h8r
      have h9src (a : ℕ) (ha : a < heap) : s9.mem a = st0.mem a := by
        subst hs9; dsimp only; rw [Function.update_of_ne (by dsimp [db]; omega)]; exact h8src a ha
      refine seq_assign_step (val := 2 * e + 1)
        (by simp [Expr.eval, BinOp.eval, h9r, h7r, show 1 < 2 ^ w by omega,
          show 2 * e + 1 < 2 ^ w by omega]) ?_
      intro s10 hs10
      have h10r : s10.regs 63 = sb ∧ s10.regs 64 = db ∧ s10.regs 10 = ec ∧
          s10.regs 9 = 2 * e + 1 := by
        subst hs10; simp [Function.update_of_ne, h9r, h7r]
      have h10src (a : ℕ) (ha : a < heap) : s10.mem a = st0.mem a := by
        subst hs10; exact h9src a ha
      refine seq_store_step (addr := db + 5 * ec + (2 * e + 1))
        (val := st0.mem (dgHePrevBase src vc ec + (2 * e + 1)))
        (copy_array_eval h10r.2.1 h10r.2.2.1 h10r.2.2.2 (by omega) (by omega) (by omega) (by omega))
        (copy_array_load h10r.1 h10r.2.2.1 h10r.2.2.2
          (by omega) (by omega) (by omega) (by omega) (h10src _ (by omega))) ?_
      intro s11 hs11
      have h11r : s11.regs = s10.regs := by subst hs11; rfl
      have h11src (a : ℕ) (ha : a < heap) : s11.mem a = st0.mem a := by
        subst hs11; dsimp only; rw [Function.update_of_ne (by dsimp [db]; omega)]; exact h10src a ha
      refine runs_store_le (x := db + 7 * ec + (2 * e + 1))
        (v := st0.mem (dgHeNextBase src vc ec + (2 * e + 1)))
        (copy_array_eval (h11r ▸ h10r.2.1) (h11r ▸ h10r.2.2.1) (h11r ▸ h10r.2.2.2)
          (by omega) (by omega) (by omega) (by omega))
        (copy_array_load (h11r ▸ h10r.1) (h11r ▸ h10r.2.2.1) (h11r ▸ h10r.2.2.2)
          (by omega) (by omega) (by omega) (by omega) (h11src _ (by omega)))
        ?_ (by simp)
      set mF := Function.update s11.mem (db + 7 * ec + (2 * e + 1))
        (st0.mem (dgHeNextBase src vc ec + (2 * e + 1)))
      have hmF_eq (a : ℕ)
          (h1 : a ≠ db + ec + i) (h2 : a ≠ db + e) (h3 : a ≠ db + 2 * ec + e)
          (h4 : a ≠ db + 3 * ec + e) (h5 : a ≠ db + 4 * ec + e)
          (h6 : a ≠ db + 5 * ec + 2 * e) (h7 : a ≠ db + 7 * ec + 2 * e)
          (h8 : a ≠ db + 5 * ec + (2 * e + 1)) (h9 : a ≠ db + 7 * ec + (2 * e + 1)) :
          mF a = s.mem a := by
        simp only [mF, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1,
          Function.update_of_ne h9, Function.update_of_ne h8, Function.update_of_ne h7,
          Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4,
          Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
      have hmF_vals :
          mF (db + ec + i) = e ∧ mF (db + e) = 1 ∧ mF (db + 2 * ec + e) = i ∧
          mF (db + 3 * ec + e) = st0.mem (dgETailSlotBase src vc ec + e) ∧
          mF (db + 4 * ec + e) = st0.mem (dgEHeadSlotBase src vc ec + e) ∧
          mF (db + 5 * ec + 2 * e) = st0.mem (dgHePrevBase src vc ec + 2 * e) ∧
          mF (db + 7 * ec + 2 * e) = st0.mem (dgHeNextBase src vc ec + 2 * e) ∧
          mF (db + 5 * ec + (2 * e + 1)) = st0.mem (dgHePrevBase src vc ec + (2 * e + 1)) ∧
          mF (db + 7 * ec + (2 * e + 1)) = st0.mem (dgHeNextBase src vc ec + (2 * e + 1)) := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp [mF]⟩
        · simp only [mF, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2,
            Function.update_of_ne (by omega : db + ec + i ≠ db + 7 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + ec + i ≠ db + 5 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + ec + i ≠ db + 7 * ec + 2 * e),
            Function.update_of_ne (by omega : db + ec + i ≠ db + 5 * ec + 2 * e),
            Function.update_of_ne (by omega : db + ec + i ≠ db + 4 * ec + e),
            Function.update_of_ne (by omega : db + ec + i ≠ db + 3 * ec + e),
            Function.update_of_ne (by omega : db + ec + i ≠ db + 2 * ec + e),
            Function.update_of_ne (by omega : db + ec + i ≠ db + e), Function.update_self]
        · simp only [mF, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3,
            Function.update_of_ne (by omega : db + e ≠ db + 7 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + e ≠ db + 5 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + e ≠ db + 7 * ec + 2 * e),
            Function.update_of_ne (by omega : db + e ≠ db + 5 * ec + 2 * e),
            Function.update_of_ne (by omega : db + e ≠ db + 4 * ec + e),
            Function.update_of_ne (by omega : db + e ≠ db + 3 * ec + e),
            Function.update_of_ne (by omega : db + e ≠ db + 2 * ec + e), Function.update_self]
        · simp only [mF, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4,
            Function.update_of_ne (by omega : db + 2 * ec + e ≠ db + 7 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + 2 * ec + e ≠ db + 5 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + 2 * ec + e ≠ db + 7 * ec + 2 * e),
            Function.update_of_ne (by omega : db + 2 * ec + e ≠ db + 5 * ec + 2 * e),
            Function.update_of_ne (by omega : db + 2 * ec + e ≠ db + 4 * ec + e),
            Function.update_of_ne (by omega : db + 2 * ec + e ≠ db + 3 * ec + e), Function.update_self]
        · simp only [mF, hs11, hs10, hs9, hs8, hs7, hs6, hs5,
            Function.update_of_ne (by omega : db + 3 * ec + e ≠ db + 7 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + 3 * ec + e ≠ db + 5 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + 3 * ec + e ≠ db + 7 * ec + 2 * e),
            Function.update_of_ne (by omega : db + 3 * ec + e ≠ db + 5 * ec + 2 * e),
            Function.update_of_ne (by omega : db + 3 * ec + e ≠ db + 4 * ec + e), Function.update_self]
        · simp only [mF, hs11, hs10, hs9, hs8, hs7, hs6,
            Function.update_of_ne (by omega : db + 4 * ec + e ≠ db + 7 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + 4 * ec + e ≠ db + 5 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + 4 * ec + e ≠ db + 7 * ec + 2 * e),
            Function.update_of_ne (by omega : db + 4 * ec + e ≠ db + 5 * ec + 2 * e), Function.update_self]
        · simp only [mF, hs11, hs10, hs9, hs8,
            Function.update_of_ne (by omega : db + 5 * ec + 2 * e ≠ db + 7 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + 5 * ec + 2 * e ≠ db + 5 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + 5 * ec + 2 * e ≠ db + 7 * ec + 2 * e), Function.update_self]
        · simp only [mF, hs11, hs10, hs9,
            Function.update_of_ne (by omega : db + 7 * ec + 2 * e ≠ db + 7 * ec + (2 * e + 1)),
            Function.update_of_ne (by omega : db + 7 * ec + 2 * e ≠ db + 5 * ec + (2 * e + 1)), Function.update_self]
        · simp only [mF, hs11,
            Function.update_of_ne (by omega : db + 5 * ec + (2 * e + 1) ≠ db + 7 * ec + (2 * e + 1)),
            Function.update_self]
      have hposF : s11.pos = st0.pos := by
        simp [hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hpos]
      have hregsF (r : ℕ) (h9 : r ≠ 9) : s11.regs r = s.regs r := by
        simp only [h11r, hs10, h9r, hs7, h6r, hs1, Function.update_of_ne h9]
      have hne_e (j : ℕ) (hji : j ≠ i) (hjl : j < eL.length) : eL[j]'hjl ≠ e := fun heq =>
        hji (congrArg Fin.val ((List.nodup_iff_injective_getElem.mp heNodup)
          (a₁ := ⟨j, hjl⟩) (a₂ := ⟨i, hil⟩) heq))
      have hex_step (u : ℕ) (hue : u ≠ e) :
          (∃ j < i + 1, ∃ hjl : j < eL.length, eL[j]'hjl = u) ↔
          (∃ j < i, ∃ hjl : j < eL.length, eL[j]'hjl = u) :=
        ⟨fun ⟨j, hj, hjl, hjeq⟩ => ⟨j, by
            by_cases hji : j = i
            · subst hji; exact absurd hjeq.symm hue
            · omega, hjl, hjeq⟩,
          fun ⟨j, hj, hjl, hjeq⟩ => ⟨j, by omega, hjl, hjeq⟩⟩
      change eLoopInv src heap vc ec G eL st0 st2.mem (i + 1)
        { mem := mF, regs := Function.update s11.regs 12 (i + 1), pos := s11.pos } ∧ s11.regs 12 = i
      clear hs11 hs10 hs9 hs8 hs7 hs6 hs5 hs4 hs3 hs2 hs1 h11src h10src h9src h8src h7src h6src
        h5src h4src h3src h2src h1src h11r h10r h9r h8r h7r h6r h5r h4r h3r h2r h1r
      refine ⟨⟨by simp [Function.update_of_ne, hregsF 5 (by decide), hr5],
        by simp [Function.update_of_ne, hregsF 6 (by decide), hr6],
        by simp [Function.update_of_ne, hregsF 10 (by decide), hr10],
        by simp [Function.update_of_ne, hregsF 11 (by decide), hr11],
        by simp [Function.update_of_ne, hregsF 8 (by decide), hr8],
        by simp [Function.update_of_ne, hregsF 63 (by decide), hr63],
        by simp [Function.update_of_ne, hregsF 64 (by decide), hr64],
        by simp, hposF,
        fun r h8 h9 h10 h11 h12 h63 h64 => by
          dsimp only; rw [Function.update_of_ne h12, hregsF r h9]; exact hregs r h8 h9 h10 h11 h12 h63 h64,
        fun a ha => (hmF_eq a (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega)).trans (hfr a ha),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, (hregsF 12 (by decide)).trans hr12⟩
      · intro j hj hjl
        by_cases hji : j = i
        · subst hji; exact hmF_vals.1
        · exact (hmF_eq _ (by unfold dgEListBase; omega) (by unfold dgEListBase; omega)
            (by unfold dgEListBase; omega) (by unfold dgEListBase; omega) (by unfold dgEListBase; omega)
            (by unfold dgEListBase; omega) (by unfold dgEListBase; omega) (by unfold dgEListBase; omega)
            (by unfold dgEListBase; omega)).trans (hEL j (by omega) hjl)
      · intro u hu
        by_cases hue : u = e
        · subst hue
          simp only [show ∃ j < i + 1, ∃ hjl : j < eL.length, eL[j]'hjl = e from ⟨i, by omega, hil, rfl⟩,
            ↓reduceIte]; exact hmF_vals.2.1
        · dsimp only
          rw [hmF_eq _ (by unfold dgEPresBase; omega) (by unfold dgEPresBase; omega)
            (by unfold dgEPresBase; omega) (by unfold dgEPresBase; omega) (by unfold dgEPresBase; omega)
            (by unfold dgEPresBase; omega) (by unfold dgEPresBase; omega) (by unfold dgEPresBase; omega)
            (by unfold dgEPresBase; omega), hEP u hu]
          simp only [hex_step u hue]
      · intro j hj hjl
        have hej : eL[j]'hjl < ec := hG.2.2.1 _ ((heMem _).mp (List.getElem_mem hjl))
        by_cases hji : j = i
        · subst hji; exact hmF_vals.2.2.1
        · have hne := hne_e j hji hjl
          exact (hmF_eq _ (by unfold dgEPosBase; omega) (by unfold dgEPosBase; omega)
            (by unfold dgEPosBase; omega) (by unfold dgEPosBase; omega) (by unfold dgEPosBase; omega)
            (by unfold dgEPosBase; omega) (by unfold dgEPosBase; omega) (by unfold dgEPosBase; omega)
            (by unfold dgEPosBase; omega)).trans (hEPos j (by omega) hjl)
      · intro j hj hjl
        have hej : eL[j]'hjl < ec := hG.2.2.1 _ ((heMem _).mp (List.getElem_mem hjl))
        by_cases hji : j = i
        · subst hji; exact hmF_vals.2.2.2.1
        · have hne := hne_e j hji hjl
          exact (hmF_eq _ (by unfold dgETailSlotBase; omega) (by unfold dgETailSlotBase; omega)
            (by unfold dgETailSlotBase; omega) (by unfold dgETailSlotBase; omega) (by unfold dgETailSlotBase; omega)
            (by unfold dgETailSlotBase; omega) (by unfold dgETailSlotBase; omega) (by unfold dgETailSlotBase; omega)
            (by unfold dgETailSlotBase; omega)).trans (hTail j (by omega) hjl)
      · intro j hj hjl
        have hej : eL[j]'hjl < ec := hG.2.2.1 _ ((heMem _).mp (List.getElem_mem hjl))
        by_cases hji : j = i
        · subst hji; exact hmF_vals.2.2.2.2.1
        · have hne := hne_e j hji hjl
          exact (hmF_eq _ (by unfold dgEHeadSlotBase; omega) (by unfold dgEHeadSlotBase; omega)
            (by unfold dgEHeadSlotBase; omega) (by unfold dgEHeadSlotBase; omega) (by unfold dgEHeadSlotBase; omega)
            (by unfold dgEHeadSlotBase; omega) (by unfold dgEHeadSlotBase; omega) (by unfold dgEHeadSlotBase; omega)
            (by unfold dgEHeadSlotBase; omega)).trans (hHead j (by omega) hjl)
      · intro j hj hjl
        have hej : eL[j]'hjl < ec := hG.2.2.1 _ ((heMem _).mp (List.getElem_mem hjl))
        by_cases hji : j = i
        · subst hji; exact ⟨hmF_vals.2.2.2.2.2.1, hmF_vals.2.2.2.2.2.2.2.1⟩
        · have hne := hne_e j hji hjl
          exact ⟨(hmF_eq _ (by unfold dgHePrevBase; omega) (by unfold dgHePrevBase; omega)
              (by unfold dgHePrevBase; omega) (by unfold dgHePrevBase; omega) (by unfold dgHePrevBase; omega)
              (by unfold dgHePrevBase; omega) (by unfold dgHePrevBase; omega) (by unfold dgHePrevBase; omega)
              (by unfold dgHePrevBase; omega)).trans (hPrev j (by omega) hjl).1,
            (hmF_eq _ (by unfold dgHePrevBase; omega) (by unfold dgHePrevBase; omega)
              (by unfold dgHePrevBase; omega) (by unfold dgHePrevBase; omega) (by unfold dgHePrevBase; omega)
              (by unfold dgHePrevBase; omega) (by unfold dgHePrevBase; omega) (by unfold dgHePrevBase; omega)
              (by unfold dgHePrevBase; omega)).trans (hPrev j (by omega) hjl).2⟩
      · intro j hj hjl
        have hej : eL[j]'hjl < ec := hG.2.2.1 _ ((heMem _).mp (List.getElem_mem hjl))
        by_cases hji : j = i
        · subst hji; exact ⟨hmF_vals.2.2.2.2.2.2.1, hmF_vals.2.2.2.2.2.2.2.2⟩
        · have hne := hne_e j hji hjl
          exact ⟨(hmF_eq _ (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega)
              (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega)
              (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega)
              (by unfold dgHeNextBase; omega)).trans (hNext j (by omega) hjl).1,
            (hmF_eq _ (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega)
              (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega)
              (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega)
              (by unfold dgHeNextBase; omega)).trans (hNext j (by omega) hjl).2⟩)
  obtain ⟨o, out, c, hr, hq, hc⟩ := htrip st2 ω hinit
  cases o with
  | returned _ => exact False.elim hq
  | normal =>
    refine ⟨out, c, hr, hq, ?_⟩
    simp only [rangeCost_const, Nat.sub_zero, Expr.size_reg] at hc
    omega

end MinCostFlow.MinRatio
