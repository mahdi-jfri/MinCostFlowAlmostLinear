module

public import MinCostFlow.HierPaths.DelProgWalkLoop
public import MinCostFlow.HierPaths.DelProgOrder

/-!
# Refreshing the support cursors of connector walks

The outer pass reads the work list of newly ineligible connectors and scans each stored walk.
The cursor invariant follows the concatenation of their vertex lists.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Visit the connector list at register 55, of length in register 56. -/
def delWalkPass : Stmt :=
  forRange 57 (.const 0) (.reg 56)
    (.seq (.assign 54 (.load (.bin .add (.reg 55) (.reg 57)))) delConnectorWalkVerts)

theorem delWalkPass_noRand : delWalkPass.NoRand := by
  simp [delWalkPass, forRange, forUp, Stmt.NoRand, delConnectorWalkVerts_noRand]

/-- Concatenated vertex lists visited by the connector scan. -/
def HierConcrete.walkPassVerts (x : HierConcrete) (cs : List ℕ) : List ℕ :=
  cs.flatMap fun c => (x.H.A.C.walk c).verts

theorem HierConcrete.refreshWalkVerts_append (x : HierConcrete) (vs ws : List ℕ) :
    x.refreshWalkVerts (vs ++ ws) = (x.refreshWalkVerts vs).refreshWalkVerts ws :=
  List.foldl_append ..

/-- The cursor state after the first `i` connectors. -/
def DelWalkPassInv (x : HierConcrete) (b base : ℕ) (cs : List ℕ) (mem0 : ℕ → ℕ)
    (i : ℕ) (s : State) : Prop :=
  s.regs 0 = b ∧ s.regs 55 = base ∧ s.regs 56 = cs.length ∧ s.regs 57 = i ∧
  ListAt s.mem b (x.refreshWalkVerts (x.walkPassVerts (cs.take i))).encode ∧
  ListAt s.mem base cs ∧ ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j

/-- Charge the walk scan at the cursor positions reached by the previous scans. -/
def delWalkPassStepCost (x : HierConcrete) (cs : List ℕ) (i : ℕ) : ℕ :=
  let c := cs.getD i 0
  let y := x.refreshWalkVerts (x.walkPassVerts (cs.take i))
  let lo := y.walkVertStart c
  let vs := (y.H.A.C.walk c).verts
  rangeCost (delWalkVertsStepCost y lo vs) lo (lo + vs.length) + vs.length * 9 + 96

/-- Scan the next stored walk, preserving the connector work list. -/
theorem delWalkPassBody_triple {w : ℕ} {p : Program} (x : HierConcrete) {b base i : ℕ}
    {cs : List ℕ} {mem0 : ℕ → ℕ}
    (hb : b + x.encode.length ≤ base) (hw : base + cs.length < 2 ^ w)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numConn)
    (hv : ∀ c ∈ cs, ∀ v ∈ (x.H.A.C.walk c).verts, v < x.n)
    (hN : ∀ v < x.n, (x.H.A.C.supportArray v).length + 1 < 2 ^ w)
    (hcur : ∀ v, x.ms.st.supCur v ≤ (x.H.A.C.supportArray v).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    (hi : i < cs.length) :
    Triple w p (DelWalkPassInv x b base cs mem0 i)
      (.seq (.assign 54 (.load (.bin .add (.reg 55) (.reg 57)))) delConnectorWalkVerts)
      (normalPost fun s => DelWalkPassInv x b base cs mem0 (i + 1)
        { s with regs := Function.update s.regs 57 (i + 1) } ∧ s.regs 57 = i)
      (fun _ => delWalkPassStepCost x cs i) := by
  let c := cs[i]
  let seen := x.walkPassVerts (cs.take i)
  let y := x.refreshWalkVerts seen
  have hcm : c ∈ cs := List.getElem_mem hi
  have hyH : y.H = x.H := (x.refreshWalkVerts_data seen).1
  have hyLoss : y.ms.st.loss = x.ms.st.loss := (x.refreshWalkVerts_data seen).2.1
  have hyIn : y.ms.st.inelig = x.ms.st.inelig := (x.refreshWalkVerts_data seen).2.2
  have hyN : y.n = x.n := x.refreshWalkVerts_n seen
  have hSurv : y.H.A.surv y.ms.st = x.H.A.surv x.ms.st := by
    simp only [StaticArrays.surv, hyH, hyLoss]
  have hlen : y.encode.length = x.encode.length := x.length_encode_refreshWalkVerts _
  have hyb : b + y.encode.length < 2 ^ w := by rw [hlen]; omega
  have hyI : y.ms.st.inelig = (Finset.range y.H.A.C.numConn).filter fun d =>
      ¬ y.H.A.C.Eligible (y.H.A.surv y.ms.st) d := by
    rw [hyIn, hSurv, hyH]; exact hinel
  have hnext : x.refreshWalkVerts (x.walkPassVerts (cs.take (i + 1))) =
      y.refreshWalkVerts (y.H.A.C.walk c).verts := by
    rw [List.take_succ_eq_append_getElem hi, HierConcrete.walkPassVerts, List.flatMap_append,
      x.refreshWalkVerts_append, hyH]
    simp
    rfl
  intro s ω hs
  obtain ⟨h0, h55, h56, h57, hy, hl, hf⟩ := hs
  let R := Function.update s.regs 54 c
  let M := fun mem => ListAt mem b y.encode ∧ mem = s.mem
  have hread : Triple w p (fun st => st.regs = s.regs ∧ M st.mem)
      (.assign 54 (.load (.bin .add (.reg 55) (.reg 57))))
      (normalPost fun st => st.regs = R ∧ M st.mem)
      (fun _ => 5) := by
    exact triple_assign_exact fun st hr hm =>
      Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_reg_of_eq (hr ▸ h55)) (Expr.eval_reg_of_eq (hr ▸ h57)) (by omega))
        (by rw [hm.2]; exact hl i hi)
  have H := delConnectorWalkVerts_triple (w := w) (p := p) (mem0 := s.mem) (R := R) (c := c) y
    (by simpa [R] using h0) (by simp [R]) (by rw [hyH]; exact hc c hcm) hyb
    (by rw [hyH, hyN]; exact hv c hcm) (by rw [hyH, hyN]; exact hN)
    (by rw [hyH]; exact x.refreshWalkVerts_cur_le seen hcur) hyI
  have Hfr := Triple.regs_frame (n := 55)
    (show Stmt.WritesBelow 55 delConnectorWalkVerts by
      simp [delConnectorWalkVerts, delCsrSetup, delWalkVertsLoop, forRange, forUp,
        delRefreshWalkVertex, delSupRefresh, delCursorSetup, advanceStmt, supTestStmt,
        delCursorStore, Stmt.WritesBelow]) H s.regs
  have htail := Hfr.weaken_pre (P' := fun st => st.regs = R ∧ M st.mem) (fun st hs =>
    ⟨⟨hs.1, hs.2.1, hs.2.2⟩, fun r hr => by rw [hs.1]; simp [R, Function.update_of_ne
      (show r ≠ 54 by omega)]⟩)
  have HT := Triple.seq_normal_const hread htail
  obtain ⟨o, s', cost, hrun, ⟨hpost, hregs⟩, hk⟩ := HT s ω ⟨rfl, hy, rfl⟩
  cases o <;> try contradiction
  obtain ⟨h0', hblock, hframe⟩ := hpost
  have hf' : ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s'.mem j = s.mem j := by
    simpa only [hlen] using hframe
  refine ⟨_, s', cost, hrun, ?_, ?_⟩
  · refine ⟨⟨by simpa using h0', by simpa using (hregs 55 (by decide)).trans h55,
      by simpa using (hregs 56 (by decide)).trans h56, by simp, hnext ▸ hblock,
      listAt_congr (fun j hj => (hf' _ (Or.inr (by omega))).symm) hl,
      fun j hj => (hf' j hj).trans (hf j hj)⟩, (hregs 57 (by decide)).trans h57⟩
  · unfold delWalkPassStepCost
    rw [List.getD_eq_getElem _ _ hi]
    dsimp only at hk ⊢
    simp only [c, y, seen] at hk
    omega

/-- The walk pass refreshes the support cursors of all listed walks and preserves all memory outside the block. -/
theorem delWalkPass_triple {w : ℕ} {p : Program} (x : HierConcrete) {b base : ℕ}
    {cs : List ℕ} {mem0 R : ℕ → ℕ}
    (h0 : R 0 = b) (h55 : R 55 = base) (h56 : R 56 = cs.length)
    (hb : b + x.encode.length ≤ base) (hw : base + cs.length < 2 ^ w)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numConn)
    (hv : ∀ c ∈ cs, ∀ v ∈ (x.H.A.C.walk c).verts, v < x.n)
    (hN : ∀ q < x.n, (x.H.A.C.supportArray q).length + 1 < 2 ^ w)
    (hcur : ∀ q, x.ms.st.supCur q ≤ (x.H.A.C.supportArray q).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base cs ∧ s.mem = mem0) delWalkPass
      (normalPost fun s => s.regs 0 = b ∧
        ListAt s.mem b (x.refreshWalkVerts (x.walkPassVerts cs)).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun _ => rangeCost (delWalkPassStepCost x cs) 0 cs.length + cs.length * 9 + 7) := by
  have hone : 1 < 2 ^ w := by have := x.le_length_encode; omega
  have H := Triple.forRange_le (w := w) (p := p) (r := 57) (lo := .const 0)
    (hi := .reg 56) (Inv := DelWalkPassInv x b base cs mem0)
    (delWalkPassStepCost x cs) 0 cs.length (Nat.zero_le _) hone (fun _ => by omega)
    (P := fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem base cs ∧ s.mem = mem0)
    (fun s hs => ⟨Expr.eval_const (by omega), ?_⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
    (fun _ _ hi => delWalkPassBody_triple x hb hw hc hv hN hcur hinel hi)
  · refine (H.strengthen_post fun o s h => ?_).mono_cost (fun _ _ => by simp [Expr.size])
    cases o <;> try contradiction
    change DelWalkPassInv x b base cs mem0 cs.length s at h
    simp only [DelWalkPassInv, List.take_length] at h
    obtain ⟨hr, _, _, _, hblock, _, hf⟩ := h
    exact ⟨hr, hblock, hf⟩
  · obtain ⟨hr, hblock, hl, hm⟩ := hs
    refine ⟨?_, ?_, ?_, by simp, ?_, hl, fun j _ => congrFun hm j⟩
    · simpa [hr] using h0
    · simpa [hr] using h55
    · simpa [hr] using h56
    · exact hblock

/-- The concrete walk pass is the model cursor refresh over the work list. -/
theorem HierConcrete.refreshWalkVerts_eq (x : HierConcrete) (cs : List ℕ) :
    (x.refreshWalkVerts cs).ms.st.supCur =
      refreshAll (fun q => x.H.A.supValid (x.H.A.surv x.ms.st) q)
        (fun q => (x.H.A.C.supportArray q).length) x.ms.st.supCur cs := by
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton cs c ih =>
    rw [x.refreshWalkVerts_append_one]
    simp only [refreshAll, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    obtain ⟨hH, hLoss, _⟩ := x.refreshWalkVerts_data cs
    have hSurv : (x.refreshWalkVerts cs).H.A.surv (x.refreshWalkVerts cs).ms.st =
        x.H.A.surv x.ms.st := by simp only [StaticArrays.surv, hH, hLoss]
    change Function.update (x.refreshWalkVerts cs).ms.st.supCur c
      (advance ((x.refreshWalkVerts cs).H.A.supValid
        ((x.refreshWalkVerts cs).H.A.surv (x.refreshWalkVerts cs).ms.st) c)
        ((x.refreshWalkVerts cs).H.A.C.supportArray c).length
        ((x.refreshWalkVerts cs).ms.st.supCur c)) = _
    rw [hSurv, hH, ih]

end MinCostFlow.HierPaths

end
