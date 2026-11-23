module

public import MinCostFlow.HierPaths.DelProgPairRefresh
public import MinCostFlow.HierPaths.DelProgOrder

/-!
# Refreshing pairs from the connector work list

Each newly ineligible connector identifies one pair in the static table. Refreshing that
pair again is safe because the cursor is already at the first eligible entry or at the end.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Read the pair of the connector in register 48 and refresh its cursor. -/
def delRefreshConnPair : Stmt :=
  .seq (.assign 39 (readSec numSec 0 5 (.reg 48))) delPairRefresh

theorem delRefreshConnPair_noRand : delRefreshConnPair.NoRand := by
  simp [delRefreshConnPair, Stmt.NoRand, delPairRefresh_noRand]

theorem delRefreshConnPair_writesBelow : Stmt.WritesBelow 49 delRefreshConnPair := by
  simp [delRefreshConnPair, delPairRefresh, delCursorSetup, delCsrSetup,
    advanceStmt, pairTestStmt, delCursorStore, Stmt.WritesBelow]

/-- A connector's pair refresh uses only its stored pair number. -/
theorem delRefreshConnPair_triple {w : ℕ} {p : Program} (x : HierConcrete) {b c : ℕ}
    {mem0 R : ℕ → ℕ} (h0 : R 0 = b) (h48 : R 48 = c)
    (hc : c < x.H.A.C.numConn) (hb : b + x.encode.length < 2 ^ w)
    (hq : x.H.A.pairOf c < x.H.A.numPairs)
    (hN : (x.H.A.pairConns (x.H.A.pairOf c)).length + 1 < 2 ^ w)
    (hold : x.ms.st.pairCur (x.H.A.pairOf c) ≤ (x.H.A.pairConns (x.H.A.pairOf c)).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    (hmem : ∀ d ∈ x.H.A.pairConns (x.H.A.pairOf c), d < x.H.A.C.numConn) :
    let q := x.H.A.pairOf c
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ s.mem = mem0)
      delRefreshConnPair (normalPost fun s => s.regs 0 = b ∧ s.regs 39 = q ∧
        ListAt s.mem b (x.refreshPair q).encode ∧
        ∀ i, (i < b ∨ b + x.encode.length ≤ i) → s.mem i = mem0 i)
      (fun _ => 165 + (advance (x.H.A.pairValid (x.H.A.surv x.ms.st) q)
        (x.H.A.pairConns q).length (x.ms.st.pairCur q) - x.ms.st.pairCur q + 1) * 90) := by
  dsimp only
  let q := x.H.A.pairOf c
  let M := fun mem => ListAt mem b x.encode ∧ mem = mem0
  have hsec : x.sections.getD 5 [] = tabList x.H.A.C.numConn x.H.A.pairOf := rfl
  have hidx : c < (x.sections.getD 5 []).length := by rw [hsec]; simpa using hc
  have hqval : (x.sections.getD 5 [])[c] = q := by
    rw [← List.getD_eq_getElem _ 0 hidx, hsec]
    simp [tabList, List.getD_eq_getElem?_getD, hc, q]
  have hread : Triple w p (fun s => s.regs = R ∧ M s.mem)
      (.assign 39 (readSec numSec 0 5 (.reg 48)))
      (normalPost fun s => s.regs = Function.update R 39 q ∧ M s.mem)
      (fun _ => 14) := by
    refine (triple_assign_exact ?_).mono_cost (fun _ _ => by decide)
    intro s hr hm
    have h := eval_readSec (w := w) (show ListAt s.mem b (layoutList x.sections) from hm.1)
      hb (r := 0) (by rw [hr, h0]) (i := 5) (by rw [x.length_sections']; decide)
      (Expr.eval_reg_of_eq (r := 48) (by rw [hr, h48])) hidx
    rwa [x.length_sections', hqval] at h
  exact (Triple.seq_normal_const hread
    (delPairRefresh_triple x (by simpa using h0) (by simp [q]) hq hb hN hold hinel hmem)).mono_cost
    (fun _ _ => by omega)

/-- The pair refresh pass over the connector list at register 49, of length in register 50. -/
def delPairPass : Stmt :=
  forRange 51 (.const 0) (.reg 50)
    (.seq (.assign 48 (.load (.bin .add (.reg 49) (.reg 51)))) delRefreshConnPair)

theorem delPairPass_noRand : delPairPass.NoRand := by
  simp [delPairPass, forRange, forUp, Stmt.NoRand, delRefreshConnPair_noRand]

/-- Apply the pair refresh to the connectors in the given order. -/
def HierConcrete.refreshPairs (x : HierConcrete) (cs : List ℕ) : HierConcrete :=
  cs.foldl (fun y c => y.refreshPair (x.H.A.pairOf c)) x

theorem HierConcrete.refreshPairs_append_one (x : HierConcrete) (cs : List ℕ) (c : ℕ) :
    x.refreshPairs (cs ++ [c]) = (x.refreshPairs cs).refreshPair (x.H.A.pairOf c) := by
  simp [refreshPairs, List.foldl_append]

theorem HierConcrete.length_encode_refreshPair (x : HierConcrete) (q : ℕ) :
    (x.refreshPair q).encode.length = x.encode.length := by
  show (layoutList (x.refreshPair q).sections).length = (layoutList x.sections).length
  unfold refreshPair
  rw [x.sections_setPairCur]
  exact length_layoutList_set _ (List.length_set ..)

theorem HierConcrete.length_encode_refreshPairs (x : HierConcrete) (cs : List ℕ) :
    (x.refreshPairs cs).encode.length = x.encode.length := by
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton cs c ih =>
    rw [x.refreshPairs_append_one, HierConcrete.length_encode_refreshPair, ih]

theorem HierConcrete.refreshPairs_data (x : HierConcrete) (cs : List ℕ) :
    (x.refreshPairs cs).H = x.H ∧ (x.refreshPairs cs).ms.st.loss = x.ms.st.loss ∧
      (x.refreshPairs cs).ms.st.inelig = x.ms.st.inelig := by
  induction cs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | append_singleton cs c ih =>
    rw [x.refreshPairs_append_one]
    exact ih

theorem HierConcrete.refreshPairs_cur_le (x : HierConcrete) (cs : List ℕ)
    (h : ∀ q, x.ms.st.pairCur q ≤ (x.H.A.pairConns q).length) :
    ∀ q, (x.refreshPairs cs).ms.st.pairCur q ≤ (x.H.A.pairConns q).length := by
  induction cs using List.reverseRecOn with
  | nil => exact h
  | append_singleton cs c ih =>
    intro q
    rw [x.refreshPairs_append_one]
    let y := x.refreshPairs cs
    change Function.update y.ms.st.pairCur (x.H.A.pairOf c) _ q ≤ _
    by_cases hq : q = x.H.A.pairOf c
    · subst q
      rw [Function.update_self]
      have he : y.H = x.H := (x.refreshPairs_data cs).1
      exact (advance_le _ (by rw [he]; exact ih _)).trans_eq (by rw [he])
    · rw [Function.update_of_ne hq]
      exact ih q

/-- Pair pass invariant after `i` connectors. -/
def DelPairPassInv (x : HierConcrete) (b base : ℕ) (cs : List ℕ) (mem0 : ℕ → ℕ)
    (i : ℕ) (s : State) : Prop :=
  s.regs 0 = b ∧ s.regs 49 = base ∧ s.regs 50 = cs.length ∧ s.regs 51 = i ∧
  ListAt s.mem b (x.refreshPairs (cs.take i)).encode ∧ ListAt s.mem base cs ∧
  ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j

/-- Cost of the indexed pair refresh using the cursor after its preceding visits. -/
def delPairPassStepCost (x : HierConcrete) (cs : List ℕ) (i : ℕ) : ℕ :=
  let q := x.H.A.pairOf (cs.getD i 0)
  let old := (x.refreshPairs (cs.take i)).ms.st.pairCur q
  171 + (advance (x.H.A.pairValid (x.H.A.surv x.ms.st) q)
    (x.H.A.pairConns q).length old - old + 1) * 90

/-- Refresh the pair of one work-list entry and preserve the list. -/
theorem delPairPassBody_triple {w : ℕ} {p : Program} (x : HierConcrete) {b base i : ℕ}
    {cs : List ℕ} {mem0 : ℕ → ℕ}
    (hb : b + x.encode.length ≤ base) (hw : base + cs.length < 2 ^ w)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numConn)
    (hq : ∀ c ∈ cs, x.H.A.pairOf c < x.H.A.numPairs)
    (hN : ∀ q < x.H.A.numPairs, (x.H.A.pairConns q).length + 1 < 2 ^ w)
    (hcur : ∀ q, x.ms.st.pairCur q ≤ (x.H.A.pairConns q).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    (hmem : ∀ q < x.H.A.numPairs, ∀ d ∈ x.H.A.pairConns q, d < x.H.A.C.numConn)
    (hi : i < cs.length) :
    Triple w p (DelPairPassInv x b base cs mem0 i)
      (.seq (.assign 48 (.load (.bin .add (.reg 49) (.reg 51)))) delRefreshConnPair)
      (normalPost fun s => DelPairPassInv x b base cs mem0 (i + 1)
        { s with regs := Function.update s.regs 51 (i + 1) } ∧ s.regs 51 = i)
      (fun _ => delPairPassStepCost x cs i) := by
  let c := cs[i]
  let y := x.refreshPairs (cs.take i)
  let q := x.H.A.pairOf c
  have hcm : c ∈ cs := List.getElem_mem hi
  have hq' := hq c hcm
  obtain ⟨hH, hLoss, hIn⟩ := x.refreshPairs_data (cs.take i)
  have hSurv : y.H.A.surv y.ms.st = x.H.A.surv x.ms.st := by
    simp only [StaticArrays.surv, y, hH, hLoss]
  have hlen : y.encode.length = x.encode.length := x.length_encode_refreshPairs _
  have hyb : b + y.encode.length < 2 ^ w := by rw [hlen]; omega
  have hyn : (y.H.A.pairConns (y.H.A.pairOf c)).length + 1 < 2 ^ w := by
    rw [hH]; exact hN q hq'
  have hyc : y.ms.st.pairCur (y.H.A.pairOf c) ≤ (y.H.A.pairConns (y.H.A.pairOf c)).length := by
    rw [hH]; exact x.refreshPairs_cur_le _ hcur q
  have hyI : y.ms.st.inelig = (Finset.range y.H.A.C.numConn).filter fun d =>
      ¬ y.H.A.C.Eligible (y.H.A.surv y.ms.st) d := by
    rw [hIn, hSurv, hH]; exact hinel
  have hnext : x.refreshPairs (cs.take (i + 1)) = y.refreshPair (y.H.A.pairOf c) := by
    rw [List.take_succ_eq_append_getElem hi, x.refreshPairs_append_one, hH]
  intro s ω hs
  obtain ⟨h0, h49, h50, h51, hy, hl, hf⟩ := hs
  let R := Function.update s.regs 48 c
  let M := fun mem => ListAt mem b y.encode ∧ mem = s.mem
  have hread : Triple w p (fun st => st.regs = s.regs ∧ M st.mem)
      (.assign 48 (.load (.bin .add (.reg 49) (.reg 51))))
      (normalPost fun st => st.regs = R ∧ M st.mem)
      (fun _ => 5) := by
    exact triple_assign_exact fun st hr hm =>
      Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_reg_of_eq (hr ▸ h49)) (Expr.eval_reg_of_eq (hr ▸ h51)) (by omega))
        (by rw [hm.2]; exact hl i hi)
  have H := delRefreshConnPair_triple (w := w) (p := p) (mem0 := s.mem) (R := R) y
    (by simpa [R] using h0) (by simp [R]) (by rw [hH]; exact hc c hcm)
    hyb (by rw [hH]; exact hq') hyn hyc hyI (by rw [hH]; exact hmem q hq')
  have Hfr := Triple.regs_frame delRefreshConnPair_writesBelow H s.regs
  have htail := Hfr.weaken_pre (P' := fun st => st.regs = R ∧ M st.mem) (fun st hs =>
    ⟨⟨hs.1, hs.2.1, hs.2.2⟩, fun r hr => by rw [hs.1]; simp [R, Function.update_of_ne
      (show r ≠ 48 by omega)]⟩)
  have HT := Triple.seq_normal_const hread htail
  obtain ⟨o, s', cost, hrun, ⟨hpost, hregs⟩, hk⟩ := HT s ω ⟨rfl, hy, rfl⟩
  cases o <;> try contradiction
  obtain ⟨h0', _, hblock, hframe⟩ := hpost
  have hf' : ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s'.mem j = s.mem j := by
    simpa only [hlen] using hframe
  refine ⟨_, s', cost, hrun, ?_, ?_⟩
  · refine ⟨⟨by simpa using h0', by simpa using (hregs 49 (by decide)).trans h49,
      by simpa using (hregs 50 (by decide)).trans h50, by simp, hnext ▸ hblock,
      listAt_congr (fun j hj => (hf' _ (Or.inr (by omega))).symm) hl,
      fun j hj => (hf' j hj).trans (hf j hj)⟩, (hregs 51 (by decide)).trans h51⟩
  · unfold delPairPassStepCost
    rw [List.getD_eq_getElem _ _ hi]
    have he : y.H = x.H := hH
    dsimp only at hk ⊢
    rw [hSurv, he] at hk
    simp only [c, y] at hk
    omega

/-- The pair pass refreshes each listed pair and preserves all memory outside the block. -/
theorem delPairPass_triple {w : ℕ} {p : Program} (x : HierConcrete) {b base : ℕ}
    {cs : List ℕ} {mem0 R : ℕ → ℕ}
    (h0 : R 0 = b) (h49 : R 49 = base) (h50 : R 50 = cs.length)
    (hb : b + x.encode.length ≤ base) (hw : base + cs.length < 2 ^ w)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numConn)
    (hq : ∀ c ∈ cs, x.H.A.pairOf c < x.H.A.numPairs)
    (hN : ∀ q < x.H.A.numPairs, (x.H.A.pairConns q).length + 1 < 2 ^ w)
    (hcur : ∀ q, x.ms.st.pairCur q ≤ (x.H.A.pairConns q).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    (hmem : ∀ q < x.H.A.numPairs, ∀ d ∈ x.H.A.pairConns q, d < x.H.A.C.numConn) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base cs ∧ s.mem = mem0) delPairPass
      (normalPost fun s => s.regs 0 = b ∧
        ListAt s.mem b (x.refreshPairs cs).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun _ => rangeCost (delPairPassStepCost x cs) 0 cs.length + cs.length * 9 + 7) := by
  have hone : 1 < 2 ^ w := by have := x.le_length_encode; omega
  have H := Triple.forRange_le (w := w) (p := p) (r := 51) (lo := .const 0)
    (hi := .reg 50) (Inv := DelPairPassInv x b base cs mem0)
    (delPairPassStepCost x cs) 0 cs.length (Nat.zero_le _) hone (fun _ => by omega)
    (P := fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem base cs ∧ s.mem = mem0)
    (fun s hs => ⟨Expr.eval_const (by omega), ?_⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
    (fun _ _ hi => delPairPassBody_triple x hb hw hc hq hN hcur hinel hmem hi)
  · refine (H.strengthen_post fun o s h => ?_).mono_cost (fun _ _ => by simp [Expr.size])
    cases o <;> try contradiction
    change DelPairPassInv x b base cs mem0 cs.length s at h
    simp only [DelPairPassInv, List.take_length] at h
    obtain ⟨hr, _, _, _, hblock, _, hf⟩ := h
    exact ⟨hr, hblock, hf⟩
  · obtain ⟨hr, hblock, hl, hm⟩ := hs
    refine ⟨?_, ?_, ?_, by simp, ?_, hl, fun j _ => congrFun hm j⟩
    · simpa [hr] using h0
    · simpa [hr] using h49
    · simpa [hr] using h50
    · exact hblock

/-- The concrete pair pass is the model cursor refresh over the mapped work list. -/
theorem HierConcrete.refreshPairs_eq (x : HierConcrete) (cs : List ℕ) :
    (x.refreshPairs cs).ms.st.pairCur =
      refreshAll (fun q => x.H.A.pairValid (x.H.A.surv x.ms.st) q)
        (fun q => (x.H.A.pairConns q).length) x.ms.st.pairCur (cs.map x.H.A.pairOf) := by
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton cs c ih =>
    rw [x.refreshPairs_append_one, List.map_append]
    simp only [refreshAll, List.foldl_append, List.map_singleton, List.foldl_cons, List.foldl_nil] at ih ⊢
    obtain ⟨hH, hLoss, _⟩ := x.refreshPairs_data cs
    have hSurv : (x.refreshPairs cs).H.A.surv (x.refreshPairs cs).ms.st =
        x.H.A.surv x.ms.st := by simp only [StaticArrays.surv, hH, hLoss]
    change Function.update (x.refreshPairs cs).ms.st.pairCur (x.H.A.pairOf c)
      (advance ((x.refreshPairs cs).H.A.pairValid
        ((x.refreshPairs cs).H.A.surv (x.refreshPairs cs).ms.st) (x.H.A.pairOf c))
        ((x.refreshPairs cs).H.A.pairConns (x.H.A.pairOf c)).length
        ((x.refreshPairs cs).ms.st.pairCur (x.H.A.pairOf c))) = _
    rw [hSurv, hH, ih]

end MinCostFlow.HierPaths

end
