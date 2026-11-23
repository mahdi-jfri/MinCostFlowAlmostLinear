module

public import MinCostFlow.HierPaths.DelProgOwnerRefresh
public import MinCostFlow.HierPaths.DelProgOrder

/-!
# Refreshing the support cursors of terminal owners

The pass visits every newly lost terminal and refreshes its owner's cursor. Repeated visits
are allowed because a refresh skips only entries that have become invalid.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The support refresh pass over the lost terminal list at register 49, of length in register 50. -/
def delOwnerPass : Stmt :=
  forRange 51 (.const 0) (.reg 50)
    (.seq (.assign 48 (.load (.bin .add (.reg 49) (.reg 51)))) delRefreshOwner)

theorem delOwnerPass_noRand : delOwnerPass.NoRand := by
  simp [delOwnerPass, forRange, forUp, Stmt.NoRand, delRefreshOwner_noRand]

/-- Apply the support refresh to the terminal owners in the given order. -/
def HierConcrete.refreshOwners (x : HierConcrete) (cs : List ℕ) : HierConcrete :=
  cs.foldl (fun y c => y.refreshSup (x.H.A.C.owner c)) x

theorem HierConcrete.refreshOwners_append_one (x : HierConcrete) (cs : List ℕ) (c : ℕ) :
    x.refreshOwners (cs ++ [c]) = (x.refreshOwners cs).refreshSup (x.H.A.C.owner c) := by
  simp [refreshOwners, List.foldl_append]

theorem HierConcrete.length_encode_refreshSup (x : HierConcrete) (q : ℕ) :
    (x.refreshSup q).encode.length = x.encode.length := by
  show (layoutList (x.refreshSup q).sections).length = (layoutList x.sections).length
  unfold refreshSup
  rw [x.sections_setSupCur]
  exact length_layoutList_set _ (List.length_set ..)

theorem HierConcrete.length_encode_refreshOwners (x : HierConcrete) (cs : List ℕ) :
    (x.refreshOwners cs).encode.length = x.encode.length := by
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton cs c ih =>
    rw [x.refreshOwners_append_one, HierConcrete.length_encode_refreshSup, ih]

theorem HierConcrete.refreshOwners_data (x : HierConcrete) (cs : List ℕ) :
    (x.refreshOwners cs).H = x.H ∧ (x.refreshOwners cs).ms.st.loss = x.ms.st.loss ∧
      (x.refreshOwners cs).ms.st.inelig = x.ms.st.inelig := by
  induction cs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | append_singleton cs c ih =>
    rw [x.refreshOwners_append_one]
    exact ih

theorem HierConcrete.refreshOwners_n (x : HierConcrete) (ts : List ℕ) :
    (x.refreshOwners ts).n = x.n := by
  induction ts using List.reverseRecOn with
  | nil => rfl
  | append_singleton ts t ih =>
    rw [x.refreshOwners_append_one]
    exact ih

theorem HierConcrete.refreshOwners_cur_le (x : HierConcrete) (cs : List ℕ)
    (h : ∀ q, x.ms.st.supCur q ≤ (x.H.A.C.supportArray q).length) :
    ∀ q, (x.refreshOwners cs).ms.st.supCur q ≤ (x.H.A.C.supportArray q).length := by
  induction cs using List.reverseRecOn with
  | nil => exact h
  | append_singleton cs c ih =>
    intro q
    rw [x.refreshOwners_append_one]
    let y := x.refreshOwners cs
    change Function.update y.ms.st.supCur (x.H.A.C.owner c) _ q ≤ _
    by_cases hq : q = x.H.A.C.owner c
    · subst q
      rw [Function.update_self]
      have he : y.H = x.H := (x.refreshOwners_data cs).1
      exact (advance_le _ (by rw [he]; exact ih _)).trans_eq (by rw [he])
    · rw [Function.update_of_ne hq]
      exact ih q

/-- Owner pass invariant after `i` terminals. -/
def DelOwnerPassInv (x : HierConcrete) (b base : ℕ) (cs : List ℕ) (mem0 : ℕ → ℕ)
    (i : ℕ) (s : State) : Prop :=
  s.regs 0 = b ∧ s.regs 49 = base ∧ s.regs 50 = cs.length ∧ s.regs 51 = i ∧
  ListAt s.mem b (x.refreshOwners (cs.take i)).encode ∧ ListAt s.mem base cs ∧
  ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j

/-- Cost of the indexed support refresh using the cursor after its preceding visits. -/
def delOwnerPassStepCost (x : HierConcrete) (cs : List ℕ) (i : ℕ) : ℕ :=
  let q := x.H.A.C.owner (cs.getD i 0)
  let old := (x.refreshOwners (cs.take i)).ms.st.supCur q
  171 + (advance (x.H.A.supValid (x.H.A.surv x.ms.st) q)
    (x.H.A.C.supportArray q).length old - old + 1) * 280

/-- Refresh the owner of one work-list entry and preserve the list. -/
theorem delOwnerPassBody_triple {w : ℕ} {p : Program} (x : HierConcrete) {b base i : ℕ}
    {cs : List ℕ} {mem0 : ℕ → ℕ}
    (hb : b + x.encode.length ≤ base) (hw : base + cs.length < 2 ^ w)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numTerm)
    (hq : ∀ c ∈ cs, x.H.A.C.owner c < x.n)
    (hN : ∀ q < x.n, (x.H.A.C.supportArray q).length + 1 < 2 ^ w)
    (hcur : ∀ q, x.ms.st.supCur q ≤ (x.H.A.C.supportArray q).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    (hi : i < cs.length) :
    Triple w p (DelOwnerPassInv x b base cs mem0 i)
      (.seq (.assign 48 (.load (.bin .add (.reg 49) (.reg 51)))) delRefreshOwner)
      (normalPost fun s => DelOwnerPassInv x b base cs mem0 (i + 1)
        { s with regs := Function.update s.regs 51 (i + 1) } ∧ s.regs 51 = i)
      (fun _ => delOwnerPassStepCost x cs i) := by
  let c := cs[i]
  let y := x.refreshOwners (cs.take i)
  let q := x.H.A.C.owner c
  have hcm : c ∈ cs := List.getElem_mem hi
  have hq' := hq c hcm
  obtain ⟨hH, hLoss, hIn⟩ := x.refreshOwners_data (cs.take i)
  have hSurv : y.H.A.surv y.ms.st = x.H.A.surv x.ms.st := by
    simp only [StaticArrays.surv, y, hH, hLoss]
  have hlen : y.encode.length = x.encode.length := x.length_encode_refreshOwners _
  have hyb : b + y.encode.length < 2 ^ w := by rw [hlen]; omega
  have hyn : (y.H.A.C.supportArray (y.H.A.C.owner c)).length + 1 < 2 ^ w := by
    rw [hH]; exact hN q hq'
  have hyc : y.ms.st.supCur (y.H.A.C.owner c) ≤ (y.H.A.C.supportArray (y.H.A.C.owner c)).length := by
    rw [hH]; exact x.refreshOwners_cur_le _ hcur q
  have hyI : y.ms.st.inelig = (Finset.range y.H.A.C.numConn).filter fun d =>
      ¬ y.H.A.C.Eligible (y.H.A.surv y.ms.st) d := by
    rw [hIn, hSurv, hH]; exact hinel
  have hnext : x.refreshOwners (cs.take (i + 1)) = y.refreshSup (y.H.A.C.owner c) := by
    rw [List.take_succ_eq_append_getElem hi, x.refreshOwners_append_one, hH]
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
  have H := delRefreshOwner_triple (w := w) (p := p) (mem0 := s.mem) (R := R) y
    (by simpa [R] using h0) (by simp [R]) (by rw [hH]; exact hc c hcm)
    hyb (by rw [hH]; exact (x.refreshOwners_n _).symm ▸ hq') hyn hyc hyI
  have Hfr := Triple.regs_frame delRefreshOwner_writesBelow H s.regs
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
  · unfold delOwnerPassStepCost
    rw [List.getD_eq_getElem _ _ hi]
    have he : y.H = x.H := hH
    dsimp only at hk ⊢
    rw [hSurv, he] at hk
    simp only [c, y] at hk
    omega

/-- The owner pass refreshes each listed terminal owner and preserves all memory outside the block. -/
theorem delOwnerPass_triple {w : ℕ} {p : Program} (x : HierConcrete) {b base : ℕ}
    {cs : List ℕ} {mem0 R : ℕ → ℕ}
    (h0 : R 0 = b) (h49 : R 49 = base) (h50 : R 50 = cs.length)
    (hb : b + x.encode.length ≤ base) (hw : base + cs.length < 2 ^ w)
    (hc : ∀ c ∈ cs, c < x.H.A.C.numTerm)
    (hq : ∀ c ∈ cs, x.H.A.C.owner c < x.n)
    (hN : ∀ q < x.n, (x.H.A.C.supportArray q).length + 1 < 2 ^ w)
    (hcur : ∀ q, x.ms.st.supCur q ≤ (x.H.A.C.supportArray q).length)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun d =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) d)
    :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base cs ∧ s.mem = mem0) delOwnerPass
      (normalPost fun s => s.regs 0 = b ∧
        ListAt s.mem b (x.refreshOwners cs).encode ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) → s.mem j = mem0 j)
      (fun _ => rangeCost (delOwnerPassStepCost x cs) 0 cs.length + cs.length * 9 + 7) := by
  have hone : 1 < 2 ^ w := by have := x.le_length_encode; omega
  have H := Triple.forRange_le (w := w) (p := p) (r := 51) (lo := .const 0)
    (hi := .reg 50) (Inv := DelOwnerPassInv x b base cs mem0)
    (delOwnerPassStepCost x cs) 0 cs.length (Nat.zero_le _) hone (fun _ => by omega)
    (P := fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧ ListAt s.mem base cs ∧ s.mem = mem0)
    (fun s hs => ⟨Expr.eval_const (by omega), ?_⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
    (fun _ _ hi => delOwnerPassBody_triple x hb hw hc hq hN hcur hinel hi)
  · refine (H.strengthen_post fun o s h => ?_).mono_cost (fun _ _ => by simp [Expr.size])
    cases o <;> try contradiction
    change DelOwnerPassInv x b base cs mem0 cs.length s at h
    simp only [DelOwnerPassInv, List.take_length] at h
    obtain ⟨hr, _, _, _, hblock, _, hf⟩ := h
    exact ⟨hr, hblock, hf⟩
  · obtain ⟨hr, hblock, hl, hm⟩ := hs
    refine ⟨?_, ?_, ?_, by simp, ?_, hl, fun j _ => congrFun hm j⟩
    · simpa [hr] using h0
    · simpa [hr] using h49
    · simpa [hr] using h50
    · exact hblock

/-- The concrete owner pass is the model cursor refresh over the mapped work list. -/
theorem HierConcrete.refreshOwners_eq (x : HierConcrete) (cs : List ℕ) :
    (x.refreshOwners cs).ms.st.supCur =
      refreshAll (fun q => x.H.A.supValid (x.H.A.surv x.ms.st) q)
        (fun q => (x.H.A.C.supportArray q).length) x.ms.st.supCur (cs.map x.H.A.C.owner) := by
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton cs c ih =>
    rw [x.refreshOwners_append_one, List.map_append]
    simp only [refreshAll, List.foldl_append, List.map_singleton, List.foldl_cons, List.foldl_nil] at ih ⊢
    obtain ⟨hH, hLoss, _⟩ := x.refreshOwners_data cs
    have hSurv : (x.refreshOwners cs).H.A.surv (x.refreshOwners cs).ms.st =
        x.H.A.surv x.ms.st := by simp only [StaticArrays.surv, hH, hLoss]
    change Function.update (x.refreshOwners cs).ms.st.supCur (x.H.A.C.owner c)
      (advance ((x.refreshOwners cs).H.A.supValid
        ((x.refreshOwners cs).H.A.surv (x.refreshOwners cs).ms.st) (x.H.A.C.owner c))
        ((x.refreshOwners cs).H.A.C.supportArray (x.H.A.C.owner c)).length
        ((x.refreshOwners cs).ms.st.supCur (x.H.A.C.owner c))) = _
    rw [hSurv, hH, ih]

end MinCostFlow.HierPaths

end
