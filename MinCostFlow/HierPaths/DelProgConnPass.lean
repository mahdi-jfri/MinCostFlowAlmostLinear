module

public import MinCostFlow.HierPaths.DelProgConnLoop
public import MinCostFlow.HierPaths.DelProgRegFrame

/-!
# Scanning the lost-terminal work list

The outer scan reads each newly lost terminal and runs its incident-list scan. The connector
work list accumulates the first visits across all of those lists.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Read the current lost terminal and scan its incident connectors. -/
def delLostConnBody : Stmt :=
  .seq (.assign 28 (.load (.bin .add (.reg 36) (.reg 38)))) delTerminalConns

/-- Register 36 holds the lost list base, and register 37 holds its length. -/
def delLostConnPass : Stmt := forRange 38 (.const 0) (.reg 37) delLostConnBody

theorem delLostConnPass_noRand : delLostConnPass.NoRand := by
  simp [delLostConnPass, forRange, forUp, delLostConnBody, Stmt.NoRand,
    delTerminalConns_noRand]

theorem delTerminalConns_writesBelow : Stmt.WritesBelow 36 delTerminalConns := by
  simp [delTerminalConns, delTermSetup, delCsrSetup, delIncidentLoop, forRange, forUp,
    delConnAt, delConnVisit, delIneligBit, delConnPush, Stmt.WritesBelow]

theorem HierConcrete.markIneligList_append (x : HierConcrete) (cs ds : List ℕ) :
    x.markIneligList (cs ++ ds) = (x.markIneligList cs).markIneligList ds := by
  simp [markIneligList, withSt, List.toFinset_append, Finset.union_assoc]

/-- The outer-loop state after the first `i` terminals have been scanned. -/
def DelLostConnInv (x : HierConcrete) (b base lostBase : ℕ) (lost : List ℕ)
    (mem0 : ℕ → ℕ) (i : ℕ) (s : State) : Prop :=
  let visited := (lost.take i).flatMap x.H.A.termConns
  let out := delCollect x.ms.st.inelig visited
  s.regs 0 = b ∧ s.regs 33 = base ∧ s.regs 34 = out.length ∧
  s.regs 36 = lostBase ∧ s.regs 37 = lost.length ∧ s.regs 38 = i ∧
  ListAt s.mem b (x.markIneligList visited).encode ∧ ListAt s.mem base out ∧
  ListAt s.mem lostBase lost ∧
  ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
    (j < base ∨ base + out.length ≤ j) → s.mem j = mem0 j

/-- A range scan over the indices of a list sums the costs of its entries. -/
theorem delRangeCost_list (f : ℕ → ℕ) (l : List ℕ) :
    rangeCost (fun i => f (l.getD i 0)) 0 l.length = (l.map f).sum := by
  unfold rangeCost
  rw [Nat.sub_zero, ← List.range_eq_range']
  congr 1
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  have hi : i < l.length := by simpa using h₂
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ hi]

/-- Charge a terminal for its own incidence list. -/
def delLostConnStepCost (x : HierConcrete) (lost : List ℕ) (i : ℕ) : ℕ :=
  99 * (x.H.A.termConns (lost.getD i 0)).length + 95

private theorem delLostConnStepCost_sum (x : HierConcrete) (lost : List ℕ) :
    rangeCost (delLostConnStepCost x lost) 0 lost.length =
      99 * (lost.flatMap x.H.A.termConns).length + 95 * lost.length := by
  unfold delLostConnStepCost
  rw [delRangeCost_list (fun t => 99 * (x.H.A.termConns t).length + 95) lost]
  induction lost with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append,
      List.length_cons, ih, Nat.mul_add]
    omega

/-- Process one lost terminal while keeping the lost-terminal list intact. -/
theorem delLostConnBody_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base lostBase i : ℕ} {lost : List ℕ} {mem0 : ℕ → ℕ}
    (ht : ∀ t ∈ lost, t < x.H.A.C.numTerm)
    (hcs : ∀ t ∈ lost, ∀ c ∈ x.H.A.termConns t, c < x.H.A.C.numConn)
    (hb : b + x.encode.length ≤ base)
    (hfLost : ∀ j < lost.length, lostBase + j < b ∨ b + x.encode.length ≤ lostBase + j)
    (hsep : lostBase + lost.length ≤ base ∨
      base + (lost.flatMap x.H.A.termConns).length ≤ lostBase)
    (hw : base + (lost.flatMap x.H.A.termConns).length < 2 ^ w)
    (hlw : lostBase + lost.length < 2 ^ w)
    (hi : i < lost.length) :
    Triple w p (DelLostConnInv x b base lostBase lost mem0 i) delLostConnBody
      (normalPost fun s => DelLostConnInv x b base lostBase lost mem0 (i + 1)
        { s with regs := Function.update s.regs 38 (i + 1) } ∧ s.regs 38 = i)
      (fun _ => delLostConnStepCost x lost i) := by
  let t := lost[i]
  let visited := (lost.take i).flatMap x.H.A.termConns
  let cs := x.H.A.termConns t
  let mid := x.markIneligList visited
  let out := delCollect x.ms.st.inelig visited
  let out' := out ++ delCollect mid.ms.st.inelig cs
  have hvisit : (lost.take (i + 1)).flatMap x.H.A.termConns = visited ++ cs := by
    rw [List.take_succ_eq_append_getElem hi, List.flatMap_append]
    simp [visited, cs, t]
  have hblock : x.markIneligList ((lost.take (i + 1)).flatMap x.H.A.termConns) =
      mid.markIneligList cs := by rw [hvisit, x.markIneligList_append]
  have hout : delCollect x.ms.st.inelig ((lost.take (i + 1)).flatMap x.H.A.termConns) =
      out' := by rw [hvisit, delCollect_append]; rfl
  have hmidlen : mid.encode.length = x.encode.length := x.length_encode_markIneligList _
  have htotal : visited.length + cs.length ≤ (lost.flatMap x.H.A.termConns).length := by
    rw [← List.length_append, ← hvisit]
    exact ((List.take_sublist _ _).flatMap _).length_le
  have hbefore := delCollect_length_le x.ms.st.inelig visited
  have hafter : out'.length ≤ (lost.flatMap x.H.A.termConns).length := by
    have h := delCollect_length_le mid.ms.st.inelig cs
    simp only [out', List.length_append]
    change out.length ≤ visited.length at hbefore
    omega
  have hgrow : out.length ≤ out'.length := by simp [out']
  have htm : t ∈ lost := List.getElem_mem hi
  intro s ω hs
  change s.regs 0 = b ∧ s.regs 33 = base ∧ s.regs 34 = out.length ∧
    s.regs 36 = lostBase ∧ s.regs 37 = lost.length ∧ s.regs 38 = i ∧
    ListAt s.mem b mid.encode ∧ ListAt s.mem base out ∧ ListAt s.mem lostBase lost ∧ _ at hs
  obtain ⟨h0, h33, h34, h36, h37, h38, hmem, hlist, hlost, hf⟩ := hs
  change out.length ≤ visited.length at hbefore
  let R := Function.update s.regs 28 t
  let M := fun mem => mem = s.mem
  have hread : Triple w p (fun st => st.regs = s.regs ∧ M st.mem)
      (.assign 28 (.load (.bin .add (.reg 36) (.reg 38))))
      (normalPost fun st => st.regs = R ∧ M st.mem)
      (fun _ => 5) := by
    exact triple_assign_exact fun st hr hm =>
      Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_reg_of_eq (hr ▸ h36)) (Expr.eval_reg_of_eq (hr ▸ h38)) (by omega))
        (by rw [show st.mem = s.mem from hm]; exact hlost i hi)
  have hfit : base + out.length + cs.length < 2 ^ w := by omega
  have H := (delTerminalConns_triple (w := w) (p := p) (R := R) (mem0 := s.mem)
    (L := out) mid (by simpa [R] using h0) (by simp [R]) (by simpa [R] using h33)
    (by simpa [R] using h34) (ht t htm) (hcs t htm) (by rwa [hmidlen]) hfit)
  have Hframe := Triple.regs_frame delTerminalConns_writesBelow H s.regs
  have hstep : Triple w p (fun st => st.regs = R ∧ M st.mem) delTerminalConns
      (normalPost fun st => DelLostConnInv x b base lostBase lost mem0 (i + 1)
        { st with regs := Function.update st.regs 38 (i + 1) } ∧ st.regs 38 = i)
      (fun _ => 99 * cs.length + 88) := by
    intro st ω' ⟨hr, hm⟩
    obtain ⟨o, s', k, hrun, ⟨hp, hreg⟩, hk⟩ := Hframe st ω'
      ⟨⟨hr, hm.symm ▸ hmem, hm.symm ▸ hlist, hm⟩,
        fun r h => by rw [hr]; simp [R, Function.update_of_ne (show r ≠ 28 by omega)]⟩
    cases o <;> try contradiction
    obtain ⟨h0', h33', h34', hmem', hlist', hf'⟩ := hp
    change s'.regs 34 = out'.length at h34'
    change ∀ j, (j < b ∨ b + mid.encode.length ≤ j) →
      (j < base + out.length ∨ base + out'.length ≤ j) → s'.mem j = s.mem j at hf'
    change ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
      (j < base ∨ base + out.length ≤ j) → s.mem j = mem0 j at hf
    refine ⟨_, s', k, hrun, ?_, hk⟩
    change DelLostConnInv x b base lostBase lost mem0 (i + 1) _ ∧ _
    simp only [DelLostConnInv, hblock, hout]
    refine ⟨⟨by simpa using h0', by simpa using h33', by simpa using h34',
      ?_, ?_, by simp, hmem', hlist', ?_, ?_⟩, (hreg 38 (by decide)).trans h38⟩
    · simpa using (hreg 36 (by decide)).trans h36
    · simpa using (hreg 37 (by decide)).trans h37
    · refine listAt_congr (fun j hj => ?_) hlost
      symm
      apply hf'
      · rw [hmidlen]
        have hleft : lostBase + j < b ∨ b + x.encode.length ≤ lostBase + j :=
          hfLost j hj
        exact hleft
      · rcases hsep with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
    · intro j hj he
      change j < base ∨ base + out'.length ≤ j at he
      have hj' : j < b ∨ b + mid.encode.length ≤ j := by rwa [hmidlen]
      rw [hf' j hj' (by omega)]
      exact hf j hj (by omega)
  have hrun := (Triple.seq_normal_const hread hstep).mono_cost
    (T' := fun _ => delLostConnStepCost x lost i) (fun _ _ => by
      unfold delLostConnStepCost
      rw [List.getD_eq_getElem _ _ hi]
      change 5 + (99 * cs.length + 88) + 1 ≤ 99 * cs.length + 95
      omega)
  exact hrun s ω ⟨rfl, rfl⟩

/-- Scan all newly lost terminals in time linear in the number of visited records. -/
theorem delLostConnPass_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base lostBase : ℕ} {lost : List ℕ} {mem0 R : ℕ → ℕ}
    (h0 : R 0 = b) (h33 : R 33 = base) (h34 : R 34 = 0)
    (h36 : R 36 = lostBase) (h37 : R 37 = lost.length)
    (ht : ∀ t ∈ lost, t < x.H.A.C.numTerm)
    (hcs : ∀ t ∈ lost, ∀ c ∈ x.H.A.termConns t, c < x.H.A.C.numConn)
    (hb : b + x.encode.length ≤ base)
    (hfLost : ∀ j < lost.length, lostBase + j < b ∨ b + x.encode.length ≤ lostBase + j)
    (hsep : lostBase + lost.length ≤ base ∨
      base + (lost.flatMap x.H.A.termConns).length ≤ lostBase)
    (hw : base + (lost.flatMap x.H.A.termConns).length < 2 ^ w)
    (hlw : lostBase + lost.length < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem lostBase lost ∧ s.mem = mem0) delLostConnPass
      (normalPost fun s =>
        let cs := lost.flatMap x.H.A.termConns
        let out := delCollect x.ms.st.inelig cs
        s.regs 0 = b ∧ s.regs 33 = base ∧ s.regs 34 = out.length ∧
        s.regs 36 = lostBase ∧ s.regs 37 = lost.length ∧
        ListAt s.mem b (x.markIneligList cs).encode ∧ ListAt s.mem base out ∧
        ListAt s.mem lostBase lost ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < base ∨ base + out.length ≤ j) → s.mem j = mem0 j)
      (fun _ => 99 * (lost.flatMap x.H.A.termConns).length + 104 * lost.length + 7) := by
  have hone : 1 < 2 ^ w := by have := x.le_length_encode; omega
  have H := Triple.forRange_le (w := w) (p := p) (r := 38) (lo := .const 0)
    (hi := .reg 37) (body := delLostConnBody)
    (Inv := DelLostConnInv x b base lostBase lost mem0) (delLostConnStepCost x lost) 0
    lost.length (Nat.zero_le _) hone (fun _ => by omega)
    (P := fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem lostBase lost ∧ s.mem = mem0)
    (fun s hs => ⟨Expr.eval_const (by omega), ?_⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.2.2.1)
    (fun _ _ hi => delLostConnBody_triple x ht hcs hb hfLost hsep hw hlw hi)
  · refine (H.strengthen_post fun o s h => ?_).mono_cost fun _ _ => by
      simp only [Expr.size, Nat.sub_zero, delLostConnStepCost_sum]
      omega
    cases o <;> try contradiction
    change DelLostConnInv x b base lostBase lost mem0 lost.length s at h
    simp only [DelLostConnInv, List.take_length] at h
    obtain ⟨h0', h33', h34', h36', h37', _, hblock, hlist, htmp, hf⟩ := h
    exact ⟨h0', h33', h34', h36', h37', hblock, hlist, htmp, hf⟩
  · obtain ⟨hr, hblock, hlist, hm⟩ := hs
    simp only [DelLostConnInv, List.take_zero, List.flatMap_nil, delCollect, List.length_nil,
      x.markIneligList_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_, by simp, hblock, (fun _ h => by simp at h), hlist, ?_⟩
    · simpa [hr] using h0
    · simpa [hr] using h33
    · simpa [hr] using h34
    · simpa [hr] using h36
    · simpa [hr] using h37
    · intro j _ _; exact congrFun hm j

/-- The ineligible bits after the connector pass agree with the abstract deletion. -/
theorem delConnectorPass_inelig (x : HierConcrete) {ξ κ e : ℕ}
    (hA : x.H.A.Spec x.ms.abs.G ξ κ)
    (hinv : x.H.A.DelInv x.ms.abs.G x.ms.st) :
    let A := x.H.A
    let afterLoss := (x.markDeleted e).withLoss (A.newLoss x.ms.st e)
    let afterConns := afterLoss.markIneligList ((A.newLost x.ms.st e).flatMap A.termConns)
    afterConns.ms.st.inelig = (Finset.range A.C.numConn).filter fun c =>
      ¬ A.C.Eligible (A.surv afterConns.ms.st) c := by
  let A := x.H.A
  let cs := (A.newLost x.ms.st e).flatMap A.termConns
  have hs : x.ms.st.inelig ∪ cs.toFinset = x.ms.st.inelig ∪ (A.newInelig x.ms.st e).toFinset := by
    rw [← delCollect_newInelig]
    ext c
    simp only [Finset.mem_union, List.mem_toFinset, mem_delCollect]
    tauto
  change x.ms.st.inelig ∪ cs.toFinset = _
  rw [hs]
  exact (A.deleteState_inv hA hinv e).1.inelig_eq

end MinCostFlow.HierPaths

end
