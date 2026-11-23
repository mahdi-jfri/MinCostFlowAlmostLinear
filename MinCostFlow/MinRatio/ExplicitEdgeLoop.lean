module

public import MinCostFlow.MinRatio.ExplicitEdgeVisit
import WordRAM.Tactic

/-!
# Iterating over explicit edge records

Algorithm 2 (page 29) updates signed flow and its absolute-value
account. The route scan visits each row, calls the first-occurrence
update, and advances the heap by the amount returned by that call.
A parallel array supplies the already resolved record addresses.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Registers 0 through 5 hold route base, route length, address-array
base, multiplier address, limb count, and current heap. Register 6 is
the row index. -/
@[expose] def explicitEdgeLoopStep (visit : ℕ) : Stmt :=
  .call 5 visit [.reg 0, .reg 1, .reg 6,
    .load (.bin .add (.reg 2) (.reg 6)), .reg 3, .reg 4, .reg 5]

/-- Visit every row in increasing order. -/
@[expose] def explicitEdgeLoop (visit : ℕ) : Stmt :=
  forUp 6 (.reg 1) (explicitEdgeLoopStep visit)

/-- The explicit-edge loop has no random statements. -/
theorem explicitEdgeLoop_noRand (visit : ℕ) : (explicitEdgeLoop visit).NoRand := by
  simp [explicitEdgeLoop, explicitEdgeLoopStep, forUp, Stmt.NoRand]

/-- Registers and the parallel address array at a route prefix.
The memory assertion describes the records after the completed prefix. -/
@[expose] def explicitEdgeLoopInv (base addrBase a L : ℕ) (addresses : List ℕ)
    (records : ℕ → ℕ → (ℕ → ℕ) → Prop) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = base ∧ st.regs 1 = addresses.length ∧ st.regs 2 = addrBase ∧
  st.regs 3 = a ∧ st.regs 4 = L ∧ st.regs 6 = i ∧
  ListAt st.mem addrBase addresses ∧ records i (st.regs 5) st.mem

/-- The linked loop transports its record invariant one prefix at a
time. The premises state the placement, the precondition for the
concrete visit, and preservation of the record invariant by its postcondition. -/
theorem explicitEdgeLoop_triple {w h visit base addrBase a L : ℕ} {p : Program}
    (edges : List (ℕ × Bool)) (addresses : List ℕ) (values : ℕ → PathEdgeValue) (num : ℤ)
    (records : ℕ → ℕ → (ℕ → ℕ) → Prop)
    (hlen : addresses.length = edges.length)
    (hwords : base < 2 ^ w ∧ addrBase + addresses.length + 1 < 2 ^ w ∧ a < 2 ^ w ∧ L < 2 ^ w)
    (haddr : ∀ x ∈ addresses, x < 2 ^ w)
    (hvisit : ∀ i, MeetsContract w p visit (explicitEdgeVisitContract w h edges i (values i) num))
    (hpre : ∀ i (hi : i < addresses.length) heap mem,
      records i heap mem → heap < 2 ^ w ∧
      (explicitEdgeVisitContract w h edges i (values i) num).pre
        [base, addresses.length, i, addresses[i], a, L, heap] mem)
    (hpost : ∀ i (hi : i < addresses.length) heap mem ret mem',
      records i heap mem → ListAt mem addrBase addresses →
      (explicitEdgeVisitContract w h edges i (values i) num).post
        [base, addresses.length, i, addresses[i], a, L, heap] mem ret mem' →
      ListAt mem' addrBase addresses ∧ records (i + 1) ret mem') :
    Triple w p (explicitEdgeLoopInv base addrBase a L addresses records 0) (explicitEdgeLoop visit)
      (normalPost (explicitEdgeLoopInv base addrBase a L addresses records addresses.length))
      (fun _ => addresses.length *
        (136 * addresses.length + 152 * L^2 + 561 * L + 800) + 4) := by
  obtain ⟨hbase, harray, ha, hL⟩ := hwords
  unfold explicitEdgeLoop
  refine Triple.forUp_const
    (Inv := explicitEdgeLoopInv base addrBase a L addresses records)
    (136 * addresses.length + 152 * L^2 + 561 * L + 791) 0 addresses.length
    (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun _ _ _ _ hin => hin.2.2.2.2.2.1)
    (fun _ _ _ _ hin => by simp [Expr.eval, hin.2.1]) ?_ |>.mono_cost ?_
  · intro i _ hi
    let vs (st : State) := [base, addresses.length, i, addresses[i], a, L, st.regs 5]
    unfold explicitEdgeLoopStep
    refine (Triple.call (vs := vs) (hvisit i) ?_ ?_ ?_ ?_).mono_cost ?_
    · intro st hin
      obtain ⟨h₀, h₁, h₂, h₃, h₄, h₆, harr, _⟩ := hin
      have hadd : addrBase + i < 2 ^ w := by omega
      simp [vs, evalArgs, Expr.eval, h₀, h₁, h₂, h₃, h₄, h₆, hadd, harr i hi]
    · intro st hin x hx
      have hheap := (hpre i hi (st.regs 5) st.mem hin.2.2.2.2.2.2.2).1
      have hrec := haddr _ (List.getElem_mem hi)
      have hiw : i < 2 ^ w := by omega
      have hlenw : addresses.length < 2 ^ w := by omega
      simp only [vs, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals assumption
    · intro st hin
      exact (hpre i hi (st.regs 5) st.mem hin.2.2.2.2.2.2.2).2
    · intro st ret mem' pos' hin hp
      obtain ⟨h₀, h₁, h₂, h₃, h₄, h₆, harr, hrec⟩ := hin
      obtain ⟨harr', hrec'⟩ := hpost i hi (st.regs 5) st.mem ret mem' hrec harr hp
      simp [explicitEdgeLoopInv, Function.update_of_ne, h₀, h₁, h₂, h₃, h₄, h₆, harr', hrec']
    · intro st _
      simp [explicitEdgeVisitContract, vs, argsSize, Expr.size, ← hlen]
      omega
  · intro st _
    simp [Expr.size]

/-- The expected record after processing a prefix. Its increment is
computed from the entire route and applied as soon as the name appears. -/
@[expose] def explicitEdgePrefixValue (edges : List (ℕ × Bool)) (i e : ℕ)
    (old : PathEdgeValue) (num : ℤ) : PathEdgeValue :=
  if e ∈ (edges.take i).map Prod.fst then
    old.shift (PathTag.ofFlow (num * ((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ))))
  else old

/-- The next prefix either preserves the expected record or applies
its full signed and absolute increments for the first occurrence. -/
theorem explicitEdgePrefixValue_succ (edges : List (ℕ × Bool)) {i : ℕ}
    (hi : i < edges.length) (e : ℕ) (old : PathEdgeValue) (num : ℤ) :
    explicitEdgePrefixValue edges (i + 1) e old num =
      if e = edges[i].1 ∧ e ∉ (edges.take i).map Prod.fst then
        old.shift (PathTag.ofFlow
          (num * ((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ))))
      else explicitEdgePrefixValue edges i e old num := by
  unfold explicitEdgePrefixValue
  by_cases row : e = edges[i].1
  · subst e
    by_cases seen : edges[i].1 ∈ (edges.take i).map Prod.fst <;>
      simp only [explicitEdge_mem_prefix_succ edges hi, seen, true_or, false_or, eq_self,
        true_and, not_true_eq_false, not_false_eq_true, ite_true, ite_false]
  · by_cases seen : e ∈ (edges.take i).map Prod.fst <;>
      simp only [explicitEdge_mem_prefix_succ edges hi, seen, row, true_or, false_or,
        false_and, not_true_eq_false, not_false_eq_true, and_false, ite_true, ite_false]

/-- The concrete record invariant holds for every explicit edge name. -/
@[expose] def ExplicitEdgePrefixAt (mem : ℕ → ℕ) (h L : ℕ) (edges : List (ℕ × Bool))
    (address : ℕ → ℕ) (old : ℕ → PathEdgeValue) (num : ℤ) (i : ℕ) : Prop :=
  ∀ e ∈ edges.map Prod.fst,
    PathEdgeAt mem (address e) h L (some (explicitEdgePrefixValue edges i e (old e) num))

/-- An initial collection of explicit edge records supplies the empty-prefix invariant. -/
theorem explicitEdgePrefixAt_zero {mem : ℕ → ℕ} {h L : ℕ} {edges : List (ℕ × Bool)}
    {address : ℕ → ℕ} {old : ℕ → PathEdgeValue} {num : ℤ}
    (hrecords : ∀ e ∈ edges.map Prod.fst, PathEdgeAt mem (address e) h L (some (old e))) :
    ExplicitEdgePrefixAt mem h L edges address old num 0 := by
  intro e he
  simpa [explicitEdgePrefixValue] using hrecords e he

/-- The first visit changes the selected record, and the contract
frames every other record. A repeated visit preserves all records. -/
theorem explicitEdgeVisit_preserves_prefix {w h L i base a heap ret : ℕ}
    {mem mem' : ℕ → ℕ} {edges : List (ℕ × Bool)} (hi : i < edges.length)
    (address : ℕ → ℕ) (old : ℕ → PathEdgeValue) (num : ℤ)
    (hbelow : ∀ e ∈ edges.map Prod.fst, address e + 2 + 4 * L ≤ heap)
    (hdisj : ∀ e ∈ edges.map Prod.fst, e ≠ edges[i].1 →
      address e + 2 + 4 * L ≤ address edges[i].1 ∨
        address edges[i].1 + 2 + 4 * L ≤ address e)
    (hrecords : ExplicitEdgePrefixAt mem h L edges address old num i)
    (hp : (explicitEdgeVisitContract w h edges i (old edges[i].1) num).post
      [base, edges.length, i, address edges[i].1, a, L, heap] mem ret mem') :
    ExplicitEdgePrefixAt mem' h L edges address old num (i + 1) := by
  obtain ⟨hi', hp⟩ := hp
  by_cases fresh : edges[i].1 ∉ (edges.take i).map Prod.fst
  · rw [ite_eq_left fresh] at hp
    change (explicitEdgeUpdateContract w h edges edges[i].1 (old edges[i].1) num).post
      [base, edges.length, edges[i].1, address edges[i].1, a, L, heap] mem ret mem' at hp
    intro e he
    rw [explicitEdgePrefixValue_succ edges hi]
    by_cases same : e = edges[i].1
    · subst e
      rw [ite_eq_left (And.intro rfl fresh)]
      exact hp.2.1
    · rw [ite_eq_right (fun h => same h.1)]
      exact explicitEdgeUpdate_frame_record hp (hrecords e he) (hbelow e he) (hdisj e he same)
  · rw [ite_eq_right fresh] at hp
    obtain ⟨_, rfl⟩ := hp
    intro e he
    rw [explicitEdgePrefixValue_succ edges hi, ite_eq_right]
    · exact hrecords e he
    · rintro ⟨rfl, hn⟩
      exact fresh hn

/-- The final prefix has applied the net count exactly once to every
explicit edge record. -/
theorem explicitEdgePrefixAt_done {mem : ℕ → ℕ} {h L : ℕ} {edges : List (ℕ × Bool)}
    {address : ℕ → ℕ} {old : ℕ → PathEdgeValue} {num : ℤ}
    (hp : ExplicitEdgePrefixAt mem h L edges address old num edges.length)
    (e : ℕ) (he : e ∈ edges.map Prod.fst) :
    PathEdgeAt mem (address e) h L (some ((old e).shift (PathTag.ofFlow
      (num * ((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)))))) := by
  simpa only [explicitEdgePrefixValue, List.take_length, ite_eq_left he] using hp e he

end MinCostFlow.MinRatio
