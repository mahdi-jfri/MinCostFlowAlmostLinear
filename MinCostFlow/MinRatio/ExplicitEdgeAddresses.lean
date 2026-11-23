module

public import MinCostFlow.MinRatio.ExplicitEdgeCount
import WordRAM.Tactic

/-!
# Resolving record addresses for the explicit route

Algorithm 2 (page 29) updates each explicit edge mentioned in the
cycle. A scan resolves each occurrence's name through the live record
address table and writes the resulting addresses beside the route.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM

/-- Registers hold the route base and length, record table base,
output base, and scanned row index. -/
@[expose] def explicitEdgeAddressStep : Stmt :=
  .store (.bin .add (.reg 3) (.reg 4))
    (.load (.bin .add (.reg 2) (.load
      (.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 4))))))

/-- Resolve each row in route order. -/
@[expose] def explicitEdgeAddressLoop : Stmt :=
  forUp 4 (.reg 1) explicitEdgeAddressStep

/-- The address scan changes only the initialized output slice. -/
@[expose] def ExplicitEdgeAddressInv (base table dst : ℕ) (edges : List (ℕ × Bool))
    (address original : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = base ∧ st.regs 1 = edges.length ∧ st.regs 2 = table ∧
    st.regs 3 = dst ∧ st.regs 4 = i ∧
    (∀ j (hj : j < edges.length), j < i → st.mem (dst + j) = address edges[j].1) ∧
    (∀ x, x < dst ∨ dst + i ≤ x → st.mem x = original x)

/-- The address scan uses no random statements. -/
theorem explicitEdgeAddressLoop_noRand : explicitEdgeAddressLoop.NoRand := by
  simp [explicitEdgeAddressLoop, explicitEdgeAddressStep, forUp, Stmt.NoRand]

/-- The initial state has no resolved rows and frames the entire memory. -/
theorem explicitEdgeAddressInv_start (base table dst : ℕ) (edges : List (ℕ × Bool))
    (address original : ℕ → ℕ) (pos : ℕ) :
    ExplicitEdgeAddressInv base table dst edges address original 0
      (startState [base, edges.length, table, dst] original pos) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ hj => (Nat.not_lt_zero _ hj).elim, fun _ _ => rfl⟩

/-- The scan resolves all explicit records in at most `25 * K + 4`
steps. The route and every table entry used by it lie below the output. -/
theorem explicitEdgeAddressLoop_triple {w base table dst : ℕ} {p : Program}
    (edges : List (ℕ × Bool)) (address original : ℕ → ℕ)
    (hr : ExplicitEdgesAt original base edges) (hb : base + 2 * edges.length ≤ dst)
    (ht : ∀ e ∈ edges.map Prod.fst, table + e < dst ∧ original (table + e) = address e)
    (hroom : dst + edges.length + 2 < 2 ^ w) :
    let inv := ExplicitEdgeAddressInv base table dst edges address original
    Triple w p (inv 0) explicitEdgeAddressLoop (normalPost (inv edges.length))
      (fun _ => 25 * edges.length + 4) := by
  dsimp only
  unfold explicitEdgeAddressLoop
  refine (Triple.forUp_const (Inv := ExplicitEdgeAddressInv base table dst edges address original)
    16 0 edges.length (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun _ _ _ _ h => h.2.2.2.2.1)
    (fun _ st _ _ h => by simp [Expr.eval, h.2.1]) ?_).mono_cost ?_
  · intro i _ hi
    unfold explicitEdgeAddressStep
    refine (Triple.store (addr := fun _ => dst + i) (val := fun _ => address edges[i].1)
      ?_ ?_ ?_).mono_cost ?_
    · intro st hin
      have hx : dst + i < 2 ^ w := by omega
      simp [Expr.eval, hin.2.2.2.1, hin.2.2.2.2.1, hx]
    · intro st hin
      obtain ⟨h₀, h₁, h₂, h₃, h₄, hprefix, hframe⟩ := hin
      have hentry := ht edges[i].1 (List.mem_map.mpr ⟨edges[i], List.getElem_mem hi, rfl⟩)
      have hread := (hframe (base + 2 * i) (Or.inl (by omega))).trans (hr.read hi).1
      have hvalue := (hframe (table + edges[i].1) (Or.inl hentry.1)).trans hentry.2
      have htwo : 2 < 2 ^ w := by omega
      have hmul : 2 * i < 2 ^ w := by omega
      have haddr : base + 2 * i < 2 ^ w := by omega
      have htable : table + edges[i].1 < 2 ^ w := by omega
      simp [Expr.eval, h₀, h₂, h₄, hread, hvalue, htwo, hmul, haddr, htable]
    · intro st hin
      obtain ⟨h₀, h₁, h₂, h₃, h₄, hprefix, hframe⟩ := hin
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h₄⟩
      · simpa [Function.update_of_ne] using h₀
      · simpa [Function.update_of_ne] using h₁
      · simpa [Function.update_of_ne] using h₂
      · simpa [Function.update_of_ne] using h₃
      · simp
      · intro j hj hji
        change Function.update st.mem (dst + i) (address edges[i].1) (dst + j) = _
        by_cases he : j = i
        · subst j
          simp
        · rw [Function.update_of_ne (by omega : dst + j ≠ dst + i)]
          exact hprefix j hj (by omega)
      · intro x hx
        change Function.update st.mem (dst + i) (address edges[i].1) x = _
        rw [Function.update_of_ne (by omega : x ≠ dst + i)]
        exact hframe x (by omega)
    · intro st _
      decide
  · intro st _
    simp [Expr.size, Nat.mul_comm]

/-- The completed address scan gives exactly the array read by the
explicit edge update loop. -/
theorem explicitEdgeAddressLoop_array {base table dst : ℕ} {edges : List (ℕ × Bool)}
    {address original : ℕ → ℕ} {st : State}
    (hin : ExplicitEdgeAddressInv base table dst edges address original edges.length st) :
    ListAt st.mem dst (edges.map fun row => address row.1) := by
  intro j hj
  have hj' : j < edges.length := by simpa only [List.length_map] using hj
  simpa only [List.getElem_map] using hin.2.2.2.2.2.1 j hj' hj'

/-- Resolve the route addresses and return the end of the array. -/
@[expose] def explicitEdgeAddressBody : Stmt :=
  explicitEdgeAddressLoop ;;
  .ret (.bin .add (.reg 3) (.reg 1))

/-- The route and its live table entries may be read below the output array. -/
@[expose] def explicitEdgeAddressContract (w : ℕ) (edges : List (ℕ × Bool))
    (address : ℕ → ℕ) : Contract where
  pre args mem := ∃ base table dst, args = [base, edges.length, table, dst] ∧
    ExplicitEdgesAt mem base edges ∧ base + 2 * edges.length ≤ dst ∧
    (∀ e ∈ edges.map Prod.fst, table + e < dst ∧ mem (table + e) = address e) ∧
    dst + edges.length + 2 < 2 ^ w
  post args mem ret mem' :=
    ret = heapArg args + edges.length ∧
    ListAt mem' (heapArg args) (edges.map fun row => address row.1) ∧
    ∀ x, x < heapArg args ∨ ret ≤ x → mem' x = mem x
  cost _ _ := 25 * edges.length + 10

/-- Address resolution and the heap return are deterministic. -/
theorem explicitEdgeAddressBody_noRand : explicitEdgeAddressBody.NoRand := by
  simp [explicitEdgeAddressBody, explicitEdgeAddressLoop_noRand, Stmt.NoRand]

/-- The callable resolver supplies the exact input array for the next phase. -/
theorem explicitEdgeAddress_meetsContract {w entry : ℕ} {p : Program}
    (edges : List (ℕ × Bool)) (address : ℕ → ℕ)
    (hp : p.HasAt entry [explicitEdgeAddressBody]) :
    MeetsContract w p entry (explicitEdgeAddressContract w edges address) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω _ hpre
  obtain ⟨base, table, dst, rfl, hr, hb, ht, hroom⟩ := hpre
  have hsum : dst + edges.length < 2 ^ w := by omega
  apply runs_start_le
  unfold explicitEdgeAddressBody
  refine runs_seq_triple_le (explicitEdgeAddressLoop_triple edges address mem hr hb ht hroom)
    (explicitEdgeAddressInv_start base table dst edges address mem pos) ?_
  intro st hin
  have hd := hin.2.2.2.1
  have hl := hin.2.1
  refine runs_ret_le (v := dst + edges.length) (by simp [Expr.eval, hd, hl, hsum]) ?_ ?_
  · exact ⟨rfl, explicitEdgeAddressLoop_array hin, hin.2.2.2.2.2.2⟩
  · simp [explicitEdgeAddressContract, Expr.size]

end MinCostFlow.MinRatio
