module

public import WordRAM.Sep.CostSpec
public import WordRAM.Sep.BridgeHeap
public import MinCostFlow.Scaling.SolverContract

/-!
# Second-layer bridge for `solverContract`

This file bridges the first-layer `solverContract` (`MinCostFlow/Scaling/SolverContract.lean`) to a
second-layer separation-logic specification `solverSpec` that exposes the solver's output as
`Assn.list h flow`.

Because `heapSpec.post` in `WordRAM/Sep/BridgeHeap.lean` omits `ZeroFrom m₁ v` and `solverContract`
does not constrain `h + J.m ≤ v`, we first prove the local strengthening `meets_heap_zero` (by the
same proof as `MeetsContract.meets_heap`), preserving `ZeroFrom m₁ v` in `heapSpecZero.post`. We
then apply it with `solverCells [a, h] = Set.Ico a h` and weaken via `Meets.weaken` to
`solverSpec`, unifying the cases `h + J.m ≤ v` and `v < h + J.m` via `max v (h + J.m)`.
-/

@[expose] public section

open WordRAM WordRAM.Sep MinCostFlow.Scaling MinCostFlow.Scaling.Machine

namespace MinCostFlow.NarrowProg

/-! ### Strengthening `heapSpec` with `ZeroFrom m₁ v` -/

/-- Specification of `heapContract w pre post cost space` on cells `D args`, retaining
`ZeroFrom m₁ v` in the postcondition so cells at `≥ v` are known to match `Assn.free v (2 ^ w - v)`. -/
def heapSpecZero (w : ℕ) (pre : List ℕ → (ℕ → ℕ) → Prop)
    (post : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) → Prop) (cost space : List ℕ → (ℕ → ℕ) → ℕ)
    (D : List ℕ → Set ℕ) : Spec (ℕ → ℕ) where
  pre m₀ args := ⌜pre args m₀ ∧ heapArg args + space args m₀ < 2 ^ w⌝ * $ (cost args m₀ : ℤ) *
    (Assn.cells (D args) m₀ * Assn.free (heapArg args) (2 ^ w - heapArg args))
  post m₀ args v := ⨆ m₁ : ℕ → ℕ,
    ⌜heapArg args ≤ v ∧ v ≤ heapArg args + space args m₀ ∧ ZeroFrom m₁ v ∧
      ∃ m : ℕ → ℕ, (∀ a ∈ D args, m a = m₀ a) ∧ pre args m ∧ post args m m₁⌝ *
    (Assn.cells (D args) m₀ * Assn.cells (Set.Ico (heapArg args) v) m₁ *
      Assn.free v (2 ^ w - v))

/-- Local strengthening of `MeetsContract.meets_heap` (`WordRAM/Sep/BridgeHeap.lean`) that keeps
`ZeroFrom m₁ v` in the postcondition. -/
theorem meets_heap_zero {w : ℕ} {p : Program} {f : ℕ}
    {pre : List ℕ → (ℕ → ℕ) → Prop} {post : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) → Prop}
    {cost space : List ℕ → (ℕ → ℕ) → ℕ} {D : List ℕ → Set ℕ} {body : Stmt}
    (hC : MeetsContract w p f (heapContract w pre post cost space))
    (hL : HeapLocalTo pre cost space D) (hproc : p.procs[f]? = some body) :
    Meets w p f (heapSpecZero w pre post cost space D) := by
  refine ⟨body, hproc, fun m₀ args => ?_⟩
  intro st ω h hf c hpre hd hin hok hw
  obtain ⟨hρ, hpre⟩ := Assn.pure_mul_apply.mp hpre
  obtain ⟨⟨hP, hfit⟩, hcells⟩ := Assn.pure_credits_apply.mp hpre
  set H := heapArg args with hHdef
  have hH : H ≤ 2 ^ w := by omega
  obtain ⟨hc, hbelow, rfl⟩ := Assn.cells_mul_free_top hH hcells hok
  have hin₁ := Heap.in_restrict.mp hin.of_union_left
  have hfD := Heap.disjoint_restrict_left.mp hd
  set st₀ := st.withHigh w fun _ => 0 with hst₀
  have hagree : ∀ a ∈ D args, st₀.mem a = m₀ a := fun a ha => by
    have hlt : a < 2 ^ w := by have := hbelow a ha; omega
    show memMix w st.mem (fun _ => 0) a = _
    rw [memMix_of_lt hlt]
    simpa [hbelow a ha] using hin₁ a (Or.inl ha)
  have hzero : ZeroFrom st₀.mem H := fun a ha => by
    by_cases hlt : a < 2 ^ w
    · show memMix w st.mem (fun _ => 0) a = _
      rw [memMix_of_lt hlt]
      simpa [Nat.not_lt.mpr ha] using hin₁ a (Or.inr ⟨ha, hlt⟩)
    · show memMix w st.mem (fun _ => 0) a = _
      rw [memMix_of_ge (Nat.not_lt.mp hlt)]
  have hP₀ := hL.pre args m₀ st₀.mem hagree hP
  have hcost := hL.cost args m₀ st₀.mem hagree hP
  have hspace := hL.space args m₀ st₀.mem hagree hP
  obtain ⟨body', hproc', o, st₁, k, hrun, ⟨hHv, hvle, hlow, hz, hpost⟩, hk⟩ :=
    hC args st₀.mem st.pos ω (args_lt_of_argRegs (hρ ▸ hw.1)) ⟨hP₀, hzero, by omega⟩
  rw [hproc] at hproc'
  cases hproc'
  rw [show startState args st₀.mem st.pos = st₀ from
    (eq_startState_of_regs (st := st₀) hρ).symm] at hrun
  have hrun' := Runs.of_withHigh_zero hrun hw
  have hv : o.value ≤ 2 ^ w := by
    change o.value ≤ H + space args st₀.mem at hvle; omega
  set st' := st₁.withHigh w st.mem with hst'
  have hlow' : ∀ a < 2 ^ w, st'.mem a = st₁.mem a := fun a ha => memMix_of_lt ha
  refine ⟨o, st', k, Heap.restrict (D args ∪ Set.Ico H (2 ^ w)) st'.mem, c - k, hrun', ?_,
    Heap.disjoint_restrict_left.mpr hfD, ?_,
    Heap.addrOk_restrict.mpr (Heap.addrOk_restrict.mp hok),
    by change k ≤ cost args st₀.mem at hk; omega⟩
  · refine Assn.mul_gc_of_nonneg ((Assn.iSup_apply _ _ _).mpr ⟨st₁.mem, ?_⟩)
      (by change k ≤ cost args st₀.mem at hk; omega)
    refine Assn.pure_mul_apply.mpr ⟨⟨hHv, by change o.value ≤ H + space args st₀.mem at hvle; omega,
      hz, st₀.mem, hagree, hP₀, hpost⟩, ?_⟩
    rw [Assn.cells_congr (D := Set.Ico H o.value) (m' := st'.mem) fun a ha => by
      simp only [Set.mem_Ico] at ha; exact (hlow' a (by omega)).symm]
    refine Assn.cells_mul_cells_mul_free_top hbelow hHv hv (fun a ha => ?_) (fun a ha hlt => ?_)
    · have hlt : a < H := hbelow a ha
      rw [hlow' a (by omega), hlow a hlt, hagree a ha]
    · rw [hlow' a hlt]; exact hz a ha
  · refine (Heap.in_union (Heap.disjoint_restrict_left.mpr hfD)).mpr
      ⟨Heap.in_restrict.mpr fun _ _ => rfl, fun a x hx => ?_⟩
    have hnot : a ∉ D args ∪ Set.Ico H (2 ^ w) := fun ha => by rw [hfD a ha] at hx; cases hx
    have hold := ((Heap.in_union hd).mp hin).2 a x hx
    by_cases haH : a < H
    · rw [hlow' a (by omega), hlow a haH]
      show memMix w st.mem (fun _ => 0) a = _
      rw [memMix_of_lt (by omega), hold]
    · have hge : 2 ^ w ≤ a := by
        by_contra hlt
        exact hnot (Or.inr ⟨Nat.not_lt.mp haH, Nat.not_le.mp hlt⟩)
      show memMix w st₁.mem st.mem a = _
      rw [memMix_of_ge hge, hold]

/-! ### Locality of `solverContract` -/

/-- The cells `[a, h)` that `solverContract` reads for arguments `[a, h]`. -/
def solverCells : List ℕ → Set ℕ
  | [a, h] => Set.Ico a h
  | _ => ∅

/-- `solverContract`'s pre, cost, and space read only `[a, h)`. -/
theorem solverContract_heapLocalTo (w : ℕ) (T S : ℕ → ℕ → ℕ) :
    HeapLocalTo
      (fun args mem => ∃ a h : ℕ, args = [a, h] ∧ ∃ J : Circulation,
        ListAt mem a J.solverWords ∧ a + J.solverWords.length ≤ h ∧
        (∀ x ∈ J.solverWords, x < 2 ^ w) ∧ J.CostsBounded (J.m ^ 10) ∧
        h + J.m + S J.n J.m < 2 ^ w ∧ ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)
      (fun args mem => T (solverDimensions args mem).1 (solverDimensions args mem).2)
      (fun args mem => (solverDimensions args mem).2 +
        S (solverDimensions args mem).1 (solverDimensions args mem).2)
      solverCells where
  pre := by
    rintro args m m' hagree ⟨a, h, rfl, J, hat, hle, hwords, hcost, hspace, hcap⟩
    refine ⟨a, h, rfl, J, fun i hi => ?_, hle, hwords, hcost, hspace, hcap⟩
    rw [hagree (a + i) (by simp only [solverCells, Set.mem_Ico]; omega)]
    exact hat i hi
  cost := by
    rintro args m m' hagree ⟨a, h, rfl, J, hat, hle, -, -, -, -⟩
    have hlen : 2 ≤ J.solverWords.length := by rw [J.solverWords_length]; omega
    have h0 : m' a = m a := hagree a (by simp only [solverCells, Set.mem_Ico]; omega)
    have h1 : m' (a + 1) = m (a + 1) :=
      hagree (a + 1) (by simp only [solverCells, Set.mem_Ico]; omega)
    have hdim : solverDimensions [a, h] m' = solverDimensions [a, h] m := by
      simp only [solverDimensions, List.getD_cons_zero, h0, h1]
    rw [hdim]
  space := by
    rintro args m m' hagree ⟨a, h, rfl, J, hat, hle, -, -, -, -⟩
    have hlen : 2 ≤ J.solverWords.length := by rw [J.solverWords_length]; omega
    have h0 : m' a = m a := hagree a (by simp only [solverCells, Set.mem_Ico]; omega)
    have h1 : m' (a + 1) = m (a + 1) :=
      hagree (a + 1) (by simp only [solverCells, Set.mem_Ico]; omega)
    have hdim : solverDimensions [a, h] m' = solverDimensions [a, h] m := by
      simp only [solverDimensions, List.getD_cons_zero, h0, h1]
    rw [hdim]

/-! ### Second-layer solver specification -/

/-- Second-layer specification of a bounded circulation solver. The solver input `J.solverWords`
is placed at `a` directly below the heap pointer `h = a + J.solverWords.length`. The postcondition
returns the solver's output as `Assn.list h flow` together with `J.Optimal` and the remaining free
heap from `max v (h + J.m)` to `2 ^ w`. -/
def solverSpec (w : ℕ) (S : ℕ → ℕ → ℕ) : Spec Circulation where
  pre J args := ⨆ (a : ℕ),
    ⌜args = [a, a + J.solverWords.length] ∧
      (∀ x ∈ J.solverWords, x < 2 ^ w) ∧ J.CostsBounded (J.m ^ 10) ∧
      a + J.solverWords.length + J.m + S J.n J.m < 2 ^ w ∧
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40)⌝ *
    Assn.list a J.solverWords *
    Assn.free (a + J.solverWords.length) (2 ^ w - (a + J.solverWords.length))
  post J args v := ⨆ (a : ℕ) (flow : List ℕ),
    let h := a + J.solverWords.length
    ⌜args = [a, h] ∧ h ≤ v ∧ v ≤ h + J.m + S J.n J.m ∧
      flow.length = J.m ∧
      J.Optimal (fun e => ((flow.getD e.val 0 : ℕ) : ℝ))⌝ *
    Assn.list a J.solverWords * Assn.list h flow *
    Assn.free (max v (h + J.m)) (2 ^ w - max v (h + J.m))

/-- Helper: combine `cells [h, v) m₁ * free v (2 ^ w - v)` with `ZeroFrom m₁ v` into
`list h flow * free (max v (h + m)) (2 ^ w - max v (h + m)) * gc`. -/
private theorem cells_free_to_flow {w h v m : ℕ} {m₁ : ℕ → ℕ}
    (hhv : h ≤ v) (hfit : h + m ≤ 2 ^ w) (hvfit : v ≤ 2 ^ w) (hz : ZeroFrom m₁ v) :
    Assn.cells (Set.Ico h v) m₁ * Assn.free v (2 ^ w - v) ≤
      Assn.list h ((List.range m).map fun i => m₁ (h + i)) *
        Assn.free (max v (h + m)) (2 ^ w - max v (h + m)) * Assn.gc := by
  rw [← Assn.cells_Ico_eq_list]
  rcases le_or_gt (h + m) v with hle | hlt
  · rw [max_eq_left hle]
    have hdisj : Disjoint (Set.Ico h (h + m)) (Set.Ico (h + m) v) := by
      rw [Set.disjoint_left]; intro x hx1 hx2
      simp only [Set.mem_Ico] at hx1 hx2; omega
    have hunion : Set.Ico h (h + m) ∪ Set.Ico (h + m) v = Set.Ico h v :=
      Set.Ico_union_Ico_eq_Ico (by omega) hle
    rw [← hunion, Assn.cells_union hdisj]
    calc Assn.cells (Set.Ico h (h + m)) m₁ * Assn.cells (Set.Ico (h + m) v) m₁ *
            Assn.free v (2 ^ w - v)
        = Assn.cells (Set.Ico h (h + m)) m₁ * Assn.free v (2 ^ w - v) *
            Assn.cells (Set.Ico (h + m) v) m₁ := by rw [mul_right_comm]
      _ ≤ _ := Assn.mul_le_mul_of_le le_rfl (Assn.noDebt_cells _ _)
  · rw [max_eq_right (le_of_lt hlt)]
    have hsplit : 2 ^ w - v = (h + m - v) + (2 ^ w - (h + m)) := by omega
    rw [hsplit, Assn.free_add', show v + (h + m - v) = h + m by omega]
    have hfree_eq : Assn.free v (h + m - v) = Assn.cells (Set.Ico v (h + m)) m₁ := by
      rw [Assn.free_eq_cells, show v + (h + m - v) = h + m by omega]
      exact Assn.cells_congr fun x hx => by
        simp only [Set.mem_Ico] at hx
        exact (hz x hx.1).symm
    rw [hfree_eq, ← mul_assoc]
    have hdisj : Disjoint (Set.Ico h v) (Set.Ico v (h + m)) := by
      rw [Set.disjoint_left]; intro x hx1 hx2
      simp only [Set.mem_Ico] at hx1 hx2; omega
    rw [← Assn.cells_union hdisj, Set.Ico_union_Ico_eq_Ico hhv (le_of_lt hlt)]
    exact Assn.le_mul_gc _

/-- **Solver bridge.** Any procedure meeting the first-layer `solverContract w T S` meets the
second-layer `(solverSpec w S).withCost (fun J _ => T J.n J.m)`. -/
theorem solverContract_meets_solverSpec {w : ℕ} {p : Program} {f : ℕ} {T S : ℕ → ℕ → ℕ}
    {body : Stmt} (hC : MeetsContract w p f (solverContract w T S))
    (hproc : p.procs[f]? = some body) :
    Meets w p f ((solverSpec w S).withCost fun J _ => T J.n J.m) := by
  have hheap := meets_heap_zero hC (solverContract_heapLocalTo w T S) hproc
  refine hheap.weaken fun J args _ h c _ hpre => ?_
  simp only [Spec.withCost, solverSpec] at hpre
  obtain ⟨h1, h2, c1, c2, hd, rfl, rfl, hpre1, hc2⟩ := hpre
  obtain ⟨a, ha⟩ := (Assn.iSup_apply _ _ _).mp hpre1
  rw [mul_assoc] at ha
  obtain ⟨⟨rfl, hwords, hcostB, hfit, hcap⟩, hlists⟩ := Assn.pure_mul_apply.mp ha
  set h₀ := a + J.solverWords.length with hh₀
  let m₀ : ℕ → ℕ := fun x => J.solverWords.getD (x - a) 0
  have hat₀ : ListAt m₀ a J.solverWords := fun i hi => by
    simp only [m₀, Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ hi]
  have hdim₀ : solverDimensions [a, h₀] m₀ = (J.n, J.m) :=
    solverDimensions_of_at J m₀ a h₀ hat₀
  have hlist_eq : Assn.list a J.solverWords = Assn.cells (solverCells [a, h₀]) m₀ := by
    rw [solverCells, Assn.list_eq_cells]
  have hheap_eq : (Assn.cells (solverCells [a, h₀]) m₀ * Assn.free h₀ (2 ^ w - h₀)) h1 c1 := by
    rwa [← hlist_eq]
  have hcredit_eq : ($ (T (solverDimensions [a, h₀] m₀).1 (solverDimensions [a, h₀] m₀).2 : ℤ)) h2 c2 := by
    rwa [hdim₀]
  refine ⟨m₀, ?_, fun v => ?_⟩
  · simp only [heapSpecZero, heapArg, List.getLastD_cons, List.getLastD_nil]
    rw [mul_assoc]
    refine Assn.pure_mul_apply.mpr ⟨⟨⟨a, h₀, rfl, J, hat₀, le_rfl, hwords, hcostB, hfit, hcap⟩,
      by rw [hdim₀]; dsimp only; omega⟩, ?_⟩
    exact ⟨h2, h1, c2, c1, hd.symm, Heap.union_comm hd, add_comm c1 c2,
      hcredit_eq, hheap_eq⟩
  · simp only [heapSpecZero, heapArg, List.getLastD_cons, List.getLastD_nil]
    refine Assn.iSup_le_iff'.mpr fun m₁ => Assn.pure_mul_le.mpr ?_
    rintro ⟨hhv, hvle, hz, m, hagree, -, hpost⟩
    rw [hdim₀] at hvle
    dsimp only at hvle
    have hat_m : ListAt m a J.solverWords := fun i hi => by
      rw [hagree (a + i) (by simp only [solverCells, Set.mem_Ico]; omega)]
      exact hat₀ i hi
    have hopt_m₁ : J.Optimal (fun e => (J.readSolverFlow m₁ h₀ e : ℝ)) :=
      hpost J hat_m
    let flow : List ℕ := (List.range J.m).map fun i => m₁ (h₀ + i)
    have hflow_len : flow.length = J.m := by simp [flow]
    have hflow_opt : J.Optimal (fun e => ((flow.getD e.val 0 : ℕ) : ℝ)) := by
      convert hopt_m₁ using 1
      funext e
      simp only [Circulation.readSolverFlow, Int.cast_natCast, flow,
        List.getD_eq_getElem _ _ (by simp [e.isLt] : e.val < ((List.range J.m).map _).length),
        List.getElem_map, List.getElem_range]
    refine le_trans ?_ (Assn.mul_le_mul_of_le (le_iSup (fun a' : ℕ => ⨆ flow' : List ℕ, _) a) le_rfl)
    refine le_trans ?_ (Assn.mul_le_mul_of_le (le_iSup (fun flow' : List ℕ => _) flow) le_rfl)
    dsimp only
    rw [← hlist_eq]
    have hpure_ok : [a, h₀] = [a, h₀] ∧ h₀ ≤ v ∧ v ≤ h₀ + J.m + S J.n J.m ∧
        flow.length = J.m ∧ J.Optimal (fun e => ((flow.getD e.val 0 : ℕ) : ℝ)) :=
      ⟨rfl, hhv, by omega, hflow_len, hflow_opt⟩
    rw [eq_true hpure_ok, Assn.pure_true, one_mul, mul_assoc, mul_assoc]
    have hcf := cells_free_to_flow (w := w) (m := J.m) hhv (by omega) (by omega) hz
    calc Assn.list a J.solverWords * (Assn.cells (Set.Ico h₀ v) m₁ * Assn.free v (2 ^ w - v))
        ≤ Assn.list a J.solverWords *
            (Assn.list h₀ flow * Assn.free (max v (h₀ + J.m)) (2 ^ w - max v (h₀ + J.m)) *
              Assn.gc) := Assn.mul_le_mul_of_le le_rfl hcf
      _ = _ := by simp only [mul_assoc, hh₀]

end MinCostFlow.NarrowProg
