module

public import MinCostFlow.LinkCut.Gen.Steps
public import MinCostFlow.Num.Negate
public import MinCostFlow.Num.Add
public import WordRAM.CopyWords

/-!
# In-place updates of one number block

The numeric library computes a new number at the heap pointer. The payload procedures of the
tree must instead change a block of a node record and leave the scratch zero. The two programs
here do that: `negBlockBody` replaces the `K`-limb number at `x` by its negative, and
`addBlockBody` adds the number at `d` to the number at `x`. Each computes the result at the heap
pointer, copies it to `x`, and clears the scratch by copying the zero block just above it.
Results wrap modulo the capacity of `K` limbs, as in the library.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.LinkCut.Gen

/-- Negate the `K`-limb number at `x`, on `[x, K, heap]`. -/
def negBlockBody (negProc copyProc : ℕ) : Stmt :=
  .call 3 negProc [.reg 0, .reg 1, .reg 2] ;;
  .call 3 copyProc [.reg 2, .reg 0, .reg 1] ;;
  .call 3 copyProc [.bin .add (.reg 2) (.reg 1), .reg 2, .reg 1] ;;
  .ret (.const 0)

/-- Add the `K`-limb number at `d` to the one at `x`, on `[x, d, K, heap]`. -/
def addBlockBody (addProc copyProc : ℕ) : Stmt :=
  .call 4 addProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .call 4 copyProc [.reg 3, .reg 0, .reg 2] ;;
  .call 4 copyProc [.bin .add (.reg 3) (.reg 2), .reg 3, .reg 2] ;;
  .ret (.const 0)

theorem negBlockBody_noRand (a b : ℕ) : (negBlockBody a b).NoRand := by
  simp [negBlockBody, Stmt.NoRand]

theorem addBlockBody_noRand (a b : ℕ) : (addBlockBody a b).NoRand := by
  simp [addBlockBody, Stmt.NoRand]

/-- The contract of `negBlockBody`. -/
def negBlockContract (w h K : ℕ) : Contract :=
  payloadContract w
    (fun args mem => ∃ x heap, args = [x, K, heap] ∧ x + K ≤ heap ∧ Valid mem x h K)
    (fun args y => args.getD 0 0 ≤ y ∧ y < args.getD 0 0 + K)
    (fun args mem _ mem' => Valid mem' (args.getD 0 0) h K ∧
      intVal mem' (args.getD 0 0) h K = wrap h K (-intVal mem (args.getD 0 0) h K))
    (80 * K + 80) (2 * K)

/-- The contract of `addBlockBody`. -/
def addBlockContract (w h K : ℕ) : Contract :=
  payloadContract w
    (fun args mem => ∃ x d heap, args = [x, d, K, heap] ∧ x + K ≤ heap ∧ d + K ≤ heap ∧
      Valid mem x h K ∧ Valid mem d h K)
    (fun args y => args.getD 0 0 ≤ y ∧ y < args.getD 0 0 + K)
    (fun args mem _ mem' => Valid mem' (args.getD 0 0) h K ∧
      intVal mem' (args.getD 0 0) h K =
        wrap h K (intVal mem (args.getD 0 0) h K + intVal mem (args.getD 1 0) h K))
    (80 * K + 80) (2 * K)

/-- Copy the result block at `heap` to `x`, then clear it from the zero block above it. The
memory facts after both copies. -/
theorem storeBack_facts {mem₁ mem₂ mem₃ : ℕ → ℕ} {x heap K : ℕ}
    (hx : x + K ≤ heap) (hz₁ : ZeroFrom mem₁ (heap + K))
    (hc₂ : ∀ i < K, mem₂ (x + i) = mem₁ (heap + i))
    (ho₂ : ∀ y, y < x ∨ x + K ≤ y → mem₂ y = mem₁ y)
    (hc₃ : ∀ i < K, mem₃ (heap + i) = mem₂ (heap + K + i))
    (ho₃ : ∀ y, y < heap ∨ heap + K ≤ y → mem₃ y = mem₂ y) :
    ZeroFrom mem₃ heap ∧ (∀ i < K, mem₃ (x + i) = mem₁ (heap + i)) ∧
      (∀ y < heap, ¬ (x ≤ y ∧ y < x + K) → mem₃ y = mem₁ y) := by
  refine ⟨fun y hy => ?_, fun i hi => ?_, fun y hy hn => ?_⟩
  · by_cases hyK : y < heap + K
    · have := hc₃ (y - heap) (by omega)
      rw [show heap + (y - heap) = y by omega] at this
      rw [this, ho₂ _ (Or.inr (by omega))]; exact hz₁ _ (by omega)
    · rw [ho₃ y (Or.inr (by omega)), ho₂ y (Or.inr (by omega))]; exact hz₁ y (by omega)
  · rw [ho₃ _ (Or.inl (by omega)), hc₂ i hi]
  · rw [ho₃ y (Or.inl hy), ho₂ y (by omega)]

/-- `negBlockBody` meets its contract. -/
theorem negBlock_meetsContract {w h K b negProc copyProc : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hb : p.procs[b]? = some (negBlockBody negProc copyProc))
    (hneg : MeetsContract w p negProc (negateContract w h))
    (hcopy : MeetsContract w p copyProc (copyWordsContract w)) :
    MeetsContract w p b (negBlockContract w h K) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨x, heap, rfl, hxh, hv⟩, hz, hroom⟩
  change ZeroFrom mem heap at hz
  change heap + 2 * K < 2 ^ w at hroom
  have hxw := hwords x (by simp)
  have hKw := hwords K (by simp)
  have hhw := hwords heap (by simp)
  apply runs_start_le
  unfold negBlockBody
  refine runs_seq_call_le hneg (vs := [x, K, heap]) (by eval_expr) (by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega) ?_ ?_
  · exact ⟨x, K, heap, rfl, ⟨x, K, 1, heap, rfl, hxh, le_rfl, hv⟩, hz, by
      change heap + K < 2 ^ w; omega⟩
  intro v₁ mem₁ pos₁ hpost₁
  rcases hpost₁ with ⟨he₁, -, -, hf₁, hz₁, hl₁⟩
  change v₁ = heap + K at he₁
  change (∀ y < heap, mem₁ y = mem y) at hf₁
  change ListAt mem₁ heap (digits h K (capacity h K - 1 - unsignedVal mem x h K + 1)) at hl₁
  rw [he₁] at hz₁
  have hval := negateCarry_value_one hv hl₁
  refine runs_seq_call_le hcopy (vs := [heap, x, K]) (by eval_expr) (by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega) ⟨_, _, _, rfl, hw, by omega, by omega, Or.inl hxh⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨s₂, d₂, l₂, heq₂, -, hc₂, ho₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  refine runs_seq_call_le hcopy (vs := [heap + K, heap, K]) (by eval_expr) (by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega) ⟨_, _, _, rfl, hw, by omega, by omega, Or.inl le_rfl⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨s₃, d₃, l₃, heq₃, -, hc₃, ho₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl⟩ := heq₃
  obtain ⟨hz₃, hx₃, hk₃⟩ := storeBack_facts hxh hz₁ hc₂ ho₂ hc₃ ho₃
  refine runs_ret_le (by eval_expr) ?_ ?_
  · show ZeroFrom mem₃ heap ∧ (∀ y < heap, ¬ (x ≤ y ∧ y < x + K) → mem₃ y = mem y) ∧
      Valid mem₃ x h K ∧ intVal mem₃ x h K = wrap h K (-intVal mem x h K)
    refine ⟨hz₃, fun y hy hn => (hk₃ y hy hn).trans (hf₁ y hy), ?_, ?_⟩
    · intro i hi; rw [hx₃ i hi]; exact hval.1 i hi
    · rw [intVal_congr (fun i hi => hx₃ i hi), hval.2]
  · simp only [negBlockContract, payloadContract, negateContract, copyWordsContract,
      Expr.size_reg, Expr.size_const, Expr.size_bin, argsSize_cons, argsSize_nil,
      List.getD_cons_zero, List.getD_cons_succ]
    omega

/-- `addBlockBody` meets its contract. -/
theorem addBlock_meetsContract {w h K b addProc copyProc : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hb : p.procs[b]? = some (addBlockBody addProc copyProc))
    (hadd : MeetsContract w p addProc (addContract w h))
    (hcopy : MeetsContract w p copyProc (copyWordsContract w)) :
    MeetsContract w p b (addBlockContract w h K) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨x, d, heap, rfl, hxh, hdh, hvx, hvd⟩, hz, hroom⟩
  change ZeroFrom mem heap at hz
  change heap + 2 * K < 2 ^ w at hroom
  have hxw := hwords x (by simp)
  have hdw := hwords d (by simp)
  have hKw := hwords K (by simp)
  have hhw := hwords heap (by simp)
  apply runs_start_le
  unfold addBlockBody
  refine runs_seq_call_le hadd (vs := [x, d, K, heap]) (by eval_expr) (by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega) ?_ ?_
  · exact ⟨x, d, K, heap, rfl, ⟨x, d, K, 0, heap, rfl, hxh, hdh, by decide, hvx, hvd⟩, hz, by
      change heap + K < 2 ^ w; omega⟩
  intro v₁ mem₁ pos₁ hpost₁
  rcases hpost₁ with ⟨he₁, -, -, hf₁, hz₁, hl₁⟩
  change v₁ = heap + K at he₁
  change (∀ y < heap, mem₁ y = mem y) at hf₁
  change ListAt mem₁ heap (digits h K (unsignedVal mem x h K + unsignedVal mem d h K + 0))
    at hl₁
  rw [he₁] at hz₁
  have hval := addCarry_value hl₁
  refine runs_seq_call_le hcopy (vs := [heap, x, K]) (by eval_expr) (by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega) ⟨_, _, _, rfl, hw, by omega, by omega, Or.inl hxh⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨s₂, d₂, l₂, heq₂, -, hc₂, ho₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl⟩ := heq₂
  refine runs_seq_call_le hcopy (vs := [heap + K, heap, K]) (by eval_expr) (by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega) ⟨_, _, _, rfl, hw, by omega, by omega, Or.inl le_rfl⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨s₃, d₃, l₃, heq₃, -, hc₃, ho₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl⟩ := heq₃
  obtain ⟨hz₃, hx₃, hk₃⟩ := storeBack_facts hxh hz₁ hc₂ ho₂ hc₃ ho₃
  refine runs_ret_le (by eval_expr) ?_ ?_
  · show ZeroFrom mem₃ heap ∧ (∀ y < heap, ¬ (x ≤ y ∧ y < x + K) → mem₃ y = mem y) ∧
      Valid mem₃ x h K ∧ intVal mem₃ x h K = wrap h K (intVal mem x h K + intVal mem d h K)
    refine ⟨hz₃, fun y hy hn => (hk₃ y hy hn).trans (hf₁ y hy), ?_, ?_⟩
    · intro i hi; rw [hx₃ i hi]; exact hval.1 i hi
    · rw [intVal_congr (fun i hi => hx₃ i hi), hval.2]
      simp
  · simp only [addBlockContract, payloadContract, addContract, copyWordsContract,
      Expr.size_reg, Expr.size_const, Expr.size_bin, argsSize_cons, argsSize_nil,
      List.getD_cons_zero, List.getD_cons_succ]
    omega

/-- A call of `negBlock`, followed by `s`. -/
theorem runs_seq_negBlock {w h K f r : ℕ} {p : Program} {ω : ℕ → Bool} {ex ek eh : Expr}
    {s : Stmt} {st : State} {x heap k T : ℕ} {Q : Outcome → State → Prop}
    (hf : MeetsContract w p f (negBlockContract w h K))
    (hargs : evalArgs w st [ex, ek, eh] = some [x, K, heap]) (hxw : x < 2 ^ w) (hhw : heap < 2 ^ w)
    (hxh : x + K ≤ heap) (hv : Valid st.mem x h K) (hz : ZeroFrom st.mem heap)
    (hroom : heap + 2 * K < 2 ^ w)
    (hrest : ∀ mem', ZeroFrom mem' heap →
      (∀ y < heap, ¬ (x ≤ y ∧ y < x + K) → mem' y = st.mem y) → Valid mem' x h K →
      intVal mem' x h K = wrap h K (-intVal st.mem x h K) → ∀ v pos', ∃ o st' c,
        Runs w p ω s { mem := mem', regs := Function.update st.regs r v, pos := pos' } o st' c ∧
        Q o st' ∧ (k + argsSize [ex, ek, eh] + (80 * K + 80) + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f [ex, ek, eh]) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  refine runs_seq_call_le hf hargs (by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega)
    ⟨⟨x, heap, rfl, hxh, hv⟩, hz, hroom⟩ ?_
  rintro v mem' pos' ⟨hz', hfr, hv', hval⟩
  exact hrest mem' hz' hfr hv' hval v pos'

/-- A call of `addBlock`, followed by `s`. -/
theorem runs_seq_addBlock {w h K f r : ℕ} {p : Program} {ω : ℕ → Bool} {ex ed ek eh : Expr}
    {s : Stmt} {st : State} {x d heap k T : ℕ} {Q : Outcome → State → Prop}
    (hf : MeetsContract w p f (addBlockContract w h K))
    (hargs : evalArgs w st [ex, ed, ek, eh] = some [x, d, K, heap]) (hxw : x < 2 ^ w)
    (hdw : d < 2 ^ w) (hhw : heap < 2 ^ w)
    (hxh : x + K ≤ heap) (hdh : d + K ≤ heap) (hvx : Valid st.mem x h K)
    (hvd : Valid st.mem d h K) (hz : ZeroFrom st.mem heap) (hroom : heap + 2 * K < 2 ^ w)
    (hrest : ∀ mem', ZeroFrom mem' heap →
      (∀ y < heap, ¬ (x ≤ y ∧ y < x + K) → mem' y = st.mem y) → Valid mem' x h K →
      intVal mem' x h K = wrap h K (intVal st.mem x h K + intVal st.mem d h K) → ∀ v pos',
        ∃ o st' c,
        Runs w p ω s { mem := mem', regs := Function.update st.regs r v, pos := pos' } o st' c ∧
        Q o st' ∧ (k + argsSize [ex, ed, ek, eh] + (80 * K + 80) + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f [ex, ed, ek, eh]) s) st o st' c ∧ Q o st' ∧
      k + c ≤ T := by
  refine runs_seq_call_le hf hargs (by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega)
    ⟨⟨x, d, heap, rfl, hxh, hdh, hvx, hvd⟩, hz, hroom⟩ ?_
  rintro v mem' pos' ⟨hz', hfr, hv', hval⟩
  exact hrest mem' hz' hfr hv' hval v pos'

end MinCostFlow.LinkCut.Path
