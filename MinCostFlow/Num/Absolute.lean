module

public import MinCostFlow.Num.IsNegative
public import MinCostFlow.Num.Negate
public import MinCostFlow.Num.Copy
import MinCostFlow.Num.DivisionSigns
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Loading the unsigned magnitude of a signed block

Division first works on absolute values. A negative block is negated, and a nonnegative
block is copied. The output is interpreted as unsigned, so the signed minimum also has
its correct magnitude. This allocates `L` limbs and costs at most `36*L+40`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Arguments `[a, L, heap]`, followed by sign, negation, and copy entries. -/
def absoluteBody (sign neg copy : ℕ) : Stmt :=
  .call 3 sign [.reg 0, .reg 1] ;;
  .cond (.reg 3)
    (.call 4 neg [.reg 0, .reg 1, .reg 2] ;; .ret (.reg 4))
    (.call 4 copy [.reg 0, .reg 1, .reg 2] ;; .ret (.reg 4))

/-- Unsigned magnitude conversion and its linked helpers. -/
def absoluteModule (b h : ℕ) : List Stmt :=
  [absoluteBody (b + 1) (b + 2) (b + 4), isNegativeBody h] ++
    (negateModule (b + 2) h ++ copyModule (b + 4))

/-- Allocate the unsigned absolute value of the signed source, including its minimum. -/
def absoluteContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a L heap, args = [a, L, heap] ∧ a + L ≤ heap ∧ Valid mem a h L)
    (fun args mem mem' => Valid mem' (heapArg args) h (args.getD 1 0) ∧
      unsignedVal mem' (heapArg args) h (args.getD 1 0) =
        (intVal mem (args.getD 0 0) h (args.getD 1 0)).natAbs)
    (fun args _ => 36 * args.getD 1 0 + 40) (fun args _ => args.getD 1 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + args.getD 1 0 ∧ C.post args mem v mem' }

/-- Magnitude conversion and all its dependencies are deterministic. -/
theorem absoluteModule_noRand (b h : ℕ) : ∀ s ∈ absoluteModule b h, s.NoRand := by
  intro s hs
  simp only [absoluteModule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (rfl | rfl) | (hn | hc)
  · simp [absoluteBody, Stmt.NoRand]
  · exact isNegativeBody_noRand _
  · exact negateModule_noRand _ _ _ hn
  · have he : s = copyBody := by simpa only [copyModule, List.mem_singleton] using hc
    subst s
    exact copyBody_noRand

/-- Unsigned magnitude conversion meets its heap contract with linear cost. -/
theorem absolute_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt b (absoluteModule b h)) : MeetsContract w p b (absoluteContract w h) := by
  have hsign : p.HasAt (b + 1) (isNegativeModule (b + 1) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [absoluteModule, isNegativeModule, negateModule, copyModule] using hp 1 (by simp [absoluteModule, negateModule, copyModule])
  have hneg : p.HasAt (b + 2) (negateModule (b + 2) h) := by
    intro i hi
    have he : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases he with rfl | rfl
    · simpa [absoluteModule, negateModule, copyModule] using hp 2 (by simp [absoluteModule, negateModule, copyModule])
    · simpa [absoluteModule, negateModule, copyModule, Nat.add_assoc] using hp 3 (by simp [absoluteModule, negateModule, copyModule])
  have hcopy : p.HasAt (b + 4) (copyModule (b + 4)) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [absoluteModule, negateModule, copyModule] using hp 4 (by simp [absoluteModule, negateModule, copyModule])
  have hs := isNegative_meetsContract hh hw hb hsign
  have hn := negate_meetsContract hw hb hneg
  have hc := copy_meetsContract (h := h) hw hcopy
  have hentry : p.procs[b]? = some (absoluteBody (b + 1) (b + 2) (b + 4)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a, L, heap, rfl, ha, hv⟩, hz, hbound⟩
  change ZeroFrom mem heap at hz
  change heap + L < 2 ^ w at hbound
  have haw : a < 2 ^ w := hwords a (by simp)
  have hLw : L < 2 ^ w := hwords L (by simp)
  have hheapw : heap < 2 ^ w := hwords heap (by simp)
  apply runs_start_le
  unfold absoluteBody
  refine runs_seq_call_le hs (vs := [a, L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨a, L, rfl, by omega, hv⟩
  · intro sign mem' pos' hpst
    rcases hpst with ⟨hmem, hsign⟩
    subst mem'
    change sign = if intVal mem a h L < 0 then 1 else 0 at hsign
    refine runs_cond_le (v := sign) (by eval_expr) ?_ ?_
    · intro hnonzero
      have hnegative : intVal mem a h L < 0 := by
        by_contra he
        simp [he] at hsign
        omega
      refine runs_seq_call_le hn (vs := [a, L, heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨a, L, heap, rfl, ⟨⟨a, L, 1, heap, rfl, ha, le_rfl, hv⟩, hz, hbound⟩⟩
      · intro v mem' pos'' hpst
        rcases hpst with ⟨he, hlo, hhi, hf, hzero, hl⟩
        change v = heap + L at he
        change (∀ z < heap, mem' z = mem z) at hf
        change ListAt mem' heap (digits h L (capacity h L - 1 - unsignedVal mem a h L + 1)) at hl
        have hvalid := valid_listAt hl (digits_lt h L _)
        rw [digits_length] at hvalid
        have hvalue := negated_unsigned_abs hv hnegative hl
        have hvw : v < 2 ^ w := by omega
        refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
        · change v = heap + L ∧ heap ≤ v ∧ v ≤ heap + L ∧ (∀ z < heap, mem' z = mem z) ∧
            ZeroFrom mem' v ∧ Valid mem' heap h L ∧ unsignedVal mem' heap h L = (intVal mem a h L).natAbs
          exact ⟨he, by omega, by omega, hf, hzero, hvalid, hvalue⟩
        · simp only [absoluteContract, isNegativeContract, negateContract, negateCarryContract,
            heapContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg,
            argsSize_cons, argsSize_nil]
          omega
    · intro hzero
      have hnonnegative : ¬ intVal mem a h L < 0 := by
        intro he
        simp [he] at hsign
        omega
      refine runs_seq_call_le hc (vs := [a, L, heap]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨a, L, heap, rfl, ha, hv⟩, hz, hbound⟩
      · intro v mem' pos'' hpst
        rcases hpst with ⟨he, hlo, hhi, hf, hzero, hlimbs, hvalid, hvalue⟩
        change v = heap + L at he
        change (∀ z < heap, mem' z = mem z) at hf
        change (∀ i < L, mem' (heap + i) = mem (a + i)) at hlimbs
        change Valid mem' heap h L at hvalid
        have huint : unsignedVal mem' heap h L = unsignedVal mem a h L := unsignedVal_congr hlimbs
        have hvw : v < 2 ^ w := by omega
        refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
        · change v = heap + L ∧ heap ≤ v ∧ v ≤ heap + L ∧ (∀ z < heap, mem' z = mem z) ∧
            ZeroFrom mem' v ∧ Valid mem' heap h L ∧ unsignedVal mem' heap h L = (intVal mem a h L).natAbs
          exact ⟨he, by omega, by omega, hf, hzero, hvalid,
            huint.trans (unsignedVal_nonnegative_abs hv hnonnegative)⟩
        · simp only [absoluteContract, isNegativeContract, copyContract, heapContract,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, argsSize_cons, argsSize_nil]
          omega

end MinCostFlow.Num
