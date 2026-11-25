module

public import MinCostFlow.Num.LoadSmall
public import MinCostFlow.Num.Negate
public import MinCostFlow.Num.Copy
public import MinCostFlow.Num.SignedPair
public import MinCostFlow.Statement.Problem
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Loading an integer written as two words

`encodeSignedPair` stores a sign word and an absolute value. The loader takes these two words,
the requested limb count, and the heap pointer as arguments. It first loads the magnitude
into an `L`-limb scratch block. It then negates or copies that block into the next `L`
cells. The result starts at `heap + L`, and the returned pointer is `heap + 2*L`.
Overflow wraps modulo the block capacity. The cost is at most `59*L + 34`.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Decode a sign word and an absolute value. Canonical inputs are supplied by `encodeSignedPair`. -/
def decodeIntWords (sign magnitude : ℕ) : ℤ :=
  if sign = 0 then (magnitude : ℤ) else -(magnitude : ℤ)

/-- Decoding the two words of the problem's integer encoding recovers its integer. -/
theorem decodeIntWords_encodeInt (n : ℤ) :
    decodeIntWords (if n < 0 then 1 else 0) n.natAbs = n := by
  unfold decodeIntWords
  by_cases hn : n < 0
  · simp only [ite_eq_left hn, Nat.one_ne_zero, ↓reduceIte]
    rw [Int.natCast_natAbs, abs_of_neg hn]
    omega
  · simp only [ite_eq_right hn, ↓reduceIte]
    rw [Int.natCast_natAbs, abs_of_nonneg (by omega)]

/-- Arguments `[sign, magnitude, L, heap]`, followed by the three procedure entries. -/
def loadIntBody (load neg copy : ℕ) : Stmt :=
  .call 4 load [.reg 1, .reg 2, .reg 3] ;;
  .cond (.reg 0)
    (.call 5 neg [.reg 3, .reg 2, .reg 4] ;; .ret (.reg 5))
    (.call 5 copy [.reg 3, .reg 2, .reg 4] ;; .ret (.reg 5))

/-- The integer loader, magnitude loader, negation module, and copy procedure. -/
def loadIntModule (b h : ℕ) : List Stmt :=
  [loadIntBody (b + 1) (b + 2) (b + 4), loadSmallBody (b + 1) h] ++
    negateModule (b + 2) h ++ [copyBody]

/-- Load canonical `encodeSignedPair` words. The scratch block starts at the old heap,
and the signed result starts `L` cells later. -/
def loadIntContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ n : ℤ, ∃ L heap, args = encodeSignedPair n ++ [L, heap])
    (fun args _ mem' =>
      Valid mem' (heapArg args + args.getD 2 0) h (args.getD 2 0) ∧
      intVal mem' (heapArg args + args.getD 2 0) h (args.getD 2 0) =
        wrap h (args.getD 2 0) (decodeIntWords (args.getD 0 0) (args.getD 1 0)))
    (fun args _ => 59 * args.getD 2 0 + 34) (fun args _ => 2 * args.getD 2 0)
  { C with post := fun args mem v mem' =>
      v = heapArg args + 2 * args.getD 2 0 ∧ C.post args mem v mem' }

/-- Every body in the integer-loading module has no random statement. -/
theorem loadIntModule_noRand (b h : ℕ) : ∀ s ∈ loadIntModule b h, s.NoRand := by
  intro s hs
  simp only [loadIntModule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with ((rfl | rfl) | hn) | rfl
  · simp [loadIntBody, Stmt.NoRand]
  · exact loadSmallBody_noRand _ _
  · exact negateModule_noRand _ _ _ hn
  · exact copyBody_noRand

/-- Loading an encoded integer meets its heap contract in at most `59*L + 34` steps. -/
theorem loadInt_meetsContract {w h b : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.HasAt b (loadIntModule b h)) :
    MeetsContract w p b (loadIntContract w h) := by
  have hload : p.HasAt (b + 1) (loadSmallModule (b + 1) h) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [loadIntModule, loadSmallModule] using hp 1 (by simp [loadIntModule, negateModule])
  have hneg : p.HasAt (b + 2) (negateModule (b + 2) h) := by
    intro i hi
    have he : i = 0 ∨ i = 1 := by change i < 2 at hi; omega
    rcases he with rfl | rfl
    · simpa [loadIntModule, negateModule] using hp 2 (by simp [loadIntModule, negateModule])
    · simpa [loadIntModule, negateModule, Nat.add_assoc] using hp 3 (by simp [loadIntModule, negateModule])
  have hcopy : p.HasAt (b + 4) (copyModule (b + 4)) := by
    intro i hi
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa [loadIntModule, negateModule, copyModule] using hp 4 (by simp [loadIntModule, negateModule])
  have hl := loadSmall_meetsContract hw hb hload
  have hn := negate_meetsContract hw hb hneg
  have hc := copy_meetsContract (h := h) hw hcopy
  have hentry : p.procs[b]? = some (loadIntBody (b + 1) (b + 2) (b + 4)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨n, L, heap, rfl⟩, hz, hbound⟩
  change ZeroFrom mem heap at hz
  change heap + 2 * L < 2 ^ w at hbound
  change ∀ x ∈ [if n < 0 then 1 else 0, n.natAbs, L, heap], x < 2 ^ w at hwords
  have hm : n.natAbs < 2 ^ w := hwords _ (by simp)
  have hL : L < 2 ^ w := hwords _ (by simp)
  have hh : heap < 2 ^ w := hwords _ (by simp)
  apply runs_start_le
  unfold loadIntBody
  refine runs_seq_call_le hl (vs := [n.natAbs, L, heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨⟨n.natAbs, L, heap, rfl⟩, hz, by change heap + L < 2 ^ w; omega⟩
  · intro v₁ mem₁ pos₁ hpost₁
    rcases hpost₁ with ⟨he₁, hlo₁, hhi₁, hf₁, hz₁, hl₁⟩
    change v₁ = heap + L at he₁
    change (∀ x < heap, mem₁ x = mem x) at hf₁
    change ListAt mem₁ heap (digits h L n.natAbs) at hl₁
    have hv := loadSmall_value hl₁
    have hv₁w : v₁ < 2 ^ w := by omega
    refine runs_cond_le (by eval_expr) ?_ ?_
    · intro hsign
      have hnegative : n < 0 := by
        by_contra he
        simp [he, encodeSignedPair] at hsign
      refine runs_seq_call_le hn (vs := [heap, L, v₁]) (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨heap, L, v₁, rfl, ?_⟩
        exact ⟨⟨heap, L, 1, v₁, rfl, by omega, le_rfl, hv.1⟩, hz₁,
          by change v₁ + L < 2 ^ w; omega⟩
      · intro v₂ mem₂ pos₂ hpost₂
        rcases hpost₂ with ⟨he₂, hlo₂, hhi₂, hf₂, hz₂, hl₂⟩
        change v₂ = v₁ + L at he₂
        change (∀ x < v₁, mem₂ x = mem₁ x) at hf₂
        change ListAt mem₂ v₁ (digits h L (capacity h L - 1 - unsignedVal mem₁ heap h L + 1)) at hl₂
        have hout := negateCarry_value_one hv.1 hl₂
        have hv₂w : v₂ < 2 ^ w := by omega
        refine runs_ret_le (v := v₂) (by eval_expr) ?_ ?_
        · refine ⟨by change v₂ = heap + 2 * L; omega, ?_⟩
          change heap ≤ v₂ ∧ v₂ ≤ heap + 2 * L ∧ (∀ x < heap, mem₂ x = mem x) ∧
            ZeroFrom mem₂ v₂ ∧ Valid mem₂ (heap + L) h L ∧
              intVal mem₂ (heap + L) h L = wrap h L (decodeIntWords (if n < 0 then 1 else 0) n.natAbs)
          refine ⟨by omega, by omega, ?_, hz₂, he₁ ▸ hout.1, ?_⟩
          · intro x hx
            rw [hf₂ x (by omega), hf₁ x hx]
          · rw [← he₁, hout.2, hv.2.2, ← wrap_natCast, wrap_neg_wrap]
            simp only [decodeIntWords, ite_eq_left hnegative, Nat.one_ne_zero, ↓reduceIte]
        · simp only [loadIntContract, loadSmallContract, negateContract, negateCarryContract,
            heapContract, encodeSignedPair, List.cons_append, List.nil_append,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, argsSize_cons, argsSize_nil]
          omega
    · intro hsign
      have hnonnegative : ¬ n < 0 := by
        intro he
        simp [he, encodeSignedPair] at hsign
      refine runs_seq_call_le hc (vs := [heap, L, v₁]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨⟨heap, L, v₁, rfl, by omega, hv.1⟩, hz₁,
          by change v₁ + L < 2 ^ w; omega⟩
      · intro v₂ mem₂ pos₂ hpost₂
        rcases hpost₂ with ⟨he₂, hlo₂, hhi₂, hf₂, hz₂, hlimbs, hvalid, hvalue⟩
        change v₂ = v₁ + L at he₂
        change (∀ x < v₁, mem₂ x = mem₁ x) at hf₂
        change Valid mem₂ v₁ h L at hvalid
        change intVal mem₂ v₁ h L = intVal mem₁ heap h L at hvalue
        have hv₂w : v₂ < 2 ^ w := by omega
        refine runs_ret_le (v := v₂) (by eval_expr) ?_ ?_
        · refine ⟨by change v₂ = heap + 2 * L; omega, ?_⟩
          change heap ≤ v₂ ∧ v₂ ≤ heap + 2 * L ∧ (∀ x < heap, mem₂ x = mem x) ∧
            ZeroFrom mem₂ v₂ ∧ Valid mem₂ (heap + L) h L ∧
              intVal mem₂ (heap + L) h L = wrap h L (decodeIntWords (if n < 0 then 1 else 0) n.natAbs)
          refine ⟨by omega, by omega, ?_, hz₂, he₁ ▸ hvalid, ?_⟩
          · intro x hx
            rw [hf₂ x (by omega), hf₁ x hx]
          · rw [← he₁, hvalue, hv.2.2]
            simp only [decodeIntWords, ite_eq_right hnonnegative, ↓reduceIte, wrap_natCast]
        · simp only [loadIntContract, loadSmallContract, copyContract,
            heapContract, encodeSignedPair, List.cons_append, List.nil_append,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, argsSize_cons, argsSize_nil]
          omega

/-- The canonical input words yield the wrapped input integer. -/
theorem loadInt_value {w h L heap v : ℕ} {n : ℤ} {mem mem' : ℕ → ℕ}
    (hp : (loadIntContract w h).post (encodeSignedPair n ++ [L, heap]) mem v mem') :
    intVal mem' (heap + L) h L = wrap h L n := by
  have he := hp.2.2.2.2.2.2
  change intVal mem' (heap + L) h L =
    wrap h L (decodeIntWords (if n < 0 then 1 else 0) n.natAbs) at he
  simpa only [decodeIntWords_encodeInt] using he

/-- When the input fits, loading its canonical words is exact. -/
theorem loadInt_value_of_fits {w h L heap v : ℕ} {n : ℤ} {mem mem' : ℕ → ℕ}
    (hp : (loadIntContract w h).post (encodeSignedPair n ++ [L, heap]) mem v mem')
    (hn : Fits h L n) : intVal mem' (heap + L) h L = n := by
  rw [loadInt_value hp, wrap_of_fits hn]

end MinCostFlow.Num
