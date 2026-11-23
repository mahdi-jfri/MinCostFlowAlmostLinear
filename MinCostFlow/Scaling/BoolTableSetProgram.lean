module

public import MinCostFlow.Scaling.BoolTableLayout
import WordRAM.Tactic

/-!
# Updating one traversal flag

Both traversals mark or clear one vertex at a time. This one-store
procedure writes its zero/one flag, computes the exact Boolean-vector
update, and preserves every other memory cell. It allocates no words,
uses no random instruction, and costs at most twelve steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[table,vertex,flagWord]`. -/
def boolTableSetBody : Stmt :=
  .store (.bin .add (.reg 0) (.reg 1)) (.reg 2) ;; .ret (.const 0)

/-- A flag update occupies one procedure slot. -/
def boolTableSetModule : List Stmt := [boolTableSetBody]

/-- The input word is the requested Boolean's canonical zero/one encoding. -/
def boolTableSetContract (w : ℕ) {n : ℕ} (flags : Fin n → Bool) (v : Fin n) (value : Bool) : Contract where
  pre args mem := ∃ a, args = [a, v.val, value.toNat] ∧ BoolTableAt mem a flags ∧ a+n < 2 ^ w
  post args mem ret mem' := ret = 0 ∧
    BoolTableAt mem' (args.getD 0 0) (Function.update flags v value) ∧
    ∀ x, x ≠ args.getD 0 0+v.val → mem' x = mem x
  cost _ _ := 12

/-- A single flag store uses no random instructions. -/
theorem boolTableSetBody_noRand : boolTableSetBody.NoRand := by
  simp only [boolTableSetBody, Stmt.NoRand, and_self]

/-- The one-store procedure computes exactly the requested Boolean update
with a complete frame on every other cell and constant cost. -/
theorem boolTableSet_meetsContract {w b n : ℕ} {p : Program}
    (hp : p.HasAt b boolTableSetModule) (flags : Fin n → Bool) (v : Fin n) (value : Bool) :
    MeetsContract w p b (boolTableSetContract w flags v value) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, rfl, hat, hspace⟩ := hpre
  have hv := v.isLt
  have ha : a < 2 ^ w := by omega
  have hvword : v.val < 2 ^ w := by omega
  have hcell : a+v.val < 2 ^ w := by omega
  have hvalue : value.toNat < 2 ^ w := hwords _ (by simp)
  have hzero : 0 < 2 ^ w := Nat.two_pow_pos _
  apply runs_start_le
  unfold boolTableSetBody
  wram_step
  refine runs_ret_le (v := 0) (by eval_expr) ?_ ?_
  · change 0 = 0 ∧ BoolTableAt (Function.update mem (a+v.val) value.toNat) a (Function.update flags v value) ∧
      ∀ x, x ≠ a+v.val → Function.update mem (a+v.val) value.toNat x = mem x
    refine ⟨rfl, ?_, fun x hx => Function.update_of_ne hx _ _⟩
    apply hat.update v value (heap := a+n) le_rfl (Function.update_self _ _ _)
    intro x _ hx
    exact Function.update_of_ne hx _ _
  · simp only [boolTableSetContract, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega

/-- Every flag vector and valid vertex have simultaneous layout and word
premises for both Boolean values. -/
theorem exists_boolTableSet_pre {n : ℕ} (flags : Fin n → Bool) (v : Fin n) (value : Bool) :
    ∃ w mem, (∀ x ∈ [0, v.val, value.toNat], x < 2 ^ w) ∧
      (boolTableSetContract w flags v value).pre [0, v.val, value.toNat] mem := by
  obtain ⟨mem, hat, _⟩ := exists_boolTableAt flags
  let w := n+3
  have hw : n+3 < 2 ^ w := Nat.lt_two_pow_self
  have hv := v.isLt
  refine ⟨w, mem, ?_, 0, rfl, hat, by omega⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · omega
  · omega
  · cases value <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

end MinCostFlow.Scaling.Machine
