module

public import MinCostFlow.MinRatio.PathPayloadLayout
public import MinCostFlow.Num.Absolute
import WordRAM.Tactic

/-!
# Preparing a tag for routing flow

Algorithm 2 (page 29) routes a signed flow increment and adds its
absolute value to the detection account. This procedure makes the
two-block argument for one path update from a single signed block.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Arguments are the signed increment, limb count, and heap. -/
def pathFlowTagBody (copy absolute : ℕ) : Stmt :=
  .call 3 copy [.reg 0, .reg 1, .reg 2] ;;
  .call 4 absolute [.reg 0, .reg 1, .reg 3] ;;
  .ret (.reg 4)

/-- The two blocks hold the signed increment and its absolute value. -/
def pathFlowTagContract (w h : ℕ) (delta : ℤ) : Contract where
  pre args mem := ∃ a L heap, args = [a, L, heap] ∧ a + L ≤ heap ∧
    PathIntAt mem a h L delta ∧ Num.Fits h L |delta| ∧
    ZeroFrom mem heap ∧ heap + 2 * L < 2 ^ w
  post args mem ret mem' :=
    ret = heapArg args + 2 * args.getD 1 0 ∧
    PathTagAt mem' (heapArg args) h (args.getD 1 0) (PathTag.ofFlow delta) ∧
    (∀ x < heapArg args, mem' x = mem x) ∧ ZeroFrom mem' ret
  cost args _ := 53 * args.getD 1 0 + 64

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- The path-tag wrapper uses no random instructions. -/
theorem pathFlowTagBody_noRand (copy absolute : ℕ) :
    (pathFlowTagBody copy absolute).NoRand := by
  simp [pathFlowTagBody, Stmt.NoRand]

/-- A fitting signed magnitude gives the exact path tag in `2 * L`
words and at most `53 * L + 64` steps. -/
theorem pathFlowTag_meetsContract {w h entry copy absolute : ℕ} {p : Program}
    (delta : ℤ) (hp : p.HasAt entry [pathFlowTagBody copy absolute])
    (hc : MeetsContract w p copy (Num.copyContract w h))
    (ha : MeetsContract w p absolute (Num.absoluteContract w h)) :
    MeetsContract w p entry (pathFlowTagContract w h delta) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, L, heap, rfl, hsrc, hdelta, hfit, hz, hh⟩ := hpre
  have haw := hwords a (by simp)
  have hLw := hwords L (by simp)
  have hheapw := hwords heap (by simp)
  apply runs_start_le
  unfold pathFlowTagBody
  refine runs_seq_call_le hc (vs := [a, L, heap]) (by eval_expr) hwords ?_ ?_
  · exact ⟨⟨a, L, heap, rfl, hsrc, hdelta.1⟩, hz, by
      change heap + L < 2 ^ w
      omega⟩
  · intro ptr mem₁ pos₁ hpost
    obtain ⟨hptr, _, _, hf, hz₁, _, hvalid, hval⟩ := hpost
    change ptr = heap + L at hptr
    change (∀ x < heap, mem₁ x = mem x) at hf
    have hptrw : ptr < 2 ^ w := by omega
    have hdelta₁ := hdelta.congr (mem' := mem₁) (fun i hi => hf _ (by omega))
    have hcopied : PathIntAt mem₁ heap h L delta := ⟨hvalid, hval.trans hdelta.2⟩
    refine runs_seq_call_le ha (vs := [a, L, ptr]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨a, L, ptr, rfl, by omega, hdelta₁.1⟩, hz₁, by
        change ptr + L < 2 ^ w
        omega⟩
    · intro ret mem₂ pos₂ hpost₂
      obtain ⟨hret, _, _, hf₂, hz₂, habsValid, habs⟩ := hpost₂
      change ret = ptr + L at hret
      change (∀ x < ptr, mem₂ x = mem₁ x) at hf₂
      change Num.unsignedVal mem₂ ptr h L = (Num.intVal mem₁ a h L).natAbs at habs
      rw [hdelta₁.2] at habs
      have habsSigned : PathIntAt mem₂ ptr h L |delta| := by
        refine ⟨habsValid, ?_⟩
        rw [Num.intVal, habs]
        unfold Num.signedVal
        have hzpos : 2 * delta.natAbs < Num.capacity h L := by
          have hhi := hfit.2
          rw [← Int.natCast_natAbs] at hhi
          exact_mod_cast hhi
        rw [ite_eq_right (not_le_of_gt hzpos), sub_zero, Int.natCast_natAbs]
      have hfirst := hcopied.congr (mem' := mem₂) (fun i hi => hf₂ _ (by omega))
      have htag : PathTagAt mem₂ heap h L (PathTag.ofFlow delta) := by
        exact ⟨hfirst, hptr ▸ habsSigned⟩
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · exact ⟨by change ret = heap + 2 * L; omega, htag,
          fun x hx => (hf₂ x (by change x < heap at hx; omega)).trans (hf x hx), hz₂⟩
      · simp only [Num.copyContract, Num.absoluteContract, pathFlowTagContract, heapContract,
          Expr.size_reg, List.getD_cons_succ, List.getD_cons_zero, argsSize_cons, argsSize_nil]
        omega

end MinCostFlow.MinRatio
