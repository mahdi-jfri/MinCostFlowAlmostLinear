module

public import MinCostFlow.MinRatio.PathPayloadLayout
public import MinCostFlow.Num.FixedMultiply
public import MinCostFlow.Num.LoadInt
import WordRAM.Tactic
import Mathlib.Tactic.Ring

/-!
# Scaling a grouped cycle coefficient

Algorithm 2 (page 29) scales the circulation before updating the
flow and detector. For an explicit edge, the multiplier's fixed-point
numerator is multiplied by the edge's net integer traversal count.
The shared multiplier uses precision zero for this product because
the count has no fractional bits.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- A signed count and a multiplier numerator are valid inputs to the
shared fixed-point multiplier at precision zero. -/
theorem offTreeScale_pre {w h a c L heap : ℕ} {mem : ℕ → ℕ} {num count : ℤ}
    (ha : a + L ≤ heap) (hc : c + L ≤ heap)
    (hnum : PathIntAt mem a h L num) (hcount : PathIntAt mem c h L count)
    (hz : ZeroFrom mem heap) (hspace : heap + (11 * L + 1) < 2 ^ w) :
    (Num.fixedMultiplyContract w h).pre [a, c, L, 0, heap] mem :=
  ⟨⟨a, c, L, 0, heap, rfl, dvd_zero h, ha, hc, hnum.1, hcount.1⟩, hz, hspace⟩

/-- The exact scaled numerator occupies the last limb block allocated
by the multiplier, ready for the signed and absolute tag writer. -/
theorem offTreeScale_post {w h a c L heap ret : ℕ} {mem mem' : ℕ → ℕ}
    {num count : ℤ} (hnum : PathIntAt mem a h L num)
    (hcount : PathIntAt mem c h L count) (hfit : Num.Fits h L (num * count))
    (hp : (Num.fixedMultiplyContract w h).post [a, c, L, 0, heap] mem ret mem') :
    ret = heap + (11 * L + 1) ∧
      PathIntAt mem' (heap + 10 * L + 1) h L (num * count) := by
  have hf : Num.Fits h L ((Num.intVal mem a h L * Num.intVal mem c h L) / (2 : ℤ) ^ (0 : ℕ)) := by
    simpa only [hnum.2, hcount.2, pow_zero, Int.ediv_one] using hfit
  refine ⟨hp.1, hp.2.2.2.2.2.1, ?_⟩
  simpa only [hnum.2, hcount.2, pow_zero, Int.ediv_one] using
    Num.fixedMultiply_value_of_fits hp hf

/-- The raw integer product represents the real fixed-point multiplier
times the integer traversal count, at the original precision. -/
theorem offTreeScale_fixVal {h L P a b : ℕ} {mem mem' : ℕ → ℕ} {num count : ℤ}
    (hn : PathIntAt mem a h L num) (hp : PathIntAt mem' b h L (num * count)) :
    Num.fixVal mem' b h L P = Num.fixVal mem a h L P * (count : ℝ) := by
  rw [Num.fixVal, Num.fixVal, hn.2, hp.2, Int.cast_mul]
  ring

/-- Load the signed count and multiply the fixed-point numerator by it.
The arguments give the numerator address, sign, magnitude, limb count,
and heap pointer. -/
@[expose] def offTreeScaleBody (load scale : ℕ) : Stmt :=
  .call 5 load [.reg 1, .reg 2, .reg 3, .reg 4] ;;
  .call 6 scale [.reg 0, .bin .add (.reg 4) (.reg 3), .reg 3, .const 0, .reg 5] ;;
  .ret (.reg 6)

/-- The block immediately before the returned heap holds the scaled numerator. -/
@[expose] def offTreeScaleContract (w h : ℕ) (num count : ℤ) : Contract where
  pre args mem := ∃ a L heap, args = a :: (encodeInt count ++ [L, heap]) ∧
    a + L ≤ heap ∧ PathIntAt mem a h L num ∧ Num.Fits h L count ∧
    Num.Fits h L (num * count) ∧ ZeroFrom mem heap ∧ heap + (13 * L + 1) < 2 ^ w
  post args mem ret mem' :=
    let L := args.getD 3 0
    let heap := heapArg args
    ret = heap + (13 * L + 1) ∧
      PathIntAt mem' (heap + 12 * L + 1) h L (num * count) ∧
      (∀ x < heap, mem' x = mem x) ∧ ZeroFrom mem' ret
  cost args _ := 152 * (args.getD 3 0)^2 + 398 * args.getD 3 0 + 310

/-- Scaling a count is deterministic when the linked numeric routines are. -/
theorem offTreeScaleBody_noRand (load scale : ℕ) : (offTreeScaleBody load scale).NoRand := by
  simp [offTreeScaleBody, Stmt.NoRand]

/-- The loader and multiplier compute the fitting product and preserve
the previous heap contents in at most `152 * L^2 + 398 * L + 310` steps. -/
theorem offTreeScale_meetsContract {w h entry load scale : ℕ} {p : Program}
    (num count : ℤ) (hp : p.HasAt entry [offTreeScaleBody load scale])
    (hl : MeetsContract w p load (Num.loadIntContract w h))
    (hs : MeetsContract w p scale (Num.fixedMultiplyContract w h)) :
    MeetsContract w p entry (offTreeScaleContract w h num count) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, L, heap, rfl, ha, hn, hc, hf, hz, hroom⟩ := hpre
  let sign : ℕ := if count < 0 then 1 else 0
  have hw : ∀ x ∈ [a, sign, count.natAbs, L, heap], x < 2 ^ w := hwords
  have haw := hw a (by simp)
  have hwL := hw L (by simp)
  have hwh := hw heap (by simp)
  have hwc : heap + L < 2 ^ w := by omega
  apply runs_start_le
  unfold offTreeScaleBody
  refine runs_seq_call_le hl (vs := [sign, count.natAbs, L, heap]) (by eval_expr)
    (fun x hx => hw x (List.mem_cons_of_mem _ hx)) ?_ ?_
  · exact ⟨⟨count, L, heap, rfl⟩, hz, by change heap + 2 * L < 2 ^ w; omega⟩
  · intro ptr mem₁ pos₁ hpost
    have hptr : ptr = heap + 2 * L := hpost.1
    have hframe : ∀ x < heap, mem₁ x = mem x := hpost.2.2.2.1
    have hzero : ZeroFrom mem₁ ptr := hpost.2.2.2.2.1
    have hav : PathIntAt mem₁ a h L num := hn.congr (fun i hi => hframe _ (by omega))
    have hcv : PathIntAt mem₁ (heap + L) h L count :=
      ⟨hpost.2.2.2.2.2.1, Num.loadInt_value_of_fits hpost hc⟩
    have hptrw : ptr < 2 ^ w := by omega
    refine runs_seq_call_le hs (vs := [a, heap + L, L, 0, ptr])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact offTreeScale_pre (by omega) (by omega) hav hcv hzero (by omega)
    · intro ret mem₂ pos₂ hres
      obtain ⟨hret, hvalue⟩ := offTreeScale_post hav hcv hf hres
      have hretw : ret < 2 ^ w := by omega
      have hframe₂ : ∀ x < ptr, mem₂ x = mem₁ x := hres.2.2.2.1
      have hzero₂ : ZeroFrom mem₂ ret := hres.2.2.2.2.1
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change ret = heap + (13 * L + 1) ∧
          PathIntAt mem₂ (heap + 12 * L + 1) h L (num * count) ∧
          (∀ x < heap, mem₂ x = mem x) ∧ ZeroFrom mem₂ ret
        exact ⟨by omega, (show ptr + 10 * L + 1 = heap + 12 * L + 1 by omega) ▸ hvalue,
          fun x hx => (hframe₂ x (by omega)).trans (hframe x hx), hzero₂⟩
      · simp only [offTreeScaleContract, Num.loadIntContract, Num.fixedMultiplyContract,
          heapContract, encodeInt, List.cons_append, List.nil_append,
          List.getD_cons_zero, List.getD_cons_succ, Expr.size_bin, Expr.size_reg,
          Expr.size_const, argsSize_cons, argsSize_nil]
        rw [show (2 * L) * (38 * (2 * L) + 35) = 152 * L^2 + 70 * L by ring]
        omega

end MinCostFlow.MinRatio
