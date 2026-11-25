module

public import MinCostFlow.MinRatio.OffTreeScale
public import MinCostFlow.MinRatio.PathFlowTag
public import MinCostFlow.MinRatio.OffTreeFlow
import WordRAM.Tactic

/-!
# Preparing an off-tree edge update

Algorithm 2 (page 29) applies the normalized signed flow change and
tracks its absolute value. For an explicit edge, scale its net count
first so that opposite occurrences cancel before taking the absolute value.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Scale the given edge count and write the signed and absolute blocks. -/
@[expose] def offTreeTagBody (scale tag : ℕ) : Stmt :=
  .call 5 scale [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
  .call 6 tag [.bin .sub (.reg 5) (.reg 3), .reg 3, .reg 5] ;;
  .ret (.reg 6)

/-- The tag starts after the scaling workspace and uses two limb blocks. -/
@[expose] def offTreeTagContract (w h : ℕ) (num count : ℤ) : Contract where
  pre args mem := ∃ a L heap, args = a :: (encodeSignedPair count ++ [L, heap]) ∧
    a + L ≤ heap ∧ PathIntAt mem a h L num ∧ Num.Fits h L count ∧
    Num.Fits h L (num * count) ∧ Num.Fits h L |num * count| ∧
    ZeroFrom mem heap ∧ heap + (15 * L + 1) < 2 ^ w
  post args mem ret mem' :=
    let L := args.getD 3 0
    let heap := heapArg args
    ret = heap + (15 * L + 1) ∧
      PathTagAt mem' (heap + (13 * L + 1)) h L (PathTag.ofFlow (num * count)) ∧
      (∀ x < heap, mem' x = mem x) ∧ ZeroFrom mem' ret
  cost args _ := 152 * (args.getD 3 0)^2 + 451 * args.getD 3 0 + 402

/-- The wrapper uses deterministic calls. -/
theorem offTreeTagBody_noRand (scale tag : ℕ) : (offTreeTagBody scale tag).NoRand := by
  simp [offTreeTagBody, Stmt.NoRand]

/-- The linked scaling and tag routines produce both exact increments
while preserving the earlier heap cells. -/
theorem offTreeTag_meetsContract {w h entry scale tag : ℕ} {p : Program}
    (num count : ℤ) (hp : p.HasAt entry [offTreeTagBody scale tag])
    (hs : MeetsContract w p scale (offTreeScaleContract w h num count))
    (ht : MeetsContract w p tag (pathFlowTagContract w h (num * count))) :
    MeetsContract w p entry (offTreeTagContract w h num count) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, L, heap, rfl, ha, hn, hc, hf, habs, hz, hroom⟩ := hpre
  let sign : ℕ := if count < 0 then 1 else 0
  have hw : ∀ x ∈ [a, sign, count.natAbs, L, heap], x < 2 ^ w := hwords
  have hwL := hw L (by simp)
  apply runs_start_le
  unfold offTreeTagBody
  refine runs_seq_call_le hs (vs := [a, sign, count.natAbs, L, heap]) (by eval_expr) hw ?_ ?_
  · exact ⟨a, L, heap, rfl, ha, hn, hc, hf, hz, by omega⟩
  · intro ptr mem₁ pos₁ hpost
    have hptr : ptr = heap + (13 * L + 1) := hpost.1
    have hv : PathIntAt mem₁ (heap + 12 * L + 1) h L (num * count) := hpost.2.1
    have hframe : ∀ x < heap, mem₁ x = mem x := hpost.2.2.1
    have hz₁ : ZeroFrom mem₁ ptr := hpost.2.2.2
    have hpw : ptr < 2 ^ w := by omega
    have haddr : ptr - L = heap + 12 * L + 1 := by omega
    have hsrcw : ptr - L < 2 ^ w := by omega
    refine runs_seq_call_le ht (vs := [ptr - L, L, ptr]) (by eval_expr)
      (by wram_words) ?_ ?_
    · exact ⟨ptr - L, L, ptr, rfl, by omega, haddr.symm ▸ hv, habs, hz₁, by omega⟩
    · intro ret mem₂ pos₂ hres
      have hret : ret = ptr + 2 * L := hres.1
      have hretw : ret < 2 ^ w := by omega
      have htag : PathTagAt mem₂ ptr h L (PathTag.ofFlow (num * count)) := hres.2.1
      have hframe₂ : ∀ x < ptr, mem₂ x = mem₁ x := hres.2.2.1
      have hz₂ : ZeroFrom mem₂ ret := hres.2.2.2
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change ret = heap + (15 * L + 1) ∧
          PathTagAt mem₂ (heap + (13 * L + 1)) h L (PathTag.ofFlow (num * count)) ∧
          (∀ x < heap, mem₂ x = mem x) ∧ ZeroFrom mem₂ ret
        exact ⟨by omega, hptr ▸ htag, fun x hx => (hframe₂ x (by omega)).trans (hframe x hx), hz₂⟩
      · simp only [offTreeTagContract, offTreeScaleContract, pathFlowTagContract, encodeSignedPair,
          List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_bin, Expr.size_reg, argsSize_cons, argsSize_nil]
        omega

/-- Prepare the tag and apply its two increments to the explicit edge. -/
@[expose] def offTreeCountUpdateBody (tag flow : ℕ) : Stmt :=
  .call 6 tag [.reg 1, .reg 2, .reg 3, .reg 4, .reg 5] ;;
  .call 7 flow [.reg 0, .bin .sub (.reg 6) (.bin .mul (.const 2) (.reg 4)), .reg 4, .reg 6] ;;
  .ret (.reg 7)

/-- The grouped update changes only the selected edge's account blocks
below the incoming heap. -/
@[expose] def offTreeCountUpdateContract (w h : ℕ) (value : PathEdgeValue)
    (num count : ℤ) : Contract where
  pre args mem := ∃ edge a L heap, args = edge :: a :: (encodeSignedPair count ++ [L, heap]) ∧
    2 < 2 ^ w ∧ edge + 2 + 4 * L ≤ heap ∧ PathEdgeAt mem edge h L (some value) ∧
    a + L ≤ heap ∧ PathIntAt mem a h L num ∧ Num.Fits h L count ∧
    Num.Fits h L (num * count) ∧ Num.Fits h L |num * count| ∧
    Num.Fits h L (value.flow + num * count) ∧ Num.Fits h L (value.detector + |num * count|) ∧
    ZeroFrom mem heap ∧ heap + (17 * L + 1) < 2 ^ w
  post args mem ret mem' :=
    let edge := args.getD 0 0
    let L := args.getD 4 0
    let heap := heapArg args
    ret = heap + (17 * L + 1) ∧
      PathEdgeAt mem' edge h L (some (value.shift (PathTag.ofFlow (num * count)))) ∧
      (∀ x < heap, x < edge + 2 + 2 * L ∨ edge + 2 + 4 * L ≤ x → mem' x = mem x) ∧
      ZeroFrom mem' ret
  cost args _ := 152 * (args.getD 4 0)^2 + 561 * args.getD 4 0 + 533

/-- The grouped update uses deterministic calls. -/
theorem offTreeCountUpdateBody_noRand (tag flow : ℕ) :
    (offTreeCountUpdateBody tag flow).NoRand := by
  simp [offTreeCountUpdateBody, Stmt.NoRand]

/-- The grouped update applies both fitting increments in place, using
at most `152 * L^2 + 561 * L + 533` steps. -/
theorem offTreeCountUpdate_meetsContract {w h entry tag flow : ℕ} {p : Program}
    (value : PathEdgeValue) (num count : ℤ)
    (hp : p.HasAt entry [offTreeCountUpdateBody tag flow])
    (ht : MeetsContract w p tag (offTreeTagContract w h num count))
    (hf : MeetsContract w p flow (offTreeFlowContract w h value (PathTag.ofFlow (num * count)))) :
    MeetsContract w p entry (offTreeCountUpdateContract w h value num count) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨edge, a, L, heap, rfl, hw, he, hv, ha, hn, hc, hprod, habs, hflow, hdet, hz, hroom⟩ := hpre
  let sign : ℕ := if count < 0 then 1 else 0
  have hwargs : ∀ x ∈ [edge, a, sign, count.natAbs, L, heap], x < 2 ^ w := hwords
  have hew := hwargs edge (by simp)
  have hLw := hwargs L (by simp)
  have h2Lw : 2 * L < 2 ^ w := by omega
  apply runs_start_le
  unfold offTreeCountUpdateBody
  refine runs_seq_call_le ht (vs := [a, sign, count.natAbs, L, heap]) (by eval_expr)
    (fun x hx => hwargs x (List.mem_cons_of_mem _ hx)) ?_ ?_
  · exact ⟨a, L, heap, rfl, ha, hn, hc, hprod, habs, hz, by omega⟩
  · intro ptr mem₁ pos₁ htagpost
    have hptr : ptr = heap + (15 * L + 1) := htagpost.1
    have htag : PathTagAt mem₁ (heap + (13 * L + 1)) h L (PathTag.ofFlow (num * count)) :=
      htagpost.2.1
    have hframe : ∀ x < heap, mem₁ x = mem x := htagpost.2.2.1
    have hz₁ : ZeroFrom mem₁ ptr := htagpost.2.2.2
    have hv₁ := hv.congr (mem' := mem₁) (fun x _ hx => hframe x (by omega))
    have hpw : ptr < 2 ^ w := by omega
    have haddr : ptr - 2 * L = heap + (13 * L + 1) := by omega
    have haddrw : ptr - 2 * L < 2 ^ w := by omega
    refine runs_seq_call_le hf (vs := [edge, ptr - 2 * L, L, ptr]) (by eval_expr)
      (by wram_words) ?_ ?_
    · exact ⟨edge, ptr - 2 * L, L, ptr, rfl, hw, by omega, by omega, hv₁, haddr.symm ▸ htag,
        hflow, hdet, hz₁, by omega⟩
    · intro ret mem₂ pos₂ hpost
      obtain ⟨edge', tag', L', ptr', heq, hret, hv₂, hframe₂, hz₂⟩ := hpost
      obtain ⟨rfl, rfl, rfl, rfl⟩ : edge = edge' ∧ ptr - 2 * L = tag' ∧ L = L' ∧ ptr = ptr' := by
        simpa only [List.cons.injEq, and_true] using heq
      have hretw : ret < 2 ^ w := by omega
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change ret = heap + (17 * L + 1) ∧
          PathEdgeAt mem₂ edge h L (some (value.shift (PathTag.ofFlow (num * count)))) ∧
          (∀ x < heap, x < edge + 2 + 2 * L ∨ edge + 2 + 4 * L ≤ x → mem₂ x = mem x) ∧
          ZeroFrom mem₂ ret
        exact ⟨by omega, hv₂,
          fun x hx hout => (hframe₂ x (by omega) hout).trans (hframe x hx), hz₂⟩
      · simp only [offTreeCountUpdateContract, offTreeTagContract, offTreeFlowContract, encodeSignedPair,
          List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil]
        omega

/-- The two tag blocks decode to the scaled signed count and its
absolute value, in the original fixed-point precision. -/
theorem offTreeTag_fixVal {h L P a b : ℕ} {mem mem' : ℕ → ℕ} {num count : ℤ}
    (hn : PathIntAt mem a h L num)
    (ht : PathTagAt mem' b h L (PathTag.ofFlow (num * count))) :
    Num.fixVal mem' b h L P = Num.fixVal mem a h L P * (count : ℝ) ∧
    Num.fixVal mem' (b + L) h L P = |Num.fixVal mem a h L P * (count : ℝ)| := by
  have hp : PathIntAt mem' b h L (num * count) := ht.1
  have hd : PathIntAt mem' (b + L) h L |num * count| := ht.2
  have hs := offTreeScale_fixVal (P := P) hn hp
  refine ⟨hs, ?_⟩
  rw [← hs, Num.fixVal, Num.fixVal, hp.2, hd.2, Int.cast_abs, abs_div,
    abs_of_nonneg (pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) P)]

end MinCostFlow.MinRatio
