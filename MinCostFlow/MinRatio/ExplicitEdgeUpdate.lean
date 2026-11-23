module

public import MinCostFlow.MinRatio.ExplicitEdgeSignedCount
public import MinCostFlow.MinRatio.OffTreeTag
import WordRAM.Tactic

/-!
# Applying a selected explicit cycle edge

Algorithm 2 (page 29) applies the normalized circulation and tracks its
absolute value. Given an explicit edge's name and record address, count
its traversals in both directions, then apply its net change in place.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Arguments are route base, route length, edge name, edge record,
multiplier address, limb count, and heap. -/
@[expose] def explicitEdgeUpdateBody (count update : ℕ) : Stmt :=
  .call 7 count [.reg 0, .reg 1, .reg 2, .reg 6] ;;
  .call 8 update [.reg 3, .reg 4, .load (.reg 6),
    .load (.bin .add (.reg 6) (.const 1)), .reg 5, .reg 7] ;;
  .ret (.reg 8)

/-- Update the selected record using the signed count of its name in the route. -/
@[expose] def explicitEdgeUpdateContract (w h : ℕ) (edges : List (ℕ × Bool)) (e : ℕ)
    (value : PathEdgeValue) (num : ℤ) : Contract where
  pre args mem :=
    let net := (edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)
    ∃ base edge a L heap, args = [base, edges.length, e, edge, a, L, heap] ∧
      ExplicitEdgesAt mem base edges ∧ base + 2 * edges.length ≤ heap ∧
      (offTreeCountUpdateContract w h value num net).pre
        (edge :: a :: (encodeInt net ++ [L, heap])) mem ∧
      heap + (17 * L + 3) < 2 ^ w
  post args mem ret mem' :=
    let edge := args.getD 3 0
    let L := args.getD 5 0
    let heap := heapArg args
    let net := (edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)
    ret = heap + (17 * L + 3) ∧
      PathEdgeAt mem' edge h L (some (value.shift (PathTag.ofFlow (num * net)))) ∧
      (∀ x < heap, x < edge + 2 + 2 * L ∨ edge + 2 + 4 * L ≤ x → mem' x = mem x) ∧
      ZeroFrom mem' ret
  cost args _ := 68 * edges.length + 152 * (args.getD 5 0)^2 + 561 * args.getD 5 0 + 650

/-- The wrapper contains no random statements. -/
theorem explicitEdgeUpdateBody_noRand (count update : ℕ) :
    (explicitEdgeUpdateBody count update).NoRand := by
  simp [explicitEdgeUpdateBody, Stmt.NoRand]

/-- The machine applies the scaled net count to the selected edge,
preserving all earlier cells outside its two account blocks. -/
theorem explicitEdgeUpdate_meetsContract {w h entry count update : ℕ} {p : Program}
    (edges : List (ℕ × Bool)) (e : ℕ) (value : PathEdgeValue) (num : ℤ)
    (hp : p.HasAt entry [explicitEdgeUpdateBody count update])
    (hc : MeetsContract w p count (explicitEdgeSignedCountContract w edges e))
    (hu : MeetsContract w p update (offTreeCountUpdateContract w h value num
      ((edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)))) :
    MeetsContract w p entry (explicitEdgeUpdateContract w h edges e value num) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨base, edge, a, L, heap, rfl, hr, hb, hupdate, hroom⟩ := hpre
  let net := (edges.count (e, true) : ℤ) - (edges.count (e, false) : ℤ)
  change (offTreeCountUpdateContract w h value num net).pre
    (edge :: a :: (encodeInt net ++ [L, heap])) mem at hupdate
  obtain ⟨edge', a', L', heap', heq, hw, her, hv, ha, hn, hcfit, hprod, habs, hf, hd, hz, _⟩ := hupdate
  obtain ⟨rfl, rfl, rfl, rfl⟩ : edge = edge' ∧ a = a' ∧ L = L' ∧ heap = heap' := by
    simpa only [encodeInt, List.cons_append, List.nil_append, List.cons.injEq, true_and, and_true] using heq
  have hbase := hwords base (by simp)
  have hlen := hwords edges.length (by simp)
  have he := hwords e (by simp)
  have hew := hwords edge (by simp)
  have haw := hwords a (by simp)
  have hLw := hwords L (by simp)
  have hheap := hwords heap (by simp)
  have hone : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold explicitEdgeUpdateBody
  refine runs_seq_call_le hc (vs := [base, edges.length, e, heap]) (by eval_expr)
    (by wram_words) ?_ ?_
  · exact ⟨base, heap, rfl, hr, hb, by omega⟩
  · intro ptr mem₁ pos₁ hpost
    obtain ⟨hptr, henc, hframe⟩ := hpost
    change ptr = heap + 2 at hptr
    change ListAt mem₁ heap (encodeInt net) at henc
    change ∀ x, x < heap ∨ heap + 2 ≤ x → mem₁ x = mem x at hframe
    let sign : ℕ := if net < 0 then 1 else 0
    have hsign : mem₁ heap = sign := henc 0 (by simp [encodeInt])
    have hmag : mem₁ (heap + 1) = net.natAbs := henc 1 (by simp [encodeInt])
    have hsw : sign < 2 ^ w := by dsimp [sign]; split <;> omega
    have hmw : net.natAbs < 2 ^ w := by
      have hf' := List.count_le_length (l := edges) (a := (e, true))
      have hb' := List.count_le_length (l := edges) (a := (e, false))
      dsimp [net]
      omega
    have hhw₁ : heap + 1 < 2 ^ w := by omega
    have hpw : ptr < 2 ^ w := by omega
    have hv₁ := hv.congr (mem' := mem₁) (fun x _ hx => hframe x (Or.inl (by omega)))
    have hn₁ := hn.congr (mem' := mem₁) (fun i hi => hframe _ (Or.inl (by omega)))
    have hz₁ : ZeroFrom mem₁ ptr := fun x hx => (hframe x (Or.inr (by omega))).trans (hz x (by omega))
    refine runs_seq_call_le hu (vs := [edge, a, sign, net.natAbs, L, ptr])
      (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨edge, a, L, ptr, rfl, hw, by omega, hv₁, by omega, hn₁, hcfit, hprod, habs,
        hf, hd, hz₁, by omega⟩
    · intro ret mem₂ pos₂ hres
      have hret : ret = ptr + (17 * L + 1) := hres.1
      have hretw : ret < 2 ^ w := by omega
      have hv₂ : PathEdgeAt mem₂ edge h L (some (value.shift (PathTag.ofFlow (num * net)))) := hres.2.1
      have hframe₂ : ∀ x < ptr, x < edge + 2 + 2 * L ∨ edge + 2 + 4 * L ≤ x →
          mem₂ x = mem₁ x := hres.2.2.1
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · change ret = heap + (17 * L + 3) ∧
          PathEdgeAt mem₂ edge h L (some (value.shift (PathTag.ofFlow (num * net)))) ∧
          (∀ x < heap, x < edge + 2 + 2 * L ∨ edge + 2 + 4 * L ≤ x → mem₂ x = mem x) ∧
          ZeroFrom mem₂ ret
        exact ⟨by omega, hv₂, fun x hx hout =>
          (hframe₂ x (by omega) hout).trans (hframe x (Or.inl hx)), hres.2.2.2⟩
      · simp [explicitEdgeUpdateContract, explicitEdgeSignedCountContract, offTreeCountUpdateContract,
          Expr.size, argsSize]
        omega

/-- The selected update leaves every disjoint edge record available
for the subsequent iterations. -/
theorem explicitEdgeUpdate_frame_record {w h base e edge a L heap ret other : ℕ}
    {edges : List (ℕ × Bool)} {value old : PathEdgeValue} {num : ℤ} {mem mem' : ℕ → ℕ}
    (hp : (explicitEdgeUpdateContract w h edges e value num).post
      [base, edges.length, e, edge, a, L, heap] mem ret mem')
    (hold : PathEdgeAt mem other h L (some old))
    (hbelow : other + 2 + 4 * L ≤ heap)
    (hdisj : other + 2 + 4 * L ≤ edge ∨ edge + 2 + 4 * L ≤ other) :
    PathEdgeAt mem' other h L (some old) := by
  have hframe : ∀ x < heap, x < edge + 2 + 2 * L ∨ edge + 2 + 4 * L ≤ x →
      mem' x = mem x := hp.2.2.1
  apply hold.congr
  intro x hx₀ hx₁
  apply hframe x (lt_of_lt_of_le hx₁ hbelow)
  rcases hdisj with h | h
  · exact Or.inl (by omega)
  · exact Or.inr (h.trans hx₀)

end MinCostFlow.MinRatio
