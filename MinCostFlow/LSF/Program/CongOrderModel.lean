module

public import MinCostFlow.LSF.Program.CongKeyMath
public import MinCostFlow.LSF.Program.BridgeLemmas
import Mathlib.Tactic.Linarith

/-!
# The written order is an approximate congestion order

`congOrderProc` leaves a list `S` of the non-root vertex indices, sorted by `congKey`, and
writes the rank `k` of `S[k]` into the cell of its parent edge `pe S[k]`. Here we show that any
edge order `π` with `π (fid i)` equal to the cell of edge `i` satisfies `IsApproxCongOrder` with
factor `5 / 4` (`congOrder_isApproxCongOrder`), as `ValidLSFParams.hπ` asks.

The steps: every tree edge is the parent edge `fid (pe x)` of exactly one non-root vertex `x`
(`parentEdge_bij_image`, `t0Rooted_spec`), so `π` of it is the position of `x` in `S`. Positions
in `S` are distinct, which makes `π` injective, and a smaller position has a smaller key. By
`congKey_eq_sum` the key of `x` is the floored congestion sum of its parent edge, which is what
`approxCongOrder_of_floor` needs.
-/

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

@[expose] public section

theorem congOrder_isApproxCongOrder {G₀ T₀ : MGraph} {vList eList : List ℕ} {tM r : ℕ}
    {fid tl hd par pe dep eu ev : ℕ → ℕ} {piv π : ℕ → ℕ} {S : List ℕ}
    {v ℓ₀ : ℕ → ℝ} {ℓ_int : ℕ → ℕ} {P_fp S_div : ℕ}
    (hv : ∀ e ∈ G₀.E, 0 < v e) (hℓ_pos : ∀ e ∈ G₀.E, 0 < ℓ_int e)
    (hℓ_lt : ∀ e ∈ G₀.E, 16 * ℓ_int e ≤ 2 ^ S_div)
    (hℓ_eq : ∀ e ∈ G₀.E, ℓ₀ e = (ℓ_int e : ℝ) / (2 : ℝ) ^ P_fp)
    (hT₀ : IsRootedTree T₀ (vList.getD r 0))
    (hA : T0IndexArrays T₀ vList tM fid tl hd) (hnd : vList.Nodup)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length)
    (hVT : ∀ i < vList.length, vList.getD i 0 ∈ T₀.V)
    (hTV : ∀ u ∈ T₀.V, ∃ i < vList.length, vList.getD i 0 = u)
    (hend : eList.Nodup) (hEl : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (heu : ∀ t < eList.length, eu t < vList.length ∧
      vList.getD (eu t) 0 = G₀.tail (eList.getD t 0))
    (hev : ∀ t < eList.length, ev t < vList.length ∧
      vList.getD (ev t) 0 = G₀.head (eList.getD t 0))
    (hSnd : S.Nodup) (hSmem : ∀ y, y ∈ S ↔ y < vList.length ∧ y ≠ r)
    (hSsort : S.Pairwise (fun a b =>
      congKey par dep eu ev (fun t => edgeMult G₀ v (eList.getD t 0) * 2 ^ S_div /
        ℓ_int (eList.getD t 0)) eList.length a ≤
      congKey par dep eu ev (fun t => edgeMult G₀ v (eList.getD t 0) * 2 ^ S_div /
        ℓ_int (eList.getD t 0)) eList.length b))
    (hrank : ∀ k (hk : k < S.length), piv (pe S[k]) = k)
    (hπ : ∀ i < tM, π (fid i) = piv i) :
    IsApproxCongOrder (open Classical in if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀) T₀
      (open Classical in if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1) (5 / 4) π := by
  classical
  set key := congKey par dep eu ev (fun t => edgeMult G₀ v (eList.getD t 0) * 2 ^ S_div /
    ℓ_int (eList.getD t 0)) eList.length with hkey
  -- every tree edge is the parent edge of a non-root index, at some position of `S`
  have hedge : ∀ f ∈ T₀.E, ∃ k, ∃ hk : k < S.length, f = fid (pe S[k]) ∧ π f = k := by
    intro f hf
    rw [← parentEdge_bij_image hT₀, Finset.mem_image] at hf
    obtain ⟨u, hu, rfl⟩ := hf
    rw [Finset.mem_erase] at hu
    obtain ⟨x, hx, rfl⟩ := hTV u hu.2
    have hxr : x ≠ r := fun h => hu.1 (by rw [h])
    have hpe := ((t0Rooted_spec hT₀.isForest hA hnd hR hr hx).2 hxr).2
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem ((hSmem x).mpr ⟨hx, hxr⟩)
    refine ⟨k, hk, by rw [hpe, hkx], ?_⟩
    rw [hpe, hπ _ (hR.step x hx hxr).1, ← hkx, hrank k hk]
  have hord : IsEdgeOrder T₀ π := by
    intro f hf g hg hfg
    obtain ⟨k, hk, rfl, hπk⟩ := hedge f hf
    obtain ⟨k', hk', rfl, hπk'⟩ := hedge g hg
    have : k = k' := by rw [← hπk, ← hπk', hfg]
    subst this; rfl
  by_cases hE : G₀.E.Nonempty
  swap
  · -- no edges: every congestion is zero
    rw [if_neg hE, if_neg hE]
    have h0 : G₀.E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    refine ⟨hord, by norm_num, fun f _ g _ _ => ?_⟩
    simp only [congestion, h0, Finset.sum_empty, mul_zero, le_refl]
  rw [if_pos hE, if_pos hE]
  refine approxCongOrder_of_floor hE hv hℓ_pos hℓ_lt hℓ_eq hord fun f hf g hg hle => ?_
  obtain ⟨k, hk, rfl, hπk⟩ := hedge f hf
  obtain ⟨k', hk', rfl, hπk'⟩ := hedge g hg
  have hmk := (hSmem _).mp (List.getElem_mem hk)
  have hmk' := (hSmem _).mp (List.getElem_mem hk')
  rw [← congKey_eq_sum (Q := fun e => edgeMult G₀ v e * 2 ^ S_div / ℓ_int e) hT₀ hA hnd hR hr
      hVT hend hEl heu hev hmk.1 hmk.2,
    ← congKey_eq_sum (Q := fun e => edgeMult G₀ v e * 2 ^ S_div / ℓ_int e) hT₀ hA hnd hR hr
      hVT hend hEl heu hev hmk'.1 hmk'.2]
  rcases Nat.lt_or_ge k k' with hlt | hge
  · exact List.pairwise_iff_getElem.mp hSsort k k' hk hk' hlt
  · have : k = k' := by omega
    subst this; exact le_rfl

end

end MinCostFlow.LSF.Program
