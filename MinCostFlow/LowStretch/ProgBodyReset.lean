module

public import MinCostFlow.LowStretch.ProgRecSpec
import MinCostFlow.LowStretch.ProgChildDelta

/-!
# The numbers of the reset rule are words

The cost of the child step has, per child, the cost `log2Cost` of the number
`resetS / (4 B |X|)` of the reset rule. `childCost_fit` bounds it when this number is a word.
`ClPre.reset_lt` proves that it is. The number is at most `resetS = max(Δ, μ, 4 B |X|)` of the
raw child, and each of the three terms is below the big term of the room in `ClPre`:
- the radius of a raw child is at most the radius of the parent (`Cl.raw_Δ`), which is at most
  `|X|` times the largest weight `Mw` (`Cl.Δ_le_card_mul`), so at most `n Mw`;
- the weight of a merge node is the weight of a pair, so at most `Mw`;
- `4 B |X| ≤ 4 B n ≤ 128 B n² < 2^J`, by `GlobL.Ok.hJ`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

theorem ClPre.reset_lt {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
    {mem : ℕ → ℕ} {D : Cl.Dec} (hpre : ClPre w A T G P c R GB RB h mem) (hD : c.DecOk G P D)
    {k : ℕ} (hk : k < D.nch) :
    Cl.resetS T G P (c.raw G D k) / (4 * P.B * (c.raw G D k).X.card) < 2 ^ w := by
  obtain ⟨Mw, hM, -, hroom⟩ := hpre.room_sq
  have hglob := hpre.glob
  have hT := hglob.tree
  set J := (GlobL.read mem GB).J
  set Z := 2 ^ (2 * J + 20) * (T.N + G.m + 2) ^ 2 * (Mw + 2) ^ 2 with hZ
  have hinv := hpre.ok.inv
  have hsub : (c.raw G D k).X ⊆ Finset.range G.n :=
    (Cl.raw_X_subset (G := G) (D := D) (c := c) k).trans hinv.sub
  have hcX : c.X.card ≤ G.n := by
    have := Finset.card_le_card hinv.sub; rwa [Finset.card_range] at this
  have hrX : (c.raw G D k).X.card ≤ G.n := by
    have := Finset.card_le_card hsub; rwa [Finset.card_range] at this
  have hnN := hT.n_lt
  -- a common bound: `(N + m + 2)² (Mw + 2)² ≤ Z`
  have hY : (T.N + G.m + 2) ^ 2 * (Mw + 2) ^ 2 ≤ Z := by
    rw [hZ, mul_assoc]
    exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have hNM : (T.N + 2) * (Mw + 2) ≤ (T.N + G.m + 2) ^ 2 * (Mw + 2) ^ 2 := by
    have h1 : T.N + 2 ≤ (T.N + G.m + 2) ^ 2 :=
      (by omega : T.N + 2 ≤ T.N + G.m + 2).trans (Nat.le_self_pow (by norm_num) _)
    have h2 : Mw + 2 ≤ (Mw + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    exact Nat.mul_le_mul h1 h2
  -- the radius
  have hΔ : (c.raw G D k).Δ G ≤ Z := by
    have h1 := Cl.raw_Δ hinv.good hD hpre.ok.hGo hk
    have h2 := Cl.Δ_le_card_mul hinv.good.conn hM
    have h3 : c.X.card * Mw ≤ (T.N + 2) * (Mw + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega
  -- the weights of the `θ`-nodes
  have hμ : ((c.raw G D k).X.sup fun a => T.mw (T.top (c.raw G D k).θ a)) ≤ Z := by
    refine Finset.sup_le fun a ha => ?_
    have haN : a < G.n := Finset.mem_range.mp (hsub ha)
    have hθ : 1 ≤ (c.raw G D k).θ := by rw [Cl.raw_θ]; exact hinv.one_le
    have htN := KT.top_lt_N hT haN hθ
    have hmw : T.mw (T.top (c.raw G D k).θ a) ≤ Mw := by
      by_cases hn : G.n ≤ T.top (c.raw G D k).θ a
      · obtain ⟨hm, he, -⟩ := hT.merge _ hn htN
        rw [← he]; exact hM _ hm
      · rw [hT.leaf_mw _ (by omega)]; exact Nat.zero_le _
    have h3 : Mw + 2 ≤ (T.N + 2) * (Mw + 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- `4 B |X|`
  have hB : 4 * P.B * (c.raw G D k).X.card ≤ Z := by
    have hJ : 128 * P.B * G.n ^ 2 < 2 ^ J := hglob.hJ
    have h1 : 4 * P.B * (c.raw G D k).X.card ≤ 128 * P.B * G.n ^ 2 := by
      have : (c.raw G D k).X.card ≤ G.n ^ 2 := hrX.trans (Nat.le_self_pow (by norm_num) _)
      have := Nat.mul_le_mul_left (4 * P.B) this
      nlinarith
    have h2 : 2 ^ J ≤ 2 ^ (2 * J + 20) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 1 ≤ (T.N + G.m + 2) ^ 2 * (Mw + 2) ^ 2 :=
      Nat.mul_pos (pow_pos (by omega) 2) (pow_pos (by omega) 2)
    have h4 : 2 ^ (2 * J + 20) ≤ Z := by
      rw [hZ, mul_assoc]; exact Nat.le_mul_of_pos_right _ h3
    omega
  have hS : Cl.resetS T G P (c.raw G D k) ≤ Z := by
    unfold Cl.resetS
    exact max_le (max_le hΔ hμ) hB
  have := Nat.div_le_self (Cl.resetS T G P (c.raw G D k)) (4 * P.B * (c.raw G D k).X.card)
  omega

end MinCostFlow.LowStretch
