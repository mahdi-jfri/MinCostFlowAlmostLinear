module

public import MinCostFlow.LowStretch.ProgRecSpec
public import MinCostFlow.LowStretch.ProgPreCost

/-!
# The cost of the body fits its share

The body of the cluster procedure makes many calls. Their costs are of two kinds.
* *Per unit*: a cost of order `log J + L` for each active pair, each stored pair, each
  super-vertex, each child, each split of a reset, and once. Here `J = rootJ n` is the number of
  classes of Dijkstra and `L = pL n` the number of buckets. We call `unitCost n` the cost of one
  unit (`10⁶ (log J + 2 + L)`).
* *Per child*: a cost of order `J` (emptying the class queues) and the logarithm of a word, at
  most `kidCost w n` for each child.

`body_fit` turns such a sum into the share `bodyShare + nch · kidCost` that `MeetsBody` allows,
with `A = bodyA = 2 · 10⁷`. Two facts make it work.
* `log J + 2 ≤ 6 L` (`logJ_le`): `J ≤ 17 pa + 4` while `2 pa + 2 < 2^L`, so `J < 2^(L + 4)`.
  So one unit costs at most `7 · 10⁶ L` (`unitCost_le`).
* There are at most `|S| + 1` super-vertices (the hypothesis `hs`), so the units are at most
  twice those that `bodyShare` counts.

`leaf_fit` is the same for a single vertex, and `childCost_fit` writes the cost `childCost` of the
child step in this form. `bodyA ≥ recK + 1`, as `recP_meets` asks (`recK = 200`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The constant `A` of the body. -/
def bodyA : ℕ := 20000000

/-- The cost of one unit of the body. -/
def unitCost (n : ℕ) : ℕ := 1000000 * (Nat.log 2 (rootJ n) + 2 + pL n)

/-- **The logarithm of `J` is of the order of `L`.** -/
theorem logJ_le (n : ℕ) : Nat.log 2 (rootJ n) + 2 ≤ 6 * pL n := by
  have h1 := pσ_le_pa n
  have h2 : 2 * pa n + 2 < 2 ^ pL n := Nat.lt_pow_succ_log_self (by norm_num) _
  have e : 2 ^ (pL n + 4) = 2 ^ pL n * 16 := by rw [pow_add]; norm_num
  have h3 : rootJ n < 2 ^ (pL n + 4) := by rw [e]; unfold rootJ; omega
  have h4 : Nat.log 2 (rootJ n) < pL n + 4 := Nat.log_lt_of_lt_pow (by unfold rootJ; omega) h3
  have := pL_pos n
  omega

theorem unitCost_le (n : ℕ) : unitCost n ≤ 7000000 * pL n := by
  unfold unitCost
  have := logJ_le n
  omega

/-- **The cost of the body fits its share.** The per-unit part counts the active pairs, the stored
pairs, the super-vertices, the children, the splits of the resets of the children and `1`; child
`k` costs `kc k ≤ kidCost` besides. -/
theorem body_fit {w : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {D : Cl.Dec}
    {cs : ℕ → Cl} {kc : ℕ → ℕ} {cost : ℕ} (hL : P.L = pL G.n)
    (hs : R.nodes.length ≤ R.S.length + 1) (hkc : ∀ k < D.nch, kc k ≤ kidCost w G.n)
    (hcost : cost ≤ unitCost G.n * ((c.act G P).card + R.S.length + R.nodes.length + D.nch + 1 +
        ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ) +
      ∑ k ∈ Finset.range D.nch, kc k) :
    cost ≤ bodyShare bodyA T G P c R D cs + D.nch * kidCost w G.n := by
  have h1 : ∑ k ∈ Finset.range D.nch, kc k ≤ D.nch * kidCost w G.n := by
    have := Finset.sum_le_sum (s := Finset.range D.nch) (g := fun _ => kidCost w G.n)
      (fun k hk => hkc k (Finset.mem_range.mp hk))
    simpa using this
  unfold bodyShare
  rw [hL]
  generalize ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ = V at hcost ⊢
  generalize ∑ k ∈ Finset.range D.nch, kc k = K at hcost h1
  generalize D.nch * kidCost w G.n = KK at h1 ⊢
  have hu := unitCost_le G.n
  generalize unitCost G.n = U at hcost hu
  generalize pL G.n = L at hu ⊢
  generalize hXd : (c.act G P).card + R.S.length + 1 + D.nch + V = X
  have hX : (c.act G P).card + R.S.length + R.nodes.length + D.nch + 1 + V ≤ 2 * X := by
    omega
  have h2 := Nat.mul_le_mul hu hX
  have e : 7000000 * L * (2 * X) = 14000000 * (L * X) := by ring
  have e2 : bodyA * L * X = 20000000 * (L * X) := by unfold bodyA; ring
  omega

/-- **The cost of a single vertex fits its share.** -/
theorem leaf_fit {P : Par} {R : Rec} {n cost : ℕ} (hL : P.L = pL n)
    (hs : R.nodes.length ≤ R.S.length + 1)
    (hcost : cost ≤ unitCost n * (R.S.length + R.nodes.length + 1)) :
    cost ≤ bodyA * P.L * (R.S.length + 1) := by
  rw [hL]
  have hu := unitCost_le n
  generalize unitCost n = U at hcost hu
  generalize pL n = L at hu ⊢
  have h2 := Nat.mul_le_mul hu (show R.S.length + R.nodes.length + 1 ≤ 2 * (R.S.length + 1) by
    omega)
  have e : 7000000 * L * (2 * (R.S.length + 1)) = 14000000 * (L * (R.S.length + 1)) := by ring
  have e2 : bodyA * L * (R.S.length + 1) = 20000000 * (L * (R.S.length + 1)) := by
    unfold bodyA; ring
  omega

/-- `log2P` on a word costs at most `kidCost`'s share for it. -/
theorem log2Cost_le_kid {w x : ℕ} (hx : x < 2 ^ w) : log2Cost x ≤ 500 * (Nat.log 2 w + 2) := by
  have := log2Cost_le_word hx
  omega

/-- **The child step in the form of `body_fit`**: `childCost` is at most `unitCost` for each
active pair, each super-vertex, each split and once, and, for each child, `10⁴ (J + 1)` and
`50 (log w + 2)`, when the reset numbers are words. -/
theorem childCost_fit {w : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {D : Cl.Dec}
    {cs : ℕ → Cl}
    (hw : ∀ k < D.nch, Cl.resetS T G P (c.raw G D k) / (4 * P.B * (c.raw G D k).X.card) < 2 ^ w) :
    childCost T G P c R D cs (rootJ G.n) ≤
      unitCost G.n * ((c.act G P).card + R.nodes.length + 1 +
        ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ) +
      D.nch * (10000 * (rootJ G.n + 1) + 50 * (Nat.log 2 w + 2)) := by
  have hconst : ∑ _k ∈ Finset.range D.nch, (10000 * (rootJ G.n + 1) + 50 * (Nat.log 2 w + 2)) =
      D.nch * (10000 * (rootJ G.n + 1) + 50 * (Nat.log 2 w + 2)) := by simp
  rw [← hconst]
  unfold childCost
  have hu : 100000 * (Nat.log 2 (rootJ G.n) + 2) ≤ unitCost G.n := by unfold unitCost; omega
  have hu2 : 10000 ≤ unitCost G.n := by unfold unitCost; omega
  have hsum : ∑ k ∈ Finset.range D.nch, (10000 * (rootJ G.n + 1) +
        log2Cost (Cl.resetS T G P (c.raw G D k) / (4 * P.B * (c.raw G D k).X.card)) +
        10000 * T.visW G (c.raw G D k) (cs k).θ) ≤
      ∑ k ∈ Finset.range D.nch, (10000 * (rootJ G.n + 1) + 50 * (Nat.log 2 w + 2)) +
        unitCost G.n * ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    have h1 := log2Cost_le_word (hw k (Finset.mem_range.mp hk))
    have h2 : 10000 * T.visW G (c.raw G D k) (cs k).θ ≤
        unitCost G.n * T.visW G (c.raw G D k) (cs k).θ := Nat.mul_le_mul_right _ hu2
    omega
  have h3 : 100000 * (Nat.log 2 (rootJ G.n) + 2) * ((c.act G P).card + R.nodes.length + 1) ≤
      unitCost G.n * ((c.act G P).card + R.nodes.length + 1) := Nat.mul_le_mul_right _ hu
  have e : unitCost G.n * ((c.act G P).card + R.nodes.length + 1 +
        ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ) =
      unitCost G.n * ((c.act G P).card + R.nodes.length + 1) +
        unitCost G.n * ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ := by ring
  rw [e]
  generalize ∑ k ∈ Finset.range D.nch, (10000 * (rootJ G.n + 1) +
        log2Cost (Cl.resetS T G P (c.raw G D k) / (4 * P.B * (c.raw G D k).X.card)) +
        10000 * T.visW G (c.raw G D k) (cs k).θ) = S1 at hsum ⊢
  generalize ∑ k ∈ Finset.range D.nch, (10000 * (rootJ G.n + 1) + 50 * (Nat.log 2 w + 2)) = S2
    at hsum ⊢
  generalize unitCost G.n * ∑ k ∈ Finset.range D.nch, T.visW G (c.raw G D k) (cs k).θ = S3
    at hsum ⊢
  generalize 100000 * (Nat.log 2 (rootJ G.n) + 2) * ((c.act G P).card + R.nodes.length + 1) = S4
    at h3 ⊢
  generalize unitCost G.n * ((c.act G P).card + R.nodes.length + 1) = S5 at h3 ⊢
  omega

theorem bodyA_ge : 201 ≤ bodyA := by unfold bodyA; omega

end MinCostFlow.LowStretch
