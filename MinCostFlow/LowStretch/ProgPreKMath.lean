module

public import MinCostFlow.LowStretch.ProgCSR
public import MinCostFlow.LowStretch.KPure
public import WordRAM.Layout

/-!
# Facts for the merge tree part of the preprocessing

* The groups `offOf` and `grp` depend only on the keys of the items below `M` (`offOf_congr`,
  `grp_congr`).
* The sorted keys `e · m + q` give the pairs `q` sorted by weight (`sorted_keys`): `q` is the key
  modulo `m`, and the exponent `e` is the key divided by `m`.
* The kept pairs have different pairs of ends, so there are at most `n²` of them
  (`card_le_sq`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem offOf_congr {f g : ℕ → ℕ} {M : ℕ} (h : ∀ i < M, f i = g i) (u : ℕ) :
    offOf f M u = offOf g M u := by
  unfold offOf; congr 1
  exact List.filter_congr fun i hi => by rw [h i (List.mem_range.mp hi)]

theorem grp_congr {f g : ℕ → ℕ} {M : ℕ} (h : ∀ i < M, f i = g i) (u : ℕ) :
    grp f M u = grp g M u := by
  unfold grp
  exact List.filter_congr fun i hi => by rw [h i (List.mem_range.mp hi)]

theorem key_mod {e q m : ℕ} (hq : q < m) : (e * m + q) % m = q := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]

theorem key_div {e q m : ℕ} (hq : q < m) : (e * m + q) / m = e := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hq, Nat.zero_add]

/-- **Sorted keys give sorted pairs.** -/
theorem sorted_keys {G : PG} {m c : ℕ} {o ex : ℕ → ℕ} {S : List ℕ}
    (ho : ∀ j < c, o j < m) (hex : ∀ j < c, G.pω (o j) = 2 ^ ex (o j))
    (hperm : S.Perm (tab c fun j => ex (o j) * m + o j)) (hs : S.Pairwise (· ≤ ·)) :
    (∀ q ∈ S.map (· % m), ∃ j < c, q = o j) ∧
      (S.map (· % m)).Pairwise (G.pω · ≤ G.pω ·) ∧ ∀ j < c, o j ∈ S.map (· % m) := by
  have hmem : ∀ x ∈ S, ∃ j < c, x = ex (o j) * m + o j := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (hperm.subset hx)
    exact ⟨j, List.mem_range.mp hj, rfl⟩
  refine ⟨fun q hq => ?_, ?_, fun j hj => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    obtain ⟨j, hj, rfl⟩ := hmem x hx
    exact ⟨j, hj, key_mod (ho j hj)⟩
  · rw [List.pairwise_map]
    refine hs.imp_of_mem fun {x y} hx hy hxy => ?_
    obtain ⟨i, hi, rfl⟩ := hmem x hx
    obtain ⟨j, hj, rfl⟩ := hmem y hy
    rw [key_mod (ho i hi), key_mod (ho j hj), hex i hi, hex j hj]
    have := Nat.div_le_div_right (c := m) hxy
    rw [key_div (ho i hi), key_div (ho j hj)] at this
    exact Nat.pow_le_pow_right (by norm_num) this
  · refine List.mem_map.mpr ⟨ex (o j) * m + o j, hperm.symm.subset ?_, key_mod (ho j hj)⟩
    exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

/-- Items with different pairs of keys below `n`: at most `n²`. -/
theorem card_le_sq {c n : ℕ} {k o : ℕ → ℕ} (hk : ∀ j < c, k j < n ∧ o j < n)
    (hinj : ∀ j1 < c, ∀ j2 < c, k j1 = k j2 → o j1 = o j2 → j1 = j2) : c ≤ n * n := by
  have h := Finset.card_le_card_of_injOn (s := Finset.range c)
    (t := Finset.range n ×ˢ Finset.range n) (fun j => (k j, o j))
    (fun j hj => by
      have := hk j (Finset.mem_range.mp hj)
      simp [this.1, this.2])
    (fun j1 h1 j2 h2 he => by
      simp only [Prod.mk.injEq] at he
      exact hinj j1 (Finset.mem_range.mp h1) j2 (Finset.mem_range.mp h2) he.1 he.2)
  simpa using h

/-- Same smaller end and same larger end: the same ends. -/
theorem same_ends_of {a b c d : ℕ} (h1 : min a b = min c d) (h2 : a + b - min a b = c + d - min c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by omega

end MinCostFlow.LowStretch
