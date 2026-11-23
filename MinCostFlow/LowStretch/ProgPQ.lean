module

public import MinCostFlow.LowStretch.PQRep

/-!
# Pushing to and popping from the class queues

`pqPush [D, c, key, node]` appends an entry to list `c` (`pqPush_spec`), and `pqPop [D, R]`
removes a least entry and writes it at `R` and `R + 1` (`pqPop_spec`). Both cost `O(log J)`. The
memory facts behind them are `PQRep.push` and `PQRep.pop`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem slot_inj {A c c' i i' : ℕ} (hi : i < A) (hi' : i' < A) (h : c * A + i = c' * A + i') :
    c = c' ∧ i = i' := by
  have h1 := pack_div (k := c) hi
  have h2 := pack_div (k := c') hi'
  have h3 := pack_mod (k := c) hi
  have h4 := pack_mod (k := c') hi'
  rw [h] at h1 h3
  exact ⟨h1.symm.trans h2, h3.symm.trans h4⟩

theorem TTOk.congr {mem mem' : ℕ → ℕ} {T S : ℕ} (h : TTOk mem T S)
    (he : ∀ a, T + 1 ≤ a → a < T + 2 * S → mem' a = mem a) : TTOk mem' T S := by
  intro i hi1 hiS
  rw [he _ (by omega) (by omega), he _ (by omega) (by omega), he _ (by omega) (by omega)]
  exact h i hi1 hiS

theorem pqList_congr {mem mem' : ℕ → ℕ} {D J A c : ℕ}
    (hh : mem' (pqH D J c) = mem (pqH D J c)) (ht : mem' (pqT D J c) = mem (pqT D J c))
    (he : ∀ i, mem (pqH D J c) ≤ i → i < mem (pqT D J c) →
      mem' (pqE D J A c i) = mem (pqE D J A c i) ∧
        mem' (pqE D J A c i + 1) = mem (pqE D J A c i + 1)) :
    pqList mem' D J A c = pqList mem D J A c := by
  unfold pqList
  rw [hh, ht]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have := he (mem (pqH D J c) + i) (by omega) (by omega)
  rw [this.1, this.2]

/-- The memory after the three stores of a push. -/
def pushMem (mem : ℕ → ℕ) (D J A c key node : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update mem (pqE D J A c (mem (pqT D J c))) key)
    (pqE D J A c (mem (pqT D J c)) + 1) node) (pqT D J c) (mem (pqT D J c) + 1)

/-- **Push** in memory: after the three stores and the repair of the tree, the memory holds the
lists with the new entry at the end of list `c`. -/
theorem PQRep.push {mem : ℕ → ℕ} {D J A INF : ℕ} {qs : ℕ → List (ℕ × ℕ)}
    (h : PQRep mem D J A INF qs) {c key node : ℕ} (hc : c < J) (hA : mem (pqT D J c) < A)
    (hk : key < INF) (hmono : ∀ e ∈ qs c, e.1 ≤ key) {M : ℕ → ℕ}
    (hM : ∀ a, (a < D + 4 ∨ D + 3 + 2 * J ≤ a) → M a = pushMem mem D J A c key node a)
    (htt : TTOk M (D + 3) J)
    (hleaf : ∀ c' < J, M (D + 3 + J + c') =
      if c' = c ∧ mem (pqH D J c) = mem (pqT D J c) then key * J + c else mem (D + 3 + J + c')) :
    PQRep M D J A INF (Function.update qs c (qs c ++ [(key, node)])) := by
  set i := mem (pqT D J c) with hi
  -- the cells of the layout that the stores leave alone
  have hE : ∀ c' i', c' < J → i' < A → (c', i') ≠ (c, i) →
      M (pqE D J A c' i') = mem (pqE D J A c' i') ∧
        M (pqE D J A c' i' + 1) = mem (pqE D J A c' i' + 1) := by
    intro c' i' hc' hi' hne
    have hne1 : pqE D J A c' i' ≠ pqE D J A c i := by
      unfold pqE; intro he
      exact hne (by
        obtain ⟨h1, h2⟩ := slot_inj hi' hA (show c' * A + i' = c * A + i by omega)
        rw [h1, h2])
    have hne2 : pqE D J A c' i' ≠ pqE D J A c i + 1 := by unfold pqE; omega
    have hne3 : pqE D J A c' i' + 1 ≠ pqE D J A c i := by unfold pqE; omega
    have hne4 : pqE D J A c' i' + 1 ≠ pqE D J A c i + 1 := by
      intro he; exact hne1 (by omega)
    constructor
    · rw [hM _ (Or.inr (by unfold pqE; omega))]
      unfold pushMem
      rw [Function.update_of_ne (by unfold pqE pqT; omega), Function.update_of_ne hne2,
        Function.update_of_ne hne1]
    · rw [hM _ (Or.inr (by unfold pqE; omega))]
      unfold pushMem
      rw [Function.update_of_ne (by unfold pqE pqT; omega), Function.update_of_ne hne4,
        Function.update_of_ne hne3]
  have hHc : ∀ c' < J, M (pqH D J c') = mem (pqH D J c') := by
    intro c' hc'
    rw [hM _ (Or.inr (by unfold pqH; omega))]
    unfold pushMem
    rw [Function.update_of_ne (by unfold pqH pqT; omega), Function.update_of_ne
      (by unfold pqH pqE; omega), Function.update_of_ne (by unfold pqH pqE; omega)]
  have hTc : ∀ c' < J, c' ≠ c → M (pqT D J c') = mem (pqT D J c') := by
    intro c' hc' hne
    rw [hM _ (Or.inr (by unfold pqT; omega))]
    unfold pushMem
    rw [Function.update_of_ne (by unfold pqT; omega), Function.update_of_ne
      (by unfold pqT pqE; omega), Function.update_of_ne (by unfold pqT pqE; omega)]
  have hTcc : M (pqT D J c) = i + 1 := by
    rw [hM _ (Or.inr (by unfold pqT; omega))]
    unfold pushMem
    rw [Function.update_self]
  have hlow : ∀ a, a < D + 3 → M a = mem a := by
    intro a ha
    rw [hM _ (Or.inl (by omega))]
    unfold pushMem
    rw [Function.update_of_ne (by unfold pqT; omega), Function.update_of_ne
      (by unfold pqE; omega), Function.update_of_ne (by unfold pqE; omega)]
  have hbc := h.bounds c hc
  -- the new list `c`
  have hlc : pqList M D J A c = qs c ++ [(key, node)] := by
    rw [h.list c hc]
    unfold pqList
    rw [hHc c hc, hTcc, show i + 1 - mem (pqH D J c) = (i - mem (pqH D J c)) + 1 by omega,
      List.range_succ, List.map_append]
    congr 1
    · refine List.map_congr_left fun i' hi' => ?_
      have hi'' := List.mem_range.mp hi'
      have := hE c (mem (pqH D J c) + i') hc (by omega) (by
        intro he; simp only [Prod.mk.injEq] at he; omega)
      rw [this.1, this.2]
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      have e : mem (pqH D J c) + (i - mem (pqH D J c)) = i := by omega
      rw [e]
      refine Prod.ext ?_ ?_ <;> dsimp only
      · rw [hM _ (Or.inr (by unfold pqE; omega))]
        unfold pushMem
        rw [Function.update_of_ne (by unfold pqE pqT; omega), Function.update_of_ne
          (by unfold pqE; omega), Function.update_self]
      · rw [hM _ (Or.inr (by unfold pqE; omega))]
        unfold pushMem
        rw [Function.update_of_ne (by unfold pqE pqT; omega), Function.update_self]
  refine ⟨by rw [hlow D (by omega)]; exact h.hJ, by rw [hlow _ (by omega)]; exact h.hA,
    by rw [hlow _ (by omega)]; exact h.hINF, h.J_pos, fun c' hc' => ?_, fun c' hc' => ?_,
    fun c' hc' => ?_, fun c' => ?_, fun c' e he => ?_, htt, fun c' hc' => ?_⟩
  · by_cases hcc : c' = c
    · subst hcc; rw [hHc c' hc', hTcc]; omega
    · rw [hHc c' hc', hTc c' hc' hcc]; exact h.bounds c' hc'
  · by_cases hcc : c' = c
    · subst hcc; rw [Function.update_self, hlc]
    · rw [Function.update_of_ne hcc, h.list c' hc']
      refine (pqList_congr (hHc c' hc') (hTc c' hc' hcc) fun i' h1 h2 => ?_).symm
      have := (h.bounds c' hc').2
      exact hE c' i' hc' (by omega) (by intro he; simp only [Prod.mk.injEq] at he; omega)
  · rw [Function.update_of_ne (by omega)]; exact h.none c' hc'
  · by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self, List.pairwise_append]
      exact ⟨h.sorted c', List.pairwise_singleton _ _, fun a ha b hb => by
        simp only [List.mem_singleton] at hb; subst hb; exact hmono a ha⟩
    · rw [Function.update_of_ne hcc]; exact h.sorted c'
  · by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self] at he
      rcases List.mem_append.mp he with he | he
      · exact h.lt c' e he
      · simp only [List.mem_singleton] at he; subst he; exact hk
    · rw [Function.update_of_ne hcc] at he; exact h.lt c' e he
  · rw [hleaf c' hc']
    by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self]
      have hlen : (qs c').length = i - mem (pqH D J c') := by
        rw [h.list c' hc']; unfold pqList; simp [hi]
      by_cases hemp : mem (pqH D J c') = i
      · rw [if_pos ⟨rfl, hemp⟩]
        have : qs c' = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this]; rfl
      · rw [if_neg (by rintro ⟨-, h'⟩; exact hemp h')]
        rw [h.leaf c' hc']
        cases hq : qs c' with
        | nil => rw [hq] at hlen; simp at hlen; omega
        | cons e rest => rfl
    · rw [if_neg (by rintro ⟨h', -⟩; exact hcc h'), Function.update_of_ne hcc]
      exact h.leaf c' hc'

/-- The first entry of a list, and what follows it, as they sit in memory. -/
theorem PQRep.head_eq {mem : ℕ → ℕ} {D J A INF : ℕ} {qs : ℕ → List (ℕ × ℕ)}
    (h : PQRep mem D J A INF qs) {c : ℕ} (hc : c < J) {e : ℕ × ℕ} {rest : List (ℕ × ℕ)}
    (hq : qs c = e :: rest) :
    mem (pqH D J c) < mem (pqT D J c) ∧
    e = (mem (pqE D J A c (mem (pqH D J c))), mem (pqE D J A c (mem (pqH D J c)) + 1)) ∧
    (rest = [] ↔ mem (pqH D J c) + 1 = mem (pqT D J c)) ∧
    (∀ f rest', rest = f :: rest' →
      f.1 = mem (pqE D J A c (mem (pqH D J c) + 1))) := by
  have hl := h.list c hc
  rw [hq] at hl
  unfold pqList at hl
  have hlen := congrArg List.length hl
  simp only [List.length_cons, List.length_map, List.length_range] at hlen
  refine ⟨by omega, ?_, ?_, ?_⟩
  · have := congrArg List.head? hl
    rw [show mem (pqT D J c) - mem (pqH D J c) = (mem (pqT D J c) - mem (pqH D J c) - 1) + 1 by
      omega, List.range_succ_eq_map] at this
    simpa using this
  · constructor
    · rintro rfl; simp at hlen; omega
    · intro he
      cases rest with
      | nil => rfl
      | cons f r => simp at hlen; omega
  · intro f rest' hr
    subst hr
    have := congrArg (fun l => l[1]?) hl
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, List.getElem?_map,
      List.getElem?_range (show 1 < mem (pqT D J c) - mem (pqH D J c) by simp at hlen; omega),
      Option.map_some, Option.some.injEq] at this
    rw [this]

/-- **Pop** in memory: after the first position of list `c` moves by one and the tree is
repaired, the memory holds the lists without the first entry of list `c`. -/
theorem PQRep.pop {mem : ℕ → ℕ} {D J A INF : ℕ} {qs : ℕ → List (ℕ × ℕ)}
    (h : PQRep mem D J A INF qs) {c : ℕ} (hc : c < J) {e : ℕ × ℕ} {rest : List (ℕ × ℕ)}
    (hq : qs c = e :: rest) {M : ℕ → ℕ}
    (hM : ∀ a, D ≤ a → a < D + pqSize J A → (a < D + 4 ∨ D + 3 + 2 * J ≤ a) →
      M a = Function.update mem (pqH D J c) (mem (pqH D J c) + 1) a)
    (htt : TTOk M (D + 3) J)
    (hleaf : ∀ c' < J, M (D + 3 + J + c') =
      if c' = c then leafv INF J c rest else mem (D + 3 + J + c')) :
    PQRep M D J A INF (Function.update qs c rest) := by
  have hhd := h.head_eq hc hq
  have hJA : ∀ c' < J, c' * A + A ≤ J * A := fun c' hc' => by nlinarith
  have hsz : ∀ c' i, c' < J → i < A → pqE D J A c' i + 1 < D + pqSize J A := by
    intro c' i hc' hi
    have := hJA c' hc'
    have h2 : 2 * J * A = 2 * (J * A) := by ring
    unfold pqE pqSize; omega
  have hlow : ∀ a, D ≤ a → a < D + 3 → M a = mem a := by
    intro a ha0 ha
    rw [hM _ ha0 (by unfold pqSize; omega) (Or.inl (by omega)),
      Function.update_of_ne (by unfold pqH; omega)]
  have hHc : ∀ c' < J, c' ≠ c → M (pqH D J c') = mem (pqH D J c') := by
    intro c' hc' hne
    rw [hM _ (by unfold pqH; omega) (by unfold pqH pqSize; omega) (Or.inr (by unfold pqH; omega)),
      Function.update_of_ne (by unfold pqH; omega)]
  have hHcc : M (pqH D J c) = mem (pqH D J c) + 1 := by
    rw [hM _ (by unfold pqH; omega) (by unfold pqH pqSize; omega) (Or.inr (by unfold pqH; omega)),
      Function.update_self]
  have hTc : ∀ c' < J, M (pqT D J c') = mem (pqT D J c') := by
    intro c' hc'
    rw [hM _ (by unfold pqT; omega) (by unfold pqT pqSize; omega) (Or.inr (by unfold pqT; omega)),
      Function.update_of_ne (by unfold pqT pqH; omega)]
  have hEc : ∀ c' i, c' < J → i < A → M (pqE D J A c' i) = mem (pqE D J A c' i) ∧
      M (pqE D J A c' i + 1) = mem (pqE D J A c' i + 1) := by
    intro c' i hc' hi
    have := hsz c' i hc' hi
    constructor
    · rw [hM _ (by unfold pqE; omega) (by omega) (Or.inr (by unfold pqE; omega)),
        Function.update_of_ne (by unfold pqE pqH; omega)]
    · rw [hM _ (by unfold pqE; omega) (by omega) (Or.inr (by unfold pqE; omega)),
        Function.update_of_ne (by unfold pqE pqH; omega)]
  have hlc : pqList M D J A c = rest := by
    have hl := h.list c hc
    rw [hq] at hl
    unfold pqList at hl ⊢
    rw [hHcc, hTc c hc]
    rw [show mem (pqT D J c) - mem (pqH D J c) = (mem (pqT D J c) - (mem (pqH D J c) + 1)) + 1 by
      omega, List.range_succ_eq_map, List.map_cons, List.map_map] at hl
    have hl2 := (List.cons.inj hl).2
    rw [hl2]
    refine List.map_congr_left fun i hi => ?_
    simp only [Function.comp_apply]
    have hi' := List.mem_range.mp hi
    have hbc := h.bounds c hc
    rw [(hEc c _ hc (by omega)).1, (hEc c _ hc (by omega)).2, show mem (pqH D J c) + 1 + i = mem (pqH D J c) + (i + 1) by
      ring]
  refine ⟨by rw [hlow D le_rfl (by omega)]; exact h.hJ,
    by rw [hlow _ (by omega) (by omega)]; exact h.hA,
    by rw [hlow _ (by omega) (by omega)]; exact h.hINF, h.J_pos, fun c' hc' => ?_, fun c' hc' => ?_,
    fun c' hc' => ?_, fun c' => ?_, fun c' e' he' => ?_, htt, fun c' hc' => ?_⟩
  · by_cases hcc : c' = c
    · subst hcc; rw [hHcc, hTc c' hc']; have := h.bounds c' hc'; omega
    · rw [hHc c' hc' hcc, hTc c' hc']; exact h.bounds c' hc'
  · by_cases hcc : c' = c
    · subst hcc; rw [Function.update_self, hlc]
    · rw [Function.update_of_ne hcc, h.list c' hc']
      exact (pqList_congr (hHc c' hc' hcc) (hTc c' hc') fun i _ h2 =>
        hEc c' i hc' (by have := h.bounds c' hc'; omega)).symm
  · rw [Function.update_of_ne (by omega)]; exact h.none c' hc'
  · by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self]
      have := h.sorted c'
      rw [hq] at this
      exact this.of_cons
    · rw [Function.update_of_ne hcc]; exact h.sorted c'
  · by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self] at he'
      exact h.lt c' e' (by rw [hq]; exact List.mem_cons_of_mem _ he')
    · rw [Function.update_of_ne hcc] at he'; exact h.lt c' e' he'
  · rw [hleaf c' hc']
    by_cases hcc : c' = c
    · subst hcc; rw [if_pos rfl, Function.update_self]
    · rw [if_neg hcc, Function.update_of_ne hcc]; exact h.leaf c' hc'

/-- **Pop of the last entry** of list `c`: the first and last-plus-one positions of the list go
back to `0`, so the space of the list is used again. -/
theorem PQRep.popLast {mem : ℕ → ℕ} {D J A INF : ℕ} {qs : ℕ → List (ℕ × ℕ)}
    (h : PQRep mem D J A INF qs) {c : ℕ} (hc : c < J) {e : ℕ × ℕ}
    (hq : qs c = [e]) {M : ℕ → ℕ}
    (hM : ∀ a, D ≤ a → a < D + pqSize J A → (a < D + 4 ∨ D + 3 + 2 * J ≤ a) →
      M a = Function.update (Function.update mem (pqH D J c) 0) (pqT D J c) 0 a)
    (htt : TTOk M (D + 3) J)
    (hleaf : ∀ c' < J, M (D + 3 + J + c') =
      if c' = c then leafv INF J c [] else mem (D + 3 + J + c')) :
    PQRep M D J A INF (Function.update qs c []) := by
  have hJA : ∀ c' < J, c' * A + A ≤ J * A := fun c' hc' => by nlinarith
  have hsz : ∀ c' i, c' < J → i < A → pqE D J A c' i + 1 < D + pqSize J A := by
    intro c' i hc' hi
    have := hJA c' hc'
    have h2 : 2 * J * A = 2 * (J * A) := by ring
    unfold pqE pqSize; omega
  have hlow : ∀ a, D ≤ a → a < D + 3 → M a = mem a := by
    intro a ha0 ha
    rw [hM _ ha0 (by unfold pqSize; omega) (Or.inl (by omega)),
      Function.update_of_ne (by unfold pqT; omega), Function.update_of_ne (by unfold pqH; omega)]
  have hHc : ∀ c' < J, c' ≠ c → M (pqH D J c') = mem (pqH D J c') := by
    intro c' hc' hne
    rw [hM _ (by unfold pqH; omega) (by unfold pqH pqSize; omega) (Or.inr (by unfold pqH; omega)),
      Function.update_of_ne (by unfold pqH pqT; omega), Function.update_of_ne (by unfold pqH; omega)]
  have hHcc : M (pqH D J c) = 0 := by
    rw [hM _ (by unfold pqH; omega) (by unfold pqH pqSize; omega) (Or.inr (by unfold pqH; omega)),
      Function.update_of_ne (by unfold pqH pqT; omega), Function.update_self]
  have hTc : ∀ c' < J, c' ≠ c → M (pqT D J c') = mem (pqT D J c') := by
    intro c' hc' hne
    rw [hM _ (by unfold pqT; omega) (by unfold pqT pqSize; omega) (Or.inr (by unfold pqT; omega)),
      Function.update_of_ne (by unfold pqT; omega), Function.update_of_ne (by unfold pqT pqH; omega)]
  have hTcc : M (pqT D J c) = 0 := by
    rw [hM _ (by unfold pqT; omega) (by unfold pqT pqSize; omega) (Or.inr (by unfold pqT; omega)),
      Function.update_self]
  have hEc : ∀ c' i, c' < J → i < A → M (pqE D J A c' i) = mem (pqE D J A c' i) ∧
      M (pqE D J A c' i + 1) = mem (pqE D J A c' i + 1) := by
    intro c' i hc' hi
    have := hsz c' i hc' hi
    constructor
    · rw [hM _ (by unfold pqE; omega) (by omega) (Or.inr (by unfold pqE; omega)),
        Function.update_of_ne (by unfold pqE pqT; omega), Function.update_of_ne (by unfold pqE pqH; omega)]
    · rw [hM _ (by unfold pqE; omega) (by omega) (Or.inr (by unfold pqE; omega)),
        Function.update_of_ne (by unfold pqE pqT; omega), Function.update_of_ne (by unfold pqE pqH; omega)]
  refine ⟨by rw [hlow D le_rfl (by omega)]; exact h.hJ,
    by rw [hlow _ (by omega) (by omega)]; exact h.hA,
    by rw [hlow _ (by omega) (by omega)]; exact h.hINF, h.J_pos, fun c' hc' => ?_, fun c' hc' => ?_,
    fun c' hc' => ?_, fun c' => ?_, fun c' e' he' => ?_, htt, fun c' hc' => ?_⟩
  · by_cases hcc : c' = c
    · subst hcc; rw [hHcc, hTcc]; omega
    · rw [hHc c' hc' hcc, hTc c' hc' hcc]; exact h.bounds c' hc'
  · by_cases hcc : c' = c
    · subst hcc; rw [Function.update_self]; unfold pqList; rw [hHcc, hTcc]; rfl
    · rw [Function.update_of_ne hcc, h.list c' hc']
      exact (pqList_congr (hHc c' hc' hcc) (hTc c' hc' hcc) fun i _ h2 =>
        hEc c' i hc' (by have := h.bounds c' hc'; omega)).symm
  · rw [Function.update_of_ne (by omega)]; exact h.none c' hc'
  · by_cases hcc : c' = c
    · subst hcc; rw [Function.update_self]; exact List.Pairwise.nil
    · rw [Function.update_of_ne hcc]; exact h.sorted c'
  · by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self] at he'
      simp at he'
    · rw [Function.update_of_ne hcc] at he'; exact h.lt c' e' he'
  · rw [hleaf c' hc']
    by_cases hcc : c' = c
    · subst hcc; rw [if_pos rfl, Function.update_self]
    · rw [if_neg hcc, Function.update_of_ne hcc]; exact h.leaf c' hc'

end MinCostFlow.LowStretch

/-! ### The push procedure -/

namespace MinCostFlow.LowStretch

open WordRAM

/-- The layout at `D` determines its constants and its lists. -/
theorem PQRep.uniq {mem : ℕ → ℕ} {D J A INF J' A' INF' : ℕ} {qs qs' : ℕ → List (ℕ × ℕ)}
    (h : PQRep mem D J A INF qs) (h' : PQRep mem D J' A' INF' qs') :
    J' = J ∧ A' = A ∧ INF' = INF ∧ qs' = qs := by
  have e1 : J' = J := h'.hJ.symm.trans h.hJ
  have e2 : A' = A := h'.hA.symm.trans h.hA
  have e3 : INF' = INF := h'.hINF.symm.trans h.hINF
  subst e1 e2 e3
  refine ⟨rfl, rfl, rfl, funext fun c => ?_⟩
  by_cases hc : c < J'
  · rw [h.list c hc, h'.list c hc]
  · rw [h.none c (by omega), h'.none c (by omega)]

/-- `pqPush [D, J, A, c, key, node]`: append `(key, node)` to list `c`. Procedure `bTT` is
`ttUpdate`. -/
def pqPush (bTT : ℕ) : Stmt :=
  .seq (.assign 6 (.bin .add (.reg 0) (.const 3)))
  (.seq (.assign 7 (.bin .add (.reg 6) (.bin .add (.reg 1) (.reg 1))))
  (.seq (.assign 8 (.bin .add (.reg 7) (.bin .add (.reg 1) (.reg 1))))
  (.seq (.assign 9 (.load (.bin .add (.bin .add (.reg 7) (.reg 1)) (.reg 3))))
  (.seq (.assign 10 (.bin .add (.reg 8) (.bin .mul (.const 2)
      (.bin .add (.bin .mul (.reg 3) (.reg 2)) (.reg 9)))))
  (.seq (.store (.reg 10) (.reg 4))
  (.seq (.store (.bin .add (.reg 10) (.const 1)) (.reg 5))
  (.seq (.store (.bin .add (.bin .add (.reg 7) (.reg 1)) (.reg 3)) (.bin .add (.reg 9) (.const 1)))
  (.seq (.cond (.bin .eq (.load (.bin .add (.reg 7) (.reg 3))) (.reg 9))
      (.call 11 bTT [.reg 6, .reg 1, .reg 3, .bin .add (.bin .mul (.reg 4) (.reg 1)) (.reg 3)])
      .nop)
  (.ret (.const 0))))))))))

theorem pqPush_noRand (bTT : ℕ) : (pqPush bTT).NoRand := by simp [pqPush, Stmt.NoRand]

/-- The word bounds of a layout. -/
def PQFits (w D J A INF : ℕ) : Prop := D + pqSize J A < 2 ^ w ∧ INF * J + J < 2 ^ w ∧ 2 < 2 ^ w

/-- The contract of `pqPush`. -/
def pqPushC (w : ℕ) : Contract where
  pre args mem := ∃ D J A INF qs c key node, args = [D, J, A, c, key, node] ∧
    PQRep mem D J A INF qs ∧ PQFits w D J A INF ∧ c < J ∧ mem (pqT D J c) < A ∧ key < INF ∧
    ∀ e ∈ qs c, e.1 ≤ key
  post args mem _ mem' := ∀ D J A INF qs c key node, args = [D, J, A, c, key, node] →
    PQRep mem D J A INF qs →
    PQRep mem' D J A INF (Function.update qs c (qs c ++ [(key, node)])) ∧
      (∀ c' < J, mem' (pqT D J c') = if c' = c then mem (pqT D J c) + 1 else mem (pqT D J c')) ∧
      ∀ a, (a < D + 3 ∨ D + pqSize J A ≤ a) → mem' a = mem a
  cost args _ := 50 * (Nat.log 2 (args.getD 1 0) + 2) + 150

theorem pushMem_T {mem : ℕ → ℕ} {D J A c key node c' : ℕ} (hc' : c' < J) :
    pushMem mem D J A c key node (pqT D J c') =
      if c' = c then mem (pqT D J c) + 1 else mem (pqT D J c') := by
  unfold pushMem
  by_cases h : c' = c
  · subst h; simp
  · rw [if_neg h, Function.update_of_ne (by unfold pqT; omega),
      Function.update_of_ne (by unfold pqE pqT; omega), Function.update_of_ne (by unfold pqE pqT; omega)]

theorem pqPush_spec {w : ℕ} {p : Program} {b bTT : ℕ} (hp : p.HasAt b [pqPush bTT])
    (hTT : MeetsContract w p bTT (ttUpdateC w)) : MeetsContract w p b (pqPushC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨D, J, A, INF, qs, c, key, node, rfl, hrep, ⟨hfit1, hfit2, hw2⟩, hc, hA, hk, hmono⟩ :=
    hpre
  have hproc : p.procs[b]? = some (pqPush bTT) := hp 0 (by simp)
  have hJ1 := hrep.J_pos
  have hbc := hrep.bounds c hc
  have hcA : c * A + A ≤ J * A := by nlinarith
  have hkJ : key * J ≤ INF * J := Nat.mul_le_mul_right _ hk.le
  unfold pqSize at hfit1
  have hfit1' : D + 3 + 4 * J + 2 * (J * A) < 2 ^ w := by
    have : 2 * J * A = 2 * (J * A) := by ring
    omega
  have hD : D < 2 ^ w := by omega
  have ht : mem (D + 3 + (J + J) + J + c) = mem (pqT D J c) := by congr 1; unfold pqT; omega
  have hh : mem (D + 3 + (J + J) + c) = mem (pqH D J c) := by congr 1; unfold pqH; omega
  have htrip : Triple w p (fun st => st = startState [D, J, A, c, key, node] mem pos) (pqPush bTT)
      (fun _ st' => PQRep st'.mem D J A INF (Function.update qs c (qs c ++ [(key, node)])) ∧
        (∀ c' < J, st'.mem (pqT D J c') = if c' = c then mem (pqT D J c) + 1 else mem (pqT D J c')) ∧
        ∀ a, (a < D + 3 ∨ D + pqSize J A ≤ a) → st'.mem a = mem a)
      (fun _ => 50 * (Nat.log 2 J + 2) + 150) := by
    wram_enter
    · subst hpre
      dsimp only [pqPush]
      -- the memory after the three stores
      have he1 : D + 3 + (J + J) + (J + J) + 2 * (c * A + mem (pqT D J c)) =
          pqE D J A c (mem (pqT D J c)) := by unfold pqE; ring
      have he3 : D + 3 + (J + J) + J + c = pqT D J c := by unfold pqT; ring
      have hTTc : ∀ a, D + 3 + 1 ≤ a → a < D + 3 + 2 * J →
          pushMem mem D J A c key node a = mem a := by
        intro a h1 h2
        unfold pushMem
        rw [Function.update_of_ne (by unfold pqT; omega), Function.update_of_ne
          (by unfold pqE; omega), Function.update_of_ne (by unfold pqE; omega)]
      have hHm : pushMem mem D J A c key node (pqH D J c) = mem (pqH D J c) := by
        unfold pushMem
        rw [Function.update_of_ne (by unfold pqT pqH; omega), Function.update_of_ne
          (by unfold pqE pqH; omega), Function.update_of_ne (by unfold pqE pqH; omega)]
      have hframe : ∀ a, (a < D + 3 ∨ D + pqSize J A ≤ a) →
          pushMem mem D J A c key node a = mem a := by
        intro a ha
        have : c * A + mem (pqT D J c) < J * A := by omega
        have h2 : 2 * J * A = 2 * (J * A) := by ring
        unfold pqSize at ha
        unfold pushMem
        rw [Function.update_of_ne (by unfold pqT; omega), Function.update_of_ne
          (by unfold pqE; omega), Function.update_of_ne (by unfold pqE; omega)]
      wram_run
      · refine ⟨D + 3, J, c, key * J + c, rfl, hc, by omega, hw2, ?_⟩
        dsimp only
        rw [ht, he1, he3]
        exact hrep.tt.congr fun a h1 h2 => hTTc a (by omega) (by omega)
      · intro v mem' pos' hpost
        dsimp only [startState] at hpost hcond
        rw [ht, he1, he3] at hpost
        rw [ht, he1, he3] at hcond
        obtain ⟨htt', hleaf', hother', hfr'⟩ := hpost
        simp only [List.getD_cons_zero, List.getD_cons_succ] at htt' hleaf' hother' hfr'
        wram_run
        · dsimp only
          refine ⟨hrep.push hc hA hk hmono (fun a ha => hfr' a (by omega)) htt' fun c' hc' => ?_,
            fun c' hc' => ?_, fun a ha => ?_⟩
          · have hhd : mem (pqH D J c) = mem (pqT D J c) := by
              have : D + 3 + (J + J) + c = pqH D J c := by unfold pqH; ring
              rw [this] at hcond
              have hc2 : pushMem mem D J A c key node (pqH D J c) = mem (pqT D J c) := hcond
              rw [hHm] at hc2
              exact hc2
            by_cases hcc : c' = c
            · subst hcc; rw [if_pos ⟨rfl, hhd⟩, ← hleaf']
            · rw [if_neg (fun h => hcc h.1)]
              have := hother' c' hc' hcc
              rw [this]
              exact hTTc _ (by omega) (by omega)
          · rw [hfr' _ (by unfold pqT; omega)]; exact pushMem_T hc'
          · rw [hfr' a (by unfold pqSize at ha; omega)]
            exact hframe a ha
        · simp only [ttUpdateC, List.getD_cons_succ, List.getD_cons_zero] at *
          wram_cost
      · dsimp only [startState] at hcond ⊢
        rw [ht, he1, he3]
        rw [ht, he1, he3] at hcond
        refine ⟨hrep.push hc hA hk hmono (fun a _ => rfl)
          (hrep.tt.congr fun a h1 h2 => hTTc a (by omega) (by omega)) fun c' hc' => ?_,
          fun c' hc' => pushMem_T hc', hframe⟩
        have hhd : mem (pqH D J c) ≠ mem (pqT D J c) := by
          have : D + 3 + (J + J) + c = pqH D J c := by unfold pqH; ring
          rw [this] at hcond
          have hc2 : pushMem mem D J A c key node (pqH D J c) ≠ mem (pqT D J c) := hcond
          rw [hHm] at hc2
          exact hc2
        rw [if_neg (fun h => hhd h.2)]
        exact hTTc _ (by omega) (by omega)
      · wram_cost
  obtain ⟨o, st', c', hrun, hpost, hcost⟩ := htrip (startState [D, J, A, c, key, node] mem pos) ω rfl
  refine ⟨pqPush bTT, hproc, o, st', c', hrun, fun D' J' A' INF' qs' c'' key' node' he hrep' => ?_,
    by simpa [pqPushC] using hcost⟩
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := he
  obtain ⟨-, -, rfl, rfl⟩ := hrep.uniq hrep'
  exact hpost

end MinCostFlow.LowStretch
