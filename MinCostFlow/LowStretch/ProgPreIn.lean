module

public import MinCostFlow.LowStretch.ProgPreLay
public import MinCostFlow.LowStretch.ProgEntrySpec

/-!
# The input of the preprocessing

The preprocessing starts from a memory that holds the graph `G` as `G.encode` at address `0`
(`InG`). From the word bound `(H + maxω + 2)^16 < 2^w` of the precondition of the cluster
procedure, with `H = aH n m`, it gets every bound that the called procedures need
(`InG.lt_word` and the lemmas after it). The input memory of the machine meets `InG`
(`inG_init`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- The weight of edge `p` of `G`. -/
def wtOf (G : WGraph) (p : ℕ) : ℕ := (G.edges.getD p (0, 0, 0)).2.2

/-- The memory holds the graph `G` at address `0`, and the word is large enough. -/
structure InG (w : ℕ) (G : WGraph) (mem : ℕ → ℕ) : Prop where
  allowed : Allowed G
  two_le : 2 ≤ G.n
  n0 : mem 0 = G.n
  m1 : mem 1 = G.m
  ends : ∀ p < G.m, mem (2 + 3 * p) = (pgOf G).pu p ∧ mem (2 + 3 * p + 1) = (pgOf G).pv p
  wt : ∀ p < G.m, mem (2 + 3 * p + 2) = wtOf G p
  word : (aH G.n G.m + (pgOf G).maxω + 2) ^ 16 < 2 ^ w

variable {w : ℕ} {G : WGraph} {mem : ℕ → ℕ}

theorem wtOf_eq {p : ℕ} (hp : p < G.m) : wtOf G p = (G.edges[p]'hp).2.2 := by
  unfold wtOf; rw [List.getD_eq_getElem _ _ hp]

theorem wtOf_pos (h : Allowed G) {p : ℕ} (hp : p < G.m) : 1 ≤ wtOf G p := by
  rw [wtOf_eq hp]; exact h.weight _ (List.getElem_mem _)

theorem pω_wtOf {p : ℕ} (hp : p < G.m) :
    (pgOf G).pω p = 2 ^ (Nat.log 2 (wtOf G p) + pσ G.n) := by
  unfold pgOf; rw [toPG.pω_eq hp, wtOf_eq hp]

theorem foldr_max_le_aux {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem wtOf_le_maxWeight {p : ℕ} (hp : p < G.m) : wtOf G p ≤ G.maxWeight := by
  rw [wtOf_eq hp]
  exact foldr_max_le_aux (List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩)

theorem pgOf_m : (pgOf G).m = G.m := by simp [pgOf]

theorem pω_le_maxω {p : ℕ} (hp : p < G.m) : (pgOf G).pω p ≤ (pgOf G).maxω :=
  PG.le_maxω (by rw [pgOf_m]; exact hp)

/-- The weight times `2^σ` is less than twice the rounded weight. -/
theorem wtOf_mul_lt {p : ℕ} (hp : p < G.m) (h : Allowed G) :
    wtOf G p * 2 ^ pσ G.n < 2 * (pgOf G).pω p := by
  rw [pω_wtOf hp, pow_add, ← mul_assoc]
  have h1 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (wtOf G p)
  rw [pow_succ] at h1
  exact Nat.mul_lt_mul_of_pos_right (by linarith) (by positivity)

/-- The exponent of a rounded weight is less than the rounded weight. -/
theorem exp_lt_pω {p : ℕ} (hp : p < G.m) : Nat.log 2 (wtOf G p) + pσ G.n < (pgOf G).pω p := by
  rw [pω_wtOf hp]; exact Nat.lt_two_pow_self

namespace InG

theorem frame (h : InG w G mem) {mem' : ℕ → ℕ} (hf : ∀ a < 2 + 3 * G.m, mem' a = mem a) :
    InG w G mem' := by
  refine ⟨h.allowed, h.two_le, ?_, ?_, fun p hp => ?_, fun p hp => ?_, h.word⟩
  · rw [hf 0 (by omega)]; exact h.n0
  · rw [hf 1 (by omega)]; exact h.m1
  · rw [hf _ (by omega), hf _ (by omega)]; exact h.ends p hp
  · rw [hf _ (by omega)]; exact h.wt p hp

theorem one_le (h : InG w G mem) : 1 ≤ G.n := by have := h.two_le; omega

/-- `X ≤ X^16`, and a little more. -/
theorem lt_word (h : InG w G mem) :
    (aH G.n G.m + (pgOf G).maxω + 2) * (aH G.n G.m + (pgOf G).maxω + 2) < 2 ^ w := by
  have hX : 2 ≤ aH G.n G.m + (pgOf G).maxω + 2 := by omega
  calc (aH G.n G.m + (pgOf G).maxω + 2) * (aH G.n G.m + (pgOf G).maxω + 2)
      = (aH G.n G.m + (pgOf G).maxω + 2) ^ 2 := by ring
    _ ≤ (aH G.n G.m + (pgOf G).maxω + 2) ^ 16 := Nat.pow_le_pow_right (by omega) (by norm_num)
    _ < 2 ^ w := h.word

theorem add_lt (h : InG w G mem) : 4 * (aH G.n G.m + (pgOf G).maxω + 2) < 2 ^ w := by
  have := h.lt_word
  have hX : 4 ≤ aH G.n G.m + (pgOf G).maxω + 2 := by have := h.two_le; unfold aH; omega
  have := Nat.mul_le_mul_right (aH G.n G.m + (pgOf G).maxω + 2) hX
  omega

theorem two_le_w (h : InG w G mem) : 2 ≤ w := by
  have h1 := h.add_lt
  have h2 : 16 < 2 ^ w := by unfold aH at h1; omega
  by_contra hw
  have : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The bound of `parP`. -/
theorem par_lt (h : InG w G mem) : 2 ^ 16 * (G.n + 4) ^ 4 < 2 ^ w := by
  set X := aH G.n G.m + (pgOf G).maxω + 2
  have h1 : G.n + 4 ≤ X := by have := h.two_le; unfold X aH; omega
  have h2 : 4 ≤ X := by have := h.two_le; unfold X aH; omega
  calc 2 ^ 16 * (G.n + 4) ^ 4 = 4 ^ 8 * (G.n + 4) ^ 4 := by norm_num
    _ ≤ X ^ 12 * X ^ 4 := Nat.mul_le_mul ((Nat.pow_le_pow_left h2 8).trans
        (Nat.pow_le_pow_right (by omega) (by norm_num))) (Nat.pow_le_pow_left h1 4)
    _ = X ^ 16 := by ring
    _ < 2 ^ w := h.word

/-- The weights times `2^σ`. -/
theorem wt_mul_lt (h : InG w G mem) {p : ℕ} (hp : p < G.m) :
    wtOf G p * 2 ^ pσ G.n < 2 ^ w := by
  have := wtOf_mul_lt hp h.allowed
  have := pω_le_maxω hp
  have := h.add_lt
  omega

/-- The sort keys `e · m + p` with `e < maxω`. -/
theorem key_lt (h : InG w G mem) {e p : ℕ} (he : e < (pgOf G).maxω) (hp : p < G.m) :
    e * G.m + p < 2 ^ w := by
  have := h.lt_word
  have h1 : e * G.m + p ≤ (aH G.n G.m + (pgOf G).maxω + 2) * (aH G.n G.m + (pgOf G).maxω + 2) := by
    have : G.m ≤ aH G.n G.m + (pgOf G).maxω + 2 := by unfold aH; omega
    have := Nat.mul_le_mul (show e ≤ aH G.n G.m + (pgOf G).maxω + 2 by omega) this
    nlinarith
  omega

end InG

/-! ### The input memory of the machine -/

theorem flatMap_getD (l : List (ℕ × ℕ × ℕ)) {p : ℕ} (hp : p < l.length) {k : ℕ} (hk : k < 3) :
    (l.flatMap fun e => [e.1, e.2.1, e.2.2]).getD (3 * p + k) 0 =
      [(l[p]'hp).1, (l[p]'hp).2.1, (l[p]'hp).2.2].getD k 0 := by
  induction l generalizing p with
  | nil => simp at hp
  | cons a l ih =>
    rcases p with _ | p
    · simp only [List.flatMap_cons, List.getElem_cons_zero, Nat.mul_zero, Nat.zero_add]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
      simp [List.getD_eq_getElem?_getD]
    · simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega)]
      have := ih (p := p) (by simp at hp; omega)
      rw [List.getD_eq_getElem?_getD] at this
      simpa [show 3 * (p + 1) + k - 3 = 3 * p + k by omega] using this

theorem encode_getD {p : ℕ} (hp : p < G.m) {k : ℕ} (hk : k < 3) :
    G.encode.getD (2 + 3 * p + k) 0 = [(G.edges[p]'hp).1, (G.edges[p]'hp).2.1,
      (G.edges[p]'hp).2.2].getD k 0 := by
  unfold WGraph.encode
  rw [show 2 + 3 * p + k = 3 * p + k + 1 + 1 by omega]
  simp only [List.getD_cons_succ]
  exact flatMap_getD G.edges hp hk

/-- The input memory of the machine holds the graph. -/
theorem inG_init (h : Allowed G) (hn : 2 ≤ G.n)
    (hw : (aH G.n G.m + (pgOf G).maxω + 2) ^ 16 < 2 ^ w) : InG w G (initMem G.encode) := by
  refine ⟨h, hn, rfl, rfl, fun p hp => ⟨?_, ?_⟩, fun p hp => ?_, hw⟩
  · unfold initMem
    have := encode_getD hp (k := 0) (by norm_num)
    rw [Nat.add_zero] at this
    rw [this]; unfold pgOf; rw [toPG.pu_eq hp]; rfl
  · unfold initMem
    rw [encode_getD hp (k := 1) (by norm_num)]; unfold pgOf; rw [toPG.pv_eq hp]; rfl
  · unfold initMem
    rw [encode_getD hp (k := 2) (by norm_num), wtOf_eq hp]; rfl

end MinCostFlow.LowStretch
