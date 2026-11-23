module

public import WordRAM.Tactic
public import WordRAM.Memory
public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Layout
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Spanner.Subgraph
public import MinCostFlow.Spanner.Embedding
import Mathlib.Tactic

/-!
# Deterministic Word-RAM setup and utility procedures for `Sparsify`

This file provides three deterministic (`Stmt.NoRand`) Word-RAM leaf modules with
explicit `Contract` / `MeetsContract` proofs:

1. `stripLoopsModule` (`stripLoopsBody`): scans `GraphAt mem gAddr J`, writes
   `GraphAt mem' j0Addr (stripLoops J)` and `ListAt mem' nlAddr (nonloopIndices J)`,
   and returns `(stripLoops J).m` in `O(J.m + 1)` time.
2. `embJHStatsModule` (`embJHStatsBody`): computes `(maxDeg J, length J embJH, vcongNat J H' embJH)`
   at `[h, h + 3)` using pre-zeroed scratch arrays `[h + 3, h + 3 + J.n + 2 * H'.n)` in
   `O(J.m * (length J embJH + 1) + 1)` time (independent of `J.n` and `H'.n`).
3. `dedupListModule` (`dedupListBody`): deduplicates a list `xs` (matching `xs.dedup`)
   of integers `< bound` stored at `[srcAddr, srcAddr + len)` into `[dstAddr, dstAddr + keptLen)`
   using pre-zeroed scratch space `[h, h + len + bound)` in `O(len + 1)` time.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## Shared memory frame, arithmetic & fast `Expr.eval` helpers -/

/-- `mem'` agrees with `mem` outside `[lo, hi)`. -/
def AgreeOutside (mem' mem : ℕ → ℕ) (lo hi : ℕ) : Prop :=
  ∀ x, (x < lo ∨ hi ≤ x) → mem' x = mem x

theorem agreeOutside_refl (mem : ℕ → ℕ) (lo hi : ℕ) :
    AgreeOutside mem mem lo hi := fun _ _ => rfl

theorem agreeOutside_update {mem : ℕ → ℕ} {lo hi addr val : ℕ}
    (hlo : lo ≤ addr) (hhi : addr < hi) :
    AgreeOutside (Function.update mem addr val) mem lo hi := by
  intro x hx
  rw [Function.update_of_ne (by rcases hx with h | h <;> omega)]

theorem agreeOutside_trans {m₂ m₁ m₀ : ℕ → ℕ} {lo₁ hi₁ lo₂ hi₂ : ℕ}
    (h₂ : AgreeOutside m₂ m₁ lo₂ hi₂) (h₁ : AgreeOutside m₁ m₀ lo₁ hi₁)
    (hlo : lo₁ ≤ lo₂) (hhi : hi₂ ≤ hi₁) :
    AgreeOutside m₂ m₀ lo₁ hi₁ := by
  intro x hx
  have hx₂ : x < lo₂ ∨ hi₂ ≤ x := by rcases hx with h | h <;> [left; right] <;> omega
  rw [h₂ x hx₂, h₁ x hx]

theorem agreeOutside_mono {mem' mem : ℕ → ℕ} {lo₁ hi₁ lo₂ hi₂ : ℕ}
    (ha : AgreeOutside mem' mem lo₂ hi₂) (hlo : lo₁ ≤ lo₂) (hhi : hi₂ ≤ hi₁) :
    AgreeOutside mem' mem lo₁ hi₁ := by
  intro x hx
  exact ha x (by rcases hx with h | h <;> [left; right] <;> omega)

theorem zeroFrom_of_agreeOutside {mem' mem : ℕ → ℕ} {h lo hi : ℕ}
    (hz : ZeroFrom mem h) (ha : AgreeOutside mem' mem lo hi) (hhi : hi ≤ h) :
    ZeroFrom mem' h := by
  intro x hx
  rw [ha x (Or.inr (le_trans hhi hx)), hz x hx]

theorem listAt_getElem {mem : ℕ → ℕ} {a : ℕ} {xs : List ℕ}
    (h : ListAt mem a xs) {i : ℕ} (hi : i < xs.length) :
    mem (a + i) = xs[i]'hi := by
  induction xs generalizing a i with
  | nil => simp at hi
  | cons x xs ih =>
    rw [listAt_cons] at h
    cases i with
    | zero => simpa using h.1
    | succ j =>
      have hj : j < xs.length := Nat.lt_of_succ_lt_succ hi
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using ih h.2 hj


theorem listAt_eq_of_length_eq {mem : ℕ → ℕ} {a : ℕ} {xs ys : List ℕ}
    (hlen : xs.length = ys.length) (hx : ListAt mem a xs) (hy : ListAt mem a ys) :
    xs = ys :=
  List.ext_getElem hlen fun _ hix hiy => by
    rw [← listAt_getElem hx hix, ← listAt_getElem hy hiy]
theorem listAt_of_congr {mem' mem : ℕ → ℕ} {a : ℕ} {xs : List ℕ}
    (h : ListAt mem a xs) (hEq : ∀ i < xs.length, mem' (a + i) = mem (a + i)) :
    ListAt mem' a xs := by
  induction xs generalizing a with
  | nil => exact listAt_nil mem' a
  | cons x xs ih =>
    rw [listAt_cons] at h ⊢
    refine ⟨?_, ih h.2 fun i hi => ?_⟩
    · simpa using (hEq 0 (by simp)).trans h.1
    · simpa [Nat.add_assoc, Nat.add_comm 1 i] using hEq (i + 1) (by simp; omega)

theorem listAt_of_agreeOutside {mem' mem : ℕ → ℕ} {a lo hi : ℕ} {xs : List ℕ}
    (h : ListAt mem a xs) (ha : AgreeOutside mem' mem lo hi)
    (hdisj : a + xs.length ≤ lo ∨ hi ≤ a) :
    ListAt mem' a xs := by
  refine listAt_of_congr h fun i hi_lt => ?_
  exact ha (a + i) (by rcases hdisj with h1 | h2 <;> [left; right] <;> omega)

theorem listAt_append_right_single {mem : ℕ → ℕ} {a : ℕ} {xs : List ℕ} {x : ℕ}
    (hxs : ListAt mem a xs) (hx : mem (a + xs.length) = x) :
    ListAt mem a (xs ++ [x]) := by
  rw [listAt_append]
  refine ⟨hxs, ?_⟩
  rw [listAt_cons]
  exact ⟨hx, listAt_nil mem _⟩

theorem listAt_append_right_pair {mem : ℕ → ℕ} {a : ℕ} {xs : List ℕ} {u v : ℕ}
    (hxs : ListAt mem a xs) (hu : mem (a + xs.length) = u) (hv : mem (a + xs.length + 1) = v) :
    ListAt mem a (xs ++ [u, v]) := by
  rw [listAt_append]
  refine ⟨hxs, ?_⟩
  rw [listAt_cons, listAt_cons]
  exact ⟨hu, hv, listAt_nil mem _⟩

theorem graphAt_of_agreeOutside {mem' mem : ℕ → ℕ} {a lo hi : ℕ} {G : Graph}
    (h : GraphAt mem a G) (ha : AgreeOutside mem' mem lo hi)
    (hdisj : a + (2 + 2 * G.m) ≤ lo ∨ hi ≤ a) :
    GraphAt mem' a G := by
  have hlen : G.encode.length = 2 + 2 * G.m := graph_encode_length G
  exact listAt_of_agreeOutside h ha (by rwa [hlen])

theorem graphAt_edge_fst_getD {mem : ℕ → ℕ} {a k : ℕ} {G : Graph}
    (h : GraphAt mem a G) (hk : k < G.m) :
    mem (a + (2 + 2 * k)) = (G.edges.getD k (0, 0)).1 := by
  rw [← Nat.add_assoc, graphAt_edge_fst h hk, List.getD_eq_getElem _ _ hk]

theorem graphAt_edge_snd_getD {mem : ℕ → ℕ} {a k : ℕ} {G : Graph}
    (h : GraphAt mem a G) (hk : k < G.m) :
    mem (a + (3 + 2 * k)) = (G.edges.getD k (0, 0)).2 := by
  rw [← Nat.add_assoc, graphAt_edge_snd h hk, List.getD_eq_getElem _ _ hk]

theorem walkAt_of_agreeOutside {mem' mem : ℕ → ℕ} {a lo hi : ℕ} {P : Walk}
    (h : WalkAt mem a P) (ha : AgreeOutside mem' mem lo hi)
    (hdisj : a + (2 + P.verts.length + P.edges.length) ≤ lo ∨ hi ≤ a) :
    WalkAt mem' a P := by
  have hlen : P.encode.length = 2 + P.verts.length + P.edges.length := walk_encode_length P
  exact listAt_of_agreeOutside h ha (by rwa [hlen])

theorem graphAt_unique {mem : ℕ → ℕ} {a : ℕ} {G₁ G₂ : Graph}
    (h1 : GraphAt mem a G₁) (h2 : GraphAt mem a G₂) : G₁ = G₂ := by
  have hn : G₁.n = G₂.n := (graphAt_n h1).symm.trans (graphAt_n h2)
  have hm : G₁.edges.length = G₂.edges.length :=
    (graphAt_m h1).symm.trans (graphAt_m h2)
  have hed : G₁.edges = G₂.edges := List.ext_getElem hm fun i hi1 hi2 => by
    have hf : G₁.edges[i].1 = G₂.edges[i].1 := by
      rw [← graphAt_edge_fst h1 hi1, ← graphAt_edge_fst h2 hi2]
    have hs : G₁.edges[i].2 = G₂.edges[i].2 := by
      rw [← graphAt_edge_snd h1 hi1, ← graphAt_edge_snd h2 hi2]
    exact Prod.ext hf hs
  cases G₁; cases G₂; simp only [Graph.mk.injEq]; exact ⟨hn, hed⟩

theorem walkAt_unique {mem : ℕ → ℕ} {a : ℕ} {P₁ P₂ : Walk}
    (h1 : WalkAt mem a P₁) (h2 : WalkAt mem a P₂) : P₁ = P₂ := by
  have hw1 := walkAt_iff.mp h1
  have hw2 := walkAt_iff.mp h2
  have hv_len : P₁.verts.length = P₂.verts.length := hw1.1.symm.trans hw2.1
  have he_len : P₁.edges.length = P₂.edges.length :=
    hw1.2.2.1.symm.trans (by simpa [hv_len] using hw2.2.2.1)
  have hv : P₁.verts = P₂.verts :=
    listAt_eq_of_length_eq hv_len h1.verts_listAt h2.verts_listAt
  have he : P₁.edges = P₂.edges :=
    listAt_eq_of_length_eq he_len h1.edges_listAt (by simpa [hv_len] using h2.edges_listAt)
  cases P₁; cases P₂; simp only [Walk.mk.injEq]; exact ⟨hv, he⟩

theorem embAt_of_agreeOutside {mem' mem : ℕ → ℕ} {a m bound lo hi : ℕ}
    {emb : ℕ → Walk}
    (hE : EmbAt mem a m emb) (hB : EmbBounded mem a m emb bound)
    (ha : AgreeOutside mem' mem lo hi) (hbound : bound ≤ lo) :
    EmbAt mem' a m emb :=
  (embAt_preserve hE hB (fun x hx => ha x (Or.inl (lt_of_lt_of_le hx hbound)))).1

theorem embBounded_of_agreeOutside {mem' mem : ℕ → ℕ} {a m bound lo hi : ℕ}
    {emb : ℕ → Walk}
    (h : EmbBounded mem a m emb bound) (ha : AgreeOutside mem' mem lo hi)
    (hbound : bound ≤ lo) :
    EmbBounded mem' a m emb bound := by
  refine ⟨h.1, fun j hj => ?_⟩
  have hlt : a + j < bound := by have := h.1; omega
  rw [ha (a + j) (Or.inl (lt_of_lt_of_le hlt hbound))]
  exact h.2 j hj

theorem ev_const {w c : ℕ} (hc : c < 2 ^ w) {st : State} :
    (Expr.const c).eval w st = some c := Expr.eval_const hc

theorem ev_reg {w r : ℕ} {st : State} {v : ℕ} (hr : st.regs r = v) (_hw : v < 2 ^ w) :
    (Expr.reg r).eval w st = some v := by
  simp [Expr.eval, hr]

theorem ev_load {w : ℕ} {st : State} {e : Expr} {a v : ℕ}
    (ha : e.eval w st = some a) (hm : st.mem a = v) (_hw : v < 2 ^ w) :
    (Expr.load e).eval w st = some v := by
  simp [Expr.eval, ha, hm]

theorem ev_add {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (hw : a + b < 2 ^ w) :
    (Expr.bin .add e₁ e₂).eval w st = some (a + b) := Expr.eval_add h₁ h₂ hw

theorem ev_sub {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (_hle : b ≤ a) (hw : a - b < 2 ^ w) :
    (Expr.bin .sub e₁ e₂).eval w st = some (a - b) := by
  simp [Expr.eval, BinOp.eval, h₁, h₂, hw]

theorem ev_mul {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (hw : a * b < 2 ^ w) :
    (Expr.bin .mul e₁ e₂).eval w st = some (a * b) := by
  simp [Expr.eval, BinOp.eval, h₁, h₂, hw]

theorem ev_lt_t {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (hlt : a < b) (hw : 1 < 2 ^ w) :
    (Expr.bin .lt e₁ e₂).eval w st = some 1 := Expr.eval_lt_true h₁ h₂ hlt hw

theorem ev_lt_f {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (hle : b ≤ a) (hw : 1 < 2 ^ w) :
    (Expr.bin .lt e₁ e₂).eval w st = some 0 := Expr.eval_lt_false h₁ h₂ hle hw

theorem ev_eq_t {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (heq : a = b) (hw : 1 < 2 ^ w) :
    (Expr.bin .eq e₁ e₂).eval w st = some 1 := by
  simp [Expr.eval, BinOp.eval, h₁, h₂, heq, hw]

theorem ev_eq_f {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (hne : a ≠ b) (hw : 1 < 2 ^ w) :
    (Expr.bin .eq e₁ e₂).eval w st = some 0 := by
  have hw0 : 0 < 2 ^ w := Nat.zero_lt_of_lt hw
  simp [Expr.eval, BinOp.eval, h₁, h₂, hne, hw0]

theorem fold_max_cast_le {α : Type*} (s : Finset α) (f : α → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x ∈ s, (f x : ℝ) ≤ B) : ((s.fold max 0 f : ℕ) : ℝ) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
    rw [Finset.fold_insert ha]
    push_cast
    exact max_le (h a (Finset.mem_insert_self a s)) (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

theorem fold_max_update_add_one (n : ℕ) (f : ℕ → ℕ) (u : ℕ) (hu : u < n) :
    (Finset.range n).fold max 0 (fun x => if x = u then f x + 1 else f x) =
      max ((Finset.range n).fold max 0 f) (f u + 1) := by
  refine le_antisymm ?_ ?_
  · rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le _, fun x hx => ?_⟩
    rw [Finset.mem_range] at hx
    rw [le_max_iff]
    by_cases hxu : x = u
    · subst hxu; right; simp
    · left; simp [hxu]
      rw [Finset.le_fold_max]
      exact Or.inr ⟨x, Finset.mem_range.mpr hx, le_rfl⟩
  · refine max_le ?_ ?_
    · rw [Finset.fold_max_le]
      refine ⟨Nat.zero_le _, fun x hx => ?_⟩
      have hge : f x ≤ (Finset.range n).fold max 0 fun y => if y = u then f y + 1 else f y := by
        rw [Finset.le_fold_max]
        refine Or.inr ⟨x, hx, ?_⟩
        by_cases hxu : x = u <;> simp [hxu]
      exact hge
    · rw [Finset.le_fold_max]
      exact Or.inr ⟨u, Finset.mem_range.mpr hu, by simp⟩

theorem list_range_map_sum (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        List.map_nil, List.sum_nil, Finset.sum_range_succ, ih]
    simp

/-- Exact natural-number vertex congestion of uniform weights (`fun _ => 1`) of `embJH : J → H'`. -/
def vcongNat (J H' : Graph) (embJH : ℕ → Walk) : ℕ :=
  (Finset.range H'.n).fold max 0 fun x =>
    ((Finset.range J.m).filter fun eJ => x ∈ (embJH eJ).verts).card

theorem vcongNat_cast_eq (J H' : Graph) (embJH : ℕ → Walk) :
    (vcongNat J H' embJH : ℝ) = vcong J H' (fun _ => 1) embJH := by
  refine le_antisymm ?_ ?_
  · refine fold_max_cast_le _ _ (vcong_nonneg J H' (fun _ => 1) embJH) fun x hx => ?_
    have hcard :
        (((Finset.range J.m).filter fun eJ => x ∈ (embJH eJ).verts).card : ℝ) =
          vcongAt J (fun _ => 1) embJH x := by
      simp [vcongAt]
    rw [hcard]
    exact vcongAt_le_vcong _ embJH (Finset.mem_range.mp hx)
  · rw [vcong_le_iff]
    refine ⟨Nat.cast_nonneg _, fun x hx => ?_⟩
    have hcard :
        vcongAt J (fun _ => 1) embJH x =
          (((Finset.range J.m).filter fun eJ => x ∈ (embJH eJ).verts).card : ℝ) := by
      simp [vcongAt]
    rw [hcard]
    have hfold : ((Finset.range J.m).filter fun eJ => x ∈ (embJH eJ).verts).card ≤
        vcongNat J H' embJH := by
      unfold vcongNat
      rw [Finset.le_fold_max]
      exact Or.inr ⟨x, Finset.mem_range.mpr hx, le_rfl⟩
    exact_mod_cast hfold

/-- Total number of walk vertices across edges `0 .. J.m - 1` of `emb`, read from memory. -/
def embVertSumMem (mem : ℕ → ℕ) (jAddr embAddr : ℕ) : ℕ :=
  ((List.range (mem (jAddr + 1))).map fun e => mem (mem (embAddr + e))).sum

theorem embVertSumMem_eq {mem : ℕ → ℕ} {jAddr embAddr : ℕ} {J : Graph}
    {emb : ℕ → Walk} (hG : GraphAt mem jAddr J) (hE : EmbAt mem embAddr J.m emb) :
    embVertSumMem mem jAddr embAddr =
      ∑ e ∈ Finset.range J.m, (emb e).verts.length := by
  unfold embVertSumMem
  rw [graphAt_m hG, list_range_map_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have he_m : e < J.m := Finset.mem_range.mp he
  exact (hE e he_m).verts_len

/-! ## Procedure 1: `stripLoopsModule` (`O(J.m + 1)`) -/

/-- `stripLoopsBody` reads `GraphAt mem gAddr J` (`args = [gAddr, j0Addr, nlAddr]`), writes
`GraphAt mem' j0Addr (stripLoops J)` and `ListAt mem' nlAddr (nonloopIndices J)`,
and returns `(stripLoops J).m`. -/
def stripLoopsBody : Stmt :=
  .store (.reg 1) (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 5 (.const 0) ;;
  forRange 4 (.const 0) (.reg 3) (
    .assign 6 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 4))))) ;;
    .assign 7 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 4))))) ;;
    .cond (.bin .eq (.bin .eq (.reg 6) (.reg 7)) (.const 0)) (
      .store (.bin .add (.reg 1) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 5)))) (.reg 6) ;;
      .store (.bin .add (.reg 1) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 5)))) (.reg 7) ;;
      .store (.bin .add (.reg 2) (.reg 5)) (.reg 4) ;;
      .assign 5 (.bin .add (.reg 5) (.const 1))
    ) (.assign 6 (.const 0))
  ) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.reg 5) ;;
  .ret (.reg 5)

/-- Single-procedure module for `stripLoops`. -/
def stripLoopsModule : List Stmt := [stripLoopsBody]

theorem stripLoopsBody_noRand : stripLoopsBody.NoRand := by
  simp [stripLoopsBody, forRange, forUp, Stmt.NoRand]

theorem stripLoopsModule_noRand : ∀ s ∈ stripLoopsModule, s.NoRand := by
  simp only [stripLoopsModule, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact stripLoopsBody_noRand

/-- Contract for `stripLoops`: `args = [gAddr, j0Addr, nlAddr]`. -/
def stripLoopsContract (w : ℕ) : Contract where
  pre args mem := ∃ (gAddr j0Addr nlAddr : ℕ) (J : Graph),
    args = [gAddr, j0Addr, nlAddr] ∧
    GraphAt mem gAddr J ∧
    (∀ x ∈ J.encode, x < 2 ^ w) ∧
    1 < 2 ^ w ∧
    gAddr + (2 + 2 * J.m) ≤ j0Addr ∧
    j0Addr + (2 + 2 * J.m) ≤ nlAddr ∧
    nlAddr + J.m < 2 ^ w
  post args mem v mem' := ∀ gAddr j0Addr nlAddr (J : Graph),
    args = [gAddr, j0Addr, nlAddr] → GraphAt mem gAddr J →
      v = (stripLoops J).m ∧
      GraphAt mem' j0Addr (stripLoops J) ∧
      ListAt mem' nlAddr (nonloopIndices J) ∧
      AgreeOutside mem' mem j0Addr (nlAddr + (stripLoops J).m) ∧
      (∀ x, j0Addr + (2 + 2 * (stripLoops J).m) ≤ x → x < nlAddr → mem' x = mem x)
  cost args mem := 115 * mem (args.getD 0 0 + 1) + 55

private def stripNlPrefix (J : Graph) (k : ℕ) : List ℕ :=
  (List.range k).filter fun i => decide ((J.edges.getD i (0, 0)).1 ≠ (J.edges.getD i (0, 0)).2)

private def stripEdgeWords (J : Graph) (k : ℕ) : List ℕ :=
  ((stripNlPrefix J k).map fun i => J.edges.getD i (0, 0)).flatMap fun e => [e.1, e.2]

private def stripLoopsInv (gAddr j0Addr nlAddr : ℕ) (J : Graph) (mem : ℕ → ℕ)
    (k : ℕ) (st : State) : Prop :=
  st.regs 0 = gAddr ∧ st.regs 1 = j0Addr ∧ st.regs 2 = nlAddr ∧ st.regs 3 = J.m ∧
  st.regs 4 = k ∧ st.regs 5 = (stripNlPrefix J k).length ∧
  k ≤ J.m ∧ (stripNlPrefix J k).length ≤ k ∧
  st.mem j0Addr = J.n ∧
  ListAt st.mem (j0Addr + 2) (stripEdgeWords J k) ∧
  ListAt st.mem nlAddr (stripNlPrefix J k) ∧
  AgreeOutside st.mem mem j0Addr (nlAddr + (stripNlPrefix J k).length) ∧
  (∀ x, j0Addr + (2 + 2 * (stripNlPrefix J k).length) ≤ x → x < nlAddr → st.mem x = mem x)

private theorem stripLoops_filter_step (J : Graph) (k : ℕ) :
    stripNlPrefix J (k + 1) =
      if (J.edges.getD k (0, 0)).1 ≠ (J.edges.getD k (0, 0)).2 then
        stripNlPrefix J k ++ [k]
      else
        stripNlPrefix J k := by
  unfold stripNlPrefix
  rw [List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]
  by_cases h : (J.edges[k]?.getD (0, 0)).1 = (J.edges[k]?.getD (0, 0)).2
  · simp [List.getD, h]
  · simp [List.getD, h]

private theorem flatMap_pair_length {α : Type*} (xs : List α) (f : α → ℕ × ℕ) :
    (xs.flatMap fun x => [(f x).1, (f x).2]).length = 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [ih]; omega

private theorem stripEdgeWords_len (J : Graph) (k : ℕ) :
    (stripEdgeWords J k).length = 2 * (stripNlPrefix J k).length := by
  simpa [stripEdgeWords, List.flatMap_map] using
    flatMap_pair_length (stripNlPrefix J k) (fun i => J.edges.getD i (0, 0))

private theorem stripLoops_loop_triple {w : ℕ} {p : Program}
    (gAddr j0Addr nlAddr : ℕ) (J : Graph) (mem : ℕ → ℕ)
    (hG : GraphAt mem gAddr J) (hJenc : ∀ x ∈ J.encode, x < 2 ^ w) (hw1 : 1 < 2 ^ w)
    (hgAddr_w : gAddr < 2 ^ w) (hj0Addr_w : j0Addr < 2 ^ w) (hnlAddr_w : nlAddr < 2 ^ w)
    (hgj : gAddr + (2 + 2 * J.m) ≤ j0Addr) (hjn : j0Addr + (2 + 2 * J.m) ≤ nlAddr)
    (hnl : nlAddr + J.m < 2 ^ w) :
    Triple w p
      (fun st =>
        st.regs 0 = gAddr ∧ st.regs 1 = j0Addr ∧ st.regs 2 = nlAddr ∧
        st.regs 3 = J.m ∧ st.regs 5 = 0 ∧
        st.mem j0Addr = J.n ∧ AgreeOutside st.mem mem j0Addr (j0Addr + 1))
      (forRange 4 (.const 0) (.reg 3) (
        .assign 6 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 4))))) ;;
        .assign 7 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 4))))) ;;
        .cond (.bin .eq (.bin .eq (.reg 6) (.reg 7)) (.const 0)) (
          .store (.bin .add (.reg 1) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 5)))) (.reg 6) ;;
          .store (.bin .add (.reg 1) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 5)))) (.reg 7) ;;
          .store (.bin .add (.reg 2) (.reg 5)) (.reg 4) ;;
          .assign 5 (.bin .add (.reg 5) (.const 1))
        ) (.assign 6 (.const 0))
      ))
      (normalPost (stripLoopsInv gAddr j0Addr nlAddr J mem J.m))
      (fun _ => J.m * (100 + (Expr.reg 3).size + 8) + ((Expr.const 0).size + (Expr.reg 3).size + 5)) := by
  have hw0 : 0 < 2 ^ w := Nat.zero_lt_of_lt hw1
  have hmJ_w : J.m < 2 ^ w := by omega
  refine Triple.forRange_const (p := p) (w := w) (r := 4) (lo := .const 0) (hi := .reg 3)
    (Inv := stripLoopsInv gAddr j0Addr nlAddr J mem) 100 0 J.m (Nat.zero_le _) hw1 (fun _ => hmJ_w)
    (fun st hP => by
      rcases hP with ⟨r0, r1, r2, r3, r5, hmem_n, hag⟩
      refine ⟨Expr.eval_const hw0, ⟨r0, r1, r2, r3, by simp [Function.update_self],
        by simpa [stripNlPrefix] using r5, Nat.zero_le _, Nat.le_refl _, hmem_n,
        by simp [stripEdgeWords, stripNlPrefix, listAt_nil],
        by simp [stripNlPrefix, listAt_nil],
        by simp [stripNlPrefix]; exact agreeOutside_mono hag le_rfl (by omega),
        fun x hx1 hx2 => hag x (Or.inr (by omega))⟩⟩)
    (fun _ _ _ _ h => h.2.2.2.2.1)
    (fun _ _ _ _ h => ev_reg h.2.2.2.1 hmJ_w) ?_
  intro k _ hk st ω hInv
  rcases hInv with ⟨r0, r1, r2, r3, r4, r5, hkm, hcnt_le, hmem_n, hEW, hNL, hag, hmid⟩
  set cnt := (stripNlPrefix J k).length
  set u := (J.edges.getD k (0, 0)).1
  set v := (J.edges.getD k (0, 0)).2
  have hk_w : k < 2 ^ w := by omega
  have h2k_w : 2 * k < 2 ^ w := by omega
  have h2k2_w : 2 + 2 * k < 2 ^ w := by omega
  have h2k3_w : 3 + 2 * k < 2 ^ w := by omega
  have ha_u_w : gAddr + (2 + 2 * k) < 2 ^ w := by omega
  have ha_v_w : gAddr + (3 + 2 * k) < 2 ^ w := by omega
  have hG_st : GraphAt st.mem gAddr J := graphAt_of_agreeOutside hG hag (Or.inl hgj)
  have hu_mem : st.mem (gAddr + (2 + 2 * k)) = u := graphAt_edge_fst_getD hG_st hk
  have hv_mem : st.mem (gAddr + (3 + 2 * k)) = v := graphAt_edge_snd_getD hG_st hk
  have hu_w : u < 2 ^ w := by
    refine hJenc u ?_
    have hget := listAt_getElem hG (i := 2 + 2 * k) (by rw [graph_encode_length]; omega)
    dsimp only [u]; rw [← graphAt_edge_fst_getD hG hk, hget]; exact List.getElem_mem _
  have hv_w : v < 2 ^ w := by
    refine hJenc v ?_
    have hget := listAt_getElem hG (i := 3 + 2 * k) (by rw [graph_encode_length]; omega)
    dsimp only [v]; rw [← graphAt_edge_snd_getD hG hk, hget]; exact List.getElem_mem _
  have hev_u : (Expr.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 4))))).eval w st = some u :=
    ev_load (ev_add (ev_reg r0 hgAddr_w) (ev_add (ev_const (by omega))
      (ev_mul (ev_const (by omega)) (ev_reg r4 hk_w) h2k_w) h2k2_w) ha_u_w) hu_mem hu_w
  let st1 : State := ⟨st.mem, Function.update st.regs 6 u, st.pos⟩
  have hev_v : (Expr.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 4))))).eval w st1 = some v :=
    ev_load (ev_add (ev_reg (by simp [st1, r0]) hgAddr_w) (ev_add (ev_const (by omega))
      (ev_mul (ev_const (by omega)) (ev_reg (by simp [st1, r4]) hk_w) h2k_w) h2k3_w) ha_v_w) hv_mem hv_w
  let stA : State := ⟨st.mem, Function.update st1.regs 7 v, st.pos⟩
  have hr6A : stA.regs 6 = u := by simp [stA, st1]
  have hr7A : stA.regs 7 = v := by simp [stA]
  apply runs_start_le
  refine runs_seq_assign_le hev_u ?_
  refine runs_seq_assign_le hev_v ?_
  by_cases huv : u = v
  · have huv' : (J.edges.getD k (0, 0)).1 = (J.edges.getD k (0, 0)).2 := huv
    have hstep : stripNlPrefix J (k + 1) = stripNlPrefix J k := by
      rw [stripLoops_filter_step]; simp only [List.getD] at huv' ⊢; simp [huv']
    have hcond : (Expr.bin .eq (.bin .eq (.reg 6) (.reg 7)) (.const 0)).eval w stA = some 0 :=
      ev_eq_f (ev_eq_t (ev_reg hr6A hu_w) (ev_reg hr7A hv_w) huv hw1) (ev_const hw0) (by decide) hw1
    refine runs_cond_le hcond (fun h0 => absurd rfl h0) fun _ => ?_
    refine runs_assign_le (ev_const hw0) ?_ (by norm_num [Expr.size])
    · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, hmem_n, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try dsimp only [stA, st1]
      · simp [r0]
      · simp [r1]
      · simp [r2]
      · simp [r3]
      · simp [Function.update_self]
      · simpa [cnt, hstep] using r5
      · rw [hstep]; omega
      · simpa [stripEdgeWords, hstep] using hEW
      · simpa [hstep] using hNL
      · simpa [hstep] using hag
      · simpa [hstep] using hmid
      · simp [r4]
  · have huv' : (J.edges.getD k (0, 0)).1 ≠ (J.edges.getD k (0, 0)).2 := huv
    have hstep : stripNlPrefix J (k + 1) = stripNlPrefix J k ++ [k] := by
      rw [stripLoops_filter_step]; simp only [List.getD] at huv' ⊢; simp [huv']
    have hew_next : stripEdgeWords J (k + 1) = stripEdgeWords J k ++ [u, v] := by
      simp [stripEdgeWords, hstep, List.flatMap_append, u, v]
    have hcond : (Expr.bin .eq (.bin .eq (.reg 6) (.reg 7)) (.const 0)).eval w stA = some 1 :=
      ev_eq_t (ev_eq_f (ev_reg hr6A hu_w) (ev_reg hr7A hv_w) huv hw1) (ev_const hw0) rfl hw1
    have hcnt_w : cnt < 2 ^ w := by omega
    have h2c_w : 2 * cnt < 2 ^ w := by omega
    have h2c2_w : 2 + 2 * cnt < 2 ^ w := by omega
    have h2c3_w : 3 + 2 * cnt < 2 ^ w := by omega
    have hdst_u : j0Addr + (2 + 2 * cnt) < 2 ^ w := by omega
    have hdst_v : j0Addr + (3 + 2 * cnt) < 2 ^ w := by omega
    have hdst_nl : nlAddr + cnt < 2 ^ w := by omega
    have hcnt1_w : cnt + 1 < 2 ^ w := by omega
    have ha1 : (Expr.bin .add (.reg 1) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 5)))).eval w stA =
        some (j0Addr + (2 + 2 * cnt)) :=
      ev_add (ev_reg (by simp [stA, st1, r1]) hj0Addr_w)
        (ev_add (ev_const (by omega)) (ev_mul (ev_const (by omega))
          (ev_reg (by simp [stA, st1, r5]) hcnt_w) h2c_w) h2c2_w) hdst_u
    let mem1 := Function.update st.mem (j0Addr + (2 + 2 * cnt)) u
    let stB : State := ⟨mem1, stA.regs, st.pos⟩
    have ha2 : (Expr.bin .add (.reg 1) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 5)))).eval w stB =
        some (j0Addr + (3 + 2 * cnt)) :=
      ev_add (ev_reg (by simp [stB, stA, st1, r1]) hj0Addr_w)
        (ev_add (ev_const (by omega)) (ev_mul (ev_const (by omega))
          (ev_reg (by simp [stB, stA, st1, r5]) hcnt_w) h2c_w) h2c3_w) hdst_v
    let mem2 := Function.update mem1 (j0Addr + (3 + 2 * cnt)) v
    let stC : State := ⟨mem2, stA.regs, st.pos⟩
    have ha3 : (Expr.bin .add (.reg 2) (.reg 5)).eval w stC = some (nlAddr + cnt) :=
      ev_add (ev_reg (by simp [stC, stA, st1, r2]) hnlAddr_w)
        (ev_reg (by simp [stC, stA, st1, r5]) hcnt_w) hdst_nl
    let mem3 := Function.update mem2 (nlAddr + cnt) k
    let stD : State := ⟨mem3, stA.regs, st.pos⟩
    have hev5' : (Expr.bin .add (.reg 5) (.const 1)).eval w stD = some (cnt + 1) :=
      ev_add (ev_reg (by simp [stD, stA, st1, r5]) hcnt_w) (ev_const hw1) hcnt1_w
    refine runs_cond_le hcond (fun _ => ?_) (fun h1 => absurd h1 (by decide))
    refine runs_seq_store_le ha1 (ev_reg hr6A hu_w) ?_
    refine runs_seq_store_le ha2 (ev_reg hr7A hv_w) ?_
    refine runs_seq_store_le ha3 (ev_reg (by simp [r4]) hk_w) ?_
    refine runs_assign_le hev5' ?_ (by norm_num [Expr.size])
    · have hlen_next : (stripNlPrefix J (k + 1)).length = cnt + 1 := by
        rw [hstep, List.length_append]; simp [cnt]
      have hag1 : AgreeOutside mem1 st.mem (j0Addr + (2 + 2 * cnt)) (nlAddr + (cnt + 1)) :=
        agreeOutside_update (lo := j0Addr + (2 + 2 * cnt)) (hi := nlAddr + (cnt + 1)) le_rfl (by omega)
      have hag2 : AgreeOutside mem2 mem1 (j0Addr + (2 + 2 * cnt)) (nlAddr + (cnt + 1)) :=
        agreeOutside_update (lo := j0Addr + (2 + 2 * cnt)) (hi := nlAddr + (cnt + 1)) (by omega) (by omega)
      have hag3 : AgreeOutside mem3 mem2 (j0Addr + (2 + 2 * cnt)) (nlAddr + (cnt + 1)) :=
        agreeOutside_update (lo := j0Addr + (2 + 2 * cnt)) (hi := nlAddr + (cnt + 1)) (by omega) (by omega)
      have hag_step : AgreeOutside mem3 st.mem (j0Addr + (2 + 2 * cnt)) (nlAddr + (cnt + 1)) :=
        agreeOutside_trans hag3 (agreeOutside_trans hag2 hag1 le_rfl le_rfl) le_rfl le_rfl
      have hew_len : (stripEdgeWords J k).length = 2 * cnt := stripEdgeWords_len J k
      have hmem3_u : mem3 (j0Addr + 2 + (stripEdgeWords J k).length) = u := by
        rw [hew_len]
        simp only [mem3, mem2, mem1]
        rw [Function.update_of_ne (by omega : j0Addr + 2 + 2 * cnt ≠ nlAddr + cnt),
            Function.update_of_ne (by omega : j0Addr + 2 + 2 * cnt ≠ j0Addr + (3 + 2 * cnt)),
            show j0Addr + 2 + 2 * cnt = j0Addr + (2 + 2 * cnt) by omega, Function.update_self]
      have hmem3_v : mem3 (j0Addr + 2 + (stripEdgeWords J k).length + 1) = v := by
        rw [hew_len]
        simp only [mem3, mem2]
        rw [Function.update_of_ne (by omega : j0Addr + 2 + 2 * cnt + 1 ≠ nlAddr + cnt),
            show j0Addr + 2 + 2 * cnt + 1 = j0Addr + (3 + 2 * cnt) by omega, Function.update_self]
      have hmem3_nl : mem3 (nlAddr + (stripNlPrefix J k).length) = k := by
        change mem3 (nlAddr + cnt) = k; exact Function.update_self _ _ _
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try dsimp only [stD, stC, stB, stA, st1]
      · simp [r0]
      · simp [r1]
      · simp [r2]
      · simp [r3]
      · simp [Function.update_self]
      · rw [hlen_next]; simp [Function.update_self]
      · rw [hlen_next]; omega
      · change mem3 j0Addr = J.n
        rw [hag_step j0Addr (Or.inl (by omega))]; exact hmem_n
      · change ListAt mem3 (j0Addr + 2) (stripEdgeWords J (k + 1))
        rw [hew_next]
        refine listAt_append_right_pair ?_ hmem3_u hmem3_v
        exact listAt_of_agreeOutside hEW hag_step (Or.inl (by rw [hew_len]; omega))
      · change ListAt mem3 nlAddr (stripNlPrefix J (k + 1))
        rw [hstep]
        refine listAt_append_right_single ?_ hmem3_nl
        refine listAt_of_congr hNL fun i hi => ?_
        simp only [mem3, mem2, mem1]
        rw [Function.update_of_ne (by omega : nlAddr + i ≠ nlAddr + cnt),
            Function.update_of_ne (by omega : nlAddr + i ≠ j0Addr + (3 + 2 * cnt)),
            Function.update_of_ne (by omega : nlAddr + i ≠ j0Addr + (2 + 2 * cnt))]
      · change AgreeOutside mem3 mem j0Addr (nlAddr + (stripNlPrefix J (k + 1)).length)
        rw [hlen_next]
        exact agreeOutside_trans hag_step (agreeOutside_mono hag le_rfl (by omega)) (by omega) le_rfl
      · intro x hx1 hx2
        rw [hlen_next] at hx1
        change mem3 x = mem x
        dsimp only [mem3, mem2, mem1]
        rw [Function.update_of_ne (by omega : x ≠ nlAddr + cnt),
            Function.update_of_ne (by omega : x ≠ j0Addr + (3 + 2 * cnt)),
            Function.update_of_ne (by omega : x ≠ j0Addr + (2 + 2 * cnt))]
        exact hmid x (by omega) hx2
      · simp [r4]

/-- `stripLoopsModule` meets `stripLoopsContract w` in `O(J.m + 1)` time. -/
theorem stripLoops_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b stripLoopsModule) :
    MeetsContract w p b (stripLoopsContract w) := by
  refine meetsContract_of_triple hp.head ?_
  intro args mem pos hwords hpre
  dsimp only [stripLoopsContract] at hpre
  rcases hpre with ⟨gAddr, j0Addr, nlAddr, J, rfl, hG, hJenc, hw1, hgj, hjn, hnl⟩
  have hw0 : 0 < 2 ^ w := Nat.zero_lt_of_lt hw1
  have hmJ_w : J.m < 2 ^ w := by omega
  have hJn_w : J.n < 2 ^ w := hJenc J.n (by simp [Graph.encode])
  have hgAddr_w : gAddr < 2 ^ w := hwords gAddr (by simp)
  have hj0Addr_w : j0Addr < 2 ^ w := hwords j0Addr (by simp)
  have hnlAddr_w : nlAddr < 2 ^ w := hwords nlAddr (by simp)
  have hg_load0 : mem gAddr = J.n := graphAt_n hG
  have hg_load1 : mem (gAddr + 1) = J.m := graphAt_m hG
  have he_g1 : gAddr + 1 < 2 ^ w := by omega
  have ht1 : Triple w p (fun st => st = startState [gAddr, j0Addr, nlAddr] mem pos)
      (.store (.reg 1) (.load (.reg 0)))
      (normalPost fun st =>
        st.regs 0 = gAddr ∧ st.regs 1 = j0Addr ∧ st.regs 2 = nlAddr ∧
        st.mem j0Addr = J.n ∧ AgreeOutside st.mem mem j0Addr (j0Addr + 1))
      (fun _ => (Expr.reg 1).size + (Expr.load (.reg 0)).size + 1) := by
    refine Triple.store (addr := fun _ => j0Addr) (val := fun _ => J.n) ?_ ?_ ?_
    · intro st h; subst h; exact ev_reg (by simp [startState]) hj0Addr_w
    · intro st h; subst h; exact ev_load (ev_reg (by simp [startState]) hgAddr_w) hg_load0 hJn_w
    · intro st h; subst h; exact ⟨by simp [startState], by simp [startState], by simp [startState],
        by simp [Function.update_self], agreeOutside_update le_rfl (by omega)⟩
  have ht2 : Triple w p
      (fun st => st.regs 0 = gAddr ∧ st.regs 1 = j0Addr ∧ st.regs 2 = nlAddr ∧
        st.mem j0Addr = J.n ∧ AgreeOutside st.mem mem j0Addr (j0Addr + 1))
      (.assign 3 (.load (.bin .add (.reg 0) (.const 1))))
      (normalPost fun st =>
        st.regs 0 = gAddr ∧ st.regs 1 = j0Addr ∧ st.regs 2 = nlAddr ∧ st.regs 3 = J.m ∧
        st.mem j0Addr = J.n ∧ AgreeOutside st.mem mem j0Addr (j0Addr + 1))
      (fun _ => (Expr.load (.bin .add (.reg 0) (.const 1))).size + 1) := by
    refine Triple.assign (val := fun _ => J.m) ?_ ?_
    · intro st h; rcases h with ⟨r0, _, _, _, hag⟩
      have hm_eq : st.mem (gAddr + 1) = J.m := by rw [hag (gAddr + 1) (Or.inl (by omega)), hg_load1]
      exact ev_load (ev_add (ev_reg r0 hgAddr_w) (ev_const hw1) he_g1) hm_eq hmJ_w
    · intro st h; rcases h with ⟨r0, r1, r2, hmn, hag⟩
      exact ⟨by simp [r0], by simp [r1], by simp [r2], by simp [Function.update_self], hmn, hag⟩
  have ht3 : Triple w p
      (fun st => st.regs 0 = gAddr ∧ st.regs 1 = j0Addr ∧ st.regs 2 = nlAddr ∧ st.regs 3 = J.m ∧
        st.mem j0Addr = J.n ∧ AgreeOutside st.mem mem j0Addr (j0Addr + 1))
      (.assign 5 (.const 0))
      (normalPost fun st =>
        st.regs 0 = gAddr ∧ st.regs 1 = j0Addr ∧ st.regs 2 = nlAddr ∧ st.regs 3 = J.m ∧
        st.regs 5 = 0 ∧ st.mem j0Addr = J.n ∧ AgreeOutside st.mem mem j0Addr (j0Addr + 1))
      (fun _ => (Expr.const 0).size + 1) := by
    refine Triple.assign (val := fun _ => 0) (fun _ _ => Expr.eval_const hw0) ?_
    intro st h; rcases h with ⟨r0, r1, r2, r3, hmn, hag⟩
    exact ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [Function.update_self], hmn, hag⟩
  have hfor := stripLoops_loop_triple (p := p) gAddr j0Addr nlAddr J mem hG hJenc hw1
    hgAddr_w hj0Addr_w hnlAddr_w hgj hjn hnl
  have hm0_le_m : (stripNlPrefix J J.m).length ≤ J.m := by
    have : (stripNlPrefix J J.m).length ≤ (List.range J.m).length := List.length_filter_le _ _
    simpa using this
  have hnl_eq : stripNlPrefix J J.m = nonloopIndices J := rfl
  have hm0_eq : (stripNlPrefix J J.m).length = (stripLoops J).m := by
    simp [stripNlPrefix, stripLoops, nonloopIndices, Graph.m]
  have ht4 : Triple w p (stripLoopsInv gAddr j0Addr nlAddr J mem J.m)
      (.store (.bin .add (.reg 1) (.const 1)) (.reg 5))
      (normalPost fun st =>
        st.regs 5 = (stripNlPrefix J J.m).length ∧
        st.mem j0Addr = J.n ∧
        st.mem (j0Addr + 1) = (stripNlPrefix J J.m).length ∧
        ListAt st.mem (j0Addr + 2) (stripEdgeWords J J.m) ∧
        ListAt st.mem nlAddr (stripNlPrefix J J.m) ∧
        AgreeOutside st.mem mem j0Addr (nlAddr + (stripLoops J).m) ∧
        (∀ x, j0Addr + (2 + 2 * (stripLoops J).m) ≤ x → x < nlAddr → st.mem x = mem x))
      (fun _ => (Expr.bin .add (.reg 1) (.const 1)).size + (Expr.reg 5).size + 1) := by
    refine Triple.store (addr := fun _ => j0Addr + 1) (val := fun _ => (stripNlPrefix J J.m).length)
      ?_ ?_ ?_
    · intro st h; rcases h with ⟨_, r1, _⟩; exact ev_add (ev_reg r1 hj0Addr_w) (ev_const hw1) (by omega)
    · intro st h; rcases h with ⟨_, _, _, _, _, r5, _⟩; exact ev_reg r5 (by omega)
    · intro st h
      rcases h with ⟨_, _, _, _, _, r5, _, hcnt_le, hmem_n, hEW, hNL, hag, hmid⟩
      refine ⟨r5, ?_, by simp [Function.update_self], ?_, ?_, ?_, ?_⟩
      · dsimp only; rw [Function.update_of_ne (by omega : j0Addr ≠ j0Addr + 1)]; exact hmem_n
      · exact listAt_of_agreeOutside hEW
          (agreeOutside_update (lo := j0Addr + 1) (hi := j0Addr + 2) le_rfl (by omega))
          (Or.inr (by omega))
      · exact listAt_of_agreeOutside hNL
          (agreeOutside_update (lo := j0Addr + 1) (hi := j0Addr + 2) le_rfl (by omega))
          (Or.inr (by omega))
      · rw [← hm0_eq]
        exact agreeOutside_trans
          (agreeOutside_update (lo := j0Addr + 1) (hi := j0Addr + 2) le_rfl (by omega))
          hag (by omega) (by omega)
      · intro x hx1 hx2
        dsimp only
        rw [Function.update_of_ne (by omega : x ≠ j0Addr + 1)]
        exact hmid x (by rwa [hm0_eq]) hx2
  have ht5 : Triple w p
      (fun st =>
        st.regs 5 = (stripNlPrefix J J.m).length ∧
        st.mem j0Addr = J.n ∧
        st.mem (j0Addr + 1) = (stripNlPrefix J J.m).length ∧
        ListAt st.mem (j0Addr + 2) (stripEdgeWords J J.m) ∧
        ListAt st.mem nlAddr (stripNlPrefix J J.m) ∧
        AgreeOutside st.mem mem j0Addr (nlAddr + (stripLoops J).m) ∧
        (∀ x, j0Addr + (2 + 2 * (stripLoops J).m) ≤ x → x < nlAddr → st.mem x = mem x))
      (.ret (.reg 5))
      (retPost fun v st =>
        ∀ g' j0' nl' J', [gAddr, j0Addr, nlAddr] = [g', j0', nl'] → GraphAt mem g' J' →
          v = (stripLoops J').m ∧
          GraphAt st.mem j0' (stripLoops J') ∧
          ListAt st.mem nl' (nonloopIndices J') ∧
          AgreeOutside st.mem mem j0' (nl' + (stripLoops J').m) ∧
          (∀ x, j0' + (2 + 2 * (stripLoops J').m) ≤ x → x < nl' → st.mem x = mem x))
      (fun _ => (Expr.reg 5).size + 1) := by
    refine Triple.ret (val := fun _ => (stripNlPrefix J J.m).length) ?_ ?_
    · intro st h; exact ev_reg h.1 (by omega)
    · intro st h g' j0' nl' J' heq hG'
      simp only [List.cons.injEq, and_true] at heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      have heqJ : J' = J := graphAt_unique hG' hG
      subst heqJ
      rcases h with ⟨_, hmem_n, hmem_m, hEW, hNL, hag, hmid⟩
      refine ⟨hm0_eq, ?_, ?_, hag, hmid⟩
      · change ListAt st.mem j0Addr (J'.n :: (stripLoops J').m :: stripEdgeWords J' J'.m)
        rw [listAt_cons, listAt_cons]
        exact ⟨hmem_n, by rw [← hm0_eq]; exact hmem_m, hEW⟩
      · rwa [← hnl_eq]
  have hall := Triple.seq_normal_const ht1
    (Triple.seq_normal_const ht2
      (Triple.seq_normal_const ht3
        (Triple.seq_normal_const hfor
          (Triple.seq_normal_const ht4 ht5))))
  refine (hall.strengthen_post fun o st h => by
    cases o with
    | normal => simp at h
    | returned v => exact h).mono_cost ?_
  intro _ _
  simp only [stripLoopsContract, hg_load1, List.getD_cons_zero, Expr.size]
  omega


end MinCostFlow.Spanner
