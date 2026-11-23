module

public import MinCostFlow.SparseCore.Program.OutStepRun
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import MinCostFlow.LowStretch.ProgAmort

/-!
# Two small procedures of the output step

The output step writes the record of a split of its output batch from a list of end keys: the
tail edges of one side, then its head edges (`UpdateAt`, tags `2` and `3`). The keys come either
from a split list of the helper or from the incidence list of a vertex of the stored output
graph. Two small procedures do this work.

* **`outFilterBody`** `[src, n, par, dst, pb]` reads the `n` keys at `src` and writes, from
  `dst` on, the edge `k / 2` of each key `k` whose parity is `par` and whose presence word
  `mem (pb + k / 2)` is `1` (`keyFilterMem`). It returns the number of edges written. With the
  presence array of the stored graph at `pb`, it drops the ends of edges that left the graph.
* **`outWalkBody`** `[nb, head, dst]` walks a doubly linked list of the graph layout from the
  word at `head`, along the next words at `nb`, and copies its elements to `dst` on. It returns
  their number. The incidence list of a vertex holds the keys of its ends.

Each costs a constant per element (`outFilter_runs`, `outWalk_runs`) and writes only its output
cells.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program MinCostFlow.LowStretch

/-! ## The filter -/

/-- The edges `k / 2` of the keys `k` of `K` with parity `par` whose presence word at
`pb + k / 2` is `1`, in the order of `K`. -/
def keyFilterMem (mem : ℕ → ℕ) (pb : ℕ) (K : List ℕ) (par : ℕ) : List ℕ :=
  (K.filter fun k => decide (k % 2 = par ∧ mem (pb + k / 2) = 1)).map (· / 2)

theorem keyFilterMem_length_le (mem : ℕ → ℕ) (pb : ℕ) (K : List ℕ) (par : ℕ) :
    (keyFilterMem mem pb K par).length ≤ K.length := by
  unfold keyFilterMem
  rw [List.length_map]
  exact List.length_filter_le _ _

theorem keyFilterMem_take_succ (mem : ℕ → ℕ) (pb : ℕ) (K : List ℕ) (par : ℕ) {i : ℕ}
    (hi : i < K.length) :
    keyFilterMem mem pb (K.take (i + 1)) par =
      keyFilterMem mem pb (K.take i) par ++
        if K[i] % 2 = par ∧ mem (pb + K[i] / 2) = 1 then [K[i] / 2] else [] := by
  unfold keyFilterMem
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.filter_append,
    List.map_append]
  congr 1
  by_cases hc : K[i] % 2 = par ∧ mem (pb + K[i] / 2) = 1
  · simp [hc]
  · simp [hc]

/-- One round of the filter: the key at place `i` (register `5`) goes to register `7`; when it
passes the two tests, its edge is written at `dst + cnt` (register `6`). -/
def ofIter : Stmt :=
  .seq (.assign 7 (.load (.bin .add (.reg 0) (.reg 5))))
    (.seq (.cond (.bin .eq (.bin .mod (.reg 7) (.const 2)) (.reg 2))
            (.cond (.bin .eq (.load (.bin .add (.reg 4) (.bin .div (.reg 7) (.const 2))))
                (.const 1))
              (.seq (.store (.bin .add (.reg 3) (.reg 6)) (.bin .div (.reg 7) (.const 2)))
                (.assign 6 (.bin .add (.reg 6) (.const 1))))
              .nop)
            .nop)
      (.assign 5 (.bin .add (.reg 5) (.const 1))))

/-- **The filter** `[src, n, par, dst, pb]`. -/
def outFilterBody : Stmt :=
  .seq (.assign 5 (.const 0))
    (.seq (.assign 6 (.const 0))
      (.seq (.loop (.bin .lt (.reg 5) (.reg 1)) ofIter) (.ret (.reg 6))))

section Filter

variable {w : ℕ} {p : Program} {ω : ℕ → Bool}

/-- The state of the filter after `i` rounds. -/
def OFInv (src n par dst pb : ℕ) (K : List ℕ) (mem₀ : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = par ∧ st.regs 3 = dst ∧ st.regs 4 = pb ∧
    st.regs 5 = i ∧ i ≤ n ∧ st.regs 6 = (keyFilterMem mem₀ pb (K.take i) par).length ∧
    ListAt st.mem dst (keyFilterMem mem₀ pb (K.take i) par) ∧
    ∀ a, ¬ (dst ≤ a ∧ a < dst + (keyFilterMem mem₀ pb (K.take i) par).length) →
      st.mem a = mem₀ a

private theorem ofIter_runs {src n par dst pb : ℕ} {K : List ℕ} {mem₀ : ℕ → ℕ} {i : ℕ}
    {st : State} (hK : ListAt mem₀ src K) (hn : K.length = n)
    (hw : ∀ k ∈ K, pb + k < 2 ^ w) (hsrc : src + n < 2 ^ w) (hdst : dst + n < 2 ^ w)
    (h2w : 2 < 2 ^ w)
    (hdsrc : ∀ i < n, ∀ j < n, src + i ≠ dst + j)
    (hdpb : ∀ k ∈ K, ∀ j < n, pb + k / 2 ≠ dst + j)
    (hI : OFInv src n par dst pb K mem₀ i st) (hi : i < n) :
    ∃ st' c, Runs w p ω ofIter st .normal st' c ∧ OFInv src n par dst pb K mem₀ (i + 1) st' ∧
      c ≤ 50 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, -, h6, hL, hag⟩ := hI
  have hiK : i < K.length := by omega
  have hlen := keyFilterMem_length_le mem₀ pb (K.take i) par
  rw [List.length_take] at hlen
  set cnt := (keyFilterMem mem₀ pb (K.take i) par).length with hcnt
  have hk : st.mem (src + i) = K[i] := by
    rw [hag (src + i) (fun ⟨h₁, h₂⟩ => hdsrc i hi (src + i - dst) (by omega) (by omega))]
    exact hK i hiK
  have hkw : pb + K[i] < 2 ^ w := hw _ (List.getElem_mem hiK)
  -- the load of the key
  obtain ⟨st₁, hr₁, hm₁, h7₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 7)
    (e := .load (.bin .add (.reg 0) (.reg 5))) (st := st) (v := K[i])
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h0) (Expr.eval_reg_of_eq h5)
      (by omega)) hk)
  have r0 : st₁.regs 0 = src := by rw [ho₁ 0 (by omega)]; exact h0
  have r2 : st₁.regs 2 = par := by rw [ho₁ 2 (by omega)]; exact h2
  have r3 : st₁.regs 3 = dst := by rw [ho₁ 3 (by omega)]; exact h3
  have r4 : st₁.regs 4 = pb := by rw [ho₁ 4 (by omega)]; exact h4
  have r5 : st₁.regs 5 = i := by rw [ho₁ 5 (by omega)]; exact h5
  have r6 : st₁.regs 6 = cnt := by rw [ho₁ 6 (by omega)]; exact h6
  have hkey : keyFilterMem mem₀ pb (K.take (i + 1)) par = keyFilterMem mem₀ pb (K.take i) par ++
      if K[i] % 2 = par ∧ mem₀ (pb + K[i] / 2) = 1 then [K[i] / 2] else [] :=
    keyFilterMem_take_succ mem₀ pb K par hiK
  have hpres : st₁.mem (pb + K[i] / 2) = mem₀ (pb + K[i] / 2) := by
    rw [hm₁]
    exact hag _ (fun ⟨h₁, h₂⟩ => hdpb K[i] (List.getElem_mem hiK) (pb + K[i] / 2 - dst)
      (by omega) (by omega))
  have hmod : (Expr.bin .eq (.bin .mod (.reg 7) (.const 2)) (.reg 2)).eval w st₁ =
      some (if K[i] % 2 = par then 1 else 0) :=
    Expr.eval_eq_op (Expr.eval_mod (Expr.eval_reg_of_eq h7₁) (Expr.eval_const (by omega))
      (by omega)) (Expr.eval_reg_of_eq r2) (by omega)
  have hdiv : (Expr.bin .div (.reg 7) (.const 2)).eval w st₁ = some (K[i] / 2) :=
    Expr.eval_div (Expr.eval_reg_of_eq h7₁) (Expr.eval_const (by omega)) (by omega)
  have hprE : (Expr.bin .eq (.load (.bin .add (.reg 4) (.bin .div (.reg 7) (.const 2))))
      (.const 1)).eval w st₁ = some (if mem₀ (pb + K[i] / 2) = 1 then 1 else 0) :=
    Expr.eval_eq_op (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r4) hdiv
      (by omega)) hpres) (Expr.eval_const (by omega)) (by omega)
  -- the two tests, and the write
  obtain ⟨st₂, c₂, hr₂, hm₂, h5₂, h6₂, hL₂, hag₂, hc₂⟩ : ∃ st₂ c₂,
      Runs w p ω (.cond (.bin .eq (.bin .mod (.reg 7) (.const 2)) (.reg 2))
            (.cond (.bin .eq (.load (.bin .add (.reg 4) (.bin .div (.reg 7) (.const 2))))
                (.const 1))
              (.seq (.store (.bin .add (.reg 3) (.reg 6)) (.bin .div (.reg 7) (.const 2)))
                (.assign 6 (.bin .add (.reg 6) (.const 1))))
              .nop)
            .nop) st₁ .normal st₂ c₂ ∧
      (∀ j, j ≠ 6 → st₂.regs j = st₁.regs j) ∧ st₂.regs 5 = i ∧
      st₂.regs 6 = (keyFilterMem mem₀ pb (K.take (i + 1)) par).length ∧
      ListAt st₂.mem dst (keyFilterMem mem₀ pb (K.take (i + 1)) par) ∧
      (∀ a, ¬ (dst ≤ a ∧ a < dst + (keyFilterMem mem₀ pb (K.take (i + 1)) par).length) →
        st₂.mem a = mem₀ a) ∧ c₂ ≤ 35 := by
    by_cases hc : K[i] % 2 = par ∧ mem₀ (pb + K[i] / 2) = 1
    · rw [ite_eq_left hc] at hkey
      have hmod' := hmod; rw [ite_eq_left hc.1] at hmod'
      have hprE' := hprE; rw [ite_eq_left hc.2] at hprE'
      obtain ⟨st₃, hr₃, hm₃, hrg₃⟩ := step_store (w := w) (p := p) (ω := ω)
        (a := .bin .add (.reg 3) (.reg 6)) (e := .bin .div (.reg 7) (.const 2)) (st := st₁)
        (Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_reg_of_eq r6) (by omega)) hdiv
      obtain ⟨st₄, hr₄, hm₄, h6₄, ho₄⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 6)
        (e := .bin .add (.reg 6) (.const 1)) (st := st₃) (v := cnt + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hrg₃]; exact r6)) (Expr.eval_const (by omega))
          (by omega))
      refine ⟨st₄, _, step_cond_true hmod' one_ne_zero
        (step_cond_true hprE' one_ne_zero (runs_seq_normal hr₃ hr₄)), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj; rw [ho₄ j hj, hrg₃]
      · rw [ho₄ 5 (by omega), hrg₃, r5]
      · rw [h6₄, hkey, List.length_append]; simp [hcnt]
      · rw [hkey, hm₄, hm₃]
        intro j hj
        rw [List.length_append, List.length_singleton] at hj
        by_cases hjc : j < cnt
        · rw [Function.update_of_ne (by omega), hm₁, hL j hjc, List.getElem_append_left]
        · have hj' : j = cnt := by omega
          subst hj'
          rw [Function.update_self, List.getElem_append_right (by omega)]
          simp
      · intro a ha
        rw [hm₄, hm₃, Function.update_of_ne (fun h => ha ⟨by omega, by
          rw [hkey, List.length_append, List.length_singleton]; omega⟩), hm₁]
        exact hag a (fun ⟨h₁, h₂⟩ => ha ⟨h₁, by
          rw [hkey, List.length_append, List.length_singleton]; omega⟩)
      · simp only [Expr.size_bin, Expr.size_reg, Expr.size_load, Expr.size_const]; omega
    · rw [ite_eq_right hc, List.append_nil] at hkey
      rw [hkey]
      by_cases hc1 : K[i] % 2 = par
      · have hc2 : ¬ mem₀ (pb + K[i] / 2) = 1 := fun h => hc ⟨hc1, h⟩
        have hmod' := hmod; rw [ite_eq_left hc1] at hmod'
        have hprE' := hprE; rw [ite_eq_right hc2] at hprE'
        refine ⟨st₁, _, step_cond_true hmod' one_ne_zero (step_cond_false hprE' step_nop),
          fun j _ => rfl, r5, r6, by rw [hm₁]; exact hL, fun a ha => by rw [hm₁]; exact hag a ha,
          ?_⟩
        simp only [Expr.size_bin, Expr.size_reg, Expr.size_load, Expr.size_const]; omega
      · have hmod' := hmod; rw [ite_eq_right hc1] at hmod'
        refine ⟨st₁, _, step_cond_false hmod' step_nop, fun j _ => rfl, r5, r6,
          by rw [hm₁]; exact hL, fun a ha => by rw [hm₁]; exact hag a ha, ?_⟩
        simp only [Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
  -- the next place
  obtain ⟨st₅, hr₅, hm₅, h5₅, ho₅⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 5)
    (e := .bin .add (.reg 5) (.const 1)) (st := st₂) (v := i + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq h5₂) (Expr.eval_const (by omega)) (by omega))
  refine ⟨st₅, _, runs_seq_normal hr₁ (runs_seq_normal hr₂ hr₅), ⟨?_, ?_, ?_, ?_, ?_, h5₅,
    by omega, ?_, by rw [hm₅]; exact hL₂, fun a ha => by rw [hm₅]; exact hag₂ a ha⟩, ?_⟩
  · rw [ho₅ 0 (by omega), hm₂ 0 (by omega), r0]
  · rw [ho₅ 1 (by omega), hm₂ 1 (by omega), ho₁ 1 (by omega), h1]
  · rw [ho₅ 2 (by omega), hm₂ 2 (by omega), r2]
  · rw [ho₅ 3 (by omega), hm₂ 3 (by omega), r3]
  · rw [ho₅ 4 (by omega), hm₂ 4 (by omega), r4]
  · rw [ho₅ 6 (by omega), h6₂]
  · simp only [Expr.size_bin, Expr.size_reg, Expr.size_load, Expr.size_const]; omega

/-- **The filter.** From the keys `K` at `src`, it writes `keyFilterMem mem pb K par` at `dst`
and returns its length, at a cost of at most `60 (n + 1)`. It writes only the cells of its
output. The output cells must not hold a key or a presence word that it reads. -/
theorem outFilter_runs
    {src n par dst pb : ℕ} {K : List ℕ} (mem : ℕ → ℕ) (pos : ℕ)
    (hK : ListAt mem src K) (hn : K.length = n)
    (hw : ∀ k ∈ K, pb + k < 2 ^ w) (hsrc : src + n < 2 ^ w) (hdst : dst + n < 2 ^ w)
    (h2w : 2 < 2 ^ w)
    (hdsrc : ∀ i < n, ∀ j < n, src + i ≠ dst + j)
    (hdpb : ∀ k ∈ K, ∀ j < n, pb + k / 2 ≠ dst + j) :
    ∃ st' c, Runs w p ω outFilterBody (startState [src, n, par, dst, pb] mem pos)
        (.returned (keyFilterMem mem pb K par).length) st' c ∧
      ListAt st'.mem dst (keyFilterMem mem pb K par) ∧
      (∀ a, ¬ (dst ≤ a ∧ a < dst + (keyFilterMem mem pb K par).length) → st'.mem a = mem a) ∧
      c ≤ 60 * (n + 1) := by
  set st₀ := startState [src, n, par, dst, pb] mem pos with hst₀
  obtain ⟨st₁, hr₁, hm₁, h5₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 5) (e := .const 0)
    (st := st₀) (Expr.eval_const (by omega))
  obtain ⟨st₂, hr₂, hm₂, h6₂, ho₂⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 6) (e := .const 0)
    (st := st₁) (Expr.eval_const (by omega))
  have hI : OFInv src n par dst pb K mem 0 st₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, by rw [ho₂ 5 (by omega), h5₁], Nat.zero_le _, by simp [h6₂,
      keyFilterMem], by simp [keyFilterMem, ListAt], fun a _ => by rw [hm₂, hm₁]; rfl⟩ <;>
    · rw [ho₂ _ (by omega), ho₁ _ (by omega)]; rfl
  have hloop := runs_loop_amort (w := w) (p := p) (ω := ω) (e := .bin .lt (.reg 5) (.reg 1))
    (body := ofIter) (Inv := fun i st => OFInv src n par dst pb K mem i st)
    (Fin := fun o st r => o = .normal ∧ OFInv src n par dst pb K mem n st ∧ r = 0)
    (fun i => n - i) (fun i => 60 * (n - i) + 4)
    (condVal := fun st => if st.regs 5 < st.regs 1 then 1 else 0)
    (fun i st _ => Expr.eval_lt_op (Expr.eval_reg w 5 st) (Expr.eval_reg w 1 st) (by omega)) ?_ ?_ 0
    st₂ hI
  · obtain ⟨o, st₃, c₃, hr₃, r, ⟨rfl, hI₃, rfl⟩, hc₃⟩ := hloop
    obtain ⟨-, -, -, -, -, -, -, h6₃, hL₃, hag₃⟩ := hI₃
    have hK' : K.take n = K := by rw [← hn, List.take_length]
    rw [hK'] at h6₃ hL₃ hag₃
    refine ⟨st₃, _, runs_seq_normal hr₁ (runs_seq_normal hr₂ (runs_seq_normal hr₃
      (step_ret (Expr.eval_reg_of_eq h6₃)))), hL₃, hag₃, ?_⟩
    simp only [Expr.size_reg, Expr.size_const] at hc₃ ⊢
    omega
  · intro i st hIi hc
    have hin' : i = n := by
      obtain ⟨-, h1, -, -, -, h5, hin, -⟩ := hIi
      rw [h1, h5] at hc
      by_contra hne
      simp only [show i < n by omega, ite_true] at hc
      exact one_ne_zero hc
    exact ⟨0, ⟨rfl, hin' ▸ hIi, rfl⟩, by simp only [Expr.size_bin, Expr.size_reg]; omega⟩
  · intro i st hIi hc
    have hin : i < n := by
      obtain ⟨-, h1, -, -, -, h5, -⟩ := hIi
      rw [h1, h5] at hc
      by_contra hn'
      simp [hn'] at hc
    obtain ⟨st', c, hr, hI', hc'⟩ := ofIter_runs hK hn hw hsrc hdst h2w hdsrc hdpb hIi hin
    refine ⟨.normal, st', c, hr, i + 1, hI', by omega, ?_⟩
    simp only [Expr.size_bin, Expr.size_reg]
    have : n - i = (n - (i + 1)) + 1 := by omega
    rw [this]
    omega

end Filter

/-! ## The walk -/

/-- One round of the walk: write the element `ptr - 1` at `dst + cnt`, and follow its next word. -/
def owIter : Stmt :=
  .seq (.store (.bin .add (.reg 2) (.reg 4)) (.bin .sub (.reg 3) (.const 1)))
    (.seq (.assign 4 (.bin .add (.reg 4) (.const 1)))
      (.assign 3 (.load (.bin .add (.reg 0) (.bin .sub (.reg 3) (.const 1))))))

/-- **The walk** `[nb, head, dst]`. -/
def outWalkBody : Stmt :=
  .seq (.assign 3 (.load (.reg 1)))
    (.seq (.assign 4 (.const 0))
      (.seq (.loop (.reg 3) owIter) (.ret (.reg 4))))

section Walk

variable {w : ℕ} {p : Program} {ω : ℕ → Bool}

/-- The pointer word of place `i` of a list: the element plus one, or `0` past the end. -/
def ptrWord (L : List ℕ) (i : ℕ) : ℕ := if h : i < L.length then L[i] + 1 else 0

/-- The state of the walk after `i` rounds. -/
def OWInv (nb dst : ℕ) (L : List ℕ) (mem₀ : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = nb ∧ st.regs 2 = dst ∧ st.regs 4 = i ∧ i ≤ L.length ∧
    st.regs 3 = ptrWord L i ∧ ListAt st.mem dst (L.take i) ∧
    ∀ a, ¬ (dst ≤ a ∧ a < dst + i) → st.mem a = mem₀ a

private theorem owIter_runs {prevB nb head dst cap : ℕ} {L : List ℕ} {mem₀ : ℕ → ℕ} {i : ℕ}
    {st : State} (hL : IsDoublyLinkedList mem₀ prevB nb head cap L)
    (hw : ∀ x ∈ L, nb + x + 1 < 2 ^ w) (hdst : dst + L.length < 2 ^ w) (h2w : 2 < 2 ^ w)
    (hdnb : ∀ x ∈ L, ∀ j < L.length, nb + x ≠ dst + j)
    (hI : OWInv nb dst L mem₀ i st) (hi : i < L.length) :
    ∃ st' c, Runs w p ω owIter st .normal st' c ∧ OWInv nb dst L mem₀ (i + 1) st' ∧ c ≤ 25 := by
  obtain ⟨h0, h2, h4, -, h3, hT, hag⟩ := hI
  have hx : L[i] ∈ L := List.getElem_mem hi
  have hxw := hw _ hx
  have h3' : st.regs 3 = L[i] + 1 := by rw [h3, ptrWord, dite_eq_left hi]
  have hsub : (Expr.bin .sub (.reg 3) (.const 1)).eval w st = some L[i] := by
    have := Expr.eval_sub (w := w) (st := st) (a := .reg 3) (b := .const 1)
      (Expr.eval_reg_of_eq h3') (Expr.eval_const (by omega)) (by omega)
    simpa using this
  obtain ⟨st₁, hr₁, hm₁, hrg₁⟩ := step_store (w := w) (p := p) (ω := ω)
    (a := .bin .add (.reg 2) (.reg 4)) (e := .bin .sub (.reg 3) (.const 1)) (st := st)
    (Expr.eval_add (Expr.eval_reg_of_eq h2) (Expr.eval_reg_of_eq h4) (by omega)) hsub
  obtain ⟨st₂, hr₂, hm₂, h4₂, ho₂⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 4)
    (e := .bin .add (.reg 4) (.const 1)) (st := st₁) (v := i + 1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hrg₁]; exact h4)) (Expr.eval_const (by omega))
      (by omega))
  have hnext : st₂.mem (nb + L[i]) = ptrWord L (i + 1) := by
    rw [hm₂, hm₁, Function.update_of_ne (hdnb L[i] hx i hi),
      hag _ (fun ⟨h₁, h₂⟩ => hdnb L[i] hx (nb + L[i] - dst) (by omega) (by omega)),
      (hL.2.2.2 i hi).2]
    unfold ptrWord
    by_cases hc : i + 1 = L.length
    · rw [ite_eq_left hc, dite_eq_right (by omega)]
    · rw [ite_eq_right hc, dite_eq_left (by omega), List.getD_eq_getElem]
  have r3₂ : st₂.regs 3 = L[i] + 1 := by rw [ho₂ 3 (by omega), hrg₁]; exact h3'
  have r0₂ : st₂.regs 0 = nb := by rw [ho₂ 0 (by omega), hrg₁]; exact h0
  have hsub₂ : (Expr.bin .sub (.reg 3) (.const 1)).eval w st₂ = some L[i] := by
    have := Expr.eval_sub (w := w) (st := st₂) (a := .reg 3) (b := .const 1)
      (Expr.eval_reg_of_eq r3₂) (Expr.eval_const (by omega)) (by omega)
    simpa using this
  obtain ⟨st₃, hr₃, hm₃, h3₃, ho₃⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 3)
    (e := .load (.bin .add (.reg 0) (.bin .sub (.reg 3) (.const 1)))) (st := st₂)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0₂) hsub₂ (by omega)) hnext)
  refine ⟨st₃, _, runs_seq_normal hr₁ (runs_seq_normal hr₂ hr₃), ⟨?_, ?_, ?_, by omega, h3₃, ?_,
    ?_⟩, ?_⟩
  · rw [ho₃ 0 (by omega), ho₂ 0 (by omega), hrg₁, h0]
  · rw [ho₃ 2 (by omega), ho₂ 2 (by omega), hrg₁, h2]
  · rw [ho₃ 4 (by omega), h4₂]
  · rw [hm₃, hm₂, hm₁]
    intro j hj
    rw [List.length_take] at hj
    by_cases hjc : j < i
    · rw [Function.update_of_ne (by omega), hT j (by rw [List.length_take]; omega),
        List.getElem_take, List.getElem_take]
    · have hj' : j = i := by omega
      subst hj'
      rw [Function.update_self, List.getElem_take]
  · intro a ha
    rw [hm₃, hm₂, hm₁, Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]
    exact hag a (fun ⟨h₁, h₂⟩ => ha ⟨h₁, by omega⟩)
  · simp only [Expr.size_bin, Expr.size_reg, Expr.size_load, Expr.size_const]; omega

/-- **The walk.** From a doubly linked list `L` with its first word at `head` and its next words
at `nb`, it writes `L` at `dst` and returns its length, at a cost of at most `30 (|L| + 1)`. It
writes only the cells of its output, which must not hold the first word or a next word. -/
theorem outWalk_runs
    {prevB nb head dst cap : ℕ} {L : List ℕ} (mem : ℕ → ℕ) (pos : ℕ)
    (hL : IsDoublyLinkedList mem prevB nb head cap L)
    (hw : ∀ x ∈ L, nb + x + 1 < 2 ^ w) (hdst : dst + L.length < 2 ^ w) (h2w : 2 < 2 ^ w)
    (hdhead : ∀ j < L.length, head ≠ dst + j)
    (hdnb : ∀ x ∈ L, ∀ j < L.length, nb + x ≠ dst + j) :
    ∃ st' c, Runs w p ω outWalkBody (startState [nb, head, dst] mem pos)
        (.returned L.length) st' c ∧ ListAt st'.mem dst L ∧
      (∀ a, ¬ (dst ≤ a ∧ a < dst + L.length) → st'.mem a = mem a) ∧ c ≤ 30 * (L.length + 1) := by
  set st₀ := startState [nb, head, dst] mem pos with hst₀
  have hhead : mem head = ptrWord L 0 := by
    rw [hL.2.2.1]
    cases L with
    | nil => rfl
    | cons x L => simp [ptrWord]
  obtain ⟨st₁, hr₁, hm₁, h3₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 3)
    (e := .load (.reg 1)) (st := st₀) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq rfl) hhead)
  obtain ⟨st₂, hr₂, hm₂, h4₂, ho₂⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 4) (e := .const 0)
    (st := st₁) (Expr.eval_const (by omega))
  have hI : OWInv nb dst L mem 0 st₂ := by
    refine ⟨?_, ?_, h4₂, Nat.zero_le _, by rw [ho₂ 3 (by omega), h3₁], by simp [ListAt],
      fun a _ => by rw [hm₂, hm₁]; rfl⟩
    · rw [ho₂ 0 (by omega), ho₁ 0 (by omega)]; rfl
    · rw [ho₂ 2 (by omega), ho₁ 2 (by omega)]; rfl
  have hloop := runs_loop_amort (w := w) (p := p) (ω := ω) (e := .reg 3)
    (body := owIter) (Inv := fun i st => OWInv nb dst L mem i st)
    (Fin := fun o st r => o = .normal ∧ OWInv nb dst L mem L.length st ∧ r = 0)
    (fun i => L.length - i) (fun i => 30 * (L.length - i) + 2)
    (condVal := fun st => st.regs 3)
    (fun i st _ => Expr.eval_reg w 3 st) ?_ ?_ 0 st₂ hI
  · obtain ⟨o, st₃, c₃, hr₃, r, ⟨rfl, hI₃, rfl⟩, hc₃⟩ := hloop
    obtain ⟨-, -, h4₃, -, -, hT₃, hag₃⟩ := hI₃
    rw [List.take_length] at hT₃
    refine ⟨st₃, _, runs_seq_normal hr₁ (runs_seq_normal hr₂ (runs_seq_normal hr₃
      (step_ret (Expr.eval_reg_of_eq h4₃)))), hT₃, hag₃, ?_⟩
    simp only [Expr.size_reg, Expr.size_load, Expr.size_const] at hc₃ ⊢
    omega
  · intro i st hIi hc
    have hin' : i = L.length := by
      obtain ⟨-, -, -, hin, h3, -⟩ := hIi
      by_contra hne
      have : st.regs 3 = L[i]'(by omega) + 1 := by rw [h3, ptrWord, dite_eq_left (by omega)]
      have hc' : st.regs 3 = 0 := hc
      omega
    exact ⟨0, ⟨rfl, hin' ▸ hIi, rfl⟩, by simp only [Expr.size_reg]; omega⟩
  · intro i st hIi hc
    have hin : i < L.length := by
      obtain ⟨-, -, -, hin, h3, -⟩ := hIi
      by_contra hn'
      have : st.regs 3 = 0 := by rw [h3, ptrWord, dite_eq_right hn']
      exact hc this
    obtain ⟨st', c, hr, hI', hc'⟩ := owIter_runs hL hw hdst h2w hdnb hIi hin
    refine ⟨.normal, st', c, hr, i + 1, hI', by omega, ?_⟩
    simp only [Expr.size_reg]
    have : L.length - i = (L.length - (i + 1)) + 1 := by omega
    rw [this]
    omega

end Walk

end MinCostFlow.SparseCore.Program
