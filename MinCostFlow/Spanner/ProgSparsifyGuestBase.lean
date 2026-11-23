module

public import MinCostFlow.Spanner.ProgSparsifyModule
public import MinCostFlow.Spanner.ProgSparsifyCost
public import MinCostFlow.Spanner.ProgSparsifyCapProps
public import MinCostFlow.Spanner.ProgSparsifySpace
public import MinCostFlow.DynSpanner.Program.SparsifyContract

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Guest `[0, heap]` Wrapper Base for Word-RAM `Sparsify`

Defines the deterministic guest entry procedure `sparsifyGuestBody` (following the `[0, heap]`
convention with `[pH, pJ, pEmb]` at addresses `0, 1, 2` and a `J.m = 0` fast path), the single
fixed program `sparsifyGuestProgram impl`, the uniform `mMax`-cap Theorem 8.1 parameters, and
the execution / cost lemmas for the zero-edge and positive-edge branches.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited MinCostFlow.DynSpanner.Program

/-! ### Guest entry body and single fixed program -/

/-- Guest entry procedure of `Sparsify` at `args = [0, heap]`, reading `[pH, pJ, pEmb]` from
addresses `0, 1, 2`. If `J.m = 0`, writes the empty sparsifier directly at `[heap .. heap + 6)`;
otherwise calls `fSparsify [pH, pJ, pEmb, heap]` and returns its new heap end. Contains no
input-dependent constants (`mMax`, `m`, `k`, `φ`). -/
def sparsifyGuestBody (fSparsify : ℕ) : Stmt :=
  .assign 2 (.load (.const 0)) ;;
  .assign 3 (.load (.const 1)) ;;
  .assign 4 (.load (.const 2)) ;;
  .assign 5 (.load (.reg 3)) ;;
  .assign 6 (.load (.bin .add (.reg 3) (.const 1))) ;;
  .cond (.bin .eq (.reg 6) (.const 0))
    (.store (.reg 1) (.bin .add (.reg 1) (.const 3)) ;;
     .store (.bin .add (.reg 1) (.const 1)) (.bin .add (.reg 1) (.const 5)) ;;
     .store (.bin .add (.reg 1) (.const 2)) (.bin .add (.reg 1) (.const 6)) ;;
     .store (.bin .add (.reg 1) (.const 3)) (.reg 5) ;;
     .store (.bin .add (.reg 1) (.const 4)) (.const 0) ;;
     .store (.bin .add (.reg 1) (.const 5)) (.const 0) ;;
     .ret (.bin .add (.reg 1) (.const 6)))
    (.call 7 fSparsify [.reg 2, .reg 3, .reg 4, .reg 1] ;;
     .ret (.reg 7))

theorem sparsifyGuestBody_noRand (fSparsify : ℕ) : (sparsifyGuestBody fSparsify).NoRand := by
  simp [sparsifyGuestBody, Stmt.NoRand]

/-- Single fixed guest procedure list for `Sparsify` (entry at procedure `0`, delegating to
`sparsifyModule impl 1` at procedure `1`). Independent of `mMax`, `m`, `k`, and `φ`. -/
def sparsifyGuestModule (impl : SpannerToolImpl) : List Stmt :=
  [sparsifyGuestBody 1] ++ sparsifyModule impl 1

/-- Standalone deterministic guest `Program` for `Sparsify`. -/
def sparsifyGuestProgram (impl : SpannerToolImpl) : Program :=
  { procs := sparsifyGuestModule impl }

theorem sparsifyGuestModule_nonempty (impl : SpannerToolImpl) :
    0 < (sparsifyGuestModule impl).length := by
  simp [sparsifyGuestModule]

theorem sparsifyGuestProgram_isDeterministic (impl : SpannerToolImpl)
    (hdec : ∀ s ∈ impl.decompose.procs (sparsifyDecBase 1), s.NoRand)
    (hce : ∀ s ∈ impl.constructExpander.procs (sparsifyCeBase impl 1), s.NoRand)
    (hds : ∀ s ∈ impl.pathDS.procs (sparsifyDsBase impl 1), s.NoRand) :
    (sparsifyGuestProgram impl).IsDeterministic := by
  intro s hs
  simp only [sparsifyGuestProgram, sparsifyGuestModule, List.mem_append, List.mem_singleton] at hs
  rcases hs with rfl | hs
  · exact sparsifyGuestBody_noRand 1
  · exact sparsifyModule_noRand impl 1 hdec hce hds s hs

/-! ### Uniform `mMax`-cap Theorem 8.1 parameters -/

/-- Congestion overhead `γ_c(mMax)` of `sparsifyGuestProgram impl`. -/
noncomputable def sparsifyGuestGammaC (impl : SpannerToolImpl) (mMax : ℕ) : ℝ :=
  capGammaC (2 * (impl.constructExpander.c_deg_int : ℝ)) impl.constructExpander.φ_Const
    (spannerTools_of_impl impl).pathDS (impl.decompose.φ_lb mMax) mMax

/-- Length overhead `γ_ℓ(mMax)` of `sparsifyGuestProgram impl`. -/
noncomputable def sparsifyGuestGammaL (impl : SpannerToolImpl) (mMax : ℕ) : ℝ :=
  capGammaL (2 * (impl.constructExpander.c_deg_int : ℝ)) impl.constructExpander.φ_Const
    (spannerTools_of_impl impl).pathDS (impl.decompose.φ_lb mMax) mMax

/-- Sparsity constant `K_s` of `sparsifyGuestProgram impl`. -/
noncomputable def sparsifyGuestKs (impl : SpannerToolImpl) : ℝ :=
  1 + impl.decompose.c_ℓ * (2 * (impl.constructExpander.c_deg_int : ℝ)) / Real.log 2

/-- Time-overhead factor `γ_t(mMax)` absorbing both `capGammaQuery / capGammaExpPath` and
`impl.decompose.decFactor mMax / γ_ℓ(mMax)^2`. -/
noncomputable def sparsifyGuestGammaT (impl : SpannerToolImpl) (mMax : ℕ) : ℝ :=
  let tools := spannerTools_of_impl impl
  let ce := impl.constructExpander
  let φ_min := impl.decompose.φ_lb mMax
  let γ_ℓ := sparsifyGuestGammaL impl mMax
  max (max 1 (capGammaQuery (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min mMax /
      capGammaExpPath (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min mMax))
    (impl.decompose.decFactor mMax / γ_ℓ ^ 2)

/-- Leading runtime constant `K_t` of `sparsifyGuestProgram impl`. -/
noncomputable def sparsifyGuestKt (impl : SpannerToolImpl) : ℝ :=
  (2 * impl.decompose.K_dec + 1) + sparsifyProgConst impl + 80

theorem sparsifyGuestGammaL_ge_one (impl : SpannerToolImpl) (mMax : ℕ) :
    1 ≤ sparsifyGuestGammaL impl mMax := by
  have h4 := four_le_capGammaL (c_deg := 2 * (impl.constructExpander.c_deg_int : ℝ))
    (pds := (spannerTools_of_impl impl).pathDS)
    impl.constructExpander.hφ_Const_pos (impl.decompose.hφ_lb_pos mMax) mMax
  unfold sparsifyGuestGammaL; linarith

theorem sparsifyGuestGammaC_ge_one (impl : SpannerToolImpl) (mMax : ℕ) :
    1 ≤ sparsifyGuestGammaC impl mMax :=
  one_le_capGammaC (c_deg := 2 * (impl.constructExpander.c_deg_int : ℝ))
    (pds := (spannerTools_of_impl impl).pathDS)
    impl.constructExpander.hφ_Const_pos (impl.decompose.hφ_lb_pos mMax) mMax

theorem sparsifyGuestKs_nonneg (impl : SpannerToolImpl) :
    0 ≤ sparsifyGuestKs impl := by
  unfold sparsifyGuestKs
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcℓ : 0 ≤ impl.decompose.c_ℓ := le_trans (by norm_num) impl.decompose.hc_ℓ
  positivity

theorem sparsifyGuestGammaT_ge_one (impl : SpannerToolImpl) (mMax : ℕ) :
    1 ≤ sparsifyGuestGammaT impl mMax :=
  le_trans (le_max_left _ _) (le_max_left _ _)

theorem sparsifyGuestKt_nonneg (impl : SpannerToolImpl) :
    0 ≤ sparsifyGuestKt impl := by
  unfold sparsifyGuestKt
  have h1 := impl.decompose.hK_dec
  have h2 := sparsifyProgConst_pos impl
  linarith

/-! ### Memory & input-size helpers -/

lemma graph_encode_len_eq (G : Cited.Graph) : G.encode.length = 2 + 2 * G.m := by
  have hfm : ∀ es : List (ℕ × ℕ), (es.flatMap fun e => [e.1, e.2]).length = 2 * es.length := by
    intro es; induction es with
    | nil => rfl
    | cons _ _ ih => simp [ih]; omega
  simp [Cited.Graph.encode, Cited.Graph.m, hfm]; omega

private lemma mem_le_foldr_max : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0
  | [], _, hx => by simp at hx
  | a :: as, x, hx => by
    simp only [List.mem_cons, List.foldr_cons] at hx ⊢
    rcases hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (mem_le_foldr_max as x hx) (le_max_right _ _)

lemma le_citedMaxWord {mem : ℕ → ℕ} {heap a : ℕ} (ha : a < heap) :
    mem a ≤ citedMaxWord mem heap :=
  mem_le_foldr_max _ _ (List.mem_map.mpr ⟨a, List.mem_range.mpr ha, rfl⟩)

lemma mem_encode_le_citedMaxWord {mem : ℕ → ℕ} {p heap : ℕ} {G : Cited.Graph}
    (hG : GraphAt mem p G) (hle : p + G.encode.length ≤ heap) :
    ∀ x ∈ G.encode, x ≤ citedMaxWord mem heap := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  have hcell : mem (p + k) = G.encode[k]'hk := by
    simpa [List.getD_eq_getElem _ 0 hk] using hG k hk
  rw [← hcell]
  exact le_citedMaxWord (by omega)

lemma citedInputSize_le_quad {mem : ℕ → ℕ} {heap : ℕ}
    {H' J : Cited.Graph} {embJH : ℕ → Walk}
    (hHle : mem 0 + H'.encode.length ≤ heap)
    (hJle : mem 1 + J.encode.length ≤ heap)
    (hH : GraphAt mem (mem 0) H')
    (hJ : GraphAt mem (mem 1) J)
    (hEmb : EmbAt mem (mem 2) J.m embJH)
    (hBnd : EmbBounded mem (mem 2) J.m embJH heap) :
    citedInputSize mem ≤ 2 * (heap + citedMaxWord mem heap + 2) ^ 2 := by
  rw [citedInputSize_eq hH hJ hEmb]
  set mVal := citedMaxWord mem heap
  have hHenc : H'.encode.length = 2 + 2 * H'.m := graph_encode_len_eq H'
  have hJenc : J.encode.length = 2 + 2 * J.m := graph_encode_len_eq J
  have hHn : H'.n ≤ mVal := by
    have h0 : mem (mem 0) = H'.n := by simpa [GraphAt, Graph.encode] using hH 0 (by simp [Graph.encode])
    rw [← h0]; exact le_citedMaxWord (by omega)
  have hJn : J.n ≤ mVal := by
    have h0 : mem (mem 1) = J.n := by simpa [GraphAt, Graph.encode] using hJ 0 (by simp [Graph.encode])
    rw [← h0]; exact le_citedMaxWord (by omega)
  have hHm : H'.m ≤ heap := by omega
  have hJm : J.m ≤ heap := by omega
  have hsum : ∑ j ∈ Finset.range J.m, (embJH j).verts.length ≤ J.m * heap := by
    calc ∑ j ∈ Finset.range J.m, (embJH j).verts.length
        ≤ ∑ _j ∈ Finset.range J.m, heap := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hb := hBnd.2 j (Finset.mem_range.mp hj)
          have hl : (embJH j).encode.length = (embJH j).verts.length + (embJH j).edges.length + 2 := by
            simp [Walk.encode]; omega
          omega
      _ = J.m * heap := by simp
  have hsq : J.m * heap ≤ heap * heap := Nat.mul_le_mul_right heap hJm
  nlinarith only [hHn, hJn, hHm, hJm, hsum, hsq]

private lemma ev_eq_zero {w : ℕ} {st : State} (r : ℕ) {v : ℕ}
    (hr : st.regs r = v) (h1 : 1 < 2 ^ w) :
    (Expr.bin .eq (.reg r) (.const 0)).eval w st = some (if v = 0 then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  simp only [Expr.eval, BinOp.eval, hr, h0, ↓reduceIte]
  split_ifs <;> simp

/-! ### Execution of `sparsifyGuestBody` -/

lemma sparsifyGuestBody_runs_zero {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {fSparsify heap : ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {H' J : Cited.Graph} {embJH : ℕ → Walk}
    {mMax : ℕ} {γ_c γ_ℓ K_s : ℝ}
    (hγ_c_nn : 0 ≤ γ_c) (hγ_ℓ_ge : 1 ≤ γ_ℓ) (hK_s_nn : 0 ≤ K_s)
    (hw16 : 16 ≤ 2 ^ w) (hheap6_w : heap + 6 < 2 ^ w)
    (hJle : mem 1 + J.encode.length ≤ heap) (hJ : GraphAt mem (mem 1) J)
    (hJn_w : J.n < 2 ^ w) (hJm0 : J.m = 0)
    (hzf : ZeroFrom mem heap) :
    ∃ o st' c,
      Runs w p ω (sparsifyGuestBody fSparsify) (startState [0, heap] mem pos) o st' c ∧
      (o.value = heap + 6 ∧
       (∀ x < heap, st'.mem x = mem x) ∧
       ZeroFrom st'.mem (heap + 6) ∧
       ∃ (cJtilde : Cited.Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk),
         CitedSparsifyProp mMax γ_c γ_ℓ K_s 1 H' J embJH cJtilde kept embJJtilde ∧
         SparsifyOutRelocAt st'.mem 0 heap (heap + 6) J.m cJtilde kept embJJtilde) ∧
      c ≤ 80 := by
  have hJenc : J.encode.length = 2 := by rw [graph_encode_len_eq, hJm0]
  have hpJ_lt : mem 1 < heap := by omega
  have hpJ1_lt : mem 1 + 1 < heap := by omega
  have hmemJ0 : mem (mem 1) = J.n := by simpa [GraphAt, Graph.encode] using hJ 0 (by simp [Graph.encode])
  have hmemJ1 : mem (mem 1 + 1) = 0 := by
    simpa [GraphAt, Graph.encode, hJm0] using hJ 1 (by simp [Graph.encode])
  let s0 := startState [0, heap] mem pos
  have hr1 : s0.regs 1 = heap := by simp [s0, startState]
  have e2 : (Expr.load (.const 0)).eval w s0 = some (mem 0) :=
    ev_load' (ev_const (by omega)) rfl
  let rg2 := Function.update s0.regs 2 (mem 0)
  have e3 : (Expr.load (.const 1)).eval w ⟨mem, rg2, pos⟩ = some (mem 1) :=
    ev_load' (ev_const (by omega)) rfl
  let rg3 := Function.update rg2 3 (mem 1)
  have e4 : (Expr.load (.const 2)).eval w ⟨mem, rg3, pos⟩ = some (mem 2) :=
    ev_load' (ev_const (by omega)) rfl
  let rg4 := Function.update rg3 4 (mem 2)
  have e5 : (Expr.load (.reg 3)).eval w ⟨mem, rg4, pos⟩ = some J.n :=
    ev_load' (ev_reg (by simp [rg4, rg3]) (by omega)) hmemJ0
  let rg5 := Function.update rg4 5 J.n
  have e6 : (Expr.load (.bin .add (.reg 3) (.const 1))).eval w ⟨mem, rg5, pos⟩ = some 0 :=
    ev_load' (ev_add (ev_reg (by simp [rg5, rg4, rg3]) (by omega)) (ev_const (by omega)) (by omega)) hmemJ1
  let rg6 := Function.update rg5 6 0
  have hr1_6 : rg6 1 = heap := by simp [rg6, rg5, rg4, rg3, rg2, hr1]
  have hr5_6 : rg6 5 = J.n := by simp [rg6, rg5]
  have hr6_6 : rg6 6 = 0 := by simp [rg6]
  unfold sparsifyGuestBody
  refine runs_start_le ?_
  refine runs_seq_assign_le e2 ?_
  refine runs_seq_assign_le e3 ?_; dsimp only
  refine runs_seq_assign_le e4 ?_; dsimp only
  refine runs_seq_assign_le e5 ?_; dsimp only
  refine runs_seq_assign_le e6 ?_; dsimp only
  change ∃ o st' c, Runs w p ω _ ⟨mem, rg6, pos⟩ o st' c ∧ _ ∧ _ ≤ _
  have hcond : (Expr.bin .eq (.reg 6) (.const 0)).eval w ⟨mem, rg6, pos⟩ = some 1 := by
    simpa using ev_eq_zero (st := ⟨mem, rg6, pos⟩) 6 hr6_6 (by omega : 1 < 2 ^ w)
  suffices hthen : ∃ o st' c,
      Runs w p ω
        (.store (.reg 1) (.bin .add (.reg 1) (.const 3)) ;;
         .store (.bin .add (.reg 1) (.const 1)) (.bin .add (.reg 1) (.const 5)) ;;
         .store (.bin .add (.reg 1) (.const 2)) (.bin .add (.reg 1) (.const 6)) ;;
         .store (.bin .add (.reg 1) (.const 3)) (.reg 5) ;;
         .store (.bin .add (.reg 1) (.const 4)) (.const 0) ;;
         .store (.bin .add (.reg 1) (.const 5)) (.const 0) ;;
         .ret (.bin .add (.reg 1) (.const 6)))
        ⟨mem, rg6, pos⟩ o st' c ∧
      (o.value = heap + 6 ∧
       (∀ x < heap, st'.mem x = mem x) ∧
       ZeroFrom st'.mem (heap + 6) ∧
       ∃ (cJtilde : Cited.Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk),
         CitedSparsifyProp mMax γ_c γ_ℓ K_s 1 H' J embJH cJtilde kept embJJtilde ∧
         SparsifyOutRelocAt st'.mem 0 heap (heap + 6) J.m cJtilde kept embJJtilde) ∧
      26 + c ≤ 80 by
    rcases hthen with ⟨o, st', c, hr, hp, hc⟩
    refine ⟨o, st', (Expr.bin .eq (.reg 6) (.const 0)).size + c + 1,
      runs_cond_iff.mpr ⟨1, c, hcond, by simpa using hr, rfl⟩, hp, ?_⟩
    simp only [Expr.size]; omega
  refine runs_seq_store_le (ev_reg hr1_6 (by omega))
    (ev_add (ev_reg hr1_6 (by omega)) (ev_const (by omega)) (by omega)) ?_; dsimp only
  refine runs_seq_store_le (ev_add (ev_reg hr1_6 (by omega)) (ev_const (by omega)) (by omega))
    (ev_add (ev_reg hr1_6 (by omega)) (ev_const (by omega)) (by omega)) ?_; dsimp only
  refine runs_seq_store_le (ev_add (ev_reg hr1_6 (by omega)) (ev_const (by omega)) (by omega))
    (ev_add (ev_reg hr1_6 (by omega)) (ev_const (by omega)) (by omega)) ?_; dsimp only
  refine runs_seq_store_le (ev_add (ev_reg hr1_6 (by omega)) (ev_const (by omega)) (by omega))
    (ev_reg hr5_6 hJn_w) ?_; dsimp only
  refine runs_seq_store_le (ev_add (ev_reg hr1_6 (by omega)) (ev_const (by omega)) (by omega))
    (ev_const (by omega)) ?_; dsimp only
  refine runs_seq_store_le (ev_add (ev_reg hr1_6 (by omega)) (ev_const (by omega)) (by omega))
    (ev_const (by omega)) ?_; dsimp only
  refine runs_ret_le (ev_add (ev_reg hr1_6 (by omega)) (ev_const (by omega)) (by omega)) ?_ ?_
  · set memF := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update mem heap (heap + 3)) (heap + 1) (heap + 5))
      (heap + 2) (heap + 6)) (heap + 3) J.n) (heap + 4) 0) (heap + 5) 0
    have hagr : ∀ x < heap, memF x = mem x := fun x hx => by
      dsimp only [memF]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hzfF : ZeroFrom memF (heap + 6) := fun x hx => by
      dsimp only [memF]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hzf x (by omega)
    have hf0 : memF heap = heap + 3 := by
      dsimp only [memF]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
    have hf1 : memF (heap + 1) = heap + 5 := by
      dsimp only [memF]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_self]
    have hf2 : memF (heap + 2) = heap + 6 := by
      dsimp only [memF]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_self]
    have hf3 : memF (heap + 3) = J.n := by
      dsimp only [memF]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    have hf4 : memF (heap + 4) = 0 := by
      dsimp only [memF]; rw [Function.update_of_ne (by omega), Function.update_self]
    have hf5 : memF (heap + 5) = 0 := by dsimp only [memF]; rw [Function.update_self]
    refine ⟨rfl, hagr, hzfF, ⟨J.n, []⟩, [], fun _ => ⟨[], []⟩, ?_, ?_⟩
    · have hvc0 : Spanner.vcong J H' (fun _ => 1)
          (Spanner.compose ⟨J.n, []⟩ (Spanner.restrictEmb embJH []) (fun _ => ⟨[], []⟩)) = 0 := by
        apply le_antisymm
        · exact vcong_le_iff.mpr ⟨le_rfl, fun x _ => by unfold Spanner.vcongAt; simp [hJm0]⟩
        · exact vcong_nonneg _ _ _ _
      have hlen0 : Spanner.length J (fun _ => ⟨[], []⟩) = 0 := by
        unfold Spanner.length; simp [hJm0]
      have hL1 : 1 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := one_le_one_add_log J.n J.m
      refine ⟨List.nodup_nil, by simp, rfl, rfl, by simp [Cited.Graph.IsValid],
        ⟨le_rfl, fun e he => by omega⟩, ?_, ?_, ?_⟩
      · rw [hvc0]; have hvc_nn := vcong_nonneg J H' (fun _ => 1) embJH; positivity
      · rw [hlen0]; simp; linarith
      · simp only [Cited.Graph.m, List.length_nil, Nat.cast_zero, pow_one]
        have hγ_nn : 0 ≤ γ_ℓ := by linarith
        have hL_nn : 0 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := by linarith
        positivity
    · refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, fun j hj => by omega⟩
      · simp [hf0, Cited.Graph.encode]
      · simp [hf1]
      · simp [hf2, hJm0]
      · intro k hk
        simp only [zero_add, hf0, Cited.Graph.encode, Cited.Graph.m, List.flatMap_nil,
          List.length_cons, List.length_nil] at hk ⊢
        rcases k with _ | _ | k
        · simpa using hf3
        · simpa [Nat.add_assoc] using hf4
        · omega
      · intro k hk
        simp only [zero_add, hf1, List.length_cons, List.length_nil] at hk ⊢
        rcases k with _ | k
        · simpa using hf5
        · omega
  · simp only [Expr.size]; omega

lemma sparsifyGuestBody_runs_pos {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {impl : SpannerToolImpl} {fSparsify heap mMax : ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    {H' J : Cited.Graph} {embJH : ℕ → Walk}
    (hsp : MeetsContract w p fSparsify (sparsifyContract impl w))
    (hw16 : 16 ≤ 2 ^ w) (hheap_w : heap < 2 ^ w)
    (hHle : mem 0 + H'.encode.length ≤ heap)
    (hJle : mem 1 + J.encode.length ≤ heap)
    (hEmble : mem 2 + J.m ≤ heap)
    (hH : GraphAt mem (mem 0) H') (hJ : GraphAt mem (mem 1) J)
    (hEmb : EmbAt mem (mem 2) J.m embJH) (hBnd : EmbBounded mem (mem 2) J.m embJH heap)
    (hHval : H'.IsValid) (hJval : J.IsValid) (hIsEmb : IsEmbedding J H' embJH)
    (hJm : J.m ≤ mMax) (hJm_pos : 1 ≤ J.m)
    (hzf : ZeroFrom mem heap)
    (hwok1 : (Task1Input.mk (mem 0) (mem 1) (mem 2) heap H' J embJH).WordWidthOK impl w)
    (hwokS : SparsifyWordOK impl (Task1Input.mk (mem 0) (mem 1) (mem 2) heap H' J embJH) w) :
    let inp : Task1Input := Task1Input.mk (mem 0) (mem 1) (mem 2) heap H' J embJH
    ∃ o st' c,
      Runs w p ω (sparsifyGuestBody fSparsify) (startState [0, heap] mem pos) o st' c ∧
      (heap ≤ o.value ∧ o.value ≤ sparsifyMaxHeapEnd impl inp ∧
       (∀ x < heap, st'.mem x = mem x) ∧
       ZeroFrom st'.mem o.value ∧
       ∃ (cJtilde : Cited.Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk),
         CitedSparsifyProp mMax (sparsifyGuestGammaC impl mMax) (sparsifyGuestGammaL impl mMax)
           (sparsifyGuestKs impl) 1 H' J embJH cJtilde kept embJJtilde ∧
         SparsifyOutRelocAt st'.mem 0 heap o.value J.m cJtilde kept embJJtilde) ∧
      c ≤ sparsifyTotalCost impl inp mem + 40 := by
  intro inp
  have hHenc : H'.encode.length = 2 + 2 * H'.m := graph_encode_len_eq H'
  have hJenc : J.encode.length = 2 + 2 * J.m := graph_encode_len_eq J
  have hp0_w : mem 0 < 2 ^ w := by omega
  have hp1_w : mem 1 < 2 ^ w := by omega
  have hp2_w : mem 2 < 2 ^ w := by omega
  have hmemJ0 : mem (mem 1) = J.n := by simpa [GraphAt, Graph.encode] using hJ 0 (by simp [Graph.encode])
  have hmemJ1 : mem (mem 1 + 1) = J.m := by simpa [GraphAt, Graph.encode] using hJ 1 (by simp [Graph.encode])
  have hValid : inp.Valid impl mem w :=
    ⟨hHval, hH, hJval, hJ, hIsEmb, hEmb, hBnd, hHle, hJle, hzf, hwok1⟩
  let s0 := startState [0, heap] mem pos
  have hr1 : s0.regs 1 = heap := by simp [s0, startState]
  have e2 : (Expr.load (.const 0)).eval w s0 = some (mem 0) :=
    ev_load' (ev_const (by omega)) rfl
  let rg2 := Function.update s0.regs 2 (mem 0)
  have e3 : (Expr.load (.const 1)).eval w ⟨mem, rg2, pos⟩ = some (mem 1) :=
    ev_load' (ev_const (by omega)) rfl
  let rg3 := Function.update rg2 3 (mem 1)
  have e4 : (Expr.load (.const 2)).eval w ⟨mem, rg3, pos⟩ = some (mem 2) :=
    ev_load' (ev_const (by omega)) rfl
  let rg4 := Function.update rg3 4 (mem 2)
  have e5 : (Expr.load (.reg 3)).eval w ⟨mem, rg4, pos⟩ = some J.n :=
    ev_load' (ev_reg (by simp [rg4, rg3]) (by omega)) hmemJ0
  let rg5 := Function.update rg4 5 J.n
  have e6 : (Expr.load (.bin .add (.reg 3) (.const 1))).eval w ⟨mem, rg5, pos⟩ = some J.m :=
    ev_load' (ev_add (ev_reg (by simp [rg5, rg4, rg3]) (by omega)) (ev_const (by omega)) (by omega)) hmemJ1
  let rg6 := Function.update rg5 6 J.m
  have hr1_6 : rg6 1 = heap := by simp [rg6, rg5, rg4, rg3, rg2, hr1]
  have hr2_6 : rg6 2 = mem 0 := by simp [rg6, rg5, rg4, rg3, rg2]
  have hr3_6 : rg6 3 = mem 1 := by simp [rg6, rg5, rg4, rg3]
  have hr4_6 : rg6 4 = mem 2 := by simp [rg6, rg5, rg4]
  have hr6_6 : rg6 6 = J.m := by simp [rg6]
  unfold sparsifyGuestBody
  refine runs_start_le ?_
  refine runs_seq_assign_le e2 ?_
  refine runs_seq_assign_le e3 ?_; dsimp only
  refine runs_seq_assign_le e4 ?_; dsimp only
  refine runs_seq_assign_le e5 ?_; dsimp only
  refine runs_seq_assign_le e6 ?_; dsimp only
  change ∃ o st' c, Runs w p ω _ ⟨mem, rg6, pos⟩ o st' c ∧ _ ∧ _ ≤ _
  have hcond : (Expr.bin .eq (.reg 6) (.const 0)).eval w ⟨mem, rg6, pos⟩ = some 0 := by
    have hne : J.m ≠ 0 := by omega
    simpa [hne] using ev_eq_zero (st := ⟨mem, rg6, pos⟩) 6 hr6_6 (by omega : 1 < 2 ^ w)
  suffices helse : ∃ o st' c,
      Runs w p ω (.call 7 fSparsify [.reg 2, .reg 3, .reg 4, .reg 1] ;; .ret (.reg 7))
        ⟨mem, rg6, pos⟩ o st' c ∧
      (heap ≤ o.value ∧ o.value ≤ sparsifyMaxHeapEnd impl inp ∧
       (∀ x < heap, st'.mem x = mem x) ∧
       ZeroFrom st'.mem o.value ∧
       ∃ (cJtilde : Cited.Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk),
         CitedSparsifyProp mMax (sparsifyGuestGammaC impl mMax) (sparsifyGuestGammaL impl mMax)
           (sparsifyGuestKs impl) 1 H' J embJH cJtilde kept embJJtilde ∧
         SparsifyOutRelocAt st'.mem 0 heap o.value J.m cJtilde kept embJJtilde) ∧
      26 + c ≤ sparsifyTotalCost impl inp mem + 40 by
    rcases helse with ⟨o, st', c, hr, hp, hc⟩
    refine ⟨o, st', (Expr.bin .eq (.reg 6) (.const 0)).size + c + 1,
      runs_cond_iff.mpr ⟨0, c, hcond, by simpa using hr, rfl⟩, hp, ?_⟩
    simp only [Expr.size]; omega
  refine runs_seq_call_le (vs := [mem 0, mem 1, mem 2, heap]) hsp
    (by simp [evalArgs, Expr.eval, hr1_6, hr2_6, hr3_6, hr4_6])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> omega)
    ⟨inp, rfl, hValid, hwokS⟩ ?_
  intro retHeap mem' pos' hpost'
  have hPost := hpost' inp rfl hValid hwokS
  obtain ⟨cJtilde, kept, embJJtilde, hnd, hkept_lt, hJn, hJed, hJval', hEmbJJ, hvc_cap, hlen_cap, hsp_cap,
    h3r, hr_max, hZr, hagr, _, _, _, hpJ_r, hpK_r, hpE_r, hGsub, hkept, hEmbC, hBndC⟩ :=
    sparsifyPost_cap_props hPost hJm
  have hret_w : retHeap < 2 ^ w := lt_of_le_of_lt hr_max hwokS.2
  refine runs_ret_le (ev_reg (by simp) hret_w) ?_ ?_
  · dsimp only [Outcome.value]
    have h3r' : heap + 3 ≤ retHeap := h3r
    refine ⟨by omega, hr_max, hagr, hZr, cJtilde, kept, embJJtilde, ?_, ?_⟩
    · refine ⟨hnd, hkept_lt, hJn, hJed, hJval', hEmbJJ, hvc_cap, hlen_cap, ?_⟩
      rw [pow_one]; exact hsp_cap
    · dsimp only [SparsifyOutRelocAt]
      simp only [zero_add]
      exact ⟨h3r, hpJ_r, hpK_r, hpE_r, hGsub, hkept, fun j hj => ⟨hBndC.2 j hj, hEmbC j hj⟩⟩
  · have h_ex : ∃ inp' : Task1Input,
        [mem 0, mem 1, mem 2, heap] = [inp'.hAddr, inp'.jAddr, inp'.embJHAddr, inp'.h] ∧
        inp'.Valid impl mem w ∧ SparsifyWordOK impl inp' w := ⟨inp, rfl, hValid, hwokS⟩
    have hcost_eq : (sparsifyContract impl w).cost [mem 0, mem 1, mem 2, heap] mem =
        sparsifyTotalCost impl inp mem := by
      dsimp only [sparsifyContract]
      rw [dite_eq_left_of_eq_true (eq_true h_ex)]
      have hspec := Classical.choose_spec h_ex
      generalize Classical.choose h_ex = inp' at hspec ⊢
      obtain ⟨hargs, hvc, _⟩ := hspec
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨_, hj, he, _⟩ := hargs
      obtain ⟨hJeq, hemb_eq⟩ := task1_inputs_agree (by simpa [inp] using hj)
        (by simpa [inp] using he) hValid hvc
      obtain ⟨hlen, hsum⟩ := t1_emb_stats_congr hemb_eq
      have hcore : sparsifyCoreCost impl inp' mem = sparsifyCoreCost impl inp mem := by
        unfold sparsifyCoreCost Task2Input.embVertSum
        simp only [Task1Input.toT2]
        rw [← hJeq, ← hlen, ← hsum, ← hj, ← he]
      unfold sparsifyTotalCost
      rw [hcore, ← hJeq]
    rw [hcost_eq]
    simp only [argsSize, Expr.size]
    omega

lemma guest_cost_bound_pos {impl : SpannerToolImpl} {inp : Task1Input} {mem : ℕ → ℕ}
    {mMax : ℕ}
    (hEmb : IsEmbedding inp.J inp.H' inp.embJH)
    (hgJ : GraphAt mem inp.jAddr inp.J)
    (hEA : EmbAt mem inp.embJHAddr inp.J.m inp.embJH)
    (hJm : inp.J.m ≤ mMax) (hJm_pos : 1 ≤ inp.J.m) (hLen : 1 ≤ length inp.J inp.embJH) :
    sparsifyTotalCost impl inp mem + 40 ≤
      ⌈sparsifyGuestKt impl * sparsifyGuestGammaT impl mMax *
        (1 + (inp.J.n : ℝ) + (inp.J.m : ℝ) * (sparsifyGuestGammaL impl mMax) ^ 2 *
          (length inp.J inp.embJH : ℝ)) *
        (1 + Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2)) ^ 1⌉₊ := by
  set tools := spannerTools_of_impl impl
  set ce := impl.constructExpander
  set φ_min := impl.decompose.φ_lb mMax
  set γ_ℓ := sparsifyGuestGammaL impl mMax
  set γ_t := sparsifyGuestGammaT impl mMax
  have hγt1 : 1 ≤ γ_t := sparsifyGuestGammaT_ge_one impl mMax
  have hγE_pos : 0 < capGammaExpPath (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min mMax := by
    have h2 := two_le_capGammaExpPath (c_deg := 2 * (ce.c_deg_int : ℝ)) (pds := tools.pathDS)
      ce.hφ_Const_pos (impl.decompose.hφ_lb_pos mMax) mMax
    linarith
  have hγq : capGammaQuery (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min mMax ≤
      γ_t * capGammaExpPath (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min mMax := by
    have h1 : capGammaQuery (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min mMax /
        capGammaExpPath (2 * (ce.c_deg_int : ℝ)) ce.φ_Const tools.pathDS φ_min mMax ≤ γ_t :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    exact (div_le_iff₀ hγE_pos).mp h1
  have hγℓ_pos : 0 < γ_ℓ := by linarith [sparsifyGuestGammaL_ge_one impl mMax]
  have hdec_le : impl.decompose.decFactor mMax ≤ γ_t * γ_ℓ ^ 2 := by
    have h1 : impl.decompose.decFactor mMax / γ_ℓ ^ 2 ≤ γ_t := le_max_right _ _
    exact (div_le_iff₀ (sq_pos_of_pos hγℓ_pos)).mp h1
  have hmain := sparsifyTotalCost_le_cap_with_time impl inp mem mMax γ_t hEmb hgJ hEA hJm hJm_pos hLen hγt1 hγq
  set L_log := 1 + Real.log ((inp.J.n : ℝ) + (inp.J.m : ℝ) + 2)
  have hL1 : 1 ≤ L_log := one_le_one_add_log inp.J.n inp.J.m
  have hlen1 : (1 : ℝ) ≤ (length inp.J inp.embJH : ℝ) := by exact_mod_cast hLen
  have hm1 : (1 : ℝ) ≤ (inp.J.m : ℝ) := by exact_mod_cast hJm_pos
  have hγℓ1 : 1 ≤ γ_ℓ := sparsifyGuestGammaL_ge_one impl mMax
  set B := (inp.J.n : ℝ) + (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ)
  have hB1 : 1 ≤ B := by
    have hn0 : (0 : ℝ) ≤ inp.J.n := Nat.cast_nonneg _
    have hsq : 1 ≤ γ_ℓ ^ 2 := by nlinarith
    have h1 : 1 ≤ (inp.J.m : ℝ) * γ_ℓ ^ 2 := by nlinarith
    have hmul : 1 ≤ (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ) := by nlinarith
    linarith
  have hdec_call : ((spannerToolCosts_of_impl impl).decompose.callCost (stripLoops inp.J).m : ℝ) ≤
      (2 * impl.decompose.K_dec + 1) * γ_t * B * L_log := by
    set costs := spannerToolCosts_of_impl impl
    have hKdec : 0 ≤ costs.decompose.K_dec + 1 := by linarith [costs.decompose.hK_dec]
    have hcall := costs.decompose.callCost_le_of_le (le_trans (stripLoops_m_le inp.J) hJm)
    have hstrip_m : ((stripLoops inp.J).m : ℝ) ≤ (inp.J.m : ℝ) :=
      Nat.cast_le.mpr (stripLoops_m_le inp.J)
    have h0 : (costs.decompose.K_dec + 1) * ((stripLoops inp.J).m : ℝ) * costs.decompose.decFactor mMax ≤
        (costs.decompose.K_dec + 1) * (inp.J.m : ℝ) * (γ_t * γ_ℓ ^ 2) := by
      have ha := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstrip_m hKdec)
        (by linarith [costs.decompose.hdec_ge mMax])
      have hb := mul_le_mul_of_nonneg_left (show costs.decompose.decFactor mMax ≤ γ_t * γ_ℓ ^ 2 from hdec_le)
        (mul_nonneg hKdec (Nat.cast_nonneg inp.J.m))
      exact le_trans ha hb
    have hsum : (inp.J.m : ℝ) * (γ_t * γ_ℓ ^ 2) ≤ γ_t * B * L_log := by
      have h1 : (inp.J.m : ℝ) * γ_ℓ ^ 2 ≤ B := by
        have hn0 : (0 : ℝ) ≤ inp.J.n := Nat.cast_nonneg _
        have : (inp.J.m : ℝ) * γ_ℓ ^ 2 ≤ (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ) :=
          le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hlen1
        linarith
      have h2 : γ_t * ((inp.J.m : ℝ) * γ_ℓ ^ 2) ≤ γ_t * B :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
      have h3 : γ_t * B ≤ γ_t * B * L_log :=
        le_mul_of_one_le_right (by positivity) hL1
      linarith
    have hKeq : costs.decompose.K_dec + 1 = 2 * impl.decompose.K_dec + 1 := rfl
    calc (costs.decompose.callCost (stripLoops inp.J).m : ℝ)
        ≤ (costs.decompose.K_dec + 1) * ((inp.J.m : ℝ) * (γ_t * γ_ℓ ^ 2)) := by
          have := le_trans hcall h0; linarith
      _ ≤ (costs.decompose.K_dec + 1) * (γ_t * B * L_log) :=
          mul_le_mul_of_nonneg_left hsum hKdec
      _ = (2 * impl.decompose.K_dec + 1) * γ_t * B * L_log := by rw [hKeq]; ring
  have h40 : (40 : ℝ) ≤ 80 * γ_t * B * L_log := by
    have h1 : 1 ≤ γ_t * B := by nlinarith
    have h2 : 1 ≤ γ_t * B * L_log := by nlinarith
    linarith
  have htot : ((sparsifyTotalCost impl inp mem + 40 : ℕ) : ℝ) ≤
      sparsifyGuestKt impl * γ_t * B * L_log ^ 1 := by
    rw [pow_one, Nat.cast_add, Nat.cast_ofNat]
    have hrew : sparsifyGuestKt impl * γ_t * B * L_log =
        (2 * impl.decompose.K_dec + 1) * γ_t * B * L_log +
        sparsifyProgConst impl * γ_t * B * L_log +
        80 * γ_t * B * L_log := by
      unfold sparsifyGuestKt; ring
    have hmain' : (sparsifyTotalCost impl inp mem : ℝ) ≤
        ((spannerToolCosts_of_impl impl).decompose.callCost (stripLoops inp.J).m : ℝ) +
          sparsifyProgConst impl * γ_t * B * L_log := hmain
    linarith only [hmain', hdec_call, h40, hrew]
  have hB_le : sparsifyGuestKt impl * γ_t * B * L_log ^ 1 ≤
      sparsifyGuestKt impl * γ_t * (1 + B) * L_log ^ 1 := by
    have hKt_nn := sparsifyGuestKt_nonneg impl
    have h1 : B ≤ 1 + B := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h1 (mul_nonneg hKt_nn (by linarith)))
      (pow_nonneg (by linarith) 1)
  have h1B : 1 + B = 1 + (inp.J.n : ℝ) + (inp.J.m : ℝ) * γ_ℓ ^ 2 * (length inp.J inp.embJH : ℝ) := by
    dsimp only [B]; ring
  rw [h1B] at hB_le
  exact Nat.le_ceil _ |> fun h => by exact_mod_cast le_trans (le_trans htot hB_le) h

end MinCostFlow.Spanner
