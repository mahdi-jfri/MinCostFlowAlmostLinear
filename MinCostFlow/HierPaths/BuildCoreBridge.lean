module

public import MinCostFlow.HierPaths.BuildCoreBridgeHelpers
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Core Bridge: Bridging `CoreOuter.coreAdapterContract` to `ProvidesCoreBump` and `ProvidesCore`

Assembles the deterministic Word-RAM bridge from `CoreOuter.coreAdapterContract` to the hierarchy
builder's core interface (`BuildProgContracts.lean`):

1. **`coreBridgeProcs base fAdapter`** (`coreBridgeEntryProc`, `coreBridgeLevelProc`,
   `coreBridgePackProc`):
   * handles `G.n ≤ 1` directly in `O(1)` time by writing `coreResultWords (.expander G.verts)`
     at `h` (requiring no adapter call);
   * for `2 ≤ G.n`, computes `q' = coreLevel M r G.n` via `coreBridgeLevelProc`, calls
     `fAdapter` at `[q', gAddr, M, r, h + 4 + 2 * G.n, h + 6 + 3 * G.n]`, converts `CoreOutAt`
     into sorted `ListAt mem' h (coreResultWords res)` via `coreBridgePackProc`, lifts
     `CoreOutcomeSpec` from `q'` to `q`, and returns the adapter's bump pointer `v2`.
   * **`coreBridgeProc_meetsBumpContract`**: proves `ProvidesCoreBump` with **constant** time
     multiplier `C_core + 500` (independent of `M, r, q, G`) and space `coreBridgeSpace C_sp M r`.
2. **`coreBridgeZeroProcs base fAdapter`** (`coreBridgeZeroEntryProc`, `coreBridgeLevelProc`,
   `coreBridgePackProc`):
   * appends a single zeroing loop over `[h + (coreResultWords res).length, v2)` and returns
     `h + (coreResultWords res).length`.
   * **`coreBridgeZeroProc_providesCore`**: proves the **exact unmodified `ProvidesCore`** for
     every `(M, r)` with `r ≤ ell M`, with time multiplier
     `C_core + 700 + 20 * C_sp * (2 * coreSpaceBase M r + 1)` and space
     `coreBridgeSpace C_sp M r` — confirming that the three obstructions of
     `BuildCoreBridgeHelpers.lean` (`r ≤ ell M`, `(M, r)`-dependent space, and bump-heap scratch
     reclamation) are the *only* differences between `coreAdapterContract` and `ProvidesCore`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-! ## 1. Bump-Heap Bridge (`coreBridgeEntryProc`, `coreBridgeProcs`) -/

/-- Entry procedure of the bump-heap core bridge taking `[q, gAddr, M, r, h]`. -/
def coreBridgeEntryProc (fLevel fPack fAdapter : ℕ) : Stmt :=
  .assign 5 (.load (.reg 1)) ;;
  .cond (.bin .lt (.reg 5) (.const 2))
    (.store (.reg 4) (.const 0) ;;
     .store (.bin .add (.reg 4) (.const 1)) (.const 1) ;;
     .store (.bin .add (.reg 4) (.const 3)) (.const 1) ;;
     .cond (.reg 5)
       (.store (.bin .add (.reg 4) (.const 2)) (.const 2) ;;
        .ret (.bin .add (.reg 4) (.const 5)))
       (.store (.bin .add (.reg 4) (.const 2)) (.const 1) ;;
        .ret (.bin .add (.reg 4) (.const 4))))
    (.call 6 fLevel [.reg 2, .reg 3, .reg 5] ;;
     .assign 7 (.bin .add (.bin .add (.reg 4) (.const 4)) (.bin .mul (.const 2) (.reg 5))) ;;
     .assign 8 (.bin .add (.bin .add (.reg 4) (.const 6)) (.bin .mul (.const 3) (.reg 5))) ;;
     .call 9 fAdapter [.reg 6, .reg 1, .reg 2, .reg 3, .reg 7, .reg 8] ;;
     .call 10 fPack [.reg 5, .reg 4, .reg 7] ;;
     .ret (.reg 9))

/-- Three-procedure module for the bump-heap core bridge placed at `base`. -/
def coreBridgeProcs (base fAdapter : ℕ) : List Stmt :=
  [coreBridgeEntryProc (base + 1) (base + 2) fAdapter, coreBridgeLevelProc, coreBridgePackProc]

theorem coreBridgeProcs_noRand (base fAdapter : ℕ) :
    ∀ s ∈ coreBridgeProcs base fAdapter, s.NoRand := by
  intro s hs
  simp only [coreBridgeProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · simp [coreBridgeEntryProc, Stmt.NoRand]
  · exact coreBridgeLevelProc_noRand
  · exact coreBridgePackProc_noRand

/-! ## 2. Zero-Reclaiming Bridge (`coreBridgeZeroEntryProc`, `coreBridgeZeroProcs`) -/

/-- Entry procedure of the zero-reclaiming core bridge taking `[q, gAddr, M, r, h]`.
Same as `coreBridgeEntryProc`, plus a loop clearing `[endOut, v2)` before returning `endOut`. -/
def coreBridgeZeroEntryProc (fLevel fPack fAdapter : ℕ) : Stmt :=
  .assign 5 (.load (.reg 1)) ;;
  .cond (.bin .lt (.reg 5) (.const 2))
    (.store (.reg 4) (.const 0) ;;
     .store (.bin .add (.reg 4) (.const 1)) (.const 1) ;;
     .store (.bin .add (.reg 4) (.const 3)) (.const 1) ;;
     .cond (.reg 5)
       (.store (.bin .add (.reg 4) (.const 2)) (.const 2) ;;
        .ret (.bin .add (.reg 4) (.const 5)))
       (.store (.bin .add (.reg 4) (.const 2)) (.const 1) ;;
        .ret (.bin .add (.reg 4) (.const 4))))
    (.call 6 fLevel [.reg 2, .reg 3, .reg 5] ;;
     .assign 7 (.bin .add (.bin .add (.reg 4) (.const 4)) (.bin .mul (.const 2) (.reg 5))) ;;
     .assign 8 (.bin .add (.bin .add (.reg 4) (.const 6)) (.bin .mul (.const 3) (.reg 5))) ;;
     .call 9 fAdapter [.reg 6, .reg 1, .reg 2, .reg 3, .reg 7, .reg 8] ;;
     .call 10 fPack [.reg 5, .reg 4, .reg 7] ;;
     forRange 11 (.reg 10) (.reg 9)
       (.store (.reg 11) (.const 0)) ;;
     .ret (.reg 10))

/-- Three-procedure module for the zero-reclaiming core bridge placed at `base`. -/
def coreBridgeZeroProcs (base fAdapter : ℕ) : List Stmt :=
  [coreBridgeZeroEntryProc (base + 1) (base + 2) fAdapter, coreBridgeLevelProc, coreBridgePackProc]

theorem coreBridgeZeroProcs_noRand (base fAdapter : ℕ) :
    ∀ s ∈ coreBridgeZeroProcs base fAdapter, s.NoRand := by
  intro s hs
  simp only [coreBridgeZeroProcs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · simp [coreBridgeZeroEntryProc, forRange, forUp, Stmt.NoRand]
  · exact coreBridgeLevelProc_noRand
  · exact coreBridgePackProc_noRand

/-! ## 3. Shared Arithmetic and Small-Graph Helper Lemmas -/

private lemma ell_le_coreAdapterCost {M r q : ℕ} {G : Graph} (hn : 1 ≤ G.n) :
    ell M ≤ coreAdapterCost M r q G := by
  have h1 : ell M ≤ WParam ParamConfig.default M := by unfold WParam LParam; omega
  have hW1 : 1 ≤ WParam ParamConfig.default M := by unfold WParam; omega
  have h2 : WParam ParamConfig.default M ≤ (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) :=
    Nat.le_self_pow (by omega) _
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  unfold coreAdapterCost
  exact le_trans h1 (le_trans h2 (Nat.le_mul_of_pos_left _ (Nat.mul_pos hn (Nat.pow_pos hN1))))

private lemma n_le_coreAdapterCost {M r q : ℕ} {G : Graph} :
    G.n ≤ coreAdapterCost M r q G := by
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hW1 : 1 ≤ WParam ParamConfig.default M := by unfold WParam; omega
  unfold coreAdapterCost
  rw [Nat.mul_assoc]
  exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.pow_pos hN1) (Nat.pow_pos hW1))

private lemma coreAdapterCost_pos {M r q : ℕ} {G : Graph} (hn : 1 ≤ G.n) :
    1 ≤ coreAdapterCost M r q G :=
  le_trans hn n_le_coreAdapterCost

private lemma small_branch_runs {w h n : ℕ} {p : Program} {G : Graph}
    (mem : ℕ → ℕ) (st : State) (ω : ℕ → Bool)
    (hmem : st.mem = mem) (hr4 : st.regs 4 = h) (hr5 : st.regs 5 = n)
    (hGn : G.n = n) (hn2 : n < 2) (hZero : ZeroFrom mem h) (hh5 : h + 5 < 2 ^ w) :
    ∃ (v c : ℕ) (st' : State),
      Runs w p ω
        (.store (.reg 4) (.const 0) ;;
         .store (.bin .add (.reg 4) (.const 1)) (.const 1) ;;
         .store (.bin .add (.reg 4) (.const 3)) (.const 1) ;;
         .cond (.reg 5)
           (.store (.bin .add (.reg 4) (.const 2)) (.const 2) ;;
            .ret (.bin .add (.reg 4) (.const 5)))
           (.store (.bin .add (.reg 4) (.const 2)) (.const 1) ;;
            .ret (.bin .add (.reg 4) (.const 4))))
        st (.returned v) st' c ∧
      v = h + (coreResultWords (.expander G.verts)).length ∧
      ListAt st'.mem h (coreResultWords (.expander G.verts)) ∧
      (∀ a < h, st'.mem a = mem a) ∧
      ZeroFrom st'.mem v ∧
      c ≤ 60 := by
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have h5w : 5 < 2 ^ w := by omega
  suffices hrun : ∃ o st' c,
      Runs w p ω
        (.store (.reg 4) (.const 0) ;;
         .store (.bin .add (.reg 4) (.const 1)) (.const 1) ;;
         .store (.bin .add (.reg 4) (.const 3)) (.const 1) ;;
         .cond (.reg 5)
           (.store (.bin .add (.reg 4) (.const 2)) (.const 2) ;;
            .ret (.bin .add (.reg 4) (.const 5)))
           (.store (.bin .add (.reg 4) (.const 2)) (.const 1) ;;
            .ret (.bin .add (.reg 4) (.const 4))))
        st o st' c ∧
      (∃ v, o = .returned v ∧
        v = h + (coreResultWords (.expander G.verts)).length ∧
        ListAt st'.mem h (coreResultWords (.expander G.verts)) ∧
        (∀ a < h, st'.mem a = mem a) ∧
        ZeroFrom st'.mem v) ∧
      c ≤ 60 by
    rcases hrun with ⟨_, st', c, hr, ⟨v, rfl, hv, hL, hfr, hZ⟩, hc⟩
    exact ⟨v, c, st', hr, hv, hL, hfr, hZ, hc⟩
  refine runs_start_le ?_
  refine runs_seq_store_le (x := h) (v := 0)
    (by simp [Expr.eval, hr4]) (by simp [Expr.eval, h0w]) ?_
  refine runs_seq_store_le (x := h + 1) (v := 1)
    (by simp [Expr.eval, BinOp.eval, hr4, h1w, (by omega : h + 1 < 2 ^ w)])
    (by simp [Expr.eval, h1w]) ?_
  refine runs_seq_store_le (x := h + 3) (v := 1)
    (by simp [Expr.eval, BinOp.eval, hr4, h3w, (by omega : h + 3 < 2 ^ w)])
    (by simp [Expr.eval, h1w]) ?_
  refine runs_cond_le (v := n) (by simp [Expr.eval, hr5]) ?_ ?_
  · intro hn_ne
    have hn1 : n = 1 := by omega
    have hverts : G.verts = {0} := by simp [Graph.verts, hGn, hn1]
    have hwords : coreResultWords (.expander G.verts) = [0, 1, 2, 1, 0] := by
      rw [coreResultWords_eq_header_append]
      simp [coreResultSet, coreTag, hverts, finsetWords]
    refine runs_seq_store_le (x := h + 2) (v := 2)
      (by simp [Expr.eval, BinOp.eval, hr4, h2w, (by omega : h + 2 < 2 ^ w)])
      (by simp [Expr.eval, h2w]) ?_
    refine runs_ret_le (v := h + 5)
      (by simp [Expr.eval, BinOp.eval, hr4, h5w, hh5]) ?_ ?_
    · refine ⟨h + 5, rfl, by simp [hwords], ?_, ?_, ?_⟩
      · rw [hwords]
        intro j hj
        have hj5 : j < 5 := by simpa using hj
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
        · simp
        · simp
        · simp
        · simp
        · simp [hmem, hZero (h + 4) (by omega)]
      · intro a ha
        simp [Function.update_of_ne (by omega : a ≠ h + 2),
              Function.update_of_ne (by omega : a ≠ h + 3),
              Function.update_of_ne (by omega : a ≠ h + 1),
              Function.update_of_ne (by omega : a ≠ h), hmem]
      · intro a ha
        simp [Function.update_of_ne (by omega : a ≠ h + 2),
              Function.update_of_ne (by omega : a ≠ h + 3),
              Function.update_of_ne (by omega : a ≠ h + 1),
              Function.update_of_ne (by omega : a ≠ h),
              hmem, hZero a (by omega)]
    · simp [Expr.size]
  · intro hn0
    have hverts : G.verts = ∅ := by simp [Graph.verts, hGn, hn0]
    have hwords : coreResultWords (.expander G.verts) = [0, 1, 1, 1] := by
      rw [coreResultWords_eq_header_append]
      simp [coreResultSet, coreTag, hverts, finsetWords]
    refine runs_seq_store_le (x := h + 2) (v := 1)
      (by simp [Expr.eval, BinOp.eval, hr4, h2w, (by omega : h + 2 < 2 ^ w)])
      (by simp [Expr.eval, h1w]) ?_
    refine runs_ret_le (v := h + 4)
      (by simp [Expr.eval, BinOp.eval, hr4, h4w, (by omega : h + 4 < 2 ^ w)]) ?_ ?_
    · refine ⟨h + 4, rfl, by simp [hwords], ?_, ?_, ?_⟩
      · rw [hwords]
        intro j hj
        have hj4 : j < 4 := by simpa using hj
        rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
        · simp
        · simp
        · simp
        · simp
      · intro a ha
        simp [Function.update_of_ne (by omega : a ≠ h + 2),
              Function.update_of_ne (by omega : a ≠ h + 3),
              Function.update_of_ne (by omega : a ≠ h + 1),
              Function.update_of_ne (by omega : a ≠ h), hmem]
      · intro a ha
        simp [Function.update_of_ne (by omega : a ≠ h + 2),
              Function.update_of_ne (by omega : a ≠ h + 3),
              Function.update_of_ne (by omega : a ≠ h + 1),
              Function.update_of_ne (by omega : a ≠ h),
              hmem, hZero a (by omega)]
    · simp [Expr.size]

/-! ## 4. Main Bridge Theorem 1: Constant-`K` `ProvidesCoreBump` -/

/-- **Main bump-heap bridge theorem**: given any deterministic core adapter meeting
`CoreOuter.coreAdapterContract M r (coreAdapterCost M r) C_core C_sp w`, `coreBridgeProcs`
meets `ProvidesCoreBump` with **constant** time multiplier `C_core + 500` (independent of
`M, r, q, G`) and scratch space `coreBridgeSpace C_sp M r`. -/
theorem coreBridgeProc_meetsBumpContract {w base fAdapter M r C_core C_sp : ℕ} {p : Program}
    (hp : p.HasAt base (coreBridgeProcs base fAdapter))
    (hAdapter : MeetsContract w p fAdapter
      (coreAdapterContract M r (coreAdapterCost M r) C_core C_sp w)) :
    ProvidesCoreBump w (C_core + 500) M r (coreAdapterCost M r) (coreBridgeSpace C_sp M r) p base := by
  have hEntry : p.procs[base]? = some (coreBridgeEntryProc (base + 1) (base + 2) fAdapter) := by
    simpa [coreBridgeProcs] using hp 0 (by simp [coreBridgeProcs])
  have hLevel : MeetsContract w p (base + 1) (coreBridgeLevelContract w) :=
    coreBridgeLevelProc_meetsContract (by simpa [coreBridgeProcs] using hp 1 (by simp [coreBridgeProcs]))
  have hPack : ∀ res, MeetsContract w p (base + 2) (coreBridgePackContract w res) := fun res =>
    coreBridgePackProc_meetsContract (by simpa [coreBridgeProcs] using hp 2 (by simp [coreBridgeProcs]))
  intro q G
  refine meetsContract_of_runs hEntry fun args mem pos ω hwords hpre => ?_
  obtain ⟨⟨gAddr, h, rfl, hGat, hgEnd, hqr, hrl, hGv, hGl, hGn_pow, hGdeg⟩, hZero0, hSpace0⟩ := hpre
  have hZero : ZeroFrom mem h := by simpa [heapArg] using hZero0
  have hSpace : h + coreBridgeSpace C_sp M r G.encode.length < 2 ^ w := by
    simpa [heapArg] using hSpace0
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hGn_r : G.n ≤ (NOf M r) ^ r := le_trans hGn_pow (Nat.pow_le_pow_right hN1 hqr)
  have h40_sp : 40 ≤ coreBridgeSpace C_sp M r G.encode.length := by unfold coreBridgeSpace; omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have h6w : 6 < 2 ^ w := by omega
  have h16w : 16 < 2 ^ w := by omega
  have hGn_read : mem gAddr = G.n := by
    have h0 := hGat 0 (by simp [Graph.encode])
    simpa [Graph.encode] using h0
  refine runs_start_le ?_
  unfold coreBridgeEntryProc
  refine runs_seq_assign_le (v := G.n) (by simp [Expr.eval, startState, hGn_read]) ?_
  refine runs_cond_le (v := if G.n < 2 then 1 else 0)
    (by by_cases hlt : G.n < 2 <;> simp [Expr.eval, BinOp.eval, h2w, h1w, hlt]) ?_ ?_
  · -- Small graph branch: G.n < 2
    intro hcond
    have hlt2 : G.n < 2 := by by_contra hge; simp [hge] at hcond
    let stA : State := { startState [q, gAddr, M, r, h] mem pos with
      regs := Function.update (startState [q, gAddr, M, r, h] mem pos).regs 5 G.n }
    obtain ⟨v, c, st', hrun, hv, hL, hfr, hZ, hc⟩ :=
      small_branch_runs (w := w) (G := G) mem stA ω rfl (by simp [stA, startState]) (by simp [stA])
        rfl hlt2 hZero (by omega)
    refine ⟨.returned v, st', c, hrun, ?_, ?_⟩
    · refine ⟨⟨?_, ?_, ?_, hZ, trivial⟩, gAddr, h, .expander G.verts, rfl, hL, le_of_eq hv.symm,
        coreOutcomeSpec_expander_verts_le_one (by omega)⟩
      · simp [heapArg, Outcome.value, hv]
      · simp only [Outcome.value, hv]
        have hha : heapArg [q, gAddr, M, r, h] = h := by simp [heapArg]
        rw [hha]
        have hlen5 : (coreResultWords (.expander G.verts)).length ≤ 5 := by
          rw [coreResultWords_eq_header_append, List.length_append]
          simp [coreResultSet, finsetWords, Graph.verts]; omega
        omega
      · intro a ha
        have ha' : a < h := by simpa [heapArg] using ha
        exact hfr a ha'
    · simp only [CoreProcBumpContract, heapContract, Expr.size]
      have : 1 ≤ coreAdapterCost M r q G + G.encode.length + 1 := by omega
      nlinarith
  · -- Main branch: 2 ≤ G.n
    intro hcond
    have hn2 : 2 ≤ G.n := by
      by_contra hlt
      have h2' : G.n < 2 := by omega
      simp [h2'] at hcond
    have hr1 : 1 ≤ r := by
      by_contra hr0
      have hr0' : r = 0 := by omega
      have hq0 : q = 0 := by omega
      rw [hq0, pow_zero] at hGn_pow; omega
    have hM2 : 2 * M + 2 ≤ (NOf M r) ^ r := two_mul_add_two_le_NOf_pow (M := M) (r := r) hr1
    have h4M_w : 4 * M + 16 < 2 ^ w := by unfold coreBridgeSpace at hSpace; omega
    have hNn_w : NOf M r * G.n + 16 < 2 ^ w := by
      have : NOf M r * G.n ≤ (NOf M r) ^ (r + 1) := by
        rw [pow_succ']; exact Nat.mul_le_mul_left _ hGn_r
      unfold coreBridgeSpace at hSpace; omega
    have hGn_w : G.n < 2 ^ w := by
      have : G.n ≤ NOf M r * G.n := Nat.le_mul_of_pos_left _ hN1
      omega
    have hMw : M < 2 ^ w := hwords M (by simp)
    have hrw : r < 2 ^ w := hwords r (by simp)
    have hgw : gAddr < 2 ^ w := hwords gAddr (by simp)
    have hhw : h < 2 ^ w := hwords h (by simp)
    -- 1. Call fLevel [M, r, G.n] -> reg 6 = q'
    refine runs_seq_call_le hLevel (vs := [M, r, G.n])
      (by simp [evalArgs, Expr.eval, startState])
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> omega)
      ⟨M, r, G.n, rfl, hr1, hrl, hn2, hGn_r, h4M_w, hNn_w⟩ ?_
    intro q' mem0 pos0 hPost0
    rcases hPost0 with ⟨hq'eq, rfl⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hq'eq
    subst hq'eq
    set q' := coreLevel M r G.n
    have hq'1 : 1 ≤ q' := one_le_coreLevel hn2
    have hq'q : q' ≤ q := Nat.clog_le_of_le_pow hGn_pow
    have hq'r : q' ≤ r := le_trans hq'q hqr
    have hq'lo : (NOf M r) ^ (q' - 1) < G.n := pow_pred_coreLevel_lt hn2
    have hq'hi : G.n ≤ (NOf M r) ^ q' := le_pow_coreLevel M r G.n
    have hSpBound := coreAdapterSpace_le_coreBridgeSpace (C_sp := C_sp) (gLen := G.encode.length) hq'r hq'hi
    have hcost_eq : coreAdapterCost M r q' G = coreAdapterCost M r q G := rfl
    set outAddr := h + 4 + 2 * G.n
    set h' := h + 6 + 3 * G.n
    have hh'_w : h' < 2 ^ w := by omega
    have hout_w : outAddr < 2 ^ w := by omega
    -- 2. Compute outAddr and h'
    refine runs_seq_assign_le (v := outAddr)
      (by simp [Expr.eval, BinOp.eval, startState, h4w, h2w, (by omega : h + 4 < 2 ^ w),
            (by omega : 2 * G.n < 2 ^ w), hout_w, outAddr]) ?_
    refine runs_seq_assign_le (v := h')
      (by simp [Expr.eval, BinOp.eval, startState, h6w, h3w, (by omega : h + 6 < 2 ^ w),
            (by omega : 3 * G.n < 2 ^ w), hh'_w, h']) ?_
    -- 3. Call fAdapter [q', gAddr, M, r, outAddr, h'] -> reg 9 = v2
    have hq'w : q' < 2 ^ w := by omega
    have hGe_len : G.encode.length = 2 + 2 * G.m := graph_encode_length G
    have hAdPre : (coreAdapterContract M r (coreAdapterCost M r) C_core C_sp w).pre
        [q', gAddr, M, r, outAddr, h'] mem0 :=
      ⟨q', gAddr, outAddr, h', G, rfl, hq'1, hq'r, hrl, hGat, hGv, hGl, hq'lo, hq'hi, hGdeg,
        fun a ha => hZero a (by omega), by omega, by omega, Or.inr (by omega),
        by omega, h16w, hMw, hrw⟩
    refine runs_seq_call_le hAdapter (vs := [q', gAddr, M, r, outAddr, h'])
      (by simp [evalArgs, Expr.eval, startState])
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      hAdPre ?_
    intro v2 mem1 pos1 hPost1
    simp only [coreAdapterContract, List.getD_cons_zero, List.getD_cons_succ,
      readGraph_eq_of_graphAt hGat] at hPost1
    rcases hPost1 with ⟨⟨res, hCoreOut, hSpec'⟩, hv2_lo, hv2_hi, hZero1, hFrame1⟩
    have hSpec : CoreOutcomeSpec ParamConfig.default M q G res := coreOutcomeSpec_mono_q hq'q hSpec'
    have hResSub : coreResultSet res ⊆ Finset.range G.n := by
      cases res with | cut U => exact hSpec.1 | expander S => exact hSpec.1
    have hZero1_pref : ∀ a, h ≤ a → a < outAddr → mem1 a = 0 := fun a ha1 ha2 =>
      (hFrame1 a (by omega) (Or.inl ha2)).trans (hZero a ha1)
    -- 4. Call fPack [G.n, h, outAddr] -> reg 10 = endOut
    refine runs_seq_call_le (hPack res) (vs := [G.n, h, outAddr])
      (by simp [evalArgs, Expr.eval, startState])
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> omega)
      ⟨G.n, h, outAddr, rfl, by omega, rfl, hh'_w, hCoreOut, hResSub, hZero1_pref⟩ ?_
    intro endOut mem2 pos2 hPost2
    rcases hPost2 with ⟨_, _, _, hEqP, hList2, hendOut, hFrame2⟩
    simp only [List.cons.injEq, and_true] at hEqP
    obtain ⟨rfl, rfl, rfl⟩ := hEqP
    -- 5. Return reg 9 (= v2)
    refine runs_ret_le (v := v2) (by simp [Expr.eval]) ?_ ?_
    · refine ⟨⟨?_, ?_, ?_, ?_, trivial⟩, gAddr, h, res, rfl, hList2, ?_, hSpec⟩
      · have hha : heapArg [q, gAddr, M, r, h] = h := by simp [heapArg]
        simp only [Outcome.value, hha]; omega
      · have hha : heapArg [q, gAddr, M, r, h] = h := by simp [heapArg]
        simp only [Outcome.value, hha]; omega
      · intro a ha
        have ha' : a < h := by simpa [heapArg] using ha
        have h1 := hFrame2 a (Or.inl ha')
        have h2 := hFrame1 a (by omega) (Or.inl (by omega))
        exact h1.trans h2
      · intro a ha
        simp only [Outcome.value] at ha
        exact (hFrame2 a (Or.inr (by omega))).trans (hZero1 a ha)
      · simp only [Outcome.value]
        have hcard : (coreResultSet res).card ≤ G.n := by
          simpa using Finset.card_le_card hResSub
        have hlen : (coreResultWords res).length = 4 + (coreResultSet res).card := by
          rw [coreResultWords_eq_header_append, List.length_append]
          simp [finsetWords]
        omega
    · simp only [CoreProcBumpContract, heapContract, coreBridgeLevelContract, coreBridgeLevelCost,
        coreAdapterContract, coreBridgePackContract, List.getD_cons_zero, List.getD_cons_succ,
        readGraph_eq_of_graphAt hGat, Expr.size, argsSize, hcost_eq]
      set cc := coreAdapterCost M r q G
      have hEll_cc : ell M ≤ cc := ell_le_coreAdapterCost (by omega)
      have hr_cc : r ≤ cc := le_trans hrl hEll_cc
      have hn_cc : G.n ≤ cc := n_le_coreAdapterCost
      have hcc1 : 1 ≤ cc := coreAdapterCost_pos (by omega)
      have h1 : (C_core + 500) * (cc + G.encode.length + 1) ≥ C_core * cc + 500 * cc + C_core + 500 := by
        nlinarith
      omega

/-- **Main core bridge theorem**: `coreBridgeProcs` directly meets `ProvidesCore` with constant
time multiplier `C_core + 500` and scratch space `coreBridgeSpace C_sp M r`, since `ProvidesCore`
adopts the bump-heap contract (`r ≤ ell M`, `(M, r)`-dependent space, `h + |res| ≤ v`). -/
theorem coreBridgeProcs_providesCore {w base fAdapter M r C_core C_sp : ℕ} {p : Program}
    (hp : p.HasAt base (coreBridgeProcs base fAdapter))
    (hAdapter : MeetsContract w p fAdapter
      (coreAdapterContract M r (coreAdapterCost M r) C_core C_sp w)) :
    ProvidesCore w (C_core + 500) M r (coreAdapterCost M r) (coreBridgeSpace C_sp M r) p base :=
  coreBridgeProc_meetsBumpContract hp hAdapter

/-! ## 5. Main Bridge Theorem 2: Zero-Reclaiming Bridge -/

private lemma zero_tail_loop {w endOut v2 : ℕ} (p : Program) (mem₀ : ℕ → ℕ)
    (hle : endOut ≤ v2) (hv2_w : v2 + 1 < 2 ^ w) :
    Triple w p
      (fun st => st.regs 9 = v2 ∧ st.regs 10 = endOut ∧ st.mem = mem₀)
      (forRange 11 (.reg 10) (.reg 9) (.store (.reg 11) (.const 0)))
      (normalPost fun st' =>
        st'.regs 10 = endOut ∧
        (∀ a, endOut ≤ a → a < v2 → st'.mem a = 0) ∧
        (∀ a, a < endOut ∨ v2 ≤ a → st'.mem a = mem₀ a))
      (fun _ => 20 * (v2 - endOut) + 30) := by
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 11) (lo := .reg 10) (hi := .reg 9)
    (body := .store (.reg 11) (.const 0))
    (P := fun st => st.regs 9 = v2 ∧ st.regs 10 = endOut ∧ st.mem = mem₀)
    (Inv := fun i st =>
      st.regs 9 = v2 ∧ st.regs 10 = endOut ∧ st.regs 11 = i ∧
      (∀ a, endOut ≤ a → a < i → st.mem a = 0) ∧
      (∀ a, a < endOut ∨ i ≤ a → st.mem a = mem₀ a))
    4 endOut v2 hle h1w (fun _ => by omega)
    (fun st ⟨h9, h10, hm⟩ =>
      ⟨by simp [Expr.eval, h10], by simp [h9], by simp [h10], by simp,
        fun _ ha1 ha2 => by omega, fun _ _ => by rw [hm]⟩)
    (fun _ st _ _ hi => hi.2.2.1)
    (fun _ st _ _ hi => by have h9 : st.regs 9 = v2 := hi.1; eval_expr)
    (fun i hilo hilt => by
      intro st ω ⟨h9, h10, h11, hz, hfr⟩
      set st1 : State := { st with mem := Function.update st.mem i 0 }
      have hs : Runs w p ω (.store (.reg 11) (.const 0)) st .normal st1 3 := by
        rw [runs_store_iff]
        exact ⟨i, 0, by simp [Expr.eval, h11], by simp [Expr.eval, h0w],
          rfl, rfl, by simp [Expr.size]⟩
      refine ⟨.normal, st1, 3, hs, ⟨⟨by simp [st1, h9], by simp [st1, h10], by simp [st1],
        ?_, ?_⟩, by simp [st1, h11]⟩, by dsimp only; omega⟩
      · intro a ha1 ha2
        by_cases hai : a = i
        · subst hai; simp [st1]
        · exact (Function.update_of_ne hai 0 st.mem).trans (hz a ha1 (by omega))
      · intro a ha
        have hai : a ≠ i := by omega
        exact (Function.update_of_ne hai 0 st.mem).trans (hfr a (by omega)))
  exact hloop.conseq (fun _ h => h)
    (fun o st' h => by
      cases o with
      | returned _ => exact False.elim h
      | normal => exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2⟩)
    (fun _ _ => by simp [Expr.size]; omega)

/-- **Unmodified `ProvidesCore` bridge theorem (for every `(M, r)` with `r ≤ ell M`)**:
appending the zeroing loop `[endOut, v2)` to `coreBridgeEntryProc` satisfies the exact unmodified
`ProvidesCore` contract (`BuildProgContracts.lean`), with time multiplier
`C_core + 700 + 20 * C_sp * (2 * coreSpaceBase M r + 1)` and space `coreBridgeSpace C_sp M r`. -/
theorem coreBridgeZeroProc_providesCore {w base fAdapter M r C_core C_sp : ℕ} {p : Program}
    (hrl : r ≤ ell M)
    (hp : p.HasAt base (coreBridgeZeroProcs base fAdapter))
    (hAdapter : MeetsContract w p fAdapter
      (coreAdapterContract M r (coreAdapterCost M r) C_core C_sp w)) :
    ProvidesCore w (C_core + 700 + 20 * C_sp * (2 * coreSpaceBase M r + 1)) M r
      (coreAdapterCost M r) (coreBridgeSpace C_sp M r) p base := by
  have hEntry : p.procs[base]? = some (coreBridgeZeroEntryProc (base + 1) (base + 2) fAdapter) := by
    simpa [coreBridgeZeroProcs] using hp 0 (by simp [coreBridgeZeroProcs])
  have hLevel : MeetsContract w p (base + 1) (coreBridgeLevelContract w) :=
    coreBridgeLevelProc_meetsContract (by simpa [coreBridgeZeroProcs] using hp 1 (by simp [coreBridgeZeroProcs]))
  have hPack : ∀ res, MeetsContract w p (base + 2) (coreBridgePackContract w res) := fun res =>
    coreBridgePackProc_meetsContract (by simpa [coreBridgeZeroProcs] using hp 2 (by simp [coreBridgeZeroProcs]))
  intro q G
  refine meetsContract_of_runs hEntry fun args mem pos ω hwords hpre => ?_
  obtain ⟨⟨gAddr, h, rfl, hGat, hgEnd, hqr, _, hGv, hGl, hGn_pow, hGdeg⟩, hZero0, hSpace0⟩ := hpre
  have hZero : ZeroFrom mem h := by simpa [heapArg] using hZero0
  have hSpace : h + coreBridgeSpace C_sp M r G.encode.length < 2 ^ w := by
    simpa [heapArg] using hSpace0
  have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
  have hGn_r : G.n ≤ (NOf M r) ^ r := le_trans hGn_pow (Nat.pow_le_pow_right hN1 hqr)
  have h40_sp : 40 ≤ coreBridgeSpace C_sp M r G.encode.length := by unfold coreBridgeSpace; omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have h6w : 6 < 2 ^ w := by omega
  have h16w : 16 < 2 ^ w := by omega
  have hGn_read : mem gAddr = G.n := by
    have h0 := hGat 0 (by simp [Graph.encode])
    simpa [Graph.encode] using h0
  refine runs_start_le ?_
  unfold coreBridgeZeroEntryProc
  refine runs_seq_assign_le (v := G.n) (by simp [Expr.eval, startState, hGn_read]) ?_
  refine runs_cond_le (v := if G.n < 2 then 1 else 0)
    (by by_cases hlt : G.n < 2 <;> simp [Expr.eval, BinOp.eval, h2w, h1w, hlt]) ?_ ?_
  · intro hcond
    have hlt2 : G.n < 2 := by by_contra hge; simp [hge] at hcond
    let stA : State := { startState [q, gAddr, M, r, h] mem pos with
      regs := Function.update (startState [q, gAddr, M, r, h] mem pos).regs 5 G.n }
    obtain ⟨v, c, st', hrun, hv, hL, hfr, hZ, hc⟩ :=
      small_branch_runs (w := w) (G := G) mem stA ω rfl (by simp [stA, startState]) (by simp [stA])
        rfl hlt2 hZero (by omega)
    refine ⟨.returned v, st', c, hrun, ?_, ?_⟩
    · refine ⟨⟨?_, ?_, ?_, hZ, trivial⟩, gAddr, h, .expander G.verts, rfl, hL, le_of_eq hv.symm,
        coreOutcomeSpec_expander_verts_le_one (by omega)⟩
      · simp [heapArg, Outcome.value, hv]
      · simp only [Outcome.value, hv]
        have hha : heapArg [q, gAddr, M, r, h] = h := by simp [heapArg]
        rw [hha]
        have hlen5 : (coreResultWords (.expander G.verts)).length ≤ 5 := by
          rw [coreResultWords_eq_header_append, List.length_append]
          simp [coreResultSet, finsetWords, Graph.verts]; omega
        omega
      · intro a ha
        have ha' : a < h := by simpa [heapArg] using ha
        exact hfr a ha'
    · simp only [CoreProcContract, heapContract, Expr.size]
      exact le_trans (by omega : 0 + (1 + 1) + 2 + (1 + 1 + 1) + 1 + c ≤ 700 * 1)
        (Nat.mul_le_mul (by omega) (by omega))
  · intro hcond
    have hn2 : 2 ≤ G.n := by
      by_contra hlt
      have h2' : G.n < 2 := by omega
      simp [h2'] at hcond
    have hr1 : 1 ≤ r := by
      by_contra hr0
      have hr0' : r = 0 := by omega
      have hq0 : q = 0 := by omega
      rw [hq0, pow_zero] at hGn_pow; omega
    have hM2 : 2 * M + 2 ≤ (NOf M r) ^ r := two_mul_add_two_le_NOf_pow (M := M) (r := r) hr1
    have h4M_w : 4 * M + 16 < 2 ^ w := by unfold coreBridgeSpace at hSpace; omega
    have hNn_w : NOf M r * G.n + 16 < 2 ^ w := by
      have : NOf M r * G.n ≤ (NOf M r) ^ (r + 1) := by
        rw [pow_succ']; exact Nat.mul_le_mul_left _ hGn_r
      unfold coreBridgeSpace at hSpace; omega
    have hGn_w : G.n < 2 ^ w := by
      have : G.n ≤ NOf M r * G.n := Nat.le_mul_of_pos_left _ hN1
      omega
    have hMw : M < 2 ^ w := hwords M (by simp)
    have hrw : r < 2 ^ w := hwords r (by simp)
    have hgw : gAddr < 2 ^ w := hwords gAddr (by simp)
    have hhw : h < 2 ^ w := hwords h (by simp)
    refine runs_seq_call_le hLevel (vs := [M, r, G.n])
      (by simp [evalArgs, Expr.eval, startState])
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> omega)
      ⟨M, r, G.n, rfl, hr1, hrl, hn2, hGn_r, h4M_w, hNn_w⟩ ?_
    intro q' mem0 pos0 hPost0
    rcases hPost0 with ⟨hq'eq, rfl⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hq'eq
    subst hq'eq
    set q' := coreLevel M r G.n
    have hq'1 : 1 ≤ q' := one_le_coreLevel hn2
    have hq'q : q' ≤ q := Nat.clog_le_of_le_pow hGn_pow
    have hq'r : q' ≤ r := le_trans hq'q hqr
    have hq'lo : (NOf M r) ^ (q' - 1) < G.n := pow_pred_coreLevel_lt hn2
    have hq'hi : G.n ≤ (NOf M r) ^ q' := le_pow_coreLevel M r G.n
    have hSpBound := coreAdapterSpace_le_coreBridgeSpace (C_sp := C_sp) (gLen := G.encode.length) hq'r hq'hi
    have hcost_eq : coreAdapterCost M r q' G = coreAdapterCost M r q G := rfl
    set outAddr := h + 4 + 2 * G.n
    set h' := h + 6 + 3 * G.n
    have hh'_w : h' < 2 ^ w := by omega
    have hout_w : outAddr < 2 ^ w := by omega
    refine runs_seq_assign_le (v := outAddr)
      (by simp [Expr.eval, BinOp.eval, startState, h4w, h2w, (by omega : h + 4 < 2 ^ w),
            (by omega : 2 * G.n < 2 ^ w), hout_w, outAddr]) ?_
    refine runs_seq_assign_le (v := h')
      (by simp [Expr.eval, BinOp.eval, startState, h6w, h3w, (by omega : h + 6 < 2 ^ w),
            (by omega : 3 * G.n < 2 ^ w), hh'_w, h']) ?_
    have hq'w : q' < 2 ^ w := by omega
    have hGe_len : G.encode.length = 2 + 2 * G.m := graph_encode_length G
    have hAdPre : (coreAdapterContract M r (coreAdapterCost M r) C_core C_sp w).pre
        [q', gAddr, M, r, outAddr, h'] mem0 :=
      ⟨q', gAddr, outAddr, h', G, rfl, hq'1, hq'r, hrl, hGat, hGv, hGl, hq'lo, hq'hi, hGdeg,
        fun a ha => hZero a (by omega), by omega, by omega, Or.inr (by omega),
        by omega, h16w, hMw, hrw⟩
    refine runs_seq_call_le hAdapter (vs := [q', gAddr, M, r, outAddr, h'])
      (by simp [evalArgs, Expr.eval, startState])
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
      hAdPre ?_
    intro v2 mem1 pos1 hPost1
    simp only [coreAdapterContract, List.getD_cons_zero, List.getD_cons_succ,
      readGraph_eq_of_graphAt hGat] at hPost1
    rcases hPost1 with ⟨⟨res, hCoreOut, hSpec'⟩, hv2_lo, hv2_hi, hZero1, hFrame1⟩
    have hSpec : CoreOutcomeSpec ParamConfig.default M q G res := coreOutcomeSpec_mono_q hq'q hSpec'
    have hResSub : coreResultSet res ⊆ Finset.range G.n := by
      cases res with | cut U => exact hSpec.1 | expander S => exact hSpec.1
    have hZero1_pref : ∀ a, h ≤ a → a < outAddr → mem1 a = 0 := fun a ha1 ha2 =>
      (hFrame1 a (by omega) (Or.inl ha2)).trans (hZero a ha1)
    refine runs_seq_call_le (hPack res) (vs := [G.n, h, outAddr])
      (by simp [evalArgs, Expr.eval, startState])
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> omega)
      ⟨G.n, h, outAddr, rfl, by omega, rfl, hh'_w, hCoreOut, hResSub, hZero1_pref⟩ ?_
    intro endOut mem2 pos2 hPost2
    rcases hPost2 with ⟨_, _, _, hEqP, hList2, hendOut, hFrame2⟩
    simp only [List.cons.injEq, and_true] at hEqP
    obtain ⟨rfl, rfl, rfl⟩ := hEqP
    have hResLen_le : (coreResultWords res).length ≤ 4 + G.n := by
      have hcard : (coreResultSet res).card ≤ G.n := by simpa using Finset.card_le_card hResSub
      rw [coreResultWords_eq_header_append, List.length_append]
      simp [finsetWords]; omega
    have hend_le_v2 : endOut ≤ v2 := by omega
    have hv2_1_w : v2 + 1 < 2 ^ w := by omega
    -- 5. Zero [endOut, v2)
    refine runs_seq_triple_le (zero_tail_loop (w := w) (endOut := endOut) (v2 := v2) p mem2 hend_le_v2 hv2_1_w)
      ⟨by simp, by simp, rfl⟩ ?_
    intro st3 ⟨h3_10, h3_zero, h3_fr⟩
    refine runs_ret_le (v := endOut) (Expr.eval_reg_of_eq h3_10) ?_ ?_
    · refine ⟨⟨?_, ?_, ?_, ?_, trivial⟩, gAddr, h, res, rfl, ?_, le_of_eq hendOut.symm, hSpec⟩
      · have hha : heapArg [q, gAddr, M, r, h] = h := by simp [heapArg]
        simp only [Outcome.value, hha]; omega
      · have hha : heapArg [q, gAddr, M, r, h] = h := by simp [heapArg]
        simp only [Outcome.value, hha]; omega
      · intro a ha
        have ha' : a < h := by simpa [heapArg] using ha
        exact (h3_fr a (Or.inl (by omega))).trans
          ((hFrame2 a (Or.inl ha')).trans (hFrame1 a (by omega) (Or.inl (by omega))))
      · intro a ha
        simp only [Outcome.value] at ha
        by_cases hlt : a < v2
        · exact h3_zero a ha hlt
        · exact (h3_fr a (Or.inr (by omega))).trans
            ((hFrame2 a (Or.inr (by omega))).trans (hZero1 a (by omega)))
      · intro j hj
        have haddr : h + j < endOut := by omega
        exact (h3_fr (h + j) (Or.inl haddr)).trans (hList2 j hj)
    · simp only [CoreProcContract, heapContract, coreBridgeLevelContract,
        coreBridgeLevelCost, coreAdapterContract, coreBridgePackContract,
        List.getD_cons_zero, List.getD_cons_succ, readGraph_eq_of_graphAt hGat,
        Expr.size, argsSize, hcost_eq]
      have hEll_cc : ell M ≤ coreAdapterCost M r q G := ell_le_coreAdapterCost (by omega)
      have hr_cc : r ≤ coreAdapterCost M r q G := le_trans hrl hEll_cc
      have hn_cc : G.n ≤ coreAdapterCost M r q G := n_le_coreAdapterCost
      have hcc1 : 1 ≤ coreAdapterCost M r q G := coreAdapterCost_pos (by omega)
      have hGn5_le : (G.n + 3) ^ 5 ≤ coreSpaceBase M r := by
        unfold coreSpaceBase
        have hL4 : 4 ≤ LParam M := four_le_LParam M
        have h1 : G.n + 3 ≤ 2048 * LParam M * (NOf M r) ^ r + 3 := by
          have : (NOf M r) ^ r ≤ 2048 * LParam M * (NOf M r) ^ r :=
            Nat.le_mul_of_pos_left _ (by omega)
          omega
        exact Nat.pow_le_pow_left h1 5
      have hAdSp_le : coreAdapterSpace C_sp M r G.n (coreAdapterCost M r q G) ≤
          C_sp * (2 * coreSpaceBase M r + 1) * (coreAdapterCost M r q G + 1) := by
        unfold coreAdapterSpace
        have h1 : coreSpaceBase M r * (coreAdapterCost M r q G + 1) + (G.n + 3) ^ 5 + 1 ≤
            (2 * coreSpaceBase M r + 1) * (coreAdapterCost M r q G + 1) := by
          clear * - hGn5_le hcc1; nlinarith
        calc C_sp * (coreSpaceBase M r * (coreAdapterCost M r q G + 1) + (G.n + 3) ^ 5 + 1)
            ≤ C_sp * ((2 * coreSpaceBase M r + 1) * (coreAdapterCost M r q G + 1)) :=
              Nat.mul_le_mul_left _ h1
          _ = C_sp * (2 * coreSpaceBase M r + 1) * (coreAdapterCost M r q G + 1) := by ring
      have hv2_hi' : v2 ≤ h + 6 + 3 * G.n + coreAdapterSpace C_sp M r G.n (coreAdapterCost M r q G) := by
        simpa [h', hcost_eq] using hv2_hi
      have hhe : h ≤ endOut := by omega
      have hv2_diff : v2 - endOut ≤
          6 + 3 * G.n + C_sp * (2 * coreSpaceBase M r + 1) * (coreAdapterCost M r q G + 1) := by
        clear * - hv2_hi' hAdSp_le hhe; omega
      have hBudget :
          C_core * coreAdapterCost M r q G + C_core +
            20 * (C_sp * (2 * coreSpaceBase M r + 1) * (coreAdapterCost M r q G + 1)) +
            300 * coreAdapterCost M r q G + 400 ≤
          (C_core + 700 + 20 * C_sp * (2 * coreSpaceBase M r + 1)) *
            (coreAdapterCost M r q G + G.encode.length + 1) := by
        generalize coreAdapterCost M r q G = cc at hcc1 ⊢
        generalize coreSpaceBase M r = sb
        generalize G.encode.length = gl
        clear * - hcc1
        have e1 : 20 * (C_sp * (2 * sb + 1) * (cc + 1)) = 20 * C_sp * (2 * sb + 1) * (cc + 1) := by ring
        rw [e1]
        have h2 : 20 * C_sp * (2 * sb + 1) * (cc + 1) ≤
            20 * C_sp * (2 * sb + 1) * (cc + gl + 1) := Nat.mul_le_mul_left _ (by omega)
        have h3 : C_core * cc + C_core + 300 * cc + 400 ≤ (C_core + 700) * (cc + gl + 1) := by nlinarith
        have e2 : (C_core + 700 + 20 * C_sp * (2 * sb + 1)) * (cc + gl + 1) =
            (C_core + 700) * (cc + gl + 1) + 20 * C_sp * (2 * sb + 1) * (cc + gl + 1) := by ring
        omega
      clear * - hEll_cc hr_cc hn_cc hcc1 hv2_diff hBudget
      omega

end MinCostFlow.HierPaths
