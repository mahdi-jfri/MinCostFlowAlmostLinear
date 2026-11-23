module

public import WordRAM.Contract
public import MinCostFlow.ExpanderDecomp.DecompModel
public import MinCostFlow.ExpanderDecomp.OuterProgContracts

import Mathlib.Tactic.Linarith

/-!
# Entry Contract for the Outer Expander-Decomposition Procedure (`ProgDecompEntrySpec`)

States the Word-RAM contract `outerDecompEntryContract` that the outer decomposition procedure must
meet when called by the top-level entry program (`ProgDecompEntry*.lean`):

- **Arguments:** `[gAddr, r, outAddr, h]`.
- **Input memory (matching `OuterProgContracts.lean`):**
  - `GraphAt mem gAddr G` for a valid loopless graph `G` with `thresholdB1 envelopeCr ≤ G.m`
    (read back as `readGraph mem gAddr = G`);
  - `r = rOf G.m`;
  - an output label buffer `[outAddr, outAddr + G.n)` disjoint from `[gAddr, gAddr + 2 + 2 * G.m)`;
  - a zero-initialized heap `ZeroFrom mem h` with `gAddr + 2 + 2 * G.m ≤ h`, `outAddr + G.n ≤ h`,
    and word-size headroom
    `h + outerDecompSpace C_sp G.n G.m (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m)) < 2 ^ w`.
- **Output memory:** `∃ labels, ListAt mem' outAddr labels ∧ IsExpanderDecomposition G (1 / 200) (phiOut ParamConfig.default G.m (rOf G.m)) labels`.
- **Cost:** at most `K * totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) + K` for an
  input-independent constant `K`.

Also proves `graphAt_initMem_encode`, `zeroFrom_initMem`, and the non-vacuity witness
`outerDecompEntryContract_pre_exists`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Heap-space headroom required by the outer decomposition procedure on an `n`-vertex, `m`-edge
graph with time budget `dcost`. Covers up to `O((n + m + 3)^6)` heap per step across
`dcost + 1` steps. -/
def outerDecompSpace (C_sp n m dcost : ℕ) : ℕ :=
  C_sp * (dcost + 1) * (n + m + 3) ^ 6

/-- Contract of the outer expander-decomposition procedure called by the top-level entry.
`args = [gAddr, r, outAddr, h]`. From `GraphAt mem gAddr G` (valid, loopless,
`thresholdB1 envelopeCr ≤ G.m`), `r = rOf G.m`, and a zero-initialized heap `ZeroFrom mem h`, it
writes a `(1 / 200, phiOut ParamConfig.default G.m (rOf G.m))`-expander decomposition of `G` at
`outAddr` within `K * totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) + K` steps. -/
noncomputable def outerDecompEntryContract (K C_sp w : ℕ) : Contract where
  pre args mem :=
    ∃ (gAddr r outAddr h : ℕ) (G : Graph),
      args = [gAddr, r, outAddr, h] ∧
      GraphAt mem gAddr G ∧
      G.IsValid ∧
      G.IsLoopless ∧
      thresholdB1 envelopeCr ≤ G.m ∧
      r = rOf G.m ∧
      ZeroFrom mem h ∧
      gAddr + 2 + 2 * G.m ≤ h ∧
      outAddr + G.n ≤ h ∧
      DisjointRange outAddr G.n gAddr (2 + 2 * G.m) ∧
      h + outerDecompSpace C_sp G.n G.m (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m)) <
        2 ^ w ∧
      16 < 2 ^ w
  post args mem _v mem' :=
    let gAddr := args.getD 0 0
    let outAddr := args.getD 2 0
    let G := readGraph mem gAddr
    ∃ labels : List ℕ,
      ListAt mem' outAddr labels ∧
      IsExpanderDecomposition G (1 / 200) (phiOut ParamConfig.default G.m (rOf G.m)) labels
  cost args mem :=
    let gAddr := args.getD 0 0
    let G := readGraph mem gAddr
    K * totalTimeRaw ParamConfig.default G.n G.m (rOf G.m) + K

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- In `initMem (G.encode ++ tail)`, `G` is stored in `GraphAt` format at address `0`. -/
lemma graphAt_initMem_encode (G : Graph) (tail : List ℕ) :
    GraphAt (initMem (G.encode ++ tail)) 0 G := by
  intro i hi
  simp only [Nat.zero_add, initMem, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi, List.getElem?_eq_getElem hi, Option.getD_some]

/-- `initMem xs` is identically zero from `xs.length` onwards. -/
lemma zeroFrom_initMem (xs : List ℕ) : ZeroFrom (initMem xs) xs.length := by
  intro a ha
  simp [initMem, List.getD_eq_getElem?_getD, List.getElem?_eq_none ha]

/-- Non-vacuity of `outerDecompEntryContract`: for every pair of constants `K, C_sp`, there exist
a word size `w`, argument list `args`, and memory `mem` satisfying all preconditions of
`outerDecompEntryContract K C_sp w` simultaneously. -/
theorem outerDecompEntryContract_pre_exists (K C_sp : ℕ) :
    ∃ w args mem, (∀ a ∈ args, a < 2 ^ w) ∧ (outerDecompEntryContract K C_sp w).pre args mem := by
  let M₀ : ℕ := thresholdB1 envelopeCr
  let G : Graph := ⟨2, List.replicate M₀ (0, 1)⟩
  have hGm : G.m = M₀ := by simp [G, Graph.m]
  have hGn : G.n = 2 := rfl
  let inp : List ℕ := G.encode ++ [1, 200, rOf G.m]
  let outAddr : ℕ := inp.length
  let h : ℕ := outAddr + G.n
  let w : ℕ := Nat.log 2
    (h + outerDecompSpace C_sp G.n G.m (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m)) + 17) + 1
  have hpow :
      h + outerDecompSpace C_sp G.n G.m (totalTimeRaw ParamConfig.default G.n G.m (rOf G.m)) + 17 <
        2 ^ w :=
    Nat.lt_pow_succ_log_self (by decide) _
  have hinp_len : outAddr = 2 + 2 * G.m + 3 := by
    simp only [outAddr, inp, List.length_append, graph_encode_length, List.length_cons,
      List.length_nil]
  have hr_le : rOf G.m ≤ G.m := by
    have h1 : (rOf G.m) ^ 3 ≤ Nat.log 2 G.m := rOf_pow_le G.m
    have h2 : Nat.log 2 G.m ≤ G.m := Nat.log_le_self 2 G.m
    have h3 : rOf G.m ≤ (rOf G.m) ^ 3 := by
      cases hr : rOf G.m with
      | zero => simp
      | succ k =>
        calc k + 1 = (k + 1) * 1 := (mul_one _).symm
          _ ≤ (k + 1) * ((k + 1) * (k + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
          _ = (k + 1) ^ 3 := by ring
    omega
  refine ⟨w, [0, rOf G.m, outAddr, h], initMem inp, ?_, ?_⟩
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> omega
  · refine ⟨0, rOf G.m, outAddr, h, G, rfl, graphAt_initMem_encode G [1, 200, rOf G.m],
      ?_, ?_, ?_, rfl, ?_, by omega, by omega, Or.inr (by omega), by omega, by omega⟩
    · intro e he
      have he' := List.eq_of_mem_replicate he
      subst he'
      decide
    · intro e he
      have he' := List.eq_of_mem_replicate he
      subst he'
      decide
    · omega
    · intro a ha
      exact zeroFrom_initMem inp a (by omega)

end MinCostFlow.ExpanderDecomp
