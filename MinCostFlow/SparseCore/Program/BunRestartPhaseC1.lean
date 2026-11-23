module

public import MinCostFlow.SparseCore.Program.BunRestartPhaseB
public import MinCostFlow.SparseCore.Program.BundleTourInterface

/-!
# The restart of the bundles: one round of loop C (`BunRestartPhaseC1`)

One round of loop C has two parts. The first (`brLoopCPair_runs`) reads the key and, for an even
key `2 e`, writes the pair `(e, edgeSlot[e] - 1)` (`brPairsOf` lists these pairs). The second
(`brLoopCOwner_runs`) asks the tour for the owner of the key and writes the answer. Both lemmas
give the registers and the memory after the part exactly.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

@[expose] public section

/-- The pairs `(k / 2, edgeSlot[k / 2] - 1)` of the even keys `k` of `ks`, with the edge slots
read in `M`. -/
def brPairsOf (tbl slotCap : ℕ) (M : ℕ → ℕ) (ks : List ℕ) : List (ℕ × ℕ) :=
  (ks.filter fun k => k % 2 = 0).map fun k => (k / 2, M (btEdgeSlotBase tbl slotCap + k / 2) - 1)

end

public section

theorem brPairsOf_take_succ {tbl slotCap : ℕ} {M : ℕ → ℕ} {ks : List ℕ} {i : ℕ}
    (hi : i < ks.length) :
    brPairsOf tbl slotCap M (ks.take (i + 1)) = brPairsOf tbl slotCap M (ks.take i) ++
      (if ks[i] % 2 = 0 then [(ks[i] / 2, M (btEdgeSlotBase tbl slotCap + ks[i] / 2) - 1)]
        else []) := by
  unfold brPairsOf
  rw [List.take_succ_eq_append_getElem hi, List.filter_append, List.map_append]
  by_cases hev : ks[i] % 2 = 0
  · simp [hev]
  · simp [hev]

theorem brPairsOf_length_le {tbl slotCap : ℕ} {M : ℕ → ℕ} {ks : List ℕ} (i : ℕ) :
    (brPairsOf tbl slotCap M (ks.take i)).length ≤
      (ks.filter fun k => k % 2 = 0).length := by
  unfold brPairsOf
  rw [List.length_map]
  conv_rhs => rw [← List.take_append_drop i ks]
  rw [List.filter_append, List.length_append]
  omega

variable {w vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
  {TS : BundleTourSpec} {bTourList bTourLen bOwner : ℕ}

/-- **The pair part of a round of loop C.** It reads the key `key` at `keyP + i`. For an even key
it writes the pair `(key / 2, mem[esb + key / 2] - 1)` at `pairP + 2 cnt` and counts it in
register `20`; for an odd key it changes only register `11`. -/
theorem brLoopCPair_runs {st : State} {esb keyP pairP i cnt key : ℕ} (hw : 16 ≤ 2 ^ w)
    (h6 : st.regs 6 = esb) (h10 : st.regs 10 = i) (h13 : st.regs 13 = keyP)
    (h14 : st.regs 14 = pairP) (h20 : st.regs 20 = cnt) (hmK : st.mem (keyP + i) = key)
    (hkw : key < 2 ^ w) (hkeyP : keyP + i < 2 ^ w)
    (hev : key % 2 = 0 → pairP + 2 * cnt + 1 < 2 ^ w ∧ esb + key / 2 < 2 ^ w ∧
      st.mem (esb + key / 2) < 2 ^ w ∧ cnt + 1 < 2 ^ w) :
    ∃ st₁ c, Runs w p ω brLoopCPair st .normal st₁ c ∧ c ≤ 60 ∧
      (key % 2 = 0 →
        st₁.regs = Function.update (Function.update (Function.update
          (Function.update st.regs 11 key) 21 (key / 2)) 22 (st.mem (esb + key / 2) - 1)) 20
          (cnt + 1) ∧
        st₁.mem = Function.update (Function.update st.mem (pairP + 2 * cnt) (key / 2))
          (pairP + 2 * cnt + 1) (st.mem (esb + key / 2) - 1)) ∧
      (key % 2 ≠ 0 → st₁.regs = Function.update st.regs 11 key ∧ st₁.mem = st.mem) := by
  by_cases hk : key % 2 = 0
  · obtain ⟨hb1, hb2, hb3, hb4⟩ := hev hk
    have hb3' : st.mem (st.regs 6 + key / 2) < 2 ^ w := by rw [h6]; exact hb3
    obtain ⟨st₁, c, hr, ⟨hreg, hmem⟩, hc⟩ := normal_of_fwd (w := w) (p := p) (ω := ω)
      (s := brLoopCPair) (st := st) (K := 60)
      (P := fun st₁ => st₁.regs = Function.update (Function.update (Function.update
          (Function.update st.regs 11 key) 21 (key / 2)) 22 (st.mem (esb + key / 2) - 1)) 20
          (cnt + 1) ∧
        st₁.mem = Function.update (Function.update st.mem (pairP + 2 * cnt) (key / 2))
          (pairP + 2 * cnt + 1) (st.mem (esb + key / 2) - 1)) (by
      unfold brLoopCPair
      wram_step; simp only [hmK]
      wram_run
      · simp only [normalPost_normal, h6, h14, h20, and_self]
      · wram_cost)
    exact ⟨st₁, c, hr, hc, fun _ => ⟨hreg, hmem⟩, fun h => absurd hk h⟩
  · obtain ⟨st₁, c, hr, ⟨hreg, hmem⟩, hc⟩ := normal_of_fwd (w := w) (p := p) (ω := ω)
      (s := brLoopCPair) (st := st) (K := 60)
      (P := fun st₁ => st₁.regs = Function.update st.regs 11 key ∧ st₁.mem = st.mem) (by
      unfold brLoopCPair
      wram_step; simp only [hmK]
      wram_run
      · simp only [normalPost_normal, and_self]
      · wram_cost)
    exact ⟨st₁, c, hr, hc, fun h => absurd h hk, fun _ => ⟨hreg, hmem⟩⟩

/-- **The owner part of a round of loop C.** With the key `key` in register `11` and the heap
pointer `hc` in register `19`, the owner query of the tour writes the owner `v` at `hc` and returns
the new heap pointer `hEnd`; the part copies `v` to `ownP + i` and sets register `19` to `hEnd`.
The memory `mem₂` after the query holds the tour, respects its footprint, and pays its cost. -/
theorem brLoopCOwner_runs (htour : BundleTourAt TS w vCap eCap p bTourList bTourLen bOwner)
    {st : State} {tx : htour.rep.τ} {cord : ℕ → List End} {tourH key v hc ownP i : ℕ}
    (h1 : st.regs 1 = tourH) (h10 : st.regs 10 = i) (h11 : st.regs 11 = key)
    (h15 : st.regs 15 = ownP) (h19 : st.regs 19 = hc) (htourH : tourH < 2 ^ w)
    (hk2 : key < 2 * eCap) (hkw : key < 2 ^ w) (hv : v < vCap) (hcw : hc < 2 ^ w)
    (hmem : endOfKey key ∈ cord v) (huniq : ∀ v', endOfKey key ∈ cord v' → v' = v)
    (hrep : htour.rep.rep tourH cord tx st.mem)
    (hfoot : ∀ a, htour.rep.foot tourH tx a → a < hc) (hz : ZeroFrom st.mem hc)
    (hsp : hc + TS.querySpace < 2 ^ w) (hownw : ownP + i < 2 ^ w) :
    ∃ (st₃ : State) (c : ℕ) (tx₂ : htour.rep.τ) (mem₂ : ℕ → ℕ) (hEnd : ℕ),
      Runs w p ω (brLoopCOwner bOwner) st .normal st₃ c ∧
      st₃.regs = Function.update (Function.update st.regs 12 hEnd) 19 hEnd ∧
      st₃.mem = Function.update mem₂ (ownP + i) v ∧
      htour.rep.rep tourH cord tx₂ mem₂ ∧
      htour.rep.Respects (htour.rep.foot tourH tx) hc TS.querySpace st.mem hEnd tourH tx₂ mem₂ ∧
      c + htour.rep.phi tourH tx₂ mem₂ ≤
        TS.mul * ordStoreLog eCap + 30 + htour.rep.phi tourH tx st.mem := by
  obtain ⟨body, hproc, o, st₂, c₂, tx₂, hrun, hrep₂, hv₂, -, hresp, hcost⟩ :=
    htour.owner_runs tourH key v hc cord tx st.mem st.pos ω htourH hk2 hkw hv hcw hmem huniq
      hrep hfoot hz hsp
  have hargs : evalArgs w st [.reg 1, .reg 11, .reg 19] = some [tourH, key, hc] := by
    eval_expr
  obtain ⟨st₃, c₃, hr₃, ⟨hreg, hmem₃⟩, hc₃⟩ := normal_of_fwd (w := w) (p := p) (ω := ω)
    (s := .store (.bin .add (.reg 15) (.reg 10)) (.load (.reg 19)) ;; .assign 19 (.reg 12))
    (st := { st₂ with regs := Function.update st.regs 12 o.value }) (K := 20)
    (P := fun st₃ => st₃.regs = Function.update (Function.update st.regs 12 o.value) 19
      o.value ∧ st₃.mem = Function.update st₂.mem (ownP + i) v) (by
    wram_run
    · simp only [normalPost_normal, h15, h10, h19, hv₂, and_self]
    · wram_cost)
  refine ⟨st₃, argsSize [Expr.reg 1, .reg 11, .reg 19] + c₂ + 1 + c₃ + 1, tx₂, st₂.mem, o.value,
    runs_seq_call_of_runs hargs hproc hrun hr₃, hreg, hmem₃, hrep₂, hresp, ?_⟩
  simp only [argsSize_cons, argsSize_nil, Expr.size_reg]
  omega

end

end MinCostFlow.SparseCore.Program.Restart
