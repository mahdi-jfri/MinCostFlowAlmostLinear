module

public import MinCostFlow.SparseCore.Program.BundleDllProcs
public import WordRAM.Logic

import WordRAM.Tactic

/-!
# Multi-bucket bundle initialization and restart (`BundleInitProcs`)

Implements `bundleInitSlotsStmt bDllPush bTourList` (`[tbl, tourH, k, nSlots, slotSpecPtr, nEdges,
edgeAssignPtr, nR, rPtr, h]`), which allocates fresh per-slot blocks for a list of inactive slots,
registers their disjoint edge sets in `edgeSlot` and `nE`, and scans the core rotation tour **once**
across `rPtr = R.sort (· ≤ ·)` to partition every slot's incident ends into consecutive chunks of
size `k`, matching `initBundleState` (`initBundleFor`) for all listed slots simultaneously in
`O(nSlots + nEdges + nR + (TS.mul + 1) * ∑ v ∈ R, (|cord v| + 1))` time.

Untouched active slots in the table are preserved verbatim, so the same procedure serves both
initial construction (`initBundleTree`) and partial or full bucket rebuilds (`restartBundleTree`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Register-clean body of the inner tour-end scan loop inside `bundleInitSlotsStmt`.
Reads `key := mem (hCur + 1 + t)`, looks up `edgeSlot[key / 2]`, checks `slotTouched[s]`,
opens a fresh bundle if `curTag[s] ≠ i + 1` or `size[curBun[s]] == k`, pushes `key` via `bDllPush`,
and updates `size` and `endBundle[key]`. -/
def bundleInitEndBody (bDllPush : ℕ) : Stmt :=
  .assign 24 (.load (.bin .add (.bin .add (.reg 10) (.const 1)) (.reg 23))) ;;  -- key
  .assign 25 (.bin .div (.reg 24) (.const 2)) ;;                                 -- e := key / 2
  .assign 26 (.load (.bin .add (.reg 12) (.reg 25))) ;;                          -- es := edgeSlot[e]
  .cond (.reg 26)
    (.assign 27 (.bin .sub (.reg 26) (.const 1)) ;;                              -- s := es - 1
     .assign 28 (.load (.bin .add (.reg 16) (.reg 27))) ;;                       -- flag := slotTouched[s]
     .cond (.reg 28)
       (.assign 29 (.load (.bin .add (.reg 11) (.reg 27))) ;;                    -- p := slotPtr[s]
        .assign 30 (.load (.reg 29)) ;;                                          -- sCap := mem[p]
        .assign 31 (.load (.bin .add (.reg 18) (.reg 27))) ;;                    -- tag := curTag[s]
        .cond (.bin .eq (.reg 31) (.bin .add (.reg 19) (.const 1)))
          (.assign 32 (.load (.bin .add (.reg 17) (.reg 27))) ;;                 -- bun := curBun[s]
           .assign 33 (.load (.bin .add (.bin .add (.bin .add (.reg 29) (.const 3)) (.reg 30)) (.reg 32))) ;;
           .cond (.bin .eq (.reg 33) (.reg 2))
             (.assign 32 (.load (.bin .add (.reg 29) (.const 1))) ;;             -- bun := nB
              .store (.bin .add (.reg 29) (.const 1)) (.bin .add (.reg 32) (.const 1)) ;;
              .store (.bin .add (.reg 17) (.reg 27)) (.reg 32))
             .nop)
          (.store (.bin .add (.reg 18) (.reg 27)) (.bin .add (.reg 19) (.const 1)) ;;
           .assign 32 (.load (.bin .add (.reg 29) (.const 1))) ;;                -- bun := nB
           .store (.bin .add (.reg 29) (.const 1)) (.bin .add (.reg 32) (.const 1)) ;;
           .store (.bin .add (.reg 17) (.reg 27)) (.reg 32)) ;;
        .call 34 bDllPush [.reg 14, .reg 15,
          .bin .add (.bin .add (.reg 29) (.const 3)) (.reg 32), .reg 24] ;;
        .assign 33 (.load (.bin .add (.bin .add (.bin .add (.reg 29) (.const 3)) (.reg 30)) (.reg 32))) ;;
        .store (.bin .add (.bin .add (.bin .add (.reg 29) (.const 3)) (.reg 30)) (.reg 32))
          (.bin .add (.reg 33) (.const 1)) ;;
        .store (.bin .add (.reg 13) (.reg 24)) (.reg 32))
       .nop)
    .nop

/-- `args = [tbl, tourH, nSlots, slotSpecPtr, nEdges, edgeAssignPtr, nR, rPtr, h]`:
reads the bundle cap `k` from `btBunCapAddr` of the table at `tbl`, allocates fresh slot blocks
for each `(s, bunCap)` in `slotSpecPtr`, assigns edges from `edgeAssignPtr`, runs a single tour
scan over `rPtr` calling `bTourList` once per vertex, and returns the updated heap pointer `h'`. -/
def bundleInitSlotsStmt (bDllPush bTourList : ℕ) : Stmt :=
  -- Shift arguments [2..8] to [3..9] and load slotCap (r35) and k (r2) from the table header
  .assign 9 (.reg 8) ;;                                                          -- h
  .assign 8 (.reg 7) ;;                                                          -- rPtr
  .assign 7 (.reg 6) ;;                                                          -- nR
  .assign 6 (.reg 5) ;;                                                          -- edgeAssignPtr
  .assign 5 (.reg 4) ;;                                                          -- nEdges
  .assign 4 (.reg 3) ;;                                                          -- slotSpecPtr
  .assign 3 (.reg 2) ;;                                                          -- nSlots
  .assign 35 (.load (.reg 0)) ;;                                                 -- slotCap
  .assign 2 (.load (.bin .add (.bin .add (.load (.bin .add (.reg 0) (.const 11)))
    (.bin .mul (.const 4) (.reg 35))) (.const 1))) ;;                            -- k := mem[btBunCapAddr]
  .assign 11 (.load (.bin .add (.reg 0) (.const 3))) ;;                          -- slotPtrBase
  .assign 12 (.load (.bin .add (.reg 0) (.const 4))) ;;                          -- edgeSlotBase
  .assign 13 (.load (.bin .add (.reg 0) (.const 5))) ;;                          -- endBundleBase
  .assign 14 (.load (.bin .add (.reg 0) (.const 6))) ;;                          -- endPrevBase
  .assign 15 (.load (.bin .add (.reg 0) (.const 7))) ;;                          -- endNextBase
  .assign 16 (.load (.bin .add (.reg 0) (.const 8))) ;;                          -- slotTouchedBase
  .assign 10 (.reg 9) ;;                                                         -- hCur := h
  -- Loop 1: allocate slot blocks and mark slotTouched[s] := 1
  forRange 19 (.const 0) (.reg 3)
    (.assign 20 (.load (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 19)))) ;;
     .assign 21 (.load (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 19))) (.const 1))) ;;
     .store (.reg 10) (.reg 21) ;;
     .store (.bin .add (.reg 11) (.reg 20)) (.reg 10) ;;
     .store (.bin .add (.reg 16) (.reg 20)) (.const 1) ;;
     .assign 10 (.bin .add (.reg 10) (.bin .add (.const 3) (.bin .mul (.const 6) (.reg 21))))) ;;
  -- Loop 2: assign edges to slots and count nE[s]
  forRange 19 (.const 0) (.reg 5)
    (.assign 25 (.load (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 19)))) ;;
     .assign 20 (.load (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 19))) (.const 1))) ;;
     .store (.bin .add (.reg 12) (.reg 25)) (.bin .add (.reg 20) (.const 1)) ;;
     .assign 29 (.load (.bin .add (.reg 11) (.reg 20))) ;;
     .assign 33 (.load (.bin .add (.reg 29) (.const 2))) ;;
     .store (.bin .add (.reg 29) (.const 2)) (.bin .add (.reg 33) (.const 1))) ;;
  -- Load table-resident per-slot chunking scratch arrays curBun[slotCap], curTag[slotCap]
  .assign 17 (.bin .add (.load (.bin .add (.reg 0) (.const 11))) (.reg 35)) ;;   -- curBunBase
  .assign 18 (.bin .add (.reg 17) (.reg 35)) ;;                                  -- curTagBase
  -- Loop 3: single tour scan over rPtr
  forRange 19 (.const 0) (.reg 7)
    (.assign 20 (.load (.bin .add (.reg 8) (.reg 19))) ;;                        -- v := rPtr[i]
     .call 21 bTourList [.reg 1, .reg 20, .reg 10] ;;                            -- hNext
     .assign 22 (.load (.reg 10)) ;;                                             -- len := mem[hCur]
     forRange 23 (.const 0) (.reg 22) (bundleInitEndBody bDllPush) ;;
     .assign 10 (.reg 21)) ;;                                                    -- hCur := hNext
  -- Loop 4: clear slotTouched[s] := 0, curBun[s] := 0, curTag[s] := 0
  forRange 19 (.const 0) (.reg 3)
    (.assign 20 (.load (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 19)))) ;;
     .store (.bin .add (.reg 16) (.reg 20)) (.const 0) ;;
     .store (.bin .add (.reg 17) (.reg 20)) (.const 0) ;;
     .store (.bin .add (.reg 18) (.reg 20)) (.const 0)) ;;
  .ret (.reg 10)

lemma bundleInitSlotsStmt_noRand (bDllPush bTourList : ℕ) :
    (bundleInitSlotsStmt bDllPush bTourList).NoRand := by
  trivial

/-- Pairs `(a, b)` read from `2 * n` contiguous memory words starting at `base`. -/
def bundleReadPairs (mem : ℕ → ℕ) (base n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).map fun i => (mem (base + 2 * i), mem (base + 2 * i + 1))

/-- Heap space consumed by allocating all slot blocks in `specs`. -/
def slotBlocksSpace (specs : List (ℕ × ℕ)) : ℕ :=
  (specs.map fun sb => bundleSlotBlockSize sb.2).sum

/-- Total heap space bound of `bundleInitSlotsStmt` (free of `slotCap`). -/
def bundleInitSlotsSpace (TS : BundleTourSpec) (specs : List (ℕ × ℕ))
    (cord : ℕ → List End) (rList : List ℕ) : ℕ :=
  slotBlocksSpace specs + (rList.map fun v => TS.listSpace (cord v).length).sum

/-- Total amortized step cost bound of `bundleInitSlotsStmt`. -/
def bundleInitSlotsCost (TS : BundleTourSpec) (eCap nSlots nEdges : ℕ)
    (cord : ℕ → List End) (rList : List ℕ) : ℕ :=
  125 * nSlots + 70 * nEdges + 50 * rList.length +
    ((rList.map fun v => (TS.mul * ordStoreLog eCap + 220) * ((cord v).length + 1)).sum) + 180

/-- Metadata update after allocating blocks for `specs` sequentially starting at `h`. -/
def allocSlotBlocksMeta {slotCap : ℕ} (m : BundleTableMeta slotCap) :
    List (ℕ × ℕ) → ℕ → BundleTableMeta slotCap
  | [], _ => m
  | (s, cap) :: rest, cur =>
    let m' : BundleTableMeta slotCap :=
      { slotBlocks := fun j => if j.1 = s then some (cur, cap) else m.slotBlocks j }
    allocSlotBlocksMeta m' rest (cur + bundleSlotBlockSize cap)

/-- Edge set assigned to slot `s` by a list of `(edge, slot)` assignments. -/
def slotEdgesOf (assigns : List (ℕ × ℕ)) (s : ℕ) : Finset ℕ :=
  ((assigns.filter fun p => p.2 == s).map Prod.fst).toFinset

end

/-! ## Helper lemmas for `initialChunks`, `allocSlotBlocksMeta`, and Loops 1, 2, 4 -/

public section

lemma initialChunks_length_eq {α : Type*} {k : ℕ} (xs : List α) :
    (initialChunks k xs).length = (xs.length + k - 1) / k := by
  rw [initialChunks_length, Nat.ceilDiv_eq_add_pred_div]

lemma initialChunks_snoc_length {α : Type*} {k : ℕ} (hk : 1 ≤ k) (xs : List α) (a : α) :
    (initialChunks k (xs ++ [a])).length =
      if xs.length % k = 0 then (initialChunks k xs).length + 1 else (initialChunks k xs).length := by
  rw [initialChunks_length_eq, initialChunks_length_eq, List.length_append, List.length_singleton]
  have hk0 : 0 < k := hk
  set q := xs.length / k
  set r := xs.length % k
  have hqr : k * q + r = xs.length := Nat.div_add_mod xs.length k
  have hrk : r < k := Nat.mod_lt _ hk0
  split_ifs with hmod
  · have hq : xs.length = k * q := by omega
    have h1 : (xs.length + 1 + k - 1) / k = q + 1 := by
      rw [show xs.length + 1 + k - 1 = k * (q + 1) by rw [hq, Nat.mul_add, Nat.mul_one]; omega,
        Nat.mul_div_right _ hk0]
    have h2 : (xs.length + k - 1) / k = q := by
      rw [show xs.length + k - 1 = (k - 1) + k * q by omega,
        Nat.add_mul_div_left _ _ hk0, Nat.div_eq_of_lt (by omega)]; omega
    omega
  · have h1 : (xs.length + 1 + k - 1) / k = q + 1 := by
      rw [show xs.length + 1 + k - 1 = r + k * (q + 1) by rw [Nat.mul_add, Nat.mul_one]; omega,
        Nat.add_mul_div_left _ _ hk0, Nat.div_eq_of_lt hrk]; omega
    have h2 : (xs.length + k - 1) / k = q + 1 := by
      rw [show xs.length + k - 1 = (r - 1) + k * (q + 1) by rw [Nat.mul_add, Nat.mul_one]; omega,
        Nat.add_mul_div_left _ _ hk0, Nat.div_eq_of_lt (by omega)]; omega
    omega

lemma initialChunks_getElem_length {α : Type*} {k : ℕ} (xs : List α)
    {j : ℕ} (hj : j < (initialChunks k xs).length) :
    (initialChunks k xs)[j].length = min k (xs.length - j * k) := by
  rw [initialChunks_getElem xs j hj, List.length_take, List.length_drop]

lemma initialChunks_snoc_getElem {α : Type*} {k : ℕ} (hk : 1 ≤ k) (xs : List α) (a : α)
    {j : ℕ} (hj : j < (initialChunks k (xs ++ [a])).length) :
    (initialChunks k (xs ++ [a]))[j] =
      if hjq : j = xs.length / k then
        (if h0 : xs.length % k = 0 then [a]
         else (initialChunks k xs)[j]'(by
           rw [initialChunks_snoc_length hk] at hj; simp [h0] at hj; exact hj) ++ [a])
      else
        (initialChunks k xs)[j]'(by
          rw [initialChunks_snoc_length hk] at hj
          split_ifs at hj with h0
          · have hq : (initialChunks k xs).length = xs.length / k := by
              rw [initialChunks_length_eq]
              have hdm : k * (xs.length / k) + xs.length % k = xs.length := Nat.div_add_mod xs.length k
              rw [show xs.length + k - 1 = (k - 1) + k * (xs.length / k) by omega,
                Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (by omega)]; omega
            omega
          · exact hj) := by
  have hk0 : 0 < k := hk
  have hdm : (xs.length / k) * k + xs.length % k = xs.length := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod xs.length k
  have hrk : xs.length % k < k := Nat.mod_lt _ hk0
  rw [initialChunks_getElem (xs ++ [a]) j hj]
  split_ifs with hjq hmod
  · subst hjq
    have hmul : (xs.length / k) * k = xs.length := by omega
    rw [hmul, List.drop_append_of_le_length le_rfl, List.drop_length, List.nil_append,
      show k = (k - 1) + 1 by omega, List.take_succ_cons, List.take_nil]
  · subst hjq
    have hrem : xs.length - (xs.length / k) * k = xs.length % k := by omega
    have hlt_j : xs.length / k < (initialChunks k xs).length := by
      rw [initialChunks_snoc_length hk] at hj; simp [hmod] at hj; exact hj
    rw [initialChunks_getElem xs (xs.length / k) hlt_j,
      List.drop_append, List.take_append,
      show (xs.length / k) * k - xs.length = 0 by omega, List.drop_zero,
      List.length_drop, hrem,
      show k - xs.length % k = (k - xs.length % k - 1) + 1 by omega,
      List.take_succ_cons, List.take_nil]
  · have hj_lt : j < (initialChunks k xs).length := by
      rw [initialChunks_snoc_length hk] at hj
      split_ifs at hj with h0
      · have hq : (initialChunks k xs).length = xs.length / k := by
          rw [initialChunks_length_eq]
          rw [show xs.length + k - 1 = (k - 1) + k * (xs.length / k) by rw [Nat.mul_comm]; omega,
            Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (by omega)]; omega
        omega
      · exact hj
    have hj_lt_div : j < xs.length / k := by
      rw [initialChunks_length_eq] at hj_lt
      by_cases h0 : xs.length % k = 0
      · rw [show xs.length + k - 1 = (k - 1) + k * (xs.length / k) by rw [Nat.mul_comm]; omega,
          Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (by omega)] at hj_lt; omega
      · rw [show xs.length + k - 1 = (xs.length % k - 1) + k * (xs.length / k + 1) by
            rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]; omega,
          Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (by omega)] at hj_lt; omega
    have hle : (j + 1) * k ≤ xs.length := by
      have h1 : j + 1 ≤ xs.length / k := hj_lt_div
      calc (j + 1) * k ≤ (xs.length / k) * k := Nat.mul_le_mul_right k h1
        _ ≤ xs.length := by omega
    have hjk_le : j * k ≤ xs.length := by
      have : j * k + k = (j + 1) * k := by rw [Nat.add_mul, Nat.one_mul]
      omega
    have hk_le : k ≤ xs.length - j * k := by
      have : j * k + k = (j + 1) * k := by rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [initialChunks_getElem xs j hj_lt,
      List.drop_append, show j * k - xs.length = 0 by omega, List.drop_zero,
      List.take_append_of_le_length (by rw [List.length_drop]; exact hk_le)]

lemma allocSlotBlocksMeta_append {slotCap : ℕ} (m : BundleTableMeta slotCap)
    (l₁ l₂ : List (ℕ × ℕ)) (h : ℕ) :
    allocSlotBlocksMeta m (l₁ ++ l₂) h =
      allocSlotBlocksMeta (allocSlotBlocksMeta m l₁ h) l₂ (h + slotBlocksSpace l₁) := by
  induction l₁ generalizing m h with
  | nil => simp [allocSlotBlocksMeta, slotBlocksSpace]
  | cons p ps ih =>
    rcases p with ⟨s, cap⟩
    simp only [List.cons_append, allocSlotBlocksMeta, slotBlocksSpace, List.map_cons, List.sum_cons]
    rw [ih, Nat.add_assoc]; rfl

lemma allocSlotBlocksMeta_of_not_mem {slotCap : ℕ} (m : BundleTableMeta slotCap)
    (specs : List (ℕ × ℕ)) (h : ℕ) {j : Fin slotCap} (hnot : j.1 ∉ specs.map Prod.fst) :
    (allocSlotBlocksMeta m specs h).slotBlocks j = m.slotBlocks j := by
  induction specs generalizing m h with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨s, cap⟩
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    simp only [allocSlotBlocksMeta]
    rw [ih _ _ hnot.2]
    simp [hnot.1]

lemma allocSlotBlocksMeta_mem {slotCap : ℕ} (m : BundleTableMeta slotCap)
    (specs : List (ℕ × ℕ)) (h : ℕ) (hnd : (specs.map Prod.fst).Nodup)
    {i : ℕ} (hi : i < specs.length) {j : Fin slotCap} (hj : j.1 = specs[i].1) :
    (allocSlotBlocksMeta m specs h).slotBlocks j =
      some (h + slotBlocksSpace (specs.take i), specs[i].2) := by
  induction specs generalizing m h i with
  | nil => simp at hi
  | cons p ps ih =>
    rcases p with ⟨s, cap⟩
    rw [List.map_cons, List.nodup_cons] at hnd
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hj ⊢
      simp only [allocSlotBlocksMeta, List.take_zero, slotBlocksSpace, List.map_nil, List.sum_nil,
        add_zero]
      rw [allocSlotBlocksMeta_of_not_mem _ ps _ (hj ▸ hnd.1)]
      simp [hj]
    | succ i' =>
      simp only [List.getElem_cons_succ, List.length_cons, Nat.add_lt_add_iff_right] at hi hj ⊢
      simp only [allocSlotBlocksMeta, List.take_succ_cons, slotBlocksSpace, List.map_cons,
        List.sum_cons]
      rw [ih _ _ hnd.2 hi hj, Nat.add_assoc]; rfl

/-! ### Loop 1, Loop 2, and Loop 4 Triples -/

/-- The read-only registers preserved across all four loops of `bundleInitSlotsStmt`. -/
@[expose] def BundleInitConstRegs (st : State) (tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr
    nR rPtr h slotCap eCap : ℕ) : Prop :=
  st.regs 0 = tbl ∧ st.regs 1 = tourH ∧ st.regs 2 = k ∧ st.regs 3 = nSlots ∧
  st.regs 4 = slotSpecPtr ∧ st.regs 5 = nEdges ∧ st.regs 6 = edgeAssignPtr ∧
  st.regs 7 = nR ∧ st.regs 8 = rPtr ∧ st.regs 9 = h ∧ st.regs 35 = slotCap ∧
  st.regs 11 = tbl + 12 ∧ st.regs 12 = tbl + 12 + slotCap ∧
  st.regs 13 = tbl + 12 + slotCap + eCap ∧ st.regs 14 = tbl + 12 + slotCap + 3 * eCap ∧
  st.regs 15 = tbl + 12 + slotCap + 5 * eCap ∧ st.regs 16 = tbl + 12 + slotCap + 7 * eCap

lemma BundleInitConstRegs.upd {st : State} {tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr
    nR rPtr h slotCap eCap r v : ℕ}
    (hc : BundleInitConstRegs st tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
      slotCap eCap)
    (hr : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 9 ∧
      r ≠ 11 ∧ r ≠ 12 ∧ r ≠ 13 ∧ r ≠ 14 ∧ r ≠ 15 ∧ r ≠ 16 ∧ r ≠ 35) :
    BundleInitConstRegs { st with regs := Function.update st.regs r v } tbl tourH k nSlots
      slotSpecPtr nEdges edgeAssignPtr nR rPtr h slotCap eCap := by
  rcases hc with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h35, h11, h12, h13, h14, h15, h16⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (dsimp only; rwa [Function.update_of_ne (by omega)])

/-- Loop 1 allocates fresh slot blocks for every `(s, cap)` in `specs`, writes `cap` at each block
header, sets `slotPtr[s] := ptr_s`, sets `slotTouched[s] := 1`, and advances `hCur` by
`slotBlocksSpace specs`. -/
lemma bundleInitLoop1_triple {w slotCap eCap tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr
    nR rPtr h : ℕ}
    {p : Program} {mem : ℕ → ℕ} {specs : List (ℕ × ℕ)}
    (hw16 : 16 ≤ 2 ^ w)
    (htbl_h : tbl + (14 + 7 * slotCap + 8 * eCap) ≤ h)
    (hspec_h : slotSpecPtr + 2 * nSlots ≤ h)
    (hspec_disj : slotSpecPtr + 2 * nSlots ≤ tbl ∨ tbl + (14 + 7 * slotCap + 8 * eCap) ≤ slotSpecPtr)
    (hfit : h + slotBlocksSpace specs < 2 ^ w)
    (hnSlots : specs.length = nSlots)
    (hspecs_mem : bundleReadPairs mem slotSpecPtr nSlots = specs)
    (hspecs_lt : ∀ sb ∈ specs, sb.1 < slotCap)
    (hspecs_nd : (specs.map Prod.fst).Nodup) :
    let Inv : ℕ → State → Prop := fun i st =>
      BundleInitConstRegs st tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
        slotCap eCap ∧
      st.regs 10 = h + slotBlocksSpace (specs.take i) ∧
      st.regs 19 = i ∧
      (∀ q < i, ∀ hql : q < specs.length,
        let ptr := h + slotBlocksSpace (specs.take q)
        st.mem ptr = specs[q].2 ∧
        st.mem (tbl + 12 + specs[q].1) = ptr ∧
        st.mem (tbl + 12 + slotCap + 7 * eCap + specs[q].1) = 1) ∧
      (∀ a, (∀ q < i, ∀ hql : q < specs.length,
          a ≠ h + slotBlocksSpace (specs.take q) ∧
          a ≠ tbl + 12 + specs[q].1 ∧
          a ≠ tbl + 12 + slotCap + 7 * eCap + specs[q].1) →
        st.mem a = mem a)
    Triple w p (fun st => st.mem = mem ∧
        BundleInitConstRegs st tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
          slotCap eCap ∧
        st.regs 10 = h)
      (forRange 19 (.const 0) (.reg 3)
        (.assign 20 (.load (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 19)))) ;;
         .assign 21 (.load (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 19))) (.const 1))) ;;
         .store (.reg 10) (.reg 21) ;;
         .store (.bin .add (.reg 11) (.reg 20)) (.reg 10) ;;
         .store (.bin .add (.reg 16) (.reg 20)) (.const 1) ;;
         .assign 10 (.bin .add (.reg 10) (.bin .add (.const 3) (.bin .mul (.const 6) (.reg 21))))))
      (normalPost (Inv nSlots))
      (fun _ => nSlots * 60 + 10) := by
  intro Inv
  have htake_le : ∀ i ≤ specs.length, slotBlocksSpace (specs.take i) ≤ slotBlocksSpace specs := by
    intro i _
    have hsp := List.take_append_drop i specs
    have : slotBlocksSpace specs = slotBlocksSpace (specs.take i) + slotBlocksSpace (specs.drop i) := by
      conv_lhs => rw [← hsp]
      simp [slotBlocksSpace]
    omega
  have htake_strict : ∀ {q i}, q < i → i ≤ specs.length →
      slotBlocksSpace (specs.take q) + 3 ≤ slotBlocksSpace (specs.take i) := by
    intro q i hqi hi
    have h1 : specs.take i = specs.take q ++ (specs.drop q).take (i - q) := by
      rw [← List.take_append_drop q (specs.take i), List.take_take, Nat.min_eq_left (by omega),
        List.drop_take]
    have hne : (specs.drop q).take (i - q) ≠ [] := by
      intro h0
      have := congrArg List.length h0
      simp at this; omega
    cases hcons : (specs.drop q).take (i - q) with
    | nil => exact absurd hcons hne
    | cons x xs =>
      rw [h1, hcons]
      simp [slotBlocksSpace, List.map_append, List.sum_append, bundleSlotBlockSize]; omega
  refine (Triple.forRange_const (p := p) (w := w) (r := 19) (lo := .const 0) (hi := .reg 3)
    (Inv := Inv) 50 0 nSlots (Nat.zero_le _) (by omega)
    (fun _ => by omega)
    (fun st ⟨hm, hc, r10⟩ => by
      refine ⟨by eval_expr, hc.upd (by omega), by simp [r10, slotBlocksSpace], by simp,
        fun q hq => by omega, fun a _ => by rw [hm]⟩)
    (fun _ _ _ _ hI => hI.2.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.2.2.1; eval_expr)
    (fun i _ hi => by
      wram_enter
      rcases hpre with ⟨hc, r10, r19, hdone, hfr⟩
      have hi_len : i < specs.length := by omega
      set si := specs[i].1
      set ci := specs[i].2
      set cur := h + slotBlocksSpace (specs.take i)
      have hsi_lt : si < slotCap := hspecs_lt specs[i] (List.getElem_mem hi_len)
      have hstep_sp : slotBlocksSpace (specs.take (i + 1)) =
          slotBlocksSpace (specs.take i) + (3 + 6 * ci) := by
        simp only [slotBlocksSpace]
        rw [List.take_succ_eq_append_getElem hi_len, List.map_append, List.map_singleton,
          List.sum_append, List.sum_singleton]
        rfl
      have hnext_le : slotBlocksSpace (specs.take (i + 1)) ≤ slotBlocksSpace specs :=
        htake_le (i + 1) (by omega)
      have hread : specs[i] = (mem (slotSpecPtr + 2 * i), mem (slotSpecPtr + 2 * i + 1)) := by
        have := congrArg (fun l => l[i]?) hspecs_mem
        simp only [bundleReadPairs, List.getElem?_map, List.getElem?_range hi, Option.map_some,
          List.getElem?_eq_getElem hi_len, Option.some.injEq] at this
        exact this.symm
      have hmem_si : st.mem (slotSpecPtr + 2 * i) = si := by
        rw [hfr _ fun q hq hql => by
          have hq_lt : specs[q].1 < slotCap := hspecs_lt _ (List.getElem_mem hql)
          exact ⟨by omega, by omega, by omega⟩]
        exact (Prod.mk.inj hread).1.symm
      have hmem_ci : st.mem (slotSpecPtr + 2 * i + 1) = ci := by
        rw [hfr _ fun q hq hql => by
          have hq_lt : specs[q].1 < slotCap := hspecs_lt _ (List.getElem_mem hql)
          exact ⟨by omega, by omega, by omega⟩]
        exact (Prod.mk.inj hread).2.symm
      have hr4 : st.regs 4 = slotSpecPtr := hc.2.2.2.2.1
      have hr11 : st.regs 11 = tbl + 12 := hc.2.2.2.2.2.2.2.2.2.2.2.1
      have hr16 : st.regs 16 = tbl + 12 + slotCap + 7 * eCap := hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      wram_step; dsimp only; simp only [hmem_si]
      wram_step; dsimp only; simp only [hr4, r19, hmem_ci]
      wram_run
      · simp only [r10, hr11, hr16]
        refine ⟨⟨?_, by simp [hstep_sp, cur]; omega, by simp, ?_, ?_⟩, by simp [r19]⟩
        · exact ((((hc.upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega))
        · intro q hq hql
          by_cases hqi : q = i
          · subst hqi
            dsimp only
            refine ⟨?_, ?_, ?_⟩
            · simp (disch := omega) only [Function.update_of_ne]; exact Function.update_self _ _ _
            · rw [Function.update_of_ne (by omega), Function.update_self]
            · exact Function.update_self _ _ _
          · have hqlt : q < i := by omega
            have hneq_s : specs[q].1 ≠ si := by
              intro heq
              have := hspecs_nd.getElem_inj_iff.mp (show (specs.map Prod.fst)[q]'(by simp [hql]) =
                (specs.map Prod.fst)[i]'(by simp [hi_len]) by simpa [si] using heq)
              omega
            have hq_lt_c : specs[q].1 < slotCap := hspecs_lt _ (List.getElem_mem hql)
            have hlt_ptr := htake_strict hqlt (by omega)
            have hdq := hdone q hqlt hql
            dsimp only at hdq ⊢
            refine ⟨?_, ?_, ?_⟩
            · simp (disch := omega) only [Function.update_of_ne]; exact hdq.1
            · simp (disch := omega) only [Function.update_of_ne]; exact hdq.2.1
            · simp (disch := omega) only [Function.update_of_ne]; exact hdq.2.2
        · intro a ha
          have hai := ha i (by omega) hi_len
          dsimp only
          simp (disch := omega) only [Function.update_of_ne]
          exact hfr a fun q hq hql => ha q (by omega) hql
      · wram_cost)).mono_cost fun _ _ => by simp only [Nat.sub_zero, Expr.size]; omega

/-- Loop 2 sets `edgeSlot[e] := s + 1` and increments `nE[s]` (`mem (slotPtr[s] + 2)`) for every
`(e, s)` in `assigns`. -/
lemma bundleInitLoop2_triple {w slotCap eCap tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr
    nR rPtr h hCur : ℕ}
    {p : Program} {mem : ℕ → ℕ} {assigns : List (ℕ × ℕ)} {slotPtrOf : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (htbl_h : tbl + (14 + 7 * slotCap + 8 * eCap) ≤ h)
    (hassign_h : edgeAssignPtr + 2 * nEdges ≤ h)
    (hassign_disj : edgeAssignPtr + 2 * nEdges ≤ tbl ∨
      tbl + (14 + 7 * slotCap + 8 * eCap) ≤ edgeAssignPtr)
    (hnEdges : assigns.length = nEdges)
    (hassigns_mem : bundleReadPairs mem edgeAssignPtr nEdges = assigns)
    (hassigns_lt : ∀ es ∈ assigns, es.1 < eCap ∧ es.2 < slotCap)
    (hassigns_nd : (assigns.map Prod.fst).Nodup)
    (hslotPtr_ge : ∀ s < slotCap, (∃ e, (e, s) ∈ assigns) →
      h ≤ slotPtrOf s ∧ slotPtrOf s + 3 < 2 ^ w ∧ mem (tbl + 12 + s) = slotPtrOf s ∧
      mem (slotPtrOf s + 2) = 0)
    (hslotPtr_inj : ∀ s₁ s₂, s₁ < slotCap → s₂ < slotCap →
      (∃ e, (e, s₁) ∈ assigns) → (∃ e, (e, s₂) ∈ assigns) →
      s₁ ≠ s₂ → slotPtrOf s₁ + 2 ≠ slotPtrOf s₂ + 2)
    (hnEdges_w : nEdges < 2 ^ w) :
    let cntUpTo : ℕ → ℕ → ℕ := fun i s => ((assigns.take i).filter fun x => x.2 == s).length
    let Inv : ℕ → State → Prop := fun i st =>
      BundleInitConstRegs st tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
        slotCap eCap ∧
      st.regs 10 = hCur ∧
      st.regs 19 = i ∧
      (∀ q < i, ∀ hql : q < assigns.length,
        st.mem (tbl + 12 + slotCap + assigns[q].1) = assigns[q].2 + 1) ∧
      (∀ s < slotCap, (∃ e, (e, s) ∈ assigns) → st.mem (slotPtrOf s + 2) = cntUpTo i s) ∧
      (∀ a, (∀ q < i, ∀ hql : q < assigns.length, a ≠ tbl + 12 + slotCap + assigns[q].1) →
        (∀ s < slotCap, (∃ e, (e, s) ∈ assigns) → a ≠ slotPtrOf s + 2) →
        st.mem a = mem a)
    Triple w p (fun st => st.mem = mem ∧
        BundleInitConstRegs st tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
          slotCap eCap ∧
        st.regs 10 = hCur)
      (forRange 19 (.const 0) (.reg 5)
        (.assign 25 (.load (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 19)))) ;;
         .assign 20 (.load (.bin .add (.bin .add (.reg 6) (.bin .mul (.const 2) (.reg 19))) (.const 1))) ;;
         .store (.bin .add (.reg 12) (.reg 25)) (.bin .add (.reg 20) (.const 1)) ;;
         .assign 29 (.load (.bin .add (.reg 11) (.reg 20))) ;;
         .assign 33 (.load (.bin .add (.reg 29) (.const 2))) ;;
         .store (.bin .add (.reg 29) (.const 2)) (.bin .add (.reg 33) (.const 1))))
      (normalPost (Inv nEdges))
      (fun _ => nEdges * 65 + 10) := by
  intro cntUpTo Inv
  have hcnt_le : ∀ i s, cntUpTo i s ≤ i := fun i s => by
    have h1 := List.length_filter_le (fun x : ℕ × ℕ => x.2 == s) (assigns.take i)
    have h2 : (assigns.take i).length ≤ i := List.length_take_le i assigns
    exact le_trans h1 h2
  refine (Triple.forRange_const (p := p) (w := w) (r := 19) (lo := .const 0) (hi := .reg 5)
    (Inv := Inv) 55 0 nEdges (Nat.zero_le _) (by omega)
    (fun _ => by omega)
    (fun st ⟨hm, hc, r10⟩ => by
      refine ⟨by eval_expr, hc.upd (by omega), by simp [r10], by simp, fun q hq => by omega,
        fun s hs hex => by rw [hm]; exact (hslotPtr_ge s hs hex).2.2.2,
        fun a _ _ => by rw [hm]⟩)
    (fun _ _ _ _ hI => hI.2.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.2.2.2.2.1; eval_expr)
    (fun i _ hi => by
      wram_enter
      rcases hpre with ⟨hc, r10, r19, hed, hcnt, hfr⟩
      have hi_len : i < assigns.length := by omega
      set ei := assigns[i].1
      set si := assigns[i].2
      have hlt_i := hassigns_lt assigns[i] (List.getElem_mem hi_len)
      have hex_si : ∃ e, (e, si) ∈ assigns := ⟨ei, List.getElem_mem hi_len⟩
      have hptr_si := hslotPtr_ge si hlt_i.2 hex_si
      have hread : assigns[i] = (mem (edgeAssignPtr + 2 * i), mem (edgeAssignPtr + 2 * i + 1)) := by
        have := congrArg (fun l => l[i]?) hassigns_mem
        simp only [bundleReadPairs, List.getElem?_map, List.getElem?_range hi, Option.map_some,
          List.getElem?_eq_getElem hi_len, Option.some.injEq] at this
        exact this.symm
      have hmem_ei : st.mem (edgeAssignPtr + 2 * i) = ei := by
        rw [hfr _ (fun q hq hql => by have := (hassigns_lt _ (List.getElem_mem hql)).1; omega)
          (fun s hs hex => by have := (hslotPtr_ge s hs hex).1; omega)]
        exact (Prod.mk.inj hread).1.symm
      have hmem_si : st.mem (edgeAssignPtr + 2 * i + 1) = si := by
        rw [hfr _ (fun q hq hql => by have := (hassigns_lt _ (List.getElem_mem hql)).1; omega)
          (fun s hs hex => by have := (hslotPtr_ge s hs hex).1; omega)]
        exact (Prod.mk.inj hread).2.symm
      have hmem_ptr : st.mem (tbl + 12 + si) = slotPtrOf si := by
        rw [hfr _ (fun q hq hql => by have := (hassigns_lt _ (List.getElem_mem hql)).1; omega)
          (fun s hs hex => by have := (hslotPtr_ge s hs hex).1; omega)]
        exact hptr_si.2.2.1
      have hmem_cnt : st.mem (slotPtrOf si + 2) = cntUpTo i si := hcnt si hlt_i.2 hex_si
      have hcnt_lt : cntUpTo i si + 1 < 2 ^ w := by have := hcnt_le i si; omega
      have hr6 : st.regs 6 = edgeAssignPtr := hc.2.2.2.2.2.2.1
      have hr11 : st.regs 11 = tbl + 12 := hc.2.2.2.2.2.2.2.2.2.2.2.1
      have hr12 : st.regs 12 = tbl + 12 + slotCap := hc.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hne_p_e : tbl + 12 + si ≠ tbl + 12 + slotCap + ei := by omega
      have hne_c_e : slotPtrOf si + 2 ≠ tbl + 12 + slotCap + ei := by omega
      wram_step; dsimp only; simp only [hmem_ei]
      wram_step; dsimp only; simp only [hr6, r19, hmem_si]
      wram_step; dsimp only; simp only [hr12]
      wram_step; dsimp only; simp only [hr11, Function.update_of_ne hne_p_e, hmem_ptr]
      wram_step; dsimp only; simp only [Function.update_of_ne hne_c_e, hmem_cnt]
      wram_run
      · refine ⟨⟨?_, by simp [r10], by simp, ?_, ?_, ?_⟩, by simp [r19]⟩
        · exact (((((hc.upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega)).upd (by omega))
        · intro q hq hql
          have hq_lt := (hassigns_lt _ (List.getElem_mem hql)).1
          dsimp only
          rw [Function.update_of_ne (by omega)]
          by_cases hqi : q = i
          · subst hqi; exact Function.update_self _ _ _
          · have hne_e : assigns[q].1 ≠ ei := by
              intro heq
              have := hassigns_nd.getElem_inj_iff.mp (show (assigns.map Prod.fst)[q]'(by simp [hql]) =
                (assigns.map Prod.fst)[i]'(by simp [hi_len]) by simpa [ei] using heq)
              omega
            rw [Function.update_of_ne (by omega)]
            exact hed q (by omega) hql
        · intro s hs hex
          have hstep_cnt : cntUpTo (i + 1) s =
              cntUpTo i s + if si = s then 1 else 0 := by
            simp only [cntUpTo, List.take_succ_eq_append_getElem hi_len, List.filter_append,
              List.length_append]
            by_cases hss : si = s
            · simp [si, hss]
            · simp [si, hss]
          rw [hstep_cnt]
          dsimp only
          by_cases hss : si = s
          · subst hss; simp
          · have hne_sp := hslotPtr_inj s si hs hlt_i.2 hex hex_si (Ne.symm hss)
            have hne_sp2 : slotPtrOf s + 2 ≠ tbl + 12 + slotCap + ei := by
              have := (hslotPtr_ge s hs hex).1; omega
            rw [Function.update_of_ne hne_sp, Function.update_of_ne hne_sp2]; simp only [hss, ↓reduceIte, add_zero]
            exact hcnt s hs hex
        · intro a ha1 ha2
          have hae := ha1 i (by omega) hi_len
          have has := ha2 si hlt_i.2 hex_si
          dsimp only
          rw [Function.update_of_ne has, Function.update_of_ne hae]
          exact hfr a (fun q hq hql => ha1 q (by omega) hql) ha2
      · wram_cost)).mono_cost fun _ _ => by simp only [Nat.sub_zero, Expr.size]; omega

/-- Loop 4 resets `slotTouched[s] := 0`, `curBun[s] := 0`, `curTag[s] := 0` for every `(s, _)` in
`specs`. -/
lemma bundleInitLoop4_triple {w slotCap eCap tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr
    nR rPtr h hCur : ℕ}
    {p : Program} {mem : ℕ → ℕ} {specs : List (ℕ × ℕ)}
    (hw16 : 16 ≤ 2 ^ w)
    (htbl_h : tbl + (14 + 7 * slotCap + 8 * eCap) ≤ h)
    (hspec_h : slotSpecPtr + 2 * nSlots ≤ h)
    (hspec_disj : slotSpecPtr + 2 * nSlots ≤ tbl ∨
      tbl + (14 + 7 * slotCap + 8 * eCap) ≤ slotSpecPtr)
    (hh_lt : h < 2 ^ w)
    (hnSlots : specs.length = nSlots)
    (hspecs_mem : bundleReadPairs mem slotSpecPtr nSlots = specs)
    (hspecs_lt : ∀ sb ∈ specs, sb.1 < slotCap) :
    let Inv : ℕ → State → Prop := fun i st =>
      st.regs 3 = nSlots ∧ st.regs 4 = slotSpecPtr ∧ st.regs 10 = hCur ∧
      st.regs 16 = tbl + 12 + slotCap + 7 * eCap ∧
      st.regs 17 = tbl + 12 + 4 * slotCap + 8 * eCap ∧
      st.regs 18 = tbl + 12 + 5 * slotCap + 8 * eCap ∧ st.regs 19 = i ∧
      (∀ q < i, ∀ hql : q < specs.length,
        st.mem (tbl + 12 + slotCap + 7 * eCap + specs[q].1) = 0 ∧
        st.mem (tbl + 12 + 4 * slotCap + 8 * eCap + specs[q].1) = 0 ∧
        st.mem (tbl + 12 + 5 * slotCap + 8 * eCap + specs[q].1) = 0) ∧
      (∀ a, (∀ q < i, ∀ hql : q < specs.length,
          a ≠ tbl + 12 + slotCap + 7 * eCap + specs[q].1 ∧
          a ≠ tbl + 12 + 4 * slotCap + 8 * eCap + specs[q].1 ∧
          a ≠ tbl + 12 + 5 * slotCap + 8 * eCap + specs[q].1) →
        st.mem a = mem a)
    Triple w p (fun st => st.mem = mem ∧
        BundleInitConstRegs st tbl tourH k nSlots slotSpecPtr nEdges edgeAssignPtr nR rPtr h
          slotCap eCap ∧
        st.regs 10 = hCur ∧
        st.regs 17 = tbl + 12 + 4 * slotCap + 8 * eCap ∧
        st.regs 18 = tbl + 12 + 5 * slotCap + 8 * eCap)
      (forRange 19 (.const 0) (.reg 3)
        (.assign 20 (.load (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 19)))) ;;
         .store (.bin .add (.reg 16) (.reg 20)) (.const 0) ;;
         .store (.bin .add (.reg 17) (.reg 20)) (.const 0) ;;
         .store (.bin .add (.reg 18) (.reg 20)) (.const 0)))
      (normalPost (Inv nSlots))
      (fun _ => nSlots * 55 + 10) := by
  intro Inv
  refine (Triple.forRange_const (p := p) (w := w) (r := 19) (lo := .const 0) (hi := .reg 3)
    (Inv := Inv) 45 0 nSlots (Nat.zero_le _) (by omega)
    (fun _ => by omega)
    (fun st ⟨hm, hc, r10, r17, r18⟩ => by
      refine ⟨by eval_expr, by simp [hc.2.2.2.1], by simp [hc.2.2.2.2.1], by simp [r10],
        by simp [hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2], by simp [r17], by simp [r18], by simp,
        fun q hq => by omega, fun a _ => by rw [hm]⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.1)
    (fun _ st _ _ hI => by have := hI.1; eval_expr)
    (fun i _ hi => by
      wram_enter
      rcases hpre with ⟨r3, r4, r10, r16, r17, r18, r19, hdone, hfr⟩
      have hi_len : i < specs.length := by omega
      set si := specs[i].1
      have hsi_lt : si < slotCap := hspecs_lt specs[i] (List.getElem_mem hi_len)
      have hread : specs[i] = (mem (slotSpecPtr + 2 * i), mem (slotSpecPtr + 2 * i + 1)) := by
        have := congrArg (fun l => l[i]?) hspecs_mem
        simp only [bundleReadPairs, List.getElem?_map, List.getElem?_range hi, Option.map_some,
          List.getElem?_eq_getElem hi_len, Option.some.injEq] at this
        exact this.symm
      have hmem_si : st.mem (slotSpecPtr + 2 * i) = si := by
        rw [hfr _ fun q hq hql => by
          have := hspecs_lt _ (List.getElem_mem hql); exact ⟨by omega, by omega, by omega⟩]
        exact (Prod.mk.inj hread).1.symm
      wram_step; dsimp only; simp only [hmem_si]
      wram_run
      · simp only [r16, r17, r18]
        refine ⟨⟨by simp [r3], by simp [r4], by simp [r10], by simp [r16], by simp [r17],
          by simp [r18], by simp, ?_, ?_⟩, by simp [r19]⟩
        · intro q hq hql
          have hq_lt := hspecs_lt _ (List.getElem_mem hql)
          dsimp only
          by_cases hqi : q = i
          · subst hqi
            refine ⟨?_, ?_, ?_⟩
            · simp (disch := omega) only [Function.update_of_ne]; exact Function.update_self _ _ _
            · rw [Function.update_of_ne (by omega), Function.update_self]
            · exact Function.update_self _ _ _
          · by_cases hqs : specs[q].1 = si
            · rw [hqs]
              refine ⟨?_, ?_, ?_⟩
              · simp (disch := omega) only [Function.update_of_ne]; exact Function.update_self _ _ _
              · rw [Function.update_of_ne (by omega), Function.update_self]
              · exact Function.update_self _ _ _
            · obtain ⟨d1, d2, d3⟩ := hdone q (by omega) hql
              refine ⟨?_, ?_, ?_⟩
              · simp (disch := omega) only [Function.update_of_ne]; exact d1
              · simp (disch := omega) only [Function.update_of_ne]; exact d2
              · simp (disch := omega) only [Function.update_of_ne]; exact d3
        · intro a ha
          have hai := ha i (by omega) hi_len
          dsimp only
          rw [Function.update_of_ne hai.2.2, Function.update_of_ne hai.2.1, Function.update_of_ne hai.1]
          exact hfr a fun q hq hql => ha q (by omega) hql
      · wram_cost)).mono_cost fun _ _ => by simp only [Nat.sub_zero, Expr.size]; omega

end

end MinCostFlow.SparseCore.Program
