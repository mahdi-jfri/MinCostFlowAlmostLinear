module

public import MinCostFlow.SparseCore.Program.BundleLayout
public import MinCostFlow.SparseCore.Program.BundleTourInterface

import WordRAM.Tactic
public import WordRAM.Logic

import WordRAM.Tactic

/-!
# Base procedures for the bundle manager (`BundleBaseProcs`)

Defines the five foundational deterministic Word-RAM procedures of the bundle manager
(`bundleBaseProcs`) and verifies `bundleTableInit_meetsContract`,
`bundleReadBundleOf_meetsContract`, and `bundleReadParent_runs` (the doubly-linked list helpers
`bundleDllPush_meetsContract` and `bundleDllErase_meetsContract` are verified in
`BundleDllProcs.lean`):

1. `bundleTableInitStmt` (`[slotCap, vCap, eCap, h]`): initializes the 12-word header and
   zero-initialized global arrays at `h`, returning `h + bundleTableFixedSize slotCap eCap` in
   `≤ 120` steps.
2. `bundleDllPushStmt` (`[prevBase, nextBase, headAddr, key]`): inserts `key` at the head of a
   1-indexed `IsDoublyLinkedList` in `≤ 45` steps.
3. `bundleDllEraseStmt` (`[prevBase, nextBase, headAddr, key]`): removes `key` from a 1-indexed
   `IsDoublyLinkedList` in `≤ 65` steps.
4. `bundleReadBundleOfStmt` (`[tbl, key, h]`): writes `endBundle[key]` to `h` and returns `h + 1`
   in `≤ 25` steps.
5. `bundleReadParentStmt bTourOwner` (`[tbl, tourH, s, b, h]`): writes `B.parent b` at `h` in
   amortized cost `≤ TS.mul * ordStoreLog eCap + 60`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Procedure bodies -/

/-- `args = [slotCap, vCap, eCap, k, h]`: writes the 12-word header and the bundle cap `k` at
`btBunCapAddr` of a fresh empty bundle table at `h` (using `ZeroFrom mem h` for the global and
scratch arrays) and returns `h + bundleTableFixedSize slotCap eCap`. -/
def bundleTableInitStmt : Stmt :=
  .store (.reg 4) (.reg 0) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.reg 1) ;;
  .store (.bin .add (.reg 4) (.const 2)) (.reg 2) ;;
  .assign 5 (.bin .add (.reg 4) (.const 12)) ;;
  .store (.bin .add (.reg 4) (.const 3)) (.reg 5) ;;
  .assign 6 (.bin .add (.reg 5) (.reg 0)) ;;
  .store (.bin .add (.reg 4) (.const 4)) (.reg 6) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 2)) ;;
  .store (.bin .add (.reg 4) (.const 5)) (.reg 7) ;;
  .assign 8 (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 2))) ;;
  .store (.bin .add (.reg 4) (.const 6)) (.reg 8) ;;
  .assign 9 (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 2))) ;;
  .store (.bin .add (.reg 4) (.const 7)) (.reg 9) ;;
  .assign 10 (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 2))) ;;
  .store (.bin .add (.reg 4) (.const 8)) (.reg 10) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 0)) ;;
  .store (.bin .add (.reg 4) (.const 9)) (.reg 11) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 0)) ;;
  .store (.bin .add (.reg 4) (.const 10)) (.reg 12) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 2)) ;;
  .store (.bin .add (.reg 4) (.const 11)) (.reg 13) ;;
  .assign 14 (.bin .add (.bin .add (.reg 13) (.bin .mul (.const 4) (.reg 0))) (.const 1)) ;;
  .store (.reg 14) (.reg 3) ;;
  .ret (.bin .add (.reg 14) (.const 1))

/-- `args = [prevBase, nextBase, headAddr, key]`: pushes `key` at the head of the 1-indexed
doubly-linked list at `headAddr`. -/
def bundleDllPushStmt : Stmt :=
  .assign 4 (.load (.reg 2)) ;;
  .store (.bin .add (.reg 0) (.reg 3)) (.const 0) ;;
  .store (.bin .add (.reg 1) (.reg 3)) (.reg 4) ;;
  .cond (.reg 4)
    (.store (.bin .add (.reg 0) (.bin .sub (.reg 4) (.const 1)))
      (.bin .add (.reg 3) (.const 1)))
    .nop ;;
  .store (.reg 2) (.bin .add (.reg 3) (.const 1)) ;;
  .ret (.const 0)

/-- `args = [prevBase, nextBase, headAddr, key]`: removes `key` from the 1-indexed doubly-linked
list at `headAddr` and clears `prev[key]` and `next[key]`. -/
def bundleDllEraseStmt : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.reg 3))) ;;
  .assign 5 (.load (.bin .add (.reg 1) (.reg 3))) ;;
  .cond (.reg 4)
    (.store (.bin .add (.reg 1) (.bin .sub (.reg 4) (.const 1))) (.reg 5))
    (.store (.reg 2) (.reg 5)) ;;
  .cond (.reg 5)
    (.store (.bin .add (.reg 0) (.bin .sub (.reg 5) (.const 1))) (.reg 4))
    .nop ;;
  .store (.bin .add (.reg 0) (.reg 3)) (.const 0) ;;
  .store (.bin .add (.reg 1) (.reg 3)) (.const 0) ;;
  .ret (.const 0)

/-- `args = [tbl, key, h]`: writes `endBundle[key]` at `h` and returns `h + 1`. -/
def bundleReadBundleOfStmt : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 5))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .store (.reg 2) (.reg 4) ;;
  .ret (.bin .add (.reg 2) (.const 1))

/-- `args = [tbl, tourH, s, b, h]`: writes `B.parent b` at `h` (from `storedParent[b]` if `size = 0`,
else via `bTourOwner [tourH, head[b] - 1, h]`) and returns the new heap pointer. -/
def bundleReadParentStmt (bTourOwner : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 6 (.load (.bin .add (.reg 5) (.reg 2))) ;;
  .assign 7 (.load (.reg 6)) ;;
  .assign 8 (.load (.bin .add (.bin .add (.bin .add (.reg 6) (.const 3)) (.reg 7)) (.reg 3))) ;;
  .cond (.reg 8)
    (.assign 9 (.load (.bin .add (.bin .add (.reg 6) (.const 3)) (.reg 3))) ;;
     .call 10 bTourOwner [.reg 1, .bin .sub (.reg 9) (.const 1), .reg 4] ;;
     .ret (.reg 10))
    (.assign 9 (.load (.bin .add (.bin .add (.bin .add (.reg 6) (.const 3))
        (.bin .mul (.const 2) (.reg 7))) (.reg 3))) ;;
     .store (.reg 4) (.reg 9) ;;
     .ret (.bin .add (.reg 4) (.const 1)))

def bundleBaseIdxInit : ℕ := 0
def bundleBaseIdxDllPush : ℕ := 1
def bundleBaseIdxDllErase : ℕ := 2
def bundleBaseIdxReadBundleOf : ℕ := 3
def bundleBaseIdxReadParent : ℕ := 4

def bundleBaseProcs (bTourOwner : ℕ) : List Stmt :=
  [bundleTableInitStmt, bundleDllPushStmt, bundleDllEraseStmt,
   bundleReadBundleOfStmt, bundleReadParentStmt bTourOwner]

lemma bundleBaseProcs_length (bTourOwner : ℕ) : (bundleBaseProcs bTourOwner).length = 5 := rfl

lemma bundleBaseProcs_noRand (bTourOwner : ℕ) : ∀ s ∈ bundleBaseProcs bTourOwner, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## 2. Contracts -/

def bundleTableInitContract (w slotCap vCap eCap k h : ℕ) : Contract where
  pre args mem :=
    args = [slotCap, vCap, eCap, k, h] ∧ 16 ≤ 2 ^ w ∧
    vCap < 2 ^ w ∧ k < 2 ^ w ∧ h + bundleTableFixedSize slotCap eCap < 2 ^ w ∧
    ZeroFrom mem h
  post _ mem ret mem' :=
    ret = h + bundleTableFixedSize slotCap eCap ∧
    ZeroFrom mem' ret ∧
    (∀ a < h, mem' a = mem a) ∧
    BundleTableRepAt slotCap vCap eCap h (fun _ => none) ⟨fun _ => none⟩ mem' ∧
    mem' (btBunCapAddr h slotCap eCap) = k
  cost _ _ := 180

def bundleDllPushContract (w prevBase nextBase headAddr cap key : ℕ) (L : List ℕ) : Contract where
  pre args mem :=
    args = [prevBase, nextBase, headAddr, key] ∧
    16 ≤ 2 ^ w ∧
    prevBase + cap < 2 ^ w ∧ nextBase + cap < 2 ^ w ∧
    (prevBase + cap ≤ nextBase ∨ nextBase + cap ≤ prevBase) ∧
    (headAddr < prevBase ∨ prevBase + cap ≤ headAddr) ∧
    (headAddr < nextBase ∨ nextBase + cap ≤ headAddr) ∧
    key < cap ∧ key ∉ L ∧
    IsDoublyLinkedList mem prevBase nextBase headAddr cap L
  post _ mem ret mem' :=
    ret = 0 ∧
    IsDoublyLinkedList mem' prevBase nextBase headAddr cap (key :: L) ∧
    ∀ a, a ≠ headAddr → a ≠ prevBase + key → a ≠ nextBase + key →
      (∀ x xs, L = x :: xs → a ≠ prevBase + x) →
      mem' a = mem a
  cost _ _ := 45

def bundleDllEraseContract (w prevBase nextBase headAddr cap key : ℕ) (L : List ℕ) : Contract where
  pre args mem :=
    args = [prevBase, nextBase, headAddr, key] ∧
    16 ≤ 2 ^ w ∧
    prevBase + cap < 2 ^ w ∧ nextBase + cap < 2 ^ w ∧
    (prevBase + cap ≤ nextBase ∨ nextBase + cap ≤ prevBase) ∧
    (headAddr < prevBase ∨ prevBase + cap ≤ headAddr) ∧
    (headAddr < nextBase ∨ nextBase + cap ≤ headAddr) ∧
    key ∈ L ∧
    IsDoublyLinkedList mem prevBase nextBase headAddr cap L
  post _ mem ret mem' :=
    ret = 0 ∧
    IsDoublyLinkedList mem' prevBase nextBase headAddr cap (L.erase key) ∧
    mem' (prevBase + key) = 0 ∧ mem' (nextBase + key) = 0 ∧
    ∀ a, a ≠ headAddr →
      (∀ k ∈ L, a ≠ prevBase + k ∧ a ≠ nextBase + k) →
      mem' a = mem a
  cost _ _ := 65

def bundleReadBundleOfContract (w slotCap vCap eCap tbl key h : ℕ)
    (S : BundleTableState slotCap) (m : BundleTableMeta slotCap)
    (j : Fin slotCap) (B : BundleState) : Contract where
  pre args mem :=
    args = [tbl, key, h] ∧ 16 ≤ 2 ^ w ∧
    tbl + bundleTableFixedSize slotCap eCap < 2 ^ w ∧
    h + 1 < 2 ^ w ∧ ZeroFrom mem h ∧
    (∀ a, bundleTableFoot eCap tbl m a → a < h) ∧
    BundleTableRepAt slotCap vCap eCap tbl S m mem ∧
    S j = some B ∧ (endOfKey key).1 ∈ B.edges
  post _ mem ret mem' :=
    ret = h + 1 ∧ ZeroFrom mem' ret ∧
    mem' h = B.bundleOf (endOfKey key) ∧
    (∀ a < h, mem' a = mem a)
  cost _ _ := 30

end

/-! ## 3. Shared flat-state execution combinators -/

public section

lemma bundle_runs_seq_store {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {ae ve : Expr} {s₂ : Stmt} {mem : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ}
    {a v c₂ : ℕ} {o : Outcome} {st' : State}
    (ha : ae.eval w ⟨mem, regs, pos⟩ = some a)
    (hv : ve.eval w ⟨mem, regs, pos⟩ = some v)
    (h2 : Runs w p ω s₂ ⟨Function.update mem a v, regs, pos⟩ o st' c₂) :
    Runs w p ω (.store ae ve ;; s₂) ⟨mem, regs, pos⟩ o st' ((ae.size + ve.size + 1) + c₂ + 1) := by
  have h1 : Runs w p ω (.store ae ve) ⟨mem, regs, pos⟩ .normal
      ⟨Function.update mem a v, regs, pos⟩ (ae.size + ve.size + 1) :=
    runs_store_iff.mpr ⟨a, v, ha, hv, rfl, rfl, rfl⟩
  exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, h1, h2, rfl⟩)

lemma bundle_runs_seq_assign {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {r : ℕ} {e : Expr} {s₂ : Stmt} {mem : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ}
    {v c₂ : ℕ} {o : Outcome} {st' : State}
    (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (h2 : Runs w p ω s₂ ⟨mem, Function.update regs r v, pos⟩ o st' c₂) :
    Runs w p ω (.assign r e ;; s₂) ⟨mem, regs, pos⟩ o st' ((e.size + 1) + c₂ + 1) := by
  have h1 : Runs w p ω (.assign r e) ⟨mem, regs, pos⟩ .normal
      ⟨mem, Function.update regs r v, pos⟩ (e.size + 1) :=
    runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩
  exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, h1, h2, rfl⟩)

lemma bundle_runs_ret {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {st : State} {v : ℕ} (he : e.eval w st = some v) :
    Runs w p ω (.ret e) st (.returned v) st (e.size + 1) :=
  runs_ret_iff.mpr ⟨v, he, rfl, rfl, rfl⟩

lemma bundle_runs_seq_normal {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ : Stmt} {st st₁ st₂ : State} {o : Outcome} {c₁ c₂ : ℕ}
    (h1 : Runs w p ω s₁ st .normal st₁ c₁)
    (h2 : Runs w p ω s₂ st₁ o st₂ c₂) :
    Runs w p ω (s₁ ;; s₂) st o st₂ (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h1, h2, rfl⟩)

lemma bundle_runs_seq_store_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {ae ve : Expr} {s₂ : Stmt} {mem : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ}
    {a v k T : ℕ} {o : Outcome} {st' : State}
    (ha : ae.eval w ⟨mem, regs, pos⟩ = some a)
    (hv : ve.eval w ⟨mem, regs, pos⟩ = some v)
    (h2 : ∃ c₂, Runs w p ω s₂ ⟨Function.update mem a v, regs, pos⟩ o st' c₂ ∧
      (k + (ae.size + ve.size + 2)) + c₂ ≤ T) :
    ∃ c, Runs w p ω (.store ae ve ;; s₂) ⟨mem, regs, pos⟩ o st' c ∧ k + c ≤ T := by
  obtain ⟨c₂, hr, hc⟩ := h2
  exact ⟨(ae.size + ve.size + 1) + c₂ + 1, bundle_runs_seq_store ha hv hr, by omega⟩

lemma bundle_runs_seq_assign_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {r : ℕ} {e : Expr} {s₂ : Stmt} {mem : ℕ → ℕ} {regs : ℕ → ℕ} {pos : ℕ}
    {v k T : ℕ} {o : Outcome} {st' : State}
    (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (h2 : ∃ c₂, Runs w p ω s₂ ⟨mem, Function.update regs r v, pos⟩ o st' c₂ ∧
      (k + (e.size + 2)) + c₂ ≤ T) :
    ∃ c, Runs w p ω (.assign r e ;; s₂) ⟨mem, regs, pos⟩ o st' c ∧ k + c ≤ T := by
  obtain ⟨c₂, hr, hc⟩ := h2
  exact ⟨(e.size + 1) + c₂ + 1, bundle_runs_seq_assign he hr, by omega⟩

lemma bundle_runs_ret_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {st : State} {v k T : ℕ}
    (he : e.eval w st = some v) (hk : k + (e.size + 1) ≤ T) :
    ∃ c, Runs w p ω (.ret e) st (.returned v) st c ∧ k + c ≤ T :=
  ⟨e.size + 1, bundle_runs_ret he, hk⟩

lemma bundle_runs_seq_normal_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ : Stmt} {st st₁ st₂ : State} {o : Outcome} {c₁ k T : ℕ}
    (h1 : Runs w p ω s₁ st .normal st₁ c₁)
    (h2 : ∃ c₂, Runs w p ω s₂ st₁ o st₂ c₂ ∧ (k + (c₁ + 1)) + c₂ ≤ T) :
    ∃ c, Runs w p ω (s₁ ;; s₂) st o st₂ c ∧ k + c ≤ T := by
  obtain ⟨c₂, hr, hc⟩ := h2
  exact ⟨c₁ + c₂ + 1, bundle_runs_seq_normal h1 hr, by omega⟩

lemma bundle_runs_cond_true_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {s₁ s₂ : Stmt} {st st' : State} {o : Outcome} {v k T : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h1 : ∃ c₁, Runs w p ω s₁ st o st' c₁ ∧ (k + (e.size + 1)) + c₁ ≤ T) :
    ∃ c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ k + c ≤ T := by
  obtain ⟨c₁, hr, hc⟩ := h1
  refine ⟨e.size + c₁ + 1, runs_cond_iff.mpr ⟨v, c₁, he, ?_, rfl⟩, by omega⟩
  simpa [hv] using hr

lemma bundle_runs_cond_false_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {e : Expr} {s₁ s₂ : Stmt} {st st' : State} {o : Outcome} {k T : ℕ}
    (he : e.eval w st = some 0)
    (h2 : ∃ c₂, Runs w p ω s₂ st o st' c₂ ∧ (k + (e.size + 1)) + c₂ ≤ T) :
    ∃ c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ k + c ≤ T := by
  obtain ⟨c₂, hr, hc⟩ := h2
  refine ⟨e.size + c₂ + 1, runs_cond_iff.mpr ⟨0, c₂, he, ?_, rfl⟩, by omega⟩
  simpa using hr

lemma bundle_runs_seq_normal_bound {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ : Stmt} {st st₁ st₂ : State} {o : Outcome} {b₁ k T : ℕ}
    (h1 : ∃ c₁, Runs w p ω s₁ st .normal st₁ c₁ ∧ c₁ ≤ b₁)
    (h2 : ∃ c₂, Runs w p ω s₂ st₁ o st₂ c₂ ∧ (k + (b₁ + 1)) + c₂ ≤ T) :
    ∃ c, Runs w p ω (s₁ ;; s₂) st o st₂ c ∧ k + c ≤ T := by
  obtain ⟨c₁, hr₁, hc₁⟩ := h1
  obtain ⟨c₂, hr₂, hc₂⟩ := h2
  exact ⟨c₁ + c₂ + 1, bundle_runs_seq_normal hr₁ hr₂, by omega⟩

/-! ## 4. Verification of `bundleTableInit`, `bundleReadBundleOf`, `bundleReadParent` -/

/-- Verification of `bundleTableInitStmt`. -/
theorem bundleTableInit_meetsContract {w slotCap vCap eCap k h : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [bundleTableInitStmt]) :
    MeetsContract w p b (bundleTableInitContract w slotCap vCap eCap k h) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨rfl, hw16, hvCap, hk_w, hfit, hzero⟩
  have hfit' : h + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := hfit
  refine runs_start_le ?_
  dsimp only [bundleTableInitStmt, startState]
  wram_run
  · dsimp only [bundleTableInitContract, Outcome.value]
    have hka : h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap + slotCap + slotCap +
        eCap + 4 * slotCap + 1 = btBunCapAddr h slotCap eCap := by
      unfold btBunCapAddr; omega
    have hm_out : ∀ a, (a < h ∨ h + 12 ≤ a) → a ≠ btBunCapAddr h slotCap eCap →
        Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update mem h slotCap) (h + 1) vCap) (h + 2) eCap)
        (h + 3) (h + 12)) (h + 4) (h + 12 + slotCap)) (h + 5) (h + 12 + slotCap + eCap))
        (h + 6) (h + 12 + slotCap + eCap + 2 * eCap))
        (h + 7) (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap))
        (h + 8) (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap))
        (h + 9) (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap + slotCap))
        (h + 10) (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap + slotCap + slotCap))
        (h + 11) (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap + slotCap + slotCap + eCap))
        (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap + slotCap + slotCap + eCap + 4 * slotCap + 1) k
        a = mem a := fun a ha hne => by
      rw [hka]
      simp (disch := omega) only [Function.update_of_ne]
    have hm_zero : ∀ a, h + 12 ≤ a → a ≠ btBunCapAddr h slotCap eCap →
        Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update mem h slotCap) (h + 1) vCap) (h + 2) eCap)
        (h + 3) (h + 12)) (h + 4) (h + 12 + slotCap)) (h + 5) (h + 12 + slotCap + eCap))
        (h + 6) (h + 12 + slotCap + eCap + 2 * eCap))
        (h + 7) (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap))
        (h + 8) (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap))
        (h + 9) (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap + slotCap))
        (h + 10) (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap + slotCap + slotCap))
        (h + 11) (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap + slotCap + slotCap + eCap))
        (h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap + slotCap + slotCap + eCap + 4 * slotCap + 1) k
        a = 0 := fun a ha hne => (hm_out a (Or.inr ha) hne).trans (hzero a (by omega))
    have hend : h + 12 + slotCap + eCap + 2 * eCap + 2 * eCap + 2 * eCap + slotCap + slotCap +
        eCap + 4 * slotCap + 1 + 1 = h + bundleTableFixedSize slotCap eCap := by
      unfold bundleTableFixedSize; omega
    refine ⟨hend,
      fun a ha => hm_zero a (by omega) (by unfold btBunCapAddr; omega),
      fun a ha => hm_out a (Or.inl ha) (by unfold btBunCapAddr; omega),
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        fun _ _ _ _ _ h1 => (by cases h1),
        fun e he => ⟨fun _ _ h1 => (by cases h1),
          fun _ => hm_zero _ (by unfold btEdgeSlotBase; omega) (by unfold btEdgeSlotBase btBunCapAddr; omega)⟩,
        fun _ _ h1 => (by cases h1),
        fun j => hm_zero _ (by unfold btSlotPtrBase; omega) (by unfold btSlotPtrBase btBunCapAddr; omega),
        fun _ _ _ _ _ _ _ h1 _ => (by cases h1),
        fun s hs => ⟨hm_zero _ (by unfold btSlotTouchedBase; omega) (by unfold btSlotTouchedBase btBunCapAddr; omega),
          hm_zero _ (by unfold btSlotDelHeadBase; omega) (by unfold btSlotDelHeadBase btBunCapAddr; omega),
          hm_zero _ (by unfold btSlotCandHeadBase; omega) (by unfold btSlotCandHeadBase btBunCapAddr; omega)⟩,
        fun e he => hm_zero _ (by unfold btSlotDelNextBase; omega) (by unfold btSlotDelNextBase btBunCapAddr; omega),
        fun s hs => ⟨hm_zero _ (by unfold btCurBunBase; omega) (by unfold btCurBunBase btBunCapAddr; omega),
          hm_zero _ (by unfold btCurTagBase; omega) (by unfold btCurTagBase btBunCapAddr; omega)⟩⟩,
      by rw [hka]; simp⟩
    · dsimp only [btOffSlotCap]; simp (disch := omega) only [Function.update_of_ne]; simp
    · dsimp only [btOffVCap]; simp (disch := omega) only [Function.update_of_ne]; simp
    · dsimp only [btOffECap]; simp (disch := omega) only [Function.update_of_ne]; simp
    · dsimp only [btOffSlotPtr, btSlotPtrBase]
      simp (disch := omega) only [Function.update_of_ne]; simp
    · dsimp only [btOffEdgeSlot, btEdgeSlotBase]
      simp (disch := omega) only [Function.update_of_ne]; simp
    · dsimp only [btOffEndBundle, btEndBundleBase]
      simp (disch := omega) only [Function.update_of_ne]; simp
    · dsimp only [btOffEndPrev, btEndPrevBase]
      simp (disch := omega) only [Function.update_of_ne]; simp; omega
    · dsimp only [btOffEndNext, btEndNextBase]
      simp (disch := omega) only [Function.update_of_ne]; simp; omega
    · dsimp only [btOffSlotTouched, btSlotTouchedBase]
      simp (disch := omega) only [Function.update_of_ne]; simp; omega
    · dsimp only [btOffSlotDelHead, btSlotDelHeadBase]
      simp (disch := omega) only [Function.update_of_ne]; simp; omega
    · dsimp only [btOffSlotDelNext, btSlotDelNextBase]
      simp (disch := omega) only [Function.update_of_ne]; simp; omega
    · dsimp only [btOffSlotCandHead, btSlotCandHeadBase]
      simp (disch := omega) only [Function.update_of_ne]; simp; omega
  · dsimp only [bundleTableInitContract]; wram_cost

/-- Verification of `bundleReadBundleOfStmt`. -/
theorem bundleReadBundleOf_meetsContract {w slotCap vCap eCap tbl key h : ℕ}
    {S : BundleTableState slotCap} {m : BundleTableMeta slotCap}
    {j : Fin slotCap} {B : BundleState} {p : Program} {b : ℕ}
    (hp : p.HasAt b [bundleReadBundleOfStmt]) :
    MeetsContract w p b (bundleReadBundleOfContract w slotCap vCap eCap tbl key h S m j B) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨rfl, hw16, htblFit, hh1, hzero, hfoot, hrep, hSj, heB⟩
  have hslot := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
  rw [hSj] at hslot
  cases hm : m.slotBlocks j with
  | none => rw [hm] at hslot; exact False.elim hslot
  | some pb =>
    rcases pb with ⟨ptr, bunCap⟩
    rw [hm] at hslot
    obtain ⟨nB, _, hnB, hE, hbo, _, _, _, _, _, _, _, _⟩ := hslot.2.1
    have hptr_h : ptr + bundleSlotBlockSize bunCap ≤ h := by
      have hlast : bundleTableFoot eCap tbl m (ptr + (bundleSlotBlockSize bunCap - 1)) :=
        Or.inr ⟨j, ptr, bunCap, hm, Nat.le_add_right _ _, by unfold bundleSlotBlockSize; omega⟩
      have hlt := hfoot _ hlast
      unfold bundleSlotBlockSize at hlt ⊢; omega
    have he_lt : (endOfKey key).1 < eCap := hE _ heB
    have hkey_lt : key < 2 * eCap := by
      have hk := bundle_endKey_endOfKey key
      cases hside : (endOfKey key).2 <;> simp [endKey, hside] at hk <;> omega
    have hendB_eq : mem (tbl + 5) = tbl + 12 + slotCap + eCap := hrep.2.2.2.2.2.1
    have hval_eq : mem (tbl + 12 + slotCap + eCap + key) = B.bundleOf (endOfKey key) := by
      have h' := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j B hSj (endOfKey key) ((mem_edgeEnds _ _).mpr heB)
      rwa [bundle_endKey_endOfKey] at h'
    have hval_lt : B.bundleOf (endOfKey key) < 2 ^ w := by
      have hblt := hbo (endOfKey key) ((mem_edgeEnds _ _).mpr heB)
      unfold bundleSlotBlockSize at hptr_h; omega
    have htblFit' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htblFit
    refine runs_start_le ?_
    dsimp only [bundleReadBundleOfStmt, startState]
    wram_step; simp only [hendB_eq]
    wram_step; simp only [hval_eq]
    wram_run
    · dsimp only [bundleReadBundleOfContract, Outcome.value]
      refine ⟨rfl, fun a ha => ?_, by simp, fun a ha => ?_⟩
      · rw [Function.update_of_ne (by omega)]; exact hzero a (by omega)
      · exact Function.update_of_ne (by omega) _ _
    · dsimp only [bundleReadBundleOfContract]; wram_cost

/-- Verification of `bundleReadParentStmt`. -/
theorem bundleReadParent_runs {TS : BundleTourSpec} {w slotCap vCap eCap : ℕ} {p : Program}
    {idxList idxLen idxOwner bProc : ℕ}
    (htour : BundleTourAt TS w vCap eCap p idxList idxLen idxOwner)
    (hp : p.HasAt bProc [bundleReadParentStmt idxOwner])
    {tbl tourH bun h : ℕ} {j : Fin slotCap} {S : BundleTableState slotCap}
    {m : BundleTableMeta slotCap} {B : BundleState} {cord : ℕ → List End}
    {tx : htour.rep.τ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hvCap : vCap < 2 ^ w)
    (htblFit : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (htourH : tourH < 2 ^ w)
    (hhSpace : h + TS.querySpace < 2 ^ w)
    (hzero : ZeroFrom mem h)
    (hfootB : ∀ a, bundleTableFoot eCap tbl m a → a < h)
    (hfootT : ∀ a, htour.rep.foot tourH tx a → a < h)
    (hdisjBT : ∀ a, bundleTableFoot eCap tbl m a → ¬ htour.rep.foot tourH tx a)
    (hrepB : BundleTableRepAt slotCap vCap eCap tbl S m mem)
    (hrepT : htour.rep.rep tourH cord tx mem)
    (hmatch : BundleTableCordMatch vCap S cord)
    (hSj : S j = some B) (hbun : bun ∈ B.vertices) :
    ∃ body, p.procs[bProc]? = some body ∧ ∃ o st' c tx',
      Runs w p ω body (startState [tbl, tourH, j.1, bun, h] mem pos) o st' c ∧
      BundleTableRepAt slotCap vCap eCap tbl S m st'.mem ∧
      htour.rep.rep tourH cord tx' st'.mem ∧
      st'.mem h = B.parent bun ∧
      h + 1 ≤ o.value ∧ o.value ≤ h + TS.querySpace ∧ ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ htour.rep.foot tourH tx a → st'.mem a = mem a) ∧
      (∀ a, htour.rep.foot tourH tx' a → htour.rep.foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
      c + htour.rep.phi tourH tx' st'.mem ≤
        TS.mul * ordStoreLog eCap + 60 + htour.rep.phi tourH tx mem := by
  have hproc : p.procs[bProc]? = some (bundleReadParentStmt idxOwner) := hp.head
  have hslot := hrepB.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
  rw [hSj] at hslot
  cases hm : m.slotBlocks j with
  | none => rw [hm] at hslot; exact False.elim hslot
  | some pb =>
    rcases pb with ⟨ptr, bunCap⟩
    rw [hm] at hslot
    obtain ⟨nB, hBV, hnB, hBE, _, _, hcapEq, _, _, hdll, hpar0, _, _⟩ := hslot.2.1
    have hbun_lt : bun < nB := Finset.mem_range.mp (hBV ▸ hbun)
    have hbun_cap : bun < bunCap := lt_of_lt_of_le hbun_lt hnB
    have hj_lt : j.1 < slotCap := j.isLt
    have hptr_h : ptr + (3 + 6 * bunCap) ≤ h := by
      have hlast : bundleTableFoot eCap tbl m (ptr + (bundleSlotBlockSize bunCap - 1)) :=
        Or.inr ⟨j, ptr, bunCap, hm, Nat.le_add_right _ _, by unfold bundleSlotBlockSize; omega⟩
      have hlt := hfootB _ hlast
      unfold bundleSlotBlockSize at hlt; omega
    have htblFit' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htblFit
    have hqge := TS.querySpace_ge
    have hslotPtr_eq : mem (tbl + 3) = tbl + 12 := hrepB.2.2.2.1
    have hptr_eq : mem (tbl + 12 + j.1) = ptr := hslot.1
    have hcapEq' : mem ptr = bunCap := by simpa [bsOffBunCap] using hcapEq
    obtain ⟨L, hL, hsz_eq, hLmem⟩ := hdll bun hbun_lt
    have hsz_eq' : mem (ptr + 3 + bunCap + bun) = L.length := hsz_eq
    have hsz_lt : L.length < 2 ^ w := by
      have hsub : L.toFinset ⊆ Finset.range (2 * eCap) := fun k hk =>
        Finset.mem_range.mpr (hL.2.1 k (List.mem_toFinset.mp hk))
      have hle : L.length ≤ 2 * eCap := by
        rw [← List.toFinset_card_of_nodup hL.1]
        exact (Finset.card_le_card hsub).trans (by simp)
      omega
    cases hLcase : L with
    | nil =>
      have hempty : B.ends bun = ∅ := by
        ext x
        simp only [Finset.notMem_empty, iff_false]
        intro hx
        have := (hLmem (endKey x)).mpr (by rwa [bundle_endOfKey_endKey])
        rw [hLcase] at this; cases this
      have hpar_eq : mem (ptr + 3 + 2 * bunCap + bun) = B.parent bun := hpar0 bun hbun_lt hempty
      have hpar_lt : B.parent bun < 2 ^ w := lt_trans (hmatch.2 j B hSj bun hbun).1 hvCap
      have hsz0 : mem (ptr + 3 + bunCap + bun) = 0 := by simpa [hLcase] using hsz_eq'
      have hres : ∃ o st' c, Runs w p ω (bundleReadParentStmt idxOwner)
          (startState [tbl, tourH, j.1, bun, h] mem pos) o st' c ∧
          (BundleTableRepAt slotCap vCap eCap tbl S m st'.mem ∧
           htour.rep.rep tourH cord tx st'.mem ∧
           st'.mem h = B.parent bun ∧
           h + 1 ≤ o.value ∧ o.value ≤ h + TS.querySpace ∧ ZeroFrom st'.mem o.value ∧
           (∀ a < h, ¬ htour.rep.foot tourH tx a → st'.mem a = mem a) ∧
           (∀ a, htour.rep.foot tourH tx a → htour.rep.foot tourH tx a ∨ (h ≤ a ∧ a < o.value)) ∧
           htour.rep.phi tourH tx st'.mem = htour.rep.phi tourH tx mem) ∧
          c ≤ 60 := by
        refine runs_start_le ?_
        dsimp only [bundleReadParentStmt, startState]
        wram_step; simp only [hslotPtr_eq]
        wram_step; simp only [hptr_eq]
        wram_step; simp only [hcapEq']
        wram_step; simp only [hsz0]
        wram_step
        wram_step; simp only [hpar_eq]
        wram_run
        · dsimp only [Outcome.value]
          refine ⟨hrepB.of_agree fun a ha => (Function.update_of_ne (ne_of_lt (hfootB a ha)) _ _).symm,
            (htour.rep_local tourH cord tx mem _
              (fun a ha => (Function.update_of_ne (ne_of_lt (hfootT a ha)) _ _).symm)).1 hrepT,
            by simp, le_rfl, by omega,
            fun a ha => by rw [Function.update_of_ne (by omega)]; exact hzero a (by omega),
            fun a ha _ => Function.update_of_ne (by omega) _ _,
            fun a ha => Or.inl ha,
            ((htour.rep_local tourH cord tx mem _
              (fun a ha => (Function.update_of_ne (ne_of_lt (hfootT a ha)) _ _).symm)).2).symm⟩
        · wram_cost
      obtain ⟨o, st', c, hrun, hpost, hc⟩ := hres
      exact ⟨_, hproc, o, st', c, tx, hrun, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1,
        hpost.2.2.2.2.1, hpost.2.2.2.2.2.1, hpost.2.2.2.2.2.2.1, hpost.2.2.2.2.2.2.2.1,
        by rw [hpost.2.2.2.2.2.2.2.2]; omega⟩
    | cons k₀ ks =>
      have hk0_mem : k₀ ∈ L := hLcase ▸ List.mem_cons_self
      have hk0_lt : k₀ < 2 * eCap := hL.2.1 k₀ hk0_mem
      have hk0_w : k₀ < 2 ^ w := by omega
      have hhd_eq : mem (ptr + 3 + bun) = k₀ + 1 := by simpa [bsHeadBase, hLcase] using hL.2.2.1
      have hsz_pos : mem (ptr + 3 + bunCap + bun) = ks.length + 1 := by simpa [hLcase] using hsz_eq'
      have hsz_pos_w : ks.length + 1 < 2 ^ w := by simpa [hLcase] using hsz_lt
      have hx_in : endOfKey k₀ ∈ B.ends bun := (hLmem k₀).mp hk0_mem
      have hpar_lt_v : B.parent bun < vCap := (hmatch.2 j B hSj bun hbun).1
      have hx_cord : endOfKey k₀ ∈ cord (B.parent bun) := (hmatch.2 j B hSj bun hbun).2 _ hx_in
      have hx_uniq : ∀ v', endOfKey k₀ ∈ cord v' → v' = B.parent bun :=
        fun v' hv' => hmatch.1 v' (B.parent bun) (endOfKey k₀) hv' hx_cord
      obtain ⟨tbody, htproc, tout, tst', tc, tx', htrun, htrep', htval, hto1, htresp, htcost⟩ :=
        htour.owner_runs tourH k₀ (B.parent bun) h cord tx mem pos ω
          htourH hk0_lt hk0_w hpar_lt_v (by omega) hx_cord hx_uniq hrepT hfootT hzero hhSpace
      have hto_lt : tout.value < 2 ^ w := by have := htresp.2.1; omega
      have hres : ∃ o st' c, Runs w p ω (bundleReadParentStmt idxOwner)
          (startState [tbl, tourH, j.1, bun, h] mem pos) o st' c ∧
          (o = .returned tout.value ∧ st'.mem = tst'.mem) ∧
          c ≤ tc + 60 := by
        refine runs_start_le ?_
        dsimp only [bundleReadParentStmt, startState]
        wram_step; simp only [hslotPtr_eq]
        wram_step; simp only [hptr_eq]
        wram_step; simp only [hcapEq']
        wram_step; simp only [hsz_pos]
        wram_step
        wram_step; simp only [hhd_eq]
        have hsub : k₀ + 1 - 1 = k₀ := by omega
        refine ⟨.returned tout.value,
          { mem := tst'.mem, regs := Function.update _ 10 tout.value, pos := tst'.pos }, _,
          bundle_runs_seq_normal
            (runs_call_iff.mpr ⟨[tourH, k₀, h], tbody, tout, tst', tc, ?_, htproc, htrun, rfl, rfl, rfl⟩)
            (runs_ret_iff.mpr ⟨tout.value, by simp [Expr.eval], rfl, rfl, rfl⟩),
          ⟨rfl, rfl⟩, by wram_cost⟩
        simp only [evalArgs, Expr.eval, BinOp.eval, Function.update, List.getD]
        simp [show 1 < 2 ^ w by omega, hsub, show k₀ < 2 ^ w by omega]
      obtain ⟨o, st', c, hrun, ⟨rfl, hstmem⟩, hc⟩ := hres
      refine ⟨_, hproc, .returned tout.value, st', c, tx', hrun, ?_, hstmem ▸ htrep',
        hstmem ▸ htval, hto1, htresp.2.1, hstmem ▸ htresp.2.2.1,
        fun a ha hnt => hstmem ▸ htresp.2.2.2.1 a ha hnt, htresp.2.2.2.2,
        by rw [hstmem]; omega⟩
      rw [hstmem]
      exact hrepB.of_agree fun a ha => (htresp.2.2.2.1 a (hfootB a ha) (hdisjBT a ha)).symm

end

end MinCostFlow.SparseCore.Program
