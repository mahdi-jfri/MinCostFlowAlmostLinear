module

public import MinCostFlow.MinRatio.FreshLookup
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Appending one detected edge

The proof of Theorem 5.1 (pages 29–30) reports one edge at a time.
The tree returns a fresh internal name. The program reads the external
name from the inverse table and appends it to the report. This takes
one output word and constant time. The tree reset is a separate call.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Arguments are the inverse table, internal edge name, and output cursor. -/
def detectEmitBody : Stmt :=
  .store (.reg 2) (.load (.bin .add (.reg 0) (.reg 1))) ;;
  .ret (.bin .add (.reg 2) (.const 1))

/-- Appends the external name. The start and contents of the existing
report prefix are logical inputs to the contract. -/
def detectEmitContract (w report : ℕ) (written : List ℕ) : Contract where
  pre args mem := ∃ inv name heap,
    args = [inv, name, heap] ∧ heap = report + written.length ∧
    inv + name < heap ∧ heap + 1 < 2 ^ w ∧ mem (inv + name) < 2 ^ w ∧
    ListAt mem report written ∧ ZeroFrom mem heap
  post args mem ret mem' :=
    ret = args.getD 2 0 + 1 ∧
    ListAt mem' report (written ++ [mem (args.getD 0 0 + args.getD 1 0)]) ∧
    (∀ a < args.getD 2 0, mem' a = mem a) ∧ ZeroFrom mem' ret
  cost _ _ := 12

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain

/-- The append procedure consumes one word and at most 12 steps. -/
theorem detectEmit_meetsContract {w entry report : ℕ} {p : Program} (written : List ℕ)
    (hp : p.HasAt entry [detectEmitBody]) :
    MeetsContract w p entry (detectEmitContract w report written) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨inv, name, heap, rfl, heq, hin, hroom, hword, hlist, hz⟩ := hpre
  have haddr : inv + name < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold detectEmitBody
  refine runs_seq_store_le (x := heap) (v := mem (inv + name)) (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (v := heap + 1) (by eval_expr) ?_ ?_
  · refine ⟨rfl, ?_, ?_, hz.update_head _⟩
    · rw [heq]
      exact hlist.snoc _
    · intro a ha
      change a < heap at ha
      exact Function.update_of_ne (Nat.ne_of_lt ha) _ _
  · change 11 ≤ 12
    decide

/-- After appending an active internal edge, the report prefix contains
the exact external name recovered by the fresh-name bijection. -/
theorem detectEmit_external {w report inv edge heap ret fwd counter extCap intCap next : ℕ}
    {written : List ℕ} {G H : MGraph} {f g : ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (hf : FreshInv G H f g next)
    (ht : FreshTablesAt mem fwd inv counter extCap intCap f g next)
    (he : edge ∈ H.E) (hcap : edge < intCap)
    (hout : (detectEmitContract w report written).post [inv, edge, heap] mem ret mem') :
    ListAt mem' report (written ++ [g edge]) ∧ g edge ∈ G.E := by
  have hlist := hout.2.1
  change ListAt mem' report (written ++ [mem (inv + edge)]) at hlist
  rw [ht.2.2 edge hcap] at hlist
  exact ⟨hlist, (hf.hRight edge he).2⟩

end MinCostFlow.MinRatio
