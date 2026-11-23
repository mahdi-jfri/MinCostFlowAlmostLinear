module

public import MinCostFlow.MinRatio.DetectReserved
import WordRAM.Tactic

/-!
# Reporting the edge at a ready slot

The reporting step in the proof of Theorem 5.1 (pages 29–30) converts
a ready tree slot to the original edge name and appends it to the
reserved output list. The name lookup and append leave the tree
records available for the subsequent point reset.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Arguments are the slot-to-name table, fresh inverse table, slot,
and output cursor. Return the next output cursor. -/
def detectSlotReportBody (lookup emit : ℕ) : Stmt :=
  .call 4 lookup [.reg 0, .reg 2] ;;
  .call 5 emit [.reg 1, .reg 4, .reg 3] ;;
  .ret (.reg 5)

/-- The two inverse reads determine the appended word. Only the
output cell can change, and the heap remains available to tree calls. -/
def detectSlotReportContract (w report heap : ℕ) (written : List ℕ) : Contract where
  pre args mem := ∃ names inverse slot cursor, args = [names, inverse, slot, cursor] ∧
    cursor = report + written.length ∧ names + slot < cursor ∧
    inverse + mem (names + slot) < cursor ∧ cursor < heap ∧ heap < 2 ^ w ∧
    mem (inverse + mem (names + slot)) < 2 ^ w ∧ ListAt mem report written ∧ ZeroFrom mem heap
  post args mem ret mem' :=
    ret = args.getD 3 0 + 1 ∧
    ListAt mem' report (written ++ [mem (args.getD 1 0 + mem (args.getD 0 0 + args.getD 2 0))]) ∧
    (∀ x, x ≠ args.getD 3 0 → mem' x = mem x) ∧ ZeroFrom mem' heap
  cost _ _ := 30

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain

/-- Resolving and appending a ready slot takes at most 30 steps. -/
theorem detectSlotReport_meetsContract {w entry lookup emit report heap : ℕ} {p : Program}
    (written : List ℕ) (hp : p.HasAt entry [detectSlotReportBody lookup emit])
    (hl : MeetsContract w p lookup (freshLookupContract w))
    (he : MeetsContract w p emit (detectEmitReservedContract w report heap written)) :
    MeetsContract w p entry (detectSlotReportContract w report heap written) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨names, inverse, slot, cursor, rfl, hcursor, hname, hinv, hlt, hheap, hval, hlist, hz⟩ := hpre
  have hnw := hwords names (by simp)
  have hiw := hwords inverse (by simp)
  have hsw := hwords slot (by simp)
  have hcw := hwords cursor (by simp)
  have hmid : mem (names + slot) < 2 ^ w := by omega
  apply runs_start_le
  unfold detectSlotReportBody
  refine runs_seq_call_le hl (vs := [names, slot]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨names, slot, rfl, by omega, hmid⟩
  · intro edge mem₁ pos₁ hpost
    obtain ⟨hedge, hmem⟩ := hpost
    change mem₁ = mem at hmem
    subst mem₁
    change edge = mem (names + slot) at hedge
    have hew : edge < 2 ^ w := by rwa [hedge]
    refine runs_seq_call_le he (vs := [inverse, edge, cursor]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨inverse, edge, cursor, rfl, hcursor, by rwa [hedge], hlt, hheap, by rwa [hedge], hlist, hz⟩
    · intro ret mem₂ pos₂ hp₂
      obtain ⟨hret, hnew, hframe, hz₂⟩ := hp₂
      change ret = cursor + 1 at hret
      have hretw : ret < 2 ^ w := by omega
      refine runs_ret_le (v := ret) (by eval_expr) ⟨hret, ?_, hframe, hz₂⟩ ?_
      · change ListAt mem₂ report (written ++ [mem (inverse + edge)]) at hnew
        rwa [hedge] at hnew
      · change 28 ≤ 30
        decide

/-- The machine appends the exact original name of the live edge held
in the ready slot. -/
theorem detectSlotReport_external {w report heap names slot cursor ret fwd inv counter extCap intCap next : ℕ}
    {written : List ℕ} {G H : MGraph} {f g name : ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (hf : FreshInv G H f g next)
    (ht : FreshTablesAt mem fwd inv counter extCap intCap f g next)
    (hs : mem (names + slot) = name slot)
    (he : name slot ∈ H.E) (hcap : name slot < intCap)
    (hout : (detectSlotReportContract w report heap written).post
      [names, inv, slot, cursor] mem ret mem') :
    ListAt mem' report (written ++ [g (name slot)]) ∧ g (name slot) ∈ G.E := by
  have hlist := hout.2.1
  change ListAt mem' report (written ++ [mem (inv + mem (names + slot))]) at hlist
  rw [hs, ht.2.2 _ hcap] at hlist
  exact ⟨hlist, (hf.hRight _ he).2⟩

end MinCostFlow.MinRatio
