module

public import MinCostFlow.IPM.Machine.Layout
public import MinCostFlow.Chain.Algorithm2
import WordRAM.Memory
import WordRAM.Tactic

/-!
# Finishing the Detect answer

Definition 4.5 (page 14) and the proof of Theorem 5.1 (pages 29–30)
return edges whose flow changes cross the detection threshold. As each
edge is found, its external name is appended to the output and its
account is reset. The final step writes the count in the reserved first
word. The proof connects the list to the model's set and gives the exact
constant cost of this step.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Arguments are the output address and the number of reported edges. -/
def detectFinishBody : Stmt :=
  .store (.reg 0) (.reg 1) ;; .ret (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 1))

/-- Finish a list of distinct edge names already written after the count.
The returned pointer is the end of the list, ready for the next allocation. -/
def detectFinishContract (w : ℕ) (reported : List ℕ) : Contract where
  pre args mem := ∃ a, args = [a, reported.length] ∧ a + 1 + reported.length < 2 ^ w ∧
    reported.Nodup ∧ ListAt mem (a + 1) reported ∧ ZeroFrom mem (a + 1 + reported.length)
  post args mem v mem' :=
    v = args.getD 0 0 + 1 + reported.length ∧
    DetectAt mem' (args.getD 0 0) reported.toFinset ∧
    (∀ x, x ≠ args.getD 0 0 → mem' x = mem x) ∧ ZeroFrom mem' v
  cost _ _ := 10

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine Chain

/-- Finishing the Detect answer uses no random instruction. -/
theorem detectFinishBody_noRand : detectFinishBody.NoRand := by
  simp [detectFinishBody, Stmt.NoRand]

/-- The Detect header write meets the layout and frame contract. -/
theorem detectFinish_meetsContract {w base : ℕ} {p : Program} (reported : List ℕ)
    (hp : p.HasAt base [detectFinishBody]) :
    MeetsContract w p base (detectFinishContract w reported) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, rfl, hbound, hnd, hlist, hz⟩ := hpre
  have hword : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold detectFinishBody
  wram_run
  · refine ⟨rfl, ⟨reported, hnd, rfl, ?_, ?_⟩, ?_, ?_⟩
    · change Function.update mem a reported.length a = reported.length
      exact Function.update_self _ _ _
    · intro i hi
      change Function.update mem a reported.length (a + 1 + i) = reported[i]
      rw [Function.update_of_ne (by omega)]
      exact hlist i hi
    · intro x hx
      change Function.update mem a reported.length x = mem x
      exact Function.update_of_ne hx _ _
    · intro x hx
      change Function.update mem a reported.length x = 0
      rw [Function.update_of_ne (by change a + 1 + reported.length ≤ x at hx; omega)]
      exact hz x hx
  · simp only [detectFinishContract]
    wram_cost

/-- A list that reports exactly the model's ready edges gives the IPM
layout of the Algorithm 2 Detect answer. -/
theorem detectFinish_algorithm2_set {w a ret : ℕ} {cfg : Alg2Config}
    {st : Alg2State cfg} {mem mem' : ℕ → ℕ} {reported : List ℕ}
    (hset : ∀ e, e ∈ reported ↔ e ∈ st.extG.E ∧ cfg.ε ≤ st.extℓ e * st.detectAccum e)
    (hout : (detectFinishContract w reported).post [a, reported.length] mem ret mem') :
    DetectAt mem' a (algorithm2_detect cfg st).1 := by
  have heq : reported.toFinset = (algorithm2_detect cfg st).1 := by
    ext e
    simp only [List.mem_toFinset, algorithm2_detect, Finset.mem_filter]
    exact hset e
  rw [← heq]
  exact hout.2.1

end MinCostFlow.MinRatio
