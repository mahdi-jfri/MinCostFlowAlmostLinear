module

public import MinCostFlow.LSF.Program.InitKeep
public import MinCostFlow.LSF.Program.AuxAssemble

/-!
# The aux block of the initial state

`init_auxHeader`: the aux header that the `store20` call writes, with the root index `0` at
`auxOffR0Idx`, is still there after the `store24` call, which writes the state header below
`gPtr`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program InitDriver

@[expose] public section

/-- After the two header stores, the aux header names the arrays of the aux block, and the root
index is `0`. -/
theorem init_auxHeader {w : ℕ} {V : InitVals} {mem₆ mem₇ mem₈ : ℕ → ℕ} {v₇ v₈ : ℕ}
    {vs₈ : List ℕ}
    (h₇ : (storeArgsContract w 20).post (V.auxPtr :: auxHdrVals V) mem₆ v₇ mem₇)
    (h₈ : (storeArgsContract w 24).post (V.b :: vs₈) mem₇ v₈ mem₈) :
    AuxHeader mem₈ V.auxPtr V.vCap V.n0 ∧ mem₈ (V.auxPtr + auxOffR0Idx) = 0 := by
  obtain ⟨_, _, heq₇, -, hv₇, -⟩ := h₇
  simp only [List.cons.injEq] at heq₇
  obtain ⟨rfl, rfl⟩ := heq₇
  obtain ⟨_, _, heq₈, -, -, hfr₈⟩ := h₈
  simp only [List.cons.injEq] at heq₈
  obtain ⟨rfl, rfl⟩ := heq₈
  have hls : lsfHdrSize = 24 := rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  have hk : ∀ i < 20, mem₈ (V.auxPtr + i) = (auxHdrVals V).getD i 0 := fun i hi => by
    rw [hfr₈ _ (Or.inr (by omega)), hv₇ i hi]
  exact ⟨⟨hk 0 (by norm_num), hk 1 (by norm_num), hk 2 (by norm_num), hk 3 (by norm_num),
    hk 4 (by norm_num), hk 5 (by norm_num), hk 6 (by norm_num), hk 7 (by norm_num),
    hk 8 (by norm_num), hk 9 (by norm_num), hk 10 (by norm_num), hk 11 (by norm_num),
    hk 12 (by norm_num), hk 13 (by norm_num), hk 14 (by norm_num), hk 15 (by norm_num),
    hk 16 (by norm_num)⟩, hk 17 (by norm_num)⟩

end

end MinCostFlow.LSF.Program
