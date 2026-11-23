module

public import MinCostFlow.LSF.Program.InitSegA
public import MinCostFlow.LSF.Program.TreePhase

/-!
# The pre of the tree phase in the init driver

`treeCopies_pre_of` gives the pre of `treeCopiesContract` at the places of `InitPlaces.lean`,
from the facts that hold after `prepStage` and `widths`: the copy of `G₀` at `gPtr` with its edge
list, the vertex list and its index table, the input arrays below the handle `b`, and zero memory
from `lsstHeap` on.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord

@[expose] public section

/-- The first `20` arguments of the tree phase, at the places of the driver. -/
def treeCopyArgsV (V : InitVals) (lenArr wtArr : ℕ) : List ℕ :=
  [V.gPtr, dgEListBase V.gPtr V.vCap V.eCap, lenArr, wtArr, V.L_in, V.m0, V.K_w, V.qNat,
    V.lsstHeap, V.vIdx, V.n0, V.eCap, V.mult, V.copyTail, V.copyHead, V.copyLen, V.copyWt,
    V.copyOrig, V.copySub, V.usedBridge]

theorem treeCopies_pre_of {w h : ℕ} {G₀ : MGraph} {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ}
    {vList eList : List ℕ} (V : InitVals) {lenArr wtArr : ℕ} {mem : ℕ → ℕ}
    (hh : 1 ≤ h) (hhw : 3 * h + 2 ≤ w) (hLin : 1 ≤ V.L_in) (h2L : 2 ≤ h * V.L_in)
    (hPd : h ∣ P_fp) (hG : G₀.IsValid) (hm : G₀.E.card = V.m0)
    (hn : G₀.n = V.n0) (hK : V.K_w = kWidthOf V.m0 V.L_in)
    (hdg : DynGraphAt mem V.gPtr V.vCap V.eCap G₀)
    (heLen : eList.length = V.m0) (heNd : eList.Nodup) (heE : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (heL : ListAt mem (dgEListBase V.gPtr V.vCap V.eCap) eList)
    (hvLen : vList.length = V.n0) (hvNd : vList.Nodup) (hvV : ∀ u, u ∈ vList ↔ u ∈ G₀.V)
    (hvI : ∀ i (hi : i < vList.length), mem (V.vIdx + vList[i]) = i + 1)
    (hlenB : ∀ e ∈ G₀.E, lenArr + e * V.L_in + V.L_in ≤ V.b)
    (hwtB : ∀ e ∈ G₀.E, wtArr + e * V.L_in + V.L_in ≤ V.b)
    (hlv : ∀ e ∈ G₀.E, Num.Valid mem (lenArr + e * V.L_in) h V.L_in ∧
      Num.fixVal mem (lenArr + e * V.L_in) h V.L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e)
    (hwv : ∀ e ∈ G₀.E, Num.Valid mem (wtArr + e * V.L_in) h V.L_in ∧
      Num.fixVal mem (wtArr + e * V.L_in) h V.L_in P_fp = v e ∧ 0 < v e)
    (hz : ZeroFrom mem V.lsstHeap)
    (hsp : V.lsstHeap + V.m0 * multQNatStepSpace V.K_w < 2 ^ w)
    (hec : V.eCap + (2 * V.m0 + V.n0) + V.eCap < 2 ^ w) :
    (treeCopiesContract w h G₀ v ℓ₀ P_fp vList eList).pre (treeCopyArgsV V lenArr wtArr) mem := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, -⟩ :=
    V.scratch_order
  have hmE : V.m0 ≤ V.eCap := by
    rw [← hm]
    have := Finset.card_le_card (show G₀.E ⊆ Finset.range V.eCap from fun e he =>
      Finset.mem_range.mpr (hdg.2.2.1 e he))
    simpa using this
  have hdgs : dynGraphSize V.vCap V.eCap = 4 + 7 * V.vCap + 9 * V.eCap := rfl
  have hEL : dgEListBase V.gPtr V.vCap V.eCap = V.gPtr + 4 + 7 * V.vCap + V.eCap := rfl
  have hbg : V.b ≤ V.gPtr := by rw [← e15]; omega
  have hmin := V.minPtr_eq
  -- `omega` is slow on these two goals with the many facts above, so they are direct
  have le3 : ∀ a b c d : ℕ, a ≤ a + b + c + d := fun a b c d =>
    Nat.le_add_right_of_le (Nat.le_add_right_of_le (Nat.le_add_right _ _))
  refine ⟨V.gPtr, dgEListBase V.gPtr V.vCap V.eCap, lenArr, wtArr, V.L_in, V.m0, V.K_w, V.qNat,
    V.lsstHeap, V.vIdx, V.n0, V.eCap, V.mult, V.copyTail, V.copyHead, V.copyLen, V.copyWt,
    V.copyOrig, V.copySub, V.usedBridge, V.vCap, V.eCap, rfl, hh, hhw, hLin, h2L, hPd, hG, hm,
    hn, hK, hdg, by omega, hdg.2.2.1, heLen, heNd, heE, heL, by omega, hvLen, hvNd, hvV,
    hvI, by omega, fun e he => by have := hlenB e he; omega,
    fun e he => by have := hwtB e he; omega, hlv, hwv, s2.symm, s3.le, by omega, by omega,
    by omega, by omega, by omega, by rw [← s12, ← s11, ← s10, ← s9]; exact le3 _ _ _ _,
    by rw [← s16, ← s15, ← s14, ← s13]; exact le3 _ _ _ _, hsp, hec, hz⟩

end

end MinCostFlow.LSF.Program
