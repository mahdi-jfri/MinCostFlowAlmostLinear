module

public import MinCostFlow.LSF.Program.Spec

/-!
# The potential of a represented state

`lsfPhi_init_le` (`Spec.lean`) bounds the potential by `3000 (n₀ + 1) (log₂ (n₀ + 2) + 1)`
when two numbers in memory are at most `n₀`: the edge count of the `F` graph, and the size of
the component of each listed vertex. `lsfPhi_rep_le` reads both from `LSFRep`. The edges of `F`
are edges of `T₀` (`forestGivenRoots` only removes edges), and `T₀` has `tM ≤ n₀` edges. A
component of `F` has at most as many vertices as `F`, whose vertex set is that of the current
tree. So the bound holds whenever the current tree has at most `n₀` vertices, which is the case
for the initial state.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- The potential of a represented state whose current tree has at most `n₀` vertices. -/
theorem lsfPhi_rep_le {h b : ℕ} {S : LSFState} {x : (LSFRep h).τ} {mem : ℕ → ℕ}
    (hrep : (LSFRep h).rep b S x mem) (hV : S.T_cur.V.card ≤ x.n0) :
    (LSFRep h).phi b x mem ≤ 3000 * (x.n0 + 1) * (Nat.log 2 (x.n0 + 2) + 1) := by
  classical
  obtain ⟨-, -, -, -, -, -, hInv, -, -, htM, -, -, htn, -, -, -, -, -, -, hdgF, hFAnc, -, -,
    hAux⟩ := hrep
  refine lsfPhi_init_le ?_ ?_
  · rw [hdgF.2.2.2.2.2.2.1]
    have hsub : S.RF.F.E ⊆ S.T₀.E := by
      show (forestGivenRoots S.T₀ S.r₀ S.R_orig S.π).E ⊆ S.T₀.E
      exact Finset.sdiff_subset
    have := Finset.card_le_card hsub
    show S.RF.F.E.card ≤ x.n0
    omega
  · intro i hi
    obtain ⟨hFval, -, -, -, -, -, hmF, -, -, hExtToInt, hIntToExt, -,
      ⟨eL, heLlen, -, heLmem, heLat, -⟩, hSlots, -⟩ := hdgF
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hAct, hCid⟩ := hFAnc
    intro dgFPtr fAncPtr eCapF e he s hs u hu cid hcid
    have hi_eL : i < eL.length := by
      have hi1 : i < mem (lsfDgFPtr b x.vCap x.eCap x.tM + dgMOff) :=
        lt_of_lt_of_le hi (Nat.min_le_left _ _)
      rw [hmF] at hi1
      exact hi1.trans_eq heLlen.symm
    have he_eq : e = eL[i] := heLat i hi_eL
    have heF : e ∈ S.RF.F.E := he_eq ▸ (heLmem _).mp (List.getElem_mem _)
    have hs_eq : s = mem (dgExtToIntBase dgFPtr x.vCap + S.RF.F.tail e) := (hSlots e heF).1
    have huF_tail : S.RF.F.tail e ∈ S.RF.F.V := (hFval e heF).1
    have hu_eq : u = S.RF.F.tail e := by
      dsimp only [u]
      rw [hs_eq]
      exact (hExtToInt _ huF_tail).2
    have huF : u ∈ S.RF.F.V := hu_eq ▸ huF_tail
    obtain ⟨-, hc, -⟩ := hCid u huF
    obtain ⟨-, -, -, -, hsz, -, hcard⟩ := hAct _ hc
    show mem (fCompSizeBase fAncPtr x.vCap + cid) ≤ x.n0
    rw [hsz, hcard]
    exact (Finset.card_filter_le _ _).trans hV

end

end MinCostFlow.LSF.Program
