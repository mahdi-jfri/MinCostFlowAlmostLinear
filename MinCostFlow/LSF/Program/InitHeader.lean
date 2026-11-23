module

public import MinCostFlow.LSF.Program.InitSegF
public import MinCostFlow.LSF.Program.Spec

/-!
# The state header of the initial state

The last call of the driver stores the 24 words `lsfHdrVals` at `b`. `init_lsfHeader` reads
them as `lsfHeaderAt`, for every concrete state whose numbers are those of the driver. The
places of the blocks in `lsfHdrVals` are the places of `InitVals`, which are the places that
the layout of `Spec.lean` computes from `b`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF InitDriver

@[expose] public section

/-- After the store of the state header, the header holds the numbers of the concrete state,
the places of its blocks, the number of roots, no updates and the root. -/
theorem init_lsfHeader {w : ℕ} {V : InitVals} {h P_fp kk nR r₀ v₈ : ℕ} {mem₇ mem₈ : ℕ → ℕ}
    {S : LSFState} {x : LSFConcrete}
    (h₈ : (storeArgsContract w 24).post (V.b :: lsfHdrVals V h P_fp kk nR r₀) mem₇ v₈ mem₈)
    (hvc : x.vCap = V.vCap) (hec : x.eCap = V.eCap) (hn : x.n0 = V.n0) (hm : x.m0 = V.m0)
    (htM : x.tM = V.tM) (hLw : x.L_w = V.L_w) (hh : x.h = h) (hP : x.P_fp = P_fp)
    (hLin : x.L_in = V.L_in) (hk : x.k_nat = kk) (hR : S.R.card = nR)
    (_hU : S.numUpdates = 0) (hr : S.r₀ = r₀) :
    lsfHeaderAt mem₈ V.b S x := by
  obtain ⟨_, _, heq, -, hv, -⟩ := h₈
  simp only [List.cons.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  have hk' : ∀ i < 24, mem₈ (V.b + i) = (lsfHdrVals V h P_fp kk nR r₀).getD i 0 := hv
  rw [lsfHeaderAt, hvc, hec, hn, hm, htM, hLw, hh, hP, hLin, hk, hR, hr]
  exact ⟨hk' 0 (by norm_num), hk' 1 (by norm_num), hk' 2 (by norm_num), hk' 3 (by norm_num),
    hk' 4 (by norm_num), hk' 5 (by norm_num), hk' 6 (by norm_num), hk' 7 (by norm_num),
    hk' 8 (by norm_num), hk' 9 (by norm_num), hk' 10 (by norm_num), hk' 11 (by norm_num),
    hk' 12 (by norm_num), hk' 13 (by norm_num), hk' 14 (by norm_num), hk' 15 (by norm_num),
    hk' 16 (by norm_num), hk' 17 (by norm_num), hk' 18 (by norm_num), hk' 19 (by norm_num),
    hk' 20 (by norm_num), hk' 21 (by norm_num), hk' 22 (by norm_num), hk' 23 (by norm_num)⟩

/-- The two header stores keep the blocks from `fPtr` to the aux header and the aux block after
its header. So the numbers that the state header reads from the memory before the stores (the
root count at `fAncPtr`, the root at `vListPtr`) are still there at the end. -/
lemma init_store_keep {w : ℕ} {V : InitVals} {v₇ v₈ : ℕ} {vs₇ vs₈ : List ℕ}
    {mem₆ mem₇ mem₈ : ℕ → ℕ}
    (h₇ : (storeArgsContract w 20).post (V.auxPtr :: vs₇) mem₆ v₇ mem₇)
    (h₈ : (storeArgsContract w 24).post (V.b :: vs₈) mem₇ v₈ mem₈) :
    ∀ a, (V.fPtr ≤ a ∧ a < V.auxPtr) ∨ V.auxPtr + 20 ≤ a → mem₈ a = mem₆ a := by
  obtain ⟨_, _, heq₇, -, -, hfr₇⟩ := h₇
  simp only [List.cons.injEq] at heq₇
  obtain ⟨rfl, rfl⟩ := heq₇
  obtain ⟨_, _, heq₈, -, -, hfr₈⟩ := h₈
  simp only [List.cons.injEq] at heq₈
  obtain ⟨rfl, rfl⟩ := heq₈
  have hls : lsfHdrSize = 24 := rfl
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  intro a ha
  rcases ha with ⟨ha1, ha2⟩ | ha
  · rw [hfr₈ a (Or.inr (by omega)), hfr₇ a (Or.inl ha2)]
  · rw [hfr₈ a (Or.inr (by omega)), hfr₇ a (Or.inr (by omega))]

end

end MinCostFlow.LSF.Program
