module

public import MinCostFlow.LowStretch.ProgResetH
public import MinCostFlow.LowStretch.ProgChildOneNc

/-!
# The reset of child `k`: the precondition of `ncP`

After the index list, `rsB` calls `ncP` on `[cnt, IDX, A, HEAD, LOC, IDX + cnt]` with
`IDX = A + 3 cnt`: entry `i` reads the index `3 i + 1`, so its node is entry `i` of column `1` of
the work array, one of the new `x`-nodes. The layout `CS.rsNcE` meets `NCE.Ok` (`CS.rsNcOk`):
the cells read lie between `h` and `IDX + cnt` or in the head array, which avoid the local
indices, and the heads of distinct `x`-nodes are distinct (`top_hd_inj`), since column `1` has no
repeated node.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable {S : CS} {w : ℕ} {k : ℕ}

/-- The layout of the call of `ncP` in the reset, on the memory `M9`. -/
def rsNcE (A cnt HEAD LOC : ℕ) (M9 : ℕ → ℕ) : NCE :=
  ⟨cnt, A + 3 * cnt, A, HEAD, LOC, A + 3 * cnt + cnt, M9⟩

/-- **The precondition of `ncP` in the reset.** Here `x` is the new threshold, column `1` of the
work array holds the `x`-nodes of child `k` once each, and the head array is unchanged. -/
theorem rsNcOk (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {x A cnt : ℕ} (hx1 : 1 ≤ x) (hA : S.h ≤ A) {M9 : ℕ → ℕ}
    (hidx : ∀ i < cnt, M9 (A + 3 * cnt + i) = 3 * i + 1)
    (hcol : ∀ j, j ∈ rdS M9 A 1 cnt ↔ ∃ a ∈ (S.raw k).X, j = S.T.top x a)
    (hnd : (rdS M9 A 1 cnt).Nodup)
    (hhd : ∀ j < S.T.N, M9 (S.E.HEAD + j) = S.T.hd S.G j)
    (hroom : A + 3 * cnt + cnt + cnt + 1 < 2 ^ w) :
    (rsNcE A cnt S.E.HEAD S.E.LOC M9).Ok w S.T.N := by
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hEN : S.E.N = S.T.N := hG.N
  have hHD : (S.E.HEAD, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have bH : S.E.HEAD + S.E.N ≤ S.h := hpre.below _ hHD
  have dH : RegDisj (S.E.HEAD, S.E.N) (S.E.LOC, S.T.N) := hpre.loc_disj _ hHD
  unfold RegDisj at dH
  dsimp only at bH dH
  have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hN := hpre.ok.tree.n_lt
  have hlen : (rdS M9 A 1 cnt).length = cnt := rdS_length _ _ _ _
  -- entry `i` of column `1`
  have hget : ∀ i (hi : i < cnt), (rdS M9 A 1 cnt)[i]'(by rw [rdS_length]; exact hi) =
      M9 (A + 3 * i + 1) := fun i hi => by
    simp [rdS]
  have hxi : ∀ i < cnt, (rsNcE A cnt S.E.HEAD S.E.LOC M9).x i = M9 (A + 3 * i + 1) :=
    fun i hi => by
      simp only [NCE.x, rsNcE]
      rw [hidx i hi]; congr 1
  have hmem : ∀ i < cnt, ∃ a ∈ (S.raw k).X, M9 (A + 3 * i + 1) = S.T.top x a := fun i hi => by
    rw [← hget i hi]; exact (hcol _).mp (List.getElem_mem _)
  have hxN : ∀ i < cnt, M9 (A + 3 * i + 1) < S.T.N := fun i hi => by
    obtain ⟨a, ha, he⟩ := hmem i hi
    rw [he]
    exact top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha)) hx1
  have hhdi : ∀ i < cnt, (rsNcE A cnt S.E.HEAD S.E.LOC M9).hd i =
      S.T.hd S.G (M9 (A + 3 * i + 1)) := fun i hi => by
    simp only [NCE.hd]; rw [hxi i hi]; exact hhd _ (hxN i hi)
  refine ⟨fun i hi => ?_, fun i hi j hj he => ?_, show S.E.LOC + S.T.N ≤ A + 3 * cnt + cnt by
    omega, hroom⟩
  · have hi : i < cnt := hi
    have hx := hxN i hi
    have hdN := (hd_under hpre.ok.tree _ hx).lt_N hpre.ok.tree hx
    have hdN' : (rsNcE A cnt S.E.HEAD S.E.LOC M9).hd i < S.T.N := by rw [hhdi i hi]; exact hdN
    have hx' := hxi i hi
    simp only [NCE.Off, rsNcE] at hx' hdN' ⊢
    rw [hidx i hi, show A + (3 * i + 1) = A + 3 * i + 1 by omega, hx']
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hdN'⟩
  · have hi : i < cnt := hi
    have hj : j < cnt := hj
    rw [hhdi i hi, hhdi j hj] at he
    obtain ⟨a, ha, ea⟩ := hmem i hi
    obtain ⟨b, hb, eb⟩ := hmem j hj
    rw [ea, eb] at he
    have := top_hd_inj hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha))
      (hpre.ok.n_of_mem (Cl.raw_X_subset k hb)) hx1 he
    rw [← ea, ← eb, ← hget i hi, ← hget j hj] at this
    exact hnd.getElem_inj_iff.mp this

end CS

end MinCostFlow.LowStretch
