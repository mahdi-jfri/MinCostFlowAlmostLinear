module

public import MinCostFlow.LowStretch.ProgPreMath
public import MinCostFlow.LowStretch.ProgPreLoop
public import MinCostFlow.LowStretch.ProgPreIn

/-!
# Facts for the record part of the preprocessing

The two filters of the record list exactly the nodes and the pairs of `rootRec`
(`kept_nodes`, `kept_pairs`). The merge weights are at most the largest rounded weight
(`KT.mw_le_maxω`), and the heads are nodes (`KT.hd_lt`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open MinCostFlow.Cited

variable {G : WGraph} {T : KT}

theorem kept_nodes {C : ℕ → ℕ} (h : ∀ k < T.N, C k ≠ 0 ↔ T.IsNode (rootθ T G) k) :
    kept C T.N = (rootRec T G).nodes := by
  classical
  unfold kept rootRec
  simp only
  exact List.filter_congr fun k hk => decide_eq_decide.mpr (h k (List.mem_range.mp hk))

theorem kept_pairs {C : ℕ → ℕ}
    (h : ∀ p < G.m, C p ≠ 0 ↔
      T.top (rootθ T G) ((pgOf G).pu p) ≠ T.top (rootθ T G) ((pgOf G).pv p)) :
    kept C G.m = (rootRec T G).S.map Prod.fst := by
  rw [rootRec_S_fst]
  unfold kept
  exact List.filter_congr fun p hp => decide_eq_decide.mpr (h p (List.mem_range.mp hp))

theorem rootRec_S_snd {j : ℕ} : ((rootRec T G).S.getD j (0, 0)).2 = 0 := by
  classical
  unfold rootRec
  simp only
  rw [List.getD_eq_getElem?_getD]
  cases h : (((List.range G.m).filter fun p =>
      T.top (rootθ T G) ((pgOf G).pu p) ≠ T.top (rootθ T G) ((pgOf G).pv p)).map
        fun p => (p, 0))[j]? with
  | none => rfl
  | some e =>
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? h)
    rfl

theorem rootRec_S_fst_getD {j : ℕ} :
    ((rootRec T G).S.getD j (0, 0)).1 = ((rootRec T G).S.map Prod.fst).getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (rootRec T G).S[j]? <;> rfl

namespace KT

theorem mw_le_maxω (h : T.Ok (pgOf G)) {k : ℕ} (hk : k < T.N) : T.mw k ≤ (pgOf G).maxω := by
  by_cases hkn : (pgOf G).n ≤ k
  · obtain ⟨hm, he, -⟩ := h.merge k hkn hk
    rw [← he]; exact PG.le_maxω hm
  · rw [h.leaf_mw k (by omega)]; exact Nat.zero_le _

theorem hd_lt (h : T.Ok (pgOf G)) {k : ℕ} (hk : k < T.N) : T.hd (pgOf G) k < T.N :=
  (hd_under h k hk).lt_N h hk

end KT

end MinCostFlow.LowStretch
