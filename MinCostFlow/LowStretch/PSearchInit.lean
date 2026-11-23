module

public import MinCostFlow.LowStretch.PSearchLoop
public import MinCostFlow.LowStretch.DijInit

/-!
# The start of a petal search

A petal search starts like a run of Dijkstra from the highway node `H[0]`: it writes the cost `0`
of `H[0]` with the stamp `rs` and pushes `(0, H[0])`. It also sets the bucket pointer to `1`,
the settled list to the empty list, the highway pointer to `H[0]`, the last key to `0` and the
five sums to `0`. The slot of `H[0]` is on and the other slots are off before the search
starts. Then the memory meets the invariant `SC.Inv` at the first state `SC.a0`
(`SC.init_inv`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

theorem esum_nil {ea eb wt : ℕ → ℕ} {ok : ℕ → Prop} {δ : ℕ → ℕ} {n : ℕ} (t : Fin 5) :
    ESum ea eb wt ok δ n [] t = 0 := by
  unfold ESum
  refine Finset.sum_eq_zero fun j _ => ?_
  fin_cases t <;> simp [eTerm, EBoth, EOne]

namespace SC

variable {C : SC} {w : ℕ}

/-- The first state of the search. -/
def a0 (C : SC) : SG := ⟨C.L.d0 C.X.G.s, DL.qs1 C.X.G.s, C.X.G.s, 0, [], 0, 1⟩

/-- **The start.** `M` is the memory after the start of the search, from the memory `mem0`. -/
theorem init_inv (h : C.Ok w) (hs : C.L.Shape w C.mem0 C.X.G.Nodes)
    (hS : ∀ v < C.L.NN, C.mem0 (C.L.TS + v) < C.L.rs ∧ C.mem0 (C.L.TS + 2 * C.L.NN + v) < C.L.rs)
    (hz : C.L.TZ C.mem0 (fun _ => []))
    (hsl : ∀ i < C.H.length, C.mem0 (C.L.HD + C.slot (C.hv i)) = if i = 0 then C.nx 0 else C.X.S)
    {M : ℕ → ℕ} (hpq : PQRep M C.L.D C.L.J C.L.A C.L.INF (DL.qs1 C.X.G.s))
    (htails : ∀ c < C.L.J, M (pqT C.L.D C.L.J c) = if c = 0 then
      DL.initMem C.L C.mem0 C.X.G.s (pqT C.L.D C.L.J 0) + 1 else
      DL.initMem C.L C.mem0 C.X.G.s (pqT C.L.D C.L.J c))
    (hM : ∀ x, (x < C.L.D + 3 ∨ C.L.D + pqSize C.L.J C.L.A ≤ x) → x < C.X.CTL →
      M x = DL.initMem C.L C.mem0 C.X.G.s x)
    (c0 : M C.X.CTL = 1) (c1 : M (C.X.CTL + 1) = 0) (c2 : M (C.X.CTL + 2) = C.X.G.s)
    (c3 : M (C.X.CTL + 3) = 0) (cs : ∀ t : Fin 5, M (C.X.SUM + t) = 0)
    (htop : ∀ x, C.X.SL + C.L.NN + 1 ≤ x → M x = C.mem0 x) :
    C.Inv w C.a0 M := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hR := h.hR
  have hCTL := h.hCTL
  unfold pqSize at hR
  have hsN : C.X.G.s ∈ C.X.G.Nodes := by rw [← h.H0]; exact h.HN 0 h.Hne
  have hsn : C.X.G.s < C.L.NN := ((hs.ok_iff _).mpr hsN).1
  have hJ1 := hpq.J_pos
  have hINF := hs.INF_pos
  have hM' : ∀ a < C.L.D, M a = DL.initMem C.L C.mem0 C.X.G.s a := fun a ha =>
    hM a (Or.inl (by omega)) (by omega)
  obtain ⟨hs1, hr1⟩ := DL.init_rep hs hsN hS hpq hM'
  have hTS : ∀ a < C.L.TS, M a = C.mem0 a := fun a ha => by
    rw [hM' a (by omega)]; unfold DL.initMem
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hg : C.L.g M = C.L.g C.mem0 := DL.g_congr C.L hs hTS
  have hzI : ∀ c < C.L.J, DL.initMem C.L C.mem0 C.X.G.s (pqT C.L.D C.L.J c) = 0 := fun c hc => by
    have := hz c hc rfl
    unfold DL.initMem
    rw [Function.update_of_ne (by unfold pqT; omega), Function.update_of_ne (by unfold pqT; omega)]
    exact this
  have hfix : ∀ x, C.Fix x → M x = C.mem0 x := by
    rintro x ⟨hk, hx, -⟩
    rcases hk with hk | ⟨hk1, hk2⟩ | ⟨hk1, -, -⟩
    · exact hTS x hk
    · rw [hM x (Or.inl hk2) hx]; unfold DL.initMem
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rw [hM x (Or.inr hk1) hx]; unfold DL.initMem
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hH0 : (C.H ++ [C.X.S]).getD 0 0 = C.X.G.s := by
    rw [List.getD_append _ _ _ _ h.Hne]; exact h.H0
  refine ⟨hs1, hr1, ?_, fun h => h.elim, fun c hc => ?_, ?_, ?_, DL.init_stamps l7 hS hM', hfix,
    Nat.zero_le _, by rw [c2]; exact hH0.symm, fun i hi => ?_, fun i _ => ?_, by rw [c1]; rfl,
    fun i hi => absurd hi (by simp [a0]), List.nodup_nil, fun v => ?_, by rw [c3]; rfl, fun t => ?_,
    c0, le_rfl, show 1 ≤ C.X.Lb + 1 by omega, fun _ => Nat.zero_le _, fun q h1 h2 => by simp only [a0] at h2; omega,
    fun q _ _ r hr => absurd hr (by simp only [a0, DL.d0]; omega), htop⟩
  · rw [hg]; exact AG.inv_init hINF
  · rw [htails c hc]
    split_ifs with h0
    · subst h0; rw [hzI 0 hJ1]; simp [a0, DL.d0]
    · rw [hzI c hc]; simp
  · exact AG.parInv_init _ _
  · exact DL.TZ.push (L := C.L) (mem := DL.initMem C.L C.mem0 C.X.G.s) (e := (0, C.X.G.s)) (c := 0)
      (fun c hc _ => hzI c hc) fun c' hc' hne => by rw [htails c' hc', if_neg hne]
  · rw [hTS _ (by have := h.slot_lt hi; omega), hsl i hi]
    simp only [a0]
    by_cases hi0 : i = 0
    · subst hi0; simp
    · simp only [hi0, ↓reduceIte, show ¬ i ≤ 0 by omega]
  · simp only [a0, DL.d0, Nat.not_lt_zero]
  · simp only [a0, DL.d0, List.not_mem_nil]
  · rw [cs t]; unfold es; exact (esum_nil t).symm

end SC

end MinCostFlow.LowStretch
