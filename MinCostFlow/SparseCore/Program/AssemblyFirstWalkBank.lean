module

public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkStep
public import MinCostFlow.DynSpanner.Program.DynSpannerDSDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerDSPrefix
public import MinCostFlow.DynSpanner.Reemb

/-!
# The new walks of a batch of the spanner are paid by its bank

A batch `U` of the dynamic spanner of Theorem 8.2 (page 39) gives new walks to the edges of
`updateReembSet` (`piTotal_eq_of_not_mem_updateReembSet`). The first phase of the step of a
branch copies these walks into the embedding table, so it must pay their total length. This file
proves that the bank of the spanner pays it, with the charge of the batch.

* `updateReemb_walks_le_spent`: along a run, the total length of the new walks of a batch is at
  most the sum of `dsStepAmortCost` over the steps of the batch. An edge can get new walks at
  several steps of the batch; only its last walk counts, and it is paid by the step that wrote it.
  The proof is an induction over the steps of the batch.
* `dsHist_reemb_walks_add_bank_le`: for the abstract state `s` of the data structure and the batch
  `U`, the total length of the new walks plus the new bank is at most the old bank plus the charge
  `dsBatchCharge` of `U`. The steps of `U` take from the bank exactly their amortized costs
  (`dsSpent_append`), and the batch puts its charge in (`dsBankTotal_append`).

So the walks are not paid by the charge of the batch alone. A restart of the spanner gives a new
walk to every edge, and one batch of one update can cause it. Over a run, the bank pays them.
-/

public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-- A deletion or a vertex split only removes edges. -/
theorem applyUpdate_E_subset_of_delOrSplit {G : MGraph} {u : Update} (hu : isDelOrSplit u) :
    (G.applyUpdate u).E ⊆ G.E := by
  rcases u with ⟨e, a, b⟩ | e | ⟨v, v', St, Sh⟩
  · exact absurd hu id
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.rfl

/-- The new walks of the first `n` steps of a batch, as an induction over `n`: the edges that got
a new walk in one of the first `n` steps and are still in the graph, with their walks after these
steps, have total length at most the amortized costs of these steps. -/
private theorem reemb_walks_prefix_le (impl : SparsifyImpl) {G₀ : MGraph}
    {mMax L q vCap eCap : ℕ} (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) (k₀ : ℕ) :
    ∀ n, k₀ + n ≤ us.length →
      ∑ e ∈ ((Finset.range n).biUnion fun i =>
          runStepReembSet (L := L) G₀ q (canonicalSparsify impl) us (k₀ + i)) ∩
          (runState (L := L) G₀ q (canonicalSparsify impl) us (k₀ + n)).G.E,
        (piTotal (runState (L := L) G₀ q (canonicalSparsify impl) us (k₀ + n)) e).length ≤
      ∑ i ∈ Finset.range n, dsStepAmortCost G₀ impl mMax L q vCap eCap us (k₀ + i)
  | 0, _ => by simp
  | n + 1, hn => by
    classical
    set sp := canonicalSparsify impl
    have hk : k₀ + n < us.length := by omega
    set u := us[k₀ + n]'hk
    have hu : us[k₀ + n]? = some u := List.getElem?_eq_getElem hk
    have ih := reemb_walks_prefix_le (vCap := vCap) (eCap := eCap) impl hVG₀ hL hq hGm₀ hBV hds k₀ n
      (by omega)
    have hstep := runStepReemb_walks_le_amortCost (vCap := vCap) (eCap := eCap) impl hVG₀ hL hq
      hGm₀ hBV hds hk
    set st := runState (L := L) G₀ q sp us (k₀ + n)
    set st' := runState (L := L) G₀ q sp us (k₀ + (n + 1))
    have hst' : st' = (step st u sp).state := by
      show runState (L := L) G₀ q sp us (k₀ + n + 1) = _
      simp only [runState, hu]; rfl
    have hR : runStepReembSet (L := L) G₀ q sp us (k₀ + n) = stepReembSet st u := by
      simp only [runStepReembSet, hu]; rfl
    have hsame := piTotal_eq_of_not_mem_stepReembSet hVG₀ hL hq hGm₀
      (canonicalSparsify_spec_absorb impl mMax) hBV hds hk
    simp only at hsame
    have hSpec := canonicalSparsify_spec_absorb impl mMax
    have hE : st'.G.E ⊆ st.G.E := by
      have hI := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k₀ + n) hk.le).1.G_eq
      have hI' := (runInv_all hVG₀ hL hq hGm₀ hSpec hBV hds (k₀ + n + 1) hk).1.G_eq
      rw [show st' = runState (L := L) G₀ q sp us (k₀ + n + 1) from rfl, hI', hI,
        take_succ_of_getElem? hu, applyBatch_append]
      exact applyUpdate_E_subset_of_delOrSplit (hds u (List.getElem_mem hk))
    set A := (Finset.range n).biUnion fun i => runStepReembSet (L := L) G₀ q sp us (k₀ + i)
    set R := runStepReembSet (L := L) G₀ q sp us (k₀ + n)
    have hA : (Finset.range (n + 1)).biUnion
        (fun i => runStepReembSet (L := L) G₀ q sp us (k₀ + i)) = A ∪ R := by
      rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
    rw [hA, Finset.sum_range_succ]
    -- Split the edges by whether step `k₀ + n` gave them a new walk.
    have hsplit := Finset.sum_filter_add_sum_filter_not ((A ∪ R) ∩ st'.G.E) (· ∈ R)
      (fun e => (piTotal st' e).length)
    have h1 : ∑ e ∈ ((A ∪ R) ∩ st'.G.E).filter (· ∈ R), (piTotal st' e).length ≤
        ∑ e ∈ R, (piTotal st' e).length :=
      Finset.sum_le_sum_of_subset (fun e he => (Finset.mem_filter.mp he).2)
    have h2 : ∑ e ∈ ((A ∪ R) ∩ st'.G.E).filter (· ∉ R), (piTotal st' e).length ≤
        ∑ e ∈ A ∩ st.G.E, (piTotal st e).length := by
      calc ∑ e ∈ ((A ∪ R) ∩ st'.G.E).filter (· ∉ R), (piTotal st' e).length
          = ∑ e ∈ ((A ∪ R) ∩ st'.G.E).filter (· ∉ R), (piTotal st e).length := by
            refine Finset.sum_congr rfl fun e he => ?_
            obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
            have heG : e ∈ st'.G.E := (Finset.mem_inter.mp he1).2
            rw [hst'] at heG ⊢
            rw [hR] at he2
            rw [hsame e heG he2]
        _ ≤ ∑ e ∈ A ∩ st.G.E, (piTotal st e).length := by
            refine Finset.sum_le_sum_of_subset fun e he => ?_
            obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
            obtain ⟨heAR, heG⟩ := Finset.mem_inter.mp he1
            refine Finset.mem_inter.mpr ⟨?_, hE heG⟩
            rcases Finset.mem_union.mp heAR with h | h
            · exact h
            · exact absurd h he2
    have hstep' : ∑ e ∈ R, (piTotal st' e).length ≤
        dsStepAmortCost G₀ impl mMax L q vCap eCap us (k₀ + n) := hstep
    omega

/-- **The new walks of a batch, along a run.** For a batch `U` that is the slice
`us[k₀, k₀ + |U|)` of a run of valid deletions and splits, the total length of the new walks of
the edges of `updateReembSet` is at most the sum of the amortized costs of the steps of `U`. -/
theorem updateReemb_walks_le_spent (impl : SparsifyImpl) {G₀ : MGraph}
    {mMax L q vCap eCap : ℕ} (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    {us U : List Update} (hBV : G₀.BatchIsValid us) (hds : ∀ u ∈ us, isDelOrSplit u) {k₀ : ℕ}
    (hlen : k₀ + U.length ≤ us.length)
    (hmatch : ∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) :
    ∑ e ∈ updateReembSet (runState (L := L) G₀ q (canonicalSparsify impl) us k₀) U
        (canonicalSparsify impl),
        (piTotal (runState (L := L) G₀ q (canonicalSparsify impl) us (k₀ + U.length)) e).length ≤
      ∑ i ∈ Finset.range U.length, dsStepAmortCost G₀ impl mMax L q vCap eCap us (k₀ + i) := by
  rw [updateReembSet_run_eq G₀ us U k₀ hmatch]
  exact reemb_walks_prefix_le impl hVG₀ hL hq hGm₀ hBV hds k₀ U.length hlen

/-- The updates of the history after a batch: the old updates, then the batch. -/
theorem dsHist_flat_append (s : DSHist) (U : List Update) :
    (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).flat = s.flat ++ U := by
  simp [DSHist.flat]

/-- **The new walks of a batch of the data structure are paid by its steps.** Let `s` be the
abstract state of the data structure of Theorem 8.2 and `U` a batch, with valid deletions and
splits. The total length of the new walks of the edges of `updateReembSet`, at the state after
`U`, plus what the steps before `U` took from the bank, is at most what the steps up to the end of
`U` took. -/
theorem dsHist_reemb_walks_add_spent_le (P : DSParams) (s : DSHist) (U : List Update)
    (hVG₀ : s.G₀.IsValid) (hL : 1 ≤ P.L) (hGm₀ : s.G₀.m ≤ P.mMax)
    (hBV : s.G₀.BatchIsValid (s.flat ++ U)) (hds : ∀ u ∈ s.flat ++ U, isDelOrSplit u) :
    ∑ e ∈ updateReembSet (s.state P) U (canonicalSparsify P.impl),
        (piTotal ((⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P) e).length +
      dsSpent P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ s.flat ≤
      dsSpent P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ (s.flat ++ U) := by
  have hq : 1 ≤ s.q P := le_trans (by decide) (two_le_phaseBase _ _)
  have hst : s.state P = runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
      s.flat.length := by
    rw [runState_append s.G₀ (s.q P) (canonicalSparsify P.impl) s.flat U s.flat.length le_rfl]; rfl
  have hst' : (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P =
      runState (L := P.L) s.G₀ (s.q P) (canonicalSparsify P.impl) (s.flat ++ U)
        (s.flat.length + U.length) := by
    simp only [DSHist.state, dsHist_flat_append, List.length_append]
    rfl
  have hmatch : ∀ (i : ℕ) (hi : i < U.length),
      (s.flat ++ U)[s.flat.length + i]? = some (U[i]'hi) := by
    intro i hi
    simp only [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact List.getElem?_eq_getElem hi
  have hw := updateReemb_walks_le_spent (vCap := P.vCap) (eCap := P.eCap) P.impl hVG₀ hL hq hGm₀
    hBV hds (us := s.flat ++ U) (U := U) (k₀ := s.flat.length) (by simp) hmatch
  rw [hst, hst']
  have hsp := dsSpent_append P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ s.flat U
  rw [hsp]
  omega

/-- **The new walks of a batch are paid by the bank and the charge of the batch.** Let `s` be the
abstract state of the data structure of Theorem 8.2 and `U` a batch, with valid deletions and
splits within the split bound. The total length of the new walks of the edges of
`updateReembSet`, plus the bank after `U`, is at most the bank before `U` plus the charge
`dsBatchCharge` of `U`. -/
theorem dsHist_reemb_walks_add_bank_le (P : DSParams) (s : DSHist) (U : List Update)
    (hVG₀ : s.G₀.IsValid) (hL : 1 ≤ P.L) (hGm₀ : s.G₀.m ≤ P.mMax)
    (hBV : s.G₀.BatchIsValid (s.flat ++ U)) (hds : ∀ u ∈ s.flat ++ U, isDelOrSplit u)
    (hsplit : batchSplitCount (s.flat ++ U) ≤ P.splitBound)
    (hp : 1 ≤ max P.impl.p_s P.impl.p_t) :
    ∑ e ∈ updateReembSet (s.state P) U (canonicalSparsify P.impl),
        (piTotal ((⟨s.G₀, s.Us ++ [U]⟩ : DSHist).state P) e).length +
      (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).bank P ≤
      s.bank P + dsBatchCharge P.impl P.mMax P.L (s.G₀.n + P.splitBound) s.G₀
        (s.G₀.applyBatch s.flat) U := by
  have hw := dsHist_reemb_walks_add_spent_le P s U hVG₀ hL hGm₀ hBV hds
  have hflat : (s.Us ++ [U]).flatten = s.flat ++ U := dsHist_flat_append s U
  have hle := dsSpent_le_bankTotal (vCap := P.vCap) (eCap := P.eCap) (nMax := s.G₀.n + P.splitBound)
    P.impl (Us := s.Us ++ [U])
    hVG₀ hL hGm₀ (by rw [hflat]; exact hBV) (by rw [hflat]; exact hds)
    (by rw [hflat]; exact Nat.add_le_add_left hsplit _) hp
  have htot := dsBankTotal_append P.impl P.mMax P.L (s.q P) (s.G₀.n + P.splitBound) s.G₀ s.Us U
  simp only [DSHist.bank, dsBank]
  have hq' : (⟨s.G₀, s.Us ++ [U]⟩ : DSHist).q P = s.q P := rfl
  rw [hq', hflat]
  rw [hflat] at hle
  change _ + (dsBankTotal P.impl P.mMax P.L (s.q P) (s.G₀.n + P.splitBound) s.G₀ (s.Us ++ [U]) -
      dsSpent P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ (s.flat ++ U)) ≤
    (dsBankTotal P.impl P.mMax P.L (s.q P) (s.G₀.n + P.splitBound) s.G₀ s.Us -
      dsSpent P.impl P.mMax P.L (s.q P) P.vCap P.eCap s.G₀ s.flat) + _
  have hq'' : s.q P = phaseBase (s.G₀.n + P.splitBound) P.L := rfl
  rw [hq''] at hw htot ⊢
  rw [show s.Us.flatten = s.flat from rfl] at htot
  omega

end MinCostFlow.SparseCore.Program
