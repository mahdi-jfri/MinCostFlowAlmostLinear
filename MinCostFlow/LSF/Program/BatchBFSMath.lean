module

public import MinCostFlow.LSF.Program.BatchMath
import Mathlib.Tactic.Linarith

/-!
# Mathematical Invariants for Lock-Step Half-Edge BFS (`BatchBFSMath`)

Develops the pure graph and doubly-linked-list invariants for lock-step half-edge BFS on a forest
`F` represented by `DynGraphAt`:

* `DllTailAt`: suffix invariant connecting `curHe` in `dgHeNextBase` to a list `remHe` of
  remaining half-edges, initialized from `IsDoublyLinkedList`.
* `sum_incL_comp_eq_two_mul_edges`: for any component `C` of `F` with edge set `E_C`,
  `∑ v ∈ C, (incL (extToInt v)).length = 2 * E_C.card`.
* `BfsInv`: single-side BFS state invariant with exact step identity
  `steps + remHe.length = qHead + ∑ k < qHead, deg(q[k])`, proving `steps ≤ 3 * E_C.card + 1`
  always and `steps = 3 * E_C.card + 1`, `q.toFinset = C`, `q.length = E_C.card + 1` on
  termination.
* `fanc_update_split`: pure `FAncAt` preservation when splitting one component `oldCid` into two
  disjoint components `C_small` (taking fresh ID `root2`) and `C_big` (keeping `oldCid`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Doubly-linked list suffix predicate -/

/-- `curHe` is the `1`-indexed head of the remaining half-edge list `rem` in `heNextAddr`. -/
def DllTailAt (mem : ℕ → ℕ) (heNextAddr cap : ℕ) : List ℕ → ℕ → Prop
  | [], cur => cur = 0
  | h :: tl, cur => cur = h + 1 ∧ h < cap ∧ DllTailAt mem heNextAddr cap tl (mem (heNextAddr + h))

lemma dllTailAt_of_isDll {mem : ℕ → ℕ} {hePrev heNext headAddr cap : ℕ} {L : List ℕ}
    (hdll : IsDoublyLinkedList mem hePrev heNext headAddr cap L) :
    DllTailAt mem heNext cap L (mem headAddr) := by
  rcases hdll with ⟨_, hlt, hhead, hlinks⟩
  have hnext : ∀ i (hi : i < L.length),
      mem (heNext + L[i]) = if i + 1 = L.length then 0 else L.getD (i + 1) 0 + 1 :=
    fun i hi => (hlinks i hi).2
  have hdrop : ∀ n, ∀ i, L.length - i = n →
      DllTailAt mem heNext cap (L.drop i)
        (if hi : i < L.length then L[i] + 1 else 0) := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have hge : L.length ≤ i := by omega
      have hnot : ¬ i < L.length := by omega
      rw [List.drop_eq_nil_of_le hge]
      simp only [hnot, ↓reduceDIte]
      rfl
    | succ n ih =>
      intro i hi
      have hilt : i < L.length := by omega
      rw [List.drop_eq_getElem_cons hilt]
      simp only [hilt, ↓reduceDIte]
      refine ⟨rfl, hlt _ (List.getElem_mem hilt), ?_⟩
      have hn := hnext i hilt
      have hsub := ih (i + 1) (by omega)
      by_cases hlast : i + 1 = L.length
      · have hnot : ¬ i + 1 < L.length := by omega
        simp only [hlast, ↓reduceIte] at hn
        simp only [hnot, ↓reduceDIte] at hsub
        rwa [hn]
      · have hilt1 : i + 1 < L.length := by omega
        simp only [hlast, ↓reduceIte, List.getD_eq_getElem _ _ hilt1] at hn
        simp only [hilt1, ↓reduceDIte] at hsub
        rwa [hn]
  have h0 := hdrop L.length 0 (Nat.sub_zero _)
  rw [List.drop_zero] at h0
  cases L with
  | nil => exact hhead
  | cons a tl =>
    simp only [List.length_cons, Nat.zero_lt_succ, ↓reduceDIte, List.getElem_cons_zero] at h0
    simpa only [hhead] using h0

lemma dllTailAt_congr {mem mem' : ℕ → ℕ} {heNext cap cur : ℕ} {L : List ℕ}
    (h : DllTailAt mem heNext cap L cur)
    (hag : ∀ i < cap, mem' (heNext + i) = mem (heNext + i)) :
    DllTailAt mem' heNext cap L cur := by
  induction L generalizing cur with
  | nil => exact h
  | cons a tl ih =>
    rcases h with ⟨hcur, hlt, htl⟩
    exact ⟨hcur, hlt, by rw [hag a hlt]; exact ih htl⟩

/-! ## Half-edge incidence and degree-sum identity on a component -/

/-- The opposite endpoint of half-edge `he` in `F`: tail if odd (`he = 2e+1`), head if even
(`he = 2e`). -/
def heOther (F : MGraph) (he : ℕ) : ℕ :=
  if he % 2 = 1 then F.tail (he / 2) else F.head (he / 2)

/-- For a valid `DynGraphAt` of `F` with incidence lists `incL`, every `he ∈ incL (extToInt v)`
connects `v` to `heOther F he` by a single edge `he / 2 ∈ F.E`. -/
lemma incL_mem_connected {mem : ℕ → ℕ} {dgFPtr vCap eCapF : ℕ} {F : MGraph}
    {incL : ℕ → List ℕ}
    (hFval : F.IsValid)
    (hExtToInt : ∀ v ∈ F.V, mem (dgExtToIntBase dgFPtr vCap + v) ∈ F.V ∧
      mem (dgIntToExtBase dgFPtr vCap + mem (dgExtToIntBase dgFPtr vCap + v)) = v)
    (hvCap : ∀ v ∈ F.V, v < vCap)
    (hincL : ∀ s < vCap,
      IsDoublyLinkedList mem (dgHePrevBase dgFPtr vCap eCapF) (dgHeNextBase dgFPtr vCap eCapF)
        (dgIncHeadBase dgFPtr vCap + s) (2 * eCapF) (incL s) ∧
      mem (dgSlotDegBase dgFPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCapF ∧ h / 2 ∈ F.E ∧
        (if h % 2 = 0 then mem (dgExtToIntBase dgFPtr vCap + F.tail (h / 2))
         else mem (dgExtToIntBase dgFPtr vCap + F.head (h / 2))) = s)
    {v he : ℕ} (hv : v ∈ F.V) (hhe : he ∈ incL (mem (dgExtToIntBase dgFPtr vCap + v))) :
    he < 2 * eCapF ∧ he / 2 ∈ F.E ∧
      heOther F he ∈ F.V ∧ F.Connected v (heOther F he) := by
  have hs_lt : mem (dgExtToIntBase dgFPtr vCap + v) < vCap := hvCap _ (hExtToInt v hv).1
  obtain ⟨hlt, heE, hslot⟩ := ((hincL _ hs_lt).2.2 he).mp hhe
  have hte := (hFval _ heE).1
  have hheV := (hFval _ heE).2
  refine ⟨hlt, heE, ?_, ?_⟩
  · dsimp only [heOther]; split_ifs <;> assumption
  · dsimp only [heOther]
    by_cases hmod : he % 2 = 0
    · have hmod1 : he % 2 ≠ 1 := by omega
      simp only [hmod, ↓reduceIte] at hslot
      simp only [hmod1, ↓reduceIte]
      have htv : F.tail (he / 2) = v := by
        have h1 := (hExtToInt _ hte).2
        rw [hslot, (hExtToInt v hv).2] at h1
        exact h1.symm
      exact ⟨[(he / 2, true)], .cons heE (by simp [MGraph.src, htv]) (.nil _)⟩
    · have hmod1 : he % 2 = 1 := by omega
      simp only [hmod, ↓reduceIte] at hslot
      simp only [hmod1, ↓reduceIte]
      have hhv : F.head (he / 2) = v := by
        have h1 := (hExtToInt _ hheV).2
        rw [hslot, (hExtToInt v hv).2] at h1
        exact h1.symm
      exact ⟨[(he / 2, false)], .cons heE (by simp [MGraph.src, hhv]) (.nil _)⟩

open Classical in
/-- Sum of `incL` lengths over a connected component `C` of `F` equals `2 * E_C.card`. -/
lemma sum_incL_comp_eq_two_mul_edges {mem : ℕ → ℕ} {dgFPtr vCap eCapF : ℕ} {F : MGraph}
    {incL : ℕ → List ℕ}
    (hFval : F.IsValid) (hvCap : ∀ v ∈ F.V, v < vCap) (heCap : ∀ e ∈ F.E, e < eCapF)
    (hExtToInt : ∀ v ∈ F.V, mem (dgExtToIntBase dgFPtr vCap + v) ∈ F.V ∧
      mem (dgIntToExtBase dgFPtr vCap + mem (dgExtToIntBase dgFPtr vCap + v)) = v)
    (hincL : ∀ s < vCap,
      IsDoublyLinkedList mem (dgHePrevBase dgFPtr vCap eCapF) (dgHeNextBase dgFPtr vCap eCapF)
        (dgIncHeadBase dgFPtr vCap + s) (2 * eCapF) (incL s) ∧
      mem (dgSlotDegBase dgFPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCapF ∧ h / 2 ∈ F.E ∧
        (if h % 2 = 0 then mem (dgExtToIntBase dgFPtr vCap + F.tail (h / 2))
         else mem (dgExtToIntBase dgFPtr vCap + F.head (h / 2))) = s)
    {u₀ : ℕ} :
    let C := F.V.filter fun v => F.Connected v u₀
    let EC := F.E.filter fun e => F.Connected (F.tail e) u₀
    ∑ v ∈ C, (incL (mem (dgExtToIntBase dgFPtr vCap + v))).length = 2 * EC.card := by
  intro C EC
  set f : ℕ → Finset ℕ := fun v => (incL (mem (dgExtToIntBase dgFPtr vCap + v))).toFinset
  have hlen : ∀ v ∈ C, (incL (mem (dgExtToIntBase dgFPtr vCap + v))).length = (f v).card := by
    intro v hv
    have hvF := (Finset.mem_filter.mp hv).1
    have hs_lt := hvCap _ (hExtToInt v hvF).1
    exact (List.toFinset_card_of_nodup (hincL _ hs_lt).1.1).symm
  rw [Finset.sum_congr rfl hlen]
  have hdisj : (C : Set ℕ).PairwiseDisjoint f := by
    intro v₁ hv₁ v₂ hv₂ hne
    refine Finset.disjoint_left.mpr fun he h1 h2 => hne ?_
    have hv₁F := (Finset.mem_filter.mp hv₁).1
    have hv₂F := (Finset.mem_filter.mp hv₂).1
    have hs₁ := hvCap _ (hExtToInt v₁ hv₁F).1
    have hs₂ := hvCap _ (hExtToInt v₂ hv₂F).1
    have he1 := ((hincL _ hs₁).2.2 he).mp (List.mem_toFinset.mp h1)
    have he2 := ((hincL _ hs₂).2.2 he).mp (List.mem_toFinset.mp h2)
    have hseq : mem (dgExtToIntBase dgFPtr vCap + v₁) = mem (dgExtToIntBase dgFPtr vCap + v₂) :=
      he1.2.2.symm.trans he2.2.2
    have h1' := (hExtToInt v₁ hv₁F).2
    rw [hseq, (hExtToInt v₂ hv₂F).2] at h1'
    exact h1'.symm
  rw [← Finset.card_biUnion hdisj]
  have hbi : C.biUnion f = EC.biUnion (fun e => ({2 * e, 2 * e + 1} : Finset ℕ)) := by
    ext he
    simp only [Finset.mem_biUnion, f, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨v, hv, hhe⟩
      obtain ⟨hvF, hvC⟩ := Finset.mem_filter.mp hv
      have hs_lt := hvCap _ (hExtToInt v hvF).1
      obtain ⟨_, heE, hslot⟩ := ((hincL _ hs_lt).2.2 he).mp hhe
      have hte := (hFval _ heE).1
      have hheV := (hFval _ heE).2
      by_cases hmod : he % 2 = 0
      · simp only [hmod, ↓reduceIte] at hslot
        have htv : F.tail (he / 2) = v := by
          have h1 := (hExtToInt _ hte).2
          rw [hslot, (hExtToInt v hvF).2] at h1; exact h1.symm
        exact ⟨he / 2, Finset.mem_filter.mpr ⟨heE, htv ▸ hvC⟩, Or.inl (by omega)⟩
      · simp only [hmod, ↓reduceIte] at hslot
        have hhv : F.head (he / 2) = v := by
          have h1 := (hExtToInt _ hheV).2
          rw [hslot, (hExtToInt v hvF).2] at h1; exact h1.symm
        have htc : F.Connected (F.tail (he / 2)) u₀ :=
          connected_trans ⟨[(he / 2, true)], .cons heE rfl (.nil _)⟩
            (by dsimp [MGraph.dst]; rw [hhv]; exact hvC)
        exact ⟨he / 2, Finset.mem_filter.mpr ⟨heE, htc⟩, Or.inr (by omega)⟩
    · rintro ⟨e, heEC, rfl | rfl⟩
      · obtain ⟨heE, htc⟩ := Finset.mem_filter.mp heEC
        have hte := (hFval e heE).1
        have hs_lt := hvCap _ (hExtToInt _ hte).1
        refine ⟨F.tail e, Finset.mem_filter.mpr ⟨hte, htc⟩, ((hincL _ hs_lt).2.2 (2 * e)).mpr ?_⟩
        refine ⟨by have := heCap e heE; omega, by simpa using heE, ?_⟩
        simp
      · obtain ⟨heE, htc⟩ := Finset.mem_filter.mp heEC
        have hheV := (hFval e heE).2
        have hhc : F.Connected (F.head e) u₀ :=
          connected_trans ⟨[(e, false)], .cons heE rfl (.nil _)⟩ htc
        have hs_lt := hvCap _ (hExtToInt _ hheV).1
        refine ⟨F.head e, Finset.mem_filter.mpr ⟨hheV, hhc⟩,
          ((hincL _ hs_lt).2.2 (2 * e + 1)).mpr ?_⟩
        refine ⟨by have := heCap e heE; omega, by rw [show (2 * e + 1) / 2 = e by omega]; exact heE, ?_⟩
        simp [show (2 * e + 1) % 2 = 1 by omega, show (2 * e + 1) / 2 = e by omega]
  rw [hbi, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun e _ => Finset.card_pair (by omega : 2 * e ≠ 2 * e + 1)]
    simp [mul_comm]
  · intro e₁ _ e₂ _ hne
    refine Finset.disjoint_left.mpr fun x h1 h2 => hne ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    omega

/-! ## Pure single-side BFS invariant -/

/-- Pure invariant of one side of half-edge-level BFS starting at `u₀ ∈ F.V`. -/
structure BfsInv (F : MGraph) (slotOf : ℕ → ℕ) (incL : ℕ → List ℕ) (u₀ : ℕ)
    (q : List ℕ) (qHead : ℕ) (remHe : List ℕ) (steps : ℕ) : Prop where
  hq_nd : q.Nodup
  hq_ne : 1 ≤ q.length
  hq_0 : q[0]'(by omega) = u₀
  hq_sub : ∀ v ∈ q, v ∈ F.V ∧ F.Connected v u₀
  hqh_le : qHead ≤ q.length
  hrem_zero : qHead = 0 → remHe = []
  hrem_pos : ∀ (hpos : 0 < qHead), ∃ pref : List ℕ,
    incL (slotOf (q[qHead - 1]'(by omega))) = pref ++ remHe ∧
    ∀ he ∈ pref, heOther F he ∈ q
  hdone_prev : ∀ k (hk : k + 1 < qHead),
    ∀ he ∈ incL (slotOf (q[k]'(by omega))), heOther F he ∈ q
  hsteps_eq : steps + remHe.length =
    qHead + (Finset.range qHead).sum (fun k => (incL (slotOf (q.getD k 0))).length)
  hq_len_le : q.length ≤ steps + 1

lemma bfsInv_init {F : MGraph} {slotOf : ℕ → ℕ} {incL : ℕ → List ℕ} {u₀ : ℕ}
    (hu₀ : u₀ ∈ F.V) :
    BfsInv F slotOf incL u₀ [u₀] 0 [] 0 where
  hq_nd := List.nodup_singleton u₀
  hq_ne := by simp
  hq_0 := rfl
  hq_sub := fun v hv => by rw [List.mem_singleton.mp hv]; exact ⟨hu₀, connected_refl F u₀⟩
  hqh_le := Nat.zero_le _
  hrem_zero := fun _ => rfl
  hrem_pos := fun h => by omega
  hdone_prev := fun _ hk => by omega
  hsteps_eq := by simp
  hq_len_le := by simp

open Classical in
/-- Step count of a BFS in a forest component `C` is always at most `3 * E_C.card + 1`. -/
lemma BfsInv.steps_le {mem : ℕ → ℕ} {dgFPtr vCap eCapF u₀ qHead steps : ℕ} {F : MGraph}
    {incL : ℕ → List ℕ} {q remHe : List ℕ}
    (hF : F.IsForest) (hu₀ : u₀ ∈ F.V)
    (hvCap : ∀ v ∈ F.V, v < vCap) (heCap : ∀ e ∈ F.E, e < eCapF)
    (hExtToInt : ∀ v ∈ F.V, mem (dgExtToIntBase dgFPtr vCap + v) ∈ F.V ∧
      mem (dgIntToExtBase dgFPtr vCap + mem (dgExtToIntBase dgFPtr vCap + v)) = v)
    (hincL : ∀ s < vCap,
      IsDoublyLinkedList mem (dgHePrevBase dgFPtr vCap eCapF) (dgHeNextBase dgFPtr vCap eCapF)
        (dgIncHeadBase dgFPtr vCap + s) (2 * eCapF) (incL s) ∧
      mem (dgSlotDegBase dgFPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCapF ∧ h / 2 ∈ F.E ∧
        (if h % 2 = 0 then mem (dgExtToIntBase dgFPtr vCap + F.tail (h / 2))
         else mem (dgExtToIntBase dgFPtr vCap + F.head (h / 2))) = s)
    (hB : BfsInv F (fun v => mem (dgExtToIntBase dgFPtr vCap + v)) incL u₀ q qHead remHe steps) :
    steps ≤ 3 * (F.E.filter fun e => F.Connected (F.tail e) u₀).card + 1 := by
  set C := F.V.filter fun v => F.Connected v u₀
  set EC := F.E.filter fun e => F.Connected (F.tail e) u₀
  have hC_card : C.card = EC.card + 1 := forest_comp_card_eq_edges_succ hF hu₀
  have hq_sub_C : q.toFinset ⊆ C := fun v hv =>
    Finset.mem_filter.mpr (hB.hq_sub v (List.mem_toFinset.mp hv))
  have hq_le_C : q.length ≤ C.card := by
    rw [← List.toFinset_card_of_nodup hB.hq_nd]
    exact Finset.card_le_card hq_sub_C
  have hqh_le := hB.hqh_le
  have hsum_deg : (Finset.range qHead).sum (fun k =>
      (incL (mem (dgExtToIntBase dgFPtr vCap + q.getD k 0))).length) ≤ 2 * EC.card := by
    have htake_nd : (q.take qHead).Nodup := hB.hq_nd.sublist (List.take_sublist _ _)
    have htake_sub : (q.take qHead).toFinset ⊆ C := fun v hv =>
      hq_sub_C (List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hv)))
    have hsum_eq : (Finset.range qHead).sum (fun k =>
        (incL (mem (dgExtToIntBase dgFPtr vCap + q.getD k 0))).length) =
        ∑ v ∈ (q.take qHead).toFinset, (incL (mem (dgExtToIntBase dgFPtr vCap + v))).length := by
      have hlen_t : (q.take qHead).length = qHead := List.length_take_of_le hqh_le
      have haux : ∀ L : List ℕ,
          (Finset.range L.length).sum (fun k =>
            (incL (mem (dgExtToIntBase dgFPtr vCap + L.getD k 0))).length) =
          (L.map fun v => (incL (mem (dgExtToIntBase dgFPtr vCap + v))).length).sum := by
        intro L
        rw [List.sum_eq_foldr]
        induction L with
        | nil => simp
        | cons a tl ih =>
          simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
            List.getD_cons_zero, List.map_cons, List.foldr_cons]
          rw [ih, Nat.add_comm]
      have hmap : (Finset.range qHead).sum (fun k =>
          (incL (mem (dgExtToIntBase dgFPtr vCap + q.getD k 0))).length) =
          ((q.take qHead).map fun v => (incL (mem (dgExtToIntBase dgFPtr vCap + v))).length).sum := by
        rw [← haux (q.take qHead)]
        refine Finset.sum_congr (by rw [hlen_t]) fun k hk => ?_
        have hk' : k < (q.take qHead).length := Finset.mem_range.mp hk
        rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hk', List.getElem_take]
      rw [hmap, ← List.sum_toFinset _ htake_nd]
    rw [hsum_eq, ← sum_incL_comp_eq_two_mul_edges hF.1 hvCap heCap hExtToInt hincL (u₀ := u₀)]
    exact Finset.sum_le_sum_of_subset htake_sub
  have hqh_le_C : qHead ≤ C.card := le_trans hqh_le hq_le_C
  have := hB.hsteps_eq
  omega

open Classical in
/-- When BFS terminates (`qHead = q.length ∧ remHe = []`), `q` lists the entire component `C` of
`u₀`, `q.length = E_C.card + 1`, and `steps = 3 * E_C.card + 1`. -/
lemma BfsInv.done_eq {mem : ℕ → ℕ} {dgFPtr vCap eCapF u₀ qHead steps : ℕ} {F : MGraph}
    {incL : ℕ → List ℕ} {q remHe : List ℕ}
    (hF : F.IsForest) (hu₀ : u₀ ∈ F.V)
    (hvCap : ∀ v ∈ F.V, v < vCap) (heCap : ∀ e ∈ F.E, e < eCapF)
    (hExtToInt : ∀ v ∈ F.V, mem (dgExtToIntBase dgFPtr vCap + v) ∈ F.V ∧
      mem (dgIntToExtBase dgFPtr vCap + mem (dgExtToIntBase dgFPtr vCap + v)) = v)
    (hincL : ∀ s < vCap,
      IsDoublyLinkedList mem (dgHePrevBase dgFPtr vCap eCapF) (dgHeNextBase dgFPtr vCap eCapF)
        (dgIncHeadBase dgFPtr vCap + s) (2 * eCapF) (incL s) ∧
      mem (dgSlotDegBase dgFPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCapF ∧ h / 2 ∈ F.E ∧
        (if h % 2 = 0 then mem (dgExtToIntBase dgFPtr vCap + F.tail (h / 2))
         else mem (dgExtToIntBase dgFPtr vCap + F.head (h / 2))) = s)
    (hB : BfsInv F (fun v => mem (dgExtToIntBase dgFPtr vCap + v)) incL u₀ q qHead remHe steps)
    (hqh_eq : qHead = q.length) (hrem_eq : remHe = []) :
    (∀ v, v ∈ q ↔ v ∈ F.V ∧ F.Connected v u₀) ∧
    q.length = (F.E.filter fun e => F.Connected (F.tail e) u₀).card + 1 ∧
    steps = 3 * (F.E.filter fun e => F.Connected (F.tail e) u₀).card + 1 := by
  subst hrem_eq
  set C := F.V.filter fun v => F.Connected v u₀
  set EC := F.E.filter fun e => F.Connected (F.tail e) u₀
  have hq_ne := hB.hq_ne
  have hclosed : ∀ v ∈ q, ∀ e ∈ F.E,
      (F.tail e = v → F.head e ∈ q) ∧ (F.head e = v → F.tail e ∈ q) := by
    intro v hv e heE
    obtain ⟨k, hk, hvk⟩ := List.mem_iff_getElem.mp hv
    have hall : ∀ he ∈ incL (mem (dgExtToIntBase dgFPtr vCap + v)), heOther F he ∈ q := by
      intro he hhe
      by_cases hlast : k + 1 < qHead
      · exact hB.hdone_prev k hlast he (by rwa [hvk])
      · have hk_eq : k = qHead - 1 := by omega
        obtain ⟨pref, hpref_eq, hpref_mem⟩ := hB.hrem_pos (by omega)
        rw [List.append_nil] at hpref_eq
        have hq_eq : q[qHead - 1]'(by omega) = v := by
          have : q[qHead - 1]'(by omega) = q[k]'hk := congrArg (fun idx => q.getD idx 0) hk_eq.symm
            |> fun h => by rwa [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hk] at h
          exact this.trans hvk
        apply hpref_mem he
        rw [← hpref_eq, hq_eq]
        exact hhe
    have hvF : v ∈ F.V := (hB.hq_sub v hv).1
    have hs_lt := hvCap _ (hExtToInt v hvF).1
    refine ⟨fun ht => ?_, fun hh => ?_⟩
    · have h2e : 2 * e ∈ incL (mem (dgExtToIntBase dgFPtr vCap + v)) :=
        ((hincL _ hs_lt).2.2 (2 * e)).mpr
          ⟨by have := heCap e heE; omega, by simpa using heE, by simp [ht]⟩
      have := hall (2 * e) h2e
      simpa [heOther] using this
    · have h2e1 : 2 * e + 1 ∈ incL (mem (dgExtToIntBase dgFPtr vCap + v)) :=
        ((hincL _ hs_lt).2.2 (2 * e + 1)).mpr
          ⟨by have := heCap e heE; omega,
            by rw [show (2 * e + 1) / 2 = e by omega]; exact heE,
            by simp [show (2 * e + 1) % 2 = 1 by omega, show (2 * e + 1) / 2 = e by omega, hh]⟩
      have := hall (2 * e + 1) h2e1
      simpa [heOther, show (2 * e + 1) % 2 = 1 by omega, show (2 * e + 1) / 2 = e by omega] using this
  have hmem_iff : ∀ v, v ∈ q ↔ v ∈ F.V ∧ F.Connected v u₀ := by
    intro v
    constructor
    · exact hB.hq_sub v
    · rintro ⟨_, hconn⟩
      obtain ⟨P, hP⟩ := connected_symm hconn
      have hu₀_in : u₀ ∈ q := hB.hq_0 ▸ List.getElem_mem (by omega)
      have hwalk_mem : ∀ {s t : ℕ} {Q : List (ℕ × Bool)}, F.IsWalk s t Q → s ∈ q → t ∈ q := by
        intro s t Q hQ
        induction hQ with
        | nil _ => exact id
        | @cons a b x xs hxE hsrc _ ih =>
          intro ha
          apply ih
          rcases x with ⟨e, _ | _⟩ <;> simp only [MGraph.src, MGraph.dst] at hsrc ⊢
          · exact (hclosed a ha e hxE).2 hsrc
          · exact (hclosed a ha e hxE).1 hsrc
      exact hwalk_mem hP hu₀_in
  have hto : q.toFinset = C := by
    ext v; simp [C, hmem_iff]
  have hC_card : C.card = EC.card + 1 := forest_comp_card_eq_edges_succ hF hu₀
  have hq_len : q.length = EC.card + 1 := by
    rw [← List.toFinset_card_of_nodup hB.hq_nd, hto, hC_card]
  have hsum_eq : (Finset.range qHead).sum (fun k =>
      (incL (mem (dgExtToIntBase dgFPtr vCap + q.getD k 0))).length) = 2 * EC.card := by
    rw [hqh_eq]
    have hmap : (Finset.range q.length).sum (fun k =>
        (incL (mem (dgExtToIntBase dgFPtr vCap + q.getD k 0))).length) =
        (q.map fun v => (incL (mem (dgExtToIntBase dgFPtr vCap + v))).length).sum := by
      have haux : ∀ L : List ℕ,
          (Finset.range L.length).sum (fun k =>
            (incL (mem (dgExtToIntBase dgFPtr vCap + L.getD k 0))).length) =
          (L.map fun v => (incL (mem (dgExtToIntBase dgFPtr vCap + v))).length).sum := by
        intro L
        rw [List.sum_eq_foldr]
        induction L with
        | nil => simp
        | cons a tl ih =>
          simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
            List.getD_cons_zero, List.map_cons, List.foldr_cons]
          rw [ih, Nat.add_comm]
      exact haux q
    rw [hmap, ← List.sum_toFinset _ hB.hq_nd, hto]
    exact sum_incL_comp_eq_two_mul_edges hF.1 hvCap heCap hExtToInt hincL
  have hst := hB.hsteps_eq
  rw [List.length_nil, add_zero, hsum_eq, hqh_eq, hq_len] at hst
  exact ⟨hmem_iff, hq_len, by omega⟩

/-- Pop micro-step (`remHe = []`, `qHead < q.length`) preserves `BfsInv` with `steps + 1`. -/
lemma BfsInv.step_pop {F : MGraph} {slotOf : ℕ → ℕ} {incL : ℕ → List ℕ} {u₀ qHead steps : ℕ}
    {q : List ℕ}
    (hB : BfsInv F slotOf incL u₀ q qHead [] steps) (hqh : qHead < q.length) :
    BfsInv F slotOf incL u₀ q (qHead + 1) (incL (slotOf (q[qHead]'hqh))) (steps + 1) := by
  refine
    { hq_nd := hB.hq_nd
      hq_ne := hB.hq_ne
      hq_0 := hB.hq_0
      hq_sub := hB.hq_sub
      hqh_le := hqh
      hrem_zero := fun h => by omega
      hrem_pos := fun _ => ⟨[], by simp, fun _ h => by cases h⟩
      hdone_prev := fun k hk he hhe => ?_
      hsteps_eq := ?_
      hq_len_le := by have := hB.hq_len_le; omega }
  · by_cases hlt : k + 1 < qHead
    · exact hB.hdone_prev k hlt he hhe
    · have hk_eq : k = qHead - 1 := by omega
      obtain ⟨pref, hpref, hpm⟩ := hB.hrem_pos (by omega)
      rw [List.append_nil] at hpref
      apply hpm he
      simpa [← hpref, hk_eq] using hhe
  · rw [Finset.sum_range_succ, List.getD_eq_getElem _ _ hqh]
    have hst := hB.hsteps_eq
    simp only [List.length_nil, add_zero] at hst
    omega

/-- Edge micro-step (`remHe = he :: tl`) preserves `BfsInv` with `steps + 1`. -/
lemma BfsInv.step_edge {F : MGraph} {slotOf : ℕ → ℕ} {incL : ℕ → List ℕ} {u₀ qHead steps he : ℕ}
    {q tl : List ℕ}
    (hB : BfsInv F slotOf incL u₀ q qHead (he :: tl) steps)
    (hyV : heOther F he ∈ F.V) (hyConn : F.Connected (heOther F he) u₀) :
    let y := heOther F he
    let q' := if y ∈ q then q else q ++ [y]
    BfsInv F slotOf incL u₀ q' qHead tl (steps + 1) := by
  intro y q'
  have hq_ne := hB.hq_ne
  have hqh_le := hB.hqh_le
  have hqh_pos : 0 < qHead := by
    by_contra h0
    have h0' : qHead = 0 := by omega
    have := hB.hrem_zero h0'
    cases this
  have hq_sub_q' : ∀ x ∈ q, x ∈ q' := fun x hx => by
    dsimp only [q']; split_ifs
    · exact hx
    · exact List.mem_append_left _ hx
  have hy_in_q' : y ∈ q' := by
    dsimp only [q']; split_ifs with h
    · exact h
    · exact List.mem_append_right _ List.mem_cons_self
  have hq'_len : q.length ≤ q'.length := by
    dsimp only [q']; split_ifs
    · exact le_rfl
    · simp
  have hq'_get : ∀ k (hk : k < q.length), q'[k]'(lt_of_lt_of_le hk hq'_len) = q[k] := by
    intro k hk
    dsimp only [q']; split_ifs
    · rfl
    · exact List.getElem_append_left hk
  have hq'_getD : ∀ k < q.length, q'.getD k 0 = q.getD k 0 := fun k hk => by
    rw [List.getD_eq_getElem _ _ (lt_of_lt_of_le hk hq'_len), List.getD_eq_getElem _ _ hk,
      hq'_get k hk]
  refine
    { hq_nd := by
        dsimp only [q']; split_ifs with h
        · exact hB.hq_nd
        · exact List.nodup_append.mpr ⟨hB.hq_nd, List.nodup_singleton y,
            fun a ha b hb => by rw [List.mem_singleton.mp hb]; intro heq; subst heq; exact h ha⟩
      hq_ne := le_trans hB.hq_ne hq'_len
      hq_0 := (hq'_get 0 (by omega)).trans hB.hq_0
      hq_sub := fun v hv => by
        dsimp only [q'] at hv; split_ifs at hv
        · exact hB.hq_sub v hv
        · rw [List.mem_append, List.mem_singleton] at hv
          rcases hv with h1 | rfl
          · exact hB.hq_sub v h1
          · exact ⟨hyV, hyConn⟩
      hqh_le := le_trans hB.hqh_le hq'_len
      hrem_zero := fun h => by omega
      hrem_pos := fun _ => by
        obtain ⟨pref, hpref, hpm⟩ := hB.hrem_pos hqh_pos
        refine ⟨pref ++ [he], ?_, fun h hh => ?_⟩
        · rw [hq'_get (qHead - 1) (by omega), hpref]; simp
        · rw [List.mem_append, List.mem_singleton] at hh
          rcases hh with h1 | rfl
          · exact hq_sub_q' _ (hpm h h1)
          · exact hy_in_q'
      hdone_prev := fun k hk h hh => by
        rw [hq'_get k (by omega)] at hh
        exact hq_sub_q' _ (hB.hdone_prev k hk h hh)
      hsteps_eq := by
        have hsum_congr : (Finset.range qHead).sum (fun k => (incL (slotOf (q'.getD k 0))).length) =
            (Finset.range qHead).sum (fun k => (incL (slotOf (q.getD k 0))).length) :=
          Finset.sum_congr rfl fun k hk => by
            rw [hq'_getD k (lt_of_lt_of_le (Finset.mem_range.mp hk) hB.hqh_le)]
        rw [hsum_congr]
        have hst := hB.hsteps_eq
        simp only [List.length_cons] at hst
        omega
      hq_len_le := by
        have h1 := hB.hq_len_le
        dsimp only [q']; split_ifs <;> simp <;> omega }

end

end MinCostFlow.LSF.Program
