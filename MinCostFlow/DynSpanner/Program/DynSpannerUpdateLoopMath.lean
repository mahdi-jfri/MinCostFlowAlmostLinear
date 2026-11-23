module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepOut
public import MinCostFlow.DynSpanner.Program.DynSpannerStepHelpers
public import MinCostFlow.DynSpanner.Program.DynSpannerStepZeroAux

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Mathematical lemmas for the batch update loop (`DynSpannerUpdateLoopMath`)

Proves the pure graph and model identities needed to lift single-step `StepOutPost` contracts to
the batch update loop `DynSpanner.update`:

* `applyBatch_perm_step_UH`: every permutation `uhActual` of `(step st u sparsify).UH` produces
  the exact same spanner graph `st.H.applyBatch uhActual = (step st u sparsify).state.H`, because
  all updates in `(step st u sparsify).UH` pairwise commute under `MGraph.applyUpdate`.
* `batchBodyAt_perm_step_UH_words_le`: if `BatchBodyAt mem a st.H uhActual uhWords` and
  `uhActual.Perm (step st u sparsify).UH`, then `uhWords ≤ len + 4 * (step st u sparsify).UH.length`
  when `UpdateAt mem0 updPtr st.G u len`.
* `update_take_spec`: exact characterization of `update st₀ (U.take i) sparsify` in terms of
  `runState` and `runStepOut` for `i ≤ U.length`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Pairwise commutation of `step.UH` -/

private lemma mgraph_ext {G₁ G₂ : MGraph} (hV : G₁.V = G₂.V) (hE : G₁.E = G₂.E)
    (ht : ∀ e, G₁.tail e = G₂.tail e) (hh : ∀ e, G₁.head e = G₂.head e) : G₁ = G₂ := by
  have ht' : G₁.tail = G₂.tail := funext ht
  have hh' : G₁.head = G₂.head := funext hh
  cases G₁; cases G₂; simp_all

/-- Two graph updates commute under `MGraph.applyUpdate`. -/
def UpdatesCommute (a b : Update) : Prop :=
  ∀ G : MGraph, (G.applyUpdate a).applyUpdate b = (G.applyUpdate b).applyUpdate a

private lemma updatesCommute_symm {a b : Update} (h : UpdatesCommute a b) : UpdatesCommute b a :=
  fun G => (h G).symm

private lemma updatesCommute_del_del (e₁ e₂ : ℕ) :
    UpdatesCommute (.delete e₁) (.delete e₂) := by
  intro G
  refine mgraph_ext rfl ?_ (fun _ => rfl) (fun _ => rfl)
  simp only [MGraph.applyUpdate, Finset.erase_right_comm]

private lemma updatesCommute_ins_ins {e₁ e₂ x₁ y₁ x₂ y₂ : ℕ} (hne : e₁ ≠ e₂) :
    UpdatesCommute (.insert e₁ x₁ y₁) (.insert e₂ x₂ y₂) := by
  intro G
  refine mgraph_ext rfl ?_ (fun e => ?_) (fun e => ?_)
  · simp only [MGraph.applyUpdate, Finset.insert_comm]
  · simp only [MGraph.applyUpdate, Function.update]
    by_cases h1 : e = e₁ <;> by_cases h2 : e = e₂ <;> simp_all
  · simp only [MGraph.applyUpdate, Function.update]
    by_cases h1 : e = e₁ <;> by_cases h2 : e = e₂ <;> simp_all

private lemma updatesCommute_del_ins {e₁ e₂ x₂ y₂ : ℕ} (hne : e₁ ≠ e₂) :
    UpdatesCommute (.delete e₁) (.insert e₂ x₂ y₂) := by
  intro G
  refine mgraph_ext rfl ?_ (fun _ => rfl) (fun _ => rfl)
  simp only [MGraph.applyUpdate]
  ext e
  simp only [Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨hne.symm, Or.inl rfl⟩
    · exact ⟨h1, Or.inr h2⟩
  · rintro ⟨h1, rfl | h2⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨h1, h2⟩

private lemma updatesCommute_split_del (v v' : ℕ) (St Sh : Finset ℕ) (e : ℕ) :
    UpdatesCommute (.split v v' St Sh) (.delete e) := by
  intro G
  exact mgraph_ext rfl rfl (fun _ => rfl) (fun _ => rfl)

private lemma updatesCommute_split_ins {v v' e x y : ℕ} {St Sh : Finset ℕ}
    (hSt : e ∉ St) (hSh : e ∉ Sh) :
    UpdatesCommute (.split v v' St Sh) (.insert e x y) := by
  intro G
  refine mgraph_ext rfl rfl (fun e' => ?_) (fun e' => ?_)
  · simp only [MGraph.applyUpdate, Function.update]
    by_cases he : e' = e
    · subst he; simp [hSt]
    · simp [he]
  · simp only [MGraph.applyUpdate, Function.update]
    by_cases he : e' = e
    · subst he; simp [hSh]
    · simp [he]

/-- If every pair of elements in `l` (at distinct positions) commutes, then any permutation of `l`
applies to the same graph under `MGraph.applyBatch`. -/
private lemma applyBatch_perm_of_pairwise :
    ∀ {l₁ l₂ : List Update}, l₁.Perm l₂ → l₁.Pairwise UpdatesCommute →
      ∀ G : MGraph, G.applyBatch l₁ = G.applyBatch l₂ := by
  intro l₁ l₂ hperm
  induction hperm with
  | nil => intro _ _; rfl
  | cons a hp ih =>
    intro hpw G
    simp only [MGraph.applyBatch, List.foldl_cons]
    exact ih (List.pairwise_cons.mp hpw).2 (G.applyUpdate a)
  | swap x y l =>
    intro hpw G
    have hxy : UpdatesCommute y x := (List.pairwise_cons.mp hpw).1 x List.mem_cons_self
    simp only [MGraph.applyBatch, List.foldl_cons, hxy G]
  | trans hp₁ hp₂ ih₁ ih₂ =>
    intro hpw G
    have hpw2 : List.Pairwise UpdatesCommute _ :=
      hp₁.pairwise_iff (fun {_ _} h => updatesCommute_symm h) |>.mp hpw
    exact (ih₁ hpw G).trans (ih₂ hpw2 G)

private lemma pairwise_diffBatch_UH {G H : MGraph} {u : Update} {H_new_E : Finset ℕ}
    (hdu : isDelOrSplit u) (hNewSub : H_new_E ⊆ (G.applyUpdate u).E) :
    let G' := G.applyUpdate u
    let uhPref := restrictUpdate u H
    let H_mid := H.applyBatch uhPref
    (uhPref ++ ((H_mid.E \ H_new_E).sort (· ≤ ·)).map Update.delete ++
      ((H_new_E \ H_mid.E).sort (· ≤ ·)).map
        (fun e => Update.insert e (G'.tail e) (G'.head e))).Pairwise UpdatesCommute := by
  intro G' uhPref H_mid
  set lDel := (H_mid.E \ H_new_E).sort (· ≤ ·)
  set lIns := (H_new_E \ H_mid.E).sort (· ≤ ·)
  have hDel_nd : lDel.Nodup := Finset.sort_nodup _ _
  have hIns_nd : lIns.Nodup := Finset.sort_nodup _ _
  have hDel_mem : ∀ e, e ∈ lDel ↔ e ∈ H_mid.E \ H_new_E := fun e => Finset.mem_sort _
  have hIns_mem : ∀ e, e ∈ lIns ↔ e ∈ H_new_E \ H_mid.E := fun e => Finset.mem_sort _
  have hpw_del : (lDel.map Update.delete).Pairwise UpdatesCommute :=
    List.pairwise_map.mpr (hDel_nd.imp fun _ => updatesCommute_del_del _ _)
  have hpw_ins : (lIns.map fun e => Update.insert e (G'.tail e) (G'.head e)).Pairwise
      UpdatesCommute :=
    List.pairwise_map.mpr (hIns_nd.imp fun hne => updatesCommute_ins_ins hne)
  have hpw_di : ∀ a ∈ lDel.map Update.delete,
      ∀ b ∈ lIns.map (fun e => Update.insert e (G'.tail e) (G'.head e)),
      UpdatesCommute a b := by
    rintro _ ha _ hb
    obtain ⟨e₁, he₁, rfl⟩ := List.mem_map.mp ha
    obtain ⟨e₂, he₂, rfl⟩ := List.mem_map.mp hb
    have h1 := (Finset.mem_sdiff.mp ((hDel_mem e₁).mp he₁)).1
    have h2 := (Finset.mem_sdiff.mp ((hIns_mem e₂).mp he₂)).2
    exact updatesCommute_del_ins (fun heq => h2 (heq ▸ h1))
  have hpw_tail : (lDel.map Update.delete ++
      lIns.map fun e => Update.insert e (G'.tail e) (G'.head e)).Pairwise UpdatesCommute :=
    List.pairwise_append.mpr ⟨hpw_del, hpw_ins, hpw_di⟩
  rw [List.append_assoc]
  refine List.pairwise_append.mpr ⟨?_, hpw_tail, ?_⟩
  · cases u with
    | insert _ _ _ => exact hdu.elim
    | delete e =>
      by_cases he : e ∈ H.E <;> simp [uhPref, restrictUpdate, he]
    | split _ _ _ _ => simp [uhPref, restrictUpdate]
  · intro a ha b hb
    cases u with
    | insert _ _ _ => exact hdu.elim
    | delete e₀ =>
      by_cases he₀ : e₀ ∈ H.E
      · simp only [uhPref, restrictUpdate, he₀, ↓reduceIte, List.mem_singleton] at ha
        subst ha
        rcases List.mem_append.mp hb with hb | hb
        · obtain ⟨e₁, _, rfl⟩ := List.mem_map.mp hb
          exact updatesCommute_del_del e₀ e₁
        · obtain ⟨e₂, he₂, rfl⟩ := List.mem_map.mp hb
          have h2G : e₂ ∈ G'.E := hNewSub (Finset.mem_sdiff.mp ((hIns_mem e₂).mp he₂)).1
          have hne : e₀ ≠ e₂ := fun heq => by
            subst heq; simp [G', MGraph.applyUpdate] at h2G
          exact updatesCommute_del_ins hne
      · simp [uhPref, restrictUpdate, he₀] at ha
    | split v v' St Sh =>
      simp only [uhPref, restrictUpdate, List.mem_singleton] at ha
      subst ha
      have hHmid_E : H_mid.E = H.E := by
        simp [H_mid, uhPref, restrictUpdate, MGraph.applyBatch, MGraph.applyUpdate]
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨e₁, _, rfl⟩ := List.mem_map.mp hb
        exact updatesCommute_split_del v v' (St ∩ H.E) (Sh ∩ H.E) e₁
      · obtain ⟨e₂, he₂, rfl⟩ := List.mem_map.mp hb
        have hnotH : e₂ ∉ H.E := hHmid_E ▸ (Finset.mem_sdiff.mp ((hIns_mem e₂).mp he₂)).2
        exact updatesCommute_split_ins
          (fun h => hnotH (Finset.mem_inter.mp h).2)
          (fun h => hnotH (Finset.mem_inter.mp h).2)

/-- Every permutation `uhActual` of `(step st u sparsify).UH` transforms `st.H` into
`(step st u sparsify).state.H`. -/
theorem applyBatch_perm_step_UH {G₀ : MGraph} {L q mMax : ℕ} {P : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    {us : List Update} {k : ℕ} {u : Update} {uhActual : List Update}
    (hVG₀ : G₀.IsValid) (hL : 1 ≤ L) (hq : 1 ≤ q) (hGm₀ : G₀.m ≤ mMax)
    (hSpec : SparsifySpec mMax P sparsify)
    (hBV : G₀.BatchIsValid us) (hds : ∀ u' ∈ us, isDelOrSplit u')
    (hu_some : us[k]? = some u)
    (hPref : ∀ s ≤ k, SnapInv G₀ L q mMax P sparsify us s)
    (hPerm : uhActual.Perm (step (runState (L := L) G₀ q sparsify us k) u sparsify).UH) :
    let st := runState (L := L) G₀ q sparsify us k
    let res := step st u sparsify
    st.H.applyBatch uhActual = res.state.H := by
  intro st res
  obtain ⟨_, _, hUk⟩ := batchIsValid_take us G₀ k hBV hds
  have hdu := (hUk u hu_some).2
  have hnext := (step_inv hVG₀ hL hq hGm₀ hSpec hBV hds hu_some hPref).1
  have hst1 : runState (L := L) G₀ q sparsify us (k + 1) = res.state := by
    simp only [runState, res, st, hu_some]
  have hH'_eq : res.state.H = st.H.applyBatch res.UH := by
    dsimp only [res, step]; split_ifs <;> rfl
  have hU_sub : unionEdgesLt res.state.H_level (L + 1) ⊆ (st.G.applyUpdate u).E := by
    have hsub := hnext.H_sub
    have hHE := hnext.H_E
    have hG1 := hnext.G_eq
    rw [hst1] at hsub hHE hG1
    have hGres : res.state.G = st.G.applyUpdate u := by
      dsimp only [res, step]; split_ifs <;> rfl
    rw [← hHE]
    rw [hG1.symm.trans hGres] at hsub
    exact hsub.2.1
  have hpw : res.UH.Pairwise UpdatesCommute := by
    by_cases hj0 : chooseLevel L st.q (st.t + 1) = 0
    · have hsub0 : (initAt (st.G.applyUpdate u) L st.q (st.t + 1) sparsify).state.H.E ⊆
          (st.G.applyUpdate u).E := fun e he => hU_sub (by
        simp only [unionEdgesLt, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨0, Nat.zero_lt_succ L⟩, Nat.zero_lt_succ L, ?_⟩
        simpa [res, step, hj0, initAt] using he)
      have hres_uh : res.UH = restrictUpdate u st.H ++
          (((st.H.applyBatch (restrictUpdate u st.H)).E \
            (initAt (st.G.applyUpdate u) L st.q (st.t + 1) sparsify).state.H.E).sort (· ≤ ·)).map
            Update.delete ++
          (((initAt (st.G.applyUpdate u) L st.q (st.t + 1) sparsify).state.H.E \
            (st.H.applyBatch (restrictUpdate u st.H)).E).sort (· ≤ ·)).map
            fun e => Update.insert e ((st.G.applyUpdate u).tail e) ((st.G.applyUpdate u).head e) := by
        simp [res, step, hj0]
      rw [hres_uh]
      exact pairwise_diffBatch_UH hdu hsub0
    · have hsub1 : unionEdgesLt res.state.H_level (L + 1) ⊆ (st.G.applyUpdate u).E := hU_sub
      have hres_uh : res.UH = restrictUpdate u st.H ++
          (((st.H.applyBatch (restrictUpdate u st.H)).E \
            unionEdgesLt res.state.H_level (L + 1)).sort (· ≤ ·)).map Update.delete ++
          ((unionEdgesLt res.state.H_level (L + 1) \
            (st.H.applyBatch (restrictUpdate u st.H)).E).sort (· ≤ ·)).map
            fun e => Update.insert e ((st.G.applyUpdate u).tail e) ((st.G.applyUpdate u).head e) := by
        simp [res, step, hj0]
      rw [hres_uh]
      exact pairwise_diffBatch_UH hdu hsub1
  rw [hH'_eq]
  exact (applyBatch_perm_of_pairwise hPerm.symm hpw st.H).symm

/-! ## Word-length upper bound for permuted `step.UH` -/

private lemma updateAt_split_len_le_two_m {mem : ℕ → ℕ} {a v v' len : ℕ} {K : MGraph}
    {St Sh : Finset ℕ} (hu : UpdateAt mem a K (.split v v' St Sh) len) :
    len ≤ 5 + 2 * K.m := by
  have hK : ∀ (Lt Lh : List ℕ), Lt.Nodup → Lh.Nodup →
      (∀ e ∈ Lt, e ∈ K.E) → (∀ e ∈ Lh, e ∈ K.E) →
      Lt.length + Lh.length ≤ 2 * K.m := fun Lt Lh hnt hnh hmt hmh => by
    have c1 : Lt.length ≤ K.m := by
      rw [← List.toFinset_card_of_nodup hnt]
      exact Finset.card_le_card fun e he => hmt e (List.mem_toFinset.mp he)
    have c2 : Lh.length ≤ K.m := by
      rw [← List.toFinset_card_of_nodup hnh]
      exact Finset.card_le_card fun e he => hmh e (List.mem_toFinset.mp he)
    omega
  rcases hu with ⟨Lt, Lh, hnt, hnh, hmt, hmh, rfl, _⟩ | ⟨Lt, Lh, hnt, hnh, hmt, hmh, rfl, _⟩
  · have := hK Lt Lh hnt hnh (fun e he => ((hmt e).mp he).1) (fun e he => ((hmh e).mp he).1)
    omega
  · have := hK Lt Lh hnt hnh (fun e he => ((hmt e).mp he).1) (fun e he => ((hmh e).mp he).1)
    omega

private lemma applyUpdate_m_le (K : MGraph) (u : Update) :
    (K.applyUpdate u).m ≤ K.m + 1 := by
  cases u with
  | insert e x y =>
    show (insert e K.E).card ≤ K.E.card + 1
    exact Finset.card_insert_le e K.E
  | delete e =>
    show (K.E.erase e).card ≤ K.E.card + 1
    exact le_trans (Finset.card_erase_le) (Nat.le_succ _)
  | split _ _ _ _ =>
    show K.E.card ≤ K.E.card + 1
    exact Nat.le_succ _

private lemma batchBodyAt_words_le_aux :
    ∀ {mem : ℕ → ℕ} {a : ℕ} {H : MGraph} {us : List Update} {tot : ℕ},
      BatchBodyAt mem a H us tot →
      tot ≤ 4 * us.length +
        (5 + 2 * (H.m + us.length)) *
          (us.countP fun u => match u with | .split _ _ _ _ => true | _ => false) := by
  intro mem a H us
  induction us generalizing a H with
  | nil =>
    intro tot hB
    have h0 : tot = 0 := hB
    simp [h0]
  | cons u us ih =>
    intro tot hB
    rcases hB with ⟨len, hle, hu, hrest⟩
    have ih' := ih hrest
    have hm1 : (H.applyUpdate u).m + us.length ≤ H.m + (us.length + 1) := by
      have := applyUpdate_m_le H u; omega
    set k := us.countP fun u => match u with | .split _ _ _ _ => true | _ => false
    have hmul_mono : (5 + 2 * ((H.applyUpdate u).m + us.length)) * k ≤
        (5 + 2 * (H.m + (us.length + 1))) * k :=
      Nat.mul_le_mul_right k (by omega)
    have h1 : tot - len ≤ 4 * us.length + (5 + 2 * (H.m + (us.length + 1))) * k :=
      le_trans ih' (Nat.add_le_add_left hmul_mono _)
    cases u with
    | insert e x y =>
      rcases hu with ⟨rfl, _⟩
      simp only [List.length_cons, List.countP_cons, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      change tot ≤ 4 * (us.length + 1) + (5 + 2 * (H.m + (us.length + 1))) * k
      omega
    | delete e =>
      rcases hu with ⟨rfl, _⟩
      simp only [List.length_cons, List.countP_cons, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      change tot ≤ 4 * (us.length + 1) + (5 + 2 * (H.m + (us.length + 1))) * k
      omega
    | split v v' St Sh =>
      have hlen_le := updateAt_split_len_le_two_m hu
      simp only [List.length_cons, List.countP_cons, ↓reduceIte]
      have h2 : (5 + 2 * (H.m + (us.length + 1))) * (k + 1) =
          (5 + 2 * (H.m + (us.length + 1))) * k + (5 + 2 * (H.m + (us.length + 1))) :=
        Nat.mul_succ _ _
      change tot ≤ 4 * (us.length + 1) + (5 + 2 * (H.m + (us.length + 1))) * (k + 1)
      omega

/-- Any `BatchBodyAt` of a permutation `uhActual` of `(step st u sparsify).UH` occupies at most
`6 * (step st u sparsify).UH.length + 2 * st.H.m + 5` words. -/
theorem batchBodyAt_perm_step_UH_words_le {L : ℕ} {st : DynSpannerState L} {u : Update}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    {mem : ℕ → ℕ} {a uhWords : ℕ} {uhActual : List Update}
    (hdu : isDelOrSplit u)
    (hB : BatchBodyAt mem a st.H uhActual uhWords)
    (hPerm : uhActual.Perm (step st u sparsify).UH) :
    uhWords ≤ 6 * (step st u sparsify).UH.length + 2 * st.H.m + 5 := by
  set res := step st u sparsify
  have hsplit_count : (res.UH.countP fun x => match x with | .split _ _ _ _ => true | _ => false) ≤ 1 := by
    have hgen : ∀ (lDel lIns : List ℕ),
        ((restrictUpdate u st.H ++ lDel.map Update.delete ++
          lIns.map fun e => Update.insert e ((st.G.applyUpdate u).tail e) ((st.G.applyUpdate u).head e)).countP
          fun x => match x with | .split _ _ _ _ => true | _ => false) ≤ 1 := by
      intro lDel lIns
      rw [List.countP_append, List.countP_append]
      have h1 : (lDel.map Update.delete).countP (fun x => match x with | .split _ _ _ _ => true | _ => false) = 0 := by
        rw [List.countP_map]; simp [Function.comp]
      have h2 : (lIns.map fun e => Update.insert e ((st.G.applyUpdate u).tail e) ((st.G.applyUpdate u).head e)).countP
          (fun x => match x with | .split _ _ _ _ => true | _ => false) = 0 := by
        rw [List.countP_map]; simp [Function.comp]
      have h0 : (restrictUpdate u st.H).countP (fun x => match x with | .split _ _ _ _ => true | _ => false) ≤ 1 := by
        cases u with
        | insert _ _ _ => exact hdu.elim
        | delete e => by_cases h : e ∈ st.H.E <;> simp [restrictUpdate, h]
        | split _ _ _ _ => simp [restrictUpdate]
      omega
    dsimp only [res, step]; split_ifs <;> exact hgen _ _
  have haux := batchBodyAt_words_le_aux hB
  have hcp_eq : (uhActual.countP fun x => match x with | .split _ _ _ _ => true | _ => false) =
      (res.UH.countP fun x => match x with | .split _ _ _ _ => true | _ => false) :=
    hPerm.countP_eq _
  have hlen_eq : uhActual.length = res.UH.length := hPerm.length_eq
  rw [hlen_eq, hcp_eq] at haux
  have hmul : (5 + 2 * (st.H.m + res.UH.length)) *
      (res.UH.countP fun x => match x with | .split _ _ _ _ => true | _ => false) ≤
      5 + 2 * (st.H.m + res.UH.length) := by
    calc (5 + 2 * (st.H.m + res.UH.length)) * _
        ≤ (5 + 2 * (st.H.m + res.UH.length)) * 1 := Nat.mul_le_mul_left _ hsplit_count
      _ = 5 + 2 * (st.H.m + res.UH.length) := Nat.mul_one _
  omega

/-! ## Exact characterization of `DynSpanner.update` along a slice of `us` -/

/-- Exact unfolding of `updateGo` with arbitrary accumulators. -/
theorem updateGo_spec {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (us : List Update) (U : List Update) :
    ∀ (k₀ : ℕ) (uhAcc : List Update) (dAcc : Finset ℕ) (cAcc : ℕ),
      (∀ i (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) →
      let out := updateGo sparsify (runState (L := L) G₀ q sparsify us k₀) U uhAcc dAcc cAcc
      out.state = runState (L := L) G₀ q sparsify us (k₀ + U.length) ∧
      out.UH = uhAcc ++ (List.range U.length).flatMap (fun r => (runStepOut (L := L) G₀ q sparsify us (k₀ + r)).UH) ∧
      out.D = (dAcc ∪ (Finset.range U.length).biUnion (fun r => (runStepOut (L := L) G₀ q sparsify us (k₀ + r)).D)) ∩
        (runState (L := L) G₀ q sparsify us (k₀ + U.length)).H.E ∧
      out.cost = cAcc + ∑ r ∈ Finset.range U.length, (runStepOut (L := L) G₀ q sparsify us (k₀ + r)).cost := by
  induction U with
  | nil =>
    intro k₀ uhAcc dAcc cAcc _
    simp [updateGo]
  | cons u rest ih =>
    intro k₀ uhAcc dAcc cAcc hslice
    have h0 : us[k₀]? = some u := by simpa using hslice 0 (Nat.zero_lt_succ _)
    have hrest : ∀ i (hi : i < rest.length), us[k₀ + 1 + i]? = some (rest[i]'hi) := fun i hi => by
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using hslice (i + 1) (Nat.succ_lt_succ hi)
    have hst1 : (step (runState (L := L) G₀ q sparsify us k₀) u sparsify).state =
        runState (L := L) G₀ q sparsify us (k₀ + 1) := by
      simp [runState, h0]
    have hres0 : step (runState (L := L) G₀ q sparsify us k₀) u sparsify =
        runStepOut (L := L) G₀ q sparsify us k₀ := by
      simp [runStepOut, h0]
    have hIH := ih (k₀ + 1)
      (uhAcc ++ (runStepOut (L := L) G₀ q sparsify us k₀).UH)
      (dAcc ∪ (runStepOut (L := L) G₀ q sparsify us k₀).D)
      (cAcc + (runStepOut (L := L) G₀ q sparsify us k₀).cost) hrest
    dsimp only [updateGo]
    rw [hst1, hres0]
    rcases hIH with ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using h1
    · rw [h2, List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
        List.append_assoc]
      simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    · rw [h3, List.length_cons]
      have hU_eq : (dAcc ∪ (runStepOut (L := L) G₀ q sparsify us k₀).D) ∪
          (Finset.range rest.length).biUnion (fun r => (runStepOut (L := L) G₀ q sparsify us (k₀ + 1 + r)).D) =
          dAcc ∪ (Finset.range (rest.length + 1)).biUnion (fun r => (runStepOut (L := L) G₀ q sparsify us (k₀ + r)).D) := by
        ext e
        simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
        constructor
        · rintro ((h | h) | ⟨r, hr, he⟩)
          · exact Or.inl h
          · exact Or.inr ⟨0, Nat.zero_lt_succ _, by simpa using h⟩
          · exact Or.inr ⟨r + 1, Nat.succ_lt_succ hr, by simpa [Nat.add_assoc, Nat.add_comm 1] using he⟩
        · rintro (h | ⟨r, hr, he⟩)
          · exact Or.inl (Or.inl h)
          · cases r with
            | zero => exact Or.inl (Or.inr (by simpa using he))
            | succ r' => exact Or.inr ⟨r', Nat.lt_of_succ_lt_succ hr, by simpa [Nat.add_assoc, Nat.add_comm 1] using he⟩
      rw [hU_eq, show k₀ + 1 + rest.length = k₀ + (rest.length + 1) by omega]
    · rw [h4, List.length_cons, Finset.sum_range_succ']
      simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
      omega

/-- Exact characterization of `update st₀ U sparsify` on a contiguous slice `U` of `us` starting
at index `k₀`. -/
theorem update_slice_spec {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (us U : List Update) (k₀ : ℕ)
    (hslice : ∀ i (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) :
    let out := update (runState (L := L) G₀ q sparsify us k₀) U sparsify
    out.state = runState (L := L) G₀ q sparsify us (k₀ + U.length) ∧
    out.UH = (List.range U.length).flatMap (fun r => (runStepOut (L := L) G₀ q sparsify us (k₀ + r)).UH) ∧
    out.D = ((Finset.range U.length).biUnion (fun r => (runStepOut (L := L) G₀ q sparsify us (k₀ + r)).D)) ∩
      (runState (L := L) G₀ q sparsify us (k₀ + U.length)).H.E ∧
    out.cost = ∑ r ∈ Finset.range U.length, (runStepOut (L := L) G₀ q sparsify us (k₀ + r)).cost := by
  simpa [update] using updateGo_spec (L := L) G₀ q sparsify us U k₀ [] ∅ 0 hslice

end

end MinCostFlow.DynSpanner.Program
