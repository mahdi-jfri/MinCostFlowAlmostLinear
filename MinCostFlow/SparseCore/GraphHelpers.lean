module

public import MinCostFlow.LSF.Lemma54Init
import Mathlib.Data.Finset.Card

/-!
# Graph Equivalence (`GraphEq`) and Batch Application Helpers

Helper lemmas shared across `SparseCore`:
* `GraphEq G₁ G₂`: vertex equality, edge equality, and endpoint equality on `E`.
  Because `MGraph.applyUpdate (.delete e)` leaves unspecified `tail`/`head` values outside `E`,
  `GraphEq` (rather than raw record `=`) is the natural congruence invariant for `applyUpdate`,
  `applyBatch`, `BatchIsValid`, `updateEnc`, `batchEnc`, `m`, `n`, and `deg`.
* `applyUpdate_delete_list_spec`, `applyUpdate_insert_list_spec`, `applyUpdate_split_list_spec`:
  clean batch specifications for list-of-deletes, list-of-inserts, and list-of-splits.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow MinCostFlow.LSF

/-! ## `GraphEq`: graph equivalence on `(V, E, tail|_E, head|_E)` -/

/-- Two `MGraph`s agree if they have the same vertex set, edge set, and endpoint maps on `E`. -/
def GraphEq (G₁ G₂ : MGraph) : Prop :=
  G₁.V = G₂.V ∧ G₁.E = G₂.E ∧ ∀ e ∈ G₁.E, G₁.tail e = G₂.tail e ∧ G₁.head e = G₂.head e

lemma graphEq_refl (G : MGraph) : GraphEq G G :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩

lemma graphEq_symm {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) : GraphEq G₂ G₁ :=
  ⟨h.1.symm, h.2.1.symm, fun e he => ⟨(h.2.2 e (h.2.1.symm ▸ he)).1.symm,
    (h.2.2 e (h.2.1.symm ▸ he)).2.symm⟩⟩

lemma graphEq_trans {G₁ G₂ G₃ : MGraph} (h₁₂ : GraphEq G₁ G₂) (h₂₃ : GraphEq G₂ G₃) :
    GraphEq G₁ G₃ :=
  ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.1.trans h₂₃.2.1, fun e he =>
    let he₂ := h₁₂.2.1 ▸ he
    ⟨(h₁₂.2.2 e he).1.trans (h₂₃.2.2 e he₂).1, (h₁₂.2.2 e he).2.trans (h₂₃.2.2 e he₂).2⟩⟩

lemma graphEq_isValid {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) (hV : G₁.IsValid) : G₂.IsValid := by
  intro e he
  have he₁ := h.2.1.symm ▸ he
  have h1 := hV e he₁
  have hEnds := h.2.2 e he₁
  exact ⟨h.1 ▸ hEnds.1 ▸ h1.1, h.1 ▸ hEnds.2 ▸ h1.2⟩

lemma graphEq_m {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) : G₁.m = G₂.m := by
  unfold MGraph.m; rw [h.2.1]

lemma graphEq_n {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) : G₁.n = G₂.n := by
  unfold MGraph.n; rw [h.1]

lemma graphEq_deg {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) (v : ℕ) : G₁.deg v = G₂.deg v := by
  unfold MGraph.deg
  have ht : G₁.E.filter (fun e => G₁.tail e = v) = G₂.E.filter (fun e => G₂.tail e = v) := by
    ext e
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨he, hv⟩
    · exact ⟨h.2.1 ▸ he, (h.2.2 e he).1.symm.trans hv⟩
    · exact ⟨h.2.1.symm ▸ he, (h.2.2 e (h.2.1.symm ▸ he)).1.trans hv⟩
  have hh : G₁.E.filter (fun e => G₁.head e = v) = G₂.E.filter (fun e => G₂.head e = v) := by
    ext e
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨he, hv⟩
    · exact ⟨h.2.1 ▸ he, (h.2.2 e he).2.symm.trans hv⟩
    · exact ⟨h.2.1.symm ▸ he, (h.2.2 e (h.2.1.symm ▸ he)).2.trans hv⟩
  rw [ht, hh]

lemma graphEq_maxDeg {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) : G₁.maxDeg = G₂.maxDeg := by
  unfold MGraph.maxDeg
  have hdeg : G₁.deg = G₂.deg := funext (graphEq_deg h)
  rw [h.1, hdeg]

lemma graphEq_updateIsValid {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) (u : Update) :
    G₁.UpdateIsValid u ↔ G₂.UpdateIsValid u := by
  cases u with
  | delete e => simp [MGraph.UpdateIsValid, h.2.1]
  | insert e a b => simp [MGraph.UpdateIsValid, h.1, h.2.1]
  | split v v' St Sh =>
    simp only [MGraph.UpdateIsValid, h.1, h.2.1]
    constructor <;> rintro ⟨hv, hv', hS, hinc⟩
    · refine ⟨hv, hv', hS, fun e he => ?_⟩
      have he₁ : e ∈ G₁.E := h.2.1 ▸ hS he
      rcases hinc e he with ht | hh
      · left; exact (h.2.2 e he₁).1.symm.trans ht
      · right; exact (h.2.2 e he₁).2.symm.trans hh
    · refine ⟨hv, hv', hS, fun e he => ?_⟩
      have he₁ : e ∈ G₁.E := h.2.1 ▸ hS he
      rcases hinc e he with ht | hh
      · left; exact (h.2.2 e he₁).1.trans ht
      · right; exact (h.2.2 e he₁).2.trans hh

lemma graphEq_applyUpdate {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) (u : Update) :
    GraphEq (G₁.applyUpdate u) (G₂.applyUpdate u) := by
  cases u with
  | delete e₀ =>
    refine ⟨h.1, ?_, fun e he => ?_⟩
    · dsimp only [MGraph.applyUpdate]; rw [h.2.1]
    · exact h.2.2 e (Finset.mem_of_mem_erase he)
  | insert e₀ a b =>
    refine ⟨h.1, ?_, fun e he => ?_⟩
    · dsimp only [MGraph.applyUpdate]; rw [h.2.1]
    · simp only [MGraph.applyUpdate, Finset.mem_insert] at he
      rcases he with rfl | he₁
      · simp [MGraph.applyUpdate]
      · by_cases hEq : e = e₀
        · subst hEq; simp [MGraph.applyUpdate]
        · simp [MGraph.applyUpdate, Function.update_of_ne hEq, h.2.2 e he₁]
  | split v v' St Sh =>
    refine ⟨?_, h.2.1, fun e he => ?_⟩
    · dsimp only [MGraph.applyUpdate]; rw [h.1]
    · dsimp only [MGraph.applyUpdate]
      have hEnds := h.2.2 e he
      rw [hEnds.1, hEnds.2]
      exact ⟨rfl, rfl⟩

lemma graphEq_updateEnc {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) (u : Update) :
    G₁.updateEnc u = G₂.updateEnc u := by
  cases u with
  | delete _ => rfl
  | insert _ _ _ => rfl
  | split v v' St Sh =>
    simp only [MGraph.updateEnc]
    have h1 := graphEq_deg (graphEq_applyUpdate h (.split v v' St Sh)) v
    have h2 := graphEq_deg (graphEq_applyUpdate h (.split v v' St Sh)) v'
    rw [h1, h2]

lemma graphEq_applyBatch {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) (U : List Update) :
    GraphEq (G₁.applyBatch U) (G₂.applyBatch U) := by
  induction U generalizing G₁ G₂ with
  | nil => exact h
  | cons u U ih => exact ih (graphEq_applyUpdate h u)

lemma graphEq_batchIsValid {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) (U : List Update) :
    G₁.BatchIsValid U ↔ G₂.BatchIsValid U := by
  induction U generalizing G₁ G₂ with
  | nil => simp [MGraph.BatchIsValid]
  | cons u U ih =>
    simp only [MGraph.BatchIsValid]
    exact and_congr (graphEq_updateIsValid h u) (ih (graphEq_applyUpdate h u))

lemma graphEq_batchEnc {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) (U : List Update) :
    G₁.batchEnc U = G₂.batchEnc U := by
  induction U generalizing G₁ G₂ with
  | nil => rfl
  | cons u U ih =>
    simp only [MGraph.batchEnc]
    rw [graphEq_updateEnc h u, ih (graphEq_applyUpdate h u)]

/-! ## Batch concatenation & primitive list-update specifications -/

lemma batchIsValid_append {G : MGraph} {U₁ U₂ : List Update} :
    G.BatchIsValid (U₁ ++ U₂) ↔ G.BatchIsValid U₁ ∧ (G.applyBatch U₁).BatchIsValid U₂ := by
  induction U₁ generalizing G with
  | nil => simp [MGraph.BatchIsValid, MGraph.applyBatch]
  | cons u U₁ ih =>
    simp only [List.cons_append, MGraph.BatchIsValid]
    change G.UpdateIsValid u ∧ (G.applyUpdate u).BatchIsValid (U₁ ++ U₂) ↔
      (G.UpdateIsValid u ∧ (G.applyUpdate u).BatchIsValid U₁) ∧
        ((G.applyUpdate u).applyBatch U₁).BatchIsValid U₂
    rw [ih (G := G.applyUpdate u), and_assoc]

lemma applyBatch_append (G : MGraph) (U₁ U₂ : List Update) :
    G.applyBatch (U₁ ++ U₂) = (G.applyBatch U₁).applyBatch U₂ := by
  simp only [MGraph.applyBatch, List.foldl_append]

lemma applyUpdate_delete_list_spec {G : MGraph} (hG : G.IsValid)
    {L : List ℕ} (hnd : L.Nodup) (hsub : ∀ e ∈ L, e ∈ G.E) :
    let U := L.map Update.delete
    let G' := G.applyBatch U
    G.BatchIsValid U ∧
    G'.V = G.V ∧
    G'.E = G.E \ L.toFinset ∧
    (∀ e ∈ G'.E, G'.tail e = G.tail e ∧ G'.head e = G.head e) ∧
    G'.IsValid := by
  induction L generalizing G with
  | nil =>
    refine ⟨trivial, rfl, by simp [MGraph.applyBatch], fun _ _ => ⟨rfl, rfl⟩, hG⟩
  | cons e L ih =>
    rw [List.nodup_cons] at hnd
    have heG : e ∈ G.E := hsub e List.mem_cons_self
    let G₁ := G.applyUpdate (.delete e)
    have hG₁V : G₁.V = G.V := rfl
    have hG₁E : G₁.E = G.E.erase e := rfl
    have hG₁_val : G₁.IsValid := fun f hf => hG f (Finset.mem_of_mem_erase hf)
    have hsub₁ : ∀ f ∈ L, f ∈ G₁.E := fun f hf =>
      Finset.mem_erase.mpr ⟨fun hfe => hnd.1 (hfe ▸ hf), hsub f (List.mem_cons_of_mem _ hf)⟩
    obtain ⟨hBV, hV, hE, hEnds, hVal⟩ := ih hG₁_val hnd.2 hsub₁
    refine ⟨⟨heG, hBV⟩, hV.trans hG₁V, ?_, fun f hf => ?_, hVal⟩
    · simp only [MGraph.applyBatch, List.map_cons, List.foldl_cons]
      change (G₁.applyBatch (L.map Update.delete)).E = _
      rw [hE, hG₁E, List.toFinset_cons]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto
    · exact hEnds f hf

lemma applyUpdate_insert_list_spec {G : MGraph} (hG : G.IsValid)
    {L : List (ℕ × ℕ × ℕ)}
    (hnd : (L.map Prod.fst).Nodup)
    (hnotin : ∀ t ∈ L, t.1 ∉ G.E)
    (hends : ∀ t ∈ L, t.2.1 ∈ G.V ∧ t.2.2 ∈ G.V) :
    let U := L.map (fun t => Update.insert t.1 t.2.1 t.2.2)
    let G' := G.applyBatch U
    G.BatchIsValid U ∧
    G'.V = G.V ∧
    G'.E = G.E ∪ (L.map Prod.fst).toFinset ∧
    (∀ e ∈ G.E, G'.tail e = G.tail e ∧ G'.head e = G.head e) ∧
    (∀ t ∈ L, G'.tail t.1 = t.2.1 ∧ G'.head t.1 = t.2.2) ∧
    G'.IsValid := by
  induction L generalizing G with
  | nil =>
    refine ⟨trivial, rfl, by simp [MGraph.applyBatch], fun _ _ => ⟨rfl, rfl⟩,
      fun _ h => by simp at h, hG⟩
  | cons t L ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    have ht_not : t.1 ∉ G.E := hnotin t List.mem_cons_self
    have ht_ends := hends t List.mem_cons_self
    let G₁ := G.applyUpdate (.insert t.1 t.2.1 t.2.2)
    have hG₁_val : G₁.IsValid :=
      applyUpdate_isValid hG ⟨ht_not, ht_ends.1, ht_ends.2⟩
    have hnotin₁ : ∀ s ∈ L, s.1 ∉ G₁.E := fun s hs hmem => by
      simp only [G₁, MGraph.applyUpdate, Finset.mem_insert] at hmem
      rcases hmem with hEq | hG_mem
      · exact hnd.1 (hEq ▸ List.mem_map_of_mem hs)
      · exact hnotin s (List.mem_cons_of_mem _ hs) hG_mem
    have hends₁ : ∀ s ∈ L, s.2.1 ∈ G₁.V ∧ s.2.2 ∈ G₁.V := fun s hs =>
      hends s (List.mem_cons_of_mem _ hs)
    obtain ⟨hBV, hV, hE, hOld, hNew, hVal⟩ := ih hG₁_val hnd.2 hnotin₁ hends₁
    refine ⟨⟨⟨ht_not, ht_ends.1, ht_ends.2⟩, hBV⟩, hV, ?_, fun e he => ?_, fun s hs => ?_, hVal⟩
    · simp only [MGraph.applyBatch, List.map_cons, List.foldl_cons]
      change (G₁.applyBatch _).E = _
      rw [hE]
      simp only [G₁, MGraph.applyUpdate, List.toFinset_cons]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    · have he1 : e ∈ G₁.E := by simp [G₁, MGraph.applyUpdate, he]
      have hne : e ≠ t.1 := fun h => ht_not (h ▸ he)
      have h1 := hOld e he1
      simp only [G₁, MGraph.applyUpdate, Function.update_of_ne hne] at h1
      exact h1
    · rcases List.mem_cons.mp hs with rfl | hsL
      · have he1 : s.1 ∈ G₁.E := by simp [G₁, MGraph.applyUpdate]
        have h1 := hOld s.1 he1
        simp only [G₁, MGraph.applyUpdate, Function.update_self] at h1
        exact h1
      · exact hNew s hsL

lemma applyUpdate_split_list_spec {G : MGraph} (hG : G.IsValid)
    {rs : List ℕ} (hnd : rs.Nodup) (hdisj : ∀ r ∈ rs, r ∉ G.V)
    {parent : ℕ → ℕ} (hparent : ∀ r ∈ rs, parent r ∈ G.V)
    {targetT targetH : ℕ → ℕ}
    (hspecT : ∀ e ∈ G.E,
      (targetT e ∈ G.V ∧ targetT e = G.tail e) ∨ (targetT e ∈ rs ∧ parent (targetT e) = G.tail e))
    (hspecH : ∀ e ∈ G.E,
      (targetH e ∈ G.V ∧ targetH e = G.head e) ∨ (targetH e ∈ rs ∧ parent (targetH e) = G.head e)) :
    let splits := rs.map fun r => Update.split (parent r) r
      (G.E.filter fun e => targetT e = r)
      (G.E.filter fun e => targetH e = r)
    let G' := G.applyBatch splits
    G.BatchIsValid splits ∧
    G'.V = G.V ∪ rs.toFinset ∧
    G'.E = G.E ∧
    (∀ e ∈ G.E, G'.tail e = targetT e ∧ G'.head e = targetH e) ∧
    G'.IsValid := by
  induction rs generalizing G with
  | nil =>
    refine ⟨trivial, by simp [MGraph.applyBatch], rfl, fun e he => ?_, hG⟩
    have ht : G.tail e = targetT e := by
      rcases hspecT e he with ⟨_, hT⟩ | ⟨hm, _⟩
      · exact hT.symm
      · simp at hm
    have hh : G.head e = targetH e := by
      rcases hspecH e he with ⟨_, hH⟩ | ⟨hm, _⟩
      · exact hH.symm
      · simp at hm
    exact ⟨ht, hh⟩
  | cons r rs ih =>
    rw [List.nodup_cons] at hnd
    have hr_not : r ∉ G.V := hdisj r List.mem_cons_self
    have hp_mem : parent r ∈ G.V := hparent r List.mem_cons_self
    let St_r := G.E.filter fun e => targetT e = r
    let Sh_r := G.E.filter fun e => targetH e = r
    have hS_sub : St_r ∪ Sh_r ⊆ G.E :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hS_inc : ∀ e ∈ St_r ∪ Sh_r, G.tail e = parent r ∨ G.head e = parent r := by
      intro e he
      rcases Finset.mem_union.mp he with heT | heH
      · rw [Finset.mem_filter] at heT
        left
        rcases hspecT e heT.1 with ⟨hV, _⟩ | ⟨_, hp⟩
        · exact absurd (heT.2 ▸ hV) hr_not
        · exact (congrArg parent heT.2 ▸ hp).symm
      · rw [Finset.mem_filter] at heH
        right
        rcases hspecH e heH.1 with ⟨hV, _⟩ | ⟨_, hp⟩
        · exact absurd (heH.2 ▸ hV) hr_not
        · exact (congrArg parent heH.2 ▸ hp).symm
    let u := Update.split (parent r) r St_r Sh_r
    have hu_val : G.UpdateIsValid u := ⟨hp_mem, hr_not, hS_sub, hS_inc⟩
    let G₁ := G.applyUpdate u
    have hG₁_val : G₁.IsValid := applyUpdate_isValid hG hu_val
    have hG₁E : G₁.E = G.E := rfl
    have hdisj₁ : ∀ x ∈ rs, x ∉ G₁.V := fun x hx hmem => by
      simp only [G₁, u, MGraph.applyUpdate, Finset.mem_insert] at hmem
      rcases hmem with rfl | hGmem
      · exact hnd.1 hx
      · exact hdisj x (List.mem_cons_of_mem _ hx) hGmem
    have hparent₁ : ∀ x ∈ rs, parent x ∈ G₁.V := fun x hx =>
      Finset.mem_insert_of_mem (hparent x (List.mem_cons_of_mem _ hx))
    have hG₁_tail : ∀ e ∈ G.E, G₁.tail e = if targetT e = r then r else G.tail e := by
      intro e he
      dsimp only [G₁, u, MGraph.applyUpdate]
      by_cases hTr : targetT e = r
      · have hparent_T : G.tail e = parent r := by
          rcases hspecT e he with ⟨hV, _⟩ | ⟨_, hp⟩
          · exact absurd (hTr ▸ hV) hr_not
          · exact (congrArg parent hTr ▸ hp).symm
        have heSr : e ∈ St_r := Finset.mem_filter.mpr ⟨he, hTr⟩
        simp [heSr, hparent_T, hTr]
      · have hnot : e ∉ St_r := fun h => hTr (Finset.mem_filter.mp h).2
        simp [hTr, hnot]
    have hG₁_head : ∀ e ∈ G.E, G₁.head e = if targetH e = r then r else G.head e := by
      intro e he
      dsimp only [G₁, u, MGraph.applyUpdate]
      by_cases hHr : targetH e = r
      · have hparent_H : G.head e = parent r := by
          rcases hspecH e he with ⟨hV, _⟩ | ⟨_, hp⟩
          · exact absurd (hHr ▸ hV) hr_not
          · exact (congrArg parent hHr ▸ hp).symm
        have heSr : e ∈ Sh_r := Finset.mem_filter.mpr ⟨he, hHr⟩
        simp [heSr, hparent_H, hHr]
      · have hnot : e ∉ Sh_r := fun h => hHr (Finset.mem_filter.mp h).2
        simp [hHr, hnot]
    have hspecT₁ : ∀ e ∈ G₁.E,
        (targetT e ∈ G₁.V ∧ targetT e = G₁.tail e) ∨ (targetT e ∈ rs ∧ parent (targetT e) = G₁.tail e) := by
      intro e he
      have heG : e ∈ G.E := hG₁E ▸ he
      rw [hG₁_tail e heG]
      rcases hspecT e heG with ⟨hV, hT⟩ | ⟨hmem, hp⟩
      · have hne : targetT e ≠ r := fun h => hr_not (h ▸ hV)
        left; exact ⟨Finset.mem_insert_of_mem hV, by simp [hT]⟩
      · rcases List.mem_cons.mp hmem with rfl | hrs
        · left; exact ⟨by simp [G₁, u, MGraph.applyUpdate], by simp⟩
        · have hne : targetT e ≠ r := fun h => hnd.1 (h ▸ hrs)
          right; exact ⟨hrs, by simp [hne, hp]⟩
    have hspecH₁ : ∀ e ∈ G₁.E,
        (targetH e ∈ G₁.V ∧ targetH e = G₁.head e) ∨ (targetH e ∈ rs ∧ parent (targetH e) = G₁.head e) := by
      intro e he
      have heG : e ∈ G.E := hG₁E ▸ he
      rw [hG₁_head e heG]
      rcases hspecH e heG with ⟨hV, hH⟩ | ⟨hmem, hp⟩
      · have hne : targetH e ≠ r := fun h => hr_not (h ▸ hV)
        left; exact ⟨Finset.mem_insert_of_mem hV, by simp [hH]⟩
      · rcases List.mem_cons.mp hmem with rfl | hrs
        · left; exact ⟨by simp [G₁, u, MGraph.applyUpdate], by simp⟩
        · have hne : targetH e ≠ r := fun h => hnd.1 (h ▸ hrs)
          right; exact ⟨hrs, by simp [hne, hp]⟩
    obtain ⟨hBV, hV, hE, hEnds, hVal⟩ :=
      ih hG₁_val hnd.2 hdisj₁ hparent₁ hspecT₁ hspecH₁
    have hSplit_map_eq :
        rs.map (fun x => Update.split (parent x) x
          (G₁.E.filter fun e => targetT e = x)
          (G₁.E.filter fun e => targetH e = x)) =
          rs.map (fun x => Update.split (parent x) x
            (G.E.filter fun e => targetT e = x)
            (G.E.filter fun e => targetH e = x)) := rfl
    rw [hSplit_map_eq] at hBV hV hE hEnds hVal
    have hSplits_cons :
        (r :: rs).map (fun x => Update.split (parent x) x
          (G.E.filter fun e => targetT e = x)
          (G.E.filter fun e => targetH e = x)) =
          u :: rs.map (fun x => Update.split (parent x) x
            (G.E.filter fun e => targetT e = x)
            (G.E.filter fun e => targetH e = x)) := rfl
    rw [hSplits_cons]
    refine ⟨⟨hu_val, hBV⟩, ?_, ?_, hEnds, hVal⟩
    · simp only [MGraph.applyBatch, List.foldl_cons]
      change (G₁.applyBatch _).V = _
      rw [hV]
      simp only [G₁, u, MGraph.applyUpdate, List.toFinset_cons]
      ext w
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    · simp only [MGraph.applyBatch, List.foldl_cons]
      exact hE

end MinCostFlow.SparseCore
