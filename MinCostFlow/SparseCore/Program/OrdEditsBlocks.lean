module

public import MinCostFlow.SparseCore.Program.ContractOrder

/-!
# Block-aligned order edits for an update batch (`OrdEditsBlocks`)

The first phase of a branch step must run each vertex split of the input batch `U` at the point
of its update in `U` (after the forest releases of earlier updates and before those of later
updates). A raw edit list `ed` satisfying only `OrderedBatch G U ord (applyOrdEdits ord ed)`
carries no alignment between edits and updates, and applying all of `ed` before the forest cuts
moves ends across cuts before the helper lists them.

This file defines `OrdEditsForBatch G U ed`, requiring `ed = ed₁ ++ … ++ ed_|U| ++ rot` with one
block per update of `U` in batch order followed by a tail `rot` of `rotateTo` edits:
* `.delete e` has the 1-edit block `[.dropEdge e]`;
* `.split v v' St Sh` has a 1-edit block `[.moveEnds v v' sel c]` that moves the exact same ends
  at `v` in the current graph `G` as `splitEnds St Sh`;
* `.insert e a b` has the 2-edit block `[.insertBefore a (e, true) y₁, .insertBefore b (e, false) y₂]`;
* after all updates of `U`, every remaining edit is `.rotateTo _ _`.

Because each update's block length (`updateEditBlockLen`) is fixed by its constructor, no extra
block-length data is needed in memory. Both P7's output edits at deeper levels (`outStepEdits` and
`outStepEditsSmall`, proved in `OutEditsBlocks.lean`) and the solver's level-`0` edits
(`batchToOrdEdits`, via `ordEditsForBatch_edgeOnly_flatMap`) have this exact block form.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle

/-! ## Block lengths and predicate -/

/-- The number of order edits in the block of one graph update:
`1` for a deletion (`dropEdge`), `1` for a split (`moveEnds`), and `2` for an insertion
(two `insertBefore` edits, tail end then head end). -/
def updateEditBlockLen : Update → ℕ
  | .delete _ => 1
  | .split _ _ _ _ => 1
  | .insert _ _ _ => 2

/-- The total number of edits in the update blocks of `U` (before the trailing `rotateTo` block). -/
def batchEditBlocksLen (U : List Update) : ℕ :=
  (U.map updateEditBlockLen).sum

theorem batchEditBlocksLen_nil : batchEditBlocksLen [] = 0 := rfl

theorem batchEditBlocksLen_cons (u : Update) (U : List Update) :
    batchEditBlocksLen (u :: U) = updateEditBlockLen u + batchEditBlocksLen U := rfl

theorem batchEditBlocksLen_append (U₁ U₂ : List Update) :
    batchEditBlocksLen (U₁ ++ U₂) = batchEditBlocksLen U₁ + batchEditBlocksLen U₂ := by
  simp [batchEditBlocksLen]

/-- An edit is a `rotateTo` edit. -/
def OrdEdit.IsRotate : OrdEdit → Prop
  | .rotateTo _ _ => True
  | _ => False

/-- Exact prefix of order edits matching the updates of `U` on `G`, with no trailing rotations:
* `.delete e` has `[.dropEdge e]`;
* `.split v v' St Sh` has `[.moveEnds v v' sel c]` agreeing with `splitEnds St Sh` on every end
  currently at `v` in `G`;
* `.insert e a b` has `[.insertBefore a (e, true) y₁, .insertBefore b (e, false) y₂]`. -/
def OrdEditsExactPrefix : MGraph → List Update → List OrdEdit → Prop
  | _, [], ed => ed = []
  | G, .delete e :: U, .dropEdge e' :: ed =>
      e' = e ∧ OrdEditsExactPrefix (G.applyUpdate (.delete e)) U ed
  | G, .split v v' St Sh :: U, .moveEnds v₁ v₁' sel c :: ed =>
      v₁ = v ∧ v₁' = v' ∧
      (∀ x : End, x.1 ∈ G.E → G.src x = v → movedBy sel c x = splitEnds St Sh x) ∧
      OrdEditsExactPrefix (G.applyUpdate (.split v v' St Sh)) U ed
  | G, .insert e a b :: U, .insertBefore a' x₁ _ :: .insertBefore b' x₂ _ :: ed =>
      a' = a ∧ x₁ = (e, true) ∧ b' = b ∧ x₂ = (e, false) ∧
      OrdEditsExactPrefix (G.applyUpdate (.insert e a b)) U ed
  | _, _ :: _, _ => False

/-- **Block-aligned order edits for a batch.** The edit list `ed` consists of one block per update
of `U` in batch order, followed by a tail of `rotateTo` edits (`ed = ed₁ ++ … ++ ed_|U| ++ rot`).
Each update's block length is fixed by its kind (`updateEditBlockLen`), so no separate block-length
data is needed in memory. -/
def OrdEditsForBatch : MGraph → List Update → List OrdEdit → Prop
  | _, [], ed => ∀ d ∈ ed, d.IsRotate
  | G, .delete e :: U, .dropEdge e' :: ed =>
      e' = e ∧ OrdEditsForBatch (G.applyUpdate (.delete e)) U ed
  | G, .split v v' St Sh :: U, .moveEnds v₁ v₁' sel c :: ed =>
      v₁ = v ∧ v₁' = v' ∧
      (∀ x : End, x.1 ∈ G.E → G.src x = v → movedBy sel c x = splitEnds St Sh x) ∧
      OrdEditsForBatch (G.applyUpdate (.split v v' St Sh)) U ed
  | G, .insert e a b :: U, .insertBefore a' x₁ _ :: .insertBefore b' x₂ _ :: ed =>
      a' = a ∧ x₁ = (e, true) ∧ b' = b ∧ x₂ = (e, false) ∧
      OrdEditsForBatch (G.applyUpdate (.insert e a b)) U ed
  | _, _ :: _, _ => False

/-! ## Decomposition and composition lemmas -/

/-- Any empty batch with no edits satisfies `OrdEditsForBatch`. -/
theorem ordEditsForBatch_nil_nil (G : MGraph) : OrdEditsForBatch G [] [] :=
  fun _ h => by cases h

/-- Inversion lemma for `OrdEditsForBatch` on an empty batch. -/
theorem ordEditsForBatch_nil_iff {G : MGraph} {ed : List OrdEdit} :
    OrdEditsForBatch G [] ed ↔ ∀ d ∈ ed, ∃ v y, d = .rotateTo v y := by
  constructor
  · intro h d hd
    have hr := h d hd
    cases d with
    | rotateTo v y => exact ⟨v, y, rfl⟩
    | _ => exact False.elim hr
  · intro h d hd
    obtain ⟨v, y, rfl⟩ := h d hd
    trivial

/-- Inversion lemma for `OrdEditsForBatch` on a deletion. -/
theorem ordEditsForBatch_delete_iff {G : MGraph} {e : ℕ} {U : List Update} {ed : List OrdEdit} :
    OrdEditsForBatch G (.delete e :: U) ed ↔
      ∃ ed', ed = .dropEdge e :: ed' ∧ OrdEditsForBatch (G.applyUpdate (.delete e)) U ed' := by
  constructor
  · intro h
    cases ed with
    | nil => exact False.elim h
    | cons d rest =>
      cases d with
      | dropEdge e' =>
        obtain ⟨rfl, hrest⟩ := h
        exact ⟨rest, rfl, hrest⟩
      | _ => exact False.elim h
  · rintro ⟨ed', rfl, hrest⟩
    exact ⟨rfl, hrest⟩

/-- Inversion lemma for `OrdEditsForBatch` on a vertex split. -/
theorem ordEditsForBatch_split_iff {G : MGraph} {v v' : ℕ} {St Sh : Finset ℕ}
    {U : List Update} {ed : List OrdEdit} :
    OrdEditsForBatch G (.split v v' St Sh :: U) ed ↔
      ∃ sel c ed', ed = .moveEnds v v' sel c :: ed' ∧
        (∀ x : End, x.1 ∈ G.E → G.src x = v → movedBy sel c x = splitEnds St Sh x) ∧
        OrdEditsForBatch (G.applyUpdate (.split v v' St Sh)) U ed' := by
  constructor
  · intro h
    cases ed with
    | nil => exact False.elim h
    | cons d rest =>
      cases d with
      | moveEnds v₁ v₁' sel c =>
        obtain ⟨rfl, rfl, hmov, hrest⟩ := h
        exact ⟨sel, c, rest, rfl, hmov, hrest⟩
      | _ => exact False.elim h
  · rintro ⟨sel, c, ed', rfl, hmov, hrest⟩
    exact ⟨rfl, rfl, hmov, hrest⟩

/-- Inversion lemma for `OrdEditsForBatch` on an edge insertion. -/
theorem ordEditsForBatch_insert_iff {G : MGraph} {e a b : ℕ} {U : List Update}
    {ed : List OrdEdit} :
    OrdEditsForBatch G (.insert e a b :: U) ed ↔
      ∃ y₁ y₂ ed', ed = .insertBefore a (e, true) y₁ :: .insertBefore b (e, false) y₂ :: ed' ∧
        OrdEditsForBatch (G.applyUpdate (.insert e a b)) U ed' := by
  constructor
  · intro h
    cases ed with
    | nil => exact False.elim h
    | cons d₁ rest₁ =>
      cases d₁ with
      | insertBefore a' x₁ y₁ =>
        cases rest₁ with
        | nil => exact False.elim h
        | cons d₂ rest₂ =>
          cases d₂ with
          | insertBefore b' x₂ y₂ =>
            obtain ⟨rfl, rfl, rfl, rfl, hrest⟩ := h
            exact ⟨y₁, y₂, rest₂, rfl, hrest⟩
          | _ => exact False.elim h
      | _ => exact False.elim h
  · rintro ⟨y₁, y₂, ed', rfl, hrest⟩
    exact ⟨rfl, rfl, rfl, rfl, hrest⟩

/-- An exact prefix has length equal to `batchEditBlocksLen U`. -/
theorem ordEditsExactPrefix_length :
    ∀ {G : MGraph} {U : List Update} {ed : List OrdEdit},
      OrdEditsExactPrefix G U ed → ed.length = batchEditBlocksLen U
  | _, [], _, rfl => rfl
  | _, .delete _ :: _, .dropEdge _ :: _, ⟨_, h⟩ => by
    simp only [List.length_cons, batchEditBlocksLen_cons, updateEditBlockLen,
      ordEditsExactPrefix_length h]
    omega
  | _, .split _ _ _ _ :: _, .moveEnds _ _ _ _ :: _, ⟨_, _, _, h⟩ => by
    simp only [List.length_cons, batchEditBlocksLen_cons, updateEditBlockLen,
      ordEditsExactPrefix_length h]
    omega
  | _, .insert _ _ _ :: _, .insertBefore _ _ _ :: .insertBefore _ _ _ :: _,
      ⟨_, _, _, _, h⟩ => by
    simp only [List.length_cons, batchEditBlocksLen_cons, updateEditBlockLen,
      ordEditsExactPrefix_length h]
    omega

/-- Concatenation of exact prefixes along concatenated batches. -/
theorem ordEditsExactPrefix_append :
    ∀ {G : MGraph} {U₁ U₂ : List Update} {ed₁ ed₂ : List OrdEdit},
      OrdEditsExactPrefix G U₁ ed₁ →
      OrdEditsExactPrefix (G.applyBatch U₁) U₂ ed₂ →
      OrdEditsExactPrefix G (U₁ ++ U₂) (ed₁ ++ ed₂)
  | _, [], _, _, _, rfl, h₂ => h₂
  | _, .delete _ :: _, _, .dropEdge _ :: _, _, ⟨he, h₁⟩, h₂ =>
    ⟨he, ordEditsExactPrefix_append h₁ h₂⟩
  | _, .split _ _ _ _ :: _, _, .moveEnds _ _ _ _ :: _, _, ⟨hv, hv', hmov, h₁⟩, h₂ =>
    ⟨hv, hv', hmov, ordEditsExactPrefix_append h₁ h₂⟩
  | _, .insert _ _ _ :: _, _, .insertBefore _ _ _ :: .insertBefore _ _ _ :: _, _,
      ⟨ha, hx₁, hb, hx₂, h₁⟩, h₂ =>
    ⟨ha, hx₁, hb, hx₂, ordEditsExactPrefix_append h₁ h₂⟩

/-- Appending a tail of `rotateTo` edits to an exact prefix gives `OrdEditsForBatch`. -/
theorem ordEditsForBatch_of_exactPrefix_append :
    ∀ {G : MGraph} {U : List Update} {edBase rot : List OrdEdit},
      OrdEditsExactPrefix G U edBase →
      (∀ d ∈ rot, d.IsRotate) →
      OrdEditsForBatch G U (edBase ++ rot)
  | _, [], _, _, rfl, hrot => hrot
  | _, .delete _ :: _, .dropEdge _ :: _, _, ⟨he, h₁⟩, hrot =>
    ⟨he, ordEditsForBatch_of_exactPrefix_append h₁ hrot⟩
  | _, .split _ _ _ _ :: _, .moveEnds _ _ _ _ :: _, _, ⟨hv, hv', hmov, h₁⟩, hrot =>
    ⟨hv, hv', hmov, ordEditsForBatch_of_exactPrefix_append h₁ hrot⟩
  | _, .insert _ _ _ :: _, .insertBefore _ _ _ :: .insertBefore _ _ _ :: _, _,
      ⟨ha, hx₁, hb, hx₂, h₁⟩, hrot =>
    ⟨ha, hx₁, hb, hx₂, ordEditsForBatch_of_exactPrefix_append h₁ hrot⟩

/-- Exact characterization: `OrdEditsForBatch G U ed` holds iff `ed = edBase ++ rot` where
`edBase` is an exact block prefix for `U` on `G` and every edit of `rot` is a `rotateTo`. -/
theorem ordEditsForBatch_iff_exists_rot :
    ∀ {G : MGraph} {U : List Update} {ed : List OrdEdit},
      OrdEditsForBatch G U ed ↔
        ∃ edBase rot, ed = edBase ++ rot ∧ OrdEditsExactPrefix G U edBase ∧
          ∀ d ∈ rot, d.IsRotate := by
  intro G U
  induction U generalizing G with
  | nil =>
    intro ed
    constructor
    · intro h
      exact ⟨[], ed, rfl, rfl, h⟩
    · rintro ⟨edBase, rot, rfl, rfl, hrot⟩
      exact hrot
  | cons u U ih =>
    intro ed
    constructor
    · intro h
      cases u with
      | delete e =>
        obtain ⟨ed', rfl, h'⟩ := ordEditsForBatch_delete_iff.mp h
        obtain ⟨edBase, rot, rfl, hpre, hrot⟩ := (ih (G := G.applyUpdate (.delete e))).mp h'
        exact ⟨.dropEdge e :: edBase, rot, rfl, ⟨rfl, hpre⟩, hrot⟩
      | split v v' St Sh =>
        obtain ⟨sel, c, ed', rfl, hmov, h'⟩ := ordEditsForBatch_split_iff.mp h
        obtain ⟨edBase, rot, rfl, hpre, hrot⟩ := (ih (G := G.applyUpdate (.split v v' St Sh))).mp h'
        exact ⟨.moveEnds v v' sel c :: edBase, rot, rfl, ⟨rfl, rfl, hmov, hpre⟩, hrot⟩
      | insert e a b =>
        obtain ⟨y₁, y₂, ed', rfl, h'⟩ := ordEditsForBatch_insert_iff.mp h
        obtain ⟨edBase, rot, rfl, hpre, hrot⟩ := (ih (G := G.applyUpdate (.insert e a b))).mp h'
        exact ⟨.insertBefore a (e, true) y₁ :: .insertBefore b (e, false) y₂ :: edBase, rot, rfl,
          ⟨rfl, rfl, rfl, rfl, hpre⟩, hrot⟩
    · rintro ⟨edBase, rot, rfl, hpre, hrot⟩
      exact ordEditsForBatch_of_exactPrefix_append hpre hrot

/-- `OrdEditsForBatch` splits `ed` cleanly into `ed.take (batchEditBlocksLen U)` (the exact prefix
for `U`) and `ed.drop (batchEditBlocksLen U)` (the trailing `rotateTo` block). -/
theorem ordEditsForBatch_take_drop {G : MGraph} {U : List Update} {ed : List OrdEdit}
    (h : OrdEditsForBatch G U ed) :
    batchEditBlocksLen U ≤ ed.length ∧
      OrdEditsExactPrefix G U (ed.take (batchEditBlocksLen U)) ∧
      ∀ d ∈ ed.drop (batchEditBlocksLen U), d.IsRotate := by
  obtain ⟨edBase, rot, rfl, hpre, hrot⟩ := ordEditsForBatch_iff_exists_rot.mp h
  have hlen : edBase.length = batchEditBlocksLen U := ordEditsExactPrefix_length hpre
  refine ⟨by simp [hlen], ?_, ?_⟩
  · rw [← hlen, List.take_left]
    exact hpre
  · rw [← hlen, List.drop_left]
    exact hrot

/-- Splitting `OrdEditsForBatch` at any prefix `U.take i` of `U` (`i ≤ U.length`): the first
`batchEditBlocksLen (U.take i)` edits form an exact prefix for `U.take i` on `G`, and the
remaining edits satisfy `OrdEditsForBatch` for `U.drop i` on `G.applyBatch (U.take i)`. -/
theorem ordEditsForBatch_split_at :
    ∀ (U : List Update) (i : ℕ) (G : MGraph) (ed : List OrdEdit),
      OrdEditsForBatch G U ed →
      OrdEditsExactPrefix G (U.take i) (ed.take (batchEditBlocksLen (U.take i))) ∧
        OrdEditsForBatch (G.applyBatch (U.take i)) (U.drop i)
          (ed.drop (batchEditBlocksLen (U.take i)))
  | _, 0, G, ed, h => ⟨rfl, h⟩
  | [], _ + 1, G, ed, h => ⟨rfl, h⟩
  | u :: U, i + 1, G, ed, h => by
    cases u with
    | delete e =>
      obtain ⟨ed', rfl, h'⟩ := ordEditsForBatch_delete_iff.mp h
      obtain ⟨h1, h2⟩ := ordEditsForBatch_split_at U i (G.applyUpdate (.delete e)) ed' h'
      simpa only [List.take_succ_cons, List.drop_succ_cons, batchEditBlocksLen_cons,
        updateEditBlockLen, Nat.one_add, MGraph.applyBatch, List.foldl_cons] using
        And.intro ⟨rfl, h1⟩ h2
    | split v v' St Sh =>
      obtain ⟨sel, c, ed', rfl, hmov, h'⟩ := ordEditsForBatch_split_iff.mp h
      obtain ⟨h1, h2⟩ := ordEditsForBatch_split_at U i (G.applyUpdate (.split v v' St Sh)) ed' h'
      simpa only [List.take_succ_cons, List.drop_succ_cons, batchEditBlocksLen_cons,
        updateEditBlockLen, Nat.one_add, MGraph.applyBatch, List.foldl_cons] using
        And.intro ⟨rfl, rfl, hmov, h1⟩ h2
    | insert e a b =>
      obtain ⟨y₁, y₂, ed', rfl, h'⟩ := ordEditsForBatch_insert_iff.mp h
      obtain ⟨h1, h2⟩ := ordEditsForBatch_split_at U i (G.applyUpdate (.insert e a b)) ed' h'
      have hlen : 2 + batchEditBlocksLen (U.take i) = (batchEditBlocksLen (U.take i) + 1) + 1 := by
        omega
      simpa only [List.take_succ_cons, List.drop_succ_cons, batchEditBlocksLen_cons,
        updateEditBlockLen, hlen, MGraph.applyBatch, List.foldl_cons] using
        And.intro ⟨rfl, rfl, rfl, rfl, h1⟩ h2

/-! ## Edge-only helper (for level `0` of the solver) -/

/-- Any edge-only batch (no `.split` updates) translated update-by-update by mapping `.delete e`
to `[.dropEdge e]` and `.insert e a b` to `[.insertBefore a (e, true) y₁,
.insertBefore b (e, false) y₂]` satisfies `OrdEditsForBatch` on every graph `G`. -/
theorem ordEditsForBatch_edgeOnly_flatMap {G : MGraph} {U : List Update}
    {f : Update → List OrdEdit}
    (hf_del : ∀ e, f (.delete e) = [.dropEdge e])
    (hf_ins : ∀ e a b, ∃ y₁ y₂,
      f (.insert e a b) = [.insertBefore a (e, true) y₁, .insertBefore b (e, false) y₂])
    (hnoSplit : ∀ u ∈ U, match u with | .split _ _ _ _ => False | _ => True) :
    OrdEditsForBatch G U (U.flatMap f) := by
  induction U generalizing G with
  | nil => exact ordEditsForBatch_nil_nil G
  | cons u U ih =>
    have hu := hnoSplit u List.mem_cons_self
    have hU : ∀ w ∈ U, match w with | .split _ _ _ _ => False | _ => True :=
      fun w hw => hnoSplit w (List.mem_cons_of_mem u hw)
    cases u with
    | split _ _ _ _ => exact False.elim hu
    | delete e =>
      simp only [List.flatMap_cons, hf_del, List.singleton_append]
      exact ⟨rfl, ih hU⟩
    | insert e a b =>
      obtain ⟨y₁, y₂, hfi⟩ := hf_ins e a b
      simp only [List.flatMap_cons, hfi, List.cons_append, List.nil_append]
      exact ⟨rfl, rfl, rfl, rfl, ih hU⟩

end MinCostFlow.SparseCore.Program
