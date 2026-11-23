module

public import Mathlib.Data.List.Basic

/-!
# Generic directional payload interface for Link-Cut trees

This file defines `LctPayload α σ τ` and its algebraic laws `LctPayload.Laws`, separating
the splay and link-cut tree machinery from the values stored on nodes and paths.

A payload specifies:
- `α`: local value stored at each node,
- `σ`: segment summary over a sequence of `(nodeId, α)` pairs, keeping directional
  information for both traversal directions when needed,
- `τ`: lazy path update tag acting on node values and segment summaries, and
- `revVal`, `revSum`, `revTag`: how reversing a segment (for `reroot`) transforms node values,
  summaries, and pending tags.

This interface is instantiated first for the cycle-cancelling flow rounding algorithm of
Lemma 4.1 (`arXiv:2309.16629v1`, page 13, from Kang–Payor Section 4), and is designed for reuse
by the dynamic tree-chain payloads of Sections 5 and 6.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

/-- Operations of a directional Link-Cut tree payload with node values `α`, segment summaries `σ`,
and lazy path tags `τ`. -/
structure LctPayload (α σ τ : Type*) where
  /-- Summary of the empty node sequence. -/
  empty : σ
  /-- Summary of a single node `(id, v)`. -/
  single : ℕ → α → σ
  /-- Associative combination of left and right segment summaries. -/
  combine : σ → σ → σ
  /-- Action of segment reversal on a node value. -/
  revVal : α → α
  /-- Action of segment reversal on a segment summary. -/
  revSum : σ → σ
  /-- Identity lazy tag (no pending update). -/
  idTag : τ
  /-- Computable test for the identity tag. -/
  isIdTag : τ → Bool
  /-- Composition of lazy tags (`compTag outer inner` applies `inner` then `outer`). -/
  compTag : τ → τ → τ
  /-- Action of a lazy tag on a node value. -/
  actVal : τ → α → α
  /-- Action of a lazy tag on a segment summary. -/
  actSum : τ → σ → σ
  /-- Action of segment reversal on a pending forward tag. -/
  revTag : τ → τ

namespace LctPayload

/-- Algebraic laws required of an `LctPayload` so that rotations, lazy reversal, and lazy path
updates preserve segment summaries and logical node values. -/
structure Laws {α σ τ : Type*} (P : LctPayload α σ τ) : Prop where
  combine_empty_left : ∀ s, P.combine P.empty s = s
  combine_empty_right : ∀ s, P.combine s P.empty = s
  combine_assoc : ∀ a b c, P.combine (P.combine a b) c = P.combine a (P.combine b c)
  revVal_revVal : ∀ v, P.revVal (P.revVal v) = v
  revSum_revSum : ∀ s, P.revSum (P.revSum s) = s
  revTag_revTag : ∀ t, P.revTag (P.revTag t) = t
  revSum_empty : P.revSum P.empty = P.empty
  revSum_single : ∀ id v, P.revSum (P.single id v) = P.single id (P.revVal v)
  revSum_combine : ∀ a b, P.revSum (P.combine a b) = P.combine (P.revSum b) (P.revSum a)
  actVal_id : ∀ v, P.actVal P.idTag v = v
  actSum_id : ∀ s, P.actSum P.idTag s = s
  actVal_comp : ∀ t₁ t₂ v, P.actVal (P.compTag t₁ t₂) v = P.actVal t₁ (P.actVal t₂ v)
  actSum_comp : ∀ t₁ t₂ s, P.actSum (P.compTag t₁ t₂) s = P.actSum t₁ (P.actSum t₂ s)
  compTag_id_left : ∀ t, P.compTag P.idTag t = t
  compTag_id_right : ∀ t, P.compTag t P.idTag = t
  compTag_assoc : ∀ t₁ t₂ t₃, P.compTag (P.compTag t₁ t₂) t₃ = P.compTag t₁ (P.compTag t₂ t₃)
  actSum_empty : ∀ t, P.actSum t P.empty = P.empty
  actSum_single : ∀ t id v, P.actSum t (P.single id v) = P.single id (P.actVal t v)
  actSum_combine : ∀ t a b, P.actSum t (P.combine a b) = P.combine (P.actSum t a) (P.actSum t b)
  revTag_id : P.revTag P.idTag = P.idTag
  revTag_comp : ∀ t₁ t₂, P.revTag (P.compTag t₁ t₂) = P.compTag (P.revTag t₁) (P.revTag t₂)
  revVal_actVal : ∀ t v, P.revVal (P.actVal t v) = P.actVal (P.revTag t) (P.revVal v)
  revSum_actSum : ∀ t s, P.revSum (P.actSum t s) = P.actSum (P.revTag t) (P.revSum s)
  isIdTag_id : P.isIdTag P.idTag = true
  isIdTag_eq : ∀ t, P.isIdTag t = true → t = P.idTag

/-- Summary of a list of `(nodeId, α)` pairs with respect to `P`. -/
def listSummary {α σ τ : Type*} (P : LctPayload α σ τ) : List (ℕ × α) → σ
  | [] => P.empty
  | (id, v) :: rest => P.combine (P.single id v) (listSummary P rest)

@[simp]
theorem listSummary_nil {α σ τ : Type*} (P : LctPayload α σ τ) :
    P.listSummary [] = P.empty := rfl

@[simp]
theorem listSummary_cons {α σ τ : Type*} (P : LctPayload α σ τ) (id : ℕ) (v : α)
    (rest : List (ℕ × α)) :
    P.listSummary ((id, v) :: rest) = P.combine (P.single id v) (P.listSummary rest) := rfl

theorem listSummary_single {α σ τ : Type*} {P : LctPayload α σ τ} (hL : P.Laws)
    (id : ℕ) (v : α) :
    P.listSummary [(id, v)] = P.single id v := by
  simp [listSummary, hL.combine_empty_right]

theorem listSummary_append {α σ τ : Type*} {P : LctPayload α σ τ} (hL : P.Laws)
    (l₁ l₂ : List (ℕ × α)) :
    P.listSummary (l₁ ++ l₂) = P.combine (P.listSummary l₁) (P.listSummary l₂) := by
  induction l₁ with
  | nil => simp [listSummary, hL.combine_empty_left]
  | cons x xs ih =>
    rcases x with ⟨id, v⟩
    simp [listSummary, ih, hL.combine_assoc]

theorem listSummary_reverse_map {α σ τ : Type*} {P : LctPayload α σ τ} (hL : P.Laws)
    (l : List (ℕ × α)) :
    P.listSummary (l.reverse.map fun p => (p.1, P.revVal p.2)) = P.revSum (P.listSummary l) := by
  induction l with
  | nil => simp [listSummary, hL.revSum_empty]
  | cons x xs ih =>
    rcases x with ⟨id, v⟩
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
    rw [listSummary_append hL, ih, listSummary_single hL, listSummary_cons,
      hL.revSum_combine, hL.revSum_single]

theorem listSummary_map_act {α σ τ : Type*} {P : LctPayload α σ τ} (hL : P.Laws)
    (t : τ) (l : List (ℕ × α)) :
    P.listSummary (l.map fun p => (p.1, P.actVal t p.2)) = P.actSum t (P.listSummary l) := by
  induction l with
  | nil => simp [listSummary, hL.actSum_empty]
  | cons x xs ih =>
    rcases x with ⟨id, v⟩
    simp only [List.map_cons, listSummary_cons]
    rw [ih, hL.actSum_combine, hL.actSum_single]

end LctPayload

end MinCostFlow.LinkCut
