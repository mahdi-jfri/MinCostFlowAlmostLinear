module

public import MinCostFlow.LinkCut.Gen.Layout
public import MinCostFlow.LinkCut.Prog.MathForestProcs

/-!
# The payload steps a generic tree program calls

The tree programs (rotate, splay, expose, …) move pointers themselves, but they leave the
payload fields of a node to procedures that the payload supplies:

* `rev`: reverse the value, summary and tag of a node in place (`revVal`, `revSum`, `revTag`);
* `act`: apply a tag kept in a separate block to the value, summary and tag of a node
  (`actVal`, `actSum`, `compTag`);
* `pull`: write into the summary of a node the combination of the summaries of its children (an
  empty summary for a missing child) and of its own value (`combine`, `single`);
* `isId`: test whether the tag of a node is the identity tag (`isIdTag`);
* `setId`: write the identity tag into the tag of a node.

Each one is called with the address of the node record (whose value block holds the layout
words, see `NodeLayout.val_hdr`), may use scratch memory from the heap
pointer on but must leave it zero again, and changes nothing below the heap pointer except the
payload blocks of that record (`payloadContract`). Since the scratch is cleaned, the heap pointer
of a tree operation stays the same through all its payload calls. Its results must be representable; the predicates `valOk`, `sumOk`,
`tagOk` say which values are. `PayloadSteps` collects the procedures, their contracts, and one
bound `cost` on the cost and one bound `space` on the scratch of every call.

This file also states the frame that every generic tree procedure keeps (`TreeFrame`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

/-- A payload contract: the call may assume `pre`, that memory from the heap pointer `h` on is
zero, and that `h + space < 2 ^ w`. It leaves memory from `h` on zero, changes below `h` only the
cells in `W`, and meets `post` (which may also speak of the returned value). -/
def payloadContract (w : ℕ) (pre : List ℕ → (ℕ → ℕ) → Prop) (W : List ℕ → ℕ → Prop)
    (post : List ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop) (cost space : ℕ) : Contract where
  pre args mem := pre args mem ∧ ZeroFrom mem (heapArg args) ∧ heapArg args + space < 2 ^ w
  post args mem v mem' := ZeroFrom mem' (heapArg args) ∧
    (∀ x < heapArg args, ¬ W args x → mem' x = mem x) ∧ post args mem v mem'
  cost _ _ := cost

namespace NodeLayout

variable (Lay : NodeLayout α σ τ)

/-- The payload cells of the record at address `a`. -/
def PayCell (a x : ℕ) : Prop := a + OFF_VAL ≤ x ∧ x < a + Lay.nodeStride

end NodeLayout

/-- Which payload values a payload's procedures can produce. -/
structure PayloadOk (α σ τ : Type*) where
  valOk : α → Prop
  sumOk : σ → Prop
  tagOk : τ → Prop

section Contracts

variable (P : LctPayload α σ τ) (Lay : NodeLayout α σ τ) (ok : PayloadOk α σ τ) (w : ℕ)

/-- `rev [a, heap]`: reverse the payload of the record at `a`. -/
def revContract (cost space : ℕ) : Contract :=
  payloadContract w
    (fun args mem => ∃ a heap, args = [a, heap] ∧ a + Lay.nodeStride ≤ heap ∧
      ∃ v s t, Lay.ValAt mem (a + OFF_VAL) v ∧ Lay.SumAt mem (a + Lay.offSum) s ∧
        Lay.TagAt mem (a + Lay.offTag) t ∧
        ok.valOk (P.revVal v) ∧ ok.sumOk (P.revSum s) ∧ ok.tagOk (P.revTag t))
    (fun args x => Lay.PayCell (args.getD 0 0) x)
    (fun args mem _ mem' => ∀ v s t, Lay.ValAt mem (args.getD 0 0 + OFF_VAL) v →
      Lay.SumAt mem (args.getD 0 0 + Lay.offSum) s → Lay.TagAt mem (args.getD 0 0 + Lay.offTag) t →
      Lay.ValAt mem' (args.getD 0 0 + OFF_VAL) (P.revVal v) ∧
      Lay.SumAt mem' (args.getD 0 0 + Lay.offSum) (P.revSum s) ∧
      Lay.TagAt mem' (args.getD 0 0 + Lay.offTag) (P.revTag t))
    cost space

/-- `act [b, a, heap]`: apply the tag kept at `b` to the payload of the record at `a`. The tag
block lies outside the record. -/
def actContract (cost space : ℕ) : Contract :=
  payloadContract w
    (fun args mem => ∃ b a heap, args = [b, a, heap] ∧ a + Lay.nodeStride ≤ heap ∧
      b + Lay.tagW ≤ heap ∧ (b + Lay.tagW ≤ a ∨ a + Lay.nodeStride ≤ b) ∧
      ∃ t₀ v s t, Lay.TagAt mem b t₀ ∧ Lay.ValAt mem (a + OFF_VAL) v ∧
        Lay.SumAt mem (a + Lay.offSum) s ∧ Lay.TagAt mem (a + Lay.offTag) t ∧
        ok.valOk (P.actVal t₀ v) ∧ ok.sumOk (P.actSum t₀ s) ∧ ok.tagOk (P.compTag t₀ t))
    (fun args x => Lay.PayCell (args.getD 1 0) x)
    (fun args mem _ mem' => ∀ t₀ v s t, Lay.TagAt mem (args.getD 0 0) t₀ →
      Lay.ValAt mem (args.getD 1 0 + OFF_VAL) v →
      Lay.SumAt mem (args.getD 1 0 + Lay.offSum) s → Lay.TagAt mem (args.getD 1 0 + Lay.offTag) t →
      Lay.ValAt mem' (args.getD 1 0 + OFF_VAL) (P.actVal t₀ v) ∧
      Lay.SumAt mem' (args.getD 1 0 + Lay.offSum) (P.actSum t₀ s) ∧
      Lay.TagAt mem' (args.getD 1 0 + Lay.offTag) (P.compTag t₀ t))
    cost space

/-- The summary of an optional child record: empty for address `0`. -/
def ChildSumAt (mem : ℕ → ℕ) (c : ℕ) (s : σ) : Prop :=
  (c = 0 ∧ s = P.empty) ∨ (c ≠ 0 ∧ Lay.SumAt mem (c + Lay.offSum) s)

/-- `pull [x, a, l, r, heap]`: the record of node `x` is at `a`, and its children's records are
at `l` and `r` (`0` for no child). Writes `combine sumL (combine (single x val) sumR)` into the
summary of `a`. A child record may be the record at `a` itself. -/
def pullContract (cost space : ℕ) : Contract :=
  payloadContract w
    (fun args mem => ∃ x a l r heap, args = [x, a, l, r, heap] ∧ a + Lay.nodeStride ≤ heap ∧
      l + Lay.nodeStride ≤ heap ∧ r + Lay.nodeStride ≤ heap ∧
      ∃ v sl sr, Lay.ValAt mem (a + OFF_VAL) v ∧ ChildSumAt P Lay mem l sl ∧
        ChildSumAt P Lay mem r sr ∧ ok.sumOk (P.combine sl (P.combine (P.single x v) sr)))
    (fun args x => Lay.PayCell (args.getD 1 0) x)
    (fun args mem _ mem' => ∀ v sl sr, Lay.ValAt mem (args.getD 1 0 + OFF_VAL) v →
      ChildSumAt P Lay mem (args.getD 2 0) sl → ChildSumAt P Lay mem (args.getD 3 0) sr →
      Lay.ValAt mem' (args.getD 1 0 + OFF_VAL) v ∧
      Lay.SumAt mem' (args.getD 1 0 + Lay.offSum)
        (P.combine sl (P.combine (P.single (args.getD 0 0) v) sr)) ∧
      ∀ t, Lay.TagAt mem (args.getD 1 0 + Lay.offTag) t →
        Lay.TagAt mem' (args.getD 1 0 + Lay.offTag) t)
    cost space

/-- `isId [a, heap]`: return `1` if the tag of the record at `a` is the identity, else `0`. It
changes no memory below the heap pointer. -/
def isIdContract (cost space : ℕ) : Contract :=
  payloadContract w
    (fun args mem => ∃ a heap, args = [a, heap] ∧ a + Lay.nodeStride ≤ heap ∧
      (∃ v, Lay.ValAt mem (a + OFF_VAL) v) ∧ ∃ t, Lay.TagAt mem (a + Lay.offTag) t)
    (fun _ _ => False)
    (fun args mem v _ => ∀ t, Lay.TagAt mem (args.getD 0 0 + Lay.offTag) t →
      v = if P.isIdTag t then 1 else 0)
    cost space

/-- `setId [a, heap]`: write the identity tag into the record at `a`. -/
def setIdContract (cost space : ℕ) : Contract :=
  payloadContract w
    (fun args mem => ∃ a heap, args = [a, heap] ∧ a + Lay.nodeStride ≤ heap ∧
      ∃ v, Lay.ValAt mem (a + OFF_VAL) v)
    (fun args x => Lay.PayCell (args.getD 0 0) x)
    (fun args mem _ mem' =>
      (∀ v, Lay.ValAt mem (args.getD 0 0 + OFF_VAL) v → Lay.ValAt mem' (args.getD 0 0 + OFF_VAL) v) ∧
      (∀ s, Lay.SumAt mem (args.getD 0 0 + Lay.offSum) s →
        Lay.SumAt mem' (args.getD 0 0 + Lay.offSum) s) ∧
      Lay.TagAt mem' (args.getD 0 0 + Lay.offTag) P.idTag)
    cost space

end Contracts

/-- The payload procedures of a program, with their contracts. -/
structure PayloadSteps (w : ℕ) (p : Program) (P : LctPayload α σ τ) (Lay : NodeLayout α σ τ)
    (ok : PayloadOk α σ τ) where
  rev : ℕ
  act : ℕ
  pull : ℕ
  isId : ℕ
  setId : ℕ
  cost : ℕ
  space : ℕ
  rev_ok : MeetsContract w p rev (revContract P Lay ok w cost space)
  act_ok : MeetsContract w p act (actContract P Lay ok w cost space)
  pull_ok : MeetsContract w p pull (pullContract P Lay ok w cost space)
  isId_ok : MeetsContract w p isId (isIdContract P Lay w cost space)
  setId_ok : MeetsContract w p setId (setIdContract P Lay w cost space)

/-- The frame of a generic tree procedure that starts with heap pointer `h` in `mem` and ends
in `mem'`: memory from `h` on is zero, and below `h` only the cells of the records of nodes
`0 .. cap` may change. -/
def TreeFrame (Lay : NodeLayout α σ τ) (nb cap h : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  ZeroFrom mem' h ∧ ∀ a < h, ¬ Lay.InRecords nb cap a → mem' a = mem a

theorem TreeFrame.refl {Lay : NodeLayout α σ τ} {nb cap h : ℕ} {mem : ℕ → ℕ}
    (hz : ZeroFrom mem h) : TreeFrame Lay nb cap h mem mem :=
  ⟨hz, fun _ _ _ => rfl⟩

theorem TreeFrame.trans {Lay : NodeLayout α σ τ} {nb cap h : ℕ} {m₁ m₂ m₃ : ℕ → ℕ}
    (h₁ : TreeFrame Lay nb cap h m₁ m₂) (h₂ : TreeFrame Lay nb cap h m₂ m₃) :
    TreeFrame Lay nb cap h m₁ m₃ :=
  ⟨h₂.1, fun a ha hr => (h₂.2 a ha hr).trans (h₁.2 a ha hr)⟩

end MinCostFlow.LinkCut.Gen
