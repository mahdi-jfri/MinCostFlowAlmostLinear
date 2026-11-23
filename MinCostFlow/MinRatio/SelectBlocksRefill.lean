module

public import MinCostFlow.MinRatio.SelectBlocksParts

/-!
# Refilling the forest, the potentials and the last graph (`SelectBlocksRefill`)

At a rebuild or a shift of level `j`, three parts of the select blocks get new contents: the
forest `F_j`, the potentials `φ_j`, and (at `j = d`) the last graph `G_d`. Two fill
procedures write them: `dgRefillFromLists` (`dgRefillFromListsContract`) refills a
`DynGraphAt` block in place, and `selectPhiFill` fills `φ_j`. Their posts give the new contents of one block and keep every word outside it.

This file shows that such a post keeps every other part of the blocks
(`SelBlocksDataAt`, `SelectBlocksParts.lean`). The lemmas take the two facts of the post as
hypotheses, so they hold for any procedure with that post. The post of `dgApplyBatchContract`
(`DynGraphBatch.lean`) has the same two facts. So the same lemmas give the `Update` changes of `F_j` (its forest deletions, insertions and
splits, as one batch) and of `G_d` (the forwarded batch), once these batches are in memory.

* `selRefillF_setF`: a refill of the block at `B.fPtr j`.
* `selRefillLast_setLast`: a refill of the block at `B.lastGPtr`.
* `selPhiFill_setPhi`: a fill of the table at `B.phiPtr j`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-- **The forest of level `j` after a refill.** If the block at `B.fPtr j` holds the forest `F'`
and every word outside the block is kept (the post of `dgRefillFromListsContract` at
`gPtr = B.fPtr j`), then all other parts of the blocks are kept. -/
theorem selRefillF_setF {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P j pLast : ℕ}
    {D : SelBlocksData} {F' : MGraph} (hblk : SelBlocksDataAt mem B P D pLast) (hj : j ≤ B.d)
    (hG : DynGraphAt mem' (B.fPtr j) B.vCap B.eCap F')
    (hfr : ∀ a, a < B.fPtr j ∨ B.fPtr j + dynGraphSize B.vCap B.eCap ≤ a → mem' a = mem a) :
    SelBlocksDataAt mem' B P { D with F := Function.update D.F j F' } pLast :=
  hblk.setF hj (fun a ha => hfr a (by
    unfold SelectBlocksLoc.regF SelectBlocksLoc.phiPtr at ha; omega)) hG

/-- **The last graph after a refill.** If the block at `B.lastGPtr` holds the graph `Gd'` and
every word outside the block is kept, then all other parts of the blocks are kept. -/
theorem selRefillLast_setLast {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P pLast : ℕ}
    {D : SelBlocksData} {Gd' : MGraph} (hblk : SelBlocksDataAt mem B P D pLast)
    (hG : DynGraphAt mem' B.lastGPtr B.vCap B.eCap Gd')
    (hfr : ∀ a, a < B.lastGPtr ∨ B.lastGPtr + dynGraphSize B.vCap B.eCap ≤ a →
      mem' a = mem a) :
    SelBlocksDataAt mem' B P { D with Gd := Gd' } pLast :=
  hblk.setLast (fun a ha => hfr a (by
    unfold SelectBlocksLoc.regLast SelectBlocksLoc.g0Ptr at ha; omega)) hG

/-- **The potentials of level `j` after a fill.** If the table at `B.phiPtr j` holds `φj'` on the
vertices `V'`, the vertices are below the cap, and every word outside the table is kept, then all
other parts of the blocks are kept. -/
theorem selPhiFill_setPhi {mem mem' : ℕ → ℕ} {B : SelectBlocksLoc} {P j pLast : ℕ}
    {D : SelBlocksData} {V' : Finset ℕ} {φj' : ℕ → ℝ} (hblk : SelBlocksDataAt mem B P D pLast)
    (hj : j ≤ B.d) (hV : ∀ v ∈ V', v < B.vCap)
    (hPhi : EdgeValuesAt mem' (B.phiPtr j) 4 B.Lk P V' φj')
    (hfr : ∀ a, a < B.phiPtr j ∨ B.phiPtr j + B.vCap * B.Lk ≤ a → mem' a = mem a) :
    SelBlocksDataAt mem' B P
      { D with V := Function.update D.V j V', φ := Function.update D.φ j φj' } pLast :=
  hblk.setPhi hj (fun a ha => hfr a (by
    unfold SelectBlocksLoc.regPhi SelectBlocksLoc.lenPtr at ha; omega)) ⟨hV, hPhi⟩

end MinCostFlow.MinRatio
