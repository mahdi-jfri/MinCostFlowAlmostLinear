module

public import MinCostFlow.MinRatio.WireChainCoreSelOutLevelKFBL
import MinCostFlow.SparseCore.Program.AssemblyReemb

/-!
# The memory part of one select-output level, with movable bounds (`WireChainCoreSelOutLevelAtKFBL`)

The chain-update core fills the slot of a level that `Update` does not rebuild in the step of that
level, and the select part reads it only at the end of the core. In between, later steps write
other words. So the memory clauses of a level must move from the memory of its step to the final
memory, and from what the step knows about the places of its words to what the end of the core
knows.

`SelOutLevelMemAt` states the memory clauses of one level of `UpdateCoreSelectOutAt` with the
places of its words in a set `Good` and the rows of its two stretch tables in a set `InTab`. The
step proves it with sets that it knows, and `SelOutLevelMemAt.transfer` moves it to larger sets
and to a memory that keeps the slot and the words of the two sets. At the end,
`SelOutLevelMemAt.toSelectOut` gives the clauses of `UpdateCoreSelectOutAt` when `Good` lies in
`[lo, hi)` off the footprint and `InTab` lies in the footprint or in `[lo, hi)`.
`selOutLevelMemAt_of_slotPost` proves it from the output of the slot writer.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

/-- The `n` words at `a` lie in `[lo, hi)` and in `Good`. -/
@[expose] def SelOutGoodAt (Good : ℕ → Prop) (lo hi a n : ℕ) : Prop :=
  lo ≤ a ∧ a + n ≤ hi ∧ ∀ t < n, Good (a + t)

/-- A table of `Lw` words per edge of `E` with base `mem a`: the base is a machine word, each row
ends at or below `hi`, and each word of a row lies in `InTab`. -/
@[expose] def SelOutRowsAt (w : ℕ) (InTab : ℕ → Prop) (hi : ℕ) (mem : ℕ → ℕ) (a Lw : ℕ)
    (E : Finset ℕ) : Prop :=
  mem a < 2 ^ w ∧ ∀ e ∈ E, mem a + e * Lw + Lw ≤ hi ∧ ∀ t < Lw, InTab (mem a + e * Lw + t)

/-- The memory clauses of one level of `UpdateCoreSelectOutAt` at the slot `slot`: the four lists
`D`, the batch `U` against the graph `G`, and the stretch descriptor with the values `vals` on `E`.
The lists, the batch and the descriptor lie in `[lo, hi)` and in `Good`, and every word of the two
tables lies in `InTab`, with each row ending at or below `hi`. -/
@[expose] def SelOutLevelMemAt (w P Lmax : ℕ) (Good InTab : ℕ → Prop) (lo hi : ℕ)
    (mem : ℕ → ℕ) (slot : ℕ) (D : LevelDiffLists) (G : MGraph) (U : List Update) (E : Finset ℕ)
    (vals : ℕ → ℝ) : Prop :=
  LevelDiffListsAt mem slot D ∧
  SelOutGoodAt Good lo hi (mem (slot + 0)) D.uG.length ∧
  SelOutGoodAt Good lo hi (mem (slot + 2)) D.fDel.length ∧
  SelOutGoodAt Good lo hi (mem (slot + 4)) D.uS.length ∧
  SelOutGoodAt Good lo hi (mem (slot + 6)) D.reemb.length ∧
  SmallBatchAt mem (mem (slot + 10)) G U (mem (slot + 11)) ∧
  (∀ t < mem (slot + 11), mem (mem (slot + 10) + t) < 2 ^ w) ∧
  SelOutGoodAt Good lo hi (mem (slot + 10)) (mem (slot + 11)) ∧
  SelOutGoodAt Good lo hi (mem (slot + 8)) 2 ∧
  mem (slot + 9) ≤ Lmax ∧
  StretchValuesAt mem (mem (slot + 8)) 4 (mem (slot + 9)) P E vals ∧
  SelOutRowsAt w InTab hi mem (mem (slot + 8)) (mem (slot + 9)) E ∧
  SelOutRowsAt w InTab hi mem (mem (slot + 8) + 1) (mem (slot + 9)) E

/-- A batch that the memory keeps. -/
theorem batchAt_of_agree' {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update}
    {words : ℕ} (hB : BatchAt mem₁ a G U words)
    (h : ∀ t < words, mem₂ (a + t) = mem₁ (a + t)) : BatchAt mem₂ a G U words := by
  obtain ⟨hw, h0, hbody⟩ := hB
  refine ⟨hw, by rw [show a = a + 0 from rfl, h 0 (by omega)]; exact h0,
    batchBodyAt_of_agree hbody fun x hx1 hx2 => ?_⟩
  have := h (x - a) (by omega)
  rwa [show a + (x - a) = x by omega] at this

/-- Words in a smaller set and a smaller range. -/
theorem SelOutGoodAt.mono {Good Good' : ℕ → Prop} {lo hi lo' hi' a n : ℕ}
    (h : SelOutGoodAt Good lo hi a n) (hGood : ∀ x, lo ≤ x → x < hi → Good x → Good' x)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : SelOutGoodAt Good' lo' hi' a n :=
  ⟨hlo.trans h.1, h.2.1.trans hhi, fun t ht => hGood _ (by have := h.1; omega)
    (by have := h.2.1; omega) (h.2.2 t ht)⟩

/-- Rows that the memory keeps, with a larger set and a larger bound. -/
theorem SelOutRowsAt.transfer {w hi hi' a Lw : ℕ} {InTab InTab' : ℕ → Prop} {mem mem' : ℕ → ℕ}
    {E : Finset ℕ} (h : SelOutRowsAt w InTab hi mem a Lw E) (ha : mem' a = mem a)
    (hTab : ∀ x, InTab x → InTab' x) (hhi : hi ≤ hi') :
    SelOutRowsAt w InTab' hi' mem' a Lw E := by
  rw [SelOutRowsAt, ha]
  exact ⟨h.1, fun e he => ⟨(h.2 e he).1.trans hhi, fun t ht => hTab _ ((h.2 e he).2 t ht)⟩⟩

/-- `SelOutLevelMemAt` moves to a memory that keeps the twelve words of the slot, every word of
`[lo, hi)` in `Good` and every word of `InTab`, and to larger sets and a larger range. -/
theorem SelOutLevelMemAt.transfer {w P Lmax lo hi lo' hi' slot : ℕ}
    {Good InTab Good' InTab' : ℕ → Prop}
    {mem mem' : ℕ → ℕ} {D : LevelDiffLists} {G : MGraph} {U : List Update} {E : Finset ℕ}
    {vals : ℕ → ℝ}
    (h : SelOutLevelMemAt w P Lmax Good InTab lo hi mem slot D G U E vals)
    (hS : ∀ i < 12, mem' (slot + i) = mem (slot + i))
    (hag : ∀ a, (lo ≤ a ∧ a < hi ∧ Good a) ∨ InTab a → mem' a = mem a)
    (hGood : ∀ a, lo ≤ a → a < hi → Good a → Good' a) (hTab : ∀ a, InTab a → InTab' a)
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    SelOutLevelMemAt w P Lmax Good' InTab' lo' hi' mem' slot D G U E vals := by
  obtain ⟨⟨hL1, hL0, hL3, hL2, hL5, hL4, hR1, hR0⟩, hG0, hG2, hG4, hG6, hB, hBW, hBG, hD,
    hLw, hSV, hT0, hT1⟩ := h
  have e0 := hS 0 (by omega); have e1 := hS 1 (by omega); have e2 := hS 2 (by omega)
  have e3 := hS 3 (by omega); have e4 := hS 4 (by omega); have e5 := hS 5 (by omega)
  have e6 := hS 6 (by omega); have e7 := hS 7 (by omega); have e8 := hS 8 (by omega)
  have e9 := hS 9 (by omega); have e10 := hS 10 (by omega); have e11 := hS 11 (by omega)
  have hagW : ∀ {a n : ℕ}, SelOutGoodAt Good lo hi a n → ∀ t < n, mem' (a + t) = mem (a + t) :=
    fun hg t ht => hag _ (Or.inl ⟨by have := hg.1; omega, by have := hg.2.1; omega, hg.2.2 t ht⟩)
  have hl : ∀ {a : ℕ} {xs : List ℕ}, ListAt mem a xs → SelOutGoodAt Good lo hi a xs.length →
      ListAt mem' a xs := fun hx hg => listAt_of_agree hx (hagW hg)
  have hd0 : mem' (mem (slot + 8)) = mem (mem (slot + 8)) := hagW hD 0 (by omega)
  have hd1 : mem' (mem (slot + 8) + 1) = mem (mem (slot + 8) + 1) := hagW hD 1 (by omega)
  have hm := fun {a n : ℕ} (hg : SelOutGoodAt Good lo hi a n) => hg.mono hGood hlo hhi
  refine ⟨⟨e1.trans hL1, ?_, e3.trans hL3, ?_, e5.trans hL5, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0]; exact hl hL0 hG0
  · rw [e2]; exact hl hL2 hG2
  · rw [e4]; exact hl hL4 hG4
  · exact e7.trans hR1
  · rw [e6]; exact hl hR0 (hR1 ▸ hG6)
  · rw [e0]; exact hm hG0
  · rw [e2]; exact hm hG2
  · rw [e4]; exact hm hG4
  · rw [e6]; exact hm hG6
  · rw [e10, e11]; exact ⟨batchAt_of_agree' hB.1 (hagW hBG), hB.2⟩
  · rw [e10, e11]
    exact fun t ht => by rw [hagW hBG t ht]; exact hBW t ht
  · rw [e10, e11]; exact hm hBG
  · rw [e8]; exact hm hD
  · rw [e9]; exact hLw
  · rw [e8, e9]
    exact stretchValuesAt_of_moved hSV (fun _ => ⟨hd0, hd1⟩)
      (fun e he t ht => hag _ (Or.inr ((hT0.2 e he).2 t ht)))
      (fun e he t ht => hag _ (Or.inr ((hT1.2 e he).2 t ht)))
  · rw [e8, e9]; exact hT0.transfer hd0 hTab hhi
  · rw [e8, e9]; exact hT1.transfer hd1 hTab hhi

/-- The memory clauses of one level of `UpdateCoreSelectOutAt` from `SelOutLevelMemAt`, when every
word of `[lo, hi)` in `Good` lies off the footprint `F` and every word of `InTab` lies in `F` or in
`[lo, hi)`. -/
theorem SelOutLevelMemAt.toSelectOut {w P Lmax lo hi slot : ℕ} {Good InTab F : ℕ → Prop}
    {mem : ℕ → ℕ} {D : LevelDiffLists} {G : MGraph} {U : List Update} {E : Finset ℕ}
    {vals : ℕ → ℝ}
    (h : SelOutLevelMemAt w P Lmax Good InTab lo hi mem slot D G U E vals)
    (hGood : ∀ a, lo ≤ a → a < hi → Good a → ¬ F a)
    (hTab : ∀ a, InTab a → F a ∨ (lo ≤ a ∧ a < hi)) :
    LevelDiffListsAt mem slot D ∧
    SelOutWordsAt F lo hi (mem (slot + 0)) D.uG.length ∧
    SelOutWordsAt F lo hi (mem (slot + 2)) D.fDel.length ∧
    SelOutWordsAt F lo hi (mem (slot + 4)) D.uS.length ∧
    SelOutWordsAt F lo hi (mem (slot + 6)) D.reemb.length ∧
    SmallBatchAt mem (mem (slot + 10)) G U (mem (slot + 11)) ∧
    (∀ t < mem (slot + 11), mem (mem (slot + 10) + t) < 2 ^ w) ∧
    SelOutWordsAt F lo hi (mem (slot + 10)) (mem (slot + 11)) ∧
    SelOutWordsAt F lo hi (mem (slot + 8)) 2 ∧
    mem (slot + 9) ≤ Lmax ∧
    StretchValuesAt mem (mem (slot + 8)) 4 (mem (slot + 9)) P E vals ∧
    SelOutTableAt w F lo hi mem (mem (slot + 8)) (mem (slot + 9)) E ∧
    SelOutTableAt w F lo hi mem (mem (slot + 8) + 1) (mem (slot + 9)) E := by
  obtain ⟨hL, hG0, hG2, hG4, hG6, hB, hBW, hBG, hD, hLw, hSV, hT0, hT1⟩ := h
  have hw : ∀ {a n : ℕ}, SelOutGoodAt Good lo hi a n → SelOutWordsAt F lo hi a n :=
    fun hg => ⟨hg.1, hg.2.1, fun t ht => hGood _ (by have := hg.1; omega)
      (by have := hg.2.1; omega) (hg.2.2 t ht)⟩
  have ht : ∀ {a : ℕ}, SelOutRowsAt w InTab hi mem a (mem (slot + 9)) E →
      SelOutTableAt w F lo hi mem a (mem (slot + 9)) E :=
    fun hr => ⟨hr.1, fun e he => ⟨(hr.2 e he).1, fun t ht => hTab _ ((hr.2 e he).2 t ht)⟩⟩
  exact ⟨hL, hw hG0, hw hG2, hw hG4, hw hG6, hB, hBW, hw hBG, hw hD, hLw, hSV, ht hT0, ht hT1⟩

/-- `SelOutLevelMemAt` at the memory that the slot writer leaves, from `SelOutSlotPost` and the
facts on the copies, the batch and the descriptor at that memory. The two touched-edge lists that
the slot writer writes from `hp` on lie in `[lo, hi)` and in `Good`. -/
theorem selOutLevelMemAt_of_slotPost {w P Lmax lo hi slot hp fDelPtr reembPtr reembLen descPtr Lw
      uPtr uWords : ℕ}
    {Good InTab : ℕ → Prop} {mem1 out1 : ℕ → ℕ} {fDel reemb uG uS : List ℕ}
    {G : MGraph} {U : List Update} {E : Finset ℕ} {vals : ℕ → ℝ}
    (hpost : SelOutSlotPost mem1 out1 slot hp fDelPtr fDel.length reembPtr reembLen descPtr Lw
      uPtr uWords uG uS)
    (hH : SelOutGoodAt Good lo hi hp (uG.length + uS.length))
    (hF : ListAt out1 fDelPtr fDel) (hFW : SelOutGoodAt Good lo hi fDelPtr fDel.length)
    (hR : ReembListAt out1 reembPtr reembLen reemb)
    (hRW : SelOutGoodAt Good lo hi reembPtr reemb.length)
    (hB : SmallBatchAt out1 uPtr G U uWords) (hBW : ∀ t < uWords, out1 (uPtr + t) < 2 ^ w)
    (hBG : SelOutGoodAt Good lo hi uPtr uWords)
    (hDW : SelOutGoodAt Good lo hi descPtr 2) (hLw : Lw ≤ Lmax)
    (hSV : StretchValuesAt out1 descPtr 4 Lw P E vals)
    (hT0 : SelOutRowsAt w InTab hi out1 descPtr Lw E)
    (hT1 : SelOutRowsAt w InTab hi out1 (descPtr + 1) Lw E) :
    SelOutLevelMemAt w P Lmax Good InTab lo hi out1 slot ⟨uG, fDel, uS, reemb⟩ G U E vals := by
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hG, hS, _, _⟩ := hpost
  obtain ⟨hH1, hH2, hH3⟩ := hH
  refine ⟨⟨hs1, by rw [hs0]; exact hG, hs3, by rw [hs2]; exact hF, hs5, by rw [hs4]; exact hS,
      by rw [hs6, hs7]; exact hR⟩, ?_, by rw [hs2]; exact hFW, ?_, by rw [hs6]; exact hRW,
    by rw [hs10, hs11]; exact hB, by rw [hs10, hs11]; exact hBW, by rw [hs10, hs11]; exact hBG,
    by rw [hs8]; exact hDW, by rw [hs9]; exact hLw, by rw [hs8, hs9]; exact hSV,
    by rw [hs8, hs9]; exact hT0, by rw [hs8, hs9]; exact hT1⟩
  · show SelOutGoodAt Good lo hi (out1 (slot + 0)) uG.length
    rw [hs0]; exact ⟨hH1, by omega, fun t ht => hH3 t (by omega)⟩
  · show SelOutGoodAt Good lo hi (out1 (slot + 4)) uS.length
    rw [hs4]
    exact ⟨by omega, by omega, fun t ht => by
      have := hH3 (uG.length + t) (by omega); rwa [← Nat.add_assoc] at this⟩

end MinCostFlow.MinRatio
