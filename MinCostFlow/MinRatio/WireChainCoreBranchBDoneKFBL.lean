module

public import MinCostFlow.MinRatio.WireChainCoreSelOutLevelAtKFBL
public import MinCostFlow.MinRatio.WireChainCoreSelOutCopyKFBL
import MinCostFlow.SparseCore.Program.AssemblyReemb
import WordRAM.Tactic

/-!
# The finished levels of the Branch B loop under `KFBL` (`WireChainCoreBranchBDoneKFBL`)

The Branch B loop of the chain-update core runs one level step (`wireBranchBStepKFBL`) at each
level that `Update` does not rebuild. Each step leaves the memory clauses of its level
(`SelOutLevelMemAt`). The later steps must not break them, so the loop carries them for every
finished level in one form, `BranchBDoneSlots`:
* the words of the lists, the batch and the descriptor of a finished level lie in the region
  `[lo, hi)` of the loop (`lo` is the first word after the reserved slots, `hi` the heap pointer)
  and off the footprints of all cores;
* the stretch rows of finished level `j` lie in the footprint of core `j`, or in `[lo, hi)` off the
  footprints of all cores.

`BranchBDoneSlots.step` adds the level of one more step. It needs only the frame of the step (below
the old heap pointer it writes only the footprint of its own core and words that the caller keeps
apart, such as the level graph and the slot of the level), the growth of the footprint of its core
into fresh heap, and the disjointness of the cores. Each old level moves by
`SelOutLevelMemAt.transfer`. `BranchBDoneSlots.frame` keeps all finished levels across a part of
the program that keeps their footprints and the words of the region off all footprints, such as
the rebuild of later levels. An op on the core of the last finished level may rewrite its
footprint, where its stretch rows lie. Then only the lists and the batch of that level stay
(`SelOutLevelListsAt`), and the caller reads the descriptor again (`SelOutLevelMemAt.of_lists`).
`BranchBDoneSlots.level` gives at the end the memory clauses of `UpdateCoreSelectOutAt` for a final
footprint that contains every core footprint and none of the other words of the region.

The level-`0` batch lies at `uIntBuf`, below the heap, so the loop first copies it to fresh heap
(`wireBranchBCopyBatch0Stmt`, run lemma `wireBranchBCopyBatch0Stmt_runs`). Then every batch that a
slot names lies in the region.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- The memory clauses of the finished levels `j < n` of the Branch B loop, with the footprint
`foot r` of core `r`, the region `[lo, hi)` and the slots `selBase + 1 + 12 j`. -/
@[expose] def BranchBDoneSlots (w P d : ℕ) (Lmax : ℕ → ℕ) (foot : ℕ → ℕ → Prop)
    (lo hi selBase : ℕ) (mem : ℕ → ℕ) (n : ℕ) (D : ℕ → LevelDiffLists) (G : ℕ → MGraph)
    (U : ℕ → List Update) (E : ℕ → Finset ℕ) (vals : ℕ → ℕ → ℝ) : Prop :=
  ∀ j < n, SelOutLevelMemAt w P (Lmax j) (fun x => ∀ r < d, ¬ foot r x)
    (fun x => foot j x ∨ (lo ≤ x ∧ x < hi ∧ ∀ r < d, ¬ foot r x)) lo hi mem
    (selBase + 1 + 12 * j) (D j) (G j) (U j) (E j) (vals j)

theorem branchBDoneSlots_zero (w P d : ℕ) (Lmax : ℕ → ℕ) (foot : ℕ → ℕ → Prop)
    (lo hi selBase : ℕ) (mem : ℕ → ℕ) (D : ℕ → LevelDiffLists) (G : ℕ → MGraph)
    (U : ℕ → List Update) (E : ℕ → Finset ℕ) (vals : ℕ → ℕ → ℝ) :
    BranchBDoneSlots w P d Lmax foot lo hi selBase mem 0 D G U E vals :=
  fun _ hj => absurd hj (Nat.not_lt_zero _)

/-- One more finished level. The step at level `idx` left the clauses `hnew` of its level, with
the batch of the level at `curBatch` and the rest in `[hi, hi')` off the new footprint `foot' idx`.
Below `hi` it wrote only the footprint of core `idx` and words outside `K`. The words of the region,
the footprints of the other cores and the old slots are in `K`. Core `idx` had no word in the
region before the step, and the footprints of the other cores do not change. -/
theorem BranchBDoneSlots.step {w P d idx lo hi hi' selBase curBatch bW : ℕ} {Lmax : ℕ → ℕ}
    {foot foot' : ℕ → ℕ → Prop} {K : ℕ → Prop} {mem mem' : ℕ → ℕ} {D : ℕ → LevelDiffLists}
    {G : ℕ → MGraph} {U : ℕ → List Update} {E : ℕ → Finset ℕ} {vals : ℕ → ℕ → ℝ}
    (h : BranchBDoneSlots w P d Lmax foot lo hi selBase mem idx D G U E vals)
    (hnew : SelOutLevelMemAt w P (Lmax idx)
      (fun x => (hi ≤ x ∧ ¬ foot' idx x) ∨ (curBatch ≤ x ∧ x < curBatch + bW))
      (fun x => foot' idx x ∨ (hi ≤ x ∧ x < hi')) curBatch hi' mem' (selBase + 1 + 12 * idx)
      (D idx) (G idx) (U idx) (E idx) (vals idx))
    (hIdx : idx < d) (hlo : lo ≤ curBatch) (hhi : hi ≤ hi') (hlohi : lo ≤ hi)
    (hBatch : ∀ x, curBatch ≤ x → x < curBatch + bW → x < hi ∧ ∀ r < d, ¬ foot r x)
    (hFootSame : ∀ r, r ≠ idx → ∀ x, foot' r x ↔ foot r x)
    (hFootNew : ∀ x, foot' idx x → foot idx x ∨ (hi ≤ x ∧ x < hi'))
    (hFootLt : ∀ r < d, ∀ x, foot r x → x < hi)
    (hFootIdx : ∀ x, foot idx x → x < lo)
    (hDisj : ∀ r < d, r ≠ idx → ∀ x, foot r x → ¬ foot idx x)
    (hKeep : ∀ a < hi, ¬ foot idx a → K a → mem' a = mem a)
    (hKlo : ∀ x, lo ≤ x → x < hi → K x)
    (hKfoot : ∀ r < d, r ≠ idx → ∀ x, foot r x → K x)
    (hSlots : ∀ j < idx, ∀ i < 12, selBase + 1 + 12 * j + i < hi ∧
      ¬ foot idx (selBase + 1 + 12 * j + i) ∧ K (selBase + 1 + 12 * j + i)) :
    BranchBDoneSlots w P d Lmax foot' lo hi' selBase mem' (idx + 1) D G U E vals := by
  have hoff : ∀ x, x < hi → ∀ r < d, ¬ foot r x → ¬ foot' r x := fun x hx r hr hn hf => by
    by_cases hri : r = idx
    · subst hri
      rcases hFootNew x hf with h' | h'
      · exact hn h'
      · omega
    · exact hn ((hFootSame r hri x).mp hf)
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · refine (h j hj).transfer (fun i hi12 => ?_) (fun a ha => ?_)
      (fun a _ ha2 hg r hr => hoff a ha2 r hr (hg r hr)) (fun a ha => ?_) le_rfl hhi
    · obtain ⟨h1, h2, h3⟩ := hSlots j hj i hi12
      exact hKeep _ h1 h2 h3
    · rcases ha with ⟨h1, h2, hg⟩ | hf | ⟨h1, h2, hg⟩
      · exact hKeep a h2 (hg idx hIdx) (hKlo a h1 h2)
      · exact hKeep a (hFootLt j (by omega) a hf) (hDisj j (by omega) (by omega) a hf)
          (hKfoot j (by omega) (by omega) a hf)
      · exact hKeep a h2 (hg idx hIdx) (hKlo a h1 h2)
    · rcases ha with hf | ⟨h1, h2, hg⟩
      · exact Or.inl ((hFootSame j (by omega) a).mpr hf)
      · exact Or.inr ⟨h1, by omega, fun r hr => hoff a h2 r hr (hg r hr)⟩
  · refine hnew.transfer (fun _ _ => rfl) (fun _ _ => rfl) (fun a _ _ hg r hr => ?_)
      (fun a ha => ?_) hlo le_rfl
    · rcases hg with ⟨h1, hn⟩ | ⟨h1, h2⟩
      · by_cases hri : r = j
        · subst hri; exact hn
        · rw [hFootSame r hri]
          intro hf
          have := hFootLt r hr a hf
          omega
      · obtain ⟨hlt, hnf⟩ := hBatch a h1 h2
        exact hoff a hlt r hr (hnf r hr)
    · rcases ha with hf | h'
      · exact Or.inl hf
      · by_cases hf : foot' j a
        · exact Or.inl hf
        · refine Or.inr ⟨by omega, h'.2, fun r hr hfr => ?_⟩
          by_cases hri : r = j
          · subst hri; exact hf hfr
          · have := hFootLt r hr a ((hFootSame r hri a).mp hfr); omega

/-- Fewer finished levels. -/
theorem BranchBDoneSlots.of_le {w P d lo hi selBase n n' : ℕ} {Lmax : ℕ → ℕ}
    {foot : ℕ → ℕ → Prop} {mem : ℕ → ℕ} {D : ℕ → LevelDiffLists} {G : ℕ → MGraph}
    {U : ℕ → List Update} {E : ℕ → Finset ℕ} {vals : ℕ → ℕ → ℝ}
    (h : BranchBDoneSlots w P d Lmax foot lo hi selBase mem n D G U E vals) (hn : n' ≤ n) :
    BranchBDoneSlots w P d Lmax foot lo hi selBase mem n' D G U E vals :=
  fun j hj => h j (by omega)

/-- One more finished level, from its clauses in the form of `BranchBDoneSlots`. -/
theorem BranchBDoneSlots.succ {w P d lo hi selBase n : ℕ} {Lmax : ℕ → ℕ}
    {foot : ℕ → ℕ → Prop} {mem : ℕ → ℕ} {D : ℕ → LevelDiffLists} {G : ℕ → MGraph}
    {U : ℕ → List Update} {E : ℕ → Finset ℕ} {vals : ℕ → ℕ → ℝ}
    (h : BranchBDoneSlots w P d Lmax foot lo hi selBase mem n D G U E vals)
    (hn : SelOutLevelMemAt w P (Lmax n) (fun x => ∀ r < d, ¬ foot r x)
      (fun x => foot n x ∨ (lo ≤ x ∧ x < hi ∧ ∀ r < d, ¬ foot r x)) lo hi mem
      (selBase + 1 + 12 * n) (D n) (G n) (U n) (E n) (vals n)) :
    BranchBDoneSlots w P d Lmax foot lo hi selBase mem (n + 1) D G U E vals := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact h j hj
  · exact hn

/-- The finished levels stay across a part of the program that keeps their footprints, their
slots and every word of the region off all footprints, and that adds no word of the region to a
footprint. -/
theorem BranchBDoneSlots.frame {w P d lo hi hi' selBase n : ℕ} {Lmax : ℕ → ℕ}
    {foot foot' : ℕ → ℕ → Prop} {mem mem' : ℕ → ℕ} {D : ℕ → LevelDiffLists} {G : ℕ → MGraph}
    {U : ℕ → List Update} {E : ℕ → Finset ℕ} {vals : ℕ → ℕ → ℝ}
    (h : BranchBDoneSlots w P d Lmax foot lo hi selBase mem n D G U E vals) (hhi : hi ≤ hi')
    (hFootSame : ∀ j < n, ∀ x, foot' j x ↔ foot j x)
    (hFootReg : ∀ r < d, ∀ x, lo ≤ x → x < hi → foot' r x → foot r x)
    (hKeep : ∀ a, (∃ j < n, foot j a) ∨ (lo ≤ a ∧ a < hi ∧ ∀ r < d, ¬ foot r a) →
      mem' a = mem a)
    (hSlots : ∀ j < n, ∀ i < 12,
      mem' (selBase + 1 + 12 * j + i) = mem (selBase + 1 + 12 * j + i)) :
    BranchBDoneSlots w P d Lmax foot' lo hi' selBase mem' n D G U E vals := by
  have hoff : ∀ x, lo ≤ x → x < hi → (∀ r < d, ¬ foot r x) → ∀ r < d, ¬ foot' r x :=
    fun x h1 h2 hn r hr hf => hn r hr (hFootReg r hr x h1 h2 hf)
  intro j hj
  refine (h j hj).transfer (hSlots j hj) (fun a ha => hKeep a ?_)
    (fun a h1 h2 hg => hoff a h1 h2 hg) (fun a ha => ?_) le_rfl hhi
  · rcases ha with ⟨h1, h2, hg⟩ | hf | ⟨h1, h2, hg⟩
    · exact Or.inr ⟨h1, h2, hg⟩
    · exact Or.inl ⟨j, hj, hf⟩
    · exact Or.inr ⟨h1, h2, hg⟩
  · rcases ha with hf | ⟨h1, h2, hg⟩
    · exact Or.inl ((hFootSame j hj a).mpr hf)
    · exact Or.inr ⟨h1, lt_of_lt_of_le h2 hhi, hoff a h1 h2 hg⟩

/-- The clauses of `SelOutLevelMemAt` on the four lists and the batch: all of it but the stretch
descriptor and its two tables. -/
@[expose] def SelOutLevelListsAt (w : ℕ) (Good : ℕ → Prop) (lo hi : ℕ) (mem : ℕ → ℕ)
    (slot : ℕ) (D : LevelDiffLists) (G : MGraph) (U : List Update) : Prop :=
  LevelDiffListsAt mem slot D ∧
  SelOutGoodAt Good lo hi (mem (slot + 0)) D.uG.length ∧
  SelOutGoodAt Good lo hi (mem (slot + 2)) D.fDel.length ∧
  SelOutGoodAt Good lo hi (mem (slot + 4)) D.uS.length ∧
  SelOutGoodAt Good lo hi (mem (slot + 6)) D.reemb.length ∧
  SmallBatchAt mem (mem (slot + 10)) G U (mem (slot + 11)) ∧
  (∀ t < mem (slot + 11), mem (mem (slot + 10) + t) < 2 ^ w) ∧
  SelOutGoodAt Good lo hi (mem (slot + 10)) (mem (slot + 11))

theorem SelOutLevelMemAt.lists {w P Lmax lo hi slot : ℕ} {Good InTab : ℕ → Prop}
    {mem : ℕ → ℕ} {D : LevelDiffLists} {G : MGraph} {U : List Update} {E : Finset ℕ}
    {vals : ℕ → ℝ} (h : SelOutLevelMemAt w P Lmax Good InTab lo hi mem slot D G U E vals) :
    SelOutLevelListsAt w Good lo hi mem slot D G U :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1⟩

/-- `SelOutLevelMemAt` from the lists and the batch, and a descriptor with its two tables. -/
theorem SelOutLevelMemAt.of_lists {w P Lmax lo hi slot : ℕ} {Good InTab : ℕ → Prop}
    {mem : ℕ → ℕ} {D : LevelDiffLists} {G : MGraph} {U : List Update} {E : Finset ℕ}
    {vals : ℕ → ℝ} (h : SelOutLevelListsAt w Good lo hi mem slot D G U)
    (hD : SelOutGoodAt Good lo hi (mem (slot + 8)) 2) (hLw : mem (slot + 9) ≤ Lmax)
    (hSV : StretchValuesAt mem (mem (slot + 8)) 4 (mem (slot + 9)) P E vals)
    (hT0 : SelOutRowsAt w InTab hi mem (mem (slot + 8)) (mem (slot + 9)) E)
    (hT1 : SelOutRowsAt w InTab hi mem (mem (slot + 8) + 1) (mem (slot + 9)) E) :
    SelOutLevelMemAt w P Lmax Good InTab lo hi mem slot D G U E vals :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2, hD, hLw, hSV, hT0, hT1⟩

/-- The lists and the batch move to a memory that keeps the slot words other than the descriptor
words `8`, `9` and the words of `[lo, hi)` in `Good`, and to a larger set and a larger range. -/
theorem SelOutLevelListsAt.transfer {w lo hi lo' hi' slot : ℕ} {Good Good' : ℕ → Prop}
    {mem mem' : ℕ → ℕ} {D : LevelDiffLists} {G : MGraph} {U : List Update}
    (h : SelOutLevelListsAt w Good lo hi mem slot D G U)
    (hS : ∀ i < 12, i ≠ 8 → i ≠ 9 → mem' (slot + i) = mem (slot + i))
    (hag : ∀ a, lo ≤ a → a < hi → Good a → mem' a = mem a)
    (hGood : ∀ a, lo ≤ a → a < hi → Good a → Good' a) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    SelOutLevelListsAt w Good' lo' hi' mem' slot D G U := by
  obtain ⟨⟨hL1, hL0, hL3, hL2, hL5, hL4, hR1, hR0⟩, hG0, hG2, hG4, hG6, hB, hBW, hBG⟩ := h
  have e0 := hS 0 (by omega) (by omega) (by omega)
  have e1 := hS 1 (by omega) (by omega) (by omega)
  have e2 := hS 2 (by omega) (by omega) (by omega)
  have e3 := hS 3 (by omega) (by omega) (by omega)
  have e4 := hS 4 (by omega) (by omega) (by omega)
  have e5 := hS 5 (by omega) (by omega) (by omega)
  have e6 := hS 6 (by omega) (by omega) (by omega)
  have e7 := hS 7 (by omega) (by omega) (by omega)
  have e10 := hS 10 (by omega) (by omega) (by omega)
  have e11 := hS 11 (by omega) (by omega) (by omega)
  have hagW : ∀ {a n : ℕ}, SelOutGoodAt Good lo hi a n → ∀ t < n, mem' (a + t) = mem (a + t) :=
    fun hg t ht => hag _ (by have := hg.1; omega) (by have := hg.2.1; omega) (hg.2.2 t ht)
  have hl : ∀ {a : ℕ} {xs : List ℕ}, ListAt mem a xs → SelOutGoodAt Good lo hi a xs.length →
      ListAt mem' a xs := fun hx hg => listAt_of_agree hx (hagW hg)
  have hm := fun {a n : ℕ} (hg : SelOutGoodAt Good lo hi a n) => hg.mono hGood hlo hhi
  refine ⟨⟨e1.trans hL1, ?_, e3.trans hL3, ?_, e5.trans hL5, ?_, e7.trans hR1, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [e0]; exact hl hL0 hG0
  · rw [e2]; exact hl hL2 hG2
  · rw [e4]; exact hl hL4 hG4
  · rw [e6]; exact hl hR0 (hR1 ▸ hG6)
  · rw [e0]; exact hm hG0
  · rw [e2]; exact hm hG2
  · rw [e4]; exact hm hG4
  · rw [e6]; exact hm hG6
  · rw [e10, e11]; exact ⟨batchAt_of_agree' hB.1 (hagW hBG), hB.2⟩
  · rw [e10, e11]
    exact fun t ht => by rw [hagW hBG t ht]; exact hBW t ht
  · rw [e10, e11]; exact hm hBG

/-- The level `j` becomes finished again after a new read of its descriptor. At the memory `mem`
the levels `r < j` are finished and level `j` has its lists and its batch, and every footprint lies
below `hi`. From `mem` to `mem'`, the program wrote below `hi` only the footprint of core `j` and
the two descriptor words `8`, `9` of the slot of level `j`, the footprints of the cores `r > j`,
and words below `lo` that lie off the footprints of the levels `r < j` and off the slots. These
now name a descriptor at `cur + 5`
(with `hi ≤ cur`) whose tables lie in the new footprint of core `j` or in `[cur, cur + 5)`. The new
footprint of core `j` lies in the old one and in `[hi, cur + 5)`, the footprints of the levels
`r < j` do not change, and the other footprints gain only words of `[hi, cur)`. -/
theorem BranchBDoneSlots.refresh {w P d lo hi cur selBase j Lw : ℕ} {Lmax : ℕ → ℕ}
    {foot foot' : ℕ → ℕ → Prop} {mem mem' : ℕ → ℕ} {D : ℕ → LevelDiffLists} {G : ℕ → MGraph}
    {U : ℕ → List Update} {E : ℕ → Finset ℕ} {vals : ℕ → ℕ → ℝ}
    (hDone : BranchBDoneSlots w P d Lmax foot lo hi selBase mem j D G U E vals)
    (hLists : SelOutLevelListsAt w (fun x => ∀ r < d, ¬ foot r x) lo hi mem
      (selBase + 1 + 12 * j) (D j) (G j) (U j))
    (hj : j < d) (hlohi : lo ≤ hi) (hhi : hi ≤ cur)
    (hFootSame : ∀ r < j, ∀ x, foot' r x ↔ foot r x)
    (hFootOther : ∀ r < d, r ≠ j → ∀ x, foot' r x → foot r x ∨ (hi ≤ x ∧ x < cur))
    (hFootNew : ∀ x, foot' j x → foot j x ∨ (hi ≤ x ∧ x < cur + 5))
    (hFootLt : ∀ r < d, ∀ x, foot r x → x < hi)
    (hDisj : ∀ r < d, r ≠ j → ∀ x, foot r x → ¬ foot j x)
    (hSlotLo : selBase + 1 + 12 * d ≤ lo)
    (hSlotOff : ∀ r < d, ∀ i < 12 * d, ¬ foot r (selBase + 1 + i))
    (hKeep : ∀ x < hi, ¬ foot j x → x ≠ selBase + 1 + 12 * j + 8 →
      x ≠ selBase + 1 + 12 * j + 9 →
      (lo ≤ x ∨ (∃ r < j, foot r x) ∨ (selBase + 1 ≤ x ∧ x < selBase + 1 + 12 * d)) →
      mem' x = mem x)
    (h8 : mem' (selBase + 1 + 12 * j + 8) = cur + 5)
    (h9 : mem' (selBase + 1 + 12 * j + 9) = Lw) (hLw : Lw ≤ Lmax j)
    (hSV : StretchValuesAt mem' (cur + 5) 4 Lw P (E j) (vals j))
    (hT0 : SelOutTableAt w (foot' j) cur (cur + 5) mem' (cur + 5) Lw (E j))
    (hT1 : SelOutTableAt w (foot' j) cur (cur + 5) mem' (cur + 5 + 1) Lw (E j)) :
    BranchBDoneSlots w P d Lmax foot' lo (cur + 7) selBase mem' (j + 1) D G U E vals := by
  have hReg : ∀ r < d, ∀ x, lo ≤ x → x < hi → foot' r x → foot r x := fun r _ x _ h2 hf => by
    by_cases hrj : r = j
    · subst hrj
      rcases hFootNew x hf with h' | h'
      · exact h'
      · omega
    · rcases hFootOther r (by omega) hrj x hf with h' | h'
      · exact h'
      · omega
  have hGood : ∀ x, lo ≤ x → x < hi → (∀ r < d, ¬ foot r x) → ∀ r < d, ¬ foot' r x :=
    fun x h1 h2 hn r hr hf => hn r hr (hReg r hr x h1 h2 hf)
  -- a word at or above `cur` that is off the new footprint of core `j` is off every footprint
  have hHigh : ∀ x, cur ≤ x → ¬ foot' j x → ∀ r < d, ¬ foot' r x := fun x hx hn r hr hf => by
    by_cases hrj : r = j
    · subst hrj; exact hn hf
    · rcases hFootOther r hr hrj x hf with h' | h'
      · have := hFootLt r hr x h'; omega
      · omega
  have hRows : ∀ {a : ℕ}, SelOutTableAt w (foot' j) cur (cur + 5) mem' a Lw (E j) →
      SelOutRowsAt w (fun x => foot' j x ∨ (lo ≤ x ∧ x < cur + 7 ∧ ∀ r < d, ¬ foot' r x))
        (cur + 7) mem' a Lw (E j) := fun {a} hT =>
    ⟨hT.1, fun e he => ⟨by have := (hT.2 e he).1; omega, fun t ht => by
      by_cases hf : foot' j (mem' a + e * Lw + t)
      · exact Or.inl hf
      · rcases (hT.2 e he).2 t ht with h' | ⟨h1, h2⟩
        · exact absurd h' hf
        · exact Or.inr ⟨by omega, by omega, hHigh _ h1 hf⟩⟩⟩
  refine BranchBDoneSlots.succ ?_ ?_
  · refine hDone.frame (by omega) (fun r hr x => hFootSame r hr x) hReg
      (fun a ha => ?_) (fun r hr i hi12 => ?_)
    · rcases ha with ⟨r, hr, hf⟩ | ⟨h1, h2, hg⟩
      · have := hFootLt r (by omega) a hf
        refine hKeep a this (hDisj r (by omega) (by omega) a hf) ?_ ?_
          (Or.inr (Or.inl ⟨r, hr, hf⟩))
        · rintro rfl
          exact hSlotOff r (by omega) (12 * j + 8) (by omega)
            (by rw [show selBase + 1 + (12 * j + 8) = selBase + 1 + 12 * j + 8 by omega]; exact hf)
        · rintro rfl
          exact hSlotOff r (by omega) (12 * j + 9) (by omega)
            (by rw [show selBase + 1 + (12 * j + 9) = selBase + 1 + 12 * j + 9 by omega]; exact hf)
      · exact hKeep a (by omega) (hg j hj) (by omega) (by omega) (Or.inl h1)
    · refine hKeep _ (by omega) ?_ (by omega) (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))
      have := hSlotOff j hj (12 * r + i) (by omega)
      rwa [← Nat.add_assoc] at this
  · refine SelOutLevelMemAt.of_lists
      (hLists.transfer (fun i hi12 h8' h9' => ?_) (fun a h1 h2 hg => ?_) hGood le_rfl
        (by omega)) ?_ (by rw [h9]; exact hLw) (by rw [h8, h9]; exact hSV)
      (by rw [h8, h9]; exact hRows hT0) (by rw [h8, h9]; exact hRows hT1)
    · refine hKeep _ (by omega) ?_ (by omega) (by omega) (Or.inr (Or.inr ⟨by omega, by omega⟩))
      have := hSlotOff j hj (12 * j + i) (by omega)
      rwa [← Nat.add_assoc] at this
    · exact hKeep a (by omega) (hg j hj) (by omega) (by omega) (Or.inl h1)
    · rw [h8]
      refine ⟨by omega, le_rfl, fun t ht => hHigh _ (by omega) fun hf => ?_⟩
      rcases hFootNew _ hf with h' | h'
      · have := hFootLt j hj _ h'; omega
      · omega

/-- The memory clauses of `UpdateCoreSelectOutAt` at a finished level, for a final footprint `F`
that contains the footprint of every core and no word of the region `[lo, hi)` that lies off all
of them, and for a select base `lo' ≤ lo`. -/
theorem BranchBDoneSlots.level {w P d lo lo' hi selBase n j : ℕ} {Lmax : ℕ → ℕ}
    {foot : ℕ → ℕ → Prop} {F : ℕ → Prop} {mem : ℕ → ℕ} {D : ℕ → LevelDiffLists}
    {G : ℕ → MGraph} {U : ℕ → List Update} {E : ℕ → Finset ℕ} {vals : ℕ → ℕ → ℝ}
    (h : BranchBDoneSlots w P d Lmax foot lo hi selBase mem n D G U E vals) (hj : j < n)
    (hlo' : lo' ≤ lo)
    (hF : ∀ a, lo ≤ a → a < hi → (∀ r < d, ¬ foot r a) → ¬ F a)
    (hT : ∀ a, foot j a → F a) :
    let slot := selBase + 1 + 12 * j
    LevelDiffListsAt mem slot (D j) ∧
    SelOutWordsAt F lo' hi (mem (slot + 0)) (D j).uG.length ∧
    SelOutWordsAt F lo' hi (mem (slot + 2)) (D j).fDel.length ∧
    SelOutWordsAt F lo' hi (mem (slot + 4)) (D j).uS.length ∧
    SelOutWordsAt F lo' hi (mem (slot + 6)) (D j).reemb.length ∧
    SmallBatchAt mem (mem (slot + 10)) (G j) (U j) (mem (slot + 11)) ∧
    (∀ t < mem (slot + 11), mem (mem (slot + 10) + t) < 2 ^ w) ∧
    SelOutWordsAt F lo' hi (mem (slot + 10)) (mem (slot + 11)) ∧
    SelOutWordsAt F lo' hi (mem (slot + 8)) 2 ∧
    mem (slot + 9) ≤ Lmax j ∧
    StretchValuesAt mem (mem (slot + 8)) 4 (mem (slot + 9)) P (E j) (vals j) ∧
    SelOutTableAt w F lo' hi mem (mem (slot + 8)) (mem (slot + 9)) (E j) ∧
    SelOutTableAt w F lo' hi mem (mem (slot + 8) + 1) (mem (slot + 9)) (E j) := by
  have h1 := (h j hj).transfer (Good' := fun x => lo ≤ x ∧ ∀ r < d, ¬ foot r x)
    (InTab' := fun x => foot j x ∨ (lo' ≤ x ∧ x < hi)) (mem' := mem)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ ha _ hg => ⟨ha, hg⟩)
    (fun a ha => ha.imp id fun h' => ⟨by omega, h'.2.1⟩) hlo' le_rfl
  exact h1.toSelectOut (fun a _ ha2 hg => hF a hg.1 ha2 hg.2)
    (fun a ha => ha.imp (hT a) id)

/-- Copy the level-`0` batch at `reg 10` (`reg 11` words) to the first free word `reg 4`, point
`reg 10` at the copy, and move `reg 4` past it. -/
@[expose] def wireBranchBCopyBatch0Stmt (copyProc : ℕ) : Stmt :=
  .call 30 copyProc [.reg 11, .reg 10, .reg 4] ;;
  .assign 10 (.reg 4) ;;
  .assign 4 (.bin .add (.reg 4) (.reg 11))

theorem wireBranchBCopyBatch0Stmt_noRand (copyProc : ℕ) :
    (wireBranchBCopyBatch0Stmt copyProc).NoRand := by
  simp [wireBranchBCopyBatch0Stmt, Stmt.NoRand]

/-- One run of `wireBranchBCopyBatch0Stmt`. The batch at `src` in `n` words lies below the first
free word `heap`. The run copies it to `heap`, changes no other word, and costs at most `20` steps
per word and a constant. -/
theorem wireBranchBCopyBatch0Stmt_runs {w copyProc src n heap : ℕ} {p : Program} {ω : ℕ → Bool}
    {s : State} {G : MGraph} {U : List Update}
    (hw : 6 < 2 ^ w) (hCopy : p.procs[copyProc]? = some wireRawCopyBody)
    (hr4 : s.regs 4 = heap) (hr10 : s.regs 10 = src) (hr11 : s.regs 11 = n)
    (hB : SmallBatchAt s.mem src G U n) (hW : ∀ t < n, s.mem (src + t) < 2 ^ w)
    (hle : src + n ≤ heap) (hRoom : heap + n < 2 ^ w) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω (wireBranchBCopyBatch0Stmt copyProc) s .normal out cost ∧
      out.regs 10 = heap ∧ out.regs 4 = heap + n ∧
      (∀ r, r ≠ 4 → r ≠ 10 → r ≠ 30 → out.regs r = s.regs r) ∧
      SmallBatchAt out.mem heap G U n ∧ (∀ t < n, out.mem (heap + t) < 2 ^ w) ∧
      (∀ a, a < heap ∨ heap + n ≤ a → out.mem a = s.mem a) ∧
      cost ≤ 20 * n + 30 := by
  have hCopyC := wireRawCopyBody_meets (w := w) hCopy
  suffices hs : ∃ o st' cost, Runs w p ω (wireBranchBCopyBatch0Stmt copyProc) s o st' cost ∧
      (o = .normal ∧ st'.regs 10 = heap ∧ st'.regs 4 = heap + n ∧
        (∀ r, r ≠ 4 → r ≠ 10 → r ≠ 30 → st'.regs r = s.regs r) ∧
        (∀ t < n, st'.mem (heap + t) = s.mem (src + t)) ∧
        (∀ a, a < heap ∨ heap + n ≤ a → st'.mem a = s.mem a)) ∧
      0 + cost ≤ 20 * n + 30 by
    obtain ⟨o, st', cost, hr, ⟨rfl, h10, h4, hreg, hcp, hfr⟩, hc⟩ := hs
    refine ⟨st', cost, hr, h10, h4, hreg, smallBatchAt_shift hB hcp, fun t ht => ?_, hfr,
      by omega⟩
    rw [hcp t ht]; exact hW t ht
  unfold wireBranchBCopyBatch0Stmt
  refine runs_seq_call_le hCopyC (vs := [n, src, heap]) (by eval_expr) (by wram_words) ?_ ?_
  · simp only [wireRawCopyContract, List.getD_cons_zero, List.getD_cons_succ]
    exact ⟨trivial, by omega, by omega, by omega, Or.inl hle⟩
  intro v1 m2 pos2 ⟨hc2, hf2⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hc2 hf2
  refine runs_seq_assign_le (v := heap) (by eval_expr) ?_
  refine runs_assign_le (v := heap + n) (by eval_expr) ?_ ?_
  · refine ⟨rfl, by simp, by simp, fun r h4 h10 h30 => by simp [h4, h10, h30], hc2,
      fun a ha => hf2 a ha⟩
  · simp only [wireRawCopyContract, List.getD_cons_zero]
    wram_cost

end MinCostFlow.MinRatio
