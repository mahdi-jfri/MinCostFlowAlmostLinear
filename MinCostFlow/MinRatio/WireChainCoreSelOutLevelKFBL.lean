module

public import MinCostFlow.MinRatio.WireChainCoreSelOutSlotKFBL
import MinCostFlow.SparseCore.Program.AssemblyReemb

/-!
# The memory clauses of one select-output slot (`WireChainCoreSelOutLevelKFBL`)

`selOutLevelMem_of_slotPost` turns the output of `wireSelOutSlotBody` (`SelOutSlotPost`) into the
memory clauses of one level of `UpdateCoreSelectOutAt`, at the final memory of the chain-update
core. The slot writer stores only the places of the copies that the core made earlier in the level
(the `fDel` list, the re-embedding list and the stretch descriptor), so the facts on those copies
come in as facts at the final memory. From the slot writer the lemma needs that the final memory
keeps the slot and the two touched-edge lists. The model clauses of the level (which lists these
are) are not memory facts, and the caller adds them.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

/-- The words `[a, a + n)` lie in `[lo, hi)` and off `foot` when `[a, a + n)` lies in `[b, c)`,
which lies in `[lo, hi)` and off `foot`. -/
theorem selOutWordsAt_of_sub {foot : ℕ → Prop} {lo hi a n b c : ℕ} (hlo : lo ≤ b) (hhi : c ≤ hi)
    (hoff : ∀ x, b ≤ x → x < c → ¬ foot x) (hab : b ≤ a) (hac : a + n ≤ c) :
    SelOutWordsAt foot lo hi a n :=
  ⟨by omega, by omega, fun t ht => hoff _ (by omega) (by omega)⟩

/-- A list that the final memory keeps. -/
theorem listAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {xs : List ℕ} (h : ListAt mem₁ a xs)
    (hag : ∀ t < xs.length, mem₂ (a + t) = mem₁ (a + t)) : ListAt mem₂ a xs :=
  fun i hi => by rw [hag i hi]; exact h i hi

/-- The memory clauses of one level of `UpdateCoreSelectOutAt`, from `SelOutSlotPost` at the
memory `out1` that the slot writer leaves, for a final memory `memF` that keeps the slot and the
words from `hp` to the returned pointer. Those words lie in `[lo, hi)` and off the final footprint
`F`. The copies of `fDel` and of the re-embedding list, the batch and the descriptor come with
their facts at `memF`. -/
theorem selOutLevelMem_of_slotPost {w P Lmax lo hi slot hp fDelPtr reembPtr reembLen descPtr Lw
      uPtr uWords : ℕ}
    {F : ℕ → Prop} {mem1 out1 memF : ℕ → ℕ} {fDel reemb uG uS : List ℕ}
    {G : MGraph} {U : List Update} {E : Finset ℕ} {vals : ℕ → ℝ}
    (hpost : SelOutSlotPost mem1 out1 slot hp fDelPtr fDel.length reembPtr reembLen descPtr Lw
      uPtr uWords uG uS)
    (hagS : ∀ i < 12, memF (slot + i) = out1 (slot + i))
    (hagH : ∀ a, hp ≤ a → a < hp + uG.length + uS.length → memF a = out1 a)
    (hHlo : lo ≤ hp) (hHhi : hp + uG.length + uS.length ≤ hi)
    (hHF : ∀ a, hp ≤ a → a < hp + uG.length + uS.length → ¬ F a)
    (hF : ListAt memF fDelPtr fDel) (hFW : SelOutWordsAt F lo hi fDelPtr fDel.length)
    (hR : ReembListAt memF reembPtr reembLen reemb)
    (hRW : SelOutWordsAt F lo hi reembPtr reemb.length)
    (hB : BatchAt memF uPtr G U uWords) (hBW : ∀ t < uWords, memF (uPtr + t) < 2 ^ w)
    (hBF : SelOutWordsAt F lo hi uPtr uWords)
    (hDW : SelOutWordsAt F lo hi descPtr 2) (hLw : Lw ≤ Lmax)
    (hSV : StretchValuesAt memF descPtr 4 Lw P E vals)
    (hT0 : SelOutTableAt w F lo hi memF descPtr Lw E)
    (hT1 : SelOutTableAt w F lo hi memF (descPtr + 1) Lw E) :
    LevelDiffListsAt memF slot ⟨uG, fDel, uS, reemb⟩ ∧
    SelOutWordsAt F lo hi (memF (slot + 0)) uG.length ∧
    SelOutWordsAt F lo hi (memF (slot + 2)) fDel.length ∧
    SelOutWordsAt F lo hi (memF (slot + 4)) uS.length ∧
    SelOutWordsAt F lo hi (memF (slot + 6)) reemb.length ∧
    BatchAt memF (memF (slot + 10)) G U (memF (slot + 11)) ∧
    (∀ t < memF (slot + 11), memF (memF (slot + 10) + t) < 2 ^ w) ∧
    SelOutWordsAt F lo hi (memF (slot + 10)) (memF (slot + 11)) ∧
    SelOutWordsAt F lo hi (memF (slot + 8)) 2 ∧
    memF (slot + 9) ≤ Lmax ∧
    StretchValuesAt memF (memF (slot + 8)) 4 (memF (slot + 9)) P E vals ∧
    SelOutTableAt w F lo hi memF (memF (slot + 8)) (memF (slot + 9)) E ∧
    SelOutTableAt w F lo hi memF (memF (slot + 8) + 1) (memF (slot + 9)) E := by
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hG, hS, _, _⟩ := hpost
  have m0 : memF (slot + 0) = hp := (hagS 0 (by omega)).trans hs0
  have m1 : memF (slot + 1) = uG.length := (hagS 1 (by omega)).trans hs1
  have m2 : memF (slot + 2) = fDelPtr := (hagS 2 (by omega)).trans hs2
  have m3 : memF (slot + 3) = fDel.length := (hagS 3 (by omega)).trans hs3
  have m4 : memF (slot + 4) = hp + uG.length := (hagS 4 (by omega)).trans hs4
  have m5 : memF (slot + 5) = uS.length := (hagS 5 (by omega)).trans hs5
  have m6 : memF (slot + 6) = reembPtr := (hagS 6 (by omega)).trans hs6
  have m7 : memF (slot + 7) = reembLen := (hagS 7 (by omega)).trans hs7
  have m8 : memF (slot + 8) = descPtr := (hagS 8 (by omega)).trans hs8
  have m9 : memF (slot + 9) = Lw := (hagS 9 (by omega)).trans hs9
  have m10 : memF (slot + 10) = uPtr := (hagS 10 (by omega)).trans hs10
  have m11 : memF (slot + 11) = uWords := (hagS 11 (by omega)).trans hs11
  have hsub := fun {a n : ℕ} (hab : hp ≤ a) (hac : a + n ≤ hp + uG.length + uS.length) =>
    selOutWordsAt_of_sub (foot := F) (lo := lo) (hi := hi) (a := a) (n := n) hHlo hHhi hHF hab hac
  rw [m2, m4, m6, m8, m9, m10, m11]
  refine ⟨⟨m1, ?_, m3, ?_, m5, ?_, ⟨m7 ▸ hR.1, ?_⟩⟩, by rw [m0]; exact hsub le_rfl (by omega),
    hFW, hsub (by omega) le_rfl, hRW, hB, hBW, hBF, hDW, hLw, hSV, hT0, hT1⟩
  · rw [m0]; exact listAt_of_agree hG fun t (ht : t < uG.length) => hagH (hp + t) (by omega) (by omega)
  · rw [m2]; exact hF
  · rw [m4]; exact listAt_of_agree hS fun t (ht : t < uS.length) =>
      hagH (hp + uG.length + t) (by omega) (by omega)
  · rw [m6]; exact hR.2

end MinCostFlow.MinRatio
