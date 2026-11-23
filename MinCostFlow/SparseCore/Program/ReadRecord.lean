module

public import MinCostFlow.SparseCore.Program.ReadSpec

import WordRAM.Tactic

/-!
# The record of a branch and its two readouts

The data of one branch (`ReadView`) lives in blocks that the record at handle `r` points to. The
first nine words of the record are:

| word | content |
| --- | --- |
| `r` | pointer to the tree `T` (`DynGraphAt`, caps `vCap`, `tCap`) |
| `r + 1` | pointer to the forest `F` (`DynGraphAt`, caps `vCap`, `tCap`) |
| `r + 2` | pointer to the root bits (`RootsAt`, `vCap` words) |
| `r + 3` | the address `r + 7` of the stretch descriptor |
| `r + 4` | the limb count `L_w` |
| `r + 5` | pointer to `S` (`DynGraphAt`, caps `vCap`, `eCap`) |
| `r + 6` | pointer to the copy of `G` (`DynGraphAt`, caps `vCap`, `eCap`) |
| `r + 7`, `r + 8` | pointers to the numerator and denominator tables of the stretches |

So the words `r, …, r + 4` are the five words that readout `2` of the contract asks for, and word
`r + 5` is the word that readout `3` asks for. Each readout copies them to the heap
(`readLSF_runs`, `readS_runs`). Here `ReadRecAt` says that the record holds a `ReadView`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner.Program

/-- The pointers of a record: the blocks of `T`, `F`, the roots, `S`, `G`, and the numerator and
denominator tables. -/
structure ReadPtrs where
  t : ℕ
  f : ℕ
  roots : ℕ
  s : ℕ
  g : ℕ
  num : ℕ
  den : ℕ

/-- The number of words of the record itself. -/
def readRecWords : ℕ := 9

/-- The record at `r` holds the data `v` with pointers `q`: the nine words of the table in the
module docstring, and each block holds its part of `v`. The stretch tables have `L_w` limbs of `4`
bits at precision `P` for each edge of `G`, and they hold the pairs `num`, `den` of `v` exactly. -/
def ReadRecAt (mem : ℕ → ℕ) (r vCap eCap tCap L_w P : ℕ) (v : ReadView) (q : ReadPtrs) : Prop :=
  mem r = q.t ∧ mem (r + 1) = q.f ∧ mem (r + 2) = q.roots ∧ mem (r + 3) = r + 7 ∧
  mem (r + 4) = L_w ∧ mem (r + 5) = q.s ∧ mem (r + 6) = q.g ∧ mem (r + 7) = q.num ∧
  mem (r + 8) = q.den ∧
  DynGraphAt mem q.t vCap tCap v.lsf.T ∧ DynGraphAt mem q.f vCap tCap v.lsf.F.F ∧
  RootsAt mem q.roots vCap v.lsf.F.R ∧ StretchValuesAt mem (r + 7) 4 L_w P v.G.E v.lsf.wstr ∧
  StretchPairsAt mem (r + 7) L_w v.G.E v.num v.den ∧
  DynGraphAt mem q.s vCap eCap v.S ∧ DynGraphAt mem q.g vCap eCap v.G

/-- The cells of a record: its nine words and its seven blocks. The stretch tables have
`eCap · L_w` words each. -/
def ReadRecFoot (r vCap eCap tCap L_w : ℕ) (q : ReadPtrs) (a : ℕ) : Prop :=
  (r ≤ a ∧ a < r + readRecWords) ∨
  (q.t ≤ a ∧ a < q.t + dynGraphSize vCap tCap) ∨
  (q.f ≤ a ∧ a < q.f + dynGraphSize vCap tCap) ∨
  (q.roots ≤ a ∧ a < q.roots + vCap) ∨
  (q.s ≤ a ∧ a < q.s + dynGraphSize vCap eCap) ∨
  (q.g ≤ a ∧ a < q.g + dynGraphSize vCap eCap) ∨
  (q.num ≤ a ∧ a < q.num + eCap * L_w) ∨
  (q.den ≤ a ∧ a < q.den + eCap * L_w)

/-! ## The readout procedures -/

/-- Readout `2`, `[r, h]`: copy the words `r, …, r + 4` to `h, …, h + 4`, and return `h + 5`. -/
def readLSFStmt : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .store (.reg 1) (.reg 2) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.reg 2) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const 2))) ;;
  .store (.bin .add (.reg 1) (.const 2)) (.reg 2) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .store (.bin .add (.reg 1) (.const 3)) (.reg 2) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .store (.bin .add (.reg 1) (.const 4)) (.reg 2) ;;
  .ret (.bin .add (.reg 1) (.const 5))

/-- Readout `3`, `[r, h]`: copy the word `r + 5` to `h`, and return `h + 1`. -/
def readSStmt : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 5))) ;;
  .store (.reg 1) (.reg 2) ;;
  .ret (.bin .add (.reg 1) (.const 1))

/-- The readouts use no random bits. -/
theorem readLSFStmt_noRand : readLSFStmt.NoRand := by simp [readLSFStmt, Stmt.NoRand]

/-- The readouts use no random bits. -/
theorem readSStmt_noRand : readSStmt.NoRand := by simp [readSStmt, Stmt.NoRand]

/-! ## Runs of the readouts -/

/-- The run of `readLSFStmt`: it returns `h + 5`, writes `mem (r + i)` at `h + i` for `i < 5`, and
costs at most `80`. -/
theorem readLSFStmt_runs {w : ℕ} (p : Program) (ω : ℕ → Bool) (r h pos : ℕ) (mem : ℕ → ℕ)
    (hr : r + 4 < h) (hroom : h + 5 < 2 ^ w) :
    ∃ o st c, Runs w p ω readLSFStmt (startState [r, h] mem pos) o st c ∧
      (o.value = h + 5 ∧
        st.mem = Function.update (Function.update (Function.update (Function.update
          (Function.update mem h (mem r)) (h + 1) (mem (r + 1))) (h + 2) (mem (r + 2)))
          (h + 3) (mem (r + 3))) (h + 4) (mem (r + 4))) ∧
      c ≤ 80 := by
  apply runs_start_le
  unfold readLSFStmt
  wram_run
  · simp only [show r + 1 ≠ h by omega, show r + 2 ≠ h by omega, show r + 3 ≠ h by omega,
      show r + 4 ≠ h by omega]
    exact ⟨rfl, rfl⟩
  · wram_cost

/-- The run of `readSStmt`: it returns `h + 1`, writes `mem (r + 5)` at `h`, and costs at most
`20`. -/
theorem readSStmt_runs {w : ℕ} (p : Program) (ω : ℕ → Bool) (r h pos : ℕ) (mem : ℕ → ℕ)
    (hr : r + 5 < h) (hroom : h + 1 < 2 ^ w) :
    ∃ o st c, Runs w p ω readSStmt (startState [r, h] mem pos) o st c ∧
      (o.value = h + 1 ∧ st.mem = Function.update mem h (mem (r + 5))) ∧ c ≤ 20 := by
  apply runs_start_le
  unfold readSStmt
  wram_run
  · exact ⟨rfl, rfl⟩
  · wram_cost

/-! ## The readouts give the posts of the contract -/

/-- If the cells of a record are below `h` and a memory `out` agrees with `mem` below `h`, the
record holds the same data in `out`. -/
theorem ReadRecAt.of_agree {mem out : ℕ → ℕ} {r vCap eCap tCap L_w P h : ℕ} {v : ReadView}
    {q : ReadPtrs} (hrec : ReadRecAt mem r vCap eCap tCap L_w P v q)
    (hfoot : ∀ a, ReadRecFoot r vCap eCap tCap L_w q a → a < h)
    (hagree : ∀ a < h, out a = mem a) (hdom : ∀ e ∈ v.G.E, e < eCap) :
    ReadRecAt out r vCap eCap tCap L_w P v q := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hT, hF, hR, hS, hPr, hSc, hG⟩ := hrec
  have hw (i : ℕ) (hi : i < readRecWords) : out (r + i) = mem (r + i) :=
    hagree _ (hfoot _ (Or.inl ⟨by omega, by omega⟩))
  have hblk (b n : ℕ) (hb : ∀ a, b ≤ a → a < b + n → ReadRecFoot r vCap eCap tCap L_w q a) :
      ∀ a, b ≤ a → a < b + n → out a = mem a :=
    fun a ha1 ha2 => hagree a (hfoot a (hb a ha1 ha2))
  have hnum (e : ℕ) (he : e ∈ v.G.E) (i : ℕ) (hi : i < L_w) :
      out (q.num + e * L_w + i) = mem (q.num + e * L_w + i) := by
    have heC := hdom e he
    have hlt : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right _ (by omega)
    exact hblk q.num (eCap * L_w)
      (fun a h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))))))
      _ (by omega) (by rw [Nat.add_mul, one_mul] at hlt; omega)
  have hden (e : ℕ) (he : e ∈ v.G.E) (i : ℕ) (hi : i < L_w) :
      out (q.den + e * L_w + i) = mem (q.den + e * L_w + i) := by
    have heC := hdom e he
    have hlt : (e + 1) * L_w ≤ eCap * L_w := Nat.mul_le_mul_right _ (by omega)
    exact hblk q.den (eCap * L_w)
      (fun a h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2⟩)))))))
      _ (by omega) (by rw [Nat.add_mul, one_mul] at hlt; omega)
  have hnP : out (r + 7) = q.num := (hw 7 (by decide)).trans h7
  have hdP : out (r + 7 + 1) = q.den := (hw 8 (by decide)).trans h8
  have hnP' : mem (r + 7) = q.num := h7
  have hdP' : mem (r + 7 + 1) = q.den := h8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show r = r + 0 from rfl, hw 0 (by decide)]; exact h0
  · rw [hw 1 (by decide)]; exact h1
  · rw [hw 2 (by decide)]; exact h2
  · rw [hw 3 (by decide)]; exact h3
  · rw [hw 4 (by decide)]; exact h4
  · rw [hw 5 (by decide)]; exact h5
  · rw [hw 6 (by decide)]; exact h6
  · rw [hw 7 (by decide)]; exact h7
  · rw [hw 8 (by decide)]; exact h8
  · exact hT.of_agree (hblk q.t _ fun a h1 h2 => Or.inr (Or.inl ⟨h1, h2⟩))
  · exact hF.of_agree (hblk q.f _ fun a h1 h2 => Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
  · refine ⟨hR.1, fun x hx => ?_⟩
    have := hblk q.roots vCap (fun a h1 h2 => Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
      (q.roots + x) (by omega) (by omega)
    rw [this]; exact hR.2 x hx
  · intro e he
    obtain ⟨hvN, hvD, hpos, hval⟩ := hS e he
    rw [hnP'] at hvN
    rw [hdP'] at hvD hpos
    rw [hnP', hdP'] at hval
    rw [hnP, hdP]
    refine ⟨fun i hi => (hnum e he i hi).trans_lt (hvN i hi),
      fun i hi => (hden e he i hi).trans_lt (hvD i hi), ?_, ?_⟩
    · simpa only [Num.fixVal, Num.intVal_congr (hden e he)] using hpos
    · simpa only [Num.fixVal, Num.intVal_congr (hnum e he), Num.intVal_congr (hden e he)]
        using hval
  · intro e he
    obtain ⟨hN, hD⟩ := hPr e he
    rw [hnP'] at hN
    rw [hdP'] at hD
    rw [hnP, hdP, Num.intVal_congr (hnum e he), Num.intVal_congr (hden e he)]
    exact ⟨hN, hD⟩
  · exact hSc.of_agree (hblk q.s _ fun a h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h1, h2⟩)))))
  · exact hG.of_agree (hblk q.g _ fun a h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨h1, h2⟩))))))

/-- **Readout `2`.** If the record at `r` holds `v` and its cells are below `h`, then
`readLSFStmt` on `[r, h]` writes `ReadLSFOut` at `h`, keeps the memory below `h`, returns `h + 5`
and costs at most `80`. -/
theorem readLSF_runs {w : ℕ} (p : Program) (ω : ℕ → Bool) {r h pos vCap eCap tCap L_w P : ℕ}
    {mem : ℕ → ℕ} {v : ReadView} {q : ReadPtrs}
    (hrec : ReadRecAt mem r vCap eCap tCap L_w P v q)
    (hfoot : ∀ a, ReadRecFoot r vCap eCap tCap L_w q a → a < h)
    (hdom : ∀ e ∈ v.G.E, e < eCap) (hroom : h + 5 < 2 ^ w) :
    ∃ o st c, Runs w p ω readLSFStmt (startState [r, h] mem pos) o st c ∧
      o.value = h + 5 ∧ ReadLSFOut st.mem h L_w P v ∧ (∀ a < h, st.mem a = mem a) ∧
      (∀ a, h + 5 ≤ a → st.mem a = mem a) ∧ c ≤ 80 := by
  have hr8 : r + 8 < h := hfoot _ (Or.inl ⟨by omega, by simp [readRecWords]⟩)
  obtain ⟨o, st, c, hrun, ⟨ho, hm⟩, hc⟩ := readLSFStmt_runs p ω r h pos mem (by omega) hroom
  have hbelow : ∀ a < h, st.mem a = mem a := by
    intro a ha
    rw [hm]
    simp only [Function.update_of_ne (show a ≠ h + 4 by omega),
      Function.update_of_ne (show a ≠ h + 3 by omega), Function.update_of_ne (show a ≠ h + 2 by omega),
      Function.update_of_ne (show a ≠ h + 1 by omega), Function.update_of_ne (show a ≠ h by omega)]
  have habove : ∀ a, h + 5 ≤ a → st.mem a = mem a := by
    intro a ha
    rw [hm]
    simp only [Function.update_of_ne (show a ≠ h + 4 by omega),
      Function.update_of_ne (show a ≠ h + 3 by omega), Function.update_of_ne (show a ≠ h + 2 by omega),
      Function.update_of_ne (show a ≠ h + 1 by omega), Function.update_of_ne (show a ≠ h by omega)]
  have hrec' := hrec.of_agree hfoot hbelow hdom
  obtain ⟨h0, h1, h2, h3, h4, _, _, _, _, hT, hF, hR, hS, hPr, _, _⟩ := hrec'
  have hh (i : ℕ) (hi : i < 5) : st.mem (h + i) = mem (r + i) := by
    rw [hm]
    interval_cases i <;> simp [Function.update_of_ne]
  have hrw (i : ℕ) (hi : i < 5) : st.mem (h + i) = st.mem (r + i) :=
    (hh i hi).trans (hbelow (r + i) (by omega)).symm
  refine ⟨o, st, c, hrun, ho, ⟨?_, ⟨vCap, tCap, ?_⟩, ?_⟩, hbelow, habove, hc⟩
  · rw [hrw 4 (by decide)]; exact h4
  · unfold LSFAt
    rw [show h = h + 0 from rfl, hrw 0 (by decide), hrw 1 (by decide), hrw 2 (by decide),
      hrw 3 (by decide), show r + 0 = r from rfl, h0, h1, h2, h3]
    exact ⟨hT, hF, hR, hS⟩
  · rw [hrw 3 (by decide), h3]
    exact hPr

/-- **Readout `3`.** If the record at `r` holds `v` and its cells are below `h`, then `readSStmt`
on `[r, h]` writes `ReadSOut` at `h`, keeps the memory below `h`, returns `h + 1` and costs at
most `20`. -/
theorem readS_runs {w : ℕ} (p : Program) (ω : ℕ → Bool) {r h pos vCap eCap tCap L_w P : ℕ}
    {mem : ℕ → ℕ} {v : ReadView} {q : ReadPtrs}
    (hrec : ReadRecAt mem r vCap eCap tCap L_w P v q)
    (hfoot : ∀ a, ReadRecFoot r vCap eCap tCap L_w q a → a < h)
    (hdom : ∀ e ∈ v.G.E, e < eCap) (hroom : h + 1 < 2 ^ w) :
    ∃ o st c, Runs w p ω readSStmt (startState [r, h] mem pos) o st c ∧
      o.value = h + 1 ∧ ReadSOut st.mem h v ∧ (∀ a < h, st.mem a = mem a) ∧
      (∀ a, h + 1 ≤ a → st.mem a = mem a) ∧ c ≤ 20 := by
  have hr8 : r + 8 < h := hfoot _ (Or.inl ⟨by omega, by simp [readRecWords]⟩)
  obtain ⟨o, st, c, hrun, ⟨ho, hm⟩, hc⟩ := readSStmt_runs p ω r h pos mem (by omega) hroom
  have hbelow : ∀ a < h, st.mem a = mem a := by
    intro a ha
    rw [hm, Function.update_of_ne (show a ≠ h by omega)]
  have habove : ∀ a, h + 1 ≤ a → st.mem a = mem a := by
    intro a ha
    rw [hm, Function.update_of_ne (show a ≠ h by omega)]
  have hrec' := hrec.of_agree hfoot hbelow hdom
  obtain ⟨_, _, _, _, _, h5, _, _, _, _, _, _, _, _, hSc, _⟩ := hrec'
  have hh : st.mem h = st.mem (r + 5) := by
    rw [hbelow (r + 5) (by omega), hm]; simp
  refine ⟨o, st, c, hrun, ho, ⟨vCap, eCap, ?_⟩, hbelow, habove, hc⟩
  rw [hh, h5]
  exact hSc

end MinCostFlow.SparseCore.Program.Read
