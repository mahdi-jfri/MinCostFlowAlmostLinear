module

public import MinCostFlow.SparseCore.Program.ReadRep

/-!
# The representation after a change of the blocks

One update of the input batch rewrites the blocks of `T`, `F`, `G`, the live and the frozen part,
and the stretch tables, and leaves the other cells: the eleven words of the record, the root bits
and the block of `S` (`readFixed`). `ReadRepAt.change` says that the representation then holds
the new data, if each rewritten block holds its new part and `ReadKeep` holds for the new data.

`stretch_step` gives the stretch facts after such a change: each edge keeps its cells and its
values, or has the new pair `(1, 1)` and the stretch `1`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open WordRAM MinCostFlow.MinRatio MinCostFlow.DynSpanner.Program

/-- The cells that an update of one entry of the batch does not write: the words of the record,
the root bits and the block of `S`. -/
def readFixed (vCap eCap r : ℕ) (y : ReadConc) (a : ℕ) : Prop :=
  (r ≤ a ∧ a < r + readFullWords) ∨ (y.q.roots ≤ a ∧ a < y.q.roots + vCap) ∨
    (y.q.s ≤ a ∧ a < y.q.s + dynGraphSize vCap eCap)

/-- **The representation after a change of the blocks.** If the fixed cells keep their values,
the new data `v'` has the roots and `S` of `v` and meets `ReadKeep`, and each block holds its new
part, the representation holds `v'`. -/
theorem ReadRepAt.change {vCap eCap tCap L_w P r : ℕ} {v v' : ReadView} {y : ReadConc}
    {mem mem' : ℕ → ℕ} (hrep : ReadRepAt vCap eCap tCap L_w P r v y mem) (hkeep : ReadKeep v')
    (hS : v'.S = v.S) (hR : v'.lsf.F.R = v.lsf.F.R)
    (hfix : ∀ a, readFixed vCap eCap r y a → mem' a = mem a)
    (hT : DynGraphAt mem' y.q.t vCap tCap v'.lsf.T)
    (hF : DynGraphAt mem' y.q.f vCap tCap v'.lsf.F.F)
    (hG : DynGraphAt mem' y.q.g vCap eCap v'.G)
    (hlive : DynGraphAt mem' y.live vCap eCap (liveT v'.G v'.lsf.T))
    (hfrz : DynGraphAt mem' y.frz vCap tCap (frozenT v'.G v'.lsf.T))
    (hval : StretchValuesAt mem' (r + 7) 4 L_w P v'.G.E v'.lsf.wstr)
    (hpairs : StretchPairsAt mem' (r + 7) L_w v'.G.E v'.num v'.den) :
    ReadRepAt vCap eCap tCap L_w P r v' { y with view := v' } mem' := by
  obtain ⟨-, hlay, -, hrec, h9, h10, -, -⟩ := hrep
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, -, -, hRoots, -, -, hSc, -⟩ := hrec
  have hw (i : ℕ) (hi : i < readFullWords) : mem' (r + i) = mem (r + i) :=
    hfix _ (Or.inl ⟨by omega, by omega⟩)
  refine ⟨rfl, hlay, hkeep, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hT, hF, ?_, hval, hpairs, ?_, hG⟩,
    ?_, ?_, hlive, hfrz⟩
  · rw [show r = r + 0 from rfl, hw 0 (by decide)]; exact h0
  · rw [hw 1 (by decide)]; exact h1
  · rw [hw 2 (by decide)]; exact h2
  · rw [hw 3 (by decide)]; exact h3
  · rw [hw 4 (by decide)]; exact h4
  · rw [hw 5 (by decide)]; exact h5
  · rw [hw 6 (by decide)]; exact h6
  · rw [hw 7 (by decide)]; exact h7
  · rw [hw 8 (by decide)]; exact h8
  · rw [hR]
    refine ⟨hRoots.1, fun x hx => ?_⟩
    rw [hfix (y.q.roots + x) (Or.inr (Or.inl ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hx _⟩))]
    exact hRoots.2 x hx
  · rw [hS]
    exact hSc.of_agree fun a h1 h2 => hfix a (Or.inr (Or.inr ⟨h1, h2⟩))
  · rw [hw 9 (by decide)]; exact h9
  · rw [hw 10 (by decide)]; exact h10

/-! ## The stretch tables -/

/-- An edge whose two blocks of limbs keep their cells. -/
def CellsKept (mem mem' : ℕ → ℕ) (numP denP L_w e : ℕ) : Prop :=
  ∀ i < L_w, mem' (numP + e * L_w + i) = mem (numP + e * L_w + i) ∧
    mem' (denP + e * L_w + i) = mem (denP + e * L_w + i)

/-- An edge whose two blocks of limbs hold the integer `1`. -/
def CellsOne (mem' : ℕ → ℕ) (numP denP L_w e : ℕ) : Prop :=
  Num.Valid mem' (numP + e * L_w) 4 L_w ∧ Num.Valid mem' (denP + e * L_w) 4 L_w ∧
    Num.intVal mem' (numP + e * L_w) 4 L_w = 1 ∧ Num.intVal mem' (denP + e * L_w) 4 L_w = 1

/-- **The stretch facts after a change.** Let the descriptor words keep their values. If each new
edge keeps its cells and its values, or holds `(1, 1)` and has stretch `1` and pair `(1, 1)`, the
stretch facts hold for the new edges. -/
theorem stretch_step {mem mem' : ℕ → ℕ} {a L_w P : ℕ} {E E' : Finset ℕ} {wstr wstr' : ℕ → ℝ}
    {num den num' den' : ℕ → ℤ} (hval : StretchValuesAt mem a 4 L_w P E wstr)
    (hpairs : StretchPairsAt mem a L_w E num den) (ha0 : mem' a = mem a)
    (ha1 : mem' (a + 1) = mem (a + 1))
    (hE : ∀ e ∈ E', (e ∈ E ∧ wstr' e = wstr e ∧ num' e = num e ∧ den' e = den e ∧
        CellsKept mem mem' (mem a) (mem (a + 1)) L_w e) ∨
      (CellsOne mem' (mem a) (mem (a + 1)) L_w e ∧ wstr' e = 1 ∧ num' e = 1 ∧ den' e = 1)) :
    StretchValuesAt mem' a 4 L_w P E' wstr' ∧ StretchPairsAt mem' a L_w E' num' den' := by
  constructor
  · intro e he
    rw [ha0, ha1]
    rcases hE e he with ⟨heE, hw, -, -, hk⟩ | ⟨⟨hvN, hvD, hN, hD⟩, hw, -, -⟩
    · obtain ⟨hvN, hvD, hpos, hq⟩ := hval e heE
      have hn : ∀ i < L_w, mem' (mem a + e * L_w + i) = mem (mem a + e * L_w + i) :=
        fun i hi => (hk i hi).1
      have hd : ∀ i < L_w, mem' (mem (a + 1) + e * L_w + i) = mem (mem (a + 1) + e * L_w + i) :=
        fun i hi => (hk i hi).2
      refine ⟨fun i hi => (hn i hi).trans_lt (hvN i hi),
        fun i hi => (hd i hi).trans_lt (hvD i hi), ?_, ?_⟩
      · simpa only [Num.fixVal, Num.intVal_congr (fun i hi => (hd i hi).symm)] using hpos
      · rw [hw]
        simpa only [Num.fixVal, Num.intVal_congr (fun i hi => (hn i hi).symm),
          Num.intVal_congr (fun i hi => (hd i hi).symm)] using hq
    · refine ⟨hvN, hvD, ?_, ?_⟩
      · simp only [Num.fixVal, hD, Int.cast_one]
        positivity
      · rw [hw]
        simp only [Num.fixVal, hN, hD, Int.cast_one]
        have : (0 : ℝ) < 2 ^ P := by positivity
        field_simp
  · intro e he
    rw [ha0, ha1]
    rcases hE e he with ⟨heE, -, hn', hd', hk⟩ | ⟨⟨-, -, hN, hD⟩, -, hn', hd'⟩
    · obtain ⟨hN, hD⟩ := hpairs e heE
      rw [hn', hd', ← hN, ← hD]
      exact ⟨Num.intVal_congr fun i hi => (hk i hi).1,
        Num.intVal_congr fun i hi => (hk i hi).2⟩
    · rw [hn', hd']
      exact ⟨hN, hD⟩

end MinCostFlow.SparseCore.Program.Read
