module

public import MinCostFlow.HierPaths.InitProgConnRows

/-!
# Finding the input of a walk substitution

A flattening step reads one child host and the table of embeddings of its edges.
Both are directly indexed by depth and group in the static output. The row bounds
below keep these reads inside the static block.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

/-- Host rows at all depths, including the leaves. -/
def initHostRow (S : StaticData) (i : ℕ) : List ℕ :=
  (S.H.host (i / S.numTerm) (i % S.numTerm)).encode

/-- An edge embedding table for one nonroot group. -/
def initEmbRow (S : StaticData) (i : ℕ) : List ℕ :=
  csrList (S.H.host (i / S.numTerm + 1) (i % S.numTerm)).m
    (S.H.emb (i / S.numTerm) (i % S.numTerm))

theorem staticHostSection (S : StaticData) :
    S.sections.getD 3 [] =
      csrList ((leafDepth S.x S.b + 1) * S.numTerm) (initHostRow S) := rfl

theorem staticEmbSection (S : StaticData) :
    S.sections.getD 4 [] =
      csrList (leafDepth S.x S.b * S.numTerm) (initEmbRow S) := rfl

private theorem levelSlot_div_mod {P g : ℕ} (j : ℕ) (hg : g < P) :
    (j * P + g) / P = j ∧ (j * P + g) % P = g := by
  have hp : 0 < P := by omega
  constructor
  · rw [Nat.mul_comm j P, Nat.mul_add_div hp, Nat.div_eq_of_lt hg, Nat.add_zero]
  · rw [Nat.mul_comm j P, Nat.mul_add_mod, Nat.mod_eq_of_lt hg]

private theorem levelSlot_lt {P j D g : ℕ} (hj : j < D) (hg : g < P) :
    j * P + g < D * P := by
  calc
    _ < j * P + P := Nat.add_lt_add_left hg _
    _ = (j + 1) * P := (Nat.succ_mul _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hj

/-- Section 3 holds the encoded host of every in-range group. -/
theorem staticOut_hostAt {mem : ℕ → ℕ} {h j g : ℕ} {S : StaticData}
    (hS : StaticOut mem h S) (hj : j ≤ leafDepth S.x S.b) (hg : g < S.numTerm) :
    GraphAt mem
      (initCSRAddr (h + 7 + mem (h + 3)) ((leafDepth S.x S.b + 1) * S.numTerm)
        (initHostRow S) (j * S.numTerm + g)) (S.H.host j g) := by
  have hsec := hS.section (i := 3) (by decide)
  rw [staticHostSection] at hsec
  have hrow := initCSRAddr_listAt hsec (levelSlot_lt (Nat.lt_succ_of_le hj) hg)
  obtain ⟨hd, hm⟩ := levelSlot_div_mod j hg
  simpa [GraphAt, initHostRow, hd, hm] using hrow

/-- Section 4 holds the substitution table of the child at depth `j + 1`. -/
theorem staticOut_embAt {mem : ℕ → ℕ} {h j g : ℕ} {S : StaticData}
    (hS : StaticOut mem h S) (hj : j < leafDepth S.x S.b) (hg : g < S.numTerm) :
    ListAt mem
      (initCSRAddr (h + 7 + mem (h + 4)) (leafDepth S.x S.b * S.numTerm)
        (initEmbRow S) (j * S.numTerm + g))
      (csrList (S.H.host (j + 1) g).m (S.H.emb j g)) := by
  have hsec := hS.section (i := 4) (by decide)
  rw [staticEmbSection] at hsec
  have hrow := initCSRAddr_listAt hsec (levelSlot_lt hj hg)
  obtain ⟨hd, hm⟩ := levelSlot_div_mod j hg
  simpa [initEmbRow, hd, hm] using hrow

/-- Every row of either hierarchy table ends inside the static block. -/
theorem staticOut_row_end_le {mem : ℕ → ℕ} {h i k r : ℕ} {S : StaticData}
    {f : ℕ → List ℕ} (hS : StaticOut mem h S) (hi : i < 6)
    (hsec : S.sections.getD i [] = csrList k f) (hr : r < k) :
    initCSRAddr (h + 7 + mem (h + i)) k f r + (f r).length ≤ h + S.encode.length := by
  rw [← initCSRAddr_succ]
  have h := hS.section_end_le hi
  rw [hsec] at h
  exact (initCSRAddr_le_end hr).trans h

theorem initHostRow_eq (S : StaticData) (j g : ℕ) (hg : g < S.numTerm) :
    initHostRow S (j * S.numTerm + g) = (S.H.host j g).encode := by
  obtain ⟨hd, hm⟩ := levelSlot_div_mod j hg
  simp [initHostRow, hd, hm]

theorem initEmbRow_eq (S : StaticData) (j g : ℕ) (hg : g < S.numTerm) :
    initEmbRow S (j * S.numTerm + g) = csrList (S.H.host (j + 1) g).m (S.H.emb j g) := by
  obtain ⟨hd, hm⟩ := levelSlot_div_mod j hg
  simp [initEmbRow, hd, hm]

end MinCostFlow.HierPaths

end
