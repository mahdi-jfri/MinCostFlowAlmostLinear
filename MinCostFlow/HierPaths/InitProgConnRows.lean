module

public import MinCostFlow.HierPaths.InitProgCSR
public import MinCostFlow.HierPaths.InitPairs

/-!
# Connector rows in the static hierarchy

Initialization visits depths, groups, and pairs of children in the order of `connRecs`.
A pair number gives a direct lookup into static section 5. The next row's offset gives its
length, including for the last pair. Only rows for distinct children of a group are read.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM
open scoped BigOperators

/-- Every static section ends within the encoded block. -/
theorem StaticOut.section_end_le {mem : ℕ → ℕ} {addr i : ℕ} {S : StaticData}
    (hS : StaticOut mem addr S) (hi : i < 6) :
    addr + 7 + mem (addr + i) + (S.sections.getD i []).length ≤ addr + S.encode.length := by
  have hl : S.sections.length = 6 := by simp [StaticData.sections]
  have henc : S.encode = csrList 6 (fun k => S.sections.getD k []) := by
    unfold StaticData.encode layoutList
    rw [hl]
  have ha : ListAt mem addr (csrList 6 fun k => S.sections.getD k []) := henc ▸ hS
  have hoff := csrList_offset ha hi.le
  have hnext := initCSRAddr_le_end (addr := addr) (f := fun k => S.sections.getD k []) hi
  rw [hoff, henc]
  rw [initCSRAddr_succ] at hnext
  exact hnext

/-- The row of connector records at a pair number in static section 5. -/
def staticConnRow (S : StaticData) (k : ℕ) : List ℕ :=
  let (j, c, c') := pairOfIdx S.x S.b k
  let rows := S.H.conn j c c'
  csrList rows.length fun i => connWords (rows.getD i (0, 0, []))

theorem staticConnSection (S : StaticData) :
    S.sections.getD 5 [] = csrList (numPairsOf S.x S.b) (staticConnRow S) := rfl

/-- The pair of two ordered siblings can be located using its pair number. -/
theorem staticConnRow_of_siblings (S : StaticData) {j g c c' : ℕ}
    (hgc : g < numGroups S.x S.b j) (hc : c ∈ childGroups S.x S.b j g)
    (hc' : c' ∈ childGroups S.x S.b j g) (hcc : c < c') :
    staticConnRow S (pairIdxOf S.x S.b j c c') =
      csrList (S.H.conn j c c').length (fun i => connWords ((S.H.conn j c c').getD i (0, 0, []))) := by
  have hsmall := (childGroups_lt_numGroups hgc hc).trans_le (numGroups_le_pow (j + 1))
  rw [staticConnRow, pairOfIdx_pairIdxOf hc hc' hcc hsmall]

/-- Every row visited by initialization is in the static connector table. -/
theorem staticConnRow_index_lt (S : StaticData) {j g c c' : ℕ}
    (hj : j < leafDepth S.x S.b) (hg : g < numGroups S.x S.b j)
    (hc : c ∈ childGroups S.x S.b j g) (hcc : c < c') :
    pairIdxOf S.x S.b j c c' < numPairsOf S.x S.b := by
  have hsmall := (childGroups_lt_numGroups hg hc).trans_le (numGroups_le_pow (j + 1))
  have hp : j * 2 ^ S.x + c + 1 ≤ leafDepth S.x S.b * 2 ^ S.x := by
    calc
      j * 2 ^ S.x + c + 1 ≤ j * 2 ^ S.x + 2 ^ S.x :=
        Nat.add_le_add_left (Nat.succ_le_of_lt hsmall) _
      _ = (j + 1) * 2 ^ S.x := (Nat.succ_mul _ _).symm
      _ ≤ leafDepth S.x S.b * 2 ^ S.x := Nat.mul_le_mul_right _ hj
  unfold pairIdxOf numPairsOf
  rw [min_eq_left hcc.le, max_eq_right hcc.le]
  calc
    _ < (j * 2 ^ S.x + c) * 2 ^ S.b + 2 ^ S.b :=
      Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _
    _ = (j * 2 ^ S.x + c + 1) * 2 ^ S.b := (Nat.succ_mul _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hp

/-- With the static output in memory, the addressed row contains exactly the connector records
for the selected siblings. -/
theorem staticOut_connectorRow {mem : ℕ → ℕ} {addr : ℕ} {S : StaticData}
    (hS : StaticOut mem addr S) {j g c c' : ℕ} (hj : j < leafDepth S.x S.b)
    (hg : g < numGroups S.x S.b j) (hc : c ∈ childGroups S.x S.b j g)
    (hc' : c' ∈ childGroups S.x S.b j g) (hcc : c < c') :
    ListAt mem
      (initCSRAddr (addr + 7 + mem (addr + 5)) (numPairsOf S.x S.b)
        (staticConnRow S) (pairIdxOf S.x S.b j c c'))
      (csrList (S.H.conn j c c').length
        (fun i => connWords ((S.H.conn j c c').getD i (0, 0, [])))) := by
  have hsec := hS.section (i := 5) (by decide)
  rw [staticConnSection] at hsec
  have hrow := initCSRAddr_listAt hsec (staticConnRow_index_lt S hj hg hc hcc)
  rwa [staticConnRow_of_siblings S hg hc hc' hcc] at hrow

/-- The slot of an ordered pair in the static connector table. The two children are passed
in increasing order. -/
def initConnSlot : Expr :=
  .bin .add
    (.bin .shiftLeft (.bin .add (.bin .shiftLeft (.reg 2) (.reg 0)) (.reg 3)) (.reg 1))
    (.bin .mod (.reg 4) (.bin .shiftLeft (.const 1) (.reg 1)))

/-- An ordered pair in a nonempty table can be addressed with two shifts and one remainder. -/
theorem eval_initConnSlot {w x b j c c' : ℕ} {s : State}
    (hr0 : s.regs 0 = x) (hr1 : s.regs 1 = b) (hr2 : s.regs 2 = j) (hr3 : s.regs 3 = c)
    (hr4 : s.regs 4 = c') (hcc : c ≤ c') (hc : c < 2 ^ x) (hc'w : c' < 2 ^ w) (hj : j < leafDepth x b)
    (hslots : numPairsOf x b < 2 ^ w) (h1w : 1 < 2 ^ w) :
    initConnSlot.eval w s = some (pairIdxOf x b j c c') := by
  set P := 2 ^ x
  set B := 2 ^ b
  have hP : 0 < P := Nat.two_pow_pos x
  have hB : 0 < B := Nat.two_pow_pos b
  have hD : 0 < leafDepth x b := Nat.zero_lt_of_lt hj
  have hPB : P * B < 2 ^ w := by
    exact (Nat.mul_le_mul_right B (Nat.le_mul_of_pos_left P hD)).trans_lt hslots
  have hBw : B < 2 ^ w := (Nat.le_mul_of_pos_left B hP).trans_lt hPB
  have hs : (j * P + c) * B + c' % B = pairIdxOf x b j c c' := by
    simp [pairIdxOf, min_eq_left hcc, max_eq_right hcc, P, B]
  have hslot : (j * P + c) * B + c' % B < 2 ^ w := by
    change c < P at hc
    have hstep : j * P + c + 1 ≤ leafDepth x b * P := by
      calc
        j * P + c + 1 ≤ j * P + P := by omega
        _ = (j + 1) * P := (Nat.succ_mul _ _).symm
        _ ≤ leafDepth x b * P := Nat.mul_le_mul_right _ hj
    exact ((Nat.add_lt_add_left (Nat.mod_lt _ hB) _).trans_le (by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right B hstep)).trans hslots
  have hbase : (j * P + c) * B < 2 ^ w := (Nat.le_add_right _ _).trans_lt hslot
  have hpre : j * P + c < 2 ^ w := (Nat.le_mul_of_pos_right _ hB).trans_lt hbase
  have hjP : j * P < 2 ^ w := (Nat.le_add_right _ _).trans_lt hpre
  have hfirst : j <<< x = j * P := Nat.shiftLeft_eq _ _
  have hlast : (1 : ℕ) <<< b = B := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hshift : (j * P + c) <<< b = (j * P + c) * B := Nat.shiftLeft_eq _ _
  exact Expr.eval_eq_of_eq (Expr.eval_add
    (Expr.eval_eq_of_eq (Expr.eval_shiftLeft
      (Expr.eval_add (Expr.eval_eq_of_eq
        (Expr.eval_shiftLeft (Expr.eval_reg_of_eq hr2) (Expr.eval_reg_of_eq hr0) (hfirst ▸ hjP))
        hfirst) (Expr.eval_reg_of_eq hr3) hpre) (Expr.eval_reg_of_eq hr1) (hshift ▸ hbase)) hshift)
    (Expr.eval_mod (Expr.eval_reg_of_eq hr4) (Expr.eval_eq_of_eq
      (Expr.eval_shiftLeft (Expr.eval_const h1w) (Expr.eval_reg_of_eq hr1) (hlast ▸ hBw)) hlast)
      hc'w) hslot) hs

/-- Visiting all pairs of children in all groups, including the pairs skipped by the writer,
takes at most one visit per available pair slot. -/
theorem initConnPairVisits_le (S : StaticData) :
    (∑ j ∈ Finset.range (leafDepth S.x S.b),
      numGroups S.x S.b j * branching S.x S.b j ^ 2) ≤ numPairsOf S.x S.b := by
  unfold numPairsOf
  calc
    _ ≤ ∑ _j ∈ Finset.range (leafDepth S.x S.b), 2 ^ S.x * 2 ^ S.b := by
      apply Finset.sum_le_sum
      intro j _
      have hparent :
          numGroups S.x S.b j * branching S.x S.b j = numGroups S.x S.b (j + 1) := by
        apply Nat.eq_of_mul_eq_mul_right (groupSize_pos (x := S.x) (b := S.b) (j := j + 1))
        rw [Nat.mul_assoc, ← groupSize_eq_mul_branching, numGroups_mul_groupSize,
          numGroups_mul_groupSize]
      rw [pow_two, ← Nat.mul_assoc, hparent]
      exact Nat.mul_le_mul (numGroups_le_pow _) (branching_le_pow _)
    _ = _ := by simp [Nat.mul_assoc]

end MinCostFlow.HierPaths

end
