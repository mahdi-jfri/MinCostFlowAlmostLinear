module

public import MinCostFlow.HierPaths.InitProgConnRange

/-!
# The connector row interval of one child

Sibling numbers run through an aligned interval whose length divides the branching limit.
Their residues therefore increase without wrapping within that interval. For a fixed first
child, the connectors to later siblings occupy consecutive rows in the static table.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- The number of children divides the power-of-two branching limit. -/
theorem initBranching_dvd {x b j : ℕ} (h : 1 < groupSize x b j) :
    branching x b j ∣ 2 ^ b := by
  rw [branching_eq h]
  by_cases hb : 2 ^ b ≤ groupSize x b j
  · rw [min_eq_left hb]
  · rw [min_eq_right (Nat.le_of_not_ge hb)]
    change 2 ^ (x - min x (j * b)) ∣ 2 ^ b
    apply Nat.pow_dvd_pow
    by_contra hn
    have hlt := Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_of_not_ge hn)
    exact hb hlt.le

/-- The residue of a group start plus a child position is the residue of the start plus
that position. The divisibility aligns group starts with the modulus. -/
theorem initSibling_mod {B br g i : ℕ} (hB : 0 < B) (hb : br ∣ B) (hi : i < br) :
    (g * br + i) % B = (g * br) % B + i := by
  obtain ⟨k, rfl⟩ := hb
  have hk : 0 < k := Nat.pos_of_ne_zero (fun hk => by simp [hk] at hB)
  have hres : (g * br) % (br * k) = (g % k) * br := by
    rw [Nat.mul_comm br k, Nat.mul_mod_mul_right]
  have hmul : (g % k) * br + br ≤ br * k := by
    rw [← Nat.succ_mul, Nat.mul_comm br k]
    exact Nat.mul_le_mul_right br (Nat.mod_lt g hk)
  have hlt : (g * br) % (br * k) + i < br * k := by rw [hres]; omega
  conv_lhs => rw [Nat.add_mod, Nat.mod_eq_of_lt (hi.trans_le (Nat.le_mul_of_pos_right br hk)),
    Nat.mod_eq_of_lt hlt]

/-- The block of slots for a fixed first child starts at its slot base plus the start
residue of its sibling group. -/
def firstChildSlot (x b j g c : ℕ) : ℕ :=
  (j * 2 ^ x + c) * 2 ^ b + (g * branching x b j) % 2 ^ b

theorem pairIdxOf_eq_firstChildSlot_add {x b j g c i : ℕ} (h : 1 < groupSize x b j)
    (hi : i < branching x b j) (hc : c ≤ g * branching x b j + i) :
    pairIdxOf x b j c (g * branching x b j + i) = firstChildSlot x b j g c + i := by
  unfold pairIdxOf firstChildSlot
  rw [min_eq_left hc, max_eq_right hc, initSibling_mod (Nat.two_pow_pos _) (initBranching_dvd h) hi,
    Nat.add_assoc]

/-- The local matching recovered from a slot of the connector table. -/
def staticConnMatching (S : StaticData) (slot : ℕ) : List (ℕ × ℕ × List ℕ) :=
  let p := pairOfIdx S.x S.b slot
  S.H.conn p.1 p.2.1 p.2.2

/-- The words in one matching record. -/
def staticConnRecord (S : StaticData) (slot i : ℕ) : List ℕ :=
  connWords ((staticConnMatching S slot).getD i (0, 0, []))

theorem staticConnRow_eq_records (S : StaticData) (slot : ℕ) :
    staticConnRow S slot =
      csrList (staticConnMatching S slot).length (staticConnRecord S slot) := rfl

/-- The last slot used for a fixed first child, plus one. -/
def firstChildSlotEnd (x b j g c : ℕ) : ℕ :=
  firstChildSlot x b j g c + branching x b j

theorem firstChildSlotEnd_le (S : StaticData) {j g c : ℕ}
    (hj : j < leafDepth S.x S.b) (hg : g < numGroups S.x S.b j)
    (hc : c ∈ childGroups S.x S.b j g) (hsize : 1 < groupSize S.x S.b j) :
    firstChildSlotEnd S.x S.b j g c ≤ numPairsOf S.x S.b := by
  let B := 2 ^ S.b
  let br := branching S.x S.b j
  have hbr : 0 < br := branching_pos
  have hcap : (g * br) % B + br ≤ B := by
    have hs := initSibling_mod (g := g) (i := br - 1) (Nat.two_pow_pos S.b)
      (initBranching_dvd hsize) (by omega)
    have hn := Nat.mod_lt (g * br + (br - 1)) (Nat.two_pow_pos S.b)
    change (g * br + (br - 1)) % B = (g * br) % B + (br - 1) at hs
    change (g * br + (br - 1)) % B < B at hn
    omega
  have hc' := (childGroups_lt_numGroups hg hc).trans_le (numGroups_le_pow (j + 1))
  have hdepth : j * 2 ^ S.x + c + 1 ≤ leafDepth S.x S.b * 2 ^ S.x := by
    calc
      _ ≤ j * 2 ^ S.x + 2 ^ S.x := by omega
      _ = (j + 1) * 2 ^ S.x := (Nat.succ_mul _ _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ hj
  unfold firstChildSlotEnd firstChildSlot numPairsOf
  change (j * 2 ^ S.x + c) * B + (g * br) % B + br ≤ _
  calc
    _ ≤ (j * 2 ^ S.x + c) * B + B := by omega
    _ = (j * 2 ^ S.x + c + 1) * B := (Nat.succ_mul _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right B hdepth

/-- The first slot for a later sibling of the selected first child. An empty suffix has
this slot equal to its end. -/
def firstChildSlotStart (x b j g c : ℕ) : ℕ :=
  firstChildSlot x b j g c + (c - g * branching x b j + 1)

theorem firstChildSlotStart_le_end {x b j g c : ℕ} (hc : c ∈ childGroups x b j g) :
    firstChildSlotStart x b j g c ≤ firstChildSlotEnd x b j g c := by
  rw [childGroups_eq_Ico, Finset.mem_Ico] at hc
  unfold firstChildSlotStart firstChildSlotEnd
  omega

/-- For a fixed first child, the interval contract applies directly to the static table. -/
theorem staticOut_endpointRange_pre {w h dst field j g c : ℕ} {S : StaticData} {mem : ℕ → ℕ}
    (hS : StaticOut mem h S) (hj : j < leafDepth S.x S.b) (hg : g < numGroups S.x S.b j)
    (hc : c ∈ childGroups S.x S.b j g) (hs : 1 < groupSize S.x S.b j)
    (hf : field < 4) (hsep : h + S.encode.length ≤ dst)
    (hword : dst + (endpointRangeWords (fun q => (staticConnMatching S q).length)
      (staticConnRecord S) (firstChildSlotStart S.x S.b j g c)
        (firstChildSlotEnd S.x S.b j g c) field).length < 2 ^ w)
    (h1 : 1 < 2 ^ w) :
    (initEndpointRangeContract w (numPairsOf S.x S.b) (firstChildSlotStart S.x S.b j g c)
      (firstChildSlotEnd S.x S.b j g c) (staticConnRow S)
      (fun q => (staticConnMatching S q).length) (staticConnRecord S)).pre
      [h + 7 + mem (h + 5), numPairsOf S.x S.b, firstChildSlotStart S.x S.b j g c,
        firstChildSlotEnd S.x S.b j g c, dst, field] mem := by
  have haddr := hS.section_end_le (i := 5) (by decide)
  rw [staticConnSection] at haddr
  refine ⟨_, dst, field, rfl, firstChildSlotStart_le_end hc, firstChildSlotEnd_le S hj hg hc hs,
    ?_, ?_, haddr.trans hsep, hword, h1⟩
  · rw [← staticConnSection]
    exact hS.section (by decide)
  · intro i _ _
    refine ⟨staticConnRow_eq_records S i, ?_⟩
    by_cases he : field = 2
    · exact Or.inl he
    right
    by_cases hi : field = 3
    · exact Or.inl hi
    right
    intro k _
    simp [staticConnRecord, connWords]
    omega

private theorem endpoint_tabList_map (l : List (ℕ × ℕ × List ℕ)) (field : ℕ) :
    tabList l.length (fun i => (connWords (l.getD i (0, 0, []))).getD field 0) =
      l.map (fun q => (connWords q).getD field 0) := by
  apply List.ext_getElem (by simp)
  intro i hi _
  have hil : i < l.length := by simpa using hi
  simp [tabList, List.getElem?_eq_getElem hil]

/-- The interval copies exactly the endpoint words for all later siblings, in child order. -/
theorem endpointRangeWords_firstChild (S : StaticData) {j g c field : ℕ}
    (hg : g < numGroups S.x S.b j) (hc : c ∈ childGroups S.x S.b j g)
    (hs : 1 < groupSize S.x S.b j) :
    endpointRangeWords (fun q => (staticConnMatching S q).length) (staticConnRecord S)
      (firstChildSlotStart S.x S.b j g c) (firstChildSlotEnd S.x S.b j g c) field =
      (childList S.x S.b j g).flatMap (initPairEndpointWords S field j c) := by
  let br := branching S.x S.b j
  let L := g * br
  let skip := c - L + 1
  let base := firstChildSlot S.x S.b j g c
  have hcI := hc
  rw [childGroups_eq_Ico, Finset.mem_Ico] at hcI
  change L ≤ c ∧ c < L + br at hcI
  have hskip : skip ≤ br := by dsimp [skip]; omega
  have hcut : L + skip = c + 1 := by dsimp [skip]; omega
  have hsplit : childList S.x S.b j g =
      List.range' L skip ++ List.range' (L + skip) (br - skip) := by
    rw [List.range'_append_1, Nat.add_sub_cancel' hskip]
    rfl
  have hempty : (List.range' L skip).flatMap (initPairEndpointWords S field j c) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro y hy
    rw [List.mem_range'_1] at hy
    have : ¬ c < y := by omega
    simp [initPairEndpointWords, this]
  rw [hsplit, List.flatMap_append, hempty, List.nil_append]
  unfold endpointRangeWords
  change (List.range' (base + skip) (base + br - (base + skip))).flatMap _ = _
  rw [Nat.add_sub_add_left, ← List.map_add_range' skip (br - skip) 1,
    ← List.map_add_range' skip (br - skip) 1, List.flatMap_map, List.flatMap_map]
  apply List.flatMap_congr
  intro i hi
  rw [List.mem_range'_1] at hi
  have hlt : i < br := by omega
  have hci : c < L + i := by omega
  have hchild : L + i ∈ childGroups S.x S.b j g := by
    rw [childGroups_eq_Ico, Finset.mem_Ico]
    change L ≤ L + i ∧ L + i < L + br
    omega
  have hslot : pairIdxOf S.x S.b j c (L + i) = base + i :=
    pairIdxOf_eq_firstChildSlot_add hs hlt hci.le
  have hsmall := (childGroups_lt_numGroups hg hc).trans_le (numGroups_le_pow (j + 1))
  have hpair := pairOfIdx_pairIdxOf hc hchild hci hsmall
  rw [hslot] at hpair
  simp only [initConnectorColumn, initPairEndpointWords, ite_eq_left hci,
    staticConnMatching, hpair, hslot]
  split
  · rfl
  · by_cases h3 : field = 3
    · subst field
      have hval : initEndpointValue 3 (staticConnRecord S (base + i)) = id := by
        funext n
        simp [initEndpointValue]
      simp [hval, tabList]
    · have hval : initEndpointValue field (staticConnRecord S (base + i)) =
          fun n => (connWords ((S.H.conn j c (L + i)).getD n (0, 0, []))).getD field 0 := by
        funext n
        simp [initEndpointValue, h3, staticConnRecord, staticConnMatching, hpair]
      rw [hval]
      simpa [h3] using endpoint_tabList_map (S.H.conn j c (L + i)) field

/-- The RAM obtains the interval from the diagonal slot and the first child's position. -/
theorem firstChildSlot_bounds_of_diag {x b j g c : ℕ} (hs : 1 < groupSize x b j)
    (hc : c ∈ childGroups x b j g) :
    firstChildSlotStart x b j g c = pairIdxOf x b j c c + 1 ∧
    firstChildSlotEnd x b j g c = pairIdxOf x b j c c +
      (branching x b j - c % branching x b j) := by
  have hb : 0 < branching x b j := branching_pos
  have hparent : c / branching x b j = g := mem_childGroups_iff.mp hc
  have hcmod := Nat.mod_lt c hb
  have hdecomp := Nat.div_add_mod' c (branching x b j)
  rw [hparent] at hdecomp
  have hc' : g * branching x b j + c % branching x b j = c := by
    simpa [Nat.mul_comm] using hdecomp
  have hdiag := pairIdxOf_eq_firstChildSlot_add hs hcmod hc'.ge
  rw [hc'] at hdiag
  unfold firstChildSlotStart firstChildSlotEnd
  constructor <;> omega

end MinCostFlow.HierPaths

end
