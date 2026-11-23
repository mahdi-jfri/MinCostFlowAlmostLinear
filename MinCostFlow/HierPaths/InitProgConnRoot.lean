module

public import MinCostFlow.HierPaths.InitProgConnProject
public import MinCostFlow.HierPaths.InitOwner

/-!
# Root projection data in the static output

The projection call reads the root graph, the label section and the owner
array directly from the static block. The bound on the block leaves all
three arrays below the connector outputs.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- The static output gives the graph and arrays required by the projection procedure. -/
theorem staticOut_initRootAt {w a d M h dst : ℕ} {S : StaticData} {G : Graph}
    {mem : ℕ → ℕ} (hS : StaticOut mem h S) (hgood : S.Good a d M G)
    (hsep : h + S.encode.length ≤ dst) (hn : G.n < 2 ^ w) (hm : G.m < 2 ^ w) :
    InitRootAt w S G mem
      (initCSRAddr (h + 7 + mem (h + 3)) ((leafDepth S.x S.b + 1) * S.numTerm)
        (initHostRow S) 0) (h + 7 + mem (h + 2)) (h + 10) dst := by
  let J := S.H.host 0 0
  let L := h + 7 + mem (h + 2)
  let H := initCSRAddr (h + 7 + mem (h + 3)) ((leafDepth S.x S.b + 1) * S.numTerm)
    (initHostRow S) 0
  have hP : 0 < S.numTerm := Nat.two_pow_pos S.x
  have hR : 0 < (leafDepth S.x S.b + 1) * S.numTerm :=
    Nat.mul_pos (Nat.succ_pos _) hP
  have hH : GraphAt mem H J := by
    simpa only [Nat.zero_mul, Nat.zero_add] using staticOut_hostAt hS (Nat.zero_le _) hP
  have hHost : H + J.encode.length ≤ dst := by
    have hx := initHostRow_eq S 0 0 hP
    simp only [Nat.zero_mul, Nat.zero_add] at hx
    have hh := staticOut_row_end_le hS (i := 3) (by decide) (staticHostSection S) hR
    rw [hx] at hh
    exact hh.trans hsep
  have hlabels : ListAt mem L (tabList J.m fun e => labelWord (S.label e)) := hS.section (by decide)
  have hL : L + J.m ≤ dst := by
    have hh := (hS.section_end_le (i := 2) (by decide)).trans hsep
    change L + (tabList J.m fun e => labelWord (S.label e)).length ≤ dst at hh
    simpa using hh
  obtain ⟨_, hown, henc⟩ := staticOut_owner_facts hS
  refine ⟨hH, hHost, hL, ?_, ?_, ?_, hgood.proj, hm⟩
  · change h + 10 + 2 ^ S.x ≤ dst
    omega
  · intro e he
    have hh := hlabels e (by simpa using he)
    simpa [tabList] using hh
  · intro t ht
    have hown' := hown t (by simpa [StaticData.sections] using ht)
    exact ⟨by simpa [StaticData.sections, tabList] using hown', (hgood.owner_lt t ht).trans hn⟩

end MinCostFlow.HierPaths

end
