module

public import MinCostFlow.LastLevelProgram.IndexGraph
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import WordRAM.Contract
import WordRAM.Tactic

/-!
# Packing one edge for the last-level LSST call

The graph stores the ends of each edge as internal vertex slots.
The packing step translates the slots to compact indices and writes
one tail and one head array entry for Theorem 2.2 (page 7).
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM DynSpanner.Program

/-- Arguments are the tail and head slot tables, the slot-to-index
table, the original edge name, and the two destination addresses. -/
def packEndpointsBody : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.reg 3))) ;;
  .assign 7 (.load (.bin .add (.reg 1) (.reg 3))) ;;
  .assign 8 (.load (.bin .add (.reg 2) (.reg 6))) ;;
  .assign 9 (.load (.bin .add (.reg 2) (.reg 7))) ;;
  .store (.reg 4) (.reg 8) ;;
  .store (.reg 5) (.reg 9) ;;
  .ret (.const 0)

/-- The packing step is deterministic. -/
theorem packEndpointsBody_noRand : packEndpointsBody.NoRand := by
  simp [packEndpointsBody, Stmt.NoRand]

/-- Execute one packing step from the named graph layout. The translation
table uses the vertex indices of the graph supplied to the LSST call. -/
theorem packEndpoints_runs {w : ℕ} (p : Program) (ω : ℕ → Bool)
    (mem : ℕ → ℕ) (pos g vCap eCap index tailOut headOut : ℕ)
    {G H : MGraph} (hG : DynGraphAt mem g vCap eCap G) (hH : G.IsSubgraph H)
    (hvalid : H.IsValid) (i : ℕ) (hi : i < H.m)
    (hindex : ∀ v ∈ H.V, mem (index + mem (dgExtToIntBase g vCap + v)) = vertexIndex H v)
    (hgraphRoom : g + dynGraphSize vCap eCap < 2 ^ w)
    (hindexRoom : index + vCap < 2 ^ w)
    (hsize : H.n ≤ 2 ^ w)
    (_htailOut : tailOut < 2 ^ w) (_hheadOut : headOut < 2 ^ w) :
    let e := edgeName H i
    let args := [dgETailSlotBase g vCap eCap, dgEHeadSlotBase g vCap eCap, index, e, tailOut, headOut]
    ∃ o st c, Runs w p ω packEndpointsBody (startState args mem pos) o st c ∧
      (o = .returned 0 ∧
        st.mem = Function.update (Function.update mem tailOut ((indexedGraph H).tail i))
          headOut ((indexedGraph H).head i)) ∧ c ≤ 40 := by
  intro e args
  have he : e ∈ H.E := edgeName_mem hi
  have heG := hH.2.1 he
  have hends := hH.2.2 e he
  obtain ⟨htV, hhV⟩ := hvalid e he
  obtain ⟨_, hvCap, heCap, _, _, _, _, _, _, hslot, _, _, _, hedge, _⟩ := hG
  obtain ⟨ht, hh⟩ := hedge e heG
  rw [← hends.1] at ht
  rw [← hends.2] at hh
  have het := heCap e heG
  have htSlot := (hslot _ (hH.1 htV)).1
  have hhSlot := (hslot _ (hH.1 hhV)).1
  have htb := hvCap _ htSlot
  have hhb := hvCap _ hhSlot
  have hti := (vertexIndex_lt htV).trans_le hsize
  have hhi := (vertexIndex_lt hhV).trans_le hsize
  have htIndex := hindex _ htV
  have hhIndex := hindex _ hhV
  have hwpos : 0 < 2 ^ w := Nat.two_pow_pos _
  simp only [dynGraphSize] at hgraphRoom
  simp only [dgETailSlotBase, dgEHeadSlotBase] at ht hh
  dsimp only [args, dgETailSlotBase, dgEHeadSlotBase]
  apply runs_start_le
  unfold packEndpointsBody
  wram_run
  · simp only [ht, hh, htIndex, hhIndex, indexedGraph]
    exact ⟨True.intro, rfl⟩
  · wram_cost

/-- Set one compact index. Arguments are the external-to-internal table,
the slot-to-index table, the vertex name, and its compact index. -/
def packVertexBody : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.reg 2))) ;;
  .store (.bin .add (.reg 1) (.reg 4)) (.reg 3) ;;
  .ret (.const 0)

/-- Assigning a compact index uses no random bits. -/
theorem packVertexBody_noRand : packVertexBody.NoRand := by
  simp [packVertexBody, Stmt.NoRand]

/-- Write a compact index at the internal slot of a live vertex. -/
theorem packVertex_runs {w : ℕ} (p : Program) (ω : ℕ → Bool)
    (mem : ℕ → ℕ) (pos g vCap eCap index : ℕ)
    {G H : MGraph} (hG : DynGraphAt mem g vCap eCap G) (hsub : G.IsSubgraph H)
    {v : ℕ} (hv : v ∈ H.V)
    (hgraphRoom : g + dynGraphSize vCap eCap < 2 ^ w)
    (hindexRoom : index + vCap < 2 ^ w) (hsize : H.n ≤ 2 ^ w) :
    let source := dgExtToIntBase g vCap
    let args := [source, index, v, vertexIndex H v]
    ∃ o st c, Runs w p ω packVertexBody (startState args mem pos) o st c ∧
      (o = .returned 0 ∧
        st.mem = Function.update mem (index + mem (source + v)) (vertexIndex H v)) ∧
      c ≤ 20 := by
  intro source args
  obtain ⟨_, hvCap, _, _, _, _, _, _, _, hslot, _⟩ := hG
  have hvG := hsub.1 hv
  have hname := hvCap v hvG
  have hbound := hvCap _ (hslot _ hvG).1
  have hvalue := (vertexIndex_lt hv).trans_le hsize
  have hwpos : 0 < 2 ^ w := Nat.two_pow_pos _
  simp only [dynGraphSize] at hgraphRoom
  simp only [dgExtToIntBase] at hbound
  dsimp only [args, source, dgExtToIntBase]
  apply runs_start_le
  unfold packVertexBody
  wram_run
  · exact ⟨rfl, rfl⟩
  · wram_cost

end MinCostFlow.LastLevelProgram
