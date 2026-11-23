module

public import MinCostFlow.LastLevelProgram.PackEndpoints
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# Building the compact endpoint arrays

The last-level call to Theorem 2.2 (page 7) needs two arrays of compact
vertex indices. The loop reads representative edge names in canonical
order and writes both endpoints, using the slot-to-index lookup table.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM DynSpanner.Program

private def edgeArgs : List Expr :=
  [.reg 0, .reg 1, .reg 2, .load (.bin .add (.reg 3) (.reg 7)),
    .bin .add (.reg 4) (.reg 7), .bin .add (.reg 5) (.reg 7)]

/-- Registers hold the two endpoint-slot bases, slot-to-index base,
edge-name base, two destinations, and edge count. -/
def packEdgeLoop (pack : ℕ) : Stmt :=
  forRange 7 (.const 0) (.reg 6)
    (.call 8 pack [.reg 0, .reg 1, .reg 2, .load (.bin .add (.reg 3) (.reg 7)),
      .bin .add (.reg 4) (.reg 7), .bin .add (.reg 5) (.reg 7)])

/-- Pack all edges from a prepared vertex lookup table and a canonical
representative edge-name array. The source tables are preserved. -/
theorem packEdgeLoop_triple {w pack : ℕ} {p : Program}
    (hp : p.procs[pack]? = some packEndpointsBody)
    (mem : ℕ → ℕ) (pos g vCap eCap index names tails heads : ℕ)
    {G H : MGraph} (hg : DynGraphAt mem g vCap eCap G)
    (hsub : G.IsSubgraph H) (hvalid : H.IsValid)
    (hword : 1 < 2 ^ w) (hn : H.n ≤ 2 ^ w)
    (hgraph : g + dynGraphSize vCap eCap ≤ tails)
    (hindex : index + vCap ≤ tails) (hnames : names + H.m ≤ tails)
    (hsep : tails + H.m ≤ heads) (hroom : heads + H.m < 2 ^ w)
    (hnamesAt : ∀ i < H.m, mem (names + i) = edgeName H i)
    (hindexAt : ∀ v ∈ H.V,
      mem (index + mem (dgExtToIntBase g vCap + v)) = vertexIndex H v) :
    Triple w p
      (fun st => st = startState [dgETailSlotBase g vCap eCap, dgEHeadSlotBase g vCap eCap,
        index, names, tails, heads, H.m] mem pos)
      (packEdgeLoop pack)
      (normalPost fun st =>
        (∀ i < H.m, st.mem (tails + i) = (indexedGraph H).tail i ∧
          st.mem (heads + i) = (indexedGraph H).head i) ∧
        (∀ a, (a < tails ∨ tails + H.m ≤ a) → (a < heads ∨ heads + H.m ≤ a) →
          st.mem a = mem a))
      (fun _ => 70 * H.m + 7) := by
  let tailSlot := dgETailSlotBase g vCap eCap
  let headSlot := dgEHeadSlotBase g vCap eCap
  have hm : H.m < 2 ^ w := by omega
  let Inv := fun i (st : State) =>
    st.regs 0 = tailSlot ∧ st.regs 1 = headSlot ∧ st.regs 2 = index ∧
    st.regs 3 = names ∧ st.regs 4 = tails ∧ st.regs 5 = heads ∧
    st.regs 6 = H.m ∧ st.regs 7 = i ∧
    (∀ j < i, st.mem (tails + j) = (indexedGraph H).tail j ∧
      st.mem (heads + j) = (indexedGraph H).head j) ∧
    (∀ a, (a < tails ∨ tails + H.m ≤ a) → (a < heads ∨ heads + H.m ≤ a) →
      st.mem a = mem a)
  have loop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 6)
    (body := .call 8 pack edgeArgs) (Inv := Inv)
    (P := fun st => st = startState [tailSlot, headSlot, index, names, tails, heads, H.m] mem pos)
    61 0 H.m (Nat.zero_le _) hword (fun _ => hm)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr, ?_⟩
      dsimp [Inv]
      simp [startState])
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.1)
    (fun _ st _ _ h => by
      have hr : st.regs 6 = H.m := h.2.2.2.2.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0, h1, h2, h3, h4, h5, h6, h7, hdone, hframe⟩
      have below (a : ℕ) (ha : a < tails) : st.mem a = mem a :=
        hframe a (Or.inl ha) (Or.inl (by omega))
      have hg' := hg.of_agree fun a _ ha => below a (by omega)
      have ht (v : ℕ) (hv : v ∈ H.V) :
          st.mem (index + st.mem (dgExtToIntBase g vCap + v)) = vertexIndex H v := by
        have hvG := hsub.1 hv
        have hvb := hg.2.1 v hvG
        have hslot := (hg.2.2.2.2.2.2.2.2.2.1 v hvG).1
        have hslotb := hg.2.1 _ hslot
        have ha : dgExtToIntBase g vCap + v < tails := by
          simp only [dgExtToIntBase, dynGraphSize] at *
          omega
        rw [below _ ha, below _ (by omega)]
        exact hindexAt v hv
      obtain ⟨o, after, cost, hrun, ⟨ho, hout⟩, hcost⟩ :=
        packEndpoints_runs p ω st.mem st.pos g vCap eCap index (tails + i) (heads + i)
          hg' hsub hvalid i hi ht (by omega) (by omega) hn (by omega) (by omega)
      subst o
      have hedge : st.mem (names + i) = edgeName H i :=
        (below _ (by omega)).trans (hnamesAt i hi)
      have hargs : evalArgs w st edgeArgs =
          some [tailSlot, headSlot, index, edgeName H i, tails + i, heads + i] := by
        unfold edgeArgs
        simp [evalArgs, Expr.eval, h0, h1, h2, h3, h4, h5, h7, hedge,
          show names + i < 2 ^ w by omega, show tails + i < 2 ^ w by omega,
          show heads + i < 2 ^ w by omega]
      let out := { after with regs := Function.update st.regs 8 0 }
      refine ⟨.normal, out, _, runs_call_iff.mpr ⟨_, _, .returned 0, after, cost,
        hargs, hp, hrun, rfl, rfl, rfl⟩, ?_, ?_⟩
      · refine ⟨⟨h0, h1, h2, h3, h4, h5, h6, by simp [out], ?_, ?_⟩, h7⟩
        · intro j hj
          change after.mem _ = _ ∧ after.mem _ = _
          rw [hout]
          by_cases hji : j = i
          · subst j
            simp [Function.update_of_ne (show tails + i ≠ heads + i by omega)]
          · have hji' : j < i := by omega
            simp only [Function.update_of_ne (show tails + j ≠ tails + i by omega),
              Function.update_of_ne (show heads + j ≠ heads + i by omega),
              Function.update_of_ne (show tails + j ≠ heads + i by omega),
              Function.update_of_ne (show heads + j ≠ tails + i by omega)]
            exact hdone j hji'
        · intro a ha hb
          change after.mem a = _
          rw [hout, Function.update_of_ne (show a ≠ heads + i by omega),
            Function.update_of_ne (show a ≠ tails + i by omega)]
          exact hframe a ha hb
      · simp [edgeArgs, Expr.size]
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o _ h
    cases o with
    | normal => exact h.2.2.2.2.2.2.2.2
    | returned _ => exact h
  · intro _ _
    simp [Expr.size_const, Expr.size_reg, Nat.mul_comm]

/-- Return after packing the compact endpoint arrays. -/
def packEdgeBody (pack : ℕ) : Stmt :=
  .seq (packEdgeLoop pack) (.ret (.const 0))

/-- Pack the representative endpoints into the first two arrays of
the persistent guest prefix. -/
def packEdgeContract (w g vCap eCap : ℕ) (G H : MGraph) : Contract where
  pre args mem := ∃ index names tails heads,
    args = [dgETailSlotBase g vCap eCap,dgEHeadSlotBase g vCap eCap,
      index,names,tails,heads,H.m] ∧ DynGraphAt mem g vCap eCap G ∧
    G.IsSubgraph H ∧ H.IsValid ∧ 1 < 2^w ∧ H.n ≤ 2^w ∧
    g+dynGraphSize vCap eCap ≤ tails ∧ index+vCap ≤ tails ∧ names+H.m ≤ tails ∧
    tails+H.m ≤ heads ∧ heads+H.m < 2^w ∧
    (∀ i < H.m, mem (names+i) = edgeName H i) ∧
    ∀ v ∈ H.V, mem (index+mem (dgExtToIntBase g vCap+v)) = vertexIndex H v
  post args mem ret out := ∃ index names tails heads,
    args = [dgETailSlotBase g vCap eCap,dgEHeadSlotBase g vCap eCap,
      index,names,tails,heads,H.m] ∧ ret = 0 ∧
    (∀ i < H.m, out (tails+i) = (indexedGraph H).tail i ∧
      out (heads+i) = (indexedGraph H).head i) ∧
    ∀ a, (a < tails ∨ tails+H.m ≤ a) → (a < heads ∨ heads+H.m ≤ a) → out a = mem a
  cost _ _ := 70*H.m+10

/-- The linked endpoint pass exposes the arrays needed by guest
format setup and subsequent round staging. -/
theorem packEdge_meetsContract {w entry pack g vCap eCap : ℕ}
    {p : Program} (G H : MGraph)
    (he : p.procs[entry]? = some (packEdgeBody pack))
    (hp : p.procs[pack]? = some packEndpointsBody) :
    MeetsContract w p entry (packEdgeContract w g vCap eCap G H) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨index,names,tails,heads,rfl,hg,hsub,hvalid,hw,hn,hgraph,hindex,hnames,hsep,hroom,
    hnamesAt,hindexAt⟩ := hpre
  apply runs_start_le
  unfold packEdgeBody
  refine runs_seq_triple_le (packEdgeLoop_triple hp mem pos g vCap eCap index names tails heads
    hg hsub hvalid hw hn hgraph hindex hnames hsep hroom hnamesAt hindexAt) rfl ?_
  intro out ⟨hends,hframe⟩
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨index,names,tails,heads,rfl,rfl,hends,hframe⟩ ?_
  change 0+(70*H.m+7)+1+2 ≤ 70*H.m+10
  omega

end MinCostFlow.LastLevelProgram
