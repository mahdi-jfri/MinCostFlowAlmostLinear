module

public import WordRAM.Logic
public import MinCostFlow.LastLevelProgram.IndexGraph
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
import WordRAM.Tactic

/-!
# Building the slot-to-index table

The compact vertex array for Theorem 2.2 (page 7) orders live vertices
by name. Given the internal slots in that order, scatter each array
index into its vertex slot. A single pass constructs the inverse table
used to pack edge endpoints.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Arguments are the slot array, the destination table, and the count. -/
def packVertexLoop : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.store (.bin .add (.reg 1) (.load (.bin .add (.reg 0) (.reg 3)))) (.reg 3))

/-- Build the inverse table in linear time. Source slots are distinct,
and the source is disjoint from the entire destination table. -/
theorem packVertexLoop_triple {w : ℕ} (p : Program) (mem : ℕ → ℕ) (pos : ℕ)
    (src dst n cap : ℕ) (slot : ℕ → ℕ)
    (hword : 1 < 2 ^ w) (hs : src + n < 2 ^ w) (hd : dst + cap < 2 ^ w)
    (hsep : src + n ≤ dst ∨ dst + cap ≤ src)
    (hslot : ∀ i < n, slot i < cap ∧ mem (src + i) = slot i)
    (hinj : ∀ i < n, ∀ j < n, slot i = slot j → i = j) :
    Triple w p (fun st => st = startState [src, dst, n] mem pos) packVertexLoop
      (normalPost fun st =>
        (∀ i < n, st.mem (dst + slot i) = i) ∧
        (∀ a, a < dst ∨ dst + cap ≤ a → st.mem a = mem a))
      (fun _ => 17 * n + 7) := by
  have hn : n < 2 ^ w := by omega
  have loop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.reg 1) (.load (.bin .add (.reg 0) (.reg 3)))) (.reg 3))
    (P := fun st => st = startState [src, dst, n] mem pos)
    (Inv := fun i st =>
      st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = n ∧ st.regs 3 = i ∧
      (∀ j < i, st.mem (dst + slot j) = j) ∧
      (∀ a, a < dst ∨ dst + cap ≤ a → st.mem a = mem a))
    8 0 n (Nat.zero_le n) hword (fun _ => hn)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr, ?_, ?_, ?_, ?_, fun _ h => False.elim (Nat.not_lt_zero _ h),
        fun _ _ => rfl⟩ <;> simp [startState])
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ st _ _ h => by
      have hreg : st.regs 2 = n := h.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0, h1, h2, h3, hdone, hframe⟩
      obtain ⟨hcap, hmem⟩ := hslot i hi
      have hread : st.mem (src + i) = slot i := (hframe _ (by omega)).trans hmem
      have hsword : src + i < 2 ^ w := by omega
      have hslotword : slot i < 2 ^ w := by omega
      have hdword : dst + slot i < 2 ^ w := by omega
      refine ⟨.normal, { st with mem := Function.update st.mem (dst + slot i) i },
        8, ?_, ?_, by simp⟩
      · refine runs_store_iff.mpr ⟨dst + slot i, i, ?_, by eval_expr, rfl, rfl, by decide⟩
        eval_expr
      · refine ⟨⟨h0, h1, h2, by simp, ?_, ?_⟩, h3⟩
        · intro j hj
          dsimp only
          by_cases heq : j = i
          · subst j
            exact Function.update_self _ _ _
          · have hne : dst + slot j ≠ dst + slot i :=
              fun h => heq (hinj j (by omega) i hi (Nat.add_left_cancel h))
            rw [Function.update_of_ne hne]
            exact hdone j (by omega)
        · intro a ha
          dsimp only
          rw [Function.update_of_ne (show a ≠ dst + slot i by omega)]
          exact hframe a ha)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | normal => exact h.2.2.2.2
    | returned _ => exact False.elim h
  · intro _ _
    simp [Expr.size_const, Expr.size_reg, Nat.mul_comm]

open DynSpanner.Program in
/-- Specialize the pass to the internal slots of the representative
vertices. The resulting table is the one used by the endpoint pass. -/
theorem packVertexLoop_graph_triple {w : ℕ} (p : Program) (mem : ℕ → ℕ) (pos : ℕ)
    (g src dst vCap eCap : ℕ) {G H : MGraph}
    (hG : DynGraphAt mem g vCap eCap G) (hH : G.IsSubgraph H)
    (hword : 1 < 2 ^ w) (hs : src + H.n < 2 ^ w) (hd : dst + vCap < 2 ^ w)
    (hsep : src + H.n ≤ dst ∨ dst + vCap ≤ src)
    (hsrc : ∀ i < H.n, mem (src + i) = mem (dgExtToIntBase g vCap + vertexName H i)) :
    Triple w p (fun st => st = startState [src, dst, H.n] mem pos) packVertexLoop
      (normalPost fun st =>
        (∀ v ∈ H.V, st.mem (dst + mem (dgExtToIntBase g vCap + v)) = vertexIndex H v) ∧
        (∀ a, a < dst ∨ dst + vCap ≤ a → st.mem a = mem a))
      (fun _ => 17 * H.n + 7) := by
  let slot := fun i => mem (dgExtToIntBase g vCap + vertexName H i)
  obtain ⟨_, hvCap, _, _, _, _, _, _, _, hslot, _⟩ := hG
  have hmem (i : ℕ) (hi : i < H.n) := hslot _ (hH.1 (vertexName_mem hi))
  have hinj (i : ℕ) (hi : i < H.n) (j : ℕ) (hj : j < H.n) (h : slot i = slot j) : i = j := by
    have hnames : vertexName H i = vertexName H j :=
      (hmem i hi).2.symm.trans ((congrArg (fun x => mem (dgIntToExtBase g vCap + x)) h).trans
        (hmem j hj).2)
    rw [← vertexIndex_name hi, ← vertexIndex_name hj, hnames]
  refine (packVertexLoop_triple p mem pos src dst H.n vCap slot hword hs hd hsep
    (fun i hi => ⟨hvCap _ (hmem i hi).1, hsrc i hi⟩) hinj).conseq
    (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st h
  cases o with
  | returned _ => exact h
  | normal =>
    refine ⟨fun v hv => ?_, h.2⟩
    simpa only [slot, vertexName_index hv] using h.1 (vertexIndex H v) (vertexIndex_lt hv)

open DynSpanner.Program

/-- Return after filling the representative vertex slot-to-index table. -/
def packVertexIndexBody : Stmt :=
  .seq packVertexLoop (.ret (.const 0))

/-- The vertex index pass takes the representative slots in sorted
name order and writes the inverse table for endpoint packing. -/
def packVertexIndexContract (w g vCap eCap : ℕ) (G H : MGraph) : Contract where
  pre args mem := ∃ src dst, args = [src,dst,H.n] ∧
    DynGraphAt mem g vCap eCap G ∧ G.IsSubgraph H ∧
    1 < 2^w ∧ src+H.n < 2^w ∧ dst+vCap < 2^w ∧
    (src+H.n ≤ dst ∨ dst+vCap ≤ src) ∧
    ∀ i < H.n, mem (src+i) = mem (dgExtToIntBase g vCap+vertexName H i)
  post args mem ret out := ∃ src dst, args = [src,dst,H.n] ∧ ret = 0 ∧
    (∀ v ∈ H.V, out (dst+mem (dgExtToIntBase g vCap+v)) = vertexIndex H v) ∧
    ∀ a, a < dst ∨ dst+vCap ≤ a → out a = mem a
  cost _ _ := 17*H.n+10

/-- The installed vertex pass provides the lookup used by the
representative endpoint packing call. -/
theorem packVertexIndex_meetsContract {w entry g vCap eCap : ℕ} {p : Program}
    (G H : MGraph) (he : p.procs[entry]? = some packVertexIndexBody) :
    MeetsContract w p entry (packVertexIndexContract w g vCap eCap G H) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨src,dst,rfl,hG,hH,hw,hs,hd,hsep,hsrc⟩ := hpre
  apply runs_start_le
  unfold packVertexIndexBody
  refine runs_seq_triple_le
    (packVertexLoop_graph_triple p mem pos g src dst vCap eCap hG hH hw hs hd hsep hsrc) rfl ?_
  intro out ⟨hindex,hframe⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨src,dst,rfl,rfl,hindex,hframe⟩ ?_
  change 0+(17*H.n+7)+1+2 ≤ 17*H.n+10
  omega

end MinCostFlow.LastLevelProgram
