module

public import MinCostFlow.SparseCore.Program.ReadEmb
public import MinCostFlow.SparseCore.Program.BunRestartLib
public import MinCostFlow.DynSpanner.Program.DynGraphLayout

/-!
# The embedding table at the init: the start table (`AssemblyFirstInitEmb`)

The build of a branch at its init must leave an embedding table (`embRep`) that holds the walk
`tr₀.emb e` of every core edge `e`. At the init, this walk is:
* the edge itself, for an edge of a spanner graph `H` of an active pair (the edges of `S₀`);
* its walk in the spanner of its pair (`piTotal`), for the other edges of the active bundles;
* the empty walk, for the other edges.

The restart of a branch already has a procedure that writes the first two kinds of walks: the
refresh of the table (`embRefreshStmt`, `embRefresh_runs`) gives every edge of the graph of a
listed slot its walk in the spanner of that slot. So the build first writes a start table, in
which every edge of `G` has the empty walk, and then calls the refresh.

This file does the start table. The piece `asmFirstInitEmbTblBody` writes the record of the table
at `h`, leaves the `eCap` words of the table at `h + 2` (they are zero, and only the words of the
edges of `G` are read), and keeps one zero word after them, at `z = h + 2 + eCap`, as the encoding
of the empty walk. Then it points the word of each edge of `G` to `z`. It reads the edges of `G`
from the edge list of the memory form of `G` (`DynGraphAt`), so it costs `O(m)`, not `O(eCap)`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Read
open MinCostFlow.SparseCore.Program.Restart (runs_forRange_const)

/-- **The start table**, `[graph, vCap, eCap, h]`, where `graph` holds the memory form of `G`.
1. write the record `[h + 2, eCap]` at `h`;
2. read `m` and the address of the edge list of `G`, and set `z = h + 2 + eCap`;
3. for each edge `e` of the list, store `z` in the word `h + 2 + e` of the table;
4. return `z + 1`. -/
def asmFirstInitEmbTblBody : Stmt :=
  .store (.reg 3) (.bin .add (.reg 3) (.const 2)) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 2) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 5 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 7) (.reg 1))) (.reg 2)) ;;
  .assign 6 (.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 2)) ;;
  forRange 7 (.const 0) (.reg 4)
    (.store (.bin .add (.bin .add (.reg 3) (.const 2)) (.load (.bin .add (.reg 5) (.reg 7))))
      (.reg 6)) ;;
  .ret (.bin .add (.reg 6) (.const 1))

/-- The piece never reads random bits. -/
theorem asmFirstInitEmbTblBody_noRand : asmFirstInitEmbTblBody.NoRand := by
  simp [asmFirstInitEmbTblBody, forRange, forUp, Stmt.NoRand]

/-- The concrete state of the start table at `h`: every walk is the shared empty walk at
`h + 2 + eCap`. -/
def asmFirstInitEmbConc (E : Finset ℕ) (h eCap : ℕ) : EmbConc :=
  ⟨fun _ => h + 2 + eCap, ⟨fun _ => [], E⟩⟩

/-- **The run of the start table.** Let `graph` hold the memory form of `G` below `h`, with fresh
memory from `h`. Then the piece returns `h + 3 + eCap`, and the table at `h` holds the empty walk
for every edge of `G`. Memory below `h` does not change, the cells of the table lie in
`[h, h + 3 + eCap)`, and the cost is at most `30 m + 50`. -/
theorem asmFirstInitEmbTbl_runs {w graph vCap eCap h pos : ℕ} {p : Program} {ω : ℕ → Bool}
    {G : MGraph} {mem : ℕ → ℕ}
    (hG : DynGraphAt mem graph vCap eCap G) (hgB : graph + dynGraphSize vCap eCap ≤ h)
    (hz : ZeroFrom mem h) (hroom : h + 3 + eCap < 2 ^ w) :
    ∃ o st' c,
      Runs w p ω asmFirstInitEmbTblBody (startState [graph, vCap, eCap, h] mem pos) o st' c ∧
      o.value = h + 3 + eCap ∧
      (embRep eCap).rep h ⟨fun _ => [], G.E⟩ (asmFirstInitEmbConc G.E h eCap) st'.mem ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem a) ∧
      (∀ a, embFoot eCap h (asmFirstInitEmbConc G.E h eCap) a → h ≤ a ∧ a < o.value) ∧
      c ≤ 30 * G.m + 50 := by
  obtain ⟨-, -, hElt, -, -, -, hmM, -, -, -, -, -, ⟨eL, heLen, -, heMem, heLA, -⟩, -⟩ := hG
  have hsz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hm_le : G.m ≤ eCap := by
    calc G.m = G.E.card := rfl
      _ ≤ (Finset.range eCap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr (hElt e he)
      _ = eCap := Finset.card_range _
  set z := h + 2 + eCap with hzdef
  set eLB := graph + 4 + 7 * vCap + eCap with heLB
  set st0 := startState [graph, vCap, eCap, h] mem pos with hst0
  have r0 : st0.regs 0 = graph := rfl
  have r1 : st0.regs 1 = vCap := rfl
  have r2 : st0.regs 2 = eCap := rfl
  have r3 : st0.regs 3 = h := rfl
  -- the record
  set mem1 := Function.update mem h (h + 2) with hmem1
  set st1 : State := { st0 with mem := mem1 } with hst1
  have q1 : Runs w p ω (.store (.reg 3) (.bin .add (.reg 3) (.const 2))) st0 .normal st1 5 :=
    runs_store_iff.mpr ⟨h, h + 2, Expr.eval_reg_of_eq r3,
      Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_const (by omega)) (by omega), rfl, rfl,
      rfl⟩
  set mem2 := Function.update mem1 (h + 1) eCap with hmem2
  set st2 : State := { st0 with mem := mem2 } with hst2
  have q2 : Runs w p ω (.store (.bin .add (.reg 3) (.const 1)) (.reg 2)) st1 .normal st2 5 :=
    runs_store_iff.mpr ⟨h + 1, eCap,
      Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_const (by omega)) (by omega),
      Expr.eval_reg_of_eq r2, rfl, rfl, rfl⟩
  have hmem2_of : ∀ a, a ≠ h → a ≠ h + 1 → mem2 a = mem a := fun a h1 h2 => by
    simp only [hmem2, hmem1, Function.update_apply, h1, h2, ite_false]
  -- the registers
  have hmread : mem2 (graph + 3) = G.m := by
    rw [hmem2_of _ (by omega) (by omega)]
    exact hmM
  set st3 : State := { st2 with regs := Function.update st2.regs 4 G.m } with hst3
  have q3 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const 3)))) st2 .normal st3 5 :=
    runs_assign_iff.mpr ⟨G.m, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_const (by omega)) (by omega)) hmread,
      rfl, rfl, rfl⟩
  have r3_0 : st3.regs 0 = graph := by simp [hst3, hst2, r0]
  have r3_1 : st3.regs 1 = vCap := by simp [hst3, hst2, r1]
  have r3_2 : st3.regs 2 = eCap := by simp [hst3, hst2, r2]
  have r3_3 : st3.regs 3 = h := by simp [hst3, hst2, r3]
  set st4 : State := { st3 with regs := Function.update st3.regs 5 eLB } with hst4
  have q4 : Runs w p ω (.assign 5 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
      (.bin .mul (.const 7) (.reg 1))) (.reg 2))) st3 .normal st4 10 :=
    runs_assign_iff.mpr ⟨eLB, Expr.eval_add (Expr.eval_add
      (Expr.eval_add (Expr.eval_reg_of_eq r3_0) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq r3_1) (by omega))
      (by omega)) (Expr.eval_reg_of_eq r3_2) (by omega), rfl, rfl, rfl⟩
  have r4_2 : st4.regs 2 = eCap := by simp [hst4, r3_2]
  have r4_3 : st4.regs 3 = h := by simp [hst4, r3_3]
  set st5 : State := { st4 with regs := Function.update st4.regs 6 z } with hst5
  have q5 : Runs w p ω (.assign 6 (.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 2))) st4 .normal
      st5 6 :=
    runs_assign_iff.mpr ⟨z, Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq r4_3)
      (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq r4_2) (by omega), rfl, rfl,
      rfl⟩
  -- the loop
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 3 = h ∧ st.regs 4 = G.m ∧ st.regs 5 = eLB ∧ st.regs 6 = z ∧ st.regs 7 = i ∧
    (∀ a, (a < h + 2 ∨ z ≤ a) → st.mem a = mem2 a) ∧
    ∀ j (hj : j < eL.length), j < i → st.mem (h + 2 + eL[j]) = z
  have hInv0 : Inv 0 { st5 with regs := Function.update st5.regs 7 0 } := by
    refine ⟨by simp [hst5, hst4, r3_3], by simp [hst5, hst4, hst3], by simp [hst5, hst4],
      by simp [hst5], by simp, fun a _ => rfl, fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
  have heL_lt : ∀ j (hj : j < eL.length), eL[j] < eCap :=
    fun j hj => hElt _ ((heMem _).mp (List.getElem_mem hj))
  obtain ⟨stL, cL, hrunL, hInvL, hcL⟩ := runs_forRange_const (w := w) (p := p) (ω := ω)
    (r := 7) (hi := .reg 4)
    (body := .store (.bin .add (.bin .add (.reg 3) (.const 2)) (.load (.bin .add (.reg 5) (.reg 7))))
      (.reg 6)) (Inv := Inv) 10 G.m (by omega) (by omega)
    (fun i st _ hI => hI.2.2.2.2.1) (fun i st _ hI => Expr.eval_reg_of_eq hI.2.1)
    (fun i st hi hI => by
      obtain ⟨hr3, hr4, hr5, hr6, hr7, hout, hset⟩ := hI
      have hi' : i < eL.length := by omega
      have hread : st.mem (eLB + i) = eL[i] := by
        rw [hout _ (Or.inl (by omega)), hmem2_of _ (by omega) (by omega)]
        exact heLA i hi'
      have hlt := heL_lt i hi'
      refine ⟨{ st with mem := Function.update st.mem (h + 2 + eL[i]) z }, 10, ?_, ⟨hr7, ?_⟩,
        le_rfl⟩
      · refine runs_store_iff.mpr ⟨h + 2 + eL[i], z, ?_, Expr.eval_reg_of_eq hr6, rfl, rfl, ?_⟩
        · exact Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr3)
            (Expr.eval_const (by omega)) (by omega)) (Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq hr5) (Expr.eval_reg_of_eq hr7) (by omega))
              hread) (by omega)
        · simp [Expr.size]
      · refine ⟨by simpa using hr3, by simpa using hr4, by simpa using hr5, by simpa using hr6,
          by simp, fun a ha => ?_, fun j hj hji => ?_⟩
        · simp only [Function.update_apply]
          split_ifs with heq
          · omega
          · exact hout a ha
        · simp only [Function.update_apply]
          split_ifs with heq
          · rfl
          · have hji' : j < i := by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hji with h1 | h1
              · exact h1
              · subst h1; exact absurd rfl heq
            exact hset j hj hji') hInv0
  obtain ⟨hL3, hL4, hL5, hL6, hL7, hLout, hLset⟩ := hInvL
  have hret : Runs w p ω (.ret (.bin .add (.reg 6) (.const 1))) stL (.returned (z + 1)) stL 4 :=
    runs_ret_iff.mpr ⟨z + 1, Expr.eval_add (Expr.eval_reg_of_eq hL6)
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, by simp [Expr.size]⟩
  have t1 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrunL, hret, rfl⟩)
  have t2 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q5, t1, rfl⟩)
  have t3 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q4, t2, rfl⟩)
  have t4 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q3, t3, rfl⟩)
  have t5 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q2, t4, rfl⟩)
  have t6 := runs_seq_iff.mpr (Or.inr ⟨_, _, _, q1, t5, rfl⟩)
  have hkeep : ∀ a < h, stL.mem a = mem a := fun a ha => by
    rw [hLout a (Or.inl (by omega)), hmem2_of a (by omega) (by omega)]
  refine ⟨_, stL, _, t6, by simp only [Outcome.value]; omega, ⟨rfl, ?_, ?_, ?_⟩, fun a ha => ?_,
    hkeep, fun a ha => ?_, ?_⟩
  · rw [hLout h (Or.inl (by omega))]
    simp [hmem2, hmem1]
  · rw [hLout (h + 1) (Or.inl (by omega))]
    simp [hmem2]
  · intro e he
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((heMem e).mpr he)
    refine ⟨heL_lt j hj, le_rfl, hLset j hj (by omega), ?_⟩
    intro i hi
    simp only [mWalkEncode, List.length_nil, List.flatMap_nil, List.length_cons] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [mWalkEncode, List.length_nil, List.flatMap_nil, List.getElem_cons_zero,
      Nat.add_zero]
    show stL.mem z = 0
    rw [hLout z (Or.inr le_rfl), hmem2_of z (by omega) (by omega)]
    exact hz z (by omega)
  · show stL.mem a = 0
    rw [hLout a (Or.inr (by simp only [Outcome.value] at ha; omega)),
      hmem2_of a (by simp only [Outcome.value] at ha; omega)
        (by simp only [Outcome.value] at ha; omega)]
    exact hz a (by simp only [Outcome.value] at ha; omega)
  · simp only [Outcome.value]
    rcases ha with ha | ⟨e, -, ha1, ha2⟩
    · omega
    · simp only [asmFirstInitEmbConc, Read.walkWords, List.length_nil] at ha1 ha2
      omega
  · simp only [Expr.size_reg] at hcL
    omega

end MinCostFlow.SparseCore.Program
