module

public import MinCostFlow.SparseCore.Program.AssemblyBranchOrdDefs

/-!
# Readout `5` of a branch: the loop (`AssemblyBranchOrdLoop`)

Readout `5` (`asmBrReadOrdStmt`) walks the vertex list `vL` of the output graph. Round `i` reads
vertex `vL[i]`, writes it at the cursor, and lets the tour list its marked ends right after it
(`asmBrOrdBody`). This file proves that the loop writes one record for each vertex of `vL`.

* `AsmBrOrdInv` is the state after `i` rounds: the records of the first `i` vertices lie from
  `h + 2` on, the cursor is right after them, and below `h` only the cells of the tour changed.
* `asmBrOrd_body_runs`: one round keeps the invariant and costs `25` steps plus the listing.
* `asmBrOrd_loop_runs`: the whole loop, by the loop rule with a ghost potential
  (`asmBr_runs_loop_ghost`). The ghost is the concrete state of the tour.

Only `asmBrOrd_loop_runs` and the word lemmas are used later.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.SparseCore.Program.Read

/-! ## Words of records -/

/-- The words of two lists of records add up. -/
theorem ordRecordsWords_append' (a b : List (ℕ × List End)) :
    ordRecordsWords (a ++ b) = ordRecordsWords a + ordRecordsWords b := by
  simp [ordRecordsWords]

/-- Each record has at least two words. -/
theorem two_mul_length_le_ordRecordsWords :
    ∀ recs : List (ℕ × List End), 2 * recs.length ≤ ordRecordsWords recs
  | [] => by simp [ordRecordsWords]
  | r :: rs => by
    have ih := two_mul_length_le_ordRecordsWords rs
    simp only [ordRecordsWords, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- The records of the first `i + 1` vertices are those of the first `i`, then one more. -/
theorem asmBrOrd_take_succ (vL : List ℕ) (out : ℕ → List End) {i : ℕ} (hi : i < vL.length) :
    (vL.take (i + 1)).map (fun v => (v, out v)) =
      (vL.take i).map (fun v => (v, out v)) ++ [(vL[i], out vL[i])] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]

/-- The records of a prefix have at most the words of all records. -/
theorem ordRecordsWords_take_le (vL : List ℕ) (out : ℕ → List End) (i : ℕ) :
    ordRecordsWords ((vL.take i).map fun v => (v, out v)) ≤
      ordRecordsWords (vL.map fun v => (v, out v)) := by
  conv_rhs => rw [← List.take_append_drop i vL]
  rw [List.map_append, ordRecordsWords_append']
  omega

/-! ## The invariant -/

/-- The memory and the registers of readout `5` after `i` rounds, with the tour `T` in concrete
state `tx`. Registers `3` to `6` hold the graph address `g`, the vertex cap `vC`, the number of
vertices and the tour handle `tH`. The records of the first `i` vertices of `vL` are written from
`h + 2`, the cursor (register `7`) is right after them, and register `8` counts the rounds. Below
`h`, only the cells of the tour at the start changed, and the cells of the tour did not grow. -/
def AsmBrOrdInv (T : DSRep OutTourAbs) (h g vC tH : ℕ) (vL : List ℕ) (out : ℕ → List End)
    (s : OutTourAbs) (mem₀ : ℕ → ℕ) (tx₀ : T.τ) (i : ℕ) (tx : T.τ) (st : State) : Prop :=
  i ≤ vL.length ∧ st.regs 3 = g ∧ st.regs 4 = vC ∧ st.regs 5 = vL.length ∧ st.regs 6 = tH ∧
    st.regs 7 = h + 2 + ordRecordsWords ((vL.take i).map fun v => (v, out v)) ∧
    st.regs 8 = i ∧ T.rep tH s tx st.mem ∧ (∀ a, T.foot tH tx a → T.foot tH tx₀ a) ∧
    (∀ a < h, ¬ T.foot tH tx₀ a → st.mem a = mem₀ a) ∧ ZeroFrom st.mem (st.regs 7) ∧
    st.mem h = h + 1 ∧ st.mem (h + 1) = vL.length ∧
    AsmBrRecsAt st.mem (h + 2) ((vL.take i).map fun v => (v, out v))

/-- The facts that every round of readout `5` uses: the vertex list `vL` is in memory at
`g + 4 + vC`, in cells below `h` outside the tour; its vertices are below `vC`; the tour lists
`out v` at each `v`; the tour lies below `h`; and all records fit below `2 ^ w`. -/
structure AsmBrOrdHyp (T : DSRep OutTourAbs) (w h g vC tH : ℕ) (vL : List ℕ)
    (out : ℕ → List End) (s : OutTourAbs) (mem₀ : ℕ → ℕ) (tx₀ : T.τ) : Prop where
  vl : ∀ j (hj : j < vL.length), mem₀ (g + 4 + vC + j) = vL[j]
  vlCell : ∀ j < vL.length, g + 4 + vC + j < h ∧ ¬ T.foot tH tx₀ (g + 4 + vC + j)
  vlt : ∀ v ∈ vL, v < vC
  marked : ∀ v, s.markedList v = out v
  footLt : ∀ a, T.foot tH tx₀ a → a < h
  tourLt : tH < 2 ^ w
  room : h + 2 + ordRecordsWords (vL.map fun v => (v, out v)) < 2 ^ w

/-! ## One round -/

/-- **One round of readout `5`.** From the state after `i < |vL|` rounds, the body writes the
record of `vL[i]` and reaches the state after `i + 1` rounds. It costs `25` steps plus the listing,
which the potential of the tour pays as in `AsmBrTourListAt`. -/
theorem asmBrOrd_body_runs {TR : ℕ → ℕ → DSRep OutTourAbs} {w : ℕ} {p : Program}
    {fList mulT : ℕ} (hL : AsmBrTourListAt TR w p fList mulT) {vC eC h g tH : ℕ}
    (hTl : (TR vC eC).Local) {vL : List ℕ} {out : ℕ → List End} {s : OutTourAbs}
    {mem₀ : ℕ → ℕ} {tx₀ : (TR vC eC).τ} {ω : ℕ → Bool}
    (H : AsmBrOrdHyp (TR vC eC) w h g vC tH vL out s mem₀ tx₀)
    {i : ℕ} {tx : (TR vC eC).τ} {st : State}
    (hinv : AsmBrOrdInv (TR vC eC) h g vC tH vL out s mem₀ tx₀ i tx st) (hi : i < vL.length) :
    ∃ st' c tx', Runs w p ω (asmBrOrdBody fList) st .normal st' c ∧
      AsmBrOrdInv (TR vC eC) h g vC tH vL out s mem₀ tx₀ (i + 1) tx' st' ∧
      c + (TR vC eC).phi tH tx' st'.mem ≤
        25 + mulT * ((out vL[i]).length + 1) * ordStoreLog eC + (TR vC eC).phi tH tx st.mem := by
  obtain ⟨-, h3, h4, h5, h6, h7, h8, hrep, hsub, hfr, hz, hmh, hmh1, hrecs⟩ := hinv
  set W := ordRecordsWords ((vL.take i).map fun u => (u, out u)) with hW
  have hWs : ordRecordsWords ((vL.take (i + 1)).map fun u => (u, out u)) =
      W + (2 + (out vL[i]).length) := by
    rw [asmBrOrd_take_succ vL out hi, ordRecordsWords_append', hW]
    simp [ordRecordsWords]
  have hWle := ordRecordsWords_take_le vL out (i + 1)
  have hroom := H.room
  have hlen2 := two_mul_length_le_ordRecordsWords ((vL.take (i + 1)).map fun u => (u, out u))
  rw [List.length_map, List.length_take, Nat.min_eq_left (by omega)] at hlen2
  have hfootlt : ∀ a, (TR vC eC).foot tH tx a → a < h := fun a ha => H.footLt a (hsub a ha)
  obtain ⟨hvlt, hvnf⟩ := H.vlCell i hi
  have hmv : st.mem (g + 4 + vC + i) = vL[i] := (hfr _ hvlt hvnf).trans (H.vl i hi)
  -- Read the vertex.
  have he1 : asmBrOrdVertexExpr.eval w st = some vL[i] :=
    Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq h3)
      (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq h4) (by omega))
      (Expr.eval_reg_of_eq h8) (by omega)) hmv
  set st₁ : State := { st with regs := Function.update st.regs 9 vL[i] } with hst₁
  have hr1 : Runs w p ω (.assign 9 asmBrOrdVertexExpr) st .normal st₁
      (asmBrOrdVertexExpr.size + 1) := runs_assign_iff.mpr ⟨vL[i], he1, rfl, rfl, rfl⟩
  -- Write it at the cursor.
  have h7₁ : st₁.regs 7 = h + 2 + W := by simp [hst₁, h7]
  have h9₁ : st₁.regs 9 = vL[i] := by simp [hst₁]
  set st₂ : State := { st₁ with mem := Function.update st₁.mem (h + 2 + W) vL[i] } with hst₂
  have hr2 : Runs w p ω (.store (.reg 7) (.reg 9)) st₁ .normal st₂ 3 :=
    runs_store_iff.mpr ⟨h + 2 + W, vL[i], Expr.eval_reg_of_eq h7₁, Expr.eval_reg_of_eq h9₁, rfl,
      rfl, rfl⟩
  have hmem₂ : ∀ a, a ≠ h + 2 + W → st₂.mem a = st.mem a := fun a ha => by
    simp [hst₂, hst₁, ha]
  -- Let the tour list the marked ends.
  have hrep₂ : (TR vC eC).rep tH s tx st₂.mem :=
    (hTl tH s tx st.mem st₂.mem fun a ha => (hmem₂ a (by have := hfootlt a ha; omega)).symm).1
      hrep
  have hphi₂ : (TR vC eC).phi tH tx st₂.mem = (TR vC eC).phi tH tx st.mem :=
    ((hTl tH s tx st.mem st₂.mem fun a ha =>
      (hmem₂ a (by have := hfootlt a ha; omega)).symm).2).symm
  have hz₂ : ZeroFrom st₂.mem (h + 2 + W + 1) := fun a ha => by
    rw [hmem₂ a (by omega)]; exact hz a (by rw [h7]; omega)
  have hvC : vL[i] < vC := H.vlt _ (List.getElem_mem hi)
  obtain ⟨body, hbody, o, st₃, c₁, tx', hrun, hrep', hEL, hval, hZ, hfr', hsub', hcost⟩ :=
    hL.runs vC eC tH vL[i] (h + 2 + W + 1) s tx st₂.mem st₂.pos ω H.tourLt hvC (by omega) hrep₂
      (fun a ha => by have := hfootlt a ha; omega) hz₂ (by rw [H.marked]; omega)
  rw [H.marked] at hEL hval hcost
  have hargs : evalArgs w st₂ [.reg 6, .reg 9, .bin .add (.reg 7) (.const 1)] =
      some [tH, vL[i], h + 2 + W + 1] := by
    have h6₂ : st₂.regs 6 = tH := by simp [hst₂, hst₁, h6]
    have h9₂ : st₂.regs 9 = vL[i] := by simp [hst₂, hst₁]
    have h7₂ : st₂.regs 7 = h + 2 + W := by simp [hst₂, hst₁, h7]
    have e3 : (Expr.bin .add (.reg 7) (.const 1)).eval w st₂ = some (h + 2 + W + 1) :=
      Expr.eval_add (Expr.eval_reg_of_eq h7₂) (Expr.eval_const (by omega)) (by omega)
    simp [evalArgs, Expr.eval_reg_of_eq h6₂, Expr.eval_reg_of_eq h9₂, e3]
  set st₄ : State := { st₃ with regs := Function.update st₂.regs 7 o.value } with hst₄
  have hr3 : Runs w p ω (.call 7 fList [.reg 6, .reg 9, .bin .add (.reg 7) (.const 1)]) st₂
      .normal st₄ (argsSize [.reg 6, .reg 9, .bin .add (.reg 7) (.const 1)] + c₁ + 1) :=
    runs_call_iff.mpr ⟨_, body, o, st₃, c₁, hargs, hbody, hrun, rfl, rfl, rfl⟩
  -- Count the round.
  have h8₄ : st₄.regs 8 = i := by simp [hst₄, hst₂, hst₁, h8]
  set st₅ : State := { st₄ with regs := Function.update st₄.regs 8 (i + 1) } with hst₅
  have hr4 : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.const 1))) st₄ .normal st₅ 4 :=
    runs_assign_iff.mpr ⟨i + 1, Expr.eval_add (Expr.eval_reg_of_eq h8₄)
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  -- Cells below the cursor that are not in the tour keep their values.
  have hkeep : ∀ a, a < h + 2 + W → ¬ (TR vC eC).foot tH tx a → st₃.mem a = st.mem a :=
    fun a ha hn => (hfr' a (by omega) hn).trans (hmem₂ a (by omega))
  have hnot : ∀ a, h ≤ a → ¬ (TR vC eC).foot tH tx a := fun a ha hf => by
    have := hfootlt a hf; omega
  have hsize : asmBrOrdVertexExpr.size = 8 := rfl
  have hargsz : argsSize [.reg 6, .reg 9, .bin .add (.reg 7) (.const 1)] = 5 := rfl
  refine ⟨st₅, (asmBrOrdVertexExpr.size + 1) + (3 + ((argsSize [.reg 6, .reg 9,
      .bin .add (.reg 7) (.const 1)] + c₁ + 1) + 4 + 1) + 1) + 1, tx',
    runs_seq_iff.mpr (Or.inr ⟨st₁, _, _, hr1, runs_seq_iff.mpr (Or.inr ⟨st₂, _, _, hr2,
      runs_seq_iff.mpr (Or.inr ⟨st₄, _, _, hr3, hr4, rfl⟩), rfl⟩), rfl⟩),
    ⟨by omega, by simp [hst₅, hst₄, hst₂, hst₁, h3], by simp [hst₅, hst₄, hst₂, hst₁, h4],
      by simp [hst₅, hst₄, hst₂, hst₁, h5], by simp [hst₅, hst₄, hst₂, hst₁, h6], ?_,
      by simp [hst₅], hrep', fun a ha => hsub a (hsub' a ha), fun a ha hn => ?_, ?_, ?_, ?_,
      ?_⟩, ?_⟩
  · have : st₅.regs 7 = o.value := by simp [hst₅, hst₄]
    rw [this, hval, hWs]; omega
  · rw [show st₅.mem = st₃.mem from rfl, hkeep a (by omega) fun hf => hn (hsub a hf)]
    exact hfr a ha hn
  · have : st₅.regs 7 = o.value := by simp [hst₅, hst₄]
    rw [this]; exact hZ
  · show st₃.mem h = h + 1
    rw [hkeep h (by omega) (hnot h le_rfl)]; exact hmh
  · show st₃.mem (h + 1) = vL.length
    rw [hkeep (h + 1) (by omega) (hnot (h + 1) (by omega))]; exact hmh1
  · show AsmBrRecsAt st₃.mem (h + 2) ((vL.take (i + 1)).map fun v => (v, out v))
    rw [asmBrOrd_take_succ vL out hi]
    refine AsmBrRecsAt.append (AsmBrRecsAt.of_agree hrecs fun c hc1 hc2 => ?_) ?_ ?_
    · exact hkeep c (by omega) (hnot c (by omega))
    · rw [← hW, hfr' (h + 2 + W) (by omega) (hnot _ (by omega))]
      simp [hst₂]
    · rw [← hW]; exact hEL
  · show _ + (TR vC eC).phi tH tx' st₃.mem ≤ _
    rw [hsize, hargsz]
    rw [hphi₂] at hcost
    omega

/-! ## The loop -/

/-- The cost of the round on vertex `v`, with the test of the loop. -/
def asmBrOrdStepCost (mulT eC : ℕ) (out : ℕ → List End) (v : ℕ) : ℕ :=
  29 + mulT * ordStoreLog eC * ((out v).length + 1)

/-- **The loop of readout `5`.** From the state after `0` rounds, the loop ends in the state after
`|vL|` rounds. Its cost plus the final potential of the tour is at most the sum of the round costs,
plus `4`, plus the potential of the tour at the start. -/
theorem asmBrOrd_loop_runs {TR : ℕ → ℕ → DSRep OutTourAbs} {w : ℕ} {p : Program}
    {fList mulT : ℕ} (hL : AsmBrTourListAt TR w p fList mulT) {vC eC h g tH : ℕ}
    (hTl : (TR vC eC).Local) {vL : List ℕ} {out : ℕ → List End} {s : OutTourAbs}
    {mem₀ : ℕ → ℕ} {tx₀ : (TR vC eC).τ} {ω : ℕ → Bool} (hw : 1 < 2 ^ w)
    (H : AsmBrOrdHyp (TR vC eC) w h g vC tH vL out s mem₀ tx₀) {st : State}
    (hinv : AsmBrOrdInv (TR vC eC) h g vC tH vL out s mem₀ tx₀ 0 tx₀ st) :
    ∃ st' c tx', Runs w p ω (.loop asmBrOrdTest (asmBrOrdBody fList)) st .normal st' c ∧
      AsmBrOrdInv (TR vC eC) h g vC tH vL out s mem₀ tx₀ vL.length tx' st' ∧
      c + (TR vC eC).phi tH tx' st'.mem ≤
        (vL.map (asmBrOrdStepCost mulT eC out)).sum + 4 + (TR vC eC).phi tH tx₀ st.mem := by
  have hloop := asmBr_runs_loop_ghost (w := w) (p := p) (ω := ω) (e := asmBrOrdTest)
    (body := asmBrOrdBody fList)
    (Inv := fun tx st => ∃ i, AsmBrOrdInv (TR vC eC) h g vC tH vL out s mem₀ tx₀ i tx st)
    (Q := fun tx st => AsmBrOrdInv (TR vC eC) h g vC tH vL out s mem₀ tx₀ vL.length tx st)
    (m := fun st => vL.length - st.regs 8)
    (rem := fun st => ((vL.drop (st.regs 8)).map (asmBrOrdStepCost mulT eC out)).sum + 4)
    (condVal := fun st => if st.regs 8 < st.regs 5 then 1 else 0)
    (pot := fun tx st => (TR vC eC).phi tH tx st.mem)
    (fun _ st _ => Expr.eval_lt_op (Expr.eval_reg 8 _ _) (Expr.eval_reg 5 _ _) hw)
    (fun tx st ⟨i, hI⟩ hc => by
      have hle := hI.1
      have h5 := hI.2.2.2.1
      have h8 := hI.2.2.2.2.2.2.1
      have hin : i = vL.length := by
        rw [h5, h8] at hc
        split_ifs at hc with hlt
        omega
      subst hin
      exact ⟨hI, by simp [asmBrOrdTest, Expr.size]⟩)
    (fun tx st ⟨i, hI⟩ hc => by
      have hle := hI.1
      have h5 := hI.2.2.2.1
      have h8 := hI.2.2.2.2.2.2.1
      have hi : i < vL.length := by
        rw [h5, h8] at hc
        split_ifs at hc with hlt
        · exact hlt
        · exact absurd rfl hc
      obtain ⟨st', c, tx', hrun, hI', hcost⟩ := asmBrOrd_body_runs hL hTl (ω := ω) H hI hi
      have h8' := hI'.2.2.2.2.2.2.1
      refine ⟨st', c, tx', hrun, ⟨i + 1, hI'⟩, by simp only [h8, h8']; omega, ?_⟩
      simp only [h8, h8', List.drop_eq_getElem_cons hi, List.map_cons, List.sum_cons]
      have hsz : asmBrOrdTest.size = 3 := rfl
      rw [hsz]
      unfold asmBrOrdStepCost
      rw [Nat.mul_right_comm mulT (ordStoreLog eC)]
      omega)
  obtain ⟨st', c, tx', hrun, hQ, hcost⟩ := hloop tx₀ st ⟨0, hinv⟩
  refine ⟨st', c, tx', hrun, hQ, ?_⟩
  have h8 : st.regs 8 = 0 := hinv.2.2.2.2.2.2.1
  simp only [h8, List.drop_zero] at hcost
  exact hcost

/-- The round costs add up to at most `(29 + mulT · log) · words`, where `words` counts the words
of all records. -/
theorem asmBrOrd_sum_le (mulT eC : ℕ) (out : ℕ → List End) :
    ∀ l : List ℕ, (l.map (asmBrOrdStepCost mulT eC out)).sum ≤
      (29 + mulT * ordStoreLog eC) * ordRecordsWords (l.map fun v => (v, out v))
  | [] => by simp [ordRecordsWords]
  | u :: l => by
    have ih := asmBrOrd_sum_le mulT eC out l
    simp only [ordRecordsWords, List.map_cons, List.sum_cons] at ih ⊢
    have hu : asmBrOrdStepCost mulT eC out u ≤
        (29 + mulT * ordStoreLog eC) * (2 + (out u).length) := by
      unfold asmBrOrdStepCost
      nlinarith
    rw [Nat.mul_add]
    omega

end MinCostFlow.SparseCore.Program
