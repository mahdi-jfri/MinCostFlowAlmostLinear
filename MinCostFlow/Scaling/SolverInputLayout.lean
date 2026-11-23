module

public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.VertexScanProgram
import Mathlib.Tactic.NormNum

/-!
# Reading edge records in the circulation solver layout

The five-word edge records expose tails and heads as two strided endpoint
tables. These lookup lemmas let the machine's vertex scan operate directly
on the solver input, preserving the model's order of all tails followed by
all heads. The same record lookup also identifies capacity and cost cells.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem block_getD {α : Type} (rows : List α) (f : α → List ℕ) (size : ℕ)
    (hsize : ∀ x ∈ rows, (f x).length = size) (i j : ℕ)
    (hi : i < rows.length) (hj : j < size) :
    (rows.flatMap f).getD (size * i + j) 0 = (f (rows[i]'hi)).getD j 0 := by
  induction rows generalizing i with
  | nil => cases hi
  | cons x xs ih =>
    have hx := hsize x (List.mem_cons_self)
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      exact List.getD_append _ _ _ _ (by omega)
    | succ i =>
      have hi' : i < xs.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      simp only [List.flatMap_cons]
      rw [List.getD_append_right _ _ _ _ (by rw [hx, Nat.mul_succ]; omega), hx]
      have he : size * (i + 1) + j - size = size * i + j := by rw [Nat.mul_succ]; omega
      rw [he]
      exact ih (fun a ha => hsize a (List.mem_cons_of_mem x ha)) i hi'

/-- The `j`th word of edge `e` starts at offset `2+5*e+j`. -/
theorem solverWords_edge_getD (J : Circulation) (e : Fin J.m) (j : Fin 5) :
    J.solverWords.getD (2 + 5 * e.val + j.val) 0 = (J.solverEdgeWords e).getD j.val 0 := by
  unfold Circulation.solverWords
  rw [show 2 + 5 * e.val + j.val = (5 * e.val + j.val) + 1 + 1 by omega]
  simp only [List.getD_cons_succ]
  have hh := block_getD (List.finRange J.m) J.solverEdgeWords 5
    (fun _ _ => rfl) e.val j.val (by simpa only [List.length_finRange] using e.isLt) j.isLt
  have he : (List.finRange J.m)[e.val] = e := by
    rw [List.getElem_finRange]
    apply Fin.ext
    rfl
  rw [he] at hh
  exact hh

/-- A solver layout is determined by its two header cells and its five-word
edge records. This form is convenient when writing a transformed graph. -/
theorem solverWords_at_iff (J : Circulation) (mem : ℕ → ℕ) (a : ℕ) :
    ListAt mem a J.solverWords ↔ mem a = J.n ∧ mem (a + 1) = J.m ∧
      ∀ (e : Fin J.m) (j : Fin 5), mem (a + (2 + 5 * e.val + j.val)) =
        (J.solverEdgeWords e).getD j.val 0 := by
  constructor
  · intro hat
    have hn := hat 0 (by simp only [Circulation.solverWords, List.length_cons]; omega)
    have hm := hat 1 (by simp only [Circulation.solverWords, List.length_cons]; omega)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Circulation.solverWords, List.getElem_cons_zero, Nat.add_zero] using hn
    · simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using hm
    · intro e j
      have hi : 2 + 5 * e.val + j.val < J.solverWords.length := by
        rw [J.solverWords_length]
        have he := e.isLt
        have hj := j.isLt
        omega
      have hh := solverWords_edge_getD J e j
      rw [List.getD_eq_getElem _ _ hi] at hh
      exact (hat _ hi).trans hh
  · intro h i hi
    by_cases hz : i = 0
    · subst i
      simpa only [Circulation.solverWords, List.getElem_cons_zero, Nat.add_zero] using h.1
    · by_cases ho : i = 1
      · subst i
        simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using h.2.1
      · have hilen : i < 2 + 5 * J.m := by simpa only [J.solverWords_length] using hi
        have hquot : (i - 2) / 5 < J.m := by omega
        let e : Fin J.m := ⟨(i - 2) / 5, hquot⟩
        let j : Fin 5 := ⟨(i - 2) % 5, Nat.mod_lt _ (by decide)⟩
        have heq : i = 2 + 5 * e.val + j.val := by
          have hh := Nat.mod_add_div (i - 2) 5
          dsimp only [e, j]
          omega
        have hh := h.2.2 e j
        have hg := solverWords_edge_getD J e j
        have hi' : 2 + 5 * e.val + j.val < J.solverWords.length := heq ▸ hi
        rw [List.getD_eq_getElem _ _ hi'] at hg
        have helem : J.solverWords[i]'hi = J.solverWords[2 + 5 * e.val + j.val]'hi' := by
          congr 1
        rw [helem]
        exact (by simpa only [← heq] using hh.trans hg.symm)

/-- Stored tails are the first strided endpoint table. -/
theorem solver_tails_at (J : Circulation) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a J.solverWords) :
    EndpointsAt mem (a + 2) 5 (List.ofFn J.tail) := by
  intro i hi
  have hei : i < J.m := by simpa only [List.length_ofFn] using hi
  have hb : 2 + 5 * i < J.solverWords.length := by rw [J.solverWords_length]; omega
  have hg := solverWords_edge_getD J ⟨i, hei⟩ ⟨0, by decide⟩
  simp only [Nat.add_zero, Circulation.solverEdgeWords, List.getD_cons_zero] at hg
  rw [List.getD_eq_getElem _ _ hb] at hg
  have hh := (hat _ hb).trans hg
  simpa only [Nat.add_assoc, List.getElem_ofFn] using hh

/-- Stored heads are the second strided endpoint table. -/
theorem solver_heads_at (J : Circulation) (mem : ℕ → ℕ) (a : ℕ)
    (hat : ListAt mem a J.solverWords) :
    EndpointsAt mem (a + 3) 5 (List.ofFn J.head) := by
  intro i hi
  have hei : i < J.m := by simpa only [List.length_ofFn] using hi
  have hb : 2 + 5 * i + 1 < J.solverWords.length := by rw [J.solverWords_length]; omega
  have hg := solverWords_edge_getD J ⟨i, hei⟩ ⟨1, by decide⟩
  simp only [Circulation.solverEdgeWords, List.getD_cons_succ, List.getD_cons_zero] at hg
  rw [List.getD_eq_getElem _ _ hb] at hg
  have hh := (hat _ hb).trans hg
  have he : a + (2 + 5 * i + 1) = a + 3 + 5 * i := by omega
  rw [he] at hh
  simpa only [List.getElem_ofFn] using hh

end MinCostFlow.Scaling.Machine
