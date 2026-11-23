module

public import WordRAM.Layout
import WordRAM.Tactic
import Mathlib.Data.List.Perm.Basic

/-!
# Exchanging two stored path destinations

The routing step of Algorithm 2 (page 29) uses endpoint pairs for
tree paths. Once the length comparison finds an improving exchange,
two stores swap the destinations and preserve the sources.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Consecutive source and destination words encode the path list. -/
def PathPairsAt (mem : ℕ → ℕ) (base : ℕ) (paths : List (ℕ × ℕ)) : Prop :=
  ∀ i (hi : i < paths.length), mem (base + 2 * i) = paths[i].1 ∧
    mem (base + 2 * i + 1) = paths[i].2

/-- The two arguments are the addresses of the destination words. -/
def pathSwapWordsBody : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.reg 1)) ;;
  .store (.reg 0) (.reg 3) ;;
  .store (.reg 1) (.reg 2) ;;
  .ret (.const 0)

/-- Exchange the two destination words, with an exact memory frame. -/
def pathSwapWordsContract (w : ℕ) : Contract where
  pre args mem := ∃ a b, args = [a,b] ∧ mem a < 2 ^ w ∧ mem b < 2 ^ w
  post args mem ret mem' := ret = 0 ∧
    mem' = Function.update (Function.update mem (args.getD 0 0) (mem (args.getD 1 0)))
      (args.getD 1 0) (mem (args.getD 0 0))
  cost _ _ := 20

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- The destination exchange takes at most 20 machine steps. -/
theorem pathSwapWords_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.HasAt entry [pathSwapWordsBody]) :
    MeetsContract w p entry (pathSwapWordsContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a,b,rfl,ha,hb⟩ := hpre
  have haw := hwords a (by simp)
  have hbw := hwords b (by simp)
  apply runs_start_le
  unfold pathSwapWordsBody
  refine runs_seq_assign_le (v := mem a) (by eval_expr) ?_
  refine runs_seq_assign_le (v := mem b) (by eval_expr) ?_
  refine runs_seq_store_le (x := a) (v := mem b) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := b) (v := mem a) (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl, rfl⟩ ?_
  change 18 ≤ 20
  decide

/-- Exchanging two odd destination addresses preserves every even source
address of the packed endpoint table. -/
theorem pathSwapWords_source {w base i j k ret : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (pathSwapWordsContract w).post [base + 2 * i + 1, base + 2 * j + 1] mem ret mem') :
    mem' (base + 2 * k) = mem (base + 2 * k) := by
  have hm := hout.2
  change mem' = Function.update
    (Function.update mem (base + 2 * i + 1) (mem (base + 2 * j + 1)))
    (base + 2 * j + 1) (mem (base + 2 * i + 1)) at hm
  rw [hm, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-- The two selected rows acquire each other's destinations.
All other destinations remain unchanged. -/
theorem pathSwapWords_destination {w base i j k ret : ℕ} {mem mem' : ℕ → ℕ}
    (hout : (pathSwapWordsContract w).post [base + 2 * i + 1, base + 2 * j + 1] mem ret mem') :
    mem' (base + 2 * k + 1) =
      if k = j then mem (base + 2 * i + 1)
      else if k = i then mem (base + 2 * j + 1)
      else mem (base + 2 * k + 1) := by
  have hm := hout.2
  change mem' = Function.update
    (Function.update mem (base + 2 * i + 1) (mem (base + 2 * j + 1)))
    (base + 2 * j + 1) (mem (base + 2 * i + 1)) at hm
  rw [hm]
  by_cases hj : k = j
  · subst k
    simp
  · rw [ite_eq_right hj, Function.update_of_ne (by omega)]
    by_cases hi : k = i
    · subst k
      simp
    · rw [ite_eq_right hi, Function.update_of_ne (by omega)]

/-- The two stores realize the indexed destination exchange on the
abstract route, with all other path pairs preserved. -/
theorem pathSwapWords_pairs {w base i j ret : ℕ} {mem mem' : ℕ → ℕ}
    {paths : List (ℕ × ℕ)} (hi : i < paths.length) (hj : j < paths.length)
    (hp : PathPairsAt mem base paths)
    (hout : (pathSwapWordsContract w).post [base + 2 * i + 1, base + 2 * j + 1] mem ret mem') :
    PathPairsAt mem' base ((paths.set i (paths[i].1, paths[j].2)).set j (paths[j].1, paths[i].2)) := by
  intro k hk
  have hk' : k < paths.length := by simpa only [List.length_set] using hk
  have hs := pathSwapWords_source (k := k) hout
  have hd := pathSwapWords_destination (k := k) hout
  by_cases he : k = j
  · subst k
    rw [List.getElem_set_self]
    exact ⟨hs.trans (hp j hj).1, hd.trans (by simpa using (hp i hi).2)⟩
  · rw [List.getElem_set_ne (Ne.symm he)]
    by_cases he' : k = i
    · subst k
      rw [List.getElem_set_self]
      exact ⟨hs.trans (hp i hi).1, hd.trans (by simpa [he] using (hp j hj).2)⟩
    · rw [List.getElem_set_ne (Ne.symm he')]
      exact ⟨hs.trans (hp k hk').1, hd.trans (by simpa [he, he'] using (hp k hk').2)⟩

/-- An exchange of two distinct ordered indices has exactly the
before and after permutations used in the forest swap budget. -/
theorem pathSwapWords_pair_permutations (paths : List (ℕ × ℕ)) {i j : ℕ}
    (hij : i < j) (hj : j < paths.length) :
    let hi : i < paths.length := hij.trans hj
    let rest := (paths.eraseIdx j).eraseIdx i
    paths.Perm (paths[i] :: paths[j] :: rest) ∧
    ((paths.set i (paths[i].1, paths[j].2)).set j (paths[j].1, paths[i].2)).Perm
      ((paths[i].1, paths[j].2) :: (paths[j].1, paths[i].2) :: rest) := by
  dsimp only
  have hi : i < paths.length := hij.trans hj
  have he : i < (paths.eraseIdx j).length := by
    rw [List.length_eraseIdx_of_lt hj]
    omega
  have hbefore := (List.getElem_cons_eraseIdx_perm hj).symm.trans
    ((List.getElem_cons_eraseIdx_perm he).symm.cons paths[j])
  rw [List.getElem_eraseIdx_of_lt he hij] at hbefore
  refine ⟨hbefore.trans (List.Perm.swap ..), ?_⟩
  let x := (paths[i].1, paths[j].2)
  let y := (paths[j].1, paths[i].2)
  have hj' : j < (paths.set i x).length := by simpa using hj
  have hafter := List.set_perm_cons_eraseIdx hj' y
  rw [List.eraseIdx_set_gt hij] at hafter
  exact hafter.trans (((List.set_perm_cons_eraseIdx he x).cons y).trans (List.Perm.swap ..))

end MinCostFlow.MinRatio
