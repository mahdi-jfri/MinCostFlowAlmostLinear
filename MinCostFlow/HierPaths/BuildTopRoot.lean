module

public import MinCostFlow.HierPaths.BuildTopPad
public import MinCostFlow.HierPaths.BuildProgCopy
public import MinCostFlow.Spanner.Layouts
import MinCostFlow.HierPaths.InitBuild

/-!
# Padding a port graph in place

The old owner table is followed by a copy of its first few words.
The old graph is followed by the padding edges and receives a new header.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

def buildTopPaddedGraph (J : Graph) (P : ℕ) : Graph :=
  ⟨P, J.edges ++ attEdges J.n (P - J.n) id⟩

/-- Arguments are the graph address, owner-table address, and padded terminal count. -/
def buildTopRootPad (copy pad : ℕ) : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.bin .sub (.reg 2) (.reg 3)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 7 copy [.reg 1, .reg 4, .bin .add (.reg 1) (.reg 3)] ;;
  .call 7 pad [.reg 3, .reg 4,
    .bin .add (.bin .add (.reg 0) (.const 2)) (.bin .add (.reg 5) (.reg 5))] ;;
  .assign 8 (.bin .add (.reg 5) (.reg 4)) ;;
  .assign 6 (.reg 0) ;;
  storeSeq [2, 8] 0 (.ret (.reg 7))

theorem buildTopRootPad_noRand (copy pad : ℕ) : (buildTopRootPad copy pad).NoRand := by
  simp [buildTopRootPad, storeSeq, Stmt.NoRand]

/-- The owner table has room up to the graph address, and the graph has room for its extra edges. -/
def buildTopRootPadContract (w : ℕ) (J : Graph) (owners : List ℕ) : Contract where
  pre args mem := ∃ ga oa P, args = [ga, oa, P] ∧
    GraphAt mem ga J ∧ ListAt mem oa owners ∧ owners.length = J.n ∧
    J.n ≤ P ∧ P - J.n ≤ J.n ∧ oa + P ≤ ga ∧
    ga + (buildTopPaddedGraph J P).encode.length < 2 ^ w
  post args mem r mem' := ∃ ga oa P, args = [ga, oa, P] ∧
    r = ga + (buildTopPaddedGraph J P).encode.length ∧
    GraphAt mem' ga (buildTopPaddedGraph J P) ∧
    ListAt mem' oa (owners ++ owners.take (P - J.n)) ∧
    ∀ y, (y < oa ∨ oa + P ≤ y) ∧ (y < ga ∨ r ≤ y) → mem' y = mem y
  cost args _ := 60 * (args.getD 2 0 - J.n) + 100

private theorem buildTopPaddedGraph_m (J : Graph) (P : ℕ) :
    (buildTopPaddedGraph J P).m = J.m + (P - J.n) := by
  simp [buildTopPaddedGraph, Graph.m, attEdges]

theorem buildTopRootPad_meetsContract {w f copy pad : ℕ} {J : Graph} {owners : List ℕ}
    {p : Program} (hp : p.procs[f]? = some (buildTopRootPad copy pad))
    (hc : p.procs[copy]? = some buildCopyProc) (hd : p.procs[pad]? = some buildTopPadProc) :
    MeetsContract w p f (buildTopRootPadContract w J owners) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨ga, oa, P, rfl, hg, ho, hon, hp, hq, hsep, hroom⟩ := hpre
  let q := P - J.n
  let dst := ga + J.encode.length
  have hlast : ga + (buildTopPaddedGraph J P).encode.length = dst + 2 * q := by
    simp only [graph_encode_length, buildTopPaddedGraph_m, dst, q]; omega
  have hd' : dst + 2 * q < 2 ^ w := hlast ▸ hroom
  have hdst : dst = ga + 2 + (J.m + J.m) := by dsimp [dst]; rw [graph_encode_length]; omega
  have hqP : J.n + q = P := Nat.add_sub_of_le hp
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hm : J.m < 2 ^ w := by omega
  have hn : J.n < 2 ^ w := (Nat.lt_of_le_of_lt hp (hw _ (by simp)))
  have hq' : q < 2 ^ w := hq.trans_lt hn
  have hoa : oa + J.n < 2 ^ w := by omega
  have hP : P < 2 ^ w := hw _ (by simp)
  refine runs_start_le ?_
  unfold buildTopRootPad
  refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := ga) rfl)
    (graphAt_n hg)) ?_
  refine runs_seq_assign_le (v := q) (Expr.eval_sub
    (Expr.eval_reg_of_eq (v := P) rfl) (Expr.eval_reg_of_eq (v := J.n) rfl) hP) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add
    (Expr.eval_reg_of_eq (v := ga) rfl) (Expr.eval_const h1) (by omega)) (graphAt_m hg)) ?_
  refine runs_seq_call_le (buildCopyProc_meetsContract hc) (vs := [oa, q, oa + J.n]) ?_ ?_
    ⟨oa, q, oa + J.n, rfl, by omega, by omega, h1⟩ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, hoa]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hq'
    · exact hoa
  intro _ mem₁ pos₁ hpost
  obtain ⟨a', n', d', he, hcopy, hf₁⟩ := hpost
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨ha', hn', hd₁⟩ := he
  subst a' n' d'
  refine runs_seq_call_le (buildTopPadProc_meetsContract hd) (vs := [J.n, q, dst]) ?_ ?_
    ⟨J.n, q, dst, rfl, by rwa [hqP], hd', h2⟩ ?_
  · have hs : J.m + J.m < 2 ^ w := by omega
    have hg' : ga + 2 < 2 ^ w := by omega
    have hds : ga + 2 + (J.m + J.m) < 2 ^ w := by omega
    simp [evalArgs, Expr.eval, startState, BinOp.eval, h2, hs, hg', hds, hdst]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  intro r mem₂ pos₂ hpost
  obtain ⟨a', n', d', he, hr, hpad, hf₂⟩ := hpost
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨ha', hn', hd₂⟩ := he
  subst a' n' d'
  have hNewM : J.m + q < 2 ^ w := by omega
  refine runs_seq_assign_le (Expr.eval_add (Expr.eval_reg_of_eq (v := J.m) rfl)
    (Expr.eval_reg_of_eq (v := q) rfl) hNewM) ?_
  refine runs_seq_assign_le (Expr.eval_reg_of_eq (v := ga) rfl) ?_
  refine runs_storeSeq [2, 8] 0 _ _ _ rfl (by simpa using (show ga + 2 < 2 ^ w by omega)) ?_
  intro mem₃ hh hf₃
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl) ⟨ga, oa, P, rfl, hr.trans hlast.symm, ?_, ?_, ?_⟩ ?_
  · have hhead : ListAt mem₃ ga [P, J.m + q] := by
      intro i hi
      have h := hh i (by simpa using hi)
      rcases i with _ | _ | i
      · simpa [startState] using h
      · simpa using h
      · simp at hi
    have hedges : ListAt mem (ga + 2) (J.edges.flatMap fun e => [e.1,e.2]) := by
      simpa [GraphAt, Graph.encode, Nat.add_assoc] using (listAt_cons.mp (listAt_cons.mp hg).2).2
    have hs : (J.edges.flatMap fun e => [e.1,e.2]).length = 2 * J.m := by
      have hh := graph_encode_length J
      simp only [Graph.encode, List.length_cons] at hh
      omega
    have he := listAt_of_eq hedges (mem' := mem₃) fun i hi =>
      (hf₃ _ (.inr (by simp))).trans ((hf₂ _ (.inl (by omega))).trans (hf₁ _ (.inr (by omega))))
    have hLast := listAt_of_eq hpad (mem' := mem₃) fun i _ => hf₃ _ (.inr (by simp; omega))
    rw [buildTopPadWords_eq] at hLast
    change GraphAt mem₃ ga (buildTopPaddedGraph J P)
    unfold GraphAt
    simp only [Graph.encode, buildTopPaddedGraph_m]
    change ListAt mem₃ ga ([P, J.m + q] ++
      (J.edges ++ attEdges J.n q id).flatMap (fun e => [e.1,e.2]))
    rw [List.flatMap_append]
    refine listAt_append.mpr ⟨hhead, listAt_append.mpr ⟨he, ?_⟩⟩
    simpa [hs, dst, graph_encode_length, Nat.add_assoc] using hLast
  · refine listAt_append.mpr ⟨listAt_of_eq ho (fun i hi => ?_), ?_⟩
    · change i < owners.length at hi
      exact (hf₃ _ (.inl (by change oa + i < ga; omega))).trans ((hf₂ _ (.inl (by omega))).trans (hf₁ _ (.inl (by omega))))
    · intro i hi
      have hi' : i < q := by simpa [List.length_take, q, Nat.min_eq_left (hq.trans_eq hon.symm)] using hi
      rw [List.getElem_take]
      have ha : oa + owners.length + i = oa + J.n + i := by rw [hon]
      change mem₃ (oa + owners.length + i) = owners[i]
      rw [ha]
      exact (hf₃ _ (.inl (by change oa + J.n + i < ga; omega))).trans ((hf₂ _ (.inl (by omega))).trans
        ((hcopy i hi').trans (ho i (by omega))))
  · intro y hframe
    change (y < oa ∨ oa + P ≤ y) ∧ (y < ga ∨ r ≤ y) at hframe
    obtain ⟨ha, hg⟩ := hframe
    have hj : y < ga ∨ ga + 2 ≤ y := by
      rcases hg with hl | hh
      · exact .inl hl
      · exact .inr (by omega)
    have hk : y < dst ∨ r ≤ y := hg.imp_left (fun hh => by omega)
    have ho' : y < oa + J.n ∨ oa + J.n + q ≤ y := by omega
    exact (hf₃ _ (by simpa using hj)).trans ((hf₂ _ hk).trans (hf₁ _ ho'))
  · simp [buildTopRootPadContract, buildCopyContract, buildTopPadContract, Expr.size, argsSize, q]
    omega

end MinCostFlow.HierPaths

end
