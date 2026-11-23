module

public import MinCostFlow.HierPaths.InitProgFlatCopy
public import MinCostFlow.HierPaths.InitProgFlatRead

/-!
# Substituting one edge of a child host

The host edge tells which way to read its embedding. The two offsets of the embedding
give its address and length without scanning the other rows of the table.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- The embedding of one edge in the direction used by `substWalk`. -/
def initFlatEdgeWords (G : Graph) (emb : ℕ → List ℕ) (e u : ℕ) : List ℕ :=
  if (edgeAt G.edges e).1 = u then emb e else (emb e).reverse

/-- Arguments are host address, embedding table address, host edge count, edge number,
current terminal, and output address. -/
def initFlatEdge (seek copy : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.bin .add (.reg 0) (.const 2))
    (.bin .mul (.const 2) (.reg 3)))) ;;
  .call 7 seek [.reg 1, .reg 2, .reg 3] ;;
  .call 8 seek [.reg 1, .reg 2, .bin .add (.reg 3) (.const 1)] ;;
  .call 9 copy [.reg 5, .reg 7, .bin .sub (.reg 8) (.reg 7), .reg 4, .reg 6] ;;
  .ret (.reg 9)

theorem initFlatEdge_noRand (seek copy : ℕ) : (initFlatEdge seek copy).NoRand := by
  simp [initFlatEdge, Stmt.NoRand]

/-- Append the directed embedding of one edge and preserve the source data. -/
def initFlatEdgeContract (w : ℕ) (G : Graph) (emb : ℕ → List ℕ) (e u : ℕ) : Contract where
  pre args mem := ∃ gAddr eAddr dst, args = [gAddr, eAddr, G.m, e, u, dst] ∧
    e < G.m ∧ (edgeAt G.edges e).1 < 2 ^ w ∧ GraphAt mem gAddr G ∧
    ListAt mem eAddr (csrList G.m emb) ∧ gAddr + G.encode.length ≤ dst ∧
    eAddr + (csrList G.m emb).length ≤ dst ∧ dst + (emb e).length < 2 ^ w
  post args mem v mem' := ∃ gAddr eAddr dst, args = [gAddr, eAddr, G.m, e, u, dst] ∧
    v = dst + (emb e).length ∧ ListAt mem' dst (initFlatEdgeWords G emb e u) ∧
    ∀ y, y < dst ∨ v ≤ y → mem' y = mem y
  cost _ _ := 30 * (emb e).length + 130

theorem initFlatEdge_meetsContract {w f seek copy forward backward e u : ℕ}
    {G : Graph} {emb : ℕ → List ℕ} {p : Program}
    (hp : p.procs[f]? = some (initFlatEdge seek copy))
    (hS : p.procs[seek]? = some initCSRSeek)
    (hC : p.procs[copy]? = some (initFlatCopy forward backward))
    (hF : p.procs[forward]? = some copyUp) (hR : p.procs[backward]? = some revCopyBody) :
    MeetsContract w p f (initFlatEdgeContract w G emb e u) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨gAddr, eAddr, dst, rfl, he, hfirst, hG, hEmb, hg, hs, hroom⟩ := hpre
  let a := initCSRAddr eAddr G.m emb e
  let b := initCSRAddr eAddr G.m emb (e + 1)
  let v₀ := (edgeAt G.edges e).1
  have hlen : G.encode.length = 2 + 2 * G.m := by simp [Graph.encode, Graph.m]; omega
  have hcell : gAddr + 2 + 2 * e < 2 ^ w := by omega
  have htwo : 2 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hread : mem (gAddr + 2 + 2 * e) = v₀ := by
    have h := graphAt_edge_fst hG he
    dsimp only [v₀, edgeAt]
    rw [List.getD_eq_getElem _ _ he]
    exact h
  have hab : b = a + (emb e).length := initCSRAddr_succ eAddr G.m emb e
  have hbd : b ≤ dst := (initCSRAddr_le_end he).trans hs
  have haw : a < 2 ^ w := by omega
  have hbw : b < 2 ^ w := by omega
  have hEmbw : eAddr + (csrList G.m emb).length < 2 ^ w := by omega
  have hew : e + 1 < 2 ^ w := lt_of_le_of_lt he (hw _ (by simp))
  have hrow : ListAt mem a (emb e) := initCSRAddr_listAt hEmb he
  refine runs_start_le ?_
  unfold initFlatEdge
  refine runs_seq_assign_le (v := v₀) (Expr.eval_load_of_eq
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := gAddr) rfl)
      (Expr.eval_const htwo) (by omega))
      (Expr.eval_mul (Expr.eval_const htwo) (Expr.eval_reg_of_eq (v := e) rfl) (by omega))
      hcell) hread) ?_
  refine runs_seq_call_le (initCSRSeek_meetsContract (w := w) (k := G.m) (f := emb) hS)
    (vs := [eAddr, G.m, e]) rfl ?_ ⟨eAddr, e, rfl, he.le, hEmb, hEmbw⟩ ?_
  · intro v hv
    exact hw _ (by simp at hv ⊢; tauto)
  intro r₁ mem₁ pos₁ hp₁
  change r₁ = a ∧ mem₁ = mem at hp₁
  obtain ⟨hr₁, hm₁⟩ := hp₁
  subst r₁ mem₁
  refine runs_seq_call_le (initCSRSeek_meetsContract (w := w) (k := G.m) (f := emb) hS)
    (vs := [eAddr, G.m, e + 1]) (by simp [evalArgs, Expr.eval, startState, BinOp.eval, h1, hew])
    ?_ ⟨eAddr, e + 1, rfl, he, hEmb, hEmbw⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hw _ (by simp)
    · exact hew
  intro r₂ mem₂ pos₂ hp₂
  change r₂ = b ∧ mem₂ = mem at hp₂
  obtain ⟨hr₂, hm₂⟩ := hp₂
  subst r₂ mem₂
  have hlenEq : b - a = (emb e).length := by omega
  have hlenw : (emb e).length < 2 ^ w := by omega
  refine runs_seq_call_le (initFlatCopy_meetsContract (w := w) (xs := emb e) hC hF hR)
    (vs := [dst, a, (emb e).length, u, v₀])
    (by simp [evalArgs, Expr.eval, startState, BinOp.eval, hlenEq, hlenw]) ?_
    ⟨dst, a, u, v₀, rfl, hrow, hab ▸ hbd, hroom, h1⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact haw
    · exact hlenw
    · exact hw _ (by simp)
    · exact hfirst
  intro r mem' pos' hp'
  obtain ⟨dst', src', u', first', ha, hv, hwds, hfr⟩ := hp'
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨hd, _, _, hu, hf'⟩ := ha
  subst dst' u' first'
  have hwds' : ListAt mem' dst (initFlatEdgeWords G emb e u) := by
    simpa [initFlatEdgeWords, v₀, eq_comm] using hwds
  refine runs_ret_le (v := r) (by simp [Expr.eval])
    ⟨gAddr, eAddr, dst, rfl, hv, hwds', fun y hy => hfr y (by rwa [hv] at hy)⟩ ?_
  simp [initCSRSeekContract, initFlatCopyContract, initFlatEdgeContract, Expr.size, argsSize]
  omega

end MinCostFlow.HierPaths

end
