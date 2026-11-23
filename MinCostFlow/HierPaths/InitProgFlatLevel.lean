module

public import MinCostFlow.HierPaths.InitProgFlatSeek
public import MinCostFlow.HierPaths.InitProgFlatPass

/-!
# Substitution at a hierarchy level

A step towards the root looks up the current host and its embedding table.
It uses the host header for the number of edges before calling the sequential
substitution pass.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Arguments are the static address, terminal count, leaf depth, parent
depth, current group, source, input length, start terminal and destination. -/
def initFlatLevel (host emb pass : ℕ) : Stmt :=
  .call 9 host [.reg 0, .reg 1, .bin .add (.reg 2) (.const 1),
    .bin .add (.reg 3) (.const 1), .reg 4] ;;
  .call 10 emb [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
  .call 11 pass [.reg 9, .reg 10, .load (.bin .add (.reg 9) (.const 1)),
    .reg 5, .reg 6, .reg 7, .reg 8] ;;
  .ret (.reg 11)

theorem initFlatLevel_noRand (host emb pass : ℕ) : (initFlatLevel host emb pass).NoRand := by
  simp [initFlatLevel, Stmt.NoRand]

/-- The substitution of a walk of a child host into its parent host. -/
def initLevelWalk (S : StaticData) (j g u : ℕ) (es : List ℕ) : List ℕ :=
  substWalk (S.H.host (j + 1) g).edges (S.H.emb j g) u es

/-- Substitute the supplied walk through the embedding at the given depth and group. -/
def initFlatLevelContract (w : ℕ) (S : StaticData) (j g u : ℕ) (es : List ℕ) : Contract where
  pre args mem := ∃ h src dst, args =
    [h, S.numTerm, leafDepth S.x S.b, j, g, src, es.length, u, dst] ∧
    StaticOut mem h S ∧ ListAt mem src es ∧
    j < leafDepth S.x S.b ∧ g < S.numTerm ∧ h + S.encode.length ≤ dst ∧
    src + es.length ≤ dst ∧ dst + (initLevelWalk S j g u es).length < 2 ^ w ∧
    leafDepth S.x S.b + 1 < 2 ^ w ∧
    ∀ e ∈ es, e < (S.H.host (j + 1) g).m ∧
      (edgeAt (S.H.host (j + 1) g).edges e).1 < 2 ^ w ∧
      (edgeAt (S.H.host (j + 1) g).edges e).2 < 2 ^ w
  post args mem v mem' := ∃ h src dst, args =
    [h, S.numTerm, leafDepth S.x S.b, j, g, src, es.length, u, dst] ∧
    v = dst + (initLevelWalk S j g u es).length ∧
    ListAt mem' dst (initLevelWalk S j g u es) ∧
    ∀ y, y < dst ∨ v ≤ y → mem' y = mem y
  cost _ _ := 30 * (initLevelWalk S j g u es).length + 199 * es.length + 150

theorem initFlatLevel_meetsContract {w f host emb pass j g u : ℕ} {S : StaticData} {es : List ℕ}
    {p : Program} (hp : p.procs[f]? = some (initFlatLevel host emb pass))
    (hhost : MeetsContract w p host
      (initFlatSeekContract w 3 S (leafDepth S.x S.b + 1) (initHostRow S)))
    (hemb : MeetsContract w p emb
      (initFlatSeekContract w 4 S (leafDepth S.x S.b) (initEmbRow S)))
    (hpass : MeetsContract w p pass
      (initFlatPassContract w (S.H.host (j + 1) g) (S.H.emb j g) u es)) :
    MeetsContract w p f (initFlatLevelContract w S j g u es) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨h, src, dst, rfl, hS, hsrc, hj, hg, hsep, hs, hroom, hD, he⟩ := hpre
  let D := leafDepth S.x S.b
  let G := S.H.host (j + 1) g
  let E := S.H.emb j g
  let ga := initCSRAddr (h + 7 + mem (h + 3)) ((D + 1) * S.numTerm)
    (initHostRow S) ((j + 1) * S.numTerm + g)
  let ea := initCSRAddr (h + 7 + mem (h + 4)) (D * S.numTerm) (initEmbRow S)
    (j * S.numTerm + g)
  have hjw : j + 1 < 2 ^ w := (Nat.succ_lt_succ hj).trans hD
  have hSw : h + S.encode.length < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hga : GraphAt mem ga G := staticOut_hostAt hS hj hg
  have hea : ListAt mem ea (csrList G.m E) := staticOut_embAt hS hj hg
  have hidx (t N : ℕ) (ht : t < N) : t * S.numTerm + g < N * S.numTerm := calc
    _ < t * S.numTerm + S.numTerm := Nat.add_lt_add_left hg _
    _ = (t + 1) * S.numTerm := (Nat.succ_mul _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ ht
  have hge : ga + G.encode.length ≤ dst := by
    have hb := staticOut_row_end_le hS (i := 3) (by decide) (staticHostSection S)
      (hidx (j + 1) (D + 1) (Nat.succ_lt_succ hj))
    rw [initHostRow_eq S _ _ hg] at hb
    exact hb.trans hsep
  have hee : ea + (csrList G.m E).length ≤ dst := by
    have hb := staticOut_row_end_le hS (i := 4) (by decide) (staticEmbSection S)
      (hidx j D hj)
    rw [initEmbRow_eq S _ _ hg] at hb
    exact hb.trans hsep
  have hm : ga + 1 < 2 ^ w := by have hl := graph_encode_length G; omega
  have hmw : G.m < 2 ^ w := by have hl := graph_encode_length G; omega
  refine runs_start_le ?_
  unfold initFlatLevel
  refine runs_seq_call_le hhost (vs := [h, S.numTerm, D + 1, j + 1, g]) ?_ ?_
    ⟨h, j + 1, g, rfl, hS, hSw, by decide, Nat.succ_lt_succ hj, hg, staticHostSection S⟩ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, D, h1, hD, hjw]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hw _ (by simp)
    · exact hD
    · exact hjw
    · exact hw _ (by simp)
  intro v mem₁ pos₁ hp₁
  obtain ⟨h', j', g', ha, hv, hm₁⟩ := hp₁
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨hh, _, _, hj', hg'⟩ := ha
  subst h' j' g' mem₁ v
  refine runs_seq_call_le hemb (vs := [h, S.numTerm, D, j, g])
    (by simp [evalArgs, Expr.eval, startState, D]) ?_
    ⟨h, j, g, rfl, hS, hSw, by decide, hj, hg, staticEmbSection S⟩ ?_
  · intro v hv
    exact hw _ (by simp [D] at hv ⊢; tauto)
  intro v mem₂ pos₂ hp₂
  obtain ⟨h', j', g', ha, hv, hm₂⟩ := hp₂
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨hh, _, _, hj', hg'⟩ := ha
  subst h' j' g' mem₂ v
  refine runs_seq_call_le hpass (vs := [ga, ea, G.m, src, es.length, u, dst]) ?_ ?_
    ⟨ga, ea, src, dst, rfl, hga, hea, hsrc, hge, hee, hs, hroom, h1, he⟩ ?_
  · simp [evalArgs, Expr.eval, startState, BinOp.eval, D,
      hm, h1, graphAt_m hga, ga, ea]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · exact hmw
    all_goals exact hw _ (by simp)
  intro r mem₃ pos₃ hp₃
  obtain ⟨_, _, src', dst', ha, hv, hwalk, hf⟩ := hp₃
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, hs', _, _, hd'⟩ := ha
  subst src' dst'
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨h, src, dst, rfl, hv, hwalk, hf⟩ ?_
  rw [initFlatPass_cost]
  simp only [initFlatSeekContract, initFlatLevelContract, argsSize, Expr.size]
  change _ ≤ 30 * (substWalk G.edges E u es).length + 199 * es.length + 150
  dsimp [G, E]
  omega

end MinCostFlow.HierPaths

end
