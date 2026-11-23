module

public import MinCostFlow.HierPaths.InitProgProjectPass

/-!
# Writing a projected walk column

The edge column is complete after the scan. For a vertex column with at least
one labelled edge, the procedure also writes the owner of the end terminal.
An empty projected walk writes neither edges nor vertices.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Arguments extend the projection pass arguments with the ending terminal. -/
def initProject (verts : Bool) (pass : ℕ) : Stmt :=
  .call 8 pass [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6] ;;
  if verts then
    .cond (.bin .eq (.reg 8) (.reg 6)) (.ret (.reg 8))
      (.store (.reg 8) (.load (.bin .add (.reg 2) (.reg 7))) ;;
        .ret (.bin .add (.reg 8) (.const 1)))
  else .ret (.reg 8)

theorem initProject_noRand (verts : Bool) (pass : ℕ) : (initProject verts pass).NoRand := by
  cases verts <;> simp [initProject, Stmt.NoRand]

/-- Select the required walk column. -/
def initProjectedColumn (S : StaticData) (verts : Bool) (u : ℕ) (es : List ℕ) : List ℕ :=
  let P := projectWalk (S.H.host 0 0).edges S.owner S.label u es
  if verts then P.verts else P.edges

/-- Both columns agree with the projection model. -/
def initProjectContract (w : ℕ) (S : StaticData) (G : Graph) (verts : Bool) (u v : ℕ)
    (es : List ℕ) : Contract where
  pre args mem := ∃ g L O src dst, args = [g, L, O, src, es.length, u, dst, v] ∧
    (initProjectPassContract w S verts u es).pre [g, L, O, src, es.length, u, dst] mem ∧
    IsProjection G (S.H.host 0 0).edges S.owner S.label ∧
    IsEdgeWalk (S.H.host 0 0).edges u v es ∧ v < S.numTerm ∧
    dst + (initProjectedColumn S verts u es).length < 2 ^ w
  post args mem r mem' := ∃ g L O src dst, args = [g, L, O, src, es.length, u, dst, v] ∧
    r = dst + (initProjectedColumn S verts u es).length ∧
    ListAt mem' dst (initProjectedColumn S verts u es) ∧
    ∀ y, y < dst ∨ r ≤ y → mem' y = mem y
  cost _ _ := 100 * es.length + 65

theorem initProject_meetsContract {w f pass u v : ℕ} {S : StaticData} {G : Graph} {verts : Bool}
    {es : List ℕ} {p : Program} (hp : p.procs[f]? = some (initProject verts pass))
    (hpass : MeetsContract w p pass (initProjectPassContract w S verts u es)) :
    MeetsContract w p f (initProjectContract w S G verts u v es) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨g, L, O, src, dst, rfl, hPass, hproj, hW, hv, hroom⟩ := hpre
  have hPass' := hPass
  obtain ⟨g', L', O', src', dst', ha, _, _, _, _, _, hO, _, hOwn, _, _, h1, _⟩ := hPass'
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, ho, _, _, _, hd⟩ := ha
  subst O' dst'
  refine runs_start_le ?_
  unfold initProject
  refine runs_seq_call_le hpass (vs := [g, L, O, src, es.length, u, dst]) rfl ?_ hPass ?_
  · intro q hq
    exact hw q (by simp at hq ⊢; tauto)
  intro r mem₁ pos₁ hp₁
  obtain ⟨g', L', O', src', dst', ha, hr, hwr, hf⟩ := hp₁
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, _, hd⟩ := ha
  subst dst'
  cases verts
  · have he : initProjectedColumn S false u es = initProjectWords S false u es := by
      simp only [initProjectedColumn, Bool.false_eq_true, ↓reduceIte, edges_projectWalk,
        initProjectWords_edges]
    refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
      ⟨g, L, O, src, dst, rfl, he.symm ▸ hr, he.symm ▸ hwr, hf⟩ ?_
    simp [initProjectPassContract, initProjectContract, argsSize, Expr.size]
    omega
  · let words := initProjectWords S true u es
    have he : initProjectedColumn S true u es =
        if words.isEmpty then [] else words ++ [S.owner v] := initProjectWords_verts hproj hW
    change r = dst + words.length at hr
    have heq : r = dst ↔ words = [] := by
      simp [hr]
    refine runs_cond_le (v := if r = dst then 1 else 0)
      (Expr.eval_eq_op (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) h1) ?_ ?_
    · intro hn
      have hr' : r = dst := by by_contra h; simp [h] at hn
      have hnil := heq.mp hr'
      have hcol : initProjectedColumn S true u es = [] := by simp [he, hnil]
      refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
        ⟨g, L, O, src, dst, rfl, by simpa [hcol, Outcome.value] using hr', by simp [hcol, ListAt], hf⟩ ?_
      simp [initProjectPassContract, initProjectContract, argsSize, Expr.size]
      omega
    · intro hz
      have hr' : r ≠ dst := by intro h; simp [h] at hz
      have hnil : words ≠ [] := fun h => hr' (heq.mpr h)
      have hcol : initProjectedColumn S true u es = words ++ [S.owner v] := by simp [he, hnil]
      have hOdst : O + v < dst := by omega
      have hOw : O + v < 2 ^ w := by omega
      have hmem : mem₁ (O + v) = S.owner v := (hf _ (.inl hOdst)).trans (hOwn v hv).1
      have hrw : r + 1 < 2 ^ w := by
        rw [hcol, List.length_append, List.length_singleton] at hroom
        change r = dst + words.length at hr
        omega
      refine runs_seq_store_le (x := r) (v := S.owner v) (Expr.eval_reg_of_eq rfl)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq rfl)
          (Expr.eval_reg_of_eq rfl) hOw) hmem) ?_
      refine runs_ret_le (v := r + 1)
        (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) hrw)
        ⟨g, L, O, src, dst, rfl, ?_, ?_, ?_⟩ ?_
      · change r + 1 = _
        rw [hcol, List.length_append, List.length_singleton]
        omega
      · rw [hcol, listAt_append, ← hr]
        refine ⟨listAt_congr (fun k hk => by
          change k < words.length at hk
          exact (Function.update_of_ne (by omega) _ _).symm) hwr,
          listAt_cons.mpr ⟨Function.update_self .., by simp [ListAt]⟩⟩
      · intro y hy
        change y < dst ∨ r + 1 ≤ y at hy
        exact (Function.update_of_ne (by omega) _ _).trans (hf y (by omega))
      · simp [initProjectPassContract, initProjectContract, argsSize, Expr.size]
        omega

end MinCostFlow.HierPaths

end
