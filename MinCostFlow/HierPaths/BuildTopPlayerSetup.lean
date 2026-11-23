module

public import MinCostFlow.HierPaths.BuildTopPlayerTableLoop
public import MinCostFlow.HierPaths.BuildTopPlayerRank
public import MinCostFlow.HierPaths.BuildTopPlayerScale

/-! # Preparing the runtime player table from the input parameters -/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- Arguments are table address, row count, terminal table, padded exponent,
input edge count, and the two conductance words. -/
def buildTopPlayerSetup (rank scale fill : ℕ) : Stmt :=
  .call 7 rank [.reg 4] ;;
  .call 8 scale [.reg 3, .reg 7] ;;
  .assign 9 (buildTopRootScaleExpr (.reg 5) (.reg 6)) ;;
  .assign 10 (.bin .shiftLeft (.const 1) (.reg 3)) ;;
  .assign 11 (.bin .add (.reg 3) (.const 1)) ;;
  .assign 12 (.bin .add (.bin .mul (.const 49) (.reg 11)) (.const 2)) ;;
  .call 13 fill [.reg 0, .reg 1, .reg 2, .reg 10, .reg 7, .reg 12, .reg 11, .reg 9, .reg 8] ;;
  .ret (.reg 13)

theorem buildTopPlayerSetup_noRand (rank scale fill : ℕ) :
    (buildTopPlayerSetup rank scale fill).NoRand := by
  simp [buildTopPlayerSetup, Stmt.NoRand]

private theorem setupFromScale
    {w f rank scale fill write dst n term x m num den root inner : ℕ} {p : Program}
    (hf : p.procs[f]? = some (buildTopPlayerSetup rank scale fill))
    (hr : p.procs[rank]? = some buildTopPlayerRank)
    (hs : MeetsContract w p scale {
      pre := fun args _ => args = [x,depthOf m] ∧ depthOf m < 2 ^ w ∧ inner < 2 ^ w
      post := fun _ mem v mem' => v = inner ∧ mem' = mem
      cost := fun _ _ => 13 * depthOf m + 100 })
    (he : ∀ s : State, s.regs 5 = num → s.regs 6 = den →
      (buildTopRootScaleExpr (.reg 5) (.reg 6)).eval w s = some root)
    (hl : p.procs[fill]? = some (buildTopPlayerTableLoop write))
    (hw : p.procs[write]? = some buildTopPlayerTableRow) :
    MeetsContract w p f {
      pre := fun args _ => args = [dst,n,term,x,m,num,den] ∧
        8 * m + 8 < 2 ^ w ∧ depthOf m ^ 3 < 2 ^ w ∧
        root < 2 ^ w ∧ inner < 2 ^ w ∧
        2 ^ x < 2 ^ w ∧ 49 * (x + 1) + 2 < 2 ^ w ∧ dst + 7 * n < 2 ^ w
      post := fun _ mem v mem' => v = dst ∧
        (∀ i < n, ListAt mem' (dst + 7 * i)
          (buildTopDepthPlayer term (2 ^ x) (depthOf m) (49 * (x + 1) + 2)
            (x + 1) root inner i).playerWords) ∧
        ∀ y, y < dst ∨ dst + 7 * n ≤ y → mem' y = mem y
      cost := fun _ _ => 13 * (Nat.log 2 (8 * m + 7) + 1) + 32 * depthOf m + 79 * n + 300 } := by
  refine meetsContract_of_runs hf fun args mem pos ω hword hpre => ?_
  obtain ⟨rfl,hm,hcube,hroot,hinner,hM,hdegree,hroom⟩ := hpre
  let r := depthOf m
  let L := x + 1
  have h1 : 1 < 2 ^ w := by omega
  have hrw : r < 2 ^ w := (Nat.le_self_pow (by decide : 3 ≠ 0) _).trans_lt hcube
  have hL : L < 2 ^ w :=
    (Nat.le_mul_of_pos_left L (by decide : 0 < 49)).trans_lt (by omega)
  have hmul : 49 * L < 2 ^ w := (Nat.le_add_right _ 2).trans_lt hdegree
  have h49 : 49 < 2 ^ w := (Nat.le_mul_of_pos_right 49 (Nat.succ_pos x)).trans_lt hmul
  have ht : term < 2 ^ w := hword _ (by simp)
  refine runs_start_le ?_
  unfold buildTopPlayerSetup
  refine runs_seq_call_le (buildTopPlayerRank_meetsContract hr) (vs := [m])
    rfl (by intro v hv; have e := List.mem_singleton.mp hv; subst v; exact hword m (by simp)) ⟨rfl,hm,hcube⟩ ?_
  intro rv mem₁ pos₁ hrv
  have hre : rv = r := hrv.1
  have hm₁ : mem₁ = mem := hrv.2
  subst rv mem₁
  refine runs_seq_call_le hs (vs := [x,r])
    rfl ?_ ⟨rfl,hrw,hinner⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hword _ (by simp)
    · exact hrw
  intro iv mem₂ pos₂ hiv
  have hie : iv = inner := hiv.1
  have hm₂ : mem₂ = mem := hiv.2
  subst iv mem₂
  refine runs_seq_assign_le (v := root)
    (he _ rfl rfl) ?_
  refine runs_seq_assign_le (v := 2 ^ x) ?_ ?_
  · simpa only [Nat.shiftLeft_eq, Nat.one_mul] using
      Expr.eval_shiftLeft (Expr.eval_const h1) (Expr.eval_reg_of_eq (v := x) rfl)
        (by simpa [Nat.shiftLeft_eq] using hM)
  refine runs_seq_assign_le (v := L)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) hL) ?_
  refine runs_seq_assign_le (v := 49 * L + 2)
    (Expr.eval_add (Expr.eval_mul (Expr.eval_const h49) (Expr.eval_reg_of_eq rfl) hmul)
      (Expr.eval_const (by omega)) hdegree) ?_
  let B := buildTopDepthPlayer term (2 ^ x) r (49 * L + 2) L root inner
  have hb : ∀ i < n, ∀ v ∈ (B i).playerWords, v < 2 ^ w := by
    intro i _ v hv
    simp only [B,buildTopDepthPlayer, BuildTopDepthInput.playerWords, List.mem_cons,
      List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ht
    · exact hM
    · exact hrw
    · exact hdegree
    · exact hL
    · exact hL
    · split <;> assumption
  refine runs_seq_call_le (buildTopPlayerTableLoop_meetsContract hl hw)
    (vs := [dst,n,term,2 ^ x,r,49 * L + 2,L,root,inner]) rfl ?_
    ⟨rfl,h1,hroom,hb⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · omega
    · exact ht
    · exact hM
    · exact hrw
    · exact hdegree
    · exact hL
    · exact hroot
    · exact hinner
  intro v mem₃ pos₃ ⟨hv,htable,hframe⟩
  refine runs_ret_le (v := dst) (Expr.eval_reg_of_eq (by simpa only [Function.update_self] using hv))
    ⟨rfl,?_,hframe⟩ ?_
  · intro i hi
    exact htable i hi
  · simp only [Expr.size, argsSize, buildTopRootScaleExpr]
    clear * - m n
    omega

def buildTopPlayerSetupContract (w dst n term x m num den : ℕ) : Contract :=
  {
      pre := fun args _ => args = [dst,n,term,x,m,num,den] ∧
        0 < x ∧ 0 < num ∧ 0 < den ∧ den < 2 ^ w ∧
        8 * m + 8 < 2 ^ w ∧ depthOf m ^ 3 < 2 ^ w ∧
        100 * dOf num den < 2 ^ w ∧ 4 * PParam ParamConfig.default (2 ^ x) (depthOf m) < 2 ^ w ∧
        2 ^ x < 2 ^ w ∧ 49 * (x + 1) + 2 < 2 ^ w ∧ dst + 7 * n < 2 ^ w
      post := fun _ mem v mem' => v = dst ∧
        (∀ i < n, ListAt mem' (dst + 7 * i) (buildTopPlayerWords term x m (dOf num den) i)) ∧
        ∀ y, y < dst ∨ dst + 7 * n ≤ y → mem' y = mem y
      cost := fun _ _ => 13 * (Nat.log 2 (8 * m + 7) + 1) + 32 * depthOf m + 79 * n + 300 }

/-- Write the model player words from the original graph size and conductance. -/
theorem buildTopPlayerSetup_meetsContract
    {w f rank scale power fill write dst n term x m num den : ℕ} {p : Program}
    (hf : p.procs[f]? = some (buildTopPlayerSetup rank scale fill))
    (hr : p.procs[rank]? = some buildTopPlayerRank)
    (hs : p.procs[scale]? = some (buildTopPlayerScale power))
    (hp : p.procs[power]? = some buildTopPlayerPower)
    (hl : p.procs[fill]? = some (buildTopPlayerTableLoop write))
    (hw : p.procs[write]? = some buildTopPlayerTableRow) :
    MeetsContract w p f (buildTopPlayerSetupContract w dst n term x m num den) := by
  intro args mem pos ω hwords hpre
  obtain ⟨heq,hx,hnum,hden,hdenw,hm,hcube,hroot,hinner,hM,hdegree,hroom⟩ := hpre
  let root := 100 * dOf num den
  let inner := 4 * PParam ParamConfig.default (2 ^ x) (depthOf m)
  have hS : MeetsContract w p scale {
      pre := fun args _ => args = [x,depthOf m] ∧ depthOf m < 2 ^ w ∧ inner < 2 ^ w
      post := fun _ mem v mem' => v = inner ∧ mem' = mem
      cost := fun _ _ => 13 * depthOf m + 100 } := by
    intro xs ms ps om hws hh
    exact buildTopPlayerScale_meetsContract hs hp hx xs ms ps om hws
      ⟨hh.1,hx,(by decide : 0 < 2).trans_le (two_le_depthOf m),hh.2⟩
  have hE (st : State) (hn : st.regs 5 = num) (hd : st.regs 6 = den) :
      (buildTopRootScaleExpr (.reg 5) (.reg 6)).eval w st = some root :=
    eval_buildTopRootScaleExpr (Expr.eval_reg_of_eq hn) (Expr.eval_reg_of_eq hd)
      hnum hden hdenw hroot
  exact setupFromScale hf hr hS hE hl hw args mem pos ω hwords
    ⟨heq,hm,hcube,hroot,hinner,hM,hdegree,hroom⟩

end MinCostFlow.HierPaths

end
