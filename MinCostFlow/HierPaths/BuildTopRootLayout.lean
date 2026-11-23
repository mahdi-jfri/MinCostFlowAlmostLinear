module

public import MinCostFlow.HierPaths.BuildTopCost

/-!
# Reserving the root buffers

Use consecutive buffers after the incoming heap pointer. Their sizes
come from the two words in the input graph header.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

def buildTopRootLoc (h n : ℕ) : ℕ := h + n
def buildTopRootOwnersAddr (h n : ℕ) : ℕ := buildTopRootLoc h n + n
def buildTopRootGraphAddr (h n m : ℕ) : ℕ := buildTopRootOwnersAddr h n + 4 * m
def buildTopRootWork (h n m : ℕ) : ℕ := buildTopRootGraphAddr h n m + 2 + 24 * m

/-- Arguments are the input graph address and the incoming heap pointer. -/
def buildTopRootLayout (root : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 4 (.bin .add (.reg 1) (.reg 2)) ;;
  .assign 5 (.bin .add (.reg 4) (.reg 2)) ;;
  .assign 6 (.bin .add (.reg 5) (.bin .mul (.const 4) (.reg 3))) ;;
  .assign 7 (.bin .add (.bin .add (.reg 6) (.const 2)) (.bin .mul (.const 24) (.reg 3))) ;;
  .assign 8 (.bin .add (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 2)))
    (.bin .add (.bin .mul (.const 20) (.reg 3)) (.const 4))) ;;
  .call 9 root [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8] ;;
  .ret (.reg 9)

theorem buildTopRootLayout_noRand (root : ℕ) : (buildTopRootLayout root).NoRand := by
  simp [buildTopRootLayout, Stmt.NoRand]

def buildTopRootLayoutContract (w : ℕ) (G : Graph) : Contract where
  pre args mem := ∃ ga h, args = [ga, h] ∧ GraphAt mem ga G ∧ G.IsValid ∧
    1 ≤ G.m ∧ ga + G.encode.length ≤ h ∧ ZeroFrom mem h ∧
    h + buildTopRootSpace G.n G.m < 2 ^ w ∧ 24 < 2 ^ w
  post args mem r mem' := ∃ ga h, args = [ga, h] ∧
    GraphAt mem' (buildTopRootGraphAddr h G.n G.m) (hostGraph cloud G) ∧
    ListAt mem' (buildTopRootOwnersAddr h G.n) (tabList (hostSize G) (hostOwner G)) ∧
    h + buildTopRootWorkspace G.n G.m ≤ r ∧ r ≤ h + buildTopRootSpace G.n G.m ∧
    ZeroFrom mem' r ∧ ∀ y < h, mem' y = mem y
  cost args mem := (buildTopRootContract w G).cost args mem + 100

theorem buildTopRootLayout_meetsContract {w f root : ℕ} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some (buildTopRootLayout root))
    (hRoot : MeetsContract w p root (buildTopRootContract w G)) :
    MeetsContract w p f (buildTopRootLayoutContract w G) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨ga, h, rfl, hg, hv, hm, hs, hz, hroom, h24⟩ := hpre
  let n := G.n
  let m := G.m
  let la := buildTopRootLoc h n
  let oa := buildTopRootOwnersAddr h n
  let ja := buildTopRootGraphAddr h n m
  let wa := buildTopRootWork h n m
  let top := wa + portGraphWorkSpace n m
  have hl := graph_encode_length G
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have h4 : 4 < 2 ^ w := by omega
  have h20 : 20 < 2 ^ w := by omega
  have hTop : top + portGraphHeapSpace m < 2 ^ w := by
    simpa only [top, wa, ja, oa, la, buildTopRootSpace, buildTopRootWorkspace,
      buildTopRootWork, buildTopRootGraphAddr, buildTopRootOwnersAddr, buildTopRootLoc,
      Nat.add_assoc] using hroom
  have hW : 4 ≤ portGraphWorkSpace n m := by simp [portGraphWorkSpace]
  have hwa : wa < 2 ^ w := by omega
  have hja : ja + 2 + 24 * m < 2 ^ w := hwa
  have hoa : oa + 4 * m < 2 ^ w := by change ja < 2 ^ w; omega
  have hla : la + n < 2 ^ w := by change oa < 2 ^ w; omega
  have hhn : h + n < 2 ^ w := by change la < 2 ^ w; omega
  have hTop' : wa + 2 * n + (20 * m + 4) = top := by
    simp [top, portGraphWorkSpace, Nat.add_assoc]
  have hTopWord : wa + 2 * n + (20 * m + 4) < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold buildTopRootLayout
  refine runs_seq_assign_le (v := n) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := ga) rfl)
    (graphAt_n hg)) ?_
  refine runs_seq_assign_le (v := m) (Expr.eval_load_of_eq (Expr.eval_add
    (Expr.eval_reg_of_eq (v := ga) rfl) (Expr.eval_const h1) (by omega)) (graphAt_m hg)) ?_
  refine runs_seq_assign_le (v := la) (Expr.eval_add
    (Expr.eval_reg_of_eq (v := h) rfl) (Expr.eval_reg_of_eq (v := n) rfl) hhn) ?_
  refine runs_seq_assign_le (v := oa) (Expr.eval_add
    (Expr.eval_reg_of_eq (v := la) rfl) (Expr.eval_reg_of_eq (v := n) rfl) hla) ?_
  refine runs_seq_assign_le (v := ja) (Expr.eval_add
    (Expr.eval_reg_of_eq (v := oa) rfl) (Expr.eval_mul (Expr.eval_const h4)
      (Expr.eval_reg_of_eq (v := m) rfl) (by omega)) hoa) ?_
  refine runs_seq_assign_le (v := wa) (Expr.eval_add
    (Expr.eval_add (Expr.eval_reg_of_eq (v := ja) rfl) (Expr.eval_const h2) (by omega))
    (Expr.eval_mul (Expr.eval_const h24) (Expr.eval_reg_of_eq (v := m) rfl) (by omega)) hja) ?_
  refine runs_seq_assign_le (v := top) (Expr.eval_eq_of_eq (Expr.eval_add
    (Expr.eval_add (Expr.eval_reg_of_eq (v := wa) rfl)
      (Expr.eval_mul (Expr.eval_const h2) (Expr.eval_reg_of_eq (v := n) rfl) (by omega)) (by omega))
    (Expr.eval_add (Expr.eval_mul (Expr.eval_const h20) (Expr.eval_reg_of_eq (v := m) rfl)
      (by omega)) (Expr.eval_const h4) (by omega)) hTopWord) hTop') ?_
  refine runs_seq_call_le hRoot (vs := [ga, h, la, oa, ja, wa, top]) rfl ?_ ?_ ?_
  · intro v hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · exact ⟨ga, h, la, oa, ja, wa, top, rfl,
      ⟨ga, h, la, oa, ja, wa, top, rfl, hg, hv, hz, hs, le_rfl, le_rfl,
        by change oa + 2 * m ≤ oa + 4 * m; omega,
        by change ja + 2 + 20 * m ≤ ja + 2 + 24 * m; omega,
        le_rfl, hTop.le, by omega⟩, hm, le_rfl, le_rfl⟩
  intro r mem₁ pos₁ hpost
  obtain ⟨ga', h', la', oa', ja', wa', top', ha, hgraph, howners, hle, hcap, hzero, hf⟩ := hpost
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, _, _⟩ := ha
  subst ga' h' la' oa' ja' wa' top'
  have he : top = h + buildTopRootWorkspace n m := by
    simp [top, wa, ja, oa, la, buildTopRootWorkspace, buildTopRootWork, buildTopRootGraphAddr,
      buildTopRootOwnersAddr, buildTopRootLoc, Nat.add_assoc]
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨ga, h, rfl, hgraph, howners, he ▸ hle, ?_, hzero, hf⟩ ?_
  · change r ≤ h + buildTopRootSpace n m
    simpa [he, buildTopRootSpace, Nat.add_assoc] using hcap
  · simp [buildTopRootLayoutContract, buildTopRootContract, buildTopPortContract, Expr.size, argsSize, n, m]
    omega

end MinCostFlow.HierPaths

end
