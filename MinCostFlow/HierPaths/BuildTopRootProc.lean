module

public import MinCostFlow.HierPaths.BuildTopRootModel
public import MinCostFlow.HierPaths.BuildTopSize

/-!
# Constructing the padded root host

The port graph uses the whole input graph. We compute the next power of
two, extend the owner and graph tables in their reserved space, and keep
the heap pointer returned by the port graph construction.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

def buildTopRootProc (port size pad : ℕ) : Stmt :=
  .call 7 port [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6] ;;
  .call 8 size [.load (.bin .add (.reg 0) (.const 1))] ;;
  .call 9 pad [.reg 4, .reg 3, .bin .shiftLeft (.const 1) (.reg 8)] ;;
  .ret (.reg 7)

theorem buildTopRootProc_noRand (port size pad : ℕ) : (buildTopRootProc port size pad).NoRand := by
  simp [buildTopRootProc, Stmt.NoRand]

/-- Port construction with enlarged owner and graph buffers for padding. -/
def buildTopRootContract (w : ℕ) (G : Graph) : Contract where
  pre args mem := ∃ ga va la oa ja wa h, args = [ga, va, la, oa, ja, wa, h] ∧
    (buildTopPortContract w G).pre args mem ∧ 1 ≤ G.m ∧
    oa + 4 * G.m ≤ ja ∧ ja + 2 + 24 * G.m ≤ wa
  post args mem r mem' := ∃ ga va la oa ja wa h, args = [ga, va, la, oa, ja, wa, h] ∧
    GraphAt mem' ja (hostGraph cloud G) ∧
    ListAt mem' oa (tabList (hostSize G) (hostOwner G)) ∧
    h ≤ r ∧ r ≤ h + portGraphHeapSpace G.m ∧ ZeroFrom mem' r ∧ ∀ y < va, mem' y = mem y
  cost args mem := (buildTopPortContract w G).cost args mem + 160 * G.m + 200

theorem buildTopRootProc_meetsContract {w f port size pad : ℕ} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some (buildTopRootProc port size pad))
    (hPort : MeetsContract w p port (buildTopPortContract w G))
    (hSize : p.procs[size]? = some buildTopSize)
    (hPad : MeetsContract w p pad (buildTopRootPadContract w (portGraph cloud G G.verts)
      ((List.range (2 * G.m)).map (portOwner G G.verts)))) :
    MeetsContract w p f (buildTopRootContract w G) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨ga, va, la, oa, ja, wa, h, rfl, hPortPre, hm, hOwnCap, hGraphCap⟩ := hpre
  have hPortPre' := hPortPre
  obtain ⟨ga', va', la', oa', ja', wa', h', ha, hGraphAt, hValid, _, hsep, hvl, hlo,
    _, _, hwh, _, h16⟩ := hPortPre'
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨e₀,e₁,e₂,e₃,e₄,e₅,e₆⟩ := ha
  subst ga' va' la' oa' ja' wa' h'
  have hLen := graph_encode_length G
  have hga : ga + 1 < va := by omega
  have hvo : va ≤ oa := by omega
  let base := [ga, va, la, oa, ja, wa, h]
  let P := hostSize G
  let q := P - portCount G
  let J := portGraph cloud G G.verts
  have hcount : portCount G = 2 * G.m := by simp [portCount, inside_verts_length hValid]
  have hJ : J.n = 2 * G.m := by simp [J, portGraph_n, inside_verts_length hValid]
  have hP := le_hostSize G
  change portCount G ≤ P at hP
  have hLt : P < 2 * portCount G :=
    hostSize_lt (by rwa [inside_verts_length hValid])
  have hq : q ≤ G.m * 2 := by dsimp [q]; omega
  have hE := graph_encode_length (hostGraph cloud G)
  have hh := hostGraph_m_le isCloudExpander_cloud (by rwa [inside_verts_length hValid])
  rw [inside_verts_length hValid] at hh
  have hHostCap : ja + (hostGraph cloud G).encode.length ≤ wa := by omega
  have hHeap : h < 2 ^ w := hw _ (by simp)
  have hPword : P < 2 ^ w := by omega
  have hJn : (portGraph cloud G G.verts).n = 2 * G.m := hJ
  have h1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold buildTopRootProc
  refine runs_seq_call_le hPort (vs := base) rfl hw hPortPre ?_
  intro r mem₁ pos₁ hpost
  obtain ⟨ga', va', la', oa', ja', wa', h', ha, hJAt, hOwner, hhr, hcap, hzero, hframe⟩ := hpost
  change [ga, va, la, oa, ja, wa, h] = _ at ha
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨e₀,e₁,e₂,e₃,e₄,e₅,e₆⟩ := ha
  subst ga' va' la' oa' ja' wa' h'
  refine runs_seq_call_le (buildTopSize_meetsContract hSize) (vs := [G.m]) ?_ ?_
    ⟨G.m, rfl, hm, by omega⟩ ?_
  · have hread : mem₁ (ga + 1) = G.m := (hframe _ hga).trans (graphAt_m hGraphAt)
    have haddr : ga + 1 < 2 ^ w := by omega
    simp [evalArgs, Expr.eval, startState, BinOp.eval, h1, haddr, hread]
  · intro v hv'
    simp only [List.mem_singleton] at hv'
    subst v
    omega
  intro x mem₂ pos₂ hpost
  obtain ⟨hx, hmem⟩ := hpost
  change mem₂ = mem₁ at hmem
  subst mem₂
  change x = Nat.clog 2 (2 * G.m) at hx
  have hxP : 2 ^ x = P := by rw [hx]; simp [P, hostSize, hcount]
  refine runs_seq_call_le hPad (vs := [ja, oa, P]) ?_ ?_
    ⟨ja, oa, P, rfl, hJAt, hOwner, by simp [hJn], by omega, by omega, by omega, ?_⟩ ?_
  · have hv' : 1 <<< x < 2 ^ w := by rw [Nat.shiftLeft_eq, Nat.one_mul, hxP]; exact hPword
    simp [evalArgs, Expr.eval, startState, BinOp.eval, h1, hv', Nat.shiftLeft_eq, hxP, hPword]
  · intro v hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hw _ (by simp)
    · exact hPword
  · rw [buildTopPaddedGraph_eq]
    omega
  intro e mem₃ pos₃ hpost
  obtain ⟨ja', oa', P', ha, he, hGraph, hOwn, hframe₃⟩ := hpost
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨e₀,e₁,e₂⟩ := ha
  subst ja' oa' P'
  rw [buildTopPaddedGraph_eq] at he hGraph
  have hOwn' : ListAt mem₃ oa (tabList P (hostOwner G)) := by
    rw [← buildTopRootOwners_eq hValid hm]
    simpa only [hJn, hcount, P] using hOwn
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨ga, va, la, oa, ja, wa, h, rfl, hGraph, hOwn', hhr, hcap, ?_, ?_⟩ ?_
  · intro y hy
    change r ≤ y at hy
    exact (hframe₃ y ⟨.inr (by omega), .inr (by omega)⟩).trans (hzero y hy)
  · intro y hy
    exact (hframe₃ y ⟨.inl (by omega), .inl (by omega)⟩).trans (hframe y hy)
  · simp [buildTopRootContract, buildTopSizeContract, buildTopRootPadContract, Expr.size, argsSize]
    dsimp only [base, startState]
    rw [hJn]
    omega

end MinCostFlow.HierPaths

end
