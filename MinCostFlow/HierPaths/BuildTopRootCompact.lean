module

public import MinCostFlow.HierPaths.BuildTopPortCompact
public import MinCostFlow.HierPaths.BuildTopPrepare

/-!
# Zero-heap compact padded root and preparation

Reuses `buildTopPort`, `buildTopRootProc`, `buildTopRootLayout`,
`buildTopRootSeeded`, and `buildTopPrepare` verbatim, substituting only
`buildTopPortCompactEntry` and `buildTopCloud` for `portGraphProcs`.
The returned root heap pointer is exactly `h + buildTopRootWorkspace G.n G.m`
(linear in `G.n + G.m`), so the final clearing pass in `buildTopFinish`
scans only `O(m * Γ)` words.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander
  MinCostFlow.ExpanderDecomp MinCostFlow.LowStretch

def buildTopPortCompactWrapContract (w : ℕ) (G : Graph) : Contract where
  pre args mem := (buildTopPortContract w G).pre args mem
  post args mem r mem' := ∃ ga va la oa ja wa h, args = [ga, va, la, oa, ja, wa, h] ∧
    GraphAt mem' ja (portGraph cloud G G.verts) ∧
    ListAt mem' oa ((List.range (2 * G.m)).map (portOwner G G.verts)) ∧
    r = h ∧ ZeroFrom mem' h ∧ ∀ y < va, mem' y = mem y
  cost _ _ := buildTopPortCompactCost G.n G.m + 30 * (G.n + 1) + 80

theorem buildTopPort_compact_meetsContract {w f iota port cloudIdx : ℕ} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some (buildTopPort iota port))
    (hi : p.HasAt iota [iotaP])
    (ht : p.procs[port]? = some (buildTopPortCompactEntry cloudIdx))
    (hc : p.procs[cloudIdx]? = some buildTopCloud) :
    MeetsContract w p f (buildTopPortCompactWrapContract w G) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨ga, va, la, oa, ja, wa, h, rfl, hg, hv, hz, hs, hl, ho, hj, hwk, hh, hroom, h16⟩ := hpre
  let n := G.n
  let m := G.m
  let ea := ga + 2
  have hlen := graph_encode_length G
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hHeap : h < 2 ^ w := hw _ (by simp)
  have hN : n < 2 ^ w := by dsimp [n]; omega
  have hM : m < 2 ^ w := by dsimp [m]; omega
  have hEa : ea < 2 ^ w := by dsimp [ea]; omega
  have hW : 4 ≤ portGraphWorkSpace G.n G.m := by simp [portGraphWorkSpace]
  have hIota : va + n + 1 < 2 ^ w := by dsimp [n]; omega
  refine runs_start_le ?_
  unfold buildTopPort
  refine runs_seq_assign_le (v := n) (Expr.eval_load_of_eq
    (Expr.eval_reg_of_eq (v := ga) rfl) (graphAt_n hg)) ?_
  refine runs_seq_assign_le (v := ea) (Expr.eval_add (Expr.eval_reg_of_eq (v := ga) rfl)
    (Expr.eval_const h2) hEa) ?_
  refine runs_seq_assign_le (v := m) (Expr.eval_load_of_eq (Expr.eval_add
    (Expr.eval_reg_of_eq (v := ga) rfl) (Expr.eval_const h1) (by omega)) (graphAt_m hg)) ?_
  refine runs_seq_call_le (iotaP_spec hi) (vs := [n, va, 1, 0]) ?_ ?_
    ⟨n, va, 1, 0, rfl, hIota, by simpa using hN⟩ ?_
  · simp [evalArgs, Expr.eval, startState, h1]
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hN
    · exact hw _ (by simp)
    · exact h1
    · omega
  intro _ mem₁ pos₁ hpost
  obtain ⟨hvert, hf₁⟩ := hpost n va 1 0 rfl
  have hList : ListAt mem₁ va (List.range n) := by
    intro i hi'
    rw [List.getElem_range]
    simpa using hvert i (by simpa using hi')
  have hEdges : EdgesAt mem₁ ea G.edges := by
    intro i hi'
    obtain ⟨hL, hR⟩ := graphAt_to_edgesAt hg i hi'
    change i < m at hi'
    exact ⟨(hf₁ _ (.inl (by dsimp [ea, m] at *; omega))).trans hL,
      (hf₁ _ (.inl (by dsimp [ea, m] at *; omega))).trans hR⟩
  have hX : (List.range n).toFinset = G.verts := by ext i; simp [Graph.verts, n]
  have hBounds : PortGraphBounds w n n m va ea la oa ja wa h := by
    unfold PortGraphBounds
    dsimp only [n, m, ea]
    exact ⟨by omega, by omega, by omega, by omega, by omega, hh, hroom, h16⟩
  have hDis : PortGraphDisjoint n n m va ea la oa ja wa := by
    unfold PortGraphDisjoint DisjointRange
    dsimp only [n, m, ea]
    repeat' apply And.intro
    all_goals first | (left; omega) | (right; omega)
  refine runs_seq_call_le (buildTopPortCompact_meetsContract ht hc)
    (vs := [n, va, m, ea, la, oa, ja, wa, h]) rfl ?_
    ⟨n, n, va, m, ea, la, oa, ja, wa, h, List.range n, G.edges, rfl, List.length_range,
      List.pairwise_lt_range, fun u hu => List.mem_range.mp hu, rfl, ?_, hList, hEdges,
      fun u hu => (hf₁ _ (.inr (by omega))).trans (hz _ (by omega)),
      fun y hy => (hf₁ _ (.inr (by omega))).trans (hz _ (by omega)), hBounds, hDis⟩ ?_
  · intro v hv'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
    rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | assumption | (apply hw; simp)
  · intro e he
    have hValid := hv e he
    simpa only [List.mem_range] using hValid
  intro r mem₂ pos₂ hpost
  have hrV : readList mem₁ va n = List.range n := by simpa using readList_eq_of_listAt hList
  have hrE : readEdges mem₁ ea m = G.edges := readEdges_eq_of_edgesAt hEdges
  simp only [buildTopPortCompactContract, List.getD_cons_zero, List.getD_cons_succ] at hpost
  rw [hrV, hrE, hX] at hpost
  obtain ⟨_, _, hG, hreq, hz₂, hf₂⟩ := hpost
  obtain ⟨hG, hOwner⟩ := hG G (inside_verts_of_isValid hv)
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl)
    ⟨ga, va, la, oa, ja, wa, h, rfl, hG, ?_, hreq, hz₂, ?_⟩ ?_
  · intro i hi'
    rw [List.getElem_map, List.getElem_range]
    exact hOwner i (by simpa using hi')
  · intro y hy
    exact (hf₂ y (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))).trans
      (hf₁ _ (.inl hy))
  · simp [buildTopPortCompactWrapContract, buildTopPortCompactContract, iotaC, Expr.size,
      argsSize, n, m]
    omega

def buildTopRootCompactContract (w : ℕ) (G : Graph) : Contract where
  pre args mem := (buildTopRootContract w G).pre args mem
  post args mem r mem' := ∃ ga va la oa ja wa h, args = [ga, va, la, oa, ja, wa, h] ∧
    GraphAt mem' ja (hostGraph cloud G) ∧
    ListAt mem' oa (tabList (hostSize G) (hostOwner G)) ∧
    r = h ∧ ZeroFrom mem' h ∧ ∀ y < va, mem' y = mem y
  cost args mem := (buildTopPortCompactWrapContract w G).cost args mem + 160 * G.m + 200

theorem buildTopRootProc_compact_meetsContract {w f port size pad : ℕ} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some (buildTopRootProc port size pad))
    (hPort : MeetsContract w p port (buildTopPortCompactWrapContract w G))
    (hSize : p.procs[size]? = some buildTopSize)
    (hPad : MeetsContract w p pad (buildTopRootPadContract w (portGraph cloud G G.verts)
      ((List.range (2 * G.m)).map (portOwner G G.verts)))) :
    MeetsContract w p f (buildTopRootCompactContract w G) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨ga, va, la, oa, ja, wa, h, rfl, hPortPre, hm, hOwnCap, hGraphCap⟩ := hpre
  have hPortPre' := hPortPre
  obtain ⟨ga', va', la', oa', ja', wa', h', ha, hGraphAt, hValid, _, hsep, hvl, hlo,
    _, _, hwh, _, h16⟩ := hPortPre'
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅, e₆⟩ := ha
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
  have hLt : P < 2 * portCount G := hostSize_lt (by rwa [inside_verts_length hValid])
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
  obtain ⟨ga', va', la', oa', ja', wa', h', ha, hJAt, hOwner, hreq, hzero, hframe⟩ := hpost
  change [ga, va, la, oa, ja, wa, h] = _ at ha
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨e₀, e₁, e₂, e₃, e₄, e₅, e₆⟩ := ha
  subst ga' va' la' oa' ja' wa' h' r
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
  obtain ⟨e₀, e₁, e₂⟩ := ha
  subst ja' oa' P'
  rw [buildTopPaddedGraph_eq] at he hGraph
  have hOwn' : ListAt mem₃ oa (tabList P (hostOwner G)) := by
    rw [← buildTopRootOwners_eq hValid hm]
    simpa only [hJn, hcount, P] using hOwn
  refine runs_ret_le (v := h) (Expr.eval_reg_of_eq rfl)
    ⟨ga, va, la, oa, ja, wa, h, rfl, hGraph, hOwn', rfl, ?_, ?_⟩ ?_
  · intro y hy
    change h ≤ y at hy
    exact (hframe₃ y ⟨.inr (by omega), .inr (by omega)⟩).trans (hzero y hy)
  · intro y hy
    exact (hframe₃ y ⟨.inl (by omega), .inl (by omega)⟩).trans (hframe y hy)
  · simp [buildTopRootCompactContract, buildTopSizeContract, buildTopRootPadContract,
      Expr.size, argsSize]
    dsimp only [base, startState]
    rw [hJn]
    omega

def buildTopRootLayoutCompactContract (w : ℕ) (G : Graph) : Contract where
  pre args mem := (buildTopRootLayoutContract w G).pre args mem
  post args mem r mem' := ∃ ga h, args = [ga, h] ∧
    GraphAt mem' (buildTopRootGraphAddr h G.n G.m) (hostGraph cloud G) ∧
    ListAt mem' (buildTopRootOwnersAddr h G.n) (tabList (hostSize G) (hostOwner G)) ∧
    r = h + buildTopRootWorkspace G.n G.m ∧
    ZeroFrom mem' r ∧ ∀ y < h, mem' y = mem y
  cost args mem := (buildTopRootCompactContract w G).cost args mem + 100

theorem buildTopRootLayout_compact_meetsContract {w f root : ℕ} {G : Graph} {p : Program}
    (hp : p.procs[f]? = some (buildTopRootLayout root))
    (hRoot : MeetsContract w p root (buildTopRootCompactContract w G)) :
    MeetsContract w p f (buildTopRootLayoutCompactContract w G) := by
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
  obtain ⟨ga', h', la', oa', ja', wa', top', ha, hgraph, howners, hreq, hzero, hf⟩ := hpost
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, _, _, _⟩ := ha
  subst ga' h' la' oa' ja' wa' top' r
  have he : top = h + buildTopRootWorkspace n m := by
    simp [top, wa, ja, oa, la, buildTopRootWorkspace, buildTopRootWork, buildTopRootGraphAddr,
      buildTopRootOwnersAddr, buildTopRootLoc, Nat.add_assoc]
  refine runs_ret_le (v := top) (Expr.eval_reg_of_eq rfl)
    ⟨ga, h, rfl, hgraph, howners, he, hzero, hf⟩ ?_
  · simp [buildTopRootLayoutCompactContract, buildTopRootCompactContract,
      buildTopPortCompactWrapContract, Expr.size, argsSize, n, m]
    omega

/-- Relocatable compact padded-root module using `buildTopPortCompactEntry` and `buildTopCloud`. -/
def buildTopRootCompactHelpers (k : ℕ) : List Stmt :=
  [buildTopRootProc (k + 1) (k + 2) (k + 3),
    buildTopPort (k + 6) (k + 7), buildTopSize, buildTopRootPad (k + 4) (k + 5),
    buildCopyProc, buildTopPadProc, iotaP,
    buildTopPortCompactEntry (k + 8), buildTopCloud]

def buildTopRootCompactModule : HierProc where
  entry := buildTopRootLayout
  helpers := buildTopRootCompactHelpers

theorem buildTopRootCompactModule_noRand : buildTopRootCompactModule.NoRand := by
  intro k
  refine ⟨buildTopRootLayout_noRand k, ?_⟩
  intro s hs
  change s ∈ buildTopRootCompactHelpers k at hs
  simp only [buildTopRootCompactHelpers, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact buildTopRootProc_noRand _ _ _
  · exact buildTopPort_noRand _ _
  · exact buildTopSize_noRand
  · exact buildTopRootPad_noRand _ _
  · simp [buildCopyProc, forRange, forUp, Stmt.NoRand]
  · exact buildTopPadProc_noRand
  · exact iotaP_noRand
  · exact buildTopPortCompactEntry_noRand _
  · exact buildTopCloud_noRand

theorem buildTopRootCompactModule_meetsContract {w f k : ℕ} {G : Graph} {p : Program}
    (hp : buildTopRootCompactModule.At p f k) :
    MeetsContract w p f (buildTopRootLayoutCompactContract w G) := by
  obtain ⟨hp, hh⟩ := hp
  have hat : ∀ i (hi : i < (buildTopRootCompactHelpers k).length),
      p.procs[k + i]? = some ((buildTopRootCompactHelpers k)[i]'hi) := hh
  have hi : p.HasAt (k + 6) [iotaP] := by
    intro q hq
    have : q = 0 := by simp at hq; omega
    subst q
    simpa [buildTopRootCompactHelpers] using hat 6 (by simp [buildTopRootCompactHelpers])
  have hPort := buildTopPort_compact_meetsContract (G := G) (w := w)
    (by simpa [buildTopRootCompactHelpers] using hat 1 (by simp [buildTopRootCompactHelpers])) hi
    (by simpa [buildTopRootCompactHelpers] using hat 7 (by simp [buildTopRootCompactHelpers]))
    (by simpa [buildTopRootCompactHelpers] using hat 8 (by simp [buildTopRootCompactHelpers]))
  have hPad := buildTopRootPad_meetsContract (w := w) (J := portGraph cloud G G.verts)
    (owners := (List.range (2 * G.m)).map (portOwner G G.verts))
    (by simpa [buildTopRootCompactHelpers] using hat 3 (by simp [buildTopRootCompactHelpers]))
    (by simpa [buildTopRootCompactHelpers] using hat 4 (by simp [buildTopRootCompactHelpers]))
    (by simpa [buildTopRootCompactHelpers] using hat 5 (by simp [buildTopRootCompactHelpers]))
  exact buildTopRootLayout_compact_meetsContract hp
    (buildTopRootProc_compact_meetsContract
      (by simpa [buildTopRootCompactHelpers] using hat 0 (by simp [buildTopRootCompactHelpers]))
      hPort
      (by simpa [buildTopRootCompactHelpers] using hat 2 (by simp [buildTopRootCompactHelpers])) hPad)

/-- Seeded compact root contract returning `r = h + buildTopRootWorkspace G.n G.m`. -/
def buildTopRootSeededCompactContract (w ga h P n : ℕ) (G : Graph) : Contract :=
  let graph := buildTopRootGraphAddr h G.n G.m
  { pre := fun args mem => args = [ga, h, P, graph, n] ∧
      (buildTopRootLayoutCompactContract w G).pre [ga, h] mem ∧
      h + buildTopRootWorkspace G.n G.m + P + 2 + 13 * n < 2 ^ w
    post := fun _ mem r mem' =>
      let dir := r + P
      let table := dir + 1
      r = h + buildTopRootWorkspace G.n G.m ∧
      GraphAt mem' (buildTopRootGraphAddr h G.n G.m) (hostGraph cloud G) ∧
      ListAt mem' (buildTopRootOwnersAddr h G.n) (tabList (hostSize G) (hostOwner G)) ∧
      (∀ y < h, mem' y = mem y) ∧
      mem' dir = graph ∧ mem' (buildTopSchedulePointer table n 0) = dir ∧
      ListAt mem' r (List.range P) ∧
      ZeroFrom mem' (buildTopSchedulePointer table n 0 + 1)
    cost := fun args mem => (buildTopRootLayoutCompactContract w G).cost args mem + 30 * (P + 1) + 100 }

theorem buildTopRootSeeded_compact_meetsContract {w f root seed iota store ga h P n : ℕ}
    {p : Program} {G : Graph}
    (hf : p.procs[f]? = some (buildTopRootSeeded root seed))
    (hr : MeetsContract w p root (buildTopRootLayoutCompactContract w G))
    (hs : p.procs[seed]? = some (buildTopSeedDepth iota store))
    (hi : p.HasAt iota [LowStretch.iotaP]) (hp : p.procs[store]? = some buildTopSeedRoot) :
    MeetsContract w p f (buildTopRootSeededCompactContract w ga h P n G) := by
  refine meetsContract_of_runs hf fun args mem pos ω hword hpre => ?_
  obtain ⟨rfl, hroot, hroom⟩ := hpre
  let graph := buildTopRootGraphAddr h G.n G.m
  refine runs_start_le ?_
  unfold buildTopRootSeeded
  refine runs_seq_call_le hr (vs := [ga, h]) rfl
    (fun a ha => hword a (List.mem_append_left _ ha)) hroot ?_
  intro r mem₁ pos₁ hpost
  obtain ⟨ga', h', he, hG, hOwn, hreq, hzero, hframe⟩ := hpost
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨rfl, rfl⟩ := he
  let dir := r + P
  let table := dir + 1
  let cell := buildTopSchedulePointer table n 0
  have hdir : dir < 2 ^ w := by dsimp [dir]; omega
  have htable : table < 2 ^ w := by dsimp [table, dir]; omega
  have hcell : cell < 2 ^ w := by dsimp [cell, table, dir, buildTopSchedulePointer]; omega
  have h13 : 13 < 2 ^ w := by
    obtain ⟨_, _, _, _, _, _, _, _, _, h24⟩ := hroot
    omega
  have hsep : dir < cell := by simp [cell, table, buildTopSchedulePointer]; omega
  have hValidG : G.IsValid := by obtain ⟨_, _, _, _, hv, _⟩ := hroot; exact hv
  have hmG : 1 ≤ G.m := by obtain ⟨_, _, _, _, _, hm, _⟩ := hroot; exact hm
  have hmIn : 1 ≤ (G.inside G.verts).length := by rw [inside_verts_length hValidG]; exact hmG
  have hOwnLen : (tabList (hostSize G) (hostOwner G)).length ≤ 4 * G.m := by
    have hp := hostSize_lt hmIn
    have hc : portCount G = 2 * G.m := by simp [portCount, inside_verts_length hValidG]
    simp only [tabList, List.length_map, List.length_range]; omega
  have hGraphLen : (hostGraph cloud G).encode.length ≤ 2 + 24 * G.m := by
    have hE := graph_encode_length (hostGraph cloud G)
    have hh := hostGraph_m_le (G := G) isCloudExpander_cloud hmIn
    rw [inside_verts_length hValidG] at hh; omega
  have hOwnEnd : buildTopRootOwnersAddr h G.n + (tabList (hostSize G) (hostOwner G)).length ≤ r := by
    rw [hreq]
    unfold buildTopRootWorkspace buildTopRootOwnersAddr buildTopRootLoc
    omega
  have hGraphEnd : buildTopRootGraphAddr h G.n G.m + (hostGraph cloud G).encode.length ≤ r := by
    rw [hreq]
    unfold buildTopRootWorkspace buildTopRootGraphAddr buildTopRootOwnersAddr buildTopRootLoc
    omega
  refine runs_seq_assign_le (v := dir)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hdir) ?_
  refine runs_seq_assign_le (v := table)
    (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) htable) ?_
  refine runs_seq_call_le (buildTopSeedDepth_meetsContract hs hi hp)
    (vs := [P, r, dir, graph, cell]) ?_ ?_ ⟨rfl, htable, hsep.ne, .inr (le_refl _), .inr hsep.le⟩ ?_
  · have h0 : 0 < 2 ^ w := Nat.two_pow_pos _
    have hm : 13 * n < 2 ^ w := by dsimp [cell, table, dir, buildTopSchedulePointer] at hcell; omega
    have ha : table + 13 * n < 2 ^ w := by simpa [cell, buildTopSchedulePointer] using hcell
    simp [evalArgs, Expr.eval, BinOp.eval, startState, buildTopPointerExpr,
      h0, h13, hm, ha, cell, buildTopSchedulePointer, graph]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact hword _ (by simp)
    · exact (Nat.le_add_right _ _).trans_lt hdir
    · exact hdir
    · exact hword _ (by simp [graph])
    · exact hcell
  intro u mem₂ pos₂ ⟨_, hd, hc, hterms, hfr⟩
  have hBelowR : ∀ y < r, mem₂ y = mem₁ y := fun y hy =>
    hfr y (.inl hy) (by omega) (by omega)
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl) ?_ ?_
  · refine ⟨hreq, ?_, ?_, ?_, hd, hc, hterms, ?_⟩
    · intro i hi; exact (hBelowR _ (by omega)).trans (hG i hi)
    · intro i hi; exact (hBelowR _ (by omega)).trans (hOwn i hi)
    · intro y hy; exact (hBelowR y (by omega)).trans (hframe y hy)
    · intro y hy
      change cell + 1 ≤ y at hy
      exact (hfr y (.inr (by omega)) (by omega) (by omega)).trans (hzero y (by omega))
  · simp [Expr.size, argsSize, buildTopPointerExpr, buildTopRootLayoutCompactContract,
      buildTopRootCompactContract, buildTopPortCompactWrapContract,
      buildTopRootSeededCompactContract]
    omega

/-- Compact preparation contract: returns `r = h + buildTopRootWorkspace G.n G.m`,
preserving the root graph, owners, terminal list, directory pointer, schedule rows,
and `ZeroFrom mem' (buildTopPrepareHeap r x n)`. -/
def buildTopPrepareCompactContract (w ga h x b n num den : ℕ) (G : Graph) : Contract :=
  let P := 2 ^ x
  let graph := buildTopRootGraphAddr h G.n G.m
  { pre := fun args mem => args = [ga, h, P, graph, n, x, b, G.m, num, den] ∧
      (buildTopRootSeededCompactContract w ga h P n G).pre [ga, h, P, graph, n] mem ∧
      0 < x ∧ 0 < num ∧ 0 < den ∧ den < 2 ^ w ∧
      8 * G.m + 8 < 2 ^ w ∧ depthOf G.m ^ 3 < 2 ^ w ∧
      100 * dOf num den < 2 ^ w ∧ 4 * PParam ParamConfig.default P (depthOf G.m) < 2 ^ w ∧
      P < 2 ^ w ∧ 49 * (x + 1) + 2 < 2 ^ w ∧ n ≤ leafDepth x b ∧ 0 < b ∧ b ≤ x ∧
      buildTopPrepareHeap (h + buildTopRootWorkspace G.n G.m) x n < 2 ^ w
    post := fun _ mem r mem' =>
      let table := buildTopPrepareTable r x
      r = h + buildTopRootWorkspace G.n G.m ∧
      GraphAt mem' (buildTopRootGraphAddr h G.n G.m) (hostGraph cloud G) ∧
      ListAt mem' (buildTopRootOwnersAddr h G.n) (tabList (hostSize G) (hostOwner G)) ∧
      (∀ y < h, mem' y = mem y) ∧
      mem' (r + P) = graph ∧
      mem' (buildTopSchedulePointer table n 0) = r + P ∧
      ListAt mem' r (List.range P) ∧
      (∀ j < n, ∀ dir addr graphs, ListAt mem' (table + 13 * j)
        ((buildTopScheduledDepth table n r x b G.m (dOf num den) j dir addr graphs).scheduleWords
          (buildTopSchedulePointer table n j) (buildTopSchedulePointer table n (j + 1)))) ∧
      ZeroFrom mem' (buildTopPrepareHeap r x n)
    cost := fun _ mem => (buildTopRootSeededCompactContract w ga h P n G).cost [ga, h, P, graph, n] mem +
      (buildTopPlayerSetupContract w 0 n 0 x G.m num den).cost [] mem + 389 * n + 110 }

theorem buildTopPrepare_compact_meetsContract {w f root players schedule ga h x b n num den : ℕ}
    {p : Program} {G : Graph}
    (hf : p.procs[f]? = some (buildTopPrepare root players schedule))
    (hr : MeetsContract w p root (buildTopRootSeededCompactContract w ga h (2 ^ x) n G))
    (hp : ∀ dst term, MeetsContract w p players (buildTopPlayerSetupContract w dst n term x G.m num den))
    (hs : ∀ table src term, MeetsContract w p schedule
      (buildTopScheduleRunContract w x b table n src term G.m (dOf num den))) :
    MeetsContract w p f (buildTopPrepareCompactContract w ga h x b n num den G) := by
  refine meetsContract_of_runs hf fun args mem pos ω hword hpre => ?_
  obtain ⟨rfl, hroot, hx, hnum, hden, hdenw, hm, hcube, hrootScale, hinner, hP, hdegree,
    hdepth, hb, hbx, hspace⟩ := hpre
  let P := 2 ^ x
  let graph := buildTopRootGraphAddr h G.n G.m
  refine runs_start_le ?_
  unfold buildTopPrepare
  refine runs_seq_call_le hr (vs := [ga, h, P, graph, n]) rfl
    (fun a ha => hword a (List.mem_append_left _ ha)) hroot ?_
  intro r mem₁ pos₁ hpost
  obtain ⟨hreq, hG₁, hOwn₁, hFrame₁, hDir₁, hPtr₁, hTerms₁, hz₁⟩ := hpost
  let table := buildTopPrepareTable r x
  let src := buildTopScheduleEnd table n x
  have hheap : buildTopPrepareHeap r x n < 2 ^ w := by rw [hreq]; exact hspace
  have hsrc : src + 7 * n < 2 ^ w := hheap
  have htable : table + 13 * n ≤ src := by
    unfold src buildTopScheduleEnd buildTopScheduleReplies buildTopSchedulePointer
    omega
  have hsrcW : src < 2 ^ w := by omega
  have htableW : table < 2 ^ w := by omega
  have hpreTable : r + 2 ^ x < 2 ^ w := Nat.lt_of_succ_lt htableW
  have hrw : r < 2 ^ w := (Nat.le_add_right _ _).trans_lt hpreTable
  have h1 : 1 < 2 ^ w := by omega
  have h13 : 13 < 2 ^ w := by
    obtain ⟨_, hh, _⟩ := hroot
    obtain ⟨_, _, _, _, _, _, _, _, _, hw⟩ := hh
    omega
  have hValidG : G.IsValid := by obtain ⟨_, hh, _⟩ := hroot; obtain ⟨_, _, _, _, hv, _⟩ := hh; exact hv
  have hmG : 1 ≤ G.m := by obtain ⟨_, hh, _⟩ := hroot; obtain ⟨_, _, _, _, _, hm, _⟩ := hh; exact hm
  have hmIn : 1 ≤ (G.inside G.verts).length := by rw [inside_verts_length hValidG]; exact hmG
  have hOwnEnd : buildTopRootOwnersAddr h G.n + (tabList (hostSize G) (hostOwner G)).length ≤ r := by
    have hp := hostSize_lt hmIn
    have hc : portCount G = 2 * G.m := by simp [portCount, inside_verts_length hValidG]
    have hl : (tabList (hostSize G) (hostOwner G)).length ≤ 4 * G.m := by
      simp only [tabList, List.length_map, List.length_range]; omega
    rw [hreq]; unfold buildTopRootWorkspace buildTopRootOwnersAddr buildTopRootLoc; omega
  have hGraphEnd : buildTopRootGraphAddr h G.n G.m + (hostGraph cloud G).encode.length ≤ r := by
    have hE := graph_encode_length (hostGraph cloud G)
    have hh := hostGraph_m_le (G := G) isCloudExpander_cloud hmIn
    rw [inside_verts_length hValidG] at hh
    rw [hreq]; unfold buildTopRootWorkspace buildTopRootGraphAddr buildTopRootOwnersAddr buildTopRootLoc; omega
  refine runs_seq_assign_le (v := table)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hpreTable)
      (Expr.eval_const h1) htableW) ?_
  refine runs_seq_assign_le (v := src)
    (eval_buildTopRepliesExpr (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl)
      (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) h13 hP hsrcW) ?_
  refine runs_seq_call_le (hp src r) (vs := [src, n, r, x, G.m, num, den]) rfl ?_
    ⟨rfl, hx, hnum, hden, hdenw, hm, hcube, hrootScale, hinner, hP, hdegree, hsrc⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · omega
    · exact hword _ (by simp)
    · exact hrw
    · exact hword _ (by simp)
    · exact hword _ (by simp)
    · exact hword _ (by simp)
    · exact hdenw
  intro a mem₂ pos₂ ⟨_, hplayers, hfp⟩
  have hwords : ∀ j < n, ∀ v ∈ buildTopPlayerWords r x G.m (dOf num den) j, v < 2 ^ w := by
    intro j _ v hv
    simp only [buildTopPlayerWords, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hrw
    · exact hP
    · exact (Nat.le_self_pow (by decide : 3 ≠ 0) _).trans_lt hcube
    · exact hdegree
    · exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 49)).trans_lt (by omega)
    · exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 49)).trans_lt (by omega)
    · split <;> assumption
  refine runs_seq_call_le (hs table src r) (vs := [x, b, table, n, src]) rfl ?_
    ⟨rfl, hdepth, hb, hbx, hP, by omega, hsrc, .inr htable, hwords, hplayers⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact hword _ (by simp)
    · exact hword _ (by simp)
    · omega
    · exact hword _ (by simp)
    · omega
  intro v mem₃ pos₃ ⟨_, hrows, hfs⟩
  have hBelowTable : ∀ y < table, mem₃ y = mem₁ y := fun y hy =>
    (hfs y (.inl hy)).trans (hfp y (.inl (by omega)))
  have hr_lt_table : r < table := by show r < r + 2 ^ x + 1; exact Nat.lt_succ_of_le (Nat.le_add_right _ _)
  have hrP_lt_table : r + 2 ^ x < table := by show r + 2 ^ x < r + 2 ^ x + 1; exact Nat.lt_succ_self _
  have hhr : h ≤ r := by rw [hreq]; exact Nat.le_add_right _ _
  have hG_lt_table : ∀ i < (hostGraph cloud G).encode.length, buildTopRootGraphAddr h G.n G.m + i < table :=
    fun i hi => lt_of_lt_of_le (Nat.add_lt_add_left hi _) (hGraphEnd.trans hr_lt_table.le)
  have hOwn_lt_table : ∀ i < (tabList (hostSize G) (hostOwner G)).length, buildTopRootOwnersAddr h G.n + i < table :=
    fun i hi => lt_of_lt_of_le (Nat.add_lt_add_left hi _) (hOwnEnd.trans hr_lt_table.le)
  have hH_lt_table : ∀ y < h, y < table := fun y hy => lt_of_lt_of_le hy (hhr.trans hr_lt_table.le)
  have hPtrKeep : mem₃ (buildTopSchedulePointer table n 0) = mem₁ (buildTopSchedulePointer table n 0) := by
    have h1' : table + 13 * n ≤ buildTopSchedulePointer table n 0 := by
      unfold buildTopSchedulePointer; omega
    have h2' : buildTopSchedulePointer table n 0 < src := by
      unfold src buildTopScheduleEnd buildTopScheduleReplies buildTopSchedulePointer; omega
    exact (hfs _ (.inr h1')).trans (hfp _ (.inl h2'))
  refine runs_ret_le (v := r) (Expr.eval_reg_of_eq rfl) ?_ ?_
  · dsimp only [buildTopPrepareCompactContract, Outcome.value]
    refine ⟨hreq, ?_, ?_, ?_, ?_, ?_, ?_, hrows, ?_⟩
    · intro i hi; exact (hBelowTable _ (hG_lt_table i hi)).trans (hG₁ i hi)
    · intro i hi; exact (hBelowTable _ (hOwn_lt_table i hi)).trans (hOwn₁ i hi)
    · intro y hy; exact (hBelowTable y (hH_lt_table y hy)).trans (hFrame₁ y hy)
    · exact (hBelowTable _ hrP_lt_table).trans hDir₁
    · exact hPtrKeep.trans hPtr₁
    · intro i hi
      have hi' : i < 2 ^ x := by simpa using hi
      exact (hBelowTable _ (lt_trans (Nat.add_lt_add_left hi' r) hrP_lt_table)).trans (hTerms₁ i hi)
    · intro y hy
      change src + 7 * n ≤ y at hy
      change mem₃ y = 0
      refine (hfs y (.inr (by omega))).trans ((hfp y (.inr hy)).trans (hz₁ y ?_))
      simp only [src, buildTopScheduleEnd, buildTopScheduleReplies, buildTopSchedulePointer,
        table, buildTopPrepareTable] at hy ⊢
      omega
  · simp only [buildTopPrepareCompactContract, Expr.size, argsSize, buildTopRepliesExpr,
      buildTopPointerExpr, buildTopScheduleRunContract, buildTopPlayerSetupContract,
      buildTopRootSeededCompactContract, buildTopRootLayoutCompactContract,
      buildTopRootCompactContract, buildTopPortCompactWrapContract]
    omega

end MinCostFlow.HierPaths

end
