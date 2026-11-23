module

public import MinCostFlow.Spanner.ProgSetup
public import MinCostFlow.Spanner.ProgEmbStats
public import MinCostFlow.Spanner.ProgWitnessPrepProof
public import MinCostFlow.Spanner.ProgBuildWitnessProof
public import MinCostFlow.Spanner.ToolContracts
public import MinCostFlow.Spanner.Runtime
public import WordRAM.Logic

/-!
# Task 1 Word-RAM program (`Sparsify` witness construction)

This module packages Task 1 of Algorithm 4 (`Sparsify`, `spanner.tex`, page 42) into a deterministic
Word-RAM procedure `task1Module`:
1. `embJHStats`: computes `maxDeg J`, `length J embJH`, `vcongNat J H' embJH` at `statsAddr = h + 6`.
2. `stripLoops`: computes `J0_strip` and `nlIdx` at `j0Addr` and `nlAddr`.
3. `impl.decompose`: computes decomposition `(d_ℓ, phiNum, phiDen, level, rawComps)` at `decAddr`.
4. `witnessPrep`: populates component subgraphs `cJSub`, `cJOrig`, degrees, and level chains at `prepH`.
5. `buildWitnessCore`: builds expanders `W_sub`, witness `W`, weights `wW`, edge sources, and
   congestion thresholds `τ₁`, `τ₂` at `coreH = prep.hEnd`, returning free heap pointer `vEnd`.

We reserve `[h, h + 6)` to store the 6 Task 1 directory pointers
`[statsAddr, j0Addr, nlAddr, decAddr, prepH, coreH]` at the end of execution so later stages
(`Task 2`, `Task 3`, `Sparsify`) read them in `O(1)` time without disturbing `[0, h)` or `[vEnd, ∞)`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## 1. Program and determinism -/

/-- Procedure body of Task 1, calling `stripBase`, `statsBase`, `decBase`, `prepBase`, `coreBase`.
Arguments in registers `0..3` (`startState` convention):
`r0 = hAddr`, `r1 = jAddr`, `r2 = embJHAddr`, `r3 = h`.
Returns the new free heap pointer `vEnd` in `r13` and writes `[statsAddr, j0Addr, nlAddr, decAddr,
prepH, coreH]` at `[h, h + 6)`. -/
def task1Body (stripBase statsBase decBase prepBase coreBase : ℕ) : Stmt :=
  Stmt.seq (Stmt.assign 4 (.load (.reg 0))) <|
  Stmt.seq (Stmt.assign 5 (.bin .add (.reg 3) (.const 6))) <|
  Stmt.seq (Stmt.call 6 statsBase [.reg 1, .reg 2, .reg 4, .reg 5]) <|
  Stmt.seq (Stmt.assign 7 (.bin .add (.reg 1) (.const 1))) <|
  Stmt.seq (Stmt.assign 7 (.load (.reg 7))) <|
  Stmt.seq (Stmt.assign 8 (.bin .mul (.const 2) (.reg 7))) <|
  Stmt.seq (Stmt.assign 8 (.bin .add (.reg 8) (.const 2))) <|
  Stmt.seq (Stmt.assign 8 (.bin .add (.reg 6) (.reg 8))) <|
  Stmt.seq (Stmt.call 9 stripBase [.reg 1, .reg 6, .reg 8]) <|
  Stmt.seq (Stmt.assign 10 (.bin .add (.reg 8) (.reg 9))) <|
  Stmt.seq (Stmt.call 11 decBase [.reg 6, .reg 10]) <|
  Stmt.seq (Stmt.call 12 prepBase [.reg 1, .reg 6, .reg 8, .reg 10, .reg 11]) <|
  Stmt.seq (Stmt.call 13 coreBase [.reg 1, .reg 5, .reg 10, .reg 11, .reg 12]) <|
  Stmt.seq (Stmt.store (.reg 3) (.reg 5)) <|
  Stmt.seq (Stmt.assign 14 (.bin .add (.reg 3) (.const 1))) <|
  Stmt.seq (Stmt.store (.reg 14) (.reg 6)) <|
  Stmt.seq (Stmt.assign 14 (.bin .add (.reg 3) (.const 2))) <|
  Stmt.seq (Stmt.store (.reg 14) (.reg 8)) <|
  Stmt.seq (Stmt.assign 14 (.bin .add (.reg 3) (.const 3))) <|
  Stmt.seq (Stmt.store (.reg 14) (.reg 10)) <|
  Stmt.seq (Stmt.assign 14 (.bin .add (.reg 3) (.const 4))) <|
  Stmt.seq (Stmt.store (.reg 14) (.reg 11)) <|
  Stmt.seq (Stmt.assign 14 (.bin .add (.reg 3) (.const 5))) <|
  Stmt.seq (Stmt.store (.reg 14) (.reg 12)) <|
  Stmt.ret (.reg 13)

/-- Single-procedure module for Task 1. -/
def task1Module (stripBase statsBase decBase prepBase coreBase : ℕ) : List Stmt :=
  [task1Body stripBase statsBase decBase prepBase coreBase]

theorem task1Body_noRand (stripBase statsBase decBase prepBase coreBase : ℕ) :
    (task1Body stripBase statsBase decBase prepBase coreBase).NoRand := by
  simp [task1Body, Stmt.NoRand]

theorem task1Module_noRand (stripBase statsBase decBase prepBase coreBase : ℕ) :
    ∀ s ∈ task1Module stripBase statsBase decBase prepBase coreBase, s.NoRand := by
  simp only [task1Module, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact task1Body_noRand stripBase statsBase decBase prepBase coreBase

/-! ## 2. Task 1 input, static bounds, output, and cost -/

/-- Input snapshot for Task 1. -/
structure Task1Input where
  hAddr : ℕ
  jAddr : ℕ
  embJHAddr : ℕ
  h : ℕ
  H' : Graph
  J : Graph
  embJH : ℕ → Walk

namespace Task1Input

/-- Upper cap on `dJInt` using `impl.decompose.φ_lb`. -/
noncomputable def dJCap (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  Nat.ceil (1 / impl.decompose.φ_lb (stripLoops J).m)

/-- Upper cap on `mwInt` using `impl.decompose.φ_lb`. -/
noncomputable def mwCap (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  Nat.ceil (2 * (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops J).m : ℝ) /
    impl.decompose.φ_lb (stripLoops J).m) + 1

/-- Maximum `phiDen_dec` allowed by `impl.decompose`. -/
def phiDenCap (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  impl.decompose.maxPhiDen (stripLoops J).m

/-- Conservative upper bound on `d_ℓ` from `DecomposeProp`. -/
noncomputable def dLMax (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  Nat.floor (impl.decompose.c_ℓ * (Nat.log 2 ((stripLoops J).m + 2) + 1))

/-- Address where `J0_strip` is written (`statsAddr + 3 + J.n + 2 * H'.n`). -/
def j0Addr (inp : Task1Input) : ℕ :=
  inp.h + 6 + 3 + inp.J.n + 2 * inp.H'.n

/-- Address where `nlIdx` is written (`j0Addr + 2 + 2 * J.m`). -/
def nlAddr (inp : Task1Input) : ℕ :=
  inp.j0Addr + 2 + 2 * inp.J.m

/-- Address where `Decompose` writes its output (`nlAddr + (stripLoops J).m`). -/
def decAddr (inp : Task1Input) : ℕ :=
  inp.nlAddr + (stripLoops inp.J).m

/-- Worst-case free heap pointer after `Decompose`. -/
def prepHMax (impl : SpannerToolImpl) (inp : Task1Input) : ℕ :=
  inp.decAddr + impl.decompose.space inp.J.n (stripLoops inp.J).m

/-- Worst-case free heap pointer after `witnessPrep`. -/
noncomputable def coreHMax (impl : SpannerToolImpl) (inp : Task1Input) : ℕ :=
  inp.prepHMax impl + 9 + dLMax impl inp.J + 16 * (stripLoops inp.J).m + 2 * inp.J.n

/-- Worst-case `phiDsDenInt`. -/
noncomputable def phiDsDenCap (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  let m0 := (stripLoops J).m
  let pds := impl.pathDS.params
  let dJ := dJCap impl J
  let mw := mwCap impl J
  max (pds.phiOutDen dJ m0) (pds.phiOutDen (WitnessCoreInput.dWInt impl.constructExpander) mw)

/-- Worst-case `γExpInt`. -/
noncomputable def gammaExpCap (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  let m0 := (stripLoops J).m
  let pds := impl.pathDS.params
  let dJ := dJCap impl J
  let mw := mwCap impl J
  max (pds.gExp dJ m0) (pds.gExp (WitnessCoreInput.dWInt impl.constructExpander) mw)

/-- Worst-case `γDelInt`. -/
noncomputable def gammaDelCap (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  let m0 := (stripLoops J).m
  let pds := impl.pathDS.params
  let dJ := dJCap impl J
  let mw := mwCap impl J
  max (pds.gDel dJ m0) (pds.gDel (WitnessCoreInput.dWInt impl.constructExpander) mw)

/-- Worst-case `tau2Int`. -/
noncomputable def tau2Cap (impl : SpannerToolImpl) (J : Graph) : ℕ :=
  gammaExpCap impl J * gammaDelCap impl J * phiDsDenCap impl J

/-- Worst-case end of Task 1 heap allocation. -/
noncomputable def maxHeapEnd (impl : SpannerToolImpl) (inp : Task1Input) : ℕ :=
  let m0 := (stripLoops inp.J).m
  let ce := impl.constructExpander
  let pds := impl.pathDS.params
  let dJ := dJCap impl inp.J
  let mw := mwCap impl inp.J
  let dW := WitnessCoreInput.dWInt ce
  let pdCap := phiDenCap impl inp.J
  let wMUpper := m0 + 2 * ce.c_deg_int * m0 * pdCap
  inp.coreHMax impl + 20 +
    pds.C_space * (dJ + m0 + 2) ^ pds.c_space +
    pds.C_space * (dW + mw + 2) ^ pds.c_space +
    6 * m0 + 4 * m0 +
    m0 * ce.C_space * (inp.J.n + 4 * m0 * pdCap + 2) ^ ce.c_space +
    (2 + 6 * wMUpper + 3 * inp.J.m)

/-- Worst-case machine word created during Task 1. -/
noncomputable def maxWordBound (impl : SpannerToolImpl) (inp : Task1Input) : ℕ :=
  let m0 := (stripLoops inp.J).m
  let ce := impl.constructExpander
  let pdCap := phiDenCap impl inp.J
  max (inp.maxHeapEnd impl)
    (max (4 * (m0 + 1) * pdCap + 2 * ce.c_deg_int * (m0 + 1) * pdCap + 2 * ce.phiDen + 2)
      (2 * tau2Cap impl inp.J * (length inp.J inp.embJH + 1) *
        (vcongNat inp.J inp.H' inp.embJH + maxDeg inp.J + 1) + 2))

/-- Sufficient word-width condition for all 5 subcalls of Task 1. -/
noncomputable def WordWidthOK (impl : SpannerToolImpl) (inp : Task1Input) (w : ℕ) : Prop :=
  let m0 := (stripLoops inp.J).m
  let ce := impl.constructExpander
  let pds := impl.pathDS.params
  let pdCap := phiDenCap impl inp.J
  let dJ := dJCap impl inp.J
  let mw := mwCap impl inp.J
  let dW := WitnessCoreInput.dWInt ce
  1 < 2 ^ w ∧
  (∀ x ∈ inp.J.encode, x < 2 ^ w) ∧
  impl.decompose.cw * (Nat.log 2 (inp.J.n + m0 + pdCap + 2) + 1) ≤ w ∧
  pds.cw * (Nat.log 2 (dJ + m0 + pds.gExp dJ m0 + pds.gDel dJ m0 + 2) + 1) ≤ w ∧
  pds.cw * (Nat.log 2 (dW + mw + pds.gExp dW mw + pds.gDel dW mw + 2) + 1) ≤ w ∧
  ce.cw * (Nat.log 2 (inp.J.n + 4 * m0 * pdCap + 2) + 1) ≤ w ∧
  inp.maxWordBound impl < 2 ^ w

/-- Full precondition for executing Task 1 on `(impl, inp, mem, w)`. -/
noncomputable def Valid (inp : Task1Input) (impl : SpannerToolImpl)
    (mem : ℕ → ℕ) (w : ℕ) : Prop :=
  inp.H'.IsValid ∧
  GraphAt mem inp.hAddr inp.H' ∧
  inp.J.IsValid ∧
  GraphAt mem inp.jAddr inp.J ∧
  IsEmbedding inp.J inp.H' inp.embJH ∧
  EmbAt mem inp.embJHAddr inp.J.m inp.embJH ∧
  EmbBounded mem inp.embJHAddr inp.J.m inp.embJH inp.h ∧
  inp.hAddr + inp.H'.encode.length ≤ inp.h ∧
  inp.jAddr + inp.J.encode.length ≤ inp.h ∧
  WordRAM.ZeroFrom mem inp.h ∧
  inp.WordWidthOK impl w

end Task1Input

/-- Static cost upper bound for Task 1 on `(impl, J, embVertSum)`. -/
noncomputable def task1StepCost (impl : SpannerToolImpl) (J : Graph) (embVertSum : ℕ) : ℕ :=
  let m0 := (stripLoops J).m
  let ce := impl.constructExpander
  let pds := impl.pathDS.params
  let φ_min := impl.decompose.φ_lb m0
  let dJ := Task1Input.dJCap impl J
  let mw := Task1Input.mwCap impl J
  let dW := WitnessCoreInput.dWInt ce
  (215 * J.m + 120 * embVertSum + 180) +
  (115 * J.m + 55) +
  ⌈impl.decompose.K_dec * ((m0 : ℝ) * impl.decompose.decFactor m0 + 1)⌉₊ +
  (1200 * m0 + 500) +
  (350 + pds.K_bounds * (Nat.log 2 (dJ + m0 + 2) + 1) +
    pds.K_bounds * (Nat.log 2 (dW + mw + 2) + 1)) +
  (265 * m0 + 10 + (m0 + ⌈ce.K_ce * (4 * (m0 : ℝ) + 2 * (m0 : ℝ) / φ_min)⌉₊)) +
  (307 * m0 + 119 * mw + 120) +
  200

/-- Output invariant guaranteed by `task1Module` upon returning `v`. -/
def Task1OutAt (impl : SpannerToolImpl) (jAddr h : ℕ)
    (H' J : Graph) (embJH : ℕ → Walk) (mem mem' : ℕ → ℕ) (v w : ℕ) : Prop :=
  ∃ (wInp : WitnessCoreInput) (WSubs : List Graph),
    wInp.H' = H' ∧
    (∀ e < J.m, wInp.embJH e = embJH e) ∧
    wInp.prep.J = J ∧
    wInp.prep.jAddr = jAddr ∧
    wInp.statsAddr = h + 6 ∧
    wInp.prep.j0Addr = h + 6 + 3 + J.n + 2 * H'.n ∧
    wInp.prep.nlAddr = wInp.prep.j0Addr + 2 + 2 * J.m ∧
    wInp.prep.decAddr = wInp.prep.nlAddr + wInp.prep.J0_strip.m ∧
    wInp.prep.c_ℓ = impl.decompose.c_ℓ ∧
    (∀ x < h, mem' x = mem x) ∧
    WordRAM.ZeroFrom mem' v ∧
    wInp.h + 20 ≤ v ∧
    v ≤ wInp.maxHeapEnd impl.constructExpander impl.pathDS.params ∧
    mem' h = wInp.statsAddr ∧
    mem' (h + 1) = wInp.prep.j0Addr ∧
    mem' (h + 2) = wInp.prep.nlAddr ∧
    mem' (h + 3) = wInp.prep.decAddr ∧
    mem' (h + 4) = wInp.prep.h ∧
    mem' (h + 5) = wInp.h ∧
    mem' wInp.statsAddr = maxDeg J ∧
    mem' (wInp.statsAddr + 1) = length J embJH ∧
    mem' (wInp.statsAddr + 2) = vcongNat J H' embJH ∧
    PrepStaticState wInp.prep mem' mem' ∧
    CompsDoneUpTo wInp.prep mem' wInp.prep.rawComps.length ∧
    wInp.prep.StaticValid mem' w ∧
    wInp.ValidWSubs impl.constructExpander WSubs ∧
    impl.decompose.φ_lb wInp.prep.J0_strip.m ≤
      (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec ∧
    wInp.prep.phiDen_dec ≤ impl.decompose.maxPhiDen wInp.prep.J0_strip.m ∧
    (∀ (memPre : ℕ → ℕ),
      wInp.OutputAt impl.constructExpander impl.pathDS.params
        (fun x => if x < wInp.h then mem' x else memPre x) mem' v
        (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs)) ∧
    (∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK tools H' J embJH
        (wInp.mkWitnessData impl.constructExpander impl.pathDS.params WSubs)) ∧
    wInp.prep.hEnd ≤ wInp.h

section Contract
open Classical

/-- Procedure contract for `task1Module`. -/
noncomputable def task1Contract (impl : SpannerToolImpl) (w : ℕ) : Contract where
  pre args mem :=
    ∃ inp : Task1Input,
      args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] ∧
      inp.Valid impl mem w
  post args mem v mem' :=
    ∀ inp : Task1Input,
      args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] →
      inp.Valid impl mem w →
      Task1OutAt impl inp.jAddr inp.h inp.H' inp.J inp.embJH mem mem' v w ∧
        v ≤ inp.maxHeapEnd impl
  cost args mem :=
    if h : ∃ inp : Task1Input,
        args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] ∧
        inp.Valid impl mem w
    then
      let inp := Classical.choose h
      task1StepCost impl inp.J (embVertSumMem mem inp.jAddr inp.embJHAddr)
    else 0

end Contract

/-! ## 3. Pure helper lemmas for input bounds and step costs -/

/-- Every vertex along a valid walk in `H'` is strictly less than `H'.n`. -/
lemma Walk.IsWalk.verts_lt {H' : Graph} (hH' : H'.IsValid)
    {u v : ℕ} {P : Walk} (hP : P.IsWalk H' u v) :
    ∀ x ∈ P.verts, x < H'.n := by
  intro x hx
  rcases hP with ⟨hu, _, ⟨hPv, _, _⟩ | ⟨_, hlen, hhead, _, hedges, hmatch⟩⟩
  · rw [hPv] at hx; simp at hx
  · rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
    cases i with
    | zero =>
      rcases List.head?_eq_some_iff.mp hhead with ⟨t, hvt⟩
      simp only [hvt, List.getElem_cons_zero]
      exact hu
    | succ i' =>
      have hi'_lt : i' < P.edges.length := by omega
      have hm := hmatch i' hi'_lt
      have he_lt : P.edges.getD i' 0 < H'.m := by
        rw [List.getD_eq_getElem _ _ hi'_lt]
        exact hedges _ (List.getElem_mem hi'_lt)
      have he_valid := hH' _ (List.getElem_mem he_lt)
      have hget_edge : H'.edges.getD (P.edges.getD i' 0) (0, 0) = H'.edges[P.edges.getD i' 0]'he_lt :=
        List.getD_eq_getElem _ _ he_lt
      have hget_vert : P.verts.getD (i' + 1) 0 = P.verts[i' + 1]'hi :=
        List.getD_eq_getElem _ _ hi
      rw [hget_edge, hget_vert] at hm
      rcases hm with ⟨_, h2⟩ | ⟨_, h2⟩
      · simpa [← h2] using he_valid.2
      · simpa [← h2] using he_valid.1

/-- Adding `h` to `WitnessCoreInput.Valid` preserves `(∀ x < wInp.h, x < h ∨ mem x = mem x)`
into `Task1OutAt`. -/
lemma embAt_agree_below {mem mem' : ℕ → ℕ} {a m : ℕ} {emb : ℕ → Walk} {bound : ℕ}
    (hemb : EmbAt mem a m emb) (hb : EmbBounded mem a m emb bound)
    (hagree : ∀ k < bound, mem' k = mem k) :
    EmbAt mem' a m emb ∧ EmbBounded mem' a m emb bound := by
  have ha_m := hb.1
  have hptr : ∀ j < m, mem' (a + j) = mem (a + j) := fun j hj => hagree _ (by omega)
  refine ⟨fun j hj => ?_, ⟨ha_m, fun j hj => ?_⟩⟩
  · rw [hptr j hj]
    intro i hi
    have hlt := hb.2 j hj
    rw [hagree _ (by omega)]
    exact hemb j hj i hi
  · rw [hptr j hj]
    exact hb.2 j hj

/-- Bounds relating runtime `phiNum, phiDen, dJInt, mwInt, tau2Int` to `Task1Input` caps. -/
lemma WitnessCoreInput.caps_le {inp : Task1Input} {impl : SpannerToolImpl}
    {wInp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hv : wInp.prep.Valid mem w)
    (hJ : wInp.prep.J = inp.J)
    (_hH : wInp.H' = inp.H')
    (_hemb : wInp.embJH = inp.embJH)
    (hcℓ : wInp.prep.c_ℓ = impl.decompose.c_ℓ)
    (hce : impl.constructExpander = impl.constructExpander)
    (hφ_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤
      (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec)
    (_hpd_cap : wInp.prep.phiDen_dec ≤ impl.decompose.maxPhiDen wInp.prep.J0_strip.m)
    (_hprep_h : wInp.prep.h ≤ inp.prepHMax impl) :
    wInp.prep.J0_strip = stripLoops inp.J ∧
    wInp.dJInt ≤ Task1Input.dJCap impl inp.J ∧
    wInp.mwInt impl.constructExpander ≤ Task1Input.mwCap impl inp.J ∧
    wInp.prep.d_ℓ ≤ Task1Input.dLMax impl inp.J ∧
    wInp.tau2Int impl.constructExpander impl.pathDS.params ≤ Task1Input.tau2Cap impl inp.J ∧
    wInp.prep.hEnd ≤ inp.coreHMax impl := by
  have _ := hce
  have hJ0 : wInp.prep.J0_strip = stripLoops inp.J := by rw [hv.2.2.1, hJ]
  have hm0 : wInp.prep.J0_strip.m = (stripLoops inp.J).m := congrArg Graph.m hJ0
  have hpn : 1 ≤ wInp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hpnd : wInp.prep.phiNum_dec ≤ wInp.prep.phiDen_dec := hv.2.2.2.2.2.2.2.2.2.1
  have hφ_pos_lb : 0 < impl.decompose.φ_lb (stripLoops inp.J).m :=
    impl.decompose.hφ_lb_pos _
  have hφ_dec_pos : (0 : ℝ) < (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec :=
    div_pos (Nat.cast_pos.mpr hpn) (Nat.cast_pos.mpr (lt_of_lt_of_le hpn hpnd))
  have hφ_lb' : impl.decompose.φ_lb (stripLoops inp.J).m ≤
      (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec := hm0 ▸ hφ_lb
  have hdJ : wInp.dJInt ≤ Task1Input.dJCap impl inp.J := by
    rw [dJInt_eq wInp hv.toStatic]
    unfold Task1Input.dJCap
    exact Nat.ceil_mono (one_div_le_one_div_of_le hφ_pos_lb hφ_lb')
  have hmw : wInp.mwInt impl.constructExpander ≤ Task1Input.mwCap impl inp.J := by
    rw [mwInt_eq wInp impl.constructExpander hv.toStatic, hm0]
    unfold Task1Input.mwCap
    have hdiv : 2 * (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops inp.J).m : ℝ) /
          ((wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) ≤
        2 * (impl.constructExpander.c_deg_int : ℝ) * ((stripLoops inp.J).m : ℝ) /
          impl.decompose.φ_lb (stripLoops inp.J).m :=
      div_le_div_of_nonneg_left (by positivity) hφ_pos_lb hφ_lb'
    exact Nat.add_le_add_right (Nat.ceil_mono hdiv) 1
  have hdl : wInp.prep.d_ℓ ≤ Task1Input.dLMax impl inp.J := by
    have hdp := hv.2.2.2.2.2.2.2.2.2.2.2.2.1.1
    change (wInp.prep.d_ℓ : ℝ) ≤ wInp.prep.c_ℓ * (Nat.log 2 (wInp.prep.J0_strip.m + 2) + 1) at hdp
    rw [hcℓ, hm0] at hdp
    exact Nat.le_floor hdp
  have hdJ1 : 1 ≤ wInp.dJInt := by
    rw [dJInt_eq wInp hv.toStatic]
    exact Nat.ceil_pos.mpr (div_pos one_pos hφ_dec_pos)
  have hdW1 : 1 ≤ WitnessCoreInput.dWInt impl.constructExpander := by
    dsimp only [WitnessCoreInput.dWInt]
    have hpos := impl.constructExpander.hphi_pos
    have hle := impl.constructExpander.hphi_le
    exact Nat.div_pos (by omega) hpos
  let pds := impl.pathDS.params
  have hphiDs : wInp.phiDsDenInt impl.constructExpander impl.pathDS.params ≤
      Task1Input.phiDsDenCap impl inp.J := by
    unfold WitnessCoreInput.phiDsDenInt Task1Input.phiDsDenCap
    exact max_le_max
      (pds.hphiOutDen_mono hdJ1 hdJ hm0.le)
      (pds.hphiOutDen_mono hdW1 le_rfl hmw)
  have hgExp : wInp.γExpInt impl.constructExpander impl.pathDS.params ≤
      Task1Input.gammaExpCap impl inp.J := by
    unfold WitnessCoreInput.γExpInt Task1Input.gammaExpCap
    exact max_le_max
      (pds.hgExp_mono hdJ1 hdJ hm0.le)
      (pds.hgExp_mono hdW1 le_rfl hmw)
  have hgDel : wInp.γDelInt impl.constructExpander impl.pathDS.params ≤
      Task1Input.gammaDelCap impl inp.J := by
    unfold WitnessCoreInput.γDelInt Task1Input.gammaDelCap
    exact max_le_max
      (pds.hgDel_mono hdJ1 hdJ hm0.le)
      (pds.hgDel_mono hdW1 le_rfl hmw)
  have htau2 : wInp.tau2Int impl.constructExpander impl.pathDS.params ≤
      Task1Input.tau2Cap impl inp.J := by
    unfold WitnessCoreInput.tau2Int Task1Input.tau2Cap
    exact Nat.mul_le_mul (Nat.mul_le_mul hgExp hgDel) hphiDs
  have hcore_h : wInp.prep.hEnd ≤ inp.coreHMax impl := by
    have hsb := (PrepInput.size_bounds hv).2.2.2.2.1
    unfold Task1Input.coreHMax
    rw [hJ, hm0] at hsb
    omega
  exact ⟨hJ0, hdJ, hmw, hdl, htau2, hcore_h⟩

private lemma list_sum_eq_finset_sum_getD (xs : List ℕ) :
    xs.sum = ∑ k ∈ Finset.range xs.length, xs.getD k 0 := by
  induction xs with
  | nil => simp
  | cons a t ih =>
    rw [List.sum_cons, List.length_cons, Finset.sum_range_succ', ih]
    simp [List.getD, Nat.add_comm]

/-- Sum of `compWeights` over all components is bounded by `2 * m0 / φ_lb m0`. -/
lemma sum_compWeights_le {wInp : WitnessCoreInput} {impl : SpannerToolImpl}
    {mem : ℕ → ℕ} {w : ℕ} (hv : wInp.prep.Valid mem w)
    (hφ_lb : impl.decompose.φ_lb wInp.prep.J0_strip.m ≤
      (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) :
    ((List.map (fun rc => (wInp.compWeights rc).sum) wInp.prep.rawComps).sum : ℝ) ≤
      2 * (wInp.prep.J0_strip.m : ℝ) / impl.decompose.φ_lb wInp.prep.J0_strip.m := by
  have hst := hv.toStatic
  have hpn : 1 ≤ wInp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hpnd : wInp.prep.phiNum_dec ≤ wInp.prep.phiDen_dec := hv.2.2.2.2.2.2.2.2.2.1
  have hφ_pos : (0 : ℝ) < (wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec :=
    div_pos (Nat.cast_pos.mpr hpn) (Nat.cast_pos.mpr (lt_of_lt_of_le hpn hpnd))
  have hstep : ∀ (ci : ℕ) (hci : ci < wInp.prep.rawComps.length),
      ((wInp.compWeights wInp.prep.rawComps[ci]).sum : ℝ) ≤
        2 * ((wInp.prep.cJSub wInp.prep.rawComps[ci]).m : ℝ) /
          impl.decompose.φ_lb wInp.prep.J0_strip.m := by
    intro ci hci
    set rc := wInp.prep.rawComps[ci]
    have hrc_bang : wInp.prep.rawComps[ci]! = rc := by simp [rc, hci]
    have hcprops := comp_props_at hv hci
    rw [hrc_bang] at hcprops
    have hcb := WitnessCoreInput.comp_weight_bounds hst hci
    have hcb_len : (wInp.compWeights rc).length = rc.2.length := hcb.2.2.1
    have hge := WitnessCoreInput.rawComps_deg_ge_phi hst hci
    have hc_pos : 1 ≤ rc.1 := hcprops.1
    have hpow2 : (2 : ℝ) ≤ (2 : ℝ) ^ rc.1 := by
      have h1 : 2 ≤ 2 ^ rc.1 := by
        simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hc_pos
      exact_mod_cast h1
    have hcw_term : ∀ k (hk : k < rc.2.length),
        ((wInp.compWeights rc).getD k 0 : ℝ) ≤
          ((wInp.prep.cJSub rc).deg k : ℝ) / impl.decompose.φ_lb wInp.prep.J0_strip.m := by
      intro k hk
      have hkl : k < (wInp.compWeights rc).length := by rw [hcb_len]; exact hk
      have hk_cb := hcb.2.2.2.1 k hk
      have hget_eq : (wInp.compWeights rc).getD k 0 = (wInp.compWeights rc)[k]'hkl :=
        List.getD_eq_getElem _ _ hkl
      have hceil_eq : ((wInp.compWeights rc).getD k 0 : ℝ) =
          (Nat.ceil (((wInp.prep.cJSub rc).deg k : ℝ) /
            (((wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) * (2 : ℝ) ^ rc.1)) : ℝ) := by
        rw [hget_eq]
        exact hk_cb.2.1
      set x : ℝ := ((wInp.prep.cJSub rc).deg k : ℝ) /
        (((wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) * (2 : ℝ) ^ rc.1)
      have hx1 : 1 ≤ x := by
        dsimp only [x]
        rw [le_div_iff₀ (mul_pos hφ_pos (pow_pos two_pos _)), one_mul]
        exact hge k hk
      have hx2 : (Nat.ceil x : ℝ) ≤ 2 * x := by
        have hlt := Nat.ceil_lt_add_one (by linarith only [hx1] : 0 ≤ x)
        linarith only [hlt, hx1]
      have hden : 2 * impl.decompose.φ_lb wInp.prep.J0_strip.m ≤
          ((wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) * (2 : ℝ) ^ rc.1 := by
        have hmul := mul_le_mul hφ_lb hpow2 (by positivity) hφ_pos.le
        linarith only [hmul]
      have hdiv_le : 2 * x ≤
          ((wInp.prep.cJSub rc).deg k : ℝ) / impl.decompose.φ_lb wInp.prep.J0_strip.m := by
        have hpos_lb := impl.decompose.hφ_lb_pos wInp.prep.J0_strip.m
        have hdx : 2 * x =
            2 * ((wInp.prep.cJSub rc).deg k : ℝ) /
              (((wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) * (2 : ℝ) ^ rc.1) := by
          dsimp only [x]; ring
        rw [hdx, div_le_div_iff₀ (mul_pos hφ_pos (pow_pos two_pos _)) hpos_lb]
        calc 2 * ((wInp.prep.cJSub rc).deg k : ℝ) * impl.decompose.φ_lb wInp.prep.J0_strip.m
            = ((wInp.prep.cJSub rc).deg k : ℝ) * (2 * impl.decompose.φ_lb wInp.prep.J0_strip.m) := by ring
          _ ≤ ((wInp.prep.cJSub rc).deg k : ℝ) *
                (((wInp.prep.phiNum_dec : ℝ) / wInp.prep.phiDen_dec) * (2 : ℝ) ^ rc.1) :=
              mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _)
      rw [hceil_eq]
      exact le_trans hx2 hdiv_le
    have hsum_cw : ((wInp.compWeights rc).sum : ℝ) =
        ∑ k ∈ Finset.range rc.2.length, ((wInp.compWeights rc).getD k 0 : ℝ) := by
      rw [list_sum_eq_finset_sum_getD, hcb_len]
      push_cast
      rfl
    have hsum_deg_le :
        ∑ k ∈ Finset.range rc.2.length, ((wInp.compWeights rc).getD k 0 : ℝ) ≤
          ∑ k ∈ Finset.range rc.2.length,
            ((wInp.prep.cJSub rc).deg k : ℝ) / impl.decompose.φ_lb wInp.prep.J0_strip.m :=
      Finset.sum_le_sum fun k hk => hcw_term k (Finset.mem_range.mp hk)
    have hsum_deg : ∑ k ∈ Finset.range rc.2.length, ((wInp.prep.cJSub rc).deg k : ℝ) =
        2 * ((wInp.prep.cJSub rc).m : ℝ) := by
      have hvol := vol_verts_eq_two_mul_m hcprops.2.2.2.2.2.2.2
      have hn : (wInp.prep.cJSub rc).n = rc.2.length := hcprops.2.2.2.2.2.2.1
      have hnat : ∑ k ∈ Finset.range rc.2.length, (wInp.prep.cJSub rc).deg k =
          2 * (wInp.prep.cJSub rc).m := by
        rw [← hvol, ← hn]; rfl
      exact_mod_cast hnat
    have hsum_div :
        (∑ k ∈ Finset.range rc.2.length,
            ((wInp.prep.cJSub rc).deg k : ℝ) / impl.decompose.φ_lb wInp.prep.J0_strip.m) =
          2 * ((wInp.prep.cJSub rc).m : ℝ) / impl.decompose.φ_lb wInp.prep.J0_strip.m := by
      rw [← Finset.sum_div, hsum_deg]
    rw [hsum_cw, ← hsum_div]
    exact hsum_deg_le
  have hsum_m : (List.map (fun rc => (wInp.prep.cJSub rc).m) wInp.prep.rawComps).sum ≤
      wInp.prep.J0_strip.m := by
    have hsz := (PrepInput.size_bounds hv).2.2.2.1
    omega
  have hsum_all : ∀ (l : List (ℕ × List ℕ)),
      (∀ rc ∈ l, ((wInp.compWeights rc).sum : ℝ) ≤
        2 * ((wInp.prep.cJSub rc).m : ℝ) / impl.decompose.φ_lb wInp.prep.J0_strip.m) →
      ((l.map fun rc => (wInp.compWeights rc).sum).sum : ℝ) ≤
        2 * ((l.map fun rc => (wInp.prep.cJSub rc).m).sum : ℝ) /
          impl.decompose.φ_lb wInp.prep.J0_strip.m := by
    intro l hl
    induction l with
    | nil => simp
    | cons r rs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      have h1 := hl r List.mem_cons_self
      have h2 := ih fun r' hr' => hl r' (List.mem_cons_of_mem r hr')
      have hadd : 2 * ((wInp.prep.cJSub r).m : ℝ) / impl.decompose.φ_lb wInp.prep.J0_strip.m +
          2 * ((rs.map fun rc => (wInp.prep.cJSub rc).m).sum : ℝ) /
            impl.decompose.φ_lb wInp.prep.J0_strip.m =
          2 * (((wInp.prep.cJSub r).m : ℝ) +
            ((rs.map fun rc => (wInp.prep.cJSub rc).m).sum : ℝ)) /
            impl.decompose.φ_lb wInp.prep.J0_strip.m := by ring
      linarith [h1, h2, hadd]
  have hall_mem : ∀ rc ∈ wInp.prep.rawComps,
      ((wInp.compWeights rc).sum : ℝ) ≤
        2 * ((wInp.prep.cJSub rc).m : ℝ) / impl.decompose.φ_lb wInp.prep.J0_strip.m := by
    intro rc hrc
    obtain ⟨ci, hci, rfl⟩ := List.mem_iff_getElem.mp hrc
    exact hstep ci hci
  have htot := hsum_all wInp.prep.rawComps hall_mem
  have hm_cast : ((wInp.prep.rawComps.map fun rc => (wInp.prep.cJSub rc).m).sum : ℝ) ≤
      (wInp.prep.J0_strip.m : ℝ) := by exact_mod_cast hsum_m
  have hpos_lb := impl.decompose.hφ_lb_pos wInp.prep.J0_strip.m
  have hmono : 2 * ((wInp.prep.rawComps.map fun rc => (wInp.prep.cJSub rc).m).sum : ℝ) /
        impl.decompose.φ_lb wInp.prep.J0_strip.m ≤
      2 * (wInp.prep.J0_strip.m : ℝ) / impl.decompose.φ_lb wInp.prep.J0_strip.m :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm_cast (by positivity)) hpos_lb.le
  exact le_trans htot hmono

end MinCostFlow.Spanner
