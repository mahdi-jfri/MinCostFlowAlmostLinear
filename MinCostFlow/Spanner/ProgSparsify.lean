module

public import MinCostFlow.Spanner.ProgSparsifyCore
public import MinCostFlow.Spanner.ProgSparsifyOut
public import MinCostFlow.Spanner.ProgSparsifyProps
public import MinCostFlow.Spanner.ProgSparsifyWord

@[expose] public section

/-!
# Top-Level Word-RAM `Sparsify` Procedure

Chains `sparsifyCorePrefix` (Tasks 1, 2, 3) with `sparsifyOutBody` (`flatEdges`, `dedupList`,
`subgraph`, `posTable`, `mapEmb`, `composeEmb`) to produce the final sparsifier `J̃`, kept-edge
list `kept`, and composed embedding `embJJtilde`, with the 3-word output header
`[pJtilde, pKept, pEmb]` stored at `[inp.h, inp.h + 3)` and returning the new heap end `retHeap`.

The body `sparsifyBody` contains no input-dependent constants (`mMax`, `m`, `k`, `φ`); it loads
`wH`, `bAddr`, and `γExp` from the Task 1 output header in memory. The main result is
`sparsify_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-! ### Program body -/

/-- Tail of `Sparsify` after `sparsifyCorePrefix`: reads `wH = mem[h+5]`, `bAddr = mem[wH+13]`,
`γExp = mem[wH+8]`, computes `E_WJ = v1 + 32` and `E_JW = v2 + 32`, calls `fout`, and returns the
new heap end. Expects `r1 = jAddr, r3 = h, r4 = v1, r5 = v2, r6 = v3`. -/
def sparsifyTailBody (fout : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 3) (.const 5))) ;;
  .assign 8 (.load (.bin .add (.reg 7) (.const 13))) ;;
  .assign 9 (.load (.bin .add (.reg 7) (.const 8))) ;;
  .assign 10 (.bin .add (.reg 4) (.const 32)) ;;
  .assign 11 (.bin .add (.reg 5) (.const 32)) ;;
  .call 12 fout [.reg 1, .reg 8, .reg 10, .reg 11, .reg 9, .reg 3, .reg 6] ;;
  .ret (.reg 12)

/-- Top-level `Sparsify` procedure body at `args = [hAddr, jAddr, embJHAddr, h]`. -/
def sparsifyBody (t1 t2 t3 fout : ℕ) : Stmt :=
  sparsifyCorePrefix t1 t2 t3 ;; sparsifyTailBody fout

theorem sparsifyBody_noRand (t1 t2 t3 fout : ℕ) : (sparsifyBody t1 t2 t3 fout).NoRand := by
  simp [sparsifyBody, sparsifyCorePrefix_noRand, sparsifyTailBody, Stmt.NoRand]

/-! ### Space, word-width, cost, and contract -/

/-- Worst-case final heap end after Tasks 1, 2, 3 and the output stage. -/
noncomputable def sparsifyMaxHeapEnd (impl : SpannerToolImpl) (inp : Task1Input) : ℕ :=
  Task3Input.maxHeapEnd impl (inp.toT3 0) +
    Task2Input.maxHeapEnd impl (inp.toT2 0) +
    inp.maxHeapEnd impl +
    sparsifyOutSpace (Task1Input.mwCap impl inp.J) inp.J.m (Task2Input.gammaExpCap impl inp.J)

/-- Word-width condition for full `Sparsify` (`sparsifyCoreWordOK` plus room for the output
stage). -/
def SparsifyWordOK (impl : SpannerToolImpl) (inp : Task1Input) (w : ℕ) : Prop :=
  SparsifyCoreWordOK impl inp w ∧ sparsifyMaxHeapEnd impl inp < 2 ^ w

/-- Worst-case Word-RAM cost bound for `sparsifyBody`. -/
noncomputable def sparsifyTotalCost (impl : SpannerToolImpl) (inp : Task1Input)
    (mem : ℕ → ℕ) : ℕ :=
  sparsifyCoreCost impl inp mem +
    sparsifyOutCost (Task1Input.mwCap impl inp.J) inp.J.m (Task2Input.gammaExpCap impl inp.J) + 100

/-- Full postcondition of `sparsifyBody`: Theorem 8.1 properties in property form together with
the relocated output layout `[pJtilde, pKept, pEmb]` at `[inp.h, inp.h + 3)`. -/
def SparsifyPost (impl : SpannerToolImpl) (inp : Task1Input)
    (mem mem' : ℕ → ℕ) (retHeap : ℕ) : Prop :=
  ∃ (wd : WitnessData) (embWJ embJW : ℕ → Walk) (η₁ η₂ : ℕ),
    let kept := (flatEdges embWJ wd.W.m).dedup
    let Jtilde := subgraphOf inp.J kept
    let embWJtilde : ℕ → Walk := fun eW => (embWJ eW).mapEdges kept.idxOf
    let embJHtilde := restrictEmb inp.embJH kept
    let embJJtilde := compose wd.W embWJtilde embJW
    η₁ ≤ eta1Bound wd inp.J ∧ η₂ ≤ eta2Bound inp.J ∧
    IsEmbedding wd.W inp.J embWJ ∧ IsEmbedding inp.J wd.W embJW ∧
    impl.decompose.φ_lb (stripLoops inp.J).m ≤ wd.φ_dec ∧
    wd.c_deg = 2 * (impl.constructExpander.c_deg_int : ℝ) ∧
    wd.φ_Const = impl.constructExpander.φ_Const ∧
    wd.J0_strip = stripLoops inp.J ∧
    wd.M_W ≤ Task1Input.mwCap impl inp.J ∧
    wd.W.m ≤ Task1Input.mwCap impl inp.J ∧
    (wd.decomp.ℓ : ℝ) ≤ impl.decompose.c_ℓ * ((Nat.log 2 ((stripLoops inp.J).m + 2) : ℝ) + 1) ∧
    (wd.W.m : ℝ) ≤ (inp.J.n : ℝ) + (wd.decomp.ℓ : ℝ) * wd.c_deg * (inp.J.n : ℝ) / wd.φ_dec ∧
    wd.φ_ds = min (impl.pathDS.params.φ_out (roundPhi wd.φ_dec) (stripLoops inp.J).m)
      (impl.pathDS.params.φ_out (roundPhi wd.φ_Const) wd.M_W) ∧
    wd.γ_ExpPath = max (impl.pathDS.params.γ_ExpPath (roundPhi wd.φ_dec) (stripLoops inp.J).m)
      (impl.pathDS.params.γ_ExpPath (roundPhi wd.φ_Const) wd.M_W) ∧
    wd.γ_del = max (impl.pathDS.params.γ_del (roundPhi wd.φ_dec) (stripLoops inp.J).m)
      (impl.pathDS.params.γ_del (roundPhi wd.φ_Const) wd.M_W) ∧
    wd.τ₁ = 2 * wd.γ_ExpPath * (length inp.J inp.embJH : ℝ) * wd.γ_del *
      (vcong inp.J inp.H' (fun _ => 1) inp.embJH + (maxDeg inp.J : ℝ)) / wd.φ_ds ∧
    wd.τ₂ = wd.γ_ExpPath * wd.γ_del / wd.φ_ds ∧
    (∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK tools inp.H' inp.J inp.embJH wd) ∧
    kept.Nodup ∧
    (∀ j ∈ kept, j < inp.J.m) ∧
    Jtilde.n = inp.J.n ∧
    Jtilde.m = kept.length ∧
    Jtilde.IsValid ∧
    IsEmbedding wd.W Jtilde embWJtilde ∧
    IsEmbedding Jtilde inp.H' embJHtilde ∧
    IsEmbedding inp.J Jtilde embJJtilde ∧
    vcong inp.J inp.H' (fun _ => 1) (compose Jtilde embJHtilde embJJtilde) ≤
      (((η₁ : ℝ) + 1 / 2) * ((η₂ : ℝ) + 1 / 2)) * wd.τ₁ * wd.τ₂ ∧
    vcong inp.J inp.H' (fun _ => 1) (compose Jtilde embJHtilde embJJtilde) ≤
      (((eta1Bound wd inp.J : ℝ) + 1 / 2) * ((eta2Bound inp.J : ℝ) + 1 / 2)) * wd.τ₁ * wd.τ₂ ∧
    (length inp.J embJJtilde : ℝ) ≤ wd.γ_ExpPath ^ 2 ∧
    (length inp.J (compose Jtilde embJHtilde embJJtilde) : ℝ) ≤
      wd.γ_ExpPath ^ 2 * (length inp.J inp.embJH : ℝ) ∧
    (Jtilde.m : ℝ) ≤ (wd.W.m : ℝ) * wd.γ_ExpPath ∧
    inp.h + 3 ≤ retHeap ∧ retHeap ≤ sparsifyMaxHeapEnd impl inp ∧
    ZeroFrom mem' retHeap ∧
    (∀ x < inp.h, mem' x = mem x) ∧
    let pJtilde := mem' inp.h
    let pKept := mem' (inp.h + 1)
    let pEmb := mem' (inp.h + 2)
    inp.h ≤ pJtilde ∧ inp.h ≤ pKept ∧ inp.h ≤ pEmb ∧
    pJtilde + Jtilde.encode.length ≤ retHeap ∧
    pKept + 1 + kept.length ≤ retHeap ∧
    pEmb + inp.J.m ≤ retHeap ∧
    GraphAt mem' pJtilde Jtilde ∧
    ListAt mem' pKept (kept.length :: kept) ∧
    EmbAt mem' pEmb inp.J.m embJJtilde ∧
    EmbBounded mem' pEmb inp.J.m embJJtilde retHeap

section Contract
open Classical

/-- Word-RAM contract for `sparsifyBody`. -/
noncomputable def sparsifyContract (impl : SpannerToolImpl) (w : ℕ) : Contract where
  pre args mem :=
    ∃ inp : Task1Input,
      args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] ∧
      inp.Valid impl mem w ∧
      SparsifyWordOK impl inp w
  post args mem v mem' :=
    ∀ inp : Task1Input,
      args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] →
      inp.Valid impl mem w →
      SparsifyWordOK impl inp w →
      SparsifyPost impl inp mem mem' v
  cost args mem :=
    if h : ∃ inp : Task1Input,
        args = [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] ∧
        inp.Valid impl mem w ∧ SparsifyWordOK impl inp w
    then
      let inp := Classical.choose h
      sparsifyTotalCost impl inp mem
    else 0

end Contract

/-! ### Monotonicity and bridge lemmas -/

lemma sparsifyOutSpace_mono {mW₁ mW₂ mJ γ₁ γ₂ : ℕ} (hm : mW₁ ≤ mW₂) (hγ : γ₁ ≤ γ₂) :
    sparsifyOutSpace mW₁ mJ γ₁ ≤ sparsifyOutSpace mW₂ mJ γ₂ := by
  unfold sparsifyOutSpace; dsimp only
  have hL : 2 * γ₁ + 3 ≤ 2 * γ₂ + 3 := by omega
  have h1 : mW₁ * γ₁ ≤ mW₂ * γ₂ := Nat.mul_le_mul hm hγ
  have h2 : mW₁ * (2 * γ₁ + 3) ≤ mW₂ * (2 * γ₂ + 3) := Nat.mul_le_mul hm hL
  have h3 : γ₁ * (2 * γ₁ + 3) ≤ γ₂ * (2 * γ₂ + 3) := Nat.mul_le_mul hγ hL
  have h4 : mJ * (2 + 2 * (γ₁ * (2 * γ₁ + 3))) ≤ mJ * (2 + 2 * (γ₂ * (2 * γ₂ + 3))) :=
    Nat.mul_le_mul_left mJ (by omega)
  omega

lemma sparsifyOutCost_mono {mW₁ mW₂ mJ γ₁ γ₂ : ℕ} (hm : mW₁ ≤ mW₂) (hγ : γ₁ ≤ γ₂) :
    sparsifyOutCost mW₁ mJ γ₁ ≤ sparsifyOutCost mW₂ mJ γ₂ := by
  unfold sparsifyOutCost; dsimp only
  have h1 : mW₁ * (20 * γ₁ + 120) ≤ mW₂ * (20 * γ₂ + 120) := Nat.mul_le_mul hm (by omega)
  have h2 : 115 * (mW₁ * γ₁) ≤ 115 * (mW₂ * γ₂) := Nat.mul_le_mul_left 115 (Nat.mul_le_mul hm hγ)
  have h3 : mW₁ * (50 * (2 * γ₁ + 3) + 200) ≤ mW₂ * (50 * (2 * γ₂ + 3) + 200) :=
    Nat.mul_le_mul hm (by omega)
  have h4 : γ₁ * (120 * (2 * γ₁ + 3) + 620) ≤ γ₂ * (120 * (2 * γ₂ + 3) + 620) :=
    Nat.mul_le_mul hγ (by omega)
  have h5 : mJ * (γ₁ * (120 * (2 * γ₁ + 3) + 620) + 300) ≤
      mJ * (γ₂ * (120 * (2 * γ₂ + 3) + 620) + 300) :=
    Nat.mul_le_mul_left mJ (Nat.add_le_add_right h4 300)
  omega

private lemma length_le_of_cast_le {G : Graph} {emb : ℕ → Walk} {γ : ℕ}
    (h : (length G emb : ℝ) ≤ (γ : ℝ)) : ∀ e < G.m, (emb e).edges.length ≤ γ :=
  fun e he => le_trans (edges_length_le_length emb he) (by exact_mod_cast h)

private lemma toT3_maxHeapEnd_eq (impl : SpannerToolImpl) (inp : Task1Input) (v2 : ℕ) :
    Task3Input.maxHeapEnd impl (inp.toT3 v2) = Task3Input.maxHeapEnd impl (inp.toT3 0) + v2 := by
  simp only [Task3Input.maxHeapEnd, Task3Input.staticEndCap, Task1Input.toT3]
  omega

/-- Extract all inputs and preconditions for `sparsifyOutBody` from a completed core run. -/
private lemma sparsifyCore_to_outPre {impl : SpannerToolImpl} {inp : Task1Input}
    {mem mem1 mem2 mem3 : ℕ → ℕ} {v1 v2 v3 w : ℕ}
    (hv : inp.Valid impl mem w) (hwok : SparsifyWordOK impl inp w)
    (hT1 : Task1OutAt impl inp.jAddr inp.h inp.H' inp.J inp.embJH mem mem1 v1 w)
    (hcap1 : v1 ≤ inp.maxHeapEnd impl)
    (hT2 : Task2OutAt impl (inp.toT2 v1) mem1 mem2 v2 w)
    (hT3 : Task3OutAt impl (inp.toT3 v2) mem2 mem3 v3 w) :
    ∃ (wd : WitnessData) (embWJ embJW : ℕ → Walk) (η₁ η₂ wH bAddr γExp : ℕ),
      mem3 (inp.h + 5) = wH ∧ mem3 (wH + 13) = bAddr ∧ mem3 (wH + 8) = γExp ∧
      wH + 13 < v1 ∧ inp.h + 9 ≤ v1 ∧ v1 + 32 ≤ v2 ∧ v2 + 32 ≤ v3 ∧
      wd.W.m ≤ Task1Input.mwCap impl inp.J ∧
      γExp ≤ Task2Input.gammaExpCap impl inp.J ∧
      v3 + sparsifyOutSpace wd.W.m inp.J.m γExp ≤ sparsifyMaxHeapEnd impl inp ∧
      SparsifyOutPre mem3 inp.jAddr bAddr (v1 + 32) (v2 + 32) γExp inp.h v3 inp.J wd.W embWJ embJW w ∧
      η₁ ≤ eta1Bound wd inp.J ∧ η₂ ≤ eta2Bound inp.J ∧
      impl.decompose.φ_lb (stripLoops inp.J).m ≤ wd.φ_dec ∧
      wd.c_deg = 2 * (impl.constructExpander.c_deg_int : ℝ) ∧
      wd.φ_Const = impl.constructExpander.φ_Const ∧
      wd.J0_strip = stripLoops inp.J ∧
      wd.M_W ≤ Task1Input.mwCap impl inp.J ∧
      (wd.decomp.ℓ : ℝ) ≤ impl.decompose.c_ℓ * ((Nat.log 2 ((stripLoops inp.J).m + 2) : ℝ) + 1) ∧
      (wd.W.m : ℝ) ≤ (inp.J.n : ℝ) + (wd.decomp.ℓ : ℝ) * wd.c_deg * (inp.J.n : ℝ) / wd.φ_dec ∧
      wd.φ_ds = min (impl.pathDS.params.φ_out (roundPhi wd.φ_dec) (stripLoops inp.J).m)
        (impl.pathDS.params.φ_out (roundPhi wd.φ_Const) wd.M_W) ∧
      wd.γ_ExpPath = max (impl.pathDS.params.γ_ExpPath (roundPhi wd.φ_dec) (stripLoops inp.J).m)
        (impl.pathDS.params.γ_ExpPath (roundPhi wd.φ_Const) wd.M_W) ∧
      wd.γ_del = max (impl.pathDS.params.γ_del (roundPhi wd.φ_dec) (stripLoops inp.J).m)
        (impl.pathDS.params.γ_del (roundPhi wd.φ_Const) wd.M_W) ∧
      wd.τ₁ = 2 * wd.γ_ExpPath * (length inp.J inp.embJH : ℝ) * wd.γ_del *
        (vcong inp.J inp.H' (fun _ => 1) inp.embJH + (maxDeg inp.J : ℝ)) / wd.φ_ds ∧
      wd.τ₂ = wd.γ_ExpPath * wd.γ_del / wd.φ_ds ∧
      (∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
        WitnessOK tools inp.H' inp.J inp.embJH wd) ∧
      (∀ x < inp.h, mem3 x = mem x) ∧
      (let kept := (flatEdges embWJ wd.W.m).dedup
       let Jtilde := subgraphOf inp.J kept
       let embWJtilde : ℕ → Walk := fun eW => (embWJ eW).mapEdges kept.idxOf
       let embJHtilde := restrictEmb inp.embJH kept
       let embJJtilde := compose wd.W embWJtilde embJW
       kept.Nodup ∧ (∀ j ∈ kept, j < inp.J.m) ∧
       Jtilde.n = inp.J.n ∧ Jtilde.m = kept.length ∧ Jtilde.IsValid ∧
       IsEmbedding wd.W Jtilde embWJtilde ∧ IsEmbedding Jtilde inp.H' embJHtilde ∧
       IsEmbedding inp.J Jtilde embJJtilde ∧
       vcong inp.J inp.H' (fun _ => 1) (compose Jtilde embJHtilde embJJtilde) ≤
         (((η₁ : ℝ) + 1 / 2) * ((η₂ : ℝ) + 1 / 2)) * wd.τ₁ * wd.τ₂ ∧
       vcong inp.J inp.H' (fun _ => 1) (compose Jtilde embJHtilde embJJtilde) ≤
         (((eta1Bound wd inp.J : ℝ) + 1 / 2) * ((eta2Bound inp.J : ℝ) + 1 / 2)) * wd.τ₁ * wd.τ₂ ∧
       (length inp.J embJJtilde : ℝ) ≤ wd.γ_ExpPath ^ 2 ∧
       (length inp.J (compose Jtilde embJHtilde embJJtilde) : ℝ) ≤
         wd.γ_ExpPath ^ 2 * (length inp.J inp.embJH : ℝ) ∧
       (Jtilde.m : ℝ) ≤ (wd.W.m : ℝ) * wd.γ_ExpPath) := by
  obtain ⟨_, _, hJv, hgJ, hEmbJH, _, _, _, hJle, _, hW1⟩ := hv
  have hs1 : inp.h + 9 ≤ v1 := task1OutAt_slots_lt hT1
  have hT1c := hT1
  obtain ⟨wInp1, WSubs1, _, _, hJ1, _, _, _, _, _, hcℓ1, hagr1, _, _, _, _, _, _, hdec1, _, hs5_1, _,
    _, _, _, _, hSV1, _, hφ_lb1, _, hO1_all, _, _⟩ := hT1c
  have hT2c := hT2
  obtain ⟨wInp2, WSubs2, η₁, embWJ, _, _, _, _, _, _, hH2, hE2, hJ2, _, hSV2, hWS2, hOK2, hagr2,
    _, hv12, hv2cap, _, _, _, _, _, _, _, _, _, _, _, _, hEmbWJ_at, hEmbWJ_bd, _, hη1, hEmbWJ,
    hvc2, _, hlen2, _, _, _, _, _, _, hs5_2, hO2, hdec2, hhe2⟩ := hT2c
  have hT3c := hT3
  obtain ⟨hagr3, hzf3, hv23, hv3cap, wInp3, WSubs3, embJW, η₂, _, _, _, hH3, hE3, hJ3, _,
    ⟨_, memT1, v1', hagrT, _, hT1', hs5_3, _, _, _, hO3⟩, _, _, _, _, _, _, _, _, _,
    hEmbJW_at, hEmbJW_bd, hEmbJW3, hη2, hec3, _, _, hlen3, _, _, _⟩ := hT3c
  have hs5_2' : mem1 (inp.h + 5) = wInp2.h := hs5_2
  have hs5_3' : memT1 (inp.h + 5) = wInp3.h := hs5_3
  have hagr2' : ∀ x < v1, mem2 x = mem1 x := hagr2
  have hagr3' : ∀ x < v2, mem3 x = mem2 x := hagr3
  have hv12' : v1 + 32 ≤ v2 := hv12
  have hv23' : v2 + 32 ≤ v3 := hv23
  have hagr3_h : ∀ x < inp.h, mem3 x = mem x := fun x hx =>
    (hagr3' x (by omega)).trans ((hagr2' x (by omega)).trans (hagr1 x hx))
  have hagr3_v1 : ∀ x < v1, mem3 x = mem1 x := fun x hx =>
    (hagr3' x (by omega)).trans (hagr2' x hx)
  have hcell : ∀ x, x < v1 → x < v1' → memT1 x = mem1 x := fun x h1 h2 => by
    rw [← hagrT x h2, hagr2' x h1]
  have hs1' : inp.h + 9 ≤ v1' := task1OutAt_slots_lt hT1'
  have hH23 : wInp2.h = wInp3.h := by
    rw [← hs5_2', ← hs5_3', hcell (inp.h + 5) (by omega) (by omega)]
  have hH12 : wInp1.h = wInp2.h := by rw [← hs5_1, hs5_2']
  obtain ⟨hb2, hG2, hr2⟩ := outputAt_W_at hO2
  obtain ⟨hb3, hG3, hr3⟩ := outputAt_W_at hO3
  rw [← hH23] at hb3 hG3 hr3
  have hA23 : memT1 (wInp2.h + 13) = mem1 (wInp2.h + 13) := hcell _ hb2 hb3
  rw [hA23] at hG3 hr3
  have hG2_m2 := GraphAt.of_agree_below hG2 hr2 hagr2'
  have hG3_m2 := GraphAt.of_agree_below hG3 hr3 hagrT
  have hWeq : (wInp2.mkWitnessData impl.constructExpander impl.pathDS.params WSubs2).W =
      (wInp3.mkWitnessData impl.constructExpander impl.pathDS.params WSubs3).W :=
    graphAt_inj hG2_m2 hG3_m2
  -- Extract φ_lb and decomposition bounds by matching wInp2 and wInp1 via cells `wH + 17..19`.
  have hO1 := hO1_all mem
  have hp1 := outputAt_prep_cells hO1
  have hp2 := outputAt_prep_cells hO2
  rw [hH12] at hp1
  have hpn12 : wInp1.prep.phiNum_dec = wInp2.prep.phiNum_dec := by rw [← hp1.2.1, hp2.2.1]
  have hpd12 : wInp1.prep.phiDen_dec = wInp2.prep.phiDen_dec := by rw [← hp1.2.2.1, hp2.2.2.1]
  have hJ2' : wInp2.prep.J = inp.J := hJ2
  have hH2' : wInp2.H' = inp.H' := hH2
  have hJ0_1 : wInp1.prep.J0_strip = stripLoops inp.J := by rw [hSV1.2.2.1, hJ1]
  have hJ0_2 : wInp2.prep.J0_strip = stripLoops inp.J := by rw [hSV2.2.2.1, hJ2']
  have hφ_lb2 : impl.decompose.φ_lb wInp2.prep.J0_strip.m ≤
      (wInp2.prep.phiNum_dec : ℝ) / wInp2.prep.phiDen_dec := by
    rw [hJ0_2, ← hJ0_1, ← hpn12, ← hpd12]; exact hφ_lb1
  set wd := wInp2.mkWitnessData impl.constructExpander impl.pathDS.params WSubs2
  set γExp := wInp2.γExpInt impl.constructExpander impl.pathDS.params
  set bAddr := mem1 (wInp2.h + 13)
  have hscal := WitnessCoreInput.mkWitnessData_scalars wInp2 impl.constructExpander impl.pathDS.params WSubs2 hSV2
  have hγ_eq : wd.γ_ExpPath = (γExp : ℝ) := hscal.2.2.1
  have hcap_scal := task2_scalars_le_caps (impl := impl) hSV2 hφ_lb2
  have hγ_cap : γExp ≤ Task2Input.gammaExpCap impl inp.J := by simpa [hJ2', γExp] using hcap_scal.1
  have hmw_cap : wInp2.mwInt impl.constructExpander ≤ Task1Input.mwCap impl inp.J := by
    simpa [hJ2'] using task2_mw_le_cap (impl := impl) hSV2 hφ_lb2
  have hOK2_loc := hOK2 (exists_localSpannerTools 0 0).some
  have hOK2_w : WitnessOK (exists_localSpannerTools 0 0).some wInp2.H' wInp2.prep.J wInp2.embJH wd := by
    rw [hH2', hJ2']
    rcases hOK2_loc with ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
      f18, f19, f20, f21, f22⟩
    exact ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17,
      f18, f19, f20, f21, f22⟩
  have hWm_cap : wd.W.m ≤ Task1Input.mwCap impl inp.J := by
    simpa [hJ2', wd] using task2_wd_W_m_le_mwCap (impl := impl) hSV2 hOK2_w hWS2 hφ_lb2
  have hv2_le : v2 ≤ Task2Input.maxHeapEnd impl (inp.toT2 0) + inp.maxHeapEnd impl := by
    rw [toT2_maxHeapEnd] at hv2cap; omega
  have hv3_le : v3 ≤ Task3Input.maxHeapEnd impl (inp.toT3 0) +
      Task2Input.maxHeapEnd impl (inp.toT2 0) + inp.maxHeapEnd impl := by
    rw [toT3_maxHeapEnd_eq] at hv3cap; omega
  have hsp_le : v3 + sparsifyOutSpace wd.W.m inp.J.m γExp ≤ sparsifyMaxHeapEnd impl inp := by
    have hm := sparsifyOutSpace_mono (mJ := inp.J.m) hWm_cap hγ_cap
    unfold sparsifyMaxHeapEnd; omega
  have hEmbJW : IsEmbedding inp.J wd.W embJW := hWeq ▸ hEmbJW3
  have hW_valid : wd.W.IsValid := hOK2_loc.W_valid
  have hWn : wd.W.n = inp.J.n := hOK2_loc.W_n
  have hJn_w : inp.J.n < 2 ^ w := by
    have h2 : inp.h + 6 + 3 + inp.J.n + 2 * inp.H'.n ≤ inp.maxHeapEnd impl := by
      unfold Task1Input.maxHeapEnd Task1Input.coreHMax Task1Input.prepHMax Task1Input.decAddr
        Task1Input.nlAddr Task1Input.j0Addr; dsimp only; omega
    have h3 : inp.maxHeapEnd impl ≤ sparsifyMaxHeapEnd impl inp := by
      unfold sparsifyMaxHeapEnd; omega
    have := hwok.2; omega
  -- Memory reads at `mem3`.
  have h5_3 : mem3 (inp.h + 5) = wInp2.h := by rw [hagr3_v1 _ (by omega), hs5_2']
  have h13_3 : mem3 (wInp2.h + 13) = bAddr := hagr3_v1 _ hb2
  have h8_3 : mem3 (wInp2.h + 8) = γExp := by
    rw [hagr3_v1 _ (by omega)]; exact hO2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- Length bounds in `ℕ` for `embWJ` and `embJW`.
  have hLenWJ : ∀ e < wd.W.m, (embWJ e).edges.length ≤ γExp :=
    length_le_of_cast_le (hγ_eq ▸ hlen2)
  have hpar23 := mkWitnessData_params_congr (ce := impl.constructExpander)
    (pds := impl.pathDS.params) (S₁ := WSubs2) (S₂ := WSubs3)
    (by have hp3 := outputAt_prep_cells hO3; rw [← hH23] at hp3
        rw [← hp2.2.1, ← hp3.2.1, hcell _ (by omega) (by omega)])
    (by have hp3 := outputAt_prep_cells hO3; rw [← hH23] at hp3
        rw [← hp2.2.2.1, ← hp3.2.2.1, hcell _ (by omega) (by omega)])
    (by have hp3 := outputAt_prep_cells hO3; rw [← hH23] at hp3
        rw [← hp2.2.2.2, ← hp3.2.2.2, hcell _ (by omega) (by omega)])
    (hJ2.trans hJ3.symm) (hH2.trans hH3.symm)
    (fun e he => by
      have he' : e < inp.J.m := by have h' : wInp2.prep.J = inp.J := hJ2; rw [← h']; exact he
      exact (hE2 e he').trans (hE3 e he').symm)
  have hLenJW : ∀ e < inp.J.m, (embJW e).edges.length ≤ γExp :=
    length_le_of_cast_le (by rw [← hγ_eq, hpar23.2.2.2.1]; exact hlen3)
  have hEmbWJ_3 : EmbAt mem3 (v1 + 32) wd.W.m embWJ ∧ EmbBounded mem3 (v1 + 32) wd.W.m embWJ v2 :=
    embAt_preserve hEmbWJ_at hEmbWJ_bd hagr3'
  have hr2' : bAddr + wd.W.encode.length ≤ v1 := hr2
  have hOutPre : SparsifyOutPre mem3 inp.jAddr bAddr (v1 + 32) (v2 + 32) γExp inp.h v3
      inp.J wd.W embWJ embJW w := by
    refine ⟨GraphAt.of_agree_below hgJ hJle hagr3_h,
      GraphAt.of_agree_below hG2 hr2 hagr3_v1,
      by omega, by omega,
      hEmbWJ_3.1, ⟨by have := hEmbWJ_3.2.1; omega, fun e he => by have := hEmbWJ_3.2.2 e he; omega⟩,
      hEmbJW_at, hEmbJW_bd, hEmbWJ, hEmbJW, hW_valid, hJn_w, hWn, hLenWJ, hLenJW,
      by omega, hzf3, lt_of_le_of_lt hsp_le hwok.2, ?_⟩
    have : 3 ≤ sparsifyOutSpace wd.W.m inp.J.m γExp := by unfold sparsifyOutSpace; dsimp only; omega
    have := hwok.2; omega
  -- Assemble Theorem 8.1 properties via `theorem_8_1_core`.
  have hd2 := outputAt_wW_at hO2
  have hd3 := outputAt_wW_at hO3
  rw [← hH23, hA23] at hd3
  have hwW23 : ∀ eW < wd.W.m, wd.wW eW =
      (wInp3.mkWitnessData impl.constructExpander impl.pathDS.params WSubs3).wW eW := by
    intro eW heW
    have heW3 : eW < (wInp3.mkWitnessData impl.constructExpander impl.pathDS.params WSubs3).W.m :=
      hWeq ▸ heW
    have e2 := hd2.2.2.2 eW heW
    have e3 := hd3.2.2.2 eW heW3
    rw [← hWeq] at e3
    have hden : (wInp2.prep.phiDen_dec : ℝ) = (wInp3.prep.phiDen_dec : ℝ) := by
      rw [← hd2.2.1, ← hd3.2.1, hcell _ hd2.1 hd3.1]
    have hn2 : bAddr + (2 + 2 * wd.W.m) + wd.W.m ≤ v1 := hd2.2.2.1
    have hn3 : bAddr + (2 + 2 * wd.W.m) + wd.W.m ≤ v1' := by
      have := hd3.2.2.1; rw [← hWeq] at this; exact this
    have hx := hcell (bAddr + (2 + 2 * wd.W.m) + eW) (by omega) (by omega)
    rw [← e2, ← e3, hden, hx]
  have hec : econg inp.J wd.W (fun _ => 1) wd.wW embJW ≤ ((η₂ : ℝ) + 1 / 2) * wd.τ₂ := by
    refine econg_le_iff.mpr ⟨mul_nonneg (by positivity) hOK2_loc.τ₂_pos.le, fun eW heW => ?_⟩
    have h := hec3 eW (hWeq ▸ heW)
    unfold econgAt at h ⊢
    rw [hwW23 eW heW, hpar23.2.2.2.2.2.2]
    exact h
  have hprops := theorem_8_1_core inp.H' inp.J wd.W wd.wW inp.embJH embWJ embJW hWn hJv hEmbJH
    hEmbWJ hEmbJW
    (outputAt_wW_pos hO2 (by have := hSV2.2.2.2.2.2.2.2.2.1; have := hSV2.2.2.2.2.2.2.2.2.2.1; omega))
    (add_nonneg (Nat.cast_nonneg _) (by norm_num))
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num))
    (add_nonneg (Nat.cast_nonneg _) (by norm_num))
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num))
    (add_le_add (Nat.cast_le.mpr hη1) le_rfl)
    (add_le_add (Nat.cast_le.mpr hη2) le_rfl)
    hvc2 hec hlen2 (by rw [hpar23.2.2.2.1]; exact hlen3)
  -- `Decompose` bounds from `Task1OutAt` / `PrepInput.StaticValid`.
  have hdec_eq : wInp2.prep.decomp = wInp1.prep.decomp := by
    have hll : wInp2.prep.level.length = wInp1.prep.level.length := by
      rw [hSV2.2.2.2.2.2.2.2.1, hSV1.2.2.2.2.2.2.2.1, hJ0_2, hJ0_1]
    have hpe2 : wInp2.prep.h ≤ wInp2.prep.hEnd := by
      unfold PrepInput.hEnd PrepInput.hBlocksStart; omega
    have hreg2 := hSV2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have D2 : DecomposeOutAt mem1 wInp2.prep.decAddr wInp2.prep.d_ℓ wInp2.prep.phiNum_dec
        wInp2.prep.phiDen_dec wInp2.prep.level wInp2.prep.rawComps :=
      ListAt.of_agree_below hSV2.2.2.2.2.2.2.1 (h₀ := v1) (by omega) fun k hk => (hagr2' k hk).symm
    have D1 := hSV1.2.2.2.2.2.2.1
    have hdec2' : mem1 (inp.h + 3) = wInp2.prep.decAddr := hdec2
    have hda : wInp2.prep.decAddr = wInp1.prep.decAddr := hdec2'.symm.trans hdec1
    rw [hda] at D2
    obtain ⟨hℓ, -, -, hlvl, hcs⟩ := decomposeOutAt_inj D2 D1 hll
    unfold PrepInput.decomp
    rw [hℓ, hlvl, hcs]
  have hdp1 := hSV1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hℓ_le : (wd.decomp.ℓ : ℝ) ≤
      impl.decompose.c_ℓ * ((Nat.log 2 ((stripLoops inp.J).m + 2) : ℝ) + 1) := by
    show (wInp2.prep.decomp.ℓ : ℝ) ≤ _
    rw [hdec_eq, ← hcℓ1, ← hJ0_1]
    exact hdp1.1
  have hWm_n : (wd.W.m : ℝ) ≤ (inp.J.n : ℝ) + (wd.decomp.ℓ : ℝ) * wd.c_deg * (inp.J.n : ℝ) / wd.φ_dec := by
    simpa [hJ2', wd] using mkW_W_m_le_n hSV2 hOK2_w hWS2
  refine ⟨wd, embWJ, embJW, η₁, η₂, wInp2.h, bAddr, γExp,
    h5_3, h13_3, h8_3, by omega, hs1, hv12', hv23', hWm_cap, hγ_cap, hsp_le, hOutPre,
    hη1, hη2, by simpa [wd, WitnessCoreInput.mkWitnessData, hJ0_2] using hφ_lb2,
    rfl, rfl, hJ0_2, by change wInp2.mwInt impl.constructExpander ≤ _; exact hmw_cap, hℓ_le, hWm_n,
    ?_, ?_, ?_, ?_, ?_, hOK2, hagr3_h, hprops⟩
  · simp only [wd, WitnessCoreInput.mkWitnessData, hJ0_2]
  · simp only [wd, WitnessCoreInput.mkWitnessData, hJ0_2]
  · simp only [wd, WitnessCoreInput.mkWitnessData, hJ0_2]
  · have hE2' : ∀ e < inp.J.m, wInp2.embJH e = inp.embJH e := hE2
    have hlen_eq : length inp.J wInp2.embJH = length inp.J inp.embJH := by
      unfold length
      exact Finset.fold_congr fun e he => by rw [hE2' e (Finset.mem_range.mp he)]
    have hvc_eq : vcong inp.J inp.H' (fun _ => 1) wInp2.embJH =
        vcong inp.J inp.H' (fun _ => 1) inp.embJH := by
      unfold vcong
      refine Finset.fold_congr fun x _ => ?_
      unfold vcongAt
      rw [Finset.sum_filter, Finset.sum_filter]
      exact Finset.sum_congr rfl fun e he => by rw [hE2' e (Finset.mem_range.mp he)]
    simp only [wd, WitnessCoreInput.mkWitnessData, hJ2, hH2, Task1Input.toT2, hlen_eq, hvc_eq]
  · simp only [wd, WitnessCoreInput.mkWitnessData]

private lemma sparsifyTail_runs {w : ℕ} {p : Program} {impl : SpannerToolImpl} {fout : ℕ}
    (hfout : MeetsContract w p fout (sparsifyOutContract w))
    {inp : Task1Input} {mem mem1 mem2 : ℕ → ℕ} {v1 v2 v3 : ℕ} {st₁ : State} {ω : ℕ → Bool}
    (hwords : ∀ a ∈ [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h], a < 2 ^ w)
    (hv : inp.Valid impl mem w) (hwok : SparsifyWordOK impl inp w)
    (hr1 : st₁.regs 1 = inp.jAddr) (hr3 : st₁.regs 3 = inp.h)
    (hr4 : st₁.regs 4 = v1) (hr5 : st₁.regs 5 = v2) (hr6 : st₁.regs 6 = v3)
    (hT1 : Task1OutAt impl inp.jAddr inp.h inp.H' inp.J inp.embJH mem mem1 v1 w)
    (hcap1 : v1 ≤ inp.maxHeapEnd impl)
    (hT2 : Task2OutAt impl (inp.toT2 v1) mem1 mem2 v2 w)
    (hT3 : Task3OutAt impl (inp.toT3 v2) mem2 st₁.mem v3 w) :
    ∃ o st₂ c₂,
      Runs w p ω (sparsifyTailBody fout) st₁ o st₂ c₂ ∧
      SparsifyPost impl inp mem st₂.mem o.value ∧
      c₂ ≤ sparsifyOutCost (Task1Input.mwCap impl inp.J) inp.J.m
        (Task2Input.gammaExpCap impl inp.J) + 80 := by
  obtain ⟨wd, embWJ, embJW, η₁, η₂, wH, bAddr, γExp,
    h5, h13, h8, hwH_v1, hh_v1, hv12, hv23, hWm_cap, hγ_cap, hsp_le, hOutPre,
    hη1, hη2, hφ_lb, hcdeg, hφC, hJ0, hMW_cap, hℓ_le, hgm_le, hφds, hγE, hγD, hτ1, hτ2,
    hOK, hagr3_h, hprops⟩ := sparsifyCore_to_outPre hv hwok hT1 hcap1 hT2 hT3
  have hret_w : v3 + sparsifyOutSpace wd.W.m inp.J.m γExp < 2 ^ w := hOutPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hw1 : 1 < 2 ^ w := hOutPre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hw32 : 32 < 2 ^ w := by omega
  have hwJ : inp.jAddr < 2 ^ w := hwords inp.jAddr (by simp)
  have hwH0 : inp.h < 2 ^ w := hwords inp.h (by simp)
  have hWh0 : bAddr + wd.W.encode.length ≤ v3 := hOutPre.2.2.2.1
  have hγ_w : γExp < 2 ^ w := by
    have : 2 * γExp + 3 ≤ sparsifyOutSpace wd.W.m inp.J.m γExp := by
      unfold sparsifyOutSpace; dsimp only; omega
    omega
  have e7 : (Expr.load (.bin .add (.reg 3) (.const 5))).eval w st₁ = some wH :=
    ev_load' (ev_add (ev_reg hr3 hwH0) (ev_const (by omega : 5 < 2 ^ w)) (by omega)) h5
  let rg7 := Function.update st₁.regs 7 wH
  let rg8 := Function.update rg7 8 bAddr
  let rg9 := Function.update rg8 9 γExp
  let rg10 := Function.update rg9 10 (v1 + 32)
  let rg11 := Function.update rg10 11 (v2 + 32)
  have e8 : (Expr.load (.bin .add (.reg 7) (.const 13))).eval w ⟨st₁.mem, rg7, st₁.pos⟩ = some bAddr :=
    ev_load' (ev_add (ev_reg (by simp [rg7]) (by omega)) (ev_const (by omega : 13 < 2 ^ w)) (by omega)) h13
  have e9 : (Expr.load (.bin .add (.reg 7) (.const 8))).eval w ⟨st₁.mem, rg8, st₁.pos⟩ = some γExp :=
    ev_load' (ev_add (ev_reg (by simp [rg8, rg7]) (by omega)) (ev_const (by omega : 8 < 2 ^ w)) (by omega)) h8
  have e10 : (Expr.bin .add (.reg 4) (.const 32)).eval w ⟨st₁.mem, rg9, st₁.pos⟩ = some (v1 + 32) :=
    ev_add (ev_reg (by simp [rg9, rg8, rg7, hr4]) (by omega)) (ev_const hw32) (by omega)
  have e11 : (Expr.bin .add (.reg 5) (.const 32)).eval w ⟨st₁.mem, rg10, st₁.pos⟩ = some (v2 + 32) :=
    ev_add (ev_reg (by simp [rg10, rg9, rg8, rg7, hr5]) (by omega)) (ev_const hw32) (by omega)
  unfold sparsifyTailBody
  refine runs_start_le ?_
  refine runs_seq_assign_le e7 ?_
  refine runs_seq_assign_le e8 ?_
  dsimp only
  refine runs_seq_assign_le e9 ?_
  dsimp only
  refine runs_seq_assign_le e10 ?_
  dsimp only
  refine runs_seq_assign_le e11 ?_
  dsimp only
  refine runs_seq_call_le (vs := [inp.jAddr, bAddr, v1 + 32, v2 + 32, γExp, inp.h, v3]) hfout
    (by simp [evalArgs, Expr.eval, hr1, hr3, hr6])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨inp.jAddr, bAddr, v1 + 32, v2 + 32, γExp, inp.h, v3, inp.J, wd.W, embWJ, embJW, rfl, hOutPre⟩ ?_
  intro retHeap mem4 pos4 hpost4
  have hOut := hpost4 inp.jAddr bAddr (v1 + 32) (v2 + 32) γExp inp.h v3 inp.J wd.W embWJ embJW rfl hOutPre
  obtain ⟨h3r, _, hr_le, hZr, hpJ0, hpK0, hpE0, hpJ_r, hpK_r, hpE_r, hGsub, hkept, hEmbC, hBndC, hOutAgr⟩ := hOut
  have hret_max : retHeap ≤ sparsifyMaxHeapEnd impl inp := le_trans hr_le hsp_le
  have hret_w' : retHeap < 2 ^ w := lt_of_le_of_lt hret_max hwok.2
  have hagr4_h : ∀ x < inp.h, mem4 x = mem x := fun x hx =>
    (hOutAgr x (by omega) (by omega) (by omega) (by omega)).trans (hagr3_h x hx)
  have hPost : SparsifyPost impl inp mem mem4 retHeap := by
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ := hprops
    exact ⟨wd, embWJ, embJW, η₁, η₂, hη1, hη2, hOutPre.2.2.2.2.2.2.2.2.1, hOutPre.2.2.2.2.2.2.2.2.2.1,
      hφ_lb, hcdeg, hφC, hJ0, hMW_cap, hWm_cap, hℓ_le, hgm_le, hφds, hγE, hγD, hτ1, hτ2, hOK,
      p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13,
      h3r, hret_max, hZr, hagr4_h, by omega, by omega, by omega, hpJ_r, hpK_r, hpE_r,
      hGsub, hkept, hEmbC, hBndC⟩
  let rg12 := Function.update rg11 12 retHeap
  refine runs_ret_le (ev_reg (show rg12 12 = retHeap by simp [rg12]) hret_w') hPost ?_
  have hmW : st₁.mem (bAddr + 1) = wd.W.m := by
    simpa [GraphAt, Graph.encode] using hOutPre.2.1 1 (by simp [Graph.encode])
  have hmJ : st₁.mem (inp.jAddr + 1) = inp.J.m := by
    simpa [GraphAt, Graph.encode] using hOutPre.1 1 (by simp [Graph.encode])
  have hcost_mono := sparsifyOutCost_mono (mJ := inp.J.m) hWm_cap hγ_cap
  simp only [Expr.size, argsSize, sparsifyOutContract, List.getD_cons_succ, List.getD_cons_zero,
    hmW, hmJ]
  omega

/-- Full execution theorem for `sparsifyBody`. -/
theorem sparsifyBody_runs {w : ℕ} {p : Program} {impl : SpannerToolImpl} {t1 t2 t3 fout : ℕ}
    (h1 : MeetsContract w p t1 (task1Contract impl w))
    (h2 : MeetsContract w p t2 (task2Contract impl w))
    (h3 : MeetsContract w p t3 (task3Contract impl w))
    (hfout : MeetsContract w p fout (sparsifyOutContract w))
    {inp : Task1Input} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hwords : ∀ a ∈ [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h], a < 2 ^ w)
    (hv : inp.Valid impl mem w) (hwok : SparsifyWordOK impl inp w) :
    ∃ o st' c,
      Runs w p ω (sparsifyBody t1 t2 t3 fout)
        (startState [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] mem pos) o st' c ∧
      SparsifyPost impl inp mem st'.mem o.value ∧
      c ≤ sparsifyTotalCost impl inp mem := by
  obtain ⟨o1, st₁, c₁, hr1, ⟨rfl, _, r1, _, r3, mem1, v1, mem2, v2, v3, r4, r5, r6,
      hT1, hcap1, hT2, hT3⟩, hc1⟩ :=
    sparsifyCorePrefix_runs h1 h2 h3 inp mem pos ω hwords hv hwok.1
  obtain ⟨o2, st₂, c₂, hr2, hp2, hc2⟩ :=
    sparsifyTail_runs hfout hwords hv hwok r1 r3 r4 r5 r6 hT1 hcap1 hT2 hT3
  refine ⟨o2, st₂, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr1, hr2, rfl⟩), hp2, ?_⟩
  unfold sparsifyTotalCost; omega

/-- `sparsifyBody` meets `sparsifyContract impl w`. -/
theorem sparsify_meetsContract {w : ℕ} {p : Program} {impl : SpannerToolImpl}
    {f t1 t2 t3 fout : ℕ}
    (hproc : p.procs[f]? = some (sparsifyBody t1 t2 t3 fout))
    (h1 : MeetsContract w p t1 (task1Contract impl w))
    (h2 : MeetsContract w p t2 (task2Contract impl w))
    (h3 : MeetsContract w p t3 (task3Contract impl w))
    (hfout : MeetsContract w p fout (sparsifyOutContract w)) :
    MeetsContract w p f (sparsifyContract impl w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨inp, rfl, hv, hwok⟩ := hpre
  obtain ⟨o, st', c, hr, hp, hc⟩ := sparsifyBody_runs h1 h2 h3 hfout hwords hv hwok
  refine ⟨o, st', c, hr, ?_, ?_⟩
  · intro inp' hargs' hv' hwok'
    obtain ⟨o', st'', c', hr', hp', -⟩ := sparsifyBody_runs h1 h2 h3 hfout (hargs' ▸ hwords) hv' hwok'
    rw [← hargs'] at hr'
    obtain ⟨ho, hst, -⟩ := Runs.det hr hr'
    rw [ho, hst]
    exact hp'
  · have h_ex : ∃ inp' : Task1Input,
        [inp.hAddr, inp.jAddr, inp.embJHAddr, inp.h] =
          [inp'.hAddr, inp'.jAddr, inp'.embJHAddr, inp'.h] ∧
        inp'.Valid impl mem w ∧ SparsifyWordOK impl inp' w := ⟨inp, rfl, hv, hwok⟩
    dsimp only [sparsifyContract]
    rw [dite_eq_left_of_eq_true (eq_true h_ex)]
    have hspec := Classical.choose_spec h_ex
    generalize Classical.choose h_ex = inp' at hspec ⊢
    obtain ⟨hargs, hvc, _⟩ := hspec
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨_, hj, he, _⟩ := hargs
    obtain ⟨hJ, hemb⟩ := task1_inputs_agree hj he hv hvc
    obtain ⟨hlen, hsum⟩ := t1_emb_stats_congr hemb
    have hcore : sparsifyCoreCost impl inp mem = sparsifyCoreCost impl inp' mem := by
      unfold sparsifyCoreCost Task2Input.embVertSum
      simp only [Task1Input.toT2]
      rw [hlen, hsum, hJ, ← hj, ← he]
    unfold sparsifyTotalCost
    rw [← hcore, ← hJ]
    exact hc

end MinCostFlow.Spanner
