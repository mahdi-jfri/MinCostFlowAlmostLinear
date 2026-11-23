module

public import MinCostFlow.MinRatio.WireReembPot
public import MinCostFlow.MinRatio.WireChainAlgebra
public import MinCostFlow.MinRatio.WireInitBase
import MinCostFlow.DynSpanner.Walks
import Mathlib.Tactic

/-!
# The re-embedding potential of the chain, and the cost of `selectUpdateLevel` (`WireReembPotChain`)

The select heap updates the keys of a level that `Update` does not rebuild with `selectUpdateLevel`
(`WireSelectUpdate.lean`). Its cost is linear in the four lists of the level, and the list of
re-embedded edges is paid only amortized (`ReembCostBound`). This file sets up the potential of the
solver that pays it, and shows that every step of the chain keeps it paid.

The potential of a chain is `chainReembPot pot C = Σ_{i < d} pot (C.scState i)`, for a potential
`pot` of the tool state that meets `ToolReembPotFacts`: it is at most the tool cost, and a restart
raises it by at most the growth of the tool cost. For the program tool, `pot = progReembPot`
(`progReembPotFacts`). The solver adds `K · chainReembPot pot` to its potential, with `K` the cost
of one key.

* `chainReembPot_init_le`, `chainReembPot_shift_le`, `chainReembPot_rebuild_le`: Init, a shift
  and a rebuild raise the potential by at most the growth of `totalRuntime`. A rebuilt level gets a
  fresh tool state, whose potential is at most its tool cost, and that cost enters `totalRuntime`.
* `updateLoop_level_step`: the step of `updateLoop` at a level `idx < d` that it does not rebuild.
  It gives the next state, its tool state at `idx`, and the growth of `totalRuntime` (the tool cost,
  the encoding of the batch, and the encoding of the forwarded batch when `idx + 1 < d`) and of
  `totalTreeUpdates` (the changes of the forest).
* `selectUpdateLevelCost_paid`: the cost of `selectUpdateLevel` on lists `L`, plus `K` times the new
  potential, is at most `140 + K · (|uG| + |fDel| + |uS|) + K · c · (ΔT + 1) + K` times the old
  potential, for `K` at least the cost of one key plus `40`.
* `selectUpdateLevel_paid_step`: the same at a step of `updateLoop`, against
  `Δ totalRuntime`, `Δ totalTreeUpdates`, and the drop of `chainReembPot`. Two lengths stay
  explicit: the batch `curU` that enters the level (paid by the encoding `enc₀` of the batch at
  level `0`, and by the forwarded encoding of the step before at a deeper level), and, at the
  last sparse level `idx + 1 = d`, the forwarded batch (paid by the rebuild of the last level).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

/-! ## The potential of a tool and of a chain -/

/-- The two facts of a potential `pot` of the tool state that the solver needs besides
`ReembCostBound`: it is at most the tool cost, and a restart raises it by at most the growth of
the tool cost. -/
structure ToolReembPotFacts (T : SparseCoreRestartTool) (pot : T.State → ℕ) : Prop where
  le_cost : ∀ st, pot st ≤ T.cost st
  restart : ∀ st b, pot (T.restart st b) + T.cost st ≤ pot st + T.cost (T.restart st b)

/-- The potential `progReembPot` of the program tool meets `ToolReembPotFacts`
(`progReembPot_le_cost`, `progReembPot_restart`). -/
theorem progReembPotFacts (lsfInit : LSFInit) (C_lsst : ℝ) (depth : ℕ) (impl : SparsifyImpl) :
    ToolReembPotFacts (sparseCoreProgTool lsfInit C_lsst depth impl) progReembPot :=
  ⟨fun st => progReembPot_le_cost st, fun st b => progReembPot_restart st b⟩

/-- The potential of a chain: the tool potential `pot` summed over the levels `i < d`. -/
noncomputable def chainReembPot {T : SparseCoreRestartTool} {P : ChainParams}
    (pot : T.State → ℕ) (C : ChainState T P) : ℕ :=
  (Finset.range P.d).sum fun i => pot (C.scState i)

private theorem sum_range_split_le {n i : ℕ} (hi : i ≤ n) (f : ℕ → ℕ) :
    (Finset.range n).sum f = (Finset.range i).sum f + (Finset.Ico i n).sum f :=
  (Finset.sum_range_add_sum_Ico f hi).symm

/-! ## Init, shift and rebuild -/

/-- **Init.** The potential of the chain that Init builds is at most its `totalRuntime`. -/
theorem chainReembPot_init_le {T : SparseCoreRestartTool} {pot : T.State → ℕ}
    (hpot : ToolReembPotFacts T pot) (L : LastLevelTool) (P : ChainParams) (lvlM : ℕ → ℕ)
    (N₀ : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) :
    let chain := (Chain.Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1
    chainReembPot pot chain ≤ chain.totalRuntime := by
  intro chain
  have h := algorithm1_initialize_totalRuntime T L P lvlM N₀ G₀ ℓ₀ g₀
  change chain.totalRuntime = _ at h
  rw [h]
  unfold chainReembPot
  exact le_trans (Finset.sum_le_sum fun i _ => hpot.le_cost _) (Nat.le_add_right _ _)

/-- **A shift at `i₀ < d`.** The potential grows by at most the growth of `totalRuntime`: level
`i₀` is restarted (`ToolReembPotFacts.restart`), and the levels above it get fresh tool states,
whose costs enter `totalRuntime` (`shiftDeep_totalRuntime_sub`). -/
theorem chainReembPot_shift_le {T : SparseCoreRestartTool} {pot : T.State → ℕ}
    (hpot : ToolReembPotFacts T pot) (L : LastLevelTool) (P : ChainParams)
    (chain : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ < P.d)
    (hMono : T.cost (chain.scState i₀) ≤
      T.cost (T.restart (chain.scState i₀) ((chain.bran i₀ + 1) % P.k))) :
    let next := (Chain.Ordered.algorithm1_shift T L P chain i₀).1
    chainReembPot pot next ≤ chainReembPot pot chain + (next.totalRuntime - chain.totalRuntime) := by
  intro next
  have hEx := ordAlgorithm1_shift_exact T L P chain hi₀
  have hΔ := shiftDeep_totalRuntime_sub T L P chain hi₀ hMono
  change next.totalRuntime - chain.totalRuntime =
    (T.cost (next.scState i₀) - T.cost (chain.scState i₀)) +
      (Finset.Ico (i₀ + 1) P.d).sum (fun j => T.cost (next.scState j)) + L.cost (next.G P.d) at hΔ
  have hsc0 : next.scState i₀ = T.restart (chain.scState i₀) ((chain.bran i₀ + 1) % P.k) :=
    hEx.2.2.1
  have hsplit : ∀ C : ChainState T P, chainReembPot pot C =
      (Finset.range i₀).sum (fun j => pot (C.scState j)) + pot (C.scState i₀) +
        (Finset.Ico (i₀ + 1) P.d).sum (fun j => pot (C.scState j)) := by
    intro C
    unfold chainReembPot
    rw [sum_range_split_le (Nat.succ_le_of_lt hi₀), Finset.sum_range_succ]
  have hpre : (Finset.range i₀).sum (fun j => pot (next.scState j)) =
      (Finset.range i₀).sum (fun j => pot (chain.scState j)) :=
    Finset.sum_congr rfl fun j hj => by rw [(hEx.2.1 j (Finset.mem_range.mp hj)).1]
  have hsuf : (Finset.Ico (i₀ + 1) P.d).sum (fun j => pot (next.scState j)) ≤
      (Finset.Ico (i₀ + 1) P.d).sum (fun j => T.cost (next.scState j)) :=
    Finset.sum_le_sum fun j _ => hpot.le_cost _
  have hres := hpot.restart (chain.scState i₀) ((chain.bran i₀ + 1) % P.k)
  rw [← hsc0] at hres hMono
  have key : pot (next.scState i₀) + (Finset.Ico (i₀ + 1) P.d).sum (fun j => pot (next.scState j)) ≤
      pot (chain.scState i₀) + (next.totalRuntime - chain.totalRuntime) := by
    rw [hΔ]; omega
  rw [hsplit next, hsplit chain, hpre]
  omega

/-- **A rebuild at `i₀ < d`.** The potential grows by at most the growth of `totalRuntime`: the
levels below `i₀` keep their tool states, and the levels from `i₀` on get fresh tool states,
whose costs enter `totalRuntime` (`rebuild_totalRuntime_sub`). -/
theorem chainReembPot_rebuild_le {T : SparseCoreRestartTool} {pot : T.State → ℕ}
    (hpot : ToolReembPotFacts T pot) (L : LastLevelTool) (P : ChainParams)
    (chain : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ < P.d) (Gnew : MGraph) (extraEnc : ℕ) :
    let next := (Chain.Ordered.algorithm1_rebuild T L P chain i₀ Gnew extraEnc).1
    chainReembPot pot next ≤ chainReembPot pot chain + (next.totalRuntime - chain.totalRuntime) := by
  intro next
  have hΔ := rebuild_totalRuntime_sub T L P chain hi₀ Gnew extraEnc
  change next.totalRuntime - chain.totalRuntime =
    (Finset.Ico i₀ P.d).sum (fun j => T.cost (next.scState j)) + L.cost (next.G P.d) + extraEnc
    at hΔ
  set G0 := fun j => if j = i₀ then Gnew else chain.G j
  set res := Chain.Ordered.rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i₀) i₀
    G0 chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd
  obtain ⟨_, hSBpre, _⟩ :=
    ordRebuildSuffix_prefix_and_coreAt T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i₀) i₀
      (by omega) G0 chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates
      chain.curFwd
  have hSc : ∀ m, next.scState m = res.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
  have hsplit : ∀ C : ChainState T P, chainReembPot pot C =
      (Finset.range i₀).sum (fun j => pot (C.scState j)) +
        (Finset.Ico i₀ P.d).sum (fun j => pot (C.scState j)) := by
    intro C
    unfold chainReembPot
    rw [sum_range_split_le (le_of_lt hi₀)]
  have hpre : (Finset.range i₀).sum (fun j => pot (next.scState j)) =
      (Finset.range i₀).sum (fun j => pot (chain.scState j)) :=
    Finset.sum_congr rfl fun j hj => by
      rw [hSc j, (hSBpre j (Finset.mem_range.mp hj)).1]
  have hsuf : (Finset.Ico i₀ P.d).sum (fun j => pot (next.scState j)) ≤
      (Finset.Ico i₀ P.d).sum (fun j => T.cost (next.scState j)) :=
    Finset.sum_le_sum fun j _ => hpot.le_cost _
  have key : (Finset.Ico i₀ P.d).sum (fun j => pot (next.scState j)) ≤
      next.totalRuntime - chain.totalRuntime := by
    rw [hΔ]; omega
  rw [hsplit next, hsplit chain, hpre]
  omega

/-! ## A level of `updateLoop` that is not rebuilt -/

/-- **The step of `updateLoop` at a level `idx < d` that is not rebuilt.** The loop goes on at
`idx + 1` from a state `stNext` whose tool state at `idx` is the update `res.1` of the old one, and
whose other tool states and branches are the old ones. `totalRuntime` grows by the growth of the
tool cost at `idx`, by the encoding `e` of the batch charged at `idx`, and, when `idx + 1 < d`, by
the encoding of the forwarded batch `nextU` at level `idx + 1`. `totalTreeUpdates` grows by the
number of changes of the forest of level `idx`. -/
theorem updateLoop_level_step (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) (rem idx : ℕ)
    (st : ChainState T P) (curG : MGraph) (curU : List Update) (e : ℕ) (hidx : idx < P.d)
    (hOver : ¬ intRebuildThreshold P N₀ idx < st.updCount idx + curU.length) :
    let Cpartial : TreeChain :=
      { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
    let res := T.updateOrd (st.scState idx) curU (Cpartial.chainLen ℓ' idx)
      (Cpartial.chainGrad g' idx)
      (Chain.Ordered.chainLevelOrd T (fun j => if j = idx then curG else st.G j) st.scState
        st.bran idx)
    let fiChanges := diffTreeChanges (T.lsfs (st.scState idx) (st.bran idx)).F.F.E
      (T.lsfs res.1 (st.bran idx)).F.F.E
    let nextU := res.2 (st.bran idx)
    ∃ stNext : ChainState T P,
      (Chain.Ordered.updateLoop T L TP P N₀ ℓ' g' (rem + 1) idx st curG curU e).1 =
        (Chain.Ordered.updateLoop T L TP P N₀ ℓ' g' rem (idx + 1) stNext
          (T.S res.1 (st.bran idx)) nextU 0).1 ∧
      (∀ j, stNext.scState j = if j = idx then res.1 else st.scState j) ∧
      stNext.bran = st.bran ∧
      stNext.totalRuntime + T.cost (st.scState idx) =
        st.totalRuntime + T.cost res.1 + e +
          (if idx + 1 < P.d then (st.G (idx + 1)).batchEnc nextU else 0) ∧
      stNext.totalTreeUpdates = st.totalTreeUpdates + fiChanges.length := by
  intro Cpartial res fiChanges nextU
  let nextEnc := (st.G (idx + 1)).batchEnc nextU
  let stNext : ChainState T P :=
    { st with
      G := fun j => if j = idx then curG else st.G j
      scState := fun j => if j = idx then res.1 else st.scState j
      updCount := fun j => if j = idx then st.updCount idx + curU.length else st.updCount j
      recUpdates := fun j =>
        if j = idx + 1 then st.recUpdates (idx + 1) + nextU.length else st.recUpdates j
      curFwd := fun j =>
        if j = idx then st.curFwd idx + nextU.length else st.curFwd j
      curEnc := fun j =>
        if j = idx then st.curEnc idx + e
        else if j = idx + 1 then st.curEnc (idx + 1) + nextEnc
        else st.curEnc j
      curDecUpdates := fun j =>
        if j = idx then st.curDecUpdates idx + fiChanges.length else st.curDecUpdates j }
  refine ⟨stNext, ?_, fun j => rfl, rfl, ?_, ?_⟩
  · conv_lhs => unfold Chain.Ordered.updateLoop
    rw [ite_eq_right hOver]
  · -- `totalRuntime`: only the terms at `idx` and `idx + 1` change.
    have hterm : ∀ i, (T.cost (stNext.scState i) + stNext.curEnc i) +
          (if i = idx then T.cost (st.scState idx) else 0) =
        (T.cost (st.scState i) + st.curEnc i) + (if i = idx then T.cost res.1 + e else 0) +
          (if i = idx + 1 then nextEnc else 0) := by
      intro i
      by_cases h1 : i = idx
      · subst h1
        simp only [stNext, ↓reduceIte, show i ≠ i + 1 by omega]
        try omega
      · by_cases h2 : i = idx + 1
        · subst h2
          simp only [stNext, h1, ↓reduceIte]
          try omega
        · simp only [stNext, h1, h2, ↓reduceIte]
          try omega
    have hsum := Finset.sum_congr (s₁ := Finset.range P.d) rfl fun i (_ : i ∈ Finset.range P.d) =>
      hterm i
    rw [Finset.sum_add_distrib (f := fun i => T.cost (stNext.scState i) + stNext.curEnc i)
        (g := fun i => if i = idx then T.cost (st.scState idx) else 0),
      Finset.sum_add_distrib
        (f := fun i => T.cost (st.scState i) + st.curEnc i + (if i = idx then T.cost res.1 + e else 0))
        (g := fun i => if i = idx + 1 then nextEnc else 0),
      Finset.sum_add_distrib (f := fun i => T.cost (st.scState i) + st.curEnc i)
        (g := fun i => if i = idx then T.cost res.1 + e else 0),
      Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq'] at hsum
    simp only [Finset.mem_range, hidx, ↓reduceIte] at hsum
    unfold ChainState.totalRuntime
    change st.closedRuntime + _ + st.curLastCost + _ = st.closedRuntime + _ + st.curLastCost + _ + _ + _
    split_ifs at hsum ⊢ with hlt <;> omega
  · -- `totalTreeUpdates`: only the term at `idx` changes.
    have hterm : ∀ i, stNext.curDecUpdates i =
        st.curDecUpdates i + (if i = idx then fiChanges.length else 0) := by
      intro i
      by_cases h1 : i = idx
      · subst h1; simp only [stNext, ↓reduceIte]
      · simp only [stNext, h1, ↓reduceIte, Nat.add_zero]
    have hsum : (Finset.range P.d).sum (fun i => stNext.curDecUpdates i) =
        (Finset.range P.d).sum (fun i => st.curDecUpdates i) + fiChanges.length := by
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_range, hidx, ↓reduceIte]
    unfold ChainState.totalTreeUpdates
    change st.closedTreeUpdates + _ + st.curLastTreeUpdates = _
    rw [hsum]
    omega

/-! ## The cost of `selectUpdateLevel` -/

/-- **The cost of `selectUpdateLevel`, paid.** Let `K` be at least the cost of one key plus `40`.
If the list of re-embedded edges meets the amortized `ReembCostBound` with the potentials `phi`
and `phi'`, then the cost of `selectUpdateLevel` on the lists `L`, plus `K` times the new
potential, is at most `140`, plus `K` times the three other lists, plus `K · c · (ΔT + 1)`, plus
`K` times the old potential. -/
theorem selectUpdateLevelCost_paid {L : LevelDiffLists} {cap Lk evalCost K c ΔT phi phi' : ℕ}
    (hK : selectProcessEdgeCost cap Lk evalCost + 40 ≤ K)
    (hre : ReembCostBound L.reemb ΔT c phi phi') :
    selectUpdateLevelCost L cap Lk evalCost + K * phi' ≤
      140 + K * (L.uG.length + L.fDel.length + L.uS.length) + K * (c * (ΔT + 1)) + K * phi := by
  unfold selectUpdateLevelCost selectProcessListCost
  unfold ReembCostBound at hre
  have h1 : L.totalLen * (selectProcessEdgeCost cap Lk evalCost + 40) ≤ L.totalLen * K :=
    Nat.mul_le_mul_left _ hK
  have h2 : K * (L.reemb.length + phi') ≤ K * (c * (ΔT + 1) + phi) := Nat.mul_le_mul_left _ hre
  have h3 : L.totalLen * K =
      K * (L.uG.length + L.fDel.length + L.uS.length) + K * L.reemb.length := by
    unfold LevelDiffLists.totalLen; ring
  rw [Nat.mul_add, Nat.mul_add] at h2
  omega

/-- **The cost of `selectUpdateLevel` at a step of `updateLoop`, paid.** At a level `idx < d` that
`updateLoop` does not rebuild, with the next state `stNext` of `updateLoop_level_step` (its tool
state at `idx` is `sc'`, the others are the old ones), let the lists `L` of the level be covered by
the batch `curU`, the forwarded batch `nextU` and the changes `fiChanges` of the forest, and let the
list of re-embedded edges meet `ReembCostBound` with the potential `pot`. Then the cost of
`selectUpdateLevel`, plus `K` times the new potential of the chain, is paid by
`K (c + 1) · Δ totalRuntime`, `K · Δ totalTreeUpdates`, the old potential, `140 + K c`, and
`K` times the two lengths that the step does not charge: the batch `curU` (charged as `enc₀` at
level `0`, and as the forwarded encoding of the step before at a deeper level), and the batch
`nextU` when `idx + 1 = d` (it enters the last level). -/
theorem selectUpdateLevel_paid_step {T : SparseCoreRestartTool} {P : ChainParams}
    (pot : T.State → ℕ) {st stNext : ChainState T P} {idx : ℕ} {sc' : T.State} {e : ℕ}
    {curU nextU : List Update} {fiLen : ℕ}
    (hsc : ∀ j, stNext.scState j = if j = idx then sc' else st.scState j) (hidx : idx < P.d)
    (hRt : stNext.totalRuntime + T.cost (st.scState idx) =
      st.totalRuntime + T.cost sc' + e +
        (if idx + 1 < P.d then (st.G (idx + 1)).batchEnc nextU else 0))
    (hTu : stNext.totalTreeUpdates = st.totalTreeUpdates + fiLen)
    (hMono : T.cost (st.scState idx) ≤ T.cost sc')
    {L : LevelDiffLists} {cap Lk evalCost K c : ℕ}
    (hK : selectProcessEdgeCost cap Lk evalCost + 40 ≤ K)
    (hre : ReembCostBound L.reemb (T.cost sc' - T.cost (st.scState idx)) c
      (pot (st.scState idx)) (pot sc'))
    (hlen : L.uG.length + L.fDel.length + L.uS.length ≤ curU.length + nextU.length + fiLen) :
    selectUpdateLevelCost L cap Lk evalCost + K * chainReembPot pot stNext ≤
      140 + K * c + K * curU.length + K * (if idx + 1 < P.d then 0 else nextU.length) +
        K * (c + 1) * (stNext.totalRuntime - st.totalRuntime) +
        K * (stNext.totalTreeUpdates - st.totalTreeUpdates) + K * chainReembPot pot st := by
  have hcost := selectUpdateLevelCost_paid hK hre
  -- The potential of the chain changes only at `idx`.
  have hpot : chainReembPot pot stNext + pot (st.scState idx) =
      chainReembPot pot st + pot sc' := by
    have hidxm : idx ∈ Finset.range P.d := Finset.mem_range.mpr hidx
    unfold chainReembPot
    rw [← Finset.add_sum_erase _ _ hidxm, ← Finset.add_sum_erase _ _ hidxm, hsc idx, ite_eq_left rfl]
    have : ((Finset.range P.d).erase idx).sum (fun i => pot (stNext.scState i)) =
        ((Finset.range P.d).erase idx).sum (fun i => pot (st.scState i)) :=
      Finset.sum_congr rfl fun i hi => by rw [hsc i, ite_eq_right (Finset.ne_of_mem_erase hi)]
    rw [this]
    omega
  -- The forwarded batch is at most its encoding.
  have hnext : nextU.length ≤ (st.G (idx + 1)).batchEnc nextU :=
    MinCostFlow.DynSpanner.length_le_batchEnc _ _
  have hfwd : (if idx + 1 < P.d then nextU.length else 0) +
      (T.cost sc' - T.cost (st.scState idx)) ≤ stNext.totalRuntime - st.totalRuntime := by
    split_ifs at hRt ⊢ <;> omega
  have hTu' : stNext.totalTreeUpdates - st.totalTreeUpdates = fiLen := by omega
  have hsplit : nextU.length =
      (if idx + 1 < P.d then nextU.length else 0) + (if idx + 1 < P.d then 0 else nextU.length) := by
    split_ifs <;> simp
  rw [hTu']
  generalize hY : (if idx + 1 < P.d then nextU.length else 0) = Y at hfwd hsplit
  generalize hX : (if idx + 1 < P.d then 0 else nextU.length) = X at hsplit ⊢
  generalize T.cost sc' - T.cost (st.scState idx) = ΔT at hcost hfwd
  generalize stNext.totalRuntime - st.totalRuntime = Δrt at hfwd ⊢
  rw [hsplit] at hlen
  -- The three lists.
  have hA : K * (L.uG.length + L.fDel.length + L.uS.length) ≤
      K * curU.length + K * X + K * Y + K * fiLen := by
    have := Nat.mul_le_mul_left K hlen
    simp only [Nat.mul_add] at this ⊢
    omega
  -- The tool cost and the forwarded batch.
  have hB : K * (c * (ΔT + 1)) + K * Y ≤ K * c + K * (c + 1) * Δrt := by
    have h0 : c * ΔT ≤ c * Δrt := Nat.mul_le_mul_left c (by omega)
    have h1 : c * ΔT + Y ≤ (c + 1) * Δrt := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h2 := Nat.mul_le_mul_left K h1
    rw [Nat.mul_add] at h2
    rw [Nat.mul_add c ΔT 1, Nat.mul_one, Nat.mul_add K (c * ΔT) c, Nat.mul_assoc K (c + 1) Δrt]
    omega
  -- The level's potential is replaced by the chain's.
  have hpotK : K * chainReembPot pot stNext + K * pot (st.scState idx) =
      K * chainReembPot pot st + K * pot sc' := by
    rw [← Nat.mul_add, ← Nat.mul_add, hpot]
  omega

end MinCostFlow.MinRatio
