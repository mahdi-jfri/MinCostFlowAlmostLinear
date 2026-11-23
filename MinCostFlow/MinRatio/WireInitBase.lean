module

public import MinCostFlow.MinRatio.InitConcretePostTail
public import MinCostFlow.MinRatio.WireSpecBase
public import MinCostFlow.MinRatio.OrdSparseCoreHelpers
public import MinCostFlow.IPM.Machine.MinRatioContract
import Mathlib.Tactic

/-!
# Shared contracts and numeric/runtime helpers for concrete ordered Init

Provides the upstream-independent building blocks shared by `WireInitLevelsK`, `WireInitLinkK`,
`WireInitPostTailK`, `WireInitConcrete`, and `WireInitSpecFix`:
1. `OrdInitChainCoresK`: pairwise-disjoint representation invariant for the `d` ordered
   sparse-core levels (`SparseCoreOrdAbs`) and the terminal last-level data structure
   (definitionally identical to `OrdInitChainCoresAt` in `SolverInitWiredBase.lean`).
2. `initParamSetupContract` + `initParamSetupContract_inhabited`: contract and deterministic
   non-vacuity witness for the parameter setup procedure writing `[d, branch, psi, quality,
   epsExp, N₀]`, `lvlM[0..d)` and, right after them, the sparse-core depth `coreDepth`.
3. `LastLevelBuildEqOnE`: extensionality of `LastLevelTool.build` on `G.E`.
4. `initialPathEdgeValue_bounds_of_ranges`: derives `B_tree` bounds for all four fields of
   `initialPathEdgeValue` and `Num.Fits 4 L (±th)` from `LengthsWithin G E len₀` and
   `∀ e ∈ G.E, |grad₀ e| ≤ 2 ^ E`.
5. `algorithm1_initialize_totalRuntime`: expresses `chain.totalRuntime` at Init as
   `(∑ i ∈ range d, T.cost (chain.scState i)) + L.cost (chain.G d)`.
6. `straightLineCost`: universal upper bound on the step cost of any straight-line sequence of
   `.assign` / `.store` / `.nop` statements.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program

/-- Pairwise-disjoint representation invariant for all `C.d` ordered sparse-core levels
(`DSRep (SparseCoreOrdAbs T)` representing `chainLevelOrdAbs chain i`) and the terminal
last-level data structure after ordered Algorithm 2 initialization.
Definitionally equal to `OrdInitChainCoresAt` (`SolverInitWiredBase.lean`). -/
@[expose] def OrdInitChainCoresK {T : SparseCoreRestartTool} {C : ChainParams}
    (Rcore : DSRep (SparseCoreOrdAbs T)) (Rterm : DSRep (ℕ × (ℕ → LSF)))
    (Rtree : DSRep PathTreeState)
    (chain : ChainState T C) (treeHandle levelTable branchTable
      rootBase edgeRecords edgeThresholds slots names slotThresholds m L heap : ℕ)
    (G : MGraph) (recPtr : ℕ → ℕ) (extraStatic : ℕ → Prop)
    (xCore : ℕ → Rcore.τ) (xTerm : Rterm.τ) (xTree : Rtree.τ) (mem : ℕ → ℕ) : Prop :=
  let Ttree := chain.toTreeChain.chainTree
  (∀ i < C.d,
    mem (branchTable + i) = chain.bran i ∧
    Rcore.rep (mem (levelTable + i)) (chainLevelOrdAbs chain i) (xCore i) mem ∧
    (∀ a, Rcore.foot (mem (levelTable + i)) (xCore i) a →
      a < heap ∧
      OutsideInitSlotTables slots names slotThresholds m G.n a ∧
      ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic a ∧
      ¬ Rtree.foot treeHandle xTree a ∧
      (∀ j < C.d, j ≠ i → ¬ Rcore.foot (mem (levelTable + j)) (xCore j) a) ∧
      ¬ Rterm.foot (mem (levelTable + C.d)) xTerm a)) ∧
  mem (branchTable + C.d) = chain.lastBran ∧
  Rterm.rep (mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) xTerm mem ∧
  (∀ a, Rterm.foot (mem (levelTable + C.d)) xTerm a →
    a < heap ∧
    OutsideInitSlotTables slots names slotThresholds m G.n a ∧
    ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic a ∧
    ¬ Rtree.foot treeHandle xTree a ∧
    (∀ j < C.d, ¬ Rcore.foot (mem (levelTable + j)) (xCore j) a))

/-- Contract for the parameter setup subroutine called at the start of `initConcreteBody`:
given `[m, V, L, P, heap]`, writes the six scalar chain parameters `[d, branch, psi, quality,
epsExp, N₀]` at `heap .. heap + 5` and the per-level edge caps `lvlM 0 .. lvlM (d - 1)` at
`heap + 6 .. heap + 6 + d`, returning the next free heap cursor `ret ≤ heap + paramSpace` in at
most `paramCost` deterministic steps. -/
@[expose] def initParamSetupContract (w m V L P d branch psi quality epsExp N₀ coreDepth : ℕ)
    (lvlM : ℕ → ℕ) (paramSpace paramCost : ℕ) : Contract where
  pre args mem := ∃ heap,
    args = [m, V, L, P, heap] ∧ ZeroFrom mem heap ∧ heap + paramSpace < 2 ^ w
  post args mem ret mem' :=
    let heap := args.getD 4 0
    heap + 7 + d ≤ ret ∧ ret ≤ heap + paramSpace ∧
    ListAt mem' heap [d, branch, psi, quality, epsExp, N₀] ∧
    (∀ i < d, mem' (heap + 6 + i) = lvlM i) ∧
    mem' (heap + 6 + d) = coreDepth ∧
    (∀ a < heap, mem' a = mem a) ∧
    ZeroFrom mem' ret
  cost _ _ := paramCost

private def storeConstList : ℕ → List ℕ → Stmt
  | _, [] => .nop
  | off, x :: xs =>
      .store (.bin .add (.reg 4) (.const off)) (.const x) ;;
      storeConstList (off + 1) xs

private theorem storeConstList_noRand (off : ℕ) (xs : List ℕ) :
    (storeConstList off xs).NoRand := by
  induction xs generalizing off with
  | nil => simp [storeConstList, Stmt.NoRand]
  | cons x xs ih => simp [storeConstList, Stmt.NoRand, ih]

private theorem storeConstList_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ (off : ℕ) (xs : List ℕ) (st : State),
      (∀ x ∈ xs, x < 2 ^ w) →
      st.regs 4 + off + xs.length < 2 ^ w →
      ∃ out c, Runs w p ω (storeConstList off xs) st .normal out c ∧
        ListAt out.mem (st.regs 4 + off) xs ∧
        (∀ a, a < st.regs 4 + off ∨ st.regs 4 + off + xs.length ≤ a → out.mem a = st.mem a) ∧
        out.regs = st.regs ∧ out.pos = st.pos ∧ c ≤ 8 * xs.length + 1
  | off, [], st, _, _ =>
      ⟨st, 1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by intro j hj; simp at hj,
        fun _ _ => rfl, rfl, rfl, by omega⟩
  | off, x :: xs, st, hxs, hroom => by
      have hxW : x < 2 ^ w := hxs x (by simp)
      have hoffW : off < 2 ^ w := by simp at hroom; omega
      have haddrW : st.regs 4 + off < 2 ^ w := by simp at hroom; omega
      let s1 := { st with mem := Function.update st.mem (st.regs 4 + off) x }
      have hr1 : Runs w p ω (.store (.bin .add (.reg 4) (.const off)) (.const x)) st .normal s1 5 :=
        runs_store_iff.mpr ⟨st.regs 4 + off, x,
          by simp [Expr.eval, BinOp.eval, hoffW, haddrW],
          by simp [Expr.eval, hxW], rfl, rfl, rfl⟩
      obtain ⟨out, c2, hr2, hlist2, hframe2, hregs2, hpos2, hc2⟩ :=
        storeConstList_runs (w := w) (p := p) (ω := ω) (off + 1) xs s1
          (fun y hy => hxs y (by simp [hy]))
          (by simp only [s1, List.length_cons] at hroom ⊢; omega)
      refine ⟨out, 5 + c2 + 1, runs_seq_iff.mpr (Or.inr ⟨s1, 5, c2, hr1, hr2, rfl⟩), ?_, ?_,
        hregs2, hpos2, by simp only [List.length_cons]; omega⟩
      · intro j hj
        cases j with
        | zero =>
          have hne : st.regs 4 + off < st.regs 4 + (off + 1) := by omega
          simpa [s1] using (hframe2 (st.regs 4 + off) (Or.inl hne)).trans (by simp [s1])
        | succ j' =>
          have hj' : j' < xs.length := by simpa using hj
          have h2 := hlist2 j' hj'
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h2
      · intro a ha
        simp only [List.length_cons] at ha
        rcases ha with hlt | hge
        · rw [hframe2 a (Or.inl (by dsimp [s1]; omega))]
          simp [s1, Function.update_of_ne (show a ≠ st.regs 4 + off by omega)]
        · rw [hframe2 a (Or.inr (by dsimp [s1]; omega))]
          simp [s1, Function.update_of_ne (show a ≠ st.regs 4 + off by omega)]

/-- Non-vacuity of `initParamSetupContract`: for any word-fitting parameters, a concrete
deterministic (`NoRand`) Word-RAM procedure meets `initParamSetupContract` in space `7 + d`
and time `8 * (7 + d) + 12`. -/
theorem initParamSetupContract_inhabited {w m V L P d branch psi quality epsExp N₀ coreDepth : ℕ}
    {lvlM : ℕ → ℕ}
    (hd : d < 2 ^ w) (hbr : branch < 2 ^ w) (hpsi : psi < 2 ^ w)
    (hq : quality < 2 ^ w) (heps : epsExp < 2 ^ w) (hN : N₀ < 2 ^ w)
    (hM : ∀ i < d, lvlM i < 2 ^ w) (hcD : coreDepth < 2 ^ w) (h7d : 7 + d < 2 ^ w) :
    ∃ (p : Program) (proc : ℕ),
      (∀ b ∈ p.procs, b.NoRand) ∧
      MeetsContract w p proc
        (initParamSetupContract w m V L P d branch psi quality epsExp N₀ coreDepth lvlM
          (7 + d) (8 * (7 + d) + 12)) := by
  let vals : List ℕ :=
    [d, branch, psi, quality, epsExp, N₀] ++ (List.range d).map lvlM ++ [coreDepth]
  let body : Stmt := storeConstList 0 vals ;; .ret (.bin .add (.reg 4) (.const (7 + d)))
  refine ⟨⟨[body]⟩, 0, ?_, ?_⟩
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    simp [body, storeConstList_noRand, Stmt.NoRand]
  · intro args mem pos ω _ hpre
    obtain ⟨heap, rfl, hz, hroom⟩ := hpre
    have hlen : vals.length = 7 + d := by simp [vals]; omega
    have hvalsW : ∀ x ∈ vals, x < 2 ^ w := by
      intro x hx
      simp only [vals, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.mem_map, List.mem_range] at hx
      rcases hx with ((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩) | rfl
      · exact hd
      · exact hbr
      · exact hpsi
      · exact hq
      · exact heps
      · exact hN
      · exact hM i hi
      · exact hcD
    let st0 := startState [m, V, L, P, heap] mem pos
    have hst4 : st0.regs 4 = heap := rfl
    obtain ⟨s1, c1, hr1, hlist1, hframe1, hregs1, _, hc1⟩ :=
      storeConstList_runs (w := w) (p := ⟨[body]⟩) (ω := ω) 0 vals st0 hvalsW
        (by rw [hst4, hlen]; omega)
    have hr2 : Runs w ⟨[body]⟩ ω (.ret (.bin .add (.reg 4) (.const (7 + d)))) s1
        (.returned (heap + (7 + d))) s1 4 :=
      runs_ret_iff.mpr ⟨heap + (7 + d),
        by simp [Expr.eval, BinOp.eval, hregs1, hst4, h7d, show heap + (7 + d) < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    refine ⟨body, rfl, .returned (heap + (7 + d)), s1, c1 + 4 + 1,
      runs_seq_iff.mpr (Or.inr ⟨s1, c1, 4, hr1, hr2, rfl⟩), ?_, ?_⟩
    · dsimp only [initParamSetupContract, Outcome.value]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
      refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · intro j hj
        have h1 := hlist1 j (by simp only [vals, List.length_append, List.length_cons,
          List.length_nil, List.length_map, List.length_range] at hj ⊢; omega)
        have hget : vals[j]'(by simp only [vals, List.length_append, List.length_cons,
            List.length_nil, List.length_map, List.length_range] at hj ⊢; omega) =
            ([d, branch, psi, quality, epsExp, N₀] : List ℕ)[j] := by
          simp only [vals]
          rw [List.getElem_append_left (by simp at hj ⊢; omega)]
          exact List.getElem_append_left (by simpa using hj)
        simpa [hst4, hget] using h1
      · intro i hi
        have h1 := hlist1 (6 + i) (by rw [hlen]; omega)
        have hget : vals[6 + i]'(by rw [hlen]; omega) = lvlM i := by
          simp only [vals]
          rw [List.getElem_append_left (by simp; omega)]
          rw [List.getElem_append_right (by simp)]
          simp
        simpa [hst4, Nat.add_assoc, hget] using h1
      · have h1 := hlist1 (6 + d) (by rw [hlen]; omega)
        have hget : vals[6 + d]'(by rw [hlen]; omega) = coreDepth := by
          simp only [vals]
          rw [List.getElem_append_right (by simp only [List.length_append, List.length_cons,
            List.length_nil, List.length_map, List.length_range]; omega)]
          simp
        simpa [hst4, Nat.add_assoc, hget] using h1
      · intro a ha
        exact hframe1 a (Or.inl (by rw [hst4]; omega))
      · intro a ha
        exact (hframe1 a (Or.inr (by rw [hst4, hlen]; omega))).trans (hz a (by omega))
    · change c1 + 4 + 1 ≤ 8 * (7 + d) + 12
      rw [hlen] at hc1
      omega

/-- Extensionality of a `LastLevelTool` on its active edge set `G.E`. -/
@[expose] def LastLevelBuildEqOnE (L : LastLevelTool) : Prop :=
  ∀ (G : MGraph) (ℓ ℓ' : ℕ → ℝ), (∀ e ∈ G.E, ℓ e = ℓ' e) → L.build G ℓ = L.build G ℓ'

/-- From `LengthsWithin G E len₀` and `|grad₀ e| ≤ 2 ^ E`, derive `B_tree` bounds for all four
fields of `initialPathEdgeValue` and `Num.Fits 4 L (±th)` for every edge `e < m`. -/
theorem initialPathEdgeValue_bounds_of_ranges
    {L P m E : ℕ} {G : MGraph} {mem : ℕ → ℕ} {gradient lengths : ℕ} {ε : ℝ} {B_tree : ℤ}
    (hGE : G.E = Finset.range m)
    (hεPos : 0 < ε) (hεLe : ε ≤ (2 : ℝ) ^ E)
    (hThrB : (2 : ℤ) ^ (P + 2 * E + 1) ≤ B_tree)
    (hCapTree : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * B_tree < (Num.capacity 4 L : ℤ))
    (hVecValid : ∀ e < m, Num.Valid mem (lengths + e * L) 4 L ∧
      0 < Num.intVal mem (lengths + e * L) 4 L ∧ Num.Valid mem (gradient + e * L) 4 L)
    (hLenWithin : IPM.LengthsWithin G E (IPM.Machine.readVector mem lengths 4 L P m))
    (hGradRange : ∀ e ∈ G.E, |IPM.Machine.readVector mem gradient 4 L P m e| ≤ (2 : ℝ) ^ E) :
    let lenInt := fun e => (Num.intVal mem (lengths + e * L) 4 L).toNat
    let gradInt := fun e => Num.intVal mem (gradient + e * L) 4 L
    ∀ e < m,
      let v := initialPathEdgeValue P ε (gradInt e) (lenInt e)
      let th := detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)
      |v.gradient| ≤ B_tree ∧ |v.length| ≤ B_tree ∧ |v.flow| ≤ B_tree ∧ |v.detector| ≤ B_tree ∧
      Num.Fits 4 L (-th) ∧ Num.Fits 4 L th := by
  intro lenInt gradInt e he
  have heG : e ∈ G.E := hGE ▸ Finset.mem_range.mpr he
  have hBnonneg : 0 ≤ B_tree := le_trans (by positivity) hThrB
  have h2pPos : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have hpowLe : (2 : ℤ) ^ (P + E) ≤ (2 : ℤ) ^ (P + 2 * E + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hlPos : 0 < Num.intVal mem (lengths + e * L) 4 L := (hVecValid e he).2.1
  have htoNat : ((lenInt e : ℕ) : ℤ) = Num.intVal mem (lengths + e * L) 4 L :=
    Int.toNat_of_nonneg hlPos.le
  have hlenEq : (lenInt e : ℝ) / (2 : ℝ) ^ P =
      IPM.Machine.readVector mem lengths 4 L P m e := by
    have hcast : ((lenInt e : ℕ) : ℝ) = (Num.intVal mem (lengths + e * L) 4 L : ℝ) := by
      exact_mod_cast htoNat
    simp [IPM.Machine.readVector, he, Num.fixVal, hcast]
  have hlenLeR : (lenInt e : ℝ) ≤ (2 : ℝ) ^ (P + E) := by
    have h1 := (hLenWithin e heG).2
    rw [← hlenEq, div_le_iff₀ h2pPos] at h1
    calc (lenInt e : ℝ) ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ P := h1
      _ = (2 : ℝ) ^ (P + E) := by rw [← pow_add, add_comm]
  have hlenIntLe : ((lenInt e : ℕ) : ℤ) ≤ B_tree := by
    have h1 : ((lenInt e : ℕ) : ℤ) ≤ (2 : ℤ) ^ (P + E) := by exact_mod_cast hlenLeR
    exact h1.trans (hpowLe.trans hThrB)
  have hgradEq : (gradInt e : ℝ) / (2 : ℝ) ^ P =
      IPM.Machine.readVector mem gradient 4 L P m e := by
    simp [IPM.Machine.readVector, he, Num.fixVal, gradInt]
  have hgradLeR : |(gradInt e : ℝ)| ≤ (2 : ℝ) ^ (P + E) := by
    have h1 := hGradRange e heG
    rw [← hgradEq, abs_div, abs_of_pos h2pPos, div_le_iff₀ h2pPos] at h1
    calc |(gradInt e : ℝ)| ≤ (2 : ℝ) ^ E * (2 : ℝ) ^ P := h1
      _ = (2 : ℝ) ^ (P + E) := by rw [← pow_add, add_comm]
  have hgradIntLe : |gradInt e| ≤ B_tree := by
    have h1 : |gradInt e| ≤ (2 : ℤ) ^ (P + E) := by exact_mod_cast hgradLeR
    exact h1.trans (hpowLe.trans hThrB)
  have hdetRange : 0 ≤ detectorThreshold P ε (IPM.Machine.readVector mem lengths 4 L P m e) ∧
      detectorThreshold P ε (IPM.Machine.readVector mem lengths 4 L P m e) ≤
        (2 : ℤ) ^ (P + 2 * E + 1) := by
    have hl : 1 / (2 : ℝ) ^ E ≤ IPM.Machine.readVector mem lengths 4 L P m e := by
      simpa [zpow_neg, zpow_natCast, one_div] using (hLenWithin e heG).1
    have hlenPos : 0 < IPM.Machine.readVector mem lengths 4 L P m e := lt_of_lt_of_le (by positivity) hl
    refine ⟨(detectorThreshold_pos P ε _ hεPos hlenPos).le, ?_⟩
    have hsc := detectorThreshold_scaled_bound P E ε _ hεLe hl
    rw [div_le_iff₀ h2pPos, ← pow_add] at hsc
    have hcast : ((detectorThreshold P ε (IPM.Machine.readVector mem lengths 4 L P m e) : ℤ) : ℝ) ≤
        (((2 : ℤ) ^ (P + 2 * E + 1) : ℤ) : ℝ) := by
      push_cast; rw [show P + 2 * E + 1 = 2 * E + 1 + P by omega]; exact hsc
    exact_mod_cast hcast
  rw [← hlenEq] at hdetRange
  have hthLeB : detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P) ≤ B_tree :=
    hdetRange.2.trans hThrB
  have h2BLt : 2 * B_tree < (Num.capacity 4 L : ℤ) := by
    have h1 : (1 : ℤ) ≤ ((2 * G.n + 1 : ℕ) : ℤ) := by omega
    have h2 : 2 * B_tree ≤ 2 * ((2 * G.n + 1 : ℕ) : ℤ) * B_tree := by nlinarith
    omega
  refine ⟨hgradIntLe,
    by simp only [initialPathEdgeValue]; rw [abs_of_nonneg (Int.natCast_nonneg _)]; exact hlenIntLe,
    by simp only [initialPathEdgeValue, abs_zero]; exact hBnonneg,
    by simp only [initialPathEdgeValue, abs_neg, abs_of_nonneg hdetRange.1]; exact hthLeB,
    ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- At initialization, `ChainState.totalRuntime` equals the sum of initial sparse-core tool costs
across all `P.d` levels plus the terminal level's `L.cost (chain.G P.d)`. -/
theorem algorithm1_initialize_totalRuntime (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) :
    let chain := (Chain.Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1
    chain.totalRuntime =
      (∑ i ∈ Finset.range P.d, T.cost (chain.scState i)) + L.cost (chain.G P.d) := by
  dsimp only [ChainState.totalRuntime]
  have hclosed : (Chain.Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1.closedRuntime = 0 := rfl
  have hcurEnc : ∀ i < P.d,
      (Chain.Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1.curEnc i = 0 := by
    intro i hi
    unfold Chain.Ordered.algorithm1_initialize
    dsimp only
    suffices h : ∀ (rem idx : ℕ) (Gf : ℕ → MGraph) (sc : ℕ → T.State)
        (br upd ce cd cf : ℕ → ℕ),
        (∀ j, ce j = 0) →
        (Chain.Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx Gf sc br upd ce cd cf).2.2.2.2.1 i = 0 by
      exact h P.d 0 _ _ _ _ _ _ _ (fun _ => rfl)
    intro rem
    induction rem with
    | zero => intro idx Gf sc br upd ce cd cf hce; exact hce i
    | succ rem ih =>
      intro idx Gf sc br upd ce cd cf hce
      dsimp only [Chain.Ordered.rebuildSuffix]
      exact ih (idx + 1) _ _ _ _ _ _ _ (fun j => by split_ifs <;> simp [hce j])
  have hcurLast : (Chain.Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1.curLastCost =
      L.cost ((Chain.Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1.G P.d) := by
    unfold Chain.Ordered.algorithm1_initialize
    dsimp only
    suffices h : ∀ (rem idx : ℕ) (Gf : ℕ → MGraph) (sc : ℕ → T.State)
        (br upd ce cd cf : ℕ → ℕ),
        let res := Chain.Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx Gf sc br upd ce cd cf
        res.2.2.2.2.2.2.2.2 = L.cost (res.1 (idx + rem)) by
      simpa using h P.d 0 _ _ _ _ _ _ _
    intro rem
    induction rem with
    | zero => intro idx Gf sc br upd ce cd cf; rfl
    | succ rem ih =>
      intro idx Gf sc br upd ce cd cf
      dsimp only [Chain.Ordered.rebuildSuffix]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (idx + 1) _ _ _ _ _ _ _
  rw [hclosed, zero_add, hcurLast]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hcurEnc i (Finset.mem_range.mp hi), add_zero]

/-- Exact per-level recurrence identities for `Chain.Ordered.algorithm1_initialize`. -/
theorem ordAlgorithm1_initialize_level_facts {T : SparseCoreRestartTool} (hEq : ToolInitOrdEqOnE T)
    (L : LastLevelTool) (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ)
    (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) :
    let chain := (Chain.Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1
    chain.G 0 = G₀ ∧
    chain.levelOrd 0 = Bundle.sortedEnds G₀ ∧
    chain.lastBran = 0 ∧
    (chain.lastK, chain.lastLSFs) = L.build (chain.G P.d) (chain.toTreeChain.chainLen ℓ₀ P.d) ∧
    (∀ i < P.d,
      chain.bran i = 0 ∧
      chain.updCount i = 0 ∧
      chain.G (i + 1) = T.S (chain.scState i) 0 ∧
      chain.levelOrd (i + 1) = T.rot (chain.scState i) 0 ∧
      chain.scState i = T.initOrd P.k (lvlM i) N₀ (chain.G i)
        (fun e => if e ∈ (chain.G i).E then chain.toTreeChain.chainLen ℓ₀ i e else 0)
        (fun e => if e ∈ (chain.G i).E then
          (if i = 0 then g₀ e else chain.toTreeChain.chainLen ℓ₀ i e) else 0)
        (chain.levelOrd i)) := by
  dsimp only
  set chain := (Chain.Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1
  have hBase := ordRebuildSuffix_prefix_and_coreAt T L P lvlM N₀ ℓ₀ g₀ P.d 0 (by omega)
    (fun _ => G₀) (fun _ => T.initOrd P.k (lvlM 0) N₀ G₀ ℓ₀ g₀ (Bundle.sortedEnds G₀))
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
  have hG0 : chain.G 0 = G₀ := hBase.1 0 (Nat.zero_le _)
  have hOrd0 : chain.levelOrd 0 = Bundle.sortedEnds G₀ := by
    simp [ChainState.levelOrd, Chain.Ordered.chainLevelOrd, hG0]
  have hLastBuild : (chain.lastK, chain.lastLSFs) =
      L.build (chain.G P.d) (chain.toTreeChain.chainLen ℓ₀ P.d) := by
    suffices h : ∀ (rem idx : ℕ) (Gf : ℕ → MGraph) (sc : ℕ → T.State)
        (br upd ce cd cf : ℕ → ℕ),
        idx + rem = P.d →
        let res := Chain.Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx Gf sc br upd ce cd cf
        let C1 : TreeChain :=
          { d := P.d, k := P.k, G := res.1, lsfs := fun j => T.lsfs (res.2.1 j),
            bran := res.2.2.1, S := fun j => T.S (res.2.1 j), emb := fun j => T.emb (res.2.1 j),
            lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2, lastBran := 0 }
        res.2.2.2.2.2.2.2.1 = L.build (res.1 P.d) (C1.chainLen ℓ₀ P.d) by
      simpa [chain, Chain.Ordered.algorithm1_initialize, ChainState.toTreeChain] using
        h P.d 0 _ _ _ _ _ _ _ (Nat.zero_add P.d)
    intro rem
    induction rem with
    | zero =>
      intro idx Gf sc br upd ce cd cf hsum
      have hidx : idx = P.d := by omega
      subst hidx
      dsimp only [Chain.Ordered.rebuildSuffix]
      congr 1
      suffices hcl : ∀ (n : ℕ) (C₁ C₂ : TreeChain),
          (∀ m < n, C₁.activeLSF m = C₂.activeLSF m) → C₁.chainLen ℓ₀ n = C₂.chainLen ℓ₀ n by
        exact hcl P.d _ _ (fun m hm => by simp [TreeChain.activeLSF, hm])
      intro n
      induction n with
      | zero => intros; rfl
      | succ n ihn =>
        intro C₁ C₂ hact
        simp only [TreeChain.chainLen]
        rw [ihn C₁ C₂ (fun m hm => hact m (Nat.lt_succ_of_lt hm)), hact n (Nat.lt_succ_self n)]
    | succ rem ih =>
      intro idx Gf sc br upd ce cd cf hsum
      dsimp only [Chain.Ordered.rebuildSuffix]
      exact ih (idx + 1) _ _ _ _ _ _ _ (by omega)
  refine ⟨hG0, hOrd0, rfl, hLastBuild, fun i hi => ?_⟩
  have hcore := hBase.2.2 i (Nat.zero_le _) (by omega)
  have hbr : chain.bran i = 0 := hcore.2.2.1
  have hupd : chain.updCount i = 0 := hcore.2.2.2
  have hGsucc : chain.G (i + 1) = T.S (chain.scState i) 0 := hcore.2.1
  have hOrdSucc : chain.levelOrd (i + 1) = T.rot (chain.scState i) 0 := by
    simp [ChainState.levelOrd, Chain.Ordered.chainLevelOrd, hbr]
  have hScZero := ordAlgorithm1_initialize_coreAt_eq_zeroExtension hEq L P lvlM N₀ G₀ ℓ₀ g₀ i hi
  have hSc : chain.scState i = T.initOrd P.k (lvlM i) N₀ (chain.G i)
      (fun e => if e ∈ (chain.G i).E then chain.toTreeChain.chainLen ℓ₀ i e else 0)
      (fun e => if e ∈ (chain.G i).E then
        (if i = 0 then g₀ e else chain.toTreeChain.chainLen ℓ₀ i e) else 0)
      (chain.levelOrd i) :=
    hScZero.trans (hEq _ _ _ _ _ _ _ _ _ (fun _ _ => rfl))
  exact ⟨hbr, hupd, hGsucc, hOrdSucc, hSc⟩

/-- Exact static cost of any straight-line sequence of `.nop`, `.assign`, and `.store` statements. -/
@[expose] def straightLineCost : Stmt → ℕ
  | .nop => 1
  | .assign _ e => e.size + 1
  | .store a v => a.size + v.size + 1
  | .seq s₁ s₂ => straightLineCost s₁ + straightLineCost s₂ + 1
  | _ => 0

/-- Straight-line predicate: a statement built solely from `.nop`, `.assign`, `.store`, `.seq`. -/
@[expose] def IsStraightLine : Stmt → Prop
  | .nop => True
  | .assign _ _ => True
  | .store _ _ => True
  | .seq s₁ s₂ => IsStraightLine s₁ ∧ IsStraightLine s₂
  | _ => False

/-- Any normal execution of a straight-line statement costs exactly `straightLineCost s`. -/
theorem straightLine_cost_eq {w : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ {s : Stmt} {st out : State} {c : ℕ},
      IsStraightLine s → Runs w p ω s st .normal out c → c = straightLineCost s
  | .nop, _, _, _, _, hr => (runs_nop_iff.mp hr).2.2
  | .assign _ _, _, _, _, _, hr => by
      obtain ⟨_, _, _, _, hc⟩ := runs_assign_iff.mp hr; exact hc
  | .store _ _, _, _, _, _, hr => by
      obtain ⟨_, _, _, _, _, _, hc⟩ := runs_store_iff.mp hr; exact hc
  | .seq s₁ s₂, _, _, _, ⟨h1, h2⟩, hr => by
      rcases runs_seq_iff.mp hr with ⟨_, _, _, hbad, _⟩ | ⟨mid, c1, c2, hr1, hr2, hc⟩
      · cases hbad
      · rw [hc, straightLine_cost_eq h1 hr1, straightLine_cost_eq h2 hr2]; rfl

end MinCostFlow.MinRatio
