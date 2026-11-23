module

public import MinCostFlow.MinRatio.SelectUpdateG0One
public import MinCostFlow.MinRatio.SelectLevelBlocksSolver
import MinCostFlow.LinkCut.PathProg.Rep
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Full level-0 gradient refresh (`SelectUpdateG0`)

Updates `B.g0Ptr` after `ordChainUpdateCoreBody` for both Branch A (`firstReb = 0`) and Branch B
(`0 < firstReb`), using `selCopyG0OneBody` (`SelectUpdateG0One.lean`) and `selFilterPresentBody`
(`SelectGraphRefill.lean`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
open MinCostFlow.LinkCut.Path MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.PathProg

/-! ## 4. Full level-0 gradient refresh (`selUpdateG0Body`) -/

/-- Update `B.g0Ptr` for `modelPre` after `ordChainUpdateCoreBody`.
* If `firstReb = 0` (Branch A): refreshes all `mNew := mem (G0Ptr + 1)` edges `0 .. mNew - 1`
  using `0` scratch.
* If `firstReb ≠ 0` (Branch B): filters slot-0 `uG` against `G0Ptr`'s edge-presence array into
  `scratch` (`uG.length` scratch words) and refreshes each surviving touched edge.
Arguments: `[firstReb, slots, edgeRecords, treeHeap, g0Ptr, G0Ptr, vCap, slot0, Lk, scratch]`
(`reg 0..9`). Returns `scOut`. -/
def selUpdateG0Body (copyOne filterPres : ℕ) : Stmt :=
  .cond (.reg 0)
    (.assign 10 (.load (.reg 7)) ;;
     .assign 11 (.load (.bin .add (.reg 7) (.const 1))) ;;
     .assign 12 (.bin .add (.bin .add (.reg 5) (.const 4)) (.bin .mul (.const 7) (.reg 6))) ;;
     .call 13 filterPres [.reg 10, .reg 11, .reg 12, .reg 9] ;;
     forRange 14 (.const 0) (.reg 13)
       (.assign 15 (.load (.bin .add (.reg 9) (.reg 14))) ;;
        .call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 15, .reg 8]) ;;
     .ret (.bin .add (.reg 9) (.reg 11)))
    (.assign 10 (.load (.bin .add (.reg 5) (.const 3))) ;;
     forRange 14 (.const 0) (.reg 10)
       (.call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 14, .reg 8]) ;;
     .ret (.reg 9))

theorem selUpdateG0Body_noRand (copyOne filterPres : ℕ) :
    (selUpdateG0Body copyOne filterPres).NoRand := by
  simp [selUpdateG0Body, forRange, forUp, Stmt.NoRand]

/-- Scratch space bound for `selUpdateG0Body`. -/
def selUpdateG0Space (firstReb uGLen : ℕ) : ℕ :=
  if firstReb = 0 then 0 else uGLen

/-- Step cost bound for `selUpdateG0Body`. -/
def selUpdateG0Cost (firstReb mNew uGLen Lk : ℕ) : ℕ :=
  if firstReb = 0 then mNew * (45 * Lk + 160) + 40
  else uGLen * (45 * Lk + 210) + 80

private lemma runs_loop_f {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

private lemma runs_loop_t {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {c₁ c₂ : ℕ} {v : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h1 : Runs w p ω body st .normal st₁ c₁)
    (h2 : Runs w p ω (.loop e body) st₁ o st₂ c₂) :
    Runs w p ω (.loop e body) st o st₂ (e.size + c₁ + c₂ + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st₁, c₁, c₂, he, hv, h1, h2, rfl⟩))

set_option maxHeartbeats 800000 in
/-- Verification of `selUpdateG0Body`: updates `D.E0 := (modelPre.chain.G 0).E` and
`D.g := modelPre.chain.g` in `SelBlocksDataAt` while preserving all memory `< scratch` outside
`B.regG0` (and thus `Rrep.rep`, `SolverLevelCapsInv`, `SelectMetaTableAt`, `SelectHeapAt`, and all
other block fields). -/
theorem selUpdateG0_runs
    {w L P m V psi k epsExp drainUnit root firstReb vCap pLast slot0 scratch pos : ℕ}
    {copyOne filterPres : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {ω : ℕ → Bool}
    {modelPre : Alg2State cfg} {tok' : SolverToken cfg L Rcore}
    {B : SelectBlocksLoc} {D : SelBlocksData} {uG : List ℕ} {mem : ℕ → ℕ}
    (hw16 : 16 < 2 ^ w) (hLpos : 0 < L) (hBLk : B.Lk = L) (hBv : B.vCap = vCap)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root modelPre tok' mem)
    (hFootSc : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a → a < scratch)
    (hFootOffG0 : ∀ a, B.g0Ptr ≤ a → a < B.g0Ptr + B.eCap * L →
      ¬ (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a)
    (hG0Ptr : DynGraphAt mem (solverLevelG tok' mem 0) vCap B.eCap (modelPre.chain.G 0))
    (hG0Le : solverLevelG tok' mem 0 + dynGraphSize vCap B.eCap ≤ scratch)
    (hG0OffB : solverLevelG tok' mem 0 + dynGraphSize vCap B.eCap ≤ B.g0Ptr ∨
      B.g0Ptr + B.eCap * L ≤ solverLevelG tok' mem 0)
    (hBEnd : B.endAddr ≤ scratch)
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hgEq : ∀ e ∈ (modelPre.chain.G 0).E, modelPre.chain.g e = modelPre.extg (modelPre.intToExt e))
    (hFit : ∀ e ∈ (modelPre.chain.G 0).E, ∀ z : ℤ,
      (z : ℝ) / (2 : ℝ) ^ P = modelPre.chain.g e → Num.Fits 4 L z ∧ Num.Fits 4 L (-z))
    (hBranchA : firstReb = 0 → (modelPre.chain.G 0).E = Finset.range (modelPre.chain.G 0).m)
    (hBranchB : firstReb ≠ 0 →
      slot0 + 2 ≤ scratch ∧
      mem (slot0 + 1) = uG.length ∧
      ListAt mem (mem slot0) uG ∧
      mem slot0 + uG.length ≤ scratch ∧
      (mem slot0 + uG.length ≤ B.g0Ptr ∨ B.g0Ptr + B.eCap * L ≤ mem slot0) ∧
      (∀ e ∈ uG, e < B.eCap) ∧
      (∀ e ∈ (modelPre.chain.G 0).E, e ∉ uG → e ∈ D.E0 ∧ modelPre.chain.g e = D.g e))
    (hCopyOne : ∀ val : ℤ, MeetsContract w p copyOne (selCopyG0OneContract w B.eCap val))
    (hFilter : MeetsContract w p filterPres (selFilterPresentContract w uG))
    (hz : ZeroFrom mem scratch)
    (hroom : scratch + selUpdateG0Space firstReb uG.length < 2 ^ w) :
    ∃ scOut cost out,
      Runs w p ω (selUpdateG0Body copyOne filterPres)
        (startState [firstReb, tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr,
          solverLevelG tok' mem 0, vCap, slot0, L, scratch] mem pos)
        (.returned scOut) out cost ∧
      scOut = scratch + selUpdateG0Space firstReb uG.length ∧
      SelBlocksDataAt out.mem B P
        { D with E0 := (modelPre.chain.G 0).E, g := modelPre.chain.g } pLast ∧
      ZeroFrom out.mem scOut ∧
      (∀ a < scratch, ¬ B.regG0 a → out.mem a = mem a) ∧
      cost ≤ selUpdateG0Cost firstReb (modelPre.chain.G 0).m uG.length L := by
  have hBEndEq : B.g0Ptr + B.eCap * L = B.endAddr := by
    rw [← hBLk]; rfl
  have hG0EndW : B.g0Ptr + B.eCap * L < 2 ^ w := by omega
  have hECapLeMul : B.eCap ≤ B.eCap * L := Nat.le_mul_of_pos_right _ hLpos
  have hECapW : B.eCap < 2 ^ w := by omega
  have hFootW : ∀ a,
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a → a < 2 ^ w :=
    fun a ha => lt_of_lt_of_le (hFootSc a ha) (by omega)
  have hRdAll : ∀ e ∈ (modelPre.chain.G 0).E,
      ∃ z : ℤ, (z : ℝ) / (2 : ℝ) ^ P = modelPre.chain.g e ∧
        SolverEdgeGradReadable w mem tok'.slots tok'.edgeRecords tok'.treeHeap
          B.g0Ptr B.eCap e L z := fun e he =>
    solverEdgeGradReadable_of_rep hw16 hLpos he (hG0Ptr.2.2.1 e he) hrep hFootW hFootOffG0
      hG0EndW (hgEq e he) (hFit e he)
  have hRdPres : ∀ (mem' : ℕ → ℕ),
      (∀ a < scratch, ¬ B.regG0 a → mem' a = mem a) →
      ∀ e ∈ (modelPre.chain.G 0).E, ∀ z : ℤ,
        SolverEdgeGradReadable w mem tok'.slots tok'.edgeRecords tok'.treeHeap
          B.g0Ptr B.eCap e L z →
        SolverEdgeGradReadable w mem' tok'.slots tok'.edgeRecords tok'.treeHeap
          B.g0Ptr B.eCap e L z := by
    intro mem' hfr e he z hRd
    obtain ⟨_, _, _, _, hFresh, _, _, ⟨hEIntCap, _, _, _⟩, _, _, _, _, ⟨hTnEq, hArena, _⟩, hAcc, _, _, _, _,
      _, hTags⟩ := hrep
    obtain ⟨hOwn, _, _, _, _, _, _, _, _, hSlotsTag, _, _, _, hRecsTag, _, _, _, hRecBlkTag, _⟩ :=
      hTags
    have heInt : e < tok'.intCap := hEIntCap e he
    have hFootAg : ∀ a,
        (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a →
        mem' a = mem a := fun a ha =>
      hfr a (hFootSc a ha) fun hreg => by
        unfold SelectBlocksLoc.regG0 SelectBlocksLoc.endAddr at hreg
        rw [hBLk] at hreg
        exact hFootOffG0 a hreg.1 hreg.2 ha
    refine hRd.of_agree
      (hFootAg _ (Or.inl (hOwn _ (by rw [hSlotsTag e heInt]; omega))))
      (fun h0 => by
        obtain ⟨he2i, heExt⟩ := hFresh.hRight e he
        have hAccE := (hAcc.1 (modelPre.intToExt e) heExt).2.2
        dsimp only at hAccE; rw [he2i] at hAccE
        have hNotF : e ∉ modelPre.chain.toTreeChain.chainTree.E := by
          intro hInF; simp only [hInF, ↓reduceIte] at hAccE
          exact hAccE.1 h0
        have hRecTagE := (hRecBlkTag (modelPre.intToExt e) heExt).2
        rw [he2i] at hRecTagE
        refine ⟨hFootAg _ (Or.inl (hOwn _ (by rw [hRecsTag e heInt]; omega))), fun i hi => ?_⟩
        rw [show mem (tok'.edgeRecords + e) + 2 + i = mem (tok'.edgeRecords + e) + (2 + i) by omega]
        exact hFootAg _ (Or.inl (hOwn _ (by rw [hRecTagE hNotF (2 + i) (by omega)]; omega))))
      (fun hne => by
        obtain ⟨he2i, heExt⟩ := hFresh.hRight e he
        have hAccE := (hAcc.1 (modelPre.intToExt e) heExt).2.2
        dsimp only at hAccE; rw [he2i] at hAccE
        have hInF : e ∈ modelPre.chain.toTreeChain.chainTree.E := by
          by_contra hNotF; simp only [hNotF, ↓reduceIte] at hAccE
          exact hne hAccE.1
        simp only [hInF, ↓reduceIte] at hAccE
        have hsLe : mem (tok'.slots + e) ≤ 2 * tok'.tree.n := Nat.le_of_lt hAccE.2.1.2
        have hK : mem (tok'.treeHeap + 3) = treeLimbs L := hArena.hK
        have hnb : mem (tok'.treeHeap + 4) = arenaNb tok'.treeHeap tok'.tree.n := hArena.hnb
        have hTreeFoot : ∀ a, tok'.treeHeap ≤ a → a < arenaEnd tok'.treeHeap tok'.tree.n L →
            mem' a = mem a := fun a h1 h2 => hFootAg a (Or.inr (Or.inl ⟨h1, by rwa [hTnEq]⟩))
        have hEndEq : arenaEnd tok'.treeHeap tok'.tree.n L =
            arenaNb tok'.treeHeap tok'.tree.n +
              (2 * tok'.tree.n + 1) * (13 + 9 * treeLimbs L) := by
          unfold arenaEnd recW; ring
        have hMulLe : (13 + 9 * treeLimbs L) * mem (tok'.slots + e) + (13 + 9 * treeLimbs L) ≤
            (2 * tok'.tree.n + 1) * (13 + 9 * treeLimbs L) := by
          rw [Nat.mul_comm (2 * tok'.tree.n + 1), ← Nat.mul_succ]
          exact Nat.mul_le_mul_left _ (Nat.succ_le_succ hsLe)
        refine ⟨hTreeFoot _ (by omega) (by unfold arenaEnd arenaNb recW treeLimbs; omega),
          hTreeFoot _ (by omega) (by unfold arenaEnd arenaNb recW treeLimbs; omega),
          hTreeFoot _ (by rw [hnb]; unfold arenaNb; omega) (by rw [hK, hnb, hEndEq]; omega),
          fun i hi => hTreeFoot _ (by rw [hnb]; unfold arenaNb; omega) (by
            rw [hK] at hi; rw [hK, hnb, hEndEq]; omega)⟩)
  by_cases hFR0 : firstReb = 0
  · subst hFR0
    have hE0Range : (modelPre.chain.G 0).E = Finset.range (modelPre.chain.G 0).m := hBranchA rfl
    set mNew := (modelPre.chain.G 0).m
    have hmNewEq : mem (solverLevelG tok' mem 0 + 3) = mNew := by
      simpa [dgMOff] using hG0Ptr.2.2.2.2.2.2.1
    have hmNewLe : mNew ≤ B.eCap := by
      have : (modelPre.chain.G 0).E.card ≤ B.eCap := by
        rw [hE0Range, Finset.card_range]
        by_contra hgt
        have hmem : B.eCap ∈ (modelPre.chain.G 0).E := by rw [hE0Range, Finset.mem_range]; omega
        have := hG0Ptr.2.2.1 B.eCap hmem
        omega
      exact this
    have hLoopA :
        ∀ (rem : ℕ) (st : State),
          rem ≤ mNew →
          st.regs 1 = tok'.slots → st.regs 2 = tok'.edgeRecords →
          st.regs 3 = tok'.treeHeap → st.regs 4 = B.g0Ptr →
          st.regs 8 = L → st.regs 9 = scratch → st.regs 10 = mNew →
          st.regs 14 = mNew - rem →
          (∀ e < mNew - rem,
            Num.Valid st.mem (B.g0Ptr + e * L) 4 L ∧
            Num.fixVal st.mem (B.g0Ptr + e * L) 4 L P = modelPre.chain.g e) →
          (∀ a, a < B.g0Ptr ∨ B.g0Ptr + B.eCap * L ≤ a → st.mem a = mem a) →
          ∃ out c,
            Runs w p ω
              (forUp 14 (.reg 10)
                (.call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 14, .reg 8]))
              st .normal out c ∧
            out.regs 9 = scratch ∧
            (∀ e < mNew,
              Num.Valid out.mem (B.g0Ptr + e * L) 4 L ∧
              Num.fixVal out.mem (B.g0Ptr + e * L) 4 L P = modelPre.chain.g e) ∧
            (∀ a, a < B.g0Ptr ∨ B.g0Ptr + B.eCap * L ≤ a → out.mem a = mem a) ∧
            c ≤ rem * (45 * L + 160) + 10 := by
      intro rem
      induction rem with
      | zero =>
        intro st _ _ _ _ _ _ r9 r10 r14 hdone hfr
        rw [Nat.sub_zero] at r14 hdone
        refine ⟨st, _, runs_loop_f (by simp [Expr.eval, BinOp.eval, r10, r14]), r9, hdone, hfr,
          by simp [Expr.size]⟩
      | succ rem' ih =>
        intro st hrem r1 r2 r3 r4 r8 r9 r10 r14 hdone hfr
        set e := mNew - (rem' + 1)
        have heLt : e < mNew := by omega
        have heMem : e ∈ (modelPre.chain.G 0).E := by rw [hE0Range, Finset.mem_range]; exact heLt
        obtain ⟨z, hzEq, hRd0⟩ := hRdAll e heMem
        have hRdSt := hRdPres st.mem (fun a _ hng => hfr a (by
          unfold SelectBlocksLoc.regG0 SelectBlocksLoc.endAddr at hng; rw [hBLk] at hng; omega))
          e heMem z hRd0
        have heMul : e * L + L ≤ B.eCap * L := by
          have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt (lt_of_lt_of_le heLt hmNewLe))
          rwa [Nat.succ_mul] at this
        have hStep :
            ∃ st1 c1,
              Runs w p ω
                (.call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 14, .reg 8] ;;
                 .assign 14 (.bin .add (.reg 14) (.const 1)))
                st .normal st1 c1 ∧
              st1.regs 1 = tok'.slots ∧ st1.regs 2 = tok'.edgeRecords ∧
              st1.regs 3 = tok'.treeHeap ∧ st1.regs 4 = B.g0Ptr ∧
              st1.regs 8 = L ∧ st1.regs 9 = scratch ∧ st1.regs 10 = mNew ∧
              st1.regs 14 = e + 1 ∧
              PathIntAt st1.mem (B.g0Ptr + e * L) 4 L z ∧
              (∀ a, a < B.g0Ptr + e * L ∨ B.g0Ptr + (e + 1) * L ≤ a → st1.mem a = st.mem a) ∧
              c1 ≤ 45 * L + 150 := by
          have hLW : L < 2 ^ w := by
            have : L ≤ B.eCap * L := Nat.le_mul_of_pos_left _ (by omega); omega
          obtain ⟨bC, hbC, oC, stC, cC, hrC, hpC, hcC⟩ :=
            hCopyOne z [tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr, e, L] st.mem st.pos ω
              (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                  rintro v (rfl | rfl | rfl | rfl | rfl | rfl) <;>
                  [exact lt_of_le_of_lt (Nat.le_add_right _ _) hRdSt.2.2.2.1;
                   exact lt_of_le_of_lt (Nat.le_add_right _ _) hRdSt.2.2.2.2.1;
                   exact lt_of_le_of_lt (Nat.le_add_right _ _) hRdSt.2.2.2.2.2.1;
                   omega; omega; omega])
              ⟨tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr, e, L, rfl, hRdSt⟩
          obtain ⟨_, _, _, _, _, _, hargs, _, hP1, hfr1⟩ := hpC
          simp only [List.cons.injEq] at hargs
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
          set rg1 := Function.update st.regs 16 oC.value
          set rg2 := Function.update rg1 14 (e + 1)
          have hrc1 : Runs w p ω (.call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 14, .reg 8])
              st .normal ⟨stC.mem, rg1, stC.pos⟩ (cC + 7) :=
            runs_call_iff.mpr ⟨[tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr, e, L],
              bC, oC, stC, cC, by simp [evalArgs, Expr.eval, r1, r2, r3, r4, r8, r14, e],
              hbC, hrC, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
          have hrc2 : Runs w p ω (.assign 14 (.bin .add (.reg 14) (.const 1)))
              ⟨stC.mem, rg1, stC.pos⟩ .normal ⟨stC.mem, rg2, stC.pos⟩ 4 :=
            runs_assign_iff.mpr ⟨e + 1, by
              simp [Expr.eval, BinOp.eval, rg1, r14, e, show 1 < 2 ^ w by omega,
                show e + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
          refine ⟨⟨stC.mem, rg2, stC.pos⟩, (cC + 7) + 4 + 1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrc1, hrc2, rfl⟩),
            by simp [rg2, rg1, r1], by simp [rg2, rg1, r2], by simp [rg2, rg1, r3],
            by simp [rg2, rg1, r4], by simp [rg2, rg1, r8], by simp [rg2, rg1, r9],
            by simp [rg2, rg1, r10], by simp [rg2], hP1, hfr1, ?_⟩
          simp only [selCopyG0OneContract, List.getD_cons_zero, List.getD_cons_succ] at hcC
          omega
        obtain ⟨st1, c1, hr1, s1, s2, s3, s4, s8, s9, s10, s14, hP1, hfr1, hc1⟩ := hStep
        have he1 : mNew - rem' = e + 1 := by omega
        have hdone1 : ∀ i < e + 1,
            Num.Valid st1.mem (B.g0Ptr + i * L) 4 L ∧
            Num.fixVal st1.mem (B.g0Ptr + i * L) 4 L P = modelPre.chain.g i := by
          intro i hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hilt | rfl
          · have hmul : i * L + L ≤ e * L := by
              have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hilt)
              rwa [Nat.succ_mul] at this
            have hag : ∀ t < L, st1.mem (B.g0Ptr + i * L + t) = st.mem (B.g0Ptr + i * L + t) :=
              fun t ht => hfr1 _ (Or.inl (by omega))
            obtain ⟨hv, hfv⟩ := hdone i hilt
            exact ⟨fun t ht => (hag t ht) ▸ hv t ht, by
              unfold Num.fixVal; rw [Num.intVal_congr hag]; exact hfv⟩
          · exact ⟨hP1.1, by unfold Num.fixVal; rw [hP1.2]; exact hzEq⟩
        have hfrAll1 : ∀ a, a < B.g0Ptr ∨ B.g0Ptr + B.eCap * L ≤ a → st1.mem a = mem a :=
          fun a ha => (hfr1 a (by rw [Nat.succ_mul] at *; omega)).trans (hfr a ha)
        obtain ⟨out, c2, hr2, o9, odone, ofr, hc2⟩ :=
          ih st1 (by omega) s1 s2 s3 s4 s8 s9 s10 (by rw [he1]; exact s14)
            (by rw [he1]; exact hdone1) hfrAll1
        unfold forUp
        refine ⟨out, _, runs_loop_t (v := 1)
          (by simp [Expr.eval, BinOp.eval, r10, r14, heLt, show 1 < 2 ^ w by omega]) (by omega)
          hr1 hr2, o9, odone, ofr, ?_⟩
        simp only [Expr.size]; nlinarith
    suffices h : ∃ o out c,
        Runs w p ω
          (.assign 10 (.load (.bin .add (.reg 5) (.const 3))) ;;
           forRange 14 (.const 0) (.reg 10)
             (.call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 14, .reg 8]) ;;
           .ret (.reg 9))
          (startState [0, tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr,
            solverLevelG tok' mem 0, vCap, slot0, L, scratch] mem pos) o out c ∧
        (o = .returned scratch ∧
         SelBlocksDataAt out.mem B P
           { D with E0 := (modelPre.chain.G 0).E, g := modelPre.chain.g } pLast ∧
         ZeroFrom out.mem scratch ∧
         (∀ a < scratch, ¬ B.regG0 a → out.mem a = mem a)) ∧
        c ≤ selUpdateG0Cost 0 (modelPre.chain.G 0).m uG.length L - 2 by
      obtain ⟨_, out, c, hr, ⟨rfl, hblk', hz', hfr'⟩, hc⟩ := h
      have hFull : Runs w p ω (selUpdateG0Body copyOne filterPres)
          (startState [0, tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr,
            solverLevelG tok' mem 0, vCap, slot0, L, scratch] mem pos) (.returned scratch) out (c + 2) := by
        unfold selUpdateG0Body
        exact runs_cond_iff.mpr ⟨0, c, by simp [Expr.eval, startState], hr, by simp [Expr.size]; omega⟩
      exact ⟨scratch, c + 2, out, hFull, by simp [selUpdateG0Space], hblk', hz', hfr', by
        unfold selUpdateG0Cost at hc ⊢; simp at hc ⊢; omega⟩
    apply runs_start_le
    refine runs_seq_assign_flat (v := mNew)
      (by simp [Expr.eval, BinOp.eval, show 3 < 2 ^ w by omega,
            show solverLevelG tok' mem 0 + 3 < 2 ^ w by
              have : 4 ≤ dynGraphSize vCap B.eCap := by unfold dynGraphSize; omega
              omega,
            hmNewEq]) ?_
    let sA1 : State := ⟨mem, Function.update
      (Function.update (startState [0, tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr,
        solverLevelG tok' mem 0, vCap, slot0, L, scratch] mem pos).regs 10 mNew) 14 0, pos⟩
    obtain ⟨out, cL, hrL, o9, odone, ofr, hcL⟩ :=
      hLoopA mNew sA1 le_rfl (by simp [sA1, startState]) (by simp [sA1, startState])
        (by simp [sA1, startState]) (by simp [sA1, startState]) (by simp [sA1, startState])
        (by simp [sA1, startState]) (by simp [sA1]) (by simp [sA1])
        (fun _ h => by omega) (fun _ _ => rfl)
    have hrFor : Runs w p ω
        (forRange 14 (.const 0) (.reg 10)
          (.call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 14, .reg 8]))
        ⟨mem, Function.update (startState [0, tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr,
          solverLevelG tok' mem 0, vCap, slot0, L, scratch] mem pos).regs 10 mNew, pos⟩
        .normal out (2 + cL + 1) := by
      unfold forRange
      refine runs_seq_iff.mpr (Or.inr ⟨sA1, 2, cL,
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩,
        hrL, rfl⟩)
    have hrRet : Runs w p ω (.ret (.reg 9)) out (.returned scratch) out 2 :=
      runs_ret_iff.mpr ⟨scratch, by simp [Expr.eval, o9], rfl, rfl, by simp [Expr.size]⟩
    have hfrSc : ∀ a < scratch, ¬ B.regG0 a → out.mem a = mem a := fun a _ hng =>
      ofr a (by unfold SelectBlocksLoc.regG0 SelectBlocksLoc.endAddr at hng; rw [hBLk] at hng; omega)
    have hblk' : SelBlocksDataAt out.mem B P
        { D with E0 := (modelPre.chain.G 0).E, g := modelPre.chain.g } pLast := by
      refine hblk.setG0 (fun a hng => ofr a (by
        unfold SelectBlocksLoc.regG0 SelectBlocksLoc.endAddr at hng; rw [hBLk] at hng; omega))
        ⟨hG0Ptr.2.2.1, fun e he => ?_⟩
      have heLt : e < mNew := by rw [hE0Range, Finset.mem_range] at he; exact he
      rw [hBLk]; exact odone e heLt
    refine ⟨.returned scratch, out, (2 + cL + 1) + 2 + 1,
      runs_seq_iff.mpr (Or.inr ⟨out, 2 + cL + 1, 2, hrFor, hrRet, rfl⟩),
      ⟨rfl, hblk', fun a ha => (ofr a (Or.inr (by omega))).trans (hz a (by omega)), hfrSc⟩, ?_⟩
    dsimp only [mNew] at hcL
    simp [selUpdateG0Cost, Expr.size]; omega
  · -- Branch B: `firstReb ≠ 0`
    obtain ⟨hSlotLe, hUGLen, hUGAt, hUGLe, hUGOffG0, hUGCaps, hKeepG0⟩ := hBranchB hFR0
    set uGPtr := mem slot0
    set presBase := dgEPresBase (solverLevelG tok' mem 0) vCap
    set liveL := selPresent mem presBase uG
    have hLiveLen : liveL.length ≤ uG.length := List.length_filter_le _ _
    have hLiveMem : ∀ e, e ∈ liveL ↔ e ∈ uG ∧ e ∈ (modelPre.chain.G 0).E := by
      intro e
      simp only [liveL, selPresent, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨heU, hne⟩
        refine ⟨heU, ?_⟩
        by_contra hnot
        have h0 := hG0Ptr.2.2.2.2.2.2.2.2.2.2.2.1 e (hUGCaps e heU)
        simp only [hnot, ↓reduceIte] at h0
        exact hne h0
      · rintro ⟨heU, heG⟩
        refine ⟨heU, ?_⟩
        have h1 := hG0Ptr.2.2.2.2.2.2.2.2.2.2.2.1 e (hUGCaps e heU)
        simp only [heG, ↓reduceIte] at h1
        change mem (presBase + e) = 1 at h1
        omega
    have hLoopB :
        ∀ (rem : ℕ) (st : State),
          rem ≤ liveL.length →
          st.regs 1 = tok'.slots → st.regs 2 = tok'.edgeRecords →
          st.regs 3 = tok'.treeHeap → st.regs 4 = B.g0Ptr →
          st.regs 8 = L → st.regs 9 = scratch → st.regs 11 = uG.length →
          st.regs 13 = liveL.length → st.regs 14 = liveL.length - rem →
          ListAt st.mem scratch liveL →
          (∀ idx < liveL.length - rem,
            let e := liveL.getD idx 0
            Num.Valid st.mem (B.g0Ptr + e * L) 4 L ∧
            Num.fixVal st.mem (B.g0Ptr + e * L) 4 L P = modelPre.chain.g e) →
          (∀ e < B.eCap, e ∉ liveL → ∀ t < L,
            st.mem (B.g0Ptr + e * L + t) = mem (B.g0Ptr + e * L + t)) →
          (∀ a < scratch, ¬ B.regG0 a → st.mem a = mem a) →
          ZeroFrom st.mem (scratch + uG.length) →
          ∃ out c,
            Runs w p ω
              (forUp 14 (.reg 13)
                (.assign 15 (.load (.bin .add (.reg 9) (.reg 14))) ;;
                 .call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 15, .reg 8]))
              st .normal out c ∧
            out.regs 9 = scratch ∧ out.regs 11 = uG.length ∧
            (∀ e ∈ liveL,
              Num.Valid out.mem (B.g0Ptr + e * L) 4 L ∧
              Num.fixVal out.mem (B.g0Ptr + e * L) 4 L P = modelPre.chain.g e) ∧
            (∀ e < B.eCap, e ∉ liveL → ∀ t < L,
              out.mem (B.g0Ptr + e * L + t) = mem (B.g0Ptr + e * L + t)) ∧
            (∀ a < scratch, ¬ B.regG0 a → out.mem a = mem a) ∧
            ZeroFrom out.mem (scratch + uG.length) ∧
            c ≤ rem * (45 * L + 160) + 10 := by
      intro rem
      induction rem with
      | zero =>
        intro st _ _ _ _ _ _ r9 r11 r13 r14 _ hdone hnotL hfr hz1
        rw [Nat.sub_zero] at r14 hdone
        refine ⟨st, _, runs_loop_f (by simp [Expr.eval, BinOp.eval, r13, r14]), r9, r11,
          fun e he => ?_, hnotL, hfr, hz1, by simp [Expr.size]⟩
        obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem he
        have hd := hdone idx hidx
        simp only [List.getD, hidx, getElem?_pos, Option.getD_some] at hd
        exact hd
      | succ rem' ih =>
        intro st hrem r1 r2 r3 r4 r8 r9 r11 r13 r14 hListAt hdone hnotL hfr hz1
        set idx := liveL.length - (rem' + 1)
        have hidxLt : idx < liveL.length := by omega
        set e := liveL[idx]
        have heLive : e ∈ liveL := List.getElem_mem hidxLt
        have heMem : e ∈ (modelPre.chain.G 0).E := (hLiveMem e).mp heLive |>.2
        have heCap : e < B.eCap := hG0Ptr.2.2.1 e heMem
        have hMemIdx : st.mem (scratch + idx) = e := by
          have := hListAt idx hidxLt
          simpa [e] using this
        obtain ⟨z, hzEq, hRd0⟩ := hRdAll e heMem
        have hRdSt := hRdPres st.mem hfr e heMem z hRd0
        have heMul : e * L + L ≤ B.eCap * L := by
          have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heCap)
          rwa [Nat.succ_mul] at this
        have hStep :
            ∃ st1 c1,
              Runs w p ω
                ((.assign 15 (.load (.bin .add (.reg 9) (.reg 14))) ;;
                  .call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 15, .reg 8]) ;;
                 .assign 14 (.bin .add (.reg 14) (.const 1)))
                st .normal st1 c1 ∧
              st1.regs 1 = tok'.slots ∧ st1.regs 2 = tok'.edgeRecords ∧
              st1.regs 3 = tok'.treeHeap ∧ st1.regs 4 = B.g0Ptr ∧
              st1.regs 8 = L ∧ st1.regs 9 = scratch ∧ st1.regs 11 = uG.length ∧
              st1.regs 13 = liveL.length ∧ st1.regs 14 = idx + 1 ∧
              PathIntAt st1.mem (B.g0Ptr + e * L) 4 L z ∧
              (∀ a, a < B.g0Ptr + e * L ∨ B.g0Ptr + (e + 1) * L ≤ a → st1.mem a = st.mem a) ∧
              c1 ≤ 45 * L + 150 := by
          have hLW : L < 2 ^ w := by
            have : L ≤ B.eCap * L := Nat.le_mul_of_pos_left _ (by omega); omega
          have hroomB0 : scratch + uG.length < 2 ^ w := by
            unfold selUpdateG0Space at hroom; simp [hFR0] at hroom; exact hroom
          set rg1 := Function.update st.regs 15 e
          have hrc0 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 9) (.reg 14))))
              st .normal ⟨st.mem, rg1, st.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨e, by
              simp [Expr.eval, BinOp.eval, r9, r14, idx, hMemIdx,
                show scratch + idx < 2 ^ w by omega, show e < 2 ^ w by omega],
              rfl, rfl, by simp [Expr.size]⟩
          obtain ⟨bC, hbC, oC, stC, cC, hrC, hpC, hcC⟩ :=
            hCopyOne z [tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr, e, L] st.mem st.pos ω
              (by simp only [List.mem_cons, List.not_mem_nil, or_false]
                  rintro v (rfl | rfl | rfl | rfl | rfl | rfl) <;>
                  [exact lt_of_le_of_lt (Nat.le_add_right _ _) hRdSt.2.2.2.1;
                   exact lt_of_le_of_lt (Nat.le_add_right _ _) hRdSt.2.2.2.2.1;
                   exact lt_of_le_of_lt (Nat.le_add_right _ _) hRdSt.2.2.2.2.2.1;
                   omega; omega; omega])
              ⟨tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr, e, L, rfl, hRdSt⟩
          obtain ⟨_, _, _, _, _, _, hargs, _, hP1, hfr1⟩ := hpC
          simp only [List.cons.injEq] at hargs
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hargs
          set rg2 := Function.update rg1 16 oC.value
          set rg3 := Function.update rg2 14 (idx + 1)
          have hrc1 : Runs w p ω (.call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 15, .reg 8])
              ⟨st.mem, rg1, st.pos⟩ .normal ⟨stC.mem, rg2, stC.pos⟩ (cC + 7) :=
            runs_call_iff.mpr ⟨[tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr, e, L],
              bC, oC, stC, cC, by simp [evalArgs, Expr.eval, rg1, r1, r2, r3, r4, r8],
              hbC, hrC, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
          have hrc2 : Runs w p ω (.assign 14 (.bin .add (.reg 14) (.const 1)))
              ⟨stC.mem, rg2, stC.pos⟩ .normal ⟨stC.mem, rg3, stC.pos⟩ 4 :=
            runs_assign_iff.mpr ⟨idx + 1, by
              simp [Expr.eval, BinOp.eval, rg2, rg1, r14, idx, show 1 < 2 ^ w by omega,
                show idx + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
          refine ⟨⟨stC.mem, rg3, stC.pos⟩, (5 + (cC + 7) + 1) + 4 + 1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrc0, hrc1, rfl⟩), hrc2, rfl⟩),
            by simp [rg3, rg2, rg1, r1], by simp [rg3, rg2, rg1, r2], by simp [rg3, rg2, rg1, r3],
            by simp [rg3, rg2, rg1, r4], by simp [rg3, rg2, rg1, r8], by simp [rg3, rg2, rg1, r9],
            by simp [rg3, rg2, rg1, r11], by simp [rg3, rg2, rg1, r13], by simp [rg3], hP1, hfr1, ?_⟩
          simp only [selCopyG0OneContract, List.getD_cons_zero, List.getD_cons_succ] at hcC
          omega
        obtain ⟨st1, c1, hr1, s1, s2, s3, s4, s8, s9, s11, s13, s14, hP1, hfr1, hc1⟩ := hStep
        have hidx1 : liveL.length - rem' = idx + 1 := by omega
        have hListAt1 : ListAt st1.mem scratch liveL := fun k hk =>
          (hfr1 (scratch + k) (Or.inr (by rw [Nat.succ_mul] at *; omega))).trans (hListAt k hk)
        have hdone1 : ∀ j < idx + 1,
            let ej := liveL.getD j 0
            Num.Valid st1.mem (B.g0Ptr + ej * L) 4 L ∧
            Num.fixVal st1.mem (B.g0Ptr + ej * L) 4 L P = modelPre.chain.g ej := by
          intro j hj
          dsimp only
          set ej := liveL.getD j 0
          by_cases hEqE : ej = e
          · rw [hEqE]
            exact ⟨hP1.1, by unfold Num.fixVal; rw [hP1.2]; exact hzEq⟩
          · have hjlt : j < idx := by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
              · exact h
              · exfalso; apply hEqE; simp [ej, List.getD, hidxLt, e]
            have hag : ∀ t < L, st1.mem (B.g0Ptr + ej * L + t) = st.mem (B.g0Ptr + ej * L + t) := by
              intro t ht
              apply hfr1
              rcases lt_or_gt_of_ne hEqE with hlt | hgt
              · left
                have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt)
                rw [Nat.succ_mul] at this; omega
              · right
                have : (e + 1) * L ≤ ej * L := Nat.mul_le_mul_right L hgt
                omega
            obtain ⟨hv, hfv⟩ := hdone j hjlt
            exact ⟨fun t ht => (hag t ht) ▸ hv t ht, by
              unfold Num.fixVal; rw [Num.intVal_congr hag]; exact hfv⟩
        have hnotL1 : ∀ x < B.eCap, x ∉ liveL → ∀ t < L,
            st1.mem (B.g0Ptr + x * L + t) = mem (B.g0Ptr + x * L + t) := by
          intro x hx hxn t ht
          have hne : x ≠ e := fun h => hxn (h ▸ heLive)
          have h1 : st1.mem (B.g0Ptr + x * L + t) = st.mem (B.g0Ptr + x * L + t) := by
            apply hfr1
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · left
              have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt)
              rw [Nat.succ_mul] at this; omega
            · right
              have : (e + 1) * L ≤ x * L := Nat.mul_le_mul_right L hgt
              omega
          exact h1.trans (hnotL x hx hxn t ht)
        have hfrAll1 : ∀ a < scratch, ¬ B.regG0 a → st1.mem a = mem a := fun a ha hng =>
          (hfr1 a (by
            unfold SelectBlocksLoc.regG0 SelectBlocksLoc.endAddr at hng
            rw [hBLk] at hng; rw [Nat.succ_mul] at *; omega)).trans (hfr a ha hng)
        have hz2 : ZeroFrom st1.mem (scratch + uG.length) := fun a ha =>
          (hfr1 a (Or.inr (by rw [Nat.succ_mul] at *; omega))).trans (hz1 a ha)
        obtain ⟨out, c2, hr2, o9, o11, odone, onotL, ofr, oz, hc2⟩ :=
          ih st1 (by omega) s1 s2 s3 s4 s8 s9 s11 s13 (by rw [hidx1]; exact s14)
            hListAt1 (by rw [hidx1]; exact hdone1) hnotL1 hfrAll1 hz2
        unfold forUp
        refine ⟨out, _, runs_loop_t (v := 1)
          (by simp [Expr.eval, BinOp.eval, r13, r14, hidxLt, show 1 < 2 ^ w by omega]) (by omega)
          hr1 hr2, o9, o11, odone, onotL, ofr, oz, ?_⟩
        simp only [Expr.size]; nlinarith
    have hroomB : scratch + uG.length < 2 ^ w := by
      unfold selUpdateG0Space at hroom; simp [hFR0] at hroom; exact hroom
    suffices h : ∃ o out c,
        Runs w p ω
          (.assign 10 (.load (.reg 7)) ;;
           .assign 11 (.load (.bin .add (.reg 7) (.const 1))) ;;
           .assign 12 (.bin .add (.bin .add (.reg 5) (.const 4)) (.bin .mul (.const 7) (.reg 6))) ;;
           .call 13 filterPres [.reg 10, .reg 11, .reg 12, .reg 9] ;;
           forRange 14 (.const 0) (.reg 13)
             (.assign 15 (.load (.bin .add (.reg 9) (.reg 14))) ;;
              .call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 15, .reg 8]) ;;
           .ret (.bin .add (.reg 9) (.reg 11)))
          (startState [firstReb, tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr,
            solverLevelG tok' mem 0, vCap, slot0, L, scratch] mem pos) o out c ∧
        (o = .returned (scratch + uG.length) ∧
         SelBlocksDataAt out.mem B P
           { D with E0 := (modelPre.chain.G 0).E, g := modelPre.chain.g } pLast ∧
         ZeroFrom out.mem (scratch + uG.length) ∧
         (∀ a < scratch, ¬ B.regG0 a → out.mem a = mem a)) ∧
        c ≤ selUpdateG0Cost firstReb (modelPre.chain.G 0).m uG.length L - 2 by
      obtain ⟨_, out, c, hr, ⟨rfl, hblk', hz', hfr'⟩, hc⟩ := h
      have hFull : Runs w p ω (selUpdateG0Body copyOne filterPres)
          (startState [firstReb, tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr,
            solverLevelG tok' mem 0, vCap, slot0, L, scratch] mem pos)
          (.returned (scratch + uG.length)) out (c + 2) := by
        unfold selUpdateG0Body
        refine runs_cond_iff.mpr ⟨firstReb, c, by simp [Expr.eval, startState], ?_, by simp [Expr.size]; omega⟩
        simp only [hFR0, ↓reduceIte]; exact hr
      exact ⟨scratch + uG.length, c + 2, out, hFull, by simp [selUpdateG0Space, hFR0], hblk', hz', hfr', by
        unfold selUpdateG0Cost at hc ⊢; simp [hFR0] at hc ⊢; omega⟩
    apply runs_start_le
    refine runs_seq_assign_flat (v := uGPtr)
      (by simp [Expr.eval, show slot0 < 2 ^ w by omega,
            show uGPtr < 2 ^ w by omega, uGPtr]) ?_
    refine runs_seq_assign_flat (v := uG.length)
      (by simp [Expr.eval, BinOp.eval, show 1 < 2 ^ w by omega,
            show slot0 + 1 < 2 ^ w by omega, hUGLen, show uG.length < 2 ^ w by omega]) ?_
    refine runs_seq_assign_flat (v := presBase)
      (by simp [Expr.eval, BinOp.eval, show 4 < 2 ^ w by omega,
            show 7 < 2 ^ w by omega, show solverLevelG tok' mem 0 + 4 < 2 ^ w by
              unfold dynGraphSize at hG0Le; omega,
            show 7 * vCap < 2 ^ w by unfold dynGraphSize at hG0Le; omega,
            show solverLevelG tok' mem 0 + 4 + 7 * vCap < 2 ^ w by
              unfold dynGraphSize at hG0Le; omega,
            presBase, dgEPresBase]) ?_
    refine runs_seq_call_flat hFilter
      (by simp [evalArgs, Expr.eval])
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro v (rfl | rfl | rfl | rfl) <;>
          [omega; omega;
           (unfold dynGraphSize at hG0Le; unfold presBase dgEPresBase; omega); omega])
      ⟨uGPtr, presBase, scratch, rfl, hw16, by omega, hroomB, Or.inl hUGLe, hUGAt,
        fun e he => by
          have heCap : e < B.eCap := hUGCaps e he
          have hpLt : presBase + e < scratch := by
            unfold dynGraphSize at hG0Le; unfold presBase dgEPresBase; omega
          have hval : mem (presBase + e) < 2 ^ w := by
            have := hG0Ptr.2.2.2.2.2.2.2.2.2.2.2.1 e heCap
            change mem (presBase + e) = _ at this
            rw [this]; split_ifs <;> omega
          exact ⟨by omega, by omega, hval, Or.inl hpLt⟩⟩ ?_
    intro cnt mem1 pos1 hpostF
    obtain ⟨_, _, _, hargsF, hcntEq, hList1, hfrF⟩ := hpostF
    simp only [List.cons.injEq] at hargsF
    obtain ⟨rfl, -, rfl, rfl, -⟩ := hargsF
    subst hcntEq
    let rgB0 := Function.update (Function.update (Function.update (Function.update
      (startState [firstReb, tok'.slots, tok'.edgeRecords, tok'.treeHeap, B.g0Ptr,
        solverLevelG tok' mem 0, vCap, slot0, L, scratch] mem pos).regs
      10 uGPtr) 11 uG.length) 12 presBase) 13 liveL.length
    let sB1 : State := ⟨mem1, Function.update rgB0 14 0, pos1⟩
    obtain ⟨out, cL, hrL, o9, o11, odone, onotL, ofr, oz, hcL⟩ :=
      hLoopB liveL.length sB1 le_rfl (by simp [sB1, rgB0, startState])
        (by simp [sB1, rgB0, startState]) (by simp [sB1, rgB0, startState])
        (by simp [sB1, rgB0, startState]) (by simp [sB1, rgB0, startState])
        (by simp [sB1, rgB0, startState]) (by simp [sB1, rgB0]) (by simp [sB1, rgB0])
        (by simp [sB1]) hList1
        (fun _ h => by omega)
        (fun e he _ t ht => hfrF (B.g0Ptr + e * L + t) (Or.inl (by
          have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
          rw [Nat.succ_mul] at this; omega)))
        (fun a ha _ => hfrF a (Or.inl ha))
        (fun a ha => (hfrF a (Or.inr ha)).trans (hz a (by omega)))
    have hrFor : Runs w p ω
        (forRange 14 (.const 0) (.reg 13)
          (.assign 15 (.load (.bin .add (.reg 9) (.reg 14))) ;;
           .call 16 copyOne [.reg 1, .reg 2, .reg 3, .reg 4, .reg 15, .reg 8]))
        ⟨mem1, rgB0, pos1⟩ .normal out (2 + cL + 1) := by
      unfold forRange
      refine runs_seq_iff.mpr (Or.inr ⟨sB1, 2, cL,
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩,
        hrL, rfl⟩)
    have hrRet : Runs w p ω (.ret (.bin .add (.reg 9) (.reg 11))) out
        (.returned (scratch + uG.length)) out 4 :=
      runs_ret_iff.mpr ⟨scratch + uG.length, by simp [Expr.eval, BinOp.eval, o9, o11, hroomB],
        rfl, rfl, by simp [Expr.size]⟩
    have hblk' : SelBlocksDataAt out.mem B P
        { D with E0 := (modelPre.chain.G 0).E, g := modelPre.chain.g } pLast := by
      have hG0Lt : B.g0Ptr ≤ scratch := by
        have : B.g0Ptr ≤ B.endAddr := by unfold SelectBlocksLoc.endAddr; omega
        omega
      have hAgPre : ∀ a < B.g0Ptr, out.mem a = mem a := fun a ha =>
        ofr a (by omega) (fun hg => by unfold SelectBlocksLoc.regG0 at hg; omega)
      have hLastLt : B.lastGPtr ≤ B.g0Ptr := by unfold SelectBlocksLoc.g0Ptr; omega
      obtain ⟨hF, hPhi, hLen, hEmb, hLast, hG0Old⟩ := hblk
      refine ⟨fun j' hj' => (hF j' hj').of_agree fun a ha =>
          hAgPre a (by have := B.blk_le_last hj'; have := B.regF_blk ha; unfold SelectBlocksLoc.regBlk at this; omega),
        fun j' hj' => (hPhi j' hj').of_agree fun a ha =>
          hAgPre a (by have := B.blk_le_last hj'; have := B.regPhi_blk ha; unfold SelectBlocksLoc.regBlk at this; omega),
        fun j' hj' => (hLen j' hj').of_agree fun a ha =>
          hAgPre a (by have := B.blk_le_last hj'; have := B.regLen_blk ha; unfold SelectBlocksLoc.regBlk at this; omega),
        fun j' hj' => (hEmb j' hj').of_agree fun a ha =>
          hAgPre a (by have := B.blk_le_last hj'.le; have := B.regEmb_blk ha; unfold SelectBlocksLoc.regBlk at this; omega),
        hLast.of_agree fun a ha => hAgPre a ha.2,
        ⟨hG0Ptr.2.2.1, fun e he => ?_⟩⟩
      rw [hBLk]
      by_cases heL : e ∈ liveL
      · exact odone e heL
      · have heNotU : e ∉ uG := fun hu => heL ((hLiveMem e).mpr ⟨hu, he⟩)
        obtain ⟨heOld, hgSame⟩ := hKeepG0 e he heNotU
        have hOld := hG0Old.2 e heOld
        rw [hBLk] at hOld
        have hag := onotL e (hG0Ptr.2.2.1 e he) heL
        exact ⟨fun t ht => (hag t ht) ▸ hOld.1 t ht, by
          dsimp only; unfold Num.fixVal; rw [Num.intVal_congr hag, hgSame]; exact hOld.2⟩
    refine ⟨.returned (scratch + uG.length), out, (2 + cL + 1) + 4 + 1,
      runs_seq_iff.mpr (Or.inr ⟨out, 2 + cL + 1, 4, hrFor, hrRet, rfl⟩),
      ⟨rfl, hblk', oz, ofr⟩, ?_⟩
    simp [selUpdateG0Cost, selFilterPresentContract, hFR0, Expr.size, argsSize]
    nlinarith

end MinCostFlow.MinRatio
