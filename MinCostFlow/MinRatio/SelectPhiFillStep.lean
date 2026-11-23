module

public import MinCostFlow.MinRatio.SelectPhiFillDefs
public import MinCostFlow.MinRatio.SelectBlocksSplit
import MinCostFlow.LSF.Walks
import WordRAM.Tactic

/-!
# Verification of `phiFillEdgeStepBody` and BFS invariant lemmas (`SelectPhiFillStep`)

Provides:
* `phiFillEdgeStep_meetsContract`: verifies `phiFillEdgeStepBody` against
  `phiFillEdgeStepContract` in `O((j + 1) * Lk)` steps and `(3 * j + 3) * Lk` scratch words.
* `PhiFillBfsInv`: the shared BFS state invariant tracking discovered vertices `q`, queue head
  `qHead`, current potential map `φcur`, and ghost component-root map `rootOf`.
* Pure transition lemmas for `PhiFillBfsInv`: `initial`, `seedRoot`, `discoverChild`,
  `finishParent`, and `finishAll` (which extracts `EdgeValuesAt`, the tree-edge difference
  equation, `SelectPotInvAt`, and the root-path formula).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Shared BFS state invariant `PhiFillBfsInv` -/

/-- Shared BFS state invariant for `phiFillAdjLoopBody`, `phiFillBfsLoopBody`, and
`phiFillOuterLoopBody` on forest `F = (C.activeLSF j).F.F` with live vertex list `vL` and
scratch base `scratch0`. -/
def PhiFillBfsInv (mem mem0 : ℕ → ℕ) (mloc : SelectLevelMetaLoc) (h P j scratch0 : ℕ)
    (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) (F : MGraph) (vL : List ℕ)
    (q : List ℕ) (qHead sc : ℕ) (φcur : ℕ → ℝ) (rootOf : ℕ → ℕ) : Prop :=
  q.Nodup ∧
  (∀ v ∈ q, v ∈ F.V) ∧
  qHead ≤ q.length ∧
  mem scratch0 = q.length ∧
  ListAt mem (scratch0 + 1 + F.n) q ∧
  (∀ i (hi : i < vL.length), mem (scratch0 + 1 + i) = if vL[i] ∈ q then 1 else 0) ∧
  EdgeValuesAt mem (mloc.phiPtr j) h mloc.Lk P q.toFinset φcur ∧
  (∀ v ∈ q, rootOf v ∈ q ∧ F.Connected v (rootOf v) ∧
    (∀ u ∈ F.walkVertices v (F.forestPath v (rootOf v)), u ∈ q) ∧
    φcur v = walkInner (potGrad C g φ j) (F.forestPath v (rootOf v))) ∧
  (∀ u ∈ q, ∀ v ∈ q, F.Connected u v → rootOf u = rootOf v) ∧
  (∀ u ∈ q.take qHead, ∀ e ∈ F.E,
    (F.tail e = u → F.head e ∈ q) ∧ (F.head e = u → F.tail e ∈ q)) ∧
  scratch0 + 1 + 2 * F.n ≤ sc ∧
  sc ≤ scratch0 + 1 + 2 * F.n + q.length * phiFillEdgeStepSpace j mloc.Lk ∧
  ZeroFrom mem sc ∧
  (∀ a < scratch0,
    (a < mloc.phiPtr j ∨ mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ a) →
    mem a = mem0 a)

/-- Remaining un-popped vertex degree volume in `F` outside `(q.take qHead).toFinset`. -/
def phiFillRemVol (F : MGraph) (q : List ℕ) (qHead : ℕ) : ℕ :=
  ∑ u ∈ F.V \ (q.take qHead).toFinset, F.deg u

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 2. Verification of `phiFillEdgeStepBody` -/

private lemma mul_add_le_mul_step {v c L : ℕ} (hv : v < c) :
    v * L + L ≤ c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at this
  exact this

private lemma entry_disj_step {a b L : ℕ} (hne : a ≠ b) :
    a * L + L ≤ b * L ∨ b * L + L ≤ a * L := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · left; exact mul_add_le_mul_step hlt
  · right; exact mul_add_le_mul_step hgt

private lemma base_lt_word_step {w h : ℕ} (hw : 2 * h + 2 ≤ w) :
    Num.base h < 2 ^ w := by
  unfold Num.base
  exact Nat.pow_lt_pow_right (by decide) (by omega)

/-- `phiFillEdgeStepBody` meets `phiFillEdgeStepContract`. -/
theorem phiFillEdgeStep_meetsContract {w h P proc evalLvlProc addProc subProc copyTo : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {p : Program}
    (hp : p.procs[proc]? = some (phiFillEdgeStepBody evalLvlProc addProc subProc copyTo))
    (heval : MeetsContract w p evalLvlProc (evalLevelPotGradContract w h P mloc C g φ))
    (hadd : MeetsContract w p addProc (Num.addContract w h))
    (hsub : MeetsContract w p subProc (Num.subtractContract w h))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w)) :
    MeetsContract w p proc (phiFillEdgeStepContract w h P mloc C g φ) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨j, f, parent, child, dir, scratch, rfl, hw16, hh, hw2, hjD, hf0, hfCap0, hfAll,
    hparCap, hchCap, hnePC, hphiJM, hPref, hBel, hDisj, hvPar, hFitsE, hFitsC, hz, hroom⟩ := hpre
  have hbaseW : Num.base h < 2 ^ w := base_lt_word_step hw2
  have hw1 : 1 < 2 ^ w := by omega
  have hmetaW : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hjW : j < 2 ^ w := hwords j (by simp)
  have hfW : f < 2 ^ w := hwords f (by simp)
  have hparW : parent < 2 ^ w := hwords parent (by simp)
  have hchW : child < 2 ^ w := hwords child (by simp)
  have hdirW : dir < 2 ^ w := hwords dir (by simp)
  have hLkW : mloc.Lk < 2 ^ w := hwords mloc.Lk (by simp)
  have hscW : scratch < 2 ^ w := hwords scratch (by simp)
  have hsmSz : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
  have hmetaHi : mloc.metaBase + selectLevelMetaSize mloc.d ≤ scratch := hBel.1
  have hphiHi : mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ scratch := hDisj.1
  have hparEnd : mloc.phiPtr j + parent * mloc.Lk + mloc.Lk ≤ scratch := by
    have := mul_add_le_mul_step (L := mloc.Lk) hparCap; omega
  have hchEnd : mloc.phiPtr j + child * mloc.Lk + mloc.Lk ≤ scratch := by
    have := mul_add_le_mul_step (L := mloc.Lk) hchCap; omega
  have hsp : phiFillEdgeStepSpace j mloc.Lk = (3 * j + 3) * mloc.Lk := rfl
  have hsc1W : scratch + mloc.Lk < 2 ^ w := by
    have : 3 * mloc.Lk ≤ (3 * j + 3) * mloc.Lk := Nat.mul_le_mul_right _ (by omega)
    omega
  have hdEq : mloc.d = C.d := hPref.1
  have hmd_lt : mloc.metaBase + smDOff < 2 ^ w := by unfold smDOff; omega
  have hd1_lt : mloc.d + 1 < 2 ^ w := by omega
  have h3d1_lt : 3 * (mloc.d + 1) < 2 ^ w := by omega
  have hphiEntry_lt : mloc.metaBase + smTableOff + (3 * (mloc.d + 1) + j) < 2 ^ w := by
    unfold smTableOff; omega
  have hphiJM' : mem (mloc.metaBase + smTableOff + (3 * (mloc.d + 1) + j)) = mloc.phiPtr j := by
    simpa [smEntryAddr, Nat.add_assoc] using hphiJM
  have hparPtrW : mloc.phiPtr j + parent * mloc.Lk < 2 ^ w := by omega
  have hchPtrW : mloc.phiPtr j + child * mloc.Lk < 2 ^ w := by omega
  have hparMulW : parent * mloc.Lk < 2 ^ w := by omega
  have hchMulW : child * mloc.Lk < 2 ^ w := by omega
  apply runs_start_le
  dsimp only [startState]
  unfold phiFillEdgeStepBody
  refine runs_seq_assign_flat (v := mloc.d)
    (Expr.eval_load_of_eq (by eval_expr) hPref.2.2.1) ?_
  refine runs_seq_assign_flat (v := mloc.phiPtr j)
    (Expr.eval_load_of_eq (by eval_expr) hphiJM') ?_
  refine runs_seq_assign_flat (v := mloc.phiPtr j + parent * mloc.Lk) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := mloc.phiPtr j + child * mloc.Lk) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := scratch + mloc.Lk) (by eval_expr) ?_
  -- Call evalLvlProc [meta, j, f, scratch, Lk, scratch + Lk]
  have hevalRoom : scratch + mloc.Lk + evalLevelPotGradSpace j mloc.Lk < 2 ^ w := by
    unfold evalLevelPotGradSpace
    have : mloc.Lk + j * (3 * mloc.Lk) + 2 * mloc.Lk = (3 * j + 3) * mloc.Lk := by ring
    omega
  refine runs_seq_call_flat heval
    (vs := [mloc.metaBase, j, f, scratch, mloc.Lk, scratch + mloc.Lk])
    (by eval_expr) (by wram_words)
    ⟨j, f, scratch, scratch + mloc.Lk, rfl, hw16, hh, hw2, hjD, hf0, hfCap0, hfAll,
      hPref, hBel, le_rfl, hFitsE, fun a ha => hz a (by omega), hevalRoom⟩ ?_
  intro sc2 mem1 pos1 hp1
  obtain ⟨hsc2Eq, hvEdge1, hfixEdge1, hz1, hfr1⟩ := hp1
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hsc2Eq hvEdge1 hfixEdge1 hz1 hfr1
  have hsc2Val : sc2 = scratch + mloc.Lk + j * (3 * mloc.Lk) := by
    simpa [evalLevelPotGradSpace] using hsc2Eq
  have hsc2W : sc2 < 2 ^ w := by omega
  have hvPar1 : Num.Valid mem1 (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk :=
    fun i hi => by rw [hfr1 _ (by omega) (Or.inl (by omega))]; exact hvPar i hi
  have hparInt1 : Num.intVal mem1 (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk =
      Num.intVal mem (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk :=
    Num.intVal_congr fun i hi => hfr1 _ (by omega) (Or.inl (by omega))
  have hfr1_below : ∀ a < scratch, mem1 a = mem a := fun a ha =>
    hfr1 a (by omega) (Or.inl ha)
  have hsc2AddW : sc2 + mloc.Lk < 2 ^ w := by
    have : mloc.Lk + j * (3 * mloc.Lk) + 2 * mloc.Lk = (3 * j + 3) * mloc.Lk := by ring
    omega
  have hsc2SubW : sc2 + 2 * mloc.Lk < 2 ^ w := by
    have : mloc.Lk + j * (3 * mloc.Lk) + 2 * mloc.Lk = (3 * j + 3) * mloc.Lk := by ring
    omega
  refine WordRAM.runs_cond_le (v := dir) (by eval_expr) ?_ ?_
  · -- dir ≠ 0: add parent + edge
    intro hnz
    refine runs_seq_call_flat hadd
      (vs := [mloc.phiPtr j + parent * mloc.Lk, scratch, mloc.Lk, sc2])
      (by eval_expr) (by wram_words)
      ⟨mloc.phiPtr j + parent * mloc.Lk, scratch, mloc.Lk, sc2, rfl,
        ⟨mloc.phiPtr j + parent * mloc.Lk, scratch, mloc.Lk, 0, sc2, rfl,
          by omega, by omega, Nat.zero_le 1, hvPar1, hvEdge1⟩,
        hz1, by change sc2 + mloc.Lk < 2 ^ w; exact hsc2AddW⟩ ?_
    intro sc3 mem2 pos2 hp2
    rcases hp2 with ⟨hsc3Eq, _, _, hf2, hz2, hlist2⟩
    change sc3 = sc2 + mloc.Lk at hsc3Eq
    change (∀ x < sc2, mem2 x = mem1 x) at hf2
    change ZeroFrom mem2 sc3 at hz2
    change ListAt mem2 sc2 (Num.digits h mloc.Lk
      (Num.unsignedVal mem1 (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk +
        Num.unsignedVal mem1 scratch h mloc.Lk + 0)) at hlist2
    have hsc3W : sc3 < 2 ^ w := hsc3Eq ▸ hsc2AddW
    have hvRes2 : Num.Valid mem2 sc2 h mloc.Lk := by
      have hv := Num.valid_listAt hlist2 (Num.digits_lt _ _ _)
      simpa [Num.digits_length] using hv
    have hvalRes2 : Num.intVal mem2 sc2 h mloc.Lk =
        Num.intVal mem (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk +
          Num.intVal mem1 scratch h mloc.Lk := by
      have hfit : Num.Fits h mloc.Lk
          (Num.intVal mem (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk +
            Num.intVal mem1 scratch h mloc.Lk) := by
        refine fits_of_real_scaled (P := P)
          (x := Num.fixVal mem (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk P + potGrad C g φ j f)
          ?_ (by simpa [hnz] using hFitsC.1) (by simpa [hnz] using hFitsC.2)
        rw [← hfixEdge1]
        unfold Num.fixVal
        push_cast
        ring
      have hwrap := (Num.addCarry_value (h := h) (L := mloc.Lk) (c := 0) hlist2).2
      rw [hparInt1] at hwrap
      simpa only [Nat.cast_zero, add_zero, Num.wrap_of_fits hfit] using hwrap
    refine runs_seq_call_flat hcopy
      (vs := [sc2, mloc.phiPtr j + child * mloc.Lk, mloc.Lk])
      (by eval_expr) (by wram_words)
      ⟨sc2, mloc.phiPtr j + child * mloc.Lk, mloc.Lk, rfl, hw1, hsc2AddW, by omega,
        Or.inr (by omega), fun i hi => lt_trans (hvRes2 i hi) hbaseW⟩ ?_
    intro _ mem3 pos3 hp3
    obtain ⟨_, hcp3, hfr3⟩ := hp3
    change (∀ i < mloc.Lk, mem3 (mloc.phiPtr j + child * mloc.Lk + i) = mem2 (sc2 + i)) at hcp3
    change (∀ a, (a < mloc.phiPtr j + child * mloc.Lk ∨
      mloc.phiPtr j + child * mloc.Lk + mloc.Lk ≤ a) → mem3 a = mem2 a) at hfr3
    refine WordRAM.runs_ret_le (v := sc3) (by eval_expr) ?_ ?_
    · dsimp only [phiFillEdgeStepContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
      have hspLe : sc3 ≤ scratch + phiFillEdgeStepSpace j mloc.Lk := by
        unfold phiFillEdgeStepSpace
        have : mloc.Lk + j * (3 * mloc.Lk) + 2 * mloc.Lk = (3 * j + 3) * mloc.Lk := by ring
        omega
      refine ⟨by omega, hspLe, fun i hi => (hcp3 i hi) ▸ hvRes2 i hi, ?_,
        fun a ha => (hfr3 a (Or.inr (by omega))).trans (hz2 a ha),
        fun a ha hout => (hfr3 a hout).trans ((hf2 a (by omega)).trans (hfr1_below a ha))⟩
      rw [ite_eq_left hnz]
      unfold Num.fixVal
      rw [Num.intVal_congr hcp3, hvalRes2, ← hfixEdge1]
      unfold Num.fixVal
      push_cast
      ring
    · simp only [phiFillEdgeStepContract, evalLevelPotGradContract, Num.addContract,
        copyLimbsToContract, phiFillEdgeStepCost, evalLevelPotGradCost,
        List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size]
      omega
  · -- dir = 0: subtract parent - edge
    intro hzDir
    refine runs_seq_call_flat hsub
      (vs := [mloc.phiPtr j + parent * mloc.Lk, scratch, mloc.Lk, sc2])
      (by eval_expr) (by wram_words)
      ⟨⟨mloc.phiPtr j + parent * mloc.Lk, scratch, mloc.Lk, sc2, rfl,
        by omega, by omega, hvPar1, hvEdge1⟩,
        hz1, by change sc2 + 2 * mloc.Lk < 2 ^ w; exact hsc2SubW⟩ ?_
    intro sc3 mem2 pos2 hp2
    rcases hp2 with ⟨hsc3Eq, _, _, hf2, hz2, hvRes2, hvalRes2⟩
    change sc3 = sc2 + 2 * mloc.Lk at hsc3Eq
    change (∀ x < sc2, mem2 x = mem1 x) at hf2
    change ZeroFrom mem2 sc3 at hz2
    change Num.Valid mem2 (sc2 + mloc.Lk) h mloc.Lk at hvRes2
    change Num.intVal mem2 (sc2 + mloc.Lk) h mloc.Lk =
      Num.wrap h mloc.Lk (Num.intVal mem1 (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk -
        Num.intVal mem1 scratch h mloc.Lk) at hvalRes2
    have hsc3W : sc3 < 2 ^ w := hsc3Eq ▸ hsc2SubW
    have hvalExact2 : Num.intVal mem2 (sc2 + mloc.Lk) h mloc.Lk =
        Num.intVal mem (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk -
          Num.intVal mem1 scratch h mloc.Lk := by
      rw [hvalRes2, hparInt1]
      have hfit : Num.Fits h mloc.Lk
          (Num.intVal mem (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk -
            Num.intVal mem1 scratch h mloc.Lk) := by
        refine fits_of_real_scaled (P := P)
          (x := Num.fixVal mem (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk P - potGrad C g φ j f)
          ?_ (by simpa [hzDir] using hFitsC.1) (by simpa [hzDir] using hFitsC.2)
        rw [← hfixEdge1]
        unfold Num.fixVal
        push_cast
        ring
      exact Num.wrap_of_fits hfit
    refine runs_seq_call_flat hcopy
      (vs := [sc2 + mloc.Lk, mloc.phiPtr j + child * mloc.Lk, mloc.Lk])
      (by eval_expr) (by wram_words)
      ⟨sc2 + mloc.Lk, mloc.phiPtr j + child * mloc.Lk, mloc.Lk, rfl, hw1,
        by omega, by omega, Or.inr (by omega), fun i hi => lt_trans (hvRes2 i hi) hbaseW⟩ ?_
    intro _ mem3 pos3 hp3
    obtain ⟨_, hcp3, hfr3⟩ := hp3
    change (∀ i < mloc.Lk, mem3 (mloc.phiPtr j + child * mloc.Lk + i) = mem2 (sc2 + mloc.Lk + i)) at hcp3
    change (∀ a, (a < mloc.phiPtr j + child * mloc.Lk ∨
      mloc.phiPtr j + child * mloc.Lk + mloc.Lk ≤ a) → mem3 a = mem2 a) at hfr3
    refine WordRAM.runs_ret_le (v := sc3) (by eval_expr) ?_ ?_
    · dsimp only [phiFillEdgeStepContract]
      simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
      have hspLe : sc3 ≤ scratch + phiFillEdgeStepSpace j mloc.Lk := by
        unfold phiFillEdgeStepSpace
        have : mloc.Lk + j * (3 * mloc.Lk) + 2 * mloc.Lk = (3 * j + 3) * mloc.Lk := by ring
        omega
      refine ⟨by omega, hspLe, fun i hi => (hcp3 i hi) ▸ hvRes2 i hi, ?_,
        fun a ha => (hfr3 a (Or.inr (by omega))).trans (hz2 a ha),
        fun a ha hout => (hfr3 a hout).trans ((hf2 a (by omega)).trans (hfr1_below a ha))⟩
      rw [ite_eq_right (not_not.mpr hzDir)]
      unfold Num.fixVal
      rw [Num.intVal_congr hcp3, hvalExact2, ← hfixEdge1]
      unfold Num.fixVal
      push_cast
      ring
    · simp only [phiFillEdgeStepContract, evalLevelPotGradContract, Num.subtractContract,
        copyLimbsToContract, heapContract, phiFillEdgeStepCost, evalLevelPotGradCost,
        List.getD_cons_zero, List.getD_cons_succ, argsSize, Expr.size]
      omega

/-! ## 3. Pure transition lemmas for `PhiFillBfsInv` -/

/-- Any vertex list `q` of distinct elements of `F.V` has length at most `F.n`. -/
theorem PhiFillBfsInv.q_length_le {mem mem0 : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P j scratch0 : ℕ} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {F : MGraph}
    {vL q : List ℕ} {qHead sc : ℕ} {φcur : ℕ → ℝ} {rootOf : ℕ → ℕ}
    (hInv : PhiFillBfsInv mem mem0 mloc h P j scratch0 C g φ F vL q qHead sc φcur rootOf) :
    q.length ≤ F.n := by
  have hsub : q.toFinset ⊆ F.V := fun v hv => hInv.2.1 v (List.mem_toFinset.mp hv)
  have hcard := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hInv.1] at hcard

/-- If `v ∈ F.V` and `v ∉ q`, then `q.length < F.n`. -/
theorem PhiFillBfsInv.q_length_lt_of_notMem {mem mem0 : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P j scratch0 : ℕ} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {F : MGraph}
    {vL q : List ℕ} {qHead sc : ℕ} {φcur : ℕ → ℝ} {rootOf : ℕ → ℕ}
    (hInv : PhiFillBfsInv mem mem0 mloc h P j scratch0 C g φ F vL q qHead sc φcur rootOf)
    {v : ℕ} (hv : v ∈ F.V) (hnot : v ∉ q) :
    q.length < F.n := by
  have hssub : q.toFinset ⊂ F.V :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨fun x hx => hInv.2.1 x (List.mem_toFinset.mp hx),
       fun hEq => hnot (List.mem_toFinset.mp (hEq.symm ▸ hv))⟩
  have hcard := Finset.card_lt_card hssub
  rwa [List.toFinset_card_of_nodup hInv.1] at hcard

/-- Initial empty BFS state at `scratch0` when `ZeroFrom mem scratch0`. -/
theorem PhiFillBfsInv.initial {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P j scratch0 : ℕ} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {F : MGraph}
    {vL : List ℕ}
    (hz : ZeroFrom mem scratch0) :
    PhiFillBfsInv mem mem mloc h P j scratch0 C g φ F vL [] 0 (scratch0 + 1 + 2 * F.n)
      (fun _ => 0) (fun _ => 0) := by
  refine ⟨List.nodup_nil, (fun _ h => by cases h), le_rfl, hz scratch0 le_rfl,
    (fun i hi => by simp at hi),
    (fun i _ => by simp only [List.not_mem_nil, ↓reduceIte]; exact hz _ (by omega)),
    (fun v hv => by simp at hv),
    (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by simp at h),
    le_rfl, by simp, (fun a ha => hz a (by omega)), (fun _ _ _ => rfl)⟩

/-- When `q` is closed under edges of `F` (i.e. `qHead = q.length`), any walk starting in `q`
stays in `q`. -/
private lemma walk_stays_in_q {F : MGraph} {q : List ℕ}
    (hclosed : ∀ u ∈ q, ∀ e ∈ F.E, (F.tail e = u → F.head e ∈ q) ∧ (F.head e = u → F.tail e ∈ q))
    {a b : ℕ} {W : List (ℕ × Bool)} (hW : F.IsWalk a b W) (ha : a ∈ q) : b ∈ q := by
  induction hW with
  | nil _ => exact ha
  | @cons u v x rest he hsrc hrest ih =>
    apply ih
    rcases x with ⟨e, dir⟩
    cases dir
    · simp only [MGraph.src, MGraph.dst, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
      exact (hclosed u ha e he).2 hsrc
    · simp only [MGraph.src, MGraph.dst, ↓reduceIte] at hsrc ⊢
      exact (hclosed u ha e he).1 hsrc

/-- Seeding an unvisited root `r = vL[idx]` when the queue is exhausted (`qHead = q.length`)
preserves `PhiFillBfsInv` with `q' = q ++ [r]`. -/
theorem PhiFillBfsInv.seedRoot {mem mem' mem0 : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P j scratch0 : ℕ} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {F : MGraph}
    {vL q : List ℕ} {sc idx : ℕ} {φcur : ℕ → ℝ} {rootOf : ℕ → ℕ}
    (hInv : PhiFillBfsInv mem mem0 mloc h P j scratch0 C g φ F vL q q.length sc φcur rootOf)
    (hF : F.IsForest) (hvLen : vL.length = F.n) (hvNd : vL.Nodup) (hvMem : ∀ v, v ∈ vL ↔ v ∈ F.V)
    (hidx : idx < vL.length) (hnot : vL[idx] ∉ q)
    (hphiHi : mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ scratch0)
    (hvCap : ∀ v ∈ F.V, v < mloc.vCap j)
    (hvis : mem' (scratch0 + 1 + idx) = 1)
    (hzeroSlot : ∀ i < mloc.Lk, mem' (mloc.phiPtr j + vL[idx] * mloc.Lk + i) = 0)
    (hqNew : mem' (scratch0 + 1 + F.n + q.length) = vL[idx])
    (hqtNew : mem' scratch0 = q.length + 1)
    (hfr : ∀ a, a ≠ scratch0 → a ≠ scratch0 + 1 + idx → a ≠ scratch0 + 1 + F.n + q.length →
      (a < mloc.phiPtr j + vL[idx] * mloc.Lk ∨
        mloc.phiPtr j + vL[idx] * mloc.Lk + mloc.Lk ≤ a) →
      mem' a = mem a) :
    PhiFillBfsInv mem' mem0 mloc h P j scratch0 C g φ F vL (q ++ [vL[idx]]) q.length sc
      (Function.update φcur vL[idx] 0) (Function.update rootOf vL[idx] vL[idx]) := by
  obtain ⟨hqNd, hqSub, _, _, hqAt, hvisAt, hEdgeV, hPaths, hRootEq, hClosed,
    hscLo, hscHi, hzSc, hfr0⟩ := hInv
  set r := vL[idx]
  have hrV : r ∈ F.V := (hvMem r).mp (List.getElem_mem hidx)
  have hrCap : r < mloc.vCap j := hvCap r hrV
  have hrEnd : mloc.phiPtr j + r * mloc.Lk + mloc.Lk ≤ scratch0 := by
    have := mul_add_le_mul_step (L := mloc.Lk) hrCap; omega
  have hqLt : q.length < F.n := by
    have hssub : q.toFinset ⊂ F.V :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨fun x hx => hqSub x (List.mem_toFinset.mp hx),
         fun hEq => hnot (List.mem_toFinset.mp (hEq.symm ▸ hrV))⟩
    have := Finset.card_lt_card hssub
    rwa [List.toFinset_card_of_nodup hqNd] at this
  have hqClosedAll : ∀ u ∈ q, ∀ e ∈ F.E,
      (F.tail e = u → F.head e ∈ q) ∧ (F.head e = u → F.tail e ∈ q) := by
    simpa [List.take_length] using hClosed
  refine ⟨List.nodup_append.mpr ⟨hqNd, List.nodup_singleton r, fun x hx y hy => by
      simp only [List.mem_singleton] at hy; subst hy; exact fun hEq => hnot (hEq ▸ hx)⟩,
    fun v hv => by
      rcases List.mem_append.mp hv with hv | hv
      · exact hqSub v hv
      · simp only [List.mem_singleton] at hv; exact hv ▸ hrV,
    by simp, by simpa using hqtNew, ?_, ?_, ?_, ?_, ?_, ?_, hscLo, ?_, ?_, ?_⟩
  · -- ListAt queue
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < q.length
    · rw [List.getElem_append_left hlt, hfr _ (by omega) (by omega) (by omega) (Or.inr (by omega))]
      exact hqAt i hlt
    · have hiEq : i = q.length := by omega
      subst hiEq
      simpa using hqNew
  · -- Visited array
    intro i hi
    by_cases hiEq : i = idx
    · subst hiEq
      simp only [List.mem_append, List.mem_singleton, or_true, ↓reduceIte, r]
      exact hvis
    · have hne : vL[i] ≠ r := fun hEq => hiEq (hvNd.getElem_inj_iff.mp hEq)
      rw [hfr _ (by omega) (by omega) (by omega) (Or.inr (by omega)), hvisAt i hi]
      simp [List.mem_append, hne]
  · -- EdgeValuesAt on (q ++ [r]).toFinset
    intro e he
    rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at he
    by_cases her : e = r
    · subst her; rw [Function.update_self]
      refine ⟨fun i hi => by rw [hzeroSlot i hi]; exact Num.base_pos h, ?_⟩
      unfold Num.fixVal
      have hu : Num.unsignedVal mem' (mloc.phiPtr j + r * mloc.Lk) h mloc.Lk = 0 :=
        Num.unsignedVal_zero hzeroSlot
      simp [Num.intVal, hu, Num.signedVal]
    · have heQ : e ∈ q := he.resolve_right her
      rw [Function.update_of_ne her]
      have heCap : e < mloc.vCap j := hvCap e (hqSub e heQ)
      have hhe := hEdgeV e (List.mem_toFinset.mpr heQ)
      have hkeep : ∀ i < mloc.Lk, mem' (mloc.phiPtr j + e * mloc.Lk + i) =
          mem (mloc.phiPtr j + e * mloc.Lk + i) := fun i hi => by
        have hlt := mul_add_le_mul_step (L := mloc.Lk) heCap
        apply hfr _ (by omega) (by omega) (by omega)
        rcases entry_disj_step (L := mloc.Lk) her with h1 | h1
        · left; omega
        · right; omega
      refine ⟨fun i hi => (hkeep i hi) ▸ hhe.1 i hi, ?_⟩
      unfold Num.fixVal
      rw [Num.intVal_congr hkeep]
      exact hhe.2
  · -- Root-path property
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have hne : v ≠ r := fun hEq => hnot (hEq ▸ hv)
      obtain ⟨hrq, hconn, hverts, hval⟩ := hPaths v hv
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact ⟨List.mem_append_left _ hrq, hconn,
        fun u hu => List.mem_append_left _ (hverts u hu), hval⟩
    · simp only [List.mem_singleton] at hv; subst hv
      rw [Function.update_self, Function.update_self, LSF.forestPath_self hF]
      refine ⟨List.mem_append_right _ List.mem_cons_self, LSF.connected_refl F r, ?_,
        by simp [walkInner_nil]⟩
      intro u hu
      simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hu
      subst hu
      exact List.mem_append_right _ List.mem_cons_self
  · -- Same-component vertices share rootOf
    intro u hu v hv hconn
    rcases List.mem_append.mp hu with hu | hu <;> rcases List.mem_append.mp hv with hv | hv
    · have hnu : u ≠ r := fun hEq => hnot (hEq ▸ hu)
      have hnv : v ≠ r := fun hEq => hnot (hEq ▸ hv)
      rw [Function.update_of_ne hnu, Function.update_of_ne hnv]
      exact hRootEq u hu v hv hconn
    · simp only [List.mem_singleton] at hv; subst hv
      obtain ⟨W, hW⟩ := hconn
      exact absurd (walk_stays_in_q hqClosedAll hW hu) hnot
    · simp only [List.mem_singleton] at hu; subst hu
      obtain ⟨W, hW⟩ := LSF.connected_symm hconn
      exact absurd (walk_stays_in_q hqClosedAll hW hv) hnot
    · simp only [List.mem_singleton] at hu hv; subst hu; subst hv; rfl
  · -- Closed on q.take q.length
    intro u hu e he
    rw [List.take_left] at hu
    have hc := hqClosedAll u hu e he
    exact ⟨fun ht => List.mem_append_left _ (hc.1 ht), fun hh => List.mem_append_left _ (hc.2 hh)⟩
  · -- Space bound
    simp only [List.length_append, List.length_singleton]
    have : q.length * phiFillEdgeStepSpace j mloc.Lk ≤
        (q.length + 1) * phiFillEdgeStepSpace j mloc.Lk :=
      Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  · -- ZeroFrom sc
    intro a ha
    rw [hfr a (by omega) (by omega) (by omega) (Or.inr (by omega))]
    exact hzSc a ha
  · -- Frame outside target below scratch0
    intro a ha hout
    rw [hfr a (by omega) (by omega) (by omega) (by
      rcases hout with h1 | h2
      · left; omega
      · right; have := mul_add_le_mul_step (L := mloc.Lk) hrCap; omega)]
    exact hfr0 a ha hout

/-- Discovering an unvisited child `child ∉ q` from `parent ∈ q` via tree edge `f ∈ F.E`
with direction `dir` (`dir = 1` iff `child = F.tail f ∧ parent = F.head f`; `dir = 0` iff
`child = F.head f ∧ parent = F.tail f`) preserves `PhiFillBfsInv`. -/
theorem PhiFillBfsInv.discoverChild {mem mem' mem0 : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P j scratch0 : ℕ} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {F : MGraph}
    {vL q : List ℕ} {qHead sc sc' f parent child dir chIdx : ℕ} {φcur : ℕ → ℝ}
    {rootOf : ℕ → ℕ}
    (hInv : PhiFillBfsInv mem mem0 mloc h P j scratch0 C g φ F vL q qHead sc φcur rootOf)
    (hF : F.IsForest) (hvLen : vL.length = F.n) (hvNd : vL.Nodup)
    (hchIdx : chIdx < vL.length) (hchEq : vL[chIdx] = child)
    (hparQ : parent ∈ q) (hchNot : child ∉ q) (hfE : f ∈ F.E)
    (hdirSpec : (dir ≠ 0 ∧ F.tail f = child ∧ F.head f = parent) ∨
      (dir = 0 ∧ F.head f = child ∧ F.tail f = parent))
    (hphiHi : mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ scratch0)
    (hvCap : ∀ v ∈ F.V, v < mloc.vCap j)
    (hscLo' : sc ≤ sc') (hscHi' : sc' ≤ sc + phiFillEdgeStepSpace j mloc.Lk)
    (hvis' : mem' (scratch0 + 1 + chIdx) = 1)
    (hqNew' : mem' (scratch0 + 1 + F.n + q.length) = child)
    (hqtNew' : mem' scratch0 = q.length + 1)
    (hchVal : Num.Valid mem' (mloc.phiPtr j + child * mloc.Lk) h mloc.Lk ∧
      Num.fixVal mem' (mloc.phiPtr j + child * mloc.Lk) h mloc.Lk P =
        (if dir ≠ 0 then φcur parent + potGrad C g φ j f else φcur parent - potGrad C g φ j f))
    (hz' : ZeroFrom mem' sc')
    (hfr : ∀ a < sc, a ≠ scratch0 → a ≠ scratch0 + 1 + chIdx → a ≠ scratch0 + 1 + F.n + q.length →
      (a < mloc.phiPtr j + child * mloc.Lk ∨
        mloc.phiPtr j + child * mloc.Lk + mloc.Lk ≤ a) →
      mem' a = mem a) :
    let newVal := if dir ≠ 0 then φcur parent + potGrad C g φ j f else φcur parent - potGrad C g φ j f
    PhiFillBfsInv mem' mem0 mloc h P j scratch0 C g φ F vL (q ++ [child]) qHead sc'
      (Function.update φcur child newVal) (Function.update rootOf child (rootOf parent)) := by
  dsimp only
  obtain ⟨hqNd, hqSub, hqHLe, _, hqAt, hvisAt, hEdgeV, hPaths, hRootEq, hClosed,
    hscLo, hscHi, _, hfr0⟩ := hInv
  have hchV : child ∈ F.V := by
    rcases hdirSpec with ⟨_, ht, _⟩ | ⟨_, hh, _⟩
    · exact ht ▸ (hF.1 f hfE).1
    · exact hh ▸ (hF.1 f hfE).2
  have hchCap : child < mloc.vCap j := hvCap child hchV
  have hchEnd : mloc.phiPtr j + child * mloc.Lk + mloc.Lk ≤ scratch0 := by
    have := mul_add_le_mul_step (L := mloc.Lk) hchCap; omega
  have hqLt : q.length < F.n := by
    have hssub : q.toFinset ⊂ F.V :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨fun x hx => hqSub x (List.mem_toFinset.mp hx),
         fun hEq => hchNot (List.mem_toFinset.mp (hEq.symm ▸ hchV))⟩
    have := Finset.card_lt_card hssub
    rwa [List.toFinset_card_of_nodup hqNd] at this
  let dirB : Bool := decide (dir ≠ 0)
  have hsrcE : F.src (f, dirB) = child := by
    rcases hdirSpec with ⟨hnz, ht, _⟩ | ⟨hz0, hh, _⟩
    · simp [dirB, hnz, MGraph.src, ht]
    · simp [dirB, hz0, MGraph.src, hh]
  have hdstE : F.dst (f, dirB) = parent := by
    rcases hdirSpec with ⟨hnz, _, hh⟩ | ⟨hz0, _, ht⟩
    · simp [dirB, hnz, MGraph.dst, hh]
    · simp [dirB, hz0, MGraph.dst, ht]
  have hconnCP : F.Connected child parent :=
    ⟨[(f, dirB)], .cons hfE hsrcE (hdstE.symm ▸ .nil parent)⟩
  obtain ⟨hrParQ, hconnPR, hvertsPR, hvalPar⟩ := hPaths parent hparQ
  have hpathChild : F.IsPath child (rootOf parent) ((f, dirB) :: F.forestPath parent (rootOf parent)) :=
    isPath_cons_of_not_mem_walkVertices hfE hsrcE hdstE
      (LSF.forestPath_isPath hF hconnPR) (fun hc => hchNot (hvertsPR child hc))
  have hfpathChild : F.forestPath child (rootOf parent) =
      (f, dirB) :: F.forestPath parent (rootOf parent) :=
    LSF.forestPath_eq_of_isPath hF hpathChild
  refine ⟨List.nodup_append.mpr ⟨hqNd, List.nodup_singleton child, fun x hx y hy => by
      simp only [List.mem_singleton] at hy; subst hy; exact fun hEq => hchNot (hEq ▸ hx)⟩,
    fun v hv => by
      rcases List.mem_append.mp hv with hv | hv
      · exact hqSub v hv
      · simp only [List.mem_singleton] at hv; exact hv ▸ hchV,
    by simp; omega, by simpa using hqtNew', ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, hz', ?_⟩
  · -- ListAt queue
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < q.length
    · rw [List.getElem_append_left hlt, hfr _ (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))]
      exact hqAt i hlt
    · have hiEq : i = q.length := by omega
      subst hiEq
      simpa using hqNew'
  · -- Visited array
    intro i hi
    by_cases hiEq : i = chIdx
    · subst hiEq
      simp only [hchEq, List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
      exact hvis'
    · have hne : vL[i] ≠ child := fun hEq => hiEq (hvNd.getElem_inj_iff.mp (hEq.trans hchEq.symm))
      rw [hfr _ (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega)), hvisAt i hi]
      simp [List.mem_append, hne]
  · -- EdgeValuesAt on (q ++ [child]).toFinset
    intro e he
    rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at he
    by_cases hec : e = child
    · subst hec; rw [Function.update_self]; exact hchVal
    · have heQ : e ∈ q := he.resolve_right hec
      rw [Function.update_of_ne hec]
      have heCap : e < mloc.vCap j := hvCap e (hqSub e heQ)
      have hhe := hEdgeV e (List.mem_toFinset.mpr heQ)
      have hkeep : ∀ i < mloc.Lk, mem' (mloc.phiPtr j + e * mloc.Lk + i) =
          mem (mloc.phiPtr j + e * mloc.Lk + i) := fun i hi => by
        have hlt := mul_add_le_mul_step (L := mloc.Lk) heCap
        apply hfr _ (by omega) (by omega) (by omega) (by omega)
        rcases entry_disj_step (L := mloc.Lk) hec with h1 | h1
        · left; omega
        · right; omega
      refine ⟨fun i hi => (hkeep i hi) ▸ hhe.1 i hi, ?_⟩
      unfold Num.fixVal
      rw [Num.intVal_congr hkeep]
      exact hhe.2
  · -- Root-path property
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have hne : v ≠ child := fun hEq => hchNot (hEq ▸ hv)
      obtain ⟨hrq, hconn, hverts, hval⟩ := hPaths v hv
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact ⟨List.mem_append_left _ hrq, hconn,
        fun u hu => List.mem_append_left _ (hverts u hu), hval⟩
    · simp only [List.mem_singleton] at hv; subst hv
      rw [Function.update_self, Function.update_self, hfpathChild]
      refine ⟨List.mem_append_left _ hrParQ, LSF.connected_trans hconnCP hconnPR, ?_, ?_⟩
      · intro u hu
        rw [LSF.walkVertices_cons, hdstE] at hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · exact List.mem_append_right _ List.mem_cons_self
        · exact List.mem_append_left _ (hvertsPR u hu')
      · rw [walkInner_cons, walkInner_singleton, ← hvalPar]
        by_cases hnz : dir ≠ 0
        · simp [dirB, hnz]; ring
        · simp [dirB, hnz]; ring
  · -- Same-component vertices share rootOf
    intro u hu v hv hconn
    rcases List.mem_append.mp hu with huQ | huC
    · rcases List.mem_append.mp hv with hvQ | hvC
      · have hnu : u ≠ child := fun hEq => hchNot (hEq ▸ huQ)
        have hnv : v ≠ child := fun hEq => hchNot (hEq ▸ hvQ)
        rw [Function.update_of_ne hnu, Function.update_of_ne hnv]
        exact hRootEq u huQ v hvQ hconn
      · rcases List.mem_singleton.mp hvC with rfl
        have hnu : u ≠ v := fun hEq => hchNot (hEq ▸ huQ)
        rw [Function.update_of_ne hnu, Function.update_self]
        exact hRootEq u huQ parent hparQ (LSF.connected_trans hconn hconnCP)
    · rcases List.mem_singleton.mp huC with rfl
      rcases List.mem_append.mp hv with hvQ | hvC
      · have hnv : v ≠ u := fun hEq => hchNot (hEq ▸ hvQ)
        rw [Function.update_self, Function.update_of_ne hnv]
        exact hRootEq parent hparQ v hvQ (LSF.connected_trans (LSF.connected_symm hconnCP) hconn)
      · rcases List.mem_singleton.mp hvC with rfl; rfl
  · -- Closed on q.take qHead
    intro u hu e he
    rw [List.take_append_of_le_length hqHLe] at hu
    have hc := hClosed u hu e he
    exact ⟨fun ht => List.mem_append_left _ (hc.1 ht), fun hh => List.mem_append_left _ (hc.2 hh)⟩
  · -- Space bound
    simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    omega
  · -- Frame outside target below scratch0
    intro a ha hout
    rw [hfr a (by omega) (by omega) (by omega) (by omega) (by
      rcases hout with h1 | h2
      · left; omega
      · right; have := mul_add_le_mul_step (L := mloc.Lk) hchCap; omega)]
    exact hfr0 a ha hout

/-- Advancing `qHead` after all incident edges of `q[qHead]` have been scanned. -/
theorem PhiFillBfsInv.finishParent {mem mem0 : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P j scratch0 : ℕ} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {F : MGraph}
    {vL q : List ℕ} {qHead sc : ℕ} {φcur : ℕ → ℝ} {rootOf : ℕ → ℕ}
    (hInv : PhiFillBfsInv mem mem0 mloc h P j scratch0 C g φ F vL q qHead sc φcur rootOf)
    (hqH : qHead < q.length)
    (hParClosed : ∀ e ∈ F.E,
      (F.tail e = q[qHead] → F.head e ∈ q) ∧ (F.head e = q[qHead] → F.tail e ∈ q)) :
    PhiFillBfsInv mem mem0 mloc h P j scratch0 C g φ F vL q (qHead + 1) sc φcur rootOf := by
  obtain ⟨a1, a2, _, a4, a5, a6, a7, a8, a9, hClosed, a11, a12, a13, a14⟩ := hInv
  refine ⟨a1, a2, by omega, a4, a5, a6, a7, a8, a9, ?_, a11, a12, a13, a14⟩
  intro u hu e he
  rw [List.take_succ_eq_append_getElem hqH, List.mem_append, List.mem_singleton] at hu
  rcases hu with hu | rfl
  · exact hClosed u hu e he
  · exact hParClosed e he

/-- When all vertices of `F` have been visited (`q.toFinset = F.V`), `PhiFillBfsInv` yields the
exact postcondition of `selectPhiFillContract`: `EdgeValuesAt`, the tree-edge difference equation,
`SelectPotInvAt`, and the root-path formula. -/
theorem PhiFillBfsInv.finishAll {mem mem0 : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P j scratch0 : ℕ} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {F : MGraph}
    {vL q : List ℕ} {qHead sc : ℕ} {φcur : ℕ → ℝ} {rootOf : ℕ → ℕ}
    (hInv : PhiFillBfsInv mem mem0 mloc h P j scratch0 C g φ F vL q qHead sc φcur rootOf)
    (hF : F.IsForest) (hFEq : F = (C.activeLSF j).F.F) (hFV : F.V = (C.G j).V)
    (hCover : ∀ v ∈ F.V, v ∈ q) :
    EdgeValuesAt mem (mloc.phiPtr j) h mloc.Lk P (C.G j).V φcur ∧
    (∀ e ∈ F.E, φcur (F.tail e) - φcur (F.head e) = potGrad C g φ j e) ∧
    SelectPotInvAt C g (Function.update φ j φcur) j ∧
    (∀ v ∈ F.V, ∃ r ∈ F.V, F.Connected v r ∧
      φcur v = walkInner (potGrad C g φ j) (F.forestPath v r)) := by
  obtain ⟨_, hqSub, _, _, _, _, hEdgeV, hPaths, hRootEq, _, _, _, _, _⟩ := hInv
  have hqFin : q.toFinset = (C.G j).V := by
    ext v
    rw [List.mem_toFinset, ← hFV]
    exact ⟨hqSub v, hCover v⟩
  have hDiff : ∀ e ∈ F.E, φcur (F.tail e) - φcur (F.head e) = potGrad C g φ j e := by
    intro e he
    have htV : F.tail e ∈ F.V := (hF.1 e he).1
    have hhV : F.head e ∈ F.V := (hF.1 e he).2
    have htQ : F.tail e ∈ q := hCover _ htV
    have hhQ : F.head e ∈ q := hCover _ hhV
    have hconnE : F.Connected (F.tail e) (F.head e) := LSF.connected_of_edge he
    have hrEq : rootOf (F.tail e) = rootOf (F.head e) := hRootEq _ htQ _ hhQ hconnE
    set r := rootOf (F.head e)
    obtain ⟨_, hconnT, _, hvalT⟩ := hPaths (F.tail e) htQ
    obtain ⟨_, hconnH, _, hvalH⟩ := hPaths (F.head e) hhQ
    rw [hrEq] at hconnT hvalT
    have hW1 : F.IsWalk (F.tail e) (F.head e) [(e, true)] :=
      .cons he rfl (.nil (F.head e))
    have hW2 : F.IsWalk (F.tail e) (F.head e) (F.forestPath (F.tail e) r ++ walkRev (F.forestPath (F.head e) r)) :=
      LSF.IsWalk_append (MGraph.isWalk_forestPath hconnT)
        (LSF.IsWalk_walkRev (MGraph.isWalk_forestPath hconnH))
    have hflow : ∀ f, walkFlow [(e, true)] f =
        walkFlow (F.forestPath (F.tail e) r ++ walkRev (F.forestPath (F.head e) r)) f :=
      walkFlow_eq_of_isForest hF hW1 hW2
    have hinner := walkInner_eq_of_walkFlow_eq (potGrad C g φ j) hflow
    rw [walkInner_singleton, walkInner_append, walkInner_walkRev] at hinner
    simp only [↓reduceIte] at hinner
    linarith
  refine ⟨hqFin ▸ hEdgeV, hDiff, selectPotInvAt_of_edge_diff (hFEq ▸ hDiff), fun v hv => ?_⟩
  obtain ⟨hrQ, hconn, _, hval⟩ := hPaths v (hCover v hv)
  exact ⟨rootOf v, hqSub _ hrQ, hconn, hval⟩

end MinCostFlow.MinRatio

end
