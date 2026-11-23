module

public import MinCostFlow.MinRatio.SelectPhiFillAdj
import WordRAM.Tactic

/-!
# Verification of `phiFillBfsLoopBody` (`SelectPhiFillBfs`)

Verifies the BFS component-drain loop `phiFillBfsLoopBody` of `selectPhiFill`:
* `phiFillBfsLoop_runs`: drains the BFS queue until `qHead = q'.length`, preserving `PhiFillBfsInv`
  and telescoping cost against remaining undiscovered vertices, remaining unpopped vertices, and
  `phiFillRemVol`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 3. Verification of `phiFillBfsLoopBody` -/

/-- Verification of `phiFillBfsLoopBody` by induction on `rem = F.n - qHead`. Drains the BFS queue
until `qHead = q'.length`, preserving `PhiFillBfsInv` and telescoping cost against remaining
undiscovered vertices, remaining unpopped vertices, and `phiFillRemVol`. -/
theorem phiFillBfsLoop_runs {w h P bfsProc adjProc edgeStepProc j scratch0 : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ : ℕ → ℕ → ℝ} {p : Program} {ω : ℕ → Bool}
    {mem0 : ℕ → ℕ} {vL : List ℕ}
    (hpBfs : p.procs[bfsProc]? = some (phiFillBfsLoopBody bfsProc adjProc))
    (hpAdj : p.procs[adjProc]? = some (phiFillAdjLoopBody adjProc edgeStepProc))
    (hEdgeStep : MeetsContract w p edgeStepProc (phiFillEdgeStepContract w h P mloc C g φ))
    (hw16 : 16 < 2 ^ w) (hh : 0 < h) (hw2 : 2 * h + 2 ≤ w)
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hjD : j ≤ C.d)
    (he0Cap : ∀ e ∈ (C.G 0).E, e < mloc.eCap 0)
    (hphiJM0 : mem0 (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j)
    (hF0 : DynGraphAt mem0 (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) (C.activeLSF j).F.F)
    (hPref0 : SelectPhiPrefixAt mem0 mloc h P C g φ j)
    (hBel0 : SelectPhiPrefixBelow mloc j scratch0)
    (hDisj0 : SelectPhiTargetDisjoint mloc j scratch0)
    (hFitsE : ∀ e ∈ (C.activeLSF j).F.F.E, PotGradEvalFits h mloc.Lk P C g φ j e)
    (hFitsW : ForestWalkFits h mloc.Lk P (C.activeLSF j).F.F (potGrad C g φ j))
    (hroom0 : scratch0 + selectPhiFillSpace j (C.activeLSF j).F.F.n mloc.Lk < 2 ^ w)
    (hvL_len : vL.length = (C.activeLSF j).F.F.n) (hvL_nd : vL.Nodup)
    (hvL_mem : ∀ v, v ∈ vL ↔ v ∈ (C.activeLSF j).F.F.V)
    (hvL_pos : ∀ i (hi : i < vL.length), mem0 (dgVPosBase (mloc.fPtr j) (mloc.vCap j) + vL[i]) = i) :
    let F := (C.activeLSF j).F.F
    ∀ (rem : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (q : List ℕ) (qHead sc : ℕ)
      (φcur : ℕ → ℝ) (rootOf : ℕ → ℕ),
      F.n - qHead = rem →
      PhiFillBfsInv mem mem0 mloc h P j scratch0 C g φ F vL q qHead sc φcur rootOf →
      ∃ sc' st' cost q' φcur' rootOf',
        Runs w p ω (phiFillBfsLoopBody bfsProc adjProc)
          (startState [mloc.metaBase, j, mloc.fPtr j,
            scratch0 + 1, scratch0 + 1 + F.n, qHead, scratch0, mloc.Lk, sc] mem pos)
          (.returned sc') st' cost ∧
        q.length ≤ q'.length ∧ q'.take q.length = q ∧
        PhiFillBfsInv st'.mem mem0 mloc h P j scratch0 C g φ F vL q' q'.length sc' φcur' rootOf' ∧
        cost + (F.n - q'.length) * (phiFillEdgeStepCost j mloc.Lk + 60) +
          (F.n - q'.length) * 100 + phiFillRemVol F q' q'.length * 180 ≤
          (F.n - q.length) * (phiFillEdgeStepCost j mloc.Lk + 60) +
            (F.n - qHead) * 100 + phiFillRemVol F q qHead * 180 + 20 := by
  dsimp only
  set F := (C.activeLSF j).F.F
  have hRF := (C.activeLSF_holds hH hjD).2.1
  have hF_forest : F.IsForest := hRF.1
  have hszF : dynGraphSize (mloc.vCap j) (mloc.eCap j) =
      4 + 7 * mloc.vCap j + 9 * mloc.eCap j := rfl
  have hF_hi : mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ scratch0 := hDisj0.2.1
  have hF_disj : mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ mloc.phiPtr j ∨
      mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.fPtr j := hDisj0.2.2.2.2.1
  have hsp0 : selectPhiFillSpace j F.n mloc.Lk =
      1 + 2 * F.n + F.n * phiFillEdgeStepSpace j mloc.Lk := rfl
  have hsc0W : scratch0 < 2 ^ w := by omega
  have hmetaW : mloc.metaBase < 2 ^ w := by
    have : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
    have := hBel0.1; omega
  have hjW : j < 2 ^ w := by
    have : mloc.d = C.d := hPref0.1
    have : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
    have := hBel0.1; omega
  have hfPtrW : mloc.fPtr j < 2 ^ w := by omega
  have hvisPtrW : scratch0 + 1 < 2 ^ w := by omega
  have hqPtrW : scratch0 + 1 + F.n < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  intro rem
  induction rem with
  | zero =>
    intro mem pos q qHead sc φcur rootOf hremEq hInv
    have hqLenLe : q.length ≤ F.n := hInv.q_length_le
    have hqHLe : qHead ≤ q.length := hInv.2.2.1
    have hqHEq : qHead = q.length := by omega
    have hqHeadW : qHead < 2 ^ w := by omega
    have hscW : sc < 2 ^ w := by
      have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) hqLenLe
      have := hInv.2.2.2.2.2.2.2.2.2.2.2.1; omega
    have hqtMem : mem scratch0 = q.length := hInv.2.2.2.1
    let stA : State :=
      { mem := mem
        regs := Function.update
          (startState [mloc.metaBase, j, mloc.fPtr j, scratch0 + 1, scratch0 + 1 + F.n,
            qHead, scratch0, mloc.Lk, sc] mem pos).regs 9 q.length
        pos := pos }
    refine ⟨sc, stA, 10, q, φcur, rootOf, ?_, le_rfl, List.take_length, hqHEq ▸ hInv,
      by rw [hqHEq]; omega⟩
    unfold phiFillBfsLoopBody
    have ha9 : Runs w p ω (.assign 9 (.load (.reg 6)))
        (startState [mloc.metaBase, j, mloc.fPtr j, scratch0 + 1, scratch0 + 1 + F.n,
          qHead, scratch0, mloc.Lk, sc] mem pos) .normal stA 3 :=
      runs_assign_iff.mpr ⟨q.length,
        Expr.eval_load_of_eq (by simp [Expr.eval, startState]) hqtMem, rfl, rfl, rfl⟩
    have hcond : (Expr.bin .lt (.reg 5) (.reg 9)).eval w stA = some 0 := by
      simp [stA, Expr.eval, BinOp.eval, startState, hqHEq]
    have hret : Runs w p ω (.ret (.reg 8)) stA (.returned sc) stA 2 :=
      runs_ret_iff.mpr ⟨sc, by simp [stA, Expr.eval, startState], rfl, rfl, rfl⟩
    have hcc : Runs w p ω (.cond (.bin .lt (.reg 5) (.reg 9))
        (.assign 10 (.load (.bin .add (.reg 4) (.reg 5))) ;;
         .assign 11 (.load (.reg 2)) ;;
         .assign 12 (.load (.bin .add (.bin .add (.bin .add (.reg 2) (.const 4))
           (.bin .mul (.const 3) (.reg 11))) (.reg 10))) ;;
         .assign 13 (.load (.bin .add (.bin .add (.bin .add (.reg 2) (.const 4))
           (.bin .mul (.const 6) (.reg 11))) (.reg 12))) ;;
         .call 14 adjProc [.reg 0, .reg 1, .reg 2, .reg 10, .reg 13, .reg 3, .reg 4, .reg 6, .reg 7, .reg 8] ;;
         .call 15 bfsProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .bin .add (.reg 5) (.const 1), .reg 6, .reg 7, .reg 14] ;;
         .ret (.reg 15))
        (.ret (.reg 8))) stA (.returned sc) stA 6 :=
      runs_cond_iff.mpr ⟨0, 2, hcond, by simpa using hret, by simp [Expr.size]⟩
    exact runs_seq_iff.mpr (Or.inr ⟨_, 3, 6, ha9, hcc, rfl⟩)
  | succ rem' ih =>
    intro mem pos q qHead sc φcur rootOf hremEq hInv
    have hqLenLe : q.length ≤ F.n := hInv.q_length_le
    have hqHLe : qHead ≤ q.length := hInv.2.2.1
    have hqHeadW : qHead < 2 ^ w := by omega
    have hqLenW : q.length < 2 ^ w := by omega
    have hscW : sc < 2 ^ w := by
      have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) hqLenLe
      have := hInv.2.2.2.2.2.2.2.2.2.2.2.1; omega
    have hqtMem : mem scratch0 = q.length := hInv.2.2.2.1
    by_cases hlt : qHead < q.length
    · -- Queue non-empty: pop parent = q[qHead], scan its incidence list, then recurse with qHead + 1
      set parent := q[qHead]'hlt
      have hparQ : parent ∈ q := List.getElem_mem hlt
      have hparV : parent ∈ F.V := hInv.2.1 parent hparQ
      have hparCap : parent < mloc.vCap j := hF0.2.1 parent hparV
      have hFnPos : 0 < F.n := Finset.card_pos.mpr ⟨parent, hparV⟩
      have hLkW : mloc.Lk < 2 ^ w := by
        have h1 : mloc.Lk ≤ phiFillEdgeStepSpace j mloc.Lk := by unfold phiFillEdgeStepSpace; nlinarith
        have h2 : phiFillEdgeStepSpace j mloc.Lk ≤ F.n * phiFillEdgeStepSpace j mloc.Lk :=
          Nat.le_mul_of_pos_left _ hFnPos
        omega
      have hfr0 := hInv.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hF_agree : ∀ a, mloc.fPtr j ≤ a → a < mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) →
          mem a = mem0 a := fun a h1 h2 => by
        apply hfr0 a (lt_of_lt_of_le h2 hF_hi)
        rcases hF_disj with hd | hd <;> [left; right] <;> omega
      obtain ⟨incAll, hincAll⟩ := hF0.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      set parSlot := mem0 (dgExtToIntBase (mloc.fPtr j) (mloc.vCap j) + parent)
      have hparSlotV : parSlot ∈ F.V := (hF0.2.2.2.2.2.2.2.2.2.1 parent hparV).1
      have hparSlotCap : parSlot < mloc.vCap j := hF0.2.1 parSlot hparSlotV
      obtain ⟨hparDll, hparDegMem, hparMem⟩ := hincAll parSlot hparSlotCap
      have hparDegEq : (incAll parSlot).length = F.deg parent := by
        rw [← hparDegMem]; exact hF0.slotDeg_eq_deg hparV
      -- Call phiFillAdjLoop_runs
      obtain ⟨sc1, st1, cAdj, q1, φcur1, rootOf1, hAdjRun, hqle1, hqtake1, hInv1, hCov1, hAdjCost⟩ :=
        phiFillAdjLoop_runs hpAdj hEdgeStep hw16 hh hw2 hH hjD he0Cap hphiJM0 hF0 hPref0 hBel0 hDisj0
          hFitsE hFitsW hroom0 hvL_len hvL_nd hvL_mem hvL_pos hparV rfl hparDll hparMem
          (incAll parSlot).length 0 mem pos q qHead sc φcur rootOf (Nat.zero_le _) (Nat.sub_zero _)
          hparQ hInv
      -- Show all incident edges of parent now have their other end in q1
      have hq1HeadEq : q1[qHead]'(by omega) = parent := by
        have h1 : (q1.take q.length)[qHead]'(by rw [List.length_take, Nat.min_eq_left hqle1]; exact hlt) =
            q1[qHead]'(by omega) := List.getElem_take
        rw [← h1]
        simp only [hqtake1]; rfl
      have hParClosed1 : ∀ e ∈ F.E,
          (F.tail e = q1[qHead]'(by omega) → F.head e ∈ q1) ∧
          (F.head e = q1[qHead]'(by omega) → F.tail e ∈ q1) := by
        rw [hq1HeadEq]
        intro e he
        have heCap : e < mloc.eCap j := hF0.2.2.1 e he
        have hslots := hF0.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
        constructor
        · intro ht
          have hmem2e : 2 * e ∈ incAll parSlot := (hparMem (2 * e)).mpr
            ⟨by omega, by simpa [show 2 * e / 2 = e by omega] using he,
             by simp [show 2 * e % 2 = 0 by omega, show 2 * e / 2 = e by omega, hslots.1, ht, parSlot]⟩
          have hc := (hCov1 (2 * e) (by simpa using hmem2e)).1 (by omega)
          simpa [show 2 * e / 2 = e by omega] using hc
        · intro hh'
          have hmem2e1 : 2 * e + 1 ∈ incAll parSlot := (hparMem (2 * e + 1)).mpr
            ⟨by omega, by simpa [show (2 * e + 1) / 2 = e by omega] using he,
             by simp [show (2 * e + 1) / 2 = e by omega, hslots.2, hh', parSlot]⟩
          have hc := (hCov1 (2 * e + 1) (by simpa using hmem2e1)).2 (by omega)
          simpa [show (2 * e + 1) / 2 = e by omega] using hc
      have hInv1' := hInv1.finishParent (by omega) hParClosed1
      -- Recursive call to phiFillBfsLoop_runs with qHead + 1
      obtain ⟨sc2, st2, cRec, q2, φcur2, rootOf2, hRecRun, hqle2, hqtake2, hInv2, hRecCost⟩ :=
        ih st1.mem st1.pos q1 (qHead + 1) sc1 φcur1 rootOf1 (by omega) hInv1'
      -- Assemble the run of phiFillBfsLoopBody
      have hheadCurEq : mem (dgIncHeadBase (mloc.fPtr j) (mloc.vCap j) + parSlot) =
          if h : 0 < (incAll parSlot).length then (incAll parSlot)[0] + 1 else 0 := by
        rw [hF_agree _ (by unfold dgIncHeadBase; omega) (by unfold dgIncHeadBase; omega),
          hparDll.2.2.1]
        cases hL : incAll parSlot with
        | nil => simp
        | cons x xs => simp
      have hheadCurW : (if h : 0 < (incAll parSlot).length then (incAll parSlot)[0] + 1 else 0) < 2 ^ w := by
        split_ifs with h1
        · have := (hparMem _).mp (List.getElem_mem h1) |>.1; omega
        · omega
      have hsc1W : sc1 < 2 ^ w := by
        have h1 : q1.length ≤ F.n := hInv1.q_length_le
        have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) h1
        have h2 : sc1 ≤ scratch0 + 1 + 2 * F.n + q1.length * phiFillEdgeStepSpace j mloc.Lk :=
          hInv1.2.2.2.2.2.2.2.2.2.2.2.1
        omega
      have hsc2W : sc2 < 2 ^ w := by
        have h1 : q2.length ≤ F.n := hInv2.q_length_le
        have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) h1
        have h2 : sc2 ≤ scratch0 + 1 + 2 * F.n + q2.length * phiFillEdgeStepSpace j mloc.Lk :=
          hInv2.2.2.2.2.2.2.2.2.2.2.2.1
        omega
      have hqHead1W : qHead + 1 < 2 ^ w := by omega
      have hparW : parent < 2 ^ w := by omega
      have hvcW : mloc.vCap j < 2 ^ w := by omega
      have hparSlotW : parSlot < 2 ^ w := by omega
      have hqAtPar : mem (scratch0 + 1 + F.n + qHead) = parent := hInv.2.2.2.2.1 qHead hlt
      have hvcM : mem (mloc.fPtr j) = mloc.vCap j := by
        rw [hF_agree _ le_rfl (by omega)]; simpa [dgVCapOff] using hF0.2.2.2.1
      have hparSlotM : mem (dgExtToIntBase (mloc.fPtr j) (mloc.vCap j) + parent) = parSlot :=
        hF_agree _ (by unfold dgExtToIntBase; omega) (by unfold dgExtToIntBase; omega)
      have hqAtW : scratch0 + 1 + F.n + qHead < 2 ^ w := by omega
      have hfPtr4W : mloc.fPtr j + 4 < 2 ^ w := by omega
      have h3vcW : 3 * mloc.vCap j < 2 ^ w := by omega
      have h6vcW : 6 * mloc.vCap j < 2 ^ w := by omega
      have hetiAddrW : dgExtToIntBase (mloc.fPtr j) (mloc.vCap j) + parent < 2 ^ w := by
        unfold dgExtToIntBase; omega
      have hincAddrW : dgIncHeadBase (mloc.fPtr j) (mloc.vCap j) + parSlot < 2 ^ w := by
        unfold dgIncHeadBase; omega
      let T : ℕ := cAdj + cRec + 80
      have hRunFull : ∃ o stFin cost,
          Runs w p ω (phiFillBfsLoopBody bfsProc adjProc)
            (startState [mloc.metaBase, j, mloc.fPtr j,
              scratch0 + 1, scratch0 + 1 + F.n, qHead, scratch0, mloc.Lk, sc] mem pos) o stFin cost ∧
          (o = .returned sc2 ∧ stFin.mem = st2.mem ∧ stFin.pos = st2.pos) ∧
          0 + cost ≤ T := by
        unfold phiFillBfsLoopBody
        refine runs_seq_assign_flat (v := q.length)
          (Expr.eval_load_of_eq (by eval_expr) hqtMem) ?_
        refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hlt, hw1]) ?_
          (fun hc => absurd hc (by decide))
        intro _
        refine runs_seq_assign_flat (v := parent)
          (Expr.eval_load_of_eq (by eval_expr) hqAtPar) ?_
        refine runs_seq_assign_flat (v := mloc.vCap j)
          (Expr.eval_load_of_eq (by eval_expr) hvcM) ?_
        refine runs_seq_assign_flat (v := parSlot)
          (Expr.eval_load_of_eq (by unfold dgExtToIntBase at hetiAddrW; eval_expr)
            (by unfold dgExtToIntBase at hparSlotM; exact hparSlotM)) ?_
        refine runs_seq_assign_flat (v := if h : 0 < (incAll parSlot).length then (incAll parSlot)[0] + 1 else 0)
          (Expr.eval_load_of_eq (by unfold dgIncHeadBase at hincAddrW; eval_expr)
            (by unfold dgIncHeadBase at hheadCurEq; exact hheadCurEq)) ?_
        refine runs_seq_rec_call hpAdj
          (vs := [mloc.metaBase, j, mloc.fPtr j, parent,
            if h : 0 < (incAll parSlot).length then (incAll parSlot)[0] + 1 else 0,
            scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc])
          (by eval_expr) (by wram_words) hAdjRun ?_
        refine runs_seq_rec_call hpBfs
          (vs := [mloc.metaBase, j, mloc.fPtr j, scratch0 + 1, scratch0 + 1 + F.n,
            qHead + 1, scratch0, mloc.Lk, sc1])
          (by eval_expr) (by wram_words) hRecRun ?_
        refine WordRAM.runs_ret_le (v := sc2) (by eval_expr) ⟨rfl, rfl, rfl⟩ ?_
        simp only [T, argsSize, Expr.size]; omega
      obtain ⟨o, stFin, cost, hRun, ⟨rfl, hstFinM, _⟩, hcostLe⟩ := hRunFull
      have hqtake12 : q2.take q.length = q := by
        have h1 : (q2.take q1.length).take q.length = q2.take q.length := by
          rw [List.take_take, Nat.min_eq_left hqle1]
        rw [← h1, hqtake2, hqtake1]
      -- Volume telescoping: q1.take qHead = q.take qHead!
      have htakeEq : q1.take qHead = q.take qHead := by
        have h1 : (q1.take q.length).take qHead = q1.take qHead := by
          rw [List.take_take, Nat.min_eq_left hqHLe]
        rw [← h1, hqtake1]
      have hvolEq : phiFillRemVol F q1 qHead = phiFillRemVol F q qHead := by
        unfold phiFillRemVol; rw [htakeEq]
      have hvolPop : phiFillRemVol F q1 (qHead + 1) + F.deg parent = phiFillRemVol F q qHead := by
        rw [← hvolEq, ← hq1HeadEq]
        exact phiFillRemVol_pop hInv1.1 hInv1.2.1 (by omega)
      refine ⟨sc2, stFin, cost, q2, φcur2, rootOf2, hRun, le_trans hqle1 hqle2, hqtake12,
        by rwa [hstFinM], ?_⟩
      change cAdj + (F.n - q1.length) * (phiFillEdgeStepCost j mloc.Lk + 60) ≤
          (incAll parSlot).length * 180 + (F.n - q.length) * (phiFillEdgeStepCost j mloc.Lk + 60) + 12 at hAdjCost
      have hvolMul : phiFillRemVol F q1 (qHead + 1) * 180 + (incAll parSlot).length * 180 =
          phiFillRemVol F q qHead * 180 := by
        rw [hparDegEq, ← Nat.add_mul, hvolPop]
      have hpopMul : (F.n - qHead) * 100 = (F.n - (qHead + 1)) * 100 + 100 := by
        conv_lhs => rw [show F.n - qHead = (F.n - (qHead + 1)) + 1 by omega]
        rw [Nat.add_mul, Nat.one_mul]
      omega
    · -- Queue already empty (`qHead = q.length`): return immediately!
      have hqHEq : qHead = q.length := by omega
      let stA : State :=
        { mem := mem
          regs := Function.update
            (startState [mloc.metaBase, j, mloc.fPtr j, scratch0 + 1, scratch0 + 1 + F.n,
              qHead, scratch0, mloc.Lk, sc] mem pos).regs 9 q.length
          pos := pos }
      refine ⟨sc, stA, 10, q, φcur, rootOf, ?_, le_rfl, List.take_length, hqHEq ▸ hInv,
        by rw [hqHEq]; omega⟩
      unfold phiFillBfsLoopBody
      have ha9 : Runs w p ω (.assign 9 (.load (.reg 6)))
          (startState [mloc.metaBase, j, mloc.fPtr j, scratch0 + 1, scratch0 + 1 + F.n,
            qHead, scratch0, mloc.Lk, sc] mem pos) .normal stA 3 :=
        runs_assign_iff.mpr ⟨q.length,
          Expr.eval_load_of_eq (by simp [Expr.eval, startState]) hqtMem, rfl, rfl, rfl⟩
      have hcond : (Expr.bin .lt (.reg 5) (.reg 9)).eval w stA = some 0 := by
        simp [stA, Expr.eval, BinOp.eval, startState, hqHEq]
      have hret : Runs w p ω (.ret (.reg 8)) stA (.returned sc) stA 2 :=
        runs_ret_iff.mpr ⟨sc, by simp [stA, Expr.eval, startState], rfl, rfl, rfl⟩
      exact runs_seq_iff.mpr (Or.inr ⟨_, 3, 6, ha9,
        runs_cond_iff.mpr ⟨0, 2, hcond, by simpa using hret, by simp [Expr.size]⟩, rfl⟩)


end MinCostFlow.MinRatio

end
