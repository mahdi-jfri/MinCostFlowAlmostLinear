module

public import MinCostFlow.MinRatio.SelectPhiFillBfs
import WordRAM.Tactic

/-!
# Verification of `selectPhiFill` (`SelectPhiFill`)

Completes the verification of the BFS forest-potential fill procedure `selectPhiFill`:
* `phiFillOuterLoop_runs`: walks live vertex indices `0 .. F.n - 1` of `F_j = (C.activeLSF j).F.F`,
  zeroing `φ_j[root]` and draining each unvisited component via `phiFillBfsLoopBody`, telescoping
  cost against `(F.n - q.length)`, `phiFillRemVol`, and `(F.n - idx)`.
* `selectPhiFill_meetsContract`: verifies `selectPhiFillBody` inside `selectPhiFillProcs` against
  `selectPhiFillContract` in `selectPhiFillCost j F.n Lk = O((F.n + 1) * (j + 1) * Lk)` steps and
  `selectPhiFillSpace j F.n Lk` scratch words.
* `selectPhiFillModule_meetsContract`: verifies the self-contained 17-procedure relocatable block
  `selectPhiFillModule b h` at `b + 16`, plus convenience lemmas exposing `evalEdgePotGrad` at
  `b + 10` and `evalLevelPotGrad` at `b + 11`.
* `selectPhiFill_pre_nonvacuous`: concrete witness showing `selectPhiFillContract.pre` is
  simultaneously satisfiable.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

private lemma mul_add_le_mul_fill {v c L : ℕ} (hv : v < c) :
    v * L + L ≤ c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at this
  exact this

/-! ## 1. Verification of `phiFillOuterLoopBody` -/

/-- Verification of `phiFillOuterLoopBody` by induction on `rem = F.n - idx`. Visits every live
vertex of `F_j = (C.activeLSF j).F.F`, establishing `∀ k < F.n, vL[k] ∈ q'` and `PhiFillBfsInv`. -/
theorem phiFillOuterLoop_runs {w h P outerProc bfsProc adjProc edgeStepProc zeroProc j scratch0 : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ : ℕ → ℕ → ℝ} {p : Program} {ω : ℕ → Bool}
    {mem0 : ℕ → ℕ} {vL : List ℕ}
    (hpOuter : p.procs[outerProc]? = some (phiFillOuterLoopBody outerProc bfsProc zeroProc))
    (hpBfs : p.procs[bfsProc]? = some (phiFillBfsLoopBody bfsProc adjProc))
    (hpAdj : p.procs[adjProc]? = some (phiFillAdjLoopBody adjProc edgeStepProc))
    (hEdgeStep : MeetsContract w p edgeStepProc (phiFillEdgeStepContract w h P mloc C g φ))
    (hZero : MeetsContract w p zeroProc (zeroLimbsContract w))
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
    (hLkW : mloc.Lk < 2 ^ w)
    (hroom0 : scratch0 + selectPhiFillSpace j (C.activeLSF j).F.F.n mloc.Lk < 2 ^ w)
    (hvL_len : vL.length = (C.activeLSF j).F.F.n) (hvL_nd : vL.Nodup)
    (hvL_mem : ∀ v, v ∈ vL ↔ v ∈ (C.activeLSF j).F.F.V)
    (hvL_at : ListAt mem0 (dgVListBase (mloc.fPtr j) (mloc.vCap j)) vL)
    (hvL_pos : ∀ i (hi : i < vL.length), mem0 (dgVPosBase (mloc.fPtr j) (mloc.vCap j) + vL[i]) = i) :
    let F := (C.activeLSF j).F.F
    ∀ (rem idx : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (q : List ℕ) (sc : ℕ)
      (φcur : ℕ → ℝ) (rootOf : ℕ → ℕ),
      idx ≤ F.n → F.n - idx = rem →
      PhiFillBfsInv mem mem0 mloc h P j scratch0 C g φ F vL q q.length sc φcur rootOf →
      (∀ k (hk : k < vL.length), k < idx → vL[k] ∈ q) →
      ∃ sc' st' cost q' φcur' rootOf',
        Runs w p ω (phiFillOuterLoopBody outerProc bfsProc zeroProc)
          (startState [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
            dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx,
            scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos)
          (.returned sc') st' cost ∧
        PhiFillBfsInv st'.mem mem0 mloc h P j scratch0 C g φ F vL q' q'.length sc' φcur' rootOf' ∧
        (∀ k (hk : k < vL.length), vL[k] ∈ q') ∧
        cost ≤ (F.n - q.length) * (phiFillEdgeStepCost j mloc.Lk + 15 * mloc.Lk + 240) +
          phiFillRemVol F q q.length * 180 + (F.n - idx) * 40 + 16 := by
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
  have hw1 : 1 < 2 ^ w := by omega
  have hsc0W : scratch0 < 2 ^ w := by omega
  have hmetaW : mloc.metaBase < 2 ^ w := by
    have : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
    have := hBel0.1; omega
  have hjW : j < 2 ^ w := by
    have : mloc.d = C.d := hPref0.1
    have : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
    have := hBel0.1; omega
  have hfPtrW : mloc.fPtr j < 2 ^ w := by omega
  have hphiJW : mloc.phiPtr j < 2 ^ w := by have := hDisj0.1; omega
  have hvListW : dgVListBase (mloc.fPtr j) (mloc.vCap j) < 2 ^ w := by unfold dgVListBase; omega
  have hnW : F.n < 2 ^ w := by omega
  have hvisPtrW : scratch0 + 1 < 2 ^ w := by omega
  have hqPtrW : scratch0 + 1 + F.n < 2 ^ w := by omega
  intro rem
  induction rem with
  | zero =>
    intro idx mem pos q sc φcur rootOf hidxLe hremEq hInv hPrev
    have hidxEq : idx = F.n := by omega
    have hqLenLe : q.length ≤ F.n := hInv.q_length_le
    have hscW : sc < 2 ^ w := by
      have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) hqLenLe
      have := hInv.2.2.2.2.2.2.2.2.2.2.2.1
      omega
    refine ⟨sc, startState [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
        dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx,
        scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos,
      6, q, φcur, rootOf, ?_, hInv, fun k hk => hPrev k hk (by omega), by omega⟩
    unfold phiFillOuterLoopBody
    have hcond : (Expr.bin .lt (.reg 6) (.reg 5)).eval w
        (startState [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
          dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx,
          scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos) = some 0 := by
      simp [Expr.eval, BinOp.eval, startState, hidxEq]
    have hret : Runs w p ω (.ret (.reg 11))
        (startState [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
          dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx,
          scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos)
        (.returned sc)
        (startState [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
          dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx,
          scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos) 2 :=
      runs_ret_iff.mpr ⟨sc, by simp [Expr.eval, startState], rfl, rfl, rfl⟩
    exact runs_cond_iff.mpr ⟨0, 2, hcond, by simpa using hret, by simp [Expr.size]⟩
  | succ rem' ih =>
    intro idx mem pos q sc φcur rootOf hidxLe hremEq hInv hPrev
    have hidxLt : idx < F.n := by omega
    have hidxLtV : idx < vL.length := by omega
    set r := vL[idx]'hidxLtV
    have hrV : r ∈ F.V := (hvL_mem r).mp (List.getElem_mem hidxLtV)
    have hrCap : r < mloc.vCap j := hF0.2.1 r hrV
    have hrW : r < 2 ^ w := by omega
    have hidxW : idx < 2 ^ w := by omega
    have hidx1W : idx + 1 < 2 ^ w := by omega
    have hqLenLe : q.length ≤ F.n := hInv.q_length_le
    have hscW : sc < 2 ^ w := by
      have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) hqLenLe
      have := hInv.2.2.2.2.2.2.2.2.2.2.2.1
      omega
    have hvisAddrW : scratch0 + 1 + idx < 2 ^ w := by omega
    have hvisMem : mem (scratch0 + 1 + idx) = if r ∈ q then 1 else 0 :=
      hInv.2.2.2.2.2.1 idx hidxLtV
    by_cases hrIn : r ∈ q
    · -- Already visited: skip directly to `idx + 1`
      have hPrev' : ∀ k (hk : k < vL.length), k < idx + 1 → vL[k] ∈ q := by
        intro k hk hlt1
        by_cases hlt : k < idx
        · exact hPrev k hk hlt
        · have hkEq : k = idx := by omega
          subst hkEq; exact hrIn
      obtain ⟨sc', st', cRec, q', φcur', rootOf', hRecRun, hInv', hCov', hRecCost⟩ :=
        ih (idx + 1) mem pos q sc φcur rootOf (by omega) (by omega) hInv hPrev'
      let T : ℕ := cRec + 40
      have hRunFull : ∃ o stFin cost,
          Runs w p ω (phiFillOuterLoopBody outerProc bfsProc zeroProc)
            (startState [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
              dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx,
              scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos) o stFin cost ∧
          (o = .returned sc' ∧ stFin.mem = st'.mem ∧ stFin.pos = st'.pos) ∧
          0 + cost ≤ T := by
        unfold phiFillOuterLoopBody
        refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, startState, hidxLt, hw1]) ?_
          (fun hc => absurd hc (by decide))
        intro _
        refine runs_seq_assign_flat (v := 1)
          (Expr.eval_load_of_eq (by eval_expr) (by dsimp only; rw [hvisMem, ite_eq_left hrIn])) ?_
        refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval])
          (fun hc => absurd rfl hc) ?_
        intro _
        refine runs_seq_rec_call hpOuter
          (vs := [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
            dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx + 1,
            scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc])
          (by eval_expr) (by wram_words) hRecRun ?_
        refine WordRAM.runs_ret_le (v := sc') (by eval_expr) ⟨rfl, rfl, rfl⟩ ?_
        simp only [T, argsSize, Expr.size]; omega
      obtain ⟨o, stFin, cost, hRun, ⟨rfl, hstFinM, _⟩, hcostLe⟩ := hRunFull
      refine ⟨sc', stFin, cost, q', φcur', rootOf', hRun, by rwa [hstFinM], hCov', ?_⟩
      have hremMul : (F.n - idx) * 40 = (F.n - (idx + 1)) * 40 + 40 := by
        conv_lhs => rw [show F.n - idx = (F.n - (idx + 1)) + 1 by omega]
        rw [Nat.add_mul, Nat.one_mul]
      omega
    · -- Unvisited component root `r = vL[idx] ∉ q`
      have hqLt : q.length < F.n := hInv.q_length_lt_of_notMem hrV hrIn
      have hqLenW : q.length < 2 ^ w := by omega
      have hqLen1W : q.length + 1 < 2 ^ w := by omega
      have hqSlotW : scratch0 + 1 + F.n + q.length < 2 ^ w := by omega
      have hrEnd : mloc.phiPtr j + r * mloc.Lk + mloc.Lk ≤ scratch0 := by
        have := mul_add_le_mul_fill (L := mloc.Lk) hrCap; have := hDisj0.1; omega
      have hrPhiW : mloc.phiPtr j + r * mloc.Lk < 2 ^ w := by omega
      have hrMulW : r * mloc.Lk < 2 ^ w := by omega
      have hF_agree : ∀ a, mloc.fPtr j ≤ a → a < mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) →
          mem a = mem0 a := fun a h1 h2 => by
        apply hInv.2.2.2.2.2.2.2.2.2.2.2.2.2 a (lt_of_lt_of_le h2 hF_hi)
        rcases hF_disj with hd | hd <;> [left; right] <;> omega
      have hnLeCap : F.n ≤ mloc.vCap j := by
        have hsub : F.V ⊆ Finset.range (mloc.vCap j) :=
          fun v hv => Finset.mem_range.mpr (hF0.2.1 v hv)
        simpa [MGraph.n] using Finset.card_le_card hsub
      have hvListAddrW : dgVListBase (mloc.fPtr j) (mloc.vCap j) + idx < 2 ^ w := by
        unfold dgVListBase; omega
      have hvListMem : mem (dgVListBase (mloc.fPtr j) (mloc.vCap j) + idx) = r := by
        rw [hF_agree _ (by unfold dgVListBase; omega) (by unfold dgVListBase; omega)]
        exact hvL_at idx hidxLtV
      -- Step 1: mark `vis[idx] := 1` -> `memV`, then call `zeroLimbs` on `phiJ[r]` -> `stZ`
      let memV : ℕ → ℕ := Function.update mem (scratch0 + 1 + idx) 1
      have hPreZero : (zeroLimbsContract w).pre [mloc.phiPtr j + r * mloc.Lk, mloc.Lk] memV :=
        ⟨mloc.phiPtr j + r * mloc.Lk, mloc.Lk, rfl, hw1, by omega⟩
      obtain ⟨zeroBody, hpZero, hZeroRuns⟩ :=
        hZero [mloc.phiPtr j + r * mloc.Lk, mloc.Lk] memV pos ω (by wram_words) hPreZero
      obtain ⟨oZ, stZ, cZ, hZeroCall, hPostZ, hCostZ⟩ := hZeroRuns
      obtain ⟨_, hZ0, hZfr⟩ := hPostZ
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hZ0 hZfr
      have hqtMemZ : stZ.mem scratch0 = q.length := by
        rw [hZfr scratch0 (Or.inr (by omega))]
        dsimp only [memV]
        rw [Function.update_of_ne (by omega)]
        exact hInv.2.2.2.1
      -- Step 2: push `r` to queue and increment `qTail` -> `memSeed`
      let memSeed : ℕ → ℕ :=
        Function.update
          (Function.update stZ.mem (scratch0 + 1 + F.n + q.length) r)
          scratch0 (q.length + 1)
      have hInvSeed : PhiFillBfsInv memSeed mem0 mloc h P j scratch0 C g φ F vL
          (q ++ [r]) q.length sc (Function.update φcur r 0) (Function.update rootOf r r) := by
        refine hInv.seedRoot hF_forest hvL_len hvL_nd hvL_mem hidxLtV hrIn hDisj0.1 hF0.2.1
          ?_ ?_ ?_ ?_ ?_
        · dsimp only [memSeed]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            hZfr _ (Or.inr (by omega))]
          dsimp only [memV]; rw [Function.update_self]
        · intro i hi
          dsimp only [memSeed]
          have hrEnd' : mloc.phiPtr j + vL[idx] * mloc.Lk + mloc.Lk ≤ scratch0 := hrEnd
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hZ0 i hi
        · dsimp only [memSeed]
          rw [Function.update_of_ne (by omega), Function.update_self]
        · dsimp only [memSeed]; rw [Function.update_self]
        · intro a h1 h2 h3 hout
          dsimp only [memSeed]
          rw [Function.update_of_ne h1, Function.update_of_ne h3, hZfr a hout]
          dsimp only [memV]; rw [Function.update_of_ne h2]
      -- Step 3: drain BFS queue via `phiFillBfsLoop_runs`
      obtain ⟨scB, stB, cB, qB, φcurB, rootOfB, hBfsRun, hqleB, hqtakeB, hInvB, hCostB⟩ :=
        phiFillBfsLoop_runs hpBfs hpAdj hEdgeStep hw16 hh hw2 hH hjD he0Cap hphiJM0 hF0
          hPref0 hBel0 hDisj0 hFitsE hFitsW hroom0 hvL_len hvL_nd hvL_mem hvL_pos
          (F.n - q.length) memSeed stZ.pos (q ++ [r]) q.length sc
          (Function.update φcur r 0) (Function.update rootOf r r) rfl hInvSeed
      -- Step 4: recurse in outer loop at `idx + 1`
      have hPrevB : ∀ k (hk : k < vL.length), k < idx + 1 → vL[k] ∈ qB := by
        intro k hk hlt1
        have hmem1 : vL[k] ∈ q ++ [r] := by
          by_cases hlt : k < idx
          · exact List.mem_append_left _ (hPrev k hk hlt)
          · have hkEq : k = idx := by omega
            subst hkEq; exact List.mem_append_right _ List.mem_cons_self
        rw [← hqtakeB] at hmem1
        exact List.mem_of_mem_take hmem1
      obtain ⟨sc', st', cRec, q', φcur', rootOf', hRecRun, hInv', hCov', hRecCost⟩ :=
        ih (idx + 1) stB.mem stB.pos qB scB φcurB rootOfB (by omega) (by omega) hInvB hPrevB
      have hscBW : scB < 2 ^ w := by
        have h1 : qB.length ≤ F.n := hInvB.q_length_le
        have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) h1
        have h2 : scB ≤ scratch0 + 1 + 2 * F.n + qB.length * phiFillEdgeStepSpace j mloc.Lk :=
          hInvB.2.2.2.2.2.2.2.2.2.2.2.1
        omega
      -- Combine the full execution of `phiFillOuterLoopBody`
      let T : ℕ := cZ + cB + cRec + 90
      have hRunFull : ∃ o stFin cost,
          Runs w p ω (phiFillOuterLoopBody outerProc bfsProc zeroProc)
            (startState [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
              dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx,
              scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos) o stFin cost ∧
          (o = .returned sc' ∧ stFin.mem = st'.mem ∧ stFin.pos = st'.pos) ∧
          0 + cost ≤ T := by
        unfold phiFillOuterLoopBody
        refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, startState, hidxLt, hw1]) ?_
          (fun hc => absurd hc (by decide))
        intro _
        refine runs_seq_assign_flat (v := 0)
          (Expr.eval_load_of_eq (by eval_expr) (by dsimp only; rw [hvisMem, ite_eq_right hrIn])) ?_
        refine WordRAM.runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hw1]) ?_
          (fun hc => absurd hc (by decide))
        intro _
        refine runs_seq_assign_flat (v := r)
          (Expr.eval_load_of_eq (by eval_expr) hvListMem) ?_
        refine runs_seq_store_le (x := scratch0 + 1 + idx) (v := 1) (by eval_expr) (by eval_expr) ?_
        have hcallZ : Runs w p ω
            (.call 14 zeroProc [.bin .add (.reg 3) (.bin .mul (.reg 13) (.reg 10)), .reg 10])
            ⟨memV, Function.update (Function.update
              (startState [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
                dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx,
                scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos).regs 12 0) 13 r, pos⟩
            .normal
            ⟨stZ.mem, Function.update (Function.update (Function.update
              (startState [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
                dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx,
                scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos).regs 12 0) 13 r) 14 oZ.value,
              stZ.pos⟩
            (6 + cZ + 1) :=
          runs_call_iff.mpr ⟨[mloc.phiPtr j + r * mloc.Lk, mloc.Lk], zeroBody, oZ, stZ, cZ,
            by eval_expr, hpZero, hZeroCall, rfl, rfl, by simp [argsSize, Expr.size]⟩
        have hAfterZ : ∃ o stFin cTail,
            Runs w p ω
              (.assign 15 (.load (.reg 9)) ;;
               .store (.bin .add (.reg 8) (.reg 15)) (.reg 13) ;;
               .store (.reg 9) (.bin .add (.reg 15) (.const 1)) ;;
               .call 16 bfsProc [.reg 0, .reg 1, .reg 2, .reg 7, .reg 8, .reg 15, .reg 9, .reg 10, .reg 11] ;;
               .call 17 outerProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5,
                 .bin .add (.reg 6) (.const 1), .reg 7, .reg 8, .reg 9, .reg 10, .reg 16] ;;
               .ret (.reg 17))
              ⟨stZ.mem, Function.update (Function.update (Function.update
                (startState [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
                  dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx,
                  scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos).regs 12 0) 13 r) 14 oZ.value,
                stZ.pos⟩
              o stFin cTail ∧
            (o = .returned sc' ∧ stFin.mem = st'.mem ∧ stFin.pos = st'.pos) ∧
            0 + cTail ≤ cB + cRec + 50 := by
          refine runs_seq_assign_flat (v := q.length)
            (Expr.eval_load_of_eq (by eval_expr) hqtMemZ) ?_
          refine runs_seq_store_le (x := scratch0 + 1 + F.n + q.length) (v := r)
            (by eval_expr) (by eval_expr) ?_
          refine runs_seq_store_le (x := scratch0) (v := q.length + 1)
            (by eval_expr) (by eval_expr) ?_
          refine runs_seq_rec_call hpBfs
            (vs := [mloc.metaBase, j, mloc.fPtr j, scratch0 + 1, scratch0 + 1 + F.n,
              q.length, scratch0, mloc.Lk, sc])
            (by eval_expr) (by wram_words) hBfsRun ?_
          refine runs_seq_rec_call hpOuter
            (vs := [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
              dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, idx + 1,
              scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, scB])
            (by eval_expr) (by wram_words) hRecRun ?_
          refine WordRAM.runs_ret_le (v := sc') (by eval_expr) ⟨rfl, rfl, rfl⟩ ?_
          simp only [argsSize, Expr.size]; omega
        obtain ⟨o, stFin, cTail, hTail, hqFin, hcTail⟩ := hAfterZ
        exact ⟨o, stFin, (6 + cZ + 1) + cTail + 1,
          runs_seq_iff.mpr (Or.inr ⟨_, 6 + cZ + 1, cTail, hcallZ, hTail, rfl⟩), hqFin, by
            simp only [T, Expr.size] at hcTail ⊢; omega⟩
      obtain ⟨o, stFin, cost, hRun, ⟨rfl, hstFinM, _⟩, hcostLe⟩ := hRunFull
      refine ⟨sc', stFin, cost, q', φcur', rootOf', hRun, by rwa [hstFinM], hCov', ?_⟩
      -- Telescope cost cleanly!
      have hq1Len : (q ++ [r]).length = q.length + 1 := by simp
      have hvol1 : phiFillRemVol F (q ++ [r]) q.length = phiFillRemVol F q q.length := by
        unfold phiFillRemVol; rw [List.take_left, List.take_length]
      change cB + (F.n - qB.length) * (phiFillEdgeStepCost j mloc.Lk + 60) +
          (F.n - qB.length) * 100 + phiFillRemVol F qB qB.length * 180 ≤
          (F.n - (q ++ [r]).length) * (phiFillEdgeStepCost j mloc.Lk + 60) +
            (F.n - q.length) * 100 + phiFillRemVol F (q ++ [r]) q.length * 180 + 20 at hCostB
      rw [hq1Len, hvol1] at hCostB
      simp only [zeroLimbsContract, zeroLimbsCost, List.getD_cons_zero, List.getD_cons_succ] at hCostZ
      have hqBle : q.length + 1 ≤ qB.length := by simpa [hq1Len] using hqleB
      have hremMul : (F.n - idx) * 40 = (F.n - (idx + 1)) * 40 + 40 := by
        conv_lhs => rw [show F.n - idx = (F.n - (idx + 1)) + 1 by omega]
        rw [Nat.add_mul, Nat.one_mul]
      have hqMulB : (F.n - qB.length) * (phiFillEdgeStepCost j mloc.Lk + 15 * mloc.Lk + 240) =
          (F.n - qB.length) * (phiFillEdgeStepCost j mloc.Lk + 60) +
          (F.n - qB.length) * 100 +
          (F.n - qB.length) * (15 * mloc.Lk + 80) := by ring
      have hqMulLe : (F.n - qB.length) * (15 * mloc.Lk + 80) ≤
          (F.n - (q.length + 1)) * (15 * mloc.Lk + 80) :=
        Nat.mul_le_mul_right _ (by omega)
      have hqStep : (F.n - q.length) * (phiFillEdgeStepCost j mloc.Lk + 15 * mloc.Lk + 240) =
          (F.n - (q.length + 1)) * (phiFillEdgeStepCost j mloc.Lk + 60) +
          (F.n - (q.length + 1)) * 100 +
          (F.n - (q.length + 1)) * (15 * mloc.Lk + 80) +
          (phiFillEdgeStepCost j mloc.Lk + 15 * mloc.Lk + 240) := by
        conv_lhs => rw [show F.n - q.length = (F.n - (q.length + 1)) + 1 by omega]
        ring
      have hpopStep : (F.n - q.length) * 100 = (F.n - (q.length + 1)) * 100 + 100 := by
        conv_lhs => rw [show F.n - q.length = (F.n - (q.length + 1)) + 1 by omega]
        rw [Nat.add_mul, Nat.one_mul]
      omega

/-! ## 2. Main verification theorems for `selectPhiFillProcs` and `selectPhiFillModule` -/

/-- `selectPhiFillProcs` meets `selectPhiFillContract` at `bSelf + pfIdxFill` (`bSelf + 8`),
provided `bAdd`, `bSub`, and `bCopy` satisfy their fixed-point contracts. -/
theorem selectPhiFill_meetsContract {w h P bAdd bSub bCopy bSelf : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ : ℕ → ℕ → ℝ} {p : Program}
    (hp : p.HasAt bSelf (selectPhiFillProcs bAdd bSub bCopy bSelf))
    (hAdd : MeetsContract w p bAdd (Num.addContract w h))
    (hSub : MeetsContract w p bSub (Num.subtractContract w h))
    (hCopy : MeetsContract w p bCopy (copyLimbsToContract w)) :
    MeetsContract w p (bSelf + pfIdxFill)
      (selectPhiFillContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ) := by
  have hpZero : p.procs[bSelf + pfIdxZeroLimbs]? = some zeroLimbsBody := by
    simpa [selectPhiFillProcs, pfIdxZeroLimbs] using hp.get (i := pfIdxZeroLimbs) (by simp [selectPhiFillProcs, pfIdxZeroLimbs])
  have hpEvalLoop : p.procs[bSelf + pfIdxEvalLoop]? =
      some (evalEdgePotGradLoopBody (bSelf + pfIdxEvalLoop) bCopy bAdd bSub) := by
    simpa [selectPhiFillProcs, pfIdxEvalLoop] using hp.get (i := pfIdxEvalLoop) (by simp [selectPhiFillProcs, pfIdxEvalLoop])
  have hpEvalEdge : p.procs[bSelf + pfIdxEvalEdge]? =
      some (evalEdgePotGradBody (bSelf + pfIdxEvalLoop) bCopy) := by
    simpa [selectPhiFillProcs, pfIdxEvalEdge] using hp.get (i := pfIdxEvalEdge) (by simp [selectPhiFillProcs, pfIdxEvalEdge])
  have hpEvalLevel : p.procs[bSelf + pfIdxEvalLevel]? =
      some (evalLevelPotGradBody (bSelf + pfIdxEvalEdge) bCopy) := by
    simpa [selectPhiFillProcs, pfIdxEvalLevel] using hp.get (i := pfIdxEvalLevel) (by simp [selectPhiFillProcs, pfIdxEvalLevel])
  have hpEdgeStep : p.procs[bSelf + pfIdxEdgeStep]? =
      some (phiFillEdgeStepBody (bSelf + pfIdxEvalLevel) bAdd bSub bCopy) := by
    simpa [selectPhiFillProcs, pfIdxEdgeStep] using hp.get (i := pfIdxEdgeStep) (by simp [selectPhiFillProcs, pfIdxEdgeStep])
  have hpAdj : p.procs[bSelf + pfIdxAdjLoop]? =
      some (phiFillAdjLoopBody (bSelf + pfIdxAdjLoop) (bSelf + pfIdxEdgeStep)) := by
    simpa [selectPhiFillProcs, pfIdxAdjLoop] using hp.get (i := pfIdxAdjLoop) (by simp [selectPhiFillProcs, pfIdxAdjLoop])
  have hpBfs : p.procs[bSelf + pfIdxBfsLoop]? =
      some (phiFillBfsLoopBody (bSelf + pfIdxBfsLoop) (bSelf + pfIdxAdjLoop)) := by
    simpa [selectPhiFillProcs, pfIdxBfsLoop] using hp.get (i := pfIdxBfsLoop) (by simp [selectPhiFillProcs, pfIdxBfsLoop])
  have hpOuter : p.procs[bSelf + pfIdxOuterLoop]? =
      some (phiFillOuterLoopBody (bSelf + pfIdxOuterLoop) (bSelf + pfIdxBfsLoop) (bSelf + pfIdxZeroLimbs)) := by
    simpa [selectPhiFillProcs, pfIdxOuterLoop] using hp.get (i := pfIdxOuterLoop) (by simp [selectPhiFillProcs, pfIdxOuterLoop])
  have hpFill : p.procs[bSelf + pfIdxFill]? =
      some (selectPhiFillBody (bSelf + pfIdxOuterLoop)) := by
    simpa [selectPhiFillProcs, pfIdxFill] using hp.get (i := pfIdxFill) (by simp [selectPhiFillProcs, pfIdxFill])
  have hZero : MeetsContract w p (bSelf + pfIdxZeroLimbs) (zeroLimbsContract w) :=
    zeroLimbs_meetsContract hpZero
  have hEvalLoop := pfEvalEdgePotGradLoop_meetsContract (P := P) (mloc := mloc) (C := C) (g := g) (φ := φ)
    hpEvalLoop hCopy hAdd hSub
  have hEvalEdge := pfEvalEdgePotGrad_meetsContract hpEvalEdge hEvalLoop hCopy
  have hEvalLevel := evalLevelPotGrad_meetsContract hpEvalLevel hEvalEdge hCopy
  have hEdgeStep := phiFillEdgeStep_meetsContract hpEdgeStep hEvalLevel hAdd hSub hCopy
  apply meetsContract_of_runs hpFill
  intro args mem pos ω hwords hpre
  obtain ⟨j, scratch, rfl, hw16, hh, hw2, hH, hjD, he0Cap, hphiJM, hfJM, hF0,
    hPref, hBel, hDisj, hFitsE, hFitsW, hzSc, hroom⟩ := hpre
  set F := (C.activeLSF j).F.F
  have hRF := (C.activeLSF_holds hH hjD).2.1
  have hF_forest : F.IsForest := hRF.1
  have hFV : F.V = (C.G j).V := hRF.2.1
  have hszF : dynGraphSize (mloc.vCap j) (mloc.eCap j) =
      4 + 7 * mloc.vCap j + 9 * mloc.eCap j := rfl
  have hsp0 : selectPhiFillSpace j F.n mloc.Lk =
      1 + 2 * F.n + F.n * phiFillEdgeStepSpace j mloc.Lk := rfl
  have hmdSz : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
  have hmetaW : mloc.metaBase < 2 ^ w := hwords mloc.metaBase (by simp)
  have hjW : j < 2 ^ w := hwords j (by simp)
  have hLkW : mloc.Lk < 2 ^ w := hwords mloc.Lk (by simp)
  have hscW : scratch < 2 ^ w := hwords scratch (by simp)
  have hdEq : mloc.d = C.d := hPref.1
  have hmdHi : mloc.metaBase + selectLevelMetaSize mloc.d ≤ scratch := hBel.1
  have hF_hi : mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ scratch := hDisj.2.1
  have hphiHi : mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ scratch := hDisj.1
  have hdMem : mem (mloc.metaBase + smDOff) = mloc.d := hPref.2.2.1
  have hdOffW : mloc.metaBase + smDOff < 2 ^ w := by unfold smDOff; omega
  have hd1W : mloc.d + 1 < 2 ^ w := by omega
  have htabW : mloc.metaBase + smTableOff < 2 ^ w := by unfold smTableOff; omega
  have h3dW : 3 * (mloc.d + 1) < 2 ^ w := by omega
  have h3djW : 3 * (mloc.d + 1) + j < 2 ^ w := by omega
  have hphiAddrEq : mloc.metaBase + smTableOff + (3 * (mloc.d + 1) + j) =
      smEntryAddr mloc.metaBase mloc.d 3 j := by unfold smEntryAddr; omega
  have hphiAddrW : mloc.metaBase + smTableOff + (3 * (mloc.d + 1) + j) < 2 ^ w := by
    unfold smTableOff; omega
  have h6dW : 6 * (mloc.d + 1) < 2 ^ w := by omega
  have h6djW : 6 * (mloc.d + 1) + j < 2 ^ w := by omega
  have hfAddrEq : mloc.metaBase + smTableOff + (6 * (mloc.d + 1) + j) =
      smEntryAddr mloc.metaBase mloc.d 6 j := by unfold smEntryAddr; omega
  have hfAddrW : mloc.metaBase + smTableOff + (6 * (mloc.d + 1) + j) < 2 ^ w := by
    unfold smTableOff; omega
  have hvcM : mem (mloc.fPtr j) = mloc.vCap j := by simpa [dgVCapOff] using hF0.2.2.2.1
  have hnM : mem (mloc.fPtr j + 2) = F.n := by simpa [dgNOff] using hF0.2.2.2.2.2.1
  have hfPtrW : mloc.fPtr j < 2 ^ w := by omega
  have hfPtr2W : mloc.fPtr j + 2 < 2 ^ w := by omega
  have hfPtr4W : mloc.fPtr j + 4 < 2 ^ w := by omega
  have hvListW : dgVListBase (mloc.fPtr j) (mloc.vCap j) < 2 ^ w := by unfold dgVListBase; omega
  have hphiJW : mloc.phiPtr j < 2 ^ w := by omega
  have hnW : F.n < 2 ^ w := by omega
  have hsc1W : scratch + 1 < 2 ^ w := by omega
  have hsc1nW : scratch + 1 + F.n < 2 ^ w := by omega
  have hsc12nW : scratch + 1 + F.n + F.n < 2 ^ w := by omega
  -- Extract live vertex list `vL` from `DynGraphAt`
  obtain ⟨vL, hvL_len, hvL_nd, hvL_mem, hvL_at, hvL_pos⟩ := hF0.2.2.2.2.2.2.2.2.1
  -- Run the outer loop starting from empty BFS state at `scratch`
  obtain ⟨sc', st', cOuter, q', φcur', rootOf', hOuterRun, hInv', hCov', hOuterCost⟩ :=
    phiFillOuterLoop_runs hpOuter hpBfs hpAdj hEdgeStep hZero hw16 hh hw2 hH hjD he0Cap hphiJM hF0
      hPref hBel hDisj hFitsE hFitsW hLkW hroom hvL_len hvL_nd hvL_mem hvL_at hvL_pos
      F.n 0 mem pos [] (scratch + 1 + 2 * F.n) (fun _ => 0) (fun _ => 0)
      (Nat.zero_le _) (Nat.sub_zero _) (PhiFillBfsInv.initial hzSc) (fun _ _ hk => absurd hk (by omega))
  -- Build full run of `selectPhiFillBody`
  apply runs_start_le
  dsimp only [startState]
  unfold selectPhiFillBody
  refine runs_seq_assign_flat (v := mloc.d)
    (Expr.eval_load_of_eq (by eval_expr) hdMem) ?_
  refine runs_seq_assign_flat (v := mloc.d + 1) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := mloc.phiPtr j)
    (Expr.eval_load_of_eq (by eval_expr) (by dsimp only; rw [hphiAddrEq]; exact hphiJM)) ?_
  refine runs_seq_assign_flat (v := mloc.fPtr j)
    (Expr.eval_load_of_eq (by eval_expr) (by dsimp only; rw [hfAddrEq]; exact hfJM)) ?_
  refine runs_seq_assign_flat (v := mloc.vCap j)
    (Expr.eval_load_of_eq (by eval_expr) hvcM) ?_
  refine runs_seq_assign_flat (v := F.n)
    (Expr.eval_load_of_eq (by eval_expr) hnM) ?_
  refine runs_seq_assign_flat (v := dgVListBase (mloc.fPtr j) (mloc.vCap j))
    (by unfold dgVListBase; eval_expr) ?_
  refine runs_seq_assign_flat (v := scratch + 1) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := scratch + 1 + F.n) (by eval_expr) ?_
  refine runs_seq_assign_flat (v := scratch + 1 + 2 * F.n)
    (by rw [show scratch + 1 + 2 * F.n = scratch + 1 + F.n + F.n by omega]; eval_expr) ?_
  refine runs_seq_rec_call hpOuter
    (vs := [mloc.metaBase, j, mloc.fPtr j, mloc.phiPtr j,
      dgVListBase (mloc.fPtr j) (mloc.vCap j), F.n, 0,
      scratch + 1, scratch + 1 + F.n, scratch, mloc.Lk, scratch + 1 + 2 * F.n])
    (by eval_expr) (by wram_words) hOuterRun ?_
  refine WordRAM.runs_ret_le (v := sc') (by eval_expr) ?_ ?_
  · dsimp only [selectPhiFillContract]
    simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
    have hqLenLe : q'.length ≤ F.n := hInv'.q_length_le
    have hmul : q'.length * phiFillEdgeStepSpace j mloc.Lk ≤
        F.n * phiFillEdgeStepSpace j mloc.Lk :=
      Nat.mul_le_mul_right _ hqLenLe
    have hscLo : scratch + 1 + 2 * F.n ≤ sc' := hInv'.2.2.2.2.2.2.2.2.2.2.1
    have hscHi : sc' ≤ scratch + 1 + 2 * F.n + q'.length * phiFillEdgeStepSpace j mloc.Lk :=
      hInv'.2.2.2.2.2.2.2.2.2.2.2.1
    have hzFin := hInv'.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hfrFin := hInv'.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hCoverV : ∀ v ∈ F.V, v ∈ q' := by
      intro v hv
      obtain ⟨k, hk, hvk⟩ := List.getElem_of_mem ((hvL_mem v).mpr hv)
      rw [← hvk]
      exact hCov' k hk
    exact ⟨by omega, by change sc' ≤ scratch + selectPhiFillSpace j F.n mloc.Lk; omega,
      hzFin, hfrFin, φcur', hInv'.finishAll hF_forest rfl hFV hCoverV⟩
  · simp only [selectPhiFillContract, selectPhiFillCost, List.getD_cons_zero,
      List.getD_cons_succ, argsSize, Expr.size]
    change cOuter ≤ (F.n - [].length) * (phiFillEdgeStepCost j mloc.Lk + 15 * mloc.Lk + 240) +
      phiFillRemVol F [] [].length * 180 + (F.n - 0) * 40 + 16 at hOuterCost
    simp only [List.length_nil, Nat.sub_zero] at hOuterCost
    have hvol0 : phiFillRemVol F [] 0 ≤ 2 * F.n := phiFillRemVol_zero_le hF_forest
    have hvolMul : phiFillRemVol F [] 0 * 180 ≤ (2 * F.n) * 180 :=
      Nat.mul_le_mul_right 180 hvol0
    have hstepEq : F.n * (phiFillEdgeStepCost j mloc.Lk + 15 * mloc.Lk + 240) +
        (2 * F.n) * 180 + F.n * 40 =
        F.n * (j * (130 * mloc.Lk + 240) + 125 * mloc.Lk + 900) := by
      unfold phiFillEdgeStepCost; ring
    change _ ≤ F.n * (j * (130 * mloc.Lk + 240) + 125 * mloc.Lk + 900) + 200
    omega

/-! ## 3. Self-contained 17-procedure module `selectPhiFillModule` -/

private theorem selectPhiFillModule_hasAdd {p : Program} {b h : ℕ}
    (hp : p.HasAt b (selectPhiFillModule b h)) :
    p.HasAt b (Num.addModule b h) := by
  intro i hi
  have hi2 : i < 2 := by simpa [Num.addModule] using hi
  have h1 := hp i (by rw [selectPhiFillModule_length]; omega)
  rw [h1]; congr 1
  simp only [selectPhiFillModule, List.append_assoc]
  exact List.getElem_append_left hi

private theorem selectPhiFillModule_hasSub {p : Program} {b h : ℕ}
    (hp : p.HasAt b (selectPhiFillModule b h)) :
    p.HasAt (b + 2) (Num.subtractModule (b + 2) h) := by
  intro i hi
  have hi5 : i < 5 := by
    simpa [Num.subtractModule, Num.negateModule, Num.addModule] using hi
  have h1 := hp (2 + i) (by rw [selectPhiFillModule_length]; omega)
  rw [show b + 2 + i = b + (2 + i) by omega, h1]; congr 1
  simp only [selectPhiFillModule, List.append_assoc]
  rw [List.getElem_append_right (by simp [Num.addModule]),
    List.getElem_append_left (by simp [Num.addModule, Num.subtractModule, Num.negateModule]; omega)]
  simp [Num.addModule]

private theorem selectPhiFillModule_hasCopy {p : Program} {b h : ℕ}
    (hp : p.HasAt b (selectPhiFillModule b h)) :
    p.procs[b + 7]? = some copyLimbsToBody := by
  have h1 := hp 7 (by rw [selectPhiFillModule_length]; omega)
  exact h1

private theorem selectPhiFillModule_hasProcs {p : Program} {b h : ℕ}
    (hp : p.HasAt b (selectPhiFillModule b h)) :
    p.HasAt (b + 8) (selectPhiFillProcs b (b + 2) (b + 7) (b + 8)) := by
  intro i hi
  have hi9 : i < 9 := by simpa [selectPhiFillProcs_length] using hi
  have h1 := hp (8 + i) (by rw [selectPhiFillModule_length]; omega)
  rw [show b + 8 + i = b + (8 + i) by omega, h1]; congr 1
  simp only [selectPhiFillModule, List.append_assoc]
  rw [List.getElem_append_right (by simp [Num.addModule]; omega),
    List.getElem_append_right (by simp [Num.addModule, Num.subtractModule, Num.negateModule]; omega),
    List.getElem_append_right (by simp [Num.addModule, Num.subtractModule, Num.negateModule]; omega)]
  simp [Num.addModule, Num.subtractModule, Num.negateModule, show 8 + i - 2 - 5 - 1 = i by omega]

/-- The self-contained 17-procedure `selectPhiFillModule b h` meets `selectPhiFillContract`
at entry index `b + 16`. -/
theorem selectPhiFillModule_meetsContract {w h P b : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ : ℕ → ℕ → ℝ} {p : Program}
    (hh : 0 < h) (hw2 : 2 * h + 2 ≤ w)
    (hp : p.HasAt b (selectPhiFillModule b h)) :
    MeetsContract w p (b + 16)
      (selectPhiFillContract w h P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ) := by
  have hAdd := Num.add_meetsContract (w := w) hh hw2 (selectPhiFillModule_hasAdd hp)
  have hSub := Num.subtract_meetsContract (w := w) hh hw2 (selectPhiFillModule_hasSub hp)
  have hCopy := copyLimbsTo_meetsContract (w := w) (selectPhiFillModule_hasCopy hp)
  simpa [pfIdxFill, Nat.add_assoc] using
    selectPhiFill_meetsContract (P := P) (mloc := mloc) (C := C) (G := G) (g := g) (ℓ := ℓ)
      (σ := σ) (σ_mwu := σ_mwu) (γ_ℓ := γ_ℓ) (γ_c := γ_c) (φ := φ)
      (selectPhiFillModule_hasProcs hp) hAdd hSub hCopy

/-- `selectPhiFillModule b h` also exposes verified `evalEdgePotGradBody` at `b + 10`. -/
theorem selectPhiFillModule_evalEdgePotGrad {w h P b : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {p : Program}
    (hh : 0 < h) (hw2 : 2 * h + 2 ≤ w)
    (hp : p.HasAt b (selectPhiFillModule b h)) :
    MeetsContract w p (b + 10) (pfEvalEdgePotGradContract w h P mloc C g φ) := by
  have hAdd := Num.add_meetsContract (w := w) hh hw2 (selectPhiFillModule_hasAdd hp)
  have hSub := Num.subtract_meetsContract (w := w) hh hw2 (selectPhiFillModule_hasSub hp)
  have hCopy := copyLimbsTo_meetsContract (w := w) (selectPhiFillModule_hasCopy hp)
  have hProcs := selectPhiFillModule_hasProcs hp
  have hpLoop : p.procs[b + 8 + pfIdxEvalLoop]? =
      some (evalEdgePotGradLoopBody (b + 8 + pfIdxEvalLoop) (b + 7) b (b + 2)) := by
    simpa [selectPhiFillProcs, pfIdxEvalLoop] using
      hProcs.get (i := pfIdxEvalLoop) (by simp [selectPhiFillProcs, pfIdxEvalLoop])
  have hpEdge : p.procs[b + 8 + pfIdxEvalEdge]? =
      some (evalEdgePotGradBody (b + 8 + pfIdxEvalLoop) (b + 7)) := by
    simpa [selectPhiFillProcs, pfIdxEvalEdge] using
      hProcs.get (i := pfIdxEvalEdge) (by simp [selectPhiFillProcs, pfIdxEvalEdge])
  have hLoop := pfEvalEdgePotGradLoop_meetsContract (P := P) (mloc := mloc) (C := C) (g := g) (φ := φ)
    hpLoop hCopy hAdd hSub
  simpa [pfIdxEvalEdge, Nat.add_assoc] using pfEvalEdgePotGrad_meetsContract hpEdge hLoop hCopy

/-- `selectPhiFillModule b h` also exposes verified `evalLevelPotGradBody` at `b + 11`. -/
theorem selectPhiFillModule_evalLevelPotGrad {w h P b : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {p : Program}
    (hh : 0 < h) (hw2 : 2 * h + 2 ≤ w)
    (hp : p.HasAt b (selectPhiFillModule b h)) :
    MeetsContract w p (b + 11) (evalLevelPotGradContract w h P mloc C g φ) := by
  have hCopy := copyLimbsTo_meetsContract (w := w) (selectPhiFillModule_hasCopy hp)
  have hEdge := selectPhiFillModule_evalEdgePotGrad (P := P) (mloc := mloc) (C := C) (g := g) (φ := φ)
    hh hw2 hp
  have hProcs := selectPhiFillModule_hasProcs hp
  have hpLevel : p.procs[b + 8 + pfIdxEvalLevel]? =
      some (evalLevelPotGradBody (b + 8 + pfIdxEvalEdge) (b + 7)) := by
    simpa [selectPhiFillProcs, pfIdxEvalLevel] using
      hProcs.get (i := pfIdxEvalLevel) (by simp [selectPhiFillProcs, pfIdxEvalLevel])
  simpa [pfIdxEvalLevel, pfIdxEvalEdge, Nat.add_assoc] using
    evalLevelPotGrad_meetsContract hpLevel (by simpa [pfIdxEvalEdge, Nat.add_assoc] using hEdge) hCopy

/-! ## 4. Non-vacuity witness -/

/-- The precondition of `selectPhiFillContract` is simultaneously satisfiable (witnessed on a
depth-0 empty chain with `w = 16`, `h = 4`, `Lk = 1`, `P = 0`). -/
theorem selectPhiFill_pre_nonvacuous :
    ∃ (mloc : SelectLevelMetaLoc) (C : TreeChain) (G : MGraph) (g ℓ : ℕ → ℝ)
      (σ σ_mwu γ_ℓ γ_c : ℝ) (φ : ℕ → ℕ → ℝ) (args : List ℕ) (mem : ℕ → ℕ),
      (selectPhiFillContract 16 4 0 mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ).pre args mem := by
  let emptyG : MGraph := { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 }
  let emptyRF : RootedForest := { F := emptyG, R := ∅ }
  let emptyLSF : LSF := { T := emptyG, F := emptyRF, wstr := fun _ => 1 }
  let C : TreeChain :=
    { d := 0, k := 1, G := fun _ => emptyG, lsfs := fun _ _ => emptyLSF, bran := fun _ => 0,
      S := fun _ _ => emptyG, emb := fun _ _ _ => [], lastK := 1,
      lastLSFs := fun _ => emptyLSF, lastBran := 0 }
  let mloc : SelectLevelMetaLoc :=
    { metaBase := 0, d := 0, Lk := 1, g0Ptr := 20,
      GPtr := fun _ => 40, vCap := fun _ => 2, eCap := fun _ => 2,
      phiPtr := fun _ => 30, coreLenPtr := fun _ => 90, embPtr := fun _ => 95,
      fPtr := fun _ => 40, sPtr := fun _ => 40 }
  -- Memory layout: metaBase [0..9] (smG0Off=0->20, smDOff=1->0, smEntry 3 0 = 5 -> 30, smEntry 6 0 = 8 -> 40),
  -- g0 [20..21], phi0 [30..31], fPtr0 [40..75] (40->2, 41->2, rest 0), scratch = 100 (all 0 from 100).
  let mem : ℕ → ℕ := fun a =>
    if a = 0 then 20
    else if a = 5 then 30
    else if a = 8 then 40
    else if a = 40 then 2
    else if a = 41 then 2
    else 0
  have hEmptyFor : emptyG.IsForest := by
    refine ⟨(fun _ h => by cases h), fun P hcyc => ?_⟩
    obtain ⟨hne, _, v, hwalk⟩ := hcyc
    cases P with
    | nil => exact hne rfl
    | cons x rest => cases hwalk with | cons he _ _ => cases he
  have hH : C.Holds emptyG (fun _ => 1) 1 1 1 1 := by
    refine ⟨rfl, (fun _ h => by cases h), by decide, by decide,
      (fun i hi => by dsimp only [C] at hi; omega),
      by decide, (fun _ _ => ⟨hEmptyFor, ⟨hEmptyFor, rfl, Finset.empty_subset _,
        (fun _ hv => by cases hv),
        ⟨Finset.Subset.refl _, Finset.Subset.refl _, (fun _ he => by cases he)⟩⟩,
        ⟨Finset.Subset.refl _, Finset.Subset.refl _, (fun _ he => by cases he)⟩,
        (fun _ he => by cases he)⟩),
      (fun _ he => by cases he)⟩
  have hF0 : DynGraphAt mem 40 2 2 emptyG := by
    refine ⟨(fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h),
      by simp [mem, dgVCapOff], by simp [mem, dgECapOff],
      by simp [mem, dgNOff, emptyG, MGraph.n], by simp [mem, dgMOff, emptyG, MGraph.m],
      (fun v hv => by simp [mem, dgVPresBase, emptyG]; split_ifs <;> omega),
      ⟨[], by simp [emptyG, MGraph.n], List.nodup_nil, (fun _ => by simp [emptyG]),
        (fun i hi => by simp at hi), (fun i hi => by simp at hi)⟩,
      (fun _ h => by cases h), (fun _ h => by cases h),
      (fun e he => by simp [mem, dgEPresBase, emptyG]; split_ifs <;> omega),
      ⟨[], by simp [emptyG, MGraph.m], List.nodup_nil, (fun _ => by simp [emptyG]),
        (fun i hi => by simp at hi), (fun i hi => by simp at hi)⟩,
      (fun _ h => by cases h),
      ⟨fun _ => [], fun s hs => ⟨IsDoublyLinkedList.nil (by simp [mem, dgIncHeadBase]; split_ifs <;> omega),
        by simp [mem, dgSlotDegBase]; split_ifs <;> omega, (fun _ => by simp [emptyG])⟩⟩⟩
  have hPref : SelectPhiPrefixAt mem mloc 4 0 C (fun _ => 0) (fun _ _ => 0) 0 :=
    ⟨rfl, by simp [mem, mloc, smG0Off], by simp [mem, mloc, smDOff],
      (fun _ he => by cases he), fun _ hk => by omega⟩
  have hBel : SelectPhiPrefixBelow mloc 0 100 :=
    ⟨by decide, by decide, fun _ hk => by omega⟩
  have hDisj : SelectPhiTargetDisjoint mloc 0 100 :=
    ⟨by decide, by decide, Or.inl (by decide), Or.inl (by decide), Or.inr (by decide),
      fun _ hk => by omega⟩
  have hFitsW : ForestWalkFits 4 1 0 emptyG (potGrad C (fun _ => 0) (fun _ _ => 0) 0) := by
    intro u v W hpath
    cases W with
    | nil =>
      simp only [walkInner_nil, zero_mul, mul_zero]
      have hpos : (0 : ℝ) < (Num.capacity 4 1 : ℝ) := by
        exact_mod_cast Num.capacity_pos 4 1
      constructor <;> linarith
    | cons x rest =>
      cases hpath.1 with
      | cons he _ _ => cases he
  refine ⟨mloc, C, emptyG, (fun _ => 0), (fun _ => 1), 1, 1, 1, 1, (fun _ _ => 0),
    [0, 0, 1, 100], mem, 0, 100, rfl, by decide, by decide, by decide, hH, le_rfl,
    (fun _ he => by cases he), by simp [mem, mloc, smEntryAddr, smTableOff],
    by simp [mem, mloc, smEntryAddr, smTableOff],
    by simpa [C, TreeChain.activeLSF, emptyLSF, emptyRF, mloc] using hF0,
    hPref, hBel, hDisj, (fun _ he => by cases he),
    by simpa [C, TreeChain.activeLSF, emptyLSF, emptyRF] using hFitsW,
    (fun a ha => by simp [mem]; split_ifs <;> omega),
    by simp [C, TreeChain.activeLSF, emptyLSF, emptyRF, emptyG, MGraph.n, selectPhiFillSpace,
      phiFillEdgeStepSpace]⟩

end MinCostFlow.MinRatio

end
