module

public import MinCostFlow.MinRatio.SelectPhiFillStep
import MinCostFlow.LSF.Walks
import WordRAM.Tactic

/-!
# Verification of `phiFillAdjLoopBody` (`SelectPhiFillAdj`)

Verifies the inner adjacency-list scan of `selectPhiFill`:
* `phiFillRemVol_pop` and `phiFillRemVol_zero_le`: degree-volume telescoping and the forest bound
  `∑ u ∈ F.V, F.deg u = 2 * F.m ≤ 2 * F.n`.
* `phiFillAdjLoop_runs`: scans the remaining suffix of `parent`'s doubly-linked incidence list in
  `F`, updating `PhiFillBfsInv`, covering all incident neighbors in `q'`, and telescoping both space
  and step cost against `(F.n - q.length)`.
* `phiFillBfsLoop_runs`: drains the BFS queue until `qHead = q'.length`, telescoping step cost
  against `(F.n - q.length)`, `(F.n - qHead)`, and `phiFillRemVol F q qHead`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Volume telescoping and recursive call helper -/

/-- Popping `q[qHead]` from the BFS queue removes `F.deg q[qHead]` from `phiFillRemVol`. -/
theorem phiFillRemVol_pop {F : MGraph} {q : List ℕ} {qHead : ℕ}
    (hqNd : q.Nodup) (hqSub : ∀ v ∈ q, v ∈ F.V) (hqH : qHead < q.length) :
    phiFillRemVol F q (qHead + 1) + F.deg q[qHead] = phiFillRemVol F q qHead := by
  unfold phiFillRemVol
  have hnot : q[qHead] ∉ (q.take qHead).toFinset := by
    rw [List.mem_toFinset]
    intro hmem
    obtain ⟨k, hk, hEq⟩ := List.getElem_of_mem hmem
    have hkLt : k < qHead := by
      have := List.length_take_le qHead q; omega
    rw [List.getElem_take] at hEq
    have := hqNd.getElem_inj_iff.mp hEq
    omega
  have huIn : q[qHead] ∈ F.V \ (q.take qHead).toFinset :=
    Finset.mem_sdiff.mpr ⟨hqSub _ (List.getElem_mem hqH), hnot⟩
  have hsetEq : F.V \ (q.take (qHead + 1)).toFinset =
      (F.V \ (q.take qHead).toFinset).erase q[qHead] := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset]
    rw [List.take_succ_eq_append_getElem hqH, List.mem_append, List.mem_singleton]
    tauto
  rw [hsetEq]
  exact Finset.sum_erase_add (F.V \ (q.take qHead).toFinset) F.deg huIn

/-- For any forest `F`, the initial degree volume is `2 * F.m ≤ 2 * F.n`. -/
theorem phiFillRemVol_zero_le {F : MGraph} (hF : F.IsForest) :
    phiFillRemVol F [] 0 ≤ 2 * F.n := by
  have hsum : ∑ u ∈ F.V, F.deg u = 2 * F.m := by
    have hdeg : ∀ u, F.deg u =
        (F.E.filter fun e => F.tail e = u).card + (F.E.filter fun e => F.head e = u).card :=
      fun _ => rfl
    simp_rw [hdeg, Finset.sum_add_distrib]
    have htail : ∑ u ∈ F.V, (F.E.filter fun e => F.tail e = u).card = F.E.card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      exact congrArg Finset.card (Finset.filter_true_of_mem fun e he => (hF.1 e he).1)
    have hhead : ∑ u ∈ F.V, (F.E.filter fun e => F.head e = u).card = F.E.card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      exact congrArg Finset.card (Finset.filter_true_of_mem fun e he => (hF.1 e he).2)
    rw [htail, hhead]
    change F.E.card + F.E.card = 2 * F.E.card
    omega
  have hm := forest_m_le_n hF
  unfold phiFillRemVol
  simp only [List.take_nil, List.toFinset_nil, Finset.sdiff_empty]
  omega

/-- Execute a recursive call whose body run is already known, then continue with `s`. -/
lemma runs_seq_rec_call {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
    {args : List Expr} {body s : Stmt} {mem regs : ℕ → ℕ} {pos : ℕ} {vs : List ℕ}
    {ret c k T : ℕ} {stCall : State} {Q : Outcome → State → Prop}
    (hproc : p.procs[f]? = some body)
    (hargs : evalArgs w ⟨mem, regs, pos⟩ args = some vs)
    (_hwords : ∀ v ∈ vs, v < 2 ^ w)
    (hcall : Runs w p ω body (startState vs mem pos) (.returned ret) stCall c)
    (hrest : ∃ o st' c', Runs w p ω s ⟨stCall.mem, Function.update regs r ret, stCall.pos⟩ o st' c' ∧
      Q o st' ∧ (k + argsSize args + c + 2) + c' ≤ T) :
    ∃ o st' cTotal, Runs w p ω (.call r f args ;; s) ⟨mem, regs, pos⟩ o st' cTotal ∧
      Q o st' ∧ k + cTotal ≤ T := by
  obtain ⟨o, st', c', hr, hq, hc⟩ := hrest
  have hcallRun : Runs w p ω (.call r f args) ⟨mem, regs, pos⟩ .normal
      ⟨stCall.mem, Function.update regs r ret, stCall.pos⟩ (argsSize args + c + 1) :=
    runs_call_iff.mpr ⟨vs, body, .returned ret, stCall, c, hargs, hproc, hcall, rfl, rfl, rfl⟩
  exact ⟨o, st', (argsSize args + c + 1) + c' + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, argsSize args + c + 1, c', hcallRun, hr, rfl⟩), hq, by omega⟩

/-! ## 2. Verification of `phiFillAdjLoopBody` -/

private lemma mul_add_le_mul_loops {v c L : ℕ} (hv : v < c) :
    v * L + L ≤ c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at this
  exact this

/-- Verification of `phiFillAdjLoopBody` by induction on the remaining suffix length `rem` of
`parent`'s doubly-linked incidence list `incL`. -/
theorem phiFillAdjLoop_runs {w h P adjProc edgeStepProc j scratch0 : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ : ℕ → ℕ → ℝ} {p : Program} {ω : ℕ → Bool}
    {mem0 : ℕ → ℕ} {vL incL : List ℕ} {parent parSlot : ℕ}
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
    (hvL_pos : ∀ i (hi : i < vL.length), mem0 (dgVPosBase (mloc.fPtr j) (mloc.vCap j) + vL[i]) = i)
    (hparV : parent ∈ (C.activeLSF j).F.F.V)
    (hparSlot : parSlot = mem0 (dgExtToIntBase (mloc.fPtr j) (mloc.vCap j) + parent))
    (hparDll : IsDoublyLinkedList mem0
      (dgHePrevBase (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j))
      (dgHeNextBase (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j))
      (dgIncHeadBase (mloc.fPtr j) (mloc.vCap j) + parSlot)
      (2 * mloc.eCap j) incL)
    (hparMem : ∀ x, x ∈ incL ↔
      x < 2 * mloc.eCap j ∧ x / 2 ∈ (C.activeLSF j).F.F.E ∧
      (if x % 2 = 0 then mem0 (dgETailSlotBase (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) + x / 2)
       else mem0 (dgEHeadSlotBase (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) + x / 2)) = parSlot) :
    let F := (C.activeLSF j).F.F
    ∀ (rem posIdx : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (q : List ℕ) (qHead sc : ℕ)
      (φcur : ℕ → ℝ) (rootOf : ℕ → ℕ),
      posIdx ≤ incL.length → incL.length - posIdx = rem →
      parent ∈ q →
      PhiFillBfsInv mem mem0 mloc h P j scratch0 C g φ F vL q qHead sc φcur rootOf →
      let cur := if h : posIdx < incL.length then incL[posIdx] + 1 else 0
      ∃ sc' st' cost q' φcur' rootOf',
        Runs w p ω (phiFillAdjLoopBody adjProc edgeStepProc)
          (startState [mloc.metaBase, j, mloc.fPtr j, parent, cur,
            scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos)
          (.returned sc') st' cost ∧
        q.length ≤ q'.length ∧ q'.take q.length = q ∧
        PhiFillBfsInv st'.mem mem0 mloc h P j scratch0 C g φ F vL q' qHead sc' φcur' rootOf' ∧
        (∀ x ∈ incL.drop posIdx,
          (x % 2 = 0 → F.head (x / 2) ∈ q') ∧ (x % 2 ≠ 0 → F.tail (x / 2) ∈ q')) ∧
        cost + (F.n - q'.length) * (phiFillEdgeStepCost j mloc.Lk + 60) ≤
          rem * 180 + (F.n - q.length) * (phiFillEdgeStepCost j mloc.Lk + 60) + 12 := by
  dsimp only
  set F := (C.activeLSF j).F.F
  have hRF := (C.activeLSF_holds hH hjD).2.1
  have hF_forest : F.IsForest := hRF.1
  have hF_sub : (C.G j).IsSubgraph F := hRF.2.2.2.2
  have hszF : dynGraphSize (mloc.vCap j) (mloc.eCap j) =
      4 + 7 * mloc.vCap j + 9 * mloc.eCap j := rfl
  have hF_hi : mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ scratch0 := hDisj0.2.1
  have hF_disj : mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ mloc.phiPtr j ∨
      mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.fPtr j := hDisj0.2.2.2.2.1
  have hMeta_hi : mloc.metaBase + selectLevelMetaSize mloc.d ≤ scratch0 := hBel0.1
  have hMeta_disj : mloc.metaBase + selectLevelMetaSize mloc.d ≤ mloc.phiPtr j ∨
      mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.metaBase := hDisj0.2.2.1
  have hsp0 : selectPhiFillSpace j F.n mloc.Lk =
      1 + 2 * F.n + F.n * phiFillEdgeStepSpace j mloc.Lk := rfl
  have hsc0W : scratch0 < 2 ^ w := by omega
  have hmetaW : mloc.metaBase < 2 ^ w := by
    have : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl; omega
  have hjW : j < 2 ^ w := by
    have : mloc.d = C.d := hPref0.1
    have : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl; omega
  have hfPtrW : mloc.fPtr j < 2 ^ w := by omega
  have hparCap : parent < mloc.vCap j := hF0.2.1 parent hparV
  have hparW : parent < 2 ^ w := by omega
  have hvisPtrW : scratch0 + 1 < 2 ^ w := by omega
  have hqPtrW : scratch0 + 1 + F.n < 2 ^ w := by omega
  have hLkW : mloc.Lk < 2 ^ w := by
    by_cases hFn : F.n = 0
    · exfalso; have : 0 < F.n := Finset.card_pos.mpr ⟨parent, hparV⟩; omega
    · have h1 : mloc.Lk ≤ phiFillEdgeStepSpace j mloc.Lk := by
        unfold phiFillEdgeStepSpace; nlinarith
      have h2 : phiFillEdgeStepSpace j mloc.Lk ≤ F.n * phiFillEdgeStepSpace j mloc.Lk :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
  have hw1 : 1 < 2 ^ w := by omega
  intro rem
  induction rem with
  | zero =>
    intro posIdx mem pos q qHead sc φcur rootOf hposLe hremEq hparQ hInv
    have hposEq : posIdx = incL.length := by omega
    have hcur0 : (if h : posIdx < incL.length then incL[posIdx] + 1 else 0) = 0 :=
      dite_eq_right_of_eq_false (eq_false (by omega))
    rw [hcur0]
    have hqLenLe : q.length ≤ F.n := hInv.q_length_le
    have hscW : sc < 2 ^ w := by
      have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) hqLenLe
      have := hInv.2.2.2.2.2.2.2.2.2.2.2.1
      omega
    refine ⟨sc, startState [mloc.metaBase, j, mloc.fPtr j, parent, 0,
      scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos, 6, q, φcur, rootOf, ?_,
      le_rfl, List.take_length, hInv, fun x hx => by simp [hposEq] at hx, by omega⟩
    unfold phiFillAdjLoopBody
    have hcond : (Expr.bin .eq (.reg 4) (.const 0)).eval w
        (startState [mloc.metaBase, j, mloc.fPtr j, parent, 0,
          scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos) = some 1 := by
      simp [Expr.eval, BinOp.eval, startState, hw1]
    have hret : Runs w p ω (.ret (.reg 9))
        (startState [mloc.metaBase, j, mloc.fPtr j, parent, 0,
          scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos)
        (.returned sc)
        (startState [mloc.metaBase, j, mloc.fPtr j, parent, 0,
          scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos) 2 :=
      runs_ret_iff.mpr ⟨sc, by simp [Expr.eval, startState], rfl, rfl, rfl⟩
    exact runs_cond_iff.mpr ⟨1, 2, hcond, by simpa using hret, by simp [Expr.size]⟩
  | succ rem' ih =>
    intro posIdx mem pos q qHead sc φcur rootOf hposLe hremEq hparQ hInv
    have hposLt : posIdx < incL.length := by omega
    set he := incL[posIdx]'hposLt
    have hcurEq : (if h : posIdx < incL.length then incL[posIdx] + 1 else 0) = he + 1 :=
      dite_eq_left_of_eq_true (eq_true hposLt)
    rw [hcurEq]
    have hqLenLe : q.length ≤ F.n := hInv.q_length_le
    have hscW : sc < 2 ^ w := by
      have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) hqLenLe
      have := hInv.2.2.2.2.2.2.2.2.2.2.2.1
      omega
    -- All F0 words agree between mem and mem0
    have hfr0 := hInv.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hF_agree : ∀ a, mloc.fPtr j ≤ a → a < mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) →
        mem a = mem0 a := fun a h1 h2 => by
      apply hfr0 a (lt_of_lt_of_le h2 hF_hi)
      rcases hF_disj with hd | hd <;> [left; right] <;> omega
    have hFm : DynGraphAt mem (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) F :=
      DynGraphAt.of_agree hF0 hF_agree
    -- Properties of half-edge `he`
    have hheMem : he ∈ incL := List.getElem_mem hposLt
    obtain ⟨hheCap, hfE, hheSlot⟩ := (hparMem he).mp hheMem
    set f := he / 2
    set dir := he % 2
    have hfCap : f < mloc.eCap j := by omega
    have hdir01 : dir = 0 ∨ dir = 1 := by omega
    have hFends := dynGraphAt_read_endpoints hF0 hfE
    have hFslots := hF0.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hfE
    have hFbi := hF0.2.2.2.2.2.2.2.2.2.1
    have hFvalid := hF0.1 f hfE
    -- Determine parent/child endpoints and direction
    have hparIsEnd : (dir = 0 → F.tail f = parent) ∧ (dir ≠ 0 → F.head f = parent) := by
      constructor
      · intro hd0
        simp only [hd0, ↓reduceIte] at hheSlot
        have h1 := congrArg (fun s => mem0 (dgIntToExtBase (mloc.fPtr j) (mloc.vCap j) + s)) hheSlot
        rw [hparSlot, (hFbi parent hparV).2, hFends.1] at h1
        exact h1
      · intro hdnz
        simp only [hdnz, ↓reduceIte] at hheSlot
        have h1 := congrArg (fun s => mem0 (dgIntToExtBase (mloc.fPtr j) (mloc.vCap j) + s)) hheSlot
        rw [hparSlot, (hFbi parent hparV).2, hFends.2] at h1
        exact h1
    set child := if dir = 0 then F.head f else F.tail f
    have hdirSpec : (dir ≠ 0 ∧ F.tail f = child ∧ F.head f = parent) ∨
        (dir = 0 ∧ F.head f = child ∧ F.tail f = parent) := by
      by_cases hd0 : dir = 0
      · exact Or.inr ⟨hd0, by simp [child, hd0], hparIsEnd.1 hd0⟩
      · exact Or.inl ⟨hd0, by simp [child, hd0], hparIsEnd.2 hd0⟩
    have hchV : child ∈ F.V := by
      rcases hdirSpec with ⟨_, ht, _⟩ | ⟨_, hh, _⟩
      · exact ht ▸ hFvalid.1
      · exact hh ▸ hFvalid.2
    have hchCap : child < mloc.vCap j := hF0.2.1 child hchV
    have hnePC : parent ≠ child := by
      have hnsl := LSF.isForest_no_selfLoop hF_forest hfE
      rcases hdirSpec with ⟨_, ht, hh⟩ | ⟨_, hh, ht⟩ <;> omega
    -- Locate child in vL
    obtain ⟨chIdx, hchIdxLt, hchIdxEq⟩ := List.getElem_of_mem ((hvL_mem child).mpr hchV)
    have hchPosMem : mem (dgVPosBase (mloc.fPtr j) (mloc.vCap j) + child) = chIdx := by
      rw [hF_agree _ (by unfold dgVPosBase; omega) (by unfold dgVPosBase; omega)]
      rw [← hchIdxEq]; exact hvL_pos chIdx hchIdxLt
    -- Next cursor in DLL
    set nextCur := if h : posIdx + 1 < incL.length then incL[posIdx + 1] + 1 else 0
    have hnextMem : mem (dgHeNextBase (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) + he) = nextCur := by
      rw [hF_agree _ (by unfold dgHeNextBase; omega) (by unfold dgHeNextBase; omega)]
      have hb := (hparDll.2.2.2 posIdx hposLt).2
      change mem0 (dgHeNextBase (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) + he) = _ at hb
      rw [hb]
      dsimp only [nextCur]
      by_cases h1 : posIdx + 1 < incL.length
      · rw [ite_eq_right (by omega : posIdx + 1 ≠ incL.length),
          dite_eq_left_of_eq_true (eq_true h1), List.getD_eq_getElem _ _ h1]
      · rw [ite_eq_left (by omega : posIdx + 1 = incL.length),
          dite_eq_right_of_eq_false (eq_false h1)]
    have hnextW : nextCur < 2 ^ w := by
      dsimp only [nextCur]; split_ifs with h1
      · have := (hparMem _).mp (List.getElem_mem h1) |>.1; omega
      · omega
    -- Child slot and child read from memory
    set childSlot := mem (dgEPresBase (mloc.fPtr j) (mloc.vCap j) + (4 - dir) * mloc.eCap j + f)
    have hchSlotEq : childSlot = mem0 (dgExtToIntBase (mloc.fPtr j) (mloc.vCap j) + child) := by
      dsimp only [childSlot]
      rcases hdir01 with hd0 | hd1
      · have haddr : dgEPresBase (mloc.fPtr j) (mloc.vCap j) + (4 - dir) * mloc.eCap j + f =
            dgEHeadSlotBase (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) + f := by
          unfold dgEPresBase dgEHeadSlotBase; rw [hd0]
        rw [haddr, hF_agree _ (by unfold dgEHeadSlotBase; omega) (by unfold dgEHeadSlotBase; omega),
          hFslots.2]
        simp [child, hd0]
      · have haddr : dgEPresBase (mloc.fPtr j) (mloc.vCap j) + (4 - dir) * mloc.eCap j + f =
            dgETailSlotBase (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) + f := by
          unfold dgEPresBase dgETailSlotBase; rw [hd1]
        rw [haddr, hF_agree _ (by unfold dgETailSlotBase; omega) (by unfold dgETailSlotBase; omega),
          hFslots.1]
        simp [child, hd1]
    have hchSlotCap : childSlot < mloc.vCap j := by
      rw [hchSlotEq]; exact hF0.2.1 _ (hFbi child hchV).1
    have hchExtMem : mem (dgIntToExtBase (mloc.fPtr j) (mloc.vCap j) + childSlot) = child := by
      rw [hF_agree _ (by unfold dgIntToExtBase; omega) (by unfold dgIntToExtBase; omega),
        hchSlotEq, (hFbi child hchV).2]
    -- Address / word bounds for straight-line body
    have hheW : he < 2 ^ w := by omega
    have hcurW : he + 1 < 2 ^ w := by omega
    have hfW : f < 2 ^ w := by omega
    have hdirW : dir < 2 ^ w := by omega
    have hvcW : mloc.vCap j < 2 ^ w := by omega
    have hecW : mloc.eCap j < 2 ^ w := by omega
    have hchW : child < 2 ^ w := by omega
    have hchIdxW : chIdx < 2 ^ w := by omega
    have hvcM : mem (mloc.fPtr j) = mloc.vCap j := by simpa [dgVCapOff] using hFm.2.2.2.1
    have hecM : mem (mloc.fPtr j + 1) = mloc.eCap j := by simpa [dgECapOff] using hFm.2.2.2.2.1
    have hfPtr1W : mloc.fPtr j + 1 < 2 ^ w := by omega
    have hfPtr4W : mloc.fPtr j + 4 < 2 ^ w := by omega
    have h7vcW : 7 * mloc.vCap j < 2 ^ w := by omega
    have h4vcW : 4 * mloc.vCap j < 2 ^ w := by omega
    have h2vcW : 2 * mloc.vCap j < 2 ^ w := by omega
    have hePresW : dgEPresBase (mloc.fPtr j) (mloc.vCap j) < 2 ^ w := by unfold dgEPresBase; omega
    have h7ecW : 7 * mloc.eCap j < 2 ^ w := by omega
    have hheNextAddrW : dgHeNextBase (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) + he < 2 ^ w := by
      unfold dgHeNextBase; omega
    have h4dirW : 4 - dir < 2 ^ w := by omega
    have h4dirEcW : (4 - dir) * mloc.eCap j < 2 ^ w := by
      rcases hdir01 with hd | hd <;> (rw [hd]; omega)
    have hchSlotAddrW : dgEPresBase (mloc.fPtr j) (mloc.vCap j) + (4 - dir) * mloc.eCap j + f < 2 ^ w := by
      unfold dgEPresBase; rcases hdir01 with hd | hd <;> (rw [hd]; omega)
    have hchExtAddrW : dgIntToExtBase (mloc.fPtr j) (mloc.vCap j) + childSlot < 2 ^ w := by
      unfold dgIntToExtBase; omega
    have hchPosAddrW : dgVPosBase (mloc.fPtr j) (mloc.vCap j) + child < 2 ^ w := by
      unfold dgVPosBase; omega
    have hvisChAddrW : scratch0 + 1 + chIdx < 2 ^ w := by omega
    have hvisChMem : mem (scratch0 + 1 + chIdx) = if child ∈ q then 1 else 0 := by
      rw [hInv.2.2.2.2.2.1 chIdx hchIdxLt, hchIdxEq]
    -- Run statement cleanly using suffices
    suffices hRun : ∃ o st' cost,
        Runs w p ω (phiFillAdjLoopBody adjProc edgeStepProc)
          (startState [mloc.metaBase, j, mloc.fPtr j, parent, he + 1,
            scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos) o st' cost ∧
        (∃ sc' q' φcur' rootOf',
          o = .returned sc' ∧
          q.length ≤ q'.length ∧ q'.take q.length = q ∧
          PhiFillBfsInv st'.mem mem0 mloc h P j scratch0 C g φ F vL q' qHead sc' φcur' rootOf' ∧
          (∀ x ∈ incL.drop posIdx,
            (x % 2 = 0 → F.head (x / 2) ∈ q') ∧ (x % 2 ≠ 0 → F.tail (x / 2) ∈ q')) ∧
          cost + (F.n - q'.length) * (phiFillEdgeStepCost j mloc.Lk + 60) ≤
            (rem' + 1) * 180 + (F.n - q.length) * (phiFillEdgeStepCost j mloc.Lk + 60) + 12) by
      obtain ⟨o, st', cost, hr, sc', q', φcur', rootOf', rfl, hqle, hqtake, hinv', hcov', hcost⟩ := hRun
      exact ⟨sc', st', cost, q', φcur', rootOf', hr, hqle, hqtake, hinv', hcov', hcost⟩
    -- Track the cost directly with a helper, and split on `child ∈ q` right after the 11
    -- straight-line assigns.
    -- Helper: run the 11 assigns
    have hbody1 : ∀ (k : ℕ) (T : ℕ) (Q : Outcome → State → Prop),
        (∀ st1, st1.mem = mem → st1.pos = pos →
          st1.regs 0 = mloc.metaBase → st1.regs 1 = j → st1.regs 2 = mloc.fPtr j →
          st1.regs 3 = parent → st1.regs 5 = scratch0 + 1 → st1.regs 6 = scratch0 + 1 + F.n →
          st1.regs 7 = scratch0 → st1.regs 8 = mloc.Lk → st1.regs 9 = sc →
          st1.regs 11 = f → st1.regs 12 = dir → st1.regs 16 = nextCur →
          st1.regs 18 = child → st1.regs 19 = chIdx →
          st1.regs 20 = (if child ∈ q then 1 else 0) →
          ∃ o st' c, Runs w p ω
            (.cond (.bin .eq (.reg 20) (.const 0))
              (.store (.bin .add (.reg 5) (.reg 19)) (.const 1) ;;
               .assign 21 (.load (.reg 7)) ;;
               .store (.bin .add (.reg 6) (.reg 21)) (.reg 18) ;;
               .store (.reg 7) (.bin .add (.reg 21) (.const 1)) ;;
               .call 9 edgeStepProc [.reg 0, .reg 1, .reg 11, .reg 3, .reg 18, .reg 12, .reg 8, .reg 9])
              .nop ;;
             .call 22 adjProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 16, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9] ;;
             .ret (.reg 22)) st1 o st' c ∧ Q o st' ∧ (k + 120) + c ≤ T) →
        ∃ o st' c, Runs w p ω (phiFillAdjLoopBody adjProc edgeStepProc)
          (startState [mloc.metaBase, j, mloc.fPtr j, parent, he + 1,
            scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc] mem pos) o st' c ∧
          Q o st' ∧ k + c ≤ T := by
      intro k T Q hcont
      unfold phiFillAdjLoopBody
      refine WordRAM.runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, startState])
        (fun hc => absurd rfl hc) ?_
      intro _
      refine runs_seq_assign_flat (v := he)
        (by simp [Expr.eval, BinOp.eval, hw1, hheW]) ?_
      refine runs_seq_assign_flat (v := f)
        (by simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, hfW, f]) ?_
      refine runs_seq_assign_flat (v := dir)
        (by simp [Expr.eval, BinOp.eval, show 2 < 2 ^ w by omega, hdirW, dir]) ?_
      refine runs_seq_assign_flat (v := mloc.vCap j)
        (Expr.eval_load_of_eq (by eval_expr) hvcM) ?_
      refine runs_seq_assign_flat (v := mloc.eCap j)
        (Expr.eval_load_of_eq (by eval_expr) hecM) ?_
      refine runs_seq_assign_flat (v := dgEPresBase (mloc.fPtr j) (mloc.vCap j))
        (by unfold dgEPresBase; eval_expr) ?_
      have hheNextAddrW' : dgEPresBase (mloc.fPtr j) (mloc.vCap j) + 7 * mloc.eCap j + he < 2 ^ w := by
        unfold dgEPresBase; unfold dgHeNextBase at hheNextAddrW; omega
      have hnextMem' : mem (dgEPresBase (mloc.fPtr j) (mloc.vCap j) + 7 * mloc.eCap j + he) = nextCur := by
        convert hnextMem using 2; unfold dgHeNextBase dgEPresBase; omega
      refine runs_seq_assign_flat (v := nextCur)
        (Expr.eval_load_of_eq (by eval_expr) hnextMem') ?_
      refine runs_seq_assign_flat (v := childSlot)
        (Expr.eval_load_of_eq (by unfold dgEPresBase at hchSlotAddrW ⊢; eval_expr)
          (by unfold dgEPresBase; rfl)) ?_
      refine runs_seq_assign_flat (v := child)
        (Expr.eval_load_of_eq (by unfold dgIntToExtBase at hchExtAddrW; eval_expr)
          (by rw [← hchSlotEq]; unfold dgIntToExtBase at hchExtMem; exact hchExtMem)) ?_
      refine runs_seq_assign_flat (v := chIdx)
        (Expr.eval_load_of_eq (by unfold dgVPosBase at hchPosAddrW; eval_expr)
          (by unfold dgVPosBase at hchPosMem; exact hchPosMem)) ?_
      refine runs_seq_assign_flat (v := if child ∈ q then 1 else 0)
        (Expr.eval_load_of_eq (by eval_expr) hvisChMem) ?_
      refine (fun ⟨o, st', c, hr, hq, hc⟩ =>
          ⟨o, st', c, hr, hq, by simp only [Expr.size] at hc ⊢; omega⟩)
        (hcont _ rfl rfl
          (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
    -- Split on whether child is already visited
    by_cases hchIn : child ∈ q
    · -- Already visited: skip edgeStep, recurse with same q and sc
      obtain ⟨sc', st', cRec, q', φcur', rootOf', hRecRun, hqle, hqtake, hInv', hCov', hRecCost⟩ :=
        ih (posIdx + 1) mem pos q qHead sc φcur rootOf (by omega) (by omega) hparQ hInv
      have hsc'W : sc' < 2 ^ w := by
        have := hInv'.q_length_le
        have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) this
        have := hInv'.2.2.2.2.2.2.2.2.2.2.2.1
        omega
      let T : ℕ := 180 + cRec
      obtain ⟨o, stFin, cost, hRun, ⟨rfl, hstFin⟩, hcostLe⟩ :=
        hbody1 0 T (fun o st => o = .returned sc' ∧ st.mem = st'.mem ∧ st.pos = st'.pos)
          (fun st1 hmem1 hpos1 hr0 hr1 hr2 hr3 hr5 hr6 hr7 hr8 hr9 hr11 hr12 hr16 hr18 hr19 hr20 => by
            rcases st1 with ⟨m1, regs1, p1⟩
            dsimp only at hmem1 hpos1 hr0 hr1 hr2 hr3 hr5 hr6 hr7 hr8 hr9 hr11 hr12 hr16 hr18 hr19 hr20
            subst m1; subst p1
            rw [ite_eq_left hchIn] at hr20
            refine runs_seq_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hr20])
              (fun hc => absurd rfl hc) ?_
            intro _
            refine runs_seq_nop_le ?_
            refine runs_seq_rec_call hpAdj
              (vs := [mloc.metaBase, j, mloc.fPtr j, parent, nextCur,
                scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc])
              (by simp [evalArgs, Expr.eval, hr0, hr1, hr2, hr3, hr16, hr5, hr6, hr7, hr8, hr9])
              (by wram_words) hRecRun ?_
            refine WordRAM.runs_ret_le (v := sc') (by simp [Expr.eval])
              ⟨rfl, rfl, rfl⟩ ?_
            simp only [T, argsSize, Expr.size]; omega)
      refine ⟨.returned sc', stFin, cost, hRun, sc', q', φcur', rootOf', rfl, hqle, hqtake,
        by rwa [hstFin.1], fun x hx => ?_, by
          rw [show (rem' + 1) * 180 = rem' * 180 + 180 by ring]; omega⟩
      rw [List.drop_eq_getElem_cons hposLt] at hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · have hchQ' : child ∈ q' := by
          rw [← hqtake] at hchIn; exact List.mem_of_mem_take hchIn
        rcases hdirSpec with ⟨hdnz, ht, _⟩ | ⟨hd0, hh, _⟩
        · exact ⟨fun h => absurd h hdnz, fun _ => ht.symm ▸ hchQ'⟩
        · exact ⟨fun _ => hh.symm ▸ hchQ', fun h => absurd hd0 h⟩
      · exact hCov' x hx'
    · -- Unvisited child: mark visited, push to queue, call edgeStep, then recurse
      have hqLt : q.length < F.n := hInv.q_length_lt_of_notMem hchV hchIn
      have hqLenW : q.length < 2 ^ w := by omega
      have hqLen1W : q.length + 1 < 2 ^ w := by omega
      have hqSlotW : scratch0 + 1 + F.n + q.length < 2 ^ w := by omega
      have hFsubG : f ∈ (C.G j).E := hF_sub.2.1 hfE
      have hf0 : f ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le j) hjD hFsubG
      have hfAll : ∀ k < j, f ∈ (C.G k).E := fun k hkj =>
        C.G_E_subset_of_le hH (Nat.le_of_lt hkj) hjD hFsubG
      -- Compute mem1 after the 3 scratch stores (vis[chIdx] := 1, q[q.length] := child, qTail := q.length + 1)
      let mem1 : ℕ → ℕ :=
        Function.update
          (Function.update
            (Function.update mem (scratch0 + 1 + chIdx) 1)
            (scratch0 + 1 + F.n + q.length) child)
          scratch0 (q.length + 1)
      have hmem1_below : ∀ a < scratch0, mem1 a = mem a := fun a ha => by
        dsimp only [mem1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
      have hmem1_sc : ZeroFrom mem1 sc := fun a ha => by
        have := hInv.2.2.2.2.2.2.2.2.2.2.1
        dsimp only [mem1]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
        exact hInv.2.2.2.2.2.2.2.2.2.2.2.2.1 a ha
      have hmem1_phiJM : mem1 (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j := by
        have hlt : smEntryAddr mloc.metaBase mloc.d 3 j < scratch0 := by
          have : mloc.d = C.d := hPref0.1
          have : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
          have := Nat.mul_le_mul_right (mloc.d + 1) (show 3 ≤ 7 by omega)
          unfold smEntryAddr smTableOff at *; omega
        have hout : smEntryAddr mloc.metaBase mloc.d 3 j < mloc.phiPtr j ∨
            mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ smEntryAddr mloc.metaBase mloc.d 3 j := by
          have : mloc.d = C.d := hPref0.1
          have : selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) := rfl
          have := Nat.mul_le_mul_right (mloc.d + 1) (show 3 ≤ 7 by omega)
          rcases hMeta_disj with h1 | h2
          · left; unfold smEntryAddr smTableOff at *; omega
          · right; unfold smEntryAddr smTableOff at *; omega
        rw [hmem1_below _ hlt, hfr0 _ hlt hout, hphiJM0]
      have hPref1 : SelectPhiPrefixAt mem1 mloc h P C g φ j :=
        hPref0.of_agree_outside_target hBel0 hDisj0 (by omega) he0Cap
          (fun a ha hout => (hmem1_below a ha).trans (hfr0 a ha hout))
      have hparEnd : mloc.phiPtr j + parent * mloc.Lk + mloc.Lk ≤ scratch0 := by
        have := mul_add_le_mul_loops (L := mloc.Lk) hparCap; have := hDisj0.1; omega
      have hparEdgeV := hInv.2.2.2.2.2.2.1 parent (List.mem_toFinset.mpr hparQ)
      have hvPar1 : Num.Valid mem1 (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk :=
        fun i hi => by rw [hmem1_below _ (by omega)]; exact hparEdgeV.1 i hi
      have hparFix1 : Num.fixVal mem1 (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk P = φcur parent := by
        unfold Num.fixVal
        rw [Num.intVal_congr (fun i hi => hmem1_below _ (by omega))]
        exact hparEdgeV.2
      -- Prove cVal fits via ForestWalkFits!
      have hFitsC :
          let pVal := Num.fixVal mem1 (mloc.phiPtr j + parent * mloc.Lk) h mloc.Lk P;
          let gVal := potGrad C g φ j f;
          let cVal := if dir ≠ 0 then pVal + gVal else pVal - gVal;
          -(Num.capacity h mloc.Lk : ℝ) ≤ 2 * (cVal * (2 : ℝ) ^ P) ∧
          2 * (cVal * (2 : ℝ) ^ P) < (Num.capacity h mloc.Lk : ℝ) := by
        dsimp only
        rw [hparFix1]
        obtain ⟨_, hconnPR, hvertsPR, hvalPar⟩ := hInv.2.2.2.2.2.2.2.1 parent hparQ
        let dirB : Bool := decide (dir ≠ 0)
        have hsrcE : F.src (f, dirB) = child := by
          rcases hdirSpec with ⟨hnz, ht, _⟩ | ⟨hz0, hh, _⟩
          · simp [dirB, hnz, MGraph.src, ht]
          · simp [dirB, hz0, MGraph.src, hh]
        have hdstE : F.dst (f, dirB) = parent := by
          rcases hdirSpec with ⟨hnz, _, hh⟩ | ⟨hz0, _, ht⟩
          · simp [dirB, hnz, MGraph.dst, hh]
          · simp [dirB, hz0, MGraph.dst, ht]
        have hpathC : F.IsPath child (rootOf parent) ((f, dirB) :: F.forestPath parent (rootOf parent)) :=
          isPath_cons_of_not_mem_walkVertices hfE hsrcE hdstE
            (LSF.forestPath_isPath hF_forest hconnPR) (fun hc => hchIn (hvertsPR child hc))
        have hwalkEq : walkInner (potGrad C g φ j) ((f, dirB) :: F.forestPath parent (rootOf parent)) =
            if dir ≠ 0 then φcur parent + potGrad C g φ j f else φcur parent - potGrad C g φ j f := by
          rw [walkInner_cons, walkInner_singleton, ← hvalPar]
          by_cases hnz : dir ≠ 0
          · simp [dirB, hnz]; ring
          · simp [dirB, hnz]; ring
        rw [← hwalkEq]
        exact hFitsW child (rootOf parent) _ hpathC
      have hscStepRoom : sc + phiFillEdgeStepSpace j mloc.Lk < 2 ^ w := by
        have h1 := hInv.2.2.2.2.2.2.2.2.2.2.2.1
        have h2 : (q.length + 1) * phiFillEdgeStepSpace j mloc.Lk ≤
            F.n * phiFillEdgeStepSpace j mloc.Lk :=
          Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hqLt)
        rw [Nat.add_mul, Nat.one_mul] at h2
        omega
      have hBelSc : SelectPhiPrefixBelow mloc j sc := by
        have hscGe : scratch0 ≤ sc := by have := hInv.2.2.2.2.2.2.2.2.2.2.1; omega
        exact ⟨le_trans hBel0.1 hscGe, le_trans hBel0.2.1 hscGe,
          fun k hk => ⟨le_trans (hBel0.2.2 k hk).1 hscGe, le_trans (hBel0.2.2 k hk).2 hscGe⟩⟩
      have hDisjSc : SelectPhiTargetDisjoint mloc j sc := by
        have hscGe : scratch0 ≤ sc := by have := hInv.2.2.2.2.2.2.2.2.2.2.1; omega
        exact ⟨le_trans hDisj0.1 hscGe, le_trans hDisj0.2.1 hscGe, hDisj0.2.2⟩
      have hPreEdge : (phiFillEdgeStepContract w h P mloc C g φ).pre
          [mloc.metaBase, j, f, parent, child, dir, mloc.Lk, sc] mem1 :=
        ⟨j, f, parent, child, dir, sc, rfl, hw16, hh, hw2, hjD, hf0, he0Cap f hf0, hfAll,
          hparCap, hchCap, hnePC, hmem1_phiJM, hPref1, hBelSc, hDisjSc, hvPar1,
          hFitsE f hfE, hFitsC, hmem1_sc, hscStepRoom⟩
      -- Run the body!
      have hInvNext : ∀ sc1 mem2,
          (phiFillEdgeStepContract w h P mloc C g φ).post
            [mloc.metaBase, j, f, parent, child, dir, mloc.Lk, sc] mem1 sc1 mem2 →
          PhiFillBfsInv mem2 mem0 mloc h P j scratch0 C g φ F vL (q ++ [child]) qHead sc1
            (Function.update φcur child
              (if dir ≠ 0 then φcur parent + potGrad C g φ j f else φcur parent - potGrad C g φ j f))
            (Function.update rootOf child (rootOf parent)) := by
        intro sc1 mem2 hpE
        obtain ⟨hscLo1, hscHi1, hvCh2, hfixCh2, hz2, hfr2⟩ := hpE
        simp only [List.getD_cons_zero, List.getD_cons_succ] at hscLo1 hscHi1 hvCh2 hfixCh2 hz2 hfr2
        rw [hparFix1] at hfixCh2
        have hchEnd : mloc.phiPtr j + child * mloc.Lk + mloc.Lk ≤ scratch0 := by
          have := mul_add_le_mul_loops (L := mloc.Lk) hchCap; have := hDisj0.1; omega
        have hscLo := hInv.2.2.2.2.2.2.2.2.2.2.1
        refine hInv.discoverChild hF_forest hvL_len hvL_nd hchIdxLt hchIdxEq hparQ hchIn hfE hdirSpec
          hDisj0.1 hF0.2.1 hscLo1 hscHi1 ?_ ?_ ?_ ⟨hvCh2, hfixCh2⟩ hz2 ?_
        · rw [hfr2 _ (by omega) (Or.inr (by omega))]
          dsimp only [mem1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
        · rw [hfr2 _ (by omega) (Or.inr (by omega))]
          dsimp only [mem1]
          rw [Function.update_of_ne (by omega), Function.update_self]
        · rw [hfr2 _ (by omega) (Or.inr (by omega))]
          dsimp only [mem1]; rw [Function.update_self]
        · intro a ha h1 h2 h3 hout
          rw [hfr2 a ha hout]
          dsimp only [mem1]
          rw [Function.update_of_ne h1, Function.update_of_ne h3, Function.update_of_ne h2]
      -- Extract the edgeStep run and recursive call run FIRST so the total cost bound T is fixed!
      obtain ⟨edgeBody, hpEdge, hEdgeRuns⟩ := hEdgeStep [mloc.metaBase, j, f, parent, child, dir, mloc.Lk, sc]
        mem1 pos ω (by wram_words) hPreEdge
      obtain ⟨oEdge, stEdge, cEdge, hEdgeCall, hPostEdge, hEdgeCost⟩ := hEdgeRuns
      set sc1 := oEdge.value
      have hInv1 := hInvNext sc1 stEdge.mem hPostEdge
      obtain ⟨sc', st', cRec, q', φcur', rootOf', hRecRun, hqle, hqtake, hInv', hCov', hRecCost⟩ :=
        ih (posIdx + 1) stEdge.mem stEdge.pos (q ++ [child]) qHead sc1
          (Function.update φcur child
            (if dir ≠ 0 then φcur parent + potGrad C g φ j f else φcur parent - potGrad C g φ j f))
          (Function.update rootOf child (rootOf parent))
          (by omega) (by omega) (List.mem_append_left _ hparQ) hInv1
      have hsc1W : sc1 < 2 ^ w := by
        have := hInv1.q_length_le
        have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) this
        have := hInv1.2.2.2.2.2.2.2.2.2.2.2.1
        omega
      have hsc'W : sc' < 2 ^ w := by
        have := hInv'.q_length_le
        have hmul := Nat.mul_le_mul_right (phiFillEdgeStepSpace j mloc.Lk) this
        have := hInv'.2.2.2.2.2.2.2.2.2.2.2.1
        omega
      have hqtMem : mem scratch0 = q.length := hInv.2.2.2.1
      have hqtMem1 : Function.update mem (scratch0 + 1 + chIdx) 1 scratch0 = q.length := by
        rw [Function.update_of_ne (by omega)]; exact hqtMem
      let T : ℕ := 180 + (phiFillEdgeStepCost j mloc.Lk + 60) + cRec
      obtain ⟨o, stFin, cost, hRun, ⟨rfl, hstFin⟩, hcostLe⟩ :=
        hbody1 0 T (fun o st => o = .returned sc' ∧ st.mem = st'.mem ∧ st.pos = st'.pos)
          (fun st1 hmem1 hpos1 hr0 hr1 hr2 hr3 hr5 hr6 hr7 hr8 hr9 hr11 hr12 hr16 hr18 hr19 hr20 => by
            rcases st1 with ⟨m1, regs1, p1⟩
            dsimp only at hmem1 hpos1 hr0 hr1 hr2 hr3 hr5 hr6 hr7 hr8 hr9 hr11 hr12 hr16 hr18 hr19 hr20
            subst m1; subst p1
            rw [ite_eq_right hchIn] at hr20
            refine runs_seq_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hr20, hw1]) ?_
              (fun hc => absurd hc (by decide))
            intro _
            -- Execute the 5-step unvisited branch as a flat sequence inside runs_seq_triple_le
            have hBranch : Runs w p ω
                (.store (.bin .add (.reg 5) (.reg 19)) (.const 1) ;;
                 .assign 21 (.load (.reg 7)) ;;
                 .store (.bin .add (.reg 6) (.reg 21)) (.reg 18) ;;
                 .store (.reg 7) (.bin .add (.reg 21) (.const 1)) ;;
                 .call 9 edgeStepProc [.reg 0, .reg 1, .reg 11, .reg 3, .reg 18, .reg 12, .reg 8, .reg 9])
                ⟨mem, regs1, pos⟩ .normal
                ⟨stEdge.mem, Function.update (Function.update regs1 21 q.length) 9 sc1, stEdge.pos⟩
                (31 + cEdge) := by
              have hs1 : Runs w p ω (.store (.bin .add (.reg 5) (.reg 19)) (.const 1))
                  ⟨mem, regs1, pos⟩ .normal
                  ⟨Function.update mem (scratch0 + 1 + chIdx) 1, regs1, pos⟩ 5 :=
                runs_store_iff.mpr ⟨scratch0 + 1 + chIdx, 1,
                  by simp [Expr.eval, BinOp.eval, hr5, hr19, hvisChAddrW],
                  by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
              have hs2 : Runs w p ω (.assign 21 (.load (.reg 7)))
                  ⟨Function.update mem (scratch0 + 1 + chIdx) 1, regs1, pos⟩ .normal
                  ⟨Function.update mem (scratch0 + 1 + chIdx) 1, Function.update regs1 21 q.length, pos⟩ 3 :=
                runs_assign_iff.mpr ⟨q.length,
                  Expr.eval_load_of_eq (by simp [Expr.eval, hr7]) hqtMem1, rfl, rfl, rfl⟩
              have hs3 : Runs w p ω (.store (.bin .add (.reg 6) (.reg 21)) (.reg 18))
                  ⟨Function.update mem (scratch0 + 1 + chIdx) 1, Function.update regs1 21 q.length, pos⟩ .normal
                  ⟨Function.update (Function.update mem (scratch0 + 1 + chIdx) 1)
                    (scratch0 + 1 + F.n + q.length) child,
                   Function.update regs1 21 q.length, pos⟩ 5 :=
                runs_store_iff.mpr ⟨scratch0 + 1 + F.n + q.length, child,
                  by simp [Expr.eval, BinOp.eval, hr6, hqSlotW],
                  by simp [Expr.eval, hr18], rfl, rfl, rfl⟩
              have hs4 : Runs w p ω (.store (.reg 7) (.bin .add (.reg 21) (.const 1)))
                  ⟨Function.update (Function.update mem (scratch0 + 1 + chIdx) 1)
                    (scratch0 + 1 + F.n + q.length) child,
                   Function.update regs1 21 q.length, pos⟩ .normal
                  ⟨mem1, Function.update regs1 21 q.length, pos⟩ 5 :=
                runs_store_iff.mpr ⟨scratch0, q.length + 1,
                  by simp [Expr.eval, hr7],
                  by simp [Expr.eval, BinOp.eval, hw1, hqLen1W], rfl, rfl, rfl⟩
              have hs5 : Runs w p ω
                  (.call 9 edgeStepProc [.reg 0, .reg 1, .reg 11, .reg 3, .reg 18, .reg 12, .reg 8, .reg 9])
                  ⟨mem1, Function.update regs1 21 q.length, pos⟩ .normal
                  ⟨stEdge.mem, Function.update (Function.update regs1 21 q.length) 9 sc1, stEdge.pos⟩
                  (8 + cEdge + 1) :=
                runs_call_iff.mpr ⟨[mloc.metaBase, j, f, parent, child, dir, mloc.Lk, sc],
                  edgeBody, oEdge, stEdge, cEdge,
                  by simp [evalArgs, Expr.eval, hr0, hr1, hr11, hr3, hr18, hr12, hr8, hr9],
                  hpEdge, hEdgeCall, rfl, rfl, by simp [argsSize, Expr.size]⟩
              have h45 := runs_seq_iff.mpr (Or.inr ⟨_, 5, 8 + cEdge + 1, hs4, hs5, rfl⟩)
              have h345 := runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hs3, h45, rfl⟩)
              have h2345 := runs_seq_iff.mpr (Or.inr ⟨_, 3, _, hs2, h345, rfl⟩)
              exact runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hs1, h2345, by omega⟩)
            -- Chain hBranch with recursive call + ret
            have hTailRun : ∃ o' stF' cTail,
                Runs w p ω
                  (.call 22 adjProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 16, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9] ;;
                   .ret (.reg 22))
                  ⟨stEdge.mem, Function.update (Function.update regs1 21 q.length) 9 sc1, stEdge.pos⟩
                  o' stF' cTail ∧
                (o' = .returned sc' ∧ stF'.mem = st'.mem ∧ stF'.pos = st'.pos) ∧
                0 + cTail ≤ 20 + cRec := by
              refine runs_seq_rec_call hpAdj
                (vs := [mloc.metaBase, j, mloc.fPtr j, parent, nextCur,
                  scratch0 + 1, scratch0 + 1 + F.n, scratch0, mloc.Lk, sc1])
                (by simp [evalArgs, Expr.eval, hr0, hr1, hr2, hr3, hr16, hr5, hr6, hr7, hr8])
                (by wram_words) hRecRun ?_
              refine WordRAM.runs_ret_le (v := sc') (by simp [Expr.eval]) ⟨rfl, rfl, rfl⟩ ?_
              simp only [argsSize, Expr.size]; omega
            obtain ⟨o', stF', cTail, hTail, hq', hc'⟩ := hTailRun
            exact ⟨o', stF', (31 + cEdge) + cTail + 1,
              runs_seq_iff.mpr (Or.inr ⟨_, 31 + cEdge, cTail, hBranch, hTail, rfl⟩), hq', by
                simp only [T, phiFillEdgeStepContract, List.getD_cons_zero, List.getD_cons_succ,
                  Expr.size] at hEdgeCost hc' ⊢
                omega⟩)
      have hqLen1 : (q ++ [child]).length = q.length + 1 := by simp
      have hqle' : q.length ≤ q'.length := by rw [hqLen1] at hqle; omega
      have hqtake' : q'.take q.length = q := by
        have h1 : (q'.take (q.length + 1)).take q.length = q'.take q.length := by
          rw [List.take_take, Nat.min_eq_left (Nat.le_succ _)]
        rw [← h1, ← hqLen1, hqtake, List.take_left]
      refine ⟨.returned sc', stFin, cost, hRun, sc', q', φcur', rootOf', rfl, hqle', hqtake',
        by rwa [hstFin.1], fun x hx => ?_, ?_⟩
      · rw [List.drop_eq_getElem_cons hposLt] at hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · have hchQ' : child ∈ q' := by
            have : child ∈ q ++ [child] := List.mem_append_right _ List.mem_cons_self
            rw [← hqtake] at this; exact List.mem_of_mem_take this
          rcases hdirSpec with ⟨hdnz, ht, _⟩ | ⟨hd0, hh, _⟩
          · exact ⟨fun h => absurd h hdnz, fun _ => ht.symm ▸ hchQ'⟩
          · exact ⟨fun _ => hh.symm ▸ hchQ', fun h => absurd hd0 h⟩
        · exact hCov' x hx'
      · rw [hqLen1] at hRecCost
        have hmul1 : (F.n - q.length) * (phiFillEdgeStepCost j mloc.Lk + 60) =
            (F.n - (q.length + 1)) * (phiFillEdgeStepCost j mloc.Lk + 60) +
              (phiFillEdgeStepCost j mloc.Lk + 60) := by
          conv_lhs => rw [show F.n - q.length = (F.n - (q.length + 1)) + 1 by omega]
          rw [Nat.add_mul, Nat.one_mul]
        have hmul2 : (rem' + 1) * 180 = rem' * 180 + 180 := by ring
        omega


end MinCostFlow.MinRatio

end
