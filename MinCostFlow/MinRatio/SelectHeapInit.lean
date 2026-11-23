module

public import MinCostFlow.MinRatio.SelectLevelBlocksSolver
public import MinCostFlow.MinRatio.SelectPhiFill
import WordRAM.Tactic

/-!
# Select-heap initialization, `φ`-fill loop, and `SolverSelectInv` region bridge (`SelectHeapInit`)

Provides the core building blocks for initializing the select region (`SelectRegion`,
`SelectLevelBlocks.lean`) and connecting it to `SolverSelectInv` (`SolverSelectState.lean`):
1. **`selectHeapInitBody`** (`[hb, cap, d, Lk, g0Ptr, metaPtr]`): writes the 14-word header of
   `SelectHeapLoc` on zeroed memory `[hb, ...)` in `O(1)` (`≤ 180`) steps, establishing
   `SelectHeapAt mem' loc 4 0`, `ZeroFrom mem' loc.endAddr`, and framing `< loc.hb`.
2. **`selectPhiLoopBody`** (`[meta, cur, d, Lk, scratch]`): loops `selectPhiFill` across levels
   `cur .. d`, advancing `SelectPhiPrefixAt` from `cur` to `d + 1` and producing frozen potentials
   `φ'` satisfying `SelectPotInvAt C g φ' j` for all `j ∈ [cur, d]` in
   `O(∑_{j=cur}^d (n_j + 1) * (j + 1) * Lk)` steps and space.
3. **`selectRegion_solverSelectInv`**: bridges a populated `SelectRegion sb loc B metaBase`
   (together with `SelectMetaTableAt`, `SelectBlocksAt`, `SelectHeapMatchesChain`,
   `SolverLevelCapsInv`, `SelectModelInv`, `SelectPotInv`, and the runtime heap-handle cell
   `mem (table + dMul * d + kOff) = loc.hb`) directly to `SolverSelectInv` with
   `sg.owned := fun a => sb ≤ a ∧ a < B.endAddr`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program SparseCore.Program

/-! ## 1. `selectHeapInitBody`: `O(1)` empty select-heap header initialization -/

/-- Initialize the 14-word header of `SelectHeapLoc` at `hb` on zeroed memory, returning `endAddr`.
Arguments: `[hb, cap, d, Lk, g0Ptr, metaPtr]` (`reg 0..5`). -/
def selectHeapInitBody : Stmt :=
  .assign 6 (.bin .add (.reg 0) (.const shHdrSize)) ;; -- arrPtr
  .assign 7 (.bin .add (.reg 6) (.reg 1)) ;; -- posPtr
  .assign 8 (.bin .add (.reg 7) (.reg 1)) ;; -- lvlPtr
  .assign 9 (.bin .add (.reg 8) (.reg 1)) ;; -- candHead
  .assign 10 (.bin .add (.reg 9) (.bin .add (.reg 2) (.const 1))) ;; -- candPrev
  .assign 11 (.bin .add (.reg 10) (.reg 1)) ;; -- candNext
  .assign 12 (.bin .add (.reg 11) (.reg 1)) ;; -- numBase
  .assign 13 (.bin .add (.reg 12) (.bin .mul (.reg 1) (.reg 3))) ;; -- denBase
  .assign 14 (.bin .add (.reg 13) (.bin .mul (.reg 1) (.reg 3))) ;; -- endAddr
  .store (.reg 0) (.const 0) ;; -- size = 0
  .store (.bin .add (.reg 0) (.const 1)) (.reg 1) ;; -- cap
  .store (.bin .add (.reg 0) (.const 2)) (.reg 2) ;; -- d
  .store (.bin .add (.reg 0) (.const 3)) (.reg 3) ;; -- Lk
  .store (.bin .add (.reg 0) (.const 4)) (.reg 6) ;; -- arrPtr
  .store (.bin .add (.reg 0) (.const 5)) (.reg 7) ;; -- posPtr
  .store (.bin .add (.reg 0) (.const 6)) (.reg 8) ;; -- lvlPtr
  .store (.bin .add (.reg 0) (.const 7)) (.reg 12) ;; -- numBase
  .store (.bin .add (.reg 0) (.const 8)) (.reg 13) ;; -- denBase
  .store (.bin .add (.reg 0) (.const 9)) (.reg 9) ;; -- candHead
  .store (.bin .add (.reg 0) (.const 10)) (.reg 10) ;; -- candPrev
  .store (.bin .add (.reg 0) (.const 11)) (.reg 11) ;; -- candNext
  .store (.bin .add (.reg 0) (.const 12)) (.reg 4) ;; -- g0Ptr
  .store (.bin .add (.reg 0) (.const 13)) (.reg 5) ;; -- metaPtr
  .ret (.reg 14)

theorem selectHeapInitBody_noRand : selectHeapInitBody.NoRand := by
  simp [selectHeapInitBody, Stmt.NoRand]

/-- Contract for `selectHeapInitBody` (`[hb, cap, d, Lk, g0Ptr, metaPtr]`): writes the 14-word
header on zeroed memory `[hb, ...)`, establishing `SelectHeapAt mem' loc 4 0` in `O(1)` steps. -/
def selectHeapInitContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ hb cap d Lk g0Ptr metaPtr,
      args = [hb, cap, d, Lk, g0Ptr, metaPtr] ∧
      16 < 2 ^ w ∧
      ZeroFrom mem hb ∧
      hb + selectHeapSize cap d Lk < 2 ^ w ∧
      g0Ptr < 2 ^ w ∧ metaPtr < 2 ^ w
  post args mem ret mem' :=
    let loc : SelectHeapLoc :=
      ⟨args.getD 0 0, args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0, args.getD 5 0⟩
    ret = loc.endAddr ∧
    SelectHeapAt mem' loc 4 0 ∧
    ZeroFrom mem' loc.endAddr ∧
    (∀ a < loc.hb, mem' a = mem a)
  cost _ _ := 240

/-! ## 2. `selectPhiLoopBody`: fill `φ_cur .. φ_d` via `selectPhiFill` -/

/-- Recursive loop calling `selectPhiFill` for levels `cur .. d`.
Arguments: `[meta, cur, d, Lk, scratch]` (`reg 0..4`). -/
def selectPhiLoopBody (self phiFillProc : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 2) (.reg 1))
    (.ret (.reg 4))
    (.call 5 phiFillProc [.reg 0, .reg 1, .reg 3, .reg 4] ;;
     .call 6 self [.reg 0, .bin .add (.reg 1) (.const 1), .reg 2, .reg 3, .reg 5] ;;
     .ret (.reg 6))

theorem selectPhiLoopBody_noRand (self phiFillProc : ℕ) :
    (selectPhiLoopBody self phiFillProc).NoRand := by
  simp [selectPhiLoopBody, Stmt.NoRand]

/-- Scratch space for `selectPhiLoopBody` over levels `cur .. C.d`. -/
def selectPhiLoopSpace (C : TreeChain) (cur Lk : ℕ) : ℕ :=
  (Finset.Icc cur C.d).sum fun j => selectPhiFillSpace j ((C.activeLSF j).F.F.n) Lk

/-- Step cost for `selectPhiLoopBody` over levels `cur .. C.d`. -/
def selectPhiLoopCost (C : TreeChain) (cur Lk : ℕ) : ℕ :=
  (Finset.Icc cur C.d).sum (fun j => selectPhiFillCost j ((C.activeLSF j).F.F.n) Lk + 40) + 20

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program SparseCore.Program

/-! ## 3. Verification of `selectHeapInitBody` -/

set_option maxHeartbeats 600000 in
/-- `selectHeapInitBody` meets `selectHeapInitContract`, establishing `SelectHeapAt mem' loc 4 0`
in `≤ 180` steps. -/
theorem selectHeapInit_meetsContract {w proc : ℕ} {p : Program}
    (hp : p.procs[proc]? = some selectHeapInitBody) :
    MeetsContract w p proc (selectHeapInitContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _hwords hpre
  obtain ⟨hb, cap, d, Lk, g0Ptr, metaPtr, rfl, hw16, hz, hroom, hg0W, hmetaW⟩ := hpre
  let loc : SelectHeapLoc := ⟨hb, cap, d, Lk, g0Ptr, metaPtr⟩
  have hend : loc.endAddr = hb + selectHeapSize cap d Lk := loc.endAddr_eq
  have hszDef : selectHeapSize cap d Lk = shHdrSize + (d + 1) + 5 * cap + 2 * (cap * Lk) := rfl
  have h14 : shHdrSize = 14 := rfl
  have hw1 : 1 < 2 ^ w := by omega
  have hArrW : loc.arrPtr < 2 ^ w := by dsimp only [loc, SelectHeapLoc.arrPtr, shHdrSize]; omega
  have hPosW : loc.posPtr < 2 ^ w := by
    dsimp only [loc, SelectHeapLoc.posPtr, SelectHeapLoc.arrPtr, shHdrSize]; omega
  have hLvlW : loc.lvlPtr < 2 ^ w := by
    dsimp only [loc, SelectHeapLoc.lvlPtr, SelectHeapLoc.posPtr, SelectHeapLoc.arrPtr, shHdrSize]; omega
  have hChW : loc.candHead < 2 ^ w := by
    dsimp only [loc, SelectHeapLoc.candHead, SelectHeapLoc.lvlPtr, SelectHeapLoc.posPtr, SelectHeapLoc.arrPtr, shHdrSize]; omega
  have hCpW : loc.candPrev < 2 ^ w := by
    dsimp only [loc, SelectHeapLoc.candPrev, SelectHeapLoc.candHead, SelectHeapLoc.lvlPtr, SelectHeapLoc.posPtr, SelectHeapLoc.arrPtr, shHdrSize]; omega
  have hCnW : loc.candNext < 2 ^ w := by
    dsimp only [loc, SelectHeapLoc.candNext, SelectHeapLoc.candPrev, SelectHeapLoc.candHead, SelectHeapLoc.lvlPtr, SelectHeapLoc.posPtr, SelectHeapLoc.arrPtr, shHdrSize]; omega
  have hNumW : loc.numBase < 2 ^ w := by
    dsimp only [loc, SelectHeapLoc.numBase, SelectHeapLoc.candNext, SelectHeapLoc.candPrev, SelectHeapLoc.candHead, SelectHeapLoc.lvlPtr, SelectHeapLoc.posPtr, SelectHeapLoc.arrPtr, shHdrSize]; omega
  have hDenW : loc.denBase < 2 ^ w := by
    dsimp only [loc, SelectHeapLoc.denBase, SelectHeapLoc.numBase, SelectHeapLoc.candNext, SelectHeapLoc.candPrev, SelectHeapLoc.candHead, SelectHeapLoc.lvlPtr, SelectHeapLoc.posPtr, SelectHeapLoc.arrPtr, shHdrSize]; omega
  have hEndW : loc.endAddr < 2 ^ w := by omega
  have hCapLkW : cap * Lk < 2 ^ w := by omega
  apply runs_start_le
  dsimp only [startState]
  unfold selectHeapInitBody
  refine runs_seq_assign_flat (v := loc.arrPtr)
    (by simp [Expr.eval, BinOp.eval, show shHdrSize < 2 ^ w by omega,
          show hb + shHdrSize = loc.arrPtr from rfl, hArrW]) ?_
  refine runs_seq_assign_flat (v := loc.posPtr)
    (by simp [Expr.eval, BinOp.eval, show loc.arrPtr + cap = loc.posPtr from rfl, hPosW]) ?_
  refine runs_seq_assign_flat (v := loc.lvlPtr)
    (by simp [Expr.eval, BinOp.eval, show loc.posPtr + cap = loc.lvlPtr from rfl, hLvlW]) ?_
  refine runs_seq_assign_flat (v := loc.candHead)
    (by simp [Expr.eval, BinOp.eval, show loc.lvlPtr + cap = loc.candHead from rfl, hChW]) ?_
  refine runs_seq_assign_flat (v := loc.candPrev)
    (by simp [Expr.eval, BinOp.eval, hw1, show d + 1 < 2 ^ w by omega,
          show loc.candHead + (d + 1) = loc.candPrev from rfl, hCpW]) ?_
  refine runs_seq_assign_flat (v := loc.candNext)
    (by simp [Expr.eval, BinOp.eval, show loc.candPrev + cap = loc.candNext from rfl, hCnW]) ?_
  refine runs_seq_assign_flat (v := loc.numBase)
    (by simp [Expr.eval, BinOp.eval, show loc.candNext + cap = loc.numBase from rfl, hNumW]) ?_
  refine runs_seq_assign_flat (v := loc.denBase)
    (by simp [Expr.eval, BinOp.eval, hCapLkW, show loc.numBase + cap * Lk = loc.denBase from rfl, hDenW]) ?_
  refine runs_seq_assign_flat (v := loc.endAddr)
    (by simp [Expr.eval, BinOp.eval, hCapLkW, show loc.denBase + cap * Lk = loc.endAddr from rfl, hEndW]) ?_
  refine runs_seq_store_flat (x := hb) (v := 0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 1) (v := cap) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 2) (v := d) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 3) (v := Lk) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 4) (v := loc.arrPtr) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 5) (v := loc.posPtr) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 6) (v := loc.lvlPtr) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 7) (v := loc.numBase) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 8) (v := loc.denBase) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 9) (v := loc.candHead) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 10) (v := loc.candPrev) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 11) (v := loc.candNext) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 12) (v := g0Ptr) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_flat (x := hb + 13) (v := metaPtr) (by eval_expr) (by eval_expr) ?_
  refine WordRAM.runs_ret_le (v := loc.endAddr) (by eval_expr) ?_ ?_
  · dsimp only [selectHeapInitContract]
    simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
    set memF := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update mem hb 0) (hb + 1) cap) (hb + 2) d) (hb + 3) Lk)
      (hb + 4) loc.arrPtr) (hb + 5) loc.posPtr) (hb + 6) loc.lvlPtr) (hb + 7) loc.numBase)
      (hb + 8) loc.denBase) (hb + 9) loc.candHead) (hb + 10) loc.candPrev) (hb + 11) loc.candNext)
      (hb + 12) g0Ptr) (hb + 13) metaPtr
    have hout : ∀ a, (a < hb ∨ hb + 14 ≤ a) → memF a = mem a := fun a ha => by
      dsimp only [memF]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hzeroAbove : ∀ a, hb + 14 ≤ a → memF a = 0 := fun a ha =>
      (hout a (Or.inr ha)).trans (hz a (by omega))
    have hpos0 : ∀ e < cap, memF (loc.posPtr + e) = 0 := fun e _ =>
      hzeroAbove _ (by dsimp only [loc, SelectHeapLoc.posPtr, SelectHeapLoc.arrPtr, shHdrSize]; omega)
    refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, fun a ha => hzeroAbove a (by change loc.endAddr ≤ a at ha; omega),
      fun a ha => hout a (Or.inl ha)⟩
    · intro idx hidx
      simp only [List.length_cons, List.length_nil] at hidx
      have : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 ∨ idx = 4 ∨ idx = 5 ∨ idx = 6 ∨
          idx = 7 ∨ idx = 8 ∨ idx = 9 ∨ idx = 10 ∨ idx = 11 ∨ idx = 12 ∨ idx = 13 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        dsimp only [memF, loc, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero]
        repeat (first | exact Function.update_self .. | rw [Function.update_of_ne (by omega)])
    · exact ⟨Nat.zero_le _, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ h => absurd h (Nat.not_lt_zero _), fun e he => Or.inl (hpos0 e he)⟩
    · intro e he hnz
      exact absurd (hpos0 e he) hnz
    · intro _ _ hlt
      exact absurd hlt (Nat.not_lt_zero _)
    · refine ⟨fun _ => [], fun i _ => ⟨⟨List.nodup_nil, fun _ h => (by cases h), ?_,
        fun _ h => (by simp at h)⟩,
        fun e => ⟨fun h => (by cases h), fun ⟨he, hnz, _⟩ => absurd (hpos0 e he) hnz⟩⟩⟩
      exact hzeroAbove _ (by
        dsimp only [loc, SelectHeapLoc.candHead, SelectHeapLoc.lvlPtr, SelectHeapLoc.posPtr,
          SelectHeapLoc.arrPtr, shHdrSize]; omega)
  · change _ ≤ 240; decide

/-! ## 4. Verification of `selectPhiLoopBody` -/

private theorem selectPhiPrefixBelow_mono {mloc : SelectLevelMetaLoc} {j hi₁ hi₂ : ℕ}
    (h : SelectPhiPrefixBelow mloc j hi₁) (hle : hi₁ ≤ hi₂) :
    SelectPhiPrefixBelow mloc j hi₂ :=
  ⟨le_trans h.1 hle, le_trans h.2.1 hle,
    fun k hk => ⟨le_trans (h.2.2 k hk).1 hle, le_trans (h.2.2 k hk).2 hle⟩⟩

private theorem selectPhiTargetDisjoint_mono {mloc : SelectLevelMetaLoc} {j hi₁ hi₂ : ℕ}
    (h : SelectPhiTargetDisjoint mloc j hi₁) (hle : hi₁ ≤ hi₂) :
    SelectPhiTargetDisjoint mloc j hi₂ :=
  ⟨le_trans h.1 hle, le_trans h.2.1 hle, h.2.2⟩

/-- `selectPhiLoopBody` fills `φ_cur .. φ_d` via `selectPhiFill`, advancing `SelectPhiPrefixAt`
from `cur` to `C.d + 1` and establishing `SelectPotInvAt C g φ' j` for all `j ∈ [cur, C.d]`. -/
theorem selectPhiLoop_runs {w P self phiFillProc : ℕ}
    {mloc : SelectLevelMetaLoc} {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {p : Program} {ω : ℕ → Bool}
    {PhiBd : (ℕ → ℕ → ℝ) → ℕ → Prop}
    (hpLoop : p.procs[self]? = some (selectPhiLoopBody self phiFillProc))
    (hFill : ∀ φ : ℕ → ℕ → ℝ,
      MeetsContract w p phiFillProc (selectPhiFillContract w 4 P mloc C G g ℓ σ σ_mwu γ_ℓ γ_c φ))
    (hw16 : 16 < 2 ^ w) (hw10 : 10 ≤ w)
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (he0Cap : ∀ e ∈ (C.G 0).E, e < mloc.eCap 0)
    (hPhiBdStep : ∀ j ≤ C.d, ∀ (φ : ℕ → ℕ → ℝ) (φj : ℕ → ℝ),
      (∀ k < j, SelectPotInvAt C g φ k) →
      (∀ k < j, PhiBd φ k) →
      (∀ v ∈ (C.activeLSF j).F.F.V, ∃ r ∈ (C.activeLSF j).F.F.V,
        (C.activeLSF j).F.F.Connected v r ∧
        φj v = walkInner (potGrad C g φ j) ((C.activeLSF j).F.F.forestPath v r)) →
      ∀ k < j + 1, PhiBd (Function.update φ j φj) k)
    (hFit : ∀ j ≤ C.d, ∀ φ' : ℕ → ℕ → ℝ,
      (∀ k < j, SelectPotInvAt C g φ' k) →
      (∀ k < j, PhiBd φ' k) →
      (∀ e ∈ (C.activeLSF j).F.F.E, PotGradEvalFits 4 mloc.Lk P C g φ' j e) ∧
      ForestWalkFits 4 mloc.Lk P (C.activeLSF j).F.F (potGrad C g φ' j)) :
    ∀ (rem cur scratch pos : ℕ) (mem : ℕ → ℕ) (φ : ℕ → ℕ → ℝ),
      C.d + 1 - cur = rem →
      mloc.metaBase < 2 ^ w → cur < 2 ^ w → C.d < 2 ^ w → mloc.Lk < 2 ^ w →
      SelectPhiPrefixAt mem mloc 4 P C g φ cur →
      (∀ k < cur, SelectPotInvAt C g φ k) →
      (∀ k < cur, PhiBd φ k) →
      (∀ j, cur ≤ j → j ≤ C.d →
        mem (smEntryAddr mloc.metaBase mloc.d 0 j) = mloc.GPtr j ∧
        mem (smEntryAddr mloc.metaBase mloc.d 1 j) = mloc.vCap j ∧
        mem (smEntryAddr mloc.metaBase mloc.d 2 j) = mloc.eCap j ∧
        mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
        mem (smEntryAddr mloc.metaBase mloc.d 6 j) = mloc.fPtr j ∧
        DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C.G j) ∧
        DynGraphAt mem (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) (C.activeLSF j).F.F) →
      (∀ j, cur ≤ j → j ≤ C.d →
        SelectPhiPrefixBelow mloc j scratch ∧
        SelectPhiTargetDisjoint mloc j scratch ∧
        mloc.GPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ scratch ∧
        (∀ j', j ≤ j' → j' ≤ C.d →
          mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.GPtr j' ∨
            mloc.GPtr j' + dynGraphSize (mloc.vCap j') (mloc.eCap j') ≤ mloc.phiPtr j) ∧
        (∀ j', j < j' → j' ≤ C.d →
          mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.fPtr j' ∨
            mloc.fPtr j' + dynGraphSize (mloc.vCap j') (mloc.eCap j') ≤ mloc.phiPtr j)) →
      ZeroFrom mem scratch →
      scratch + selectPhiLoopSpace C cur mloc.Lk < 2 ^ w →
      ∃ sc' cost out φ',
        Runs w p ω (selectPhiLoopBody self phiFillProc)
          (startState [mloc.metaBase, cur, C.d, mloc.Lk, scratch] mem pos) (.returned sc') out cost ∧
        scratch ≤ sc' ∧ sc' ≤ scratch + selectPhiLoopSpace C cur mloc.Lk ∧
        ZeroFrom out.mem sc' ∧
        (∀ k < cur, φ' k = φ k) ∧
        SelectPhiPrefixAt out.mem mloc 4 P C g φ' (C.d + 1) ∧
        (∀ j ≤ C.d, SelectPotInvAt C g φ' j) ∧
        (∀ j ≤ C.d, PhiBd φ' j) ∧
        (∀ a < scratch,
          (∀ j, cur ≤ j → j ≤ C.d →
            a < mloc.phiPtr j ∨ mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ a) →
          out.mem a = mem a) ∧
        cost ≤ selectPhiLoopCost C cur mloc.Lk := by
  intro rem
  induction rem with
  | zero =>
    intro cur scratch pos mem φ hrem hmetaW hcurW hdW hLkW hpref hpot hbd _ _ hz hroom
    have hgt : C.d < cur := by omega
    have hIcc : Finset.Icc cur C.d = ∅ := Finset.Icc_eq_empty (by omega)
    have hprefFull : SelectPhiPrefixAt mem mloc 4 P C g φ (C.d + 1) := by
      refine ⟨hpref.1, hpref.2.1, hpref.2.2.1, hpref.2.2.2.1, fun k hk => hpref.2.2.2.2 k (by omega)⟩
    have hrun : Runs w p ω (selectPhiLoopBody self phiFillProc)
        (startState [mloc.metaBase, cur, C.d, mloc.Lk, scratch] mem pos)
        (.returned scratch) (startState [mloc.metaBase, cur, C.d, mloc.Lk, scratch] mem pos) 6 := by
      unfold selectPhiLoopBody
      refine runs_cond_iff.mpr ⟨1, 2,
        by simp [Expr.eval, BinOp.eval, startState, hgt, show 1 < 2 ^ w by omega],
        runs_ret_iff.mpr ⟨scratch, by simp [Expr.eval, startState], rfl, rfl, rfl⟩, rfl⟩
    refine ⟨scratch, 6, _, φ, hrun, le_rfl, Nat.le_add_right _ _, hz, fun _ _ => rfl,
      hprefFull, fun j hj => hpot j (by omega), fun j hj => hbd j (by omega), fun _ _ _ => rfl, ?_⟩
    simp only [selectPhiLoopCost, hIcc, Finset.sum_empty]; omega
  | succ rem ih =>
    intro cur scratch pos mem φ hrem hmetaW hcurW hdW hLkW hpref hpot hbd hlevels hdisj hz hroom
    have hcurLe : cur ≤ C.d := by omega
    have hIccSplit : Finset.Icc cur C.d = insert cur (Finset.Icc (cur + 1) C.d) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hNotMem : cur ∉ Finset.Icc (cur + 1) C.d := by simp
    have hSpSplit : selectPhiLoopSpace C cur mloc.Lk =
        selectPhiFillSpace cur ((C.activeLSF cur).F.F.n) mloc.Lk +
          selectPhiLoopSpace C (cur + 1) mloc.Lk := by
      unfold selectPhiLoopSpace; rw [hIccSplit, Finset.sum_insert hNotMem]
    have hCostSplit : selectPhiLoopCost C cur mloc.Lk =
        selectPhiFillCost cur ((C.activeLSF cur).F.F.n) mloc.Lk + 40 +
          selectPhiLoopCost C (cur + 1) mloc.Lk := by
      unfold selectPhiLoopCost; rw [hIccSplit, Finset.sum_insert hNotMem]; omega
    obtain ⟨hG0, hV0, hE0, hPhi0, hF0, hGDG, hFDG⟩ := hlevels cur le_rfl hcurLe
    obtain ⟨hBel0, hTgt0, hG0Hi, hGDisj0, hFDisj0⟩ := hdisj cur le_rfl hcurLe
    have hFit0 := hFit cur hcurLe φ hpot hbd
    -- Step 1: call `selectPhiFill` at level `cur`
    obtain ⟨bFill, hbFill, oFill, stFill, cFill, hrFill, hpFill, hcFill⟩ :=
      hFill φ [mloc.metaBase, cur, mloc.Lk, scratch] mem pos ω
        (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> omega)
        ⟨cur, scratch, rfl, hw16, by decide, by omega, hH, hcurLe, he0Cap,
          hPhi0, hF0, hFDG, hpref, hBel0, hTgt0, hFit0.1, hFit0.2, hz, by omega⟩
    obtain ⟨hsc1Lo, hsc1Hi, hz1, hfr1, φj, hPhiAt1, _hDiff1, hPotAt1, hFillAt1⟩ := hpFill
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hsc1Lo hsc1Hi hfr1 hPhiAt1 hPotAt1 hFillAt1
    set sc1 := oFill.value
    set φ1 := Function.update φ cur φj
    have hbd1 : ∀ k < cur + 1, PhiBd φ1 k :=
      hPhiBdStep cur hcurLe φ φj hpot hbd hFillAt1
    have hfr1Meta : ∀ a, mloc.metaBase ≤ a → a < mloc.metaBase + selectLevelMetaSize mloc.d →
        stFill.mem a = mem a := fun a h1 h2 => by
      apply hfr1 a (lt_of_lt_of_le h2 hBel0.1)
      rcases hTgt0.2.2.1 with h | h <;> [left; right] <;> omega
    have hEntLt : ∀ blk ≤ 6, ∀ j ≤ C.d,
        smEntryAddr mloc.metaBase mloc.d blk j < mloc.metaBase + selectLevelMetaSize mloc.d := by
      intro blk hblk j hj
      have hm := Nat.mul_le_mul_right (mloc.d + 1) hblk
      have hjd : j ≤ mloc.d := by rw [hpref.1]; exact hj
      unfold smEntryAddr smTableOff selectLevelMetaSize; omega
    have hpref1 : SelectPhiPrefixAt stFill.mem mloc 4 P C g φ1 (cur + 1) := by
      have hKeep := hpref.of_agree_outside_target hBel0 hTgt0 (by omega) he0Cap hfr1
      refine ⟨hKeep.1, hKeep.2.1, hKeep.2.2.1, hKeep.2.2.2.1, fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
      · obtain ⟨a0, a1, a2, a3, aG, aP⟩ := hKeep.2.2.2.2 k hlt
        refine ⟨a0, a1, a2, a3, aG, ?_⟩
        dsimp only [φ1]; rw [Function.update_of_ne (by omega)]; exact aP
      · rw [heq]
        have hG1 : DynGraphAt stFill.mem (mloc.GPtr cur) (mloc.vCap cur) (mloc.eCap cur) (C.G cur) :=
          DynGraphAt.of_agree hGDG fun a h1 h2 => hfr1 a (lt_of_lt_of_le h2 hG0Hi) (by
            rcases hGDisj0 cur le_rfl hcurLe with h | h <;> [right; left] <;> omega)
        refine ⟨(hfr1Meta _ (by unfold smEntryAddr smTableOff; omega) (hEntLt 0 (by omega) cur hcurLe)).trans hG0,
          (hfr1Meta _ (by unfold smEntryAddr smTableOff; omega) (hEntLt 1 (by omega) cur hcurLe)).trans hV0,
          (hfr1Meta _ (by unfold smEntryAddr smTableOff; omega) (hEntLt 2 (by omega) cur hcurLe)).trans hE0,
          (hfr1Meta _ (by unfold smEntryAddr smTableOff; omega) (hEntLt 3 (by omega) cur hcurLe)).trans hPhi0,
          hG1, by dsimp only [φ1]; rw [Function.update_self]; exact hPhiAt1⟩
    have hpot1 : ∀ k < cur + 1, SelectPotInvAt C g φ1 k := fun k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact (selectPotInvAt_update_of_lt C g φ φj hlt).mpr (hpot k hlt)
      · exact hPotAt1
    have hlevels1 : ∀ j, cur + 1 ≤ j → j ≤ C.d →
        stFill.mem (smEntryAddr mloc.metaBase mloc.d 0 j) = mloc.GPtr j ∧
        stFill.mem (smEntryAddr mloc.metaBase mloc.d 1 j) = mloc.vCap j ∧
        stFill.mem (smEntryAddr mloc.metaBase mloc.d 2 j) = mloc.eCap j ∧
        stFill.mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
        stFill.mem (smEntryAddr mloc.metaBase mloc.d 6 j) = mloc.fPtr j ∧
        DynGraphAt stFill.mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C.G j) ∧
        DynGraphAt stFill.mem (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) (C.activeLSF j).F.F := by
      intro j hj1 hj2
      obtain ⟨b0, b1, b2, b3, b6, bG, bF⟩ := hlevels j (by omega) hj2
      obtain ⟨_, bTgt, bGHi, _, _⟩ := hdisj j (by omega) hj2
      refine ⟨(hfr1Meta _ (by unfold smEntryAddr smTableOff; omega) (hEntLt 0 (by omega) j hj2)).trans b0,
        (hfr1Meta _ (by unfold smEntryAddr smTableOff; omega) (hEntLt 1 (by omega) j hj2)).trans b1,
        (hfr1Meta _ (by unfold smEntryAddr smTableOff; omega) (hEntLt 2 (by omega) j hj2)).trans b2,
        (hfr1Meta _ (by unfold smEntryAddr smTableOff; omega) (hEntLt 3 (by omega) j hj2)).trans b3,
        (hfr1Meta _ (by unfold smEntryAddr smTableOff; omega) (hEntLt 6 (by omega) j hj2)).trans b6,
        DynGraphAt.of_agree bG fun a h1 h2 => hfr1 a (lt_of_lt_of_le h2 bGHi) (by
          rcases hGDisj0 j (by omega) hj2 with h | h <;> [right; left] <;> omega),
        DynGraphAt.of_agree bF fun a h1 h2 => hfr1 a (lt_of_lt_of_le h2 bTgt.2.1) (by
          rcases hFDisj0 j (by omega) hj2 with h | h <;> [right; left] <;> omega)⟩
    have hdisj1 : ∀ j, cur + 1 ≤ j → j ≤ C.d →
        SelectPhiPrefixBelow mloc j sc1 ∧ SelectPhiTargetDisjoint mloc j sc1 ∧
        mloc.GPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ sc1 ∧
        (∀ j', j ≤ j' → j' ≤ C.d →
          mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.GPtr j' ∨
            mloc.GPtr j' + dynGraphSize (mloc.vCap j') (mloc.eCap j') ≤ mloc.phiPtr j) ∧
        (∀ j', j < j' → j' ≤ C.d →
          mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ mloc.fPtr j' ∨
            mloc.fPtr j' + dynGraphSize (mloc.vCap j') (mloc.eCap j') ≤ mloc.phiPtr j) := by
      intro j hj1 hj2
      obtain ⟨d1, d2, d3, d4, d5⟩ := hdisj j (by omega) hj2
      exact ⟨selectPhiPrefixBelow_mono d1 hsc1Lo, selectPhiTargetDisjoint_mono d2 hsc1Lo,
        le_trans d3 hsc1Lo, d4, d5⟩
    have hcur1W : cur + 1 < 2 ^ w := by
      have hmb := hBel0.1
      rw [show selectLevelMetaSize mloc.d = 2 + 8 * (mloc.d + 1) from rfl, hpref.1] at hmb
      omega
    -- Step 2: recursive call at `cur + 1`
    obtain ⟨sc2, cRec, stRec, φ2, hrRec, hsc2Lo, hsc2Hi, hz2, hφKeep, hpref2, hpot2, hbd2, hfr2, hcRec⟩ :=
      ih (cur + 1) sc1 stFill.pos stFill.mem φ1 (by omega) hmetaW hcur1W hdW hLkW
        hpref1 hpot1 hbd1 hlevels1 hdisj1 hz1 (by omega)
    -- Stitch the two calls into `selectPhiLoopBody`
    let s0 := startState [mloc.metaBase, cur, C.d, mloc.Lk, scratch] mem pos
    let rg5 := Function.update s0.regs 5 sc1
    let rg6 := Function.update rg5 6 sc2
    have r1 : Runs w p ω (.call 5 phiFillProc [.reg 0, .reg 1, .reg 3, .reg 4])
        s0 .normal ⟨stFill.mem, rg5, stFill.pos⟩ (cFill + 5) :=
      runs_call_iff.mpr ⟨[mloc.metaBase, cur, mloc.Lk, scratch], bFill, oFill, stFill, cFill,
        by simp [evalArgs, Expr.eval, s0, startState], hbFill, hrFill, rfl, rfl,
        by simp [argsSize, Expr.size]; omega⟩
    have r2 : Runs w p ω
        (.call 6 self [.reg 0, .bin .add (.reg 1) (.const 1), .reg 2, .reg 3, .reg 5])
        ⟨stFill.mem, rg5, stFill.pos⟩ .normal ⟨stRec.mem, rg6, stRec.pos⟩ (cRec + 8) :=
      runs_call_iff.mpr ⟨[mloc.metaBase, cur + 1, C.d, mloc.Lk, sc1],
        selectPhiLoopBody self phiFillProc, .returned sc2, stRec, cRec,
        by simp [evalArgs, Expr.eval, BinOp.eval, rg5, s0, startState, show 1 < 2 ^ w by omega, hcur1W],
        hpLoop, hrRec, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have r3 : Runs w p ω (.ret (.reg 6))
        ⟨stRec.mem, rg6, stRec.pos⟩ (.returned sc2) ⟨stRec.mem, rg6, stRec.pos⟩ 2 :=
      runs_ret_iff.mpr ⟨sc2, by simp [Expr.eval, rg6], rfl, rfl, rfl⟩
    have rFull : Runs w p ω (selectPhiLoopBody self phiFillProc) s0 (.returned sc2)
        ⟨stRec.mem, rg6, stRec.pos⟩ (4 + ((cFill + 5) + ((cRec + 8) + 2 + 1) + 1)) := by
      unfold selectPhiLoopBody
      refine runs_cond_iff.mpr ⟨0, _,
        by simp [Expr.eval, BinOp.eval, s0, startState, show ¬ C.d < cur by omega, show 0 < 2 ^ w by omega],
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, r1, runs_seq_iff.mpr (Or.inr ⟨_, _, _, r2, r3, rfl⟩), rfl⟩),
        by simp [Expr.size]; omega⟩
    refine ⟨sc2, _, ⟨stRec.mem, rg6, stRec.pos⟩, φ2, rFull, by omega, by omega, hz2,
      fun k hk => (hφKeep k (by omega)).trans (by dsimp only [φ1]; rw [Function.update_of_ne (by omega)]),
      hpref2, hpot2, hbd2, fun a ha hout => ?_, ?_⟩
    · exact (hfr2 a (by omega) fun j hj1 hj2 => hout j (by omega) hj2).trans
        (hfr1 a ha (hout cur le_rfl hcurLe))
    · simp only [selectPhiFillContract, List.getD_cons_zero, List.getD_cons_succ] at hcFill
      omega

/-! ## 5. Region bridge to `SolverSelectInv` -/

private theorem blk_le_end {B : SelectBlocksLoc} {j : ℕ} (hj : j ≤ B.d) :
    B.base ≤ B.fPtr j ∧ B.fPtr j + B.levelSize ≤ B.endAddr := by
  have h1 : B.base ≤ B.fPtr j := by unfold SelectBlocksLoc.fPtr; omega
  have h2 : j * B.levelSize + B.levelSize ≤ (B.d + 1) * B.levelSize := by
    have := Nat.mul_le_mul_right B.levelSize (Nat.succ_le_succ hj)
    rwa [Nat.succ_mul] at this
  have h3 : B.lastGPtr ≤ B.endAddr := by
    unfold SelectBlocksLoc.endAddr SelectBlocksLoc.g0Ptr; omega
  unfold SelectBlocksLoc.fPtr SelectBlocksLoc.lastGPtr at *
  exact ⟨h1, by omega⟩

/-- **Bridge from `SelectRegion` to `SolverSelectInv`.** A populated select region `[sb, B.endAddr)`
above `foot`, together with `SelectMetaTableAt`, `SelectBlocksAt`, `SelectHeapMatchesChain`,
`SolverLevelCapsInv` (with every interior level graph lying in `foot`), `SelectModelInv`,
`SelectPotInv`, and the runtime heap-handle cell `mem (table + dMul * d + kOff) = loc.hb`,
establishes `SolverSelectInv` with `sg.owned := fun a => sb ≤ a ∧ a < B.endAddr`. -/
theorem selectRegion_solverSelectInv
    {cfg : Alg2Config} {L P V m vCap eCap dMul kOff sb metaBase pLast size : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {G : MGraph} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {foot metaFoot : ℕ → Prop} {mem : ℕ → ℕ}
    {loc : SelectHeapLoc} {B : SelectBlocksLoc}
    {G₀ : MGraph} {σ σ_mwu γ_ℓ γ_c : ℝ} {φ : ℕ → ℕ → ℝ}
    (hreg : SelectRegion sb loc B metaBase)
    (hcap : loc.cap = selectHeapCap cfg G m)
    (hBd : B.d = cfg.P.d) (hBv : B.vCap = vCap) (hBe : B.eCap = eCap) (hBLk : B.Lk = L)
    (hFootDisj : ∀ a, sb ≤ a → a < B.endAddr → ¬ foot a)
    (hhbRd : mem (tok.table + dMul * cfg.P.d + kOff) = loc.hb)
    (hhbOwn : metaFoot (tok.table + dMul * cfg.P.d + kOff) ∨
      (sb ≤ tok.table + dMul * cfg.P.d + kOff ∧ tok.table + dMul * cfg.P.d + kOff < B.endAddr))
    (hLvlGFoot : ∀ j < cfg.P.d,
      ∀ a, solverLevelG tok mem j ≤ a → a < solverLevelG tok mem j + dynGraphSize vCap eCap → metaFoot a)
    (hLvlGPtrFoot : ∀ j < cfg.P.d, metaFoot (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j))
    (htab : SelectMetaTableAt mem (selectMlocOf B metaBase (solverLevelG tok mem) pLast))
    (hblk : SelectBlocksAt mem B P model.chain.toTreeChain model.chain.g model.chain.ℓ φ pLast)
    (hmatch : SelectHeapMatchesChain mem loc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ size)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hmod : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hPot : SelectPotInv model.chain.toTreeChain model.chain.g φ) :
    let mloc := selectMlocOf B metaBase (solverLevelG tok mem) pLast
    let sg : SelectGhost :=
      { loc := loc
        mloc := mloc
        size := size
        φ := φ
        coreLen := fun j => model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1)
        owned := fun a => sb ≤ a ∧ a < B.endAddr
        reembPot := 0 }
    SolverSelectInv G L P m dMul kOff tok.table model foot metaFoot sg mem := by
  intro mloc sg
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hreg
  have hsbLeEnd : sb ≤ loc.endAddr := by rw [loc.endAddr_eq, h1]; omega
  have hMetaEnd : metaBase + selectLevelMetaSize cfg.P.d ≤ B.endAddr := by
    have hlo : B.base ≤ B.endAddr := by
      rw [B.endAddr_eq]; omega
    rw [← hBd]; omega
  have hHeapEnd : loc.endAddr ≤ B.endAddr := by
    have : B.base ≤ B.endAddr := by rw [B.endAddr_eq]; omega
    omega
  refine ⟨fun mem' hag => ?_, fun a ha => hFootDisj a ha.1 ha.2,
    ⟨G₀, σ, σ_mwu, γ_ℓ, γ_c, hmod⟩⟩
  have hOwnAg : ∀ a, sb ≤ a → a < B.endAddr → mem' a = mem a := fun a hlo hhi =>
    hag a (Or.inr ⟨hlo, hhi⟩)
  have hGPtrEq : ∀ j < cfg.P.d, solverLevelG tok mem' j = solverLevelG tok mem j := fun j hj =>
    hag _ (Or.inl (hLvlGPtrFoot j hj))
  have htab' : SelectMetaTableAt mem' mloc :=
    htab.of_agree fun a ha1 ha2 => by
      dsimp only [mloc, selectMlocOf] at ha1 ha2
      exact hOwnAg a (by omega) (by rw [← hBd] at hMetaEnd; omega)
  have hblk' : SelectBlocksAt mem' B P model.chain.toTreeChain model.chain.g model.chain.ℓ φ pLast :=
    hblk.of_agree fun a ha1 ha2 => hOwnAg a (by omega) ha2
  have hmatch' : SelectHeapMatchesChain mem' loc 4 P model.chain.toTreeChain model.chain.g
      model.chain.ℓ size :=
    hmatch.of_agree fun a ha1 ha2 => hOwnAg a (by omega) (lt_of_lt_of_le ha2 hHeapEnd)
  have hmeta' : SelectLevelMetaAt mem' mloc 4 P model.chain.toTreeChain model.chain.g model.chain.ℓ
      φ (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ (j + 1)) := by
    have hd : model.chain.toTreeChain.d = B.d := by rw [hBd]; rfl
    refine selectLevelMetaAt_of_blocks hd htab' (fun j hj => ?_) (fun j hj => ?_) hblk' hPot
    · rw [hBd] at hj
      have hG := (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 j hj).1
      rw [hBv, hBe]
      exact DynGraphAt.of_agree hG fun a hlo hhi => hag a (Or.inl (hLvlGFoot j hj a hlo hhi))
    · rw [hBd] at hj
      exact hmod.activeS_eq_G_succ j hj
  dsimp only [SelectStateAt, sg, mloc, selectMlocOf]
  refine ⟨hcap, by omega, by omega, h3, h7.symm, hBLk,
    (hag _ hhbOwn).trans hhbRd, hhbOwn,
    fun a ha1 ha2 => ⟨by omega, lt_of_lt_of_le ha2 hHeapEnd⟩,
    fun a ha1 ha2 => ⟨by omega, by omega⟩,
    fun i hi => ?_, hmatch', hmeta'⟩
  have hiB : i < B.d := by omega
  have hblkI := blk_le_end (B := B) (Nat.le_of_lt hiB)
  have hembBounds : B.fPtr i ≤ B.embPtr i ∧ B.embPtr i + B.eCap + B.eCap * B.slot ≤ B.fPtr i + B.levelSize := by
    unfold SelectBlocksLoc.embPtr SelectBlocksLoc.lenPtr SelectBlocksLoc.phiPtr SelectBlocksLoc.levelSize
    omega
  refine ⟨fun a ha1 ha2 => ⟨by omega, by omega⟩,
    fun e he t ht => ?_⟩
  have hEmbE := hblk'.2.2.2.2.2.1 i hiB e he
  have hslotLt : B.slotPtr i e + t < B.fPtr i + B.levelSize := by
    have hmul : e * B.slot + t < B.eCap * B.slot := by
      have h1 := Nat.mul_le_mul_right B.slot (Nat.succ_le_of_lt hEmbE.1)
      rw [Nat.succ_mul] at h1
      have := hEmbE.2.2.1; omega
    unfold SelectBlocksLoc.slotPtr; omega
  have hslotLo : B.fPtr i ≤ B.slotPtr i e := by
    unfold SelectBlocksLoc.slotPtr; omega
  rw [hEmbE.2.1]
  exact ⟨by omega, by omega⟩

end MinCostFlow.MinRatio
