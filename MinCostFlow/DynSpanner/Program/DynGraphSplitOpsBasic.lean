module

public import MinCostFlow.DynSpanner.Program.DynGraphEdges
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.Finset.Card

/-!
# Part 1 of `DynGraphSplitOps`

The first part of `DynGraphSplitOps.lean`, split off to keep files short. See `DynGraphSplitOps.lean` for the
overview.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Procedure indices and bodies -/

def dgIdxMoveSlotEdge : ℕ := 0
def dgIdxMoveSlotLoop : ℕ := 1
def dgIdxApplySplit : ℕ := 2

/-- Move one half-edge (`isHead = false` -> `slotReg = 7`, `he = 2 * e`;
`isHead = true` -> `slotReg = 8`, `he = 2 * e + 1`) from `r1` (`sSrc`) to `r2` (`sDst`)
assuming `r9..r12` hold `hePrevBase, heNextBase, incHeadBase, slotDegBase` and `r3 = e`. -/
def dgMoveHalfEdgeStmt (bOps : ℕ) (isHead : Bool) : Stmt :=
  let slotReg : ℕ := if isHead then 8 else 7
  let heExpr : Expr :=
    if isHead then .bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1)
    else .bin .mul (.const 2) (.reg 3)
  .cond (.bin .eq (.load (.bin .add (.reg slotReg) (.reg 3))) (.reg 1))
    (.call 13 (bOps + dgIdxDllRemove)
      [.reg 9, .reg 10, .bin .add (.reg 11) (.reg 1), .bin .add (.reg 12) (.reg 1), heExpr] ;;
     .call 13 (bOps + dgIdxDllCons)
      [.reg 9, .reg 10, .bin .add (.reg 11) (.reg 2), .bin .add (.reg 12) (.reg 2), heExpr] ;;
     .store (.bin .add (.reg slotReg) (.reg 3)) (.reg 2))
    .nop

/-- Body of `dgMoveSlotEdgeStmt` after checking `e < eCap` and `ePres[e] != 0`, with
`r4 = vCap, r5 = eCap, r6 = dgEPresBase, r14 = isHead`. -/
def dgMoveSlotEdgeBodyStmt (bOps : ℕ) : Stmt :=
  .assign 7 (.bin .add (.reg 6) (.bin .mul (.const 3) (.reg 5))) ;;
  .assign 8 (.bin .add (.reg 6) (.bin .mul (.const 4) (.reg 5))) ;;
  .assign 9 (.bin .add (.reg 6) (.bin .mul (.const 5) (.reg 5))) ;;
  .assign 10 (.bin .add (.reg 6) (.bin .mul (.const 7) (.reg 5))) ;;
  .assign 11 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 6) (.reg 4))) ;;
  .assign 12 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 5) (.reg 4))) ;;
  .cond (.reg 14)
    (dgMoveHalfEdgeStmt bOps true)
    (dgMoveHalfEdgeStmt bOps false)

/-- Move tail (`isHead = 0`) or head (`isHead = 1`) half-edge of `e` currently attached to `sSrc`
over to `sDst` (`[gPtr, sSrc, sDst, e, isHead]`). No-op if `e ∉ G.E` (including `e ≥ eCap`). -/
def dgMoveSlotEdgeStmt (bOps : ℕ) : Stmt :=
  .assign 14 (.reg 4) ;;
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 6 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 4))) ;;
  .cond (.bin .lt (.reg 3) (.reg 5))
    (.cond (.load (.bin .add (.reg 6) (.reg 3)))
      (dgMoveSlotEdgeBodyStmt bOps)
      .nop)
    .nop ;;
  .ret (.const 0)

/-- Iterate `dgMoveSlotEdge` over an array of edge IDs (`[gPtr, sSrc, sDst, L_ptr, L_len, isHead]`). -/
def dgMoveSlotLoopStmt (bSplit : ℕ) : Stmt :=
  WordRAM.forRange 6 (.const 0) (.reg 4)
    (.assign 7 (.load (.bin .add (.reg 3) (.reg 6))) ;;
     .call 8 (bSplit + dgIdxMoveSlotEdge) [.reg 0, .reg 1, .reg 2, .reg 7, .reg 5]) ;;
  .ret (.const 0)

/-- Load `vCap`, `extToInt`/`intToExt` bases, `s_v`, `s_{v'}`, and swap slots iff `tag = 3`.
Uses `r11..r13` as temporaries so `r4..r6` (`kt, kh, L_ptr`) are preserved. -/
def dgApplySplitSetupStmt : Stmt :=
  .assign 11 (.load (.reg 0)) ;;
  .assign 12 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 11))) ;;
  .assign 13 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 11))) ;;
  .assign 9 (.load (.bin .add (.reg 12) (.reg 2))) ;;
  .assign 10 (.load (.bin .add (.reg 12) (.reg 3))) ;;
  .cond (.bin .eq (.reg 1) (.const 3))
    (.store (.bin .add (.reg 12) (.reg 2)) (.reg 10) ;;
     .store (.bin .add (.reg 13) (.reg 10)) (.reg 2) ;;
     .store (.bin .add (.reg 12) (.reg 3)) (.reg 9) ;;
     .store (.bin .add (.reg 13) (.reg 9)) (.reg 3))
    .nop

/-- Apply an encoded split (`[gPtr, tag, v, v', kt, kh, L_ptr]`) to `DynGraphAt`. -/
def dgApplySplitStmt (bOps bSplit : ℕ) : Stmt :=
  .call 7 (bOps + dgIdxAddVertex) [.reg 0, .reg 3] ;;
  dgApplySplitSetupStmt ;;
  .call 14 (bSplit + dgIdxMoveSlotLoop)
    [.reg 0, .reg 9, .reg 10, .reg 6, .reg 4, .const 0] ;;
  .call 14 (bSplit + dgIdxMoveSlotLoop)
    [.reg 0, .reg 9, .reg 10, .bin .add (.reg 6) (.reg 4), .reg 5, .const 1] ;;
  .ret (.const 0)

/-- Dynamic-graph split procedures (`[dgMoveSlotEdgeStmt, dgMoveSlotLoopStmt, dgApplySplitStmt]`). -/
def dgSplitProcs (bOps bSplit : ℕ) : List Stmt :=
  [dgMoveSlotEdgeStmt bOps, dgMoveSlotLoopStmt bSplit, dgApplySplitStmt bOps bSplit]

lemma dgSplitProcs_length (bOps bSplit : ℕ) : (dgSplitProcs bOps bSplit).length = 3 := rfl

lemma dgSplitProcs_noRand (bOps bSplit : ℕ) : ∀ s ∈ dgSplitProcs bOps bSplit, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Predicates and contracts -/

/-- Memory agrees everywhere except on the six endpoint/incidence arrays of `DynGraphAt`. -/
def DgSlotsOnlyModified (mem mem' : ℕ → ℕ) (gPtr vCap eCap : ℕ) : Prop :=
  ∀ addr,
    (∀ s < vCap, addr ≠ dgSlotDegBase gPtr vCap + s) →
    (∀ s < vCap, addr ≠ dgIncHeadBase gPtr vCap + s) →
    (∀ e < eCap, addr ≠ dgETailSlotBase gPtr vCap eCap + e) →
    (∀ e < eCap, addr ≠ dgEHeadSlotBase gPtr vCap eCap + e) →
    (∀ h < 2 * eCap, addr ≠ dgHePrevBase gPtr vCap eCap + h) →
    (∀ h < 2 * eCap, addr ≠ dgHeNextBase gPtr vCap eCap + h) →
    mem' addr = mem addr

/-- Incidence and endpoint-slot slice of `DynGraphAt` parameterized by `slotTail` and `slotHead`. -/
def DgIncStateAt (mem : ℕ → ℕ) (gPtr vCap eCap : ℕ)
    (E : Finset ℕ) (slotTail slotHead : ℕ → ℕ) : Prop :=
  mem (gPtr + dgVCapOff) = vCap ∧
  mem (gPtr + dgECapOff) = eCap ∧
  (∀ e ∈ E, e < eCap ∧ slotTail e < vCap ∧ slotHead e < vCap) ∧
  (∀ e < eCap, mem (dgEPresBase gPtr vCap + e) = if e ∈ E then 1 else 0) ∧
  (∀ e ∈ E,
    mem (dgETailSlotBase gPtr vCap eCap + e) = slotTail e ∧
    mem (dgEHeadSlotBase gPtr vCap eCap + e) = slotHead e) ∧
  (∃ incL : ℕ → List ℕ, ∀ s < vCap,
    IsDoublyLinkedList mem (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
      (dgIncHeadBase gPtr vCap + s) (2 * eCap) (incL s) ∧
    mem (dgSlotDegBase gPtr vCap + s) = (incL s).length ∧
    ∀ h, h ∈ incL s ↔
      h < 2 * eCap ∧ h / 2 ∈ E ∧
      (if h % 2 = 0 then slotTail (h / 2) else slotHead (h / 2)) = s)

/-- Contract for `dgMoveSlotEdgeStmt` (`[gPtr, sSrc, sDst, e, isHead]`). -/
def dgMoveSlotEdgeContract (w vCap eCap : ℕ) (E : Finset ℕ)
    (slotTail slotHead : ℕ → ℕ) (isHead : Bool) : Contract where
  pre args mem := ∃ gPtr sSrc sDst e, args = [gPtr, sSrc, sDst, e, if isHead then 1 else 0] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    sSrc < vCap ∧ sDst < vCap ∧ sSrc ≠ sDst ∧
    DgIncStateAt mem gPtr vCap eCap E slotTail slotHead
  post args mem ret mem' := ∃ gPtr sSrc sDst e,
    args = [gPtr, sSrc, sDst, e, if isHead then 1 else 0] ∧ ret = 0 ∧
    DgIncStateAt mem' gPtr vCap eCap E
      (if isHead then slotTail else fun x => if x = e ∧ slotTail e = sSrc then sDst else slotTail x)
      (if isHead then (fun x => if x = e ∧ slotHead e = sSrc then sDst else slotHead x) else slotHead) ∧
    DgSlotsOnlyModified mem mem' gPtr vCap eCap
  cost _ _ := 600

/-- Contract for `dgMoveSlotLoopStmt` (`[gPtr, sSrc, sDst, L_ptr, L_len, isHead]`). -/
def dgMoveSlotLoopContract (w vCap eCap : ℕ) (E : Finset ℕ)
    (slotTail slotHead : ℕ → ℕ) (L : List ℕ) (isHead : Bool) : Contract where
  pre args mem := ∃ gPtr sSrc sDst L_ptr L_len,
    args = [gPtr, sSrc, sDst, L_ptr, L_len, if isHead then 1 else 0] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ L_ptr + L_len < 2 ^ w ∧
    sSrc < vCap ∧ sDst < vCap ∧ sSrc ≠ sDst ∧
    L.length = L_len ∧ ListAt mem L_ptr L ∧ (∀ x ∈ L, x < 2 ^ w) ∧
    (∀ i < L_len, L_ptr + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ L_ptr + i) ∧
    DgIncStateAt mem gPtr vCap eCap E slotTail slotHead
  post args mem ret mem' := ∃ gPtr sSrc sDst L_ptr L_len,
    args = [gPtr, sSrc, sDst, L_ptr, L_len, if isHead then 1 else 0] ∧ ret = 0 ∧
    DgIncStateAt mem' gPtr vCap eCap E
      (if isHead then slotTail else fun x => if x ∈ L.toFinset ∧ slotTail x = sSrc then sDst else slotTail x)
      (if isHead then (fun x => if x ∈ L.toFinset ∧ slotHead x = sSrc then sDst else slotHead x) else slotHead) ∧
    DgSlotsOnlyModified mem mem' gPtr vCap eCap
  cost args _ := 625 * (args[4]?.getD 0) + 25

/-- Contract for `dgApplySplitStmt` (`[gPtr, tag, v, v', kt, kh, L_ptr]`), uniformly covering both
direct split of `G` and restricted split of any subgraph `H ⊆ G` with `H.V = G.V`. -/
def dgApplySplitContract (w vCap eCap : ℕ) (H : MGraph) (St Sh : Finset ℕ)
    (Lt Lh : List ℕ) : Contract where
  pre args mem := ∃ gPtr tag v v' kt kh L_ptr,
    args = [gPtr, tag, v, v', kt, kh, L_ptr] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ L_ptr + (kt + kh) < 2 ^ w ∧
    v ∈ H.V ∧ v' ∉ H.V ∧ v' < vCap ∧
    DynGraphAt mem gPtr vCap eCap H ∧
    Lt.length = kt ∧ Lh.length = kh ∧ ListAt mem L_ptr (Lt ++ Lh) ∧
    (∀ x ∈ Lt ++ Lh, x < 2 ^ w) ∧
    (∀ i < kt + kh, L_ptr + i < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ L_ptr + i) ∧
    ((tag = 2 ∧ (∀ e ∈ H.E, e ∈ Lt ↔ H.tail e = v ∧ e ∈ St) ∧
       (∀ e ∈ H.E, e ∈ Lh ↔ H.head e = v ∧ e ∈ Sh)) ∨
     (tag = 3 ∧ (∀ e ∈ H.E, e ∈ Lt ↔ H.tail e = v ∧ e ∉ St) ∧
       (∀ e ∈ H.E, e ∈ Lh ↔ H.head e = v ∧ e ∉ Sh)))
  post args mem ret mem' := ∃ gPtr tag v v' kt kh L_ptr,
    args = [gPtr, tag, v, v', kt, kh, L_ptr] ∧ ret = 0 ∧
    DynGraphAt mem' gPtr vCap eCap (H.applyUpdate (.split v v' (St ∩ H.E) (Sh ∩ H.E))) ∧
    ∀ addr, addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost args _ := 625 * ((args[4]?.getD 0) + (args[5]?.getD 0)) + 260

end

/-! ## Verification helpers and proofs -/

public section

lemma DgSlotsOnlyModified.refl (mem : ℕ → ℕ) (gPtr vCap eCap : ℕ) :
    DgSlotsOnlyModified mem mem gPtr vCap eCap := fun _ _ _ _ _ _ _ => rfl

lemma DgSlotsOnlyModified.trans {m0 m1 m2 : ℕ → ℕ} {gPtr vCap eCap : ℕ}
    (h01 : DgSlotsOnlyModified m0 m1 gPtr vCap eCap)
    (h12 : DgSlotsOnlyModified m1 m2 gPtr vCap eCap) :
    DgSlotsOnlyModified m0 m2 gPtr vCap eCap := by
  intro addr h1 h2 h3 h4 h5 h6
  exact (h12 addr h1 h2 h3 h4 h5 h6).trans (h01 addr h1 h2 h3 h4 h5 h6)

lemma DgSlotsOnlyModified.outside {m0 m1 : ℕ → ℕ} {gPtr vCap eCap : ℕ}
    (h : DgSlotsOnlyModified m0 m1 gPtr vCap eCap)
    {addr : ℕ} (hout : addr < gPtr ∨ gPtr + dynGraphSize vCap eCap ≤ addr) :
    m1 addr = m0 addr := by
  have _ : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  apply h addr
  · intro s hs; dsimp [dgSlotDegBase]; omega
  · intro s hs; dsimp [dgIncHeadBase]; omega
  · intro e he; dsimp [dgETailSlotBase]; omega
  · intro e he; dsimp [dgEHeadSlotBase]; omega
  · intro x hx; dsimp [dgHePrevBase]; omega
  · intro x hx; dsimp [dgHeNextBase]; omega

lemma DgSlotsOnlyModified.before_slotDeg {m0 m1 : ℕ → ℕ} {gPtr vCap eCap : ℕ}
    (h : DgSlotsOnlyModified m0 m1 gPtr vCap eCap)
    {addr : ℕ} (hlt : addr < dgSlotDegBase gPtr vCap) : m1 addr = m0 addr := by
  apply h addr
  · intro s hs; dsimp [dgSlotDegBase] at *; omega
  · intro s hs; dsimp [dgSlotDegBase, dgIncHeadBase] at *; omega
  · intro e he; dsimp [dgSlotDegBase, dgETailSlotBase] at *; omega
  · intro e he; dsimp [dgSlotDegBase, dgEHeadSlotBase] at *; omega
  · intro x hx; dsimp [dgSlotDegBase, dgHePrevBase] at *; omega
  · intro x hx; dsimp [dgSlotDegBase, dgHeNextBase] at *; omega

lemma DgSlotsOnlyModified.ePres_eq {m0 m1 : ℕ → ℕ} {gPtr vCap eCap : ℕ}
    (h : DgSlotsOnlyModified m0 m1 gPtr vCap eCap)
    {addr : ℕ} (hlo : dgEPresBase gPtr vCap ≤ addr)
    (hhi : addr < dgETailSlotBase gPtr vCap eCap) : m1 addr = m0 addr := by
  apply h addr
  · intro s hs; dsimp [dgSlotDegBase, dgEPresBase] at *; omega
  · intro s hs; dsimp [dgIncHeadBase, dgEPresBase] at *; omega
  · intro e he; dsimp [dgETailSlotBase] at *; omega
  · intro e he; dsimp [dgETailSlotBase, dgEHeadSlotBase] at *; omega
  · intro x hx; dsimp [dgETailSlotBase, dgHePrevBase] at *; omega
  · intro x hx; dsimp [dgETailSlotBase, dgHeNextBase] at *; omega

lemma runs_cond_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (hT : v ≠ 0 → ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T)
    (hF : v = 0 → ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  by_cases hv : v = 0
  · rcases hF hv with ⟨o, st', c, hr, hq, hc⟩
    exact ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨0, c, hv ▸ he, by simpa using hr, rfl⟩,
      hq, by omega⟩
  · rcases hT hv with ⟨o, st', c, hr, hq, hc⟩
    exact ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩,
      hq, by omega⟩

lemma dgIncStateAt_move_halfEdge_step {w : ℕ} {mem0 mem1 mem2 mem3 : ℕ → ℕ}
    {gPtr vCap eCap sSrc sDst e : ℕ} {E : Finset ℕ} {slotTail slotHead : ℕ → ℕ} (isHead : Bool)
    (hbound : gPtr + dynGraphSize vCap eCap < 2 ^ w)
    (hsSrc_lt : sSrc < vCap) (hsDst_lt : sDst < vCap) (hne : sSrc ≠ sDst)
    (heE : e ∈ E)
    (hInc : DgIncStateAt mem0 gPtr vCap eCap E slotTail slotHead)
    (hcur : (if isHead then slotHead e else slotTail e) = sSrc)
    {incL : ℕ → List ℕ}
    (hincL : ∀ s < vCap,
      IsDoublyLinkedList mem0 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
        (dgIncHeadBase gPtr vCap + s) (2 * eCap) (incL s) ∧
      mem0 (dgSlotDegBase gPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔
        h < 2 * eCap ∧ h / 2 ∈ E ∧
        (if h % 2 = 0 then slotTail (h / 2) else slotHead (h / 2)) = s)
    (hc1_dll : IsDoublyLinkedList mem1 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
      (dgIncHeadBase gPtr vCap + sSrc) (2 * eCap)
      ((incL sSrc).erase (if isHead then 2 * e + 1 else 2 * e)))
    (hc1_deg : mem1 (dgSlotDegBase gPtr vCap + sSrc) = mem0 (dgSlotDegBase gPtr vCap + sSrc) - 1)
    (hc1_fr : ∀ addr, (∀ x, addr = dgHePrevBase gPtr vCap eCap + x → x ∉ incL sSrc) →
      (∀ x, addr = dgHeNextBase gPtr vCap eCap + x → x ∉ incL sSrc) →
      addr ≠ dgIncHeadBase gPtr vCap + sSrc → addr ≠ dgSlotDegBase gPtr vCap + sSrc →
      mem1 addr = mem0 addr)
    (hc2_dll : IsDoublyLinkedList mem2 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
      (dgIncHeadBase gPtr vCap + sDst) (2 * eCap)
      ((if isHead then 2 * e + 1 else 2 * e) :: incL sDst))
    (hc2_deg : mem2 (dgSlotDegBase gPtr vCap + sDst) = mem1 (dgSlotDegBase gPtr vCap + sDst) + 1)
    (hc2_fr : ∀ addr,
      (∀ x, addr = dgHePrevBase gPtr vCap eCap + x →
        x ∉ (if isHead then 2 * e + 1 else 2 * e) :: incL sDst) →
      (∀ x, addr = dgHeNextBase gPtr vCap eCap + x →
        x ∉ (if isHead then 2 * e + 1 else 2 * e) :: incL sDst) →
      addr ≠ dgIncHeadBase gPtr vCap + sDst → addr ≠ dgSlotDegBase gPtr vCap + sDst →
      mem2 addr = mem1 addr)
    (hmem3 : mem3 = Function.update mem2
      ((if isHead then dgEHeadSlotBase gPtr vCap eCap else dgETailSlotBase gPtr vCap eCap) + e)
      sDst) :
    DgIncStateAt mem3 gPtr vCap eCap E
      (if isHead then slotTail else fun x => if x = e ∧ slotTail e = sSrc then sDst else slotTail x)
      (if isHead then (fun x => if x = e ∧ slotHead e = sSrc then sDst else slotHead x) else slotHead) ∧
    DgSlotsOnlyModified mem0 mem3 gPtr vCap eCap := by
  let hh : ℕ := if isHead then 2 * e + 1 else 2 * e
  change IsDoublyLinkedList mem1 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
      (dgIncHeadBase gPtr vCap + sSrc) (2 * eCap) ((incL sSrc).erase hh) at hc1_dll
  change IsDoublyLinkedList mem2 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
      (dgIncHeadBase gPtr vCap + sDst) (2 * eCap) (hh :: incL sDst) at hc2_dll
  have hbound' : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := hbound
  rcases hInc with ⟨h0, h1, hEcap, hep, hets_ehs, _⟩
  have he_lt := (hEcap e heE).1
  have h_lt : hh < 2 * eCap := by cases isHead <;> simp [hh] <;> omega
  have h_div : hh / 2 = e := by
    cases isHead
    · simp [hh]
    · simp [hh]; omega
  have h_mod : hh % 2 = if isHead then 1 else 0 := by cases isHead <;> simp [hh]
  have hh_in_src : hh ∈ incL sSrc := by
    rw [(hincL sSrc hsSrc_lt).2.2 hh]
    refine ⟨h_lt, h_div ▸ heE, ?_⟩
    cases isHead
    · simp only [Bool.false_eq_true, ↓reduceIte] at hcur h_mod; simp [h_mod, h_div, hcur]
    · simp only [↓reduceIte] at hcur h_mod; simp [h_mod, h_div, hcur]
  have hh_not_dst : hh ∉ incL sDst := by
    intro hm
    have hs := ((hincL sDst hsDst_lt).2.2 hh).mp hm |>.2.2
    rw [h_div, h_mod] at hs
    cases isHead
    · simp only [Bool.false_eq_true, ↓reduceIte] at hcur hs; exact hne (hcur.symm.trans hs)
    · simp only [↓reduceIte] at hcur hs; exact hne (hcur.symm.trans hs)
  have hdisj : ∀ s₁ s₂, s₁ < vCap → s₂ < vCap → s₁ ≠ s₂ →
      ∀ y, y ∈ incL s₁ → y ∉ incL s₂ := by
    intro s₁ s₂ hs1 hs2 h12 y hy1 hy2
    have hEq1 := ((hincL s₁ hs1).2.2 y).mp hy1 |>.2.2
    have hEq2 := ((hincL s₂ hs2).2.2 y).mp hy2 |>.2.2
    exact h12 (hEq1.symm.trans hEq2)
  have hfr03 : DgSlotsOnlyModified mem0 mem3 gPtr vCap eCap := by
    intro addr hsd hih hets hehs hhp hhn
    rw [hmem3, Function.update_of_ne]
    · rw [hc2_fr addr
        (fun x hEq hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hhp _ h_lt hEq
          · exact hhp _ ((hincL sDst hsDst_lt).1.2.1 x hx) hEq)
        (fun x hEq hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hhn _ h_lt hEq
          · exact hhn _ ((hincL sDst hsDst_lt).1.2.1 x hx) hEq)
        (hih sDst hsDst_lt) (hsd sDst hsDst_lt)]
      exact hc1_fr addr
        (fun x hEq hx => hhp _ ((hincL sSrc hsSrc_lt).1.2.1 x hx) hEq)
        (fun x hEq hx => hhn _ ((hincL sSrc hsSrc_lt).1.2.1 x hx) hEq)
        (hih sSrc hsSrc_lt) (hsd sSrc hsSrc_lt)
    · intro hEq
      cases isHead
      · exact hets e he_lt (by simpa using hEq)
      · exact hehs e he_lt (by simpa using hEq)
  have he_upd_ne : ∀ addr,
      ((if isHead then dgEHeadSlotBase gPtr vCap eCap else dgETailSlotBase gPtr vCap eCap) + e) ≠ addr →
      mem3 addr = mem2 addr := fun addr hne_a => by rw [hmem3, Function.update_of_ne hne_a.symm]
  have hslot_lt_hePrev :
      ((if isHead then dgEHeadSlotBase gPtr vCap eCap else dgETailSlotBase gPtr vCap eCap) + e) <
      dgHePrevBase gPtr vCap eCap := by
    cases isHead <;> dsimp [dgETailSlotBase, dgEHeadSlotBase, dgHePrevBase] <;> omega
  let slotTail' :=
    if isHead then slotTail else fun x => if x = e ∧ slotTail e = sSrc then sDst else slotTail x
  let slotHead' :=
    if isHead then (fun x => if x = e ∧ slotHead e = sSrc then sDst else slotHead x) else slotHead
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hfr03⟩
  · rw [hfr03.before_slotDeg (by dsimp [dgSlotDegBase, dgVCapOff]; omega), h0]
  · rw [hfr03.before_slotDeg (by dsimp [dgSlotDegBase, dgECapOff]; omega), h1]
  · intro x hxE
    rcases hEcap x hxE with ⟨hx_lt, hxt, hxh⟩
    refine ⟨hx_lt, ?_, ?_⟩
    · cases isHead
      · simp only [Bool.false_eq_true, ↓reduceIte]; split_ifs <;> assumption
      · simp only [↓reduceIte]; exact hxt
    · cases isHead
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hxh
      · simp only [↓reduceIte]; split_ifs <;> assumption
  · intro x hx_lt
    rw [hfr03.ePres_eq (by dsimp [dgEPresBase]; omega) (by dsimp [dgEPresBase, dgETailSlotBase]; omega)]
    exact hep x hx_lt
  · intro x hxE
    rcases hets_ehs x hxE with ⟨hxt0, hxh0⟩
    have hx_lt_e := (hEcap x hxE).1
    have hxt_m2 : mem2 (dgETailSlotBase gPtr vCap eCap + x) = mem0 (dgETailSlotBase gPtr vCap eCap + x) := by
      have hm12 := hc2_fr (dgETailSlotBase gPtr vCap eCap + x)
        (fun y hEq _ => by dsimp [dgETailSlotBase, dgHePrevBase] at hEq; omega)
        (fun y hEq _ => by dsimp [dgETailSlotBase, dgHeNextBase] at hEq; omega)
        (by dsimp [dgETailSlotBase, dgIncHeadBase]; omega)
        (by dsimp [dgETailSlotBase, dgSlotDegBase]; omega)
      have hm01 := hc1_fr (dgETailSlotBase gPtr vCap eCap + x)
        (fun y hEq _ => by dsimp [dgETailSlotBase, dgHePrevBase] at hEq; omega)
        (fun y hEq _ => by dsimp [dgETailSlotBase, dgHeNextBase] at hEq; omega)
        (by dsimp [dgETailSlotBase, dgIncHeadBase]; omega)
        (by dsimp [dgETailSlotBase, dgSlotDegBase]; omega)
      exact hm12.trans hm01
    have hxh_m2 : mem2 (dgEHeadSlotBase gPtr vCap eCap + x) = mem0 (dgEHeadSlotBase gPtr vCap eCap + x) := by
      have hm12 := hc2_fr (dgEHeadSlotBase gPtr vCap eCap + x)
        (fun y hEq _ => by dsimp [dgEHeadSlotBase, dgHePrevBase] at hEq; omega)
        (fun y hEq _ => by dsimp [dgEHeadSlotBase, dgHeNextBase] at hEq; omega)
        (by dsimp [dgEHeadSlotBase, dgIncHeadBase]; omega)
        (by dsimp [dgEHeadSlotBase, dgSlotDegBase]; omega)
      have hm01 := hc1_fr (dgEHeadSlotBase gPtr vCap eCap + x)
        (fun y hEq _ => by dsimp [dgEHeadSlotBase, dgHePrevBase] at hEq; omega)
        (fun y hEq _ => by dsimp [dgEHeadSlotBase, dgHeNextBase] at hEq; omega)
        (by dsimp [dgEHeadSlotBase, dgIncHeadBase]; omega)
        (by dsimp [dgEHeadSlotBase, dgSlotDegBase]; omega)
      exact hm12.trans hm01
    cases isHead
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hcur_t : slotTail e = sSrc := by simpa using hcur
      have hmem3_t : mem3 = Function.update mem2 (dgETailSlotBase gPtr vCap eCap + e) sDst := by
        simpa using hmem3
      constructor
      · by_cases hxe : x = e
        · subst hxe; rw [hmem3_t, Function.update_self]; simp [hcur_t]
        · rw [hmem3_t, Function.update_of_ne (by dsimp [dgETailSlotBase]; omega), hxt_m2, hxt0]
          simp [hxe]
      · rw [hmem3_t, Function.update_of_ne (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega),
          hxh_m2, hxh0]
    · simp only [↓reduceIte]
      have hcur_h : slotHead e = sSrc := by simpa using hcur
      have hmem3_h : mem3 = Function.update mem2 (dgEHeadSlotBase gPtr vCap eCap + e) sDst := by
        simpa using hmem3
      constructor
      · rw [hmem3_h, Function.update_of_ne (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega),
          hxt_m2, hxt0]
      · by_cases hxe : x = e
        · subst hxe; rw [hmem3_h, Function.update_self]; simp [hcur_h]
        · rw [hmem3_h, Function.update_of_ne (by dsimp [dgEHeadSlotBase]; omega), hxh_m2, hxh0]
          simp [hxe]
  · refine ⟨fun s => if s = sSrc then (incL sSrc).erase hh else
        if s = sDst then hh :: incL sDst else incL s, fun s hs => ?_⟩
    have hm1_deg_dst : mem1 (dgSlotDegBase gPtr vCap + sDst) = mem0 (dgSlotDegBase gPtr vCap + sDst) :=
      hc1_fr _
        (fun x hEq _ => by dsimp [dgSlotDegBase, dgHePrevBase] at hEq; omega)
        (fun x hEq _ => by dsimp [dgSlotDegBase, dgHeNextBase] at hEq; omega)
        (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega)
        (by dsimp [dgSlotDegBase]; omega)
    have hm3_dll : IsDoublyLinkedList mem3 (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
        (dgIncHeadBase gPtr vCap + s) (2 * eCap)
        (if s = sSrc then (incL sSrc).erase hh else
          if s = sDst then hh :: incL sDst else incL s) := by
      split_ifs with hs1 hs2
      · rw [hs1]
        have hnot_src : ∀ y ∈ (incL sSrc).erase hh, y ∉ hh :: incL sDst := by
          intro y hy hc
          rcases List.mem_cons.mp hc with rfl | hydst
          · exact ((hincL sSrc hsSrc_lt).1.1.mem_erase_iff).mp hy |>.1 rfl
          · exact hdisj sSrc sDst hsSrc_lt hsDst_lt hne y (List.mem_of_mem_erase hy) hydst
        have h12 := hc1_dll.of_agree
          (by rw [hc2_fr _ (fun x hEq hx => by
                have hlt := hc2_dll.2.1 x hx; dsimp [dgIncHeadBase, dgHePrevBase] at hEq; omega)
              (fun x hEq hx => by
                have hlt := hc2_dll.2.1 x hx; dsimp [dgIncHeadBase, dgHeNextBase] at hEq; omega)
              (by dsimp [dgIncHeadBase]; omega)
              (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega)])
          (fun x hx => hc2_fr _
            (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnot_src x hx hy)
            (fun y hEq hy => by
              have hlt1 := hc1_dll.2.1 x hx; have hlt2 := hc2_dll.2.1 y hy
              dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega)
            (by dsimp [dgHePrevBase, dgIncHeadBase]; omega)
            (by dsimp [dgHePrevBase, dgSlotDegBase]; omega))
          (fun x hx => hc2_fr _
            (fun y hEq hy => by
              have hlt1 := hc1_dll.2.1 x hx; have hlt2 := hc2_dll.2.1 y hy
              dsimp [dgHeNextBase, dgHePrevBase] at hEq; omega)
            (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnot_src x hx hy)
            (by dsimp [dgHeNextBase, dgIncHeadBase]; omega)
            (by dsimp [dgHeNextBase, dgSlotDegBase]; omega))
        exact h12.of_agree
          (he_upd_ne _ (by cases isHead <;> dsimp [dgIncHeadBase, dgETailSlotBase, dgEHeadSlotBase] <;> omega))
          (fun x hx => he_upd_ne _ (by omega))
          (fun x hx => he_upd_ne _ (by dsimp [dgHePrevBase, dgHeNextBase] at *; omega))
      · rw [hs2]
        exact hc2_dll.of_agree
          (he_upd_ne _ (by cases isHead <;> dsimp [dgIncHeadBase, dgETailSlotBase, dgEHeadSlotBase] <;> omega))
          (fun x hx => he_upd_ne _ (by omega))
          (fun x hx => he_upd_ne _ (by dsimp [dgHePrevBase, dgHeNextBase] at *; omega))
      · have hnot1 : ∀ y ∈ incL s, y ∉ incL sSrc := fun y hy hc => hdisj s sSrc hs hsSrc_lt hs1 y hy hc
        have hnot2 : ∀ y ∈ incL s, y ∉ hh :: incL sDst := by
          intro y hy hc
          rcases List.mem_cons.mp hc with rfl | hydst
          · have hEq := ((hincL s hs).2.2 hh).mp hy |>.2.2
            rw [h_div, h_mod] at hEq
            cases isHead
            · simp only [Bool.false_eq_true, ↓reduceIte] at hEq hcur; exact hs1 (hEq.symm.trans hcur)
            · simp only [↓reduceIte] at hEq hcur; exact hs1 (hEq.symm.trans hcur)
          · exact hdisj s sDst hs hsDst_lt hs2 y hy hydst
        have h01 := (hincL s hs).1.of_agree
          (hc1_fr _ (fun x hEq hx => by
            have hlt := (hincL sSrc hsSrc_lt).1.2.1 x hx; dsimp [dgIncHeadBase, dgHePrevBase] at hEq; omega)
            (fun x hEq hx => by
              have hlt := (hincL sSrc hsSrc_lt).1.2.1 x hx; dsimp [dgIncHeadBase, dgHeNextBase] at hEq; omega)
            (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega))
          (fun x hx => hc1_fr _
            (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnot1 x hx hy)
            (fun y hEq hy => by
              have hlt1 := (hincL s hs).1.2.1 x hx; have hlt2 := (hincL sSrc hsSrc_lt).1.2.1 y hy
              dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega)
            (by dsimp [dgHePrevBase, dgIncHeadBase]; omega)
            (by dsimp [dgHePrevBase, dgSlotDegBase]; omega))
          (fun x hx => hc1_fr _
            (fun y hEq hy => by
              have hlt1 := (hincL s hs).1.2.1 x hx; have hlt2 := (hincL sSrc hsSrc_lt).1.2.1 y hy
              dsimp [dgHeNextBase, dgHePrevBase] at hEq; omega)
            (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnot1 x hx hy)
            (by dsimp [dgHeNextBase, dgIncHeadBase]; omega)
            (by dsimp [dgHeNextBase, dgSlotDegBase]; omega))
        have h02 := h01.of_agree
          (hc2_fr _ (fun x hEq hx => by
            have hlt := hc2_dll.2.1 x hx; dsimp [dgIncHeadBase, dgHePrevBase] at hEq; omega)
            (fun x hEq hx => by
              have hlt := hc2_dll.2.1 x hx; dsimp [dgIncHeadBase, dgHeNextBase] at hEq; omega)
            (by dsimp [dgIncHeadBase]; omega) (by dsimp [dgIncHeadBase, dgSlotDegBase]; omega))
          (fun x hx => hc2_fr _
            (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnot2 x hx hy)
            (fun y hEq hy => by
              have hlt1 := h01.2.1 x hx; have hlt2 := hc2_dll.2.1 y hy
              dsimp [dgHePrevBase, dgHeNextBase] at hEq; omega)
            (by dsimp [dgHePrevBase, dgIncHeadBase]; omega)
            (by dsimp [dgHePrevBase, dgSlotDegBase]; omega))
          (fun x hx => hc2_fr _
            (fun y hEq hy => by
              have hlt1 := h01.2.1 x hx; have hlt2 := hc2_dll.2.1 y hy
              dsimp [dgHeNextBase, dgHePrevBase] at hEq; omega)
            (fun y hEq hy => by rw [← Nat.add_left_cancel hEq] at hy; exact hnot2 x hx hy)
            (by dsimp [dgHeNextBase, dgIncHeadBase]; omega)
            (by dsimp [dgHeNextBase, dgSlotDegBase]; omega))
        exact h02.of_agree
          (he_upd_ne _ (by cases isHead <;> dsimp [dgIncHeadBase, dgETailSlotBase, dgEHeadSlotBase] <;> omega))
          (fun x hx => he_upd_ne _ (by omega))
          (fun x hx => he_upd_ne _ (by dsimp [dgHePrevBase, dgHeNextBase] at *; omega))
    refine ⟨hm3_dll, ?_, fun x => ?_⟩
    · dsimp only
      split_ifs with hs1 hs2
      · rw [hs1]
        have hm2_deg := hc2_fr (dgSlotDegBase gPtr vCap + sSrc)
          (fun x hEq _ => by dsimp [dgSlotDegBase, dgHePrevBase] at hEq; omega)
          (fun x hEq _ => by dsimp [dgSlotDegBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega)
          (by dsimp [dgSlotDegBase]; omega)
        rw [he_upd_ne _ (by dsimp [dgSlotDegBase] at *; cases isHead <;> [dsimp [dgETailSlotBase]; dsimp [dgEHeadSlotBase]] <;> omega),
          hm2_deg, hc1_deg, (hincL sSrc hsSrc_lt).2.1, List.length_erase_of_mem hh_in_src]
      · rw [hs2]
        rw [he_upd_ne _ (by dsimp [dgSlotDegBase] at *; cases isHead <;> [dsimp [dgETailSlotBase]; dsimp [dgEHeadSlotBase]] <;> omega),
          hc2_deg, hm1_deg_dst, (hincL sDst hsDst_lt).2.1, List.length_cons]
      · have hm1_deg := hc1_fr (dgSlotDegBase gPtr vCap + s)
          (fun x hEq _ => by dsimp [dgSlotDegBase, dgHePrevBase] at hEq; omega)
          (fun x hEq _ => by dsimp [dgSlotDegBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega)
          (by dsimp [dgSlotDegBase]; omega)
        have hm2_deg := hc2_fr (dgSlotDegBase gPtr vCap + s)
          (fun x hEq _ => by dsimp [dgSlotDegBase, dgHePrevBase] at hEq; omega)
          (fun x hEq _ => by dsimp [dgSlotDegBase, dgHeNextBase] at hEq; omega)
          (by dsimp [dgSlotDegBase, dgIncHeadBase]; omega)
          (by dsimp [dgSlotDegBase]; omega)
        rw [he_upd_ne _ (by dsimp [dgSlotDegBase] at *; cases isHead <;> [dsimp [dgETailSlotBase]; dsimp [dgEHeadSlotBase]] <;> omega),
          hm2_deg, hm1_deg, (hincL s hs).2.1]
    · by_cases hxh : x = hh
      · subst hxh
        constructor
        · intro hx
          refine ⟨h_lt, h_div ▸ heE, ?_⟩
          dsimp only at hx
          have hs_eq : s = sDst := by
            split_ifs at hx with hs1 hs2
            · exact absurd hx ((hincL sSrc hsSrc_lt).1.1.mem_erase_iff.mp · |>.1 rfl)
            · exact hs2
            · have hEq := ((hincL s hs).2.2 hh).mp hx |>.2.2
              rw [h_div, h_mod] at hEq
              cases isHead
              · simp only [Bool.false_eq_true, ↓reduceIte] at hEq hcur; exact absurd (hEq.symm.trans hcur) hs1
              · simp only [↓reduceIte] at hEq hcur; exact absurd (hEq.symm.trans hcur) hs1
          rw [hs_eq, h_div, h_mod]
          cases isHead
          · simp only [Bool.false_eq_true, ↓reduceIte] at hcur ⊢; simp [hcur]
          · simp only [↓reduceIte] at hcur ⊢; simp [hcur]
        · rintro ⟨_, _, hslot⟩
          have hs_eq : s = sDst := by
            rw [h_div, h_mod] at hslot
            cases isHead
            · simp only [Bool.false_eq_true, ↓reduceIte] at hcur hslot
              simpa [slotTail', hcur] using hslot.symm
            · simp only [↓reduceIte] at hcur hslot
              simpa [slotHead', hcur] using hslot.symm
          dsimp only; rw [hs_eq]; simp [hne.symm]
      · have hslot_eq :
            (if x % 2 = 0 then slotTail' (x / 2) else slotHead' (x / 2)) =
            (if x % 2 = 0 then slotTail (x / 2) else slotHead (x / 2)) := by
          have hne_pair : x / 2 ≠ e ∨ x % 2 ≠ hh % 2 := by
            by_contra hc; push Not at hc
            apply hxh
            have hm_eq := hc.2; rw [h_mod] at hm_eq
            have hd_eq := hc.1
            cases isHead
            · simp only [Bool.false_eq_true, ↓reduceIte] at hm_eq; dsimp [hh]; omega
            · simp only [↓reduceIte] at hm_eq; dsimp [hh]; omega
          cases isHead <;> simp only [slotTail', slotHead', Bool.false_eq_true, ↓reduceIte]
          · by_cases hmx : x % 2 = 0
            · simp only [hmx, ↓reduceIte]
              split_ifs with hp
              · rcases hne_pair with hne_e | hne_m
                · exact absurd hp.1 hne_e
                · exact absurd (by simp only [hmx, h_mod, Bool.false_eq_true, ↓reduceIte]) hne_m
              · rfl
            · simp only [hmx, ↓reduceIte]
          · by_cases hmx : x % 2 = 0
            · simp only [hmx, ↓reduceIte]
            · simp only [hmx, ↓reduceIte]
              split_ifs with hp
              · rcases hne_pair with hne_e | hne_m
                · exact absurd hp.1 hne_e
                · exact absurd (by simp only [h_mod, ↓reduceIte]; omega) hne_m
              · rfl
        rw [hslot_eq]
        dsimp only
        constructor
        · intro hx
          have hx_in : x ∈ incL s := by
            split_ifs at hx with hs1 hs2
            · rw [hs1]; exact List.mem_of_mem_erase hx
            · rw [hs2]
              rcases List.mem_cons.mp hx with hEq | hx'
              · exact absurd hEq hxh
              · exact hx'
            · exact hx
          exact ((hincL s hs).2.2 x).mp hx_in
        · intro hx
          have hx_in := ((hincL s hs).2.2 x).mpr hx
          split_ifs with hs1 hs2
          · rw [hs1] at hx_in; exact (hincL sSrc hsSrc_lt).1.1.mem_erase_iff.mpr ⟨hxh, hx_in⟩
          · rw [hs2] at hx_in; exact List.mem_cons_of_mem _ hx_in
          · exact hx_in

lemma dgIncStateAt_of_not_mem {mem : ℕ → ℕ} {gPtr vCap eCap sSrc sDst e : ℕ}
    {E : Finset ℕ} {slotTail slotHead : ℕ → ℕ} (isHead : Bool)
    (he_not : e ∉ E) (hInc : DgIncStateAt mem gPtr vCap eCap E slotTail slotHead) :
    DgIncStateAt mem gPtr vCap eCap E
      (if isHead then slotTail else fun x => if x = e ∧ slotTail e = sSrc then sDst else slotTail x)
      (if isHead then (fun x => if x = e ∧ slotHead e = sSrc then sDst else slotHead x) else slotHead) := by
  cases isHead <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rcases hInc with ⟨h0, h1, hEcap, hep, hets_ehs, ⟨incL, hincL⟩⟩
    have hne_E : ∀ x ∈ E, x ≠ e := fun x hx hEq => he_not (hEq ▸ hx)
    refine ⟨h0, h1, fun x hx => ?_, hep, fun x hx => ?_, ⟨incL, fun s hs => ?_⟩⟩
    · simp [hne_E x hx]; exact hEcap x hx
    · simp [hne_E x hx]; exact hets_ehs x hx
    · rcases hincL s hs with ⟨hdll, hdeg, hmem⟩
      refine ⟨hdll, hdeg, fun h => ?_⟩
      rw [hmem h]
      constructor <;> rintro ⟨hlt, h2E, hslot⟩ <;> refine ⟨hlt, h2E, ?_⟩ <;>
        have hne2 := hne_E (h / 2) h2E <;> simpa [hne2] using hslot
  · rcases hInc with ⟨h0, h1, hEcap, hep, hets_ehs, ⟨incL, hincL⟩⟩
    have hne_E : ∀ x ∈ E, x ≠ e := fun x hx hEq => he_not (hEq ▸ hx)
    refine ⟨h0, h1, fun x hx => ?_, hep, fun x hx => ?_, ⟨incL, fun s hs => ?_⟩⟩
    · simp [hne_E x hx]; exact hEcap x hx
    · simp [hne_E x hx]; exact hets_ehs x hx
    · rcases hincL s hs with ⟨hdll, hdeg, hmem⟩
      refine ⟨hdll, hdeg, fun h => ?_⟩
      rw [hmem h]
      constructor <;> rintro ⟨hlt, h2E, hslot⟩ <;> refine ⟨hlt, h2E, ?_⟩ <;>
        have hne2 := hne_E (h / 2) h2E <;> simpa [hne2] using hslot

end

end MinCostFlow.DynSpanner.Program
