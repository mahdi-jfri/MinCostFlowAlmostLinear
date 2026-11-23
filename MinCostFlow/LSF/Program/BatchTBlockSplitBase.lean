module

public import MinCostFlow.LSF.Program.BatchTBlockOps
public import MinCostFlow.DynSpanner.Program.DynGraphSplit
import Mathlib.Tactic.Linarith

/-!
# `T`-Block Vertex Split Definitions and Scan Loop (`BatchTBlockSplitBase`)

Defines `lsfTBlockSplitProc`, its contract `lsfTBlockSplitContract`, `scanTrackList`, and proves
the scan loop (`scanLoop_runs`) and setup prefix (`tBlockSplitSetup_regs_lo`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Sequence a normal-termination `Runs` derivation with a cost-bounded continuation. -/
lemma runs_seq_of_runs_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ : Stmt} {st st₁ : State} {c₁ k T : ℕ} {Q : Outcome → State → Prop}
    (hr₁ : Runs w p ω s₁ st .normal st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s₂ st₁ o st' c₂ ∧ Q o st' ∧ (k + c₁ + 1) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases hrest with ⟨o, st', c₂, hr₂, hq, hc⟩
  exact ⟨o, st', c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), hq, by omega⟩

/-! ## Procedure definitions -/

/-- Scan `lenReg` (`r8` or `r9`) edge IDs starting at `baseExpr` (`updPtr + 5` or
`updPtr + 5 + kt`), appending `2 * i` (for `isHead = false`) or `2 * i + 1` (for `isHead = true`)
to `scratchPtr` (`r12 + r13`) whenever `e < eCap` and `idxOfEdge[e] = i + 1 ≠ 0`. -/
def lsfTBlockSplitScanLoopStmt (isHead : Bool) : Stmt :=
  let lenReg : ℕ := if isHead then 9 else 8
  let baseExpr : Expr :=
    if isHead then .bin .add (.bin .add (.reg 1) (.const 5)) (.reg 8)
    else .bin .add (.reg 1) (.const 5)
  let trackExpr : Expr :=
    if isHead then .bin .add (.bin .mul (.const 2) (.bin .sub (.reg 16) (.const 1))) (.const 1)
    else .bin .mul (.const 2) (.bin .sub (.reg 16) (.const 1))
  .assign 14 (.const 0) ;;
  .loop (.bin .lt (.reg 14) (.reg lenReg))
    (.assign 15 (.load (.bin .add baseExpr (.reg 14))) ;;
     .cond (.bin .lt (.reg 15) (.reg 3))
       (.assign 16 (.load (.bin .add (.reg 11) (.reg 15))) ;;
        .cond (.reg 16)
          (.store (.bin .add (.reg 12) (.reg 13)) trackExpr ;;
           .assign 13 (.bin .add (.reg 13) (.const 1)))
          .nop)
       .nop ;;
     .assign 14 (.bin .add (.reg 14) (.const 1)))

/-- Load `dgExtToIntBase`, `dgIntToExtBase`, `s_v`, `s_v'` of `dgT` (`r10`, `vCap = r2`, `tag = r5`,
`v = r6`, `v' = r7`) into `r14..r17`, swapping slots iff `tag = 3`. -/
def lsfTBlockSplitSetupStmt : Stmt :=
  .assign 14 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 3) (.reg 2))) ;;
  .assign 15 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 4) (.reg 2))) ;;
  .assign 16 (.load (.bin .add (.reg 14) (.reg 6))) ;;
  .assign 17 (.load (.bin .add (.reg 14) (.reg 7))) ;;
  .cond (.bin .eq (.reg 5) (.const 3))
    (.store (.bin .add (.reg 14) (.reg 6)) (.reg 17) ;;
     .store (.bin .add (.reg 15) (.reg 17)) (.reg 6) ;;
     .store (.bin .add (.reg 14) (.reg 7)) (.reg 16) ;;
     .store (.bin .add (.reg 15) (.reg 16)) (.reg 7))
    .nop

/-- Update `TBlockAt` across a canonical vertex split encoded at `updPtr`
(`[tPtr, updPtr, vCap, eCap, tM]`). -/
def lsfTBlockSplitProc (idxDgAddV idxDgMoveLoop : ℕ) : Stmt :=
  .assign 5 (.load (.reg 1)) ;;
  .assign 6 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 7 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .assign 8 (.load (.bin .add (.reg 1) (.const 3))) ;;
  .assign 9 (.load (.bin .add (.reg 1) (.const 4))) ;;
  .assign 10 (.load (.bin .add (.reg 0) (.const tOffDgTPtr))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const tOffIdxOfEdgePtr))) ;;
  .assign 12 (.load (.bin .add (.reg 0) (.const tOffSplitScratchPtr))) ;;
  .assign 13 (.const 0) ;;
  lsfTBlockSplitScanLoopStmt false ;;
  lsfTBlockSplitScanLoopStmt true ;;
  .call 14 idxDgAddV [.reg 10, .reg 7] ;;
  lsfTBlockSplitSetupStmt ;;
  .call 18 idxDgMoveLoop [.reg 10, .reg 16, .reg 17, .reg 12, .reg 13, .const 0] ;;
  .call 18 idxDgMoveLoop [.reg 10, .reg 16, .reg 17, .reg 12, .reg 13, .const 1] ;;
  .ret (.const 0)

lemma lsfTBlockSplitProc_noRand (idxDgAddV idxDgMoveLoop : ℕ) :
    (lsfTBlockSplitProc idxDgAddV idxDgMoveLoop).NoRand := by
  dsimp [lsfTBlockSplitProc, lsfTBlockSplitScanLoopStmt, lsfTBlockSplitSetupStmt]; trivial

/-! ## Contract -/

/-- Contract for `lsfTBlockSplitProc` (`[tPtr, updPtr, vCap, eCap, tM]`). -/
def lsfTBlockSplitContract (w vCap eCap tM : ℕ) (G T_cur T₀ : MGraph)
    (π : ℕ → ℕ) (tOrigList : List ℕ) (v v' : ℕ) (St Sh : Finset ℕ) (len : ℕ) : Contract where
  pre args mem := ∃ tPtr updPtr,
    args = [tPtr, updPtr, vCap, eCap, tM] ∧
    16 ≤ 2 ^ w ∧ tPtr + tBlockSize vCap eCap tM < 2 ^ w ∧ updPtr + len < 2 ^ w ∧
    (∀ i < len, updPtr + i < tPtr ∨ tPtr + tBlockSize vCap eCap tM ≤ updPtr + i) ∧
    (∀ i < len, mem (updPtr + i) < 2 ^ w) ∧
    G.IsValid ∧ (∀ e ∈ G.E, e < eCap) ∧
    G.UpdateIsValid (.split v v' St Sh) ∧ v' < vCap ∧
    (∀ e ∈ St, e ∈ G.E ∧ G.tail e = v) ∧
    (∀ e ∈ Sh, e ∈ G.E ∧ G.head e = v) ∧
    UpdateAt mem updPtr G (.split v v' St Sh) len ∧
    T_cur.IsValid ∧ T_cur.V = G.V ∧ T_cur.E = T₀.E ∧
    TBlockAt mem tPtr vCap eCap tM G T_cur T₀ π tOrigList
  post args mem ret mem' := ∃ tPtr updPtr,
    args = [tPtr, updPtr, vCap, eCap, tM] ∧ ret = 0 ∧
    TBlockAt mem' tPtr vCap eCap tM
      (G.applyUpdate (.split v v' St Sh)) (T_cur.applyUpdate (.split v v' St Sh)) T₀ π tOrigList ∧
    ∀ a, a < tPtr ∨ tPtr + tBlockSize vCap eCap tM ≤ a → mem' a = mem a
  cost args mem := 1400 * (mem (args.getD 1 0 + 3) + mem (args.getD 1 0 + 4) + 1)

/-! ## Pure scan-list and `DynGraphAt` postcondition helpers -/

/-- Tracker IDs extracted from an edge list `L` by looking up `idxOfEdge[e]`. -/
def scanTrackList (mem : ℕ → ℕ) (idxBase eCap : ℕ) (isHead : Bool) (L : List ℕ) : List ℕ :=
  L.filterMap fun e =>
    if e < eCap ∧ mem (idxBase + e) ≠ 0 then
      some (if isHead then 2 * (mem (idxBase + e) - 1) + 1 else 2 * (mem (idxBase + e) - 1))
    else none

lemma scanTrackList_length_le (mem : ℕ → ℕ) (idxBase eCap : ℕ) (isHead : Bool) (L : List ℕ) :
    (scanTrackList mem idxBase eCap isHead L).length ≤ L.length := by
  dsimp [scanTrackList]
  exact List.length_filterMap_le _ _

lemma scanTrackList_nodup_and_bounds {mem : ℕ → ℕ} {tPtr vCap eCap tM : ℕ} {tOrigList L : List ℕ}
    {isHead : Bool}
    (hlen : tOrigList.length = tM) (hndL : L.Nodup)
    (hidx2 : ∀ e < eCap, mem (tIdxOfEdgeBase tPtr vCap tM + e) ≠ 0 →
      ∃ i, ∃ (_ : i < tOrigList.length),
        tOrigList[i] = e ∧ mem (tIdxOfEdgeBase tPtr vCap tM + e) = i + 1) :
    let res := scanTrackList mem (tIdxOfEdgeBase tPtr vCap tM) eCap isHead L
    res.Nodup ∧ res.length ≤ tM ∧
    (∀ k ∈ res, k < 2 * tM ∧ k % 2 = if isHead then 1 else 0) ∧
    (∀ i (hi : i < tOrigList.length), tOrigList[i] < eCap →
      ((if isHead then 2 * i + 1 else 2 * i) ∈ res ↔
        tOrigList[i] ∈ L ∧ mem (tIdxOfEdgeBase tPtr vCap tM + tOrigList[i]) = i + 1)) := by
  intro res
  have hmem_res : ∀ k, k ∈ res ↔ ∃ e ∈ L, e < eCap ∧ mem (tIdxOfEdgeBase tPtr vCap tM + e) ≠ 0 ∧
      k = if isHead then 2 * (mem (tIdxOfEdgeBase tPtr vCap tM + e) - 1) + 1
          else 2 * (mem (tIdxOfEdgeBase tPtr vCap tM + e) - 1) := by
    intro k
    simp only [res, scanTrackList, List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq]
    constructor
    · rintro ⟨e, heL, ⟨hlt, hne⟩, hEq⟩; exact ⟨e, heL, hlt, hne, hEq.symm⟩
    · rintro ⟨e, heL, hlt, hne, hEq⟩; exact ⟨e, heL, ⟨hlt, hne⟩, hEq.symm⟩
  have hbounds : ∀ k ∈ res, k < 2 * tM ∧ k % 2 = if isHead then 1 else 0 := by
    intro k hk
    obtain ⟨e, _, hlt, hne, rfl⟩ := (hmem_res k).mp hk
    obtain ⟨i, hi, _, hidx_eq⟩ := hidx2 e hlt hne
    rw [hidx_eq]
    cases isHead <;> simp <;> omega
  have hnd : res.Nodup := by
    dsimp only [res, scanTrackList]
    clear res hmem_res hbounds
    induction L with
    | nil => simp
    | cons a as ih =>
      obtain ⟨ha_not, has_nd⟩ := List.nodup_cons.mp hndL
      rw [List.filterMap_cons]
      by_cases h : a < eCap ∧ mem (tIdxOfEdgeBase tPtr vCap tM + a) ≠ 0
      · rw [ite_eq_left h]; dsimp only
        rw [List.nodup_cons]
        refine ⟨?_, ih has_nd⟩
        intro hmem
        simp only [List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq] at hmem
        obtain ⟨b, hb, ⟨hb1, hb2⟩, hEq⟩ := hmem
        obtain ⟨ia, hia, ha_eq, hia_m⟩ := hidx2 a h.1 h.2
        obtain ⟨ib, hib, hb_eq, hib_m⟩ := hidx2 b hb1 hb2
        rw [hia_m, hib_m] at hEq
        have hi_eq : ia = ib := by cases isHead <;> simp at hEq <;> omega
        have hab : a = b := ha_eq.symm.trans (hi_eq ▸ hb_eq)
        exact ha_not (hab ▸ hb)
      · rw [ite_eq_right h]; dsimp only
        exact ih has_nd
  have hlen_le : res.length ≤ tM := by
    have hsub : res.toFinset ⊆ (Finset.range tM).image (fun i => if isHead then 2 * i + 1 else 2 * i) := by
      intro k hk
      obtain ⟨hk_lt, hk_mod⟩ := hbounds k (List.mem_toFinset.mp hk)
      refine Finset.mem_image.mpr ⟨k / 2, Finset.mem_range.mpr (by omega), ?_⟩
      cases isHead <;> simp at hk_mod ⊢ <;> omega
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd] at hcard
    exact hcard.trans (Finset.card_image_le.trans (by simp))
  refine ⟨hnd, hlen_le, hbounds, fun i hi hlt => ?_⟩
  rw [hmem_res]
  constructor
  · rintro ⟨e, heL, he_lt, he_ne, hEq⟩
    obtain ⟨j, hj, hj_eq, hj_m⟩ := hidx2 e he_lt he_ne
    rw [hj_m] at hEq
    have hij : i = j := by cases isHead <;> simp at hEq <;> omega
    subst hij
    rw [hj_eq]; exact ⟨heL, hj_m⟩
  · rintro ⟨heL, hidx_m⟩
    refine ⟨tOrigList[i], heL, hlt, by rw [hidx_m]; omega, ?_⟩
    rw [hidx_m]; cases isHead <;> simp

/-- Loop verification for `lsfTBlockSplitScanLoopStmt isHead`: appends
`scanTrackList mem0 idxBase eCap isHead L` to `scratchBase + k0` in `≤ 45 * L.length + 15` steps. -/
lemma scanLoop_runs {w updPtr kt kh idxBase scratchBase eCap tM : ℕ}
    {p : Program} {ω : ℕ → Bool} {L : List ℕ} {isHead : Bool} {mem0 : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hupd_lt : updPtr + 5 + kt + kh < 2 ^ w)
    (hidx_lt : idxBase + eCap < 2 ^ w)
    (hscr_lt : scratchBase + (2 * tM + 4) < 2 ^ w)
    (hL_len : L.length = if isHead then kh else kt)
    (hLA0 : ListAt mem0 (if isHead then updPtr + 5 + kt else updPtr + 5) L)
    (hdisj_L : ∀ j < L.length, ∀ q < 2 * tM,
      (if isHead then updPtr + 5 + kt else updPtr + 5) + j ≠ scratchBase + q)
    (hdisj_idx : ∀ e < eCap, ∀ q < 2 * tM, idxBase + e ≠ scratchBase + q)
    (hL_word : ∀ x ∈ L, x < 2 ^ w)
    (hidx_bd : ∀ e < eCap, mem0 (idxBase + e) ≤ tM) :
    ∀ (rem j k : ℕ) (acc : List ℕ) (st : State),
      j + rem = L.length →
      k = acc.length →
      acc.length + (scanTrackList mem0 idxBase eCap isHead (L.drop j)).length ≤ 2 * tM →
      st.regs 1 = updPtr → st.regs 3 = eCap →
      st.regs 8 = kt → st.regs 9 = kh →
      st.regs 11 = idxBase → st.regs 12 = scratchBase →
      st.regs 13 = k → st.regs 14 = j →
      ListAt st.mem scratchBase acc →
      (∀ a, ¬ (scratchBase ≤ a ∧ a < scratchBase + 2 * tM) → st.mem a = mem0 a) →
      ∃ st' c,
        Runs w p ω
          (.loop (.bin .lt (.reg 14) (.reg (if isHead then 9 else 8)))
            (.assign 15 (.load (.bin .add
              (if isHead then .bin .add (.bin .add (.reg 1) (.const 5)) (.reg 8)
               else .bin .add (.reg 1) (.const 5)) (.reg 14))) ;;
             .cond (.bin .lt (.reg 15) (.reg 3))
               (.assign 16 (.load (.bin .add (.reg 11) (.reg 15))) ;;
                .cond (.reg 16)
                  (.store (.bin .add (.reg 12) (.reg 13))
                    (if isHead then .bin .add (.bin .mul (.const 2) (.bin .sub (.reg 16) (.const 1))) (.const 1)
                     else .bin .mul (.const 2) (.bin .sub (.reg 16) (.const 1))) ;;
                   .assign 13 (.bin .add (.reg 13) (.const 1)))
                  .nop)
               .nop ;;
             .assign 14 (.bin .add (.reg 14) (.const 1))))
          st .normal st' c ∧
        (∀ r, r ≤ 12 → st'.regs r = st.regs r) ∧
        st'.regs 13 = acc.length + (scanTrackList mem0 idxBase eCap isHead (L.drop j)).length ∧
        ListAt st'.mem scratchBase (acc ++ scanTrackList mem0 idxBase eCap isHead (L.drop j)) ∧
        (∀ a, ¬ (scratchBase ≤ a ∧ a < scratchBase + 2 * tM) → st'.mem a = mem0 a) ∧
        c ≤ 55 * rem + 10 := by
  let baseAddr := if isHead then updPtr + 5 + kt else updPtr + 5
  intro rem
  have hlen_lt : (if isHead then kh else kt) < 2 ^ w := by cases isHead <;> simp <;> omega
  have hupd5_lt : updPtr + 5 < 2 ^ w := by omega
  have hbase_lt : baseAddr < 2 ^ w := by dsimp [baseAddr]; cases isHead <;> simp <;> omega
  have hupd_lt0 : updPtr < 2 ^ w := by omega
  have hkt_ltw : kt < 2 ^ w := by omega
  have heCap_ltw : eCap < 2 ^ w := by omega
  have hidx0_ltw : idxBase < 2 ^ w := by omega
  have hscr0_ltw : scratchBase < 2 ^ w := by omega
  induction rem with
  | zero =>
    intro j k acc st hjrem hk hcap hr1 hr3 hr8 hr9 hr11 hr12 hr13 hr14 hacc hfr
    have hjL : j = L.length := by omega
    have hj_ltw : j < 2 ^ w := by omega
    have hdrop : L.drop j = [] := List.drop_of_length_le (by omega)
    have hcond : (Expr.bin .lt (.reg 14) (.reg (if isHead then 9 else 8))).eval w st = some 0 := by
      have hregL : (Expr.reg (if isHead then 9 else 8)).eval w st = some (if isHead then kh else kt) := by
        cases isHead <;> simp [Expr.eval_reg, hr8, hr9]
      rw [show (0 : ℕ) = BinOp.lt.eval j (if isHead then kh else kt) by
        dsimp [BinOp.eval]; rw [ite_eq_right (by omega)]]
      exact Expr.eval_bin (by eval_expr) hregL
        (by dsimp [BinOp.eval]; rw [ite_eq_right (by omega)]; omega)
    refine ⟨st, 4, ?_, fun _ _ => rfl, ?_, ?_, hfr, by omega⟩
    · rw [runs_loop_iff]; exact Or.inl ⟨hcond, rfl, rfl, by cases isHead <;> decide⟩
    · rw [hdrop]; simp [scanTrackList, hr13, hk]
    · rw [hdrop]; simpa [scanTrackList] using hacc
  | succ rem ih =>
    intro j k acc st hjrem hk hcap hr1 hr3 hr8 hr9 hr11 hr12 hr13 hr14 hacc hfr
    have hj_lt : j < L.length := by omega
    have hj_ltw : j < 2 ^ w := by omega
    have hj1_ltw : j + 1 < 2 ^ w := by omega
    have hk_ltw : k < 2 ^ w := by omega
    have hdrop_eq : L.drop j = L[j] :: L.drop (j + 1) := List.drop_eq_getElem_cons hj_lt
    have hcond : (Expr.bin .lt (.reg 14) (.reg (if isHead then 9 else 8))).eval w st = some 1 := by
      have hregL : (Expr.reg (if isHead then 9 else 8)).eval w st = some (if isHead then kh else kt) := by
        cases isHead <;> simp [Expr.eval_reg, hr8, hr9]
      rw [show (1 : ℕ) = BinOp.lt.eval j (if isHead then kh else kt) by
        dsimp [BinOp.eval]; rw [ite_eq_left (by omega)]]
      exact Expr.eval_bin (by eval_expr) hregL
        (by dsimp [BinOp.eval]; rw [ite_eq_left (by omega)]; omega)
    set e := L[j]
    have he_ltw : e < 2 ^ w := hL_word e (List.getElem_mem hj_lt)
    have hbj_ltw : baseAddr + j < 2 ^ w := by dsimp [baseAddr]; cases isHead <;> simp at * <;> omega
    have hst_bj : st.mem (baseAddr + j) = e := by
      have hnot : ¬ (scratchBase ≤ baseAddr + j ∧ baseAddr + j < scratchBase + 2 * tM) := by
        rintro ⟨h1, h2⟩; exact hdisj_L j hj_lt (baseAddr + j - scratchBase) (by omega) (by omega)
      exact (hfr _ hnot).trans (hLA0 j hj_lt)
    have heval_base : (Expr.bin .add
        (if isHead then .bin .add (.bin .add (.reg 1) (.const 5)) (.reg 8)
         else .bin .add (.reg 1) (.const 5)) (.reg 14)).eval w st = some (baseAddr + j) := by
      cases isHead <;> dsimp [baseAddr] at hbj_ltw ⊢ <;> eval_expr
    let acc1 : List ℕ :=
      if e < eCap ∧ mem0 (idxBase + e) ≠ 0 then
        acc ++ [if isHead then 2 * (mem0 (idxBase + e) - 1) + 1 else 2 * (mem0 (idxBase + e) - 1)]
      else acc
    have hdrop_scan : scanTrackList mem0 idxBase eCap isHead (L.drop j) =
        (if e < eCap ∧ mem0 (idxBase + e) ≠ 0 then
          [if isHead then 2 * (mem0 (idxBase + e) - 1) + 1 else 2 * (mem0 (idxBase + e) - 1)]
         else []) ++ scanTrackList mem0 idxBase eCap isHead (L.drop (j + 1)) := by
      rw [hdrop_eq]; dsimp [scanTrackList]; rw [List.filterMap_cons]
      split_ifs <;> simp
    have hacc1_app : acc1 ++ scanTrackList mem0 idxBase eCap isHead (L.drop (j + 1)) =
        acc ++ scanTrackList mem0 idxBase eCap isHead (L.drop j) := by
      rw [hdrop_scan]; dsimp [acc1]; split_ifs <;> simp [List.append_assoc]
    have hacc1_len : acc1.length + (scanTrackList mem0 idxBase eCap isHead (L.drop (j + 1))).length =
        acc.length + (scanTrackList mem0 idxBase eCap isHead (L.drop j)).length := by
      have := congrArg List.length hacc1_app; simp only [List.length_append] at this; exact this
    have hbody : ∃ st1 c_b,
        Runs w p ω
          (.assign 15 (.load (.bin .add
              (if isHead then .bin .add (.bin .add (.reg 1) (.const 5)) (.reg 8)
               else .bin .add (.reg 1) (.const 5)) (.reg 14))) ;;
           .cond (.bin .lt (.reg 15) (.reg 3))
             (.assign 16 (.load (.bin .add (.reg 11) (.reg 15))) ;;
              .cond (.reg 16)
                (.store (.bin .add (.reg 12) (.reg 13))
                  (if isHead then .bin .add (.bin .mul (.const 2) (.bin .sub (.reg 16) (.const 1))) (.const 1)
                   else .bin .mul (.const 2) (.bin .sub (.reg 16) (.const 1))) ;;
                 .assign 13 (.bin .add (.reg 13) (.const 1)))
                .nop)
             .nop ;;
           .assign 14 (.bin .add (.reg 14) (.const 1)))
          st .normal st1 c_b ∧
        (∀ r, r ≤ 12 → st1.regs r = st.regs r) ∧
        st1.regs 13 = acc1.length ∧ st1.regs 14 = j + 1 ∧
        ListAt st1.mem scratchBase acc1 ∧
        (∀ a, ¬ (scratchBase ≤ a ∧ a < scratchBase + 2 * tM) → st1.mem a = mem0 a) ∧
        c_b ≤ 50 := by
      suffices h : ∃ o st1 c_b,
          Runs w p ω
            (.assign 15 (.load (.bin .add
                (if isHead then .bin .add (.bin .add (.reg 1) (.const 5)) (.reg 8)
                 else .bin .add (.reg 1) (.const 5)) (.reg 14))) ;;
             .cond (.bin .lt (.reg 15) (.reg 3))
               (.assign 16 (.load (.bin .add (.reg 11) (.reg 15))) ;;
                .cond (.reg 16)
                  (.store (.bin .add (.reg 12) (.reg 13))
                    (if isHead then .bin .add (.bin .mul (.const 2) (.bin .sub (.reg 16) (.const 1))) (.const 1)
                     else .bin .mul (.const 2) (.bin .sub (.reg 16) (.const 1))) ;;
                   .assign 13 (.bin .add (.reg 13) (.const 1)))
                  .nop)
               .nop ;;
             .assign 14 (.bin .add (.reg 14) (.const 1)))
            st o st1 c_b ∧
          (o = .normal ∧ (∀ r, r ≤ 12 → st1.regs r = st.regs r) ∧
            st1.regs 13 = acc1.length ∧ st1.regs 14 = j + 1 ∧
            ListAt st1.mem scratchBase acc1 ∧
            (∀ a, ¬ (scratchBase ≤ a ∧ a < scratchBase + 2 * tM) → st1.mem a = mem0 a)) ∧
          0 + c_b ≤ 50 by
        rcases h with ⟨_, st1, c_b, hr, ⟨rfl, h1, h2, h3, h4, h5⟩, hc⟩
        exact ⟨st1, c_b, hr, h1, h2, h3, h4, h5, by omega⟩
      refine runs_seq_assign_le (v := e) (Expr.eval_load_of_eq heval_base hst_bj) ?_
      by_cases he_cap : e < eCap
      · have hlt_eval : (Expr.bin .lt (.reg 15) (.reg 3)).eval w
            { mem := st.mem, regs := Function.update st.regs 15 e, pos := st.pos } = some 1 := by
          rw [show (1 : ℕ) = BinOp.lt.eval e eCap by dsimp [BinOp.eval]; rw [ite_eq_left he_cap]]
          exact Expr.eval_bin (by eval_expr) (by eval_expr)
            (by dsimp [BinOp.eval]; rw [ite_eq_left he_cap]; omega)
        refine runs_seq_cond_le hlt_eval ?_ (fun h => by omega)
        intro _
        refine runs_seq_assoc_le ?_
        have hidx_st : st.mem (idxBase + e) = mem0 (idxBase + e) := by
          apply hfr; rintro ⟨h1, h2⟩
          exact hdisj_idx e he_cap (idxBase + e - scratchBase) (by omega) (by omega)
        set idx1 := mem0 (idxBase + e)
        have hidx1_le : idx1 ≤ tM := hidx_bd e he_cap
        have hidx1_ltw : idx1 < 2 ^ w := by omega
        refine runs_seq_assign_le (v := idx1) ?_ ?_
        · exact Expr.eval_load_of_eq (by eval_expr) hidx_st
        by_cases hidx0 : idx1 = 0
        · refine runs_seq_cond_le (v := 0) (by rw [hidx0]; eval_expr) (fun h => by omega) ?_
          intro _
          refine runs_seq_nop_le ?_
          refine runs_assign_le (v := j + 1) (by eval_expr) ?_ ?_
          · have hacc1_eq : acc1 = acc := by simp [acc1, he_cap, idx1, hidx0]
            rw [hacc1_eq]
            refine ⟨rfl, fun r hr => ?_, ?_, by simp, hacc, hfr⟩
            · dsimp only
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega)]
            · dsimp only
              rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
                Function.update_of_ne (by decide), hr13, hk]
          · cases isHead <;> simp only [Bool.false_eq_true, ↓reduceIte, Expr.size] <;> omega
        · refine runs_seq_cond_le (v := idx1) (by eval_expr) ?_ (fun h => absurd h hidx0)
          intro _
          refine runs_seq_assoc_le ?_
          have hk_lt_2tM : k < 2 * tM := by
            have h1 : acc1.length = acc.length + 1 := by simp [acc1, he_cap, idx1, hidx0]
            omega
          have hval_ltw : (if isHead then 2 * (idx1 - 1) + 1 else 2 * (idx1 - 1)) < 2 ^ w := by
            cases isHead <;> simp <;> omega
          have heval_tr : (if isHead then Expr.bin .add (.bin .mul (.const 2) (.bin .sub (.reg 16) (.const 1))) (.const 1)
              else Expr.bin .mul (.const 2) (.bin .sub (.reg 16) (.const 1))).eval w
              { mem := st.mem, regs := Function.update (Function.update st.regs 15 e) 16 idx1, pos := st.pos } =
              some (if isHead then 2 * (idx1 - 1) + 1 else 2 * (idx1 - 1)) := by
            cases isHead <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> eval_expr
          refine runs_seq_store_le (by eval_expr) heval_tr ?_
          refine runs_seq_assign_le (v := k + 1) (by eval_expr) ?_
          refine runs_assign_le (v := j + 1) (by eval_expr) ?_ ?_
          · have hacc1_eq : acc1 = acc ++ [if isHead then 2 * (idx1 - 1) + 1 else 2 * (idx1 - 1)] := by
              simp [acc1, he_cap, idx1, hidx0]
            refine ⟨rfl, fun r hr => ?_, ?_, by simp, ?_, fun a ha => ?_⟩
            · dsimp only
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            · dsimp only
              rw [Function.update_of_ne (by decide), Function.update_self, hacc1_eq]; simp [hk]
            · rw [hacc1_eq]; intro q hq
              simp only [List.length_append, List.length_singleton] at hq
              by_cases hqk : q = acc.length
              · subst hqk; dsimp only; rw [hk, Function.update_self]; simp
              · have hq_lt : q < acc.length := by omega
                dsimp only; rw [Function.update_of_ne (by omega), hacc q hq_lt, List.getElem_append_left hq_lt]
            · dsimp only; rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩)]
              exact hfr a ha
          · cases isHead <;> simp only [Bool.false_eq_true, ↓reduceIte, Expr.size] <;> omega
      · have hlt_eval : (Expr.bin .lt (.reg 15) (.reg 3)).eval w
            { mem := st.mem, regs := Function.update st.regs 15 e, pos := st.pos } = some 0 := by
          rw [show (0 : ℕ) = BinOp.lt.eval e eCap by dsimp [BinOp.eval]; rw [ite_eq_right he_cap]]
          exact Expr.eval_bin (by eval_expr) (by eval_expr)
            (by dsimp [BinOp.eval]; rw [ite_eq_right he_cap]; omega)
        refine runs_seq_cond_le hlt_eval (fun h => by omega) ?_
        intro _
        refine runs_seq_nop_le ?_
        refine runs_assign_le (v := j + 1) (by eval_expr) ?_ ?_
        · have hacc1_eq : acc1 = acc := by simp [acc1, he_cap]
          rw [hacc1_eq]
          refine ⟨rfl, fun r hr => ?_, ?_, by simp, hacc, hfr⟩
          · dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          · dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr13, hk]
        · cases isHead <;> simp only [Bool.false_eq_true, ↓reduceIte, Expr.size] <;> omega
    rcases hbody with ⟨st1, c_b, hrun_b, hreg1, hr1_13, hr1_14, hacc1_at, hfr1, hcb⟩
    obtain ⟨st', c_r, hrun_r, hreg', hr'_13, hacc'_at, hfr', hcr⟩ :=
      ih (j + 1) acc1.length acc1 st1 (by omega) rfl (by omega)
        ((hreg1 1 (by decide)).trans hr1) ((hreg1 3 (by decide)).trans hr3)
        ((hreg1 8 (by decide)).trans hr8) ((hreg1 9 (by decide)).trans hr9)
        ((hreg1 11 (by decide)).trans hr11) ((hreg1 12 (by decide)).trans hr12)
        hr1_13 hr1_14 hacc1_at hfr1
    refine ⟨st', 3 + c_b + c_r + 1, ?_, fun r hr => (hreg' r hr).trans (hreg1 r hr),
      hr'_13.trans hacc1_len, hacc1_app ▸ hacc'_at, hfr', by omega⟩
    rw [runs_loop_iff]
    exact Or.inr (Or.inr ⟨1, st1, c_b, c_r, hcond, by decide, hrun_b, hrun_r, by cases isHead <;> rfl⟩)

lemma tBlockSplitSetup_regs_lo {w : ℕ} {p : Program}
    {dgTPtr vCap tag v v' s_v s_v' eCapT : ℕ} {mem₁ : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (hbound : dgTPtr + dynGraphSize vCap eCapT < 2 ^ w)
    (hsv_eq : mem₁ (dgExtToIntBase dgTPtr vCap + v) = s_v)
    (hsv'_eq : mem₁ (dgExtToIntBase dgTPtr vCap + v') = s_v')
    (hv_lt : v < vCap) (hv'_lt : v' < vCap)
    (hsv_lt : s_v < vCap) (hsv'_lt : s_v' < vCap) (_htag_lt : tag < 2 ^ w)
    (hr2 : st.regs 2 = vCap) (hr5 : st.regs 5 = tag) (hr6 : st.regs 6 = v)
    (hr7 : st.regs 7 = v') (hr10 : st.regs 10 = dgTPtr) (hmem : st.mem = mem₁) :
    let mem₂ := if tag = 3 then
      Function.update
        (Function.update
          (Function.update
            (Function.update mem₁ (dgExtToIntBase dgTPtr vCap + v) s_v')
            (dgIntToExtBase dgTPtr vCap + s_v') v)
          (dgExtToIntBase dgTPtr vCap + v') s_v)
        (dgIntToExtBase dgTPtr vCap + s_v) v'
      else mem₁
    ∃ st' c,
      Runs w p ω lsfTBlockSplitSetupStmt st .normal st' c ∧
      (∀ r, r ≤ 13 → st'.regs r = st.regs r) ∧
      st'.regs 16 = s_v ∧ st'.regs 17 = s_v' ∧ st'.mem = mem₂ ∧ c ≤ 75 := by
  intro mem₂
  rcases st with ⟨stm, str, stp⟩
  dsimp only at hr2 hr5 hr6 hr7 hr10 hmem
  subst hmem
  have hbound' : dgTPtr + (4 + 7 * vCap + 9 * eCapT) < 2 ^ w := hbound
  have hlt_gp : dgTPtr < 2 ^ w := by omega
  have hlt_gp4 : dgTPtr + 4 < 2 ^ w := by omega
  have hlt_vc : vCap < 2 ^ w := by omega
  have hlt_3vc : 3 * vCap < 2 ^ w := by omega
  have hlt_4vc : 4 * vCap < 2 ^ w := by omega
  have hlt_eti : dgExtToIntBase dgTPtr vCap < 2 ^ w := by dsimp [dgExtToIntBase]; omega
  have hlt_ite : dgIntToExtBase dgTPtr vCap < 2 ^ w := by dsimp [dgIntToExtBase]; omega
  have hlt_eti_v : dgExtToIntBase dgTPtr vCap + v < 2 ^ w := by dsimp [dgExtToIntBase]; omega
  have hlt_eti_v' : dgExtToIntBase dgTPtr vCap + v' < 2 ^ w := by dsimp [dgExtToIntBase]; omega
  have hlt_ite_sv : dgIntToExtBase dgTPtr vCap + s_v < 2 ^ w := by dsimp [dgIntToExtBase]; omega
  have hlt_ite_sv' : dgIntToExtBase dgTPtr vCap + s_v' < 2 ^ w := by dsimp [dgIntToExtBase]; omega
  have hlt_v : v < 2 ^ w := by omega
  have hlt_v' : v' < 2 ^ w := by omega
  have hlt_sv : s_v < 2 ^ w := by omega
  have hlt_sv' : s_v' < 2 ^ w := by omega
  suffices h : ∃ o st' c,
      Runs w p ω lsfTBlockSplitSetupStmt { mem := stm, regs := str, pos := stp } o st' c ∧
      (o = .normal ∧ (∀ r, r ≤ 13 → st'.regs r = str r) ∧
        st'.regs 16 = s_v ∧ st'.regs 17 = s_v' ∧ st'.mem = mem₂) ∧
      0 + c ≤ 75 by
    rcases h with ⟨_, st', c, hr, ⟨rfl, h1, h2, h3, h4⟩, hc⟩
    exact ⟨st', c, hr, h1, h2, h3, h4, by omega⟩
  dsimp only [lsfTBlockSplitSetupStmt]
  refine runs_seq_assign_le (v := dgExtToIntBase dgTPtr vCap) (by dsimp [dgExtToIntBase]; eval_expr) ?_
  refine runs_seq_assign_le (v := dgIntToExtBase dgTPtr vCap) (by dsimp [dgIntToExtBase]; eval_expr) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := s_v) (by eval_expr) hsv_eq) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := s_v') (by eval_expr) hsv'_eq) ?_
  have hlo : ∀ r ≤ 13,
      Function.update (Function.update (Function.update (Function.update str
        14 (dgExtToIntBase dgTPtr vCap)) 15 (dgIntToExtBase dgTPtr vCap)) 16 s_v) 17 s_v' r = str r := by
    intro r hr
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine WordRAM.runs_cond_le (v := if tag = 3 then 1 else 0) (by eval_expr) ?_ ?_
  · intro hne3
    have htag3 : tag = 3 := by by_contra hc; simp [hc] at hne3
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    refine runs_store_le (by eval_expr) (by eval_expr)
      ⟨rfl, hlo, by simp, by simp, by simp [mem₂, htag3]⟩ ?_
    dsimp only [Expr.size]; omega
  · intro he3
    have htag_ne : tag ≠ 3 := fun hc => by simp [hc] at he3
    refine runs_nop_le ⟨rfl, hlo, by simp, by simp, by simp [mem₂, htag_ne]⟩ ?_
    dsimp only [Expr.size]; omega

end

end MinCostFlow.LSF.Program
