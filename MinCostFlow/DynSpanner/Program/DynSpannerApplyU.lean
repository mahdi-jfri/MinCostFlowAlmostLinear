module

public import MinCostFlow.DynSpanner.Program.DynSpannerLevelsDelete
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
import WordRAM.Tactic

/-!
# Applying the update `u` to the state

The first part of `step` applies the update `u` (a deletion or a split) to `G`, to `H` and to
each level. The levels are not stored as graphs: they are kept through the words `minH` and the
buckets (see `StateLayout.lean`). For a deletion or a split, a level loses exactly the edges that
`G` loses (`applyBatch_restrict_E_inter` in `DynSpannerStepMid.lean`). So only a deletion changes
the buckets, and it only has to take the deleted edge out of its bucket.

`dsApplyUStmt` does this in three calls:
1. `dgApplyUpdateStmt` on `H` with `allowInsert = 0`, which applies `restrictUpdate u H`;
2. `dgApplyUpdateStmt` on `G` with `allowInsert = 1`, which applies `u`;
3. for a deletion (tag `1`), `dsLevelsDeleteStmt` on the deleted edge.

`dsApplyU_meetsContract` proves its contract, with cost `1280 · len + 300` for an update record of
`len` words.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args = [gPtr, hPtr, b, minHBase, updPtr]`. -/
def dsApplyUStmt (bBatch bD : ℕ) : Stmt :=
  .call 5 (bBatch + dgIdxApplyUpdate) [.reg 1, .reg 4, .const 0] ;;
  .call 5 (bBatch + dgIdxApplyUpdate) [.reg 0, .reg 4, .const 1] ;;
  .cond (.bin .eq (.load (.reg 4)) (.const 1))
    (.call 5 (bD + levelsDeleteIdx) [.reg 2, .reg 3, .load (.bin .add (.reg 4) (.const 1))])
    .nop ;;
  .ret (.const 0)

def applyUProcs (bBatch bD : ℕ) : List Stmt := [dsApplyUStmt bBatch bD]

def applyUIdx : ℕ := 0

lemma applyUProcs_noRand (bBatch bD : ℕ) : ∀ s ∈ applyUProcs bBatch bD, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The bucket lists after the update: a deletion of `e` erases `e`, a split changes nothing. -/
def delErase : Update → List ℕ → List ℕ
  | .delete e, l => l.erase e
  | _, l => l

/-- The word `minH[e']` after the update, from the old word `old`. -/
def minHAfter : Update → ℕ → ℕ → ℕ
  | .delete e, old, e' => if e' = e then 0 else old
  | _, old, _ => old

/-- Contract of `dsApplyUStmt` for the update `u` of `G`, stored in `len` words. -/
def dsApplyUContract (w L vCap eCap b : ℕ) (G H : MGraph) (u : Update) (len : ℕ)
    (B : ℕ → List ℕ) : Contract where
  pre args mem := ∃ updPtr,
    args = [dsGPtr b, dsHPtr b vCap eCap, b, dsMinHBase b vCap eCap, updPtr] ∧
    16 ≤ 2 ^ w ∧ b + dsFixedSize L vCap eCap < 2 ^ w ∧ updPtr + len < 2 ^ w ∧
    (∀ i < len, updPtr + i < dsGPtr b ∨ b + dsFixedSize L vCap eCap ≤ updPtr + i) ∧
    (∀ i < len, mem (updPtr + i) < 2 ^ w) ∧
    UpdateAt mem updPtr G u len ∧ G.UpdateIsValid u ∧ UpdateWithinCaps vCap eCap u ∧
    isDelOrSplit u ∧ (∀ e ∈ G.E, e < eCap) ∧
    DynGraphAt mem (dsGPtr b) vCap eCap G ∧ DynGraphAt mem (dsHPtr b vCap eCap) vCap eCap H ∧
    G.IsSubgraph H ∧ H.V = G.V ∧
    mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
    BucketsAt mem L vCap eCap b B ∧
    (∀ i ≤ L, ∀ i' ≤ L, i ≠ i' → ∀ x ∈ B i, x ∉ B i') ∧
    (∀ e < eCap, mem (dsMinHBase b vCap eCap + e) = 0 → ∀ i ≤ L, e ∉ B i) ∧
    (∀ e < eCap, ∀ i, mem (dsMinHBase b vCap eCap + e) = i + 1 → i ≤ L ∧ e ∈ B i)
  post _ mem _ mem' :=
    DynGraphAt mem' (dsGPtr b) vCap eCap (G.applyUpdate u) ∧
    DynGraphAt mem' (dsHPtr b vCap eCap) vCap eCap (H.applyBatch (restrictUpdate u H)) ∧
    BucketsAt mem' L vCap eCap b (fun i => delErase u (B i)) ∧
    (∀ e' < eCap, mem' (dsMinHBase b vCap eCap + e') =
      minHAfter u (mem (dsMinHBase b vCap eCap + e')) e') ∧
    ∀ addr, (addr < dsGPtr b ∨
        (dsAuxPtr b vCap eCap ≤ addr ∧ addr < dsMinHBase b vCap eCap) ∨
        dsDomGenBase b L vCap eCap ≤ addr) → mem' addr = mem addr
  cost _ _ := 1280 * len + 300

end

lemma BucketsAt.of_agree {mem mem' : ℕ → ℕ} {L vCap eCap b : ℕ} {B : ℕ → List ℕ}
    (hB : BucketsAt mem L vCap eCap b B)
    (hagree : ∀ addr, dsMinHBase b vCap eCap ≤ addr → mem' addr = mem addr) :
    BucketsAt mem' L vCap eCap b B := by
  intro i hi
  obtain ⟨hdll, hdeg⟩ := hB i hi
  have hn : dsHNextBase b vCap eCap = dsMinHBase b vCap eCap + eCap := rfl
  have hp : dsHPrevBase b vCap eCap = dsHNextBase b vCap eCap + eCap := rfl
  have hh : dsHHeadBase b vCap eCap = dsHPrevBase b vCap eCap + eCap := rfl
  have hd : dsHDegDummyBase b L vCap eCap = dsHHeadBase b vCap eCap + (L + 1) := rfl
  refine ⟨hdll.of_agree (hagree _ (by omega)) (fun x _ => hagree _ (by omega))
    (fun x _ => hagree _ (by omega)), ?_⟩
  rw [hagree _ (by omega)]
  exact hdeg

private lemma domGen_le' (b L vCap eCap : ℕ) :
    dsDomGenBase b L vCap eCap ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase, dsVStampBase, dsSBitBase,
    dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase, dsRevGenBase, dsPiPtrBase,
    dsEdgeDomGenBase]
  omega

public section

/-- `dsApplyUStmt` meets `dsApplyUContract`. -/
theorem dsApplyU_meetsContract {w L vCap eCap b : ℕ} {G H : MGraph} {u : Update} {len : ℕ}
    {B : ℕ → List ℕ} {p : Program} {bU bD bPhase bOps bEdge bSplit bBatch : ℕ}
    (hpB : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpSplit : p.HasAt bSplit (dgSplitProcs bOps bSplit))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpP : p.HasAt bPhase (phaseProcs bOps bEdge))
    (hpD : p.HasAt bD (levelsDeleteProcs bPhase))
    (hpU : p.HasAt bU (applyUProcs bBatch bD)) :
    MeetsContract w p (bU + applyUIdx) (dsApplyUContract w L vCap eCap b G H u len B) := by
  refine meetsContract_of_runs
    (hpU.get (i := applyUIdx) (by simp [applyUProcs, applyUIdx])) ?_
  rintro args mem pos ω _ ⟨updPtr, rfl, hw16, hbound, hubound, hudisj, huwords, hu_at, hvalid,
    hcaps, hds, heC, hG, hH, hsub, hHV, hL, hvC, heCw, hB, hdisj, hzero, hsome⟩
  simp only [applyUProcs, applyUIdx, List.getElem_cons_zero]
  dsimp only [dsApplyUStmt]
  have hdom := domGen_le' b L vCap eCap
  have hdom_eq := dsDomGenBase_eq b L vCap eCap
  have hHp : dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap := rfl
  have hAp : dsAuxPtr b vCap eCap = dsHPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hMp : dsMinHBase b vCap eCap = dsAuxPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hGp : dsGPtr b = b + dsHdrSize := rfl
  have hlen0 : dgUpdateMemLen mem updPtr = len := dgUpdateMemLen_eq hu_at
  -- The update words lie outside both graphs.
  have hud_H : ∀ i < len, updPtr + i < dsHPtr b vCap eCap ∨
      dsHPtr b vCap eCap + dynGraphSize vCap eCap ≤ updPtr + i := fun i hi => by
    rcases hudisj i hi with h | h <;> [left; right] <;> omega
  have hud_G : ∀ i < len, updPtr + i < dsGPtr b ∨
      dsGPtr b + dynGraphSize vCap eCap ≤ updPtr + i := fun i hi => by
    rcases hudisj i hi with h | h <;> [left; right] <;> omega
  refine runs_start_le ?_
  -- Call 1: `H`.
  refine runs_seq_call_le (dgApplyUpdate_meetsContract (w := w) (vCap := vCap) (eCap := eCap)
      (G := G) (H := H) (u := u) (len := len) hpB hpEdge hpSplit hpOps)
    (by eval_expr)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl|rfl) <;> omega)
    ⟨dsHPtr b vCap eCap, updPtr, 0, rfl, hw16, by omega, hubound, hud_H, huwords, hu_at, hvalid,
      hcaps, hH, Or.inr ⟨rfl, hsub, hHV⟩⟩ ?_
  rintro r₁ mem₁ pos₁ ⟨_, _, _, hEq₁, _, hH₁, hfr₁⟩
  simp only [List.cons.injEq, and_true] at hEq₁
  obtain ⟨h1, h2, h3⟩ := hEq₁
  subst h1 h2 h3
  have hfr₁' : ∀ addr, addr < dsHPtr b vCap eCap ∨ dsAuxPtr b vCap eCap ≤ addr →
      mem₁ addr = mem addr := fun addr h => hfr₁ addr (by omega)
  have hu_at₁ : UpdateAt mem₁ updPtr G u len :=
    hu_at.of_agree fun i hi => hfr₁ _ (hud_H i hi)
  have hlen₁ : dgUpdateMemLen mem₁ updPtr = len := dgUpdateMemLen_eq hu_at₁
  have hG₁ : DynGraphAt mem₁ (dsGPtr b) vCap eCap G :=
    dynGraphAt_of_agree hG fun addr _ h2 => hfr₁' addr (Or.inl (by omega))
  -- Call 2: `G`.
  refine runs_seq_call_le (dgApplyUpdate_meetsContract (w := w) (vCap := vCap) (eCap := eCap)
      (G := G) (H := G) (u := u) (len := len) hpB hpEdge hpSplit hpOps)
    (by eval_expr)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl|rfl) <;> omega)
    ⟨dsGPtr b, updPtr, 1, rfl, hw16, by omega, hubound, hud_G,
      fun i hi => by show mem₁ (updPtr + i) < 2 ^ w; rw [hfr₁ _ (hud_H i hi)]; exact huwords i hi, hu_at₁, hvalid,
      hcaps, hG₁, Or.inl ⟨one_ne_zero, rfl⟩⟩ ?_
  rintro r₂ mem₂ pos₂ ⟨_, _, _, hEq₂, _, hG₂, hfr₂⟩
  simp only [List.cons.injEq, and_true] at hEq₂
  obtain ⟨h1, h2, h3⟩ := hEq₂
  subst h1 h2 h3
  have hfr₂' : ∀ addr, addr < dsGPtr b ∨ dsHPtr b vCap eCap ≤ addr →
      mem₂ addr = mem₁ addr := fun addr h => hfr₂ addr (by omega)
  -- Everything outside the two graphs is unchanged.
  have hout : ∀ addr, addr < dsGPtr b ∨ dsAuxPtr b vCap eCap ≤ addr → mem₂ addr = mem addr :=
    fun addr h => (hfr₂' addr (by omega)).trans (hfr₁' addr (by omega))
  have hG₂' : DynGraphAt mem₂ (dsGPtr b) vCap eCap (G.applyUpdate u) := by
    simpa [dgBatchTarget] using hG₂
  have hH₂ : DynGraphAt mem₂ (dsHPtr b vCap eCap) vCap eCap (H.applyBatch (restrictUpdate u H)) := by
    have := dynGraphAt_of_agree hH₁ fun addr h1 _ => hfr₂' addr (Or.inr h1)
    simpa [dgBatchTarget] using this
  have hB₂ : BucketsAt mem₂ L vCap eCap b B :=
    hB.of_agree fun addr h => hout addr (Or.inr (by omega))
  have hminw : ∀ e' < eCap, mem₂ (dsMinHBase b vCap eCap + e') = mem (dsMinHBase b vCap eCap + e') :=
    fun e' _ => hout _ (Or.inr (by omega))
  have hupd : ∀ i < len, mem₂ (updPtr + i) = mem (updPtr + i) := fun i hi =>
    (hfr₂ _ (hud_G i hi)).trans (hfr₁ _ (hud_H i hi))
  have hhdr : ∀ k < dsHdrSize, mem₂ (b + k) = mem (b + k) := fun k hk =>
    hout _ (Or.inl (by omega))
  have hw0 : w ≠ 0 := by rintro rfl; omega
  cases u with
  | insert _ _ _ => exact absurd hds (by simp [isDelOrSplit])
  | delete e =>
    obtain ⟨hlen2, hLA⟩ := hu_at
    have ht0 : mem updPtr = 1 := by simpa using hLA 0 (by simp)
    have ht1 : mem (updPtr + 1) = e := by simpa using hLA 1 (by simp)
    have ht0' : mem₂ updPtr = 1 := by rw [← ht0]; simpa using hupd 0 (by omega)
    have ht1' : mem₂ (updPtr + 1) = e := by rw [← ht1]; exact hupd 1 (by omega)
    have heE : e ∈ G.E := hvalid
    have he_lt : e < eCap := heC e heE
    refine runs_seq_cond_le (v := 1)
      (by simp [Expr.eval, BinOp.eval, startState, ht0', hw0]) (fun _ => ?_) (fun h => absurd h one_ne_zero)
    refine runs_seq_call_le (dsLevelsDelete_meetsContract (w := w) (L := L) (vCap := vCap)
        (eCap := eCap) (b := b) (B := B) (e := e) hpP hpOps hpD)
      (by
        simp only [evalArgs, Expr.eval, BinOp.eval, Function.update_of_ne (show (2 : ℕ) ≠ 5 by omega),
          Function.update_of_ne (show (3 : ℕ) ≠ 5 by omega),
          Function.update_of_ne (show (4 : ℕ) ≠ 5 by omega)]
        simp [startState, ht1', show updPtr + 1 < 2 ^ w by omega,
          show (1 : ℕ) < 2 ^ w by omega])
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro z (rfl|rfl|rfl) <;> omega)
      ⟨rfl, hw16, hbound, he_lt, (hhdr dsLOff (by decide)).trans hL,
        (hhdr dsVCapOff (by decide)).trans hvC, (hhdr dsECapOff (by decide)).trans heCw, hB₂,
        hdisj, fun h => hzero e he_lt (by rw [← hminw e he_lt]; exact h),
        fun i h => hsome e he_lt i (by rw [← hminw e he_lt]; exact h)⟩ ?_
    rintro r₃ mem₃ pos₃ ⟨hm0, hB₃, hmfr, hfr₃⟩
    refine runs_ret_le (v := 0) (Expr.eval_const (by omega))
      ⟨dynGraphAt_of_agree hG₂' fun addr _ h2 => hfr₃ addr (Or.inl (by omega)),
        dynGraphAt_of_agree hH₂ fun addr _ h2 => hfr₃ addr (Or.inl (by omega)),
        hB₃, fun e' he' => ?_, fun addr h => ?_⟩ ?_
    · by_cases hee : e' = e
      · subst hee; simp [minHAfter, hm0]
      · simp only [minHAfter, hee, ite_false]
        exact (hmfr e' he' hee).trans (hminw e' he')
    · show mem₃ addr = _
      rw [hfr₃ addr (by omega)]
      exact hout addr (by omega)
    · simp [dgApplyUpdateContract, dsLevelsDeleteContract, dsApplyUContract, startState, hlen0,
        hlen₁, Expr.size, argsSize]
      omega
  | split v v' St Sh =>
    have ht0 : mem updPtr = 2 ∨ mem updPtr = 3 := by
      rcases hu_at with ⟨Lt, Lh, -, -, -, -, -, hLA⟩ | ⟨Lt, Lh, -, -, -, -, -, hLA⟩
      · left; simpa using hLA 0 (by simp)
      · right; simpa using hLA 0 (by simp)
    have hlen_pos : 0 < len := by
      rcases hu_at with ⟨Lt, Lh, -, -, -, -, h, -⟩ | ⟨Lt, Lh, -, -, -, -, h, -⟩ <;> omega
    have ht0' : mem₂ updPtr = mem updPtr := by simpa using hupd 0 hlen_pos
    refine runs_seq_cond_le (v := 0)
      (by rcases ht0 with h | h <;> simp [Expr.eval, BinOp.eval, startState, ht0', h, hw0])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine runs_seq_nop_le (runs_ret_le (v := 0) (Expr.eval_const (by omega))
      ⟨hG₂', hH₂, hB₂, fun e' he' => by simpa [minHAfter] using hminw e' he',
        fun addr h => hout addr (by omega)⟩ ?_)
    simp [dgApplyUpdateContract, dsApplyUContract, startState, hlen0, hlen₁, Expr.size, argsSize]
    omega

end

end MinCostFlow.DynSpanner.Program
