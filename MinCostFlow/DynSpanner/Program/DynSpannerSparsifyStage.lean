module

public import MinCostFlow.DynSpanner.Program.SparsifyHost
public import MinCostFlow.DynSpanner.Program.DynSpannerShortcut
public import MinCostFlow.DynSpanner.Program.DynSpannerShortcutBridge
import WordRAM.Tactic

/-!
# The `Sparsify` stage: sparsify `J`, then shortcut the output walks

`dsSparsifyStageStmt` calls `sparsifyDynStmt` on `J` and then `dsShortcutEmbStmt`, which
shortcuts every output walk `out.emb e` (`e ∈ E(J)`) in the graph `J` itself. By
`canonicalSparsify_ends` and `shortcutWalk_congr_ends` this gives the walks
`shortcutWalk J̃ (J.tail e) (out.emb e)` of `step`. The shortcut reads the table of output walks
that `sparsifyDynStmt` wrote and puts its walks in the heap after the output of `sparsifyDynStmt`.
The post names the memory `mid` between the two calls (`dsSparsifyStage_meetsContract`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-- `args = [hPtr, jPtr, mEmbPtr, vCapOut, eCapOut, scratchPtr, guestBase, b, eListPtr, eLen]`;
returns the end of the heap used. -/
def dsSparsifyStageStmt (bSp bLW : ℕ) : Stmt :=
  .call 10 (bSp + gtIdxSparsifyDyn) [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6] ;;
  .assign 11 (.load (.bin .add (.reg 5) (.const 1))) ;;
  .call 12 (bLW + lwIdxShortcutEmb) [.reg 7, .reg 1, .reg 8, .reg 9, .reg 11, .reg 10] ;;
  .ret (.reg 12)

def sparsifyStageProcs (bSp bLW : ℕ) : List Stmt := [dsSparsifyStageStmt bSp bLW]

def sparsifyStageIdx : ℕ := 0

lemma sparsifyStageProcs_noRand (bSp bLW : ℕ) : ∀ s ∈ sparsifyStageProcs bSp bLW, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-- The bound on the end of the output of `sparsifyDynStmt` (from its post). -/
noncomputable def spOutBound (impl : SparsifyImpl) (mMax vCapOut eCapOut guestBase : ℕ)
    (H' J : MGraph) (emb : MinCostFlow.Embedding) : ℕ :=
  guestBase + 2 ^ (wordSize impl.cw (canonSparsifyInput H' J emb) + 1) + 2 +
    3 * J.m + dynGraphSize vCapOut eCapOut + eCapOut + J.m * (1 + 2 * Nat.ceil (impl.γ_ℓ mMax))

/-- Contract of `dsSparsifyStageStmt` for the list `eL` of the edges of `J`. -/
noncomputable def dsSparsifyStageContract (impl : SparsifyImpl) (mMax : ℕ)
    (w vCapH eCapH vCapJ eCapJ vCapOut eCapOut L vCap eCap b : ℕ)
    (H' J : MGraph) (emb : MinCostFlow.Embedding) (eL : List ℕ) : Contract where
  pre args mem := ∃ hPtr jPtr mEmbPtr scratchPtr guestBase eListPtr,
    args = [hPtr, jPtr, mEmbPtr, vCapOut, eCapOut, scratchPtr, guestBase, b, eListPtr,
      eL.length] ∧
    (sparsifyDynContract impl mMax w vCapH eCapH vCapJ eCapJ vCapOut eCapOut H' J emb).pre
      [hPtr, jPtr, mEmbPtr, vCapOut, eCapOut, scratchPtr, guestBase] mem ∧
    1 ≤ b ∧ b + dsFixedSize L vCap eCap ≤ scratchPtr ∧
    eListPtr + eL.length ≤ scratchPtr ∧
    spOutBound impl mMax vCapOut eCapOut guestBase H' J emb +
      dsShortcutHeapSpace eL (canonicalSparsify impl H' J emb).emb < 2 ^ w ∧
    mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
    mem (b + dsGenOff) + 1 < 2 ^ w ∧
    (∀ v < vCap, mem (dsVStampBase b L vCap eCap + v) ≤ mem (b + dsGenOff)) ∧
    (jPtr + dynGraphSize vCapJ eCapJ ≤ dsVStampBase b L vCap eCap ∨
      dsVStampBase b L vCap eCap + vCap ≤ jPtr) ∧
    (eListPtr + eL.length ≤ dsVStampBase b L vCap eCap ∨
      dsVStampBase b L vCap eCap + vCap ≤ eListPtr) ∧
    eL.Nodup ∧ (∀ e, e ∈ eL ↔ e ∈ J.E) ∧ ListAt mem eListPtr eL ∧
    J.IsValid ∧ (∀ v ∈ J.V, v < vCap) ∧
    (∀ e ∈ J.E, J.IsWalk (J.tail e) (J.head e) ((canonicalSparsify impl H' J emb).emb e))
  post args mem ret mem' := ∃ mid r₁,
    (sparsifyDynContract impl mMax w vCapH eCapH vCapJ eCapJ vCapOut eCapOut H' J emb).post
      (args.take 7) mem r₁ mid ∧
    (dsShortcutEmbContract w L vCap eCap b vCapJ eCapJ eCapOut J eL
      (canonicalSparsify impl H' J emb).emb).post
      [b, args.getD 1 0, args.getD 8 0, eL.length, mid (args.getD 5 0 + 1), r₁] mid ret mem'
  cost _ _ :=
    (sparsifyDynContract impl mMax w vCapH eCapH vCapJ eCapJ vCapOut eCapOut H' J emb).cost [] 0 +
    400 * (eL.map fun e => ((canonicalSparsify impl H' J emb).emb e).length).sum +
    300 * eL.length + 1000

end

private lemma vStamp_le_fix (b L vCap eCap : ℕ) :
    dsVStampBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap := by
  rw [← dsFixedSize_add]
  simp only [dsMEmbTempBase, dsKeptStampBase, dsEStampBase]
  omega

public section

/-- `dsSparsifyStageStmt` meets `dsSparsifyStageContract`. -/
theorem dsSparsifyStage_meetsContract (impl : SparsifyImpl) (mMax : ℕ)
    {w vCapH eCapH vCapJ eCapJ vCapOut eCapOut L vCap eCap b : ℕ}
    {H' J : MGraph} {emb : MinCostFlow.Embedding} {eL : List ℕ}
    {p : Program}
    {bSort bOps bEdge bSplit bBatch bFwd bRevPrim bGT bRevCore bRevDyn bEmit bGuest bSpDyn
      bLW bRev bSS : ℕ}
    (hpSpDyn : p.HasAt bSpDyn (sparsifyDynProcs impl.program.regBound impl.cw bFwd bRevDyn bGuest))
    (hpGuest : p.HasAt bGuest (sparsifyGuestProcs impl bGuest))
    (hpFwd : p.HasAt bFwd (gtForwardProcs bOps bGT bEmit bFwd))
    (hpEmit : p.HasAt bEmit (gtEmitProcs bSort bOps bGT))
    (hpRevDyn : p.HasAt bRevDyn (gtRevDynProcs bOps bGT bRevCore))
    (hpRevCore : p.HasAt bRevCore (gtRevCoreProcs bBatch bRevPrim))
    (hpRevPrim : p.HasAt bRevPrim gtRevPrimProcs)
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort))
    (hpLW : p.HasAt bLW (levelWalkProcs bOps bRev))
    (hpSS : p.HasAt bSS (sparsifyStageProcs bSpDyn bLW)) :
    MeetsContract w p (bSS + sparsifyStageIdx)
      (dsSparsifyStageContract impl mMax w vCapH eCapH vCapJ eCapJ vCapOut eCapOut L vCap eCap b
        H' J emb eL) := by
  refine meetsContract_of_runs
    (hpSS.get (i := sparsifyStageIdx) (by simp [sparsifyStageProcs, sparsifyStageIdx])) ?_
  rintro args mem pos ω hW ⟨hPtr, jPtr, mEmbPtr, scratchPtr, guestBase, eListPtr, rfl, hpreS,
    hb1, hbS, heS, hbound, hmL, hmV, hmE, hgen, hvst, hJv, hEv, hnd, hiffE, hEL, hJval, hJV,
    hJwalk⟩
  simp only [sparsifyStageProcs, sparsifyStageIdx, List.getElem_cons_zero]
  dsimp only [dsSparsifyStageStmt]
  have hpreS' := hpreS
  obtain ⟨hPtr', jPtr', mEmbPtr', scratchPtr', guestBase', hargsS, hw16, hJn1, hvCap_ltw,
    heCap_ltw, hgB1, hw'_le, hMemBnd, hH_ltgb, hJ_ltgb, hME_ltgb, hScr_le_gb,
    hdisjH, hdisjJ, hdisjME, hdisjW, hzMem, hDynH, hDynJ, hemb, hmEmb,
    hJm_le, hLen_pos, hvOut_cap, heOut_cap, hWalks_ltgb⟩ := hpreS'
  simp only [List.cons.injEq, and_true] at hargsS
  obtain ⟨rfl, rfl, rfl, -, -, rfl, rfl⟩ := hargsS
  have hfixpos := dsFixedSize_pos L vCap eCap
  have hvsf := vStamp_le_fix b L vCap eCap
  have hpw : 1 ≤ 2 ^ (wordSize impl.cw (canonSparsifyInput H' J emb) + 1) := Nat.one_le_two_pow
  simp only [spOutBound] at hbound
  refine runs_start_le ?_
  -- Call 1: `Sparsify`.
  refine runs_seq_call_le (vs := [hPtr, jPtr, mEmbPtr, vCapOut, eCapOut, scratchPtr, guestBase])
    (sparsifyDyn_meetsContract impl mMax (w := w) (vCapH := vCapH) (eCapH := eCapH)
      (vCapJ := vCapJ) (eCapJ := eCapJ) (vCapOut := vCapOut) (eCapOut := eCapOut)
      (H' := H') (J := J) (emb := emb)
      hpSpDyn hpGuest hpFwd hpEmit hpRevDyn hpRevCore hpRevPrim hpBatch hpEdge hpOps hpGT hpSort)
    (by eval_expr)
    (fun v hv => hW v (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; omega))
    hpreS ?_
  rintro r₁ mem₁ pos₁ hpost₁
  have hpost₁' := hpost₁
  obtain ⟨hPtr₂, jPtr₂, mE₂, scr₂, gB₂, hargs₁, hgle, hjt, hmEO, hr₁lt, hr₁le, hJt, hMEB, hEOle,
    hZ, hfr₁⟩ := hpost₁'
  simp only [List.cons.injEq, and_true] at hargs₁
  obtain ⟨rfl, rfl, rfl, -, -, rfl, rfl⟩ := hargs₁
  have hkeep : ∀ addr, addr < scratchPtr → mem₁ addr = mem addr := fun addr h =>
    hfr₁ addr (Or.inl h) (by omega)
  set mEO := mem₁ (scratchPtr + 1) with hmEOdef
  -- The pointer to the table of output walks.
  refine runs_seq_assign_le (v := mEO)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_const (by omega)) (by omega)) rfl) ?_
  -- Call 2: the shortcut, in `J`.
  refine runs_seq_call_le (vs := [b, jPtr, eListPtr, eL.length, mEO, r₁])
    (dsShortcutEmb_meetsContract (w := w) (L := L) (vCap := vCap) (eCap := eCap) (b := b)
      (vCapG := vCapJ) (eCapG := eCapJ) (eCapEmb := eCapOut) (G := J) (eL := eL)
      (emb := (canonicalSparsify impl H' J emb).emb) hpLW hpOps)
    (by
      simp only [evalArgs, Expr.eval]
      simp [startState])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro z (rfl|rfl|rfl|rfl|rfl|rfl)
      · exact hW _ (by simp)
      · exact hW _ (by simp)
      · omega
      · omega
      · omega
      · omega)
    ⟨jPtr, eListPtr, mEO, r₁, rfl, hw16, hb1, by omega, by omega, by omega, by omega, by omega,
      (hkeep (b + dsLOff) (by simp only [dsLOff]; omega)).trans hmL,
      (hkeep (b + dsVCapOff) (by simp only [dsVCapOff]; omega)).trans hmV,
      (hkeep (b + dsECapOff) (by simp only [dsECapOff]; omega)).trans hmE,
      by
        have h2 := hkeep (b + dsGenOff) (by simp only [dsGenOff]; omega)
        show mem₁ _ + 1 < _
        rw [h2]; exact hgen,
      fun e he => ⟨fun v hv => by omega, Or.inl (by omega)⟩,
      fun v hv => by
        have h1 := hkeep (dsVStampBase b L vCap eCap + v) (by omega)
        have h2 := hkeep (b + dsGenOff) (by simp only [dsGenOff]; omega)
        show mem₁ _ ≤ mem₁ _
        rw [h1, h2]; exact hvst v hv,
      fun i hi => ⟨fun v hv => by omega, fun e he => by omega, Or.inl (by omega)⟩,
      fun k hk => ⟨fun v hv => by omega, fun e he => by omega, Or.inl (by omega)⟩,
      hnd, hEL.congr fun k h1 h2 => hkeep k (by omega),
      dynGraphAt_of_agree hDynJ fun addr h1 h2 => by
        have := hdisjJ (addr - jPtr) (by omega)
        rw [show jPtr + (addr - jPtr) = addr by omega] at this
        exact hfr₁ addr this (by omega),
      hJval, hJV, fun e he => ?_⟩ ?_
  · have heJ := (hiffE e).mp he
    obtain ⟨heC, hlo, hhi, hwalk⟩ := hMEB.2.2 e heJ
    have hge := hEOle e heJ
    rw [mWalkEncode_length] at hhi
    refine ⟨heJ, heC, hJwalk e heJ, hwalk, ?_, fun addr h1 h2 => ?_⟩
    · show mem₁ (mEO + e) + 1 + 2 * _ < 2 ^ w
      omega
    · dsimp only at h1 h2
      exact ⟨fun v hv => by omega, fun e' he' => by omega, Or.inl (by omega)⟩
  rintro r₂ mem₂ pos₂ hpost₂
  refine runs_ret_le (v := r₂) (Expr.eval_reg_of_eq (by simp)) ⟨mem₁, r₁, hpost₁, hpost₂⟩ ?_
  have hc : ∀ (a : List ℕ) (m : ℕ → ℕ),
      (sparsifyDynContract impl mMax w vCapH eCapH vCapJ eCapJ vCapOut eCapOut H' J emb).cost a m =
      (sparsifyDynContract impl mMax w vCapH eCapH vCapJ eCapJ vCapOut eCapOut H' J emb).cost
        [] 0 := fun _ _ => rfl
  simp only [Expr.size, argsSize, dsSparsifyStageContract, dsShortcutEmbContract]
  rw [hc]
  omega

end

end MinCostFlow.DynSpanner.Program
