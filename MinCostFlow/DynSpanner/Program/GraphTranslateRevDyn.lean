module

public import MinCostFlow.DynSpanner.Program.GraphTranslateRevCore
public import MinCostFlow.DynSpanner.Program.GraphTranslateHelpers
import WordRAM.Tactic

/-!
# Dynamic Reverse Graph Translation (`GraphTranslateRevDyn`)

Completes reverse graph translation from a dynamic handle `DynGraphAt J` and a canonical relocated
`Sparsify` output `SparsifyOutRelocAt`:
* `gtReverseDynStmt` (`gtIdxReverseDyn = 0` in `gtRevDynProcs`): extracts sorted `(jVs, jEs,
  jTails, jHeads)` from `DynGraphAt J` into scratch via `gtForwardDynPrepStmt` without mutating
  `J`, then calls `gtReverseCoreStmt` to populate `DynGraphAt (outJtilde J kept)` and
  `MEmbAt (citedEmbToMGraph J cJtilde kept embJJtilde)`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

@[expose] public section

def gtIdxReverseDyn : ℕ := 0

/-- Scratch word budget required by `gtReverseDynStmt`. -/
def gtRevDynScratchLen (nJ mJ : ℕ) : ℕ :=
  8 + 3 * nJ + 6 * mJ

/-- Save extra arguments `[guestBase, spOutG, vCap, eCap, triplesBufPtr, jtildeDynPtr,
mEmbOutPtr, walkBufPtr]` at `[scratchPtr .. scratchPtr + 7]` and set up registers for
`gtForwardDynPrepStmt`. -/
def gtRevSaveAndSetStmt : Stmt :=
  .store (.reg 5) (.reg 1) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.reg 2) ;;
  .store (.bin .add (.reg 5) (.const 2)) (.reg 3) ;;
  .store (.bin .add (.reg 5) (.const 3)) (.reg 4) ;;
  .store (.bin .add (.reg 5) (.const 4)) (.reg 6) ;;
  .store (.bin .add (.reg 5) (.const 5)) (.reg 7) ;;
  .store (.bin .add (.reg 5) (.const 6)) (.reg 8) ;;
  .store (.bin .add (.reg 5) (.const 7)) (.reg 9) ;;
  .assign 1 (.reg 0) ;;
  .assign 3 (.bin .add (.reg 5) (.const 8)) ;;
  .assign 0 (.const 0) ;;
  .assign 2 (.const 0) ;;
  .assign 4 (.const 0)

/-- Dynamic reverse graph translator:
`[jPtr, guestBase, spOutG, vCap, eCap, scratchPtr, triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr]`.
Returns end of written `walkBuf` (`walkBufPtr + citedDecPrefLen ...`). -/
def gtReverseDynStmt (bOps bGT bRevCore : ℕ) : Stmt :=
  gtRevSaveAndSetStmt ;;
  gtForwardDynPrepStmt bOps bGT ;;
  .assign 14 (.bin .sub (.reg 3) (.const 8)) ;;
  .call 15 (bRevCore + gtIdxReverseCore)
    [.reg 9, .reg 7, .reg 10, .reg 8, .reg 11, .reg 12,
     .load (.reg 14),
     .load (.bin .add (.reg 14) (.const 1)),
     .load (.bin .add (.reg 14) (.const 2)),
     .load (.bin .add (.reg 14) (.const 3)),
     .load (.bin .add (.reg 14) (.const 4)),
     .load (.bin .add (.reg 14) (.const 5)),
     .load (.bin .add (.reg 14) (.const 6)),
     .load (.bin .add (.reg 14) (.const 7))] ;;
  .ret (.reg 15)

/-- Module containing `gtReverseDynStmt`. -/
def gtRevDynProcs (bOps bGT bRevCore : ℕ) : List Stmt :=
  [gtReverseDynStmt bOps bGT bRevCore]

/-- Contract for `gtReverseDynStmt`. -/
def gtReverseDynContract (w vCapJ eCapJ vCapOut eCapOut : ℕ) (J : MGraph)
    (retHeap : ℕ) (cJtilde : Cited.Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk) : Contract where
  pre args mem := ∃ jPtr guestBase spOutG scratchPtr
      triplesBufPtr jtildeDynPtr mEmbOutPtr walkBufPtr,
    let jEs := vertsOf J.E
    let sLen := gtRevDynScratchLen J.n J.m
    let totWalk := citedDecPrefLen jEs cJtilde kept embJJtilde jEs.length
    args = [jPtr, guestBase, spOutG, vCapOut, eCapOut, scratchPtr,
      triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr] ∧
    16 ≤ 2 ^ w ∧
    vCapOut < 2 ^ w ∧ eCapOut < 2 ^ w ∧
    jPtr + dynGraphSize vCapJ eCapJ < 2 ^ w ∧
    guestBase + retHeap < 2 ^ w ∧
    scratchPtr + sLen ≤ triplesBufPtr ∧
    guestBase + retHeap ≤ triplesBufPtr ∧
    triplesBufPtr + 3 * kept.length ≤ jtildeDynPtr ∧
    jtildeDynPtr + dynGraphSize vCapOut eCapOut ≤ mEmbOutPtr ∧
    mEmbOutPtr + eCapOut ≤ walkBufPtr ∧
    walkBufPtr + totWalk < 2 ^ w ∧
    (∀ i < dynGraphSize vCapJ eCapJ, jPtr + i < scratchPtr ∨ scratchPtr + sLen ≤ jPtr + i) ∧
    (∀ i < retHeap, guestBase + i < scratchPtr ∨ scratchPtr + sLen ≤ guestBase + i) ∧
    ZeroFrom mem triplesBufPtr ∧
    DynGraphAt mem jPtr vCapJ eCapJ J ∧
    (∀ v ∈ J.V, v < vCapOut) ∧ (∀ e ∈ J.E, e < eCapOut) ∧
    kept.Nodup ∧ (∀ k ∈ kept, k < J.m) ∧
    cJtilde.encode.all (· < 2 ^ w) ∧
    (∀ i < cJtilde.m, (cJtilde.edges[i]!).1 < 2 ^ w ∧ (cJtilde.edges[i]!).2 < 2 ^ w) ∧
    cJtilde.m = kept.length ∧
    (∀ j < J.m,
      (embJJtilde j).verts.length < 2 ^ w ∧ (embJJtilde j).edges.length < 2 ^ w ∧
      (∀ c ∈ (embJJtilde j).edges, c < cJtilde.m ∧ c < kept.length) ∧
      (∀ u ∈ (embJJtilde j).verts, u < 2 ^ w)) ∧
    SparsifyOutRelocAt mem guestBase spOutG retHeap J.m cJtilde kept embJJtilde
  post args mem ret mem' := ∃ jPtr guestBase spOutG scratchPtr
      triplesBufPtr jtildeDynPtr mEmbOutPtr walkBufPtr,
    let jEs := vertsOf J.E
    let sLen := gtRevDynScratchLen J.n J.m
    let totWalk := citedDecPrefLen jEs cJtilde kept embJJtilde jEs.length
    args = [jPtr, guestBase, spOutG, vCapOut, eCapOut, scratchPtr,
      triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr] ∧
    ret = walkBufPtr + totWalk ∧
    DynGraphAt mem' jtildeDynPtr vCapOut eCapOut (outJtilde J kept) ∧
    MEmbAt mem' mEmbOutPtr J.E eCapOut (citedEmbToMGraph J cJtilde kept embJJtilde) ∧
    (∀ j (hj : j < jEs.length),
      let wPtr := mem' (mEmbOutPtr + jEs[j]'hj)
      walkBufPtr ≤ wPtr ∧
      wPtr + (mWalkEncode (citedDecWalk jEs cJtilde kept embJJtilde j)).length ≤ walkBufPtr + totWalk) ∧
    ZeroFrom mem' (walkBufPtr + totWalk) ∧
    ∀ addr, (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) →
      addr < triplesBufPtr → mem' addr = mem addr
  cost _ _ :=
    250 * J.n * (Nat.log 2 (J.n + 1) + 1) +
    250 * J.m * (Nat.log 2 (J.m + 1) + 1) +
    430 * J.n + 500 * J.m + 565 * kept.length +
    250 * ((List.range J.m).map fun j => (embJJtilde j).edges.length).sum + 1000

end

section PrivateHelpers

private lemma gtRevSaveAndSet_triple {w : ℕ} {p : Program}
    {jPtr guestBase spOutG vCap eCap scratchPtr triplesBufPtr jtildeDynPtr mEmbOutPtr walkBufPtr : ℕ}
    {mem : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hs8 : scratchPtr + 8 < 2 ^ w)
    (_h0 : jPtr < 2 ^ w) (_h1 : guestBase < 2 ^ w) (_h2 : spOutG < 2 ^ w)
    (_h3 : vCap < 2 ^ w) (_h4 : eCap < 2 ^ w) (_h5 : scratchPtr < 2 ^ w)
    (_h6 : triplesBufPtr < 2 ^ w) (_h7 : jtildeDynPtr < 2 ^ w)
    (_h8 : mEmbOutPtr < 2 ^ w) (_h9 : walkBufPtr < 2 ^ w) :
    Triple w p
      (fun st => st.mem = mem ∧
        st.regs 0 = jPtr ∧ st.regs 1 = guestBase ∧ st.regs 2 = spOutG ∧
        st.regs 3 = vCap ∧ st.regs 4 = eCap ∧ st.regs 5 = scratchPtr ∧
        st.regs 6 = triplesBufPtr ∧ st.regs 7 = jtildeDynPtr ∧ st.regs 8 = mEmbOutPtr ∧
        st.regs 9 = walkBufPtr)
      gtRevSaveAndSetStmt
      (normalPost fun st =>
        st.regs 0 = 0 ∧ st.regs 1 = jPtr ∧ st.regs 2 = 0 ∧
        st.regs 3 = scratchPtr + 8 ∧ st.regs 4 = 0 ∧
        st.mem scratchPtr = guestBase ∧
        st.mem (scratchPtr + 1) = spOutG ∧
        st.mem (scratchPtr + 2) = vCap ∧
        st.mem (scratchPtr + 3) = eCap ∧
        st.mem (scratchPtr + 4) = triplesBufPtr ∧
        st.mem (scratchPtr + 5) = jtildeDynPtr ∧
        st.mem (scratchPtr + 6) = mEmbOutPtr ∧
        st.mem (scratchPtr + 7) = walkBufPtr ∧
        ∀ addr, addr < scratchPtr ∨ scratchPtr + 8 ≤ addr → st.mem addr = mem addr)
      (fun _ => 70) := by
  wram_enter
  rcases hpre with ⟨rfl, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9⟩
  dsimp only [gtRevSaveAndSetStmt]
  wram_run
  · refine ⟨by simp, by simp, by simp, by simp [r5], by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · intro addr haddr
      have hn0 : addr ≠ scratchPtr := by rcases haddr with h | h <;> omega
      have hn1 : addr ≠ scratchPtr + 1 := by rcases haddr with h | h <;> omega
      have hn2 : addr ≠ scratchPtr + 2 := by rcases haddr with h | h <;> omega
      have hn3 : addr ≠ scratchPtr + 3 := by rcases haddr with h | h <;> omega
      have hn4 : addr ≠ scratchPtr + 4 := by rcases haddr with h | h <;> omega
      have hn5 : addr ≠ scratchPtr + 5 := by rcases haddr with h | h <;> omega
      have hn6 : addr ≠ scratchPtr + 6 := by rcases haddr with h | h <;> omega
      have hn7 : addr ≠ scratchPtr + 7 := by rcases haddr with h | h <;> omega
      simp [Function.update_of_ne, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7]
  · wram_cost

private lemma evalArgs_gtRevCore {w : ℕ} {st : State}
    {jVsPtr nJ jEsPtr mJ jTailsPtr jHeadsPtr scratchPtr
     guestBase spOutG vCap eCap triplesBufPtr jtildeDynPtr mEmbOutPtr walkBufPtr : ℕ}
    (hs7 : scratchPtr + 7 < 2 ^ w)
    (hr9 : st.regs 9 = jVsPtr) (hr7 : st.regs 7 = nJ) (hr10 : st.regs 10 = jEsPtr)
    (hr8 : st.regs 8 = mJ) (hr11 : st.regs 11 = jTailsPtr) (hr12 : st.regs 12 = jHeadsPtr)
    (hr14 : st.regs 14 = scratchPtr)
    (hm0 : st.mem scratchPtr = guestBase)
    (hm1 : st.mem (scratchPtr + 1) = spOutG)
    (hm2 : st.mem (scratchPtr + 2) = vCap)
    (hm3 : st.mem (scratchPtr + 3) = eCap)
    (hm4 : st.mem (scratchPtr + 4) = triplesBufPtr)
    (hm5 : st.mem (scratchPtr + 5) = jtildeDynPtr)
    (hm6 : st.mem (scratchPtr + 6) = mEmbOutPtr)
    (hm7 : st.mem (scratchPtr + 7) = walkBufPtr) :
    evalArgs w st
      [.reg 9, .reg 7, .reg 10, .reg 8, .reg 11, .reg 12,
       .load (.reg 14),
       .load (.bin .add (.reg 14) (.const 1)),
       .load (.bin .add (.reg 14) (.const 2)),
       .load (.bin .add (.reg 14) (.const 3)),
       .load (.bin .add (.reg 14) (.const 4)),
       .load (.bin .add (.reg 14) (.const 5)),
       .load (.bin .add (.reg 14) (.const 6)),
       .load (.bin .add (.reg 14) (.const 7))] =
      some [jVsPtr, nJ, jEsPtr, mJ, jTailsPtr, jHeadsPtr,
        guestBase, spOutG, vCap, eCap, triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr] := by
  have h1 : (Expr.load (.reg 14)).eval w st = some guestBase := by
    simp [Expr.eval, hr14, hm0]
  have h2 : (Expr.load (.bin .add (.reg 14) (.const 1))).eval w st = some spOutG := by
    simp [Expr.eval, BinOp.eval, hr14, hm1, show (1 : ℕ) < 2 ^ w by omega, show scratchPtr + 1 < 2 ^ w by omega]
  have h3 : (Expr.load (.bin .add (.reg 14) (.const 2))).eval w st = some vCap := by
    simp [Expr.eval, BinOp.eval, hr14, hm2, show (2 : ℕ) < 2 ^ w by omega, show scratchPtr + 2 < 2 ^ w by omega]
  have h4 : (Expr.load (.bin .add (.reg 14) (.const 3))).eval w st = some eCap := by
    simp [Expr.eval, BinOp.eval, hr14, hm3, show (3 : ℕ) < 2 ^ w by omega, show scratchPtr + 3 < 2 ^ w by omega]
  have h5 : (Expr.load (.bin .add (.reg 14) (.const 4))).eval w st = some triplesBufPtr := by
    simp [Expr.eval, BinOp.eval, hr14, hm4, show (4 : ℕ) < 2 ^ w by omega, show scratchPtr + 4 < 2 ^ w by omega]
  have h6 : (Expr.load (.bin .add (.reg 14) (.const 5))).eval w st = some jtildeDynPtr := by
    simp [Expr.eval, BinOp.eval, hr14, hm5, show (5 : ℕ) < 2 ^ w by omega, show scratchPtr + 5 < 2 ^ w by omega]
  have h7 : (Expr.load (.bin .add (.reg 14) (.const 6))).eval w st = some mEmbOutPtr := by
    simp [Expr.eval, BinOp.eval, hr14, hm6, show (6 : ℕ) < 2 ^ w by omega, show scratchPtr + 6 < 2 ^ w by omega]
  have h8 : (Expr.load (.bin .add (.reg 14) (.const 7))).eval w st = some walkBufPtr := by
    simp [Expr.eval, BinOp.eval, hr14, hm7, show (7 : ℕ) < 2 ^ w by omega, hs7]
  dsimp only [evalArgs]
  rw [h1, h2, h3, h4, h5, h6, h7, h8]
  simp only [Expr.eval, hr9, hr7, hr10, hr8, hr11, hr12]

end PrivateHelpers

public section

theorem gtReverseDyn_meetsContract {w vCapJ eCapJ vCapOut eCapOut : ℕ} {p : Program}
    {bSort bOps bEdge bSplit bBatch bRevPrim bGT bRevCore bRevDyn : ℕ} {J : MGraph} {retHeap : ℕ}
    {cJtilde : Cited.Graph} {kept : List ℕ} {embJJtilde : ℕ → Walk}
    (hpRevDyn : p.HasAt bRevDyn (gtRevDynProcs bOps bGT bRevCore))
    (hpRevCore : p.HasAt bRevCore (gtRevCoreProcs bBatch bRevPrim))
    (hpRevPrim : p.HasAt bRevPrim gtRevPrimProcs)
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (bRevDyn + gtIdxReverseDyn)
      (gtReverseDynContract w vCapJ eCapJ vCapOut eCapOut J retHeap cJtilde kept embJJtilde) := by
  refine meetsContract_of_runs
    (hpRevDyn.get (i := gtIdxReverseDyn) (by simp [gtRevDynProcs, gtIdxReverseDyn]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨jPtr, guestBase, spOutG, scratchPtr,
      triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr,
      rfl, hw16, hvCap_ltw, heCap_ltw, hjB, hgB_ltw, hscr_le, hsp_le,
      htr_le, hjtd_le, hmemb_le, hwb_ltw,
      hdisjJ, hdisjGB, hz, hDynJ, hvJ_cap, heJ_cap,
      hkept_nd, hkept_lt, hcJall, hcJ_w, hcJm, hembWalks, hSpOut⟩
  let jEs := vertsOf J.E
  let jVs := vertsOf J.V
  let jTails := jEs.map J.tail
  let jHeads := jEs.map J.head
  let sLen := gtRevDynScratchLen J.n J.m
  let prepScratch := scratchPtr + 8
  let jVsPtr := prepScratch
  let jEsPtr := jVsPtr + J.n
  let jTailsPtr := jEsPtr + J.m
  let jHeadsPtr := jTailsPtr + J.m
  have hsLen_eq : sLen = 8 + gtFwdDynScratchLen J.n J.m 0 := by
    dsimp [sLen, gtRevDynScratchLen, gtFwdDynScratchLen]; omega
  have hprep_eq : gtFwdDynScratchLen J.n J.m 0 = 3 * J.n + 6 * J.m := by
    simp [gtFwdDynScratchLen]
  have hlt_jP : jPtr < 2 ^ w := hargs jPtr (by simp)
  have hlt_gB : guestBase < 2 ^ w := hargs guestBase (by simp)
  have hlt_spO : spOutG < 2 ^ w := hargs spOutG (by simp)
  have hlt_scrP : scratchPtr < 2 ^ w := hargs scratchPtr (by simp)
  have hlt_trB : triplesBufPtr < 2 ^ w := hargs triplesBufPtr (by simp)
  have hlt_jtdP : jtildeDynPtr < 2 ^ w := hargs jtildeDynPtr (by simp)
  have hlt_mEP : mEmbOutPtr < 2 ^ w := hargs mEmbOutPtr (by simp)
  have hlt_wBP : walkBufPtr < 2 ^ w := hargs walkBufPtr (by simp)
  have htr_ltw : triplesBufPtr < 2 ^ w := hlt_trB
  have hscr8_ltw : scratchPtr + 8 < 2 ^ w := by dsimp [sLen, gtRevDynScratchLen] at *; omega
  have hprep_ltw : prepScratch + gtFwdDynScratchLen J.n J.m 0 < 2 ^ w := by
    dsimp [prepScratch, sLen, gtRevDynScratchLen, gtFwdDynScratchLen] at *; omega
  dsimp only [gtRevDynProcs, gtIdxReverseDyn, List.getElem_cons_zero, gtReverseDynStmt]
  refine runs_start_le ?_
  refine runs_seq_triple_le
    (gtRevSaveAndSet_triple (p := p)
      (jPtr := jPtr) (guestBase := guestBase) (spOutG := spOutG)
      (vCap := vCapOut) (eCap := eCapOut) (scratchPtr := scratchPtr)
      (triplesBufPtr := triplesBufPtr) (jtildeDynPtr := jtildeDynPtr)
      (mEmbOutPtr := mEmbOutPtr) (walkBufPtr := walkBufPtr)
      hw16 hscr8_ltw hlt_jP hlt_gB hlt_spO hvCap_ltw heCap_ltw hlt_scrP hlt_trB hlt_jtdP hlt_mEP hlt_wBP)
    ⟨rfl, by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp [startState], by simp [startState], by simp [startState]⟩
    ?_
  intro st1 ⟨hr0, hr1, hr2, hr3, hr4, hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hfr1⟩
  have hDynJ1 : DynGraphAt st1.mem jPtr vCapJ eCapJ J := by
    refine hDynJ.of_agree fun addr ha1 ha2 => ?_
    have hdj := hdisjJ (addr - jPtr) (Nat.sub_lt_left_of_lt_add ha1 ha2)
    rw [Nat.add_sub_cancel' ha1] at hdj
    exact hfr1 addr (by rcases hdj with h | h <;> [left; right] <;> omega)
  have hdisjJ_prep : ∀ i < dynGraphSize vCapJ eCapJ,
      jPtr + i < prepScratch ∨ prepScratch + gtFwdDynScratchLen J.n J.m 0 ≤ jPtr + i := fun i hi => by
    rcases hdisjJ i hi with h | h <;> [left; right] <;> omega
  refine runs_seq_triple_le
    (gtForwardDyn_prepPhase (vCapJ := vCapJ) (eCapJ := eCapJ) (rawEsLen := 0)
      (J := J) hpOps hpGT hpSort)
    ⟨hw16, by omega, hjB, by omega, by omega, hprep_ltw, hdisjJ_prep, hDynJ1, rfl,
      hr0, hr1, hr2, hr3, hr4⟩
    ?_
  intro st2 ⟨_, _, _, hr2_3, _, hr2_7, hr2_8, hr2_9, hr2_10, hr2_11, hr2_12, _,
    hVAt2, hEAt2, hTAt2, hHAt2, hfr2⟩
  have h8_lt : 8 < 2 ^ w := by omega
  have hscr_back : st2.regs 3 - 8 = scratchPtr := by rw [hr2_3]; dsimp [prepScratch]; omega
  refine runs_seq_assign_le (v := scratchPtr)
    (by simp [Expr.eval, BinOp.eval, hr2_3, prepScratch, h8_lt, hlt_scrP]) ?_
  have hs2_ltw : scratchPtr + 1 < 2 ^ w := by omega
  have hs3_ltw : scratchPtr + 2 < 2 ^ w := by omega
  have hs4_ltw : scratchPtr + 3 < 2 ^ w := by omega
  have hs5_ltw : scratchPtr + 4 < 2 ^ w := by omega
  have hs6_ltw : scratchPtr + 5 < 2 ^ w := by omega
  have hs7_ltw : scratchPtr + 6 < 2 ^ w := by omega
  have hs8_ltw : scratchPtr + 7 < 2 ^ w := by omega
  have hmem_s0 : st2.mem scratchPtr = guestBase :=
    (hfr2 scratchPtr (Or.inl (by dsimp [prepScratch]; omega))).trans hm0
  have hmem_s1 : st2.mem (scratchPtr + 1) = spOutG :=
    (hfr2 (scratchPtr + 1) (Or.inl (by dsimp [prepScratch]; omega))).trans hm1
  have hmem_s2 : st2.mem (scratchPtr + 2) = vCapOut :=
    (hfr2 (scratchPtr + 2) (Or.inl (by dsimp [prepScratch]; omega))).trans hm2
  have hmem_s3 : st2.mem (scratchPtr + 3) = eCapOut :=
    (hfr2 (scratchPtr + 3) (Or.inl (by dsimp [prepScratch]; omega))).trans hm3
  have hmem_s4 : st2.mem (scratchPtr + 4) = triplesBufPtr :=
    (hfr2 (scratchPtr + 4) (Or.inl (by dsimp [prepScratch]; omega))).trans hm4
  have hmem_s5 : st2.mem (scratchPtr + 5) = jtildeDynPtr :=
    (hfr2 (scratchPtr + 5) (Or.inl (by dsimp [prepScratch]; omega))).trans hm5
  have hmem_s6 : st2.mem (scratchPtr + 6) = mEmbOutPtr :=
    (hfr2 (scratchPtr + 6) (Or.inl (by dsimp [prepScratch]; omega))).trans hm6
  have hmem_s7 : st2.mem (scratchPtr + 7) = walkBufPtr :=
    (hfr2 (scratchPtr + 7) (Or.inl (by dsimp [prepScratch]; omega))).trans hm7
  have hfr_scr : ∀ addr, (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) → st2.mem addr = mem addr :=
    fun addr ha => by
      have ha2 : addr < prepScratch ∨ prepScratch + gtFwdDynScratchLen J.n J.m 0 ≤ addr := by
        rcases ha with h | h
        · exact Or.inl (by dsimp [prepScratch]; omega)
        · exact Or.inr (by dsimp [prepScratch, sLen, gtRevDynScratchLen, gtFwdDynScratchLen] at *; omega)
      have ha1 : addr < scratchPtr ∨ scratchPtr + 8 ≤ addr := by
        rcases ha with h | h
        · exact Or.inl h
        · exact Or.inr (by dsimp [sLen, gtRevDynScratchLen] at *; omega)
      exact (hfr2 addr ha2).trans (hfr1 addr ha1)
  have hz2 : ZeroFrom st2.mem triplesBufPtr := fun addr ha => by
    rw [hfr_scr addr (Or.inr (by omega))]
    exact hz addr ha
  have hSpOut2 : SparsifyOutRelocAt st2.mem guestBase spOutG retHeap J.m cJtilde kept embJJtilde := by
    have hAgree : ∀ addr < guestBase + retHeap, guestBase ≤ addr → st2.mem addr = mem addr :=
      fun addr ha1 ha2 =>
        hfr_scr addr (hdisjGB (addr - guestBase) (Nat.sub_lt_left_of_lt_add ha2 ha1) |>.imp
          (fun h => by omega) (fun h => by omega))
    dsimp only [SparsifyOutRelocAt] at hSpOut
    rcases hSpOut with ⟨hsp3, hpJ, hpK, hpE, hG, hL, hEm⟩
    have hsp0_lt : guestBase + spOutG < guestBase + retHeap := by omega
    have hsp1_lt : guestBase + spOutG + 1 < guestBase + retHeap := by omega
    have hsp2_lt : guestBase + spOutG + 2 < guestBase + retHeap := by omega
    have hsp0_ge : guestBase ≤ guestBase + spOutG := by omega
    have hsp1_ge : guestBase ≤ guestBase + spOutG + 1 := by omega
    have hsp2_ge : guestBase ≤ guestBase + spOutG + 2 := by omega
    have e0 : st2.mem (guestBase + spOutG) = mem (guestBase + spOutG) := hAgree _ hsp0_lt hsp0_ge
    have e1 : st2.mem (guestBase + spOutG + 1) = mem (guestBase + spOutG + 1) := hAgree _ hsp1_lt hsp1_ge
    have e2 : st2.mem (guestBase + spOutG + 2) = mem (guestBase + spOutG + 2) := hAgree _ hsp2_lt hsp2_ge
    refine ⟨hsp3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e0]; exact hpJ
    · rw [e1]; exact hpK
    · rw [e2]; exact hpE
    · rw [e0]
      intro i hi
      rw [hAgree (guestBase + mem (guestBase + spOutG) + i) (by omega) (by omega)]
      exact hG i hi
    · rw [e1]
      intro i hi
      simp only [List.length_cons] at hi
      rw [hAgree (guestBase + mem (guestBase + spOutG + 1) + i) (by omega) (by omega)]
      exact hL i (by simpa using hi)
    · intro j hj
      rw [e2, hAgree (guestBase + mem (guestBase + spOutG + 2) + j) (by omega) (by omega)]
      refine ⟨(hEm j hj).1, fun i hi => ?_⟩
      rw [hAgree (guestBase + mem (guestBase + mem (guestBase + spOutG + 2) + j) + i)
        (by have := (hEm j hj).1; omega) (by omega)]
      exact (hEm j hj).2 i hi
  have hjV_len : jVs.length = J.n := vertsOf_length J.V
  have hjE_len : jEs.length = J.m := vertsOf_length J.E
  have hkept_lt_jEs : ∀ k ∈ kept, k < jEs.length := fun k hk => by
    rw [hjE_len]; exact hkept_lt k hk
  have hembWalks_jEs : ∀ j < jEs.length,
      (embJJtilde j).verts.length < 2 ^ w ∧ (embJJtilde j).edges.length < 2 ^ w ∧
      (∀ c ∈ (embJJtilde j).edges, c < cJtilde.m ∧ c < kept.length) ∧
      (∀ u ∈ (embJJtilde j).verts, u < 2 ^ w) := fun j hj => by
    rw [hjE_len] at hj; exact hembWalks j hj
  have hSpOut2_jEs : SparsifyOutRelocAt st2.mem guestBase spOutG retHeap jEs.length cJtilde kept embJJtilde := by
    rw [hjE_len]; exact hSpOut2
  refine runs_seq_call_le
    (gtReverseCore_meetsContract (w := w) (vCap := vCapOut) (eCap := eCapOut)
      (J := J) (jVs := jVs) (jEs := jEs) (jTails := jTails) (jHeads := jHeads)
      (retHeap := retHeap) (cJtilde := cJtilde) (kept := kept) (embJJtilde := embJJtilde)
      hpRevCore hpRevPrim hpBatch hpEdge hpOps)
    (vs := [jVsPtr, jVs.length, jEsPtr, jEs.length, jTailsPtr, jHeadsPtr,
      guestBase, spOutG, vCapOut, eCapOut, triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr])
    (evalArgs_gtRevCore hs8_ltw
      (by simp [Function.update_of_ne, hr2_9]; rfl)
      (by simp [Function.update_of_ne, hr2_7, hjV_len])
      (by simp [Function.update_of_ne, hr2_10]; rfl)
      (by simp [Function.update_of_ne, hr2_8, hjE_len])
      (by simp [Function.update_of_ne, hr2_11]; rfl)
      (by simp [Function.update_of_ne, hr2_12]; rfl)
      (by simp [Function.update_self])
      hmem_s0 hmem_s1 hmem_s2 hmem_s3 hmem_s4 hmem_s5 hmem_s6 hmem_s7)
    (by intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · dsimp [jVsPtr, prepScratch] at *; omega
        · rw [hjV_len]; exact lt_of_le_of_lt (by omega) hprep_ltw
        · dsimp [jEsPtr, jVsPtr, prepScratch] at *; omega
        · rw [hjE_len]; exact lt_of_le_of_lt (by omega) hprep_ltw
        · dsimp [jTailsPtr, jEsPtr, jVsPtr, prepScratch] at *; omega
        · dsimp [jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr, prepScratch] at *; omega
        · exact hlt_gB
        · exact hlt_spO
        · exact hvCap_ltw
        · exact heCap_ltw
        · exact hlt_trB
        · exact hlt_jtdP
        · exact hlt_mEP
        · exact hlt_wBP)
    ⟨jVsPtr, jEsPtr, jTailsPtr, jHeadsPtr, guestBase, spOutG, triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr,
      rfl, hw16, hvCap_ltw, heCap_ltw, hgB_ltw, htr_le, hjtd_le, hmemb_le, hwb_ltw, hz2,
      hDynJ.1, hvJ_cap, heJ_cap, rfl, rfl, by simp [jTails], by simp [jHeads],
      fun j hj => ⟨by simp [jTails, hj], by simp [jHeads, hj]⟩,
      hkept_nd, hkept_lt_jEs, hcJall, hcJ_w, hcJm, hembWalks_jEs,
      hVAt2, hEAt2, hTAt2, hHAt2,
      by dsimp [jVsPtr, prepScratch]; rw [hjV_len]; dsimp [sLen, gtRevDynScratchLen] at hscr_le; omega,
      by dsimp [jEsPtr, jVsPtr, prepScratch]; rw [hjE_len]; dsimp [sLen, gtRevDynScratchLen] at hscr_le; omega,
      by dsimp [jTailsPtr, jEsPtr, jVsPtr, prepScratch]; rw [hjE_len]; dsimp [sLen, gtRevDynScratchLen] at hscr_le; omega,
      by dsimp [jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr, prepScratch]; rw [hjE_len]; dsimp [sLen, gtRevDynScratchLen] at hscr_le; omega,
      hsp_le, hSpOut2_jEs⟩
    ?_
  intro ret mem3 pos3 ⟨_, _, _, _, _, _, _, _, _, _, hargs3, hret3, hDyn3, hmEmb3, hwb3, hz3, hfr3⟩
  simp only [List.cons.injEq, true_and, and_true] at hargs3
  rcases hargs3 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hfr3_out : ∀ addr, (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) →
      addr < triplesBufPtr → mem3 addr = mem addr := fun addr hs ht =>
    (hfr3 addr ht).trans (hfr_scr addr hs)
  refine runs_ret_le (v := walkBufPtr + citedDecPrefLen jEs cJtilde kept embJJtilde jEs.length)
    (by simp [Expr.eval, Function.update_self, hret3])
    ⟨jPtr, guestBase, spOutG, scratchPtr, triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr,
      rfl, (by simp [Outcome.value, jEs]), hDyn3, hmEmb3, hwb3, hz3, hfr3_out⟩
    ?_
  dsimp only [gtReverseDynContract, gtReverseCoreContract, argsSize, Expr.size]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [hjV_len, hjE_len]
  omega

end

end MinCostFlow.DynSpanner.Program
