module

public import MinCostFlow.DynSpanner.Program.GraphTranslateHelpersPrep

/-!
# Dynamic Forward Graph Translation (`GraphTranslateDyn`)

Completes verification of `gtForwardCore_meetsContract` (`gtIdxForwardCore = 0`) and
`gtForwardDyn_meetsContract` (`gtIdxForwardDyn = 1`) for translating `DynGraphAt H'` and
`DynGraphAt J` with `MEmbAt emb` into canonical `canonSparsifyInput` memory.

The file is split in three parts: `GraphTranslateHelpersCopy.lean` (loop lemmas),
`GraphTranslateHelpersPrep.lean` (programs, invariants and the vertex phase), and this file (the
edge phases and the whole preparation).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

@[expose] public section

/-- Mid-point invariant between `gtForwardDynPrepE1Stmt` and `gtForwardDynPrepE2Stmt`. -/
def gtDynPrepEMid (w vCapJ eCapJ rawEsLen : ℕ) (J : MGraph)
    (hPtr jPtr mEmbPtr scratchPtr outPtr : ℕ) (mem : ℕ → ℕ) : State → Prop :=
  fun st =>
    gtDynPrepVMid w vCapJ eCapJ rawEsLen J hPtr jPtr mEmbPtr scratchPtr outPtr mem st ∧
    ListAt st.mem (scratchPtr + J.n) (vertsOf J.E)

private lemma gt_prepE1_cost_le {m lg a b c4 : ℕ}
    (hc4 : c4 ≤ b + (250 * m * lg + 120) + 1) (ha : a ≤ 20) (hb : b ≤ 10) :
    0 + a + 2 + (m * 18 + 7) + 1 + c4 ≤ 250 * m * lg + 50 * m + 200 := by
  omega

theorem gtForwardDyn_prepE1Phase {w vCapJ eCapJ rawEsLen : ℕ} {p : Program}
    {bSort bOps bGT : ℕ} {J : MGraph}
    {hPtr jPtr mEmbPtr scratchPtr outPtr : ℕ} {mem : ℕ → ℕ}
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort)) :
    Triple w p
      (gtDynPrepVMid w vCapJ eCapJ rawEsLen J hPtr jPtr mEmbPtr scratchPtr outPtr mem)
      (gtForwardDynPrepE1Stmt bGT)
      (normalPost (gtDynPrepEMid w vCapJ eCapJ rawEsLen J hPtr jPtr mEmbPtr scratchPtr outPtr mem))
      (fun _ => 250 * J.m * (Nat.log 2 (J.m + 1) + 1) + 50 * J.m + 200) := by
  intro st2 ω hMid
  rcases hMid with ⟨hw16, hlt_hP, hjB, hlt_mEP, hlt_outP, hscB, hdisjJ, hDynJ,
    hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
    hVAt2, hfr2_out⟩
  let jVs := vertsOf J.V
  let jEs := vertsOf J.E
  let jTails := jEs.map J.tail
  let jHeads := jEs.map J.head
  let sLen := gtFwdDynScratchLen J.n J.m rawEsLen
  have hsLen_eq : sLen = 3 * J.n + 6 * J.m + 5 * rawEsLen := rfl
  have hscB' : scratchPtr + sLen < 2 ^ w := hscB
  rw [hsLen_eq] at hscB'
  have hjV_len : jVs.length = J.n := vertsOf_length J.V
  have hjE_len : jEs.length = J.m := vertsOf_length J.E
  have hjE_iff : ∀ e, e ∈ jEs ↔ e ∈ J.E := fun e => by simp [jEs, mem_vertsOf]
  have heCapJ_ltw : eCapJ < 2 ^ w := by unfold dynGraphSize at hjB; omega
  have hmJ_le : J.m ≤ eCapJ := dynGraph_m_le_eCap hDynJ
  have hlt_mJ : J.m < 2 ^ w := by omega
  let jVsPtr := scratchPtr
  let jEsPtr := jVsPtr + J.n
  let jTailsPtr := jEsPtr + J.m
  let jHeadsPtr := jTailsPtr + J.m
  let coreScratch := jHeadsPtr + J.m
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h4_lt : (4 : ℕ) < 2 ^ w := by omega
  have h7_lt : (7 : ℕ) < 2 ^ w := by omega
  have h7vc_ltw : 7 * vCapJ < 2 ^ w := by unfold dynGraphSize at hjB; omega
  have h7vcec_ltw : 7 * vCapJ + eCapJ < 2 ^ w := by unfold dynGraphSize at hjB; omega
  have h4_7vcec_ltw : 4 + (7 * vCapJ + eCapJ) < 2 ^ w := by unfold dynGraphSize at hjB; omega
  have heListP_ltw : dgEListBase jPtr vCapJ eCapJ < 2 ^ w := by
    dsimp [dgEListBase]; unfold dynGraphSize at hjB; omega
  have hdgEL_ltw : jPtr + (4 + (7 * vCapJ + eCapJ)) < 2 ^ w := by
    dsimp [dgEListBase] at heListP_ltw; omega
  have hcs_m_ltw : coreScratch + J.m < 2 ^ w := by
    dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have hcs2m_ltw : coreScratch + 2 * J.m < 2 ^ w := by
    dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have hJEc : ∀ e ∈ J.E, e < eCapJ := hDynJ.2.2.1
  rcases hDynJ.2.2.2.2.2.2.2.2.2.2.2.2.1 with ⟨eL, heL_len, -, heL_mem, heL_at, -⟩
  have hjV_eq : jVsPtr = scratchPtr := rfl
  have hjE_eq : jEsPtr = scratchPtr + J.n := rfl
  have hjT_eq : jTailsPtr = scratchPtr + J.n + J.m := rfl
  have hjH_eq : jHeadsPtr = scratchPtr + J.n + 2 * J.m := by
    dsimp only [jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have hcs_eq : coreScratch = scratchPtr + J.n + 3 * J.m := by
    dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have hdg_ub : coreScratch + 2 * J.m ≤ scratchPtr + gtFwdDynScratchLen J.n J.m rawEsLen := by
    rw [hcs_eq]; dsimp only [gtFwdDynScratchLen]; omega
  have hcs_ub : coreScratch + 2 * J.m ≤ scratchPtr + sLen := by
    rw [hsLen_eq]; exact hdg_ub
  have h_s_le_cs : scratchPtr ≤ coreScratch := by
    rw [hcs_eq, Nat.add_assoc]; exact Nat.le_add_right _ _
  have h_vn_le_cs : jVsPtr + J.n ≤ coreScratch := by
    rw [hjV_eq, hcs_eq]; exact Nat.le_add_right _ _
  have h_cs_m_ub : coreScratch + J.m ≤ scratchPtr + sLen :=
    le_trans (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by decide)) _) hcs_ub
  have h_s_le_e : scratchPtr ≤ jEsPtr := by
    rw [hjE_eq]; exact Nat.le_add_right _ _
  have h_s_le_csm : scratchPtr ≤ coreScratch + J.m :=
    le_trans h_s_le_cs (Nat.le_add_right _ _)
  have h_e_ub : jEsPtr + J.m ≤ scratchPtr + sLen :=
    le_trans (by rw [hjE_eq, hcs_eq]; omega) h_cs_m_ub
  have h_cs_2m_ub : coreScratch + J.m + J.m ≤ scratchPtr + sLen := by
    rw [Nat.add_assoc, ← Nat.two_mul]; exact hcs_ub
  have h_vn_le_e : jVsPtr + J.n ≤ jEsPtr := by rw [hjV_eq, hjE_eq]
  have hcsP_ltw : coreScratch < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ J.m) hcs_m_ltw
  have hjEsP_ltw : jEsPtr < 2 ^ w := by rw [hcs_eq] at hcsP_ltw; rw [hjE_eq]; omega
  have h_dgE_lt : dgEListBase jPtr vCapJ eCapJ + J.m < 2 ^ w := by
    dsimp [dgEListBase]; unfold dynGraphSize at hjB; omega
  have h_dgE_in_J : ∀ i < J.m,
      dgEListBase jPtr vCapJ eCapJ + i < scratchPtr ∨
        scratchPtr + sLen ≤ dgEListBase jPtr vCapJ eCapJ + i := fun i hi => by
    have hdj := hdisjJ (dgEListBase jPtr vCapJ eCapJ + i - jPtr) (by
      dsimp [dgEListBase]; unfold dynGraphSize; omega)
    rw [show jPtr + (dgEListBase jPtr vCapJ eCapJ + i - jPtr) = dgEListBase jPtr vCapJ eCapJ + i by
      dsimp [dgEListBase]; omega] at hdj
    exact hdj
  have h_dgE_disj : ∀ i < J.m, ∀ j < J.m, dgEListBase jPtr vCapJ eCapJ + i ≠ coreScratch + j :=
    fun i hi j hj heq => by
      rcases h_dgE_in_J i hi with h | h <;> omega
  have h_e_m_ltw : jEsPtr + eL.length < 2 ^ w := by
    rw [heL_len]; exact lt_of_le_of_lt h_e_ub hscB
  have h_cs_e_ltw : coreScratch + eL.length < 2 ^ w := by rw [heL_len]; exact hcs_m_ltw
  have h_cse_e_ltw : coreScratch + eL.length + eL.length < 2 ^ w := by
    rw [heL_len, Nat.add_assoc, ← Nat.two_mul]; exact hcs2m_ltw
  have h_cse_disj : coreScratch + eL.length ≤ jEsPtr ∨ jEsPtr + eL.length ≤ coreScratch := by
    right; rw [heL_len, hjE_eq, hcs_eq]; omega
  let rOrigDyn : ℕ → ℕ := fun r =>
    match r with
    | 0 => hPtr | 1 => jPtr | 2 => mEmbPtr | 3 => scratchPtr | 4 => outPtr
    | 5 => vCapJ | 6 => eCapJ | 7 => J.n | 8 => J.m
    | 9 => jVsPtr | 10 => jEsPtr | 11 => jTailsPtr | 12 => jHeadsPtr | _ => coreScratch
  have hOrig2 : ∀ r < 14, st2.regs r = rOrigDyn r := fun r hr => by
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨
        r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hr0
    · exact hr1
    · exact hr2
    · exact hr3
    · exact hr4
    · exact hr5
    · exact hr6
    · exact hr7
    · exact hr8
    · exact hr9
    · exact hr10
    · exact hr11
    · dsimp only [rOrigDyn]; rw [hjH_eq, hr12]; omega
    · dsimp only [rOrigDyn]; rw [hcs_eq, hr13]; omega
  dsimp only [gtForwardDynPrepE1Stmt]
  refine runs_start_le ?_
  -- 5. assign 14 := dgEListBase jPtr vCapJ eCapJ
  refine runs_seq_assign_le (v := dgEListBase jPtr vCapJ eCapJ)
    (by simp only [Expr.eval, BinOp.eval, hr1, hr5, hr6, h4_lt, h7_lt,
          h7vc_ltw, h7vcec_ltw, h4_7vcec_ltw, hdgEL_ltw, ↓reduceIte]
        rw [show jPtr + (4 + (7 * vCapJ + eCapJ)) = dgEListBase jPtr vCapJ eCapJ by
          dsimp [dgEListBase]; omega])
    ?_
  -- 6. Copy eL to coreScratch
  have hOrig3 : ∀ r < 14, (Function.update st2.regs 14 (dgEListBase jPtr vCapJ eCapJ)) r = rOrigDyn r :=
    fun r hr => by rw [Function.update_of_ne (Nat.ne_of_lt hr)]; exact hOrig2 r hr
  have heL_at2 : ListAt st2.mem (dgEListBase jPtr vCapJ eCapJ) eL := fun i hi =>
    (hfr2_out _ (h_dgE_in_J i (heL_len ▸ hi))).trans (heL_at i hi)
  have hr13_3 : (Function.update st2.regs 14 (dgEListBase jPtr vCapJ eCapJ)) 13 = coreScratch := by
    rw [Function.update_of_ne (by decide)]; exact hr13
  have hr8_3 : (Function.update st2.regs 14 (dgEListBase jPtr vCapJ eCapJ)) 8 = J.m := by
    rw [Function.update_of_ne (by decide)]; exact hr8
  refine runs_seq_triple_le
    (gtCopyRange_triple 14 13 8 (by decide) (by decide) (by decide)
      (srcPtr := dgEListBase jPtr vCapJ eCapJ) (dstPtr := coreScratch) (len := J.m) (L := eL)
      (mem := st2.mem) (rOrig := rOrigDyn)
      h1_lt hlt_mJ h_dgE_lt hcs_m_ltw heL_len heL_at2 h_dgE_disj)
    ⟨rfl, by simp [Function.update_self], hr13_3, hr8_3, hOrig3⟩
    ?_
  intro st3 ⟨_, _, _, _, hOrig4, heCopy3, hfr3⟩
  have hfr3_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr → st3.mem addr = mem addr :=
    fun addr ha => by
      have ha3 : addr < coreScratch ∨ coreScratch + J.m ≤ addr := by
        rcases ha with h | h
        · exact Or.inl (lt_of_lt_of_le h h_s_le_cs)
        · exact Or.inr (le_trans h_cs_m_ub h)
      exact (hfr3 addr ha3).trans (hfr2_out addr ha)
  have hVAt3 : ListAt st3.mem jVsPtr jVs := fun i hi => by
    have hi_n : i < J.n := hjV_len ▸ hi
    rw [hfr3 _ (Or.inl (lt_of_lt_of_le (Nat.add_lt_add_left hi_n _) h_vn_le_cs))]
    exact hVAt2 i hi
  have heAt3 : ListAt st3.mem coreScratch eL := fun i hi => heCopy3 i (heL_len ▸ hi) hi
  have heL_w : ∀ x ∈ eL, x < 2 ^ w := fun x hx => by
    rw [heL_mem] at hx
    exact lt_trans (hJEc x hx) heCapJ_ltw
  -- 7. SortDedup eL -> jEsPtr (terminal call of gtForwardDynPrepE1Stmt)
  rcases runs_call_of_meetsContract (gtSortDedup_meetsContract (L := eL) (X := J.E) hpGT hpSort)
      (r := 15) (args := [.reg 13, .reg 8, .reg 10, .bin .add (.reg 13) (.reg 8)])
      (st := st3) (vs := [coreScratch, eL.length, jEsPtr, coreScratch + eL.length])
      (by have hr13 := hOrig4 13 (by decide)
          have hr8 := hOrig4 8 (by decide)
          have hr10 := hOrig4 10 (by decide)
          dsimp only [rOrigDyn] at hr13 hr8 hr10
          simp only [evalArgs, Expr.eval, BinOp.eval, hr13, hr8, hr10, heL_len, hcs_m_ltw, ↓reduceIte])
      (by intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl
          · exact hcsP_ltw
          · rw [heL_len]; exact hlt_mJ
          · exact hjEsP_ltw
          · rw [heL_len]; exact hcs_m_ltw)
      ⟨coreScratch, jEsPtr, coreScratch + eL.length, rfl, hw16,
        h_cs_e_ltw, h_e_m_ltw, h_cse_e_ltw, Or.inl (le_refl _), h_cse_disj,
        heAt3, heL_w, heL_mem⟩ ω with
    ⟨st4, c4, lenE, hrun4, ⟨_, _, _, hargs4, hret4, hEAt4, hfr4⟩, hr4_self, hr4_other, hcost4⟩
  simp only [List.cons.injEq, and_true] at hargs4
  rcases hargs4 with ⟨rfl, _, rfl, rfl⟩
  refine ⟨.normal, st4, c4, hrun4, ?_, ?_⟩
  · have hfr4' : ∀ addr, (addr < coreScratch ∨ coreScratch + eL.length ≤ addr) →
        (addr < coreScratch + eL.length ∨ coreScratch + eL.length + eL.length ≤ addr) →
        (addr < jEsPtr ∨ jEsPtr + (vertsOf J.E).length ≤ addr) → st4.mem addr = st3.mem addr := hfr4
    have hfr4_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr → st4.mem addr = mem addr :=
      fun addr ha => by
        have ha1 : addr < coreScratch ∨ coreScratch + eL.length ≤ addr := by
          rw [heL_len]; rcases ha with h | h
          · exact Or.inl (lt_of_lt_of_le h h_s_le_cs)
          · exact Or.inr (le_trans h_cs_m_ub h)
        have ha2 : addr < jEsPtr ∨ jEsPtr + (vertsOf J.E).length ≤ addr := by
          rw [hjE_len]; rcases ha with h | h
          · exact Or.inl (lt_of_lt_of_le h h_s_le_e)
          · exact Or.inr (le_trans h_e_ub h)
        have ha3 : addr < coreScratch + eL.length ∨ coreScratch + eL.length + eL.length ≤ addr := by
          rw [heL_len]; rcases ha with h | h
          · exact Or.inl (lt_of_lt_of_le h h_s_le_csm)
          · exact Or.inr (le_trans h_cs_2m_ub h)
        exact (hfr4' addr ha1 ha3 ha2).trans (hfr3_out addr ha)
    have hVAt4 : ListAt st4.mem jVsPtr jVs := fun i hi => by
      have hi_n : i < J.n := hjV_len ▸ hi
      have hlt_cs : jVsPtr + i < coreScratch :=
        lt_of_lt_of_le (Nat.add_lt_add_left hi_n _) h_vn_le_cs
      have hlt_csm : jVsPtr + i < coreScratch + eL.length :=
        lt_of_lt_of_le hlt_cs (Nat.le_add_right _ _)
      have hlt_e : jVsPtr + i < jEsPtr :=
        lt_of_lt_of_le (Nat.add_lt_add_left hi_n _) h_vn_le_e
      rw [hfr4' _ (Or.inl hlt_cs) (Or.inl hlt_csm) (Or.inl hlt_e)]
      exact hVAt3 i hi
    have hOrig5 : ∀ r < 14, st4.regs r = rOrigDyn r := fun r hr => by
      rw [hr4_other r (Nat.ne_of_lt (Nat.lt_trans hr (by decide : 14 < 15)))]; exact hOrig4 r hr
    refine ⟨⟨hw16, hlt_hP, hjB, hlt_mEP, hlt_outP, hscB, hdisjJ, hDynJ,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hVAt4, hfr4_out⟩, hEAt4⟩
    · have h := hOrig5 0 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 1 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 2 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 3 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 4 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 5 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 6 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 7 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 8 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 9 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 10 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 11 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 12 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig5 13 (by decide); dsimp only [rOrigDyn] at h; exact h
  · dsimp only [gtSortDedupContract, argsSize, Expr.size] at hcost4 ⊢
    rw [heL_len] at hcost4
    exact gt_prepE1_cost_le hcost4
      (by decide : 1 + (1 + (1 + 1 + 1 + 1 + 1) + 1) + 1 ≤ 20)
      (by decide : 1 + (1 + (1 + (1 + 1 + 1 + 0))) ≤ 10)

theorem gtForwardDyn_prepE2Phase {w vCapJ eCapJ rawEsLen : ℕ} {p : Program}
    {bOps : ℕ} {J : MGraph}
    {hPtr jPtr mEmbPtr scratchPtr outPtr : ℕ} {mem : ℕ → ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs) :
    Triple w p
      (gtDynPrepEMid w vCapJ eCapJ rawEsLen J hPtr jPtr mEmbPtr scratchPtr outPtr mem)
      (gtForwardDynPrepE2Stmt bOps)
      (normalPost (gtDynPrepPost J rawEsLen hPtr jPtr mEmbPtr scratchPtr outPtr mem))
      (fun _ => 125 * J.m + 7) := by
  intro st4 ω ⟨hMidV, hEAt4⟩
  rcases hMidV with ⟨hw16, hlt_hP, hjB, hlt_mEP, hlt_outP, hscB, hdisjJ, hDynJ,
    hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr10, hr11, hr12, hr13,
    hVAt4, hfr4_out⟩
  let jVs := vertsOf J.V
  let jEs := vertsOf J.E
  let jTails := jEs.map J.tail
  let jHeads := jEs.map J.head
  let sLen := gtFwdDynScratchLen J.n J.m rawEsLen
  have hsLen_eq : sLen = 3 * J.n + 6 * J.m + 5 * rawEsLen := rfl
  have hscB' : scratchPtr + sLen < 2 ^ w := hscB
  rw [hsLen_eq] at hscB'
  have hjV_len : jVs.length = J.n := vertsOf_length J.V
  have hjE_len : jEs.length = J.m := vertsOf_length J.E
  have hjE_iff : ∀ e, e ∈ jEs ↔ e ∈ J.E := fun e => by simp [jEs, mem_vertsOf]
  let jVsPtr := scratchPtr
  let jEsPtr := jVsPtr + J.n
  let jTailsPtr := jEsPtr + J.m
  let jHeadsPtr := jTailsPtr + J.m
  let coreScratch := jHeadsPtr + J.m
  have hjV_eq : jVsPtr = scratchPtr := rfl
  have hjE_eq : jEsPtr = scratchPtr + J.n := rfl
  have hjT_eq : jTailsPtr = scratchPtr + J.n + J.m := rfl
  have hjH_eq : jHeadsPtr = scratchPtr + J.n + 2 * J.m := by
    dsimp only [jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have hcs_eq : coreScratch = scratchPtr + J.n + 3 * J.m := by
    dsimp only [coreScratch, jHeadsPtr, jTailsPtr, jEsPtr, jVsPtr]; omega
  have hdg_ub : coreScratch + 2 * J.m ≤ scratchPtr + gtFwdDynScratchLen J.n J.m rawEsLen := by
    rw [hcs_eq]; dsimp only [gtFwdDynScratchLen]; omega
  have h_s_le_t : scratchPtr ≤ jTailsPtr := by
    rw [hjT_eq, Nat.add_assoc]; exact Nat.le_add_right _ _
  have h_s_le_h : scratchPtr ≤ jHeadsPtr := by
    rw [hjH_eq, Nat.add_assoc]; exact Nat.le_add_right _ _
  have h_vn_le_t : jVsPtr + J.n ≤ jTailsPtr := by
    rw [hjV_eq, hjT_eq]; exact Nat.le_add_right _ _
  have h_em_le_t : jEsPtr + J.m ≤ jTailsPtr := by rw [hjE_eq, hjT_eq]
  have h_t_le_h : jTailsPtr ≤ jHeadsPtr := by rw [hjT_eq, hjH_eq]; omega
  have h_tm_le_h : jTailsPtr + jEs.length ≤ jHeadsPtr := by
    rw [hjT_eq, hjH_eq, hjE_len]; omega
  have h_t_ub : jTailsPtr + jEs.length ≤ scratchPtr + sLen := by
    rw [hjT_eq, hjE_len]; dsimp only [sLen, gtFwdDynScratchLen]; omega
  have h_h_ub : jHeadsPtr + jEs.length ≤ scratchPtr + sLen := by
    rw [hjH_eq, hjE_len]; dsimp only [sLen, gtFwdDynScratchLen]; omega
  have hjEB : jEsPtr + jEs.length < 2 ^ w := by rw [hjE_eq, hjE_len]; omega
  have hjTB : jTailsPtr + jEs.length < 2 ^ w := lt_of_le_of_lt h_t_ub hscB
  have hjHB : jHeadsPtr + jEs.length < 2 ^ w := lt_of_le_of_lt h_h_ub hscB
  have hjT_disjJ : ∀ i < jEs.length, ∀ k < dynGraphSize vCapJ eCapJ, jPtr + k ≠ jTailsPtr + i :=
    fun i hi k hk => by
      rcases hdisjJ k hk with h | h
      · exact Nat.ne_of_lt (lt_of_lt_of_le h (le_trans h_s_le_t (Nat.le_add_right _ _)))
      · exact Nat.ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left hi _) h_t_ub) h)
  have hjH_disjJ : ∀ i < jEs.length, ∀ k < dynGraphSize vCapJ eCapJ, jPtr + k ≠ jHeadsPtr + i :=
    fun i hi k hk => by
      rcases hdisjJ k hk with h | h
      · exact Nat.ne_of_lt (lt_of_lt_of_le h (le_trans h_s_le_h (Nat.le_add_right _ _)))
      · exact Nat.ne_of_gt (lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left hi _) h_h_ub) h)
  have hdisjT_E : ∀ i < jEs.length, ∀ k < jEs.length, jEsPtr + k ≠ jTailsPtr + i :=
    fun i _ k hk => Nat.ne_of_lt (lt_of_lt_of_le (Nat.add_lt_add_left (hjE_len ▸ hk) _)
      (le_trans h_em_le_t (Nat.le_add_right _ _)))
  have hdisjH_E : ∀ i < jEs.length, ∀ k < jEs.length, jEsPtr + k ≠ jHeadsPtr + i :=
    fun i _ k hk => Nat.ne_of_lt (lt_of_lt_of_le (Nat.add_lt_add_left (hjE_len ▸ hk) _)
      (le_trans h_em_le_t (le_trans h_t_le_h (Nat.le_add_right _ _))))
  have hdisjTH : ∀ i < jEs.length, ∀ k < jEs.length, jTailsPtr + k ≠ jHeadsPtr + i :=
    fun i _ k hk => Nat.ne_of_lt (lt_of_lt_of_le (Nat.add_lt_add_left hk _)
      (le_trans h_tm_le_h (Nat.le_add_right _ _)))
  have hEAt4_j : ListAt st4.mem jEsPtr jEs := hEAt4
  have hDynJ4 : DynGraphAt st4.mem jPtr vCapJ eCapJ J := by
    refine hDynJ.of_agree fun addr ha1 ha2 => ?_
    have hdj := hdisjJ (addr - jPtr) (Nat.sub_lt_left_of_lt_add ha1 ha2)
    rw [Nat.add_sub_cancel' ha1] at hdj
    exact hfr4_out addr hdj
  let rOrigDyn : ℕ → ℕ := fun r =>
    match r with
    | 0 => hPtr | 1 => jPtr | 2 => mEmbPtr | 3 => scratchPtr | 4 => outPtr
    | 5 => vCapJ | 6 => eCapJ | 7 => J.n | 8 => J.m
    | 9 => jVsPtr | 10 => jEsPtr | 11 => jTailsPtr | 12 => jHeadsPtr | _ => coreScratch
  have hOrig5 : ∀ r < 14, st4.regs r = rOrigDyn r := fun r hr => by
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨
        r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hr0
    · exact hr1
    · exact hr2
    · exact hr3
    · exact hr4
    · exact hr5
    · exact hr6
    · exact hr7
    · exact hr8
    · exact hr9
    · exact hr10
    · exact hr11
    · exact hr12
    · exact hr13
  dsimp only [gtForwardDynPrepE2Stmt]
  obtain ⟨o, st5, c5, hrun5, hpost5, hcost5⟩ := gtFillTailHead_triple (vCapJ := vCapJ) (eCapJ := eCapJ)
      (J := J) (jEs := jEs) (rOrig := rOrigDyn) hpOps hw16 hjB
      hjEB hjTB hjHB hjE_iff hDynJ4 hEAt4_j hjT_disjJ hjH_disjJ
      hdisjT_E hdisjH_E hdisjTH st4 ω
      ⟨rfl, hr1, hr8.trans hjE_len.symm, hr10, hr11, hr12, hOrig5⟩
  cases o; swap; exact False.elim hpost5
  rcases hpost5 with ⟨_, _, _, _, _, _, hOrig6, hTH5, hfr5⟩
  refine ⟨.normal, st5, c5, hrun5, ?_, ?_⟩
  · have hfr5_out : ∀ addr, addr < scratchPtr ∨ scratchPtr + sLen ≤ addr → st5.mem addr = mem addr :=
      fun addr ha => by
        have haT : addr < jTailsPtr ∨ jTailsPtr + jEs.length ≤ addr := by
          rcases ha with h | h
          · exact Or.inl (lt_of_lt_of_le h h_s_le_t)
          · exact Or.inr (le_trans h_t_ub h)
        have haH : addr < jHeadsPtr ∨ jHeadsPtr + jEs.length ≤ addr := by
          rcases ha with h | h
          · exact Or.inl (lt_of_lt_of_le h h_s_le_h)
          · exact Or.inr (le_trans h_h_ub h)
        exact (hfr5 addr haT haH).trans (hfr4_out addr ha)
    have hVAt5 : ListAt st5.mem jVsPtr jVs := fun i hi => by
      have hi_n : i < J.n := hjV_len ▸ hi
      have hlt_t : jVsPtr + i < jTailsPtr :=
        lt_of_lt_of_le (Nat.add_lt_add_left hi_n _) h_vn_le_t
      have hlt_h : jVsPtr + i < jHeadsPtr := lt_of_lt_of_le hlt_t h_t_le_h
      rw [hfr5 _ (Or.inl hlt_t) (Or.inl hlt_h)]
      exact hVAt4 i hi
    have hEAt5 : ListAt st5.mem jEsPtr jEs := fun i hi => by
      have hi_m : i < J.m := hjE_len ▸ hi
      have hlt_t : jEsPtr + i < jTailsPtr :=
        lt_of_lt_of_le (Nat.add_lt_add_left hi_m _) h_em_le_t
      have hlt_h : jEsPtr + i < jHeadsPtr := lt_of_lt_of_le hlt_t h_t_le_h
      rw [hfr5 _ (Or.inl hlt_t) (Or.inl hlt_h)]
      exact hEAt4_j i hi
    have hTAt5 : ListAt st5.mem jTailsPtr jTails := fun i hi => by
      simp only [jTails, List.length_map] at hi
      exact (hTH5 i hi hi).1
    have hHAt5 : ListAt st5.mem jHeadsPtr jHeads := fun i hi => by
      simp only [jHeads, List.length_map] at hi
      exact (hTH5 i hi hi).2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hVAt5, hEAt5, hTAt5, hHAt5, hfr5_out⟩
    · have h := hOrig6 0 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig6 1 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig6 2 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig6 3 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig6 4 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig6 7 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig6 8 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig6 9 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig6 10 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig6 11 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig6 12 (by decide); dsimp only [rOrigDyn] at h; exact h
    · have h := hOrig6 13 (by decide); dsimp only [rOrigDyn] at h; exact h
  · dsimp only at hcost5
    rw [hjE_len, Nat.mul_comm] at hcost5
    exact hcost5

theorem gtForwardDyn_prepEPhase {w vCapJ eCapJ rawEsLen : ℕ} {p : Program}
    {bSort bOps bGT : ℕ} {J : MGraph}
    {hPtr jPtr mEmbPtr scratchPtr outPtr : ℕ} {mem : ℕ → ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort)) :
    Triple w p
      (gtDynPrepVMid w vCapJ eCapJ rawEsLen J hPtr jPtr mEmbPtr scratchPtr outPtr mem)
      (gtForwardDynPrepEStmt bOps bGT)
      (normalPost (gtDynPrepPost J rawEsLen hPtr jPtr mEmbPtr scratchPtr outPtr mem))
      (fun _ => 250 * J.m * (Nat.log 2 (J.m + 1) + 1) + 300 * J.m + 210) := by
  intro st2 ω hMid
  dsimp only [gtForwardDynPrepEStmt]
  refine runs_start_le ?_
  refine runs_seq_triple_le
    (gtForwardDyn_prepE1Phase (vCapJ := vCapJ) (eCapJ := eCapJ) (rawEsLen := rawEsLen)
      (J := J) hpGT hpSort)
    hMid ?_
  intro st4 hMidE
  refine runs_triple_le
    (gtForwardDyn_prepE2Phase (vCapJ := vCapJ) (eCapJ := eCapJ) (rawEsLen := rawEsLen)
      (J := J) hpOps)
    hMidE (fun _ _ h => h) ?_
  omega

theorem gtForwardDyn_prepPhase {w vCapJ eCapJ rawEsLen : ℕ} {p : Program}
    {bSort bOps bGT : ℕ} {J : MGraph}
    {hPtr jPtr mEmbPtr scratchPtr outPtr : ℕ} {mem : ℕ → ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort)) :
    Triple w p
      (gtDynPrepPre w vCapJ eCapJ rawEsLen J hPtr jPtr mEmbPtr scratchPtr outPtr mem)
      (gtForwardDynPrepStmt bOps bGT)
      (normalPost (gtDynPrepPost J rawEsLen hPtr jPtr mEmbPtr scratchPtr outPtr mem))
      (fun _ =>
        250 * J.n * (Nat.log 2 (J.n + 1) + 1) +
        250 * J.m * (Nat.log 2 (J.m + 1) + 1) +
        300 * (J.n + J.m) + 612) := by
  intro st ω hPre
  dsimp only [gtForwardDynPrepStmt]
  refine runs_start_le ?_
  refine runs_seq_triple_le
    (gtForwardDyn_prepVPhase (vCapJ := vCapJ) (eCapJ := eCapJ) (rawEsLen := rawEsLen)
      (J := J) hpGT hpSort)
    hPre ?_
  intro st2 hMid
  refine runs_triple_le
    (gtForwardDyn_prepEPhase (vCapJ := vCapJ) (eCapJ := eCapJ) (rawEsLen := rawEsLen)
      (J := J) hpOps hpGT hpSort)
    hMid (fun _ _ h => h) ?_
  omega

end

end MinCostFlow.DynSpanner.Program
