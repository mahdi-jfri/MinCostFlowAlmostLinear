module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepRotTour

import WordRAM.Tactic

/-!
# Phase 4 edit-vertex root collection for `T₀` (`AssemblyFirstStepRotEdits`)

Verifies `asmFirstCollectRotEditsStmt fVertRoot` (`AssemblyFirstStepRotRaw.lean`): scans
`OrdEditsAt mem₀ edits ed editWords`, appending `a.rf.root v` for every vertex named by `ed` into
`outPtr` (updating `mem[cntAddr]` and advancing `hp` by `≤ 2 * H.querySpace` per edit), preserving
`TR.rep`, `ZeroFrom`, frame, and paying `≤ 2 * ed.length * (H.mul * ordStoreLog eCap + 60) + 30`
amortized against `TR.phi`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

public section

private lemma rotEditVertList_append (rt : ℕ → ℕ) (A B : List OrdEdit) :
    rotEditVertList rt (A ++ B) = rotEditVertList rt A ++ rotEditVertList rt B := by
  induction A with
  | nil => rfl
  | cons e r ih => cases e <;> simp [rotEditVertList, ih]

private lemma ordEditVert_subset_ordEditVerts {ed : List OrdEdit} {e : OrdEdit} (he : e ∈ ed) :
    OrdEdit.verts e ⊆ ordEditVerts ed := by
  induction ed with
  | nil => cases he
  | cons a r ih =>
    rcases List.mem_cons.mp he with rfl | hr
    · exact Finset.subset_union_left
    · exact (ih hr).trans Finset.subset_union_right

set_option maxHeartbeats 600000 in
/-- **Verification of `asmFirstCollectRotEditsStmt`**: scans `edits` (`OrdEditsAt`), appending
`rotEditVertList a.rf.root ed` onto `L0` at `outPtr` and updating `mem[cntAddr]`. -/
theorem asmFirstCollectRotEdits_runs {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w fVertRoot vCap eCap tourH edits editWords outPtr cntAddr rotCap hBase pos : ℕ} {p : Program}
    (H : AsmFirstTourRootAt TR w p fVertRoot)
    (hTR_loc : ∀ v e, (TR v e).Local)
    {ed : List OrdEdit} {a : AsmTourAbs} {tx₀ : (TR vCap eCap).τ}
    {L0 : List ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (htour_w : tourH < 2 ^ w) (hvCap_w : vCap < 2 ^ w)
    (hEd : OrdEditsAt mem₀ edits ed editWords) (hEd_le : edits + editWords ≤ hBase)
    (hEd_disj : ∀ x, edits ≤ x → x < edits + editWords →
      ¬ (TR vCap eCap).foot tourH tx₀ x ∧ (x < outPtr ∨ outPtr + rotCap ≤ x) ∧ x ≠ cntAddr)
    (hV_ok : ∀ v ∈ ordEditVerts ed, v < vCap)
    (hrep : (TR vCap eCap).rep tourH a tx₀ mem₀)
    (hfoot : ∀ x, (TR vCap eCap).foot tourH tx₀ x → x < hBase)
    (hout_lt : outPtr + rotCap ≤ hBase) (hcnt_lt : cntAddr < hBase)
    (hcnt_disj : cntAddr < outPtr ∨ outPtr + rotCap ≤ cntAddr)
    (hout_nf : ∀ x, outPtr ≤ x → x < outPtr + rotCap → ¬ (TR vCap eCap).foot tourH tx₀ x)
    (hcnt_nf : ¬ (TR vCap eCap).foot tourH tx₀ cntAddr)
    (hL0_len : L0.length + 2 * ed.length ≤ rotCap)
    (hcnt_mem : mem₀ cntAddr = L0.length)
    (hL0_at : ListAt mem₀ outPtr L0)
    (hz : ZeroFrom mem₀ hBase)
    (hsp : hBase + 2 * ed.length * H.querySpace < 2 ^ w) :
    let outL := L0 ++ rotEditVertList a.rf.root ed
    ∃ hEnd st' cost tx',
      Runs w p ω (asmFirstCollectRotEditsStmt fVertRoot)
        (startState [tourH, edits, outPtr, cntAddr, hBase] mem₀ pos) (.returned hEnd) st' cost ∧
      (TR vCap eCap).rep tourH a tx' st'.mem ∧
      st'.mem cntAddr = outL.length ∧
      ListAt st'.mem outPtr outL ∧
      hBase ≤ hEnd ∧ hEnd ≤ hBase + 2 * ed.length * H.querySpace ∧
      ZeroFrom st'.mem hEnd ∧
      (∀ x < hBase, ¬ (TR vCap eCap).foot tourH tx₀ x →
        (x < outPtr ∨ outPtr + rotCap ≤ x) → x ≠ cntAddr → st'.mem x = mem₀ x) ∧
      (∀ x, (TR vCap eCap).foot tourH tx' x →
        (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < hEnd)) ∧
      cost + (TR vCap eCap).phi tourH tx' st'.mem ≤
        2 * ed.length * (H.mul * ordStoreLog eCap + 60) + 30 +
          (TR vCap eCap).phi tourH tx₀ mem₀ := by
  intro outL
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have hEdLen : mem₀ edits = ed.length := by
    have h1 := congrArg List.length hEd.1
    rw [readOrdEdits, (decodeOrdEdits_len _ _ _).1] at h1; exact h1
  have hEdL_w : ed.length < 2 ^ w := by
    have hge : ∀ (m a : ℕ), m ≤ (decodeOrdEdits mem₀ m a).2.sum := by
      intro m; induction m with
      | zero => intro _; simp [decodeOrdEdits]
      | succ k ih =>
        intro a; simp only [decodeOrdEdits, List.sum_cons]
        have hpos : 1 ≤ (decodeOrdEdit mem₀ a).2 := by unfold decodeOrdEdit; split_ifs <;> dsimp only <;> omega
        have := ih (a + (decodeOrdEdit mem₀ a).2); omega
    have := hge (mem₀ edits) (edits + 1)
    have h2 := hEd.2.1; omega
  set s0 := startState [tourH, edits, outPtr, cntAddr, hBase] mem₀ pos
  set r1 := Function.update s0.regs 5 ed.length
  set r2 := Function.update r1 6 (edits + 1)
  set r3 := Function.update r2 7 0
  have ha5 : Runs w p ω (.assign 5 (.load (.reg 1))) s0 .normal ⟨mem₀, r1, pos⟩ 3 :=
    runs_assign_iff.mpr ⟨ed.length, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [s0, startState])) hEdLen, rfl, rfl, rfl⟩
  have ha6 : Runs w p ω (.assign 6 (.bin .add (.reg 1) (.const 1))) ⟨mem₀, r1, pos⟩ .normal ⟨mem₀, r2, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨edits + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, s0, startState]))
      (Expr.eval_const h1w) (by have := hEd.2.1; omega), rfl, rfl, rfl⟩
  have ha7 : Runs w p ω (.assign 7 (.const 0)) ⟨mem₀, r2, pos⟩ .normal ⟨mem₀, r3, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  have hloop : ∀ (k : ℕ) (hk : k ≤ ed.length) (cur : ℕ) (stK : State) (txK : (TR vCap eCap).τ),
      edits < cur → cur + (decodeOrdEdits mem₀ (ed.length - k) cur).2.sum ≤ edits + editWords →
      (decodeOrdEdits mem₀ (ed.length - k) cur).1 = ed.drop k →
      stK.regs 0 = tourH → stK.regs 2 = outPtr → stK.regs 3 = cntAddr →
      hBase ≤ stK.regs 4 → stK.regs 4 ≤ hBase + 2 * k * H.querySpace →
      stK.regs 5 = ed.length → stK.regs 6 = cur → stK.regs 7 = k →
      (TR vCap eCap).rep tourH a txK stK.mem →
      stK.mem cntAddr = (L0 ++ rotEditVertList a.rf.root (ed.take k)).length →
      ListAt stK.mem outPtr (L0 ++ rotEditVertList a.rf.root (ed.take k)) →
      ZeroFrom stK.mem (stK.regs 4) →
      (∀ x < hBase, ¬ (TR vCap eCap).foot tourH tx₀ x →
        (x < outPtr ∨ outPtr + rotCap ≤ x) → x ≠ cntAddr → stK.mem x = mem₀ x) →
      (∀ x, (TR vCap eCap).foot tourH txK x →
        (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < stK.regs 4)) →
      ∃ st1 c1 tx1,
        Runs w p ω (forUp 7 (.reg 5) (asmFirstCollectRotEditsBody fVertRoot)) stK .normal st1 c1 ∧
        hBase ≤ st1.regs 4 ∧ st1.regs 4 ≤ hBase + 2 * ed.length * H.querySpace ∧
        (TR vCap eCap).rep tourH a tx1 st1.mem ∧
        st1.mem cntAddr = outL.length ∧
        ListAt st1.mem outPtr outL ∧
        ZeroFrom st1.mem (st1.regs 4) ∧
        (∀ x < hBase, ¬ (TR vCap eCap).foot tourH tx₀ x →
          (x < outPtr ∨ outPtr + rotCap ≤ x) → x ≠ cntAddr → st1.mem x = mem₀ x) ∧
        (∀ x, (TR vCap eCap).foot tourH tx1 x →
          (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < st1.regs 4)) ∧
        c1 + (TR vCap eCap).phi tourH tx1 st1.mem ≤
          2 * (ed.length - k) * (H.mul * ordStoreLog eCap + 60) + 6 + (TR vCap eCap).phi tourH txK stK.mem := by
    intro k
    induction hrem : ed.length - k generalizing k with
    | zero =>
      intro hk cur stK txK _ _ _ _ _ _ hge hhi r5k _ r7k hrepK hcntK hLK hzK hfrK hftK
      have hkEq : k = ed.length := by omega
      subst hkEq; rw [List.take_length] at hcntK hLK
      have hcond : (Expr.bin .lt (.reg 7) (.reg 5)).eval w stK = some 0 := by
        simp [Expr.eval, r5k, r7k, BinOp.eval, h0w]
      exact ⟨stK, 4, txK, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        hge, hhi, hrepK, hcntK, hLK, hzK, hfrK, hftK, by omega⟩
    | succ d ih =>
      intro hk cur stK txK hclo hchi hdec r0k r2k r3k hge hhi r5k r6k r7k hrepK hcntK hLK hzK hfrK hftK
      have hklt : k < ed.length := by omega
      simp only [decodeOrdEdits, List.sum_cons] at hchi hdec
      set rec0 := decodeOrdEdit mem₀ cur
      have hdrop : ed.drop k = ed[k]'hklt :: ed.drop (k + 1) := List.drop_eq_getElem_cons hklt
      rw [hdrop] at hdec
      have heq_head : rec0.1 = ed[k]'hklt := (List.cons.inj hdec).1
      have heq_tail : (decodeOrdEdits mem₀ d (cur + rec0.2)).1 = ed.drop (k + 1) := (List.cons.inj hdec).2
      have htake : ed.take (k + 1) = ed.take k ++ [rec0.1] := by
        rw [heq_head]; exact List.take_succ_eq_append_getElem hklt
      have hrec_mem : rec0.1 ∈ ed := heq_head ▸ List.getElem_mem hklt
      have hV_rec : ∀ v ∈ OrdEdit.verts rec0.1, v < vCap := fun v hv =>
        hV_ok v (ordEditVert_subset_ordEditVerts hrec_mem hv)
      have hed_eq : ∀ x, cur ≤ x → x < cur + rec0.2 → stK.mem x = mem₀ x := fun x hx1 hx2 => by
        obtain ⟨h1, h2, h3⟩ := hEd_disj x (by omega) (by omega)
        exact hfrK x (by omega) h1 h2 h3
      set Lk := L0 ++ rotEditVertList a.rf.root (ed.take k)
      have hLk_len : Lk.length ≤ L0.length + 2 * k := by
        have := rotEditVertList_length_le a.rf.root (ed.take k)
        simp only [Lk, List.length_append, List.length_take, Nat.min_eq_left (by omega : k ≤ ed.length)] at this ⊢
        omega
      have hmul_step : 2 * k * H.querySpace + 2 * H.querySpace = 2 * (k + 1) * H.querySpace := by ring
      have hmul_le : 2 * (k + 1) * H.querySpace ≤ 2 * ed.length * H.querySpace :=
        Nat.mul_le_mul_right _ (by omega)
      have hq1 : 1 ≤ H.querySpace := H.querySpace_ge
      have hbody : ∃ stA cA txA,
          Runs w p ω (asmFirstCollectRotEditsBody fVertRoot) stK .normal stA cA ∧
          stA.regs 0 = tourH ∧ stA.regs 2 = outPtr ∧ stA.regs 3 = cntAddr ∧
          hBase ≤ stA.regs 4 ∧ stA.regs 4 ≤ hBase + 2 * (k + 1) * H.querySpace ∧
          stA.regs 5 = ed.length ∧ stA.regs 6 = cur + rec0.2 ∧ stA.regs 7 = k ∧
          (TR vCap eCap).rep tourH a txA stA.mem ∧
          stA.mem cntAddr = (L0 ++ rotEditVertList a.rf.root (ed.take (k + 1))).length ∧
          ListAt stA.mem outPtr (L0 ++ rotEditVertList a.rf.root (ed.take (k + 1))) ∧
          ZeroFrom stA.mem (stA.regs 4) ∧
          (∀ x < hBase, ¬ (TR vCap eCap).foot tourH tx₀ x →
            (x < outPtr ∨ outPtr + rotCap ≤ x) → x ≠ cntAddr → stA.mem x = mem₀ x) ∧
          (∀ x, (TR vCap eCap).foot tourH txA x →
            (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < stA.regs 4)) ∧
          cA + (TR vCap eCap).phi tourH txA stA.mem ≤
            2 * H.mul * ordStoreLog eCap + 110 + (TR vCap eCap).phi tourH txK stK.mem := by
        set tag := mem₀ cur
        have hrec_pos : 2 ≤ rec0.2 := by dsimp only [rec0, decodeOrdEdit]; split_ifs <;> dsimp only <;> omega
        have hm0 : stK.mem cur = tag := hed_eq cur le_rfl (by omega)
        set rA := Function.update stK.regs 8 tag
        have h8 : Runs w p ω (.assign 8 (.load (.reg 6))) stK .normal ⟨stK.mem, rA, stK.pos⟩ 3 :=
          runs_assign_iff.mpr ⟨tag, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r6k) hm0, rfl, rfl, rfl⟩
        by_cases ht0 : tag = 0
        · have hrec : rec0 = (.dropEdge (mem₀ (cur + 1)), 2) := by
            simp [rec0, decodeOrdEdit, tag, ht0]
          have heC0 : (Expr.bin .eq (.reg 8) (.const 0)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 1 := by
            simp [Expr.eval, rA, ht0, BinOp.eval, h0w, h1w]
          set rB := Function.update rA 6 (cur + 2)
          have h6s : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 2))) ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 4 :=
            runs_assign_iff.mpr ⟨cur + 2, Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r6k])) (Expr.eval_const h2w) (by rw [hrec] at hchi; dsimp only at hchi; omega), rfl, rfl, rfl⟩
          have hseq : L0 ++ rotEditVertList a.rf.root (ed.take (k + 1)) = Lk := by
            rw [htake, rotEditVertList_append, hrec]; simp [Lk, rotEditVertList]
          refine ⟨⟨stK.mem, rB, stK.pos⟩, _, txK,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h8,
              runs_cond_iff.mpr ⟨1, 4, heC0, by simpa using h6s, rfl⟩, rfl⟩),
            by simp [rB, rA, r0k], by simp [rB, rA, r2k], by simp [rB, rA, r3k],
            by simp [rB, rA]; omega, by simp [rB, rA]; omega,
            by simp [rB, rA, r5k], by simp [rB, hrec], by simp [rB, rA, r7k],
            hrepK, by rw [hseq]; exact hcntK, by rw [hseq]; exact hLK,
            by simpa [rB, rA] using hzK, hfrK, by simpa [rB, rA] using hftK,
            by simp only [Expr.size]; omega⟩
        · have heC0 : (Expr.bin .eq (.reg 8) (.const 0)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 0 := by
            simp [Expr.eval, rA, ht0, BinOp.eval, h0w]
          by_cases ht12 : tag = 1 ∨ tag = 2
          · have hrec : rec0 = (.moveEnds (mem₀ (cur + 1)) (mem₀ (cur + 2))
                ((readList mem₀ (cur + 4) (mem₀ (cur + 3))).map endOfKey).toFinset (decide (tag = 2)),
                4 + mem₀ (cur + 3)) := by
              simp [rec0, decodeOrdEdit, tag, ht0, ht12]
            have hrec2 : rec0.2 = 4 + mem₀ (cur + 3) := by rw [hrec]
            have heC12 : (Expr.bin .add (.bin .eq (.reg 8) (.const 1)) (.bin .eq (.reg 8) (.const 2))).eval w
                ⟨stK.mem, rA, stK.pos⟩ = some 1 := by
              rcases ht12 with h | h <;> simp [Expr.eval, rA, h, BinOp.eval, h0w, h1w, h2w]
            set v0 := mem₀ (cur + 1)
            set v0' := mem₀ (cur + 2)
            have hv1 := hV_rec v0 (by rw [hrec]; simp [OrdEdit.verts, v0])
            have hv2 := hV_rec v0' (by rw [hrec]; simp [OrdEdit.verts, v0'])
            have hm1 : stK.mem (cur + 1) = v0 := hed_eq (cur + 1) (by omega) (by omega)
            have hm2 : stK.mem (cur + 2) = v0' := hed_eq (cur + 2) (by omega) (by omega)
            set rB := Function.update rA 9 v0
            set rC := Function.update rB 10 v0'
            have hrC4 : rC 4 = stK.regs 4 := by simp [rC, rB, rA]
            have h9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 6) (.const 1))))
                ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 5 :=
              runs_assign_iff.mpr ⟨v0, Expr.eval_load_of_eq
                (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r6k])) (Expr.eval_const h1w) (by omega)) hm1, rfl, rfl, rfl⟩
            have h10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 6) (.const 2))))
                ⟨stK.mem, rB, stK.pos⟩ .normal ⟨stK.mem, rC, stK.pos⟩ 5 :=
              runs_assign_iff.mpr ⟨v0', Expr.eval_load_of_eq
                (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, r6k])) (Expr.eval_const h2w) (by omega)) hm2, rfl, rfl, rfl⟩
            obtain ⟨stP, cP, hp', txP, hrP, hrP4, hrP_oth, hhp_lo, hhp_hi, hrepP, hcntP, hLP, hzP, hfrP, hftP, hcP⟩ :=
              rotPushTwo_runs (st := ⟨stK.mem, rC, stK.pos⟩) (L := Lk) (v1 := v0) (v2 := v0') (ω := ω)
                H hTR_loc hw16 htour_w (by simp [rC, rB, rA, r0k]) (by simp [rC, rB, rA, r2k])
                (by simp [rC, rB, rA, r3k]) (by simp [rC, rB]) (by simp [rC])
                (by simpa [rC, rB, rA] using hge) (by simp only [hrC4]; omega)
                hout_lt hcnt_lt hcnt_disj (by omega) hcntK hLK hv1 hv2 hvCap_w hrepK hfoot
                (by simpa [rC, rB, rA] using hftK) hout_nf hcnt_nf (by simpa [rC, rB, rA] using hzK)
            have hstP6 : stP.regs 6 = cur := by
              rw [hrP_oth 6 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r6k]
            have hm3 : stP.mem (cur + 3) = mem₀ (cur + 3) := by
              obtain ⟨h1, h2, h3⟩ := hEd_disj (cur + 3) (by omega) (by omega)
              exact (hfrP (cur + 3) (by omega) h1 h2 h3).trans (hfrK (cur + 3) (by omega) h1 h2 h3)
            set rD := Function.update stP.regs 9 (mem₀ (cur + 3))
            set rE := Function.update rD 6 (cur + rec0.2)
            have h9s : Runs w p ω (.assign 9 (.load (.bin .add (.reg 6) (.const 3)))) stP .normal ⟨stP.mem, rD, stP.pos⟩ 5 :=
              runs_assign_iff.mpr ⟨mem₀ (cur + 3), Expr.eval_load_of_eq
                (Expr.eval_add (Expr.eval_reg_of_eq hstP6) (Expr.eval_const h3w) (by omega)) hm3, rfl, rfl, rfl⟩
            have h6s : Runs w p ω (.assign 6 (.bin .add (.bin .add (.reg 6) (.const 4)) (.reg 9)))
                ⟨stP.mem, rD, stP.pos⟩ .normal ⟨stP.mem, rE, stP.pos⟩ 6 := by
              have hr6 : rD 6 = cur := by simp [rD, hstP6]
              have hr9 : rD 9 = mem₀ (cur + 3) := by simp [rD]
              have he1 : (Expr.bin .add (.reg 6) (.const 4)).eval w ⟨stP.mem, rD, stP.pos⟩ = some (cur + 4) :=
                Expr.eval_add (Expr.eval_reg_of_eq hr6) (Expr.eval_const h4w) (by omega)
              have he2 : (Expr.bin .add (.bin .add (.reg 6) (.const 4)) (.reg 9)).eval w ⟨stP.mem, rD, stP.pos⟩ =
                  some (cur + 4 + mem₀ (cur + 3)) := Expr.eval_add he1 (Expr.eval_reg_of_eq hr9) (by omega)
              rw [show cur + 4 + mem₀ (cur + 3) = cur + rec0.2 by omega] at he2
              exact runs_assign_iff.mpr ⟨cur + rec0.2, he2, rfl, rfl, rfl⟩
            have hseq : L0 ++ rotEditVertList a.rf.root (ed.take (k + 1)) = Lk ++ [a.rf.root v0, a.rf.root v0'] := by
              rw [htake, rotEditVertList_append, hrec]; simp [Lk, rotEditVertList, List.append_assoc, v0, v0']
            have hTail := runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9s, h6s, rfl⟩)
            have hPT := runs_seqSnoc hrP hTail
            refine ⟨⟨stP.mem, rE, stP.pos⟩, _, txP,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, h8,
                runs_cond_iff.mpr ⟨0, _, heC0, by
                  simp only [↓reduceIte]
                  exact runs_cond_iff.mpr ⟨1, _, heC12, by
                    simp only [one_ne_zero, ↓reduceIte]
                    exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9,
                      runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10, hPT, rfl⟩), rfl⟩), rfl⟩, rfl⟩, rfl⟩),
              by simp only [rE, rD, Function.update_of_ne (by decide : (0 : ℕ) ≠ 6),
                Function.update_of_ne (by decide : (0 : ℕ) ≠ 9)]
                 rw [hrP_oth 0 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r0k],
              by simp only [rE, rD, Function.update_of_ne (by decide : (2 : ℕ) ≠ 6),
                Function.update_of_ne (by decide : (2 : ℕ) ≠ 9)]
                 rw [hrP_oth 2 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r2k],
              by simp only [rE, rD, Function.update_of_ne (by decide : (3 : ℕ) ≠ 6),
                Function.update_of_ne (by decide : (3 : ℕ) ≠ 9)]
                 rw [hrP_oth 3 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r3k],
              by simp only [rE, rD, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6),
                Function.update_of_ne (by decide : (4 : ℕ) ≠ 9), hrP4]; simp only [hrC4] at hhp_lo; omega,
              by simp only [rE, rD, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6),
                Function.update_of_ne (by decide : (4 : ℕ) ≠ 9), hrP4]; simp only [hrC4] at hhp_hi; omega,
              by simp only [rE, rD, Function.update_of_ne (by decide : (5 : ℕ) ≠ 6),
                Function.update_of_ne (by decide : (5 : ℕ) ≠ 9)]
                 rw [hrP_oth 5 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r5k],
              by simp [rE],
              by simp only [rE, rD, Function.update_of_ne (by decide : (7 : ℕ) ≠ 6),
                Function.update_of_ne (by decide : (7 : ℕ) ≠ 9)]
                 rw [hrP_oth 7 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r7k],
              hrepP, by rw [hseq]; simpa using hcntP, by rw [hseq]; exact hLP,
              by simpa [rE, rD, hrP4] using hzP,
              fun x hx hnf hout hnc => (hfrP x hx hnf hout hnc).trans (hfrK x hx hnf hout hnc),
              by simpa [rE, rD, hrP4] using hftP,
              by
                simp only [Expr.size]
                have hphiC : (TR vCap eCap).phi tourH txK ({ mem := stK.mem, regs := rC, pos := stK.pos } : State).mem =
                    (TR vCap eCap).phi tourH txK stK.mem := rfl
                omega⟩
          · have hnt1 : tag ≠ 1 := fun h => ht12 (Or.inl h)
            have hnt2 : tag ≠ 2 := fun h => ht12 (Or.inr h)
            have heC12 : (Expr.bin .add (.bin .eq (.reg 8) (.const 1)) (.bin .eq (.reg 8) (.const 2))).eval w
                ⟨stK.mem, rA, stK.pos⟩ = some 0 := by
              simp [Expr.eval, rA, hnt1, hnt2, BinOp.eval, h0w, h1w, h2w]
            set v0 := mem₀ (cur + 1)
            have hrec_info : rec0.2 = (if tag = 3 then 4 else 3) ∧
                OrdEdit.verts rec0.1 = {v0} ∧ rotEditVertList a.rf.root [rec0.1] = [a.rf.root v0] := by
              by_cases ht3 : tag = 3
              · simp [rec0, decodeOrdEdit, tag, ht3, OrdEdit.verts, rotEditVertList, v0]
              · simp [rec0, decodeOrdEdit, tag, ht0, ht12, ht3, OrdEdit.verts, rotEditVertList, v0]
            have hv1 := hV_rec v0 (by rw [hrec_info.2.1]; simp)
            have hm1 : stK.mem (cur + 1) = v0 := hed_eq (cur + 1) (by omega) (by omega)
            set rB := Function.update rA 9 v0
            have hrB4 : rB 4 = stK.regs 4 := by simp [rB, rA]
            have h9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 6) (.const 1))))
                ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 5 :=
              runs_assign_iff.mpr ⟨v0, Expr.eval_load_of_eq
                (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r6k])) (Expr.eval_const h1w) (by omega)) hm1, rfl, rfl, rfl⟩
            obtain ⟨stP, cP, hp', txP, hrP, hrP4, hrP_oth, hhp_lo, hhp_hi, hrepP, hcntP, hLP, hzP, hfrP, hftP, hcP⟩ :=
              rotPushOne_runs (st := ⟨stK.mem, rB, stK.pos⟩) (L := Lk) (v1 := v0) (ω := ω)
                H hTR_loc hw16 htour_w (by simp [rB, rA, r0k]) (by simp [rB, rA, r2k])
                (by simp [rB, rA, r3k]) (by simp [rB])
                (by simpa [rB, rA] using hge) (by simp only [hrB4]; omega)
                hout_lt hcnt_lt hcnt_disj (by omega) hcntK hLK hv1 hvCap_w hrepK hfoot
                (by simpa [rB, rA] using hftK) hout_nf hcnt_nf (by simpa [rB, rA] using hzK)
            have hstP6 : stP.regs 6 = cur := by
              rw [hrP_oth 6 (by decide) (by decide) (by decide)]; simp [rB, rA, r6k]
            have hstP8 : stP.regs 8 = tag := by
              rw [hrP_oth 8 (by decide) (by decide) (by decide)]; simp [rB, rA]
            set rD := Function.update stP.regs 6 (cur + rec0.2)
            have hstep6 : ∃ c6, Runs w p ω
                (.cond (.bin .eq (.reg 8) (.const 3))
                  (.assign 6 (.bin .add (.reg 6) (.const 4)))
                  (.assign 6 (.bin .add (.reg 6) (.const 3))))
                stP .normal ⟨stP.mem, rD, stP.pos⟩ c6 ∧ c6 ≤ 10 := by
              by_cases ht3 : tag = 3
              · have he3 : (Expr.bin .eq (.reg 8) (.const 3)).eval w stP = some 1 := by
                  simp [Expr.eval, hstP8, ht3, BinOp.eval, h1w, h3w]
                have hr4 : rec0.2 = 4 := by simp [hrec_info.1, ht3]
                have ha6' : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 4))) stP .normal ⟨stP.mem, rD, stP.pos⟩ 4 :=
                  runs_assign_iff.mpr ⟨cur + 4, Expr.eval_add (Expr.eval_reg_of_eq hstP6) (Expr.eval_const h4w) (by omega),
                    rfl, by simp [rD, hr4], rfl⟩
                exact ⟨_, runs_cond_iff.mpr ⟨1, 4, he3, by simpa using ha6', rfl⟩, by simp [Expr.size]⟩
              · have he3 : (Expr.bin .eq (.reg 8) (.const 3)).eval w stP = some 0 := by
                  simp [Expr.eval, hstP8, ht3, BinOp.eval, h0w, h3w]
                have hr3' : rec0.2 = 3 := by simp [hrec_info.1, ht3]
                have ha6' : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 3))) stP .normal ⟨stP.mem, rD, stP.pos⟩ 4 :=
                  runs_assign_iff.mpr ⟨cur + 3, Expr.eval_add (Expr.eval_reg_of_eq hstP6) (Expr.eval_const h3w) (by omega),
                    rfl, by simp [rD, hr3'], rfl⟩
                exact ⟨_, runs_cond_iff.mpr ⟨0, 4, he3, by simpa using ha6', rfl⟩, by simp [Expr.size]⟩
            obtain ⟨c6, hr6, hc6⟩ := hstep6
            have hseq : L0 ++ rotEditVertList a.rf.root (ed.take (k + 1)) = Lk ++ [a.rf.root v0] := by
              rw [htake, rotEditVertList_append, hrec_info.2.2]; simp [Lk, List.append_assoc]
            have hPT := runs_seqSnoc hrP hr6
            refine ⟨⟨stP.mem, rD, stP.pos⟩, _, txP,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, h8,
                runs_cond_iff.mpr ⟨0, _, heC0, by
                  simp only [↓reduceIte]
                  exact runs_cond_iff.mpr ⟨0, _, heC12, by
                    simp only [↓reduceIte]
                    exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9, hPT, rfl⟩), rfl⟩, rfl⟩, rfl⟩),
              by simp only [rD, Function.update_of_ne (show (0 : ℕ) ≠ 6 by decide)]
                 rw [hrP_oth 0 (by decide) (by decide) (by decide)]; simp [rB, rA, r0k],
              by simp only [rD, Function.update_of_ne (show (2 : ℕ) ≠ 6 by decide)]
                 rw [hrP_oth 2 (by decide) (by decide) (by decide)]; simp [rB, rA, r2k],
              by simp only [rD, Function.update_of_ne (show (3 : ℕ) ≠ 6 by decide)]
                 rw [hrP_oth 3 (by decide) (by decide) (by decide)]; simp [rB, rA, r3k],
              by simp only [rD, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), hrP4]; simp only [hrB4] at hhp_lo; omega,
              by simp only [rD, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), hrP4]; simp only [hrB4] at hhp_hi; omega,
              by simp only [rD, Function.update_of_ne (show (5 : ℕ) ≠ 6 by decide)]
                 rw [hrP_oth 5 (by decide) (by decide) (by decide)]; simp [rB, rA, r5k],
              by simp [rD],
              by simp only [rD, Function.update_of_ne (show (7 : ℕ) ≠ 6 by decide)]
                 rw [hrP_oth 7 (by decide) (by decide) (by decide)]; simp [rB, rA, r7k],
              hrepP, by rw [hseq]; simpa using hcntP, by rw [hseq]; exact hLP,
              by simpa [rD, hrP4] using hzP,
              fun x hx hnf hout hnc => (hfrP x hx hnf hout hnc).trans (hfrK x hx hnf hout hnc),
              by simpa [rD, hrP4] using hftP,
              by
                simp only [Expr.size]
                have hphiC : (TR vCap eCap).phi tourH txK ({ mem := stK.mem, regs := rB, pos := stK.pos } : State).mem =
                    (TR vCap eCap).phi tourH txK stK.mem := rfl
                have h2m : 2 * H.mul * ordStoreLog eCap = 2 * (H.mul * ordStoreLog eCap) := by ring
                omega⟩
      obtain ⟨stA, cA, txA, hrA, r0A, r2A, r3A, hgeA, hhiA, r5A, r6A, r7A, hrepA, hcntA, hLA, hzA, hfrA, hftA, hcA⟩ := hbody
      set stB : State := ⟨stA.mem, Function.update stA.regs 7 (k + 1), stA.pos⟩
      have ha7s : Runs w p ω (.assign 7 (.bin .add (.reg 7) (.const 1))) stA .normal stB 4 :=
        runs_assign_iff.mpr ⟨k + 1, Expr.eval_add (Expr.eval_reg_of_eq r7A) (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
      obtain ⟨st1, c1, tx1, hr1, hge1, hhi1, hrep1, hcnt1, hL1, hz1, hfr1, hft1, hc1⟩ :=
        ih (k + 1) (by omega) (by omega) (cur + rec0.2) stB txA (by omega) (by omega) heq_tail
          (by simp [stB, r0A]) (by simp [stB, r2A]) (by simp [stB, r3A])
          (by simpa [stB] using hgeA) (by simpa [stB] using hhiA)
          (by simp [stB, r5A]) (by simp [stB, r6A]) (by simp [stB])
          hrepA hcntA hLA (by simpa [stB] using hzA) hfrA (by simpa [stB] using hftA)
      have hcond : (Expr.bin .lt (.reg 7) (.reg 5)).eval w stK = some 1 := by
        simp [Expr.eval, r5k, r7k, BinOp.eval, hklt, h1w]
      refine ⟨st1, _, tx1, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stB, _, c1, hcond, by decide,
        runs_seq_iff.mpr (Or.inr ⟨stA, cA, 4, hrA, ha7s, rfl⟩), hr1, rfl⟩)),
        hge1, hhi1, hrep1, hcnt1, hL1, hz1, hfr1, hft1, ?_⟩
      simp only [Expr.size]
      have hphiB : (TR vCap eCap).phi tourH txA stB.mem = (TR vCap eCap).phi tourH txA stA.mem := rfl
      have hexp : 2 * (d + 1) * (H.mul * ordStoreLog eCap + 60) =
          2 * d * (H.mul * ordStoreLog eCap + 60) + 2 * H.mul * ordStoreLog eCap + 120 := by ring
      omega
  obtain ⟨st1, c1, tx1, hrB, hge1, hhi1, hrep1, hcnt1, hL1, hz1, hfr1, hft1, hc1⟩ :=
    hloop 0 (Nat.zero_le _) (edits + 1) ⟨mem₀, r3, pos⟩ tx₀
      (by omega) (by have := hEd.2.1; rw [Nat.sub_zero, ← hEdLen]; omega)
      (by rw [Nat.sub_zero, ← hEdLen]; exact hEd.1)
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1, s0, startState])
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1, s0, startState])
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1]) (by simp [r3, r2]) (by simp [r3])
      hrep (by simpa [rotEditVertList] using hcnt_mem) (by simpa [rotEditVertList] using hL0_at)
      (by simpa [r3, r2, r1, s0, startState] using hz)
      (fun _ _ _ _ _ => rfl) (fun x hx => Or.inl hx)
  have hret : Runs w p ω (.ret (.reg 4)) st1 (.returned (st1.regs 4)) st1 2 :=
    runs_ret_iff.mpr ⟨st1.regs 4, Expr.eval_reg_of_eq rfl, rfl, rfl, rfl⟩
  have hseqLoop : Runs w p ω (forRange 7 (.const 0) (.reg 5) (asmFirstCollectRotEditsBody fVertRoot))
      ⟨mem₀, r2, pos⟩ .normal st1 (2 + c1 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha7, hrB, rfl⟩)
  exact ⟨st1.regs 4, st1, _, tx1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha5,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha6,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hseqLoop, hret, rfl⟩), rfl⟩), rfl⟩),
    hrep1, hcnt1, hL1, hge1, hhi1, hz1, hfr1, hft1, by
      simp only [Nat.sub_zero] at hc1
      have hphi0 : (TR vCap eCap).phi tourH tx₀ ({ mem := mem₀, regs := r3, pos := pos } : State).mem =
          (TR vCap eCap).phi tourH tx₀ mem₀ := rfl
      omega⟩

end

end MinCostFlow.SparseCore.Program
