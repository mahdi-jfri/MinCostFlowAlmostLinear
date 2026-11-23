module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepRotRaw

import WordRAM.Tactic

/-!
# Phase 4 tour-root collection for the batch of `T₀` (`AssemblyFirstStepRotTour`)

Verifies `asmFirstCollectRotBatchStmt fVertRoot` (`AssemblyFirstStepRotRaw.lean`).
* `rotPushTwo_runs`, `rotPushOne_runs`: query the tour root of one or two vertices through
  `fVertRoot` and append the roots to the list at `outPtr`.
* `asmFirstCollectRotBatch_runs`: scans `batch`, appending `a.rf.root v` for both vertices of each
  `.insert` / `.split` into `outPtr` (updating `mem[cntAddr]` and advancing `hp` by
  `≤ 2 * querySpace` per update), preserving `TR.rep`, `ZeroFrom` and the frame, and paying
  `≤ 2 * U.length * (H.mul * ordStoreLog eCap + 60) + 30` amortized against `TR.phi`.
The edit list is scanned in `AssemblyFirstStepRotEdits.lean`. -/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

public section

/-- Appends `t` at the end of the right-nested `;;` chain `s`. -/
@[expose] def seqSnoc : Stmt → Stmt → Stmt
  | .seq a b, t => .seq a (seqSnoc b t)
  | s, t => .seq s t

/-- Running a chain `s` and then `t` runs `seqSnoc s t`, with the cost of `s ;; t`. -/
lemma runs_seqSnoc {w : ℕ} {p : Program} {ω : ℕ → Bool} {t : Stmt} :
    ∀ {s : Stmt} {st st₁ st' : State} {c₁ c₂ : ℕ},
      Runs w p ω s st .normal st₁ c₁ → Runs w p ω t st₁ .normal st' c₂ →
      Runs w p ω (seqSnoc s t) st .normal st' (c₁ + c₂ + 1) := by
  intro s
  induction s with
  | seq a b _ ihb =>
    intro st st₁ st' c₁ c₂ hs ht
    rcases runs_seq_iff.mp hs with ⟨v, _, _, ho, _⟩ | ⟨s0, ca, cb, ha, hb, rfl⟩
    · cases ho
    exact runs_seq_iff.mpr (Or.inr ⟨s0, ca, cb + c₂ + 1, ha, ihb hb ht, by omega⟩)
  | _ =>
    intro st st₁ st' c₁ c₂ hs ht
    exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs, ht, rfl⟩)

/-- Shared helper for querying two vertices `v1, v2` (`reg 9, reg 10`) via `fVertRoot` and storing
their roots at `outPtr + cnt` and `outPtr + cnt + 1`, then incrementing `mem[cntAddr]` by `2`. -/
lemma rotPushTwo_runs {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w fVertRoot vCap eCap tourH outPtr cntAddr rotCap hBase : ℕ} {p : Program}
    (H : AsmFirstTourRootAt TR w p fVertRoot)
    (hTR_loc : ∀ v e, (TR v e).Local)
    {a : AsmTourAbs} {tx₀ tx : (TR vCap eCap).τ}
    {st : State} {L : List ℕ} {v1 v2 : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (htour_w : tourH < 2 ^ w)
    (h0 : st.regs 0 = tourH) (h2 : st.regs 2 = outPtr) (h3 : st.regs 3 = cntAddr)
    (h9 : st.regs 9 = v1) (h10 : st.regs 10 = v2)
    (hge : hBase ≤ st.regs 4) (hsp : st.regs 4 + 2 * H.querySpace < 2 ^ w)
    (hout_lt : outPtr + rotCap ≤ hBase) (hcnt_lt : cntAddr < hBase)
    (hcnt_disj : cntAddr < outPtr ∨ outPtr + rotCap ≤ cntAddr)
    (hL_len : L.length + 2 ≤ rotCap)
    (hcnt_mem : st.mem cntAddr = L.length)
    (hL_at : ListAt st.mem outPtr L)
    (hv1 : v1 < vCap) (hv2 : v2 < vCap) (hvCap_w : vCap < 2 ^ w)
    (hrep : (TR vCap eCap).rep tourH a tx st.mem)
    (hfoot0 : ∀ x, (TR vCap eCap).foot tourH tx₀ x → x < hBase)
    (hfoot : ∀ x, (TR vCap eCap).foot tourH tx x →
      (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < st.regs 4))
    (hout_nf : ∀ x, outPtr ≤ x → x < outPtr + rotCap → ¬ (TR vCap eCap).foot tourH tx₀ x)
    (hcnt_nf : ¬ (TR vCap eCap).foot tourH tx₀ cntAddr)
    (hz : ZeroFrom st.mem (st.regs 4)) :
    ∃ st' c hp' tx',
      Runs w p ω
        (.assign 11 (.reg 4) ;;
         .call 4 fVertRoot [.reg 0, .reg 9, .reg 4] ;;
         .assign 12 (.load (.reg 3)) ;;
         .store (.bin .add (.reg 2) (.reg 12)) (.load (.reg 11)) ;;
         .assign 11 (.reg 4) ;;
         .call 4 fVertRoot [.reg 0, .reg 10, .reg 4] ;;
         .store (.bin .add (.bin .add (.reg 2) (.reg 12)) (.const 1)) (.load (.reg 11)) ;;
         .store (.reg 3) (.bin .add (.reg 12) (.const 2)))
        st .normal st' c ∧
      st'.regs 4 = hp' ∧
      (∀ r, r ≠ 4 → r ≠ 11 → r ≠ 12 → st'.regs r = st.regs r) ∧
      st.regs 4 ≤ hp' ∧ hp' ≤ st.regs 4 + 2 * H.querySpace ∧
      (TR vCap eCap).rep tourH a tx' st'.mem ∧
      st'.mem cntAddr = L.length + 2 ∧
      ListAt st'.mem outPtr (L ++ [a.rf.root v1, a.rf.root v2]) ∧
      ZeroFrom st'.mem hp' ∧
      (∀ x < hBase, ¬ (TR vCap eCap).foot tourH tx₀ x →
        (x < outPtr ∨ outPtr + rotCap ≤ x) → x ≠ cntAddr → st'.mem x = st.mem x) ∧
      (∀ x, (TR vCap eCap).foot tourH tx' x →
        (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < hp')) ∧
      c + (TR vCap eCap).phi tourH tx' st'.mem ≤
        2 * H.mul * ordStoreLog eCap + 60 + (TR vCap eCap).phi tourH tx st.mem := by
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have hq1 : 1 ≤ H.querySpace := H.querySpace_ge
  set hp0 := st.regs 4
  have hft_lt : ∀ x, (TR vCap eCap).foot tourH tx x → x < hp0 := fun x hx => by
    rcases hfoot x hx with h0' | ⟨_, hhi⟩
    · have := hfoot0 x h0'; omega
    · exact hhi
  set rA := Function.update st.regs 11 hp0
  have ha11_1 : Runs w p ω (.assign 11 (.reg 4)) st .normal ⟨st.mem, rA, st.pos⟩ 2 :=
    runs_assign_iff.mpr ⟨hp0, Expr.eval_reg_of_eq rfl, rfl, rfl, rfl⟩
  -- Query 1
  obtain ⟨bd1, hbd1, o1, st1, c1, tx1, hr1, hrep1, hans1, hval1, hresp1, hcost1⟩ :=
    H.runs vCap eCap tourH v1 hp0 a tx st.mem st.pos ω
      htour_w hv1 (by omega) (by omega) hrep hft_lt hz (by omega)
  set hp1 := o1.value
  have hhp1_lo : hp0 + 1 ≤ hp1 := hval1
  have hhp1_hi : hp1 ≤ hp0 + H.querySpace := hresp1.2.1
  have hft1 : ∀ x, (TR vCap eCap).foot tourH tx1 x →
      (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < hp1) := fun x hx => by
    rcases hresp1.2.2.2.2 x hx with h0' | ⟨hlo, hhi⟩
    · rcases hfoot x h0' with ha0 | ⟨h1, h2⟩
      · exact Or.inl ha0
      · exact Or.inr ⟨h1, by omega⟩
    · exact Or.inr ⟨by omega, hhi⟩
  have heA1 : evalArgs w ⟨st.mem, rA, st.pos⟩ [.reg 0, .reg 9, .reg 4] = some [tourH, v1, hp0] :=
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, h0])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, h9])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, hp0])) <| evalArgs_nil _ _
  set rB := Function.update rA 4 hp1
  have hc1_run : Runs w p ω (.call 4 fVertRoot [.reg 0, .reg 9, .reg 4])
      ⟨st.mem, rA, st.pos⟩ .normal ⟨st1.mem, rB, st1.pos⟩
      (argsSize [.reg 0, .reg 9, .reg 4] + c1 + 1) :=
    runs_call_iff.mpr ⟨_, bd1, o1, st1, c1, heA1, hbd1, hr1, rfl, rfl, rfl⟩
  have hnf_cnt : ¬ (TR vCap eCap).foot tourH tx cntAddr := fun hf => by
    rcases hfoot _ hf with h0' | ⟨hlo, _⟩; exact hcnt_nf h0'; omega
  have hm1_cnt : st1.mem cntAddr = L.length := (hresp1.2.2.2.1 cntAddr (by omega) hnf_cnt).trans hcnt_mem
  set rC := Function.update rB 12 L.length
  have ha12 : Runs w p ω (.assign 12 (.load (.reg 3))) ⟨st1.mem, rB, st1.pos⟩ .normal ⟨st1.mem, rC, st1.pos⟩ 3 :=
    runs_assign_iff.mpr ⟨L.length, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [rB, rA, h3])) hm1_cnt, rfl, rfl, rfl⟩
  set m1 := Function.update st1.mem (outPtr + L.length) (a.rf.root v1)
  have hs1 : Runs w p ω (.store (.bin .add (.reg 2) (.reg 12)) (.load (.reg 11)))
      ⟨st1.mem, rC, st1.pos⟩ .normal ⟨m1, rC, st1.pos⟩ 6 :=
    runs_store_iff.mpr ⟨outPtr + L.length, a.rf.root v1,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC, rB, rA, h2])) (Expr.eval_reg_of_eq (by simp [rC])) (by omega),
      Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [rC, rB, rA])) hans1, rfl, rfl, rfl⟩
  have hnotft1_o1 : ¬ (TR vCap eCap).foot tourH tx1 (outPtr + L.length) := fun hf => by
    rcases hft1 _ hf with h0' | ⟨hlo, _⟩
    · exact hout_nf (outPtr + L.length) (by omega) (by omega) h0'
    · omega
  have hloc1 := hTR_loc vCap eCap tourH a tx1 st1.mem m1 fun x hx => by
    have hne : x ≠ outPtr + L.length := fun heq => hnotft1_o1 (heq ▸ hx)
    simp [m1, hne]
  have hrep1_m1 : (TR vCap eCap).rep tourH a tx1 m1 := hloc1.1 hrep1
  have hphi1_m1 : (TR vCap eCap).phi tourH tx1 m1 = (TR vCap eCap).phi tourH tx1 st1.mem := hloc1.2.symm
  have hz1_m1 : ZeroFrom m1 hp1 := fun x hx => by
    dsimp only [m1]; rw [Function.update_of_ne (by omega)]; exact hresp1.2.2.1 x hx
  have hft1_lt : ∀ x, (TR vCap eCap).foot tourH tx1 x → x < hp1 := fun x hx => by
    rcases hft1 x hx with h0' | ⟨_, hhi⟩; have := hfoot0 x h0'; omega; exact hhi
  set rD := Function.update rC 11 hp1
  have ha11_2 : Runs w p ω (.assign 11 (.reg 4)) ⟨m1, rC, st1.pos⟩ .normal ⟨m1, rD, st1.pos⟩ 2 :=
    runs_assign_iff.mpr ⟨hp1, Expr.eval_reg_of_eq (by simp [rC, rB]), rfl, rfl, rfl⟩
  -- Query 2
  obtain ⟨bd2, hbd2, o2, st2, c2, tx2, hr2, hrep2, hans2, hval2, hresp2, hcost2⟩ :=
    H.runs vCap eCap tourH v2 hp1 a tx1 m1 st1.pos ω
      htour_w hv2 (by omega) (by omega) hrep1_m1 hft1_lt hz1_m1 (by omega)
  set hp2 := o2.value
  have hhp2_lo : hp1 + 1 ≤ hp2 := hval2
  have hhp2_hi : hp2 ≤ hp1 + H.querySpace := hresp2.2.1
  have hft2 : ∀ x, (TR vCap eCap).foot tourH tx2 x →
      (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < hp2) := fun x hx => by
    rcases hresp2.2.2.2.2 x hx with h1 | ⟨hlo, hhi⟩
    · rcases hft1 x h1 with h0' | ⟨ha, hb⟩
      · exact Or.inl h0'
      · exact Or.inr ⟨ha, by omega⟩
    · exact Or.inr ⟨by omega, hhi⟩
  have heA2 : evalArgs w ⟨m1, rD, st1.pos⟩ [.reg 0, .reg 10, .reg 4] = some [tourH, v2, hp1] :=
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [rD, rC, rB, rA, h0])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [rD, rC, rB, rA, h10])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [rD, rC, rB])) <| evalArgs_nil _ _
  set rE := Function.update rD 4 hp2
  have hc2_run : Runs w p ω (.call 4 fVertRoot [.reg 0, .reg 10, .reg 4])
      ⟨m1, rD, st1.pos⟩ .normal ⟨st2.mem, rE, st2.pos⟩
      (argsSize [.reg 0, .reg 10, .reg 4] + c2 + 1) :=
    runs_call_iff.mpr ⟨_, bd2, o2, st2, c2, heA2, hbd2, hr2, rfl, rfl, rfl⟩
  set m2 := Function.update st2.mem (outPtr + L.length + 1) (a.rf.root v2)
  set m3 := Function.update m2 cntAddr (L.length + 2)
  have hs2 : Runs w p ω (.store (.bin .add (.bin .add (.reg 2) (.reg 12)) (.const 1)) (.load (.reg 11)))
      ⟨st2.mem, rE, st2.pos⟩ .normal ⟨m2, rE, st2.pos⟩ 8 := by
    have he1 : (Expr.bin .add (.reg 2) (.reg 12)).eval w ⟨st2.mem, rE, st2.pos⟩ = some (outPtr + L.length) :=
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [rE, rD, rC, rB, rA, h2]))
        (Expr.eval_reg_of_eq (by simp [rE, rD, rC])) (by omega)
    exact runs_store_iff.mpr ⟨outPtr + L.length + 1, a.rf.root v2,
      Expr.eval_add he1 (Expr.eval_const h1w) (by omega),
      Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [rE, rD])) hans2, rfl, rfl, rfl⟩
  have hs3 : Runs w p ω (.store (.reg 3) (.bin .add (.reg 12) (.const 2)))
      ⟨m2, rE, st2.pos⟩ .normal ⟨m3, rE, st2.pos⟩ 5 :=
    runs_store_iff.mpr ⟨cntAddr, L.length + 2,
      Expr.eval_reg_of_eq (by simp [rE, rD, rC, rB, rA, h3]),
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [rE, rD, rC])) (Expr.eval_const h2w) (by omega), rfl, rfl, rfl⟩
  have hnotft2_o2 : ¬ (TR vCap eCap).foot tourH tx2 (outPtr + L.length + 1) := fun hf => by
    rcases hft2 _ hf with h0' | ⟨hlo, _⟩
    · exact hout_nf (outPtr + L.length + 1) (by omega) (by omega) h0'
    · omega
  have hnotft2_cnt : ¬ (TR vCap eCap).foot tourH tx2 cntAddr := fun hf => by
    rcases hft2 _ hf with h0' | ⟨hlo, _⟩
    · exact hcnt_nf h0'
    · omega
  have hloc2 := hTR_loc vCap eCap tourH a tx2 st2.mem m3 fun x hx => by
    have hne1 : x ≠ outPtr + L.length + 1 := fun heq => hnotft2_o2 (heq ▸ hx)
    have hne2 : x ≠ cntAddr := fun heq => hnotft2_cnt (heq ▸ hx)
    simp [m3, m2, hne1, hne2]
  have hfr_m3 : ∀ x < hBase, ¬ (TR vCap eCap).foot tourH tx₀ x →
      x ≠ outPtr + L.length → x ≠ outPtr + L.length + 1 → x ≠ cntAddr → m3 x = st.mem x :=
    fun x hx hnf hne1 hne2 hne3 => by
      have hnf1 : ¬ (TR vCap eCap).foot tourH tx1 x := fun hf => by
        rcases hft1 x hf with h0' | ⟨hlo, _⟩; exact hnf h0'; omega
      have hnf0 : ¬ (TR vCap eCap).foot tourH tx x := fun hf => by
        rcases hfoot x hf with h0' | ⟨hlo, _⟩; exact hnf h0'; omega
      dsimp only [m3, m2]; rw [Function.update_of_ne hne3, Function.update_of_ne hne2]
      rw [hresp2.2.2.2.1 x (by omega) hnf1]
      dsimp only [m1]; rw [Function.update_of_ne hne1]
      exact hresp1.2.2.2.1 x (by omega) hnf0
  refine ⟨⟨m3, rE, st2.pos⟩, _, hp2, tx2,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha11_1,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hc1_run,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha12,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha11_2,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, hc2_run,
                runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs2, hs3, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by simp [rE],
    fun r hr4 hr11 hr12 => by simp [rE, rD, rC, rB, rA, hr4, hr11, hr12],
    by omega, by omega, hloc2.1 hrep2, by simp [m3], ?_, ?_, ?_, hft2, ?_⟩
  · intro i hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hi
    have hne_c : outPtr + i ≠ cntAddr := by rcases hcnt_disj with h | h <;> omega
    by_cases hil : i < L.length
    · rw [List.getElem_append_left hil]
      dsimp only; rw [hfr_m3 (outPtr + i) (by omega) (hout_nf _ (by omega) (by omega)) (by omega) (by omega) hne_c]
      exact hL_at i hil
    · by_cases hi1 : i = L.length
      · subst hi1
        rw [List.getElem_append_right le_rfl]; simp only [Nat.sub_self, List.getElem_cons_zero]
        dsimp only [m3, m2]
        rw [Function.update_of_ne hne_c, Function.update_of_ne (by omega : outPtr + L.length ≠ outPtr + L.length + 1)]
        rw [hresp2.2.2.2.1 (outPtr + L.length) (by omega) hnotft1_o1]; simp [m1]
      · have hi2 : i = L.length + 1 := by omega
        subst hi2
        rw [List.getElem_append_right (by omega)]
        simp only [show L.length + 1 - L.length = 1 by omega, List.getElem_cons_succ, List.getElem_cons_zero]
        dsimp only [m3]; rw [Function.update_of_ne hne_c]
        simp only [m2, show outPtr + (L.length + 1) = outPtr + L.length + 1 by omega, Function.update_self]
  · intro x hx
    dsimp only [m3, m2]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hresp2.2.2.1 x hx
  · intro x hx hnf hout hnc
    exact hfr_m3 x hx hnf (by rcases hout with h | h <;> omega) (by rcases hout with h | h <;> omega) hnc
  · rw [hloc2.2.symm]; rw [hphi1_m1] at hcost2; simp only [argsSize, Expr.size]
    rw [show 2 * H.mul * ordStoreLog eCap = 2 * (H.mul * ordStoreLog eCap) from Nat.mul_assoc _ _ _]
    omega

/-- Shared helper for querying one vertex `v1` (`reg 9`) via `fVertRoot` and storing its root at
`outPtr + cnt`, then incrementing `mem[cntAddr]` by `1`. -/
lemma rotPushOne_runs {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w fVertRoot vCap eCap tourH outPtr cntAddr rotCap hBase : ℕ} {p : Program}
    (H : AsmFirstTourRootAt TR w p fVertRoot)
    (hTR_loc : ∀ v e, (TR v e).Local)
    {a : AsmTourAbs} {tx₀ tx : (TR vCap eCap).τ}
    {st : State} {L : List ℕ} {v1 : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (htour_w : tourH < 2 ^ w)
    (h0 : st.regs 0 = tourH) (h2 : st.regs 2 = outPtr) (h3 : st.regs 3 = cntAddr)
    (h9 : st.regs 9 = v1)
    (hge : hBase ≤ st.regs 4) (hsp : st.regs 4 + H.querySpace < 2 ^ w)
    (hout_lt : outPtr + rotCap ≤ hBase) (hcnt_lt : cntAddr < hBase)
    (hcnt_disj : cntAddr < outPtr ∨ outPtr + rotCap ≤ cntAddr)
    (hL_len : L.length + 1 ≤ rotCap)
    (hcnt_mem : st.mem cntAddr = L.length)
    (hL_at : ListAt st.mem outPtr L)
    (hv1 : v1 < vCap) (hvCap_w : vCap < 2 ^ w)
    (hrep : (TR vCap eCap).rep tourH a tx st.mem)
    (hfoot0 : ∀ x, (TR vCap eCap).foot tourH tx₀ x → x < hBase)
    (hfoot : ∀ x, (TR vCap eCap).foot tourH tx x →
      (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < st.regs 4))
    (hout_nf : ∀ x, outPtr ≤ x → x < outPtr + rotCap → ¬ (TR vCap eCap).foot tourH tx₀ x)
    (hcnt_nf : ¬ (TR vCap eCap).foot tourH tx₀ cntAddr)
    (hz : ZeroFrom st.mem (st.regs 4)) :
    ∃ st' c hp' tx',
      Runs w p ω
        (.assign 11 (.reg 4) ;;
         .call 4 fVertRoot [.reg 0, .reg 9, .reg 4] ;;
         .assign 12 (.load (.reg 3)) ;;
         .store (.bin .add (.reg 2) (.reg 12)) (.load (.reg 11)) ;;
         .store (.reg 3) (.bin .add (.reg 12) (.const 1)))
        st .normal st' c ∧
      st'.regs 4 = hp' ∧
      (∀ r, r ≠ 4 → r ≠ 11 → r ≠ 12 → st'.regs r = st.regs r) ∧
      st.regs 4 ≤ hp' ∧ hp' ≤ st.regs 4 + H.querySpace ∧
      (TR vCap eCap).rep tourH a tx' st'.mem ∧
      st'.mem cntAddr = L.length + 1 ∧
      ListAt st'.mem outPtr (L ++ [a.rf.root v1]) ∧
      ZeroFrom st'.mem hp' ∧
      (∀ x < hBase, ¬ (TR vCap eCap).foot tourH tx₀ x →
        (x < outPtr ∨ outPtr + rotCap ≤ x) → x ≠ cntAddr → st'.mem x = st.mem x) ∧
      (∀ x, (TR vCap eCap).foot tourH tx' x →
        (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < hp')) ∧
      c + (TR vCap eCap).phi tourH tx' st'.mem ≤
        H.mul * ordStoreLog eCap + 35 + (TR vCap eCap).phi tourH tx st.mem := by
  have h1w : 1 < 2 ^ w := by omega
  have hq1 : 1 ≤ H.querySpace := H.querySpace_ge
  set hp0 := st.regs 4
  have hft_lt : ∀ x, (TR vCap eCap).foot tourH tx x → x < hp0 := fun x hx => by
    rcases hfoot x hx with h0' | ⟨_, hhi⟩; have := hfoot0 x h0'; omega; exact hhi
  set rA := Function.update st.regs 11 hp0
  have ha11 : Runs w p ω (.assign 11 (.reg 4)) st .normal ⟨st.mem, rA, st.pos⟩ 2 :=
    runs_assign_iff.mpr ⟨hp0, Expr.eval_reg_of_eq rfl, rfl, rfl, rfl⟩
  obtain ⟨bd1, hbd1, o1, st1, c1, tx1, hr1, hrep1, hans1, hval1, hresp1, hcost1⟩ :=
    H.runs vCap eCap tourH v1 hp0 a tx st.mem st.pos ω
      htour_w hv1 (by omega) (by omega) hrep hft_lt hz (by omega)
  set hp1 := o1.value
  have hhp1_hi : hp1 ≤ hp0 + H.querySpace := hresp1.2.1
  have hft1 : ∀ x, (TR vCap eCap).foot tourH tx1 x →
      (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < hp1) := fun x hx => by
    rcases hresp1.2.2.2.2 x hx with h0' | ⟨hlo, hhi⟩
    · rcases hfoot x h0' with ha0 | ⟨h1, h2⟩
      · exact Or.inl ha0
      · exact Or.inr ⟨h1, by omega⟩
    · exact Or.inr ⟨by omega, hhi⟩
  have heA1 : evalArgs w ⟨st.mem, rA, st.pos⟩ [.reg 0, .reg 9, .reg 4] = some [tourH, v1, hp0] :=
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, h0])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, h9])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, hp0])) <| evalArgs_nil _ _
  set rB := Function.update rA 4 hp1
  have hc1_run : Runs w p ω (.call 4 fVertRoot [.reg 0, .reg 9, .reg 4])
      ⟨st.mem, rA, st.pos⟩ .normal ⟨st1.mem, rB, st1.pos⟩
      (argsSize [.reg 0, .reg 9, .reg 4] + c1 + 1) :=
    runs_call_iff.mpr ⟨_, bd1, o1, st1, c1, heA1, hbd1, hr1, rfl, rfl, rfl⟩
  have hnf_cnt : ¬ (TR vCap eCap).foot tourH tx cntAddr := fun hf => by
    rcases hfoot _ hf with h0' | ⟨hlo, _⟩; exact hcnt_nf h0'; omega
  have hm1_cnt : st1.mem cntAddr = L.length := (hresp1.2.2.2.1 cntAddr (by omega) hnf_cnt).trans hcnt_mem
  set rC := Function.update rB 12 L.length
  have ha12 : Runs w p ω (.assign 12 (.load (.reg 3))) ⟨st1.mem, rB, st1.pos⟩ .normal ⟨st1.mem, rC, st1.pos⟩ 3 :=
    runs_assign_iff.mpr ⟨L.length, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [rB, rA, h3])) hm1_cnt, rfl, rfl, rfl⟩
  set m1 := Function.update st1.mem (outPtr + L.length) (a.rf.root v1)
  set m2 := Function.update m1 cntAddr (L.length + 1)
  have hs1 : Runs w p ω (.store (.bin .add (.reg 2) (.reg 12)) (.load (.reg 11)))
      ⟨st1.mem, rC, st1.pos⟩ .normal ⟨m1, rC, st1.pos⟩ 6 :=
    runs_store_iff.mpr ⟨outPtr + L.length, a.rf.root v1,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC, rB, rA, h2])) (Expr.eval_reg_of_eq (by simp [rC])) (by omega),
      Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [rC, rB, rA])) hans1, rfl, rfl, rfl⟩
  have hs2 : Runs w p ω (.store (.reg 3) (.bin .add (.reg 12) (.const 1)))
      ⟨m1, rC, st1.pos⟩ .normal ⟨m2, rC, st1.pos⟩ 5 :=
    runs_store_iff.mpr ⟨cntAddr, L.length + 1,
      Expr.eval_reg_of_eq (by simp [rC, rB, rA, h3]),
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC])) (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
  have hnotft1_o1 : ¬ (TR vCap eCap).foot tourH tx1 (outPtr + L.length) := fun hf => by
    rcases hft1 _ hf with h0' | ⟨hlo, _⟩; exact hout_nf _ (by omega) (by omega) h0'; omega
  have hnotft1_cnt : ¬ (TR vCap eCap).foot tourH tx1 cntAddr := fun hf => by
    rcases hft1 _ hf with h0' | ⟨hlo, _⟩; exact hcnt_nf h0'; omega
  have hloc1 := hTR_loc vCap eCap tourH a tx1 st1.mem m2 fun x hx => by
    have hne1 : x ≠ outPtr + L.length := fun heq => hnotft1_o1 (heq ▸ hx)
    have hne2 : x ≠ cntAddr := fun heq => hnotft1_cnt (heq ▸ hx)
    simp [m2, m1, hne1, hne2]
  refine ⟨⟨m2, rC, st1.pos⟩, _, hp1, tx1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha11,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hc1_run,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha12,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1, hs2, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by simp [rC, rB],
    fun r hr4 hr11 hr12 => by simp [rC, rB, rA, hr4, hr11, hr12],
    by omega, hhp1_hi, hloc1.1 hrep1, by simp [m2], ?_, ?_, ?_, hft1, ?_⟩
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    have hne_c : outPtr + i ≠ cntAddr := by rcases hcnt_disj with h | h <;> omega
    by_cases hil : i < L.length
    · rw [List.getElem_append_left hil]
      have hnf0 : ¬ (TR vCap eCap).foot tourH tx (outPtr + i) := fun hf => by
        rcases hfoot _ hf with h0' | ⟨hlo, _⟩; exact hout_nf _ (by omega) (by omega) h0'; omega
      dsimp only [m2, m1]; rw [Function.update_of_ne hne_c, Function.update_of_ne (by omega)]
      exact (hresp1.2.2.2.1 (outPtr + i) (by omega) hnf0).trans (hL_at i hil)
    · have hi1 : i = L.length := by omega
      subst hi1; rw [List.getElem_append_right le_rfl]; simp [m2, m1, hne_c]
  · intro x hx; dsimp only [m2, m1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hresp1.2.2.1 x hx
  · intro x hx hnf hout hnc
    have hnf0 : ¬ (TR vCap eCap).foot tourH tx x := fun hf => by
      rcases hfoot x hf with h0' | ⟨hlo, _⟩; exact hnf h0'; omega
    dsimp only [m2, m1]
    rw [Function.update_of_ne hnc, Function.update_of_ne (by rcases hout with h | h <;> omega)]
    exact hresp1.2.2.2.1 x (by omega) hnf0
  · rw [hloc1.2.symm]; simp only [argsSize, Expr.size]; omega

/-! ## Verification of `asmFirstCollectRotBatchStmt` -/

private lemma updVerts_subset_batchVerts {u : Update} {U : List Update} (hu : u ∈ U) :
    updVerts u ⊆ batchVerts U := by
  induction U with
  | nil => cases hu
  | cons a r ih =>
    rcases List.mem_cons.mp hu with rfl | hr
    · exact Finset.subset_union_left
    · exact (ih hr).trans Finset.subset_union_right

set_option maxHeartbeats 600000 in
theorem asmFirstCollectRotBatch_runs {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w fVertRoot vCap eCap tourH batch words outPtr cntAddr rotCap hBase pos : ℕ} {p : Program}
    (H : AsmFirstTourRootAt TR w p fVertRoot)
    (hTR_loc : ∀ v e, (TR v e).Local)
    {G₀ : MGraph} {U : List Update} {a : AsmTourAbs} {tx₀ : (TR vCap eCap).τ}
    {L0 : List ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (htour_w : tourH < 2 ^ w) (hvCap_w : vCap < 2 ^ w)
    (hBat : BatchAt mem₀ batch G₀ U words) (hBat_le : batch + words ≤ hBase)
    (hBat_disj : ∀ x, batch ≤ x → x < batch + words →
      ¬ (TR vCap eCap).foot tourH tx₀ x ∧ (x < outPtr ∨ outPtr + rotCap ≤ x) ∧ x ≠ cntAddr)
    (hV_ok : ∀ v ∈ batchVerts U, v < vCap)
    (hrep : (TR vCap eCap).rep tourH a tx₀ mem₀)
    (hfoot : ∀ x, (TR vCap eCap).foot tourH tx₀ x → x < hBase)
    (hout_lt : outPtr + rotCap ≤ hBase) (hcnt_lt : cntAddr < hBase)
    (hcnt_disj : cntAddr < outPtr ∨ outPtr + rotCap ≤ cntAddr)
    (hout_nf : ∀ x, outPtr ≤ x → x < outPtr + rotCap → ¬ (TR vCap eCap).foot tourH tx₀ x)
    (hcnt_nf : ¬ (TR vCap eCap).foot tourH tx₀ cntAddr)
    (hL0_len : L0.length + 2 * U.length ≤ rotCap)
    (hcnt_mem : mem₀ cntAddr = L0.length)
    (hL0_at : ListAt mem₀ outPtr L0)
    (hz : ZeroFrom mem₀ hBase)
    (hsp : hBase + 2 * U.length * H.querySpace < 2 ^ w) :
    let outL := L0 ++ rotBatchVertList a.rf.root U
    ∃ hEnd st' cost tx',
      Runs w p ω (asmFirstCollectRotBatchStmt fVertRoot)
        (startState [tourH, batch, outPtr, cntAddr, hBase] mem₀ pos) (.returned hEnd) st' cost ∧
      (TR vCap eCap).rep tourH a tx' st'.mem ∧
      st'.mem cntAddr = outL.length ∧
      ListAt st'.mem outPtr outL ∧
      hBase ≤ hEnd ∧ hEnd ≤ hBase + 2 * U.length * H.querySpace ∧
      ZeroFrom st'.mem hEnd ∧
      (∀ x < hBase, ¬ (TR vCap eCap).foot tourH tx₀ x →
        (x < outPtr ∨ outPtr + rotCap ≤ x) → x ≠ cntAddr → st'.mem x = mem₀ x) ∧
      (∀ x, (TR vCap eCap).foot tourH tx' x →
        (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < hEnd)) ∧
      cost + (TR vCap eCap).phi tourH tx' st'.mem ≤
        2 * U.length * (H.mul * ordStoreLog eCap + 60) + 30 +
          (TR vCap eCap).phi tourH tx₀ mem₀ := by
  intro outL
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have h5w : 5 < 2 ^ w := by omega
  have hUL : U.length < 2 ^ w := by have := batchBodyAt_length_le hBat.2.2; have := hBat.1; omega
  have hrot_app : ∀ (k : ℕ) (hk : k < U.length),
      rotBatchVertList a.rf.root (U.take (k + 1)) =
        rotBatchVertList a.rf.root (U.take k) ++ rotBatchVertList a.rf.root [U[k]'hk] := by
    intro k hk; rw [List.take_succ_eq_append_getElem hk]
    have : ∀ (A B : List Update), rotBatchVertList a.rf.root (A ++ B) =
        rotBatchVertList a.rf.root A ++ rotBatchVertList a.rf.root B := by
      intro A B; induction A with
      | nil => rfl
      | cons u r ih => cases u <;> simp [rotBatchVertList, ih]
    exact this _ _
  have hV_take : ∀ {k : ℕ} (hk : k < U.length), ∀ v ∈ updVerts (U[k]'hk), v < vCap := by
    intro k hk v hv
    exact hV_ok v (updVerts_subset_batchVerts (List.getElem_mem hk) hv)
  set s0 := startState [tourH, batch, outPtr, cntAddr, hBase] mem₀ pos
  set r1 := Function.update s0.regs 5 U.length
  set r2 := Function.update r1 6 (batch + 1)
  set r3 := Function.update r2 7 0
  have ha5 : Runs w p ω (.assign 5 (.load (.reg 1))) s0 .normal ⟨mem₀, r1, pos⟩ 3 :=
    runs_assign_iff.mpr ⟨U.length, Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [s0, startState])) hBat.2.1, rfl, rfl, rfl⟩
  have ha6 : Runs w p ω (.assign 6 (.bin .add (.reg 1) (.const 1))) ⟨mem₀, r1, pos⟩ .normal ⟨mem₀, r2, pos⟩ 4 :=
    runs_assign_iff.mpr ⟨batch + 1, Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, s0, startState]))
      (Expr.eval_const h1w) (by have := hBat.1; omega), rfl, rfl, rfl⟩
  have ha7 : Runs w p ω (.assign 7 (.const 0)) ⟨mem₀, r2, pos⟩ .normal ⟨mem₀, r3, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  have hloop : ∀ (k : ℕ) (hk : k ≤ U.length) (cur W : ℕ) (stK : State) (txK : (TR vCap eCap).τ),
      batch < cur → cur + W ≤ batch + words →
      BatchBodyAt mem₀ cur (G₀.applyBatch (U.take k)) (U.drop k) W →
      stK.regs 0 = tourH → stK.regs 2 = outPtr → stK.regs 3 = cntAddr →
      hBase ≤ stK.regs 4 → stK.regs 4 ≤ hBase + 2 * k * H.querySpace →
      stK.regs 5 = U.length → stK.regs 6 = cur → stK.regs 7 = k →
      (TR vCap eCap).rep tourH a txK stK.mem →
      stK.mem cntAddr = (L0 ++ rotBatchVertList a.rf.root (U.take k)).length →
      ListAt stK.mem outPtr (L0 ++ rotBatchVertList a.rf.root (U.take k)) →
      ZeroFrom stK.mem (stK.regs 4) →
      (∀ x < hBase, ¬ (TR vCap eCap).foot tourH tx₀ x →
        (x < outPtr ∨ outPtr + rotCap ≤ x) → x ≠ cntAddr → stK.mem x = mem₀ x) →
      (∀ x, (TR vCap eCap).foot tourH txK x →
        (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < stK.regs 4)) →
      ∃ st1 c1 tx1,
        Runs w p ω (forUp 7 (.reg 5) (asmFirstCollectRotBatchBody fVertRoot)) stK .normal st1 c1 ∧
        hBase ≤ st1.regs 4 ∧ st1.regs 4 ≤ hBase + 2 * U.length * H.querySpace ∧
        (TR vCap eCap).rep tourH a tx1 st1.mem ∧
        st1.mem cntAddr = outL.length ∧
        ListAt st1.mem outPtr outL ∧
        ZeroFrom st1.mem (st1.regs 4) ∧
        (∀ x < hBase, ¬ (TR vCap eCap).foot tourH tx₀ x →
          (x < outPtr ∨ outPtr + rotCap ≤ x) → x ≠ cntAddr → st1.mem x = mem₀ x) ∧
        (∀ x, (TR vCap eCap).foot tourH tx1 x →
          (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < st1.regs 4)) ∧
        c1 + (TR vCap eCap).phi tourH tx1 st1.mem ≤
          2 * (U.length - k) * (H.mul * ordStoreLog eCap + 60) + 6 + (TR vCap eCap).phi tourH txK stK.mem := by
    intro k
    induction hrem : U.length - k generalizing k with
    | zero =>
      intro hk cur W stK txK _ _ _ _ _ _ hge hhi r5k _ r7k hrepK hcntK hLK hzK hfrK hftK
      have hkEq : k = U.length := by omega
      subst hkEq; rw [List.take_length] at hcntK hLK
      have hcond : (Expr.bin .lt (.reg 7) (.reg 5)).eval w stK = some 0 := by
        simp [Expr.eval, r5k, r7k, BinOp.eval, h0w]
      exact ⟨stK, 4, txK, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
        hge, hhi, hrepK, hcntK, hLK, hzK, hfrK, hftK, by omega⟩
    | succ d ih =>
      intro hk cur W stK txK hclo hchi hBB r0k r2k r3k hge hhi r5k r6k r7k hrepK hcntK hLK hzK hfrK hftK
      have hklt : k < U.length := by omega
      obtain ⟨u, hu_eq⟩ : ∃ u, U[k]'hklt = u := ⟨_, rfl⟩
      have hdrop : U.drop k = u :: U.drop (k + 1) := by rw [← hu_eq]; exact List.drop_eq_getElem_cons hklt
      have htake : U.take (k + 1) = U.take k ++ [u] := by rw [← hu_eq]; exact List.take_succ_eq_append_getElem hklt
      rw [hdrop] at hBB
      obtain ⟨len, hlenW, huAt, hBBrest⟩ := hBB
      have hbat_eq : ∀ x, cur ≤ x → x < cur + len → stK.mem x = mem₀ x := fun x hx1 hx2 => by
        obtain ⟨h1, h2, h3⟩ := hBat_disj x (by omega) (by omega)
        exact hfrK x (by omega) h1 h2 h3
      set Lk := L0 ++ rotBatchVertList a.rf.root (U.take k)
      have hLk_len : Lk.length ≤ L0.length + 2 * k := by
        have := rotBatchVertList_length_le a.rf.root (U.take k)
        simp only [Lk, List.length_append, List.length_take, Nat.min_eq_left (by omega : k ≤ U.length)] at this ⊢
        omega
      have hmul_step : 2 * k * H.querySpace + 2 * H.querySpace = 2 * (k + 1) * H.querySpace := by ring
      have hmul_le : 2 * (k + 1) * H.querySpace ≤ 2 * U.length * H.querySpace :=
        Nat.mul_le_mul_right _ (by omega)
      have hbody : ∃ stA cA txA,
          Runs w p ω (asmFirstCollectRotBatchBody fVertRoot) stK .normal stA cA ∧
          stA.regs 0 = tourH ∧ stA.regs 2 = outPtr ∧ stA.regs 3 = cntAddr ∧
          hBase ≤ stA.regs 4 ∧ stA.regs 4 ≤ hBase + 2 * (k + 1) * H.querySpace ∧
          stA.regs 5 = U.length ∧ stA.regs 6 = cur + len ∧ stA.regs 7 = k ∧
          (TR vCap eCap).rep tourH a txA stA.mem ∧
          stA.mem cntAddr = (L0 ++ rotBatchVertList a.rf.root (U.take (k + 1))).length ∧
          ListAt stA.mem outPtr (L0 ++ rotBatchVertList a.rf.root (U.take (k + 1))) ∧
          ZeroFrom stA.mem (stA.regs 4) ∧
          (∀ x < hBase, ¬ (TR vCap eCap).foot tourH tx₀ x →
            (x < outPtr ∨ outPtr + rotCap ≤ x) → x ≠ cntAddr → stA.mem x = mem₀ x) ∧
          (∀ x, (TR vCap eCap).foot tourH txA x →
            (TR vCap eCap).foot tourH tx₀ x ∨ (hBase ≤ x ∧ x < stA.regs 4)) ∧
          cA + (TR vCap eCap).phi tourH txA stA.mem ≤
            2 * H.mul * ordStoreLog eCap + 110 + (TR vCap eCap).phi tourH txK stK.mem := by
        have hrot_k := hrot_app k hklt
        rw [hu_eq] at hrot_k
        cases u with
        | insert e0 a0 b0 =>
          rcases huAt with ⟨rfl, hL⟩
          have hm0 : stK.mem cur = 0 := (hbat_eq cur le_rfl (by omega)).trans (by simpa using hL 0 (by simp))
          have hm2 : stK.mem (cur + 2) = a0 := (hbat_eq (cur + 2) (by omega) (by omega)).trans (by simpa using hL 2 (by simp))
          have hm3 : stK.mem (cur + 3) = b0 := (hbat_eq (cur + 3) (by omega) (by omega)).trans (by simpa using hL 3 (by simp))
          have hva := hV_take hklt a0 (by rw [hu_eq]; simp [updVerts])
          have hvb := hV_take hklt b0 (by rw [hu_eq]; simp [updVerts])
          set rA := Function.update stK.regs 8 0
          set rB := Function.update rA 9 a0
          set rC := Function.update rB 10 b0
          have hrC4 : rC 4 = stK.regs 4 := by simp [rC, rB, rA]
          have h8 : Runs w p ω (.assign 8 (.load (.reg 6))) stK .normal ⟨stK.mem, rA, stK.pos⟩ 3 :=
            runs_assign_iff.mpr ⟨0, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r6k) hm0, rfl, rfl, rfl⟩
          have heC : (Expr.bin .eq (.reg 8) (.const 0)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 1 := by
            simp [Expr.eval, rA, BinOp.eval, h0w, h1w]
          have h9 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 6) (.const 2))))
              ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨a0, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r6k])) (Expr.eval_const h2w) (by omega)) hm2, rfl, rfl, rfl⟩
          have h10 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 6) (.const 3))))
              ⟨stK.mem, rB, stK.pos⟩ .normal ⟨stK.mem, rC, stK.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨b0, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, r6k])) (Expr.eval_const h3w) (by omega)) hm3, rfl, rfl, rfl⟩
          obtain ⟨stP, cP, hp', txP, hrP, hrP4, hrP_oth, hhp_lo, hhp_hi, hrepP, hcntP, hLP, hzP, hfrP, hftP, hcP⟩ :=
            rotPushTwo_runs (st := ⟨stK.mem, rC, stK.pos⟩) (L := Lk) (v1 := a0) (v2 := b0) (ω := ω)
              H hTR_loc hw16 htour_w (by simp [rC, rB, rA, r0k]) (by simp [rC, rB, rA, r2k])
              (by simp [rC, rB, rA, r3k]) (by simp [rC, rB]) (by simp [rC])
              (by simpa [rC, rB, rA] using hge) (by simp only [hrC4]; omega)
              hout_lt hcnt_lt hcnt_disj (by omega) hcntK hLK hva hvb hvCap_w hrepK hfoot
              (by simpa [rC, rB, rA] using hftK) hout_nf hcnt_nf (by simpa [rC, rB, rA] using hzK)
          set rD := Function.update stP.regs 6 (cur + 4)
          have h6s : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 4))) stP .normal ⟨stP.mem, rD, stP.pos⟩ 4 :=
            runs_assign_iff.mpr ⟨cur + 4, Expr.eval_add
              (Expr.eval_reg_of_eq (by rw [hrP_oth 6 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r6k]))
              (Expr.eval_const h4w) (by omega), rfl, rfl, rfl⟩
          have hseq_L : L0 ++ rotBatchVertList a.rf.root (U.take (k + 1)) = Lk ++ [a.rf.root a0, a.rf.root b0] := by
            rw [hrot_k]; simp [Lk, rotBatchVertList, List.append_assoc]
          have hPT := runs_seqSnoc hrP h6s
          refine ⟨⟨stP.mem, rD, stP.pos⟩, _, txP,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h8,
              runs_cond_iff.mpr ⟨1, _, heC, by
                simp only [one_ne_zero, ↓reduceIte]
                exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9,
                  runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10, hPT, rfl⟩), rfl⟩), rfl⟩, rfl⟩),
            by simp only [rD, Function.update_of_ne (show (0 : ℕ) ≠ 6 by decide)]
               rw [hrP_oth 0 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r0k],
            by simp only [rD, Function.update_of_ne (show (2 : ℕ) ≠ 6 by decide)]
               rw [hrP_oth 2 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r2k],
            by simp only [rD, Function.update_of_ne (show (3 : ℕ) ≠ 6 by decide)]
               rw [hrP_oth 3 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r3k],
            by simp only [rD, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), hrP4]; simp only [hrC4] at hhp_lo; omega,
            by simp only [rD, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6), hrP4]; simp only [hrC4] at hhp_hi; omega,
            by simp only [rD, Function.update_of_ne (show (5 : ℕ) ≠ 6 by decide)]
               rw [hrP_oth 5 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r5k],
            by simp [rD],
            by simp only [rD, Function.update_of_ne (show (7 : ℕ) ≠ 6 by decide)]
               rw [hrP_oth 7 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r7k],
            hrepP, by rw [hseq_L]; simpa using hcntP, by rw [hseq_L]; exact hLP,
            by simpa [rD, hrP4] using hzP,
            fun x hx hnf hout hnc => (hfrP x hx hnf hout hnc).trans (hfrK x hx hnf hout hnc),
            by simpa [rD, hrP4] using hftP,
            by
              simp only [Expr.size]
              have hphiC : (TR vCap eCap).phi tourH txK ({ mem := stK.mem, regs := rC, pos := stK.pos } : State).mem =
                  (TR vCap eCap).phi tourH txK stK.mem := rfl
              omega⟩
        | delete e0 =>
          rcases huAt with ⟨rfl, hL⟩
          have hm0 : stK.mem cur = 1 := (hbat_eq cur le_rfl (by omega)).trans (by simpa using hL 0 (by simp))
          set rA := Function.update stK.regs 8 1
          set rB := Function.update rA 6 (cur + 2)
          have h8 : Runs w p ω (.assign 8 (.load (.reg 6))) stK .normal ⟨stK.mem, rA, stK.pos⟩ 3 :=
            runs_assign_iff.mpr ⟨1, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r6k) hm0, rfl, rfl, rfl⟩
          have heC0 : (Expr.bin .eq (.reg 8) (.const 0)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 0 := by
            simp [Expr.eval, rA, BinOp.eval, h0w]
          have heC1 : (Expr.bin .eq (.reg 8) (.const 1)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 1 := by
            simp [Expr.eval, rA, BinOp.eval, h1w]
          have h6s : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 2))) ⟨stK.mem, rA, stK.pos⟩ .normal ⟨stK.mem, rB, stK.pos⟩ 4 :=
            runs_assign_iff.mpr ⟨cur + 2, Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r6k])) (Expr.eval_const h2w) (by omega), rfl, rfl, rfl⟩
          have hseq_L : L0 ++ rotBatchVertList a.rf.root (U.take (k + 1)) = Lk := by
            rw [hrot_k]; simp [Lk, rotBatchVertList]
          refine ⟨⟨stK.mem, rB, stK.pos⟩, _, txK,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h8,
              runs_cond_iff.mpr ⟨0, _, heC0, by
                simpa using runs_cond_iff.mpr ⟨1, 4, heC1, by simpa using h6s, rfl⟩, rfl⟩, rfl⟩),
            by simp [rB, rA, r0k], by simp [rB, rA, r2k], by simp [rB, rA, r3k],
            by simp [rB, rA]; omega, by simp [rB, rA]; omega,
            by simp [rB, rA, r5k], by simp [rB], by simp [rB, rA, r7k],
            hrepK, by rw [hseq_L]; exact hcntK, by rw [hseq_L]; exact hLK,
            by simpa [rB, rA] using hzK, hfrK, by simpa [rB, rA] using hftK,
            by simp only [Expr.size]; omega⟩
        | split v0 v0' St Sh =>
          obtain ⟨tag, Lt, Lh, htag, hlen, hL⟩ :
              ∃ tag Lt Lh, (tag = 2 ∨ tag = 3) ∧ len = 5 + Lt.length + Lh.length ∧
                ListAt mem₀ cur ([tag, v0, v0', Lt.length, Lh.length] ++ Lt ++ Lh) := by
            rcases huAt with ⟨Lt, Lh, _, _, _, _, hlen, hL⟩ | ⟨Lt, Lh, _, _, _, _, hlen, hL⟩
            · exact ⟨2, Lt, Lh, Or.inl rfl, hlen, hL⟩
            · exact ⟨3, Lt, Lh, Or.inr rfl, hlen, hL⟩
          have hm0 : stK.mem cur = tag := (hbat_eq cur le_rfl (by omega)).trans (by simpa using hL 0 (by simp))
          have hm1 : stK.mem (cur + 1) = v0 := (hbat_eq (cur + 1) (by omega) (by omega)).trans (by simpa using hL 1 (by simp))
          have hm2 : stK.mem (cur + 2) = v0' := (hbat_eq (cur + 2) (by omega) (by omega)).trans (by simpa using hL 2 (by simp))
          have hm3 : mem₀ (cur + 3) = Lt.length := by simpa using hL 3 (by simp)
          have hm4 : mem₀ (cur + 4) = Lh.length := by simpa using hL 4 (by simp)
          have hv1 := hV_take hklt v0 (by rw [hu_eq]; simp [updVerts])
          have hv2 := hV_take hklt v0' (by rw [hu_eq]; simp [updVerts])
          set rA := Function.update stK.regs 8 tag
          set rB := Function.update rA 9 v0
          set rC := Function.update rB 10 v0'
          have hrC4 : rC 4 = stK.regs 4 := by simp [rC, rB, rA]
          have h8 : Runs w p ω (.assign 8 (.load (.reg 6))) stK .normal ⟨stK.mem, rA, stK.pos⟩ 3 :=
            runs_assign_iff.mpr ⟨tag, Expr.eval_load_of_eq (Expr.eval_reg_of_eq r6k) hm0, rfl, rfl, rfl⟩
          have heC0 : (Expr.bin .eq (.reg 8) (.const 0)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 0 := by
            rcases htag with rfl | rfl <;> simp [Expr.eval, rA, BinOp.eval, h0w]
          have heC1 : (Expr.bin .eq (.reg 8) (.const 1)).eval w ⟨stK.mem, rA, stK.pos⟩ = some 0 := by
            rcases htag with rfl | rfl <;> simp [Expr.eval, rA, BinOp.eval, h0w, h1w]
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
          have hstP_bat : ∀ x, cur ≤ x → x < cur + len → stP.mem x = mem₀ x := fun x hx1 hx2 => by
            obtain ⟨h1, h2, h3⟩ := hBat_disj x (by omega) (by omega)
            exact (hfrP x (by omega) h1 h2 h3).trans (hfrK x (by omega) h1 h2 h3)
          have hstP6 : stP.regs 6 = cur := by
            rw [hrP_oth 6 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r6k]
          set rD := Function.update stP.regs 9 Lt.length
          set rE := Function.update rD 10 Lh.length
          set rF := Function.update rE 6 (cur + len)
          have h9s : Runs w p ω (.assign 9 (.load (.bin .add (.reg 6) (.const 3)))) stP .normal ⟨stP.mem, rD, stP.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨Lt.length, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq hstP6) (Expr.eval_const h3w) (by omega))
              ((hstP_bat (cur + 3) (by omega) (by omega)).trans hm3), rfl, rfl, rfl⟩
          have h10s : Runs w p ω (.assign 10 (.load (.bin .add (.reg 6) (.const 4)))) ⟨stP.mem, rD, stP.pos⟩ .normal ⟨stP.mem, rE, stP.pos⟩ 5 :=
            runs_assign_iff.mpr ⟨Lh.length, Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp [rD, hstP6])) (Expr.eval_const h4w) (by omega))
              ((hstP_bat (cur + 4) (by omega) (by omega)).trans hm4), rfl, rfl, rfl⟩
          have h6s : Runs w p ω (.assign 6 (.bin .add (.bin .add (.bin .add (.reg 6) (.const 5)) (.reg 9)) (.reg 10)))
              ⟨stP.mem, rE, stP.pos⟩ .normal ⟨stP.mem, rF, stP.pos⟩ 8 := by
            have hr6 : rE 6 = cur := by simp [rE, rD, hstP6]
            have hr9 : rE 9 = Lt.length := by simp [rE, rD]
            have hr10 : rE 10 = Lh.length := by simp [rE]
            have he1 : (Expr.bin .add (.reg 6) (.const 5)).eval w ⟨stP.mem, rE, stP.pos⟩ = some (cur + 5) :=
              Expr.eval_add (Expr.eval_reg_of_eq hr6) (Expr.eval_const h5w) (by omega)
            have he2 : (Expr.bin .add (.bin .add (.reg 6) (.const 5)) (.reg 9)).eval w ⟨stP.mem, rE, stP.pos⟩ =
                some (cur + 5 + Lt.length) := Expr.eval_add he1 (Expr.eval_reg_of_eq hr9) (by omega)
            have he3 : (Expr.bin .add (.bin .add (.bin .add (.reg 6) (.const 5)) (.reg 9)) (.reg 10)).eval w
                ⟨stP.mem, rE, stP.pos⟩ = some (cur + 5 + Lt.length + Lh.length) :=
              Expr.eval_add he2 (Expr.eval_reg_of_eq hr10) (by omega)
            rw [show cur + 5 + Lt.length + Lh.length = cur + len by omega] at he3
            exact runs_assign_iff.mpr ⟨cur + len, he3, rfl, rfl, rfl⟩
          have hseq_L : L0 ++ rotBatchVertList a.rf.root (U.take (k + 1)) = Lk ++ [a.rf.root v0, a.rf.root v0'] := by
            rw [hrot_k]; simp [Lk, rotBatchVertList, List.append_assoc]
          have hTail := runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9s,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10s, h6s, rfl⟩), rfl⟩)
          have hPT := runs_seqSnoc hrP hTail
          refine ⟨⟨stP.mem, rF, stP.pos⟩, _, txP,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, h8,
              runs_cond_iff.mpr ⟨0, _, heC0, by
                simp only [↓reduceIte]
                exact runs_cond_iff.mpr ⟨0, _, heC1, by
                  simp only [↓reduceIte]
                  exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, h9,
                    runs_seq_iff.mpr (Or.inr ⟨_, _, _, h10, hPT, rfl⟩), rfl⟩), rfl⟩, rfl⟩, rfl⟩),
            by simp only [rF, rE, rD, Function.update_of_ne (by decide : (0 : ℕ) ≠ 6),
              Function.update_of_ne (by decide : (0 : ℕ) ≠ 10), Function.update_of_ne (by decide : (0 : ℕ) ≠ 9)]
               rw [hrP_oth 0 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r0k],
            by simp only [rF, rE, rD, Function.update_of_ne (by decide : (2 : ℕ) ≠ 6),
              Function.update_of_ne (by decide : (2 : ℕ) ≠ 10), Function.update_of_ne (by decide : (2 : ℕ) ≠ 9)]
               rw [hrP_oth 2 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r2k],
            by simp only [rF, rE, rD, Function.update_of_ne (by decide : (3 : ℕ) ≠ 6),
              Function.update_of_ne (by decide : (3 : ℕ) ≠ 10), Function.update_of_ne (by decide : (3 : ℕ) ≠ 9)]
               rw [hrP_oth 3 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r3k],
            by simp only [rF, rE, rD, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6),
              Function.update_of_ne (by decide : (4 : ℕ) ≠ 10), Function.update_of_ne (by decide : (4 : ℕ) ≠ 9), hrP4]
               simp only [hrC4] at hhp_lo; omega,
            by simp only [rF, rE, rD, Function.update_of_ne (by decide : (4 : ℕ) ≠ 6),
              Function.update_of_ne (by decide : (4 : ℕ) ≠ 10), Function.update_of_ne (by decide : (4 : ℕ) ≠ 9), hrP4]
               simp only [hrC4] at hhp_hi; omega,
            by simp only [rF, rE, rD, Function.update_of_ne (by decide : (5 : ℕ) ≠ 6),
              Function.update_of_ne (by decide : (5 : ℕ) ≠ 10), Function.update_of_ne (by decide : (5 : ℕ) ≠ 9)]
               rw [hrP_oth 5 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r5k],
            by simp [rF],
            by simp only [rF, rE, rD, Function.update_of_ne (by decide : (7 : ℕ) ≠ 6),
              Function.update_of_ne (by decide : (7 : ℕ) ≠ 10), Function.update_of_ne (by decide : (7 : ℕ) ≠ 9)]
               rw [hrP_oth 7 (by decide) (by decide) (by decide)]; simp [rC, rB, rA, r7k],
            hrepP, by rw [hseq_L]; simpa using hcntP, by rw [hseq_L]; exact hLP,
            by simpa [rF, rE, rD, hrP4] using hzP,
            fun x hx hnf hout hnc => (hfrP x hx hnf hout hnc).trans (hfrK x hx hnf hout hnc),
            by simpa [rF, rE, rD, hrP4] using hftP,
            by
              simp only [Expr.size]
              have hphiC : (TR vCap eCap).phi tourH txK ({ mem := stK.mem, regs := rC, pos := stK.pos } : State).mem =
                  (TR vCap eCap).phi tourH txK stK.mem := rfl
              omega⟩
      obtain ⟨stA, cA, txA, hrA, r0A, r2A, r3A, hgeA, hhiA, r5A, r6A, r7A, hrepA, hcntA, hLA, hzA, hfrA, hftA, hcA⟩ := hbody
      set stB : State := ⟨stA.mem, Function.update stA.regs 7 (k + 1), stA.pos⟩
      have ha7s : Runs w p ω (.assign 7 (.bin .add (.reg 7) (.const 1))) stA .normal stB 4 :=
        runs_assign_iff.mpr ⟨k + 1, Expr.eval_add (Expr.eval_reg_of_eq r7A) (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
      have hGnext : G₀.applyBatch (U.take (k + 1)) = (G₀.applyBatch (U.take k)).applyUpdate u := by
        rw [htake, applyBatch_append]; rfl
      obtain ⟨st1, c1, tx1, hr1, hge1, hhi1, hrep1, hcnt1, hL1, hz1, hfr1, hft1, hc1⟩ :=
        ih (k + 1) (by omega) (by omega) (cur + len) (W - len) stB txA (by omega) (by omega)
          (hGnext.symm ▸ hBBrest)
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
    hloop 0 (Nat.zero_le _) (batch + 1) (words - 1) ⟨mem₀, r3, pos⟩ tx₀
      (by omega) (by have := hBat.1; omega) hBat.2.2
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1, s0, startState])
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1, s0, startState])
      (by simp [r3, r2, r1, s0, startState]) (by simp [r3, r2, r1]) (by simp [r3, r2]) (by simp [r3])
      hrep (by simpa [rotBatchVertList] using hcnt_mem) (by simpa [rotBatchVertList] using hL0_at)
      (by simpa [r3, r2, r1, s0, startState] using hz)
      (fun _ _ _ _ _ => rfl) (fun x hx => Or.inl hx)
  have hret : Runs w p ω (.ret (.reg 4)) st1 (.returned (st1.regs 4)) st1 2 :=
    runs_ret_iff.mpr ⟨st1.regs 4, Expr.eval_reg_of_eq rfl, rfl, rfl, rfl⟩
  have hseqLoop : Runs w p ω (forRange 7 (.const 0) (.reg 5) (asmFirstCollectRotBatchBody fVertRoot))
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
