module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase1Prog

import WordRAM.Tactic

/-!
# First-phase step Phase 1 Word-RAM verification (`AssemblyFirstStepPhase1Proof`)

Verifies `asmFirstScanBatchBody` (`asmFirstScanBatchBody_runs`) and `asmFirstScanBatchStmt`
(`asmFirstScanBatch_runs`) against `scanBatchFold` (`AssemblyFirstStepPhase1Model.lean`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

private lemma scanRegsAt_of_lt15 {regs regs₀ : ℕ → ℕ}
    {gPtr cmpH ctH batch words vCap eCap h nUpd cur cur' i i' : ℕ} {sb sb' : ScanBatchState}
    (hR : ScanRegsAt regs₀ gPtr cmpH ctH batch words vCap eCap h nUpd cur sb i)
    (hkr : ∀ r < 15, regs r = regs₀ r)
    (h15 : regs 15 = cur') (h16 : regs 16 = sb'.newComps.length)
    (h17 : regs 17 = sb'.delEdges.length) (h18 : regs 18 = sb'.insEdges.length) (h19 : regs 19 = i') :
    ScanRegsAt regs gPtr cmpH ctH batch words vCap eCap h nUpd cur' sb' i' := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, _, _, _, _, _⟩ := hR
  exact ⟨(hkr 0 (by decide)).trans r0, (hkr 1 (by decide)).trans r1, (hkr 2 (by decide)).trans r2,
    (hkr 3 (by decide)).trans r3, (hkr 4 (by decide)).trans r4, (hkr 5 (by decide)).trans r5,
    (hkr 6 (by decide)).trans r6, (hkr 7 (by decide)).trans r7, (hkr 8 (by decide)).trans r8,
    (hkr 9 (by decide)).trans r9, (hkr 10 (by decide)).trans r10, (hkr 11 (by decide)).trans r11,
    (hkr 12 (by decide)).trans r12, (hkr 13 (by decide)).trans r13, (hkr 14 (by decide)).trans r14,
    h15, h16, h17, h18, h19⟩

public section

private def ScanUpdateCap (vCap eCap : ℕ) (G₀ : MGraph) (sb : ScanBatchState) : Update → Prop
  | .insert e a b => e < eCap ∧ a < vCap ∧ b < vCap
  | .delete e => e < eCap ∧ (sb.insFlag e = false → e ∈ G₀.E)
  | .split v v' _ _ => v < vCap ∧ v' < vCap

/-- Updates never remove a vertex. -/
private lemma applyBatch_V_sub (G : MGraph) (U : List Update) : G.V ⊆ (G.applyBatch U).V := by
  induction U generalizing G with
  | nil => exact fun _ h => h
  | cons u r ih =>
    refine fun x hx => ih (G.applyUpdate u) ?_
    cases u <;> simp [MGraph.applyUpdate, hx]

/-- One iteration of `asmFirstScanBatchBody` on update `u` at `cur` of length `len`. -/
private lemma asmFirstScanBatchBody_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {gPtr cmpH ctH nComp batch words vCap eCap h nUpd cur len i : ℕ}
    {G₀ Gcur : MGraph} {u : Update} {mem₀ : ℕ → ℕ} {sb : ScanBatchState} {st : State}
    (hGeo : ScanGeom w gPtr cmpH ctH nComp batch words vCap eCap h)
    (hG0 : DynGraphAt mem₀ gPtr vCap eCap G₀)
    (hcur_lo : batch < cur) (hcur_hi : cur + len ≤ batch + words)
    (huAt : UpdateAt mem₀ cur Gcur u len)
    (huCap : ScanUpdateCap vCap eCap G₀ sb u)
    (huValid : Gcur.UpdateIsValid u) (hGV : G₀.V ⊆ Gcur.V)
    (hcmp_lt : ∀ v ∈ Gcur.V, sb.cmpMap v < nComp)
    (_horig_w : ∀ v < vCap, sb.origVert v < 2 ^ w)
    (hnew_lt : sb.newComps.length + 2 ≤ 2 * words)
    (hdel_lt : sb.delEdges.length < words)
    (hins_lt : sb.insEdges.length < words)
    (hR : ScanRegsAt st.regs gPtr cmpH ctH batch words vCap eCap h nUpd cur sb i)
    (hM : ScanMemAt mem₀ st.mem cmpH ctH nComp vCap eCap words h sb) :
    ∃ st' cost,
      Runs w p ω asmFirstScanBatchBody st .normal st' cost ∧
      ScanRegsAt st'.regs gPtr cmpH ctH batch words vCap eCap h nUpd (cur + len)
        (scanBatchStep G₀ sb u) i ∧
      ScanMemAt mem₀ st'.mem cmpH ctH nComp vCap eCap words h (scanBatchStep G₀ sb u) ∧
      cost ≤ 235 := by
  have hsp' : h + (3 + 2 * eCap + vCap + 6 * words) < 2 ^ w := hGeo.hsp
  have hw16 : 16 ≤ 2 ^ w := hGeo.hw16
  have h1w : 1 < 2 ^ w := by omega
  have hbat_eq : ∀ a, cur ≤ a → a < cur + len → st.mem a = mem₀ a := fun a ha1 ha2 => by
    have hbl := hGeo.hbat_le; have hdc := hGeo.hdisj_bat_cmp; have hdt := hGeo.hdisj_bat_ct
    exact hM.2.2.2.2.2.2.2.2.1 a (by omega) (by omega) (fun c hc => by omega)
  have ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19⟩ := hR
  have hcur_w : cur + len < 2 ^ w := by have := hGeo.hbat_le; omega
  have hcl := hGeo.hcmp_le; have htl := hGeo.hct_le
  cases u with
  | insert e a b =>
    obtain ⟨rfl, hlist⟩ := huAt
    obtain ⟨he, ha, hb⟩ := huCap
    have hm0 : st.mem cur = 0 := (hbat_eq cur (le_refl _) (by omega)).trans (by simpa using hlist 0 (by simp))
    have hm1 : st.mem (cur + 1) = e := (hbat_eq (cur + 1) (by omega) (by omega)).trans (by simpa using hlist 1 (by simp))
    have hm2 : st.mem (cur + 2) = a := (hbat_eq (cur + 2) (by omega) (by omega)).trans (by simpa using hlist 2 (by simp))
    have hm3 : st.mem (cur + 3) = b := (hbat_eq (cur + 3) (by omega) (by omega)).trans (by simpa using hlist 3 (by simp))
    have hca : sb.cmpMap a < nComp := hcmp_lt a huValid.2.1
    have hcb : sb.cmpMap b < nComp := hcmp_lt b huValid.2.2
    set sb1 : ScanBatchState := { sb with insFlag := Function.update sb.insFlag e true, insEdges := sb.insEdges ++ [e] }
    set memA := Function.update st.mem (scanInsFlagBase h + e) 1
    set memB := Function.update memA (scanInsEdgesBase h vCap eCap words + sb.insEdges.length) e
    have hMB : ScanMemAt mem₀ memB cmpH ctH nComp vCap eCap words h sb1 :=
      scanMemAt_insert hGeo he (by omega) (by omega) hins_lt hM
    have hca_mem : memB (cmpH + a) = sb.cmpMap a := hMB.1 a ha
    set stA : State := ⟨memB, Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update st.regs 20 0) 21 e) 22 a) 23 b) 18 (sb.insEdges.length + 1)) 24 (sb.cmpMap a), st.pos⟩
    obtain ⟨stB, cB, hrunB, hregsB, hr16B, hMB', hcB⟩ :=
      asmScanActivate_runs (p := p) (ω := ω) (rComp := 24) (rVert := 22) (c := sb.cmpMap a) (v := a)
        (sb := sb1) (st := stA) hGeo (by simp [stA, r2]) (by simp [stA, r11]) (by simp [stA, r16, sb1])
        (by simp [stA]) (by simp [stA]) (by decide) (by decide) hca ha (by simp [sb1]; omega) hMB
    set sb2 := scanActivate sb1 (sb.cmpMap a) a
    have hsb2_len : sb2.newComps.length < 2 * words := by
      have h1 := scanActivate_newComps_len sb1 (sb.cmpMap a) a
      have h0 : sb1.newComps.length = sb.newComps.length := rfl
      change sb2.newComps.length ≤ sb1.newComps.length + 1 at h1; omega
    have hcb_mem : stB.mem (cmpH + b) = sb.cmpMap b := by have := hMB'.1 b hb; simp [sb2, sb1] at this; exact this
    set stC : State := ⟨stB.mem, Function.update stB.regs 25 (sb.cmpMap b), stB.pos⟩
    obtain ⟨stD, cD, hrunD, hregsD, hr16D, hMD', hcD⟩ :=
      asmScanActivate_runs (p := p) (ω := ω) (rComp := 25) (rVert := 23) (c := sb.cmpMap b) (v := b)
        (sb := sb2) (st := stC) hGeo
        (by simp [stC, hregsB 2 (by decide) (by decide), stA, r2])
        (by simp [stC, hregsB 11 (by decide) (by decide), stA, r11])
        (by simp [stC, hr16B]) (by simp [stC])
        (by simp [stC, hregsB 23 (by decide) (by decide), stA])
        (by decide) (by decide) hcb hb hsb2_len hMB'
    set sb3 := scanActivate sb2 (sb.cmpMap b) b
    have hsb3_eq : sb3 = scanBatchStep G₀ sb (.insert e a b) := by simp [sb3, sb2, sb1, scanBatchStep]
    have ha25 : Runs w p ω (.assign 25 (.load (.bin .add (.reg 1) (.reg 23)))) stB .normal stC 5 :=
      runs_assign_iff.mpr ⟨sb.cmpMap b, Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hregsB 1 (by decide) (by decide)]; simp [stA, r1]))
          (Expr.eval_reg_of_eq (by rw [hregsB 23 (by decide) (by decide)]; simp [stA])) (by omega)) hcb_mem, rfl, rfl, rfl⟩
    have hstD_15 : stD.regs 15 = cur := by
      rw [hregsD 15 (by decide) (by decide)]; simp [stC, hregsB 15 (by decide) (by decide), stA, r15]
    set stE : State := ⟨stD.mem, Function.update stD.regs 15 (cur + 4), stD.pos⟩
    have ha15 : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.const 4))) stD .normal stE 4 :=
      runs_assign_iff.mpr ⟨cur + 4,
        Expr.eval_add (Expr.eval_reg_of_eq hstD_15) (Expr.eval_const (by omega)) hcur_w, rfl, rfl, rfl⟩
    have hcond0 : (Expr.bin .eq (.reg 20) (.const 0)).eval w ⟨st.mem, Function.update st.regs 20 0, st.pos⟩ = some 1 := by
      simp [Expr.eval, BinOp.eval, (by omega : 0 < 2 ^ w), h1w]
    obtain ⟨cAll, hfull, hcAll⟩ : ∃ c, Runs w p ω asmFirstScanBatchBody st .normal stE c ∧ 0 + c ≤ 235 := by
      unfold asmFirstScanBatchBody
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_reg_of_eq r15) hm0)
        (rCondTLe hcond0 (by decide) ?_)
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r15]; try rfl))
        (Expr.eval_const h1w) (by omega)) hm1) ?_
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r15]; try rfl))
        (Expr.eval_const (by omega)) (by omega)) hm2) ?_
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r15]; try rfl))
        (Expr.eval_const (by omega)) (by omega)) hm3) ?_
      refine rStoreLe (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r8]; try rfl)) (Expr.eval_reg_of_eq (by simp; try rfl))
        (by unfold scanInsFlagBase; omega)) (Expr.eval_const h1w) ?_
      refine rStoreLe (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r13]; try rfl)) (Expr.eval_reg_of_eq (by simp [r18]; try rfl))
        (by unfold scanInsEdgesBase; omega)) (Expr.eval_reg_of_eq (by simp; try rfl)) ?_
      refine rAssignLe (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r18]; try rfl)) (Expr.eval_const h1w) (by omega)) ?_
      refine rAssignLe (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1]; try rfl)) (Expr.eval_reg_of_eq (by simp; try rfl)) (by omega))
        hca_mem) ?_
      exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨stB, cB, _, hrunB,
        runs_seq_iff.mpr (Or.inr ⟨stC, 5, _, ha25, runs_seq_iff.mpr (Or.inr ⟨stD, cD, 4, hrunD, ha15, rfl⟩), rfl⟩), rfl⟩),
        by simp only [Expr.size]; omega⟩
    rw [← hsb3_eq]
    have hkr : ∀ r < 15, stE.regs r = st.regs r := fun r hr => by
      simp only [stE, Function.update_of_ne (by omega : r ≠ 15)]
      rw [hregsD r (by omega) (by omega)]; simp only [stC, Function.update_of_ne (by omega : r ≠ 25)]
      rw [hregsB r (by omega) (by omega)]
      simp [stA, Function.update_of_ne (by omega : r ≠ 24), Function.update_of_ne (by omega : r ≠ 18),
        Function.update_of_ne (by omega : r ≠ 23), Function.update_of_ne (by omega : r ≠ 22),
        Function.update_of_ne (by omega : r ≠ 21), Function.update_of_ne (by omega : r ≠ 20)]
    refine ⟨stE, cAll, hfull,
      scanRegsAt_of_lt15 hR hkr (by simp [stE]) (by simp [stE, hr16D])
        (by simp only [stE, Function.update_of_ne (by decide : (17 : ℕ) ≠ 15)]
            rw [hregsD 17 (by decide) (by decide)]; simp only [stC, Function.update_of_ne (by decide : (17 : ℕ) ≠ 25)]
            rw [hregsB 17 (by decide) (by decide)]; simp [stA, r17, sb3, sb2, sb1])
        (by simp only [stE, Function.update_of_ne (by decide : (18 : ℕ) ≠ 15)]
            rw [hregsD 18 (by decide) (by decide)]; simp only [stC, Function.update_of_ne (by decide : (18 : ℕ) ≠ 25)]
            rw [hregsB 18 (by decide) (by decide)]; simp [stA, sb3, sb2, sb1])
        (by simp only [stE, Function.update_of_ne (by decide : (19 : ℕ) ≠ 15)]
            rw [hregsD 19 (by decide) (by decide)]; simp only [stC, Function.update_of_ne (by decide : (19 : ℕ) ≠ 25)]
            rw [hregsB 19 (by decide) (by decide)]; simp [stA, r19]),
      hMD', by omega⟩
  | delete e =>
    obtain ⟨rfl, hlist⟩ := huAt
    obtain ⟨he, heG0⟩ := huCap
    have hm0 : st.mem cur = 1 := (hbat_eq cur (le_refl _) (by omega)).trans (by simpa using hlist 0 (by simp))
    have hm1 : st.mem (cur + 1) = e := (hbat_eq (cur + 1) (by omega) (by omega)).trans (by simpa using hlist 1 (by simp))
    set sb1 : ScanBatchState := { sb with delFlag := Function.update sb.delFlag e true, delEdges := sb.delEdges ++ [e] }
    set memA := Function.update st.mem (scanDelFlagBase h eCap + e) 1
    set memB := Function.update memA (scanDelEdgesBase h vCap eCap words + sb.delEdges.length) e
    have hMB : ScanMemAt mem₀ memB cmpH ctH nComp vCap eCap words h sb1 :=
      scanMemAt_delete hGeo he (by omega) hdel_lt hM
    set ifVal := if sb.insFlag e then 1 else 0
    have hif_mem : memB (scanInsFlagBase h + e) = ifVal := hMB.2.2.1 e he
    set stA : State := ⟨memB, Function.update (Function.update (Function.update
      (Function.update st.regs 20 1) 21 e) 17 (sb.delEdges.length + 1)) 22 ifVal, st.pos⟩
    have hinner : ∃ stD cD,
        Runs w p ω
          (.cond (.bin .eq (.reg 22) (.const 0))
            (.assign 23 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
              (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 3) (.reg 6)))) (.reg 21))) ;;
             .assign 24 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
              (.bin .mul (.const 4) (.reg 5))) (.reg 23))) ;;
             .assign 25 (.load (.bin .add (.reg 1) (.reg 24))) ;;
             asmScanActivateStmt 25 24 ;;
             .assign 23 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
              (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 4) (.reg 6)))) (.reg 21))) ;;
             .assign 24 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
              (.bin .mul (.const 4) (.reg 5))) (.reg 23))) ;;
             .assign 25 (.load (.bin .add (.reg 1) (.reg 24))) ;;
             asmScanActivateStmt 25 24)
            .nop)
          stA .normal stD cD ∧
        (∀ r, r < 20 → r ≠ 16 → stD.regs r = stA.regs r) ∧
        stD.regs 16 = (scanBatchStep G₀ sb (.delete e)).newComps.length ∧
        ScanMemAt mem₀ stD.mem cmpH ctH nComp vCap eCap words h (scanBatchStep G₀ sb (.delete e)) ∧
        cD ≤ 175 := by
      cases hif : sb.insFlag e with
      | true =>
        have hv1 : ifVal = 1 := by simp [ifVal, hif]
        have heC : (Expr.bin .eq (.reg 22) (.const 0)).eval w stA = some 0 := by
          simp [Expr.eval, stA, hv1, BinOp.eval, (by omega : 0 < 2 ^ w)]
        rw [show scanBatchStep G₀ sb (.delete e) = sb1 by simp [scanBatchStep, sb1, hif]]
        have hnop : Runs w p ω .nop stA .normal stA 1 := runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
        exact ⟨stA, 5, runs_cond_iff.mpr ⟨0, 1, heC, by simpa using hnop, rfl⟩,
          fun _ _ _ => rfl, by simp [stA, r16, sb1], hMB, by omega⟩
      | false =>
        have hv0 : ifVal = 0 := by simp [ifVal, hif]
        have heC : (Expr.bin .eq (.reg 22) (.const 0)).eval w stA = some 1 := by
          simp [Expr.eval, stA, hv0, BinOp.eval, (by omega : 0 < 2 ^ w), h1w]
        have he0 : e ∈ G₀.E := heG0 hif
        obtain ⟨hts_lt, htu_eq, hhs_lt, hhv_eq⟩ := dynGraph_tail_head_read hG0 he0
        have hu_lt : G₀.tail e < vCap := hG0.2.1 _ (hG0.1 e he0).1
        have hv_lt : G₀.head e < vCap := hG0.2.1 _ (hG0.1 e he0).2
        have hcu : sb.cmpMap (G₀.tail e) < nComp := hcmp_lt _ (hGV (hG0.1 e he0).1)
        have hcv : sb.cmpMap (G₀.head e) < nComp := hcmp_lt _ (hGV (hG0.1 e he0).2)
        have hgl := hGeo.hg_le; have hdgS : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
        have hMB_dg : ∀ x, gPtr ≤ x → x < gPtr + dynGraphSize vCap eCap → memB x = mem₀ x := fun x h1 h2 => by
          have := hGeo.hdisj_g_cmp; have := hGeo.hdisj_g_ct
          exact hMB.2.2.2.2.2.2.2.2.1 x (by omega) (by omega) (fun c hc => by omega)
        set ts := mem₀ (dgETailSlotBase gPtr vCap eCap + e)
        set hs := mem₀ (dgEHeadSlotBase gPtr vCap eCap + e)
        have hts_m : memB (gPtr + 4 + (7 * vCap + 3 * eCap) + e) = ts := by
          have h := hMB_dg (dgETailSlotBase gPtr vCap eCap + e) (by unfold dgETailSlotBase; omega) (by unfold dgETailSlotBase; omega)
          simpa only [ts, dgETailSlotBase, Nat.add_assoc] using h
        have htu_m : memB (gPtr + 4 + 4 * vCap + ts) = G₀.tail e := by
          have h := hMB_dg (dgIntToExtBase gPtr vCap + ts) (by unfold dgIntToExtBase; omega) (by unfold dgIntToExtBase; omega)
          simpa only [dgIntToExtBase, Nat.add_assoc] using h.trans htu_eq
        have hcu_m : memB (cmpH + G₀.tail e) = sb.cmpMap (G₀.tail e) := hMB.1 _ hu_lt
        set rA1 := Function.update (Function.update (Function.update stA.regs 23 ts) 24 (G₀.tail e)) 25 (sb.cmpMap (G₀.tail e))
        obtain ⟨stB, cB, hrunB, hregsB, hr16B, hMB', hcB⟩ :=
          asmScanActivate_runs (p := p) (ω := ω) (rComp := 25) (rVert := 24) (c := sb.cmpMap (G₀.tail e))
            (v := G₀.tail e) (sb := sb1) (st := ⟨memB, rA1, st.pos⟩) hGeo
            (by simp [rA1, stA, r2]) (by simp [rA1, stA, r11]) (by simp [rA1, stA, r16, sb1])
            (by simp [rA1]) (by simp [rA1]) (by decide) (by decide) hcu hu_lt (by simp [sb1]; omega) hMB
        set sb2 := scanActivate sb1 (sb.cmpMap (G₀.tail e)) (G₀.tail e)
        have hsb2_len : sb2.newComps.length < 2 * words := by
          have h1 := scanActivate_newComps_len sb1 (sb.cmpMap (G₀.tail e)) (G₀.tail e)
          have h0 : sb1.newComps.length = sb.newComps.length := rfl
          change sb2.newComps.length ≤ sb1.newComps.length + 1 at h1; omega
        have hMB'_dg : ∀ x, gPtr ≤ x → x < gPtr + dynGraphSize vCap eCap → stB.mem x = mem₀ x := fun x h1 h2 => by
          have := hGeo.hdisj_g_cmp; have := hGeo.hdisj_g_ct
          exact hMB'.2.2.2.2.2.2.2.2.1 x (by omega) (by omega) (fun c hc => by omega)
        have hhs_m : stB.mem (gPtr + 4 + (7 * vCap + 4 * eCap) + e) = hs := by
          have h := hMB'_dg (dgEHeadSlotBase gPtr vCap eCap + e) (by unfold dgEHeadSlotBase; omega) (by unfold dgEHeadSlotBase; omega)
          simpa only [hs, dgEHeadSlotBase, Nat.add_assoc] using h
        have hhv_m : stB.mem (gPtr + 4 + 4 * vCap + hs) = G₀.head e := by
          have h := hMB'_dg (dgIntToExtBase gPtr vCap + hs) (by unfold dgIntToExtBase; omega) (by unfold dgIntToExtBase; omega)
          simpa only [dgIntToExtBase, Nat.add_assoc] using h.trans hhv_eq
        have hcv_m : stB.mem (cmpH + G₀.head e) = sb.cmpMap (G₀.head e) := by
          have := hMB'.1 _ hv_lt; simp [sb2, sb1] at this; exact this
        set rB1 := Function.update (Function.update (Function.update stB.regs 23 hs) 24 (G₀.head e)) 25 (sb.cmpMap (G₀.head e))
        obtain ⟨stD, cD, hrunD, hregsD, hr16D, hMD', hcD⟩ :=
          asmScanActivate_runs (p := p) (ω := ω) (rComp := 25) (rVert := 24) (c := sb.cmpMap (G₀.head e))
            (v := G₀.head e) (sb := sb2) (st := ⟨stB.mem, rB1, stB.pos⟩) hGeo
            (by simp [rB1, hregsB 2 (by decide) (by decide), rA1, stA, r2])
            (by simp [rB1, hregsB 11 (by decide) (by decide), rA1, stA, r11])
            (by simp [rB1, hr16B]) (by simp [rB1]) (by simp [rB1]) (by decide) (by decide) hcv hv_lt hsb2_len hMB'
        rw [show scanBatchStep G₀ sb (.delete e) = scanActivate sb2 (sb.cmpMap (G₀.head e)) (G₀.head e)
          by simp [scanBatchStep, sb2, sb1, hif]]
        obtain ⟨cBr, hbr, hcBr⟩ : ∃ c, Runs w p ω
            (.cond (.bin .eq (.reg 22) (.const 0))
              (.assign 23 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
                (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 3) (.reg 6)))) (.reg 21))) ;;
               .assign 24 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
                (.bin .mul (.const 4) (.reg 5))) (.reg 23))) ;;
               .assign 25 (.load (.bin .add (.reg 1) (.reg 24))) ;;
               asmScanActivateStmt 25 24 ;;
               .assign 23 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
                (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 4) (.reg 6)))) (.reg 21))) ;;
               .assign 24 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
                (.bin .mul (.const 4) (.reg 5))) (.reg 23))) ;;
               .assign 25 (.load (.bin .add (.reg 1) (.reg 24))) ;;
               asmScanActivateStmt 25 24)
              .nop) stA .normal stD c ∧ 0 + c ≤ 175 := by
          refine rCondTLe heC (by decide) ?_
          refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_add
            (Expr.eval_reg_of_eq (by simp [stA, r0]; try rfl)) (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [stA, r5]; try rfl)) (by omega))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [stA, r6]; try rfl)) (by omega)) (by omega)) (by omega))
            (Expr.eval_reg_of_eq (by simp [stA]; try rfl)) (by omega)) hts_m) ?_
          refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_add
            (Expr.eval_reg_of_eq (by simp [stA, r0]; try rfl)) (Expr.eval_const (by omega)) (by omega))
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [stA, r5]; try rfl)) (by omega)) (by omega))
            (Expr.eval_reg_of_eq (by simp; try rfl)) (by omega)) htu_m) ?_
          refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add
            (Expr.eval_reg_of_eq (by simp [stA, r1]; try rfl)) (Expr.eval_reg_of_eq (by simp; try rfl)) (by omega)) hcu_m) ?_
          have htail : ∃ c, Runs w p ω
              (.assign 23 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
                (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 4) (.reg 6)))) (.reg 21))) ;;
               .assign 24 (.load (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
                (.bin .mul (.const 4) (.reg 5))) (.reg 23))) ;;
               .assign 25 (.load (.bin .add (.reg 1) (.reg 24))) ;;
               asmScanActivateStmt 25 24) stB .normal stD c ∧ 0 + c ≤ 80 := by
            refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_add
              (Expr.eval_reg_of_eq (by rw [hregsB 0 (by decide) (by decide)]; simp [rA1, stA, r0]; try rfl)) (Expr.eval_const (by omega)) (by omega))
              (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by rw [hregsB 5 (by decide) (by decide)]; simp [rA1, stA, r5]; try rfl)) (by omega))
                (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by rw [hregsB 6 (by decide) (by decide)]; simp [rA1, stA, r6]; try rfl)) (by omega)) (by omega)) (by omega))
              (Expr.eval_reg_of_eq (by rw [hregsB 21 (by decide) (by decide)]; simp [rA1, stA]; try rfl)) (by omega)) hhs_m) ?_
            refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_add
              (Expr.eval_reg_of_eq (by simp [hregsB 0 (by decide) (by decide), rA1, stA, r0]; try rfl)) (Expr.eval_const (by omega)) (by omega))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [hregsB 5 (by decide) (by decide), rA1, stA, r5]; try rfl)) (by omega)) (by omega))
              (Expr.eval_reg_of_eq (by simp; try rfl)) (by omega)) hhv_m) ?_
            refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add
              (Expr.eval_reg_of_eq (by simp [hregsB 1 (by decide) (by decide), rA1, stA, r1]; try rfl)) (Expr.eval_reg_of_eq (by simp; try rfl)) (by omega)) hcv_m) ?_
            exact ⟨cD, hrunD, by simp only [Expr.size]; omega⟩
          obtain ⟨ct, hrt, hct⟩ := htail
          exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨stB, cB, ct, hrunB, hrt, rfl⟩), by simp only [Expr.size]; omega⟩
        refine ⟨stD, cBr, hbr, ?_, hr16D, hMD', by omega⟩
        intro r hr h16
        rw [hregsD r h16 (by omega)]
        simp only [rB1, Function.update_of_ne (by omega : r ≠ 25), Function.update_of_ne (by omega : r ≠ 24),
          Function.update_of_ne (by omega : r ≠ 23)]
        rw [hregsB r h16 (by omega)]
        simp [rA1, Function.update_of_ne (by omega : r ≠ 25), Function.update_of_ne (by omega : r ≠ 24),
          Function.update_of_ne (by omega : r ≠ 23)]
    obtain ⟨stD, cD, hrunD, hregsD, hr16D, hMD', hcD⟩ := hinner
    have hstD_15 : stD.regs 15 = cur := by rw [hregsD 15 (by decide) (by decide)]; simp [stA, r15]
    set stE : State := ⟨stD.mem, Function.update stD.regs 15 (cur + 2), stD.pos⟩
    have ha15 : Runs w p ω (.assign 15 (.bin .add (.reg 15) (.const 2))) stD .normal stE 4 :=
      runs_assign_iff.mpr ⟨cur + 2,
        Expr.eval_add (Expr.eval_reg_of_eq hstD_15) (Expr.eval_const (by omega)) hcur_w, rfl, rfl, rfl⟩
    have hcond0 : (Expr.bin .eq (.reg 20) (.const 0)).eval w ⟨st.mem, Function.update st.regs 20 1, st.pos⟩ = some 0 := by
      simp [Expr.eval, BinOp.eval, (by omega : 0 < 2 ^ w)]
    have hcond1 : (Expr.bin .eq (.reg 20) (.const 1)).eval w ⟨st.mem, Function.update st.regs 20 1, st.pos⟩ = some 1 := by
      simp [Expr.eval, BinOp.eval, h1w]
    obtain ⟨cAll, hfull, hcAll⟩ : ∃ c, Runs w p ω asmFirstScanBatchBody st .normal stE c ∧ 0 + c ≤ 235 := by
      unfold asmFirstScanBatchBody
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_reg_of_eq r15) hm0)
        (rCondFLe hcond0 (rCondTLe hcond1 (by decide) ?_))
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r15]; try rfl))
        (Expr.eval_const h1w) (by omega)) hm1) ?_
      refine rStoreLe (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r9]; try rfl)) (Expr.eval_reg_of_eq (by simp; try rfl))
        (by unfold scanDelFlagBase; omega)) (Expr.eval_const h1w) ?_
      refine rStoreLe (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r12]; try rfl)) (Expr.eval_reg_of_eq (by simp [r17]; try rfl))
        (by unfold scanDelEdgesBase; omega)) (Expr.eval_reg_of_eq (by simp; try rfl)) ?_
      refine rAssignLe (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r17]; try rfl)) (Expr.eval_const h1w) (by omega)) ?_
      refine rAssignLe (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r8]; try rfl)) (Expr.eval_reg_of_eq (by simp; try rfl))
          (by unfold scanInsFlagBase; omega)) hif_mem) ?_
      exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨stD, cD, 4, hrunD, ha15, rfl⟩), by simp only [Expr.size]; omega⟩
    have hkr : ∀ r < 15, stE.regs r = st.regs r := fun r hr => by
      simp only [stE, Function.update_of_ne (by omega : r ≠ 15)]
      rw [hregsD r (by omega) (by omega)]
      simp [stA, Function.update_of_ne (by omega : r ≠ 22), Function.update_of_ne (by omega : r ≠ 17),
        Function.update_of_ne (by omega : r ≠ 21), Function.update_of_ne (by omega : r ≠ 20)]
    have hdelL : (scanBatchStep G₀ sb (.delete e)).delEdges.length = sb.delEdges.length + 1 := by
      dsimp only [scanBatchStep]; split_ifs <;> simp
    have hinsL : (scanBatchStep G₀ sb (.delete e)).insEdges.length = sb.insEdges.length := by
      dsimp only [scanBatchStep]; split_ifs <;> simp
    refine ⟨stE, cAll, hfull,
      scanRegsAt_of_lt15 hR hkr (by simp [stE]) (by simp [stE, hr16D])
        (by simp only [stE, Function.update_of_ne (by decide : (17 : ℕ) ≠ 15)]
            rw [hregsD 17 (by decide) (by decide)]; simp [stA, hdelL])
        (by simp only [stE, Function.update_of_ne (by decide : (18 : ℕ) ≠ 15)]
            rw [hregsD 18 (by decide) (by decide)]; simp [stA, r18, hinsL])
        (by simp only [stE, Function.update_of_ne (by decide : (19 : ℕ) ≠ 15)]
            rw [hregsD 19 (by decide) (by decide)]; simp [stA, r19]),
      hMD', by omega⟩
  | split v v' St Sh =>
    obtain ⟨hv, hv'⟩ := huCap
    obtain ⟨tag, Lt, Lh, htag, hlen, hlist⟩ :
        ∃ tag Lt Lh, (tag = 2 ∨ tag = 3) ∧ len = 5 + Lt.length + Lh.length ∧
          ListAt mem₀ cur ([tag, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) := by
      rcases huAt with ⟨Lt, Lh, _, _, _, _, hlen, hlist⟩ | ⟨Lt, Lh, _, _, _, _, hlen, hlist⟩
      · exact ⟨2, Lt, Lh, Or.inl rfl, hlen, hlist⟩
      · exact ⟨3, Lt, Lh, Or.inr rfl, hlen, hlist⟩
    have hm0 : st.mem cur = tag := (hbat_eq cur (le_refl _) (by omega)).trans (by simpa using hlist 0 (by simp))
    have hm1 : st.mem (cur + 1) = v := (hbat_eq (cur + 1) (by omega) (by omega)).trans (by simpa using hlist 1 (by simp))
    have hm2 : st.mem (cur + 2) = v' := (hbat_eq (cur + 2) (by omega) (by omega)).trans (by simpa using hlist 2 (by simp))
    have hm3 : st.mem (cur + 3) = Lt.length := (hbat_eq (cur + 3) (by omega) (by omega)).trans (by simpa using hlist 3 (by simp))
    have hm4 : st.mem (cur + 4) = Lh.length := (hbat_eq (cur + 4) (by omega) (by omega)).trans (by simpa using hlist 4 (by simp))
    have hcv : sb.cmpMap v < nComp := hcmp_lt v huValid.1
    set ov := sb.origVert v
    set ov' := if ov = 0 then v + 1 else ov
    set sb1 : ScanBatchState := { sb with
      cmpMap := Function.update sb.cmpMap v' (sb.cmpMap v)
      origVert := Function.update sb.origVert v' ov' }
    set memA := Function.update st.mem (cmpH + v') (sb.cmpMap v)
    set memB := Function.update memA (scanOrigVertBase h eCap + v') ov'
    have hMB : ScanMemAt mem₀ memB cmpH ctH nComp vCap eCap words h sb1 := scanMemAt_split hGeo hv' hM
    have hcv_m : st.mem (cmpH + v) = sb.cmpMap v := hM.1 v hv
    have hov_m : memA (scanOrigVertBase h eCap + v) = ov := by
      dsimp only [memA]; rw [Function.update_of_ne (by unfold scanOrigVertBase; omega)]; exact hM.2.2.2.2.1 v hv
    set rA := Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update st.regs 20 tag) 21 v) 22 v') 23 Lt.length) 24 Lh.length)
      25 (sb.cmpMap v)) 26 ov
    have hcondOv : ∃ c1, Runs w p ω
        (.cond (.bin .eq (.reg 26) (.const 0))
          (.store (.bin .add (.reg 10) (.reg 22)) (.bin .add (.reg 21) (.const 1)))
          (.store (.bin .add (.reg 10) (.reg 22)) (.reg 26)))
        ⟨memA, rA, st.pos⟩ .normal ⟨memB, rA, st.pos⟩ c1 ∧ c1 ≤ 15 := by
      by_cases hov0 : ov = 0
      · have heC : (Expr.bin .eq (.reg 26) (.const 0)).eval w ⟨memA, rA, st.pos⟩ = some 1 := by
          simp [Expr.eval, rA, hov0, BinOp.eval, (by omega : 0 < 2 ^ w), h1w]
        have hs : Runs w p ω (.store (.bin .add (.reg 10) (.reg 22)) (.bin .add (.reg 21) (.const 1)))
            ⟨memA, rA, st.pos⟩ .normal ⟨memB, rA, st.pos⟩ 7 := by
          have hov'_eq : ov' = v + 1 := by simp [ov', hov0]
          exact runs_store_iff.mpr ⟨scanOrigVertBase h eCap + v', v + 1,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r10])) (Expr.eval_reg_of_eq (by simp [rA]))
              (by unfold scanOrigVertBase; omega),
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA])) (Expr.eval_const h1w) (by omega), rfl,
            by simp [memB, hov'_eq], rfl⟩
        exact ⟨11, runs_cond_iff.mpr ⟨1, 7, heC, by simpa using hs, rfl⟩, by omega⟩
      · have heC : (Expr.bin .eq (.reg 26) (.const 0)).eval w ⟨memA, rA, st.pos⟩ = some 0 := by
          simp [Expr.eval, rA, hov0, BinOp.eval, (by omega : 0 < 2 ^ w)]
        have hs : Runs w p ω (.store (.bin .add (.reg 10) (.reg 22)) (.reg 26))
            ⟨memA, rA, st.pos⟩ .normal ⟨memB, rA, st.pos⟩ 5 := by
          have hov'_eq : ov' = ov := by simp [ov', hov0]
          exact runs_store_iff.mpr ⟨scanOrigVertBase h eCap + v', ov,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, r10])) (Expr.eval_reg_of_eq (by simp [rA]))
              (by unfold scanOrigVertBase; omega),
            Expr.eval_reg_of_eq (by simp [rA]), rfl, by simp [memB, hov'_eq], rfl⟩
        exact ⟨9, runs_cond_iff.mpr ⟨0, 5, heC, by simpa using hs, rfl⟩, by omega⟩
    obtain ⟨c1, hc1_run, hc1_le⟩ := hcondOv
    obtain ⟨stD, cD, hrunD, hregsD, hr16D, hMD', hcD⟩ :=
      asmScanActivate_runs (p := p) (ω := ω) (rComp := 25) (rVert := 21) (c := sb.cmpMap v) (v := v)
        (sb := sb1) (st := ⟨memB, rA, st.pos⟩) hGeo
        (by simp [rA, r2]) (by simp [rA, r11]) (by simp [rA, r16, sb1])
        (by simp [rA]) (by simp [rA]) (by decide) (by decide) hcv hv (by simp [sb1]; omega) hMB
    have hstD_15 : stD.regs 15 = cur := by rw [hregsD 15 (by decide) (by decide)]; simp [rA, r15]
    have hstD_23 : stD.regs 23 = Lt.length := by rw [hregsD 23 (by decide) (by decide)]; simp [rA]
    have hstD_24 : stD.regs 24 = Lh.length := by rw [hregsD 24 (by decide) (by decide)]; simp [rA]
    set stE : State := ⟨stD.mem, Function.update stD.regs 15 (cur + len), stD.pos⟩
    have ha15 : Runs w p ω (.assign 15 (.bin .add (.bin .add (.bin .add (.reg 15) (.const 5)) (.reg 23)) (.reg 24)))
        stD .normal stE 8 := by
      have he15 : (Expr.bin .add (.bin .add (.bin .add (.reg 15) (.const 5)) (.reg 23)) (.reg 24)).eval w stD =
          some (cur + 5 + Lt.length + Lh.length) :=
        Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hstD_15)
          (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq hstD_23) (by omega))
          (Expr.eval_reg_of_eq hstD_24) (by omega)
      rw [show cur + 5 + Lt.length + Lh.length = cur + len by omega] at he15
      exact runs_assign_iff.mpr ⟨cur + len, he15, rfl, rfl, rfl⟩
    have hcond0 : (Expr.bin .eq (.reg 20) (.const 0)).eval w ⟨st.mem, Function.update st.regs 20 tag, st.pos⟩ = some 0 := by
      rcases htag with rfl | rfl <;> simp [Expr.eval, BinOp.eval, (by omega : 0 < 2 ^ w)]
    have hcond1 : (Expr.bin .eq (.reg 20) (.const 1)).eval w ⟨st.mem, Function.update st.regs 20 tag, st.pos⟩ = some 0 := by
      rcases htag with rfl | rfl <;> simp [Expr.eval, BinOp.eval, (by omega : 0 < 2 ^ w), h1w]
    obtain ⟨cAll, hfull, hcAll⟩ : ∃ c, Runs w p ω asmFirstScanBatchBody st .normal stE c ∧ 0 + c ≤ 235 := by
      unfold asmFirstScanBatchBody
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_reg_of_eq r15) hm0)
        (rCondFLe hcond0 (rCondFLe hcond1 ?_))
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r15]; try rfl))
        (Expr.eval_const h1w) (by omega)) hm1) ?_
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r15]; try rfl))
        (Expr.eval_const (by omega)) (by omega)) hm2) ?_
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r15]; try rfl))
        (Expr.eval_const (by omega)) (by omega)) hm3) ?_
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r15]; try rfl))
        (Expr.eval_const (by omega)) (by omega)) hm4) ?_
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1]; try rfl))
        (Expr.eval_reg_of_eq (by simp; try rfl)) (by omega)) hcv_m) ?_
      refine rStoreLe (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1]; try rfl))
        (Expr.eval_reg_of_eq (by simp; try rfl)) (by omega)) (Expr.eval_reg_of_eq (by simp; try rfl)) ?_
      refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r10]; try rfl))
        (Expr.eval_reg_of_eq (by simp; try rfl)) (by unfold scanOrigVertBase; omega)) hov_m) ?_
      exact ⟨_, runs_seq_iff.mpr (Or.inr ⟨⟨memB, rA, st.pos⟩, c1, _, hc1_run,
        runs_seq_iff.mpr (Or.inr ⟨stD, cD, 8, hrunD, ha15, rfl⟩), rfl⟩), by simp only [Expr.size]; omega⟩
    have hkr : ∀ r < 15, stE.regs r = st.regs r := fun r hr => by
      simp only [stE, Function.update_of_ne (by omega : r ≠ 15)]
      rw [hregsD r (by omega) (by omega)]
      simp [rA, Function.update_of_ne (by omega : r ≠ 26), Function.update_of_ne (by omega : r ≠ 25),
        Function.update_of_ne (by omega : r ≠ 24), Function.update_of_ne (by omega : r ≠ 23),
        Function.update_of_ne (by omega : r ≠ 22), Function.update_of_ne (by omega : r ≠ 21),
        Function.update_of_ne (by omega : r ≠ 20)]
    rw [show scanBatchStep G₀ sb (.split v v' St Sh) = scanActivate sb1 (sb.cmpMap v) v
      by simp [scanBatchStep, sb1, ov', ov]]
    refine ⟨stE, cAll, hfull,
      scanRegsAt_of_lt15 hR hkr (by simp [stE]) (by simp [stE, hr16D])
        (by simp only [stE, Function.update_of_ne (by decide : (17 : ℕ) ≠ 15)]
            rw [hregsD 17 (by decide) (by decide)]; simp [rA, r17, sb1])
        (by simp only [stE, Function.update_of_ne (by decide : (18 : ℕ) ≠ 15)]
            rw [hregsD 18 (by decide) (by decide)]; simp [rA, r18, sb1])
        (by simp only [stE, Function.update_of_ne (by decide : (19 : ℕ) ≠ 15)]
            rw [hregsD 19 (by decide) (by decide)]; simp [rA, r19]),
      hMD', by omega⟩

/-- **Full verification of `asmFirstScanBatchStmt`**: runs the Phase 1 batch scan on
`[gPtr, cmpH, ctH, batch, words, vCap, eCap, h]` matching `scanBatchFold tr.cs.G st0 U`, writing
`[nNew, nDel, nIns]` at `[h, h + 3)` and returning `h + asmFirstScanBatchSpace vCap eCap words` in
`≤ 245 * words + 120` steps. The component map only needs to be in range on the vertices of
`tr.cs.G` (`hCmp0_lt`), since the scan reads it only at vertices of the current graph. -/
theorem asmFirstScanBatch_runs {w depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {p : Program} {ω : ℕ → Bool}
    {gPtr cmpH ctH batch words vCap eCap h pos : ℕ}
    {tr : BundleTreeState depth} {U : List Update} {comps : List (Finset ℕ)}
    {cmpMap₀ : ℕ → ℕ} {mem₀ : ℕ → ℕ}
    (_hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hCaps : BatchWithinCaps vCap eCap U)
    (_hCnd : comps.Nodup) (_hCiff : ∀ C, C ∈ comps ↔ C ∈ components tr.cs.G₀)
    (hCmp0_mem : ∀ v < vCap, mem₀ (cmpH + v) = cmpMap₀ v)
    (hCmp0_lt : ∀ v ∈ tr.cs.G.V, cmpMap₀ v < comps.length)
    (_hCmp0_ok : ∀ c (hc : c < comps.length), ∀ v ∈ (tr.cs.compSt comps[c]).G.V, cmpMap₀ v = c)
    (hCt0_mem : ∀ c (hc : c < comps.length),
      mem₀ (ctH + 3 * c) = if comps[c] ∈ tr.activeComps then 1 else 0)
    (_hCross : AsmFirstCrossInactiveInv tr)
    (hG0 : DynGraphAt mem₀ gPtr vCap eCap tr.cs.G)
    (hBat : BatchAt mem₀ batch tr.cs.G U words)
    (hGeo : ScanGeom w gPtr cmpH ctH comps.length batch words vCap eCap h)
    (hz : ZeroFrom mem₀ h) :
    let st0 : ScanBatchState :=
      { cmpMap := cmpMap₀
        actFlag := fun c => if hc : c < comps.length then decide (comps[c] ∈ tr.activeComps) else false
        insFlag := fun _ => false
        delFlag := fun _ => false
        origVert := fun _ => 0
        newComps := []
        delEdges := []
        insEdges := [] }
    let sbF := scanBatchFold tr.cs.G st0 U
    ∃ st' cost,
      Runs w p ω asmFirstScanBatchStmt
        (startState [gPtr, cmpH, ctH, batch, words, vCap, eCap, h] mem₀ pos)
        (.returned (h + asmFirstScanBatchSpace vCap eCap words)) st' cost ∧
      st'.mem h = sbF.newComps.length ∧
      st'.mem (h + 1) = sbF.delEdges.length ∧
      st'.mem (h + 2) = sbF.insEdges.length ∧
      ScanMemAt mem₀ st'.mem cmpH ctH comps.length vCap eCap words h sbF ∧
      cost ≤ 245 * words + 120 := by
  classical
  intro st0 sbF
  have hsp' : h + (3 + 2 * eCap + vCap + 6 * words) < 2 ^ w := hGeo.hsp
  have hw16 : 16 ≤ 2 ^ w := hGeo.hw16
  have h1w : 1 < 2 ^ w := by omega
  have hUL : 2 * U.length ≤ words - 1 := batchBodyAt_len_le hBat.2.2
  have hM0 : ScanMemAt mem₀ mem₀ cmpH ctH comps.length vCap eCap words h st0 :=
    ⟨hCmp0_mem, fun c hc => by simp [st0, hc, hCt0_mem c hc],
     fun e _ => by simp [st0, hz (scanInsFlagBase h + e) (by unfold scanInsFlagBase; omega)],
     fun e _ => by simp [st0, hz (scanDelFlagBase h eCap + e) (by unfold scanDelFlagBase; omega)],
     fun v _ => by simp [st0, hz (scanOrigVertBase h eCap + v) (by unfold scanOrigVertBase; omega)],
     fun _ hi => by simp [st0] at hi, fun _ hi => by simp [st0] at hi, fun _ hi => by simp [st0] at hi,
     fun _ _ _ _ => rfl, fun a ha => hz a (by omega)⟩
  set s0 := startState [gPtr, cmpH, ctH, batch, words, vCap, eCap, h] mem₀ pos
  set rInit : ℕ → ℕ :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update s0.regs 8 (scanInsFlagBase h)) 9 (scanDelFlagBase h eCap))
    10 (scanOrigVertBase h eCap)) 11 (scanNewCompsBase h vCap eCap))
    12 (scanDelEdgesBase h vCap eCap words)) 13 (scanInsEdgesBase h vCap eCap words))
    14 U.length) 15 (batch + 1)) 16 0) 17 0) 18 0
  have hloop : ∀ (k : ℕ) (hk : k ≤ U.length) (cur W : ℕ) (stK : State),
      let csK := compLSFBatch tr.cs (U.take k)
      let sbK := scanBatchFold tr.cs.G st0 (U.take k)
      batch < cur → cur + W ≤ batch + words →
      BatchBodyAt mem₀ cur csK.G (U.drop k) W →
      (∀ v ∈ csK.G.V, sbK.cmpMap v < comps.length) →
      (∀ v < vCap, sbK.origVert v < 2 ^ w) →
      sbK.newComps.length ≤ 2 * k → sbK.delEdges.length ≤ k → sbK.insEdges.length ≤ k →
      (∀ e ∈ csK.G.E, sbK.insFlag e = false → e ∈ tr.cs.G.E) →
      ScanRegsAt stK.regs gPtr cmpH ctH batch words vCap eCap h U.length cur sbK k →
      ScanMemAt mem₀ stK.mem cmpH ctH comps.length vCap eCap words h sbK →
      ∃ stF cF,
        Runs w p ω (forUp 19 (.reg 14) asmFirstScanBatchBody) stK .normal stF cF ∧
        ScanRegsAt stF.regs gPtr cmpH ctH batch words vCap eCap h U.length (cur + W) sbF U.length ∧
        ScanMemAt mem₀ stF.mem cmpH ctH comps.length vCap eCap words h sbF ∧
        cF ≤ 245 * (U.length - k) + 10 := by
    intro k
    induction hrem : U.length - k generalizing k with
    | zero =>
      intro hk cur W stK csK sbK _ _ hBB _ _ _ _ _ _ hRK hMK
      have hkEq : k = U.length := by omega
      subst hkEq
      rw [List.drop_length] at hBB; have hW0 : W = 0 := hBB; subst hW0
      simp only [sbK, List.take_length] at hRK hMK
      have hcond : (Expr.bin .lt (.reg 19) (.reg 14)).eval w stK = some 0 := by
        simp [Expr.eval, hRK.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hRK.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
          BinOp.eval, (by omega : 0 < 2 ^ w)]
      exact ⟨stK, 4, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩), by simpa using hRK, hMK, by omega⟩
    | succ d ih =>
      intro hk cur W stK csK sbK hclo hchi hBB hclt howl hnl hdl hil hins0 hRK hMK
      have hklt : k < U.length := by omega
      obtain ⟨u, hu_eq⟩ : ∃ u, U[k]'hklt = u := ⟨_, rfl⟩
      have hdrop : U.drop k = u :: U.drop (k + 1) := by rw [← hu_eq]; exact List.drop_eq_getElem_cons hklt
      have htake : U.take (k + 1) = U.take k ++ [u] := by rw [← hu_eq]; exact List.take_succ_eq_append_getElem hklt
      rw [hdrop] at hBB
      obtain ⟨len, hlenW, huAt, hBBrest⟩ := hBB
      have hU_valid_k : (tr.cs.G.applyBatch (U.take k)).BatchIsValid (u :: U.drop (k + 1)) := by
        have hv := hU; rw [show U = U.take k ++ u :: U.drop (k + 1) by rw [← hdrop, List.take_append_drop]] at hv
        exact (batchIsValid_append.mp hv).2
      have huValid : csK.G.UpdateIsValid u := (compLSFBatch_G tr.cs (U.take k)) ▸ hU_valid_k.1
      have huc : UpdateWithinCaps vCap eCap u := hCaps u (hu_eq ▸ List.getElem_mem hklt)
      obtain ⟨hvK, heK⟩ := batchWithinCaps_applyBatch (vCap := vCap) (eCap := eCap)
        (fun x hx => hCaps x (List.mem_of_mem_take hx)) hG0.2.1 hG0.2.2.1
      rw [← compLSFBatch_G tr.cs (U.take k)] at hvK heK
      have huCap : ScanUpdateCap vCap eCap tr.cs.G sbK u := by
        cases u with
        | insert e a b => exact ⟨huc, hvK a huValid.2.1, hvK b huValid.2.2⟩
        | delete e => exact ⟨heK e huValid, fun hF => hins0 e huValid hF⟩
        | split v v' _ _ => exact ⟨hvK v huValid.1, huc⟩
      obtain ⟨st1, c1, hrun1, hR1, hM1, hc1⟩ :=
        asmFirstScanBatchBody_runs (p := p) (ω := ω) (G₀ := tr.cs.G) (Gcur := csK.G)
          hGeo hG0 hclo (by omega) huAt huCap huValid
          (by show tr.cs.G.V ⊆ (compLSFBatch tr.cs (U.take k)).G.V
              rw [compLSFBatch_G]; exact applyBatch_V_sub _ _)
          hclt howl (by omega) (by omega) (by omega) hRK hMK
      set st2 : State := ⟨st1.mem, Function.update st1.regs 19 (k + 1), st1.pos⟩
      have ha19 : Runs w p ω (.assign 19 (.bin .add (.reg 19) (.const 1))) st1 .normal st2 4 :=
        runs_assign_iff.mpr ⟨k + 1,
          Expr.eval_add (Expr.eval_reg_of_eq hR1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
            (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
      have hsbK1 : scanBatchFold tr.cs.G st0 (U.take (k + 1)) = scanBatchStep tr.cs.G sbK u := by
        simp only [scanBatchFold, htake, List.foldl_append, List.foldl_cons, List.foldl_nil]; try rfl
      have hcsK1 : compLSFBatch tr.cs (U.take (k + 1)) = compLSFStepSingle csK u := by
        simp only [compLSFBatch, htake, List.foldl_append, List.foldl_cons, List.foldl_nil]; try rfl
      have hR2 : ScanRegsAt st2.regs gPtr cmpH ctH batch words vCap eCap h U.length (cur + len)
          (scanBatchFold tr.cs.G st0 (U.take (k + 1))) (k + 1) := by
        rw [hsbK1]
        exact scanRegsAt_of_lt15 hR1 (fun r hr => by simp [st2, Function.update_of_ne (by omega : r ≠ 19)])
          (by simp [st2, hR1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])
          (by simp [st2, hR1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])
          (by simp [st2, hR1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1])
          (by simp [st2, hR1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]) (by simp [st2])
      have hstep_clt : ∀ v ∈ (compLSFStepSingle csK u).G.V,
          (scanBatchStep tr.cs.G sbK u).cmpMap v < comps.length := fun v hv => by
        cases u with
        | insert _ _ _ => simpa [scanBatchStep] using hclt v hv
        | delete _ => dsimp only [scanBatchStep]; split_ifs <;> simpa using hclt v hv
        | split v₀ v' _ _ =>
          simp only [scanBatchStep, scanActivate_cmpMap]
          by_cases hEq : v = v'
          · subst hEq; simp [hclt v₀ huValid.1]
          · rw [Function.update_of_ne hEq]
            exact hclt v ((Finset.mem_insert.mp hv).resolve_left hEq)
      have hstep_owl : ∀ v < vCap, (scanBatchStep tr.cs.G sbK u).origVert v < 2 ^ w := fun v hv => by
        cases u with
        | insert _ _ _ => simpa [scanBatchStep] using howl v hv
        | delete _ => dsimp only [scanBatchStep]; split_ifs <;> simpa using howl v hv
        | split v₀ v' _ _ =>
          simp only [scanBatchStep, scanActivate_origVert]
          by_cases hEq : v = v'
          · subst hEq; simp only [Function.update_self]; split_ifs
            · have := hGeo.hcmp_le; have := hvK v₀ huValid.1; omega
            · exact howl v₀ (hvK v₀ huValid.1)
          · rw [Function.update_of_ne hEq]; exact howl v hv
      have hstep_nl : (scanBatchStep tr.cs.G sbK u).newComps.length ≤ 2 * (k + 1) := by
        cases u with
        | insert e a b =>
          dsimp only [scanBatchStep]
          have h1 := scanActivate_newComps_len (scanActivate { sbK with insFlag := Function.update sbK.insFlag e true, insEdges := sbK.insEdges ++ [e] } (sbK.cmpMap a) a)
            ((scanActivate { sbK with insFlag := Function.update sbK.insFlag e true, insEdges := sbK.insEdges ++ [e] } (sbK.cmpMap a) a).cmpMap b) b
          have h2 := scanActivate_newComps_len { sbK with insFlag := Function.update sbK.insFlag e true, insEdges := sbK.insEdges ++ [e] } (sbK.cmpMap a) a
          dsimp only at h1 h2 ⊢; omega
        | delete e =>
          dsimp only [scanBatchStep]
          split_ifs
          · dsimp only; omega
          · have h1 := scanActivate_newComps_len (scanActivate { sbK with delFlag := Function.update sbK.delFlag e true, delEdges := sbK.delEdges ++ [e] } (sbK.cmpMap (tr.cs.G.tail e)) (tr.cs.G.tail e))
              ((scanActivate { sbK with delFlag := Function.update sbK.delFlag e true, delEdges := sbK.delEdges ++ [e] } (sbK.cmpMap (tr.cs.G.tail e)) (tr.cs.G.tail e)).cmpMap (tr.cs.G.head e)) (tr.cs.G.head e)
            have h2 := scanActivate_newComps_len { sbK with delFlag := Function.update sbK.delFlag e true, delEdges := sbK.delEdges ++ [e] } (sbK.cmpMap (tr.cs.G.tail e)) (tr.cs.G.tail e)
            dsimp only at h1 h2 ⊢; omega
        | split v v' _ _ =>
          dsimp only [scanBatchStep]
          have h1 := scanActivate_newComps_len { sbK with cmpMap := Function.update sbK.cmpMap v' (sbK.cmpMap v), origVert := Function.update sbK.origVert v' (if sbK.origVert v = 0 then v + 1 else sbK.origVert v) } (sbK.cmpMap v) v
          dsimp only at h1 ⊢; omega
      have hstep_dl : (scanBatchStep tr.cs.G sbK u).delEdges.length ≤ k + 1 := by
        cases u <;> (dsimp only [scanBatchStep]; try split_ifs) <;> simp <;> omega
      have hstep_il : (scanBatchStep tr.cs.G sbK u).insEdges.length ≤ k + 1 := by
        cases u <;> (dsimp only [scanBatchStep]; try split_ifs) <;> simp <;> omega
      have hstep_ins0 : ∀ e ∈ (compLSFStepSingle csK u).G.E,
          (scanBatchStep tr.cs.G sbK u).insFlag e = false → e ∈ tr.cs.G.E := fun e he hF => by
        cases u with
        | insert e₀ _ _ =>
          simp only [scanBatchStep, scanActivate_insFlag] at hF
          have hne : e ≠ e₀ := by rintro rfl; simp at hF
          rw [Function.update_of_ne hne] at hF
          exact hins0 e (by simpa [compLSFStepSingle, MGraph.applyUpdate, hne] using he) hF
        | delete e₀ =>
          have hF0 : sbK.insFlag e = false := by dsimp only [scanBatchStep] at hF; split_ifs at hF <;> simpa using hF
          exact hins0 e (Finset.mem_erase.mp he).2 hF0
        | split _ _ _ _ =>
          simp only [scanBatchStep, scanActivate_insFlag] at hF; exact hins0 e he hF
      obtain ⟨stF, cF, hrunF, hRF, hMF, hcF⟩ :=
        ih (k + 1) (by omega) (by omega) (cur + len) (W - len) st2
          (by omega) (by omega) (by rw [hcsK1]; exact hBBrest)
          (by rw [hcsK1, hsbK1]; exact hstep_clt) (by rw [hsbK1]; exact hstep_owl)
          (by rw [hsbK1]; exact hstep_nl) (by rw [hsbK1]; exact hstep_dl)
          (by rw [hsbK1]; exact hstep_il) (by rw [hcsK1, hsbK1]; exact hstep_ins0)
          hR2 (by rw [hsbK1]; exact hM1)
      have hcond : (Expr.bin .lt (.reg 19) (.reg 14)).eval w stK = some 1 := by
        simp [Expr.eval, hRK.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hRK.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
          BinOp.eval, hklt, h1w]
      exact ⟨stF, _, runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st2, _, cF, hcond, by decide,
        runs_seq_iff.mpr (Or.inr ⟨st1, c1, 4, hrun1, ha19, rfl⟩), hrunF, rfl⟩)),
        by rwa [show cur + len + (W - len) = cur + W by omega] at hRF, hMF, by simp only [Expr.size]; omega⟩
  set stLoop0 : State := ⟨mem₀, Function.update rInit 19 0, pos⟩
  have ha19_0 : Runs w p ω (.assign 19 (.const 0)) ⟨mem₀, rInit, pos⟩ .normal stLoop0 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  have hR0 : ScanRegsAt stLoop0.regs gPtr cmpH ctH batch words vCap eCap h U.length (batch + 1) st0 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [stLoop0, rInit, s0, startState, st0]
  obtain ⟨stF, cF, hrunF, hRF, hMF, hcF⟩ :=
    hloop 0 (Nat.zero_le _) (batch + 1) (words - 1) stLoop0
      (by omega) (by have := hBat.1; omega) hBat.2.2 hCmp0_lt (fun _ _ => by simp [scanBatchFold, st0])
      (by simp [scanBatchFold, st0]) (by simp [scanBatchFold, st0]) (by simp [scanBatchFold, st0])
      (fun _ he _ => he) (by simpa [scanBatchFold] using hR0) (by simpa [scanBatchFold] using hM0)
  have hret_eq : scanInsEdgesBase h vCap eCap words + words = h + asmFirstScanBatchSpace vCap eCap words := by
    unfold scanInsEdgesBase asmFirstScanBatchSpace; omega
  set memF1 := Function.update stF.mem h sbF.newComps.length
  set memF2 := Function.update memF1 (h + 1) sbF.delEdges.length
  set memF3 := Function.update memF2 (h + 2) sbF.insEdges.length
  have heRet : (Expr.bin .add (.reg 13) (.reg 4)).eval w ⟨memF3, stF.regs, stF.pos⟩ =
      some (h + asmFirstScanBatchSpace vCap eCap words) := by
    have h1 : (Expr.bin .add (.reg 13) (.reg 4)).eval w ⟨memF3, stF.regs, stF.pos⟩ =
        some (scanInsEdgesBase h vCap eCap words + words) :=
      Expr.eval_add (Expr.eval_reg_of_eq hRF.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
        (Expr.eval_reg_of_eq hRF.2.2.2.2.1) (by rw [hret_eq]; exact hGeo.hsp)
    rwa [hret_eq] at h1
  obtain ⟨cEpi, hepi, hcEpi⟩ : ∃ c, Runs w p ω
      (.store (.reg 7) (.reg 16) ;;
       .store (.bin .add (.reg 7) (.const 1)) (.reg 17) ;;
       .store (.bin .add (.reg 7) (.const 2)) (.reg 18) ;;
       .ret (.bin .add (.reg 13) (.reg 4)))
      stF (.returned (h + asmFirstScanBatchSpace vCap eCap words)) ⟨memF3, stF.regs, stF.pos⟩ c ∧ 0 + c ≤ 35 := by
    refine rStoreLe (Expr.eval_reg_of_eq hRF.2.2.2.2.2.2.2.1)
      (Expr.eval_reg_of_eq hRF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
    refine rStoreLe (Expr.eval_add (Expr.eval_reg_of_eq hRF.2.2.2.2.2.2.2.1) (Expr.eval_const h1w) (by omega))
      (Expr.eval_reg_of_eq hRF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
    refine rStoreLe (Expr.eval_add (Expr.eval_reg_of_eq hRF.2.2.2.2.2.2.2.1) (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_reg_of_eq hRF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) ?_
    exact ⟨_, runs_ret_iff.mpr ⟨_, heRet, rfl, rfl, rfl⟩, by simp only [Expr.size]; omega⟩
  have hmemF3_of : ∀ a, a ≠ h → a ≠ h + 1 → a ≠ h + 2 → memF3 a = stF.mem a := fun a h0 h1 h2 => by
    simp [memF3, memF2, memF1, Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]
  obtain ⟨hMc, hMct, hMif, hMdf, hMo, hMn, hMde, hMie, hMfr, hMzf⟩ := hMF
  have hcl := hGeo.hcmp_le; have htl := hGeo.hct_le
  obtain ⟨cAll, hall, hcAll⟩ : ∃ c, Runs w p ω asmFirstScanBatchStmt s0
      (.returned (h + asmFirstScanBatchSpace vCap eCap words)) ⟨memF3, stF.regs, stF.pos⟩ c ∧
      0 + c ≤ 245 * words + 120 := by
    unfold asmFirstScanBatchStmt
    refine rAssignLe (v := scanInsFlagBase h) (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]; try rfl))
        (Expr.eval_const (by omega)) (by omega)) (by unfold scanInsFlagBase; omega)) ?_
    refine rAssignLe (v := scanDelFlagBase h eCap) (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp; try rfl))
        (Expr.eval_reg_of_eq (by simp [s0, startState]; try rfl)) (by unfold scanInsFlagBase; omega))
      (by unfold scanInsFlagBase scanDelFlagBase; omega)) ?_
    refine rAssignLe (v := scanOrigVertBase h eCap) (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp; try rfl))
        (Expr.eval_reg_of_eq (by simp [s0, startState]; try rfl)) (by unfold scanDelFlagBase; omega))
      (by unfold scanDelFlagBase scanOrigVertBase; omega)) ?_
    refine rAssignLe (v := scanNewCompsBase h vCap eCap) (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp; try rfl))
        (Expr.eval_reg_of_eq (by simp [s0, startState]; try rfl)) (by unfold scanOrigVertBase; omega))
      (by unfold scanOrigVertBase scanNewCompsBase; omega)) ?_
    refine rAssignLe (v := scanDelEdgesBase h vCap eCap words) (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp; try rfl))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [s0, startState]; try rfl)) (by omega))
        (by unfold scanNewCompsBase; omega))
      (by unfold scanNewCompsBase scanDelEdgesBase; omega)) ?_
    refine rAssignLe (v := scanInsEdgesBase h vCap eCap words) (Expr.eval_eq_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp; try rfl))
        (Expr.eval_reg_of_eq (by simp [s0, startState]; try rfl)) (by unfold scanDelEdgesBase; omega))
      (by unfold scanDelEdgesBase scanInsEdgesBase; omega)) ?_
    refine rAssignLe (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [s0, startState])) hBat.2.1) ?_
    refine rAssignLe (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]; try rfl))
      (Expr.eval_const h1w) (by have := hGeo.hbat_le; omega)) ?_
    refine rAssignLe (Expr.eval_const (by omega)) ?_
    refine rAssignLe (Expr.eval_const (by omega)) ?_
    refine rAssignLe (Expr.eval_const (by omega)) ?_
    exact ⟨2 + cF + 1 + cEpi + 1,
      runs_seq_iff.mpr (Or.inr ⟨stF, 2 + cF + 1, cEpi,
        runs_seq_iff.mpr (Or.inr ⟨stLoop0, 2, cF, ha19_0, hrunF, rfl⟩), hepi, rfl⟩),
      by simp only [Expr.size]; omega⟩
  have hMF3 : ScanMemAt mem₀ memF3 cmpH ctH comps.length vCap eCap words h sbF :=
    ⟨fun v hv => by rw [hmemF3_of _ (by omega) (by omega) (by omega)]; exact hMc v hv,
     fun c hc => by rw [hmemF3_of _ (by omega) (by omega) (by omega)]; exact hMct c hc,
     fun e he => by rw [hmemF3_of _ (by unfold scanInsFlagBase; omega) (by unfold scanInsFlagBase; omega) (by unfold scanInsFlagBase; omega)]; exact hMif e he,
     fun e he => by rw [hmemF3_of _ (by unfold scanDelFlagBase; omega) (by unfold scanDelFlagBase; omega) (by unfold scanDelFlagBase; omega)]; exact hMdf e he,
     fun v hv => by rw [hmemF3_of _ (by unfold scanOrigVertBase; omega) (by unfold scanOrigVertBase; omega) (by unfold scanOrigVertBase; omega)]; exact hMo v hv,
     fun j hj => by rw [hmemF3_of _ (by unfold scanNewCompsBase; omega) (by unfold scanNewCompsBase; omega) (by unfold scanNewCompsBase; omega),
       hmemF3_of _ (by unfold scanNewCompsBase; omega) (by unfold scanNewCompsBase; omega) (by unfold scanNewCompsBase; omega)]; exact hMn j hj,
     fun j hj => by rw [hmemF3_of _ (by unfold scanDelEdgesBase; omega) (by unfold scanDelEdgesBase; omega) (by unfold scanDelEdgesBase; omega)]; exact hMde j hj,
     fun j hj => by rw [hmemF3_of _ (by unfold scanInsEdgesBase; omega) (by unfold scanInsEdgesBase; omega) (by unfold scanInsEdgesBase; omega)]; exact hMie j hj,
     fun x hx h1 h2 => by rw [hmemF3_of x (by omega) (by omega) (by omega)]; exact hMfr x hx h1 h2,
     fun x hx => by
       have hx' : h + (3 + 2 * eCap + vCap + 6 * words) ≤ x := hx
       rw [hmemF3_of x (by omega) (by omega) (by omega)]; exact hMzf x hx⟩
  exact ⟨⟨memF3, stF.regs, stF.pos⟩, cAll, hall,
    by simp [memF3, memF2, memF1], by simp [memF3, memF2], by simp [memF3], hMF3, by omega⟩

end

end MinCostFlow.SparseCore.Program
