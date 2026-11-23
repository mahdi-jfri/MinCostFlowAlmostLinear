module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActLoops

import WordRAM.Tactic

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## 3a. Preparation prefix verification (`asmFirstInitOneCompPrepStmt`) -/

public section

/-- Cost bound of `asmFirstInitOneCompPrepStmt` on `len`, `m_C`, `r`. -/
@[expose] def newActPrepCost (len m_C r : ℕ) : ℕ :=
  200 * len * (Nat.log 2 (len + 1) + 1) + 200 * m_C * (Nat.log 2 (m_C + 1) + 1) +
  m_C * (45 * (Nat.log 2 (r + 1) + 1) + 80) + 120 * len + 120 * m_C + 120 * r + 500

set_option maxHeartbeats 1000000 in
/-- Verification of `asmFirstInitOneCompPrepStmt`: extracts `uniqE` and `uniqB`, constructs
`specs`, `assigns`, `csl`, `rPtr`, updates `ctH`, `ASM_SD_NSLOTS`, `lazySlotPtr`, and `slotsPtr`. -/
theorem asmFirstInitOneComp_prep_runs {w depth slotCap eCap bSort : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hpSort : p.HasAt bSort (sortProcs bSort))
    {restH tourH c v lazySlotPtr h h1 h2 : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    {bunH slotsPtr bktH ctH nSlots : ℕ}
    {comps : List (Finset ℕ)} {mem₀ : ℕ → ℕ} {st5 : State}
    (hc : c < comps.length)
    (hBktsEq : tr.activeBuckets comps[c] =
      ((coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
        (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c]).image tr.origBucket)
    (hCoreInG₀ : ∀ e ∈ (coreGraph tr.cs.G tr.cs.lsf).E,
      (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c] → e ∈ tr.cs.G₀.E)
    (heCapG : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hw16 : 16 ≤ 2 ^ w) (heCapW : 4 * eCap < 2 ^ w)
    (_hrc_w : tr.cs.RF.root v < 2 ^ w)
    (hCordIff : ∀ x, x ∈ outCoreOrder tr ord (tr.cs.RF.root v) ↔
      x.1 ∈ (coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
        (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c])
    (hrestH_lt : restH + ASM_SD_SIZE ≤ h)
    (hRec : mem₀ (restH + ASM_SD_BUN) = bunH ∧ mem₀ (restH + ASM_SD_SLOTS) = slotsPtr ∧
      mem₀ (restH + ASM_SD_NSLOTS) = nSlots ∧ mem₀ (restH + ASM_SD_BKT) = bktH ∧
      mem₀ (restH + ASM_SD_CT) = ctH)
    (hbkt_ok : ∀ e ∈ tr.cs.G₀.E, e < eCap ∧ st5.mem (bktH + e) = bucketCode (tr.origBucket e) ∧
      st5.mem (bktH + e) < 2 ^ w)
    (hbkt_lt : eCap = 0 ∨ bktH + eCap ≤ h) (hct_lt : ctH + 3 * comps.length ≤ h)
    (hsl_lt : slotsPtr + nSlots + (tr.activeBuckets comps[c]).card ≤ h) (hlazy_lt : lazySlotPtr + 2 ≤ h)
    (hCapRoom : nSlots + (tr.activeBuckets comps[c]).card ≤ slotCap)
    (hMutDisj :
      (∀ a, ctH + 3 * c + 1 ≤ a → a < ctH + 3 * c + 3 →
        ¬ (restH ≤ a ∧ a < restH + ASM_SD_SIZE) ∧ ¬ (bktH ≤ a ∧ a < bktH + eCap)) ∧
      (∀ a, slotsPtr + nSlots ≤ a → a < slotsPtr + nSlots + (tr.activeBuckets comps[c]).card →
        ¬ (restH ≤ a ∧ a < restH + ASM_SD_SIZE) ∧ ¬ (bktH ≤ a ∧ a < bktH + eCap) ∧
        ¬ (ctH + 3 * c + 1 ≤ a ∧ a < ctH + 3 * c + 3)) ∧
      (∀ a, lazySlotPtr ≤ a → a < lazySlotPtr + 2 →
        ¬ (restH ≤ a ∧ a < restH + ASM_SD_SIZE) ∧ ¬ (bktH ≤ a ∧ a < bktH + eCap) ∧
        ¬ (ctH + 3 * c + 1 ≤ a ∧ a < ctH + 3 * c + 3) ∧
        ¬ (slotsPtr + nSlots ≤ a ∧ a < slotsPtr + nSlots + (tr.activeBuckets comps[c]).card)))
    (hh_le : h ≤ h1) (hh1_le : h1 + (outCoreOrder tr ord (tr.cs.RF.root v)).length + 1 ≤ h2)
    (hEndL : EndListAt st5.mem h1 (outCoreOrder tr ord (tr.cs.RF.root v)))
    (hzL : ZeroFrom st5.mem h2)
    (hrec5 : ∀ i < ASM_SD_SIZE, st5.mem (restH + i) = mem₀ (restH + i))
    (hregs5 : st5.regs 0 = restH ∧ st5.regs 1 = tourH ∧ st5.regs 2 = c ∧
      st5.regs 4 = lazySlotPtr ∧ st5.regs 6 = h1 ∧ st5.regs 7 = tr.cs.RF.root v ∧
      st5.regs 8 = h2 ∧ st5.regs 9 = (outCoreOrder tr ord (tr.cs.RF.root v)).length ∧
      st5.regs 10 = ctH)
    (hSpace2 : let len := (outCoreOrder tr ord (tr.cs.RF.root v)).length
      let coreE := (coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
        (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c]
      let r := (tr.activeBuckets comps[c]).card
      h2 + 3 * len + 6 * coreE.card + 7 * r + 1 < 2 ^ w) :
    let cord := outCoreOrder tr ord
    let r_c := tr.cs.RF.root v
    let len := (cord r_c).length
    let coreE := (coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
      (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ comps[c]
    let r := (tr.activeBuckets comps[c]).card
    ∃ st28 cost, ∃ (uniqE uniqB : List ℕ), ∃ uniqE_ptr assigns specs csl rPtr,
      Runs w p ω (asmFirstInitOneCompPrepStmt bSort) st5 .normal st28 cost ∧
      uniqE.Pairwise (· < ·) ∧ uniqE.toFinset = coreE ∧
      uniqB.Pairwise (· < ·) ∧ uniqB.length = r ∧
      (∀ b, b ∈ tr.activeBuckets comps[c] ↔ bucketCode b ∈ uniqB) ∧
      (∀ x ∈ uniqB, x < 2 ^ w) ∧
      h2 ≤ uniqE_ptr ∧ uniqE_ptr + uniqE.length ≤ assigns ∧
      assigns + 2 * uniqE.length = specs ∧ specs + 2 * uniqB.length = csl ∧
      csl + 2 * uniqB.length = rPtr ∧ rPtr + 1 ≤ h2 + 2 * len + 6 * coreE.card + 7 * r + 1 ∧
      st28.regs 1 = tourH ∧ st28.regs 15 = uniqE.length ∧ st28.regs 20 = uniqB.length ∧
      st28.regs 22 = assigns ∧ st28.regs 24 = specs ∧ st28.regs 26 = rPtr ∧ st28.regs 29 = bunH ∧
      bundleReadPairs st28.mem specs uniqB.length =
        (List.range uniqB.length).map (fun bi =>
          (nSlots + bi, 4 * (uniqE.filter fun e => decide (uniqB.idxOf (bucketCode (tr.origBucket e)) = bi)).length)) ∧
      bundleReadPairs st28.mem assigns uniqE.length =
        uniqE.map (fun e => (e, nSlots + uniqB.idxOf (bucketCode (tr.origBucket e)))) ∧
      st28.mem rPtr = r_c ∧
      ListAt st28.mem uniqE_ptr uniqE ∧
      st28.mem (restH + ASM_SD_NSLOTS) = nSlots + r ∧
      st28.mem (ctH + 3 * c + 1) = csl ∧ st28.mem (ctH + 3 * c + 2) = r ∧
      (∀ bi (hbi : bi < uniqB.length),
        st28.mem (csl + 2 * bi) = uniqB[bi]'hbi ∧ st28.mem (csl + 2 * bi + 1) = nSlots + bi) ∧
      (∀ bi < r, st28.mem (slotsPtr + (nSlots + bi)) = nSlots + bi) ∧
      st28.mem lazySlotPtr = uniqE_ptr ∧ st28.mem (lazySlotPtr + 1) = uniqE.length ∧
      ZeroFrom st28.mem (rPtr + 1) ∧
      (∀ a < h2, a ≠ restH + ASM_SD_NSLOTS →
        ¬ (ctH + 3 * c + 1 ≤ a ∧ a < ctH + 3 * c + 3) →
        ¬ (slotsPtr + nSlots ≤ a ∧ a < slotsPtr + nSlots + r) →
        ¬ (lazySlotPtr ≤ a ∧ a < lazySlotPtr + 2) →
        st28.mem a = st5.mem a) ∧
      cost ≤ newActPrepCost len coreE.card r := by
  intro cord r_c len coreE r
  have h1w : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have h3w : 3 < 2 ^ w := by omega
  rcases hRec with ⟨hRecBun, hRecSlots, hRecNSlots, hRecBkt, _⟩
  rcases hMutDisj with ⟨hMD_ct, hMD_sl, hMD_lazy⟩
  rcases hregs5 with ⟨hr0_5, hr1_5, hr2_5, hr4_5, hr6_5, hr7_5, hr8_5, hr9_5, hr10_5⟩
  have hr9_5' : st5.regs 9 = len := hr9_5
  change h2 + 3 * len + 6 * coreE.card + 7 * r + 1 < 2 ^ w at hSpace2
  change nSlots + r ≤ slotCap at hCapRoom
  change ∀ a, slotsPtr + nSlots ≤ a → a < slotsPtr + nSlots + r → _ at hMD_sl
  change ∀ a, lazySlotPtr ≤ a → a < lazySlotPtr + 2 →
    ¬ (restH ≤ a ∧ a < restH + ASM_SD_SIZE) ∧ ¬ (bktH ≤ a ∧ a < bktH + eCap) ∧
    ¬ (ctH + 3 * c + 1 ≤ a ∧ a < ctH + 3 * c + 3) ∧
    ¬ (slotsPtr + nSlots ≤ a ∧ a < slotsPtr + nSlots + r) at hMD_lazy
  have hsd_bkt : restH + ASM_SD_BKT < h2 := by unfold ASM_SD_BKT ASM_SD_SIZE at *; omega
  have hsd_nsl : restH + ASM_SD_NSLOTS < h2 := by unfold ASM_SD_NSLOTS ASM_SD_SIZE at *; omega
  have hsd_sl : restH + ASM_SD_SLOTS < h2 := by unfold ASM_SD_SLOTS ASM_SD_SIZE at *; omega
  have hsd_bun : restH + ASM_SD_BUN < h2 := by unfold ASM_SD_BUN ASM_SD_SIZE at *; omega
  set rawE := h2; set scratch1 := rawE + len; set uniqE_ptr := rawE + 2 * len
  have ha11 : Runs w p ω (.assign 11 (.reg 8)) st5 .normal { st5 with regs := Function.update st5.regs 11 rawE } _ :=
    runs_assign_iff.mpr ⟨rawE, Expr.eval_reg_of_eq hr8_5, rfl, rfl, rfl⟩
  set st6 : State := { st5 with regs := Function.update st5.regs 11 rawE }
  have ha12 : Runs w p ω (.assign 12 (.bin .add (.reg 11) (.reg 9))) st6 .normal
      { st6 with regs := Function.update st6.regs 12 scratch1 } _ :=
    runs_assign_iff.mpr ⟨scratch1,
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [st6])) (Expr.eval_reg_of_eq (by simp [st6, hr9_5'])) (by omega),
      rfl, rfl, rfl⟩
  set st7 : State := { st6 with regs := Function.update st6.regs 12 scratch1 }
  have ha13 : Runs w p ω (.assign 13 (.bin .add (.reg 12) (.reg 9))) st7 .normal
      { st7 with regs := Function.update st7.regs 13 uniqE_ptr } _ :=
    runs_assign_iff.mpr ⟨uniqE_ptr, by
      rw [show uniqE_ptr = scratch1 + len by omega]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp [st7])) (Expr.eval_reg_of_eq (by simp [st7, st6, hr9_5'])) (by omega),
      rfl, rfl, rfl⟩
  set st8 : State := { st7 with regs := Function.update st7.regs 13 uniqE_ptr }
  obtain ⟨st9, cL1, hrunL1, hreg9, hrawE_at, hfr9, hcL1⟩ :=
    newAct_loop1_runs (p := p) (ω := ω) (st0 := st8) (rawE := rawE) hw16 (by simp [st8, st7, st6, hr6_5])
      (by simp [st8, st7, st6, hr9_5', len, cord, r_c]) (by simp [st8, st7, st6]) hEndL
      (fun x hx => by
        have he := heCapG x.1 (Finset.mem_sdiff.mp (Finset.mem_filter.mp ((hCordIff x).mp hx)).1).1
        unfold endKey; split_ifs <;> omega)
      (by omega) (by dsimp only [len, cord, r_c] at hSpace2; omega)
  have hrawE_w : ∀ x ∈ (cord r_c).map Prod.fst, x < 2 ^ w := by
    intro x hx; rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
    have he := (hCordIff y).mp hy
    have := heCapG y.1 (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1; omega
  obtain ⟨bodyMS1, hbMS1, retMS1, stMS1, cMS1, hrunMS1, hpostMS1, hcMS1⟩ :=
    mergeSort_meetsContract (L := (cord r_c).map Prod.fst) hpSort hpSort [rawE, len, scratch1] st9.mem st9.pos ω
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl | rfl <;> omega)
      ⟨rawE, scratch1, by simp [len], hw16, by simp; omega, by simp; omega, Or.inl (by simp; omega), hrawE_at, hrawE_w⟩
  obtain ⟨aMS1, scMS1, sortedE, hargsMS1, _, hpermE, hpairE, hsortedE_at, hfrMS1⟩ := hpostMS1
  simp only [List.cons.injEq, and_true] at hargsMS1; rcases hargsMS1 with ⟨rfl, _, rfl⟩
  have hcallMS1 : Runs w p ω (.call 27 (bSort + sortIdxMergeSort) [.reg 11, .reg 9, .reg 12])
      st9 .normal { stMS1 with regs := Function.update st9.regs 27 retMS1.value } _ :=
    runs_call_iff.mpr ⟨[rawE, len, scratch1], bodyMS1, retMS1, stMS1, cMS1,
      by simp [evalArgs, Expr.eval, hreg9 11 (by decide), hreg9 9 (by decide), hreg9 12 (by decide), st8, st7, st6, hr9_5'],
      hbMS1, hrunMS1, rfl, rfl, rfl⟩
  set st10 : State := { stMS1 with regs := Function.update st9.regs 27 retMS1.value }
  have hsortedE_len : sortedE.length = len := hpermE.length_eq.trans (List.length_map ..)
  have hsortedE_w : ∀ x ∈ sortedE, x < 2 ^ w := fun x hx => hrawE_w x (hpermE.subset hx)
  obtain ⟨bodyDD1, hbDD1, retDD1, stDD1, cDD1, hrunDD1, hpostDD1, hcDD1⟩ :=
    dedup_meetsContract (L := sortedE) hpSort [rawE, len, uniqE_ptr] st10.mem st10.pos ω
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl | rfl <;> omega)
      ⟨rawE, uniqE_ptr, by simp [hsortedE_len], hw16, by omega, by omega, Or.inl (by omega), hpairE, hsortedE_at, hsortedE_w⟩
  obtain ⟨sDD1, dDD1, hargsDD1, hretDD1, huniqE_pw, huniqE_mem, huniqE_at, hfrDD1⟩ := hpostDD1
  simp only [List.cons.injEq, and_true] at hargsDD1; rcases hargsDD1 with ⟨rfl, _, rfl⟩
  set uniqE := sortedDedup sortedE
  have huniqE_toFinset : uniqE.toFinset = coreE := by
    ext e; simp only [List.mem_toFinset, huniqE_mem, hpermE.mem_iff, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (hCordIff x).mp hx
    · intro he; exact ⟨(e, true), (hCordIff (e, true)).mpr he, rfl⟩
  have hmC_eq : uniqE.length = coreE.card := by
    rw [← huniqE_toFinset, List.toFinset_card_of_nodup (huniqE_pw.imp fun h => Nat.ne_of_lt h)]
  have hmC_le : uniqE.length ≤ len := (sortedDedup_length_le_local sortedE).trans (le_of_eq hsortedE_len)
  have hcallDD1 : Runs w p ω (.call 15 (bSort + sortIdxDedup) [.reg 11, .reg 9, .reg 13])
      st10 .normal { stDD1 with regs := Function.update st10.regs 15 uniqE.length }
      (argsSize [.reg 11, .reg 9, .reg 13] + cDD1 + 1) := by
    rw [← hretDD1]
    exact runs_call_iff.mpr ⟨[rawE, len, uniqE_ptr], bodyDD1, retDD1, stDD1, cDD1,
      by simp [evalArgs, Expr.eval, st10, hreg9 11 (by decide), hreg9 9 (by decide), hreg9 13 (by decide), st8, st7, st6, hr9_5'],
      hbDD1, hrunDD1, rfl, rfl, rfl⟩
  set st11 : State := { stDD1 with regs := Function.update st10.regs 15 uniqE.length }
  have hfr11 : ∀ a, a < h2 ∨ uniqE_ptr + uniqE.length ≤ a → st11.mem a = st5.mem a := fun a ha => by
    have h1' : stDD1.mem a = stMS1.mem a := hfrDD1 a (by omega)
    have h2' : stMS1.mem a = st9.mem a := hfrMS1 a (by simp; omega) (by simp; omega)
    have hlen_eq : (outCoreOrder tr ord (tr.cs.RF.root v)).length = len := rfl
    have h3' : st9.mem a = st5.mem a := hfr9 a (by omega)
    exact h1'.trans (h2'.trans h3')
  set rawB := uniqE_ptr + uniqE.length
  set scratch2 := rawB + uniqE.length
  set uniqB_ptr := scratch2 + uniqE.length
  have ha16 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 0) (.const ASM_SD_BKT)))) st11 .normal
      { st11 with regs := Function.update st11.regs 16 bktH } _ :=
    runs_assign_iff.mpr ⟨bktH,
      Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_reg_of_eq (by simp [st11, st10, hreg9 0 (by decide), st8, st7, st6, hr0_5]))
        (Expr.eval_const (by unfold ASM_SD_BKT; omega)) (by omega))
        ((hfr11 _ (Or.inl hsd_bkt)).trans ((hrec5 ASM_SD_BKT (by decide)).trans hRecBkt)), rfl, rfl, rfl⟩
  set st12 : State := { st11 with regs := Function.update st11.regs 16 bktH }
  have ha17 : Runs w p ω (.assign 17 (.bin .add (.reg 13) (.reg 15))) st12 .normal
      { st12 with regs := Function.update st12.regs 17 rawB } _ :=
    runs_assign_iff.mpr ⟨rawB, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st12, st11, st10, hreg9 13 (by decide), st8]))
      (Expr.eval_reg_of_eq (by simp [st12, st11])) (by omega), rfl, rfl, rfl⟩
  set st13 : State := { st12 with regs := Function.update st12.regs 17 rawB }
  have ha18 : Runs w p ω (.assign 18 (.bin .add (.reg 17) (.reg 15))) st13 .normal
      { st13 with regs := Function.update st13.regs 18 scratch2 } _ :=
    runs_assign_iff.mpr ⟨scratch2, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st13]))
      (Expr.eval_reg_of_eq (by simp [st13, st12, st11])) (by omega), rfl, rfl, rfl⟩
  set st14 : State := { st13 with regs := Function.update st13.regs 18 scratch2 }
  have ha19 : Runs w p ω (.assign 19 (.bin .add (.reg 18) (.reg 15))) st14 .normal
      { st14 with regs := Function.update st14.regs 19 uniqB_ptr } _ :=
    runs_assign_iff.mpr ⟨uniqB_ptr, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st14]))
      (Expr.eval_reg_of_eq (by simp [st14, st13, st12, st11])) (by omega), rfl, rfl, rfl⟩
  set st15 : State := { st14 with regs := Function.update st14.regs 19 uniqB_ptr }
  have hBkt15 : ∀ e ∈ uniqE, bktH + e < 2 ^ w ∧ st15.mem (bktH + e) = bucketCode (tr.origBucket e) ∧
      bucketCode (tr.origBucket e) < 2 ^ w := by
    intro e he
    have heC : e ∈ coreE := huniqE_toFinset ▸ List.mem_toFinset.mpr he
    have hbk := hbkt_ok e (hCoreInG₀ e (Finset.mem_filter.mp heC).1 (Finset.mem_filter.mp heC).2)
    exact ⟨by omega, (hfr11 _ (Or.inl (by omega))).trans hbk.2.1, by rw [← hbk.2.1]; exact hbk.2.2⟩
  obtain ⟨st16, cL2, hrunL2, hreg16, hrawB_at, hfr16, hcL2⟩ :=
    newAct_loop2_runs (p := p) (ω := ω) (st0 := st15) (bktH := bktH) (rawB := rawB) hw16
      (by simp [st15, st14, st13, st12, st11, st10, hreg9 13 (by decide), st8])
      (by simp [st15, st14, st13, st12, st11])
      (by simp [st15, st14, st13, st12]) (by simp [st15, st14, st13])
      huniqE_at (fun e he => ⟨(hBkt15 e he).1, (hBkt15 e he).2.1⟩) (by omega)
      (fun e he => Or.inl (by have heC : e ∈ coreE := huniqE_toFinset ▸ List.mem_toFinset.mpr he; have := (hbkt_ok e (hCoreInG₀ e (Finset.mem_filter.mp heC).1 (Finset.mem_filter.mp heC).2)).1; omega))
      (by omega)
  have hrawB_w : ∀ x ∈ uniqE.map (fun e => bucketCode (tr.origBucket e)), x < 2 ^ w := by
    intro x hx; rcases List.mem_map.mp hx with ⟨e, he, rfl⟩; exact (hBkt15 e he).2.2
  obtain ⟨bodyMS2, hbMS2, retMS2, stMS2, cMS2, hrunMS2, hpostMS2, hcMS2⟩ :=
    mergeSort_meetsContract (L := uniqE.map fun e => bucketCode (tr.origBucket e)) hpSort hpSort
      [rawB, uniqE.length, scratch2] st16.mem st16.pos ω
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl | rfl <;> omega)
      ⟨rawB, scratch2, by simp, hw16, by simp; omega, by simp; omega, Or.inl (by simp; omega), hrawB_at, hrawB_w⟩
  obtain ⟨aMS2, scMS2, sortedB, hargsMS2, _, hpermB, hpairB, hsortedB_at, hfrMS2⟩ := hpostMS2
  simp only [List.cons.injEq, and_true] at hargsMS2; rcases hargsMS2 with ⟨rfl, _, rfl⟩
  have hcallMS2 : Runs w p ω (.call 27 (bSort + sortIdxMergeSort) [.reg 17, .reg 15, .reg 18])
      st16 .normal { stMS2 with regs := Function.update st16.regs 27 retMS2.value } _ :=
    runs_call_iff.mpr ⟨[rawB, uniqE.length, scratch2], bodyMS2, retMS2, stMS2, cMS2,
      by simp [evalArgs, Expr.eval, hreg16 17 (by decide) (by decide), hreg16 15 (by decide) (by decide),
        hreg16 18 (by decide) (by decide), st15, st14, st13, st12, st11],
      hbMS2, hrunMS2, rfl, rfl, rfl⟩
  set st17 : State := { stMS2 with regs := Function.update st16.regs 27 retMS2.value }
  have hsortedB_len : sortedB.length = uniqE.length := hpermB.length_eq.trans (List.length_map ..)
  have hsortedB_w : ∀ x ∈ sortedB, x < 2 ^ w := fun x hx => hrawB_w x (hpermB.subset hx)
  obtain ⟨bodyDD2, hbDD2, retDD2, stDD2, cDD2, hrunDD2, hpostDD2, hcDD2⟩ :=
    dedup_meetsContract (L := sortedB) hpSort [rawB, uniqE.length, uniqB_ptr] st17.mem st17.pos ω
      (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl | rfl <;> omega)
      ⟨rawB, uniqB_ptr, by simp [hsortedB_len], hw16, by omega, by omega, Or.inl (by omega), hpairB, hsortedB_at, hsortedB_w⟩
  obtain ⟨sDD2, dDD2, hargsDD2, hretDD2, huniqB_pw, huniqB_mem, huniqB_at, hfrDD2⟩ := hpostDD2
  simp only [List.cons.injEq, and_true] at hargsDD2; rcases hargsDD2 with ⟨rfl, _, rfl⟩
  set uniqB := sortedDedup sortedB
  have huniqB_iff : ∀ b, b ∈ tr.activeBuckets comps[c] ↔ bucketCode b ∈ uniqB := by
    intro b
    rw [hBktsEq, Finset.mem_image, huniqB_mem, hpermB.mem_iff, List.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩; exact ⟨e, List.mem_toFinset.mp (huniqE_toFinset.symm ▸ he), rfl⟩
    · rintro ⟨e, he, hbc⟩; exact ⟨e, by change e ∈ coreE; rw [← huniqE_toFinset]; exact List.mem_toFinset.mpr he, bucketCode_injective hbc⟩
  have hr_eq : uniqB.length = r := by
    have hndB : uniqB.Nodup := huniqB_pw.imp fun h => Nat.ne_of_lt h
    have himg : uniqB.toFinset = (tr.activeBuckets comps[c]).image bucketCode := by
      ext k; simp only [List.mem_toFinset, Finset.mem_image]
      constructor
      · intro hk; have hk' : k ∈ uniqB := hk
        rw [huniqB_mem, hpermB.mem_iff, List.mem_map] at hk'
        rcases hk' with ⟨e, he, rfl⟩; exact ⟨tr.origBucket e, (huniqB_iff _).mpr hk, rfl⟩
      · rintro ⟨b, hb, rfl⟩; exact (huniqB_iff b).mp hb
    rw [← List.toFinset_card_of_nodup hndB, himg, Finset.card_image_of_injective _ bucketCode_injective]
  have hr_le : uniqB.length ≤ uniqE.length := (sortedDedup_length_le_local sortedB).trans (le_of_eq hsortedB_len)
  have huniqB_w : ∀ x ∈ uniqB, x < 2 ^ w := fun x hx => hsortedB_w x ((huniqB_mem x).mp hx)
  have hcallDD2 : Runs w p ω (.call 20 (bSort + sortIdxDedup) [.reg 17, .reg 15, .reg 19])
      st17 .normal { stDD2 with regs := Function.update st17.regs 20 uniqB.length }
      (argsSize [.reg 17, .reg 15, .reg 19] + cDD2 + 1) := by
    rw [← hretDD2]
    exact runs_call_iff.mpr ⟨[rawB, uniqE.length, uniqB_ptr], bodyDD2, retDD2, stDD2, cDD2,
      by simp [evalArgs, Expr.eval, st17, hreg16 17 (by decide) (by decide), hreg16 15 (by decide) (by decide),
        hreg16 19 (by decide) (by decide), st15, st14, st13, st12, st11],
      hbDD2, hrunDD2, rfl, rfl, rfl⟩
  set st18 : State := { stDD2 with regs := Function.update st17.regs 20 uniqB.length }
  have hfr18 : ∀ a, a < rawB ∨ uniqB_ptr + uniqB.length ≤ a → st18.mem a = st11.mem a := fun a ha =>
    (hfrDD2 a (by omega)).trans ((hfrMS2 a (by simp; omega) (by simp; omega)).trans (hfr16 a (by omega)))
  set cnt := uniqB_ptr + uniqB.length; set assigns := cnt + uniqB.length
  have ha21 : Runs w p ω (.assign 21 (.bin .add (.reg 19) (.reg 20))) st18 .normal
      { st18 with regs := Function.update st18.regs 21 cnt } _ :=
    runs_assign_iff.mpr ⟨cnt, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st18, st17, hreg16 19 (by decide) (by decide), st15]))
      (Expr.eval_reg_of_eq (by simp [st18])) (by omega), rfl, rfl, rfl⟩
  set st19 : State := { st18 with regs := Function.update st18.regs 21 cnt }
  have ha22 : Runs w p ω (.assign 22 (.bin .add (.reg 21) (.reg 20))) st19 .normal
      { st19 with regs := Function.update st19.regs 22 assigns } _ :=
    runs_assign_iff.mpr ⟨assigns, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st19]))
      (Expr.eval_reg_of_eq (by simp [st19, st18])) (by omega), rfl, rfl, rfl⟩
  set st20 : State := { st19 with regs := Function.update st19.regs 22 assigns }
  have ha23 : Runs w p ω (.assign 23 (.load (.bin .add (.reg 0) (.const ASM_SD_NSLOTS)))) st20 .normal
      { st20 with regs := Function.update st20.regs 23 nSlots } _ :=
    runs_assign_iff.mpr ⟨nSlots, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st20, st19, st18, st17, hreg16 0 (by decide) (by decide),
        st15, st14, st13, st12, st11, st10, hreg9 0 (by decide), st8, st7, st6, hr0_5]))
      (Expr.eval_const (by unfold ASM_SD_NSLOTS; omega)) (by omega))
      ((hfr18 _ (Or.inl (by omega))).trans ((hfr11 _ (Or.inl hsd_nsl)).trans
        ((hrec5 ASM_SD_NSLOTS (by decide)).trans hRecNSlots))), rfl, rfl, rfl⟩
  set st21 : State := { st20 with regs := Function.update st20.regs 23 nSlots }
  have huniqE_at21 : ListAt st21.mem uniqE_ptr uniqE := fun i hi => by
    change st18.mem (uniqE_ptr + i) = uniqE[i]'hi; rw [hfr18 _ (Or.inl (by omega))]; exact huniqE_at i hi
  have hBkt21 : ∀ e ∈ uniqE, bktH + e < 2 ^ w ∧ st21.mem (bktH + e) = bucketCode (tr.origBucket e) ∧
      bucketCode (tr.origBucket e) ∈ uniqB := fun e he => by
    have h1 := hBkt15 e he; have heC : e ∈ coreE := huniqE_toFinset ▸ List.mem_toFinset.mpr he
    have hlt := (hbkt_ok e (hCoreInG₀ e (Finset.mem_filter.mp heC).1 (Finset.mem_filter.mp heC).2)).1
    exact ⟨h1.1, (hfr18 _ (Or.inl (by omega))).trans h1.2.1,
      (huniqB_mem _).mpr (hpermB.mem_iff.mpr (List.mem_map.mpr ⟨e, he, rfl⟩))⟩
  have hCnt0_21 : ∀ bi < uniqB.length, st21.mem (cnt + bi) = 0 := fun bi hbi => by
    change st18.mem (cnt + bi) = 0
    rw [hfr18 _ (Or.inr (by omega)), hfr11 _ (Or.inr (by omega))]; exact hzL _ (by omega)
  obtain ⟨st22, cL3, hrunL3, hreg22, hcnt22, hass22, hfr22, hcL3⟩ :=
    newAct_loop3_runs (ω := ω) (st0 := st21) (bktH := bktH) (cnt := cnt) (assigns := assigns) (nSlots := nSlots) hpSort hw16
      (by simp [st21, st20, st19, st18, st17, hreg16 13 (by decide) (by decide), st15, st14, st13, st12, st11, st10, hreg9 13 (by decide), st8])
      (by simp [st21, st20, st19, st18, st17, hreg16 15 (by decide) (by decide), st15, st14, st13, st12, st11])
      (by simp [st21, st20, st19, st18, st17, hreg16 16 (by decide) (by decide), st15, st14, st13, st12])
      (by simp [st21, st20, st19, st18, st17, hreg16 19 (by decide) (by decide), st15])
      (by simp [st21, st20, st19, st18]) (by simp [st21, st20, st19]) (by simp [st21, st20]) (by simp [st21])
      huniqE_at21 huniqB_at huniqB_pw huniqB_w hBkt21 hCnt0_21
      ⟨by omega, by omega, by omega,
       fun e he => Or.inl (by
         have heC : e ∈ coreE := huniqE_toFinset ▸ List.mem_toFinset.mpr he
         have := (hbkt_ok e (hCoreInG₀ e (Finset.mem_filter.mp heC).1 (Finset.mem_filter.mp heC).2)).1; omega),
       by omega, by omega⟩
  set specs := assigns + 2 * uniqE.length; set csl := specs + 2 * uniqB.length; set rPtr := csl + 2 * uniqB.length
  have ha24 : Runs w p ω (.assign 24 (.bin .add (.reg 22) (.bin .mul (.const 2) (.reg 15)))) st22 .normal
      { st22 with regs := Function.update st22.regs 24 specs } _ :=
    runs_assign_iff.mpr ⟨specs, Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [hreg22 22 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20]))
      (Expr.eval_mul (Expr.eval_const h2w)
        (Expr.eval_reg_of_eq (by simp [hreg22 15 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18, st17, hreg16 15 (by decide) (by decide), st15, st14, st13, st12, st11]))
        (by omega)) (by omega), rfl, rfl, rfl⟩
  set st23 : State := { st22 with regs := Function.update st22.regs 24 specs }
  have ha25 : Runs w p ω (.assign 25 (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 20)))) st23 .normal
      { st23 with regs := Function.update st23.regs 25 csl } _ :=
    runs_assign_iff.mpr ⟨csl, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st23]))
      (Expr.eval_mul (Expr.eval_const h2w)
        (Expr.eval_reg_of_eq (by simp [st23, hreg22 20 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18]))
        (by omega)) (by omega), rfl, rfl, rfl⟩
  set st24 : State := { st23 with regs := Function.update st23.regs 25 csl }
  have ha26 : Runs w p ω (.assign 26 (.bin .add (.reg 25) (.bin .mul (.const 2) (.reg 20)))) st24 .normal
      { st24 with regs := Function.update st24.regs 26 rPtr } _ :=
    runs_assign_iff.mpr ⟨rPtr, Expr.eval_add (Expr.eval_reg_of_eq (by simp [st24]))
      (Expr.eval_mul (Expr.eval_const h2w)
        (Expr.eval_reg_of_eq (by simp [st24, st23, hreg22 20 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18]))
        (by omega)) (by omega), rfl, rfl, rfl⟩
  set st25 : State := { st24 with regs := Function.update st24.regs 26 rPtr }
  have ha28 : Runs w p ω (.assign 28 (.load (.bin .add (.reg 0) (.const ASM_SD_SLOTS)))) st25 .normal
      { st25 with regs := Function.update st25.regs 28 slotsPtr } _ :=
    runs_assign_iff.mpr ⟨slotsPtr, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [st25, st24, st23, hreg22 0 (by decide) (by decide) (by decide) (by decide) (by decide),
        st21, st20, st19, st18, st17, hreg16 0 (by decide) (by decide), st15, st14, st13, st12, st11, st10, hreg9 0 (by decide),
        st8, st7, st6, hr0_5]))
      (Expr.eval_const (by unfold ASM_SD_SLOTS; omega)) (by omega))
      ((hfr22 _ (Or.inl (by omega))).trans ((hfr18 _ (Or.inl (by omega))).trans
        ((hfr11 _ (Or.inl hsd_sl)).trans ((hrec5 ASM_SD_SLOTS (by decide)).trans hRecSlots)))), rfl, rfl, rfl⟩
  set st26 : State := { st25 with regs := Function.update st25.regs 28 slotsPtr }
  let cntFn : ℕ → ℕ := fun bi => (uniqE.filter fun e => decide (uniqB.idxOf (bucketCode (tr.origBucket e)) = bi)).length
  have hcnt_le_mC : ∀ bi, cntFn bi ≤ uniqE.length := fun bi => List.length_filter_le _ _
  have hmC_le_eCap : coreE.card ≤ eCap :=
    (Finset.card_le_card (show coreE ⊆ Finset.range eCap from fun e he =>
      Finset.mem_range.mpr (heCapG e (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1))).trans (by simp)
  obtain ⟨st27, cL4, hrunL4, hreg27, hspecs27, hcsl27, hslots27, hfr27, hcL4⟩ :=
    newAct_loop4_runs (p := p) (ω := ω) (st0 := st26) (uniqB_ptr := uniqB_ptr) (cnt := cnt) (nSlots := nSlots)
      (specs := specs) (csl := csl) (slotsPtr := slotsPtr) (cntFn := cntFn) hw16
      (by simp [st26, st25, st24, st23, hreg22 19 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18, st17, hreg16 19 (by decide) (by decide), st15])
      (by simp [st26, st25, st24, st23, hreg22 20 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18])
      (by simp [st26, st25, st24, st23, hreg22 21 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19])
      (by simp [st26, st25, st24, st23, hreg22 23 (by decide) (by decide) (by decide) (by decide) (by decide), st21])
      (by simp [st26, st25, st24, st23]) (by simp [st26, st25, st24]) (by simp [st26])
      (fun i hi => by change st22.mem (uniqB_ptr + i) = uniqB[i]'hi; rw [hfr22 _ (Or.inl (by omega))]; exact huniqB_at i hi)
      (fun bi hbi => ⟨hcnt22 bi hbi, by have := hcnt_le_mC bi; omega⟩)
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  set mS1 := Function.update st27.mem (ctH + 3 * c + 1) csl
  set mS2 := Function.update mS1 (ctH + 3 * c + 2) uniqB.length
  set mS3 := Function.update mS2 (restH + ASM_SD_NSLOTS) (nSlots + uniqB.length)
  set mS4 := Function.update mS3 lazySlotPtr uniqE_ptr
  set mS5 := Function.update mS4 (lazySlotPtr + 1) uniqE.length
  set mS6 := Function.update mS5 rPtr r_c
  have hfr27_lt : ∀ a < h2, ¬ (slotsPtr + nSlots ≤ a ∧ a < slotsPtr + nSlots + uniqB.length) →
      st27.mem a = st5.mem a := fun a ha hsl =>
    (hfr27 a (by omega) hsl).trans ((hfr22 a (Or.inl (by omega))).trans
      ((hfr18 a (Or.inl (by omega))).trans (hfr11 a (Or.inl ha))))
  have hmS6_of : ∀ a, a ≠ ctH + 3 * c + 1 → a ≠ ctH + 3 * c + 2 → a ≠ restH + ASM_SD_NSLOTS →
      a ≠ lazySlotPtr → a ≠ lazySlotPtr + 1 → a ≠ rPtr → mS6 a = st27.mem a :=
    fun a h1' h2' h3' h4' h5' h6' => by
      simp [mS6, mS5, mS4, mS3, mS2, mS1, Function.update_of_ne h6', Function.update_of_ne h5',
        Function.update_of_ne h4', Function.update_of_ne h3', Function.update_of_ne h2', Function.update_of_ne h1']
  have hloB : restH ≤ restH + ASM_SD_BUN := by unfold ASM_SD_BUN; omega
  have hhiB : restH + ASM_SD_BUN < restH + ASM_SD_SIZE := by unfold ASM_SD_BUN ASM_SD_SIZE; omega
  have hloN : restH ≤ restH + ASM_SD_NSLOTS := by unfold ASM_SD_NSLOTS; omega
  have hhiN : restH + ASM_SD_NSLOTS < restH + ASM_SD_SIZE := by unfold ASM_SD_NSLOTS ASM_SD_SIZE; omega
  have hbun_mS6 : mS6 (restH + ASM_SD_BUN) = bunH := by
    rw [hmS6_of _ (fun h => (hMD_ct _ (by omega) (by omega)).1 ⟨h ▸ hloB, h ▸ hhiB⟩)
      (fun h => (hMD_ct _ (by omega) (by omega)).1 ⟨h ▸ hloB, h ▸ hhiB⟩)
      (by unfold ASM_SD_BUN ASM_SD_NSLOTS; omega)
      (fun h => (hMD_lazy _ (by omega) (by omega)).1 ⟨h ▸ hloB, h ▸ hhiB⟩)
      (fun h => (hMD_lazy _ (by omega) (by omega)).1 ⟨h ▸ hloB, h ▸ hhiB⟩) (by omega),
      hfr27_lt _ hsd_bun (fun hs => (hMD_sl _ hs.1 (by omega)).1 ⟨hloB, hhiB⟩)]
    exact (hrec5 ASM_SD_BUN (by decide)).trans hRecBun
  have hr0_27 : st27.regs 0 = restH := by simp [hreg27 0 (by decide) (by decide) (by decide), st26, st25, st24, st23, hreg22 0 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18, st17, hreg16 0 (by decide) (by decide), st15, st14, st13, st12, st11, st10, hreg9 0 (by decide), st8, st7, st6, hr0_5]
  have hr1_27 : st27.regs 1 = tourH := by simp [hreg27 1 (by decide) (by decide) (by decide), st26, st25, st24, st23, hreg22 1 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18, st17, hreg16 1 (by decide) (by decide), st15, st14, st13, st12, st11, st10, hreg9 1 (by decide), st8, st7, st6, hr1_5]
  have hr2_27 : st27.regs 2 = c := by simp [hreg27 2 (by decide) (by decide) (by decide), st26, st25, st24, st23, hreg22 2 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18, st17, hreg16 2 (by decide) (by decide), st15, st14, st13, st12, st11, st10, hreg9 2 (by decide), st8, st7, st6, hr2_5]
  have hr4_27 : st27.regs 4 = lazySlotPtr := by simp [hreg27 4 (by decide) (by decide) (by decide), st26, st25, st24, st23, hreg22 4 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18, st17, hreg16 4 (by decide) (by decide), st15, st14, st13, st12, st11, st10, hreg9 4 (by decide), st8, st7, st6, hr4_5]
  have hr7_27 : st27.regs 7 = r_c := by simp [hreg27 7 (by decide) (by decide) (by decide), st26, st25, st24, st23, hreg22 7 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18, st17, hreg16 7 (by decide) (by decide), st15, st14, st13, st12, st11, st10, hreg9 7 (by decide), st8, st7, st6, hr7_5, r_c]
  have hr10_27 : st27.regs 10 = ctH := by simp [hreg27 10 (by decide) (by decide) (by decide), st26, st25, st24, st23, hreg22 10 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18, st17, hreg16 10 (by decide) (by decide), st15, st14, st13, st12, st11, st10, hreg9 10 (by decide), st8, st7, st6, hr10_5]
  have hr13_27 : st27.regs 13 = uniqE_ptr := by simp [hreg27 13 (by decide) (by decide) (by decide), st26, st25, st24, st23, hreg22 13 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18, st17, hreg16 13 (by decide) (by decide), st15, st14, st13, st12, st11, st10, hreg9 13 (by decide), st8]
  have hr15_27 : st27.regs 15 = uniqE.length := by simp [hreg27 15 (by decide) (by decide) (by decide), st26, st25, st24, st23, hreg22 15 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18, st17, hreg16 15 (by decide) (by decide), st15, st14, st13, st12, st11]
  have hr20_27 : st27.regs 20 = uniqB.length := by simp [hreg27 20 (by decide) (by decide) (by decide), st26, st25, st24, st23, hreg22 20 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20, st19, st18]
  have hr22_27 : st27.regs 22 = assigns := by simp [hreg27 22 (by decide) (by decide) (by decide), st26, st25, st24, st23, hreg22 22 (by decide) (by decide) (by decide) (by decide) (by decide), st21, st20]
  have hr23_27 : st27.regs 23 = nSlots := by simp [hreg27 23 (by decide) (by decide) (by decide), st26, st25, st24, st23, hreg22 23 (by decide) (by decide) (by decide) (by decide) (by decide), st21]
  have hr24_27 : st27.regs 24 = specs := by simp [hreg27 24 (by decide) (by decide) (by decide), st26, st25, st24, st23]
  have hr25_27 : st27.regs 25 = csl := by simp [hreg27 25 (by decide) (by decide) (by decide), st26, st25, st24]
  have hr26_27 : st27.regs 26 = rPtr := by simp [hreg27 26 (by decide) (by decide) (by decide), st26, st25]
  obtain ⟨cSt, hrunSt, hcSt⟩ : ∃ cS, Runs w p ω
      (.store (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 2))) (.const 1)) (.reg 25) ;;
       .store (.bin .add (.bin .add (.reg 10) (.bin .mul (.const 3) (.reg 2))) (.const 2)) (.reg 20) ;;
       .store (.bin .add (.reg 0) (.const ASM_SD_NSLOTS)) (.bin .add (.reg 23) (.reg 20)) ;;
       .store (.reg 4) (.reg 13) ;;
       .store (.bin .add (.reg 4) (.const 1)) (.reg 15) ;;
       .store (.reg 26) (.reg 7) ;;
       .assign 29 (.load (.bin .add (.reg 0) (.const ASM_SD_BUN))))
      st27 .normal ⟨mS6, Function.update st27.regs 29 bunH, st27.pos⟩ cS ∧ 0 + cS ≤ 75 := by
    refine rStoreLe (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr10_27)
      (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq hr2_27) (by omega)) (by omega))
      (Expr.eval_const h1w) (by omega)) (Expr.eval_reg_of_eq hr25_27) ?_
    refine rStoreLe (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr10_27)
      (Expr.eval_mul (Expr.eval_const h3w) (Expr.eval_reg_of_eq hr2_27) (by omega)) (by omega))
      (Expr.eval_const h2w) (by omega)) (Expr.eval_reg_of_eq hr20_27) ?_
    refine rStoreLe (Expr.eval_add (Expr.eval_reg_of_eq hr0_27)
      (Expr.eval_const (by unfold ASM_SD_NSLOTS; omega)) (by omega))
      (Expr.eval_add (Expr.eval_reg_of_eq hr23_27) (Expr.eval_reg_of_eq hr20_27) (by omega)) ?_
    refine rStoreLe (Expr.eval_reg_of_eq hr4_27) (Expr.eval_reg_of_eq hr13_27) ?_
    refine rStoreLe (Expr.eval_add (Expr.eval_reg_of_eq hr4_27) (Expr.eval_const h1w) (by omega))
      (Expr.eval_reg_of_eq hr15_27) ?_
    refine rStoreLe (Expr.eval_reg_of_eq hr26_27) (Expr.eval_reg_of_eq hr7_27) ?_
    exact ⟨_, runs_assign_iff.mpr ⟨bunH, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hr0_27)
      (Expr.eval_const (by unfold ASM_SD_BUN; omega)) (by omega))
      hbun_mS6, rfl, rfl, rfl⟩, by simp only [Expr.size]; omega⟩
  set st28 : State := ⟨mS6, Function.update st27.regs 29 bunH, st27.pos⟩
  have hbr_mid2 := runs_seq_iff.mpr (Or.inr ⟨st23, _, _, ha24, runs_seq_iff.mpr (Or.inr ⟨st24, _, _, ha25, runs_seq_iff.mpr (Or.inr ⟨st25, _, _, ha26, runs_seq_iff.mpr (Or.inr ⟨st26, _, _, ha28, runs_seq_iff.mpr (Or.inr ⟨st27, _, _, hrunL4, hrunSt, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hbr_mid1 := runs_seq_iff.mpr (Or.inr ⟨st16, _, _, hrunL2, runs_seq_iff.mpr (Or.inr ⟨st17, _, _, hcallMS2, runs_seq_iff.mpr (Or.inr ⟨st18, _, _, hcallDD2, runs_seq_iff.mpr (Or.inr ⟨st19, _, _, ha21, runs_seq_iff.mpr (Or.inr ⟨st20, _, _, ha22, runs_seq_iff.mpr (Or.inr ⟨st21, _, _, ha23, runs_seq_iff.mpr (Or.inr ⟨st22, _, _, hrunL3, hbr_mid2, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hrunP := runs_seq_iff.mpr (Or.inr ⟨st6, _, _, ha11, runs_seq_iff.mpr (Or.inr ⟨st7, _, _, ha12, runs_seq_iff.mpr (Or.inr ⟨st8, _, _, ha13, runs_seq_iff.mpr (Or.inr ⟨st9, _, _, hrunL1, runs_seq_iff.mpr (Or.inr ⟨st10, _, _, hcallMS1, runs_seq_iff.mpr (Or.inr ⟨st11, _, _, hcallDD1, runs_seq_iff.mpr (Or.inr ⟨st12, _, _, ha16, runs_seq_iff.mpr (Or.inr ⟨st13, _, _, ha17, runs_seq_iff.mpr (Or.inr ⟨st14, _, _, ha18, runs_seq_iff.mpr (Or.inr ⟨st15, _, _, ha19, hbr_mid1, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hmS6_ge : ∀ a, h2 ≤ a → a ≠ rPtr → mS6 a = st27.mem a := fun a ha hne =>
    hmS6_of a (by omega) (by omega) (by omega) (by omega) (by omega) hne
  have hfr27_mid : ∀ a, h2 ≤ a → a < specs → st27.mem a = st22.mem a := fun a ha hlt =>
    hfr27 a (by omega) (by omega)
  refine ⟨st28, _, uniqE, uniqB, uniqE_ptr, assigns, specs, csl, rPtr, hrunP,
    huniqE_pw, huniqE_toFinset, huniqB_pw, hr_eq, huniqB_iff, huniqB_w,
    by omega, by omega, rfl, rfl, rfl, by omega,
    by simp [st28, hr1_27], by simp [st28, hr15_27], by simp [st28, hr20_27],
    by simp [st28, hr22_27], by simp [st28, hr24_27], by simp [st28, hr26_27], by simp [st28],
    ?_, ?_, by simp [st28, mS6], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · trans bundleReadPairs st27.mem specs uniqB.length
    · apply List.ext_getElem (by simp [bundleReadPairs])
      intro i hi1 _; have hi : i < uniqB.length := by simpa [bundleReadPairs] using hi1
      simp only [bundleReadPairs, List.getElem_map, List.getElem_range]
      exact Prod.ext (hmS6_ge _ (by omega) (by omega)) (hmS6_ge _ (by omega) (by omega))
    · exact hspecs27
  · trans bundleReadPairs st22.mem assigns uniqE.length
    · apply List.ext_getElem (by simp [bundleReadPairs])
      intro i hi1 _; have hi : i < uniqE.length := by simpa [bundleReadPairs] using hi1
      simp only [bundleReadPairs, List.getElem_map, List.getElem_range]
      exact Prod.ext ((hmS6_ge _ (by omega) (by omega)).trans (hfr27_mid _ (by omega) (by omega)))
        ((hmS6_ge _ (by omega) (by omega)).trans (hfr27_mid _ (by omega) (by omega)))
    · exact hass22
  · intro i hi
    change mS6 (uniqE_ptr + i) = uniqE[i]'hi
    rw [hmS6_ge _ (by omega) (by omega), hfr27_mid _ (by omega) (by omega),
      hfr22 _ (Or.inl (by omega)), hfr18 _ (Or.inl (by omega))]
    exact huniqE_at i hi
  · simp [st28, mS6, mS5, mS4, mS3, Function.update_of_ne (by omega : restH + ASM_SD_NSLOTS ≠ rPtr),
      Function.update_of_ne (fun heq => (hMD_lazy (lazySlotPtr + 1) (by omega) (by omega)).1 ⟨heq ▸ hloN, heq ▸ hhiN⟩ : restH + ASM_SD_NSLOTS ≠ lazySlotPtr + 1),
      Function.update_of_ne (fun heq => (hMD_lazy lazySlotPtr (by omega) (by omega)).1 ⟨heq ▸ hloN, heq ▸ hhiN⟩ : restH + ASM_SD_NSLOTS ≠ lazySlotPtr), hr_eq]
  · simp [st28, mS6, mS5, mS4, mS3, mS2, mS1, Function.update_of_ne (by omega : ctH + 3 * c + 1 ≠ rPtr),
      Function.update_of_ne (fun heq => (hMD_lazy (lazySlotPtr + 1) (by omega) (by omega)).2.2.1 ⟨by omega, by omega⟩ : ctH + 3 * c + 1 ≠ lazySlotPtr + 1),
      Function.update_of_ne (fun heq => (hMD_lazy lazySlotPtr (by omega) (by omega)).2.2.1 ⟨by omega, by omega⟩ : ctH + 3 * c + 1 ≠ lazySlotPtr),
      Function.update_of_ne (fun heq => (hMD_ct (ctH + 3 * c + 1) (by omega) (by omega)).1 ⟨heq.symm ▸ hloN, heq.symm ▸ hhiN⟩ : ctH + 3 * c + 1 ≠ restH + ASM_SD_NSLOTS)]
  · simp [st28, mS6, mS5, mS4, mS3, mS2, Function.update_of_ne (by omega : ctH + 3 * c + 2 ≠ rPtr),
      Function.update_of_ne (fun heq => (hMD_lazy (lazySlotPtr + 1) (by omega) (by omega)).2.2.1 ⟨by omega, by omega⟩ : ctH + 3 * c + 2 ≠ lazySlotPtr + 1),
      Function.update_of_ne (fun heq => (hMD_lazy lazySlotPtr (by omega) (by omega)).2.2.1 ⟨by omega, by omega⟩ : ctH + 3 * c + 2 ≠ lazySlotPtr),
      Function.update_of_ne (fun heq => (hMD_ct (ctH + 3 * c + 2) (by omega) (by omega)).1 ⟨heq.symm ▸ hloN, heq.symm ▸ hhiN⟩ : ctH + 3 * c + 2 ≠ restH + ASM_SD_NSLOTS), hr_eq]
  · intro bi hbi
    exact ⟨(hmS6_ge _ (by omega) (by omega)).trans (hcsl27 bi hbi).1,
      (hmS6_ge _ (by omega) (by omega)).trans (hcsl27 bi hbi).2⟩
  · intro bi hbi; have hbi' : bi < uniqB.length := by omega
    exact (hmS6_of (slotsPtr + (nSlots + bi))
      (fun heq => (hMD_sl (slotsPtr + (nSlots + bi)) (by omega) (by omega)).2.2 ⟨by omega, by omega⟩)
      (fun heq => (hMD_sl (slotsPtr + (nSlots + bi)) (by omega) (by omega)).2.2 ⟨by omega, by omega⟩)
      (fun heq => (hMD_sl (slotsPtr + (nSlots + bi)) (by omega) (by omega)).1 ⟨heq.symm ▸ hloN, heq.symm ▸ hhiN⟩)
      (fun heq => (hMD_lazy lazySlotPtr (by omega) (by omega)).2.2.2 ⟨by omega, by omega⟩)
      (fun heq => (hMD_lazy (lazySlotPtr + 1) (by omega) (by omega)).2.2.2 ⟨by omega, by omega⟩) (by omega)).trans (hslots27 bi hbi')
  · simp [st28, mS6, mS5, mS4, Function.update_of_ne (by omega : lazySlotPtr ≠ rPtr)]
  · simp [st28, mS6, mS5, Function.update_of_ne (by omega : lazySlotPtr + 1 ≠ rPtr)]
  · intro a ha; change mS6 a = 0
    rw [hmS6_ge a (by omega) (by omega), hfr27 a (by omega) (by omega), hfr22 a (Or.inr (by omega)),
      hfr18 a (Or.inr (by omega)), hfr11 a (Or.inr (by omega))]
    exact hzL a (by omega)
  · intro a ha hns hct hsl hlz; change mS6 a = st5.mem a
    rw [hmS6_of a (by omega) (by omega) hns (by omega) (by omega) (by omega)]
    exact hfr27_lt a ha (by omega)
  · dsimp only [newActPrepCost, mergeSortContract, dedupContract, argsSize, Expr.size] at hcL1 hcMS1 hcDD1 hcL2 hcMS2 hcDD2 hcL3 hcL4 hcSt ⊢
    simp only [List.length_map, hsortedE_len, hsortedB_len] at hcMS1 hcDD1 hcMS2 hcDD2 ⊢
    change cL1 ≤ 30 * len + 20 at hcL1
    change cMS1 ≤ 200 * len * (Nat.log 2 (len + 1) + 1) + 50 at hcMS1
    rw [hmC_eq] at hcL2 hcMS2 hcDD2 hcL3
    rw [hr_eq] at hcL3 hcL4
    linarith [hcL1, hcMS1, hcDD1, hcL2, hcMS2, hcDD2, hcL3, hcL4, hcSt]

end

end MinCostFlow.SparseCore.Program
