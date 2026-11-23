module

public import MinCostFlow.Expander.PruningAbsorbCurProg

import Mathlib.Tactic.Ring

/-!
# Push-Active-W and Push-Flow-Prefix Triples
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

def pushActWStmt : Stmt :=
  seqStmts
    [ .assign prTmp2 (.load (.bin .add (.reg prInAct) (.reg prW)))
    , .cond (.bin .eq (.reg prTmp2) (.const 0))
        (seqStmts
          [ .store (.bin .add (.reg prInAct) (.reg prW)) (.const 1)
          , .store (.bin .add (.reg prActStk) (.reg prActTop)) (.reg prW)
          , .assign prActTop (.bin .add (.reg prActTop) (.const 1)) ])
        .nop ]

lemma pushActWStmt_noRand : pushActWStmt.NoRand := by
  dsimp [pushActWStmt, seqStmts]
  repeat' constructor

lemma pushActW_triple {w : ℕ} {p : Program}
    {workAddr n m C_cap H target : ℕ} (active : List ℕ) (inAct : ℕ → Bool) (st₀ : State)
    (hw : PruneWordBound w n m C_cap H workAddr)
    (htarget : target < n)
    (hreg_w : st₀.regs prW = target)
    (hreg_ia : st₀.regs prInAct = wInAct workAddr n m H)
    (hreg_as : st₀.regs prActStk = wActStk workAddr n m H)
    (hreg_at : st₀.regs prActTop = active.length)
    (hinAct_mem : ∀ x < n, st₀.mem (wInAct workAddr n m H + x) = if inAct x = true then 1 else 0)
    (hactStk_mem : ∀ i < active.length,
      st₀.mem (wActStk workAddr n m H + i) = active.getD (active.length - 1 - i) 0)
    (hlen : (if inAct target = true then active else target :: active).length ≤ n) :
    let active' := if inAct target = true then active else target :: active
    let inAct' := fun x => if x = target then true else inAct x
    Triple w p (fun st => st = st₀) pushActWStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp2 → r ≠ prActTop → st'.regs r = st₀.regs r) ∧
          st'.regs prActTop = active'.length ∧
            st'.pos = st₀.pos ∧
              MemFrame st₀.mem st'.mem (wInAct workAddr n m H) (wPeelStk workAddr n m H) ∧
                (∀ x < n, st'.mem (wInAct workAddr n m H + x) = if inAct' x = true then 1 else 0) ∧
                  ∀ i < active'.length,
                    st'.mem (wActStk workAddr n m H + i) = active'.getD (active'.length - 1 - i) 0)
      (fun _ => 29) := by
  intro active' inAct'
  have hwb := pruneWordBound_pos hw
  have hlt2w : ∀ k, k < workAddr + pruneWorkSpace n m H → k < 2 ^ w := fun k hk => by
    unfold PruneWordBound at hw; omega
  have hia_addr : wInAct workAddr n m H + target < 2 ^ w :=
    hlt2w _ (by unfold pruneWorkSpace; dsimp [wInAct]; omega)
  let b := if inAct target = true then 1 else 0
  have h1 : Triple w p (fun st => st = st₀)
      (.assign prTmp2 (.load (.bin .add (.reg prInAct) (.reg prW))))
      (normalPost fun st1 =>
        st1.mem = st₀.mem ∧ st1.pos = st₀.pos ∧
          st1.regs = Function.update st₀.regs prTmp2 b)
      (fun _ => 5) := by
    intro st ω hst
    subst st
    have he := eval_load_add_eq w st₀ prInAct prW hreg_ia hreg_w hia_addr (hinAct_mem target htarget)
    refine ⟨.normal, { mem := st₀.mem, regs := Function.update st₀.regs prTmp2 b, pos := st₀.pos },
      5, ?_, ⟨rfl, rfl, rfl⟩, le_rfl⟩
    exact runs_assign_iff.mpr ⟨b, he, rfl, rfl, by simp [Expr.size]⟩
  have h2 : Triple w p
      (fun st1 => st1.mem = st₀.mem ∧ st1.pos = st₀.pos ∧
        st1.regs = Function.update st₀.regs prTmp2 b)
      (.cond (.bin .eq (.reg prTmp2) (.const 0))
        (seqStmts
          [ .store (.bin .add (.reg prInAct) (.reg prW)) (.const 1)
          , .store (.bin .add (.reg prActStk) (.reg prActTop)) (.reg prW)
          , .assign prActTop (.bin .add (.reg prActTop) (.const 1)) ])
        .nop)
      (normalPost fun st' =>
        (∀ r, r ≠ prTmp2 → r ≠ prActTop → st'.regs r = st₀.regs r) ∧
          st'.regs prActTop = active'.length ∧
            st'.pos = st₀.pos ∧
              MemFrame st₀.mem st'.mem (wInAct workAddr n m H) (wPeelStk workAddr n m H) ∧
                (∀ x < n, st'.mem (wInAct workAddr n m H + x) = if inAct' x = true then 1 else 0) ∧
                  ∀ i < active'.length,
                    st'.mem (wActStk workAddr n m H + i) = active'.getD (active'.length - 1 - i) 0)
      (fun _ => 23) := by
    intro st1 ω ⟨hm1, hpos1, hr1⟩
    have hr_tmp2 : st1.regs prTmp2 = b := by rw [hr1]; simp
    have hcond_eq : Expr.eval w st1 (.bin .eq (.reg prTmp2) (.const 0)) =
        some (if b = 0 then 1 else 0) :=
      Expr.eval_bin (eval_reg_eq w st1 prTmp2 hr_tmp2) (Expr.eval_const (by omega))
        (by simp [BinOp.eval]; split_ifs <;> omega)
    by_cases hia : inAct target = true
    · have hb1 : b = 1 := by simp [b, hia]
      have hact' : active' = active := by simp [active', hia]
      refine ⟨.normal, st1, 5, runs_cond_iff.mpr ⟨0, 1, ?_, ?_, by simp [Expr.size]⟩, ?_, by dsimp; omega⟩
      · simpa [hb1] using hcond_eq
      · simpa [hb1] using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
      · refine ⟨fun r hr2 _ => by rw [hr1, Function.update_of_ne hr2], ?_, hpos1, ?_, ?_, ?_⟩
        · rw [hr1, Function.update_of_ne (by decide), hreg_at, hact']
        · rw [hm1]; intro a _; rfl
        · intro x hx
          rw [hm1, hinAct_mem x hx]
          by_cases hxeq : x = target <;> simp [inAct', hxeq, hia]
        · intro i hi
          rw [hact'] at hi ⊢
          rw [hm1, hactStk_mem i hi]
    · have hiaF : inAct target = false := Bool.eq_false_iff.mpr hia
      have hb0 : b = 0 := by simp [b, hiaF]
      have hact' : active' = target :: active := by simp [active', hiaF]
      have hlen1 : active.length + 1 ≤ n := by simpa [hiaF] using hlen
      have hstk_addr : wActStk workAddr n m H + active.length < 2 ^ w :=
        hlt2w _ (by unfold pruneWorkSpace; dsimp [wActStk]; omega)
      have hat1_lt2w : active.length + 1 < 2 ^ w :=
        hlt2w _ (by unfold pruneWorkSpace; omega)
      have hr1_ia : st1.regs prInAct = wInAct workAddr n m H := by
        rw [hr1, Function.update_of_ne (by decide)]; exact hreg_ia
      have hr1_w : st1.regs prW = target := by
        rw [hr1, Function.update_of_ne (by decide)]; exact hreg_w
      have hr1_as : st1.regs prActStk = wActStk workAddr n m H := by
        rw [hr1, Function.update_of_ne (by decide)]; exact hreg_as
      have hr1_at : st1.regs prActTop = active.length := by
        rw [hr1, Function.update_of_ne (by decide)]; exact hreg_at
      let m2 := Function.update st1.mem (wInAct workAddr n m H + target) 1
      let m3 := Function.update m2 (wActStk workAddr n m H + active.length) target
      let regs' := Function.update st1.regs prActTop (active.length + 1)
      let st' : State := { mem := m3, regs := regs', pos := st1.pos }
      obtain ⟨o1, stx1, cx1, hrx1, ⟨ho1, hstx1⟩, hc1⟩ := runs_store_le
        (w := w) (p := p) (ω := ω) (st := st1)
        (x := wInAct workAddr n m H + target) (v := 1) (k := 0) (T := 5)
        (Q := fun o s => o = .normal ∧ s = { mem := m2, regs := st1.regs, pos := st1.pos })
        (eval_add_eq w st1 prInAct prW hr1_ia hr1_w hia_addr)
        (Expr.eval_const (by omega)) ⟨rfl, rfl⟩ (by simp [Expr.size])
      rcases ho1 with rfl; rcases hstx1 with rfl
      let st1m2 : State := { mem := m2, regs := st1.regs, pos := st1.pos }
      obtain ⟨o2, stx2, cx2, hrx2, ⟨ho2, hstx2⟩, hc2⟩ := runs_store_le
        (w := w) (p := p) (ω := ω) (st := st1m2)
        (x := wActStk workAddr n m H + active.length) (v := target) (k := 0) (T := 7)
        (Q := fun o s => o = .normal ∧ s = { mem := m3, regs := st1.regs, pos := st1.pos })
        (eval_add_eq w st1m2 prActStk prActTop hr1_as hr1_at hstk_addr)
        (eval_reg_eq w st1m2 prW hr1_w)
        ⟨rfl, rfl⟩ (by simp [Expr.size])
      rcases ho2 with rfl; rcases hstx2 with rfl
      have hrun_s3 : Runs w p ω (.assign prActTop (.bin .add (.reg prActTop) (.const 1)))
          { mem := m3, regs := st1.regs, pos := st1.pos } .normal st' 4 :=
        runs_assign_iff.mpr ⟨active.length + 1,
          Expr.eval_bin (eval_reg_eq w { mem := m3, regs := st1.regs, pos := st1.pos } prActTop hr1_at)
            (Expr.eval_const (by omega)) (by simp [BinOp.eval]; exact hat1_lt2w),
          rfl, rfl, by simp [Expr.size]⟩
      have hrun_body := runs_seq hrx1 (runs_seq hrx2 hrun_s3)
      refine ⟨.normal, st', 3 + (cx1 + (cx2 + 4 + 1) + 1) + 1,
        runs_cond_iff.mpr ⟨1, cx1 + (cx2 + 4 + 1) + 1, ?_, ?_, by simp [Expr.size]⟩,
        ?_, by dsimp; omega⟩
      · simpa [hb0] using hcond_eq
      · simpa [seqStmts] using hrun_body
      · refine ⟨fun r hr2 hrAT => by
          dsimp [st', regs']
          rw [Function.update_of_ne hrAT, hr1, Function.update_of_ne hr2], ?_, hpos1, ?_, ?_, ?_⟩
        · dsimp [st', regs']; simp [hact']
        · intro a ha
          dsimp [st', m3, m2]
          rw [Function.update_of_ne (by dsimp [wInAct, wActStk, wPeelStk] at *; omega),
            Function.update_of_ne (by dsimp [wInAct, wActStk, wPeelStk] at *; omega), hm1]
        · intro x hx
          dsimp [st', m3, m2]
          rw [Function.update_of_ne (by dsimp [wInAct, wActStk] at *; omega)]
          by_cases hxeq : x = target
          · subst hxeq; simp [inAct']
          · rw [Function.update_of_ne (by omega), hm1, hinAct_mem x hx]
            simp [inAct', hxeq]
        · intro i hi
          rw [hact'] at hi ⊢
          dsimp [st', m3, m2]
          by_cases hi_eq : i = active.length
          · subst hi_eq; simp
          · have hi_lt : i < active.length := by simp at hi; omega
            rw [Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp [wInAct, wActStk] at *; omega), hm1, hactStk_mem i hi_lt]
            have hget_rhs : (target :: active).getD (active.length - i) 0 =
                active.getD (active.length - 1 - i) 0 := by
              have hk : active.length - i = (active.length - 1 - i) + 1 := by omega
              rw [hk]; rfl
            rw [hget_rhs]
  exact Triple.seq h1 h2 (fun _ _ h => False.elim h) (fun _ _ _ _ h => False.elim h)
    (fun _ _ _ _ => by omega)

def pushFlowPrefixStmt : Stmt :=
  seqStmts
    [ .assign prTmp1 (.load (.bin .add (.reg prCur) (.reg prU)))
    , .assign prStart (.load (.bin .add (.reg prCsr) (.reg prU)))
    , .assign prJ (.bin .add (.reg prStart) (.reg prTmp1))
    , .assign prW (.load (.bin .add (.reg prCsrAdjV) (.reg prJ)))
    , .assign prTmp2 (.load (.bin .add (.reg prCsrAdjH) (.reg prJ)))
    , .assign prIdx (.bin .div (.reg prTmp2) (.const 2))
    , .assign prDir (.bin .mod (.reg prTmp2) (.const 2))
    , .assign prTmp2 (.load (.bin .add (.reg prFlowEnc) (.reg prIdx)))
    , .cond (.bin .eq (.reg prDir) (.const 1))
        (.assign prRc (.reg prTmp2))
        (.assign prRc (.bin .sub (.bin .mul (.const 2) (.reg prCcap)) (.reg prTmp2)))
    , .assign prTmp1 (.load (.bin .add (.reg prEx) (.reg prU)))
    , .cond (.bin .lt (.reg prRc) (.reg prTmp1))
        (.assign prDelta (.reg prRc))
        (.assign prDelta (.reg prTmp1))
    , .cond (.bin .eq (.reg prDir) (.const 1))
        (.store (.bin .add (.reg prFlowEnc) (.reg prIdx)) (.bin .sub (.reg prTmp2) (.reg prDelta)))
        (.store (.bin .add (.reg prFlowEnc) (.reg prIdx)) (.bin .add (.reg prTmp2) (.reg prDelta)))
    , .store (.bin .add (.reg prEx) (.reg prU)) (.bin .sub (.reg prTmp1) (.reg prDelta))
    , .assign prTmp3 (.load (.bin .add (.reg prEx) (.reg prW)))
    , .store (.bin .add (.reg prEx) (.reg prW)) (.bin .add (.reg prTmp3) (.reg prDelta)) ]

lemma pushFlowPrefixStmt_noRand : pushFlowPrefixStmt.NoRand := by
  dsimp [pushFlowPrefixStmt, seqStmts]
  repeat' constructor

def pushFlowStepStmt : Stmt :=
  .seq pushFlowPrefixStmt
    (.cond (.bin .lt (.reg prTmp1) (.reg prRc))
      (seqStmts
        [ .assign prActTop (.bin .sub (.reg prActTop) (.const 1))
        , .store (.bin .add (.reg prInAct) (.reg prU)) (.const 0)
        , pushActWStmt ])
      (seqStmts
        [ .assign prTmp3 (.load (.bin .add (.reg prCur) (.reg prU)))
        , .store (.bin .add (.reg prCur) (.reg prU)) (.bin .add (.reg prTmp3) (.const 1))
        , pushActWStmt ]))

lemma pushFlowStepStmt_noRand : pushFlowStepStmt.NoRand := by
  dsimp [pushFlowStepStmt, seqStmts, Stmt.NoRand]
  simp [pushFlowPrefixStmt_noRand, pushActWStmt_noRand]

lemma pushFlowPrefix_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr u : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} (st₀ : State)
    (hinv : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st₀)
    (huR : s.inR u = true)
    (hcur : s.cur u < (cfg.incEdges u).length)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hcsrB : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w) :
    let n := cfg.G.n
    let m := cfg.G.m
    let H := cfg.H
    let q := (cfg.incEdges u).getD (s.cur u) (0, false, 0)
    let idx := q.1
    let dir := q.2.1
    let nbr := q.2.2
    let rc := (↑cfg.C_cap - flowDir s.flow idx dir).toNat
    let δ := min (s.ex u) rc
    let flow' := fun k => if k = idx then if dir = true then s.flow idx - ↑δ else s.flow idx + ↑δ else s.flow k
    let ex' := fun x => if x = u then s.ex u - δ else if x = nbr then s.ex nbr + δ else s.ex x
    Triple w p (fun st => st = st₀ ∧ st.regs prU = u) pushFlowPrefixStmt
      (normalPost fun st1 =>
        (∀ r ≤ prCsrAdjH, st1.regs r = st₀.regs r) ∧
          st1.regs prU = u ∧
          st1.regs prW = nbr ∧
          st1.regs prTmp1 = s.ex u ∧
          st1.regs prRc = rc ∧
          st1.pos = st₀.pos ∧
          nbr < n ∧ nbr ≠ u ∧ idx < m ∧
          MemFrame st₀.mem st1.mem (wEx workAddr n m H) (wLvlVol workAddr n m H) ∧
          (∀ x, x < wEx workAddr n m H ∨ wDegR workAddr n m H ≤ x →
            x ≠ wFlowEnc workAddr n m H + idx → st1.mem x = st₀.mem x) ∧
          (∀ x < n, st1.mem (wEx workAddr n m H + x) = ex' x) ∧
          (∀ k < m, st1.mem (wFlowEnc workAddr n m H + k) = (↑cfg.C_cap + flow' k).toNat))
      (fun _ => 112) := by
  intro n m H q idx dir nbr rc δ flow' ex' st ω ⟨hst, hru⟩
  subst st
  have hwb := pruneWordBound_pos hw
  have hlt2w : ∀ k, k < workAddr + pruneWorkSpace n m H → k < 2 ^ w := fun k hk => by
    dsimp only [n, m, H] at hk; unfold PruneWordBound at hw; omega
  have huX : u ∈ cfg.X := hinv.prune_inv.inR_sub u huR
  have huN : u < n := by rw [hinv.cfg_X] at huX; exact Finset.mem_range.mp huX
  have hk_csr : s.cur u < (csrIncAux u 0 cfg.G.edges).length := by
    rwa [← hinv.cfg_incEdges u]
  have hq_eq : q = (csrIncAux u 0 cfg.G.edges)[s.cur u]'hk_csr := by
    dsimp [q]; rw [hinv.cfg_incEdges u, List.getD_eq_getElem _ _ hk_csr]
  rcases csrIncAux_getElem_lt hinv.cfg_valid.1 hk_csr with ⟨hq_idx_lt, hq_nbr_lt, hq_nbr_ne, _⟩
  have hidx_lt : idx < m := by dsimp [idx, m]; rw [hq_eq]; exact hq_idx_lt
  have hnbr_lt : nbr < n := by dsimp [nbr, n]; rw [hq_eq]; exact hq_nbr_lt
  have hnbr_ne : nbr ≠ u := by dsimp [nbr]; rw [hq_eq]; exact hq_nbr_ne
  have hcsr_off_lt : csrOff cfg.G u + s.cur u < 2 * m := by
    have hsub := csrOff_le_two_mul_m cfg.G (u + 1)
    rw [csrOff_succ] at hsub
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk_csr _) hsub
  have hj_lt2w : csrOff cfg.G u + s.cur u < 2 ^ w := by dsimp only [m] at *; omega
  have htwoC_lt2w : 2 * cfg.C_cap < 2 ^ w := by unfold PruneWordBound at hw; omega
  have h48 : 4 * cfg.C_cap * cfg.G.m ≤ 8 * cfg.C_cap * cfg.G.m :=
    Nat.mul_le_mul_right cfg.G.m (by omega)
  have hc_cap := hinv.prune_inv.flow_cap idx (by rw [hinv.cfg_edges]; exact hidx_lt)
  let enc := (↑cfg.C_cap + s.flow idx).toNat
  have henc_le : enc ≤ 2 * cfg.C_cap := by dsimp [enc]; omega
  have henc_eq : st₀.mem (wFlowEnc workAddr n m H + idx) = enc := hinv.flowEnc_eq idx hidx_lt
  have hrc_val : rc = if dir = true then enc else 2 * cfg.C_cap - enc := by
    dsimp [rc, enc, flowDir]; cases dir <;> (simp; try omega)
  have hrc_le : rc ≤ 2 * cfg.C_cap := by rw [hrc_val]; split_ifs <;> omega
  have hrc_lt2w : rc < 2 ^ w := by omega
  have hexu_le : s.ex u ≤ 4 * cfg.C_cap * m := hinv.ex_bound u huN
  have hexu_lt2w : s.ex u < 2 ^ w := by
    dsimp only [m] at *; unfold PruneWordBound at hw; omega
  have hexnbr_le : s.ex nbr ≤ 4 * cfg.C_cap * m := hinv.ex_bound nbr hnbr_lt
  have hexnbr_add_lt2w : s.ex nbr + δ < 2 ^ w := by
    have hdl_le : δ ≤ 2 * cfg.C_cap := by dsimp [δ]; omega
    dsimp only [m] at *; unfold PruneWordBound at hw; omega
  have hdir_val : (2 * idx + (if dir = true then 1 else 0)) % 2 = if dir = true then 1 else 0 := by
    cases dir <;> simp
  have hidx_val : (2 * idx + (if dir = true then 1 else 0)) / 2 = idx := by
    cases dir <;> (simp; try omega)
  have hadjH_lt2w : 2 * idx + (if dir = true then 1 else 0) < 2 ^ w := by
    have hidx_gm : idx < cfg.G.m := hidx_lt
    unfold PruneWordBound at hw; cases dir <;> simp <;> omega
  have hadjV_mem : st₀.mem (csrAddr + 2 * n + 1 + (csrOff cfg.G u + s.cur u)) = nbr := by
    have h1 := (hinv.csr_at.2 u huN (s.cur u) hk_csr).1
    rw [Nat.add_assoc (csrAddr + 2 * cfg.G.n + 1)] at h1
    dsimp only [n, nbr]; simp only [hq_eq]; exact h1
  have hadjH_mem : st₀.mem (csrAddr + 2 * n + 1 + 2 * m + (csrOff cfg.G u + s.cur u)) =
      2 * idx + (if dir = true then 1 else 0) := by
    have h2 := (hinv.csr_at.2 u huN (s.cur u) hk_csr).2
    rw [Nat.add_assoc (csrAddr + 2 * cfg.G.n + 1 + 2 * cfg.G.m)] at h2
    dsimp only [n, m, idx, dir]; simp only [hq_eq]; exact h2
  let r1 := Function.update st₀.regs prTmp1 (s.cur u)
  let r2 := Function.update r1 prStart (csrOff cfg.G u)
  let r3 := Function.update r2 prJ (csrOff cfg.G u + s.cur u)
  let r4 := Function.update r3 prW nbr
  let r5 := Function.update r4 prTmp2 (2 * idx + (if dir = true then 1 else 0))
  let r6 := Function.update r5 prIdx idx
  let r7 := Function.update r6 prDir (if dir = true then 1 else 0)
  let r8 := Function.update r7 prTmp2 enc
  let r9 := Function.update r8 prRc rc
  let r10 := Function.update r9 prTmp1 (s.ex u)
  let r11 := Function.update r10 prDelta δ
  let m12 := Function.update st₀.mem (wFlowEnc workAddr n m H + idx)
    (if dir = true then enc - δ else enc + δ)
  let m13 := Function.update m12 (wEx workAddr n m H + u) (s.ex u - δ)
  let r14 := Function.update r11 prTmp3 (s.ex nbr)
  let m15 := Function.update m13 (wEx workAddr n m H + nbr) (s.ex nbr + δ)
  let st15 : State := { mem := m15, regs := r14, pos := st₀.pos }
  have hs1 : Runs w p ω (.assign prTmp1 (.load (.bin .add (.reg prCur) (.reg prU)))) st₀
      .normal { mem := st₀.mem, regs := r1, pos := st₀.pos } 5 :=
    runs_assign_iff.mpr ⟨s.cur u,
      eval_load_add_eq w st₀ prCur prU hinv.reg_cur hru
        (hlt2w _ (by dsimp only [n, m, H]; unfold pruneWorkSpace; dsimp [wCur]; omega))
        (hinv.cur_eq u huN),
      rfl, rfl, by simp [Expr.size]⟩
  let s1 : State := { mem := st₀.mem, regs := r1, pos := st₀.pos }
  have hs2 : Runs w p ω (.assign prStart (.load (.bin .add (.reg prCsr) (.reg prU)))) s1
      .normal { mem := st₀.mem, regs := r2, pos := st₀.pos } 5 :=
    runs_assign_iff.mpr ⟨csrOff cfg.G u,
      eval_load_add_eq w s1 prCsr prU
        (by dsimp [s1, r1]; rw [Function.update_of_ne (by decide)]; exact hinv.reg_csr)
        (by dsimp [s1, r1]; rw [Function.update_of_ne (by decide)]; exact hru)
        (by dsimp only [n, m, H] at *; omega) (hinv.csr_at.1 u (Nat.le_of_lt huN)),
      rfl, rfl, by simp [Expr.size]⟩
  let s2 : State := { mem := st₀.mem, regs := r2, pos := st₀.pos }
  have hs3 : Runs w p ω (.assign prJ (.bin .add (.reg prStart) (.reg prTmp1))) s2
      .normal { mem := st₀.mem, regs := r3, pos := st₀.pos } 4 :=
    runs_assign_iff.mpr ⟨csrOff cfg.G u + s.cur u,
      eval_add_eq w s2 prStart prTmp1
        (by dsimp [s2, r2]; rw [Function.update_self])
        (by dsimp [s2, r2, r1]; rw [Function.update_of_ne (by decide), Function.update_self]) hj_lt2w,
      rfl, rfl, by simp [Expr.size]⟩
  let s3 : State := { mem := st₀.mem, regs := r3, pos := st₀.pos }
  have hs4 : Runs w p ω (.assign prW (.load (.bin .add (.reg prCsrAdjV) (.reg prJ)))) s3
      .normal { mem := st₀.mem, regs := r4, pos := st₀.pos } 5 :=
    runs_assign_iff.mpr ⟨nbr,
      eval_load_add_eq w s3 prCsrAdjV prJ
        (by dsimp [s3, r3, r2, r1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide)]; exact hinv.reg_adjV)
        (by dsimp [s3, r3]; rw [Function.update_self])
        (by dsimp only [n, m, H] at *; omega) hadjV_mem,
      rfl, rfl, by simp [Expr.size]⟩
  let s4 : State := { mem := st₀.mem, regs := r4, pos := st₀.pos }
  have hs5 : Runs w p ω (.assign prTmp2 (.load (.bin .add (.reg prCsrAdjH) (.reg prJ)))) s4
      .normal { mem := st₀.mem, regs := r5, pos := st₀.pos } 5 :=
    runs_assign_iff.mpr ⟨2 * idx + (if dir = true then 1 else 0),
      eval_load_add_eq w s4 prCsrAdjH prJ
        (by dsimp [s4, r4, r3, r2, r1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hinv.reg_adjH)
        (by dsimp [s4, r4, r3]; rw [Function.update_of_ne (by decide), Function.update_self])
        (by dsimp only [n, m, H] at *; omega) hadjH_mem,
      rfl, rfl, by simp [Expr.size]⟩
  let s5 : State := { mem := st₀.mem, regs := r5, pos := st₀.pos }
  have hr5_t2 : s5.regs prTmp2 = 2 * idx + (if dir = true then 1 else 0) := by
    dsimp [s5, r5]; rw [Function.update_self]
  have hdiv_lt : (2 * idx + if dir = true then 1 else 0) / 2 < 2 ^ w := by
    rw [hidx_val]; unfold PruneWordBound at hw; dsimp only [m] at hidx_lt; omega
  have hs6 : Runs w p ω (.assign prIdx (.bin .div (.reg prTmp2) (.const 2))) s5
      .normal { mem := st₀.mem, regs := r6, pos := st₀.pos } 4 :=
    runs_assign_iff.mpr ⟨idx, by
      have hev : Expr.eval w s5 (.bin .div (.reg prTmp2) (.const 2)) =
          some ((2 * idx + (if dir = true then 1 else 0)) / 2) :=
        Expr.eval_bin (op := .div)
          (eval_reg_eq w s5 prTmp2 hr5_t2)
          (Expr.eval_const (by omega)) (by dsimp only [BinOp.eval]; exact hdiv_lt)
      simpa only [hidx_val] using hev,
      rfl, rfl, by simp [Expr.size]⟩
  let s6 : State := { mem := st₀.mem, regs := r6, pos := st₀.pos }
  have hr6_t2 : s6.regs prTmp2 = 2 * idx + (if dir = true then 1 else 0) := by
    dsimp [s6, r6, r5]; rw [Function.update_of_ne (by decide), Function.update_self]
  have hs7 : Runs w p ω (.assign prDir (.bin .mod (.reg prTmp2) (.const 2))) s6
      .normal { mem := st₀.mem, regs := r7, pos := st₀.pos } 4 :=
    runs_assign_iff.mpr ⟨(if dir = true then 1 else 0), by
      have hev : Expr.eval w s6 (.bin .mod (.reg prTmp2) (.const 2)) =
          some ((2 * idx + (if dir = true then 1 else 0)) % 2) :=
        Expr.eval_bin (op := .mod)
          (eval_reg_eq w s6 prTmp2 hr6_t2)
          (Expr.eval_const (by omega))
          (lt_trans (Nat.mod_lt _ (by omega)) (by omega))
      simpa only [hdir_val] using hev,
      rfl, rfl, by simp [Expr.size]⟩
  let s7 : State := { mem := st₀.mem, regs := r7, pos := st₀.pos }
  have hr7_fe : s7.regs prFlowEnc = wFlowEnc workAddr n m H := by
    dsimp [s7, r7, r6, r5, r4, r3, r2, r1]; repeat rw [Function.update_of_ne (by decide)]
    exact hinv.reg_flowEnc
  have hr7_idx : s7.regs prIdx = idx := by
    dsimp [s7, r7, r6]; rw [Function.update_of_ne (by decide), Function.update_self]
  have hs8 : Runs w p ω (.assign prTmp2 (.load (.bin .add (.reg prFlowEnc) (.reg prIdx)))) s7
      .normal { mem := st₀.mem, regs := r8, pos := st₀.pos } 5 :=
    runs_assign_iff.mpr ⟨enc,
      eval_load_add_eq w s7 prFlowEnc prIdx hr7_fe hr7_idx
        (hlt2w _ (by dsimp only [n, m, H]; unfold pruneWorkSpace; dsimp [wFlowEnc]; omega)) henc_eq,
      rfl, rfl, by simp [Expr.size]⟩
  let s8 : State := { mem := st₀.mem, regs := r8, pos := st₀.pos }
  have hs9 : ∃ c9, c9 ≤ 10 ∧ Runs w p ω
      (.cond (.bin .eq (.reg prDir) (.const 1))
        (.assign prRc (.reg prTmp2))
        (.assign prRc (.bin .sub (.bin .mul (.const 2) (.reg prCcap)) (.reg prTmp2))))
      s8 .normal { mem := st₀.mem, regs := r9, pos := st₀.pos } c9 := by
    have hr8_dir : s8.regs prDir = (if dir = true then 1 else 0) := by
      dsimp [s8, r8, r7]; rw [Function.update_of_ne (by decide), Function.update_self]
    have hr8_t2 : s8.regs prTmp2 = enc := by dsimp [s8, r8]; rw [Function.update_self]
    have hr8_cc : s8.regs prCcap = cfg.C_cap := by
      dsimp [s8, r8, r7, r6, r5, r4, r3, r2, r1]; repeat rw [Function.update_of_ne (by decide)]
      exact hinv.reg_ccap
    have hcond : Expr.eval w s8 (.bin .eq (.reg prDir) (.const 1)) =
        some (if dir = true then 1 else 0) := by
      have hev : Expr.eval w s8 (.bin .eq (.reg prDir) (.const 1)) =
          some (if (if dir = true then 1 else 0) = 1 then 1 else 0) :=
        Expr.eval_bin (op := .eq) (eval_reg_eq w s8 prDir hr8_dir)
          (Expr.eval_const (by omega)) (by dsimp only [BinOp.eval]; split_ifs <;> omega)
      simpa only [show (if (if dir = true then 1 else 0) = 1 then 1 else 0) = if dir = true then 1 else 0 by cases dir <;> rfl] using hev
    cases hdir_b : dir
    · have hrc_b : rc = 2 * cfg.C_cap - enc := by simp [hrc_val, hdir_b]
      refine ⟨10, le_rfl, runs_cond_iff.mpr ⟨0, 6, ?_, ?_, by simp [Expr.size]⟩⟩
      · simpa [hdir_b] using hcond
      · simp only [↓reduceIte]
        refine runs_assign_iff.mpr ⟨rc, ?_, rfl, rfl, by simp [Expr.size]⟩
        rw [hrc_b]
        exact Expr.eval_bin (op := .sub)
          (Expr.eval_bin (op := .mul) (Expr.eval_const (by omega))
            (eval_reg_eq w s8 prCcap hr8_cc)
            (by simp [BinOp.eval]; exact htwoC_lt2w))
          (eval_reg_eq w s8 prTmp2 hr8_t2) (by simp [BinOp.eval]; omega)
    · have hrc_b : rc = enc := by simp [hrc_val, hdir_b]
      refine ⟨6, by omega, runs_cond_iff.mpr ⟨1, 2, ?_, ?_, by simp [Expr.size]⟩⟩
      · simpa [hdir_b] using hcond
      · simp only [Nat.one_ne_zero, ↓reduceIte]
        exact runs_assign_iff.mpr ⟨rc, by rw [hrc_b]; exact eval_reg_eq w s8 prTmp2 hr8_t2,
          rfl, rfl, by simp [Expr.size]⟩
  rcases hs9 with ⟨c9, hc9, hs9⟩
  let s9 : State := { mem := st₀.mem, regs := r9, pos := st₀.pos }
  have hs10 : Runs w p ω (.assign prTmp1 (.load (.bin .add (.reg prEx) (.reg prU)))) s9
      .normal { mem := st₀.mem, regs := r10, pos := st₀.pos } 5 :=
    runs_assign_iff.mpr ⟨s.ex u,
      eval_load_add_eq w s9 prEx prU
        (by dsimp [s9, r9, r8, r7, r6, r5, r4, r3, r2, r1]; repeat rw [Function.update_of_ne (by decide)]; exact hinv.reg_ex)
        (by dsimp [s9, r9, r8, r7, r6, r5, r4, r3, r2, r1]; repeat rw [Function.update_of_ne (by decide)]; exact hru)
        (hlt2w _ (by dsimp only [n, m, H]; unfold pruneWorkSpace; dsimp [wEx]; omega)) (hinv.ex_eq u huN),
      rfl, rfl, by simp [Expr.size]⟩
  let s10 : State := { mem := st₀.mem, regs := r10, pos := st₀.pos }
  have hs11 : Runs w p ω
      (.cond (.bin .lt (.reg prRc) (.reg prTmp1))
        (.assign prDelta (.reg prRc))
        (.assign prDelta (.reg prTmp1)))
      s10 .normal { mem := st₀.mem, regs := r11, pos := st₀.pos } 6 := by
    have hr10_rc : s10.regs prRc = rc := by
      dsimp [s10, r10, r9]; rw [Function.update_of_ne (by decide), Function.update_self]
    have hr10_t1 : s10.regs prTmp1 = s.ex u := by dsimp [s10, r10]; rw [Function.update_self]
    have hcond : Expr.eval w s10 (.bin .lt (.reg prRc) (.reg prTmp1)) =
        some (if rc < s.ex u then 1 else 0) :=
      Expr.eval_bin
        (eval_reg_eq w s10 prRc hr10_rc)
        (eval_reg_eq w s10 prTmp1 hr10_t1)
        (by simp [BinOp.eval]; split_ifs <;> omega)
    by_cases hlt : rc < s.ex u
    · have hdl : δ = rc := by dsimp [δ]; omega
      refine runs_cond_iff.mpr ⟨1, 2, ?_, ?_, by simp [Expr.size]⟩
      · simpa [hlt] using hcond
      · simp only [Nat.one_ne_zero, ↓reduceIte]
        exact runs_assign_iff.mpr ⟨δ, by rw [hdl]; exact eval_reg_eq w s10 prRc hr10_rc,
          rfl, rfl, by simp [Expr.size]⟩
    · have hdl : δ = s.ex u := by dsimp [δ]; omega
      refine runs_cond_iff.mpr ⟨0, 2, ?_, ?_, by simp [Expr.size]⟩
      · simpa [hlt] using hcond
      · simp only [↓reduceIte]
        exact runs_assign_iff.mpr ⟨δ, by rw [hdl]; exact eval_reg_eq w s10 prTmp1 hr10_t1,
          rfl, rfl, by simp [Expr.size]⟩
  let s11 : State := { mem := st₀.mem, regs := r11, pos := st₀.pos }
  have hs12 : ∃ c12, c12 ≤ 11 ∧ Runs w p ω
      (.cond (.bin .eq (.reg prDir) (.const 1))
        (.store (.bin .add (.reg prFlowEnc) (.reg prIdx)) (.bin .sub (.reg prTmp2) (.reg prDelta)))
        (.store (.bin .add (.reg prFlowEnc) (.reg prIdx)) (.bin .add (.reg prTmp2) (.reg prDelta))))
      s11 .normal { mem := m12, regs := r11, pos := st₀.pos } c12 := by
    have hfe_addr : wFlowEnc workAddr n m H + idx < 2 ^ w :=
      hlt2w _ (by dsimp only [n, m, H]; unfold pruneWorkSpace; dsimp [wFlowEnc]; omega)
    have hr11_dir : s11.regs prDir = (if dir = true then 1 else 0) := by
      dsimp [s11, r11, r10, r9, r8, r7]; repeat rw [Function.update_of_ne (by decide)]
      rw [Function.update_self]
    have hcond : Expr.eval w s11 (.bin .eq (.reg prDir) (.const 1)) =
        some (if dir = true then 1 else 0) := by
      have hev : Expr.eval w s11 (.bin .eq (.reg prDir) (.const 1)) =
          some (if (if dir = true then 1 else 0) = 1 then 1 else 0) :=
        Expr.eval_bin (op := .eq) (eval_reg_eq w s11 prDir hr11_dir)
          (Expr.eval_const (by omega)) (by dsimp only [BinOp.eval]; split_ifs <;> omega)
      simpa only [show (if (if dir = true then 1 else 0) = 1 then 1 else 0) = if dir = true then 1 else 0 by cases dir <;> rfl] using hev
    have haddr_ev : Expr.eval w s11 (.bin .add (.reg prFlowEnc) (.reg prIdx)) =
        some (wFlowEnc workAddr n m H + idx) :=
      eval_add_eq w s11 prFlowEnc prIdx
        (by dsimp [s11, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1]
            simp only [Function.update_apply, prDelta, prTmp1, prRc, prTmp2, prDir, prIdx,
              prW, prJ, prStart, prFlowEnc]
            simp [hinv.reg_flowEnc, n, m, H])
        (by dsimp [s11, r11, r10, r9, r8, r7, r6]
            simp only [Function.update_apply, prDelta, prTmp1, prRc, prTmp2, prDir, prIdx]
            simp)
        hfe_addr
    have hr11_t2 : s11.regs prTmp2 = enc := by
      dsimp [s11, r11, r10, r9, r8]
      simp only [Function.update_apply, prDelta, prTmp1, prRc, prTmp2]
      simp
    have hr11_dl : s11.regs prDelta = δ := by dsimp [s11, r11]; rw [Function.update_self]
    cases hdir_b : dir
    · have hval_lt : enc + δ < 2 ^ w := by
        have : δ ≤ 2 * cfg.C_cap - enc := by dsimp [δ]; rw [hrc_val, hdir_b]; exact min_le_right _ _
        omega
      obtain ⟨o, stx, cx, hrx, ⟨ho, hstx⟩, hc⟩ := runs_store_le
        (w := w) (p := p) (ω := ω) (st := s11)
        (x := wFlowEnc workAddr n m H + idx) (v := enc + δ) (k := 0) (T := 7)
        (Q := fun o s => o = .normal ∧ s = { mem := m12, regs := r11, pos := st₀.pos })
        haddr_ev
        (Expr.eval_bin (op := .add) (eval_reg_eq w s11 prTmp2 hr11_t2) (eval_reg_eq w s11 prDelta hr11_dl)
          (by simp [BinOp.eval]; exact hval_lt))
        ⟨rfl, by simp [s11, m12, hdir_b]⟩ (by simp [Expr.size])
      rcases ho with rfl; rcases hstx with rfl
      refine ⟨3 + cx + 1, by omega, runs_cond_iff.mpr ⟨0, cx, ?_, ?_, by simp [Expr.size]⟩⟩
      · simpa [hdir_b] using hcond
      · simp only [↓reduceIte]; exact hrx
    · have hval_lt : enc - δ < 2 ^ w := by omega
      obtain ⟨o, stx, cx, hrx, ⟨ho, hstx⟩, hc⟩ := runs_store_le
        (w := w) (p := p) (ω := ω) (st := s11)
        (x := wFlowEnc workAddr n m H + idx) (v := enc - δ) (k := 0) (T := 7)
        (Q := fun o s => o = .normal ∧ s = { mem := m12, regs := r11, pos := st₀.pos })
        haddr_ev
        (Expr.eval_bin (op := .sub) (eval_reg_eq w s11 prTmp2 hr11_t2) (eval_reg_eq w s11 prDelta hr11_dl)
          (by simp [BinOp.eval]; exact hval_lt))
        ⟨rfl, by simp [s11, m12, hdir_b]⟩ (by simp [Expr.size])
      rcases ho with rfl; rcases hstx with rfl
      refine ⟨3 + cx + 1, by omega, runs_cond_iff.mpr ⟨1, cx, ?_, ?_, by simp [Expr.size]⟩⟩
      · simpa [hdir_b] using hcond
      · simp only [Nat.one_ne_zero, ↓reduceIte]; exact hrx
  rcases hs12 with ⟨c12, hc12, hs12⟩
  let s12 : State := { mem := m12, regs := r11, pos := st₀.pos }
  have hr12_t1 : s12.regs prTmp1 = s.ex u := by
    dsimp [s12, r11, r10]; rw [Function.update_of_ne (by decide), Function.update_self]
  have hr12_dl : s12.regs prDelta = δ := by dsimp [s12, r11]; rw [Function.update_self]
  have hexu_addr : wEx workAddr n m H + u < 2 ^ w :=
    hlt2w _ (by dsimp only [n, m, H]; unfold pruneWorkSpace; dsimp [wEx]; omega)
  obtain ⟨o13, stx13, c13, hs13, ⟨ho13, hstx13⟩, hc13⟩ := runs_store_le
    (w := w) (p := p) (ω := ω) (st := s12)
    (x := wEx workAddr n m H + u) (v := s.ex u - δ) (k := 0) (T := 7)
    (Q := fun o s => o = .normal ∧ s = { mem := m13, regs := r11, pos := st₀.pos })
    (eval_add_eq w s12 prEx prU
      (by dsimp [s12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1]; repeat rw [Function.update_of_ne (by decide)]; exact hinv.reg_ex)
      (by dsimp [s12, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1]; repeat rw [Function.update_of_ne (by decide)]; exact hru) hexu_addr)
    (Expr.eval_bin (op := .sub) (eval_reg_eq w s12 prTmp1 hr12_t1) (eval_reg_eq w s12 prDelta hr12_dl)
      (by simp [BinOp.eval]; omega))
    ⟨rfl, rfl⟩ (by simp [Expr.size])
  rcases ho13 with rfl; rcases hstx13 with rfl
  let s13 : State := { mem := m13, regs := r11, pos := st₀.pos }
  have hm13_nbr : m13 (wEx workAddr n m H + nbr) = s.ex nbr := by
    dsimp [m13, m12]
    rw [Function.update_of_ne (by omega),
      Function.update_of_ne (by dsimp [wEx, wFlowEnc]; omega), hinv.ex_eq nbr hnbr_lt]
  have hexw_addr : wEx workAddr n m H + nbr < 2 ^ w :=
    hlt2w _ (by dsimp only [n, m, H]; unfold pruneWorkSpace; dsimp [wEx]; omega)
  have hs14 : Runs w p ω (.assign prTmp3 (.load (.bin .add (.reg prEx) (.reg prW)))) s13
      .normal { mem := m13, regs := r14, pos := st₀.pos } 5 :=
    runs_assign_iff.mpr ⟨s.ex nbr,
      eval_load_add_eq w s13 prEx prW
        (by dsimp [s13, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1]
            simp only [Function.update_apply, prDelta, prTmp1, prRc, prTmp2, prDir, prIdx,
              prW, prJ, prStart, prEx]
            simp [hinv.reg_ex, n, m, H])
        (by dsimp [s13, r11, r10, r9, r8, r7, r6, r5, r4]
            simp only [Function.update_apply, prDelta, prTmp1, prRc, prTmp2, prDir, prIdx, prW]
            simp)
        hexw_addr hm13_nbr,
      rfl, rfl, by simp [Expr.size]⟩
  let s14 : State := { mem := m13, regs := r14, pos := st₀.pos }
  have hr14_t3 : s14.regs prTmp3 = s.ex nbr := by dsimp [s14, r14]; rw [Function.update_self]
  have hr14_dl : s14.regs prDelta = δ := by
    dsimp [s14, r14, r11]; rw [Function.update_of_ne (by decide), Function.update_self]
  obtain ⟨o15, stx15, c15, hs15, ⟨ho15, hstx15⟩, hc15⟩ := runs_store_le
    (w := w) (p := p) (ω := ω) (st := s14)
    (x := wEx workAddr n m H + nbr) (v := s.ex nbr + δ) (k := 0) (T := 7)
    (Q := fun o s => o = .normal ∧ s = st15)
    (eval_add_eq w s14 prEx prW
      (by dsimp [s14, r14, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1]
          simp only [Function.update_apply, prTmp3, prDelta, prTmp1, prRc, prTmp2, prDir, prIdx,
            prW, prJ, prStart, prEx]
          simp [hinv.reg_ex, n, m, H])
      (by dsimp [s14, r14, r11, r10, r9, r8, r7, r6, r5, r4]
          simp only [Function.update_apply, prTmp3, prDelta, prTmp1, prRc, prTmp2, prDir, prIdx, prW]
          simp)
      hexw_addr)
    (Expr.eval_bin (op := .add) (eval_reg_eq w s14 prTmp3 hr14_t3)
      (eval_reg_eq w s14 prDelta hr14_dl)
      (by simp [BinOp.eval]; exact hexnbr_add_lt2w))
    ⟨rfl, rfl⟩ (by simp [Expr.size])
  rcases ho15 with rfl; rcases hstx15 with rfl
  have hrun :=
    runs_seq hs1 (runs_seq hs2 (runs_seq hs3 (runs_seq hs4 (runs_seq hs5
      (runs_seq hs6 (runs_seq hs7 (runs_seq hs8 (runs_seq hs9 (runs_seq hs10
        (runs_seq hs11 (runs_seq hs12 (runs_seq hs13 (runs_seq hs14 hs15)))))))))))))
  refine ⟨.normal, st15, _, hrun, ?_, by dsimp; omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, hnbr_lt, hnbr_ne, hidx_lt, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have hne := le_adjH_ne_work hr
    dsimp [st15, r14, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1]
    simp [hne.2.2.1, hne.2.2.2.2.1, hne.1, hne.2.2.2.1, hne.2.1,
      hne.2.2.2.2.2.2.1, hne.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.1, hne.2.2.2.2.2.2.2.2.1,
      hne.2.2.2.2.2.2.2.2.2.1]
  · dsimp [st15, r14, r11, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1]
    simp only [Function.update_apply, prTmp3, prDelta, prTmp1, prRc, prTmp2, prDir, prIdx,
      prW, prJ, prStart, prU]
    simp [hru]
  · dsimp [st15, r14, r11, r10, r9, r8, r7, r6, r5, r4]
    simp only [Function.update_apply, prTmp3, prDelta, prTmp1, prRc, prTmp2, prDir, prIdx, prW]
    simp
  · dsimp [st15, r14, r11, r10]
    simp only [Function.update_apply, prTmp3, prDelta, prTmp1]
    simp
  · dsimp [st15, r14, r11, r10, r9]
    simp only [Function.update_apply, prTmp3, prDelta, prTmp1, prRc]
    simp
  · intro a ha
    dsimp [st15, m15, m13, m12]
    dsimp only [n, m, H, wEx, wFlowEnc, wLvlVol] at ha hnbr_lt huN hidx_lt ⊢
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  · intro a ha hne
    dsimp [st15, m15, m13, m12]
    dsimp only [n, m, H, wEx, wDegR, wFlowEnc] at ha hnbr_lt huN hidx_lt ⊢
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne hne]
  · intro x hx
    dsimp [st15, m15, m13, m12, ex']
    by_cases hxn : x = nbr
    · subst hxn
      rw [Function.update_self]; simp [hnbr_ne]
    · rw [Function.update_of_ne (by omega)]
      by_cases hxu : x = u
      · subst hxu; simp
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by dsimp [wEx, wFlowEnc]; omega),
          hinv.ex_eq x hx]
        simp [hxu, hxn]
  · intro k hk
    dsimp [st15, m15, m13, m12, flow']
    rw [Function.update_of_ne (by dsimp [wEx, wFlowEnc]; omega),
      Function.update_of_ne (by dsimp [wEx, wFlowEnc]; omega)]
    by_cases hki : k = idx
    · rw [hki, Function.update_self]
      simp only [↓reduceIte]
      have hnonneg : (0 : ℤ) ≤ ↑cfg.C_cap + s.flow idx := by omega
      have henc_z : (enc : ℤ) = ↑cfg.C_cap + s.flow idx := by
        dsimp [enc]; exact Int.toNat_of_nonneg hnonneg
      cases hdb : dir <;> simp
      · have : (↑(enc + δ) : ℤ) = ↑cfg.C_cap + (s.flow idx + ↑δ) := by rw [Nat.cast_add, henc_z]; ring
        rw [← this]; exact (Int.toNat_natCast _).symm
      · have hdel_le : δ ≤ enc := by dsimp [δ]; rw [hrc_val, hdb]; exact min_le_right _ _
        have : (↑(enc - δ) : ℤ) = ↑cfg.C_cap + (s.flow idx - ↑δ) := by
          rw [Nat.cast_sub hdel_le, henc_z]; ring
        rw [← this]; exact (Int.toNat_natCast _).symm
    · rw [Function.update_of_ne (by omega), hinv.flowEnc_eq k hk]
      simp [hki]


end MinCostFlow.Expander
