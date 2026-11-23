module

public import MinCostFlow.Expander.PruningRemoveBranchProg

/-!
# Full Loop Triple for Removing a Vertex from R
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM
open MinCostFlow.Cited

theorem removeOneFromR_triple {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr a : ℕ}
    {A : Finset ℕ} {s : PruneState} (peelInit : List ℕ) (st₀ : State)
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hval : cfg.Valid)
    (hsw : SweepInv cfg A s) (haR : s.inR a = true)
    (hpeel_nd : peelInit.Nodup)
    (hpeel_lt : ∀ x ∈ peelInit, x < cfg.G.n ∧ ((if x = a then false else s.inR x) = true → s.degR x < cfg.θ_out_nat))
    (hpeel_iso : ∀ x, (cfg.incEdges x).length = 0 → x ∉ peelInit)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (hcsr : HasCsrAt st₀.mem csrAddr cfg.G) :
    let n := cfg.G.n
    let m := cfg.G.m
    let H := cfg.H
    let inR' : ℕ → Bool := fun x => if x = a then false else s.inR x
    let sInit : PruneState := { s with inR := inR', peelQ := peelInit }
    let sRes := (cfg.incEdges a).foldl (removeEdgeStep cfg s.flow inR') sInit
    let s' := removeOneFromR cfg a s
    Triple w p
      (fun st => st = st₀ ∧
        PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st ∧
        st.regs prU = a ∧
        st.regs prActTop = s.active.length ∧
        st.regs prPeelTop = peelInit.length ∧
        (∀ u < n, st.mem (outRAddr + u) = if s.inR u then 1 else 0) ∧
        (∀ u < n, st.mem (wEx workAddr n m H + u) = s.ex u) ∧
        (∀ u < n, st.mem (wDegR workAddr n m H + u) = s.degR u) ∧
        (∀ u < n, st.mem (wInAct workAddr n m H + u) = if s.inActive u then 1 else 0) ∧
        (∀ i < s.active.length, st.mem (wActStk workAddr n m H + i) = s.active.getD (s.active.length - 1 - i) 0) ∧
        (∀ i < peelInit.length, st.mem (wPeelStk workAddr n m H + i) = peelInit.getD (peelInit.length - 1 - i) 0) ∧
        (∀ idx < m, st.mem (wFlowEnc workAddr n m H + idx) = (↑cfg.C_cap + s.flow idx).toNat))
      removeOneFromRStmt
      (normalPost fun st' =>
        (∀ r, r ≠ prStart → r ≠ prEnd → r ≠ prJ → r ≠ prW → r ≠ prIdx → r ≠ prDir →
          r ≠ prRc → r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prTmp3 →
          r ≠ prActTop → r ≠ prPeelTop → st'.regs r = st₀.regs r) ∧
        PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st' ∧
        st'.regs prU = a ∧
        st'.regs prActTop = s'.active.length ∧
        st'.regs prPeelTop = sRes.peelQ.length ∧
        st'.pos = st₀.pos ∧
        PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + n)
          (wEx workAddr n m H) (wLvlNext workAddr n m H) ∧
        (∀ u < n, st'.mem (outRAddr + u) = if s'.inR u then 1 else 0) ∧
        (∀ u < n, st'.mem (wEx workAddr n m H + u) = s'.ex u) ∧
        (∀ u < n, st'.mem (wDegR workAddr n m H + u) = s'.degR u) ∧
        (∀ u < n, st'.mem (wInAct workAddr n m H + u) = if s'.inActive u then 1 else 0) ∧
        (∀ i < s'.active.length, st'.mem (wActStk workAddr n m H + i) = s'.active.getD (s'.active.length - 1 - i) 0) ∧
        (∀ i < sRes.peelQ.length, st'.mem (wPeelStk workAddr n m H + i) = sRes.peelQ.getD (sRes.peelQ.length - 1 - i) 0))
      (fun _ => 150 * (cfg.incEdges a).length + 30) := by
  intro n m H inR' sInit sRes s' st ω
    ⟨hst, hptrs, hru, hrAT, hrPT, houtR, hex, hdr, hia, has, hps, hfe⟩
  subst st
  have hGv : cfg.G.IsValid := hval.1
  have haX : a ∈ cfg.X := hsw.inR_sub a haR
  have ha_n : a < n := by rw [hcfgX] at haX; exact Finset.mem_range.mp haX
  have hinc_eq : cfg.incEdges a = csrIncAux a 0 cfg.G.edges := by
    unfold PruneCfg.incEdges PruneCfg.edges
    have hx : cfg.X = cfg.G.verts := hcfgX
    rw [hx, inside_verts_of_isValid hGv]
    exact incEdgesAux_eq_csrIncAux' a 0 cfg.G.edges
  have hs'_inv_all := removeOneFromR_inv hval hsw haR
  have hsw' : SweepInv cfg (A \ {a}) s' := hs'_inv_all.1
  have hs'_ex_bd : ∀ u, s'.inR u = true → s'.ex u ≤ 4 * cfg.C_cap * m := fun u hu =>
    ex_le_bound_of_flow_balance hcfgX hGv hsw'.flow_cap hsw'.flow_balance hsw'.inR_sub hu
  have hL_inR : ∀ q ∈ cfg.incEdges a, inR' q.2.2 = true → q.2.2 ∈ cfg.X := fun q hq _ =>
    (incEdges_mem_sub hq).2
  have hL_n : ∀ q ∈ cfg.incEdges a, inR' q.2.2 = true → q.2.2 < n := fun q hq hqR => by
    have := hL_inR q hq hqR; rw [hcfgX] at this; exact Finset.mem_range.mp this
  have hL_deg : ∀ q ∈ cfg.incEdges a, inR' q.2.2 = true → 0 < (cfg.incEdges q.2.2).length :=
    fun q hq _ => List.length_pos_of_mem (incEdges_symm hq)
  have hwb := hw
  unfold PruneWordBound pruneWorkSpace at hwb
  have h0lt : 0 < 2 ^ w := by omega
  have h1lt : 1 < 2 ^ w := by omega
  have h2lt : 2 < 2 ^ w := by omega
  have h2m_lt : 2 * m < 2 ^ w := by omega
  have h4Cm_lt : 4 * cfg.C_cap * m < 2 ^ w := by
    have h4le8 : 4 * cfg.C_cap * m ≤ 8 * cfg.C_cap * cfg.G.m :=
      Nat.mul_le_mul_right cfg.G.m (by omega)
    omega
  have h2C_lt : 2 * cfg.C_cap < 2 ^ w := by omega
  have hn_lt : n < 2 ^ w := by omega
  have hlt_pow : ∀ x, x ≤ workAddr + (12 * n + m + 2 * H + 2) → x < 2 ^ w := fun x hx => by omega
  have hdisj_outR_work := hdisj.2.2.2.2.2.2
  have hdisj_csr_outR := hdisj.2.1
  have hdisj_csr_work := hdisj.2.2.2.2.1
  have ha1_lt : a + 1 < 2 ^ w := by omega
  have ha1_le : a + 1 ≤ n := by omega
  have hcsr_a_lt : csrAddr + a < 2 ^ w := by omega
  have hcsr_a1_lt : csrAddr + (a + 1) < 2 ^ w := by omega
  have houtRa_lt : outRAddr + a < 2 ^ w := by omega
  have hstart_eq : st₀.mem (csrAddr + a) = csrOff cfg.G a := hcsr.1 a (le_of_lt ha_n)
  have hend_eq : st₀.mem (csrAddr + (a + 1)) = csrOff cfg.G (a + 1) := hcsr.1 (a + 1) ha1_le
  have hlen_eq : csrOff cfg.G (a + 1) = csrOff cfg.G a + (cfg.incEdges a).length := by
    rw [csrOff_succ, hinc_eq]
  have hend_lt_2m : csrOff cfg.G (a + 1) ≤ 2 * m := by
    simpa [m, Cited.Graph.m] using csrOff_le_two_mul_m cfg.G (a + 1)
  have hstart_lt_w : csrOff cfg.G a < 2 ^ w := by omega
  have hend_lt_w : csrOff cfg.G (a + 1) < 2 ^ w := by omega
  let baseIdx := csrOff cfg.G a
  let len := (cfg.incEdges a).length
  have hshift_all := foldl_removeEdgeStep_peelShift cfg s.flow inR' (cfg.incEdges a) s
  obtain ⟨_, _, hshift⟩ := hshift_all
  have hshift_eq := hshift peelInit
  have hs0_const : { s with inR := inR', peelQ := peelInit } = sInit := rfl
  have hs'_foldl : s' = (cfg.incEdges a).foldl (removeEdgeStep cfg s.flow inR') { s with inR := inR' } := rfl
  have hres_fields : sRes.inR = s'.inR ∧ sRes.ex = s'.ex ∧ sRes.degR = s'.degR ∧
      sRes.active = s'.active ∧ sRes.inActive = s'.inActive := by
    have hf1 := foldl_removeEdgeStep_peelShift cfg s.flow inR' (cfg.incEdges a) { s with inR := inR' }
    rcases hf1 with ⟨_, _, hf1s⟩
    have hf1p := hf1s peelInit
    have heq1 : ({ { s with inR := inR' } with peelQ := peelInit } : PruneState) = sInit := rfl
    rw [heq1] at hf1p
    exact ⟨hf1p.2.1, hf1p.2.2.2.2.2.1, hf1p.2.2.2.2.2.2.1, hf1p.2.2.2.2.2.2.2.1, hf1p.2.2.2.2.2.2.2.2.1⟩
  let skFn : ℕ → PruneState := fun k => ((cfg.incEdges a).take k).foldl (removeEdgeStep cfg s.flow inR') sInit
  have hsk_const : ∀ k, (skFn k).inR = inR' ∧ (skFn k).h = s.h ∧ (skFn k).cur = s.cur ∧
      (skFn k).abs = s.abs ∧ (skFn k).flow = s.flow ∧ (skFn k).steps = s.steps := by
    intro k
    have hc := foldl_removeEdgeStep_const cfg s.flow inR' ((cfg.incEdges a).take k) sInit
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2⟩
  have hsk_props : ∀ k ≤ len,
      (∀ x, (skFn k).inActive x = true ↔ x ∈ (skFn k).active) ∧
      (skFn k).active.Nodup ∧ (∀ x ∈ (skFn k).active, x ∈ cfg.X) ∧
      (skFn k).peelQ.Nodup ∧
      (∀ x ∈ (skFn k).peelQ, x < n ∧ (inR' x = true → (skFn k).degR x < cfg.θ_out_nat)) ∧
      (∀ w, (skFn k).ex w ≤ sRes.ex w) ∧
      (∀ w, (skFn k).degR w ≤ s.degR w) := by
    intro k hk
    have hL1 : ∀ q ∈ (cfg.incEdges a).take k, inR' q.2.2 = true → q.2.2 ∈ cfg.X :=
      fun q hq => hL_inR q (List.mem_of_mem_take hq)
    have hL2 : ∀ q ∈ (cfg.incEdges a).take k, inR' q.2.2 = true → 0 < (cfg.incEdges q.2.2).length :=
      fun q hq => hL_deg q (List.mem_of_mem_take hq)
    have hLn : ∀ q ∈ (cfg.incEdges a).take k, inR' q.2.2 = true → q.2.2 < n :=
      fun q hq => hL_n q (List.mem_of_mem_take hq)
    have hinit_iso : ∀ x, (cfg.incEdges x).length = 0 →
        sInit.ex x = 0 ∧ sInit.h x = 0 ∧ x ∉ sInit.active ∧ x ∉ sInit.peelQ := by
      intro x hx
      have h0 := hsw.no_ex_isolated x hx
      exact ⟨h0.1, h0.2.1, h0.2.2.1, hpeel_iso x hx⟩
    have hp := foldl_removeEdgeStep_mem_props cfg s.flow inR' ((cfg.incEdges a).take k) hL1 hL2
      sInit rfl hsw.active_mem_inActive hsw.active_nodup hsw.active_sub hinit_iso
    have hpq := @foldl_removeEdgeStep_peelQ_props cfg s.flow inR'
      ((cfg.incEdges a).take k) sInit hLn hpeel_nd hpeel_lt
    refine ⟨hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hpq.1, hpq.2, fun w => ?_, fun w => ?_⟩
    · have hsplit : cfg.incEdges a = (cfg.incEdges a).take k ++ (cfg.incEdges a).drop k :=
        (List.take_append_drop k (cfg.incEdges a)).symm
      dsimp only [sRes, skFn]
      conv_rhs => rw [hsplit, List.foldl_append]
      exact foldl_removeEdgeStep_ex_mono ((cfg.incEdges a).drop k) _ w
    · exact foldl_removeEdgeStep_degR_antitone ((cfg.incEdges a).take k) sInit w
  let eCond : Expr := .bin .lt (.reg prJ) (.reg prEnd)
  have heSize : eCond.size = 3 := rfl
  let Inv : ℕ → State → Prop := fun k st =>
    k ≤ len ∧
    (∀ r, r ≠ prStart → r ≠ prEnd → r ≠ prJ → r ≠ prW → r ≠ prIdx → r ≠ prDir →
      r ≠ prRc → r ≠ prTmp1 → r ≠ prTmp2 → r ≠ prTmp3 →
      r ≠ prActTop → r ≠ prPeelTop → st.regs r = st₀.regs r) ∧
    st.regs prStart = baseIdx ∧
    st.regs prEnd = baseIdx + len ∧
    st.regs prJ = baseIdx + k ∧
    st.regs prActTop = (skFn k).active.length ∧
    st.regs prPeelTop = (skFn k).peelQ.length ∧
    st.pos = st₀.pos ∧
    PreservedOutside2 st₀.mem st.mem outRAddr (outRAddr + n)
      (wEx workAddr n m H) (wLvlNext workAddr n m H) ∧
    (∀ u < n, st.mem (outRAddr + u) = if inR' u then 1 else 0) ∧
    (∀ u < n, st.mem (wEx workAddr n m H + u) = (skFn k).ex u) ∧
    (∀ u < n, st.mem (wDegR workAddr n m H + u) = (skFn k).degR u) ∧
    (∀ u < n, st.mem (wInAct workAddr n m H + u) = if (skFn k).inActive u then 1 else 0) ∧
    (∀ i < (skFn k).active.length,
      st.mem (wActStk workAddr n m H + i) = (skFn k).active.getD ((skFn k).active.length - 1 - i) 0) ∧
    (∀ i < (skFn k).peelQ.length,
      st.mem (wPeelStk workAddr n m H + i) = (skFn k).peelQ.getD ((skFn k).peelQ.length - 1 - i) 0)
  have hInv_csr : ∀ k st, Inv k st → HasCsrAt st.mem csrAddr cfg.G ∧
      (∀ idx < m, st.mem (wFlowEnc workAddr n m H + idx) = (↑cfg.C_cap + s.flow idx).toNat) := by
    intro k st hInv
    rcases hInv with ⟨_, _, _, _, _, _, _, _, hpr, _⟩
    have hmem_csr : ∀ x, csrAddr ≤ x → x < csrAddr + 2 * n + 1 + 4 * m → st.mem x = st₀.mem x := by
      intro x hx1 hx2
      dsimp only [n, m, H] at hx1 hx2
      apply hpr x
      · rcases hdisj_csr_outR with h | h <;> [right; left] <;> omega
      · unfold pruneWorkSpace at hdisj_csr_work
        rcases hdisj_csr_work with h | h
        · exact Or.inr (by dsimp only [wLvlNext]; omega)
        · exact Or.inl (by dsimp only [wEx]; omega)
    refine ⟨⟨fun u hu => (hmem_csr _ (by omega) (by omega)).trans (hcsr.1 u hu), fun u hu j hj => ?_⟩,
      fun idx hidx => ?_⟩
    · have hj_lt : csrOff cfg.G u + j < 2 * m := by
        have h1 : csrOff cfg.G u + j < csrOff cfg.G (u + 1) := by rw [csrOff_succ]; omega
        have h2 := csrOff_le_two_mul_m cfg.G (u + 1)
        exact lt_of_lt_of_le h1 (by simpa [m, Cited.Graph.m] using h2)
      refine ⟨(hmem_csr _ (by omega) (by omega)).trans (hcsr.2 u hu j hj).1,
        (hmem_csr _ (by omega) (by omega)).trans (hcsr.2 u hu j hj).2⟩
    · rw [hpr (wFlowEnc workAddr n m H + idx)]
      · exact hfe idx hidx
      · unfold pruneWorkSpace at hdisj_outR_work
        rcases hdisj_outR_work with h | h <;> [right; left] <;> dsimp [wFlowEnc] <;> omega
      · right; dsimp [wFlowEnc, wLvlNext]; omega
  have hInv_ptrs : ∀ k st, Inv k st → PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st := by
    intro k st ⟨_, hr, _⟩
    exact pruneStepRegs_of_agree hptrs fun r hle hAT hPT => by
      dsimp only [prCsrAdjH] at hle
      exact hr r
        (by dsimp only [prStart]; omega)
        (by dsimp only [prEnd]; omega)
        (by dsimp only [prJ]; omega)
        (by dsimp only [prW]; omega)
        (by dsimp only [prIdx]; omega)
        (by dsimp only [prDir]; omega)
        (by dsimp only [prRc]; omega)
        (by dsimp only [prTmp1]; omega)
        (by dsimp only [prTmp2]; omega)
        (by dsimp only [prTmp3]; omega)
        hAT hPT
  have hloop : Triple w p (Inv 0)
      (.loop eCond
        (seqStmts [
          .assign prW (.load (.bin .add (.reg prCsrAdjV) (.reg prJ))),
          .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prW))),
          removeOneBranchStmt,
          .assign prJ (.bin .add (.reg prJ) (.const 1))
        ]))
      (normalPost fun st => Inv len st)
      (fun _ => 150 * len + 4) := by
    apply (Triple.loop_inv (α := ℕ)
      (m := fun k => len - k) (rem := fun k => 150 * (len - k) + 4)
      (condVal := fun st => if st.regs prJ < st.regs prEnd then 1 else 0)
      (Inv := Inv) ?_ ?_ ?_ 0).mono_cost (fun _ _ => le_rfl)
    · intro k st hInv
      rcases hInv with ⟨hk, _, _, hrEnd, hrJ, _⟩
      simp only [eCond, Expr.eval, hrJ, hrEnd, WordRAM.BinOp.eval]
      by_cases hcmp : baseIdx + k < baseIdx + len <;> simp [hcmp, h1lt, h0lt]
    · intro k st hInv heq
      rcases hInv with ⟨hk, hr, hrS, hrE, hrJ, hrAT1, hrPT1, hp, hpr, hOut, hEx, hDr, hIA, hAS, hPS⟩
      have hkEq : k = len := by
        by_contra hne
        have hlt : k < len := by omega
        rw [hrJ, hrE] at heq; simp [hlt] at heq
      subst hkEq
      exact ⟨⟨le_rfl, hr, hrS, hrE, hrJ, hrAT1, hrPT1, hp, hpr, hOut, hEx, hDr, hIA, hAS, hPS⟩,
        by simp [eCond, Expr.size]⟩
    · intro k st hInv hne
      have hptrs_k := hInv_ptrs k st hInv
      obtain ⟨hcsr_k, hfe_k⟩ := hInv_csr k st hInv
      rcases hInv with ⟨hk, hr, hrS, hrE, hrJ, hrAT1, hrPT1, hp, hpr, hOut, hEx, hDr, hIA, hAS, hPS⟩
      have hk_lt : k < len := by
        by_contra hge
        rw [hrJ, hrE] at hne; simp [hge] at hne
      have hk_csr : k < (csrIncAux a 0 cfg.G.edges).length := by rw [← hinc_eq]; exact hk_lt
      let q := (cfg.incEdges a)[k]'hk_lt
      have hq_csr : (csrIncAux a 0 cfg.G.edges)[k]'hk_csr = q := by
        dsimp only [q]; simp only [hinc_eq]
      have hq_props := csrIncAux_getElem_lt hGv hk_csr
      rw [hq_csr] at hq_props
      rcases hq_props with ⟨hq_idx_lt, hq_w_lt, hq_ne_a, _⟩
      have hjk_2m : baseIdx + k < 2 * m := by omega
      have hjk_w : baseIdx + k < 2 ^ w := by omega
      have hj1_w : baseIdx + k + 1 < 2 ^ w := by omega
      have hadjV_addr_lt : csrAddr + 2 * n + 1 + (baseIdx + k) < 2 ^ w := by omega
      have hadjH_addr_lt : csrAddr + 2 * n + 1 + 2 * m + (baseIdx + k) < 2 ^ w := by omega
      have hcsr_val := hcsr_k.2 a ha_n k hk_csr
      rw [hq_csr] at hcsr_val
      have hw_mem_V : st.mem (csrAddr + 2 * n + 1 + (baseIdx + k)) = q.2.2 := by
        simpa [n, baseIdx, Nat.add_assoc] using hcsr_val.1
      have hw_mem_H : st.mem (csrAddr + 2 * n + 1 + 2 * m + (baseIdx + k)) =
          2 * q.1 + (if q.2.1 then 1 else 0) := by
        simpa [n, m, baseIdx, Nat.add_assoc] using hcsr_val.2
      have hqw_lt_w : q.2.2 < 2 ^ w := by omega
      have houtRw_addr_lt : outRAddr + q.2.2 < 2 ^ w := by omega
      have houtRw_val : st.mem (outRAddr + q.2.2) = if inR' q.2.2 then 1 else 0 := hOut q.2.2 hq_w_lt
      have hsk_step : skFn (k + 1) = removeEdgeStep cfg s.flow inR' (skFn k) q := by
        dsimp only [skFn]
        rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem hk_lt]
        rfl
      have hprops_k := hsk_props k hk
      have hprops_k1 := hsk_props (k + 1) hk_lt
      let st1 : State :=
        { st with
          regs := Function.update (Function.update st.regs prW q.2.2)
            prTmp1 (if inR' q.2.2 then 1 else 0) }
      have hst1_reg : ∀ r, r ≠ prW → r ≠ prTmp1 → st1.regs r = st.regs r := fun r h1 h2 => by
        simp [st1, Function.update_of_ne h2, Function.update_of_ne h1]
      have hst1_w : st1.regs prW = q.2.2 := by simp [st1]
      have hst1_1 : st1.regs prTmp1 = if inR' q.2.2 then 1 else 0 := by simp [st1]
      have hst1_J : st1.regs prJ = baseIdx + k :=
        (hst1_reg prJ (by decide) (by decide)).trans hrJ
      have hst1_S : st1.regs prStart = baseIdx :=
        (hst1_reg prStart (by decide) (by decide)).trans hrS
      have hst1_E : st1.regs prEnd = baseIdx + len :=
        (hst1_reg prEnd (by decide) (by decide)).trans hrE
      have hst1_AT : st1.regs prActTop = (skFn k).active.length :=
        (hst1_reg prActTop (by decide) (by decide)).trans hrAT1
      have hst1_PT : st1.regs prPeelTop = (skFn k).peelQ.length :=
        (hst1_reg prPeelTop (by decide) (by decide)).trans hrPT1
      have hst1_ptrs : PruneStepRegs cfg gAddr csrAddr inBAddr outRAddr workAddr st1 :=
        pruneStepRegs_of_agree hptrs_k fun r hle _ _ => hst1_reg r
          (by dsimp only [prCsrAdjH] at hle; dsimp only [prW]; omega)
          (by dsimp only [prCsrAdjH] at hle; dsimp only [prTmp1]; omega)
      have hqR_imp : inR' q.2.2 = true → s.inR q.2.2 = true := by
        intro hqR; dsimp only [inR'] at hqR; split_ifs at hqR; exact hqR
      have hex_bd : inR' q.2.2 = true → (removeEdgeStep cfg s.flow inR' (skFn k) q).ex q.2.2 < 2 ^ w := by
        intro hqR
        have hqR_s' : s'.inR q.2.2 = true := by
          rw [removeOneFromR_inR]; dsimp only [inR'] at hqR; exact hqR
        rw [← hsk_step]
        have hle := hprops_k1.2.2.2.2.2.1 q.2.2
        have hbd := hs'_ex_bd q.2.2 hqR_s'
        rw [hres_fields.2.1] at hle
        omega
      have hdr_old_lt : inR' q.2.2 = true → (skFn k).degR q.2.2 < 2 ^ w := by
        intro hqR
        have hqR_s : s.inR q.2.2 = true := hqR_imp hqR
        have hle1 := hprops_k.2.2.2.2.2.2 q.2.2
        have hdeg := hsw.degR_eq q.2.2 hqR_s
        have hdx : cfg.G.degIn (s.Rset cfg) q.2.2 ≤ cfg.G.deg q.2.2 := by
          have hsub : s.Rset cfg ⊆ cfg.G.verts := by
            have hx : cfg.X = cfg.G.verts := hcfgX
            rw [← hx]; unfold PruneState.Rset; exact Finset.filter_subset _ _
          simpa [Cited.Graph.deg, Cited.Graph.degIn, inside_verts_of_isValid hGv] using
            degIn_mono (G := cfg.G) hsub q.2.2
        have hsum := sum_deg_eq_two_mul_m hGv
        have hqV : q.2.2 ∈ cfg.G.verts := by
          have hx : cfg.X = cfg.G.verts := hcfgX
          rw [← hx]; exact hL_inR q (List.getElem_mem hk_lt) hqR
        have hsing := Finset.single_le_sum (f := cfg.G.deg) (fun _ _ => Nat.zero_le _) hqV
        omega
      have hnext_act_len : (removeEdgeStep cfg s.flow inR' (skFn k) q).active.length ≤ cfg.G.n := by
        rw [← hsk_step]
        exact nodup_length_le_range hprops_k1.2.1 (fun x hx => by
          have := hprops_k1.2.2.1 x hx; rw [hcfgX] at this; exact Finset.mem_range.mp this)
      have hnext_peel_len : (removeEdgeStep cfg s.flow inR' (skFn k) q).peelQ.length ≤ cfg.G.n := by
        rw [← hsk_step]
        exact nodup_length_le_range hprops_k1.2.2.2.1 (fun x hx => (hprops_k1.2.2.2.2.1 x hx).1)
      have hcond_branch := removeOneBranch_triple (p := p) inR' q baseIdx k st1 hcfgX hval hsw hw hcsr_w
        hst1_ptrs hq_idx_lt hq_w_lt hqR_imp hjk_2m hst1_J hst1_w hst1_1 hst1_AT hst1_PT
        hw_mem_H (hfe_k q.1 (by simpa [m, Cited.Graph.m] using hq_idx_lt))
        hex_bd hdr_old_lt hnext_act_len hnext_peel_len hEx hDr hIA hAS hPS
      refine ⟨145, ?_⟩
      intro stx ω2 hstx
      subst stx
      have hbody : ∃ o st' c_b,
          Runs w p ω2
            (seqStmts [
              .assign prW (.load (.bin .add (.reg prCsrAdjV) (.reg prJ))),
              .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prW))),
              removeOneBranchStmt,
              .assign prJ (.bin .add (.reg prJ) (.const 1))
            ]) st o st' c_b ∧
          normalPost (fun st' => Inv (k + 1) st') o st' ∧ c_b ≤ 145 := by
        dsimp only [seqStmts]
        refine runs_start_le (T := 145) ?_
        apply runs_seq_assign_le (v := q.2.2)
        · exact eval_load_add_regs hptrs_k.reg_adjV hrJ hadjV_addr_lt hw_mem_V hqw_lt_w
        apply runs_seq_assign_le (v := if inR' q.2.2 then 1 else 0)
        · have hr1_OR : Function.update st.regs prW q.2.2 prOutR = outRAddr := by
            simp [hptrs_k.reg_outR]
          have h1lt_if : (if inR' q.2.2 then 1 else 0) < 2 ^ w := by split_ifs <;> omega
          exact eval_load_add_regs hr1_OR (by simp) houtRw_addr_lt houtRw_val h1lt_if
        apply runs_seq_triple_le hcond_branch
        · rfl
        intro st2 ⟨hr2, hrAT2, hrPT2, hp2, hmf2, hEx2, hDr2, hIA2, hAS2, hPS2⟩
        rw [← hsk_step] at hrAT2 hrPT2 hEx2 hDr2 hIA2 hAS2 hPS2
        have hrS2 : st2.regs prStart = baseIdx :=
          (hr2 prStart (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hst1_S
        have hrE2 : st2.regs prEnd = baseIdx + len :=
          (hr2 prEnd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hst1_E
        have hrJ2 : st2.regs prJ = baseIdx + k :=
          (hr2 prJ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hst1_J
        have hpr2 : PreservedOutside2 st₀.mem st2.mem outRAddr (outRAddr + n)
            (wEx workAddr n m H) (wLvlNext workAddr n m H) := by
          dsimp only [st1] at hmf2
          exact preservedOutside2_trans hpr
            (preservedOutside2_of_memFrame2
              (memFrame_weaken hmf2 (by dsimp [wEx]; omega) le_rfl))
        have hOut2 : ∀ u < n, st2.mem (outRAddr + u) = if inR' u then 1 else 0 := by
          intro u hu
          have hmem2 : st2.mem (outRAddr + u) = st.mem (outRAddr + u) := by
            unfold pruneWorkSpace at hdisj_outR_work
            rcases hdisj_outR_work with hOW | hWO
            · exact hmf2 (outRAddr + u) (Or.inl (by dsimp [wEx]; omega))
            · exact hmf2 (outRAddr + u) (Or.inr (by dsimp [wHArr, wLvlNext]; omega))
          exact hmem2.trans (hOut u hu)
        apply runs_assign_le (v := baseIdx + (k + 1))
        · have hj1_w' : baseIdx + (k + 1) < 2 ^ w := by omega
          simp only [Expr.eval, hrJ2, h1lt, WordRAM.BinOp.eval, Nat.add_assoc, hj1_w', ↓reduceIte]
        · refine ⟨hk_lt, ?_, ?_, ?_, ?_, ?_, ?_, hp2.trans hp, hpr2, hOut2, hEx2, hDr2, hIA2, hAS2, hPS2⟩
          · intro r hS hE hJ hW hIdx hDir hRc h1 h2 h3 hAT hPT
            dsimp only; rw [Function.update_of_ne hJ]
            exact ((hr2 r hIdx hDir hRc h1 h2 hAT hPT).trans (hst1_reg r hW h1)).trans
              (hr r hS hE hJ hW hIdx hDir hRc h1 h2 h3 hAT hPT)
          · dsimp only; rw [Function.update_of_ne (by decide : prStart ≠ prJ)]; exact hrS2
          · dsimp only; rw [Function.update_of_ne (by decide : prEnd ≠ prJ)]; exact hrE2
          · simp
          · dsimp only; rw [Function.update_of_ne (by decide : prActTop ≠ prJ)]; exact hrAT2
          · dsimp only; rw [Function.update_of_ne (by decide : prPeelTop ≠ prJ)]; exact hrPT2
        · simp only [Expr.size]; omega
      obtain ⟨o, st_next, c_b, hrun_b, hpost_b, hc_b⟩ := hbody
      cases o with
      | returned _ => exact absurd hpost_b (by simp [normalPost])
      | normal =>
          exact ⟨.normal, st_next, c_b, hrun_b, ⟨k + 1, hpost_b, by omega, by omega⟩, hc_b⟩
  refine runs_start_le (T := 150 * (cfg.incEdges a).length + 30) ?_
  dsimp only [removeOneFromRStmt, seqStmts]
  apply runs_seq_store_le (x := outRAddr + a) (v := 0)
  · exact eval_add_regs hptrs.reg_outR hru houtRa_lt
  · simp [Expr.eval, h0lt]
  apply runs_seq_assign_le (v := baseIdx)
  · have hm1 : Function.update st₀.mem (outRAddr + a) 0 (csrAddr + a) = csrOff cfg.G a := by
      rw [Function.update_of_ne]
      · exact hstart_eq
      · rcases hdisj_csr_outR with h | h <;> omega
    exact eval_load_add_regs hptrs.reg_csr hru hcsr_a_lt hm1 hstart_lt_w
  apply runs_seq_assign_le (v := a + 1)
  · exact eval_add_reg_const hru h1lt ha1_lt
  apply runs_seq_assign_le (v := baseIdx + len)
  · have hcsr2 : Function.update (Function.update st₀.regs prStart baseIdx) prTmp1 (a + 1) prCsr = csrAddr := by
      simp [hptrs.reg_csr]
    have hm1 : Function.update st₀.mem (outRAddr + a) 0 (csrAddr + (a + 1)) = baseIdx + len := by
      rw [Function.update_of_ne, hend_eq, hlen_eq]
      rcases hdisj_csr_outR with h | h <;> omega
    exact eval_load_add_regs hcsr2 (by simp) hcsr_a1_lt hm1 (by omega)
  apply runs_seq_assign_le (v := baseIdx)
  · exact eval_reg (by simp) hstart_lt_w
  apply runs_triple_le hloop
  · have hs0_eq : skFn 0 = sInit := by simp [skFn]
    refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, rfl,
      preservedOutside2_update_left (Nat.le_add_right _ _) (by omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hS hE hJ _ _ _ _ h1 _ _ _ _
      dsimp only
      rw [Function.update_of_ne hJ, Function.update_of_ne hE,
        Function.update_of_ne h1, Function.update_of_ne hS]
    · dsimp only
      rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_self]
    · dsimp only
      rw [Function.update_of_ne (by decide), Function.update_self]
    · dsimp only; rw [Function.update_self]; simp
    · dsimp only
      rw [hs0_eq, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hrAT]
    · dsimp only
      rw [hs0_eq, Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide), hrPT]
    · intro u hu
      dsimp only
      by_cases hua : u = a
      · subst hua; simp [inR', Function.update_self]
      · rw [Function.update_of_ne (by omega), houtR u hu]; simp [inR', hua]
    · intro u hu
      dsimp only
      rw [hs0_eq, Function.update_of_ne (by
        unfold pruneWorkSpace at hdisj_outR_work
        dsimp only [n, m, H] at *
        rcases hdisj_outR_work with h | h <;> dsimp [wEx] at h ⊢ <;> omega)]
      exact hex u hu
    · intro u hu
      dsimp only
      rw [hs0_eq, Function.update_of_ne (by
        unfold pruneWorkSpace at hdisj_outR_work
        dsimp only [n, m, H] at *
        rcases hdisj_outR_work with h | h <;> dsimp [wDegR] at h ⊢ <;> omega)]
      exact hdr u hu
    · intro u hu
      dsimp only
      rw [hs0_eq, Function.update_of_ne (by
        unfold pruneWorkSpace at hdisj_outR_work
        dsimp only [n, m, H] at *
        rcases hdisj_outR_work with h | h <;> dsimp [wInAct] at h ⊢ <;> omega)]
      exact hia u hu
    · intro i hi
      dsimp only
      rw [hs0_eq] at hi ⊢
      dsimp only [sInit] at hi
      rw [Function.update_of_ne (by
        have hlt_n := hsw.active_nodup |> fun hnd => nodup_length_le_range hnd fun x hx => by
          have := hsw.active_sub x hx; rw [hcfgX] at this; exact Finset.mem_range.mp this
        unfold pruneWorkSpace at hdisj_outR_work
        dsimp only [n, m, H] at *
        rcases hdisj_outR_work with h | h <;> dsimp [wActStk] at h ⊢ <;> omega)]
      exact has i hi
    · intro i hi
      dsimp only
      rw [hs0_eq] at hi ⊢
      dsimp only [sInit] at hi
      rw [Function.update_of_ne (by
        have hlt_n := nodup_length_le_range hpeel_nd (fun x hx => (hpeel_lt x hx).1)
        unfold pruneWorkSpace at hdisj_outR_work
        dsimp only [n, m, H] at *
        rcases hdisj_outR_work with h | h <;> dsimp [wPeelStk] at h ⊢ <;> omega)]
      exact hps i hi
  · intro o stFin hFin
    cases o with
    | returned _ => exact absurd hFin (by simp [normalPost])
    | normal =>
        have hInvFin := hFin
        have hptrs_fin := hInv_ptrs len stFin hInvFin
        rcases hFin with ⟨_, hr, _, _, _, hrAT, hrPT, hp, hpr, hOut, hEx, hDr, hIA, hAS, hPS⟩
        have hsk_len : skFn len = sRes := by
          dsimp only [skFn, sRes, len]; rw [List.take_length]
        rw [hsk_len] at hrAT hrPT hEx hDr hIA hAS hPS
        have hrU_fin : stFin.regs prU = a :=
          (hr prU (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hru
        have hinR_eq : s'.inR = inR' := by
          ext x; rw [removeOneFromR_inR]
        refine ⟨hr, hptrs_fin, hrU_fin, ?_, hrPT, hp, hpr, ?_, ?_, ?_, ?_, ?_, hPS⟩
        · rw [hrAT, hres_fields.2.2.2.1]
        · intro u hu; simp [hOut u hu, hinR_eq]
        · intro u hu; rw [hEx u hu, hres_fields.2.1]
        · intro u hu; rw [hDr u hu, hres_fields.2.2.1]
        · intro u hu; rw [hIA u hu, hres_fields.2.2.2.2]
        · intro i hi; rw [← hres_fields.2.2.2.1] at hi ⊢; exact hAS i hi
  · dsimp only [len]; simp only [Expr.size]; omega


end MinCostFlow.Expander
