module

public import MinCostFlow.Expander.PathDSProg.SubdivProg

/-!
# Deterministic Word-RAM Fallback Mask and Walk-Projection Subroutines

Implements:
1. `initMasksStmt`: initializes `outR[0..n_s-1] := 1` and `eMask[0..m_s-1] := 1`.
2. `fbUpdateBStmt`: prepares `inB` and marks deleted edge `e` (`eMask[3*e + 1] := 0`).
3. `emitNewVhatFromOutRStmt`: emits newly pruned original vertices (`outR[v] = 0 ∧ inVhat[v] = 0`).
4. `projSeqToWalkStmt`: shared projection from subdivision vertex sequence `P_s` to
   `WalkAt mem' dst ⟨projPath n P_s, projEdges n P_s⟩`.
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. `initMasksStmt` (`outR := 1`, `eMask := 1`) -/

/-- Sets `[outRAddr, outRAddr + n_s)` (`r20, r21`) and `[eMaskAddr, eMaskAddr + m_s)` (`r22, r23`)
all to `1`. -/
def initMasksStmt : Stmt :=
  seqStmts
    [ forRange 24 (.const 0) (.reg 21) (.store (.bin .add (.reg 20) (.reg 24)) (.const 1))
    , forRange 24 (.const 0) (.reg 23) (.store (.bin .add (.reg 22) (.reg 24)) (.const 1)) ]

lemma initMasksStmt_noRand : initMasksStmt.NoRand := by
  simp [initMasksStmt, seqStmts, forRange, forUp, Stmt.NoRand]

theorem initMasksStmt_triple {w outRAddr n_s eMaskAddr m_s : ℕ} {p : Program}
    (st₀ : State)
    (hr20 : st₀.regs 20 = outRAddr) (hr21 : st₀.regs 21 = n_s)
    (hr22 : st₀.regs 22 = eMaskAddr) (hr23 : st₀.regs 23 = m_s)
    (hdisj : outRAddr + n_s ≤ eMaskAddr ∨ eMaskAddr + m_s ≤ outRAddr)
    (hout_w : outRAddr + n_s < 2 ^ w) (he_w : eMaskAddr + m_s < 2 ^ w) (hw2 : 1 < 2 ^ w) :
    Triple w p (fun st => st = st₀) initMasksStmt
      (normalPost fun st' =>
        (∀ v < n_s, st'.mem (outRAddr + v) = 1) ∧
        (∀ e < m_s, st'.mem (eMaskAddr + e) = 1) ∧
        PreservedOutside2 st₀.mem st'.mem outRAddr (outRAddr + n_s) eMaskAddr (eMaskAddr + m_s) ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 25 * (n_s + m_s) + 25) := by
  have hn_w : n_s < 2 ^ w := by omega
  have hm_w : m_s < 2 ^ w := by omega
  let Pre1 : State → Prop := fun st => st = st₀
  let Inv1 : ℕ → State → Prop := fun k st =>
    k ≤ n_s ∧ st.regs 20 = outRAddr ∧ st.regs 21 = n_s ∧ st.regs 22 = eMaskAddr ∧ st.regs 23 = m_s ∧
    st.regs 24 = k ∧ (∀ v < k, st.mem (outRAddr + v) = 1) ∧
    MemFrame st₀.mem st.mem outRAddr (outRAddr + n_s) ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  have hloop1 := Triple.forRange_const (p := p) (r := 24) (lo := .const 0) (hi := .reg 21)
    (body := .store (.bin .add (.reg 20) (.reg 24)) (.const 1)) (P := Pre1) (Inv := Inv1)
    10 0 n_s (Nat.zero_le n_s) hw2 (fun _ => hn_w)
    (fun st hst => by
      change st = st₀ at hst; rw [hst]
      refine ⟨by eval_expr, Nat.zero_le _, by simp [hr20], by simp [hr21], by simp [hr22],
        by simp [hr23], by simp, fun _ hv => absurd hv (Nat.not_lt_zero _),
        memFrame_refl _ _ _, fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)], rfl⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.1)
    (fun _ _ _ _ hI => by have := hI.2.2.1; eval_expr)
    (fun k _ hklt st ω ⟨_, h20, h21, h22, h23, h24, hm1, hfr, hlt20, hpos⟩ => by
      refine runs_start_le ?_
      wram_run
      · refine ⟨⟨hklt, by simp [h20], by simp [h21], by simp [h22], by simp [h23], by simp,
          fun v hv => ?_, ?_, fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩, h24⟩
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv' | rfl
          · rw [Function.update_of_ne (by omega)]; exact hm1 v hv'
          · rw [Function.update_self]
        · dsimp only
          exact memFrame_trans hfr (memFrame_update (by omega) (by omega))
      · wram_cost)
  let Inv2 : ℕ → State → Prop := fun k st =>
    k ≤ m_s ∧ st.regs 22 = eMaskAddr ∧ st.regs 23 = m_s ∧ st.regs 24 = k ∧
    (∀ v < n_s, st.mem (outRAddr + v) = 1) ∧ (∀ e < k, st.mem (eMaskAddr + e) = 1) ∧
    PreservedOutside2 st₀.mem st.mem outRAddr (outRAddr + n_s) eMaskAddr (eMaskAddr + m_s) ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  have hloop2 := Triple.forRange_const (p := p) (r := 24) (lo := .const 0) (hi := .reg 23)
    (body := .store (.bin .add (.reg 22) (.reg 24)) (.const 1)) (P := Inv1 n_s) (Inv := Inv2)
    10 0 m_s (Nat.zero_le m_s) hw2 (fun _ => hm_w)
    (fun st ⟨_, _, _, h22, h23, _, hm1, hfr, hlt20, hpos⟩ => ⟨by eval_expr,
      Nat.zero_le _, by simp [h22], by simp [h23], by simp, hm1,
      fun _ he => absurd he (Nat.not_lt_zero _), fun x hx _ => hfr x hx,
      fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩)
    (fun _ _ _ _ hI => hI.2.2.2.1)
    (fun _ _ _ _ hI => by have := hI.2.2.1; eval_expr)
    (fun k _ hklt st ω ⟨_, h22, h23, h24, hm1, hm2, hpo, hlt20, hpos⟩ => by
      refine runs_start_le ?_
      wram_run
      · refine ⟨⟨hklt, by simp [h22], by simp [h23], by simp, fun v hv => ?_, fun e he => ?_,
          ?_, fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩, h24⟩
        · dsimp only
          rw [Function.update_of_ne (by omega)]; exact hm1 v hv
        · dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp he with he' | rfl
          · rw [Function.update_of_ne (by omega)]; exact hm2 e he'
          · rw [Function.update_self]
        · dsimp only
          exact preservedOutside2_trans hpo (preservedOutside2_update_right (by omega) (by omega))
      · wram_cost)
  refine (Triple.seq_normal hloop1 hloop2 (T := fun _ => 25 * (n_s + m_s) + 25)
    (fun _ _ _ _ => by simp [Expr.size]; omega)).conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st' h
  cases o with
  | returned _ => exact False.elim h
  | normal =>
    rcases h with ⟨_, _, _, _, hm1, hm2, hpo, hlt20, hpos⟩
    exact ⟨hm1, hm2, hpo, hlt20, hpos⟩

/-! ## 2. `fbUpdateBStmt` & `emitNewVhatFromOutRStmt` (Fallback Deletion Helpers) -/

def fbUpdateBBody : Stmt :=
  seqStmts
    [ .assign 27 (.load (.bin .add (.reg 20) (.reg 26)))
    , .cond (.bin .eq (.reg 27) (.const 0))
        (.store (.bin .add (.reg 21) (.reg 26)) (.const 1))
        (.store (.bin .add (.reg 21) (.reg 26)) (.const 0)) ]

def fbUpdateBTail : Stmt :=
  seqStmts
    [ .assign 28 (.bin .add (.reg 24) (.bin .mul (.const 2) (.reg 23)))
    , .store (.bin .add (.reg 21) (.reg 28)) (.const 1)
    , .store (.bin .add (.reg 21) (.bin .add (.reg 28) (.const 1))) (.const 1)
    , .store (.bin .add (.reg 22) (.bin .add (.bin .mul (.const 3) (.reg 23)) (.const 1))) (.const 0) ]

/-- Sets `inB[v] := if outR[v] = 0 then 1 else 0` (`r21, r20, r25`), sets endpoints
`inB[n + 2*e] := 1`, `inB[n + 2*e + 1] := 1` (`r24, r23`), and sets `eMask[3*e + 1] := 0` (`r22`). -/
def fbUpdateBStmt : Stmt :=
  forRange 26 (.const 0) (.reg 25) fbUpdateBBody ;; fbUpdateBTail

lemma fbUpdateBStmt_noRand : fbUpdateBStmt.NoRand := by
  simp [fbUpdateBStmt, fbUpdateBBody, fbUpdateBTail, seqStmts, forRange, forUp, Stmt.NoRand]

theorem fbUpdateBStmt_triple {w outRAddr inBAddr eMaskAddr e n n_s m_s : ℕ} {p : Program}
    (st₀ : State) (R : Finset ℕ) (del : Finset ℕ)
    (hr20 : st₀.regs 20 = outRAddr) (hr21 : st₀.regs 21 = inBAddr)
    (hr22 : st₀.regs 22 = eMaskAddr) (hr23 : st₀.regs 23 = e)
    (hr24 : st₀.regs 24 = n) (hr25 : st₀.regs 25 = n_s)
    (he_lt : n + 2 * e + 1 < n_s) (hms_eq : 3 * e + 1 < m_s)
    (houtR : ∀ v < n_s, st₀.mem (outRAddr + v) = if v ∈ R then 1 else 0)
    (heMask : ∀ j < m_s, st₀.mem (eMaskAddr + j) = if ∃ d ∈ del, j = 3 * d + 1 then 0 else 1)
    (hdisj_ob : outRAddr + n_s ≤ inBAddr ∨ inBAddr + n_s ≤ outRAddr)
    (hdisj_oe : outRAddr + n_s ≤ eMaskAddr ∨ eMaskAddr + m_s ≤ outRAddr)
    (hdisj_be : inBAddr + n_s ≤ eMaskAddr ∨ eMaskAddr + m_s ≤ inBAddr)
    (hout_w : outRAddr + n_s < 2 ^ w) (hinB_w : inBAddr + n_s < 2 ^ w)
    (heM_w : eMaskAddr + m_s < 2 ^ w) (hw4 : 4 ≤ 2 ^ w) :
    Triple w p (fun st => st = st₀) fbUpdateBStmt
      (normalPost fun st' =>
        (∀ v < n_s, (st'.mem (inBAddr + v) ≠ 0 ↔
          v ∉ R ∨ v = n + 2 * e ∨ v = n + 2 * e + 1)) ∧
        (∀ j < m_s, st'.mem (eMaskAddr + j) =
          if ∃ d ∈ insert e del, j = 3 * d + 1 then 0 else 1) ∧
        PreservedOutside2 st₀.mem st'.mem inBAddr (inBAddr + n_s) eMaskAddr (eMaskAddr + m_s) ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 45 * n_s + 55) := by
  have hw2 : 1 < 2 ^ w := by omega
  have hns_w : n_s < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun k st =>
    k ≤ n_s ∧ st.regs 20 = outRAddr ∧ st.regs 21 = inBAddr ∧ st.regs 22 = eMaskAddr ∧
    st.regs 23 = e ∧ st.regs 24 = n ∧ st.regs 25 = n_s ∧ st.regs 26 = k ∧
    (∀ v < k, st.mem (inBAddr + v) = if v ∈ R then 0 else 1) ∧
    MemFrame st₀.mem st.mem inBAddr (inBAddr + n_s) ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  have hloop := Triple.forRange_const (p := p) (r := 26) (lo := .const 0) (hi := .reg 25)
    (body := fbUpdateBBody) (P := fun st => st = st₀) (Inv := Inv) 20 0 n_s (Nat.zero_le n_s) hw2 (fun _ => hns_w)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, Nat.zero_le _, by simp [hr20], by simp [hr21], by simp [hr22],
        by simp [hr23], by simp [hr24], by simp [hr25], by simp,
        fun _ hv => absurd hv (Nat.not_lt_zero _), memFrame_refl _ _ _,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)], rfl⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => by have := hI.2.2.2.2.2.2.1; eval_expr)
    (fun k _ hklt st ω ⟨_, h20, h21, h22, h23, h24, h25, h26, hinB, hfr, hlt20, hpos⟩ => by
      have hout_k : st.mem (outRAddr + k) = if k ∈ R then 1 else 0 := by
        rw [hfr _ (by omega)]; exact houtR k hklt
      have hout_kw : st.mem (outRAddr + k) < 2 ^ w := by rw [hout_k]; split_ifs <;> omega
      refine runs_start_le ?_
      dsimp only [fbUpdateBBody, seqStmts]
      by_cases hkR : k ∈ R
      · have hout_k1 : st.mem (outRAddr + k) = 1 := by simp [hout_k, hkR]
        wram_step; simp only [hout_k1]
        wram_run
        · refine ⟨⟨hklt, by simp [h20], by simp [h21], by simp [h22], by simp [h23],
            by simp [h24], by simp [h25], by simp, fun v hv => ?_, ?_,
            fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
            hpos⟩, by simp [h26]⟩
          · (try dsimp only); (try rw [h21]); (try rw [h26])
            rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv' | rfl
            · rw [Function.update_of_ne (by omega)]; exact hinB v hv'
            · rw [Function.update_self]; simp [hkR]
          · (try dsimp only); (try rw [h21]); (try rw [h26])
            exact memFrame_trans hfr (memFrame_update (by omega) (by omega))
        · wram_cost
      · have hout_k0 : st.mem (outRAddr + k) = 0 := by simp [hout_k, hkR]
        wram_step; simp only [hout_k0]
        wram_step
        · wram_run
          · refine ⟨⟨hklt, by simp [h20], by simp [h21], by simp [h22], by simp [h23],
              by simp [h24], by simp [h25], by simp, fun v hv => ?_, ?_,
              fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
              hpos⟩, by simp [h26]⟩
            · (try dsimp only); (try rw [h21]); (try rw [h26])
              rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv' | rfl
              · rw [Function.update_of_ne (by omega)]; exact hinB v hv'
              · rw [Function.update_self]; simp [hkR]
            · (try dsimp only); (try rw [h21]); (try rw [h26])
              exact memFrame_trans hfr (memFrame_update (by omega) (by omega))
          · wram_cost)
  have htail : Triple w p (Inv n_s) fbUpdateBTail
      (normalPost fun st' =>
        (∀ v < n_s, (st'.mem (inBAddr + v) ≠ 0 ↔
          v ∉ R ∨ v = n + 2 * e ∨ v = n + 2 * e + 1)) ∧
        (∀ j < m_s, st'.mem (eMaskAddr + j) =
          if ∃ d ∈ insert e del, j = 3 * d + 1 then 0 else 1) ∧
        PreservedOutside2 st₀.mem st'.mem inBAddr (inBAddr + n_s) eMaskAddr (eMaskAddr + m_s) ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 40) := by
    wram_enter
    rcases hpre with ⟨_, _, h21, h22, h23, h24, _, _, hinB, hfr, hlt20, hpos⟩
    dsimp only [fbUpdateBTail, seqStmts]
    wram_run
    · refine ⟨fun v hv => ?_, fun j hj => ?_, ?_,
        fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
        hpos⟩
      · (try dsimp only); (try rw [h21]); (try rw [h22]); (try rw [h23])
        by_cases hv1 : v = n + 2 * e + 1
        · subst hv1; rw [Function.update_of_ne (by omega), Function.update_self]; simp
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          by_cases hv0 : v = n + 2 * e
          · subst hv0; rw [Function.update_self]; simp
          · rw [Function.update_of_ne (by omega), hinB v hv]
            simp [hv0, hv1]
      · (try dsimp only); (try rw [h21]); (try rw [h22]); (try rw [h23])
        by_cases hje : j = 3 * e + 1
        · subst hje; rw [Function.update_self]; simp
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), hfr _ (by omega), heMask j hj]
          simp [hje, Finset.mem_insert]
      · (try dsimp only); (try rw [h21]); (try rw [h22]); (try rw [h23])
        exact preservedOutside2_trans (fun x hx _ => hfr x hx)
          (preservedOutside2_trans (preservedOutside2_update_left (by omega) (by omega))
            (preservedOutside2_trans (preservedOutside2_update_left (by omega) (by omega))
              (preservedOutside2_update_right (by omega) (by omega))))
    · wram_cost
  exact (Triple.seq_normal hloop htail (T := fun _ => 45 * n_s + 55)
    (fun _ _ _ _ => by simp [Expr.size]; omega)).conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_rfl)

def emitNewVhatBody : Stmt :=
  seqStmts
    [ .assign 26 (.load (.bin .add (.reg 22) (.reg 25)))
    , .cond (.bin .eq (.reg 26) (.const 0))
        (seqStmts
          [ .assign 27 (.load (.bin .add (.reg 21) (.reg 25)))
          , .cond (.bin .eq (.reg 27) (.const 0))
              (seqStmts
                [ .store (.bin .add (.reg 21) (.reg 25)) (.const 1)
                , .store (.bin .add (.bin .add (.reg 20) (.const 1)) (.reg 24)) (.reg 25)
                , .assign 24 (.bin .add (.reg 24) (.const 1)) ])
              .nop ])
        .nop ]

/-- Scans `v = 0 .. n - 1` (`r23`): if `outR[v] = 0` (`r22`) and `inVhat[v] = 0` (`r21`),
marks `inVhat[v] := 1` and emits `v` into `dst` (`r20`) as `SeqAt`. -/
def emitNewVhatFromOutRStmt : Stmt :=
  (.assign 24 (.const 0) ;; forRange 25 (.const 0) (.reg 23) emitNewVhatBody) ;;
  (.store (.reg 20) (.reg 24) ;; .assign 24 (.bin .add (.bin .add (.reg 20) (.const 1)) (.reg 24)))

lemma emitNewVhatFromOutRStmt_noRand : emitNewVhatFromOutRStmt.NoRand := by
  simp [emitNewVhatFromOutRStmt, emitNewVhatBody, seqStmts, forRange, forUp, Stmt.NoRand]

theorem emitNewVhatFromOutRStmt_triple {w dst inVhatAddr outRAddr n : ℕ} {p : Program}
    (st₀ : State) (Vhat R : Finset ℕ)
    (hr20 : st₀.regs 20 = dst) (hr21 : st₀.regs 21 = inVhatAddr)
    (hr22 : st₀.regs 22 = outRAddr) (hr23 : st₀.regs 23 = n)
    (hinVhat : ∀ v < n, st₀.mem (inVhatAddr + v) = if v ∈ Vhat then 1 else 0)
    (houtR : ∀ v < n, st₀.mem (outRAddr + v) = if v ∈ R then 1 else 0)
    (hdisj_di : dst + 1 + n ≤ inVhatAddr ∨ inVhatAddr + n ≤ dst)
    (hdisj_do : dst + 1 + n ≤ outRAddr ∨ outRAddr + n ≤ dst)
    (hdisj_io : inVhatAddr + n ≤ outRAddr ∨ outRAddr + n ≤ inVhatAddr)
    (hdst_w : dst + 1 + n < 2 ^ w) (hin_w : inVhatAddr + n < 2 ^ w)
    (hout_w : outRAddr + n < 2 ^ w) (hw4 : 4 ≤ 2 ^ w) :
    Triple w p (fun st => st = st₀) emitNewVhatFromOutRStmt
      (normalPost fun st' =>
        let L := (List.range n).filter fun v => decide (v ∉ R ∧ v ∉ Vhat)
        SeqAt st'.mem dst L ∧ L.Nodup ∧ L.length ≤ n ∧
        L.toFinset = (Finset.range n \ R) \ Vhat ∧
        (∀ v < n, st'.mem (inVhatAddr + v) =
          if v ∈ Vhat ∪ (Finset.range n \ R) then 1 else 0) ∧
        PreservedOutside2 st₀.mem st'.mem dst (dst + 1 + n) inVhatAddr (inVhatAddr + n) ∧
        st'.regs 24 = dst + 1 + L.length ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 65 * n + 35) := by
  have hw2 : 1 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  let PreL : State → Prop := fun st =>
    st.regs 20 = dst ∧ st.regs 21 = inVhatAddr ∧ st.regs 22 = outRAddr ∧ st.regs 23 = n ∧
    st.regs 24 = 0 ∧ st.mem = st₀.mem ∧ (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  let Inv : ℕ → State → Prop := fun k st =>
    let curL := (List.range k).filter fun v => decide (v ∉ R ∧ v ∉ Vhat)
    k ≤ n ∧ st.regs 20 = dst ∧ st.regs 21 = inVhatAddr ∧ st.regs 22 = outRAddr ∧
    st.regs 23 = n ∧ st.regs 24 = curL.length ∧ st.regs 25 = k ∧
    PreservedOutside2 st₀.mem st.mem dst (dst + 1 + n) inVhatAddr (inVhatAddr + n) ∧
    ListAt st.mem (dst + 1) curL ∧
    (∀ v < n, st.mem (inVhatAddr + v) =
      if v ∈ Vhat ∪ (Finset.range k \ R) then 1 else 0) ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  have hsetup : Triple w p (fun st => st = st₀) (.assign 24 (.const 0)) (normalPost PreL) (fun _ => 4) := by
    wram_enter; subst hpre; wram_run
    · exact ⟨by simp [hr20], by simp [hr21], by simp [hr22], by simp [hr23], by simp, rfl,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)], rfl⟩
    · wram_cost
  have hloop := Triple.forRange_const (p := p) (r := 25) (lo := .const 0) (hi := .reg 23)
    (body := emitNewVhatBody) (P := PreL) (Inv := Inv) 40 0 n (Nat.zero_le n) hw2 (fun _ => hn_w)
    (fun st ⟨h20, h21, h22, h23, h24, hm, hlt20, hpos⟩ => ⟨by eval_expr, by
      refine ⟨Nat.zero_le _, by simp [h20], by simp [h21], by simp [h22], by simp [h23],
        by simp [h24], by simp, hm ▸ preservedOutside2_refl _ _ _ _ _, fun _ hk => by simp at hk,
        fun v hv => by simpa [hm] using hinVhat v hv,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => by have := hI.2.2.2.2.1; eval_expr)
    (fun k _ hklt st ω ⟨_, h20, h21, h22, h23, h24, h25, hpo, hlist, hinV, hlt20, hpos⟩ => by
      set curL := (List.range k).filter fun v => decide (v ∉ R ∧ v ∉ Vhat)
      have hcur_le : curL.length ≤ k := by
        have hlen := List.length_filter_le (fun v => decide (v ∉ R ∧ v ∉ Vhat)) (List.range k)
        simpa [curL, List.length_range] using hlen
      have hout_k : st.mem (outRAddr + k) = if k ∈ R then 1 else 0 := by
        rw [hpo _ (by omega) (by omega)]; exact houtR k hklt
      have hout_kw : st.mem (outRAddr + k) < 2 ^ w := by rw [hout_k]; split_ifs <;> omega
      have hin_k : st.mem (inVhatAddr + k) = if k ∈ Vhat then 1 else 0 := by
        rw [hinV k hklt]; simp [Finset.mem_range]
      have hin_kw : st.mem (inVhatAddr + k) < 2 ^ w := by rw [hin_k]; split_ifs <;> omega
      refine runs_start_le ?_
      dsimp only [emitNewVhatBody, seqStmts]
      by_cases hkR : k ∈ R
      · have hout_k1 : st.mem (outRAddr + k) = 1 := by simp [hout_k, hkR]
        wram_step; simp only [hout_k1]
        wram_run
        · have hcur' : (List.range (k + 1)).filter (fun v => decide (v ∉ R ∧ v ∉ Vhat)) = curL := by
            rw [List.range_succ, List.filter_append]; simp [hkR, curL]
          refine ⟨⟨hklt, by simp [h20], by simp [h21], by simp [h22], by simp [h23],
            by simp only [hcur']; simp [h24],
            by simp, hpo, by simpa only [hcur'] using hlist, fun v hv => ?_,
            fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
            hpos⟩, by simp [h25]⟩
          rw [hinV v hv]
          by_cases hvk : v = k
          · subst hvk; simp [hkR]
          · simp [Finset.mem_range, show v < k + 1 ↔ v < k by omega]
        · wram_cost
      · have hout_k0 : st.mem (outRAddr + k) = 0 := by simp [hout_k, hkR]
        wram_step; simp only [hout_k0]
        wram_step
        · by_cases hkV : k ∈ Vhat
          · have hin_k1 : st.mem (inVhatAddr + k) = 1 := by simp [hin_k, hkV]
            wram_step; simp only [h21, h25, hin_k1]
            wram_run
            · have hcur' : (List.range (k + 1)).filter (fun v => decide (v ∉ R ∧ v ∉ Vhat)) = curL := by
                rw [List.range_succ, List.filter_append]; simp [hkR, hkV, curL]
              refine ⟨⟨hklt, by simp [h20], by simp [h21], by simp [h22], by simp [h23],
                by simp only [hcur']; simp [h24],
                by simp, hpo, by simpa only [hcur'] using hlist, fun v hv => ?_,
                fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
                hpos⟩, by simp [h25]⟩
              rw [hinV v hv]
              by_cases hvk : v = k
              · subst hvk; simp [hkV]
              · simp [Finset.mem_range, show v < k + 1 ↔ v < k by omega]
            · wram_cost
          · have hin_k0 : st.mem (inVhatAddr + k) = 0 := by simp [hin_k, hkV]
            have hcur' : (List.range (k + 1)).filter (fun v => decide (v ∉ R ∧ v ∉ Vhat)) = curL ++ [k] := by
              rw [List.range_succ, List.filter_append]; simp [hkR, hkV, curL]
            wram_step; simp only [h21, h25, hin_k0]
            wram_run
            · refine ⟨⟨hklt, by simp [h20], by simp [h21], by simp [h22], by simp [h23],
                by dsimp only; simp only [hcur', List.length_append, List.length_cons, List.length_nil]
                   rw [Function.update_of_ne (by decide), Function.update_self, h24],
                by simp, ?_, ?_, fun v hv => ?_,
                fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
                hpos⟩, by simp [h25]⟩
              · (try dsimp only); (try rw [h20]); (try rw [h21]); (try rw [h24]); (try rw [h25])
                exact preservedOutside2_trans hpo
                  (preservedOutside2_trans (preservedOutside2_update_right (by omega) (by omega))
                    (preservedOutside2_update_left (by omega) (by omega)))
              · simp only [hcur']
                refine listAt_append_singleton hlist (fun j hj => ?_) ?_
                · (try rw [h20]); (try rw [h21]); (try rw [h24]); (try rw [h25])
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                · (try rw [h20]); (try rw [h24]); (try rw [h25])
                  rw [Function.update_self]
              · by_cases hvk : v = k
                · subst hvk; (try dsimp only); (try rw [h20]); (try rw [h21]); (try rw [h24]); (try rw [h25])
                  rw [Function.update_of_ne (by omega), Function.update_self]; simp [hkR]
                · (try dsimp only); (try rw [h20]); (try rw [h21]); (try rw [h24]); (try rw [h25])
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hinV v hv]
                  simp [Finset.mem_range, show v < k + 1 ↔ v < k by omega]
            · wram_cost)
  have hmid : Triple w p (fun st => st = st₀)
      (.assign 24 (.const 0) ;; forRange 25 (.const 0) (.reg 23) emitNewVhatBody)
      (normalPost (Inv n)) (fun _ => 65 * n + 15) :=
    (Triple.seq_normal hsetup hloop (T := fun _ => 65 * n + 15)
      (fun _ _ _ _ => by simp [Expr.size]; omega)).conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_rfl)
  have htail : Triple w p (Inv n)
      (.store (.reg 20) (.reg 24) ;; .assign 24 (.bin .add (.bin .add (.reg 20) (.const 1)) (.reg 24)))
      (normalPost fun st' =>
        let L := (List.range n).filter fun v => decide (v ∉ R ∧ v ∉ Vhat)
        SeqAt st'.mem dst L ∧ L.Nodup ∧ L.length ≤ n ∧
        L.toFinset = (Finset.range n \ R) \ Vhat ∧
        (∀ v < n, st'.mem (inVhatAddr + v) =
          if v ∈ Vhat ∪ (Finset.range n \ R) then 1 else 0) ∧
        PreservedOutside2 st₀.mem st'.mem dst (dst + 1 + n) inVhatAddr (inVhatAddr + n) ∧
        st'.regs 24 = dst + 1 + L.length ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 15) := by
    wram_enter
    rcases hpre with ⟨_, h20, h21, _, _, h24, _, hpo, hlist, hinV, hlt20, hpos⟩
    have hlen_le : ((List.range n).filter fun v => decide (v ∉ R ∧ v ∉ Vhat)).length ≤ n := by
      have h := List.length_filter_le (fun v => decide (v ∉ R ∧ v ∉ Vhat)) (List.range n)
      simpa only [List.length_range] using h
    wram_run
    · refine ⟨⟨by simp, fun k hk => ?_⟩, List.nodup_range.filter _, hlen_le, ?_,
        fun v hv => ?_, ?_, by simp,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩
      · dsimp only
        rw [Function.update_of_ne (by omega)]; exact hlist k hk
      · ext x; simp [Finset.mem_sdiff, Finset.mem_range]; tauto
      · dsimp only
        rw [Function.update_of_ne (by omega)]; exact hinV v hv
      · dsimp only
        exact preservedOutside2_trans hpo (preservedOutside2_update_left (by omega) (by omega))
    · wram_cost
  exact (Triple.seq_normal hmid htail (T := fun _ => 65 * n + 35)
    (fun _ _ _ _ => by omega)).conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_rfl)

/-! ## 3. `projSeqToWalkStmt` (Shared `[CS21]` / Fallback Path Projection) -/

def projSeqSetupStmt : Stmt :=
  seqStmts
    [ .assign 24 (.load (.reg 20))
    , .assign 25 (.bin .div (.bin .sub (.reg 24) (.const 1)) (.const 3))
    , .assign 26 (.load (.bin .add (.reg 20) (.const 1)))
    , .store (.reg 21) (.bin .add (.reg 25) (.const 1))
    , .store (.bin .add (.reg 21) (.const 1)) (.reg 26)
    , .store (.bin .add (.reg 21) (.bin .add (.reg 25) (.const 2))) (.reg 25) ]

def projSeqBodyStmt : Stmt :=
  seqStmts
    [ .assign 27 (.load (.bin .add (.bin .add (.reg 20) (.const 2)) (.bin .mul (.const 3) (.reg 26))))
    , .assign 28 (.load (.bin .add (.bin .add (.reg 20) (.const 4)) (.bin .mul (.const 3) (.reg 26))))
    , .store (.bin .add (.bin .add (.reg 21) (.const 2)) (.reg 26)) (.reg 28)
    , .store (.bin .add (.bin .add (.reg 21) (.bin .add (.reg 25) (.const 3))) (.reg 26))
        (.bin .div (.bin .sub (.reg 27) (.reg 22)) (.const 2)) ]

/-- Projects a subdivision path vertex list `P_s` (`mem[src] = P_s.length`, `ListAt mem (src + 1) P_s`)
into `WalkAt mem' dst ⟨projPath n P_s, projEdges n P_s⟩`, returning `dst + 2 * k + 3` in `r23`
where `k = (P_s.length - 1) / 3`. Inputs: `r20 = src`, `r21 = dst`, `r22 = n`. -/
def projSeqToWalkStmt : Stmt :=
  (projSeqSetupStmt ;; forRange 26 (.const 0) (.reg 25) projSeqBodyStmt) ;;
  .assign 23 (.bin .add (.bin .add (.reg 21) (.bin .mul (.const 2) (.reg 25))) (.const 3))

lemma projSeqToWalkStmt_noRand : projSeqToWalkStmt.NoRand := by
  simp [projSeqToWalkStmt, projSeqSetupStmt, projSeqBodyStmt, seqStmts, forRange, forUp, Stmt.NoRand]

theorem projSeqToWalkStmt_triple {w src dst n k : ℕ} {p : Program}
    (st₀ : State) (P_s : List ℕ)
    (hr20 : st₀.regs 20 = src) (hr21 : st₀.regs 21 = dst) (hr22 : st₀.regs 22 = n)
    (halt : SubdivAltSeq n k P_s)
    (hm_len : st₀.mem src = P_s.length)
    (hm_verts : ListAt st₀.mem (src + 1) P_s)
    (hPs_w : ∀ x ∈ P_s, x < 2 ^ w)
    (hdisj : dst + 2 * k + 3 ≤ src ∨ src + P_s.length + 1 ≤ dst)
    (hsrc_w : src + P_s.length + 1 < 2 ^ w)
    (hdst_w : dst + 2 * k + 3 < 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w) :
    Triple w p (fun st => st = st₀) projSeqToWalkStmt
      (normalPost fun st' =>
        WalkAt st'.mem dst ⟨projPath n P_s, projEdges n P_s⟩ ∧
        MemFrame st₀.mem st'.mem dst (dst + 2 * k + 3) ∧
        st'.regs 23 = dst + 2 * k + 3 ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 65 * k + 75) := by
  have hw2 : 1 < 2 ^ w := by omega
  have hw5 : 4 < 2 ^ w := by
    have hlen := halt.1
    rcases hdisj with h | h <;> omega
  have hk_w : k < 2 ^ w := by omega
  have hlen_w : P_s.length < 2 ^ w := by omega
  have hk_div : (P_s.length - 1) / 3 = k := by rw [halt.1]; omega
  have hu0_w : P_s.getD 0 0 < 2 ^ w := by
    have h0 : 0 < P_s.length := by rw [halt.1]; omega
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0] using hPs_w _ (List.getElem_mem h0)
  have hsu0 : st₀.mem (src + 1) = P_s.getD 0 0 := by
    have h0 : 0 < P_s.length := by rw [halt.1]; omega
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0] using hm_verts 0 h0
  let PreL : State → Prop := fun st =>
    st.regs 20 = src ∧ st.regs 21 = dst ∧ st.regs 22 = n ∧ st.regs 25 = k ∧
    MemFrame st₀.mem st.mem dst (dst + 2 * k + 3) ∧
    st.mem dst = k + 1 ∧ st.mem (dst + 1) = P_s.getD 0 0 ∧ st.mem (dst + k + 2) = k ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  let Inv : ℕ → State → Prop := fun i st =>
    i ≤ k ∧ st.regs 20 = src ∧ st.regs 21 = dst ∧ st.regs 22 = n ∧ st.regs 25 = k ∧
    st.regs 26 = i ∧ MemFrame st₀.mem st.mem dst (dst + 2 * k + 3) ∧
    st.mem dst = k + 1 ∧ st.mem (dst + 1) = P_s.getD 0 0 ∧ st.mem (dst + k + 2) = k ∧
    (∀ t < i, st.mem (dst + 2 + t) = P_s.getD (3 * t + 3) 0 ∧
      st.mem (dst + k + 3 + t) = (P_s.getD (3 * t + 1) 0 - n) / 2) ∧
    (∀ r < 20, st.regs r = st₀.regs r) ∧ st.pos = st₀.pos
  have hsetup : Triple w p (fun st => st = st₀) projSeqSetupStmt (normalPost PreL) (fun _ => 38) := by
    wram_enter; subst hpre; dsimp only [projSeqSetupStmt, seqStmts]
    wram_step; simp only [hm_len]
    wram_step
    wram_step; simp only [hr20, hsu0]
    wram_run
    · refine ⟨by simp [hr20], by simp [hr21], by simp [hr22], by simp [hk_div], ?_, ?_, ?_, ?_,
        fun r hr => by simp only [Function.update_apply]; split_ifs <;> omega, rfl⟩
      · (try dsimp only); (try rw [hr21]); (try rw [hk_div])
        exact memFrame_trans (memFrame_update (by omega) (by omega))
          (memFrame_trans (memFrame_update (by omega) (by omega)) (memFrame_update (by omega) (by omega)))
      · (try dsimp only); (try rw [hr21]); (try rw [hk_div])
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
      · dsimp only; rw [hr21, hk_div, Function.update_of_ne (by omega), Function.update_self]
        simp [List.getD_eq_getElem?_getD]
      · (try dsimp only); (try rw [hr21]); (try rw [hk_div])
        rw [show dst + (k + 2) = dst + k + 2 by omega, Function.update_self]
    · wram_cost
  have hloop := Triple.forRange_const (p := p) (r := 26) (lo := .const 0) (hi := .reg 25)
    (body := projSeqBodyStmt) (P := PreL) (Inv := Inv) 45 0 k (Nat.zero_le k) hw2 (fun _ => hk_w)
    (fun st ⟨h20, h21, h22, h25, hfr, hmd0, hmd1, hmdk, hlt20, hpos⟩ => ⟨by eval_expr,
      Nat.zero_le _, by simp [h20], by simp [h21], by simp [h22], by simp [h25], by simp,
      hfr, hmd0, hmd1, hmdk, fun _ ht => absurd ht (Nat.not_lt_zero _),
      fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.1)
    (fun _ _ _ _ hI => by have := hI.2.2.2.2.1; eval_expr)
    (fun i _ hilt st ω ⟨_, h20, h21, h22, h25, h26, hfr, hmd0, hmd1, hmdk, hrec, hlt20, hpos⟩ => by
      have hy_idx : 3 * i + 1 < P_s.length := by rw [halt.1]; omega
      have hw_idx : 3 * i + 3 < P_s.length := by rw [halt.1]; omega
      have hy_w : P_s.getD (3 * i + 1) 0 < 2 ^ w := by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy_idx] using hPs_w _ (List.getElem_mem hy_idx)
      have hy_w' : P_s[3 * i + 1]?.getD 0 < 2 ^ w := by
        simpa [List.getD_eq_getElem?_getD] using hy_w
      have hy_ge : n ≤ P_s.getD (3 * i + 1) 0 := (halt.2.2 i hilt).1
      have hn_w : n < 2 ^ w := by omega
      have hwi_w : P_s.getD (3 * i + 3) 0 < 2 ^ w := by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw_idx] using hPs_w _ (List.getElem_mem hw_idx)
      have hsrc_y : st.mem (src + 2 + 3 * i) = P_s.getD (3 * i + 1) 0 := by
        rw [hfr _ (by omega), show src + 2 + 3 * i = src + 1 + (3 * i + 1) by omega]
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy_idx] using hm_verts (3 * i + 1) hy_idx
      have hsrc_w' : st.mem (src + 4 + 3 * i) = P_s.getD (3 * i + 3) 0 := by
        rw [hfr _ (by omega), show src + 4 + 3 * i = src + 1 + (3 * i + 3) by omega]
        simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw_idx] using hm_verts (3 * i + 3) hw_idx
      refine runs_start_le ?_
      dsimp only [projSeqBodyStmt, seqStmts]
      wram_step; simp only [hsrc_y]
      wram_step; simp only [h20, h26, hsrc_w']
      wram_run
      · refine ⟨⟨hilt, by simp [h20], by simp [h21], by simp [h22], by simp [h25], by simp,
          ?_, ?_, ?_, ?_, fun t ht => ?_,
          fun r hr => by simp only [Function.update_apply]; split_ifs <;> first | omega | exact hlt20 r hr,
          hpos⟩, by simp [h26]⟩
        · (try dsimp only); (try rw [h21]); (try rw [h25]); (try rw [h26])
          exact memFrame_trans hfr (memFrame_trans (memFrame_update (by omega) (by omega))
            (memFrame_update (by omega) (by omega)))
        · (try dsimp only); (try rw [h21]); (try rw [h25]); (try rw [h26])
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hmd0]
        · (try dsimp only); (try rw [h21]); (try rw [h25]); (try rw [h26])
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hmd1]
        · (try dsimp only); (try rw [h21]); (try rw [h25]); (try rw [h26])
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hmdk]
        · dsimp only; rw [h21, h25, h26, h22]
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
          · exact ⟨by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                      simpa [List.getD_eq_getElem?_getD] using (hrec t ht').1,
              by rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                 simpa [List.getD_eq_getElem?_getD] using (hrec t ht').2⟩
          · exact ⟨by rw [Function.update_of_ne (by omega), Function.update_self]
                      simp [List.getD_eq_getElem?_getD],
              by rw [show dst + (k + 3) + t = dst + k + 3 + t by omega, Function.update_self]
                 simp [List.getD_eq_getElem?_getD]⟩
      · wram_cost)
  have hmid : Triple w p (fun st => st = st₀)
      (projSeqSetupStmt ;; forRange 26 (.const 0) (.reg 25) projSeqBodyStmt)
      (normalPost (Inv k)) (fun _ => 65 * k + 55) :=
    (Triple.seq_normal hsetup hloop (T := fun _ => 65 * k + 55)
      (fun _ _ _ _ => by simp [Expr.size]; omega)).conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_rfl)
  have htail : Triple w p (Inv k)
      (.assign 23 (.bin .add (.bin .add (.reg 21) (.bin .mul (.const 2) (.reg 25))) (.const 3)))
      (normalPost fun st' =>
        WalkAt st'.mem dst ⟨projPath n P_s, projEdges n P_s⟩ ∧
        MemFrame st₀.mem st'.mem dst (dst + 2 * k + 3) ∧
        st'.regs 23 = dst + 2 * k + 3 ∧
        (∀ r < 20, st'.regs r = st₀.regs r) ∧
        st'.pos = st₀.pos)
      (fun _ => 10) := by
    wram_enter
    rcases hpre with ⟨_, _, h21, _, h25, _, hfr, hmd0, hmd1, hmdk, hrec, hlt20, hpos⟩
    obtain ⟨hVlen, hV0, hVs⟩ := projPath_subdivAlt n k P_s halt
    obtain ⟨hElen, hEs⟩ := projEdges_subdivAlt n k P_s halt
    have hVpos : 0 < (projPath n P_s).length := by rw [hVlen]; omega
    have hV0' : (projPath n P_s)[0]'hVpos = P_s.getD 0 0 := by
      have hg : (projPath n P_s)[0]'hVpos = (projPath n P_s).getD 0 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hVpos]
      rw [hg, hV0]
    wram_run
    · refine ⟨walkAt_of_cells (by simpa [hVlen] using hmd0) (fun i hi => ?_)
          (by rw [hVlen, hElen, show dst + 1 + (k + 1) = dst + k + 2 by omega]; exact hmdk) (fun i hi => ?_),
        hfr, by simp,
        fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hlt20 r hr, hpos⟩
      · have hgi : (projPath n P_s)[i]'hi = (projPath n P_s).getD i 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        cases i with
        | zero => rw [hV0', hmd1]
        | succ i' =>
          have hi' : i' < k := by rw [hVlen] at hi; omega
          rw [hgi, hVs i' hi', show dst + 1 + (i' + 1) = dst + 2 + i' by omega]
          exact (hrec i' hi').1
      · have hgi : (projEdges n P_s)[i]'hi = (projEdges n P_s).getD i 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        have hi' : i < k := by rw [hElen] at hi; exact hi
        dsimp only at hi ⊢
        rw [hgi, hEs i hi', show dst + 2 + (projPath n P_s).length + i = dst + k + 3 + i by rw [hVlen]; omega]
        exact (hrec i hi').2
    · wram_cost
  exact (Triple.seq_normal hmid htail (T := fun _ => 65 * k + 75)
    (fun _ _ _ _ => by omega)).conseq (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_rfl)

end MinCostFlow.Expander.PathDSProg
