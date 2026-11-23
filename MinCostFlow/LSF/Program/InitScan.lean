module

public import MinCostFlow.LSF.Program.InitScanOuter
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Top-Level Verification of `initScanStmt` (`InitScan`)

Proves `initScan_copy_runs`, `initScan_setup_runs`, `initScan_runs_of_pre`, and
`initScan_meetsContract`: `initScanStmt` satisfies `initScanContract` in
`O(n₀ + m₀)` time (`≤ 170 * G₀.n + 300 * G₀.m + 220`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

private lemma initScan_copy_runs {w g0Ptr vCap auxPtr logCap auxEnd vCap0 : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State} {sb : ScanBases} {G₀ : MGraph} {vL : List ℕ}
    (hw1 : 1 < 2 ^ w) (hauxW : auxEnd < 2 ^ w)
    (hvlt0 : ∀ v ∈ G₀.V, v < vCap0) (hvs0 : vCap0 ≤ vCap)
    (hVL_len : vL.length = G₀.n) (hVL_nd : vL.Nodup) (hVL_mem : ∀ v, v ∈ vL ↔ v ∈ G₀.V)
    (hVL_LA : ListAt st.mem sb.gVListBase vL)
    (hle_aux : auxPtr + auxHdrSize ≤ sb.vIdxBase)
    (hdisj_iv : sb.vIdxBase + vCap = sb.vListBase)
    (hdisj_vo : sb.vListBase + G₀.n ≤ sb.origVertBase)
    (hdisj_oi : sb.origVertBase + vCap = sb.isOrigBase)
    (hdisj_iq : sb.isOrigBase + vCap ≤ auxEnd)
    (hg_lo : sb.gVListBase + G₀.n ≤ auxPtr)
    (hb : ScanBaseRegs st g0Ptr vCap auxPtr logCap sb) (hn_eq : sb.n0 = G₀.n)
    (hvidx0 : ∀ v < vCap, st.mem (sb.vIdxBase + v) = 0)
    (hisorig0 : ∀ v < vCap, st.mem (sb.isOrigBase + v) = 0) :
    ∃ st' c, Runs w p ω
      (forRange 22 (.const 0) (.reg 6)
        (.assign 24 (.load (.bin .add (.reg 15) (.reg 22))) ;;
         .store (.bin .add (.reg 8) (.reg 22)) (.reg 24) ;;
         .store (.bin .add (.reg 7) (.reg 24)) (.bin .add (.reg 22) (.const 1)) ;;
         .store (.bin .add (.reg 10) (.reg 24)) (.reg 24) ;;
         .store (.bin .add (.reg 11) (.reg 24)) (.const 1))) st .normal st' c ∧
      ScanBaseRegs st' g0Ptr vCap auxPtr logCap sb ∧
      ListAt st'.mem sb.vListBase vL ∧
      (∀ i (hi : i < vL.length), st'.mem (sb.vIdxBase + vL[i]) = i + 1) ∧
      (∀ v < vCap, v ∉ G₀.V → st'.mem (sb.vIdxBase + v) = 0) ∧
      (∀ v < vCap, st'.mem (sb.isOrigBase + v) = if v ∈ G₀.V then 1 else 0) ∧
      (∀ w' ∈ G₀.V, w' < vCap → st'.mem (sb.origVertBase + w') = w') ∧
      (∀ a, a < sb.vIdxBase ∨ (sb.vListBase + G₀.n ≤ a ∧ a < sb.origVertBase) ∨
        sb.isOrigBase + vCap ≤ a → st'.mem a = st.mem a) ∧
      c ≤ 55 * G₀.n + 10 := by
  let Inv : ℕ → State → Prop := fun i st_k =>
    ScanBaseRegs st_k g0Ptr vCap auxPtr logCap sb ∧
    st_k.regs 22 = i ∧
    (∀ j < i, st_k.mem (sb.vListBase + j) = vL.getD j 0) ∧
    (∀ j < i, st_k.mem (sb.vIdxBase + vL.getD j 0) = j + 1) ∧
    (∀ v < vCap, (∀ j < i, v ≠ vL.getD j 0) → st_k.mem (sb.vIdxBase + v) = 0) ∧
    (∀ v < vCap, st_k.mem (sb.isOrigBase + v) = if ∃ j < i, v = vL.getD j 0 then 1 else 0) ∧
    (∀ j < i, st_k.mem (sb.origVertBase + vL.getD j 0) = vL.getD j 0) ∧
    ∀ a, a < sb.vIdxBase ∨ (sb.vListBase + G₀.n ≤ a ∧ a < sb.origVertBase) ∨
      sb.isOrigBase + vCap ≤ a → st_k.mem a = st.mem a
  have hgnW : G₀.n < 2 ^ w := by omega
  have hloop : Triple w p (fun s => s = st)
      (forRange 22 (.const 0) (.reg 6)
        (.assign 24 (.load (.bin .add (.reg 15) (.reg 22))) ;;
         .store (.bin .add (.reg 8) (.reg 22)) (.reg 24) ;;
         .store (.bin .add (.reg 7) (.reg 24)) (.bin .add (.reg 22) (.const 1)) ;;
         .store (.bin .add (.reg 10) (.reg 24)) (.reg 24) ;;
         .store (.bin .add (.reg 11) (.reg 24)) (.const 1)))
      (normalPost (Inv G₀.n)) (fun _ => (G₀.n - 0) * (45 + (.reg 6 : Expr).size + 8) + ((.const 0 : Expr).size + (.reg 6 : Expr).size + 5)) :=
    Triple.forRange_const (w := w) (p := p) (P := fun s => s = st)
      (r := 22) (lo := .const 0) (hi := .reg 6) (Inv := Inv) 45 0 G₀.n
      (Nat.zero_le G₀.n) hw1 (fun _ => hgnW)
      (fun st_0 hst0 => by
        subst hst0
        exact ⟨Expr.eval_const (by omega), scanBaseRegs_upd hb 22 0 (by decide), rfl,
          fun _ h => by omega, fun _ h => by omega,
          fun v hv _ => hvidx0 v hv, fun v hv => by simp [hisorig0 v hv],
          fun _ h => by omega, fun _ _ => rfl⟩)
      (fun i st_k _ _ hInv => hInv.2.1)
      (fun i st_k _ _ hInv => by have h6 := hInv.1.r6; rw [hn_eq] at h6; eval_expr)
      (fun i hi0 hilt st_k ω' hInv => by
      rcases hInv with ⟨hb_k, hr22, hvL_k, hvI_k, hvI0_k, hIO_k, hOV_k, hfr_k⟩
      have hi_len : i < vL.length := hVL_len.symm ▸ hilt
      set u := vL[i]'hi_len
      have huV : u ∈ G₀.V := (hVL_mem u).mp (List.getElem_mem hi_len)
      have hu_cap : u < vCap := lt_of_lt_of_le (hvlt0 u huV) hvs0
      have hr7 : st_k.regs 7 = sb.vIdxBase := hb_k.r7
      have hr8 : st_k.regs 8 = sb.vListBase := hb_k.r8
      have hr10 : st_k.regs 10 = sb.origVertBase := hb_k.r10
      have hr11 : st_k.regs 11 = sb.isOrigBase := hb_k.r11
      have hr15 : st_k.regs 15 = sb.gVListBase := hb_k.r15
      have huW : u < 2 ^ w := by omega
      have hiW : i < 2 ^ w := by omega
      have hi1W : i + 1 < 2 ^ w := by omega
      have hviB_w : sb.vIdxBase < 2 ^ w := by omega
      have hvlB_w : sb.vListBase < 2 ^ w := by omega
      have hovB_w : sb.origVertBase < 2 ^ w := by omega
      have hioB_w : sb.isOrigBase < 2 ^ w := by omega
      have hgvlB_w : sb.gVListBase < 2 ^ w := by omega
      have hg_addrW : sb.gVListBase + i < 2 ^ w := by omega
      have hvl_addrW : sb.vListBase + i < 2 ^ w := by omega
      have hvi_addrW : sb.vIdxBase + u < 2 ^ w := by omega
      have hov_addrW : sb.origVertBase + u < 2 ^ w := by omega
      have hio_addrW : sb.isOrigBase + u < 2 ^ w := by omega
      have hload_u : st_k.mem (sb.gVListBase + i) = u := by
        rw [hfr_k _ (Or.inl (by omega))]
        exact hVL_LA i hi_len
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := u) (by eval_expr) ?_
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      refine runs_store_le (by eval_expr) (by eval_expr) ?_ (by wram_cost)
      have hnd_lt : ∀ j < i, vL.getD j 0 ≠ u := by
        intro j hj hEq
        have hj_len : j < vL.length := by omega
        rw [List.getD_eq_getElem _ _ hj_len] at hEq
        have hij := hVL_nd.getElem_inj_iff.mp hEq
        omega
      refine ⟨⟨scanBaseRegs_upd (scanBaseRegs_updMem (scanBaseRegs_upd hb_k 24 u (by decide)) _)
          22 (i + 1) (by decide),
        by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [hr22]⟩
      · intro j hj
        dsimp only
        have hne1 : sb.vListBase + j ≠ sb.isOrigBase + u := by omega
        have hne2 : sb.vListBase + j ≠ sb.origVertBase + u := by omega
        have hne3 : sb.vListBase + j ≠ sb.vIdxBase + u := by omega
        rw [Function.update_of_ne hne1, Function.update_of_ne hne2, Function.update_of_ne hne3]
        by_cases hji : j = i
        · subst j; rw [Function.update_self]; exact (List.getD_eq_getElem _ _ hi_len).symm
        · rw [Function.update_of_ne (by omega)]; exact hvL_k j (by omega)
      · intro j hj
        dsimp only
        by_cases hji : j = i
        · subst j
          have hget : vL.getD i 0 = u := List.getD_eq_getElem _ _ hi_len
          rw [hget, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          simp
        · have hne_u := hnd_lt j (by omega)
          have hj_lt : vL.getD j 0 < vCap :=
            lt_of_lt_of_le (hvlt0 _ ((hVL_mem _).mp (by
              rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _))) hvs0
          have hne1 : sb.vIdxBase + vL.getD j 0 ≠ sb.isOrigBase + u := by omega
          have hne2 : sb.vIdxBase + vL.getD j 0 ≠ sb.origVertBase + u := by omega
          have hne3 : sb.vIdxBase + vL.getD j 0 ≠ sb.vIdxBase + u := by omega
          have hne4 : sb.vIdxBase + vL.getD j 0 ≠ sb.vListBase + i := by omega
          rw [Function.update_of_ne hne1, Function.update_of_ne hne2,
            Function.update_of_ne hne3, Function.update_of_ne hne4]
          exact hvI_k j (by omega)
      · intro v hv hne_j
        dsimp only
        have hne_u : v ≠ u := by
          have := hne_j i (by omega)
          rwa [List.getD_eq_getElem _ _ hi_len] at this
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hvI0_k v hv fun j hj => hne_j j (by omega)
      · intro v hv
        dsimp only
        by_cases hvu : v = u
        · subst v
          simp only [Function.update_self]
          rw [eq_comm, ite_eq_left_iff]
          intro hnot
          exact absurd ⟨i, by omega, (List.getD_eq_getElem _ _ hi_len).symm⟩ hnot
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega), hIO_k v hv]
          have hiff : (∃ j < i, v = vL.getD j 0) ↔ (∃ j < i + 1, v = vL.getD j 0) := by
            constructor
            · rintro ⟨j, hj, hEq⟩; exact ⟨j, by omega, hEq⟩
            · rintro ⟨j, hj, hEq⟩
              by_cases hji : j = i
              · subst j; rw [List.getD_eq_getElem _ _ hi_len] at hEq; exact False.elim (hvu hEq)
              · exact ⟨j, by omega, hEq⟩
          simp only [hiff]
      · intro j hj
        dsimp only
        by_cases hji : j = i
        · subst j
          have hget : vL.getD i 0 = u := List.getD_eq_getElem _ _ hi_len
          rw [hget, Function.update_of_ne (by omega)]
          simp
        · have hne_u := hnd_lt j (by omega)
          have hlt_j : vL.getD j 0 < vCap :=
            lt_of_lt_of_le (hvlt0 _ ((hVL_mem _).mp (by
              rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _))) hvs0
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hOV_k j (by omega)
      · intro a ha
        dsimp only
        have hu1 : a ≠ sb.isOrigBase + u := by rcases ha with h | ⟨h1, h2⟩ | h <;> omega
        have hu2 : a ≠ sb.origVertBase + u := by rcases ha with h | ⟨h1, h2⟩ | h <;> omega
        have hu3 : a ≠ sb.vIdxBase + u := by rcases ha with h | ⟨h1, h2⟩ | h <;> omega
        have hu4 : a ≠ sb.vListBase + i := by rcases ha with h | ⟨h1, h2⟩ | h <;> omega
        rw [Function.update_of_ne hu1, Function.update_of_ne hu2,
          Function.update_of_ne hu3, Function.update_of_ne hu4]
        exact hfr_k a ha)
  obtain ⟨o, st', c, hr, hpost, hc⟩ := hloop st ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨hb', _, hvL', hvI', hvI0', hIO', hOV', hfr'⟩
    refine ⟨st', c, hr, hb',
      fun i hi => by
        have h := hvL' i (hVL_len ▸ hi)
        rwa [List.getD_eq_getElem _ _ hi] at h,
      fun i hi => by
        have h := hvI' i (hVL_len ▸ hi)
        rwa [List.getD_eq_getElem _ _ hi] at h,
      fun v hv hnotV => hvI0' v hv fun j hj hEq => by
        have hj_len : j < vL.length := hVL_len.symm ▸ hj
        rw [List.getD_eq_getElem _ _ hj_len] at hEq
        exact hnotV (hEq ▸ (hVL_mem _).mp (List.getElem_mem hj_len)),
      fun v hv => ?_,
      fun w' hwV _ => ?_, hfr', ?_⟩
    · rw [hIO' v hv]
      have hiff : (∃ j < G₀.n, v = vL.getD j 0) ↔ v ∈ G₀.V := by
        rw [← hVL_mem v, List.mem_iff_getElem]
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j, hVL_len.symm ▸ hj, (List.getD_eq_getElem _ _ (hVL_len.symm ▸ hj)).symm⟩
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j, hVL_len ▸ hj, (List.getD_eq_getElem _ _ hj).symm⟩
      simp only [hiff]
    · obtain ⟨j, hj_lt, hj_eq⟩ := List.mem_iff_getElem.mp ((hVL_mem w').mpr hwV)
      have hov := hOV' j (hVL_len ▸ hj_lt)
      rwa [List.getD_eq_getElem _ _ hj_lt, hj_eq] at hov
    · dsimp [Expr.size] at hc
      omega

private lemma runs_seq_assign_state {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {r : ℕ} {e : Expr} {s : Stmt} {st : State} {v : ℕ}
    {Q : Outcome → State → Prop} {k T : ℕ}
    (he : e.eval w st = some v)
    (hnext : ∀ st', st'.mem = st.mem → st'.pos = st.pos → st'.regs r = v →
      (∀ r', r' ≠ r → st'.regs r' = st.regs r') →
      ∃ o st'' c, Runs w p ω s st' o st'' c ∧ Q o st'' ∧ (k + (e.size + 1) + 1) + c ≤ T) :
    ∃ o st'' c, Runs w p ω (.assign r e ;; s) st o st'' c ∧ Q o st'' ∧ k + c ≤ T := by
  obtain ⟨o, st'', c, hr, hq, hc⟩ := hnext { st with regs := Function.update st.regs r v }
    rfl rfl (Function.update_self _ _ _) (fun r' hr' => by simp [Function.update_of_ne hr'])
  exact ⟨o, st'', (e.size + 1) + c + 1,
    WordRAM.runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, c,
      runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr, rfl⟩), hq, by omega⟩

private def initScanRegVal (g0Ptr vCap auxPtr logCap vCap0 eCap0 n0 : ℕ)
    (sb : ScanBases) : ℕ → ℕ
  | 0 => g0Ptr
  | 1 => vCap
  | 2 => auxPtr
  | 3 => logCap
  | 4 => vCap0
  | 5 => eCap0
  | 6 => n0
  | 7 => sb.vIdxBase
  | 8 => sb.vListBase
  | 9 => sb.thParentBase
  | 10 => sb.origVertBase
  | 11 => sb.isOrigBase
  | 12 => sb.qBufABase
  | 13 => sb.cRepsBase
  | 14 => sb.visBBase
  | 15 => sb.gVListBase
  | 16 => sb.gExtToIntBase
  | 17 => sb.gIntToExtBase
  | 18 => sb.gIncHeadBase
  | 19 => sb.gETailBase
  | 20 => sb.gEHeadBase
  | 21 => sb.gHeNextBase
  | _ => 0

private lemma initScan_setup_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {pos g0Ptr vCap auxPtr logCap vCap0 eCap0 n0 : ℕ}
    {Q : Outcome → State → Prop} {T : ℕ}
    (hw16 : 16 ≤ 2 ^ w) (hn_pos : 1 ≤ n0) (hn_v0 : n0 ≤ vCap0) (hvs0 : vCap0 ≤ vCap)
    (hlog_eq : logCap = auxLogCap n0)
    (haux_lo : g0Ptr + dynGraphSize vCap0 eCap0 ≤ auxPtr)
    (hauxW : auxPtr + auxSize vCap n0 < 2 ^ w)
    (hvcap0_eq : mem (g0Ptr + dgVCapOff) = vCap0)
    (hecap0_eq : mem (g0Ptr + dgECapOff) = eCap0)
    (hn_eq : mem (g0Ptr + dgNOff) = n0)
    (hrest : ∀ st_s : State,
      ScanBaseRegs st_s g0Ptr vCap auxPtr logCap
        (mkScanBases g0Ptr vCap auxPtr (auxLogCap n0) vCap0 eCap0 n0) →
      st_s.mem = mem → st_s.pos = pos →
      ∃ o st' c, Runs w p ω
        (forRange 22 (.const 0) (.reg 6)
          (.assign 24 (.load (.bin .add (.reg 15) (.reg 22))) ;;
           .store (.bin .add (.reg 8) (.reg 22)) (.reg 24) ;;
           .store (.bin .add (.reg 7) (.reg 24)) (.bin .add (.reg 22) (.const 1)) ;;
           .store (.bin .add (.reg 10) (.reg 24)) (.reg 24) ;;
           .store (.bin .add (.reg 11) (.reg 24)) (.const 1)) ;;
         .assign 23 (.const 0) ;;
         forRange 22 (.const 0) (.reg 6)
           (.assign 24 (.load (.bin .add (.reg 8) (.reg 22))) ;;
            .cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 24))) (.const 0))
              (.store (.bin .add (.reg 13) (.reg 23)) (.reg 24) ;;
               .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
               .store (.bin .add (.reg 14) (.reg 24)) (.const 1) ;;
               .store (.reg 12) (.reg 24) ;;
               .assign 25 (.const 0) ;;
               .assign 26 (.const 1) ;;
               initScanBfsCompStmt)
              .nop) ;;
         forRange 22 (.const 0) (.reg 6)
           (.assign 24 (.load (.bin .add (.reg 8) (.reg 22))) ;;
            .store (.bin .add (.reg 14) (.reg 24)) (.const 0)) ;;
         .ret (.reg 23)) st_s o st' c ∧
        Q o st' ∧ 170 + c ≤ T) :
    ∃ o st' c, Runs w p ω initScanStmt (startState [g0Ptr, vCap, auxPtr, logCap] mem pos) o st' c ∧
      Q o st' ∧ c ≤ T := by
  let sb := mkScanBases g0Ptr vCap auxPtr (auxLogCap n0) vCap0 eCap0 n0
  let rval := initScanRegVal g0Ptr vCap auxPtr logCap vCap0 eCap0 n0 sb
  have hlog_le : auxLogCap n0 ≤ n0 * auxLogCap n0 := Nat.le_mul_of_pos_left _ hn_pos
  have hw_bds : 1 < 2 ^ w ∧ auxHdrSize < 2 ^ w ∧ g0Ptr < 2 ^ w ∧ vCap < 2 ^ w ∧
      auxPtr < 2 ^ w ∧ logCap < 2 ^ w ∧ vCap0 < 2 ^ w ∧ eCap0 < 2 ^ w ∧ n0 < 2 ^ w ∧
      dgVCapOff < 2 ^ w ∧ dgECapOff < 2 ^ w ∧ dgNOff < 2 ^ w ∧
      g0Ptr + dgVCapOff < 2 ^ w ∧ g0Ptr + dgECapOff < 2 ^ w ∧ g0Ptr + dgNOff < 2 ^ w ∧
      sb.vIdxBase < 2 ^ w ∧ sb.vListBase < 2 ^ w ∧ sb.thParentBase < 2 ^ w ∧
      sb.origVertBase < 2 ^ w ∧ sb.isOrigBase < 2 ^ w ∧ sb.qBufABase < 2 ^ w ∧
      sb.cRepsBase < 2 ^ w ∧ sb.visBBase < 2 ^ w ∧
      4 * n0 < 2 ^ w ∧ n0 * logCap < 2 ^ w ∧ 2 * (n0 * logCap) < 2 ^ w ∧
      sb.vListBase + 4 * n0 < 2 ^ w ∧ 2 * vCap < 2 ^ w ∧
      g0Ptr + 4 < 2 ^ w ∧ 3 * vCap0 < 2 ^ w ∧ 4 * vCap0 < 2 ^ w ∧ 6 * vCap0 < 2 ^ w ∧
      7 * vCap0 < 2 ^ w ∧ 3 * eCap0 < 2 ^ w ∧ 4 * eCap0 < 2 ^ w ∧ 7 * eCap0 < 2 ^ w ∧
      sb.gVListBase < 2 ^ w ∧ sb.gExtToIntBase < 2 ^ w ∧ sb.gIntToExtBase < 2 ^ w ∧
      sb.gIncHeadBase < 2 ^ w ∧ sb.gETailBase < 2 ^ w ∧ sb.gEHeadBase < 2 ^ w ∧
      sb.gHeNextBase < 2 ^ w ∧
      sb.gIncHeadBase + vCap0 < 2 ^ w ∧ sb.gETailBase + eCap0 < 2 ^ w ∧
      sb.gEHeadBase + eCap0 < 2 ^ w ∧
      7 * vCap0 + 3 * eCap0 < 2 ^ w ∧ 7 * vCap0 + 4 * eCap0 < 2 ^ w ∧
      7 * vCap0 + 7 * eCap0 < 2 ^ w ∧
      g0Ptr + 4 + (7 * vCap0 + 3 * eCap0) < 2 ^ w ∧
      g0Ptr + 4 + (7 * vCap0 + 4 * eCap0) < 2 ^ w ∧
      g0Ptr + 4 + (7 * vCap0 + 7 * eCap0) < 2 ^ w := by
    dsimp only [sb, mkScanBases, auxSize, auxVListBase, auxVIdxBase, auxHdrSize,
      dgVListBase, dgExtToIntBase, dgIntToExtBase, dgIncHeadBase,
      dgETailSlotBase, dgEHeadSlotBase, dgHeNextBase, dgVCapOff, dgECapOff, dgNOff,
      dynGraphSize] at *
    subst hlog_eq
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have ⟨hw1, hhdrW, hgW, hvW, hauxpW, hlogW, hv0W, he0W, hn0W, hdvW, hdeW, hdnW,
    hgvW, hgeW, hgnW, h7W, h8W, h9W, h10W, h11W, h12W, h13W, h14W,
    h4nW, hnlogW, h2nlogW, h8_4nW, h2vW,
    hg4W, h3v0W, h4v0W, h6v0W, h7v0W, h3e0W, h4e0W, h7e0W,
    h15W, h16W, h17W, h18W, h19W, h20W, h21W, h18vW, h19eW, h20eW,
    h7v3eW, h7v4eW, h7v7eW, hg7v3eW, hg7v4eW, hg7v7eW⟩ := hw_bds
  let st3 := startState [g0Ptr, vCap, auxPtr, logCap] mem pos
  have hm3 : st3.mem = mem := rfl
  have hp3 : st3.pos = pos := rfl
  have ha3 : ∀ j < 4, st3.regs j = rval j := fun j hj => by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  unfold initScanStmt
  refine runs_start_le ?_
  -- Step 4
  have hr3_0 : st3.regs 0 = g0Ptr := ha3 0 (by decide)
  have hm3_4 : st3.mem (g0Ptr + dgVCapOff) = vCap0 := by rw [hm3]; exact hvcap0_eq
  refine runs_seq_assign_state (v := vCap0) (by eval_expr) ?_
  intro st4 hm4 hp4 hr4_4 hf4
  have hm4' : st4.mem = mem := hm4.trans hm3
  have hp4' : st4.pos = pos := hp4.trans hp3
  have ha4 : ∀ j < 5, st4.regs j = rval j := fun j hj => by
    by_cases hjk : j = 4
    · subst j; exact hr4_4
    · exact (hf4 j hjk).trans (ha3 j (by omega))
  -- Step 5
  have hr4_0 : st4.regs 0 = g0Ptr := ha4 0 (by decide)
  have hm4_5 : st4.mem (g0Ptr + dgECapOff) = eCap0 := by rw [hm4']; exact hecap0_eq
  refine runs_seq_assign_state (v := eCap0) (by eval_expr) ?_
  intro st5 hm5 hp5 hr5_5 hf5
  have hm5' : st5.mem = mem := hm5.trans hm4'
  have hp5' : st5.pos = pos := hp5.trans hp4'
  have ha5 : ∀ j < 6, st5.regs j = rval j := fun j hj => by
    by_cases hjk : j = 5
    · subst j; exact hr5_5
    · exact (hf5 j hjk).trans (ha4 j (by omega))
  -- Step 6
  have hr5_0 : st5.regs 0 = g0Ptr := ha5 0 (by decide)
  have hm5_6 : st5.mem (g0Ptr + dgNOff) = n0 := by rw [hm5']; exact hn_eq
  refine runs_seq_assign_state (v := n0) (by eval_expr) ?_
  intro st6 hm6 hp6 hr6_6 hf6
  have hm6' : st6.mem = mem := hm6.trans hm5'
  have hp6' : st6.pos = pos := hp6.trans hp5'
  have ha6 : ∀ j < 7, st6.regs j = rval j := fun j hj => by
    by_cases hjk : j = 6
    · subst j; exact hr6_6
    · exact (hf6 j hjk).trans (ha5 j (by omega))
  -- Step 7
  have hr6_2 : st6.regs 2 = auxPtr := ha6 2 (by decide)
  refine runs_seq_assign_state (v := sb.vIdxBase) (by
    have hdef : sb.vIdxBase = auxPtr + auxHdrSize := rfl
    rw [hdef]; eval_expr) ?_
  intro st7 hm7 hp7 hr7_7 hf7
  have hm7' : st7.mem = mem := hm7.trans hm6'
  have hp7' : st7.pos = pos := hp7.trans hp6'
  have ha7 : ∀ j < 8, st7.regs j = rval j := fun j hj => by
    by_cases hjk : j = 7
    · subst j; exact hr7_7
    · exact (hf7 j hjk).trans (ha6 j (by omega))
  -- Step 8
  have hr7_1 : st7.regs 1 = vCap := ha7 1 (by decide)
  have hr7_7' : st7.regs 7 = sb.vIdxBase := ha7 7 (by decide)
  refine runs_seq_assign_state (v := sb.vListBase) (by
    have hdef : sb.vListBase = sb.vIdxBase + vCap := rfl
    rw [hdef]; eval_expr) ?_
  intro st8 hm8 hp8 hr8_8 hf8
  have hm8' : st8.mem = mem := hm8.trans hm7'
  have hp8' : st8.pos = pos := hp8.trans hp7'
  have ha8 : ∀ j < 9, st8.regs j = rval j := fun j hj => by
    by_cases hjk : j = 8
    · subst j; exact hr8_8
    · exact (hf8 j hjk).trans (ha7 j (by omega))
  -- Step 9
  have hr8_3 : st8.regs 3 = logCap := ha8 3 (by decide)
  have hr8_6 : st8.regs 6 = n0 := ha8 6 (by decide)
  have hr8_8' : st8.regs 8 = sb.vListBase := ha8 8 (by decide)
  refine runs_seq_assign_state (v := sb.thParentBase) (by
    have hdef : sb.thParentBase = sb.vListBase + 4 * n0 + 2 * (n0 * logCap) := by
      rw [hlog_eq]; rfl
    rw [hdef]; eval_expr) ?_
  intro st9 hm9 hp9 hr9_9 hf9
  have hm9' : st9.mem = mem := hm9.trans hm8'
  have hp9' : st9.pos = pos := hp9.trans hp8'
  have ha9 : ∀ j < 10, st9.regs j = rval j := fun j hj => by
    by_cases hjk : j = 9
    · subst j; exact hr9_9
    · exact (hf9 j hjk).trans (ha8 j (by omega))
  -- Step 10
  have hr9_6 : st9.regs 6 = n0 := ha9 6 (by decide)
  have hr9_9' : st9.regs 9 = sb.thParentBase := ha9 9 (by decide)
  refine runs_seq_assign_state (v := sb.origVertBase) (by
    have hdef : sb.origVertBase = sb.thParentBase + n0 := rfl
    rw [hdef]; eval_expr) ?_
  intro st10 hm10 hp10 hr10_10 hf10
  have hm10' : st10.mem = mem := hm10.trans hm9'
  have hp10' : st10.pos = pos := hp10.trans hp9'
  have ha10 : ∀ j < 11, st10.regs j = rval j := fun j hj => by
    by_cases hjk : j = 10
    · subst j; exact hr10_10
    · exact (hf10 j hjk).trans (ha9 j (by omega))
  -- Step 11
  have hr10_1 : st10.regs 1 = vCap := ha10 1 (by decide)
  have hr10_10' : st10.regs 10 = sb.origVertBase := ha10 10 (by decide)
  refine runs_seq_assign_state (v := sb.isOrigBase) (by
    have hdef : sb.isOrigBase = sb.origVertBase + vCap := rfl
    rw [hdef]; eval_expr) ?_
  intro st11 hm11 hp11 hr11_11 hf11
  have hm11' : st11.mem = mem := hm11.trans hm10'
  have hp11' : st11.pos = pos := hp11.trans hp10'
  have ha11 : ∀ j < 12, st11.regs j = rval j := fun j hj => by
    by_cases hjk : j = 11
    · subst j; exact hr11_11
    · exact (hf11 j hjk).trans (ha10 j (by omega))
  -- Step 12
  have hr11_1 : st11.regs 1 = vCap := ha11 1 (by decide)
  have hr11_11' : st11.regs 11 = sb.isOrigBase := ha11 11 (by decide)
  refine runs_seq_assign_state (v := sb.qBufABase) (by
    have hdef : sb.qBufABase = sb.isOrigBase + vCap := by dsimp only [sb, mkScanBases]; ring
    rw [hdef]; eval_expr) ?_
  intro st12 hm12 hp12 hr12_12 hf12
  have hm12' : st12.mem = mem := hm12.trans hm11'
  have hp12' : st12.pos = pos := hp12.trans hp11'
  have ha12 : ∀ j < 13, st12.regs j = rval j := fun j hj => by
    by_cases hjk : j = 12
    · subst j; exact hr12_12
    · exact (hf12 j hjk).trans (ha11 j (by omega))
  -- Step 13
  have hr12_1 : st12.regs 1 = vCap := ha12 1 (by decide)
  have hr12_12' : st12.regs 12 = sb.qBufABase := ha12 12 (by decide)
  refine runs_seq_assign_state (v := sb.cRepsBase) (by
    have hdef : sb.cRepsBase = sb.qBufABase + vCap := by dsimp only [sb, mkScanBases]; ring
    rw [hdef]; eval_expr) ?_
  intro st13 hm13 hp13 hr13_13 hf13
  have hm13' : st13.mem = mem := hm13.trans hm12'
  have hp13' : st13.pos = pos := hp13.trans hp12'
  have ha13 : ∀ j < 14, st13.regs j = rval j := fun j hj => by
    by_cases hjk : j = 13
    · subst j; exact hr13_13
    · exact (hf13 j hjk).trans (ha12 j (by omega))
  -- Step 14
  have hr13_1 : st13.regs 1 = vCap := ha13 1 (by decide)
  have hr13_13' : st13.regs 13 = sb.cRepsBase := ha13 13 (by decide)
  refine runs_seq_assign_state (v := sb.visBBase) (by
    have hdef : sb.visBBase = sb.cRepsBase + 2 * vCap := by dsimp only [sb, mkScanBases]; ring
    rw [hdef]; eval_expr) ?_
  intro st14 hm14 hp14 hr14_14 hf14
  have hm14' : st14.mem = mem := hm14.trans hm13'
  have hp14' : st14.pos = pos := hp14.trans hp13'
  have ha14 : ∀ j < 15, st14.regs j = rval j := fun j hj => by
    by_cases hjk : j = 14
    · subst j; exact hr14_14
    · exact (hf14 j hjk).trans (ha13 j (by omega))
  -- Step 15
  have hr14_0 : st14.regs 0 = g0Ptr := ha14 0 (by decide)
  have hr14_4 : st14.regs 4 = vCap0 := ha14 4 (by decide)
  refine runs_seq_assign_state (v := sb.gVListBase) (by
    have hdef : sb.gVListBase = g0Ptr + 4 + vCap0 := rfl
    rw [hdef]; eval_expr) ?_
  intro st15 hm15 hp15 hr15_15 hf15
  have hm15' : st15.mem = mem := hm15.trans hm14'
  have hp15' : st15.pos = pos := hp15.trans hp14'
  have ha15 : ∀ j < 16, st15.regs j = rval j := fun j hj => by
    by_cases hjk : j = 15
    · subst j; exact hr15_15
    · exact (hf15 j hjk).trans (ha14 j (by omega))
  -- Step 16
  have hr15_0 : st15.regs 0 = g0Ptr := ha15 0 (by decide)
  have hr15_4 : st15.regs 4 = vCap0 := ha15 4 (by decide)
  refine runs_seq_assign_state (v := sb.gExtToIntBase) (by
    have hdef : sb.gExtToIntBase = g0Ptr + 4 + 3 * vCap0 := rfl
    rw [hdef]; eval_expr) ?_
  intro st16 hm16 hp16 hr16_16 hf16
  have hm16' : st16.mem = mem := hm16.trans hm15'
  have hp16' : st16.pos = pos := hp16.trans hp15'
  have ha16 : ∀ j < 17, st16.regs j = rval j := fun j hj => by
    by_cases hjk : j = 16
    · subst j; exact hr16_16
    · exact (hf16 j hjk).trans (ha15 j (by omega))
  -- Step 17
  have hr16_0 : st16.regs 0 = g0Ptr := ha16 0 (by decide)
  have hr16_4 : st16.regs 4 = vCap0 := ha16 4 (by decide)
  refine runs_seq_assign_state (v := sb.gIntToExtBase) (by
    have hdef : sb.gIntToExtBase = g0Ptr + 4 + 4 * vCap0 := rfl
    rw [hdef]; eval_expr) ?_
  intro st17 hm17 hp17 hr17_17 hf17
  have hm17' : st17.mem = mem := hm17.trans hm16'
  have hp17' : st17.pos = pos := hp17.trans hp16'
  have ha17 : ∀ j < 18, st17.regs j = rval j := fun j hj => by
    by_cases hjk : j = 17
    · subst j; exact hr17_17
    · exact (hf17 j hjk).trans (ha16 j (by omega))
  -- Step 18
  have hr17_0 : st17.regs 0 = g0Ptr := ha17 0 (by decide)
  have hr17_4 : st17.regs 4 = vCap0 := ha17 4 (by decide)
  refine runs_seq_assign_state (v := sb.gIncHeadBase) (by
    have hdef : sb.gIncHeadBase = g0Ptr + 4 + 6 * vCap0 := rfl
    rw [hdef]; eval_expr) ?_
  intro st18 hm18 hp18 hr18_18 hf18
  have hm18' : st18.mem = mem := hm18.trans hm17'
  have hp18' : st18.pos = pos := hp18.trans hp17'
  have ha18 : ∀ j < 19, st18.regs j = rval j := fun j hj => by
    by_cases hjk : j = 18
    · subst j; exact hr18_18
    · exact (hf18 j hjk).trans (ha17 j (by omega))
  -- Step 19
  have hr18_0 : st18.regs 0 = g0Ptr := ha18 0 (by decide)
  have hr18_4 : st18.regs 4 = vCap0 := ha18 4 (by decide)
  have hr18_5 : st18.regs 5 = eCap0 := ha18 5 (by decide)
  refine runs_seq_assign_state (v := sb.gETailBase) (by
    have hdef : sb.gETailBase = (g0Ptr + 4) + (7 * vCap0 + 3 * eCap0) := by
      dsimp only [sb, mkScanBases, dgETailSlotBase]; ring
    rw [hdef]; eval_expr) ?_
  intro st19 hm19 hp19 hr19_19 hf19
  have hm19' : st19.mem = mem := hm19.trans hm18'
  have hp19' : st19.pos = pos := hp19.trans hp18'
  have ha19 : ∀ j < 20, st19.regs j = rval j := fun j hj => by
    by_cases hjk : j = 19
    · subst j; exact hr19_19
    · exact (hf19 j hjk).trans (ha18 j (by omega))
  -- Step 20
  have hr19_0 : st19.regs 0 = g0Ptr := ha19 0 (by decide)
  have hr19_4 : st19.regs 4 = vCap0 := ha19 4 (by decide)
  have hr19_5 : st19.regs 5 = eCap0 := ha19 5 (by decide)
  refine runs_seq_assign_state (v := sb.gEHeadBase) (by
    have hdef : sb.gEHeadBase = (g0Ptr + 4) + (7 * vCap0 + 4 * eCap0) := by
      dsimp only [sb, mkScanBases, dgEHeadSlotBase]; ring
    rw [hdef]; eval_expr) ?_
  intro st20 hm20 hp20 hr20_20 hf20
  have hm20' : st20.mem = mem := hm20.trans hm19'
  have hp20' : st20.pos = pos := hp20.trans hp19'
  have ha20 : ∀ j < 21, st20.regs j = rval j := fun j hj => by
    by_cases hjk : j = 20
    · subst j; exact hr20_20
    · exact (hf20 j hjk).trans (ha19 j (by omega))
  -- Step 21
  have hr20_0 : st20.regs 0 = g0Ptr := ha20 0 (by decide)
  have hr20_4 : st20.regs 4 = vCap0 := ha20 4 (by decide)
  have hr20_5 : st20.regs 5 = eCap0 := ha20 5 (by decide)
  refine runs_seq_assign_state (v := sb.gHeNextBase) (by
    have hdef : sb.gHeNextBase = (g0Ptr + 4) + (7 * vCap0 + 7 * eCap0) := by
      dsimp only [sb, mkScanBases, dgHeNextBase]; ring
    rw [hdef]; eval_expr) ?_
  intro st21 hm21 hp21 hr21_21 hf21
  have hm21' : st21.mem = mem := hm21.trans hm20'
  have hp21' : st21.pos = pos := hp21.trans hp20'
  have ha21 : ∀ j < 22, st21.regs j = rval j := fun j hj => by
    by_cases hjk : j = 21
    · subst j; exact hr21_21
    · exact (hf21 j hjk).trans (ha20 j (by omega))
  have hb21 : ScanBaseRegs st21 g0Ptr vCap auxPtr logCap sb :=
    ⟨ha21 0 (by decide), ha21 1 (by decide), ha21 2 (by decide), ha21 3 (by decide),
     ha21 4 (by decide), ha21 5 (by decide), ha21 6 (by decide), ha21 7 (by decide),
     ha21 8 (by decide), ha21 9 (by decide), ha21 10 (by decide), ha21 11 (by decide),
     ha21 12 (by decide), ha21 13 (by decide), ha21 14 (by decide), ha21 15 (by decide),
     ha21 16 (by decide), ha21 17 (by decide), ha21 18 (by decide), ha21 19 (by decide),
     ha21 20 (by decide), ha21 21 (by decide)⟩
  obtain ⟨o, st', c, hr, hpost, hc⟩ := hrest st21 hb21 hm21' hp21'
  refine ⟨o, st', c, hr, hpost, ?_⟩
  dsimp only [Expr.size] at hc ⊢
  omega

private lemma initScan_cost_arith {n m c1 c2 c3 : ℕ}
    (hc1 : c1 ≤ 55 * n + 10)
    (hc2 : c2 ≤ 85 * n + 280 * m + 50 * n + 25)
    (hc3 : c3 ≤ 25 * n + 10) :
    170 + (c1 + (2 + (c2 + (c3 + 2 + 1) + 1) + 1) + 1) ≤ 500 * n + 320 * m + 250 := by
  omega

private structure ScanAddrFacts (vCap n0 auxPtr auxEnd auxHdr : ℕ)
    (sb : ScanBases) : Prop where
  vi_qb : ∀ x < vCap, sb.vIdxBase + x < sb.qBufABase
  vi_vb : ∀ x < vCap, sb.vIdxBase + x < sb.visBBase
  vl_qb : ∀ x < n0, sb.vListBase + x < sb.qBufABase
  vl_vb : ∀ x < n0, sb.vListBase + x < sb.visBBase
  io_qb : ∀ x < vCap, sb.isOrigBase + x < sb.qBufABase
  io_vb : ∀ x < vCap, sb.isOrigBase + x < sb.visBBase
  ov_qb : ∀ x < vCap, sb.origVertBase + x < sb.qBufABase
  ov_vb : ∀ x < vCap, sb.origVertBase + x < sb.visBBase
  cr_vb : ∀ x < vCap, sb.cRepsBase + x < sb.visBBase
  aux_vi : ∀ a, a < auxPtr → a < sb.vIdxBase
  aux_qb : ∀ a, a < auxPtr → a < sb.qBufABase
  aux_vb : ∀ a, a < auxPtr → a < sb.visBBase
  ae_io : ∀ a, auxEnd ≤ a → sb.isOrigBase + vCap ≤ a
  ae_vb : ∀ a, auxEnd ≤ a → sb.visBBase + vCap ≤ a
  iq_ae : sb.isOrigBase + vCap ≤ auxEnd
  vl_vb_lo : sb.vListBase + n0 ≤ sb.visBBase
  vl_qb_lo : sb.vListBase + n0 ≤ sb.qBufABase

private lemma mk_scanAddrFacts {vCap n0 auxPtr auxEnd : ℕ}
    {sb : ScanBases}
    (h_aux_vi : auxPtr + auxHdrSize ≤ sb.vIdxBase)
    (h_vi_vl : sb.vIdxBase + vCap = sb.vListBase)
    (h_vl_ov : sb.vListBase + n0 ≤ sb.origVertBase)
    (h_ov_io : sb.origVertBase + vCap = sb.isOrigBase)
    (hsb_iq : sb.isOrigBase + vCap = sb.qBufABase)
    (hsb_qc : sb.qBufABase + vCap = sb.cRepsBase)
    (hsb_cv : sb.cRepsBase + 2 * vCap = sb.visBBase)
    (hsb_vis : sb.visBBase + vCap ≤ auxEnd) :
    ScanAddrFacts vCap n0 auxPtr auxEnd auxHdrSize sb :=
  { vi_qb := fun _ hx => by omega
    vi_vb := fun _ hx => by omega
    vl_qb := fun _ hx => by omega
    vl_vb := fun _ hx => by omega
    io_qb := fun _ hx => by omega
    io_vb := fun _ hx => by omega
    ov_qb := fun _ hx => by omega
    ov_vb := fun _ hx => by omega
    cr_vb := fun _ hx => by omega
    aux_vi := fun _ ha => by omega
    aux_qb := fun _ ha => by omega
    aux_vb := fun _ ha => by omega
    ae_io := fun _ ha => by omega
    ae_vb := fun _ ha => by omega
    iq_ae := by omega
    vl_vb_lo := by omega
    vl_qb_lo := by omega }

private lemma initScan_tail_runs {w g0Ptr vCap auxPtr logCap vCap0 eCap0 : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {pos : ℕ}
    {st_s : State} {G₀ : MGraph} {vL : List ℕ} {incL : ℕ → List ℕ}
    (hw1 : 1 < 2 ^ w) (haux_lo : g0Ptr + dynGraphSize vCap0 eCap0 ≤ auxPtr)
    (hauxW : auxPtr + auxSize vCap G₀.n < 2 ^ w)
    (hn_pos : 1 ≤ G₀.n) (hvs0 : vCap0 ≤ vCap) (hvs : G₀.n ≤ vCap) (hn_vcap0 : G₀.n ≤ vCap0)
    (hdg : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hVL_len : vL.length = G₀.n) (hVL_nd : vL.Nodup) (hVL_mem : ∀ v, v ∈ vL ↔ v ∈ G₀.V)
    (hVL_LA : ListAt mem (dgVListBase g0Ptr vCap0) vL)
    (hinc : ∀ s < vCap0,
      IsDoublyLinkedList mem (dgHePrevBase g0Ptr vCap0 eCap0)
        (dgHeNextBase g0Ptr vCap0 eCap0) (dgIncHeadBase g0Ptr vCap0 + s) (2 * eCap0) (incL s) ∧
      mem (dgSlotDegBase g0Ptr vCap0 + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCap0 ∧ h / 2 ∈ G₀.E ∧
        (if h % 2 = 0 then mem (dgETailSlotBase g0Ptr vCap0 eCap0 + h / 2)
         else mem (dgEHeadSlotBase g0Ptr vCap0 eCap0 + h / 2)) = s)
    (hvidx0 : ∀ v < vCap, mem (auxVIdxBase auxPtr + v) = 0)
    (hisorig0 : ∀ v < vCap, mem (auxIsOrigVertBase auxPtr vCap G₀.n + v) = 0)
    (hvis0 : ∀ v < vCap, mem (auxVisBBase auxPtr vCap G₀.n + v) = 0)
    (hvisA0 : ∀ v < vCap, mem (auxVisABase auxPtr vCap G₀.n + v) = 0)
    (hb_s : ScanBaseRegs st_s g0Ptr vCap auxPtr logCap
      (mkScanBases g0Ptr vCap auxPtr (auxLogCap G₀.n) vCap0 eCap0 G₀.n))
    (hmem_s : st_s.mem = mem) (_hpos_s : st_s.pos = pos) :
    ∃ o st' c, Runs w p ω
      (forRange 22 (.const 0) (.reg 6)
        (.assign 24 (.load (.bin .add (.reg 15) (.reg 22))) ;;
         .store (.bin .add (.reg 8) (.reg 22)) (.reg 24) ;;
         .store (.bin .add (.reg 7) (.reg 24)) (.bin .add (.reg 22) (.const 1)) ;;
         .store (.bin .add (.reg 10) (.reg 24)) (.reg 24) ;;
         .store (.bin .add (.reg 11) (.reg 24)) (.const 1)) ;;
       .assign 23 (.const 0) ;;
       forRange 22 (.const 0) (.reg 6)
         (.assign 24 (.load (.bin .add (.reg 8) (.reg 22))) ;;
          .cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 24))) (.const 0))
            (.store (.bin .add (.reg 13) (.reg 23)) (.reg 24) ;;
             .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
             .store (.bin .add (.reg 14) (.reg 24)) (.const 1) ;;
             .store (.reg 12) (.reg 24) ;;
             .assign 25 (.const 0) ;;
             .assign 26 (.const 1) ;;
             initScanBfsCompStmt)
            .nop) ;;
       forRange 22 (.const 0) (.reg 6)
         (.assign 24 (.load (.bin .add (.reg 8) (.reg 22))) ;;
          .store (.bin .add (.reg 14) (.reg 24)) (.const 0)) ;;
       .ret (.reg 23)) st_s o st' c ∧
      (∃ ret, o = .returned ret ∧ (initScanContract w G₀).post [g0Ptr, vCap, auxPtr, logCap] mem ret st'.mem) ∧
      170 + c ≤ (initScanContract w G₀).cost [g0Ptr, vCap, auxPtr, logCap] mem := by
  let auxEnd := auxPtr + auxSize vCap G₀.n
  let sb := mkScanBases g0Ptr vCap auxPtr (auxLogCap G₀.n) vCap0 eCap0 G₀.n
  have hsb_bounds := scanBases_bounds (g0Ptr := g0Ptr) (vCap := vCap) (auxPtr := auxPtr)
    (vCap0 := vCap0) (eCap0 := eCap0) (n0 := G₀.n) haux_lo hn_vcap0 hvs
  have hsb_eq' := scanBases_eq g0Ptr vCap auxPtr vCap0 eCap0 G₀.n
  have hauxW' : auxEnd < 2 ^ w := hauxW
  have hdg_copy := hdg
  have hvlt0 := hdg.2.1
  have hn_eq : mem (g0Ptr + dgNOff) = G₀.n := hdg.2.2.2.2.2.1
  have hm_eq : mem (g0Ptr + dgMOff) = G₀.m := hdg.2.2.2.2.2.2.1
  have hvL_LA_s : ListAt st_s.mem sb.gVListBase vL := hmem_s ▸ hVL_LA
  rcases hsb_bounds with ⟨hg_lo, _, _, _, _, _, _, h_aux_vi, h_vi_vl, h_vl_ov, h_ov_io,
    hsb_iq, hsb_qc, hsb_cv, hsb_vis⟩
  have hg_lo' : sb.gVListBase + G₀.n ≤ auxPtr := hg_lo
  have h_aux_vi' : auxPtr + auxHdrSize ≤ sb.vIdxBase := h_aux_vi
  have h_vi_vl' : sb.vIdxBase + vCap = sb.vListBase := h_vi_vl
  have h_vl_ov' : sb.vListBase + G₀.n ≤ sb.origVertBase := h_vl_ov
  have h_ov_io' : sb.origVertBase + vCap = sb.isOrigBase := h_ov_io
  have hsb_iq' : sb.isOrigBase + vCap = sb.qBufABase := hsb_iq
  have hsb_qc' : sb.qBufABase + vCap = sb.cRepsBase := hsb_qc
  have hsb_cv' : sb.cRepsBase + 2 * vCap = sb.visBBase := hsb_cv
  have hsb_vis' : sb.visBBase + vCap ≤ auxEnd := hsb_vis
  have haf := mk_scanAddrFacts h_aux_vi' h_vi_vl' h_vl_ov' h_ov_io'
    hsb_iq' hsb_qc' hsb_cv' hsb_vis'
  have hcopy := initScan_copy_runs (p := p) (ω := ω) hw1 hauxW' hvlt0 hvs0
    hVL_len hVL_nd hVL_mem hvL_LA_s
    h_aux_vi' h_vi_vl' h_vl_ov' h_ov_io'
    haf.iq_ae hg_lo' hb_s rfl
    (fun v hv => by rw [hmem_s]; simpa [sb, hsb_eq'.1] using hvidx0 v hv)
    (fun v hv => by rw [hmem_s]; simpa [sb, hsb_eq'.2.2.2.1] using hisorig0 v hv)
  obtain ⟨st1, c1, hr1, hb1, hvL1, hvI1, hvI0_1, hIO1, hOV1, hfr1, hc1⟩ := hcopy
  set st1_23 : State := { st1 with regs := Function.update st1.regs 23 0 }
  have hr_r23 : Runs w p ω (.assign 23 (.const 0)) st1 .normal st1_23 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  have hb1_23 : ScanBaseRegs st1_23 g0Ptr vCap auxPtr logCap sb :=
    scanBaseRegs_upd hb1 23 0 (by decide)
  have hagree1 : ∀ a < g0Ptr + dynGraphSize vCap0 eCap0, st1_23.mem a = mem a := fun a ha => by
    dsimp [st1_23]; rw [hfr1 a (Or.inl (haf.aux_vi a (lt_of_lt_of_le ha haux_lo))), hmem_s]
  have hsb_rel : sb.gExtToIntBase = dgExtToIntBase g0Ptr vCap0 ∧
      sb.gIntToExtBase = dgIntToExtBase g0Ptr vCap0 ∧
      sb.gIncHeadBase = dgIncHeadBase g0Ptr vCap0 ∧
      sb.gETailBase = dgETailSlotBase g0Ptr vCap0 eCap0 ∧
      sb.gEHeadBase = dgEHeadSlotBase g0Ptr vCap0 eCap0 ∧
      sb.gHeNextBase = dgHeNextBase g0Ptr vCap0 eCap0 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have houter := initScan_outer_runs (p := p) (ω := ω) hw1 hauxW' hdg_copy hinc hagree1
    hvs hvs0 hn_pos haux_lo (by omega) hsb_qc' hsb_cv' hsb_vis'
    hsb_rel hb1_23 rfl (by simp [st1_23]) hVL_len hVL_nd hVL_mem hvL1
    haf.vl_qb_lo (fun v hv => by
      dsimp [st1_23]
      have h1 : sb.isOrigBase + vCap ≤ sb.visBBase + v := by
        calc sb.isOrigBase + vCap = sb.qBufABase := hsb_iq'
          _ ≤ sb.visBBase := by omega
          _ ≤ sb.visBBase + v := Nat.le_add_right _ _
      rw [hfr1 _ (Or.inr (Or.inr h1)), hmem_s]
      simpa [sb, hsb_eq'.2.2.2.2.2.2] using hvis0 v hv)
  obtain ⟨st2, c2, repList, hr2, hb2, hrep_pos, hrep_le, hrep_nd, hr23_2, hrep0_2, hrepLA2,
    hcomp2, hvis1_2, hvisOut_2, hfr2, hc2⟩ := houter
  have hclear := initScan_clear_runs (p := p) (ω := ω) hw1 hauxW'
    (fun v hv => lt_of_lt_of_le (hvlt0 v hv) hvs0)
    hVL_len hVL_mem (fun i hi => by
      rw [hfr2 _ (Or.inl (haf.vl_qb i (hVL_len ▸ hi)))]
      exact hvL1 i hi)
    haf.vl_vb_lo hsb_vis' hb2 rfl hvisOut_2
  obtain ⟨st3, c3, hr3, hb3, hr23_3, hvis_clr3, hfr3, hc3⟩ := hclear
  have hret_ev : Expr.eval w st3 (.reg 23) = some repList.length := by
    simp [Expr.eval, hr23_3, hr23_2]
  have hr4 : Runs w p ω (.ret (.reg 23)) st3 (.returned repList.length) st3 2 :=
    runs_ret_iff.mpr ⟨repList.length, hret_ev, rfl, rfl, rfl⟩
  refine ⟨.returned repList.length, st3, c1 + (2 + (c2 + (c3 + 2 + 1) + 1) + 1) + 1,
    WordRAM.runs_seq_iff.mpr (Or.inr ⟨st1, c1, _, hr1,
      WordRAM.runs_seq_iff.mpr (Or.inr ⟨st1_23, 2, _, hr_r23,
        WordRAM.runs_seq_iff.mpr (Or.inr ⟨st2, c2, _, hr2,
          WordRAM.runs_seq_iff.mpr (Or.inr ⟨st3, c3, 2, hr3, hr4, rfl⟩),
          rfl⟩),
        rfl⟩),
      rfl⟩),
    ⟨repList.length, rfl, ?_⟩, ?_⟩
  · refine ⟨g0Ptr, vCap, auxPtr, logCap, vCap0, eCap0, vL, repList, rfl, hdg_copy,
      hVL_len, hVL_nd, hVL_mem,
      fun i hi => by
        have hin : i < G₀.n := hVL_len ▸ hi
        rw [← hsb_eq'.2.1, hfr3 _ (Or.inl (haf.vl_vb i hin)), hfr2 _ (Or.inl (haf.vl_qb i hin))]
        exact hvL1 i hi,
      fun i hi => by
        have hvlt := lt_of_lt_of_le (hvlt0 _ ((hVL_mem _).mp (List.getElem_mem hi))) hvs0
        rw [← hsb_eq'.1, hfr3 _ (Or.inl (haf.vi_vb _ hvlt)), hfr2 _ (Or.inl (haf.vi_qb _ hvlt))]
        exact hvI1 i hi,
      fun v hv hnv => by
        rw [← hsb_eq'.1, hfr3 _ (Or.inl (haf.vi_vb v hv)), hfr2 _ (Or.inl (haf.vi_qb v hv))]
        exact hvI0_1 v hv hnv,
      fun v hv => by
        rw [← hsb_eq'.2.2.2.1, hfr3 _ (Or.inl (haf.io_vb v hv)), hfr2 _ (Or.inl (haf.io_qb v hv))]
        exact hIO1 v hv,
      fun w' hw' hwc => by
        rw [← hsb_eq'.2.2.1, hfr3 _ (Or.inl (haf.ov_vb w' hwc)), hfr2 _ (Or.inl (haf.ov_qb w' hwc))]
        exact hOV1 w' hw' hwc,
      fun v hv => ⟨by
        have hA : auxVisABase auxPtr vCap G₀.n + v = sb.cRepsBase + vCap + v := by
          rw [hsb_eq'.2.2.2.2.2.1]; simp only [auxVisABase]
        have h1 : sb.isOrigBase + vCap ≤ sb.cRepsBase + vCap + v := by omega
        rw [hA, hfr3 _ (Or.inl (by omega)), hfr2 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
        show st1.mem _ = _
        rw [hfr1 _ (Or.inr (Or.inr h1)), hmem_s, ← hA]
        exact hvisA0 v hv,
        by rw [← hsb_eq'.2.2.2.2.2.2]; exact hvis_clr3 v hv⟩,
      hrep_pos, hrep_le, rfl, hrep_nd, hrep0_2,
      fun i hi => by
        have hiv : i < vCap := lt_of_lt_of_le (lt_of_lt_of_le hi hrep_le) hvs
        rw [← hsb_eq'.2.2.2.2.2.1, hfr3 _ (Or.inl (haf.cr_vb i hiv))]
        exact hrepLA2 i hi,
      hcomp2, fun a ha => ?_⟩
    rcases ha with ha | ha
    · rw [hfr3 a (Or.inl (haf.aux_vb a ha)), hfr2 a (Or.inl (haf.aux_qb a ha)),
        hfr1 a (Or.inl (haf.aux_vi a ha)), hmem_s]
    · rw [hfr3 a (Or.inr (haf.ae_vb a ha)), hfr2 a (Or.inr (Or.inr (haf.ae_vb a ha))),
        hfr1 a (Or.inr (Or.inr (haf.ae_io a ha))), hmem_s]
  · have hget0 : ([g0Ptr, vCap, auxPtr, logCap] : List ℕ).getD 0 0 = g0Ptr := rfl
    dsimp [initScanContract]
    rw [hget0, hn_eq, hm_eq]
    exact initScan_cost_arith hc1 hc2 hc3

lemma initScan_runs_of_pre {w : ℕ} {G₀ : MGraph} {p : Program} {ω : ℕ → Bool}
    {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ}
    (hpre : (initScanContract w G₀).pre args mem) :
    ∃ ret st' c, Runs w p ω initScanStmt (startState args mem pos) (.returned ret) st' c ∧
      (initScanContract w G₀).post args mem ret st'.mem ∧
      c ≤ (initScanContract w G₀).cost args mem := by
  rcases hpre with ⟨g0Ptr, vCap, auxPtr, logCap, vCap0, eCap0, rfl,
    hw16, hn_pos, _, hvs0, hlog_eq, haux_lo, hauxW, hdg, hvidx0, hisorig0, hvisAB⟩
  have hdg_copy := hdg
  rcases hdg with ⟨_, hvlt0, _, hvcap0_eq, hecap0_eq, hn_eq, _, _,
    ⟨vL, hVL_len, hVL_nd, hVL_mem, hVL_LA, _⟩, _, _, _, _, _, ⟨incL, hinc⟩⟩
  have hn_vcap0 : G₀.n ≤ vCap0 := by
    have hsub : G₀.V ⊆ Finset.range vCap0 := fun v hv => Finset.mem_range.mpr (hvlt0 v hv)
    simpa [MGraph.n] using Finset.card_le_card hsub
  have hvs : G₀.n ≤ vCap := le_trans hn_vcap0 hvs0
  have hw1 : 1 < 2 ^ w := by omega
  suffices h : ∃ o st' c, Runs w p ω initScanStmt (startState [g0Ptr, vCap, auxPtr, logCap] mem pos) o st' c ∧
      (∃ ret, o = .returned ret ∧ (initScanContract w G₀).post [g0Ptr, vCap, auxPtr, logCap] mem ret st'.mem) ∧
      c ≤ (initScanContract w G₀).cost [g0Ptr, vCap, auxPtr, logCap] mem by
    rcases h with ⟨_, st', c, hr, ⟨ret, rfl, hp⟩, hc⟩
    exact ⟨ret, st', c, hr, hp, hc⟩
  refine initScan_setup_runs hw16 hn_pos hn_vcap0 hvs0 hlog_eq haux_lo hauxW
    hvcap0_eq hecap0_eq hn_eq ?_
  intro st_s hb_s hmem_s hpos_s
  exact initScan_tail_runs hw1 haux_lo hauxW hn_pos hvs0 hvs hn_vcap0 hdg_copy
    hVL_len hVL_nd hVL_mem hVL_LA hinc hvidx0 hisorig0 (fun v hv => (hvisAB v hv).2)
    (fun v hv => (hvisAB v hv).1) hb_s hmem_s hpos_s

theorem initScan_meetsContract {w : ℕ} {G₀ : MGraph} {p : Program} {idx : ℕ}
    (hproc : p.procs[idx]? = some initScanStmt) :
    MeetsContract w p idx (initScanContract w G₀) := by
  refine meetsContract_of_runs hproc fun _ _ _ _ _ hpre => ?_
  obtain ⟨ret, st', c, hr, hp, hc⟩ := initScan_runs_of_pre hpre
  exact ⟨.returned ret, st', c, hr, hp, hc⟩

end

end MinCostFlow.LSF.Program
