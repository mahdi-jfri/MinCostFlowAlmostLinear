module

public import MinCostFlow.SparseCore.Program.RestartIface
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import WordRAM.Logic

import WordRAM.Tactic

/-!
# Exporting a `DynGraphAt` into `ExportAt` (`AssemblyFirstExport`)

Implements and verifies the deterministic Word-RAM procedure `asmFirstExportDynGraphStmt`
(`[gPtr, h]`): given a valid graph `G` stored in `DynGraphAt mem gPtr vCap eCap G` below `h`,
writes the `4`-word header `[n, h + 4, m, h + 4 + n]`, the `n`-word vertex list, and the
`3 * m`-word edge triple list `(e, G.tail e, G.head e)` into `[h, h + 4 + n + 3 * m)`, returning
`h + 4 + n + 3 * m`.

Produces `ExportAt st'.mem h o.value G` in exact space `4 + G.n + 3 * G.m` and time
`≤ 200 * (G.n + G.m + 1)` with zero modification below `h`. This directly supplies both graph
exports (`ASM_BR_GEXP` for `G` and `ASM_BR_SEXP` for `tr₀.S_cur`) required by `AsmBrCoreInitAt`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## Procedure -/

@[expose] public section

/-- **Export `DynGraphAt` into `ExportAt`**, `[gPtr, h]`.
Writes `[n, h + 4, m, h + 4 + n]`, `vL[0..n)`, and `(e, tail e, head e)` for `eL[0..m)` into
`[h, h + 4 + n + 3 * m)`, returning `h + 4 + n + 3 * m`. -/
def asmFirstExportDynGraphStmt : Stmt :=
  .assign 2 (.load (.reg 0)) ;;                                                   -- vCap
  .assign 3 (.load (.bin .add (.reg 0) (.const 1))) ;;                            -- eCap
  .assign 4 (.load (.bin .add (.reg 0) (.const 2))) ;;                            -- n
  .assign 5 (.load (.bin .add (.reg 0) (.const 3))) ;;                            -- m
  .assign 6 (.bin .add (.reg 1) (.const 4)) ;;                                    -- vPtr := h + 4
  .assign 7 (.bin .add (.reg 6) (.reg 4)) ;;                                      -- ePtr := h + 4 + n
  .assign 8 (.bin .add (.reg 7) (.bin .mul (.const 3) (.reg 5))) ;;               -- hEnd
  .store (.reg 1) (.reg 4) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.reg 6) ;;
  .store (.bin .add (.reg 1) (.const 2)) (.reg 5) ;;
  .store (.bin .add (.reg 1) (.const 3)) (.reg 7) ;;
  .assign 9 (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 2)) ;;               -- vListBase
  .assign 10 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 2))) ;; -- intToExtBase
  .assign 11 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 7) (.reg 2))) (.reg 3)) ;;                                 -- eListBase
  .assign 12 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 7) (.reg 2))) (.bin .mul (.const 3) (.reg 3))) ;;          -- eTailSlotBase
  .assign 13 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 7) (.reg 2))) (.bin .mul (.const 4) (.reg 3))) ;;          -- eHeadSlotBase
  forRange 14 (.const 0) (.reg 4)
    (.store (.bin .add (.reg 6) (.reg 14)) (.load (.bin .add (.reg 9) (.reg 14)))) ;;
  forRange 14 (.const 0) (.reg 5)
    (.assign 15 (.load (.bin .add (.reg 11) (.reg 14))) ;;                        -- e
     .assign 16 (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 12) (.reg 15))))) ;; -- tail e
     .assign 17 (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 13) (.reg 15))))) ;; -- head e
     .assign 18 (.bin .add (.reg 7) (.bin .mul (.const 3) (.reg 14))) ;;          -- dst
     .store (.reg 18) (.reg 15) ;;
     .store (.bin .add (.reg 18) (.const 1)) (.reg 16) ;;
     .store (.bin .add (.reg 18) (.const 2)) (.reg 17)) ;;
  .ret (.reg 8)

end

/-! ## Determinism -/

public section

theorem asmFirstExportDynGraphStmt_noRand : asmFirstExportDynGraphStmt.NoRand := by
  simp [asmFirstExportDynGraphStmt, forRange, forUp, Stmt.NoRand]

end

/-! ## Private verification helpers -/

private lemma runs_seq_assign_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {s₂ : Stmt} {mem : ℕ → ℕ} {regs : ℕ → ℕ} {pos v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w ⟨mem, regs, pos⟩ = some v)
    (h₂ : ∃ o st' c, Runs w p ω s₂ ⟨mem, Function.update regs r v, pos⟩ o st' c ∧ Q o st' ∧
      (k + e.size + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.assign r e ;; s₂) ⟨mem, regs, pos⟩ o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h₂ with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', e.size + 1 + c + 1,
    runs_seq_iff.mpr (Or.inr ⟨⟨mem, Function.update regs r v, pos⟩, e.size + 1, c,
      runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr, rfl⟩),
    hq, by omega⟩

private lemma runs_seq_store_flat {w : ℕ} {p : Program} {ω : ℕ → Bool} {ea ev : Expr}
    {s₂ : Stmt} {mem : ℕ → ℕ} {regs : ℕ → ℕ} {pos a v k T : ℕ} {Q : Outcome → State → Prop}
    (ha : ea.eval w ⟨mem, regs, pos⟩ = some a) (hv : ev.eval w ⟨mem, regs, pos⟩ = some v)
    (h₂ : ∃ o st' c, Runs w p ω s₂ ⟨Function.update mem a v, regs, pos⟩ o st' c ∧ Q o st' ∧
      (k + ea.size + ev.size + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.store ea ev ;; s₂) ⟨mem, regs, pos⟩ o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h₂ with ⟨o, st', c, hr, hq, hc⟩
  exact ⟨o, st', ea.size + ev.size + 1 + c + 1,
    runs_seq_iff.mpr (Or.inr ⟨⟨Function.update mem a v, regs, pos⟩, ea.size + ev.size + 1, c,
      runs_store_iff.mpr ⟨a, v, ha, hv, rfl, rfl, rfl⟩, hr, rfl⟩),
    hq, by omega⟩

private lemma runs_seq_split_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt}
    {st : State} {k T₁ T : ℕ} {P₁ : State → Prop} {Q : Outcome → State → Prop}
    (h₁ : ∃ o₁ st₁ c₁, Runs w p ω s₁ st o₁ st₁ c₁ ∧ (o₁ = .normal ∧ P₁ st₁) ∧ 0 + c₁ ≤ T₁)
    (h₂ : ∀ st₁, P₁ st₁ →
      ∃ o₂ st₂ c₂, Runs w p ω s₂ st₁ o₂ st₂ c₂ ∧ Q o₂ st₂ ∧ (k + T₁ + 1) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (s₁ ;; s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases h₁ with ⟨_, st₁, c₁, hr₁, ⟨rfl, hp₁⟩, hc₁⟩
  rcases h₂ st₁ hp₁ with ⟨o₂, st₂, c₂, hr₂, hq₂, hc₂⟩
  exact ⟨o₂, st₂, c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩),
    hq₂, by omega⟩

private lemma readList_eq_of_forall {mem : ℕ → ℕ} {a : ℕ} {L : List ℕ}
    (h : ∀ i (hi : i < L.length), mem (a + i) = L[i]'hi) :
    readList mem a L.length = L := by
  refine List.ext_getElem (by simp [readList]) fun i hi _ => ?_
  simp only [readList, List.getElem_map, List.getElem_range]
  exact h i (by simpa [readList] using hi)

private lemma readTriples_eq_of_forall {mem : ℕ → ℕ} {a : ℕ} {L : List (ℕ × ℕ × ℕ)}
    (h : ∀ i (hi : i < L.length),
      mem (a + 3 * i) = (L[i]'hi).1 ∧
      mem (a + 3 * i + 1) = (L[i]'hi).2.1 ∧
      mem (a + 3 * i + 2) = (L[i]'hi).2.2) :
    readTriples mem a L.length = L := by
  refine List.ext_getElem (by simp [readTriples]) fun i hi _ => ?_
  have hi' : i < L.length := by simpa [readTriples] using hi
  obtain ⟨h1, h2, h3⟩ := h i hi'
  simp only [readTriples, List.getElem_map, List.getElem_range]
  exact Prod.ext h1 (Prod.ext h2 h3)

private lemma export_post_of_mem {w vCap eCap h : ℕ} {G : MGraph} {vL eL : List ℕ}
    {mem : ℕ → ℕ}
    (hGval : G.IsValid) (hVlt : ∀ v ∈ G.V, v < vCap) (hElt : ∀ e ∈ G.E, e < eCap)
    (hvLen : vL.length = G.n) (hvNd : vL.Nodup) (hvMem : ∀ v, v ∈ vL ↔ v ∈ G.V)
    (heLen : eL.length = G.m) (heNd : eL.Nodup) (heMem : ∀ e, e ∈ eL ↔ e ∈ G.E)
    (hvCapW : vCap < 2 ^ w) (heCapW : eCap < 2 ^ w)
    (hsp : h + 4 + G.n + 3 * G.m < 2 ^ w)
    (m0 : mem h = G.n) (m1 : mem (h + 1) = h + 4)
    (m2 : mem (h + 2) = G.m) (m3 : mem (h + 3) = h + 4 + G.n)
    (hvC : ∀ j (hj : j < vL.length), mem (h + 4 + j) = vL[j]'hj)
    (heC : ∀ j (_hj : j < G.m), ∀ hjm : j < eL.length,
      mem (h + 4 + G.n + 3 * j) = eL[j]'hjm ∧
      mem (h + 4 + G.n + 3 * j + 1) = G.tail (eL[j]'hjm) ∧
      mem (h + 4 + G.n + 3 * j + 2) = G.head (eL[j]'hjm)) :
    let hEnd := h + 4 + G.n + 3 * G.m
    ExportAt mem h hEnd G ∧ ∀ a, h ≤ a → a < hEnd → mem a < 2 ^ w := by
  intro hEnd
  have hvListEq : readList mem (mem (h + 1)) (mem h) = vL := by
    rw [m1, m0, ← hvLen]; exact readList_eq_of_forall hvC
  set eTrips : List (ℕ × ℕ × ℕ) := eL.map fun e => (e, G.tail e, G.head e)
  have heTripsEq : readTriples mem (mem (h + 3)) (mem (h + 2)) = eTrips := by
    rw [m3, m2]
    have hlen : eTrips.length = G.m := by simp [eTrips, heLen]
    rw [← hlen]
    refine readTriples_eq_of_forall fun i hi => ?_
    have hiL : i < eL.length := by simpa [eTrips] using hi
    obtain ⟨a1, a2, a3⟩ := heC i (heLen ▸ hiL) hiL
    simpa [eTrips] using And.intro a1 (And.intro a2 a3)
  refine ⟨?_, ?_⟩
  · dsimp only [ExportAt]
    rw [hvListEq, heTripsEq, m0, m1, m2, m3]
    refine ⟨rfl, rfl, hvNd, hvMem, ?_, ?_, ?_, by omega, by omega, by omega, by omega, by omega⟩
    · simpa [eTrips, Function.comp_def] using heNd
    · intro t ht
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
      exact ⟨(heMem e).mp he, rfl, rfl⟩
    · intro e he
      exact ⟨(e, G.tail e, G.head e), List.mem_map.mpr ⟨e, (heMem e).mpr he, rfl⟩, rfl⟩
  · intro a ha1 ha2
    by_cases h0 : a = h
    · rw [h0, m0]; omega
    by_cases h1 : a = h + 1
    · rw [h1, m1]; omega
    by_cases h2 : a = h + 2
    · rw [h2, m2]; omega
    by_cases h3 : a = h + 3
    · rw [h3, m3]; omega
    by_cases h4 : a < h + 4 + G.n
    · set j := a - (h + 4)
      have hj : j < vL.length := by omega
      have hae : a = h + 4 + j := by omega
      rw [hae, hvC j hj]
      have := hVlt _ ((hvMem _).mp (List.getElem_mem hj))
      omega
    · set off := a - (h + 4 + G.n)
      set j := off / 3
      have hj : j < eL.length := by omega
      have hrem : off % 3 = 0 ∨ off % 3 = 1 ∨ off % 3 = 2 := by omega
      obtain ⟨a1, a2, a3⟩ := heC j (heLen ▸ hj) hj
      have heG : eL[j]'hj ∈ G.E := (heMem _).mp (List.getElem_mem hj)
      rcases hrem with hr | hr | hr
      · have hae : a = h + 4 + G.n + 3 * j := by omega
        rw [hae, a1]; have := hElt _ heG; omega
      · have hae : a = h + 4 + G.n + 3 * j + 1 := by omega
        rw [hae, a2]; have := hVlt _ (hGval _ heG).1; omega
      · have hae : a = h + 4 + G.n + 3 * j + 2 := by omega
        rw [hae, a3]; have := hVlt _ (hGval _ heG).2; omega

/-! ## Main verification theorem -/

public section

/-- **Verification of `asmFirstExportDynGraphStmt`**: exports `DynGraphAt mem₀ gPtr vCap eCap G`
into `ExportAt st'.mem h (h + 4 + G.n + 3 * G.m) G` in exact space `4 + G.n + 3 * G.m` and time
`≤ 200 * (G.n + G.m + 1)`. -/
theorem asmFirstExportDynGraph_runs {w gPtr vCap eCap h pos : ℕ} {p : Program}
    {G : MGraph} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hG : DynGraphAt mem₀ gPtr vCap eCap G)
    (hG_le : gPtr + dynGraphSize vCap eCap ≤ h)
    (hz : ZeroFrom mem₀ h)
    (hsp : h + 4 + G.n + 3 * G.m < 2 ^ w) :
    ∃ o st' c,
      Runs w p ω asmFirstExportDynGraphStmt (startState [gPtr, h] mem₀ pos) o st' c ∧
      o.value = h + 4 + G.n + 3 * G.m ∧
      ExportAt st'.mem h o.value G ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem₀ a) ∧
      (∀ a, h ≤ a → a < o.value → st'.mem a < 2 ^ w) ∧
      c ≤ 200 * (G.n + G.m + 1) := by
  obtain ⟨hGval, hVlt, hElt, hmVCap, hmECap, hmN, hmM, _,
    ⟨vL, hvLen, hvNd, hvMem, hvLA, _⟩, hE2I, _, _,
    ⟨eL, heLen, heNd, heMem, heLA, _⟩, hETailHead, _⟩ := hG
  have hdgSize : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hG_w : gPtr + (4 + 7 * vCap + 9 * eCap) < 2 ^ w := by omega
  have hvL_lt : ∀ i (hi : i < vL.length), vL[i]'hi < vCap := fun i hi =>
    hVlt _ ((hvMem _).mp (List.getElem_mem hi))
  have heL_lt : ∀ i (hi : i < eL.length), eL[i]'hi < eCap := fun i hi =>
    hElt _ ((heMem _).mp (List.getElem_mem hi))
  have htail_mem : ∀ e ∈ G.E, mem₀ (dgIntToExtBase gPtr vCap + mem₀ (dgETailSlotBase gPtr vCap eCap + e)) = G.tail e := by
    intro e he
    rw [(hETailHead e he).1]
    exact (hE2I (G.tail e) (hGval e he).1).2
  have hhead_mem : ∀ e ∈ G.E, mem₀ (dgIntToExtBase gPtr vCap + mem₀ (dgEHeadSlotBase gPtr vCap eCap + e)) = G.head e := by
    intro e he
    rw [(hETailHead e he).2]
    exact (hE2I (G.head e) (hGval e he).2).2
  have htailSlot_lt : ∀ e ∈ G.E, mem₀ (dgETailSlotBase gPtr vCap eCap + e) < vCap := fun e he => by
    rw [(hETailHead e he).1]
    exact hVlt _ (hE2I (G.tail e) (hGval e he).1).1
  have hheadSlot_lt : ∀ e ∈ G.E, mem₀ (dgEHeadSlotBase gPtr vCap eCap + e) < vCap := fun e he => by
    rw [(hETailHead e he).2]
    exact hVlt _ (hE2I (G.head e) (hGval e he).2).1
  have hn_le_vCap : G.n ≤ vCap := by
    calc G.n = vL.length := hvLen.symm
      _ = vL.toFinset.card := (List.toFinset_card_of_nodup hvNd).symm
      _ ≤ (Finset.range vCap).card := Finset.card_le_card fun v hv =>
          Finset.mem_range.mpr (hVlt v ((hvMem v).mp (List.mem_toFinset.mp hv)))
      _ = vCap := Finset.card_range vCap
  have hm_le_eCap : G.m ≤ eCap := by
    calc G.m = eL.length := heLen.symm
      _ = eL.toFinset.card := (List.toFinset_card_of_nodup heNd).symm
      _ ≤ (Finset.range eCap).card := Finset.card_le_card fun x hx =>
          Finset.mem_range.mpr (hElt x ((heMem x).mp (List.mem_toFinset.mp hx)))
      _ = eCap := Finset.card_range eCap
  set hEnd := h + 4 + G.n + 3 * G.m
  -- Loop 1 invariant (copies `vL[0..i)` into `[h + 4, h + 4 + i)`)
  let inv1 : ℕ → State → Prop := fun i st =>
    st.regs 4 = G.n ∧ st.regs 5 = G.m ∧ st.regs 6 = h + 4 ∧ st.regs 7 = h + 4 + G.n ∧
    st.regs 8 = hEnd ∧ st.regs 9 = dgVListBase gPtr vCap ∧
    st.regs 10 = dgIntToExtBase gPtr vCap ∧ st.regs 11 = dgEListBase gPtr vCap eCap ∧
    st.regs 12 = dgETailSlotBase gPtr vCap eCap ∧ st.regs 13 = dgEHeadSlotBase gPtr vCap eCap ∧
    st.regs 14 = i ∧
    st.mem h = G.n ∧ st.mem (h + 1) = h + 4 ∧ st.mem (h + 2) = G.m ∧ st.mem (h + 3) = h + 4 + G.n ∧
    (∀ j (hj : j < i), ∀ hjn : j < vL.length, st.mem (h + 4 + j) = vL[j]'hjn) ∧
    ZeroFrom st.mem (h + 4 + i) ∧ (∀ a < h, st.mem a = mem₀ a)
  have hloop1 := Triple.forRange_le (w := w) (p := p) (r := 14) (lo := .const 0) (hi := .reg 4)
    (body := .store (.bin .add (.reg 6) (.reg 14)) (.load (.bin .add (.reg 9) (.reg 14))))
    (P := fun st => inv1 0 { st with regs := Function.update st.regs 14 0 })
    (Inv := inv1) (fun _ => 12) 0 G.n (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const (by omega), hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.1)
    (fun i _ hi st ω hI => by
      obtain ⟨r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, m0, m1, m2, m3, hcp, hzf, hfr⟩ := hI
      have hiL : i < vL.length := hvLen.symm ▸ hi
      have hsrc : st.mem (dgVListBase gPtr vCap + i) = vL[i]'hiL := by
        rw [hfr _ (by simp only [dgVListBase]; omega)]
        exact hvLA i hiL
      have hval_lt : dgVListBase gPtr vCap + i < 2 ^ w := by
        simp only [dgVListBase]; omega
      refine ⟨.normal, { st with mem := Function.update st.mem (h + 4 + i) (vL[i]'hiL) },
        (Expr.bin .add (.reg 6) (.reg 14)).size + (Expr.load (.bin .add (.reg 9) (.reg 14))).size + 1,
        runs_store_iff.mpr ⟨h + 4 + i, vL[i]'hiL,
          Expr.eval_add (Expr.eval_reg_of_eq r6) (Expr.eval_reg_of_eq r14) (by omega),
          Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r9) (Expr.eval_reg_of_eq r14) hval_lt) hsrc,
          rfl, rfl, rfl⟩,
        ⟨⟨by simp [r4], by simp [r5], by simp [r6], by simp [r7], by simp [r8], by simp [r9],
          by simp [r10], by simp [r11], by simp [r12], by simp [r13], by simp,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact m0,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact m1,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact m2,
          by dsimp only; rw [Function.update_of_ne (by omega)]; exact m3,
          fun j hj hjn => by
            by_cases hji : j = i
            · subst hji; simp [Function.update_self]
            · dsimp only; rw [Function.update_of_ne (by omega)]; exact hcp j (by omega) hjn,
          fun x hx => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hzf x (by omega),
          fun a ha => by dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a ha⟩,
          r14⟩,
        by simp [Expr.size]⟩)
  -- Loop 2 invariant (copies `(e, tail e, head e)` for `eL[0..i)` into `[h + 4 + n, h + 4 + n + 3 * i)`)
  let inv2 : ℕ → State → Prop := fun i st =>
    st.regs 4 = G.n ∧ st.regs 5 = G.m ∧ st.regs 6 = h + 4 ∧ st.regs 7 = h + 4 + G.n ∧
    st.regs 8 = hEnd ∧ st.regs 9 = dgVListBase gPtr vCap ∧
    st.regs 10 = dgIntToExtBase gPtr vCap ∧ st.regs 11 = dgEListBase gPtr vCap eCap ∧
    st.regs 12 = dgETailSlotBase gPtr vCap eCap ∧ st.regs 13 = dgEHeadSlotBase gPtr vCap eCap ∧
    st.regs 14 = i ∧
    st.mem h = G.n ∧ st.mem (h + 1) = h + 4 ∧ st.mem (h + 2) = G.m ∧ st.mem (h + 3) = h + 4 + G.n ∧
    (∀ j (hj : j < vL.length), st.mem (h + 4 + j) = vL[j]'hj) ∧
    (∀ j (hj : j < i), ∀ hjm : j < eL.length,
      st.mem (h + 4 + G.n + 3 * j) = eL[j]'hjm ∧
      st.mem (h + 4 + G.n + 3 * j + 1) = G.tail (eL[j]'hjm) ∧
      st.mem (h + 4 + G.n + 3 * j + 2) = G.head (eL[j]'hjm)) ∧
    ZeroFrom st.mem (h + 4 + G.n + 3 * i) ∧ (∀ a < h, st.mem a = mem₀ a)
  let body2 : Stmt :=
    .assign 15 (.load (.bin .add (.reg 11) (.reg 14))) ;;
    .assign 16 (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 12) (.reg 15))))) ;;
    .assign 17 (.load (.bin .add (.reg 10) (.load (.bin .add (.reg 13) (.reg 15))))) ;;
    .assign 18 (.bin .add (.reg 7) (.bin .mul (.const 3) (.reg 14))) ;;
    .store (.reg 18) (.reg 15) ;;
    .store (.bin .add (.reg 18) (.const 1)) (.reg 16) ;;
    .store (.bin .add (.reg 18) (.const 2)) (.reg 17)
  have hloop2 := Triple.forRange_le (w := w) (p := p) (r := 14) (lo := .const 0) (hi := .reg 5)
    (body := body2)
    (P := fun st => inv2 0 { st with regs := Function.update st.regs 14 0 })
    (Inv := inv2) (fun _ => 70) 0 G.m (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const (by omega), hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.1)
    (fun i _ hi st ω hI => by
      obtain ⟨r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, m0, m1, m2, m3, hvC, heC, hzf, hfr⟩ := hI
      have hiL : i < eL.length := heLen.symm ▸ hi
      set e := eL[i]'hiL
      have heG : e ∈ G.E := (heMem e).mp (List.getElem_mem hiL)
      have heLt : e < eCap := hElt e heG
      have hsrcE : st.mem (dgEListBase gPtr vCap eCap + i) = e := by
        rw [hfr _ (by simp only [dgEListBase]; omega)]; exact heLA i hiL
      have hts_eq : st.mem (dgETailSlotBase gPtr vCap eCap + e) = mem₀ (dgETailSlotBase gPtr vCap eCap + e) :=
        hfr _ (by simp only [dgETailSlotBase]; omega)
      have hhs_eq : st.mem (dgEHeadSlotBase gPtr vCap eCap + e) = mem₀ (dgEHeadSlotBase gPtr vCap eCap + e) :=
        hfr _ (by simp only [dgEHeadSlotBase]; omega)
      have ht_eq : st.mem (dgIntToExtBase gPtr vCap + mem₀ (dgETailSlotBase gPtr vCap eCap + e)) = G.tail e := by
        have := htailSlot_lt e heG
        rw [hfr _ (by simp only [dgIntToExtBase]; omega)]; exact htail_mem e heG
      have hh_eq : st.mem (dgIntToExtBase gPtr vCap + mem₀ (dgEHeadSlotBase gPtr vCap eCap + e)) = G.head e := by
        have := hheadSlot_lt e heG
        rw [hfr _ (by simp only [dgIntToExtBase]; omega)]; exact hhead_mem e heG
      have htSlotLt := htailSlot_lt e heG
      have hhSlotLt := hheadSlot_lt e heG
      suffices hmain : ∃ o st' c, Runs w p ω body2 st o st' c ∧
          normalPost (fun st₁ =>
            inv2 (i + 1) { st₁ with regs := Function.update st₁.regs 14 (i + 1) } ∧ st₁.regs 14 = i) o st' ∧
          0 + c ≤ 70 by
        obtain ⟨o, st', c, hr, hp, hc⟩ := hmain; exact ⟨o, st', c, hr, hp, by dsimp only; omega⟩
      dsimp only [body2]
      refine runs_seq_assign_flat (v := e)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r11) (Expr.eval_reg_of_eq r14)
          (by simp only [dgEListBase]; omega)) hsrcE) ?_
      refine runs_seq_assign_flat (v := G.tail e)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r10]))
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r12]))
            (Expr.eval_reg_of_eq (by simp)) (by simp only [dgETailSlotBase]; omega)) hts_eq)
          (by simp only [dgIntToExtBase]; omega)) ht_eq) ?_
      refine runs_seq_assign_flat (v := G.head e)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r10]))
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r13]))
            (Expr.eval_reg_of_eq (by simp)) (by simp only [dgEHeadSlotBase]; omega)) hhs_eq)
          (by simp only [dgIntToExtBase]; omega)) hh_eq) ?_
      refine runs_seq_assign_flat (v := h + 4 + G.n + 3 * i)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r7]))
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [r14])) (by omega))
          (by omega)) ?_
      refine runs_seq_store_flat (a := h + 4 + G.n + 3 * i) (v := e)
        (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) ?_
      refine runs_seq_store_flat (a := h + 4 + G.n + 3 * i + 1) (v := G.tail e)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_reg_of_eq (by simp)) ?_
      refine ⟨.normal, _, (Expr.bin .add (.reg 18) (.const 2)).size + (Expr.reg 17).size + 1,
        runs_store_iff.mpr ⟨h + 4 + G.n + 3 * i + 2, G.head e,
          Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) (by omega),
          Expr.eval_reg_of_eq (by simp), rfl, rfl, rfl⟩,
        ⟨⟨by simp [r4], by simp [r5], by simp [r6], by simp [r7], by simp [r8], by simp [r9],
          by simp [r10], by simp [r11], by simp [r12], by simp [r13], by simp,
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact m0,
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact m1,
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact m2,
          by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact m3,
          fun j hj => by
            have hjN : j < G.n := hvLen ▸ hj
            dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hvC j hj,
          fun j hj hjm => by
            by_cases hji : j = i
            · subst hji
              exact ⟨by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_self],
                by dsimp only; rw [Function.update_of_ne (by omega), Function.update_self],
                by dsimp only; rw [Function.update_self]⟩
            · obtain ⟨a1, a2, a3⟩ := heC j (by omega) hjm
              exact ⟨by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]; exact a1,
                by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]; exact a2,
                by dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]; exact a3⟩,
          fun x hx => by
            dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hzf x (by omega),
          fun a ha => by
            dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]; exact hfr a ha⟩,
          by simp [r14]⟩,
        by simp [Expr.size]⟩)
  -- Main flat sequence
  suffices hmain : ∃ o st' c,
      Runs w p ω asmFirstExportDynGraphStmt (startState [gPtr, h] mem₀ pos) o st' c ∧
      (o.value = hEnd ∧ ExportAt st'.mem h o.value G ∧ ZeroFrom st'.mem o.value ∧
        (∀ a < h, st'.mem a = mem₀ a) ∧ (∀ a, h ≤ a → a < o.value → st'.mem a < 2 ^ w)) ∧
      0 + c ≤ 200 * (G.n + G.m + 1) by
    obtain ⟨o, st', c, hr, ⟨h1, h2, h3, h4, h5⟩, hc⟩ := hmain
    exact ⟨o, st', c, hr, h1, h2, h3, h4, h5, by omega⟩
  have hrc1 : rangeCost (fun _ => 12) 0 G.n = 12 * G.n := by
    simp [rangeCost, Nat.mul_comm]
  have hrc2 : rangeCost (fun _ => 70) 0 G.m = 70 * G.m := by
    simp [rangeCost, Nat.mul_comm]
  dsimp only [asmFirstExportDynGraphStmt, startState]
  refine runs_seq_assign_flat (v := vCap)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (v := gPtr) (by simp))
      (by simpa [dgVCapOff] using hmVCap)) ?_
  refine runs_seq_assign_flat (v := eCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := gPtr) (by simp))
      (Expr.eval_const (by omega)) (by omega)) (by simpa [dgECapOff] using hmECap)) ?_
  refine runs_seq_assign_flat (v := G.n)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := gPtr) (by simp))
      (Expr.eval_const (by omega)) (by omega)) (by simpa [dgNOff] using hmN)) ?_
  refine runs_seq_assign_flat (v := G.m)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := gPtr) (by simp))
      (Expr.eval_const (by omega)) (by omega)) (by simpa [dgMOff] using hmM)) ?_
  refine runs_seq_assign_flat (v := h + 4)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp)) (Expr.eval_const (by omega)) (by omega)) ?_
  refine runs_seq_assign_flat (v := h + 4 + G.n)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := h + 4) (by simp)) (Expr.eval_reg_of_eq (v := G.n) (by simp))
      (by omega)) ?_
  refine runs_seq_assign_flat (v := hEnd)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := h + 4 + G.n) (by simp))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := G.m) (by simp)) (by omega))
      (by omega)) ?_
  refine runs_seq_store_flat (a := h) (v := G.n)
    (Expr.eval_reg_of_eq (v := h) (by simp)) (Expr.eval_reg_of_eq (v := G.n) (by simp)) ?_
  refine runs_seq_store_flat (a := h + 1) (v := h + 4)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp)) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := h + 4) (by simp)) ?_
  refine runs_seq_store_flat (a := h + 2) (v := G.m)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp)) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := G.m) (by simp)) ?_
  refine runs_seq_store_flat (a := h + 3) (v := h + 4 + G.n)
    (Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp)) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (v := h + 4 + G.n) (by simp)) ?_
  refine runs_seq_assign_flat (v := dgVListBase gPtr vCap)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := gPtr) (by simp))
      (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq (v := vCap) (by simp))
      (by omega)) ?_
  refine runs_seq_assign_flat (v := dgIntToExtBase gPtr vCap)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := gPtr) (by simp))
      (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := vCap) (by simp)) (by omega))
      (by omega)) ?_
  refine runs_seq_assign_flat (v := dgEListBase gPtr vCap eCap)
    (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := gPtr) (by simp))
      (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := vCap) (by simp)) (by omega))
      (by omega))
      (Expr.eval_reg_of_eq (v := eCap) (by simp))
      (by omega)) ?_
  refine runs_seq_assign_flat (v := dgETailSlotBase gPtr vCap eCap)
    (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := gPtr) (by simp))
      (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := vCap) (by simp)) (by omega))
      (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := eCap) (by simp)) (by omega))
      (by omega)) ?_
  refine runs_seq_assign_flat (v := dgEHeadSlotBase gPtr vCap eCap)
    (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (v := gPtr) (by simp))
      (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := vCap) (by simp)) (by omega))
      (by omega))
      (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := eCap) (by simp)) (by omega))
      (by omega)) ?_
  refine runs_seq_split_le (T₁ := 21 * G.n + 10) (P₁ := inv1 G.n) ?_ ?_
  · have hl1 : ∀ st, inv1 0 { st with regs := Function.update st.regs 14 0 } →
        ∃ o₁ st₁ c₁,
          Runs w p ω (forRange 14 (.const 0) (.reg 4)
            (.store (.bin .add (.reg 6) (.reg 14)) (.load (.bin .add (.reg 9) (.reg 14)))))
            st o₁ st₁ c₁ ∧ (o₁ = .normal ∧ inv1 G.n st₁) ∧ 0 + c₁ ≤ 21 * G.n + 10 := by
      intro st hpre
      obtain ⟨o₁, st₁, c₁, hr₁, hp₁, hc₁⟩ := hloop1 st ω hpre
      cases o₁ with
      | returned _ => cases hp₁
      | normal =>
        dsimp only at hc₁; rw [hrc1] at hc₁; simp only [Nat.sub_zero, Expr.size] at hc₁
        exact ⟨.normal, st₁, c₁, hr₁, ⟨rfl, hp₁⟩, by omega⟩
    apply hl1
    exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp,
      by simp [Function.update],
      by simp [Function.update],
      by simp [Function.update],
      by simp [Function.update],
      fun j hj => by omega,
      fun x hx => by
        simp [Function.update, show x ≠ h + 3 by omega, show x ≠ h + 2 by omega,
          show x ≠ h + 1 by omega, show x ≠ h by omega, hz x (by omega)],
      fun a ha => by
        simp [Function.update, show a ≠ h + 3 by omega, show a ≠ h + 2 by omega,
          show a ≠ h + 1 by omega, show a ≠ h by omega]⟩
  · intro st1 hI1
    obtain ⟨r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, -, m0, m1, m2, m3, hvC, hzf1, hfr1⟩ := hI1
    refine runs_seq_split_le (T₁ := 79 * G.m + 10) (P₁ := inv2 G.m) ?_ ?_
    · have hl2 : ∀ st, inv2 0 { st with regs := Function.update st.regs 14 0 } →
          ∃ o₂ st₂ c₂,
            Runs w p ω (forRange 14 (.const 0) (.reg 5) body2) st o₂ st₂ c₂ ∧
            (o₂ = .normal ∧ inv2 G.m st₂) ∧ 0 + c₂ ≤ 79 * G.m + 10 := by
        intro st hpre
        obtain ⟨o₂, st₂, c₂, hr₂, hp₂, hc₂⟩ := hloop2 st ω hpre
        cases o₂ with
        | returned _ => cases hp₂
        | normal =>
          dsimp only at hc₂; rw [hrc2] at hc₂; simp only [Nat.sub_zero, Expr.size] at hc₂
          exact ⟨.normal, st₂, c₂, hr₂, ⟨rfl, hp₂⟩, by omega⟩
      apply hl2
      exact ⟨by simp [r4], by simp [r5], by simp [r6], by simp [r7], by simp [r8], by simp [r9],
        by simp [r10], by simp [r11], by simp [r12], by simp [r13], by simp,
        m0, m1, m2, m3, fun j hj => hvC j (hvLen ▸ hj) hj, fun j hj => by omega,
        by simpa using hzf1, hfr1⟩
    · intro st2 hI2
      obtain ⟨-, -, -, -, r8, -, -, -, -, -, -, m0, m1, m2, m3, hvC, heC, hzf2, hfr2⟩ := hI2
      obtain ⟨hexp, hwords⟩ := export_post_of_mem hGval hVlt hElt hvLen hvNd hvMem heLen heNd heMem
        (by omega) (by omega) hsp m0 m1 m2 m3 hvC heC
      refine ⟨.returned hEnd, st2, (Expr.reg 8).size + 1,
        runs_ret_iff.mpr ⟨hEnd, Expr.eval_reg_of_eq r8, rfl, rfl, rfl⟩,
        ⟨rfl, hexp, hzf2, hfr2, hwords⟩, ?_⟩
      simp only [Expr.size]; clear * -; omega

end

end MinCostFlow.SparseCore.Program
