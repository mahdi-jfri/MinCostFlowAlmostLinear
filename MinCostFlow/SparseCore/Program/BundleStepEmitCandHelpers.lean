module

public import MinCostFlow.SparseCore.Program.BundleStepEmitCandRuns
public import MinCostFlow.SparseCore.Program.BundleStepEmitMaxRun

/-!
# Shared single-candidate emission helpers (`BundleStepEmitCandHelpers`)

Provides helper lemmas shared by `BundleStepEmitCandBranch2` and `BundleStepEmitCand`:
* `runs_seq_assoc_normal`, `runs_seq_congr_right`, `foldOneSplitRuns_append`, `vRuns_len_le_ends`,
* `copy_slice_runs`: copies a CSR bucket slice `[bufPtr + lo, bufPtr + lo + m_b)` to `dstPtr`,
* `branch2_pack_sort_maxRun_runs`: prefix of Branch 2 (packs all `degB` ends via `bTourOwner`,
  sorts via `bMergeSort`, and runs `bundleStepEmitMaxRunStmt`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

lemma runs_seq_assoc_normal {w : ℕ} {pProg : Program} {ω : ℕ → Bool}
    {s₁ s₂ s₃ : Stmt} {st₀ st₂ : State} {c : ℕ}
    (h : Runs w pProg ω ((s₁ ;; s₂) ;; s₃) st₀ .normal st₂ c) :
    Runs w pProg ω (s₁ ;; (s₂ ;; s₃)) st₀ .normal st₂ c := by
  rcases runs_seq_iff.mp h with ⟨_, _, _, hne, _⟩ | ⟨_, c12, c3, h12, h3, hc⟩
  · cases hne
  · rcases runs_seq_iff.mp h12 with ⟨_, _, _, hne, _⟩ | ⟨_, c1, c2, h1, h2, hc12⟩
    · cases hne
    · have := bundle_runs_seq_normal h1 (bundle_runs_seq_normal h2 h3)
      rwa [show c1 + (c2 + c3 + 1) + 1 = c by omega] at this

lemma runs_seq_congr_right {w : ℕ} {pProg : Program} {ω : ℕ → Bool}
    {s₁ s₂ s₂' : Stmt} {st₀ st₂ : State} {c : ℕ}
    (h : Runs w pProg ω (s₁ ;; s₂) st₀ .normal st₂ c)
    (hmap : ∀ {st st' c'}, Runs w pProg ω s₂ st .normal st' c' → Runs w pProg ω s₂' st .normal st' c') :
    Runs w pProg ω (s₁ ;; s₂') st₀ .normal st₂ c := by
  rcases runs_seq_iff.mp h with ⟨_, _, _, hne, _⟩ | ⟨_, _, _, h1, h2, hc⟩
  · cases hne
  · exact hc ▸ bundle_runs_seq_normal h1 (hmap h2)

lemma foldOneSplitRuns_append (b : ℕ) (rs₁ rs₂ : List (ℕ × List End))
    (acc : List Update × BundleState × ℕ) :
    foldOneSplitRuns b (rs₁ ++ rs₂) acc = foldOneSplitRuns b rs₂ (foldOneSplitRuns b rs₁ acc) := by
  induction rs₁ generalizing acc with
  | nil => rfl
  | cons vr tl ih => exact ih _

lemma vRuns_len_le_ends (rs : List (ℕ × List End))
    (hpos : ∀ vr ∈ rs, 0 < vr.2.length) : rs.length ≤ vRunsEndsLen rs := by
  induction rs with
  | nil => simp [vRunsEndsLen]
  | cons r rs' ihr =>
    have h1 := hpos r List.mem_cons_self
    have h2 := ihr fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons, vRunsEndsLen, List.map_cons, List.sum_cons] at h2 ⊢; omega

lemma copy_slice_runs {w bufPtr lo dstPtr : ℕ} {pProg : Program} {ω : ℕ → Bool}
    {L : List ℕ} {st₀ : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hbuf_w : bufPtr + lo + L.length < 2 ^ w)
    (hdst_w : dstPtr + L.length < 2 ^ w)
    (hdisj : bufPtr + lo + L.length ≤ dstPtr)
    (hL_at : ListAt st₀.mem (bufPtr + lo) L)
    (hr14 : st₀.regs 14 = bufPtr) (hr27 : st₀.regs 27 = dstPtr)
    (hr28 : st₀.regs 28 = lo) (hr30 : st₀.regs 30 = L.length) :
    ∃ st1 c1,
      Runs w pProg ω
        (forRange 31 (.const 0) (.reg 30)
          (.store (.bin .add (.reg 27) (.reg 31))
            (.load (.bin .add (.reg 14) (.bin .add (.reg 28) (.reg 31))))))
        st₀ .normal st1 c1 ∧
      (∀ r ≤ 30, st1.regs r = st₀.regs r) ∧
      ListAt st1.mem dstPtr L ∧
      (∀ a, (a < dstPtr ∨ dstPtr + L.length ≤ a) → st1.mem a = st₀.mem a) ∧
      c1 ≤ 20 * L.length + 7 := by
  let Inv : ℕ → Unit → State → Prop := fun i _ st =>
    (∀ r ≤ 30, st.regs r = st₀.regs r) ∧
    st.regs 31 = i ∧
    (∀ j < i, ∀ (hj : j < L.length), st.mem (dstPtr + j) = L[j]'hj) ∧
    (∀ a, (a < dstPtr ∨ dstPtr + i ≤ a) → st.mem a = st₀.mem a)
  obtain ⟨st1, c1, _, hrun, hInvEnd, hc1⟩ :=
    runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 31) (lo := .const 0) (hi := .reg 30)
      (body := .store (.bin .add (.reg 27) (.reg 31))
        (.load (.bin .add (.reg 14) (.bin .add (.reg 28) (.reg 31)))))
      (fun _ _ => 0) Inv (fun _ => 10) L.length (by omega) (fun _ => by omega) (st₀ := st₀) (a₀ := ())
      ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega],
       ⟨fun r hr => by simp [show r ≠ 31 by omega], by simp, fun _ h => by omega, fun _ _ => rfl⟩, rfl⟩
      (fun _ _ _ _ hI => hI.2.1)
      (fun _ _ st _ hI => by simp [Expr.eval, hI.1 30 (le_refl _), hr30])
      (fun i _ st hi hI => by
        rcases hI with ⟨hregs, hr31, hcopy, hfr⟩
        have hval : st.mem (bufPtr + (lo + i)) = L[i]'hi := by
          rw [hfr (bufPtr + (lo + i)) (Or.inl (by omega)), ← Nat.add_assoc]
          exact hL_at i hi
        let m1 := Function.update st.mem (dstPtr + i) (L[i]'hi)
        have hst : Runs w pProg ω
            (.store (.bin .add (.reg 27) (.reg 31))
              (.load (.bin .add (.reg 14) (.bin .add (.reg 28) (.reg 31)))))
            st .normal { st with mem := m1 } 10 :=
          runs_store_iff.mpr ⟨dstPtr + i, L[i]'hi,
            by simp [Expr.eval, BinOp.eval, hregs 27 (by decide), hr27, hr31, show dstPtr + i < 2 ^ w by omega],
            by simp [Expr.eval, BinOp.eval, hregs 14 (by decide), hr14, hregs 28 (by decide), hr28, hr31,
              show lo + i < 2 ^ w by omega, show bufPtr + (lo + i) < 2 ^ w by omega, hval],
            rfl, rfl, by simp [Expr.size]⟩
        refine ⟨{ st with mem := m1 }, 10, (), hst, hr31,
          ⟨fun r hr => by simp [show r ≠ 31 by omega, hregs r hr], by simp, fun j hj1 hj2 => ?_, fun a ha => ?_⟩,
          rfl, by omega⟩
        · dsimp only [m1]
          by_cases hji : j = i
          · subst hji; rw [Function.update_self]
          · rw [Function.update_of_ne (by omega)]; exact hcopy j (by omega) hj2
        · dsimp only [m1]
          rw [Function.update_of_ne (by omega)]
          exact hfr a (by omega))
  have hrc : rangeCost (fun _ => 10) 0 L.length = 10 * L.length := by
    unfold rangeCost; simp [Nat.mul_comm]
  rw [hrc] at hc1; simp only [Expr.size] at hc1
  exact ⟨st1, c1, hrun, hInvEnd.1, fun i hi => hInvEnd.2.2.1 i hi hi, hInvEnd.2.2.2, by omega⟩

/-- Prefix of Branch 2: packs all `degB` ends of `b` via `bTourOwner`, sorts via `bMergeSort`,
and computes `(winStart, winEnd, winLen)` via `bundleStepEmitMaxRunStmt`. -/
lemma branch2_pack_sort_maxRun_runs {TS : BundleTourSpec} {w vCap eCap p bunCap b nB tourH
    prevBase nextBase hCur m_b : ℕ}
    {pProg : Program} {bMergeSort bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    {htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner}
    {cord' : ℕ → List End} {src' : End → ℕ} {B : BundleState}
    {tx₀ : htour.rep.τ} {st₀ : State}
    (hMergeSort : ∀ L : List ℕ, MeetsContract w pProg bMergeSort (mergeSortContract w L))
    (hw16 : 16 ≤ 2 ^ w) (htourH_w : tourH < 2 ^ w) (heCap_w : 2 * eCap < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hh_w : hCur + (6 + 2 * TS.querySpace) * m_b < 2 ^ w)
    (hV : B.vertices = Finset.range nB) (hb_lt : b < nB)
    (hdeg_le : (B.ends b).card ≤ 2 * m_b)
    (hsrc_lt : ∀ x ∈ B.ends b, src' x < vCap)
    (hsrc_mem : ∀ x ∈ B.ends b, x ∈ cord' (src' x))
    (hsrc_uniq : ∀ x ∈ B.ends b, ∀ v', x ∈ cord' v' → v' = src' x)
    (hh_blk : p + bundleSlotBlockSize bunCap ≤ hCur)
    (hh_next : nextBase + 2 * eCap ≤ hCur)
    (htrep : htour.rep.rep tourH cord' tx₀ st₀.mem)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < hCur)
    (htfoot_disj_next : ∀ a, htour.rep.foot tourH tx₀ a → a < nextBase ∨ nextBase + 2 * eCap ≤ a)
    (hzero : ZeroFrom st₀.mem hCur)
    (hrep : BundleSlotRepAt eCap prevBase nextBase p bunCap B st₀.mem)
    (hr1 : st₀.regs 1 = tourH) (hr4 : st₀.regs 4 = hCur) (hr6 : st₀.regs 6 = 2 * eCap)
    (hr7 : st₀.regs 7 = p) (hr11 : st₀.regs 11 = nextBase)
    (hr25 : st₀.regs 25 = b) (hr26 : st₀.regs 26 = (B.ends b).card) :
    let degB := (B.ends b).card
    let raw := rawByRootVRuns B B.edges src' b
    let bestIdx := maxRunIdx raw
    ∃ stMR cPref txP hP,
      (∀ {sTail stEnd cTail},
        Runs w pProg ω sTail stMR .normal stEnd cTail →
        Runs w pProg ω
          (.assign 27 (.reg 4) ;;
           .assign 4 (.bin .add (.reg 27) (.reg 26)) ;;
           .assign 28 (.load (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25))) ;;
           .assign 29 (.const 0) ;;
           .loop (.reg 28)
             (.assign 30 (.bin .sub (.reg 28) (.const 1)) ;;
              .assign 31 (.reg 4) ;;
              .call 4 bTourOwner [.reg 1, .reg 30, .reg 4] ;;
              .assign 32 (.load (.reg 31)) ;;
              .store (.bin .add (.reg 27) (.reg 29))
                (.bin .add (.bin .mul (.reg 32) (.reg 6)) (.reg 30)) ;;
              .assign 29 (.bin .add (.reg 29) (.const 1)) ;;
              .assign 28 (.load (.bin .add (.reg 11) (.reg 30)))) ;;
           .assign 28 (.reg 4) ;;
           .assign 4 (.bin .add (.reg 28) (.reg 26)) ;;
           .call 29 bMergeSort [.reg 27, .reg 26, .reg 28] ;;
           .assign 30 (.reg 26) ;;
           bundleStepEmitMaxRunStmt ;; sTail)
          st₀ .normal stEnd (cPref + cTail)) ∧
      (∀ r ≤ 26, r ≠ 4 → stMR.regs r = st₀.regs r) ∧
      stMR.regs 4 = hP + degB ∧ stMR.regs 27 = hCur ∧
      stMR.regs 31 = vRunsEndsLen (raw.take bestIdx) ∧
      stMR.regs 32 = vRunsEndsLen (raw.take (bestIdx + 1)) ∧
      hCur + degB ≤ hP ∧ hP ≤ hCur + (1 + TS.querySpace) * degB ∧
      vRunsEndsLen raw = degB ∧
      ListAt stMR.mem hCur (vRunsPacked eCap raw) ∧
      htour.rep.rep tourH cord' txP stMR.mem ∧
      (∀ a, htour.rep.foot tourH txP a → htour.rep.foot tourH tx₀ a ∨ (hCur + degB ≤ a ∧ a < hP)) ∧
      (∀ a, ¬ htour.rep.foot tourH tx₀ a → (a < hCur ∨ hP + degB ≤ a) → stMR.mem a = st₀.mem a) ∧
      cPref + htour.rep.phi tourH txP stMR.mem ≤
        (2 * TS.mul * ordStoreLog eCap + 400 * (Nat.log 2 (2 * m_b + 1) + 1) + 250) * m_b + 180 +
        htour.rep.phi tourH tx₀ st₀.mem := by
  intro degB raw bestIdx
  obtain ⟨nB', hV', hnB', hE_lt, _, _, _, _, _, hdll_all, _, _, _⟩ := hrep
  have hnB_eq : nB' = nB := by
    have := congrArg Finset.card (hV'.symm.trans hV); simpa [Finset.card_range] using this
  rw [hnB_eq] at hV' hnB' hdll_all
  obtain ⟨L_b, hdll_b, _, hmem_b⟩ := hdll_all b hb_lt
  have hL_len : L_b.length = degB := by
    have himg : (B.ends b).image endKey = L_b.toFinset := by
      ext k; simp only [Finset.mem_image, List.mem_toFinset, hmem_b]
      exact ⟨fun ⟨x, hx, heq⟩ => by subst heq; rwa [bundle_endOfKey_endKey],
        fun hk => ⟨endOfKey k, hk, bundle_endKey_endOfKey k⟩⟩
    rw [← List.toFinset_card_of_nodup hdll_b.1, ← himg, Finset.card_image_of_injective _ endKey_injective]
  have hsurv_eq : survivingEnds B B.edges b = B.ends b := by
    ext x; simp only [survivingEnds, Finset.mem_filter, BundleState.mem_ends]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  have h1q_deg_le : (1 + TS.querySpace) * degB ≤ (2 + 2 * TS.querySpace) * m_b := by
    calc (1 + TS.querySpace) * degB ≤ (1 + TS.querySpace) * (2 * m_b) := Nat.mul_le_mul_left _ hdeg_le
      _ = (2 + 2 * TS.querySpace) * m_b := by ring
  have hdeg_budget : (1 + TS.querySpace) * degB + degB + 2 * m_b ≤ (6 + 2 * TS.querySpace) * m_b := by
    have hmul : (6 + 2 * TS.querySpace) * m_b = (2 + 2 * TS.querySpace) * m_b + 2 * m_b + 2 * m_b := by ring
    omega
  obtain ⟨stP, cP, txP, hP, hrunP, hregsP, hr4P, hr27P, hhP_lo, hhP_hi, hLatP, htrP, htfP, _, hfrP, hcP⟩ :=
    bundleStepEmitCand_pack_runs (htour := htour) (ω := ω) (st₀ := st₀) (L := L_b) hw16 htourH_w heCap_w hpk_w
      hp_w hnext_w (by rw [hL_len]; omega) (lt_of_lt_of_le hb_lt hnB') hdll_b
      (fun k hk => hsrc_lt _ ((hmem_b k).mp hk))
      (fun k hk => hsrc_mem _ ((hmem_b k).mp hk))
      (fun k hk => hsrc_uniq _ ((hmem_b k).mp hk))
      htrep htfoot_lt htfoot_disj_next hzero
      (by rw [hL_len]; clear * - hh_blk h1q_deg_le; omega)
      (by rw [hL_len]; clear * - hh_next h1q_deg_le; omega)
      hr1 hr4 hr6 hr7 hr11 hr25 (by rw [hL_len]; exact hr26)
  rw [hL_len] at htfP hhP_lo hhP_hi hcP
  let r28s := Function.update stP.regs 28 hP
  let r4s := Function.update r28s 4 (hP + degB)
  have h26P : stP.regs 26 = degB := (hregsP 26 (by decide) (by decide)).trans hr26
  have ha28s : Runs w pProg ω (.assign 28 (.reg 4)) stP .normal { stP with regs := r28s } 2 :=
    runs_assign_iff.mpr ⟨hP, by simp [Expr.eval, hr4P], rfl, rfl, rfl⟩
  have ha4s : Runs w pProg ω (.assign 4 (.bin .add (.reg 28) (.reg 26)))
      { stP with regs := r28s } .normal { stP with regs := r4s } 4 :=
    runs_assign_iff.mpr ⟨hP + degB, by
      simp [Expr.eval, BinOp.eval, r28s, h26P, show hP + degB < 2 ^ w by omega], rfl, rfl, rfl⟩
  set rawPk := L_b.map fun k => packEndKey eCap (src' (endOfKey k)) k
  have hrawPk_len : rawPk.length = degB := by simp [rawPk, hL_len]
  have hrawPk_nd : rawPk.Nodup := by
    rw [List.nodup_map_iff_inj_on hdll_b.1]
    intro k₁ hk₁ k₂ hk₂ heq
    exact (packEndKey_inj (hdll_b.2.1 k₁ hk₁) (hdll_b.2.1 k₂ hk₂) heq).2
  have hrawPk_w : ∀ z ∈ rawPk, z < 2 ^ w := by
    intro z hz; obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hz
    have h1 := Nat.mul_le_mul_right (2 * eCap) (show src' (endOfKey k) + 1 ≤ vCap by
      have := hsrc_lt _ ((hmem_b k).mp hk); omega)
    have h2 := hdll_b.2.1 k hk
    unfold packEndKey; rw [Nat.add_mul, Nat.one_mul] at h1; omega
  obtain ⟨bodyS, hbodyS, oS, stS, cS, hrunS, hpostS, hcS⟩ :=
    hMergeSort rawPk [hCur, rawPk.length, hP] stP.mem stP.pos ω
      (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
      ⟨hCur, hP, rfl, hw16, by rw [hrawPk_len]; omega, by rw [hrawPk_len]; omega,
        Or.inl (by rw [hrawPk_len]; exact hhP_lo), hLatP, hrawPk_w⟩
  rcases hpostS with ⟨aS, scS, L', hargsS, _, hpermS, hsortS, hLatS, hfrS⟩
  rcases List.cons.inj hargsS with ⟨haS_eq, hargsS1⟩
  rcases List.cons.inj hargsS1 with ⟨_, hargsS2⟩
  rcases List.cons.inj hargsS2 with ⟨hscS_eq, _⟩
  rw [← haS_eq] at hLatS hfrS; rw [← hscS_eq] at hfrS
  have hL'_eq : L' = vRunsPacked eCap raw := by
    rw [sorted_perm_eq_toFinset_sort hrawPk_nd hpermS hsortS]
    have hset_eq : rawPk.toFinset = (survivingEnds B B.edges b).image fun x => packEndKey eCap (src' x) (endKey x) := by
      ext pk; simp only [rawPk, List.mem_toFinset, List.mem_map, Finset.mem_image, hsurv_eq]
      constructor
      · rintro ⟨k, hk, rfl⟩; exact ⟨endOfKey k, (hmem_b k).mp hk, by rw [bundle_endKey_endOfKey]⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨endKey x, (hmem_b _).mpr (by rwa [bundle_endOfKey_endKey]), by rw [bundle_endOfKey_endKey]⟩
    rw [hset_eq, ← rawByRootVRuns_pack_eq_sort hE_lt]; rfl
  rw [hL'_eq] at hLatS
  let stM : State := { mem := stS.mem, regs := Function.update r4s 29 oS.value, pos := stS.pos }
  have hcallS : Runs w pProg ω (.call 29 bMergeSort [.reg 27, .reg 26, .reg 28])
      { stP with regs := r4s } .normal stM (cS + 4) :=
    runs_call_iff.mpr ⟨[hCur, rawPk.length, hP], bodyS, oS, stS, cS,
      by simp [evalArgs, Expr.eval, r4s, r28s, hr27P, h26P, hrawPk_len], hbodyS, hrunS, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
  have hraw_len : vRunsEndsLen raw = degB := by
    rw [← vRunsPacked_length eCap, ← hL'_eq, hpermS.length_eq, hrawPk_len]
  have hraw_pw : (raw.map Prod.fst).Pairwise (· < ·) := rawByRootVRuns_pairwise
  have hraw_keys : ∀ vr ∈ raw, ∀ x ∈ vr.2, endKey x < 2 * eCap := fun vr hvr x hx => by
    have := hE_lt x.1 ((BundleState.mem_ends B b x).mp ((rawByRootVRuns_info vr hvr).2.2 x hx).1).1
    rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] <;> omega
  have hraw_pos : ∀ vr ∈ raw, vr.1 < vCap ∧ 0 < vr.2.length := fun vr hvr => by
    have hi := rawByRootVRuns_info vr hvr
    obtain ⟨x₀, hx₀⟩ := List.length_pos_iff_exists_mem.mp hi.1
    have hx_info := hi.2.2 x₀ hx₀
    exact ⟨hx_info.2 ▸ hsrc_lt x₀ hx_info.1, hi.1⟩
  let r30m := Function.update stM.regs 30 degB
  let stM0 : State := { stM with regs := r30m }
  have ha30 : Runs w pProg ω (.assign 30 (.reg 26)) stM .normal stM0 2 :=
    runs_assign_iff.mpr ⟨degB, by simp [Expr.eval, stM, r4s, r28s, h26P], rfl, rfl, rfl⟩
  obtain ⟨stMR, cMR, hrunMR, hmemMR, hregsMR, hr31MR, hr32MR, _, hcMR⟩ :=
    bundleStepEmitMaxRun_runs (vCap := vCap) (arr := hCur) (vruns := raw) (st₀ := stM0)
      hw16 hpk_w (by rw [hraw_len]; omega) hraw_pos hraw_pw hraw_keys hLatS
      (by simp [stM0, r30m, stM, r4s, r28s, hregsP 6 (by decide) (by decide), hr6])
      (by simp [stM0, r30m, stM, r4s, r28s, hr27P])
      (by simp [stM0, r30m, hraw_len])
  rw [hraw_len] at hcMR
  have hlocMR := htour.rep_local tourH cord' txP stP.mem stMR.mem fun a ha => by
    rw [hmemMR]; dsimp only [stM0, stM]
    refine (hfrS a ?_ ?_).symm
    · rcases htfP a ha with h0 | ⟨h1, _⟩
      · left; exact htfoot_lt a h0
      · right; rw [hrawPk_len]; exact h1
    · left; rcases htfP a ha with h0 | ⟨_, h2⟩
      · exact lt_of_lt_of_le (htfoot_lt a h0) (by omega)
      · exact h2
  refine ⟨stMR, cP + (2 + (4 + (cS + 4 + (2 + (cMR + 1) + 1) + 1) + 1) + 1) + 1, txP, hP,
    fun {sTail stEnd cTail} hTail => ?_,
    fun r hr h4 => by
      rw [hregsMR r (by omega)]
      simp only [stM0, r30m, stM, r4s, r28s, Function.update_of_ne (show r ≠ 30 by omega),
        Function.update_of_ne (show r ≠ 29 by omega), Function.update_of_ne h4,
        Function.update_of_ne (show r ≠ 28 by omega)]
      exact hregsP r (by omega) h4,
    by rw [hregsMR 4 (by decide)]; simp [stM0, r30m, stM, r4s],
    by rw [hregsMR 27 (by decide)]; simp [stM0, r30m, stM, r4s, r28s, hr27P],
    hr31MR, hr32MR, hhP_lo, hhP_hi, hraw_len, hmemMR.symm ▸ hLatS,
    hlocMR.1 htrP, htfP,
    fun a hnf ha => by
      rw [hmemMR]; dsimp only [stM0, stM]
      rw [hfrS a (by rw [hrawPk_len]; omega) (by rw [hrawPk_len]; omega), hfrP a hnf (by omega)],
    ?_⟩
  · have htail0 := bundle_runs_seq_normal ha28s (bundle_runs_seq_normal ha4s (bundle_runs_seq_normal hcallS
      (bundle_runs_seq_normal ha30 (bundle_runs_seq_normal hrunMR hTail))))
    have hfull := runs_seq_congr_right (runs_seq_assoc_normal (bundle_runs_seq_normal hrunP htail0))
      (fun h => runs_seq_congr_right (runs_seq_assoc_normal h)
        (fun h => runs_seq_congr_right (runs_seq_assoc_normal h) (fun h => runs_seq_assoc_normal h)))
    convert hfull using 1; omega
  · dsimp only [mergeSortContract] at hcS
    rw [hrawPk_len] at hcS
    rw [hlocMR.2.symm]
    have hlog_le : Nat.log 2 (degB + 1) ≤ Nat.log 2 (2 * m_b + 1) := Nat.log_mono_right (by omega)
    have hsort_le : 200 * degB * (Nat.log 2 (degB + 1) + 1) ≤
        400 * m_b * (Nat.log 2 (2 * m_b + 1) + 1) := by
      calc 200 * degB * (Nat.log 2 (degB + 1) + 1)
          ≤ 200 * (2 * m_b) * (Nat.log 2 (2 * m_b + 1) + 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hdeg_le) (by omega)
        _ = 400 * m_b * (Nat.log 2 (2 * m_b + 1) + 1) := by ring
    have htour_le : (TS.mul * ordStoreLog eCap + 42) * degB ≤
        (2 * TS.mul * ordStoreLog eCap + 84) * m_b := by
      calc (TS.mul * ordStoreLog eCap + 42) * degB
          ≤ (TS.mul * ordStoreLog eCap + 42) * (2 * m_b) := Nat.mul_le_mul_left _ hdeg_le
        _ = (2 * TS.mul * ordStoreLog eCap + 84) * m_b := by ring
    have hmul_tot : (2 * TS.mul * ordStoreLog eCap + 400 * (Nat.log 2 (2 * m_b + 1) + 1) + 250) * m_b =
        (2 * TS.mul * ordStoreLog eCap + 84) * m_b + 400 * m_b * (Nat.log 2 (2 * m_b + 1) + 1) +
        166 * m_b := by ring
    clear * - hcP hcS hcMR hdeg_le hsort_le htour_le hmul_tot
    omega

end

end MinCostFlow.SparseCore.Program
