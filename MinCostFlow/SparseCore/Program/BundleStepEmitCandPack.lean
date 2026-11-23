module

public import MinCostFlow.SparseCore.Program.BundleStepEmitOneRunPost

/-!
# Phase 3 single-candidate splitting verification (`BundleStepEmitCand`)

Verifies `bundleStepEmitOneCandStmt bDllPush bDllErase bMergeSort bTourOwner`:
1. `bundleStepEmitCand_pack_runs`: walks the bundle's doubly-linked list, queries `bTourOwner` for
   each end, and writes packed `(v, key)` words into `packArr`.
2. `bundleStepEmitCand_skip0_runs`: skips the lexicographically first core-vertex group `xs0`
   (which stays in bundle `b`).
3. `bundleStepEmitCand_runsLoop`: iterates `bundleStepEmitOneRunStmt` over `rest = vruns.drop 1`,
   preserving `BundleSlotRepAt`, accumulating `BatchBodyAt`, and reproducing `foldOneSplitRuns`.
4. `bundleStepEmitOneCand_runs`: combines both `degB = 0` and `degB > 0` branches (including
   `bMergeSort` and `byRootVRuns_pack_eq_sort`) to match `runsFoldStep` exactly.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Concatenated packed-key words for a list of `(v, xs)` runs. -/
def vRunsPacked (eCap : ℕ) (rs : List (ℕ × List End)) : List ℕ :=
  rs.flatMap fun vr => vr.2.map fun x => packEndKey eCap vr.1 (endKey x)

/-- Total number of ends across a list of `(v, xs)` runs. -/
def vRunsEndsLen (rs : List (ℕ × List End)) : ℕ :=
  (rs.map fun vr => vr.2.length).sum

/-- Total batch words emitted by `rest : List (ℕ × List End)` (each run takes `5 + xs.length`). -/
def vRunsBatchWords (rs : List (ℕ × List End)) : ℕ :=
  (rs.map fun vr => 5 + vr.2.length).sum

end

public section

lemma vRunsPacked_length (eCap : ℕ) (rs : List (ℕ × List End)) :
    (vRunsPacked eCap rs).length = vRunsEndsLen rs := by
  induction rs with
  | nil => rfl
  | cons vr tl ih => simp [vRunsPacked, vRunsEndsLen]

lemma vRunsBatchWords_le (rs : List (ℕ × List End)) (hpos : ∀ vr ∈ rs, 0 < vr.2.length) :
    vRunsBatchWords rs ≤ 6 * vRunsEndsLen rs := by
  induction rs with
  | nil => simp [vRunsBatchWords, vRunsEndsLen]
  | cons vr tl ih =>
    have h1 := hpos vr List.mem_cons_self
    have h2 := ih fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    simp only [vRunsBatchWords, vRunsEndsLen, List.map_cons, List.sum_cons] at h2 ⊢
    omega

/-! ## 1. DLL walk & packed-key fill (`bundleStepEmitCand_pack_runs`) -/

lemma bundleStepEmitCand_pack_runs {TS : BundleTourSpec} {w vCap eCap p bunCap b
    tourH prevBase nextBase hCur : ℕ}
    {pProg : Program} {bTourList bTourLen bTourOwner : ℕ} {ω : ℕ → Bool}
    {htour : BundleTourAt TS w vCap eCap pProg bTourList bTourLen bTourOwner}
    {cord' : ℕ → List End} {src' : End → ℕ} {L : List ℕ} {tx₀ : htour.rep.τ} {st₀ : State}
    (hw16 : 16 ≤ 2 ^ w)
    (htourH_w : tourH < 2 ^ w) (heCap_w : 2 * eCap < 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (hp_w : p + bundleSlotBlockSize bunCap < 2 ^ w)
    (hnext_w : nextBase + 2 * eCap < 2 ^ w)
    (hh_w : hCur + (1 + TS.querySpace) * L.length < 2 ^ w)
    (hb_lt : b < bunCap)
    (hdll : IsDoublyLinkedList st₀.mem prevBase nextBase (bsHeadBase p + b) (2 * eCap) L)
    (hsrc_lt : ∀ k ∈ L, src' (endOfKey k) < vCap)
    (hsrc_mem : ∀ k ∈ L, endOfKey k ∈ cord' (src' (endOfKey k)))
    (hsrc_uniq : ∀ k ∈ L, ∀ v', endOfKey k ∈ cord' v' → v' = src' (endOfKey k))
    (htrep : htour.rep.rep tourH cord' tx₀ st₀.mem)
    (htfoot_lt : ∀ a, htour.rep.foot tourH tx₀ a → a < hCur)
    (htfoot_disj_next : ∀ a, htour.rep.foot tourH tx₀ a → a < nextBase ∨ nextBase + 2 * eCap ≤ a)
    (hzero : ZeroFrom st₀.mem hCur)
    (hh_disj_blk : hCur + (1 + TS.querySpace) * L.length ≤ p ∨ p + bundleSlotBlockSize bunCap ≤ hCur)
    (hh_disj_next : hCur + (1 + TS.querySpace) * L.length ≤ nextBase ∨ nextBase + 2 * eCap ≤ hCur)
    (hr1 : st₀.regs 1 = tourH) (hr4 : st₀.regs 4 = hCur) (hr6 : st₀.regs 6 = 2 * eCap)
    (hr7 : st₀.regs 7 = p) (hr11 : st₀.regs 11 = nextBase) (hr25 : st₀.regs 25 = b)
    (hr26 : st₀.regs 26 = L.length) :
    ∃ st1 c1 tx1 h1,
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
            .assign 28 (.load (.bin .add (.reg 11) (.reg 30))))) st₀ .normal st1 c1 ∧
      (∀ r ≤ 26, r ≠ 4 → st1.regs r = st₀.regs r) ∧
      st1.regs 4 = h1 ∧ st1.regs 27 = hCur ∧
      hCur + L.length ≤ h1 ∧ h1 ≤ hCur + (1 + TS.querySpace) * L.length ∧
      ListAt st1.mem hCur (L.map fun k => packEndKey eCap (src' (endOfKey k)) k) ∧
      htour.rep.rep tourH cord' tx1 st1.mem ∧
      (∀ a, htour.rep.foot tourH tx1 a →
        htour.rep.foot tourH tx₀ a ∨ (hCur + L.length ≤ a ∧ a < h1)) ∧
      ZeroFrom st1.mem h1 ∧
      (∀ a, ¬ htour.rep.foot tourH tx₀ a → (a < hCur ∨ h1 ≤ a) → st1.mem a = st₀.mem a) ∧
      c1 + htour.rep.phi tourH tx1 st1.mem ≤
        (TS.mul * ordStoreLog eCap + 42) * L.length + 25 + htour.rep.phi tourH tx₀ st₀.mem := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have hL_lt : ∀ k ∈ L, k < 2 * eCap := hdll.2.1
  have hdeg_w : L.length < 2 ^ w := by
    have : L.length ≤ (1 + TS.querySpace) * L.length := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hhd_val := hdll.2.2.1
  -- 4 setup assigns
  let r27 := Function.update st₀.regs 27 hCur
  let r4 := Function.update r27 4 (hCur + L.length)
  let r28 := Function.update r4 28 (st₀.mem (bsHeadBase p + b))
  let r29 := Function.update r28 29 0
  let stA : State := { st₀ with regs := r29 }
  have ha27 : Runs w pProg ω (.assign 27 (.reg 4)) st₀ .normal { st₀ with regs := r27 } 2 :=
    runs_assign_iff.mpr ⟨hCur, by simp [Expr.eval, hr4], rfl, rfl, rfl⟩
  have ha4 : Runs w pProg ω (.assign 4 (.bin .add (.reg 27) (.reg 26)))
      { st₀ with regs := r27 } .normal { st₀ with regs := r4 } 4 :=
    runs_assign_iff.mpr ⟨hCur + L.length, by
      simp [Expr.eval, BinOp.eval, r27, hr26,
        show hCur + L.length < 2 ^ w by
          have := Nat.le_mul_of_pos_left L.length (show 0 < 1 + TS.querySpace by omega); omega],
      rfl, rfl, rfl⟩
  have ha28 : Runs w pProg ω (.assign 28 (.load (.bin .add (.bin .add (.reg 7) (.const 3)) (.reg 25))))
      { st₀ with regs := r4 } .normal { st₀ with regs := r28 } 7 :=
    runs_assign_iff.mpr ⟨st₀.mem (bsHeadBase p + b), by
      simp [Expr.eval, BinOp.eval, r4, r27, hr7, hr25, h3_w, bsHeadBase,
        show p + 3 < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega,
        show p + 3 + b < 2 ^ w by unfold bundleSlotBlockSize at hp_w; omega],
      rfl, rfl, by simp [Expr.size]⟩
  have ha29 : Runs w pProg ω (.assign 29 (.const 0)) { st₀ with regs := r28 } .normal stA 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  let loopBody : Stmt :=
    .assign 30 (.bin .sub (.reg 28) (.const 1)) ;;
    .assign 31 (.reg 4) ;;
    .call 4 bTourOwner [.reg 1, .reg 30, .reg 4] ;;
    .assign 32 (.load (.reg 31)) ;;
    .store (.bin .add (.reg 27) (.reg 29))
      (.bin .add (.bin .mul (.reg 32) (.reg 6)) (.reg 30)) ;;
    .assign 29 (.bin .add (.reg 29) (.const 1)) ;;
    .assign 28 (.load (.bin .add (.reg 11) (.reg 30)))
  have hloop : ∀ rem i (hi : i ≤ L.length) (hrem : L.length - i = rem) (st : State) (tx : htour.rep.τ) (hI : ℕ),
      (∀ r ≤ 26, r ≠ 4 → st.regs r = st₀.regs r) →
      st.regs 4 = hI → st.regs 27 = hCur → st.regs 29 = i →
      st.regs 28 = (if h : i < L.length then L[i]'h + 1 else 0) →
      hCur + L.length ≤ hI → hI ≤ hCur + L.length + TS.querySpace * i →
      ListAt st.mem hCur ((L.take i).map fun k => packEndKey eCap (src' (endOfKey k)) k) →
      htour.rep.rep tourH cord' tx st.mem →
      (∀ a, htour.rep.foot tourH tx a → htour.rep.foot tourH tx₀ a ∨ (hCur + L.length ≤ a ∧ a < hI)) →
      ZeroFrom st.mem hI →
      (∀ a, ¬ htour.rep.foot tourH tx₀ a → (a < hCur ∨ hI ≤ a) → st.mem a = st₀.mem a) →
      ∃ stF cF txF hF,
        Runs w pProg ω (.loop (.reg 28) loopBody) st .normal stF cF ∧
        (∀ r ≤ 26, r ≠ 4 → stF.regs r = st₀.regs r) ∧
        stF.regs 4 = hF ∧ stF.regs 27 = hCur ∧
        hI ≤ hF ∧ hF ≤ hCur + L.length + TS.querySpace * L.length ∧
        ListAt stF.mem hCur (L.map fun k => packEndKey eCap (src' (endOfKey k)) k) ∧
        htour.rep.rep tourH cord' txF stF.mem ∧
        (∀ a, htour.rep.foot tourH txF a → htour.rep.foot tourH tx₀ a ∨ (hCur + L.length ≤ a ∧ a < hF)) ∧
        ZeroFrom stF.mem hF ∧
        (∀ a, ¬ htour.rep.foot tourH tx₀ a → (a < hCur ∨ hF ≤ a) → stF.mem a = st₀.mem a) ∧
        cF + htour.rep.phi tourH txF stF.mem ≤
          (TS.mul * ordStoreLog eCap + 42) * rem + 2 + htour.rep.phi tourH tx st.mem := by
    intro rem
    induction rem with
    | zero =>
      intro i hi hrem st tx hI hregs hr4I hr27I hr29I hr28I hh_lo hh_hi hLat htr htf hzf hfr
      have hi_eq : i = L.length := by omega
      subst hi_eq
      rw [dite_eq_right (by omega : ¬ L.length < L.length)] at hr28I
      rw [List.take_length] at hLat
      refine ⟨st, 2, tx, hI, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr28I], rfl, rfl, rfl⟩),
        hregs, hr4I, hr27I, le_refl _, hh_hi, hLat, htr, htf, hzf, hfr, by omega⟩
    | succ rem ih =>
      intro i hi hrem st tx hI hregs hr4I hr27I hr29I hr28I hh_lo hh_hi hLat htr htf hzf hfr
      have hi_lt : i < L.length := by omega
      set k := L[i]'hi_lt
      have hk_mem : k ∈ L := List.getElem_mem hi_lt
      have hk_lt : k < 2 * eCap := hL_lt k hk_mem
      have hv_lt : src' (endOfKey k) < vCap := hsrc_lt k hk_mem
      have hpk_lt : packEndKey eCap (src' (endOfKey k)) k < 2 ^ w := by
        unfold packEndKey
        have h1 : (src' (endOfKey k) + 1) * (2 * eCap) ≤ vCap * (2 * eCap) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at h1; omega
      have hhI_sp : hI + TS.querySpace < 2 ^ w := by
        have h1 : L.length + TS.querySpace * (i + 1) ≤ (1 + TS.querySpace) * L.length := by
          rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
        rw [Nat.mul_add, Nat.mul_one] at h1; omega
      rw [dite_eq_left hi_lt] at hr28I
      -- Query `bTourOwner`
      have htf_lt : ∀ a, htour.rep.foot tourH tx a → a < hI := fun a ha => by
        rcases htf a ha with h0 | ⟨_, h2⟩
        · have := htfoot_lt a h0; omega
        · exact h2
      obtain ⟨body, hbody, oQ, stQ, cQ, txQ, hrunQ, hrepQ, hmemQ, hoQ_ge, hrespQ, hcQ⟩ :=
        htour.owner_runs tourH k (src' (endOfKey k)) hI cord' tx st.mem st.pos ω
          htourH_w hk_lt (by omega) hv_lt (by omega) (hsrc_mem k hk_mem) (hsrc_uniq k hk_mem)
          htr htf_lt hzf hhI_sp
      obtain ⟨hoQ_ge', hoQ_le, hzfQ, hfrQ, hfootQ⟩ := hrespQ
      set hNext := oQ.value
      have hfrQ_all : ∀ a, ¬ htour.rep.foot tourH tx a → (a < hI ∨ hNext ≤ a) → stQ.mem a = st.mem a :=
        fun a hnf ha => by
          rcases ha with h1 | h2
          · exact hfrQ a h1 hnf
          · exact (hzfQ a h2).trans (hzf a (by omega)).symm
      -- Step states for one iteration
      let r30 := Function.update st.regs 30 k
      let r31 := Function.update r30 31 hI
      let stC : State := { mem := stQ.mem, regs := Function.update r31 4 hNext, pos := stQ.pos }
      let r32 := Function.update stC.regs 32 (src' (endOfKey k))
      let mP := Function.update stQ.mem (hCur + i) (packEndKey eCap (src' (endOfKey k)) k)
      let r29' := Function.update r32 29 (i + 1)
      let nextVal := if h : i + 1 < L.length then L[i + 1]'h + 1 else 0
      let r28' := Function.update r29' 28 nextVal
      let stNext : State := { mem := mP, regs := r28', pos := stQ.pos }
      have hfootQ_sub : ∀ a, htour.rep.foot tourH txQ a →
          htour.rep.foot tourH tx₀ a ∨ (hCur + L.length ≤ a ∧ a < hNext) := fun a ha => by
        rcases hfootQ a ha with h1 | ⟨h1, h2⟩
        · rcases htf a h1 with h0 | ⟨h3, h4⟩
          · exact Or.inl h0
          · exact Or.inr ⟨h3, by omega⟩
        · exact Or.inr ⟨by omega, h2⟩
      have hnot_footQ_pack : ¬ htour.rep.foot tourH txQ (hCur + i) := fun ha => by
        rcases hfootQ_sub _ ha with h0 | ⟨h1, _⟩
        · have := htfoot_lt _ h0; omega
        · omega
      have hlocP := htour.rep_local tourH cord' txQ stQ.mem mP
        (fun a ha => (Function.update_of_ne (fun (heq : a = hCur + i) => hnot_footQ_pack (heq ▸ ha)) _ _).symm)
      have hrep_next : htour.rep.rep tourH cord' txQ mP := hlocP.1 hrepQ
      have hphi_next : htour.rep.phi tourH txQ mP = htour.rep.phi tourH txQ stQ.mem := hlocP.2.symm
      have hmP_next : mP (nextBase + k) = nextVal := by
        have hne1 : nextBase + k ≠ hCur + i := by
          rcases hh_disj_next with h1 | h2
          · have : L.length ≤ (1 + TS.querySpace) * L.length := Nat.le_mul_of_pos_left _ (by omega)
            clear * - h1 this hi_lt hk_lt; omega
          · clear * - h2 hi_lt hk_lt; omega
        dsimp only [mP]; rw [Function.update_of_ne hne1]
        have hnot_f : ¬ htour.rep.foot tourH tx (nextBase + k) := fun hf => by
          rcases htf _ hf with h0 | ⟨h1, h2⟩
          · have := htfoot_disj_next _ h0; omega
          · rcases hh_disj_next with h3 | h4
            · have : L.length + TS.querySpace * i ≤ (1 + TS.querySpace) * L.length := by
                rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
              clear * - h3 this h2 hh_hi hk_lt; omega
            · clear * - h4 h1 hk_lt; omega
        have hnot_hi : nextBase + k < hI ∨ hNext ≤ nextBase + k := by
          rcases hh_disj_next with h3 | h4
          · right
            have : L.length + TS.querySpace * (i + 1) ≤ (1 + TS.querySpace) * L.length := by
              rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
            rw [Nat.mul_add, Nat.mul_one] at this; clear * - h3 this hoQ_le hh_hi hk_lt; omega
          · left; clear * - h4 hh_lo hk_lt; omega
        rw [hfrQ_all _ hnot_f hnot_hi, hfr _ (fun hf => by have := htfoot_disj_next _ hf; omega)
          (by rcases hh_disj_next with h3 | h4
              · right
                have : L.length + TS.querySpace * i ≤ (1 + TS.querySpace) * L.length := by
                  rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
                clear * - h3 this hh_hi hk_lt; omega
              · left; clear * - h4 hk_lt; omega)]
        have hnxt := (hdll.2.2.2 i hi_lt).2
        dsimp only [nextVal]
        by_cases h1 : i + 1 < L.length
        · rw [dite_eq_left h1, hnxt, ite_eq_right (by omega), List.getD_eq_getElem L 0 h1]
        · rw [dite_eq_right h1, hnxt, ite_eq_left (by omega)]
      -- Build the 7-statement body run
      have hs1 : Runs w pProg ω (.assign 30 (.bin .sub (.reg 28) (.const 1)))
          st .normal { st with regs := r30 } 4 :=
        runs_assign_iff.mpr ⟨k, by
          simp [Expr.eval, BinOp.eval, hr28I, h1_w, k]; omega, rfl, rfl, rfl⟩
      have hs2 : Runs w pProg ω (.assign 31 (.reg 4))
          { st with regs := r30 } .normal { st with regs := r31 } 2 :=
        runs_assign_iff.mpr ⟨hI, by simp [Expr.eval, r30, hr4I], rfl, rfl, rfl⟩
      have hs3 : Runs w pProg ω (.call 4 bTourOwner [.reg 1, .reg 30, .reg 4])
          { st with regs := r31 } .normal stC (cQ + 4) := by
        refine runs_call_iff.mpr ⟨[tourH, k, hI], body, oQ, stQ, cQ, ?_, hbody, hrunQ, rfl, rfl, ?_⟩
        · simp [evalArgs, Expr.eval, r31, r30, hregs 1 (by decide) (by decide), hr1, hr4I]
        · simp [argsSize, Expr.size]; omega
      have hs4 : Runs w pProg ω (.assign 32 (.load (.reg 31))) stC .normal { stC with regs := r32 } 3 :=
        runs_assign_iff.mpr ⟨src' (endOfKey k), by
          simp [Expr.eval, stC, r31, hmemQ],
          rfl, rfl, rfl⟩
      have hs5 : Runs w pProg ω
          (.store (.bin .add (.reg 27) (.reg 29)) (.bin .add (.bin .mul (.reg 32) (.reg 6)) (.reg 30)))
          { stC with regs := r32 } .normal { mem := mP, regs := r32, pos := stQ.pos } 9 :=
        runs_store_iff.mpr ⟨hCur + i, packEndKey eCap (src' (endOfKey k)) k,
          by simp [Expr.eval, BinOp.eval, r32, stC, r31, r30, hr27I, hr29I,
              show hCur + i < 2 ^ w by
                have := Nat.le_mul_of_pos_left L.length (show 0 < 1 + TS.querySpace by omega); omega],
          by have hmul_w : src' (endOfKey k) * (2 * eCap) < 2 ^ w := by
               have := Nat.mul_le_mul_right (2 * eCap) (Nat.le_of_lt hv_lt); omega
             have hadd_w : src' (endOfKey k) * (2 * eCap) + k < 2 ^ w := hpk_lt
             simp [Expr.eval, BinOp.eval, r32, stC, r31, r30, hregs 6 (by decide) (by decide), hr6,
               hmul_w, packEndKey, hadd_w],
          rfl, rfl, by simp [Expr.size]⟩
      have hs6 : Runs w pProg ω (.assign 29 (.bin .add (.reg 29) (.const 1)))
          { mem := mP, regs := r32, pos := stQ.pos } .normal { mem := mP, regs := r29', pos := stQ.pos } 4 :=
        runs_assign_iff.mpr ⟨i + 1, by
          simp [Expr.eval, BinOp.eval, r32, stC, r31, r30, hr29I, h1_w, show i + 1 < 2 ^ w by omega],
          rfl, rfl, rfl⟩
      have hs7 : Runs w pProg ω (.assign 28 (.load (.bin .add (.reg 11) (.reg 30))))
          { mem := mP, regs := r29', pos := stQ.pos } .normal stNext 5 :=
        runs_assign_iff.mpr ⟨nextVal, by
          simp [Expr.eval, BinOp.eval, r29', r32, stC, r31, r30, hregs 11 (by decide) (by decide),
            hr11, show nextBase + k < 2 ^ w by omega, hmP_next],
          rfl, rfl, rfl⟩
      have hbody_run_raw :=
        bundle_runs_seq_normal hs1 (bundle_runs_seq_normal hs2 (bundle_runs_seq_normal hs3
          (bundle_runs_seq_normal hs4 (bundle_runs_seq_normal hs5 (bundle_runs_seq_normal hs6 hs7)))))
      have hbody_run : Runs w pProg ω loopBody st .normal stNext (cQ + 37) := by
        convert hbody_run_raw using 1; omega
      -- IH at `i + 1`
      have hLat_next : ListAt mP hCur ((L.take (i + 1)).map fun k => packEndKey eCap (src' (endOfKey k)) k) := by
        intro t ht
        simp only [List.length_map, List.length_take] at ht
        rw [List.getElem_map, List.getElem_take]
        by_cases hti : t < i
        · dsimp only [mP]; rw [Function.update_of_ne (by omega)]
          have hnf : ¬ htour.rep.foot tourH tx (hCur + t) := fun ha => by
            rcases htf _ ha with h0 | ⟨h1, _⟩
            · have := htfoot_lt _ h0; omega
            · omega
          rw [hfrQ_all _ hnf (Or.inl (by omega))]
          have hp := hLat t (by simp; omega)
          rwa [List.getElem_map, List.getElem_take] at hp
        · have hteq : t = i := by omega
          simp [mP, hteq, k]
      have hzf_next : ZeroFrom mP hNext := fun a ha => by
        dsimp only [mP]; rw [Function.update_of_ne (by omega)]; exact hzfQ a ha
      have hfr_next : ∀ a, ¬ htour.rep.foot tourH tx₀ a → (a < hCur ∨ hNext ≤ a) → mP a = st₀.mem a := by
        intro a hnf ha
        dsimp only [mP]; rw [Function.update_of_ne (by omega)]
        have hnf_tx : ¬ htour.rep.foot tourH tx a := fun h => by
          rcases htf a h with h0 | ⟨h1, h2⟩
          · exact hnf h0
          · omega
        rw [hfrQ_all a hnf_tx (by omega), hfr a hnf (by omega)]
      obtain ⟨stF, cF, txF, hF, hrunF, hregsF, hr4F, hr27F, hhF_lo, hhF_hi, hLatF, htrF, htfF,
        hzfF, hfrF, hcF⟩ :=
        ih (i + 1) (by omega) (by omega) stNext txQ hNext
          (fun r hr h4 => by
            simp [stNext, r28', r29', r32, stC, r31, r30, show r ≠ 28 by omega, show r ≠ 29 by omega,
              show r ≠ 32 by omega, h4, show r ≠ 31 by omega, show r ≠ 30 by omega, hregs r hr h4])
          (by simp [stNext, r28', r29', r32, stC]) (by simp [stNext, r28', r29', r32, stC, r31, r30, hr27I])
          (by simp [stNext, r28', r29']) (by simp [stNext, r28', nextVal])
          (by omega) (by rw [Nat.mul_add, Nat.mul_one]; omega) hLat_next hrep_next hfootQ_sub hzf_next hfr_next
      refine ⟨stF, 1 + (cQ + 37) + cF + 1, txF, hF,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨k + 1, stNext, cQ + 37, cF,
          by simp [Expr.eval, hr28I, k], by omega, hbody_run, hrunF, rfl⟩)),
        hregsF, hr4F, hr27F, by omega, hhF_hi, hLatF, htrF, htfF, hzfF, hfrF, ?_⟩
      rw [hphi_next] at hcF
      have hmul : (TS.mul * ordStoreLog eCap + 42) * (rem + 1) =
          (TS.mul * ordStoreLog eCap + 42) * rem + (TS.mul * ordStoreLog eCap + 42) := by ring
      omega
  obtain ⟨stF, cF, txF, hF, hrunF, hregsF, hr4F, hr27F, hhF_lo, hhF_hi, hLatF, htrF, htfF,
    hzfF, hfrF, hcF⟩ :=
    hloop L.length 0 (Nat.zero_le _) (by omega) stA tx₀ (hCur + L.length)
      (fun r hr h4 => by simp [stA, r29, r28, r4, r27, h4, show r ≠ 29 by omega, show r ≠ 28 by omega, show r ≠ 27 by omega])
      (by simp [stA, r29, r28, r4]) (by simp [stA, r29, r28, r4, r27]) (by simp [stA, r29])
      (by simp only [stA, r29, r28, Function.update_of_ne (by decide : (28 : ℕ) ≠ 29), Function.update_self, hhd_val]
          cases L <;> simp)
      (le_refl _) (by simp) (by intro t ht; simp at ht) htrep (fun a ha => Or.inl ha)
      (fun a ha => hzero a (by omega)) (fun _ _ _ => rfl)
  dsimp only [stA] at hcF
  refine ⟨stF, 2 + (4 + (7 + (2 + cF + 1) + 1) + 1) + 1, txF, hF,
    bundle_runs_seq_normal ha27 (bundle_runs_seq_normal ha4 (bundle_runs_seq_normal ha28
      (bundle_runs_seq_normal ha29 hrunF))),
    hregsF, hr4F, hr27F, hhF_lo, by rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc]; exact hhF_hi, hLatF, htrF,
    htfF, hzfF, hfrF, by omega⟩

/-! ## 2. Skipping group 0 (`bundleStepEmitCand_skip0_runs`) -/

lemma bundleStepEmitCand_skip0_runs {w eCap degB packArr v0 : ℕ}
    {pProg : Program} {ω : ℕ → Bool} {xs0 : List End} {rest : List (ℕ × List End)} {st₀ : State}
    (hw16 : 16 ≤ 2 ^ w) (_h2e_pos : 0 < 2 * eCap)
    (hpack_w : packArr + degB < 2 ^ w) (hv0_w : v0 < 2 ^ w)
    (hxs0_pos : 0 < xs0.length) (hdeg_eq : degB = xs0.length + vRunsEndsLen rest)
    (hLat : ListAt st₀.mem packArr (vRunsPacked eCap ((v0, xs0) :: rest)))
    (hkeys_lt : ∀ vr ∈ (v0, xs0) :: rest, ∀ x ∈ vr.2, endKey x < 2 * eCap)
    (hrest_pos : ∀ vr ∈ rest, 0 < vr.2.length)
    (hrest_gt : ∀ vr ∈ rest, v0 < vr.1)
    (hpk_w : ∀ t, t < degB → st₀.mem (packArr + t) < 2 ^ w)
    (hr6 : st₀.regs 6 = 2 * eCap) (hr26 : st₀.regs 26 = degB) (hr27 : st₀.regs 27 = packArr) :
    ∃ st1 c1,
      Runs w pProg ω
        (.assign 28 (.bin .div (.load (.reg 27)) (.reg 6)) ;;
         .assign 29 (.const 0) ;;
         .assign 30 (.const 1) ;;
         .loop (.reg 30)
           (.cond (.bin .lt (.reg 29) (.reg 26))
             (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 29))) (.reg 6)) (.reg 28))
               (.assign 29 (.bin .add (.reg 29) (.const 1)))
               (.assign 30 (.const 0)))
             (.assign 30 (.const 0)))) st₀ .normal st1 c1 ∧
      st1.mem = st₀.mem ∧
      (∀ r ≤ 27, st1.regs r = st₀.regs r) ∧
      st1.regs 28 = v0 ∧ st1.regs 29 = xs0.length ∧
      c1 ≤ 20 * xs0.length + 32 := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hdiv_lt : ∀ i (hi : i < xs0.length), st₀.mem (packArr + i) / (2 * eCap) = v0 := fun i hi => by
    have h1 := hLat i (by rw [vRunsPacked_length]; simp [vRunsEndsLen]; omega)
    simp only [vRunsPacked, List.flatMap_cons] at h1
    rw [List.getElem_append_left (by simp; omega), List.getElem_map] at h1
    rw [h1, packEndKey_div (hkeys_lt _ List.mem_cons_self _ (List.getElem_mem hi))]
  have hdiv_end : xs0.length < degB → st₀.mem (packArr + xs0.length) / (2 * eCap) ≠ v0 := by
    intro hlt
    cases rest with
    | nil => simp [vRunsEndsLen] at hdeg_eq; omega
    | cons vr tl =>
      have hvr_pos : 0 < vr.2.length := hrest_pos vr List.mem_cons_self
      have h1 := hLat xs0.length (by rw [vRunsPacked_length]; simp [vRunsEndsLen]; omega)
      simp only [vRunsPacked, List.flatMap_cons] at h1
      rw [List.getElem_append_right (by simp), List.getElem_append_left (by simp; omega),
        List.getElem_map] at h1
      have hsub0 : xs0.length - (List.map (fun x => packEndKey eCap v0 (endKey x)) xs0).length = 0 := by simp
      simp only [hsub0] at h1
      rw [h1, packEndKey_div (hkeys_lt _ (List.mem_cons_of_mem _ List.mem_cons_self) _ (List.getElem_mem hvr_pos))]
      have := hrest_gt vr List.mem_cons_self; omega
  let r28 := Function.update st₀.regs 28 v0
  let r29 := Function.update r28 29 0
  let r30 := Function.update r29 30 1
  let stA : State := { st₀ with regs := r30 }
  have ha28 : Runs w pProg ω (.assign 28 (.bin .div (.load (.reg 27)) (.reg 6)))
      st₀ .normal { st₀ with regs := r28 } 5 :=
    runs_assign_iff.mpr ⟨v0, by
      have := hdiv_lt 0 hxs0_pos; simp only [Nat.add_zero] at this
      simp [Expr.eval, BinOp.eval, hr27, hr6, this, hv0_w],
      rfl, rfl, rfl⟩
  have ha29 : Runs w pProg ω (.assign 29 (.const 0)) { st₀ with regs := r28 } .normal { st₀ with regs := r29 } 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  have ha30 : Runs w pProg ω (.assign 30 (.const 1)) { st₀ with regs := r29 } .normal stA 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h1_w], rfl, rfl, rfl⟩
  let body : Stmt :=
    .cond (.bin .lt (.reg 29) (.reg 26))
      (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 29))) (.reg 6)) (.reg 28))
        (.assign 29 (.bin .add (.reg 29) (.const 1)))
        (.assign 30 (.const 0)))
      (.assign 30 (.const 0))
  have hloop : ∀ rem i (hi : i ≤ xs0.length) (hrem : xs0.length - i = rem) (st : State),
      st.mem = st₀.mem → (∀ r ≤ 27, st.regs r = st₀.regs r) →
      st.regs 28 = v0 → st.regs 29 = i → st.regs 30 = 1 →
      ∃ stF cF,
        Runs w pProg ω (.loop (.reg 30) body) st .normal stF cF ∧
        stF.mem = st₀.mem ∧ (∀ r ≤ 27, stF.regs r = st₀.regs r) ∧
        stF.regs 28 = v0 ∧ stF.regs 29 = xs0.length ∧
        cF ≤ 20 * rem + 19 := by
    intro rem
    induction rem with
    | zero =>
      intro i hi hrem st hmem hregs hr28 hr29 hr30
      have hieq : i = xs0.length := by omega
      subst hieq
      let stZ : State := { st with regs := Function.update st.regs 30 0 }
      have hexit : Runs w pProg ω (.loop (.reg 30) body) stZ .normal stZ 2 :=
        runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, stZ], rfl, rfl, rfl⟩)
      have haZ : Runs w pProg ω (.assign 30 (.const 0)) st .normal stZ 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
      by_cases hlt : xs0.length < degB
      · have hne := hdiv_end hlt
        have hc2 : Runs w pProg ω
            (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 29))) (.reg 6)) (.reg 28))
              (.assign 29 (.bin .add (.reg 29) (.const 1))) (.assign 30 (.const 0)))
            st .normal stZ 11 :=
          runs_cond_iff.mpr ⟨0, 2, by
            have hdv_w : st₀.mem (packArr + xs0.length) / (2 * eCap) < 2 ^ w :=
              lt_of_le_of_lt (Nat.div_le_self _ _) (hpk_w xs0.length hlt)
            simp [Expr.eval, BinOp.eval, hregs 27 (by decide), hr27, hr29, hregs 6 (by decide), hr6,
              hr28, hmem, show packArr + xs0.length < 2 ^ w by omega, hdv_w, hne, h0_w],
            by simpa using haZ, by simp [Expr.size]⟩
        have hc1 : Runs w pProg ω body st .normal stZ 15 :=
          runs_cond_iff.mpr ⟨1, 11, by
            simp [Expr.eval, BinOp.eval, hr29, hregs 26 (by decide), hr26, hlt, h1_w],
            by simpa using hc2, by simp [Expr.size]⟩
        exact ⟨stZ, 1 + 15 + 2 + 1,
          runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stZ, 15, 2, by simp [Expr.eval, hr30], by decide, hc1, hexit, rfl⟩)),
          hmem, fun r hr => by simp [stZ, show r ≠ 30 by omega, hregs r hr],
          by simp [stZ, hr28], by simp [stZ, hr29], by omega⟩
      · have hc1 : Runs w pProg ω body st .normal stZ 6 :=
          runs_cond_iff.mpr ⟨0, 2, by
            simp [Expr.eval, BinOp.eval, hr29, hregs 26 (by decide), hr26, hlt, h0_w],
            by simpa using haZ, by simp [Expr.size]⟩
        exact ⟨stZ, 1 + 6 + 2 + 1,
          runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stZ, 6, 2, by simp [Expr.eval, hr30], by decide, hc1, hexit, rfl⟩)),
          hmem, fun r hr => by simp [stZ, show r ≠ 30 by omega, hregs r hr],
          by simp [stZ, hr28], by simp [stZ, hr29], by omega⟩
    | succ rem ih =>
      intro i hi hrem st hmem hregs hr28 hr29 hr30
      have hi_lt : i < xs0.length := by omega
      have hdiv := hdiv_lt i hi_lt
      let st1 : State := { st with regs := Function.update st.regs 29 (i + 1) }
      have hinc : Runs w pProg ω (.assign 29 (.bin .add (.reg 29) (.const 1))) st .normal st1 4 :=
        runs_assign_iff.mpr ⟨i + 1, by
          simp [Expr.eval, BinOp.eval, hr29, h1_w, show i + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hc2 : Runs w pProg ω
          (.cond (.bin .eq (.bin .div (.load (.bin .add (.reg 27) (.reg 29))) (.reg 6)) (.reg 28))
            (.assign 29 (.bin .add (.reg 29) (.const 1))) (.assign 30 (.const 0)))
          st .normal st1 13 :=
        runs_cond_iff.mpr ⟨1, 4, by
          simp [Expr.eval, BinOp.eval, hregs 27 (by decide), hr27, hr29, hregs 6 (by decide), hr6,
            hr28, hmem, show packArr + i < 2 ^ w by omega, hdiv, hv0_w, h1_w],
          by simpa using hinc, by simp [Expr.size]⟩
      have hc1 : Runs w pProg ω body st .normal st1 17 :=
        runs_cond_iff.mpr ⟨1, 13, by
          simp [Expr.eval, BinOp.eval, hr29, hregs 26 (by decide), hr26, show i < degB by omega, h1_w],
          by simpa using hc2, by simp [Expr.size]⟩
      obtain ⟨stF, cF, hrunF, hmemF, hregsF, hr28F, hr29F, hcF⟩ :=
        ih (i + 1) (by omega) (by omega) st1 hmem
          (fun r hr => by simp [st1, show r ≠ 29 by omega, hregs r hr])
          (by simp [st1, hr28]) (by simp [st1]) (by simp [st1, hr30])
      exact ⟨stF, 1 + 17 + cF + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st1, 17, cF, by simp [Expr.eval, hr30], by decide, hc1, hrunF, rfl⟩)),
        hmemF, hregsF, hr28F, hr29F, by omega⟩
  obtain ⟨stF, cF, hrunF, hmemF, hregsF, hr28F, hr29F, hcF⟩ :=
    hloop xs0.length 0 (Nat.zero_le _) (by omega) stA rfl
      (fun r hr => by simp [stA, r30, r29, r28, show r ≠ 30 by omega, show r ≠ 29 by omega, show r ≠ 28 by omega])
      (by simp [stA, r30, r29, r28]) (by simp [stA, r30, r29]) (by simp [stA, r30])
  exact ⟨stF, 5 + (2 + (2 + cF + 1) + 1) + 1,
    bundle_runs_seq_normal ha28 (bundle_runs_seq_normal ha29 (bundle_runs_seq_normal ha30 hrunF)),
    hmemF, hregsF, hr28F, hr29F, by omega⟩


end

end MinCostFlow.SparseCore.Program
