module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActOne
public import MinCostFlow.SparseCore.Program.AssemblyBranchSide

import WordRAM.Tactic

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-!
# Phase 2 loop verification (`AssemblyFirstStepNewActLoop`)

Proves:
* `forRange_amort`: generic amortized `forRange` loop rule parameterized by an abstract state `α`
  and potential `Φ : α → State → ℕ`.
* `bunAgree_normGraph_eq`: agreeing bundle states have identical normalized bundle graphs.
* `asmFirstNewAct_loop_runs`: verifies the `forRange 7 (.const 0) (.reg 3)` loop of
  `asmFirstNewActStmt`, threading `asmFirstInitOneComp_runs` across all newly active components
  in `newComps`.
-/

public section

/-- Generic amortized rule for `forRange r (.const 0) hi body` with an abstract witness `α` and
potential `Φ : α → State → ℕ`. -/
theorem forRange_amort {w : ℕ} {p : Program} {ω : ℕ → Bool} {α : Type*}
    {r : ℕ} {hi : Expr} {body : Stmt}
    (Inv : ℕ → α → State → Prop) (Φ : α → State → ℕ)
    (stepCost : ℕ → ℕ) (hiVal : ℕ)
    (hw : 1 < 2 ^ w) (hhi_word : hiVal < 2 ^ w)
    {a₀ : α} {st₀ : State}
    (hinit : Inv 0 a₀ { st₀ with regs := Function.update st₀.regs r 0 })
    (hreg : ∀ i a st, i ≤ hiVal → Inv i a st → st.regs r = i)
    (hhi : ∀ i a st, i ≤ hiVal → Inv i a st → hi.eval w st = some hiVal)
    (hbody : ∀ i a st, i < hiVal → Inv i a st →
      ∃ st₁ c₁ a₁, Runs w p ω body st .normal st₁ c₁ ∧
        st₁.regs r = i ∧
        Inv (i + 1) a₁ { st₁ with regs := Function.update st₁.regs r (i + 1) } ∧
        Φ a₁ { st₁ with regs := Function.update st₁.regs r (i + 1) } = Φ a₁ st₁ ∧
        c₁ + Φ a₁ st₁ ≤ stepCost i + Φ a st) :
    ∃ st' c a', Runs w p ω (forRange r (.const 0) hi body) st₀ .normal st' c ∧
      Inv hiVal a' st' ∧
      c + Φ a' st' ≤ rangeCost stepCost 0 hiVal + hiVal * (hi.size + 8) + (hi.size + 6) +
        Φ a₀ { st₀ with regs := Function.update st₀.regs r 0 } := by
  have hup : ∀ k i a st, hiVal - i = k → i ≤ hiVal → Inv i a st →
      ∃ st' c a', Runs w p ω (forUp r hi body) st .normal st' c ∧
        Inv hiVal a' st' ∧
        c + Φ a' st' ≤ rangeCost stepCost i hiVal + (hiVal - i) * (hi.size + 8) + (hi.size + 3) +
          Φ a st := by
    intro k
    induction k with
    | zero =>
      intro i a st hk hle hInv
      have heq : i = hiVal := by omega
      subst heq
      have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 0 :=
        Expr.eval_lt_false (by simp [Expr.eval, hreg i a st hle hInv])
          (hhi i a st hle hInv) (Nat.le_refl _) hw
      refine ⟨st, hi.size + 3, a,
        runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, by simp [Expr.size]; omega⟩),
        hInv, by simp only [rangeCost_of_le (Nat.le_refl _)]; omega⟩
    | succ k ih =>
      intro i a st hk hle hInv
      have hlt : i < hiVal := by omega
      have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 1 :=
        Expr.eval_lt_true (by simp [Expr.eval, hreg i a st hle hInv])
          (hhi i a st hle hInv) hlt hw
      obtain ⟨st₁, c₁, a₁, hrun₁, hr₁, hInv₁, hΦ₁, hc₁⟩ := hbody i a st hlt hInv
      set st₂ : State := { st₁ with regs := Function.update st₁.regs r (i + 1) }
      have hinc : Runs w p ω (.assign r (.bin .add (.reg r) (.const 1))) st₁ .normal st₂ 4 :=
        runs_assign_iff.mpr ⟨i + 1,
          Expr.eval_add (Expr.eval_reg_of_eq hr₁) (Expr.eval_const hw) (by omega),
          rfl, rfl, by simp [Expr.size]⟩
      have hiter : Runs w p ω (body ;; .assign r (.bin .add (.reg r) (.const 1))) st .normal st₂
          (c₁ + 4 + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, 4, hrun₁, hinc, rfl⟩)
      obtain ⟨st', cRest, a', hrunR, hInvR, hcR⟩ := ih (i + 1) a₁ st₂ (by omega) (by omega) hInv₁
      have hloop : Runs w p ω (forUp r hi body) st .normal st'
          ((Expr.bin .lt (.reg r) hi).size + (c₁ + 4 + 1) + cRest + 1) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, st₂, c₁ + 4 + 1, cRest, hcond, by decide,
          hiter, hrunR, rfl⟩))
      refine ⟨st', _, a', hloop, hInvR, ?_⟩
      rw [rangeCost_step hlt]
      have hsub : hiVal - i = (hiVal - (i + 1)) + 1 := by omega
      rw [hsub, Nat.add_mul, Nat.one_mul]
      simp only [Expr.size] at hcR ⊢
      omega
  have ha0 : Runs w p ω (.assign r (.const 0)) st₀ .normal
      { st₀ with regs := Function.update st₀.regs r 0 } 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨st', cU, a', hrunU, hInvU, hcU⟩ := hup hiVal 0 a₀ _ (by omega) (Nat.zero_le _) hinit
  refine ⟨st', 2 + cU + 1, a',
    runs_seq_iff.mpr (Or.inr ⟨_, 2, cU, ha0, hrunU, rfl⟩), hInvU, ?_⟩
  simp only [Nat.sub_zero] at hcU
  omega

/-- Agreeing bundle states have identical normalized bundle graphs. -/
theorem bunAgree_normGraph_eq {B B' : BundleState} (h : BunAgree B B') :
    normGraph B.graph = normGraph B'.graph := by
  rcases h with ⟨hV, hE, -, hB⟩
  simp only [normGraph, BundleState.graph, hV, hE]
  congr 1
  · funext e; by_cases he : e ∈ B'.edges
    · simp only [he, ↓reduceIte]; exact hB (e, true) (hE ▸ he)
    · simp [he]
  · funext e; by_cases he : e ∈ B'.edges
    · simp only [he, ↓reduceIte]; exact hB (e, false) (hE ▸ he)
    · simp [he]

/-- Number of core edges of component `C` in `tr`. -/
@[expose] noncomputable def compCoreEdges {depth : ℕ} (tr : BundleTreeState depth) (C : Finset ℕ) : Finset ℕ :=
  (coreGraph tr.cs.G tr.cs.lsf).E.filter fun e => (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ C

/-- Total space used by the per-component loop of `asmFirstNewActStmt`. -/
@[expose] noncomputable def newActLoopSpace {depth : ℕ} (TS : BundleTourSpec) (rQ : ℕ)
    (tr : BundleTreeState depth) (ord : ℕ → List End) (comps : List (Finset ℕ))
    (newComps : List (ℕ × ℕ)) : ℕ :=
  (newComps.map fun p =>
    let C := comps.getD p.1 ∅
    newActOneSpace TS rQ (outCoreOrder tr ord (tr.cs.RF.root p.2)).length
      (compCoreEdges tr C).card (tr.activeBuckets C).card).sum

/-- Per-iteration cost bound for `asmFirstNewActStmt`'s component-initialization loop. -/
@[expose] noncomputable def newActLoopStepCost {depth : ℕ} (TS : BundleTourSpec) (rMul eCap : ℕ)
    (tr : BundleTreeState depth) (ord : ℕ → List End) (comps : List (Finset ℕ))
    (p : ℕ × ℕ) : ℕ :=
  let C := comps.getD p.1 ∅
  let cord := outCoreOrder tr ord
  let r_c := tr.cs.RF.root p.2
  newActOneCost TS rMul eCap (cord r_c).length (compCoreEdges tr C).card (tr.activeBuckets C).card
    cord r_c + 40

/-- Total bucket count across a list of `(c, v)` component pairs. -/
@[expose] noncomputable def newCompsBucketSum {depth : ℕ} (tr : BundleTreeState depth)
    (comps : List (Finset ℕ)) (newComps : List (ℕ × ℕ)) : ℕ :=
  (newComps.map fun p => (tr.activeBuckets (comps.getD p.1 ∅)).card).sum

/-- **Loop invariant of `asmFirstNewActStmt`'s `forRange 7` loop** at iteration `j ≤ newComps.length`,
parameterized by concrete bundle/tour metadata `(m, tx)`. -/
@[expose] def NewActLoopInv {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {depth : ℕ} (TS : BundleTourSpec) (rQ w : ℕ)
    (tr : BundleTreeState depth) (ord : ℕ → List End) (mk : Finset End)
    (restH tourH h : ℕ)
    (y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth)
    (tx₀ : (TR y.vCap5 y.eCap5).τ) (newComps : List (ℕ × ℕ))
    (mem₀ : ℕ → ℕ) (st₀ : State)
    (j : ℕ) (mt : BundleTableMeta y.slotCap × (TR y.vCap5 y.eCap5).τ) (st : State) : Prop :=
  let m := mt.1; let tx := mt.2
  let pref := newComps.take j
  let prefComps : Finset (Finset ℕ) := (pref.map fun p => y.comps.getD p.1 ∅).toFinset
  let tr_j : BundleTreeState depth := { tr with activeComps := tr.activeComps ∪ prefComps }
  let nSlots := y.slots.length + newCompsBucketSum tr y.comps pref
  ∃ (hCur : ℕ) (S : BundleTableState y.slotCap) (slotOf : Finset ℕ × ℤ → ℕ)
    (cslPtr : ℕ → ℕ) (cslL : ℕ → List (ℤ × ℕ)) (lazyE : Fin j → List ℕ),
    (∀ r, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → st.regs r = st₀.regs r) ∧
    st.regs 7 = j ∧ st.regs 6 = hCur ∧
    SlotMapOK tr_j y.slotCap y.cap (List.range nSlots) slotOf ∧
    BunTableMatches tr_j slotOf S ∧
    (∀ q ∈ activePairs tr, slotOf q = y.slotOf q) ∧
    (∀ i : Fin y.slotCap, i.1 < y.slots.length ∨ nSlots ≤ i.1 → S i = y.bunS i) ∧
    (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).rep y.bunH S m st.mem ∧
    (TR y.vCap5 y.eCap5).rep tourH ⟨ord, tr.cs.RF, mk⟩ tx st.mem ∧
    bunRestartInv y.vCap5 y.eCap5 S (outCoreOrder tr ord) ∧
    st.mem (restH + ASM_SD_NSLOTS) = nSlots ∧
    (∀ s, y.slots.length ≤ s → s < nSlots → st.mem (y.slotsPtr + s) = s) ∧
    (∀ c (hc : c < y.comps.length),
      st.mem (y.ctH + 3 * c + 1) = cslPtr c ∧
      cslPtr c < 2 ^ w ∧
      st.mem (y.ctH + 3 * c + 2) = (cslL c).length ∧
      (cslL c).Nodup ∧
      (∀ bi (hbi : bi < (cslL c).length),
        st.mem (cslPtr c + 2 * bi) = bucketCode (cslL c)[bi].1 ∧
        st.mem (cslPtr c + 2 * bi + 1) = (cslL c)[bi].2) ∧
      (∀ b t, (b, t) ∈ cslL c ↔
        (y.comps[c], b) ∈ activePairs tr_j ∧ t = slotOf (y.comps[c], b)) ∧
      (c ∉ pref.map Prod.fst → cslPtr c = y.cslPtr c ∧ cslL c = y.cslL c) ∧
      ((cslL c).length = 0 ∨
        ((c ∉ pref.map Prod.fst → cslPtr c + 2 * (cslL c).length ≤ h) ∧
         (c ∈ pref.map Prod.fst → h + 2 * newComps.length ≤ cslPtr c ∧
           cslPtr c + 2 * (cslL c).length ≤ hCur) ∧
         ∀ a, cslPtr c ≤ a → a < cslPtr c + 2 * (cslL c).length →
           ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m a ∧
           ¬ (TR y.vCap5 y.eCap5).foot tourH tx a ∧ st.mem a < 2 ^ w))) ∧
    (∀ c₁ < y.comps.length, ∀ c₂ < y.comps.length, c₁ ≠ c₂ →
      ∀ a, cslPtr c₁ ≤ a → a < cslPtr c₁ + 2 * (cslL c₁).length →
        ¬ (cslPtr c₂ ≤ a ∧ a < cslPtr c₂ + 2 * (cslL c₂).length)) ∧
    (∀ k (hk : k < j),
      ListAt st.mem (st.mem (h + 2 * k)) (lazyE ⟨k, hk⟩) ∧
      st.mem (h + 2 * k + 1) = (lazyE ⟨k, hk⟩).length ∧
      (lazyE ⟨k, hk⟩).Pairwise (· < ·) ∧
      (lazyE ⟨k, hk⟩).toFinset = compCoreEdges tr (y.comps.getD (newComps.getD k (0, 0)).1 ∅) ∧
      h + 2 * newComps.length ≤ st.mem (h + 2 * k) ∧
      st.mem (h + 2 * k) + (lazyE ⟨k, hk⟩).length ≤ hCur ∧
      (∀ a, st.mem (h + 2 * k) ≤ a → a < st.mem (h + 2 * k) + (lazyE ⟨k, hk⟩).length →
        ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m a ∧
        ¬ (TR y.vCap5 y.eCap5).foot tourH tx a)) ∧
    h + 2 * newComps.length ≤ hCur ∧
    hCur ≤ h + 2 * newComps.length + newActLoopSpace TS rQ tr ord y.comps pref ∧
    ZeroFrom st.mem hCur ∧
    (∀ a, (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m a →
      (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH y.xBun a ∨
        (h + 2 * newComps.length ≤ a ∧ a < hCur)) ∧
    (∀ a, (TR y.vCap5 y.eCap5).foot tourH tx a →
      (TR y.vCap5 y.eCap5).foot tourH tx₀ a ∨
        (h + 2 * newComps.length ≤ a ∧ a < hCur)) ∧
    (∀ a, (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH m a →
      ¬ (TR y.vCap5 y.eCap5).foot tourH tx a) ∧
    (∀ a < h,
      ¬ (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).foot y.bunH y.xBun a →
      ¬ (TR y.vCap5 y.eCap5).foot tourH tx₀ a →
      a ≠ restH + ASM_SD_NSLOTS →
      (∀ k (_hk : k < j), ¬ (y.ctH + 3 * (newComps.getD k (0, 0)).1 + 1 ≤ a ∧
        a < y.ctH + 3 * (newComps.getD k (0, 0)).1 + 3)) →
      ¬ (y.slotsPtr + y.slots.length ≤ a ∧ a < y.slotsPtr + nSlots) →
      st.mem a = mem₀ a)

theorem activeBuckets_disj_sum_le {depth : ℕ} (tr : BundleTreeState depth)
    (comps : List (Finset ℕ)) (hnd : comps.Nodup)
    (hmem : ∀ C, C ∈ comps ↔ C ∈ components tr.cs.G₀)
    (hact_sub : tr.activeComps ⊆ components tr.cs.G₀)
    (newComps : List (ℕ × ℕ)) (hNC_nd : (newComps.map Prod.fst).Nodup)
    (hNC_ok : ∀ p ∈ newComps, p.1 < comps.length ∧ comps[p.1]! ∉ tr.activeComps) :
    (activePairs tr).card + newCompsBucketSum tr comps newComps ≤
      (components tr.cs.G₀).sum (fun C => (tr.activeBuckets C).card) := by
  have h1 : (activePairs tr).card = tr.activeComps.sum (fun C => (tr.activeBuckets C).card) := by
    rw [activePairs, Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun C _ => Finset.card_image_of_injective _ fun _ _ h => (Prod.mk.inj h).2
    · intro C₁ _ C₂ _ hne
      refine Finset.disjoint_left.mpr fun q hq1 hq2 => ?_
      rcases Finset.mem_image.mp hq1 with ⟨b₁, _, rfl⟩
      rcases Finset.mem_image.mp hq2 with ⟨b₂, _, hEq⟩
      exact hne (Prod.mk.inj hEq).1.symm
  have hnew_list_nd : (newComps.map fun p => comps.getD p.1 ∅).Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hi : i.1 < newComps.length := by simpa using i.2
    have hj : j.1 < newComps.length := by simpa using j.2
    have hci : newComps[i.1].1 < comps.length := (hNC_ok _ (List.getElem_mem hi)).1
    have hcj : newComps[j.1].1 < comps.length := (hNC_ok _ (List.getElem_mem hj)).1
    simp only [List.getElem_map, List.getD_eq_getElem _ _ hci, List.getD_eq_getElem _ _ hcj] at hij
    have heq_c : newComps[i.1].1 = newComps[j.1].1 := (List.nodup_iff_injective_getElem.mp hnd)
      (a₁ := ⟨newComps[i.1].1, hci⟩) (a₂ := ⟨newComps[j.1].1, hcj⟩) hij |> congrArg Fin.val
    have heq_i := (List.nodup_iff_injective_getElem.mp hNC_nd)
      (a₁ := ⟨i.1, by simpa using hi⟩) (a₂ := ⟨j.1, by simpa using hj⟩) (by simpa using heq_c)
    exact Fin.ext (by simpa using congrArg Fin.val heq_i)
  set newS : Finset (Finset ℕ) := (newComps.map fun p => comps.getD p.1 ∅).toFinset
  have h2 : newCompsBucketSum tr comps newComps = newS.sum (fun C => (tr.activeBuckets C).card) := by
    unfold newCompsBucketSum
    have hmap : (newComps.map fun p => (tr.activeBuckets (comps.getD p.1 ∅)).card) =
        (newComps.map fun p => comps.getD p.1 ∅).map (fun C => (tr.activeBuckets C).card) := by
      simp [List.map_map, Function.comp_def]
    rw [hmap, ← List.sum_toFinset _ hnew_list_nd]
  have hdisj : Disjoint tr.activeComps newS := by
    rw [Finset.disjoint_left]
    intro C hC hCN
    rw [List.mem_toFinset, List.mem_map] at hCN
    rcases hCN with ⟨p, hp, rfl⟩
    have hlt := (hNC_ok p hp).1
    have hnot := (hNC_ok p hp).2
    rw [List.getD_eq_getElem _ _ hlt] at hC
    rw [getElem!_pos comps p.1 hlt] at hnot
    exact hnot hC
  have hsub : tr.activeComps ∪ newS ⊆ components tr.cs.G₀ := by
    intro C hC
    rcases Finset.mem_union.mp hC with hA | hN
    · exact hact_sub hA
    · rw [List.mem_toFinset, List.mem_map] at hN
      rcases hN with ⟨p, hp, rfl⟩
      have hlt := (hNC_ok p hp).1
      rw [List.getD_eq_getElem _ _ hlt]
      exact (hmem _).mp (List.getElem_mem hlt)
  rw [h1, h2, ← Finset.sum_union hdisj]
  exact Finset.sum_le_sum_of_subset hsub

/-- Lifts all non-`cmpH`, non-`ctH[3*c]` facts of `AsmBrSideAt` from `mem_orig` to a post-Phase-1
memory `mem₀` that agrees on `asmSdFoot` outside `ctH + 3 * c` and `cmpH + v`. -/
theorem asmBrSide_lift_agree {impl : SparsifyImpl} {w depth L capExp limbMul restH : ℕ}
    {Ψ : BundleTreeState depth → ℕ} {tr : BundleTreeState depth} {ord : ℕ → List End}
    {y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth}
    {mem_orig mem₀ : ℕ → ℕ}
    (hSide : AsmBrSideAt (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w depth L capExp limbMul Ψ restH ⟨tr, ord, y.vCap5, y.eCap5⟩ y mem_orig)
    (hAgree : ∀ a, asmSdFoot restH y a →
      (∀ c < y.comps.length, a ≠ y.ctH + 3 * c) →
      (∀ v < y.vCap5, a ≠ y.cmpH + v) → mem₀ a = mem_orig a) :
    (∀ off < ASM_SD_SIZE, mem₀ (restH + off) = mem_orig (restH + off)) ∧
    (bunTableHeadroomRep y.slotCap y.vCap5 y.eCap5 y.kB).rep y.bunH y.bunS y.xBun mem₀ ∧
    (bucketSpannerRep (asmBrSP impl w depth y) y.cap).rep y.spanH y.spanS y.xSpan mem₀ ∧
    ListAt mem₀ y.slotsPtr y.slots ∧
    (∀ e ∈ tr.cs.G₀.E, e < y.eCap5 ∧ mem₀ (y.bktH + e) = bucketCode (tr.origBucket e)) ∧
    (∀ c (hc : c < y.comps.length),
      mem₀ (y.ctH + 3 * c + 1) = y.cslPtr c ∧ y.cslPtr c < 2 ^ w ∧ mem₀ (y.ctH + 3 * c + 2) = (y.cslL c).length ∧
      (y.cslL c).Nodup ∧
      (∀ bi (hbi : bi < (y.cslL c).length),
        mem₀ (y.cslPtr c + 2 * bi) = bucketCode (y.cslL c)[bi].1 ∧
        mem₀ (y.cslPtr c + 2 * bi + 1) = (y.cslL c)[bi].2) ∧
      (∀ b t, (b, t) ∈ y.cslL c ↔ (y.comps[c], b) ∈ activePairs tr ∧ t = y.slotOf (y.comps[c], b))) ∧
    (∀ a, (asmSdMapPart y 1 a ∨ ∃ c < y.comps.length, asmSdMapPart y (c + 3) a) → mem₀ a < 2 ^ w) := by
  rcases hSide with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hrepB0, hrepS0, hSl0, hSlCap, hPartDisj, hMaps, _⟩
  unfold AsmSdMapsAt at hMaps; dsimp only at hMaps
  rcases hMaps with ⟨_, _, _, _, _, _, _, hBkt0, hCt0, hMW0, hMapDisj, hMapNotSl⟩
  have hSD : ASM_SD_SIZE = 16 := rfl
  refine ⟨fun off hoff => hAgree (restH + off) ⟨0, by omega, by omega, by omega⟩
      (fun c hc _ => hPartDisj 0 (by omega) 3 (by omega) (by decide) (restH + off) ⟨by omega, by omega⟩ (Or.inr ⟨2, by omega, by omega⟩))
      (fun v hv _ => hPartDisj 0 (by omega) 3 (by omega) (by decide) (restH + off) ⟨by omega, by omega⟩ (Or.inr ⟨0, by omega, by omega⟩)),
    ((bunTableHeadroomRep_local y.slotCap y.vCap5 y.eCap5 y.kB) y.bunH y.bunS y.xBun mem_orig mem₀ fun a ha =>
      (hAgree a ⟨1, by omega, ha⟩
        (fun c hc _ => hPartDisj 1 (by omega) 3 (by omega) (by decide) a ha (Or.inr ⟨2, by omega, by omega⟩))
        (fun v hv _ => hPartDisj 1 (by omega) 3 (by omega) (by decide) a ha (Or.inr ⟨0, by omega, by omega⟩))).symm).1 hrepB0,
    ((bucketSpannerRep_local (asmBrSP impl w depth y) y.cap) y.spanH y.spanS y.xSpan mem_orig mem₀ fun a ha =>
      (hAgree a ⟨2, by omega, ha⟩
        (fun c hc _ => hPartDisj 2 (by omega) 3 (by omega) (by decide) a ha (Or.inr ⟨2, by omega, by omega⟩))
        (fun v hv _ => hPartDisj 2 (by omega) 3 (by omega) (by decide) a ha (Or.inr ⟨0, by omega, by omega⟩))).symm).1 hrepS0,
    fun i hi => (hAgree (y.slotsPtr + i) ⟨3, by omega, Or.inl ⟨by omega, by omega⟩⟩
      (fun c hc _ => hMapNotSl (y.slotsPtr + i) ⟨2, by omega, by omega⟩ ⟨by omega, by omega⟩)
      (fun v hv _ => hMapNotSl (y.slotsPtr + i) ⟨0, by omega, by omega⟩ ⟨by omega, by omega⟩)).trans (hSl0 i hi),
    fun e he => by
      obtain ⟨hlt, heq⟩ := hBkt0 e he
      exact ⟨hlt, (hAgree (y.bktH + e) ⟨3, by omega, Or.inr ⟨1, by omega, by omega⟩⟩
        (fun c hc _ => hMapDisj 1 2 (by decide) (y.bktH + e) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
        (fun v hv _ => hMapDisj 1 0 (by decide) (y.bktH + e) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)).trans heq⟩,
    fun c hc => by
      obtain ⟨_, h1, h2, hnd, hcsl, hiff⟩ := hCt0 c hc
      have hct_off : ∀ off, off = 1 ∨ off = 2 → mem₀ (y.ctH + 3 * c + off) = mem_orig (y.ctH + 3 * c + off) := fun off hoff =>
        hAgree (y.ctH + 3 * c + off) ⟨3, by omega, Or.inr ⟨2, by omega, by omega⟩⟩
          (fun c' _ _ => by omega)
          (fun v hv _ => hMapDisj 2 0 (by decide) (y.ctH + 3 * c + off) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩)
      have hcsl_eq : ∀ a, y.cslPtr c ≤ a → a < y.cslPtr c + 2 * (y.cslL c).length → mem₀ a = mem_orig a := fun a ha1 ha2 =>
        hAgree a ⟨3, by omega, Or.inr ⟨c + 3, hc, ha1, ha2⟩⟩
          (fun c' hc' _ => hMapDisj (c + 3) 2 (by omega) a ⟨hc, ha1, ha2⟩ ⟨by omega, by omega⟩)
          (fun v hv _ => hMapDisj (c + 3) 0 (by omega) a ⟨hc, ha1, ha2⟩ ⟨by omega, by omega⟩)
      exact ⟨(hct_off 1 (Or.inl rfl)).trans h1, h1 ▸ hMW0 (y.ctH + 3 * c + 1) ⟨2, by omega, by omega⟩,
        (hct_off 2 (Or.inr rfl)).trans h2, hnd,
        fun bi hbi => ⟨(hcsl_eq _ (by omega) (by omega)).trans (hcsl bi hbi).1,
          (hcsl_eq _ (by omega) (by omega)).trans (hcsl bi hbi).2⟩, hiff⟩,
    fun a ha => by
      rcases ha with h1 | ⟨c, hc, hc3⟩
      · rw [hAgree a ⟨3, by omega, Or.inr ⟨1, h1⟩⟩
          (fun c' hc' _ => hMapDisj 1 2 (by decide) a h1 ⟨by omega, by omega⟩)
          (fun v hv _ => hMapDisj 1 0 (by decide) a h1 ⟨by omega, by omega⟩)]
        exact hMW0 a ⟨1, h1⟩
      · rw [hAgree a ⟨3, by omega, Or.inr ⟨c + 3, hc3⟩⟩
          (fun c' hc' _ => hMapDisj (c + 3) 2 (by omega) a hc3 ⟨by omega, by omega⟩)
          (fun v hv _ => hMapDisj (c + 3) 0 (by omega) a hc3 ⟨by omega, by omega⟩)]
        exact hMW0 a ⟨c + 3, hc3⟩⟩

end

end MinCostFlow.SparseCore.Program
