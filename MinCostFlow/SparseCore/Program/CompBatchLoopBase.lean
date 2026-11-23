module

public import MinCostFlow.SparseCore.Program.CompBatchStepIns
public import MinCostFlow.SparseCore.Program.CompBatchStepDel
public import MinCostFlow.SparseCore.Program.CompBatchStepSplit
import WordRAM.Tactic

/-!
# Batch-Update Loop Helpers (`CompBatchLoopBase`)

Defines `compBatchLoopStmt` and proves the pure step-cost summation (`≤ 3 * sumTouchedLsfBatchCost`),
forest-cut composition across insert/delete/split steps, and `BatchBodyAt` memory-agreement lemmas.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Loop statement -/

/-- Main batch-update loop over updates `r10 = i < r6 = numU`, decoding each update at `r11 = uPtr`
and dispatching to `bIns`, `bDel`, or `bSplit`. Registers:
* `r0 = b`, `r1 = batchPtr`, `r2 = heap`, `r3 = k`, `r4 = vCap`, `r5 = touchMarkBase`,
  `r6 = numU`, `r7 = cntBase`, `r8 = splitBase`, `r9 = updBuf`, `r10 = i`, `r11 = uPtr`,
  `r12 = numSplits`, `r13 = tag`. -/
def compBatchLoopStmt (bIns bDel bSplit : ℕ) : Stmt :=
  .loop (.bin .lt (.reg 10) (.reg 6))
    (.assign 13 (.load (.reg 11)) ;;
     .cond (.bin .eq (.reg 13) (.const 0))
       (.call 11 bIns [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9])
       (.cond (.bin .eq (.reg 13) (.const 1))
         (.call 11 bDel [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9])
         (.call 11 bSplit [.reg 0, .reg 11, .reg 2, .reg 7, .reg 9, .bin .add (.reg 8) (.reg 12)] ;;
          .assign 12 (.bin .add (.reg 12) (.const 1)))) ;;
     .assign 10 (.bin .add (.reg 10) (.const 1)))

lemma compBatchLoopStmt_noRand (bIns bDel bSplit : ℕ) :
    (compBatchLoopStmt bIns bDel bSplit).NoRand := by
  simp [compBatchLoopStmt, Stmt.NoRand]

/-! ## 2. Step-cost summation bound (`≤ 3 * sumTouchedLsfBatchCost`) -/

/-- Sum of per-step touched-edgeful dispatch costs along a batch `U` encoded at `ptr` in `mem`. -/
noncomputable def compBatchStepsCost (mem : ℕ → ℕ) (L_w : ℕ) :
    CompLSFState → ℕ → List Update → ℕ
  | _, _, [] => 0
  | cs, ptr, u :: us =>
    (open Classical in
      ((touchedComps cs u).filter fun C => 1 ≤ (compGraph cs.G₀ C).m).sum fun C =>
        lsfBatchCostFactor * ((1 + projUpdWords mem cs C ptr u) * L_w + 1) +
        lsfBatchCostFactor * (projUpdWords mem cs C ptr u * L_w)) +
    compBatchStepsCost mem L_w (compLSFStepSingle cs u) (ptr + dgUpdateMemLen mem ptr) us

/-- Per-component contribution to `compBatchStepsCost`. -/
private noncomputable def compCompStepsCost (mem : ℕ → ℕ) (C : Finset ℕ) (L_w : ℕ) :
    CompLSFState → ℕ → List Update → ℕ
  | _, _, [] => 0
  | cs, ptr, u :: us =>
    (open Classical in
      if C ∈ touchedComps cs u then
        lsfBatchCostFactor * ((1 + projUpdWords mem cs C ptr u) * L_w + 1) +
        lsfBatchCostFactor * (projUpdWords mem cs C ptr u * L_w)
      else 0) +
    compCompStepsCost mem C L_w (compLSFStepSingle cs u) (ptr + dgUpdateMemLen mem ptr) us

private lemma projUpdWords_ge_two_of_touched {mem : ℕ → ℕ} {cs : CompLSFState} {C : Finset ℕ}
    {ptr len : ℕ} {u : Update}
    (hu : UpdateAt mem ptr cs.G u len) (hC : C ∈ touchedComps cs u) :
    2 ≤ projUpdWords mem cs C ptr u := by
  classical
  have hne : projCompUpdateG cs.G (cs.compSt C).G u ≠ [] := (Finset.mem_filter.mp hC).2
  cases u with
  | insert e a b =>
    simp only [projCompUpdateG] at hne
    have hab : a ∈ (cs.compSt C).G.V ∨ b ∈ (cs.compSt C).G.V := by
      split_ifs at hne with h1 h2 h3
      · exact Or.inl h1.1
      · exact Or.inl h2
      · exact Or.inr h3
      · exact absurd rfl hne
    dsimp only [projUpdWords]
    split_ifs <;> simp_all
  | delete e =>
    simp only [projCompUpdateG] at hne
    have he : e ∈ (cs.compSt C).G.E := by
      by_contra hnot; simp [hnot] at hne
    simp [projUpdWords, he]
  | split v v' St Sh =>
    simp only [projCompUpdateG] at hne
    have hv : v ∈ (cs.compSt C).G.V := by
      by_contra hnot; simp [hnot] at hne
    have hlen : dgUpdateMemLen mem ptr = len := dgUpdateMemLen_eq hu
    have hge2 : 2 ≤ len := updateAt_len_ge_two hu
    dsimp only [projUpdWords]
    rw [ite_eq_left hv, hlen]
    exact hge2

private lemma compCompStepsCost_le {mem : ℕ → ℕ} {C : Finset ℕ} {L_w : ℕ} (hLw : 1 ≤ L_w) :
    ∀ {cs : CompLSFState} {ptr tw : ℕ} {U : List Update},
      BatchBodyAt mem ptr cs.G U tw →
      compCompStepsCost mem C L_w cs ptr U ≤
        3 * lsfBatchCostFactor * (projBatchBodyWords mem C cs ptr U * L_w)
  | _, _, _, [], _ => by simp [compCompStepsCost, projBatchBodyWords]
  | cs, ptr, tw, u :: us, ⟨l, _, hu, hrest⟩ => by
    classical
    have hlen : dgUpdateMemLen mem ptr = l := dgUpdateMemLen_eq hu
    have ih := compCompStepsCost_le (C := C) hLw (cs := compLSFStepSingle cs u)
      (ptr := ptr + l) (U := us) hrest
    rw [← hlen] at ih
    simp only [compCompStepsCost, projBatchBodyWords]
    set w := projUpdWords mem cs C ptr u
    set W_rest := projBatchBodyWords mem C (compLSFStepSingle cs u) (ptr + dgUpdateMemLen mem ptr) us
    have hstep : (if C ∈ touchedComps cs u then
        lsfBatchCostFactor * ((1 + w) * L_w + 1) + lsfBatchCostFactor * (w * L_w) else 0) ≤
        3 * lsfBatchCostFactor * (w * L_w) := by
      split_ifs with hmem
      · have hw2 : 2 ≤ w := projUpdWords_ge_two_of_touched hu hmem
        have hinner : (1 + w) * L_w + 1 + w * L_w ≤ 3 * (w * L_w) := by
          have : 2 * L_w ≤ w * L_w := Nat.mul_le_mul_right L_w hw2
          have : (1 + w) * L_w = L_w + w * L_w := by ring
          omega
        calc lsfBatchCostFactor * ((1 + w) * L_w + 1) + lsfBatchCostFactor * (w * L_w)
            = lsfBatchCostFactor * ((1 + w) * L_w + 1 + w * L_w) := by ring
          _ ≤ lsfBatchCostFactor * (3 * (w * L_w)) := Nat.mul_le_mul_left _ hinner
          _ = 3 * lsfBatchCostFactor * (w * L_w) := by ring
      · exact Nat.zero_le _
    have hdist : 3 * lsfBatchCostFactor * ((w + W_rest) * L_w) =
        3 * lsfBatchCostFactor * (w * L_w) + 3 * lsfBatchCostFactor * (W_rest * L_w) := by ring
    omega

private lemma compBatchStepsCost_eq_sum {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {mem : ℕ → ℕ} {L_w : ℕ} :
    ∀ {cs : CompLSFState} {ptr : ℕ} {U : List Update},
      CompLSFInv C_lsst ℓ₀ cs → cs.G.BatchIsValid U →
      compBatchStepsCost mem L_w cs ptr U =
        (open Classical in
          ((touchedCompsBatch cs U).filter fun C => 1 ≤ (compGraph cs.G₀ C).m).sum fun C =>
            compCompStepsCost mem C L_w cs ptr U)
  | cs, ptr, [], _, _ => by
    classical
    simp [compBatchStepsCost, touchedCompsBatch, projCompBatchG]
  | cs, ptr, u :: us, hI, ⟨hu, hrest⟩ => by
    classical
    set cs1 := compLSFStepSingle cs u
    have hI1 : CompLSFInv C_lsst ℓ₀ cs1 := compLSFInv_step hI hu
    have ih := compBatchStepsCost_eq_sum (mem := mem) (L_w := L_w) (cs := cs1)
      (ptr := ptr + dgUpdateMemLen mem ptr) (U := us) hI1 hrest
    simp only [compBatchStepsCost]
    set S_all := (touchedCompsBatch cs (u :: us)).filter fun C => 1 ≤ (compGraph cs.G₀ C).m
    set S_u := (touchedComps cs u).filter fun C => 1 ≤ (compGraph cs.G₀ C).m
    set S_r := (touchedCompsBatch cs1 us).filter fun C => 1 ≤ (compGraph cs.G₀ C).m
    have hG0_eq : cs1.G₀ = cs.G₀ := rfl
    have hS_union : S_all = S_u ∪ S_r := by
      ext C; simp only [S_all, S_u, S_r, Finset.mem_filter, Finset.mem_union,
        touchedCompsBatch_cons hI hu]; tauto
    have h1 : S_u.sum (fun C => lsfBatchCostFactor * ((1 + projUpdWords mem cs C ptr u) * L_w + 1) +
        lsfBatchCostFactor * (projUpdWords mem cs C ptr u * L_w)) =
        S_all.sum (fun C => if C ∈ touchedComps cs u then
          lsfBatchCostFactor * ((1 + projUpdWords mem cs C ptr u) * L_w + 1) +
          lsfBatchCostFactor * (projUpdWords mem cs C ptr u * L_w) else 0) := by
      rw [← Finset.sum_filter]
      congr 1; ext C; simp only [Finset.mem_filter, S_u, S_r, hS_union, Finset.mem_union]; tauto
    have hcomp_zero_not : ∀ C, C ∉ touchedCompsBatch cs1 us →
        compCompStepsCost mem C L_w cs1 (ptr + dgUpdateMemLen mem ptr) us = 0 := by
      intro C hnot
      have haux : ∀ {cs' : CompLSFState} {p' : ℕ} {V : List Update},
          CompLSFInv C_lsst ℓ₀ cs' → cs'.G.BatchIsValid V → C ∉ touchedCompsBatch cs' V →
          compCompStepsCost mem C L_w cs' p' V = 0 := by
        intro cs' p' V
        induction V generalizing cs' p' with
        | nil => intros; rfl
        | cons v vs ihv =>
          intro hI' ⟨hv, hvs⟩ hnv
          rw [touchedCompsBatch_cons hI' hv, Finset.mem_union, not_or] at hnv
          simp only [compCompStepsCost, hnv.1, ↓reduceIte, zero_add]
          exact ihv (compLSFInv_step hI' hv) hvs hnv.2
      exact haux hI1 hrest hnot
    have h2 : S_r.sum (fun C => compCompStepsCost mem C L_w cs1 (ptr + dgUpdateMemLen mem ptr) us) =
        S_all.sum (fun C => compCompStepsCost mem C L_w cs1 (ptr + dgUpdateMemLen mem ptr) us) := by
      refine Finset.sum_subset (by rw [hS_union]; exact Finset.subset_union_right) fun C hCa hCr => ?_
      have hpos : 1 ≤ (compGraph cs.G₀ C).m := (Finset.mem_filter.mp hCa).2
      have hnt : C ∉ touchedCompsBatch cs1 us := fun h => hCr (Finset.mem_filter.mpr ⟨h, hpos⟩)
      exact hcomp_zero_not C hnt
    have hih : compBatchStepsCost mem L_w cs1 (ptr + dgUpdateMemLen mem ptr) us =
        S_r.sum (fun C => compCompStepsCost mem C L_w cs1 (ptr + dgUpdateMemLen mem ptr) us) := by
      simpa [S_r, hG0_eq] using ih
    change S_u.sum _ + compBatchStepsCost mem L_w cs1 (ptr + dgUpdateMemLen mem ptr) us = _
    rw [hih, h1, h2, ← Finset.sum_add_distrib]
    rfl

/-- Total per-step touched-edgeful dispatch cost across a valid encoded batch `U` is at most
`3 * sumTouchedLsfBatchCost`. -/
lemma compBatchStepsCost_le_three_mul {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {mem : ℕ → ℕ}
    {cs : CompLSFState} {batchPtr L_w tw : ℕ} {U : List Update}
    (hLw : 1 ≤ L_w) (hI : CompLSFInv C_lsst ℓ₀ cs) (hval : cs.G.BatchIsValid U)
    (hB : BatchAt mem batchPtr cs.G U tw) :
    compBatchStepsCost mem L_w cs (batchPtr + 1) U ≤
      3 * sumTouchedLsfBatchCost mem cs batchPtr L_w U := by
  classical
  rw [compBatchStepsCost_eq_sum hI hval, sumTouchedLsfBatchCost, Finset.mul_sum]
  refine Finset.sum_le_sum fun C _ => ?_
  calc compCompStepsCost mem C L_w cs (batchPtr + 1) U
      ≤ 3 * lsfBatchCostFactor * (projBatchBodyWords mem C cs (batchPtr + 1) U * L_w) :=
        compCompStepsCost_le hLw hB.2.2
    _ = 3 * (lsfBatchCostFactor * (projBatchBodyWords mem C cs (batchPtr + 1) U * L_w)) := by ring
    _ ≤ 3 * compProjLsfBatchCost mem cs C batchPtr L_w U := by
        refine Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left lsfBatchCostFactor ?_)
        have := Nat.mul_le_mul_right L_w
          (Nat.le_add_left (projBatchBodyWords mem C cs (batchPtr + 1) U) 1)
        omega

/-! ## 3. Forest-cut combination across steps -/

lemma compLSFStepSingle_ins_RF_V_ends {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {e a bVert : ℕ} (hI : CompLSFInv C_lsst ℓ₀ cs) (hu : cs.G.UpdateIsValid (.insert e a bVert)) :
    let cs1 := compLSFStepSingle cs (.insert e a bVert)
    cs1.RF.F.V = cs.RF.F.V ∧
    ∀ f ∈ cs1.RF.F.E, cs1.RF.F.E ⊆ cs.RF.F.E →
      cs1.RF.F.tail f = cs.RF.F.tail f ∧ cs1.RF.F.head f = cs.RF.F.head f := by
  intro cs1
  have hG : cs1.G = cs.G.applyUpdate (.insert e a bVert) := by
    simp only [cs1, compLSFStepSingle]
  have hV : cs1.RF.F.V = cs1.G.V := by simp only [CompLSFState.RF]
  have hV0 : cs.RF.F.V = cs.G.V := by simp only [CompLSFState.RF]
  have hT : ∀ f, cs1.RF.F.tail f = cs1.G.tail f := fun _ => by simp only [CompLSFState.RF]
  have hT0 : ∀ f, cs.RF.F.tail f = cs.G.tail f := fun _ => by simp only [CompLSFState.RF]
  have hH : ∀ f, cs1.RF.F.head f = cs1.G.head f := fun _ => by simp only [CompLSFState.RF]
  have hH0 : ∀ f, cs.RF.F.head f = cs.G.head f := fun _ => by simp only [CompLSFState.RF]
  refine ⟨by rw [hV, hV0, hG]; rfl, fun f hf hsub => ?_⟩
  have hfG : f ∈ cs.G.E := (compLSF_RF_isRSF hI).2.2.2.2.2.1 (hsub hf)
  have hne : f ≠ e := fun h => hu.1 (h ▸ hfG)
  rw [hT, hT0, hH, hH0, hG]
  dsimp only [MGraph.applyUpdate]
  exact ⟨Function.update_of_ne hne a cs.G.tail, Function.update_of_ne hne bVert cs.G.head⟩

/-- Combine forest cuts and split vertices across a non-split step `cs → cs1` followed by a
remaining batch `cs1 → cs2`. -/
lemma compBatchStep_cuts_combine_nonSplit {vCap : ℕ} {cs cs1 cs2 : CompLSFState}
    {cuts1 cuts2 : List (ℕ × ℕ)} {sp2 : List ℕ}
    (hV1 : cs1.RF.F.V = cs.RF.F.V)
    (hends1 : ∀ f ∈ cs1.RF.F.E, cs1.RF.F.tail f = cs.RF.F.tail f ∧ cs1.RF.F.head f = cs.RF.F.head f)
    (hval1 : CompForestCutsValid vCap cs.RF cuts1)
    (hndE1 : (cuts1.map Prod.fst).Nodup)
    (hsE1 : (cuts1.map Prod.fst).toFinset = cs.RF.F.E \ cs1.RF.F.E)
    (hEsub1 : cs1.RF.F.E ⊆ cs.RF.F.E)
    (hndR1 : (cuts1.map Prod.snd).Nodup)
    (hsR1 : (cuts1.map Prod.snd).toFinset = cs1.RF.R \ cs.RF.R)
    (hRsub1 : cs.RF.R ⊆ cs1.RF.R)
    (hval2 : CompForestCutsValid vCap cs1.RF cuts2)
    (hndE2 : (cuts2.map Prod.fst).Nodup)
    (hsE2 : (cuts2.map Prod.fst).toFinset = cs1.RF.F.E \ cs2.RF.F.E)
    (hEsub2 : cs2.RF.F.E ⊆ cs1.RF.F.E)
    (hndR2 : (cuts2.map Prod.snd).Nodup)
    (hndS2 : sp2.Nodup)
    (hdisj2 : ∀ r ∈ cuts2.map Prod.snd, r ∉ sp2)
    (hsR2 : (cuts2.map Prod.snd).toFinset ∪ sp2.toFinset = cs2.RF.R \ cs1.RF.R)
    (hRsub2 : cs1.RF.R ⊆ cs2.RF.R) :
    let cuts := cuts1 ++ cuts2
    CompForestCutsValid vCap cs.RF cuts ∧
    (cuts.map Prod.fst).Nodup ∧
    (cuts.map Prod.fst).toFinset = cs.RF.F.E \ cs2.RF.F.E ∧
    cs2.RF.F.E ⊆ cs.RF.F.E ∧
    (cuts.map Prod.snd).Nodup ∧
    sp2.Nodup ∧
    (∀ r ∈ cuts.map Prod.snd, r ∉ sp2) ∧
    (cuts.map Prod.snd).toFinset ∪ sp2.toFinset = cs2.RF.R \ cs.RF.R ∧
    cs.RF.R ⊆ cs2.RF.R := by
  intro cuts
  set RF1 := cuts1.foldl compApplyForestCut cs.RF
  have hRF1_E : RF1.F.E = cs1.RF.F.E := by
    rw [compApplyForestCut_foldl_E, hsE1]
    ext f; simp only [Finset.mem_sdiff]; exact ⟨fun ⟨h1, h2⟩ => by_contra fun hn => h2 ⟨h1, hn⟩,
      fun h => ⟨hEsub1 h, fun h' => h'.2 h⟩⟩
  have hRF1_R : RF1.R = cs1.RF.R := by
    rw [compApplyForestCut_foldl_R, hsR1]
    ext r; simp only [Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h => h.elim (fun h1 => hRsub1 h1) (fun h2 => h2.1),
      fun h => by by_cases h0 : r ∈ cs.RF.R; exact Or.inl h0; exact Or.inr ⟨h, h0⟩⟩
  have hval2_RF1 : CompForestCutsValid vCap RF1 cuts2 :=
    compForestCutsValid_congr (RF₁ := cs1.RF) (RF₂ := RF1)
      (hV1.trans (compApplyForestCut_foldl_V _ _).symm) hRF1_E.symm hRF1_R.symm
      (fun f hf => by rw [compApplyForestCut_foldl_tail, compApplyForestCut_foldl_head]; exact hends1 f hf)
      hval2
  refine ⟨compForestCutsValid_append hval1 hval2_RF1, ?_, ?_, hEsub2.trans hEsub1, ?_, hndS2, ?_, ?_, hRsub1.trans hRsub2⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hndE1, hndE2, fun f hf1 g hg2 heq => ?_⟩
    subst heq
    have h1 : f ∈ cs.RF.F.E \ cs1.RF.F.E := hsE1 ▸ List.mem_toFinset.mpr hf1
    have h2 : f ∈ cs1.RF.F.E \ cs2.RF.F.E := hsE2 ▸ List.mem_toFinset.mpr hg2
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
  · rw [List.map_append, List.toFinset_append, hsE1, hsE2]
    ext f; simp only [Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h => h.elim (fun h1 => ⟨h1.1, fun h2 => h1.2 (hEsub2 h2)⟩) (fun h2 => ⟨hEsub1 h2.1, h2.2⟩),
      fun ⟨h0, hn2⟩ => by by_cases h1 : f ∈ cs1.RF.F.E; exact Or.inr ⟨h1, hn2⟩; exact Or.inl ⟨h0, h1⟩⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hndR1, hndR2, fun r hr1 s hs2 heq => ?_⟩
    subst heq
    have h1 : r ∈ cs1.RF.R \ cs.RF.R := hsR1 ▸ List.mem_toFinset.mpr hr1
    have h2 : r ∈ cs2.RF.R \ cs1.RF.R := hsR2 ▸ Finset.mem_union_left _ (List.mem_toFinset.mpr hs2)
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_sdiff.mp h1).1
  · intro r hr hsp
    rw [List.map_append, List.mem_append] at hr
    rcases hr with hr1 | hr2
    · have h1 : r ∈ cs1.RF.R \ cs.RF.R := hsR1 ▸ List.mem_toFinset.mpr hr1
      have h2 : r ∈ cs2.RF.R \ cs1.RF.R := hsR2 ▸ Finset.mem_union_right _ (List.mem_toFinset.mpr hsp)
      exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_sdiff.mp h1).1
    · exact hdisj2 r hr2 hsp
  · rw [List.map_append, List.toFinset_append, Finset.union_assoc, hsR1, hsR2]
    ext r; simp only [Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h => h.elim (fun h1 => ⟨hRsub2 h1.1, h1.2⟩) (fun h2 => ⟨h2.1, fun h0 => h2.2 (hRsub1 h0)⟩),
      fun ⟨h2, hn0⟩ => by by_cases h1 : r ∈ cs1.RF.R; exact Or.inl ⟨h1, hn0⟩; exact Or.inr ⟨h2, h1⟩⟩

/-- Combine forest cuts and split vertices across a split step `cs → cs1` (creating `v'`) followed
by a remaining batch `cs1 → cs2`. -/
lemma compBatchStep_cuts_combine_split {vCap v v' : ℕ} {cs cs1 cs2 : CompLSFState}
    {cuts1 cuts2 : List (ℕ × ℕ)} {sp2 : List ℕ}
    (hval1 : CompForestCutsValid vCap cs.RF cuts1)
    (hndE1 : (cuts1.map Prod.fst).Nodup)
    (hsE1 : (cuts1.map Prod.fst).toFinset = cs.RF.F.E \ cs1.RF.F.E)
    (hEsub1 : cs1.RF.F.E ⊆ cs.RF.F.E)
    (hndR1 : (cuts1.map Prod.snd).Nodup)
    (hv'_not0 : v' ∉ cs.RF.R) (hv'_in1 : v' ∈ cs1.RF.R) (hv'_not_c1 : v' ∉ cuts1.map Prod.snd)
    (hsR1 : (cuts1.map Prod.snd).toFinset = cs1.RF.R.erase v' \ cs.RF.R)
    (hRsub1 : cs.RF.R ⊆ cs1.RF.R)
    (hmid_val : (cuts1.foldl compApplyForestCut cs.RF).F.IsValid)
    (hv_midR : v ∈ (cuts1.foldl compApplyForestCut cs.RF).R)
    (hv_midV : v ∈ (cuts1.foldl compApplyForestCut cs.RF).F.V)
    (hv'_not_midV : v' ∉ (cuts1.foldl compApplyForestCut cs.RF).F.V)
    (hV1 : cs1.RF.F.V = insert v' (cuts1.foldl compApplyForestCut cs.RF).F.V)
    (hE1 : cs1.RF.F.E = (cuts1.foldl compApplyForestCut cs.RF).F.E)
    (hR1 : cs1.RF.R = insert v' (cuts1.foldl compApplyForestCut cs.RF).R)
    (hends1 : ∀ e ∈ (cuts1.foldl compApplyForestCut cs.RF).F.E,
      unsplitMap v v' (cs1.RF.F.tail e) = (cuts1.foldl compApplyForestCut cs.RF).F.tail e ∧
      unsplitMap v v' (cs1.RF.F.head e) = (cuts1.foldl compApplyForestCut cs.RF).F.head e)
    (hval2 : CompForestCutsValid vCap cs1.RF cuts2)
    (hndE2 : (cuts2.map Prod.fst).Nodup)
    (hsE2 : (cuts2.map Prod.fst).toFinset = cs1.RF.F.E \ cs2.RF.F.E)
    (hEsub2 : cs2.RF.F.E ⊆ cs1.RF.F.E)
    (hndR2 : (cuts2.map Prod.snd).Nodup)
    (hndS2 : sp2.Nodup)
    (hdisj2 : ∀ r ∈ cuts2.map Prod.snd, r ∉ sp2)
    (hsR2 : (cuts2.map Prod.snd).toFinset ∪ sp2.toFinset = cs2.RF.R \ cs1.RF.R)
    (hRsub2 : cs1.RF.R ⊆ cs2.RF.R) :
    let cuts := cuts1 ++ cuts2
    let sp := v' :: sp2
    CompForestCutsValid vCap cs.RF cuts ∧
    (cuts.map Prod.fst).Nodup ∧
    (cuts.map Prod.fst).toFinset = cs.RF.F.E \ cs2.RF.F.E ∧
    cs2.RF.F.E ⊆ cs.RF.F.E ∧
    (cuts.map Prod.snd).Nodup ∧
    sp.Nodup ∧
    (∀ r ∈ cuts.map Prod.snd, r ∉ sp) ∧
    (cuts.map Prod.snd).toFinset ∪ sp.toFinset = cs2.RF.R \ cs.RF.R ∧
    cs.RF.R ⊆ cs2.RF.R := by
  intro cuts sp
  have hv'_not_c2 : ∀ p ∈ cuts2, p.2 ≠ v' := fun p hp heq => by
    have hm : v' ∈ cs2.RF.R \ cs1.RF.R :=
      hsR2 ▸ Finset.mem_union_left _ (List.mem_toFinset.mpr (heq ▸ List.mem_map_of_mem hp))
    exact (Finset.mem_sdiff.mp hm).2 hv'_in1
  have hv'_not_sp2 : v' ∉ sp2 := fun h => by
    have hm : v' ∈ cs2.RF.R \ cs1.RF.R := hsR2 ▸ Finset.mem_union_right _ (List.mem_toFinset.mpr h)
    exact (Finset.mem_sdiff.mp hm).2 hv'_in1
  have hval2_mid : CompForestCutsValid vCap (cuts1.foldl compApplyForestCut cs.RF) cuts2 :=
    compForestCutsValid_of_splitRoot cuts2 _ cs1.RF hmid_val hv_midR hv_midV hv'_not_midV
      hV1 hE1 hR1 hends1 hv'_not_c2 hval2
  refine ⟨compForestCutsValid_append hval1 hval2_mid, ?_, ?_, hEsub2.trans hEsub1, ?_,
    List.nodup_cons.mpr ⟨hv'_not_sp2, hndS2⟩, ?_, ?_, hRsub1.trans hRsub2⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hndE1, hndE2, fun f hf1 g hg2 heq => ?_⟩
    subst heq
    have h1 : f ∈ cs.RF.F.E \ cs1.RF.F.E := hsE1 ▸ List.mem_toFinset.mpr hf1
    have h2 : f ∈ cs1.RF.F.E \ cs2.RF.F.E := hsE2 ▸ List.mem_toFinset.mpr hg2
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
  · rw [List.map_append, List.toFinset_append, hsE1, hsE2]
    ext f; simp only [Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h => h.elim (fun h1 => ⟨h1.1, fun h2 => h1.2 (hEsub2 h2)⟩) (fun h2 => ⟨hEsub1 h2.1, h2.2⟩),
      fun ⟨h0, hn2⟩ => by by_cases h1 : f ∈ cs1.RF.F.E; exact Or.inr ⟨h1, hn2⟩; exact Or.inl ⟨h0, h1⟩⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨hndR1, hndR2, fun r hr1 s hs2 heq => ?_⟩
    subst heq
    have h1 : r ∈ cs1.RF.R.erase v' \ cs.RF.R := hsR1 ▸ List.mem_toFinset.mpr hr1
    have h2 : r ∈ cs2.RF.R \ cs1.RF.R := hsR2 ▸ Finset.mem_union_left _ (List.mem_toFinset.mpr hs2)
    exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_of_mem_erase (Finset.mem_sdiff.mp h1).1)
  · intro r hr hsp
    rw [List.map_append, List.mem_append] at hr
    rcases List.mem_cons.mp hsp with rfl | hsp2
    · rcases hr with hr1 | hr2
      · exact hv'_not_c1 hr1
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr2; exact hv'_not_c2 p hp rfl
    · rcases hr with hr1 | hr2
      · have h1 : r ∈ cs1.RF.R.erase v' \ cs.RF.R := hsR1 ▸ List.mem_toFinset.mpr hr1
        have h2 : r ∈ cs2.RF.R \ cs1.RF.R := hsR2 ▸ Finset.mem_union_right _ (List.mem_toFinset.mpr hsp2)
        exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_of_mem_erase (Finset.mem_sdiff.mp h1).1)
      · exact hdisj2 r hr2 hsp2
  · rw [List.map_append, List.toFinset_append, List.toFinset_cons]
    have hrearr : (cuts1.map Prod.snd).toFinset ∪ (cuts2.map Prod.snd).toFinset ∪ insert v' sp2.toFinset =
        insert v' (cuts1.map Prod.snd).toFinset ∪ ((cuts2.map Prod.snd).toFinset ∪ sp2.toFinset) := by
      ext r; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [hrearr, hsR1, hsR2]
    ext r; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ((rfl | ⟨⟨_, h1⟩, hn0⟩) | ⟨h2, hn1⟩)
      · exact ⟨hRsub2 hv'_in1, hv'_not0⟩
      · exact ⟨hRsub2 h1, hn0⟩
      · exact ⟨h2, fun h0 => hn1 (hRsub1 h0)⟩
    · rintro ⟨h2, hn0⟩
      by_cases h1 : r ∈ cs1.RF.R
      · by_cases hrv : r = v'
        · exact Or.inl (Or.inl hrv)
        · exact Or.inl (Or.inr ⟨⟨hrv, h1⟩, hn0⟩)
      · exact Or.inr ⟨h2, h1⟩

/-! ## 4. `BatchBodyAt` memory agreement -/

lemma compBatchBodyAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {tw : ℕ}
    (h : BatchBodyAt mem₁ a G U tw) (hag : ∀ i < tw, mem₂ (a + i) = mem₁ (a + i)) :
    BatchBodyAt mem₂ a G U tw := by
  induction U generalizing a tw G with
  | nil => rcases h with rfl; rfl
  | cons u us ih =>
    rcases h with ⟨l, r, hu, hr⟩
    have hu' : UpdateAt mem₂ a G u l := by
      cases u with
      | insert e x y =>
        rcases hu with ⟨rfl, hLA⟩
        exact ⟨rfl, fun i hi => (hag i (by simp at hi; omega)).trans (hLA i hi)⟩
      | delete e =>
        rcases hu with ⟨rfl, hLA⟩
        exact ⟨rfl, fun i hi => (hag i (by simp at hi; omega)).trans (hLA i hi)⟩
      | split v v' St Sh =>
        rcases hu with ⟨Lt, Lh, h1, h2, h3, h4, hlen, hLA⟩ | ⟨Lt, Lh, h1, h2, h3, h4, hlen, hLA⟩
        · left; exact ⟨Lt, Lh, h1, h2, h3, h4, hlen, fun i hi =>
            (hag i (by simp at hi; omega)).trans (hLA i hi)⟩
        · right; exact ⟨Lt, Lh, h1, h2, h3, h4, hlen, fun i hi =>
            (hag i (by simp at hi; omega)).trans (hLA i hi)⟩
    exact ⟨l, r, hu', ih hr fun i hi => by
      have := hag (l + i) (by omega); rwa [← Nat.add_assoc] at this⟩

end

end MinCostFlow.SparseCore.Program
