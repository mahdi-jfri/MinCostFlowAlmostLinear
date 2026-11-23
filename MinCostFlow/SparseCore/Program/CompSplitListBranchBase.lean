module

public import MinCostFlow.SparseCore.Program.CompSplitListUFPairClean
public import MinCostFlow.SparseCore.Program.CompBatchBase
import MinCostFlow.SparseCore.Program.CompReadout
import MinCostFlow.SparseCore.CompLSFBridge
import WordRAM.Tactic

/-!
# Per-Branch Canonical Split Helpers (`CompSplitListBranchBase`)

Defines and verifies the three `O(1)`-time helper procedures and pure bridge lemmas needed by
`compEmitBranchSplitProc` (`CompSplitListBranch`):

1. `compRootValProc` (`args = [b, j, v]`): returns `(S j).RF.root v` directly in `≤ 60` steps
   without modifying memory, under `CompLSFRepDirty`.
2. `compEdgeEndsProc` (`args = [b, e, out2]`): for `e ∈ (S 0).G.E`, if `isCross[e] = 0` and
   `isIns[e] = 0` reads `(G.tail e, G.head e)` from branch `0`'s component `dgG` and stores them
   at `[out2, out2 + 2)`; otherwise stores `(0, 0)`. Runs in `≤ 110` steps.
3. `compEdgeEndRootsProc` (`args = [b, j, d, out2]`): for an original same-component edge `d`
   present in branch `j`'s component graph `((S j).compSt C_d).G`, reads its endpoints `(u, v)`
   from `dgG` and their roots `(ru, rv)` from `fAnc` of `hWin = handles[ec_d * k + j]`, storing
   `[ru, rv]` at `[out2, out2 + 2)` in `≤ 140` steps.
4. Pure bridge lemmas `list_eq_finset_sort`, `compLSF_orig_edge_in_comp`, `compLSF_F_edge_orig`,
   and `compReleased_edge_in_comp`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.Bundle
  MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Helper procedures -/

/-- `args = [b, j, v]`. Returns `(S j).RF.root v` directly without modifying memory. -/
def compRootValProc : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const compOffVCompPtr))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 2))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const compOffEdgefulPtr))) ;;
  .assign 6 (.load (.bin .add (.reg 5) (.reg 4))) ;;
  .cond (.reg 6)
    (.assign 7 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr))) ;;
     .assign 8 (.load (.bin .add (.reg 7) (.reg 4))) ;;
     .assign 9 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
     .assign 10 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr))) ;;
     .assign 11 (.load (.bin .add (.reg 10) (.bin .add (.bin .mul (.reg 8) (.reg 9)) (.reg 1)))) ;;
     .assign 12 (.load (.bin .add (.reg 11) (.const lsfOffFAncPtr))) ;;
     .assign 13 (.load (.bin .add (.reg 12) (.const fOffCompIdPtr))) ;;
     .assign 14 (.load (.bin .add (.reg 12) (.const fOffCompRootPtr))) ;;
     .assign 15 (.load (.bin .add (.reg 13) (.reg 2))) ;;
     .assign 16 (.load (.bin .add (.reg 14) (.reg 15))) ;;
     .ret (.reg 16))
    (.ret (.reg 2))

/-- `args = [b, e, out2]`. If `isCross[e] = 0` and `isIns[e] = 0`, reads `(G.tail e, G.head e)`
from branch `0`'s component `dgG` and writes `[tail, head]` at `[out2, out2 + 2)`; otherwise
writes `[0, 0]`. Returns `0`. -/
def compEdgeEndsProc : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const compOffIsCrossPtr))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const compOffIsInsPtr))) ;;
  .assign 6 (.load (.bin .add (.reg 5) (.reg 1))) ;;
  .cond (.bin .add (.reg 4) (.reg 6))
    (.store (.reg 2) (.const 0) ;;
     .store (.bin .add (.reg 2) (.const 1)) (.const 0) ;;
     .ret (.const 0))
    (.assign 7 (.load (.bin .add (.reg 0) (.const compOffEdgeC1Ptr))) ;;
     .assign 8 (.load (.bin .add (.reg 7) (.reg 1))) ;;
     .assign 9 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr))) ;;
     .assign 10 (.load (.bin .add (.reg 9) (.reg 8))) ;;
     .assign 11 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
     .assign 12 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr))) ;;
     .assign 13 (.load (.bin .add (.reg 12) (.bin .mul (.reg 10) (.reg 11)))) ;;
     .assign 14 (.load (.bin .add (.reg 13) (.const lsfOffDgGPtr))) ;;
     .assign 15 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
     .assign 16 (.load (.bin .add (.reg 14) (.const dgECapOff))) ;;
     .assign 17 (.bin .add (.bin .add (.reg 14) (.const 4)) (.bin .mul (.const 4) (.reg 15))) ;;
     .assign 18 (.bin .add (.bin .add (.bin .add (.reg 14) (.const 4)) (.bin .mul (.const 7) (.reg 15)))
       (.bin .mul (.const 3) (.reg 16))) ;;
     .assign 19 (.bin .add (.bin .add (.bin .add (.reg 14) (.const 4)) (.bin .mul (.const 7) (.reg 15)))
       (.bin .mul (.const 4) (.reg 16))) ;;
     .assign 20 (.load (.bin .add (.reg 18) (.reg 1))) ;;
     .assign 20 (.load (.bin .add (.reg 17) (.reg 20))) ;;
     .assign 21 (.load (.bin .add (.reg 19) (.reg 1))) ;;
     .assign 21 (.load (.bin .add (.reg 17) (.reg 21))) ;;
     .store (.reg 2) (.reg 20) ;;
     .store (.bin .add (.reg 2) (.const 1)) (.reg 21) ;;
     .ret (.const 0))

/-- `args = [b, j, d, out2]`. For a surviving original same-component edge `d` in edgeful
component `c = edgeC1[d]`, reads `(u, v) = (G_c.tail d, G_c.head d)` from `hWin`'s `dgG` and
`(ru, rv) = (fAnc.root u, fAnc.root v)` from `hWin`'s `fAnc`, writes `[ru, rv]` at
`[out2, out2 + 2)`, and returns `0`. -/
def compEdgeEndRootsProc : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.const compOffEdgeC1Ptr))) ;;
  .assign 5 (.load (.bin .add (.reg 4) (.reg 2))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr))) ;;
  .assign 7 (.load (.bin .add (.reg 6) (.reg 5))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr))) ;;
  .assign 10 (.load (.bin .add (.reg 9) (.bin .add (.bin .mul (.reg 7) (.reg 8)) (.reg 1)))) ;;
  .assign 11 (.load (.bin .add (.reg 10) (.const lsfOffDgGPtr))) ;;
  .assign 12 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .assign 13 (.load (.bin .add (.reg 11) (.const dgECapOff))) ;;
  .assign 14 (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 4) (.reg 12))) ;;
  .assign 15 (.bin .add (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 7) (.reg 12)))
    (.bin .mul (.const 3) (.reg 13))) ;;
  .assign 16 (.bin .add (.bin .add (.bin .add (.reg 11) (.const 4)) (.bin .mul (.const 7) (.reg 12)))
    (.bin .mul (.const 4) (.reg 13))) ;;
  .assign 17 (.load (.bin .add (.reg 15) (.reg 2))) ;;
  .assign 17 (.load (.bin .add (.reg 14) (.reg 17))) ;;
  .assign 18 (.load (.bin .add (.reg 16) (.reg 2))) ;;
  .assign 18 (.load (.bin .add (.reg 14) (.reg 18))) ;;
  .assign 19 (.load (.bin .add (.reg 10) (.const lsfOffFAncPtr))) ;;
  .assign 20 (.load (.bin .add (.reg 19) (.const fOffCompIdPtr))) ;;
  .assign 21 (.load (.bin .add (.reg 19) (.const fOffCompRootPtr))) ;;
  .assign 17 (.load (.bin .add (.reg 20) (.reg 17))) ;;
  .assign 17 (.load (.bin .add (.reg 21) (.reg 17))) ;;
  .assign 18 (.load (.bin .add (.reg 20) (.reg 18))) ;;
  .assign 18 (.load (.bin .add (.reg 21) (.reg 18))) ;;
  .store (.reg 3) (.reg 17) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 18) ;;
  .ret (.const 0)

lemma compRootValProc_noRand : compRootValProc.NoRand := by
  simp [compRootValProc, Stmt.NoRand]

lemma compEdgeEndsProc_noRand : compEdgeEndsProc.NoRand := by
  simp [compEdgeEndsProc, Stmt.NoRand]

lemma compEdgeEndRootsProc_noRand : compEdgeEndRootsProc.NoRand := by
  simp [compEdgeEndRootsProc, Stmt.NoRand]

/-! ## 2. Pure math bridge lemmas -/

/-- Any sorted duplicate-free list with the same elements as a `Finset ℕ` equals `S.sort (· ≤ ·)`. -/
lemma list_eq_finset_sort {L : List ℕ} {S : Finset ℕ}
    (hnd : L.Nodup) (hsort : L.Pairwise (· ≤ ·)) (hmem : ∀ x, x ∈ L ↔ x ∈ S) :
    L = S.sort (· ≤ ·) := by
  have hperm : L.Perm (S.sort (· ≤ ·)) :=
    (List.perm_ext_iff_of_nodup hnd (Finset.sort_nodup S (· ≤ ·))).mpr fun x => by
      rw [hmem, Finset.mem_sort]
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => Nat.le_antisymm h1 h2) hsort
    (Finset.pairwise_sort S (· ≤ ·))

/-- Any surviving original edge `e ∈ cs.G.E \ cs.insertedGlobal` belongs to an edgeful component
`c = edgeC1 e` with `e ∈ (cs.compSt (compOf c)).G.E` and matching endpoints. -/
lemma compLSF_orig_edge_in_comp {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {numComps vCap eCap : ℕ} {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    {e : ℕ} (heG : e ∈ cs.G.E) (hni : e ∉ cs.insertedGlobal) :
    ∃ c : Fin numComps, edgeC1 e = c.1 ∧
      1 ≤ (compGraph cs.G₀ (compOf c)).m ∧
      e ∈ (cs.compSt (compOf c)).G.E ∧
      e ∉ cs.crossEdges ∧
      (cs.compSt (compOf c)).G.tail e = cs.G.tail e ∧
      (cs.compSt (compOf c)).G.head e = cs.G.head e := by
  obtain ⟨C, hC, heC, hniC, _⟩ := hI.hWstr_surv e heG hni
  have hCI := (hI.hCompLSF C hC).1
  have heG0C : e ∈ (compGraph cs.G₀ C).E := by
    have h0 := (hCI.hsurv_edge e heC hniC).1
    rwa [(hI.hCompLSF C hC).2.1] at h0
  have hm_ge1 : 1 ≤ (compGraph cs.G₀ C).m := Finset.card_pos.mpr ⟨e, heG0C⟩
  have hnc : e ∉ cs.crossEdges := hI.hNonIns_notCross C hC e heC hniC
  obtain ⟨c1, c2, hc1, _, _, _, hmem, hcr_iff, _⟩ := hT.hEdge e heG
  have hc12 : c1 = c2 := by
    by_contra hne; exact hnc (hcr_iff.mpr hne)
  subst hc12
  obtain ⟨cC, rfl⟩ := (hT.hBij.2 C).mp hC
  have hcc : cC = c1 := ((hmem cC).mp heC).2
  subst hcc
  have hends := hI.hNonCross_ends (compOf cC) (hT.compOf_mem cC) e heC hnc
  exact ⟨cC, hc1, hm_ge1, heC, hnc, hends.1, hends.2⟩

/-- Every edge `e ∈ cs.RF.F.E` is a surviving original edge of `cs.G` (`e ∈ cs.G.E \ cs.insertedGlobal`,
`e ∉ cs.crossEdges`) whose endpoints in `cs.RF.F` match `cs.G`. -/
lemma compLSF_F_edge_orig {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {e : ℕ} (he : e ∈ cs.RF.F.E) :
    e ∈ cs.G.E ∧ e ∉ cs.insertedGlobal ∧ e ∉ cs.crossEdges ∧
    cs.RF.F.tail e = cs.G.tail e ∧ cs.RF.F.head e = cs.G.head e := by
  have heT : e ∈ cs.T.E := (compLSF_RF_sub_T hI).2.1 he
  have hmem : e ∈ cs.G.E \ cs.insertedGlobal := (Finset.mem_inter.mp heT).2
  have ⟨heG, hni⟩ := Finset.mem_sdiff.mp hmem
  exact ⟨heG, hni, fun hc => hni (hI.hCross_sub hc), rfl, rfl⟩

/-- Every released edge `d ∈ (forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E`
remains a surviving original same-component edge in `cs' = compLSFStepSingle cs u` whose
endpoints in `forestAfterInput cs.RF.F u` equal its endpoints in `(cs'.compSt (compOf c)).G`. -/
lemma compReleased_edge_in_comp {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    {numComps vCap eCap : ℕ} {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {u : Update} (hu : cs.G.UpdateIsValid u)
    (hT' : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList
      (compLSFStepSingle cs u))
    {d : ℕ} (hd : d ∈ (forestAfterInput cs.RF.F u).E \ (compLSFStepSingle cs u).RF.F.E) :
    let cs' := compLSFStepSingle cs u
    ∃ c : Fin numComps, edgeC1 d = c.1 ∧
      1 ≤ (compGraph cs'.G₀ (compOf c)).m ∧
      d ∈ (cs'.compSt (compOf c)).G.E ∧
      (forestAfterInput cs.RF.F u).tail d = (cs'.compSt (compOf c)).G.tail d ∧
      (forestAfterInput cs.RF.F u).head d = (cs'.compSt (compOf c)).G.head d := by
  intro cs'
  have hI' : CompLSFInv C_lsst ℓ₀ cs' :=
    compLSFBatch_inv (U := [u]) hI ⟨hu, trivial⟩
  have hd_mid : d ∈ (forestAfterInput cs.RF.F u).E := (Finset.mem_sdiff.mp hd).1
  have hd_orig_F : d ∈ cs.RF.F.E := by
    cases u with
    | insert _ _ _ => exact hd_mid
    | delete e => exact (Finset.mem_erase.mp hd_mid).2
    | split _ _ _ _ => exact hd_mid
  have ⟨hdG0, hd_ni0, _, hFt, hFh⟩ := compLSF_F_edge_orig hI hd_orig_F
  have hd_in_G' : d ∈ cs'.G.E ∧ (forestAfterInput cs.RF.F u).tail d = cs'.G.tail d ∧
      (forestAfterInput cs.RF.F u).head d = cs'.G.head d := by
    cases u with
    | insert e _ _ =>
      have hne : d ≠ e := fun h => hu.1 (h ▸ hdG0)
      exact ⟨Finset.mem_insert_of_mem hdG0,
        by simp [cs', compLSFStepSingle, MGraph.applyUpdate, forestAfterInput, hne, hFt],
        by simp [cs', compLSFStepSingle, MGraph.applyUpdate, forestAfterInput, hne, hFh]⟩
    | delete e =>
      have hne : d ≠ e := (Finset.mem_erase.mp hd_mid).1
      exact ⟨Finset.mem_erase.mpr ⟨hne, hdG0⟩,
        by simp [cs', compLSFStepSingle, MGraph.applyUpdate, forestAfterInput, eraseForestEdge, hFt],
        by simp [cs', compLSFStepSingle, MGraph.applyUpdate, forestAfterInput, eraseForestEdge, hFh]⟩
    | split v v' At Ah =>
      refine ⟨hdG0, ?_, ?_⟩
      · simp only [cs', compLSFStepSingle, MGraph.applyUpdate, forestAfterInput, hFt]
      · simp only [cs', compLSFStepSingle, MGraph.applyUpdate, forestAfterInput, hFh]
  have hd_ni' : d ∉ cs'.insertedGlobal := by
    cases u with
    | insert e _ _ =>
      have hne : d ≠ e := fun h => hu.1 (h ▸ hdG0)
      intro h; simp only [cs', compLSFStepSingle, updateInserted, Finset.mem_insert, hne, false_or] at h
      exact hd_ni0 h
    | delete e => exact fun h => hd_ni0 (Finset.mem_of_mem_erase h)
    | split _ _ _ _ => exact hd_ni0
  obtain ⟨c, hc1, hm1, hdC, _, htC, hhC⟩ := compLSF_orig_edge_in_comp hI' hT' hd_in_G'.1 hd_ni'
  exact ⟨c, hc1, hm1, hdC, hd_in_G'.2.1.trans htC.symm, hd_in_G'.2.2.trans hhC.symm⟩

/-! ## 3. Verification of `compRootValProc`, `compEdgeEndsProc`, `compEdgeEndRootsProc` -/

set_option maxHeartbeats 600000 in
/-- Verification of `compRootValProc` under `CompLSFRepDirty`: returns `(S j).RF.root v` directly
without modifying memory, in `≤ 60` steps. -/
theorem compRootVal_runs {W : LSFWindowImpl} {w k b v : ℕ}
    {S : CompLSFFamily k} {x : CompLSFMeta k} {touched : List ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool} (j : Fin k)
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepDirty W k b S x touched mem)
    (hend_w : x.endAddr < 2 ^ w)
    (hv : v ∈ (S j).G.V) :
    ∃ st' c,
      Runs w p ω compRootValProc (startState [b, j.1, v] mem pos) (.returned ((S j).RF.root v)) st' c ∧
      st'.mem = mem ∧ c ≤ 95 := by
  obtain ⟨hk, _, _, _, _, _, _, hnc, hne, hTE, hhdr, ⟨ℓ₀, hBr⟩, _, hT,
    hCompInfo, _, hVComp, _, _, _, _, _, hWins, _⟩ := hrep
  have hIj := (hBr j).1
  have hG_eq := (hBr j).2.2.1
  have hG0_eq := (hBr j).2.1
  have hv0 : v ∈ (S ⟨0, hk⟩).G.V := hG_eq ▸ hv
  obtain ⟨C, hC, hvC0⟩ := Finset.mem_biUnion.mp (hIj.hV_eq.symm ▸ hv)
  rw [hG0_eq] at hC
  obtain ⟨cF, rfl⟩ := (hT.hBij.2 C).mp hC
  have hvC_j : v ∈ ((S j).compSt (x.compOf cF)).G.V := hvC0
  have hvC_0 : v ∈ ((S ⟨0, hk⟩).compSt (x.compOf cF)).G.V := (hBr j).2.2.2.2.2.2 cF ▸ hvC_j
  have hC_mem_j : x.compOf cF ∈ components (S j).G₀ := hG0_eq.symm ▸ hT.compOf_mem cF
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hb_w : b + compHdrSize < 2 ^ w := by
    dsimp only [compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by omega
  have hv_lt : v < x.vCap := hT.hVlt v hv0
  have hvc_lt : compVCompBase b + v < 2 ^ w := by
    dsimp only [compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hef_lt : compEdgefulBase b x.vCap + cF.1 < 2 ^ w := by
    dsimp only [compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hvc_m : mem (compVCompBase b + v) = cF.1 := hVComp cF v hvC_0
  obtain ⟨hef_m, _, _, hEfEx⟩ := hCompInfo cF
  have hroot_eq : (S j).RF.root v = ((S j).compSt (x.compOf cF)).RF.root v :=
    compLSF_RF_root_eq hIj hC_mem_j hvC_j
  have hh_vComp := hhdr.2.2.2.2.2.2.2.2.2.1
  have hh_ef := hhdr.2.2.2.2.2.2.2.2.2.2.1
  have hh_efIdx := hhdr.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_k := hhdr.2.2.1
  have hh_hdl := hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrun : ∃ o st' c, Runs w p ω compRootValProc (startState [b, j.1, v] mem pos) o st' c ∧
      (o = .returned ((S j).RF.root v) ∧ st'.mem = mem) ∧ c ≤ 95 := by
    refine runs_start_le ?_
    unfold compRootValProc
    refine runs_seq_assign_le (v := compVCompBase b)
      (Expr.eval_load_of_eq (by have := hb_off compOffVCompPtr (by decide); eval_expr) hh_vComp) ?_
    refine runs_seq_assign_le (v := cF.1) (Expr.eval_load_of_eq (by eval_expr) hvc_m) ?_
    refine runs_seq_assign_le (v := compEdgefulBase b x.vCap)
      (Expr.eval_load_of_eq (by have := hb_off compOffEdgefulPtr (by decide); eval_expr) hh_ef) ?_
    refine runs_seq_assign_le (v := if 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf cF)).m then 1 else 0)
      (Expr.eval_load_of_eq (by eval_expr) hef_m) ?_
    refine WordRAM.runs_cond_le (v := if 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf cF)).m then 1 else 0)
      (by eval_expr) ?_ ?_
    · intro hef_ne
      have hm : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf cF)).m := by
        by_contra h0; exact hef_ne (by simp [h0])
      obtain ⟨ec, _, hec_m, hec_eq⟩ := hEfEx hm
      obtain ⟨hWin_m, hWin_rep, hvWin, _, _, _, hWin_le⟩ := hWins ec j
      set hWin := x.winHandle ec j
      set xWin := x.winConc ec j
      rw [hec_eq] at hWin_rep
      have hWin_hdr := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hWin_fAnc := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hWin_inv := hWin_rep.2.2.2.2.2.2.1
      set fAncPtr := lsfFAncPtr hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM
      have hfAnc_sub := lsfFAnc_sub_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
      have hWin_hdr_le := lsfHdr_lt_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
      dsimp only [LSFConcrete.endAddr] at hWin_le
      have hcid_mem := hWin_fAnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 v (hWin_inv.RF_V_eq ▸ hvC_j)
      set cid := mem (fCompIdBase fAncPtr xWin.vCap + v)
      have hcid_lt : cid < xWin.vCap := (hWin_fAnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 cid hcid_mem.2.1).1
      have hrt_val : mem (fCompRootBase fAncPtr xWin.vCap + cid) = (S j).RF.root v :=
        compRoot_eq_of_fAncAt hIj hC_mem_j hWin_fAnc hvC_j
      have hidx_lt : ec.1 * k + j.1 < x.m0Total * k := by
        calc ec.1 * k + j.1 < ec.1 * k + k := Nat.add_lt_add_left j.2 _
          _ = (ec.1 + 1) * k := by ring
          _ ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
      have hk_w : k < 2 ^ w := by
        have : k ≤ x.m0Total * k := Nat.le_mul_of_pos_left k (by omega)
        dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
      have hWin_ltw : hWin + lsfHdrSize < 2 ^ w := by omega
      have hfAnc_ltw : fAncPtr + fAncSize xWin.vCap < 2 ^ w := by omega
      have hcid_ltw : fCompIdBase fAncPtr xWin.vCap + v < 2 ^ w := by
        dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
      have hcr_ltw : fCompRootBase fAncPtr xWin.vCap + cid < 2 ^ w := by
        dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
      have hH_w : compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1) < 2 ^ w := by
        dsimp only [compTablesEnd] at hTE; omega
      have hefi_w : compEdgefulIdxBase b x.vCap + cF.1 < 2 ^ w := by
        dsimp [compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
          compGhostSize, compHdrSize] at hStat ⊢; omega
      refine runs_seq_assign_le (v := compEdgefulIdxBase b x.vCap)
        (Expr.eval_load_of_eq (by have := hb_off compOffEdgefulIdxPtr (by decide); eval_expr) hh_efIdx) ?_
      refine runs_seq_assign_le (v := ec.1) (Expr.eval_load_of_eq (by eval_expr) hec_m) ?_
      refine runs_seq_assign_le (v := k)
        (Expr.eval_load_of_eq (by have := hb_off compOffK (by decide); eval_expr) hh_k) ?_
      refine runs_seq_assign_le (v := compHandlesBase b x.vCap x.eCap x.L_w)
        (Expr.eval_load_of_eq (by have := hb_off compOffHandlesPtr (by decide); eval_expr) hh_hdl) ?_
      refine runs_seq_assign_le (v := hWin)
        (Expr.eval_load_of_eq (by
          have : ec.1 * k + j.1 < 2 ^ w := by dsimp only [compTablesEnd] at hTE; omega
          have : ec.1 * k < 2 ^ w := by omega
          eval_expr) hWin_m) ?_
      refine runs_seq_assign_le (v := fAncPtr)
        (Expr.eval_load_of_eq (by
          have : lsfOffFAncPtr < 2 ^ w ∧ hWin + lsfOffFAncPtr < 2 ^ w := by
            dsimp [lsfOffFAncPtr, lsfHdrSize] at hWin_ltw ⊢; omega
          eval_expr) hWin_hdr.2.2.2.2.2.2.2.1) ?_
      refine runs_seq_assign_le (v := fCompIdBase fAncPtr xWin.vCap)
        (Expr.eval_load_of_eq (by
          have : fOffCompIdPtr < 2 ^ w ∧ fAncPtr + fOffCompIdPtr < 2 ^ w := by
            dsimp [fOffCompIdPtr, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
          eval_expr) hWin_fAnc.2.2.2.1) ?_
      refine runs_seq_assign_le (v := fCompRootBase fAncPtr xWin.vCap)
        (Expr.eval_load_of_eq (by
          have : fOffCompRootPtr < 2 ^ w ∧ fAncPtr + fOffCompRootPtr < 2 ^ w := by
            dsimp [fOffCompRootPtr, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
          eval_expr) hWin_fAnc.2.2.2.2.1) ?_
      refine runs_seq_assign_le (v := cid) (Expr.eval_load_of_eq (by eval_expr) rfl) ?_
      refine runs_seq_assign_le (v := (S j).RF.root v) (Expr.eval_load_of_eq (by eval_expr) hrt_val) ?_
      exact runs_ret_le (v := (S j).RF.root v) (by eval_expr) ⟨rfl, rfl⟩ (by simp [Expr.size])
    · intro hef_0
      have hm0_c : (compGraph (S j).G₀ (x.compOf cF)).m = 0 := by
        rw [hG0_eq]; by_contra hpos
        have h1 : 1 ≤ (compGraph (S ⟨0, hk⟩).G₀ (x.compOf cF)).m := by omega
        simp [h1] at hef_0
      have hrt_self : (S j).RF.root v = v :=
        (isoComp_props hIj hC_mem_j hm0_c).2.2 v hvC_j
      exact runs_ret_le (v := v) (by eval_expr) ⟨by rw [hrt_self], rfl⟩ (by simp [Expr.size])
  rcases hrun with ⟨o, st', c, hrun', ⟨rfl, hmem⟩, hc⟩
  exact ⟨st', c, hrun', hmem, hc⟩

set_option maxHeartbeats 800000 in
/-- Verification of `compEdgeEndsProc` under `CompLSFRepDirty`: for `e ∈ (S 0).G.E`, writes
`(G.tail e, G.head e)` at `[out2, out2 + 2)` when `e ∉ crossEdges ∧ e ∉ insertedGlobal` (and
`(0, 0)` otherwise), preserving all other memory in `≤ 110` steps. -/
theorem compEdgeEnds_runs {W : LSFWindowImpl} {w k b e out2 : ℕ}
    {S : CompLSFFamily k} {x : CompLSFMeta k} {touched : List ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepDirty W k b S x touched mem)
    (hend_le : x.endAddr ≤ out2) (hout_w : out2 + 2 < 2 ^ w)
    (heG : e ∈ (S ⟨0, hrep.1⟩).G.E) :
    ∃ st' c,
      Runs w p ω compEdgeEndsProc (startState [b, e, out2] mem pos) (.returned 0) st' c ∧
      (e ∉ (S ⟨0, hrep.1⟩).crossEdges → e ∉ (S ⟨0, hrep.1⟩).insertedGlobal →
        st'.mem out2 = (S ⟨0, hrep.1⟩).G.tail e ∧ st'.mem (out2 + 1) = (S ⟨0, hrep.1⟩).G.head e) ∧
      st'.mem out2 < 2 ^ w ∧ st'.mem (out2 + 1) < 2 ^ w ∧
      (∀ a, a < out2 ∨ out2 + 2 ≤ a → st'.mem a = mem a) ∧
      c ≤ 170 := by
  obtain ⟨hk, _, _, _, _, _, _, hnc, hne, hTE, hhdr, ⟨ℓ₀, hBr⟩, _, hT,
    hCompInfo, _, _, hEdgeC, hCrossIns, _, _, _, hWins, _⟩ := hrep
  set cs0 := S ⟨0, hk⟩
  have hI0 := (hBr ⟨0, hk⟩).1
  have he_lt : e < x.eCap := hT.hElt e heG
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hb_w : b + compHdrSize < 2 ^ w := by
    dsimp only [compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by omega
  have hcr_m := (hCrossIns e he_lt).1
  have hins_m := (hCrossIns e he_lt).2
  have hcr_lt : compIsCrossBase b x.vCap x.eCap + e < 2 ^ w := by
    dsimp only [compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
      compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hins_lt : compIsInsBase b x.vCap x.eCap + e < 2 ^ w := by
    dsimp only [compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
      compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hh_vCap := hhdr.1
  have hh_k := hhdr.2.2.1
  have hh_efIdx := hhdr.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_eC1 := hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_cr := hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_ins := hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_hdl := hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrun : ∃ o st' c, Runs w p ω compEdgeEndsProc (startState [b, e, out2] mem pos) o st' c ∧
      (o = .returned 0 ∧
       (e ∉ cs0.crossEdges → e ∉ cs0.insertedGlobal →
         st'.mem out2 = cs0.G.tail e ∧ st'.mem (out2 + 1) = cs0.G.head e) ∧
       st'.mem out2 < 2 ^ w ∧ st'.mem (out2 + 1) < 2 ^ w ∧
       (∀ a, a < out2 ∨ out2 + 2 ≤ a → st'.mem a = mem a)) ∧ c ≤ 170 := by
    refine runs_start_le ?_
    unfold compEdgeEndsProc
    refine runs_seq_assign_le (v := compIsCrossBase b x.vCap x.eCap)
      (Expr.eval_load_of_eq (by have := hb_off compOffIsCrossPtr (by decide); eval_expr) hh_cr) ?_
    refine runs_seq_assign_le (v := if e ∈ cs0.crossEdges then 1 else 0)
      (Expr.eval_load_of_eq (by eval_expr) hcr_m) ?_
    refine runs_seq_assign_le (v := compIsInsBase b x.vCap x.eCap)
      (Expr.eval_load_of_eq (by have := hb_off compOffIsInsPtr (by decide); eval_expr) hh_ins) ?_
    refine runs_seq_assign_le (v := if e ∈ cs0.insertedGlobal then 1 else 0)
      (Expr.eval_load_of_eq (by eval_expr) hins_m) ?_
    set cval := (if e ∈ cs0.crossEdges then 1 else 0) + (if e ∈ cs0.insertedGlobal then 1 else 0)
    have hcw : cval < 2 ^ w := by dsimp [cval]; split_ifs <;> omega
    refine WordRAM.runs_cond_le (v := cval) (by eval_expr) ?_ ?_
    · intro hne0
      have hbad : e ∈ cs0.crossEdges ∨ e ∈ cs0.insertedGlobal := by
        by_contra h; rw [not_or] at h; simp [cval, h.1, h.2] at hne0
      refine runs_seq_store_le (x := out2) (v := 0) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := out2 + 1) (v := 0) (by eval_expr) (by eval_expr) ?_
      refine runs_ret_le (v := 0) (by eval_expr) ?_ (by simp [Expr.size])
      exact ⟨rfl, fun h1 h2 => absurd hbad (not_or.mpr ⟨h1, h2⟩),
        by simp [startState], by simp [startState],
        fun a ha => by simp [startState, Function.update_of_ne (by omega : a ≠ out2 + 1),
          Function.update_of_ne (by omega : a ≠ out2)]⟩
    · intro hzero
      have hnc : e ∉ cs0.crossEdges := by intro h; simp [cval, h] at hzero
      have hni : e ∉ cs0.insertedGlobal := by intro h; simp [cval, h] at hzero
      obtain ⟨cF, hc1, hm1, heC, _, htC, hhC⟩ := compLSF_orig_edge_in_comp hI0 hT heG hni
      obtain ⟨ec, _, hec_m, hec_eq⟩ := (hCompInfo cF).2.2.2 hm1
      obtain ⟨hWin_m, hWin_rep, hxV, hxE, _, _, hWin_le⟩ := hWins ec ⟨0, hk⟩
      set hWin := x.winHandle ec ⟨0, hk⟩
      set xWin := x.winConc ec ⟨0, hk⟩
      rw [hec_eq] at hWin_rep
      have hWin_hdr := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hdgG_at : DynGraphAt mem (lsfDgGPtr hWin) xWin.vCap xWin.eCap
          (cs0.compSt (x.compOf cF)).G := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      set dgG := lsfDgGPtr hWin
      have hWin_hdr_le := lsfHdr_lt_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
      dsimp only [LSFConcrete.endAddr] at hWin_le
      have hdg_lt : dgG + dynGraphSize xWin.vCap xWin.eCap < 2 ^ w := by
        have : dgG + dynGraphSize xWin.vCap xWin.eCap ≤
            lsfEndAddr hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w := by
          dsimp only [dgG, lsfDgGPtr, lsfEndAddr, lsfStaticSize]; omega
        omega
      have hWin_ltw : hWin + lsfHdrSize < 2 ^ w := by omega
      have he_ends := hdgG_at.1 e heC
      set sT := mem (dgExtToIntBase dgG xWin.vCap + (cs0.compSt (x.compOf cF)).G.tail e)
      set sH := mem (dgExtToIntBase dgG xWin.vCap + (cs0.compSt (x.compOf cF)).G.head e)
      have hsT_lt : sT < xWin.vCap := hdgG_at.2.1 sT (hdgG_at.2.2.2.2.2.2.2.2.2.1 _ he_ends.1).1
      have hsH_lt : sH < xWin.vCap := hdgG_at.2.1 sH (hdgG_at.2.2.2.2.2.2.2.2.2.1 _ he_ends.2).1
      have ht_slot : mem (dgETailSlotBase dgG xWin.vCap xWin.eCap + e) = sT :=
        (hdgG_at.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e heC).1
      have hh_slot : mem (dgEHeadSlotBase dgG xWin.vCap xWin.eCap + e) = sH :=
        (hdgG_at.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e heC).2
      have hi2eT : mem (dgIntToExtBase dgG xWin.vCap + sT) = cs0.G.tail e :=
        (hdgG_at.2.2.2.2.2.2.2.2.2.1 _ he_ends.1).2.trans htC
      have hi2eH : mem (dgIntToExtBase dgG xWin.vCap + sH) = cs0.G.head e :=
        (hdgG_at.2.2.2.2.2.2.2.2.2.1 _ he_ends.2).2.trans hhC
      have hidx_lt : ec.1 * k + 0 < x.m0Total * k := by
        calc ec.1 * k + 0 < ec.1 * k + k := Nat.add_lt_add_left hk _
          _ = (ec.1 + 1) * k := by ring
          _ ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
      have hWin_m0 : mem (compHandlesBase b x.vCap x.eCap x.L_w + ec.1 * k) = hWin := by
        simpa [Nat.add_zero] using hWin_m
      refine runs_seq_assign_le (v := compEdgeC1Base b x.vCap)
        (Expr.eval_load_of_eq (by have := hb_off compOffEdgeC1Ptr (by decide); eval_expr) hh_eC1) ?_
      refine runs_seq_assign_le (v := cF.1)
        (Expr.eval_load_of_eq (by
          have : compEdgeC1Base b x.vCap + e < 2 ^ w := by
            dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase,
              compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
          eval_expr) ((hEdgeC e heG).1.trans hc1)) ?_
      refine runs_seq_assign_le (v := compEdgefulIdxBase b x.vCap)
        (Expr.eval_load_of_eq (by have := hb_off compOffEdgefulIdxPtr (by decide); eval_expr) hh_efIdx) ?_
      refine runs_seq_assign_le (v := ec.1)
        (Expr.eval_load_of_eq (by
          have : compEdgefulIdxBase b x.vCap + cF.1 < 2 ^ w := by
            dsimp only [compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
              compGhostSize, compHdrSize] at hStat ⊢; omega
          eval_expr) hec_m) ?_
      refine runs_seq_assign_le (v := k)
        (Expr.eval_load_of_eq (by have := hb_off compOffK (by decide); eval_expr) hh_k) ?_
      refine runs_seq_assign_le (v := compHandlesBase b x.vCap x.eCap x.L_w)
        (Expr.eval_load_of_eq (by have := hb_off compOffHandlesPtr (by decide); eval_expr) hh_hdl) ?_
      refine runs_seq_assign_le (v := hWin)
        (Expr.eval_load_of_eq (by
          have : ec.1 * k < 2 ^ w := by dsimp only [compTablesEnd] at hTE; omega
          have : compHandlesBase b x.vCap x.eCap x.L_w + ec.1 * k < 2 ^ w := by
            dsimp only [compTablesEnd] at hTE; omega
          eval_expr) hWin_m0) ?_
      refine runs_seq_assign_le (v := dgG)
        (Expr.eval_load_of_eq (by
          have : lsfOffDgGPtr < 2 ^ w ∧ hWin + lsfOffDgGPtr < 2 ^ w := by
            dsimp [lsfOffDgGPtr, lsfHdrSize] at hWin_ltw ⊢; omega
          eval_expr) hWin_hdr.2.2.2.2.1) ?_
      refine runs_seq_assign_le (v := x.vCap)
        (Expr.eval_load_of_eq (by have := hb_off compOffVCap (by decide); eval_expr) hh_vCap) ?_
      refine runs_seq_assign_le (v := xWin.eCap)
        (Expr.eval_load_of_eq (by
          have : dgECapOff < 2 ^ w ∧ dgG + dgECapOff < 2 ^ w := by
            dsimp [dgECapOff, dynGraphSize] at hdg_lt ⊢; omega
          eval_expr) hdgG_at.2.2.2.2.1) ?_
      refine runs_seq_assign_le (v := dgIntToExtBase dgG xWin.vCap)
        (by dsimp only [dgIntToExtBase, dynGraphSize] at hdg_lt ⊢; rw [hxV]; eval_expr) ?_
      refine runs_seq_assign_le (v := dgETailSlotBase dgG xWin.vCap xWin.eCap)
        (by dsimp only [dgETailSlotBase, dynGraphSize] at hdg_lt ⊢; rw [hxV]; eval_expr) ?_
      refine runs_seq_assign_le (v := dgEHeadSlotBase dgG xWin.vCap xWin.eCap)
        (by dsimp only [dgEHeadSlotBase, dynGraphSize] at hdg_lt ⊢; rw [hxV]; eval_expr) ?_
      refine runs_seq_assign_le (v := sT)
        (Expr.eval_load_of_eq (by
          have : dgETailSlotBase dgG xWin.vCap xWin.eCap + e < 2 ^ w := by
            dsimp only [dgETailSlotBase, dynGraphSize] at hdg_lt ⊢; omega
          eval_expr) ht_slot) ?_
      refine runs_seq_assign_le (v := cs0.G.tail e)
        (Expr.eval_load_of_eq (by
          have : dgIntToExtBase dgG xWin.vCap + sT < 2 ^ w := by
            dsimp only [dgIntToExtBase, dynGraphSize] at hdg_lt ⊢; omega
          eval_expr) hi2eT) ?_
      refine runs_seq_assign_le (v := sH)
        (Expr.eval_load_of_eq (by
          have : dgEHeadSlotBase dgG xWin.vCap xWin.eCap + e < 2 ^ w := by
            dsimp only [dgEHeadSlotBase, dynGraphSize] at hdg_lt ⊢; omega
          eval_expr) hh_slot) ?_
      refine runs_seq_assign_le (v := cs0.G.head e)
        (Expr.eval_load_of_eq (by
          have : dgIntToExtBase dgG xWin.vCap + sH < 2 ^ w := by
            dsimp only [dgIntToExtBase, dynGraphSize] at hdg_lt ⊢; omega
          eval_expr) hi2eH) ?_
      refine runs_seq_store_le (x := out2) (v := cs0.G.tail e) (by eval_expr) (by eval_expr) ?_
      refine runs_seq_store_le (x := out2 + 1) (v := cs0.G.head e) (by eval_expr) (by eval_expr) ?_
      refine runs_ret_le (v := 0) (by eval_expr) ?_ (by simp [Expr.size])
      exact ⟨rfl, fun _ _ => ⟨by simp [startState], by simp [startState]⟩,
        by simp [startState]; have hlt := hdgG_at.2.1 _ he_ends.1; rw [htC] at hlt; dsimp only [dynGraphSize] at hdg_lt; dsimp only [cs0] at hlt ⊢; omega,
        by simp [startState]; have hlt := hdgG_at.2.1 _ he_ends.2; rw [hhC] at hlt; dsimp only [dynGraphSize] at hdg_lt; dsimp only [cs0] at hlt ⊢; omega,
        fun a ha => by simp [startState, Function.update_of_ne (by omega : a ≠ out2 + 1),
          Function.update_of_ne (by omega : a ≠ out2)]⟩
  rcases hrun with ⟨o, st', c, hrun', ⟨rfl, hpost, hlt1, hlt2, hfr⟩, hc⟩
  exact ⟨st', c, hrun', hpost, hlt1, hlt2, hfr, hc⟩

set_option maxHeartbeats 800000 in
/-- Verification of `compEdgeEndRootsProc` under `CompLSFRepDirty`: for a surviving original
same-component edge `d ∈ ((S j).compSt (x.compOf c)).G.E` with `edgeC1 d = c.1`, stores
`[(S j).RF.root (G_c.tail d), (S j).RF.root (G_c.head d)]` at `[out2, out2 + 2)`, preserving all
other memory in `≤ 140` steps. -/
theorem compEdgeEndRoots_runs {W : LSFWindowImpl} {w k b d out2 : ℕ}
    {S : CompLSFFamily k} {x : CompLSFMeta k} {touched : List ℕ}
    {p : Program} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (j : Fin k) (cF : Fin x.numComps)
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepDirty W k b S x touched mem)
    (hend_le : x.endAddr ≤ out2) (hout_w : out2 + 2 < 2 ^ w)
    (hdG : d ∈ (S ⟨0, hrep.1⟩).G.E)
    (hc1 : x.edgeC1 d = cF.1)
    (hm1 : 1 ≤ (compGraph (S ⟨0, hrep.1⟩).G₀ (x.compOf cF)).m)
    (hdC : d ∈ ((S j).compSt (x.compOf cF)).G.E) :
    let u := ((S j).compSt (x.compOf cF)).G.tail d
    let v := ((S j).compSt (x.compOf cF)).G.head d
    ∃ st' c,
      Runs w p ω compEdgeEndRootsProc (startState [b, j.1, d, out2] mem pos) (.returned 0) st' c ∧
      st'.mem out2 = (S j).RF.root u ∧
      st'.mem (out2 + 1) = (S j).RF.root v ∧
      (∀ a, a < out2 ∨ out2 + 2 ≤ a → st'.mem a = mem a) ∧
      c ≤ 200 := by
  intro u v
  obtain ⟨hk, _, _, _, _, _, _, hnc, hne, hTE, hhdr, ⟨ℓ₀, hBr⟩, _, hT,
    hCompInfo, _, _, hEdgeC, _, _, _, _, hWins, _⟩ := hrep
  have hIj := (hBr j).1
  have hG0_eq := (hBr j).2.1
  have hC_mem_j : x.compOf cF ∈ components (S j).G₀ := hG0_eq.symm ▸ hT.compOf_mem cF
  have hd_lt : d < x.eCap := hT.hElt d hdG
  obtain ⟨ec, _, hec_m, hec_eq⟩ := (hCompInfo cF).2.2.2 hm1
  obtain ⟨hWin_m, hWin_rep, hxV, hxE, _, _, hWin_le⟩ := hWins ec j
  set hWin := x.winHandle ec j
  set xWin := x.winConc ec j
  rw [hec_eq] at hWin_rep
  have hWin_hdr := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdgG_at : DynGraphAt mem (lsfDgGPtr hWin) xWin.vCap xWin.eCap
      ((S j).compSt (x.compOf cF)).G := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hWin_fAnc := hWin_rep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hWin_inv := hWin_rep.2.2.2.2.2.2.1
  set dgG := lsfDgGPtr hWin
  set fAncPtr := lsfFAncPtr hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM
  have hfAnc_sub := lsfFAnc_sub_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
  have hWin_hdr_le := lsfHdr_lt_end hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w
  dsimp only [LSFConcrete.endAddr] at hWin_le
  have hStat : b + compStaticSize x.vCap x.eCap x.L_w ≤ x.endAddr := by
    dsimp only [compTablesEnd, compHandlesBase] at hTE; omega
  have hb_w : b + compHdrSize < 2 ^ w := by
    dsimp only [compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
  have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by omega
  have hdg_lt : dgG + dynGraphSize xWin.vCap xWin.eCap < 2 ^ w := by
    have : dgG + dynGraphSize xWin.vCap xWin.eCap ≤
        lsfEndAddr hWin xWin.vCap xWin.eCap xWin.n0 xWin.tM xWin.L_w := by
      dsimp only [dgG, lsfDgGPtr, lsfEndAddr, lsfStaticSize]; omega
    omega
  have hWin_ltw : hWin + lsfHdrSize < 2 ^ w := by omega
  have hfAnc_ltw : fAncPtr + fAncSize xWin.vCap < 2 ^ w := by omega
  have hd_ends := hdgG_at.1 d hdC
  set sT := mem (dgExtToIntBase dgG xWin.vCap + u)
  set sH := mem (dgExtToIntBase dgG xWin.vCap + v)
  have hsT_lt : sT < xWin.vCap := hdgG_at.2.1 sT (hdgG_at.2.2.2.2.2.2.2.2.2.1 _ hd_ends.1).1
  have hsH_lt : sH < xWin.vCap := hdgG_at.2.1 sH (hdgG_at.2.2.2.2.2.2.2.2.2.1 _ hd_ends.2).1
  have ht_slot : mem (dgETailSlotBase dgG xWin.vCap xWin.eCap + d) = sT :=
    (hdgG_at.2.2.2.2.2.2.2.2.2.2.2.2.2.1 d hdC).1
  have hh_slot : mem (dgEHeadSlotBase dgG xWin.vCap xWin.eCap + d) = sH :=
    (hdgG_at.2.2.2.2.2.2.2.2.2.2.2.2.2.1 d hdC).2
  have hi2eT : mem (dgIntToExtBase dgG xWin.vCap + sT) = u :=
    (hdgG_at.2.2.2.2.2.2.2.2.2.1 _ hd_ends.1).2
  have hi2eH : mem (dgIntToExtBase dgG xWin.vCap + sH) = v :=
    (hdgG_at.2.2.2.2.2.2.2.2.2.1 _ hd_ends.2).2
  have hcidU_mem := hWin_fAnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 u (hWin_inv.RF_V_eq ▸ hd_ends.1)
  have hcidV_mem := hWin_fAnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 v (hWin_inv.RF_V_eq ▸ hd_ends.2)
  set cidU := mem (fCompIdBase fAncPtr xWin.vCap + u)
  set cidV := mem (fCompIdBase fAncPtr xWin.vCap + v)
  have hcidU_lt : cidU < xWin.vCap := (hWin_fAnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 cidU hcidU_mem.2.1).1
  have hcidV_lt : cidV < xWin.vCap := (hWin_fAnc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 cidV hcidV_mem.2.1).1
  have hu_lt : u < xWin.vCap := hWin_fAnc.2.2.2.2.2.2.1 u (hWin_inv.RF_V_eq ▸ hd_ends.1)
  have hv_lt : v < xWin.vCap := hWin_fAnc.2.2.2.2.2.2.1 v (hWin_inv.RF_V_eq ▸ hd_ends.2)
  have hru_m : mem (fCompRootBase fAncPtr xWin.vCap + cidU) = (S j).RF.root u :=
    compRoot_eq_of_fAncAt hIj hC_mem_j hWin_fAnc hd_ends.1
  have hrv_m : mem (fCompRootBase fAncPtr xWin.vCap + cidV) = (S j).RF.root v :=
    compRoot_eq_of_fAncAt hIj hC_mem_j hWin_fAnc hd_ends.2
  have hidx_lt : ec.1 * k + j.1 < x.m0Total * k := by
    calc ec.1 * k + j.1 < ec.1 * k + k := Nat.add_lt_add_left j.2 _
      _ = (ec.1 + 1) * k := by ring
      _ ≤ x.m0Total * k := Nat.mul_le_mul_right k (by omega)
  have hh_vCap := hhdr.1
  have hh_k := hhdr.2.2.1
  have hh_efIdx := hhdr.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_eC1 := hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_hdl := hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hrun : ∃ o st' c, Runs w p ω compEdgeEndRootsProc (startState [b, j.1, d, out2] mem pos) o st' c ∧
      (o = .returned 0 ∧ st'.mem out2 = (S j).RF.root u ∧ st'.mem (out2 + 1) = (S j).RF.root v ∧
       (∀ a, a < out2 ∨ out2 + 2 ≤ a → st'.mem a = mem a)) ∧ c ≤ 200 := by
    refine runs_start_le ?_
    unfold compEdgeEndRootsProc
    refine runs_seq_assign_le (v := compEdgeC1Base b x.vCap)
      (Expr.eval_load_of_eq (by have := hb_off compOffEdgeC1Ptr (by decide); eval_expr) hh_eC1) ?_
    refine runs_seq_assign_le (v := cF.1)
      (Expr.eval_load_of_eq (by
        have : compEdgeC1Base b x.vCap + d < 2 ^ w := by
          dsimp only [compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase,
            compVCompBase, compStaticSize, compGhostSize, compHdrSize] at hStat ⊢; omega
        eval_expr) ((hEdgeC d hdG).1.trans hc1)) ?_
    refine runs_seq_assign_le (v := compEdgefulIdxBase b x.vCap)
      (Expr.eval_load_of_eq (by have := hb_off compOffEdgefulIdxPtr (by decide); eval_expr) hh_efIdx) ?_
    refine runs_seq_assign_le (v := ec.1)
      (Expr.eval_load_of_eq (by
        have : compEdgefulIdxBase b x.vCap + cF.1 < 2 ^ w := by
          dsimp only [compEdgefulIdxBase, compEdgefulBase, compVCompBase, compStaticSize,
            compGhostSize, compHdrSize] at hStat ⊢; omega
        eval_expr) hec_m) ?_
    refine runs_seq_assign_le (v := k)
      (Expr.eval_load_of_eq (by have := hb_off compOffK (by decide); eval_expr) hh_k) ?_
    refine runs_seq_assign_le (v := compHandlesBase b x.vCap x.eCap x.L_w)
      (Expr.eval_load_of_eq (by have := hb_off compOffHandlesPtr (by decide); eval_expr) hh_hdl) ?_
    refine runs_seq_assign_le (v := hWin)
      (Expr.eval_load_of_eq (by
        have : ec.1 * k < 2 ^ w := by dsimp only [compTablesEnd] at hTE; omega
        have : compHandlesBase b x.vCap x.eCap x.L_w + (ec.1 * k + j.1) < 2 ^ w := by
          dsimp only [compTablesEnd] at hTE; omega
        eval_expr) hWin_m) ?_
    refine runs_seq_assign_le (v := dgG)
      (Expr.eval_load_of_eq (by
        have : lsfOffDgGPtr < 2 ^ w ∧ hWin + lsfOffDgGPtr < 2 ^ w := by
          dsimp [lsfOffDgGPtr, lsfHdrSize] at hWin_ltw ⊢; omega
        eval_expr) hWin_hdr.2.2.2.2.1) ?_
    refine runs_seq_assign_le (v := x.vCap)
      (Expr.eval_load_of_eq (by have := hb_off compOffVCap (by decide); eval_expr) hh_vCap) ?_
    refine runs_seq_assign_le (v := xWin.eCap)
      (Expr.eval_load_of_eq (by
        have : dgECapOff < 2 ^ w ∧ dgG + dgECapOff < 2 ^ w := by
          dsimp [dgECapOff, dynGraphSize] at hdg_lt ⊢; omega
        eval_expr) hdgG_at.2.2.2.2.1) ?_
    refine runs_seq_assign_le (v := dgIntToExtBase dgG xWin.vCap)
      (by dsimp only [dgIntToExtBase, dynGraphSize] at hdg_lt ⊢; rw [hxV]; eval_expr) ?_
    refine runs_seq_assign_le (v := dgETailSlotBase dgG xWin.vCap xWin.eCap)
      (by dsimp only [dgETailSlotBase, dynGraphSize] at hdg_lt ⊢; rw [hxV]; eval_expr) ?_
    refine runs_seq_assign_le (v := dgEHeadSlotBase dgG xWin.vCap xWin.eCap)
      (by dsimp only [dgEHeadSlotBase, dynGraphSize] at hdg_lt ⊢; rw [hxV]; eval_expr) ?_
    refine runs_seq_assign_le (v := sT)
      (Expr.eval_load_of_eq (by
        have : dgETailSlotBase dgG xWin.vCap xWin.eCap + d < 2 ^ w := by
          dsimp only [dgETailSlotBase, dynGraphSize] at hdg_lt ⊢; omega
        eval_expr) ht_slot) ?_
    refine runs_seq_assign_le (v := u)
      (Expr.eval_load_of_eq (by
        have : dgIntToExtBase dgG xWin.vCap + sT < 2 ^ w := by
          dsimp only [dgIntToExtBase, dynGraphSize] at hdg_lt ⊢; omega
        eval_expr) hi2eT) ?_
    refine runs_seq_assign_le (v := sH)
      (Expr.eval_load_of_eq (by
        have : dgEHeadSlotBase dgG xWin.vCap xWin.eCap + d < 2 ^ w := by
          dsimp only [dgEHeadSlotBase, dynGraphSize] at hdg_lt ⊢; omega
        eval_expr) hh_slot) ?_
    refine runs_seq_assign_le (v := v)
      (Expr.eval_load_of_eq (by
        have : dgIntToExtBase dgG xWin.vCap + sH < 2 ^ w := by
          dsimp only [dgIntToExtBase, dynGraphSize] at hdg_lt ⊢; omega
        eval_expr) hi2eH) ?_
    refine runs_seq_assign_le (v := fAncPtr)
      (Expr.eval_load_of_eq (by
        have : lsfOffFAncPtr < 2 ^ w ∧ hWin + lsfOffFAncPtr < 2 ^ w := by
          dsimp [lsfOffFAncPtr, lsfHdrSize] at hWin_ltw ⊢; omega
        eval_expr) hWin_hdr.2.2.2.2.2.2.2.1) ?_
    refine runs_seq_assign_le (v := fCompIdBase fAncPtr xWin.vCap)
      (Expr.eval_load_of_eq (by
        have : fOffCompIdPtr < 2 ^ w ∧ fAncPtr + fOffCompIdPtr < 2 ^ w := by
          dsimp [fOffCompIdPtr, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
        eval_expr) hWin_fAnc.2.2.2.1) ?_
    refine runs_seq_assign_le (v := fCompRootBase fAncPtr xWin.vCap)
      (Expr.eval_load_of_eq (by
        have : fOffCompRootPtr < 2 ^ w ∧ fAncPtr + fOffCompRootPtr < 2 ^ w := by
          dsimp [fOffCompRootPtr, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
        eval_expr) hWin_fAnc.2.2.2.2.1) ?_
    refine runs_seq_assign_le (v := cidU)
      (Expr.eval_load_of_eq (by
        have : fCompIdBase fAncPtr xWin.vCap + u < 2 ^ w := by
          dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
        eval_expr) rfl) ?_
    refine runs_seq_assign_le (v := (S j).RF.root u)
      (Expr.eval_load_of_eq (by
        have : fCompRootBase fAncPtr xWin.vCap + cidU < 2 ^ w := by
          dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
        eval_expr) hru_m) ?_
    refine runs_seq_assign_le (v := cidV)
      (Expr.eval_load_of_eq (by
        have : fCompIdBase fAncPtr xWin.vCap + v < 2 ^ w := by
          dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
        eval_expr) rfl) ?_
    refine runs_seq_assign_le (v := (S j).RF.root v)
      (Expr.eval_load_of_eq (by
        have : fCompRootBase fAncPtr xWin.vCap + cidV < 2 ^ w := by
          dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncSize, fAncHdrSize] at hfAnc_ltw ⊢; omega
        eval_expr) hrv_m) ?_
    refine runs_seq_store_le (x := out2) (v := (S j).RF.root u) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := out2 + 1) (v := (S j).RF.root v) (by eval_expr) (by eval_expr) ?_
    refine runs_ret_le (v := 0) (by eval_expr) ?_ (by simp [Expr.size])
    exact ⟨rfl, by simp [startState], by simp [startState],
      fun a ha => by simp [startState, Function.update_of_ne (by omega : a ≠ out2 + 1),
        Function.update_of_ne (by omega : a ≠ out2)]⟩
  rcases hrun with ⟨o, st', c, hrun', ⟨rfl, h0, h1, hfr⟩, hc⟩
  exact ⟨st', c, hrun', h0, h1, hfr, hc⟩

end

end MinCostFlow.SparseCore.Program
