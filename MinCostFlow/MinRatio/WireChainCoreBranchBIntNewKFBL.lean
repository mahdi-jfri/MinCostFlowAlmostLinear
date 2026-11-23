module

public import MinCostFlow.MinRatio.WireShiftDeepCollectKFBL
import WordRAM.Tactic

/-!
# The new forests of the interior step after the Branch B loop (`WireChainCoreBranchBIntNewKFBL`)

After the suffix rebuild, the tree sync of the interior step needs the new active forests of the
rebuilt levels `i₀, …, d`. The chain-update core keeps one pointer array `newPtrs` (`reg 81`)
indexed by level (`reg 71 = 0`), so the forest of level `j` goes to `newPtrs + j`. The collection
`wireBranchBIntNewStmt` starts the loop of `collectLSFForestsLoop` at the level `reg 96 = i₀` and
then stores the forest of the new last level (`collectTermForestStmt`).

`wireBranchBIntNewKFBL_runs` is `shiftDeepCollectNewKFBL_runs` (`WireShiftDeepCollectKFBL.lean`)
with the start level `i₀` apart from the base index `0`. It gives the list of the new forests at
`newPtrs + i₀` (`ForestPtrListAt`), keeps the cores of the levels `j ≥ i₀`, and changes no word
below the heap pointer outside their footprints and the cells `newPtrs + i₀, …, newPtrs + d`.
Each forest lies in the footprint of its core or of the new last level, so every pointer is at
least any bound `lo` below those footprints.

`ForestPtrListAt.congr_from` moves such a list to a later memory that keeps the pointer cells and
the words from `lo` on. The last part of the interior step uses it.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

/-- Collect the new forests of the levels from `reg 96` on into `newPtrs = reg 81`, indexed by
level (`reg 71 = 0`). -/
@[expose] def wireBranchBIntNewStmt (readLSF : ℕ) : Stmt :=
  .assign 20 (.reg 96) ;; collectLSFForestsLoop readLSF 81 ;; collectTermForestStmt 81

theorem wireBranchBIntNewStmt_noRand (readLSF : ℕ) : (wireBranchBIntNewStmt readLSF).NoRand := by
  simp [wireBranchBIntNewStmt, collectLSFForestsLoop_noRand, collectTermForestStmt_noRand,
    Stmt.NoRand]

/-- A forest list whose pointers are at least `lo` moves to a memory that agrees with the old one
on the pointer cells and on `[lo, bound)`, and to any larger bound. -/
theorem ForestPtrListAt.congr_from {mem mem' : ℕ → ℕ} {ptrBase intCap bound bound' lo : ℕ}
    {Fs : List MGraph} (h : ForestPtrListAt mem ptrBase Fs intCap bound)
    (hlo : ∀ t < Fs.length, lo ≤ mem (ptrBase + t))
    (hPtr : ∀ t < Fs.length, mem' (ptrBase + t) = mem (ptrBase + t))
    (hBlk : ∀ a, lo ≤ a → a < bound → mem' a = mem a) (hb : bound ≤ bound') :
    ForestPtrListAt mem' ptrBase Fs intCap bound' := by
  refine ⟨h.1.trans hb, fun t ht => ?_⟩
  obtain ⟨vc, ec, hG, hEnd, hCap⟩ := h.2 t ht
  have hp := hPtr t ht
  have hl := hlo t ht
  refine ⟨vc, ec, ?_, by rw [hp]; omega, hCap⟩
  rw [hp]
  exact dynGraphAt_of_agree hG (fun x h1 h2 => hBlk x (by omega) (by omega))

/-- **The new-forest collection of the interior step.** The program `wireBranchBIntNewStmt`
collects the active forests of `next` on `[i0, d]` into `newPtrs + i0, …, newPtrs + d`. It gives
`ForestPtrListAt out.mem (newPtrs + i0) (chainSuffixForests next i0) intCap (out.regs 4)`, keeps the
cores on `[i0, d)` and telescopes their potentials. -/
theorem wireBranchBIntNewKFBL_runs
    {w L depth vCap eCap capExp i0 handleBase branchBase levelMeta newPtrs intCap termHandle
      vcLast ecLast lsfHdr forestPtr lo : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {CP : ChainParams}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {p : Program} {op : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool}
    (next : ChainState T CP) (coreHandle : ℕ → ℕ) (coreTok0 : ℕ → Rcore.τ)
    (hCoreLocal : Rcore.Local)
    (hiLt : i0 < CP.d)
    (h96 : st.regs 96 = i0) (h71 : st.regs 71 = 0) (h75 : st.regs 75 = CP.d)
    (h77 : st.regs 77 = handleBase) (h78 : st.regs 78 = branchBase)
    (h81 : st.regs 81 = newPtrs) (h83 : st.regs 83 = levelMeta)
    (hkW : CP.k < 2 ^ w) (hdW : CP.d < 2 ^ w) (hw1 : 1 < 2 ^ w)
    (hMetaEnd : levelMeta + 2 * CP.d ≤ st.regs 4) (hHEnd : handleBase + CP.d + 1 ≤ st.regs 4)
    (hBEnd : branchBase + CP.d + 1 ≤ st.regs 4)
    (hNewEnd : newPtrs + (CP.d + 1) ≤ st.regs 4)
    (hRoom : st.regs 4 + 5 * (CP.d - i0) < 2 ^ w)
    (hz0 : ZeroFrom st.mem (st.regs 4))
    (hFootAt : ∀ j, i0 ≤ j → j < CP.d →
      SparseCoreReadoutFootAt fmt L depth T (next.G j) CP.k (next.lvlM j) next.N₀ vCap eCap
        capExp P allocation Rcore p op)
    (hCores : ∀ j, i0 ≤ j → j < CP.d →
      st.mem (handleBase + j) = coreHandle j ∧
      st.mem (branchBase + j) = next.bran j ∧
      next.bran j < CP.k ∧ coreHandle j < 2 ^ w ∧
      Rcore.rep (coreHandle j) (chainLevelOrdAbs next j) (coreTok0 j) st.mem ∧
      SparseCoreOrdInput T CP.k (next.lvlM j) next.N₀ (next.scState j) (next.G j)
        (next.levelOrd j) (next.updCount j) ∧
      (∀ a, Rcore.foot (coreHandle j) (coreTok0 j) a → a < st.regs 4) ∧
      (∀ r, i0 ≤ r → r < CP.d →
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (handleBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (branchBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (levelMeta + CP.d + j)) ∧
      (handleBase + j < newPtrs + i0 ∨ newPtrs + (CP.d + 1) ≤ handleBase + j) ∧
      (branchBase + j < newPtrs + i0 ∨ newPtrs + (CP.d + 1) ≤ branchBase + j) ∧
      (levelMeta + CP.d + j < newPtrs + i0 ∨ newPtrs + (CP.d + 1) ≤ levelMeta + CP.d + j) ∧
      (∀ t, i0 ≤ t → t < CP.d + 1 → ¬ Rcore.foot (coreHandle j) (coreTok0 j) (newPtrs + t)) ∧
      (DynGraphAt st.mem (st.mem (levelMeta + CP.d + j)) vCap eCap (next.G j) ∧
        st.mem (levelMeta + CP.d + j) + dynGraphSize vCap eCap ≤ st.regs 4 ∧
        (∀ a, st.mem (levelMeta + CP.d + j) ≤ a →
          a < st.mem (levelMeta + CP.d + j) + dynGraphSize vCap eCap →
          (∀ r, i0 ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a) ∧
          (a < newPtrs + i0 ∨ newPtrs + (CP.d + 1) ≤ a))))
    (hCoreDisj : ∀ j₁ j₂, i0 ≤ j₁ → j₁ < CP.d → i0 ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
      ∀ a, Rcore.foot (coreHandle j₁) (coreTok0 j₁) a →
        ¬ Rcore.foot (coreHandle j₂) (coreTok0 j₂) a)
    (hTermH : st.mem (handleBase + CP.d) = termHandle)
    (hTermB : st.mem (branchBase + CP.d) = next.lastBran)
    (hTermLsf : st.mem (termHandle + 1 + next.lastBran) = lsfHdr)
    (hTermFPtr : st.mem (lsfHdr + 1) = forestPtr)
    (hTermFDG : DynGraphAt st.mem forestPtr vcLast ecLast (next.lastLSFs next.lastBran).F.F)
    (hTermFEnd : forestPtr + dynGraphSize vcLast ecLast ≤ st.regs 4)
    (hTermFCap : ∀ e ∈ (next.lastLSFs next.lastBran).F.F.E, e < intCap)
    (hTermDisjCells :
      (handleBase + CP.d < newPtrs + i0 ∨ newPtrs + (CP.d + 1) ≤ handleBase + CP.d) ∧
      (branchBase + CP.d < newPtrs + i0 ∨ newPtrs + (CP.d + 1) ≤ branchBase + CP.d) ∧
      (termHandle + 1 + next.lastBran < newPtrs + i0 ∨
        newPtrs + (CP.d + 1) ≤ termHandle + 1 + next.lastBran) ∧
      (lsfHdr + 1 < newPtrs + i0 ∨ newPtrs + (CP.d + 1) ≤ lsfHdr + 1) ∧
      termHandle + 1 + next.lastBran < st.regs 4 ∧ lsfHdr + 1 < st.regs 4 ∧
      (∀ r, i0 ≤ r → r < CP.d →
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (handleBase + CP.d) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (branchBase + CP.d) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (termHandle + 1 + next.lastBran) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (lsfHdr + 1)) ∧
      (∀ a, forestPtr ≤ a → a < forestPtr + dynGraphSize vcLast ecLast →
        (∀ r, i0 ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a) ∧
        (a < newPtrs + i0 ∨ newPtrs + (CP.d + 1) ≤ a)))
    (hIntCap : ∀ j, i0 ≤ j → j < CP.d →
      ∀ e ∈ (T.lsfs (next.scState j) (next.bran j)).F.F.E, e < intCap)
    (hLoFoot : ∀ j, i0 ≤ j → j < CP.d → ∀ a, Rcore.foot (coreHandle j) (coreTok0 j) a → lo ≤ a)
    (hLoSt : lo ≤ st.regs 4) (hLoTerm : lo ≤ forestPtr) :
    ∃ (out : State) (c : ℕ) (coreTok' : ℕ → Rcore.τ),
      Runs w p ω (wireBranchBIntNewStmt (op 2)) st .normal out c ∧
      st.regs 4 ≤ out.regs 4 ∧ out.regs 4 ≤ st.regs 4 + 5 * (CP.d - i0) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      ForestPtrListAt out.mem (newPtrs + i0) (chainSuffixForests next i0) intCap (out.regs 4) ∧
      (∀ t < (chainSuffixForests next i0).length, lo ≤ out.mem (newPtrs + i0 + t)) ∧
      (∀ j, i0 ≤ j → j < CP.d →
        Rcore.rep (coreHandle j) (chainLevelOrdAbs next j) (coreTok' j) out.mem ∧
        (∀ a, Rcore.foot (coreHandle j) (coreTok' j) a →
          Rcore.foot (coreHandle j) (coreTok0 j) a ∨ (st.regs 4 ≤ a ∧ a < out.regs 4))) ∧
      (∀ j₁ j₂, i0 ≤ j₁ → j₁ < CP.d → i0 ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
        ∀ a, Rcore.foot (coreHandle j₁) (coreTok' j₁) a →
          ¬ Rcore.foot (coreHandle j₂) (coreTok' j₂) a) ∧
      (∀ a < st.regs 4,
        (∀ j, i0 ≤ j → j < CP.d → ¬ Rcore.foot (coreHandle j) (coreTok0 j) a) →
        (a < newPtrs + i0 ∨ newPtrs + (CP.d + 1) ≤ a) →
        out.mem a = st.mem a) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      c + (Finset.Ico i0 CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok' j) out.mem) ≤
        (CP.d - i0) * (P.readout + 48) + 50 +
        (Finset.Ico i0 CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem) := by
  let s1 := { st with regs := Function.update st.regs 20 i0 }
  have r1 : Runs w p ω (.assign 20 (.reg 96)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨i0, by simp [Expr.eval, h96], rfl, rfl, rfl⟩
  obtain ⟨s2, cLoop, coreTok', rLoop, hs2_lo, hs2_hi, hz2, hTokRep2, hTokDisj2, hForests2,
      hs2_fr, hs2_regs, hcLoop⟩ :=
    collectLSFForestsLoopKFBL_runs (w := w) (L := L) (capExp := capExp)
      (first := i0) (baseIdx := 0) (dstReg := 81) (dstPtrs := newPtrs)
      (handleBase := handleBase) (branchBase := branchBase) (levelMeta := levelMeta)
      (p := p) (ω := ω) (st := s1) next coreHandle coreTok0 hCoreLocal (by decide)
      (Nat.zero_le _) (le_of_lt hiLt) (by simp [s1]) (by simp [s1, h71]) (by simp [s1, h75])
      (by simp [s1, h77]) (by simp [s1, h78]) (by simp [s1, h83]) (by simp [s1, h81])
      hkW hdW hw1 hMetaEnd (by simp [s1]; omega) (by simp [s1]; omega) (by simp [s1]; omega)
      (by simpa [s1] using hRoom) hz0 hFootAt
      (fun j hj1 hj2 => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hG, hE, hD⟩ :=
          hCores j hj1 hj2
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8,
          by rcases h9 with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
          by rcases h10 with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
          by rcases h11 with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
          fun t ht1 ht2 => h12 t (by omega) (by omega),
          hG, hE, fun a ha1 ha2 => ⟨(hD a ha1 ha2).1,
            by rcases (hD a ha1 ha2).2 with h | h <;>
              [exact Or.inl (by omega); exact Or.inr (by omega)]⟩⟩)
      hCoreDisj
  obtain ⟨hTHO, hTBO, hTLO, hTFO, hTLLt, hTFLt, hTNf, hTFDisj⟩ := hTermDisjCells
  have hs2_eq (a : ℕ) (ha : a < st.regs 4)
      (hnf : ∀ r, i0 ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a)
      (hout : a < newPtrs + i0 ∨ newPtrs + CP.d ≤ a) : s2.mem a = st.mem a :=
    hs2_fr a ha hnf
      (by rcases hout with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
  obtain ⟨out, cTerm, rTerm, hcTerm, houtMem, houtRegs⟩ :=
    collectTermForestStmt_runs (w := w) (dstReg := 81) (dstPtrs := newPtrs) (baseIdx := 0)
      (d := CP.d) (handleBase := handleBase) (branchBase := branchBase) (termHandle := termHandle)
      (lastBran := next.lastBran) (lsfHdr := lsfHdr) (forestPtr := forestPtr)
      (p := p) (ω := ω) (st := s2)
      ((hs2_regs 81 (Or.inl (by decide))).trans (by simp [s1, h81]))
      ((hs2_regs 71 (Or.inl (by decide))).trans (by simp [s1, h71]))
      ((hs2_regs 75 (Or.inl (by decide))).trans (by simp [s1, h75]))
      ((hs2_regs 77 (Or.inl (by decide))).trans (by simp [s1, h77]))
      ((hs2_regs 78 (Or.inl (by decide))).trans (by simp [s1, h78]))
      (by decide) (Nat.zero_le _)
      ((hs2_eq _ (by omega) (fun r hr1 hr2 => (hTNf r hr1 hr2).1)
        (by rcases hTHO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hTermH)
      ((hs2_eq _ (by omega) (fun r hr1 hr2 => (hTNf r hr1 hr2).2.1)
        (by rcases hTBO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hTermB)
      ((hs2_eq _ hTLLt (fun r hr1 hr2 => (hTNf r hr1 hr2).2.2.1)
        (by rcases hTLO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans
        hTermLsf)
      ((hs2_eq _ hTFLt (fun r hr1 hr2 => (hTNf r hr1 hr2).2.2.2)
        (by rcases hTFO with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans
        hTermFPtr)
      (by omega) (by omega) (by omega) (by omega) (by omega) hw1
  simp only [Nat.sub_zero] at houtMem hForests2
  have hout4 : out.regs 4 = s2.regs 4 := houtRegs 4 (by decide) (by decide) (by decide)
  have hs1_4 : s1.regs 4 = st.regs 4 := rfl
  have hs1_m : s1.mem = st.mem := rfl
  rw [hs1_4] at hs2_lo hs2_hi
  rw [hs1_m] at hcLoop
  have hLastEq : newPtrs + CP.d = newPtrs + i0 + (CP.d - i0) := by omega
  have hCorePres (j : ℕ) (hj1 : i0 ≤ j) (hj2 : j < CP.d) :
      Rcore.rep (coreHandle j) (chainLevelOrdAbs next j) (coreTok' j) out.mem ∧
      Rcore.phi (coreHandle j) (coreTok' j) out.mem =
        Rcore.phi (coreHandle j) (coreTok' j) s2.mem := by
    have hloc := hCoreLocal (coreHandle j) (chainLevelOrdAbs next j) (coreTok' j) s2.mem out.mem
      (fun a ha => by
        have hne : a ≠ newPtrs + CP.d := by
          rcases (hTokRep2 j hj1 hj2).2 a ha with h0 | ⟨hlo, _⟩
          · exact fun heq =>
              (hCores j hj1 hj2).2.2.2.2.2.2.2.2.2.2.2.1 CP.d (by omega) (by omega) (heq ▸ h0)
          · omega
        rw [houtMem, Function.update_of_ne hne])
    exact ⟨hloc.1 (hTokRep2 j hj1 hj2).1, hloc.2.symm⟩
  have hForestList :
      ForestPtrListAt out.mem (newPtrs + i0) (chainSuffixForests next i0) intCap (out.regs 4) := by
    rw [hout4]
    refine ⟨by rw [chainSuffixForests_length]; omega, fun t ht => ?_⟩
    rw [chainSuffixForests_length] at ht
    by_cases htLt : t < CP.d - i0
    · rw [chainSuffixForests_getElem_lt next htLt]
      obtain ⟨vcT, ecT, hDGT, hEndT, hFootT⟩ := hForests2 (i0 + t) (by omega) (by omega)
      have hSub : newPtrs + (i0 + t) = newPtrs + i0 + t := by omega
      rw [hSub] at hDGT hEndT hFootT
      have hOutT : ∀ a, s2.mem (newPtrs + i0 + t) ≤ a →
          a < s2.mem (newPtrs + i0 + t) + dynGraphSize vcT ecT → a ≠ newPtrs + CP.d :=
        fun a ha1 ha2 heq => by
          have hf := hFootT a ha1 ha2
          rw [heq] at hf
          rcases (hTokRep2 (i0 + t) (by omega) (by omega)).2 _ hf with h0 | ⟨hlo, _⟩
          · exact (hCores (i0 + t) (by omega) (by omega)).2.2.2.2.2.2.2.2.2.2.2.1 CP.d
              (by omega) (by omega) h0
          · omega
      have hPtrT : out.mem (newPtrs + i0 + t) = s2.mem (newPtrs + i0 + t) := by
        rw [houtMem, Function.update_of_ne (by omega)]
      refine ⟨vcT, ecT, ?_, hPtrT.symm ▸ hEndT, hIntCap (i0 + t) (by omega) (by omega)⟩
      rw [hPtrT]
      exact dynGraphAt_of_agree hDGT (fun a ha1 ha2 => by
        rw [houtMem, Function.update_of_ne (hOutT a ha1 ha2)])
    · have htEq : t = CP.d - i0 := by omega
      subst htEq
      rw [chainSuffixForests_getElem_last]
      have hPtrL : out.mem (newPtrs + i0 + (CP.d - i0)) = forestPtr := by
        rw [houtMem, ← hLastEq, Function.update_self]
      refine ⟨vcLast, ecLast, ?_, hPtrL.symm ▸ (hTermFEnd.trans hs2_lo), hTermFCap⟩
      rw [hPtrL]
      exact dynGraphAt_of_agree hTermFDG (fun a ha1 ha2 => by
        obtain ⟨hNF, hOut⟩ := hTFDisj a ha1 ha2
        rw [houtMem, Function.update_of_ne (by rcases hOut with h | h <;> omega)]
        exact hs2_eq a (by omega) hNF
          (by rcases hOut with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]))
  have hForestLo :
      ∀ t < (chainSuffixForests next i0).length, lo ≤ out.mem (newPtrs + i0 + t) := by
    intro t ht
    rw [chainSuffixForests_length] at ht
    by_cases htLt : t < CP.d - i0
    · obtain ⟨vcT, ecT, _, _, hFootT⟩ := hForests2 (i0 + t) (by omega) (by omega)
      have hSub : newPtrs + (i0 + t) = newPtrs + i0 + t := by omega
      rw [hSub] at hFootT
      have hPtrT : out.mem (newPtrs + i0 + t) = s2.mem (newPtrs + i0 + t) := by
        rw [houtMem, Function.update_of_ne (by omega)]
      rw [hPtrT]
      have hf := hFootT _ le_rfl (by unfold dynGraphSize; omega)
      rcases (hTokRep2 (i0 + t) (by omega) (by omega)).2 _ hf with h0 | ⟨hlo, _⟩
      · exact hLoFoot (i0 + t) (by omega) (by omega) _ h0
      · have := hs1_4; omega
    · have htEq : t = CP.d - i0 := by omega
      subst htEq
      rw [houtMem, ← hLastEq, Function.update_self]
      exact hLoTerm
  have hPhiEq :
      (Finset.Ico i0 CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok' j) out.mem) =
      (Finset.Ico i0 CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok' j) s2.mem) :=
    Finset.sum_congr rfl (fun j hj =>
      (hCorePres j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2).2)
  refine ⟨out, 2 + (cLoop + cTerm + 1) + 1, coreTok',
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, cLoop + cTerm + 1, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, cLoop, cTerm, rLoop, rTerm, rfl⟩), rfl⟩),
    hout4.symm ▸ hs2_lo, hout4.symm ▸ hs2_hi,
    fun a ha => by
      rw [hout4] at ha
      rw [houtMem, Function.update_of_ne (by omega : a ≠ newPtrs + CP.d)]
      exact hz2 a ha,
    hForestList, hForestLo,
    fun j hj1 hj2 => ⟨(hCorePres j hj1 hj2).1,
      fun a ha => hout4.symm ▸ (hTokRep2 j hj1 hj2).2 a ha⟩,
    hTokDisj2,
    fun a ha hnf hout => by
      rw [houtMem, Function.update_of_ne (by rcases hout with h | h <;> omega)]
      exact hs2_eq a ha hnf
        (by rcases hout with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]),
    fun r hr => (houtRegs r (by omega) (by omega) (by omega)).trans
      ((hs2_regs r (Or.inl hr)).trans (by simp [s1, Function.update_of_ne (by omega : r ≠ 20)])),
    by rw [hPhiEq]; omega⟩

end MinCostFlow.MinRatio

end
