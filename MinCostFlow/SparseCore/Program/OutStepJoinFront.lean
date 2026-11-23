module

public import MinCostFlow.SparseCore.Program.OutStepEnds

/-!
# The first three phases of the output step

The output step runs six phases (`outStepBody`). This file joins the first three: the setup
(`osSetup_runs`), the deletions (`osDelPhase_runs`) and the splits (`osSplitPhase_runs`). The
lemma `osFront_runs` is stated for any lists of leaving edges `delL` and of splits `P` with the
facts that the phase lemmas ask for, so it does not mention the model. Afterwards the stored
graph is the old graph after the deletions and the splits, the batch region holds these updates,
the edit region holds their edits, and the marked ends are the ends of the kept edges.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ}

/-- **The setup, the deletions and the splits.** -/
theorem osFront_runs (hC : SCtx T A tx₀) {au gd flt wk : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    (hgd : ∀ G, MeetsContract w p gd (dgGetDegContract w vCap eCap G))
    (hflt : p.procs[flt]? = some outFilterBody) (hwk : p.procs[wk]? = some outWalkBody)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (hRdef : A.R = (vCap + 1) * (eCap + 1) * 16)
    (ht0 : A.t0 < 2 ^ w) (htour : A.tourH < 2 ^ w)
    {S₀ : MGraph} {s : OutTourAbs} {cord : ℕ → List End} {E' E₀ keep : Finset ℕ} {delL : List ℕ}
    {P : List Update} {Ys : List (List End)} {st : State}
    (h0 : st.regs 0 = A.outH) (h1 : st.regs 1 = A.tourH) (h2 : st.regs 2 = A.delPtr)
    (h3 : st.regs 3 = A.splitPtr) (h4 : st.regs 4 = A.insPtr) (h5 : st.regs 5 = A.rotPtr)
    (h6 : st.regs 6 = A.h)
    (hB : SBase T A tx₀ mem₀ S₀ S₀ [] [] (A.h + 5) (A.e0 + 1) A.t0 s tx₀ st.mem)
    (hmk : OutMarksOf s cord E₀) (hE₀ : keep ⊆ E₀ ∧ E₀ ⊆ S₀.E) (hS₀ : ∀ e ∈ S₀.E, e < eCap)
    (hdel : OutDelAt mem₀ A.delPtr delL E')
    (hdfree : OutCellsFree A.delPtr (1 + 2 * delL.length) A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a))
    (hdnd : delL.Nodup) (hdsub : ∀ e ∈ delL, e ∈ S₀.E)
    (hflag1 : ∀ e ∈ delL, e ∈ E' → ∀ b, ∃ v < vCap, (e, b) ∈ cord v)
    (hflag0 : ∀ e ∈ delL, e ∉ E' → ∀ b v, (e, b) ∉ cord v)
    (hkeep : S₀.E \ delL.toFinset = keep)
    (hsl : OutSplitListsAt mem₀ A.h
      (fun a => (outGraphRep vCap eCap).foot A.outH A.g a ∨ T.rep.foot A.tourH tx₀ a)
      keep S₀.E A.splitPtr (S₀.applyBatch (delL.map Update.delete)) P Ys)
    (hGv : (S₀.applyBatch (delL.map Update.delete)).IsValid)
    (hbv : (S₀.applyBatch (delL.map Update.delete)).BatchIsValid P)
    (hcap : ∀ u ∈ P, UpdateWithinCaps vCap eCap u)
    (hroomR : 2 * delL.length + 4 * P.length +
      (S₀.applyBatch (delL.map Update.delete)).batchEnc P + 4 * eCap + 6 ≤ A.R)
    (hnw : delL.length + P.length < 2 ^ w)
    (hroom : A.t0 + 2 * delL.length * S.querySpace < 2 ^ w) :
    ∃ st₁ c₁ st₂ c₂ st₃ c₃ s' tx',
      Runs w p ω osSetup st .normal st₁ c₁ ∧ Runs w p ω (osDelPhase sm au) st₁ .normal st₂ c₂ ∧
      Runs w p ω (osSplitPhase au gd flt wk) st₂ .normal st₃ c₃ ∧
      SBase T A tx₀ mem₀ S₀ ((S₀.applyBatch (delL.map Update.delete)).applyBatch P)
        (delL.map Update.delete ++ P)
        (delL.map OrdEdit.dropEdge ++ outPrefixEditsOn (S₀.applyBatch (delL.map Update.delete)) P)
        (A.h + 5 + 2 * delL.length +
          (4 * P.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P))
        (A.e0 + 1 + 2 * delL.length +
          (3 * P.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P))
        (st₃.regs 7) s' tx' st₃.mem ∧
      OutMarksOf s' cord keep ∧ SRegs st₃ A vCap eCap ∧
      st₃.regs 14 = A.h + 5 + 2 * delL.length +
        (4 * P.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P) ∧
      st₃.regs 16 = A.e0 + 1 + 2 * delL.length +
        (3 * P.length + (S₀.applyBatch (delL.map Update.delete)).batchEnc P) ∧
      st₃.regs 17 = delL.length + P.length ∧ st₃.regs 18 = delL.length + P.length ∧
      A.t0 ≤ st₃.regs 7 ∧ st₃.regs 7 ≤ A.t0 + 2 * delL.length * S.querySpace ∧
      c₁ + c₂ + c₃ + T.rep.phi A.tourH tx' st₃.mem ≤
        delL.length * (2 * (S.mul * ordStoreLog eCap) + 1700) +
          2000 * (Ys.map List.length).sum +
          5000 * (S₀.applyBatch (delL.map Update.delete)).batchEnc P + 230 +
          T.rep.phi A.tourH tx₀ st.mem := by
  have hgh := hC.2.2.1
  have hR0 : A.e0 = A.h + 4 + A.R := rfl
  have ht0e : A.t0 = A.e0 + A.R := rfl
  -- the setup
  obtain ⟨st₁, c₁, hr₁, hm₁, hR₁, h7₁, h14₁, h16₁, h17₁, h18₁, hc₁⟩ :=
    osSetup_runs (p := p) (ω := ω) (vCap := vCap) (eCap := eCap) h0 h1 h2 h3 h4 h5 h6
      hB.2.2.2.2.2.1 hB.2.2.2.2.2.2.1 hRdef ht0 hgh
  rw [← hm₁] at hB
  -- the deletions
  have hdcap : ∀ e ∈ delL, e < eCap := fun e he => hS₀ e (hdsub e he)
  obtain ⟨st₂, c₂, hr₂, φ₂, hI₂, hc₂⟩ := osDelPhase_runs (sm := sm) (ω := ω) hC hau hw ht0
    htour hdel hdfree hdnd hdsub hdcap hflag1 hflag0 (by omega) hroom hB hR₁ h7₁ h14₁ h16₁ h17₁
    h18₁ hmk
  obtain ⟨s₂, tx₂, hB₂, hR₂, h14₂, h16₂, h17₂, h18₂, -, -, -, hmk₂, hc2a, hc2b, hphi₂⟩ := hI₂
  simp only [List.take_length] at hB₂ hmk₂
  have hE₀del : E₀ \ delL.toFinset = keep := by
    ext e
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨he, hd⟩
      rw [← hkeep]; exact Finset.mem_sdiff.mpr ⟨hE₀.2 he, hd⟩
    · intro hk
      refine ⟨hE₀.1 hk, ?_⟩
      rw [← hkeep] at hk; exact (Finset.mem_sdiff.mp hk).2
  rw [hE₀del] at hmk₂
  -- the splits
  have hkeepE : (S₀.applyBatch (delL.map Update.delete)).E ⊆ keep := by
    rw [(applyBatch_dels_E S₀ delL).1, hkeep]
  obtain ⟨st₃, c₃, hr₃, hB₃, hp₃, hR₃, h7₃, h14₃, h16₃, h17₃, h18₃, hc₃⟩ :=
    osSplitPhase_runs (ω := ω) hC hau hgd hflt hwk hw ht0 hS₀ hB₂ hR₂ h14₂ h16₂
      (by rw [h17₂, List.length_map]) (by rw [h18₂, List.length_map]) hsl rfl hGv hbv hcap
      hkeepE (by omega) (by omega) (by rw [List.length_map]; omega)
      (by rw [List.length_map]; omega)
  rw [List.length_map] at h17₃ h18₃
  refine ⟨st₁, c₁, st₂, c₂, st₃, c₃, s₂, tx₂, hr₁, hr₂, hr₃, ?_, hmk₂, hR₃, h14₃, h16₃,
    h17₃, h18₃, by rw [h7₃]; exact hc2a, by rw [h7₃]; exact hc2b, ?_⟩
  · rw [h7₃]; exact hB₃
  · rw [hp₃, hphi₂]
    rw [hm₁] at hc₂
    omega

end MinCostFlow.SparseCore.Program
