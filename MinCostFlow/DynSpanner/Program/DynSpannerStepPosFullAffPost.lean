module

public import MinCostFlow.DynSpanner.Program.DynSpannerStepPosFullAff
import MinCostFlow.DynSpanner.Program.DynSpannerAffectedFilter

/-!
# The post of the affected stage as facts on one memory

`stepPosAff_facts` turns the post of `dsAffStage` (`dsAffStageContract`, stated with the context
`AffCtx` and the memories after each of its three calls) into facts on the memory `memAff` after
the stage, stated with the values of the fields of the context. These are the facts that
`StepPosCtx` asks about `memAff`. See `DynSpannerStepPosFullAff.lean` for the reasons.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- The facts on the memory `memAff` after `dsAffStage`, with `mem2` the memory before it. The
candidates `cand` and the affected edges `eAff` (an enumeration of `E`) lie in the heap after the
list of `S_{j-1}` at `heapAff + 2`, and the walk pointers right after `eAff`. The walks `Π_{<j}(e)`
lie in `F`. -/
def StepPosAffFacts (L vCap eCap b heapAff : ℕ) (G' : MGraph) (piLt_mid : Embedding)
    (S_prev E : Finset ℕ) (sPrevList : List ℕ) (mem2 memAff : ℕ → ℕ) (F : ℕ → Prop)
    (cand eAff : List ℕ) : Prop :=
  cand.Nodup ∧ (∀ e ∈ cand, e ∈ G'.E) ∧
  eAff.Nodup ∧ (∀ e, e ∈ eAff ↔ e ∈ E) ∧
  memAff heapAff = sPrevList.length ∧ memAff (heapAff + 1) = cand.length ∧
  ListAt memAff (heapAff + 2) sPrevList ∧
  ListAt memAff (heapAff + 2 + sPrevList.length + cand.length) eAff ∧
  DynGraphAt memAff (dsAuxPtr b vCap eCap) vCap eCap
    (buildProjGraph G' G' piLt_mid S_prev E) ∧
  (∀ k (hk : k < eAff.length),
    let ptr := memAff (heapAff + 2 + sPrevList.length + cand.length + eAff.length + k)
    b + dsFixedSize L vCap eCap ≤ ptr ∧
    (∀ addr, ptr ≤ addr → addr < ptr + (mWalkEncode (piLt_mid eAff[k])).length → F addr) ∧
    MWalkAt memAff ptr (piLt_mid eAff[k])) ∧
  (∀ e ∈ eAff,
    let wpEnd := heapAff + 2 + sPrevList.length + cand.length + eAff.length + eAff.length
    wpEnd ≤ memAff (dsMEmbTempBase b L vCap eCap + e) ∧
    memAff (dsMEmbTempBase b L vCap eCap + e) +
      (2 * (projWalk G' G' piLt_mid S_prev e).length + 1) ≤
      wpEnd + projHeapNeed piLt_mid eAff ∧
    MWalkAt memAff (memAff (dsMEmbTempBase b L vCap eCap + e))
      (projWalk G' G' piLt_mid S_prev e)) ∧
  (∀ v < vCap, memAff (dsSBitBase b L vCap eCap + v) = if v ∈ S_prev then 1 else 0) ∧
  memAff (b + dsGenOff) = mem2 (b + dsGenOff) + 1 ∧
  (∀ e < eCap, memAff (dsEStampBase b L vCap eCap + e) ≤ memAff (b + dsGenOff)) ∧
  (∀ addr, addr < heapAff → addr ≠ b + dsGenOff →
    (addr < dsAuxPtr b vCap eCap ∨ dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ addr) →
    (addr < dsSBitBase b L vCap eCap ∨ dsSBitBase b L vCap eCap + vCap ≤ addr) →
    (addr < dsEStampBase b L vCap eCap ∨ dsEStampBase b L vCap eCap + eCap ≤ addr) →
    (addr < dsMEmbTempBase b L vCap eCap ∨ dsMEmbTempBase b L vCap eCap + eCap ≤ addr) →
    memAff addr = mem2 addr) ∧
  (∀ addr, heapAff + 2 + sPrevList.length + cand.length + eAff.length + eAff.length +
      projHeapNeed piLt_mid eAff + cand.length ≤ addr → memAff addr = mem2 addr)

end

public section

/-- `dsAffStage` run on the context `a`, whose fields have the given values, returns `|eAff|` and
leaves a memory with the facts `StepPosAffFacts`. -/
theorem stepPosAff_facts {L vCap eCap b heapAff : ℕ} {G' : MGraph} {piLt_mid : Embedding}
    {S_prev E : Finset ℕ} {sPrevList : List ℕ} {mem2 memAff : ℕ → ℕ} {F : ℕ → Prop}
    {args : List ℕ} {ret : ℕ}
    (a : AffCtx) (haL : a.L = L) (havC : a.vCap = vCap) (haeC : a.eCap = eCap)
    (hab : a.b = b) (hah : a.heapPtr = heapAff) (haG : a.G' = G')
    (hapi : a.piLt_mid = piLt_mid) (haS : a.S_prev = S_prev) (has : a.sPrevList = sPrevList)
    (ham : a.mem0 = mem2) (haF : a.footPi = F) (haE : a.affSet = E)
    (hpost : (dsAffStageContract a).post args mem2 ret memAff) :
    ∃ cand eAff : List ℕ, ret = eAff.length ∧
      StepPosAffFacts L vCap eCap b heapAff G' piLt_mid S_prev E sPrevList mem2 memAff F cand eAff := by
  subst haL havC haeC hab hah haG hapi haS has ham haF haE
  obtain ⟨cand, eAff, mem₁, mem₂, retP, h₁, h₂, hiffC, hiffA, hproj, hret, hm0, hm1, hsL, hgen,
    hest, hfr₁, hfr₂⟩ := hpost
  obtain ⟨hJ, hwp, hemb, hretP, hfr₃⟩ := hproj
  simp only [AffCtx.toFilter] at hJ hwp hemb hretP hfr₃
  obtain ⟨hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10⟩ :=
    sBit_ge_layout a.b a.L a.vCap a.eCap
  have hfa := dsFixedSize_add a.b a.L a.vCap a.eCap
  have hfixH := a.hfixH
  have hES : dsEStampBase a.b a.L a.vCap a.eCap + a.eCap ≤ a.b + dsFixedSize a.L a.vCap a.eCap := by
    simp only [dsMEmbTempBase, dsKeptStampBase] at hfa; omega
  have hSE : dsSBitBase a.b a.L a.vCap a.eCap + a.vCap ≤ dsEStampBase a.b a.L a.vCap a.eCap := by
    simp only [dsEStampBase, dsVStampBase]; omega
  have hMT : dsMEmbTempBase a.b a.L a.vCap a.eCap + a.eCap = a.b + dsFixedSize a.L a.vCap a.eCap :=
    hfa
  have hcp : a.candPtr = a.heapPtr + 2 + a.sPrevList.length := rfl
  have hsubE : a.affSet ⊆ a.candSet := Finset.filter_subset _ _
  have hiffE : ∀ e, e ∈ eAff ↔ e ∈ a.affSet := hiffA
  have heAffG : ∀ e ∈ eAff, e ∈ a.G'.E := fun e he => h₂.sub e he
  have heAffC : ∀ e ∈ eAff, e < a.eCap := fun e he => h₂.lt e he
  -- The frame of the projection, for addresses of the heap below its area or above it.
  have hF3 : ∀ addr, (addr < a.candPtr + cand.length + eAff.length ∨
      a.candPtr + cand.length + eAff.length + eAff.length + projHeapNeed a.piLt_mid eAff ≤
        addr) →
      (addr < dsAuxPtr a.b a.vCap a.eCap ∨
        dsAuxPtr a.b a.vCap a.eCap + dynGraphSize a.vCap a.eCap ≤ addr) →
      (addr < dsMEmbTempBase a.b a.L a.vCap a.eCap ∨
        dsMEmbTempBase a.b a.L a.vCap a.eCap + a.eCap ≤ addr) →
      memAff addr = mem₂ addr := fun addr h1 h2 h3 =>
    hfr₃ addr h1 h2 fun e he => by have := heAffC e he; omega
  have hgenAff : memAff (a.b + dsGenOff) = a.mem0 (a.b + dsGenOff) + 1 := by
    rw [hF3 _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
      hfr₂ _ (Or.inl (by omega))]
    exact hgen
  refine ⟨cand, eAff, hret, h₁.nd, h₁.sub, h₂.nd, hiffE, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hgenAff, ?_, ?_, ?_⟩
  · rw [hF3 _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega)),
      hfr₂ _ (Or.inl (by omega))]
    exact hm0
  · rw [hF3 _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega)),
      hfr₂ _ (Or.inl (by omega))]
    exact hm1
  · refine hsL.congr fun k hk1 hk2 => ?_
    rw [hF3 _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega)),
      hfr₂ _ (Or.inl (by omega))]
  · refine h₂.at_.congr fun k hk1 hk2 => ?_
    exact hF3 _ (Or.inl (by simp only [AffCtx.candPtr] at hk2 ⊢; omega)) (Or.inr (by omega))
      (Or.inr (by omega))
  · have hfs : eAff.toFinset = a.affSet := by ext e; simp [hiffE]
    rw [hfs] at hJ
    exact hJ
  · intro k hk
    set e := eAff[k]
    have heE : e ∈ eAff := List.getElem_mem hk
    have hj1 := a.h1j
    have hjL := a.hjL
    have hlv := findEmbLevel_lt a.inDom_mid hj1 hjL e
    set i : Fin (a.L + 1) := ⟨findEmbLevel a.inDom_mid a.j e, hlv.2⟩
    have hei : e ∈ a.inDom_mid i := findEmbLevel_mem a.inDom_mid hj1 hjL (a.hinDom0 e (heAffG e heE))
    obtain ⟨hW, hfoot, _⟩ := a.hpi_at i hlv.1 e hei
    have hidx : i.1 * a.eCap + e < (a.L + 1) * a.eCap := idx_lt_mul i.2 (heAffC e heE)
    have hptr : memAff (a.candPtr + cand.length + eAff.length + k) =
        a.mem0 (dsPiPtrBase a.b a.L a.vCap a.eCap + i.1 * a.eCap + e) := by
      have ha1 : dsPiPtrBase a.b a.L a.vCap a.eCap + i.1 * a.eCap + e <
          dsSBitBase a.b a.L a.vCap a.eCap := by omega
      have ha2 : dsPiPtrBase a.b a.L a.vCap a.eCap + i.1 * a.eCap + e ≠ a.b + dsGenOff := by
        have : dsDomGenBase a.b a.L a.vCap a.eCap ≤ dsPiPtrBase a.b a.L a.vCap a.eCap := by
          simp only [dsPiPtrBase, dsEdgeDomGenBase]; omega
        omega
      rw [hwp k hk]
      exact h₂.agree _ (Or.inl ⟨ha1, ha2⟩)
    have hpiE : a.piLt_mid e = a.Pi_level i e := by
      rw [a.hpiLt_eq]
      simp only [piLtFrom, hlv.2, ↓reduceDIte]
      rfl
    simp only [AffCtx.candPtr] at hptr
    simp only
    rw [hptr, hpiE]
    set ptr := a.mem0 (dsPiPtrBase a.b a.L a.vCap a.eCap + i.1 * a.eCap + e)
    have hlen : 0 < (mWalkEncode (a.Pi_level i e)).length := by
      rw [mWalkEncode_length]; omega
    refine ⟨(a.hfootPi ptr (hfoot ptr le_rfl (by omega))).1, hfoot, ?_⟩
    refine hW.of_agree fun addr h1 h2 => ?_
    have hfa' := a.hfootPi addr (hfoot addr h1 (by rw [mWalkEncode_length]; omega))
    rw [hF3 addr (Or.inl (by simp only [AffCtx.candPtr]; omega)) (Or.inr (by omega))
      (Or.inr (by omega))]
    exact h₂.agree addr (Or.inr hfa')
  · intro e he
    obtain ⟨h1, h2, h3⟩ := hemb e he
    have hle := projHeapAt_length_le a.G' a.piLt_mid a.S_prev eAff
      (a.candPtr + cand.length + eAff.length + eAff.length)
    simp only [AffCtx.candPtr] at h1 h2 hle hretP ⊢
    refine ⟨h1, by omega, h3⟩
  · intro v hv
    rw [hF3 _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
    exact h₂.sBit v hv
  · intro e he
    have hEM : dsEStampBase a.b a.L a.vCap a.eCap + a.eCap ≤ dsMEmbTempBase a.b a.L a.vCap a.eCap := by
      simp only [dsMEmbTempBase, dsKeptStampBase]; omega
    rw [hgenAff, hF3 _ (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega)),
      hfr₂ _ (Or.inl (by omega))]
    exact hest e he
  · intro addr h1 h2 h3 h4 h5 h6
    rw [hF3 addr (Or.inl (by omega)) h3 h6, hfr₂ addr (Or.inl (by omega))]
    exact hfr₁ addr ⟨h2, fun v hv => by omega, fun e he => by omega, Or.inl h1⟩
  · intro addr h
    simp only [AffCtx.candPtr] at hF3 hfr₂ hfr₁
    rw [hF3 addr (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)),
      hfr₂ addr (Or.inr (by omega))]
    exact hfr₁ addr ⟨by omega, fun v hv => by omega, fun e he => by omega, Or.inr (by omega)⟩

end

end MinCostFlow.DynSpanner.Program
