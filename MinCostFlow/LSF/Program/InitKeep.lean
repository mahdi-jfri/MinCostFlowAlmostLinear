module

public import MinCostFlow.LSF.Program.InitWstrMain

/-!
# The blocks that the last calls of the driver keep

After the decomposition phase the driver runs the forest phase and stores the two headers. The
forest phase writes the `F` graph, the `F` block and the `W` block, which lie between the `T`
block and the aux block, and uses a scratch area from `wBase` on. The headers are the first
`20` words of the aux block and the first `24` words of the state. So the `G` and `T` blocks
and the aux block after its header keep their contents up to `wBase` (`init_tail_frame`), and
the stretch arrays, which lie between the aux block and `endA`, keep `WstrAt`
(`init_wstrAt_final`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num
  InitDriver

@[expose] public section

/-- The forest phase changes only the `F` graph, the `F` block, the `W` block and its scratch
area. -/
lemma fPhase_frame {w h : ℕ} {X : FLayout} {bG bA bW : ℕ} {mem mem₃ : ℕ → ℕ} {ret : ℕ}
    (hpost : (fPhaseContract w h bG bA bW).post X.args mem ret mem₃) :
    ∀ a, (a < X.dgF ∨ X.dgF + dynGraphSize X.vCap X.eCap ≤ a) →
      (a < X.fAnc ∨ X.fAnc + fAncSize X.vCap ≤ a) →
      (a < X.wBase ∨ X.wBase + wWorkSize X.n X.logCap ≤ a) →
      (a < X.wPtr ∨ X.wPtr + wBlockSize X.n ≤ a) → mem₃ a = mem a := by
  obtain ⟨v₁, m₁, v₂, m₂, v₃, h₁, h₂, h₃⟩ := fPhase_post hpost
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₁, -, -, hfr₁⟩ := h₁
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  obtain ⟨_, _, _, _, _, _, heq₂, -, hfr₂, -⟩ := h₂
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₃, -, -, hfr₃, -⟩ := h₃
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  intro a ha1 ha2 ha3 ha4
  rw [hfr₃ a ha3 ha4, hfr₂ a ha2, hfr₁ a ha1]

/-- After the forest phase and the two headers, the `G` and `T` blocks and the aux block after
its header hold what they held after the decomposition phase. -/
lemma init_tail_frame {w h : ℕ} {bG bA bW : ℕ} {V : InitVals}
    {nOrig θ D kk lenArr cnt v₆ v₇ v₈ : ℕ} {vs₇ vs₈ : List ℕ} {mem₅ mem₆ mem₇ mem₈ : ℕ → ℕ}
    (h₆ : (fPhaseContract w h bG bA bW).post
      (FLayout.ofVals V nOrig θ D kk lenArr cnt).args mem₅ v₆ mem₆)
    (h₇ : (storeArgsContract w 20).post (V.auxPtr :: vs₇) mem₆ v₇ mem₇)
    (h₈ : (storeArgsContract w 24).post (V.b :: vs₈) mem₇ v₈ mem₈) (hH : V.lsstHeap ≤ V.H) :
    ∀ a, ((V.gPtr ≤ a ∧ a < V.fPtr) ∨ (V.auxPtr + 20 ≤ a ∧ a < V.wBase)) → mem₈ a = mem₅ a := by
  have hfr₆ := fPhase_frame h₆
  obtain ⟨_, _, heq₇, -, -, hfr₇⟩ := h₇
  simp only [List.cons.injEq] at heq₇
  obtain ⟨rfl, rfl⟩ := heq₇
  obtain ⟨_, _, heq₈, -, -, hfr₈⟩ := h₈
  simp only [List.cons.injEq] at heq₈
  obtain ⟨rfl, rfl⟩ := heq₈
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  have hls : lsfHdrSize = 24 := rfl
  have hwb : V.endA ≤ V.wBase := by
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
      s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32⟩ := V.scratch_order
    omega
  have hax : V.auxPtr ≤ V.numSt := by
    have h20' : auxHdrSize = 20 := rfl
    have : 20 ≤ auxSize V.vCap V.n0 := by simp only [auxSize]; omega
    omega
  intro a ha
  rw [hfr₈ a (Or.inr (by omega)), hfr₇ a (by omega)]
  refine hfr₆ a ?_ ?_ ?_ ?_
  · show a < V.fPtr ∨ V.fPtr + dynGraphSize V.vCap (fECap V.eCap V.n0) ≤ a
    omega
  · show a < V.fAncPtr ∨ V.fAncPtr + fAncSize V.vCap ≤ a
    omega
  · show a < V.wBase ∨ _
    omega
  · show a < V.wPtr ∨ V.wPtr + wBlockSize V.n0 ≤ a
    omega

/-- The stretch arrays keep `WstrAt` through the forest phase and the headers. -/
lemma init_wstrAt_final {w h : ℕ} {bG bA bW : ℕ} {V : InitVals}
    {nOrig θ D kk lenArr cnt v₆ v₇ v₈ : ℕ} {vs₇ vs₈ : List ℕ} {mem₅ mem₆ mem₇ mem₈ : ℕ → ℕ}
    {G : MGraph} {wstr : ℕ → ℝ}
    (hW : WstrAt mem₅ V.numSt V.denSt V.eCap h V.L_w G wstr)
    (h₆ : (fPhaseContract w h bG bA bW).post
      (FLayout.ofVals V nOrig θ D kk lenArr cnt).args mem₅ v₆ mem₆)
    (h₇ : (storeArgsContract w 20).post (V.auxPtr :: vs₇) mem₆ v₇ mem₇)
    (h₈ : (storeArgsContract w 24).post (V.b :: vs₈) mem₇ v₈ mem₈) (hH : V.lsstHeap ≤ V.H) :
    WstrAt mem₈ V.numSt V.denSt V.eCap h V.L_w G wstr := by
  have hfr := init_tail_frame h₆ h₇ h₈ hH
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, -⟩ := V.aux_order
  have hwb : V.endA ≤ V.wBase := by
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
      s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32⟩ := V.scratch_order
    omega
  have h20 : V.auxPtr + 20 ≤ V.numSt := by
    have h20' : auxHdrSize = 20 := rfl
    have : 20 ≤ auxSize V.vCap V.n0 := by simp only [auxSize]; omega
    omega
  exact hW.of_agree (fun a ha1 ha2 => hfr a (Or.inr ⟨by omega, by omega⟩))
    (fun a ha1 ha2 => hfr a (Or.inr ⟨by omega, by omega⟩))

end

end MinCostFlow.LSF.Program
