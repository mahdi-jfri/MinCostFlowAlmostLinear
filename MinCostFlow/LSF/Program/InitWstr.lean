module

public import MinCostFlow.LSF.Program.WstrBridge
public import MinCostFlow.LSF.Program.WstrCopy

/-!
# The stretches of the initial state

`wstr_bridge` gives the stretch of one edge position `t` after `wstrProc`. The edge list at
`eList` holds every edge of `G` once, so every edge `e` of `G` is `mem (eList + t)` for some
`t < m₀`. `wstrAt_of_bridge` collects the edges: the arrays at `numPtr` and `denPtr` represent the
stretches `wstr` of the model (`initLSFWith`), which are `1` for an edge whose raw stretch is at
least the threshold and the raw stretch otherwise (`wstrAt_of_bridge`). `WstrAt.of_copy` then moves
the arrays to the static places, after the two copies of the initialization.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.Num

@[expose] public section

/-- The stretches that `initLSFWith` stores, for the tree `T₀`, the root `r₀`, the order `π`, the
lengths `ℓ` and the threshold `thresh`. -/
noncomputable def initWstr (T₀ G : MGraph) (r₀ : ℕ) (π : ℕ → ℕ) (ℓ : ℕ → ℝ) (thresh : ℝ) :
    ℕ → ℝ :=
  open Classical in
  fun e => if e ∈ G.E then
    (if thresh ≤ levelStretchBound T₀ r₀ π G ℓ e then (1 : ℝ) else levelStretchBound T₀ r₀ π G ℓ e)
  else 1

/-- The stretches of `initLSFWith` are `initWstr`. -/
lemma initLSFWith_wstr (G₀ : MGraph) (ℓ₀ v : ℕ → ℝ) (k : ℝ) (T_raw : MGraph) (r₀ : ℕ)
    (C_reps : Finset ℕ) (π : ℕ → ℕ) (W_T : Finset (Finset ℕ)) (thresh : ℝ) :
    (initLSFWith G₀ ℓ₀ v k T_raw r₀ C_reps π W_T thresh).wstr =
      initWstr (projectTree G₀ v T_raw) G₀ r₀ π (safeLen G₀ ℓ₀) thresh := by
  funext e
  simp only [initLSFWith, initWstr]

/-- After `wstrProc`, the arrays at `numPtr` and `denPtr` represent the stretches `initWstr`. The
hypotheses are those of `wstr_bridge`; the ones that depend on the edge position `t` are asked for
every `t < m₀`. The edge list holds every edge of `G` (`heL`). The high flags are `1` exactly
for the edges whose stretch bound reaches the threshold. -/
theorem wstrAt_of_bridge {w h C : ℕ} {mem mem' : ℕ → ℕ}
    {n tM m0 k LB Lw Lin nOrig r logCap lenArr fidPtr qPtr parPtr pePtr piPtr thDepPtr euPtr evPtr
     upPtr depPtr eList numPtr denPtr idPtr ltBase ldBase duvBase inRPtr mpPtr ownPtr rtPtr dRBase
     accBase leBase k2Out thOut tA tB tF tmp1 tmp2 highPtr eCap : ℕ}
    {T₀ G : MGraph} {vList : List ℕ} {fid tl hd dep π : ℕ → ℕ} {ℓ : ℕ → ℝ} {S M : ℕ}
    {thresh : ℝ}
    (hpre : WstrPre w h C mem n tM m0 k LB Lw Lin nOrig r logCap lenArr fidPtr qPtr parPtr pePtr
      piPtr thDepPtr euPtr evPtr upPtr depPtr eList numPtr denPtr idPtr ltBase ldBase duvBase
      inRPtr mpPtr ownPtr rtPtr dRBase accBase leBase k2Out thOut tA tB tF tmp1 tmp2 highPtr)
    (hpost : WstrPost w h C mem mem' n tM m0 k LB Lw Lin nOrig r logCap lenArr fidPtr qPtr parPtr
      pePtr piPtr thDepPtr euPtr evPtr upPtr depPtr eList numPtr denPtr idPtr ltBase ldBase
      duvBase inRPtr mpPtr ownPtr rtPtr dRBase accBase leBase k2Out thOut tA tB tF tmp1 tmp2
      highPtr)
    (hI : TreeIdx T₀ vList tM r fid tl hd (fun x => mem (parPtr + x)) (fun x => mem (pePtr + x))
      dep)
    (hnl : vList.length = n)
    (hLT : LcaTables w n logCap upPtr depPtr parPtr (fun x => mem (parPtr + x)) dep mem)
    (hthd : ∀ x < n, mem (thDepPtr + x) =
      depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0))
    (hπ : IsEdgeOrder T₀ π) (hpiv : ∀ j < tM, π (fid j) = mem (piPtr + j))
    (hℓT : ∀ f ∈ T₀.E, 0 ≤ ℓ f)
    (hlt : ∀ i < tM, (blkExtVal h mem lenArr fidPtr Lin nOrig i : ℝ) = S * ℓ (fid i))
    (hM : ∀ x < n, (S : ℝ) * wDepth T₀ (vList.getD r 0) ℓ (vList.getD x 0) ≤ M)
    (hcap : 4 * M * (hldDepthBound n + 1 + 1) < capacity h LB)
    (hhL : 2 ≤ h * Lw) (hLw : 1 ≤ Lw) (hS : 0 < S)
    (heL : ∀ e ∈ G.E, ∃ t < m0, mem (eList + t) = e) (heC : ∀ e ∈ G.E, e < eCap)
    (htail : ∀ t < m0, vList.getD (mem (euPtr + t)) 0 = G.tail (mem (eList + t)))
    (hhead : ∀ t < m0, vList.getD (mem (evPtr + t)) 0 = G.head (mem (eList + t)))
    (hE : ∀ t < m0,
      (unsignedVal mem (lenArr + mem (eList + t) * Lin) h Lin : ℝ) = S * ℓ (mem (eList + t)))
    (hE1 : ∀ t < m0, 1 ≤ unsignedVal mem (lenArr + mem (eList + t) * Lin) h Lin)
    (hE2 : ∀ t < m0, 2 * unsignedVal mem (lenArr + mem (eList + t) * Lin) h Lin < capacity h Lin)
    (hfitN : ∀ t < m0, 2 * (4 * M * (hldDepthBound n + 1)) +
      2 * (hldDepthBound n + 1) * unsignedVal mem (lenArr + mem (eList + t) * Lin) h Lin <
        capacity h LB)
    (hθ : threshProd C n k < 2 ^ (h * (Lw - Lin)))
    (hthr : (threshProd C n k : ℝ) = thresh) :
    WstrAt mem' numPtr denPtr eCap h Lw G
      (initWstr T₀ G (vList.getD r 0) π ℓ thresh) ∧
    ∀ t < m0, mem' (highPtr + t) =
      if thresh ≤ levelStretchBound T₀ (vList.getD r 0) π G ℓ (mem (eList + t)) then 1 else 0 := by
  refine ⟨⟨hhL, hLw, fun e he => ?_⟩, fun t ht => ?_⟩
  swap
  · obtain ⟨-, -, -, -, -, hhi⟩ := wstr_bridge hpre hpost hI hnl hLT hthd hπ hpiv hℓT hlt
      hM hcap hhL hS ht (htail t ht) (hhead t ht) (hE t ht) (hE1 t ht) (hE2 t ht) (hfitN t ht) hθ
    rw [hhi, hthr]
  obtain ⟨t, ht, rfl⟩ := heL e he
  obtain ⟨hVN, hVD, hIN, hID, hval, -⟩ := wstr_bridge hpre hpost hI hnl hLT hthd hπ hpiv hℓT hlt
    hM hcap hhL hS ht (htail t ht) (hhead t ht) (hE t ht) (hE1 t ht) (hE2 t ht) (hfitN t ht) hθ
  refine ⟨heC _ he, hVN, hVD, hIN, hID, ?_⟩
  rw [hval, hthr]
  simp only [initWstr, if_pos he]

end

end MinCostFlow.LSF.Program
