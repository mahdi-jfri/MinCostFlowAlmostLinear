module

public import MinCostFlow.LSF.Program.Wstr
public import MinCostFlow.LSF.Program.WstrLevelMath
public import MinCostFlow.Num.ShiftFacts
public import MinCostFlow.LSF.Program.THDepthMath

/-!
# From `wstrProc` to the stretches of the model

The model sets `wstr e = 1` when the raw stretch `levelStretchBound` of `e` is at least the
threshold `θ`, and `wstr e = levelStretchBound` otherwise (`initLSFWith`). With `H` levels,

  `levelStretchBound = 2 Σ_{j < H} (1 + levelDist_j / ℓ e) = (2 H E + 2 A) / E`,

where `E = S ℓ e` is the integer length and `A = S Σ_j levelDist_j` the accumulator
(`levelStretchBound_eq`). So the test `N < θ E` of `wstrEdgeProc`, with `N = 2 A + 2 H E`, is the
test `raw < θ`.

* `wstrEdgeOut_value`: the arithmetic of one edge, when no block overflows.
* `levelStretchBound_eq`: the sum above.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.Num

/-- A block value below half the capacity is its signed value. -/
lemma intVal_of_lt_half {mem : ℕ → ℕ} {a h L : ℕ}
    (hu : 2 * unsignedVal mem a h L < capacity h L) :
    intVal mem a h L = unsignedVal mem a h L := by
  unfold intVal signedVal
  rw [if_neg (by omega)]
  simp

/-- The value of one edge. The accumulator `A`, the length `E`, the level count `H` and the
threshold `θ` are such that nothing overflows: `2 A + 2 H E` and `θ E` fit in `LB` limbs, and
`2 θ E` fits in `L_w` limbs. Then the two output blocks hold the stretch of the model, and the
flag says whether the raw stretch reached the threshold. -/
theorem wstrEdgeOut_value {h LB Lw : ℕ} {mem' : ℕ → ℕ} {numOut denOut acc le th k2 ret : ℕ}
    {A E H θ : ℕ} (hO : WstrEdgeOut h LB Lw mem' mem' numOut denOut acc le th k2 ret)
    (hA : unsignedVal mem' acc h LB = A) (hE : unsignedVal mem' le h LB = E)
    (hth : unsignedVal mem' th h LB = θ % capacity h LB)
    (hk : unsignedVal mem' k2 h LB = 2 * H % capacity h LB) (hE1 : 1 ≤ E) (hH : 1 ≤ H)
    (hhL : 2 ≤ h * Lw) (hLw : Lw ≤ LB)
    (hfitN : 2 * A + 2 * H * E < capacity h LB) (hfitY : 2 * (θ * E) < capacity h Lw)
    (hE2 : 2 * E < capacity h Lw) :
    Valid mem' numOut h Lw ∧ Valid mem' denOut h Lw ∧
    1 ≤ intVal mem' numOut h Lw ∧ 1 ≤ intVal mem' denOut h Lw ∧
    (intVal mem' numOut h Lw : ℝ) / (intVal mem' denOut h Lw : ℝ) =
      (if (θ : ℝ) ≤ ((2 * H * E + 2 * A : ℕ) : ℝ) / E then 1
        else ((2 * H * E + 2 * A : ℕ) : ℝ) / E) ∧
    ret = if (θ : ℝ) ≤ ((2 * H * E + 2 * A : ℕ) : ℝ) / E then 1 else 0 := by
  obtain ⟨hvn, hvd, hlt, hge⟩ := hO
  rw [hA, hE, hth, hk] at hlt hge
  have hcLw : capacity h Lw ≤ capacity h LB := by
    unfold capacity
    exact Nat.pow_le_pow_right (base_pos h) hLw
  have hc4 : 4 ≤ capacity h Lw := by
    unfold capacity base
    rw [← pow_mul]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (h * Lw) := Nat.pow_le_pow_right (by norm_num) hhL
  have hθc : θ < capacity h LB := by
    rcases Nat.eq_zero_or_pos θ with h0 | hpos
    · rw [h0]; exact capacity_pos h LB
    · have : θ ≤ θ * E := Nat.le_mul_of_pos_right _ (by omega)
      omega
  have h2H : 2 * H < capacity h LB := by
    have : 2 * H ≤ 2 * H * E := Nat.le_mul_of_pos_right _ (by omega)
    omega
  rw [Nat.mod_eq_of_lt hθc, Nat.mod_eq_of_lt h2H, Nat.mod_eq_of_lt (by omega : θ * E <
    capacity h LB), wstrNumVal_eq (by omega)] at hlt hge
  have hEpos : (0 : ℝ) < E := by exact_mod_cast hE1
  have hiff : (θ : ℝ) ≤ ((2 * H * E + 2 * A : ℕ) : ℝ) / E ↔ θ * E ≤ 2 * A + 2 * H * E := by
    rw [le_div_iff₀ hEpos]
    constructor
    · intro h'
      have : ((θ * E : ℕ) : ℝ) ≤ ((2 * A + 2 * H * E : ℕ) : ℝ) := by
        push_cast at h' ⊢; linarith
      exact_mod_cast this
    · intro h'
      have : ((θ * E : ℕ) : ℝ) ≤ ((2 * A + 2 * H * E : ℕ) : ℝ) := by exact_mod_cast h'
      push_cast at this ⊢; linarith
  by_cases hNY : 2 * A + 2 * H * E < θ * E
  · obtain ⟨hr, hun, hud⟩ := hlt hNY
    have hN : 2 * A + 2 * H * E < capacity h Lw := by omega
    rw [Nat.mod_eq_of_lt hN] at hun
    rw [Nat.mod_eq_of_lt (by omega : E < capacity h Lw)] at hud
    have hin := intVal_of_lt_half (show 2 * unsignedVal mem' numOut h Lw < capacity h Lw by omega)
    have hid := intVal_of_lt_half (show 2 * unsignedVal mem' denOut h Lw < capacity h Lw by omega)
    have hHE : 1 ≤ 2 * H * E := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hnot : ¬ (θ : ℝ) ≤ ((2 * H * E + 2 * A : ℕ) : ℝ) / E := fun h' => by
      have := hiff.mp h'; omega
    refine ⟨hvn, hvd, by rw [hin, hun]; exact_mod_cast (show 1 ≤ 2 * A + 2 * H * E by omega),
      by rw [hid, hud]; exact_mod_cast hE1,
      ?_, ?_⟩
    · rw [if_neg hnot, hin, hid, hun, hud]
      push_cast; ring_nf
    · rw [if_neg hnot]; exact hr
  · obtain ⟨hr, hun, hud⟩ := hge hNY
    rw [Nat.mod_eq_of_lt (by omega : 1 < capacity h Lw)] at hun hud
    have hin := intVal_of_lt_half (show 2 * unsignedVal mem' numOut h Lw < capacity h Lw by omega)
    have hid := intVal_of_lt_half (show 2 * unsignedVal mem' denOut h Lw < capacity h Lw by omega)
    have hyes : (θ : ℝ) ≤ ((2 * H * E + 2 * A : ℕ) : ℝ) / E := hiff.mpr (by omega)
    refine ⟨hvn, hvd, by rw [hin, hun]; norm_num, by rw [hid, hud]; norm_num, ?_, ?_⟩
    · rw [if_pos hyes, hin, hid, hun, hud]; norm_num
    · rw [if_pos hyes]; exact hr

/-- The raw stretch as a sum of level distances. Here `H = hldDepthBound |V(T)| + 1` is the
number of levels. -/
lemma levelStretchBound_eq {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) (π : ℕ → ℕ)
    (G : MGraph) (ℓ : ℕ → ℝ) {e : ℕ} (hu : G.tail e ∈ T.V) (hv : G.head e ∈ T.V) :
    levelStretchBound T r π G ℓ e =
      2 * ((hldDepthBound T.V.card + 1 : ℕ) : ℝ) +
        2 * (∑ j ∈ Finset.range (hldDepthBound T.V.card + 1),
          levelDist T r (levelRoots T r j) π ℓ (G.tail e) (G.head e)) / ℓ e := by
  unfold levelStretchBound hldDepthBound
  dsimp only
  have hstep : ∀ j, (rootedForestGivenRoots T r (levelRoots T r j) π).stretch G ℓ e =
      1 + levelDist T r (levelRoots T r j) π ℓ (G.tail e) (G.head e) / ℓ e := fun j =>
    stretch_eq_levelDist hT (upClosure_levelRoots hT ▸ upClosure_isBranchFree hT levelRoots_subset)
      (root_mem_levelRoots hT) π G ℓ hu hv
  simp only [hstep, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, ← Finset.sum_div]
  push_cast
  ring

/-- The stretch of edge position `t` after `wstrProc`. The tree `T₀` is given by the index arrays
(`TreeIdx`, with the parents and parent edges in memory), the `T_H` depths are at `thDepPtr`, the
order `π` is at `piPtr` on tree indices, and the lengths are `S` times the model's `ℓ`. The bound
`M` on the scaled weighted depths keeps all blocks below the capacity. -/
theorem wstr_bridge {w h C : ℕ} {mem mem' : ℕ → ℕ}
    {n tM m0 k LB Lw Lin nOrig r logCap lenArr fidPtr qPtr parPtr pePtr piPtr thDepPtr euPtr evPtr
     upPtr depPtr eList numPtr denPtr idPtr ltBase ldBase duvBase inRPtr mpPtr ownPtr rtPtr dRBase
     accBase leBase k2Out thOut tA tB tF tmp1 tmp2 highPtr : ℕ}
    {T₀ G : MGraph} {vList : List ℕ} {fid tl hd dep π : ℕ → ℕ} {ℓ : ℕ → ℝ} {S M : ℕ}
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
    (hhL : 2 ≤ h * Lw) (hS : 0 < S)
    {t : ℕ} (ht : t < m0)
    (htail : vList.getD (mem (euPtr + t)) 0 = G.tail (mem (eList + t)))
    (hhead : vList.getD (mem (evPtr + t)) 0 = G.head (mem (eList + t)))
    (hE : (unsignedVal mem (lenArr + mem (eList + t) * Lin) h Lin : ℝ) = S * ℓ (mem (eList + t)))
    (hE1 : 1 ≤ unsignedVal mem (lenArr + mem (eList + t) * Lin) h Lin)
    (hE2 : 2 * unsignedVal mem (lenArr + mem (eList + t) * Lin) h Lin < capacity h Lin)
    (hfitN : 2 * (4 * M * (hldDepthBound n + 1)) +
      2 * (hldDepthBound n + 1) * unsignedVal mem (lenArr + mem (eList + t) * Lin) h Lin <
        capacity h LB)
    (hθ : threshProd C n k < 2 ^ (h * (Lw - Lin))) :
    let raw := levelStretchBound T₀ (vList.getD r 0) π G ℓ (mem (eList + t))
    let e := mem (eList + t)
    Valid mem' (numPtr + e * Lw) h Lw ∧ Valid mem' (denPtr + e * Lw) h Lw ∧
    1 ≤ intVal mem' (numPtr + e * Lw) h Lw ∧ 1 ≤ intVal mem' (denPtr + e * Lw) h Lw ∧
    (intVal mem' (numPtr + e * Lw) h Lw : ℝ) / (intVal mem' (denPtr + e * Lw) h Lw : ℝ) =
      (if (threshProd C n k : ℝ) ≤ raw then 1 else raw) ∧
    mem' (highPtr + t) = if (threshProd C n k : ℝ) ≤ raw then 1 else 0 := by
  intro raw e
  obtain ⟨h16, hn, hLin1, hLinw, hLwB, hnO, hr, hC, hHw, hn2, -, hth0, hlenT, hlenE, hlen0, heuv,
    ⟨eCap, heC, heInj, hnd, hdi⟩, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, L12, L13, L14,
    L15, L16, L17, L18, L19, L20, L21, L22, L23, L24, L25, L26, L27, L28, L29, L30⟩ := hpre
  obtain ⟨mem₀, hlow, ⟨hid₀, hlt₀, hld₀, ⟨hroot₀, hrule₀⟩, hduvV₀, hduvF₀, hacc₀⟩,
    ⟨rts, lxs, hrts, hlxs, hacc⟩, hle, hth, hk2, -, -, hout⟩ := hpost
  subst hnl
  set H := hldDepthBound vList.length + 1 with hH
  have hH1 : 1 ≤ H := by omega
  have hnum : numPtr ≤ idPtr := by omega
  have hpar : ∀ x < vList.length, mem (parPtr + x) = mem₀ (parPtr + x) := fun x hx =>
    (hlow _ (by omega)).symm
  have hpe : ∀ x < vList.length, mem (pePtr + x) = mem₀ (pePtr + x) := fun x hx =>
    (hlow _ (by omega)).symm
  have hR₀ := hI.hR.congr hI.hr hpar hpe (fun _ _ => rfl)
  have hI₀ : TreeIdx T₀ vList tM r fid tl hd (fun x => mem₀ (parPtr + x))
      (fun x => mem₀ (pePtr + x)) dep := ⟨hI.hT, hI.hA, hI.hnd, hI.hV, hR₀, hI.hr⟩
  have hLT₀ : LcaTables w vList.length logCap upPtr depPtr parPtr (fun x => mem₀ (parPtr + x))
      dep mem₀ :=
    (hLT.of_agree (B := idPtr) hlow (by omega) (by omega) (by omega)).congr hI.hR hpar
      (fun _ _ => rfl)
  have hMc : M < capacity h LB := by
    have : M ≤ 4 * M * (H + 1) := by
      calc M ≤ 4 * M := by omega
        _ ≤ 4 * M * (H + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hLd : ∀ z < vList.length, (unsignedVal mem₀ (ldBase + z * LB) h LB : ℝ) =
      S * wDepth T₀ (vList.getD r 0) ℓ (vList.getD z 0) :=
    ld_bridge hI₀ (lt := fun i => unsignedVal mem₀ (ltBase + i * LB) h LB)
      (Ld := fun y => unsignedVal mem₀ (ldBase + y * LB) h LB) hroot₀ hrule₀
      (fun i hi => by rw [(hlt₀ i hi).2]; exact hlt i hi)
      (fun x hx => lt_of_le_of_lt (hM x hx) (by exact_mod_cast hMc))
  have hMn : ∀ z < vList.length, unsignedVal mem₀ (ldBase + z * LB) h LB ≤ M := by
    intro z hz
    have h1 : ((unsignedVal mem₀ (ldBase + z * LB) h LB : ℕ) : ℝ) ≤ (M : ℝ) := by
      rw [hLd z hz]; exact hM z hz
    exact_mod_cast h1
  have hthd₀ : ∀ x < vList.length, mem₀ (thDepPtr + x) =
      depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0) := fun x hx => by
    rw [hlow _ (by omega)]; exact hthd x hx
  have hpiv₀ : ∀ j < tM, π (fid j) = mem₀ (piPtr + j) := fun j hj => by
    rw [hlow _ (by omega)]; exact hpiv j hj
  have hlxs' := hlxs tl hd dep hR₀ hLT₀
  have heu₀ : mem₀ (euPtr + t) = mem (euPtr + t) := hlow _ (by omega)
  have hev₀ : mem₀ (evPtr + t) = mem (evPtr + t) := hlow _ (by omega)
  have hu : mem₀ (euPtr + t) < vList.length := by rw [heu₀]; exact (heuv t ht).1
  have hv : mem₀ (evPtr + t) < vList.length := by rw [hev₀]; exact (heuv t ht).2
  obtain ⟨l, hl, hlca, hdv⟩ := hduvF₀ tM r tl hd _ _ dep hR₀ hLT₀ t ht
  have hfit : unsignedVal mem₀ (ldBase + mem₀ (euPtr + t) * LB) h LB +
      unsignedVal mem₀ (ldBase + mem₀ (evPtr + t) * LB) h LB < capacity h LB := by
    have := hMn _ hu
    have := hMn _ hv
    have : 2 * M ≤ 4 * M * (H + 1) := by
      calc 2 * M ≤ 4 * M := by omega
        _ ≤ 4 * M * (H + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hduv : (unsignedVal mem₀ (duvBase + t * LB) h LB : ℝ) = S * walkLength ℓ
      (T₀.forestPath (vList.getD (mem₀ (euPtr + t)) 0) (vList.getD (mem₀ (evPtr + t)) 0)) := by
    rw [hdv]
    exact treeDist_bridge hI₀ (Ld := fun z => unsignedVal mem₀ (ldBase + z * LB) h LB) hℓT hLd
      hl hu hv hlca hfit
  have hduvM : unsignedVal mem₀ (duvBase + t * LB) h LB ≤ 2 * M := by
    have hw := walkLength_le_wDepth_add hI.hT hℓT (hI.getD_mem hu) (hI.getD_mem hv) (ℓ := ℓ)
    have h1 : ((unsignedVal mem₀ (duvBase + t * LB) h LB : ℕ) : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by
      rw [hduv]
      have hSn : (0 : ℝ) ≤ S := Nat.cast_nonneg _
      have := hM _ hu
      have := hM _ hv
      push_cast
      nlinarith
    exact_mod_cast h1
  obtain ⟨hAle, hAeq⟩ := accFold_bridge hI₀ hℓT hthd₀ hπ hpiv₀ hLd hMn hrts hlxs' hu hv hduv
    hduvM (hacc₀ t ht).2 hcap H le_rfl
  set A := accFold h LB mem₀ euPtr evPtr ldBase duvBase accBase rts lxs t H with hAdef
  set E := unsignedVal mem (lenArr + mem (eList + t) * Lin) h Lin with hEdef
  have hcLw : capacity h Lw = capacity h Lin * 2 ^ (h * (Lw - Lin)) := by
    have h1 : capacity h Lw = capacity h Lin * capacity h (Lw - Lin) := by
      rw [← capacity_add, Nat.add_sub_cancel' hLinw]
    have h2 : capacity h (Lw - Lin) = 2 ^ (h * (Lw - Lin)) := by
      unfold capacity base; rw [← pow_mul]
    rw [h1, h2]
  have hfitY : 2 * (threshProd C vList.length k * E) < capacity h Lw := by
    rw [hcLw, show 2 * (threshProd C vList.length k * E) = threshProd C vList.length k * (2 * E)
      by ring, mul_comm (capacity h Lin)]
    exact Nat.mul_lt_mul'' hθ hE2
  have hE2' : 2 * E < capacity h Lw := by
    rw [hcLw]
    have : 1 ≤ 2 ^ (h * (Lw - Lin)) := Nat.one_le_two_pow
    calc 2 * E < capacity h Lin := hE2
      _ ≤ capacity h Lin * 2 ^ (h * (Lw - Lin)) := Nat.le_mul_of_pos_right _ (by omega)
  have hfitN' : 2 * A + 2 * H * E < capacity h LB := by
    have h1 := hAle
    have h2 := hfitN
    omega
  have hval := wstrEdgeOut_value (hout t ht) (hacc t ht) (hle t ht) hth hk2 hE1 hH1 hhL hLwB
    hfitN' hfitY hE2'
  have hraw : raw = ((2 * H * E + 2 * A : ℕ) : ℝ) / E := by
    have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
    have hEpos : (0 : ℝ) < E := by exact_mod_cast hE1
    have htail' : G.tail e = vList.getD (mem₀ (euPtr + t)) 0 := by rw [heu₀, htail]
    have hhead' : G.head e = vList.getD (mem₀ (evPtr + t)) 0 := by rw [hev₀, hhead]
    have hsum : ∑ j ∈ Finset.range H, levelDist T₀ (vList.getD r 0)
        (levelRoots T₀ (vList.getD r 0) j) π ℓ (vList.getD (mem₀ (euPtr + t)) 0)
        (vList.getD (mem₀ (evPtr + t)) 0) = (A : ℝ) / S := by
      rw [hAeq]; field_simp
    have hℓe : ℓ e = (E : ℝ) / S := by
      show ℓ (mem (eList + t)) = _
      rw [hE]; field_simp
    show levelStretchBound T₀ (vList.getD r 0) π G ℓ e = _
    rw [levelStretchBound_eq hI.hT π G ℓ (by rw [htail']; exact hI.getD_mem hu)
      (by rw [hhead']; exact hI.getD_mem hv), hI.card_V, htail', hhead', hsum, hℓe]
    field_simp
    simp only [hH]
    push_cast
    ring
  rw [hraw]
  exact hval

end MinCostFlow.LSF.Program
