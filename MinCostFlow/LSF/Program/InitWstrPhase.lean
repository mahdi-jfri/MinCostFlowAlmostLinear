module

public import MinCostFlow.LSF.Program.InitWstr
public import MinCostFlow.LSF.Program.DecompPhasePre
public import MinCostFlow.LSF.Program.OrderPhasePre

/-!
# The stretches after the decomposition phase

`wstrAt_of_bridge` asks for a bound `M` on the scaled weighted depths of the tree and for a
block width `LB` with room for `4 M (D + 2)`. Here we choose `M = n · 2^(h L_in)`. Every tree edge
has a scaled length below `2^(h L_in)` (it is a length block, or `0` for an edge that is not an
edge of `G`), and a path to the root has fewer than `n` edges, so `M` bounds the depths
(`scaled_wDepth_le`). The width `wstrLB` of the decomposition phase has room for `16 (n + 1) (D + 2)`
numbers below `2^(h L_w)` (`wstrLB_cap`), which gives the two width bounds (`wstr_fit_bounds`).

`decompPhase_wstrAt` then reads the posts of the decomposition phase: the arrays at the static
places `numSt` and `denSt` represent the stretches `initWstr` after the two copies at its end.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- The scaled weighted depth of a vertex is at most the number of tree edges times a bound on
the scaled length of one tree edge. -/
lemma scaled_wDepth_le {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) {ℓ : ℕ → ℝ} {S c : ℝ}
    (hS : 0 ≤ S) (hℓ : ∀ f ∈ T.E, 0 ≤ ℓ f) (hc : ∀ f ∈ T.E, S * ℓ f ≤ c) {x : ℕ}
    (hx : x ∈ T.V) : S * wDepth T r ℓ x ≤ T.E.card * c := by
  unfold wDepth
  rw [walkLength_forestPath_eq_sum hT ℓ hx hT.2]
  have hsub : walkEdges (T.forestPath x r) ⊆ T.E := fun _ hf =>
    walkEdges_forestPath_sub_edges hT.isForest hf
  calc S * ∑ e ∈ walkEdges (T.forestPath x r), ℓ e ≤ S * ∑ e ∈ T.E, ℓ e :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun f hf _ => hℓ f hf) hS
    _ = ∑ e ∈ T.E, S * ℓ e := Finset.mul_sum _ _ _
    _ ≤ ∑ _e ∈ T.E, c := Finset.sum_le_sum hc
    _ = T.E.card * c := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The two width bounds of the stretch pass, for `M = n c` with `c ≤ P`. -/
lemma wstr_fit_bounds {n D c P X len : ℕ} (hc : c ≤ P) (hX : 16 * (n + 1) * (D + 2) * P ≤ X)
    (hlen : len < c) :
    4 * (n * c) * (D + 1 + 1) < X ∧ 2 * (4 * (n * c) * (D + 1)) + 2 * (D + 1) * len < X := by
  have hP : 0 < P := by omega
  have h1 : n * c ≤ n * P := Nat.mul_le_mul_left _ hc
  have h2 : len ≤ P := by omega
  have hA : 4 * (n * c) * (D + 2) ≤ 4 * (n * P) * (D + 2) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
  have hY : 0 < (D + 2) * P := Nat.mul_pos (by omega) hP
  have hZ : (D + 1) * P ≤ (D + 2) * P := Nat.mul_le_mul_right _ (by omega)
  have hB : 4 * (n * P) * (D + 2) < 16 * (n + 1) * (D + 2) * P := by
    have e1 : 4 * (n * P) * (D + 2) = (4 * n) * ((D + 2) * P) := by ring
    have e2 : 16 * (n + 1) * (D + 2) * P = (16 * (n + 1)) * ((D + 2) * P) := by ring
    rw [e1, e2]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hY
  have hC : 2 * (4 * (n * c) * (D + 1)) + 2 * (D + 1) * len ≤
      (8 * n + 2) * ((D + 2) * P) := by
    have : 4 * (n * c) * (D + 1) ≤ 4 * n * ((D + 1) * P) := by
      have := Nat.mul_le_mul_right (D + 1) (Nat.mul_le_mul_left 4 h1)
      calc 4 * (n * c) * (D + 1) ≤ 4 * (n * P) * (D + 1) := this
        _ = 4 * n * ((D + 1) * P) := by ring
    have : 2 * (D + 1) * len ≤ 2 * ((D + 1) * P) := by
      calc 2 * (D + 1) * len ≤ 2 * (D + 1) * P := Nat.mul_le_mul_left _ h2
        _ = 2 * ((D + 1) * P) := by ring
    have : 4 * n * ((D + 1) * P) ≤ 4 * n * ((D + 2) * P) := Nat.mul_le_mul_left _ hZ
    have e3 : (8 * n + 2) * ((D + 2) * P) = 2 * (4 * n * ((D + 2) * P)) + 2 * ((D + 2) * P) := by
      ring
    omega
  have hD : (8 * n + 2) * ((D + 2) * P) < 16 * (n + 1) * (D + 2) * P := by
    have e2 : 16 * (n + 1) * (D + 2) * P = (16 * (n + 1)) * ((D + 2) * P) := by ring
    rw [e2]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hY
  refine ⟨?_, by omega⟩
  rw [show D + 1 + 1 = D + 2 by omega]
  omega

/-- `capacity h L` is `2 ^ (h L)`. -/
lemma capacity_eq_pow (h L : ℕ) : capacity h L = 2 ^ (h * L) := by
  rw [capacity, base, ← pow_mul]

set_option maxHeartbeats 1600000 in
/-- After the decomposition phase, the arrays at `numSt` and `denSt` represent the stretches
`initWstr` of every edge of `G`. Here `mem` is the memory at the start of the phase, `ℓ` the
lengths of the model and `S` their scale; the edge list of the graph block holds every edge of
`G` once, with its ends in `eu` and `ev`. -/
theorem decompPhase_wstrAt {w h C : ℕ} {T₀ G : MGraph} {vList : List ℕ} {X : DecompLayout}
    {mem m₁ m₃ m₄ m₅ m₆ m₇ m₈ : ℕ → ℕ} {v₁ v₄ v₅ v₆ : ℕ}
    {π : ℕ → ℕ} {ℓ : ℕ → ℝ} {S : ℕ} {thresh : ℝ}
    (I : DecompPhaseIn w h C T₀ vList X mem)
    (h₁ : (decompWTContract w).post [X.n, X.m0, X.eu, X.ev, X.qOrd, X.auxPar, 0, X.θ, X.dBase] mem
      v₁ m₁)
    (h₃ : (wstrStageContract w h C).post [X.n, X.tM, X.m0, X.k, wstrLB X.n X.D X.Lw, X.Lw, X.Lin,
      X.nOrig, 0, X.logCap, X.lenArr, tOrigIdBase X.tPtr X.vCap X.tM, X.qOrd, X.auxPar,
      X.auxPar + X.n, tPiBase X.tPtr X.vCap X.tM, X.thBase + 7 * X.n, X.eu, X.ev,
      X.auxPar + 3 * X.n, X.auxPar + X.n + X.n, dgEListBase X.gPtr X.vCap X.eCap, X.numS,
      X.denS, X.idPtr] m₁ (wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18) m₃)
    (h₄ : (memCopyContract w).post [X.hiCopy, wsPt X.idPtr X.n X.tM X.m0 (wstrLB X.n X.D X.Lw) 18,
      X.m0] m₃ v₄ m₄)
    (h₅ : (flagMergeContract w).post [X.n, X.cnt, X.m0, X.dBase + 11 * X.n, X.repPtr, X.vIdx,
      X.hiCopy, X.eu, X.ev, X.inR] m₄ v₅ m₅)
    (h₆ : (rootsStageContract w).post [X.n, X.tM, 0, X.qOrd, X.auxPar, X.auxPar + X.n,
      tPiBase X.tPtr X.vCap X.tM, X.thDst, X.thBase + 7 * X.n, X.D, X.inR, X.inR + X.n,
      X.inR + X.n + X.n, X.inR + X.n + X.n + X.tM] m₅ v₆ m₆)
    (h₇ : wstrCopyEdgesPost X.numSt X.numS (dgEListBase X.gPtr X.vCap X.eCap) X.m0 X.Lw
      (X.eCap * X.Lw) m₆ m₇)
    (h₈ : wstrCopyEdgesPost X.denSt X.denS (dgEListBase X.gPtr X.vCap X.eCap) X.m0 X.Lw
      (X.eCap * X.Lw) m₇ m₈)
    (hπ : IsEdgeOrder T₀ π)
    (hpiv : ∀ j < X.tM, π (mem (tOrigIdBase X.tPtr X.vCap X.tM + j)) =
      mem (tPiBase X.tPtr X.vCap X.tM + j))
    (hℓT : ∀ f ∈ T₀.E, 0 ≤ ℓ f)
    (hlt : ∀ i < X.tM, (blkExtVal h mem X.lenArr (tOrigIdBase X.tPtr X.vCap X.tM) X.Lin X.nOrig i
      : ℝ) = S * ℓ (mem (tOrigIdBase X.tPtr X.vCap X.tM + i)))
    (hhL : 2 ≤ h * X.Lw) (hS : 0 < S)
    (heL : ∀ e ∈ G.E, ∃ t < X.m0, mem (dgEListBase X.gPtr X.vCap X.eCap + t) = e)
    (htail : ∀ t < X.m0, vList.getD (mem (X.eu + t)) 0 =
      G.tail (mem (dgEListBase X.gPtr X.vCap X.eCap + t)))
    (hhead : ∀ t < X.m0, vList.getD (mem (X.ev + t)) 0 =
      G.head (mem (dgEListBase X.gPtr X.vCap X.eCap + t)))
    (hE : ∀ t < X.m0, (unsignedVal mem (X.lenArr + mem (dgEListBase X.gPtr X.vCap X.eCap + t) *
      X.Lin) h X.Lin : ℝ) = S * ℓ (mem (dgEListBase X.gPtr X.vCap X.eCap + t)))
    (hE1 : ∀ t < X.m0,
      1 ≤ unsignedVal mem (X.lenArr + mem (dgEListBase X.gPtr X.vCap X.eCap + t) * X.Lin) h X.Lin)
    (hE2 : ∀ t < X.m0, 2 * unsignedVal mem (X.lenArr + mem (dgEListBase X.gPtr X.vCap X.eCap + t) *
      X.Lin) h X.Lin < capacity h X.Lin)
    (hθ : threshProd C X.n X.k < 2 ^ (h * (X.Lw - X.Lin)))
    (hthr : (threshProd C X.n X.k : ℝ) = thresh) :
    WstrAt m₈ X.numSt X.denSt X.eCap h X.Lw G (initWstr T₀ G (vList.getD 0 0) π ℓ thresh) ∧
    ∀ t < X.m0, m₈ (X.hiCopy + t) =
      if thresh ≤ levelStretchBound T₀ (vList.getD 0 0) π G ℓ
        (mem (dgEListBase X.gPtr X.vCap X.eCap + t)) then 1 else 0 := by
  have hn := I.hn
  have L2 := I.L2; have L3 := I.L3; have L4 := I.L4; have L5 := I.L5
  have L7 := I.L7; have L8 := I.L8; have L10 := I.L10
  have L13 := I.L13; have L14 := I.L14; have L15 := I.L15; have L16 := I.L16; have L17 := I.L17
  have L18 := I.L18
  have hden : X.denS = X.numS + X.eCap * X.Lw := rfl
  set LB := wstrLB X.n X.D X.Lw with hLBdef
  have hp18 := wsPt_mono X.idPtr X.n X.tM X.m0 LB (Nat.zero_le 18)
  have hp0 : wsPt X.idPtr X.n X.tM X.m0 LB 0 = X.idPtr := rfl
  rw [hp0] at hp18
  -- the frame of the first call
  obtain ⟨_, _, _, _, _, _, _, _, _, heq₁, -, hfr₁, -⟩ := h₁
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  have hag : ∀ a, a < X.dBase → m₁ a = mem a := fun a ha => hfr₁ a (Or.inl ha)
  -- the pre and the post of the stretch pass
  have hpre₀ := (decompPhase_wstrPre I hag).2.2
  rw [wstrStageArgs_eq] at hpre₀
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, heqP, hpre⟩ := hpre₀
  simp only [List.cons.injEq, and_true] at heqP
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := heqP
  obtain ⟨-, hW⟩ := h₃
  rw [wstrStageArgs_eq] at hW
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, heqW, hpost⟩ := hW
  simp only [List.cons.injEq, and_true] at heqW
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := heqW
  -- the tree arrays on `m₁`
  obtain ⟨Q, tl, hd, dep, hQ, hQat, hRA, hLT, hTA⟩ := I.htree
  obtain ⟨-, -, hRA₁, hLT₁⟩ := treeIn_transfer (B := X.dBase) (mem' := m₁) hn hQ hQat hRA hLT
    hag (by have := I.L6; omega) (by omega) (by omega) (by omega) (by omega)
  have hfid : ∀ i < X.tM, mem (tOrigIdBase X.tPtr X.vCap X.tM + i) =
      m₁ (tOrigIdBase X.tPtr X.vCap X.tM + i) := fun i hi => (hag _ (by omega)).symm
  have hI : TreeIdx T₀ vList X.tM 0 (fun i => m₁ (tOrigIdBase X.tPtr X.vCap X.tM + i)) tl hd
      (fun x => m₁ (X.auxPar + x)) (fun x => m₁ (X.auxPar + X.n + x)) dep :=
    ⟨I.hT, hTA.congr hfid (fun _ _ => rfl) (fun _ _ => rfl), I.hnd, I.hV,
      by rw [I.hvlen]; exact hRA₁, by rw [I.hvlen]; exact hn⟩
  -- the lengths of the tree edges
  have hlenT : ∀ i < X.tM, blkExtVal h m₁ X.lenArr (tOrigIdBase X.tPtr X.vCap X.tM) X.Lin X.nOrig i
      = blkExtVal h mem X.lenArr (tOrigIdBase X.tPtr X.vCap X.tM) X.Lin X.nOrig i := by
    intro i hi
    unfold blkExtVal
    split_ifs with hio
    · obtain ⟨-, hle⟩ := I.hlenT i hio
      have hLwB : X.Lin ≤ LB := le_trans I.hLinw (lw_le_wstrLB _ _ _)
      rw [← hfid i hi]
      exact unsignedVal_congr fun j hj => hag _ (by omega)
    · rfl
  have hcapT : ∀ i < X.tM,
      blkExtVal h mem X.lenArr (tOrigIdBase X.tPtr X.vCap X.tM) X.Lin X.nOrig i <
        capacity h X.Lin := by
    intro i hi
    unfold blkExtVal
    split_ifs with hio
    · exact unsignedVal_lt (I.hlenT i hio).1
    · rw [capacity, base]; positivity
  -- the bound on the depths
  set c := capacity h X.Lin with hc
  have hcard : T₀.E.card ≤ X.n := by
    have h1 : T₀.E.card + 1 = T₀.V.card := spanningTree_edge_card I.hT.1 ⟨_, I.hT.2⟩
    have h2 : T₀.V ⊆ vList.toFinset := fun v hv => List.mem_toFinset.mpr ((I.hV v).mp hv)
    have h3 := Finset.card_le_card h2
    have h4 := List.toFinset_card_le vList
    rw [I.hvlen] at h4
    omega
  have hM : ∀ x < X.n, (S : ℝ) * wDepth T₀ (vList.getD 0 0) ℓ (vList.getD x 0) ≤
      ((X.n * c : ℕ) : ℝ) := by
    intro x hx
    have hxV : vList.getD x 0 ∈ T₀.V := hI.getD_mem (by rw [I.hvlen]; exact hx)
    have hle := scaled_wDepth_le (S := (S : ℝ)) (c := (c : ℝ)) I.hT (Nat.cast_nonneg _) hℓT
      (fun f hf => by
        obtain ⟨i, hi, rfl⟩ := hTA.fid_cover f hf
        rw [← hlt i hi]
        exact_mod_cast (hcapT i hi).le) hxV
    calc (S : ℝ) * wDepth T₀ (vList.getD 0 0) ℓ (vList.getD x 0) ≤ T₀.E.card * c := hle
      _ ≤ X.n * c := by
        have : (T₀.E.card : ℝ) ≤ X.n := by exact_mod_cast hcard
        gcongr
      _ = ((X.n * c : ℕ) : ℝ) := by push_cast; ring
  -- the widths
  have hcP : c ≤ 2 ^ (h * X.Lw) := by
    rw [hc, capacity_eq_pow]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ I.hLinw)
  have hX : 16 * (X.n + 1) * (hldDepthBound X.n + 2) * 2 ^ (h * X.Lw) ≤ capacity h LB := by
    rw [capacity_eq_pow, hLBdef, I.hD]
    exact wstrLB_cap (le_trans I.hh le_rfl)
  have hfit := fun t (ht : t < X.m0) => wstr_fit_bounds hcP hX (len :=
    unsignedVal m₁ (X.lenArr + m₁ (dgEListBase X.gPtr X.vCap X.eCap + t) * X.Lin) h X.Lin)
    (by
      have h2 := hE2 t ht
      have h1 := hE1 t ht
      rw [hag _ (by omega)]
      obtain ⟨-, hle⟩ := I.hlenE t ht
      have hLwB : X.Lin ≤ LB := le_trans I.hLinw (lw_le_wstrLB _ _ _)
      rw [unsignedVal_congr (mem' := mem) (a' := X.lenArr + mem (dgEListBase X.gPtr X.vCap X.eCap
        + t) * X.Lin) fun j hj => hag _ (by omega)]
      omega)
  have hcap : 4 * (X.n * c) * (hldDepthBound X.n + 1 + 1) < capacity h LB := by
    rcases Nat.eq_zero_or_pos X.m0 with h0 | h0
    · obtain ⟨hA, -⟩ := wstr_fit_bounds hcP hX (len := 0) (by rw [hc, capacity_eq_pow]; positivity)
      exact hA
    · exact (hfit 0 h0).1
  -- the edge facts on `m₁`
  have heL₁ : ∀ t < X.m0, m₁ (dgEListBase X.gPtr X.vCap X.eCap + t) =
      mem (dgEListBase X.gPtr X.vCap X.eCap + t) := fun t ht => hag _ (by omega)
  have hlenE₁ : ∀ t < X.m0,
      unsignedVal m₁ (X.lenArr + m₁ (dgEListBase X.gPtr X.vCap X.eCap + t) * X.Lin) h X.Lin =
      unsignedVal mem (X.lenArr + mem (dgEListBase X.gPtr X.vCap X.eCap + t) * X.Lin) h X.Lin := by
    intro t ht
    obtain ⟨-, hle⟩ := I.hlenE t ht
    have hLwB : X.Lin ≤ LB := le_trans I.hLinw (lw_le_wstrLB _ _ _)
    rw [heL₁ t ht]
    exact unsignedVal_congr fun j hj => hag _ (by omega)
  have hW3 := wstrAt_of_bridge (G := G) (π := π) (ℓ := ℓ) (S := S) (M := X.n * c)
    (thresh := thresh) (eCap := X.eCap) hpre hpost.2 hI I.hvlen hLT₁
    (fun x hx => by rw [hag _ (by omega)]; exact I.hthDep x hx) hπ
    (fun j hj => by rw [← hfid j hj, hag _ (by omega)]; exact hpiv j hj) hℓT
    (fun i hi => by rw [hlenT i hi, hlt i hi, hfid i hi]) hM hcap hhL
    (by have := I.hLin1; have := I.hLinw; omega) hS
    (fun e he => by
      obtain ⟨t, ht, rfl⟩ := heL e he
      exact ⟨t, ht, heL₁ t ht⟩)
    (fun e he => by
      obtain ⟨t, ht, rfl⟩ := heL e he
      exact I.heLt t ht)
    (fun t ht => by rw [hag _ (by omega), heL₁ t ht]; exact htail t ht)
    (fun t ht => by rw [hag _ (by omega), heL₁ t ht]; exact hhead t ht)
    (fun t ht => by rw [hlenE₁ t ht, heL₁ t ht]; exact hE t ht)
    (fun t ht => by rw [hlenE₁ t ht]; exact hE1 t ht)
    (fun t ht => by rw [hlenE₁ t ht]; exact hE2 t ht)
    (fun t ht => (hfit t ht).2) hθ hthr
  -- the copies
  obtain ⟨_, _, _, heq₄, -, hcp₄, hfr₄⟩ := h₄
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl⟩ := heq₄
  obtain ⟨_, _, _, _, _, _, _, _, _, _, heq₅, -, hfr₅, -⟩ := h₅
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, heq₆, -, hfr₆, -⟩ := h₆
  simp only [List.cons.injEq, and_true] at heq₆
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₆
  obtain ⟨hcp₇, hfr₇⟩ := h₇
  obtain ⟨hcp₈, hfr₈⟩ := h₈
  have hm63 : ∀ a, X.numS ≤ a → m₆ a = m₃ a := by
    intro a ha
    rw [hfr₆ a (Or.inr (by omega)) (Or.inr (by omega)), hfr₅ a (Or.inr (by omega)),
      hfr₄ a (Or.inr (by omega))]
  obtain ⟨_, -, -, -, -, -, -, hfrW, -, -⟩ := hpost.2
  have hm60 : ∀ a < X.dBase, m₆ a = mem a := by
    intro a ha
    rw [hfr₆ a (Or.inl (by omega)) (Or.inl (by omega)), hfr₅ a (Or.inl (by omega)),
      hfr₄ a (Or.inl (by omega)),
      hfrW a (by omega) (fun t _ => ⟨Or.inl (by omega), Or.inl (by omega)⟩),
      hag a ha]
  have hm70 : ∀ t < X.m0, m₇ (dgEListBase X.gPtr X.vCap X.eCap + t) =
      mem (dgEListBase X.gPtr X.vCap X.eCap + t) := by
    intro t ht
    have hL4s := I.L4s
    rw [hfr₇ _ (Or.inl (by omega)), hm60 _ (by omega)]
  refine ⟨WstrAt.of_copy_edges hW3.1 (fun e he i hi => ?_) (fun e he i hi => ?_), fun t ht => ?_⟩
  rotate_left 2
  · rw [hfr₈ _ (Or.inr (by omega)), hfr₇ _ (Or.inr (by omega)),
      hfr₆ _ (Or.inl (by omega)) (Or.inl (by omega)), hfr₅ _ (Or.inl (by omega)), hcp₄ t ht,
      hW3.2 t ht, heL₁ t ht]
  · obtain ⟨t, ht, hte⟩ := heL e he
    have he_lt : e < X.eCap := hte ▸ I.heLt t ht
    have he_bd : e * X.Lw + i < X.eCap * X.Lw :=
      calc e * X.Lw + i < (e + 1) * X.Lw := by nlinarith
        _ ≤ X.eCap * X.Lw := Nat.mul_le_mul_right _ he_lt
    have hm6e : m₆ (dgEListBase X.gPtr X.vCap X.eCap + t) = e :=
      (hm60 _ (by omega)).trans hte
    rw [hfr₈ _ (Or.inl (by omega)), ← hm6e, hcp₇ t ht i hi, hm6e, hm63 _ (by omega)]
  · obtain ⟨t, ht, hte⟩ := heL e he
    have he_lt : e < X.eCap := hte ▸ I.heLt t ht
    have he_bd : e * X.Lw + i < X.eCap * X.Lw :=
      calc e * X.Lw + i < (e + 1) * X.Lw := by nlinarith
        _ ≤ X.eCap * X.Lw := Nat.mul_le_mul_right _ he_lt
    have hm7e : m₇ (dgEListBase X.gPtr X.vCap X.eCap + t) = e :=
      (hm70 t ht).trans hte
    rw [← hm7e, hcp₈ t ht i hi, hm7e, hfr₇ _ (Or.inr (by omega)), hm63 _ (by omega)]

end

end MinCostFlow.LSF.Program
