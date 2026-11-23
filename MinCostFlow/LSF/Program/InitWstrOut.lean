module

public import MinCostFlow.LSF.Program.InitWstrPhase
public import MinCostFlow.LSF.Program.InitWstrGlue

/-!
# The stretches of the initial state, from the order and decomposition phases

`order_decomp_wstrAt` gives `WstrAt` at the static places after the decomposition phase, for the
stretches `initWstr` of the model with the lengths `safeLen G₀ ℓ₀`, the root `vList[0]` and the
order `orderPi` of the order phase. It checks the inputs of `decompPhase_wstrAt` from the posts
of the order phase (`order_pi_idx`, `order_ends`, `order_tOrigId`) and from the length blocks.

A length block holds a positive fixed-point number, so its unsigned value `u` is at least `1`,
satisfies `2 u < capacity` (the sign bit is clear), and is `2^P` times the length
(`len_unsigned_facts`). Each tree edge at index `i` is an edge of `G₀` exactly when `i < nOrig`
(`OrderPhaseIn.hO`), so the scaled length that the stretch pass reads for it is `2^P` times
`safeLen G₀ ℓ₀`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- A block that holds a positive fixed-point number `ℓ` at precision `P` has an unsigned value
`u` with `1 ≤ u`, `2 u < capacity h L` and `u = 2^P ℓ`. -/
lemma len_unsigned_facts {mem : ℕ → ℕ} {a h L P : ℕ} {ℓ : ℝ} (hv : Valid mem a h L)
    (hf : fixVal mem a h L P = ℓ) (hpos : 0 < ℓ) :
    1 ≤ unsignedVal mem a h L ∧ 2 * unsignedVal mem a h L < capacity h L ∧
      (unsignedVal mem a h L : ℝ) = (2 : ℝ) ^ P * ℓ := by
  have hlt := unsignedVal_lt hv
  have hP : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  rw [fixVal, intVal, signedVal] at hf
  by_cases hc : capacity h L ≤ 2 * unsignedVal mem a h L
  · rw [if_pos hc] at hf
    have hneg : (((unsignedVal mem a h L : ℤ) - (capacity h L : ℤ) : ℤ) : ℝ) < 0 := by
      exact_mod_cast (show (unsignedVal mem a h L : ℤ) - capacity h L < 0 by omega)
    have : ℓ < 0 := by rw [← hf]; exact div_neg_of_neg_of_pos hneg hP
    linarith
  · rw [if_neg hc, sub_zero] at hf
    push_cast at hf
    have hu : (unsignedVal mem a h L : ℝ) = (2 : ℝ) ^ P * ℓ := by
      rw [← hf]; field_simp
    refine ⟨?_, by omega, hu⟩
    have : (0 : ℝ) < unsignedVal mem a h L := by rw [hu]; positivity
    exact_mod_cast this

set_option maxHeartbeats 1600000 in
/-- After the decomposition phase, the arrays at `numSt` and `denSt` represent the stretches of
the initial state of the model. Here `mem` is the memory at the start of the order phase, `mem₄`
the memory after it and `mem₅` the memory after the decomposition phase. The length blocks of
the edges of `G₀` lie below the `T` block and hold `ℓ₀` at precision `P`. -/
theorem order_decomp_wstrAt {w h C : ℕ} {G₀ T₀ : MGraph} {vList eList : List ℕ} {X : OrderLayout}
    {θ dBase D Lw k Lin lenArr numS idPtr hiCopy cnt repPtr inR numSt denSt : ℕ}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots : ℕ}
    {K : List ℕ → (ℕ → ℕ) → ℕ} {mem mem₄ mem₅ : ℕ → ℕ} {ret₄ ret₅ P : ℕ}
    {ℓ₀ : ℕ → ℝ} {thresh : ℝ}
    (IO : OrderPhaseIn w h G₀ T₀ vList eList X mem)
    (h₄ : (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH).post X.args
      mem ret₄ mem₄)
    (ID : DecompPhaseIn w h C T₀ vList (DecompLayout.ofOrder X θ dBase D Lw k Lin lenArr numS
      idPtr hiCopy cnt repPtr inR numSt denSt) mem₄)
    (h₅ : (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots K).post
      (DecompLayout.ofOrder X θ dBase D Lw k Lin lenArr numS idPtr hiCopy cnt repPtr inR numSt
        denSt).args mem₄ ret₅ mem₅)
    (hπ : IsEdgeOrder T₀ (orderPi X mem mem₄))
    (hEl : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (hlen : ∀ e ∈ G₀.E, Valid mem (lenArr + e * Lin) h Lin ∧
      fixVal mem (lenArr + e * Lin) h Lin P = ℓ₀ e ∧ 0 < ℓ₀ e ∧ lenArr + e * Lin + Lin ≤ X.tPtr)
    (hhL : 2 ≤ h * Lw)
    (hθ : threshProd C X.n k < 2 ^ (h * (Lw - Lin)))
    (hthr : (threshProd C X.n k : ℝ) = thresh) :
    WstrAt mem₅ numSt denSt X.eCap h Lw G₀
      (initWstr T₀ G₀ (vList.getD 0 0) (orderPi X mem mem₄) (safeLen G₀ ℓ₀) thresh) ∧
    ∀ t < X.m0, mem₅ (hiCopy + t) =
      if thresh ≤ levelStretchBound T₀ (vList.getD 0 0) (orderPi X mem mem₄) G₀ (safeLen G₀ ℓ₀)
        (mem₄ (dgEListBase X.gPtr X.vCap X.eCap + t)) then 1 else 0 := by
  obtain ⟨v₁, m₁, v₃, m₃, v₄, m₄, v₅, o₁, o₃, o₄, o₅⟩ := orderPhase_post h₄
  have hFr := (orderPhase_frame IO o₁ o₃ o₄ o₅).1
  have hfid := order_tOrigId IO o₁ o₃ o₄ o₅
  have hpiv := order_pi_idx IO h₄
  obtain ⟨heL₄, hends⟩ := order_ends IO h₄
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := decompPhase_post h₅
  -- the length blocks in `mem₄`
  have hval : ∀ e ∈ G₀.E, unsignedVal mem₄ (lenArr + e * Lin) h Lin =
      unsignedVal mem (lenArr + e * Lin) h Lin := fun e he =>
    unsignedVal_congr fun j hj => hFr _ (Or.inl (by have := (hlen e he).2.2.2; omega))
  have hLF : ∀ e ∈ G₀.E, 1 ≤ unsignedVal mem₄ (lenArr + e * Lin) h Lin ∧
      2 * unsignedVal mem₄ (lenArr + e * Lin) h Lin < capacity h Lin ∧
      (unsignedVal mem₄ (lenArr + e * Lin) h Lin : ℝ) = ((2 ^ P : ℕ) : ℝ) * safeLen G₀ ℓ₀ e := by
    intro e he
    obtain ⟨hv, hf, hp, -⟩ := hlen e he
    rw [hval e he, safeLen_eq_of_mem ℓ₀ he]
    push_cast
    exact len_unsigned_facts hv hf hp
  have hEt : ∀ t < X.m0, mem₄ (dgEListBase X.gPtr X.vCap X.eCap + t) ∈ G₀.E := fun t ht => by
    rw [heL₄ t ht]
    exact (hEl _).mp (getD_mem_of_lt (by rw [IO.heLen]; exact ht))
  refine (decompPhase_wstrAt (S := 2 ^ P) ID q₁ q₂ q₃ q₄ q₅ q₆ q₇ hπ (fun j hj => hpiv j hj)
    (fun f _ => safeLen_nonneg (fun e he => (hlen e he).2.2.1) f) (fun i hi => ?_) hhL
    (by positivity) (fun e he => ?_) (fun t ht => by dsimp only [DecompLayout.ofOrder]; rw [heL₄ t ht]; exact (hends t ht).1)
    (fun t ht => by dsimp only [DecompLayout.ofOrder]; rw [heL₄ t ht]; exact (hends t ht).2) (fun t ht => (hLF _ (hEt t ht)).2.2)
    (fun t ht => (hLF _ (hEt t ht)).1) (fun t ht => (hLF _ (hEt t ht)).2.1) hθ hthr)
  · -- the tree edge at index `i`
    have hi' : i < X.tM := hi
    show (blkExtVal h mem₄ lenArr (tOrigIdBase X.tPtr X.vCap X.tM) Lin X.nOrig i : ℝ) =
      ((2 ^ P : ℕ) : ℝ) * safeLen G₀ ℓ₀ (mem₄ (tOrigIdBase X.tPtr X.vCap X.tM + i))
    unfold blkExtVal
    split_ifs with hio
    · have he : mem₄ (tOrigIdBase X.tPtr X.vCap X.tM + i) ∈ G₀.E := by
        rw [hfid i hi']; exact (IO.hO i hi').mpr hio
      exact (hLF _ he).2.2
    · have he : mem₄ (tOrigIdBase X.tPtr X.vCap X.tM + i) ∉ G₀.E := by
        rw [hfid i hi']; exact fun h' => hio ((IO.hO i hi').mp h')
      unfold safeLen
      rw [if_neg he]
      simp
  · -- every edge of `G₀` is in the edge list
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp ((hEl e).mpr he)
    refine ⟨t, show t < X.m0 by rw [← IO.heLen]; exact ht, ?_⟩
    show mem₄ (dgEListBase X.gPtr X.vCap X.eCap + t) = _
    rw [heL₄ t (by rw [← IO.heLen]; exact ht), List.getD_eq_getElem _ _ ht]

end

end MinCostFlow.LSF.Program
