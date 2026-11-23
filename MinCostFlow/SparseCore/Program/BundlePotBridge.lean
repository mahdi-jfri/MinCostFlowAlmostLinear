module

public import MinCostFlow.SparseCore.BundleTreeCore
public import MinCostFlow.Bundle.Initialize
public import MinCostFlow.SparseCore.Program.ContractOrder

import Mathlib.Data.Nat.Log

/-!
# Potential and initialization bridge for the bundle program (`BundlePotBridge`)

Supplies two mathematical foundations for the Word-RAM bundle manager (`Bundle*.lean`):

1. **Piecewise-linear logarithmic potential (`tourPotTerm`, `tourPot`)**:
   `tourPotTerm n = (Nat.log 2 n + 2) * n - 2 ^ (Nat.log 2 n + 1)` for `n ≥ 1` (`0` for `n = 0`).
   Its unit increment is exact (`Nat.log 2 n + 2`), eliminating power-of-two jumps on insertions,
   satisfying `h(a) + h(b) + min(a, b) ≤ h(a + b)`, and paying for scanning all non-largest new
   roots in every core split group over an epoch (`tourPotTerm_sum_split`).
2. **End-key round-trip and chunked initialization (`bundle_endOfKey_endKey`, `bundle_endKey_endOfKey`,
   `initBundleFor_eq_initBundleState`, `bundleState_eq_initBundleState_of_slots`,
   `initialChunks_getElem`, `mem_initialChunks_div`)**:
   Shows that single-pass chunking of each core vertex's tour restricted to a bucket's edges
   produces the exact initial bundle state `initBundleFor cs ord E k`.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.LSF MinCostFlow.Chain

/-! ## 1. Definitions -/

@[expose] public section

/-- Piecewise-linear integer surrogate for `n log₂ n`, agreeing with `k · 2^k` at `n = 2^k` and
having exact unit increment `Nat.log 2 n + 2` for every `n ≥ 1`. -/
def tourPotTerm (n : ℕ) : ℕ :=
  if n = 0 then 0 else (Nat.log 2 n + 2) * n - 2 ^ (Nat.log 2 n + 1)

/-- Potential of a core rotation on root set `R`. -/
def tourPot (R : Finset ℕ) (cord : ℕ → List End) : ℕ :=
  ∑ r ∈ R, tourPotTerm (cord r).length

end

/-! ## 2. End-key round-trip lemmas -/

public section

lemma bundle_endOfKey_endKey (x : End) : endOfKey (endKey x) = x := by
  rcases x with ⟨e, side⟩
  cases side <;> simp [endOfKey, endKey]
  omega

lemma bundle_endKey_endOfKey (a : ℕ) : endKey (endOfKey a) = a := by
  unfold endKey endOfKey
  dsimp only
  by_cases h : a % 2 = 0
  · simp [h]; omega
  · simp [h]; omega

lemma endKey_injective : Function.Injective endKey := by
  intro x y h
  have := congrArg endOfKey h
  rwa [bundle_endOfKey_endKey, bundle_endOfKey_endKey] at this

/-! ## 3. Piecewise-linear logarithmic potential lemmas -/

lemma tourPotTerm_zero : tourPotTerm 0 = 0 := rfl

lemma tourPotTerm_one : tourPotTerm 1 = 0 := by
  simp [tourPotTerm]

private lemma two_pow_log_succ_le_mul {n : ℕ} (hn : n ≠ 0) :
    2 ^ (Nat.log 2 n + 1) ≤ (Nat.log 2 n + 2) * n := by
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have h1 : 2 ^ (Nat.log 2 n + 1) = 2 * 2 ^ Nat.log 2 n := by rw [Nat.pow_succ, Nat.mul_comm]
  have h2 : 2 * n ≤ (Nat.log 2 n + 2) * n :=
    Nat.mul_le_mul_right n (Nat.le_add_left 2 _)
  omega

/-- Exact first difference of `tourPotTerm`: `0` at `n = 0`, and `Nat.log 2 n + 2` for `n ≥ 1`. -/
theorem tourPotTerm_succ (n : ℕ) :
    tourPotTerm (n + 1) = tourPotTerm n + (if n = 0 then 0 else Nat.log 2 n + 2) := by
  cases n with
  | zero => simp [tourPotTerm]
  | succ m =>
    have hn : m + 1 ≠ 0 := Nat.succ_ne_zero m
    have hn1 : m + 2 ≠ 0 := Nat.succ_ne_zero (m + 1)
    set k := Nat.log 2 (m + 1) with hk
    have hpow_le : 2 ^ k ≤ m + 1 := Nat.pow_log_le_self 2 hn
    have hlt_pow : m + 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) (m + 1)
    have hbound1 : 2 ^ (k + 1) ≤ (k + 2) * (m + 1) := hk ▸ two_pow_log_succ_le_mul hn
    have hbound2 := two_pow_log_succ_le_mul hn1
    change tourPotTerm (m + 2) = tourPotTerm (m + 1) + (if m + 1 = 0 then 0 else k + 2)
    simp only [tourPotTerm, hn, hn1, ↓reduceIte]
    rw [← hk]
    by_cases heq : m + 2 = 2 ^ (k + 1)
    · have hk' : Nat.log 2 (m + 2) = k + 1 := by
        rw [heq, Nat.log_pow (by decide)]
      rw [hk'] at hbound2 ⊢
      have hpow2 : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
      have hmul1 : (k + 1 + 2) * (m + 2) = (k + 2) * (m + 2) + 2 ^ (k + 1) := by
        rw [← heq]; ring
      have hmul2 : (k + 2) * (m + 2) = (k + 2) * (m + 1) + (k + 2) := by ring
      omega
    · have hlt2 : m + 2 < 2 ^ (k + 1) := by omega
      have hk' : Nat.log 2 (m + 2) = k := by
        apply le_antisymm
        · exact Nat.lt_succ_iff.mp ((Nat.log_lt_iff_lt_pow (by decide) hn1).mpr hlt2)
        · exact Nat.log_mono_right (Nat.le_succ _)
      rw [hk'] at hbound2 ⊢
      have hmul : (k + 2) * (m + 2) = (k + 2) * (m + 1) + (k + 2) := by ring
      omega

theorem tourPotTerm_mono {a b : ℕ} (h : a ≤ b) : tourPotTerm a ≤ tourPotTerm b := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih =>
    rw [tourPotTerm_succ]
    exact ih.trans (Nat.le_add_right _ _)

private lemma tourPotTerm_step_le_add_one (j b : ℕ) (hjb : j < b) :
    (if j = 0 then 0 else Nat.log 2 j + 2) + 1 ≤
      if b + j = 0 then 0 else Nat.log 2 (b + j) + 2 := by
  have hbj : b + j ≠ 0 := by omega
  simp only [hbj, ↓reduceIte]
  by_cases hj : j = 0
  · simp [hj]
  · simp only [hj, ↓reduceIte]
    have h2j : j * 2 ≤ b + j := by omega
    have hlog : Nat.log 2 j + 1 ≤ Nat.log 2 (b + j) := by
      rw [← Nat.log_mul_base (by decide) hj]
      exact Nat.log_mono_right h2j
    omega

/-- Smaller-side splitting drop: splitting `a + b` into `a` and `b` releases at least `min a b`
units of potential. -/
theorem tourPotTerm_add_ge (a b : ℕ) :
    tourPotTerm a + tourPotTerm b + min a b ≤ tourPotTerm (a + b) := by
  suffices h : ∀ x y, x ≤ y → tourPotTerm x + tourPotTerm y + x ≤ tourPotTerm (y + x) by
    by_cases hab : a ≤ b
    · rw [min_eq_left hab, Nat.add_comm a b]
      exact h a b hab
    · have hba : b ≤ a := Nat.le_of_not_le hab
      rw [min_eq_right hba, Nat.add_comm (tourPotTerm a)]
      exact h b a hba
  intro x y hxy
  induction x with
  | zero => simp [tourPotTerm_zero]
  | succ m ih =>
    have hm_le : m ≤ y := Nat.le_of_succ_le hxy
    have ih' := ih hm_le
    rw [tourPotTerm_succ m, show y + (m + 1) = (y + m) + 1 by omega, tourPotTerm_succ (y + m)]
    have hstep := tourPotTerm_step_le_add_one m y (by omega)
    omega

/-- Multi-way splitting drop: splitting a group `G` of roots with largest root `w_max ∈ G`
releases at least `∑_{w ∈ G.erase w_max} L w` units of potential. -/
theorem tourPotTerm_sum_split {G : Finset ℕ} {L : ℕ → ℕ} {w_max : ℕ}
    (hw : w_max ∈ G) (hmax : ∀ w ∈ G, L w ≤ L w_max) :
    (∑ w ∈ G, tourPotTerm (L w)) + (∑ w ∈ G.erase w_max, L w) ≤ tourPotTerm (∑ w ∈ G, L w) := by
  classical
  have key : ∀ (S : Finset ℕ), w_max ∉ S → (∀ w ∈ S, L w ≤ L w_max) →
      tourPotTerm (L w_max) + (∑ w ∈ S, tourPotTerm (L w)) + (∑ w ∈ S, L w) ≤
        tourPotTerm (L w_max + ∑ w ∈ S, L w) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _ _; simp
    | @insert a s ha ih =>
      intro hwn hle
      have haw : L a ≤ L w_max := hle a (Finset.mem_insert_self a s)
      have hs_le : ∀ w ∈ s, L w ≤ L w_max := fun w hw' => hle w (Finset.mem_insert_of_mem hw')
      have hwn' : w_max ∉ s := fun h => hwn (Finset.mem_insert_of_mem h)
      have ih' := ih hwn' hs_le
      simp only [Finset.sum_insert ha]
      set sumS := ∑ w ∈ s, L w
      have hmin : min (L a) (L w_max + sumS) = L a :=
        min_eq_left (haw.trans (Nat.le_add_right _ _))
      have hadd := tourPotTerm_add_ge (L a) (L w_max + sumS)
      rw [hmin] at hadd
      have hcomm : L a + (L w_max + sumS) = L w_max + (L a + sumS) := by omega
      rw [hcomm] at hadd
      omega
  have hG : insert w_max (G.erase w_max) = G := Finset.insert_erase hw
  have h1 := key (G.erase w_max) (Finset.notMem_erase w_max G)
    (fun w hw' => hmax w (Finset.mem_of_mem_erase hw'))
  rw [← hG]
  simp only [Finset.sum_insert (Finset.notMem_erase w_max G),
    Finset.erase_insert (Finset.notMem_erase w_max G)]
  exact h1

/-- Insertion growth bound: adding `I` elements increases `tourPotTerm` by at most
`I * (Nat.log 2 (n + I) + 2)`. -/
theorem tourPotTerm_add_le (n I : ℕ) :
    tourPotTerm (n + I) ≤ tourPotTerm n + I * (Nat.log 2 (n + I) + 2) := by
  induction I with
  | zero => simp
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 by omega, tourPotTerm_succ (n + k)]
    have hstep : (if n + k = 0 then 0 else Nat.log 2 (n + k) + 2) ≤ Nat.log 2 (n + k + 1) + 2 := by
      split_ifs
      · exact Nat.zero_le _
      · exact Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ _)) 2
    have hmono : k * (Nat.log 2 (n + k) + 2) ≤ k * (Nat.log 2 (n + k + 1) + 2) :=
      Nat.mul_le_mul_left k (Nat.add_le_add_right (Nat.log_mono_right (Nat.le_succ _)) 2)
    have hmul : (k + 1) * (Nat.log 2 (n + k + 1) + 2) =
        k * (Nat.log 2 (n + k + 1) + 2) + (Nat.log 2 (n + k + 1) + 2) := by ring
    omega

/-- Initialization bound: `tourPotTerm n ≤ n * (Nat.log 2 n + 2)`. -/
theorem tourPotTerm_le_mul (n : ℕ) : tourPotTerm n ≤ n * (Nat.log 2 n + 2) := by
  have h := tourPotTerm_add_le 0 n
  simpa [tourPotTerm_zero] using h

/-! ## 4. Single-pass chunked initialization lemmas -/

/-- Exact equality between `initBundleFor` and `initBundleState` under `CompLSFInv` and a rotation
`ρ` with order `ord`. -/
theorem initBundleFor_eq_initBundleState {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {ord : ℕ → List End} (ρ : Rotation cs.G) (hρ : ρ.order = ord)
    (E : Finset ℕ) (k : ℕ) :
    initBundleFor cs ord E k =
      initBundleState (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) E k := by
  classical
  have hex : ∃ (C' : ℝ) (ℓ' : ℕ → ℝ) (_ : CompLSFInv C' ℓ' cs) (ρ' : Rotation cs.G),
      ρ'.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
  unfold initBundleFor
  rw [dite_eq_left hex]
  dsimp only
  have key : ∀ (ρ₁ ρ₂ : Rotation cs.G) (hG₁ hG₂ : cs.G.IsValid)
      (hF₁ hF₂ : cs.lsf.F.IsRootedSpanningForestOf cs.G), ρ₁.order = ρ₂.order →
      coreRotation (L := cs.lsf) ρ₁ hG₁ hF₁ = coreRotation (L := cs.lsf) ρ₂ hG₂ hF₂ := by
    intro ρ₁ ρ₂ hG₁ hG₂ hF₁ hF₂ he
    have := Rotation.ext_order he
    subst this
    rfl
  exact congrArg (fun r => initBundleState r E k)
    (key _ _ _ _ _ _ (hex.choose_spec.choose_spec.choose_spec.choose_spec.trans hρ.symm))

/-- Any `BundleState` whose vertices are `Finset.range slots.length`, edges are `E`, parents match
`slots[b].1` (and `0` outside), and `bundleOf` assigns each end `x ∈ slots[b].2` to `b` agrees with
`initBundleState ρ E k` on `vertices`, `edges`, `parent`, and on `bundleOf x` for every admitted
end `x.1 ∈ E` (and hence has `GraphEq`). -/
theorem bundleState_eq_initBundleState_of_slots {C : MGraph} (ρ : Rotation C) (hC : C.IsValid)
    {E : Finset ℕ} (hE : E ⊆ C.E) {k : ℕ} (hk : 0 < k) (B : BundleState)
    (hV : B.vertices = Finset.range (initialSlots ρ E k).length)
    (hEd : B.edges = E)
    (hPar : ∀ b, B.parent b = ((initialSlots ρ E k)[b]?.getD (0, [])).1)
    (hBun : ∀ b (hb : b < (initialSlots ρ E k).length), ∀ x ∈ (initialSlots ρ E k)[b].2,
      B.bundleOf x = b) :
    B.vertices = (initBundleState ρ E k).vertices ∧
    B.edges = (initBundleState ρ E k).edges ∧
    B.parent = (initBundleState ρ E k).parent ∧
    (∀ x, x.1 ∈ E → B.bundleOf x = (initBundleState ρ E k).bundleOf x) ∧
    GraphEq B.graph (initBundleState ρ E k).graph := by
  set slots := initialSlots ρ E k
  have hPar_eq : B.parent = (initBundleState ρ E k).parent := funext hPar
  have hBun_eq : ∀ x, x.1 ∈ E → B.bundleOf x = (initBundleState ρ E k).bundleOf x := by
    intro x hx
    have hinv := initBundleState_inv ρ hC hE hk
    have hxB := hinv.2.2.1 x ((mem_edgeEnds E x).mpr hx)
    have hblt : (initBundleState ρ E k).bundleOf x < slots.length := Finset.mem_range.mp hxB.1
    have hmem : x ∈ slots[(initBundleState ρ E k).bundleOf x].2 :=
      List.contains_iff_mem.mp (List.findIdx_getElem (w := hblt))
    exact hBun _ hblt x hmem
  have hGr : GraphEq B.graph (initBundleState ρ E k).graph :=
    ⟨hV, hEd, fun e he => ⟨hBun_eq (e, true) (hEd ▸ he), hBun_eq (e, false) (hEd ▸ he)⟩⟩
  exact ⟨hV, hEd, hPar_eq, hBun_eq, hGr⟩

/-- Chunk membership by index: in `initialChunks k xs` (`0 < k`), chunk `c` is
`(xs.drop (c * k)).take k`. -/
theorem initialChunks_getElem {α : Type*} {k : ℕ} (xs : List α)
    (c : ℕ) (hc : c < (initialChunks k xs).length) :
    (initialChunks k xs)[c] = (xs.drop (c * k)).take k := by
  have hgo : ∀ (m : ℕ) (ys : List α) (j : ℕ) (hj : j < m),
      ((List.replicate m k).splitLengths ys)[j]'(by simp [List.length_splitLengths]; exact hj) =
        (ys.drop (j * k)).take k := by
    intro m
    induction m with
    | zero => intro _ _ hj; cases hj
    | succ m ih =>
      intro ys j hj
      cases j with
      | zero => simp [List.replicate_succ]
      | succ j' =>
        have hj' : j' < m := Nat.lt_of_succ_lt_succ hj
        simp only [List.replicate_succ, List.splitLengths, List.getElem_cons_succ, List.splitAt_eq]
        rw [ih (ys.drop k) j' hj', List.drop_drop, show k + j' * k = (j' + 1) * k by ring]
  simpa [initialChunks] using hgo (xs.length ⌈/⌉ k) xs c (by simpa [initialChunks_length] using hc)

/-- Every element `xs[i]` (`i < xs.length`) lies in chunk `i / k` of `initialChunks k xs`. -/
theorem mem_initialChunks_div {α : Type*} {k : ℕ} (hk : 0 < k) (xs : List α)
    (i : ℕ) (hi : i < xs.length) :
    ∃ hdiv : i / k < (initialChunks k xs).length,
      xs[i] ∈ (initialChunks k xs)[i / k]'hdiv := by
  have hdiv : i / k < (initialChunks k xs).length := by
    rw [initialChunks_length]
    have h1 : (i / k + 1) * k ≤ (xs.length ⌈/⌉ k) * k := by
      have hceil := le_smul_ceilDiv (β := ℕ) hk (b := xs.length)
      simp only [smul_eq_mul, Nat.mul_comm k] at hceil
      have hmod : i % k < k := Nat.mod_lt i hk
      have hmul : (i / k) * k + i % k = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i k
      have h2 : (i / k) * k < (xs.length ⌈/⌉ k) * k := by omega
      have h3 : i / k < xs.length ⌈/⌉ k := (Nat.mul_lt_mul_right hk).mp h2
      exact Nat.mul_le_mul_right k h3
    exact (Nat.mul_lt_mul_right hk).mp (by
      have h2 : (i / k) * k + k ≤ (xs.length ⌈/⌉ k) * k := by rwa [Nat.add_mul, Nat.one_mul] at h1
      omega)
  refine ⟨hdiv, ?_⟩
  rw [initialChunks_getElem xs (i / k) hdiv]
  have hmod : i % k < k := Nat.mod_lt i hk
  have hidx : (i / k) * k + i % k = i := by rw [Nat.mul_comm]; exact Nat.div_add_mod i k
  have hlt : i % k < ((xs.drop ((i / k) * k)).take k).length := by
    rw [List.length_take, List.length_drop]
    omega
  have hget : ((xs.drop ((i / k) * k)).take k)[i % k]'hlt = xs[i]'hi := by
    rw [List.getElem_take, List.getElem_drop]
    congr 1
  rw [← hget]
  exact List.getElem_mem hlt

/-! ## 5. Exact smaller-side split detection -/

/-- The surviving ends of bundle `b` under kept edge set `E`. -/
@[expose] def survivingEnds (B : BundleState) (E : Finset ℕ) (b : ℕ) : Finset End :=
  (B.ends b).filter fun x => x.1 ∈ E

/-- The set of final core vertices containing surviving ends of bundle `b`. -/
@[expose] def finalRootsOf (B : BundleState) (E : Finset ℕ) (src' : End → ℕ) (b : ℕ) : Finset ℕ :=
  (survivingEnds B E b).image src'

/-- When all surviving ends of bundle `b` map into a root group `G_v` with distinguished root
`w_max ∈ G_v`, bundle `b` splits (`2 ≤ (finalRootsOf B E src' b).card`) if and only if some
non-maximal root `w ∈ G_v.erase w_max` contains at least one and strictly fewer than all
surviving ends of `b`. -/
theorem splitCands_exact_iff {B : BundleState} {E : Finset ℕ} {src' : End → ℕ} {b : ℕ}
    {G_v : Finset ℕ} {w_max : ℕ}
    (hG : ∀ x ∈ survivingEnds B E b, src' x ∈ G_v) :
    2 ≤ (finalRootsOf B E src' b).card ↔
      ∃ w ∈ G_v.erase w_max,
        0 < ((survivingEnds B E b).filter fun x => src' x = w).card ∧
        ((survivingEnds B E b).filter fun x => src' x = w).card < (survivingEnds B E b).card := by
  constructor
  · intro h2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (Nat.lt_of_succ_le h2)
    have hex : ∃ w ∈ finalRootsOf B E src' b, w ≠ w_max ∧ ∃ w' ∈ finalRootsOf B E src' b, w' ≠ w := by
      by_cases huw : u = w_max
      · exact ⟨v, hv, fun h => huv (huw.trans h.symm), u, hu, huv⟩
      · exact ⟨u, hu, huw, v, hv, huv.symm⟩
    obtain ⟨w, hw, hwn, w', hw', hww'⟩ := hex
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw'
    refine ⟨src' x, Finset.mem_erase.mpr ⟨hwn, hG x hx⟩, ?_, ?_⟩
    · exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
    · refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩)
      intro heq
      have hyin : y ∈ (survivingEnds B E b).filter (fun z => src' z = src' x) := heq.symm ▸ hy
      exact hww' (Finset.mem_filter.mp hyin).2
  · rintro ⟨w, _, hpos, hlt⟩
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    obtain ⟨hxS, hxw⟩ := Finset.mem_filter.mp hx
    have hne : (survivingEnds B E b).filter (fun z => src' z = w) ≠ survivingEnds B E b := by
      intro heq; rw [heq] at hlt; exact lt_irrefl _ hlt
    have hex_out : ∃ y ∈ survivingEnds B E b, src' y ≠ w := by
      by_contra hall
      push Not at hall
      apply hne
      ext z
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      exact hall z
    obtain ⟨y, hyS, hyw⟩ := hex_out
    have h1 : src' x ∈ finalRootsOf B E src' b := Finset.mem_image.mpr ⟨x, hxS, rfl⟩
    have h2 : src' y ∈ finalRootsOf B E src' b := Finset.mem_image.mpr ⟨y, hyS, rfl⟩
    have hne' : src' x ≠ src' y := by rw [hxw]; exact hyw.symm
    exact Finset.one_lt_card.mpr ⟨src' x, h1, src' y, h2, hne'⟩

end

end MinCostFlow.SparseCore.Program
