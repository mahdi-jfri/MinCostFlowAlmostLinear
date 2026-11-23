module

public import MinCostFlow.SparseCore.Program.LSFWindowWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Canonical Guest Memory Image and `canonicalLSFInit` (`LSFWindowCanon`)

Defines:
* The canonical guest memory layout (`canonVCap`, `canonECap`, `canonVList`, `canonEList`,
  `canonLw`, `canonDGMem`, `canonGuestMem`, `canonWordBits`) for `(G₀, ℓ₀, k)` depending only on
  the abstract graph `G₀`, edge lengths `ℓ₀` restricted to `G₀.E`, and parameters `(h, L_in, P_fp, k)`.
* `CanonicalLSFValid`, `CanonicalLSFGuestRun`, and `canonicalLSFGuestRun_exists`: a single
  witnessed guest execution of `lemma55Module` at word size `canonWordBits` producing all `k`
  initial LSF states, `(LSFRep h).rep` witnesses, pairwise-disjoint footprints, and approximate-MWU
  bounds at step error `δ = 1 / (20 * k)`.
* `canonicalLSFInitWithH` and `canonicalLSFInit := canonicalLSFInitWithH 4`: returns the guest-run
  LSF states under `CanonicalLSFValid`, and `fallbackLSFInit` otherwise.
* `canonicalLSFInitWithH_approxMWU` and `canonicalLSFInit_approxMWU`: proves the approximate-MWU
  specification with `(C_lsst = 4 * max K_AN 1 + 5, α = 5 / 4, K_σ = defaultK_sigma K_AN,
  K_ρ = 40960)` under the stretch-only `[AN19]` hypothesis.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
  MinCostFlow.DynSpanner.Program MinCostFlow.WideWord MinCostFlow.Num

/-! ## Canonical graph dimensions, widths, and guest layout -/

def canonVCap (G₀ : MGraph) : ℕ := G₀.V.sup id + 1

def canonECap (G₀ : MGraph) : ℕ := max 1 (G₀.E.sup id + 1)

def canonVList (G₀ : MGraph) : List ℕ := G₀.V.sort (· ≤ ·)

def canonEList (G₀ : MGraph) : List ℕ := G₀.E.sort (· ≤ ·)

/-- Canonical stretch-array limb width computed purely from `(K_AN, L_in, n0, k_nat)`. -/
noncomputable def canonLw (K_AN : ℝ) (L_in n0 k_nat : ℕ) : ℕ :=
  L_in + Nat.log 2 (lemma55RhoConst K_AN + 1) + Nat.log 2 (k_nat + 1) +
    6 * Nat.log 2 (Nat.log 2 (n0 + 2) + 2) + 8

def canonLenArr (G₀ : MGraph) : ℕ := dynGraphSize (canonVCap G₀) (canonECap G₀)

def canonHandlesOut (G₀ : MGraph) (L_in : ℕ) : ℕ := canonLenArr G₀ + canonECap G₀ * L_in

def canonHeap (G₀ : MGraph) (L_in k_nat : ℕ) : ℕ := canonHandlesOut G₀ L_in + k_nat

noncomputable def canonGuestArgs (K_AN : ℝ) (L_in P_fp : ℕ) (G₀ : MGraph) (k_nat : ℕ) : List ℕ :=
  [0, canonLenArr G₀, L_in, P_fp, k_nat, canonLw K_AN L_in G₀.n k_nat,
   canonVCap G₀, canonECap G₀, canonHandlesOut G₀ L_in, canonHeap G₀ L_in k_nat]

/-- Tight linear upper bound on all addresses and intermediate word values of the canonical guest. -/
noncomputable def canonWordBound (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (h L_in P_fp : ℕ) (G₀ : MGraph) (k_nat : ℕ) : ℕ :=
  max (canonHeap G₀ L_in k_nat +
        lemma55Space Q_AN K_AN c_AN h L_in (canonLw K_AN L_in G₀.n k_nat) P_fp k_nat
          (canonVCap G₀) (canonECap G₀) G₀.n G₀.m)
      (max (2 * P_fp + 9) (3 * (4 * k_nat * (hldDepthBound G₀.n + 1)))) + 1

/-- Canonical guest word bit-width `w'` (with `2 ^ w'` linear in `canonWordBound`). -/
noncomputable def canonWordBits (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (h L_in P_fp : ℕ) (G₀ : MGraph) (k_nat : ℕ) : ℕ :=
  max (3 * h + 2) (Nat.log 2 (canonWordBound Q_AN c_AN K_AN h L_in P_fp G₀ k_nat) + 1)

lemma canonVCap_gt {G₀ : MGraph} {v : ℕ} (hv : v ∈ G₀.V) : v < canonVCap G₀ :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hv)

lemma canonECap_gt {G₀ : MGraph} {e : ℕ} (he : e ∈ G₀.E) : e < canonECap G₀ :=
  lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) he)) (le_max_right _ _)

lemma canonECap_pos (G₀ : MGraph) : 1 ≤ canonECap G₀ := le_max_left _ _

lemma canonVCap_le_of_dynGraphAt {mem : ℕ → ℕ} {g0Ptr vCap0 eCap0 : ℕ} {G₀ : MGraph}
    (hdg : DynGraphAt mem g0Ptr vCap0 eCap0 G₀) (hV : G₀.V.Nonempty) :
    canonVCap G₀ ≤ vCap0 := by
  have hsup : G₀.V.sup id < vCap0 := by
    have ⟨v₀, hv₀⟩ := hV
    have hpos : 0 < vCap0 := Nat.lt_of_le_of_lt (Nat.zero_le v₀) (hdg.2.1 v₀ hv₀)
    exact (Finset.sup_lt_iff hpos).mpr fun v hv => hdg.2.1 v hv
  unfold canonVCap; omega

lemma canonECap_le_of_dynGraphAt {mem : ℕ → ℕ} {g0Ptr vCap0 eCap0 : ℕ} {G₀ : MGraph}
    (hdg : DynGraphAt mem g0Ptr vCap0 eCap0 G₀) (heCap1 : 1 ≤ eCap0) :
    canonECap G₀ ≤ eCap0 := by
  unfold canonECap
  refine max_le heCap1 ?_
  have hsup : G₀.E.sup id < eCap0 := (Finset.sup_lt_iff heCap1).mpr fun e he => hdg.2.2.1 e he
  omega

lemma canonLw_ge_Lin (K_AN : ℝ) (L_in n0 k_nat : ℕ) : L_in ≤ canonLw K_AN L_in n0 k_nat := by
  unfold canonLw; omega

lemma canonLw_rho_cap (K_AN : ℝ) {h : ℕ} (hh : 1 ≤ h) (L_in n0 k_nat : ℕ) :
    lemma55RhoNat K_AN n0 k_nat < 2 ^ (h * (canonLw K_AN L_in n0 k_nat - L_in)) := by
  set a := Nat.log 2 (lemma55RhoConst K_AN + 1) + 1
  set b := Nat.log 2 (k_nat + 1) + 1
  set c := Nat.log 2 (Nat.log 2 (n0 + 2) + 2) + 1
  have ha : lemma55RhoConst K_AN < 2 ^ a :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.lt_pow_succ_log_self (by decide) _).le
  have hb : k_nat < 2 ^ b :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.lt_pow_succ_log_self (by decide) _).le
  have hc1 : Nat.log 2 (n0 + 2) + 1 < 2 ^ c :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.lt_pow_succ_log_self (by decide) _).le
  have hc6 : (Nat.log 2 (n0 + 2) + 1) ^ 6 < (2 ^ c) ^ 6 :=
    Nat.pow_lt_pow_left hc1 (by decide)
  have hc6' : (Nat.log 2 (n0 + 2) + 1) ^ 6 < 2 ^ (6 * c) := by
    rwa [← pow_mul, mul_comm c 6] at hc6
  have hprod : lemma55RhoConst K_AN * k_nat * (Nat.log 2 (n0 + 2) + 1) ^ 6 <
      2 ^ (a + b + 6 * c) := by
    have h1 : lemma55RhoConst K_AN * k_nat < 2 ^ a * 2 ^ b := by
      rcases Nat.eq_zero_or_pos k_nat with rfl | hkpos
      · simp
      · exact Nat.mul_lt_mul_of_lt_of_le' ha hb.le hkpos
    have h2 : lemma55RhoConst K_AN * k_nat * (Nat.log 2 (n0 + 2) + 1) ^ 6 <
        (2 ^ a * 2 ^ b) * 2 ^ (6 * c) :=
      Nat.mul_lt_mul_of_lt_of_le' h1 hc6'.le (Nat.pow_pos (Nat.succ_pos _))
    rwa [← pow_add, ← pow_add] at h2
  have hexp : a + b + 6 * c ≤ h * (canonLw K_AN L_in n0 k_nat - L_in) := by
    have hdiff : canonLw K_AN L_in n0 k_nat - L_in = a + b + 6 * c := by
      dsimp only [canonLw, a, b, c]; omega
    rw [hdiff]
    exact Nat.le_mul_of_pos_left _ hh
  exact lt_of_lt_of_le hprod (Nat.pow_le_pow_right (by decide) hexp)

lemma canonWordBits_bounds (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ)
    (h L_in P_fp : ℕ) (G₀ : MGraph) (k_nat : ℕ) :
    3 * h + 2 ≤ canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k_nat ∧
    canonWordBound Q_AN c_AN K_AN h L_in P_fp G₀ k_nat <
      2 ^ canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k_nat ∧
    2 ^ canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k_nat ≤
      max (2 ^ (3 * h + 2)) (2 * canonWordBound Q_AN c_AN K_AN h L_in P_fp G₀ k_nat) := by
  set B := canonWordBound Q_AN c_AN K_AN h L_in P_fp G₀ k_nat
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · exact lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by decide) B)
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  · unfold canonWordBits
    rcases le_total (3 * h + 2) (Nat.log 2 B + 1) with hle | hle
    · rw [max_eq_right hle, pow_succ, mul_comm]
      have hBpos : 0 < B := by dsimp only [B, canonWordBound]; omega
      have hlog : 2 ^ Nat.log 2 B ≤ B := Nat.pow_log_le_self 2 (Nat.ne_of_gt hBpos)
      exact le_trans (Nat.mul_le_mul_left 2 hlog) (le_max_right _ _)
    · rw [max_eq_left hle]
      exact le_max_left _ _

/-! ## Canonical `DynGraphAt` memory image and base-`2^h` limbs -/

/-- Base-`2^h` limb `i` of natural number `u`. -/
def natLimb (u h i : ℕ) : ℕ := (u / (2 ^ h) ^ i) % 2 ^ h

/-- Integer representation `⌊ℓ₀(e) · 2^P_fp⌋` for canonical positive fixed-point edge lengths. -/
noncomputable def canonLenInt (ℓ₀ : ℕ → ℝ) (P_fp e : ℕ) : ℕ :=
  Nat.floor (ℓ₀ e * (2 : ℝ) ^ P_fp)

lemma unsignedVal_eq_sum_limbs {mem : ℕ → ℕ} {a h L : ℕ} :
    ∀ {u : ℕ}, Valid mem a h L → unsignedVal mem a h L = u →
      ∀ i < L, mem (a + i) = natLimb u h i := by
  induction L generalizing a with
  | zero => intro _ _ _ _ hi; omega
  | succ L ih =>
    intro u hv hu i hi
    obtain ⟨hhead, htail⟩ := valid_succ.mp hv
    rw [unsignedVal] at hu
    have hbase : 0 < base h := base_pos h
    cases i with
    | zero =>
      simp only [Nat.add_zero, natLimb, pow_zero, Nat.div_one]
      rw [← hu]
      change mem a = (mem a + base h * unsignedVal mem (a + 1) h L) % base h
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hhead]
    | succ i =>
      have hdiv : u / base h = unsignedVal mem (a + 1) h L := by
        rw [← hu, Nat.add_mul_div_left _ _ hbase, Nat.div_eq_of_lt hhead, Nat.zero_add]
      have hrec := ih htail hdiv.symm i (by omega)
      rw [show a + (i + 1) = (a + 1) + i by omega, hrec]
      unfold natLimb
      change (u / base h / base h ^ i) % base h = (u / base h ^ (i + 1)) % base h
      rw [Nat.div_div_eq_div_mul, ← pow_succ']

lemma valid_limbs_eq_natLimb {mem : ℕ → ℕ} {a h L P_fp : ℕ} {x : ℝ}
    (hv : Valid mem a h L) (hfx : fixVal mem a h L P_fp = x) (hx : 0 < x) :
    ∀ i < L, mem (a + i) = natLimb (Nat.floor (x * (2 : ℝ) ^ P_fp)) h i := by
  have h2P_pos : (0 : ℝ) < (2 : ℝ) ^ P_fp := by positivity
  have hint_pos : 0 < intVal mem a h L := by
    have h1 : (0 : ℝ) < (intVal mem a h L : ℝ) / (2 : ℝ) ^ P_fp := by
      rw [← fixVal, hfx]; exact hx
    have h2 : (0 : ℝ) < (intVal mem a h L : ℝ) := (div_pos_iff_of_pos_right h2P_pos).mp h1
    exact_mod_cast h2
  have hu_lt := unsignedVal_lt hv
  have hnot_neg : ¬ capacity h L ≤ 2 * unsignedVal mem a h L := by
    intro hge
    unfold intVal signedVal at hint_pos
    rw [ite_eq_left hge] at hint_pos
    omega
  have hint_eq : intVal mem a h L = (unsignedVal mem a h L : ℤ) := by
    unfold intVal signedVal
    rw [ite_eq_right hnot_neg, sub_zero]
  have hx_mul : x * (2 : ℝ) ^ P_fp = (unsignedVal mem a h L : ℝ) := by
    rw [← hfx, fixVal, div_mul_cancel₀ _ h2P_pos.ne', hint_eq]
    norm_cast
  have hfl : Nat.floor (x * (2 : ℝ) ^ P_fp) = unsignedVal mem a h L := by
    rw [hx_mul, Nat.floor_natCast]
  rw [hfl]
  exact unsignedVal_eq_sum_limbs hv rfl

lemma natLimb_lt_base (u h i : ℕ) : natLimb u h i < base h :=
  Nat.mod_lt _ (base_pos h)

lemma valid_of_natLimb {mem : ℕ → ℕ} {a h L u : ℕ}
    (hmem : ∀ i < L, mem (a + i) = natLimb u h i) : Valid mem a h L := fun i hi => by
  rw [hmem i hi]; exact natLimb_lt_base u h i

lemma unsignedVal_natLimb {mem : ℕ → ℕ} {a h L u : ℕ}
    (hmem : ∀ i < L, mem (a + i) = natLimb u h i) (hu : u < capacity h L) :
    unsignedVal mem a h L = u := by
  induction L generalizing a u with
  | zero => simp [unsignedVal, capacity] at hu ⊢; omega
  | succ L ih =>
    have hbase : 0 < base h := base_pos h
    have h0 : mem a = u % base h := by
      have := hmem 0 (Nat.succ_pos L)
      simpa [natLimb, base] using this
    have htail : ∀ i < L, mem ((a + 1) + i) = natLimb (u / base h) h i := fun i hi => by
      have := hmem (i + 1) (by omega)
      rw [show a + (i + 1) = (a + 1) + i by omega] at this
      rw [this]
      unfold natLimb
      change (u / base h ^ (i + 1)) % base h = (u / base h / base h ^ i) % base h
      rw [Nat.div_div_eq_div_mul, ← pow_succ']
    have hdiv_lt : u / base h < capacity h L := by
      rw [capacity_succ] at hu
      exact Nat.div_lt_of_lt_mul hu
    rw [unsignedVal, h0, ih htail hdiv_lt, Nat.mod_add_div]

/-- Static non-incidence part of the canonical `DynGraphAt` image at guest address `0`. -/
def canonDGMemBase (G₀ : MGraph) (a : ℕ) : ℕ :=
  open Classical in
  let vCap := canonVCap G₀
  let eCap := canonECap G₀
  let vL := canonVList G₀
  let eL := canonEList G₀
  if a = 0 then vCap
  else if a = 1 then eCap
  else if a = 2 then G₀.n
  else if a = 3 then G₀.m
  else if dgVPresBase 0 ≤ a ∧ a < dgVListBase 0 vCap then
    let v := a - dgVPresBase 0
    if v ∈ G₀.V then 1 else 0
  else if dgVListBase 0 vCap ≤ a ∧ a < dgVPosBase 0 vCap then
    let i := a - dgVListBase 0 vCap
    vL.getD i 0
  else if dgVPosBase 0 vCap ≤ a ∧ a < dgExtToIntBase 0 vCap then
    let v := a - dgVPosBase 0 vCap
    if v ∈ G₀.V then vL.idxOf v else 0
  else if dgExtToIntBase 0 vCap ≤ a ∧ a < dgIntToExtBase 0 vCap then
    let v := a - dgExtToIntBase 0 vCap
    if v ∈ G₀.V then v else 0
  else if dgIntToExtBase 0 vCap ≤ a ∧ a < dgSlotDegBase 0 vCap then
    let v := a - dgIntToExtBase 0 vCap
    if v ∈ G₀.V then v else 0
  else if dgEPresBase 0 vCap ≤ a ∧ a < dgEListBase 0 vCap eCap then
    let e := a - dgEPresBase 0 vCap
    if e ∈ G₀.E then 1 else 0
  else if dgEListBase 0 vCap eCap ≤ a ∧ a < dgEPosBase 0 vCap eCap then
    let i := a - dgEListBase 0 vCap eCap
    eL.getD i 0
  else if dgEPosBase 0 vCap eCap ≤ a ∧ a < dgETailSlotBase 0 vCap eCap then
    let e := a - dgEPosBase 0 vCap eCap
    if e ∈ G₀.E then eL.idxOf e else 0
  else if dgETailSlotBase 0 vCap eCap ≤ a ∧ a < dgEHeadSlotBase 0 vCap eCap then
    let e := a - dgETailSlotBase 0 vCap eCap
    if e ∈ G₀.E then G₀.tail e else 0
  else if dgEHeadSlotBase 0 vCap eCap ≤ a ∧ a < dgHePrevBase 0 vCap eCap then
    let e := a - dgEHeadSlotBase 0 vCap eCap
    if e ∈ G₀.E then G₀.head e else 0
  else 0

/-- Pure single-half-edge doubly-linked-list prepend at guest address `0`. -/
def pushHalfEdgeMem (vCap eCap s he : ℕ) (mem : ℕ → ℕ) : ℕ → ℕ :=
  let oldHead := mem (dgIncHeadBase 0 vCap + s)
  let deg := mem (dgSlotDegBase 0 vCap + s)
  let m1 := Function.update mem (dgHePrevBase 0 vCap eCap + he) 0
  let m2 := Function.update m1 (dgHeNextBase 0 vCap eCap + he) oldHead
  let m3 := if oldHead = 0 then m2
            else Function.update m2 (dgHePrevBase 0 vCap eCap + (oldHead - 1)) (he + 1)
  let m4 := Function.update m3 (dgIncHeadBase 0 vCap + s) (he + 1)
  Function.update m4 (dgSlotDegBase 0 vCap + s) (deg + 1)

/-- Pure two-half-edge prepend for edge `e` (`2 * e` at `G₀.tail e`, then `2 * e + 1` at `G₀.head e`). -/
def pushEdgeIncMem (G₀ : MGraph) (vCap eCap : ℕ) (mem : ℕ → ℕ) (e : ℕ) : ℕ → ℕ :=
  pushHalfEdgeMem vCap eCap (G₀.head e) (2 * e + 1)
    (pushHalfEdgeMem vCap eCap (G₀.tail e) (2 * e) mem)

/-- Full canonical `DynGraphAt` memory image at guest address `0`. -/
def canonDGMem (G₀ : MGraph) : ℕ → ℕ :=
  (canonEList G₀).foldl (pushEdgeIncMem G₀ (canonVCap G₀) (canonECap G₀)) (canonDGMemBase G₀)

/-- Full canonical guest initial memory image for `(G₀, ℓ₀, h, L_in, P_fp)`. -/
noncomputable def canonGuestMem (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (h L_in P_fp : ℕ) (a : ℕ) : ℕ :=
  open Classical in
  if a < canonLenArr G₀ then
    canonDGMem G₀ a
  else if a < canonHandlesOut G₀ L_in then
    let off := a - canonLenArr G₀
    let e := off / L_in
    let t := off % L_in
    if e ∈ G₀.E then natLimb (canonLenInt ℓ₀ P_fp e) h t else 0
  else 0

lemma canonGuestMem_eq_of_eq_on_E {G₀ : MGraph} {ℓ₁ ℓ₂ : ℕ → ℝ} {h L_in P_fp : ℕ}
    (hℓ : ∀ e ∈ G₀.E, ℓ₁ e = ℓ₂ e) :
    canonGuestMem G₀ ℓ₁ h L_in P_fp = canonGuestMem G₀ ℓ₂ h L_in P_fp := by
  classical
  funext a
  unfold canonGuestMem
  split_ifs with h1 h2
  · rfl
  · dsimp only
    split_ifs with h3
    · simp [canonLenInt, hℓ _ h3]
    · rfl
  · rfl

lemma canonGuestMem_zeroFrom (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (h L_in P_fp k_nat : ℕ) :
    ZeroFrom (canonGuestMem G₀ ℓ₀ h L_in P_fp) (canonHeap G₀ L_in k_nat) := by
  intro z hz
  unfold canonGuestMem
  have h1 : ¬ z < canonLenArr G₀ := by unfold canonHeap canonHandlesOut at hz; omega
  have h2 : ¬ z < canonHandlesOut G₀ L_in := by unfold canonHeap at hz; omega
  simp [h1, h2]

/-! ## Fast accessor lemmas for `canonDGMemBase` -/

lemma canonDGMemBase_hdr (G₀ : MGraph) :
    canonDGMemBase G₀ 0 = canonVCap G₀ ∧
    canonDGMemBase G₀ 1 = canonECap G₀ ∧
    canonDGMemBase G₀ 2 = G₀.n ∧
    canonDGMemBase G₀ 3 = G₀.m := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [canonDGMemBase]

lemma canonDGMemBase_vPres {G₀ : MGraph} {v : ℕ} (hv : v < canonVCap G₀) :
    canonDGMemBase G₀ (dgVPresBase 0 + v) = (open Classical in if v ∈ G₀.V then 1 else 0) := by
  classical
  set a := dgVPresBase 0 + v
  have ha : a = 4 + v := by simp [a, dgVPresBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by dsimp [dgVPresBase, dgVListBase]; omega)]
  simp [show a - dgVPresBase 0 = v by dsimp [a]; omega]

lemma canonDGMemBase_vList {G₀ : MGraph} {i : ℕ} (hi : i < canonVCap G₀) :
    canonDGMemBase G₀ (dgVListBase 0 (canonVCap G₀) + i) = (canonVList G₀).getD i 0 := by
  set a := dgVListBase 0 (canonVCap G₀) + i
  have ha : a = 4 + canonVCap G₀ + i := by simp [a, dgVListBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_left (by dsimp [dgVListBase, dgVPosBase]; omega)]
  simp [show a - dgVListBase 0 (canonVCap G₀) = i by dsimp [a]; omega]

lemma canonDGMemBase_vPos {G₀ : MGraph} {v : ℕ} (hv : v < canonVCap G₀) :
    canonDGMemBase G₀ (dgVPosBase 0 (canonVCap G₀) + v) =
      (open Classical in if v ∈ G₀.V then (canonVList G₀).idxOf v else 0) := by
  classical
  set a := dgVPosBase 0 (canonVCap G₀) + v
  have ha : a = 4 + 2 * canonVCap G₀ + v := by simp [a, dgVPosBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_right (by dsimp [dgVListBase, dgVPosBase]; omega),
      ite_eq_left (by dsimp [dgVPosBase, dgExtToIntBase]; omega)]
  simp [show a - dgVPosBase 0 (canonVCap G₀) = v by dsimp [a]; omega]

lemma canonDGMemBase_extToInt {G₀ : MGraph} {v : ℕ} (hv : v < canonVCap G₀) :
    canonDGMemBase G₀ (dgExtToIntBase 0 (canonVCap G₀) + v) =
      (open Classical in if v ∈ G₀.V then v else 0) := by
  classical
  set a := dgExtToIntBase 0 (canonVCap G₀) + v
  have ha : a = 4 + 3 * canonVCap G₀ + v := by simp [a, dgExtToIntBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_right (by dsimp [dgVListBase, dgVPosBase]; omega),
      ite_eq_right (by dsimp [dgVPosBase, dgExtToIntBase]; omega),
      ite_eq_left (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega)]
  simp [show a - dgExtToIntBase 0 (canonVCap G₀) = v by dsimp [a]; omega]

lemma canonDGMemBase_intToExt {G₀ : MGraph} {v : ℕ} (hv : v < canonVCap G₀) :
    canonDGMemBase G₀ (dgIntToExtBase 0 (canonVCap G₀) + v) =
      (open Classical in if v ∈ G₀.V then v else 0) := by
  classical
  set a := dgIntToExtBase 0 (canonVCap G₀) + v
  have ha : a = 4 + 4 * canonVCap G₀ + v := by simp [a, dgIntToExtBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_right (by dsimp [dgVListBase, dgVPosBase]; omega),
      ite_eq_right (by dsimp [dgVPosBase, dgExtToIntBase]; omega),
      ite_eq_right (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
      ite_eq_left (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega)]
  simp [show a - dgIntToExtBase 0 (canonVCap G₀) = v by dsimp [a]; omega]

lemma canonDGMemBase_slotDeg {G₀ : MGraph} {s : ℕ} (hs : s < canonVCap G₀) :
    canonDGMemBase G₀ (dgSlotDegBase 0 (canonVCap G₀) + s) = 0 := by
  set a := dgSlotDegBase 0 (canonVCap G₀) + s
  have ha : a = 4 + 5 * canonVCap G₀ + s := by simp [a, dgSlotDegBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_right (by dsimp [dgVListBase, dgVPosBase]; omega),
      ite_eq_right (by dsimp [dgVPosBase, dgExtToIntBase]; omega),
      ite_eq_right (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
      ite_eq_right (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega),
      ite_eq_right (by dsimp [dgEPresBase, dgEListBase]; omega),
      ite_eq_right (by dsimp [dgEListBase, dgEPosBase]; omega),
      ite_eq_right (by dsimp [dgEPosBase, dgETailSlotBase]; omega),
      ite_eq_right (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega),
      ite_eq_right (by dsimp [dgEHeadSlotBase, dgHePrevBase]; omega)]

lemma canonDGMemBase_incHead {G₀ : MGraph} {s : ℕ} (hs : s < canonVCap G₀) :
    canonDGMemBase G₀ (dgIncHeadBase 0 (canonVCap G₀) + s) = 0 := by
  set a := dgIncHeadBase 0 (canonVCap G₀) + s
  have ha : a = 4 + 6 * canonVCap G₀ + s := by simp [a, dgIncHeadBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_right (by dsimp [dgVListBase, dgVPosBase]; omega),
      ite_eq_right (by dsimp [dgVPosBase, dgExtToIntBase]; omega),
      ite_eq_right (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
      ite_eq_right (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega),
      ite_eq_right (by dsimp [dgEPresBase, dgEListBase]; omega),
      ite_eq_right (by dsimp [dgEListBase, dgEPosBase]; omega),
      ite_eq_right (by dsimp [dgEPosBase, dgETailSlotBase]; omega),
      ite_eq_right (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega),
      ite_eq_right (by dsimp [dgEHeadSlotBase, dgHePrevBase]; omega)]

lemma canonDGMemBase_ePres {G₀ : MGraph} {e : ℕ} (he : e < canonECap G₀) :
    canonDGMemBase G₀ (dgEPresBase 0 (canonVCap G₀) + e) =
      (open Classical in if e ∈ G₀.E then 1 else 0) := by
  classical
  set a := dgEPresBase 0 (canonVCap G₀) + e
  have ha : a = 4 + 7 * canonVCap G₀ + e := by simp [a, dgEPresBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_right (by dsimp [dgVListBase, dgVPosBase]; omega),
      ite_eq_right (by dsimp [dgVPosBase, dgExtToIntBase]; omega),
      ite_eq_right (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
      ite_eq_right (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega),
      ite_eq_left (by dsimp [dgEPresBase, dgEListBase]; omega)]
  simp [show a - dgEPresBase 0 (canonVCap G₀) = e by dsimp [a]; omega]

lemma canonDGMemBase_eList {G₀ : MGraph} {i : ℕ} (hi : i < canonECap G₀) :
    canonDGMemBase G₀ (dgEListBase 0 (canonVCap G₀) (canonECap G₀) + i) = (canonEList G₀).getD i 0 := by
  set a := dgEListBase 0 (canonVCap G₀) (canonECap G₀) + i
  have ha : a = 4 + 7 * canonVCap G₀ + canonECap G₀ + i := by simp [a, dgEListBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_right (by dsimp [dgVListBase, dgVPosBase]; omega),
      ite_eq_right (by dsimp [dgVPosBase, dgExtToIntBase]; omega),
      ite_eq_right (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
      ite_eq_right (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega),
      ite_eq_right (by dsimp [dgEPresBase, dgEListBase]; omega),
      ite_eq_left (by dsimp [dgEListBase, dgEPosBase]; omega)]
  simp [show a - dgEListBase 0 (canonVCap G₀) (canonECap G₀) = i by dsimp [a]; omega]

lemma canonDGMemBase_ePos {G₀ : MGraph} {e : ℕ} (he : e < canonECap G₀) :
    canonDGMemBase G₀ (dgEPosBase 0 (canonVCap G₀) (canonECap G₀) + e) =
      (open Classical in if e ∈ G₀.E then (canonEList G₀).idxOf e else 0) := by
  classical
  set a := dgEPosBase 0 (canonVCap G₀) (canonECap G₀) + e
  have ha : a = 4 + 7 * canonVCap G₀ + 2 * canonECap G₀ + e := by simp [a, dgEPosBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_right (by dsimp [dgVListBase, dgVPosBase]; omega),
      ite_eq_right (by dsimp [dgVPosBase, dgExtToIntBase]; omega),
      ite_eq_right (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
      ite_eq_right (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega),
      ite_eq_right (by dsimp [dgEPresBase, dgEListBase]; omega),
      ite_eq_right (by dsimp [dgEListBase, dgEPosBase]; omega),
      ite_eq_left (by dsimp [dgEPosBase, dgETailSlotBase]; omega)]
  simp [show a - dgEPosBase 0 (canonVCap G₀) (canonECap G₀) = e by dsimp [a]; omega]

lemma canonDGMemBase_eTailSlot {G₀ : MGraph} {e : ℕ} (he : e < canonECap G₀) :
    canonDGMemBase G₀ (dgETailSlotBase 0 (canonVCap G₀) (canonECap G₀) + e) =
      (open Classical in if e ∈ G₀.E then G₀.tail e else 0) := by
  classical
  set a := dgETailSlotBase 0 (canonVCap G₀) (canonECap G₀) + e
  have ha : a = 4 + 7 * canonVCap G₀ + 3 * canonECap G₀ + e := by simp [a, dgETailSlotBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_right (by dsimp [dgVListBase, dgVPosBase]; omega),
      ite_eq_right (by dsimp [dgVPosBase, dgExtToIntBase]; omega),
      ite_eq_right (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
      ite_eq_right (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega),
      ite_eq_right (by dsimp [dgEPresBase, dgEListBase]; omega),
      ite_eq_right (by dsimp [dgEListBase, dgEPosBase]; omega),
      ite_eq_right (by dsimp [dgEPosBase, dgETailSlotBase]; omega),
      ite_eq_left (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega)]
  simp [show a - dgETailSlotBase 0 (canonVCap G₀) (canonECap G₀) = e by dsimp [a]; omega]

lemma canonDGMemBase_eHeadSlot {G₀ : MGraph} {e : ℕ} (he : e < canonECap G₀) :
    canonDGMemBase G₀ (dgEHeadSlotBase 0 (canonVCap G₀) (canonECap G₀) + e) =
      (open Classical in if e ∈ G₀.E then G₀.head e else 0) := by
  classical
  set a := dgEHeadSlotBase 0 (canonVCap G₀) (canonECap G₀) + e
  have ha : a = 4 + 7 * canonVCap G₀ + 4 * canonECap G₀ + e := by simp [a, dgEHeadSlotBase]
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_right (by dsimp [dgVListBase, dgVPosBase]; omega),
      ite_eq_right (by dsimp [dgVPosBase, dgExtToIntBase]; omega),
      ite_eq_right (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
      ite_eq_right (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega),
      ite_eq_right (by dsimp [dgEPresBase, dgEListBase]; omega),
      ite_eq_right (by dsimp [dgEListBase, dgEPosBase]; omega),
      ite_eq_right (by dsimp [dgEPosBase, dgETailSlotBase]; omega),
      ite_eq_right (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega),
      ite_eq_left (by dsimp [dgEHeadSlotBase, dgHePrevBase]; omega)]
  simp [show a - dgEHeadSlotBase 0 (canonVCap G₀) (canonECap G₀) = e by dsimp [a]; omega]

lemma canonDGMemBase_zero_ge_hePrev {G₀ : MGraph} {a : ℕ}
    (ha : dgHePrevBase 0 (canonVCap G₀) (canonECap G₀) ≤ a) :
    canonDGMemBase G₀ a = 0 := by
  have ha' : 4 + 7 * canonVCap G₀ + 5 * canonECap G₀ ≤ a := by dsimp [dgHePrevBase] at ha; omega
  unfold canonDGMemBase
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by dsimp [dgVPresBase, dgVListBase]; omega),
      ite_eq_right (by dsimp [dgVListBase, dgVPosBase]; omega),
      ite_eq_right (by dsimp [dgVPosBase, dgExtToIntBase]; omega),
      ite_eq_right (by dsimp [dgExtToIntBase, dgIntToExtBase]; omega),
      ite_eq_right (by dsimp [dgIntToExtBase, dgSlotDegBase]; omega),
      ite_eq_right (by dsimp [dgEPresBase, dgEListBase]; omega),
      ite_eq_right (by dsimp [dgEListBase, dgEPosBase]; omega),
      ite_eq_right (by dsimp [dgEPosBase, dgETailSlotBase]; omega),
      ite_eq_right (by dsimp [dgETailSlotBase, dgEHeadSlotBase]; omega),
      ite_eq_right (by dsimp [dgEHeadSlotBase, dgHePrevBase]; omega)]

end MinCostFlow.SparseCore.Program
