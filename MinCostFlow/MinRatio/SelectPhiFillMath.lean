module

public import MinCostFlow.MinRatio.SelectLevelBlocks
public import MinCostFlow.MinRatio.WireSelectKeyEval
public import MinCostFlow.MinRatio.WireSelectSplitPotModel
import MinCostFlow.LSF.Components
import MinCostFlow.LSF.Walks
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pure mathematical invariants and bridges for `selectPhiFill` (`SelectPhiFillMath`)

Provides the per-level frozen-potential invariant, the prefix memory invariant read by
`evalEdgePotGradBody`, and the pure forest-traversal / overflow-fit lemmas used by
`MinCostFlow.MinRatio.SelectPhiFill`:

* `SelectPotInvAt C g φ j`: per-level clause of `SelectPotInv` at level `j`, with
  `selectPotInv_iff_forall_at`, `potGrad_update_self_eq`, `selectPotInvAt_update_of_lt`, and
  `selectPotInvAt_of_edge_diff`.
* `SelectPhiPrefixAt` and `SelectPhiPrefixBelow`: the exact prefix of `SelectLevelMetaAt`
  (levels `0 .. j - 1` of `G` and `φ`, plus `g0` and metadata header) needed to evaluate
  `potGrad C g φ j f` while filling `φ_j`, with frame and step-extension lemmas.
* `PotGradEvalFits` and `ForestWalkFits`: exact signed no-overflow predicates for fixed-point
  evaluation of `potGrad C g φ j f` and tree-path accumulation on `F_j`, plus sufficient real
  magnitude bounds.
* `forest_m_le_n`: every forest `F` satisfies `F.m ≤ F.n` (so BFS over `F_j` visits at most
  `2 * F_j.n` half-edges and evaluates at most `F_j.n` tree edges).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Per-level `SelectPotInvAt` and edge-difference bridge -/

/-- `SelectPotInv` holds iff `SelectPotInvAt` holds at every level `j ≤ C.d`. -/
theorem selectPotInv_iff_forall_at (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) :
    SelectPotInv C g φ ↔ ∀ j ≤ C.d, SelectPotInvAt C g φ j := Iff.rfl

/-- Updating `φ` at level `j` does not change `potGrad C g φ k` for any `k ≤ j`. -/
theorem potGrad_update_eq_of_le (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ)
    (φj : ℕ → ℝ) {k j : ℕ} (hkj : k ≤ j) (e : ℕ) :
    potGrad C g (Function.update φ j φj) k e = potGrad C g φ k e := by
  rw [potGrad_eq_sum, potGrad_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i ≠ j := by
    have := Finset.mem_range.mp hi
    omega
  simp [Function.update_of_ne hij]

/-- Updating `φ` at level `j` preserves `SelectPotInvAt` at all earlier levels `k < j`. -/
theorem selectPotInvAt_update_of_lt (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ)
    (φj : ℕ → ℝ) {k j : ℕ} (hkj : k < j) :
    SelectPotInvAt C g (Function.update φ j φj) k ↔ SelectPotInvAt C g φ k := by
  unfold SelectPotInvAt
  have hne : k ≠ j := Nat.ne_of_lt hkj
  have hpg : potGrad C g (Function.update φ j φj) k = potGrad C g φ k :=
    funext fun e => potGrad_update_eq_of_le C g φ φj (Nat.le_of_lt hkj) e
  simp [hpg, Function.update_of_ne hne]

/-- If `φj (F.tail e) - φj (F.head e) = gCur e` on every edge `e ∈ F.E`, then `walkInner gCur W`
telescopes to `φj a - φj b` on every walk `F.IsWalk a b W`. -/
theorem walkInner_eq_sub_of_edge_diff {F : MGraph} {gCur φj : ℕ → ℝ}
    (hdiff : ∀ e ∈ F.E, φj (F.tail e) - φj (F.head e) = gCur e)
    {a b : ℕ} {W : List (ℕ × Bool)} (hW : F.IsWalk a b W) :
    walkInner gCur W = φj a - φj b := by
  induction hW with
  | nil u => simp [walkInner_nil]
  | @cons u v x rest he hsrc hrest ih =>
    rw [walkInner_cons, ih]
    rcases x with ⟨e, dir⟩
    have hde := hdiff e he
    cases dir
    · simp only [MGraph.src, MGraph.dst, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
      rw [walkInner_singleton]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← hsrc]
      linarith
    · simp only [MGraph.src, MGraph.dst, ↓reduceIte] at hsrc ⊢
      rw [walkInner_singleton]
      simp only [↓reduceIte]
      rw [← hsrc]
      linarith

/-- If `φj` satisfies the local tree-edge difference equation on `(C.activeLSF j).F.F` for
`potGrad C g φ j`, then `Function.update φ j φj` satisfies `SelectPotInvAt` at level `j`. -/
theorem selectPotInvAt_of_edge_diff {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ}
    {φj : ℕ → ℝ} {j : ℕ}
    (hdiff : ∀ e ∈ (C.activeLSF j).F.F.E,
      φj ((C.activeLSF j).F.F.tail e) - φj ((C.activeLSF j).F.F.head e) = potGrad C g φ j e) :
    SelectPotInvAt C g (Function.update φ j φj) j := by
  intro a b hconn
  have hpg : potGrad C g (Function.update φ j φj) j = potGrad C g φ j :=
    funext fun e => potGrad_update_eq_of_le C g φ φj le_rfl e
  rw [hpg, Function.update_self]
  exact walkInner_eq_sub_of_edge_diff hdiff (MGraph.isWalk_forestPath hconn)

/-! ## 2. Prefix memory layout for `evalEdgePotGradBody` and `selectPhiFill` -/

/-- The prefix of `SelectLevelMetaAt` read when evaluating `potGrad C g φ j f`: the metadata
header (`g0Ptr`, `d`), the base gradient `g` on `G_0`, and for every `k < j`, the metadata entries
`(GPtr, vCap, eCap, phiPtr)`, the graph `G_k`, and the frozen potentials `φ_k`. -/
def SelectPhiPrefixAt (mem : ℕ → ℕ) (mloc : SelectLevelMetaLoc) (h P : ℕ)
    (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) (j : ℕ) : Prop :=
  mloc.d = C.d ∧
  mem (mloc.metaBase + smG0Off) = mloc.g0Ptr ∧
  mem (mloc.metaBase + smDOff) = mloc.d ∧
  EdgeValuesAt mem mloc.g0Ptr h mloc.Lk P (C.G 0).E g ∧
  ∀ k < j,
    mem (smEntryAddr mloc.metaBase mloc.d 0 k) = mloc.GPtr k ∧
    mem (smEntryAddr mloc.metaBase mloc.d 1 k) = mloc.vCap k ∧
    mem (smEntryAddr mloc.metaBase mloc.d 2 k) = mloc.eCap k ∧
    mem (smEntryAddr mloc.metaBase mloc.d 3 k) = mloc.phiPtr k ∧
    DynGraphAt mem (mloc.GPtr k) (mloc.vCap k) (mloc.eCap k) (C.G k) ∧
    EdgeValuesAt mem (mloc.phiPtr k) h mloc.Lk P (C.G k).V (φ k)

/-- Address upper-bound condition placing all data read by `SelectPhiPrefixAt` at level `j`
strictly below `hi`. -/
def SelectPhiPrefixBelow (mloc : SelectLevelMetaLoc) (j hi : ℕ) : Prop :=
  mloc.metaBase + selectLevelMetaSize mloc.d ≤ hi ∧
  mloc.g0Ptr + mloc.eCap 0 * mloc.Lk ≤ hi ∧
  ∀ k < j,
    mloc.GPtr k + dynGraphSize (mloc.vCap k) (mloc.eCap k) ≤ hi ∧
    mloc.phiPtr k + mloc.vCap k * mloc.Lk ≤ hi

/-- Disjointness between `SelectPhiPrefixAt` at level `j` and the destination potential table
`[mloc.phiPtr j, mloc.phiPtr j + mloc.vCap j * mloc.Lk)`. -/
def SelectPhiTargetDisjoint (mloc : SelectLevelMetaLoc) (j hi : ℕ) : Prop :=
  let lo := mloc.phiPtr j
  let up := mloc.phiPtr j + mloc.vCap j * mloc.Lk
  up ≤ hi ∧
  mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ hi ∧
  (mloc.metaBase + selectLevelMetaSize mloc.d ≤ lo ∨ up ≤ mloc.metaBase) ∧
  (mloc.g0Ptr + mloc.eCap 0 * mloc.Lk ≤ lo ∨ up ≤ mloc.g0Ptr) ∧
  (mloc.fPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ lo ∨ up ≤ mloc.fPtr j) ∧
  ∀ k < j,
    (mloc.GPtr k + dynGraphSize (mloc.vCap k) (mloc.eCap k) ≤ lo ∨ up ≤ mloc.GPtr k) ∧
    (mloc.phiPtr k + mloc.vCap k * mloc.Lk ≤ lo ∨ up ≤ mloc.phiPtr k)

private theorem mul_add_lt_mul_cap {v c L i : ℕ} (hv : v < c) (hi : i < L) :
    v * L + i < c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at this
  omega

/-- Frame lemma for `SelectPhiPrefixAt`: agreeing on every address `< hi` preserves
`SelectPhiPrefixAt` when `SelectPhiPrefixBelow` holds. -/
theorem SelectPhiPrefixAt.of_agree_below {mem mem' : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P j hi : ℕ} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ}
    (hpre : SelectPhiPrefixAt mem mloc h P C g φ j)
    (hbel : SelectPhiPrefixBelow mloc j hi)
    (hj : j ≤ C.d + 1)
    (he0 : ∀ e ∈ (C.G 0).E, e < mloc.eCap 0)
    (hag : ∀ a < hi, mem' a = mem a) :
    SelectPhiPrefixAt mem' mloc h P C g φ j := by
  obtain ⟨hd, hg0p, hdp, hg0, hk⟩ := hpre
  obtain ⟨hmetaHi, hg0Hi, hkHi⟩ := hbel
  refine ⟨hd, ?_, ?_, ?_, fun k hkj => ?_⟩
  · rw [hag _ (by unfold smG0Off selectLevelMetaSize at *; omega)]; exact hg0p
  · rw [hag _ (by unfold smDOff selectLevelMetaSize at *; omega)]; exact hdp
  · refine EdgeValuesAt.congr hg0 fun e he i hiL => hag _ ?_
    have hlt := mul_add_lt_mul_cap (he0 e he) hiL
    omega
  · obtain ⟨h0, h1, h2, h3, hG, hPhi⟩ := hk k hkj
    obtain ⟨hGHi, hPhiHi⟩ := hkHi k hkj
    have hkd : k ≤ mloc.d := by omega
    have hEnt : ∀ blk ≤ 3, smEntryAddr mloc.metaBase mloc.d blk k < hi := fun blk hb => by
      have hm := Nat.mul_le_mul_right (mloc.d + 1) hb
      unfold smEntryAddr smTableOff selectLevelMetaSize at *; omega
    refine ⟨(hag _ (hEnt 0 (by omega))).trans h0, (hag _ (hEnt 1 (by omega))).trans h1,
      (hag _ (hEnt 2 (by omega))).trans h2, (hag _ (hEnt 3 (by omega))).trans h3,
      DynGraphAt.of_agree hG (fun a _ ha2 => hag a (lt_of_lt_of_le ha2 hGHi)),
      EdgeValuesAt.congr hPhi fun v hv i hiL => hag _ ?_⟩
    have hlt := mul_add_lt_mul_cap (hG.2.1 v hv) hiL
    omega

/-- Frame lemma for `SelectPhiPrefixAt` when writing inside `[mloc.phiPtr j, mloc.phiPtr j +
mloc.vCap j * mloc.Lk)` (and optionally at or above `hi`). -/
theorem SelectPhiPrefixAt.of_agree_outside_target {mem mem' : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P j hi : ℕ} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ}
    (hpre : SelectPhiPrefixAt mem mloc h P C g φ j)
    (hbel : SelectPhiPrefixBelow mloc j hi)
    (hdisj : SelectPhiTargetDisjoint mloc j hi)
    (hj : j ≤ C.d + 1)
    (he0 : ∀ e ∈ (C.G 0).E, e < mloc.eCap 0)
    (hag : ∀ a < hi, (a < mloc.phiPtr j ∨ mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ a) →
      mem' a = mem a) :
    SelectPhiPrefixAt mem' mloc h P C g φ j := by
  obtain ⟨hd, hg0p, hdp, hg0, hk⟩ := hpre
  obtain ⟨hmetaHi, hg0Hi, hkHi⟩ := hbel
  obtain ⟨_, _, hmetaD, hg0D, _, hkD⟩ := hdisj
  have hMetaEq : ∀ a, mloc.metaBase ≤ a → a < mloc.metaBase + selectLevelMetaSize mloc.d →
      mem' a = mem a := fun a h1 h2 => by
    apply hag a (lt_of_lt_of_le h2 hmetaHi)
    rcases hmetaD with h | h <;> [left; right] <;> omega
  refine ⟨hd, hMetaEq _ (by unfold smG0Off; omega) (by unfold smG0Off selectLevelMetaSize; omega) |>.trans hg0p,
    hMetaEq _ (by unfold smDOff; omega) (by unfold smDOff selectLevelMetaSize; omega) |>.trans hdp,
    ?_, fun k hkj => ?_⟩
  · refine EdgeValuesAt.congr hg0 fun e he i hiL => ?_
    have hlt := mul_add_lt_mul_cap (he0 e he) hiL
    apply hag _ (by omega)
    rcases hg0D with h | h <;> [left; right] <;> omega
  · obtain ⟨h0, h1, h2, h3, hG, hPhi⟩ := hk k hkj
    obtain ⟨hGHi, hPhiHi⟩ := hkHi k hkj
    obtain ⟨hGD, hPhiD⟩ := hkD k hkj
    have hkd : k ≤ mloc.d := by omega
    have hEnt : ∀ blk ≤ 3, mem' (smEntryAddr mloc.metaBase mloc.d blk k) =
        mem (smEntryAddr mloc.metaBase mloc.d blk k) := fun blk hb => by
      have hm := Nat.mul_le_mul_right (mloc.d + 1) hb
      apply hMetaEq
      · unfold smEntryAddr smTableOff; omega
      · unfold smEntryAddr smTableOff selectLevelMetaSize; omega
    refine ⟨(hEnt 0 (by omega)).trans h0, (hEnt 1 (by omega)).trans h1,
      (hEnt 2 (by omega)).trans h2, (hEnt 3 (by omega)).trans h3,
      DynGraphAt.of_agree hG (fun a h1 h2 => by
        apply hag a (lt_of_lt_of_le h2 hGHi)
        rcases hGD with h | h <;> [left; right] <;> omega),
      EdgeValuesAt.congr hPhi fun v hv i hiL => ?_⟩
    have hlt := mul_add_lt_mul_cap (hG.2.1 v hv) hiL
    apply hag _ (by omega)
    rcases hPhiD with h | h <;> [left; right] <;> omega

/-- Extending `SelectPhiPrefixAt` from level `j` to level `j + 1` once `φ_j` is written. -/
theorem SelectPhiPrefixAt.step {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P j : ℕ} {C : TreeChain} {g : ℕ → ℝ} {φ : ℕ → ℕ → ℝ} {φj : ℕ → ℝ}
    (hpre : SelectPhiPrefixAt mem mloc h P C g φ j)
    (hm0 : mem (smEntryAddr mloc.metaBase mloc.d 0 j) = mloc.GPtr j)
    (hm1 : mem (smEntryAddr mloc.metaBase mloc.d 1 j) = mloc.vCap j)
    (hm2 : mem (smEntryAddr mloc.metaBase mloc.d 2 j) = mloc.eCap j)
    (hm3 : mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j)
    (hGj : DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C.G j))
    (hPhij : EdgeValuesAt mem (mloc.phiPtr j) h mloc.Lk P (C.G j).V φj) :
    SelectPhiPrefixAt mem mloc h P C g (Function.update φ j φj) (j + 1) := by
  obtain ⟨hd, hg0p, hdp, hg0, hk⟩ := hpre
  refine ⟨hd, hg0p, hdp, hg0, fun k hkj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hkj with hlt | rfl
  · obtain ⟨a0, a1, a2, a3, aG, aPhi⟩ := hk k hlt
    exact ⟨a0, a1, a2, a3, aG, by rwa [Function.update_of_ne (Nat.ne_of_lt hlt)]⟩
  · exact ⟨hm0, hm1, hm2, hm3, hGj, by rwa [Function.update_self]⟩

/-- Project `SelectPhiPrefixAt` at any `j ≤ C.d + 1` from a full `SelectLevelMetaAt`. -/
theorem SelectPhiPrefixAt.of_selectLevelMetaAt {mem : ℕ → ℕ} {mloc : SelectLevelMetaLoc}
    {h P j : ℕ} {C : TreeChain} {g ℓ : ℕ → ℝ} {φ coreLen : ℕ → ℕ → ℝ}
    (hmeta : SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen) (hj : j ≤ C.d + 1) :
    SelectPhiPrefixAt mem mloc h P C g φ j := by
  obtain ⟨hd, hg0p, hdp, hent, hg0, hG, hPhi, _⟩ := hmeta
  refine ⟨hd, hg0p, hdp, hg0, fun k hkj => ?_⟩
  have hkd : k ≤ C.d := by omega
  obtain ⟨a0, a1, a2, a3, _⟩ := hent k hkd
  exact ⟨a0, a1, a2, a3, hG k hkd, hPhi k hkd⟩

/-! ## 3. Signed no-overflow conditions (`PotGradEvalFits`, `ForestWalkFits`) -/

/-- No-overflow condition for evaluating `potGrad C g φ j f` term-by-term with `Lk` limbs of `h`
bits at precision `P`. -/
def PotGradEvalFits (h Lk P : ℕ) (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) (j f : ℕ) : Prop :=
  ∀ k < j,
    (-(Num.capacity h Lk : ℝ) ≤ 2 * ((potGrad C g φ k f + φ k ((C.G k).head f)) * (2 : ℝ) ^ P) ∧
      2 * ((potGrad C g φ k f + φ k ((C.G k).head f)) * (2 : ℝ) ^ P) < (Num.capacity h Lk : ℝ)) ∧
    (-(Num.capacity h Lk : ℝ) ≤ 2 * (potGrad C g φ (k + 1) f * (2 : ℝ) ^ P) ∧
      2 * (potGrad C g φ (k + 1) f * (2 : ℝ) ^ P) < (Num.capacity h Lk : ℝ))

/-- No-overflow condition for accumulating `walkInner gCur W` along any simple path `W` in `F`
with `Lk` limbs of `h` bits at precision `P`. -/
def ForestWalkFits (h Lk P : ℕ) (F : MGraph) (gCur : ℕ → ℝ) : Prop :=
  ∀ u v W, F.IsPath u v W →
    -(Num.capacity h Lk : ℝ) ≤ 2 * (walkInner gCur W * (2 : ℝ) ^ P) ∧
    2 * (walkInner gCur W * (2 : ℝ) ^ P) < (Num.capacity h Lk : ℝ)

/-- Convert a real scaled range inequality on an integer value into `Num.Fits h Lk z`. -/
theorem fits_of_real_scaled {h Lk P : ℕ} {z : ℤ} {x : ℝ}
    (hx : x = (z : ℝ) / (2 : ℝ) ^ P)
    (hlo : -(Num.capacity h Lk : ℝ) ≤ 2 * (x * (2 : ℝ) ^ P))
    (hhi : 2 * (x * (2 : ℝ) ^ P) < (Num.capacity h Lk : ℝ)) :
    Num.Fits h Lk z := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ P := pow_pos zero_lt_two P
  have hmul : x * (2 : ℝ) ^ P = (z : ℝ) := by
    rw [hx, div_mul_cancel₀ _ hpow.ne']
  rw [hmul] at hlo hhi
  constructor
  · have h1 : ((-(Num.capacity h Lk : ℤ) : ℤ) : ℝ) ≤ ((2 * z : ℤ) : ℝ) := by
      simpa [Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hlo
    exact Int.cast_le.mp h1
  · have h2 : ((2 * z : ℤ) : ℝ) < ((Num.capacity h Lk : ℤ) : ℝ) := by
      simpa [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hhi
    exact Int.cast_lt.mp h2

/-- Sufficient uniform real magnitude bound for `PotGradEvalFits`. -/
theorem potGradEvalFits_of_bound {h Lk P j f : ℕ} {C : TreeChain} {g : ℕ → ℝ}
    {φ : ℕ → ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hg : |g f| ≤ B)
    (hphi : ∀ k < j, |φ k ((C.G k).head f)| ≤ B ∧ |φ k ((C.G k).tail f)| ≤ B)
    (hcap : 2 * (((2 * j + 1 : ℕ) : ℝ) * B * (2 : ℝ) ^ P) < (Num.capacity h Lk : ℝ)) :
    PotGradEvalFits h Lk P C g φ j f := by
  have hpgBound : ∀ k ≤ j, |potGrad C g φ k f| ≤ (2 * k + 1 : ℕ) * B := by
    intro k hk
    induction k with
    | zero => simpa [potGrad] using hg
    | succ k ih =>
      have hk1 := ih (Nat.le_of_lt hk)
      have hpk := hphi k hk
      rw [potGrad]
      have h1 : |potGrad C g φ k f + φ k ((C.G k).head f) - φ k ((C.G k).tail f)| ≤
          |potGrad C g φ k f| + |φ k ((C.G k).head f)| + |φ k ((C.G k).tail f)| := by
        calc |potGrad C g φ k f + φ k ((C.G k).head f) - φ k ((C.G k).tail f)|
            ≤ |potGrad C g φ k f + φ k ((C.G k).head f)| + |φ k ((C.G k).tail f)| :=
              abs_sub _ _
          _ ≤ |potGrad C g φ k f| + |φ k ((C.G k).head f)| + |φ k ((C.G k).tail f)| := by
              linarith [abs_add_le (potGrad C g φ k f) (φ k ((C.G k).head f))]
      have hcast : ((2 * (k + 1) + 1 : ℕ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      linarith [hpk.1, hpk.2]
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ P := le_of_lt (pow_pos zero_lt_two P)
  intro k hkj
  have hk0 := hpgBound k (Nat.le_of_lt hkj)
  have hk1 := hpgBound (k + 1) hkj
  have hpk := hphi k hkj
  have hmid : |potGrad C g φ k f + φ k ((C.G k).head f)| ≤ ((2 * j + 1 : ℕ) : ℝ) * B := by
    have hle : ((2 * k + 1 : ℕ) : ℝ) + 1 ≤ ((2 * j + 1 : ℕ) : ℝ) := by
      have : 2 * k + 2 ≤ 2 * j + 1 := by omega
      exact_mod_cast this
    calc |potGrad C g φ k f + φ k ((C.G k).head f)|
        ≤ |potGrad C g φ k f| + |φ k ((C.G k).head f)| := abs_add_le _ _
      _ ≤ ((2 * k + 1 : ℕ) : ℝ) * B + B := by linarith [hpk.1]
      _ = (((2 * k + 1 : ℕ) : ℝ) + 1) * B := by ring
      _ ≤ ((2 * j + 1 : ℕ) : ℝ) * B := mul_le_mul_of_nonneg_right hle hB
  have hnext : |potGrad C g φ (k + 1) f| ≤ ((2 * j + 1 : ℕ) : ℝ) * B := by
    have hle : ((2 * (k + 1) + 1 : ℕ) : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
      have : 2 * (k + 1) + 1 ≤ 2 * j + 1 := by omega
      exact_mod_cast this
    exact hk1.trans (mul_le_mul_of_nonneg_right hle hB)
  have hmid' := abs_le.mp hmid
  have hnext' := abs_le.mp hnext
  have hmul1 : -(((2 * j + 1 : ℕ) : ℝ) * B * (2 : ℝ) ^ P) ≤
      (potGrad C g φ k f + φ k ((C.G k).head f)) * (2 : ℝ) ^ P := by
    have := mul_le_mul_of_nonneg_right hmid'.1 hpow
    linarith
  have hmul2 : (potGrad C g φ k f + φ k ((C.G k).head f)) * (2 : ℝ) ^ P ≤
      ((2 * j + 1 : ℕ) : ℝ) * B * (2 : ℝ) ^ P :=
    mul_le_mul_of_nonneg_right hmid'.2 hpow
  have hmul3 : -(((2 * j + 1 : ℕ) : ℝ) * B * (2 : ℝ) ^ P) ≤
      potGrad C g φ (k + 1) f * (2 : ℝ) ^ P := by
    have := mul_le_mul_of_nonneg_right hnext'.1 hpow
    linarith
  have hmul4 : potGrad C g φ (k + 1) f * (2 : ℝ) ^ P ≤
      ((2 * j + 1 : ℕ) : ℝ) * B * (2 : ℝ) ^ P :=
    mul_le_mul_of_nonneg_right hnext'.2 hpow
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Sufficient uniform real magnitude bound for `ForestWalkFits`. -/
theorem forestWalkFits_of_bound {h Lk P : ℕ} {F : MGraph} {gCur : ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hg : ∀ e ∈ F.E, |gCur e| ≤ B)
    (hcap : 2 * ((F.m : ℝ) * B * (2 : ℝ) ^ P) < (Num.capacity h Lk : ℝ)) :
    ForestWalkFits h Lk P F gCur := by
  intro u v W hP
  have hnd : (W.map Prod.fst).Nodup := LSF.isPath_nodup_edges hP
  have habs : |walkInner gCur W| ≤ (F.m : ℝ) * B := by
    unfold walkInner
    calc |∑ e ∈ walkEdges W, gCur e * walkFlow W e|
        ≤ ∑ e ∈ walkEdges W, |gCur e * walkFlow W e| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ walkEdges W, B := by
          refine Finset.sum_le_sum fun e he => ?_
          rw [abs_mul, LSF.walkFlow_abs_of_nodup hnd e, ite_eq_left he, mul_one]
          obtain ⟨dir, hmem⟩ := LSF.mem_walkEdges_iff.mp he
          exact hg e (LSF.IsWalk_edges_mem hP.1 hmem)
      _ = ((walkEdges W).card : ℝ) * B := by simp
      _ ≤ (F.m : ℝ) * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          have hsub : walkEdges W ⊆ F.E := fun e he => by
            obtain ⟨dir, hmem⟩ := LSF.mem_walkEdges_iff.mp he
            exact LSF.IsWalk_edges_mem hP.1 hmem
          exact_mod_cast Finset.card_le_card hsub
  have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ P := le_of_lt (pow_pos zero_lt_two P)
  have hpair := abs_le.mp habs
  have h1 : -((F.m : ℝ) * B * (2 : ℝ) ^ P) ≤ walkInner gCur W * (2 : ℝ) ^ P := by
    have := mul_le_mul_of_nonneg_right hpair.1 hpow; linarith
  have h2 : walkInner gCur W * (2 : ℝ) ^ P ≤ (F.m : ℝ) * B * (2 : ℝ) ^ P :=
    mul_le_mul_of_nonneg_right hpair.2 hpow
  exact ⟨by linarith, by linarith⟩

/-! ## 4. Forest edge-count and simple-path extension lemmas -/

/-- Every forest has at most as many edges as vertices (`F.m ≤ F.n`). -/
theorem forest_m_le_n {F : MGraph} (hF : F.IsForest) : F.m ≤ F.n := by
  have h := LSF.forest_components_add_edges F hF
  change F.E.card ≤ F.V.card
  omega

/-- Extending a simple path `F.IsPath parent r W` by an edge `(f, dir)` from an unvisited `child`
(not appearing in `F.walkVertices parent W`) yields a simple path `F.IsPath child r ((f, dir) :: W)`. -/
theorem isPath_cons_of_not_mem_walkVertices {F : MGraph} {child parent r : ℕ}
    {e : ℕ × Bool} {W : List (ℕ × Bool)}
    (he : e.1 ∈ F.E) (hsrc : F.src e = child) (hdst : F.dst e = parent)
    (hP : F.IsPath parent r W) (hnot : child ∉ F.walkVertices parent W) :
    F.IsPath child r (e :: W) := by
  refine ⟨.cons he hsrc (hdst.symm ▸ hP.1), ?_⟩
  rw [LSF.walkVertices_cons, hdst]
  exact List.nodup_cons.mpr ⟨hnot, hP.2⟩

end MinCostFlow.MinRatio
