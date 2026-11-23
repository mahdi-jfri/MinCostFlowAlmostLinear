module

public import MinCostFlow.LSF.Program.Lca
public import MinCostFlow.LSF.Program.Utils
import Mathlib.Tactic.Linarith

/-!
# Spreading the edge values over their endpoints

This is the first half of the congestion computation. Each graph edge `t < m0` joins the
vertex indices `eu t` and `ev t` and carries a value `q t` (a `Kq`-limb block). Its tree path
leaves the subtree of a vertex `y ≠ r` exactly when one endpoint lies below `y` and the other does
not. So if we put `q t` at both endpoints and `-2 q t` at their lowest common ancestor `lc t`, the
sum over the subtree of `y` is `q t` when the path uses the parent edge of `y`, and `0` otherwise.

`congScatterProc` does this for all edges, adding into one `K`-limb block per vertex modulo the
block capacity: two calls of `addTo` and two of `subFrom` per edge, after the `lca` call and a
copy of `q t` into a zero-extended `K`-limb scratch block. The cost is `O(m0 (logCap + K))`.

`scatterWeight` is the coefficient of `q t` at the vertex `y`.

This file holds the definitions, the contract and the small lemmas. The four block updates of one
step are in `CongScatterTail`, and the main proof is in `CongScatter`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow.Num

@[expose] public section

/-- The coefficient of edge `t` at vertex `y`: one for each endpoint at `y`, minus two when the
lowest common ancestor of the endpoints is `y`. -/
def scatterWeight (eu ev lc : ℕ → ℕ) (t y : ℕ) : ℤ :=
  (if eu t = y then 1 else 0) + (if ev t = y then 1 else 0) - 2 * (if lc t = y then 1 else 0)

/-! ## Block lemmas -/

/-- The block of `y < n` ends inside an array of `n` blocks of size `K`. -/
lemma block_end_le {y n : ℕ} (K : ℕ) (hy : y < n) : y * K + K ≤ n * K := by
  have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hy)
  rwa [Nat.succ_mul] at this

/-- A block whose cells from `M` on are zero has the value of its first `M` cells. -/
lemma unsignedVal_extend_zero {mem : ℕ → ℕ} {h : ℕ} :
    ∀ {M K a : ℕ}, M ≤ K → (∀ i, M ≤ i → i < K → mem (a + i) = 0) →
      unsignedVal mem a h K = unsignedVal mem a h M
  | 0, K, a, _, hz => by
    rw [unsignedVal_zero (fun i hi => hz i (Nat.zero_le _) hi)]; rfl
  | M + 1, 0, a, hMK, _ => absurd hMK (by omega)
  | M + 1, K + 1, a, hMK, hz => by
    have hz' : ∀ i, M ≤ i → i < K → mem (a + 1 + i) = 0 := fun i hi1 hi2 => by
      rw [show a + 1 + i = a + (i + 1) by omega]; exact hz (i + 1) (by omega) (by omega)
    simp only [unsignedVal]
    rw [unsignedVal_extend_zero (M := M) (K := K) (a := a + 1) (by omega) hz']

/-- The value after `subFrom`, modulo the capacity. -/
lemma unsignedVal_emod_of_intVal_wrap {mem mem' : ℕ → ℕ} {a b h L : ℕ}
    (hi : intVal mem' a h L = wrap h L (intVal mem a h L - intVal mem b h L)) :
    (unsignedVal mem' a h L : ℤ) % (capacity h L : ℤ) =
      ((unsignedVal mem a h L : ℤ) - (unsignedVal mem b h L : ℤ)) % (capacity h L : ℤ) := by
  rw [← signedVal_emod, ← intVal, hi, wrap_emod, Int.sub_emod, intVal, intVal, signedVal_emod,
    signedVal_emod, ← Int.sub_emod]

/-- Changing the block of `y₀` by `c` modulo the capacity, and nothing else in the array,
changes the array state by `c` at `y₀`. -/
lemma blocks_update {mem mem' : ℕ → ℕ} {dPtr n K h y₀ : ℕ} {f : ℕ → ℤ} {c : ℤ}
    (hD : ∀ y < n, Valid mem (dPtr + y * K) h K ∧
      (unsignedVal mem (dPtr + y * K) h K : ℤ) % (capacity h K : ℤ) = f y % (capacity h K : ℤ))
    (hy₀ : y₀ < n) (hv' : Valid mem' (dPtr + y₀ * K) h K)
    (hu' : (unsignedVal mem' (dPtr + y₀ * K) h K : ℤ) % (capacity h K : ℤ) =
      ((unsignedVal mem (dPtr + y₀ * K) h K : ℤ) + c) % (capacity h K : ℤ))
    (hfr : ∀ z, z < dPtr + y₀ * K ∨ dPtr + y₀ * K + K ≤ z → mem' z = mem z) :
    ∀ y < n, Valid mem' (dPtr + y * K) h K ∧
      (unsignedVal mem' (dPtr + y * K) h K : ℤ) % (capacity h K : ℤ) =
        (f y + if y = y₀ then c else 0) % (capacity h K : ℤ) := by
  intro y hy
  by_cases hyy : y = y₀
  · subst hyy
    refine ⟨hv', ?_⟩
    rw [hu', if_pos rfl, Int.add_emod, (hD y hy).2, ← Int.add_emod]
  · have hdisj : dPtr + y * K + K ≤ dPtr + y₀ * K ∨ dPtr + y₀ * K + K ≤ dPtr + y * K := by
      rcases Nat.lt_or_gt_of_ne hyy with h1 | h1
      · left; have := Nat.mul_le_mul_right K (show y + 1 ≤ y₀ by omega); nlinarith
      · right; have := Nat.mul_le_mul_right K (show y₀ + 1 ≤ y by omega); nlinarith
    have hag : ∀ i < K, mem' (dPtr + y * K + i) = mem (dPtr + y * K + i) :=
      fun i hi => hfr _ (by omega)
    refine ⟨fun i hi => by rw [hag i hi]; exact (hD y hy).1 i hi, ?_⟩
    rw [unsignedVal_congr (mem' := mem) (a' := dPtr + y * K) hag, (hD y hy).2, if_neg hyy,
      add_zero]

/-! ## Lowest common ancestors are unique -/

lemma IsLcaOf.unique {n tM r : ℕ} {tl hd par pe dep : ℕ → ℕ}
    (hR : RootedArrays n tM r tl hd par pe dep) {x y z z' : ℕ} (hx : x < n)
    (h : IsLcaOf par dep z x y) (h' : IsLcaOf par dep z' x y) : z = z' := by
  have h1 : AncOf par dep z' z := h.2.2 z' h'.1 h'.2.1
  have h2 : AncOf par dep z z' := h'.2.2 z h.1 h.2.1
  have hz := h.1.lt hR hx
  have hz' := h'.1.lt hR hx
  exact h.1.eq_of_dep_eq hR hx h'.1 (le_antisymm (h2.dep_le hR hz') (h1.dep_le hR hz))

open Classical in
/-- The lowest common ancestor, when there is one. -/
noncomputable def lcaChoice (par dep : ℕ → ℕ) (x y : ℕ) : ℕ :=
  if hex : ∃ z, IsLcaOf par dep z x y then hex.choose else 0

lemma lcaChoice_eq {n tM r : ℕ} {tl hd par pe dep : ℕ → ℕ}
    (hR : RootedArrays n tM r tl hd par pe dep) {x y z : ℕ} (hx : x < n)
    (h : IsLcaOf par dep z x y) : lcaChoice par dep x y = z := by
  have hex : ∃ z, IsLcaOf par dep z x y := ⟨z, h⟩
  rw [lcaChoice, dif_pos hex]
  exact IsLcaOf.unique hR hx hex.choose_spec h

/-! ## The procedure -/

/-- One edge `t` (register `12`): look up the endpoints and their lowest common ancestor, copy
`q t` into the scratch block, and add it at the endpoints and subtract it twice at the
ancestor. -/
def congScatterBody (bLca bFill bCopy bAdd bSub : ℕ) : Stmt :=
  .assign 13 (.load (.bin .add (.reg 1) (.reg 12))) ;;
  .assign 14 (.load (.bin .add (.reg 2) (.reg 12))) ;;
  .call 15 bLca [.reg 13, .reg 14, .reg 8, .reg 9, .reg 10, .reg 11] ;;
  .call 16 bFill [.reg 7, .reg 6, .const 0] ;;
  .call 16 bCopy [.reg 7, .bin .add (.reg 3) (.bin .mul (.reg 12) (.reg 4)), .reg 4] ;;
  .call 16 bAdd [.bin .add (.reg 5) (.bin .mul (.reg 13) (.reg 6)), .reg 7, .reg 6] ;;
  .call 16 bAdd [.bin .add (.reg 5) (.bin .mul (.reg 14) (.reg 6)), .reg 7, .reg 6] ;;
  .call 16 bSub [.bin .add (.reg 5) (.bin .mul (.reg 15) (.reg 6)), .reg 7, .reg 6] ;;
  .call 16 bSub [.bin .add (.reg 5) (.bin .mul (.reg 15) (.reg 6)), .reg 7, .reg 6]

/-- Args: `[m0, euPtr, evPtr, qPtr, Kq, dPtr, K, tmpPtr, logCap, upPtr, depPtr, parPtr, n]`.
The last argument, the number of vertices, is not read; it names the range of the result. -/
def congScatterProc (bLca bFill bCopy bAdd bSub : ℕ) : Stmt :=
  forRange 12 (.const 0) (.reg 0) (congScatterBody bLca bFill bCopy bAdd bSub) ;;
  .ret (.const 0)

lemma congScatterProc_noRand (bLca bFill bCopy bAdd bSub : ℕ) :
    (congScatterProc bLca bFill bCopy bAdd bSub).NoRand := by
  simp [congScatterProc, congScatterBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `congScatterProc`. The tables of the tree, the endpoint arrays and the
values lie below the block array at `dPtr`; the scratch block follows the array. -/
def congScatterContract (w h : ℕ) : Contract where
  pre args mem := ∃ (m0 euPtr evPtr qPtr Kq dPtr K tmpPtr L upPtr depPtr parPtr n tM r : ℕ)
      (tl hd pe : ℕ → ℕ),
    args = [m0, euPtr, evPtr, qPtr, Kq, dPtr, K, tmpPtr, L, upPtr, depPtr, parPtr, n] ∧
    0 < h ∧ 2 * h + 2 ≤ w ∧ 16 ≤ 2 ^ w ∧ Kq ≤ K ∧
    RootedArrays n tM r tl hd (fun x => mem (parPtr + x)) pe (fun x => mem (depPtr + x)) ∧
    LcaTables w n L upPtr depPtr parPtr (fun x => mem (parPtr + x))
      (fun x => mem (depPtr + x)) mem ∧
    (∀ t < m0, mem (euPtr + t) < n ∧ mem (evPtr + t) < n) ∧
    (∀ t < m0, Valid mem (qPtr + t * Kq) h Kq) ∧
    euPtr + m0 ≤ dPtr ∧ evPtr + m0 ≤ dPtr ∧ qPtr + m0 * Kq ≤ dPtr ∧
    upPtr + n * L ≤ dPtr ∧ depPtr + n ≤ dPtr ∧ parPtr + n ≤ dPtr ∧
    dPtr + n * K ≤ tmpPtr ∧ tmpPtr + K < 2 ^ w ∧
    ∀ y < n, Valid mem (dPtr + y * K) h K
  post args mem ret mem' := ∃ (m0 euPtr evPtr qPtr Kq dPtr K tmpPtr L upPtr depPtr parPtr n
      : ℕ) (lc : ℕ → ℕ),
    args = [m0, euPtr, evPtr, qPtr, Kq, dPtr, K, tmpPtr, L, upPtr, depPtr, parPtr, n] ∧ ret = 0 ∧
    (∀ a, a < dPtr ∨ tmpPtr + K ≤ a → mem' a = mem a) ∧
    (∀ t < m0, IsLcaOf (fun x => mem (parPtr + x)) (fun x => mem (depPtr + x)) (lc t)
      (mem (euPtr + t)) (mem (evPtr + t)) ∧ lc t < n) ∧
    ∀ y < n, Valid mem' (dPtr + y * K) h K ∧
      (unsignedVal mem' (dPtr + y * K) h K : ℤ) % (capacity h K : ℤ) =
        ((unsignedVal mem (dPtr + y * K) h K : ℤ) +
          ∑ t ∈ Finset.range m0, (unsignedVal mem (qPtr + t * Kq) h Kq : ℤ) *
            scatterWeight (fun t => mem (euPtr + t)) (fun t => mem (evPtr + t)) lc t y) %
          (capacity h K : ℤ)
  cost args _ := args.getD 0 0 * (100 * args.getD 8 0 + 300 * args.getD 6 0 + 420) + 20

/-! ## Proof -/

lemma LcaTables.of_agree {w n L upPtr depPtr parPtr B : ℕ} {par dep : ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (hT : LcaTables w n L upPtr depPtr parPtr par dep mem) (hag : ∀ a < B, mem' a = mem a)
    (hu : upPtr + n * L ≤ B) (hd : depPtr + n ≤ B) (hp : parPtr + n ≤ B) :
    LcaTables w n L upPtr depPtr parPtr par dep mem' := by
  refine ⟨hT.hL, hT.hdep, fun i hi j hj => ?_, fun i hi => ?_, fun i hi => ?_, hT.hupW, hT.hdW,
    hT.hpW⟩
  · have : (i + 1) * L ≤ n * L := Nat.mul_le_mul_right _ hi
    rw [hag _ (by nlinarith)]; exact hT.hup i hi j hj
  · rw [hag _ (by omega)]; exact hT.hd i hi
  · rw [hag _ (by omega)]; exact hT.hp i hi

/-- The state between the calls of one step: the memory is unchanged outside the array and the
scratch block, the scratch block holds `qv`, and the array holds `f` modulo the capacity. -/
def ScatterMid (mem₀ mem : ℕ → ℕ) (dPtr n K tmpPtr h qv : ℕ) (f : ℕ → ℤ) : Prop :=
  (∀ a, a < dPtr ∨ tmpPtr + K ≤ a → mem a = mem₀ a) ∧ Valid mem tmpPtr h K ∧
    unsignedVal mem tmpPtr h K = qv ∧
    ∀ y < n, Valid mem (dPtr + y * K) h K ∧
      (unsignedVal mem (dPtr + y * K) h K : ℤ) % (capacity h K : ℤ) = f y % (capacity h K : ℤ)

/-- One `addTo` or `subFrom` call on the block of `y₀`, with the scratch block as the source. -/
lemma ScatterMid.step {mem₀ mem mem' : ℕ → ℕ} {dPtr n K tmpPtr h qv y₀ : ℕ} {f : ℕ → ℤ}
    {c : ℤ} (hM : ScatterMid mem₀ mem dPtr n K tmpPtr h qv f) (hy₀ : y₀ < n)
    (hle : dPtr + n * K ≤ tmpPtr) (hv' : Valid mem' (dPtr + y₀ * K) h K)
    (hu' : (unsignedVal mem' (dPtr + y₀ * K) h K : ℤ) % (capacity h K : ℤ) =
      ((unsignedVal mem (dPtr + y₀ * K) h K : ℤ) + c) % (capacity h K : ℤ))
    (hfr : ∀ z, z < dPtr + y₀ * K ∨ dPtr + y₀ * K + K ≤ z → mem' z = mem z) :
    ScatterMid mem₀ mem' dPtr n K tmpPtr h qv (fun y => f y + if y = y₀ then c else 0) := by
  have hb : y₀ * K + K ≤ n * K := by
    have := Nat.mul_le_mul_right K (show y₀ + 1 ≤ n by omega); nlinarith
  have htmp : ∀ i < K, mem' (tmpPtr + i) = mem (tmpPtr + i) := fun i _ => hfr _ (by omega)
  refine ⟨fun a ha => ?_, fun i hi => by rw [htmp i hi]; exact hM.2.1 i hi, ?_,
    blocks_update hM.2.2.2 hy₀ hv' hu' hfr⟩
  · rw [hfr a (by rcases ha with ha | ha <;> [left; right] <;> omega)]; exact hM.1 a ha
  · rw [unsignedVal_congr (mem' := mem) (a' := tmpPtr) htmp]; exact hM.2.2.1

lemma scatter_combine (a c : ℤ) (u v l y : ℕ) :
    a + (if y = u then c else 0) + (if y = v then c else 0) + (if y = l then -c else 0) +
        (if y = l then -c else 0) =
      a + c * ((if u = y then 1 else 0) + (if v = y then 1 else 0) -
        2 * (if l = y then 1 else 0)) := by
  simp only [eq_comm (a := u), eq_comm (a := v), eq_comm (a := l)]
  split_ifs <;> ring

/-- `ScatterMid` only sees the array state modulo the capacity, so it can be moved along a
pointwise equality of states. -/
lemma ScatterMid.congr_f {mem₀ mem : ℕ → ℕ} {dPtr n K tmpPtr h qv : ℕ} {f g : ℕ → ℤ}
    (hM : ScatterMid mem₀ mem dPtr n K tmpPtr h qv f) (hfg : ∀ y, f y = g y) :
    ScatterMid mem₀ mem dPtr n K tmpPtr h qv g :=
  ⟨hM.1, hM.2.1, hM.2.2.1, fun y hy => ⟨(hM.2.2.2 y hy).1, by rw [(hM.2.2.2 y hy).2, hfg]⟩⟩

end

end MinCostFlow.LSF.Program
