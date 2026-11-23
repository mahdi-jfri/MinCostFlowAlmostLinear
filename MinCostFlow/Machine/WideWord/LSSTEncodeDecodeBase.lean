module

public import MinCostFlow.Machine.WideWord.LSSTGraphCSR
public import MinCostFlow.Machine.WideWord.LSSTGAug
public import MinCostFlow.Machine.WideWord.LSSTWeightsBase
public import MinCostFlow.Machine.WideWord.Simulate
public import MinCostFlow.Machine.WideWord.Wrappers
public import MinCostFlow.Machine.WideWord.Compile
public import MinCostFlow.Machine.WideWord.ArithMulDiv
public import MinCostFlow.Num.PackWord
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Guest input encoding, simulation, and decoding procedures

This file provides the limb/encoding bridges, decoding step lemmas, procedures
(`encodeEdgeCopiesProc`, `encodeBridgesProc`, `encodeGAugProc`, `decodeOutProc`, `simDecodeProc`),
and module layout `encodeDecodeModule` for Theorem 2.2.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### List, limb, and encoding lemmas -/

theorem limbsAt_numValid {mem : ℕ → ℕ} {a L h x : ℕ}
    (hx : LimbsAt mem a L h x) : Num.Valid mem a h L :=
  fun _ hi => hx.limb_lt hi

theorem limbsAt_unsignedVal {mem : ℕ → ℕ} {a L h x : ℕ} (hh : 0 < h)
    (hx : LimbsAt mem a L h x) : Num.unsignedVal mem a h L = x := by
  have _ := hh
  exact LimbsAt.ext (limbsAt_of_numValid (limbsAt_numValid hx)) hx

theorem limbsAt_of_fromHost {mem : ℕ → ℕ} {dst L h x : ℕ}
    (hx : x < 2 ^ (L * h))
    (hd : ∀ i < L, mem (dst + i) = (x / 2 ^ (i * h)) % 2 ^ h) :
    LimbsAt mem dst L h x :=
  limbsAt_iff_pointwise.mpr ⟨hx, hd⟩

theorem limbsAt_of_copy_zeroExt {mem mem' : ℕ → ℕ} {src dst K L h x : ℕ}
    (hKL : K ≤ L) (hx : LimbsAt mem src K h x)
    (hcopy : ∀ i < K, mem' (dst + i) = mem (src + i))
    (hzero : ∀ i, K ≤ i → i < L → mem' (dst + i) = 0) :
    LimbsAt mem' dst L h x := by
  have hlt_K : x < 2 ^ (K * h) := hx.lt_pow
  have hlt_L : x < 2 ^ (L * h) :=
    lt_of_lt_of_le hlt_K (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right h hKL))
  refine limbsAt_iff_pointwise.mpr ⟨hlt_L, fun i hi => ?_⟩
  by_cases hiK : i < K
  · rw [hcopy i hiK, (limbsAt_iff_pointwise.mp hx).2 i hiK]
  · have hge : K ≤ i := Nat.le_of_not_lt hiK
    rw [hzero i hge hi]
    have hpow : 2 ^ (K * h) ≤ 2 ^ (i * h) :=
      Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right h hge)
    have hdiv0 : x / 2 ^ (i * h) = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hlt_K hpow)
    simp [hdiv0]

private theorem flatMap_triples_length (es : List (ℕ × ℕ × ℕ)) :
    (es.flatMap fun e => [e.1, e.2.1, e.2.2]).length = 3 * es.length := by
  induction es with
  | nil => rfl
  | cons _ _ ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
      omega

private theorem flatMap_triples_getElem (es : List (ℕ × ℕ × ℕ)) :
    ∀ idx (hidx : idx < es.length),
      (es.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * idx]'(by rw [flatMap_triples_length]; omega) = (es[idx]'hidx).1 ∧
      (es.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * idx + 1]'(by rw [flatMap_triples_length]; omega) = (es[idx]'hidx).2.1 ∧
      (es.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * idx + 2]'(by rw [flatMap_triples_length]; omega) = (es[idx]'hidx).2.2 := by
  induction es with
  | nil => intro idx hidx; simp at hidx
  | cons e rest ih =>
      intro idx hidx
      cases idx with
      | zero => simp
      | succ k =>
          have hk : k < rest.length := Nat.lt_of_succ_lt_succ hidx
          simpa [Nat.mul_succ, Nat.add_assoc] using ih k hk

private theorem flatMap_replicate_length {α β : Type} (xs : List α) (cnt : α → ℕ) (f : α → β) :
    (xs.flatMap fun a => List.replicate (cnt a) (f a)).length = (xs.map cnt).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_replicate,
        List.map_cons, List.sum_cons, ih]

private theorem flatMap_replicate_getElem {α β : Type} (xs : List α) (cnt : α → ℕ) (f : α → β) :
    ∀ j (hj : j < xs.length) c (hc : c < cnt (xs[j]'hj)),
      ((xs.flatMap fun a => List.replicate (cnt a) (f a))[((xs.take j).map cnt).sum + c]'(by
        rw [flatMap_replicate_length]
        have hdrop : xs = xs.take j ++ xs[j]'hj :: xs.drop (j + 1) := by
          have h1 : xs.take j ++ xs[j]'hj :: xs.drop (j + 1) =
              (xs.take j ++ [xs[j]'hj]) ++ xs.drop (j + 1) := by simp
          rw [h1, List.take_append_getElem hj, List.take_append_drop]
        calc ((xs.take j).map cnt).sum + c < ((xs.take j).map cnt).sum + cnt (xs[j]'hj) := by omega
          _ ≤ (xs.map cnt).sum := by
              conv_rhs => rw [hdrop]
              simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
              omega)) = f (xs[j]'hj) := by
  induction xs with
  | nil => intro j hj; simp at hj
  | cons x xs ih =>
      intro j hj c hc
      cases j with
      | zero =>
          simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
            List.flatMap_cons, List.getElem_cons_zero] at hc ⊢
          rw [List.getElem_append_left (by simp [hc])]
          exact List.getElem_replicate (h := by simp [hc])
      | succ j' =>
          have hj' : j' < xs.length := Nat.lt_of_succ_lt_succ hj
          have hc' : c < cnt (xs[j']'hj') := by simpa using hc
          have ihj := ih j' hj' c hc'
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatMap_cons,
            List.getElem_cons_succ]
          have hbound_r : cnt x + (((xs.take j').map cnt).sum + c) <
              (List.replicate (cnt x) (f x) ++
                xs.flatMap fun a => List.replicate (cnt a) (f a)).length := by
            rw [List.length_append, List.length_replicate, flatMap_replicate_length]
            have hdrop' : xs = xs.take j' ++ xs[j']'hj' :: xs.drop (j' + 1) := by
              have h1 : xs.take j' ++ xs[j']'hj' :: xs.drop (j' + 1) =
                  (xs.take j' ++ [xs[j']'hj']) ++ xs.drop (j' + 1) := by simp
              rw [h1, List.take_append_getElem hj', List.take_append_drop]
            have hle_sum : ((xs.take j').map cnt).sum + cnt (xs[j']'hj') ≤ (xs.map cnt).sum := by
              conv_rhs => rw [hdrop']
              simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
              omega
            omega
          have hbound_l : cnt x + ((xs.take j').map cnt).sum + c <
              (List.replicate (cnt x) (f x) ++
                xs.flatMap fun a => List.replicate (cnt a) (f a)).length := by
            rw [Nat.add_assoc]; exact hbound_r
          have hcon : (List.replicate (cnt x) (f x) ++
                xs.flatMap fun a => List.replicate (cnt a) (f a))[cnt x +
                  ((xs.take j').map cnt).sum + c]'hbound_l =
              (List.replicate (cnt x) (f x) ++
                xs.flatMap fun a => List.replicate (cnt a) (f a))[cnt x +
                  (((xs.take j').map cnt).sum + c)]'hbound_r := by
            congr 1; exact Nat.add_assoc _ _ _
          have hle : (List.replicate (cnt x) (f x)).length ≤
              cnt x + (((xs.take j').map cnt).sum + c) := by
            simp only [List.length_replicate]; omega
          rw [hcon, List.getElem_append_right hle]
          simpa [List.length_replicate, Nat.add_sub_cancel_left] using ihj

private theorem exists_copy_index_of_lt_sum (nl : List ℕ) (mult : ℕ → ℕ) :
    ∀ q, q < (nl.map mult).sum →
      ∃ (j : ℕ) (hj : j < nl.length) (c : ℕ) (_hc : c < mult (nl[j]'hj)),
        q = ((nl.take j).map mult).sum + c := by
  induction nl with
  | nil => intro q hq; simp at hq
  | cons e rest ih =>
      intro q hq
      simp only [List.map_cons, List.sum_cons] at hq
      by_cases hqe : q < mult e
      · exact ⟨0, by simp, q, by simpa using hqe, by simp⟩
      · have hq' : q - mult e < (rest.map mult).sum := by omega
        obtain ⟨j', hj', c, hc, heq⟩ := ih (q - mult e) hq'
        refine ⟨j' + 1, by simp [hj'], c, by simpa using hc, ?_⟩
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
        omega

theorem limbsAt_gAug_encode_of_pieces {G : IndexedGraph} {V_list B : List ℕ}
    {mult w_orig : ℕ → ℕ} {mem : ℕ → ℕ} {outArr L_sim h : ℕ}
    (h0 : LimbsAt mem outArr L_sim h V_list.length)
    (h1 : LimbsAt mem (outArr + L_sim) L_sim h (((nonloopEdges G).map mult).sum + B.length))
    (hedge : ∀ (j : ℕ) (hj : j < (nonloopEdges G).length) c, c < mult ((nonloopEdges G)[j]'hj) →
      let idx := (((nonloopEdges G).take j).map mult).sum + c
      LimbsAt mem (outArr + (2 + 3 * idx) * L_sim) L_sim h (V_list.idxOf (G.tail ((nonloopEdges G)[j]'hj))) ∧
      LimbsAt mem (outArr + (2 + 3 * idx + 1) * L_sim) L_sim h (V_list.idxOf (G.head ((nonloopEdges G)[j]'hj))) ∧
      LimbsAt mem (outArr + (2 + 3 * idx + 2) * L_sim) L_sim h (w_orig ((nonloopEdges G)[j]'hj)))
    (hbridge : ∀ (k : ℕ) (hk : k < B.length),
      let idx := ((nonloopEdges G).map mult).sum + k
      LimbsAt mem (outArr + (2 + 3 * idx) * L_sim) L_sim h 0 ∧
      LimbsAt mem (outArr + (2 + 3 * idx + 1) * L_sim) L_sim h (V_list.idxOf (B[k]'hk)) ∧
      LimbsAt mem (outArr + (2 + 3 * idx + 2) * L_sim) L_sim h 1) :
    let G_aug := buildGAug G V_list B mult w_orig
    ∀ i (hi : i < G_aug.encode.length),
      LimbsAt mem (outArr + i * L_sim) L_sim h (G_aug.encode[i]'hi) := by
  intro G_aug i hi
  let nl := nonloopEdges G
  let m₁ := (nl.map mult).sum
  let lhs := nl.flatMap fun e =>
    List.replicate (mult e) (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)
  let rhs := B.map fun b => (0, V_list.idxOf b, 1)
  have hlhs_len : lhs.length = m₁ := flatMap_replicate_length nl mult _
  have hrhs_len : rhs.length = B.length := List.length_map _
  have hm_eq : G_aug.edges.length = m₁ + B.length := by
    change (lhs ++ rhs).length = m₁ + B.length
    rw [List.length_append, hlhs_len, hrhs_len]
  have henc_len : G_aug.encode.length = 2 + 3 * (m₁ + B.length) := by
    simp only [Cited.WGraph.encode, List.length_cons, flatMap_triples_length, hm_eq]
    omega
  rcases i with _ | _ | p
  · simpa [G_aug, Cited.WGraph.encode, buildGAug] using h0
  · simpa [G_aug, Cited.WGraph.encode, Cited.WGraph.m, buildGAug, hlhs_len, hrhs_len,
      Nat.one_mul] using h1
  · have hp_lt : p < 3 * G_aug.edges.length := by
      rw [hm_eq]; rw [henc_len] at hi; omega
    let q := p / 3
    let r := p % 3
    have hq_lt : q < G_aug.edges.length := Nat.div_lt_of_lt_mul (by omega)
    have hr_lt : r < 3 := Nat.mod_lt p (by omega)
    have hp_decomp : p = 3 * q + r := by omega
    have hget_tri := flatMap_triples_getElem G_aug.edges q hq_lt
    have hi' : p + 2 < G_aug.encode.length := hi
    have heq_p : G_aug.encode[p + 2]'hi' =
        (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[p]'(by
          rw [flatMap_triples_length]; exact hp_lt) := by rfl
    have heq_addr : outArr + (p + 1 + 1) * L_sim = outArr + (2 + 3 * q + r) * L_sim := by
      rw [show p + 1 + 1 = 2 + (3 * q + r) by omega]; ring
    change LimbsAt mem (outArr + (p + 1 + 1) * L_sim) L_sim h (G_aug.encode[p + 2]'hi')
    rw [heq_p, heq_addr]
    have hp_len : 3 * q + r < (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2]).length := by
      rw [flatMap_triples_length, ← hp_decomp]; exact hp_lt
    have hflat_eq : (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[p]'(by
        rw [flatMap_triples_length]; exact hp_lt) =
        (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q + r]'hp_len := by
      congr 1
    rw [hflat_eq]
    have hq_lr : q < (lhs ++ rhs).length := by
      rw [List.length_append, hlhs_len, hrhs_len]; rw [hm_eq] at hq_lt; exact hq_lt
    have he_get : G_aug.edges[q]'hq_lt = (lhs ++ rhs)[q]'hq_lr := rfl
    by_cases hqm : q < m₁
    · obtain ⟨j, hj, c, hc, hq_sum⟩ := exists_copy_index_of_lt_sum nl mult q hqm
      have hlhs_get := flatMap_replicate_getElem nl mult
        (fun e => (V_list.idxOf (G.tail e), V_list.idxOf (G.head e), w_orig e)) j hj c hc
      have hq_lhs : q < lhs.length := by rw [hlhs_len]; exact hqm
      have hedge_q : G_aug.edges[q]'hq_lt =
          (V_list.idxOf (G.tail (nl[j]'hj)), V_list.idxOf (G.head (nl[j]'hj)), w_orig (nl[j]'hj)) := by
        rw [he_get, List.getElem_append_left hq_lhs]
        have hq_idx : ((nl.take j).map mult).sum + c < lhs.length := by rw [← hq_sum]; exact hq_lhs
        have hcon : (lhs)[q]'hq_lhs = lhs[((nl.take j).map mult).sum + c]'hq_idx := by congr 1
        exact hcon.trans hlhs_get
      have hpc := hedge j hj c hc
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with hr_r | hr_r | hr_r
      · have hp_len0 : 3 * q < (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2]).length := by
          simpa [hr_r] using hp_len
        have hidx0 : (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q + r]'hp_len =
            (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q]'hp_len0 := by congr 1; simp [hr_r]
        have haddr0 : outArr + (2 + 3 * q + r) * L_sim =
            outArr + (2 + 3 * (((nl.take j).map mult).sum + c)) * L_sim := by
          rw [hr_r, hq_sum, Nat.add_zero]
        rw [hidx0, hget_tri.1, hedge_q, haddr0]; exact hpc.1
      · have hp_len1 : 3 * q + 1 < (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2]).length := by
          simpa [hr_r] using hp_len
        have hidx1 : (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q + r]'hp_len =
            (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q + 1]'hp_len1 := by congr 1; simp [hr_r]
        have haddr1 : outArr + (2 + 3 * q + r) * L_sim =
            outArr + (2 + 3 * (((nl.take j).map mult).sum + c) + 1) * L_sim := by
          rw [hr_r, hq_sum]
        rw [hidx1, hget_tri.2.1, hedge_q, haddr1]; exact hpc.2.1
      · have hp_len2 : 3 * q + 2 < (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2]).length := by
          simpa [hr_r] using hp_len
        have hidx2 : (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q + r]'hp_len =
            (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q + 2]'hp_len2 := by congr 1; simp [hr_r]
        have haddr2 : outArr + (2 + 3 * q + r) * L_sim =
            outArr + (2 + 3 * (((nl.take j).map mult).sum + c) + 2) * L_sim := by
          rw [hr_r, hq_sum]
        rw [hidx2, hget_tri.2.2, hedge_q, haddr2]; exact hpc.2.2
    · have hqm_ge : m₁ ≤ q := Nat.le_of_not_lt hqm
      have hk_lt : q - m₁ < B.length := by rw [hm_eq] at hq_lt; omega
      have hqm_ge' : lhs.length ≤ q := by rw [hlhs_len]; exact hqm_ge
      have hk_rhs : q - lhs.length < rhs.length := by rw [hlhs_len, hrhs_len]; exact hk_lt
      have hedge_q : G_aug.edges[q]'hq_lt = (0, V_list.idxOf (B[q - m₁]'hk_lt), 1) := by
        rw [he_get, List.getElem_append_right hqm_ge']
        have hcon : rhs[q - lhs.length]'hk_rhs = (B.map fun b => (0, V_list.idxOf b, 1))[q - m₁]'(by simpa [hrhs_len] using hk_lt) := by
          congr 1; simp [hlhs_len]
        rw [hcon]; simp
      have hbr := hbridge (q - m₁) hk_lt
      have hq_eq : m₁ + (q - m₁) = q := by omega
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with hr_r | hr_r | hr_r
      · have hp_len0 : 3 * q < (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2]).length := by
          simpa [hr_r] using hp_len
        have hidx0 : (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q + r]'hp_len =
            (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q]'hp_len0 := by congr 1; simp [hr_r]
        have haddr0 : outArr + (2 + 3 * q + r) * L_sim =
            outArr + (2 + 3 * (m₁ + (q - m₁))) * L_sim := by rw [hr_r, hq_eq, Nat.add_zero]
        rw [hidx0, hget_tri.1, hedge_q, haddr0]; exact hbr.1
      · have hp_len1 : 3 * q + 1 < (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2]).length := by
          simpa [hr_r] using hp_len
        have hidx1 : (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q + r]'hp_len =
            (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q + 1]'hp_len1 := by congr 1; simp [hr_r]
        have haddr1 : outArr + (2 + 3 * q + r) * L_sim =
            outArr + (2 + 3 * (m₁ + (q - m₁)) + 1) * L_sim := by rw [hr_r, hq_eq]
        rw [hidx1, hget_tri.2.1, hedge_q, haddr1]; exact hbr.2.1
      · have hp_len2 : 3 * q + 2 < (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2]).length := by
          simpa [hr_r] using hp_len
        have hidx2 : (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q + r]'hp_len =
            (G_aug.edges.flatMap fun e => [e.1, e.2.1, e.2.2])[3 * q + 2]'hp_len2 := by congr 1; simp [hr_r]
        have haddr2 : outArr + (2 + 3 * q + r) * L_sim =
            outArr + (2 + 3 * (m₁ + (q - m₁)) + 2) * L_sim := by rw [hr_r, hq_eq]
        rw [hidx2, hget_tri.2.2, hedge_q, haddr2]; exact hbr.2.2

theorem decodeAN19_step_lt (out : List ℕ) (m₁ : ℕ) (origs : List ℕ)
    (i : ℕ) (hi : i < out.length) (hlt : out[i]'hi < m₁) :
    ((out.take (i + 1)).filter (· < m₁)).map (fun j => origs.getD j 0) =
      ((out.take i).filter (· < m₁)).map (fun j => origs.getD j 0) ++ [origs.getD (out[i]'hi) 0] := by
  rw [List.take_succ_eq_append_getElem hi, List.filter_append]
  simp [hlt]

theorem decodeAN19_step_ge (out : List ℕ) (m₁ : ℕ) (origs : List ℕ)
    (i : ℕ) (hi : i < out.length) (hge : m₁ ≤ out[i]'hi) :
    ((out.take (i + 1)).filter (· < m₁)).map (fun j => origs.getD j 0) =
      ((out.take i).filter (· < m₁)).map (fun j => origs.getD j 0) := by
  rw [List.take_succ_eq_append_getElem hi, List.filter_append]
  simp [Nat.not_lt_of_ge hge]

theorem decodeAN19_bridge_step_mem (out : List ℕ) (m₁ : ℕ) (B : List ℕ) (r₀ : ℕ)
    (i : ℕ) (hi : i < out.length) (hge : m₁ ≤ out[i]'hi) (hlt : out[i]'hi < m₁ + B.length) :
    ((out.take (i + 1)).filter fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)).map
        (fun j => (r₀, B.getD (j - m₁) 0)) =
      ((out.take i).filter fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)).map
        (fun j => (r₀, B.getD (j - m₁) 0)) ++ [(r₀, B.getD ((out[i]'hi) - m₁) 0)] := by
  rw [List.take_succ_eq_append_getElem hi, List.filter_append]
  simp [hge, hlt]

theorem decodeAN19_bridge_step_skip (out : List ℕ) (m₁ : ℕ) (B : List ℕ) (r₀ : ℕ)
    (i : ℕ) (hi : i < out.length) (hnot : ¬ (m₁ ≤ out[i]'hi ∧ out[i]'hi < m₁ + B.length)) :
    ((out.take (i + 1)).filter fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)).map
        (fun j => (r₀, B.getD (j - m₁) 0)) =
      ((out.take i).filter fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)).map
        (fun j => (r₀, B.getD (j - m₁) 0)) := by
  rw [List.take_succ_eq_append_getElem hi, List.filter_append]
  simp [hnot]

/-! ### Procedures and module definition -/

def idxEncodeEdgeCopies : ℕ := 0
def idxEncodeBridges : ℕ := 1
def idxEncodeGAug : ℕ := 2
def idxDecodeOut : ℕ := 3
def idxSimDecode : ℕ := 4

/-- Encode `cnt` copies of edge `(uIdx, vIdx, wSrc)` into `3 * cnt * L_sim` limbs starting at
`pos`, and write `origVal` to `origPtr[origIdx .. origIdx + cnt - 1]`. Returns the new cursor
`pos + cnt * (3 * L_sim)`.
Args: `[uIdx, vIdx, wSrc, K, cnt, L_sim, B, pos, origPtr, origIdx, origVal]`. -/
def encodeEdgeCopiesProc (arithBase : ℕ) : Stmt :=
  .assign 11 (.reg 7) ;;
  .assign 12 (.bin .sub (.reg 5) (.reg 3)) ;;
  forRange 13 (.const 0) (.reg 4)
    (.store (.bin .add (.reg 8) (.bin .add (.reg 9) (.reg 13))) (.reg 10) ;;
     .call 14 (arithBase + idxFromHost) [.reg 0, .reg 11, .reg 5, .reg 6] ;;
     .assign 11 (.bin .add (.reg 11) (.reg 5)) ;;
     .call 14 (arithBase + idxFromHost) [.reg 1, .reg 11, .reg 5, .reg 6] ;;
     .assign 11 (.bin .add (.reg 11) (.reg 5)) ;;
     .call 14 (arithBase + idxCopy) [.reg 2, .reg 11, .reg 3] ;;
     .call 14 (arithBase + idxZero) [.bin .add (.reg 11) (.reg 3), .reg 12] ;;
     .assign 11 (.bin .add (.reg 11) (.reg 5))) ;;
  .ret (.reg 11)

/-- Encode `B_len` bridge edges `(0, vIdx[bArr[k]], 1)` into `3 * B_len * L_sim` limbs starting
at `pos`. Returns `pos + B_len * (3 * L_sim)`.
Args: `[B_len, bArr, vIdxPtr, L_sim, B, pos]`. -/
def encodeBridgesProc (arithBase : ℕ) : Stmt :=
  .assign 6 (.reg 5) ;;
  forRange 7 (.const 0) (.reg 0)
    (.call 8 (arithBase + idxZero) [.reg 6, .reg 3] ;;
     .assign 6 (.bin .add (.reg 6) (.reg 3)) ;;
     .assign 8 (.load (.bin .add (.reg 1) (.reg 7))) ;;
     .assign 8 (.load (.bin .add (.reg 2) (.reg 8))) ;;
     .call 9 (arithBase + idxFromHost) [.reg 8, .reg 6, .reg 3, .reg 4] ;;
     .assign 6 (.bin .add (.reg 6) (.reg 3)) ;;
     .call 8 (arithBase + idxFromHost) [.const 1, .reg 6, .reg 3, .reg 4] ;;
     .assign 6 (.bin .add (.reg 6) (.reg 3))) ;;
  .ret (.reg 6)

/-- Write `G_aug.encode` in `L_sim`-limb base-`2^h` blocks at `outArr` and populate `origPtr`
with `origOfCopy G mult`. Returns `m₁ = ∑ mult`.
Args: `[nlCnt, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K, Vcnt, B_len, bArr, L_sim, B, origPtr, outArr]`. -/
def encodeGAugProc (arithBase encodeBase : ℕ) : Stmt :=
  .assign 15 (.const 0) ;;
  forRange 16 (.const 0) (.reg 0)
    (.assign 15 (.bin .add (.reg 15) (.load (.bin .add (.reg 5) (.reg 16))))) ;;
  .assign 16 (.bin .add (.reg 15) (.reg 9)) ;;
  .call 17 (arithBase + idxFromHost) [.reg 8, .reg 14, .reg 11, .reg 12] ;;
  .call 17 (arithBase + idxFromHost) [.reg 16, .bin .add (.reg 14) (.reg 11), .reg 11, .reg 12] ;;
  .assign 17 (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 11))) ;;
  .assign 18 (.const 0) ;;
  forRange 19 (.const 0) (.reg 0)
    (.assign 20 (.load (.bin .add (.reg 1) (.reg 19))) ;;
     .assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
     .assign 21 (.load (.bin .add (.reg 4) (.reg 21))) ;;
     .assign 22 (.load (.bin .add (.reg 3) (.reg 20))) ;;
     .assign 22 (.load (.bin .add (.reg 4) (.reg 22))) ;;
     .assign 23 (.bin .add (.reg 6) (.bin .mul (.reg 19) (.reg 7))) ;;
     .assign 24 (.load (.bin .add (.reg 5) (.reg 19))) ;;
     .call 17 (encodeBase + idxEncodeEdgeCopies)
       [.reg 21, .reg 22, .reg 23, .reg 7, .reg 24, .reg 11, .reg 12, .reg 17, .reg 13, .reg 18, .reg 20] ;;
     .assign 18 (.bin .add (.reg 18) (.reg 24))) ;;
  .call 17 (encodeBase + idxEncodeBridges) [.reg 9, .reg 10, .reg 4, .reg 11, .reg 12, .reg 17] ;;
  .ret (.reg 15)

/-- Pack `outLen` `L_sim`-limb words from `outLimbsPtr` and decode them using `origsPtr`, `bArr`,
and `inactArr` into `outOrigPtr` and `outBridgePtr`, storing `(origCnt, bridgeCnt)` at
`[outHdrPtr, outHdrPtr + 1]`.
Args: `[outLimbsPtr, outLen, m₁, B_len, bArr, inactLen, inactArr, r₀, L_sim, origsPtr, outOrigPtr, outBridgePtr, outHdrPtr]`. -/
def decodeOutProc (packBase : ℕ) : Stmt :=
  .assign 13 (.const 0) ;;
  .assign 14 (.const 0) ;;
  forRange 15 (.const 0) (.reg 1)
    (.assign 16 (.bin .add (.reg 0) (.bin .mul (.reg 15) (.reg 8))) ;;
     .call 17 packBase [.reg 16, .reg 8] ;;
     .cond (.bin .lt (.reg 17) (.reg 2))
       (.assign 18 (.load (.bin .add (.reg 9) (.reg 17))) ;;
        .store (.bin .add (.reg 10) (.reg 13)) (.reg 18) ;;
        .assign 13 (.bin .add (.reg 13) (.const 1)))
       (.cond (.bin .lt (.reg 17) (.bin .add (.reg 2) (.reg 3)))
         (.assign 18 (.bin .sub (.reg 17) (.reg 2)) ;;
          .assign 18 (.load (.bin .add (.reg 4) (.reg 18))) ;;
          .assign 19 (.bin .mul (.const 2) (.reg 14)) ;;
          .store (.bin .add (.reg 11) (.reg 19)) (.reg 7) ;;
          .store (.bin .add (.reg 11) (.bin .add (.reg 19) (.const 1))) (.reg 18) ;;
          .assign 14 (.bin .add (.reg 14) (.const 1)))
         .nop)) ;;
  forRange 15 (.const 0) (.reg 5)
    (.assign 16 (.load (.bin .add (.reg 6) (.reg 15))) ;;
     .assign 17 (.bin .mul (.const 2) (.reg 14)) ;;
     .store (.bin .add (.reg 11) (.reg 17)) (.reg 7) ;;
     .store (.bin .add (.reg 11) (.bin .add (.reg 17) (.const 1))) (.reg 16) ;;
     .assign 14 (.bin .add (.reg 14) (.const 1))) ;;
  .store (.reg 12) (.reg 13) ;;
  .store (.bin .add (.reg 12) (.const 1)) (.reg 14) ;;
  .ret (.const 0)

/-- Build the initial trie for `G_aug.encode`, simulate `[AN19]` (`simBase`), read back
`Vcnt - 1` output limbs, and decode the output via `decodeOutProc`.
Args: `[Vcnt, m_aug, m₁, B_len, bArr, inactLen, inactArr, r₀, arrPtr, L_sim, h, h2pow, origsPtr, outOrigPtr, outBridgePtr, outHdrPtr, heap]`. -/
def simDecodeProc (wrapperBase simBase encodeBase : ℕ) : Stmt :=
  .assign 17 (.bin .add (.reg 16) (.bin .add (.const 5)
    (.bin .mul (.bin .add (.const 1) (.reg 0)) (.reg 9)))) ;;
  .assign 18 (.bin .add (.const 2) (.bin .mul (.const 3) (.reg 1))) ;;
  .assign 19 (.bin .add (.reg 16) (.const 5)) ;;
  .assign 20 (.bin .sub (.reg 0) (.const 1)) ;;
  .assign 21 (.bin .add (.reg 19) (.reg 9)) ;;
  .assign 22 (.bin .add (.reg 21) (.reg 9)) ;;
  .store (.bin .add (.reg 16) (.const 1)) (.reg 17) ;;
  .store (.bin .add (.reg 16) (.const 2)) (.reg 9) ;;
  .store (.bin .add (.reg 16) (.const 3)) (.reg 10) ;;
  .store (.bin .add (.reg 16) (.const 4)) (.reg 11) ;;
  .call 24 (wrapperBase + idxBuildInitTrie)
    [.reg 16, .bin .add (.reg 16) (.const 1), .reg 8, .reg 18, .reg 9, .reg 10, .reg 11] ;;
  .call 24 simBase [.reg 16, .reg 18, .reg 19] ;;
  .assign 23 (.load (.reg 16)) ;;
  .call 24 (wrapperBase + idxReadOutLimbs)
    [.reg 23, .reg 21, .reg 22, .reg 20, .reg 9, .reg 11] ;;
  .call 24 (encodeBase + idxDecodeOut)
    [.reg 22, .reg 20, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 9, .reg 12,
     .reg 13, .reg 14, .reg 15] ;;
  .ret (.const 0)

def encodeDecodeModule (arithBase packBase wrapperBase simBase encodeBase : ℕ) : List Stmt :=
  [ encodeEdgeCopiesProc arithBase,
    encodeBridgesProc arithBase,
    encodeGAugProc arithBase encodeBase,
    decodeOutProc packBase,
    simDecodeProc wrapperBase simBase encodeBase ]

theorem encodeDecodeModule_length (a p w s e : ℕ) :
    (encodeDecodeModule a p w s e).length = 5 := rfl

theorem encodeDecodeModule_noRand (a p w s e : ℕ) :
    ∀ st ∈ encodeDecodeModule a p w s e, st.NoRand := by
  intro st hst
  simp only [encodeDecodeModule, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl <;>
    simp [encodeEdgeCopiesProc, encodeBridgesProc, encodeGAugProc, decodeOutProc, simDecodeProc,
      forRange, forUp, Stmt.NoRand]

end MinCostFlow.WideWord
