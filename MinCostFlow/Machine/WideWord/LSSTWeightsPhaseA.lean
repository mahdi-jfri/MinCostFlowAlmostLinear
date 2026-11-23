module

public import MinCostFlow.Machine.WideWord.LSSTWeightStep
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Setup and Phase A of Theorem 2.2 weight computation

This module defines `weightsContract`, helper capacity/alignment facts, and proves the Phase A
run lemma covering bit-width computation, minimum-length discovery, and loading small constants.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM MinCostFlow

/-! ### Full weight computation contract -/

theorem weights_callees_le (nlCnt L : ℕ) :
    let K := kWidthOf nlCnt L
    (25 * nlCnt + 80) + (nlCnt * (41 * L + 100) + 50) +
      (23 * K + 6) + (23 * K + 6) + (23 * K + 6) + 64 +
      ((30 * K + 42) + (30 * (2 * K) + 42) +
      (nlCnt * (70 * K + 120) + 25 * K + 50) + (74 * K + 42) +
      (30 * (2 * K) + 42) + (30 * (2 * K) + 42) + 92) +
      (nlCnt * (weightStepCost K + 42) + 10) ≤
      weightsCost nlCnt L := by
  intro K
  change (25 * nlCnt + 80) + (nlCnt * (41 * L + 100) + 50) +
      (23 * K + 6) + (23 * K + 6) + (23 * K + 6) + 64 +
      ((30 * K + 42) + (30 * (2 * K) + 42) +
      (nlCnt * (70 * K + 120) + 25 * K + 50) + (74 * K + 42) +
      (30 * (2 * K) + 42) + (30 * (2 * K) + 42) + 92) +
      (nlCnt * (weightStepCost K + 42) + 10) ≤
      (nlCnt + 1) * (weightStepCost K + 140 * K + 600) + nlCnt * (42 * L + 200) + 300
  have hmul : nlCnt * (41 * L + 70 * K + 245 + (weightStepCost K + 42)) ≤
      nlCnt * (weightStepCost K + 140 * K + 600 + (42 * L + 200)) :=
    Nat.mul_le_mul_left nlCnt (by omega)
  have h0 : 4200 * K + 1800 ≤ weightStepCost K := by
    dsimp only [weightStepCost]; have : 0 ≤ 2800 * K * K := Nat.zero_le _; omega
  have hnl_eq : (nlCnt + 1) * (weightStepCost K + 140 * K + 600) + nlCnt * (42 * L + 200) + 300 =
      nlCnt * (weightStepCost K + 140 * K + 600 + (42 * L + 200)) +
        (weightStepCost K + 140 * K + 900) := by ring
  have hl_eq : nlCnt * (41 * L + 100) + 25 * nlCnt + nlCnt * (70 * K + 120) +
      nlCnt * (weightStepCost K + 42) =
      nlCnt * (41 * L + 70 * K + 245 + (weightStepCost K + 42)) := by ring
  omega

def weightsContract (w h : ℕ) : Contract where
  pre args mem := ∃ (G : IndexedGraph) (v ℓ : ℕ → ℝ)
      (nlPtr lenPtr wtPtr L P outMultPtr outWPtr outKPtr heap : ℕ),
    args = [(nonloopEdges G).length, nlPtr, lenPtr, wtPtr, (activeVertsList G).length, L,
      outMultPtr, outWPtr, outKPtr, heap] ∧
    G.Valid ∧ 1 ≤ L ∧ 0 < h ∧ 3 * h + 2 ≤ w ∧
    1 ≤ (nonloopEdges G).length ∧
    ListAt mem nlPtr (nonloopEdges G) ∧
    (∀ e < G.m, Num.Valid mem (lenPtr + e * L) h L ∧
      Num.fixVal mem (lenPtr + e * L) h L P = ℓ e ∧ 0 < ℓ e) ∧
    (∀ e < G.m, Num.Valid mem (wtPtr + e * L) h L ∧
      Num.fixVal mem (wtPtr + e * L) h L P = v e ∧ 0 < v e) ∧
    nlPtr + (nonloopEdges G).length ≤ heap ∧
    lenPtr + G.m * L ≤ heap ∧ wtPtr + G.m * L ≤ heap ∧
    outMultPtr + (nonloopEdges G).length ≤ heap ∧
    outWPtr + (nonloopEdges G).length * kWidthOf (nonloopEdges G).length L ≤ heap ∧
    outKPtr < heap ∧
    DisjointRanges outMultPtr (nonloopEdges G).length outWPtr
      ((nonloopEdges G).length * kWidthOf (nonloopEdges G).length L) ∧
    DisjointRanges outMultPtr (nonloopEdges G).length outKPtr 1 ∧
    DisjointRanges outWPtr ((nonloopEdges G).length * kWidthOf (nonloopEdges G).length L) outKPtr 1 ∧
    DisjointRanges outMultPtr (nonloopEdges G).length nlPtr (nonloopEdges G).length ∧
    DisjointRanges outMultPtr (nonloopEdges G).length lenPtr (G.m * L) ∧
    DisjointRanges outMultPtr (nonloopEdges G).length wtPtr (G.m * L) ∧
    DisjointRanges outWPtr ((nonloopEdges G).length * kWidthOf (nonloopEdges G).length L)
      nlPtr (nonloopEdges G).length ∧
    DisjointRanges outWPtr ((nonloopEdges G).length * kWidthOf (nonloopEdges G).length L)
      lenPtr (G.m * L) ∧
    DisjointRanges outWPtr ((nonloopEdges G).length * kWidthOf (nonloopEdges G).length L)
      wtPtr (G.m * L) ∧
    DisjointRanges outKPtr 1 nlPtr (nonloopEdges G).length ∧
    DisjointRanges outKPtr 1 lenPtr (G.m * L) ∧
    DisjointRanges outKPtr 1 wtPtr (G.m * L) ∧
    ZeroFrom mem heap ∧
    heap + weightsSpace (nonloopEdges G).length (kWidthOf (nonloopEdges G).length L) < 2 ^ w
  post args mem v_ret mem' := ∃ (G : IndexedGraph) (v ℓ : ℕ → ℝ)
      (nlPtr lenPtr wtPtr L _P outMultPtr outWPtr outKPtr heap : ℕ),
    args = [(nonloopEdges G).length, nlPtr, lenPtr, wtPtr, (activeVertsList G).length, L,
      outMultPtr, outWPtr, outKPtr, heap] ∧
    let nl := nonloopEdges G
    let K := kWidthOf nl.length L
    v_ret = heap + weightsSpace nl.length K ∧
    mem' outKPtr = K ∧
    ZeroFrom mem' v_ret ∧
    (∀ a < heap, (a < outMultPtr ∨ outMultPtr + nl.length ≤ a) →
      (a < outWPtr ∨ outWPtr + nl.length * K ≤ a) → a ≠ outKPtr → mem' a = mem a) ∧
    ∃ (mult w_orig : ℕ → ℕ) (δ : ℝ),
      (∀ j (hj : j < nl.length), mem' (outMultPtr + j) = mult (nl[j]'hj)) ∧
      (∀ j (hj : j < nl.length), LimbsAt mem' (outWPtr + j * K) K h (w_orig (nl[j]'hj))) ∧
      (∀ e ∈ nl, mult e = LSF.edgeMult { G.toMGraph with E := nl.toFinset } v e) ∧
      (∀ e ∈ nl, 1 ≤ mult e ∧ mult e ≤ nl.length) ∧
      0 < δ ∧
      (∀ e ∈ nl, 4 ≤ w_orig e ∧ w_orig e < 2 ^ (K * h - 1)) ∧
      (∀ e ∈ nl, ℓ e ≤ δ * ((w_orig e : ℝ) + 1)) ∧
      (∀ e ∈ nl, δ * (w_orig e : ℝ) ≤ ℓ e) ∧
      (∀ e ∈ nl, δ * ((activeVertsList G).length : ℝ) ≤ ℓ e / 2)
  cost args _ := weightsCost (args.getD 0 0) (args.getD 5 0)

/-! ### Helper facts and setup phase proofs for `weights_meetsContract` -/

lemma numValid_intVal_of_digits {mem : ℕ → ℕ} {a h K n : ℕ}
    (hlist : ListAt mem a (Num.digits h K n)) (hn : 2 * n < Num.capacity h K) :
    Num.Valid mem a h K ∧ Num.intVal mem a h K = (n : ℤ) := by
  have hlen : (Num.digits h K n).length = K := Num.digits_length h K n
  refine ⟨hlen ▸ Num.valid_listAt hlist (Num.digits_lt h K n), ?_⟩
  have hl := Num.intVal_listAt (h := h) hlist
  have hn_cap : n < Num.capacity h K := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left n (by decide)) hn
  rw [hlen, Num.listVal_digits, Nat.mod_eq_of_lt hn_cap] at hl
  rw [hl, signedVal_eq_of_lt hn]

lemma weights_cap_facts {G : IndexedGraph} {h L : ℕ} {vNat lNat : ℕ → ℕ}
    (hG : G.Valid) (hh : 0 < h) (hL1 : 1 ≤ L) (hne : 1 ≤ (nonloopEdges G).length)
    (hvb : ∀ e ∈ nonloopEdges G, 2 * vNat e < Num.capacity h L)
    (hlb : ∀ e ∈ nonloopEdges G, 2 * lNat e < Num.capacity h L) :
    let nl := nonloopEdges G
    let K := kWidthOf nl.length L
    let Vcnt := (activeVertsList G).length
    let S := (nl.map vNat).sum
    2 * nl.length < Num.capacity h K ∧
    2 * (2 * Vcnt) < Num.capacity h K ∧
    2 * S < Num.capacity h K ∧
    (∀ e ∈ nl, 2 * (nl.length * vNat e + (S - 1)) < Num.capacity h (2 * K)) ∧
    (∀ e ∈ nl, ∀ lmin, 1 ≤ lmin →
      2 * ((2 * Vcnt * lNat e) / lmin) < Num.capacity h K ∧
      (2 * Vcnt * lNat e) / lmin < 2 ^ (K * h - 1)) := by
  intro nl K Vcnt S
  have hcb := kWidth_capacity_bounds (h := h) (L := L) (nlCnt := nl.length) hh hL1 hne
  change L ≤ K ∧ 2 ≤ (Nat.log 2 (4 * nl.length + 2) + 1) ∧
      4 * nl.length + 2 < 2 ^ (Nat.log 2 (4 * nl.length + 2) + 1) ∧
      4 * nl.length < 2 ^ (Nat.log 2 (4 * nl.length + 2) + 1) ∧
      nl.length < 2 ^ ((Nat.log 2 (4 * nl.length + 2) + 1) - 2) ∧
      2 * nl.length * Num.capacity h L < Num.capacity h K ∧
      8 * nl.length < Num.capacity h K at hcb
  have hV_bds := activeVertsList_length_bounds hG hne
  have hnl_cap : 2 * nl.length < Num.capacity h K := by omega
  have h2V_cap : 2 * (2 * Vcnt) < Num.capacity h K := by
    have : 2 * (2 * Vcnt) ≤ 8 * nl.length := by dsimp only [Vcnt, nl] at *; omega
    exact lt_of_le_of_lt this hcb.2.2.2.2.2.2
  have hS_le : 2 * S ≤ 2 * nl.length * Num.capacity h L := by
    have hsum_le : S ≤ nl.length * (Num.capacity h L / 2) := by
      have hterm : ∀ y ∈ nl.map vNat, y ≤ Num.capacity h L / 2 := by
        intro y hy
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
        have := hvb e he; omega
      have hle := List.sum_le_length_nsmul (nl.map vNat) (Num.capacity h L / 2) hterm
      simpa [S, nl, List.length_map] using hle
    calc 2 * S ≤ 2 * (nl.length * (Num.capacity h L / 2)) := Nat.mul_le_mul_left 2 hsum_le
      _ = nl.length * (2 * (Num.capacity h L / 2)) := by ring
      _ ≤ nl.length * Num.capacity h L := Nat.mul_le_mul_left _ (by omega)
      _ ≤ (2 * nl.length) * Num.capacity h L := Nat.mul_le_mul_right _ (by omega)
  have hS_cap : 2 * S < Num.capacity h K := lt_of_le_of_lt hS_le hcb.2.2.2.2.2.1
  have hcap2K : Num.capacity h (2 * K) = Num.capacity h K * Num.capacity h K := by
    simp only [Num.capacity, Num.base, ← pow_mul, two_mul, pow_add]
  refine ⟨hnl_cap, h2V_cap, hS_cap, fun e he => ?_, fun e he lmin hlmin => ?_⟩
  · have hv_le : vNat e ≤ S :=
      List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem he)
    have h1 : 2 * (nl.length * vNat e + (S - 1)) ≤ 2 * nl.length * (2 * S) := by
      have hmul : nl.length * vNat e + (S - 1) ≤ (nl.length + 1) * S := by
        have hlv := Nat.mul_le_mul_left nl.length hv_le
        rw [Nat.add_mul, Nat.one_mul]; omega
      have h2le : (nl.length + 1) * S ≤ (2 * nl.length) * S := by
        apply Nat.mul_le_mul_right; dsimp only [nl] at *; omega
      have : 2 * ((nl.length + 1) * S) ≤ 2 * (2 * nl.length * S) := Nat.mul_le_mul_left 2 h2le
      calc 2 * (nl.length * vNat e + (S - 1)) ≤ 2 * ((nl.length + 1) * S) := Nat.mul_le_mul_left 2 hmul
        _ ≤ 2 * (2 * nl.length * S) := this
        _ = 2 * nl.length * (2 * S) := by ring
    have hnl_half : 2 * nl.length < Num.capacity h K := hnl_cap
    have hmul_cap : 2 * nl.length * (2 * S) < Num.capacity h K * Num.capacity h K := by
      rcases Nat.eq_zero_or_pos S with hS0 | hSp
      · simp only [hS0, Nat.mul_zero]
        exact Nat.mul_pos (Num.capacity_pos h K) (Num.capacity_pos h K)
      · exact Nat.mul_lt_mul'' hnl_half hS_cap
    rw [hcap2K]; exact lt_of_le_of_lt h1 hmul_cap
  · have hmul_le : (2 * Vcnt * lNat e) / lmin ≤ 4 * nl.length * lNat e := by
      have h1 : (2 * Vcnt * lNat e) / lmin ≤ 2 * Vcnt * lNat e := Nat.div_le_self _ _
      have h2 : 2 * Vcnt * lNat e ≤ (4 * nl.length) * lNat e :=
        Nat.mul_le_mul_right _ (by dsimp only [Vcnt, nl] at *; omega)
      exact h1.trans h2
    have h4L : 2 * ((2 * Vcnt * lNat e) / lmin) ≤ 4 * nl.length * (2 * lNat e) := by
      calc 2 * ((2 * Vcnt * lNat e) / lmin) ≤ 2 * (4 * nl.length * lNat e) :=
            Nat.mul_le_mul_left 2 hmul_le
        _ = 4 * nl.length * (2 * lNat e) := by ring
    have hcapL : 4 * nl.length * (2 * lNat e) < Num.capacity h K := by
      have hLcnt : 4 * nl.length < 2 ^ (Nat.log 2 (4 * nl.length + 2) + 1) := hcb.2.2.2.1
      have hLcnt_h : 2 ^ (Nat.log 2 (4 * nl.length + 2) + 1) ≤
          2 ^ ((Nat.log 2 (4 * nl.length + 2) + 1) * h) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hh)
      have hl_lt : 2 * lNat e < 2 ^ (L * h) := by
        have h0 := hlb e he
        rw [Num.capacity, Num.base, ← pow_mul, Nat.mul_comm h L] at h0
        exact h0
      have hprod : 4 * nl.length * (2 * lNat e) <
          2 ^ ((Nat.log 2 (4 * nl.length + 2) + 1) * h) * 2 ^ (L * h) :=
        Nat.mul_lt_mul'' (lt_of_lt_of_le hLcnt hLcnt_h) hl_lt
      have hle_K : 2 ^ ((Nat.log 2 (4 * nl.length + 2) + 1) * h) * 2 ^ (L * h) ≤ Num.capacity h K := by
        rw [Num.capacity, Num.base, ← pow_mul, ← pow_add]
        apply Nat.pow_le_pow_right (by norm_num)
        dsimp only [K, kWidthOf]
        nlinarith
      exact lt_of_lt_of_le hprod hle_K
    have hlt_cap : 2 * ((2 * Vcnt * lNat e) / lmin) < Num.capacity h K := lt_of_le_of_lt h4L hcapL
    have hKh_pos : 1 ≤ K * h := Nat.mul_pos (by omega) hh
    have hcap_eq : Num.capacity h K = 2 * 2 ^ (K * h - 1) := by
      have hsub : h * K = (K * h - 1) + 1 := by rw [Nat.mul_comm h K]; omega
      rw [Num.capacity, Num.base, ← pow_mul, hsub, pow_succ, mul_comm _ 2]
    rw [hcap_eq] at hlt_cap
    exact ⟨lt_of_le_of_lt h4L hcapL, by omega⟩

structure WeightsRegs (s : State) (nlCnt nlPtr lenPtr wtPtr Vcnt L
    outMultPtr outWPtr outKPtr K nlCnt_K twoV_K lmin_2K S_2K S_m1_2K : ℕ) : Prop where
  r0 : s.regs 0 = nlCnt
  r1 : s.regs 1 = nlPtr
  r2 : s.regs 2 = lenPtr
  r3 : s.regs 3 = wtPtr
  r4 : s.regs 4 = Vcnt
  r5 : s.regs 5 = L
  r6 : s.regs 6 = outMultPtr
  r7 : s.regs 7 = outWPtr
  r8 : s.regs 8 = outKPtr
  r11 : s.regs 11 = K
  r13 : s.regs 13 = 2 * K
  r14 : s.regs 14 = twoV_K
  r15 : s.regs 15 = nlCnt_K
  r17 : s.regs 17 = lmin_2K
  r18 : s.regs 18 = S_2K
  r23 : s.regs 23 = S_m1_2K

lemma weightsRegs_upd {s s' : State} {nlCnt nlPtr lenPtr wtPtr Vcnt L
    outMultPtr outWPtr outKPtr K nlCnt_K twoV_K lmin_2K S_2K S_m1_2K r v : ℕ}
    (h : WeightsRegs s nlCnt nlPtr lenPtr wtPtr Vcnt L
      outMultPtr outWPtr outKPtr K nlCnt_K twoV_K lmin_2K S_2K S_m1_2K)
    (hreg : s'.regs = Function.update s.regs r v)
    (hr : r ∈ ([19, 20, 21, 22, 24] : List ℕ)) :
    WeightsRegs s' nlCnt nlPtr lenPtr wtPtr Vcnt L
      outMultPtr outWPtr outKPtr K nlCnt_K twoV_K lmin_2K S_2K S_m1_2K := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  exact ⟨by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r0,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r1,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r2,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r3,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r4,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r5,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r6,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r7,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r8,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r11,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r13,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r14,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r15,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r17,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r18,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r23⟩

private theorem weights_phaseA1_runs {w b h : ℕ} {p : Program} {ω : ℕ → Bool}
    {Q_w : Outcome → (ℕ → ℕ) → Prop}
    {mem : ℕ → ℕ} {pos : ℕ} {G : IndexedGraph} {nlPtr lenPtr wtPtr L outMultPtr outWPtr outKPtr heap target : ℕ}
    (hp : p.HasAt b (weightsModule b h))
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w) (hL1 : 1 ≤ L) (hne : 1 ≤ (nonloopEdges G).length)
    (hnl_list : ListAt mem nlPtr (nonloopEdges G))
    (hnl_h : nlPtr + (nonloopEdges G).length ≤ heap)
    (hlen_mem : ∀ (j : ℕ) (hj : j < (nonloopEdges G).length),
      lenPtr + (nonloopEdges G)[j]'hj * L + L ≤ heap ∧ Num.Valid mem (lenPtr + (nonloopEdges G)[j]'hj * L) h L)
    (hdisj_K_nl : DisjointRanges outKPtr 1 nlPtr (nonloopEdges G).length)
    (hdisj_K_len : DisjointRanges outKPtr 1 lenPtr (G.m * L))
    (hG_edges : ∀ e ∈ nonloopEdges G, e < G.m)
    (hoK_h : outKPtr < heap)
    (hbound : heap + weightsSpace (nonloopEdges G).length (kWidthOf (nonloopEdges G).length L) < 2 ^ w)
    (hrest : Stmt) :
    let nl := nonloopEdges G
    let Vcnt := (activeVertsList G).length
    let K := kWidthOf nl.length L
    (∀ st4 : State, ∀ (minIdx : ℕ) (hm_min : minIdx < nl.length),
      (∀ (j : ℕ) (hj : j < nl.length), Num.intVal mem (lenPtr + (nl[minIdx]'hm_min) * L) h L ≤
        Num.intVal mem (lenPtr + (nl[j]'hj) * L) h L) →
      st4.regs 0 = nl.length → st4.regs 1 = nlPtr → st4.regs 2 = lenPtr →
      st4.regs 3 = wtPtr → st4.regs 4 = Vcnt → st4.regs 5 = L →
      st4.regs 6 = outMultPtr → st4.regs 7 = outWPtr → st4.regs 8 = outKPtr →
      st4.regs 9 = heap → st4.regs 11 = K → st4.regs 12 = minIdx →
      st4.mem outKPtr = K →
      (∀ a, a ≠ outKPtr → st4.mem a = mem a) →
      ∃ o st'' c, Runs w p ω hrest st4 o st'' c ∧
        Q_w o st''.mem ∧
        c ≤ target) →
    ∃ o st'' c, Runs w p ω
      (.call 10 (b + idxBitWidth) [.reg 0] ;;
       .assign 11 (.bin .add (.reg 5) (.bin .add (.reg 10) (.const 2))) ;;
       .store (.reg 8) (.reg 11) ;;
       .call 12 (b + idxFindMinLen) [.reg 0, .reg 1, .reg 2, .reg 5] ;;
       hrest)
      (startState [nl.length, nlPtr, lenPtr, wtPtr, Vcnt, L, outMultPtr, outWPtr, outKPtr, heap] mem pos)
      o st'' c ∧
      Q_w o st''.mem ∧
      c ≤ (25 * nl.length + 80) + (nl.length * (41 * L + 100) + 50) + 30 + target := by
  intro nl Vcnt K hcont
  have hbw_mc := bitWidth_meetsContract (w := w) hp
  have hfm_mc := findMinLen_meetsContract (w := w) (h := h) hp
  have hbh : Num.base h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt
    (by simpa [Num.base] using Nat.one_le_two_pow (n := h)) hbh
  have hK1 : 1 ≤ K := by dsimp only [K, kWidthOf]; omega
  have hbound' : heap + weightsSpace nl.length K < 2 ^ w := hbound
  have hws_lb : 13 * K + nl.length * (18 * K) ≤ weightsSpace nl.length K := by
    dsimp only [weightsSpace]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _
  have h4_w : 4 < 2 ^ w := by
    have h18_1 : 18 ≤ 18 * K := Nat.le_mul_of_pos_right 18 (by omega)
    have h18_2 : 18 * K ≤ nl.length * (18 * K) := by
      simpa [Nat.one_mul] using Nat.mul_le_mul_right (18 * K) hne
    omega
  have h4nl2_w : 4 * nl.length + 2 < 2 ^ w := by
    have h18 : 18 * nl.length ≤ nl.length * (18 * K) := by
      rw [Nat.mul_comm 18 nl.length]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hLcnt_val : Nat.log 2 (4 * nl.length + 2) + 1 ≤ K := by
    dsimp only [K, kWidthOf]; omega
  have hK_w : K < 2 ^ w := by
    have : K ≤ 13 * K := by omega
    omega
  have hheap_w : heap < 2 ^ w := by omega
  have hnl_w : nl.length < 2 ^ w := by
    have hnl_heap : nl.length ≤ heap := le_trans (Nat.le_add_left _ _) hnl_h
    omega
  have hnlPtr_w : nlPtr < 2 ^ w := by
    have : nlPtr ≤ nlPtr + nl.length := Nat.le_add_right _ _
    omega
  have hlenPtr_w : lenPtr < 2 ^ w := by
    have hlenPtr_heap : lenPtr ≤ heap :=
      le_trans (Nat.le_add_right _ _) (le_trans (Nat.le_add_right _ _) (hlen_mem 0 hne).1)
    omega
  have hL_w : L < 2 ^ w := by
    have hLK : L ≤ K := by dsimp only [K, kWidthOf]; omega
    omega
  have hoK_w : outKPtr < 2 ^ w := by omega
  refine runs_start_le ?_
  refine runs_seq_call_step hbw_mc (vs := [nl.length])
    (evalArgs_cons (Expr.eval_reg_of_eq (v := nl.length) rfl) (evalArgs_nil _ _))
    (fun x hx => by simp at hx; subst x; exact hnl_w)
    ⟨nl.length, rfl, h4_w, h4nl2_w⟩
    rfl (rfl : _ = 25 * nl.length + 80)
    fun Lcnt mem0' st1 hpost1 hm1 hr1 => ?_
  obtain ⟨hm0_eq, hLcnt_eq⟩ := hpost1
  change Lcnt = Nat.log 2 (4 * nl.length + 2) + 1 at hLcnt_eq
  have hK_eq : L + (Lcnt + 2) = K := by
    dsimp only [K, kWidthOf]; rw [hLcnt_eq]; omega
  have hst1_mem : st1.mem = mem := hm1.trans hm0_eq
  have hr1_0 : st1.regs 0 = nl.length := by rw [hr1, Function.update_of_ne (by decide)]; rfl
  have hr1_1 : st1.regs 1 = nlPtr := by rw [hr1, Function.update_of_ne (by decide)]; rfl
  have hr1_2 : st1.regs 2 = lenPtr := by rw [hr1, Function.update_of_ne (by decide)]; rfl
  have hr1_3 : st1.regs 3 = wtPtr := by rw [hr1, Function.update_of_ne (by decide)]; rfl
  have hr1_4 : st1.regs 4 = Vcnt := by rw [hr1, Function.update_of_ne (by decide)]; rfl
  have hr1_5 : st1.regs 5 = L := by rw [hr1, Function.update_of_ne (by decide)]; rfl
  have hr1_6 : st1.regs 6 = outMultPtr := by rw [hr1, Function.update_of_ne (by decide)]; rfl
  have hr1_7 : st1.regs 7 = outWPtr := by rw [hr1, Function.update_of_ne (by decide)]; rfl
  have hr1_8 : st1.regs 8 = outKPtr := by rw [hr1, Function.update_of_ne (by decide)]; rfl
  have hr1_9 : st1.regs 9 = heap := by rw [hr1, Function.update_of_ne (by decide)]; rfl
  have hr1_10 : st1.regs 10 = Lcnt := by rw [hr1, Function.update_self]
  have hLcnt2_w : Lcnt + 2 < 2 ^ w := by rw [hLcnt_eq]; exact lt_of_le_of_lt (by omega) hK_w
  refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hr1_5)
    (Expr.eval_add (Expr.eval_reg_of_eq hr1_10) (Expr.eval_const (by omega)) hLcnt2_w)
    (hK_eq ▸ hK_w)) rfl fun st2 hm2 _ hr2 => ?_
  rw [hK_eq] at hr2
  have hst2_mem : st2.mem = mem := hm2.trans hst1_mem
  have hr2_0 : st2.regs 0 = nl.length := by rw [hr2, Function.update_of_ne (by decide), hr1_0]
  have hr2_1 : st2.regs 1 = nlPtr := by rw [hr2, Function.update_of_ne (by decide), hr1_1]
  have hr2_2 : st2.regs 2 = lenPtr := by rw [hr2, Function.update_of_ne (by decide), hr1_2]
  have hr2_3 : st2.regs 3 = wtPtr := by rw [hr2, Function.update_of_ne (by decide), hr1_3]
  have hr2_4 : st2.regs 4 = Vcnt := by rw [hr2, Function.update_of_ne (by decide), hr1_4]
  have hr2_5 : st2.regs 5 = L := by rw [hr2, Function.update_of_ne (by decide), hr1_5]
  have hr2_6 : st2.regs 6 = outMultPtr := by rw [hr2, Function.update_of_ne (by decide), hr1_6]
  have hr2_7 : st2.regs 7 = outWPtr := by rw [hr2, Function.update_of_ne (by decide), hr1_7]
  have hr2_8 : st2.regs 8 = outKPtr := by rw [hr2, Function.update_of_ne (by decide), hr1_8]
  have hr2_9 : st2.regs 9 = heap := by rw [hr2, Function.update_of_ne (by decide), hr1_9]
  have hr2_11 : st2.regs 11 = K := by rw [hr2, Function.update_self]
  refine runs_seq_store_step (Expr.eval_reg_of_eq hr2_8) (Expr.eval_reg_of_eq hr2_11)
    rfl fun st3 hm3 hr3 _ => ?_
  rw [hst2_mem] at hm3
  let mem1 := Function.update mem outKPtr K
  have hst3_mem : st3.mem = mem1 := hm3
  have hm1_K : mem1 outKPtr = K := Function.update_self _ _ _
  have hm1_pres : ∀ a, a ≠ outKPtr → mem1 a = mem a := fun a ha => Function.update_of_ne ha _ _
  have hm1_nl : ∀ (j : ℕ) (hj : j < nl.length), mem1 (nlPtr + j) = nl[j]'hj := fun j hj => by
    have hdisj_K_nl' : DisjointRanges outKPtr 1 nlPtr nl.length := hdisj_K_nl
    dsimp only [DisjointRanges] at hdisj_K_nl'
    have hne : nlPtr + j ≠ outKPtr := by rcases hdisj_K_nl' with h1 | h1 <;> omega
    rw [hm1_pres _ hne, hnl_list j hj]
  have hm1_len : ∀ e < G.m, ∀ i < L, mem1 (lenPtr + e * L + i) = mem (lenPtr + e * L + i) := fun e he i hi => by
    have hne : lenPtr + e * L + i ≠ outKPtr := by
      have hmul : (e + 1) * L ≤ G.m * L := Nat.mul_le_mul_right L (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hmul
      dsimp only [DisjointRanges] at hdisj_K_len
      rcases hdisj_K_len with h1 | h1 <;> omega
    exact hm1_pres _ hne
  have hm1_len_mem : ∀ j (hj : j < nl.length),
      lenPtr + mem1 (nlPtr + j) * L + L < 2 ^ w ∧ Num.Valid mem1 (lenPtr + mem1 (nlPtr + j) * L) h L := by
    intro j hj
    rw [hm1_nl j hj]
    have hlt_m := hG_edges _ (List.getElem_mem hj)
    have hmemj := hlen_mem j hj
    exact ⟨lt_of_le_of_lt hmemj.1 hheap_w,
      numValid_congr (fun i hi => (hm1_len _ hlt_m i hi).symm) hmemj.2⟩
  have hr3_0 : st3.regs 0 = nl.length := by rw [hr3]; exact hr2_0
  have hr3_1 : st3.regs 1 = nlPtr := by rw [hr3]; exact hr2_1
  have hr3_2 : st3.regs 2 = lenPtr := by rw [hr3]; exact hr2_2
  have hr3_3 : st3.regs 3 = wtPtr := by rw [hr3]; exact hr2_3
  have hr3_4 : st3.regs 4 = Vcnt := by rw [hr3]; exact hr2_4
  have hr3_5 : st3.regs 5 = L := by rw [hr3]; exact hr2_5
  have hr3_6 : st3.regs 6 = outMultPtr := by rw [hr3]; exact hr2_6
  have hr3_7 : st3.regs 7 = outWPtr := by rw [hr3]; exact hr2_7
  have hr3_8 : st3.regs 8 = outKPtr := by rw [hr3]; exact hr2_8
  have hr3_9 : st3.regs 9 = heap := by rw [hr3]; exact hr2_9
  have hr3_11 : st3.regs 11 = K := by rw [hr3]; exact hr2_11
  refine runs_seq_call_step hfm_mc (vs := [nl.length, nlPtr, lenPtr, L])
    (evalArgs_cons (Expr.eval_reg_of_eq hr3_0)
      (evalArgs_cons (Expr.eval_reg_of_eq hr3_1)
        (evalArgs_cons (Expr.eval_reg_of_eq hr3_2)
          (evalArgs_cons (Expr.eval_reg_of_eq hr3_5) (evalArgs_nil _ _)))))
    (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
    (hst3_mem ▸ ⟨nl.length, nlPtr, lenPtr, L, rfl, hne, hL1, hh, hw1, hbh,
      lt_of_le_of_lt hnl_h hheap_w, hm1_len_mem⟩)
    rfl (rfl : _ = nl.length * (41 * L + 100) + 50)
    fun r_fm mem1' st4 hpost2 hm4 hr4 => ?_
  rw [hst3_mem] at hpost2
  obtain ⟨nlCnt', nlPtr', lenPtr', L', hfm_eq, hm1'_eq, minIdx, hmin_lt, hr_fm, hmin_spec⟩ := hpost2
  simp only [List.cons.injEq, and_true] at hfm_eq
  obtain ⟨hfm1, hfm2, hfm3, hfm4⟩ := hfm_eq
  rw [← hfm1] at hmin_lt hmin_spec
  rw [← hfm2, ← hfm3, ← hfm4] at hmin_spec
  have hmin_spec_orig : ∀ (j : ℕ) (hj : j < nl.length),
      Num.intVal mem (lenPtr + (nl[minIdx]'hmin_lt) * L) h L ≤
        Num.intVal mem (lenPtr + (nl[j]'hj) * L) h L := by
    intro j hj
    have h0 := hmin_spec j hj
    rw [hm1_nl minIdx hmin_lt, hm1_nl j hj] at h0
    have hlt1 := hG_edges _ (List.getElem_mem hmin_lt)
    have hlt2 := hG_edges _ (List.getElem_mem hj)
    have he1 : ∀ i < L, mem1 (lenPtr + (nl[minIdx]'hmin_lt) * L + i) = mem (lenPtr + (nl[minIdx]'hmin_lt) * L + i) :=
      fun i hi => hm1_len _ hlt1 i hi
    have he2 : ∀ i < L, mem1 (lenPtr + (nl[j]'hj) * L + i) = mem (lenPtr + (nl[j]'hj) * L + i) :=
      fun i hi => hm1_len _ hlt2 i hi
    rwa [intVal_congr_range he1, intVal_congr_range he2] at h0
  have hr4_0 : st4.regs 0 = nl.length := by rw [hr4, Function.update_of_ne (by decide), hr3_0]
  have hr4_1 : st4.regs 1 = nlPtr := by rw [hr4, Function.update_of_ne (by decide), hr3_1]
  have hr4_2 : st4.regs 2 = lenPtr := by rw [hr4, Function.update_of_ne (by decide), hr3_2]
  have hr4_3 : st4.regs 3 = wtPtr := by rw [hr4, Function.update_of_ne (by decide), hr3_3]
  have hr4_4 : st4.regs 4 = Vcnt := by rw [hr4, Function.update_of_ne (by decide), hr3_4]
  have hr4_5 : st4.regs 5 = L := by rw [hr4, Function.update_of_ne (by decide), hr3_5]
  have hr4_6 : st4.regs 6 = outMultPtr := by rw [hr4, Function.update_of_ne (by decide), hr3_6]
  have hr4_7 : st4.regs 7 = outWPtr := by rw [hr4, Function.update_of_ne (by decide), hr3_7]
  have hr4_8 : st4.regs 8 = outKPtr := by rw [hr4, Function.update_of_ne (by decide), hr3_8]
  have hr4_9 : st4.regs 9 = heap := by rw [hr4, Function.update_of_ne (by decide), hr3_9]
  have hr4_11 : st4.regs 11 = K := by rw [hr4, Function.update_of_ne (by decide), hr3_11]
  have hr4_12 : st4.regs 12 = minIdx := by rw [hr4, Function.update_self, hr_fm]
  obtain ⟨o, st'', c_rest, hrun_rest, hpost_rest, hc_rest⟩ :=
    hcont st4 minIdx hmin_lt hmin_spec_orig hr4_0 hr4_1 hr4_2 hr4_3 hr4_4 hr4_5 hr4_6 hr4_7 hr4_8
      hr4_9 hr4_11 hr4_12 (by rw [hm4, hm1'_eq]; exact hm1_K)
      (fun a hneK => by rw [hm4, hm1'_eq]; exact hm1_pres a hneK)
  refine ⟨o, st'', c_rest, hrun_rest, hpost_rest, ?_⟩
  dsimp only [argsSize, Expr.size]
  linarith only [hc_rest]

private structure ABaseRegs (s : State) (nlCnt nlPtr lenPtr wtPtr Vcnt L
    outMultPtr outWPtr outKPtr heap K minIdx : ℕ) : Prop where
  r0 : s.regs 0 = nlCnt
  r1 : s.regs 1 = nlPtr
  r2 : s.regs 2 = lenPtr
  r3 : s.regs 3 = wtPtr
  r4 : s.regs 4 = Vcnt
  r5 : s.regs 5 = L
  r6 : s.regs 6 = outMultPtr
  r7 : s.regs 7 = outWPtr
  r8 : s.regs 8 = outKPtr
  r9 : s.regs 9 = heap
  r11 : s.regs 11 = K
  r12 : s.regs 12 = minIdx

private lemma aBaseRegs_upd {s s' : State} {nlCnt nlPtr lenPtr wtPtr Vcnt L
    outMultPtr outWPtr outKPtr heap K minIdx r v : ℕ}
    (h : ABaseRegs s nlCnt nlPtr lenPtr wtPtr Vcnt L outMultPtr outWPtr outKPtr heap K minIdx)
    (hreg : s'.regs = Function.update s.regs r v)
    (hr : r ∈ ([13, 14, 15, 16, 19] : List ℕ)) :
    ABaseRegs s' nlCnt nlPtr lenPtr wtPtr Vcnt L outMultPtr outWPtr outKPtr heap K minIdx := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  exact ⟨by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r0,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r1,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r2,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r3,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r4,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r5,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r6,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r7,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r8,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r9,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r11,
   by rw [hreg, Function.update_of_ne (by rcases hr with rfl|rfl|rfl|rfl|rfl <;> decide)]; exact h.r12⟩

private theorem weights_phaseA2_runs {w b h : ℕ} {p : Program} {ω : ℕ → Bool}
    {Q_w : Outcome → (ℕ → ℕ) → Prop}
    {st4 : State} {mem : ℕ → ℕ} {G : IndexedGraph}
    {nlPtr lenPtr wtPtr L outMultPtr outWPtr outKPtr heap minIdx target : ℕ}
    (hp : p.HasAt b (weightsModule b h)) (hG : G.Valid)
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w) (hne : 1 ≤ (nonloopEdges G).length)
    (hoK_h : outKPtr < heap) (hz0 : ZeroFrom mem heap)
    (hbound : heap + weightsSpace (nonloopEdges G).length (kWidthOf (nonloopEdges G).length L) < 2 ^ w)
    (h2V_cap : 2 * (2 * (activeVertsList G).length) < Num.capacity h (kWidthOf (nonloopEdges G).length L))
    (hnl_cap : 2 * (nonloopEdges G).length < Num.capacity h (kWidthOf (nonloopEdges G).length L))
    (hnl_h : nlPtr + (nonloopEdges G).length ≤ heap)
    (hr4_0 : st4.regs 0 = (nonloopEdges G).length) (hr4_1 : st4.regs 1 = nlPtr)
    (hr4_2 : st4.regs 2 = lenPtr) (hr4_3 : st4.regs 3 = wtPtr)
    (hr4_4 : st4.regs 4 = (activeVertsList G).length) (hr4_5 : st4.regs 5 = L)
    (hr4_6 : st4.regs 6 = outMultPtr) (hr4_7 : st4.regs 7 = outWPtr)
    (hr4_8 : st4.regs 8 = outKPtr) (hr4_9 : st4.regs 9 = heap)
    (hr4_11 : st4.regs 11 = kWidthOf (nonloopEdges G).length L) (hr4_12 : st4.regs 12 = minIdx)
    (hm4_K : st4.mem outKPtr = kWidthOf (nonloopEdges G).length L)
    (hm4_pres : ∀ a, a ≠ outKPtr → st4.mem a = mem a)
    (hrest : Stmt) :
    let nl := nonloopEdges G
    let Vcnt := (activeVertsList G).length
    let K := kWidthOf nl.length L
    (∀ st' : State,
      st'.regs 0 = nl.length → st'.regs 1 = nlPtr → st'.regs 2 = lenPtr →
      st'.regs 3 = wtPtr → st'.regs 4 = Vcnt → st'.regs 5 = L →
      st'.regs 6 = outMultPtr → st'.regs 7 = outWPtr → st'.regs 8 = outKPtr →
      st'.regs 9 = heap → st'.regs 11 = K → st'.regs 12 = minIdx →
      st'.regs 13 = 2 * K → st'.regs 14 = heap → st'.regs 15 = heap + K →
      st'.regs 16 = heap + 2 * K → st'.regs 19 = heap + 3 * K →
      st'.mem outKPtr = K →
      (∀ a < heap, a ≠ outKPtr → st'.mem a = mem a) →
      ZeroFrom st'.mem (heap + 3 * K) →
      (Num.Valid st'.mem heap h K ∧ Num.intVal st'.mem heap h K = ((2 * Vcnt : ℕ) : ℤ)) →
      (Num.Valid st'.mem (heap + K) h K ∧ Num.intVal st'.mem (heap + K) h K = (nl.length : ℤ)) →
      (Num.Valid st'.mem (heap + 2 * K) h K ∧ Num.intVal st'.mem (heap + 2 * K) h K = (1 : ℤ)) →
      ∃ o st'' c, Runs w p ω hrest st' o st'' c ∧
        Q_w o st''.mem ∧
        c ≤ target) →
    ∃ o st'' c, Runs w p ω
      (.assign 13 (.bin .mul (.const 2) (.reg 11)) ;;
       .assign 19 (.reg 9) ;;
       .assign 14 (.reg 19) ;;
       .call 19 (b + idxWLoadSmall) [.bin .mul (.const 2) (.reg 4), .reg 11, .reg 19] ;;
       .assign 15 (.reg 19) ;;
       .call 19 (b + idxWLoadSmall) [.reg 0, .reg 11, .reg 19] ;;
       .assign 16 (.reg 19) ;;
       .call 19 (b + idxWLoadSmall) [.const 1, .reg 11, .reg 19] ;;
       hrest)
      st4 o st'' c ∧
      Q_w o st''.mem ∧
      c ≤ (23 * K + 6) + (23 * K + 6) + (23 * K + 6) + 34 + target := by
  intro nl Vcnt K hcont
  have hsub := weights_hasAt_sub hp
  have hbh : Num.base h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt
    (by simpa [Num.base] using Nat.one_le_two_pow (n := h)) hbh
  have hls_mc := Num.loadSmall_meetsContract hw1 hbh hsub.1
  have hK1 : 1 ≤ K := by dsimp only [K, kWidthOf]; omega
  have hbound' : heap + weightsSpace nl.length K < 2 ^ w := hbound
  have hws_lb : 13 * K + nl.length * (18 * K) ≤ weightsSpace nl.length K := by
    dsimp only [weightsSpace]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _
  have h13K_lb : 13 * K ≤ weightsSpace nl.length K := le_trans (Nat.le_add_right _ _) hws_lb
  have hK_w : K < 2 ^ w := by omega
  have h2K_w : 2 * K < 2 ^ w := by omega
  have hheap_w : heap < 2 ^ w := by omega
  have hheapK_w : heap + K < 2 ^ w := by omega
  have hheap2K_w : heap + 2 * K < 2 ^ w := by omega
  have hheap3K_w : heap + 3 * K < 2 ^ w := by omega
  have hnl_w : nl.length < 2 ^ w := by
    have hnl_heap : nl.length ≤ heap := le_trans (Nat.le_add_left _ _) hnl_h
    omega
  have h2V_w : 2 * Vcnt < 2 ^ w := by
    have hVub := (activeVertsList_length_bounds hG hne).2
    have h2V_le : 2 * Vcnt ≤ 4 * nl.length := by dsimp only [Vcnt, nl]; omega
    have h18 : 4 * nl.length ≤ nl.length * (18 * K) := by
      rw [Nat.mul_comm 4 nl.length]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  have h2_w : 2 < 2 ^ w := lt_of_le_of_lt (by linarith only [hK1]) h2K_w
  have hoK_heap_lt : outKPtr < heap := hoK_h
  have hheap_lt_K : heap < heap + K := by linarith only [hK1]
  have hheapK_lt_2K : heap + K < heap + 2 * K := by linarith only [hK1]
  have hlt_K_2K : ∀ i, i < K → heap + i < heap + K := fun i hi => by linarith only [hi]
  have hlt_K_3K : ∀ i, i < K → heap + i < heap + 2 * K := fun i hi => by linarith only [hi, hK1]
  have hlt_KK_3K : ∀ i, i < K → heap + K + i < heap + 2 * K := fun i hi => by linarith only [hi]
  have ha4_init : ABaseRegs st4 nl.length nlPtr lenPtr wtPtr Vcnt L
      outMultPtr outWPtr outKPtr heap K minIdx :=
    ⟨hr4_0, hr4_1, hr4_2, hr4_3, hr4_4, hr4_5, hr4_6, hr4_7, hr4_8, hr4_9, hr4_11, hr4_12⟩
  refine runs_start_le ?_
  refine runs_seq_assign_step (Expr.eval_mul (Expr.eval_const h2_w) (Expr.eval_reg_of_eq ha4_init.r11) h2K_w)
    rfl fun st5 hm5 _ hr5 => ?_
  have ha5 := aBaseRegs_upd ha4_init hr5 (by decide)
  have hr5_13 : st5.regs 13 = 2 * K := by rw [hr5, Function.update_self]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq ha5.r9) rfl fun st6 hm6 _ hr6 => ?_
  have ha6 := aBaseRegs_upd ha5 hr6 (by decide)
  have hr6_13 : st6.regs 13 = 2 * K := by rw [hr6, Function.update_of_ne (by decide), hr5_13]
  have hr6_19 : st6.regs 19 = heap := by rw [hr6, Function.update_self]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr6_19) rfl fun st7 hm7 _ hr7 => ?_
  have ha7 := aBaseRegs_upd ha6 hr7 (by decide)
  have hst7_mem : st7.mem = st4.mem := hm7.trans (hm6.trans hm5)
  have hz_st4 : ZeroFrom st4.mem heap := fun a ha => by
    rw [hm4_pres a (ne_of_gt (lt_of_lt_of_le hoK_heap_lt ha))]; exact hz0 a ha
  have hr7_13 : st7.regs 13 = 2 * K := by rw [hr7, Function.update_of_ne (by decide), hr6_13]
  have hr7_14 : st7.regs 14 = heap := by rw [hr7, Function.update_self]
  have hr7_19 : st7.regs 19 = heap := by rw [hr7, Function.update_of_ne (by decide), hr6_19]
  refine runs_seq_call_step hls_mc (vs := [2 * Vcnt, K, heap])
    (evalArgs_cons (Expr.eval_mul (Expr.eval_const h2_w) (Expr.eval_reg_of_eq ha7.r4) h2V_w)
      (evalArgs_cons (Expr.eval_reg_of_eq ha7.r11)
        (evalArgs_cons (Expr.eval_reg_of_eq hr7_19) (evalArgs_nil _ _))))
    (fun x hx => by
      simp at hx
      rcases hx with rfl | rfl | rfl
      · exact h2V_w
      · exact hK_w
      · exact hheap_w)
    (hst7_mem ▸ ⟨⟨2 * Vcnt, K, heap, rfl⟩, hz_st4, hheapK_w⟩)
    rfl (rfl : _ = 23 * K + 6)
    fun hp_a mem2 st8 hpost3 hm8 hr8 => ?_
  rw [hst7_mem] at hpost3
  obtain ⟨hhpa, hloa, hhia, hfr2, hz2, hdig_2V⟩ := hpost3
  clear hloa hhia
  change ∀ x < heap, mem2 x = st4.mem x at hfr2
  change ListAt mem2 heap (Num.digits h K (2 * Vcnt)) at hdig_2V
  have hhpa_val : hp_a = heap + K := by
    have ha : heapArg [2 * Vcnt, K, heap] = heap := rfl
    have hg : ([2 * Vcnt, K, heap] : List ℕ).getD 1 0 = K := rfl
    rw [ha, hg] at hhpa; exact hhpa
  have hz2' : ZeroFrom mem2 (heap + K) := hhpa_val ▸ hz2
  have hv_2V2 := numValid_intVal_of_digits hdig_2V h2V_cap
  have ha8 := aBaseRegs_upd ha7 hr8 (by decide)
  have hr8_13 : st8.regs 13 = 2 * K := by rw [hr8, Function.update_of_ne (by decide), hr7_13]
  have hr8_14 : st8.regs 14 = heap := by rw [hr8, Function.update_of_ne (by decide), hr7_14]
  have hr8_19 : st8.regs 19 = heap + K := by rw [hr8, hhpa_val, Function.update_self]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr8_19) rfl fun st9 hm9 _ hr9 => ?_
  have ha9 := aBaseRegs_upd ha8 hr9 (by decide)
  have hr9_13 : st9.regs 13 = 2 * K := by rw [hr9, Function.update_of_ne (by decide), hr8_13]
  have hr9_14 : st9.regs 14 = heap := by rw [hr9, Function.update_of_ne (by decide), hr8_14]
  have hr9_15 : st9.regs 15 = heap + K := by rw [hr9, Function.update_self]
  have hr9_19 : st9.regs 19 = heap + K := by rw [hr9, Function.update_of_ne (by decide), hr8_19]
  have hst9_mem : st9.mem = mem2 := hm9.trans hm8
  refine runs_seq_call_step hls_mc (vs := [nl.length, K, heap + K])
    (evalArgs_cons (Expr.eval_reg_of_eq ha9.r0)
      (evalArgs_cons (Expr.eval_reg_of_eq ha9.r11)
        (evalArgs_cons (Expr.eval_reg_of_eq hr9_19) (evalArgs_nil _ _))))
    (fun x hx => by
      simp at hx
      rcases hx with rfl | rfl | rfl
      · exact hnl_w
      · exact hK_w
      · exact hheapK_w)
    (hst9_mem ▸ ⟨⟨nl.length, K, heap + K, rfl⟩, hz2', (by change (heap + K) + K < 2 ^ w; linarith only [hheap2K_w])⟩)
    rfl (rfl : _ = 23 * K + 6)
    fun hp_b mem3 st10 hpost4 hm10 hr10 => ?_
  rw [hst9_mem] at hpost4
  obtain ⟨hhpb, hlob, hhib, hfr3, hz3, hdig_nl⟩ := hpost4
  clear hlob hhib
  change ∀ x < heap + K, mem3 x = mem2 x at hfr3
  change ListAt mem3 (heap + K) (Num.digits h K nl.length) at hdig_nl
  have hhpb_val : hp_b = heap + 2 * K := by
    have ha : heapArg [nl.length, K, heap + K] = heap + K := rfl
    have hg : ([nl.length, K, heap + K] : List ℕ).getD 1 0 = K := rfl
    rw [ha, hg] at hhpb; rw [hhpb]; ring
  have hz3' : ZeroFrom mem3 (heap + 2 * K) := hhpb_val ▸ hz3
  have hv_nl3 := numValid_intVal_of_digits hdig_nl hnl_cap
  have ha10 := aBaseRegs_upd ha9 hr10 (by decide)
  have hr10_13 : st10.regs 13 = 2 * K := by rw [hr10, Function.update_of_ne (by decide), hr9_13]
  have hr10_14 : st10.regs 14 = heap := by rw [hr10, Function.update_of_ne (by decide), hr9_14]
  have hr10_15 : st10.regs 15 = heap + K := by rw [hr10, Function.update_of_ne (by decide), hr9_15]
  have hr10_19 : st10.regs 19 = heap + 2 * K := by rw [hr10, hhpb_val, Function.update_self]
  refine runs_seq_assign_step (Expr.eval_reg_of_eq hr10_19) rfl fun st11 hm11 _ hr11 => ?_
  have ha11 := aBaseRegs_upd ha10 hr11 (by decide)
  have hr11_13 : st11.regs 13 = 2 * K := by rw [hr11, Function.update_of_ne (by decide), hr10_13]
  have hr11_14 : st11.regs 14 = heap := by rw [hr11, Function.update_of_ne (by decide), hr10_14]
  have hr11_15 : st11.regs 15 = heap + K := by rw [hr11, Function.update_of_ne (by decide), hr10_15]
  have hr11_16 : st11.regs 16 = heap + 2 * K := by rw [hr11, Function.update_self]
  have hr11_19 : st11.regs 19 = heap + 2 * K := by rw [hr11, Function.update_of_ne (by decide), hr10_19]
  have hst11_mem : st11.mem = mem3 := hm11.trans hm10
  refine runs_seq_call_step hls_mc (vs := [1, K, heap + 2 * K])
    (evalArgs_cons (Expr.eval_const hw1)
      (evalArgs_cons (Expr.eval_reg_of_eq ha11.r11)
        (evalArgs_cons (Expr.eval_reg_of_eq hr11_19) (evalArgs_nil _ _))))
    (fun x hx => by
      simp at hx
      rcases hx with rfl | rfl | rfl
      · exact hw1
      · exact hK_w
      · exact hheap2K_w)
    (hst11_mem ▸ ⟨⟨1, K, heap + 2 * K, rfl⟩, hz3', (by change (heap + 2 * K) + K < 2 ^ w; linarith only [hheap3K_w])⟩)
    rfl (rfl : _ = 23 * K + 6)
    fun hp_c mem4 st12 hpost5 hm12 hr12 => ?_
  rw [hst11_mem] at hpost5
  obtain ⟨hhpc, hloc, hhic, hfr4, hz4, hdig_one⟩ := hpost5
  clear hloc hhic
  change ∀ x < heap + 2 * K, mem4 x = mem3 x at hfr4
  change ListAt mem4 (heap + 2 * K) (Num.digits h K 1) at hdig_one
  have hhpc_val : hp_c = heap + 3 * K := by
    have ha : heapArg [1, K, heap + 2 * K] = heap + 2 * K := rfl
    have hg : ([1, K, heap + 2 * K] : List ℕ).getD 1 0 = K := rfl
    rw [ha, hg] at hhpc; rw [hhpc]; ring
  have hz4' : ZeroFrom mem4 (heap + 3 * K) := hhpc_val ▸ hz4
  have h1_cap : 2 * 1 < Num.capacity h K := lt_of_le_of_lt (by linarith only [hne]) hnl_cap
  have hv_one4 := numValid_intVal_of_digits hdig_one h1_cap
  have hm4_K' : mem4 outKPtr = K := by
    rw [hfr4 _ (lt_trans hoK_heap_lt (lt_trans hheap_lt_K hheapK_lt_2K)),
      hfr3 _ (lt_trans hoK_heap_lt hheap_lt_K), hfr2 _ hoK_heap_lt, hm4_K]
  have hm4_pres' : ∀ a < heap, a ≠ outKPtr → mem4 a = mem a := fun a ha hne => by
    rw [hfr4 _ (lt_trans ha (lt_trans hheap_lt_K hheapK_lt_2K)),
      hfr3 _ (lt_trans ha hheap_lt_K), hfr2 _ ha, hm4_pres _ hne]
  have hv_2V4 : Num.Valid mem4 heap h K ∧ Num.intVal mem4 heap h K = ((2 * Vcnt : ℕ) : ℤ) := by
    have heq : ∀ i < K, mem4 (heap + i) = mem2 (heap + i) := fun i hi => by
      rw [hfr4 _ (hlt_K_3K i hi), hfr3 _ (hlt_K_2K i hi)]
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hv_2V2.1, by rw [intVal_congr_range heq, hv_2V2.2]⟩
  have hv_nl4 : Num.Valid mem4 (heap + K) h K ∧ Num.intVal mem4 (heap + K) h K = (nl.length : ℤ) := by
    have heq : ∀ i < K, mem4 (heap + K + i) = mem3 (heap + K + i) := fun i hi =>
      hfr4 _ (hlt_KK_3K i hi)
    exact ⟨numValid_congr (fun i hi => (heq i hi).symm) hv_nl3.1, by rw [intVal_congr_range heq, hv_nl3.2]⟩
  have ha12 := aBaseRegs_upd ha11 hr12 (by decide)
  have hr12_13 : st12.regs 13 = 2 * K := by rw [hr12, Function.update_of_ne (by decide), hr11_13]
  have hr12_14 : st12.regs 14 = heap := by rw [hr12, Function.update_of_ne (by decide), hr11_14]
  have hr12_15 : st12.regs 15 = heap + K := by rw [hr12, Function.update_of_ne (by decide), hr11_15]
  have hr12_16 : st12.regs 16 = heap + 2 * K := by rw [hr12, Function.update_of_ne (by decide), hr11_16]
  have hr12_19 : st12.regs 19 = heap + 3 * K := by rw [hr12, hhpc_val, Function.update_self]
  obtain ⟨o, st'', c_rest, hrun_rest, hpost_rest, hc_rest⟩ :=
    hcont st12 ha12.r0 ha12.r1 ha12.r2 ha12.r3 ha12.r4 ha12.r5 ha12.r6
      ha12.r7 ha12.r8 ha12.r9 ha12.r11 ha12.r12 hr12_13 hr12_14 hr12_15 hr12_16 hr12_19
      (hm12 ▸ hm4_K') (fun a ha hne => by rw [hm12]; exact hm4_pres' a ha hne) (hm12 ▸ hz4')
      ⟨hm12 ▸ hv_2V4.1, hm12 ▸ hv_2V4.2⟩ ⟨hm12 ▸ hv_nl4.1, hm12 ▸ hv_nl4.2⟩
      ⟨hm12 ▸ hv_one4.1, hm12 ▸ hv_one4.2⟩
  refine ⟨o, st'', c_rest, hrun_rest, hpost_rest, ?_⟩
  dsimp only [argsSize, Expr.size]
  linarith only [hc_rest]

theorem weights_phaseA_runs {w b h : ℕ} {p : Program} {ω : ℕ → Bool}
    {Q_w : Outcome → (ℕ → ℕ) → Prop}
    {mem : ℕ → ℕ} {pos : ℕ} {G : IndexedGraph} {nlPtr lenPtr wtPtr L outMultPtr outWPtr outKPtr heap target : ℕ}
    (hp : p.HasAt b (weightsModule b h)) (hG : G.Valid)
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w) (hL1 : 1 ≤ L) (hne : 1 ≤ (nonloopEdges G).length)
    (hnl_list : ListAt mem nlPtr (nonloopEdges G))
    (hnl_h : nlPtr + (nonloopEdges G).length ≤ heap)
    (hlen_mem : ∀ (j : ℕ) (hj : j < (nonloopEdges G).length),
      lenPtr + (nonloopEdges G)[j]'hj * L + L ≤ heap ∧ Num.Valid mem (lenPtr + (nonloopEdges G)[j]'hj * L) h L)
    (hdisj_K_nl : DisjointRanges outKPtr 1 nlPtr (nonloopEdges G).length)
    (hdisj_K_len : DisjointRanges outKPtr 1 lenPtr (G.m * L))
    (hG_edges : ∀ e ∈ nonloopEdges G, e < G.m)
    (hoK_h : outKPtr < heap) (hz0 : ZeroFrom mem heap)
    (hbound : heap + weightsSpace (nonloopEdges G).length (kWidthOf (nonloopEdges G).length L) < 2 ^ w)
    (h2V_cap : 2 * (2 * (activeVertsList G).length) < Num.capacity h (kWidthOf (nonloopEdges G).length L))
    (hnl_cap : 2 * (nonloopEdges G).length < Num.capacity h (kWidthOf (nonloopEdges G).length L))
    (hrest : Stmt) :
    let nl := nonloopEdges G
    let Vcnt := (activeVertsList G).length
    let K := kWidthOf nl.length L
    (∀ st' : State, ∀ (minIdx : ℕ) (hm_min : minIdx < nl.length),
      (∀ (j : ℕ) (hj : j < nl.length), Num.intVal mem (lenPtr + (nl[minIdx]'hm_min) * L) h L ≤
        Num.intVal mem (lenPtr + (nl[j]'hj) * L) h L) →
      st'.regs 0 = nl.length → st'.regs 1 = nlPtr → st'.regs 2 = lenPtr →
      st'.regs 3 = wtPtr → st'.regs 4 = Vcnt → st'.regs 5 = L →
      st'.regs 6 = outMultPtr → st'.regs 7 = outWPtr → st'.regs 8 = outKPtr →
      st'.regs 9 = heap → st'.regs 11 = K → st'.regs 12 = minIdx →
      st'.regs 13 = 2 * K → st'.regs 14 = heap → st'.regs 15 = heap + K →
      st'.regs 16 = heap + 2 * K → st'.regs 19 = heap + 3 * K →
      st'.mem outKPtr = K →
      (∀ a < heap, a ≠ outKPtr → st'.mem a = mem a) →
      ZeroFrom st'.mem (heap + 3 * K) →
      (Num.Valid st'.mem heap h K ∧ Num.intVal st'.mem heap h K = ((2 * Vcnt : ℕ) : ℤ)) →
      (Num.Valid st'.mem (heap + K) h K ∧ Num.intVal st'.mem (heap + K) h K = (nl.length : ℤ)) →
      (Num.Valid st'.mem (heap + 2 * K) h K ∧ Num.intVal st'.mem (heap + 2 * K) h K = (1 : ℤ)) →
      ∃ o st'' c, Runs w p ω hrest st' o st'' c ∧
        Q_w o st''.mem ∧
        c ≤ target) →
    ∃ o st'' c, Runs w p ω
      (.call 10 (b + idxBitWidth) [.reg 0] ;;
       .assign 11 (.bin .add (.reg 5) (.bin .add (.reg 10) (.const 2))) ;;
       .store (.reg 8) (.reg 11) ;;
       .call 12 (b + idxFindMinLen) [.reg 0, .reg 1, .reg 2, .reg 5] ;;
       .assign 13 (.bin .mul (.const 2) (.reg 11)) ;;
       .assign 19 (.reg 9) ;;
       .assign 14 (.reg 19) ;;
       .call 19 (b + idxWLoadSmall) [.bin .mul (.const 2) (.reg 4), .reg 11, .reg 19] ;;
       .assign 15 (.reg 19) ;;
       .call 19 (b + idxWLoadSmall) [.reg 0, .reg 11, .reg 19] ;;
       .assign 16 (.reg 19) ;;
       .call 19 (b + idxWLoadSmall) [.const 1, .reg 11, .reg 19] ;;
       hrest)
      (startState [nl.length, nlPtr, lenPtr, wtPtr, Vcnt, L, outMultPtr, outWPtr, outKPtr, heap] mem pos)
      o st'' c ∧
      Q_w o st''.mem ∧
      c ≤ (25 * nl.length + 80) + (nl.length * (41 * L + 100) + 50) +
          (23 * K + 6) + (23 * K + 6) + (23 * K + 6) + 64 + target := by
  intro nl Vcnt K hcont
  obtain ⟨o, st'', c, hrun, hpost, hc⟩ :=
    weights_phaseA1_runs hp hh hw hL1 hne hnl_list hnl_h hlen_mem hdisj_K_nl hdisj_K_len
      hG_edges hoK_h hbound
      (target := (23 * K + 6) + (23 * K + 6) + (23 * K + 6) + 34 + target)
      _ fun st4 minIdx hm_min hmin_spec hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr11 hr12 hmK hpres =>
      weights_phaseA2_runs hp hG hh hw hne hoK_h hz0 hbound h2V_cap hnl_cap hnl_h
        hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9 hr11 hr12 hmK hpres _
        (fun st' h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 h12 h13 h14 h15 h16 h19 hK hpr hz hv2 hvnl hv1 =>
          hcont st' minIdx hm_min hmin_spec h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 h12 h13 h14 h15 h16 h19
            hK hpr hz hv2 hvnl hv1)
  refine ⟨o, st'', c, hrun, hpost, ?_⟩
  linarith only [hc]

end MinCostFlow.WideWord
