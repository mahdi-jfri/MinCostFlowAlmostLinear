module

public import MinCostFlow.LSF.Program.InitOrderIn

/-!
# The edge weights that the order phase reads

The copy part of the tree phase writes, for edge `t` of the edge list, the number
`edgeMult · 2^(h (L_in + 4)) / ℓ_int` at `qNat + t · Kq`, where `ℓ_int` is the integer of the
length block of the edge. `order_q` shows that these numbers are still there when the order
phase starts, and that `ℓ_int` can be read in the input memory. This is the weight hypothesis of
`orderPhase_pi`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.Num

@[expose] public section

/-- The integer length of edge `e`, read in the input memory. -/
noncomputable def lenInt (mem : ℕ → ℕ) (lenArr L_in h e : ℕ) : ℕ :=
  (intVal mem (lenArr + e * L_in) h L_in).toNat

set_option maxHeartbeats 1600000 in
/-- The weights at `qNat` after the tree phase. -/
theorem order_q {w h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {v ℓ₀ : ℕ → ℝ} {P_fp : ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr kk cnt H : ℕ}
    {mem mem₁ mem₂ mem₃ : ℕ → ℕ} {vList eList : List ℕ} (V : InitVals)
    (S : SegBIn w h Q_AN c_AN K_AN G₀ v ℓ₀ P_fp V lenArr wtArr kk mem)
    (hn : G₀.n = V.n0) (hH : V.H = H)
    (h₁ : (prepStageContract w G₀).post (prepArgsV V g0Ptr vCap0 eCap0 kk) mem cnt mem₁)
    (h₂ : (widthsContract w).post [V.m0, V.L_in, V.endA + 3] mem₁ 0 mem₂)
    (heLen : eList.length = V.m0) (heE : ∀ e, e ∈ eList ↔ e ∈ G₀.E)
    (h₃ : (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList).post
        (treeArgsV V lenArr wtArr) mem₂ H mem₃) :
    ∀ t < V.m0, unsignedVal mem₃ (V.qNat + t * V.Kq) h V.Kq =
      edgeMult G₀ v (eList.getD t 0) * 2 ^ (h * (V.L_in + 4)) /
        lenInt mem lenArr V.L_in h (eList.getD t 0) := by
  have hfrB := segB_frame h₁ h₂ hn
  obtain ⟨mem₁', hcp, hls⟩ := h₃
  rw [treePhaseCopyArgs_treeArgsV] at hcp
  obtain ⟨g0'', eListPtr', lenArr', wtArr', L_in', m0', K_w', qNatPtr', lsstHeap', vIdxBase',
    n0', eCap', multPtr', copyTailPtr', copyHeadPtr', copyLenPtr', copyWtPtr', copyOrigIdxPtr',
    copySubIdxPtr', usedBridgePtr', heqc, -, -, hq, -⟩ := hcp
  simp only [treeCopyArgsV, List.cons.injEq, and_true] at heqc
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩ := heqc
  rw [treePhaseLsstArgs_treeArgsV] at hls
  obtain ⟨n0'', M', ct', ch', cl', cw', L'', Ls', oo', ob', oh', lh', co', ub', ubl', ec'', to',
    tt', th', heql, hHlo, -, -, -, -, hfrl⟩ := hls
  simp only [List.cons.injEq, and_true] at heql
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩ := heql
  subst hH
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, s21, s22, s23, s24, s25, -⟩ := V.scratch_order
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩ := V.aux_order
  have hKq : V.Kq = V.K_w + 6 := rfl
  intro t ht
  obtain ⟨-, -, hqt⟩ := hq t ht
  have h1 : (t + 1) * V.Kq ≤ V.m0 * V.Kq := Nat.mul_le_mul_right _ ht
  rw [Nat.succ_mul] at h1
  rw [unsignedVal_congr (mem' := mem₁') (a' := V.qNat + t * V.Kq) fun i hi =>
    hfrl _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)), ← hKq] at *
  rw [hqt, treeMult]
  congr 2
  have he : eList.getD t 0 ∈ G₀.E := (heE _).mp (List.getD_eq_getElem eList 0 (show t < eList.length by omega) ▸ List.getElem_mem _)
  have hb := S.hlenB _ he
  refine intVal_congr fun i hi => ?_
  exact hfrB _ (Or.inl (by have : lsfHdrSize = 24 := rfl; omega))

/-- A positive length block gives a positive integer `ℓ_int` with `ℓ = ℓ_int / 2^P` and
`16 ℓ_int ≤ 2^(h (L + 4))`, the facts that `orderPhase_pi` asks of the lengths. -/
lemma lenInt_facts {mem : ℕ → ℕ} {a h L P : ℕ} {ℓ : ℝ} (hh : 1 ≤ h) (hv : Valid mem a h L)
    (hf : fixVal mem a h L P = ℓ) (hpos : 0 < ℓ) :
    0 < (intVal mem a h L).toNat ∧ 16 * (intVal mem a h L).toNat ≤ 2 ^ (h * (L + 4)) ∧
      ℓ = ((intVal mem a h L).toNat : ℝ) / (2 : ℝ) ^ P := by
  have hP : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have hI : (0 : ℝ) < (intVal mem a h L : ℝ) := by
    rw [← hf, fixVal] at hpos
    exact (div_pos_iff_of_pos_right hP).mp hpos
  have hI' : 0 < intVal mem a h L := by exact_mod_cast hI
  have hcast : ((intVal mem a h L).toNat : ℤ) = intVal mem a h L := Int.toNat_of_nonneg hI'.le
  have hle : intVal mem a h L ≤ (unsignedVal mem a h L : ℤ) := by
    unfold intVal signedVal; split_ifs <;> omega
  have hlt := unsignedVal_lt hv
  unfold capacity base at hlt
  rw [← pow_mul] at hlt
  refine ⟨by omega, ?_, ?_⟩
  · have h1 : (intVal mem a h L).toNat < 2 ^ (h * L) := by omega
    have h2 : 16 ≤ 2 ^ (h * 4) :=
      le_trans (by norm_num : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc 16 * (intVal mem a h L).toNat ≤ 2 ^ (h * 4) * 2 ^ (h * L) := by
          have := Nat.mul_le_mul h2 h1.le; omega
      _ = 2 ^ (h * (L + 4)) := by rw [← pow_add]; ring_nf
  · rw [← hf, fixVal]
    congr 1
    exact_mod_cast hcast.symm

end

end MinCostFlow.LSF.Program
