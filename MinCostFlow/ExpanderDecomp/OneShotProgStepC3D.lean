module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.OneShotProgStepC
import MinCostFlow.ExpanderDecomp.RouteMeets
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `OneShot` Cut-Copy and Steps C3–D Verification (`OneShotProgStepC3D`)

Contains the verified statement fragments shared by the tail of `oneShotProc`:
* `copyCutRetStmt`, `copyCutRet_runs`, `copyCutRet_conseq`: copies a router cut into
  `CoreOutAt (.cut U)` at `outAddr` and returns the updated heap cursor.
* `oneShotStepC3DStmt`, `oneShotStepC3D_runs`, `oneShotStepC3D_conseq`: executes Step C
  leftover injection (`ProgStepCSpec.stepCLeftoverContract`) followed by fake-edge concatenation
  and Step D trimming (`stepDContract`).
* `edgesAt_append`, `inside_length_le_512`, `stepDWordSpace_le_oneShot`, `stepDCost_le_oneShot`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Shared cut-copy-and-return fragment: writes `CoreOutAt (.cut U)` at `r6 = outAddr` from
`r26 = srcOut` (`r27 = |U|`) and returns `r17 = hRet`. -/
def copyCutRetStmt (idx : CoreIdx) : Stmt :=
  seqStmts
    [ .store (.reg 6) (.const 0)
    , .store (.bin .add (.reg 6) (.const 1)) (.reg 27)
    , .call 29 idx.copyWords
        [.reg 27, .bin .add (.reg 26) (.const 2), .bin .add (.reg 6) (.const 2)]
    , .ret (.reg 17) ]

/-- Stage C3 + D fragment inside `oneShotProc`: invokes `idx.stepCLeftover`, either copying the
returned cut to `outAddr` and returning, or appending fake edges to `fAddr` and invoking
`idx.stepD`. -/
def oneShotStepC3DStmt (idx : CoreIdx) : Stmt :=
  seqStmts
    [ .assign 26 (.reg 17)
    , .assign 17 (.bin .add (.bin .add (.reg 26) (.const 2)) (.bin .mul (.const 2) (.reg 2)))
    , .call 17 idx.stepCLeftover
        [.reg 1, .reg 20, .reg 14, .reg 13, .reg 9, .reg 8, .reg 5, .reg 26, .reg 17]
    , .assign 19 (.load (.reg 26))
    , .assign 27 (.load (.bin .add (.reg 26) (.const 1)))
    , .cond (.bin .eq (.reg 19) (.const 1))
        (copyCutRetStmt idx)
        (seqStmts
          [ .call 29 idx.copyWords
              [.bin .mul (.const 2) (.reg 27), .bin .add (.reg 26) (.const 2),
               .bin .add (.reg 16) (.bin .mul (.const 2) (.reg 18))]
          , .assign 18 (.bin .add (.reg 18) (.reg 27))
          , .call 17 idx.stepD
              [.reg 1, .reg 2, .reg 3, .reg 18, .reg 16, .reg 8, .reg 11,
               .reg 5, .reg 6, .reg 17]
          , .ret (.reg 17) ]) ]

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

lemma copyCutRetStmt_noRand (idx : CoreIdx) : (copyCutRetStmt idx).NoRand := by
  simp [copyCutRetStmt, seqStmts, Stmt.NoRand]

lemma oneShotStepC3DStmt_noRand (idx : CoreIdx) : (oneShotStepC3DStmt idx).NoRand := by
  simp [oneShotStepC3DStmt, copyCutRetStmt_noRand, seqStmts, Stmt.NoRand]

lemma edgesAt_append {mem : ℕ → ℕ} {a : ℕ} {es1 es2 : List (ℕ × ℕ)}
    (h1 : EdgesAt mem a es1) (h2 : EdgesAt mem (a + 2 * es1.length) es2) :
    EdgesAt mem a (es1 ++ es2) := by
  intro j hj
  rw [List.length_append] at hj
  by_cases hlt : j < es1.length
  · rw [List.getElem_append_left hlt]
    exact h1 j hlt
  · have hge : es1.length ≤ j := by omega
    have hlt2 : j - es1.length < es2.length := by omega
    rw [List.getElem_append_right hge]
    have h1' := h2 (j - es1.length) hlt2
    rw [show a + 2 * es1.length + 2 * (j - es1.length) = a + 2 * j by omega] at h1'
    exact h1'

lemma inside_length_le_512 {G : Graph} {X : Finset ℕ} {L : ℕ}
    (hdeg : ∀ v ∈ X, G.degIn X v ≤ 1024 * L) :
    (G.inside X).length ≤ 512 * L * X.card := by
  have hsum : G.volIn X X = 2 * (G.inside X).length := volIn_self G X
  unfold Graph.volIn at hsum
  have hle : ∑ v ∈ X, G.degIn X v ≤ ∑ _v ∈ X, (1024 * L) :=
    Finset.sum_le_sum fun v hv => hdeg v hv
  simp only [Finset.sum_const, smul_eq_mul] at hle
  have hring : X.card * (1024 * L) = 2 * (512 * L * X.card) := by ring
  omega

lemma stepDWordSpace_le_oneShot {cfg : ParamConfig} {M r q k mG mF : ℕ}
    (hq1 : 1 ≤ q) (hk : k ≤ (NOf M r) ^ q) (hmG : mG ≤ 2 * deltaParam M * k) (hmF : mF ≤ k) :
    stepDWordSpace k mG mF (LParam M) (PParam cfg M q) ≤
      65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
  set N := NOf M r
  set L := LParam M
  set F := FParam cfg M
  set Pq := PParam cfg M q
  have hN1 : 1 ≤ N := le_trans (by decide) (four_le_NOf M r)
  have hL4 : 4 ≤ L := four_le_LParam M
  have hF1 : 1 ≤ F := one_le_FParam cfg M
  have hPq_le : Pq ≤ F ^ q := le_rfl
  have hPq12 : 12 ≤ Pq := by
    have hF12 : 12 ≤ F := Nat.le_of_dvd (by omega) (twelve_dvd_FParam cfg M)
    have hFq : F ≤ F ^ q := by
      calc F = F ^ 1 := (pow_one _).symm
        _ ≤ F ^ q := Nat.pow_le_pow_right hF1 hq1
    exact le_trans hF12 hFq
  have hmG' : mG ≤ 2048 * L * N ^ q := by
    have h1 : 2 * deltaParam M * k ≤ 2 * (1024 * L) * N ^ q :=
      Nat.mul_le_mul_left (2 * (1024 * L)) hk
    have h2 : 2 * (1024 * L) * N ^ q = 2048 * L * N ^ q := by ring
    omega
  have hNq1 : 1 ≤ N ^ q := Nat.one_le_pow _ _ hN1
  have hFq1 : 1 ≤ F ^ q := Nat.one_le_pow _ _ hF1
  have hFq2 : F ^ q ≤ F ^ (2 * q) := Nat.pow_le_pow_right hF1 (by omega)
  have hL1 : L ≤ L ^ 3 := by
    calc L = L ^ 1 := (pow_one _).symm
      _ ≤ L ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hLF : L * F ^ q ≤ L ^ 3 * F ^ (2 * q) := Nat.mul_le_mul hL1 hFq2
  have hNLF : N ^ q * (L * F ^ q) ≤ N ^ q * L ^ 3 * F ^ (2 * q) := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left (N ^ q) hLF
  have hP2 : Pq + 2 ≤ 2 * F ^ q := by omega
  have hm2f : mG + 2 * mF ≤ 2050 * L * N ^ q := by
    have h2f : 2 * mF ≤ 2 * L * N ^ q := by
      calc 2 * mF ≤ 2 * k := by omega
        _ ≤ 2 * N ^ q := by omega
        _ = 2 * 1 * N ^ q := by ring
        _ ≤ 2 * L * N ^ q := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by omega))
    have h2050 : 2048 * L * N ^ q + 2 * L * N ^ q = 2050 * L * N ^ q := by ring
    omega
  have h8 : 8 * (Pq + 2) * (mG + 2 * mF) ≤ 32800 * (N ^ q * (L * F ^ q)) := by
    calc 8 * (Pq + 2) * (mG + 2 * mF)
        ≤ 8 * (2 * F ^ q) * (2050 * L * N ^ q) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 8 hP2) hm2f
      _ = 32800 * (N ^ q * (L * F ^ q)) := by ring
  have h40 : 40 * (Pq + 2) * L ≤ 80 * (N ^ q * (L * F ^ q)) := by
    calc 40 * (Pq + 2) * L
        ≤ 40 * (2 * F ^ q) * L := Nat.mul_le_mul_right L (Nat.mul_le_mul_left 40 hP2)
      _ = 80 * (1 * (L * F ^ q)) := by ring
      _ ≤ 80 * (N ^ q * (L * F ^ q)) :=
          Nat.mul_le_mul_left 80 (Nat.mul_le_mul_right _ hNq1)
  have h16P : 16 * Pq + 40 ≤ 56 * (N ^ q * (L * F ^ q)) := by
    have h1 : 1 ≤ N ^ q * (L * F ^ q) :=
      Nat.mul_le_mul hNq1 (Nat.mul_le_mul (by omega : 1 ≤ L) hFq1)
    have h2 : Pq ≤ N ^ q * (L * F ^ q) := by
      calc Pq ≤ F ^ q := hPq_le
        _ = 1 * (1 * F ^ q) := by ring
        _ ≤ N ^ q * (L * F ^ q) := Nat.mul_le_mul hNq1 (Nat.mul_le_mul (by omega : 1 ≤ L) (le_refl _))
    omega
  have hrest : 16 * k + 9 * mG + 30 * mF ≤ 18500 * (N ^ q * (L * F ^ q)) := by
    have hk_le : k ≤ N ^ q * (L * F ^ q) := by
      calc k ≤ N ^ q := hk
        _ = N ^ q * (1 * 1) := by ring
        _ ≤ N ^ q * (L * F ^ q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega : 1 ≤ L) hFq1)
    have hmG_le : mG ≤ 2048 * (N ^ q * (L * F ^ q)) := by
      calc mG ≤ 2048 * L * N ^ q := hmG'
        _ = 2048 * (N ^ q * (L * 1)) := by ring
        _ ≤ 2048 * (N ^ q * (L * F ^ q)) :=
            Nat.mul_le_mul_left 2048 (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left L hFq1))
    omega
  have hfin : 65536 * (N ^ q * (L * F ^ q)) ≤ 65536 * N ^ q * L ^ 3 * F ^ (2 * q) := by
    have hmul := Nat.mul_le_mul_left 65536 hNLF
    have hr : 65536 * (N ^ q * L ^ 3 * F ^ (2 * q)) =
        65536 * N ^ q * L ^ 3 * F ^ (2 * q) := by ring
    omega
  unfold stepDWordSpace
  omega

lemma stepDCost_le_oneShot {cfg : ParamConfig} {M r q : ℕ} {G : Graph} {X : Finset ℕ}
    {F : List (ℕ × ℕ)} (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    (hk : X.card ≤ (NOf M r) ^ q) (hdeg : ∀ v ∈ X, G.degIn X v ≤ deltaParam M)
    (hmG : G.m ≤ 2 * deltaParam M * X.card) (hmF : F.length ≤ X.card) :
    stepDCost X.card G.m (G.inside X).length F.length (PParam cfg M q) ≤
      (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
  set N := NOf M r
  set L := LParam M
  set Fp := FParam cfg M
  set Pq := PParam cfg M q
  set k := X.card
  set mH := (G.inside X).length
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hL4 : 4 ≤ L := four_le_LParam M
  have hN1 : 1 ≤ N := le_trans (by decide) (four_le_NOf M r)
  have hF1 : 1 ≤ Fp := one_le_FParam cfg M
  have hkL : k < 2 ^ L := lt_of_le_of_lt hk (hcfg.hNq_lt_two_pow hqr)
  have hmH : mH ≤ 512 * L * k := inside_length_le_512 hdeg
  have hP12 : 12 ≤ Pq := hcfg.hP12 q hq1 hqr
  have hPq_le : Pq ≤ Fp ^ q := le_rfl
  have hrf := progRemoveFakeCost_le_coreRemoveFakeCost hL4 hkL hmH hmF hP12
  have hcore_rf : coreRemoveFakeCost L G X F Pq ≤ 2048 * N ^ q * L ^ 3 * Fp ^ (2 * q) := by
    unfold coreRemoveFakeCost
    have hkm : k + mH + F.length + 1 ≤ 2048 * L * N ^ q := by
      have hmH' : mH ≤ 512 * L * N ^ q := le_trans hmH (Nat.mul_le_mul_left _ hk)
      have h1 : 1 ≤ L * N ^ q := Nat.mul_le_mul (by omega : 1 ≤ L) (Nat.one_le_pow _ _ hN1)
      have hkLN : k ≤ L * N ^ q := by
        calc k ≤ N ^ q := hk
          _ = 1 * N ^ q := (Nat.one_mul _).symm
          _ ≤ L * N ^ q := Nat.mul_le_mul_right _ (by omega : 1 ≤ L)
      have h512 : 512 * L * N ^ q = 512 * (L * N ^ q) := by ring
      have h2048 : 2048 * L * N ^ q = 2048 * (L * N ^ q) := by ring
      omega
    have hP2 : Pq ^ 2 ≤ Fp ^ (2 * q) := by
      calc Pq ^ 2 ≤ (Fp ^ q) ^ 2 := Nat.pow_le_pow_left hPq_le 2
        _ = Fp ^ (q * 2) := (pow_mul Fp q 2).symm
        _ = Fp ^ (2 * q) := by rw [Nat.mul_comm]
    calc (k + mH + F.length + 1) * L ^ 2 * Pq ^ 2
        ≤ (2048 * L * N ^ q) * L ^ 2 * Fp ^ (2 * q) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right (L ^ 2) hkm) hP2
      _ = 2048 * N ^ q * L ^ 3 * Fp ^ (2 * q) := by ring
  have hrf_bd : removeFakeCost k mH F.length 12 Pq ≤
      2048 * 200000000 * N ^ q * L ^ 3 * Fp ^ (2 * q) := by
    calc removeFakeCost k mH F.length 12 Pq
        ≤ 200000000 * coreRemoveFakeCost L G X F Pq := hrf
      _ ≤ 200000000 * (2048 * N ^ q * L ^ 3 * Fp ^ (2 * q)) := Nat.mul_le_mul_left _ hcore_rf
      _ = 2048 * 200000000 * N ^ q * L ^ 3 * Fp ^ (2 * q) := by ring
  have hfe_bd : filterEdgesInCost k G.m + 150 ≤ 206000 * N ^ q * L ^ 3 * Fp ^ (2 * q) := by
    unfold filterEdgesInCost
    have hmG' : G.m ≤ 2048 * L * N ^ q := by
      have h1 : 2 * deltaParam M * k ≤ 2 * (1024 * L) * N ^ q :=
        Nat.mul_le_mul_left (2 * (1024 * L)) hk
      have h2 : 2 * (1024 * L) * N ^ q = 2048 * L * N ^ q := by ring
      omega
    have hLN : L * N ^ q ≤ N ^ q * L ^ 3 * Fp ^ (2 * q) := by
      have hL1 : L ≤ L ^ 3 := by
        calc L = L ^ 1 := (pow_one _).symm
          _ ≤ L ^ 3 := Nat.pow_le_pow_right (by omega) (by decide)
      have hF2 : 1 ≤ Fp ^ (2 * q) := Nat.one_le_pow _ _ hF1
      calc L * N ^ q = N ^ q * L * 1 := by ring
        _ ≤ N ^ q * L ^ 3 * Fp ^ (2 * q) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hL1) hF2
    have h1 : 1 ≤ L * N ^ q := Nat.mul_le_mul (by omega : 1 ≤ L) (Nat.one_le_pow _ _ hN1)
    have hkLN : k ≤ L * N ^ q := by
      calc k ≤ N ^ q := hk
        _ = 1 * N ^ q := (Nat.one_mul _).symm
        _ ≤ L * N ^ q := Nat.mul_le_mul_right _ (by omega : 1 ≤ L)
    have h2048 : 2048 * L * N ^ q = 2048 * (L * N ^ q) := by ring
    have hsum : 70 * k + 100 * G.m + 100 + 150 ≤ 206000 * (L * N ^ q) := by omega
    calc 70 * k + 100 * G.m + 100 + 150
        ≤ 206000 * (L * N ^ q) := hsum
      _ ≤ 206000 * (N ^ q * L ^ 3 * Fp ^ (2 * q)) := Nat.mul_le_mul_left _ hLN
      _ = 206000 * N ^ q * L ^ 3 * Fp ^ (2 * q) := by ring
  unfold stepDCost
  have hsum : (2048 * 200000000 + 206000) * N ^ q * L ^ 3 * Fp ^ (2 * q) =
      2048 * 200000000 * N ^ q * L ^ 3 * Fp ^ (2 * q) +
        206000 * N ^ q * L ^ 3 * Fp ^ (2 * q) := by ring
  omega

/-! ## 3. Verified Execution of Cut-Copy, Stage C3+D, and Full Steps C–D Tail -/

/-- Verified execution of `copyCutRetStmt`: copies `U_list` from `srcOut + 2` into
`CoreOutAt (.cut U)` at `outAddr` and returns `hRet`. -/
private lemma copyCutRet_runs {idx : CoreIdx} {w : ℕ} {p : Program}
    (hcopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    (st : State) (ω : ℕ → Bool)
    {outAddr hRet srcOut locAddr h k n : ℕ} {U : Finset ℕ} {U_list : List ℕ}
    {mem₀ : ℕ → ℕ}
    (hr6 : st.regs 6 = outAddr) (hr17 : st.regs 17 = hRet)
    (hr26 : st.regs 26 = srcOut) (hr27 : st.regs 27 = U_list.length)
    (hUnd : U_list.Nodup) (hUfin : U_list.toFinset = U)
    (hUlat : ListAt st.mem (srcOut + 2) U_list)
    (hUlen : U_list.length ≤ k) (hUrange : U ⊆ Finset.range n)
    (hout_le : outAddr + 2 + k ≤ h) (hloc_le : locAddr + n ≤ h)
    (hsrc_ge : h ≤ srcOut) (hsrc_le : srcOut + 2 + U_list.length ≤ hRet)
    (hhRet_w : hRet < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hd_lo : DisjointRange locAddr n outAddr (2 + k))
    (hZero : ZeroFrom st.mem hRet)
    (hloc : ∀ u < n, st.mem (locAddr + u) = 0)
    (hfr : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st.mem a = mem₀ a) :
    ∃ st' c,
      Runs w p ω (copyCutRetStmt idx) st (.returned hRet) st' c ∧
      CoreOutAt st'.mem outAddr (.cut U) ∧
      ZeroFrom st'.mem hRet ∧
      (∀ u < n, st'.mem (locAddr + u) = 0) ∧
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st'.mem a = mem₀ a) ∧
      c ≤ copyWordsCost U_list.length + 30 := by
  have hw0 : w ≠ 0 := by intro h0; subst h0; simp at hw16
  have h2_lt : 2 < 2 ^ w := by omega
  suffices hret : ∃ out st' c,
      Runs w p ω (copyCutRetStmt idx) st out st' c ∧
      (out = .returned hRet ∧
        CoreOutAt st'.mem outAddr (.cut U) ∧
        ZeroFrom st'.mem hRet ∧
        (∀ u < n, st'.mem (locAddr + u) = 0) ∧
        (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st'.mem a = mem₀ a)) ∧
      c ≤ copyWordsCost U_list.length + 30 by
    rcases hret with ⟨_, st', c, hr, ⟨rfl, hp1, hp2, hp3, hp4⟩, hc⟩
    exact ⟨st', c, hr, hp1, hp2, hp3, hp4, hc⟩
  refine runs_start_le ?_
  unfold copyCutRetStmt seqStmts
  refine runs_seq_store_le (x := outAddr) (v := 0)
    (by simp [Expr.eval, hr6]) (Expr.eval_const (by omega)) ?_
  refine runs_seq_store_le (x := outAddr + 1) (v := U_list.length)
    (by simp [Expr.eval, hr6, hw0, show outAddr + 1 < 2 ^ w by omega])
    (by simp [Expr.eval, hr27]) ?_
  set mem2 := Function.update (Function.update st.mem outAddr 0) (outAddr + 1) U_list.length
  have hcp_pre : (copyWordsContract w).pre [U_list.length, srcOut + 2, outAddr + 2] mem2 := by
    refine ⟨U_list.length, srcOut + 2, outAddr + 2, rfl, by omega, by omega, by omega,
      by omega, Or.inl (by omega), fun i hi => ?_⟩
    dsimp only [mem2]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hUlat i hi]
    have hmem : U_list[i]'hi ∈ U := hUfin ▸ List.mem_toFinset.mpr (List.getElem_mem hi)
    have hlt : U_list[i]'hi < n := Finset.mem_range.mp (hUrange hmem)
    omega
  refine runs_seq_call_le (vs := [U_list.length, srcOut + 2, outAddr + 2]) hcopy
    (by simp [evalArgs, Expr.eval, hr6, hr26, hr27, h2_lt,
      show srcOut + 2 < 2 ^ w by omega, show outAddr + 2 < 2 ^ w by omega])
    (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
    hcp_pre ?_
  intro _v2 mem3 _pos2 hpostCp
  simp only [copyWordsContract, List.getD_cons_zero, List.getD_cons_succ] at hpostCp
  rcases hpostCp with ⟨_, hcp_eq, hcp_fr⟩
  refine runs_ret_le (v := hRet) (by simp [Expr.eval, hr17]) ?_ ?_
  · refine ⟨rfl, ⟨?_, U_list, hUnd, hUfin, ?_, ?_⟩, ?_, ?_, ?_⟩
    · dsimp only; rw [hcp_fr outAddr (Or.inl (by omega))]
      dsimp only [mem2]; rw [Function.update_of_ne (by omega), Function.update_self]
    · dsimp only; rw [hcp_fr (outAddr + 1) (Or.inl (by omega))]
      dsimp only [mem2]; rw [Function.update_self]
    · intro i hi
      dsimp only; rw [hcp_eq i hi]
      dsimp only [mem2]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hUlat i hi
    · intro a ha
      dsimp only; rw [hcp_fr a (Or.inr (by omega))]
      dsimp only [mem2]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hZero a ha
    · intro u hu
      have hdisj : locAddr + u < outAddr ∨ outAddr + 2 + k ≤ locAddr + u := by
        rcases hd_lo with d1 | d2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
      dsimp only
      rw [hcp_fr (locAddr + u) (by rcases hdisj with d1 | d2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
      dsimp only [mem2]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hloc u hu
    · intro a ha hno
      dsimp only
      rw [hcp_fr a (by rcases hno with d1 | d2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
      dsimp only [mem2]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfr a ha hno
  · simp only [Expr.size, argsSize, copyWordsContract, List.getD_cons_zero]
    omega

/-- Consequence wrapper for `copyCutRet_runs` that unifies `st` directly from the goal. -/
lemma copyCutRet_conseq {idx : CoreIdx} {w : ℕ} {p : Program}
    (hcopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    {st : State} {ω : ℕ → Bool}
    {outAddr hRet srcOut locAddr h k n : ℕ} {U : Finset ℕ} {U_list : List ℕ}
    {mem₀ : ℕ → ℕ} {Q : Outcome → State → Prop} {Pcost : ℕ → Prop}
    (hr6 : st.regs 6 = outAddr) (hr17 : st.regs 17 = hRet)
    (hr26 : st.regs 26 = srcOut) (hr27 : st.regs 27 = U_list.length)
    (hUnd : U_list.Nodup) (hUfin : U_list.toFinset = U)
    (hUlat : ListAt st.mem (srcOut + 2) U_list)
    (hUlen : U_list.length ≤ k) (hUrange : U ⊆ Finset.range n)
    (hout_le : outAddr + 2 + k ≤ h) (hloc_le : locAddr + n ≤ h)
    (hsrc_ge : h ≤ srcOut) (hsrc_le : srcOut + 2 + U_list.length ≤ hRet)
    (hhRet_w : hRet < 2 ^ w) (hw16 : 16 < 2 ^ w)
    (hd_lo : DisjointRange locAddr n outAddr (2 + k))
    (hZero : ZeroFrom st.mem hRet)
    (hloc : ∀ u < n, st.mem (locAddr + u) = 0)
    (hfr : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st.mem a = mem₀ a)
    (hQ : ∀ st', CoreOutAt st'.mem outAddr (.cut U) → ZeroFrom st'.mem hRet →
      (∀ u < n, st'.mem (locAddr + u) = 0) →
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st'.mem a = mem₀ a) →
      Q (.returned hRet) st')
    (hB : ∀ c, c ≤ copyWordsCost U_list.length + 30 → Pcost c) :
    ∃ o st' c, Runs w p ω (copyCutRetStmt idx) st o st' c ∧ Q o st' ∧ Pcost c := by
  obtain ⟨st', c, hrun, hUout, hZ, hloc', hfr', hc⟩ :=
    copyCutRet_runs hcopy st ω hr6 hr17 hr26 hr27 hUnd hUfin hUlat hUlen hUrange
      hout_le hloc_le hsrc_ge hsrc_le hhRet_w hw16 hd_lo hZero hloc hfr
  exact ⟨.returned hRet, st', c, hrun, hQ st' hUout hZ hloc' hfr', hB c hc⟩

/-- Verified execution of `oneShotStepC3DStmt` (Step C leftover injection + Step D trimming). -/
lemma oneShotStepC3D_runs {idx : CoreIdx} {cfg : ParamConfig}
    {M r q w C_left C_sp : ℕ} {p : Program}
    (hcopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    (hleft : MeetsContract w p idx.stepCLeftover
      (stepCLeftoverContract (coreParamsOf cfg M r) C_left C_sp w))
    (hstepD : MeetsContract w p idx.stepD (stepDContract w))
    (st : State) (ω : ℕ → Bool)
    {gAddr k xAddr locAddr outAddr h lenXAddr hCur mBC b z hBound : ℕ}
    {G : Graph} {X : Finset ℕ} {callsBC : List RoutedCall} {mem₀ : ℕ → ℕ}
    (_ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    (hG : GraphAt st.mem gAddr G) (hGvalid : G.IsValid)
    (hX : VertsAt st.mem xAddr k X) (hLenX : LenListAt st.mem lenXAddr (X.sort (· ≤ ·)))
    (hXrange : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hmG : G.m ≤ 2 * (coreParamsOf cfg M r).Δ * k)
    (hk2 : 2 ≤ k) (hkNq : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_pos : 0 < b) (hble : b ≤ k) (hz_eq : z = k / (coreParamsOf cfg M r).D q)
    (hloc : ∀ u < G.n, st.mem (locAddr + u) = 0)
    (hcallsBC_len : callsBC.length ≤ 49 * (coreParamsOf cfg M r).L + 19)
    (hcallsBC_v : ∀ c ∈ callsBC, c.Valid G X (routeCong (coreParamsOf cfg M r).Δ 100
      (coreParamsOf cfg M r).L) z)
    (hcallsBC_exp : (Graph.mk G.n (callsWitnessEdges callsBC)).IsExpansionExpanderOn
      (fullVerts (X.sort (· ≤ ·)) b)
      ((coreParamsOf cfg M r).α / (20 * ((coreParamsOf cfg M r).P (q - 1) : ℝ))))
    (hmBC_eq : mBC = (callsFakeEdges callsBC).length)
    (hFBC : EdgesAt st.mem h (callsFakeEdges callsBC))
    (hg_le : gAddr + 2 + 2 * G.m ≤ h) (hx_le : xAddr + k ≤ h)
    (hloc_le : locAddr + G.n ≤ h) (hout_le : outAddr + 2 + k ≤ h)
    (hlenX_ge : h + 2 * k ≤ lenXAddr) (hlenX_le : lenXAddr + 1 + k ≤ hCur)
    (hd_lg : DisjointRange locAddr G.n gAddr (2 + 2 * G.m))
    (hd_lx : DisjointRange locAddr G.n xAddr k)
    (hd_lo : DisjointRange locAddr G.n outAddr (2 + k))
    (hd_og : DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m))
    (hd_ox : DisjointRange outAddr (2 + k) xAddr k)
    (hZero : ZeroFrom st.mem hCur)
    (hframe₀ : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st.mem a = mem₀ a)
    (hBound_ge : hCur + (2 + 2 * k) +
      stepCLeftoverSpace C_sp G.n k
        (stepCLeftoverCost (coreParamsOf cfg M r) routerCallCost G X (X.sort (· ≤ ·)) b z) +
      65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) ≤ hBound)
    (hBound_w : hBound < 2 ^ w)
    (hr1 : st.regs 1 = gAddr) (hr2 : st.regs 2 = k) (hr3 : st.regs 3 = xAddr)
    (hr5 : st.regs 5 = locAddr) (hr6 : st.regs 6 = outAddr)
    (hr8 : st.regs 8 = (coreParamsOf cfg M r).L) (hr9 : st.regs 9 = (coreParamsOf cfg M r).Δ)
    (hr11 : st.regs 11 = (coreParamsOf cfg M r).P q) (hr13 : st.regs 13 = z)
    (hr14 : st.regs 14 = b) (hr16 : st.regs 16 = h) (hr17 : st.regs 17 = hCur)
    (hr18 : st.regs 18 = mBC) (hr20 : st.regs 20 = lenXAddr) :
    ∃ v st' c,
      Runs w p ω (oneShotStepC3DStmt idx) st (.returned v) st' c ∧
      (∃ res : CoreResult, CoreOutAt st'.mem outAddr res ∧
        OneShotSpec (coreParamsOf cfg M r) q G X res) ∧
      h ≤ v ∧ v ≤ hBound ∧
      ZeroFrom st'.mem v ∧
      (∀ u < G.n, st'.mem (locAddr + u) = 0) ∧
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st'.mem a = mem₀ a) ∧
      c ≤ (C_left * stepCLeftoverCost (coreParamsOf cfg M r) routerCallCost G X
            (X.sort (· ≤ ·)) b z + C_left) + copyWordsCost (2 * k) +
          (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 *
            (FParam cfg M) ^ (2 * q) + 120 := by
  set cp := coreParamsOf cfg M r
  set vs := X.sort (· ≤ ·)
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hnd : vs.Nodup := Finset.sort_nodup X (· ≤ ·)
  have hpw : vs.Pairwise (· < ·) :=
    ((Finset.pairwise_sort X (· ≤ ·)).and hnd).imp fun h => Nat.lt_of_le_of_ne h.1 h.2
  have hvs : vs.toFinset = X := by ext v; simp [vs]
  have hvslen : vs.length = k := by rw [Finset.length_sort]; exact hX.1.symm
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have hXL : X.card < 2 ^ cp.L := lt_of_le_of_lt (hX.1 ▸ hkNq) (hcfg.hNq_lt_two_pow hqr)
  have hbig : 65536 ≤ 65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
    have hN4 := four_le_NOf M r
    have h1 : 1 ≤ (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega))
        (Nat.one_le_pow _ _ (by omega))) (Nat.one_le_pow _ _ (one_le_FParam cfg M))
    calc 65536 = 65536 * 1 := (Nat.mul_one _).symm
      _ ≤ 65536 * ((NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q)) :=
          Nat.mul_le_mul_left _ h1
      _ = _ := by ring
  have hw16 : 16 < 2 ^ w := by omega
  have hw0 : w ≠ 0 := by intro h0; subst h0; simp at hw16
  have h2_lt : 2 < 2 ^ w := by omega
  have hΔ_lt : cp.Δ < 2 ^ w := by
    have hN4 := four_le_NOf M r
    have h1 : 1 ≤ (NOf M r) ^ q * (LParam M) ^ 2 * (FParam cfg M) ^ (2 * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.one_le_pow _ _ (by omega))
        (Nat.one_le_pow _ _ (by omega))) (Nat.one_le_pow _ _ (one_le_FParam cfg M))
    have hle : cp.Δ ≤ 65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
      have : cp.Δ = 1024 * LParam M := rfl
      calc cp.Δ = 1024 * LParam M * 1 := by rw [this, Nat.mul_one]
        _ ≤ 65536 * LParam M * ((NOf M r) ^ q * (LParam M) ^ 2 * (FParam cfg M) ^ (2 * q)) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide)) h1
        _ = _ := by ring
    omega
  have hL_lt : cp.L < 2 ^ w := by
    have : cp.L ≤ cp.Δ := by change LParam M ≤ 1024 * LParam M; omega
    omega
  set outC2 := hCur
  set hC2 := outC2 + 2 + 2 * k
  set costL := stepCLeftoverCost cp routerCallCost G X vs b z
  have hstepL_spec := stepCLeftover_spec hcfg routeOrCut_isMatchingPlayer (z := z)
    hXrange hGloop hdegG hXL hnd hvs hb_pos (hvslen ▸ hble)
    (by have := hcfg.hα0; have := hcfg.hP_pos (by omega : q - 1 ≤ r); positivity)
    (by
      rw [div_le_one (by have := hcfg.hP_pos (by omega : q - 1 ≤ r); positivity)]
      have h1 : (1 : ℝ) ≤ cp.P (q - 1) := by exact_mod_cast hcfg.hP_pos (by omega : q - 1 ≤ r)
      have h2 := hcfg.hα1
      nlinarith)
    hcallsBC_exp
  suffices h : ∃ out st' c,
      Runs w p ω (oneShotStepC3DStmt idx) st out st' c ∧
      (∃ v, out = .returned v ∧
        (∃ res : CoreResult, CoreOutAt st'.mem outAddr res ∧ OneShotSpec cp q G X res) ∧
        h ≤ v ∧ v ≤ hBound ∧
        ZeroFrom st'.mem v ∧
        (∀ u < G.n, st'.mem (locAddr + u) = 0) ∧
        (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st'.mem a = mem₀ a)) ∧
      c ≤ (C_left * costL + C_left) + copyWordsCost (2 * k) +
          (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 *
            (FParam cfg M) ^ (2 * q) + 120 by
    rcases h with ⟨_, st', c, hrun, ⟨v, rfl, hpost⟩, hc⟩
    exact ⟨v, st', c, hrun, hpost.1, hpost.2.1, hpost.2.2.1, hpost.2.2.2.1,
      hpost.2.2.2.2.1, hpost.2.2.2.2.2, hc⟩
  refine runs_start_le ?_
  unfold oneShotStepC3DStmt seqStmts
  -- r26 := r17 (= outC2)
  refine runs_seq_assign_le (v := outC2) (by rw [Expr.eval_reg, hr17]) ?_
  -- r17 := r26 + 2 + 2 * r2 (= hC2)
  refine runs_seq_assign_le (v := hC2)
    (by simp [Expr.eval, hr2, hC2, h2_lt, show outC2 + 2 < 2 ^ w by omega,
      show 2 * k < 2 ^ w by omega, show outC2 + 2 + 2 * k < 2 ^ w by omega]) ?_
  -- call stepCLeftover
  have hleft_pre : (stepCLeftoverContract cp C_left C_sp w).pre
      [gAddr, lenXAddr, b, z, cp.Δ, cp.L, locAddr, outC2, hC2] st.mem := by
    refine ⟨gAddr, lenXAddr, b, z, locAddr, outC2, hC2, G, vs, rfl,
      hG, hGvalid, hLenX, hpw, hvs.symm ▸ hXrange, hvs.symm ▸ hGloop,
      hcfg.hΔ_pos, hvs.symm ▸ hdegG, by change 1 ≤ LParam M; omega,
      by rw [hvslen, hX.1]; exact hXL,
      hb_pos, fun _ => by rw [hvslen]; exact hble, hloc,
      fun a ha => hZero a (by omega),
      by omega, by omega, by omega, by omega,
      hd_lg, Or.inl (by omega), Or.inl (by omega),
      Or.inr (by omega), Or.inr (by omega), ?_, hw16, by rw [hvslen]; exact hmG, by rw [hvslen, hz_eq]; exact Nat.div_le_self _ _⟩
    rw [hvslen, hvs]
    change hC2 + stepCLeftoverSpace C_sp G.n k costL < 2 ^ w
    omega
  refine runs_seq_call_le
    (vs := [gAddr, lenXAddr, b, z, cp.Δ, cp.L, locAddr, outC2, hC2]) hleft
    (by simp [evalArgs, Expr.eval, hr1, hr20, hr14, hr13, hr9, hr8, hr5])
    (by intro v hv; simp at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · rw [hz_eq]; have := Nat.div_le_self k (cp.D q); omega
        · exact hΔ_lt
        · exact hL_lt
        · omega
        · omega
        · omega)
    hleft_pre ?_
  intro hAfterC2 mem1 _pos1 hpostL
  simp only [stepCLeftoverContract, List.getD_cons_zero, List.getD_cons_succ] at hpostL
  have hrdG : readGraph st.mem gAddr = G := readGraph_eq_of_graphAt hG
  have hrdX : readLenPrefixedList st.mem lenXAddr = vs := readLenPrefixedList_eq_of_lenListAt hLenX
  rw [hrdG, hrdX, hvs, hvslen] at hpostL
  rcases hpostL with ⟨hOutL, hloc1, hhC2_le, hhC2_hi, hZero1, hframe1⟩
  have hhC2_le_Bound : hAfterC2 + 65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) ≤ hBound := by
    dsimp only [hC2, outC2] at hhC2_hi
    linarith only [hhC2_hi, hBound_ge]
  have hmem1_eq_lt : ∀ a < h, (a < locAddr ∨ locAddr + G.n ≤ a) → mem1 a = st.mem a :=
    fun a ha hnl => hframe1 a (by omega) hnl (Or.inl (by omega))
  have hmem1_f : ∀ a, h ≤ a → a < h + 2 * k → mem1 a = st.mem a := fun a h1 h2 =>
    hframe1 a (by omega) (Or.inr (by omega)) (Or.inl (by omega))
  -- r19 := load r26, r27 := load (r26 + 1)
  have htag1_w : mem1 outC2 < 2 ^ w := by
    cases hres : stepCLeftover cp routeOrCut G X vs b z with
    | inl U => rw [hres] at hOutL; rw [hOutL.1]; omega
    | inr callsZ => rw [hres] at hOutL; rw [hOutL.1]; omega
  have hlen1_w : mem1 (outC2 + 1) < 2 ^ w := by
    cases hres : stepCLeftover cp routeOrCut G X vs b z with
    | inl U =>
      rw [hres] at hOutL hstepL_spec
      rcases hOutL.2 with ⟨U_list, hUnd, hUfin, hUlen, _⟩
      have hUsub : U ⊆ X := hstepL_spec.1
      have : U_list.length ≤ k := by
        rw [← List.toFinset_card_of_nodup hUnd, hUfin, hX.1]; exact Finset.card_le_card hUsub
      omega
    | inr callsZ =>
      rw [hres] at hOutL hstepL_spec
      have hlen_z : (callsFakeEdges callsZ).length ≤ k :=
        callsFakeEdges_length_le_k ha hrl hq1 hqr
          (by have := hstepL_spec.1; have := hcfg.hΔ; omega)
          (hz_eq ▸ hstepL_spec.2.1)
      rw [hOutL.2.1]; omega
  refine runs_seq_assign_le (v := mem1 outC2)
    (by simp [Expr.eval]) ?_
  refine runs_seq_assign_le (v := mem1 (outC2 + 1))
    (by simp [Expr.eval, hw0, show outC2 + 1 < 2 ^ w by omega]) ?_
  -- cond (r19 == 1)
  cases hres : stepCLeftover cp routeOrCut G X vs b z with
  | inl U =>
    rw [hres] at hOutL hstepL_spec
    rcases hOutL with ⟨htag1, U_list, hUnd, hUfin, hUlen, hUlat⟩
    have hUsub : U ⊆ X := hstepL_spec.1
    have hUlen_le : U_list.length ≤ k := by
      rw [← List.toFinset_card_of_nodup hUnd, hUfin, hX.1]; exact Finset.card_le_card hUsub
    refine runs_cond_le (v := 1) (by simp [Expr.eval, htag1, hw0]) ?_ (fun h0 => absurd h0 (by decide))
    intro _
    have hfr1 : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → mem1 a = mem₀ a := fun a ha hno => by
      by_cases hloca : locAddr ≤ a ∧ a < locAddr + G.n
      · have hu : a - locAddr < G.n := by omega
        have ha_eq : a = locAddr + (a - locAddr) := by omega
        rw [ha_eq, hloc1 (a - locAddr) hu, ← hloc (a - locAddr) hu, ← ha_eq, hframe₀ a ha hno]
      · rw [hmem1_eq_lt a ha (by omega)]
        exact hframe₀ a ha hno
    apply copyCutRet_conseq hcopy (outAddr := outAddr) (hRet := hAfterC2) (srcOut := outC2)
      (locAddr := locAddr) (h := h) (k := k) (n := G.n) (U := U) (U_list := U_list) (mem₀ := mem₀)
      (by simp [hr6]) (by simp) (by simp) (by simp [hUlen])
      hUnd hUfin hUlat hUlen_le (hUsub.trans hXrange) hout_le hloc_le (by omega)
      (by dsimp only [hC2, outC2] at hhC2_le; omega) (by omega) hw16 hd_lo hZero1 hloc1 hfr1
    · intro stF hUout hZF hlocF hfrF
      exact ⟨hAfterC2, rfl, ⟨.cut U, hUout, by simpa [OneShotSpec, hz_eq, hX.1] using hstepL_spec⟩,
        by omega, by omega, hZF, hlocF, hfrF⟩
    · intro cF hcF
      simp only [Expr.size, argsSize, stepCLeftoverContract,
        List.getD_cons_zero, List.getD_cons_succ, hrdG, hrdX, hvs]
      have hcp_le : copyWordsCost U_list.length ≤ copyWordsCost (2 * k) := by
        unfold copyWordsCost; omega
      have h1_prod : 1 ≤ (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
        have hN : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
        have hL : 1 ≤ LParam M := le_trans (by decide) (four_le_LParam M)
        have hF : 1 ≤ FParam cfg M := one_le_FParam cfg M
        exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hN) (Nat.pow_pos hL)) (Nat.pow_pos hF)
      have h30 : 30 ≤ (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 *
          (FParam cfg M) ^ (2 * q) := by
        calc 30 ≤ (2048 * 200000000 + 206000) * 1 := by omega
          _ ≤ (2048 * 200000000 + 206000) *
                ((NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q)) :=
              Nat.mul_le_mul_left _ h1_prod
          _ = (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 *
                (FParam cfg M) ^ (2 * q) := by ring
      dsimp only [costL]
      linarith only [hcF, hcp_le, h30]
  | inr callsZ =>
    rw [hres] at hOutL hstepL_spec
    rcases hOutL with ⟨htag0, hmZ_eq, hFZ_at⟩
    rcases hstepL_spec with ⟨hcallsZ_len, hcallsZ_v, hcallsAll_exp⟩
    set callsAll := callsBC ++ callsZ
    have hcallsAll_len : callsAll.length ≤ cp.Δ := by
      have hΔ : 49 * cp.L + 20 ≤ cp.Δ := by change 49 * LParam M + 20 ≤ 1024 * LParam M; omega
      simp only [callsAll, List.length_append]
      omega
    have hcallsAll_v : ∀ c ∈ callsAll, c.Valid G X (routeCong cp.Δ 100 cp.L) z := by
      intro c hc
      simp only [callsAll, List.mem_append] at hc
      rcases hc with h1 | h2
      · exact hcallsBC_v c h1
      · exact hcallsZ_v c h2
    have hmAll_le : (callsFakeEdges callsAll).length ≤ k :=
      callsFakeEdges_length_le_k ha hrl hq1 hqr hcallsAll_len (hz_eq ▸ hcallsAll_v)
    have hmAll_sum : (callsFakeEdges callsAll).length = mBC + (callsFakeEdges callsZ).length := by
      simp [callsAll, callsFakeEdges, hmBC_eq]
    set mZ := (callsFakeEdges callsZ).length
    refine runs_cond_le (v := 0) (by simp [Expr.eval, htag0, hw0]) (fun h => absurd rfl h) ?_
    intro _
    -- copyWords [2 * mZ, outC2 + 2, h + 2 * mBC]
    have hcp_pre : (copyWordsContract w).pre [2 * mZ, outC2 + 2, h + 2 * mBC] mem1 := by
      refine ⟨2 * mZ, outC2 + 2, h + 2 * mBC, rfl, by omega, by omega, by omega, by omega,
        Or.inl (by omega), fun i hi => ?_⟩
      have hlt := edgesAt_words_lt hFZ_at hXrange (fun e he => by
        unfold callsFakeEdges at he
        obtain ⟨c, hc, hce⟩ := List.mem_flatMap.mp he
        exact (hcallsZ_v c hc).2.2.2.1 e hce) i hi
      omega
    refine runs_seq_call_le (vs := [2 * mZ, outC2 + 2, h + 2 * mBC]) hcopy
      (by simp [evalArgs, Expr.eval, hr16, hr18, hmZ_eq, h2_lt,
        show 2 * mZ < 2 ^ w by omega, show outC2 + 2 < 2 ^ w by omega,
        show 2 * mBC < 2 ^ w by omega, show h + 2 * mBC < 2 ^ w by omega])
      (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
      hcp_pre ?_
    intro _v2 mem2 _pos2 hpostCp
    simp only [copyWordsContract, List.getD_cons_zero, List.getD_cons_succ] at hpostCp
    rcases hpostCp with ⟨_, hcp_eq, hcp_fr⟩
    -- r18 := mBC + mZ
    refine runs_seq_assign_le (v := mBC + mZ)
      (by simp [Expr.eval, hr18, hmZ_eq, show mBC + mZ < 2 ^ w by omega]) ?_
    -- Prepare stepD preconditions on mem2
    have hmem2_eq_lt : ∀ a < h, (a < locAddr ∨ locAddr + G.n ≤ a) → mem2 a = st.mem a :=
      fun a ha hnl => by rw [hcp_fr a (Or.inl (by omega))]; exact hmem1_eq_lt a ha hnl
    have hG2 : GraphAt mem2 gAddr G :=
      hG.congr fun a h1 h2 => by
        have hlenG : G.encode.length = 2 + 2 * G.m := graph_encode_length G
        exact hmem2_eq_lt a (by omega)
          (by rcases hd_lg with d1 | d2 <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
    have hX2 : VertsAt mem2 xAddr k X := by
      refine ⟨hX.1, fun i hi => ?_⟩
      have hik : i < k := by rw [Finset.length_sort] at hi; rw [hX.1]; exact hi
      rw [hmem2_eq_lt (xAddr + i) (by omega)
        (by rcases hd_lx with d1 | d2 <;> [exact Or.inr (by omega); exact Or.inl (by omega)])]
      exact hX.2 i hi
    have hFAll2 : EdgesAt mem2 h (callsFakeEdges callsAll) := by
      have hcat : callsFakeEdges callsAll = callsFakeEdges callsBC ++ callsFakeEdges callsZ := by
        simp [callsAll, callsFakeEdges]
      rw [hcat]
      refine edgesAt_append ?_ ?_
      · intro j hj
        have h1 := hFBC j hj
        have hj' : j < mBC := by omega
        refine ⟨?_, ?_⟩
        · rw [hcp_fr (h + 2 * j) (Or.inl (by omega)), hmem1_f (h + 2 * j) (by omega) (by omega)]
          exact h1.1
        · rw [hcp_fr (h + 2 * j + 1) (Or.inl (by omega)),
            hmem1_f (h + 2 * j + 1) (by omega) (by omega)]
          exact h1.2
      · rw [← hmBC_eq]
        exact edgesAt_of_copyWords hFZ_at hcp_eq
    have hloc2 : ∀ u < G.n, mem2 (locAddr + u) = 0 := fun u hu => by
      rw [hcp_fr (locAddr + u) (Or.inl (by omega))]; exact hloc1 u hu
    have hZero2 : ZeroFrom mem2 hAfterC2 := fun a ha => by
      rw [hcp_fr a (Or.inr (by omega))]; exact hZero1 a ha
    have hDword : stepDWordSpace k G.m (mBC + mZ) cp.L (cp.P q) ≤
        65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) :=
      stepDWordSpace_le_oneShot hq1 hkNq hmG (by omega)
    have hcallsAll_v' : ∀ c ∈ callsAll,
        c.Valid G X (routeCong cp.Δ 100 cp.L) (X.card / cp.D q) := by
      intro c hc; rw [← hX.1, ← hz_eq]; exact hcallsAll_v c hc
    have hwit_exp : (Graph.mk G.n (callsWitnessEdges callsAll)).IsExpansionExpanderOn X
        (cp.α / (40 * (cp.P (q - 1) : ℝ))) := by
      have hdiv : cp.α / (20 * (cp.P (q - 1) : ℝ)) / 2 = cp.α / (40 * (cp.P (q - 1) : ℝ)) := by ring
      rwa [← hdiv]
    obtain ⟨_, hFmem, hKcond, hKdeg, hR_imp⟩ :=
      stepD_of_removeFake_out hcfg hq1 hqr (hX.1 ▸ hk2) hdegG hcallsAll_len hcallsAll_v' hwit_exp
    have hk_lt_2L : k < 2 ^ cp.L := hX.1.symm ▸ hXL
    have hstepD_pre : (stepDContract w).pre
        [gAddr, k, xAddr, mBC + mZ, h, cp.L, cp.P q, locAddr, outAddr, hAfterC2] mem2 :=
      ⟨gAddr, k, xAddr, mBC + mZ, h, cp.L, cp.P q, locAddr, outAddr, hAfterC2,
        G, X, callsFakeEdges callsAll, rfl, hG2, hGvalid, hX2, hXrange,
        hFAll2, hmAll_sum, by omega, hL4, hk_lt_2L, hcfg.hP12 q hq1 hqr,
        hX.1.symm ▸ inside_length_le_512 hdegG, hFmem, hKcond, hKdeg, hloc2,
        by omega, by omega, by omega, by omega, by omega,
        hd_lg, hd_lx, Or.inl (by omega), hd_lo, hd_ox, Or.inl (by omega),
        hZero2, by omega⟩
    have hP_lt : cp.P q < 2 ^ w := by
      have hN4 := four_le_NOf M r
      have hF1 := one_le_FParam cfg M
      have hFq : cp.P q ≤ (FParam cfg M) ^ (2 * q) := Nat.pow_le_pow_right hF1 (by omega)
      have h1 : 1 ≤ 65536 * (NOf M r) ^ q * (LParam M) ^ 3 :=
        Nat.mul_le_mul (Nat.mul_le_mul (by decide : 1 ≤ 65536) (Nat.one_le_pow _ _ (by omega)))
          (Nat.one_le_pow _ _ (by omega))
      have hle : cp.P q ≤ 65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
        calc cp.P q = 1 * cp.P q := (Nat.one_mul _).symm
          _ ≤ (65536 * (NOf M r) ^ q * (LParam M) ^ 3) * (FParam cfg M) ^ (2 * q) :=
              Nat.mul_le_mul h1 hFq
      omega
    refine runs_seq_call_le
      (vs := [gAddr, k, xAddr, mBC + mZ, h, cp.L, cp.P q, locAddr, outAddr, hAfterC2]) hstepD
      (by simp [evalArgs, Expr.eval, hr1, hr2, hr3, hr16, hr8, hr11, hr5, hr6])
      (by intro v hv; simp at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · omega
          · omega
          · omega
          · omega
          · omega
          · exact hL_lt
          · exact hP_lt
          · omega
          · omega
          · omega)
      hstepD_pre ?_
    intro hOut mem3 _pos3 hpostD
    obtain ⟨R, hRout, hRsub, hRcond, hRdeg, hRvol, hhOut_eq, hZero3, hloc3, hframe3⟩ :=
      hpostD gAddr k xAddr (mBC + mZ) h cp.L (cp.P q) locAddr outAddr hAfterC2
        G X (callsFakeEdges callsAll) rfl hG2 hGvalid hX2 hXrange
        hFAll2 hmAll_sum (by omega) hL4 hk_lt_2L (hcfg.hP12 q hq1 hqr)
        (hX.1.symm ▸ inside_length_le_512 hdegG) hFmem hKcond hKdeg hloc2
        (by omega) (by omega) (by omega) (by omega) (by omega)
        hd_lg hd_lx (Or.inl (by omega)) hd_lo hd_ox (Or.inl (by omega))
        hZero2 (by omega)
    have hOneShotR : OneShotSpec cp q G X (.expander R) := by
      rw [← hmAll_sum] at hRvol
      exact hR_imp R hRsub hRcond hRdeg hRvol
    have hDcost : stepDCost k G.m (G.inside X).length (mBC + mZ) (cp.P q) ≤
        (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 *
          (FParam cfg M) ^ (2 * q) := by
      rw [← hmAll_sum, hX.1]
      exact stepDCost_le_oneShot ha hrl hq1 hqr (hX.1 ▸ hkNq) hdegG (hX.1 ▸ hmG) (by omega)
    have hDsp : stepDSpace k G.m (mBC + mZ) cp.L (cp.P q) ≤
        stepDWordSpace k G.m (mBC + mZ) cp.L (cp.P q) := by
      unfold stepDSpace stepDWordSpace; omega
    have hreadG2 : readGraph mem2 gAddr = G := readGraph_eq_of_graphAt hG2
    have hreadX2 : (readList mem2 xAddr k).toFinset = X := by
      have hlen : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort]; exact hX2.1.symm
      have hr : readList mem2 xAddr k = X.sort (· ≤ ·) := by
        rw [← hlen]; exact readList_eq_of_listAt hX2.2
      rw [hr]; ext v; simp
    refine runs_ret_le (v := hOut) (by simp [Expr.eval]) ?_ ?_
    · refine ⟨hOut, rfl, ⟨.expander R, hRout, hOneShotR⟩, by omega, by omega, hZero3, hloc3, ?_⟩
      intro a ha hno
      dsimp only
      rw [hframe3 a (by omega) hno]
      dsimp only
      by_cases hloca : locAddr ≤ a ∧ a < locAddr + G.n
      · have hu : a - locAddr < G.n := by omega
        have ha_eq : a = locAddr + (a - locAddr) := by omega
        rw [ha_eq, hloc2 (a - locAddr) hu, ← hloc (a - locAddr) hu, ← ha_eq, hframe₀ a ha hno]
      · rw [hmem2_eq_lt a ha (by omega)]
        exact hframe₀ a ha hno
    · simp only [Expr.size, argsSize, stepCLeftoverContract, copyWordsContract, stepDContract,
        List.getD_cons_zero, List.getD_cons_succ, hrdG, hrdX, hvs, hreadG2, hreadX2]
      have hcp_le : copyWordsCost (2 * mZ) ≤ copyWordsCost (2 * k) := by
        unfold copyWordsCost; omega
      dsimp only [costL]
      linarith only [hDcost, hcp_le]

/-- Consequence wrapper for `oneShotStepC3D_runs` unifying `st` from the goal. -/
lemma oneShotStepC3D_conseq {idx : CoreIdx} {cfg : ParamConfig}
    {M r q w C_left C_sp : ℕ} {p : Program}
    (hcopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    (hleft : MeetsContract w p idx.stepCLeftover
      (stepCLeftoverContract (coreParamsOf cfg M r) C_left C_sp w))
    (hstepD : MeetsContract w p idx.stepD (stepDContract w))
    {st : State} {ω : ℕ → Bool}
    {gAddr k xAddr locAddr outAddr h lenXAddr hCur mBC b z hBound : ℕ}
    {G : Graph} {X : Finset ℕ} {callsBC : List RoutedCall} {mem₀ : ℕ → ℕ}
    {Q : Outcome → State → Prop} {Pcost : ℕ → Prop}
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    (hG : GraphAt st.mem gAddr G) (hGvalid : G.IsValid)
    (hX : VertsAt st.mem xAddr k X) (hLenX : LenListAt st.mem lenXAddr (X.sort (· ≤ ·)))
    (hXrange : X ⊆ Finset.range G.n) (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hmG : G.m ≤ 2 * (coreParamsOf cfg M r).Δ * k)
    (hk2 : 2 ≤ k) (hkNq : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hb_pos : 0 < b) (hble : b ≤ k) (hz_eq : z = k / (coreParamsOf cfg M r).D q)
    (hloc : ∀ u < G.n, st.mem (locAddr + u) = 0)
    (hcallsBC_len : callsBC.length ≤ 49 * (coreParamsOf cfg M r).L + 19)
    (hcallsBC_v : ∀ c ∈ callsBC, c.Valid G X (routeCong (coreParamsOf cfg M r).Δ 100
      (coreParamsOf cfg M r).L) z)
    (hcallsBC_exp : (Graph.mk G.n (callsWitnessEdges callsBC)).IsExpansionExpanderOn
      (fullVerts (X.sort (· ≤ ·)) b)
      ((coreParamsOf cfg M r).α / (20 * ((coreParamsOf cfg M r).P (q - 1) : ℝ))))
    (hmBC_eq : mBC = (callsFakeEdges callsBC).length)
    (hFBC : EdgesAt st.mem h (callsFakeEdges callsBC))
    (hg_le : gAddr + 2 + 2 * G.m ≤ h) (hx_le : xAddr + k ≤ h)
    (hloc_le : locAddr + G.n ≤ h) (hout_le : outAddr + 2 + k ≤ h)
    (hlenX_ge : h + 2 * k ≤ lenXAddr) (hlenX_le : lenXAddr + 1 + k ≤ hCur)
    (hd_lg : DisjointRange locAddr G.n gAddr (2 + 2 * G.m))
    (hd_lx : DisjointRange locAddr G.n xAddr k)
    (hd_lo : DisjointRange locAddr G.n outAddr (2 + k))
    (hd_og : DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m))
    (hd_ox : DisjointRange outAddr (2 + k) xAddr k)
    (hZero : ZeroFrom st.mem hCur)
    (hframe₀ : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st.mem a = mem₀ a)
    (hBound_ge : hCur + (2 + 2 * k) +
      stepCLeftoverSpace C_sp G.n k
        (stepCLeftoverCost (coreParamsOf cfg M r) routerCallCost G X (X.sort (· ≤ ·)) b z) +
      65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) ≤ hBound)
    (hBound_w : hBound < 2 ^ w)
    (hr1 : st.regs 1 = gAddr) (hr2 : st.regs 2 = k) (hr3 : st.regs 3 = xAddr)
    (hr5 : st.regs 5 = locAddr) (hr6 : st.regs 6 = outAddr)
    (hr8 : st.regs 8 = (coreParamsOf cfg M r).L) (hr9 : st.regs 9 = (coreParamsOf cfg M r).Δ)
    (hr11 : st.regs 11 = (coreParamsOf cfg M r).P q) (hr13 : st.regs 13 = z)
    (hr14 : st.regs 14 = b) (hr16 : st.regs 16 = h) (hr17 : st.regs 17 = hCur)
    (hr18 : st.regs 18 = mBC) (hr20 : st.regs 20 = lenXAddr)
    (hQ : ∀ v st',
      (∃ res : CoreResult, CoreOutAt st'.mem outAddr res ∧
        OneShotSpec (coreParamsOf cfg M r) q G X res) →
      h ≤ v → v ≤ hBound → ZeroFrom st'.mem v →
      (∀ u < G.n, st'.mem (locAddr + u) = 0) →
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st'.mem a = mem₀ a) →
      Q (.returned v) st')
    (hB : ∀ c, c ≤ (C_left * stepCLeftoverCost (coreParamsOf cfg M r) routerCallCost G X
          (X.sort (· ≤ ·)) b z + C_left) + copyWordsCost (2 * k) +
        (2048 * 200000000 + 206000) * (NOf M r) ^ q * (LParam M) ^ 3 *
          (FParam cfg M) ^ (2 * q) + 120 → Pcost c) :
    ∃ o st' c, Runs w p ω (oneShotStepC3DStmt idx) st o st' c ∧ Q o st' ∧ Pcost c := by
  obtain ⟨v, st', c, hrun, hres, hv1, hv2, hZ, hloc', hfr', hc⟩ :=
    oneShotStepC3D_runs hcopy hleft hstepD st ω ha0 ha hrl hq1 hqr hG hGvalid hX hLenX hXrange
      hGloop hdegG hmG hk2 hkNq hb_pos hble hz_eq hloc hcallsBC_len hcallsBC_v hcallsBC_exp
      hmBC_eq hFBC hg_le hx_le hloc_le hout_le hlenX_ge hlenX_le hd_lg hd_lx hd_lo hd_og hd_ox
      hZero hframe₀ hBound_ge hBound_w hr1 hr2 hr3 hr5 hr6 hr8 hr9 hr11 hr13 hr14 hr16 hr17
      hr18 hr20
  exact ⟨.returned v, st', c, hrun, hQ v st' hres hv1 hv2 hZ hloc' hfr', hB c hc⟩


end MinCostFlow.ExpanderDecomp
