module

public import MinCostFlow.ExpanderDecomp.CoreProgPeel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verification of the `Core` Peeling Loop (`CoreProgPeelLoop`)

Proves `corePeelLoop_triple`, establishing the loop invariant `CorePeelInv` and step/space bounds
for the `2 * D_q`-iteration peeling loop `corePeelLoopStmt idx` (`CoreProgPeel.lean`) over
`oneShotContract`, `filterSetContract w false`, and `copyWordsContract`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-- Loop invariant for `corePeelLoopStmt idx` at iteration `iter ≤ 2 * DCore cfg M q`. -/
def CorePeelInv (cfg : ParamConfig) (M r q S_B S_C gAddr k xAddr pAddr locAddr outAddr h : ℕ)
    (G : Graph) (X : Finset ℕ) (mem₀ : ℕ → ℕ) (iter : ℕ) (st : State) : Prop :=
  let cp := coreParamsOf cfg M r
  let Sone := oneShotProgSpace S_B S_C cfg M r q (coreProgSpace S_B S_C cfg M r (q - 1))
  st.regs 0 = q ∧
  st.regs 1 = gAddr ∧
  st.regs 2 = k ∧
  st.regs 3 = xAddr ∧
  st.regs 4 = pAddr ∧
  st.regs 5 = locAddr ∧
  st.regs 6 = outAddr ∧
  st.regs 7 = h ∧
  st.regs 10 = h ∧
  st.regs 11 = h + k ∧
  st.regs 15 = 2 * DCore cfg M q ∧
  st.regs 16 = iter ∧
  h + 2 * k ≤ st.regs 12 ∧
  st.regs 12 ≤ h + 2 * k + iter * Sone ∧
  ZeroFrom st.mem (st.regs 12) ∧
  (∀ u < G.n, st.mem (locAddr + u) = 0) ∧
  (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st.mem a = mem₀ a) ∧
  ((st.regs 14 = 0 ∧ ∃ U : Finset ℕ,
      NodupVertsAt st.mem h (st.regs 13) U ∧
      U ⊆ X ∧
      100 * G.cutIn X U ≤ U.card ∧
      X.card ≤ 4 * (X \ U).card ∧
      2 * cp.D q * X.card ≤
        8 * cp.D q * U.card + 3 * (2 * cp.D q - iter) * X.card) ∨
   (st.regs 14 = 1 ∧ ∃ R : Finset ℕ,
      CoreOutAt st.mem outAddr (.expander R) ∧
      CoreSpec cp q G X (.expander R)))

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

lemma nodupVertsAt_card {mem : ℕ → ℕ} {addr len : ℕ} {S : Finset ℕ}
    (h : NodupVertsAt mem addr len S) : S.card = len := by
  obtain ⟨ls, hnd, hfin, rfl, _⟩ := nodupVertsAt_iff_exists_listAt.mp h
  rw [← hfin, List.toFinset_card_of_nodup hnd]

lemma nodupVertsAt_congr {mem₁ mem₂ : ℕ → ℕ} {addr len : ℕ} {S : Finset ℕ}
    (h : NodupVertsAt mem₁ addr len S) (heq : ∀ i < len, mem₂ (addr + i) = mem₁ (addr + i)) :
    NodupVertsAt mem₂ addr len S := by
  obtain ⟨ls, hnd, hfin, rfl, hlat⟩ := nodupVertsAt_iff_exists_listAt.mp h
  exact nodupVertsAt_iff_exists_listAt.mpr ⟨ls, hnd, hfin, rfl,
    fun i hi => by rw [heq i hi]; exact hlat i hi⟩

lemma nodupVertsAt_of_copyWords {mem₁ mem₂ : ℕ → ℕ} {src dst len : ℕ} {S : Finset ℕ}
    (h : NodupVertsAt mem₁ src len S) (hcp : ∀ i < len, mem₂ (dst + i) = mem₁ (src + i)) :
    NodupVertsAt mem₂ dst len S := by
  obtain ⟨ls, hnd, hfin, rfl, hlat⟩ := nodupVertsAt_iff_exists_listAt.mp h
  exact nodupVertsAt_iff_exists_listAt.mpr ⟨ls, hnd, hfin, rfl,
    fun i hi => by rw [hcp i hi]; exact hlat i hi⟩

lemma nodupVertsAt_append {mem : ℕ → ℕ} {addr len₁ len₂ : ℕ} {S₁ S₂ : Finset ℕ}
    (h₁ : NodupVertsAt mem addr len₁ S₁)
    (h₂ : NodupVertsAt mem (addr + len₁) len₂ S₂)
    (hdisj : Disjoint S₁ S₂) :
    NodupVertsAt mem addr (len₁ + len₂) (S₁ ∪ S₂) := by
  obtain ⟨l₁, hnd₁, hfin₁, rfl, hlat₁⟩ := nodupVertsAt_iff_exists_listAt.mp h₁
  obtain ⟨l₂, hnd₂, hfin₂, rfl, hlat₂⟩ := nodupVertsAt_iff_exists_listAt.mp h₂
  refine nodupVertsAt_iff_exists_listAt.mpr ⟨l₁ ++ l₂, ?_, ?_, (List.length_append).symm, ?_⟩
  · refine List.nodup_append.mpr ⟨hnd₁, hnd₂, fun a ha₁ b hb₂ hab => ?_⟩
    subst hab
    exact Finset.disjoint_left.mp hdisj
      (hfin₁ ▸ List.mem_toFinset.mpr ha₁) (hfin₂ ▸ List.mem_toFinset.mpr hb₂)
  · simp [List.toFinset_append, hfin₁, hfin₂]
  · intro i hi
    rw [List.length_append] at hi
    by_cases hlt : i < l₁.length
    · rw [List.getElem_append_left hlt]
      exact hlat₁ i hlt
    · have hge : l₁.length ≤ i := Nat.le_of_not_lt hlt
      rw [List.getElem_append_right hge]
      have hidx : addr + i = addr + l₁.length + (i - l₁.length) := by omega
      rw [hidx]
      exact hlat₂ (i - l₁.length) (by omega)

/-- Single peeling iteration of `corePeelBodyStmt idx`. -/
private lemma corePeelBody_runs {w : ℕ} {p : Program} {idx : CoreIdx}
    {cfg : ParamConfig} {M r q K_B K_C S_B S_C : ℕ}
    (hDiff : MeetsContract w p idx.filterDiff (filterSetContract w false))
    (hCopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    (hOneShot : MeetsContract w p idx.oneShot
      (oneShotContract cfg M r q w K_B K_C S_B S_C
        (coreProgTime K_B K_C cfg M r (q - 1)) (coreProgSpace S_B S_C cfg M r (q - 1))))
    {gAddr k xAddr pAddr locAddr outAddr h : ℕ} {G : Graph} {X : Finset ℕ} {mem₀ : ℕ → ℕ}
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    (hP : CoreParamsAt mem₀ pAddr (coreParamsOf cfg M r) r)
    (hG : GraphAt mem₀ gAddr G) (hGvalid : G.IsValid)
    (hGn : G.n ≤ 2048 * LParam M * (NOf M r) ^ r)
    (hX : VertsAt mem₀ xAddr k X) (hXrange : X ⊆ Finset.range G.n)
    (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hkgt : (coreParamsOf cfg M r).N ^ (q - 1) < k)
    (hkNq : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hmG : G.m ≤ (coreParamsOf cfg M r).Δ * k)
    (hg_h : gAddr + 2 + 2 * G.m ≤ h) (hx_h : xAddr + k ≤ h)
    (hp_h : pAddr + coreParamsSize r ≤ h) (hloc_h : locAddr + G.n ≤ h)
    (hout_h : outAddr + 2 + k ≤ h)
    (hd_lg : DisjointRange locAddr G.n gAddr (2 + 2 * G.m))
    (hd_lx : DisjointRange locAddr G.n xAddr k)
    (hd_lp : DisjointRange locAddr G.n pAddr (coreParamsSize r))
    (hd_lo : DisjointRange locAddr G.n outAddr (2 + k))
    (hd_og : DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m))
    (hd_ox : DisjointRange outAddr (2 + k) xAddr k)
    (hd_op : DisjointRange outAddr (2 + k) pAddr (coreParamsSize r))
    (hw : h + coreProgSpace S_B S_C cfg M r q < 2 ^ w)
    (iter : ℕ) (hiter : iter < 2 * DCore cfg M q) :
    Triple w p
      (CorePeelInv cfg M r q S_B S_C gAddr k xAddr pAddr locAddr outAddr h G X mem₀ iter)
      (corePeelBodyStmt idx)
      (normalPost fun st₁ =>
        CorePeelInv cfg M r q S_B S_C gAddr k xAddr pAddr locAddr outAddr h G X mem₀ (iter + 1)
          { st₁ with regs := Function.update st₁.regs 16 (iter + 1) } ∧
        st₁.regs 16 = iter)
      (fun _ =>
        oneShotProgCost K_B K_C cfg M r q (coreProgTime K_B K_C cfg M r (q - 1)) +
          260 * k + 450) := by
  set cp := coreParamsOf cfg M r
  set Tprev := coreProgTime K_B K_C cfg M r (q - 1)
  set Sprev := coreProgSpace S_B S_C cfg M r (q - 1)
  set Sone := oneShotProgSpace S_B S_C cfg M r q Sprev
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  have hsp_rec : 2 * k + 2 * DCore cfg M q * Sone ≤ coreProgSpace S_B S_C cfg M r q :=
    coreProgSpace_rec S_B S_C cfg M r q k hq1 hkNq
  have hsp4000 : 4000 ≤ coreProgSpace S_B S_C cfg M r q :=
    coreProgSpace_base_ge S_B S_C cfg M r q
  have hw16 : 16 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hDq_pos : 0 < cp.D q := hcfg.hD_pos hq1 hqr
  intro st ω hInv
  rcases hInv with ⟨hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr10, hr11, hr15, hr16,
    hhCur_lo, hhCur_hi, hZero, hloc, hframe₀, hdisj⟩
  have hhCur_hi' : st.regs 12 ≤ h + 2 * k + iter * Sone := hhCur_hi
  have hhCur_Sone_le : st.regs 12 + Sone ≤ h + coreProgSpace S_B S_C cfg M r q := by
    have hmul : (iter + 1) * Sone ≤ 2 * DCore cfg M q * Sone :=
      Nat.mul_le_mul_right Sone (by omega)
    rw [Nat.add_one_mul] at hmul
    omega
  have hcs : coreParamsSize r = 7 + 3 * r := rfl
  have hkX : k = X.card := hX.1
  have hhCur_Sone_w : st.regs 12 + Sone < 2 ^ w := by omega
  dsimp only [corePeelBodyStmt]
  refine runs_start_le ?_
  -- Outer cond: `r14 = 0`
  refine runs_cond_le (v := if st.regs 14 = 0 then 1 else 0)
    (Expr.eval_eq_op (Expr.eval_reg _ _ _) (Expr.eval_const (by omega)) hw1) ?_ ?_
  · -- `r14 = 0`: check `4 * r13 < k`
    intro hne14
    have hr14 : st.regs 14 = 0 := by by_contra hne; simp [hne] at hne14
    have hUcase : ∃ U : Finset ℕ,
        NodupVertsAt st.mem h (st.regs 13) U ∧
        U ⊆ X ∧
        100 * G.cutIn X U ≤ U.card ∧
        X.card ≤ 4 * (X \ U).card ∧
        2 * cp.D q * X.card ≤
          8 * cp.D q * U.card + 3 * (2 * cp.D q - iter) * X.card := by
      rcases hdisj with ⟨_, hU⟩ | ⟨h1, _⟩
      · exact hU
      · omega
    obtain ⟨U, hUat, hUX, hUcut, hUbal, hUfuel⟩ := hUcase
    set uLen := st.regs 13
    have hUcard : U.card = uLen := nodupVertsAt_card hUat
    have huLen_le : uLen ≤ k := by rw [← hUcard, hX.1]; exact Finset.card_le_card hUX
    have h4u_w : 4 * uLen < 2 ^ w := by
      have h2k_le : 2 * k ≤ coreProgSpace S_B S_C cfg M r q := by omega
      have h4k_le : 4 * k ≤ 2 * coreProgSpace S_B S_C cfg M r q := by omega
      -- We have `4 * uLen ≤ 4 * k`. Bound `4 * k` by `Sone`,
      -- using `2 * DCore ≥ 2048` and `Sone ≥ 65536`.
      have hSone_k : 4 * k ≤ Sone := by
        unfold Sone oneShotProgSpace; dsimp only
        have hN1 : 1 ≤ NOf M r := le_trans (by decide) (four_le_NOf M r)
        have hL1 : 1 ≤ LParam M := le_trans (by decide) (four_le_LParam M)
        have hF1 : 1 ≤ FParam cfg M := one_le_FParam cfg M
        have hprod : 1 ≤ (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) :=
          Nat.mul_le_mul (Nat.one_le_pow _ _ hL1) (Nat.one_le_pow _ _ hF1)
        have h65 : 4 * (NOf M r) ^ q ≤
            65536 * (NOf M r) ^ q * (LParam M) ^ 3 * (FParam cfg M) ^ (2 * q) := by
          calc 4 * (NOf M r) ^ q = (4 * (NOf M r) ^ q) * 1 := (Nat.mul_one _).symm
            _ ≤ (65536 * (NOf M r) ^ q) * ((LParam M) ^ 3 * (FParam cfg M) ^ (2 * q)) :=
                Nat.mul_le_mul (by omega) hprod
            _ = _ := by ring
        have hk' : k ≤ (NOf M r) ^ q := hkNq
        omega
      omega
    refine runs_cond_le (v := if 4 * uLen < k then 1 else 0)
      (Expr.eval_lt_op
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg _ _ _) h4u_w)
        (Expr.eval_reg_of_eq hr2) hw1) ?_ ?_
    · -- Active iteration: `4 * uLen < k`
      intro hne4
      have h4ult : 4 * uLen < k := by by_contra hge; simp [hge] at hne4
      set X' := X \ U
      have hX'sub : X' ⊆ X := Finset.sdiff_subset
      have hX'card : X'.card + U.card = X.card := Finset.card_sdiff_add_card_eq_card hUX
      have h3k : 3 * k < 4 * X'.card := by omega
      have hX'range : X' ⊆ Finset.range G.n := hX'sub.trans hXrange
      have hX'loop : ∀ e ∈ G.inside X', e.1 ≠ e.2 := fun e he => by
        rw [mem_inside_iff] at he
        exact hGloop e (mem_inside_iff.mpr ⟨he.1, hX'sub he.2.1, hX'sub he.2.2⟩)
      have hX'deg : ∀ v ∈ X', G.degIn X' v ≤ cp.Δ :=
        fun v hv => le_trans (degIn_mono hX'sub v) (hdegG v (hX'sub hv))
      have hmG' : G.m ≤ 2 * cp.Δ * X'.card := by
        have hk2X' : k ≤ 2 * X'.card := by omega
        calc G.m ≤ cp.Δ * k := hmG
          _ ≤ cp.Δ * (2 * X'.card) := Nat.mul_le_mul_left _ hk2X'
          _ = 2 * cp.Δ * X'.card := by ring
      have hX'size1 : q = 1 → 2 ≤ X'.card ∧ X'.card ≤ cp.N := by
        intro hq
        subst hq
        simp only [Nat.sub_self, pow_zero, pow_one] at hkgt hkNq
        omega
      have hX'size2 : 2 ≤ q → cp.N ^ (q - 1) / 2 ≤ X'.card ∧ X'.card ≤ cp.N ^ q := by
        intro hq2
        have hdiv : 2 * (cp.N ^ (q - 1) / 2) ≤ cp.N ^ (q - 1) := Nat.mul_div_le _ 2
        omega
      -- Reconstruct `CoreParamsAt`, `GraphAt`, `VertsAt` in `st.mem` from `hframe₀`
      have hPst : CoreParamsAt st.mem pAddr cp r := by
        have hag : ∀ a, pAddr ≤ a → a < pAddr + coreParamsSize r → st.mem a = mem₀ a := fun a h1 h2 =>
          hframe₀ a (by omega)
            (by rcases hd_op with d1 | d2 <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
        refine ⟨by rw [hag pAddr le_rfl (by omega)]; exact hP.1,
          by rw [hag (pAddr + 1) (by omega) (by omega)]; exact hP.2.1,
          by rw [hag (pAddr + 2) (by omega) (by omega)]; exact hP.2.2.1,
          by rw [hag (pAddr + 3) (by omega) (by omega)]; exact hP.2.2.2.1,
          fun j hj => by rw [hag (pAddr + 4 + j) (by omega) (by omega)]; exact hP.2.2.2.2.1 j hj,
          fun j hj => by rw [hag (pAddr + 5 + r + j) (by omega) (by omega)]; exact hP.2.2.2.2.2.1 j hj,
          fun j hj => by rw [hag (pAddr + 6 + 2 * r + j) (by omega) (by omega)]; exact hP.2.2.2.2.2.2 j hj⟩
      have hGst : GraphAt st.mem gAddr G :=
        hG.congr fun a h1 h2 => by
          have hlenG : G.encode.length = 2 + 2 * G.m := graph_encode_length G
          exact hframe₀ a (by omega)
            (by rcases hd_og with d1 | d2 <;> [exact Or.inr (by omega); exact Or.inl (by omega)])
      have hXst : VertsAt st.mem xAddr k X := by
        refine ⟨hX.1, fun i hi => ?_⟩
        have hik : i < k := by rw [Finset.length_sort] at hi; rw [hX.1]; exact hi
        rw [hframe₀ (xAddr + i) (by omega)
          (by rcases hd_ox with d1 | d2 <;> [exact Or.inr (by omega); exact Or.inl (by omega)])]
        exact hX.2 i hi
      dsimp only [seqStmts]
      -- Step 1: `r17 := call idx.filterDiff [k, xAddr, uLen, h, locAddr, h + k]`
      have hDiff1_pre : (filterSetContract w false).pre
          [k, xAddr, uLen, h, locAddr, h + k] st.mem :=
        ⟨G.n, k, xAddr, uLen, h, locAddr, h + k, X, U, rfl, hXst, hUat, hXrange,
          hUX.trans hXrange, hloc,
          ⟨by omega, by omega, by omega, by omega, by omega, by omega, hw16⟩,
          ⟨hd_lx, Or.inl hloc_h, Or.inl (by omega), Or.inr (by omega), Or.inr (by omega)⟩⟩
      refine runs_seq_call_le (vs := [k, xAddr, uLen, h, locAddr, h + k]) hDiff
        (by simp [evalArgs, Expr.eval, hr2, hr3, hr10, hr5, hr11, uLen])
        (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        hDiff1_pre ?_
      intro k' mem1 _pos1 hpostD1
      simp only [filterSetContract, List.getD_cons_zero, List.getD_cons_succ, Bool.false_eq_true,
        ↓reduceIte] at hpostD1
      have hrdXst : (readList st.mem xAddr k).toFinset = X := by
        have hlen : (X.sort (· ≤ ·)).length = k := by rw [Finset.length_sort, ← hXst.1]
        rw [← hlen, readList_eq_of_listAt hXst.2]; ext v; simp
      have hrdUst : (readList st.mem h uLen).toFinset = U := hUat.2
      rw [hrdXst, hrdUst] at hpostD1
      rcases hpostD1 with ⟨hk'_le, hX'1, hfr1⟩
      have hk'_eq : k' = X'.card := hX'1.1
      -- Preserve everything outside `[h + k, h + 2 * k)` into `mem1`
      have hP1 : CoreParamsAt mem1 pAddr cp r := by
        have hag : ∀ a, pAddr ≤ a → a < pAddr + coreParamsSize r → mem1 a = st.mem a :=
          fun a h1 h2 => hfr1 a (Or.inl (by omega))
        have hcs : coreParamsSize r = 7 + 3 * r := rfl
        refine ⟨by rw [hag pAddr le_rfl (by omega)]; exact hPst.1,
          by rw [hag (pAddr + 1) (by omega) (by omega)]; exact hPst.2.1,
          by rw [hag (pAddr + 2) (by omega) (by omega)]; exact hPst.2.2.1,
          by rw [hag (pAddr + 3) (by omega) (by omega)]; exact hPst.2.2.2.1,
          fun j hj => by rw [hag (pAddr + 4 + j) (by omega) (by omega)]; exact hPst.2.2.2.2.1 j hj,
          fun j hj => by rw [hag (pAddr + 5 + r + j) (by omega) (by omega)]; exact hPst.2.2.2.2.2.1 j hj,
          fun j hj => by rw [hag (pAddr + 6 + 2 * r + j) (by omega) (by omega)]; exact hPst.2.2.2.2.2.2 j hj⟩
      have hG1 : GraphAt mem1 gAddr G :=
        hGst.congr fun a h1 h2 => by
          have hlenG : G.encode.length = 2 + 2 * G.m := graph_encode_length G
          exact hfr1 a (Or.inl (by omega))
      have hU1 : NodupVertsAt mem1 h uLen U :=
        nodupVertsAt_congr hUat fun i hi => hfr1 (h + i) (Or.inl (by omega))
      have hloc1 : ∀ u < G.n, mem1 (locAddr + u) = 0 := fun u hu => by
        rw [hfr1 (locAddr + u) (Or.inl (by omega))]; exact hloc u hu
      have hZero1 : ZeroFrom mem1 (st.regs 12) := fun a ha => by
        rw [hfr1 a (Or.inr (by omega))]; exact hZero a ha
      have hfr1_0 : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → mem1 a = mem₀ a := fun a ha hno => by
        rw [hfr1 a (Or.inl (by omega))]; exact hframe₀ a ha hno
      -- Step 2: `r12 := call idx.oneShot [q, gAddr, k', h + k, pAddr, locAddr, outAddr, st.regs 12]`
      have hOS_pre : (oneShotContract cfg M r q w K_B K_C S_B S_C Tprev Sprev).pre
          [q, gAddr, k', h + k, pAddr, locAddr, outAddr, st.regs 12] mem1 :=
        ⟨gAddr, k', h + k, pAddr, locAddr, outAddr, st.regs 12, G, X',
          rfl, ha0, ha, hrl, hq1, hqr, hP1, hG1, hGvalid, hGn, hX'1, hX'range, hX'loop,
          hX'deg, hk'_eq ▸ hmG', fun hq => hk'_eq ▸ hX'size1 hq, fun hq2 => hk'_eq ▸ hX'size2 hq2,
          hloc1, by omega, by omega, by omega, by omega, by omega,
          hd_lg, Or.inl (by omega), hd_lp,
          by rcases hd_lo with d1 | d2 <;> [exact Or.inl d1; exact Or.inr (by omega)],
          by rcases hd_og with d1 | d2 <;> [exact Or.inl (by omega); exact Or.inr d2],
          Or.inl (by omega),
          by rcases hd_op with d1 | d2 <;> [exact Or.inl (by omega); exact Or.inr d2],
          hZero1, hhCur_Sone_w⟩
      refine runs_seq_call_le
        (vs := [q, gAddr, k', h + k, pAddr, locAddr, outAddr, st.regs 12]) hOneShot
        (by simp [evalArgs, Expr.eval, hr0, hr1, hr11, hr4, hr5, hr6])
        (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
        hOS_pre ?_
      intro h2 mem2 _pos2 hpostOS
      have hOS_res := hpostOS gAddr k' (h + k) pAddr locAddr outAddr (st.regs 12) G X'
        rfl ha0 ha hrl hq1 hqr hP1 hG1 hGvalid hGn hX'1 hX'range hX'loop
        hX'deg (hk'_eq ▸ hmG') (fun hq => hk'_eq ▸ hX'size1 hq) (fun hq2 => hk'_eq ▸ hX'size2 hq2)
        hloc1 (by omega) (by omega) (by omega) (by omega) (by omega)
        hd_lg (Or.inl (by omega)) hd_lp
        (by rcases hd_lo with d1 | d2 <;> [exact Or.inl d1; exact Or.inr (by omega)])
        (by rcases hd_og with d1 | d2 <;> [exact Or.inl (by omega); exact Or.inr d2])
        (Or.inl (by omega))
        (by rcases hd_op with d1 | d2 <;> [exact Or.inl (by omega); exact Or.inr d2])
        hZero1 hhCur_Sone_w
      rcases hOS_res with ⟨⟨res, hResOut, hResSpec⟩, hh2_lo, hh2_hi, hZero2, hloc2, hfr2⟩
      have hh2_iter : h2 ≤ h + 2 * k + (iter + 1) * Sone := by
        rw [Nat.add_one_mul iter Sone]; change h2 ≤ st.regs 12 + Sone at hh2_hi; omega
      have hfr2_0 : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → mem2 a = mem₀ a := fun a ha hno => by
        rw [hfr2 a (by omega) (by omega)]; exact hfr1_0 a ha hno
      -- Step 3: `r18 := load outAddr`
      set tag := mem2 outAddr
      refine runs_seq_assign_le (v := tag) (by simp [Expr.eval, hr6, tag]) ?_
      -- Step 4: branch on `tag = 1`
      cases res with
      | expander R =>
        have htag1 : tag = 1 := hResOut.1
        refine runs_cond_le (v := 1) (by simp [Expr.eval, htag1, hw1]) ?_
          (fun h => absurd h (by decide))
        intro _
        refine runs_assign_le (v := 1) (by simp [Expr.eval, hw1]) ?_ ?_
        · refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
            by simp [hr5], by simp [hr6], by simp [hr7], by simp [hr10], by simp [hr11],
            by simp [hr15], by simp, by simp; omega, by simp; exact hh2_iter, hZero2, hloc2, hfr2_0,
            Or.inr ⟨by simp, R, hResOut, ?_⟩⟩, by simp [hr16]⟩
          rcases hResSpec with ⟨hRX', h11, hRexp⟩
          exact ⟨hRX'.trans hX'sub, by omega, hRexp⟩
        · have hargD1 : argsSize [.reg 2, .reg 3, .reg 13, .reg 10, .reg 5, .reg 11] = 6 := by decide
          have hargOS : argsSize [.reg 0, .reg 1, .reg 17, .reg 11, .reg 4, .reg 5, .reg 6,
            .reg 12] = 8 := by decide
          simp only [filterSetContract, oneShotContract, Expr.size, hargD1, hargOS, filterSetCost,
            List.getD_cons_zero, List.getD_cons_succ]
          omega
      | cut V =>
        have htag0 : tag = 0 := hResOut.1
        rcases hResOut with ⟨_, V_list, hVnd, hVfin, hVlen_eq, hVlat⟩
        rcases hResSpec with ⟨hVX', hcutV, hV1, hV2⟩
        have hVcard : V.card = V_list.length := by
          rw [← hVfin, List.toFinset_card_of_nodup hVnd]
        have hVlen_le : V_list.length ≤ k' := by
          rw [← hVcard, hk'_eq]; exact Finset.card_le_card hVX'
        refine runs_cond_le (v := 0) (by simp [Expr.eval, htag0, hw1])
          (fun h => absurd rfl h) ?_
        intro _
        dsimp only [seqStmts]
        -- `r19 := load (outAddr + 1)` (= V_list.length)
        refine runs_seq_assign_le (v := V_list.length)
          (by simp [Expr.eval, hr6, hw1, show outAddr + 1 < 2 ^ w by omega, hVlen_eq]) ?_
        -- `r21 := h + uLen`
        refine runs_seq_assign_le (v := h + uLen)
          (by simp [Expr.eval, hr10, uLen, show h + uLen < 2 ^ w by omega]) ?_
        -- `r22 := outAddr + 2`
        refine runs_seq_assign_le (v := outAddr + 2)
          (by simp [Expr.eval, hr6, show 2 < 2 ^ w by omega, show outAddr + 2 < 2 ^ w by omega]) ?_
        -- Preserve `X'` and `U` in `mem2`
        have hX'2 : VertsAt mem2 (h + k) k' X' := by
          refine ⟨hX'1.1, fun i hi => ?_⟩
          have hik' : i < k' := by rw [Finset.length_sort] at hi; rw [hX'1.1]; exact hi
          rw [hfr2 (h + k + i) (by omega) (Or.inr (by omega))]
          exact hX'1.2 i hi
        have hU2 : NodupVertsAt mem2 h uLen U :=
          nodupVertsAt_congr hU1 fun i hi => hfr2 (h + i) (by omega) (Or.inr (by omega))
        have hV2at : NodupVertsAt mem2 (outAddr + 2) V_list.length V :=
          nodupVertsAt_iff_exists_listAt.mpr ⟨V_list, hVnd, hVfin, rfl, hVlat⟩
        -- Helper to finish after writing `Y` (the smaller side of `V` in `X'`) at `h + uLen`
        set regsMid :=
          Function.update
            (Function.update
              (Function.update
                (Function.update
                  (Function.update
                    (Function.update st.regs 17 k') 12 h2) 18 tag)
                19 V_list.length) 21 (h + uLen)) 22 (outAddr + 2)
        have hfinish_Y : ∀ (Y : Finset ℕ) (yLen : ℕ) (mem3 : ℕ → ℕ),
            Y = smallerSide X' V →
            yLen = Y.card →
            NodupVertsAt mem3 (h + uLen) yLen Y →
            MemFrame mem2 mem3 (h + uLen) (h + k) →
            ∀ st' : State,
              st'.mem = mem3 →
              (∀ j, j ≤ 22 → j ≠ 20 → st'.regs j = regsMid j) →
              st'.regs 20 = yLen →
              ∃ o stF cF,
                Runs w p ω (.assign 13 (.bin .add (.reg 13) (.reg 20))) st' o stF cF ∧
                normalPost (fun st₁ =>
                  CorePeelInv cfg M r q S_B S_C gAddr k xAddr pAddr locAddr outAddr h G X mem₀
                    (iter + 1) { st₁ with regs := Function.update st₁.regs 16 (iter + 1) } ∧
                  st₁.regs 16 = iter) o stF ∧
                cF ≤ 10 := by
          intro Y yLen mem3 hY_eq hyLen hYat hfr3 st' hmem3 hregs_eq hreg20
          have hYX' : Y ⊆ X' := by
            rw [hY_eq]; unfold smallerSide; split_ifs <;> [exact hVX'; exact Finset.sdiff_subset]
          have hY2 : 2 * Y.card ≤ X'.card := by
            have hadd : (X' \ V).card + V.card = X'.card := Finset.card_sdiff_add_card_eq_card hVX'
            rw [hY_eq]; unfold smallerSide; split_ifs <;> omega
          have hYcut : 100 * G.cutIn X' Y ≤ Y.card := by
            rw [hY_eq]; unfold smallerSide
            split_ifs with hle
            · rw [min_eq_left hle] at hcutV; exact hcutV
            · rw [cutIn_sdiff G X' V hVX']; rw [min_eq_right (le_of_not_ge hle)] at hcutV; exact hcutV
          have hYlb : X'.card / cp.D q + 1 ≤ 2 * Y.card := by
            rw [hY_eq]; unfold smallerSide; split_ifs <;> [exact hV1; exact hV2]
          have hY_big : 3 * X.card < 8 * cp.D q * Y.card := by
            have hdiv_lt : X'.card < cp.D q * (X'.card / cp.D q + 1) := by
              have hmod : X'.card % cp.D q < cp.D q := Nat.mod_lt _ hDq_pos
              have hdm := Nat.div_add_mod X'.card (cp.D q)
              rw [Nat.mul_add, Nat.mul_one]; omega
            have h1 : X'.card < cp.D q * (2 * Y.card) :=
              lt_of_lt_of_le hdiv_lt (Nat.mul_le_mul_left _ hYlb)
            have h2 : 4 * X'.card < 4 * (cp.D q * (2 * Y.card)) := by omega
            have h3 : 4 * (cp.D q * (2 * Y.card)) = 8 * cp.D q * Y.card := by ring
            omega
          have hdisjUY : Disjoint U Y :=
            Finset.disjoint_of_subset_right hYX' disjoint_sdiff_self_right
          have hU'X : U ∪ Y ⊆ X := Finset.union_subset hUX (hYX'.trans hX'sub)
          have hU'card : (U ∪ Y).card = U.card + Y.card := Finset.card_union_of_disjoint hdisjUY
          have hU'cut : 100 * G.cutIn X (U ∪ Y) ≤ (U ∪ Y).card := by
            have hadd := cutIn_union_le G hUX hYX'
            dsimp only [X'] at hYcut; rw [hU'card]; omega
          have hU'bal : X.card ≤ 4 * (X \ (U ∪ Y)).card := by
            have hsd : (X \ (U ∪ Y)).card + (U ∪ Y).card = X.card :=
              Finset.card_sdiff_add_card_eq_card hU'X
            omega
          have hU'fuel : 2 * cp.D q * X.card ≤
              8 * cp.D q * (U ∪ Y).card + 3 * (2 * cp.D q - (iter + 1)) * X.card := by
            rw [hU'card, Nat.mul_add]
            have hrem : 2 * cp.D q - iter = (2 * cp.D q - (iter + 1)) + 1 := by
              change 2 * DCore cfg M q - iter = (2 * DCore cfg M q - (iter + 1)) + 1; omega
            rw [hrem] at hUfuel
            have hstep : 3 * ((2 * cp.D q - (iter + 1)) + 1) * X.card =
                3 * (2 * cp.D q - (iter + 1)) * X.card + 3 * X.card := by ring
            rw [hstep] at hUfuel
            omega
          have hU3 : NodupVertsAt mem3 h uLen U :=
            nodupVertsAt_congr hU2 fun i hi => hfr3 (h + i) (Or.inl (by omega))
          have hUYat : NodupVertsAt mem3 h (uLen + yLen) (U ∪ Y) :=
            nodupVertsAt_append hU3 hYat hdisjUY
          have hZero3 : ZeroFrom mem3 h2 := fun a ha => by
            rw [hfr3 a (Or.inr (by omega))]; exact hZero2 a ha
          have hloc3 : ∀ u < G.n, mem3 (locAddr + u) = 0 := fun u hu => by
            rw [hfr3 (locAddr + u) (Or.inl (by omega))]; exact hloc2 u hu
          have hfr3_0 : ∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → mem3 a = mem₀ a :=
            fun a ha hno => by rw [hfr3 a (Or.inl (by omega))]; exact hfr2_0 a ha hno
          have hreg13 : st'.regs 13 = uLen := by
            rw [hregs_eq 13 (by omega) (by omega)]; simp [regsMid, uLen]
          have hsum_w : uLen + yLen < 2 ^ w := by
            have : uLen + yLen ≤ k := by rw [← hUcard, hyLen, ← hU'card, hX.1]; exact Finset.card_le_card hU'X
            omega
          refine runs_start_le ?_
          refine runs_assign_le (v := uLen + yLen)
            (Expr.eval_add (Expr.eval_reg_of_eq hreg13) (Expr.eval_reg_of_eq hreg20) hsum_w)
            ?_ (by simp [Expr.size])
          refine ⟨⟨by simp [hregs_eq 0 (by omega) (by omega), regsMid, hr0],
            by simp [hregs_eq 1 (by omega) (by omega), regsMid, hr1],
            by simp [hregs_eq 2 (by omega) (by omega), regsMid, hr2],
            by simp [hregs_eq 3 (by omega) (by omega), regsMid, hr3],
            by simp [hregs_eq 4 (by omega) (by omega), regsMid, hr4],
            by simp [hregs_eq 5 (by omega) (by omega), regsMid, hr5],
            by simp [hregs_eq 6 (by omega) (by omega), regsMid, hr6],
            by simp [hregs_eq 7 (by omega) (by omega), regsMid, hr7],
            by simp [hregs_eq 10 (by omega) (by omega), regsMid, hr10],
            by simp [hregs_eq 11 (by omega) (by omega), regsMid, hr11],
            by simp [hregs_eq 15 (by omega) (by omega), regsMid, hr15],
            by simp,
            by simp [hregs_eq 12 (by omega) (by omega), regsMid]; omega,
            by simp [hregs_eq 12 (by omega) (by omega), regsMid]; exact hh2_iter,
            by simpa [hregs_eq 12 (by omega) (by omega), regsMid, hmem3] using hZero3,
            by simpa [hmem3] using hloc3,
            by simpa [hmem3] using hfr3_0,
            Or.inl ⟨by simp [hregs_eq 14 (by omega) (by omega), regsMid, hr14], U ∪ Y,
              by simpa [hmem3] using hUYat, hU'X, hU'cut, hU'bal, hU'fuel⟩⟩,
            by simp [hregs_eq 16 (by omega) (by omega), regsMid, hr16]⟩
        -- Branch on `k' < 2 * V_list.length`
        have h2V_w : 2 * V_list.length < 2 ^ w := by omega
        refine runs_seq_cond_le (v := if k' < 2 * V_list.length then 1 else 0)
          (Expr.eval_lt_op (Expr.eval_reg_of_eq (by simp [regsMid]))
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_reg_of_eq (by simp [regsMid])) h2V_w)
            hw1) ?_ ?_
        · -- `k' < 2 * V_list.length`: `Y = X' \ V`, call `filterDiff`
          intro hneLt
          have hlt2V : k' < 2 * V_list.length := by by_contra hge; simp [hge] at hneLt
          have hDiff2_pre : (filterSetContract w false).pre
              [k', h + k, V_list.length, outAddr + 2, locAddr, h + uLen] mem2 :=
            ⟨G.n, k', h + k, V_list.length, outAddr + 2, locAddr, h + uLen, X', V,
              rfl, hX'2, hV2at, hX'range, (hVX'.trans hX'sub).trans hXrange, hloc2,
              ⟨by omega, by omega, by omega, by omega, by omega, by omega, hw16⟩,
              ⟨Or.inl (by omega),
               by rcases hd_lo with d1 | d2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)],
               Or.inl (by omega),
               Or.inl (by omega),
               Or.inr (by omega)⟩⟩
          refine runs_seq_call_le (vs := [k', h + k, V_list.length, outAddr + 2, locAddr, h + uLen])
            hDiff (by simp [evalArgs, Expr.eval, regsMid, hr11, hr5])
            (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
            hDiff2_pre ?_
          intro yLen mem3 _pos3 hpostD2
          simp only [filterSetContract, List.getD_cons_zero, List.getD_cons_succ,
            Bool.false_eq_true, ↓reduceIte] at hpostD2
          have hrdX'2 : (readList mem2 (h + k) k').toFinset = X' := by
            have hlen : (X'.sort (· ≤ ·)).length = k' := by rw [Finset.length_sort, ← hX'2.1]
            rw [← hlen, readList_eq_of_listAt hX'2.2]; ext v; simp
          have hrdV2 : (readList mem2 (outAddr + 2) V_list.length).toFinset = V := hV2at.2
          rw [hrdX'2, hrdV2] at hpostD2
          rcases hpostD2 with ⟨_, hY3, hfr3⟩
          have hfr3' : MemFrame mem2 mem3 (h + uLen) (h + k) := by
            have heq : h + uLen + k' = h + k := by omega
            rwa [heq] at hfr3
          have hY_eq : X' \ V = smallerSide X' V := by
            have hadd : (X' \ V).card + V.card = X'.card := Finset.card_sdiff_add_card_eq_card hVX'
            unfold smallerSide
            exact (ite_eq_right (fun h => by omega)).symm
          obtain ⟨o, stF, cF, hrunF, hqF, hcF⟩ := hfinish_Y (X' \ V) yLen mem3
            hY_eq hY3.1 hY3.toNodupVertsAt hfr3'
            { mem := mem3, regs := Function.update regsMid 20 yLen, pos := _pos3 } rfl
            (fun j hj hne => by simp [hne]) (by simp)
          refine ⟨o, stF, cF, hrunF, hqF, ?_⟩
          have hargD1 : argsSize [.reg 2, .reg 3, .reg 13, .reg 10, .reg 5, .reg 11] = 6 := by decide
          have hargOS : argsSize [.reg 0, .reg 1, .reg 17, .reg 11, .reg 4, .reg 5, .reg 6,
            .reg 12] = 8 := by decide
          have hargD2 : argsSize [.reg 17, .reg 11, .reg 19, .reg 22, .reg 5, .reg 21] = 6 := by decide
          simp only [filterSetContract, oneShotContract, Expr.size, hargD1, hargOS, hargD2,
            filterSetCost, List.getD_cons_zero, List.getD_cons_succ]
          omega
        · -- `2 * V_list.length ≤ k'`: `Y = V`, call `copyWords`, set `r20 := V_list.length`
          intro hzeroLt
          have hle2V : 2 * V_list.length ≤ k' := by
            by_contra hgt; simp [Nat.lt_of_not_ge hgt] at hzeroLt
          have hCp_pre : (copyWordsContract w).pre [V_list.length, outAddr + 2, h + uLen] mem2 :=
            ⟨V_list.length, outAddr + 2, h + uLen, rfl, by omega, by omega, by omega, by omega,
              Or.inr (by omega), fun i hi => by
                rw [hVlat i hi]
                have hmem : V_list[i] ∈ V := hVfin ▸ List.mem_toFinset.mpr (List.getElem_mem hi)
                have hlt : V_list[i] < G.n := Finset.mem_range.mp (hX'range (hVX' hmem))
                omega⟩
          dsimp only [seqStmts]
          -- Run the copyWords + `r20 := r19` sequence first, then chain `.assign 13 ...`
          have hsub : ∃ st3 cSub,
              Runs w p ω
                (.seq (.call 20 idx.copyWords [.reg 19, .reg 22, .reg 21])
                  (.assign 20 (.reg 19)))
                { mem := mem2
                  regs := Function.update
                    (Function.update
                      (Function.update
                        (Function.update
                          (Function.update
                            (Function.update st.regs 17 k') 12 h2) 18 tag)
                          19 V_list.length) 21 (h + uLen)) 22 (outAddr + 2)
                  pos := _pos2 }
                .normal st3 cSub ∧
              (NodupVertsAt st3.mem (h + uLen) V_list.length V ∧
               MemFrame mem2 st3.mem (h + uLen) (h + k) ∧
               (∀ j, j ≤ 22 → j ≠ 20 → st3.regs j =
                 (Function.update
                   (Function.update
                     (Function.update
                       (Function.update
                         (Function.update
                           (Function.update st.regs 17 k') 12 h2) 18 tag)
                         19 V_list.length) 21 (h + uLen)) 22 (outAddr + 2)) j) ∧
               st3.regs 20 = V_list.length) ∧
              cSub ≤ copyWordsCost V_list.length + 20 := by
            have hrun_sub : ∃ o st3 cSub,
                Runs w p ω
                  (.seq (.call 20 idx.copyWords [.reg 19, .reg 22, .reg 21])
                    (.assign 20 (.reg 19)))
                  { mem := mem2
                    regs := Function.update
                      (Function.update
                        (Function.update
                          (Function.update
                            (Function.update
                              (Function.update st.regs 17 k') 12 h2) 18 tag)
                            19 V_list.length) 21 (h + uLen)) 22 (outAddr + 2)
                    pos := _pos2 }
                  o st3 cSub ∧
                normalPost (fun st3 =>
                  NodupVertsAt st3.mem (h + uLen) V_list.length V ∧
                  MemFrame mem2 st3.mem (h + uLen) (h + k) ∧
                  (∀ j, j ≤ 22 → j ≠ 20 → st3.regs j =
                    (Function.update
                      (Function.update
                        (Function.update
                          (Function.update
                            (Function.update
                              (Function.update st.regs 17 k') 12 h2) 18 tag)
                            19 V_list.length) 21 (h + uLen)) 22 (outAddr + 2)) j) ∧
                  st3.regs 20 = V_list.length) o st3 ∧
                0 + cSub ≤ copyWordsCost V_list.length + 20 := by
              refine runs_seq_call_le (vs := [V_list.length, outAddr + 2, h + uLen]) hCopy
                (by simp [evalArgs, Expr.eval])
                (by intro v hv; simp at hv; rcases hv with rfl | rfl | rfl <;> omega)
                hCp_pre ?_
              intro _v3 mem3 _pos3 hpostCp
              simp only [copyWordsContract, List.getD_cons_zero, List.getD_cons_succ] at hpostCp
              rcases hpostCp with ⟨_, hcp_eq, hfr3⟩
              have hfr3' : MemFrame mem2 mem3 (h + uLen) (h + k) := fun a ha =>
                hfr3 a (by
                  have : h + uLen + V_list.length ≤ h + k := by omega
                  rcases ha with h1 | h2 <;> [exact Or.inl h1; exact Or.inr (by omega)])
              refine runs_assign_le (v := V_list.length) (by simp [Expr.eval]) ?_ ?_
              · refine ⟨nodupVertsAt_of_copyWords hV2at hcp_eq, hfr3',
                  fun j hj hne => by simp [hne], by simp⟩
              · have hargC : argsSize [.reg 19, .reg 22, .reg 21] = 3 := by decide
                simp only [copyWordsContract, Expr.size, hargC, List.getD_cons_zero]
                omega
            obtain ⟨o, st3, cSub, hrun3, hq3, hc3⟩ := hrun_sub
            cases o with
            | returned _ => exact False.elim hq3
            | normal => exact ⟨st3, cSub, hrun3, hq3, by omega⟩
          obtain ⟨st3, cSub, hrun3, ⟨hV3, hfr3', hregs3, hr20_3⟩, hcSub⟩ := hsub
          have hY_eq : V = smallerSide X' V := by
            have hadd : (X' \ V).card + V.card = X'.card := Finset.card_sdiff_add_card_eq_card hVX'
            simp [smallerSide, show V.card ≤ (X' \ V).card by omega]
          obtain ⟨o, stF, cF, hrunF, hqF, hcF⟩ := hfinish_Y V V_list.length st3.mem
            hY_eq hVcard.symm hV3 hfr3' st3 rfl
            (fun j hj hne => by rw [hregs3 j hj hne]) hr20_3
          refine ⟨o, stF, cSub + cF + 1,
            runs_seq_iff.mpr (Or.inr ⟨st3, cSub, cF, hrun3, hrunF, rfl⟩), hqF, ?_⟩
          have hargD1 : argsSize [.reg 2, .reg 3, .reg 13, .reg 10, .reg 5, .reg 11] = 6 := by decide
          have hargOS : argsSize [.reg 0, .reg 1, .reg 17, .reg 11, .reg 4, .reg 5, .reg 6,
            .reg 12] = 8 := by decide
          simp only [filterSetContract, oneShotContract, Expr.size, hargD1, hargOS,
            filterSetCost, copyWordsCost, List.getD_cons_zero, List.getD_cons_succ] at hcSub ⊢
          omega
    · -- Inactive: `r14 = 0 ∧ k ≤ 4 * uLen`, body is `.nop`
      intro hzero4
      have hk_le4u : k ≤ 4 * uLen := by by_contra hlt; simp [Nat.lt_of_not_ge hlt] at hzero4
      have hhCur_next : st.regs 12 ≤ h + 2 * k + (iter + 1) * Sone := by
        rw [Nat.add_one_mul iter Sone]; omega
      refine ⟨.normal, st, 1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
      · refine ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
          by simp [hr5], by simp [hr6], by simp [hr7], by simp [hr10], by simp [hr11],
          by simp [hr15], by simp, by simp; omega,
          by simp; exact hhCur_next, hZero, hloc, hframe₀,
          Or.inl ⟨by simp [hr14], U, hUat, hUX, hUcut, hUbal, ?_⟩⟩, hr16⟩
        have h1 : 2 * (coreParamsOf cfg M r).D q * X.card ≤
            8 * (coreParamsOf cfg M r).D q * U.card := by
          have hle : X.card ≤ 4 * U.card := by omega
          calc 2 * (coreParamsOf cfg M r).D q * X.card
              ≤ 2 * (coreParamsOf cfg M r).D q * (4 * U.card) := Nat.mul_le_mul_left _ hle
            _ = 8 * (coreParamsOf cfg M r).D q * U.card := by ring
        omega
      · simp only [Expr.size]; omega
  · -- Inactive: `r14 ≠ 0` (already found expander), body is `.nop`
    intro hzero14
    have hr14_ne : st.regs 14 ≠ 0 := by by_contra h0; simp [h0] at hzero14
    have hRcase : st.regs 14 = 1 ∧ ∃ R : Finset ℕ,
        CoreOutAt st.mem outAddr (.expander R) ∧ CoreSpec cp q G X (.expander R) := by
      rcases hdisj with ⟨h0, _⟩ | hR
      · exact absurd h0 hr14_ne
      · exact hR
    have hhCur_next : st.regs 12 ≤ h + 2 * k + (iter + 1) * Sone := by
      rw [Nat.add_one_mul iter Sone]; omega
    refine ⟨.normal, st, 1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
    · exact ⟨⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp [hr4],
        by simp [hr5], by simp [hr6], by simp [hr7], by simp [hr10], by simp [hr11],
        by simp [hr15], by simp, by simp; omega,
        by simp; exact hhCur_next, hZero, hloc, hframe₀,
        Or.inr ⟨by simp [hRcase.1], hRcase.2⟩⟩, hr16⟩
    · simp only [Expr.size]; omega

/-- Verified Hoare triple for the `2 * D_q`-iteration peeling loop `corePeelLoopStmt idx`. -/
theorem corePeelLoop_triple {w : ℕ} {p : Program} {idx : CoreIdx}
    {cfg : ParamConfig} {M r q K_B K_C S_B S_C : ℕ}
    (hDiff : MeetsContract w p idx.filterDiff (filterSetContract w false))
    (hCopy : MeetsContract w p idx.copyWords (copyWordsContract w))
    (hOneShot : MeetsContract w p idx.oneShot
      (oneShotContract cfg M r q w K_B K_C S_B S_C
        (coreProgTime K_B K_C cfg M r (q - 1)) (coreProgSpace S_B S_C cfg M r (q - 1))))
    {gAddr k xAddr pAddr locAddr outAddr h : ℕ} {G : Graph} {X : Finset ℕ} {mem₀ : ℕ → ℕ}
    (ha0 : 12 ≤ cfg.a₀) (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M) (hq1 : 1 ≤ q) (hqr : q ≤ r)
    (hP : CoreParamsAt mem₀ pAddr (coreParamsOf cfg M r) r)
    (hG : GraphAt mem₀ gAddr G) (hGvalid : G.IsValid)
    (hGn : G.n ≤ 2048 * LParam M * (NOf M r) ^ r)
    (hX : VertsAt mem₀ xAddr k X) (hXrange : X ⊆ Finset.range G.n)
    (hGloop : ∀ e ∈ G.inside X, e.1 ≠ e.2)
    (hkgt : (coreParamsOf cfg M r).N ^ (q - 1) < k)
    (hkNq : k ≤ (coreParamsOf cfg M r).N ^ q)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ (coreParamsOf cfg M r).Δ)
    (hmG : G.m ≤ (coreParamsOf cfg M r).Δ * k)
    (hg_h : gAddr + 2 + 2 * G.m ≤ h) (hx_h : xAddr + k ≤ h)
    (hp_h : pAddr + coreParamsSize r ≤ h) (hloc_h : locAddr + G.n ≤ h)
    (hout_h : outAddr + 2 + k ≤ h)
    (hd_lg : DisjointRange locAddr G.n gAddr (2 + 2 * G.m))
    (hd_lx : DisjointRange locAddr G.n xAddr k)
    (hd_lp : DisjointRange locAddr G.n pAddr (coreParamsSize r))
    (hd_lo : DisjointRange locAddr G.n outAddr (2 + k))
    (hd_og : DisjointRange outAddr (2 + k) gAddr (2 + 2 * G.m))
    (hd_ox : DisjointRange outAddr (2 + k) xAddr k)
    (hd_op : DisjointRange outAddr (2 + k) pAddr (coreParamsSize r))
    (hw : h + coreProgSpace S_B S_C cfg M r q < 2 ^ w)
    (P : State → Prop)
    (hP_init : ∀ st, P st →
      st.regs 0 = q ∧ st.regs 1 = gAddr ∧ st.regs 2 = k ∧ st.regs 3 = xAddr ∧
      st.regs 4 = pAddr ∧ st.regs 5 = locAddr ∧ st.regs 6 = outAddr ∧ st.regs 7 = h ∧
      st.regs 10 = h ∧ st.regs 11 = h + k ∧ st.regs 12 = h + 2 * k ∧
      st.regs 13 = 0 ∧ st.regs 14 = 0 ∧ st.regs 15 = 2 * DCore cfg M q ∧
      ZeroFrom st.mem (h + 2 * k) ∧
      (∀ u < G.n, st.mem (locAddr + u) = 0) ∧
      (∀ a < h, (a < outAddr ∨ outAddr + 2 + k ≤ a) → st.mem a = mem₀ a)) :
    Triple w p P (corePeelLoopStmt idx)
      (normalPost (CorePeelInv cfg M r q S_B S_C gAddr k xAddr pAddr locAddr outAddr h G X mem₀
        (2 * DCore cfg M q)))
      (fun _ =>
        2 * DCore cfg M q *
          (oneShotProgCost K_B K_C cfg M r q (coreProgTime K_B K_C cfg M r (q - 1)) +
            260 * k + 500) + 10) := by
  have hsp4000 : 4000 ≤ coreProgSpace S_B S_C cfg M r q :=
    coreProgSpace_base_ge S_B S_C cfg M r q
  have h2D_le : 2 * DCore cfg M q + 1 ≤ coreProgSpace S_B S_C cfg M r q :=
    two_mul_DCore_lt_coreProgSpace S_B S_C cfg M r q hq1
  have hw1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 16) (lo := .const 0) (hi := .reg 15)
    (body := corePeelBodyStmt idx) (P := P)
    (Inv := CorePeelInv cfg M r q S_B S_C gAddr k xAddr pAddr locAddr outAddr h G X mem₀)
    (oneShotProgCost K_B K_C cfg M r q (coreProgTime K_B K_C cfg M r (q - 1)) + 260 * k + 450)
    0 (2 * DCore cfg M q) (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hPst => by
      rcases hP_init st hPst with
        ⟨r0, r1, r2, r3, r4, r5, r6, r7, r10, r11, r12, r13, r14, r15, hZ, hloc, hfr⟩
      refine ⟨by simp [Expr.eval], by simp [r0], by simp [r1], by simp [r2], by simp [r3],
        by simp [r4], by simp [r5], by simp [r6], by simp [r7], by simp [r10], by simp [r11],
        by simp [r15], by simp, by simp [r12], by simp [r12], by simpa [r12] using hZ, hloc, hfr,
        Or.inl ⟨by simp [r14], ∅, ?_, Finset.empty_subset X,
          by simp [Graph.cutIn, Graph.inside], by simp; omega, ?_⟩⟩
      · simp only [Function.update_of_ne (by decide : (13 : ℕ) ≠ 16), r13]
        exact nodupVertsAt_iff_exists_listAt.mpr ⟨[], List.nodup_nil, rfl, rfl, listAt_nil _ _⟩
      · simp only [Finset.card_empty, mul_zero, zero_add, Nat.sub_zero]
        have h6 : 3 * (2 * (coreParamsOf cfg M r).D q) * X.card =
            6 * (coreParamsOf cfg M r).D q * X.card := by ring
        rw [h6]
        exact Nat.mul_le_mul_right X.card
          (Nat.mul_le_mul_right ((coreParamsOf cfg M r).D q) (by decide)))
    (fun _ st _ _ hInv => hInv.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hInv => by simp [Expr.eval, hInv.2.2.2.2.2.2.2.2.2.2.1])
    (fun iter _ hlt =>
      corePeelBody_runs hDiff hCopy hOneShot ha0 ha hrl hq1 hqr hP hG hGvalid hGn hX hXrange
        hGloop hkgt hkNq hdegG hmG hg_h hx_h hp_h hloc_h hout_h hd_lg hd_lx hd_lp hd_lo
        hd_og hd_ox hd_op hw iter hlt)
  refine hloop.mono_cost fun _ _ => ?_
  simp only [Nat.sub_zero, Expr.size]
  set C := oneShotProgCost K_B K_C cfg M r q (coreProgTime K_B K_C cfg M r (q - 1))
  have h1 : C + 260 * k + 450 + 1 + 8 ≤ C + 260 * k + 500 := by omega
  have h2 := Nat.mul_le_mul_left (2 * DCore cfg M q) h1
  linarith only [h2]

end MinCostFlow.ExpanderDecomp
