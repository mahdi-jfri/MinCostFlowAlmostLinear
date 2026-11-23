module

public import MinCostFlow.SparseCore.Program.LSFWindowProcBase
public import MinCostFlow.SparseCore.Program.LSFWindowSpec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import WordRAM.Tactic

/-!
# Host Canonical LSF Window Initializer Execution Theorems (`LSFWindowProc`)

Proves `lsfWindowInit_runs` (relocatable host execution of `lsfWindowProcs` on format-fitting
inputs, returning `(LSFRep h).rep` of the exact states `canonicalLSFInitWithH h ... j` with
pairwise-disjoint footprints in time `≤ lsfWindowCost`) and `lsfWindowInit_from_cited` (the
unconditional `h = 4` corollary using `cited_c_pos_of_lsst`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM WordRAM.Link MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
open MinCostFlow.DynSpanner.Program MinCostFlow.WideWord MinCostFlow.Num

/-! ## Main host execution theorem -/

private lemma canon_state_init_props {Q_AN : Program} {c_AN h L_in P_fp k_nat : ℕ}
    {K_AN : ℝ} {G₀ : MGraph} {ℓ₀ : ℕ → ℝ}
    (hV : CanonicalLSFValid Q_AN c_AN K_AN h L_in P_fp G₀ (safeLen G₀ ℓ₀) k_nat)
    {j : ℕ} (hj : j < k_nat) :
    let S := canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j
    S.G.V = S.T₀.V ∧ S.G.m ≤ G₀.E.card := by
  intro S
  have hSeq : S = (chosenGuestRun hV).S₀ j := canonicalLSFInitWithH_eq_chosen hV
  obtain ⟨hvp, hinit⟩ := (chosenGuestRun hV).hinit j hj
  have hTV : ((chosenGuestRun hV).T_raw j).V = G₀.V := by
    have h1 := hvp.hT_raw.1.2.1
    by_cases hne : G₀.E.Nonempty
    · simp only [hne, ↓reduceIte, weightedCopyGraph] at h1; exact h1
    · simp only [hne, ↓reduceIte] at h1; exact h1
  rw [hSeq, hinit]
  refine ⟨?_, le_rfl⟩
  unfold initLSFWith projectTree
  dsimp only
  split_ifs <;> exact hTV.symm

private lemma with_state {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {k T : ℕ} {Q : Outcome → State → Prop}
    (h : ∀ st₀, st₀ = st → ∃ o st' c, Runs w p ω s st₀ o st' c ∧ Q o st' ∧ k + c ≤ T) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k + c ≤ T := h st rfl

private lemma evalArgs_cons_eq {w : ℕ} {st : State} {e : Expr} {es : List Expr} {v : ℕ} {vs : List ℕ}
    (he : e.eval w st = some v) (hes : evalArgs w st es = some vs) :
    evalArgs w st (e :: es) = some (v :: vs) := by
  simp [evalArgs, he, hes]

private lemma eval_add_eq {w : ℕ} {st : State} {e1 e2 : Expr} {v1 v2 : ℕ}
    (h1 : e1.eval w st = some v1) (h2 : e2.eval w st = some v2) (hlt : v1 + v2 < 2 ^ w) :
    (Expr.bin .add e1 e2).eval w st = some (v1 + v2) := by
  simp [Expr.eval, BinOp.eval, h1, h2, hlt]

private lemma eval_mul_eq {w : ℕ} {st : State} {e1 e2 : Expr} {v1 v2 : ℕ}
    (h1 : e1.eval w st = some v1) (h2 : e2.eval w st = some v2) (hlt : v1 * v2 < 2 ^ w) :
    (Expr.bin .mul e1 e2).eval w st = some (v1 * v2) := by
  simp [Expr.eval, BinOp.eval, h1, h2, hlt]

private lemma lsfStaticSize_bounds (vCap eCap n0 L_w : ℕ) :
    vCap ≤ lsfStaticSize vCap eCap n0 n0 L_w ∧
    eCap ≤ lsfStaticSize vCap eCap n0 n0 L_w ∧
    eCap * L_w ≤ lsfStaticSize vCap eCap n0 n0 L_w := by
  unfold lsfStaticSize dynGraphSize; omega

set_option maxHeartbeats 400000 in
/-- Relocatable execution theorem for the canonical LSF window initializer (`lsfWindowProcs`):
on every input that fits the fixed-point format, entry `b + lsfWindowIdxInit` runs the canonical
guest `lemma55Module` in `[heap, heap + 2 ^ w')` and sparsely repacks all `k_nat` handles into
fresh zeroed host memory, yielding `(LSFRep h).rep` of the exact states
`canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j` with pairwise-disjoint footprints
in time `≤ lsfWindowCost Q_AN c_AN K_AN h L_in P_fp k_nat G₀.n G₀.m` (independent of `vCap_host`,
`eCap_host`, and `L_w_host`). -/
theorem lsfWindowInit_runs {w h q c_AN b g0Ptr lenArr L_in P_fp k_nat L_w_host
    vCap_host eCap_host handlesOut heap vCap0 eCap0 : ℕ}
    {p Q_AN : Program} {K_AN : ℝ} {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {mem : ℕ → ℕ}
    (pos : ℕ) (ω : ℕ → Bool)
    (hp : p.HasAt b (lsfWindowProcs Q_AN c_AN K_AN b h))
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hh : 1 ≤ h) (hLin1 : 1 ≤ L_in) (hdiv : h ∣ P_fp) (hP_Lin : P_fp + 6 ≤ h * L_in)
    (hk : 1 ≤ k_nat) (hq_P : q + 11 ≤ P_fp) (hk_q : 40 * k_nat ≤ 2 ^ q)
    (hm_Lin : 32 * (G₀.E.card + 1) * 2 ^ P_fp < 2 ^ (h * L_in - 1))
    (hLw_host : canonLw K_AN L_in G₀.n k_nat ≤ L_w_host)
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hvCap_le : vCap0 ≤ vCap_host) (heCap_le : eCap0 ≤ eCap_host) (heCap1 : 1 ≤ eCap_host)
    (hℓ₀_mem : ∀ e ∈ G₀.E, Valid mem (lenArr + e * L_in) h L_in ∧
      fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e)
    (hg0_le : g0Ptr + dynGraphSize vCap0 eCap0 ≤ heap)
    (hlen_le : lenArr + eCap0 * L_in ≤ heap)
    (hhnd_le : handlesOut + k_nat ≤ heap)
    (hheap1 : 1 ≤ heap)
    (hz : ZeroFrom mem heap)
    (hw_le : canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k_nat ≤ w)
    (hsp : heap + lsfWindowSpace Q_AN K_AN c_AN h L_in L_w_host P_fp k_nat
      vCap_host eCap_host G₀ < 2 ^ w) :
    ∃ body, p.procs[b + lsfWindowIdxInit]? = some body ∧
      ∃ (endHeap : ℕ) (st' : State) (c : ℕ) (x_h : ℕ → LSFConcrete) (hs : ℕ → ℕ),
        Runs w p ω body
          (startState [g0Ptr, lenArr, L_in, P_fp, k_nat, L_w_host, vCap_host, eCap_host,
            handlesOut, heap] mem pos)
          (.returned endHeap) st' c ∧
        heap ≤ endHeap ∧
        endHeap ≤ heap + lsfWindowSpace Q_AN K_AN c_AN h L_in L_w_host P_fp k_nat
          vCap_host eCap_host G₀ ∧
        ZeroFrom st'.mem endHeap ∧
        (∀ z < heap, (z < handlesOut ∨ handlesOut + k_nat ≤ z) → st'.mem z = mem z) ∧
        (∀ j < k_nat, st'.mem (handlesOut + j) = hs j ∧
          (LSFRep h).rep (hs j)
            (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j)
            (x_h j) st'.mem ∧
          (x_h j).vCap = vCap_host ∧ (x_h j).eCap = eCap_host ∧ (x_h j).L_w = L_w_host ∧
          (x_h j).n0 = G₀.n ∧ (x_h j).m0 = G₀.E.card ∧
          ∀ a, (LSFRep h).foot (hs j) (x_h j) a → heap ≤ a ∧ a < endHeap) ∧
        (∀ j₁ < k_nat, ∀ j₂ < k_nat, j₁ ≠ j₂ →
          ∀ a, (LSFRep h).foot (hs j₁) (x_h j₁) a → ¬ (LSFRep h).foot (hs j₂) (x_h j₂) a) ∧
        c ≤ lsfWindowCost Q_AN c_AN K_AN h L_in P_fp k_nat G₀.n G₀.m := by
  obtain ⟨hp0, hpCopy, hpFill, hpLog, hpSort, hpBuild, hpRep, hpReloc⟩ := hasAt_lsfWindow_split hp
  refine ⟨_, hp0, ?_⟩
  set w' := canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k_nat
  set R_Q := (lemma55Module Q_AN c_AN K_AN h).regBound
  set rhoConstLog := Nat.log 2 (lemma55RhoConst K_AN + 1)
  have hw'_h := (canonWordBits_bounds Q_AN c_AN K_AN h L_in P_fp G₀ k_nat).1
  have hB_lt := (canonWordBits_bounds Q_AN c_AN K_AN h L_in P_fp G₀ k_nat).2.1
  have hw_3h : 3 * h + 2 ≤ w := le_trans hw'_h hw_le
  have hw20 : 20 < 2 ^ w :=
    lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (by omega : 5 ≤ w))
  have hw16 : 16 ≤ 2 ^ w := by omega
  have hpow_le : 2 ^ w' ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw_le
  have hCopy : MeetsContract w p (b + 1) (memCopyContract w) :=
    memCopy_meetsContract (by omega) hpCopy
  have hFill : MeetsContract w p (b + 2) (memFillContract w) :=
    memFill_meetsContract (by omega) hpFill
  have hLog : MeetsContract w p (b + 3) log2Contract :=
    log2_meetsContract (by omega) hpLog
  -- Establish `CanonicalLSFValid` for `safeLen G₀ ℓ₀`
  have hV : CanonicalLSFValid Q_AN c_AN K_AN h L_in P_fp G₀ (safeLen G₀ ℓ₀) k_nat := by
    refine ⟨hQ, hh, hLin1, hdiv, hP_Lin, hk, ⟨q, hq_P, hk_q⟩, hm_Lin, hG₀, hV₀, fun e he => ?_⟩
    obtain ⟨hval, hfx, hpos⟩ := hℓ₀_mem e he
    refine ⟨fun i => mem (lenArr + e * L_in + i), ?_, ?_, ?_⟩
    · intro i hi; simpa using hval i hi
    · rw [safeLen_eq_of_mem ℓ₀ he, ← hfx]
      unfold fixVal intVal signedVal
      have huns : unsignedVal (fun i => mem (lenArr + e * L_in + i)) 0 h L_in =
          unsignedVal mem (lenArr + e * L_in) h L_in :=
        unsignedVal_congr fun i _ => by simp
      rw [huns]
    · rw [safeLen_eq_of_mem ℓ₀ he]; exact hpos
  set r := chosenGuestRun hV
  set L_w_g := canonLw K_AN L_in G₀.n k_nat
  set vCap_g := canonVCap G₀
  set eCap_g := canonECap G₀
  set sp_g := lsfWindowSpace Q_AN K_AN c_AN h L_in L_w_host P_fp k_nat vCap_host eCap_host G₀
  have hsp_guest_lt : canonHeap G₀ L_in k_nat +
      lemma55Space Q_AN K_AN c_AN h L_in L_w_g P_fp k_nat vCap_g eCap_g G₀.n G₀.m < 2 ^ w' :=
    lt_trans (Nat.lt_succ_of_le (le_max_left _ _)) hB_lt
  have hP_lt : P_fp < 2 ^ w' := by
    have : 2 * P_fp + 9 < 2 ^ w' :=
      lt_trans (Nat.lt_succ_of_le (le_trans (le_max_left _ _) (le_max_right _ _))) hB_lt
    omega
  have hLw_g_lt : L_w_g < 2 ^ w' := by
    have h1 : L_w_g ≤ lemma55Space Q_AN K_AN c_AN h L_in L_w_g P_fp k_nat vCap_g eCap_g G₀.n G₀.m := by
      unfold lemma55Space; dsimp only
      have ha : L_w_g ≤ 2 * L_w_g := by omega
      exact Nat.le_trans ha (Nat.le_trans (Nat.le_add_left _ _)
        (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))
    omega
  have hLin_lt : L_in < 2 ^ w' := lt_of_le_of_lt (canonLw_ge_Lin K_AN L_in G₀.n k_nat) hLw_g_lt
  have hdg_lt : dynGraphSize vCap_g eCap_g < 2 ^ w' := by
    have hdg_eq : dynGraphSize (canonVCap G₀) (canonECap G₀) = dynGraphSize vCap_g eCap_g := rfl
    unfold canonHeap canonHandlesOut canonLenArr at hsp_guest_lt; omega
  have hvCap_g_lt : vCap_g < 2 ^ w' := by unfold dynGraphSize at hdg_lt; omega
  have heCap_g_lt : eCap_g < 2 ^ w' := by unfold dynGraphSize at hdg_lt; omega
  have hn0_le_vCap_g : G₀.n ≤ vCap_g := by
    have hsub : G₀.V ⊆ Finset.range vCap_g := fun v hv => Finset.mem_range.mpr (canonVCap_gt hv)
    calc G₀.n = G₀.V.card := rfl
      _ ≤ (Finset.range vCap_g).card := Finset.card_le_card hsub
      _ = vCap_g := Finset.card_range vCap_g
  have hlen_lt : canonLenArr G₀ < 2 ^ w' := hdg_lt
  have hhnd_g_lt : canonHandlesOut G₀ L_in < 2 ^ w' := by unfold canonHeap at hsp_guest_lt; omega
  have hheap_g_lt : canonHeap G₀ L_in k_nat < 2 ^ w' := by omega
  have hk_lt : k_nat < 2 ^ w' := by unfold canonHeap at hsp_guest_lt; omega
  have hss_b := lsfStaticSize_bounds vCap_host eCap_host G₀.n L_w_host
  have hss_le_k : lsfStaticSize vCap_host eCap_host G₀.n G₀.n L_w_host ≤
      k_nat * lsfStaticSize vCap_host eCap_host G₀.n G₀.n L_w_host :=
    Nat.le_mul_of_pos_left _ hk
  have hsp_lt_k : heap + 2 ^ w' + k_nat * lsfStaticSize vCap_host eCap_host G₀.n G₀.n L_w_host < 2 ^ w := by
    have h1 : 2 ^ w' ≤ max (2 ^ w') (canonHandlesOut G₀ L_in + max G₀.n G₀.m + 1) := le_max_left _ _
    have h2 : heap + 2 ^ w' + k_nat * lsfStaticSize vCap_host eCap_host G₀.n G₀.n L_w_host ≤
        heap + (max (2 ^ w') (canonHandlesOut G₀ L_in + max G₀.n G₀.m + 1) +
        k_nat * lsfStaticSize vCap_host eCap_host G₀.n G₀.n L_w_host + 1) := by
      rw [Nat.add_assoc heap]
      exact Nat.add_le_add_left (le_trans (Nat.add_le_add_right h1 _) (Nat.le_add_right _ 1)) heap
    exact lt_of_le_of_lt h2 hsp
  have hss_lt_w : k_nat * lsfStaticSize vCap_host eCap_host G₀.n G₀.n L_w_host < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_add_left _ _) hsp_lt_k
  have hLwh_lt : L_w_host < 2 ^ w :=
    lt_of_le_of_lt (le_trans (Nat.le_mul_of_pos_left L_w_host heCap1)
      (le_trans hss_b.2.2 hss_le_k)) hss_lt_w
  have hvCap_h_lt : vCap_host < 2 ^ w :=
    lt_of_le_of_lt (le_trans hss_b.1 hss_le_k) hss_lt_w
  have heCap_h_lt : eCap_host < 2 ^ w :=
    lt_of_le_of_lt (le_trans hss_b.2.1 hss_le_k) hss_lt_w
  have hheap_w'_lt : heap + 2 ^ w' < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_add_right _ _) hsp_lt_k
  have hbuild_sp : heap + canonHandlesOut G₀ L_in + max G₀.n G₀.m < 2 ^ w := by
    have h1 : canonHandlesOut G₀ L_in + max G₀.n G₀.m + 1 ≤
        max (2 ^ w') (canonHandlesOut G₀ L_in + max G₀.n G₀.m + 1) := le_max_right _ _
    have h2 : canonHandlesOut G₀ L_in + max G₀.n G₀.m + 1 ≤
        max (2 ^ w') (canonHandlesOut G₀ L_in + max G₀.n G₀.m + 1) +
        k_nat * lsfStaticSize vCap_host eCap_host G₀.n G₀.n L_w_host + 1 :=
      le_trans h1 (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ 1))
    have h3 : heap + (canonHandlesOut G₀ L_in + max G₀.n G₀.m + 1) < 2 ^ w :=
      lt_of_le_of_lt (Nat.add_le_add_left h2 heap) hsp
    exact lt_of_le_of_lt (by rw [Nat.add_assoc]; exact Nat.le_add_right _ 1) h3
  -- Step 1: Run `buildCanonGuestProc`
  obtain ⟨bodyB, st1, c1, hpB, hrun1, hfr1, hcmem1, hz1, hc1⟩ :=
    buildCanonGuestProc_runs (p := p) (w := w) (h := h) (ω := ω) (pos := pos)
      (g0Ptr := g0Ptr) (vCap0 := vCap0) (eCap0 := eCap0) (lenArr := lenArr)
      (L_in := L_in) (P_fp := P_fp) (guestBase := heap) (G₀ := G₀) (ℓ₀ := ℓ₀)
      hw16 hLin1 hG₀ hV₀ hdg0 hℓ₀_mem hg0_le hlen_le hz hbuild_sp hpBuild hpSort hCopy hFill
  have hdg1_hdr : st1.mem (heap + dgVCapOff) = vCap_g ∧
      st1.mem (heap + dgECapOff) = eCap_g ∧ st1.mem (heap + dgNOff) = G₀.n := by
    have hdg_c := canonGuestMem_dynGraphAt hG₀ ℓ₀ h L_in P_fp
    refine ⟨(hcmem1 dgVCapOff).trans (by simpa using hdg_c.2.2.2.1),
      (hcmem1 dgECapOff).trans (by simpa using hdg_c.2.2.2.2.1),
      (hcmem1 dgNOff).trans (by simpa using hdg_c.2.2.2.2.2.1)⟩
  -- Step 5: Run `canonicalLSF_relocated_run` on `st1.mem`
  have hz1_above : ZeroFrom st1.mem (heap + 2 ^ w') := fun z hz_ge =>
    hz1 z (by omega)
  obtain ⟨bodyR, st2, c2, hpR, hrun2, hc2, hge2, hle2, hz2, hout2, hmem2, hmemW2, hrep2, _⟩ :=
    canonicalLSF_relocated_run (w := w) (h := h) (c_AN := c_AN) (bReloc := b + 20)
      (guestBase := heap) (L_in := L_in) (P_fp := P_fp) (k := k_nat)
      (p := p) (Q_AN := Q_AN) (K_AN := K_AN) (G₀ := G₀) (ℓ₀ := ℓ₀) (mem := st1.mem)
      st1.pos ω hV hpReloc hheap1 hw_le hheap_w'_lt.le (fun a _ => hcmem1 a) hz1_above
  have hrEnd_lt : r.endHeap < 2 ^ w' := lt_of_le_of_lt hle2 hsp_guest_lt
  -- Construct the deterministic host handle addresses and concrete records
  set hAddr := hostHandleAddr (heap + r.endHeap) vCap_host eCap_host G₀.n L_w_host
    (fun j => (r.x₀ j).tM)
  set x_h : ℕ → LSFConcrete := fun j =>
    { r.x₀ j with vCap := vCap_host, eCap := eCap_host, L_w := L_w_host }
  have hguest_ok : ∀ j < k_nat,
      st2.mem (heap + canonHandlesOut G₀ L_in + j) = r.hs j ∧
      (LSFRep h).rep (r.hs j)
        (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j)
        (r.x₀ j) (fun a => st2.mem (heap + a)) ∧
      (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j).G.V =
        (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j).T₀.V ∧
      (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j).G.m ≤ G₀.E.card ∧
      (r.x₀ j).vCap ≤ vCap_host ∧ (r.x₀ j).eCap ≤ eCap_host ∧ (r.x₀ j).L_w = L_w_g ∧
      L_w_g ≤ L_w_host ∧ (r.x₀ j).n0 = G₀.n ∧ (r.x₀ j).m0 = G₀.E.card ∧ (r.x₀ j).tM ≤ G₀.n ∧
      (r.x₀ j).endAddr (r.hs j) ≤ r.endHeap := by
    intro j hj
    obtain ⟨hhnd_j, hrep_j, hv_j, he_j, hlw_j, hn_j, hm_j, hfoot_j⟩ := hrep2 j hj
    obtain ⟨hGV, hGm⟩ := canon_state_init_props hV hj
    have hv_le : vCap_g ≤ vCap_host :=
      le_trans (canonVCap_le_of_dynGraphAt hdg0 hV₀) hvCap_le
    have he_le : eCap_g ≤ eCap_host := by
      unfold eCap_g canonECap
      refine max_le heCap1 ?_
      have hsup : G₀.E.sup id < eCap_host :=
        (Finset.sup_lt_iff heCap1).mpr fun e he => lt_of_lt_of_le (hdg0.2.2.1 e he) heCap_le
      omega
    have htM_le_n0 : (r.x₀ j).tM ≤ G₀.n := by
      rcases hrep_j with ⟨_, _, _, _, _, _, _, _, _, _, _, _, htM_le, _⟩
      exact le_trans htM_le (by rw [hn_j])
    have hend_le : (r.x₀ j).endAddr (r.hs j) ≤ r.endHeap := by
      have hlt_end : r.hs j < (r.x₀ j).endAddr (r.hs j) := by
        have := lsfHdr_lt_end (r.hs j) (r.x₀ j).vCap (r.x₀ j).eCap (r.x₀ j).n0 (r.x₀ j).tM (r.x₀ j).L_w
        dsimp only [LSFConcrete.endAddr]; unfold lsfHdrSize at this; omega
      have hlast : (LSFRep h).foot (r.hs j) (r.x₀ j) ((r.x₀ j).endAddr (r.hs j) - 1) :=
        ⟨by omega, by omega⟩
      have hft : (r.x₀ j).endAddr (r.hs j) - 1 < r.endHeap := (hfoot_j _ hlast).2
      omega
    exact ⟨hhnd_j, hrep_j, hGV, hGm, hv_j ▸ hv_le, he_j ▸ he_le, hlw_j, hLw_host,
      hn_j, hm_j, htM_le_n0, hend_le⟩
  have htM_fn_le : ∀ j < k_nat, (r.x₀ j).tM ≤ G₀.n := fun j hj =>
    (hguest_ok j hj).2.2.2.2.2.2.2.2.2.2.1
  have hend_sp_le : hAddr k_nat ≤ heap + sp_g := by
    have h1 := hostHandleAddr_le_mul (startDst := heap + r.endHeap) (vCap_h := vCap_host)
      (eCap_h := eCap_host) (L_w_h := L_w_host) htM_fn_le k_nat le_rfl
    have h2 : r.endHeap ≤ max (2 ^ w') (canonHandlesOut G₀ L_in + max G₀.n G₀.m + 1) :=
      le_trans hrEnd_lt.le (le_max_left _ _)
    have h3 : heap + r.endHeap + k_nat * lsfStaticSize vCap_host eCap_host G₀.n G₀.n L_w_host ≤
        heap + (max (2 ^ w') (canonHandlesOut G₀ L_in + max G₀.n G₀.m + 1) +
        k_nat * lsfStaticSize vCap_host eCap_host G₀.n G₀.n L_w_host + 1) := by
      rw [Nat.add_assoc heap]
      exact Nat.add_le_add_left (le_trans (Nat.add_le_add_right h2 _) (Nat.le_add_right _ 1)) heap
    exact le_trans h1 h3
  -- Prove the top-level run via `_flat` stepping
  suffices hmain : ∃ o st' c,
      Runs w p ω
        (lsfWindowInitProc (b + 13) (b + 20) (b + 3) (b + 20) R_Q rhoConstLog)
        (startState [g0Ptr, lenArr, L_in, P_fp, k_nat, L_w_host, vCap_host, eCap_host,
          handlesOut, heap] mem pos) o st' c ∧
      (o = .returned (hAddr k_nat) ∧
        ZeroFrom st'.mem (hAddr k_nat) ∧
        (∀ z < heap, (z < handlesOut ∨ handlesOut + k_nat ≤ z) → st'.mem z = mem z) ∧
        (∀ j < k_nat, st'.mem (handlesOut + j) = hAddr j ∧
          (LSFRep h).rep (hAddr j)
            (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j)
            (x_h j) st'.mem)) ∧
      c ≤ lsfWindowCost Q_AN c_AN K_AN h L_in P_fp k_nat G₀.n G₀.m by
    rcases hmain with ⟨_, st', c, hrun, ⟨rfl, hz', hfr', hrep'⟩, hc⟩
    refine ⟨hAddr k_nat, st', c, x_h, hAddr, hrun,
      le_trans (Nat.le_add_right _ _) (hostHandleAddr_mono (Nat.zero_le k_nat)),
      hend_sp_le, hz', hfr', ?_, ?_, hc⟩
    · intro j hj
      obtain ⟨hhnd_j, hrep_j⟩ := hrep' j hj
      refine ⟨hhnd_j, hrep_j, rfl, rfl, rfl,
        (hguest_ok j hj).2.2.2.2.2.2.2.2.1, (hguest_ok j hj).2.2.2.2.2.2.2.2.2.1, fun a ha => ?_⟩
      have hfoot_ge : heap ≤ hAddr j :=
        le_trans (Nat.le_add_right _ _) (hostHandleAddr_mono (Nat.zero_le j))
      have hfoot_end : (x_h j).endAddr (hAddr j) = hAddr (j + 1) := by
        dsimp only [LSFConcrete.endAddr, x_h, hAddr, hostHandleAddr, lsfEndAddr]
        rw [(hguest_ok j hj).2.2.2.2.2.2.2.2.1]
      have ha2 : a < hAddr (j + 1) := by rw [← hfoot_end]; exact ha.2
      exact ⟨le_trans hfoot_ge ha.1, lt_of_lt_of_le ha2 (hostHandleAddr_mono hj)⟩
    · intro j₁ hj₁ j₂ hj₂ hne a ha₁ ha₂
      have hend_eq : ∀ j < k_nat, (x_h j).endAddr (hAddr j) = hAddr (j + 1) := fun j hj => by
        dsimp only [LSFConcrete.endAddr, x_h, hAddr, hostHandleAddr, lsfEndAddr]
        rw [(hguest_ok j hj).2.2.2.2.2.2.2.2.1]
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · have h1a : a < hAddr (j₁ + 1) := by rw [← hend_eq j₁ hj₁]; exact ha₁.2
        have h1 := lt_of_lt_of_le h1a (hostHandleAddr_mono hlt)
        exact absurd (lt_of_lt_of_le h1 ha₂.1) (lt_irrefl _)
      · have h2a : a < hAddr (j₂ + 1) := by rw [← hend_eq j₂ hj₂]; exact ha₂.2
        have h2 := lt_of_lt_of_le h2a (hostHandleAddr_mono hgt)
        exact absurd (lt_of_lt_of_le h2 ha₁.1) (lt_irrefl _)
  refine runs_start_le ?_
  unfold lsfWindowInitProc startState
  -- Step 1: call `buildCanonGuestProc` at `b + 13`
  refine runs_seq_call_body_flat (show p.procs[b + 13]? = some bodyB by simpa using hpB)
    (vs := [g0Ptr, lenArr, L_in, heap]) (P_call := fun _ st => st = st1)
    (c1_max := buildCanonGuestCost G₀.n G₀.m L_in)
    (by simp only [evalArgs, Expr.eval, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some])
    ⟨0, st1, c1, hrun1, rfl, hc1⟩
    (fun _ st1' hst1 => ?_)
  subst st1'
  -- Step 2: load `vCap_g`, `eCap_g`, `G₀.n`
  refine runs_seq_assign_flat (v := vCap_g)
    (Expr.eval_load_of_eq (x := heap + 0) (by
      simp only [Expr.eval, BinOp.eval, dgVCapOff, Function.update_of_ne, ne_eq, Nat.reduceEqDiff,
        not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, show 0 < 2 ^ w by omega,
        show heap + 0 < 2 ^ w by omega, ↓reduceIte])
      (by simpa [dgVCapOff] using hdg1_hdr.1)) ?_
  refine runs_seq_assign_flat (v := eCap_g)
    (Expr.eval_load_of_eq (x := heap + 1) (by
      simp only [Expr.eval, BinOp.eval, dgECapOff, Function.update_of_ne, ne_eq, Nat.reduceEqDiff,
        not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, show 1 < 2 ^ w by omega,
        show heap + 1 < 2 ^ w by omega, ↓reduceIte])
      (by simpa [dgECapOff] using hdg1_hdr.2.1)) ?_
  refine runs_seq_assign_flat (v := G₀.n)
    (Expr.eval_load_of_eq (x := heap + 2) (by
      simp only [Expr.eval, BinOp.eval, dgNOff, Function.update_of_ne, ne_eq, Nat.reduceEqDiff,
        not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, show 2 < 2 ^ w by omega,
        show heap + 2 < 2 ^ w by omega, ↓reduceIte])
      (by simpa [dgNOff] using hdg1_hdr.2.2)) ?_
  -- Step 3: compute `canonLenArr`, `canonHandlesOut`, `canonHeap`
  refine runs_seq_assign_flat (v := canonLenArr G₀) (by
    have hsz : canonLenArr G₀ = 4 + 7 * vCap_g + 9 * eCap_g := rfl
    have h1 : 7 * vCap_g < 2 ^ w := by unfold dynGraphSize at hdg_lt; omega
    have h2 : 4 + 7 * vCap_g < 2 ^ w := by unfold dynGraphSize at hdg_lt; omega
    have h3 : 9 * eCap_g < 2 ^ w := by unfold dynGraphSize at hdg_lt; omega
    have h4 : 4 + 7 * vCap_g + 9 * eCap_g < 2 ^ w := by rw [← hsz]; omega
    rw [hsz]; simp only [Expr.eval, BinOp.eval, Function.update_self, Function.update_of_ne,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
      show 9 < 2 ^ w by omega, h1, h2, h3, h4, ↓reduceIte]) ?_
  refine runs_seq_assign_flat (v := canonHandlesOut G₀ L_in) (by
    have hh : canonHandlesOut G₀ L_in = canonLenArr G₀ + eCap_g * L_in := rfl
    have h1 : eCap_g * L_in < 2 ^ w := by omega
    have h2 : canonLenArr G₀ + eCap_g * L_in < 2 ^ w := by rw [← hh]; omega
    rw [hh]; simp only [Expr.eval, BinOp.eval, Function.update_self, Function.update_of_ne,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, h1, h2, ↓reduceIte]) ?_
  refine runs_seq_assign_flat (v := canonHeap G₀ L_in k_nat) (by
    have hh : canonHeap G₀ L_in k_nat = canonHandlesOut G₀ L_in + k_nat := rfl
    have h1 : canonHandlesOut G₀ L_in + k_nat < 2 ^ w := by rw [← hh]; omega
    rw [hh]; simp only [Expr.eval, BinOp.eval, Function.update_self, Function.update_of_ne,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, h1, ↓reduceIte]) ?_
  -- Step 4: compute `canonLw K_AN L_in G₀.n k_nat`
  refine runs_seq_call_flat hLog (vs := [k_nat + 1])
    (by simp only [evalArgs, Expr.eval, BinOp.eval, Function.update_of_ne,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, show 1 < 2 ^ w by omega,
      show k_nat + 1 < 2 ^ w by omega, ↓reduceIte])
    (by intro v hv; simp at hv; subst hv; omega)
    ⟨k_nat + 1, rfl, by omega⟩
    (fun retK memK posK hpK => ?_)
  rcases hpK with ⟨_, hargK, hmemK, hretK⟩; cases hargK; subst hretK; subst memK
  have hn0_add4_lt : G₀.n + 4 < 2 ^ w := by unfold dynGraphSize at hdg_lt; omega
  refine runs_seq_call_flat hLog (vs := [G₀.n + 2])
    (by simp only [evalArgs, Expr.eval, BinOp.eval, Function.update_self, Function.update_of_ne,
      ne_eq, Nat.reduceEqDiff, not_false_eq_true, show 2 < 2 ^ w by omega,
      show G₀.n + 2 < 2 ^ w by omega, ↓reduceIte])
    (by intro v hv; simp at hv; subst hv; omega)
    ⟨G₀.n + 2, rfl, by omega⟩
    (fun retN memN posN hpN => ?_)
  rcases hpN with ⟨_, hargN, hmemN, hretN⟩; cases hargN; subst hretN; subst memN
  have hlogn_le_n : Nat.log 2 (G₀.n + 2) ≤ G₀.n + 2 := (Nat.log_lt_self 2 (by omega)).le
  refine runs_seq_call_flat hLog (vs := [Nat.log 2 (G₀.n + 2) + 2])
    (by simp only [evalArgs, Expr.eval, BinOp.eval, Function.update_self,
      show 2 < 2 ^ w by omega, show Nat.log 2 (G₀.n + 2) + 2 < 2 ^ w by omega, ↓reduceIte])
    (by intro v hv; simp at hv; subst hv; omega)
    ⟨Nat.log 2 (G₀.n + 2) + 2, rfl, by omega⟩
    (fun retLL memLL posLL hpLL => ?_)
  rcases hpLL with ⟨_, hargLL, hmemLL, hretLL⟩; cases hargLL; subst hretLL; subst memLL
  refine runs_seq_assign_flat (v := L_w_g) (by
    have hdef : L_w_g = L_in + rhoConstLog + Nat.log 2 (k_nat + 1) +
        6 * Nat.log 2 (Nat.log 2 (G₀.n + 2) + 2) + 8 := rfl
    have hLwg_w : L_w_g < 2 ^ w := lt_of_lt_of_le hLw_g_lt hpow_le
    rw [hdef]
    refine eval_add_eq (eval_add_eq (eval_add_eq (eval_add_eq ?_ ?_ (by omega)) ?_ (by omega))
      (eval_mul_eq ?_ ?_ (by omega)) (by omega)) ?_ (by omega)
    · simp only [Expr.eval, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    · simp only [Expr.eval, show rhoConstLog < 2 ^ w by omega, ↓reduceIte]
    · simp only [Expr.eval, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        Function.update_self]
    · simp only [Expr.eval, show 6 < 2 ^ w by omega, ↓reduceIte]
    · simp only [Expr.eval, Function.update_self]
    · simp only [Expr.eval, show 8 < 2 ^ w by omega, ↓reduceIte]) ?_
  -- Step 5: call relocated `lemma55Module` at `b + 20 + 1` (invoked at `posLL`)
  obtain ⟨bodyR_p, st2_p, c2_p, hpR_p, hrun2_p, hc2_p, _, _, hz2_p, hout2_p, _, hmemW2_p, hrep2_p, _⟩ :=
    canonicalLSF_relocated_run (w := w) (h := h) (c_AN := c_AN) (bReloc := b + 20)
      (guestBase := heap) (L_in := L_in) (P_fp := P_fp) (k := k_nat)
      (p := p) (Q_AN := Q_AN) (K_AN := K_AN) (G₀ := G₀) (ℓ₀ := ℓ₀) (mem := st1.mem)
      posLL ω hV hpReloc hheap1 hw_le hheap_w'_lt.le (fun a _ => hcmem1 a) hz1_above
  have hguest_ok_p : ∀ j < k_nat,
      st2_p.mem (heap + canonHandlesOut G₀ L_in + j) = r.hs j ∧
      (LSFRep h).rep (r.hs j)
        (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j)
        (r.x₀ j) (fun a => st2_p.mem (heap + a)) ∧
      (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j).G.V =
        (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j).T₀.V ∧
      (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j).G.m ≤ G₀.E.card ∧
      (r.x₀ j).vCap ≤ vCap_host ∧ (r.x₀ j).eCap ≤ eCap_host ∧ (r.x₀ j).L_w = L_w_g ∧
      L_w_g ≤ L_w_host ∧ (r.x₀ j).n0 = G₀.n ∧ (r.x₀ j).m0 = G₀.E.card ∧ (r.x₀ j).tM ≤ G₀.n ∧
      (r.x₀ j).endAddr (r.hs j) ≤ r.endHeap := fun j hj => by
    obtain ⟨hhnd_j, hrep_j, _, _, _, _, _, _⟩ := hrep2_p j hj
    obtain ⟨_, _, hGV, hGm, hv_le, he_le, hlw, hLw, hn, hm, htM, hend⟩ := hguest_ok j hj
    exact ⟨hhnd_j, hrep_j, hGV, hGm, hv_le, he_le, hlw, hLw, hn, hm, htM, hend⟩
  refine runs_seq_call_body_flat (show p.procs[b + 20 + 1]? = some bodyR_p by exact hpR_p)
    (vs := canonGuestArgs K_AN L_in P_fp G₀ k_nat ++ List.replicate (R_Q - 10) 0 ++ [heap, 0])
    (P_call := fun ret st => ret = r.endHeap ∧ st = st2_p)
    (c1_max := (R_Q + 6) * lemma55Cost Q_AN c_AN K_AN h L_in L_w_g P_fp k_nat G₀.n G₀.m)
    (by apply evalArgs_append
        · apply evalArgs_append
          · unfold canonGuestArgs
            refine evalArgs_cons_eq (by simp only [Expr.eval, show 0 < 2 ^ w by omega, ↓reduceIte]) ?_
            refine evalArgs_cons_eq (by simp only [Expr.eval, Function.update_self, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true]) ?_
            refine evalArgs_cons_eq (by simp only [Expr.eval, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]) ?_
            refine evalArgs_cons_eq (by simp only [Expr.eval, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]) ?_
            refine evalArgs_cons_eq (by simp only [Expr.eval, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]) ?_
            refine evalArgs_cons_eq (by simp only [Expr.eval, Function.update_self, L_w_g]) ?_
            refine evalArgs_cons_eq (by simp only [Expr.eval, Function.update_self, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true, vCap_g]) ?_
            refine evalArgs_cons_eq (by simp only [Expr.eval, Function.update_self, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true, eCap_g]) ?_
            refine evalArgs_cons_eq (by simp only [Expr.eval, Function.update_self, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true]) ?_
            refine evalArgs_cons_eq (by simp only [Expr.eval, Function.update_self, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true]) rfl
          · exact evalArgs_replicate_const_zero (by omega) _
        · refine evalArgs_cons_eq (by simp only [Expr.eval, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]) ?_
          refine evalArgs_cons_eq (by simp only [Expr.eval, show 0 < 2 ^ w by omega, ↓reduceIte]) rfl)
    ⟨r.endHeap, st2_p, c2_p, hrun2_p, ⟨rfl, rfl⟩, hc2_p⟩
    (fun ret2 st2' ⟨hret2, hst2⟩ => ?_)
  subst ret2; subst st2'
  -- Step 6: set up `curDst := heap + r.endHeap`, `guestHndBase := heap + canonHandlesOut`, and repack
  refine runs_seq_assign_flat (v := heap + r.endHeap) (by
    simp only [Expr.eval, BinOp.eval, Function.update_self, Function.update_of_ne, ne_eq, Nat.reduceEqDiff,
      not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, show heap + r.endHeap < 2 ^ w by omega,
      ↓reduceIte]) ?_
  refine runs_seq_assign_flat (v := heap + canonHandlesOut G₀ L_in) (by
    simp only [Expr.eval, BinOp.eval, Function.update_self, Function.update_of_ne, ne_eq, Nat.reduceEqDiff,
      not_false_eq_true, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, show heap + canonHandlesOut G₀ L_in < 2 ^ w by omega,
      ↓reduceIte]) ?_
  have hrep_loop := lsfWindow_repackLoop hw20 hpRep hCopy hLog (by omega) hhnd_le
    (Nat.le_add_right _ _) (by have : canonHandlesOut G₀ L_in + k_nat ≤ r.endHeap := hge2; omega) hLwh_lt
    (lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_left hrEnd_lt.le heap) _) hsp_lt_k)
    hz2_p (fun a ha1 ha2 => by
      have hsub : a - heap < 2 ^ w' := by omega
      have h1 := hmemW2_p (a - heap) hsub
      rw [show heap + (a - heap) = a by omega] at h1
      exact lt_of_lt_of_le h1 hpow_le)
    hguest_ok_p
  rw [show b + 14 + 6 = b + 20 by omega] at hrep_loop
  refine with_state fun st_cur hst_cur => ?_
  obtain ⟨o3, st3, c3, hrun3, hq3, hc3⟩ := hrep_loop st_cur ω
    ⟨by simp only [hst_cur, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
          List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some],
     by simp only [hst_cur, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
          List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some],
     by simp only [hst_cur, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
          List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some],
     by simp only [hst_cur, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
          List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some],
     by simp only [hst_cur, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
          List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some],
     by simp only [hst_cur, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
          List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some],
     by simp only [hst_cur, Function.update_self, Function.update_of_ne, ne_eq, Nat.reduceEqDiff, not_false_eq_true],
     by simp only [hst_cur, Function.update_self],
     by simp only [hst_cur]⟩
  cases o3 with
  | returned _ => exact False.elim hq3
  | normal =>
    rcases hq3 with ⟨hr19_3, hz3, hlo3, hrep3⟩
    have hret3 : Runs w p ω (.ret (.reg 19)) st3 (.returned (hAddr k_nat)) st3 2 :=
      runs_ret_iff.mpr ⟨hAddr k_nat, by simp [Expr.eval, hr19_3, hAddr], rfl, rfl, rfl⟩
    refine ⟨.returned (hAddr k_nat), st3, c3 + 2 + 1,
      runs_seq_iff.mpr (Or.inr ⟨st3, c3, 2, hrun3, hret3, rfl⟩),
      ⟨rfl, hz3, fun z hz_lt hne =>
        (hlo3 z hz_lt hne).trans ((hout2_p z (Or.inl hz_lt)).trans (hfr1 z hz_lt)),
        hrep3⟩, ?_⟩
    have hsz_args : argsSize ([.const 0, .reg 13, .reg 2, .reg 3, .reg 4, .reg 16, .reg 10, .reg 11,
        .reg 14, .reg 15] ++ List.replicate (R_Q - 10) (.const 0) ++ [.reg 9, .const 0]) =
        10 + (R_Q - 10) + 2 := by
      rw [argsSize_append, argsSize_append, argsSize_replicate_const_zero]
      simp [argsSize, Expr.size]
    have hlogLL_le : Nat.log 2 (Nat.log 2 (G₀.n + 2) + 2) ≤ Nat.log 2 (G₀.n + 2) + 1 := by
      have := Nat.log_lt_self 2 (by omega : Nat.log 2 (G₀.n + 2) + 2 ≠ 0); omega
    have htot := lsfWindow_total_cost_le (Q_AN := Q_AN) (c_AN := c_AN) (K_AN := K_AN)
      (L_in := L_in) (P_fp := P_fp) (n0 := G₀.n) (m0 := G₀.m) hh hk
    change buildCanonGuestCost G₀.n G₀.m L_in +
        (R_Q + 6) * lemma55Cost Q_AN c_AN K_AN h L_in L_w_g P_fp k_nat G₀.n G₀.m +
        k_nat * (repackOneLSFCost G₀.n G₀.m L_w_g + 120) +
        (2 * R_Q + 40 * Nat.log 2 (k_nat + 1) + 40 * Nat.log 2 (G₀.n + 2) + 400) ≤
      lsfWindowCost Q_AN c_AN K_AN h L_in P_fp k_nat G₀.n G₀.m at htot
    have hc3' : c3 ≤ k_nat * (repackOneLSFCost G₀.n G₀.m L_w_g + 60) + 10 := hc3
    simp only [hsz_args, log2Contract, argsSize, Expr.size, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, Option.getD_some]
    have hmul_rep : k_nat * (repackOneLSFCost G₀.n G₀.m L_w_g + 60) ≤
        k_nat * (repackOneLSFCost G₀.n G₀.m L_w_g + 120) :=
      Nat.mul_le_mul_left k_nat (by omega)
    have hR_sub : 10 + (R_Q - 10) + 2 ≤ 2 * R_Q + 12 := by omega
    linarith only [hc3', htot, hmul_rep, hR_sub, hlogLL_le]

/-- End-to-end unconditional Word-RAM realization of the canonical LSF window initializer at `h = 4`,
using the verified low-stretch spanning tree program (`cited_c_pos_of_lsst`). -/
theorem lsfWindowInit_from_cited :
    ∃ (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ),
      1 ≤ c_AN ∧
      (lsfWindowModule Q_AN c_AN K_AN 4).IsDeterministic ∧
      (∀ (w q g0Ptr lenArr L_in P_fp k_nat L_w_host vCap_host eCap_host handlesOut heap
          vCap0 eCap0 : ℕ) (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
        1 ≤ L_in → 4 ∣ P_fp → P_fp + 6 ≤ 4 * L_in →
        1 ≤ k_nat → q + 11 ≤ P_fp → 40 * k_nat ≤ 2 ^ q →
        32 * (G₀.E.card + 1) * 2 ^ P_fp < 2 ^ (4 * L_in - 1) →
        canonLw K_AN L_in G₀.n k_nat ≤ L_w_host →
        G₀.IsValid → G₀.V.Nonempty →
        DynGraphAt mem g0Ptr vCap0 eCap0 G₀ →
        vCap0 ≤ vCap_host → eCap0 ≤ eCap_host → 1 ≤ eCap_host →
        (∀ e ∈ G₀.E, Valid mem (lenArr + e * L_in) 4 L_in ∧
          fixVal mem (lenArr + e * L_in) 4 L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e) →
        g0Ptr + dynGraphSize vCap0 eCap0 ≤ heap →
        lenArr + eCap0 * L_in ≤ heap →
        handlesOut + k_nat ≤ heap →
        1 ≤ heap →
        ZeroFrom mem heap →
        canonWordBits Q_AN c_AN K_AN 4 L_in P_fp G₀ k_nat ≤ w →
        heap + lsfWindowSpace Q_AN K_AN c_AN 4 L_in L_w_host P_fp k_nat
          vCap_host eCap_host G₀ < 2 ^ w →
        ∃ body, (lsfWindowModule Q_AN c_AN K_AN 4).procs[lsfWindowIdxInit]? = some body ∧
          ∃ (endHeap : ℕ) (st' : State) (c : ℕ) (x_h : ℕ → LSFConcrete) (hs : ℕ → ℕ),
            Runs w (lsfWindowModule Q_AN c_AN K_AN 4) ω body
              (startState [g0Ptr, lenArr, L_in, P_fp, k_nat, L_w_host, vCap_host, eCap_host,
                handlesOut, heap] mem pos)
              (.returned endHeap) st' c ∧
            heap ≤ endHeap ∧
            endHeap ≤ heap + lsfWindowSpace Q_AN K_AN c_AN 4 L_in L_w_host P_fp k_nat
              vCap_host eCap_host G₀ ∧
            ZeroFrom st'.mem endHeap ∧
            (∀ z < heap, (z < handlesOut ∨ handlesOut + k_nat ≤ z) → st'.mem z = mem z) ∧
            (∀ j < k_nat, st'.mem (handlesOut + j) = hs j ∧
              (LSFRep 4).rep (hs j)
                (canonicalLSFInit Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k_nat j)
                (x_h j) st'.mem ∧
              (x_h j).vCap = vCap_host ∧ (x_h j).eCap = eCap_host ∧ (x_h j).L_w = L_w_host ∧
              (x_h j).n0 = G₀.n ∧ (x_h j).m0 = G₀.E.card ∧
              ∀ a, (LSFRep 4).foot (hs j) (x_h j) a → heap ≤ a ∧ a < endHeap) ∧
            (∀ j₁ < k_nat, ∀ j₂ < k_nat, j₁ ≠ j₂ →
              ∀ a, (LSFRep 4).foot (hs j₁) (x_h j₁) a → ¬ (LSFRep 4).foot (hs j₂) (x_h j₂) a) ∧
            c ≤ lsfWindowCost Q_AN c_AN K_AN 4 L_in P_fp k_nat G₀.n G₀.m) := by
  obtain ⟨Q_AN, c_AN, K_AN, hc_pos, hQ⟩ := cited_c_pos_of_lsst
  have hp0 : (lsfWindowModule Q_AN c_AN K_AN 4).HasAt 0 (lsfWindowProcs Q_AN c_AN K_AN 0 4) := by
    intro i hi; simp [lsfWindowModule, hi]
  refine ⟨Q_AN, c_AN, K_AN, hc_pos, lsfWindowModule_isDeterministic Q_AN c_AN K_AN 4, ?_⟩
  intro w q g0Ptr lenArr L_in P_fp k_nat L_w_host vCap_host eCap_host handlesOut heap vCap0 eCap0
    G₀ ℓ₀ mem pos ω hLin1 hdiv hP_Lin hk hq_P hk_q hm_Lin hLw_host hG₀ hV₀ hdg0 hvCap_le heCap_le
    heCap1 hℓ₀_mem hg0_le hlen_le hhnd_le hheap1 hz hw_le hsp
  exact lsfWindowInit_runs pos ω hp0 ⟨hc_pos, hQ⟩ (by decide) hLin1 hdiv hP_Lin hk hq_P hk_q hm_Lin
    hLw_host hG₀ hV₀ hdg0 hvCap_le heCap_le heCap1 hℓ₀_mem hg0_le hlen_le hhnd_le hheap1 hz hw_le hsp

/-- Relocatable host execution theorem for `canonicalLSFInitAuto` (`h = 4`,
`L_in = autoLimbCount G₀ ℓ₀ P_fp`): automatically discharges the limb-count capacity inequalities
from `autoLimbCount_spec` and returns `(LSFRep 4).rep` of `canonicalLSFInitAuto Q_AN c_AN K_AN P_fp
G₀ ℓ₀ k_nat j` for all `j < k_nat`. -/
theorem lsfWindowInit_runs_auto {w q c_AN b g0Ptr lenArr P_fp k_nat L_w_host
    vCap_host eCap_host handlesOut heap vCap0 eCap0 : ℕ}
    {p Q_AN : Program} {K_AN : ℝ} {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {mem : ℕ → ℕ}
    (pos : ℕ) (ω : ℕ → Bool)
    (hp : p.HasAt b (lsfWindowProcs Q_AN c_AN K_AN b 4))
    (hQ : FullAN19Spec Q_AN c_AN K_AN)
    (hdiv : 4 ∣ P_fp)
    (hk : 1 ≤ k_nat) (hq_P : q + 11 ≤ P_fp) (hk_q : 40 * k_nat ≤ 2 ^ q)
    (hLw_host : canonLw K_AN (autoLimbCount G₀ ℓ₀ P_fp) G₀.n k_nat ≤ L_w_host)
    (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hvCap_le : vCap0 ≤ vCap_host) (heCap_le : eCap0 ≤ eCap_host) (heCap1 : 1 ≤ eCap_host)
    (hℓ₀_mem : ∀ e ∈ G₀.E, Valid mem (lenArr + e * autoLimbCount G₀ ℓ₀ P_fp) 4
        (autoLimbCount G₀ ℓ₀ P_fp) ∧
      fixVal mem (lenArr + e * autoLimbCount G₀ ℓ₀ P_fp) 4 (autoLimbCount G₀ ℓ₀ P_fp) P_fp =
        ℓ₀ e ∧ 0 < ℓ₀ e)
    (hg0_le : g0Ptr + dynGraphSize vCap0 eCap0 ≤ heap)
    (hlen_le : lenArr + eCap0 * autoLimbCount G₀ ℓ₀ P_fp ≤ heap)
    (hhnd_le : handlesOut + k_nat ≤ heap)
    (hheap1 : 1 ≤ heap)
    (hz : ZeroFrom mem heap)
    (hw_le : canonWordBits Q_AN c_AN K_AN 4 (autoLimbCount G₀ ℓ₀ P_fp) P_fp G₀ k_nat ≤ w)
    (hsp : heap + lsfWindowSpace Q_AN K_AN c_AN 4 (autoLimbCount G₀ ℓ₀ P_fp) L_w_host P_fp k_nat
      vCap_host eCap_host G₀ < 2 ^ w) :
    let L_in := autoLimbCount G₀ ℓ₀ P_fp
    ∃ body, p.procs[b + lsfWindowIdxInit]? = some body ∧
      ∃ (endHeap : ℕ) (st' : State) (c : ℕ) (x_h : ℕ → LSFConcrete) (hs : ℕ → ℕ),
        Runs w p ω body
          (startState [g0Ptr, lenArr, L_in, P_fp, k_nat, L_w_host, vCap_host, eCap_host,
            handlesOut, heap] mem pos)
          (.returned endHeap) st' c ∧
        heap ≤ endHeap ∧
        endHeap ≤ heap + lsfWindowSpace Q_AN K_AN c_AN 4 L_in L_w_host P_fp k_nat
          vCap_host eCap_host G₀ ∧
        ZeroFrom st'.mem endHeap ∧
        (∀ z < heap, (z < handlesOut ∨ handlesOut + k_nat ≤ z) → st'.mem z = mem z) ∧
        (∀ j < k_nat, st'.mem (handlesOut + j) = hs j ∧
          (LSFRep 4).rep (hs j)
            (canonicalLSFInitAuto Q_AN c_AN K_AN P_fp G₀ ℓ₀ k_nat j)
            (x_h j) st'.mem ∧
          (x_h j).vCap = vCap_host ∧ (x_h j).eCap = eCap_host ∧ (x_h j).L_w = L_w_host ∧
          (x_h j).n0 = G₀.n ∧ (x_h j).m0 = G₀.E.card ∧
          ∀ a, (LSFRep 4).foot (hs j) (x_h j) a → heap ≤ a ∧ a < endHeap) ∧
        (∀ j₁ < k_nat, ∀ j₂ < k_nat, j₁ ≠ j₂ →
          ∀ a, (LSFRep 4).foot (hs j₁) (x_h j₁) a → ¬ (LSFRep 4).foot (hs j₂) (x_h j₂) a) ∧
        c ≤ lsfWindowCost Q_AN c_AN K_AN 4 L_in P_fp k_nat G₀.n G₀.m := by
  obtain ⟨hLin1, hP_Lin, hm_Lin, _⟩ := autoLimbCount_spec G₀ ℓ₀ P_fp
  exact lsfWindowInit_runs pos ω hp hQ (by decide) hLin1 hdiv hP_Lin hk hq_P hk_q hm_Lin
    hLw_host hG₀ hV₀ hdg0 hvCap_le heCap_le heCap1 hℓ₀_mem hg0_le hlen_le hhnd_le hheap1 hz
    hw_le hsp

end MinCostFlow.SparseCore.Program
