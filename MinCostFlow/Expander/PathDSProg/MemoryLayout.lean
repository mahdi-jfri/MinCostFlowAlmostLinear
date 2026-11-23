module

public import MinCostFlow.Expander.PathDSProg.MaskProjProg
public import MinCostFlow.Expander.PathDSProg.BoundsProg
public import MinCostFlow.Expander.DecomposePartBase
public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.Expander.GraphHelpers

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
public import MinCostFlow.Expander.PathDSProg.MemoryLayoutBase

/-!
# Memory Layout, Footprint, Potential, and Mathematical Invariants for `PathDSImpl`

Defines the 18-word metadata header at `b = hInit`, `PathDSConcrete` state, `pathDSRep : DSRep PathDSAbsState`,
`pathDSRep_local`, word-bound / heap-space / cost lemmas for `pathDSParams`, and the combinatorial
correctness bridges for both `[CS21]` and fallback modes:

1. `[CS21]` mode (`10 * csPhi Kγ c (3 * G.m) ≤ φ_in`):
   - `cs_init_S_empty`: `s_cs.S = ∅` on init (`deleted = []`, no isolated vertices in `subdivGraph G`).
   - `cs_del_vol_bound` / `cs_overBudget_vol_bound`: `G.vol V̂' ≤ gDel * t / φ_out`.
2. Fallback mode (`φ_in < 10 * csPhi Kγ c (3 * G.m)`):
   - `pruneWrap_runs_vc`: `pruneWrapProc` execution preserving both cut+volume potential inequality
     `volIn X (X \ R) + 2 * C_cap * cutIn X R ≤ volIn X B + 2 * C_cap * cutIn X B` and `pruneTimeBound`.
   - `fb_telescoping_step`: step bound `Φ(R') ≤ Φ(R) + 4 * C_cap + 4` yielding `G.vol V̂' ≤ gDel * t / φ_out`.
   - `fb_bfs_connected`: connectedness of `(subdivGraph G)[R]` guaranteeing `bfsPathProc` returns `1`.
   - `subdiv_walk_isAlt` & `walk_isWalk_of_proj`: alternating subdivision path projection for both modes.
-/

@[expose] public section

namespace MinCostFlow.Expander.PathDSProg

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 3. Volume, Connectivity, and `[CS21]` Helpers -/

lemma cs_init_S_empty {Kγ c : ℕ} {K : ℝ} {G : Cited.Graph}
    (hV : G.IsValid) (hnoIso : ∀ v < G.n, 1 ≤ G.deg v)
    {s_cs : PrunedExpander} (hG : s_cs.G = subdivGraph G) (hdel : s_cs.deleted = [])
    (hgood : PrunedExpander.Good K (Cited.csPhi Kγ c s_cs.G.m) s_cs) :
    s_cs.S = ∅ := by
  by_contra hne
  have hne' := Finset.nonempty_iff_ne_empty.mpr hne
  rcases hne' with ⟨v, hv⟩
  have hv_verts : v ∈ (subdivGraph G).verts := hG ▸ hgood.1 hv
  have hv_lt : v < (subdivGraph G).n := Finset.mem_range.mp hv_verts
  have hdeg : 1 ≤ (subdivGraph G).deg v := subdivGraph_no_isolated hV hnoIso v hv_lt
  have hvol_ge : 1 ≤ (subdivGraph G).vol s_cs.S := by
    have hs : (subdivGraph G).deg v ≤ (subdivGraph G).vol s_cs.S :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
    omega
  have hvol_zero : ((subdivGraph G).vol s_cs.S : ℝ) ≤ 0 := by
    have hg := hgood.2.1
    rw [hdel, List.length_nil, Nat.cast_zero, mul_zero, zero_div, hG] at hg
    exact hg
  have hvol_le : (subdivGraph G).vol s_cs.S ≤ 0 := by exact_mod_cast hvol_zero
  omega

lemma cs_del_vol_bound {Kγ c K_int cw_cs M : ℕ} {K : ℝ} (hK : max K 1 ≤ K_int)
    {G : Cited.Graph} (hV : G.IsValid) (hmM : G.m ≤ M) (hc : 1 ≤ c)
    {phiNum phiDen : ℕ} (hpn : 1 ≤ phiNum) (hpd : phiNum ≤ phiDen)
    {s_cs : PrunedExpander} (hG : s_cs.G = subdivGraph G)
    (hgood : PrunedExpander.Good K (Cited.csPhi Kγ c s_cs.G.m) s_cs) :
    (G.vol (projSet G.n s_cs.S) : ℝ) ≤
      (pathDSParams Kγ c K_int cw_cs).γ_del ((phiNum : ℝ) / (phiDen : ℝ)) M *
        (s_cs.deleted.length : ℝ) /
        (pathDSParams Kγ c K_int cw_cs).φ_out ((phiNum : ℝ) / (phiDen : ℝ)) M := by
  have hproj := projSet_spec hV s_cs.S
  have hvol1 : (G.vol (projSet G.n s_cs.S) : ℝ) ≤ ((subdivGraph G).vol s_cs.S : ℝ) := by
    exact_mod_cast hproj.2
  have hgood_vol := hgood.2.1
  rw [hG, subdivGraph_m] at hgood_vol
  have hφ_cs_pos : 0 < Cited.csPhi Kγ c (3 * G.m) := by
    unfold Cited.csPhi Cited.csGamma
    have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    positivity
  have hinv_cs : 1 / Cited.csPhi Kγ c (3 * G.m) ≤
      1 / (pathDSParams Kγ c K_int cw_cs).φ_out ((phiNum : ℝ) / (phiDen : ℝ)) M := by
    unfold PathDSParams.φ_out Cited.csPhi
    dsimp only [pathDSParams]
    rw [nat_ceil_div_eq hpn hpd, one_div_one_div, one_div_one_div]
    have hcs_mono : c * Cited.csGamma Kγ (3 * G.m) ≤ c * Cited.csGamma Kγ (3 * M) :=
      Nat.mul_le_mul_left c (csGamma_mono (by omega))
    have hden_ge : c * Cited.csGamma Kγ (3 * G.m) ≤
        phiOutDenImpl Kγ c ((phiDen + phiNum - 1) / phiNum) M := by
      unfold phiOutDenImpl; omega
    exact_mod_cast hden_ge
  have hgdel : max K 1 ≤ (pathDSParams Kγ c K_int cw_cs).γ_del ((phiNum : ℝ) / (phiDen : ℝ)) M := by
    rw [pathDSParams_γ_del_const]
    have hK_le : K ≤ (K_int : ℝ) := le_trans (le_max_left K 1) hK
    have h1_le : (1 : ℝ) ≤ (K_int : ℝ) := le_trans (le_max_right K 1) hK
    exact max_le hK_le h1_le |>.trans (le_max_of_le_right (le_max_left _ _))
  have hK_le_del : K ≤ (pathDSParams Kγ c K_int cw_cs).γ_del ((phiNum : ℝ) / (phiDen : ℝ)) M :=
    le_trans (le_max_left K 1) hgdel
  have hdel_nn : (0 : ℝ) ≤ (s_cs.deleted.length : ℝ) := Nat.cast_nonneg _
  calc (G.vol (projSet G.n s_cs.S) : ℝ)
      ≤ ((subdivGraph G).vol s_cs.S : ℝ) := hvol1
    _ ≤ K * (s_cs.deleted.length : ℝ) / Cited.csPhi Kγ c (3 * G.m) := hgood_vol
    _ = K * (s_cs.deleted.length : ℝ) * (1 / Cited.csPhi Kγ c (3 * G.m)) := by ring
    _ ≤ (pathDSParams Kγ c K_int cw_cs).γ_del ((phiNum : ℝ) / (phiDen : ℝ)) M *
          (s_cs.deleted.length : ℝ) *
          (1 / Cited.csPhi Kγ c (3 * G.m)) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK_le_del hdel_nn) (by positivity)
    _ ≤ (pathDSParams Kγ c K_int cw_cs).γ_del ((phiNum : ℝ) / (phiDen : ℝ)) M *
          (s_cs.deleted.length : ℝ) *
          (1 / (pathDSParams Kγ c K_int cw_cs).φ_out ((phiNum : ℝ) / (phiDen : ℝ)) M) := by
        apply mul_le_mul_of_nonneg_left hinv_cs
        have : 0 ≤ (pathDSParams Kγ c K_int cw_cs).γ_del ((phiNum : ℝ) / (phiDen : ℝ)) M := by
          rw [pathDSParams_γ_del_const]; positivity
        positivity
    _ = _ := by ring

lemma cs_overBudget_vol_bound {Kγ c K_int cw_cs M : ℕ}
    {G : Cited.Graph} (hV : G.IsValid) (hmM : G.m ≤ M) (hc : 1 ≤ c)
    {phiNum phiDen t : ℕ} (hpn : 1 ≤ phiNum) (hpd : phiNum ≤ phiDen)
    (ht : (3 * G.m) / (10 * c * Cited.csGamma Kγ (3 * G.m)) + 1 ≤ t) :
    (G.vol G.verts : ℝ) ≤
      (pathDSParams Kγ c K_int cw_cs).γ_del ((phiNum : ℝ) / (phiDen : ℝ)) M * (t : ℝ) /
        (pathDSParams Kγ c K_int cw_cs).φ_out ((phiNum : ℝ) / (phiDen : ℝ)) M := by
  rw [vol_verts_of_isValid hV]
  have hmul : 3 * G.m < t * (10 * c * Cited.csGamma Kγ (3 * G.m)) := by
    have hgam_pos : 1 ≤ Cited.csGamma Kγ (3 * G.m) := by
      rw [csGamma_eq_two_pow]; exact Nat.one_le_pow _ _ (by decide)
    have hdiv_pos : 0 < 10 * c * Cited.csGamma Kγ (3 * G.m) := by nlinarith
    exact (Nat.div_lt_iff_lt_mul hdiv_pos).mp (by omega)
  have h2m : 2 * G.m ≤ 10 * t * (c * Cited.csGamma Kγ (3 * G.m)) := by
    have : 2 * G.m ≤ 3 * G.m := by omega
    nlinarith
  have hcs_le : c * Cited.csGamma Kγ (3 * G.m) ≤
      phiOutDenImpl Kγ c ((phiDen + phiNum - 1) / phiNum) M := by
    have hm' := csGamma_mono (Kγ := Kγ) (by omega : 3 * G.m ≤ 3 * M)
    unfold phiOutDenImpl
    exact le_trans (Nat.mul_le_mul_left c hm') (le_trans (le_max_right _ _) (le_max_right _ _))
  have h2m_nat : 2 * G.m ≤ 190 * t * phiOutDenImpl Kγ c ((phiDen + phiNum - 1) / phiNum) M := by
    have : 10 * t * (c * Cited.csGamma Kγ (3 * G.m)) ≤ 190 * t * phiOutDenImpl Kγ c ((phiDen + phiNum - 1) / phiNum) M :=
      Nat.mul_le_mul (by omega) hcs_le
    omega
  have h2m_real : ((2 * G.m : ℕ) : ℝ) ≤
      (max 190 (max (K_int : ℝ) 7)) * (t : ℝ) *
        (phiOutDenImpl Kγ c ((phiDen + phiNum - 1) / phiNum) M : ℝ) := by
    have hle : ((190 * t * phiOutDenImpl Kγ c ((phiDen + phiNum - 1) / phiNum) M : ℕ) : ℝ) ≤
        (max (190 : ℝ) (max (K_int : ℝ) 7)) * (t : ℝ) *
          (phiOutDenImpl Kγ c ((phiDen + phiNum - 1) / phiNum) M : ℝ) := by
      push_cast
      have h190 : (190 : ℝ) ≤ max (190 : ℝ) (max (K_int : ℝ) 7) := le_max_left _ _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h190 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    exact le_trans (by exact_mod_cast h2m_nat) hle
  rw [pathDSParams_γ_del_const]
  unfold PathDSParams.φ_out
  dsimp only [pathDSParams]
  rw [nat_ceil_div_eq hpn hpd, div_div_eq_mul_div, div_one]
  exact h2m_real

/-! ## 4. Fallback Pruning (`pruneWrap_runs_vc`), Telescoping, and BFS Connectivity -/

/-- Exact analogue of `DecomposePartBase.pruneWrap_runs`, retaining the cut-plus-volume invariant
`volIn X ((X \ B) \ R) + 2 * C_cap * cutIn X R ≤ 2 * C_cap * cutIn X B`. -/
theorem pruneWrap_runs_vc {w : ℕ} {p : Program}
    {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ} {φ₀ : ℝ}
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hval : cfg.Valid)
    (hexp : cfg.G.IsConductanceExpanderOn cfg.X φ₀) (hφ₀ : 0 < φ₀)
    (hC5 : 5 ≤ cfg.C_cap) (hCphi : 4 ≤ φ₀ * ((cfg.C_cap : ℝ) - 1))
    (hθ : ∀ x ∈ cfg.X, x ∉ cfg.B → ∀ d < cfg.θ_out_nat, 3 * d ≤ cfg.degX x)
    (hw : PruneWordBound w cfg.G.n cfg.G.m cfg.C_cap cfg.H workAddr)
    (hdisj : PruneMemDisjoint gAddr csrAddr inBAddr outRAddr workAddr
      cfg.G.n cfg.G.m cfg.H cfg.G.encode.length)
    (hg_w : gAddr + cfg.G.encode.length < 2 ^ w)
    (hcsr_w : csrAddr + 2 * cfg.G.n + 1 + 4 * cfg.G.m < 2 ^ w)
    (hinB_w : inBAddr + cfg.G.n < 2 ^ w)
    (houtR_w : outRAddr + cfg.G.n < 2 ^ w)
    (hG : GraphAt mem gAddr cfg.G)
    (hCsr : HasCsrAt mem csrAddr cfg.G)
    (hinB : ∀ b, b ∈ cfg.B ↔ b < cfg.G.n ∧ mem (inBAddr + b) ≠ 0) :
    let args := [gAddr, csrAddr, inBAddr, outRAddr, workAddr, cfg.C_cap, cfg.H, cfg.θ_out_nat]
    ∃ st' c,
      Runs w p ω pruneWrapProc (startState args mem pos) (.returned 0) st' c ∧
      st'.pos = pos ∧
      PreservedOutside2 mem st'.mem outRAddr (outRAddr + cfg.G.n)
        workAddr (workAddr + pruneWorkSpace cfg.G.n cfg.G.m cfg.H) ∧
      c ≤ pruneTimeBound cfg.G.n cfg.G.m cfg.H + 3 ∧
      have R := (Finset.range cfg.G.n).filter fun x => decide (st'.mem (outRAddr + x) ≠ 0)
      R ⊆ cfg.X \ cfg.B ∧
      cfg.G.IsConductanceExpanderOn R (φ₀ / 3) ∧
      (∀ v ∈ R, cfg.θ_out_nat ≤ cfg.G.degIn R v) ∧
      cfg.G.volIn cfg.X (cfg.X \ R) + 2 * cfg.C_cap * cfg.G.cutIn cfg.X R ≤
        cfg.G.volIn cfg.X cfg.B + 2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B ∧
      (∀ u < cfg.G.n, st'.mem (outRAddr + u) = if u ∈ R then 1 else 0) := by
  intro args
  let st₀ := startState args mem pos
  have hreg0 : InitRegPre cfg gAddr csrAddr inBAddr outRAddr workAddr st₀ :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨st', c, hr, hpos', hpr, hc, hRsub, hexpR, hdegR, hvc, _, hbits⟩ :=
    pruneExpander_wordram_spec_bits (p := p) st₀ ω hreg0 hcfgX hval hexp hφ₀ hC5 hCphi hθ hw hdisj
      hg_w hcsr_w hinB_w houtR_w hG hCsr hinB
  have hret : Runs w p ω (.ret (.const 0)) st' (.returned 0) st' 2 :=
    runs_ret_iff.mpr ⟨0, by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  have hseq : Runs w p ω pruneWrapProc st₀ (.returned 0) st' (c + 2 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st', c, 2, hr, hret, rfl⟩)
  set R := (Finset.range cfg.G.n).filter fun x => decide (st'.mem (outRAddr + x) ≠ 0)
  change cfg.G.volIn cfg.X ((cfg.X \ cfg.B) \ R) + 2 * cfg.C_cap * cfg.G.cutIn cfg.X R ≤
    2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B at hvc
  have hunion : cfg.X \ R = cfg.B ∪ ((cfg.X \ cfg.B) \ R) := by
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨huX, huR⟩
      by_cases huB : u ∈ cfg.B
      · exact Or.inl huB
      · exact Or.inr ⟨⟨huX, huB⟩, huR⟩
    · rintro (huB | ⟨⟨huX, _⟩, huR⟩)
      · exact ⟨hval.2.1 huB, fun huR => (Finset.mem_sdiff.mp (hRsub huR)).2 huB⟩
      · exact ⟨huX, huR⟩
  have hdisj_BR : Disjoint cfg.B ((cfg.X \ cfg.B) \ R) :=
    Finset.disjoint_left.mpr fun _ hxB hx => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2 hxB
  have hvol_eq : cfg.G.volIn cfg.X (cfg.X \ R) =
      cfg.G.volIn cfg.X cfg.B + cfg.G.volIn cfg.X ((cfg.X \ cfg.B) \ R) := by
    rw [hunion, volIn_disjoint_union cfg.G cfg.X cfg.B ((cfg.X \ cfg.B) \ R) hdisj_BR]
  refine ⟨st', c + 2 + 1, hseq, hpos', hpr, by omega, hRsub, hexpR, hdegR, ?_, hbits⟩
  change cfg.G.volIn cfg.X (cfg.X \ R) + 2 * cfg.C_cap * cfg.G.cutIn cfg.X R ≤
    cfg.G.volIn cfg.X cfg.B + 2 * cfg.C_cap * cfg.G.cutIn cfg.X cfg.B
  rw [hvol_eq]
  omega

private lemma subdivGraph_cutIn_insert_mid_le {G : Cited.Graph} (hV : G.IsValid)
    (R : Finset ℕ) (e : ℕ) (_he : e < G.m) :
    let G_s := subdivGraph G
    let X := G_s.verts
    let B := (X \ R) ∪ {G.n + 2 * e, G.n + 2 * e + 1}
    G_s.cutIn X B ≤ G_s.cutIn X (X \ R) + 2 := by
  intro G_s X B
  have hSV : G_s.IsValid := subdivGraph_isValid hV
  rw [cutIn_eq_sum_map, cutIn_eq_sum_map, inside_verts_of_isValid hSV]
  have hlen : G_s.edges.length = 3 * G.m := subdivGraph_m G
  have heds : G_s.edges = (List.range (3 * G.m)).map fun k => G_s.edges.getD k (0, 0) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro k hk1 hk2
      simp only [List.length_map, List.length_range] at hk2
      simp only [List.getElem_map, List.getElem_range]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1]
  rw [heds, List.map_map, List.map_map]
  set f : ℕ → ℕ := fun k =>
    let ed := G_s.edges.getD k (0, 0)
    if (decide (ed.1 ∈ B) != decide (ed.2 ∈ B)) then 1 else 0
  set g : ℕ → ℕ := fun k =>
    let ed := G_s.edges.getD k (0, 0)
    (if (decide (ed.1 ∈ X \ R) != decide (ed.2 ∈ X \ R)) then 1 else 0) +
      (if k = 3 * e ∨ k = 3 * e + 2 then 1 else 0)
  have hpt : ∀ k ∈ List.range (3 * G.m), f k ≤ g k := by
    intro k hk
    rw [List.mem_range] at hk
    dsimp only [f, g]
    have hed := subdivGraph_edges_getD G hk
    set j := k / 3
    have hj : j < G.m := Nat.div_lt_of_lt_mul (by omega)
    have hvj := edge_valid_lt hV hj
    have hmem_a : G.n + 2 * e ∈ B := Finset.mem_union_right _ (by simp)
    have hmem_b : G.n + 2 * e + 1 ∈ B := Finset.mem_union_right _ (by simp)
    have hiff_B : ∀ x, x ≠ G.n + 2 * e → x ≠ G.n + 2 * e + 1 → decide (x ∈ B) = decide (x ∈ X \ R) := by
      intro x hx1 hx2
      exact decide_eq_decide.mpr (by simp [B, hx1, hx2])
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with hr | hr | hr
    · simp only [hr, ↓reduceIte] at hed
      rw [hed]
      by_cases hj_eq : j = e
      · have hk_eq : k = 3 * e := by omega
        simp [hk_eq]
        split_ifs <;> omega
      · have hne_k : ¬ (k = 3 * e ∨ k = 3 * e + 2) := by omega
        have h1 : (G.edges.getD j (0, 0)).1 ≠ G.n + 2 * e ∧ (G.edges.getD j (0, 0)).1 ≠ G.n + 2 * e + 1 :=
          ⟨by omega, by omega⟩
        have h2 : G.n + 2 * j ≠ G.n + 2 * e ∧ G.n + 2 * j ≠ G.n + 2 * e + 1 :=
          ⟨by omega, by omega⟩
        dsimp only
        rw [hiff_B _ h1.1 h1.2, hiff_B _ h2.1 h2.2]
        simp [hne_k]
    · simp only [hr, Nat.one_ne_zero, ↓reduceIte] at hed
      rw [hed]
      by_cases hj_eq : j = e
      · rw [hj_eq]
        simp [hmem_a, hmem_b]
      · have hne_k : ¬ (k = 3 * e ∨ k = 3 * e + 2) := by omega
        have h1 : G.n + 2 * j ≠ G.n + 2 * e ∧ G.n + 2 * j ≠ G.n + 2 * e + 1 :=
          ⟨by omega, by omega⟩
        have h2 : G.n + 2 * j + 1 ≠ G.n + 2 * e ∧ G.n + 2 * j + 1 ≠ G.n + 2 * e + 1 :=
          ⟨by omega, by omega⟩
        dsimp only
        rw [hiff_B _ h1.1 h1.2, hiff_B _ h2.1 h2.2]
        simp [hne_k]
    · simp only [show k % 3 ≠ 0 by omega, show k % 3 ≠ 1 by omega, ↓reduceIte] at hed
      rw [hed]
      by_cases hj_eq : j = e
      · have hk_eq : k = 3 * e + 2 := by omega
        simp [hk_eq]
        split_ifs <;> omega
      · have hne_k : ¬ (k = 3 * e ∨ k = 3 * e + 2) := by omega
        have h1 : G.n + 2 * j + 1 ≠ G.n + 2 * e ∧ G.n + 2 * j + 1 ≠ G.n + 2 * e + 1 :=
          ⟨by omega, by omega⟩
        have h2 : (G.edges.getD j (0, 0)).2 ≠ G.n + 2 * e ∧ (G.edges.getD j (0, 0)).2 ≠ G.n + 2 * e + 1 :=
          ⟨by omega, by omega⟩
        dsimp only
        rw [hiff_B _ h1.1 h1.2, hiff_B _ h2.1 h2.2]
        simp [hne_k]
  have hsum := sum_map_le_sum_map hpt
  rw [sum_map_add] at hsum
  have hadd_le : ((List.range (3 * G.m)).map fun k => if k = 3 * e ∨ k = 3 * e + 2 then 1 else 0).sum ≤ 2 := by
    have hsplit : ∀ k ∈ List.range (3 * G.m),
        (if k = 3 * e ∨ k = 3 * e + 2 then 1 else 0) ≤
          (if k = 3 * e then 1 else 0) + (if k = 3 * e + 2 then 1 else 0) := by
      intro k _; split_ifs <;> omega
    have hs1 := sum_map_le_sum_map hsplit
    rw [sum_map_add] at hs1
    have hnodup := List.nodup_range (n := 3 * G.m)
    have hle1 : ((List.range (3 * G.m)).map fun k => if k = 3 * e then 1 else 0).sum ≤ 1 := by
      have heq1 : ((List.range (3 * G.m)).map fun k => if k = 3 * e then 1 else 0) =
          ((List.range (3 * G.m)).map fun k => if decide (k = 3 * e) then 1 else 0) :=
        List.map_congr_left fun k _ => by simp
      rw [heq1, ← length_filter_eq_sum_map]
      have hnd : ((List.range (3 * G.m)).filter (fun k => decide (k = 3 * e))).Nodup := hnodup.filter _
      calc ((List.range (3 * G.m)).filter (fun k => decide (k = 3 * e))).length
          = ((List.range (3 * G.m)).filter (fun k => decide (k = 3 * e))).toFinset.card :=
            (List.toFinset_card_of_nodup hnd).symm
        _ ≤ ({3 * e} : Finset ℕ).card := Finset.card_le_card fun x hx => by
            simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx; simp [hx.2]
        _ = 1 := Finset.card_singleton _
    have hle2 : ((List.range (3 * G.m)).map fun k => if k = 3 * e + 2 then 1 else 0).sum ≤ 1 := by
      have heq2 : ((List.range (3 * G.m)).map fun k => if k = 3 * e + 2 then 1 else 0) =
          ((List.range (3 * G.m)).map fun k => if decide (k = 3 * e + 2) then 1 else 0) :=
        List.map_congr_left fun k _ => by simp
      rw [heq2, ← length_filter_eq_sum_map]
      have hnd : ((List.range (3 * G.m)).filter (fun k => decide (k = 3 * e + 2))).Nodup := hnodup.filter _
      calc ((List.range (3 * G.m)).filter (fun k => decide (k = 3 * e + 2))).length
          = ((List.range (3 * G.m)).filter (fun k => decide (k = 3 * e + 2))).toFinset.card :=
            (List.toFinset_card_of_nodup hnd).symm
        _ ≤ ({3 * e + 2} : Finset ℕ).card := Finset.card_le_card fun x hx => by
            simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx; simp [hx.2]
        _ = 1 := Finset.card_singleton _
    omega
  exact le_trans hsum (Nat.add_le_add_left hadd_le _)

private lemma subdivGraph_volIn_insert_mid_le {G : Cited.Graph} (hV : G.IsValid)
    (R : Finset ℕ) (e : ℕ) (he : e < G.m) :
    let G_s := subdivGraph G
    let X := G_s.verts
    let B := (X \ R) ∪ {G.n + 2 * e, G.n + 2 * e + 1}
    G_s.volIn X B ≤ G_s.volIn X (X \ R) + 4 := by
  intro G_s X B
  set S_new := ({G.n + 2 * e, G.n + 2 * e + 1} : Finset ℕ) \ (X \ R)
  have hunion : B = (X \ R) ∪ S_new := by
    ext x; simp [B, S_new]
  have hdisj : Disjoint (X \ R) S_new := disjoint_sdiff_self_right
  rw [hunion, volIn_disjoint_union G_s X (X \ R) S_new hdisj]
  have hsub : S_new ⊆ {G.n + 2 * e, G.n + 2 * e + 1} := Finset.sdiff_subset
  have hvol_pair : G_s.volIn X {G.n + 2 * e, G.n + 2 * e + 1} ≤ 4 := by
    unfold Cited.Graph.volIn
    have hSV : G_s.IsValid := subdivGraph_isValid hV
    have hmid := subdivGraph_deg_mid hV he
    have ha_eq : G_s.degIn X (G.n + 2 * e) = G_s.deg (G.n + 2 * e) := rfl
    have hb_eq : G_s.degIn X (G.n + 2 * e + 1) = G_s.deg (G.n + 2 * e + 1) := rfl
    have hne : G.n + 2 * e ≠ G.n + 2 * e + 1 := by omega
    rw [Finset.sum_pair hne, ha_eq, hb_eq, hmid.1, hmid.2]
  have hvol_mono : G_s.volIn X S_new ≤ G_s.volIn X {G.n + 2 * e, G.n + 2 * e + 1} :=
    volIn_mono_right G_s X hsub
  omega

lemma fb_telescoping_step {Kγ c K_int cw_cs M : ℕ}
    {G : Cited.Graph} (hV : G.IsValid) (_hmM : G.m ≤ M)
    {phiNum phiDen t e : ℕ} (hpn : 1 ≤ phiNum) (hpd : phiNum ≤ phiDen) (he : e < G.m)
    {R R' : Finset ℕ} (hRsub : R ⊆ (subdivGraph G).verts)
    (_hR'sub : R' ⊆ (subdivGraph G).verts)
    (hstep_pot :
      let G_s := subdivGraph G
      let X := G_s.verts
      let C_cap := 40 * ((phiDen + phiNum - 1) / phiNum) + 1
      let B := (X \ R) ∪ {G.n + 2 * e, G.n + 2 * e + 1}
      G_s.volIn X (X \ R') + 2 * C_cap * G_s.cutIn X R' ≤
        G_s.volIn X B + 2 * C_cap * G_s.cutIn X B)
    (hprev :
      let G_s := subdivGraph G
      let X := G_s.verts
      let C_cap := 40 * ((phiDen + phiNum - 1) / phiNum) + 1
      G_s.volIn X (X \ R) + 2 * C_cap * G_s.cutIn X R ≤ t * (4 * C_cap + 4)) :
    let G_s := subdivGraph G
    let X := G_s.verts
    let C_cap := 40 * ((phiDen + phiNum - 1) / phiNum) + 1
    G_s.volIn X (X \ R') + 2 * C_cap * G_s.cutIn X R' ≤ (t + 1) * (4 * C_cap + 4) ∧
    (G.vol (G.verts \ R') : ℝ) ≤
      (pathDSParams Kγ c K_int cw_cs).γ_del ((phiNum : ℝ) / (phiDen : ℝ)) M * ((t + 1 : ℕ) : ℝ) /
        (pathDSParams Kγ c K_int cw_cs).φ_out ((phiNum : ℝ) / (phiDen : ℝ)) M := by
  set G_s := subdivGraph G
  set X := G_s.verts
  set d := (phiDen + phiNum - 1) / phiNum
  set C_cap := 40 * d + 1
  have hcut := subdivGraph_cutIn_insert_mid_le hV R e he
  have hvol := subdivGraph_volIn_insert_mid_le hV R e he
  dsimp only at hcut hvol
  change G_s.cutIn X ((X \ R) ∪ {G.n + 2 * e, G.n + 2 * e + 1}) ≤ G_s.cutIn X (X \ R) + 2 at hcut
  change G_s.volIn X ((X \ R) ∪ {G.n + 2 * e, G.n + 2 * e + 1}) ≤ G_s.volIn X (X \ R) + 4 at hvol
  have hcut_sym : G_s.cutIn X (X \ R) = G_s.cutIn X R := cutIn_sdiff G_s X R hRsub
  have hpot' : G_s.volIn X (X \ R') + 2 * C_cap * G_s.cutIn X R' ≤ (t + 1) * (4 * C_cap + 4) := by
    have h1 : G_s.cutIn X ((X \ R) ∪ {G.n + 2 * e, G.n + 2 * e + 1}) ≤ G_s.cutIn X R + 2 := by
      omega
    have hmul : 2 * C_cap * G_s.cutIn X ((X \ R) ∪ {G.n + 2 * e, G.n + 2 * e + 1}) ≤
        2 * C_cap * (G_s.cutIn X R + 2) := Nat.mul_le_mul_left (2 * C_cap) h1
    nlinarith
  refine ⟨hpot', ?_⟩
  have hsub_orig : G.verts \ R' ⊆ X \ R' := by
    intro v hv
    dsimp only [X]
    simp only [Finset.mem_sdiff, Cited.Graph.verts, Finset.mem_range] at hv ⊢
    have hns : G.n ≤ G_s.n := by dsimp [G_s]; rw [subdivGraph_n]; omega
    exact ⟨lt_of_lt_of_le hv.1 hns, hv.2⟩
  have hvol_orig : G.vol (G.verts \ R') ≤ G_s.volIn X (X \ R') := by
    calc G.vol (G.verts \ R')
        = ∑ v ∈ G.verts \ R', G.deg v := rfl
      _ = ∑ v ∈ G.verts \ R', G_s.deg v := by
          refine Finset.sum_congr rfl fun v hv => ?_
          have hv' : v < G.n := Finset.mem_range.mp (Finset.mem_sdiff.mp hv).1
          exact (subdivGraph_deg_orig hV hv').symm
      _ ≤ ∑ v ∈ X \ R', G_s.degIn X v := Finset.sum_le_sum_of_subset hsub_orig
      _ = G_s.volIn X (X \ R') := rfl
  have hvol_nat : G.vol (G.verts \ R') ≤ 168 * d * (t + 1) := by
    have hd1 : 1 ≤ d := Nat.div_pos (by omega) hpn
    have h4C : 4 * C_cap + 4 ≤ 168 * d := by dsimp [C_cap]; omega
    calc G.vol (G.verts \ R') ≤ G_s.volIn X (X \ R') := hvol_orig
      _ ≤ (t + 1) * (4 * C_cap + 4) := by omega
      _ ≤ (t + 1) * (168 * d) := Nat.mul_le_mul_left (t + 1) h4C
      _ = 168 * d * (t + 1) := by ring
  have hd_le_den : d ≤ phiOutDenImpl Kγ c d M := by unfold phiOutDenImpl; omega
  have hmul_nat : G.vol (G.verts \ R') ≤ 190 * (t + 1) * phiOutDenImpl Kγ c d M := by
    calc G.vol (G.verts \ R') ≤ 168 * d * (t + 1) := hvol_nat
      _ ≤ 190 * (t + 1) * d := by nlinarith
      _ ≤ 190 * (t + 1) * phiOutDenImpl Kγ c d M := Nat.mul_le_mul_left (190 * (t + 1)) hd_le_den
  rw [pathDSParams_γ_del_const]
  unfold PathDSParams.φ_out
  dsimp only [pathDSParams]
  rw [nat_ceil_div_eq hpn hpd, div_div_eq_mul_div, div_one]
  have hreal : ((G.vol (G.verts \ R') : ℕ) : ℝ) ≤
      (max (190 : ℝ) (max (K_int : ℝ) 7)) * ((t + 1 : ℕ) : ℝ) *
        (phiOutDenImpl Kγ c d M : ℝ) := by
    have hcast : ((190 * (t + 1) * phiOutDenImpl Kγ c d M : ℕ) : ℝ) ≤
        (max (190 : ℝ) (max (K_int : ℝ) 7)) * ((t + 1 : ℕ) : ℝ) *
          (phiOutDenImpl Kγ c d M : ℝ) := by
      push_cast
      have h190 : (190 : ℝ) ≤ max (190 : ℝ) (max (K_int : ℝ) 7) := le_max_left _ _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h190 (by positivity)) (by positivity)
    exact le_trans (by exact_mod_cast hmul_nat) hcast
  exact hreal

lemma fb_bfs_no_zero_cut {G : Cited.Graph} (_hV : G.IsValid)
    {φ₀ : ℝ} (hφ₀ : 0 < φ₀)
    {del R : Finset ℕ} {mem : ℕ → ℕ} {vMaskAddr eMaskAddr : ℕ}
    (hRsub : R ⊆ (subdivGraph G).verts)
    (hexpR : (subdivGraph G).IsConductanceExpanderOn R φ₀)
    (hdegR : ∀ z ∈ R, 1 ≤ (subdivGraph G).degIn R z)
    (hmidR : ∀ e ∈ del, G.n + 2 * e ∉ R ∧ G.n + 2 * e + 1 ∉ R)
    (hvMask : ∀ x < (subdivGraph G).n, mem (vMaskAddr + x) = if x ∈ R then 1 else 0)
    (heMask : ∀ j < (subdivGraph G).m, mem (eMaskAddr + j) = if ∃ e ∈ del, j = 3 * e + 1 then 0 else 1)
    {u v : ℕ} (hu : u ∈ R) (hv : v ∈ R)
    (hbad : ∃ S : Finset ℕ, u ∈ S ∧ v ∉ S ∧ S ⊆ Finset.range (subdivGraph G).n ∧
      (∀ x ∈ S, mem (vMaskAddr + x) ≠ 0) ∧
      (∀ j < (subdivGraph G).m, mem (eMaskAddr + j) ≠ 0 →
        ∀ x ∈ S, ∀ y, Walk.EdgeMatches ((subdivGraph G).edges.getD j (0, 0)) x y →
          y < (subdivGraph G).n → mem (vMaskAddr + y) ≠ 0 → y ∈ S)) :
    False := by
  set G_s := subdivGraph G
  rcases hbad with ⟨S, huS, hvS, hSn, hSmask, hclosed⟩
  have hSR : S ⊆ R := fun x hx => by
    have hxn : x < G_s.n := Finset.mem_range.mp (hSn hx)
    have hnz := hSmask x hx
    rw [hvMask x hxn] at hnz
    by_contra hxR
    simp [hxR] at hnz
  have hSne : S.Nonempty := ⟨u, huS⟩
  have hSneR : S ≠ R := fun hEq => hvS (hEq ▸ hv)
  have hcut_pos : 0 < G_s.cutIn R S := by
    have hexp := hexpR S hSR hSne hSneR
    have hvol1 : (1 : ℝ) ≤ (G_s.volIn R S : ℝ) := by
      have h1 : G_s.degIn R u ≤ G_s.volIn R S := Finset.single_le_sum (fun _ _ => Nat.zero_le _) huS
      have hu_deg := hdegR u hu
      exact_mod_cast (by omega : 1 ≤ G_s.volIn R S)
    have hv_in : v ∈ R \ S := Finset.mem_sdiff.mpr ⟨hv, hvS⟩
    have hvol2 : (1 : ℝ) ≤ (G_s.volIn R (R \ S) : ℝ) := by
      have h1 : G_s.degIn R v ≤ G_s.volIn R (R \ S) := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv_in
      have hv_deg := hdegR v hv
      exact_mod_cast (by omega : 1 ≤ G_s.volIn R (R \ S))
    have hmin1 : 1 ≤ min (G_s.volIn R S : ℝ) (G_s.volIn R (R \ S) : ℝ) := le_min hvol1 hvol2
    have hmul_pos : φ₀ ≤ φ₀ * min (G_s.volIn R S : ℝ) (G_s.volIn R (R \ S) : ℝ) :=
      le_mul_of_one_le_right hφ₀.le hmin1
    have hcut_r : 0 < (G_s.cutIn R S : ℝ) := by linarith
    exact_mod_cast hcut_r
  rw [cutIn_eq_sum_map] at hcut_pos
  have hmem_cut : ∃ ed ∈ G_s.inside R, decide (ed.1 ∈ S) != decide (ed.2 ∈ S) := by
    by_contra hnone
    push Not at hnone
    have hzero : ((G_s.inside R).map fun ed => if decide (ed.1 ∈ S) != decide (ed.2 ∈ S) then 1 else 0) =
        (G_s.inside R).map fun _ => 0 := by
      apply List.map_congr_left
      intro ed hed
      have hf := hnone ed hed
      simp [hf]
    rw [hzero, sum_map_const, mul_zero] at hcut_pos
    omega
  rcases hmem_cut with ⟨ed, hed_in, hdiff⟩
  rw [mem_inside_iff] at hed_in
  rcases hed_in with ⟨hed_mem, h1R, h2R⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hed_mem
  have hj' : j < G_s.m := by simpa [Cited.Graph.m] using hj
  have hed_get : G_s.edges[j]'hj = G_s.edges.getD j (0, 0) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hm_nz : mem (eMaskAddr + j) ≠ 0 := by
    rw [heMask j hj']
    by_cases hdel : ∃ e ∈ del, j = 3 * e + 1
    · rcases hdel with ⟨e, he_del, rfl⟩
      have hne_mid := hmidR e he_del
      have hj3 : 3 * e + 1 < 3 * G.m := by simpa [G_s, subdivGraph_m] using hj'
      have hed3 := subdivGraph_edges_getD G hj3
      have hm1 : (3 * e + 1) % 3 = 1 := by omega
      have hdiv : (3 * e + 1) / 3 = e := by omega
      simp only [hm1, Nat.one_ne_zero, ↓reduceIte, hdiv] at hed3
      have hed1 : G_s.edges[3 * e + 1]'hj = (G.n + 2 * e, G.n + 2 * e + 1) :=
        hed_get.trans hed3
      rw [hed1] at h1R
      exact False.elim (hne_mid.1 h1R)
    · simp [hdel]
  have h1n : (G_s.edges[j]'hj).1 < G_s.n := Finset.mem_range.mp (hRsub h1R)
  have h2n : (G_s.edges[j]'hj).2 < G_s.n := Finset.mem_range.mp (hRsub h2R)
  have hm1_nz : mem (vMaskAddr + (G_s.edges[j]'hj).1) ≠ 0 := by rw [hvMask _ h1n]; simp [h1R]
  have hm2_nz : mem (vMaskAddr + (G_s.edges[j]'hj).2) ≠ 0 := by rw [hvMask _ h2n]; simp [h2R]
  by_cases h1S : (G_s.edges[j]'hj).1 ∈ S
  · have h2S : (G_s.edges[j]'hj).2 ∈ S := by
      apply hclosed j hj' hm_nz _ h1S _ ?_ h2n hm2_nz
      rw [← hed_get]; exact Or.inl ⟨rfl, rfl⟩
    simp [h1S, h2S] at hdiff
  · have h2S : (G_s.edges[j]'hj).2 ∈ S := by
      by_contra h2nS
      simp [h1S, h2nS] at hdiff
    have h1S' : (G_s.edges[j]'hj).1 ∈ S := by
      apply hclosed j hj' hm_nz _ h2S _ ?_ h1n hm1_nz
      rw [← hed_get]; exact Or.inr ⟨rfl, rfl⟩
    exact h1S h1S'

/-! ## 5. Shared Subdivision Path Projection Bridge -/

lemma isWalk_to_isPathAlong_subdiv {G : Cited.Graph}
    (del : List ℕ) (P : Walk) (u v : ℕ) (huv : u ≠ v)
    (hP : P.IsWalk (subdivGraph G) u v)
    (heMask : ∀ j ∈ P.edges, j ∉ subdivDel del) :
    IsPathAlong (PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, ∅⟩) u v P.verts := by
  rcases hP with ⟨_, _, ⟨_, _, heq⟩ | ⟨hne, hlen, hhead, hlast, hedges, hstep⟩⟩
  · exact False.elim (huv heq)
  · refine ⟨hhead, hlast, ?_⟩
    rw [List.isChain_iff_getElem]
    intro i hi
    have hi_len : i < P.edges.length := by omega
    have hj := hedges (P.edges.getD i 0) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_len]; exact List.getElem_mem _)
    have hj_nd := heMask (P.edges.getD i 0) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_len]; exact List.getElem_mem _)
    have hsm : P.edges.getD i 0 < (subdivGraph G).m := hj
    have hce : (subdivGraph G).edges.getD (P.edges.getD i 0) (0, 0) ∈
        PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, ∅⟩ := by
      unfold PrunedExpander.currentEdges
      simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨P.edges.getD i 0, ⟨hsm, hj_nd⟩, rfl⟩
    have hm := hstep i hi_len
    have hvi : P.verts[i] = P.verts.getD i 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < P.verts.length)]
    have hvi1 : P.verts[i + 1] = P.verts.getD (i + 1) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i + 1 < P.verts.length)]
    rw [hvi, hvi1]
    rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [← h1, ← h2]; exact hce
    · right; rw [← h1, ← h2]; exact hce

private lemma mem_currentEdges_subdiv_getD {G : Cited.Graph} {del : List ℕ} {a b : ℕ}
    (h : (a, b) ∈ PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, ∅⟩) :
    ∃ k < 3 * G.m, k ∉ subdivDel del ∧ (subdivGraph G).edges.getD k (0, 0) = (a, b) := by
  unfold PrunedExpander.currentEdges at h
  simp only [subdivGraph_m, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at h
  rcases h with ⟨k, ⟨hk, hnd⟩, he⟩
  exact ⟨k, hk, hnd, he⟩

lemma isPathAlong_subdivAlt {G : Cited.Graph} (hV : G.IsValid) (del : List ℕ) :
    ∀ (nlen : ℕ) (P_s : List ℕ) (u v : ℕ),
      P_s.length = nlen → u < G.n → v < G.n → P_s.Nodup →
      IsPathAlong (PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, ∅⟩) u v P_s →
      ∃ k, SubdivAltSeq G.n k P_s := by
  intro nlen
  induction nlen using Nat.strong_induction_on with
  | h nlen ih =>
    intro P_s u v hlen hu hv hnd hP
    rcases P_s with _ | ⟨x, rest⟩
    · simp [IsPathAlong] at hP
    · have hx : x = u := by simpa [IsPathAlong] using hP.1
      subst x
      rcases rest with _ | ⟨y, rest1⟩
      · exact ⟨0, rfl, fun i hi => by have := Nat.le_zero.mp hi; subst this; exact hu,
          fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
      · rcases hP with ⟨_, hlast, hch⟩
        rw [List.isChain_cons_cons] at hch
        have hy_edge : ∃ k1 < 3 * G.m, k1 ∉ subdivDel del ∧
            ((subdivGraph G).edges.getD k1 (0, 0) = (u, y) ∨
              (subdivGraph G).edges.getD k1 (0, 0) = (y, u)) := by
          rcases hch.1 with hm | hm
          · rcases mem_currentEdges_subdiv_getD hm with ⟨k, hk, hnd_k, he⟩; exact ⟨k, hk, hnd_k, Or.inl he⟩
          · rcases mem_currentEdges_subdiv_getD hm with ⟨k, hk, hnd_k, he⟩; exact ⟨k, hk, hnd_k, Or.inr he⟩
        rcases hy_edge with ⟨k1, hk1, hk1_nd, he1⟩
        rw [subdivGraph_edges_getD G hk1] at he1
        set j := k1 / 3
        have hj : j < G.m := by omega
        have hvj := edge_valid_lt hV hj
        have hstep3 : ∃ z w rest2, rest1 = z :: w :: rest2 ∧ w < G.n ∧ G.n ≤ y ∧ G.n ≤ z := by
          by_cases hm0 : k1 % 3 = 0
          · simp only [hm0, ↓reduceIte] at he1
            have hy_eq : y = G.n + 2 * j := by
              rcases he1 with h | h <;> have h1 := congrArg Prod.fst h <;>
                have h2 := congrArg Prod.snd h <;> omega
            have hu_eq : (G.edges.getD j (0, 0)).1 = u := by
              rcases he1 with h | h <;> have h1 := congrArg Prod.fst h <;>
                have h2 := congrArg Prod.snd h <;> omega
            subst hy_eq
            rcases rest1 with _ | ⟨z, rest1'⟩
            · simp at hlast; omega
            · rw [List.isChain_cons_cons] at hch
              have hne_zu : z ≠ u := fun hzu => (List.nodup_cons.mp hnd).1 (by simp [hzu])
              have hz_edge : ∃ k2 < 3 * G.m, k2 ∉ subdivDel del ∧
                  ((subdivGraph G).edges.getD k2 (0, 0) = (G.n + 2 * j, z) ∨
                    (subdivGraph G).edges.getD k2 (0, 0) = (z, G.n + 2 * j)) := by
                rcases hch.2.1 with hm | hm
                · rcases mem_currentEdges_subdiv_getD hm with ⟨k, hk, hndk, hek⟩; exact ⟨k, hk, hndk, Or.inl hek⟩
                · rcases mem_currentEdges_subdiv_getD hm with ⟨k, hk, hndk, hek⟩; exact ⟨k, hk, hndk, Or.inr hek⟩
              rcases hz_edge with ⟨k2, hk2, hk2_nd, he2⟩
              rw [subdivGraph_edges_getD G hk2] at he2
              have hv2 := edge_valid_lt hV (by omega : k2 / 3 < G.m)
              have hz_eq : z = G.n + 2 * j + 1 := by
                by_cases h0 : k2 % 3 = 0
                · simp only [h0, ↓reduceIte] at he2
                  rcases he2 with h | h
                  · have := congrArg Prod.fst h; omega
                  · have hf := congrArg Prod.fst h; have hs := congrArg Prod.snd h
                    have hk2j : k2 / 3 = j := by omega
                    rw [hk2j] at hf
                    omega
                · by_cases h1 : k2 % 3 = 1
                  · simp only [h1, Nat.one_ne_zero, ↓reduceIte] at he2
                    rcases he2 with h | h <;> have hf := congrArg Prod.fst h <;>
                      have hs := congrArg Prod.snd h <;> omega
                  · simp only [h0, h1, ↓reduceIte] at he2
                    rcases he2 with h | h <;> have hf := congrArg Prod.fst h <;>
                      have hs := congrArg Prod.snd h <;> omega
              subst hz_eq
              rcases rest1' with _ | ⟨w, rest2⟩
              · simp at hlast; omega
              · rw [List.isChain_cons_cons] at hch
                have hw_edge : ∃ k3 < 3 * G.m,
                    ((subdivGraph G).edges.getD k3 (0, 0) = (G.n + 2 * j + 1, w) ∨
                      (subdivGraph G).edges.getD k3 (0, 0) = (w, G.n + 2 * j + 1)) := by
                  rcases hch.2.2.1 with hm | hm
                  · rcases mem_currentEdges_subdiv_getD hm with ⟨k, hk, _, hek⟩; exact ⟨k, hk, Or.inl hek⟩
                  · rcases mem_currentEdges_subdiv_getD hm with ⟨k, hk, _, hek⟩; exact ⟨k, hk, Or.inr hek⟩
                rcases hw_edge with ⟨k3, hk3, he3⟩
                rw [subdivGraph_edges_getD G hk3] at he3
                have hv3 := edge_valid_lt hV (by omega : k3 / 3 < G.m)
                have hw_lt : w < G.n := by
                  have hne_wy : w ≠ G.n + 2 * j := fun hwy =>
                    (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by simp [hwy])
                  by_cases h0 : k3 % 3 = 0
                  · simp only [h0, ↓reduceIte] at he3
                    rcases he3 with h | h <;> have hf := congrArg Prod.fst h <;> have hs := congrArg Prod.snd h <;> omega
                  · by_cases h1 : k3 % 3 = 1
                    · simp only [h1, Nat.one_ne_zero, ↓reduceIte] at he3
                      rcases he3 with h | h <;> have hf := congrArg Prod.fst h <;> have hs := congrArg Prod.snd h <;> omega
                    · simp only [h0, h1, ↓reduceIte] at he3
                      rcases he3 with h | h <;> have hf := congrArg Prod.fst h <;> have hs := congrArg Prod.snd h <;> omega
                exact ⟨G.n + 2 * j + 1, w, rest2, rfl, hw_lt, by omega, by omega⟩
          · by_cases hm1 : k1 % 3 = 1
            · simp only [hm1, Nat.one_ne_zero, ↓reduceIte] at he1
              rcases he1 with h | h <;> have hf := congrArg Prod.fst h <;> have hs := congrArg Prod.snd h <;> omega
            · simp only [hm0, hm1, ↓reduceIte] at he1
              have hy_eq : y = G.n + 2 * j + 1 := by
                rcases he1 with h | h <;> have hf := congrArg Prod.fst h <;> have hs := congrArg Prod.snd h <;> omega
              have hu_eq : (G.edges.getD j (0, 0)).2 = u := by
                rcases he1 with h | h <;> have hf := congrArg Prod.fst h <;> have hs := congrArg Prod.snd h <;> omega
              subst hy_eq
              rcases rest1 with _ | ⟨z, rest1'⟩
              · simp at hlast; omega
              · rw [List.isChain_cons_cons] at hch
                have hne_zu : z ≠ u := fun hzu => (List.nodup_cons.mp hnd).1 (by simp [hzu])
                have hz_edge : ∃ k2 < 3 * G.m,
                    ((subdivGraph G).edges.getD k2 (0, 0) = (G.n + 2 * j + 1, z) ∨
                      (subdivGraph G).edges.getD k2 (0, 0) = (z, G.n + 2 * j + 1)) := by
                  rcases hch.2.1 with hm | hm
                  · rcases mem_currentEdges_subdiv_getD hm with ⟨k, hk, _, hek⟩; exact ⟨k, hk, Or.inl hek⟩
                  · rcases mem_currentEdges_subdiv_getD hm with ⟨k, hk, _, hek⟩; exact ⟨k, hk, Or.inr hek⟩
                rcases hz_edge with ⟨k2, hk2, he2⟩
                rw [subdivGraph_edges_getD G hk2] at he2
                have hv2 := edge_valid_lt hV (by omega : k2 / 3 < G.m)
                have hz_eq : z = G.n + 2 * j := by
                  by_cases h0 : k2 % 3 = 0
                  · simp only [h0, ↓reduceIte] at he2
                    rcases he2 with h | h <;> have hf := congrArg Prod.fst h <;> have hs := congrArg Prod.snd h <;> omega
                  · by_cases h1 : k2 % 3 = 1
                    · simp only [h1, Nat.one_ne_zero, ↓reduceIte] at he2
                      rcases he2 with h | h <;> have hf := congrArg Prod.fst h <;> have hs := congrArg Prod.snd h <;> omega
                    · simp only [h0, h1, ↓reduceIte] at he2
                      rcases he2 with h | h
                      · have hf := congrArg Prod.fst h; have hs := congrArg Prod.snd h
                        have hk2j : k2 / 3 = j := by omega
                        rw [hk2j] at hs
                        omega
                      · have := congrArg Prod.snd h; omega
                subst hz_eq
                rcases rest1' with _ | ⟨w, rest2⟩
                · simp at hlast; omega
                · rw [List.isChain_cons_cons] at hch
                  have hw_edge : ∃ k3 < 3 * G.m,
                      ((subdivGraph G).edges.getD k3 (0, 0) = (G.n + 2 * j, w) ∨
                        (subdivGraph G).edges.getD k3 (0, 0) = (w, G.n + 2 * j)) := by
                    rcases hch.2.2.1 with hm | hm
                    · rcases mem_currentEdges_subdiv_getD hm with ⟨k, hk, _, hek⟩; exact ⟨k, hk, Or.inl hek⟩
                    · rcases mem_currentEdges_subdiv_getD hm with ⟨k, hk, _, hek⟩; exact ⟨k, hk, Or.inr hek⟩
                  rcases hw_edge with ⟨k3, hk3, he3⟩
                  rw [subdivGraph_edges_getD G hk3] at he3
                  have hv3 := edge_valid_lt hV (by omega : k3 / 3 < G.m)
                  have hw_lt : w < G.n := by
                    have hne_wy : w ≠ G.n + 2 * j + 1 := fun hwy =>
                      (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by simp [hwy])
                    by_cases h0 : k3 % 3 = 0
                    · simp only [h0, ↓reduceIte] at he3
                      rcases he3 with h | h <;> have hf := congrArg Prod.fst h <;> have hs := congrArg Prod.snd h <;> omega
                    · by_cases h1 : k3 % 3 = 1
                      · simp only [h1, Nat.one_ne_zero, ↓reduceIte] at he3
                        rcases he3 with h | h <;> have hf := congrArg Prod.fst h <;> have hs := congrArg Prod.snd h <;> omega
                      · simp only [h0, h1, ↓reduceIte] at he3
                        rcases he3 with h | h <;> have hf := congrArg Prod.fst h <;> have hs := congrArg Prod.snd h <;> omega
                  exact ⟨G.n + 2 * j, w, rest2, rfl, hw_lt, by omega, by omega⟩
        rcases hstep3 with ⟨z, w, rest2, rfl, hw_lt, hy_ge, hz_ge⟩
        have hlast' : (w :: rest2).getLast? = some v := by
          simpa [List.getLast?_cons_cons] using hlast
        have hnd' : (w :: rest2).Nodup :=
          (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).2
        have hP' : IsPathAlong (PrunedExpander.currentEdges ⟨subdivGraph G, 2, subdivDel del, ∅⟩)
            w v (w :: rest2) := by
          rw [List.isChain_cons_cons, List.isChain_cons_cons] at hch
          exact ⟨rfl, hlast', hch.2.2.2⟩
        obtain ⟨k', hk'_alt⟩ := ih (w :: rest2).length (by simp only [List.length_cons] at hlen ⊢; omega)
          (w :: rest2) w v rfl hw_lt hv hnd' hP'
        refine ⟨k' + 1, ?_, fun i hi => ?_, fun i hi => ?_⟩
        · have := hk'_alt.1; simp at this ⊢; omega
        · cases i with
          | zero => simp [hu]
          | succ i' =>
            simpa [show 3 * (i' + 1) = 3 * i' + 3 by omega] using hk'_alt.2.1 i' (by omega)
        · cases i with
          | zero => exact ⟨by simpa using hy_ge, by simpa using hz_ge⟩
          | succ i' =>
            exact ⟨by simpa [show 3 * (i' + 1) + 1 = (3 * i' + 1) + 3 by omega] using (hk'_alt.2.2 i' (by omega)).1,
              by simpa [show 3 * (i' + 1) + 2 = (3 * i' + 2) + 3 by omega] using (hk'_alt.2.2 i' (by omega)).2⟩

lemma walk_isWalk_of_proj {G : Cited.Graph} (hV : G.IsValid) {q : ℕ} (del : List ℕ)
    (delSet : Finset ℕ) (hdel_eq : del.toFinset = delSet)
    (S_s Vhat : Finset ℕ) (hVhat : ∀ x, x < G.n → x ∉ S_s → x ∉ Vhat)
    {u v : ℕ} (hu : u < G.n) (hv : v < G.n) (huv : u ≠ v)
    {P_s : List ℕ} (hnd : P_s.Nodup) (hnotS : ∀ w ∈ P_s, w ∉ S_s)
    (hP : IsPathAlong (PrunedExpander.currentEdges ⟨subdivGraph G, q, subdivDel del, S_s⟩) u v P_s) :
    let P : Walk := ⟨projPath G.n P_s, projEdges G.n P_s⟩
    P.IsWalk G u v ∧ P.verts.Nodup ∧
    (∀ e ∈ P.edges, e ∉ delSet) ∧
    (∀ x ∈ P.verts, x ∉ Vhat) := by
  have hpp := projPath_spec hV del S_s hu hv hnd hnotS hP
  have hpe := projEdges_spec hV del S_s hu hv hnd hP
  rcases hpp with ⟨hPnd, hPnotS, hPalong, hlen3, _⟩
  rcases hpe with ⟨hlenE, he_mem, he_match⟩
  have he_ne : (projEdges G.n P_s) ≠ [] := by
    intro hnil
    have hP_len1 : (projPath G.n P_s).length = 1 := by simp [hlenE, hnil]
    rcases hPalong with ⟨hhead, hlast, _⟩
    cases hp : projPath G.n P_s with
    | nil => simp [hp] at hP_len1
    | cons a t =>
      cases t with
      | nil =>
        rw [hp] at hhead hlast
        simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at hhead hlast
        exact huv (hhead.symm.trans hlast)
      | cons b t' => simp [hp] at hP_len1
  refine ⟨⟨hu, hv, Or.inr ⟨he_ne, hlenE, hPalong.1, hPalong.2.1,
    fun j hj => (he_mem j hj).1, fun i hi => he_match i hi⟩⟩,
    hPnd, fun e he heSet => (he_mem e he).2 (by simpa [← hdel_eq] using heSet), fun x hx => ?_⟩
  have hxn : x < G.n := by
    rw [projPath, List.mem_filter] at hx
    exact decide_eq_true_eq.mp hx.2
  have hxnot : x ∉ projSet G.n S_s := hPnotS x hx
  have hxnotS : x ∉ S_s := fun hxs => hxnot (by simp [projSet, hxs, hxn])
  exact hVhat x hxn hxnotS

end MinCostFlow.Expander.PathDSProg
