module

public import MinCostFlow.Spanner.ProgBuildWitness

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pure Arithmetic, Alignment, and Witness-OK Proofs for `buildWitnessCoreBody`

Proves the integer ceil-division identities (`dJInt`, `dWInt`, `mwInt`, `tau1Int`, `tau2Int`,
`compWeights`), word-size and size upper bounds (`two_pow_level_le`, `compWeights_sum_le`,
`W_m_upper_le`), alignment properties of `WitnessCoreInput.buildCompsFrom`, and `mkWitnessData_ok`
showing that all Task 1 `WitnessOK` invariants hold for any valid concrete `WSubs`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## 1. General ceil-division & list-sum helpers -/

theorem nat_ceil_div_eq_all (a : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    Nat.ceil ((a : ℝ) / (b : ℝ)) = (a + (b - 1)) / b := by
  by_cases ha : a = 0
  · subst ha
    simp only [Nat.cast_zero, zero_div, Nat.ceil_zero, zero_add]
    exact (Nat.div_eq_of_lt (by omega)).symm
  · have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha
    set k := (a + (b - 1)) / b
    have hk_pos : 1 ≤ k := Nat.div_pos (by omega) hb
    have h1 : k * b ≤ a + (b - 1) := Nat.div_mul_le_self (a + (b - 1)) b
    have h2 : a + (b - 1) < k * b + b := by
      have := Nat.lt_div_mul_add hb (a := a + (b - 1))
      dsimp only [k]
      nlinarith
    have hb_pos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
    have hlo : ((k - 1 : ℕ) : ℝ) < (a : ℝ) / (b : ℝ) := by
      rw [lt_div_iff₀ hb_pos]
      have hnat : (k - 1) * b < a := by
        have : k * b = (k - 1) * b + b := by
          calc k * b = (k - 1 + 1) * b := by rw [Nat.sub_add_cancel hk_pos]
            _ = (k - 1) * b + b := by ring
        omega
      exact_mod_cast hnat
    have hhi : (a : ℝ) / (b : ℝ) ≤ (k : ℝ) := by
      rw [div_le_iff₀ hb_pos]
      exact_mod_cast (by omega : a ≤ k * b)
    exact Nat.ceil_eq_iff (by omega : k ≠ 0) |>.mpr ⟨hlo, hhi⟩

private lemma max_one_div_eq_inv_min {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    min ((1 : ℝ) / (a : ℝ)) ((1 : ℝ) / (b : ℝ)) = 1 / ((max a b : ℕ) : ℝ) := by
  rcases le_total a b with hab | hba
  · have hmax : max a b = b := max_eq_right hab
    have hinv : (1 : ℝ) / (b : ℝ) ≤ (1 : ℝ) / (a : ℝ) :=
      one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast hab)
    rw [hmax, min_eq_right hinv]
  · have hmax : max a b = a := max_eq_left hba
    have hinv : (1 : ℝ) / (a : ℝ) ≤ (1 : ℝ) / (b : ℝ) :=
      one_div_le_one_div_of_le (by exact_mod_cast hb) (by exact_mod_cast hba)
    rw [hmax, min_eq_left hinv]

namespace WitnessCoreInput

/-- Integer weight vector passed to `ConstructExpander` for raw component `c = (lvl, X_list)`. -/
def compWeights (inp : WitnessCoreInput) (c : ℕ × List ℕ) : List ℕ :=
  let J_sub := inp.prep.cJSub c
  let denom := inp.prep.phiNum_dec * 2 ^ c.1
  (List.range c.2.length).map fun k =>
    (J_sub.deg k * inp.prep.phiDen_dec + (denom - 1)) / denom

/-- Specification satisfied by the concrete `W_sub` graphs returned by `ceBase`. -/
def ValidWSubs (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (WSubs : List Graph) : Prop :=
  WSubs.length = inp.prep.rawComps.length ∧
  ∀ (ci : ℕ) (hci : ci < inp.prep.rawComps.length),
    let rc := inp.prep.rawComps[ci]
    let W := WSubs.getD ci ⟨0, []⟩
    let wList := inp.compWeights rc
    W.n = rc.2.length ∧
    W.IsValid ∧
    W.IsConductanceExpanderOn W.verts ce.φ_Const ∧
    ∀ (k : ℕ) (hk : k < rc.2.length),
      let hk_w : k < wList.length := by
        dsimp only [wList, compWeights]
        rw [List.length_map, List.length_range]
        exact hk
      (wList[k]'hk_w : ℝ) ≤ (W.deg k : ℝ) ∧
      (W.deg k : ℝ) ≤ (ce.c_deg_int : ℝ) * (wList[k]'hk_w : ℝ)

/-! ## 2. `buildCompsFrom` structural properties -/

theorem buildCompsFrom_length (inp : WitnessCoreInput) :
    ∀ offset raw ws, ws.length = raw.length →
      (inp.buildCompsFrom offset raw ws).length = raw.length
  | _, [], [], _ => rfl
  | offset, _ :: rest, _ :: ws, hlen => by
    simp only [List.length_cons] at hlen ⊢
    simpa [buildCompsFrom] using buildCompsFrom_length inp _ rest ws (by omega)

theorem buildCompsFrom_aligned (inp : WitnessCoreInput) :
    ∀ offset raw ws, ws.length = raw.length →
      CompsAligned offset (inp.buildCompsFrom offset raw ws)
  | _, [], [], _ => trivial
  | offset, (_, _) :: rest, W :: ws, hlen => by
    simp only [List.length_cons] at hlen
    exact ⟨rfl, buildCompsFrom_aligned inp (offset + W.m) rest ws (by omega)⟩

theorem buildCompsFrom_getElem_full (inp : WitnessCoreInput) :
    ∀ offset raw ws (hlen : ws.length = raw.length) (ci : ℕ) (hci : ci < raw.length),
      let cs := inp.buildCompsFrom offset raw ws
      let c := cs[ci]'(by rw [buildCompsFrom_length inp offset raw ws hlen]; exact hci)
      let rc := raw[ci]'hci
      c.level = rc.1 ∧ c.X = rc.2.toFinset ∧ c.verts = vertsOf rc.2.toFinset ∧
      c.J_sub = inp.prep.cJSub rc ∧ c.jSubOrigEdges = inp.prep.cJOrig rc ∧
      c.W_sub = ws[ci]'(by omega)
  | _, [], _, _, ci, hci => (Nat.not_lt_zero _ hci).elim
  | offset, rc :: rest, W :: ws, hlen, ci, hci => by
    cases ci with
    | zero => simp [buildCompsFrom, PrepInput.cJSub, PrepInput.cJOrig]
    | succ k =>
      simp only [List.length_cons] at hlen hci
      exact buildCompsFrom_getElem_full inp (offset + W.m) rest ws (by omega) k (by omega)

theorem buildCompsFrom_mem (inp : WitnessCoreInput) :
    ∀ offset raw ws (_hlen : ws.length = raw.length) c,
      c ∈ inp.buildCompsFrom offset raw ws →
      ∃ (rc : ℕ × List ℕ) (W : Graph),
        rc ∈ raw ∧ W ∈ ws ∧
        c.level = rc.1 ∧
        c.X = rc.2.toFinset ∧
        c.verts = vertsOf c.X ∧
        c.J_sub = inp.prep.cJSub rc ∧
        c.jSubOrigEdges = inp.prep.cJOrig rc ∧
        c.W_sub = W
  | _, [], _, _, _, hc => by simp [buildCompsFrom] at hc
  | _, _ :: _, [], hlen, _, _ => by simp at hlen
  | offset, rc :: rest, W :: ws, hlen, c, hc => by
    simp only [List.length_cons] at hlen
    simp only [buildCompsFrom, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨rc, W, List.mem_cons_self, List.mem_cons_self,
        rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rcases buildCompsFrom_mem inp (offset + W.m) rest ws (by omega) c hc with
        ⟨rc', W', hrc', hW', hl, hX, hv, hJ, hO, hW⟩
      exact ⟨rc', W', List.mem_cons_of_mem _ hrc', List.mem_cons_of_mem _ hW',
        hl, hX, hv, hJ, hO, hW⟩

/-! ## 3. Exact integer arithmetic equalities for `Phase 1` & weights -/

theorem dJInt_eq (inp : WitnessCoreInput) {mem : ℕ → ℕ} {w : ℕ} (hv : inp.prep.StaticValid mem w) :
    inp.dJInt =
      Nat.ceil (1 / ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ))) := by
  have hpn : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hpnd : inp.prep.phiNum_dec ≤ inp.prep.phiDen_dec := hv.2.2.2.2.2.2.2.2.2.1
  simpa [dJInt] using (nat_ceil_div_eq hpn hpnd).symm

theorem dWInt_eq (ce : ConstructExpanderImpl) :
    dWInt ce = Nat.ceil (1 / ce.φ_Const) := by
  simpa [dWInt, ConstructExpanderImpl.φ_Const] using
    (nat_ceil_div_eq ce.hphi_pos ce.hphi_le).symm

theorem mwInt_eq (inp : WitnessCoreInput) (ce : ConstructExpanderImpl)
    {mem : ℕ → ℕ} {w : ℕ} (hv : inp.prep.StaticValid mem w) :
    inp.mwInt ce =
      Nat.ceil ((2 * (ce.c_deg_int : ℝ)) * (inp.prep.J0_strip.m : ℝ) /
        ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ))) + 1 := by
  have hpn : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hpnd : inp.prep.phiNum_dec ≤ inp.prep.phiDen_dec := hv.2.2.2.2.2.2.2.2.2.1
  have hpn0 : (inp.prep.phiNum_dec : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hpn
  have hpd0 : (inp.prep.phiDen_dec : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le hpn hpnd)
  have hdiv : ((2 * (ce.c_deg_int : ℝ)) * (inp.prep.J0_strip.m : ℝ)) /
      ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) =
      (((2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec : ℕ) : ℝ)) /
        (inp.prep.phiNum_dec : ℝ) := by
    push_cast
    field_simp
  rw [hdiv, nat_ceil_div_eq_all _ hpn, mwInt, Nat.add_sub_assoc hpn]

private lemma ceil_inv_roundPhi_eq {φ : ℝ} (_hφ : 0 < φ) :
    Nat.ceil (1 / roundPhi φ) = Nat.ceil (1 / φ) := by
  unfold roundPhi
  rw [one_div_one_div]
  exact Nat.ceil_natCast _

theorem mkWitnessData_scalars (inp : WitnessCoreInput) (ce : ConstructExpanderImpl)
    (pds : PathDSParams) (WSubs : List Graph) {mem : ℕ → ℕ} {w : ℕ} (hv : inp.prep.StaticValid mem w) :
    let wd := inp.mkWitnessData ce pds WSubs
    wd.M_W = inp.mwInt ce ∧
    wd.φ_ds = (1 : ℝ) / (inp.phiDsDenInt ce pds : ℝ) ∧
    wd.γ_ExpPath = (inp.γExpInt ce pds : ℝ) ∧
    wd.γ_del = (inp.γDelInt ce pds : ℝ) ∧
    wd.τ₂ = (inp.tau2Int ce pds : ℝ) ∧
    wd.τ₁ = (inp.tau1Int ce pds : ℝ) := by
  have hpn : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hpnd : inp.prep.phiNum_dec ≤ inp.prep.phiDen_dec := hv.2.2.2.2.2.2.2.2.2.1
  have hφdec_pos : 0 < (inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ) :=
    div_pos (by exact_mod_cast hpn) (by exact_mod_cast lt_of_lt_of_le hpn hpnd)
  have hφce_pos : 0 < ce.φ_Const := ce.hφ_Const_pos
  have hdJ : Nat.ceil (1 / roundPhi ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ))) =
      inp.dJInt := by
    rw [ceil_inv_roundPhi_eq hφdec_pos, ← inp.dJInt_eq hv]
  have hdW : Nat.ceil (1 / roundPhi ce.φ_Const) = dWInt ce := by
    rw [ceil_inv_roundPhi_eq hφce_pos, ← dWInt_eq ce]
  have hdJ1 : 1 ≤ inp.dJInt := by rw [inp.dJInt_eq hv]; exact Nat.one_le_ceil_iff.mpr (div_pos one_pos hφdec_pos)
  have hdW1 : 1 ≤ dWInt ce := by rw [dWInt_eq ce]; exact Nat.one_le_ceil_iff.mpr (div_pos one_pos hφce_pos)
  have hdenJ : 1 ≤ pds.phiOutDen inp.dJInt inp.prep.J0_strip.m :=
    le_trans (le_trans (by decide : 1 ≤ 2) (le_max_left 2 _)) (pds.hphiOutDen_ge _ _ hdJ1)
  have hdenW : 1 ≤ pds.phiOutDen (dWInt ce) (inp.mwInt ce) :=
    le_trans (le_trans (by decide : 1 ≤ 2) (le_max_left 2 _)) (pds.hphiOutDen_ge _ _ hdW1)
  have hφds : (inp.mkWitnessData ce pds WSubs).φ_ds = 1 / (inp.phiDsDenInt ce pds : ℝ) := by
    change min (pds.φ_out (roundPhi _) _) (pds.φ_out (roundPhi ce.φ_Const) _) = _
    simp only [PathDSParams.φ_out, hdJ, hdW]
    exact max_one_div_eq_inv_min hdenJ hdenW
  have hγE : (inp.mkWitnessData ce pds WSubs).γ_ExpPath = (inp.γExpInt ce pds : ℝ) := by
    change max (pds.γ_ExpPath (roundPhi _) _) (pds.γ_ExpPath (roundPhi ce.φ_Const) _) = _
    simp only [PathDSParams.γ_ExpPath, hdJ, hdW]
    exact (Nat.cast_max _ _).symm
  have hγD : (inp.mkWitnessData ce pds WSubs).γ_del = (inp.γDelInt ce pds : ℝ) := by
    change max (pds.γ_del (roundPhi _) _) (pds.γ_del (roundPhi ce.φ_Const) _) = _
    simp only [PathDSParams.γ_del, hdJ, hdW]
    exact (Nat.cast_max _ _).symm
  have hdenPos : 0 < (inp.phiDsDenInt ce pds : ℝ) := by
    exact_mod_cast lt_of_lt_of_le hdenJ (le_max_left _ _)
  have hτ₂ : (inp.mkWitnessData ce pds WSubs).τ₂ = (inp.tau2Int ce pds : ℝ) := by
    change (inp.mkWitnessData ce pds WSubs).γ_ExpPath * (inp.mkWitnessData ce pds WSubs).γ_del /
      (inp.mkWitnessData ce pds WSubs).φ_ds = _
    rw [hγE, hγD, hφds, div_div_eq_mul_div, div_one, tau2Int]
    push_cast; ring
  have hvc : vcong inp.prep.J inp.H' (fun _ => 1) inp.embJH =
      (vcongNat inp.prep.J inp.H' inp.embJH : ℝ) :=
    (vcongNat_cast_eq inp.prep.J inp.H' inp.embJH).symm
  have hτ₁ : (inp.mkWitnessData ce pds WSubs).τ₁ = (inp.tau1Int ce pds : ℝ) := by
    change 2 * (inp.mkWitnessData ce pds WSubs).γ_ExpPath * (length inp.prep.J inp.embJH : ℝ) *
      (inp.mkWitnessData ce pds WSubs).γ_del *
      (vcong inp.prep.J inp.H' (fun _ => 1) inp.embJH + (maxDeg inp.prep.J : ℝ)) /
      (inp.mkWitnessData ce pds WSubs).φ_ds = _
    rw [hγE, hγD, hφds, hvc, div_div_eq_mul_div, div_one, tau1Int, tau2Int]
    push_cast; ring
  exact ⟨rfl, hφds, hγE, hγD, hτ₂, hτ₁⟩

/-! ## 4. Component degree, weight, and size upper bounds -/

theorem rawComps_deg_ge_phi {inp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hv : inp.prep.StaticValid mem w) {ci : ℕ} (hci : ci < inp.prep.rawComps.length) :
    let c := inp.prep.rawComps[ci]
    ∀ (k : ℕ), k < c.2.length →
      ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.1 ≤
        ((inp.prep.cJSub c).deg k : ℝ) := by
  rcases hv with ⟨_, _, _, _, _, _, _, _, hpn, hpnd, _pw, hprops, hdp, _⟩
  set c := inp.prep.rawComps[ci]
  have hc_mem : c ∈ inp.prep.rawComps := List.getElem_mem hci
  have hc_p := hprops c hc_mem
  have hX_mem : c.2.toFinset ∈ inp.prep.decomp.comps c.1 := by
    simp only [PrepInput.decomp, mkDecomposeOutput, List.mem_map, List.mem_filter]
    exact ⟨c, ⟨hc_mem, decide_eq_true rfl⟩, rfl⟩
  have hdi := (hdp.2.2.2 c.1 hc_p.1 hc_p.2.1).2.1 c.2.toFinset hX_mem
  have _hverts_eq : vertsOf c.2.toFinset = c.2 := vertsOf_toFinset_of_pairwise_lt hc_p.2.2.1
  dsimp only
  intro k hk
  have hnodup : c.2.Nodup := hc_p.2.2.1.imp (fun h => h.ne)
  have hcard : k < c.2.toFinset.card := by simpa [List.toFinset_card_of_nodup hnodup] using hk
  have hvk_mem : (vertsOf c.2.toFinset).getD k 0 ∈ c.2.toFinset := getD_vertsOf_mem hcard
  have hdeg_eq : (inp.prep.cJSub c).deg k =
      (inp.prep.decomp.graphAt inp.prep.J0_strip c.1).degIn c.2.toFinset
        ((vertsOf c.2.toFinset).getD k 0) :=
    inducedSubgraph_deg hcard
  rw [hdeg_eq]
  exact hdi.2.2.2.1 _ hvk_mem

theorem comp_weight_bounds {inp : WitnessCoreInput} {mem : ℕ → ℕ} {w : ℕ}
    (hv : inp.prep.StaticValid mem w) {ci : ℕ} (hci : ci < inp.prep.rawComps.length) :
    let c := inp.prep.rawComps[ci]
    let m0 := inp.prep.J0_strip.m
    inp.prep.phiNum_dec * 2 ^ c.1 ≤ 2 * m0 * inp.prep.phiDen_dec ∧
    2 ^ c.1 ≤ 2 * m0 * inp.prep.phiDen_dec ∧
    (inp.compWeights c).length = c.2.length ∧
    (∀ k (hk : k < c.2.length),
      let hk_w : k < (inp.compWeights c).length := by simpa [compWeights] using hk
      1 ≤ (inp.compWeights c)[k]'hk_w ∧
      ((inp.compWeights c)[k]'hk_w : ℝ) =
        Nat.ceil (((inp.prep.cJSub c).deg k : ℝ) /
          (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.1)) ∧
      (inp.prep.cJSub c).deg k ≤ 2 * m0) ∧
    (inp.compWeights c).sum ≤ 4 * m0 * inp.prep.phiDen_dec := by
  have hcprops := comp_props_at hv.toValid_zeroTail hci
  have hsz := PrepInput.StaticValid.size_bounds hv
  have hpn : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hpnd : inp.prep.phiNum_dec ≤ inp.prep.phiDen_dec := hv.2.2.2.2.2.2.2.2.2.1
  have hc_eq : inp.prep.rawComps[ci]! = inp.prep.rawComps[ci] := by
    simp [hci]
  set c := inp.prep.rawComps[ci]
  rw [hc_eq] at hcprops
  have hdeg_ge := rawComps_deg_ge_phi hv hci
  have hdeg_le_2m : ∀ k, (inp.prep.cJSub c).deg k ≤ 2 * inp.prep.J0_strip.m := by
    intro k
    have hcvalid : (inp.prep.cJSub c).IsValid := hcprops.2.2.2.2.2.2.2
    have hsum_deg := vol_verts_eq_two_mul_m hcvalid
    have hk_le : (inp.prep.cJSub c).deg k ≤ (inp.prep.cJSub c).vol (inp.prep.cJSub c).verts := by
      by_cases hk_n : k < (inp.prep.cJSub c).n
      · unfold Graph.vol Graph.volIn Graph.deg
        rw [Graph.verts, ← Finset.add_sum_erase (Finset.range (inp.prep.cJSub c).n) _ (Finset.mem_range.mpr hk_n)]
        exact Nat.le_add_right _ _
      · have h0 : (inp.prep.cJSub c).deg k = 0 := by
          unfold Graph.deg Graph.degIn
          rw [inside_verts_eq_edges hcvalid, Nat.add_eq_zero_iff, List.length_eq_zero_iff,
            List.length_eq_zero_iff, List.filter_eq_nil_iff, List.filter_eq_nil_iff]
          refine ⟨fun e he => ?_, fun e he => ?_⟩
          · have hev := hcvalid e he; simp [show e.1 ≠ k by omega]
          · have hev := hcvalid e he; simp [show e.2 ≠ k by omega]
        rw [h0]; exact Nat.zero_le _
    have hcm_le : (inp.prep.cJSub c).m ≤ inp.prep.J0_strip.m := by
      have h1 : (inp.prep.cJSub c).m ≤ (inp.prep.rawComps.map fun p => (inp.prep.cJSub p).m).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _
          (List.mem_map.mpr ⟨c, List.getElem_mem hci, rfl⟩)
      have hsum_jm := hsz.2.2.2.1
      omega
    omega
  have h0_lt : 0 < c.2.length := by have := hcprops.2.2.2.1; omega
  have hge0 := hdeg_ge 0 h0_lt
  have hdeg0_le := hdeg_le_2m 0
  have hmul_r : (inp.prep.phiNum_dec : ℝ) * (2 : ℝ) ^ c.1 ≤
      ((inp.prep.cJSub c).deg 0 : ℝ) * (inp.prep.phiDen_dec : ℝ) := by
    have hpd_pos : (0 : ℝ) < (inp.prep.phiDen_dec : ℝ) := by exact_mod_cast lt_of_lt_of_le hpn hpnd
    rw [div_mul_eq_mul_div, div_le_iff₀ hpd_pos] at hge0
    exact hge0
  have hmul_nat : inp.prep.phiNum_dec * 2 ^ c.1 ≤ (inp.prep.cJSub c).deg 0 * inp.prep.phiDen_dec := by
    exact_mod_cast hmul_r
  have hshift_le1 : inp.prep.phiNum_dec * 2 ^ c.1 ≤ 2 * inp.prep.J0_strip.m * inp.prep.phiDen_dec :=
    le_trans hmul_nat (Nat.mul_le_mul_right _ hdeg0_le)
  have hshift_le2 : 2 ^ c.1 ≤ 2 * inp.prep.J0_strip.m * inp.prep.phiDen_dec :=
    le_trans (Nat.le_mul_of_pos_left _ hpn) hshift_le1
  have hden_pos : 1 ≤ inp.prep.phiNum_dec * 2 ^ c.1 := by
    have := Nat.one_le_two_pow (n := c.1)
    nlinarith
  have hpt : ∀ (k : ℕ) (hk : k < c.2.length),
      let hk_w : k < (inp.compWeights c).length := by simpa [compWeights] using hk
      1 ≤ (inp.compWeights c)[k]'hk_w ∧
      ((inp.compWeights c)[k]'hk_w : ℝ) =
        Nat.ceil (((inp.prep.cJSub c).deg k : ℝ) /
          (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.1)) ∧
      (inp.prep.cJSub c).deg k ≤ 2 * inp.prep.J0_strip.m := by
    intro k hk hk_w
    have hgk := hdeg_ge k hk
    have hpd_pos : (0 : ℝ) < (inp.prep.phiDen_dec : ℝ) := by exact_mod_cast lt_of_lt_of_le hpn hpnd
    have hnat_ge : inp.prep.phiNum_dec * 2 ^ c.1 ≤ (inp.prep.cJSub c).deg k * inp.prep.phiDen_dec := by
      have : (inp.prep.phiNum_dec : ℝ) * (2 : ℝ) ^ c.1 ≤
          ((inp.prep.cJSub c).deg k : ℝ) * (inp.prep.phiDen_dec : ℝ) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hpd_pos] at hgk; exact hgk
      exact_mod_cast this
    have hget : (inp.compWeights c)[k]'hk_w =
        ((inp.prep.cJSub c).deg k * inp.prep.phiDen_dec + (inp.prep.phiNum_dec * 2 ^ c.1 - 1)) /
          (inp.prep.phiNum_dec * 2 ^ c.1) := by
      simp [compWeights]
    have h1 : 1 ≤ (inp.compWeights c)[k]'hk_w := by
      rw [hget]
      exact Nat.div_pos (by omega) hden_pos
    have hdiv_eq : ((inp.prep.cJSub c).deg k : ℝ) /
        (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.1) =
        (((inp.prep.cJSub c).deg k * inp.prep.phiDen_dec : ℕ) : ℝ) /
          ((inp.prep.phiNum_dec * 2 ^ c.1 : ℕ) : ℝ) := by
      push_cast; field_simp
    have hceil_eq : (inp.compWeights c)[k]'hk_w =
        Nat.ceil (((inp.prep.cJSub c).deg k : ℝ) /
          (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.1)) := by
      rw [hget, hdiv_eq, nat_ceil_div_eq_all _ hden_pos]
    exact ⟨h1, by exact_mod_cast hceil_eq, hdeg_le_2m k⟩
  have hsum_real : ((inp.compWeights c).sum : ℝ) ≤ 4 * (inp.prep.J0_strip.m : ℝ) * (inp.prep.phiDen_dec : ℝ) := by
    have hlen_w : (inp.compWeights c).length = c.2.length := by simp [compWeights]
    have hsum_cast : ((inp.compWeights c).sum : ℝ) =
        ∑ k ∈ Finset.range c.2.length, ((inp.compWeights c).getD k 0 : ℝ) := by
      have hnat : (inp.compWeights c).sum =
          ∑ k ∈ Finset.range (inp.compWeights c).length, (inp.compWeights c).getD k 0 := by
        simpa using (sum_range_getD_nat (inp.compWeights c) 0 (fun x => x)).symm
      rw [hnat, hlen_w, Nat.cast_sum]
    have hpt_le : ∀ k ∈ Finset.range c.2.length, ((inp.compWeights c).getD k 0 : ℝ) ≤
        2 * ((inp.prep.cJSub c).deg k : ℝ) * (inp.prep.phiDen_dec : ℝ) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hk_w : k < (inp.compWeights c).length := by simpa [compWeights] using hk'
      obtain ⟨_, hceil, _⟩ := hpt k hk'
      rw [List.getD_eq_getElem _ _ hk_w]
      have hw1 : 1 ≤ ((inp.prep.cJSub c).deg k : ℝ) /
          (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.1) := by
        have hpos : 0 < ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.1 := by
          have : (0 : ℝ) < inp.prep.phiNum_dec := by exact_mod_cast hpn
          have : (0 : ℝ) < inp.prep.phiDen_dec := by exact_mod_cast lt_of_lt_of_le hpn hpnd
          positivity
        rw [one_le_div hpos]
        exact hdeg_ge k hk'
      have hceil_r : ((inp.compWeights c)[k]'hk_w : ℝ) ≤
          2 * (((inp.prep.cJSub c).deg k : ℝ) /
            (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.1)) := by
        rw [hceil]; exact real_ceil_le_two_mul hw1
      have hge1_den : (1 : ℝ) ≤ (inp.prep.phiNum_dec : ℝ) * (2 : ℝ) ^ c.1 := by
        exact_mod_cast hden_pos
      have hdiv_le : ((inp.prep.cJSub c).deg k : ℝ) /
          (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.1) ≤
          ((inp.prep.cJSub c).deg k : ℝ) * (inp.prep.phiDen_dec : ℝ) := by
        have hpd0 : (inp.prep.phiDen_dec : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le hpn hpnd))
        have heq : ((inp.prep.cJSub c).deg k : ℝ) /
            (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ c.1) =
            ((inp.prep.cJSub c).deg k : ℝ) * (inp.prep.phiDen_dec : ℝ) /
              ((inp.prep.phiNum_dec : ℝ) * (2 : ℝ) ^ c.1) := by field_simp
        rw [heq]
        exact div_le_self (by positivity) hge1_den
      linarith
    have hsum_deg : ∑ k ∈ Finset.range c.2.length, ((inp.prep.cJSub c).deg k : ℝ) =
        2 * ((inp.prep.cJSub c).m : ℝ) := by
      have hvol := vol_verts_eq_two_mul_m hcprops.2.2.2.2.2.2.2
      have hnat : ∑ k ∈ Finset.range c.2.length, (inp.prep.cJSub c).deg k =
          2 * (inp.prep.cJSub c).m := by
        rw [← hvol, ← hcprops.2.2.2.2.2.2.1]; rfl
      exact_mod_cast hnat
    have hcm_le : (inp.prep.cJSub c).m ≤ inp.prep.J0_strip.m := by
      have h1 : (inp.prep.cJSub c).m ≤ (inp.prep.rawComps.map fun p => (inp.prep.cJSub p).m).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _
          (List.mem_map.mpr ⟨c, List.getElem_mem hci, rfl⟩)
      omega
    rw [hsum_cast]
    calc ∑ k ∈ Finset.range c.2.length, ((inp.compWeights c).getD k 0 : ℝ)
        ≤ ∑ k ∈ Finset.range c.2.length,
            2 * ((inp.prep.cJSub c).deg k : ℝ) * (inp.prep.phiDen_dec : ℝ) :=
          Finset.sum_le_sum hpt_le
      _ = 2 * (∑ k ∈ Finset.range c.2.length, ((inp.prep.cJSub c).deg k : ℝ)) *
            (inp.prep.phiDen_dec : ℝ) := by
          simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
      _ = 4 * ((inp.prep.cJSub c).m : ℝ) * (inp.prep.phiDen_dec : ℝ) := by
          rw [hsum_deg]; ring
      _ ≤ 4 * (inp.prep.J0_strip.m : ℝ) * (inp.prep.phiDen_dec : ℝ) := by
          have : ((inp.prep.cJSub c).m : ℝ) ≤ (inp.prep.J0_strip.m : ℝ) := by exact_mod_cast hcm_le
          nlinarith [show (0 : ℝ) ≤ inp.prep.phiDen_dec by exact_mod_cast Nat.zero_le _]
  have hsum_nat : (inp.compWeights c).sum ≤ 4 * inp.prep.J0_strip.m * inp.prep.phiDen_dec := by
    exact_mod_cast hsum_real
  exact ⟨hshift_le1, hshift_le2, by simp [compWeights], hpt, hsum_nat⟩

theorem mkWitnessData_W_m_upper {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hv : inp.prep.StaticValid mem w) (hws : inp.ValidWSubs ce WSubs) :
    (inp.mkWitnessData ce pds WSubs).W.m ≤
      inp.prep.J0_strip.m + 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec ∧
    ∀ ci (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length),
      ((inp.mkWitnessData ce pds WSubs).comps[ci]'hci).W_sub.m ≤ inp.mwInt ce := by
  have hsz := PrepInput.StaticValid.size_bounds hv
  have hpn : 1 ≤ inp.prep.phiNum_dec := hv.2.2.2.2.2.2.2.2.1
  have hpnd : inp.prep.phiNum_dec ≤ inp.prep.phiDen_dec := hv.2.2.2.2.2.2.2.2.2.1
  set cs := inp.buildCompsFrom inp.prep.j0Edges.length inp.prep.rawComps WSubs
  have hclen : cs.length = inp.prep.rawComps.length :=
    buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hsub_le_mw : ∀ ci (hci : ci < cs.length),
      (cs[ci]'hci).W_sub.m ≤ inp.mwInt ce ∧
      (cs[ci]'hci).W_sub.m * inp.prep.phiNum_dec ≤
        2 * ce.c_deg_int * (inp.prep.cJSub (inp.prep.rawComps[ci]'(by omega))).m * inp.prep.phiDen_dec := by
    intro ci hci
    have hcir : ci < inp.prep.rawComps.length := by omega
    obtain ⟨_, _, _, hJsub, _, hWsub⟩ :=
      buildCompsFrom_getElem_full inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hcir
    have hws_ci := hws.2 ci hcir
    rcases hws_ci with ⟨hWn, hWval, _, hWdeg⟩
    have hW_vol := vol_verts_eq_two_mul_m hWval
    have hcb := comp_weight_bounds hv hcir
    have hw_sub_eq : (cs[ci]'hci).W_sub = WSubs.getD ci ⟨0, []⟩ := by
      rw [hWsub, List.getD_eq_getElem _ _ (by rw [hws.1]; exact hcir)]
    have hW_sum_r : (2 * ((cs[ci]'hci).W_sub.m : ℝ)) ≤
        2 * (ce.c_deg_int : ℝ) *
          (2 * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ)) /
            ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) := by
      have hsumW : (2 * ((cs[ci]'hci).W_sub.m : ℝ)) =
          ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length, ((cs[ci]'hci).W_sub.deg k : ℝ) := by
        have hnat : 2 * (cs[ci]'hci).W_sub.m =
            ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length, (cs[ci]'hci).W_sub.deg k := by
          rw [hw_sub_eq, ← hW_vol]
          unfold Graph.vol Graph.volIn Graph.deg
          rw [Graph.verts, hWn]
        exact_mod_cast hnat
      have hdeg_pt : ∀ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
          ((cs[ci]'hci).W_sub.deg k : ℝ) ≤
            2 * (ce.c_deg_int : ℝ) *
              (((inp.prep.cJSub inp.prep.rawComps[ci]).deg k : ℝ) /
                (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) *
                  (2 : ℝ) ^ inp.prep.rawComps[ci].1)) := by
        intro k hk
        have hk' := Finset.mem_range.mp hk
        have hdk := hWdeg k hk'
        obtain ⟨_, hceil, _⟩ := hcb.2.2.2.1 k hk'
        have hdeg_ge := rawComps_deg_ge_phi hv hcir k hk'
        have hw1 : 1 ≤ ((inp.prep.cJSub inp.prep.rawComps[ci]).deg k : ℝ) /
            (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (2 : ℝ) ^ inp.prep.rawComps[ci].1) := by
          have hpd0 : (0 : ℝ) < (inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ) :=
            div_pos (by exact_mod_cast hpn) (by exact_mod_cast lt_of_lt_of_le hpn hpnd)
          rw [one_le_div (by positivity)]
          exact hdeg_ge
        have h2 := real_ceil_le_two_mul hw1
        have hle_c : ((inp.compWeights inp.prep.rawComps[ci])[k]'(by simp [compWeights]; exact hk') : ℝ) ≤
            2 * (((inp.prep.cJSub inp.prep.rawComps[ci]).deg k : ℝ) /
              (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) *
                (2 : ℝ) ^ inp.prep.rawComps[ci].1)) := hceil ▸ h2
        rw [hw_sub_eq]
        have hc_nn : (0 : ℝ) ≤ ce.c_deg_int := Nat.cast_nonneg _
        nlinarith [hdk.2]
      have hcprops := comp_props_at hv.toValid_zeroTail hcir
      have hc_eq' : inp.prep.rawComps[ci]! = inp.prep.rawComps[ci] := by
        simp [hcir]
      rw [hc_eq'] at hcprops
      have hsumJ : ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
          ((inp.prep.cJSub inp.prep.rawComps[ci]).deg k : ℝ) =
          2 * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ) := by
        have hvol := vol_verts_eq_two_mul_m hcprops.2.2.2.2.2.2.2
        have hnat : ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
            (inp.prep.cJSub inp.prep.rawComps[ci]).deg k =
            2 * (inp.prep.cJSub inp.prep.rawComps[ci]).m := by
          rw [← hvol, ← hcprops.2.2.2.2.2.2.1]; rfl
        exact_mod_cast hnat
      have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ inp.prep.rawComps[ci].1 := by exact_mod_cast Nat.one_le_two_pow
      rw [hsumW]
      calc ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length, ((cs[ci]'hci).W_sub.deg k : ℝ)
          ≤ ∑ k ∈ Finset.range inp.prep.rawComps[ci].2.length,
              2 * (ce.c_deg_int : ℝ) *
                (((inp.prep.cJSub inp.prep.rawComps[ci]).deg k : ℝ) /
                  (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) *
                    (2 : ℝ) ^ inp.prep.rawComps[ci].1)) := Finset.sum_le_sum hdeg_pt
        _ = 2 * (ce.c_deg_int : ℝ) *
              (2 * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ)) /
                (((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) *
                  (2 : ℝ) ^ inp.prep.rawComps[ci].1) := by
            simp_rw [div_eq_mul_inv, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hsumJ]
            ring
        _ ≤ 2 * (ce.c_deg_int : ℝ) *
              (2 * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ)) /
                ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) := by
            have hpd0 : (0 : ℝ) < (inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ) :=
              div_pos (by exact_mod_cast hpn) (by exact_mod_cast lt_of_lt_of_le hpn hpnd)
            exact div_le_div_of_nonneg_left (by positivity) hpd0 (le_mul_of_one_le_right hpd0.le hpow1)
    have hpd_pos : (0 : ℝ) < (inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ) :=
      div_pos (by exact_mod_cast hpn) (by exact_mod_cast lt_of_lt_of_le hpn hpnd)
    have hW_m_r : ((cs[ci]'hci).W_sub.m : ℝ) ≤
        2 * (ce.c_deg_int : ℝ) * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ) /
          ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) := by
      linarith [show 2 * (ce.c_deg_int : ℝ) * (2 * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ)) /
          ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) =
          2 * (2 * (ce.c_deg_int : ℝ) * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ) /
            ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ))) from by ring]
    have hJ_le_m0 : (inp.prep.cJSub inp.prep.rawComps[ci]).m ≤ inp.prep.J0_strip.m := by
      have h1 : (inp.prep.cJSub inp.prep.rawComps[ci]).m ≤
          (inp.prep.rawComps.map fun p => (inp.prep.cJSub p).m).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _
          (List.mem_map.mpr ⟨inp.prep.rawComps[ci], List.getElem_mem hcir, rfl⟩)
      omega
    have hceil_mw : (cs[ci]'hci).W_sub.m ≤ inp.mwInt ce := by
      rw [inp.mwInt_eq ce hv]
      have h1 : ((cs[ci]'hci).W_sub.m : ℝ) ≤
          2 * (ce.c_deg_int : ℝ) * (inp.prep.J0_strip.m : ℝ) /
            ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) := by
        refine le_trans hW_m_r ?_
        have : ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ) ≤ (inp.prep.J0_strip.m : ℝ) := by
          exact_mod_cast hJ_le_m0
        gcongr
      exact le_trans (Nat.le_ceil _ |>.trans' (Nat.cast_le.mp (le_trans h1 (Nat.le_ceil _)))) (Nat.le_succ _)
    have hmul_nat : (cs[ci]'hci).W_sub.m * inp.prep.phiNum_dec ≤
        2 * ce.c_deg_int * (inp.prep.cJSub inp.prep.rawComps[ci]).m * inp.prep.phiDen_dec := by
      have hpn_pos : (0 : ℝ) < (inp.prep.phiNum_dec : ℝ) := by exact_mod_cast hpn
      have h1 : ((cs[ci]'hci).W_sub.m : ℝ) * (inp.prep.phiNum_dec : ℝ) ≤
          2 * (ce.c_deg_int : ℝ) * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ) *
            (inp.prep.phiDen_dec : ℝ) := by
        have hpd0 : (inp.prep.phiDen_dec : ℝ) ≠ 0 :=
          by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le hpn hpnd))
        have hr := mul_le_mul_of_nonneg_right hW_m_r hpn_pos.le
        have hre : 2 * (ce.c_deg_int : ℝ) * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ) /
            ((inp.prep.phiNum_dec : ℝ) / (inp.prep.phiDen_dec : ℝ)) * (inp.prep.phiNum_dec : ℝ) =
            2 * (ce.c_deg_int : ℝ) * ((inp.prep.cJSub inp.prep.rawComps[ci]).m : ℝ) *
              (inp.prep.phiDen_dec : ℝ) := by
          have : (inp.prep.phiNum_dec : ℝ) ≠ 0 := hpn_pos.ne'
          field_simp
        linarith
      exact_mod_cast h1
    exact ⟨hceil_mw, hmul_nat⟩
  have hsum_w_le : (cs.map fun c => c.W_sub.m).sum ≤
      2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec := by
    have h1 : (cs.map fun c => c.W_sub.m).sum ≤
        (cs.map fun c => c.W_sub.m).sum * inp.prep.phiNum_dec :=
      Nat.le_mul_of_pos_right _ hpn
    have hsum_mul : (cs.map fun c => c.W_sub.m).sum * inp.prep.phiNum_dec =
        ∑ ci ∈ Finset.range cs.length, (cs.getD ci defaultCompInfo).W_sub.m * inp.prep.phiNum_dec := by
      rw [← Finset.sum_mul, sum_range_getD_nat cs defaultCompInfo (fun c => c.W_sub.m)]
    have hsum_pt : ∑ ci ∈ Finset.range cs.length,
        (cs.getD ci defaultCompInfo).W_sub.m * inp.prep.phiNum_dec ≤
        ∑ ci ∈ Finset.range inp.prep.rawComps.length,
          2 * ce.c_deg_int * (inp.prep.cJSub (inp.prep.rawComps.getD ci (0, []))).m *
            inp.prep.phiDen_dec := by
      rw [hclen]
      refine Finset.sum_le_sum fun ci hci_r => ?_
      have hci_r' := Finset.mem_range.mp hci_r
      have hci : ci < cs.length := by omega
      rw [List.getD_eq_getElem _ _ hci, List.getD_eq_getElem _ _ hci_r']
      exact (hsub_le_mw ci hci).2
    have hsum_j : ∑ ci ∈ Finset.range inp.prep.rawComps.length,
        2 * ce.c_deg_int * (inp.prep.cJSub (inp.prep.rawComps.getD ci (0, []))).m *
          inp.prep.phiDen_dec =
        2 * ce.c_deg_int * (inp.prep.rawComps.map fun c => (inp.prep.cJSub c).m).sum *
          inp.prep.phiDen_dec := by
      have hrange : ∑ ci ∈ Finset.range inp.prep.rawComps.length,
          (inp.prep.cJSub (inp.prep.rawComps.getD ci (0, []))).m =
          (inp.prep.rawComps.map fun c => (inp.prep.cJSub c).m).sum :=
        sum_range_getD_nat inp.prep.rawComps (0, []) (fun c => (inp.prep.cJSub c).m)
      simp_rw [mul_assoc, ← Finset.mul_sum]
      rw [← Finset.sum_mul, hrange]
    have hjm_le : (inp.prep.rawComps.map fun c => (inp.prep.cJSub c).m).sum ≤ inp.prep.J0_strip.m := by
      omega
    have hprod_le : 2 * ce.c_deg_int * (inp.prep.rawComps.map fun c => (inp.prep.cJSub c).m).sum *
        inp.prep.phiDen_dec ≤ 2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hjm_le)
    omega
  have hWm_eq : (inp.mkWitnessData ce pds WSubs).W.m =
      inp.prep.j0Edges.length + (cs.map fun c => c.W_sub.m).sum := by
    change (inp.prep.j0Edges.map _ ++ cs.flatMap compWEdges).length = _
    rw [List.length_append, List.length_map, compsAligned_sum_m]
  refine ⟨?_, fun ci hci => (hsub_le_mw ci hci).1⟩
  rw [hWm_eq]
  omega

end WitnessCoreInput

end MinCostFlow.Spanner
