module

public import MinCostFlow.Spanner.ProgTask2InitMath
public import MinCostFlow.Spanner.Task3Base

@[expose] public section

namespace MinCostFlow.Spanner

open Cited

/-!
# Pure Mathematical Specs and Round Counting for Word-RAM Task 3

Provides witness-data lifting lemmas (`mkW_isWalk_liftWSubWalk`,
`mkW_two_le_tau2_wW_comp`, `mkW_jSources_spec`, `t3_thresh_le_econg_iff`,
`t3_econg_le_thresh_iff`), initial embedding invariant (`t3Init_pure_inv`),
per-round progress bound (`t3Round_math_spec`), and logarithmic round-count
termination bound (`t3Round_bound_of_unembedded`).
-/

/-- Finset of unembedded edges in `J` (`0 ≤ eJ < J.m` with `emb eJ = none`). -/
def unembeddedSet2Pure (J : Graph) (emb : ℕ → Option Walk) : Finset ℕ :=
  {eJ ∈ Finset.range J.m | (emb eJ).isNone = true}

/-- A simple walk (`P.verts.Nodup`) cannot repeat an edge index. -/
lemma t3_walk_edges_nodup_of_verts_nodup {G : Graph} {u v : ℕ} {P : Walk}
    (hW : P.IsWalk G u v) (hnd : P.verts.Nodup) :
    P.edges.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  rcases hW with ⟨_, _, htriv | ⟨_, hvlen, _, _, _, hmatch⟩⟩
  · exfalso; rw [htriv.2.1] at hi; simp at hi
  have hij_aux : ∀ a b (ha : a < P.edges.length) (hb : b < P.edges.length), a < b →
    (P.edges[a]'ha) = (P.edges[b]'hb) → False := by
    intro a b ha hb hab hpe
    have hma := hmatch a ha
    have hmb := hmatch b hb
    rw [List.getD_eq_getElem _ _ ha] at hma
    rw [List.getD_eq_getElem _ _ hb] at hmb
    have hpe' : G.edges.getD (P.edges[a]'ha) (0, 0) = G.edges.getD (P.edges[b]'hb) (0, 0) :=
      congrArg (fun x => G.edges.getD x (0, 0)) hpe
    have ha0 : a < P.verts.length := by omega
    have ha1 : a + 1 < P.verts.length := by omega
    have hb0 : b < P.verts.length := by omega
    have hb1 : b + 1 < P.verts.length := by omega
    rw [List.getD_eq_getElem _ _ ha0, List.getD_eq_getElem _ _ ha1] at hma
    rw [List.getD_eq_getElem _ _ hb0, List.getD_eq_getElem _ _ hb1] at hmb
    rw [hpe'] at hma
    have hnod := List.nodup_iff_injective_getElem.mp hnd
    have hcases : (P.verts[b] = P.verts[a] ∧ P.verts[b + 1] = P.verts[a + 1]) ∨
        (P.verts[b] = P.verts[a + 1] ∧ P.verts[b + 1] = P.verts[a]) := by
      rcases hma with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hmb with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · left; exact ⟨h3.symm.trans h1, h4.symm.trans h2⟩
      · right; exact ⟨h3.symm.trans h2, h4.symm.trans h1⟩
      · right; exact ⟨h3.symm.trans h2, h4.symm.trans h1⟩
      · left; exact ⟨h3.symm.trans h1, h4.symm.trans h2⟩
    rcases hcases with ⟨hba, _⟩ | ⟨_, hba1⟩
    · have hfin := @hnod ⟨b, hb0⟩ ⟨a, ha0⟩ hba; simp at hfin; omega
    · have hfin := @hnod ⟨b + 1, hb1⟩ ⟨a, ha0⟩ hba1; simp at hfin; omega
  ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hij_aux i j hi hj hlt heq
  · exact hij_aux j i hj hi hgt heq.symm

/-- Lifting a walk `P` from `c.W_sub` to `wd.W` preserves `IsWalk` and edge bounds. -/
lemma mkW_isWalk_liftWSubWalk {tools : LocalSpannerTools 0 0}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {WSubs : List Graph}
    (hok : WitnessOK tools inp.H' inp.prep.J inp.embJH (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {ci : ℕ} (hci : ci < (inp.mkWitnessData ce pds WSubs).comps.length)
    {uL vL : ℕ} {P : Walk}
    (hP : P.IsWalk (inp.mkWitnessData ce pds WSubs).comps[ci].W_sub uL vL) :
    let wd := inp.mkWitnessData ce pds WSubs
    let c := wd.comps[ci]
    (liftWSubWalk c P).IsWalk wd.W (c.verts.getD uL 0) (c.verts.getD vL 0) ∧
      (liftWSubWalk c P).edges.length = P.edges.length ∧
      (P.verts.Nodup → (liftWSubWalk c P).edges.Nodup) ∧
      ∀ eW ∈ (liftWSubWalk c P).edges, wd.j0Edges.length ≤ eW ∧ eW < wd.W.m := by
  intro wd c
  have hcprops := hok.comp_props ci hci
  have hcX_sub : c.X ⊆ inp.prep.J.verts := hcprops.2.2.1
  have hcverts : c.verts = vertsOf c.X := hcprops.2.2.2.2.1
  have hcWn : c.W_sub.n = c.X.card := hcprops.2.2.2.2.2.2.2.2.2.2.2.1
  have hcstart_ge : wd.j0Edges.length ≤ c.wStart := hcprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcw_end : c.wStart + c.W_sub.m ≤ wd.W.m := hcprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hcverts_len : c.verts.length = c.X.card := by
    rw [hcverts]; exact Finset.length_sort (r := (· ≤ ·))
  rcases hP with ⟨huL, hvL, hcase⟩
  have huL_X : uL < c.verts.length := by rw [hcverts_len, ← hcWn]; exact huL
  have hvL_X : vL < c.verts.length := by rw [hcverts_len, ← hcWn]; exact hvL
  have hmem_in_J : ∀ x, x < c.verts.length → c.verts.getD x 0 < wd.W.n := by
    intro x hx
    rw [hok.W_n, List.getD_eq_getElem _ _ hx]
    have hmem : c.verts[x] ∈ vertsOf c.X := hcverts ▸ List.getElem_mem hx
    have hx_X : c.verts[x] ∈ c.X := (Finset.mem_sort (r := (· ≤ ·))).mp hmem
    exact Finset.mem_range.mp (hcX_sub hx_X)
  have hu_W : c.verts.getD uL 0 < wd.W.n := hmem_in_J uL huL_X
  have hv_W : c.verts.getD vL 0 < wd.W.n := hmem_in_J vL hvL_X
  have hwalk : (liftWSubWalk c P).IsWalk wd.W (c.verts.getD uL 0) (c.verts.getD vL 0) := by
    refine ⟨hu_W, hv_W, ?_⟩
    rcases hcase with ⟨hve, hee, huv⟩ | ⟨hne, hvlen, hhead, hlast, hedges_lt, hmatch⟩
    · left
      refine ⟨?_, ?_, ?_⟩
      · simp [liftWSubWalk, hve]
      · simp [liftWSubWalk, hee]
      · rw [huv]
    · right
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [liftWSubWalk] using hne
      · simp [liftWSubWalk, hvlen]
      · simp [liftWSubWalk, List.head?_map, hhead]
      · simp [liftWSubWalk, List.getLast?_map, hlast]
      · intro eW heW
        simp only [liftWSubWalk, List.mem_map] at heW
        rcases heW with ⟨eL, heL_mem, rfl⟩
        have heL_lt : eL < c.W_sub.m := hedges_lt eL heL_mem
        exact (mkW_W_edges_comp hws hci heL_lt).1
      · intro i hi
        simp only [liftWSubWalk, List.length_map] at hi
        have hi0 : i < P.verts.length := by omega
        have hi1 : i + 1 < P.verts.length := by omega
        have he_mem : P.edges.getD i 0 ∈ P.edges := by
          rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
        have heL_lt : P.edges.getD i 0 < c.W_sub.m := hedges_lt _ he_mem
        have hcomp := mkW_W_edges_comp hws hci heL_lt
        have hgetE : (liftWSubWalk c P).edges.getD i 0 = c.wStart + P.edges.getD i 0 := by
          rw [List.getD_eq_getElem _ _ (by simp [liftWSubWalk]; exact hi)]
          simp only [liftWSubWalk, List.getElem_map, List.getD_eq_getElem _ _ hi]
        have hgetV0 : (liftWSubWalk c P).verts.getD i 0 = c.verts.getD (P.verts.getD i 0) 0 := by
          rw [List.getD_eq_getElem _ _ (by simp [liftWSubWalk]; exact hi0)]
          simp only [liftWSubWalk, List.getElem_map, List.getD_eq_getElem _ _ hi0]
        have hgetV1 : (liftWSubWalk c P).verts.getD (i + 1) 0 = c.verts.getD (P.verts.getD (i + 1) 0) 0 := by
          rw [List.getD_eq_getElem _ _ (by simp [liftWSubWalk]; exact hi1)]
          simp only [liftWSubWalk, List.getElem_map, List.getD_eq_getElem _ _ hi1]
        rw [hgetE, hgetV0, hgetV1, hcomp.2.2.1]
        have hm := hmatch i hi
        rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨by rw [h1], by rw [h2]⟩
        · right; exact ⟨by rw [h1], by rw [h2]⟩
  refine ⟨hwalk, ?_, ?_, ?_⟩
  · simp [liftWSubWalk]
  · intro hnd
    have he_nd : P.edges.Nodup :=
      t3_walk_edges_nodup_of_verts_nodup ⟨huL, hvL, hcase⟩ hnd
    exact he_nd.map (fun _ _ h => by omega)
  · intro eW heW
    simp only [liftWSubWalk, List.mem_map] at heW
    rcases heW with ⟨eL, heL_mem, rfl⟩
    rcases hcase with ⟨_, hee, _⟩ | ⟨_, _, _, _, hedges_lt, _⟩
    · simp [hee] at heL_mem
    · have heL_lt : eL < c.W_sub.m := hedges_lt eL heL_mem
      exact ⟨by omega, by omega⟩

lemma mkW_one_div_phi_dec_le_tau2_half {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK (N_max := N_max) (W_max := W_max) tools inp.H' inp.prep.J inp.embJH
        (inp.mkWitnessData ce pds WSubs)) :
    let wd := inp.mkWitnessData ce pds WSubs
    1 / wd.φ_dec ≤ wd.τ₂ / 2 := by
  intro wd
  have hw := hok (exists_localSpannerTools 0 0).some
  have hds_pos := hw.φ_ds_pos
  have hds_half := hw.φ_ds_half
  have hγ_ge := hw.γ_ExpPath_ge
  have hτ₂_def : wd.τ₂ = wd.γ_ExpPath * wd.γ_del / wd.φ_ds := rfl
  have h1 : (2 : ℝ) ≤ 1 / wd.φ_ds := by
    rw [le_div_iff₀ hds_pos]; linarith
  have h2 : (2 : ℝ) ≤ wd.γ_ExpPath := le_trans h1 hγ_ge
  have h3 : (2 : ℝ) ≤ wd.γ_ExpPath * wd.γ_del := by
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ wd.γ_ExpPath * wd.γ_del := mul_le_mul h2 hw.γ_del_ge zero_le_one (by positivity)
  have h4 : 1 / wd.φ_dec ≤ 1 / wd.φ_ds :=
    one_div_le_one_div_of_le hds_pos hw.φ_ds_le_dec
  have h5 : 1 / wd.φ_ds ≤ (wd.γ_ExpPath * wd.γ_del / wd.φ_ds) / 2 := by
    calc 1 / wd.φ_ds = (2 / wd.φ_ds) / 2 := by ring
      _ ≤ ((wd.γ_ExpPath * wd.γ_del) / wd.φ_ds) / 2 :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right h3 (le_of_lt hds_pos)) (by norm_num)
  rw [← hτ₂_def] at h5
  exact le_trans h4 h5

lemma mkW_two_le_tau2_wW_comp {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK (N_max := N_max) (W_max := W_max) tools inp.H' inp.prep.J inp.embJH
        (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {eW : ℕ} (hge : (inp.mkWitnessData ce pds WSubs).j0Edges.length ≤ eW)
    (heW : eW < (inp.mkWitnessData ce pds WSubs).W.m) :
    let wd := inp.mkWitnessData ce pds WSubs
    2 ≤ wd.τ₂ * wd.wW eW := by
  intro wd
  have hw0 := hok (exists_localSpannerTools 0 0).some
  have hhalf : 1 / wd.φ_dec ≤ wd.τ₂ / 2 := mkW_one_div_phi_dec_le_tau2_half hok
  have h2phi : 2 * wd.φ_dec ≤ wd.wW eW := mkW_wW_ge_two_phi_comp hw0 hws hge heW
  have hdec_pos : 0 < wd.φ_dec := hw0.φ_dec_pos
  have hτ_pos : 0 < wd.τ₂ := hw0.τ₂_pos
  have hmul : 2 ≤ wd.τ₂ * wd.φ_dec := (div_le_iff₀ hdec_pos).mp hhalf |> fun h => by linarith
  calc (2 : ℝ) ≤ wd.τ₂ * wd.φ_dec := hmul
    _ ≤ wd.τ₂ * (2 * wd.φ_dec) := mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hτ_pos)
    _ ≤ wd.τ₂ * wd.wW eW := mul_le_mul_of_nonneg_left h2phi (le_of_lt hτ_pos)

/-- Relating Word-RAM integer edge-congestion threshold to `econgAt` for `mkWitnessData`. -/
lemma t3_thresh_le_econg_iff {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {emb : ℕ → Walk}
    (hok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK (N_max := N_max) (W_max := W_max) tools inp.H' inp.prep.J inp.embJH
        (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {eW r cnt wWNum : ℕ} (heW : eW < (inp.mkWitnessData ce pds WSubs).W.m)
    (hphi_pos : 0 < inp.prep.phiDen_dec)
    (hwW_num : (wWNum : ℝ) / (inp.prep.phiDen_dec : ℝ) = (inp.mkWitnessData ce pds WSubs).wW eW)
    (htau2_eq : (inp.tau2Int ce pds : ℝ) = (inp.mkWitnessData ce pds WSubs).τ₂)
    (hcnt_eq : (cnt : ℝ) / (inp.mkWitnessData ce pds WSubs).wW eW =
      econgAt inp.prep.J (fun _ => 1) (inp.mkWitnessData ce pds WSubs).wW emb eW) :
    (r * inp.tau2Int ce pds * wWNum ≤ cnt * inp.prep.phiDen_dec ↔
      (r : ℝ) * (inp.mkWitnessData ce pds WSubs).τ₂ ≤
        econgAt inp.prep.J (fun _ => 1) (inp.mkWitnessData ce pds WSubs).wW emb eW) := by
  let wd := inp.mkWitnessData ce pds WSubs
  have hwW_pos : 0 < wd.wW eW := mkW_wW_pos (hok (exists_localSpannerTools 0 0).some) hws heW
  have hden_pos : (0 : ℝ) < inp.prep.phiDen_dec := by exact_mod_cast hphi_pos
  rw [← hcnt_eq, le_div_iff₀ hwW_pos, ← hwW_num, ← htau2_eq]
  have hmul_eq : (r : ℝ) * (inp.tau2Int ce pds : ℝ) * ((wWNum : ℝ) / (inp.prep.phiDen_dec : ℝ)) *
      (inp.prep.phiDen_dec : ℝ) = (r : ℝ) * (inp.tau2Int ce pds : ℝ) * (wWNum : ℝ) := by field_simp
  constructor
  · intro h
    have hR : (r : ℝ) * (inp.tau2Int ce pds : ℝ) * (wWNum : ℝ) ≤ (cnt : ℝ) * (inp.prep.phiDen_dec : ℝ) := by
      exact_mod_cast h
    nlinarith [div_le_div_of_nonneg_right hR (le_of_lt hden_pos),
      show ((r : ℝ) * (inp.tau2Int ce pds : ℝ) * ((wWNum : ℝ) / (inp.prep.phiDen_dec : ℝ))) * (inp.prep.phiDen_dec : ℝ) =
        (r : ℝ) * (inp.tau2Int ce pds : ℝ) * (wWNum : ℝ) by field_simp]
  · intro h
    have hm := mul_le_mul_of_nonneg_right h (le_of_lt hden_pos)
    have hR : (r : ℝ) * (inp.tau2Int ce pds : ℝ) * (wWNum : ℝ) ≤ (cnt : ℝ) * (inp.prep.phiDen_dec : ℝ) := by linarith
    exact_mod_cast hR

/-- Relating reverse Word-RAM integer inequality `cnt * phiDen ≤ r * tau2Int * wWNum` to `econgAt ≤ r * τ₂`. -/
lemma t3_econg_le_thresh_iff {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph} {emb : ℕ → Walk}
    (hok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK (N_max := N_max) (W_max := W_max) tools inp.H' inp.prep.J inp.embJH
        (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {eW r cnt wWNum : ℕ} (heW : eW < (inp.mkWitnessData ce pds WSubs).W.m)
    (hphi_pos : 0 < inp.prep.phiDen_dec)
    (hwW_num : (wWNum : ℝ) / (inp.prep.phiDen_dec : ℝ) = (inp.mkWitnessData ce pds WSubs).wW eW)
    (htau2_eq : (inp.tau2Int ce pds : ℝ) = (inp.mkWitnessData ce pds WSubs).τ₂)
    (hcnt_eq : (cnt : ℝ) / (inp.mkWitnessData ce pds WSubs).wW eW =
      econgAt inp.prep.J (fun _ => 1) (inp.mkWitnessData ce pds WSubs).wW emb eW) :
    (cnt * inp.prep.phiDen_dec ≤ r * inp.tau2Int ce pds * wWNum ↔
      econgAt inp.prep.J (fun _ => 1) (inp.mkWitnessData ce pds WSubs).wW emb eW ≤
        (r : ℝ) * (inp.mkWitnessData ce pds WSubs).τ₂) := by
  let wd := inp.mkWitnessData ce pds WSubs
  have hwW_pos : 0 < wd.wW eW := mkW_wW_pos (hok (exists_localSpannerTools 0 0).some) hws heW
  have hden_pos : (0 : ℝ) < inp.prep.phiDen_dec := by exact_mod_cast hphi_pos
  rw [← hcnt_eq, div_le_iff₀ hwW_pos, ← hwW_num, ← htau2_eq]
  have hr : (r : ℝ) * (inp.tau2Int ce pds : ℝ) * ((wWNum : ℝ) / (inp.prep.phiDen_dec : ℝ)) *
      (inp.prep.phiDen_dec : ℝ) = (r : ℝ) * (inp.tau2Int ce pds : ℝ) * (wWNum : ℝ) := by field_simp
  constructor
  · intro h
    have hR : (cnt : ℝ) * (inp.prep.phiDen_dec : ℝ) ≤ (r : ℝ) * (inp.tau2Int ce pds : ℝ) * (wWNum : ℝ) := by
      exact_mod_cast h
    have hd := div_le_div_of_nonneg_right hR (le_of_lt hden_pos)
    have hleft : ((cnt : ℝ) * (inp.prep.phiDen_dec : ℝ)) / (inp.prep.phiDen_dec : ℝ) = (cnt : ℝ) := by field_simp
    have hright : ((r : ℝ) * (inp.tau2Int ce pds : ℝ) * (wWNum : ℝ)) / (inp.prep.phiDen_dec : ℝ) =
        (r : ℝ) * (inp.tau2Int ce pds : ℝ) * ((wWNum : ℝ) / (inp.prep.phiDen_dec : ℝ)) := by ring
    linarith
  · intro h
    have hm := mul_le_mul_of_nonneg_right h (le_of_lt hden_pos)
    have hR : (cnt : ℝ) * (inp.prep.phiDen_dec : ℝ) ≤ (r : ℝ) * (inp.tau2Int ce pds : ℝ) * (wWNum : ℝ) := by linarith
    exact_mod_cast hR

/-- Pure initial partial embedding for Task 3 matching `task3Init`. -/
def initEmb2 (J : Graph) (wd : WitnessData) : ℕ → Option Walk := fun eJ =>
  if eJ < J.m then
    match wd.jSources.getD eJ JEdgeSource.isLoop with
    | JEdgeSource.isLoop => some Walk.empty
    | JEdgeSource.inJ0 eW =>
      let e := wd.W.edges.getD eW (0, 0)
      some (Walk.single e.1 e.2 eW)
    | JEdgeSource.inComp _ _ => none
  else none

/-- Exact `jSources` characterization for `WitnessCoreInput.mkWitnessData`. -/
lemma mkW_jSources_spec {tools : LocalSpannerTools 0 0}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : WitnessOK tools inp.H' inp.prep.J inp.embJH (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {eJ : ℕ} (heJ : eJ < inp.prep.J.m) :
    let wd := inp.mkWitnessData ce pds WSubs
    wd.jSources.length = inp.prep.J.m ∧
      match wd.jSources.getD eJ JEdgeSource.isLoop with
      | JEdgeSource.isLoop => (inp.prep.J.edges[eJ]'heJ).1 = (inp.prep.J.edges[eJ]'heJ).2
      | JEdgeSource.inJ0 eW =>
          eW < wd.j0Edges.length ∧
            wd.j0Edges.getD eW 0 = eJ ∧
              eW < wd.W.m ∧
                wd.W.edges.getD eW (0, 0) = inp.prep.J.edges[eJ]'heJ ∧
                  wd.wW eW = wd.φ_dec
      | JEdgeSource.inComp ci jL =>
          ∃ (hci : ci < wd.comps.length) (hj : jL < wd.comps[ci].jSubOrigEdges.length),
            wd.comps[ci].jSubOrigEdges[jL] = eJ ∧
              jL < wd.comps[ci].J_sub.m ∧
                inp.prep.J.edges[eJ]'heJ =
                  (wd.comps[ci].verts.getD (wd.comps[ci].J_sub.edges.getD jL (0, 0)).1 0,
                    wd.comps[ci].verts.getD (wd.comps[ci].J_sub.edges.getD jL (0, 0)).2 0) := by
  intro wd
  have hjlen : wd.jSources.length = inp.prep.J.m := by
    simp [wd, WitnessCoreInput.mkWitnessData]
  have hjget : wd.jSources.getD eJ JEdgeSource.isLoop =
      if eJ ∈ wd.j0Edges then JEdgeSource.inJ0 (List.idxOf eJ wd.j0Edges)
      else match findJCompEdge eJ wd.comps 0 with
        | some (ci, jLocal) => JEdgeSource.inComp ci jLocal
        | none => JEdgeSource.isLoop := by
    rw [List.getD_eq_getElem _ _ (by rw [hjlen]; exact heJ)]
    change ((List.range inp.prep.J.m).map fun eJ' =>
      if eJ' ∈ wd.j0Edges then JEdgeSource.inJ0 (List.idxOf eJ' wd.j0Edges)
      else match findJCompEdge eJ' wd.comps 0 with
        | some (ci, jLocal) => JEdgeSource.inComp ci jLocal
        | none => JEdgeSource.isLoop)[eJ]'(by simp [heJ]) = _
    rw [List.getElem_map, List.getElem_range]
  refine ⟨hjlen, ?_⟩
  rw [hjget]
  split_ifs with hj0
  · refine ⟨List.idxOf_lt_length_iff.mpr hj0, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_iff.mpr hj0)]
      exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hj0)
    · have hj0_m : List.idxOf eJ wd.j0Edges < wd.j0Edges.length :=
        List.idxOf_lt_length_iff.mpr hj0
      have hj0_m' : List.idxOf eJ wd.j0Edges < inp.prep.j0Edges.length := hj0_m
      have hWm := mkW_W_edges_j0 (inp := inp) (ce := ce) (pds := pds) (WSubs := WSubs) hj0_m'
      have hidx : wd.j0Edges.getD (List.idxOf eJ wd.j0Edges) 0 = eJ := by
        rw [List.getD_eq_getElem _ _ hj0_m]
        exact List.getElem_idxOf hj0_m
      refine ⟨hWm.1, ?_, hWm.2.2⟩
      rw [hWm.2.1]
      change inp.prep.J.edges.getD (wd.j0Edges.getD (List.idxOf eJ wd.j0Edges) 0) (0, 0) = _
      rw [hidx, List.getD_eq_getElem _ _ heJ]
  · have hspec := findJCompEdge_spec eJ wd.comps 0
    cases hf : findJCompEdge eJ wd.comps 0 with
    | some p =>
      rcases p with ⟨ci, jL⟩
      rw [hf] at hspec
      rcases hspec with ⟨hci, hj, _, heq_eJ⟩
      simp only [Nat.sub_zero] at hci hj heq_eJ
      have hprops := hok.comp_props ci hci
      have hjlen_sub : wd.comps[ci].jSubOrigEdges.length = wd.comps[ci].J_sub.m :=
        hprops.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hjL_m : jL < wd.comps[ci].J_sub.m := hjlen_sub ▸ hj
      have hedge_eq := mkW_comp_jOrig_edge hs hok hws hci jL hjL_m
      refine ⟨hci, hj, heq_eJ, hjL_m, ?_⟩
      have h1 : wd.comps[ci].jSubOrigEdges.getD jL 0 = eJ := by
        rw [List.getD_eq_getElem _ _ hj]; exact heq_eJ
      have h2 := hedge_eq.2
      rw [h1, List.getD_eq_getElem _ _ heJ] at h2
      exact h2
    | none =>
      rw [hf] at hspec
      by_contra hne
      have hnl_eq : inp.prep.nlIdx = nonloopIndices inp.prep.J := hs.2.2.2.2.1
      have hJ0_eq : inp.prep.J0_strip = stripLoops inp.prep.J := hs.2.2.1
      have hdec := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hmem_nl : eJ ∈ inp.prep.nlIdx := by
        rw [hnl_eq]
        refine mem_nonloopIndices.mpr ⟨heJ, ?_⟩
        rw [List.getD_eq_getElem _ _ heJ]; exact hne
      obtain ⟨b, hb_nl, hb_eq⟩ := List.mem_iff_getElem.mp hmem_nl
      have hnl_len : (nonloopIndices inp.prep.J).length = inp.prep.J0_strip.m := by
        rw [hJ0_eq]; simp [stripLoops, Graph.m]
      have hb_m : b < inp.prep.J0_strip.m := by
        have hb_len : b < (nonloopIndices inp.prep.J).length := hnl_eq ▸ hb_nl
        omega
      have hlvl_le : inp.prep.decomp.level b ≤ inp.prep.decomp.ℓ := hdec.2.1 b hb_m
      cases hlvl : inp.prep.decomp.level b with
      | zero =>
        apply hj0
        change eJ ∈ inp.prep.j0Edges
        simp only [PrepInput.j0Edges, List.mem_map]
        refine ⟨b, ?_, ?_⟩
        · simp [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range, hb_m, hlvl]
        · rw [List.getD_eq_getElem _ _ hb_nl]; exact hb_eq
      | succ i' =>
        have hi0 : 0 < i' + 1 := Nat.zero_lt_succ i'
        have hiℓ : i' + 1 ≤ inp.prep.decomp.ℓ := by omega
        set J_i := DecomposeOutput.graphAt inp.prep.J0_strip inp.prep.decomp (i' + 1)
        have hb_ed : b ∈ DecomposeOutput.edgesAt inp.prep.J0_strip inp.prep.decomp (i' + 1) := by
          simp [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range, hb_m, hlvl]
        have he_Ji : inp.prep.J0_strip.edges.getD b (0, 0) ∈ J_i.edges := by
          simp only [J_i, DecomposeOutput.graphAt, List.mem_map]
          exact ⟨b, hb_ed, rfl⟩
        obtain ⟨X, hXcomp, hXends⟩ := (hdec.2.2.2 (i' + 1) hi0 hiℓ).2.2 _ he_Ji
        have hcomp_def : inp.prep.decomp = mkDecomposeOutput inp.prep.d_ℓ inp.prep.level inp.prep.rawComps := rfl
        rw [hcomp_def] at hXcomp
        simp only [mkDecomposeOutput, List.mem_map, List.mem_filter, decide_eq_true_eq] at hXcomp
        rcases hXcomp with ⟨rc, ⟨hrc_mem, hrc_lvl⟩, hrc_X⟩
        rcases List.mem_iff_getElem.mp hrc_mem with ⟨ci, hci_r, hci_eq⟩
        have hlen_c := inp.buildCompsFrom_length inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
        have hci : ci < wd.comps.length := by simpa [wd, WitnessCoreInput.mkWitnessData, hlen_c] using hci_r
        have hgf := inp.buildCompsFrom_getElem_full inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci_r
        set c := wd.comps[ci]'hci
        have hci_orig : c.jSubOrigEdges = inp.prep.cJOrig (inp.prep.rawComps[ci]'hci_r) := by
          simpa [c, wd, WitnessCoreInput.mkWitnessData] using hgf.2.2.2.2.1
        rcases List.mem_iff_getElem.mp hb_ed with ⟨a, ha_ed, ha_eq⟩
        have ha_m : a < J_i.m := by simpa [J_i, DecomposeOutput.graphAt, Graph.m] using ha_ed
        have ha_ed' : a < ((DecomposeOutput.edgesAt inp.prep.J0_strip inp.prep.decomp (i' + 1)).map
            (fun j => inp.prep.J0_strip.edges.getD j (0, 0))).length := by
          rw [List.length_map]; exact ha_ed
        have hJied : J_i.edges.getD a (0, 0) = inp.prep.J0_strip.edges.getD b (0, 0) := by
          simp only [J_i, DecomposeOutput.graphAt]
          rw [List.getD_eq_getElem _ _ ha_ed', List.getElem_map, ha_eq]
        have ha_inX : ((DecomposeOutput.graphAt inp.prep.J0_strip inp.prep.decomp rc.1).edges.getD a (0, 0)).1 ∈ rc.2.toFinset ∧
            ((DecomposeOutput.graphAt inp.prep.J0_strip inp.prep.decomp rc.1).edges.getD a (0, 0)).2 ∈ rc.2.toFinset := by
          rw [hrc_lvl, hrc_X]
          change (J_i.edges.getD a (0, 0)).1 ∈ X ∧ (J_i.edges.getD a (0, 0)).2 ∈ X
          rw [hJied]; exact hXends
        have ha_inside : a ∈ insideIndices (DecomposeOutput.graphAt inp.prep.J0_strip inp.prep.decomp rc.1) rc.2.toFinset := by
          refine mem_insideIndices.mpr ⟨?_, ha_inX⟩
          rw [hrc_lvl]; exact ha_m
        have heJ_mem : eJ ∈ c.jSubOrigEdges := by
          rw [hci_orig, hci_eq]; dsimp only [PrepInput.cJOrig]; rw [List.mem_map]
          refine ⟨a, ha_inside, ?_⟩
          have ha_ed_rc : a < (DecomposeOutput.edgesAt inp.prep.J0_strip inp.prep.decomp rc.1).length := by
            rw [hrc_lvl]; exact ha_ed
          rw [List.getD_eq_getElem _ _ ha_ed_rc]
          have : (DecomposeOutput.edgesAt inp.prep.J0_strip inp.prep.decomp rc.1)[a]'ha_ed_rc = b := by
            simp only [hrc_lvl]; exact ha_eq
          rw [this, List.getD_eq_getElem _ _ hb_nl, hb_eq]
        exact absurd heJ_mem (hspec c (List.getElem_mem hci))

/-- Properties of initial embedding `initEmb2`: partial embedding, `j0`/loops covered, length ≤ 1 ≤ γ, and `econg ≤ τ₂/2` at round `0`. -/
lemma t3Init_pure_inv
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {WSubs : List Graph} {mem : ℕ → ℕ} {w : ℕ}
    (hs : inp.prep.StaticValid mem w)
    (hok : ∀ {N_max : ℕ} {W_max : ℝ} (t : LocalSpannerTools N_max W_max),
      WitnessOK (N_max := N_max) (W_max := W_max) t inp.H' inp.prep.J inp.embJH
        (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs) :
    let wd := inp.mkWitnessData ce pds WSubs
    let emb := initEmb2 inp.prep.J wd
    IsPartialEmbedding inp.prep.J wd.W emb ∧
      (∀ eJ < inp.prep.J.m,
        (wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.isLoop ∨
          ∃ eW, wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW) →
          (emb eJ).isSome = true) ∧
      (∀ eJ < inp.prep.J.m, (partialToWalk emb eJ).edges.length ≤ 1) ∧
      (∀ eJ < inp.prep.J.m, ↑(partialToWalk emb eJ).edges.length ≤ wd.γ_ExpPath) ∧
      (∀ eJ < inp.prep.J.m, ∀ P, emb eJ = some P → P.edges.Nodup) ∧
      (∀ eW < wd.j0Edges.length,
        {eJ ∈ Finset.range inp.prep.J.m | eW ∈ (partialToWalk emb eJ).edges}.card ≤ 1) ∧
      (∀ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m,
        {eJ ∈ Finset.range inp.prep.J.m | eW ∈ (partialToWalk emb eJ).edges}.card = 0) ∧
      (∀ eW < wd.j0Edges.length, econgAt inp.prep.J (fun _ => 1) wd.wW (partialToWalk emb) eW ≤ wd.τ₂ / 2) ∧
      (∀ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m,
        econgAt inp.prep.J (fun _ => 1) wd.wW (partialToWalk emb) eW = 0) ∧
      (∀ eW < wd.W.m, econgAt inp.prep.J (fun _ => 1) wd.wW (partialToWalk emb) eW ≤ (0 + 1 / 2 : ℝ) * wd.τ₂) := by
  intro wd emb
  have hw := hok (exists_localSpannerTools 0 (0 : ℝ)).some
  have hJvalid : inp.prep.J.IsValid := hs.1
  have hτ₂_half : 1 / wd.φ_dec ≤ wd.τ₂ / 2 := mkW_one_div_phi_dec_le_tau2_half hok
  have hγ_ge : 1 ≤ wd.γ_ExpPath := by
    have h1 : (2 : ℝ) ≤ 1 / wd.φ_ds := by rw [le_div_iff₀ hw.φ_ds_pos]; linarith [hw.φ_ds_half]
    linarith [hw.γ_ExpPath_ge, h1]
  have hpart : IsPartialEmbedding inp.prep.J wd.W emb := by
    refine ⟨hw.W_n.symm.le, fun eJ heJ P hP => ?_⟩
    have hmem := List.getElem_mem heJ
    have hv := hJvalid inp.prep.J.edges[eJ] hmem
    have hu_W : inp.prep.J.edges[eJ].1 < wd.W.n := by rw [hw.W_n]; exact hv.1
    have hv_W : inp.prep.J.edges[eJ].2 < wd.W.n := by rw [hw.W_n]; exact hv.2
    have hcase := (mkW_jSources_spec hs hw hws heJ).2
    dsimp only [emb, initEmb2] at hP
    simp only [heJ, ↓reduceIte] at hP
    cases hsrc : wd.jSources.getD eJ JEdgeSource.isLoop with
    | isLoop =>
      rw [hsrc] at hP hcase
      simp only [Option.some.injEq] at hP
      rw [← hP]
      exact ⟨hu_W, hv_W, Or.inl ⟨rfl, rfl, hcase⟩⟩
    | inJ0 eW =>
      rw [hsrc] at hP hcase
      simp only [Option.some.injEq] at hP
      rcases hcase with ⟨_, _, heWm, hWe, _⟩
      change wd.W.edges.getD eW (0, 0) = inp.prep.J.edges[eJ] at hWe
      rw [← hP, hWe]
      refine ⟨hu_W, hv_W, Or.inr ⟨by simp [Walk.single], by simp [Walk.single], by simp [Walk.single],
        by simp [Walk.single], ?_, ?_⟩⟩
      · intro e he; simp [Walk.single] at he; subst he; exact heWm
      · intro i hi
        simp [Walk.single] at hi; subst hi
        left; simp [Walk.single]; exact ⟨congrArg Prod.fst hWe, congrArg Prod.snd hWe⟩
    | inComp ci jL =>
      rw [hsrc] at hP
      simp at hP
  have hj0_cov : ∀ eJ < inp.prep.J.m,
      (wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.isLoop ∨
        ∃ eW, wd.jSources.getD eJ JEdgeSource.isLoop = JEdgeSource.inJ0 eW) →
        (emb eJ).isSome = true := by
    intro eJ heJ h
    dsimp only [emb, initEmb2]
    simp only [heJ, ↓reduceIte]
    rcases h with h0 | ⟨eW, h0⟩ <;> rw [h0] <;> simp
  have hlen1 : ∀ eJ < inp.prep.J.m, (partialToWalk emb eJ).edges.length ≤ 1 := by
    intro eJ heJ
    dsimp only [partialToWalk, emb, initEmb2]
    simp only [heJ, ↓reduceIte]
    cases wd.jSources.getD eJ JEdgeSource.isLoop <;> simp [Walk.empty, Walk.single]
  have hlenγ : ∀ eJ < inp.prep.J.m, ↑(partialToWalk emb eJ).edges.length ≤ wd.γ_ExpPath := by
    intro eJ heJ
    have h1 : ((partialToWalk emb eJ).edges.length : ℝ) ≤ 1 := by exact_mod_cast hlen1 eJ heJ
    exact le_trans h1 hγ_ge
  have hnd : ∀ eJ < inp.prep.J.m, ∀ P, emb eJ = some P → P.edges.Nodup := by
    intro eJ heJ P hP
    dsimp only [emb, initEmb2] at hP
    simp only [heJ, ↓reduceIte] at hP
    cases hsrc : wd.jSources.getD eJ JEdgeSource.isLoop <;> rw [hsrc] at hP
    · simp only [Option.some.injEq] at hP; rw [← hP]; simp [Walk.empty]
    · simp only [Option.some.injEq] at hP; rw [← hP]; simp [Walk.single]
    · simp at hP
  have hj0_cnt : ∀ eW < wd.j0Edges.length,
      {eJ ∈ Finset.range inp.prep.J.m | eW ∈ (partialToWalk emb eJ).edges}.card ≤ 1 := by
    intro eW heW
    have hsub : {eJ ∈ Finset.range inp.prep.J.m | eW ∈ (partialToWalk emb eJ).edges} ⊆
        {wd.j0Edges.getD eW 0} := by
      intro eJ heJ_mem
      rw [Finset.mem_filter, Finset.mem_range] at heJ_mem
      rcases heJ_mem with ⟨heJm, he_in⟩
      dsimp only [partialToWalk, emb, initEmb2] at he_in
      simp only [heJm, ↓reduceIte] at he_in
      have hcase := (mkW_jSources_spec hs hw hws heJm).2
      cases hsrc : wd.jSources.getD eJ JEdgeSource.isLoop <;> rw [hsrc] at he_in hcase
      · simp [Walk.empty] at he_in
      · simp [Walk.single] at he_in
        subst he_in
        rw [Finset.mem_singleton, hcase.2.1]
      · simp [Walk.empty] at he_in
    exact (Finset.card_le_card hsub).trans (by simp)
  have hcomp_cnt : ∀ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m,
      {eJ ∈ Finset.range inp.prep.J.m | eW ∈ (partialToWalk emb eJ).edges}.card = 0 := by
    intro eW heW
    rw [Finset.mem_Ico] at heW
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro eJ heJ_mem
    rw [Finset.mem_filter, Finset.mem_range] at heJ_mem
    rcases heJ_mem with ⟨heJm, he_in⟩
    dsimp only [partialToWalk, emb, initEmb2] at he_in
    simp only [heJm, ↓reduceIte] at he_in
    have hcase := (mkW_jSources_spec hs hw hws heJm).2
    cases hsrc : wd.jSources.getD eJ JEdgeSource.isLoop <;> rw [hsrc] at he_in hcase
    · simp [Walk.empty] at he_in
    · simp [Walk.single] at he_in
      have : eW < wd.j0Edges.length := he_in ▸ hcase.1
      omega
    · simp [Walk.empty] at he_in
  have hj0_ec : ∀ eW < wd.j0Edges.length, econgAt inp.prep.J (fun _ => 1) wd.wW (partialToWalk emb) eW ≤ wd.τ₂ / 2 := by
    intro eW heW
    have heW_j0 : eW < inp.prep.j0Edges.length := heW
    have hWm := mkW_W_edges_j0 (inp := inp) (ce := ce) (pds := pds) (WSubs := WSubs) heW_j0
    have hcnt := hj0_cnt eW heW
    have hphi_pos : 0 < wd.φ_dec := hw.φ_dec_pos
    unfold econgAt
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hle1 : ({x ∈ Finset.range inp.prep.J.m | eW ∈ (partialToWalk emb x).edges}.card : ℝ) ≤ 1 := by
      exact_mod_cast hcnt
    rw [hWm.2.2]
    calc ({x ∈ Finset.range inp.prep.J.m | eW ∈ (partialToWalk emb x).edges}.card : ℝ) / wd.φ_dec
        ≤ 1 / wd.φ_dec := div_le_div_of_nonneg_right hle1 (le_of_lt hphi_pos)
      _ ≤ wd.τ₂ / 2 := hτ₂_half
  have hcomp_ec : ∀ eW ∈ Finset.Ico wd.j0Edges.length wd.W.m,
      econgAt inp.prep.J (fun _ => 1) wd.wW (partialToWalk emb) eW = 0 := by
    intro eW heW
    have h0 := hcomp_cnt eW heW
    unfold econgAt
    simp [h0]
  have hec_half : ∀ eW < wd.W.m, econgAt inp.prep.J (fun _ => 1) wd.wW (partialToWalk emb) eW ≤ (0 + 1 / 2 : ℝ) * wd.τ₂ := by
    intro eW heW
    by_cases hj : eW < wd.j0Edges.length
    · linarith [hj0_ec eW hj]
    · have hc := hcomp_ec eW (Finset.mem_Ico.mpr ⟨by omega, heW⟩)
      rw [hc]
      linarith [hw.τ₂_pos]
  exact ⟨hpart, hj0_cov, hlen1, hlenγ, hnd, hj0_cnt, hcomp_cnt, hj0_ec, hcomp_ec, hec_half⟩


end MinCostFlow.Spanner
