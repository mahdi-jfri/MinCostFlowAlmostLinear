module

public import MinCostFlow.Spanner.PathDSContract
public import MinCostFlow.HierPaths.Params

public import MinCostFlow.HierPaths.ParamsExp

/-!
# The parameters of the path data structure built from the hierarchy

The hierarchy of embedded matchings gives the bounds
`φ_out = 1/Γ`, `γ_del = 1` and `γ_path = γ_time = Γ`, with `Γ = gammaHP a d M` and
`d = ⌈1/φ_in⌉`. This file packs them as a `Spanner.PathDSParams` (`hierParams`), with
`phiOutDen = gExp = gQuery = Γ` and `gDel = 1`.

The RAM constants `K_init`, `K_del`, `K_query`, `K_bounds`, the word constant `cw` and the space
functions come from the programs of the operations. They are arguments here, together with the
side conditions the fields of `PathDSParams` ask of them. The fields about `Γ` are proved from
`gammaHP_mono`, `max_two_le_gammaHP` and the polynomial bound `gammaHP_le_poly`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Spanner

/-- The `PathDSParams` of the hierarchy: `phiOutDen = gExp = gQuery = Γ` and `gDel = 1`. -/
def hierParams (a : ℕ) (K_init K_del K_query : ℝ) (hK_init : 0 ≤ K_init) (hK_del : 0 ≤ K_del)
    (hK_query : 0 ≤ K_query) (K_bounds cw : ℕ) (hcw_pos : 1 ≤ cw)
    (boundsSpace : ℕ → ℕ → ℕ) (initSpace delSpace querySpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (C_space c_space : ℕ) (hC_space : 1 ≤ C_space)
    (hboundsSpace_le : ∀ d M, boundsSpace d M ≤ C_space * (d + M + 2) ^ c_space)
    (hinitSpace_le : ∀ phiNum phiDen n m M, 1 ≤ phiNum → phiNum ≤ phiDen →
      initSpace phiNum phiDen n m M ≤
        C_space * (phiDen + n + m + M + gammaHP a ((phiDen + phiNum - 1) / phiNum) M + 2) ^ c_space)
    (hdelSpace_le : ∀ phiNum phiDen n m M, 1 ≤ phiNum → phiNum ≤ phiDen →
      delSpace phiNum phiDen n m M ≤
        C_space * (phiDen + n + m + M + gammaHP a ((phiDen + phiNum - 1) / phiNum) M + 2) ^ c_space)
    (hquerySpace_le : ∀ phiNum phiDen n m M, 1 ≤ phiNum → phiNum ≤ phiDen →
      querySpace phiNum phiDen n m M ≤
        C_space * (phiDen + n + m + M + gammaHP a ((phiDen + phiNum - 1) / phiNum) M + 2) ^ c_space) :
    PathDSParams where
  phiOutDen := gammaHP a
  gExp := gammaHP a
  gDel _ _ := 1
  gQuery := gammaHP a
  hphiOutDen_ge d M _ := max_two_le_gammaHP a d M
  hgExp_ge _ _ _ := le_rfl
  hgDel_ge _ _ _ := le_rfl
  hphiOutDen_mono _ _ _ _ _ hd hM := gammaHP_mono a hd hM
  hgExp_mono _ _ _ _ _ hd hM := gammaHP_mono a hd hM
  hgDel_mono _ _ _ _ _ _ _ := le_rfl
  hgQuery_ge _ _ _ := le_rfl
  hgQuery_mono _ _ _ _ _ hd hM := gammaHP_mono a hd hM
  hpoly := ⟨2 ^ 28, 810 * a + 58, fun d M _ =>
    ⟨gammaHP_le_poly a d M, by
      have : 1 ≤ (d + M + 2) ^ (810 * a + 58) := Nat.one_le_pow _ _ (by omega)
      calc 1 ≤ 2 ^ 28 * 1 := by norm_num
        _ ≤ 2 ^ 28 * (d + M + 2) ^ (810 * a + 58) := Nat.mul_le_mul_left _ this⟩⟩
  K_init := K_init
  K_del := K_del
  K_query := K_query
  hK_init := hK_init
  hK_del := hK_del
  hK_query := hK_query
  K_bounds := K_bounds
  cw := cw
  hcw_pos := hcw_pos
  boundsSpace := boundsSpace
  initSpace := initSpace
  delSpace := delSpace
  querySpace := querySpace
  C_space := C_space
  c_space := c_space
  hC_space := hC_space
  hboundsSpace_le := hboundsSpace_le
  hinitSpace_le := hinitSpace_le
  hdelSpace_le := hdelSpace_le
  hquerySpace_le := hquerySpace_le

/-- The output conductance of `hierParams` is `1/Γ`, at `d = ⌈1/φ_in⌉`. -/
lemma hierParams_φ_out (a : ℕ) {K_init K_del K_query : ℝ} {hK_init : 0 ≤ K_init}
    {hK_del : 0 ≤ K_del} {hK_query : 0 ≤ K_query} {K_bounds cw : ℕ} {hcw_pos : 1 ≤ cw}
    {boundsSpace : ℕ → ℕ → ℕ} {initSpace delSpace querySpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {C_space c_space : ℕ} {hC_space : 1 ≤ C_space} {hb hi hd hq} (φ_in : ℝ) (M : ℕ) :
    (hierParams a K_init K_del K_query hK_init hK_del hK_query K_bounds cw hcw_pos boundsSpace
      initSpace delSpace querySpace C_space c_space hC_space hb hi hd hq).φ_out φ_in M =
      1 / (gammaHP a (Nat.ceil (1 / φ_in)) M : ℝ) := rfl

/-- The deletion factor of `hierParams` is `1`. -/
lemma hierParams_γ_del (a : ℕ) {K_init K_del K_query : ℝ} {hK_init : 0 ≤ K_init}
    {hK_del : 0 ≤ K_del} {hK_query : 0 ≤ K_query} {K_bounds cw : ℕ} {hcw_pos : 1 ≤ cw}
    {boundsSpace : ℕ → ℕ → ℕ} {initSpace delSpace querySpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    {C_space c_space : ℕ} {hC_space : 1 ≤ C_space} {hb hi hd hq} (φ_in : ℝ) (M : ℕ) :
    (hierParams a K_init K_del K_query hK_init hK_del hK_query K_bounds cw hcw_pos boundsSpace
      initSpace delSpace querySpace C_space c_space hC_space hb hi hd hq).γ_del φ_in M = 1 := by
  simp [PathDSParams.γ_del, hierParams]

/-- The side conditions of `hierParams` can hold at once: zero constants and zero space. -/
example : PathDSParams :=
  hierParams 1 0 0 0 le_rfl le_rfl le_rfl 0 1 le_rfl (fun _ _ => 0) (fun _ _ _ _ _ => 0)
    (fun _ _ _ _ _ => 0) (fun _ _ _ _ _ => 0) 1 0 le_rfl (fun _ _ => Nat.zero_le _)
    (fun _ _ _ _ _ _ _ => Nat.zero_le _) (fun _ _ _ _ _ _ _ => Nat.zero_le _)
    (fun _ _ _ _ _ _ _ => Nat.zero_le _)

end MinCostFlow.HierPaths
