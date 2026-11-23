module

public import MinCostFlow.LowStretch.ProgClusterSetupO6

/-!
# The setup of a cluster: the setting of the petal searches

After the stores of the block, the memory `F` meets `PW.Ok` for the setting `a.W` (`SuFin.ok`),
and the word facts `LW` hold (`SuAt.lw`). The facts come from the files before this one: the
graph of `pgP` (`ProgClusterSetupO2`, `ProgClusterSetupO3`), the entries and the tables
(`ProgClusterSetupO4`), the layout (`ProgClusterSetupO5`) and the words (`ProgClusterSetupO6`,
and `SuAt.wT1` for the product `wT1`, which needs the room `SuRoom3`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st} {F : ℕ → ℕ}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

/-- `Δ ≥ 1`, as `8 L (λ₀ + 3) ≤ Δ`. -/
theorem ClPre.Δ_pos (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
    (hP : P = par G.n G.m) : 1 ≤ c.Δ G := by
  have hΔ := setup_hΔ hp.ok hP hX
  have : 1 ≤ P.L := by rw [hp.L_eq]; have := log_pa_le G.n; omega
  have : 1 ≤ 8 * P.L * (Cl.lam P 0 + 3) :=
    (show 1 ≤ 8 * P.L by omega).trans (Nat.le_mul_of_pos_right _ (by omega))
  omega

namespace SuAt

variable (a) (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
  (hP : P = par G.n G.m)
include hp hX hP

omit hX in
theorem κ_eq : a.W.κ = P.κ := by
  show (GlobL.read mem GB).m / ((GlobL.read mem GB).n * (GlobL.read mem GB).n) + 1 = P.κ
  rw [hp.glob.m, hp.glob.n, hP]
  simp [par, pκ, pow_two]

/-- `Sm` is at most `wT2`. -/
theorem wSm : a.W.Sm < 2 ^ w := by
  have h2 := (a.wU_wT2 hp hX).2
  have hM : 1 ≤ a.W.M := Nat.one_le_two_pow
  have hκ : 1 ≤ a.W.κ := by rw [a.κ_eq hp hP, hP]; simp [par, pκ]
  have h1 : a.W.Sm ≤ a.W.κ * a.W.Sm := Nat.le_mul_of_pos_left _ hκ
  have h3 : 4 * (a.W.κ + a.W.nact) + a.W.κ * a.W.Sm ≤
      8 * a.W.M * (4 * (a.W.κ + a.W.nact) + a.W.κ * a.W.Sm) :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

end SuAt

namespace SuFin

variable (hf : SuFin a F) (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
  (hP : P = par G.n G.m)
include hf hp hX hP

set_option maxHeartbeats 2000000 in
/-- **The setting of the petal searches holds after the setup.** -/
theorem ok : a.W.Ok w F := by
  have hs := SuAt.W_s (a := a) hp
  have hnA := SuAt.nA_le (a := a)
  have hL1 : 1 ≤ P.L := by rw [hp.L_eq]; have := log_pa_le G.n; omega
  have hΔ1 := hp.Δ_pos hX hP
  obtain ⟨E', hE', -, -, -, -, hI, -⟩ := hp.drawPre hX
  obtain rfl := DWE.eq_of_args hE'
  have hΔI : c.Δ G < (GlobL.read mem GB).INF := hI
  obtain ⟨wU, wT2⟩ := a.wU_wT2 hp hX
  have hcw : ∀ p, P.cw p = 1 := by subst hP; intro p; rfl
  have hκ1 : 1 ≤ P.κ := by subst hP; simp [par, pκ]
  exact {
    hrec := hp.ok
    conn := hp.ok.inv.good.conn
    hNN := by rw [hs]; rfl
    sS := hf.sS hp
    lohi := hf.lohi hp
    chain := SuFin.chain (a := a) (F := F)
    hiMM := hf.hiMM
    lay := a.lay
    lEXP := hf.lEXP
    lES := a.lES
    hR := a.hRR
    hCTL := a.hCTL
    hSUM := a.hSUM
    hSL := a.hSL
    wSL := a.wSL hp hX
    heads := hf.heads hp hX (SuAt.heads_w hp hX)
    classes := hf.classes hp hX
    budget := hf.budget hp (by show _ ≤ SuN.A2 𝔑; unfold SuN.A2; omega)
    fits := a.fits hp hX
    os_lt := by
      show 0 + 1 < 2 ^ w
      have := hp.room_h; have : 2 < 2 ^ 24 := by norm_num
      omega
    INF_pos := by show 0 < (GlobL.read mem GB).INF; omega
    arcsN := hf.arcsN hp
    hdNN := hf.hdNN
    hdN := hf.hdN hp
    ordA := hf.ordA hp
    hsum := hf.hsum hp
    img := a.img hp hP
    inj := a.inj hp
    hwt := hf.hwt hp
    wE := hf.wE hp hX
    hwM := a.hwM hp hP
    wU := wU
    wR2 := a.wR2 hp hX
    wL := a.wL hp hX
    wSm := a.wSm hp hX hP
    wSQ := a.wSQ hp hX
    wP2 := a.wP2 hp hX
    wNXT := a.wNXT hp hX
    nxt := hf.nxt' hp hX
    hSm := hf.hSm
    wT2 := wT2
    hM := Nat.one_le_two_pow
    hLb := rfl
    hbw := rfl
    hκ := a.κ_eq hp hP
    hnact := a.hnact hp hP
    hsq := hf.hsq
    hP2 := hf.hP2
    hcw := hcw
    hκ1 := hκ1
    hL1 := hL1
    hΔ := setup_hΔ hp.ok hP hX
    hV := setup_hV hp.ok hP hX
    hRm2 := by show 2 * c.Δ G - 1 < 2 * c.Δ G; omega }

end SuFin

end MinCostFlow.LowStretch
