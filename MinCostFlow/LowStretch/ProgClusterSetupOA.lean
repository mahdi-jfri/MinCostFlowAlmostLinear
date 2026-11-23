module

public import MinCostFlow.LowStretch.ProgClusterSetupO9

/-!
# The setup of a cluster: the first invariant of the loop and the path of the target

After the setup every node is allowed (`SuFin.ok_os`), so the first invariant `LInv` of the
petal loop holds with no petal, `u = 0`, the stamp `1` and `M0 = F` (`SuFin.linv`): its parts
about petals are empty, and the tree, the cone and the remaining vertices are those of the
start (`PW.Cone.init`, `PW.Y_init`, `PW.card_init`). The path of parents of the node of `c.t`
is the path of `hwFix`, so it has `nH` steps and `c.hw` splits along it (`SuFin.path`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st} {F : ℕ → ℕ}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

namespace SuFin

variable (hf : SuFin a F) (hp : ClPre w A T G P c R GB RB h mem)
include hf hp

/-- **Every node is allowed after the setup.** -/
theorem ok_os : ∀ v < a.W.s, F (a.W.L.OK + v) = a.W.L.os := by
  rw [SuAt.W_s hp]
  intro v hv
  show F (SuN.z 𝔑 18 18 0 5 + v) = 0
  rw [hf.okc hv.le]
  exact a.suPg.ok v hv

variable (hX : 2 ≤ c.X.card)
include hX

omit hp hX in
/-- The tree arrays after the setup are those of `hwFix`. -/
theorem arr {v : ℕ} (hv : v < SuN.s 𝔑) (k : ℕ) (hk : k ≤ 5) :
    F (SuN.Z 𝔑 + k * (RecL.read mem RB).s + 1 + v) =
      a.M3 (SuN.Z 𝔑 + k * (RecL.read mem RB).s + 1 + v) := by
  have hZ := suN_hZ GB RB h mem P.L
  have vs : SuN.s 𝔑 = (RecL.read mem RB).s := rfl
  have h1 : k * (RecL.read mem RB).s ≤ 5 * (RecL.read mem RB).s := Nat.mul_le_mul_right _ hk
  rw [hf.low (by omega) (by simp only [SuN.z]; omega), a.hM.ac_fr _ (by omega)]

omit hX in
/-- **The path of the target** has `nH` steps, along the split highway. -/
theorem path : a.W.Path F (a.W.sv a.W.c.t) (RecL.read mem RB).nH ∧
    a.W.c.HwDec a.W.G a.W.c.t (a.W.stp (suTA 𝔑) F (a.W.sv a.W.c.t) (RecL.read mem RB).nH)
      a.W.c.hw := by
  have hZ := suN_hZ GB RB h mem P.L
  have hVf := hp.hfV a.hM.first hZ a.hM.tr_fr
  have hs := SuAt.W_s (a := a) hp
  have vs : SuN.s 𝔑 = (RecL.read mem RB).s := rfl
  have hcp : ∀ v < a.W.s, F (a.W.NXT + v) = a.M3 (SuN.Z 𝔑 + v) := by
    intro v hv
    rw [hs] at hv
    show F (SuN.z 𝔑 18 19 0 6 + v) = _
    rw [hf.nxt hv, a.hM.ac_fr _ (by omega)]
  have hpp : ∀ v < a.W.s, F ((suTA 𝔑).PP + v) =
      a.M3 (SuN.Z 𝔑 + (RecL.read mem RB).s + 1 + v) ∧
      F ((suTA 𝔑).PA + v) = a.M3 (SuN.Z 𝔑 + 3 * (RecL.read mem RB).s + 1 + v) ∧
      F ((suTA 𝔑).PB + v) = a.M3 (SuN.Z 𝔑 + 4 * (RecL.read mem RB).s + 1 + v) := by
    intro v hv
    rw [hs] at hv
    have e : ∀ k, SuN.z 𝔑 0 k 0 1 + v = SuN.Z 𝔑 + k * (RecL.read mem RB).s + 1 + v :=
      fun k => by simp only [SuN.z, vs, Nat.zero_mul, Nat.add_zero]
    show F (SuN.z 𝔑 0 1 0 1 + v) = _ ∧ F (SuN.z 𝔑 0 3 0 1 + v) = _ ∧
      F (SuN.z 𝔑 0 4 0 1 + v) = _
    rw [e, e, e, hf.arr hv, hf.arr hv, hf.arr hv, one_mul]
    all_goals omega
  exact ⟨(PW.path_t (W := a.W) hVf a.hM.hf hcp hpp).1, PW.path_t_dec hVf a.hM.hf hcp hpp⟩

variable (hP : P = par G.n G.m)
include hP

set_option maxHeartbeats 2000000 in
/-- **The first invariant of the loop.** -/
theorem linv (sp : Bool) (st' : State) (hm : st'.mem = F)
    (hr : ∀ i < 43, i ≠ 13 → i ≠ 32 → i ≠ 41 →
      st'.regs i = (a.W.LReg (suTA 𝔑) (suLA 𝔑) (a.W.c.Δ a.W.G)).getD i 0)
    (h13 : st'.regs 13 = 1) (h32 : st'.regs 32 = 0) (h41 : st'.regs 41 = 0) :
    a.W.LInv (suTA 𝔑) (suLA 𝔑) sp 0 F w ⟨0, 1, [], a.W.Φ F⟩ st' := by
  subst hm
  have hok := hf.ok hp hX hP
  have hos := hf.ok_os hp
  have hT := hf.tree hp hX
  have hL := a.lLay hp hX
  have wpt := hL.wpt
  have hcard := PW.card_init hok hos
  have hPO : st'.mem ((suLA 𝔑).PO + 0) = 0 := by
    show st'.mem (SuN.r 𝔑 2 13 + 0) = 0
    exact hf.zero hp (Or.inr (by simp only [SuN.r]; omega))
  exact {
    regs := hr
    r13 := h13
    r32 := h32
    r41 := h41
    k0le := le_rfl
    btw := hf.btw hp hX hP
    tree := hT
    cone := PW.Cone.init hT hos
    φ := rfl
    Y := PW.Y_init hok hos sp
    safe := fun _ _ _ => rfl
    low := fun _ _ _ _ => rfl
    scan := fun v hv => absurd hv (Nat.not_lt_zero v)
    reg := fun j _ hj => absurd hj (Nat.not_lt_zero j)
    po := fun j hj => absurd hj (Nat.not_lt_zero j)
    out := fun j hj => absurd hj (Nat.not_lt_zero j)
    room := by simp only [List.length_nil]; rw [hPO, hcard]; omega
    kle := by simp only [List.length_nil]; rw [hcard]; omega
    ule := Nat.zero_le _
    rsw := by
      have : 1 ≤ (suLA 𝔑).PT := by show 1 ≤ SuN.r 𝔑 5 16; simp only [SuN.r]; omega
      show 1 + (a.W.s - 0) < 2 ^ w
      omega }

end SuFin

end MinCostFlow.LowStretch
