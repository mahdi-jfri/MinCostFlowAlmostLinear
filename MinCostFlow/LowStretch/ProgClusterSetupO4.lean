module

public import MinCostFlow.LowStretch.ProgClusterSetupO3

/-!
# The setup of a cluster: the entries and the tables after the setup

The facts of `PW.Ok` about the active entries (`img`, `inj`, `hnact`, `hwt`, `wE`, `hwM`,
`lEXP`), the tables `SQ` and `P2` (`hsq`, `hP2`, `hSm`) and the copy `NXT` of the parents
(`nxt`), for the memory `F` after the setup. The entries name exactly the active pairs, once
each (`Rec.act_img`, `Rec.act_inj`). The halves `AS[2 j] = j` and the exponents
`EXP[j] = EXP[pr j]` give the weights `1 <<< (Es - EXP[pr j]) = 2^Es / ω` (`Rec.wt_tab`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st} {F : ℕ → ℕ}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

namespace SuAt

variable (a) (hp : ClPre w A T G P c R GB RB h mem)
include hp

/-- The stored entries in the memory after `hwFix`. -/
theorem smem : Rec.SMem T G c R a.M3 (RecL.read mem RB).SA (GlobL.read mem GB).PW
    (RecL.read mem RB).nS := by
  have hb := hp.below
  have bSA := hb ((RecL.read mem RB).SA, 2 * (RecL.read mem RB).nS)
    (by simp [recRegs, RecL.regs])
  have bPW := hb ((GlobL.read mem GB).PW, (GlobL.read mem GB).m) (by simp [recRegs])
  have hm' : (GlobL.read mem GB).m = G.m := hp.glob.m
  dsimp only at bSA bPW
  have hAr := hp.recAt.arcs
  have hnS : (RecL.read mem RB).nS = R.S.length := hAr.nS
  exact ⟨hnS, fun j hj => by
    rw [a.hM.low3 (by omega)]; exact hAr.pr j hj,
    fun p hp' => by rw [a.hM.low3 (by omega)]; exact hAr.pw p hp'⟩

/-- The pair of entry `j` is the pair of the kept entry `j`. -/
theorem pr_eq {j : ℕ} (hj : j < a.hM.nA) :
    a.W.pr j = Rec.apr a.M3 (RecL.read mem RB).SA (GlobL.read mem GB).PW
      ((suVOf GB RB h mem).QD (c.Δ G)) (RecL.read mem RB).nS j :=
  (hp.actEnt a.hM hj).2

/-- The pair of entry `j` is a pair of the graph, and its exponent is a word. -/
theorem pr_lt {j : ℕ} (hj : j < a.hM.nA) : a.W.pr j < G.m :=
  (hp.actEnt a.hM hj).1.lt

/-- **The entries name the active pairs.** -/
theorem img (hP : P = par G.n G.m) :
    (Finset.range a.W.nA).image a.W.pr = a.W.c.act a.W.G a.W.P := by
  have hQD : (suVOf GB RB h mem).QD (c.Δ G) = P.Q * (c.Δ G * c.θ) := by
    rw [hp.QD_eq]
    have hB : P.B = pB G.n := by rw [hP]; rfl
    have hQ : P.Q = 512 * pB G.n * G.n ^ 2 := by rw [hP]; rfl
    rw [hB, hQ]; ring
  have h1 := Rec.act_img hp.ok (a.smem hp) hQD
  show (Finset.range a.hM.nA).image a.W.pr = c.act G P
  rw [← h1]
  exact Finset.image_congr fun j hj => a.pr_eq hp (Finset.mem_range.mp hj)

/-- **The entries name distinct pairs.** -/
theorem inj : Set.InjOn a.W.pr ↑(Finset.range a.W.nA) := by
  have h1 := Rec.act_inj (QD := (suVOf GB RB h mem).QD (c.Δ G)) hp.ok (a.smem hp)
  intro j hj j' hj' he
  have hj1 : j < a.hM.nA := Finset.mem_range.mp (Finset.mem_coe.mp hj)
  have hj2 : j' < a.hM.nA := Finset.mem_range.mp (Finset.mem_coe.mp hj')
  rw [a.pr_eq hp hj1, a.pr_eq hp hj2] at he
  exact h1 hj hj' he

theorem hnact (hP : P = par G.n G.m) : a.W.nact = (a.W.c.act a.W.G a.W.P).card := by
  rw [← a.img hp hP, Finset.card_image_of_injOn (a.inj hp), Finset.card_range]; rfl

/-- The exponent of the pair of entry `j`, read through the copies. -/
theorem exp_eq {j : ℕ} (hj : j < a.hM.nA) :
    a.M4 ((suVOf GB RB h mem).EXP + a.M4 (SuN.z 𝔑 0 8 0 2 + 2 * j)) =
      mem ((GlobL.read mem GB).EXP + a.W.pr j) := by
  have hb := hp.below
  have bEX := hb ((GlobL.read mem GB).EXP, (GlobL.read mem GB).m) (by simp [recRegs])
  have hm' : (GlobL.read mem GB).m = G.m := hp.glob.m
  dsimp only at bEX
  have := a.pr_lt hp hj
  have e : a.W.pr j = a.M4 (SuN.z 𝔑 0 8 0 2 + 2 * j) := rfl
  rw [← e]
  exact a.hM.low_h (show (GlobL.read mem GB).EXP + a.W.pr j < h + 51 by omega)

/-- The exponent bound: `V.EXP + pr j` lies below the graph of `pgP`. -/
theorem exp_lt {j : ℕ} (hj : j < a.hM.nA) :
    (suVOf GB RB h mem).EXP + a.M4 (SuN.z 𝔑 0 8 0 2 + 2 * j) < SuN.z 𝔑 2 8 0 2 := by
  have hb := hp.below
  have bEX := hb ((GlobL.read mem GB).EXP, (GlobL.read mem GB).m) (by simp [recRegs])
  have hm' : (GlobL.read mem GB).m = G.m := hp.glob.m
  dsimp only at bEX
  have := a.pr_lt hp hj
  have e : a.W.pr j = a.M4 (SuN.z 𝔑 0 8 0 2 + 2 * j) := rfl
  have hZ := suN_hZ GB RB h mem P.L
  rw [← e]
  show (GlobL.read mem GB).EXP + _ < _
  simp only [SuN.z]; omega

/-- The largest exponent bounds the exponent of every entry. -/
theorem es_ge' {j : ℕ} (hj : j < a.hM.nA) : mem ((GlobL.read mem GB).EXP + a.W.pr j) ≤ a.Es := by
  have h1 := a.es_ge j hj
  have := SuAt.nA_le (a := a)
  rw [a.t4 j hj, a.n3_low (x := SuN.z 𝔑 0 8 0 2 + 2 * j) (by simp only [SuN.z]; omega),
    a.n3_low (a.exp_lt hp hj), a.exp_eq hp hj] at h1
  exact h1

/-- **The weights of the entries**: `wtP p · ω(p) = 2^Es` for every active pair. -/
theorem hwM (hP : P = par G.n G.m) :
    ∀ p ∈ a.W.c.act a.W.G a.W.P, a.W.wtP p * a.W.G.pω p = a.W.M := by
  intro p hp'
  rw [← a.img hp hP] at hp'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp'
  have hj' : j < a.hM.nA := Finset.mem_range.mp hj
  obtain ⟨e1, e2⟩ := Rec.wt_tab (G := G) (nA := a.hM.nA) (Es := a.Es) (pr := a.W.pr)
    (e := fun j => mem ((GlobL.read mem GB).EXP + a.W.pr j)) (fun j hj => a.es_ge' hp hj)
    (fun j hj => (hp.actEnt a.hM hj).1.ex) hj'
  show 1 <<< (a.Es - mem ((suVOf GB RB h mem).EXP + a.W.pr j)) * G.pω (a.W.pr j) = 2 ^ a.Es
  rw [show (suVOf GB RB h mem).EXP = (GlobL.read mem GB).EXP from rfl, e1, e2]

end SuAt

namespace SuFin

variable (hf : SuFin a F) (hp : ClPre w A T G P c R GB RB h mem)
include hf hp

omit hp in
theorem as2 {j : ℕ} (hj : j < a.W.nA) : F (a.W.AS + 2 * j) = j := by
  show F (SuN.z 𝔑 20 21 0 7 + 2 * j) = j
  rw [hf.as (show 2 * j < 2 * a.hM.nA by have : j < a.hM.nA := hj; omega)]; omega

theorem expj {j : ℕ} (hj : j < a.W.nA) :
    F (a.W.EXP + F (a.W.AS + 2 * j)) = mem ((GlobL.read mem GB).EXP + a.W.pr j) := by
  rw [hf.as2 hj]
  show F (SuN.z 𝔑 22 21 0 7 + j) = _
  rw [hf.exp hj (a.exp_lt hp hj), a.exp_eq hp hj]

theorem hwt : ∀ j < a.W.nA,
    1 <<< (a.W.Es - F (a.W.EXP + F (a.W.AS + 2 * j))) = a.W.wtP (a.W.pr j) := by
  intro j hj
  rw [hf.expj hp hj]; rfl

theorem wE (hX : 2 ≤ c.X.card) : ∀ j < a.W.nA, F (a.W.EXP + F (a.W.AS + 2 * j)) < 2 ^ w := by
  intro j hj
  rw [hf.expj hp hj]
  have := (hp.pw_words hX _ (a.pr_lt hp hj)).2
  omega

omit hp in
theorem lEXP : ∀ j < a.W.nA, a.W.EXP + F (a.W.AS + 2 * j) < a.W.SQ := by
  intro j hj
  rw [hf.as2 hj]
  have : j < a.hM.nA := hj
  have := SuAt.nA_le (a := a)
  show SuN.z 𝔑 22 21 0 7 + j < SuN.z 𝔑 23 21 0 7
  simp only [SuN.z]; omega

omit hp in
theorem hsq : ∀ q, 1 ≤ q → q ≤ a.W.Lb → F (a.W.SQ + q) = a.W.c.sq a.W.G a.W.P q := by
  intro q _ hq
  have hq' : q ≤ P.L := hq
  show F (SuN.z 𝔑 23 21 0 7 + q) = _
  rw [hf.sq (by omega)]; rfl

omit hp in
theorem hP2 : ∀ q, 1 ≤ q → q ≤ a.W.Lb → F (a.W.P2 + q) = 2 ^ Cl.lam a.W.P q := by
  intro q _ hq
  have hq' : q ≤ P.L := hq
  show F (SuN.z 𝔑 23 21 1 9 + q) = _
  rw [hf.p2 (by omega)]; rfl

omit hp in
theorem hSm : ∀ q ≤ a.W.Lb + 1, F (a.W.SQ + q) ≤ a.W.Sm ∧ F (a.W.P2 + q) ≤ a.W.Sm := by
  intro q hq
  have hq' : q ≤ P.L + 1 := hq
  show F (SuN.z 𝔑 23 21 0 7 + q) ≤ 2 ^ 2 ^ P.L + c.Δ G ∧
    F (SuN.z 𝔑 23 21 1 9 + q) ≤ 2 ^ 2 ^ P.L + c.Δ G
  rw [hf.sq (by omega), hf.p2 (by omega)]
  have h1 : c.Δ G / 8 / P.L / (2 ^ (P.L - (q - 1)) + 3) ≤ c.Δ G :=
    (Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans (Nat.div_le_self _ _))
  have h2 : 2 ^ 2 ^ (P.L - q) ≤ 2 ^ 2 ^ P.L :=
    Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact ⟨h1.trans (Nat.le_add_left _ _), h2.trans (Nat.le_add_right _ _)⟩

/-- The copy `NXT` holds nodes. -/
theorem nxt' (hX : 2 ≤ c.X.card) : ∀ v < a.W.L.NN, F (a.W.NXT + v) < a.W.L.NN := by
  intro v hv
  have hv' : v < SuN.s 𝔑 + 1 := hv
  show F (SuN.z 𝔑 18 19 0 6 + v) < SuN.s 𝔑 + 1
  rcases Nat.lt_or_ge v (SuN.s 𝔑) with h1 | h1
  · rw [hf.nxt h1]
    have hT := a.hM.ptree hp hX
    by_cases hr : v = R.sv T c c.x0
    · rw [hr, hT.root]
      show (RecL.read mem RB).s < SuN.s 𝔑 + 1
      exact Nat.lt_succ_self _
    · exact lt_trans (hT.edge v h1 hr).1 (Nat.lt_succ_self _)
  · rw [show v = SuN.s 𝔑 by omega, hf.nxt_s hp]; omega

end SuFin

end MinCostFlow.LowStretch
