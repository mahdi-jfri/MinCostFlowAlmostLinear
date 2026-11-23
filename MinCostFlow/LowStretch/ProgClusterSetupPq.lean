module

public import MinCostFlow.LowStretch.ProgClusterSetupPp

/-!
# The setup of a cluster: the precondition of `pgP`

After `drawP`, `treeP`, `hwFix` and `actP`, the memory meets the precondition of `pgP` for the
setting `suPGA` (`ClPre.pgPre`). The memories after these four calls are collected in `SuMem`.

The entries that `pgP` reads are the active entries copied by `actP`. Each one names a stored pair
whose ends lie in the cluster, so its two nodes are below `s`. The distances `FD` of the first
run are at most `Δ`. The shifted lengths are at most `Δ + ω`, where `ω ≤ 128 B n² θ` because
`ω² ≤ Q Δ θ` and `Δ ≤ 32 B n² θ`. Since `128 B n² < 2^J`, twice a shifted length is below
`2^(lθ + J + 2)`, which is the bound of `pfill` for `Jc = J + 3` classes. The slots of the nodes
have class below `J` and cost at most `Δ` (`Rec.slot_bd`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

/-- The memories of the setup: `M` after `drawP`, `M2` after `treeP`, `M3` after `hwFix` and
`M4` after `actP`, with what each call gives and the cells it keeps. -/
structure SuMem (w : ℕ) (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (GB RB h : ℕ)
    (mem M M2 M3 M4 : ℕ → ℕ) : Prop where
  first : Rec.First w T G c R (suVOf GB RB h mem).dwE mem M
  tr : ((suVOf GB RB h mem).dwE.tf ((suVOf GB RB h mem).N P.L).Z).Done M M2
    (RecL.read mem RB).s
  tr_s : M2 (((suVOf GB RB h mem).N P.L).Z + (RecL.read mem RB).s) = (RecL.read mem RB).s
  tr_fr : ∀ a, ¬ ((suVOf GB RB h mem).dwE.tf ((suVOf GB RB h mem).N P.L).Z).Out a → M2 a = M a
  hf : ((suVOf GB RB h mem).dwE.hfx ((suVOf GB RB h mem).N P.L).Z (RecL.read mem RB).nH
    (RecL.read mem RB).HW).Done M2 M3 (RecL.read mem RB).nH
  hf_fr : ∀ a, ((suVOf GB RB h mem).dwE.hfx ((suVOf GB RB h mem).N P.L).Z (RecL.read mem RB).nH
    (RecL.read mem RB).HW).Free M2 (RecL.read mem RB).nH a → M3 a = M2 a
  ac : ActDone M3 M4 (RecL.read mem RB).SA
    (((suVOf GB RB h mem).N P.L).Z + 8 * (RecL.read mem RB).s + 2)
    (selL M3 (RecL.read mem RB).SA (GlobL.read mem GB).PW ((suVOf GB RB h mem).QD (c.Δ G))
      (RecL.read mem RB).nS)
  ac_fr : ∀ a, ¬ (((suVOf GB RB h mem).N P.L).Z + 8 * (RecL.read mem RB).s + 2 ≤ a ∧
    a < ((suVOf GB RB h mem).N P.L).Z + 8 * (RecL.read mem RB).s + 2 +
      2 * (RecL.read mem RB).nS) → M4 a = M3 a

namespace SuMem

variable {M M2 M3 M4 : ℕ → ℕ}

/-- The number of active entries. -/
noncomputable def nA (_ : SuMem w T G P c R GB RB h mem M M2 M3 M4) : ℕ :=
  (selL M3 (RecL.read mem RB).SA (GlobL.read mem GB).PW ((suVOf GB RB h mem).QD (c.Δ G))
    (RecL.read mem RB).nS).length

/-- `hwFix` writes no cell below `Z`. -/
theorem free_lt (hM : SuMem w T G P c R GB RB h mem M M2 M3 M4) {a : ℕ}
    (ha : a < ((suVOf GB RB h mem).N P.L).Z) :
    ((suVOf GB RB h mem).dwE.hfx ((suVOf GB RB h mem).N P.L).Z (RecL.read mem RB).nH
      (RecL.read mem RB).HW).Free M2 (RecL.read mem RB).nH a := fun j _ => by
  simp only [DWE.hfx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Below `Z`, the memory after `actP` is the memory after `drawP`. -/
theorem low_Z (hM : SuMem w T G P c R GB RB h mem M M2 M3 M4) {a : ℕ}
    (ha : a < ((suVOf GB RB h mem).N P.L).Z) : M4 a = M a := by
  rw [hM.ac_fr a (fun h' => by omega), hM.hf_fr a (hM.free_lt ha),
    hM.tr_fr a (fun ho => by have := ho.1; simp only [DWE.tf] at this; omega)]

/-- Below `h + 51`, the memory after `actP` is the memory at the start. -/
theorem low_h (hM : SuMem w T G P c R GB RB h mem M M2 M3 M4) {a : ℕ} (ha : a < h + 51) :
    M4 a = mem a := by
  have hZ : h + 51 ≤ ((suVOf GB RB h mem).N P.L).Z := by
    simp only [SuN.Z, SuN.H, SuV.N, suVOf]; omega
  rw [hM.low_Z (by omega)]
  exact hM.first.low ha

/-- The memory after `hwFix` below `h + 51`. -/
theorem low3 (hM : SuMem w T G P c R GB RB h mem M M2 M3 M4) {a : ℕ} (ha : a < h + 51) :
    M3 a = mem a := by
  have hZ : h + 51 ≤ ((suVOf GB RB h mem).N P.L).Z := by
    simp only [SuN.Z, SuN.H, SuV.N, suVOf]; omega
  exact ClPre.low3 hM.first hZ hM.tr_fr hM.hf_fr a ha

/-- The parents `PCI[u] = u` that `treeP` writes are still there after `actP`. -/
theorem pci (hM : SuMem w T G P c R GB RB h mem M M2 M3 M4)
    (hp : ClPre w A T G P c R GB RB h mem) {u : ℕ} (hu : u < (RecL.read mem RB).s) :
    M4 (((suVOf GB RB h mem).N P.L).Z + 7 * (RecL.read mem RB).s + 1 + u) = u := by
  have hZ : h + 51 ≤ ((suVOf GB RB h mem).N P.L).Z := by
    simp only [SuN.Z, SuN.H, SuV.N, suVOf]; omega
  have hVf := hp.hfV hM.first hZ hM.tr_fr
  have hs : (RecL.read mem RB).s = R.nodes.length := hp.recAt.arcs.s
  have hnu : ∀ j < (RecL.read mem RB).nH, ((suVOf GB RB h mem).dwE.hfx
      ((suVOf GB RB h mem).N P.L).Z (RecL.read mem RB).nH (RecL.read mem RB).HW).nu M2 j <
      (RecL.read mem RB).s := fun j hj => by
    rw [hVf.nu_eq hj, hs]; exact hVf.ok.sv_lt (hVf.step hj).2.1
  have ds : (suVOf GB RB h mem).dwE.s = (RecL.read mem RB).s := rfl
  rw [hM.ac_fr _ (by omega), hM.hf_fr _ (fun j hj => by
    have := hnu j hj
    generalize ((suVOf GB RB h mem).dwE.hfx ((suVOf GB RB h mem).N P.L).Z (RecL.read mem RB).nH
      (RecL.read mem RB).HW).nu M2 j = x at *
    simp only [DWE.hfx]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)]
  exact (hM.tr u hu).2.2.2.2.2.2.2

/-- **The slots after `actP`**: the class of the slot of `k` is below `J` and its cost is at most
`Δ` (`Rec.slot_bd`). -/
theorem slot (hM : SuMem w T G P c R GB RB h mem M M2 M3 M4)
    (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) {k : ℕ}
    (hk : k < (RecL.read mem RB).s) :
    M4 (((suVOf GB RB h mem).N P.L).Z + 6 * (RecL.read mem RB).s + 1 + k) <
        (GlobL.read mem GB).J ∧
      M4 (((suVOf GB RB h mem).N P.L).Z + 5 * (RecL.read mem RB).s + 1 + k) ≤ c.Δ G := by
  have hZ : h + 51 ≤ ((suVOf GB RB h mem).N P.L).Z := by
    simp only [SuN.Z, SuN.H, SuV.N, suVOf]; omega
  have hVf := hp.hfV hM.first hZ hM.tr_fr
  obtain ⟨E', hE', -, -, hAP, -, -, -, -, -, -, -, -, -, -⟩ := hp.drawPre hX
  obtain rfl := DWE.eq_of_args hE'
  obtain ⟨hDΔ, hD4, -⟩ := hp.D_facts
  have hθ : c.θ = 2 ^ (RecL.read mem RB).lθ := hp.recAt.arcs.th
  have hb := hp.below
  have bSA := hb ((RecL.read mem RB).SA, 2 * (RecL.read mem RB).nS)
    (by simp [recRegs, RecL.regs])
  dsimp only at bSA
  have hJ0 : 128 * P.B * G.n ^ 2 < 2 ^ (GlobL.read mem GB).J := hp.glob.hJ
  have hB1 : 1 ≤ P.B := hp.ok.hB
  have hn1 : 1 ≤ G.n := hp.ok.n_pos hX
  have hJ1 : 1 ≤ (GlobL.read mem GB).J := by
    by_contra h0
    have e : (GlobL.read mem GB).J = 0 := by omega
    rw [e, pow_zero] at hJ0
    have : 0 < P.B * G.n ^ 2 := Nat.mul_pos (by omega) (pow_pos (by omega) 2)
    have e2 : 128 * P.B * G.n ^ 2 = 128 * (P.B * G.n ^ 2) := by ring
    omega
  have h4 : 4 * c.Δ G < 2 ^ ((suVOf GB RB h mem).dwE.lθ + (GlobL.read mem GB).J) := by
    rw [add_comm]; show _ < 2 ^ ((GlobL.read mem GB).J + (RecL.read mem RB).lθ); omega
  have hsb := Rec.slot_bd hM.first hAP
    (show (RecL.read mem RB).SA + 2 * (RecL.read mem RB).nS ≤ h + 51 by omega) _ _ _ hVf hM.tr
    hM.hf hM.hf_fr hJ1 h4 hθ hk
  rw [hM.ac_fr _ (by omega), hM.ac_fr _ (by omega)]
  exact hsb

end SuMem

set_option maxHeartbeats 8000000 in
/-- **The precondition of `pgP`** after `actP`, with `NL = N` labels, `NS = s` nodes and `MM = s`
parent arcs. -/
theorem ClPre.pgPre (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
    {M M2 M3 M4 : ℕ → ℕ} (hM : SuMem w T G P c R GB RB h mem M M2 M3 M4) :
    (suPGA (suVOf GB RB h mem) P.L hM.nA).Pre w M4 G.m G.n T.N (RecL.read mem RB).s
      (RecL.read mem RB).s := by
  have hS := hp.hS_lt hX
  have hW := hp.words hX
  have hWh := hp.words_hi hX
  obtain ⟨hDΔ, hD4, -⟩ := hp.D_facts
  have hF := hM.first
  obtain ⟨E', hE', -, -, hAP, -, -, -, -, -, hx0s, -, -, -, -⟩ := hp.drawPre hX
  obtain rfl := DWE.eq_of_args hE'
  set V := suVOf GB RB h mem with hV
  set N := V.N P.L with hN
  set Lr := RecL.read mem RB with hLr
  set Eg := GlobL.read mem GB with hEg
  have hb : ∀ r ∈ recRegs GB RB Eg Lr, r.1 + r.2 ≤ h := hp.below
  have bSA := hb (Lr.SA, 2 * Lr.nS) (by simp [recRegs, RecL.regs])
  have bIN := hb (Eg.IN, 3 * Eg.m) (by simp [recRegs])
  have bPW := hb (Eg.PW, Eg.m) (by simp [recRegs])
  dsimp only at bSA bIN bPW
  have hm' : Eg.m = G.m := hp.glob.m
  have hlab : Eg.LAB + G.n ≤ h := hp.lab_below
  have hloc : Eg.LOC + T.N ≤ h := hp.loc_below
  have hAr := hp.recAt.arcs
  have hnS : Lr.nS = R.S.length := hAr.nS
  have hs : Lr.s = R.nodes.length := hAr.s
  have hθ : c.θ = 2 ^ Lr.lθ := hAr.th
  have hθ1 := hp.ok.inv.one_le
  have hJ0 : 128 * P.B * G.n ^ 2 < 2 ^ Eg.J := hp.glob.hJ
  have hINF : c.Δ G < Eg.INF := hF.hINF
  -- the numbers of the layout
  have vs : N.s = Lr.s := rfl
  have vnS : N.nS = Lr.nS := rfl
  have vh : N.h = h := rfl
  have vJ : N.J = Eg.J := rfl
  have vL : N.L = P.L := rfl
  have wh : V.h = h := rfl
  have ws : V.s = Lr.s := rfl
  have wnS : V.nS = Lr.nS := rfl
  have wJ : V.J = Eg.J := rfl
  have wIN : V.IN = Eg.IN := rfl
  have wPW : V.PW = Eg.PW := rfl
  have wLAB : V.LAB = Eg.LAB := rfl
  have wLOC : V.LOC = Eg.LOC := rfl
  have eZ : N.Z = N.h + 51 + 16 * N.nS + 8 * N.s + 14 + 4 * N.J +
      2 * N.J * (2 * N.nS + N.s + 1) := rfl
  have hzS := N.z_le_hS (a := 18) (b := 19) (c := 0) (k := 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have ez : ∀ a b c k, N.z a b c k = N.Z + a * N.nS + b * N.s + c * N.L + k :=
    fun _ _ _ _ => rfl
  have hzb := ez 18 19 0 8
  have hnA : hM.nA ≤ Lr.nS := selL_length_le _ _ _ _ _
  have hHZ : h + 51 ≤ N.Z := by omega
  have lowZ : ∀ a < N.Z, M4 a = M a := fun a ha => hM.low_Z ha
  set sel := selL M3 Lr.SA Eg.PW (V.QD (c.Δ G)) Lr.nS with hsel
  have hnAe : hM.nA = sel.length := rfl
  have hac : ActDone M3 M4 Lr.SA (N.Z + 8 * Lr.s + 2) sel := hM.ac
  have hacf : ∀ a, ¬ (N.Z + 8 * Lr.s + 2 ≤ a ∧ a < N.Z + 8 * Lr.s + 2 + 2 * Lr.nS) →
      M4 a = M3 a := hM.ac_fr
  -- the stored entries in the memory after `hwFix`
  have hSM : Rec.SMem T G c R M3 Lr.SA Eg.PW Lr.nS :=
    ⟨hnS, fun j hj => by rw [hM.low3 (by omega)]; exact hAr.pr j hj,
      fun p hp' => by rw [hM.low3 (by omega)]; exact hAr.pw p hp'⟩
  have hlocM : ∀ v ∈ c.X, M4 (Eg.LOC + M4 (Eg.LAB + v)) = R.sv T c v := fun v hv => by
    have hvn : v < G.n := Finset.mem_range.mp (hp.ok.inv.sub hv)
    have h2 : mem (Eg.LAB + v) < T.N := hp.lab_lt v hvn
    rw [hM.low_h (a := Eg.LAB + v) (show Eg.LAB + v < h + 51 by omega),
      hM.low_h (show Eg.LOC + mem (Eg.LAB + v) < h + 51 by omega)]
    exact hAr.loc v hv
  have hsv : ∀ a ∈ c.X, R.sv T c a < Lr.s := fun a ha => hs ▸ hp.ok.sv_lt ha
  have hfd : ∀ a ∈ c.X, M4 (V.h + 51 + 16 * V.nS + 4 * V.s + 5 + R.sv T c a) = c.d G c.x0 a :=
    fun a ha => by
      have h1 := (hF.fd ha).2
      have := hsv a ha
      rw [lowZ (V.h + 51 + 16 * V.nS + 4 * V.s + 5 + R.sv T c a) (by omega),
        show V.h + 51 + 16 * V.nS + 4 * V.s + 5 + R.sv T c a =
        V.dwE.TS + (V.dwE.s + 1) + R.sv T c a by simp only [DWE.TS, SuV.dwE]; ring]
      exact h1
  set F := (suPGA V P.L hM.nA).toPF with hFd
  -- what each active entry names
  have ent : ∀ j < hM.nA, ∃ p, F.pr M4 j = p ∧
      F.fl M4 j = (if p ∈ c.half then 1 else 0) ∧ p < G.m ∧ G.pu p ∈ c.X ∧ G.pv p ∈ c.X ∧
      G.pω p * G.pω p ≤ 512 * P.B * G.n ^ 2 * c.Δ G * c.θ := by
    intro j hj
    rw [hnAe] at hj
    obtain ⟨hi, hpr, hwq⟩ := Rec.sel_entry (P := P) hSM hj hp.ok
    have hi' : sel.getD j 0 < R.S.length := hi
    obtain ⟨e1, e2, e3, -, e5, e6⟩ := hp.ok.entry hi
    obtain ⟨a1, a2⟩ := hac j hj
    have eAS : F.AS = N.Z + 8 * Lr.s + 2 := by
      have e : F.AS = N.z 0 8 0 2 := rfl
      have := ez 0 8 0 2
      omega
    refine ⟨_, ?_, ?_, e1, e2, e3, ?_⟩
    · show M4 (F.AS + 2 * j) = _
      rw [eAS, a1]; exact hpr
    · show M4 (F.AS + 2 * j + 1) = _
      rw [eAS, a2]
      show M3 (Lr.SA + 2 * _ + 1) = _
      rw [hM.low3 (a := Lr.SA + 2 * sel.getD j 0 + 1) (by omega),
        show mem (Lr.SA + 2 * sel.getD j 0 + 1) = _ from hAr.fl _ hi]
      split_ifs with hh
      · exact e6.mpr hh
      · have : (R.S.getD (sel.getD j 0) (0, 0)).2 ≠ 1 :=
          fun e => hh (e6.mp e)
        have e5' : (R.S.getD (sel.getD j 0) (0, 0)).2 ≤ 1 := e5
        omega
    · rw [← hp.QD_eq, ← hpr]; exact hwq
  have hlowh : ∀ a < h + 51, M4 a = mem a := fun a ha => hM.low_h ha
  have hIN : ∀ p < G.m, M4 (Eg.IN + 3 * p) = G.pu p ∧ M4 (Eg.IN + 3 * p + 1) = G.pv p :=
    fun p hp' => by
      rw [hlowh (Eg.IN + 3 * p) (by omega), hlowh (Eg.IN + 3 * p + 1) (by omega)]
      exact hAr.ends p hp'
  have hPW : ∀ p < G.m, M4 (Eg.PW + p) = G.pω p := fun p hp' => by
    rw [hlowh (Eg.PW + p) (by omega)]; exact hAr.pw p hp'
  have hfd' : ∀ a ∈ c.X, M4 (F.DV + R.sv T c a) = c.d G c.x0 a := hfd
  -- the two nodes, the length and the weight of an active entry
  have hj4 : ∀ j < hM.nA, ∃ p, F.pr M4 j = p ∧ p < G.m ∧ G.pu p ∈ c.X ∧ G.pv p ∈ c.X ∧
      F.ea M4 j = R.sv T c (G.pu p) ∧ F.eb M4 j = R.sv T c (G.pv p) ∧ F.ln M4 j ≤ G.pω p ∧
      G.pω p ≤ 128 * P.B * G.n ^ 2 * c.θ ∧ F.fl M4 j ≤ 1 := by
    intro j hj
    obtain ⟨p, e0, ef, e1, e2, e3, e4⟩ := ent j hj
    obtain ⟨i1, i2⟩ := hIN p e1
    refine ⟨p, e0, e1, e2, e3, ?_, ?_, ?_, ?_, ?_⟩
    · show M4 (Eg.LOC + M4 (Eg.LAB + M4 (Eg.IN + 3 * F.pr M4 j))) = _
      rw [e0, i1]; exact hlocM _ e2
    · show M4 (Eg.LOC + M4 (Eg.LAB + M4 (Eg.IN + 3 * F.pr M4 j + 1))) = _
      rw [e0, i2]; exact hlocM _ e3
    · show M4 (Eg.PW + F.pr M4 j) >>> F.fl M4 j ≤ _
      rw [e0, hPW p e1, Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
    · have hK : G.pω p * G.pω p ≤
          (128 * P.B * G.n ^ 2 * c.θ) * (128 * P.B * G.n ^ 2 * c.θ) := by
        have hs2 := hp.ok.inv.small
        calc G.pω p * G.pω p ≤ 512 * P.B * G.n ^ 2 * c.Δ G * c.θ := e4
          _ ≤ 512 * P.B * G.n ^ 2 * (32 * P.B * G.n ^ 2 * c.θ) * c.θ := by gcongr
          _ = _ := by ring
      exact Nat.mul_self_le_mul_self_iff.mp hK
    · rw [ef]; split_ifs <;> omega
  -- the numbers
  have hK : 128 * P.B * G.n ^ 2 * c.θ < 2 ^ Eg.J * c.θ :=
    Nat.mul_lt_mul_of_pos_right hJ0 (by omega)
  have hD4' : 4 * c.Δ G < 2 ^ Eg.J * c.θ := by
    have e : 2 ^ (Eg.J + Lr.lθ) = 2 ^ Eg.J * c.θ := by rw [pow_add, hθ]
    omega
  have e4 : 2 ^ (Lr.lθ + (Eg.J + 3 - 1)) = 4 * (2 ^ Eg.J * c.θ) := by
    rw [hθ, show Lr.lθ + (Eg.J + 3 - 1) = 2 + (Eg.J + Lr.lθ) by omega, pow_add, pow_add]; ring
  have e8 : 2 ^ (Lr.lθ + (Eg.J + 3)) = 8 * (2 ^ Eg.J * c.θ) := by
    rw [hθ, show Lr.lθ + (Eg.J + 3) = 3 + (Eg.J + Lr.lθ) by omega, pow_add, pow_add]; ring
  have e256 : 2 ^ (Eg.J + 8) * c.θ = 256 * (2 ^ Eg.J * c.θ) := by rw [pow_add]; ring
  have hq : 1000 * 1 * 10 ≤ 1000 * (Eg.J + 1) * (G.m + T.N + P.L + 10) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hlθ : Lr.lθ < c.θ := hθ ▸ Nat.lt_two_pow_self
  have hθJ : c.θ ≤ 2 ^ Eg.J * c.θ := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  have hB1 : 1 ≤ P.B := hp.ok.hB
  have hn1 : 1 ≤ G.n := hp.ok.n_pos hX
  have hJ1 : 1 ≤ Eg.J := by
    by_contra h0
    have e : Eg.J = 0 := by omega
    rw [e, pow_zero] at hJ0
    have : 0 < P.B * G.n ^ 2 := Nat.mul_pos (by omega) (pow_pos (by omega) 2)
    have e2 : 128 * P.B * G.n ^ 2 = 128 * (P.B * G.n ^ 2) := by ring
    omega
  have hzt : ∀ a b c k, (V.N P.L).z a b c k = N.Z + a * Lr.nS + b * Lr.s + c * P.L + k :=
    fun _ _ _ _ => rfl
  have hfill : F.Pre M4 w G.m G.n T.N Lr.s := by
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun p hp' => ?_, fun j hj => ?_, fun j hj => ?_,
      fun p hp' => ?_, fun u hu => ?_, fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_,
      fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨p, e0, e1, -⟩ := hj4 j hj; rw [e0]; exact e1
    · obtain ⟨p, -, -, -, -, -, -, -, -, e9⟩ := hj4 j hj; exact e9
    · obtain ⟨i1, i2⟩ := hIN p hp'
      have := hp.glob.hG p hp'
      exact ⟨by rw [show F.IN = Eg.IN from rfl, i1]; exact this.1,
        by rw [show F.IN = Eg.IN from rfl, i2]; exact this.2⟩
    · obtain ⟨p, e0, e1, -⟩ := hj4 j hj
      obtain ⟨i1, i2⟩ := hIN p e1
      have := hp.glob.hG p e1
      show M4 (Eg.LAB + M4 (Eg.IN + 3 * F.pr M4 j)) < T.N ∧
        M4 (Eg.LAB + M4 (Eg.IN + 3 * F.pr M4 j + 1)) < T.N
      rw [e0, i1, i2, hlowh (Eg.LAB + G.pu p) (by omega), hlowh (Eg.LAB + G.pv p) (by omega)]
      exact ⟨hp.lab_lt _ this.1, hp.lab_lt _ this.2⟩
    · obtain ⟨p, -, -, e2, e3, e5, e6, -⟩ := hj4 j hj
      rw [e5, e6]; exact ⟨hsv _ e2, hsv _ e3⟩
    · show M4 (Eg.PW + p) < 2 ^ w
      rw [hPW p hp']; exact (hp.pw_words hX p hp').1
    · obtain ⟨a, ha, rfl⟩ := hp.ok.sv_surj (hs ▸ hu)
      have h1 := hfd' a ha
      have h2 := c.d_le_Δ (G := G) ha
      rw [h1]; omega
    · obtain ⟨p, -, -, e2, e3, e5, e6, e7, e8', -⟩ := hj4 j hj
      show 2 * (M4 (F.DV + F.ea M4 j) + F.ln M4 j - M4 (F.DV + F.eb M4 j)) ≤
        2 ^ (Lr.lθ + (Eg.J + 3 - 1))
      rw [e4, e5, hfd' _ e2]
      have := c.d_le_Δ (G := G) e2
      omega
    · obtain ⟨p, -, -, e2, e3, e5, e6, e7, e8', -⟩ := hj4 j hj
      show 2 * (M4 (F.DV + F.eb M4 j) + F.ln M4 j - M4 (F.DV + F.ea M4 j)) ≤
        2 ^ (Lr.lθ + (Eg.J + 3 - 1))
      rw [e4, e6, hfd' _ e3]
      have := c.d_le_Δ (G := G) e3
      omega
    · show 1 ≤ Eg.J + 3; omega
    · show 2 ^ (Lr.lθ + (Eg.J + 3)) < 2 ^ w
      rw [e8]; omega
    · show Lr.lθ + (Eg.J + 3) + 2 < 2 ^ w
      have : Eg.J < 2 ^ Eg.J := Nat.lt_two_pow_self
      omega
    · obtain ⟨p, -, -, e2, e3, e5, e6, e7, e8', -⟩ := hj4 j hj
      rw [e5, e6, hfd' _ e2, hfd' _ e3]
      have := c.d_le_Δ (G := G) e2
      have := c.d_le_Δ (G := G) e3
      constructor <;> omega
    all_goals try simp only [hFd, PGA.toPF, suPGA, hzt]
    all_goals omega
  have hpc : ∀ u < Lr.s, M4 (N.Z + 7 * Lr.s + 1 + u) = u := fun u hu => hM.pci hp hu
  have hsl : ∀ k < Lr.s, M4 (N.Z + 6 * Lr.s + 1 + k) < Eg.J ∧
      M4 (N.Z + 5 * Lr.s + 1 + k) ≤ c.Δ G := fun k hk => hM.slot hp hX hk
  refine ⟨hfill, fun j hj => ?_, fun j hj => ?_, fun u hu _ => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p, -, -, e2, -, e5, -⟩ := hj4 j hj
    show F.ea M4 j < Lr.s
    rw [e5]; exact hsv _ e2
  · obtain ⟨p, -, -, -, e3, -, e6, -⟩ := hj4 j hj
    show F.eb M4 j < Lr.s
    rw [e6]; exact hsv _ e3
  · have e : (suPGA V P.L hM.nA).PC + u = N.Z + 7 * Lr.s + 1 + u := by
      show N.z 0 7 0 1 + u = _; rw [ez]; omega
    rw [e, hpc u hu]; exact hu
  · have e1 : (suPGA V P.L hM.nA).CS1 + k = N.Z + 5 * Lr.s + 1 + k := by
      show N.z 0 5 0 1 + k = _; rw [ez]; omega
    have e2 : (suPGA V P.L hM.nA).CL1 + k = N.Z + 6 * Lr.s + 1 + k := by
      show N.z 0 6 0 1 + k = _; rw [ez]; omega
    obtain ⟨a1, a2⟩ := hsl k hk
    rw [e1, e2]; constructor <;> omega
  all_goals try simp only [PGA.toPF, suPGA, hzt]
  all_goals omega

end MinCostFlow.LowStretch
