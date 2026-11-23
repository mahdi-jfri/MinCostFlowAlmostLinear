module

public import MinCostFlow.LowStretch.ProgClusterSetupFm

/-!
# The setup of a cluster: the active entries after `actP`

Each active entry `j` that `actP` writes at `ACT = Z + 8 s + 2` names a stored pair `p`: its
flag is the half flag of `p`, both ends of `p` lie in the cluster, `p` is not light, and the
values that `pgP` reads for it are the nodes of its ends, its length and its shifted lengths
(`ClPre.actEnt`). The facts come from the stored entries of the record (`Rec.Ok.entry`,
`Rec.Ok.theta_le`), the arrays of the global block (`RecAt.arcs`) and the distances of the first
run (`ClPre.fdM4`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

/-- **The distances of the first run** after `actP`: the cell `FD + sv a` holds `d(x0, a)`. -/
theorem ClPre.fdM4 (hp : ClPre w A T G P c R GB RB h mem) {M M2 M3 M4 : ℕ → ℕ}
    (hM : SuMem w T G P c R GB RB h mem M M2 M3 M4) {a : ℕ} (ha : a ∈ c.X) :
    M4 (h + 51 + 16 * (RecL.read mem RB).nS + 4 * (RecL.read mem RB).s + 5 + R.sv T c a) =
      c.d G c.x0 a := by
  have h1 := (hM.first.fd ha).2
  have hs : (RecL.read mem RB).s = R.nodes.length := hp.recAt.arcs.s
  have hsv : R.sv T c a < (RecL.read mem RB).s := hs ▸ hp.ok.sv_lt ha
  have eZ : ((suVOf GB RB h mem).N P.L).Z = h + 51 + 16 * (RecL.read mem RB).nS +
      8 * (RecL.read mem RB).s + 14 + 4 * (GlobL.read mem GB).J +
      2 * (GlobL.read mem GB).J * (2 * (RecL.read mem RB).nS + (RecL.read mem RB).s + 1) := rfl
  rw [hM.low_Z (by omega),
    show h + 51 + 16 * (RecL.read mem RB).nS + 4 * (RecL.read mem RB).s + 5 + R.sv T c a =
      (suVOf GB RB h mem).dwE.TS + ((suVOf GB RB h mem).dwE.s + 1) + R.sv T c a by
      simp only [DWE.TS, SuV.dwE, suVOf]; ring]
  exact h1

/-- What an active entry `j` names, with `F = (suPGA V L nA).toPF` the setting of `pfill`. -/
structure SuEnt (T : KT) (G : PG) (c : Cl) (R : Rec) (GB : ℕ) (mem M4 : ℕ → ℕ) (F : PF)
    (j : ℕ) : Prop where
  lt : F.pr M4 j < G.m
  fl : F.fl M4 j = if F.pr M4 j ∈ c.half then 1 else 0
  hu : G.pu (F.pr M4 j) ∈ c.X
  hv : G.pv (F.pr M4 j) ∈ c.X
  θ_le : c.θ ≤ G.pω (F.pr M4 j)
  ea : F.ea M4 j = R.sv T c (G.pu (F.pr M4 j))
  eb : F.eb M4 j = R.sv T c (G.pv (F.pr M4 j))
  x1 : F.x1 M4 j = c.wbar G (F.pr M4 j) (G.pu (F.pr M4 j)) (G.pv (F.pr M4 j))
  x2 : F.x2 M4 j = c.wbar G (F.pr M4 j) (G.pv (F.pr M4 j)) (G.pu (F.pr M4 j))
  ex : G.pω (F.pr M4 j) = 2 ^ mem ((GlobL.read mem GB).EXP + F.pr M4 j)

set_option maxHeartbeats 4000000 in
/-- **The active entries.** -/
theorem ClPre.actEnt (hp : ClPre w A T G P c R GB RB h mem) {M M2 M3 M4 : ℕ → ℕ}
    (hM : SuMem w T G P c R GB RB h mem M M2 M3 M4) {j : ℕ} (hj : j < hM.nA) :
    SuEnt T G c R GB mem M4 (suPGA (suVOf GB RB h mem) P.L hM.nA).toPF j ∧
      (suPGA (suVOf GB RB h mem) P.L hM.nA).toPF.pr M4 j =
        Rec.apr M3 (RecL.read mem RB).SA (GlobL.read mem GB).PW
          ((suVOf GB RB h mem).QD (c.Δ G)) (RecL.read mem RB).nS j := by
  set V := suVOf GB RB h mem with hV
  set N := V.N P.L with hN
  set Lr := RecL.read mem RB with hLr
  set Eg := GlobL.read mem GB with hEg
  have hb : ∀ r ∈ recRegs GB RB Eg Lr, r.1 + r.2 ≤ h := hp.below
  have bSA := hb (Lr.SA, 2 * Lr.nS) (by simp [recRegs, RecL.regs])
  have bIN := hb (Eg.IN, 3 * Eg.m) (by simp [recRegs])
  have bPW := hb (Eg.PW, Eg.m) (by simp [recRegs])
  have bEX := hb (Eg.EXP, Eg.m) (by simp [recRegs])
  dsimp only at bSA bIN bPW bEX
  have hm' : Eg.m = G.m := hp.glob.m
  have hlab : Eg.LAB + G.n ≤ h := hp.lab_below
  have hloc : Eg.LOC + T.N ≤ h := hp.loc_below
  have hAr := hp.recAt.arcs
  have hnS : Lr.nS = R.S.length := hAr.nS
  have hs : Lr.s = R.nodes.length := hAr.s
  have ez : ∀ a b c k, N.z a b c k = N.Z + a * N.nS + b * N.s + c * N.L + k :=
    fun _ _ _ _ => rfl
  have vs : N.s = Lr.s := rfl
  have vnS : N.nS = Lr.nS := rfl
  have eZ : N.Z = h + 51 + 16 * N.nS + 8 * N.s + 14 + 4 * N.J +
      2 * N.J * (2 * N.nS + N.s + 1) := rfl
  set sel := selL M3 Lr.SA Eg.PW (V.QD (c.Δ G)) Lr.nS with hsel
  have hnAe : hM.nA = sel.length := rfl
  have hac : ActDone M3 M4 Lr.SA (N.Z + 8 * Lr.s + 2) sel := hM.ac
  have hSM : Rec.SMem T G c R M3 Lr.SA Eg.PW Lr.nS :=
    ⟨hnS, fun j hj => by rw [hM.low3 (by omega)]; exact hAr.pr j hj,
      fun p hp' => by rw [hM.low3 (by omega)]; exact hAr.pw p hp'⟩
  have hlowh : ∀ a < h + 51, M4 a = mem a := fun a ha => hM.low_h ha
  have hlocM : ∀ v ∈ c.X, M4 (Eg.LOC + M4 (Eg.LAB + v)) = R.sv T c v := fun v hv => by
    have hvn : v < G.n := Finset.mem_range.mp (hp.ok.inv.sub hv)
    have h2 : mem (Eg.LAB + v) < T.N := hp.lab_lt v hvn
    rw [hlowh (Eg.LAB + v) (by omega), hlowh (Eg.LOC + mem (Eg.LAB + v)) (by omega)]
    exact hAr.loc v hv
  set F := (suPGA V P.L hM.nA).toPF with hFd
  have eAS : F.AS = N.Z + 8 * Lr.s + 2 := by
    have e : F.AS = N.z 0 8 0 2 := rfl
    rw [e, ez]; omega
  rw [hnAe] at hj
  obtain ⟨hi, hpr, -⟩ := Rec.sel_entry (P := P) hSM hj hp.ok
  have hi' : sel.getD j 0 < R.S.length := hi
  obtain ⟨e1, e2, e3, -, e5, e6⟩ := hp.ok.entry hi
  have hθ := hp.ok.theta_le hi
  obtain ⟨a1, a2⟩ := hac j hj
  have hpr' : F.pr M4 j = (R.S.getD (sel.getD j 0) (0, 0)).1 := by
    show M4 (F.AS + 2 * j) = _
    rw [eAS, a1]; exact hpr
  have hapr : F.pr M4 j = Rec.apr M3 Lr.SA Eg.PW (V.QD (c.Δ G)) Lr.nS j := by
    show M4 (F.AS + 2 * j) = _
    rw [eAS, a1]; rfl
  refine ⟨?_, hapr⟩
  set p := F.pr M4 j with hp'
  have hfl : F.fl M4 j = if p ∈ c.half then 1 else 0 := by
    show M4 (F.AS + 2 * j + 1) = _
    rw [eAS, a2]
    show M3 (Lr.SA + 2 * _ + 1) = _
    rw [hM.low3 (a := Lr.SA + 2 * sel.getD j 0 + 1) (by omega),
      show mem (Lr.SA + 2 * sel.getD j 0 + 1) = _ from hAr.fl _ hi, hpr']
    split_ifs with hh
    · exact e6.mpr hh
    · have : (R.S.getD (sel.getD j 0) (0, 0)).2 ≠ 1 := fun e => hh (e6.mp e)
      have e5' : (R.S.getD (sel.getD j 0) (0, 0)).2 ≤ 1 := e5
      omega
  rw [← hpr'] at e1 e2 e3 hθ
  obtain ⟨i1, i2⟩ := hAr.ends p e1
  have hea : F.ea M4 j = R.sv T c (G.pu p) := by
    show M4 (Eg.LOC + M4 (Eg.LAB + M4 (Eg.IN + 3 * F.pr M4 j))) = _
    rw [← hp', hlowh (Eg.IN + 3 * p) (by omega)]
    erw [i1]; exact hlocM _ e2
  have heb : F.eb M4 j = R.sv T c (G.pv p) := by
    show M4 (Eg.LOC + M4 (Eg.LAB + M4 (Eg.IN + 3 * F.pr M4 j + 1))) = _
    rw [← hp', hlowh (Eg.IN + 3 * p + 1) (by omega)]
    erw [i2]; exact hlocM _ e3
  have hln : F.ln M4 j = c.len G p := by
    show M4 (Eg.PW + F.pr M4 j) >>> F.fl M4 j = _
    rw [← hp', hlowh (Eg.PW + p) (by omega), hfl]
    erw [hAr.pw p e1]
    exact Cl.shr_len hθ
  have hDV : ∀ a ∈ c.X, M4 (F.DV + R.sv T c a) = c.d G c.x0 a := fun a ha => hp.fdM4 hM ha
  obtain ⟨x1, x2⟩ := PGA.x1_eq (suPGA V P.L hM.nA) hea heb e2 e3 hDV hln
  exact ⟨e1, hfl, e2, e3, hθ, hea, heb, x1, x2, hAr.ex p e1⟩

end MinCostFlow.LowStretch
