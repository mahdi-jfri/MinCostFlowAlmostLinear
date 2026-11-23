module

public import MinCostFlow.LowStretch.ProgClusterSet4
public import MinCostFlow.LowStretch.ProgHwFix
public import MinCostFlow.LowStretch.ProgChildSpec

/-!
# The setup of a cluster: the stored highway

`hwFix` reads the stored highway of the record and writes each of its pairs over the tree arrays,
at the node of its end at the side of the target. Here we read what it reads: entry `j` of the
stored highway is step `j` of the split highway `hwSt` with its flag (`RecAt.hwSt`), its node is
the local index of the start of the step, and its length is the length of the pair
(`HFV.nu_eq`, `HFV.hl_eq`). The nodes of the entries are distinct, since the distance from the
center drops strictly from one step to the next (`HFV.pre`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

/-- The steps of `hwSt` are not light. -/
theorem hwSt_heavy {θ t : ℕ} {hw : List ℕ} : ∀ s ∈ hwSt G θ t hw, θ ≤ G.pω s.1 := by
  induction hw generalizing t with
  | nil => simp [hwSt]
  | cons p hw ih =>
    intro s hs
    rw [hwSt] at hs
    rcases List.mem_append.mp hs with hs | hs
    · split_ifs at hs with h1
      · simp only [List.mem_singleton] at hs; subst hs; exact h1
      · simp at hs
    · exact ih s hs

end Cl

theorem getD_mem_st {st : List (ℕ × ℕ × ℕ)} {j : ℕ} (hj : j < st.length) :
    st.getD j (0, 0, 0) ∈ st := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

/-- **The stored highway is the split highway with its flags.** -/
theorem RecAt.hwSt {T : KT} {G : PG} {c : Cl} {R : Rec} {E : GlobL} {L : RecL} {mem : ℕ → ℕ}
    (h : RecAt T G c R E L mem) :
    L.nH = (Cl.hwSt G c.θ c.t c.hw).length ∧ ∀ j < L.nH,
      mem (L.HW + 4 * j) = ((Cl.hwSt G c.θ c.t c.hw).getD j (0, 0, 0)).1 ∧
      mem (L.HW + 4 * j + 1) =
        (if ((Cl.hwSt G c.θ c.t c.hw).getD j (0, 0, 0)).1 ∈ c.half then 1 else 0) ∧
      mem (L.HW + 4 * j + 2) = ((Cl.hwSt G c.θ c.t c.hw).getD j (0, 0, 0)).2.1 ∧
      mem (L.HW + 4 * j + 3) = ((Cl.hwSt G c.θ c.t c.hw).getD j (0, 0, 0)).2.2 := by
  have e := Cl.hwE_eq_hwSt (G := G) c.t c.hw c.θ c.half
  have hn : L.nH = (Cl.hwSt G c.θ c.t c.hw).length := by rw [h.nH, e, List.length_map]
  refine ⟨hn, fun j hj => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.hw j hj
  have hj' : j < (Cl.hwSt G c.θ c.t c.hw).length := hn ▸ hj
  have g : (Cl.hwE G c.t c.hw c.θ c.half).getD j (0, 0, 0, 0) =
      Cl.stE c.half ((Cl.hwSt G c.θ c.t c.hw).getD j (0, 0, 0)) := by
    rw [e, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
      List.getD_eq_getElem _ _ hj']
  rw [g] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

namespace HF

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec}

/-- The setting of `hwFix` in a cluster: the stored highway at `HW` (as `RecAt.hwSt` gives it),
the record in memory below `H` (labels, local indices, weights and exponents), and the memory
`M` that agrees with `mem` below `H`. -/
structure V (F : HF) (T : KT) (G : PG) (P : Par) (c : Cl) (R : Rec) (mem M : ℕ → ℕ) (H NL : ℕ) :
    Prop where
  ok : R.Ok T G P c
  nH : F.nH = (Cl.hwSt G c.θ c.t c.hw).length
  hw : ∀ j < F.nH,
      mem (F.HW + 4 * j) = ((Cl.hwSt G c.θ c.t c.hw).getD j (0, 0, 0)).1 ∧
      mem (F.HW + 4 * j + 1) =
        (if ((Cl.hwSt G c.θ c.t c.hw).getD j (0, 0, 0)).1 ∈ c.half then 1 else 0) ∧
      mem (F.HW + 4 * j + 2) = ((Cl.hwSt G c.θ c.t c.hw).getD j (0, 0, 0)).2.1 ∧
      mem (F.HW + 4 * j + 3) = ((Cl.hwSt G c.θ c.t c.hw).getD j (0, 0, 0)).2.2
  loc : ∀ v ∈ c.X, mem (F.LOC + mem (F.LAB + v)) = R.sv T c v
  lab : ∀ v ∈ c.X, mem (F.LAB + v) < NL
  pw : ∀ p < G.m, mem (F.PW + p) = G.pω p
  ex : ∀ p < G.m, G.pω p = 2 ^ mem (F.EXP + p)
  th : c.θ = 2 ^ F.lθ
  low : ∀ a < H, M a = mem a
  rHW : F.HW + 4 * F.nH ≤ H
  rLAB : F.LAB + G.n ≤ H
  rLOC : F.LOC + NL ≤ H
  rPW : F.PW + G.m ≤ H
  rEXP : F.EXP + G.m ≤ H
  hs : F.s = R.nodes.length

variable {F : HF} {mem M : ℕ → ℕ} {H NL : ℕ}

/-- Step `j` of the split highway of the cluster. -/
noncomputable abbrev sj (G : PG) (c : Cl) (j : ℕ) : ℕ × ℕ × ℕ :=
  (Cl.hwSt G c.θ c.t c.hw).getD j (0, 0, 0)

theorem V.split (h : V F T G P c R mem M H NL) :
    c.StOk G c.t (Cl.hwSt G c.θ c.t c.hw) := h.ok.inv.good.high.hwDec.stOk

theorem V.step (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    G.Joins (sj G c j).1 (sj G c j).2.1 (sj G c j).2.2 ∧ (sj G c j).2.1 ∈ c.X ∧
      (sj G c j).2.2 ∈ c.X ∧
      c.d G c.x0 (sj G c j).2.1 = c.d G c.x0 (sj G c j).2.2 + c.len G (sj G c j).1 :=
  h.split.step (h.nH ▸ hj)

theorem V.hp_eq (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    F.hp M j = (sj G c j).1 := by
  unfold HF.hp; rw [h.low _ (by have := h.rHW; omega)]; exact (h.hw j hj).1

theorem V.hf_eq (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    F.hf M j = if (sj G c j).1 ∈ c.half then 1 else 0 := by
  unfold HF.hf; rw [h.low _ (by have := h.rHW; omega)]; exact (h.hw j hj).2.1

theorem V.ha_eq (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    F.ha M j = (sj G c j).2.1 := by
  unfold HF.ha; rw [h.low _ (by have := h.rHW; omega)]; exact (h.hw j hj).2.2.1

theorem V.hb_eq (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    F.hb M j = (sj G c j).2.2 := by
  unfold HF.hb; rw [h.low _ (by have := h.rHW; omega)]; exact (h.hw j hj).2.2.2

/-- The local index of a vertex of the cluster, read through its label. -/
theorem V.loc_read (h : V F T G P c R mem M H NL) {v : ℕ} (hv : v ∈ c.X) :
    M (F.LOC + M (F.LAB + v)) = R.sv T c v := by
  have hvn := h.ok.n_of_mem hv
  have hl := h.lab v hv
  have := h.rLAB; have := h.rLOC
  rw [h.low (F.LAB + v) (by omega), h.low _ (by omega)]
  exact h.loc v hv

theorem V.nu_eq (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    F.nu M j = R.sv T c (sj G c j).2.1 := by
  unfold HF.nu; rw [V.ha_eq h hj]; exact h.loc_read (h.step hj).2.1

theorem V.nv_eq (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    F.nv M j = R.sv T c (sj G c j).2.2 := by
  unfold HF.nv; rw [V.hb_eq h hj]; exact h.loc_read (h.step hj).2.2.1

theorem V.heavy (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    c.θ ≤ G.pω (sj G c j).1 :=
  Cl.hwSt_heavy _ (getD_mem_st (h.nH ▸ hj))

theorem V.hl_eq (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    F.hl M j = c.len G (sj G c j).1 := by
  have hm := (h.step hj).1.1
  have hθ := h.heavy hj
  have := h.rPW
  unfold HF.hl
  rw [V.hp_eq h hj, V.hf_eq h hj, h.low (F.PW + (sj G c j).1) (by omega), h.pw _ hm]
  unfold Cl.len
  have hnl : ¬ G.pω (sj G c j).1 < c.θ := by omega
  by_cases hh : (sj G c j).1 ∈ c.half
  · simp only [hh, hnl, if_true, if_false]; simp [Nat.shiftRight_eq_div_pow]
  · simp only [hh, hnl, if_false]; simp

theorem V.pos (h : V F T G P c R mem M H NL) {j : ℕ} (hj : j < F.nH) :
    0 < c.len G (sj G c j).1 :=
  Cl.hwSt_pos h.ok.hGo h.ok.inv.good.high _ (getD_mem_st (h.nH ▸ hj))

/-- **The nodes of the entries are distinct.** -/
theorem V.nu_inj (h : V F T G P c R mem M H NL) {j j' : ℕ} (hj : j < F.nH) (hj' : j' < F.nH)
    (he : F.nu M j = F.nu M j') : j = j' := by
  rw [h.nu_eq hj, h.nu_eq hj'] at he
  have hc := h.ok.inv.good.conn
  have hl := (h.ok.sv_iff (h.step hj).2.1 (h.step hj').2.1).mp he
  exact h.split.d_start_inj hc (Cl.hwSt_pos h.ok.hGo h.ok.inv.good.high) (h.nH ▸ hj)
    (h.nH ▸ hj') (Cl.d_lconn hc hl)

/-- **The precondition of `hwFix`.** -/
theorem V.pre {w : ℕ} (h : V F T G P c R mem M H NL) (hP : H ≤ F.PAR)
    (l1 : F.PAR + F.s ≤ F.PP) (l2 : F.PP + F.s ≤ F.PF) (l3 : F.PF + F.s ≤ F.PA)
    (l4 : F.PA + F.s ≤ F.PB) (l5 : F.PB + F.s ≤ F.SCc) (l6 : F.SCc + F.s ≤ F.SCk)
    (l7 : F.SCk + F.s < 2 ^ w) (hw1 : 1 < 2 ^ w) (hww : ∀ p < G.m, G.pω p < 2 ^ w ∧ mem (F.EXP + p) + 2 < 2 ^ w) :
    F.Pre M w := by
  have rHW := h.rHW; have rLAB := h.rLAB; have rLOC := h.rLOC; have rPW := h.rPW
  have rEXP := h.rEXP
  refine ⟨fun j hj j' hj' he => h.nu_inj hj hj' he, fun j hj => ?_, l1, l2, l3, l4, l5, l6, l7,
    by omega, hw1, fun j hj => ?_⟩
  · rw [h.nu_eq hj, h.hs]; exact h.ok.sv_lt (h.step hj).2.1
  · obtain ⟨hjn, ha, hb, -⟩ := h.step hj
    have hm := hjn.1
    have han := h.ok.n_of_mem ha
    have hbn := h.ok.n_of_mem hb
    have hla := h.lab _ ha
    have hlb := h.lab _ hb
    rw [V.ha_eq h hj, V.hb_eq h hj, V.hp_eq h hj, h.low (F.LAB + _) (by omega),
      h.low (F.LAB + (sj G c j).2.2) (by omega), h.low (F.PW + _) (by omega),
      h.low (F.EXP + _) (by omega), h.pw _ hm]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, (hww _ hm).1,
      (hww _ hm).2⟩

end HF

end MinCostFlow.LowStretch
