module

public import MinCostFlow.LowStretch.ProgClusterSet9
public import MinCostFlow.LowStretch.ProgAct

/-!
# The setup of a cluster: the active entries

`actP` keeps the stored entries whose weight `ω` has `ω² ≤ QD`, in order (`selL`). With
`QD = Q · (Δ · θ)` these are exactly the active pairs of the cluster: a stored pair has both ends
in `X` and its ends in different nodes, so it is not light-joined, and every active pair is stored
(`Rec.Ok.act_sub`). The stored pairs are distinct (`Rec.Ok.S_nodup`), so the kept entries name
distinct pairs. This gives the facts `img` and `inj` of `PW.Ok` (`Rec.act_img`, `Rec.act_inj`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Rec

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {mem : ℕ → ℕ}

/-- The pair of kept entry `j`. -/
def apr (mem : ℕ → ℕ) (SA PW QD nS j : ℕ) : ℕ := gpr mem SA ((selL mem SA PW QD nS).getD j 0)

/-- The facts of the stored entries in memory that `actP` reads. -/
structure SMem (T : KT) (G : PG) (c : Cl) (R : Rec) (mem : ℕ → ℕ) (SA PW nS : ℕ) : Prop where
  nS : nS = R.S.length
  pr : ∀ j < R.S.length, mem (SA + 2 * j) = (R.S.getD j (0, 0)).1
  pw : ∀ p < G.m, mem (PW + p) = G.pω p

variable {SA PW nS QD : ℕ}

/-- A kept entry is a stored entry with `ω² ≤ QD`. -/
theorem sel_entry (hM : SMem T G c R mem SA PW nS) {j : ℕ}
    (hj : j < (selL mem SA PW QD nS).length) (h : R.Ok T G P c) :
    (selL mem SA PW QD nS).getD j 0 < R.S.length ∧
      apr mem SA PW QD nS j = (R.S.getD ((selL mem SA PW QD nS).getD j 0) (0, 0)).1 ∧
      G.pω (apr mem SA PW QD nS j) * G.pω (apr mem SA PW QD nS j) ≤ QD := by
  have hm : (selL mem SA PW QD nS).getD j 0 ∈ selL mem SA PW QD nS := by
    rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
  obtain ⟨h1, h2⟩ := mem_selL.mp hm
  have hi : (selL mem SA PW QD nS).getD j 0 < R.S.length := hM.nS ▸ h1
  have hpr : apr mem SA PW QD nS j = (R.S.getD ((selL mem SA PW QD nS).getD j 0) (0, 0)).1 :=
    hM.pr _ hi
  refine ⟨hi, hpr, ?_⟩
  have hlt := (h.entry hi).1
  rw [← hpr] at hlt
  have := hM.pw _ hlt
  unfold apr at this ⊢
  rw [← this]; exact h2

/-- **The kept entries name the active pairs.** -/
theorem act_img (h : R.Ok T G P c) (hM : SMem T G c R mem SA PW nS)
    (hQD : QD = P.Q * (c.Δ G * c.θ)) :
    (Finset.range (selL mem SA PW QD nS).length).image (apr mem SA PW QD nS) = c.act G P := by
  ext p
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨hi, hpr, hw⟩ := sel_entry (P := P) hM hj h
    obtain ⟨e1, e2, e3, e4, -⟩ := h.entry hi
    rw [← hpr] at e1 e2 e3 e4
    unfold Cl.act
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨e1, e1, e2, e3, h.not_lconn e2 e3 e4, ?_⟩
    rw [sq, ← hQD]; exact hw
  · intro hp
    have ha := hp
    unfold Cl.act at ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨-, hpm, -, -, -, hpw⟩ := ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (h.act_sub p hp)
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp he
    have hgi : R.S.getD i (0, 0) = e := by rw [List.getD_eq_getElem _ _ hi]; exact hie
    have hsel : i ∈ selL mem SA PW QD nS := by
      refine mem_selL.mpr ⟨hM.nS ▸ hi, ?_⟩
      unfold gpr
      rw [hM.pr i hi, hgi, hM.pw _ hpm, ← sq, hQD]; exact hpw
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.mp hsel
    refine ⟨j, hj, ?_⟩
    unfold apr gpr
    rw [List.getD_eq_getElem _ _ hj, hji, hM.pr i hi, hgi]

/-- **The kept entries name distinct pairs.** -/
theorem act_inj (h : R.Ok T G P c) (hM : SMem T G c R mem SA PW nS) :
    Set.InjOn (apr mem SA PW QD nS) ↑(Finset.range (selL mem SA PW QD nS).length) := by
  intro j hj j' hj' he
  simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
  obtain ⟨hi, hpr, -⟩ := sel_entry (P := P) hM hj h
  obtain ⟨hi', hpr', -⟩ := sel_entry (P := P) hM hj' h
  rw [hpr, hpr'] at he
  have hnd := h.S_nodup
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at he
  have hidx := (List.Nodup.getElem_inj_iff hnd (i := (selL mem SA PW QD nS).getD j 0)
    (j := (selL mem SA PW QD nS).getD j' 0) (hi := by simpa using hi)
    (hj := by simpa using hi')).mp (by simpa using he)
  have hsn : (selL mem SA PW QD nS).Nodup := (List.nodup_range).filter _
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] at hidx
  exact (List.Nodup.getElem_inj_iff hsn).mp hidx

/-- **The weights of the active entries.** With `Es` at least every exponent `e j`, the weight
`2^Es / ω` of entry `j` is `1 <<< (Es - e j)`, and weight times `ω` is `2^Es`. -/
theorem wt_tab {G : PG} {nA Es : ℕ} {pr e : ℕ → ℕ} (hle : ∀ j < nA, e j ≤ Es)
    (hex : ∀ j < nA, G.pω (pr j) = 2 ^ e j) {j : ℕ} (hj : j < nA) :
    1 <<< (Es - e j) = 2 ^ Es / G.pω (pr j) ∧ 2 ^ Es / G.pω (pr j) * G.pω (pr j) = 2 ^ Es := by
  have h1 := hle j hj
  have hp : 2 ^ Es = 2 ^ (Es - e j) * 2 ^ e j := by rw [← pow_add]; congr 1; omega
  rw [hex j hj, Nat.one_shiftLeft, hp, Nat.mul_div_cancel _ (by positivity)]
  exact ⟨rfl, rfl⟩

end Rec

end MinCostFlow.LowStretch
