module

public import MinCostFlow.LowStretch.ProgClusterSC2
public import MinCostFlow.LowStretch.ProgPSearchA
public import MinCostFlow.LowStretch.ProgClusterPortal

/-!
# One petal of a cluster: the rules of `PetalOk`

After a petal search stops (`SC.SFound`), the petal at the radius `r = v - 2` is the settled part,
and it passed both tests in its bucket. If `r` is below the distance of the target to the center,
the center is not in the petal, so the highway leaves the petal: its first exit gives the portal
(`PW.Ok.petalOk`). Then the petal meets `PetalOk`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {t : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ}
  {lo rs : ℕ}

/-- The last vertex of a walk is its vertex number `length`. -/
theorem vtx_last (G : PG) (a : ℕ) (ps : List ℕ) : (G.vtx a ps).getD ps.length 0 = G.wend a ps := by
  have := PG.vtx_append_getD (G := G) a ps [] 0
  rw [List.append_nil, Nat.add_zero, PG.vtx_getD_zero] at this
  exact this

open Classical in
/-- **The petal of a search meets `PetalOk`**, with the portal at the first exit of the highway,
when the radius is below the distance of the target to the center. -/
theorem Ok.petalOk (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) {a : SG} {memL : ℕ → ℕ} {v : ℕ}
    (hf : (W.sc mem t st hw lo rs).SFound w a memL v) (hr : v - 2 < W.c.d W.G W.c.x0 t) :
    ∃ i, W.c.PetalOk W.G W.P (W.Y mem) lo ⟨t, hw, v - 2, i⟩ ∧
      W.c.carve W.G (W.Y mem) ⟨t, hw, v - 2, i⟩ = (W.Y mem).filter (fun x => a.d.sett (W.sv x)) := by
  obtain ⟨-, -, ht1, ht2, hcarve, -, -, hq1, hqL, hlo, hhi, -⟩ := hf
  have hY : (↑(W.Y mem) : Set ℕ) ⊆ ↑W.c.X := fun x hx => (mem_Y.mp hx).1
  have hhw := hp.hwd.highway h.conn
  have htY := hp.t_mem
  have ht : t ∈ W.c.carve W.G (W.Y mem) ⟨t, hw, v - 2, 0⟩ :=
    Finset.mem_filter.mpr ⟨htY, 0, Nat.zero_le _, .start htY⟩
  have hx0 : ¬ W.G.wend t hw ∈ W.c.carve W.G (W.Y mem) ⟨t, hw, v - 2, 0⟩ := by
    rw [hhw.1.wend_eq]
    intro hm
    obtain ⟨-, k, hk, hD⟩ := Finset.mem_filter.mp hm
    change k ≤ v - 2 at hk
    have := Cl.potential h.conn hY hhw hD
    have h0 : W.c.d W.G W.c.x0 W.c.x0 = 0 := PG.dist_self (by simpa using h.conn.1)
    omega
  obtain ⟨i, hi, hin, hout⟩ := PG.first_exit (G := W.G) t hw
    (· ∈ W.c.carve W.G (W.Y mem) ⟨t, hw, v - 2, 0⟩) ht ⟨hw.length, le_rfl, by rw [vtx_last]; exact hx0⟩
  refine ⟨i, ⟨htY, hhw, hi, hin, hout, a.q, hq1, ?_, ?_, ?_, ht1, ht2⟩, hcarve⟩
  · have := h.hLb; change a.q ≤ W.Lb at hqL; omega
  · have := h.hbw; change lo + (a.q - 1) * W.bw ≤ v - 2 at hlo; rw [← this]; exact hlo
  · have := h.hbw; change v - 2 ≤ lo + a.q * W.bw at hhi; rw [← this]; exact hhi

open Classical in
/-- **The portal is a step.** The first exit of the highway is step `m` of `st`, from the last
settled highway node `H[m]` to the pointer node `H[m + 1]`: so `m + 1` is the pointer index `a.j`
of the stopped state. -/
theorem Ok.portal (h : W.Ok w mem) (hp : W.PS w mem t st hw lo) {a : SG} {memL : ℕ → ℕ} {v : ℕ}
    (hf : (W.sc mem t st hw lo rs).SFound w a memL v) (hr : v - 2 < W.c.d W.G W.c.x0 t) :
    ∃ i, W.c.PetalOk W.G W.P (W.Y mem) lo ⟨t, hw, v - 2, i⟩ ∧
      W.c.carve W.G (W.Y mem) ⟨t, hw, v - 2, i⟩ = (W.Y mem).filter (fun x => a.d.sett (W.sv x)) ∧
      ∃ m, ∃ hm : m < st.length, m + 1 = a.j ∧ hw.getD i 0 = st[m].1 ∧
        hv W.G t hw i = st[m].2.1 ∧ hv W.G t hw (i + 1) = st[m].2.2 := by
  have hsett := hf.1.hsett
  obtain ⟨i, hpet, hcarve⟩ := h.petalOk hp hf hr
  refine ⟨i, hpet, hcarve, ?_⟩
  obtain ⟨-, -, hi, hin, hout, -⟩ := hpet
  change i < hw.length at hi
  have hin' := hin i le_rfl
  change W.c.carve W.G (W.Y mem) ⟨t, hw, v - 2, i⟩ = _ at hcarve
  rw [hcarve, Finset.mem_filter] at hin'
  have hout' : ¬ (hv W.G t hw (i + 1) ∈ W.Y mem ∧ a.d.sett (W.sv (hv W.G t hw (i + 1)))) := by
    intro hh; apply hout; rw [hcarve, Finset.mem_filter]; exact hh
  rcases (hp.hwd.steps h.conn hi).2 with hl | hmem
  · exfalso
    have hX : hv W.G t hw (i + 1) ∈ W.c.X := by
      have := hp.hwd.walk.getD_mem (i := i + 1) (by omega)
      exact this
    have hY := h.Y_cl hin'.1 hX hl
    have e := (h.sv_iff (mem_Y.mp hin'.1).1 hX).mpr hl
    exact hout' ⟨hY, by rw [← e]; exact hin'.2⟩
  · obtain ⟨m, hm, e⟩ := List.getElem_of_mem hmem
    have e1 : st[m].2.1 = hv W.G t hw i := by rw [e]; rfl
    have e2 : st[m].2.2 = hv W.G t hw (i + 1) := by rw [e]; rfl
    have e0 : st[m].1 = hw.getD i 0 := by rw [e]
    have hHm : (W.Hl t st).getD m 0 = W.sv (st[m].2.1) := by
      rw [Hl_getD t st hm.le, (h.sv_fst hp hm).1]
    have hHm1 : (W.Hl t st).getD (m + 1) 0 = W.sv (st[m].2.2) := by
      rw [Hl_getD t st hm, stEnt_succ hm]
    have hlen : (W.Hl t st).length = st.length + 1 := Hl_length t st
    have s1 : m < a.j := by
      have := (hsett m (by show m < (W.Hl t st).length; omega)).mp
      apply this
      show a.d.sett ((W.Hl t st).getD m 0)
      rw [hHm, e1]; exact hin'.2
    have s2 : ¬ m + 1 < a.j := by
      intro hlt
      have := (hsett (m + 1) (by show m + 1 < (W.Hl t st).length; omega)).mpr hlt
      change a.d.sett ((W.Hl t st).getD (m + 1) 0) at this
      rw [hHm1, e2] at this
      have hY : hv W.G t hw (i + 1) ∈ W.Y mem := by
        rw [← e2, ← stEnt_succ hm]; exact hp.entY (m + 1) hm
      exact hout' ⟨hY, this⟩
    exact ⟨m, hm, by omega, e0.symm, e1.symm, e2.symm⟩

/-- The walk along `NXT` from the target follows the highway nodes. -/
theorem PS.pIt_eq (hp : W.PS w mem t st hw lo) {k : ℕ} (hk : k ≤ st.length) :
    pIt mem W.NXT (W.sv t) k = (W.Hl t st).getD k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pIt_succ, ih (by omega), Hl_getD t st (by omega), hp.nxt k (by omega), Hl_getD t st hk]

/-- **The portal walk** from the target stops at `H[m]` when the pointer is `H[m + 1]`. -/
theorem PS.portOk (hp : W.PS w mem t st hw lo) {m : ℕ} (hm : m < st.length) :
    PortOk mem W.NXT (W.sv t) ((W.Hl t st).getD (m + 1) 0) m := by
  have hlen : (W.Hl t st).length = st.length + 1 := Hl_length t st
  refine ⟨?_, fun k hk => ?_⟩
  · rw [← pIt_succ mem W.NXT (W.sv t) m, hp.pIt_eq hm]
  · rw [← pIt_succ mem W.NXT (W.sv t) k, hp.pIt_eq (by omega)]
    intro e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    have := (List.Nodup.getElem_inj_iff hp.nd).mp e
    omega

end PW

end MinCostFlow.LowStretch
