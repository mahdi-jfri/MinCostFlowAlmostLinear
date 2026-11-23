module

public import MinCostFlow.LowStretch.ProgClusterSet1
public import MinCostFlow.LowStretch.ProgTree

/-!
# The setup of a cluster: the tree of the first run

At the end of the first run of Dijkstra (`drawP_spec2`), the tentative cost of the node of each
vertex `a` is its distance `d(x0, a)` (`Rec.first_fd`). Each node `u` other than the node of the
center has a parent `par u` and a parent arc `k`, which goes from `par u` to `u` and gives the
cost of `u`. The arc `k` holds a direction of a stored entry `j`, a pair between a vertex of `u`
and a vertex of `par u`. `treeP` reads these. So the values it writes for `u` are the parent, the
pair of `j`, its flag, its end in `u`, its end in `par u` and its length, and the distance drops
by the length along the pair (`Rec.first_edge`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace DWE

variable (E : DWE)

/-- The graph of `arcP` depends only on the cells below the stamps. -/
theorem g_congr {M M' : ℕ → ℕ} (h : ∀ a < E.TS, M a = M' a) : E.ap.g M = E.ap.g M' := by
  have eTS : E.TS = E.H + 16 * E.nS + 3 * E.s + 4 := rfl
  have e1 : E.ap.s = E.s := rfl
  have e2 : E.ap.nS = E.nS := rfl
  unfold AP.g
  congr 1
  · funext u; split_ifs with hu
    · exact h _ (by simp only [DWE.ap]; omega)
    · rfl
  · funext u; split_ifs with hu
    · exact h _ (by simp only [DWE.ap]; omega)
    · rfl
  · funext k; split_ifs with hk
    · exact h _ (by simp only [DWE.ap]; omega)
    · rfl
  · funext k; split_ifs with hk
    · exact h _ (by simp only [DWE.ap]; omega)
    · rfl
  · funext v
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← h _ (by simp only [DWE.ap]; omega)]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [h _ (by simp only [DWE.ap]; omega)]; exact h2⟩

/-- The layout of `treeP` after the first run, with its arrays from `P` on. -/
def tf (P : ℕ) : TF :=
  ⟨E.s, E.x0, E.TS, E.s + 1, E.ap.ORD, E.ap.CS, E.ap.CL, E.SA, E.IN, E.LAB, E.LOC, P,
    P + E.s + 1, P + 2 * E.s + 1, P + 3 * E.s + 1, P + 4 * E.s + 1, P + 5 * E.s + 1,
    P + 6 * E.s + 1, P + 7 * E.s + 1⟩

end DWE

namespace Rec

variable {T : KT} {G : PG} {c : Cl} {R : Rec}

/-- The setting of the first run: the record in memory, the memory `mem1` after `arcP`, and the
state `x` of Dijkstra at the end, in the memory `M`. -/
structure First (w : ℕ) (T : KT) (G : PG) (c : Cl) (R : Rec) (E : DWE) (mem M : ℕ → ℕ) : Prop where
  hM : Mem T G c R E.ap.toAF mem
  ok : R.OkW T G c
  hD : c.Δ G ≤ E.D
  hINF : c.Δ G < E.INF
  hx0 : E.x0 = R.sv T c c.x0
  run : ∃ v1 mem1 M3 x, (arcPC w).post E.ap.args mem v1 mem1 ∧ (∀ a < E.TS, M3 a = mem1 a) ∧
    RunI w E.RG M3 x M ∧ (∀ cl, x.2.1 cl = []) ∧
    (∀ a, (a < E.TS ∨ E.Rr + 2 ≤ a) → M a = mem1 a) ∧
    ∀ a, (a < E.H ∨ drawEnd E ≤ a) → M a = mem a

variable {w : ℕ} {E : DWE} {mem M : ℕ → ℕ}

/-- **The distances.** At the end of the first run, the cost cell of the node of each vertex holds
its distance to the center, with the stamp of the run. -/
theorem First.fd (h : First w T G c R E mem M) {a : ℕ} (ha : a ∈ c.X) :
    M (E.TS + R.sv T c a) = 1 ∧ M (E.TS + (E.s + 1) + R.sv T c a) = c.d G c.x0 a := by
  obtain ⟨v1, mem1, M3, x, hp1, hlow, hI, hE, -, -⟩ := h.run
  obtain ⟨hctr, -⟩ := arcP_outW hp1 h.hM h.ok h.hD
  have hg : E.L.g M3 = E.ap.g mem1 := by
    show E.ap.g M3 = E.ap.g mem1
    exact E.g_congr hlow
  obtain ⟨-, hrep, hinv, hdone, -⟩ := hI
  have hinv' : (E.ap.g mem1).Inv (R.sv T c c.x0) E.INF x.2.2.1 x.2.2.2 x.1 := by
    have := hinv; simp only [DWE.RG] at this; rw [hg, h.hx0] at this; exact this
  have hdone' : x.1.sett x.2.2.1 → (E.ap.g mem1).hi x.2.2.1 ≤ x.2.2.2 := by
    have := hdone; simp only [DWE.RG] at this; rw [hg] at this; exact this
  have hQ : x.1.Q = [] := by
    rw [hrep.Q]
    refine List.eq_nil_iff_forall_not_mem.mpr fun e he => ?_
    obtain ⟨cl, -, hcl⟩ := mem_pqAll.mp he
    rw [hE cl] at hcl
    exact List.not_mem_nil hcl
  have hs : E.s = R.nodes.length := h.hM.s
  have hsv : R.sv T c a < E.s := by rw [hs]; exact h.ok.sv_lt ha
  have ht := (hctr.tent_eq h.ok.good.conn hinv' hdone' hQ h.hINF ha).2
  have hle := c.d_le_Δ (G := G) ha
  rw [hrep.tent, if_pos (by simp only [DWE.RG, Finset.mem_range]; exact hsv)] at ht
  unfold DL.tentOf at ht
  change (if M (E.TS + R.sv T c a) = 1 then M (E.TS + (E.s + 1) + R.sv T c a) else E.INF) = _
    at ht
  have hINF := h.hINF
  split_ifs at ht with h1
  · exact ⟨h1, ht⟩
  · omega


/-- **The parent arcs.** At the end of the first run, every node `u` other than the node of the
center has its parent below `s`, and the values that `treeP` writes for `u` are a pair between a
vertex of `u` and a vertex of the parent, along which the distance drops by its positive length.
The cells that `treeP` reads for `u` are below the heap pointer or among the arrays of the run. -/
theorem First.edge (h : First w T G c R E mem M) {m n NL : ℕ} (hAP : E.ap.Pre w mem m n NL)
    (hSA : E.SA + 2 * E.nS ≤ E.H) (P : ℕ) {u : ℕ} (hu : u < E.s) (hux : u ≠ E.x0) :
    (E.tf P).vPAR M u < E.s ∧ (E.tf P).vPA M u ∈ c.X ∧ R.sv T c ((E.tf P).vPA M u) = u ∧
    (E.tf P).vPB M u ∈ c.X ∧ R.sv T c ((E.tf P).vPB M u) = (E.tf P).vPAR M u ∧
    G.Joins ((E.tf P).vPP M u) ((E.tf P).vPA M u) ((E.tf P).vPB M u) ∧
    c.d G c.x0 ((E.tf P).vPA M u) = c.d G c.x0 ((E.tf P).vPB M u) + c.len G ((E.tf P).vPP M u) ∧
    0 < c.len G ((E.tf P).vPP M u) ∧ (E.tf P).vSC M u = c.len G ((E.tf P).vPP M u) ∧
    (E.tf P).vPF M u = (if (E.tf P).vPP M u ∈ c.half then 1 else 0) ∧
    (E.tf P).vSK M u = E.ap.toAF.cl mem ((E.tf P).pj M u) ∧ (E.tf P).pj M u < E.nS ∧
    (E.tf P).pk M u < 2 * E.nS ∧ M (E.ap.ORD + (E.tf P).pk M u) < 2 * E.nS ∧
    (E.tf P).pp M u = E.ap.toAF.pr mem ((E.tf P).pj M u) ∧ (E.tf P).pp M u < m ∧
    (E.tf P).e0 M u < n ∧ M (E.LAB + (E.tf P).e0 M u) < NL := by
  obtain ⟨v1, mem1, M3, x, hp1, hlow, hI, hE, hM1, hM0⟩ := h.run
  obtain ⟨hctr, hokg, hrng, -⟩ := arcP_outW hp1 h.hM h.ok h.hD
  obtain ⟨-, hper, -, -, -, -, -, hitem, -⟩ := hp1 E.ap rfl
  have hg : E.L.g M3 = E.ap.g mem1 := by
    show E.ap.g M3 = E.ap.g mem1
    exact E.g_congr hlow
  obtain ⟨-, hrep, hinv, hdone, -, hpar, -⟩ := hI
  have hinv' : (E.ap.g mem1).Inv (R.sv T c c.x0) E.INF x.2.2.1 x.2.2.2 x.1 := by
    have := hinv; simp only [DWE.RG] at this; rw [hg, h.hx0] at this; exact this
  have hdone' : x.1.sett x.2.2.1 → (E.ap.g mem1).hi x.2.2.1 ≤ x.2.2.2 := by
    have := hdone; simp only [DWE.RG] at this; rw [hg] at this; exact this
  have hpar' : (E.ap.g mem1).ParInv E.x0 E.INF x.1 (E.L.par M) (E.L.parc M) := by
    have := hpar; simp only [DWE.RG] at this; rw [hg] at this; exact this
  have hQ : x.1.Q = [] := by
    rw [hrep.Q]
    refine List.eq_nil_iff_forall_not_mem.mpr fun e he => ?_
    obtain ⟨cl, -, hcl⟩ := mem_pqAll.mp he
    rw [hE cl] at hcl
    exact List.not_mem_nil hcl
  have hs : E.s = R.nodes.length := h.hM.s
  have hnS : E.ap.nS = E.nS := rfl
  have hapS : E.ap.s = E.s := rfl
  have htent : ∀ y ∈ c.X, x.1.tent (R.sv T c y) = c.d G c.x0 y := fun y hy =>
    (hctr.tent_eq h.ok.good.conn hinv' hdone' hQ h.hINF hy).2
  obtain ⟨a, ha, rfl⟩ := h.ok.exists_of_node (hs ▸ hu)
  have hlt : x.1.tent (R.sv T c a) < E.INF := by
    rw [htent a ha]; have := c.d_le_Δ (G := G) ha; have := h.hINF; omega
  obtain ⟨hq1, hq2, hq3, hq4, -, hq6⟩ := hpar' _ hux hlt
  set q := E.L.par M (R.sv T c a) with hqdef
  set k := E.L.parc M (R.sv T c a) with hkdef
  have hqs : q < E.s := by
    have := (hrep.sett q).mp hq1
    simpa [DWE.RG] using this.1
  have hlo : (E.ap.g mem1).lo q = mem1 (E.ap.OFF + q) := by
    simp only [AP.g, if_pos (show q < E.ap.s + 1 by omega)]
  have hhi : (E.ap.g mem1).hi q = mem1 (E.ap.OFF + 1 + q) := by
    simp only [AP.g, if_pos (show q < E.ap.s + 1 by omega)]
  have hk2 : k < 2 * E.nS := by
    have := (hrng q (by omega)).2; omega
  obtain ⟨hj, hkeep, hends, hcs, hcl⟩ :=
    hitem q (by omega) k (by rw [← hlo]; exact hq2) (by rw [← hhi]; exact hq3)
  set j := mem1 (E.ap.ORD + k) / 2 with hjdef
  have hhd : mem1 (E.ap.HD + k) = R.sv T c a := by
    have := hq4; simp only [AP.g, if_pos (show k < 2 * E.ap.nS by omega)] at this; exact this
  have hcsk : (E.ap.g mem1).cs k = mem1 (E.ap.CS + k) := by
    simp only [AP.g, if_pos (show k < 2 * E.ap.nS by omega)]
  have eTS : E.TS = E.H + 16 * E.nS + 3 * E.s + 4 := rfl
  have hORD : E.ap.ORD = E.H + 8 * E.nS + 2 * E.s + 3 := rfl
  have hCS : E.ap.CS = E.H + 12 * E.nS + 2 * E.s + 3 := rfl
  have hCL : E.ap.CL = E.H + 14 * E.nS + 2 * E.s + 3 := rfl
  have mO : M (E.ap.ORD + k) = mem1 (E.ap.ORD + k) := hM1 _ (Or.inl (by omega))
  have mC : M (E.ap.CS + k) = mem1 (E.ap.CS + k) := hM1 _ (Or.inl (by omega))
  have mL : M (E.ap.CL + k) = mem1 (E.ap.CL + k) := hM1 _ (Or.inl (by omega))
  have hpk : (E.tf P).pk M (R.sv T c a) = k := rfl
  have hpj : (E.tf P).pj M (R.sv T c a) = j := by
    show M (E.ap.ORD + (E.tf P).pk M (R.sv T c a)) / 2 = j; rw [hpk, mO]
  have hj' : j < R.S.length := h.hM.nS ▸ hj
  obtain ⟨hm, hpu, hpv, htop, hf1, hf2⟩ := h.ok.entry hj'
  have epr := h.hM.pr_eqW (F := E.ap.toAF) hj
  have efl := h.hM.fl_eqW (F := E.ap.toAF) hj
  rw [← epr] at hm hpu hpv htop hf2
  rw [← efl] at hf1 hf2
  have rIN := hAP.fill.rIN
  have rLAB := hAP.fill.rLAB
  have rLOC := hAP.fill.rLOC
  have hTL : E.ap.toAF.TL = E.H := rfl
  have mP : M (E.SA + 2 * j) = mem (E.SA + 2 * j) := hM0 _ (Or.inl (by omega))
  have mF : M (E.SA + 2 * j + 1) = mem (E.SA + 2 * j + 1) := hM0 _ (Or.inl (by omega))
  have hpp : (E.tf P).pp M (R.sv T c a) = E.ap.toAF.pr mem j := by
    show M (E.SA + 2 * (E.tf P).pj M (R.sv T c a)) = _; rw [hpj, mP]; rfl
  have hpf : (E.tf P).pf M (R.sv T c a) = E.ap.toAF.fl mem j := by
    show M (E.SA + 2 * (E.tf P).pj M (R.sv T c a) + 1) = _; rw [hpj, mF]; rfl
  have hen := h.hM.ends _ hm
  have hprm : E.ap.toAF.pr mem j < m := hAP.fill.pr_lt j hj
  have hGn := hAP.fill.ends _ hprm
  have mU : M (E.IN + 3 * E.ap.toAF.pr mem j) = mem (E.IN + 3 * E.ap.toAF.pr mem j) :=
    hM0 _ (Or.inl (by simp only [DWE.ap, AP.toAF] at rIN; omega))
  have mV : M (E.IN + 3 * E.ap.toAF.pr mem j + 1) = mem (E.IN + 3 * E.ap.toAF.pr mem j + 1) :=
    hM0 _ (Or.inl (by simp only [DWE.ap, AP.toAF] at rIN; omega))
  have he0 : (E.tf P).e0 M (R.sv T c a) = G.pu (E.ap.toAF.pr mem j) := by
    show M (E.IN + 3 * (E.tf P).pp M (R.sv T c a)) = _; rw [hpp, mU]; exact hen.1
  have he1 : (E.tf P).e1 M (R.sv T c a) = G.pv (E.ap.toAF.pr mem j) := by
    show M (E.IN + 3 * (E.tf P).pp M (R.sv T c a) + 1) = _; rw [hpp, mV]; exact hen.2
  have hlabu := (hAP.fill.lab j hj).1
  have hpun : G.pu (E.ap.toAF.pr mem j) < n := hen.1 ▸ hGn.1
  have mLU : M (E.LAB + G.pu (E.ap.toAF.pr mem j)) = mem (E.LAB + G.pu (E.ap.toAF.pr mem j)) :=
    hM0 _ (Or.inl (by simp only [DWE.ap, AP.toAF] at rLAB; omega))
  have hl0 : (E.tf P).l0 M (R.sv T c a) = R.sv T c (G.pu (E.ap.toAF.pr mem j)) := by
    show M (E.LOC + M (E.LAB + (E.tf P).e0 M (R.sv T c a))) = _
    rw [he0, mLU]
    have hlu : mem (E.LAB + G.pu (E.ap.toAF.pr mem j)) < NL := by
      have := hlabu; rw [hen.1] at this; exact this
    rw [hM0 _ (Or.inl (by simp only [DWE.ap, AP.toAF] at rLOC; omega))]
    exact h.hM.loc _ hpu
  have hea := h.hM.ea_eqW (F := E.ap.toAF) h.ok hj
  have heb := h.hM.eb_eqW (F := E.ap.toAF) h.ok hj
  have hne : R.sv T c (G.pu (E.ap.toAF.pr mem j)) ≠ R.sv T c (G.pv (E.ap.toAF.pr mem j)) :=
    fun e => h.ok.not_lconn hpu hpv htop ((h.ok.sv_iff hpu hpv).mp e)
  have hln := h.hM.ln_eqW (F := E.ap.toAF) h.ok hj
  have hlpos : 0 < E.ap.toAF.ln mem j := by
    rw [h.hM.ln_powW (F := E.ap.toAF) h.ok hj]; exact Nat.pos_of_ne_zero (by positivity)
  have hcost : x.1.tent q + mem1 (E.ap.CS + k) = x.1.tent (R.sv T c a) := by
    rw [← hcsk]; exact hq6
  have hux' : R.sv T c a ≠ (E.tf P).x0 := hux
  have hPAR : (E.tf P).vPAR M (R.sv T c a) = q := by
    unfold TF.vPAR; rw [if_neg hux']; rfl
  refine ⟨by rw [hPAR]; exact hqs, ?_⟩
  simp only [TF.vPA, TF.vPB, TF.vPP, TF.vPF, TF.vSC, TF.vSK, if_neg hux', hPAR, hl0, he0, he1,
    hpp, hpf]
  have hsc : (E.tf P).CS = E.ap.CS := rfl
  have hscl : (E.tf P).CL = E.ap.CL := rfl
  have hvsc : M ((E.tf P).CS + (E.tf P).pk M (R.sv T c a)) = c.len G (E.ap.toAF.pr mem j) := by
    rw [hsc, hpk, mC, hcs, hln]
  have hvsk : M ((E.tf P).CL + (E.tf P).pk M (R.sv T c a)) = E.ap.toAF.cl mem j := by
    rw [hscl, hpk, mL, hcl]
  rw [hvsc, hvsk, hpj]
  have hflag : E.ap.toAF.fl mem j = if E.ap.toAF.pr mem j ∈ c.half then 1 else 0 := by
    split_ifs with hh
    · exact hf2.mpr hh
    · by_contra h0; exact hh (hf2.mp (by omega))
  have hlab' : M (E.LAB + G.pu (E.ap.toAF.pr mem j)) < NL := by
    rw [mLU]; have := hlabu; rw [hen.1] at this; exact this
  rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · -- the arc goes along the pair from its first end to its second
    rw [hea] at e1
    rw [heb, hhd] at e2
    have hnl : ¬ R.sv T c (G.pu (E.ap.toAF.pr mem j)) = R.sv T c a := by
      rw [e2]; exact hne
    simp only [if_neg hnl]
    refine ⟨hpv, e2.symm, hpu, e1, ⟨hm, Or.inr ⟨rfl, rfl⟩⟩, ?_, by rw [← hln]; exact hlpos, (by first | rfl | trivial),
      hflag, (by first | rfl | trivial), hj, by rw [hpk]; exact hk2, by rw [hpk, mO]; omega,
      (by first | rfl | trivial), hprm,
      hpun, hlab'⟩
    have t1 := htent _ hpv
    have t2 := htent _ hpu
    rw [← e2] at t1
    rw [e1] at t2
    rw [hcs] at hcost
    rw [← hln]; omega
  · rw [heb] at e1
    rw [hea, hhd] at e2
    have hnl : R.sv T c (G.pu (E.ap.toAF.pr mem j)) = R.sv T c a := e2.symm
    simp only [if_pos hnl]
    refine ⟨hpu, hnl, hpv, e1, ⟨hm, Or.inl ⟨rfl, rfl⟩⟩, ?_, by rw [← hln]; exact hlpos, (by first | rfl | trivial),
      hflag, (by first | rfl | trivial), hj, by rw [hpk]; exact hk2, by rw [hpk, mO]; omega,
      (by first | rfl | trivial), hprm,
      hpun, hlab'⟩
    have t1 := htent _ hpu
    have t2 := htent _ hpv
    rw [hnl] at t1
    rw [e1] at t2
    rw [hcs] at hcost
    rw [← hln]; omega

end Rec

end MinCostFlow.LowStretch
