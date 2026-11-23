module

public import MinCostFlow.LowStretch.PSearchStep

/-!
# Facts for a step that settles a node

When `dijStep` settles `u`, the settle phase of `pstep` writes five kinds of cells: the settled
list, the count, the last key, the highway pointer and, at most once, a slot. The lemmas
`PSG.setM_*` give the memory after the settle phase cell by cell.

The facts of the search:
* the key of `u` is the least key of the queue before the step (`Inv.key_eq`);
* if `u` is on the highway, it is the node `H[j]` of the pointer (`Ok.hw_order`): a later node
  `H[i]` costs more than `H[j]`, which is not settled;
* the buckets: every bucket from `q` on fails below the new key (`Inv.settle_buckets`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PSG

variable {X : PSG} {mem1 mem2 : ℕ → ℕ}

theorem setM_ne {x : ℕ} (h1 : x ≠ X.SL + mem1 (X.CTL + 1)) (h2 : x ≠ X.CTL + 1)
    (h3 : x ≠ X.CTL + 3) (h4 : x ≠ X.CTL + 2)
    (h5 : X.u mem1 = mem1 (X.CTL + 2) → mem1 (X.NXT + X.u mem1) < X.S →
      x ≠ X.G.L.HD + (mem1 (X.G.L.HI + mem1 (X.NXT + X.u mem1)) - 1)) :
    X.setM mem1 mem2 x = mem2 x := by
  unfold setM
  split_ifs with e1 e2
  · simp only [Function.update_apply, if_neg (h5 e1 e2), if_neg h4, if_neg h3, if_neg h2,
      if_neg h1]
  · simp only [Function.update_apply, if_neg h4, if_neg h3, if_neg h2, if_neg h1]
  · simp only [Function.update_apply, if_neg h3, if_neg h2, if_neg h1]

theorem setM_SL (h2 : X.SL + mem1 (X.CTL + 1) ≠ X.CTL + 1)
    (h3 : X.SL + mem1 (X.CTL + 1) ≠ X.CTL + 3) (h4 : X.SL + mem1 (X.CTL + 1) ≠ X.CTL + 2)
    (h5 : X.SL + mem1 (X.CTL + 1) ≠ X.G.L.HD + (mem1 (X.G.L.HI + mem1 (X.NXT + X.u mem1)) - 1)) :
    X.setM mem1 mem2 (X.SL + mem1 (X.CTL + 1)) = X.u mem1 := by
  unfold setM
  split_ifs with e1 e2
  · simp only [Function.update_apply, if_neg h5, if_neg h4, if_neg h3, if_neg h2, if_true]
  · simp only [Function.update_apply, if_neg h4, if_neg h3, if_neg h2, if_true]
  · simp only [Function.update_apply, if_neg h3, if_neg h2, if_true]

theorem setM_C1 (h5 : X.CTL + 1 ≠ X.G.L.HD + (mem1 (X.G.L.HI + mem1 (X.NXT + X.u mem1)) - 1)) :
    X.setM mem1 mem2 (X.CTL + 1) = mem1 (X.CTL + 1) + 1 := by
  have h3 : X.CTL + 1 ≠ X.CTL + 3 := by omega
  have h4 : X.CTL + 1 ≠ X.CTL + 2 := by omega
  unfold setM
  split_ifs with e1 e2
  · simp only [Function.update_apply, if_neg h5, if_neg h4, if_neg h3, if_true]
  · simp only [Function.update_apply, if_neg h4, if_neg h3, if_true]
  · simp only [Function.update_apply, if_neg h3, if_true]

theorem setM_C3 (h5 : X.CTL + 3 ≠ X.G.L.HD + (mem1 (X.G.L.HI + mem1 (X.NXT + X.u mem1)) - 1)) :
    X.setM mem1 mem2 (X.CTL + 3) = mem1 X.G.R := by
  have h4 : X.CTL + 3 ≠ X.CTL + 2 := by omega
  unfold setM
  split_ifs with e1 e2
  · simp only [Function.update_apply, if_neg h5, if_neg h4, if_true]
  · simp only [Function.update_apply, if_neg h4, if_true]
  · simp only [Function.update_apply, if_true]

theorem setM_C2 (h5 : X.CTL + 2 ≠ X.G.L.HD + (mem1 (X.G.L.HI + mem1 (X.NXT + X.u mem1)) - 1))
    (h1 : X.CTL + 2 ≠ X.SL + mem1 (X.CTL + 1)) :
    X.setM mem1 mem2 (X.CTL + 2) =
      if X.u mem1 = mem1 (X.CTL + 2) then mem1 (X.NXT + X.u mem1) else mem2 (X.CTL + 2) := by
  have h2 : X.CTL + 2 ≠ X.CTL + 1 := by omega
  have h3 : X.CTL + 2 ≠ X.CTL + 3 := by omega
  unfold setM
  split_ifs with e1 e2
  · simp only [Function.update_apply, if_neg h5, if_true]
  · simp only [Function.update_apply, if_true]
  · simp only [Function.update_apply, if_neg h3, if_neg h2, if_neg h1]

theorem setM_HD (e1 : X.u mem1 = mem1 (X.CTL + 2)) (e2 : mem1 (X.NXT + X.u mem1) < X.S) :
    X.setM mem1 mem2 (X.G.L.HD + (mem1 (X.G.L.HI + mem1 (X.NXT + X.u mem1)) - 1)) =
      mem1 (X.NXT + mem1 (X.NXT + X.u mem1)) := by
  rw [setM_1 e1 e2, Function.update_self]

end PSG

namespace SC

variable {C : SC} {w : ℕ} {a : SG} {mem : ℕ → ℕ}

theorem Ok.hv_inj (h : C.Ok w) {i i' : ℕ} (hi : i < C.H.length) (hi' : i' < C.H.length)
    (he : C.hv i = C.hv i') : i = i' := by
  unfold hv at he
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at he
  exact (List.Nodup.getElem_inj_iff h.Hnd).mp he

theorem Ok.nx_eq (h : C.Ok w) {j : ℕ} (hj : j < C.H.length) :
    C.nx j = if j + 1 < C.H.length then C.hv (j + 1) else C.X.S := by
  rw [h.hnx j hj]
  split_ifs with h1
  · exact List.getD_append _ _ _ _ h1
  · rw [show j + 1 = C.H.length by omega, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
    rfl

/-- A node at the pointer is the highway node `H[j]`. -/
theorem Inv.ptr_hv (h : C.Ok w) (hI : C.Inv w a mem) {u : ℕ} (hu : u = mem (C.X.CTL + 2))
    (huN : u ∈ C.X.G.Nodes) : a.j < C.H.length ∧ u = C.hv a.j := by
  rw [hI.ptr] at hu
  by_cases hj : a.j < C.H.length
  · refine ⟨hj, ?_⟩
    rw [hu, List.getD_append _ _ _ _ hj]; rfl
  · have hj' : a.j = C.H.length := by have := hI.jle; omega
    rw [hj', List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self] at hu
    have hS : u = C.X.S := hu
    exact absurd ((hI.okN_iff h u).mpr huN) (hS ▸ h.Sok)

/-- **The key of a settled node** is the least key of the queue before the step. -/
theorem Inv.key_eq (hI : C.Inv w a mem) {u k : ℕ} (hns : ¬ a.d.sett u)
    (hr : (C.L.g mem).Reach C.X.G.s u k) (hk : k < C.L.INF) (hmin : ∀ e ∈ a.d.Q, k ≤ e.1) :
    k = mem (C.L.D + 4) / C.L.J := by
  obtain ⟨hK, hLK, hQ⟩ := hI.kmin
  have h1 := (hI.inv.path hI.done hK hLK hQ hr).2 hns
  have hroot := hI.rep.pq.root_spec
  rw [show C.L.D + 3 + 1 = C.L.D + 4 from rfl] at hroot
  unfold kq at h1
  have hlt : mem (C.L.D + 4) / C.L.J < C.L.INF := by omega
  obtain ⟨e, rest, he, he1, hc, -⟩ := hroot.1 hlt
  have hmem : e ∈ a.d.Q := by
    rw [hI.rep.Q]; exact mem_pqAll.mpr ⟨_, hc, by rw [he]; exact List.mem_cons_self⟩
  have h2 := hmin e hmem
  rw [he1] at h2
  have h3 : min (mem (C.L.D + 4) / C.L.J) C.L.INF ≤ k := h1
  clear hroot hmin hQ hK hLK he hr
  omega

/-- **The highway nodes settle in order.** While `H[j]` is not settled, no later `H[i]` is. -/
theorem Ok.hw_order (h : C.Ok w) {j u pos : ℕ} {d : DS}
    (hinv : (C.gC j).Inv C.X.G.s C.L.INF u pos d) (hdone : d.sett u → (C.gC j).hi u ≤ pos)
    (hu : d.sett u) (hj : j < C.H.length) (hnj : ¬ d.sett (C.hv j)) {i : ℕ}
    (hi : i < C.H.length) (hji : j < i) (hui : u = C.hv i) : False := by
  have hw : (C.gC j).Reach C.X.G.s (C.hv j) (C.hc j) :=
    h.reach_gC (h.hhc j hj).1 fun i' h1 h2 => h.hc_lt h1 h2
  have h1 := (hinv.path hdone hinv.L_lt.le le_rfl (fun e he => (hinv.keys e he).1) hw).2 hnj
  have htu := hinv.cur_L hu
  have hru := hinv.reach u (by rw [htu]; exact hinv.L_lt)
  have hrF : C.gF.Reach C.X.G.s u (d.tent u) := hru.sub fun _ _ _ ha => h.gC_arc ha
  rw [hui] at hrF
  have h2 := (h.hhc i hi).2 _ hrF
  have h3 := h.hc_lt hji hi
  rw [← hui] at h2
  omega

theorem Inv.bF (h : C.Ok w) : C.X.bw = C.c.bw C.G C.P := h.hbw

/-- **The buckets after a settle at the least key `D'`.** -/
theorem Inv.settle_buckets (h : C.Ok w) (hI : C.Inv w a mem)
    (hT : (C.Xf a).TB mem → ¬ ((C.Xf a).pt mem).Pass mem ∧ (C.Xf a).k mem ≤ (C.Xf a).bq mem)
    {D' : ℕ} (hkey : D' = mem (C.L.D + 4) / C.L.J) (hDI : D' < C.L.INF) :
    (a.q ≤ C.X.Lb → D' ≤ C.X.lo + a.q * C.X.bw) ∧
      ∀ q, a.q ≤ q → q ≤ C.X.Lb → C.BF q D' := by
  have hbw := h.hbw
  have hRm := h.hRm
  have hINF := h.hINF
  have hkq : C.kq mem = D' := by unfold kq; omega
  have hq1 := hI.q1
  -- when the test is made, it failed with the least key inside bucket `q`
  have hTB : a.q < C.X.Lb + 1 → C.X.lo + (a.q - 1) * C.X.bw < D' → a.d.L < D' →
      ¬ ((C.Xf a).pt mem).Pass mem ∧ D' ≤ C.X.lo + a.q * C.X.bw := by
    intro t1 t2 t3
    have hT' : (C.Xf a).TB mem := hI.tb_iff.mpr ⟨t1, by omega, by omega⟩
    have := hT hT'
    rw [k_eq, hI.bq_eq, ← hkey] at this
    exact this
  refine ⟨fun hqL => ?_, fun q h1 h2 => ?_⟩
  · by_cases hle : D' ≤ a.d.L
    · exact hle.trans (hI.qd hqL)
    · by_cases hb : C.X.lo + (a.q - 1) * C.X.bw < D'
      · exact (hTB (by omega) hb (by omega)).2
      · have : (a.q - 1) * C.X.bw ≤ a.q * C.X.bw := Nat.mul_le_mul_right _ (by omega)
        omega
  · by_cases hle : D' ≤ a.d.L
    · exact Cl.BFail.mono (hI.bnow q h1 h2) hle
    · refine Cl.BFail.step2 h.hGo h.link.conn h.link.hY (hI.bnow q h1 h2) ?_ ?_
      · intro r r1 r2 r3
        rw [← hbw] at r3 ⊢
        have hm : a.q * C.X.bw ≤ (C.X.Lb + 1) * C.X.bw := Nat.mul_le_mul_right _ (by omega)
        have hm' : q * C.X.bw ≤ (C.X.Lb + 1) * C.X.bw := Nat.mul_le_mul_right _ (by omega)
        rw [hI.carve h (by omega) r1 (by omega),
          hI.carve h (by omega) (by omega) (by omega)]
      · intro t2 _
        rw [← hbw] at t2 ⊢
        have hm : (a.q - 1) * C.X.bw ≤ (q - 1) * C.X.bw := Nat.mul_le_mul_right _ (by omega)
        obtain ⟨hP, hk⟩ := hTB (by omega) (by omega) (by omega)
        have hqq : q = a.q := by
          by_contra hne
          have : a.q * C.X.bw ≤ (q - 1) * C.X.bw := Nat.mul_le_mul_right _ (by omega)
          omega
        subst hqq
        have hT' : (C.Xf a).TB mem := hI.tb_iff.mpr ⟨by omega, by omega, by omega⟩
        have hrr : (C.Xf a).rr mem = D' - 1 := by
          rw [PSG.rr_of_ge _ _ (by rw [hI.bq_eq, k_eq, ← hkey]; omega), k_eq, ← hkey]
        rw [show min (D' - 1) (C.X.lo + a.q * C.X.bw) = D' - 1 by omega, ← hrr]
        exact fun ht => hP ((hI.pass h hT').mpr ht)

end SC

end MinCostFlow.LowStretch
