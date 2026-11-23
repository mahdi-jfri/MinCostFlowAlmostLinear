module

public import MinCostFlow.LowStretch.ProgClusterAfter

/-!
# One petal of a cluster, as a procedure

`petalP` runs one petal: it turns on the slot of the target, runs the search `psrchA`, carves the
settled nodes with `pfin`, and finds the start of the portal with `portP`, which it stores in the
cell `CTL + 3`. It returns the value of the search (the radius plus `2`).

This file proves the end of `petalP`, after the search (`petalTail_runs`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The end of `petalP`, after the search: carve, find the portal, store it, return. -/
def petalTail (bF bT : ℕ) : Stmt :=
  .seq (.call 35 bF [.reg 9, .reg 10, .reg 5, .reg 6, .reg 29, .reg 31, .reg 30])
  (.seq (.call 35 bT [.reg 28, .reg 32, .load (.bin .add (.reg 31) (.const 2))])
  (.seq (.store (.bin .add (.reg 31) (.const 3)) (.reg 35))
  (.ret (.reg 34))))

/-- `petalP` with the `33` arguments of `psrchA`. Procedures `bS`, `bF` and `bT` are `psrchA`,
`pfin` and `portP`. -/
def petalP (bS bF bT : ℕ) : Stmt :=
  .seq (.assign 33 (.load (.bin .add (.reg 5) (.reg 32))))
  (.seq (.store (.bin .add (.reg 6) (.bin .sub (.reg 33) (.const 1)))
    (.load (.bin .add (.reg 28) (.reg 32))))
  (.seq (.call 34 bS [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8,
    .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 14, .reg 15, .reg 16, .reg 17, .reg 18,
    .reg 19, .reg 20, .reg 21, .reg 22, .reg 23, .reg 24, .reg 25, .reg 26, .reg 27, .reg 28,
    .reg 29, .reg 30, .reg 31, .reg 32])
  (petalTail bF bT)))

theorem petalP_noRand (bS bF bT : ℕ) : (petalP bS bF bT).NoRand := by
  simp [petalP, petalTail, Stmt.NoRand]

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {t : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ}
  {lo rs : ℕ}

/-- The arguments of the search, as a list. -/
noncomputable def pargs (W : PW) (mem : ℕ → ℕ) (t : ℕ) (st : List (ℕ × ℕ × ℕ)) (hw : List ℕ)
    (lo rs : ℕ) : List ℕ :=
  (W.sc mem t st hw lo rs).X.args ++ [W.sv t]

theorem pargs_eq : W.pargs mem t st hw lo rs =
    [W.L.D, W.L.J, W.L.A, W.L.INF, W.L.LO, W.L.HI, W.L.HD, W.L.CS, W.L.CL, W.L.OK, W.L.os, W.L.TS,
      W.L.NN, rs, W.RR, W.ORD, W.AS, W.EXP, W.Es, W.SUM, W.M, W.κ, W.nact, lo, W.bw, W.Lb, W.SQ,
      W.P2, W.NXT, W.SL, W.s, W.CTL, W.sv t] := rfl

theorem pargs_getD (i : ℕ) : (W.pargs mem t st hw lo rs).getD i 0 =
    [W.L.D, W.L.J, W.L.A, W.L.INF, W.L.LO, W.L.HI, W.L.HD, W.L.CS, W.L.CL, W.L.OK, W.L.os, W.L.TS,
      W.L.NN, rs, W.RR, W.ORD, W.AS, W.EXP, W.Es, W.SUM, W.M, W.κ, W.nact, lo, W.bw, W.Lb, W.SQ,
      W.P2, W.NXT, W.SL, W.s, W.CTL, W.sv t].getD i 0 := by rw [pargs_eq]

/-- The walk along `NXT` follows the highway nodes, in every memory that agrees on `NXT`. -/
theorem PS.pIt_eq' (hp : W.PS w mem t st hw lo) {M : ℕ → ℕ}
    (hM : ∀ v < W.L.NN, M (W.NXT + v) = mem (W.NXT + v)) (hs : ∀ u ∈ W.Hl t st, u < W.L.NN)
    {k : ℕ} (hk : k ≤ st.length) : pIt M W.NXT (W.sv t) k = (W.Hl t st).getD k 0 := by
  have hlen : (W.Hl t st).length = st.length + 1 := Hl_length t st
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pIt_succ, ih (by omega), hM _ (hs _ (getD_mem' (by omega))), Hl_getD t st (by omega),
      hp.nxt k (by omega), Hl_getD t st hk]

theorem PS.portOk' (hp : W.PS w mem t st hw lo) {M : ℕ → ℕ}
    (hM : ∀ v < W.L.NN, M (W.NXT + v) = mem (W.NXT + v)) (hs : ∀ u ∈ W.Hl t st, u < W.L.NN)
    {m : ℕ} (hm : m < st.length) :
    PortOk M W.NXT (W.sv t) ((W.Hl t st).getD (m + 1) 0) m := by
  have hlen : (W.Hl t st).length = st.length + 1 := Hl_length t st
  refine ⟨?_, fun k hk => ?_⟩
  · rw [← pIt_succ M W.NXT (W.sv t) m, hp.pIt_eq' hM hs hm]
  · rw [← pIt_succ M W.NXT (W.sv t) k, hp.pIt_eq' hM hs (by omega)]
    intro e
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
    have := (List.Nodup.getElem_inj_iff hp.nd).mp e
    omega

set_option maxHeartbeats 4000000 in
/-- **The end of a petal.** -/
theorem Ok.petalTail_runs {p : Program} {bF bT : ℕ} (hF : MeetsContract w p bF (pfinC w))
    (hT : MeetsContract w p bT (portC w)) (h : W.Ok w mem) (hp : W.PS w mem t st hw lo)
    {a : SG} {memL memC : ℕ → ℕ} (hI : (W.sc mem t st hw lo rs).Inv w a memL)
    (hclr : (W.sc mem t st hw lo rs).SClr memL memC) {m : ℕ} (hm : m < st.length)
    (hj : m + 1 = a.j) (sx : State)
    (hreg : ∀ i < 33, sx.regs i = (W.pargs mem t st hw lo rs).getD i 0) (hmx : sx.mem = memC)
    (hwA : ∀ x ∈ W.pargs mem t st hw lo rs, x < 2 ^ w) (ω : ℕ → Bool) :
    ∃ o st' c, Runs w p ω (petalTail bF bT) sx o st' c ∧
      (o = .returned (sx.regs 34) ∧ st'.mem (W.CTL + 3) = (W.Hl t st).getD m 0 ∧
        (∀ i < a.ℓ.length, st'.mem (W.L.OK + a.ℓ.getD i 0) = W.L.os + 1 ∧
          st'.mem (W.L.HD + (mem (W.L.HI + a.ℓ.getD i 0) - 1)) = W.s) ∧
        st'.mem (W.L.HD + (mem (W.L.HI + (W.Hl t st).getD (m + 1) 0) - 1)) = W.s ∧
        ∀ x, x ≠ W.CTL + 3 → (∀ i < a.ℓ.length, x ≠ W.L.OK + a.ℓ.getD i 0 ∧
          x ≠ W.L.HD + (mem (W.L.HI + a.ℓ.getD i 0) - 1)) →
          x ≠ W.L.HD + (mem (W.L.HI + (W.Hl t st).getD (m + 1) 0) - 1) → st'.mem x = memC x) ∧
      c ≤ 100 * a.ℓ.length + 20 * (m + 1) + 300 := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hES := h.lES; have hNN := h.hNN; have hR := h.hR; have hCTL := h.hCTL
  have hSUM := h.hSUM; have hSL := h.hSL; have wSL := h.wSL; have wos := h.os_lt
  have hlen : (W.Hl t st).length = st.length + 1 := Hl_length t st
  have gl : ∀ i < 33, sx.regs i = (W.pargs mem t st hw lo rs).getD i 0 := hreg
  have e5 : sx.regs 5 = W.L.HI := by rw [gl 5 (by omega), pargs_getD]; rfl
  have e6 : sx.regs 6 = W.L.HD := by rw [gl 6 (by omega), pargs_getD]; rfl
  have e9 : sx.regs 9 = W.L.OK := by rw [gl 9 (by omega), pargs_getD]; rfl
  have e10 : sx.regs 10 = W.L.os := by rw [gl 10 (by omega), pargs_getD]; rfl
  have e28 : sx.regs 28 = W.NXT := by rw [gl 28 (by omega), pargs_getD]; rfl
  have e29 : sx.regs 29 = W.SL := by rw [gl 29 (by omega), pargs_getD]; rfl
  have e30 : sx.regs 30 = W.s := by rw [gl 30 (by omega), pargs_getD]; rfl
  have e31 : sx.regs 31 = W.CTL := by rw [gl 31 (by omega), pargs_getD]; rfl
  have e32 : sx.regs 32 = W.sv t := by rw [gl 32 (by omega), pargs_getD]; rfl
  have hs0 : 0 < W.s := by have := h.sv_lt h.conn.1; omega
  have hMM : 1 ≤ W.L.MM := by
    have := h.lohi 0 hs0; have := h.hiMM 0 (by omega); omega
  have wNXT := h.wNXT
  obtain ⟨c1, c2, c3⟩ := h.after_ctl hI hclr
  have hHs : ∀ u ∈ W.Hl t st, u < W.s := fun u hu => h.H_lt hp hu
  have hpp : memC (W.CTL + 2) = (W.Hl t st).getD (m + 1) 0 := by
    rw [c2, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD, hj]
  have hppS : (W.Hl t st).getD (m + 1) 0 < W.s := hHs _ (getD_mem' (by omega))
  have hfix : ∀ v < W.L.NN, memC (W.NXT + v) = mem (W.NXT + v) ∧
      memC (W.L.HI + v) = mem (W.L.HI + v) ∧ memC (W.L.LO + v) = mem (W.L.LO + v) ∧
      memC (W.L.OK + v) = mem (W.L.OK + v) := fun v hv => h.after_fix hp hI hclr hv
  have hℓ : ∀ v ∈ a.ℓ, v ∈ W.Nodes mem ∧ v < W.s := fun v hv => h.sett_lt hI hv
  have hℓlen := h.sett_len hI
  have hsl : ∀ i < a.ℓ.length, memC (W.SL + i) < W.L.NN := fun i hi => by
    rw [c3 i hi]
    have := (hℓ (a.ℓ.getD i 0) (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)).2
    omega
  let F : FF := ⟨W.L.OK, W.L.os, W.L.HI, W.L.HD, W.SL, W.CTL, W.s⟩
  have hFpre : F.Pre memC w W.L.NN W.L.MM := {
    vN := fun i hi => by
      change i < memC (W.CTL + 1) at hi
      rw [c1] at hi
      exact hsl i hi
    pN := fun hx => by
      change memC (W.CTL + 2) < W.s at hx
      change memC (W.CTL + 2) < W.L.NN
      omega
    hiM := fun u hu => by
      change memC (W.L.HI + u) ≤ W.L.MM
      rw [(hfix u hu).2.1]; exact h.hiMM u hu
    l1 := l2
    l2 := by change W.L.HD + W.L.MM < W.L.OK; omega
    l3 := by change W.L.OK + W.L.NN ≤ W.CTL; omega
    l4 := by change W.CTL + 3 ≤ W.SL; omega
    l5 := by change W.SL + memC (W.CTL + 1) < 2 ^ w; rw [c1]; omega
    wos := wos
    wS := by change W.s < 2 ^ w; omega }
  refine runs_start_le ?_
  dsimp only [petalTail]
  have wC : W.CTL + 3 < 2 ^ w := by omega
  have wH : (W.Hl t st).getD (m + 1) 0 < 2 ^ w := by omega
  have hHN : ∀ u ∈ W.Hl t st, u < W.L.NN := fun u hu => by have := hHs u hu; omega
  wram_step
  · rw [hmx]; exact ⟨F, W.L.NN, W.L.MM, rfl, hFpre⟩
  intro v2 mem2 pos2 hpost
  rw [hmx] at hpost
  obtain ⟨p1, p2, p3⟩ := hpost F rfl
  have hns : F.ns memC = a.ℓ.length := c1
  have hv : ∀ j, F.v memC j = memC (W.SL + j) := fun _ => rfl
  have hsa : ∀ u < W.L.NN, F.sa memC u = W.L.HD + (mem (W.L.HI + u) - 1) := fun u hu => by
    show W.L.HD + (memC (W.L.HI + u) - 1) = _
    rw [(hfix u hu).2.1]
  have hsaR : ∀ u < W.L.NN, F.sa memC u < W.L.HD + W.L.MM := fun u hu => by
    rw [hsa u hu]; have := h.hiMM u hu; omega
  have hkeep : ∀ x, ¬ (W.L.HD ≤ x ∧ x < W.L.HD + W.L.MM) → ¬ (W.L.OK ≤ x ∧ x < W.L.OK + W.L.NN) →
      mem2 x = memC x := by
    intro x h1 h2
    refine p3 x ?_ ?_
    · rintro ⟨j, hj, hx | hx⟩
      · rw [hns] at hj; have := hsl j hj; rw [← hv] at this
        exact h2 ⟨by rw [hx]; exact Nat.le_add_right _ _, by rw [hx]; change W.L.OK + _ < _; omega⟩
      · rw [hns] at hj; have := hsl j hj; rw [← hv] at this
        have := hsaR _ this
        exact h1 ⟨by rw [hx]; show W.L.HD ≤ W.L.HD + _; omega, by rw [hx]; exact this⟩
    · intro hlt hx
      have hpn : F.pp memC < W.L.NN := by change memC (W.CTL + 2) < W.L.NN; omega
      have := hsaR _ hpn
      exact h1 ⟨by rw [hx]; show W.L.HD ≤ W.L.HD + _; omega, by rw [hx]; exact this⟩
  have q1 : mem2 (W.CTL + 2) = (W.Hl t st).getD (m + 1) 0 := by
    rw [hkeep _ (by omega) (by omega)]; exact hpp
  have q2 : ∀ v < W.L.NN, mem2 (W.NXT + v) = mem (W.NXT + v) := fun v hv => by
    rw [hkeep _ (by omega) (by omega)]; exact (hfix v hv).1
  have hpo := hp.portOk' q2 hHN hm
  have hpi : ∀ k ≤ st.length, pIt mem2 W.NXT (W.sv t) k = (W.Hl t st).getD k 0 :=
    fun k hk => hp.pIt_eq' q2 hHN hk
  have hb : ∀ k' ≤ m, W.NXT + pIt mem2 W.NXT (W.sv t) k' < 2 ^ w ∧
      pIt mem2 W.NXT (W.sv t) (k' + 1) < 2 ^ w := fun k' hk' => by
    rw [hpi k' (by omega), hpi (k' + 1) (by omega)]
    have := hHN _ (getD_mem' (show k' < (W.Hl t st).length by omega))
    have := hHN _ (getD_mem' (show k' + 1 < (W.Hl t st).length by omega))
    omega
  have wsv : W.sv t < 2 ^ w := by
    have := hHN _ (getD_mem' (show 0 < (W.Hl t st).length by omega)); change W.sv t < W.L.NN at this
    omega
  wram_step
  · exact ⟨W.NXT, W.sv t, (W.Hl t st).getD (m + 1) 0, m, by rw [q1], hpo, by omega, hb⟩
  intro v3 mem3 pos3 hpost
  obtain ⟨rfl, hv3⟩ := hpost
  have ev3 : v3 = (W.Hl t st).getD m 0 := by
    rw [hv3 _ _ _ m (by rw [q1]) hpo, hpi m hm.le]
  wram_step
  wram_step
  rotate_left
  · simp only [pfinC, portC, List.getD_cons_zero, List.getD_cons_succ, hmx, c1, q1,
      hpo.portK_eq]
    wram_cost
  dsimp only
  rw [e31]
  refine ⟨by simp, ?_, fun i hi => ?_, ?_, fun x hx1 hx2 hx3 => ?_⟩
  · simp [ev3]
  · have hj := hsl i hi
    rw [← c3 i hi]
    have hO := (p1 i (by rw [hns]; exact hi)).1
    have hS := (p1 i (by rw [hns]; exact hi)).2
    rw [hv, hsa _ hj] at hS
    rw [hv] at hO
    refine ⟨?_, ?_⟩
    · rw [Function.update_of_ne (by omega)]; exact hO
    · have := hsaR _ hj; rw [hsa _ hj] at this
      rw [Function.update_of_ne (by omega)]; exact hS
  · have hpn : F.pp memC < W.s := by change memC (W.CTL + 2) < W.s; omega
    have := p2 hpn
    have e : F.pp memC = (W.Hl t st).getD (m + 1) 0 := hpp
    rw [e, hsa _ (by omega)] at this
    have := hsaR _ (show (W.Hl t st).getD (m + 1) 0 < W.L.NN by omega)
    rw [hsa _ (by omega)] at this
    rw [Function.update_of_ne (by omega)]; assumption
  · rw [Function.update_of_ne hx1]
    refine p3 x ?_ ?_
    · rintro ⟨j, hj, hx | hx⟩
      · rw [hns] at hj; rw [hv, c3 j hj] at hx; exact (hx2 j hj).1 hx
      · rw [hns] at hj
        have hjN := hsl j hj
        rw [hv, hsa _ hjN, c3 j hj] at hx
        exact (hx2 j hj).2 hx
    · intro _ hx
      have e : F.pp memC = (W.Hl t st).getD (m + 1) 0 := hpp
      rw [e, hsa _ (by omega)] at hx
      exact hx3 hx


end PW

end MinCostFlow.LowStretch
