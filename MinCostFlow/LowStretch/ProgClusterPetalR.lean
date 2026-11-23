module

public import MinCostFlow.LowStretch.ProgClusterPetalP

/-!
# One petal of a cluster, as a run

`PW.Ok.petalP_runs`: for every bit stream, `petalP` runs one petal. The search finds a radius
(`SC.SFound`), the petal meets `PetalOk` with its portal at step `m` of the highway, the settled
nodes are carved, all the slots of the highway are off again, and `CTL + 3` holds the start
`H[m]` of the portal. The cost plus the measure of the stopped search is at most the measure of
its first state plus `O(J + log J)` plus a constant for each settled node.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- A call whose body is given by a run, at the start of a sequence. -/
theorem runs_seq_call_runs_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {s : Stmt} {st : State} {vs : List ℕ} {body : Stmt} {k T : ℕ} {Q : Outcome → State → Prop}
    (hargs : evalArgs w st args = some vs) (hb : p.procs[f]? = some body) {o₁ : Outcome}
    {st₁ : State} {c₁ : ℕ} (h₁ : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s { st₁ with regs := Function.update st.regs r o₁.value }
      o st' c₂ ∧ Q o st' ∧ (k + argsSize args + c₁ + 2) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c₂, hr₂, hq, hc⟩ := hrest
  exact ⟨o, st', (argsSize args + c₁ + 1) + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, c₂,
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hb, h₁, rfl, rfl, rfl⟩, hr₂, rfl⟩), hq,
    by omega⟩

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {t : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ}
  {lo rs : ℕ}

open Classical in
set_option maxHeartbeats 4000000 in
/-- **One petal, as a run.** The memory `mem` has every slot off; `mem1` is `mem` with the slot
of the target on. -/
theorem Ok.petalP_runs {p : Program} {bS bF bT bPush bPS bClr : ℕ}
    (hS : p.HasAt bS [psrchA bPush bPS bClr]) (hPush : MeetsContract w p bPush (pqPushC w))
    (hPS : MeetsContract w p bPS (pstepC w)) (hClr : MeetsContract w p bClr (pqClearC w))
    (hF : MeetsContract w p bF (pfinC w)) (hT : MeetsContract w p bT (portC w))
    {mem1 : ℕ → ℕ} (h : W.Ok w mem1) (hp : W.PS w mem1 t st hw lo) (hrs : rs < 2 ^ w)
    (hpq : PQRep mem1 W.L.D W.L.J W.L.A W.L.INF (fun _ => []))
    (htz : ∀ c < W.L.J, mem1 (pqT W.L.D W.L.J c) = 0)
    (hst : ∀ v < W.L.NN, mem1 (W.L.TS + v) < rs ∧ mem1 (W.L.TS + 2 * W.L.NN + v) < rs)
    (hmem : mem1 = Function.update mem (W.L.HD + W.slotA mem (W.sv t)) (mem (W.NXT + W.sv t)))
    (hwA : ∀ x ∈ W.pargs mem1 t st hw lo rs, x < 2 ^ w)
    (hd : lo + W.Lb * W.bw < W.c.d W.G W.c.x0 t) (pos : ℕ) (ω : ℕ → Bool) :
    ∃ o st' c, Runs w p ω (petalP bS bF bT) (startState (W.pargs mem1 t st hw lo rs) mem pos)
        o st' c ∧
      ∃ a memL memC i m, ∃ hm : m < st.length,
        (W.sc mem1 t st hw lo rs).SFound w a memL o.value ∧
        (W.sc mem1 t st hw lo rs).SClr memL memC ∧
        W.c.PetalOk W.G W.P (W.Y mem1) lo ⟨t, hw, o.value - 2, i⟩ ∧
        W.c.carve W.G (W.Y mem1) ⟨t, hw, o.value - 2, i⟩ =
          (W.Y mem1).filter (fun x => a.d.sett (W.sv x)) ∧
        m + 1 = a.j ∧ hw.getD i 0 = st[m].1 ∧ hv W.G t hw i = st[m].2.1 ∧
        hv W.G t hw (i + 1) = st[m].2.2 ∧
        st'.mem (W.CTL + 3) = (W.Hl t st).getD m 0 ∧
        (∀ i < a.ℓ.length, st'.mem (W.L.OK + a.ℓ.getD i 0) = W.L.os + 1 ∧
          st'.mem (W.L.HD + (mem1 (W.L.HI + a.ℓ.getD i 0) - 1)) = W.s) ∧
        st'.mem (W.L.HD + (mem1 (W.L.HI + (W.Hl t st).getD (m + 1) 0) - 1)) = W.s ∧
        (∀ x, x ≠ W.CTL + 3 → (∀ i < a.ℓ.length, x ≠ W.L.OK + a.ℓ.getD i 0 ∧
          x ≠ W.L.HD + (mem1 (W.L.HI + a.ℓ.getD i 0) - 1)) →
          x ≠ W.L.HD + (mem1 (W.L.HI + (W.Hl t st).getD (m + 1) 0) - 1) → st'.mem x = memC x) ∧
        (∀ x, (x < W.L.HD ∨ W.SL + W.L.NN + 1 ≤ x) → st'.mem x = mem1 x) ∧
        c + (W.sc mem1 t st hw lo rs).μ a ≤ (W.sc mem1 t st hw lo rs).μ (W.sc mem1 t st hw lo rs).a0 +
          psPreCost W.L.J + 150 * W.L.J + 100 * a.ℓ.length + 20 * (m + 1) + 1500 := by
  have hpre := h.spre hp hrs hpq htz hst
  obtain ⟨o1, st1, c1, hr1, a, memL, hfd, hclr, hc1⟩ :=
    psrchA_runs hPush hPS hClr (C := W.sc mem1 t st hw lo rs) pos ω hwA hpre
  have hr : o1.value - 2 < W.c.d W.G W.c.x0 t := by
    obtain ⟨-, -, -, -, -, -, -, -, hqL, -, hhi, -⟩ := hfd
    change a.q ≤ W.Lb at hqL
    change o1.value - 2 ≤ lo + a.q * W.bw at hhi
    have : a.q * W.bw ≤ W.Lb * W.bw := Nat.mul_le_mul_right _ hqL
    omega
  obtain ⟨i, hpet, hcarve, m, hm, hj, e0, e1, e2⟩ := h.portal hp hfd hr
  have hlen : (W.Hl t st).length = st.length + 1 := Hl_length t st
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := h.lay
  have hNN := h.hNN; have wNXT := h.wNXT
  have htu := h.H_lt hp (getD_mem' (show 0 < (W.Hl t st).length by omega))
  change W.sv t < W.s at htu
  have hl := h.lohi _ htu
  have hHI : mem (W.L.HI + W.sv t) = mem1 (W.L.HI + W.sv t) := by
    rw [hmem, Function.update_of_ne (by unfold slotA; omega)]
  have hNX : mem (W.NXT + W.sv t) < W.L.NN := by
    have := h.nxt (W.sv t) (by omega)
    rw [hmem, Function.update_of_ne (by unfold slotA; have := h.hiMM (W.sv t) (by omega); omega)]
      at this
    exact this
  have b1 : mem (W.L.HI + W.sv t) < 2 ^ w := by
    have := h.hiMM (W.sv t) (by omega); omega
  have b0 : 1 ≤ mem (W.L.HI + W.sv t) := by omega
  have key : ∃ o st' c, Runs w p ω (petalP bS bF bT)
      (startState (W.pargs mem1 t st hw lo rs) mem pos) o st' c ∧
      (o = .returned o1.value ∧ st'.mem (W.CTL + 3) = (W.Hl t st).getD m 0 ∧
        (∀ i < a.ℓ.length, st'.mem (W.L.OK + a.ℓ.getD i 0) = W.L.os + 1 ∧
          st'.mem (W.L.HD + (mem1 (W.L.HI + a.ℓ.getD i 0) - 1)) = W.s) ∧
        st'.mem (W.L.HD + (mem1 (W.L.HI + (W.Hl t st).getD (m + 1) 0) - 1)) = W.s ∧
        ∀ x, x ≠ W.CTL + 3 → (∀ i < a.ℓ.length, x ≠ W.L.OK + a.ℓ.getD i 0 ∧
          x ≠ W.L.HD + (mem1 (W.L.HI + a.ℓ.getD i 0) - 1)) →
          x ≠ W.L.HD + (mem1 (W.L.HI + (W.Hl t st).getD (m + 1) 0) - 1) → st'.mem x = st1.mem x) ∧
      c ≤ c1 + 100 * a.ℓ.length + 20 * (m + 1) + 500 := by
    have b2 : W.L.HD + (mem (W.L.HI + W.sv t) - 1) < 2 ^ w := by
      have := h.hiMM (W.sv t) (by omega); have := h.hR; have := h.hCTL; have := h.hSUM
      have := h.hSL; have := h.wSL; have := h.lES; omega
    have hm1 : Function.update mem (W.L.HD + (mem (W.L.HI + W.sv t) - 1)) (mem (W.NXT + W.sv t)) =
        mem1 := by rw [hmem]; rfl
    refine runs_start_le ?_
    dsimp only [petalP]
    rw [pargs_eq]
    wram_step
    wram_step
    have hb : p.procs[bS]? = some (psrchA bPush bPS bClr) := hS 0 (by simp)
    refine runs_seq_call_runs_le (vs := W.pargs mem1 t st hw lo rs) ?_ hb
      (by convert hr1 using 2 <;> first | exact hm1 | rfl) ?_
    · rw [pargs_eq]; eval_expr
    obtain ⟨o2, st2, c2, hr2, ⟨ho2, t1, t2, t3, t4⟩, hc2⟩ := h.petalTail_runs (bF := bF) (bT := bT)
      hF hT hp hfd.1 hclr hm hj
      ⟨st1.mem, Function.update (Function.update (startState (W.pargs mem1 t st hw lo rs) mem
        pos).regs 33 (mem (W.L.HI + W.sv t))) 34 o1.value, st1.pos⟩
      (fun i hi => by
        show Function.update _ _ _ i = _
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; rfl) rfl hwA ω
    refine ⟨o2, st2, c2, hr2, ⟨by rw [ho2]; simp, t1, t2, t3, t4⟩, ?_⟩
    simp only [argsSize_cons, argsSize_nil, Expr.size_reg] at *
    wram_cost
  obtain ⟨o, st', c, hrun, ⟨ho, q1, q2, q3, q4⟩, hc⟩ := key
  have hov : o.value = o1.value := by rw [ho]; rfl
  refine ⟨o, st', c, hrun, a, memL, st1.mem, i, m, hm, by rw [hov]; exact hfd, hclr,
    by rw [hov]; exact hpet, by rw [hov]; exact hcarve, hj, e0, e1, e2, q1, q2, q3, q4,
    fun x hx => ?_, ?_⟩
  · have := h.hCTL; have := h.hSUM; have := h.hSL; have := h.hR; have hES := h.lES
    have hmH : (W.Hl t st).getD (m + 1) 0 < W.s :=
      h.H_lt hp (getD_mem' (show m + 1 < (W.Hl t st).length by omega))
    have hmH' := h.hiMM _ (show (W.Hl t st).getD (m + 1) 0 < W.L.NN by omega)
    rw [q4 x (by omega) (fun i hi => by
      have hv := (h.sett_lt hfd.1 (getD_mem' hi)).2
      have := h.hiMM _ (show a.ℓ.getD i 0 < W.L.NN by omega)
      constructor <;> omega) (by omega)]
    exact h.after_out hp hfd.1 hclr hx
  have hc1' : c1 + (W.sc mem1 t st hw lo rs).μ a ≤ (W.sc mem1 t st hw lo rs).μ
      (W.sc mem1 t st hw lo rs).a0 + psPreCost W.L.J + 150 * W.L.J + 600 := hc1
  omega

end PW

end MinCostFlow.LowStretch
