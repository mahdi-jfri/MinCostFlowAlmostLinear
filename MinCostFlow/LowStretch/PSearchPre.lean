module

public import MinCostFlow.LowStretch.PSearchInv

/-!
# The invariant gives the precondition of `pstep`

`SC.Inv.pre` gives the precondition of `pstep` from the invariant of the search. The only part
that needs work is that of `psum` (`Inv.sum_pre`): after `dijStep` settles `u`, the arcs of `u`
before its slot read arrays that the search never writes, and every value is a word.

`SC.Inv.pay` says that the measure `μ` pays for one call of `pstep`: a step of Dijkstra costs at
most the potential plus one pop (`Inv.dij_le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

theorem PSG.cost_tb (X : PSG) (mem : ℕ → ℕ) (h : X.TB mem ∧ X.bq mem < X.k mem) :
    pstepCost X.args mem = 400 := X.cost_400 mem ⟨h.1, Or.inl h.2⟩

theorem PSG.cost_le (X : PSG) (mem : ℕ → ℕ) :
    pstepCost X.args mem ≤ 2 * dijCost (X.G.L.argsR X.G.R) mem + 600 := by
  by_cases h : X.TB mem ∧ (X.bq mem < X.k mem ∨ (X.pt mem).Pass mem)
  · rw [X.cost_400 mem h]; omega
  · rw [X.cost_dij mem h]

/-- A settled head in memory: its cost is below `INF` and is the cell at `TS + NN`. -/
theorem DL.ty_lt {L : DL} {w : ℕ} {mem : ℕ → ℕ} {Nodes : Finset ℕ} {d : DS}
    {qs : ℕ → List (ℕ × ℕ)} {g : AG} {s cur pos : ℕ} (hs : L.Shape w mem Nodes)
    (hr : L.Rep mem Nodes d qs) (hinv : g.Inv s L.INF cur pos d) {y : ℕ} (hy : y < L.NN)
    (hok : mem (L.OK + y) = L.os) (hst : mem (L.TS + 2 * L.NN + y) = L.rs) :
    y ∈ Nodes ∧ d.sett y ∧ d.tent y = mem (L.TS + L.NN + y) ∧ mem (L.TS + L.NN + y) < L.INF := by
  have hyN : y ∈ Nodes := (hs.ok_iff y).mp ⟨hy, hok⟩
  have hsy : d.sett y := (hr.sett y).mpr ⟨hyN, hst⟩
  have hlt : d.tent y < L.INF := (hinv.settled_le y hsy).trans_lt hinv.L_lt
  have ht := hr.tent y
  rw [if_pos hyN] at ht
  unfold DL.tentOf at ht
  split_ifs at ht with hts
  · exact ⟨hyN, hsy, ht, ht ▸ hlt⟩
  · omega

namespace SC

variable {C : SC} {w : ℕ} {a : SG} {mem : ℕ → ℕ}

theorem Ok.fixLt (h : C.Ok w) {x : ℕ} (hx : C.Fix x) : x < C.X.CTL := hx.2.1

open Classical in
/-- **The precondition of `psum`.** -/
theorem Inv.sum_pre (h : C.Ok w) (hI : C.Inv w a mem) {mem1 : ℕ → ℕ}
    (hp : stepPost w (C.Xf a).G (C.L.argsR C.X.G.R) mem 2 mem1) :
    ((C.Xf a).ps mem1).Pre mem1 w := by
  rcases hp with ⟨h0, -⟩ | ⟨h0, -⟩ |
    ⟨-, d', qs', -, -, hL', hsett', hs1, hr1, hinv1, -, -, hk1, -, -, -, -⟩
  · omega
  · omega
  set u := mem1 (C.X.G.R + 1) with hu
  have hus : d'.sett u := by rw [hsett']; exact Or.inr rfl
  have huN : u ∈ C.X.G.Nodes := ((hr1.sett u).mp hus).1
  have hun : u < C.L.NN := ((hs1.ok_iff u).mpr huN).1
  have hF1 : ∀ x, C.Fix x → mem1 x = C.mem0 x := fun x hx => (hk1 x hx.1).trans (hI.fix x hx)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hI.shape.lay
  have eLO : mem1 (C.L.LO + u) = C.mem0 (C.L.LO + u) := hF1 _ (h.fLO u hun).1
  have eHI : mem1 (C.L.HI + u) = C.mem0 (C.L.HI + u) := hF1 _ (h.fLO u hun).2.1
  have hlh := h.lohi u huN
  have hiM := h.hiMM u hun
  have hR := h.hR
  have hCTL := h.hCTL
  have hSUM := h.hSUM
  have hSL := h.hSL
  have wSL := h.wSL
  have hU := h.wU
  have hL'' : mem1 C.X.G.R < C.L.INF := hL' ▸ hinv1.L_lt
  set E := 2 ^ C.X.Es
  set U := E * C.L.INF + E + 1
  have hE1 : 1 ≤ E := Nat.one_le_two_pow
  have hU2 : 2 ≤ U := by omega
  have hUw : U ≤ (C.nA + C.L.MM + 1) * U := Nat.le_mul_of_pos_left _ (by omega)
  -- the arcs before the slot
  have hjM : ∀ j, mem1 (C.L.LO + u) ≤ j → j < mem1 (C.L.HI + u) - 1 → j < C.L.MM := by
    intro j _ h2; omega
  have hORD : ∀ j, mem1 (C.L.LO + u) ≤ j → j < mem1 (C.L.HI + u) - 1 →
      mem1 (C.X.ORD + j) >>> 1 = C.mem0 (C.X.ORD + j) / 2 ∧ C.mem0 (C.X.ORD + j) / 2 < C.nA := by
    intro j h1 h2
    rw [hF1 _ (h.fCS j (hjM j h1 h2)).2.2, Nat.shiftRight_eq_div_pow, pow_one]
    exact ⟨rfl, h.ordA u huN j (by omega) (by omega)⟩
  have hpa : ∀ j, mem1 (C.L.LO + u) ≤ j → j < mem1 (C.L.HI + u) - 1 →
      ((C.Xf a).ps mem1).pa mem1 j = C.mem0 (C.X.AS + 2 * (C.mem0 (C.X.ORD + j) / 2)) := by
    intro j h1 h2
    show mem1 (C.X.AS + 2 * (mem1 (C.X.ORD + j) >>> 1)) = _
    rw [(hORD j h1 h2).1, hF1 _ (h.fAS _ (hORD j h1 h2).2).1]
  have hwt : ∀ j, mem1 (C.L.LO + u) ≤ j → j < mem1 (C.L.HI + u) - 1 →
      ((C.Xf a).ps mem1).wt mem1 j ≤ E := by
    intro j h1 h2
    show 1 <<< (C.X.Es - mem1 (C.X.EXP + ((C.Xf a).ps mem1).pa mem1 j)) ≤ E
    exact shl_le _ _
  have hy : ∀ j, mem1 (C.L.LO + u) ≤ j → j < mem1 (C.L.HI + u) - 1 →
      ((C.Xf a).ps mem1).y mem1 j < C.L.NN := fun j h1 h2 => (hs1.heads j (hjM j h1 h2)).1
  have hty : ∀ j, mem1 (C.L.LO + u) ≤ j → j < mem1 (C.L.HI + u) - 1 →
      ((C.Xf a).ps mem1).okc mem1 j → ((C.Xf a).ps mem1).stc mem1 j →
      ((C.Xf a).ps mem1).ty mem1 j < C.L.INF := fun j h1 h2 ho hst =>
    (DL.ty_lt hs1 hr1 hinv1 (hy j h1 h2) ho hst).2.2.2
  have hwk : ∀ j, mem1 (C.L.LO + u) ≤ j → j < mem1 (C.L.HI + u) - 1 →
      ((C.Xf a).ps mem1).wt mem1 j * ((C.Xf a).ps mem1).k ≤ E * C.L.INF := fun j h1 h2 =>
    Nat.mul_le_mul (hwt j h1 h2) (show mem1 C.X.G.R ≤ C.L.INF by omega)
  have hwty : ∀ j, mem1 (C.L.LO + u) ≤ j → j < mem1 (C.L.HI + u) - 1 →
      ((C.Xf a).ps mem1).okc mem1 j → ((C.Xf a).ps mem1).stc mem1 j →
      ((C.Xf a).ps mem1).wt mem1 j * ((C.Xf a).ps mem1).ty mem1 j ≤ E * C.L.INF :=
    fun j h1 h2 hc hs => Nat.mul_le_mul (hwt j h1 h2) (hty j h1 h2 hc hs).le
  have hgu : ∀ j, mem1 (C.L.LO + u) ≤ j → j < mem1 (C.L.HI + u) - 1 → ∀ t,
      ((C.Xf a).ps mem1).gu mem1 j t ≤ U := by
    intro j h1 h2 t
    have hw := hwt j h1 h2
    have hk := hwk j h1 h2
    fin_cases t
    · show 1 ≤ U; omega
    · show ((C.Xf a).ps mem1).wt mem1 j ≤ U; omega
    · show ((C.Xf a).ps mem1).wt mem1 j ≤ U; omega
    · show ((C.Xf a).ps mem1).wt mem1 j * ((C.Xf a).ps mem1).k ≤ U; omega
    · show (if ((C.Xf a).ps mem1).okc mem1 j ∧ ((C.Xf a).ps mem1).stc mem1 j then
        ((C.Xf a).ps mem1).wt mem1 j * ((C.Xf a).ps mem1).ty mem1 j else 0) ≤ U
      split_ifs with hc
      · have := hwty j h1 h2 hc.1 hc.2
        omega
      · omega
  refine ⟨?_, ?_, ?_, fun j h1 h2 => ?_, fun j h1 h2 => ?_, fun j h1 h2 => ?_,
    fun j h1 h2 => ?_, fun j h1 h2 => ?_, fun j h1 h2 hc hs => ?_, fun t => ?_,
    fun j h1 h2 => ?_, fun j h1 h2 => ?_, ?_, ?_⟩
  · show mem1 (C.L.LO + u) ≤ mem1 (C.L.HI + u) - 1
    omega
  · show C.L.HD + (mem1 (C.L.HI + u) - 1) ≤ C.X.SUM
    unfold pqSize at hR; omega
  · show C.X.ORD + (mem1 (C.L.HI + u) - 1) ≤ C.X.SUM
    have := h.fixLt (h.fCS (C.L.MM - 1) (by omega)).2.2
    omega
  · show C.X.AS + 2 * (mem1 (C.X.ORD + j) >>> 1) < C.X.SUM
    rw [(hORD j h1 h2).1]
    have := h.fixLt (h.fAS _ (hORD j h1 h2).2).1
    omega
  · show C.X.EXP + ((C.Xf a).ps mem1).pa mem1 j < C.X.SUM
    rw [hpa j h1 h2]
    have := h.fixLt (h.fAS _ (hORD j h1 h2).2).2
    omega
  · have := hy j h1 h2
    show C.L.OK + ((C.Xf a).ps mem1).y mem1 j < C.X.SUM ∧
      C.L.TS + 2 * C.L.NN + ((C.Xf a).ps mem1).y mem1 j < C.X.SUM
    unfold pqSize at hR; omega
  · have := hwt j h1 h2
    omega
  · have := hwk j h1 h2
    omega
  · have := hwty j h1 h2 hc hs
    omega
  · show mem1 (C.X.SUM + t) + ((C.Xf a).ps mem1).ub mem1 t ((C.Xf a).ps mem1).hi < 2 ^ w
    have e1 : mem1 (C.X.SUM + t) = mem (C.X.SUM + t) :=
      hk1 _ (keepS_of_ge h (by have := t.isLt; omega))
    rw [e1, hI.sums t]
    have hs : C.es a.ℓ t ≤ C.nA * U := (hI.sums_le h).2.2.2 t
    have hub : ((C.Xf a).ps mem1).ub mem1 t ((C.Xf a).ps mem1).hi ≤ C.L.MM * U := by
      unfold PS.ub
      have := Finset.sum_le_card_nsmul (Finset.Ico ((C.Xf a).ps mem1).lo ((C.Xf a).ps mem1).hi)
        (fun j => ((C.Xf a).ps mem1).gu mem1 j t) U fun j hj => by
          obtain ⟨j1, j2⟩ := Finset.mem_Ico.mp hj
          exact hgu j j1 j2 t
      rw [Nat.card_Ico, smul_eq_mul] at this
      refine this.trans (Nat.mul_le_mul_right _ ?_)
      show mem1 (C.L.HI + u) - 1 - mem1 (C.L.LO + u) ≤ C.L.MM
      omega
    have : (C.nA + C.L.MM + 1) * U = C.nA * U + C.L.MM * U + U := by ring
    omega
  · show mem1 (C.X.ORD + j) < 2 ^ w
    rw [hF1 _ (h.fCS j (hjM j h1 h2)).2.2]
    have := (hORD j h1 h2).2
    have : C.nA * 2 ≤ (C.nA + C.L.MM + 1) * U := Nat.mul_le_mul (by omega) hU2
    omega
  · show mem1 (C.X.EXP + ((C.Xf a).ps mem1).pa mem1 j) < 2 ^ w
    rw [hpa j h1 h2, hF1 _ (h.fAS _ (hORD j h1 h2).2).2]
    exact h.wE _ (hORD j h1 h2).2
  · show C.X.SUM + 5 < 2 ^ w
    omega
  · show C.L.TS + 2 * C.L.NN < 2 ^ w
    have := h.wR2
    unfold pqSize at hR; omega

/-- **The precondition of `pstep`.** -/
theorem Inv.pre (h : C.Ok w) (hI : C.Inv w a mem) : (C.Xf a).Pre mem w := by
  have hR := h.hR
  have hCTL := h.hCTL
  have hSUM := h.hSUM
  have hSL := h.hSL
  have wSL := h.wSL
  have hlen := hI.len_le
  have hNN : 1 ≤ C.L.NN := by have := h.SN; omega
  refine ⟨⟨rfl, h.hR, h.wR2, hI.shape, hI.rep, hI.inv, hI.done, hI.cap, hI.par, hI.tz,
    hI.stamps⟩, hI.test_pre h, fun mem1 hp => hI.sum_pre h hp, ?_, ?_, h.wb, h.wL, h.wSQ, h.wP2,
    ?_, ?_, h.wNXT, fun v hv => ?_, fun q hq => ?_, fun v hv => ?_, fun t ht => ?_,
    fun i hi => ?_, fun i hi => ?_, fun v hv => (h.fLO v hv).2.2.2.1,
    fun q hq => ⟨(h.fSQ q hq).1.1, (h.fSQ q hq).2.1⟩, Or.inl h.hSUM, Or.inr h.hSL, ?_, ?_⟩
  · show 1 ≤ mem C.X.CTL; rw [hI.qc]; exact hI.q1
  · show mem C.X.CTL ≤ C.X.Lb + 1; rw [hI.qc]; exact hI.qL
  · show C.X.CTL + 3 < 2 ^ w; omega
  · show C.X.SL + mem (C.X.CTL + 1) + 1 < 2 ^ w; rw [hI.ns]; omega
  · show mem (C.X.NXT + v) < C.L.NN
    rw [hI.fix _ (h.fLO v hv).2.2.2]; exact h.nxt v hv
  · show mem (C.X.SQ + q) < 2 ^ w ∧ mem (C.X.P2 + q) < 2 ^ w
    rw [hI.fix _ (h.fSQ q hq).1, hI.fix _ (h.fSQ q hq).2]
    have := h.hSm q hq
    have := h.wSm
    omega
  · show mem (C.L.HI + v) ≤ C.L.MM
    rw [hI.fix _ (h.fLO v hv).2.1]; exact h.hiMM v hv
  · exact keepS_of_ge h (show C.X.G.R + 2 ≤ C.X.SUM + t by omega)
  · have hi' : i ≤ mem (C.X.CTL + 1) := hi
    rw [hI.ns] at hi'
    exact keepS_of_ge h (show C.X.G.R + 2 ≤ C.X.SL + i by omega)
  · exact keepS_of_ge h (show C.X.G.R + 2 ≤ C.X.CTL + i by omega)
  · show C.X.SL + mem (C.X.CTL + 1) < C.X.CTL ∨ C.X.CTL + 4 ≤ C.X.SL
    omega
  · have := h.fixLt (h.fLO (C.L.NN - 1) (by omega)).2.2.2
    show C.X.NXT + C.L.NN ≤ C.X.SUM ∨ C.X.SUM + 5 ≤ C.X.NXT
    exact Or.inl (by omega)

open Classical in
/-- **A step of Dijkstra costs at most the potential and one pop.** -/
theorem Inv.dij_le (h : C.Ok w) (hI : C.Inv w a mem) :
    dijCost (C.L.argsR C.X.G.R) mem ≤ C.L.pot C.mem0 C.X.G.Nodes a.d a.qs + stCost C.L.J := by
  have hroot := hI.rep.pq.root_spec
  rw [show C.L.D + 3 + 1 = C.L.D + 4 from rfl] at hroot
  rw [← pot_eq_of_deg (hI.deg h)]
  by_cases hlt : mem (C.L.D + 4) / C.L.J < C.L.INF
  · obtain ⟨e, rest, he, -, hc, -⟩ := hroot.1 hlt
    set mem1 := Function.update (Function.update mem (C.X.G.R + 1) e.2) C.X.G.R e.1
    have m0 : mem1 C.X.G.R = e.1 := by simp [mem1]
    have m1 : mem1 (C.X.G.R + 1) = e.2 := by simp [mem1]
    have hq : (C.Xf a).G.qs (mem (C.L.D + 4) % C.L.J) =
        (mem1 (C.Xf a).G.R, mem1 ((C.Xf a).G.R + 1)) :: rest := by
      show a.qs _ = (mem1 C.X.G.R, mem1 (C.X.G.R + 1)) :: rest
      rw [he, m0, m1]
    have hdc := dijCost_eq (G := (C.Xf a).G) hI.shape hI.rep hI.inv hc rfl hq
    have hpop := popped (G := (C.Xf a).G) hI.shape hI.rep hI.inv hc hq
    change dijCost (C.L.argsR C.X.G.R) mem = _ at hdc
    rw [hdc]
    split_ifs with hst
    · show stCost C.L.J ≤ _; omega
    · show stCost C.L.J + 100 + (C.L.deg mem (mem1 (C.X.G.R + 1)) + 1) *
        (50 * (Nat.log 2 C.L.J + 2) + 300) ≤ _
      have hxN : mem1 (C.X.G.R + 1) ∈ C.X.G.Nodes.filter (fun u => ¬ a.d.sett u) :=
        Finset.mem_filter.mpr ⟨hpop.2.2.2.1, fun hs => hst (Or.inl hs)⟩
      have hle := Finset.single_le_sum (f := fun u => C.L.deg mem u + 1)
        (fun _ _ => Nat.zero_le _) hxN
      unfold DL.pot stCost
      set b := Nat.log 2 C.L.J
      set dg := C.L.deg mem (mem1 (C.X.G.R + 1))
      have h1 : (100 * (b + 2) + 900) * (dg + 1) ≤ (100 * (b + 2) + 900) *
          ∑ u ∈ C.X.G.Nodes.filter (fun u => ¬ a.d.sett u), (C.L.deg mem u + 1) :=
        Nat.mul_le_mul_left _ hle
      have h2 : 100 + (dg + 1) * (50 * (b + 2) + 300) ≤ (100 * (b + 2) + 900) * (dg + 1) := by
        nlinarith
      omega
  · have hall := hroot.2 (by omega)
    have e := dijCost_empty (L := C.L) (R := C.X.G.R) (mem := mem) (by omega)
    rw [show dijCost (C.L.argsR C.X.G.R) mem = stCost C.L.J from e]
    omega

/-- **The measure pays for one call of `pstep`.** -/
theorem Inv.pay (h : C.Ok w) (hI : C.Inv w a mem) : pstepCost (C.Xf a).args mem ≤ C.μ a := by
  have h1 := (C.Xf a).cost_le mem
  have h2 := hI.dij_le h
  change pstepCost (C.Xf a).args mem ≤ 2 * dijCost (C.L.argsR C.X.G.R) mem + 600 at h1
  unfold μ
  omega

end SC

end MinCostFlow.LowStretch
