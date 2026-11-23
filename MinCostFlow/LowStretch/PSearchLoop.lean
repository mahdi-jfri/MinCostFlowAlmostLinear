module

public import MinCostFlow.LowStretch.PSearchSet2

/-!
# The loop of one petal search

Each call of `pstep` that returns `1` keeps the invariant `SC.Inv` and pays for itself
(`Inv.step`, from `Inv.adv`, `Inv.drop` and `Inv.settle`). So `psLoop` runs within the measure
`μ` (`search_loop`).

The loop stops when `pstep` returns another value. It never returns `0` (`Inv.not_zero`): the
queue is empty only after every bucket failed, and by `Cl.Fail.false` some bucket passes. So the
loop stops when a test passes, at a radius `r` in the current bucket, and then the petal at `r`
is the settled part (`Inv.found`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace SC

variable {C : SC} {w : ℕ} {a : SG} {mem : ℕ → ℕ}

/-- **A call of `pstep` that returns `1`** keeps the invariant and pays for itself. -/
theorem Inv.step (h : C.Ok w) (hI : C.Inv w a mem) {mem' : ℕ → ℕ}
    (hp : (C.Xf a).Post mem w 1 mem') :
    ∃ a', C.Inv w a' mem' ∧ C.μ a' + pstepCost (C.Xf a).args mem + 50 ≤ C.μ a ∧
      C.L.pot C.mem0 C.X.G.Nodes a'.d a'.qs ≤ C.L.pot C.mem0 C.X.G.Nodes a.d a.qs := by
  rcases hp with ⟨h2, -⟩ | ⟨-, hT, hP, hb, hm⟩ | ⟨hT, mem1, v1, hs, hc⟩
  · omega
  · exact ⟨_, (hI.adv h hT hP hb hm).1, (hI.adv h hT hP hb hm).2, le_rfl⟩
  · rcases hc with ⟨-, h0, -⟩ | ⟨h1, -, hm⟩ | ⟨h2, -, mem2, hs2, hf2, hm⟩
    · omega
    · subst h1; subst hm; exact hI.drop h hs hT
    · subst h2; exact hI.settle h hT hs hs2 hf2 hm

/-- **`pstep` never returns `0`.** It would mean that the queue is empty and the tests were
made in every bucket, but some bucket passes. -/
theorem Inv.not_zero (h : C.Ok w) (hI : C.Inv w a mem) {mem' : ℕ → ℕ}
    (hp : (C.Xf a).Post mem w 0 mem') : False := by
  rcases hp with ⟨h2, -⟩ | ⟨h1, -⟩ | ⟨hT, mem1, v1, hs, hc⟩
  · omega
  · omega
  rcases hc with ⟨h0, -, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩
  swap
  · omega
  swap
  · omega
  subst h0
  rcases hs with ⟨-, hq, -⟩ | ⟨h1, -⟩ | ⟨h2, -⟩
  swap
  · omega
  swap
  · omega
  change ∀ c, a.qs c = [] at hq
  -- the queue is empty, so the least key is at least `INF`
  have hroot := hI.rep.pq.root_spec
  rw [show C.L.D + 3 + 1 = C.L.D + 4 from rfl] at hroot
  have hge : C.L.INF ≤ mem (C.L.D + 4) / C.L.J := by
    by_contra hlt
    obtain ⟨e, rest, he, -⟩ := hroot.1 (by omega)
    rw [hq] at he
    exact List.cons_ne_nil e rest he.symm
  have hINF := h.hINF
  have hqL := hI.qL
  have hm1 : a.q * C.X.bw ≤ (C.X.Lb + 1) * C.X.bw := Nat.mul_le_mul_right _ hqL
  have hm2 : (a.q - 1) * C.X.bw ≤ (C.X.Lb + 1) * C.X.bw := Nat.mul_le_mul_right _ (by omega)
  -- so no test is made, and the bucket pointer is past the last bucket
  have hnT : ¬ (C.Xf a).TB mem := by
    intro hTB
    have := (hT hTB).2
    rw [k_eq, hI.bq_eq] at this
    omega
  have hq : a.q = C.X.Lb + 1 := by
    by_contra hne
    exact hnT (hI.tb_iff.mpr ⟨by omega, by omega, by have := hI.inv.L_lt; omega⟩)
  have hbw := h.hbw
  have hLb := h.hLb
  refine Cl.Fail.false h.hGo h.link.conn h.link.hY (a := C.X.lo + C.X.Lb * C.X.bw + 1)
    (Cl.fail_of_bfail fun q h1 h2 => hI.bdone q h1 (by omega) _) ?_ h.hκ1 h.hL1 h.hΔ h.hV
  rw [← hbw, ← hLb]; omega

open Classical in
/-- **When the loop stops**, a test passed at the tested radius `r` of the current bucket, and
the petal at `r` is the settled part. The memory is the one before the last call. -/
theorem Inv.found (h : C.Ok w) (hI : C.Inv w a mem) {v : ℕ} {mem' : ℕ → ℕ}
    (hp : (C.Xf a).Post mem w v mem') (hv : v ≠ 1) :
    mem' = mem ∧ v = (C.Xf a).rr mem + 2 ∧
      C.c.cost C.G C.P C.Y (C.pd.withR ((C.Xf a).rr mem)) * C.c.sq C.G C.P a.q ≤
        8 * C.c.vol C.G C.P C.Y (C.pd.withR ((C.Xf a).rr mem)) ∧
      C.c.vol C.G C.P C.Y (C.pd.withR ((C.Xf a).rr mem)) ≤ C.c.T C.G C.P a.q ∧
      C.c.carve C.G C.Y (C.pd.withR ((C.Xf a).rr mem)) = C.Y.filter (fun x => a.d.sett (C.sv x)) ∧
      a.d.L ≤ (C.Xf a).rr mem ∧ (C.Xf a).rr mem ≤ C.Rm ∧ 1 ≤ a.q ∧ a.q ≤ C.X.Lb ∧
      C.X.lo + (a.q - 1) * C.X.bw ≤ (C.Xf a).rr mem ∧
      (C.Xf a).rr mem ≤ C.X.lo + a.q * C.X.bw ∧ (C.Xf a).rr mem < C.kq mem := by
  by_cases hv0 : v = 0
  · subst hv0; exact (hI.not_zero h hp).elim
  rcases hp with ⟨-, hTB, hvr, hP, hm⟩ | ⟨h1, -⟩ | ⟨-, mem1, v1, -, hc⟩
  · obtain ⟨hr1, hr2, hr3, hq1, hqL, hb1, hb2⟩ := hI.rr_facts h hTB
    obtain ⟨t1, t2⟩ := (hI.pass h hTB).mp hP
    exact ⟨hm, hvr, t1, t2, hI.carve h hr1 hr2 hr3, hr2, hr3, hq1, hqL, hb1, hb2, hr1⟩
  · omega
  · rcases hc with ⟨-, h0, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> omega

/-- The potential of a state of the search. -/
noncomputable def potA (C : SC) (a : SG) : ℕ := C.L.pot C.mem0 C.X.G.Nodes a.d a.qs

/-- The invariant of the loop: the search invariant, and a potential at most `P0`. -/
def LI (C : SC) (w P0 : ℕ) (a : SG) (mem : ℕ → ℕ) : Prop := C.Inv w a mem ∧ C.potA a ≤ P0

/-- **The loop of the search** runs within the measure, and the potential never grows. -/
theorem search_loop (h : C.Ok w) {p : Program} {bPS : ℕ} (hPS : MeetsContract w p bPS (pstepC w))
    (hw1 : 1 < 2 ^ w) (hlen : C.X.args.length = 32) (hwA : ∀ x ∈ C.X.args, x < 2 ^ w)
    (P0 : ℕ) (x0 : Option SG) :
    Triple w p (PLI (w := w) C.X.args C.Xf (C.LI w P0) x0) (psLoop bPS)
      (normalPost (PLI (w := w) C.X.args C.Xf (C.LI w P0) none)) (fun _ => plrem C.μ x0) :=
  psLoop_spec C.X.args C.Xf (C.LI w P0) hPS C.μ hw1 hlen hwA (fun _ => rfl)
    (fun _ _ hI => hI.1.pre h) (fun _ _ hI => hI.1.pay h)
    (fun _ _ _ hI hp => by
      obtain ⟨a', h1, h2, h3⟩ := hI.1.step h hp
      exact ⟨a', ⟨h1, le_trans h3 hI.2⟩, h2⟩) x0

end SC

end MinCostFlow.LowStretch
