module

public import MinCostFlow.LowStretch.KRep
public import MinCostFlow.LowStretch.ProgFind

/-!
# Kruskal's merge tree: one step

`kstP` processes one pair `q`. It finds the roots of the two ends of `q`. If they differ, it adds
the node `N` to the tree, with the two current tops as children, and joins the two sets by size
(`kstP_spec`). The memory then holds `kstep G s q` (`KRep.step`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The arrays of the Kruskal data, as arguments. -/
def KL.arr (E : KL) : List ℕ := [E.UF, E.SZ, E.TN, E.KPAR, E.KCH1, E.KCH2, E.KMW, E.KMP]

/-- Hang the root in register `ra` below the root in register `rb`, and label the set with `N`. -/
def kUnion (ra rb : ℕ) : Stmt :=
  .seq (.store (.bin .add (.reg 5) (.reg ra)) (.reg rb))
  (.seq (.store (.bin .add (.reg 6) (.reg rb)) (.bin .add (.reg 18) (.reg 19)))
  (.store (.bin .add (.reg 7) (.reg rb)) (.reg 1)))

/-- `kstP bF` with `args = q :: N :: IN :: PW :: n :: E.arr`; `findP` sits at `bF`. It returns
the new number of nodes. -/
def kstP (bF : ℕ) : Stmt :=
  .seq (.call 13 bF [.reg 5, .load (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 0))), .reg 4])
  (.seq (.call 14 bF [.reg 5,
    .load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 3) (.reg 0))) (.const 1)), .reg 4])
  (.cond (.bin .eq (.reg 13) (.reg 14)) (.ret (.reg 1))
  (.seq (.assign 15 (.load (.bin .add (.reg 7) (.reg 13))))
  (.seq (.assign 16 (.load (.bin .add (.reg 7) (.reg 14))))
  (.seq (.assign 17 (.load (.bin .add (.reg 3) (.reg 0))))
  (.seq (.assign 18 (.load (.bin .add (.reg 6) (.reg 13))))
  (.seq (.assign 19 (.load (.bin .add (.reg 6) (.reg 14))))
  (.seq (.store (.bin .add (.reg 9) (.reg 1)) (.reg 15))
  (.seq (.store (.bin .add (.reg 10) (.reg 1)) (.reg 16))
  (.seq (.store (.bin .add (.reg 8) (.reg 15)) (.reg 1))
  (.seq (.store (.bin .add (.reg 8) (.reg 16)) (.reg 1))
  (.seq (.store (.bin .add (.reg 8) (.reg 1)) (.reg 1))
  (.seq (.store (.bin .add (.reg 11) (.reg 1)) (.reg 17))
  (.seq (.store (.bin .add (.reg 12) (.reg 1)) (.reg 0))
  (.seq (.cond (.bin .lt (.reg 19) (.reg 18))
      (kUnion 14 13) (kUnion 13 14))
  (.ret (.bin .add (.reg 1) (.const 1))))))))))))))))))

theorem kstP_noRand (bF : ℕ) : (kstP bF).NoRand := by
  simp [kstP, kUnion, Stmt.NoRand]

/-- The contract of `kstP`, for the graph `G`, the state `s` and the pair `q`. -/
def kstC (w : ℕ) (G : PG) (s : KS) (q : ℕ) : Contract where
  pre args mem := ∃ IN PW : ℕ, ∃ E : KL, ∃ dep : ℕ → ℕ, ∃ l r : List ℕ,
    args = q :: s.T.N :: IN :: PW :: E.n :: E.arr ∧ E.Lay ∧ KRep mem E s dep ∧ s.Inv G l r ∧
    E.n = G.n ∧ G.pu q < G.n ∧ G.pv q < G.n ∧ mem (IN + 3 * q) = G.pu q ∧
    mem (IN + 3 * q + 1) = G.pv q ∧ mem (PW + q) = G.pω q ∧ IN + 3 * q + 1 < 2 ^ w ∧
    PW + q < 2 ^ w ∧ E.KMP + 2 * E.n < 2 ^ w
  post args mem v mem' := ∀ IN PW : ℕ, ∀ E : KL, args = q :: s.T.N :: IN :: PW :: E.n :: E.arr →
    v = (kstep G s q).T.N ∧ (∃ dep, KRep mem' E (kstep G s q) dep) ∧
    ∀ a, (a < E.UF ∨ E.KMP + 2 * E.n ≤ a) → mem' a = mem a
  cost args _ := 40 * Nat.log 2 (args.getD 4 0) + 300

theorem KL.eq_of_args {E E' : KL} {a b c d a' b' c' d' : ℕ}
    (h : a :: b :: c :: d :: E.n :: E.arr = a' :: b' :: c' :: d' :: E'.n :: E'.arr) :
    E' = E := by
  cases E; cases E'; simp only [KL.arr, List.cons.injEq] at h; obtain ⟨-, -, -, -, h⟩ := h
  simp_all

theorem kstP_spec {w : ℕ} {p : Program} {b bF : ℕ} (hp : p.HasAt b [kstP bF])
    (hf : p.HasAt bF [findP]) (G : PG) (s : KS) (q : ℕ) : MeetsContract w p b (kstC w G s q) := by
  intro args mem pos ω hwords hpre
  obtain ⟨IN, PW, E, dep, l, r, rfl, hl, hK, hI, hn, hqu, hqv, mu, mv, mw, hw1, hw2, hw3⟩ := hpre
  have hproc : p.procs[b]? = some (kstP bF) := hp 0 (by simp)
  have hF := findP_spec (w := w) hf
  clear hp hf
  have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4; have l5 := hl.l5
  have l6 := hl.l6; have l7 := hl.l7
  have hu := hK.uf
  have hc := hu.cons
  have hqu' : G.pu q < E.n := by omega
  have hqv' : G.pv q < E.n := by omega
  have hdu := hu.dep_le hqu'
  have hdv := hu.dep_le hqv'
  have hnN : E.n ≤ s.T.N := by rw [hn]; exact hI.n_le
  have hcnt := hK.cnt
  have hcard : (ufRoots mem E.UF E.n).card ≤ E.n := by
    unfold ufRoots; exact (Finset.card_filter_le _ _).trans (by simp)
  have hN2 : s.T.N ≤ 2 * E.n := by omega
  refine ⟨kstP bF, hproc, ?_⟩
  simp only [KL.arr]
  refine runs_start_le ?_
  dsimp only [kstP, kUnion]
  have hmu : mem (IN + 3 * q) < 2 ^ w := by rw [mu]; omega
  have hmv : mem (IN + 3 * q + 1) < 2 ^ w := by rw [mv]; omega
  wram_step
  · intro v hv; simp only [startState, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> omega
  · exact ⟨E.UF, G.pu q, E.n, dep, by simp [startState, mu, hn], hc, hqu', hdu, by omega⟩
  intro v1 mem1 pos1 ⟨hm1, hv1⟩
  simp only [startState, List.getD_cons_zero, List.getD_cons_succ, mu] at hm1 hv1
  subst mem1
  have e1 : v1 = rt mem E.UF dep (G.pu q) := hv1 dep (by rw [← hn]; exact hc) (by omega)
  clear hv1
  wram_step
  · exact ⟨E.UF, G.pv q, E.n, dep, by simp [mv, hn], hc, hqv', hdv, by omega⟩
  intro v2 mem2 pos2 ⟨hm2, hv2⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ, mv] at hm2 hv2
  subst mem2
  have e2 : v2 = rt mem E.UF dep (G.pv q) := hv2 dep (by rw [← hn]; exact hc) (by omega)
  clear hv2
  subst v1 v2
  have hR1 := hc.rt_lt hqu'
  have hR2 := hc.rt_lt hqv'
  have hta := hu.lab _ hqu'
  have htb := hu.lab _ hqv'
  obtain ⟨haN, -, -⟩ := hI.top _ hqu
  obtain ⟨hbN, -, -⟩ := hI.top _ hqv
  have hs1 := hu.size_le hR1 (hc.rt_is_root hqu')
  have hs2 := hu.size_le hR2 (hc.rt_is_root hqv')
  generalize hR1e : rt mem E.UF dep (G.pu q) = R1 at *
  generalize hR2e : rt mem E.UF dep (G.pv q) = R2 at *
  have hfin : ∀ (ra rb : ℕ) (M' : ℕ → ℕ), (∃ dep', KRep (kU E (kW E mem s.T.N (mem (E.TN + R1))
      (mem (E.TN + R2)) (G.pω q) q) ra rb s.T.N (mem (E.SZ + R1) + mem (E.SZ + R2))) E
        (kstep G s q) dep') →
      M' = kU E (kW E mem s.T.N (mem (E.TN + R1)) (mem (E.TN + R2)) (G.pω q) q) ra rb s.T.N
        (mem (E.SZ + R1) + mem (E.SZ + R2)) → ra < E.n → rb < E.n → s.T.N + 2 ≤ 2 * E.n →
      R1 ≠ R2 →
      (kstC w G s q).post [q, s.T.N, IN, PW, E.n, E.UF, E.SZ, E.TN, E.KPAR, E.KCH1, E.KCH2, E.KMW,
        E.KMP] mem (s.T.N + 1) M' := by
    intro ra rb M' hK' hM' hra hrb hN2' hne IN' PW' E' he
    obtain rfl := KL.eq_of_args he
    refine ⟨?_, hM' ▸ hK', fun a ha => ?_⟩
    · have hab : s.top (G.pu q) ≠ s.top (G.pv q) := fun e =>
        hne (by rw [← hR1e, ← hR2e]; exact (hu.same _ hqu' _ hqv').mpr e)
      simp only [kstep]; rw [if_neg hab]
    · rw [hM', kU_out hl hra hrb (by omega), kW_out hl (by omega) (by omega) (by omega) (by omega)]
  have stepA : R1 ≠ R2 → mem (E.SZ + R2) < mem (E.SZ + R1) → s.T.N + 2 ≤ 2 * E.n ∧
      ∃ dep', KRep (kU E (kW E mem s.T.N (mem (E.TN + R1)) (mem (E.TN + R2)) (G.pω q) q) R2 R1
        s.T.N (mem (E.SZ + R1) + mem (E.SZ + R2))) E (kstep G s q) dep' := fun hne hlt => by
    have := KRep.step hK hI hl hn ⟨hqu, hqv⟩ (ra := R2) (rb := R1)
      (Or.inr ⟨hR1e, hR2e⟩) (Ne.symm hne) hlt.le
    rw [hR1e, hR2e, Nat.add_comm (mem (E.SZ + R2))] at this
    exact this
  have stepB : R1 ≠ R2 → ¬ mem (E.SZ + R2) < mem (E.SZ + R1) → s.T.N + 2 ≤ 2 * E.n ∧
      ∃ dep', KRep (kU E (kW E mem s.T.N (mem (E.TN + R1)) (mem (E.TN + R2)) (G.pω q) q) R1 R2
        s.T.N (mem (E.SZ + R1) + mem (E.SZ + R2))) E (kstep G s q) dep' := fun hne hlt => by
    have := KRep.step hK hI hl hn ⟨hqu, hqv⟩ (ra := R1) (rb := R2)
      (Or.inl ⟨hR1e, hR2e⟩) hne (by omega)
    rw [hR1e, hR2e] at this
    exact this
  clear hI hR1e hR2e
  wram_run
  · intro IN' PW' E' he
    obtain rfl := KL.eq_of_args he
    have hab : s.top (G.pu q) = s.top (G.pv q) := by rw [← hta, ← htb, hcond]
    have hks : kstep G s q = s := by simp only [kstep]; rw [if_pos hab]
    rw [hks]
    exact ⟨rfl, ⟨dep, hK⟩, fun a _ => rfl⟩
  · simp only [kstC, findC, List.getD_cons_zero, List.getD_cons_succ, startState, hn]
    wram_cost
  · have hne : R1 ≠ R2 := by assumption
    have hlt : mem (E.SZ + R2) < mem (E.SZ + R1) := by simpa using hcond
    have hA := stepA hne hlt
    refine hfin R2 R1 _ hA.2 ?_ hR2 hR1 hA.1 hne
    simp only [kU, kW, mw]
  · simp only [kstC, findC, List.getD_cons_zero, List.getD_cons_succ, startState, hn]
    wram_cost
  · have hne : R1 ≠ R2 := by assumption
    have hlt : ¬ mem (E.SZ + R2) < mem (E.SZ + R1) := by simpa using hcond
    have hB := stepB hne hlt
    refine hfin R1 R2 _ hB.2 ?_ hR1 hR2 hB.1 hne
    simp only [kU, kW, mw]
  · simp only [kstC, findC, List.getD_cons_zero, List.getD_cons_succ, startState, hn]
    wram_cost

end MinCostFlow.LowStretch
