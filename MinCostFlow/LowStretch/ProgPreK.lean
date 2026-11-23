module

public import MinCostFlow.LowStretch.ProgPreW
public import MinCostFlow.LowStretch.ProgPreKLoop
public import MinCostFlow.LowStretch.ProgPreKMath
public import MinCostFlow.LowStretch.ProgDedup
public import MinCostFlow.LowStretch.ProgKrun
public import MinCostFlow.Expander.HeapSortProg

/-!
# The preprocessing, part 2: the merge tree

`kP` builds Kruskal's merge tree of the pair graph `pgOf G`. It writes the smaller end of each
pair (`tabP eMin`), groups the pairs by it (`csrB`), keeps one lightest pair for each pair of
ends (`ddP`), writes the sort keys `EXP[q] · m + q` of the kept pairs (`tabP eKey`), sorts them
(the heap sort), and runs Kruskal's algorithm on the sorted pairs (`krP`). It returns the number
of nodes of the tree (`kP_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited MinCostFlow.Expander

/-- `kP` with `args = [n, m]`. The called procedures sit at `bMin`, `bCsr`, `bDd`, `bKey`, `bHs`
and `bKr`. -/
def kP (bMin bCsr bDd bKey bHs bKr : ℕ) : Stmt :=
  .seq (.call 5 bMin [.reg 1, lin 8 5 0, .const 2])
  (.seq (.call 5 bCsr [lin 8 5 0, .reg 1, .reg 0, lin 8 6 0, lin 9 6 1, lin 9 6 2])
  (.seq (.call 2 bDd [.reg 1, .reg 0, .const 2, lin 8 4 0, lin 8 6 0, lin 9 6 2, lin 9 7 2,
    lin 9 7 3, lin 9 7 4])
  (.seq (.call 5 bKey [.reg 2, lin 9 8 4, lin 9 7 4, lin 8 3 0, .reg 1])
  (.seq (.call 5 bHs [lin 9 8 4, .reg 2])
  (.seq (.call 3 bKr [.reg 0, .reg 2, lin 9 8 4, .reg 1, .const 2, lin 8 4 0, lin 9 9 4,
    lin 9 9 5, lin 9 9 6, lin 9 9 7, lin 9 9 9, lin 9 9 11, lin 9 9 13, lin 9 9 15])
  (.ret (.reg 3)))))))

theorem kP_noRand (bMin bCsr bDd bKey bHs bKr : ℕ) : (kP bMin bCsr bDd bKey bHs bKr).NoRand := by
  simp [kP, lin, Stmt.NoRand]

/-- The cost of `kP`. -/
def kCost (G : WGraph) : ℕ :=
  2000 * (G.m + G.n + 1) + G.m * (560 * Nat.log 2 (G.n * G.n + 2) + 40 * Nat.log 2 G.n + 400)

/-- The contract of `kP` for the graph `G`: it needs the rounded weights and their exponents. -/
def kC (w : ℕ) (G : WGraph) : Contract where
  pre args mem := args = [G.n, G.m] ∧ InG w G mem ∧
    ∀ p < G.m, mem (aPW G.n G.m + p) = (pgOf G).pω p ∧
      (pgOf G).pω p = 2 ^ mem (aEXP G.n G.m + p)
  post _ mem v mem' := ∃ T : KT, T.Ok (pgOf G) ∧ v = T.N ∧ T.N ≤ 2 * G.n ∧
    (∀ k < T.N, mem' (aKPAR G.n G.m + k) = T.par k ∧ mem' (aKMW G.n G.m + k) = T.mw k) ∧
    (∀ k, G.n ≤ k → k < T.N → mem' (aKCH1 G.n G.m + k) = T.ch1 k ∧
      mem' (aKCH2 G.n G.m + k) = T.ch2 k ∧ mem' (aKMP G.n G.m + k) = T.mp k) ∧
    ∀ a, (a < aTLK G.n G.m ∨ aKSZ G.n G.m ≤ a) → mem' a = mem a
  cost _ _ := kCost G

/-- The arrays of `krP`. -/
def kLOf (n m : ℕ) : KL :=
  ⟨n, 9 + 9 * m + 4 * n, 9 + 9 * m + 5 * n, 9 + 9 * m + 6 * n, 9 + 9 * m + 7 * n,
    9 + 9 * m + 9 * n, 9 + 9 * m + 11 * n, 9 + 9 * m + 13 * n, 9 + 9 * m + 15 * n⟩

theorem tab_congr {c : ℕ} {f g : ℕ → ℕ} (h : ∀ i < c, f i = g i) : tab c f = tab c g := by
  unfold tab
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem kP_spec {w : ℕ} {p : Program} {b bMin bCsr bDd bKey bHs bKr : ℕ} {G : WGraph}
    (hp : p.HasAt b [kP bMin bCsr bDd bKey bHs bKr])
    (hMin : MeetsContract w p bMin (tabC w eMin (minPre w) minF))
    (hCsr : MeetsContract w p bCsr (csrC w)) (hDd : MeetsContract w p bDd (ddC w))
    (hKey : MeetsContract w p bKey (tabC w eKey (keyPre w) keyF))
    (hHs : MeetsContract w p bHs (heapSortContract w))
    (hKr : MeetsContract w p bKr (krC w (pgOf G))) : MeetsContract w p b (kC w G) := by
  intro args mem pos ω _ hpre
  obtain ⟨rfl, hG, hPW⟩ := hpre
  have hproc : p.procs[b]? = some (kP bMin bCsr bDd bKey bHs bKr) := hp 0 (by simp)
  refine ⟨_, hproc, ?_⟩
  have hw := hG.add_lt
  have hn1 := hG.one_le
  have hw2 := hG.two_le_w
  simp only [aH] at hw
  have hends := hG.ends
  have hpG : ∀ q < G.m, (pgOf G).pu q < G.n ∧ (pgOf G).pv q < G.n := fun q hq =>
    ⟨(hG.allowed.fit.ok q (by rw [pgOf_m]; exact hq)).1,
      (hG.allowed.fit.ok q (by rw [pgOf_m]; exact hq)).2.1⟩
  dsimp only [kP, lin]
  refine runs_start_le ?_
  -- the smaller ends
  wram_step
  · refine ⟨⟨G.m, 8 + 5 * G.m + 0 * G.n, 2, rfl, by omega, by omega, fun i hi => ?_⟩,
      by simp, by simp; omega⟩
    show mem (2 + 3 * i) < _
    rw [(hends i hi).1]; have := (hpG i hi).1; omega
  intro v1 mem1 pos1 h1
  obtain ⟨h1a, h1b⟩ := h1
  simp only [List.getD_cons_zero, List.getD_cons_succ, minF, startState] at h1a h1b
  have hin1 : ∀ a < 2 + 3 * G.m, mem1 a = mem a := fun a ha => h1b a (Or.inl (by omega))
  -- the groups by the smaller end
  wram_step
  · refine ⟨_, _, _, _, _, _, rfl, fun i hi => ?_, by omega, by omega, by omega, by omega⟩
    show mem1 _ < _
    rw [h1a i hi]; have := (hpG i hi).1; have := (hends i hi).1; omega
  intro v2 mem2 pos2 h2
  obtain ⟨h2a, h2b, h2c⟩ := h2
  simp only [List.getD_cons_zero, List.getD_cons_succ, csrOut] at h2a h2b h2c
  have hin2 : ∀ a < 2 + 3 * G.m, mem2 a = mem a := fun a ha => by
    rw [h2c a (by omega), hin1 a ha]
  have hPW2 : ∀ q < G.m, mem2 (8 + 4 * G.m + 0 * G.n + q) = (pgOf G).pω q := fun q hq => by
    rw [h2c _ (by omega), h1b _ (Or.inl (by omega))]
    have := (hPW q hq).1; unfold aPW at this; simpa using this
  have hkey : ∀ i < G.m, mem1 (8 + 5 * G.m + 0 * G.n + i) =
      min (mem2 (2 + 3 * i)) (mem2 (2 + 3 * i + 1)) := fun i hi => by
    rw [h1a i hi, hin2 _ (by omega), hin2 _ (by omega)]
  -- one lightest pair for each pair of ends
  wram_step
  · refine ⟨rfl, fun q hq => ?_, fun u hu => ?_, fun u hu j hj => ?_, fun q hq => ?_,
      by simp [DDE.ofArgs]; omega, by simp [DDE.ofArgs]; omega, by simp [DDE.ofArgs]; omega,
      by simp [DDE.ofArgs]; omega, by simp [DDE.ofArgs]; omega, by simp [DDE.ofArgs]; omega,
      by simp [DDE.ofArgs]; omega⟩
    · show mem2 (2 + 3 * q) < G.n ∧ mem2 (2 + 3 * q + 1) < G.n
      simp only [DDE.ofArgs, List.getD_cons_zero, List.getD_cons_succ] at hq
      rw [hin2 _ (by omega), hin2 _ (by omega), (hends q hq).1, (hends q hq).2]; exact hpG q hq
    · show mem2 (8 + 6 * G.m + 0 * G.n + u) = offOf (fun q => min (mem2 (2 + 3 * q)) (mem2 (2 + 3 * q + 1))) G.m u
      simp only [DDE.ofArgs, List.getD_cons_zero, List.getD_cons_succ] at hu
      rw [h2a u hu]; exact offOf_congr (fun i hi => hkey i hi) u
    · simp only [DDE.ofArgs, List.getD_cons_zero, List.getD_cons_succ] at hu hj ⊢
      have hc := offOf_congr (M := G.m) (f := fun i => mem1 (8 + 5 * G.m + 0 * G.n + i))
        (g := fun q => min (mem2 (2 + 3 * q)) (mem2 (2 + 3 * q + 1))) hkey u
      have hg := grp_congr (M := G.m) (f := fun i => mem1 (8 + 5 * G.m + 0 * G.n + i))
        (g := fun q => min (mem2 (2 + 3 * q)) (mem2 (2 + 3 * q + 1))) hkey u
      have := h2b u hu j (by rw [hg]; exact hj)
      rw [hc, hg] at this
      exact this
    · show mem2 (8 + 4 * G.m + 0 * G.n + q) < 2 ^ w
      simp only [DDE.ofArgs, List.getD_cons_zero, List.getD_cons_succ] at hq
      rw [hPW2 q hq]; have := pω_le_maxω (G := G) hq; omega
  intro c mem3 pos3 h3
  obtain ⟨h3c, h3o, h3cov, h3inj, h3f⟩ := h3
  simp only [DDE.ofArgs, List.getD_cons_zero, List.getD_cons_succ, DDE.key, DDE.oth, DDE.wt,
    DDE.pu, DDE.pv] at h3c h3o h3cov h3inj h3f
  have hin3 : ∀ a < 2 + 3 * G.m, mem3 a = mem a := fun a ha => by
    rw [h3f a (by omega), hin2 a ha]
  have hu2 : ∀ q < G.m, mem2 (2 + 3 * q) = (pgOf G).pu q ∧ mem2 (2 + 3 * q + 1) = (pgOf G).pv q :=
    fun q hq => by rw [hin2 _ (by omega), hin2 _ (by omega)]; exact hends q hq
  have hEX3 : ∀ q < G.m, mem3 (8 + 3 * G.m + 0 * G.n + q) = mem (aEXP G.n G.m + q) := fun q hq => by
    rw [h3f _ (by omega), h2c _ (by omega), h1b _ (Or.inl (by omega))]; unfold aEXP; congr 1; omega
  obtain ⟨o, ho⟩ : ∃ o : ℕ → ℕ, ∀ j, mem3 (9 + 7 * G.m + 4 * G.n + j) = o j := ⟨_, fun _ => rfl⟩
  simp only [ho] at h3o h3cov h3inj
  have hcov : ∀ q < G.m, ∃ j < c, KS.SameEnds (pgOf G) q (o j) ∧ (pgOf G).pω (o j) ≤ (pgOf G).pω q := by
    intro q hq
    obtain ⟨j, hj, e1, e2, e3⟩ := h3cov q hq
    have hoj := h3o j hj
    rw [(hu2 _ hoj).1, (hu2 _ hoj).2, (hu2 _ hq).1, (hu2 _ hq).2] at e1 e2
    rw [hPW2 _ hoj, hPW2 _ hq] at e3
    refine ⟨j, hj, ?_, e3⟩
    unfold KS.SameEnds
    rcases same_ends_of e1 e2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hc2 : c ≤ G.n * G.n := by
    refine card_le_sq (k := fun j => min ((pgOf G).pu (o j)) ((pgOf G).pv (o j)))
      (o := fun j => (pgOf G).pu (o j) + (pgOf G).pv (o j) - min ((pgOf G).pu (o j)) ((pgOf G).pv (o j)))
      (fun j hj => ?_) (fun j1 h1 j2 h2 e1 e2 => ?_)
    · have := hpG _ (h3o j hj); omega
    · have := h3inj j1 h1 j2 h2
      rw [(hu2 _ (h3o j1 h1)).1, (hu2 _ (h3o j1 h1)).2, (hu2 _ (h3o j2 h2)).1,
        (hu2 _ (h3o j2 h2)).2] at this
      exact this e1 e2
  have hkw : ∀ j < c, mem3 (8 + 3 * G.m + 0 * G.n + o j) * G.m + o j < 2 ^ w := fun j hj => by
    have hoj := h3o j hj
    rw [hEX3 _ hoj]
    refine hG.key_lt ?_ hoj
    have h1 := (hPW _ hoj).2
    have h2 := pω_le_maxω (G := G) hoj
    have h3 : mem (aEXP G.n G.m + o j) < 2 ^ mem (aEXP G.n G.m + o j) := Nat.lt_two_pow_self
    omega
  -- the sort keys
  wram_step
  · refine ⟨⟨c, _, _, _, _, rfl, by omega, by omega, by omega, by omega, fun j hj => ⟨?_, ?_⟩⟩,
      by simp, by simp; omega⟩
    · show mem3 _ < _; rw [ho]; exact h3o j hj
    · show mem3 (8 + 3 * G.m + 0 * G.n + mem3 (9 + 7 * G.m + 4 * G.n + j)) * G.m +
        mem3 (9 + 7 * G.m + 4 * G.n + j) < _
      rw [ho]; exact hkw j hj
  intro v4 mem4 pos4 h4
  obtain ⟨h4a, h4b⟩ := h4
  simp only [List.getD_cons_zero, List.getD_cons_succ, keyF, ho] at h4a h4b
  -- the heap sort
  wram_step
  · refine ⟨_, _, rfl, by omega, by omega, by omega, fun i hi => ?_⟩
    show mem4 (9 + 8 * G.m + 4 * G.n + i) < 2 ^ w
    rw [h4a i hi]; exact hkw i hi
  intro v5 mem5 pos5 h5
  obtain ⟨-, h5p, h5s, h5w, h5f⟩ := h5
  simp only [List.getD_cons_zero, List.getD_cons_succ] at h5p h5s h5w h5f
  have hperm : (tab c fun i => mem5 (9 + 8 * G.m + 4 * G.n + i)).Perm
      (tab c fun j => mem (aEXP G.n G.m + o j) * G.m + o j) := by
    refine h5p.trans (List.Perm.of_eq (tab_congr fun j hj => ?_))
    rw [h4a j hj, hEX3 _ (h3o j hj)]
  obtain ⟨hLo, hsort, hLin⟩ := sorted_keys (G := pgOf G) (ex := fun q => mem (aEXP G.n G.m + q)) h3o
    (fun j hj => (hPW _ (h3o j hj)).2) hperm h5s
  have hkL : kL mem5 (9 + 8 * G.m + 4 * G.n) G.m c =
      (tab c fun i => mem5 (9 + 8 * G.m + 4 * G.n + i)).map (· % G.m) := by
    unfold kL tab; rw [List.map_map]; rfl
  have hin5 : ∀ a < 9 + 7 * G.m + 2 * G.n, mem5 a = mem2 a := fun a ha => by
    rw [h5f a (Or.inl (by omega)), h4b a (Or.inl (by omega)), h3f a (Or.inl ha)]
  have hL : ∀ q ∈ kL mem5 (9 + 8 * G.m + 4 * G.n) G.m c, q < (pgOf G).m := by
    rw [hkL, pgOf_m]; intro q hq; obtain ⟨j, hj, rfl⟩ := hLo q hq; exact h3o j hj
  have hcov' : ∀ q < (pgOf G).m, ∃ r0 ∈ kL mem5 (9 + 8 * G.m + 4 * G.n) G.m c,
      KS.SameEnds (pgOf G) q r0 ∧ (pgOf G).pω r0 ≤ (pgOf G).pω q := by
    rw [hkL, pgOf_m]; intro q hq
    obtain ⟨j, hj, h1, h2⟩ := hcov q hq
    exact ⟨o j, hLin j hj, h1, h2⟩
  have hpG' : ∀ q < (pgOf G).m, (pgOf G).pu q < (pgOf G).n ∧ (pgOf G).pv q < (pgOf G).n := by
    rw [pgOf_m]; exact hpG
  -- Kruskal's algorithm
  wram_step
  · refine ⟨c, 9 + 8 * G.m + 4 * G.n, G.m, 2, 8 + 4 * G.m + 0 * G.n,
      kLOf G.n G.m, rfl, ⟨by simp only [kLOf]; omega, by simp only [kLOf]; omega,
        by simp only [kLOf]; omega, by simp only [kLOf]; omega, by simp only [kLOf]; omega,
        by simp only [kLOf]; omega, by simp only [kLOf]; omega⟩, rfl, hL, by rw [hkL]; exact hsort,
      hcov', hpG', fun q hq => ?_, fun i hi => h5w i hi, by simp only [kLOf, pgOf_m]; omega,
      by simp only [kLOf, pgOf_m]; omega, by simp only [kLOf]; omega, by simp only [kLOf]; omega,
      by simp only [kLOf]; omega⟩
    rw [pgOf_m] at hq
    show mem5 _ = _ ∧ mem5 _ = _ ∧ mem5 _ = _
    rw [hin5 _ (by omega), hin5 _ (by omega), hin5 _ (by omega), hPW2 q hq]
    exact ⟨(hu2 q hq).1, (hu2 q hq).2, rfl⟩
  intro v6 mem6 pos6 h6
  obtain ⟨hv6, ⟨dep, hK⟩, h6f⟩ := h6 c (9 + 8 * G.m + 4 * G.n) G.m 2 (8 + 4 * G.m + 0 * G.n)
    (kLOf G.n G.m) rfl
  have hconn : ∀ v < (pgOf G).n, (pgOf G).Reach ↑(Finset.range (pgOf G).n) 0 v := fun v hv =>
    (root_conn hG.allowed.valid hG.allowed.conn).2 v (by simp [root]; exact hv)
  have hok := KS.krun_ok hL (by rw [hkL]; exact hsort) hcov' hpG' hconn hG.two_le
  have hcnt := hK.cnt
  simp only [kLOf] at hcnt
  wram_step
  · refine ⟨_, hok, hv6, by omega, fun k hk => ⟨hK.par k hk, hK.mw k hk⟩,
      fun k h1 h2 => hK.ch k h1 h2, fun a ha => ?_⟩
    unfold aTLK aKSZ at ha
    show mem6 a = mem a
    have e5 : mem5 a = mem4 a := h5f a (by omega)
    have e6 : mem6 a = mem5 a := h6f a (by simp only [kLOf]; omega)
    rw [e6, e5, h4b a (by omega), h3f a (by omega),
      h2c a (by omega), h1b a (by omega)]
  · simp only [kC, kCost, tabC, csrC, ddC, heapSortContract, krC, List.getD_cons_zero,
      List.getD_cons_succ, Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin,
      argsSize_cons, argsSize_nil, eMin, eEnd0, eEnd1, eKey, eOut]
    have hA : c * Nat.log 2 (c + 2) ≤ G.m * Nat.log 2 (G.n * G.n + 2) :=
      Nat.mul_le_mul h3c (Nat.log_mono_right (by omega))
    have hB : c * Nat.log 2 G.n ≤ G.m * Nat.log 2 G.n := Nat.mul_le_mul_right _ h3c
    nlinarith

end MinCostFlow.LowStretch
