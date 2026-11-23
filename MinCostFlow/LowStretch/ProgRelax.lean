module

public import MinCostFlow.LowStretch.DijRep

/-!
# Relaxing all arcs of a vertex

`relaxAll` takes a vertex `u` that Dijkstra has just settled, with key `k`, and relaxes its arcs
one by one: for arc `j` to a vertex `h` of the graph, if `k + cost j` is below the tentative cost
of `h`, it writes the new cost, records `u` and `j` as the parent and the parent arc of `h`, and
pushes `(k + cost j, h)` to the queue of the class of `j`.
Each arc costs `O(log J)` (`relaxAll_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The arguments of `relaxAll`. -/
def DL.args (L : DL) (u k : ℕ) : List ℕ :=
  [L.D, L.J, L.A, L.INF, L.LO, L.HI, L.HD, L.CS, L.CL, L.OK, L.os, L.TS, L.NN, L.rs, u, k]

/-- The body of the loop over the arcs, with the arc in register `16`. -/
def relaxBody (bPush : ℕ) : Stmt :=
  .seq (.assign 18 (.load (.bin .add (.reg 6) (.reg 16))))
  (.cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 18))) (.reg 10))
    (.seq (.assign 19 (.bin .add (.reg 15) (.load (.bin .add (.reg 7) (.reg 16)))))
    (.seq (.assign 20 (.load (.bin .add (.reg 11) (.reg 18))))
    (.seq (.assign 21 (.load (.bin .add (.bin .add (.reg 11) (.reg 12)) (.reg 18))))
    (.seq (.cond (.bin .eq (.reg 20) (.reg 13)) .nop (.assign 21 (.reg 3)))
    (.cond (.bin .lt (.reg 19) (.reg 21))
      (.seq (.assign 23 (.load (.bin .add (.reg 8) (.reg 16))))
      (.seq (.store (.bin .add (.reg 11) (.reg 18)) (.reg 13))
      (.seq (.store (.bin .add (.bin .add (.reg 11) (.reg 12)) (.reg 18)) (.reg 19))
      (.seq (.store (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 3) (.reg 12))) (.reg 18))
        (.reg 14))
      (.seq (.store (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 4) (.reg 12))) (.reg 18))
        (.reg 16))
        (.call 22 bPush [.reg 0, .reg 1, .reg 2, .reg 23, .reg 19, .reg 18]))))))
      .nop)))))
    .nop)

/-- `relaxAll (L.args u k)`: relax every arc of `u`. Procedure `bPush` is `pqPush`. -/
def relaxAll (bPush : ℕ) : Stmt :=
  .seq (.assign 16 (.load (.bin .add (.reg 4) (.reg 14))))
  (.seq (.assign 17 (.load (.bin .add (.reg 5) (.reg 14))))
  (.seq (forUp 16 (.reg 17) (relaxBody bPush))
  (.ret (.const 0))))

theorem relaxAll_noRand (bPush : ℕ) : (relaxAll bPush).NoRand := by
  simp [relaxAll, relaxBody, forUp, Stmt.NoRand]

/-- The ghost values of `relaxAll`. -/
structure RlxG where
  L : DL
  Nodes : Finset ℕ
  s : ℕ
  u : ℕ
  d : DS
  qs : ℕ → List (ℕ × ℕ)
  cnt : ℕ

/-- The cells that `relaxAll` leaves alone. -/
def DL.Keep (L : DL) (a : ℕ) : Prop :=
  a < L.TS ∨ (L.TS + 2 * L.NN ≤ a ∧ a < L.TS + 3 * L.NN) ∨ (L.TS + 5 * L.NN ≤ a ∧ a < L.D + 3) ∨
    L.D + pqSize L.J L.A ≤ a

/-- The precondition of `relaxAll`. -/
def relaxPre (w : ℕ) (G : RlxG) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  args = G.L.args G.u G.d.L ∧ G.L.Shape w mem G.Nodes ∧ G.L.Rep mem G.Nodes G.d G.qs ∧
    (G.L.g mem).Inv G.s G.L.INF G.u ((G.L.g mem).lo G.u) G.d ∧ G.d.sett G.u ∧ G.u ∈ G.Nodes ∧
    (∀ c < G.L.J, mem (pqT G.L.D G.L.J c) ≤ G.cnt) ∧ G.cnt + G.L.deg mem G.u ≤ G.L.A ∧
    (G.L.g mem).ParInv G.s G.L.INF G.d (G.L.par mem) (G.L.parc mem) ∧ G.L.TZ mem G.qs ∧
    G.L.Stamps mem

/-- The postcondition of `relaxAll`. -/
def relaxPost (w : ℕ) (G : RlxG) (_ : List ℕ) (mem : ℕ → ℕ) (_ : ℕ) (mem' : ℕ → ℕ) : Prop :=
  ∃ d' qs', G.L.Shape w mem' G.Nodes ∧ G.L.Rep mem' G.Nodes d' qs' ∧
    (G.L.g mem).Inv G.s G.L.INF G.u ((G.L.g mem).hi G.u) d' ∧ d'.sett = G.d.sett ∧
    d'.L = G.d.L ∧ (∀ c < G.L.J, mem' (pqT G.L.D G.L.J c) ≤ G.cnt + G.L.deg mem G.u) ∧
    (pqAll G.L.J qs').length ≤ (pqAll G.L.J G.qs).length + G.L.deg mem G.u ∧
    (∀ a, G.L.Keep a → mem' a = mem a) ∧
    (G.L.g mem).ParInv G.s G.L.INF d' (G.L.par mem') (G.L.parc mem') ∧ G.L.TZ mem' qs' ∧
    G.L.Stamps mem'

/-- The cost of `relaxAll`: `O(log J)` for each arc. -/
def relaxCost (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  (mem (args.getD 5 0 + args.getD 14 0) - mem (args.getD 4 0 + args.getD 14 0) + 1) *
    (50 * (Nat.log 2 (args.getD 1 0) + 2) + 300)

/-- The contract of `relaxAll`. -/
def relaxAllC (w : ℕ) : Contract := ghostC (relaxPre w) (relaxPost w) relaxCost

theorem Triple.of_eq {w : ℕ} {p : Program} {P : State → Prop} {s : Stmt}
    {Q : Outcome → State → Prop} {T : State → ℕ}
    (h : ∀ st0, P st0 → Triple w p (fun st => st = st0) s Q T) : Triple w p P s Q T :=
  fun st ω hP => h st hP st ω rfl

/-! ### The invariant of the loop over the arcs -/

/-- The memory part of the invariant, after the arcs of `u` below `i`. -/
def RInv (w : ℕ) (G : RlxG) (mem0 : ℕ → ℕ) (i : ℕ) (M : ℕ → ℕ) : Prop :=
  ∃ d qs, G.L.Shape w M G.Nodes ∧ G.L.Rep M G.Nodes d qs ∧
    (G.L.g mem0).Inv G.s G.L.INF G.u i d ∧ d.sett = G.d.sett ∧ d.L = G.d.L ∧
    (∀ c < G.L.J, M (pqT G.L.D G.L.J c) ≤ G.cnt + (i - (G.L.g mem0).lo G.u)) ∧
    (pqAll G.L.J qs).length ≤ (pqAll G.L.J G.qs).length + (i - (G.L.g mem0).lo G.u) ∧
    (∀ a, G.L.Keep a → M a = mem0 a) ∧ (G.L.g mem0).ParInv G.s G.L.INF d (G.L.par M) (G.L.parc M) ∧
    G.L.TZ M qs ∧ G.L.Stamps M

theorem rinv_start {w : ℕ} {G : RlxG} {args : List ℕ} {mem0 : ℕ → ℕ}
    (h : relaxPre w G args mem0) : RInv w G mem0 ((G.L.g mem0).lo G.u) mem0 := by
  obtain ⟨-, hs, hr, hi, -, -, hcap, -, hp, hz, hS⟩ := h
  exact ⟨G.d, G.qs, hs, hr, hi, rfl, rfl, fun c hc => by simpa using hcap c hc, by simp,
    fun _ _ => rfl, hp, hz, hS⟩

theorem keep_of_lt {L : DL} {a : ℕ} (h : a < L.TS) : L.Keep a := Or.inl h

/-- The graph seen from the current memory is the graph at the start. -/
theorem RInv.g_eq {w : ℕ} {G : RlxG} {mem0 M : ℕ → ℕ} {i : ℕ} (h : RInv w G mem0 i M) :
    G.L.g M = G.L.g mem0 := by
  obtain ⟨d, qs, hs, -, -, -, -, -, -, hk, -, -, -⟩ := h
  have := DL.g_congr G.L hs (fun a ha => (hk a (keep_of_lt ha)).symm)
  exact this.symm

/-- **No change.** The arc leaves the graph, or does not improve the cost of its head. -/
theorem rinv_no {w : ℕ} {G : RlxG} {mem0 M : ℕ → ℕ} {i : ℕ} (h : RInv w G mem0 i M)
    (hsu : G.d.sett G.u) (hu : G.u ∈ G.Nodes) (hi1 : (G.L.g mem0).lo G.u ≤ i)
    (hi2 : i < (G.L.g mem0).hi G.u)
    (hno : ¬ (M (G.L.OK + M (G.L.HD + i)) = G.L.os ∧
      G.d.L + M (G.L.CS + i) < G.L.tentOf M (M (G.L.HD + i)))) :
    RInv w G mem0 (i + 1) M := by
  have hg := h.g_eq
  obtain ⟨d, qs, hs, hr, hinv, hsett, hL, hcap, hlen, hk, hp, hz, hS⟩ := h
  rw [← hg] at hi2 hinv
  obtain ⟨hjM, hhd, hcs⟩ := DL.arc_data hs hu hi2
  have hhN := (hs.heads i hjM).1
  have hsu' : d.sett G.u := by rw [hsett]; exact hsu
  have hcL := hinv.cur_L hsu'
  have hstep := (hinv.relax hsu' (by rw [hg]; exact hi1) hi2).2 (by
    rintro ⟨hok, hlt⟩
    rw [hhd] at hok hlt
    rw [hcs, hcL, hr.tent, if_pos ((hs.ok_iff _).mp hok), hL] at hlt
    exact hno ⟨hok.2, hlt⟩)
  rw [hg] at hstep
  exact ⟨d, qs, hs, hr, hstep, hsett, hL, fun c hc => by have := hcap c hc; omega,
    by omega, hk, hp, hz, hS⟩

/-- The memory after the four stores of an improving relax step of arc `j` of `u`. -/
def relaxMem (L : DL) (M : ℕ → ℕ) (h k u j : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update M (L.TS + h) L.rs)
    (L.TS + L.NN + h) k) (L.TS + 3 * L.NN + h) u) (L.TS + 4 * L.NN + h) j

theorem relaxMem_eq {L : DL} {M : ℕ → ℕ} {h k u j a : ℕ} (hh : h < L.NN)
    (ha : a < L.TS ∨ (L.TS + 2 * L.NN ≤ a ∧ a < L.TS + 3 * L.NN) ∨ L.TS + 5 * L.NN ≤ a) :
    relaxMem L M h k u j a = M a := by
  unfold relaxMem
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem relaxMem_low {L : DL} {M : ℕ → ℕ} {h k u j a : ℕ} (hh : h < L.NN)
    (ha : a < L.TS + 3 * L.NN) :
    relaxMem L M h k u j a = Function.update (Function.update M (L.TS + h) L.rs)
      (L.TS + L.NN + h) k a := by
  unfold relaxMem
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem relaxMem_par {L : DL} {M : ℕ → ℕ} {h k u j v : ℕ} (hh : h < L.NN) (hv : v < L.NN) :
    relaxMem L M h k u j (L.TS + 3 * L.NN + v) = Function.update (L.par M) h u v ∧
      relaxMem L M h k u j (L.TS + 4 * L.NN + v) = Function.update (L.parc M) h j v := by
  unfold relaxMem DL.par DL.parc
  simp only [Function.update_apply]
  constructor <;> split_ifs <;> first | rfl | omega

theorem DL.Stamps.relax {L : DL} {M : ℕ → ℕ} {h k u j : ℕ} (hS : L.Stamps M) (hh : h < L.NN) :
    L.Stamps (relaxMem L M h k u j) := by
  intro v hv
  obtain ⟨a, b⟩ := hS v hv
  unfold relaxMem
  simp only [Function.update_apply]
  constructor <;> split_ifs <;> omega

theorem keep_split {L : DL} {a : ℕ} (hl : L.TS + 5 * L.NN ≤ L.D) (ha : L.Keep a) :
    (a < L.TS ∨ (L.TS + 2 * L.NN ≤ a ∧ a < L.TS + 3 * L.NN) ∨ L.TS + 5 * L.NN ≤ a) ∧
      (a < L.D + 3 ∨ L.D + pqSize L.J L.A ≤ a) := by
  rcases ha with ha | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ha <;> omega

/-- Before the push of an improving relax step, the precondition of `pqPush` holds. -/
theorem rinv_pushPre {w : ℕ} {G : RlxG} {mem0 M : ℕ → ℕ} {i : ℕ} (h : RInv w G mem0 i M)
    (hu : G.u ∈ G.Nodes) (hi2 : i < (G.L.g mem0).hi G.u)
    (hcnt : G.cnt + G.L.deg mem0 G.u ≤ G.L.A) (hi1 : (G.L.g mem0).lo G.u ≤ i)
    (hok : M (G.L.OK + M (G.L.HD + i)) = G.L.os)
    (hlt : G.d.L + M (G.L.CS + i) < G.L.tentOf M (M (G.L.HD + i))) :
    (pqPushC w).pre [G.L.D, G.L.J, G.L.A, M (G.L.CL + i), G.d.L + M (G.L.CS + i), M (G.L.HD + i)]
      (relaxMem G.L M (M (G.L.HD + i)) (G.d.L + M (G.L.CS + i)) G.u i) := by
  have hg := h.g_eq
  obtain ⟨d, qs, hs, hr, hinv, hsett, hL, hcap, hlen, hk, -, -, -⟩ := h
  have hdeg : G.L.deg mem0 G.u = (G.L.g mem0).hi G.u - (G.L.g mem0).lo G.u := rfl
  have hi2' : i < (G.L.g M).hi G.u := by rw [hg]; exact hi2
  rw [← hg] at hinv
  obtain ⟨hjM, hhd, hcs⟩ := DL.arc_data hs hu hi2'
  have hh := hs.heads i hjM
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hD : ∀ k a, G.L.D ≤ a → relaxMem G.L M (M (G.L.HD + i)) k G.u i a = M a :=
    fun k a ha => relaxMem_eq hh.1 (Or.inr (Or.inr (by omega)))
  have hokN : M (G.L.HD + i) ∈ G.Nodes := (hs.ok_iff _).mp ⟨hh.1, hok⟩
  rw [← hL] at hlt
  obtain ⟨p1, p2, p3⟩ := DL.Rep.push_pre hs hr hinv hu hi2' hokN hlt hcap (by omega)
  refine ⟨G.L.D, G.L.J, G.L.A, G.L.INF, qs, M (G.L.CL + i), G.d.L + M (G.L.CS + i),
    M (G.L.HD + i), rfl, DL.PQRep.congr hr.pq fun a ha _ => hD _ a ha, hs.fits, hh.2.1, ?_, ?_, ?_⟩
  · rw [hD _ _ (pqT_bounds (A := 0) hh.2.1).2.1]; exact p1
  · rw [← hL]; exact p2
  · rw [← hL]; exact p3

/-- **An improving relax step**: after the stores and the push, the invariant holds for the next
arc. -/
theorem rinv_yes {w : ℕ} {G : RlxG} {mem0 M M2 : ℕ → ℕ} {i v : ℕ} (h : RInv w G mem0 i M)
    (hsu : G.d.sett G.u) (hu : G.u ∈ G.Nodes) (hi1 : (G.L.g mem0).lo G.u ≤ i)
    (hi2 : i < (G.L.g mem0).hi G.u)
    (hok : M (G.L.OK + M (G.L.HD + i)) = G.L.os)
    (hlt : G.d.L + M (G.L.CS + i) < G.L.tentOf M (M (G.L.HD + i)))
    (hpost : (pqPushC w).post [G.L.D, G.L.J, G.L.A, M (G.L.CL + i), G.d.L + M (G.L.CS + i),
      M (G.L.HD + i)] (relaxMem G.L M (M (G.L.HD + i)) (G.d.L + M (G.L.CS + i)) G.u i) v M2) :
    RInv w G mem0 (i + 1) M2 := by
  have hg := h.g_eq
  obtain ⟨d, qs, hs, hr, hinv, hsett, hL, hcap, hlen, hk, hp, hz, hS⟩ := h
  have hi2' : i < (G.L.g M).hi G.u := by rw [hg]; exact hi2
  have hi1' : (G.L.g M).lo G.u ≤ i := by rw [hg]; exact hi1
  rw [← hg] at hinv
  obtain ⟨hjM, hhd, hcs⟩ := DL.arc_data hs hu hi2'
  have hh := hs.heads i hjM
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hD : ∀ k a, G.L.D ≤ a → relaxMem G.L M (M (G.L.HD + i)) k G.u i a = M a :=
    fun k a ha => relaxMem_eq hh.1 (Or.inr (Or.inr (by omega)))
  have hpq1 := DL.PQRep.congr hr.pq fun a ha _ => hD (G.d.L + M (G.L.CS + i)) a ha
  obtain ⟨hpq2, htails, hfr⟩ := hpost G.L.D G.L.J G.L.A G.L.INF qs _ _ _ rfl hpq1
  have hokN : M (G.L.HD + i) ∈ G.Nodes := (hs.ok_iff _).mp ⟨hh.1, hok⟩
  have hsu' : d.sett G.u := by rw [hsett]; exact hsu
  rw [← hL] at hlt hpq2 htails hfr
  obtain ⟨hs2, hr2, hinv2⟩ := DL.Rep.relax_improve hs hr hinv hsu' hu hi1' hi2' hokN hlt hpq2
    (fun a ha => by rw [hfr a (Or.inl (by omega)), relaxMem_low hh.1 ha])
  rw [← hg] at hp
  have hp2 := DL.Rep.relax_par (M := M2) hs hr hp hinv hsu' hu hi1' hi2' hokN hlt
    (pqAll G.L.J (Function.update qs (M (G.L.CL + i))
      (qs (M (G.L.CL + i)) ++ [(d.L + M (G.L.CS + i), M (G.L.HD + i))])))
    (fun v hv => by
      rw [hfr _ (Or.inl (by omega)), hfr _ (Or.inl (by omega))]
      exact relaxMem_par hh.1 hv)
  rw [hg] at hinv2 hp2
  refine ⟨_, _, hs2, hr2, hinv2, hsett, hL, fun c hc => ?_, ?_, fun a ha => ?_, hp2,
    hz.push fun c' hc' hne => ?_, (hS.relax hh.1).congr l7 fun a ha => hfr a (Or.inl (by omega))⟩
  · rw [htails c hc]
    have := hcap c hc
    have := hcap _ hh.2.1
    rw [hD _ _ (pqT_bounds (A := 0) hh.2.1).2.1, hD _ _ (pqT_bounds (A := 0) hc).2.1]
    split_ifs <;> omega
  · rw [DL.length_pqAll_push hh.2.1]; omega
  · have hks := keep_split l7 ha
    rw [hfr a hks.2, relaxMem_eq hh.1 hks.1, hk a ha]
  · rw [htails c' hc', if_neg hne, hD _ _ (pqT_bounds (A := 0) hc').2.1]

/-- At the end of the loop, the postcondition holds. -/
theorem rinv_end {w : ℕ} {G : RlxG} {mem0 M : ℕ → ℕ} {args : List ℕ} {v : ℕ}
    (h : RInv w G mem0 ((G.L.g mem0).hi G.u) M) : relaxPost w G args mem0 v M := by
  obtain ⟨d, qs, hs, hr, hinv, hsett, hL, hcap, hlen, hk, hp, hz, hS⟩ := h
  exact ⟨d, qs, hs, hr, hinv, hsett, hL, hcap, hlen, hk, hp, hz, hS⟩

/-- The loop invariant: the registers of the arguments and the bound, the counter, and
`RInv`. -/
def relaxInv (w : ℕ) (G : RlxG) (mem0 : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  (∀ r < 16, st.regs r = (G.L.args G.u G.d.L).getD r 0) ∧
    st.regs 17 = (G.L.g mem0).hi G.u ∧ st.regs 16 = i ∧ RInv w G mem0 i st.mem

theorem relaxInv_next {w : ℕ} {G : RlxG} {mem0 : ℕ → ℕ} {i : ℕ} {st1 : State}
    (hr : ∀ r < 16, st1.regs r = (G.L.args G.u G.d.L).getD r 0)
    (h17 : st1.regs 17 = (G.L.g mem0).hi G.u) (h16 : st1.regs 16 = i)
    (hm : RInv w G mem0 (i + 1) st1.mem) :
    relaxInv w G mem0 (i + 1) { st1 with regs := Function.update st1.regs 16 (i + 1) } ∧
      st1.regs 16 = i := by
  refine ⟨⟨fun r hr' => ?_, ?_, by simp, hm⟩, h16⟩
  · simp only
    rw [Function.update_of_ne (by omega), hr r hr']
  · simp only
    rw [Function.update_of_ne (by omega), h17]

theorem A_lt_of_fits {w D J A INF : ℕ} (hJ : 1 ≤ J) (h : PQFits w D J A INF) : A < 2 ^ w := by
  have h1 := h.1
  unfold pqSize at h1
  have : A ≤ 2 * J * A := by nlinarith
  omega

theorem relax_cost_le (a b : ℕ) :
    a * (50 * (b + 2) + 280 + 1 + 8) + 100 ≤ (a + 1) * (50 * (b + 2) + 300) := by
  nlinarith

theorem relaxInv_next2 {w : ℕ} {G : RlxG} {mem0 : ℕ → ℕ} {i : ℕ} {st1 : State}
    (hr : ∀ r < 18, st1.regs r = (G.L.args G.u G.d.L ++ [i, (G.L.g mem0).hi G.u]).getD r 0)
    (hm : RInv w G mem0 (i + 1) st1.mem) :
    relaxInv w G mem0 (i + 1) { st1 with regs := Function.update st1.regs 16 (i + 1) } ∧
      st1.regs 16 = i :=
  relaxInv_next (fun r h => by rw [hr r (by omega)]; interval_cases r <;> rfl)
    (hr 17 (by norm_num)) (hr 16 (by norm_num)) hm

/-- The registers in the loop, as a chain of updates, so that the evaluation of an expression
finds their values. -/
theorem relax_regs {w : ℕ} {G : RlxG} {mem0 : ℕ → ℕ} {i : ℕ} {st : State}
    (h : relaxInv w G mem0 i st) :
    st = { mem := st.mem, regs := (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update st.regs 0 (G.L.D)) 1 (G.L.J)) 2 (G.L.A)) 3 (G.L.INF)) 4 (G.L.LO)) 5 (G.L.HI)) 6 (G.L.HD)) 7 (G.L.CS)) 8 (G.L.CL)) 9 (G.L.OK)) 10 (G.L.os)) 11 (G.L.TS)) 12 (G.L.NN)) 13 (G.L.rs)) 14 (G.u)) 15 (G.d.L)) 16 (i)) 17 ((G.L.g mem0).hi G.u)), pos := st.pos } := by
  obtain ⟨hR, hR17, hR16, -⟩ := h
  cases st with
  | mk mem regs pos =>
    simp only [State.mk.injEq, true_and, and_true]
    funext r
    by_cases hr : r < 18
    · interval_cases r <;> simp only [Function.update_apply, Nat.reduceEqDiff, ↓reduceIte] <;>
        first | exact hR _ (by norm_num) | exact hR17 | exact hR16
    · repeat rw [Function.update_of_ne (by omega)]

theorem relaxAll_spec {w : ℕ} {p : Program} {b bPush : ℕ} (hp : p.HasAt b [relaxAll bPush])
    (hP : MeetsContract w p bPush (pqPushC w)) : MeetsContract w p b (relaxAllC w) := by
  have hproc : p.procs[b]? = some (relaxAll bPush) := hp 0 (by simp)
  refine meets_of_ghost hproc ?_
  intro G args mem0 pos hwords hpre
  have hpre' := hpre
  obtain ⟨rfl, hs, hr, hinv, hsu, hu, hcap, hbud, -, -, -⟩ := hpre
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have huN : G.u < G.L.NN := ((hs.ok_iff _).mpr hu).1
  have hlo : (G.L.g mem0).lo G.u = mem0 (G.L.LO + G.u) := by simp [DL.g, huN]
  have hhi : (G.L.g mem0).hi G.u = mem0 (G.L.HI + G.u) := by simp [DL.g, huN]
  have harc := hs.arcs G.u hu
  have hfit := hs.fits
  obtain ⟨hf1, hf2, hf3⟩ := hfit
  unfold pqSize at hf1
  have hD : G.L.D < 2 ^ w := by omega
  -- the loop
  have hloop : Triple w p (relaxInv w G mem0 ((G.L.g mem0).lo G.u)) (forUp 16 (.reg 17) (relaxBody bPush))
      (normalPost (relaxInv w G mem0 ((G.L.g mem0).hi G.u)))
      (fun _ => ((G.L.g mem0).hi G.u - (G.L.g mem0).lo G.u) *
        (50 * (Nat.log 2 G.L.J + 2) + 280 + (Expr.reg 17).size + 8) + ((Expr.reg 17).size + 3)) := by
    refine Triple.forUp_const (50 * (Nat.log 2 G.L.J + 2) + 280) _ _ harc.1 (by omega)
      (fun _ => by omega) (fun i st _ _ hI => hI.2.2.1) (fun i st _ _ hI => ?_) ?_
    · simp [Expr.eval, hI.2.1]
    intro i hi1 hi2
    refine Triple.of_eq fun st0 hI => ?_
    have hI' := hI
    obtain ⟨hR, hR17, hR16, hm⟩ := hI'
    have e0 : st0.regs 0 = G.L.D := hR 0 (by norm_num)
    have e1 : st0.regs 1 = G.L.J := hR 1 (by norm_num)
    have e2 : st0.regs 2 = G.L.A := hR 2 (by norm_num)
    have e3 : st0.regs 3 = G.L.INF := hR 3 (by norm_num)
    have e6 : st0.regs 6 = G.L.HD := hR 6 (by norm_num)
    have e7 : st0.regs 7 = G.L.CS := hR 7 (by norm_num)
    have e8 : st0.regs 8 = G.L.CL := hR 8 (by norm_num)
    have e9 : st0.regs 9 = G.L.OK := hR 9 (by norm_num)
    have e10 : st0.regs 10 = G.L.os := hR 10 (by norm_num)
    have e11 : st0.regs 11 = G.L.TS := hR 11 (by norm_num)
    have e12 : st0.regs 12 = G.L.NN := hR 12 (by norm_num)
    have e13 : st0.regs 13 = G.L.rs := hR 13 (by norm_num)
    have e15 : st0.regs 15 = G.d.L := hR 15 (by norm_num)
    have hm' := hm
    obtain ⟨d, qs, hsM, hrM, hinvM, hsettM, hLM, -, -, hkM, -, -, -⟩ := hm'
    have hg := hm.g_eq
    have hi2' : i < (G.L.g st0.mem).hi G.u := by rw [hg]; exact hi2
    obtain ⟨hjM, -, -⟩ := DL.arc_data hsM hu hi2'
    have hh := hsM.heads i hjM
    have hLt : G.d.L < G.L.INF := hLM ▸ hinvM.L_lt
    have hrs := hs.rs_lt
    have hst := relax_regs hI
    wram_enter
    · subst hpre
      rw [hst]
      dsimp only [relaxBody]
      have hA : G.L.A ≤ G.L.J * G.L.A := Nat.le_mul_of_pos_left _ hrM.pq.J_pos
      have hJw : G.L.J < 2 ^ w := by
        have : G.L.J ≤ G.L.INF * G.L.J + G.L.J := Nat.le_add_left _ _
        omega
      have hregs : ∀ (R : ℕ → ℕ), (∀ r < 18, R r = (G.L.args G.u G.d.L ++ [i, (G.L.g mem0).hi G.u]).getD r 0) →
          (∀ r < 16, R r = (G.L.args G.u G.d.L).getD r 0) ∧ R 17 = (G.L.g mem0).hi G.u ∧ R 16 = i :=
        fun R hR' => ⟨fun r hr => by rw [hR' r (by omega)]; interval_cases r <;> rfl,
          hR' 17 (by norm_num), hR' 16 (by norm_num)⟩
      have hno := rinv_no hm hsu hu hi1 hi2
      have hyes := fun v M2 hok hlt hpost => rinv_yes (v := v) (M2 := M2) hm hsu hu hi1 hi2 hok hlt hpost
      have hpp := fun hok hlt => rinv_pushPre hm hu hi2 hbud hi1 hok hlt
      have hAw : G.L.A < 2 ^ w := A_lt_of_fits hrM.pq.J_pos hs.fits
      wram_run
      all_goals first
        | (simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
            imp_false, not_false_eq_true, implies_true, and_true]; omega)
        | (apply hpp <;> first | assumption |
            (unfold DL.tentOf; split_ifs <;> first | assumption | contradiction))
        | (intro v mem' pos' hpost
           refine ⟨relaxInv_next2 (fun r hr => by
              interval_cases r <;> simp [Function.update_apply, DL.args]) (hyes v mem' ‹_› ?_ hpost), ?_⟩
           · unfold DL.tentOf; split_ifs <;> first | assumption | contradiction
           · simp only [pqPushC, List.getD_cons_succ, List.getD_cons_zero]
             wram_cost)
        | (exact relaxInv_next2 (fun r hr => by
              interval_cases r <;> simp [Function.update_apply, DL.args])
            (hno (by
              rintro ⟨h1, h2⟩
              first | contradiction |
                (unfold DL.tentOf at h2; split_ifs at h2 <;> first | contradiction | omega))))
        | wram_cost
  intro st ω hst
  refine runs_start_le ?_
  subst hst
  dsimp only [relaxAll, DL.args]
  wram_step
  wram_step
  refine runs_seq_triple_le hloop ?_ (fun st' hst' => ?_)
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [startState]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      rfl
    · simp [hhi, startState]
    · simp [hlo, startState]
    · exact rinv_start hpre'
  · wram_step
    · exact rinv_end hst'.2.2.2
    · simp only [relaxCost, DL.args, List.getD_cons_succ, List.getD_cons_zero, Expr.size_reg,
        Expr.size_const, Expr.size_load, Expr.size_bin]
      rw [← hlo, ← hhi]
      have := relax_cost_le ((G.L.g mem0).hi G.u - (G.L.g mem0).lo G.u) (Nat.log 2 G.L.J)
      omega

end MinCostFlow.LowStretch
