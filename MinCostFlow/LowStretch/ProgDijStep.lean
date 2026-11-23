module

public import MinCostFlow.LowStretch.DijStep

/-!
# One step of Dijkstra

`dijStep (L.argsR R)` pops a least entry `(k, x)` into the cells `R` and `R + 1`. It returns `0`
if the queue was empty, `1` if the entry was stale, and `2` if it settled `x` with key `k` and
relaxed the arcs of `x` (`dijStep_spec`). Its cost is `dijCost`, and the potential `DL.pot`
drops by at least this cost.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The arguments of `dijStep`. -/
def DL.argsR (L : DL) (R : ℕ) : List ℕ :=
  [L.D, L.J, L.A, L.INF, L.LO, L.HI, L.HD, L.CS, L.CL, L.OK, L.os, L.TS, L.NN, L.rs, R]

/-- `dijStep`. Procedure `bPop` is `pqPop` and `bRelax` is `relaxAll`. -/
def dijStep (bPop bRelax : ℕ) : Stmt :=
  .seq (.call 20 bPop [.reg 0, .reg 1, .reg 2, .reg 3, .reg 14])
  (.cond (.bin .eq (.reg 20) (.const 0)) (.ret (.const 0))
  (.seq (.assign 21 (.load (.reg 14)))
  (.seq (.assign 22 (.load (.bin .add (.reg 14) (.const 1))))
  (.seq (.assign 23 (.load (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 12))) (.reg 22))))
  (.cond (.bin .eq (.reg 23) (.reg 13)) (.ret (.const 1))
  (.seq (.assign 24 (.load (.bin .add (.reg 11) (.reg 22))))
  (.seq (.assign 25 (.load (.bin .add (.bin .add (.reg 11) (.reg 12)) (.reg 22))))
  (.seq (.cond (.bin .eq (.reg 24) (.reg 13)) .nop (.assign 25 (.reg 3)))
  (.cond (.bin .lt (.reg 25) (.reg 21)) (.ret (.const 1))
  (.seq (.store (.bin .add (.bin .add (.reg 11) (.bin .mul (.const 2) (.reg 12))) (.reg 22)) (.reg 13))
  (.seq (.call 26 bRelax [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8,
      .reg 9, .reg 10, .reg 11, .reg 12, .reg 13, .reg 22, .reg 21])
  (.ret (.const 2)))))))))))))

theorem dijStep_noRand (bPop bRelax : ℕ) : (dijStep bPop bRelax).NoRand := by
  simp [dijStep, Stmt.NoRand]

/-- The ghost values of `dijStep`. -/
structure StG where
  L : DL
  Nodes : Finset ℕ
  s : ℕ
  cur : ℕ
  pos : ℕ
  d : DS
  qs : ℕ → List (ℕ × ℕ)
  R : ℕ

/-- The cells that a step leaves alone. -/
def DL.KeepS (L : DL) (R a : ℕ) : Prop :=
  a < L.TS ∨ (L.TS + 5 * L.NN ≤ a ∧ a < L.D + 3) ∨ (L.D + pqSize L.J L.A ≤ a ∧ a ≠ R ∧ a ≠ R + 1)

/-- The precondition of `dijStep`. -/
def stepPre (w : ℕ) (G : StG) (args : List ℕ) (mem : ℕ → ℕ) : Prop :=
  args = G.L.argsR G.R ∧ G.L.D + pqSize G.L.J G.L.A ≤ G.R ∧ G.R + 2 < 2 ^ w ∧
    G.L.Shape w mem G.Nodes ∧ G.L.Rep mem G.Nodes G.d G.qs ∧
    (G.L.g mem).Inv G.s G.L.INF G.cur G.pos G.d ∧
    (G.d.sett G.cur → (G.L.g mem).hi G.cur ≤ G.pos) ∧
    (∀ c < G.L.J, mem (pqT G.L.D G.L.J c) ≤ G.L.setSum mem G.Nodes G.d.sett + 1) ∧
    (G.L.g mem).ParInv G.s G.L.INF G.d (G.L.par mem) (G.L.parc mem) ∧ G.L.TZ mem G.qs ∧
    G.L.Stamps mem

/-- The postcondition of `dijStep`. -/
def stepPost (w : ℕ) (G : StG) (args : List ℕ) (mem : ℕ → ℕ) (v : ℕ) (mem' : ℕ → ℕ) : Prop :=
  (v = 0 ∧ (∀ c, G.qs c = []) ∧ mem' = mem) ∨
  (v = 1 ∧ ∃ qs', G.L.Shape w mem' G.Nodes ∧
    G.L.Rep mem' G.Nodes { G.d with Q := pqAll G.L.J qs' } qs' ∧
    (G.L.g mem).Inv G.s G.L.INF G.cur G.pos { G.d with Q := pqAll G.L.J qs' } ∧
    (∀ c < G.L.J, mem' (pqT G.L.D G.L.J c) ≤ G.L.setSum mem G.Nodes G.d.sett + 1) ∧
    G.L.pot mem G.Nodes { G.d with Q := pqAll G.L.J qs' } qs' + dijCost args mem ≤
      G.L.pot mem G.Nodes G.d G.qs ∧
    (∀ a, G.L.KeepS G.R a → mem' a = mem a) ∧
    (G.L.g mem).ParInv G.s G.L.INF { G.d with Q := pqAll G.L.J qs' } (G.L.par mem') (G.L.parc mem') ∧
    G.L.TZ mem' qs' ∧ G.L.Stamps mem') ∨
  (v = 2 ∧ ∃ d' qs', ¬ G.d.sett (mem' (G.R + 1)) ∧
    (G.d.L ≤ mem' G.R ∧ ∀ e ∈ G.d.Q, mem' G.R ≤ e.1) ∧ d'.L = mem' G.R ∧
    d'.sett = (fun u => G.d.sett u ∨ u = mem' (G.R + 1)) ∧
    G.L.Shape w mem' G.Nodes ∧ G.L.Rep mem' G.Nodes d' qs' ∧
    (G.L.g mem).Inv G.s G.L.INF (mem' (G.R + 1)) ((G.L.g mem).hi (mem' (G.R + 1))) d' ∧
    (∀ c < G.L.J, mem' (pqT G.L.D G.L.J c) ≤ G.L.setSum mem G.Nodes d'.sett + 1) ∧
    G.L.pot mem G.Nodes d' qs' + dijCost args mem ≤ G.L.pot mem G.Nodes G.d G.qs ∧
    (∀ a, G.L.KeepS G.R a → mem' a = mem a) ∧
    (G.L.g mem).ParInv G.s G.L.INF d' (G.L.par mem') (G.L.parc mem') ∧ G.L.TZ mem' qs' ∧
    G.L.Stamps mem' ∧
    dijCost args mem = stCost G.L.J + 100 + (G.L.deg mem (mem' (G.R + 1)) + 1) *
      (50 * (Nat.log 2 G.L.J + 2) + 300))

/-- The contract of `dijStep`. -/
def dijStepC (w : ℕ) : Contract := ghostC (stepPre w) (stepPost w) dijCost

/-! ### The facts behind the three outcomes -/

section Facts

variable {w : ℕ} {G : StG} {mem mem1 : ℕ → ℕ} {c : ℕ} {rest : List (ℕ × ℕ)}

/-- What the popped entry is. -/
theorem popped (hs : G.L.Shape w mem G.Nodes) (hr : G.L.Rep mem G.Nodes G.d G.qs)
    (hinv : (G.L.g mem).Inv G.s G.L.INF G.cur G.pos G.d) (hc : c < G.L.J)
    (hq : G.qs c = (mem1 G.R, mem1 (G.R + 1)) :: rest) :
    mem1 G.R = mem (pqE G.L.D G.L.J G.L.A c (mem (pqH G.L.D G.L.J c))) ∧
    mem1 (G.R + 1) = mem (pqE G.L.D G.L.J G.L.A c (mem (pqH G.L.D G.L.J c)) + 1) ∧
    (mem1 G.R, mem1 (G.R + 1)) ∈ G.d.Q ∧ mem1 (G.R + 1) ∈ G.Nodes ∧ mem1 G.R < G.L.INF ∧
    G.d.L ≤ mem1 G.R ∧ G.d.tent (mem1 (G.R + 1)) ≤ mem1 G.R := by
  have hh := (hr.pq.head_eq hc hq).2.1
  simp only [Prod.mk.injEq] at hh
  have hmem : (mem1 G.R, mem1 (G.R + 1)) ∈ G.d.Q := by
    rw [hr.Q]; exact mem_pqAll.mpr ⟨c, hc, by rw [hq]; exact List.mem_cons_self⟩
  have hk := hinv.keys _ hmem
  simp only at hk
  refine ⟨hh.1, hh.2, hmem, ?_, hk.2.2, hk.1, hk.2.1⟩
  by_contra hn
  have := hr.tent (mem1 (G.R + 1))
  rw [if_neg hn] at this
  omega

/-- The root is below `INF` when a list is not empty. -/
theorem root_lt (hr : G.L.Rep mem G.Nodes G.d G.qs) (hq : G.qs c = (mem1 G.R, mem1 (G.R + 1)) :: rest) :
    mem (G.L.D + 4) / G.L.J < G.L.INF := by
  by_contra hn
  have := (hr.pq.root_spec.2 (by rw [show G.L.D + 3 + 1 = G.L.D + 4 from rfl]; omega)) c
  rw [hq] at this
  exact List.cons_ne_nil _ _ this

open Classical in
/-- The cost of the step, in terms of the popped entry. -/
theorem dijCost_eq (hs : G.L.Shape w mem G.Nodes) (hr : G.L.Rep mem G.Nodes G.d G.qs)
    (hinv : (G.L.g mem).Inv G.s G.L.INF G.cur G.pos G.d) (hc : c < G.L.J)
    (hcr : c = mem (G.L.D + 4) % G.L.J)
    (hq : G.qs c = (mem1 G.R, mem1 (G.R + 1)) :: rest) :
    dijCost (G.L.argsR G.R) mem =
      if G.d.sett (mem1 (G.R + 1)) ∨ G.d.tent (mem1 (G.R + 1)) < mem1 G.R then stCost G.L.J
      else stCost G.L.J + 100 + (G.L.deg mem (mem1 (G.R + 1)) + 1) *
        (50 * (Nat.log 2 G.L.J + 2) + 300) := by
  obtain ⟨hk, hx, -, hxN, -, -, -⟩ := popped hs hr hinv hc hq
  have hroot := root_lt hr hq
  have hxn : mem1 (G.R + 1) < G.L.NN := ((hs.ok_iff _).mpr hxN).1
  simp only [dijCost, DL.argsR]
  rw [if_neg (by omega), ← hcr, ← hk, ← hx]
  have hsett : (mem (G.L.TS + 2 * G.L.NN + mem1 (G.R + 1)) = G.L.rs) ↔ G.d.sett (mem1 (G.R + 1)) := by
    rw [hr.sett]; exact ⟨fun h => ⟨hxN, h⟩, fun h => h.2⟩
  have htent : (if mem (G.L.TS + mem1 (G.R + 1)) = G.L.rs then mem (G.L.TS + G.L.NN + mem1 (G.R + 1))
      else G.L.INF) = G.d.tent (mem1 (G.R + 1)) := by
    rw [hr.tent, if_pos hxN]; rfl
  have hdeg : mem (G.L.HI + mem1 (G.R + 1)) - mem (G.L.LO + mem1 (G.R + 1)) =
      G.L.deg mem (mem1 (G.R + 1)) := by simp [DL.deg, DL.g, hxn]
  rw [htent, hdeg]
  by_cases h : G.d.sett (mem1 (G.R + 1)) ∨ G.d.tent (mem1 (G.R + 1)) < mem1 G.R
  · rw [if_pos h, if_pos]
    rcases h with h | h
    · exact Or.inl (hsett.mpr h)
    · exact Or.inr h
  · rw [if_neg h, if_neg]
    rintro (h' | h')
    · exact h (Or.inl (hsett.mp h'))
    · exact h (Or.inr h')

/-- The facts that a pop gives, in the form of `pqPopC`. -/
structure PopOut (G : StG) (mem mem1 : ℕ → ℕ) (c : ℕ) (rest : List (ℕ × ℕ)) : Prop where
  hc : c < G.L.J
  hcr : c = mem (G.L.D + 4) % G.L.J
  hq : G.qs c = (mem1 G.R, mem1 (G.R + 1)) :: rest
  hmin : ∀ e ∈ pqAll G.L.J G.qs, mem1 G.R ≤ e.1
  hpq : PQRep mem1 G.L.D G.L.J G.L.A G.L.INF (Function.update G.qs c rest)
  htails : ∀ c' < G.L.J, mem1 (pqT G.L.D G.L.J c') ≤ mem (pqT G.L.D G.L.J c')
  hz : rest = [] → mem1 (pqT G.L.D G.L.J c) = 0
  hfr : ∀ a, (a < G.L.D + 3 ∨ G.L.D + pqSize G.L.J G.L.A ≤ a) → a ≠ G.R → a ≠ G.R + 1 → mem1 a = mem a

theorem PopOut.frD {args : List ℕ} (hpre : stepPre w G args mem) (h : PopOut G mem mem1 c rest) :
    ∀ a < G.L.D, mem1 a = mem a := by
  obtain ⟨-, hR, -⟩ := hpre
  intro a ha
  exact h.hfr a (Or.inl (by omega)) (by unfold pqSize at hR; omega) (by unfold pqSize at hR; omega)

theorem len_pop (h : PopOut G mem mem1 c rest) :
    (pqAll G.L.J (Function.update G.qs c rest)).length + 1 = (pqAll G.L.J G.qs).length := by
  have := length_pqAll_update h.hc (qs := G.qs) rest
  rw [h.hq, List.length_cons] at this
  omega

open Classical in
/-- **A stale entry is dropped.** -/
theorem step_drop {args : List ℕ} (hpre : stepPre w G args mem) (h : PopOut G mem mem1 c rest)
    (hstale : G.d.sett (mem1 (G.R + 1)) ∨ G.d.tent (mem1 (G.R + 1)) < mem1 G.R) :
    stepPost w G args mem 1 mem1 := by
  have hfrD := h.frD hpre
  obtain ⟨rfl, hR, hR2, hs, hr, hinv, hdone, hcap, hpar, hz, hS⟩ := hpre
  obtain ⟨hs1, hr1⟩ := DL.Rep.pop hs hr h.hc h.hq h.hpq hfrD
  have hdrop := hinv.drop (e := (mem1 G.R, mem1 (G.R + 1))) hstale
    (Q' := pqAll G.L.J (Function.update G.qs c rest))
    (fun e' he' => by rw [hr.Q]; exact (mem_pqAll_pop h.hc h.hq).1 he')
    (fun e' he' hne => (mem_pqAll_pop h.hc h.hq).2 (by rw [← hr.Q]; exact he') hne)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  refine Or.inr (Or.inl ⟨rfl, _, hs1, hr1, hdrop, fun c' hc' => (h.htails c' hc').trans (hcap c' hc'),
    ?_, fun a ha => ?_, ?_, ?_, ?_⟩)
  · rw [dijCost_eq hs hr hinv h.hc h.hcr h.hq, if_pos hstale]
    unfold DL.pot stCost
    rw [← len_pop h]
    exact pot_drop_le _ _ _
  · rcases ha with ha | ⟨ha1, ha2⟩ | ⟨ha1, ha2, ha3⟩
    · exact h.hfr a (Or.inl (by omega)) (by unfold pqSize at hR; omega) (by unfold pqSize at hR; omega)
    · exact h.hfr a (Or.inl ha2) (by unfold pqSize at hR; omega) (by unfold pqSize at hR; omega)
    · exact h.hfr a (Or.inr ha1) ha2 ha3
  · exact (G.L.parInv_frame hs hr hpar fun v hv => ⟨hfrD _ (by omega), hfrD _ (by omega)⟩).mono rfl
      fun _ h => h
  · exact hz.pop h.htails h.hz
  · exact hS.congr l7 hfrD

/-- The state after a settle, before the arcs are relaxed. -/
def settled (d : DS) (Q : List (ℕ × ℕ)) (x k : ℕ) : DS :=
  { tent := d.tent, sett := fun u => d.sett u ∨ u = x, Q := Q, L := k }

/-- The ghost values for the call of `relaxAll` after a settle. -/
noncomputable def relaxG (G : StG) (mem mem1 : ℕ → ℕ) (c : ℕ) (rest : List (ℕ × ℕ)) : RlxG where
  L := G.L
  Nodes := G.Nodes
  s := G.s
  u := mem1 (G.R + 1)
  d := settled G.d (pqAll G.L.J (Function.update G.qs c rest)) (mem1 (G.R + 1)) (mem1 G.R)
  qs := Function.update G.qs c rest
  cnt := G.L.setSum mem G.Nodes G.d.sett + 1

/-- The memory after the settled stamp is written. -/
def settleMem (L : DL) (mem1 : ℕ → ℕ) (x : ℕ) : ℕ → ℕ :=
  Function.update mem1 (L.TS + 2 * L.NN + x) L.rs

/-- **A settle**: before the arcs are relaxed, the precondition of `relaxAll` holds. -/
theorem step_relaxPre {args : List ℕ} (hpre : stepPre w G args mem) (h : PopOut G mem mem1 c rest)
    (hfresh : ¬ (G.d.sett (mem1 (G.R + 1)) ∨ G.d.tent (mem1 (G.R + 1)) < mem1 G.R)) :
    relaxPre w (relaxG G mem mem1 c rest) (G.L.args (mem1 (G.R + 1)) (mem1 G.R))
      (settleMem G.L mem1 (mem1 (G.R + 1))) := by
  have hfrD := h.frD hpre
  obtain ⟨rfl, hR, hR2, hs, hr, hinv, hdone, hcap, hpar, hz, hS⟩ := hpre
  obtain ⟨hs1, hr1⟩ := DL.Rep.pop hs hr h.hc h.hq h.hpq hfrD
  obtain ⟨-, -, hmem, hxN, hkI, hLk, htk⟩ := popped hs hr hinv h.hc h.hq
  simp only [not_or, not_lt] at hfresh
  obtain ⟨hns, hge⟩ := hfresh
  obtain ⟨hs2, hr2⟩ := DL.Rep.settle hs1 hr1 hxN (k := mem1 G.R) hLk
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hxn : mem1 (G.R + 1) < G.L.NN := ((hs.ok_iff _).mpr hxN).1
  have hTS2 : ∀ a < G.L.TS, settleMem G.L mem1 (mem1 (G.R + 1)) a = mem a := fun a ha => by
    unfold settleMem; rw [Function.update_of_ne (by omega), hfrD a (by omega)]
  have hg : G.L.g (settleMem G.L mem1 (mem1 (G.R + 1))) = G.L.g mem := DL.g_congr G.L hs hTS2
  have hset := hinv.settle hdone hmem (fun e' he' => h.hmin e' (by rw [← hr.Q]; exact he')) hns
    (by simp only; omega) (Q' := pqAll G.L.J (Function.update G.qs c rest))
    (fun e' he' => by rw [hr.Q]; exact (mem_pqAll_pop h.hc h.hq).1 he')
    (fun e' he' hne => (mem_pqAll_pop h.hc h.hq).2 (by rw [← hr.Q]; exact he') hne)
  refine ⟨rfl, hs2, hr2, ?_, Or.inr rfl, hxN, fun c' hc' => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [relaxG]
    rw [hg]; exact hset
  · simp only [relaxG]
    have hpT : G.L.D ≤ pqT G.L.D G.L.J c' := by unfold pqT; omega
    unfold settleMem
    rw [Function.update_of_ne (by omega)]
    exact (h.htails c' hc').trans (hcap c' hc')
  · simp only [relaxG]
    have := DL.setSum_le hs (fun u => G.d.sett u ∨ u = mem1 (G.R + 1))
    rw [DL.deg_eq_of_g hg]
    rw [DL.setSum_insert hxN hns] at this
    omega
  · simp only [relaxG]
    rw [hg]
    refine (G.L.parInv_frame hs hr hpar fun v hv => ?_).mono rfl fun _ h => Or.inl h
    unfold settleMem
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hfrD _ (by omega),
      hfrD _ (by omega)]
    exact ⟨rfl, rfl⟩
  · simp only [relaxG]
    refine (hz.pop h.htails h.hz).congr fun a ha => ?_
    unfold settleMem
    rw [Function.update_of_ne (by omega)]
  · simp only [relaxG]
    intro v hv
    obtain ⟨a, b⟩ := hS v hv
    unfold settleMem
    simp only [Function.update_apply]
    rw [hfrD (G.L.TS + v) (by omega), hfrD (G.L.TS + 2 * G.L.NN + v) (by omega)]
    constructor <;> split_ifs <;> omega

open Classical in
/-- **A settle**: after the arcs are relaxed, the postcondition holds. -/
theorem step_settle {args : List ℕ} (hpre : stepPre w G args mem) (h : PopOut G mem mem1 c rest)
    (hfresh : ¬ (G.d.sett (mem1 (G.R + 1)) ∨ G.d.tent (mem1 (G.R + 1)) < mem1 G.R))
    {v : ℕ} {mem3 : ℕ → ℕ}
    (hpost : relaxPost w (relaxG G mem mem1 c rest) (G.L.args (mem1 (G.R + 1)) (mem1 G.R))
      (settleMem G.L mem1 (mem1 (G.R + 1))) v mem3) :
    stepPost w G args mem 2 mem3 := by
  have hpre' := hpre
  have hfrD := h.frD hpre
  have hrp := step_relaxPre hpre h hfresh
  obtain ⟨rfl, hR, hR2, hs, hr, hinv, hdone, hcap, hpar, hz, hS⟩ := hpre
  obtain ⟨-, -, hmem, hxN, hkI, hLk, htk⟩ := popped hs hr hinv h.hc h.hq
  obtain ⟨d', qs', hs3, hr3, hinv3, hsett3, hL3, htails3, hlen3, hk3, hp3, hz3, hS3⟩ := hpost
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hxn : mem1 (G.R + 1) < G.L.NN := ((hs.ok_iff _).mpr hxN).1
  have hTS2 : ∀ a < G.L.TS, settleMem G.L mem1 (mem1 (G.R + 1)) a = mem a := fun a ha => by
    unfold settleMem; rw [Function.update_of_ne (by omega), hfrD a (by omega)]
  have hg : G.L.g (settleMem G.L mem1 (mem1 (G.R + 1))) = G.L.g mem := DL.g_congr G.L hs hTS2
  simp only [relaxG, settled] at hinv3 hsett3 hL3 htails3 hlen3 hk3 hp3 hz3
  have hRk : ∀ a, G.L.D + pqSize G.L.J G.L.A ≤ a → mem3 a = mem1 a := by
    intro a ha
    rw [hk3 a (Or.inr (Or.inr (Or.inr ha)))]
    unfold settleMem
    rw [Function.update_of_ne (by unfold pqSize at ha; omega)]
  have e1 : mem3 (G.R + 1) = mem1 (G.R + 1) := hRk _ (by omega)
  have e0 : mem3 G.R = mem1 G.R := hRk _ hR
  simp only [not_or, not_lt] at hfresh
  obtain ⟨hns, hge⟩ := hfresh
  rw [hg] at hinv3 hp3
  refine Or.inr (Or.inr ⟨rfl, d', qs', by rw [e1]; exact hns,
    by rw [e0]; exact ⟨hLk, fun e he => h.hmin e (by rw [← hr.Q]; exact he)⟩,
    by rw [e0, hL3], by rw [e1, hsett3], hs3, hr3, by rw [e1]; exact hinv3, fun c' hc' => ?_, ?_,
    fun a ha => ?_, hp3, hz3, hS3, ?_⟩)
  · rw [hsett3, DL.setSum_insert hxN hns, ← DL.deg_eq_of_g hg]
    have := htails3 c' hc'
    omega
  · rw [dijCost_eq hs hr hinv h.hc h.hcr h.hq, if_neg (by simp only [not_or, not_lt]; exact ⟨hns, hge⟩)]
    have hUV : ∑ u ∈ G.Nodes.filter (fun u => ¬ d'.sett u), (G.L.deg mem u + 1) +
        (G.L.deg mem (mem1 (G.R + 1)) + 1) =
        ∑ u ∈ G.Nodes.filter (fun u => ¬ G.d.sett u), (G.L.deg mem u + 1) := by
      rw [hsett3]; convert DL.unsett_insert (L := G.L) (mem := mem) hxN hns
    rw [DL.deg_eq_of_g hg] at hlen3
    have hlp := len_pop h
    unfold DL.pot stCost
    rw [← hUV, ← hlp]
    exact pot_settle_le (Nat.log 2 G.L.J) (G.L.deg mem (mem1 (G.R + 1)))
      (∑ u ∈ G.Nodes.filter (fun u => ¬ d'.sett u), (G.L.deg mem u + 1))
      (pqAll G.L.J (Function.update G.qs c rest)).length (pqAll G.L.J qs').length hlen3
  · rcases ha with ha | ⟨ha1, ha2⟩ | ⟨ha1, ha2, ha3⟩
    · rw [hk3 a (Or.inl ha)]; exact hTS2 a ha
    · rw [hk3 a (Or.inr (Or.inr (Or.inl ⟨by omega, ha2⟩)))]
      unfold settleMem
      rw [Function.update_of_ne (by omega)]
      exact h.hfr a (Or.inl ha2) (by unfold pqSize at hR; omega) (by unfold pqSize at hR; omega)
    · rw [hRk a ha1]; exact h.hfr a (Or.inr ha1) ha2 ha3
  · rw [dijCost_eq hs hr hinv h.hc h.hcr h.hq, if_neg (by simp only [not_or, not_lt]; exact ⟨hns, hge⟩),
      e1]

end Facts

theorem dijCost_empty {L : DL} {R : ℕ} {mem : ℕ → ℕ} (h : L.INF ≤ mem (L.D + 4) / L.J) :
    dijCost [L.D, L.J, L.A, L.INF, L.LO, L.HI, L.HD, L.CS, L.CL, L.OK, L.os, L.TS, L.NN, L.rs, R] mem =
      stCost L.J := by
  simp only [dijCost, if_pos h]

theorem dijStep_spec {w : ℕ} {p : Program} {b bPop bRelax : ℕ} (hp : p.HasAt b [dijStep bPop bRelax])
    (hPop : MeetsContract w p bPop (pqPopC w)) (hRelax : MeetsContract w p bRelax (relaxAllC w)) :
    MeetsContract w p b (dijStepC w) := by
  have hproc : p.procs[b]? = some (dijStep bPop bRelax) := hp 0 (by simp)
  refine meets_of_ghost hproc ?_
  intro G args mem pos hwords hpre
  have hpre' := hpre
  obtain ⟨rfl, hR, hR2, hs, hr, hinv, hdone, hcap, hpar, hz, hS⟩ := hpre
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hfit := hs.fits
  obtain ⟨hf1, hf2, hf3⟩ := hfit
  have hD : G.L.D < 2 ^ w := by unfold pqSize at hf1; omega
  have hrs := hs.rs_lt
  have hJ1 := hr.pq.J_pos
  have hJw : G.L.J < 2 ^ w := by
    have : G.L.J ≤ G.L.INF * G.L.J + G.L.J := Nat.le_add_left _ _
    omega
  have hAw : G.L.A < 2 ^ w := A_lt_of_fits hJ1 hs.fits
  have hINFw : G.L.INF < 2 ^ w := by
    have : G.L.INF ≤ G.L.INF * G.L.J := Nat.le_mul_of_pos_right _ hJ1
    omega
  wram_enter
  · subst hpre
    dsimp only [dijStep, DL.argsR]
    wram_step
    · exact ⟨G.L.D, G.L.J, G.L.A, G.L.INF, G.qs, G.R, rfl, hr.pq, hs.fits, Or.inr hR, by omega⟩
    · intro v mem1 pos1 hpost
      rcases hpost _ _ _ _ _ _ rfl hr.pq with ⟨rfl, hall, hm1⟩ |
        ⟨rfl, c, hc, hcr, rest, hq, hmin, hpq, htails, hz1, hfr⟩
      · -- the queue is empty
        have hroot : G.L.INF ≤ mem (G.L.D + 4) / G.L.J := by
          by_contra hn
          obtain ⟨e, rest, he, -⟩ := hr.pq.root_spec.1 (by rw [show G.L.D + 3 + 1 = G.L.D + 4 from rfl]; omega)
          rw [hall] at he
          exact List.cons_ne_nil _ _ he.symm
        wram_run
        all_goals first
          | (exact Or.inl ⟨rfl, hall, hm1⟩)
          | (rw [dijCost_empty hroot]
             simp only [stCost, pqPopC, List.getD_cons_succ, List.getD_cons_zero]
             wram_cost)
      · have hpop : PopOut G mem mem1 c rest := ⟨hc, hcr, hq, hmin, hpq, htails, hz1, hfr⟩
        have hfrD := hpop.frD hpre'
        obtain ⟨hs1, hr1⟩ := DL.Rep.pop hs hr hc hq hpq hfrD
        obtain ⟨-, -, hmem, hxN, hkI, hLk, htk⟩ := popped hs hr hinv hc hq
        have hxn : mem1 (G.R + 1) < G.L.NN := ((hs.ok_iff _).mpr hxN).1
        have hcost := dijCost_eq hs hr hinv hc hcr hq
        have hsettI : mem1 (G.L.TS + 2 * G.L.NN + mem1 (G.R + 1)) = G.L.rs ↔ G.d.sett (mem1 (G.R + 1)) := by
          rw [hr1.sett]; exact ⟨fun h => ⟨hxN, h⟩, fun h => h.2⟩
        have htentI : G.d.tent (mem1 (G.R + 1)) = G.L.tentOf mem1 (mem1 (G.R + 1)) := by
          rw [hr1.tent, if_pos hxN]
        have hcost' : dijCost [G.L.D, G.L.J, G.L.A, G.L.INF, G.L.LO, G.L.HI, G.L.HD, G.L.CS, G.L.CL,
            G.L.OK, G.L.os, G.L.TS, G.L.NN, G.L.rs, G.R] mem = _ := hcost
        have hdeg : G.L.deg mem (mem1 (G.R + 1)) =
            mem (G.L.HI + mem1 (G.R + 1)) - mem (G.L.LO + mem1 (G.R + 1)) := by
          simp [DL.deg, DL.g, hxn]
        have hHI : Function.update mem1 (G.L.TS + 2 * G.L.NN + mem1 (G.R + 1)) G.L.rs
            (G.L.HI + mem1 (G.R + 1)) = mem (G.L.HI + mem1 (G.R + 1)) := by
          rw [Function.update_of_ne (by omega), hfrD _ (by omega)]
        have hLO : Function.update mem1 (G.L.TS + 2 * G.L.NN + mem1 (G.R + 1)) G.L.rs
            (G.L.LO + mem1 (G.R + 1)) = mem (G.L.LO + mem1 (G.R + 1)) := by
          rw [Function.update_of_ne (by omega), hfrD _ (by omega)]
        have hos := hs.os_lt
        have hfr2 : ∀ (hf : ¬ (G.d.sett (mem1 (G.R + 1)) ∨ G.d.tent (mem1 (G.R + 1)) < mem1 G.R)),
            (relaxAllC w).pre (G.L.args (mem1 (G.R + 1)) (mem1 G.R)) (settleMem G.L mem1 (mem1 (G.R + 1))) :=
          fun hf => ⟨relaxG G mem mem1 c rest, step_relaxPre hpre' hpop hf⟩
        wram_run
        all_goals first
          | (exact step_drop hpre' hpop (Or.inl (hsettI.mp ‹_›)))
          | (exact step_drop hpre' hpop (Or.inr (by
              rw [htentI]; unfold DL.tentOf; rw [if_pos ‹_›]; assumption)))
          | (rw [hcost', if_pos (Or.inl (hsettI.mp ‹_›))]
             simp only [stCost, pqPopC, List.getD_cons_succ, List.getD_cons_zero]
             wram_cost)
          | (rw [hcost', if_pos (Or.inr (by
              rw [htentI]; unfold DL.tentOf; rw [if_pos ‹_›]; assumption))]
             simp only [stCost, pqPopC, List.getD_cons_succ, List.getD_cons_zero]
             wram_cost)
          | (simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
              imp_false, not_false_eq_true, implies_true, and_true]; omega)
          | (exact hfr2 (by
              rintro (h1 | h1)
              · exact ‹¬ mem1 (G.L.TS + 2 * G.L.NN + mem1 (G.R + 1)) = G.L.rs› (hsettI.mpr h1)
              · rw [htentI] at h1; unfold DL.tentOf at h1; split_ifs at h1 <;> omega))
          | (intro v3 mem3 pos3 hpost3
             have hf : ¬ (G.d.sett (mem1 (G.R + 1)) ∨ G.d.tent (mem1 (G.R + 1)) < mem1 G.R) := by
               rintro (h1 | h1)
               · exact ‹¬ mem1 (G.L.TS + 2 * G.L.NN + mem1 (G.R + 1)) = G.L.rs› (hsettI.mpr h1)
               · rw [htentI] at h1; unfold DL.tentOf at h1; split_ifs at h1 <;> omega
             have h3 := hpost3 (relaxG G mem mem1 c rest) (step_relaxPre hpre' hpop hf)
             wram_run
             · exact step_settle hpre' hpop hf h3
             · rw [hcost', if_neg hf, hdeg]
               simp only [stCost, pqPopC, relaxAllC, ghostC, relaxCost, List.getD_cons_succ,
                 List.getD_cons_zero]
               rw [hHI, hLO]
               wram_cost)

end MinCostFlow.LowStretch
