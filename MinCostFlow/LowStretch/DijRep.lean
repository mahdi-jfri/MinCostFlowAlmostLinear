module

public import MinCostFlow.LowStretch.ProgPQPop
public import MinCostFlow.LowStretch.DijAbs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Dijkstra in memory

This file ties the abstract state of `MinCostFlow/LowStretch/DijAbs.lean` to the memory of the
program. A run of Dijkstra works on a graph whose vertices are the members of a finite set
`Nodes`, all below `NN`, and whose arcs are numbered below `MM`. The layout (`DL`) fixes where
everything is:
* the arcs of `u` are those from `mem (LO + u)` to `mem (HI + u)`; arc `k` goes to
  `mem (HD + k)`, costs `mem (CS + k)` and has class `mem (CL + k)`;
* `v` is a vertex when `mem (OK + v) = os`;
* five arrays of length `NN` start at `TS`: a stamp, a tentative cost, a settled stamp, a parent
  and a parent arc. A vertex has a tentative cost only when its stamp is the stamp `rs` of the
  run, and it is settled when its settled stamp is `rs`. So a new run needs no clearing: it takes
  a new stamp;
* the class queues are at `D` (`PQRep`).
All arrays that are only read lie below `TS`, and the program writes only at `TS` and above.

Arcs of the same class have the same cost. So, since the keys of settled vertices only grow, the
list of each class stays sorted (`Rep.mono`).

We also prove `meets_of_ghost`: to show a contract whose postcondition holds for every ghost
value that meets the precondition, it is enough to run the procedure once for each such value,
because runs are deterministic.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- A contract whose precondition holds for some ghost value `a`, and whose postcondition must
hold for every ghost value that meets the precondition. -/
def ghostC {α : Type} (pre : α → List ℕ → (ℕ → ℕ) → Prop)
    (post : α → List ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop) (cost : List ℕ → (ℕ → ℕ) → ℕ) :
    Contract where
  pre args mem := ∃ a, pre a args mem
  post args mem v mem' := ∀ a, pre a args mem → post a args mem v mem'
  cost := cost

/-- **One run for each ghost value is enough**, since runs are deterministic. -/
theorem meets_of_ghost {α : Type} {w : ℕ} {p : Program} {f : ℕ} {body : Stmt}
    {pre : α → List ℕ → (ℕ → ℕ) → Prop} {post : α → List ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop}
    {cost : List ℕ → (ℕ → ℕ) → ℕ} (hproc : p.procs[f]? = some body)
    (h : ∀ a args mem pos, (∀ x ∈ args, x < 2 ^ w) → pre a args mem →
      Triple w p (fun st => st = startState args mem pos) body
        (fun o st' => post a args mem o.value st'.mem) (fun _ => cost args mem)) :
    MeetsContract w p f (ghostC pre post cost) := by
  intro args mem pos ω hwords hpre
  obtain ⟨a0, ha0⟩ := hpre
  obtain ⟨o, st', c, hrun, -, hc⟩ := h a0 args mem pos hwords ha0 _ ω rfl
  refine ⟨body, hproc, o, st', c, hrun, fun a ha => ?_, hc⟩
  obtain ⟨o2, st2, c2, hrun2, hpost2, -⟩ := h a args mem pos hwords ha _ ω rfl
  obtain ⟨rfl, rfl, -⟩ := Runs.det hrun hrun2
  exact hpost2

/-- The layout of a run of Dijkstra. -/
structure DL where
  D : ℕ
  J : ℕ
  A : ℕ
  INF : ℕ
  LO : ℕ
  HI : ℕ
  HD : ℕ
  CS : ℕ
  CL : ℕ
  OK : ℕ
  os : ℕ
  TS : ℕ
  NN : ℕ
  rs : ℕ
  MM : ℕ

namespace DL

variable (L : DL)

/-- The graph that the memory holds. -/
def g (mem : ℕ → ℕ) : AG where
  lo u := if u < L.NN then mem (L.LO + u) else 0
  hi u := if u < L.NN then mem (L.HI + u) else 0
  hd k := if k < L.MM then mem (L.HD + k) else 0
  cs k := if k < L.MM then mem (L.CS + k) else 0
  ok v := v < L.NN ∧ mem (L.OK + v) = L.os

/-- The class of an arc. -/
def cl (mem : ℕ → ℕ) (k : ℕ) : ℕ := if k < L.MM then mem (L.CL + k) else 0

/-- The tentative cost in memory. -/
def tentOf (mem : ℕ → ℕ) (v : ℕ) : ℕ :=
  if mem (L.TS + v) = L.rs then mem (L.TS + L.NN + v) else L.INF

/-- The parent in memory. -/
def par (mem : ℕ → ℕ) (v : ℕ) : ℕ := mem (L.TS + 3 * L.NN + v)

/-- The parent arc in memory. -/
def parc (mem : ℕ → ℕ) (v : ℕ) : ℕ := mem (L.TS + 4 * L.NN + v)

/-- The number of arcs of `u`. -/
def deg (mem : ℕ → ℕ) (u : ℕ) : ℕ := (L.g mem).hi u - (L.g mem).lo u

/-- The facts about the graph and the layout that do not change during a run. -/
structure Shape (w : ℕ) (mem : ℕ → ℕ) (Nodes : Finset ℕ) : Prop where
  ok_iff : ∀ v, (L.g mem).ok v ↔ v ∈ Nodes
  arcs : ∀ u ∈ Nodes, (L.g mem).lo u ≤ (L.g mem).hi u ∧ (L.g mem).hi u ≤ L.MM
  heads : ∀ k < L.MM, mem (L.HD + k) < L.NN ∧ mem (L.CL + k) < L.J ∧
    L.INF + mem (L.CS + k) < 2 ^ w
  classes : ∀ k < L.MM, ∀ k' < L.MM, mem (L.CL + k) = mem (L.CL + k') →
    mem (L.CS + k) = mem (L.CS + k')
  budget : ∑ u ∈ Nodes, L.deg mem u + 1 ≤ L.A
  lay : L.LO + L.NN ≤ L.TS ∧ L.HI + L.NN ≤ L.TS ∧ L.HD + L.MM ≤ L.TS ∧ L.CS + L.MM ≤ L.TS ∧
    L.CL + L.MM ≤ L.TS ∧ L.OK + L.NN ≤ L.TS ∧ L.TS + 5 * L.NN ≤ L.D
  fits : PQFits w L.D L.J L.A L.INF
  rs_lt : L.rs < 2 ^ w
  os_lt : L.os < 2 ^ w
  INF_pos : 0 < L.INF

/-- The memory holds the state `d` of a run from `s`, with the lists `qs` of the class queues. -/
structure Rep (mem : ℕ → ℕ) (Nodes : Finset ℕ) (d : DS) (qs : ℕ → List (ℕ × ℕ)) : Prop where
  pq : PQRep mem L.D L.J L.A L.INF qs
  tent : ∀ v, d.tent v = if v ∈ Nodes then L.tentOf mem v else L.INF
  sett : ∀ v, d.sett v ↔ v ∈ Nodes ∧ mem (L.TS + 2 * L.NN + v) = L.rs
  Q : d.Q = pqAll L.J qs
  mono : ∀ c, ∀ e ∈ qs c, ∀ k < L.MM, mem (L.CL + k) = c → e.1 ≤ d.L + mem (L.CS + k)

/-- The graph depends only on the memory below `TS`. -/
theorem g_congr {mem mem' : ℕ → ℕ} {w : ℕ} {Nodes : Finset ℕ} (hs : L.Shape w mem Nodes)
    (h : ∀ a < L.TS, mem' a = mem a) : L.g mem' = L.g mem := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hs.lay
  unfold g
  congr 1
  · funext u; split_ifs with hu
    · exact h _ (by omega)
    · rfl
  · funext u; split_ifs with hu
    · exact h _ (by omega)
    · rfl
  · funext k; split_ifs with hk
    · exact h _ (by omega)
    · rfl
  · funext k; split_ifs with hk
    · exact h _ (by omega)
    · rfl
  · funext v; apply propext; constructor
    · rintro ⟨hv, he⟩; exact ⟨hv, by rw [← h _ (by omega)]; exact he⟩
    · rintro ⟨hv, he⟩; exact ⟨hv, by rw [h _ (by omega)]; exact he⟩

/-- The shape depends only on the memory below `TS`. -/
theorem Shape.congr {mem mem' : ℕ → ℕ} {w : ℕ} {Nodes : Finset ℕ} (hs : L.Shape w mem Nodes)
    (h : ∀ a < L.TS, mem' a = mem a) : L.Shape w mem' Nodes := by
  have hg := L.g_congr hs h
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hs.lay
  have hdeg : ∀ u, L.deg mem' u = L.deg mem u := fun u => by unfold deg; rw [hg]
  refine ⟨by rw [hg]; exact hs.ok_iff, by rw [hg]; exact hs.arcs, fun k hk => ?_,
    fun k hk k' hk' he => ?_, by simp only [hdeg]; exact hs.budget, hs.lay, hs.fits, hs.rs_lt,
    hs.os_lt, hs.INF_pos⟩
  · rw [h _ (by omega), h _ (by omega), h _ (by omega)]; exact hs.heads k hk
  · rw [h _ (by omega), h _ (by omega)] at he ⊢; exact hs.classes k hk k' hk' he

theorem PQRep.congr {mem mem' : ℕ → ℕ} {D J A INF : ℕ} {qs : ℕ → List (ℕ × ℕ)}
    (hp : PQRep mem D J A INF qs) (h : ∀ a, D ≤ a → a < D + pqSize J A → mem' a = mem a) :
    PQRep mem' D J A INF qs := by
  have hJA : ∀ c' < J, c' * A + A ≤ J * A := fun c' hc' => by nlinarith
  have hsz : ∀ c' i, c' < J → i < A → pqE D J A c' i + 1 < D + pqSize J A := by
    intro c' i hc' hi
    have := hJA c' hc'
    have h2 : 2 * J * A = 2 * (J * A) := by ring
    unfold pqE pqSize; omega
  have hH : ∀ c < J, mem' (pqH D J c) = mem (pqH D J c) := fun c hc =>
    h _ (by unfold pqH; omega) (by unfold pqH pqSize; omega)
  have hT : ∀ c < J, mem' (pqT D J c) = mem (pqT D J c) := fun c hc =>
    h _ (by unfold pqT; omega) (by unfold pqT pqSize; omega)
  have hL : ∀ c < J, pqList mem' D J A c = pqList mem D J A c := fun c hc =>
    pqList_congr (hH c hc) (hT c hc) fun i _ hi => by
      have hb := hp.bounds c hc
      have := hsz c i hc (by omega)
      exact ⟨h _ (by unfold pqE; omega) (by omega), h _ (by unfold pqE; omega) this⟩
  refine ⟨by rw [h D le_rfl (by unfold pqSize; omega)]; exact hp.hJ,
    by rw [h _ (by omega) (by unfold pqSize; omega)]; exact hp.hA,
    by rw [h _ (by omega) (by unfold pqSize; omega)]; exact hp.hINF, hp.J_pos,
    fun c hc => by rw [hH c hc, hT c hc]; exact hp.bounds c hc,
    fun c hc => by rw [hL c hc]; exact hp.list c hc, hp.none, hp.sorted, hp.lt,
    hp.tt.congr fun a h1 h2 => h _ (by omega) (by unfold pqSize; omega),
    fun c hc => by rw [h _ (by omega) (by unfold pqSize; omega)]; exact hp.leaf c hc⟩

/-- Nothing above the class queues matters for a run. -/
theorem Rep.congr {mem mem' : ℕ → ℕ} {w : ℕ} {Nodes : Finset ℕ} {d : DS}
    {qs : ℕ → List (ℕ × ℕ)} (hs : L.Shape w mem Nodes) (hr : L.Rep mem Nodes d qs)
    (h : ∀ a < L.D + pqSize L.J L.A, mem' a = mem a) : L.Rep mem' Nodes d qs := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hs.lay
  have hv : ∀ v ∈ Nodes, v < L.NN := fun v hv => ((hs.ok_iff v).mpr hv).1
  refine ⟨PQRep.congr hr.pq fun a _ ha => h a ha, fun v => ?_, fun v => ?_, hr.Q,
    fun c e he k hk hc => ?_⟩
  · rw [hr.tent v]
    split_ifs with hvn
    · have := hv v hvn
      unfold tentOf
      rw [h _ (by unfold pqSize; omega), h _ (by unfold pqSize; omega)]
    · rfl
  · rw [hr.sett v]
    constructor
    · rintro ⟨hvn, he⟩
      have := hv v hvn
      exact ⟨hvn, by rw [h _ (by unfold pqSize; omega)]; exact he⟩
    · rintro ⟨hvn, he⟩
      have := hv v hvn
      exact ⟨hvn, by rw [← h _ (by unfold pqSize; omega)]; exact he⟩
  · have hk' := (hs.heads k hk)
    rw [h _ (by unfold pqSize; omega)] at hc
    rw [h _ (by unfold pqSize; omega)]
    exact hr.mono c e he k hk hc

/-! ### Relaxing one arc -/

/-- The state after a relax step that improves the cost of `h` to `k`. -/
def _root_.MinCostFlow.LowStretch.DS.relaxed (d : DS) (h k : ℕ) (Q : List (ℕ × ℕ)) : DS :=
  { d with tent := Function.update d.tent h k, Q := Q }

theorem mem_pqAll_push {J : ℕ} {qs : ℕ → List (ℕ × ℕ)} {c : ℕ} (hc : c < J) {n e : ℕ × ℕ} :
    e ∈ pqAll J (Function.update qs c (qs c ++ [n])) ↔ e ∈ pqAll J qs ∨ e = n := by
  simp only [mem_pqAll]
  constructor
  · rintro ⟨c', hc', he⟩
    by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self, List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact Or.inl ⟨c', hc', he⟩
      · exact Or.inr he
    · rw [Function.update_of_ne hcc] at he; exact Or.inl ⟨c', hc', he⟩
  · rintro (⟨c', hc', he⟩ | rfl)
    · by_cases hcc : c' = c
      · subst hcc; exact ⟨c', hc', by rw [Function.update_self]; simp [he]⟩
      · exact ⟨c', hc', by rw [Function.update_of_ne hcc]; exact he⟩
    · exact ⟨c, hc, by rw [Function.update_self]; simp⟩

theorem length_pqAll_push {J : ℕ} {qs : ℕ → List (ℕ × ℕ)} {c : ℕ} (hc : c < J) {n : ℕ × ℕ} :
    (pqAll J (Function.update qs c (qs c ++ [n]))).length = (pqAll J qs).length + 1 := by
  unfold pqAll
  simp only [List.length_flatMap]
  induction J with
  | zero => omega
  | succ J ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases hcJ : c = J
    · subst hcJ
      rw [Function.update_self, List.length_append, List.length_singleton]
      have : (List.map (fun a => (Function.update qs c (qs c ++ [n]) a).length) (List.range c)) =
          List.map (fun a => (qs a).length) (List.range c) := by
        refine List.map_congr_left fun a ha => ?_
        rw [Function.update_of_ne (by simp at ha; omega)]
      rw [this]; omega
    · rw [Function.update_of_ne (Ne.symm hcJ), ih (by omega)]; omega

variable {L}

/-- The arc data that a relax step reads. -/
theorem arc_data {w : ℕ} {mem : ℕ → ℕ} {Nodes : Finset ℕ} (hs : L.Shape w mem Nodes) {u j : ℕ}
    (hu : u ∈ Nodes) (hj : j < (L.g mem).hi u) :
    j < L.MM ∧ (L.g mem).hd j = mem (L.HD + j) ∧ (L.g mem).cs j = mem (L.CS + j) := by
  have := (hs.arcs u hu).2
  have hj' : j < L.MM := by omega
  exact ⟨hj', by simp [g, hj'], by simp [g, hj']⟩

/-- **Relax, the cost improves.** The program writes the new cost and its stamp, and pushes the
entry to the queue of the class of the arc. Then the memory holds the new state. -/
theorem Rep.relax_improve {w : ℕ} {mem M : ℕ → ℕ} {Nodes : Finset ℕ} {d : DS}
    {qs : ℕ → List (ℕ × ℕ)} {s u j : ℕ} (hs : L.Shape w mem Nodes) (hr : L.Rep mem Nodes d qs)
    (hi : (L.g mem).Inv s L.INF u j d) (hsu : d.sett u) (hu : u ∈ Nodes)
    (hj1 : (L.g mem).lo u ≤ j) (hj2 : j < (L.g mem).hi u)
    (hok : mem (L.HD + j) ∈ Nodes)
    (hlt : d.L + mem (L.CS + j) < L.tentOf mem (mem (L.HD + j)))
    (hpq : PQRep M L.D L.J L.A L.INF (Function.update qs (mem (L.CL + j))
      (qs (mem (L.CL + j)) ++ [(d.L + mem (L.CS + j), mem (L.HD + j))])))
    (hM : ∀ a < L.TS + 3 * L.NN, M a = Function.update (Function.update mem (L.TS + mem (L.HD + j)) L.rs)
      (L.TS + L.NN + mem (L.HD + j)) (d.L + mem (L.CS + j)) a) :
    L.Shape w M Nodes ∧
    L.Rep M Nodes (d.relaxed (mem (L.HD + j)) (d.L + mem (L.CS + j))
      (pqAll L.J (Function.update qs (mem (L.CL + j))
        (qs (mem (L.CL + j)) ++ [(d.L + mem (L.CS + j), mem (L.HD + j))]))))
      (Function.update qs (mem (L.CL + j))
        (qs (mem (L.CL + j)) ++ [(d.L + mem (L.CS + j), mem (L.HD + j))])) ∧
    (L.g mem).Inv s L.INF u (j + 1) (d.relaxed (mem (L.HD + j)) (d.L + mem (L.CS + j))
      (pqAll L.J (Function.update qs (mem (L.CL + j))
        (qs (mem (L.CL + j)) ++ [(d.L + mem (L.CS + j), mem (L.HD + j))])))) := by
  obtain ⟨hjM, hhd, hcs⟩ := arc_data hs hu hj2
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hh := hs.heads j hjM
  set h := mem (L.HD + j) with hh_def
  set nk := d.L + mem (L.CS + j) with hnk
  set c := mem (L.CL + j) with hc_def
  have hTS : ∀ a < L.TS, M a = mem a := by
    intro a ha
    rw [hM a (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hs' := Shape.congr L hs hTS
  refine ⟨hs', ⟨hpq, fun v => ?_, fun v => ?_, rfl, fun c' e he k hk hck => ?_⟩, ?_⟩
  · -- the tentative costs
    simp only [DS.relaxed]
    by_cases hv : v = h
    · subst hv
      rw [Function.update_self, if_pos hok]
      unfold tentOf
      rw [hM _ (by omega), hM _ (by omega), Function.update_of_ne (by omega), Function.update_self,
        Function.update_self]
      simp
    · rw [Function.update_of_ne hv, hr.tent v]
      split_ifs with hvn
      · have hvN := ((hs.ok_iff v).mpr hvn).1
        unfold tentOf
        rw [hM _ (by omega), hM _ (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]
      · rfl
  · simp only [DS.relaxed]
    rw [hr.sett v]
    constructor
    · rintro ⟨hvn, he⟩
      have := ((hs.ok_iff v).mpr hvn).1
      refine ⟨hvn, ?_⟩
      rw [hM _ (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact he
    · rintro ⟨hvn, he⟩
      have := ((hs.ok_iff v).mpr hvn).1
      refine ⟨hvn, ?_⟩
      rw [hM _ (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at he
      exact he
  · -- the lists stay sorted by class
    simp only [DS.relaxed]
    rw [hTS _ (by omega)] at hck
    rw [hTS _ (by omega)]
    by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hr.mono _ e he k hk hck
      · simp only
        rw [hs.classes k hk j hjM hck]
    · rw [Function.update_of_ne hcc] at he
      exact hr.mono c' e he k hk hck
  · -- the invariant of Dijkstra
    have hcL := hi.cur_L hsu
    have hok' : (L.g mem).ok h := (hs.ok_iff h).mpr hok
    have htn : d.tent h = L.tentOf mem h := by rw [hr.tent h, if_pos hok]
    have key := (hi.relax hsu hj1 hj2).1 ⟨by rw [hhd]; exact hok', by rw [hhd, hcs, hcL, htn]; exact hlt⟩
      (pqAll L.J (Function.update qs c (qs c ++ [(nk, h)])))
      (fun e he => ?_) (fun e he => ?_) ?_
    · rw [hhd, hcs, hcL] at key; exact key
    · rw [mem_pqAll_push hh.2.1] at he
      rcases he with he | he
      · left; rw [hr.Q]; exact he
      · right; rw [he, hhd, hcs, hcL]
    · rw [mem_pqAll_push hh.2.1]; left; rw [← hr.Q]; exact he
    · rw [mem_pqAll_push hh.2.1, hhd, hcs, hcL]; right; rfl

/-- The checks before a push: the list has room, the key is below `INF`, and the key is at least
every key of its class. -/
theorem Rep.push_pre {w : ℕ} {mem : ℕ → ℕ} {Nodes : Finset ℕ} {d : DS}
    {qs : ℕ → List (ℕ × ℕ)} {s u j cnt : ℕ} (hs : L.Shape w mem Nodes) (hr : L.Rep mem Nodes d qs)
    (hi : (L.g mem).Inv s L.INF u j d) (hu : u ∈ Nodes) (hj2 : j < (L.g mem).hi u)
    (hok : mem (L.HD + j) ∈ Nodes)
    (hlt : d.L + mem (L.CS + j) < L.tentOf mem (mem (L.HD + j)))
    (hcap : ∀ c < L.J, mem (pqT L.D L.J c) ≤ cnt) (hcnt : cnt < L.A) :
    mem (pqT L.D L.J (mem (L.CL + j))) < L.A ∧ d.L + mem (L.CS + j) < L.INF ∧
      ∀ e ∈ qs (mem (L.CL + j)), e.1 ≤ d.L + mem (L.CS + j) := by
  obtain ⟨hjM, -, -⟩ := arc_data hs hu hj2
  have hh := hs.heads j hjM
  refine ⟨lt_of_le_of_lt (hcap _ hh.2.1) hcnt, ?_, fun e he => hr.mono _ e he j hjM rfl⟩
  have h1 := hi.tent_le (mem (L.HD + j))
  rw [hr.tent, if_pos hok] at h1
  omega

/-- The parents matter only at vertices with a cost. -/
theorem _root_.MinCostFlow.LowStretch.AG.ParInv.congr {g : AG} {s INF : ℕ} {d : DS}
    {par parc par' parc' : ℕ → ℕ} (h : g.ParInv s INF d par parc)
    (he : ∀ x, d.tent x < INF → par' x = par x ∧ parc' x = parc x) : g.ParInv s INF d par' parc' := by
  intro x hx hlt
  obtain ⟨e1, e2⟩ := he x hlt
  rw [e1, e2]
  exact h x hx hlt

/-- **Relax, the parents.** After an improving relax step that writes `u` and `j` as the parent
and the parent arc of the head, the parents in memory still meet `ParInv`. -/
theorem Rep.relax_par {w : ℕ} {mem M : ℕ → ℕ} {Nodes : Finset ℕ} {d : DS}
    {qs : ℕ → List (ℕ × ℕ)} {s u j : ℕ} (hs : L.Shape w mem Nodes) (hr : L.Rep mem Nodes d qs)
    (hp : (L.g mem).ParInv s L.INF d (L.par mem) (L.parc mem))
    (hi : (L.g mem).Inv s L.INF u j d) (hsu : d.sett u) (hu : u ∈ Nodes)
    (hj1 : (L.g mem).lo u ≤ j) (hj2 : j < (L.g mem).hi u)
    (hok : mem (L.HD + j) ∈ Nodes)
    (hlt : d.L + mem (L.CS + j) < L.tentOf mem (mem (L.HD + j))) (Q' : List (ℕ × ℕ))
    (hM : ∀ v < L.NN, M (L.TS + 3 * L.NN + v) = Function.update (L.par mem) (mem (L.HD + j)) u v ∧
      M (L.TS + 4 * L.NN + v) = Function.update (L.parc mem) (mem (L.HD + j)) j v) :
    (L.g mem).ParInv s L.INF (d.relaxed (mem (L.HD + j)) (d.L + mem (L.CS + j)) Q')
      (L.par M) (L.parc M) := by
  obtain ⟨hjM, hhd, hcs⟩ := arc_data hs hu hj2
  have hcL := hi.cur_L hsu
  have hok' : (L.g mem).ok (mem (L.HD + j)) := (hs.ok_iff _).mpr hok
  have htn : d.tent (mem (L.HD + j)) = L.tentOf mem (mem (L.HD + j)) := by
    rw [hr.tent, if_pos hok]
  have key := hp.relax hi hsu hj1 hj2 (by rw [hhd]; exact hok')
    (by rw [hhd, hcs, hcL, htn]; exact hlt) Q'
  rw [hhd, hcs, hcL] at key
  refine AG.ParInv.congr key fun x hx => ?_
  have hxN : x ∈ Nodes := by
    by_contra hn
    have := hr.tent x
    simp only [DS.relaxed] at hx
    by_cases hxh : x = mem (L.HD + j)
    · exact hn (hxh ▸ hok)
    · rw [Function.update_of_ne hxh, this, if_neg hn] at hx; omega
  have hxn := ((hs.ok_iff x).mpr hxN).1
  exact ⟨(hM x hxn).1, (hM x hxn).2⟩

/-! ### Empty lists sit at `0`

Each list that is empty has its last-plus-one position at `0`. So at the end of a run, when all
lists are empty, the next run starts with lists that have room for all its entries (`TZ`). -/

/-- Every empty list has its last-plus-one position at `0`. -/
def TZ (mem : ℕ → ℕ) (qs : ℕ → List (ℕ × ℕ)) : Prop :=
  ∀ c < L.J, qs c = [] → mem (pqT L.D L.J c) = 0

/-- `TZ` after a push to list `c`, which changes no other last-plus-one position. -/
theorem TZ.push {mem mem' : ℕ → ℕ} {qs : ℕ → List (ℕ × ℕ)} {c : ℕ} {e : ℕ × ℕ}
    (h : L.TZ mem qs) (ht : ∀ c' < L.J, c' ≠ c → mem' (pqT L.D L.J c') = mem (pqT L.D L.J c')) :
    L.TZ mem' (Function.update qs c (qs c ++ [e])) := by
  intro c' hc' hq
  by_cases hcc : c' = c
  · subst hcc
    rw [Function.update_self] at hq
    simp at hq
  · rw [Function.update_of_ne hcc] at hq
    rw [ht c' hc' hcc]
    exact h c' hc' hq

/-- `TZ` after a pop from list `c`: no position grows, and list `c` goes back to `0` if it
becomes empty. -/
theorem TZ.pop {mem mem' : ℕ → ℕ} {qs : ℕ → List (ℕ × ℕ)} {c : ℕ} {rest : List (ℕ × ℕ)}
    (h : L.TZ mem qs) (ht : ∀ c' < L.J, mem' (pqT L.D L.J c') ≤ mem (pqT L.D L.J c'))
    (hz : rest = [] → mem' (pqT L.D L.J c) = 0) :
    L.TZ mem' (Function.update qs c rest) := by
  intro c' hc' hq
  by_cases hcc : c' = c
  · subst hcc
    rw [Function.update_self] at hq
    exact hz hq
  · rw [Function.update_of_ne hcc] at hq
    have := ht c' hc'
    have := h c' hc' hq
    omega

theorem TZ.congr {mem mem' : ℕ → ℕ} {qs : ℕ → List (ℕ × ℕ)} (h : L.TZ mem qs)
    (ht : ∀ a, L.D ≤ a → mem' a = mem a) : L.TZ mem' qs := by
  intro c hc hq
  rw [ht _ (by unfold pqT; omega)]
  exact h c hc hq

/-- No stamp is above the stamp `rs` of the run. Then a later run can take a larger stamp, and
it sees no cost and no settled vertex at the start. -/
def Stamps (M : ℕ → ℕ) : Prop :=
  ∀ v < L.NN, M (L.TS + v) ≤ L.rs ∧ M (L.TS + 2 * L.NN + v) ≤ L.rs

theorem Stamps.congr {M M' : ℕ → ℕ} (h : L.Stamps M) (hl : L.TS + 5 * L.NN ≤ L.D)
    (h' : ∀ a < L.D, M' a = M a) : L.Stamps M' := by
  intro v hv
  rw [h' _ (by omega), h' _ (by omega)]
  exact h v hv

/-- The parents survive a change of memory that keeps the parent cells. -/
theorem parInv_frame {w : ℕ} {mem M M0 : ℕ → ℕ} {Nodes : Finset ℕ} {d : DS}
    {qs : ℕ → List (ℕ × ℕ)} {g : AG} {s : ℕ} (hs : L.Shape w mem Nodes) (hr : L.Rep mem Nodes d qs)
    (hp : g.ParInv s L.INF d (L.par M0) (L.parc M0))
    (hM : ∀ v < L.NN, M (L.TS + 3 * L.NN + v) = M0 (L.TS + 3 * L.NN + v) ∧
      M (L.TS + 4 * L.NN + v) = M0 (L.TS + 4 * L.NN + v)) :
    g.ParInv s L.INF d (L.par M) (L.parc M) := by
  refine AG.ParInv.congr hp fun x hx => ?_
  have hxN : x ∈ Nodes := by
    by_contra hn
    rw [hr.tent, if_neg hn] at hx
    omega
  exact hM x ((hs.ok_iff x).mpr hxN).1

end DL

end MinCostFlow.LowStretch
