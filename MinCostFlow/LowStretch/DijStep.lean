module

public import MinCostFlow.LowStretch.ProgRelax

/-!
# One step of Dijkstra: the memory facts

A step of Dijkstra pops a least entry `(k, x)` of the queue. If `x` is settled, or its tentative
cost is below `k`, the entry is stale and is dropped (`Rep.drop`). Otherwise `x` is settled with
key `k` (`Rep.settle`) and its arcs are relaxed. This file proves what the memory holds after
each part. It also defines the potential `pot` that pays for the steps: every vertex that is not
settled holds `O(log J)` for each of its arcs, and every entry of the queue holds `O(log J)` for
its pop.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem sum_range_update {J c : ℕ} (hc : c < J) (f g : ℕ → ℕ) (hfg : ∀ c' < J, c' ≠ c → f c' = g c') :
    (List.map f (List.range J)).sum + g c = (List.map g (List.range J)).sum + f c := by
  induction J with
  | zero => omega
  | succ J ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases hcJ : c = J
    · subst hcJ
      have : (List.map f (List.range c)) = (List.map g (List.range c)) :=
        List.map_congr_left fun a ha => hfg a (by simp at ha; omega) (by simp at ha; omega)
      rw [this]; omega
    · rw [hfg J (by omega) (Ne.symm hcJ)]
      have := ih (by omega) (fun c' hc' hne => hfg c' (by omega) hne)
      omega

/-- The length of all lists after list `c` is replaced. -/
theorem length_pqAll_update {J : ℕ} {qs : ℕ → List (ℕ × ℕ)} {c : ℕ} (hc : c < J)
    (l : List (ℕ × ℕ)) :
    (pqAll J (Function.update qs c l)).length + (qs c).length = (pqAll J qs).length + l.length := by
  unfold pqAll
  simp only [List.length_flatMap]
  have := sum_range_update hc (fun a => (Function.update qs c l a).length) (fun a => (qs a).length)
    (fun c' _ hne => by simp [Function.update_of_ne hne])
  simp only [Function.update_self] at this
  exact this

theorem mem_pqAll_pop {J : ℕ} {qs : ℕ → List (ℕ × ℕ)} {c : ℕ} (hc : c < J) {e : ℕ × ℕ}
    {rest : List (ℕ × ℕ)} (hq : qs c = e :: rest) {e' : ℕ × ℕ} :
    (e' ∈ pqAll J (Function.update qs c rest) → e' ∈ pqAll J qs) ∧
      (e' ∈ pqAll J qs → e' ≠ e → e' ∈ pqAll J (Function.update qs c rest)) := by
  simp only [mem_pqAll]
  constructor
  · rintro ⟨c', hc', he⟩
    by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self] at he
      exact ⟨c', hc', by rw [hq]; exact List.mem_cons_of_mem _ he⟩
    · rw [Function.update_of_ne hcc] at he; exact ⟨c', hc', he⟩
  · rintro ⟨c', hc', he⟩ hne
    by_cases hcc : c' = c
    · subst hcc
      rw [hq] at he
      rcases List.mem_cons.mp he with he | he
      · exact absurd he hne
      · exact ⟨c', hc', by rw [Function.update_self]; exact he⟩
    · exact ⟨c', hc', by rw [Function.update_of_ne hcc]; exact he⟩

namespace DL

variable {L : DL}

open Classical in
/-- The arcs of the settled vertices. -/
noncomputable def setSum (L : DL) (mem : ℕ → ℕ) (Nodes : Finset ℕ) (sett : ℕ → Prop) : ℕ :=
  ∑ u ∈ Nodes.filter sett, L.deg mem u

open Classical in
/-- The potential of a state of Dijkstra. -/
noncomputable def pot (L : DL) (mem : ℕ → ℕ) (Nodes : Finset ℕ) (d : DS)
    (qs : ℕ → List (ℕ × ℕ)) : ℕ :=
  (100 * (Nat.log 2 L.J + 2) + 900) * ∑ u ∈ Nodes.filter (fun u => ¬ d.sett u), (L.deg mem u + 1) +
    (50 * (Nat.log 2 L.J + 2) + 600) * (pqAll L.J qs).length

/-- After a pop, the memory holds the state with the entry removed from the queue. -/
theorem Rep.pop {w : ℕ} {mem mem1 : ℕ → ℕ} {Nodes : Finset ℕ} {d : DS}
    {qs : ℕ → List (ℕ × ℕ)} (hs : L.Shape w mem Nodes) (hr : L.Rep mem Nodes d qs) {c : ℕ}
    (hc : c < L.J) {e : ℕ × ℕ} {rest : List (ℕ × ℕ)} (hq : qs c = e :: rest)
    (hpq : PQRep mem1 L.D L.J L.A L.INF (Function.update qs c rest))
    (hfr : ∀ a < L.D, mem1 a = mem a) :
    L.Shape w mem1 Nodes ∧
      L.Rep mem1 Nodes { d with Q := pqAll L.J (Function.update qs c rest) }
        (Function.update qs c rest) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hTS : ∀ a < L.TS, mem1 a = mem a := fun a ha => hfr a (by omega)
  have hv : ∀ v ∈ Nodes, v < L.NN := fun v hv => ((hs.ok_iff v).mpr hv).1
  refine ⟨Shape.congr L hs hTS, hpq, fun v => ?_, fun v => ?_, rfl, fun c' e' he' k hk hck => ?_⟩
  · rw [hr.tent v]
    split_ifs with hvn
    · have := hv v hvn
      unfold tentOf
      rw [hfr _ (by omega), hfr _ (by omega)]
    · rfl
  · rw [hr.sett v]
    constructor
    · rintro ⟨hvn, he⟩
      have := hv v hvn
      exact ⟨hvn, by rw [hfr _ (by omega)]; exact he⟩
    · rintro ⟨hvn, he⟩
      have := hv v hvn
      exact ⟨hvn, by rw [← hfr _ (by omega)]; exact he⟩
  · have hk' := hs.heads k hk
    rw [hTS _ (by omega)] at hck
    rw [hTS _ (by omega)]
    by_cases hcc : c' = c
    · subst hcc
      rw [Function.update_self] at he'
      exact hr.mono c' e' (by rw [hq]; exact List.mem_cons_of_mem _ he') k hk hck
    · rw [Function.update_of_ne hcc] at he'
      exact hr.mono c' e' he' k hk hck

/-- The memory after the settled stamp of `x` is written. -/
theorem Rep.settle {w : ℕ} {mem : ℕ → ℕ} {Nodes : Finset ℕ} {d : DS}
    {qs : ℕ → List (ℕ × ℕ)} (hs : L.Shape w mem Nodes) (hr : L.Rep mem Nodes d qs) {x k : ℕ}
    (hx : x ∈ Nodes) (hk : d.L ≤ k) :
    L.Shape w (Function.update mem (L.TS + 2 * L.NN + x) L.rs) Nodes ∧
      L.Rep (Function.update mem (L.TS + 2 * L.NN + x) L.rs) Nodes
        { tent := d.tent, sett := fun u => d.sett u ∨ u = x, Q := d.Q, L := k } qs := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hv : ∀ v ∈ Nodes, v < L.NN := fun v hv => ((hs.ok_iff v).mpr hv).1
  have hxN := hv x hx
  have hTS : ∀ a < L.TS, Function.update mem (L.TS + 2 * L.NN + x) L.rs a = mem a :=
    fun a ha => Function.update_of_ne (by omega) _ _
  refine ⟨Shape.congr L hs hTS, PQRep.congr hr.pq fun a ha _ => Function.update_of_ne (by omega) _ _,
    fun v => ?_, fun v => ?_, hr.Q, fun c' e' he' kk hkk hck => ?_⟩
  · rw [hr.tent v]
    split_ifs with hvn
    · have := hv v hvn
      unfold tentOf
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rfl
  · simp only
    rw [hr.sett v]
    by_cases hvx : v = x
    · subst hvx; simp [hx]
    · rw [Function.update_of_ne (by omega)]; simp [hvx]
  · have hk' := hs.heads kk hkk
    rw [Function.update_of_ne (by omega)] at hck
    rw [Function.update_of_ne (by omega)]
    have := hr.mono c' e' he' kk hkk hck
    simp only
    omega

open Classical in
theorem setSum_insert {mem : ℕ → ℕ} {Nodes : Finset ℕ} {sett : ℕ → Prop} {x : ℕ} (hx : x ∈ Nodes)
    (hn : ¬ sett x) :
    L.setSum mem Nodes (fun u => sett u ∨ u = x) = L.setSum mem Nodes sett + L.deg mem x := by
  unfold setSum
  rw [Finset.sum_congr (s₂ := insert x (Nodes.filter sett)) ?_ (fun _ _ => rfl),
    Finset.sum_insert (by simp [hn]), Nat.add_comm]
  ext u; simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hu, h | rfl⟩
    · exact Or.inr ⟨hu, h⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨hu, h⟩)
    · exact ⟨hx, Or.inr rfl⟩
    · exact ⟨hu, Or.inl h⟩

open Classical in
theorem unsett_insert {mem : ℕ → ℕ} {Nodes : Finset ℕ} {sett : ℕ → Prop} {x : ℕ} (hx : x ∈ Nodes)
    (hn : ¬ sett x) :
    ∑ u ∈ Nodes.filter (fun u => ¬ (sett u ∨ u = x)), (L.deg mem u + 1) + (L.deg mem x + 1) =
      ∑ u ∈ Nodes.filter (fun u => ¬ sett u), (L.deg mem u + 1) := by
  rw [Finset.sum_congr (s₁ := Nodes.filter (fun u => ¬ sett u))
    (s₂ := insert x (Nodes.filter (fun u => ¬ (sett u ∨ u = x)))) ?_ (fun _ _ => rfl),
    Finset.sum_insert (by simp), Nat.add_comm]
  ext u; simp only [Finset.mem_filter, Finset.mem_insert, not_or]
  constructor
  · rintro ⟨hu, h⟩
    by_cases hux : u = x
    · exact Or.inl hux
    · exact Or.inr ⟨hu, h, hux⟩
  · rintro (rfl | ⟨hu, h, -⟩)
    · exact ⟨hx, hn⟩
    · exact ⟨hu, h⟩

theorem setSum_le {w : ℕ} {mem : ℕ → ℕ} {Nodes : Finset ℕ} (hs : L.Shape w mem Nodes)
    (sett : ℕ → Prop) : L.setSum mem Nodes sett + 1 ≤ L.A := by
  classical
  unfold setSum
  have := hs.budget
  have := Finset.sum_le_sum_of_subset (f := fun u => L.deg mem u) (Finset.filter_subset sett Nodes)
  omega

theorem deg_eq_of_g {mem mem' : ℕ → ℕ} (h : L.g mem' = L.g mem) (u : ℕ) :
    L.deg mem' u = L.deg mem u := by unfold deg; rw [h]

theorem setSum_congr {mem mem' : ℕ → ℕ} (h : L.g mem' = L.g mem) (Nodes : Finset ℕ)
    (sett : ℕ → Prop) : L.setSum mem' Nodes sett = L.setSum mem Nodes sett := by
  classical
  unfold setSum
  exact Finset.sum_congr rfl fun u _ => deg_eq_of_g h u

end DL

/-- The cost of a pop and its stale test. -/
def stCost (J : ℕ) : ℕ := 50 * (Nat.log 2 J + 2) + 400

/-- The cost of one step of Dijkstra, from the memory before it: a pop if the queue is empty or
the least entry is stale, and a pop and the relaxing of the arcs of the vertex
otherwise. -/
def dijCost : List ℕ → (ℕ → ℕ) → ℕ
  | [D, J, A, INF, LO, HI, _, _, _, _, _, TS, NN, rs, _], mem =>
    if INF ≤ mem (D + 4) / J then stCost J
    else if mem (TS + 2 * NN + mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1)) = rs ∨
        (if mem (TS + mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1)) = rs
          then mem (TS + NN + mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1))
          else INF) < mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))))
      then stCost J
    else stCost J + 100 + (mem (HI + mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1)) -
        mem (LO + mem (pqE D J A (mem (D + 4) % J) (mem (pqH D J (mem (D + 4) % J))) + 1)) + 1) *
        (50 * (Nat.log 2 J + 2) + 300)
  | _, _ => 0

/-- The potential pays for a settle step. -/
theorem pot_settle_le (b dg V n len' : ℕ) (hl : len' ≤ n + dg) :
    (100 * (b + 2) + 900) * V + (50 * (b + 2) + 600) * len' +
      (50 * (b + 2) + 400 + 100 + (dg + 1) * (50 * (b + 2) + 300)) ≤
    (100 * (b + 2) + 900) * (V + (dg + 1)) + (50 * (b + 2) + 600) * (n + 1) := by
  have : (50 * (b + 2) + 600) * len' ≤ (50 * (b + 2) + 600) * (n + dg) :=
    Nat.mul_le_mul_left _ hl
  nlinarith

/-- The potential pays for a drop step. -/
theorem pot_drop_le (b U n : ℕ) :
    (100 * (b + 2) + 900) * U + (50 * (b + 2) + 600) * n + (50 * (b + 2) + 400) ≤
    (100 * (b + 2) + 900) * U + (50 * (b + 2) + 600) * (n + 1) := by
  nlinarith

end MinCostFlow.LowStretch
