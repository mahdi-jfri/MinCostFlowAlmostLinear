module

public import MinCostFlow.LowStretch.ProgDijStep

/-!
# The start of a run of Dijkstra

A run starts with the queue empty and every stamp below the stamp `rs` of the run. It writes the
cost `0` of the source with the stamp `rs`, and pushes `(0, s)` to list `0`. Then the memory holds
the first state of Dijkstra (`DL.init_rep`). This file also has the facts on the potential that
the loop of a run needs.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace DL

variable {L : DL}

/-- The lists after the first push. -/
def qs1 (s : ℕ) : ℕ → List (ℕ × ℕ) := Function.update (fun _ => []) 0 [(0, s)]

/-- The first state of Dijkstra. -/
def d0 (L : DL) (s : ℕ) : DS :=
  { tent := Function.update (fun _ => L.INF) s 0, sett := fun _ => False, Q := [(0, s)], L := 0 }

theorem pqAll_qs1 {J s : ℕ} (hJ : 1 ≤ J) : pqAll J (qs1 s) = [(0, s)] := by
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  unfold pqAll qs1
  rw [List.range_succ_eq_map, List.flatMap_cons, Function.update_self, List.flatMap_map]
  simp

/-- The memory after the two stores of the start. -/
def initMem (L : DL) (mem : ℕ → ℕ) (s : ℕ) : ℕ → ℕ :=
  Function.update (Function.update mem (L.TS + s) L.rs) (L.TS + L.NN + s) 0

/-- **The start.** -/
theorem init_rep {w : ℕ} {mem mem1 : ℕ → ℕ} {Nodes : Finset ℕ} {s : ℕ}
    (hs : L.Shape w mem Nodes) (hsN : s ∈ Nodes)
    (hS : ∀ v < L.NN, mem (L.TS + v) < L.rs ∧ mem (L.TS + 2 * L.NN + v) < L.rs)
    (hpq : PQRep mem1 L.D L.J L.A L.INF (qs1 s))
    (hM : ∀ a < L.D, mem1 a = initMem L mem s a) :
    L.Shape w mem1 Nodes ∧ L.Rep mem1 Nodes (L.d0 s) (qs1 s) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hs.lay
  have hsn : s < L.NN := ((hs.ok_iff s).mpr hsN).1
  have hTS : ∀ a < L.TS, mem1 a = mem a := fun a ha => by
    rw [hM a (by omega)]; unfold initMem
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine ⟨Shape.congr L hs hTS, hpq, fun v => ?_, fun v => ?_, (pqAll_qs1 hpq.J_pos).symm,
    fun c e he k _ _ => ?_⟩
  · unfold d0 tentOf
    simp only
    by_cases hvs : v = s
    · subst hvs
      rw [if_pos hsN, hM _ (by omega), hM _ (by omega), Function.update_self]
      unfold initMem
      rw [Function.update_of_ne (by omega), Function.update_self, if_pos rfl, Function.update_self]
    · rw [Function.update_of_ne hvs]
      split_ifs with hvN h1
      · have hvn := ((hs.ok_iff v).mpr hvN).1
        rw [hM _ (by omega)] at h1
        unfold initMem at h1
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at h1
        have := (hS v hvn).1
        omega
      · rfl
      · rfl
  · unfold d0
    simp only [false_iff, not_and]
    intro hvN h1
    have hvn := ((hs.ok_iff v).mpr hvN).1
    rw [hM _ (by omega)] at h1
    unfold initMem at h1
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)] at h1
    have := (hS v hvn).2
    omega
  · unfold qs1 at he
    unfold d0
    by_cases hc : c = 0
    · subst hc
      rw [Function.update_self, List.mem_singleton] at he
      subst he
      simp
    · rw [Function.update_of_ne hc] at he
      simp at he

theorem init_stamps {mem mem1 : ℕ → ℕ} {s : ℕ} (hl : L.TS + 5 * L.NN ≤ L.D)
    (hS : ∀ v < L.NN, mem (L.TS + v) < L.rs ∧ mem (L.TS + 2 * L.NN + v) < L.rs)
    (hM : ∀ a < L.D, mem1 a = initMem L mem s a) : L.Stamps mem1 := by
  intro v hv
  obtain ⟨a, b⟩ := hS v hv
  rw [hM _ (by omega), hM _ (by omega)]
  unfold initMem
  simp only [Function.update_apply]
  constructor <;> split_ifs <;> omega

open Classical in
/-- The potential depends only on the graph. -/
theorem pot_congr {mem mem' : ℕ → ℕ} (h : L.g mem' = L.g mem) (Nodes : Finset ℕ) (d : DS)
    (qs : ℕ → List (ℕ × ℕ)) : L.pot mem' Nodes d qs = L.pot mem Nodes d qs := by
  unfold pot
  simp only [deg_eq_of_g h]

/-- The arcs and vertices of the graph, read from the memory. -/
def nodeSum (L : DL) (mem : ℕ → ℕ) : ℕ :=
  ∑ v ∈ (Finset.range L.NN).filter (fun v => mem (L.OK + v) = L.os), (mem (L.HI + v) - mem (L.LO + v) + 1)

theorem nodeSum_eq {w : ℕ} {mem : ℕ → ℕ} {Nodes : Finset ℕ} (hs : L.Shape w mem Nodes) :
    L.nodeSum mem = ∑ u ∈ Nodes, (L.deg mem u + 1) := by
  unfold nodeSum
  refine Finset.sum_congr ?_ fun v hv => ?_
  · ext v
    rw [Finset.mem_filter, Finset.mem_range, ← hs.ok_iff]
    rfl
  · have hvn := ((hs.ok_iff v).mpr hv).1
    simp [deg, g, hvn]

open Classical in
theorem pot_d0 {w : ℕ} {mem : ℕ → ℕ} {Nodes : Finset ℕ} (hs : L.Shape w mem Nodes) (s : ℕ)
    (hJ : 1 ≤ L.J) :
    L.pot mem Nodes (L.d0 s) (qs1 s) =
      (100 * (Nat.log 2 L.J + 2) + 900) * L.nodeSum mem + (50 * (Nat.log 2 L.J + 2) + 600) := by
  unfold pot
  rw [pqAll_qs1 hJ, nodeSum_eq hs]
  simp [d0]

end DL

/-- Each step costs at least a pop. -/
theorem stCost_le_dijCost {L : DL} {R : ℕ} {mem : ℕ → ℕ} :
    stCost L.J ≤ dijCost (L.argsR R) mem := by
  simp only [DL.argsR, dijCost]
  split_ifs <;> omega

end MinCostFlow.LowStretch
