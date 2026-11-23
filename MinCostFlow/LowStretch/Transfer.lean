module

public import MinCostFlow.LowStretch.Params
public import MinCostFlow.LowStretch.Stretch5

/-!
# The tree in the weighted graph

A run from the first cluster gives a spanning tree of the weighted graph (`spanning`): its pairs
are `n - 1` different edges, and every vertex is joined to vertex `0` in the tree. Its stretch in
the graph is at most `4` times the stretch bound of the run (`stretch_le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open MinCostFlow.Cited

variable {G : WGraph}

/-- The hypotheses on the graph. -/
structure Allowed (G : WGraph) : Prop where
  valid : G.graph.IsValid
  loopless : G.graph.IsLoopless
  conn : G.IsConnected
  weight : ∀ e ∈ G.edges, 1 ≤ e.2.2

theorem Allowed.fit (h : Allowed G) : (par G.n G.m).Fit (pgOf G) :=
  LowStretch.fit h.valid h.loopless h.conn.1

/-- **A run gives a spanning tree.** -/
theorem spanning (h : Allowed G) {θ : ℕ} {T : List ℕ}
    (hc : (root (pgOf G) θ).Inv (pgOf G) (par G.n G.m))
    (hr : Run (pgOf G) (par G.n G.m) (root (pgOf G) θ) T) : G.IsSpanningTree T := by
  have hP := h.fit
  obtain ⟨hin, hnd, hlen⟩ := Run.tree hP.ok hP.B hr hc
  have hrad := Run.radius hP.ok hP.B hr hc
  have hcard : (root (pgOf G) θ).X.card = G.n := by simp [root, pgOf]
  refine ⟨hnd, fun j hj => by simpa [pgOf] using (hin j hj).1, by omega, fun u hu v hv => ?_⟩
  have hu' : u ∈ (root (pgOf G) θ).X := by simp [root, pgOf, hu]
  have hv' : v ∈ (root (pgOf G) θ).X := by simp [root, pgOf, hv]
  obtain ⟨ps, hps, -⟩ := ((hrad.1 u hu').symm.trans (hrad.1 v hv'))
  exact ⟨ps, toPG.walk_to hps⟩

/-- One edge: its stretch in the graph is at most `4` times `d_T / ω` in the pair graph. -/
theorem edge_stretch_le (h : Allowed G) {θ : ℕ} {T : List ℕ}
    (hc : (root (pgOf G) θ).Inv (pgOf G) (par G.n G.m))
    (hr : Run (pgOf G) (par G.n G.m) (root (pgOf G) θ) T) {j : ℕ} (hj : j < G.m) :
    (G.treeDist T (G.edges[j]'hj).1 (G.edges[j]'hj).2.1 : ℝ) / (G.edges[j]'hj).2.2 ≤
      4 * ((pgOf G).tdist T ((pgOf G).pu j) ((pgOf G).pv j) / (pgOf G).pω j) := by
  have hP := h.fit
  have hrad := Run.radius hP.ok hP.B hr hc
  have hjm : j < (pgOf G).m := by simpa [pgOf] using hj
  have hok := hP.ok j hjm
  have hjins : j ∈ (pgOf G).ins (root (pgOf G) θ).X := by
    refine PG.mem_ins.mpr ⟨hjm, ?_, ?_⟩
    · simpa [root, pgOf] using hok.1
    · simpa [root, pgOf] using hok.2.1
  obtain ⟨ps, hps, hl⟩ := tw_tdist (hrad.tw hjins)
  have hu : (pgOf G).pu j = (G.edges[j]'hj).1 := toPG.pu_eq hj
  have hv : (pgOf G).pv j = (G.edges[j]'hj).2.1 := toPG.pv_eq hj
  have hω : (pgOf G).pω j = 2 ^ (Nat.log 2 (G.edges[j]'hj).2.2 + pσ G.n) := toPG.pω_eq hj
  have hw : 1 ≤ (G.edges[j]'hj).2.2 := h.weight _ (List.getElem_mem _)
  have hσ : 1 ≤ pσ G.n := by unfold pσ; omega
  have hwalk : G.IsWalkIn T (G.edges[j]'hj).1 (G.edges[j]'hj).2.1 ps := by
    rw [← hu, ← hv]; exact toPG.walk_to hps
  have htd : G.treeDist T (G.edges[j]'hj).1 (G.edges[j]'hj).2.1 ≤ G.weightOf ps :=
    Nat.sInf_le ⟨ps, hwalk, rfl⟩
  have hwt := toPG.weight_le hps hσ
  have hpow : 2 ^ Nat.log 2 (G.edges[j]'hj).2.2 ≤ (G.edges[j]'hj).2.2 :=
    Nat.pow_log_le_self 2 (by omega)
  set td := G.treeDist T (G.edges[j]'hj).1 (G.edges[j]'hj).2.1
  set w := (G.edges[j]'hj).2.2
  set t := (pgOf G).tdist T ((pgOf G).pu j) ((pgOf G).pv j)
  have key : td * (pgOf G).pω j ≤ 4 * t * w := by
    rw [hω, pow_add]
    have h1 : td * (2 ^ Nat.log 2 w * 2 ^ pσ G.n) ≤ td * (w * 2 ^ pσ G.n) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
    have h2 : 2 ^ pσ G.n * td ≤ 4 * t := by
      have : 2 ^ pσ G.n * td ≤ 2 ^ pσ G.n * G.weightOf ps := Nat.mul_le_mul_left _ htd
      have : 4 * PG.wlen (toPG G (pσ G.n)).hl ps ≤ 4 * t := Nat.mul_le_mul_left _ hl
      unfold pgOf at hwt
      omega
    have e : td * (w * 2 ^ pσ G.n) = w * (2 ^ pσ G.n * td) := by ring
    have h3 : w * (2 ^ pσ G.n * td) ≤ w * (4 * t) := Nat.mul_le_mul_left _ h2
    have e2 : w * (4 * t) = 4 * t * w := by ring
    omega
  have hwr : (0 : ℝ) < w := by exact_mod_cast hw
  have hωr : (0 : ℝ) < (pgOf G).pω j := by exact_mod_cast hok.2.2.2.2
  rw [mul_div_assoc', div_le_div_iff₀ hwr hωr]
  exact_mod_cast key

/-- **The stretch in the graph** is at most `4` times the stretch bound of the run. -/
theorem stretch_le (h : Allowed G) {θ : ℕ} {T : List ℕ}
    (hc : (root (pgOf G) θ).Inv (pgOf G) (par G.n G.m))
    (hr : Run (pgOf G) (par G.n G.m) (root (pgOf G) θ) T) :
    G.totalStretch T ≤ 4 * Str (pgOf G) (par G.n G.m) (root (pgOf G) θ).X T := by
  have hP := h.fit
  have hins : (pgOf G).ins (root (pgOf G) θ).X = Finset.range G.m := by
    ext p
    simp only [PG.mem_ins, Finset.mem_range]
    constructor
    · rintro ⟨hp, -, -⟩; simpa [pgOf] using hp
    · intro hp
      have hjm : p < (pgOf G).m := by simpa [pgOf] using hp
      have hok := hP.ok p hjm
      exact ⟨hjm, by simpa [root, pgOf] using hok.1, by simpa [root, pgOf] using hok.2.1⟩
  unfold Str WGraph.totalStretch
  rw [hins, Finset.mul_sum]
  simp only [par, Nat.cast_one, one_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_le_sum fun j _ => ?_
  exact edge_stretch_le h hc hr j.2

end MinCostFlow.LowStretch
