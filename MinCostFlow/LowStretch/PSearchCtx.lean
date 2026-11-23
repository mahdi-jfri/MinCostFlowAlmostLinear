module

public import MinCostFlow.LowStretch.ProgPLoop
public import MinCostFlow.LowStretch.DijSub
public import MinCostFlow.LowStretch.PTestLink
public import MinCostFlow.LowStretch.PSumMem
public import MinCostFlow.LowStretch.PLink
public import MinCostFlow.LowStretch.PCand

/-!
# The setting of one petal search

A petal search runs `psLoop` on a fixed petal graph. This file fixes what does not change during
the search (`SC`), and what it must satisfy (`SC.Ok`).

The highway is the list `H` of nodes, from the source `H[0]`. Each node `v` has a last arc, its
*slot* `slot v`. In the full graph `gF` the slot of `H[i]` goes to `H[i+1]` (to the dummy node `S`
for the last one), and in the memory `mem0` at the start every slot of `H` goes to `S`, which is
not an allowed node. While the pointer is at `H[j]`, the slots of `H[0], …, H[j]` are on: the
graph is `gC j`. Every arc of `gC j` is an arc of `gF`, and they agree at the settled nodes
(`gC_sub`), so the invariant of Dijkstra moves from `gC j` to `gF`. On `gF` the settled costs are
the distances `δF` (`tent_eq`).

The highway costs `hc i` grow along `H` (`hc_lt`), and they are the distances to `H[i]` in `gF`.
A walk that costs less than `hc i` for every `i > j` never uses a slot that is off, so it is a
walk of `gC j` (`reach_gC`). This is why the highway nodes settle in their order.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The fixed values of one petal search. `X` gives the addresses (its state of Dijkstra is not
used), `mem0` is the memory at the start, `nA` entries with ends `ea`, `eb`, pairs `pr` and
weights `wtP ∘ pr`, and the cluster `c` with the set `Y`, the petal data `pd`, the map `sv` to
super-vertices, and the largest radius `Rm` that the graph represents. -/
structure SC where
  X : PSG
  mem0 : ℕ → ℕ
  H : List ℕ
  hc : ℕ → ℕ
  gF : AG
  nA : ℕ
  ea : ℕ → ℕ
  eb : ℕ → ℕ
  pr : ℕ → ℕ
  wtP : ℕ → ℕ
  Sm : ℕ
  G : PG
  P : Par
  c : Cl
  Y : Finset ℕ
  pd : PD
  sv : ℕ → ℕ
  Rm : ℕ

namespace SC

variable (C : SC)

/-- The layout of Dijkstra. -/
abbrev L : DL := C.X.G.L

/-- Node `i` of the highway. -/
def hv (i : ℕ) : ℕ := C.H.getD i 0

/-- The slot of node `v`: its last arc. -/
def slot (v : ℕ) : ℕ := C.mem0 (C.L.HI + v) - 1

/-- The head of the slot of `H[i]` when it is on. -/
def nx (i : ℕ) : ℕ := C.mem0 (C.X.NXT + C.hv i)

/-- Arc `k` is the slot of some `H[i]` with `i > j`: it is off while the pointer is at `H[j]`. -/
def IsSlot (j k : ℕ) : Prop := ∃ i, j < i ∧ i < C.H.length ∧ k = C.slot (C.hv i)

open Classical in
/-- The graph while the pointer is at `H[j]`. -/
noncomputable def gC (j : ℕ) : AG := { C.gF with hd := fun k => if C.IsSlot j k then C.X.S else C.gF.hd k }

/-- The distances in the full graph. -/
noncomputable def δF (v : ℕ) : ℕ := sInf {k | C.gF.Reach C.X.G.s v k}

/-- The allowed nodes. -/
def okN (y : ℕ) : Prop := (C.L.g C.mem0).ok y

/-- The cells that the search never writes. -/
def Fix (a : ℕ) : Prop :=
  C.L.KeepS C.X.G.R a ∧ a < C.X.CTL ∧ ∀ i < C.H.length, a ≠ C.L.HD + C.slot (C.hv i)

/-- What the fixed values must satisfy. -/
structure Ok (w : ℕ) : Prop where
  /-- The highway. -/
  Hnd : C.H.Nodup
  Hne : 0 < C.H.length
  H0 : C.hv 0 = C.X.G.s
  HS : ∀ i < C.H.length, C.hv i < C.X.S
  HN : ∀ i < C.H.length, C.hv i ∈ C.X.G.Nodes
  SN : C.X.S < C.L.NN
  Sok : ¬ C.okN C.X.S
  hnx : ∀ i < C.H.length, C.nx i = (C.H ++ [C.X.S]).getD (i + 1) 0
  lohi : ∀ v ∈ C.X.G.Nodes, C.mem0 (C.L.LO + v) < C.mem0 (C.L.HI + v)
  own : ∀ u k i, (C.L.g C.mem0).lo u ≤ k → k < (C.L.g C.mem0).hi u → i < C.H.length →
    k = C.slot (C.hv i) → u = C.hv i
  /-- The full graph. -/
  Flo : ∀ u, C.gF.lo u = (C.L.g C.mem0).lo u
  Fhi : ∀ u, C.gF.hi u = (C.L.g C.mem0).hi u
  Fcs : ∀ k, C.gF.cs k = (C.L.g C.mem0).cs k
  Fok : ∀ v, C.gF.ok v ↔ (C.L.g C.mem0).ok v
  Fhd : ∀ k, (∀ i < C.H.length, k ≠ C.slot (C.hv i)) → C.gF.hd k = (C.L.g C.mem0).hd k
  Fsl : ∀ i < C.H.length, C.gF.hd (C.slot (C.hv i)) = C.nx i
  hhc : ∀ i < C.H.length, C.gF.Reach C.X.G.s (C.hv i) (C.hc i) ∧
    ∀ k, C.gF.Reach C.X.G.s (C.hv i) k → C.hc i ≤ k
  hinc : ∀ i, i + 1 < C.H.length → C.hc i < C.hc (i + 1)
  /-- The cells that are read and never written. -/
  fLO : ∀ v < C.L.NN, C.Fix (C.L.LO + v) ∧ C.Fix (C.L.HI + v) ∧ C.Fix (C.L.OK + v) ∧
    C.Fix (C.X.NXT + v)
  fCS : ∀ k < C.L.MM, C.Fix (C.L.CS + k) ∧ C.Fix (C.L.CL + k) ∧ C.Fix (C.X.ORD + k)
  fHD : ∀ k < C.L.MM, (∀ i < C.H.length, k ≠ C.slot (C.hv i)) → C.Fix (C.L.HD + k)
  fAS : ∀ j < C.nA, C.Fix (C.X.AS + 2 * j) ∧ C.Fix (C.X.EXP + C.mem0 (C.X.AS + 2 * j))
  fSQ : ∀ q ≤ C.X.Lb + 1, C.Fix (C.X.SQ + q) ∧ C.Fix (C.X.P2 + q)
  /-- The cells that are written lie above Dijkstra. -/
  hR : C.L.D + pqSize C.L.J C.L.A ≤ C.X.G.R
  hCTL : C.X.G.R + 2 ≤ C.X.CTL
  hSUM : C.X.CTL + 4 ≤ C.X.SUM
  hSL : C.X.SUM + 5 ≤ C.X.SL
  wSL : C.X.SL + C.L.NN + 1 < 2 ^ w
  /-- The arcs of a node before its slot are the two directions of its entries. -/
  ordA : ∀ u ∈ C.X.G.Nodes, ∀ k, C.mem0 (C.L.LO + u) ≤ k → k < C.mem0 (C.L.HI + u) - 1 →
    C.mem0 (C.X.ORD + k) / 2 < C.nA
  hsum : ∀ u ∈ C.X.G.Nodes, ∀ Fs : ℕ → ℕ → ℕ,
    ∑ k ∈ Finset.Ico (C.mem0 (C.L.LO + u)) (C.mem0 (C.L.HI + u) - 1),
        Fs (C.mem0 (C.L.HD + k)) (C.mem0 (C.X.ORD + k) / 2) =
      ∑ j ∈ (Finset.range C.nA).filter (C.ea · = u), Fs (C.eb j) j +
      ∑ j ∈ (Finset.range C.nA).filter (C.eb · = u), Fs (C.ea j) j
  hwt : ∀ j < C.nA, 1 <<< (C.X.Es - C.mem0 (C.X.EXP + C.mem0 (C.X.AS + 2 * j))) = C.wtP (C.pr j)
  ends : ∀ j < C.nA, C.ea j < C.L.NN ∧ C.eb j < C.L.NN ∧ C.ea j ≠ C.eb j
  /-- Words. -/
  wU : (C.nA + C.L.MM + 1) * (2 ^ C.X.Es * C.L.INF + 2 ^ C.X.Es + 1) < 2 ^ w
  wE : ∀ j < C.nA, C.mem0 (C.X.EXP + C.mem0 (C.X.AS + 2 * j)) < 2 ^ w
  wR2 : C.X.G.R + 2 < 2 ^ w
  wb : C.X.lo + (C.X.Lb + 1) * C.X.bw + 2 < 2 ^ w
  wL : C.X.Lb + 2 < 2 ^ w
  wSm : C.Sm < 2 ^ w
  wSQ : C.X.SQ + C.X.Lb + 1 < 2 ^ w
  wP2 : C.X.P2 + C.X.Lb + 1 < 2 ^ w
  wNXT : C.X.NXT + C.L.NN < 2 ^ w
  nxt : ∀ v < C.L.NN, C.mem0 (C.X.NXT + v) < C.L.NN
  hiMM : ∀ v < C.L.NN, C.mem0 (C.L.HI + v) ≤ C.L.MM
  hSm : ∀ q ≤ C.X.Lb + 1, C.mem0 (C.X.SQ + q) ≤ C.Sm ∧ C.mem0 (C.X.P2 + q) ≤ C.Sm
  wT1 : (8 * C.X.M * (C.X.κ + C.nA) + (C.X.lo + (C.X.Lb + 1) * C.X.bw + 1) * (C.nA * 2 ^ C.X.Es)) *
    (C.Sm + 1) < 2 ^ w
  wT2 : 8 * C.X.M * (4 * (C.X.κ + C.X.nact) + C.X.κ * C.Sm) < 2 ^ w
  /-- The radii of the buckets are represented and below `INF`. -/
  hRm : C.X.lo + (C.X.Lb + 1) * C.X.bw ≤ C.Rm
  hINF : C.X.lo + (C.X.Lb + 1) * C.X.bw < C.L.INF
  /-- The numbers of the tests. -/
  hM : 1 ≤ C.X.M
  hLb : C.X.Lb = C.P.L
  hbw : C.X.bw = C.c.bw C.G C.P
  hκ : C.X.κ = C.P.κ
  hnact : C.X.nact = (C.c.act C.G C.P).card
  hsq : ∀ q, 1 ≤ q → q ≤ C.X.Lb → C.mem0 (C.X.SQ + q) = C.c.sq C.G C.P q
  hP2 : ∀ q, 1 ≤ q → q ≤ C.X.Lb → C.mem0 (C.X.P2 + q) = 2 ^ Cl.lam C.P q
  hcw : ∀ p, C.P.cw p = 1
  hwM : ∀ p ∈ C.c.act C.G C.P, C.wtP p * C.G.pω p = C.X.M
  /-- The petal graph represents the petal metric. -/
  link : C.c.PLink C.G C.pd.tj C.pd.hw C.Y C.sv C.gF C.Rm
  hsv : C.sv C.pd.tj = C.X.G.s
  img : (Finset.range C.nA).image C.pr = C.c.act C.G C.P
  inj : Set.InjOn C.pr ↑(Finset.range C.nA)
  hea : ∀ j < C.nA, C.ea j = C.sv (C.G.pu (C.pr j))
  heb : ∀ j < C.nA, C.eb j = C.sv (C.G.pv (C.pr j))
  okY : ∀ j < C.nA, (C.okN (C.ea j) ↔ C.G.pu (C.pr j) ∈ C.Y) ∧ (C.okN (C.eb j) ↔ C.G.pv (C.pr j) ∈ C.Y)
  /-- What `Fail.false` needs. -/
  hGo : C.G.Ok
  hκ1 : 1 ≤ C.P.κ
  hL1 : 1 ≤ C.P.L
  hΔ : 8 * C.P.L * (Cl.lam C.P 0 + 3) ≤ C.c.Δ C.G
  hV : C.c.V C.G C.P ≤ 2 ^ Cl.lam C.P 0 * C.P.κ

variable {C} {w : ℕ}

theorem Ok.hv_lt (h : C.Ok w) {i : ℕ} (hi : i < C.H.length) : C.hv i < C.L.NN :=
  (h.HS i hi).trans h.SN

theorem Ok.slot_mem (h : C.Ok w) {i : ℕ} (hi : i < C.H.length) :
    (C.L.g C.mem0).lo (C.hv i) ≤ C.slot (C.hv i) ∧ C.slot (C.hv i) < (C.L.g C.mem0).hi (C.hv i) := by
  have hn := h.hv_lt hi
  have hl := h.lohi _ (h.HN i hi)
  simp only [DL.g, if_pos hn, slot]
  omega

theorem Ok.slot_lt (h : C.Ok w) {i : ℕ} (hi : i < C.H.length) : C.slot (C.hv i) < C.L.MM := by
  have hn := h.hv_lt hi
  have := (h.slot_mem hi).2
  have := h.hiMM _ hn
  simp only [DL.g, if_pos hn] at *
  omega

theorem Ok.slot_inj (h : C.Ok w) {i i' : ℕ} (hi : i < C.H.length) (hi' : i' < C.H.length)
    (he : C.slot (C.hv i) = C.slot (C.hv i')) : i = i' := by
  have hm := h.slot_mem hi'
  have e := h.own (C.hv i') (C.slot (C.hv i')) i hm.1 hm.2 hi he.symm
  unfold hv at e
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at e
  exact ((List.Nodup.getElem_inj_iff h.Hnd).mp e).symm

theorem Ok.isSlot_iff (h : C.Ok w) {j i : ℕ} (hi : i < C.H.length) :
    C.IsSlot j (C.slot (C.hv i)) ↔ j < i := by
  constructor
  · rintro ⟨i', h1, h2, h3⟩
    rw [h.slot_inj hi h2 h3]; exact h1
  · intro hj; exact ⟨i, hj, hi, rfl⟩

theorem Ok.not_isSlot (_h : C.Ok w) {j k : ℕ} (hk : ∀ i < C.H.length, k ≠ C.slot (C.hv i)) :
    ¬ C.IsSlot j k := by
  rintro ⟨i, -, h2, h3⟩; exact hk i h2 h3

theorem Ok.not_okS (h : C.Ok w) : ¬ C.gF.ok C.X.S := fun hs => h.Sok ((h.Fok _).mp hs)

/-- **The memory graph.** While the cells that are not written are those of `mem0` and the slots
of `H[0], …, H[j]` are on, the graph in memory is `gC j`. -/
theorem Ok.g_eq (h : C.Ok w) {mem : ℕ → ℕ} {j : ℕ} (hfix : ∀ a, C.Fix a → mem a = C.mem0 a)
    (hsl : ∀ i < C.H.length, mem (C.L.HD + C.slot (C.hv i)) = if i ≤ j then C.nx i else C.X.S) :
    C.L.g mem = C.gC j := by
  show AG.mk _ _ _ _ _ = AG.mk _ _ _ _ _
  congr 1
  · funext u
    rw [h.Flo u]
    simp only [DL.g]
    split_ifs with hu
    · exact hfix _ (h.fLO u hu).1
    · rfl
  · funext u
    rw [h.Fhi u]
    simp only [DL.g]
    split_ifs with hu
    · exact hfix _ (h.fLO u hu).2.1
    · rfl
  · funext k
    by_cases hs : ∃ i < C.H.length, k = C.slot (C.hv i)
    · obtain ⟨i, hi, rfl⟩ := hs
      have hkM := h.slot_lt hi
      simp only [if_pos hkM, hsl i hi, h.isSlot_iff hi]
      by_cases hij : i ≤ j
      · rw [if_pos hij, if_neg (by omega), h.Fsl i hi]
      · rw [if_neg hij, if_pos (by omega)]
    · push Not at hs
      rw [if_neg (h.not_isSlot hs), h.Fhd k hs]
      simp only [DL.g]
      split_ifs with hk
      · exact hfix _ (h.fHD k hk hs)
      · rfl
  · funext k
    rw [h.Fcs k]
    simp only [DL.g]
    split_ifs with hk
    · exact hfix _ (h.fCS k hk).1
    · rfl
  · funext v
    apply propext
    rw [h.Fok v]
    simp only [DL.g]
    constructor
    · rintro ⟨hv, he⟩; exact ⟨hv, by rw [← hfix _ (h.fLO v hv).2.2.1]; exact he⟩
    · rintro ⟨hv, he⟩; exact ⟨hv, by rw [hfix _ (h.fLO v hv).2.2.1]; exact he⟩

theorem gC_top : C.gC C.H.length = C.gF := by
  have hn : ∀ k, ¬ C.IsSlot C.H.length k := fun k ⟨i, h1, h2, _⟩ => by omega
  exact (congrArg (fun f => AG.mk C.gF.lo C.gF.hi f C.gF.cs C.gF.ok)
    (funext fun k => if_neg (hn k))).trans rfl

/-- Every arc of `gC j` is an arc of the full graph. -/
theorem Ok.gC_arc (h : C.Ok w) {j u v c' : ℕ} (ha : (C.gC j).Arc u v c') : C.gF.Arc u v c' := by
  obtain ⟨k, k1, k2, hk, hc, hok⟩ := ha
  refine ⟨k, k1, k2, ?_, hc, hok⟩
  simp only [gC] at hk
  split_ifs at hk with hs
  · subst hk; exact absurd hok h.not_okS
  · exact hk

/-- The slots that are off are owned by nodes that are not settled. -/
theorem Ok.gC_sub (h : C.Ok w) {d : DS} {j j' : ℕ} (hjj : j ≤ j')
    (hns : ∀ i, j < i → i < C.H.length → ¬ d.sett (C.hv i)) : AG.Sub (C.gC j) (C.gC j') d := by
  have key : ∀ j'', j ≤ j'' → ∀ u, d.sett u → ∀ k, C.gF.lo u ≤ k → k < C.gF.hi u →
      ¬ C.IsSlot j'' k := by
    rintro j'' hj'' u hu k k1 k2 ⟨i, h1, h2, h3⟩
    rw [h.Flo] at k1; rw [h.Fhi] at k2
    have e := h.own u k i k1 k2 h2 h3
    subst e
    exact hns i (by omega) h2 hu
  refine ⟨fun u v c' ha => ?_, fun _ _ => rfl, fun _ _ => rfl, fun u hu k k1 k2 => ?_,
    fun _ _ _ _ _ => rfl, fun _ => Iff.rfl⟩
  · obtain ⟨k, k1, k2, hk, hc, hok⟩ := ha
    refine ⟨k, k1, k2, ?_, hc, hok⟩
    simp only [gC] at hk ⊢
    split_ifs at hk with hs
    · subst hk; exact absurd hok h.not_okS
    · have : ¬ C.IsSlot j' k := fun ⟨i, h1, h2, h3⟩ => hs ⟨i, by omega, h2, h3⟩
      rw [if_neg this]; exact hk
  · simp only [gC]
    rw [if_neg (key j' hjj u hu k k1 k2), if_neg (key j le_rfl u hu k k1 k2)]

theorem Ok.gC_subF (h : C.Ok w) {d : DS} {j : ℕ}
    (hns : ∀ i, j < i → i < C.H.length → ¬ d.sett (C.hv i)) : AG.Sub (C.gC j) C.gF d := by
  by_cases hj : j ≤ C.H.length
  · rw [← gC_top]; exact h.gC_sub (j := j) (j' := C.H.length) (d := d) hj hns
  · have hn : ∀ k, ¬ C.IsSlot j k := fun k ⟨i, h1, h2, _⟩ => by omega
    have e : C.gC j = C.gF := (congrArg (fun f => AG.mk C.gF.lo C.gF.hi f C.gF.cs C.gF.ok)
      (funext fun k => if_neg (hn k))).trans rfl
    rw [e]; exact AG.Sub.refl _ _

/-- The highway costs grow along the highway. -/
theorem Ok.hc_lt (h : C.Ok w) {i i' : ℕ} (hii : i < i') (hi' : i' < C.H.length) : C.hc i < C.hc i' := by
  induction i' with
  | zero => omega
  | succ n ih =>
    have := h.hinc n hi'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hii with hlt | heq
    · exact (ih hlt (by omega)).trans this
    · subst heq; exact this

/-- **A cheap walk uses no slot that is off.** -/
theorem Ok.reach_gC (h : C.Ok w) {j v k : ℕ} (hr : C.gF.Reach C.X.G.s v k)
    (hk : ∀ i, j < i → i < C.H.length → k < C.hc i) : (C.gC j).Reach C.X.G.s v k := by
  revert hk
  induction hr with
  | refl => intro _; exact .refl
  | @step u v' k1 c' hr ha ih =>
    intro hk
    refine .step (ih fun i h1 h2 => by have := hk i h1 h2; omega) ?_
    obtain ⟨kk, k1', k2', hkk, hc, hok⟩ := ha
    refine ⟨kk, k1', k2', ?_, hc, hok⟩
    have hns : ¬ C.IsSlot j kk := by
      rintro ⟨i, h1, h2, h3⟩
      rw [h.Flo] at k1'; rw [h.Fhi] at k2'
      have e := h.own u kk i k1' k2' h2 h3
      subst e
      have := (h.hhc i h2).2 k1 hr
      have := hk i h1 h2
      omega
    simp only [gC]
    rw [if_neg hns]
    exact hkk

/-- The distance to `H[i]` is `hc i`. -/
theorem Ok.δF_hv (h : C.Ok w) {i : ℕ} (hi : i < C.H.length) : C.δF (C.hv i) = C.hc i :=
  le_antisymm (Nat.sInf_le (h.hhc i hi).1) (le_csInf ⟨_, (h.hhc i hi).1⟩ (h.hhc i hi).2)

/-- **On the full graph, a settled cost is the distance.** -/
theorem tent_eq {INF cur pos : ℕ} {d : DS} (hinv : C.gF.Inv C.X.G.s INF cur pos d)
    (hdone : d.sett cur → C.gF.hi cur ≤ pos) {v : ℕ} (hv : d.sett v) : d.tent v = C.δF v := by
  have hlt : d.tent v < INF := (hinv.settled_le v hv).trans_lt hinv.L_lt
  have hr := hinv.reach v hlt
  have hlow : ∀ k ∈ {k | C.gF.Reach C.X.G.s v k}, d.tent v ≤ k := fun k hk =>
    (hinv.path hdone hinv.L_lt.le le_rfl (fun e he => (hinv.keys e he).1) hk).1 hv
  exact le_antisymm (le_csInf ⟨_, hr⟩ hlow) (Nat.sInf_le hr)

end SC

end MinCostFlow.LowStretch
