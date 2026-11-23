module

public import MinCostFlow.LowStretch.ProgChildRec
public import MinCostFlow.LowStretch.ProgChildMath
public import MinCostFlow.LowStretch.ProgChildOkW2

/-!
# The child step: its setting and the records of the raw children

The child step of a cluster `c` is fixed by the data `CS`: the merge tree, the pair graph, the
parameters, the cluster with its record and its decomposition step, the three blocks, the heap
pointer and the memory at the call. This file names the scratch arrays that the top level lays
out from the heap pointer (`CS.CHX`, …, `CS.H0`), states what they hold after the top level
(`TopOk`), and builds the record of each raw child from them (`CS.rawRec`). The record of a raw
child that keeps its threshold meets `Rec.Ok` (`CS.rawRec_ok`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The setting of one child step. -/
structure CS where
  T : KT
  G : PG
  P : Par
  c : Cl
  R : Rec
  D : Cl.Dec
  GB : ℕ
  RB : ℕ
  XB : ℕ
  h : ℕ
  mem : ℕ → ℕ

namespace CS

variable (S : CS)

/-- The three blocks at the call. -/
def E : GlobL := GlobL.read S.mem S.GB
def L : RecL := RecL.read S.mem S.RB
def X : PetL := PetL.read S.mem S.XB

/-- The number of children, of nodes of `c`, and of active pairs. -/
def nch : ℕ := S.D.nch
def s : ℕ := S.L.s
def nA : ℕ := S.X.nA

/-- The scratch arrays of the top level, one after the other from `h + 9 nch`: the piece of each
node, the node groups (`csrB`), the keys of the active pairs, the key groups (`csrB`) and the
highway marks. The children's arrays start at `H0`. -/
def CHX : ℕ := S.h + 9 * S.nch
def OFFN : ℕ := S.CHX + S.s
def CNTN : ℕ := S.OFFN + S.nch + 1
def ORDN : ℕ := S.CNTN + S.nch
def KEY : ℕ := S.ORDN + S.s
def OFFK : ℕ := S.KEY + S.nA
def CNTK : ℕ := S.OFFK + S.nch + 2
def ORDK : ℕ := S.CNTK + S.nch + 1
def HM : ℕ := S.ORDK + S.nA
def H0 : ℕ := S.HM + S.s

/-- The active pair of entry `i` and its flag. -/
def actP (i : ℕ) : ℕ := S.mem (S.X.ACT + 2 * i)
def actF (i : ℕ) : ℕ := S.mem (S.X.ACT + 2 * i + 1)

/-- The piece of node `u`, as `chxP` leaves it in the memory `M`. -/
def chxF (M : ℕ → ℕ) (u : ℕ) : ℕ := if u < S.s then M (S.CHX + u) else 0

/-- The key of active entry `i`: its piece when both ends lie in one piece, `nch` otherwise. -/
noncomputable def keyF (M : ℕ → ℕ) (i : ℕ) : ℕ :=
  if S.chxF M (S.R.sv S.T S.c (S.G.pu (S.actP i))) = S.chxF M (S.R.sv S.T S.c (S.G.pv (S.actP i)))
  then S.chxF M (S.R.sv S.T S.c (S.G.pu (S.actP i))) else S.nch

/-- The node `i` of the node groups, and the entry `i` of the key groups. -/
noncomputable def raw (k : ℕ) : Cl := S.c.raw S.G S.D k

end CS

/-- **What the top level leaves**, in the memory `M`: the pieces of the nodes, the nodes grouped by
piece, the keys of the active pairs and the entries grouped by key. Below `h` nothing changed,
and the highway marks and everything after them are zero. -/
structure TopOk (S : CS) (M : ℕ → ℕ) : Prop where
  chx1 : ∀ k < S.X.nP, ∀ u ∈ S.X.nodesOf S.mem k, M (S.CHX + u) = k + 1
  chx0 : ∀ u < S.s, (∀ k < S.X.nP, u ∉ S.X.nodesOf S.mem k) → M (S.CHX + u) = 0
  offN : ∀ u ≤ S.nch, M (S.OFFN + u) = offOf (S.chxF M) S.s u
  ordN : ∀ u < S.nch, ∀ j < (grp (S.chxF M) S.s u).length,
    M (S.ORDN + offOf (S.chxF M) S.s u + j) = (grp (S.chxF M) S.s u).getD j 0
  offK : ∀ u ≤ S.nch + 1, M (S.OFFK + u) = offOf (S.keyF M) S.nA u
  ordK : ∀ u < S.nch + 1, ∀ j < (grp (S.keyF M) S.nA u).length,
    M (S.ORDK + offOf (S.keyF M) S.nA u + j) = (grp (S.keyF M) S.nA u).getD j 0
  low : ∀ a < S.h, M a = S.mem a
  blk : ∀ a, S.h ≤ a → a < S.CHX → M a = 0
  zero : ∀ a, S.HM ≤ a → M a = 0

namespace CS

variable {S : CS} {M : ℕ → ℕ}

theorem chxF_one (hT : TopOk S M) (hnd : ∀ k < S.X.nP, ∀ u ∈ S.X.nodesOf S.mem k, u < S.s) :
    ∀ k < S.X.nP, ∀ u ∈ S.X.nodesOf S.mem k, S.chxF M u = k + 1 := by
  intro k hk u hu
  unfold chxF
  rw [ite_eq_left_iff.mpr (fun h => absurd (hnd k hk u hu) h)]
  exact hT.chx1 k hk u hu

theorem chxF_zero (hT : TopOk S M) :
    ∀ u, (∀ k < S.X.nP, u ∉ S.X.nodesOf S.mem k) → S.chxF M u = 0 := by
  intro u hu
  unfold chxF
  split_ifs with h
  · exact hT.chx0 u h hu
  · rfl

/-! ### The record of a raw child -/

variable (S) (M)

/-- The nodes of piece `k`, in the order of the node group `k`. -/
def nodesK (k : ℕ) : List ℕ := (grp (S.chxF M) S.s k).map (fun u => S.R.nodes.getD u 0)

/-- The stored pairs of piece `k`: the active entries of key `k`, with the half flags of the
piece. -/
noncomputable def SK (k : ℕ) : List (ℕ × ℕ) :=
  (grp (S.keyF M) S.nA k).map (fun i => (S.actP i, if S.actP i ∈ (S.raw k).half then 1 else 0))

/-- **The record of raw child `k`.** -/
noncomputable def rawRec (k : ℕ) : Rec :=
  ⟨S.nodesK M k, S.SK M k, (S.raw k).hw.filter (fun p => S.c.θ ≤ S.G.pω p)⟩

variable {S} {M}

/-- The facts of the call that the records use. -/
structure Pre (S : CS) : Prop where
  two : 2 ≤ S.c.X.card
  ok : S.R.Ok S.T S.G S.P S.c
  dec : S.c.DecOk S.G S.P S.D
  pet : S.X.Ok S.T S.G S.P S.c S.R S.D S.mem
  s : S.s = S.R.nodes.length

theorem Pre.nd_lt (h : Pre S) : ∀ k < S.X.nP, ∀ u ∈ S.X.nodesOf S.mem k, u < S.s := by
  intro k hk u hu
  obtain ⟨v, hv, rfl⟩ := (h.pet.nodes k hk u).mp hu
  rw [h.s]
  exact h.ok.sv_lt (Cl.W_subset_X k hv)

theorem Pre.mem_act (h : Pre S) {p : ℕ} : p ∈ S.c.act S.G S.P ↔ ∃ i < S.nA, S.actP i = p := by
  rw [← h.pet.act p]
  unfold PetL.actL
  simp only [List.mem_map, List.mem_range]
  rfl

theorem Pre.actP_inj (h : Pre S) {i j : ℕ} (hi : i < S.nA) (hj : j < S.nA)
    (he : S.actP i = S.actP j) : i = j := by
  have hnd := h.pet.act_nodup
  unfold PetL.actL at hnd
  exact List.inj_on_of_nodup_map hnd (List.mem_range.mpr hi) (List.mem_range.mpr hj) he

/-- The entries of key `k` are the active pairs with both ends in piece `k`. -/
theorem Pre.mem_SK (h : Pre S) (hT : TopOk S M) {k : ℕ} (hk : k < S.nch) (p : ℕ) :
    p ∈ (S.SK M k).map Prod.fst ↔
      p ∈ S.c.act S.G S.P ∧ S.G.pu p ∈ (S.raw k).X ∧ S.G.pv p ∈ (S.raw k).X := by
  have hc1 := chxF_one hT h.nd_lt
  have hc0 := chxF_zero (M := M) hT
  have hs : S.s = S.R.nodes.length := h.s
  unfold SK
  simp only [List.map_map, List.mem_map, Function.comp_apply, grp, List.mem_filter,
    List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨hi, hki⟩, rfl⟩
    have hpa : S.actP i ∈ S.c.act S.G S.P := h.mem_act.mpr ⟨i, hi, rfl⟩
    refine ⟨hpa, ?_⟩
    refine (h.ok.act_raw_iff h.pet hc1 hc0 hk hpa).mpr ?_
    unfold keyF at hki
    split_ifs at hki with he
    · exact ⟨he, hki⟩
    · exact absurd hki (Nat.ne_of_gt hk)
  · rintro ⟨hpa, hu, hv⟩
    obtain ⟨i, hi, rfl⟩ := h.mem_act.mp hpa
    refine ⟨i, ⟨hi, ?_⟩, rfl⟩
    obtain ⟨e1, e2⟩ := (h.ok.act_raw_iff h.pet hc1 hc0 hk hpa).mp ⟨hu, hv⟩
    unfold keyF
    rw [ite_eq_left_iff.mpr (fun hn => absurd e1 hn)]
    exact e2

theorem Pre.SK_nodup (h : Pre S) (k : ℕ) : ((S.SK M k).map Prod.fst).Nodup := by
  unfold SK
  rw [List.map_map]
  refine List.Nodup.map_on (fun i hi j hj he => ?_) (List.Nodup.filter _ List.nodup_range)
  simp only [grp, List.mem_filter, List.mem_range] at hi hj
  exact h.actP_inj hi.1 hj.1 he

/-- **The record of a raw child meets `Rec.OkW`.** -/
theorem Pre.rawRec_okW (h : Pre S) (hT : TopOk S M) {k : ℕ} (hk : k < S.nch) :
    (S.rawRec M k).OkW S.T S.G (S.raw k) := by
  have hc1 := chxF_one hT h.nd_lt
  have hc0 := chxF_zero (M := M) hT
  refine Rec.ok_rawW h.ok h.two h.dec hk ?_ ?_ (h.SK_nodup k) ?_ (h.mem_SK hT hk)
  · show (S.nodesK M k).Nodup
    unfold nodesK; rw [h.s]; exact h.ok.chxNodes_nodup _ k
  · intro j
    show j ∈ S.nodesK M k ↔ _
    unfold nodesK; rw [h.s]; exact h.ok.mem_chxNodes h.pet hc1 hc0 hk j
  · intro e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp he
    rfl

/-- **The record of a raw child that keeps the invariant meets `Rec.Ok`.** -/
theorem Pre.rawRec_ok (h : Pre S) (hT : TopOk S M) {k : ℕ} (hk : k < S.nch)
    (hinv : (S.raw k).Inv S.G S.P) : (S.rawRec M k).Ok S.T S.G S.P (S.raw k) := by
  have hc1 := chxF_one hT h.nd_lt
  have hc0 := chxF_zero (M := M) hT
  refine Rec.ok_raw h.ok h.dec hk hinv ?_ ?_ (h.SK_nodup k) ?_ (h.mem_SK hT hk) rfl
  · show (S.nodesK M k).Nodup
    unfold nodesK; rw [h.s]; exact h.ok.chxNodes_nodup _ k
  · intro j
    show j ∈ S.nodesK M k ↔ _
    unfold nodesK; rw [h.s]; exact h.ok.mem_chxNodes h.pet hc1 hc0 hk j
  · intro e he
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp he
    rfl

end CS

end MinCostFlow.LowStretch
