module

public import MinCostFlow.LowStretch.PSearchCtx

/-!
# The invariant of the petal search

The ghost state `SG` of the search is the state of Dijkstra, the settled list `ℓ`, the highway
pointer `j` and the bucket pointer `q`. The invariant `SC.Inv` says:
* the memory holds the state of Dijkstra on the graph in memory, as in a run of `dijRun`;
* the cells that are never written are those of `mem0`, the slots of `H[0], …, H[j]` are on and
  the others off, and the settled highway nodes are `H[0], …, H[j-1]`;
* the settled list is in memory, and the five sums are `ESum` of it;
* the buckets below `q` fail for every radius, and the others below the last key `d.L`.

This file shows that the invariant gives the precondition of `pstep` (`Inv.pre`), and that the
measure `μ` pays for a call (`Inv.pay`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The ghost state of the petal search. -/
structure SG where
  d : DS
  qs : ℕ → List (ℕ × ℕ)
  cur : ℕ
  pos : ℕ
  ℓ : List ℕ
  j : ℕ
  q : ℕ

/-! ### Bounds on the five sums -/

theorem efst_mem {ea eb : ℕ → ℕ} {ℓ : List ℕ} {j : ℕ} (h : ea j ∈ ℓ ∨ eb j ∈ ℓ) :
    efst ea eb ℓ j ∈ ℓ := by
  unfold efst
  split_ifs with hle
  · by_contra hn
    rcases h with h | h
    · exact hn h
    · have := idxOf_lt_of_mem h
      rw [idxOf_of_not_mem hn] at hle; omega
  · by_contra hn
    rcases h with h | h
    · have := idxOf_lt_of_mem h
      rw [idxOf_of_not_mem hn] at hle; omega
    · exact hn h

theorem esum_le {ea eb wt : ℕ → ℕ} {ok : ℕ → Prop} {δ : ℕ → ℕ} {n : ℕ} {ℓ : List ℕ} {W B : ℕ}
    (hw : ∀ j < n, wt j ≤ W) (hδ : ∀ v ∈ ℓ, δ v ≤ B) :
    ESum ea eb wt ok δ n ℓ 0 ≤ n ∧ ESum ea eb wt ok δ n ℓ 1 ≤ n * W ∧
      ESum ea eb wt ok δ n ℓ 3 ≤ n * (W * B) ∧ ∀ t, ESum ea eb wt ok δ n ℓ t ≤ n * (W * B + W + 1) := by
  have key : ∀ j < n, eTerm ea eb wt ok δ ℓ j 0 ≤ 1 ∧ eTerm ea eb wt ok δ ℓ j 1 ≤ W ∧
      eTerm ea eb wt ok δ ℓ j 3 ≤ W * B ∧ ∀ t, eTerm ea eb wt ok δ ℓ j t ≤ W * B + W + 1 := by
    intro j hj
    have h1 := hw j hj
    have h3 : EOne ea eb ok ℓ j → wt j * δ (efst ea eb ℓ j) ≤ W * B := fun he =>
      Nat.mul_le_mul h1 (hδ _ (efst_mem he.1))
    have h4 : EBoth ea eb ℓ j → wt j * δ (efst ea eb ℓ j) ≤ W * B := fun he =>
      Nat.mul_le_mul h1 (hδ _ (efst_mem (Or.inl he.1)))
    refine ⟨?_, ?_, ?_, fun t => ?_⟩
    · simp only [eTerm]; split_ifs <;> omega
    · simp only [eTerm]; split_ifs <;> omega
    · simp only [eTerm]; split_ifs with he
      · exact h3 he
      · omega
    · fin_cases t <;> simp only [eTerm] <;> split_ifs with he <;>
        first | omega | (have := h3 he; omega) | (have := h4 he; omega)
  unfold ESum
  refine ⟨?_, ?_, ?_, fun t => ?_⟩
  · have := Finset.sum_le_sum fun j (hj : j ∈ Finset.range n) => (key j (Finset.mem_range.mp hj)).1
    simpa using this
  · have := Finset.sum_le_sum fun j (hj : j ∈ Finset.range n) => (key j (Finset.mem_range.mp hj)).2.1
    simpa using this
  · have := Finset.sum_le_sum fun j (hj : j ∈ Finset.range n) =>
      (key j (Finset.mem_range.mp hj)).2.2.1
    simpa using this
  · have := Finset.sum_le_sum fun j (hj : j ∈ Finset.range n) =>
      (key j (Finset.mem_range.mp hj)).2.2.2 t
    simpa using this

theorem shl_le (E e : ℕ) : 1 <<< (E - e) ≤ 2 ^ E := by
  rw [Nat.one_shiftLeft]; exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)

namespace SC

variable (C : SC)

/-- The ghost values of `pstep` at the ghost state `a`. -/
def Xf (a : SG) : PSG :=
  { C.X with G := ⟨C.L, C.X.G.Nodes, C.X.G.s, a.cur, a.pos, a.d, a.qs, C.X.G.R⟩ }

/-- The sums at the settled list `ℓ`. -/
noncomputable def es (ℓ : List ℕ) (t : Fin 5) : ℕ :=
  ESum C.ea C.eb (C.wtP ∘ C.pr) C.okN C.δF C.nA ℓ t

/-- The bucket failures. -/
def BF (q x : ℕ) : Prop := C.c.BFail C.G C.P C.Y C.pd C.X.lo q x

/-- **The invariant of the search.** -/
structure Inv (w : ℕ) (a : SG) (mem : ℕ → ℕ) : Prop where
  shape : C.L.Shape w mem C.X.G.Nodes
  rep : C.L.Rep mem C.X.G.Nodes a.d a.qs
  inv : (C.L.g mem).Inv C.X.G.s C.L.INF a.cur a.pos a.d
  done : a.d.sett a.cur → (C.L.g mem).hi a.cur ≤ a.pos
  cap : ∀ c < C.L.J, mem (pqT C.L.D C.L.J c) ≤ C.L.setSum mem C.X.G.Nodes a.d.sett + 1
  par : (C.L.g mem).ParInv C.X.G.s C.L.INF a.d (C.L.par mem) (C.L.parc mem)
  tz : C.L.TZ mem a.qs
  stamps : C.L.Stamps mem
  fix : ∀ x, C.Fix x → mem x = C.mem0 x
  jle : a.j ≤ C.H.length
  ptr : mem (C.X.CTL + 2) = (C.H ++ [C.X.S]).getD a.j 0
  slots : ∀ i < C.H.length, mem (C.L.HD + C.slot (C.hv i)) = if i ≤ a.j then C.nx i else C.X.S
  hsett : ∀ i < C.H.length, (a.d.sett (C.hv i) ↔ i < a.j)
  ns : mem (C.X.CTL + 1) = a.ℓ.length
  sl : ∀ i < a.ℓ.length, mem (C.X.SL + i) = a.ℓ.getD i 0
  nd : a.ℓ.Nodup
  sett : ∀ v, a.d.sett v ↔ v ∈ a.ℓ
  lastL : mem (C.X.CTL + 3) = a.d.L
  sums : ∀ t : Fin 5, mem (C.X.SUM + t) = C.es a.ℓ t
  qc : mem C.X.CTL = a.q
  q1 : 1 ≤ a.q
  qL : a.q ≤ C.X.Lb + 1
  qd : a.q ≤ C.X.Lb → a.d.L ≤ C.X.lo + a.q * C.X.bw
  bdone : ∀ q, 1 ≤ q → q < a.q → ∀ x, C.BF q x
  bnow : ∀ q, a.q ≤ q → q ≤ C.X.Lb → C.BF q a.d.L
  /-- The cells above the settled list are never written. -/
  top : ∀ x, C.X.SL + C.L.NN + 1 ≤ x → mem x = C.mem0 x

/-- The measure of the search. -/
noncomputable def μ (a : SG) : ℕ :=
  4 * C.L.pot C.mem0 C.X.G.Nodes a.d a.qs + 500 * (C.X.Lb + 1 - a.q) + 2 * stCost C.L.J + 2000

variable {C} {w : ℕ} {a : SG} {mem : ℕ → ℕ}

theorem Inv.g (h : C.Ok w) (hI : C.Inv w a mem) : C.L.g mem = C.gC a.j := h.g_eq hI.fix hI.slots

theorem Inv.deg (h : C.Ok w) (hI : C.Inv w a mem) (u : ℕ) : C.L.deg mem u = C.L.deg C.mem0 u := by
  unfold DL.deg
  rw [hI.g h]
  show C.gF.hi u - C.gF.lo u = _
  rw [h.Fhi, h.Flo]

theorem pot_eq_of_deg {L : DL} {mem mem' : ℕ → ℕ} (h : ∀ u, L.deg mem' u = L.deg mem u)
    (Nodes : Finset ℕ) (d : DS) (qs : ℕ → List (ℕ × ℕ)) :
    L.pot mem' Nodes d qs = L.pot mem Nodes d qs := by
  unfold DL.pot; simp only [h]

theorem setSum_eq_of_deg {L : DL} {mem mem' : ℕ → ℕ} (h : ∀ u, L.deg mem' u = L.deg mem u)
    (Nodes : Finset ℕ) (s : ℕ → Prop) : L.setSum mem' Nodes s = L.setSum mem Nodes s := by
  unfold DL.setSum; simp only [h]

/-- The invariant of Dijkstra holds on the full graph. -/
theorem Inv.invF (h : C.Ok w) (hI : C.Inv w a mem) :
    C.gF.Inv C.X.G.s C.L.INF a.cur a.pos a.d := by
  have hs := h.gC_subF (d := a.d) (j := a.j) fun i h1 h2 hs => by
    have := (hI.hsett i h2).mp hs; omega
  have := hI.inv
  rw [hI.g h] at this
  exact this.sub hs

theorem Inv.doneF (h : C.Ok w) (hI : C.Inv w a mem) : a.d.sett a.cur → C.gF.hi a.cur ≤ a.pos := by
  have := hI.done
  rw [hI.g h] at this
  exact this

/-- A settled cost is the distance in the full graph. -/
theorem Inv.tent (h : C.Ok w) (hI : C.Inv w a mem) {v : ℕ} (hv : a.d.sett v) :
    a.d.tent v = C.δF v :=
  tent_eq (hI.invF h) (hI.doneF h) hv

theorem Inv.δF_lt (h : C.Ok w) (hI : C.Inv w a mem) {v : ℕ} (hv : v ∈ a.ℓ) :
    C.δF v < C.L.INF := by
  have hs := (hI.sett v).mpr hv
  rw [← hI.tent h hs]
  exact (hI.inv.settled_le v hs).trans_lt hI.inv.L_lt

theorem Inv.lt_NN (hI : C.Inv w a mem) {v : ℕ} (hv : a.d.sett v) : v < C.L.NN :=
  ((hI.shape.ok_iff v).mpr ((hI.rep.sett v).mp hv).1).1

theorem Inv.len_le (hI : C.Inv w a mem) : a.ℓ.length ≤ C.L.NN := by
  rw [← List.toFinset_card_of_nodup hI.nd]
  have : a.ℓ.toFinset ⊆ Finset.range C.L.NN := fun v hv =>
    Finset.mem_range.mpr (hI.lt_NN ((hI.sett v).mpr (List.mem_toFinset.mp hv)))
  simpa using Finset.card_le_card this

theorem Ok.wtP_le (h : C.Ok w) {j : ℕ} (hj : j < C.nA) : C.wtP (C.pr j) ≤ 2 ^ C.X.Es := by
  rw [← h.hwt j hj]; exact shl_le _ _

/-- The bounds on the sums in memory. -/
theorem Inv.sums_le (h : C.Ok w) (hI : C.Inv w a mem) :
    C.es a.ℓ 0 ≤ C.nA ∧ C.es a.ℓ 1 ≤ C.nA * 2 ^ C.X.Es ∧
      C.es a.ℓ 3 ≤ C.nA * (2 ^ C.X.Es * C.L.INF) ∧
      ∀ t, C.es a.ℓ t ≤ C.nA * (2 ^ C.X.Es * C.L.INF + 2 ^ C.X.Es + 1) :=
  esum_le (fun j hj => h.wtP_le hj) (fun v hv => (hI.δF_lt h hv).le)

theorem keepS_of_ge (h : C.Ok w) {x : ℕ} (hx : C.X.G.R + 2 ≤ x) : C.L.KeepS C.X.G.R x :=
  Or.inr (Or.inr ⟨by have := h.hR; omega, by omega, by omega⟩)

/-- **The test can be made.** -/
theorem Inv.test_pre (h : C.Ok w) (hI : C.Inv w a mem) (hT : (C.Xf a).TB mem) :
    ((C.Xf a).pt mem).Pre mem w := by
  obtain ⟨s0, s1, s3, -⟩ := hI.sums_le h
  have e0 := hI.sums 0
  have e1 := hI.sums 1
  have e3 := hI.sums 3
  simp only [Fin.val_zero, Fin.val_one, Nat.add_zero] at e0 e1
  have e3' : mem (C.X.SUM + 3) = C.es a.ℓ 3 := e3
  have hq := hI.qc
  have hqL := hI.qL
  have hTq : mem C.X.CTL < C.X.Lb + 1 := hT.1
  have hfq := h.fSQ (mem C.X.CTL) (by omega)
  have hsq := h.hSm (mem C.X.CTL) (by omega)
  rw [← hI.fix _ hfq.1, ← hI.fix _ hfq.2] at hsq
  have hr : (C.Xf a).rr mem ≤ C.X.lo + (C.X.Lb + 1) * C.X.bw := by
    have : mem C.X.CTL * C.X.bw ≤ (C.X.Lb + 1) * C.X.bw := Nat.mul_le_mul_right _ (by omega)
    have hbq : (C.Xf a).bq mem = C.X.lo + mem C.X.CTL * C.X.bw := rfl
    by_cases hb : (C.Xf a).bq mem < (C.Xf a).k mem
    · rw [PSG.rr_of_lt _ _ hb]; omega
    · rw [PSG.rr_of_ge _ _ hb]; omega
  have hκ : 1 ≤ C.X.κ := by rw [h.hκ]; exact h.hκ1
  have hW := h.wT1
  have hW2 := h.wT2
  have hU := h.wU
  set BB := C.X.lo + (C.X.Lb + 1) * C.X.bw
  set E := 2 ^ C.X.Es
  have hI0 : ((C.Xf a).pt mem).I mem ≤ C.nA := by
    show mem C.X.SUM ≤ _; rw [e0]; exact s0
  have hC0 : ((C.Xf a).pt mem).C mem ≤ C.nA * E := by
    show mem (C.X.SUM + 1) - mem (C.X.SUM + 2) ≤ _; rw [e1]; omega
  have hrC : ((C.Xf a).pt mem).r * ((C.Xf a).pt mem).C mem ≤ BB * (C.nA * E) :=
    Nat.mul_le_mul hr hC0
  have hvol : ((C.Xf a).pt mem).vol8 mem ≤ 8 * C.X.M * (C.X.κ + C.nA) + BB * (C.nA * E) := by
    unfold PT.vol8
    have : 8 * C.X.M * (C.X.κ + ((C.Xf a).pt mem).I mem) ≤ 8 * C.X.M * (C.X.κ + C.nA) :=
      Nat.mul_le_mul_left _ (by omega)
    show 8 * C.X.M * (C.X.κ + ((C.Xf a).pt mem).I mem) + ((C.Xf a).pt mem).r * _ - _ ≤ _
    omega
  have hsq' : ((C.Xf a).pt mem).sq ≤ C.Sm := hsq.1
  have hp2' : ((C.Xf a).pt mem).P2 ≤ C.Sm := hsq.2
  set A0 := 8 * C.X.M * (C.X.κ + C.nA) + (BB + 1) * (C.nA * E)
  have hA0 : 8 * C.X.M * (C.X.κ + C.nA) + BB * (C.nA * E) + C.nA * E ≤ A0 := by
    have : (BB + 1) * (C.nA * E) = BB * (C.nA * E) + C.nA * E := add_one_mul _ _
    omega
  have hm : ∀ x y, x ≤ A0 → y ≤ C.Sm → x * y < 2 ^ w := fun x y hx hy =>
    lt_of_le_of_lt (Nat.mul_le_mul hx (by omega : y ≤ C.Sm + 1)) hW
  have hA1 : A0 < 2 ^ w := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by omega)) hW
  refine ⟨h.hM, hκ, by show C.X.SUM + 4 < 2 ^ w; have := h.wSL; have := h.hSL; omega,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 8 * C.X.M * (C.X.κ + ((C.Xf a).pt mem).I mem) + ((C.Xf a).pt mem).r * _ < 2 ^ w
    have : 8 * C.X.M * (C.X.κ + ((C.Xf a).pt mem).I mem) ≤ 8 * C.X.M * (C.X.κ + C.nA) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · exact hm _ _ (by omega) hsq'
  · show 8 * C.X.M * (4 * (C.X.κ + C.X.nact) + C.X.κ * ((C.Xf a).pt mem).P2) < 2 ^ w
    have : C.X.κ * ((C.Xf a).pt mem).P2 ≤ C.X.κ * C.Sm := Nat.mul_le_mul_left _ hp2'
    have : 8 * C.X.M * (4 * (C.X.κ + C.X.nact) + C.X.κ * ((C.Xf a).pt mem).P2) ≤
        8 * C.X.M * (4 * (C.X.κ + C.X.nact) + C.X.κ * C.Sm) := Nat.mul_le_mul_left _ (by omega)
    omega
  · exact hm _ _ (by omega) hp2'
  · show mem (C.X.SUM + 1) < 2 ^ w
    rw [e1]
    have : C.nA * E ≤ (C.nA + C.L.MM + 1) * (E * C.L.INF + E + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  · show mem (C.X.SUM + 3) < 2 ^ w
    rw [e3']
    have : C.nA * (E * C.L.INF) ≤ (C.nA + C.L.MM + 1) * (E * C.L.INF + E + 1) :=
      Nat.mul_le_mul (by omega) (Nat.le_succ_of_le (Nat.le_add_right _ _))
    omega

end SC

end MinCostFlow.LowStretch
