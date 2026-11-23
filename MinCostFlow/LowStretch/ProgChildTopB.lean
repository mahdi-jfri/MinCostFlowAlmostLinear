module

public import MinCostFlow.LowStretch.ProgChildTopM

/-!
# The top level: the scratch arrays

After the loads, the child step calls `chxP` (the piece of each node), `csrB` on the pieces (the
nodes grouped by piece), `keyP` (the key of each active entry) and `csrB` on the keys (the
entries grouped by key). This file proves that the four calls leave what `TopOk` says
(`CS.topCalls_runs`), within `CS.topCost`.

The facts that tie the calls to `TopOk` are in `CS.topOk_of`. The keys that `keyP` writes are
the keys `keyF` of `TopOk`, since the node of a vertex `v` of `c` is `LOC[LAB[v]]`
(`Rec.Mem.loc`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable (S : CS)

/-- The cost of the four calls. -/
def topCost : ℕ := 1000 + 300 * (S.s + S.nch + S.nA)

/-- The keys, as `keyP` computes them on the memory `M`. -/
def keyE (M : ℕ → ℕ) : KYE := ⟨S.nA, S.X.ACT, S.E.IN, S.E.LAB, S.E.LOC, S.CHX, S.nch, S.KEY, M⟩

/-- The registers of the top level after a call that returns into register `28`. -/
def TopR (st : State) : Prop := ∀ r, r ≠ 28 → st.regs r = S.topF r

variable {S} {w : ℕ}

theorem TopR.map {st : State} (h : S.TopR st) {l : List ℕ} (hl : 28 ∉ l) :
    l.map st.regs = l.map S.topF :=
  List.map_congr_left fun r hr => h r (by rintro rfl; exact hl hr)

theorem TopR.upd {st : State} (h : S.TopR st) (v : ℕ) (M : ℕ → ℕ) (q : ℕ) :
    S.TopR { mem := M, regs := Function.update st.regs 28 v, pos := q } := fun r hr => by
  show Function.update st.regs 28 v r = _
  rw [Function.update_of_ne hr]
  exact h r hr

/-- The scratch arrays one after the other. -/
theorem lay : S.CHX = S.h + 9 * S.nch ∧ S.OFFN = S.CHX + S.s ∧ S.CNTN = S.OFFN + S.nch + 1 ∧
    S.ORDN = S.CNTN + S.nch ∧ S.KEY = S.ORDN + S.s ∧ S.OFFK = S.KEY + S.nA ∧
    S.CNTK = S.OFFK + S.nch + 2 ∧ S.ORDK = S.CNTK + S.nch + 1 ∧ S.HM = S.ORDK + S.nA ∧
    S.H0 = S.HM + S.s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The words of the registers after the loads. -/
theorem topF_lt (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hb : S.H0 + S.nch + 4 < 2 ^ w) (r : ℕ) : S.topF r < 2 ^ w := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := S.lay
  have hX : S.XB + 16 ≤ S.h := hpre.below (S.XB, 16) (by simp [readRegs])
  have hG : S.GB + 21 ≤ S.h := hpre.below (S.GB, 21) (by simp [readRegs])
  have hR : S.RB + 9 ≤ S.h := hpre.below (S.RB, 9) (by simp [readRegs])
  have hPLr : (S.X.PL, S.mem (S.X.PO + S.X.nP)) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have hPOr : (S.X.PO, S.X.nP + 1) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have hACr : (S.X.ACT, 2 * S.X.nA) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have hINr : (S.E.IN, 3 * S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have hPL := hpre.below _ hPLr
  have hPO := hpre.below _ hPOr
  have hAC := hpre.below _ hACr
  have hIN := hpre.below _ hINr
  have hLA : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hLO : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hnP := nch_eq hpre
  dsimp only at hPL hPO hAC hIN
  unfold topF
  rcases Nat.lt_or_ge r 27 with h | h
  · interval_cases r <;> simp only [topVals, List.getD_cons_zero, List.getD_cons_succ] <;> omega
  · rw [List.getD_eq_default _ _ (by simp [topVals]; omega)]
    omega

/-! ### The memory after `chxP` -/

/-- What `chxP` leaves in `M`. -/
def ChxDone (S : CS) (M : ℕ → ℕ) : Prop :=
  (∀ k < S.chxE.nP, ∀ j, S.chxE.In k j → M (S.chxE.CHX + S.chxE.nd j) = k + 1) ∧
    ∀ a, (∀ k < S.chxE.nP, ∀ j, S.chxE.In k j → a ≠ S.chxE.CHX + S.chxE.nd j) → M a = S.mem a

theorem ChxDone.out (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {M : ℕ → ℕ} (h : S.ChxDone M) {a : ℕ} (ha : a < S.CHX ∨ S.CHX + S.s ≤ a) : M a = S.mem a :=
  h.2 a fun k hk j hj he => by
    have := (pre_of hpre).nd_lt k hk _ (mem_nodesOf.mpr ⟨j, hj, rfl⟩)
    change a = S.CHX + S.chxE.nd j at he
    omega

theorem ChxDone.one {M : ℕ → ℕ} (h : S.ChxDone M) {k : ℕ} (hk : k < S.X.nP) {u : ℕ}
    (hu : u ∈ S.X.nodesOf S.mem k) : M (S.CHX + u) = k + 1 := by
  obtain ⟨j, hj, rfl⟩ := mem_nodesOf.mp hu
  exact h.1 k hk j hj

theorem ChxDone.zero (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {M : ℕ → ℕ} (h : S.ChxDone M) {u : ℕ} (hu : ∀ k < S.X.nP, u ∉ S.X.nodesOf S.mem k) :
    M (S.CHX + u) = 0 := by
  rw [h.2 _ fun k hk j hj he => hu k hk (mem_nodesOf.mpr ⟨j, hj, by
    change S.CHX + u = S.CHX + S.chxE.nd j at he
    omega⟩)]
  exact hpre.zero _ (by have := S.lay.1; omega)

/-- The pieces are below `nch`. -/
theorem ChxDone.lt (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {M : ℕ → ℕ} (h : S.ChxDone M) (u : ℕ) : M (S.CHX + u) < S.nch := by
  have hnP := nch_eq hpre
  by_cases hu : ∃ k < S.X.nP, u ∈ S.X.nodesOf S.mem k
  · obtain ⟨k, hk, hu⟩ := hu
    rw [h.one hk hu]
    omega
  · push_neg at hu
    rw [h.zero hpre hu]
    omega

/-! ### The keys -/

/-- The node of a vertex of `c`, read through its label. -/
theorem keyE_nd (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {M : ℕ → ℕ} (hM : ∀ a < S.h, M a = S.mem a) {v : ℕ} (hv : v ∈ S.c.X) :
    (S.keyE M).nd v = S.R.sv S.T S.c v := by
  have hvn := hpre.ok.n_of_mem hv
  have hLA : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hLO : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hl : S.mem (S.E.LAB + v) < S.T.N := hpre.lab_lt v hvn
  show M (S.E.LOC + M (S.E.LAB + v)) = _
  rw [hM (S.E.LAB + v) (by omega), hM _ (by omega)]
  exact hpre.recAt.arcs.loc v hv

/-- The pair of an active entry and its ends. -/
theorem keyE_ends (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {M : ℕ → ℕ} (hM : ∀ a < S.h, M a = S.mem a) {i : ℕ} (hi : i < S.nA) :
    (S.keyE M).pr i = S.actP i ∧ (S.keyE M).eu i = S.G.pu (S.actP i) ∧
      (S.keyE M).ev i = S.G.pv (S.actP i) ∧ S.actP i ∈ S.c.act S.G S.P := by
  have hACr : (S.X.ACT, 2 * S.X.nA) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have hINr : (S.E.IN, 3 * S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have hAC := hpre.below _ hACr
  have hIN := hpre.below _ hINr
  dsimp only at hAC hIN
  have hnA : S.nA = S.X.nA := rfl
  have hact : S.actP i ∈ S.c.act S.G S.P := (pre_of hpre).mem_act.mpr ⟨i, hi, rfl⟩
  have hpm : S.actP i < S.G.m := (Cl.mem_act.mp hact).1
  have hm : S.E.m = S.G.m := hpre.glob.m
  have hpr : (S.keyE M).pr i = S.actP i := by
    show M (S.X.ACT + 2 * i) = _
    rw [hM _ (by omega)]; rfl
  have e1 : (S.keyE M).eu i = S.G.pu (S.actP i) := by
    show M (S.E.IN + 3 * (S.keyE M).pr i) = _
    rw [hpr, hM _ (by omega)]
    exact (hpre.glob.ends _ hpm).1
  have e2 : (S.keyE M).ev i = S.G.pv (S.actP i) := by
    show M (S.E.IN + 3 * (S.keyE M).pr i + 1) = _
    rw [hpr, hM _ (by omega)]
    exact (hpre.glob.ends _ hpm).2
  exact ⟨hpr, e1, e2, hact⟩

/-- **The precondition of `keyP`.** -/
theorem keyE_ok (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hb : S.H0 + S.nch + 4 < 2 ^ w) {M : ℕ → ℕ} (hM : ∀ a < S.h, M a = S.mem a) :
    (S.keyE M).Ok w := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := S.lay
  have hACr : (S.X.ACT, 2 * S.X.nA) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs, PetL.regs]
  have hINr : (S.E.IN, 3 * S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have hAC := hpre.below _ hACr
  have hIN := hpre.below _ hINr
  dsimp only at hAC hIN
  have hnA : S.nA = S.X.nA := rfl
  have hm : S.E.m = S.G.m := hpre.glob.m
  have hLA : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hLO : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hs := (pre_of hpre).s
  have rdv : ∀ v ∈ S.c.X, (S.keyE M).RdV v := fun v hv => by
    have hvn := hpre.ok.n_of_mem hv
    have hl : S.mem (S.E.LAB + v) < S.T.N := hpre.lab_lt v hvn
    have hsv := hpre.ok.sv_lt hv
    have hnd := keyE_nd hpre hM hv
    refine ⟨show S.E.LAB + v < S.KEY by omega, ?_, ?_⟩
    · show S.E.LOC + M (S.E.LAB + v) < S.KEY
      rw [hM _ (by omega)]; omega
    · show S.CHX + (S.keyE M).nd v < S.KEY
      rw [hnd]; omega
  refine ⟨fun i hi => ?_, by show S.KEY + S.nA + 1 < 2 ^ w; omega,
    by show S.nch < 2 ^ w; omega⟩
  have hi' : i < S.nA := hi
  obtain ⟨hpr, e1, e2, hact⟩ := keyE_ends hpre hM hi'
  have hpm : S.actP i < S.G.m := (Cl.mem_act.mp hact).1
  have hu := (Cl.mem_act.mp hact).2.1
  have hv := (Cl.mem_act.mp hact).2.2.1
  refine ⟨show S.X.ACT + 2 * i < S.KEY by omega, ?_, ?_, ?_⟩
  · show S.E.IN + 3 * (S.keyE M).pr i + 1 < S.KEY
    rw [hpr]; omega
  · rw [e1]; exact rdv _ hu
  · rw [e2]; exact rdv _ hv

/-- **The keys of `keyP` are `keyF`**, for a memory `M'` that agrees on the pieces with the
memory `Ma` after `chxP`. -/
theorem keyE_key (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {M Ma M' : ℕ → ℕ} (hM : ∀ a < S.h, M a = S.mem a)
    (hc : ∀ u < S.s, M (S.CHX + u) = Ma (S.CHX + u))
    (hc' : ∀ u < S.s, M' (S.CHX + u) = Ma (S.CHX + u)) {i : ℕ} (hi : i < S.nA) :
    (S.keyE M).key i = S.keyF M' i := by
  obtain ⟨hpr, e1, e2, hact⟩ := keyE_ends hpre hM hi
  have hu := (Cl.mem_act.mp hact).2.1
  have hv := (Cl.mem_act.mp hact).2.2.1
  have hs := (pre_of hpre).s
  have hsu := hpre.ok.sv_lt hu
  have hsv := hpre.ok.sv_lt hv
  have ch : ∀ v ∈ S.c.X, (S.keyE M).ch v = S.chxF M' (S.R.sv S.T S.c v) := fun v hv => by
    have := hpre.ok.sv_lt hv
    show M (S.CHX + (S.keyE M).nd v) = _
    rw [keyE_nd hpre hM hv]
    unfold chxF
    rw [if_pos (by omega), hc _ (by omega), hc' _ (by omega)]
  unfold KYE.key keyF
  rw [e1, e2, ch _ hu, ch _ hv]
  rfl

end CS

end MinCostFlow.LowStretch
