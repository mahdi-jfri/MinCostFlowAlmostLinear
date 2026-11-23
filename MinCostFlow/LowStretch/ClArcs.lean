module

public import MinCostFlow.LowStretch.ClRep
public import MinCostFlow.LowStretch.ProgArcs2
public import MinCostFlow.LowStretch.DijRep

/-!
# The arcs of a cluster in memory

`arcFill` reads the record of a cluster from memory: the stored pairs with their half flags, the
ends and weights of all pairs, and the local index of every vertex (through a label). `Rec.Mem`
states what these arrays hold. Then:
* the length that `arcFill` computes is the length of the pair in the cluster (`Rec.Mem.ln_eq`);
* the arcs that `arcP` builds are the stored pairs of length at most `D`, between the local
  indices of their ends (`Rec.Mem.arc_iff`), as `Rec.Ok.ctr` asks;
* the class of an item fixes its cost (`Rec.Mem.cs_eq`), and the classes are few
  (`Rec.Mem.cc_lt`), as Dijkstra asks.

The weights are powers of two: `ω = 2 ^ E`, with `E` in the array `EXP`, and `θ = 2 ^ lθ`. A kept
item has length `2 ^ (E - f)` (`f` the half flag) and class `E - f + 2 - lθ ≥ 1`, while a dropped
item has cost and class `0`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Rec

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec}

/-- The arrays that `arcFill` reads hold the record `R`. -/
structure Mem (T : KT) (G : PG) (c : Cl) (R : Rec) (F : AF) (mem : ℕ → ℕ) : Prop where
  nS : F.nS = R.S.length
  s : F.s = R.nodes.length
  pr : ∀ j < R.S.length, mem (F.SA + 2 * j) = (R.S.getD j (0, 0)).1
  fl : ∀ j < R.S.length, mem (F.SA + 2 * j + 1) = (R.S.getD j (0, 0)).2
  ends : ∀ p < G.m, mem (F.IN + 3 * p) = G.pu p ∧ mem (F.IN + 3 * p + 1) = G.pv p
  pw : ∀ p < G.m, mem (F.PW + p) = G.pω p
  ex : ∀ p < G.m, G.pω p = 2 ^ mem (F.EXP + p)
  loc : ∀ v ∈ c.X, mem (F.LOC + mem (F.LAB + v)) = R.sv T c v
  th : c.θ = 2 ^ F.lθ

variable {F : AF} {mem : ℕ → ℕ}

theorem getD_mem {j : ℕ} (hj : j < R.S.length) : R.S.getD j (0, 0) ∈ R.S := by
  rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj

/-- The facts about stored entry `j`. -/
theorem Ok.entry (h : R.Ok T G P c) {j : ℕ} (hj : j < R.S.length) :
    (R.S.getD j (0, 0)).1 < G.m ∧ G.pu (R.S.getD j (0, 0)).1 ∈ c.X ∧
      G.pv (R.S.getD j (0, 0)).1 ∈ c.X ∧
      T.top c.θ (G.pu (R.S.getD j (0, 0)).1) ≠ T.top c.θ (G.pv (R.S.getD j (0, 0)).1) ∧
      (R.S.getD j (0, 0)).2 ≤ 1 ∧
      ((R.S.getD j (0, 0)).2 = 1 ↔ (R.S.getD j (0, 0)).1 ∈ c.half) :=
  h.S_ok _ (getD_mem hj)

/-- Two vertices with different nodes are not joined by light pairs. -/
theorem Ok.not_lconn (h : R.Ok T G P c) {a b : ℕ} (ha : a ∈ c.X) (hb : b ∈ c.X)
    (hne : T.top c.θ a ≠ T.top c.θ b) : ¬ c.LConn G a b := by
  rw [← h.sv_iff ha hb]
  intro e
  apply hne
  rw [← h.get_sv ha, ← h.get_sv hb]
  simp only [e]

/-- A stored pair is not light. -/
theorem Ok.theta_le (h : R.Ok T G P c) {j : ℕ} (hj : j < R.S.length) :
    c.θ ≤ G.pω (R.S.getD j (0, 0)).1 := by
  obtain ⟨hm, hu, hv, hne, -⟩ := h.entry hj
  exact h.not_light ⟨hm, Or.inl ⟨rfl, rfl⟩⟩ hu hv (h.not_lconn hu hv hne)

theorem Mem.pr_eq (hM : Mem T G c R F mem) {j : ℕ} (hj : j < F.nS) :
    F.pr mem j = (R.S.getD j (0, 0)).1 := hM.pr j (hM.nS ▸ hj)

theorem Mem.fl_eq (hM : Mem T G c R F mem) {j : ℕ} (hj : j < F.nS) :
    F.fl mem j = (R.S.getD j (0, 0)).2 := hM.fl j (hM.nS ▸ hj)

/-- The exponent of a stored pair is at least that of `θ`, and at least `1`. -/
theorem Mem.exp_ge (hM : Mem T G c R F mem) (h : R.Ok T G P c) {j : ℕ} (hj : j < F.nS) :
    F.lθ ≤ mem (F.EXP + F.pr mem j) ∧ 1 ≤ mem (F.EXP + F.pr mem j) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨hm, -⟩ := h.entry hj'
  have hθ := h.theta_le hj'
  rw [← hM.pr_eq hj] at hm hθ
  rw [hM.ex _ hm, hM.th] at hθ
  refine ⟨(Nat.pow_le_pow_iff_right (by norm_num)).mp hθ, ?_⟩
  obtain ⟨-, -, -, h2, -⟩ := h.hGo _ hm
  rw [hM.ex _ hm] at h2
  by_contra h0
  have e : mem (F.EXP + F.pr mem j) = 0 := by omega
  rw [e] at h2
  norm_num at h2

/-- **The length is the length in the cluster.** -/
theorem Mem.ln_eq (hM : Mem T G c R F mem) (h : R.Ok T G P c) {j : ℕ} (hj : j < F.nS) :
    F.ln mem j = c.len G (F.pr mem j) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨hm, -, -, -, hf1, hf2⟩ := h.entry hj'
  have hθ := h.theta_le hj'
  rw [← hM.pr_eq hj] at hm hθ hf2
  rw [← hM.fl_eq hj] at hf1 hf2
  unfold AF.ln Cl.len
  rw [if_neg (by omega), hM.pw _ hm, Nat.shiftRight_eq_div_pow]
  by_cases hh : F.pr mem j ∈ c.half
  · rw [if_pos hh, hf2.mpr hh]
  · rw [if_neg hh]
    have : F.fl mem j = 0 := by
      by_contra h0; exact hh (hf2.mp (by omega))
    rw [this]; simp

/-- A kept item has length `2 ^ (E - f)`. -/
theorem Mem.ln_pow (hM : Mem T G c R F mem) (h : R.Ok T G P c) {j : ℕ} (hj : j < F.nS) :
    F.ln mem j = 2 ^ (mem (F.EXP + F.pr mem j) - F.fl mem j) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨hm, -, -, -, hf1, -⟩ := h.entry hj'
  rw [← hM.pr_eq hj] at hm
  rw [← hM.fl_eq hj] at hf1
  have he := (hM.exp_ge h hj).2
  unfold AF.ln
  rw [hM.pw _ hm, hM.ex _ hm, Nat.shiftRight_eq_div_pow,
    Nat.pow_div (by omega) (by norm_num)]

/-- The class of a kept item is at least `1`. -/
theorem Mem.cl_pos (hM : Mem T G c R F mem) (h : R.Ok T G P c) {j : ℕ} (hj : j < F.nS) :
    1 ≤ F.cl mem j := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨-, -, -, -, hf1, -⟩ := h.entry hj'
  rw [← hM.fl_eq hj] at hf1
  have := (hM.exp_ge h hj).1
  unfold AF.cl; omega

theorem Mem.cl_add (hM : Mem T G c R F mem) (h : R.Ok T G P c) {j : ℕ} (hj : j < F.nS) :
    F.cl mem j + F.lθ = mem (F.EXP + F.pr mem j) - F.fl mem j + 2 := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨-, -, -, -, hf1, -⟩ := h.entry hj'
  rw [← hM.fl_eq hj] at hf1
  have := (hM.exp_ge h hj)
  unfold AF.cl; omega

/-- A kept item has length `2 ^ (cl + lθ - 2)`. -/
theorem Mem.ln_cl (hM : Mem T G c R F mem) (h : R.Ok T G P c) {j : ℕ} (hj : j < F.nS) :
    F.ln mem j = 2 ^ (F.cl mem j + F.lθ - 2) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨-, -, -, -, hf1, -⟩ := h.entry hj'
  rw [← hM.fl_eq hj] at hf1
  have := (hM.exp_ge h hj)
  rw [hM.ln_pow h hj]
  unfold AF.cl
  congr 1; omega

/-- **The class fixes the cost.** -/
theorem Mem.cs_eq (hM : Mem T G c R F mem) (h : R.Ok T G P c) {j j' : ℕ} (hj : j < F.nS)
    (hj' : j' < F.nS) (he : F.cc mem j = F.cc mem j') : F.cs mem j = F.cs mem j' := by
  unfold AF.cc at he
  unfold AF.cs
  have p1 := hM.cl_pos h hj
  have p2 := hM.cl_pos h hj'
  split_ifs at he ⊢ with k1 k2 k2
  · rw [hM.ln_cl h hj, hM.ln_cl h hj', he]
  · omega
  · omega
  · rfl

/-- **The classes are few.** If `4 D < 2 ^ (J + lθ)`, every class is below `J`. -/
theorem Mem.cc_lt (hM : Mem T G c R F mem) (h : R.Ok T G P c) {J : ℕ}
    (hJ : 4 * F.D < 2 ^ (J + F.lθ)) (hJ1 : 1 ≤ J) {j : ℕ} (hj : j < F.nS) : F.cc mem j < J := by
  unfold AF.cc
  split_ifs with hk
  · have hl := hM.ln_cl h hj
    have p := hM.cl_add h hj
    unfold AF.keep at hk
    have h1 : 2 ^ (F.cl mem j + F.lθ) ≤ 4 * F.D := by
      have e : 2 ^ (F.cl mem j + F.lθ) = 4 * 2 ^ (F.cl mem j + F.lθ - 2) := by
        rw [show F.cl mem j + F.lθ = (F.cl mem j + F.lθ - 2) + 2 by omega, pow_add]
        simp only [show F.cl mem j + F.lθ - 2 + 2 - 2 = F.cl mem j + F.lθ - 2 by omega]
        ring
      rw [e, ← hl]; omega
    have := lt_of_le_of_lt h1 hJ
    have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    omega
  · omega

/-- The local index of the first end of an item. -/
theorem Mem.ea_eq (hM : Mem T G c R F mem) (h : R.Ok T G P c) {j : ℕ} (hj : j < F.nS) :
    F.ea mem j = R.sv T c (G.pu (F.pr mem j)) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨hm, hu, -⟩ := h.entry hj'
  rw [← hM.pr_eq hj] at hm hu
  unfold AF.ea
  rw [(hM.ends _ hm).1, hM.loc _ hu]

/-- The local index of the second end of an item. -/
theorem Mem.eb_eq (hM : Mem T G c R F mem) (h : R.Ok T G P c) {j : ℕ} (hj : j < F.nS) :
    F.eb mem j = R.sv T c (G.pv (F.pr mem j)) := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨hm, -, hv, -⟩ := h.entry hj'
  rw [← hM.pr_eq hj] at hm hv
  unfold AF.eb
  rw [(hM.ends _ hm).2, hM.loc _ hv]

theorem Mem.ea_lt (hM : Mem T G c R F mem) (h : R.Ok T G P c) {j : ℕ} (hj : j < F.nS) :
    F.ea mem j < F.s := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨-, hu, -⟩ := h.entry hj'
  rw [← hM.pr_eq hj] at hu
  rw [hM.ea_eq h hj, hM.s]; exact h.sv_lt hu

theorem Mem.eb_lt (hM : Mem T G c R F mem) (h : R.Ok T G P c) {j : ℕ} (hj : j < F.nS) :
    F.eb mem j < F.s := by
  have hj' : j < R.S.length := hM.nS ▸ hj
  obtain ⟨-, -, hv, -⟩ := h.entry hj'
  rw [← hM.pr_eq hj] at hv
  rw [hM.eb_eq h hj, hM.s]; exact h.sv_lt hv

/-- **The arcs are the stored pairs of length at most `D`.** -/
theorem Mem.arc_iff (hM : Mem T G c R F mem) (h : R.Ok T G P c) (u v k : ℕ) :
    (∃ j < F.nS, F.keep mem j ∧
      ((F.ea mem j = u ∧ F.eb mem j = v) ∨ (F.eb mem j = u ∧ F.ea mem j = v)) ∧
      F.ln mem j = k) ↔
    ∃ p ∈ R.S.map Prod.fst, c.len G p ≤ F.D ∧ ∃ a ∈ c.X, ∃ b ∈ c.X,
      G.Joins p a b ∧ R.sv T c a = u ∧ R.sv T c b = v ∧ k = c.len G p := by
  constructor
  · rintro ⟨j, hj, hk, hc, hl⟩
    have hj' : j < R.S.length := hM.nS ▸ hj
    obtain ⟨hm, hu, hv, -⟩ := h.entry hj'
    rw [← hM.pr_eq hj] at hm hu hv
    unfold AF.keep at hk
    rw [hM.ln_eq h hj] at hk hl
    refine ⟨F.pr mem j, ?_, hk, ?_⟩
    · rw [hM.pr_eq hj]
      exact List.mem_map.mpr ⟨_, getD_mem hj', rfl⟩
    rw [hM.ea_eq h hj, hM.eb_eq h hj] at hc
    rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨_, hu, _, hv, ⟨hm, Or.inl ⟨rfl, rfl⟩⟩, e1, e2, hl.symm⟩
    · exact ⟨_, hv, _, hu, ⟨hm, Or.inr ⟨rfl, rfl⟩⟩, e1, e2, hl.symm⟩
  · rintro ⟨p, hp, hk, a, ha, b, hb, ⟨hm, hjn⟩, e1, e2, hl⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
    obtain ⟨j, hj', hje⟩ := List.mem_iff_getElem.mp he
    have hj : j < F.nS := hM.nS ▸ hj'
    have hpr : F.pr mem j = e.1 := by
      rw [hM.pr_eq hj, List.getD_eq_getElem _ _ hj', hje]
    refine ⟨j, hj, ?_, ?_, ?_⟩
    · unfold AF.keep; rw [hM.ln_eq h hj, hpr]; exact hk
    · rw [hM.ea_eq h hj, hM.eb_eq h hj, hpr]
      rcases hjn with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact Or.inl ⟨e1, e2⟩
      · rw [h1, h2]; exact Or.inr ⟨e1, e2⟩
    · rw [hM.ln_eq h hj, hpr, hl]

end Rec

/-! ### The graph that `arcP` leaves, as Dijkstra reads it -/

namespace AP

variable (A : AP)

/-- The layout of a run of Dijkstra on the graph of `arcP`: the arcs of `u` are the cells
`OFF[u], …, OFF[u + 1] - 1`, with `s + 1` nodes and `2 nS` arcs. -/
def toDL (D J Aa INF TS rs : ℕ) : DL :=
  ⟨D, J, Aa, INF, A.OFF, A.OFF + 1, A.HD, A.CS, A.CL, A.OK, A.os, TS, A.s + 1, rs, 2 * A.nS⟩

theorem toDL_g (D J Aa INF TS rs : ℕ) (mem : ℕ → ℕ) : (A.toDL D J Aa INF TS rs).g mem = A.g mem :=
  rfl

variable {A}

/-- The offsets grow. -/
theorem off_mono {mem : ℕ → ℕ} (hm : ∀ u < A.s + 1, mem (A.OFF + u) ≤ mem (A.OFF + 1 + u))
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ A.s + 1) : mem (A.OFF + a) ≤ mem (A.OFF + b) := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with e | e
    · rw [e]
    · have := ih (by omega) (by omega)
      have h2 := hm b (by omega)
      rw [show A.OFF + 1 + b = A.OFF + (b + 1) by omega] at h2
      omega

/-- The degrees add up to the last offset. -/
theorem sum_deg {mem : ℕ → ℕ} (hm : ∀ u < A.s + 1, mem (A.OFF + u) ≤ mem (A.OFF + 1 + u))
    {k : ℕ} (hk : k ≤ A.s + 1) :
    ∑ u ∈ Finset.range k, (mem (A.OFF + 1 + u) - mem (A.OFF + u)) =
      mem (A.OFF + k) - mem A.OFF := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have h1 := off_mono hm (Nat.zero_le k) (by omega)
    have h2 := hm k (by omega)
    rw [Nat.add_zero] at h1
    rw [show A.OFF + 1 + k = A.OFF + (k + 1) by omega] at h2 ⊢
    omega

end AP

namespace Rec

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec}

/-- **What `arcP` leaves, for Dijkstra.** After `arcP` on the record `R`, the graph sits on the
cluster as `Cl.Ctr` asks, its nodes are the local indices, and the arcs meet the conditions of
`DL.Shape` that concern them. -/
theorem arcP_out {w : ℕ} {A : AP} {mem mem' : ℕ → ℕ} {v : ℕ}
    (hpost : (arcPC w).post A.args mem v mem') (hM : Mem T G c R A.toAF mem) (h : R.Ok T G P c)
    (hD : c.Δ G ≤ A.D) :
    c.Ctr G (A.g mem') (R.sv T c) {p | p ∈ R.S.map Prod.fst ∧ c.len G p ≤ A.D} ∧
    (∀ u, (A.g mem').ok u ↔ u ∈ Finset.range A.s) ∧
    (∀ u < A.s, (A.g mem').lo u ≤ (A.g mem').hi u ∧ (A.g mem').hi u ≤ 2 * A.nS) ∧
    (∀ k < 2 * A.nS, mem' (A.HD + k) < A.s + 1 ∧ mem' (A.CS + k) ≤ A.D ∧
      ∃ j < A.nS, mem' (A.CL + k) = A.toAF.cc mem j) ∧
    (∀ k < 2 * A.nS, ∀ k' < 2 * A.nS, mem' (A.CL + k) = mem' (A.CL + k') →
      mem' (A.CS + k) = mem' (A.CS + k')) ∧
    ∑ u ∈ Finset.range A.s, ((A.g mem').hi u - (A.g mem').lo u + 1) ≤ 2 * A.nS + A.s := by
  obtain ⟨harc, hper, h0, hmono, hlast, hmk1, hmk2, -⟩ := hpost A rfl
  have hea : ∀ j < A.nS, A.toAF.ea mem j < A.s := fun j hj => hM.ea_lt h hj
  have heb : ∀ j < A.nS, A.toAF.eb mem j < A.s := fun j hj => hM.eb_lt h hj
  refine ⟨h.ctr hD fun u v k => (harc u v k).trans (hM.arc_iff h u v k), fun u => ?_,
    fun u hu => ?_, fun k hk => ?_, fun k hk k' hk' he => ?_, ?_⟩
  · simp only [AP.g, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hc
      have e : u = A.s := by omega
      rw [e, hmk2] at h2; omega
    · intro hu; exact ⟨by omega, hmk1 u hu⟩
  · simp only [AP.g, if_pos (show u < A.s + 1 by omega)]
    refine ⟨hmono u (by omega), ?_⟩
    have := AP.off_mono hmono (show u + 1 ≤ A.s + 1 by omega) le_rfl
    rw [show A.OFF + 1 + u = A.OFF + (u + 1) by omega]
    rw [show A.OFF + 1 + A.s = A.OFF + (A.s + 1) by omega] at hlast
    omega
  · obtain ⟨j, hj, hh, hc, hl⟩ := hper k hk
    refine ⟨?_, ?_, j, hj, hl⟩
    · rcases hh with e | e <;> rw [e] <;> simp only [AF.ta, AF.tb] <;> split_ifs
      · have := hea j hj; omega
      · show A.s < A.s + 1; omega
      · have := heb j hj; omega
      · show A.s < A.s + 1; omega
    · rw [hc]; unfold AF.cs; split_ifs with hk
      · exact hk
      · exact Nat.zero_le _
  · obtain ⟨j, hj, -, hc, hl⟩ := hper k hk
    obtain ⟨j', hj', -, hc', hl'⟩ := hper k' hk'
    rw [hc, hc']
    rw [hl, hl'] at he
    exact hM.cs_eq h hj hj' he
  · have e : ∀ u ∈ Finset.range A.s, (A.g mem').hi u - (A.g mem').lo u + 1 =
        (mem' (A.OFF + 1 + u) - mem' (A.OFF + u)) + 1 := fun u hu => by
      have hu' : u < A.s + 1 := by simp at hu; omega
      simp only [AP.g, if_pos hu']
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, AP.sum_deg hmono (by omega)]
    have := AP.off_mono hmono (show A.s ≤ A.s + 1 by omega) le_rfl
    rw [show A.OFF + 1 + A.s = A.OFF + (A.s + 1) by omega] at hlast
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    omega

end Rec

end MinCostFlow.LowStretch
