module

public import MinCostFlow.LowStretch.ProgRecSpec
public import MinCostFlow.LowStretch.ProgArcs2

/-!
# What the children of a cluster leave for each other

The recursion calls the cluster procedure on the children one after the other. Each call
changes the memory below its heap pointer only at the cells of `ChildWr` of its child and at its
part of the output. This file shows that these changes do not touch what a later child reads.

* `GlobL.Ok.congr` and `RecAt.congr`: the global block and a record block still hold what they
  held when the memory agrees on the regions they read (`SameOn`), and, for a record, on the
  labels of its vertices and the local indices of their heads.
* `ChildWr.cell`: a cell of `ChildWr` is a label or a local index. So a region apart from the
  labels and the local indices has no such cell (`not_childWr`).
* `childWr_mono`: a cell of `ChildWr` of a child is one of its parent.
* `childWr_disj`: a child does not write the label of a vertex of another child, nor the local
  index of the head of its node. Two nodes with the same head lie on one heavy path, so one is
  below the other (`KT.hd_eq`), and the vertex sets are unions of nodes (`KT.Sat`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {T : KT} {G : PG} {P : Par}

/-- The memories `M` and `M'` agree on the regions `rs`. -/
def SameOn (rs : List (ℕ × ℕ)) (M M' : ℕ → ℕ) : Prop :=
  ∀ r ∈ rs, ∀ i < r.2, M' (r.1 + i) = M (r.1 + i)

/-- The global arrays among the regions read. -/
def globArrs (E : GlobL) : List (ℕ × ℕ) :=
  [(E.IN, 3 * E.m), (E.PW, E.m), (E.EXP, E.m), (E.KPAR, E.N), (E.KCH1, E.N), (E.KCH2, E.N),
    (E.KMW, E.N), (E.KSZ, E.N), (E.KLO, E.N), (E.HEAD, E.N), (E.ORDL, E.n), (E.GOFF, E.N + 1),
    (E.GPR, E.m)]

theorem recRegs_eq (GB RB : ℕ) (E : GlobL) (L : RecL) :
    recRegs GB RB E L = (GB, 21) :: (RB, 9) :: (globArrs E ++ L.regs) := rfl

theorem mem_recRegs {GB RB : ℕ} {E : GlobL} {L : RecL} {r : ℕ × ℕ} :
    r ∈ recRegs GB RB E L ↔ r = (GB, 21) ∨ r = (RB, 9) ∨ r ∈ globArrs E ∨ r ∈ L.regs := by
  rw [recRegs_eq]; simp [List.mem_append]

theorem GlobL.read_congr {M M' : ℕ → ℕ} {a : ℕ} (h : ∀ i < 21, M' (a + i) = M (a + i)) :
    GlobL.read M' a = GlobL.read M a := by
  simp only [GlobL.read, GlobL.mk.injEq]
  have h0 := h 0 (by norm_num)
  simp only [Nat.add_zero] at h0
  exact ⟨h0, h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num), h 8 (by norm_num),
    h 9 (by norm_num), h 10 (by norm_num), h 11 (by norm_num), h 12 (by norm_num),
    h 13 (by norm_num), h 14 (by norm_num), h 15 (by norm_num), h 16 (by norm_num),
    h 17 (by norm_num), h 18 (by norm_num), h 19 (by norm_num), h 20 (by norm_num)⟩

theorem RecL.read_congr {M M' : ℕ → ℕ} {a : ℕ} (h : ∀ i < 9, M' (a + i) = M (a + i)) :
    RecL.read M' a = RecL.read M a := by
  simp only [RecL.read, RecL.mk.injEq]
  have h0 := h 0 (by norm_num)
  simp only [Nat.add_zero] at h0
  exact ⟨h0, h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num), h 8 (by norm_num)⟩

/-- **The global block keeps what it holds** when the memory agrees on the global arrays. -/
theorem GlobL.Ok.congr {E : GlobL} {M M' : ℕ → ℕ} (hE : E.Ok T G P M)
    (hs : SameOn (globArrs E) M M') : E.Ok T G P M' := by
  have hr : ∀ a len, (a, len) ∈ globArrs E → ∀ i < len, M' (a + i) = M (a + i) :=
    fun a len h i hi => hs _ h i hi
  have hN := hE.N
  have hm := hE.m
  have hn := hE.n
  obtain ⟨lf, hl1, hl2, hl3⟩ := hE.lca
  refine ⟨hE.n, hE.m, hE.N, hE.B, hE.tree, hE.hG, hE.hGo, fun k hk => ?_, fun k h1 h2 => ?_,
    fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun v hv => ?_,
    fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, ⟨lf, hl1, fun u hu => ?_, fun u hu j hj => ?_⟩,
    hE.heavy, hE.hB, hE.hJ, hE.hINF⟩
  · rw [hr E.KPAR E.N (by simp [globArrs]) k (by omega)]; exact hE.par k hk
  · rw [hr E.KCH1 E.N (by simp [globArrs]) k (by omega),
      hr E.KCH2 E.N (by simp [globArrs]) k (by omega)]
    exact hE.ch k h1 h2
  · rw [hr E.KMW E.N (by simp [globArrs]) k (by omega)]; exact hE.mw k hk
  · rw [hr E.KSZ E.N (by simp [globArrs]) k (by omega)]; exact hE.sz k hk
  · rw [hr E.KLO E.N (by simp [globArrs]) k (by omega)]; exact hE.lo k hk
  · rw [hr E.HEAD E.N (by simp [globArrs]) k (by omega)]; exact hE.hd k hk
  · have := KT.lo_lt hE.tree hv
    rw [hr E.ORDL E.n (by simp [globArrs]) _ (by omega)]; exact hE.ordl v hv
  · rw [show E.IN + 3 * p + 1 = E.IN + (3 * p + 1) by omega,
      hr E.IN (3 * E.m) (by simp [globArrs]) (3 * p) (by omega),
      hr E.IN (3 * E.m) (by simp [globArrs]) (3 * p + 1) (by omega)]
    rw [← show E.IN + 3 * p + 1 = E.IN + (3 * p + 1) by omega]
    exact hE.ends p hp
  · rw [hr E.PW E.m (by simp [globArrs]) p (by omega)]; exact hE.pw p hp
  · rw [hr E.EXP E.m (by simp [globArrs]) p (by omega)]; exact hE.ex p hp
  · rw [hr E.GOFF (E.N + 1) (by simp [globArrs]) u (by omega)]; exact hl2 u hu
  · have h1 := offOf_succ lf G.m u
    have h2 := offOf_le lf G.m (u + 1)
    rw [show E.GPR + offOf lf G.m u + j = E.GPR + (offOf lf G.m u + j) by omega,
      hr E.GPR E.m (by simp [globArrs]) _ (by omega),
      ← show E.GPR + offOf lf G.m u + j = E.GPR + (offOf lf G.m u + j) by omega]
    exact hl3 u hu j hj

/-- **A record block keeps what it holds** when the memory agrees on the regions read, on the
labels of the vertices and on the local indices of their heads. -/
theorem RecAt.congr {c : Cl} {R : Rec} {E : GlobL} {L : RecL} {M M' : ℕ → ℕ} {GB RB : ℕ}
    (hE : E.Ok T G P M) (hA : RecAt T G c R E L M) (hs : SameOn (recRegs GB RB E L) M M')
    (hlab : ∀ v ∈ c.X, M' (E.LAB + v) = M (E.LAB + v))
    (hloc : ∀ v ∈ c.X, M' (E.LOC + T.hd G (T.top c.θ v)) = M (E.LOC + T.hd G (T.top c.θ v))) :
    RecAt T G c R E L M' := by
  have hr : ∀ a len, (a, len) ∈ recRegs GB RB E L → ∀ i < len, M' (a + i) = M (a + i) :=
    fun a len h i hi => hs _ h i hi
  have hm := hE.m
  have hnS := hA.arcs.nS
  have hsS := hA.arcs.s
  have hnH := hA.nH
  simp only [RecL.af] at hnS hsS
  refine ⟨⟨hA.arcs.nS, hA.arcs.s, fun j hj => ?_, fun j hj => ?_, fun p hp => ?_, fun p hp => ?_,
    fun p hp => ?_, fun v hv => ?_, hA.arcs.th⟩, fun i hi => ?_, hA.x0, hA.t, hA.nH,
    fun j hj => ?_, fun v hv => ?_⟩
  all_goals try simp only [RecL.af]
  · rw [hr L.SA (2 * L.nS) (by simp [recRegs, RecL.regs]) (2 * j) (by omega)]
    have := hA.arcs.pr j hj; simpa [RecL.af] using this
  · rw [show L.SA + 2 * j + 1 = L.SA + (2 * j + 1) by omega,
      hr L.SA (2 * L.nS) (by simp [recRegs, RecL.regs]) (2 * j + 1) (by omega),
      ← show L.SA + 2 * j + 1 = L.SA + (2 * j + 1) by omega]
    have := hA.arcs.fl j hj; simpa [RecL.af] using this
  · rw [show E.IN + 3 * p + 1 = E.IN + (3 * p + 1) by omega,
      hr E.IN (3 * E.m) (by simp [recRegs]) (3 * p) (by omega),
      hr E.IN (3 * E.m) (by simp [recRegs]) (3 * p + 1) (by omega),
      ← show E.IN + 3 * p + 1 = E.IN + (3 * p + 1) by omega]
    have := hA.arcs.ends p hp; simpa [RecL.af] using this
  · rw [hr E.PW E.m (by simp [recRegs]) p (by omega)]
    have := hA.arcs.pw p hp; simpa [RecL.af] using this
  · rw [hr E.EXP E.m (by simp [recRegs]) p (by omega)]
    have := hA.arcs.ex p hp; simpa [RecL.af] using this
  · rw [hlab v hv, hA.lab v hv, hloc v hv, ← hA.lab v hv]
    have := hA.arcs.loc v hv; simpa [RecL.af] using this
  · rw [hr L.NA L.s (by simp [recRegs, RecL.regs]) i (by omega)]; exact hA.nodes i hi
  · have e : ∀ t < 4, M' (L.HW + 4 * j + t) = M (L.HW + 4 * j + t) := fun t ht => by
      rw [show L.HW + 4 * j + t = L.HW + (4 * j + t) by omega]
      exact hr L.HW (4 * L.nH) (by simp [recRegs, RecL.regs]) _ (by omega)
    have h0 := e 0 (by norm_num)
    simp only [Nat.add_zero] at h0
    rw [h0, e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num)]
    exact hA.hw j hj
  · rw [hlab v hv]; exact hA.lab v hv

/-- **A cell of `ChildWr` is a label or a local index.** -/
theorem ChildWr.cell (hT : T.Ok G) {c : Cl} {E : GlobL} {a : ℕ} (hsub : c.X ⊆ Finset.range G.n)
    (_hθ : 1 ≤ c.θ) (hw : ChildWr T G c E a) :
    (∃ v < G.n, a = E.LAB + v) ∨ ∃ x < T.N, a = E.LOC + x := by
  rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, k, hvk, -, rfl⟩
  · exact Or.inl ⟨v, Finset.mem_range.mp (hsub hv), rfl⟩
  · have hvn := Finset.mem_range.mp (hsub hv)
    have hkN : k < T.N := hvk.lt_N hT (by have := hT.n_lt; omega)
    exact Or.inr ⟨T.hd G k, (KT.hd_under hT k hkN).lt_N hT hkN, rfl⟩

/-- A cell of a region apart from the labels and the local indices is not in `ChildWr`. -/
theorem not_childWr (hT : T.Ok G) {c : Cl} {E : GlobL} {r : ℕ × ℕ} {a : ℕ}
    (hsub : c.X ⊆ Finset.range G.n) (hθ : 1 ≤ c.θ) (h1 : RegDisj r (E.LAB, G.n))
    (h2 : RegDisj r (E.LOC, T.N)) (ha1 : r.1 ≤ a) (ha2 : a < r.1 + r.2) :
    ¬ ChildWr T G c E a := by
  intro hw
  unfold RegDisj at h1 h2
  simp only at h1 h2
  rcases ChildWr.cell hT hsub hθ hw with ⟨v, hv, rfl⟩ | ⟨x, hx, rfl⟩ <;> omega

/-- **A cell of `ChildWr` of a child is one of its parent.** -/
theorem childWr_mono (hT : T.Ok G) {c c' : Cl} {E : GlobL} {a : ℕ} (hsub : c'.X ⊆ c.X)
    (hXn : c.X ⊆ Finset.range G.n) (hθ : c'.θ ≤ c.θ) (hθ1 : 1 ≤ c'.θ)
    (hw : ChildWr T G c' E a) : ChildWr T G c E a := by
  rcases hw with ⟨v, hv, rfl⟩ | ⟨v, hv, k, hvk, hk, rfl⟩
  · exact Or.inl ⟨v, hsub hv, rfl⟩
  · refine Or.inr ⟨v, hsub hv, k, hvk, hk.trans ?_, rfl⟩
    have hvn := Finset.mem_range.mp (hXn (hsub hv))
    have ht := KT.isTop_top hT hvn hθ1
    exact KT.under_top hT hvn (by omega) ht.1 (by have := ht.2.1; omega)

/-- **A child does not write what another child reads**: the label of one of its vertices and
the local index of the head of its node. -/
theorem childWr_disj (hT : T.Ok G) {c1 c2 : Cl} {E : GlobL} (hs1 : T.Sat G c1.θ c1.X)
    (hs2 : T.Sat G c2.θ c2.X) (hsub1 : c1.X ⊆ Finset.range G.n) (hsub2 : c2.X ⊆ Finset.range G.n)
    (_hθ1 : 1 ≤ c1.θ) (hθ2 : 1 ≤ c2.θ) (hdisj : ∀ z ∈ c1.X, z ∉ c2.X)
    (hll : E.LAB + G.n ≤ E.LOC ∨ E.LOC + T.N ≤ E.LAB) {v : ℕ} (hv : v ∈ c2.X) :
    ¬ ChildWr T G c1 E (E.LAB + v) ∧ ¬ ChildWr T G c1 E (E.LOC + T.hd G (T.top c2.θ v)) := by
  have hvn := Finset.mem_range.mp (hsub2 hv)
  have htop := KT.top_lt_N hT hvn hθ2
  have hhd := (KT.hd_under hT _ htop).lt_N hT htop
  constructor
  · intro hw
    rcases hw with ⟨v'', hv'', he'⟩ | ⟨v'', hv'', k, hvk, -, he'⟩
    · have : v = v'' := by omega
      subst this; exact hdisj v hv'' hv
    · have hv''n := Finset.mem_range.mp (hsub1 hv'')
      have hkN : k < T.N := hvk.lt_N hT (by have := hT.n_lt; omega)
      have := (KT.hd_under hT k hkN).lt_N hT hkN
      omega
  · intro hw
    rcases hw with ⟨v', hv', he⟩ | ⟨v', hv', k, hvk, hk, he⟩
    · have := Finset.mem_range.mp (hsub1 hv'); omega
    · have hv'n := Finset.mem_range.mp (hsub1 hv')
      have hkN : k < T.N := hvk.lt_N hT (by have := hT.n_lt; omega)
      have heq : T.hd G (T.top c2.θ v) = T.hd G k := by omega
      have ht2 := KT.isTop_top hT hvn hθ2
      rcases KT.hd_eq hT htop hkN heq with hu | hu
      · exact hdisj v (hs1 v' hv' v hvn (ht2.1.trans (hu.trans hk))) hv
      · exact hdisj v' hv' (hs2 v hv v' hv'n (hvk.trans hu))

end MinCostFlow.LowStretch
