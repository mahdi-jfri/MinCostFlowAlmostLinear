module

public import MinCostFlow.LowStretch.ProgChildSpec
public import MinCostFlow.LowStretch.Volume

/-!
# The records of the children, in mathematics

The child step builds a record for each child of a cluster `c`. This file shows that the records
it builds meet `Rec.Ok`.
* The pieces of a step are unions of `θ`-nodes (`Cl.sat_raw`), since petals contain whole
  `θ`-nodes.
* A child that keeps the threshold (`Rec.ok_raw`): its super-vertices are the `θ`-nodes of its
  vertices, and its stored pairs are the active pairs of `c` with both ends in it. Every active
  pair of the child is one of them, since the radius only shrinks and light connections are the
  same in `c` and in the child.
* A reset child (`Rec.ok_reset`): its super-vertices are the `x`-nodes of its vertices for the new
  threshold `x`, and its stored pairs are the pairs above, together with the pairs whose lowest
  common node is split (`KT.splitSet`). An active pair of the reset child that is light in `c`
  has its lowest common node split: its ends lie in one `θ`-node but in two `x`-nodes.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open KT

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {D : Cl.Dec}

namespace Cl

/-- What is left before each petal is a union of `θ`-nodes. -/
theorem sat_Z (h : R.Ok T G P c) (k : ℕ) : T.Sat G c.θ (c.Z G D k) := by
  induction k with
  | zero => exact h.sat
  | succ k ih =>
    rw [Z_succ]
    exact Sat.diff h.tree h.hG h.inv.good.conn (Z_subset_X D k) h.sub h.inv.one_le ih _

/-- **The pieces are unions of `θ`-nodes.** -/
theorem sat_raw (h : R.Ok T G P c) (k : ℕ) : T.Sat G c.θ (c.raw G D k).X := by
  cases k with
  | zero => rw [raw0_X]; exact sat_Z h _
  | succ k =>
    exact Sat.carve h.tree h.hG h.inv.good.conn (Z_subset_X D k) h.sub h.inv.one_le (sat_Z h k) _

end Cl

namespace Rec

/-- Light connections in a piece are those of the cluster. -/
theorem Ok.lconn_raw (h : R.Ok T G P c) (k : ℕ) {a b : ℕ} (ha : a ∈ (c.raw G D k).X)
    (hb : b ∈ (c.raw G D k).X) : (c.raw G D k).LConn G a b ↔ c.LConn G a b := by
  have hsub := Cl.raw_X_subset (G := G) (c := c) (D := D) k
  have hsat : T.Sat G (c.raw G D k).θ (c.raw G D k).X := by rw [Cl.raw_θ]; exact Cl.sat_raw h k
  rw [Cl.lconn_iff h.tree h.hG hsat (hsub.trans h.sub)
      (by rw [Cl.raw_θ]; exact h.inv.one_le) ha hb,
    Cl.lconn_iff h.tree h.hG h.sat h.sub h.inv.one_le (hsub ha) (hsub hb), Cl.raw_θ]

/-- **The record of a child that keeps the threshold.** Its super-vertices are the `θ`-nodes of
its vertices, its stored pairs are the active pairs of `c` inside it, with the half flags of the
child, and its highway is the highway of the child without light pairs. -/
theorem ok_raw (h : R.Ok T G P c) (hD : c.DecOk G P D) {k : ℕ}
    (hk : k < D.nch) (hinv : (c.raw G D k).Inv G P) {R' : Rec} (hnd : R'.nodes.Nodup)
    (hnodes : ∀ j, j ∈ R'.nodes ↔ ∃ a ∈ (c.raw G D k).X, T.top c.θ a = j)
    (hSnd : (R'.S.map Prod.fst).Nodup)
    (hS : ∀ e ∈ R'.S, e.2 = if e.1 ∈ (c.raw G D k).half then 1 else 0)
    (hSm : ∀ p, p ∈ R'.S.map Prod.fst ↔
      p ∈ c.act G P ∧ G.pu p ∈ (c.raw G D k).X ∧ G.pv p ∈ (c.raw G D k).X)
    (hhw : R'.hwc = (c.raw G D k).hw.filter (fun p => c.θ ≤ G.pω p)) :
    R'.Ok T G P (c.raw G D k) := by
  have hθ : (c.raw G D k).θ = c.θ := Cl.raw_θ k
  have hsub := Cl.raw_X_subset (G := G) (c := c) (D := D) k
  have hsat := Cl.sat_raw (D := D) h k
  have hN := h.tree.n_lt
  refine ⟨hinv, h.tree, h.hG, h.hGo, h.hB, h.hQ, hnd, fun j hj => ?_, fun j hj v hv hu => ?_,
    fun v => ?_, fun e he => ?_, hSnd, fun p hp => ?_, by rw [hhw, hθ]⟩
  · obtain ⟨a, ha, rfl⟩ := (hnodes j).mp hj
    exact top_lt_N h.tree (h.n_of_mem (hsub ha)) h.inv.one_le
  · obtain ⟨a, ha, rfl⟩ := (hnodes j).mp hj
    have han := h.n_of_mem (hsub ha)
    rw [hθ]
    exact ((IsTop.of_common h.tree (by omega) (isTop_top h.tree han h.inv.one_le)
      (isTop_top h.tree han h.inv.one_le).1 hu
      (isTop_top h.tree han h.inv.one_le).2.1).eq_top h.tree hv h.inv.one_le).symm
  · rw [hθ]
    constructor
    · intro hv
      exact ⟨h.n_of_mem (hsub hv), (hnodes _).mpr ⟨v, hv, rfl⟩⟩
    · rintro ⟨hv, hm⟩
      obtain ⟨a, ha, he⟩ := (hnodes _).mp hm
      exact hsat a ha v hv (by rw [he]; exact (isTop_top h.tree hv h.inv.one_le).1)
  · have hp : e.1 ∈ R'.S.map Prod.fst := List.mem_map.mpr ⟨e, he, rfl⟩
    obtain ⟨hpa, hu, hv⟩ := (hSm _).mp hp
    obtain ⟨hm, hu', hv', hnl, -⟩ := Cl.mem_act.mp hpa
    have hf := hS e he
    refine ⟨hm, hu, hv, ?_, by rw [hf]; split_ifs <;> omega, by rw [hf]; split_ifs <;> simp_all⟩
    rw [hθ]
    intro he'
    exact hnl ((Cl.lconn_iff h.tree h.hG h.sat h.sub h.inv.one_le hu' hv').mpr he')
  · obtain ⟨hm, hu, hv, hnl, hω⟩ := Cl.mem_act.mp hp
    refine (hSm p).mpr ⟨Cl.mem_act.mpr ⟨hm, hsub hu, hsub hv, fun hl => hnl
      ((h.lconn_raw k hu hv).mpr hl), ?_⟩, hu, hv⟩
    have h1 := Cl.raw_Δ h.inv.good hD h.hGo hk
    rw [hθ] at hω
    calc G.pω p ^ 2 ≤ P.Q * ((c.raw G D k).Δ G * c.θ) := hω
      _ ≤ P.Q * (c.Δ G * c.θ) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))

/-- **The record of a reset child.** The child `r.reset x` of the piece `r` has as super-vertices
the `x`-nodes of its vertices. Its stored pairs are the active pairs of `c` inside it and the
pairs whose lowest common node `lf p` is split, all with flag `0`; its highway is empty. -/
theorem ok_reset (h : R.Ok T G P c) (hX : 2 ≤ c.X.card) (hD : c.DecOk G P D) {k : ℕ}
    (hk : k < D.nch) {x : ℕ} (hn : Next G P (c.raw G D k) ((c.raw G D k).reset x))
    (hx1 : 1 ≤ x) (hxθ : x ≤ c.θ) {lf : ℕ → ℕ}
    (hlf : ∀ p < G.m, T.IsLca (G.pu p) (G.pv p) (lf p)) {R' : Rec} (hnd : R'.nodes.Nodup)
    (hnodes : ∀ j, j ∈ R'.nodes ↔ ∃ a ∈ (c.raw G D k).X, T.top x a = j)
    (hSnd : (R'.S.map Prod.fst).Nodup) (hS : ∀ e ∈ R'.S, e.2 = 0)
    (hSm : ∀ p, p ∈ R'.S.map Prod.fst ↔
      (p ∈ c.act G P ∧ G.pu p ∈ (c.raw G D k).X ∧ G.pv p ∈ (c.raw G D k).X) ∨
        (p < G.m ∧ lf p ∈ T.splitSet G (c.raw G D k) x))
    (hhw : R'.hwc = []) : R'.Ok T G P ((c.raw G D k).reset x) := by
  set r := c.raw G D k with hr
  have hθ : r.θ = c.θ := Cl.raw_θ k
  have hsub : r.X ⊆ c.X := Cl.raw_X_subset (G := G) (c := c) (D := D) k
  have hsatθ : T.Sat G c.θ r.X := Cl.sat_raw (D := D) h k
  have hsat : T.Sat G x r.X := hsatθ.mono h.tree (hsub.trans h.sub) hx1 hxθ
  have hN := h.tree.n_lt
  have hinv : (r.reset x).Inv G P := Cl.child_inv h.hGo h.hB h.inv hX hD hk hn
  have hrX : (r.reset x).X = r.X := rfl
  have hrθ : (r.reset x).θ = x := rfl
  have hsat' : T.Sat G (r.reset x).θ (r.reset x).X := hsat
  have hsub' : (r.reset x).X ⊆ Finset.range G.n := hsub.trans h.sub
  -- light connections at `x` imply light connections in `c`
  have hl : ∀ {a b}, a ∈ r.X → b ∈ r.X → T.top x a = T.top x b → c.LConn G a b := by
    intro a b ha hb he
    obtain ⟨ps, hps⟩ := (Cl.lconn_iff (c := r.reset x) h.tree h.hG hsat' hsub' hx1 ha hb).mpr he
    exact ⟨ps, hps.mono (fun z hz => hsub hz) fun q hq => lt_of_lt_of_le hq hxθ⟩
  refine ⟨hinv, h.tree, h.hG, h.hGo, h.hB, h.hQ, hnd, fun j hj => ?_, fun j hj v hv hu => ?_,
    fun v => ?_, fun e he => ?_, hSnd, fun p hp => ?_, by rw [hhw]; rfl⟩
  · obtain ⟨a, ha, rfl⟩ := (hnodes j).mp hj
    exact top_lt_N h.tree (h.n_of_mem (hsub ha)) hx1
  · obtain ⟨a, ha, rfl⟩ := (hnodes j).mp hj
    have han := h.n_of_mem (hsub ha)
    rw [hrθ]
    exact ((IsTop.of_common h.tree (by omega) (isTop_top h.tree han hx1)
      (isTop_top h.tree han hx1).1 hu (isTop_top h.tree han hx1).2.1).eq_top h.tree hv hx1).symm
  · rw [hrθ, hrX]
    constructor
    · intro hv
      exact ⟨h.n_of_mem (hsub hv), (hnodes _).mpr ⟨v, hv, rfl⟩⟩
    · rintro ⟨hv, hm⟩
      obtain ⟨a, ha, he⟩ := (hnodes _).mp hm
      exact hsat a ha v hv (by rw [he]; exact (isTop_top h.tree hv hx1).1)
  · have hp : e.1 ∈ R'.S.map Prod.fst := List.mem_map.mpr ⟨e, he, rfl⟩
    have hf := hS e he
    have hhalf : (r.reset x).half = ∅ := rfl
    rw [hrX, hrθ, hhalf, hf]
    rcases (hSm _).mp hp with ⟨hpa, hu, hv⟩ | ⟨hm, hsp⟩
    · obtain ⟨hm, hu', hv', hnl, -⟩ := Cl.mem_act.mp hpa
      exact ⟨hm, hu, hv, fun he' => hnl (hl hu hv he'), by omega, by simp⟩
    · obtain ⟨hpu, hpv⟩ := h.hG _ hm
      unfold KT.splitSet at hsp
      simp only [Finset.mem_filter, Finset.mem_range] at hsp
      obtain ⟨huN, -, hxu, a, ha, hau, hut⟩ := hsp
      obtain ⟨h1, h2, -⟩ := hlf _ hm
      have hin : ∀ z, z < G.n → T.Under z (lf e.1) → z ∈ r.X := fun z hz hzu =>
        hsatθ a ha z hz (by rw [← hθ]; exact hzu.trans hut)
      refine ⟨hm, hin _ hpu h1, hin _ hpv h2, fun he' => ?_, by omega, by simp⟩
      have ht := isTop_top h.tree hpu hx1
      have ht' : T.IsTop x (G.pv e.1) (T.top x (G.pu e.1)) := by
        rw [he']; exact isTop_top h.tree hpv hx1
      have := (hlf _ hm).2.2 _ ht.1 ht'.1
      have h4 := this.mw_le h.tree huN
      have h5 := ht.2.1
      have h6 : (r.reset x).θ = x := rfl
      omega
  · obtain ⟨hm, hu, hv, hnl, hω⟩ := Cl.mem_act.mp hp
    rw [hrX] at hu hv
    have hnl' : ¬ T.top x (G.pu p) = T.top x (G.pv p) := fun he =>
      hnl ((Cl.lconn_iff (c := r.reset x) h.tree h.hG hsat' hsub' hx1 hu hv).mpr he)
    by_cases hlc : c.LConn G (G.pu p) (G.pv p)
    · refine (hSm p).mpr (Or.inr ⟨hm, ?_⟩)
      have hte := (Cl.lconn_iff h.tree h.hG h.sat h.sub h.inv.one_le (hsub hu) (hsub hv)).mp hlc
      obtain ⟨hpu, hpv⟩ := h.hG _ hm
      obtain ⟨h1, h2, h3⟩ := hlf _ hm
      have huN : lf p < T.N := h1.lt_N h.tree (by omega)
      have hut : T.Under (lf p) (T.top c.θ (G.pu p)) :=
        h3 _ (isTop_top h.tree hpu h.inv.one_le).1
          (by rw [hte]; exact (isTop_top h.tree hpv h.inv.one_le).1)
      have hxu : x ≤ T.mw (lf p) := by
        by_contra hc
        push Not at hc
        apply hnl'
        exact (IsTop.of_common h.tree (by omega) (isTop_top h.tree hpu hx1) h1 h2 hc).eq_top
          h.tree hpv hx1
      have hnu : G.n ≤ lf p := by
        by_contra hc
        push Not at hc
        have e1 := under_leaf h.tree (by omega) hc h1
        have e2 := under_leaf h.tree (by omega) hc h2
        exact (h.hGo p hm).2.2.1 (e1.trans e2.symm)
      unfold KT.splitSet
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨huN, hnu, hxu, G.pu p, hu, h1, by rw [← hθ] at hut; exact hut⟩
    · refine (hSm p).mpr (Or.inl ⟨Cl.mem_act.mpr ⟨hm, hsub hu, hsub hv, hlc, ?_⟩, hu, hv⟩)
      have h1 := Cl.psi_child h.hGo h.hB h.inv hX hD hk hn
      rw [hrθ] at hω
      calc G.pω p ^ 2 ≤ P.Q * ((r.reset x).Δ G * x) := hω
        _ ≤ P.Q * (c.Δ G * c.θ) := Nat.mul_le_mul_left _ (by rw [hrθ] at h1; omega)

/-- **Active pairs are not grouped at split nodes.** An active pair of `c` joins two `θ`-nodes,
so its lowest common node lies above a `θ`-node, while the split nodes of a piece lie below
one. -/
theorem Ok.lca_not_split (h : R.Ok T G P c) {p : ℕ} (hp : p ∈ c.act G P) {l : ℕ}
    (hl : T.IsLca (G.pu p) (G.pv p) l) (k x : ℕ) : l ∉ T.splitSet G (c.raw G D k) x := by
  intro hs
  obtain ⟨-, hu, hv, hnl, -⟩ := Cl.mem_act.mp hp
  simp only [KT.splitSet, Finset.mem_filter, Cl.raw_θ] at hs
  obtain ⟨-, -, -, v, hvX, -, hlt⟩ := hs
  have hvn : v < G.n := h.n_of_mem (Cl.raw_X_subset k hvX)
  have hN := h.tree.n_lt
  have ht := isTop_top h.tree hvn h.inv.one_le
  have hu' : T.IsTop c.θ (G.pu p) (T.top c.θ v) :=
    IsTop.of_common h.tree (by omega) ht ht.1 (hl.1.trans hlt) ht.2.1
  have hv' : T.IsTop c.θ (G.pv p) (T.top c.θ v) :=
    IsTop.of_common h.tree (by omega) ht ht.1 (hl.2.1.trans hlt) ht.2.1
  apply hnl
  rw [Cl.lconn_iff h.tree h.hG h.sat h.sub h.inv.one_le hu hv,
    ← hu'.eq_top h.tree (h.n_of_mem hu) h.inv.one_le,
    ← hv'.eq_top h.tree (h.n_of_mem hv) h.inv.one_le]

end Rec

end MinCostFlow.LowStretch
