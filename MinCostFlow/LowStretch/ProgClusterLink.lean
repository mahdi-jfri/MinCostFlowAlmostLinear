module

public import MinCostFlow.LowStretch.ProgClusterHw2
public import MinCostFlow.LowStretch.PLink
public import MinCostFlow.LowStretch.ClRep

/-!
# The petal graph represents the petal metric

A petal search runs on an arc graph `g` of super-vertices. Its arcs are of two kinds:
* *normal arcs*, one for each direction of each stored active pair, with the rounded cost
  `rc θ wbar` of the pair;
* *slot arcs*, from `H[k]` to `H[k+1]` along the highway, with the length of the pair `q_k`.

`plink_of` turns these two kinds into `Cl.PLink`, for the highway `hwB` of `ProgClusterHw`. It
needs that every arc of `g` is of one of the two kinds (soundness), and that every normal arc of
the petal metric of cost at most `Rm` between two super-vertices, and every slot step, is an arc
of `g` (completeness).

A pair that joins two super-vertices and is not active costs at least `2Δ` in the petal metric
(`Rec.Ok.rc_ge`), so the graph needs no arc for it when `Rm < 2Δ`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable {G : PG} {c : Cl}

/-- **The link of the petal graph.** -/
theorem plink_of (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) {t : ℕ} (ht : t ∈ Y)
    (hcl : ∀ a ∈ Y, ∀ b ∈ c.X, c.LConn G a b → b ∈ Y) {sv : ℕ → ℕ}
    (hsv : ∀ a ∈ c.X, ∀ b ∈ c.X, sv a = sv b ↔ c.LConn G a b) {st : List (ℕ × ℕ × ℕ)}
    {hw : List ℕ} (hst : c.HwDec G t st hw) {g : AG} {Rm : ℕ}
    (hsnd : ∀ u v k, (u = sv t ∨ g.ok u) → g.Arc u v k →
      (∃ p a b, a ∈ Y ∧ b ∈ Y ∧ G.Joins p a b ∧ sv a = u ∧ sv b = v ∧
        k = rc c.θ (c.wbar G p a b)) ∨
      (∃ s ∈ st, s.2.1 ∈ Y ∧ s.2.2 ∈ Y ∧ sv s.2.1 = u ∧ sv s.2.2 = v ∧ k = c.len G s.1))
    (hcmpN : ∀ p a b, a ∈ Y → b ∈ Y → G.Joins p a b → ¬ c.LConn G a b →
      rc c.θ (c.wbar G p a b) ≤ Rm → g.Arc (sv a) (sv b) (rc c.θ (c.wbar G p a b)))
    (hcmpH : ∀ s ∈ st, s.2.1 ∈ Y → s.2.2 ∈ Y → g.Arc (sv s.2.1) (sv s.2.2) (c.len G s.1)) :
    c.PLink G t hw Y sv g Rm where
  conn := hc
  hY := hY
  ht := ht
  hcl := hcl
  hsv a ha b hb := (hsv a ha b hb).mp
  snd u v k hu harc := by
    rcases hsnd u v k hu harc with ⟨p, a, b, ha, hb, hj, rfl, rfl, rfl⟩ | ⟨s, hs, ha, hb, rfl, rfl, rfl⟩
    · exact ⟨a, ha, b, hb, rfl, rfl, Arc.normal hj⟩
    · obtain ⟨i, hi, e1, e2, e3⟩ := hst.index hs
      refine ⟨s.2.1, ha, s.2.2, hb, rfl, rfl, ?_⟩
      have := Arc.high (G := G) (c := c) (t := t) (hw := hw) hi
      unfold hv at this
      rw [e1, e2, e3] at this
      exact this
  cmp a ha b hb k harc hk := by
    cases harc with
    | @normal p _ _ hj =>
      by_cases hl : c.LConn G a b
      · exact Or.inl ((hsv a (hY ha) b (hY hb)).mpr hl)
      · exact Or.inr (hcmpN p a b ha hb hj hl hk)
    | @high i hi =>
      rcases (hst.steps hc hi).2 with hl | hm
      · exact Or.inl ((hsv _ (hY ha) _ (hY hb)).mpr hl)
      · exact Or.inr (hcmpH _ hm ha hb)

/-- Light-joined vertices have the same distance to the center. -/
theorem d_lconn (hc : c.Conn G) {a b : ℕ} (h : c.LConn G a b) : c.d G c.x0 a = c.d G c.x0 b := by
  obtain ⟨ps, hw⟩ := h
  induction hw with
  | nil _ => rfl
  | @cons x y z p ps hx hp hj rest ih =>
    have := d_light hc hp hj hx rest.start_mem
    have h0 : c.len G p = 0 := c.len_eq_zero_of_light hp
    omega

/-- The entry of a step list: `e`, then the far end of each step. -/
def stEnt (e : ℕ) (st : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℕ := (e :: st.map (·.2.2)).getD i 0

/-- The length of the first `i` steps. -/
noncomputable def hcL (G : PG) (c : Cl) (st : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℕ :=
  ((st.take i).map (fun s => c.len G s.1)).sum

/-- Along the steps, the distance drops by the length of the steps. -/
theorem StOk.d_ent (hc : c.Conn G) {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st) {i : ℕ}
    (hi : i ≤ st.length) : c.d G c.x0 e = c.d G c.x0 (stEnt e st i) + hcL G c st i := by
  induction h generalizing i with
  | nil _ =>
    simp only [List.length_nil, Nat.le_zero] at hi
    subst hi; simp [stEnt, hcL]
  | @cons e s st hl hj hb hd hst ih =>
    cases i with
    | zero => simp [stEnt, hcL]
    | succ i =>
      have h1 := ih (i := i) (by simp at hi; omega)
      have h2 := d_lconn hc hl
      simp only [stEnt, hcL, List.map_cons, List.getD_cons_succ, List.take_succ_cons,
        List.sum_cons] at h1 ⊢
      cases i with
      | zero => simp only [List.getD_cons_zero, List.take_zero, List.map_nil, List.sum_nil] at h1 ⊢; omega
      | succ i => simp only [List.getD_cons_succ] at h1 ⊢; omega

/-- The entries lie in `X`. -/
theorem StOk.ent_mem {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st) {i : ℕ}
    (hi : i ≤ st.length) : stEnt e st i ∈ c.X := by
  induction h generalizing i with
  | nil hl => simp only [List.length_nil, Nat.le_zero] at hi; subst hi; exact (lw_walk hl).start_mem
  | @cons e s st hl hj hb hd hst ih =>
    cases i with
    | zero => exact (lw_walk hl).start_mem
    | succ i =>
      have := ih (i := i) (by simp at hi; omega)
      simp only [stEnt, List.map_cons, List.getD_cons_succ] at this ⊢
      cases i with
      | zero => simpa using hb
      | succ i => simpa using this

/-- Step `k` starts in the super-vertex of entry `k`. -/
theorem StOk.lconn_ent {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st) {k : ℕ}
    (hk : k < st.length) : c.LConn G (stEnt e st k) (st.getD k (0, 0, 0)).2.1 := by
  induction h generalizing k with
  | nil _ => simp at hk
  | @cons e s st hl hj hb hd hst ih =>
    cases k with
    | zero => simpa [stEnt] using hl
    | succ k =>
      have := ih (k := k) (by simp at hk; omega)
      simp only [stEnt, List.map_cons, List.getD_cons_succ] at this ⊢
      cases k with
      | zero =>
        cases hst with
        | nil _ => simp at hk
        | cons hl' _ _ _ _ => simpa using hl'
      | succ k => simpa using this

/-- **The highway costs.** If the slot steps are arcs of `g` and `g` is sound for the petal metric,
then the cost of the first `i` steps is the distance in `g` from the source to the super-vertex
of entry `i`. -/
theorem hc_of {Y : Finset ℕ} {t : ℕ} {sv : ℕ → ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ} {g : AG}
    {Rm : ℕ} (hc : c.Conn G) (hst : c.HwDec G t st hw) (hL : c.PLink G t hw Y sv g Rm)
    (hsv : ∀ a ∈ c.X, ∀ b ∈ c.X, sv a = sv b ↔ c.LConn G a b)
    (hentY : ∀ i ≤ st.length, stEnt t st i ∈ Y)
    (harc : ∀ k < st.length, g.Arc (sv (stEnt t st k)) (sv (stEnt t st (k + 1)))
      (c.len G (st.getD k (0, 0, 0)).1)) {i : ℕ} (hi : i ≤ st.length) :
    g.Reach (sv t) (sv (stEnt t st i)) (hcL G c st i) ∧
      ∀ k, g.Reach (sv t) (sv (stEnt t st i)) k → hcL G c st i ≤ k := by
  refine ⟨?_, fun k hk => ?_⟩
  · induction i with
    | zero => simpa [stEnt, hcL] using AG.Reach.refl
    | succ i ih =>
      have h1 := ih (by omega)
      have h2 := harc i (by omega)
      have e : hcL G c st (i + 1) = hcL G c st i + c.len G (st.getD i (0, 0, 0)).1 := by
        simp only [hcL]
        rw [List.take_succ, List.map_append, List.sum_append]
        rw [List.getElem?_eq_getElem (by omega)]
        simp [List.getElem?_eq_getElem (show i < st.length by omega)]
      rw [e]
      exact AG.Reach.step h1 h2
  · have hD := reach_sound hL.conn hL.hY hL.hcl hL.hsv hL.snd hL.ht hk (stEnt t st i) (hentY i hi) rfl
    have hp := potential hc (Y := ↑Y) (fun x hx => hL.hY (by simpa using hx)) (hst.highway hc) hD
    have := hst.stOk.d_ent hc hi
    omega

end Cl

namespace Rec

variable {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec}

/-- **A pair that is not active costs at least `2Δ`.** If it joins two super-vertices of the
cluster and is not active, its weight is more than `4Δ`, so its length is at least `2Δ` and its
shifted length at least `Δ`. -/
theorem Ok.rc_ge (h : R.Ok T G P c) {p a b : ℕ} (hj : G.Joins p a b) (ha : a ∈ c.X)
    (hb : b ∈ c.X) (hnl : ¬ c.LConn G a b) (hna : p ∉ c.act G P) :
    2 * c.Δ G ≤ rc c.θ (c.wbar G p a b) := by
  have hθ := h.not_light hj ha hb hnl
  have hlen := Cl.half_le_len (c := c) (G := G) hθ
  obtain ⟨hm, hj'⟩ := hj
  have hnl' : ¬ c.LConn G (G.pu p) (G.pv p) := by
    rcases hj' with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; exact hnl
    · rw [e1, e2]; rintro ⟨ps, hps⟩; exact hnl ⟨ps.reverse, hps.reverse⟩
  have hu : G.pu p ∈ c.X := by rcases hj' with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rw [e1] <;> assumption
  have hv : G.pv p ∈ c.X := by rcases hj' with ⟨-, e2⟩ | ⟨-, e2⟩ <;> rw [e2] <;> assumption
  have h4 := h.heavy4 hm hu hv hnl' hna
  have hdb := Cl.d_le_Δ (G := G) (c := c) hb
  have hr := le_rc c.θ (c.wbar G p a b)
  have hw : c.d G c.x0 a + c.len G p ≤ c.wbar G p a b + c.d G c.x0 b := by
    unfold Cl.wbar; omega
  omega

end Rec

end MinCostFlow.LowStretch
