module

public import MinCostFlow.Expander.GraphHelpers
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card

/-!
# Connected components and simple path search

Computable connected-component labeling (`compLabels`) via label relaxation and computable
simple-path search (`findSimplePath`) via layer relaxation, over `MinCostFlow.Cited.Graph`.
-/

public section

namespace MinCostFlow.Expander

open MinCostFlow.Cited

/-! ### Connected components via label relaxation (`compLabels`) -/

def relaxEdge (lbl : List ℕ) (e : ℕ × ℕ) : List ℕ :=
  if e.1 < lbl.length ∧ e.2 < lbl.length then
    let m := min (lbl.getD e.1 0) (lbl.getD e.2 0)
    (lbl.set e.1 m).set e.2 m
  else lbl

def relaxPass (edges : List (ℕ × ℕ)) (lbl : List ℕ) : List ℕ :=
  edges.foldl relaxEdge lbl

def compLabels (G : Graph) : List ℕ :=
  (relaxPass G.edges)^[G.n] (List.range G.n)

lemma relaxEdge_length (lbl : List ℕ) (e : ℕ × ℕ) :
    (relaxEdge lbl e).length = lbl.length := by
  unfold relaxEdge
  split_ifs <;> simp

lemma relaxPass_length (edges : List (ℕ × ℕ)) (lbl : List ℕ) :
    (relaxPass edges lbl).length = lbl.length := by
  unfold relaxPass
  induction edges generalizing lbl with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih, relaxEdge_length]

lemma compLabels_length (G : Graph) : (compLabels G).length = G.n := by
  unfold compLabels
  have h : ∀ k (lbl : List ℕ), lbl.length = G.n → ((relaxPass G.edges)^[k] lbl).length = G.n := by
    intro k
    induction k with
    | zero => intro lbl hl; simpa using hl
    | succ k ih =>
      intro lbl hl
      rw [Function.iterate_succ_apply']
      rw [relaxPass_length]
      exact ih lbl hl
  exact h G.n (List.range G.n) (List.length_range)

private lemma getD_set_eq_of_lt {l : List ℕ} {i v : ℕ} (hi : i < l.length) :
    (l.set i v).getD i 0 = v := by
  simp [List.getD, List.getElem?_set_self hi]

private lemma getD_set_ne {l : List ℕ} {i j v : ℕ} (hne : i ≠ j) :
    (l.set i v).getD j 0 = l.getD j 0 := by
  simp [List.getD, List.getElem?_set_ne hne]

private lemma relaxEdge_getD_le (lbl : List ℕ) (e : ℕ × ℕ) (x : ℕ) :
    (relaxEdge lbl e).getD x 0 ≤ lbl.getD x 0 := by
  unfold relaxEdge
  split_ifs with h
  · by_cases hx2 : x = e.2
    · subst hx2
      rw [getD_set_eq_of_lt (by simpa using h.2)]
      exact min_le_right _ _
    · rw [getD_set_ne (Ne.symm hx2)]
      by_cases hx1 : x = e.1
      · subst hx1
        rw [getD_set_eq_of_lt h.1]
        exact min_le_left _ _
      · rw [getD_set_ne (Ne.symm hx1)]
  · exact le_rfl

private lemma relaxEdge_getD_endpoints {lbl : List ℕ} {e : ℕ × ℕ}
    (h1 : e.1 < lbl.length) (h2 : e.2 < lbl.length) :
    (relaxEdge lbl e).getD e.1 0 ≤ lbl.getD e.2 0 ∧
      (relaxEdge lbl e).getD e.2 0 ≤ lbl.getD e.1 0 := by
  unfold relaxEdge
  simp only [h1, h2, and_self, ↓reduceIte]
  constructor
  · by_cases heq : e.1 = e.2
    · rw [heq, getD_set_eq_of_lt (by simpa using h2)]
      exact min_le_right _ _
    · rw [getD_set_ne (Ne.symm heq), getD_set_eq_of_lt h1]
      exact min_le_right _ _
  · rw [getD_set_eq_of_lt (by simpa using h2)]
    exact min_le_left _ _

private lemma relaxPass_getD_le (edges : List (ℕ × ℕ)) (lbl : List ℕ) (x : ℕ) :
    (relaxPass edges lbl).getD x 0 ≤ lbl.getD x 0 := by
  unfold relaxPass
  induction edges generalizing lbl with
  | nil => exact le_rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih _) (relaxEdge_getD_le lbl e x)

private lemma relaxPass_getD_edge_le {edges : List (ℕ × ℕ)} {lbl : List ℕ}
    {a b : ℕ} (hab : (a, b) ∈ edges) (ha : a < lbl.length) (hb : b < lbl.length) :
    (relaxPass edges lbl).getD a 0 ≤ lbl.getD b 0 ∧
      (relaxPass edges lbl).getD b 0 ≤ lbl.getD a 0 := by
  unfold relaxPass
  induction edges generalizing lbl with
  | nil => cases hab
  | cons e es ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hab with rfl | hes
    · have hstep := relaxEdge_getD_endpoints (e := (a, b)) ha hb
      have hm1 : (es.foldl relaxEdge (relaxEdge lbl (a, b))).getD a 0 ≤ (relaxEdge lbl (a, b)).getD a 0 :=
        relaxPass_getD_le es (relaxEdge lbl (a, b)) a
      have hm2 : (es.foldl relaxEdge (relaxEdge lbl (a, b))).getD b 0 ≤ (relaxEdge lbl (a, b)).getD b 0 :=
        relaxPass_getD_le es (relaxEdge lbl (a, b)) b
      exact ⟨le_trans hm1 hstep.1, le_trans hm2 hstep.2⟩
    · have ha' : a < (relaxEdge lbl e).length := by rw [relaxEdge_length]; exact ha
      have hb' : b < (relaxEdge lbl e).length := by rw [relaxEdge_length]; exact hb
      have hrec := ih hes ha' hb'
      exact ⟨le_trans hrec.1 (relaxEdge_getD_le lbl e b), le_trans hrec.2 (relaxEdge_getD_le lbl e a)⟩

private lemma relaxEdge_reachable {G : Graph} {lbl : List ℕ} {e : ℕ × ℕ} (he : e ∈ G.edges)
    (hinv : ∀ x < lbl.length, ∃ P, IsPathAlong G.edges x (lbl.getD x 0) P) :
    ∀ x < (relaxEdge lbl e).length, ∃ P, IsPathAlong G.edges x ((relaxEdge lbl e).getD x 0) P := by
  rw [relaxEdge_length]
  intro x hx
  unfold relaxEdge
  split_ifs with h
  · by_cases hx2 : x = e.2
    · subst hx2
      rw [getD_set_eq_of_lt (by simpa using h.2)]
      rcases min_cases (lbl.getD e.1 0) (lbl.getD e.2 0) with ⟨hm, _⟩ | ⟨hm, _⟩
      · rw [hm]
        obtain ⟨P, hP⟩ := hinv e.1 h.1
        exact ⟨e.2 :: P, isPathAlong_cons (Or.inr he) hP⟩
      · rw [hm]
        exact hinv e.2 h.2
    · rw [getD_set_ne (Ne.symm hx2)]
      by_cases hx1 : x = e.1
      · subst hx1
        rw [getD_set_eq_of_lt h.1]
        rcases min_cases (lbl.getD e.1 0) (lbl.getD e.2 0) with ⟨hm, _⟩ | ⟨hm, _⟩
        · rw [hm]
          exact hinv e.1 h.1
        · rw [hm]
          obtain ⟨P, hP⟩ := hinv e.2 h.2
          exact ⟨e.1 :: P, isPathAlong_cons (Or.inl he) hP⟩
      · rw [getD_set_ne (Ne.symm hx1)]
        exact hinv x hx
  · exact hinv x hx

private lemma compLabels_reachable (G : Graph) (k x : ℕ) (hx : x < G.n) :
    ∃ P, IsPathAlong G.edges x (((relaxPass G.edges)^[k] (List.range G.n)).getD x 0) P := by
  induction k generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    have hget : (List.range G.n).getD x 0 = x := by
      simp [List.getD, hx]
    rw [hget]
    exact ⟨[x], isPathAlong_singleton G.edges x⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hpass : ∀ (es : List (ℕ × ℕ)), (∀ e ∈ es, e ∈ G.edges) →
        ∀ (lbl : List ℕ), (∀ z < lbl.length, ∃ P, IsPathAlong G.edges z (lbl.getD z 0) P) →
        ∀ z < (relaxPass es lbl).length, ∃ P, IsPathAlong G.edges z ((relaxPass es lbl).getD z 0) P := by
      intro es hes
      induction es with
      | nil => intro lbl hlbl z hz; exact hlbl z hz
      | cons e es' ih_es =>
        intro lbl hlbl z hz
        unfold relaxPass at hz ⊢
        simp only [List.foldl_cons] at hz ⊢
        exact ih_es (fun a ha => hes a (by simp [ha])) (relaxEdge lbl e)
          (relaxEdge_reachable (hes e (by simp)) hlbl) z hz
    have hlen : ((relaxPass G.edges)^[k] (List.range G.n)).length = G.n := by
      clear ih
      induction k with
      | zero => simp
      | succ j ihj => rw [Function.iterate_succ_apply', relaxPass_length, ihj]
    exact hpass G.edges (fun _ h => h) _ (fun z hz => ih z (hlen ▸ hz)) x (by rw [relaxPass_length, hlen]; exact hx)

private lemma iterate_relaxPass_le_of_path {G : Graph} (hv : G.IsValid)
    {u v : ℕ} (hu : u < G.n) {P : List ℕ} (hP : IsPathAlong G.edges u v P) (k : ℕ)
    (hk : P.length ≤ k + 1) :
    ((relaxPass G.edges)^[k] (List.range G.n)).getD v 0 ≤ u := by
  have hle_step : ∀ j z, ((relaxPass G.edges)^[j + 1] (List.range G.n)).getD z 0 ≤
      ((relaxPass G.edges)^[j] (List.range G.n)).getD z 0 := by
    intro j z
    rw [Function.iterate_succ_apply']
    exact relaxPass_getD_le G.edges _ z
  have hmono : ∀ a b z, a ≤ b →
      ((relaxPass G.edges)^[b] (List.range G.n)).getD z 0 ≤
      ((relaxPass G.edges)^[a] (List.range G.n)).getD z 0 := by
    intro a b z hab
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    clear hab
    induction d with
    | zero => exact le_rfl
    | succ d ihd =>
      rw [← Nat.add_assoc]
      exact le_trans (hle_step (a + d) z) ihd
  have hlen : ∀ j, ((relaxPass G.edges)^[j] (List.range G.n)).length = G.n := by
    intro j
    induction j with
    | zero => simp
    | succ j ihj => rw [Function.iterate_succ_apply', relaxPass_length, ihj]
  suffices hgen : ∀ (P : List ℕ) (u v k : ℕ), u < G.n → IsPathAlong G.edges u v P → P.length ≤ k + 1 →
      ((relaxPass G.edges)^[k] (List.range G.n)).getD v 0 ≤
        ((relaxPass G.edges)^[k - (P.length - 1)] (List.range G.n)).getD u 0 by
    have h1 := hgen P u v k hu hP hk
    have h2 : ((relaxPass G.edges)^[k - (P.length - 1)] (List.range G.n)).getD u 0 ≤
        ((relaxPass G.edges)^[0] (List.range G.n)).getD u 0 :=
      hmono 0 (k - (P.length - 1)) u (Nat.zero_le _)
    have h0 : ((relaxPass G.edges)^[0] (List.range G.n)).getD u 0 = u := by
      simp [List.getD, hu]
    omega
  clear u v k hu hP hk
  intro P
  induction P using List.reverseRecOn with
  | nil => intro u v k _ hP _; simp [IsPathAlong] at hP
  | append_singleton xs w ih =>
    intro u v k hu hP hk
    have hw : v = w := by
      have := hP.2.1
      simp at this
      exact this.symm
    subst v
    cases xs using List.reverseRecOn with
    | nil =>
      simp only [List.nil_append] at hP
      have huv : w = u := by simpa [IsPathAlong] using hP.1
      rw [huv]
      simp
    | append_singleton ys z =>
      have hP1 : IsPathAlong G.edges u z (ys ++ [z]) := by
        rcases hP with ⟨hh, _, hc⟩
        refine ⟨?_, by simp, (List.isChain_append.mp hc).1⟩
        cases ys <;> simpa using hh
      have hzw : (z, w) ∈ G.edges ∨ (w, z) ∈ G.edges := by
        exact (List.isChain_append.mp hP.2.2).2.2 z (by simp) w (by simp)
      have hzn : z < G.n := by
        rcases hzw with h | h
        · exact (hv _ h).1
        · exact (hv _ h).2
      have hwn : w < G.n := by
        rcases hzw with h | h
        · exact (hv _ h).2
        · exact (hv _ h).1
      have hk_pos : 1 ≤ k := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk_pos
      have hk' : (ys ++ [z]).length ≤ k' + 1 := by
        simp only [List.length_append, List.length_singleton] at hk ⊢
        omega
      have ih1 := ih u z k' hu hP1 hk'
      have hstep : ((relaxPass G.edges)^[k' + 1] (List.range G.n)).getD w 0 ≤
          ((relaxPass G.edges)^[k'] (List.range G.n)).getD z 0 := by
        rw [Function.iterate_succ_apply']
        have hzl : z < ((relaxPass G.edges)^[k'] (List.range G.n)).length := by rw [hlen]; exact hzn
        have hwl : w < ((relaxPass G.edges)^[k'] (List.range G.n)).length := by rw [hlen]; exact hwn
        rcases hzw with h | h
        · exact (relaxPass_getD_edge_le h hzl hwl).2
        · exact (relaxPass_getD_edge_le h hwl hzl).1
      have hlen_eq : (k' + 1) - ((ys ++ [z] ++ [w]).length - 1) = k' - ((ys ++ [z]).length - 1) := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [hlen_eq]
      exact le_trans hstep ih1

lemma compLabels_eq_iff_reachable {G : Graph} (hv : G.IsValid) {u v : ℕ}
    (hu : u < G.n) (hv' : v < G.n) :
    (compLabels G).getD u 0 = (compLabels G).getD v 0 ↔
      ∃ P, IsPathAlong G.edges u v P := by
  constructor
  · intro heq
    obtain ⟨Pu, hPu⟩ := compLabels_reachable G G.n u hu
    obtain ⟨Pv, hPv⟩ := compLabels_reachable G G.n v hv'
    change IsPathAlong G.edges u ((compLabels G).getD u 0) Pu at hPu
    change IsPathAlong G.edges v ((compLabels G).getD v 0) Pv at hPv
    rw [heq] at hPu
    exact ⟨Pu.dropLast ++ Pv.reverse, isPathAlong_append hPu (isPathAlong_reverse hPv)⟩
  · rintro ⟨P, hP⟩
    obtain ⟨Pu, hPu⟩ := compLabels_reachable G G.n u hu
    obtain ⟨Pv, hPv⟩ := compLabels_reachable G G.n v hv'
    change IsPathAlong G.edges u ((compLabels G).getD u 0) Pu at hPu
    change IsPathAlong G.edges v ((compLabels G).getD v 0) Pv at hPv
    have h_v_to_lblu : IsPathAlong G.edges v ((compLabels G).getD u 0) ((P.reverse).dropLast ++ Pu) :=
      isPathAlong_append (isPathAlong_reverse hP) hPu
    have h_u_to_lblv : IsPathAlong G.edges u ((compLabels G).getD v 0) (P.dropLast ++ Pv) :=
      isPathAlong_append hP hPv
    obtain ⟨Q1, hQ1, hQ1_nd, _, _⟩ := exists_nodup_isPathAlong h_v_to_lblu
    obtain ⟨Q2, hQ2, hQ2_nd, _, _⟩ := exists_nodup_isPathAlong h_u_to_lblv
    have hQ1_sub : ∀ x ∈ Q1, x < G.n :=
      isPathAlong_all_mem_range hv hv' hQ1
    have hQ2_sub : ∀ x ∈ Q2, x < G.n :=
      isPathAlong_all_mem_range hv hu hQ2
    have hQ1_len : Q1.length ≤ G.n := by
      have hsub : Q1 ⊆ List.range G.n := fun x hx => List.mem_range.mpr (hQ1_sub x hx)
      simpa [List.length_range] using hQ1_nd.length_le_of_subset hsub
    have hQ2_len : Q2.length ≤ G.n := by
      have hsub : Q2 ⊆ List.range G.n := fun x hx => List.mem_range.mpr (hQ2_sub x hx)
      simpa [List.length_range] using hQ2_nd.length_le_of_subset hsub
    have hlblu_lt : (compLabels G).getD u 0 < G.n := by
      have := (isPathAlong_mem_endpoints hPu).2
      exact isPathAlong_all_mem_range hv hu hPu _ this
    have hlblv_lt : (compLabels G).getD v 0 < G.n := by
      have := (isPathAlong_mem_endpoints hPv).2
      exact isPathAlong_all_mem_range hv hv' hPv _ this
    have h1 : (compLabels G).getD v 0 ≤ (compLabels G).getD u 0 :=
      iterate_relaxPass_le_of_path hv hlblu_lt (isPathAlong_reverse hQ1) G.n (by rw [List.length_reverse]; omega)
    have h2 : (compLabels G).getD u 0 ≤ (compLabels G).getD v 0 :=
      iterate_relaxPass_le_of_path hv hlblv_lt (isPathAlong_reverse hQ2) G.n (by rw [List.length_reverse]; omega)
    omega

lemma compLabels_eq_of_edge {G : Graph} (hv : G.IsValid) {e : ℕ × ℕ} (he : e ∈ G.edges) :
    (compLabels G).getD e.1 0 = (compLabels G).getD e.2 0 := by
  have h := hv e he
  rw [compLabels_eq_iff_reachable hv h.1 h.2]
  exact ⟨[e.1, e.2], rfl, rfl, List.isChain_cons_cons.mpr ⟨Or.inl he, List.isChain_singleton _⟩⟩

lemma cut_part_compLabels_eq_zero {G : Graph} (hv : G.IsValid) {X : Finset ℕ}
    (hX : X ∈ partsOf G (compLabels G)) : G.cut X = 0 := by
  have hsum := sum_cut_partsOf hv (compLabels G)
  have hzero : (G.edges.filter fun e => decide ((compLabels G).getD e.1 0 ≠ (compLabels G).getD e.2 0)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro e he
    rw [decide_eq_true_iff]
    push Not
    exact compLabels_eq_of_edge hv he
  rw [hzero, mul_zero] at hsum
  exact Finset.sum_eq_zero_iff.mp hsum X hX

lemma cutIn_ge_one_of_part_compLabels {G : Graph} (hv : G.IsValid) {X : Finset ℕ}
    (hX : X ∈ partsOf G (compLabels G)) {S : Finset ℕ}
    (hSX : S ⊆ X) (hSne : S.Nonempty) (hSXne : S ≠ X) :
    1 ≤ G.cutIn X S := by
  by_contra hlt
  have hzero : G.cutIn X S = 0 := by omega
  obtain ⟨u, huS⟩ := hSne
  have hv_exists : ∃ v ∈ X, v ∉ S := by
    by_contra hsub
    push Not at hsub
    exact hSXne (Finset.Subset.antisymm hSX hsub)
  obtain ⟨v, hvX, hvS⟩ := hv_exists
  have hXv : X ⊆ G.verts := partsOf_subset_verts hX
  have huV : u ∈ G.verts := hXv (hSX huS)
  have hvV : v ∈ G.verts := hXv hvX
  have hu_lt : u < G.n := Finset.mem_range.mp huV
  have hv_lt : v < G.n := Finset.mem_range.mp hvV
  have hlbl : (compLabels G).getD u 0 = (compLabels G).getD v 0 := by
    rw [mem_partsOf_iff] at hX
    obtain ⟨w, _, rfl⟩ := hX
    have hu_eq := (Finset.mem_filter.mp (hSX huS)).2
    have hv_eq := (Finset.mem_filter.mp hvX).2
    exact hu_eq.trans hv_eq.symm
  obtain ⟨P, hP⟩ := (compLabels_eq_iff_reachable hv hu_lt hv_lt).mp hlbl
  -- Every vertex in P has the same label as u, hence lies in X!
  have hP_in_X : ∀ z ∈ P, z ∈ X := by
    intro z hz
    have hzn : z < G.n := isPathAlong_all_mem_range hv hu_lt hP z hz
    have hzV : z ∈ G.verts := Finset.mem_range.mpr hzn
    have hPz : ∃ Pz, IsPathAlong G.edges u z Pz := by
      obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hz
      rw [hsplit] at hP
      exact ⟨l₁ ++ [z], isPathAlong_prefix_of_split hP⟩
    have hlblz : (compLabels G).getD u 0 = (compLabels G).getD z 0 :=
      (compLabels_eq_iff_reachable hv hu_lt hzn).mpr hPz
    exact (mem_part_iff_label_eq hX (hSX huS) hzV).mpr hlblz.symm
  -- Now walk along P from u ∈ S to v ∉ S: some edge crosses S!
  have hcross : ∃ a b, ((a, b) ∈ G.edges ∨ (b, a) ∈ G.edges) ∧ a ∈ X ∧ b ∈ X ∧
      (decide (a ∈ S) != decide (b ∈ S)) = true := by
    suffices hwalk : ∀ (P' : List ℕ) (w : ℕ), w ∈ S → IsPathAlong G.edges w v P' →
        ∃ a b, ((a, b) ∈ G.edges ∨ (b, a) ∈ G.edges) ∧ a ∈ X ∧ b ∈ X ∧
          (decide (a ∈ S) != decide (b ∈ S)) = true by
      exact hwalk P u huS hP
    intro P'
    induction P' with
    | nil => intro w _ hP'; simp [IsPathAlong] at hP'
    | cons a t ih =>
      intro w hwS hP'
      rcases hP' with ⟨hh, hl, hc⟩
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst a
      cases t with
      | nil =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hl
        subst hl
        exact False.elim (hvS hwS)
      | cons b bs =>
        rw [List.isChain_cons_cons] at hc
        have haX : w ∈ X := hSX hwS
        have hbX : b ∈ X := by
          have hw_lt : w < G.n := Finset.mem_range.mp (hXv haX)
          have hb_lt : b < G.n := by
            rcases hc.1 with h | h
            · exact (hv _ h).2
            · exact (hv _ h).1
          have hb_reach : ∃ Pb, IsPathAlong G.edges w b Pb :=
            ⟨[w, b], rfl, rfl, List.isChain_cons_cons.mpr ⟨hc.1, List.isChain_singleton _⟩⟩
          have hlblb := (compLabels_eq_iff_reachable hv hw_lt hb_lt).mpr hb_reach
          exact (mem_part_iff_label_eq hX haX (Finset.mem_range.mpr hb_lt)).mpr hlblb.symm
        by_cases hbS : b ∈ S
        · exact ih b hbS ⟨rfl, by simpa [List.getLast?_cons] using hl, hc.2⟩
        · exact ⟨w, b, hc.1, haX, hbX, by simp [hwS, hbS]⟩
  obtain ⟨a, b, hab, haX, hbX, hdiff⟩ := hcross
  have hmem : (∃ e ∈ G.inside X, (decide (e.1 ∈ S) != decide (e.2 ∈ S)) = true) := by
    rcases hab with h | h
    · exact ⟨(a, b), mem_inside_iff.mpr ⟨h, haX, hbX⟩, hdiff⟩
    · refine ⟨(b, a), mem_inside_iff.mpr ⟨h, hbX, haX⟩, ?_⟩
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp_all
  obtain ⟨e, he_in, he_diff⟩ := hmem
  have hpos : 0 < G.cutIn X S := by
    unfold Graph.cutIn
    exact List.length_pos_iff_exists_mem.mpr ⟨e, List.mem_filter.mpr ⟨he_in, he_diff⟩⟩
  omega

/-! ### Computable simple path search (`findSimplePath`) -/

private def expandStep (E : List (ℕ × ℕ)) (n : ℕ) (best : List (Option (List ℕ))) :
    List (Option (List ℕ)) :=
  E.foldl (fun acc e =>
    if _h : e.1 < n ∧ e.2 < n then
      let acc1 :=
        match acc.getD e.1 none, acc.getD e.2 none with
        | some p1, none => acc.set e.2 (some (e.2 :: p1))
        | _, _ => acc
      match acc1.getD e.2 none, acc1.getD e.1 none with
      | some p2, none => acc1.set e.1 (some (e.1 :: p2))
      | _, _ => acc1
    else acc) best

def findSimplePath (E : List (ℕ × ℕ)) (n u v : ℕ) : Option (List ℕ) :=
  if u < n ∧ v < n then
    let init : List (Option (List ℕ)) := (List.range n).map fun x => if x = u then some [u] else none
    let final := (expandStep E n)^[n] init
    (final.getD v none).map List.reverse
  else none

private lemma expandStep_length (E : List (ℕ × ℕ)) (n : ℕ) (best : List (Option (List ℕ))) :
    (expandStep E n best).length = best.length := by
  unfold expandStep
  induction E generalizing best with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split_ifs <;> cases h1 : best.getD e.1 none <;> cases h2 : best.getD e.2 none <;>
      simp <;> split <;> simp

private lemma expandStep_preserves_some (E : List (ℕ × ℕ)) (n : ℕ)
    (best : List (Option (List ℕ))) (w : ℕ) (p : List ℕ)
    (hw : best.getD w none = some p) :
    ∃ p', (expandStep E n best).getD w none = some p' := by
  unfold expandStep
  induction E generalizing best p with
  | nil => exact ⟨p, hw⟩
  | cons e es ih =>
    simp only [List.foldl_cons]
    have hstep : ∀ (acc : List (Option (List ℕ))) (a b : ℕ),
        (∃ q, acc.getD w none = some q) →
        ∃ q', (match acc.getD a none, acc.getD b none with
          | some p1, none => acc.set b (some (b :: p1))
          | _, _ => acc).getD w none = some q' := by
      intro acc a b ⟨q, hq⟩
      cases ha : acc.getD a none <;> cases hb : acc.getD b none
      · exact ⟨q, hq⟩
      · exact ⟨q, hq⟩
      · rename_i p1
        by_cases hwb : w = b
        · subst hwb; rw [hq] at hb; cases hb
        · simp [List.getD, List.getElem?_set_ne (Ne.symm hwb)]
          exact ⟨q, by simpa [List.getD] using hq⟩
      · exact ⟨q, hq⟩
    have h1 : ∃ q1, (if h : e.1 < n ∧ e.2 < n then
        let acc1 := match best.getD e.1 none, best.getD e.2 none with
          | some p1, none => best.set e.2 (some (e.2 :: p1))
          | _, _ => best
        match acc1.getD e.2 none, acc1.getD e.1 none with
        | some p2, none => acc1.set e.1 (some (e.1 :: p2))
        | _, _ => acc1
      else best).getD w none = some q1 := by
      split_ifs
      · obtain ⟨q0, hq0⟩ := hstep best e.1 e.2 ⟨p, hw⟩
        exact hstep _ e.2 e.1 ⟨q0, hq0⟩
      · exact ⟨p, hw⟩
    obtain ⟨q1, hq1⟩ := h1
    exact ih _ q1 hq1

private lemma expandStep_inv (E : List (ℕ × ℕ)) (n u : ℕ) (_hu : u < n)
    (best : List (Option (List ℕ))) (hlen : best.length = n)
    (hinv : ∀ w < n, ∀ rp, best.getD w none = some rp →
      IsPathAlong E u w rp.reverse ∧ rp.Nodup ∧ ∀ z ∈ rp, z < n ∧ (best.getD z none).isSome) :
    ∀ w < n, ∀ rp, (expandStep E n best).getD w none = some rp →
      IsPathAlong E u w rp.reverse ∧ rp.Nodup ∧ ∀ z ∈ rp, z < n ∧ ( (expandStep E n best).getD z none).isSome := by
  have hsingle : ∀ (a b : ℕ), a < n → b < n → ((a, b) ∈ E ∨ (b, a) ∈ E) →
      ∀ (acc : List (Option (List ℕ))), acc.length = n →
      (∀ w < n, ∀ rp, acc.getD w none = some rp →
        IsPathAlong E u w rp.reverse ∧ rp.Nodup ∧ ∀ z ∈ rp, z < n ∧ (acc.getD z none).isSome) →
      let acc' := match acc.getD a none, acc.getD b none with
        | some p1, none => acc.set b (some (b :: p1))
        | _, _ => acc
      acc'.length = n ∧
      (∀ w < n, ∀ rp, acc'.getD w none = some rp →
        IsPathAlong E u w rp.reverse ∧ rp.Nodup ∧ ∀ z ∈ rp, z < n ∧ (acc'.getD z none).isSome) := by
    intro a b ha hb hab acc hlen_acc hinv_acc
    cases ha_eq : acc.getD a none with
    | none => exact ⟨by simp [hlen_acc], hinv_acc⟩
    | some p1 =>
      cases hb_eq : acc.getD b none with
      | some p2 => exact ⟨by simp [hlen_acc], hinv_acc⟩
      | none =>
        dsimp only
        have hlen' : (acc.set b (some (b :: p1))).length = n := by simp [hlen_acc]
        refine ⟨hlen', fun w hw rp hrp => ?_⟩
        have hpres : ∀ z, (acc.getD z none).isSome →
            ((acc.set b (some (b :: p1))).getD z none).isSome := by
          intro z hz
          by_cases hzb : z = b
          · subst hzb; simp [List.getD, List.getElem?_set_self (hlen_acc ▸ hb)]
          · simp [List.getD, List.getElem?_set_ne (Ne.symm hzb)]
            simpa [List.getD] using hz
        by_cases hwb : w = b
        · subst hwb
          have hset : (acc.set w (some (w :: p1))).getD w none = some (w :: p1) := by
            simp [List.getD, List.getElem?_set_self (hlen_acc ▸ hw)]
          rw [hset] at hrp
          injection hrp with hEq
          subst hEq
          obtain ⟨hp1_path, hp1_nd, hp1_mem⟩ := hinv_acc a ha p1 ha_eq
          have hw_not_mem : w ∉ p1 := by
            intro hmem
            have hsome := (hp1_mem w hmem).2
            rw [hb_eq] at hsome
            simp at hsome
          refine ⟨?_, List.nodup_cons.mpr ⟨hw_not_mem, hp1_nd⟩, fun z hz => ?_⟩
          · rw [List.reverse_cons]
            exact isPathAlong_concat hp1_path hab
          · rcases List.mem_cons.mp hz with rfl | hzp1
            · exact ⟨hw, by simp [List.getD, List.getElem?_set_self (hlen_acc ▸ hw)]⟩
            · exact ⟨(hp1_mem z hzp1).1, hpres z (hp1_mem z hzp1).2⟩
        · have hget : (acc.set b (some (b :: p1))).getD w none = acc.getD w none := by
            simp [List.getD, List.getElem?_set_ne (Ne.symm hwb)]
          rw [hget] at hrp
          obtain ⟨h1, h2, h3⟩ := hinv_acc w hw rp hrp
          exact ⟨h1, h2, fun z hz => ⟨(h3 z hz).1, hpres z (h3 z hz).2⟩⟩
  unfold expandStep
  suffices hgen : ∀ (es : List (ℕ × ℕ)), (∀ e ∈ es, e ∈ E) →
      ∀ (acc : List (Option (List ℕ))), acc.length = n →
      (∀ w < n, ∀ rp, acc.getD w none = some rp →
        IsPathAlong E u w rp.reverse ∧ rp.Nodup ∧ ∀ z ∈ rp, z < n ∧ (acc.getD z none).isSome) →
      (es.foldl (fun acc e =>
        if h : e.1 < n ∧ e.2 < n then
          let acc1 :=
            match acc.getD e.1 none, acc.getD e.2 none with
            | some p1, none => acc.set e.2 (some (e.2 :: p1))
            | _, _ => acc
          match acc1.getD e.2 none, acc1.getD e.1 none with
          | some p2, none => acc1.set e.1 (some (e.1 :: p2))
          | _, _ => acc1
        else acc) acc).length = n ∧
      ∀ w < n, ∀ rp, (es.foldl (fun acc e =>
        if h : e.1 < n ∧ e.2 < n then
          let acc1 :=
            match acc.getD e.1 none, acc.getD e.2 none with
            | some p1, none => acc.set e.2 (some (e.2 :: p1))
            | _, _ => acc
          match acc1.getD e.2 none, acc1.getD e.1 none with
          | some p2, none => acc1.set e.1 (some (e.1 :: p2))
          | _, _ => acc1
        else acc) acc).getD w none = some rp →
        IsPathAlong E u w rp.reverse ∧ rp.Nodup ∧ ∀ z ∈ rp, z < n ∧
          ((es.foldl (fun acc e =>
            if h : e.1 < n ∧ e.2 < n then
              let acc1 :=
                match acc.getD e.1 none, acc.getD e.2 none with
                | some p1, none => acc.set e.2 (some (e.2 :: p1))
                | _, _ => acc
              match acc1.getD e.2 none, acc1.getD e.1 none with
              | some p2, none => acc1.set e.1 (some (e.1 :: p2))
              | _, _ => acc1
            else acc) acc).getD z none).isSome by
    exact (hgen E (fun _ h => h) best hlen hinv).2
  intro es hes
  induction es with
  | nil => intro acc hl hi; exact ⟨hl, hi⟩
  | cons e es ih =>
    intro acc hl hi
    simp only [List.foldl_cons]
    have heE : e ∈ E := hes e (by simp)
    have hes' : ∀ e' ∈ es, e' ∈ E := fun e' he' => hes e' (by simp [he'])
    by_cases h : e.1 < n ∧ e.2 < n
    · rw [dite_eq_left_of_eq_true (eq_true h)]
      obtain ⟨hl1, hi1⟩ := hsingle e.1 e.2 h.1 h.2 (Or.inl heE) acc hl hi
      obtain ⟨hl2, hi2⟩ := hsingle e.2 e.1 h.2 h.1 (Or.inr heE) _ hl1 hi1
      exact ih hes' _ hl2 hi2
    · rw [dite_eq_right_of_eq_false (eq_false h)]
      exact ih hes' acc hl hi

private lemma expandStep_reaches_of_edge {E : List (ℕ × ℕ)} {n a b : ℕ}
    (ha : a < n) (hb : b < n) (hab : (a, b) ∈ E ∨ (b, a) ∈ E)
    (best : List (Option (List ℕ))) (hlen : best.length = n)
    (ha_some : (best.getD a none).isSome) :
    ((expandStep E n best).getD b none).isSome := by
  have hmono : ∀ (es : List (ℕ × ℕ)) (acc : List (Option (List ℕ))) (w : ℕ),
      (acc.getD w none).isSome →
      ((es.foldl (fun acc e =>
        if h : e.1 < n ∧ e.2 < n then
          let acc1 := match acc.getD e.1 none, acc.getD e.2 none with
            | some p1, none => acc.set e.2 (some (e.2 :: p1))
            | _, _ => acc
          match acc1.getD e.2 none, acc1.getD e.1 none with
          | some p2, none => acc1.set e.1 (some (e.1 :: p2))
          | _, _ => acc1
        else acc) acc).getD w none).isSome := by
    intro es
    induction es with
    | nil => intro acc w hw; exact hw
    | cons e es ih =>
      intro acc w hw
      simp only [List.foldl_cons]
      apply ih
      have hs : ∀ (x y : ℕ) (st : List (Option (List ℕ))), (st.getD w none).isSome →
          ((match st.getD x none, st.getD y none with
            | some p1, none => st.set y (some (y :: p1))
            | _, _ => st).getD w none).isSome := by
        intro x y st hst
        cases hx : st.getD x none <;> cases hy : st.getD y none <;> try exact hst
        rename_i p1
        by_cases hwy : w = y
        · subst hwy; rw [hy] at hst; simp at hst
        · simp [List.getD, List.getElem?_set_ne (Ne.symm hwy)]
          simpa [List.getD] using hst
      split_ifs
      · exact hs e.2 e.1 _ (hs e.1 e.2 acc hw)
      · exact hw
  have step_edge : ∀ (x y : ℕ) (st : List (Option (List ℕ))), st.length = n → x < n → y < n →
      (st.getD x none).isSome →
      ((match st.getD x none, st.getD y none with
        | some p1, none => st.set y (some (y :: p1))
        | _, _ => st).getD y none).isSome := by
    intro x y st hsl hx hy hxs
    cases hx_eq : st.getD x none
    · rw [hx_eq] at hxs; simp at hxs
    · cases hy_eq : st.getD y none
      · simp [List.getD, List.getElem?_set_self (hsl ▸ hy)]
      · change (st.getD y none).isSome = true
        rw [hy_eq]; rfl
  unfold expandStep
  have he_mem : ∃ e ∈ E, (e = (a, b) ∨ e = (b, a)) := by
    rcases hab with h | h
    · exact ⟨(a, b), h, Or.inl rfl⟩
    · exact ⟨(b, a), h, Or.inr rfl⟩
  obtain ⟨e, heE, heq⟩ := he_mem
  obtain ⟨es₁, es₂, hsplit⟩ := List.append_of_mem heE
  rw [hsplit, List.foldl_append, List.foldl_cons]
  apply hmono es₂
  have hlen1 : (es₁.foldl (fun acc e =>
      if h : e.1 < n ∧ e.2 < n then
        let acc1 := match acc.getD e.1 none, acc.getD e.2 none with
          | some p1, none => acc.set e.2 (some (e.2 :: p1))
          | _, _ => acc
        match acc1.getD e.2 none, acc1.getD e.1 none with
        | some p2, none => acc1.set e.1 (some (e.1 :: p2))
        | _, _ => acc1
      else acc) best).length = n := by
    clear hsplit heE heq ha_some
    induction es₁ generalizing best with
    | nil => exact hlen
    | cons x xs ihx =>
      simp only [List.foldl_cons]
      apply ihx
      split_ifs
      · have hsl : ∀ u v (st : List (Option (List ℕ))), (match st.getD u none, st.getD v none with
            | some p1, none => st.set v (some (v :: p1))
            | _, _ => st).length = st.length := by
          intro u v st
          cases st.getD u none <;> cases st.getD v none <;> simp
        rw [hsl, hsl, hlen]
      · exact hlen
  have ha1 : ((es₁.foldl (fun acc e =>
      if h : e.1 < n ∧ e.2 < n then
        let acc1 := match acc.getD e.1 none, acc.getD e.2 none with
          | some p1, none => acc.set e.2 (some (e.2 :: p1))
          | _, _ => acc
        match acc1.getD e.2 none, acc1.getD e.1 none with
        | some p2, none => acc1.set e.1 (some (e.1 :: p2))
        | _, _ => acc1
      else acc) best).getD a none).isSome := hmono es₁ best a ha_some
  set acc0 := es₁.foldl (fun acc e =>
    if h : e.1 < n ∧ e.2 < n then
      let acc1 := match acc.getD e.1 none, acc.getD e.2 none with
        | some p1, none => acc.set e.2 (some (e.2 :: p1))
        | _, _ => acc
      match acc1.getD e.2 none, acc1.getD e.1 none with
      | some p2, none => acc1.set e.1 (some (e.1 :: p2))
      | _, _ => acc1
    else acc) best
  rcases heq with rfl | rfl
  · rw [dite_eq_left_of_eq_true (eq_true ⟨ha, hb⟩)]
    have hb1 : (let acc1 := match acc0.getD a none, acc0.getD b none with
        | some p1, none => acc0.set b (some (b :: p1))
        | _, _ => acc0
        (acc1.getD b none)).isSome := step_edge a b acc0 hlen1 ha hb ha1
    set acc1 := match acc0.getD a none, acc0.getD b none with
      | some p1, none => acc0.set b (some (b :: p1))
      | _, _ => acc0
    cases ha_acc1 : acc1.getD b none <;> cases hb_acc1 : acc1.getD a none
    · rw [ha_acc1] at hb1; simp at hb1
    · rw [ha_acc1] at hb1; simp at hb1
    · by_cases hba : b = a
      · subst hba; rw [ha_acc1] at hb_acc1; cases hb_acc1
      · dsimp only
        rw [ha_acc1, hb_acc1]
        change ((acc1.set a (some (a :: _))).getD b none).isSome = true
        rw [List.getD, List.getElem?_set_ne (Ne.symm hba)]
        change (acc1.getD b none).isSome = true
        rw [ha_acc1]; rfl
    · dsimp only
      rw [ha_acc1, hb_acc1]
      change (acc1.getD b none).isSome = true
      rw [ha_acc1]; rfl
  · rw [dite_eq_left_of_eq_true (eq_true ⟨hb, ha⟩)]
    set acc1 := match acc0.getD b none, acc0.getD a none with
      | some p1, none => acc0.set a (some (a :: p1))
      | _, _ => acc0
    have ha1' : (acc1.getD a none).isSome := by
      dsimp only [acc1]
      cases h1 : acc0.getD b none <;> cases h2 : acc0.getD a none
      · rw [h2] at ha1; simp at ha1
      · rfl
      · simp [List.getD, hlen1 ▸ ha]
      · dsimp only; rw [h2]; rfl
    have hlen_acc1 : acc1.length = n := by
      dsimp [acc1]
      cases acc0.getD b none <;> cases acc0.getD a none <;> simp [hlen1]
    exact step_edge a b acc1 hlen_acc1 ha hb ha1'

theorem findSimplePath_some {E : List (ℕ × ℕ)} {n u v : ℕ} {Q : List ℕ}
    (hQ : findSimplePath E n u v = some Q) :
    IsPathAlong E u v Q ∧ Q.Nodup ∧ ∀ x ∈ Q, x < n := by
  unfold findSimplePath at hQ
  split_ifs at hQ with huv
  · set init : List (Option (List ℕ)) :=
      (List.range n).map fun x => if x = u then some [u] else none
    have hinit_len : init.length = n := by simp [init]
    have hinit_inv : ∀ w < n, ∀ rp, init.getD w none = some rp →
        IsPathAlong E u w rp.reverse ∧ rp.Nodup ∧ ∀ z ∈ rp, z < n ∧ (init.getD z none).isSome := by
      intro w hw rp hrp
      have hget : init.getD w none = if w = u then some [u] else none := by
        simp [init, List.getD, hw]
      rw [hget] at hrp
      split_ifs at hrp with hwu
      · subst hwu
        injection hrp with hrp_eq
        subst hrp_eq
        refine ⟨by simpa using isPathAlong_singleton E w, List.nodup_singleton w, fun z hz => ?_⟩
        simp only [List.mem_singleton] at hz
        subst hz
        exact ⟨hw, by simp [init, List.getD, hw]⟩
    have hk_inv : ∀ k, ((expandStep E n)^[k] init).length = n ∧
        ∀ w < n, ∀ rp, ((expandStep E n)^[k] init).getD w none = some rp →
          IsPathAlong E u w rp.reverse ∧ rp.Nodup ∧
            ∀ z ∈ rp, z < n ∧ (((expandStep E n)^[k] init).getD z none).isSome := by
      intro k
      induction k with
      | zero => exact ⟨hinit_len, hinit_inv⟩
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact ⟨by rw [expandStep_length, ih.1],
          expandStep_inv E n u huv.1 _ ih.1 ih.2⟩
    obtain ⟨rp, hrp_eq, rfl⟩ := Option.map_eq_some_iff.mp hQ
    obtain ⟨h1, h2, h3⟩ := (hk_inv n).2 v huv.2 rp hrp_eq
    refine ⟨h1, List.nodup_reverse.mpr h2, fun x hx => (h3 x (List.mem_reverse.mp hx)).1⟩

theorem findSimplePath_complete {E : List (ℕ × ℕ)} {n u v : ℕ}
    (hE : ∀ e ∈ E, e.1 < n ∧ e.2 < n) (hu : u < n) (hv : v < n)
    {P : List ℕ} (hP : IsPathAlong E u v P) :
    ∃ Q, findSimplePath E n u v = some Q ∧ Q.length ≤ n := by
  obtain ⟨Pnd, hPnd, hPnd_nodup, _, _⟩ := exists_nodup_isPathAlong hP
  have hPnd_lt : ∀ x ∈ Pnd, x < n := isPathAlong_all_mem_range hE hu hPnd
  have hPnd_len : Pnd.length ≤ n := by
    have hsub : Pnd ⊆ List.range n := fun x hx => List.mem_range.mpr (hPnd_lt x hx)
    simpa [List.length_range] using hPnd_nodup.length_le_of_subset hsub
  set init : List (Option (List ℕ)) :=
    (List.range n).map fun x => if x = u then some [u] else none
  have hlen : ∀ k, ((expandStep E n)^[k] init).length = n := by
    intro k
    induction k with
    | zero => simp [init]
    | succ k ih => rw [Function.iterate_succ_apply', expandStep_length, ih]
  have hreach : ∀ (Q : List ℕ) (w k : ℕ), IsPathAlong E u w Q → (∀ z ∈ Q, z < n) →
      Q.length ≤ k + 1 → (((expandStep E n)^[k] init).getD w none).isSome := by
    intro Q
    induction Q using List.reverseRecOn with
    | nil => intro w k hQ _ _; simp [IsPathAlong] at hQ
    | append_singleton xs w ih =>
      intro v' k hQ hQlt hk
      have hvw : v' = w := by
        have := hQ.2.1
        simp at this
        exact this.symm
      subst hvw
      cases xs using List.reverseRecOn with
      | nil =>
        simp only [List.nil_append] at hQ
        have huw : v' = u := by simpa [IsPathAlong] using hQ.1
        rw [huw]
        clear ih
        induction k with
        | zero => simp [init, List.getD, hu]
        | succ k ihk =>
          rw [Function.iterate_succ_apply']
          cases hcur : ((expandStep E n)^[k] init).getD u none with
          | none => rw [hcur] at ihk; simp at ihk
          | some p =>
            obtain ⟨p', hp'⟩ := expandStep_preserves_some E n _ u p hcur
            change ((expandStep E n ((expandStep E n)^[k] init)).getD u none).isSome = true
            rw [hp']
            rfl
      | append_singleton ys z =>
        have hQ1 : IsPathAlong E u z (ys ++ [z]) := by
          rcases hQ with ⟨hh, _, hc⟩
          refine ⟨?_, by simp, (List.isChain_append.mp hc).1⟩
          cases ys <;> simpa using hh
        have hzw : (z, v') ∈ E ∨ (v', z) ∈ E := by
          have hc := hQ.2.2
          exact (List.isChain_append.mp hc).2.2 z (by simp) v' (by simp)
        have hz_lt : z < n := hQlt z (by simp)
        have hw_lt : v' < n := hQlt v' (by simp)
        have hk_pos : 1 ≤ k := by
          simp only [List.length_append, List.length_singleton] at hk
          omega
        obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk_pos
        have ih1 := ih z k' hQ1 (fun a ha => hQlt a (by simp at ha ⊢; rcases ha with h | rfl <;> simp [*]))
          (by simp only [List.length_append, List.length_singleton] at hk ⊢; omega)
        rw [Function.iterate_succ_apply']
        exact expandStep_reaches_of_edge hz_lt hw_lt hzw _ (hlen k') ih1
  have hv_some := hreach Pnd v n hPnd hPnd_lt (by omega)
  cases hres : ((expandStep E n)^[n] init).getD v none with
  | none => rw [hres] at hv_some; simp at hv_some
  | some rp =>
    have hfind : findSimplePath E n u v = some rp.reverse := by
      unfold findSimplePath
      simp only [hu, hv, and_self, ↓reduceIte]
      change Option.map List.reverse (((expandStep E n)^[n] init).getD v none) = some rp.reverse
      rw [hres]
      rfl
    obtain ⟨hpath, hnd, hlt⟩ := findSimplePath_some hfind
    refine ⟨rp.reverse, hfind, ?_⟩
    have hsub : rp.reverse ⊆ List.range n := fun x hx => List.mem_range.mpr (hlt x hx)
    simpa [List.length_range] using hnd.length_le_of_subset hsub

end MinCostFlow.Expander

