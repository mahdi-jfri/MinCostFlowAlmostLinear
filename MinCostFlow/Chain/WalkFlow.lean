module

public import MinCostFlow.Basic.Forest
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic.Ring

/-!
# Walk flows, paths, and circulations on forests

This file develops basic facts about `MGraph` walks, paths, cycles, `walkFlow`, `walkRev`,
`walkInner`, `walkLength`, and circulations supported on forests, for use across `MinCostFlow.Chain`.
-/

public section

namespace MinCostFlow

namespace MGraph

lemma b_self (G : MGraph) {e : ℕ} (h : G.tail e = G.head e) (v : ℕ) : G.b e v = 0 := by
  simp [MGraph.b, h]

lemma b_eq_zero_of_ne (G : MGraph) {e v : ℕ} (ht : v ≠ G.tail e) (hh : v ≠ G.head e) :
    G.b e v = 0 := by
  simp [MGraph.b, ht, hh]

lemma abs_b_le_one (G : MGraph) (e v : ℕ) : |G.b e v| ≤ 1 := by
  simp only [MGraph.b]
  split_ifs <;> norm_num

lemma demand_zero (G : MGraph) (v : ℕ) : G.demand 0 v = 0 := by
  simp [MGraph.demand]

lemma demand_add (G : MGraph) (f g : ℕ → ℝ) (v : ℕ) :
    G.demand (f + g) v = G.demand f v + G.demand g v := by
  simp [MGraph.demand, mul_add, Finset.sum_add_distrib]

lemma demand_sub (G : MGraph) (f g : ℕ → ℝ) (v : ℕ) :
    G.demand (f - g) v = G.demand f v - G.demand g v := by
  simp [MGraph.demand, mul_sub, Finset.sum_sub_distrib]

lemma demand_smul (G : MGraph) (a : ℝ) (f : ℕ → ℝ) (v : ℕ) :
    G.demand (fun e => a * f e) v = a * G.demand f v := by
  simp only [MGraph.demand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

lemma isCirculation_zero (G : MGraph) : G.IsCirculation 0 := by
  intro v _
  exact G.demand_zero v

lemma isCirculation_sub {G : MGraph} {f g : ℕ → ℝ} (hf : G.IsCirculation f)
    (hg : G.IsCirculation g) : G.IsCirculation (f - g) := by
  intro v hv
  rw [G.demand_sub, hf v hv, hg v hv, sub_zero]

lemma isWalk_append {G : MGraph} {u v w : ℕ} {P Q : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) (hQ : G.IsWalk v w Q) : G.IsWalk u w (P ++ Q) := by
  induction hP with
  | nil _ => exact hQ
  | cons he hsrc _ ih => exact .cons he hsrc (ih hQ)

lemma isWalk_src_mem {G : MGraph} (hG : G.IsValid) {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) (hne : P ≠ []) : u ∈ G.V ∧ v ∈ G.V := by
  induction hP with
  | nil _ => contradiction
  | @cons u v x P he hsrc hrest ih =>
    have hxy := hG x.1 he
    have hu : u ∈ G.V := by
      rw [← hsrc]
      cases hx : x.2 <;> simp [MGraph.src, hx, hxy.1, hxy.2]
    rcases eq_or_ne P [] with rfl | hneP
    · cases hrest
      have hdst : G.dst x ∈ G.V := by cases hx : x.2 <;> simp [MGraph.dst, hx, hxy.1, hxy.2]
      exact ⟨hu, hdst⟩
    · exact ⟨hu, (ih hneP).2⟩

lemma isWalk_edges_mem {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) : ∀ x ∈ P, x.1 ∈ G.E := by
  induction hP with
  | nil _ => intro x hx; cases hx
  | cons he _ _ ih =>
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact he
    · exact ih y hy

lemma isWalk_of_isSubgraph {G H : MGraph} (hGH : G.IsSubgraph H) {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : H.IsWalk u v P) : G.IsWalk u v P := by
  induction hP with
  | nil w => exact .nil w
  | @cons u v x P he hsrc _ ih =>
    have hEnd := hGH.2.2 x.1 he
    have hsrcG : G.src x = u := by
      rw [← hsrc]
      cases x.2 <;> simp [MGraph.src, hEnd.1, hEnd.2]
    have hdstG : G.dst x = H.dst x := by
      cases x.2 <;> simp [MGraph.dst, hEnd.1, hEnd.2]
    exact .cons (hGH.2.1 he) hsrcG (hdstG ▸ ih)

lemma isWalk_walkRev {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) : G.IsWalk v u (walkRev P) := by
  induction hP with
  | nil w => exact .nil w
  | @cons u v x P he hsrc _ ih =>
    simp only [walkRev, List.map_cons, List.reverse_cons]
    refine isWalk_append ih ?_
    have hsrc' : G.src (x.1, !x.2) = G.dst x := by
      cases hx : x.2 <;> simp [MGraph.src, MGraph.dst, hx]
    have hdst' : G.dst (x.1, !x.2) = u := by
      rw [← hsrc]
      cases hx : x.2 <;> simp [MGraph.src, MGraph.dst, hx]
    refine .cons he hsrc' ?_
    rw [hdst']
    exact MGraph.IsWalk.nil u

lemma connected_refl (G : MGraph) (u : ℕ) : G.Connected u u :=
  ⟨[], .nil u⟩

lemma connected_symm {G : MGraph} {u v : ℕ} (h : G.Connected u v) : G.Connected v u :=
  let ⟨P, hP⟩ := h
  ⟨walkRev P, isWalk_walkRev hP⟩

lemma connected_trans {G : MGraph} {u v w : ℕ} (h1 : G.Connected u v) (h2 : G.Connected v w) :
    G.Connected u w :=
  let ⟨P, hP⟩ := h1
  let ⟨Q, hQ⟩ := h2
  ⟨P ++ Q, isWalk_append hP hQ⟩

lemma connected_of_isSubgraph {G H : MGraph} (hGH : G.IsSubgraph H) {u v : ℕ}
    (h : H.Connected u v) : G.Connected u v :=
  let ⟨P, hP⟩ := h
  ⟨P, isWalk_of_isSubgraph hGH hP⟩

lemma walkVertices_append (G : MGraph) (u : ℕ) (P Q : List (ℕ × Bool)) :
    G.walkVertices u (P ++ Q) = G.walkVertices u P ++ Q.map G.dst := by
  simp [MGraph.walkVertices, List.map_append]

private lemma isWalk_nil_eq {G : MGraph} {u v : ℕ} : G.IsWalk u v [] → u = v
  | .nil _ => rfl

private lemma isWalk_split_of_mem_walkVertices {G : MGraph} :
    ∀ {u v w : ℕ} {P : List (ℕ × Bool)}, G.IsWalk u v P → w ∈ G.walkVertices u P →
      ∃ P₁ P₂ : List (ℕ × Bool), P = P₁ ++ P₂ ∧ G.IsWalk u w P₁ ∧ G.IsWalk w v P₂ := by
  intro u v w P hP hw
  induction hP with
  | nil z =>
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hw
    rcases hw with rfl
    exact ⟨[], [], rfl, MGraph.IsWalk.nil _, MGraph.IsWalk.nil _⟩
  | @cons u v x P he hsrc hrest ih =>
    simp only [MGraph.walkVertices, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨[], x :: P, rfl, MGraph.IsWalk.nil w, .cons he hsrc hrest⟩
    · have hw' : w ∈ G.walkVertices (G.dst x) P := hw
      obtain ⟨P₁, P₂, hsplit, h1, h2⟩ := ih hw'
      exact ⟨x :: P₁, P₂, by simp [hsplit], .cons he hsrc h1, h2⟩

private lemma exists_shorter_walk_of_not_nodup {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) (hnodup : ¬ (G.walkVertices u P).Nodup) :
    ∃ Q : List (ℕ × Bool), Q.length < P.length ∧ G.IsWalk u v Q := by
  induction hP with
  | nil z =>
    exfalso
    exact hnodup (by simp [MGraph.walkVertices])
  | @cons u v x P he hsrc hrest ih =>
    simp only [MGraph.walkVertices, List.map_cons, List.nodup_cons, List.mem_cons,
      not_or] at hnodup
    by_cases hmem : u ∈ P.map G.dst
    · have hw : u ∈ G.walkVertices (G.dst x) P := by
        simp [MGraph.walkVertices, hmem]
      obtain ⟨P₁, P₂, hsplit, _, h2⟩ := isWalk_split_of_mem_walkVertices hrest hw
      refine ⟨P₂, ?_, h2⟩
      have hlen : P.length = P₁.length + P₂.length := by
        have := congrArg List.length hsplit
        simpa [List.length_append] using this
      simp only [List.length_cons]
      omega
    · by_cases hu_dst : u = G.dst x
      · exact ⟨P, by simp, hu_dst ▸ hrest⟩
      · have hnd : ¬ (G.walkVertices (G.dst x) P).Nodup := by
          intro hnd'
          exact hnodup ⟨⟨hu_dst, hmem⟩, by simpa [MGraph.walkVertices] using hnd'⟩
        obtain ⟨Q, hQlen, hQ⟩ := ih hnd
        exact ⟨x :: Q, by simp; omega, .cons he hsrc hQ⟩

lemma exists_isPath_of_connected {G : MGraph} {u v : ℕ} (h : G.Connected u v) :
    ∃ P, G.IsPath u v P := by
  have hex : ∃ n, ∃ P : List (ℕ × Bool), P.length = n ∧ G.IsWalk u v P :=
    let ⟨P, hP⟩ := h
    ⟨P.length, P, rfl, hP⟩
  classical
  obtain ⟨P, hlen, hP⟩ := Nat.find_spec hex
  refine ⟨P, hP, ?_⟩
  by_contra hnd
  obtain ⟨Q, hQlen, hQ⟩ := exists_shorter_walk_of_not_nodup hP hnd
  exact Nat.find_min hex (hlen ▸ hQlen) ⟨Q, rfl, hQ⟩

lemma isPath_forestPath {F : MGraph} {u v : ℕ} (h : F.Connected u v) :
    F.IsPath u v (forestPath F u v) := by
  classical
  have hex := exists_isPath_of_connected h
  simpa [forestPath, hex] using Classical.choose_spec hex

lemma isWalk_forestPath {F : MGraph} {u v : ℕ} (h : F.Connected u v) :
    F.IsWalk u v (forestPath F u v) :=
  (isPath_forestPath h).1

lemma walkVertices_edges_mem_V {G : MGraph} (hG : G.IsValid) {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) (hu : u ∈ G.V) : ∀ w ∈ G.walkVertices u P, w ∈ G.V := by
  induction hP with
  | nil z =>
    intro w hw
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hw
    rwa [hw]
  | @cons u v x P he _ _ ih =>
    intro w hw
    simp only [MGraph.walkVertices, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hu
    · have hxy := hG x.1 he
      have hdst : G.dst x ∈ G.V := by cases hx2 : x.2 <;> simp [MGraph.dst, hx2, hxy.1, hxy.2]
      exact ih hdst w hw

lemma walkVertices_last {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)} (hP : G.IsWalk u v P) :
    (G.walkVertices u P).getLast (by simp [MGraph.walkVertices]) = v := by
  induction hP with
  | nil z => simp [MGraph.walkVertices]
  | @cons u v x P _ _ _ ih =>
    simp only [MGraph.walkVertices, List.map_cons]
    rw [List.getLast_cons (by simp)]
    exact ih

lemma isPath_edges_nodup {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsPath u v P) : (P.map Prod.fst).Nodup := by
  rcases hP with ⟨hW, hnd⟩
  induction hW with
  | nil _ => simp
  | @cons u v x P he hsrc hrest ih =>
    have hnd_step : u ∉ G.walkVertices (G.dst x) P ∧ (G.walkVertices (G.dst x) P).Nodup := by
      simpa [MGraph.walkVertices, List.nodup_cons] using hnd
    have ih' := ih hnd_step.2
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih'⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨y, hyP, hyx⟩ := hmem
    have hyMem : G.src y ∈ G.walkVertices (G.dst x) P ∧ G.dst y ∈ P.map G.dst := by
      clear ih ih' hnd hnd_step hsrc he
      generalize hd : G.dst x = d at hrest ⊢
      clear hd
      induction hrest with
      | nil _ => cases hyP
      | @cons a b z Q _ hsrcz _ ihQ =>
        simp only [List.mem_cons] at hyP
        rcases hyP with rfl | hyQ
        · exact ⟨by simp [MGraph.walkVertices, hsrcz], by simp⟩
        · obtain ⟨h1, h2⟩ := ihQ hyQ
          refine ⟨?_, by simp [h2]⟩
          simp only [MGraph.walkVertices, List.mem_cons] at h1 ⊢
          exact Or.inr (by simpa [MGraph.walkVertices] using h1)
    by_cases hdir : y.2 = x.2
    · have hdstEq : G.dst y = G.dst x := by
        cases hx2 : x.2 <;> cases hy2 : y.2 <;> simp_all [MGraph.dst]
      rw [hdstEq] at hyMem
      have hndDst : G.dst x ∉ P.map G.dst := by
        dsimp only [MGraph.walkVertices] at hnd_step
        exact (List.nodup_cons.mp hnd_step.2).1
      exact hndDst hyMem.2
    · have hsrcEq : G.dst y = u := by
        rw [← hsrc]
        cases hx2 : x.2 <;> cases hy2 : y.2 <;> simp_all [MGraph.src, MGraph.dst]
      rw [hsrcEq] at hyMem
      have hnotP : u ∉ P.map G.dst := by
        intro hm
        exact hnd_step.1 (by simp [MGraph.walkVertices, hm])
      exact hnotP hyMem.2

lemma isPath_append_right_mem_walkVertices {G : MGraph} {u v w : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsPath u v P) (hnot : w ∉ G.walkVertices u P) {x : ℕ × Bool}
    (he : x.1 ∈ G.E) (hsrc : G.src x = v) (hdst : G.dst x = w) :
    G.IsPath u w (P ++ [x]) := by
  refine ⟨isWalk_append hP.1 (.cons he hsrc (by rw [hdst]; exact MGraph.IsWalk.nil w)), ?_⟩
  rw [walkVertices_append, List.map_cons, List.map_nil, hdst, List.nodup_append]
  refine ⟨hP.2, List.nodup_singleton w, fun a ha b hb heq => ?_⟩
  rw [List.mem_singleton] at hb
  exact hnot (hb ▸ heq ▸ ha)

lemma no_selfLoop_of_isForest {F : MGraph} (hF : F.IsForest) {e : ℕ} (he : e ∈ F.E) :
    F.tail e ≠ F.head e := by
  intro hloop
  apply hF.2 [(e, true)]
  refine ⟨by simp, by simp, F.tail e, ?_⟩
  refine .cons he rfl ?_
  have hdst : F.dst (e, true) = F.tail e := by simp [MGraph.dst, hloop]
  rw [hdst]
  exact .nil (F.tail e)

end MGraph

section WalkFlow

lemma walkFlow_nil (e : ℕ) : walkFlow [] e = 0 := by
  simp [walkFlow]

lemma walkFlow_cons (x : ℕ × Bool) (P : List (ℕ × Bool)) (e : ℕ) :
    walkFlow (x :: P) e = (if x.1 = e then (if x.2 then (1 : ℝ) else -1) else 0) + walkFlow P e := by
  simp [walkFlow]

lemma walkFlow_append (P Q : List (ℕ × Bool)) (e : ℕ) :
    walkFlow (P ++ Q) e = walkFlow P e + walkFlow Q e := by
  simp [walkFlow, List.map_append, List.sum_append]

lemma walkFlow_walkRev (P : List (ℕ × Bool)) (e : ℕ) :
    walkFlow (walkRev P) e = -walkFlow P e := by
  induction P with
  | nil => simp [walkRev, walkFlow]
  | cons x P ih =>
    have ih' : walkFlow (List.map (fun y => (y.1, !y.2)) P).reverse e = -walkFlow P e := ih
    simp only [walkRev, List.map_cons, List.reverse_cons]
    rw [walkFlow_append, ih', walkFlow_cons, walkFlow_cons, walkFlow_nil, add_zero]
    cases hx : x.2 <;> by_cases h : x.1 = e <;> simp [h]

lemma walkFlow_eq_zero_of_not_mem {P : List (ℕ × Bool)} {e : ℕ} (h : e ∉ walkEdges P) :
    walkFlow P e = 0 := by
  induction P with
  | nil => simp [walkFlow]
  | cons x P ih =>
    rw [walkFlow_cons]
    simp only [walkEdges, List.map_cons, List.toFinset_cons, Finset.mem_insert,
      not_or] at h
    have hne : x.1 ≠ e := Ne.symm h.1
    rw [ite_eq_right_iff.mpr (fun hEq => absurd hEq hne), zero_add]
    exact ih h.2

lemma mem_walkEdges_of_walkFlow_ne_zero {P : List (ℕ × Bool)} {e : ℕ} (h : walkFlow P e ≠ 0) :
    e ∈ walkEdges P := by
  by_contra hnot
  exact h (walkFlow_eq_zero_of_not_mem hnot)

lemma sum_abs_walkFlow_le_length (S : Finset ℕ) (P : List (ℕ × Bool)) :
    ∑ e ∈ S, |walkFlow P e| ≤ (P.length : ℝ) := by
  induction P with
  | nil => simp [walkFlow]
  | cons x P ih =>
    simp only [List.length_cons, Nat.cast_succ]
    calc
      ∑ e ∈ S, |walkFlow (x :: P) e|
          = ∑ e ∈ S, |(if x.1 = e then (if x.2 then (1 : ℝ) else -1) else 0) + walkFlow P e| := by
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [walkFlow_cons]
      _ ≤ ∑ e ∈ S, (|(if x.1 = e then (if x.2 then (1 : ℝ) else -1) else 0)| + |walkFlow P e|) := by
            refine Finset.sum_le_sum fun e _ => abs_add_le _ _
      _ = (∑ e ∈ S, |if x.1 = e then (if x.2 then (1 : ℝ) else -1) else 0|) +
            ∑ e ∈ S, |walkFlow P e| := Finset.sum_add_distrib
      _ ≤ 1 + (P.length : ℝ) := by
            refine add_le_add ?_ ih
            by_cases hx : x.1 ∈ S
            · rw [Finset.sum_eq_single x.1]
              · cases x.2 <;> simp
              · intro e _ hne
                simp [Ne.symm hne]
              · intro hnot; exact absurd hx hnot
            · rw [Finset.sum_eq_zero]
              · norm_num
              · intro e he
                have hne : x.1 ≠ e := fun h => hx (h ▸ he)
                simp [hne]
      _ = (P.length : ℝ) + 1 := add_comm _ _

lemma walkLength_nonneg {ℓ : ℕ → ℝ} {P : List (ℕ × Bool)}
    (hℓ : ∀ e ∈ walkEdges P, 0 ≤ ℓ e) : 0 ≤ walkLength ℓ P :=
  Finset.sum_nonneg fun e he => mul_nonneg (hℓ e he) (abs_nonneg _)

lemma walkEdges_walkRev (P : List (ℕ × Bool)) : walkEdges (walkRev P) = walkEdges P := by
  ext e
  simp only [walkEdges, walkRev, List.mem_toFinset, List.mem_map, List.mem_reverse]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨⟨a', b'⟩, hmem, h1⟩, h2⟩
    simp only [Prod.mk.injEq] at h1
    rcases h1 with ⟨rfl, rfl⟩
    exact ⟨(a', b'), hmem, h2⟩
  · rintro ⟨⟨a, b⟩, hmem, h1⟩
    exact ⟨(a, !b), ⟨(a, b), hmem, rfl⟩, h1⟩

lemma walkEdges_append (P Q : List (ℕ × Bool)) :
    walkEdges (P ++ Q) = walkEdges P ∪ walkEdges Q := by
  ext e
  simp [walkEdges, List.map_append]

lemma walkLength_walkRev (ℓ : ℕ → ℝ) (P : List (ℕ × Bool)) :
    walkLength ℓ (walkRev P) = walkLength ℓ P := by
  simp only [walkLength, walkEdges_walkRev]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [walkFlow_walkRev, abs_neg]

/-- Unoriented edge multiplicity `walkCount P e'` of `e'` in walk `P` (non-cancelling occurrence
count for passing `w^𝒮` in Definition 5.15 / `D40`). -/
@[expose] def walkCount (P : List (ℕ × Bool)) (e' : ℕ) : ℝ :=
  ((P.countP fun x => decide (x.1 = e') : ℕ) : ℝ)

lemma walkCount_nil (e' : ℕ) : walkCount [] e' = 0 := by
  simp [walkCount]

lemma walkCount_cons (x : ℕ × Bool) (P : List (ℕ × Bool)) (e' : ℕ) :
    walkCount (x :: P) e' = (if x.1 = e' then (1 : ℝ) else 0) + walkCount P e' := by
  by_cases h : x.1 = e' <;> simp [walkCount, h, add_comm]

lemma walkCount_append (P Q : List (ℕ × Bool)) (e' : ℕ) :
    walkCount (P ++ Q) e' = walkCount P e' + walkCount Q e' := by
  simp [walkCount, List.countP_append, Nat.cast_add]

lemma walkCount_walkRev (P : List (ℕ × Bool)) (e' : ℕ) :
    walkCount (walkRev P) e' = walkCount P e' := by
  simp [walkCount, walkRev, List.countP_reverse, List.countP_map]
  rfl

lemma walkCount_eq_zero_of_not_mem {P : List (ℕ × Bool)} {e' : ℕ} (h : e' ∉ walkEdges P) :
    walkCount P e' = 0 := by
  induction P with
  | nil => exact walkCount_nil e'
  | cons x P ih =>
    simp only [walkEdges, List.map_cons, List.toFinset_cons, Finset.mem_insert, not_or] at h
    rw [walkCount_cons, ite_eq_right_iff.mpr (fun hEq => absurd hEq (Ne.symm h.1)), zero_add]
    exact ih h.2

lemma walkCount_nonneg (P : List (ℕ × Bool)) (e' : ℕ) : 0 ≤ walkCount P e' := by
  unfold walkCount
  exact Nat.cast_nonneg _

lemma walkCount_le_length (P : List (ℕ × Bool)) (e' : ℕ) :
    walkCount P e' ≤ (P.length : ℝ) := by
  unfold walkCount
  exact Nat.cast_le.mpr List.countP_le_length

lemma abs_walkFlow_le_walkCount (P : List (ℕ × Bool)) (e' : ℕ) :
    |walkFlow P e'| ≤ walkCount P e' := by
  induction P with
  | nil => simp [walkFlow, walkCount]
  | cons x P ih =>
    rw [walkFlow_cons, walkCount_cons]
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ih)
    by_cases hx : x.1 = e'
    · subst hx; cases x.2 <;> norm_num
    · simp [hx]

lemma walkCount_eq_abs_walkFlow_of_nodup {P : List (ℕ × Bool)} (hnd : (P.map Prod.fst).Nodup)
    (e' : ℕ) : walkCount P e' = |walkFlow P e'| := by
  induction P with
  | nil => simp [walkFlow, walkCount]
  | cons x P ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [walkFlow_cons, walkCount_cons]
    by_cases hx : x.1 = e'
    · have hnotin : e' ∉ walkEdges P := by
        intro hmem
        simp only [walkEdges, List.mem_toFinset, List.mem_map] at hmem
        rcases hmem with ⟨y, hy, hy1⟩
        exact hnd.1 ⟨y, hy, hy1.trans hx.symm⟩
      rw [hx, walkFlow_eq_zero_of_not_mem hnotin, walkCount_eq_zero_of_not_mem hnotin]
      cases x.2 <;> simp
    · simp only [hx, ↓reduceIte, zero_add]
      exact ih hnd.2

lemma sum_walkCount_le_length (S : Finset ℕ) (P : List (ℕ × Bool)) :
    ∑ e' ∈ S, walkCount P e' ≤ (P.length : ℝ) := by
  induction P with
  | nil => simp [walkCount_nil]
  | cons x P ih =>
    simp only [List.length_cons, Nat.cast_succ]
    calc
      ∑ e' ∈ S, walkCount (x :: P) e'
          = ∑ e' ∈ S, ((if x.1 = e' then (1 : ℝ) else 0) + walkCount P e') :=
            Finset.sum_congr rfl fun e' _ => walkCount_cons x P e'
      _ = (∑ e' ∈ S, if x.1 = e' then (1 : ℝ) else 0) + ∑ e' ∈ S, walkCount P e' :=
            Finset.sum_add_distrib
      _ ≤ 1 + (P.length : ℝ) := by
            refine add_le_add ?_ ih
            by_cases hx : x.1 ∈ S
            · rw [Finset.sum_eq_single x.1]
              · simp
              · intro e' _ hne; simp [Ne.symm hne]
              · intro hn; exact absurd hx hn
            · rw [Finset.sum_eq_zero]
              · norm_num
              · intro e' he'
                have hne : x.1 ≠ e' := fun h => hx (h ▸ he')
                simp [hne]
      _ = (P.length : ℝ) + 1 := add_comm _ _

lemma walkCount_sublist {P Q : List (ℕ × Bool)} (h : P.Sublist Q) (e' : ℕ) :
    walkCount P e' ≤ walkCount Q e' :=
  Nat.cast_le.mpr (List.Sublist.countP_le h)

lemma walkInner_eq_sum_of_subset {x : ℕ → ℝ} {P : List (ℕ × Bool)} {S : Finset ℕ}
    (hsub : walkEdges P ⊆ S) :
    walkInner x P = ∑ e ∈ S, x e * walkFlow P e := by
  unfold walkInner
  refine Finset.sum_subset hsub ?_
  intro e _ hnot
  rw [walkFlow_eq_zero_of_not_mem hnot, mul_zero]

lemma walkLength_eq_sum_of_subset {ℓ : ℕ → ℝ} {P : List (ℕ × Bool)} {S : Finset ℕ}
    (hsub : walkEdges P ⊆ S) :
    walkLength ℓ P = ∑ e ∈ S, ℓ e * |walkFlow P e| := by
  unfold walkLength
  refine Finset.sum_subset hsub ?_
  intro e _ hnot
  rw [walkFlow_eq_zero_of_not_mem hnot, abs_zero, mul_zero]

lemma walkInner_append (x : ℕ → ℝ) (P Q : List (ℕ × Bool)) :
    walkInner x (P ++ Q) = walkInner x P + walkInner x Q := by
  have hP : walkEdges P ⊆ walkEdges (P ++ Q) := by rw [walkEdges_append]; exact Finset.subset_union_left
  have hQ : walkEdges Q ⊆ walkEdges (P ++ Q) := by rw [walkEdges_append]; exact Finset.subset_union_right
  rw [walkInner_eq_sum_of_subset hP, walkInner_eq_sum_of_subset hQ]
  unfold walkInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [walkFlow_append, mul_add]

lemma walkInner_walkRev (x : ℕ → ℝ) (P : List (ℕ × Bool)) :
    walkInner x (walkRev P) = -walkInner x P := by
  simp only [walkInner, walkEdges_walkRev, walkFlow_walkRev, mul_neg, Finset.sum_neg_distrib]

lemma walkInner_nil (x : ℕ → ℝ) : walkInner x [] = 0 := by
  simp [walkInner, walkEdges]

lemma walkLength_nil (ℓ : ℕ → ℝ) : walkLength ℓ [] = 0 := by
  simp [walkLength, walkEdges]

lemma walkInner_singleton (x : ℕ → ℝ) (y : ℕ × Bool) :
    walkInner x [y] = if y.2 then x y.1 else -x y.1 := by
  simp only [walkInner, walkEdges, List.map_cons, List.map_nil, List.toFinset_cons,
    List.toFinset_nil, insert_empty_eq, Finset.sum_singleton, walkFlow_cons, walkFlow_nil,
    add_zero, ↓reduceIte]
  cases y.2 <;> simp

lemma demand_walkFlow {G : MGraph} {u v : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u v P) (x : ℕ) :
    G.demand (walkFlow P) x = (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
  induction hP with
  | nil z => simp [MGraph.demand, walkFlow]
  | @cons u v y P he hsrc _ ih =>
    simp only [MGraph.demand] at ih ⊢
    have hstep : ∀ e ∈ G.E,
        G.b e x * walkFlow (y :: P) e =
          G.b e x * (if y.1 = e then (if y.2 then (1 : ℝ) else -1) else 0) +
          G.b e x * walkFlow P e := by
      intro e _
      rw [walkFlow_cons, mul_add]
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ih]
    have hsingle :
        ∑ e ∈ G.E, G.b e x * (if y.1 = e then (if y.2 then (1 : ℝ) else -1) else 0) =
          G.b y.1 x * (if y.2 then (1 : ℝ) else -1) := by
      rw [Finset.sum_eq_single y.1]
      · simp
      · intro e _ hne
        simp [Ne.symm hne]
      · intro hnot; exact absurd he hnot
    rw [hsingle]
    have hbd :
        G.b y.1 x * (if y.2 then (1 : ℝ) else -1) =
          (if x = u then (1 : ℝ) else 0) - (if x = G.dst y then (1 : ℝ) else 0) := by
      rw [← hsrc]
      cases hy2 : y.2 <;> simp [MGraph.b, MGraph.src, MGraph.dst, hy2]
    rw [hbd]
    ring

lemma isCirculation_walkFlow_of_closed {G : MGraph} {u : ℕ} {P : List (ℕ × Bool)}
    (hP : G.IsWalk u u P) : G.IsCirculation (walkFlow P) := by
  intro x _
  rw [demand_walkFlow hP x, sub_self]

end WalkFlow

namespace MGraph

private lemma isPath_suffix_of_split {G : MGraph} {u v w : ℕ} {P₁ P₂ : List (ℕ × Bool)}
    (hP : G.IsPath u v (P₁ ++ P₂)) (hW1 : G.IsWalk u w P₁) (hW2 : G.IsWalk w v P₂) :
    G.IsPath w v P₂ := by
  refine ⟨hW2, ?_⟩
  have hnd := hP.2
  rw [walkVertices_append] at hnd
  have hsub := List.Nodup.of_append_right hnd
  have hlast : (G.walkVertices u P₁).getLast (by simp [MGraph.walkVertices]) = w :=
    walkVertices_last hW1
  -- `w :: P₂.map G.dst` is a suffix of `(G.walkVertices u P₁) ++ P₂.map G.dst`
  have hcons : ∃ l, G.walkVertices u P₁ = l ++ [w] := by
    refine ⟨(G.walkVertices u P₁).dropLast, ?_⟩
    conv_lhs => rw [← List.dropLast_append_getLast (l := G.walkVertices u P₁) (by simp [MGraph.walkVertices])]
    rw [hlast]
  obtain ⟨l, hl⟩ := hcons
  rw [hl, List.append_assoc, List.singleton_append] at hnd
  exact List.Nodup.of_append_right hnd

private lemma mem_edges_of_path_two_endpoints {F : MGraph} {w v e' : ℕ} {P₂ : List (ℕ × Bool)}
    (hP2 : F.IsPath w v P₂) (hlen : 2 ≤ P₂.length) (hwv : w ≠ v)
    (htail : F.tail e' = v ∨ F.head e' = v) (hother : (if F.tail e' = v then F.head e' else F.tail e') = w)
    (he' : ∃ y ∈ P₂, y.1 = e') : False := by
  obtain ⟨y, hyP2, hye'⟩ := he'
  rcases hP2 with ⟨hW2, hnd⟩
  -- Compare indices in `P₂` and `F.walkVertices w P₂`
  obtain ⟨i, hi, hyget⟩ := List.getElem_of_mem hyP2
  have hvw_step : ∀ {a b : ℕ} {Q : List (ℕ × Bool)}, F.IsWalk a b Q →
      ∀ (k : ℕ) (hk : k < Q.length),
        (F.walkVertices a Q)[k]'(by simp [MGraph.walkVertices]; omega) = F.src (Q[k]'hk) ∧
        (F.walkVertices a Q)[k + 1]'(by simp [MGraph.walkVertices]; omega) = F.dst (Q[k]'hk) := by
    intro a b Q hQ
    induction hQ with
    | nil _ => intro k hk; cases hk
    | @cons a b z Q _ hsrcz _ ihQ =>
      intro k hk
      cases k with
      | zero =>
        simp [MGraph.walkVertices, hsrcz]
      | succ k' =>
        have hk' : k' < Q.length := by simpa using hk
        simpa [MGraph.walkVertices] using ihQ k' hk'
  have hpair := hvw_step hW2 i hi
  have h1 : (F.walkVertices w P₂)[i]'(by simp [MGraph.walkVertices]; omega) = F.src y := by
    simpa [hyget] using hpair.1
  have h2 : (F.walkVertices w P₂)[i + 1]'(by simp [MGraph.walkVertices]; omega) = F.dst y := by
    simpa [hyget] using hpair.2
  have hlast_idx : (F.walkVertices w P₂)[P₂.length]'(by simp [MGraph.walkVertices]) = v := by
    have hgl := walkVertices_last hW2
    rw [List.getLast_eq_getElem] at hgl
    simpa [MGraph.walkVertices] using hgl
  have h0_idx : (F.walkVertices w P₂)[0]'(by simp [MGraph.walkVertices]) = w := by
    simp [MGraph.walkVertices]
  have hnd_inj := List.nodup_iff_injective_getElem.mp hnd
  have hends : (F.src y = v ∧ F.dst y = w) ∨ (F.src y = w ∧ F.dst y = v) := by
    rcases htail with htv | hhv
    · have hwh : F.head e' = w := by simpa [htv] using hother
      cases hy2 : y.2 <;> simp [MGraph.src, MGraph.dst, hye', htv, hwh, hy2]
    · have hwt : F.tail e' = w := by
        by_cases htv : F.tail e' = v
        · exfalso; simp [htv] at hother; exact hwv (hother.symm.trans hhv)
        · simpa [htv] using hother
      cases hy2 : y.2 <;> simp [MGraph.src, MGraph.dst, hye', hhv, hwt, hy2]
  rcases hends with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · have hi_eq : i = P₂.length := by
      have hfin : (⟨i, by simp [MGraph.walkVertices]; omega⟩ : Fin (F.walkVertices w P₂).length) =
          ⟨P₂.length, by simp [MGraph.walkVertices]⟩ :=
        hnd_inj (by simp [h1, hs, hlast_idx])
      exact Fin.mk.inj hfin
    omega
  · have hi_zero : i = 0 := by
      have hfin : (⟨i, by simp [MGraph.walkVertices]; omega⟩ : Fin (F.walkVertices w P₂).length) =
          ⟨0, by simp [MGraph.walkVertices]⟩ :=
        hnd_inj (by simp [h1, hs, h0_idx])
      exact Fin.mk.inj hfin
    have hi1_last : i + 1 = P₂.length := by
      have hfin : (⟨i + 1, by simp [MGraph.walkVertices]; omega⟩ : Fin (F.walkVertices w P₂).length) =
          ⟨P₂.length, by simp [MGraph.walkVertices]⟩ :=
        hnd_inj (by simp [h2, hd, hlast_idx])
      exact Fin.mk.inj hfin
    omega

theorem isCirculation_eq_zero_of_isForest {F : MGraph} (hF : F.IsForest) {f : ℕ → ℝ}
    (hf : F.IsCirculation f) : ∀ e ∈ F.E, f e = 0 := by
  classical
  let S : Finset ℕ := F.E.filter (fun e => f e ≠ 0)
  suffices hEmpty : S = ∅ by
    intro e he
    by_contra hne
    have hmem : e ∈ S := Finset.mem_filter.mpr ⟨he, hne⟩
    rw [hEmpty] at hmem
    exact Finset.notMem_empty e hmem
  by_contra hS
  obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
  have he₀E : e₀ ∈ F.E := (Finset.mem_filter.mp he₀).1
  have hdeg2 : ∀ v ∈ F.V, (S.filter (fun e => F.tail e = v ∨ F.head e = v)).Nonempty →
      2 ≤ (S.filter (fun e => F.tail e = v ∨ F.head e = v)).card := by
    intro v hv hne
    by_contra hlt
    have hcard1 : (S.filter (fun e => F.tail e = v ∨ F.head e = v)).card = 1 := by
      have hpos := Finset.Nonempty.card_pos hne
      omega
    obtain ⟨e, he_eq⟩ := Finset.card_eq_one.mp hcard1
    have he_mem : e ∈ S.filter (fun e => F.tail e = v ∨ F.head e = v) := by rw [he_eq]; simp
    have heS : e ∈ S := (Finset.mem_filter.mp he_mem).1
    have heE : e ∈ F.E := (Finset.mem_filter.mp heS).1
    have hfne : f e ≠ 0 := (Finset.mem_filter.mp heS).2
    have heInc : F.tail e = v ∨ F.head e = v := (Finset.mem_filter.mp he_mem).2
    have hnoLoop : F.tail e ≠ F.head e := no_selfLoop_of_isForest hF heE
    have hdem := hf v hv
    simp only [MGraph.demand] at hdem
    have hsingle : ∑ e' ∈ F.E, F.b e' v * f e' = F.b e v * f e := by
      rw [Finset.sum_eq_single e]
      · intro e' he'E hne'
        by_cases hf0 : f e' = 0
        · simp [hf0]
        · have he'S : e' ∈ S := Finset.mem_filter.mpr ⟨he'E, hf0⟩
          have hnotInc : ¬ (F.tail e' = v ∨ F.head e' = v) := by
            intro hinc
            have hmem' : e' ∈ S.filter (fun e => F.tail e = v ∨ F.head e = v) :=
              Finset.mem_filter.mpr ⟨he'S, hinc⟩
            rw [he_eq, Finset.mem_singleton] at hmem'
            exact hne' hmem'
          push Not at hnotInc
          rw [b_eq_zero_of_ne F hnotInc.1.symm hnotInc.2.symm, zero_mul]
      · intro hnot; exact absurd heE hnot
    rw [hsingle] at hdem
    have hbne : F.b e v ≠ 0 := by
      rcases heInc with h1 | h2
      · have : v ≠ F.head e := fun h => hnoLoop (h1.trans h)
        simp [MGraph.b, h1, this]
      · have : v ≠ F.tail e := fun h => hnoLoop (h.symm.trans h2.symm)
        simp [MGraph.b, h2, this]
    exact hfne (mul_eq_zero.mp hdem |>.resolve_left hbne)
  -- No GoodPath can exist by induction on `F.V.card - P.length`
  have hNoGood : ∀ m u v (P : List (ℕ × Bool)),
      F.IsPath u v P → P ≠ [] → (∀ x ∈ P, x.1 ∈ S) → F.V.card - P.length ≤ m → False := by
    intro m
    induction m with
    | zero =>
      intro u v P hP hPne hPS hm
      have hu : u ∈ F.V := (isWalk_src_mem hF.1 hP.1 hPne).1
      have hsub : (F.walkVertices u P).toFinset ⊆ F.V := by
        intro w hw
        exact walkVertices_edges_mem_V hF.1 hP.1 hu w (List.mem_toFinset.mp hw)
      have hlen : (F.walkVertices u P).length ≤ F.V.card := by
        rw [← List.toFinset_card_of_nodup hP.2]
        exact Finset.card_le_card hsub
      simp only [MGraph.walkVertices, List.length_cons, List.length_map] at hlen
      omega
    | succ m ih =>
      intro u v P hP hPne hPS hm
      have hsrcv := isWalk_src_mem hF.1 hP.1 hPne
      have hv : v ∈ F.V := hsrcv.2
      -- Find the last step of `P`
      have hexLast : ∃ P_init x_last, P = P_init ++ [x_last] :=
        ⟨P.dropLast, P.getLast hPne, (List.dropLast_append_getLast hPne).symm⟩
      obtain ⟨P_init, x_last, hPeq⟩ := hexLast
      have hxLastMem : x_last ∈ P := by rw [hPeq]; simp
      have hxLastS : x_last.1 ∈ S := hPS x_last hxLastMem
      have hxLastE : x_last.1 ∈ F.E := (Finset.mem_filter.mp hxLastS).1
      have hdstLast : F.dst x_last = v := by
        have hgl := walkVertices_last hP.1
        have hgl2 : (F.walkVertices u (P_init ++ [x_last])).getLast (by simp [MGraph.walkVertices]) =
            F.dst x_last := by
          simp [MGraph.walkVertices]
        rw [← hgl2]
        simpa [hPeq] using hgl
      have hxLastInc : F.tail x_last.1 = v ∨ F.head x_last.1 = v := by
        rw [← hdstLast]
        cases hdir : x_last.2 <;> simp [MGraph.dst, hdir]
      have hincV : 2 ≤ (S.filter (fun e => F.tail e = v ∨ F.head e = v)).card :=
        hdeg2 v hv ⟨x_last.1, Finset.mem_filter.mpr ⟨hxLastS, hxLastInc⟩⟩
      obtain ⟨e', he'Mem, he'Ne⟩ :=
        Finset.exists_mem_ne (by omega : 1 < (S.filter (fun e => F.tail e = v ∨ F.head e = v)).card)
          x_last.1
      have he'S : e' ∈ S := (Finset.mem_filter.mp he'Mem).1
      have he'E : e' ∈ F.E := (Finset.mem_filter.mp he'S).1
      have he'Inc : F.tail e' = v ∨ F.head e' = v := (Finset.mem_filter.mp he'Mem).2
      let x' : ℕ × Bool := if F.tail e' = v then (e', true) else (e', false)
      have hx'Fst : x'.1 = e' := by dsimp [x']; split_ifs <;> rfl
      have hx'Src : F.src x' = v := by
        dsimp [x']
        split_ifs with h
        · simp [MGraph.src, h]
        · have h' : F.head e' = v := he'Inc.resolve_left h
          simp [MGraph.src, h']
      let w : ℕ := F.dst x'
      have hnoLoop' : F.tail e' ≠ F.head e' := no_selfLoop_of_isForest hF he'E
      have hwNeV : w ≠ v := by
        dsimp [w, x']
        split_ifs with h
        · simp only [MGraph.dst, ↓reduceIte]
          exact fun hEq => hnoLoop' (h.trans hEq.symm)
        · simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte]
          exact fun hEq => hnoLoop' (hEq.trans (he'Inc.resolve_left h).symm)
      by_cases hwMem : w ∈ F.walkVertices u P
      · obtain ⟨P₁, P₂, hsplit, hW1, hW2⟩ := isWalk_split_of_mem_walkVertices hP.1 hwMem
        have hP2ne : P₂ ≠ [] := by
          intro hnil
          rw [hnil] at hW2
          exact hwNeV (isWalk_nil_eq hW2)
        have hP2path : F.IsPath w v P₂ := isPath_suffix_of_split (hsplit ▸ hP) hW1 hW2
        have hP2edgeNd : (P₂.map Prod.fst).Nodup := isPath_edges_nodup hP2path
        have he'NotInP2 : e' ∉ P₂.map Prod.fst := by
          intro hmem
          rw [List.mem_map] at hmem
          by_cases hlen1 : P₂.length = 1
          · obtain ⟨y, hyP2, hye'⟩ := hmem
            have hP2last : P₂.getLast hP2ne = x_last := by
              have hP_last : P.getLast hPne = x_last := by
                have hgl := List.getLast_append_singleton (a := x_last) (l := P_init)
                convert hgl using 2
              have hP_last2 : P.getLast hPne = P₂.getLast hP2ne := by
                have hgl : (P₁ ++ P₂).getLast (by simp [hP2ne]) = P₂.getLast hP2ne := by
                  simp [List.getLast_append_of_ne_nil, hP2ne]
                convert hgl using 2
              exact hP_last2.symm.trans hP_last
            obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp hlen1
            have hzx : z = x_last := by simpa [hz] using hP2last
            rw [hz, hzx, List.mem_singleton] at hyP2
            rw [hyP2] at hye'
            exact he'Ne hye'.symm
          · have hlen2 : 2 ≤ P₂.length := by
              have : P₂.length ≠ 0 := (List.length_pos_of_ne_nil hP2ne).ne'
              omega
            have hwEq : (if F.tail e' = v then F.head e' else F.tail e') = w := by
              dsimp [w, x']
              split_ifs <;> simp [MGraph.dst]
            exact mem_edges_of_path_two_endpoints hP2path hlen2 hwNeV he'Inc hwEq hmem
        apply hF.2 (P₂ ++ [x'])
        refine ⟨by simp, ?_, w, isWalk_append hW2 (.cons (hx'Fst ▸ he'E) hx'Src (.nil w))⟩
        rw [List.map_append, List.map_cons, List.map_nil, hx'Fst, List.nodup_append]
        refine ⟨hP2edgeNd, List.nodup_singleton e', ?_⟩
        intro a ha b hb heq
        rw [List.mem_singleton] at hb
        subst hb heq
        exact he'NotInP2 ha
      · have hP' : F.IsPath u w (P ++ [x']) :=
          isPath_append_right_mem_walkVertices hP hwMem (hx'Fst ▸ he'E) hx'Src rfl
        have hP'S : ∀ x ∈ P ++ [x'], x.1 ∈ S := by
          intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hPS x hx
          · rw [hx'Fst]; exact he'S
        have hu' : u ∈ F.V := hsrcv.1
        have hsub' : (F.walkVertices u (P ++ [x'])).toFinset ⊆ F.V := by
          intro z hz
          exact walkVertices_edges_mem_V hF.1 hP'.1 hu' z (List.mem_toFinset.mp hz)
        have hlen' : (F.walkVertices u (P ++ [x'])).length ≤ F.V.card := by
          rw [← List.toFinset_card_of_nodup hP'.2]
          exact Finset.card_le_card hsub'
        simp only [MGraph.walkVertices, List.length_cons, List.length_map, List.length_append] at hlen'
        have hm' : F.V.card - (P ++ [x']).length ≤ m := by
          simp only [List.length_append, List.length_singleton]
          omega
        exact ih u w (P ++ [x']) hP' (by simp) hP'S hm'
  -- Apply `hNoGood` to `[(e₀, true)]`
  have hno0 : F.tail e₀ ≠ F.head e₀ := no_selfLoop_of_isForest hF he₀E
  have hP0 : F.IsPath (F.tail e₀) (F.head e₀) [(e₀, true)] := by
    refine ⟨.cons he₀E rfl (.nil (F.head e₀)), ?_⟩
    simp [MGraph.walkVertices, MGraph.dst, hno0]
  exact hNoGood (F.V.card - 1) (F.tail e₀) (F.head e₀) [(e₀, true)] hP0 (by simp)
    (by simp [he₀]) (by simp)

end MGraph

section ForestFlows

lemma walkFlow_eq_zero_of_isForest_closed {F : MGraph} (hF : F.IsForest) {u : ℕ}
    {P : List (ℕ × Bool)} (hP : F.IsWalk u u P) (e : ℕ) : walkFlow P e = 0 := by
  by_cases he : e ∈ F.E
  · exact MGraph.isCirculation_eq_zero_of_isForest hF (isCirculation_walkFlow_of_closed hP) e he
  · refine walkFlow_eq_zero_of_not_mem ?_
    intro hmem
    rw [walkEdges, List.mem_toFinset, List.mem_map] at hmem
    obtain ⟨x, hx, rfl⟩ := hmem
    exact he (MGraph.isWalk_edges_mem hP x hx)

lemma walkFlow_eq_of_isForest {F : MGraph} (hF : F.IsForest) {u v : ℕ} {P Q : List (ℕ × Bool)}
    (hP : F.IsWalk u v P) (hQ : F.IsWalk u v Q) (e : ℕ) : walkFlow P e = walkFlow Q e := by
  have hclosed : F.IsWalk u u (P ++ walkRev Q) :=
    MGraph.isWalk_append hP (MGraph.isWalk_walkRev hQ)
  have h0 := walkFlow_eq_zero_of_isForest_closed hF hclosed e
  rw [walkFlow_append, walkFlow_walkRev] at h0
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using h0)

lemma walkFlow_forestPath_add {F : MGraph} (hF : F.IsForest) {u v w : ℕ}
    (huv : F.Connected u v) (hvw : F.Connected v w) (e : ℕ) :
    walkFlow (MGraph.forestPath F u v) e + walkFlow (MGraph.forestPath F v w) e =
      walkFlow (MGraph.forestPath F u w) e := by
  have huw : F.Connected u w := MGraph.connected_trans huv hvw
  have h1 := MGraph.isWalk_forestPath huv
  have h2 := MGraph.isWalk_forestPath hvw
  have h3 := MGraph.isWalk_forestPath huw
  rw [← walkFlow_append]
  exact walkFlow_eq_of_isForest hF (MGraph.isWalk_append h1 h2) h3 e

lemma walkFlow_forestPath_walkRev {F : MGraph} (hF : F.IsForest) {u v : ℕ}
    (huv : F.Connected u v) (e : ℕ) :
    walkFlow (MGraph.forestPath F v u) e = -walkFlow (MGraph.forestPath F u v) e := by
  have hvu : F.Connected v u := MGraph.connected_symm huv
  rw [← walkFlow_walkRev]
  exact walkFlow_eq_of_isForest hF (MGraph.isWalk_forestPath hvu)
    (MGraph.isWalk_walkRev (MGraph.isWalk_forestPath huv)) e

lemma walkLength_forestPath_symm {F : MGraph} (hF : F.IsForest) {u v : ℕ}
    (huv : F.Connected u v) (ℓ : ℕ → ℝ) :
    walkLength ℓ (MGraph.forestPath F v u) = walkLength ℓ (MGraph.forestPath F u v) := by
  have hvu : F.Connected v u := MGraph.connected_symm huv
  have hsub1 : walkEdges (MGraph.forestPath F v u) ⊆ F.E := by
    intro e he
    rw [walkEdges, List.mem_toFinset, List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    exact MGraph.isWalk_edges_mem (MGraph.isWalk_forestPath hvu) x hx
  have hsub2 : walkEdges (MGraph.forestPath F u v) ⊆ F.E := by
    intro e he
    rw [walkEdges, List.mem_toFinset, List.mem_map] at he
    obtain ⟨x, hx, rfl⟩ := he
    exact MGraph.isWalk_edges_mem (MGraph.isWalk_forestPath huv) x hx
  rw [walkLength_eq_sum_of_subset hsub1, walkLength_eq_sum_of_subset hsub2]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [walkFlow_forestPath_walkRev hF huv e, abs_neg]

end ForestFlows

end MinCostFlow
