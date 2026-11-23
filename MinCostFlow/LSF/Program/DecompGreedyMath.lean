module

public import MinCostFlow.LSF.Program.SubtreeSumMath
public import MinCostFlow.LSF.Program.DecompOnline

/-!
# The greedy pass over the vertex indices

`decompGreedyProc` (`DecompGreedy.lean`) walks the top-down order `Q` from the back. At a
vertex index `x` with parent `p` it fixes the weight `s x = ν x + cur x` of the open bag of `x`
(all children of `x` come after `x` in `Q`, so they are done) and hands `x` to the greedy
batching of `p`: `x` gets the batch number `nb p`, and the batch is closed when its sum reaches
`θ`.

`GreedyState` is the loop invariant after the positions `j, j + 1, …` of `Q` are done: for every
index `u`, the children of `u` that are done were handled one at a time in the order of the walk
(`OnlineRun`), and every done index has its weight. `greedyState_step` is one step of the walk.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow.LSF.Program.DecompGen

variable {n r j : ℕ} {par : ℕ → ℕ} {Q : List ℕ}

/-- The children of `u` among the positions `j, j + 1, …` of `Q`, in the order of the walk from
the back. -/
def procChildren (Q : List ℕ) (par : ℕ → ℕ) (u j : ℕ) : List ℕ :=
  ((Q.drop j).reverse).filter (fun c => par c = u)

/-- The loop invariant of the greedy pass. -/
def GreedyState (Q : List ℕ) (par : ℕ → ℕ) (n θ : ℕ) (ν cur nb bidx s : ℕ → ℕ) (j : ℕ) : Prop :=
  (∀ u < n, OnlineRun (θ : ℝ) (fun c => (s c : ℝ)) bidx 0 0 (procChildren Q par u j) (nb u)
    (cur u : ℝ)) ∧
  (∀ x ∈ Q.drop j, s x = ν x + cur x) ∧
  (∀ u < n, cur u < θ)

lemma onlineRun_congr {α : Type*} {θ : ℝ} {f f' : α → ℝ} {b b' : α → ℕ} :
    ∀ (xs : List α) (nb : ℕ) (cur : ℝ) (nbF : ℕ) (curF : ℝ),
      (∀ x ∈ xs, f x = f' x ∧ b x = b' x) →
      OnlineRun θ f b nb cur xs nbF curF → OnlineRun θ f' b' nb cur xs nbF curF := by
  intro xs
  induction xs with
  | nil => intro nb cur nbF curF _ h; exact h
  | cons x xs ih =>
    intro nb cur nbF curF hfb h
    obtain ⟨hx, h⟩ := h
    obtain ⟨hf, hb⟩ := hfb x List.mem_cons_self
    have hxs : ∀ y ∈ xs, f y = f' y ∧ b y = b' y := fun y hy => hfb y (List.mem_cons_of_mem _ hy)
    refine ⟨hb ▸ hx, ?_⟩
    rw [← hf]
    split_ifs at h ⊢ <;> exact ih _ _ _ _ hxs h

lemma onlineRun_nb_le {α : Type*} {θ : ℝ} {f : α → ℝ} {b : α → ℕ} :
    ∀ (xs : List α) (nb : ℕ) (cur : ℝ) (nbF : ℕ) (curF : ℝ),
      OnlineRun θ f b nb cur xs nbF curF → nbF ≤ nb + xs.length := by
  intro xs
  induction xs with
  | nil => intro nb cur nbF curF h; obtain ⟨rfl, -⟩ := h; simp
  | cons x xs ih =>
    intro nb cur nbF curF h
    obtain ⟨-, h⟩ := h
    split_ifs at h
    · have := ih _ _ _ _ h; simp only [List.length_cons]; omega
    · have := ih _ _ _ _ h; simp only [List.length_cons]; omega

lemma procChildren_length_lt (hQ : TopDownOrder n r par Q) (u j : ℕ) (hj : 1 ≤ j)
    (hn : 0 < n) : (procChildren Q par u j).length < n := by
  unfold procChildren
  have h1 := List.length_filter_le (fun c => decide (par c = u)) (Q.drop j).reverse
  rw [List.length_reverse, List.length_drop, hQ.len] at h1
  omega

lemma drop_pred_eq (hj : 1 ≤ j) (hjQ : j ≤ Q.length) :
    Q.drop (j - 1) = Q[j - 1]'(by omega) :: Q.drop j := by
  have := List.drop_eq_getElem_cons (show j - 1 < Q.length by omega)
  rw [this, show j - 1 + 1 = j by omega]

lemma procChildren_pred (hj : 1 ≤ j) (hjQ : j ≤ Q.length) (u : ℕ) :
    procChildren Q par u (j - 1) =
      procChildren Q par u j ++ (if par (Q[j - 1]'(by omega)) = u then [Q[j - 1]'(by omega)]
        else []) := by
  unfold procChildren
  rw [drop_pred_eq hj hjQ, List.reverse_cons, List.filter_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]
  split_ifs <;> simp_all

/-- The invariant only looks at the indices below `n`. -/
lemma greedyState_congr (hQ : TopDownOrder n r par Q) {θ : ℕ} {ν cur nb bidx s cur' nb' bidx' s' : ℕ → ℕ}
    {j : ℕ} (hcur : ∀ u < n, cur u = cur' u) (hnb : ∀ u < n, nb u = nb' u)
    (hb : ∀ u < n, bidx u = bidx' u) (hs : ∀ u < n, s u = s' u)
    (hI : GreedyState Q par n θ ν cur nb bidx s j) :
    GreedyState Q par n θ ν cur' nb' bidx' s' j := by
  obtain ⟨hrun, hsx, hc⟩ := hI
  have hlt : ∀ u c, c ∈ procChildren Q par u j → c < n := fun u c hc =>
    hQ.lt c (List.mem_of_mem_drop (List.mem_reverse.mp (List.mem_filter.mp hc).1))
  refine ⟨fun u hu => ?_, fun x hx => ?_, fun u hu => ?_⟩
  · rw [← hnb u hu, ← hcur u hu]
    exact onlineRun_congr _ _ _ _ _ (fun c hcm => ⟨by rw [hs c (hlt u c hcm)],
      hb c (hlt u c hcm)⟩) (hrun u hu)
  · have hxn := hQ.lt x (List.mem_of_mem_drop hx)
    rw [← hs x hxn, ← hcur x hxn]; exact hsx x hx
  · rw [← hcur u hu]; exact hc u hu

/-- The start: nothing is done, and all counts and sums are `0`. -/
lemma greedyState_init (hQ : TopDownOrder n r par Q) {θ : ℕ} (hθ : 0 < θ) (ν bidx s : ℕ → ℕ) :
    GreedyState Q par n θ ν (fun _ => 0) (fun _ => 0) bidx s n := by
  refine ⟨fun u _ => ?_, fun x hx => ?_, fun u _ => hθ⟩
  · have : procChildren Q par u n = [] := by
      unfold procChildren; rw [← hQ.len, List.drop_length]; rfl
    rw [this]
    exact ⟨rfl, by simp⟩
  · rw [← hQ.len, List.drop_length] at hx; simp at hx

/-- One step of the greedy pass, at `x = Q[j - 1]` with parent `p`. -/
theorem greedyState_step (hQ : TopDownOrder n r par Q) {θ : ℕ} {ν cur nb bidx s : ℕ → ℕ}
    {j : ℕ} (hj : 2 ≤ j) (hjn : j ≤ n) (hI : GreedyState Q par n θ ν cur nb bidx s j) :
    let x := Q[j - 1]'(by rw [hQ.len]; omega)
    let p := par x
    let sx := ν x + cur x
    let c' := cur p + sx
    GreedyState Q par n θ ν
      (Function.update cur p (if c' < θ then c' else 0))
      (Function.update nb p (if c' < θ then nb p else nb p + 1))
      (Function.update bidx x (nb p))
      (Function.update s x sx) (j - 1) := by
  classical
  intro x p sx c'
  obtain ⟨hrun, hs, hcur⟩ := hI
  have hjQ : j ≤ Q.length := by rw [hQ.len]; exact hjn
  have hxQ : x ∈ Q := List.getElem_mem _
  have hxn : x < n := hQ.lt x hxQ
  have hxr : x ≠ r := by
    intro h
    have h0 := hQ.head_eq (by omega)
    have := (hQ.nodup.getElem_inj_iff (hi := by omega) (hj := by rw [hQ.len]; omega)).mp
      (h.trans h0.symm)
    omega
  have hpQ : p ∈ Q.take (j - 1) := hQ.after (j - 1) (by omega) hxr
  have hpn : p < n := hQ.lt p (List.mem_of_mem_take hpQ)
  -- `x` is not done yet, and `p` is not done after this step
  have hx_not : x ∉ Q.drop j := by
    intro h
    have hnd := hQ.nodup
    rw [← List.take_append_drop (j - 1) Q, drop_pred_eq (by omega) hjQ] at hnd
    have := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
    exact this h
  have hp_not : p ∉ Q.drop (j - 1) := by
    intro h
    have hnd := hQ.nodup
    rw [← List.take_append_drop (j - 1) Q] at hnd
    exact (List.nodup_append.mp hnd).2.2 p hpQ p h rfl
  have hpx : p ≠ x := by
    intro h
    apply hp_not
    rw [h, drop_pred_eq (by omega) hjQ]
    exact List.mem_cons_self
  have hnot_proc : ∀ u, x ∉ procChildren Q par u j := by
    intro u h
    unfold procChildren at h
    exact hx_not (List.mem_reverse.mp (List.mem_filter.mp h).1)
  refine ⟨fun u hu => ?_, fun y hy => ?_, fun u hu => ?_⟩
  · rw [procChildren_pred (by omega) hjQ u]
    have hcongr : ∀ c ∈ procChildren Q par u j,
        ((s c : ℝ)) = ((Function.update s x sx c : ℕ) : ℝ) ∧ bidx c = Function.update bidx x (nb p) c := by
      intro c hc
      have hcx : c ≠ x := fun h => hnot_proc u (h ▸ hc)
      exact ⟨by rw [Function.update_of_ne hcx], by rw [Function.update_of_ne hcx]⟩
    have hold := onlineRun_congr _ _ _ _ _ hcongr (hrun u hu)
    by_cases hpu : p = u
    · subst hpu
      have hif : (if par x = p then [x] else []) = [x] := ite_eq_left rfl
      change OnlineRun _ _ _ 0 0 (procChildren Q par p j ++ (if par x = p then [x] else [])) _ _
      rw [hif]
      refine onlineRun_append _ _ _ _ _ _ _ _ x _ _ hold ⟨by simp, ?_⟩
      simp only [Function.update_self]
      have hcast : ((cur p : ℕ) : ℝ) + ((sx : ℕ) : ℝ) = ((c' : ℕ) : ℝ) := by
        simp only [c']; push_cast; ring
      rw [hcast]
      by_cases hlt : c' < θ
      · rw [ite_eq_right (by exact_mod_cast not_le.mpr hlt), ite_eq_left hlt, ite_eq_left hlt]
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_left (by exact_mod_cast not_lt.mp hlt), ite_eq_right hlt, ite_eq_right hlt]
        exact ⟨rfl, by simp⟩
    · have hif : (if par x = u then [x] else []) = [] := ite_eq_right hpu
      change OnlineRun _ _ _ 0 0 (procChildren Q par u j ++ (if par x = u then [x] else [])) _ _
      rw [hif, List.append_nil]
      simp only [Function.update_of_ne (Ne.symm hpu)]
      exact hold
  · rw [drop_pred_eq (by omega) hjQ, List.mem_cons] at hy
    rcases hy with hy | hy
    · rw [hy]
      show Function.update s x sx x = ν x + Function.update cur p _ x
      rw [Function.update_self, Function.update_of_ne (Ne.symm hpx)]
    · have hyx : y ≠ x := fun h => hx_not (h ▸ hy)
      have hyp : y ≠ p := by
        intro h; apply hp_not; rw [drop_pred_eq (by omega) hjQ, ← h]
        exact List.mem_cons_of_mem _ hy
      simp only [Function.update_of_ne hyx, Function.update_of_ne hyp]
      exact hs y hy
  · by_cases hpu : u = p
    · rw [hpu]
      simp only [Function.update_self]
      split_ifs with h
      · exact h
      · exact lt_of_le_of_lt (Nat.zero_le _) (hcur p hpn)
    · simp only [Function.update_of_ne hpu]; exact hcur u hu

end MinCostFlow.LSF.Program

end
