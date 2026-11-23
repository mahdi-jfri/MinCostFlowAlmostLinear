module

public import MinCostFlow.LSF.Program.RootTreeBuild
import Mathlib.Tactic.Linarith

/-!
# Rooting a tree: the search state and one visit

During the breadth-first search of `rootTreeProc` the memory holds the queue `Q` of visited
vertices (in visiting order), a visited flag per vertex, and for each visited vertex its parent,
its parent edge and its depth. `RTCore` states these facts. The main lemma, `rtVisit_runs`,
shows that the visit step `rtVisit` keeps `RTCore`: a vertex `x` reached from a visited `u`
along edge `f` is either already in `Q`, or it is appended with parent `u`, parent edge `f`
and depth one more than that of `u`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-- Edge `f` joins `x` and `y`, in either direction. -/
def RTJoin (tl hd : ℕ → ℕ) (f x y : ℕ) : Prop :=
  (tl f = x ∧ hd f = y) ∨ (tl f = y ∧ hd f = x)

/-- The facts the search records for a visited vertex `x`: its depth is below the queue length;
the root is its own parent at depth `0`; any other vertex has a visited parent joined to it by
its parent edge, one level up. -/
def RTGood (n m r outPtr : ℕ) (tl hd : ℕ → ℕ) (Q : List ℕ) (mem : ℕ → ℕ) (x : ℕ) : Prop :=
  mem (outPtr + n + n + x) < Q.length ∧
  (x = r → mem (outPtr + x) = r ∧ mem (outPtr + n + n + x) = 0) ∧
  (x ≠ r → mem (outPtr + x) ∈ Q ∧ mem (outPtr + n + x) < m ∧
    RTJoin tl hd (mem (outPtr + n + x)) x (mem (outPtr + x)) ∧
    mem (outPtr + n + n + x) = mem (outPtr + n + n + mem (outPtr + x)) + 1)

/-- The memory during the search, with queue `Q`: the queue cells, the visited flags, the
records of visited vertices, and the cells outside the search arrays equal those of `m₁`. -/
structure RTCore (n m r outPtr sPtr : ℕ) (tl hd : ℕ → ℕ) (m₁ : ℕ → ℕ) (Q : List ℕ)
    (mem : ℕ → ℕ) : Prop where
  q : ∀ j (hj : j < Q.length), mem (sPtr + n + 2 * m + n + j) = Q[j]
  nd : Q.Nodup
  lt : ∀ x ∈ Q, x < n
  head : Q[0]? = some r
  vis : ∀ x < n, mem (sPtr + n + 2 * m + x) = if x ∈ Q then 1 else 0
  good : ∀ x ∈ Q, RTGood n m r outPtr tl hd Q mem x
  fr : ∀ a, (a < outPtr ∨ (outPtr + 3 * n ≤ a ∧ a < sPtr + n + 2 * m) ∨
    sPtr + n + 2 * m + n + n ≤ a) → mem a = m₁ a
  /-- The parent of each vertex comes before it in the queue. -/
  po : ∀ j (hj : j < Q.length), Q[j] ≠ r → mem (outPtr + Q[j]) ∈ Q.take j

lemma RTCore.length_le {n m r outPtr sPtr : ℕ} {tl hd : ℕ → ℕ} {m₁ : ℕ → ℕ} {Q : List ℕ}
    {mem : ℕ → ℕ} (hc : RTCore n m r outPtr sPtr tl hd m₁ Q mem) : Q.length ≤ n := by
  have h := Finset.card_le_card (s := Q.toFinset) (t := Finset.range n) (fun x hx =>
    Finset.mem_range.mpr (hc.lt x (List.mem_toFinset.mp hx)))
  rwa [List.toFinset_card_of_nodup hc.nd, Finset.card_range] at h

lemma RTCore.length_lt {n m r outPtr sPtr : ℕ} {tl hd : ℕ → ℕ} {m₁ : ℕ → ℕ} {Q : List ℕ}
    {mem : ℕ → ℕ} (hc : RTCore n m r outPtr sPtr tl hd m₁ Q mem) {x : ℕ} (hx : x < n)
    (hxQ : x ∉ Q) : Q.length < n := by
  have hsub : insert x Q.toFinset ⊆ Finset.range n := by
    intro z hz
    rw [Finset.mem_insert, List.mem_toFinset] at hz
    rcases hz with rfl | hz
    · exact Finset.mem_range.mpr hx
    · exact Finset.mem_range.mpr (hc.lt z hz)
  have h := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simpa using hxQ), List.toFinset_card_of_nodup hc.nd,
    Finset.card_range] at h
  omega

lemma RTCore.r_mem {n m r outPtr sPtr : ℕ} {tl hd : ℕ → ℕ} {m₁ : ℕ → ℕ} {Q : List ℕ}
    {mem : ℕ → ℕ} (hc : RTCore n m r outPtr sPtr tl hd m₁ Q mem) : r ∈ Q :=
  List.mem_of_getElem? hc.head

/-- Appending a new vertex `x` with parent `u` and parent edge `f` keeps `RTCore`. -/
lemma RTCore.push {n m r outPtr sPtr : ℕ} {tl hd : ℕ → ℕ} {m₁ : ℕ → ℕ} {Q : List ℕ}
    {mem : ℕ → ℕ} (hc : RTCore n m r outPtr sPtr tl hd m₁ Q mem) (hout : outPtr + 3 * n ≤ sPtr)
    {u x f : ℕ} (hu : u ∈ Q) (hx : x < n) (hxQ : x ∉ Q) (hf : f < m)
    (hj : RTJoin tl hd f x u) :
    let mem' := Function.update (Function.update (Function.update (Function.update
      (Function.update mem (sPtr + n + 2 * m + x) 1) (sPtr + n + 2 * m + n + Q.length) x)
      (outPtr + x) u) (outPtr + n + x) f) (outPtr + n + n + x)
      (mem (outPtr + n + n + u) + 1)
    RTCore n m r outPtr sPtr tl hd m₁ (Q ++ [x]) mem' := by
  intro mem'
  have hlt := hc.length_lt hx hxQ
  have hun := hc.lt u hu
  have hxr : x ≠ r := fun h => hxQ (h ▸ hc.r_mem)
  -- cells of `mem'`
  have hD : ∀ y, y < n → y ≠ x → mem' (outPtr + n + n + y) = mem (outPtr + n + n + y) := by
    intro y hy hyx
    simp only [mem']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  have hP : ∀ y, y < n → y ≠ x → mem' (outPtr + y) = mem (outPtr + y) := by
    intro y hy hyx
    simp only [mem']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  have hE : ∀ y, y < n → y ≠ x → mem' (outPtr + n + y) = mem (outPtr + n + y) := by
    intro y hy hyx
    simp only [mem']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  have hDx : mem' (outPtr + n + n + x) = mem (outPtr + n + n + u) + 1 := by
    simp only [mem', Function.update_self]
  have hPx : mem' (outPtr + x) = u := by
    simp only [mem']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  have hEx : mem' (outPtr + n + x) = f := by
    simp only [mem']
    rw [Function.update_of_ne (by omega), Function.update_self]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    by_cases hjl : j < Q.length
    · rw [List.getElem_append_left hjl, ← hc.q j hjl]
      simp only [mem']
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
    · have hje : j = Q.length := by simp at hj; omega
      subst hje
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.sub_self, List.getElem_cons_zero, mem']
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
  · exact List.nodup_append.mpr ⟨hc.nd, List.nodup_singleton _, fun a ha b hb => by
      simp only [List.mem_singleton] at hb; subst hb; intro h; subst h; exact hxQ ha⟩
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hc.lt y hy
    · simp only [List.mem_singleton] at hy; subst hy; exact hx
  · rw [List.getElem?_append_left (by have := hc.r_mem; exact List.length_pos_of_mem this)]
    exact hc.head
  · intro y hy
    simp only [mem']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    by_cases hyx : y = x
    · subst hyx; simp
    · rw [Function.update_of_ne (by omega), hc.vis y hy]
      simp [hyx]
  · intro y hy
    simp only [RTGood, List.length_append, List.length_singleton]
    rcases List.mem_append.mp hy with hyQ | hyx
    · have hyn := hc.lt y hyQ
      have hyx : y ≠ x := fun h => hxQ (h ▸ hyQ)
      obtain ⟨g1, g2, g3⟩ := hc.good y hyQ
      refine ⟨by rw [hD y hyn hyx]; omega, fun hyr => ?_, fun hyr => ?_⟩
      · rw [hP y hyn hyx, hD y hyn hyx]; exact g2 hyr
      · obtain ⟨h1, h2, h3, h4⟩ := g3 hyr
        have hpn := hc.lt _ h1
        have hpx : mem (outPtr + y) ≠ x := fun h => hxQ (h ▸ h1)
        rw [hP y hyn hyx, hE y hyn hyx, hD y hyn hyx, hD _ hpn hpx]
        exact ⟨List.mem_append_left _ h1, h2, h3, h4⟩
    · simp only [List.mem_singleton] at hyx; subst hyx
      obtain ⟨g1, -, -⟩ := hc.good u hu
      refine ⟨by rw [hDx]; omega, fun h => absurd h hxr, fun _ => ?_⟩
      have hux : u ≠ y := fun h => hxQ (h ▸ hu)
      rw [hPx, hEx, hDx, hD u hun hux]
      exact ⟨List.mem_append_left _ hu, hf, hj, rfl⟩
  · intro a ha
    simp only [mem']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hc.fr a ha
  · intro j hj hjr
    by_cases hjl : j < Q.length
    · have hQj : (Q ++ [x])[j] = Q[j] := List.getElem_append_left hjl
      have hyx : Q[j] ≠ x := fun h => hxQ (h ▸ List.getElem_mem hjl)
      rw [hQj] at hjr ⊢
      rw [hP _ (hc.lt _ (List.getElem_mem hjl)) hyx, List.take_append_of_le_length (by omega)]
      exact hc.po j hjl hjr
    · have hje : j = Q.length := by simp at hj; omega
      subst hje
      have hQj : (Q ++ [x])[Q.length] = x := by simp
      rw [hQj, hPx, List.take_left' rfl]
      exact hu

/-- One visit: `x` (register 20), reached from the visited `u` (register 16) along edge `f`
(register 19), ends up in the queue, which only grows at its end. -/
theorem rtVisit_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {n m tailArr headArr r outPtr sPtr : ℕ} {tl hd : ℕ → ℕ} {m₁ : ℕ → ℕ} {Q : List ℕ}
    {u x f : ℕ}
    (hout : outPtr + 3 * n ≤ sPtr) (hword : sPtr + 4 * n + 2 * m < 2 ^ w)
    (hb : RTRegs st n m tailArr headArr r outPtr sPtr)
    (h15 : st.regs 15 = Q.length) (h16 : st.regs 16 = u) (h19 : st.regs 19 = f)
    (h20 : st.regs 20 = x)
    (hc : RTCore n m r outPtr sPtr tl hd m₁ Q st.mem)
    (hu : u ∈ Q) (hx : x < n) (hf : f < m) (hj : RTJoin tl hd f x u) :
    ∃ st' c, Runs w p ω rtVisit st .normal st' c ∧ c ≤ 80 ∧
      ∃ ext, x ∈ Q ++ ext ∧ RTCore n m r outPtr sPtr tl hd m₁ (Q ++ ext) st'.mem ∧
        st'.regs 15 = (Q ++ ext).length ∧ (∀ q, q ≠ 15 → st'.regs q = st.regs q) := by
  have hun := hc.lt u hu
  have hlen := hc.length_le
  have r5 := hb.r5; have r7 := hb.r7; have r8 := hb.r8; have r10 := hb.r10; have r11 := hb.r11
  have hw1 : 1 < 2 ^ w := by omega
  suffices h : ∃ o st' c, Runs w p ω rtVisit st o st' c ∧ (o = .normal ∧
      ∃ ext, x ∈ Q ++ ext ∧ RTCore n m r outPtr sPtr tl hd m₁ (Q ++ ext) st'.mem ∧
        st'.regs 15 = (Q ++ ext).length ∧ (∀ q, q ≠ 15 → st'.regs q = st.regs q)) ∧ 0 + c ≤ 80 by
    obtain ⟨o, st', c, hr, ⟨rfl, hrest⟩, hc⟩ := h
    exact ⟨st', c, hr, by omega, hrest⟩
  have hvis := hc.vis x hx
  unfold rtVisit
  refine runs_cond_le (v := if st.mem (sPtr + n + 2 * m + x) = 0 then 1 else 0)
    (by eval_expr) ?_ ?_
  · intro hne
    have h0 : st.mem (sPtr + n + 2 * m + x) = 0 := by
      by_contra h; simp [h] at hne
    have hxQ : x ∉ Q := by
      intro hxQ; rw [hvis] at h0; simp [hxQ] at h0
    have hlt := hc.length_lt hx hxQ
    have hdu := (hc.good u hu).1
    refine runs_seq_store_le (x := sPtr + n + 2 * m + x) (v := 1) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := sPtr + n + 2 * m + n + Q.length) (v := x)
      (by eval_expr) (by eval_expr) ?_
    refine runs_seq_assign_le (v := Q.length + 1) (by eval_expr) ?_
    refine runs_seq_store_le (x := outPtr + x) (v := u) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := outPtr + n + x) (v := f) (by eval_expr) (by eval_expr) ?_
    have hDu : (Function.update (Function.update (Function.update (Function.update st.mem
        (sPtr + n + 2 * m + x) 1) (sPtr + n + 2 * m + n + Q.length) x) (outPtr + x) u)
        (outPtr + n + x) f) (outPtr + n + n + u) = st.mem (outPtr + n + n + u) := by
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    refine runs_store_le (x := outPtr + n + n + x) (v := st.mem (outPtr + n + n + u) + 1)
      (by eval_expr) (by eval_expr) ?_ ?_
    · refine ⟨rfl, [x], by simp, hc.push hout hu hx hxQ hf hj, by simp, fun q hq => ?_⟩
      simp [Function.update_of_ne hq]
    · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
      omega
  · intro h0
    have hxQ : x ∈ Q := by
      by_contra hxQ; rw [hvis] at h0; simp [hxQ] at h0
    refine runs_nop_le ⟨rfl, [], (by simpa using hxQ), (by simpa using hc), (by simpa using h15),
      fun _ _ => rfl⟩ ?_
    simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
    omega

end

end MinCostFlow.LSF.Program
