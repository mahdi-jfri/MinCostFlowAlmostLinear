module

public import MinCostFlow.LSF.Program.RootTreeBfs
import Mathlib.Tactic.Linarith

/-!
# Rooting a tree: the contract of `rootTreeProc`

`rootTree_meetsContract` proves that `rootTreeProc` (`RootTreeBase.lean`) roots a graph on the
vertices `0, …, n - 1` with edges `f < m` at a vertex `r` from which every vertex is reachable.
For every vertex `x ≠ r` it stores a parent, an edge `f < m` joining `x` to that parent, and a
depth one more than the parent's; `r` is its own parent at depth `0`. The run costs at most
`300 n + 400 m + 200`. The initialization of Lemma 5.4 uses it to root `T₀` at `r₀`
(the arrays `t0Parent`, `t0ParentTreeIdx` and `t0Depth` of `AuxAt`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-- The rooted arrays at `outPtr` (parents), `outPtr + n` (parent edges) and `outPtr + 2 n`
(depths). -/
def RTRooted (n m r outPtr : ℕ) (tl hd : ℕ → ℕ) (mem : ℕ → ℕ) : Prop :=
  mem (outPtr + r) = r ∧ mem (outPtr + n + n + r) = 0 ∧
  ∀ x < n, mem (outPtr + x) < n ∧ mem (outPtr + n + n + x) < n ∧
    (x ≠ r → mem (outPtr + n + x) < m ∧
      RTJoin tl hd (mem (outPtr + n + x)) x (mem (outPtr + x)) ∧
      mem (outPtr + n + n + x) = mem (outPtr + n + n + mem (outPtr + x)) + 1)

/-- The search order, left in the queue area `sPtr + n + 2 m + n`: every vertex once, each
after its parent. -/
def RTOrder (n m r outPtr sPtr : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∃ Q : List ℕ, Q.length = n ∧ Q.Nodup ∧ (∀ x < n, x ∈ Q) ∧ (∀ x ∈ Q, x < n) ∧
    ListAt mem (sPtr + n + 2 * m + n) Q ∧
    ∀ j (hj : j < Q.length), Q[j] ≠ r → mem (outPtr + Q[j]) ∈ Q.take j

/-- The contract of `rootTreeProc`. Args: `[n, m, tailArr, headArr, r, outPtr, sPtr]`. -/
def rootTreeContract (w : ℕ) : Contract where
  pre args mem := ∃ (n m tailArr headArr r outPtr sPtr : ℕ) (tl hd : ℕ → ℕ),
    args = [n, m, tailArr, headArr, r, outPtr, sPtr] ∧
    RTInput w n m tailArr headArr r outPtr sPtr tl hd mem ∧
    (∀ i < n, mem (sPtr + i) = 0) ∧ (∀ i < n, mem (sPtr + n + 2 * m + i) = 0) ∧
    ∀ x < n, Relation.ReflTransGen (rtAdj m tl hd) r x
  post args mem ret mem' := ∃ (n m tailArr headArr r outPtr sPtr : ℕ) (tl hd : ℕ → ℕ),
    args = [n, m, tailArr, headArr, r, outPtr, sPtr] ∧
    (∀ f < m, mem (tailArr + f) = tl f ∧ mem (headArr + f) = hd f) ∧
    ret = 0 ∧ RTRooted n m r outPtr tl hd mem' ∧ RTOrder n m r outPtr sPtr mem' ∧
    ∀ a, a < outPtr ∨ (outPtr + 3 * n ≤ a ∧ a < sPtr) ∨ sPtr + 4 * n + 2 * m ≤ a →
      mem' a = mem a
  cost args _ := 300 * args.getD 0 0 + 400 * args.getD 1 0 + 200

private lemma rtOrder_of_done {n m tailArr headArr r outPtr sPtr : ℕ} {tl hd : ℕ → ℕ}
    {m₁ : ℕ → ℕ} {st : State}
    (hd' : RTBfsDone n m tailArr headArr r outPtr sPtr tl hd m₁ st) :
    RTOrder n m r outPtr sPtr st.mem := by
  obtain ⟨-, Q, hc, hall⟩ := hd'
  have hle := hc.length_le
  have hge : n ≤ Q.length := by
    have h := Finset.card_le_card (s := Finset.range n) (t := Q.toFinset) (fun x hx =>
      List.mem_toFinset.mpr (hall x (Finset.mem_range.mp hx)))
    rw [Finset.card_range] at h
    exact h.trans (List.toFinset_card_le Q)
  exact ⟨Q, by omega, hc.nd, hall, hc.lt, fun j hj => hc.q j hj, hc.po⟩

private lemma rtRooted_of_done {n m tailArr headArr r outPtr sPtr : ℕ} {tl hd : ℕ → ℕ}
    {m₁ : ℕ → ℕ} {st : State}
    (hd' : RTBfsDone n m tailArr headArr r outPtr sPtr tl hd m₁ st) :
    RTRooted n m r outPtr tl hd st.mem := by
  obtain ⟨-, Q, hc, hall⟩ := hd'
  have hlen := hc.length_le
  obtain ⟨g1, g2, -⟩ := hc.good r hc.r_mem
  refine ⟨(g2 rfl).1, (g2 rfl).2, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hc.good x (hall x hx)
  refine ⟨?_, by omega, fun hxr => ?_⟩
  · by_cases hxr : x = r
    · subst hxr; rw [(h2 rfl).1]; exact hx
    · exact hc.lt _ (h3 hxr).1
  · obtain ⟨-, h4, h5, h6⟩ := h3 hxr
    exact ⟨h4, h5, h6⟩

theorem rootTree_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some rootTreeProc) :
    MeetsContract w p b (rootTreeContract w) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨n, m, tailArr, headArr, r, outPtr, sPtr, tl, hd, rfl, hI, hz1, hz2, hreach⟩ := hpre
  have hw := hI.hw; have hword := hI.hword; have hout := hI.hout; have hr := hI.hr
  have htA := hI.htA; have hhA := hI.hhA
  have hw1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold rootTreeProc
  refine runs_seq_assign_le (v := outPtr + n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := outPtr + n + n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := sPtr + n) (by eval_expr) ?_
  refine runs_seq_assign_le (v := sPtr + n + 2 * m) (by eval_expr) ?_
  refine runs_seq_assign_le (v := sPtr + n + 2 * m + n) (by eval_expr) ?_
  refine runs_seq_triple_le (rtBuild_triple (p := p) hI hz1) ⟨⟨by simp [startState],
    by simp [startState], by simp [startState], by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp, by simp, by simp, by simp, by simp⟩,
    rfl⟩ ?_
  rintro st₁ ⟨hb, -, hch, hfr⟩
  have r4 := hb.r4; have r5 := hb.r5; have r7 := hb.r7; have r8 := hb.r8; have r10 := hb.r10
  have r11 := hb.r11
  refine runs_seq_store_le (x := sPtr + n + 2 * m + r) (v := 1) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := sPtr + n + 2 * m + n) (v := r) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := outPtr + r) (v := r) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := outPtr + n + r) (v := 0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := outPtr + n + n + r) (v := 0) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
  set m₂ := Function.update (Function.update (Function.update (Function.update
    (Function.update st₁.mem (sPtr + n + 2 * m + r) 1) (sPtr + n + 2 * m + n) r) (outPtr + r) r)
    (outPtr + n + r) 0) (outPtr + n + n + r) 0 with hm₂
  have hI' : RTScanInput n m tailArr headArr outPtr sPtr tl hd st₁.mem :=
    ⟨fun f hf => by rw [hfr _ (Or.inl (by omega))]; exact hI.htl f hf,
      fun f hf => by rw [hfr _ (Or.inl (by omega))]; exact hI.hhd f hf, htA, hhA, hout⟩
  have hcore : RTCore n m r outPtr sPtr tl hd st₁.mem [r] m₂ := by
    refine ⟨?_, List.nodup_singleton _, by simpa using hr, rfl, ?_, ?_, ?_, ?_⟩
    · intro j hj
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      simp (disch := omega) only [hm₂, List.getElem_singleton, Nat.add_zero,
        Function.update_of_ne, Function.update_self]
    · intro x hx
      by_cases hxr : x = r
      · subst hxr
        simp (disch := omega) only [hm₂, Function.update_of_ne, Function.update_self]
        simp
      · simp (disch := omega) only [hm₂, Function.update_of_ne]
        rw [hfr _ (Or.inr (by omega)), hz2 x hx]
        simp [hxr]
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      refine ⟨?_, fun _ => ⟨?_, ?_⟩, fun h => absurd rfl h⟩
      · simp [hm₂]
      · simp (disch := omega) only [hm₂, Function.update_of_ne, Function.update_self]
      · simp [hm₂]
    · intro a ha
      simp (disch := omega) only [hm₂, Function.update_of_ne]
    · intro j hj hjr
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      exact absurd rfl hjr
  refine runs_seq_triple_le (rtBfs_triple (p := p) hI' hw hword hch hreach (0, [r]))
    ⟨((((hb.mem m₂).upd 14 0 (by omega)).upd 15 1 (by omega))), by simp, by simp, by simp,
      hcore, fun j hj => absurd hj (by simp)⟩ ?_
  intro st₂ hdone
  refine runs_ret_le (by eval_expr) ⟨n, m, tailArr, headArr, r, outPtr, sPtr, tl, hd, rfl,
    fun f hf => ⟨(hI.htl f hf).1, (hI.hhd f hf).1⟩, rfl, rtRooted_of_done hdone, rtOrder_of_done hdone, ?_⟩ ?_
  · intro a ha
    obtain ⟨-, Q, hc, -⟩ := hdone
    rw [hc.fr a (by omega), hfr a (by omega)]
  · simp only [rtBfsRem, rootTreeContract, Expr.size_const, Expr.size_reg, Expr.size_bin,
      List.getD_cons_zero, List.getD_cons_succ, List.take_zero, List.map_nil, List.sum_nil]
    omega

end

end MinCostFlow.LSF.Program
