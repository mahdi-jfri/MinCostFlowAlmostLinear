module

public import MinCostFlow.LSF.Program.RootTreeVisit
import Mathlib.Tactic.Linarith

/-!
# Rooting a tree: scanning the half-edges of one vertex

The inner loop of the search follows the linked list of half-edges at the current vertex `u`
and visits the other end of each (`rtVisit_runs`). We prove `rtScan_triple` with
`Triple.loop_list` over the list of half-edges still to scan: at the end every neighbour of `u`
is in the queue, the queue only grew at its end, and the cost is `O(deg u)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-- The state while scanning `u`: `L` is the part of the list of `u` not scanned yet, and the
other ends of the scanned half-edges are in the queue `Q₀ ++ ext`. -/
def RTScanInv (n m tailArr headArr r outPtr sPtr : ℕ) (tl hd : ℕ → ℕ) (m₁ : ℕ → ℕ)
    (u qh : ℕ) (Q₀ : List ℕ) (L : List ℕ) (st : State) : Prop :=
  RTRegs st n m tailArr headArr r outPtr sPtr ∧ st.regs 14 = qh ∧ st.regs 16 = u ∧
  ChainFrom m₁ (sPtr + n) (st.regs 17) L ∧
  ∃ ext pre, st.regs 15 = (Q₀ ++ ext).length ∧
    RTCore n m r outPtr sPtr tl hd m₁ (Q₀ ++ ext) st.mem ∧
    pre ++ L = rtHalf tl hd (2 * m) u ∧ ∀ h ∈ pre, rtOther tl hd h ∈ Q₀ ++ ext

/-- The facts about `m₁`, the memory after the half-edge lists are built, that the search
reads. -/
structure RTScanInput (n m tailArr headArr outPtr sPtr : ℕ) (tl hd : ℕ → ℕ)
    (m₁ : ℕ → ℕ) : Prop where
  htl : ∀ f < m, m₁ (tailArr + f) = tl f ∧ tl f < n
  hhd : ∀ f < m, m₁ (headArr + f) = hd f ∧ hd f < n
  htA : tailArr + m ≤ outPtr
  hhA : headArr + m ≤ outPtr
  hout : outPtr + 3 * n ≤ sPtr

private lemma rtJoin_of_half {tl hd : ℕ → ℕ} {m u h : ℕ}
    (hh : h ∈ rtHalf tl hd (2 * m) u) :
    RTJoin tl hd (h / 2) (rtOther tl hd h) u := by
  have hend := (mem_rtHalf.mp hh).2
  unfold RTJoin
  by_cases hp : h % 2 = 0
  · simp only [rtEnd, hp, ↓reduceIte] at hend
    simp only [rtOther, hp, ↓reduceIte]
    exact Or.inr ⟨hend, trivial⟩
  · simp only [rtEnd, hp, ↓reduceIte] at hend
    simp only [rtOther, hp, ↓reduceIte]
    exact Or.inl ⟨trivial, hend⟩

theorem rtScan_triple {w : ℕ} {p : Program} {n m tailArr headArr r outPtr sPtr : ℕ}
    {tl hd : ℕ → ℕ} {m₁ : ℕ → ℕ} {u qh : ℕ} {Q₀ : List ℕ}
    (hI : RTScanInput n m tailArr headArr outPtr sPtr tl hd m₁)
    (hword : sPtr + 4 * n + 2 * m < 2 ^ w) (hu : u ∈ Q₀) :
    Triple w p (RTScanInv n m tailArr headArr r outPtr sPtr tl hd m₁ u qh Q₀
        (rtHalf tl hd (2 * m) u))
      (.loop (.reg 17) rtScanBody)
      (normalPost (RTScanInv n m tailArr headArr r outPtr sPtr tl hd m₁ u qh Q₀ []))
      (fun _ => 120 * rtDeg m tl hd u + 2) := by
  refine (Triple.loop_list (Inv := RTScanInv n m tailArr headArr r outPtr sPtr tl hd m₁ u qh Q₀)
    (fun _ => 110) ?_ ?_ (rtHalf tl hd (2 * m) u)).mono_cost ?_
  · intro st hinv
    have h17 : st.regs 17 = 0 := hinv.2.2.2.1
    exact ⟨by eval_expr, hinv⟩
  · intro h L st hinv
    obtain ⟨hb, h14, h16, hch, ext, pre, h15, hc, hpre, hpreQ⟩ := hinv
    obtain ⟨h17, hch'⟩ := hch
    have hhmem : h ∈ rtHalf tl hd (2 * m) u := by rw [← hpre]; simp
    have hh2m := (mem_rtHalf.mp hhmem).1
    have hf : h / 2 < m := by omega
    have hxn : rtOther tl hd h < n := by
      unfold rtOther; split_ifs
      · exact (hI.hhd _ hf).2
      · exact (hI.htl _ hf).2
    refine ⟨h + 1, by eval_expr, by omega, ?_⟩
    intro s ω hs
    subst s
    have r2 := hb.r2; have r3 := hb.r3; have r9 := hb.r9
    have hout := hI.hout
    have hlen := hc.length_le
    have hw1 : 1 < 2 ^ w := by omega
    have hnext : st.mem (sPtr + n + h) = m₁ (sPtr + n + h) :=
      hc.fr _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
    have hT : st.mem (tailArr + h / 2) = tl (h / 2) := by
      rw [hc.fr _ (Or.inl (by have := hI.htA; omega))]; exact (hI.htl _ hf).1
    have hH : st.mem (headArr + h / 2) = hd (h / 2) := by
      rw [hc.fr _ (Or.inl (by have := hI.hhA; omega))]; exact (hI.hhd _ hf).1
    -- the state before the visit
    let rg3 := Function.update (Function.update (Function.update st.regs 18 h) 19 (h / 2)) 17
      (st.mem (sPtr + n + h))
    let st3 : State := { st with regs := rg3 }
    have hb3 : RTRegs st3 n m tailArr headArr r outPtr sPtr :=
      ((hb.upd 18 h (by omega)).upd 19 (h / 2) (by omega)).upd 17 _ (by omega)
    have hA1 : headArr + h / 2 < 2 ^ w := by have := hI.hhA; omega
    have hA2 : tailArr + h / 2 < 2 ^ w := by have := hI.htA; omega
    let st4 : State := ⟨st.mem, Function.update rg3 20 (rtOther tl hd h), st.pos⟩
    have hvisit : ∃ o st' c, Runs w p ω rtVisit st4 o st' c ∧
          (match o with
            | .returned v => normalPost (RTScanInv n m tailArr headArr r outPtr sPtr tl hd m₁
                u qh Q₀ []) (.returned v) st'
            | .normal => RTScanInv n m tailArr headArr r outPtr sPtr tl hd m₁ u qh Q₀ L st') ∧
          c ≤ 80 := by
      have hb4 : RTRegs st4 n m tailArr headArr r outPtr sPtr :=
        (hb3.upd 20 (rtOther tl hd h) (by omega)).mem st.mem
      have g15 : st4.regs 15 = (Q₀ ++ ext).length := by simp [st4, rg3, h15]
      have g16 : st4.regs 16 = u := by simp [st4, rg3, h16]
      have g19 : st4.regs 19 = h / 2 := by simp [st4, rg3]
      have g20 : st4.regs 20 = rtOther tl hd h := by simp [st4]
      have hc4 : RTCore n m r outPtr sPtr tl hd m₁ (Q₀ ++ ext) st4.mem := hc
      obtain ⟨st', c, hrun, hcost, ext', hx', hc', h15', hregs'⟩ :=
        rtVisit_runs (ω := ω) (p := p) hout hword hb4 g15 g16 g19 g20 hc4
          (List.mem_append_left _ hu) hxn hf (rtJoin_of_half hhmem)
      refine ⟨.normal, st', c, hrun, ?_, hcost⟩
      have hb' : RTRegs st' n m tailArr headArr r outPtr sPtr :=
        ⟨(hregs' 0 (by omega)).trans hb4.r0, (hregs' 1 (by omega)).trans hb4.r1,
          (hregs' 2 (by omega)).trans hb4.r2, (hregs' 3 (by omega)).trans hb4.r3,
          (hregs' 4 (by omega)).trans hb4.r4, (hregs' 5 (by omega)).trans hb4.r5,
          (hregs' 6 (by omega)).trans hb4.r6, (hregs' 7 (by omega)).trans hb4.r7,
          (hregs' 8 (by omega)).trans hb4.r8, (hregs' 9 (by omega)).trans hb4.r9,
          (hregs' 10 (by omega)).trans hb4.r10, (hregs' 11 (by omega)).trans hb4.r11⟩
      refine ⟨hb', ?_, ?_, ?_, ext ++ ext', pre ++ [h], by simpa using h15', by simpa using hc',
        by simpa using hpre, ?_⟩
      · rw [hregs' 14 (by omega)]; simp [st4, rg3, h14]
      · rw [hregs' 16 (by omega), g16]
      · rw [hregs' 17 (by omega)]
        simp only [st4, rg3, Function.update_of_ne (show (17 : ℕ) ≠ 20 by omega),
          Function.update_self]
        rw [hnext]; exact hch'
      · intro h' hh'
        rcases List.mem_append.mp hh' with hh' | hh'
        · have := hpreQ h' hh'
          simp only [← List.append_assoc]
          exact List.mem_append_left _ this
        · simp only [List.mem_singleton] at hh'; subst hh'
          simpa using hx'
    refine runs_start_le ?_
    unfold rtScanBody
    refine runs_seq_assign_le (v := h) (by show _ = some (h + 1 - 1); eval_expr) ?_
    refine runs_seq_assign_le (v := h / 2) (by eval_expr) ?_
    refine runs_seq_assign_le (v := st.mem (sPtr + n + h)) (by eval_expr) ?_
    refine runs_seq_cond_le (v := if h % 2 = 0 then 1 else 0) (by eval_expr) ?_ ?_
    · intro hne
      have hp : h % 2 = 0 := by by_contra hp; simp [hp] at hne
      have hx : rtOther tl hd h = hd (h / 2) := by simp [rtOther, hp]
      refine runs_seq_assign_le (v := rtOther tl hd h) (by rw [hx]; eval_expr) ?_
      obtain ⟨o, st', c, hrun, hq, hc⟩ := hvisit
      refine ⟨o, st', c, hrun, ?_, ?_⟩
      · cases o with
        | normal => exact hq
        | returned v => exact hq
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
    · intro hz
      have hp : h % 2 ≠ 0 := by intro hp; simp [hp] at hz
      have hx : rtOther tl hd h = tl (h / 2) := by simp [rtOther, hp]
      refine runs_seq_assign_le (v := rtOther tl hd h) (by rw [hx]; eval_expr) ?_
      obtain ⟨o, st', c, hrun, hq, hc⟩ := hvisit
      refine ⟨o, st', c, hrun, ?_, ?_⟩
      · cases o with
        | normal => exact hq
        | returned v => exact hq
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]; omega
  · intro _ _
    have hs : ∀ L : List ℕ, (L.map (fun _ => 110)).sum = 110 * L.length := by
      intro L; induction L with
      | nil => simp
      | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring
    rw [hs]
    simp only [Expr.size_reg, rtDeg]
    omega

end

end MinCostFlow.LSF.Program
