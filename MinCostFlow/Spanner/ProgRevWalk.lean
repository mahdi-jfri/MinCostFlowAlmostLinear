module

public import MinCostFlow.Spanner.ProgRevCopy
public import MinCostFlow.Spanner.ProgMapEmb

@[expose] public section

/-!
# Writing a Walk Turned Around

A step of the composed embedding may use the walk of an edge turned around (`Walk.reverse`).
This file gives the procedure that reads a stored walk and writes the reversed walk in the same
layout: the two counts are copied, and the vertex list and the edge list are copied in reverse
order with `revCopyBody`. The result is `revWalk_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-- Procedure body, at `args = [src, dst]`; `fr` holds `revCopyBody`. -/
def revWalkBody (fr : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 2))) ;;
  .store (.reg 1) (.reg 2) ;;
  .call 4 fr [.bin .add (.reg 1) (.const 1), .bin .add (.reg 0) (.const 1), .reg 2] ;;
  .store (.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 2)) (.reg 3) ;;
  .call 4 fr [.bin .add (.bin .add (.reg 1) (.const 2)) (.reg 2),
    .bin .add (.bin .add (.reg 0) (.const 2)) (.reg 2), .reg 3] ;;
  .ret (.const 0)

/-- The walk is at `src`, below the output `dst`, and the output fits in a word. -/
def RevWalkPre (mem : ℕ → ℕ) (src dst : ℕ) (P : Walk) (w : ℕ) : Prop :=
  WalkAt mem src P ∧ src + (Walk.encode P).length ≤ dst ∧
    dst + (Walk.encode P).length < 2 ^ w ∧ 1 < 2 ^ w

/-- Contract of `revWalkBody`. The cost bound uses the length of the stored walk, read from
memory. -/
def revWalkContract (w : ℕ) : Contract where
  pre args mem := ∃ src dst P, args = [src, dst] ∧ RevWalkPre mem src dst P w
  post args mem _ mem' := ∀ src dst P, args = [src, dst] → RevWalkPre mem src dst P w →
    WalkAt mem' dst P.reverse ∧
      ∀ x, x < dst ∨ dst + (Walk.encode P).length ≤ x → mem' x = mem x
  cost args mem := 30 * (mem (args.getD 0 0) + mem (args.getD 0 0 + 1 + mem (args.getD 0 0)))
    + 100

/-- `revWalkBody fr` at `f` meets `revWalkContract`, given that `fr` holds `revCopyBody`. The
cost is `30 (|verts| + |edges|) + 100`. -/
theorem revWalk_meetsContract {w : ℕ} {p : Program} {f fr : ℕ}
    (hproc : p.procs[f]? = some (revWalkBody fr))
    (hfr : MeetsContract w p fr (revCopyContract w)) :
    MeetsContract w p f (revWalkContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨src, dst, P, rfl, hP⟩ := hpre
  have hP' := hP
  obtain ⟨hW, hsd, hdw, hw1⟩ := hP'
  obtain ⟨hnv, hverts, hne, hedges⟩ := walkAt_iff.mp hW
  rw [walk_encode_length] at hsd hdw
  set nv := P.verts.length with hnvdef
  set ne := P.edges.length with hnedef
  let s0 := startState [src, dst] mem pos
  have r0 : s0.regs 0 = src := by simp [s0, startState]
  have r1 : s0.regs 1 = dst := by simp [s0, startState]
  have e2 : (Expr.load (.reg 0)).eval w s0 = some nv :=
    ev_load (ev_reg r0 (by omega)) hnv (by omega)
  let s1 : State := { s0 with regs := Function.update s0.regs 2 nv }
  have e3 : (Expr.load (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 2))).eval w s1 =
      some ne :=
    ev_load (ev_add (ev_add (ev_reg (v := src) (by simp [s1, r0]) (by omega)) (ev_const hw1)
      (by omega)) (ev_reg (v := nv) (by simp [s1]) (by omega)) (by omega)) hne (by omega)
  let s2 : State := { s1 with regs := Function.update s1.regs 3 ne }
  have esa : (Expr.reg 1).eval w s2 = some dst := ev_reg (v := dst) (by simp [s2, s1, r1]) (by omega)
  have esv : (Expr.reg 2).eval w s2 = some nv := ev_reg (v := nv) (by simp [s2, s1]) (by omega)
  let s3 : State := { s2 with mem := Function.update mem dst nv }
  have hargs1 : evalArgs w s3 [.bin .add (.reg 1) (.const 1), .bin .add (.reg 0) (.const 1),
      .reg 2] = some [dst + 1, src + 1, nv] := by
    have a1 : (Expr.bin .add (.reg 1) (.const 1)).eval w s3 = some (dst + 1) :=
      ev_add (ev_reg (v := dst) (by simp [s3, s2, s1, r1]) (by omega)) (ev_const hw1) (by omega)
    have a2 : (Expr.bin .add (.reg 0) (.const 1)).eval w s3 = some (src + 1) :=
      ev_add (ev_reg (v := src) (by simp [s3, s2, s1, r0]) (by omega)) (ev_const hw1) (by omega)
    have a3 : (Expr.reg 2).eval w s3 = some nv := ev_reg (v := nv) (by simp [s3, s2, s1]) (by omega)
    simp [evalArgs, a1, a2, a3]
  have hpre1 : RevCopyPre s3.mem (dst + 1) (src + 1) nv P.verts w :=
    ⟨ListAt.of_agree hverts fun i hi => by
      simp only [s3]; rw [Function.update_of_ne (by omega)], rfl, by omega, by omega, hw1⟩
  refine runs_start_le ?_
  refine runs_seq_assign_le e2 ?_
  refine runs_seq_assign_le e3 ?_
  refine runs_seq_store_le esa esv ?_
  refine runs_seq_call_le hfr hargs1 ?_ ⟨_, _, _, _, rfl, hpre1⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  intro v₁ mem₁ pos₁ hpost₁
  obtain ⟨hV, hother₁⟩ := hpost₁ _ _ _ _ rfl hpre1
  let s4 : State := { mem := mem₁, regs := Function.update s3.regs 4 v₁, pos := pos₁ }
  have esa2 : (Expr.bin .add (.bin .add (.reg 1) (.const 1)) (.reg 2)).eval w s4 =
      some (dst + 1 + nv) :=
    ev_add (ev_add (ev_reg (v := dst) (by simp [s4, s3, s2, s1, r1]) (by omega)) (ev_const hw1)
      (by omega)) (ev_reg (v := nv) (by simp [s4, s3, s2, s1]) (by omega)) (by omega)
  have esv2 : (Expr.reg 3).eval w s4 = some ne := ev_reg (v := ne) (by simp [s4, s3, s2]) (by omega)
  let s5 : State := { s4 with mem := Function.update mem₁ (dst + 1 + nv) ne }
  have hargs2 : evalArgs w s5 [.bin .add (.bin .add (.reg 1) (.const 2)) (.reg 2),
      .bin .add (.bin .add (.reg 0) (.const 2)) (.reg 2), .reg 3] =
      some [dst + 2 + nv, src + 2 + nv, ne] := by
    have a1 : (Expr.bin .add (.bin .add (.reg 1) (.const 2)) (.reg 2)).eval w s5 =
        some (dst + 2 + nv) :=
      ev_add (ev_add (ev_reg (v := dst) (by simp [s5, s4, s3, s2, s1, r1]) (by omega))
        (ev_const (c := 2) (by omega)) (by omega))
        (ev_reg (v := nv) (by simp [s5, s4, s3, s2, s1]) (by omega)) (by omega)
    have a2 : (Expr.bin .add (.bin .add (.reg 0) (.const 2)) (.reg 2)).eval w s5 =
        some (src + 2 + nv) :=
      ev_add (ev_add (ev_reg (v := src) (by simp [s5, s4, s3, s2, s1, r0]) (by omega))
        (ev_const (c := 2) (by omega)) (by omega))
        (ev_reg (v := nv) (by simp [s5, s4, s3, s2, s1]) (by omega)) (by omega)
    have a3 : (Expr.reg 3).eval w s5 = some ne := ev_reg (v := ne) (by simp [s5, s4, s3, s2])
      (by omega)
    simp [evalArgs, a1, a2, a3]
  -- Below `dst` nothing has changed yet.
  have hlow : ∀ x, x < dst → s5.mem x = mem x := fun x hx => by
    simp only [s5, s4]
    rw [Function.update_of_ne (by omega), hother₁ x (Or.inl (by omega))]
    simp only [s3]; rw [Function.update_of_ne (by omega)]; rfl
  have hpre2 : RevCopyPre s5.mem (dst + 2 + nv) (src + 2 + nv) ne P.edges w :=
    ⟨ListAt.of_agree hedges fun i hi => hlow _ (by omega), rfl, by omega, by omega, hw1⟩
  refine runs_seq_store_le esa2 esv2 ?_
  refine runs_seq_call_le hfr hargs2 ?_ ⟨_, _, _, _, rfl, hpre2⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  intro v₂ mem₂ pos₂ hpost₂
  obtain ⟨hE, hother₂⟩ := hpost₂ _ _ _ _ rfl hpre2
  refine runs_ret_le (v := 0) (ev_const (by omega)) (fun src' dst' P' h1 h2 => ?_) ?_
  · simp only [List.cons.injEq, and_true] at h1
    obtain ⟨rfl, rfl⟩ := h1
    have hPP : P = P' := walkAt_unique hW h2.1
    subst hPP
    rw [walk_encode_length]
    refine ⟨walkAt_iff.mpr ⟨?_, fun i hi => ?_, ?_, ?_⟩, fun x hx => ?_⟩
    · simp only [Walk.reverse, List.length_reverse]
      rw [hother₂ _ (Or.inl (by omega))]
      simp only [s5, s4]
      rw [Function.update_of_ne (by omega), hother₁ _ (Or.inl (by omega))]
      simp [s3, hnvdef]
    · simp only [Walk.reverse, List.length_reverse] at hi ⊢
      rw [hother₂ _ (Or.inl (by omega))]
      simp only [s5, s4]
      rw [Function.update_of_ne (by omega)]
      exact hV i (by simpa using hi)
    · simp only [Walk.reverse, List.length_reverse]
      rw [hother₂ _ (Or.inl (by omega))]
      show Function.update mem₁ (dst + 1 + nv) ne (dst + 1 + P.verts.length) = P.edges.length
      rw [← hnvdef, ← hnedef, Function.update_self]
    · simp only [Walk.reverse, List.length_reverse]
      exact hE
    · show mem₂ x = mem x
      rw [hother₂ x (by omega)]
      simp only [s5, s4]
      rw [Function.update_of_ne (by omega), hother₁ x (by omega)]
      simp only [s3]; rw [Function.update_of_ne (by omega)]; rfl
  · simp only [Expr.size, argsSize, revCopyContract, revWalkContract, List.getD_cons_succ,
      List.getD_cons_zero]
    rw [hnv, hne]
    omega

end MinCostFlow.Spanner
