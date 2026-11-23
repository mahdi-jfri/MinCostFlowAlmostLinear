module

public import MinCostFlow.Spanner.ProgComposeWalk

@[expose] public section

/-!
# Writing a Composed Walk: the Procedure

This file puts together the loop of `ProgComposeWalk`. After the loop, the vertex buffer holds
the vertices of `composeAux B embBC vs js` and the edge buffer holds its edges
(`composeAux_eq_foldApp`, `foldApp_verts`, `foldApp_edges`). The procedure then writes the walk
at `dst`. The result is `composeWalk_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited LSF.Program

/-- `composeAux` reads `embBC` only at the edges in `js`. -/
lemma composeAux_congr (B : Graph) {e₁ e₂ : ℕ → Walk} :
    ∀ (vs js : List ℕ), (∀ j ∈ js, e₁ j = e₂ j) → composeAux B e₁ vs js = composeAux B e₂ vs js
  | u :: v :: vs, j :: js, h => by
    rw [composeAux, composeAux, h j (by simp),
      composeAux_congr B (v :: vs) js fun j' hj' => h j' (by simp [hj'])]
  | [], _, _ => by simp [composeAux]
  | [_], _, _ => by simp [composeAux]
  | _ :: _ :: _, [], _ => by simp [composeAux]

/-- Procedure body, at `args = [bAddr, E, A, dst, S, VB, EB, L]`. Here `fs` holds
`composeStepBody` and `fc` holds `memCopyStmt`. The last argument is used only by the
contract. -/
def composeWalkBody (fs fc : ℕ) : Stmt :=
  .assign 8 (.load (.reg 2)) ;;
  .assign 9 (.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 8))) ;;
  .assign 11 (.const 0) ;;
  .assign 12 (.const 0) ;;
  forRange 10 (.const 0) (.reg 9) (composeWalkLoop fs fc) ;;
  .store (.reg 3) (.reg 11) ;;
  .call 18 fc [.bin .add (.reg 3) (.const 1), .reg 5, .reg 11] ;;
  .store (.bin .add (.bin .add (.reg 3) (.const 1)) (.reg 11)) (.reg 12) ;;
  .call 18 fc [.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 11), .reg 6, .reg 12] ;;
  .ret (.const 0)

/-- Contract of `composeWalkBody`. The cost bound uses the edge count of the stored walk. -/
def composeWalkContract (w : ℕ) : Contract where
  pre args mem := ∃ bAddr E A dst S VB EB L B embBC Q, args = [bAddr, E, A, dst, S, VB, EB, L] ∧
    ComposeWalkPre mem bAddr E A dst S VB EB L B embBC Q w
  post args mem _ mem' := ∀ bAddr E A dst S VB EB L B embBC Q,
    args = [bAddr, E, A, dst, S, VB, EB, L] →
    ComposeWalkPre mem bAddr E A dst S VB EB L B embBC Q w →
    WalkAt mem' dst (composeAux B embBC Q.verts Q.edges) ∧
      (Walk.encode (composeAux B embBC Q.verts Q.edges)).length ≤
        2 + 2 * (Q.edges.length * L) ∧
      ∀ x, x < S ∨ (EB + Q.edges.length * L ≤ x ∧ x < dst) ∨
        dst + (Walk.encode (composeAux B embBC Q.verts Q.edges)).length ≤ x → mem' x = mem x
  cost args mem :=
    mem (args.getD 2 0 + 1 + mem (args.getD 2 0)) * (120 * args.getD 7 0 + 620) + 150

/-- `composeWalkBody fs fc` at `f` meets `composeWalkContract`, given that `fs` holds
`composeStepBody` and `fc` holds `memCopyStmt`. The cost is `|edges| (120 L + 620) + 150` for
the stored walk. -/
theorem composeWalk_meetsContract {w : ℕ} {p : Program} {f fs fc : ℕ}
    (hproc : p.procs[f]? = some (composeWalkBody fs fc))
    (hfs : MeetsContract w p fs (composeStepContract w))
    (hfc : MeetsContract w p fc (memCopyContract w)) :
    MeetsContract w p f (composeWalkContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨bAddr, E, A, dst, S, VB, EB, L, B, embBC, Q, rfl, hP⟩ := hpre
  have hP' := hP
  obtain ⟨hG, hEmb, hBnd, hGS, hQ, hQS, hQshape, hQe, hQv, hL, hEV, hSV, hVE, hED, hdw,
    hw1⟩ := hP'
  obtain ⟨hnvA, -, hneA, -⟩ := walkAt_iff.mp hQ
  have hQlen := walk_encode_length Q
  set nvA := Q.verts.length with hnvAdef
  set neA := Q.edges.length with hneAdef
  set fstep := stepsOf B embBC Q.verts Q.edges with hfdef
  have hdstw : dst < 2 ^ w := by omega
  have hS : S < 2 ^ w := by omega
  let s0 := startState [bAddr, E, A, dst, S, VB, EB, L] mem pos
  have e8 : (Expr.load (.reg 2)).eval w s0 = some nvA :=
    ev_load' (ev_reg (v := A) (by simp [s0, startState]) (by omega)) hnvA
  let s1 : State := { s0 with regs := Function.update s0.regs 8 nvA }
  have e9 : (Expr.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 8))).eval w s1 =
      some neA :=
    ev_load' (ev_add (ev_add (ev_reg (v := A) (by simp [s1, s0, startState]) (by omega))
      (ev_const hw1) (by omega)) (ev_reg (v := nvA) (by simp [s1]) (by omega)) (by omega)) hneA
  have hk0 : keptSteps fstep 0 = [] := by simp [keptSteps]
  have he0 : stepEdges fstep 0 = [] := by simp [stepEdges]
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 10) (lo := .const 0)
    (hi := .reg 9)
    (P := fun st => st.regs 0 = bAddr ∧ st.regs 1 = E ∧ st.regs 2 = A ∧ st.regs 3 = dst ∧
      st.regs 4 = S ∧ st.regs 5 = VB ∧ st.regs 6 = EB ∧ st.regs 8 = nvA ∧ st.regs 9 = neA ∧
      st.regs 11 = 0 ∧ st.regs 12 = 0 ∧ st.mem = mem)
    (Inv := CWInv mem bAddr E A dst S VB EB L B embBC Q) (80 * L + 600) 0 neA (Nat.zero_le _) hw1
    (fun _ => by omega)
    (fun st ⟨q0, q1, q2, q3, q4, q5, q6, q8, q9, q11, q12, hm⟩ => ⟨ev_const (by omega),
      ⟨by simp [q0], by simp [q1], by simp [q2], by simp [q3], by simp [q4], by simp [q5],
        by simp [q6], by simp [q8, hnvAdef], by simp [q9, hneAdef], by simp,
        by simp [q11, ← hfdef, hk0, joinVerts], by simp [q12, ← hfdef, he0], Nat.zero_le _,
        by simp [← hfdef, hk0, joinVerts], by simp [← hfdef, he0],
        by simp [← hfdef, hk0, joinVerts, listAt_nil], by simp [← hfdef, he0, listAt_nil],
        fun x _ => by simp [hm]⟩⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => ev_reg h.2.2.2.2.2.2.2.2.1 (by omega))
    (fun i _ hi => composeWalk_step hfs hfc hP i hi)
  refine runs_start_le ?_
  refine runs_seq_assign_le e8 ?_
  refine runs_seq_assign_le e9 ?_
  refine runs_seq_assign_le (ev_const (c := 0) (by omega)) ?_
  refine runs_seq_assign_le (ev_const (c := 0) (by omega)) ?_
  refine runs_seq_triple_le hloop ⟨by simp [s1, s0, startState], by simp [s1, s0, startState],
    by simp [s1, s0, startState], by simp [s1, s0, startState], by simp [s1, s0, startState],
    by simp [s1, s0, startState], by simp [s1, s0, startState], by simp [s1], by simp,
    by simp, by simp, rfl⟩ ?_
  intro st₁ hI
  obtain ⟨-, -, -, r3, -, r5, r6, -, -, -, r11, r12, -, hcV, hcE, hVB, hEB, hout⟩ := hI
  set VL := joinVerts (keptSteps fstep neA) with hVLdef
  set EL := stepEdges fstep neA with hELdef
  have hesa : (Expr.reg 3).eval w st₁ = some dst := ev_reg r3 hdstw
  have hesv : (Expr.reg 11).eval w st₁ = some VL.length := ev_reg r11 (by omega)
  let t1 : State := { st₁ with mem := Function.update st₁.mem dst VL.length }
  have hargs1 : evalArgs w t1 [.bin .add (.reg 3) (.const 1), .reg 5, .reg 11] =
      some [dst + 1, VB, VL.length] := by
    have a1 : (Expr.bin .add (.reg 3) (.const 1)).eval w t1 = some (dst + 1) :=
      ev_add (ev_reg (v := dst) (by simp [t1, r3]) hdstw) (ev_const hw1) (by omega)
    have a2 : (Expr.reg 5).eval w t1 = some VB := ev_reg (v := VB) (by simp [t1, r5]) (by omega)
    have a3 : (Expr.reg 11).eval w t1 = some VL.length :=
      ev_reg (v := VL.length) (by simp [t1, r11]) (by omega)
    simp [evalArgs, a1, a2, a3]
  refine runs_seq_store_le hesa hesv ?_
  refine runs_seq_call_le hfc hargs1 ?_ ⟨dst + 1, VB, VL.length, rfl, by omega, by omega,
    Or.inr (by omega)⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  intro v₁ mem₁ pos₁ hpost₁
  obtain ⟨d', s', l', hargs', -, hcopy0, hother0⟩ := hpost₁
  simp only [List.cons.injEq, and_true] at hargs'
  obtain ⟨hd', hs', hl'⟩ := hargs'
  subst hd' hs' hl'
  have hcopy₁ : ∀ t < VL.length, mem₁ (dst + 1 + t) = t1.mem (VB + t) := hcopy0
  have hfr₁ : ∀ x, x < dst + 1 ∨ dst + 1 + VL.length ≤ x → mem₁ x = t1.mem x := hother0
  let t2 : State := { mem := mem₁, regs := Function.update t1.regs 18 v₁, pos := pos₁ }
  have hesa2 : (Expr.bin .add (.bin .add (.reg 3) (.const 1)) (.reg 11)).eval w t2 =
      some (dst + 1 + VL.length) :=
    ev_add (ev_add (ev_reg (v := dst) (by simp [t2, t1, r3]) hdstw) (ev_const hw1) (by omega))
      (ev_reg (v := VL.length) (by simp [t2, t1, r11]) (by omega)) (by omega)
  have hesv2 : (Expr.reg 12).eval w t2 = some EL.length :=
    ev_reg (v := EL.length) (by simp [t2, t1, r12]) (by omega)
  let t3 : State := { t2 with mem := Function.update mem₁ (dst + 1 + VL.length) EL.length }
  have hargs2 : evalArgs w t3 [.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 11), .reg 6,
      .reg 12] = some [dst + 2 + VL.length, EB, EL.length] := by
    have a1 : (Expr.bin .add (.bin .add (.reg 3) (.const 2)) (.reg 11)).eval w t3 =
        some (dst + 2 + VL.length) :=
      ev_add (ev_add (ev_reg (v := dst) (by simp [t3, t2, t1, r3]) hdstw)
        (ev_const (c := 2) (by omega)) (by omega))
        (ev_reg (v := VL.length) (by simp [t3, t2, t1, r11]) (by omega)) (by omega)
    have a2 : (Expr.reg 6).eval w t3 = some EB :=
      ev_reg (v := EB) (by simp [t3, t2, t1, r6]) (by omega)
    have a3 : (Expr.reg 12).eval w t3 = some EL.length :=
      ev_reg (v := EL.length) (by simp [t3, t2, t1, r12]) (by omega)
    simp [evalArgs, a1, a2, a3]
  refine runs_seq_store_le hesa2 hesv2 ?_
  refine runs_seq_call_le hfc hargs2 ?_ ⟨dst + 2 + VL.length, EB, EL.length, rfl, by omega,
    by omega, Or.inr (by omega)⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  intro v₂ mem₂ pos₂ hpost₂
  obtain ⟨d', s', l', hargs', -, hcopy0', hother0'⟩ := hpost₂
  simp only [List.cons.injEq, and_true] at hargs'
  obtain ⟨hd', hs', hl'⟩ := hargs'
  subst hd' hs' hl'
  have hcopy₂ : ∀ t < EL.length, mem₂ (dst + 2 + VL.length + t) = t3.mem (EB + t) := hcopy0'
  have hfr₂ : ∀ x, x < dst + 2 + VL.length ∨ dst + 2 + VL.length + EL.length ≤ x →
      mem₂ x = t3.mem x := hother0'
  -- The model walk.
  have hK : min (Q.verts.length - 1) Q.edges.length = neA := by
    rcases hQshape with h | ⟨h1, h2⟩
    · omega
    · simp [neA, h1, h2]
  have hcomp : composeAux B embBC Q.verts Q.edges = foldApp ((List.range neA).map fstep) := by
    rw [composeAux_eq_foldApp, hK]
    rfl
  have hstepsV : ∀ T ∈ (List.range neA).map fstep, T.edges ≠ [] → T.verts ≠ [] := by
    intro T hT hTe
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hT
    rw [List.mem_range] at hi
    have hj : Q.edges.getD i 0 < B.m := by
      rw [List.getD_eq_getElem _ _ hi]; exact hQe _ (List.getElem_mem hi)
    exact composeStep_verts _ _ _ _ _ (hEV _ hj (composeStep_edges _ _ _ _ _ hTe))
  have hWv : (composeAux B embBC Q.verts Q.edges).verts = VL := by
    rw [hcomp, foldApp_verts _ hstepsV]; rfl
  have hWe : (composeAux B embBC Q.verts Q.edges).edges = EL := by
    rw [hcomp, foldApp_edges]; rfl
  refine runs_ret_le (v := 0) (ev_const (by omega))
    (fun bA' E' A' d' S' VB' EB' L' B' emb' Q' h1 h2 => ?_) ?_
  · simp only [List.cons.injEq, and_true] at h1
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
    have hB : B = B' := graphAt_unique hG h2.1
    subst hB
    have hQQ : Q = Q' := walkAt_unique hQ h2.2.2.2.2.1
    subst hQQ
    have hcongr : composeAux B emb' Q.verts Q.edges = composeAux B embBC Q.verts Q.edges :=
      composeAux_congr B _ _ fun j hj => (walkAt_unique (hEmb j (hQe j hj))
        (h2.2.1 j (hQe j hj))).symm
    rw [hcongr]
    refine ⟨walkAt_iff.mpr ⟨?_, fun t ht => ?_, ?_, ?_⟩, ?_, fun x hx => ?_⟩
    · rw [hWv]
      show mem₂ dst = _
      rw [hfr₂ _ (Or.inl (by omega))]
      show Function.update mem₁ _ _ dst = _
      rw [Function.update_of_ne (by omega), hfr₁ _ (Or.inl (by omega))]
      show Function.update st₁.mem dst VL.length dst = _
      rw [Function.update_self]
    · have ht' : t < VL.length := by rw [← hWv]; exact ht
      rw [List.getElem_of_eq hWv]
      show mem₂ _ = _
      rw [hfr₂ _ (Or.inl (by omega))]
      show Function.update mem₁ _ _ _ = _
      rw [Function.update_of_ne (by omega), hcopy₁ t ht']
      show Function.update st₁.mem dst VL.length _ = _
      rw [Function.update_of_ne (by omega)]
      exact hVB t ht'
    · rw [hWv, hWe]
      show mem₂ _ = _
      rw [hfr₂ _ (Or.inl (by omega))]
      show Function.update mem₁ _ _ _ = _
      rw [Function.update_self]
    · rw [hWv, hWe]
      intro t ht
      show mem₂ _ = _
      rw [hcopy₂ t ht]
      show Function.update mem₁ _ _ _ = _
      rw [Function.update_of_ne (by omega), hfr₁ _ (Or.inl (by omega))]
      show Function.update st₁.mem dst VL.length _ = _
      rw [Function.update_of_ne (by omega)]
      exact hEB t ht
    · rw [walk_encode_length, hWv, hWe, ← hneAdef]; omega
    · rw [walk_encode_length, hWv, hWe] at hx
      simp only [← hneAdef] at hx
      show mem₂ x = mem x
      rw [hfr₂ x (by omega)]
      show Function.update mem₁ _ _ x = _
      rw [Function.update_of_ne (by omega), hfr₁ x (by omega)]
      show Function.update st₁.mem dst VL.length x = _
      rw [Function.update_of_ne (by omega)]
      exact hout x (by simp only [← hneAdef]; omega)
  · simp only [Expr.size, argsSize, memCopyContract, composeWalkContract, List.getD_cons_succ,
      List.getD_cons_zero, Nat.sub_zero]
    rw [hnvA, hneA]
    have h1 : VL.length * 20 ≤ neA * L * 20 := Nat.mul_le_mul_right _ hcV
    have h2 : EL.length * 20 ≤ neA * L * 20 := Nat.mul_le_mul_right _ hcE
    nlinarith [Nat.mul_le_mul_left neA (show 80 * L + 600 + 1 + 8 ≤ 80 * L + 620 by omega)]

end MinCostFlow.Spanner
