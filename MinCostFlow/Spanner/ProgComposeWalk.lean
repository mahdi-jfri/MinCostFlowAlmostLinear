module

public import MinCostFlow.Spanner.ProgComposeStep

@[expose] public section

/-!
# Writing a Composed Walk

This file gives the loop that writes the walk `composeAux B embBC vs js` for a stored walk with
vertices `vs` and edges `js`. Each step is written to a scratch area by `composeStepBody`. Its
edges are added to an edge buffer, and its vertices to a vertex buffer, all of them for the first
step with an edge and all but the first one for later steps (`foldApp_verts`). This part gives
the list facts used by the loop.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited LSF.Program

/-- The steps of `composeAux B embBC vs js`. -/
def stepsOf (B : Graph) (embBC : ℕ → Walk) (vs js : List ℕ) (i : ℕ) : Walk :=
  composeStep B embBC (vs.getD i 0) (vs.getD (i + 1) 0) (js.getD i 0)

/-- The steps among the first `k` that have at least one edge. -/
def keptSteps (f : ℕ → Walk) (k : ℕ) : List Walk :=
  ((List.range k).map f).filter fun S => !S.edges.isEmpty

/-- The edges of the first `k` steps. -/
def stepEdges (f : ℕ → Walk) (k : ℕ) : List ℕ :=
  ((List.range k).map f).flatMap Walk.edges

lemma keptSteps_eq_nil_iff (f : ℕ → Walk) (k : ℕ) :
    keptSteps f k = [] ↔ stepEdges f k = [] := by
  unfold keptSteps stepEdges
  rw [List.filter_eq_nil_iff, List.flatMap_eq_nil_iff]
  simp

lemma stepEdges_succ (f : ℕ → Walk) (k : ℕ) :
    stepEdges f (k + 1) = stepEdges f k ++ (f k).edges := by
  simp [stepEdges, List.range_succ, List.flatMap_append]

/-- The vertex list after one more step, with `off = 1` exactly when an earlier step had an
edge. -/
lemma joinVerts_keptSteps_succ (f : ℕ → Walk) (k : ℕ) (hk : (f k).edges ≠ []) :
    joinVerts (keptSteps f (k + 1)) = joinVerts (keptSteps f k) ++
      (f k).verts.drop (if stepEdges f k = [] then 0 else 1) := by
  unfold keptSteps
  rw [filter_range_succ, ite_eq_right (by simpa using hk), joinVerts_append_single]
  by_cases h : stepEdges f k = []
  · have h' := (keptSteps_eq_nil_iff f k).mpr h
    unfold keptSteps at h'
    rw [ite_eq_left h', ite_eq_left h, h']
    simp [joinVerts]
  · have h' : ¬ keptSteps f k = [] := fun h'' => h ((keptSteps_eq_nil_iff f k).mp h'')
    unfold keptSteps at h'
    rw [ite_eq_right h', ite_eq_right h, List.drop_one]

lemma joinVerts_keptSteps_succ_of_nil (f : ℕ → Walk) (k : ℕ) (hk : (f k).edges = []) :
    keptSteps f (k + 1) = keptSteps f k := by
  unfold keptSteps
  rw [filter_range_succ, ite_eq_left (by simp [hk]), List.append_nil]

lemma listAt_drop {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ} (h : ListAt mem a l) (d : ℕ) :
    ListAt mem (a + d) (l.drop d) := fun t ht => by
  rw [List.getElem_drop, ← h (d + t) (by simp at ht; omega), Nat.add_assoc]

lemma ev_lt_ite {w : ℕ} {st : State} {e₁ e₂ : Expr} {a b : ℕ}
    (h₁ : e₁.eval w st = some a) (h₂ : e₂.eval w st = some b) (hw : 1 < 2 ^ w) :
    (Expr.bin .lt e₁ e₂).eval w st = some (if a < b then 1 else 0) := by
  by_cases h : a < b
  · rw [ite_eq_left h]; exact ev_lt_t h₁ h₂ h hw
  · rw [ite_eq_right h]; exact ev_lt_f h₁ h₂ (by omega) hw

/-- The loop body of `composeWalkBody`. -/
def composeWalkLoop (fs fc : ℕ) : Stmt :=
  .assign 13 (.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 10))) ;;
  .assign 14 (.load (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 10))) ;;
  .assign 15 (.load (.bin .add (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 8)) (.reg 10))) ;;
  .call 16 fs [.reg 0, .reg 1, .reg 13, .reg 14, .reg 15, .reg 4] ;;
  .assign 13 (.load (.reg 4)) ;;
  .assign 14 (.load (.bin .add (.bin .add (.reg 4) (.const 1)) (.reg 13))) ;;
  .assign 15 (.bin .lt (.const 0) (.reg 14)) ;;
  .assign 16 (.bin .lt (.const 0) (.reg 12)) ;;
  .assign 17 (.bin .sub (.bin .mul (.reg 15) (.reg 13)) (.bin .mul (.reg 15) (.reg 16))) ;;
  .call 18 fc [.bin .add (.reg 5) (.reg 11), .bin .add (.bin .add (.reg 4) (.const 1)) (.reg 16),
    .reg 17] ;;
  .call 18 fc [.bin .add (.reg 6) (.reg 12), .bin .add (.bin .add (.reg 4) (.const 2)) (.reg 13),
    .reg 14] ;;
  .assign 11 (.bin .add (.reg 11) (.reg 17)) ;;
  .assign 12 (.bin .add (.reg 12) (.reg 14))

/-- The stored walk `Q` at `A` and the data for `composeStepBody` lie below the scratch area
`S`. The scratch area, the vertex buffer `VB`, the edge buffer `EB` and the output `dst` follow
one another, each step has encoded length at most `L`, and the output fits in a word. -/
def ComposeWalkPre (mem : ℕ → ℕ) (bAddr E A dst S VB EB L : ℕ) (B : Graph) (embBC : ℕ → Walk)
    (Q : Walk) (w : ℕ) : Prop :=
  GraphAt mem bAddr B ∧ EmbAt mem E B.m embBC ∧ EmbBounded mem E B.m embBC S ∧
    bAddr + (2 + 2 * B.m) ≤ S ∧ WalkAt mem A Q ∧ A + (Walk.encode Q).length ≤ S ∧
    (Q.verts.length = Q.edges.length + 1 ∨ (Q.verts = [] ∧ Q.edges = [])) ∧
    (∀ j ∈ Q.edges, j < B.m) ∧ (∀ x ∈ Q.verts, x < 2 ^ w) ∧
    (∀ j < B.m, (Walk.encode (embBC j)).length ≤ L) ∧
    (∀ j < B.m, (embBC j).edges ≠ [] → (embBC j).verts ≠ []) ∧
    S + L ≤ VB ∧ VB + Q.edges.length * L ≤ EB ∧ EB + Q.edges.length * L ≤ dst ∧
    dst + 2 + 2 * (Q.edges.length * L) < 2 ^ w ∧ 1 < 2 ^ w

/-- Loop invariant after `i` steps. -/
def CWInv (mem : ℕ → ℕ) (bAddr E A dst S VB EB L : ℕ) (B : Graph) (embBC : ℕ → Walk)
    (Q : Walk) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = bAddr ∧ st.regs 1 = E ∧ st.regs 2 = A ∧ st.regs 3 = dst ∧ st.regs 4 = S ∧
    st.regs 5 = VB ∧ st.regs 6 = EB ∧ st.regs 8 = Q.verts.length ∧ st.regs 9 = Q.edges.length ∧
    st.regs 10 = i ∧
    st.regs 11 = (joinVerts (keptSteps (stepsOf B embBC Q.verts Q.edges) i)).length ∧
    st.regs 12 = (stepEdges (stepsOf B embBC Q.verts Q.edges) i).length ∧ i ≤ Q.edges.length ∧
    (joinVerts (keptSteps (stepsOf B embBC Q.verts Q.edges) i)).length ≤ i * L ∧
    (stepEdges (stepsOf B embBC Q.verts Q.edges) i).length ≤ i * L ∧
    ListAt st.mem VB (joinVerts (keptSteps (stepsOf B embBC Q.verts Q.edges) i)) ∧
    ListAt st.mem EB (stepEdges (stepsOf B embBC Q.verts Q.edges) i) ∧
    ∀ x, x < S ∨ EB + Q.edges.length * L ≤ x → st.mem x = mem x

lemma composeStep_encode_length (B : Graph) (embBC : ℕ → Walk) (u v j : ℕ) :
    (Walk.encode (composeStep B embBC u v j)).length = (Walk.encode (embBC j)).length := by
  unfold composeStep
  split_ifs <;> simp [walk_encode_length, Walk.reverse]

lemma composeStep_edges (B : Graph) (embBC : ℕ → Walk) (u v j : ℕ) :
    (composeStep B embBC u v j).edges ≠ [] → (embBC j).edges ≠ [] := by
  unfold composeStep
  split_ifs <;> simp [Walk.reverse]

lemma composeStep_verts (B : Graph) (embBC : ℕ → Walk) (u v j : ℕ) :
    (embBC j).verts ≠ [] → (composeStep B embBC u v j).verts ≠ [] := by
  unfold composeStep
  split_ifs <;> simp [Walk.reverse]

lemma composeWalk_step {w : ℕ} {p : Program} {fs fc : ℕ}
    (hfs : MeetsContract w p fs (composeStepContract w))
    (hfc : MeetsContract w p fc (memCopyContract w))
    {mem : ℕ → ℕ} {bAddr E A dst S VB EB L : ℕ} {B : Graph} {embBC : ℕ → Walk} {Q : Walk}
    (hpre : ComposeWalkPre mem bAddr E A dst S VB EB L B embBC Q w) (i : ℕ)
    (hi : i < Q.edges.length) :
    Triple w p (CWInv mem bAddr E A dst S VB EB L B embBC Q i) (composeWalkLoop fs fc)
      (normalPost fun st₁ =>
        CWInv mem bAddr E A dst S VB EB L B embBC Q (i + 1)
          { st₁ with regs := Function.update st₁.regs 10 (i + 1) } ∧ st₁.regs 10 = i)
      (fun _ => 80 * L + 600) := by
  obtain ⟨hG, hEmb, hBnd, hGS, hQ, hQS, hQshape, hQe, hQv, hL, hEV, hSV, hVE, hED, hdw,
    hw1⟩ := hpre
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r8, r9, r10, r11, r12, hin, hcV, hcE, hVB, hEB, hout⟩ := hI
  set f := stepsOf B embBC Q.verts Q.edges with hfdef
  set cV := (joinVerts (keptSteps f i)).length with hcVdef
  set cE := (stepEdges f i).length with hcEdef
  obtain ⟨hnvA, hvs, hneA, hjs⟩ := walkAt_iff.mp hQ
  have hQlen := walk_encode_length Q
  set nvA := Q.verts.length with hnvAdef
  set neA := Q.edges.length with hneAdef
  have hnv1 : nvA = neA + 1 := by
    rcases hQshape with h | ⟨-, h2⟩
    · exact h
    · exfalso; simp [neA, h2] at hi
  have hst : ∀ x, x < S → st.mem x = mem x := fun x hx => hout x (Or.inl hx)
  have hil : i < Q.verts.length := by omega
  have hil1 : i + 1 < Q.verts.length := by omega
  set u := Q.verts[i] with hu
  set v := Q.verts[i + 1] with hv
  set j := Q.edges[i] with hj
  have hjB : j < B.m := hQe j (List.getElem_mem hi)
  have huw : u < 2 ^ w := hQv u (List.getElem_mem hil)
  have hvw : v < 2 ^ w := hQv v (List.getElem_mem hil1)
  have hLj := hL j hjB
  have hlenj := walk_encode_length (embBC j)
  have hiL : i * L + L ≤ neA * L := by
    have := Nat.mul_le_mul_right L (show i + 1 ≤ neA by omega); rw [Nat.succ_mul] at this
    exact this
  have hBm : bAddr + (2 + 2 * B.m) ≤ S := hGS
  have hEm : E + B.m ≤ S := hBnd.1
  -- Step `i` is the step along `u`, `v` and edge `j`.
  have hfi : f i = composeStep B embBC u v j := by
    simp only [hfdef, stepsOf, List.getD_eq_getElem _ _ hil, List.getD_eq_getElem _ _ hil1,
      List.getD_eq_getElem _ _ hi]
    rfl
  -- Reading `u`, `v` and `j`.
  have e13 : (Expr.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 10))).eval w st =
      some u :=
    ev_load' (ev_add (ev_add (ev_reg r2 (by omega)) (ev_const hw1) (by omega))
      (ev_reg r10 (by omega)) (by omega)) (by rw [hst _ (by omega)]; exact hvs i hil)
  let s1 : State := { st with regs := Function.update st.regs 13 u }
  have e14 : (Expr.load (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 10))).eval w s1 =
      some v :=
    ev_load' (ev_add (ev_add (ev_reg (v := A) (by simp [s1, r2]) (by omega))
      (ev_const (c := 2) (by omega)) (by omega)) (ev_reg (v := i) (by simp [s1, r10]) (by omega))
      (by omega))
      (by simp only [s1]; rw [hst _ (by omega), show A + 2 + i = A + 1 + (i + 1) by omega]
          exact hvs (i + 1) hil1)
  let s2 : State := { s1 with regs := Function.update s1.regs 14 v }
  have e15 : (Expr.load (.bin .add (.bin .add (.bin .add (.reg 2) (.const 2)) (.reg 8))
      (.reg 10))).eval w s2 = some j :=
    ev_load' (ev_add (ev_add (ev_add (ev_reg (v := A) (by simp [s2, s1, r2]) (by omega))
      (ev_const (c := 2) (by omega)) (by omega)) (ev_reg (v := nvA) (by simp [s2, s1, r8])
      (by omega)) (by omega)) (ev_reg (v := i) (by simp [s2, s1, r10]) (by omega)) (by omega))
      (by simp only [s2, s1]; rw [hst _ (by omega)]; exact hjs i hi)
  let s3 : State := { s2 with regs := Function.update s2.regs 15 j }
  have hargs1 : evalArgs w s3 [.reg 0, .reg 1, .reg 13, .reg 14, .reg 15, .reg 4] =
      some [bAddr, E, u, v, j, S] := by
    simp [evalArgs, Expr.eval, s3, s2, s1, r0, r1, r4, huw, hvw,
      show bAddr < 2 ^ w by omega, show E < 2 ^ w by omega, show j < 2 ^ w by omega,
      show S < 2 ^ w by omega]
  have hagree : ∀ k < S, st.mem k = mem k := hst
  have hGst : GraphAt st.mem bAddr B :=
    hG.of_agree_below (by rw [graph_encode_length]; omega) hagree
  obtain ⟨hEst, hBst⟩ := embAt_preserve hEmb hBnd hagree
  have hpreS : ComposeStepPre s3.mem bAddr E j S B embBC w :=
    ⟨hGst, hEst, hBst, hBm, hjB, by omega, hw1⟩
  refine runs_start_le ?_
  refine runs_seq_assign_le e13 ?_
  refine runs_seq_assign_le e14 ?_
  refine runs_seq_assign_le e15 ?_
  refine runs_seq_call_le hfs hargs1 ?_ ⟨_, _, _, _, _, _, _, _, rfl, hpreS⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  intro v₁ mem₁ pos₁ hpost₁
  obtain ⟨hWS0, hfr0⟩ := hpost₁ _ _ _ _ _ _ _ _ rfl hpreS
  rw [← hfi] at hWS0
  have hWS : WalkAt mem₁ S (f i) := hWS0
  have hfr₁ : ∀ x, x < S ∨ S + (Walk.encode (embBC j)).length ≤ x → mem₁ x = st.mem x := hfr0
  have hZlen : (Walk.encode (f i)).length = (Walk.encode (embBC j)).length := by
    rw [hfi]; exact composeStep_encode_length _ _ _ _ _
  obtain ⟨hsnv, hsverts, hsne, hsedges⟩ := walkAt_iff.mp hWS
  have hZl := walk_encode_length (f i)
  set snv := (f i).verts.length with hsnvdef
  set sne := (f i).edges.length with hsnedef
  have hZverts : sne ≠ 0 → 1 ≤ snv := fun h => by
    have h1 : (f i).edges ≠ [] := fun h' => h (by simp [sne, h'])
    rw [hfi] at h1
    have h2 := composeStep_verts B embBC u v j (hEV j hjB (composeStep_edges B embBC u v j h1))
    rw [← hfi] at h2
    exact List.length_pos_of_ne_nil h2
  set g := if 0 < sne then 1 else 0 with hgdef
  set off := if 0 < cE then 1 else 0 with hoffdef
  have hgoff : (g = 0 ∧ sne = 0) ∨ (g = 1 ∧ 0 < sne ∧ off ≤ snv) := by
    by_cases h : 0 < sne
    · right; refine ⟨by simp [g, h], h, ?_⟩
      have := hZverts (by omega); simp only [off]; split_ifs <;> omega
    · left; exact ⟨by simp [g, h], by omega⟩
  have hoff1 : off ≤ 1 := by simp only [off]; split_ifs <;> omega
  set lenV := g * snv - g * off with hlenVdef
  have hlenV : (g = 0 ∧ sne = 0 ∧ lenV = 0) ∨ (g = 1 ∧ 0 < sne ∧ off ≤ snv ∧ lenV = snv - off) := by
    rcases hgoff with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · left; exact ⟨h1, h2, by simp [lenV, h1]⟩
    · right; exact ⟨h1, h2, h3, by simp [lenV, h1]⟩
  let s4 : State := { mem := mem₁, regs := Function.update s3.regs 16 v₁, pos := pos₁ }
  have e13' : (Expr.load (.reg 4)).eval w s4 = some snv :=
    ev_load' (ev_reg (v := S) (by simp [s4, s3, s2, s1, r4]) (by omega)) hsnv
  let s5 : State := { s4 with regs := Function.update s4.regs 13 snv }
  have e14' : (Expr.load (.bin .add (.bin .add (.reg 4) (.const 1)) (.reg 13))).eval w s5 =
      some sne :=
    ev_load' (ev_add (ev_add (ev_reg (v := S) (by simp [s5, s4, s3, s2, s1, r4]) (by omega))
      (ev_const hw1) (by omega)) (ev_reg (v := snv) (by simp [s5]) (by omega)) (by omega)) hsne
  let s6 : State := { s5 with regs := Function.update s5.regs 14 sne }
  have e15' : (Expr.bin .lt (.const 0) (.reg 14)).eval w s6 = some g :=
    ev_lt_ite (ev_const (by omega)) (ev_reg (v := sne) (by simp [s6]) (by omega)) hw1
  let s7 : State := { s6 with regs := Function.update s6.regs 15 g }
  have e16' : (Expr.bin .lt (.const 0) (.reg 12)).eval w s7 = some off :=
    ev_lt_ite (ev_const (by omega)) (ev_reg (v := cE) (by simp [s7, s6, s5, s4, s3, s2, s1, r12])
      (by omega)) hw1
  let s8 : State := { s7 with regs := Function.update s7.regs 16 off }
  have e17' : (Expr.bin .sub (.bin .mul (.reg 15) (.reg 13)) (.bin .mul (.reg 15) (.reg 16))).eval
      w s8 = some lenV := by
    have m1 := ev_mul (w := w) (st := s8) (e₁ := .reg 15) (e₂ := .reg 13)
      (ev_reg (v := g) (by simp [s8, s7]) (by omega))
      (ev_reg (v := snv) (by simp [s8, s7, s6, s5]) (by omega))
      (by rcases hlenV with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> omega)
    have m2 := ev_mul (w := w) (st := s8) (e₁ := .reg 15) (e₂ := .reg 16)
      (ev_reg (v := g) (by simp [s8, s7]) (by omega))
      (ev_reg (v := off) (by simp [s8]) (by omega))
      (by rcases hlenV with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> omega)
    exact ev_sub m1 m2 (by rcases hlenV with ⟨h1, -⟩ | ⟨h1, -, h3, -⟩ <;> rw [h1] <;> omega)
      (by rcases hlenV with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> omega)
  let s9 : State := { s8 with regs := Function.update s8.regs 17 lenV }
  have hlenVle : lenV ≤ snv := by rcases hlenV with ⟨-, -, h⟩ | ⟨-, -, -, h⟩ <;> omega
  have hoffV : off + lenV ≤ snv + 1 := by rcases hlenV with ⟨-, -, h⟩ | ⟨-, -, h3, h⟩ <;> omega
  have hargs2 : evalArgs w s9 [.bin .add (.reg 5) (.reg 11),
      .bin .add (.bin .add (.reg 4) (.const 1)) (.reg 16), .reg 17] =
      some [VB + cV, S + 1 + off, lenV] := by
    have a1 : (Expr.bin .add (.reg 5) (.reg 11)).eval w s9 = some (VB + cV) :=
      ev_add (ev_reg (v := VB) (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, r5]) (by omega))
        (ev_reg (v := cV) (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, r11]) (by omega))
        (by omega)
    have a2 : (Expr.bin .add (.bin .add (.reg 4) (.const 1)) (.reg 16)).eval w s9 =
        some (S + 1 + off) :=
      ev_add (ev_add (ev_reg (v := S) (by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, r4])
        (by omega)) (ev_const hw1) (by omega)) (ev_reg (v := off) (by simp [s9, s8]) (by omega))
        (by omega)
    have a3 : (Expr.reg 17).eval w s9 = some lenV := ev_reg (v := lenV) (by simp [s9]) (by omega)
    simp [evalArgs, a1, a2, a3]
  refine runs_seq_assign_le e13' ?_
  refine runs_seq_assign_le e14' ?_
  refine runs_seq_assign_le e15' ?_
  refine runs_seq_assign_le e16' ?_
  refine runs_seq_assign_le e17' ?_
  refine runs_seq_call_le hfc hargs2 ?_ ⟨VB + cV, S + 1 + off, lenV, rfl, by omega, by omega,
    Or.inr (by omega)⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  intro v₂ mem₂ pos₂ hpost₂
  obtain ⟨d', s', l', hargs', -, hcopy0, hother0⟩ := hpost₂
  simp only [List.cons.injEq, and_true] at hargs'
  obtain ⟨hd', hs', hl'⟩ := hargs'
  subst hd' hs' hl'
  have hcopy₂ : ∀ t < lenV, mem₂ (VB + cV + t) = mem₁ (S + 1 + off + t) := hcopy0
  have hfr₂ : ∀ x, x < VB + cV ∨ VB + cV + lenV ≤ x → mem₂ x = mem₁ x := hother0
  let s10 : State := { mem := mem₂, regs := Function.update s9.regs 18 v₂, pos := pos₂ }
  have hargs3 : evalArgs w s10 [.bin .add (.reg 6) (.reg 12),
      .bin .add (.bin .add (.reg 4) (.const 2)) (.reg 13), .reg 14] =
      some [EB + cE, S + 2 + snv, sne] := by
    have a1 : (Expr.bin .add (.reg 6) (.reg 12)).eval w s10 = some (EB + cE) :=
      ev_add (ev_reg (v := EB) (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r6]) (by omega))
        (ev_reg (v := cE) (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r12]) (by omega))
        (by omega)
    have a2 : (Expr.bin .add (.bin .add (.reg 4) (.const 2)) (.reg 13)).eval w s10 =
        some (S + 2 + snv) :=
      ev_add (ev_add (ev_reg (v := S) (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r4])
        (by omega)) (ev_const (c := 2) (by omega)) (by omega))
        (ev_reg (v := snv) (by simp [s10, s9, s8, s7, s6, s5]) (by omega)) (by omega)
    have a3 : (Expr.reg 14).eval w s10 = some sne :=
      ev_reg (v := sne) (by simp [s10, s9, s8, s7, s6]) (by omega)
    simp [evalArgs, a1, a2, a3]
  refine runs_seq_call_le hfc hargs3 ?_ ⟨EB + cE, S + 2 + snv, sne, rfl, by omega, by omega,
    Or.inr (by omega)⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  intro v₃ mem₃ pos₃ hpost₃
  obtain ⟨d', s', l', hargs', -, hcopy0', hother0'⟩ := hpost₃
  simp only [List.cons.injEq, and_true] at hargs'
  obtain ⟨hd', hs', hl'⟩ := hargs'
  subst hd' hs' hl'
  have hcopy₃ : ∀ t < sne, mem₃ (EB + cE + t) = mem₂ (S + 2 + snv + t) := hcopy0'
  have hfr₃ : ∀ x, x < EB + cE ∨ EB + cE + sne ≤ x → mem₃ x = mem₂ x := hother0'
  let s11 : State := { mem := mem₃, regs := Function.update s10.regs 18 v₃, pos := pos₃ }
  have e11 : (Expr.bin .add (.reg 11) (.reg 17)).eval w s11 = some (cV + lenV) :=
    ev_add (ev_reg (v := cV) (by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r11])
      (by omega)) (ev_reg (v := lenV) (by simp [s11, s10, s9]) (by omega)) (by omega)
  let s12 : State := { s11 with regs := Function.update s11.regs 11 (cV + lenV) }
  have e12 : (Expr.bin .add (.reg 12) (.reg 14)).eval w s12 = some (cE + sne) :=
    ev_add (ev_reg (v := cE) (by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r12])
      (by omega)) (ev_reg (v := sne) (by simp [s12, s11, s10, s9, s8, s7, s6]) (by omega))
      (by omega)
  -- The memory after the step, below `VB + cV` and on the edge buffer.
  have hVBkeep : ∀ t < cV, mem₃ (VB + t) = st.mem (VB + t) := fun t ht => by
    rw [hfr₃ _ (Or.inl (by omega)), hfr₂ _ (Or.inl (by omega)), hfr₁ _ (Or.inr (by omega))]
  have hEBkeep : ∀ t < cE, mem₃ (EB + t) = st.mem (EB + t) := fun t ht => by
    rw [hfr₃ _ (Or.inl (by omega)), hfr₂ _ (Or.inr (by omega)), hfr₁ _ (Or.inr (by omega))]
  have hstepE : stepEdges f (i + 1) = stepEdges f i ++ (f i).edges := stepEdges_succ f i
  have hoffeq : (if stepEdges f i = [] then 0 else 1) = off := by
    simp only [off, cE]
    by_cases h : stepEdges f i = []
    · simp [h]
    · rw [ite_eq_right h, ite_eq_left (List.length_pos_of_ne_nil h)]
  have hJV : joinVerts (keptSteps f (i + 1)) =
      joinVerts (keptSteps f i) ++ (f i).verts.drop off ∧ lenV = snv - off ∨
      joinVerts (keptSteps f (i + 1)) = joinVerts (keptSteps f i) ∧ lenV = 0 := by
    rcases hlenV with ⟨-, h2, h3⟩ | ⟨-, h2, -, h4⟩
    · right
      have hnil : (f i).edges = [] := List.eq_nil_of_length_eq_zero h2
      exact ⟨by rw [joinVerts_keptSteps_succ_of_nil f i hnil], h3⟩
    · left
      have hne : (f i).edges ≠ [] := fun h => by simp [sne, h] at h2
      exact ⟨by rw [joinVerts_keptSteps_succ f i hne, hoffeq], h4⟩
  have hVlen : (joinVerts (keptSteps f (i + 1))).length = cV + lenV := by
    rcases hJV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, List.length_append, List.length_drop, h2]
    · rw [h1, h2, Nat.add_zero]
  refine runs_seq_assign_le e11 ?_
  refine runs_assign_le e12 ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_, ?_, by omega,
    ?_, ?_, ?_, ?_, ?_⟩, by simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r10]⟩ ?_
  · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r0]
  · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r1]
  · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r2]
  · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r3]
  · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r4]
  · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r5]
  · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r6]
  · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r8, hnvAdef]
  · simp [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, r9, hneAdef]
  · simp only [Function.update_of_ne (show (11 : ℕ) ≠ 10 by omega), Function.update_of_ne
      (show (11 : ℕ) ≠ 12 by omega), s12, Function.update_self]
    exact hVlen.symm
  · simp only [Function.update_of_ne (show (12 : ℕ) ≠ 10 by omega), Function.update_self]
    rw [hstepE, List.length_append]
  · rw [hVlen, Nat.succ_mul]; omega
  · rw [hstepE, List.length_append, Nat.succ_mul]; omega
  · -- The vertex buffer.
    dsimp only
    rcases hJV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, listAt_append]
      refine ⟨ListAt.of_agree hVB fun t ht => hVBkeep t ht, fun t ht => ?_⟩
      rw [List.length_drop] at ht
      rw [hfr₃ _ (Or.inl (by omega)), hcopy₂ t (by omega)]
      exact listAt_drop hsverts off t (by rw [List.length_drop]; omega)
    · rw [h1]
      exact ListAt.of_agree hVB fun t ht => hVBkeep t ht
  · -- The edge buffer.
    dsimp only
    rw [hstepE, listAt_append]
    refine ⟨ListAt.of_agree hEB fun t ht => hEBkeep t ht, fun t ht => ?_⟩
    rw [← hcEdef, hcopy₃ t ht, hfr₂ _ (Or.inl (by omega))]
    exact hsedges t ht
  · intro x hx
    simp only [← hneAdef] at hx
    dsimp only
    rw [hfr₃ x (by omega), hfr₂ x (by omega), hfr₁ x (by omega)]
    exact hout x hx
  · -- The cost.
    have hPj := hEmb j hjB
    obtain ⟨hnvj, -, hnej, -⟩ := walkAt_iff.mp hPj
    have hPb := hBnd.2 j hjB
    have c1 : st.mem (E + j) = mem (E + j) := hst _ (by omega)
    have c2 : st.mem (mem (E + j)) = (embBC j).verts.length := by
      rw [hst _ (by rw [walk_encode_length] at hPb; omega)]; exact hnvj
    have c3 : st.mem (mem (E + j) + 1 + (embBC j).verts.length) = (embBC j).edges.length := by
      rw [hst _ (by rw [walk_encode_length] at hPb; omega)]; exact hnej
    simp only [Expr.size, argsSize, memCopyContract, composeStepContract, List.getD_cons_succ,
      List.getD_cons_zero]
    rw [c1, c2, c3]
    omega

end MinCostFlow.Spanner
