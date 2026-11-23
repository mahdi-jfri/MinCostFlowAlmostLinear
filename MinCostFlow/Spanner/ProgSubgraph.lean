module

public import MinCostFlow.Spanner.ProgSetup
public import MinCostFlow.Spanner.Layouts

@[expose] public section

/-!
# Writing the Subgraph `J̃`

After the kept edges are known, `Sparsify` outputs `J̃ = ⟨J.n, kept.map (J.edges.getD · (0, 0))⟩`.
The procedure `subgraphBody` writes the encoding of `J̃` at `dst`: first `J.n` and the number of
kept edges, then the two end points of each kept edge, read from the encoding of `J`. The result
is `subgraph_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited

/-- The end points of a list of edges, one edge after the other. -/
def edgeWords (es : List (ℕ × ℕ)) : List ℕ := es.flatMap fun e => [e.1, e.2]

lemma edgeWords_append (a b : List (ℕ × ℕ)) : edgeWords (a ++ b) = edgeWords a ++ edgeWords b := by
  simp [edgeWords]

lemma edgeWords_length (es : List (ℕ × ℕ)) : (edgeWords es).length = 2 * es.length := by
  induction es with
  | nil => simp [edgeWords]
  | cons e es ih => simp [edgeWords] at ih ⊢; omega

/-- The sub-graph of `J` on the edges with numbers in `kept`. -/
def subgraphOf (J : Graph) (kept : List ℕ) : Graph :=
  ⟨J.n, kept.map fun j => J.edges.getD j (0, 0)⟩

/-- Procedure body, at `args = [jAddr, kAddr, k, dst]`. -/
def subgraphBody : Stmt :=
  .store (.reg 3) (.load (.reg 0)) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 2) ;;
  forRange 4 (.const 0) (.reg 2) (
    .assign 5 (.load (.bin .add (.reg 1) (.reg 4))) ;;
    .assign 6 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .add (.reg 5) (.reg 5))) ;;
    .assign 7 (.bin .add (.bin .add (.reg 3) (.const 2)) (.bin .add (.reg 4) (.reg 4))) ;;
    .store (.reg 7) (.load (.reg 6)) ;;
    .store (.bin .add (.reg 7) (.const 1)) (.load (.bin .add (.reg 6) (.const 1)))) ;;
  .ret (.const 0)

/-- `J` is at `jAddr`, the kept edge numbers at `kAddr`, both below `dst`, and the output fits. -/
def SubgraphPre (mem : ℕ → ℕ) (jAddr kAddr k dst : ℕ) (J : Graph) (kept : List ℕ) (w : ℕ) :
    Prop :=
  GraphAt mem jAddr J ∧ ListAt mem kAddr kept ∧ kept.length = k ∧ (∀ j ∈ kept, j < J.m) ∧
    jAddr + J.encode.length ≤ dst ∧ kAddr + k ≤ dst ∧ dst + 2 + 2 * k < 2 ^ w ∧ 1 < 2 ^ w

/-- Contract of `subgraphBody`. -/
def subgraphContract (w : ℕ) : Contract where
  pre args mem := ∃ jAddr kAddr k dst J kept, args = [jAddr, kAddr, k, dst] ∧
    SubgraphPre mem jAddr kAddr k dst J kept w
  post args mem _ mem' := ∀ jAddr kAddr k dst J kept, args = [jAddr, kAddr, k, dst] →
    SubgraphPre mem jAddr kAddr k dst J kept w →
    GraphAt mem' dst (subgraphOf J kept) ∧
      ∀ x, x < dst ∨ dst + 2 + 2 * k ≤ x → mem' x = mem x
  cost args _ := args.getD 2 0 * 60 + 40

/-- A load needs no bound on the loaded value. -/
lemma ev_load' {w : ℕ} {st : State} {e : Expr} {a v : ℕ}
    (ha : e.eval w st = some a) (hm : st.mem a = v) : (Expr.load e).eval w st = some v := by
  simp [Expr.eval, ha, hm]

/-- Loop invariant after `i` kept edges. -/
def SubgraphInv (mem : ℕ → ℕ) (jAddr kAddr k dst : ℕ) (J : Graph) (kept : List ℕ) (i : ℕ)
    (st : State) : Prop :=
  st.regs 0 = jAddr ∧ st.regs 1 = kAddr ∧ st.regs 2 = k ∧ st.regs 3 = dst ∧ st.regs 4 = i ∧
    i ≤ k ∧ st.mem dst = J.n ∧ st.mem (dst + 1) = k ∧
    ListAt st.mem (dst + 2) (edgeWords ((kept.take i).map fun j => J.edges.getD j (0, 0))) ∧
    ∀ x, x < dst ∨ dst + 2 + 2 * i ≤ x → st.mem x = mem x

lemma subgraph_step {w : ℕ} {p : Program} {mem : ℕ → ℕ} {jAddr kAddr k dst : ℕ} {J : Graph}
    {kept : List ℕ} (hpre : SubgraphPre mem jAddr kAddr k dst J kept w) (i : ℕ) (hi : i < k) :
    Triple w p (SubgraphInv mem jAddr kAddr k dst J kept i)
      (.assign 5 (.load (.bin .add (.reg 1) (.reg 4))) ;;
        .assign 6 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .add (.reg 5) (.reg 5))) ;;
        .assign 7 (.bin .add (.bin .add (.reg 3) (.const 2)) (.bin .add (.reg 4) (.reg 4))) ;;
        .store (.reg 7) (.load (.reg 6)) ;;
        .store (.bin .add (.reg 7) (.const 1)) (.load (.bin .add (.reg 6) (.const 1))))
      (normalPost fun st₁ =>
        SubgraphInv mem jAddr kAddr k dst J kept (i + 1)
          { st₁ with regs := Function.update st₁.regs 4 (i + 1) } ∧ st₁.regs 4 = i)
      (fun _ => 50) := by
  obtain ⟨hJ, hK, hlen, hlt, hJd, hKd, hdw, hw1⟩ := hpre
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, r4, hik, hn, hm, hlist, hout⟩ := hI
  rw [graph_encode_length] at hJd
  have hst : ∀ x, x < dst → st.mem x = mem x := fun x hx => hout x (Or.inl hx)
  have hil : i < kept.length := by omega
  set j := kept[i]'hil with hjdef
  have hjm : j < J.m := hlt j (List.getElem_mem hil)
  have hkj : st.mem (kAddr + i) = j := by rw [hst _ (by omega)]; exact hK.getElem hil
  have hu : st.mem (jAddr + (2 + 2 * j)) = (J.edges.getD j (0, 0)).1 := by
    rw [hst _ (by omega)]; exact graphAt_edge_fst_getD hJ hjm
  have hv : st.mem (jAddr + (2 + 2 * j) + 1) = (J.edges.getD j (0, 0)).2 := by
    rw [hst _ (by omega)]
    rw [show jAddr + (2 + 2 * j) + 1 = jAddr + 3 + 2 * j by omega, graphAt_edge_snd hJ hjm,
      List.getD_eq_getElem _ _ hjm]
  have hwd : dst < 2 ^ w := by omega
  have e5 : (Expr.load (.bin .add (.reg 1) (.reg 4))).eval w st = some j :=
    ev_load (ev_add (ev_reg r1 (by omega)) (ev_reg r4 (by omega)) (by omega)) hkj (by omega)
  let s1 : State := { st with regs := Function.update st.regs 5 j }
  have e6 : (Expr.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .add (.reg 5) (.reg 5))).eval w s1 =
      some (jAddr + 2 + (j + j)) :=
    ev_add (ev_add (ev_reg (v := jAddr) (by simp [s1, r0]) (by omega)) (ev_const (c := 2) (by omega))
      (by omega)) (ev_add (ev_reg (v := j) (by simp [s1]) (by omega))
      (ev_reg (v := j) (by simp [s1]) (by omega)) (by omega)) (by omega)
  let s2 : State := { s1 with regs := Function.update s1.regs 6 (jAddr + 2 + (j + j)) }
  have e7 : (Expr.bin .add (.bin .add (.reg 3) (.const 2)) (.bin .add (.reg 4) (.reg 4))).eval w s2 =
      some (dst + 2 + (i + i)) :=
    ev_add (ev_add (ev_reg (v := dst) (by simp [s2, s1, r3]) hwd) (ev_const (c := 2) (by omega))
      (by omega)) (ev_add (ev_reg (v := i) (by simp [s2, s1, r4]) (by omega))
      (ev_reg (v := i) (by simp [s2, s1, r4]) (by omega)) (by omega)) (by omega)
  let s3 : State := { s2 with regs := Function.update s2.regs 7 (dst + 2 + (i + i)) }
  have hs3 : s3.mem = st.mem := rfl
  have ea1 : (Expr.reg 7).eval w s3 = some (dst + 2 + (i + i)) :=
    ev_reg (v := dst + 2 + (i + i)) (by simp [s3]) (by omega)
  have ev1 : (Expr.load (.reg 6)).eval w s3 = some (J.edges.getD j (0, 0)).1 :=
    ev_load' (ev_reg (v := jAddr + 2 + (j + j)) (by simp [s3, s2]) (by omega))
      (by rw [hs3, show jAddr + 2 + (j + j) = jAddr + (2 + 2 * j) by omega]; exact hu)
  let s4 : State :=
    { s3 with mem := Function.update s3.mem (dst + 2 + (i + i)) (J.edges.getD j (0, 0)).1 }
  have ea2 : (Expr.bin .add (.reg 7) (.const 1)).eval w s4 = some (dst + 2 + (i + i) + 1) :=
    ev_add (ev_reg (v := dst + 2 + (i + i)) (by simp [s4, s3]) (by omega))
      (ev_const (c := 1) (by omega)) (by omega)
  have ev2 : (Expr.load (.bin .add (.reg 6) (.const 1))).eval w s4 =
      some (J.edges.getD j (0, 0)).2 :=
    ev_load' (ev_add (ev_reg (v := jAddr + 2 + (j + j)) (by simp [s4, s3, s2]) (by omega))
      (ev_const (c := 1) (by omega)) (by omega))
      (by
        simp only [s4, hs3]
        rw [Function.update_of_ne (by omega), show jAddr + 2 + (j + j) + 1 =
          jAddr + (2 + 2 * j) + 1 by omega]
        exact hv)
  refine runs_start_le ?_
  refine runs_seq_assign_le e5 ?_
  refine runs_seq_assign_le e6 ?_
  refine runs_seq_assign_le e7 ?_
  refine runs_seq_store_le ea1 ev1 ?_
  refine runs_store_le ea2 ev2 ⟨⟨by simp [s4, s3, s2, s1, r0], by simp [s4, s3, s2, s1, r1],
    by simp [s4, s3, s2, s1, r2], by simp [s4, s3, s2, s1, r3], by simp, by omega, ?_, ?_, ?_, ?_⟩,
    by simp [s4, s3, s2, s1, r4]⟩ (by simp only [Expr.size]; omega)
  · simp only [s4, hs3]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hn
  · simp only [s4, hs3]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hm
  · simp only [s4, hs3]
    rw [List.take_succ_eq_append_getElem hil, List.map_append, edgeWords_append]
    have hl : (edgeWords ((kept.take i).map fun j => J.edges.getD j (0, 0))).length = 2 * i := by
      rw [edgeWords_length, List.length_map, List.length_take]; omega
    have hpair : edgeWords [J.edges.getD j (0, 0)] =
        [(J.edges.getD j (0, 0)).1, (J.edges.getD j (0, 0)).2] := by simp [edgeWords]
    rw [List.map_singleton, ← hjdef, hpair]
    refine listAt_append_right_pair ?_ ?_ ?_
    · intro t ht
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hlist t ht
    · rw [hl, Function.update_of_ne (by omega), show dst + 2 + 2 * i = dst + 2 + (i + i) by omega,
        Function.update_self]
    · rw [hl, show dst + 2 + 2 * i + 1 = dst + 2 + (i + i) + 1 by omega, Function.update_self]
  · intro x hx
    simp only [s4, hs3]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hout x (by omega)

/-- `subgraphBody` at `f` meets `subgraphContract`. The cost is `60 k + 40`. -/
theorem subgraph_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    (hproc : p.procs[f]? = some subgraphBody) :
    MeetsContract w p f (subgraphContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨jAddr, kAddr, k, dst, J, kept, rfl, hP⟩ := hpre
  have hP' := hP
  obtain ⟨hJ, hK, hlen, hlt, hJd, hKd, hdw, hw1⟩ := hP'
  rw [graph_encode_length] at hJd
  have hkw : k < 2 ^ w := by omega
  have hwd : dst < 2 ^ w := by omega
  let st0 := startState [jAddr, kAddr, k, dst] mem pos
  have r0 : st0.regs 0 = jAddr := by simp [st0, startState]
  have r1 : st0.regs 1 = kAddr := by simp [st0, startState]
  have r2 : st0.regs 2 = k := by simp [st0, startState]
  have r3 : st0.regs 3 = dst := by simp [st0, startState]
  have hm0 : st0.mem = mem := rfl
  let mem1 := Function.update mem dst J.n
  let mem2 := Function.update mem1 (dst + 1) k
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 4) (lo := .const 0) (hi := .reg 2)
    (P := fun st => st.regs 0 = jAddr ∧ st.regs 1 = kAddr ∧ st.regs 2 = k ∧ st.regs 3 = dst ∧
      st.mem = mem2)
    (Inv := SubgraphInv mem jAddr kAddr k dst J kept) 50 0 k (Nat.zero_le _) hw1 (fun _ => hkw)
    (fun st ⟨q0, q1, q2, q3, hm⟩ => ⟨ev_const (by omega),
      ⟨by simp [q0], by simp [q1], by simp [q2], by simp [q3], by simp, Nat.zero_le _,
        by simp [hm, mem2, mem1], by simp [hm, mem2], by simp [edgeWords, listAt_nil],
        fun x hx => by
          simp only [hm, mem2, mem1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]⟩⟩)
    (fun _ _ _ _ h => h.2.2.2.2.1)
    (fun _ _ _ _ h => ev_reg h.2.2.1 hkw)
    (fun i _ hi => subgraph_step hP i hi)
  refine runs_start_le ?_
  refine runs_seq_store_le (ev_reg r3 hwd) (ev_load' (ev_reg r0 (by omega)) (graphAt_n hJ)) ?_
  refine runs_seq_store_le (ev_add (ev_reg r3 hwd) (ev_const (c := 1) (by omega)) (by omega))
    (ev_reg r2 hkw) ?_
  refine runs_seq_triple_le hloop ⟨r0, r1, r2, r3, rfl⟩ ?_
  intro st₁ hI
  obtain ⟨-, -, -, -, -, -, hn, hm, hlist, hout⟩ := hI
  refine runs_ret_le (v := 0) (ev_const (by omega)) (fun jA' kA' k' dst' J' kept' h1 h2 => ?_) ?_
  · simp only [List.cons.injEq, and_true] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    have hJJ : J = J' := graphAt_unique hJ h2.1
    have hkk : kept = kept' := List.ext_getElem (hlen.trans h2.2.2.1.symm) fun t h1 h2' =>
      (hK.getElem h1).symm.trans (h2.2.1.getElem h2')
    subst hJJ hkk
    rw [List.take_of_length_le (by omega)] at hlist
    refine ⟨?_, hout⟩
    show ListAt st₁.mem dst (Graph.encode (subgraphOf J kept))
    simp only [Graph.encode, subgraphOf]
    rw [listAt_cons, listAt_cons]
    refine ⟨hn, ?_, ?_⟩
    · rw [hm]; simp [Graph.m, hlen]
    · exact hlist
  · simp only [Expr.size, subgraphContract, List.getD_cons_succ, List.getD_cons_zero,
      Nat.sub_zero]
    omega

end MinCostFlow.Spanner
