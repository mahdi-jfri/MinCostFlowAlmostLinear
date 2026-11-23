module

public import MinCostFlow.HierPaths.InitProgFlatPassModel
public import MinCostFlow.HierPaths.InitProgFlatStep

/-!
# Substitution through one host embedding

The procedure scans the input edge list and appends one directed embedding
at a time. The loop invariant identifies the current terminal and keeps the
input lists and host unchanged.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Arguments are the host, embedding table, host edge count, input list, input
length, initial terminal and destination. -/
def initFlatPass (edge finish : ℕ) : Stmt :=
  .assign 7 (.reg 5) ;;
  forRange 8 (.const 0) (.reg 4)
    (.assign 9 (.load (.bin .add (.reg 3) (.reg 8))) ;; initFlatStep edge finish) ;;
  .ret (.reg 6)

theorem initFlatPass_noRand (edge finish : ℕ) : (initFlatPass edge finish).NoRand := by
  simp [initFlatPass, forRange, forUp, initFlatStep, Stmt.NoRand]

/-- A pass writes only its substituted edge list. The input data lie before
the destination, and each visited edge and its terminals fit in words. -/
def initFlatPassContract (w : ℕ) (G : Graph) (emb : ℕ → List ℕ) (u : ℕ)
    (es : List ℕ) : Contract where
  pre args mem := ∃ g a src dst, args = [g, a, G.m, src, es.length, u, dst] ∧
    GraphAt mem g G ∧ ListAt mem a (csrList G.m emb) ∧ ListAt mem src es ∧
    g + G.encode.length ≤ dst ∧ a + (csrList G.m emb).length ≤ dst ∧ src + es.length ≤ dst ∧
    dst + (substWalk G.edges emb u es).length < 2 ^ w ∧ 1 < 2 ^ w ∧
    ∀ e ∈ es, e < G.m ∧ (edgeAt G.edges e).1 < 2 ^ w ∧ (edgeAt G.edges e).2 < 2 ^ w
  post args mem v mem' := ∃ g a src dst, args = [g, a, G.m, src, es.length, u, dst] ∧
    v = dst + (substWalk G.edges emb u es).length ∧
    ListAt mem' dst (substWalk G.edges emb u es) ∧
    ∀ y, y < dst ∨ v ≤ y → mem' y = mem y
  cost _ _ := rangeCost (fun i => 30 * (emb es[i]!).length + 190) 0 es.length +
    9 * es.length + 20

private theorem initFlatPass_sum (emb : ℕ → List ℕ) (es : List ℕ) :
    ((List.range es.length).map fun (i : ℕ) => 30 * (emb es[i]!).length + 190).sum =
      30 * (es.map fun e => (emb e).length).sum + 190 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
    change (30 * (emb e).length + 190) +
      ((List.range es.length).map fun (i : ℕ) => 30 * (emb es[i]!).length + 190).sum = _
    rw [ih, List.map_cons, List.sum_cons]
    omega

/-- The cost is linear in the number of edges read and written in one substitution. -/
theorem initFlatPass_cost (w : ℕ) (G : Graph) (emb : ℕ → List ℕ) (u : ℕ)
    (es args : List ℕ) (mem : ℕ → ℕ) :
    (initFlatPassContract w G emb u es).cost args mem =
      30 * (substWalk G.edges emb u es).length + 199 * es.length + 20 := by
  simp only [initFlatPassContract, rangeCost_zero_eq_range, initFlatPass_sum, length_substWalk]
  omega

private theorem initFlatTerminal_lt {w : ℕ} (G : Graph) (u : ℕ) (es : List ℕ)
    (hu : u < 2 ^ w)
    (hends : ∀ e ∈ es, e < G.m ∧ (edgeAt G.edges e).1 < 2 ^ w ∧
      (edgeAt G.edges e).2 < 2 ^ w) :
    ∀ i ≤ es.length, initFlatTerminal G u es i < 2 ^ w := by
  intro i hi
  cases i with
  | zero => exact hu
  | succ i =>
    have hi' : i < es.length := hi
    rw [initFlatTerminal_succ G u es i hi']
    obtain ⟨_, hl, hr⟩ := hends _ (List.getElem_mem hi')
    unfold otherEnd
    split
    · exact hr
    · exact hl

theorem initFlatPass_meetsContract {w f edge finish : ℕ} {p : Program}
    {G : Graph} {emb : ℕ → List ℕ} {u : ℕ} {es : List ℕ}
    (hp : p.procs[f]? = some (initFlatPass edge finish))
    (hEdge : ∀ e t, MeetsContract w p edge (initFlatEdgeContract w G emb e t))
    (hEnd : ∀ e t, MeetsContract w p finish (initFlatEndContract w G e t)) :
    MeetsContract w p f (initFlatPassContract w G emb u es) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨g, a, src, dst, rfl, hG, hEmb, hsrc, hg, ha, hs, hroom, h1, hends⟩ := hpre
  let chunks := initFlatChunk G emb u es
  let cost := fun (i : ℕ) => 30 * (emb es[i]!).length + 190
  let R := fun (i : ℕ) (s : State) => s.regs 0 = g ∧ s.regs 1 = a ∧ s.regs 2 = G.m ∧
    s.regs 3 = src ∧ s.regs 4 = es.length ∧ s.regs 7 = initFlatTerminal G u es i
  have hlen : es.length < 2 ^ w := hw _ (by simp)
  have hu : u < 2 ^ w := hw _ (by simp)
  have hm : G.m < 2 ^ w := hw _ (by simp)
  have heq : initAppendPrefix chunks es.length = substWalk G.edges emb u es :=
    initFlatPass_eq_substWalk G emb u es
  have hloop := initAppendIndexedLoop_triple (w := w) (p := p) (dstReg := 6) (idxReg := 8)
    (hi := .reg 4) (body := .assign 9 (.load (.bin .add (.reg 3) (.reg 8))) ;;
      initFlatStep edge finish) R chunks cost es.length dst mem (by decide) h1 hlen
    (fun s i hr => by simpa [R] using hr)
    (fun _ _ hr => Expr.eval_reg_of_eq hr.2.2.2.2.1) ?_
  · refine runs_start_le ?_
    unfold initFlatPass
    refine runs_seq_assign_le (v := u) (Expr.eval_reg_of_eq rfl) ?_
    refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩ ?_
    intro t ht
    obtain ⟨_, hdst, hwords, hf⟩ := ht
    rw [heq] at hdst hwords hf
    refine runs_ret_le (v := t.regs 6) (Expr.eval_reg_of_eq rfl)
      ⟨g, a, src, dst, rfl, hdst, hwords, fun y hy => hf y (by rwa [hdst] at hy)⟩ ?_
    simp [initFlatPassContract, Expr.size, cost]
    omega
  intro i hi s hr hidx hdst hframe st ω' hst
  subst st
  obtain ⟨r0, r1, r2, r3, r4, r7⟩ := hr
  let e := es[i]
  let cur := initFlatTerminal G u es i
  let out := dst + (initAppendPrefix chunks i).length
  have hnext : initFlatTerminal G u es (i + 1) = otherEnd G.edges e cur :=
    initFlatTerminal_succ G u es i hi
  have hei : e = es[i]! := (getElem!_pos es i hi).symm
  have hchunk : chunks i = initFlatEdgeWords G emb e cur := by simp [chunks, initFlatChunk, ← hei, cur]
  have hout : dst + (initAppendPrefix chunks (i + 1)).length = out + (emb e).length := by
    rw [initAppendPrefix_succ, List.length_append, Nat.add_assoc, initFlatChunk_length, ← hei]
  have hword : out + (emb e).length < 2 ^ w := by
    rw [← hout]
    apply lt_of_le_of_lt (Nat.add_le_add_left (initAppendPrefix_length_mono chunks hi) dst)
    simpa only [heq] using hroom
  have hdout : dst ≤ out := Nat.le_add_right _ _
  have hload : s.mem (src + i) = e := (hframe _ (by omega)).trans (hsrc i hi)
  obtain ⟨he, hl, hrr⟩ := hends e (List.getElem_mem hi)
  have hGw : g + G.encode.length < 2 ^ w := by omega
  have hread : ListAt s.mem a (csrList G.m emb) :=
    listAt_congr (fun k hk => (hframe _ (by omega)).symm) hEmb
  have hGraph (mem' : ℕ → ℕ) (hf : ∀ y < out, mem' y = s.mem y) : GraphAt mem' g G :=
    listAt_congr (fun k hk => ((hf _ (by omega)).trans (hframe _ (by omega))).symm) hG
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := e) (Expr.eval_load_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_reg_of_eq hidx) (by omega)) hload) ?_
  have step := initFlatStep_triple (hEdge e cur) (hEnd e cur) (g := g) (a := a)
    (dst := out) (s := {s with regs := Function.update s.regs 9 e}) ?_
    ⟨g, a, out, rfl, he, hl, hGraph _ (fun _ _ => rfl), hread, hg.trans hdout, ha.trans hdout, hword⟩
    (fun mem' hf => ⟨g, rfl, hGraph mem' hf, he, hGw, hl, hrr⟩)
    (by simpa using r0) (by simpa using r1) (by simpa using r2)
    (by simpa [out] using hdst) (by simpa [cur] using r7) (by simp)
  · obtain ⟨o, t, c, hrun, ht, hc⟩ := step _ ω' rfl
    cases o with
    | returned => exact False.elim ht
    | normal =>
      obtain ⟨hregs, hwrite, hf⟩ := ht
      refine ⟨.normal, t, c, hrun, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp [R, hregs, r0, r1, r2, r3, r4, hnext]
      · simpa [hregs] using hidx
      · simp [hregs, hout]
      · simpa only [hchunk] using hwrite
      · simpa only [hout] using hf
      · change c ≤ 30 * (emb e).length + 180 at hc
        simp only [cost, ← hei, Expr.size]
        omega
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hw _ (by simp)
    · exact hm
    · omega
    · exact initFlatTerminal_lt G u es hu hends i hi.le
    · omega

end MinCostFlow.HierPaths

end
