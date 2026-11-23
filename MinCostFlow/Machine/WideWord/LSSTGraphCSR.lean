module

public import MinCostFlow.Machine.WideWord.LSSTModel
public import WordRAM.Logic
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# WordRAM graph preprocessing helpers: non-loop scan, star fallback, and vertex index table

This file defines and verifies the small helper procedures in `csrAuxModule` and the shared
graph/memory lemmas used across `LSSTGraphBuildCSR` and `LSSTGraph`:

* `scanNonloops`: extracts `nonloopEdges G` from `tailArr` and `headArr` in `O(m + 1)`.
* `starPairs`: outputs `[(0, 1), ..., (0, n - 1)]` when all edges are loops, in `O(n + 1)`.
* `buildVertIdx`: builds `vIdx[V_list[k]] := k` in `O(n + 1)`.
* `isBridgeVerts_of_bfs_spec`: lifts CSR component-closure invariants to `IsBridgeVerts`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM
open MinCostFlow
open MinCostFlow.LSF

/-! ### Shared list/memory and connectivity helpers -/

lemma listAt_nil' (mem : ℕ → ℕ) (a : ℕ) : ListAt mem a [] := by
  intro i hi; exact absurd hi (Nat.not_lt_zero _)

lemma listAt_snoc' {mem : ℕ → ℕ} {a x : ℕ} {l : List ℕ}
    (h : ListAt mem a l) :
    ListAt (Function.update mem (a + l.length) x) a (l ++ [x]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  by_cases hil : i < l.length
  · rw [Function.update_of_ne (by omega), List.getElem_append_left hil]
    exact h i hil
  · have heq : i = l.length := by omega
    subst heq
    rw [Function.update_self, List.getElem_append_right (le_refl _)]
    simp

lemma mem_ofFn_eq {f : ℕ → ℕ} {mem : ℕ → ℕ} {a n i : ℕ}
    (h : ListAt mem a (List.ofFn fun j : Fin n => f j)) (hi : i < n) :
    mem (a + i) = f i := by
  have h1 := h i (by simp [hi])
  rwa [List.getElem_ofFn] at h1

lemma listAt_congr' {mem₁ mem₂ : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (hc : ∀ i, i < l.length → mem₁ (a + i) = mem₂ (a + i))
    (h : ListAt mem₁ a l) : ListAt mem₂ a l := fun i hi => by
  rw [← hc i hi]; exact h i hi

lemma listAt_pairs_snoc {mem : ℕ → ℕ} {a u v : ℕ} {l : List (ℕ × ℕ)}
    (h : ListAt mem a (l.flatMap fun p => [p.1, p.2])) :
    ListAt (Function.update (Function.update mem (a + 2 * l.length) u) (a + 2 * l.length + 1) v)
      a ((l ++ [(u, v)]).flatMap fun p => [p.1, p.2]) := by
  have hlen : (l.flatMap fun p => [p.1, p.2]).length = 2 * l.length := by
    clear h
    induction l with
    | nil => simp
    | cons _ _ ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; omega
  rw [List.flatMap_append, List.flatMap_singleton]
  have h1 := listAt_snoc' (x := u) h
  rw [hlen] at h1
  have h2 := listAt_snoc' (x := v) h1
  simpa [List.length_append, hlen, Nat.add_assoc] using h2

private lemma gvWalk_of_nlWalk {G : IndexedGraph} {v : ℕ → ℝ} {G_nl G_v : MGraph}
    (hG_nl : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v : G_v = weightedCopyGraph G_nl v) (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hv : ∀ e < G.m, 0 < v e) :
    ∀ {x y : ℕ} {Q : List (ℕ × Bool)}, G_nl.IsWalk x y Q → G_v.Connected x y
  | x, _, [], .nil _ => ⟨[], .nil x⟩
  | x, _, (e, dir) :: rest, .cons heE hsrc hrest => by
    have hnl_ne' : G_nl.E.Nonempty := hG_nl ▸ hnl_ne
    have hnl_E : G_nl.E = (nonloopEdges G).toFinset := by rw [hG_nl]
    obtain ⟨Q', hQ'⟩ := gvWalk_of_nlWalk hG_nl hG_v hnl_ne hv hrest
    have hv_nl : ∀ f ∈ G_nl.E, 0 < v f := fun f hf =>
      hv f (mem_nonloopEdges_iff.mp (List.mem_toFinset.mp (hnl_E ▸ hf))).1
    have hmult := edgeMult_pos hnl_ne' hv_nl heE
    let e' := copyId (copyMod G_nl) e 0
    have he'_mem : e' ∈ G_v.E := by
      rw [hG_v, weightedCopyGraph, ite_eq_left hnl_ne']
      exact Finset.mem_biUnion.mpr ⟨e, heE, Finset.mem_image_of_mem _ (Finset.mem_range.mpr hmult)⟩
    have htail : G_v.tail e' = G_nl.tail e := by
      rw [hG_v, weightedCopyGraph, ite_eq_left hnl_ne']; dsimp only; rw [origEdge_copyId heE]
    have hhead : G_v.head e' = G_nl.head e := by
      rw [hG_v, weightedCopyGraph, ite_eq_left hnl_ne']; dsimp only; rw [origEdge_copyId heE]
    refine ⟨(e', dir) :: Q', .cons he'_mem ?_ ?_⟩
    · cases dir <;> simp [MGraph.src, htail, hhead] at hsrc ⊢ <;> exact hsrc
    · cases dir <;> simp [MGraph.dst, htail, hhead] at hQ' ⊢ <;> exact hQ'

private lemma nlWalk_of_gvWalk {v : ℕ → ℝ} {G_nl G_v : MGraph}
    (hG_v : G_v = weightedCopyGraph G_nl v) (hnl_ne' : G_nl.E.Nonempty) :
    ∀ {x y : ℕ} {Q : List (ℕ × Bool)}, G_v.IsWalk x y Q → G_nl.Connected x y
  | x, _, [], .nil _ => ⟨[], .nil x⟩
  | x, _, (e', dir) :: rest, .cons heE hsrc hrest => by
    obtain ⟨Q', hQ'⟩ := nlWalk_of_gvWalk hG_v hnl_ne' hrest
    have hm := weightedCopyGraph_origEdge_mem hnl_ne' (hG_v ▸ heE)
    have htail : G_v.tail e' = G_nl.tail (origEdge (copyMod G_nl) e') := by rw [hG_v]; exact hm.2.1
    have hhead : G_v.head e' = G_nl.head (origEdge (copyMod G_nl) e') := by rw [hG_v]; exact hm.2.2
    refine ⟨(origEdge (copyMod G_nl) e', dir) :: Q', .cons hm.1 ?_ ?_⟩
    · cases dir <;> simp [MGraph.src, htail, hhead] at hsrc ⊢ <;> exact hsrc
    · cases dir <;> simp [MGraph.dst, htail, hhead] at hQ' ⊢ <;> exact hQ'

lemma nonloopConnected_iff_gvConnected {G : IndexedGraph} {v : ℕ → ℝ}
    {G_nl G_v : MGraph} (hG_nl : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v : G_v = weightedCopyGraph G_nl v) (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hv : ∀ e < G.m, 0 < v e) {a b : ℕ} :
    G_nl.Connected a b ↔ G_v.Connected a b :=
  ⟨fun ⟨_, h⟩ => gvWalk_of_nlWalk hG_nl hG_v hnl_ne hv h,
   fun ⟨_, h⟩ => nlWalk_of_gvWalk hG_v (hG_nl ▸ hnl_ne) h⟩

private lemma gvbWalk_of_nlWalk {G : IndexedGraph} {v : ℕ → ℝ} {V_act : Finset ℕ}
    {G_nl G_v : MGraph} {r₀ : ℕ} {B : List ℕ}
    (hG_nl : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v : G_v = weightedCopyGraph G_nl v) (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hv : ∀ e < G.m, 0 < v e) :
    ∀ {x y : ℕ} {Q : List (ℕ × Bool)}, G_nl.IsWalk x y Q → (gvWithBridges G_v V_act r₀ B).Connected x y
  | x, _, [], .nil _ => ⟨[], .nil x⟩
  | x, _, (e, dir) :: rest, .cons heE hsrc hrest => by
    have hnl_ne' : G_nl.E.Nonempty := hG_nl ▸ hnl_ne
    have hnl_E : G_nl.E = (nonloopEdges G).toFinset := by rw [hG_nl]
    obtain ⟨Q', hQ'⟩ := gvbWalk_of_nlWalk hG_nl hG_v hnl_ne hv hrest
    have hv_nl : ∀ f ∈ G_nl.E, 0 < v f := fun f hf =>
      hv f (mem_nonloopEdges_iff.mp (List.mem_toFinset.mp (hnl_E ▸ hf))).1
    have hmult := edgeMult_pos hnl_ne' hv_nl heE
    let e' := copyId (copyMod G_nl) e 0
    have he'_gv : e' ∈ G_v.E := by
      rw [hG_v, weightedCopyGraph, ite_eq_left hnl_ne']
      exact Finset.mem_biUnion.mpr ⟨e, heE, Finset.mem_image_of_mem _ (Finset.mem_range.mpr hmult)⟩
    have he'_mem : e' ∈ (gvWithBridges G_v V_act r₀ B).E := Finset.mem_union_left _ he'_gv
    have htail : (gvWithBridges G_v V_act r₀ B).tail e' = G_nl.tail e := by
      dsimp only [gvWithBridges]; rw [ite_eq_left he'_gv, hG_v, weightedCopyGraph, ite_eq_left hnl_ne']
      dsimp only; rw [origEdge_copyId heE]
    have hhead : (gvWithBridges G_v V_act r₀ B).head e' = G_nl.head e := by
      dsimp only [gvWithBridges]; rw [ite_eq_left he'_gv, hG_v, weightedCopyGraph, ite_eq_left hnl_ne']
      dsimp only; rw [origEdge_copyId heE]
    refine ⟨(e', dir) :: Q', .cons he'_mem ?_ ?_⟩
    · cases dir <;> simp [MGraph.src, htail, hhead] at hsrc ⊢ <;> exact hsrc
    · cases dir <;> simp [MGraph.dst, htail, hhead] at hQ' ⊢ <;> exact hQ'

theorem isBridgeVerts_of_bfs_spec {G : IndexedGraph} {v : ℕ → ℝ} {V_act : Finset ℕ}
    {G_nl G_v : MGraph} {r₀ : ℕ} {B : List ℕ}
    (hG_nl : G_nl = { G.toMGraph with E := (nonloopEdges G).toFinset })
    (hG_v : G_v = weightedCopyGraph G_nl v)
    (hnl_ne : (nonloopEdges G).toFinset.Nonempty)
    (hv : ∀ e < G.m, 0 < v e)
    (hB_nd : B.Nodup) (hB_act : ∀ b ∈ B, b ∈ V_act) (hr₀_nB : r₀ ∉ B)
    (hReach : ∀ x ∈ V_act, ∃ c ∈ r₀ :: B, G_nl.Connected c x)
    (hDisj : ∀ a ∈ r₀ :: B, ∀ b ∈ r₀ :: B, a ≠ b → ¬ G_nl.Connected a b) :
    IsBridgeVerts G_v V_act r₀ B := by
  refine ⟨hB_nd, hB_act, hr₀_nB, ?_, ?_⟩
  · intro x hx _
    obtain ⟨c, hc, ⟨P, hP⟩⟩ := hReach x hx
    have hcx_H : (gvWithBridges G_v V_act r₀ B).Connected c x :=
      gvbWalk_of_nlWalk hG_nl hG_v hnl_ne hv hP
    rcases List.mem_cons.mp hc with rfl | hcB
    · exact hcx_H
    · have hbr : (gvWithBridges G_v V_act r₀ B).Connected r₀ c := by
        let f := copyMod G_v + c
        have hfE : f ∈ (gvWithBridges G_v V_act r₀ B).E :=
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hcB, rfl⟩)
        have hfGv : f ∉ G_v.E := fun h =>
          Nat.not_lt_of_ge (Nat.le_add_right (copyMod G_v) c) (lt_copyMod h)
        have htail : (gvWithBridges G_v V_act r₀ B).tail f = r₀ := by
          dsimp [gvWithBridges]; exact ite_eq_right hfGv
        have hhead : (gvWithBridges G_v V_act r₀ B).head f = c := by
          dsimp [gvWithBridges]; rw [ite_eq_right hfGv]; dsimp [f]; omega
        exact ⟨[(f, true)], .cons hfE (by simp [MGraph.src, htail])
          (by simpa [MGraph.dst, hhead] using .nil c)⟩
      exact connected_trans hbr hcx_H
  · intro a ha b hb hne hab
    exact hDisj a ha b hb hne ((nonloopConnected_iff_gvConnected hG_nl hG_v hnl_ne hv).mpr hab)

/-! ### Helper endpoint-counting lemmas -/

def nlEndpoints (G : IndexedGraph) (es : List ℕ) : List ℕ :=
  es.flatMap fun e => [G.tail e, G.head e]

lemma nlEndpoints_count_le {G : IndexedGraph} {i u : ℕ} :
    (nlEndpoints G ((nonloopEdges G).take i)).count u ≤
      (nlEndpoints G (nonloopEdges G)).count u := by
  have htake : (nonloopEdges G).take i ++ (nonloopEdges G).drop i = nonloopEdges G :=
    List.take_append_drop i _
  conv_rhs => rw [← htake]
  simp only [nlEndpoints, List.flatMap_append, List.count_append]
  omega

lemma nlEndpoints_sum_count {G : IndexedGraph} {n : ℕ}
    (hsub : ∀ x ∈ nlEndpoints G (nonloopEdges G), x < n) :
    ∑ u ∈ Finset.range n, (nlEndpoints G (nonloopEdges G)).count u = 2 * (nonloopEdges G).length := by
  have key : ∀ l : List ℕ, (∀ x ∈ l, x < n) →
      ∑ u ∈ Finset.range n, l.count u = l.length := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a as ih =>
      intro ha
      have han : a < n := ha a List.mem_cons_self
      have has := ih fun x hx => ha x (List.mem_cons_of_mem _ hx)
      have hcons : ∀ u, (a :: as).count u = as.count u + (if u = a then 1 else 0) := by
        intro u
        rw [List.count_cons]
        by_cases hua : a = u
        · simp [hua]
        · have hua' : u ≠ a := Ne.symm hua
          simp [hua, hua']
      simp_rw [hcons, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp [han, has]
  have hlen : ∀ es : List ℕ, (nlEndpoints G es).length = 2 * es.length := fun es => by
    induction es with
    | nil => simp [nlEndpoints]
    | cons _ _ ih =>
      simp only [nlEndpoints, List.flatMap_cons, List.length_cons, List.length_nil,
        List.length_append] at ih ⊢; omega
  rw [← hlen (nonloopEdges G)]
  exact key _ hsub

lemma nlEndpoints_pos_iff {G : IndexedGraph} {u : ℕ} :
    0 < (nlEndpoints G (nonloopEdges G)).count u ↔
      ∃ e ∈ nonloopEdges G, G.tail e = u ∨ G.head e = u := by
  rw [List.count_pos_iff]
  simp [nlEndpoints, eq_comm]

/-! ### Procedures and indices -/

def idxScanNonloops : ℕ := 0
def idxStarPairs : ℕ := 1
def idxBuildVertIdx : ℕ := 2

/-- Extract non-loop edge indices `e < m` (`tail[e] ≠ head[e]`) into `outArr`.
Args: `[m, tailArr, headArr, outArr]`. Returns `nlCnt`. -/
def scanNonloops : Stmt :=
  .assign 4 (.const 0) ;;
  WordRAM.forRange 5 (.const 0) (.reg 0) (
    .assign 6 (.load (.bin .add (.reg 1) (.reg 5))) ;;
    .assign 7 (.load (.bin .add (.reg 2) (.reg 5))) ;;
    .cond (.bin .eq (.reg 6) (.reg 7))
      .nop
      (.store (.bin .add (.reg 3) (.reg 4)) (.reg 5) ;;
       .assign 4 (.bin .add (.reg 4) (.const 1)))
  ) ;;
  .ret (.reg 4)

/-- Build star edge pairs `[(0, 1), ..., (0, n - 1)]` when all graph edges are self-loops.
Args: `[n, outPairs]`. Returns `n - 1`. -/
def starPairs : Stmt :=
  .cond (.bin .lt (.const 1) (.reg 0))
    (.assign 2 (.bin .sub (.reg 0) (.const 1)) ;;
     WordRAM.forRange 3 (.const 0) (.reg 2) (
       .store (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 3))) (.const 0) ;;
       .store (.bin .add (.reg 1) (.bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1)))
         (.bin .add (.reg 3) (.const 1))
     ) ;;
     .ret (.reg 2))
    (.ret (.const 0))

/-- Populate vertex index lookup table `vIdx[V_list[k]] := k` for `k < vLen`.
Args: `[vLen, vListPtr, vIdxPtr]`. Returns `0`. -/
def buildVertIdx : Stmt :=
  WordRAM.forRange 3 (.const 0) (.reg 0) (
    .store (.bin .add (.reg 2) (.load (.bin .add (.reg 1) (.reg 3)))) (.reg 3)
  ) ;;
  .ret (.const 0)

def csrAuxModule : List Stmt := [scanNonloops, starPairs, buildVertIdx]

theorem csrAuxModule_noRand : ∀ s ∈ csrAuxModule, s.NoRand := by
  intro s hs
  simp only [csrAuxModule, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;>
    simp [scanNonloops, starPairs, buildVertIdx, Stmt.NoRand, WordRAM.forRange, WordRAM.forUp]

/-! ### `scanNonloops` contract -/

def scanNonloopsCost (m : ℕ) : ℕ := m * 55 + 25

def scanNonloopsContract (G : IndexedGraph) (w : ℕ) : Contract where
  pre args mem := ∃ tailArr headArr outArr,
    args = [G.m, tailArr, headArr, outArr] ∧ 16 ≤ 2 ^ w ∧
    tailArr + G.m < 2 ^ w ∧ headArr + G.m < 2 ^ w ∧ outArr + G.m < 2 ^ w ∧
    (outArr + G.m ≤ tailArr ∨ tailArr + G.m ≤ outArr) ∧
    (outArr + G.m ≤ headArr ∨ headArr + G.m ≤ outArr) ∧
    ListAt mem tailArr (List.ofFn fun i : Fin G.m => G.tail i) ∧
    ListAt mem headArr (List.ofFn fun i : Fin G.m => G.head i)
  post args mem ret mem' := ∃ tailArr headArr outArr,
    args = [G.m, tailArr, headArr, outArr] ∧
    ret = (nonloopEdges G).length ∧
    ListAt mem' outArr (nonloopEdges G) ∧
    (∀ a, a < outArr ∨ outArr + G.m ≤ a → mem' a = mem a)
  cost _ _ := scanNonloopsCost G.m

lemma filter_range_succ_lt {n : ℕ} (p : ℕ → Bool) :
    (List.range (n + 1)).filter p =
      (List.range n).filter p ++ (if p n then [n] else []) := by
  rw [List.range_succ, List.filter_append]
  cases hp : p n <;> simp [hp]

theorem scanNonloops_meetsContract {G : IndexedGraph} {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b csrAuxModule) :
    MeetsContract w p (b + idxScanNonloops) (scanNonloopsContract G w) := by
  have hproc : p.procs[b + idxScanNonloops]? = some scanNonloops := hp 0 (by simp [csrAuxModule])
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨tailArr, headArr, outArr, rfl, hw16, htw, hhw, how, hdt, hdh, htm, hhm⟩
  have hm_w : G.m < 2 ^ w := hwords G.m (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  let stepInv : ℕ → State → Prop := fun i st =>
    st.regs 0 = G.m ∧ st.regs 1 = tailArr ∧ st.regs 2 = headArr ∧ st.regs 3 = outArr ∧
    st.regs 5 = i ∧ st.regs 4 = ((List.range i).filter (fun e => G.tail e != G.head e)).length ∧
    ListAt st.mem outArr ((List.range i).filter (fun e => G.tail e != G.head e)) ∧
    (∀ a, a < outArr ∨ outArr + G.m ≤ a → st.mem a = mem a)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 0)
    (body :=
      .assign 6 (.load (.bin .add (.reg 1) (.reg 5))) ;;
      .assign 7 (.load (.bin .add (.reg 2) (.reg 5))) ;;
      .cond (.bin .eq (.reg 6) (.reg 7))
        .nop
        (.store (.bin .add (.reg 3) (.reg 4)) (.reg 5) ;;
         .assign 4 (.bin .add (.reg 4) (.const 1))))
    (P := fun st => st.regs 0 = G.m ∧ st.regs 1 = tailArr ∧ st.regs 2 = headArr ∧
      st.regs 3 = outArr ∧ st.regs 4 = 0 ∧ st.mem = mem)
    (Inv := stepInv)
    42 0 G.m (Nat.zero_le G.m) hw1 (fun _ => hm_w)
    (fun st ⟨h0, h1, h2, h3, h4, hmem⟩ =>
      ⟨by eval_expr, h0, h1, h2, h3, by simp, by simp [h4], by rw [hmem]; exact listAt_nil' _ _,
        fun _ _ => by simp [hmem]⟩)
    (fun _ st _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by have h0 := hi.1; eval_expr)
    (fun i _ hi => by
      intro st _ ⟨h0, h1, h2, h3, h5, h4, hlist, hframe⟩
      set pref := (List.range i).filter (fun e => G.tail e != G.head e)
      have hpref_len : pref.length ≤ i := (List.length_filter_le _ _).trans (by simp)
      have hti : st.mem (tailArr + i) = G.tail i := by
        rw [hframe (tailArr + i) (by rcases hdt with h | h <;> omega)]
        exact mem_ofFn_eq htm hi
      have hhi : st.mem (headArr + i) = G.head i := by
        rw [hframe (headArr + i) (by rcases hdh with h | h <;> omega)]
        exact mem_ofFn_eq hhm hi
      refine runs_start_le ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq h1) (Expr.eval_reg_of_eq h5) (by omega)) hti) ?_
      refine runs_seq_assign_le (Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h2] : _ = headArr))
          (Expr.eval_reg_of_eq (by simp [h5] : _ = i)) (by omega)) (by simpa using hhi)) ?_
      refine runs_cond_le (Expr.eval_eq_op
        (Expr.eval_reg_of_eq (by simp : _ = G.tail i))
        (Expr.eval_reg_of_eq (by simp : _ = G.head i))
        (by omega)) ?_ ?_
      · intro hcond
        have hti_eq : G.tail i = G.head i := by
          by_contra hne; exact hcond (by simp [hne])
        have hpref' : (List.range (i + 1)).filter (fun e => G.tail e != G.head e) = pref := by
          rw [filter_range_succ_lt]; simp [hti_eq, pref]
        refine runs_nop_le ?_ ?_
        · dsimp only
          refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hframe⟩, by simp [h5]⟩
          all_goals try (simp [h0, h1, h2, h3, h4]; done)
          · simp [h4, hpref']
          · simpa [hpref'] using hlist
        · wram_cost
      · intro hcond
        have hti_ne : G.tail i ≠ G.head i := by
          intro heq; simp [heq] at hcond
        have hpref' : (List.range (i + 1)).filter (fun e => G.tail e != G.head e) = pref ++ [i] := by
          rw [filter_range_succ_lt]; simp [hti_ne, pref]
        refine runs_seq_store_le
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h3] : _ = outArr))
            (Expr.eval_reg_of_eq (by simp [h4] : _ = pref.length)) (by omega))
          (Expr.eval_reg_of_eq (by simp [h5] : _ = i)) ?_
        refine runs_assign_le
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [h4] : _ = pref.length))
            (Expr.eval_const (by omega)) (by omega)) ?_ ?_
        · dsimp only
          refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [h5]⟩
          all_goals try (simp [h0, h1, h2, h3]; done)
          · simp [hpref']
          · rw [hpref']; exact listAt_snoc' hlist
          · intro a ha
            dsimp only
            rw [Function.update_of_ne (show a ≠ outArr + pref.length by omega)]
            exact hframe a ha
        · wram_cost)
  refine runs_start_le ?_
  dsimp only [scanNonloops]
  wram_step
  have hloop' := hloop.conseq
    (fun st (h : st.regs 0 = G.m ∧ st.regs 1 = tailArr ∧ st.regs 2 = headArr ∧
        st.regs 3 = outArr ∧ st.regs 4 = 0 ∧ st.mem = mem) => h)
    (fun _ _ h => h) (fun _ _ => le_refl _)
  refine runs_seq_triple_le hloop' (by simp [startState]) ?_
  · intro st₁ ⟨_, _, _, _, _, h4, hlist, hframe⟩
    refine runs_ret_le (by eval_expr) ⟨tailArr, headArr, outArr, rfl, h4, hlist, hframe⟩ ?_
    simp only [scanNonloopsContract, scanNonloopsCost, Expr.size_const, Expr.size_reg,
      Nat.sub_zero]
    omega

/-! ### `starPairs` contract -/

def starPairsCost (n : ℕ) : ℕ := n * 40 + 25

def starPairsContract (w : ℕ) : Contract where
  pre args _ := ∃ n outPairs, args = [n, outPairs] ∧ 16 ≤ 2 ^ w ∧
    outPairs + 2 * (n - 1) < 2 ^ w
  post args mem ret mem' := ∃ n outPairs, args = [n, outPairs] ∧
    ret = n - 1 ∧
    ListAt mem' outPairs (((List.range (n - 1)).map fun i => (0, i + 1)).flatMap fun p => [p.1, p.2]) ∧
    (∀ a, a < outPairs ∨ outPairs + 2 * (n - 1) ≤ a → mem' a = mem a)
  cost args _ := starPairsCost (args.getD 0 0)

theorem starPairs_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b csrAuxModule) :
    MeetsContract w p (b + idxStarPairs) (starPairsContract w) := by
  have hproc : p.procs[b + idxStarPairs]? = some starPairs := hp 1 (by simp [csrAuxModule])
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨n, outPairs, rfl, hw16, hop_w⟩
  have hn_w : n < 2 ^ w := hwords n (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [starPairs]
  wram_step
  · have hn1 : 1 < n := by omega
    have hlim_w : n - 1 < 2 ^ w := by omega
    let stepInv : ℕ → State → Prop := fun i st =>
      st.regs 0 = n ∧ st.regs 1 = outPairs ∧ st.regs 2 = n - 1 ∧ st.regs 3 = i ∧
      ListAt st.mem outPairs (((List.range i).map fun k => (0, k + 1)).flatMap fun p => [p.1, p.2]) ∧
      (∀ a, a < outPairs ∨ outPairs + 2 * (n - 1) ≤ a → st.mem a = mem a)
    have hloop := Triple.forRange_const (w := w) (p := p) (r := 3) (lo := .const 0) (hi := .reg 2)
      (body :=
        .store (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 3))) (.const 0) ;;
        .store (.bin .add (.reg 1) (.bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1)))
          (.bin .add (.reg 3) (.const 1)))
      (P := fun st => st.regs 0 = n ∧ st.regs 1 = outPairs ∧ st.regs 2 = n - 1 ∧ st.mem = mem)
      (Inv := stepInv)
      28 0 (n - 1) (Nat.zero_le _) hw1 (fun _ => hlim_w)
      (fun st ⟨h0, h1, h2, hmem⟩ =>
        ⟨by eval_expr, h0, h1, h2, by simp, by simp [hmem],
          fun _ _ => by simp [hmem]⟩)
      (fun _ st _ _ hi => hi.2.2.2.1)
      (fun _ st _ _ hi => by have h2 := hi.2.2.1; eval_expr)
      (fun i _ hi => by
        intro st _ ⟨h0, h1, h2, h3, hlist, hframe⟩
        refine runs_start_le ?_
        refine runs_seq_store_le
          (Expr.eval_add (Expr.eval_reg_of_eq h1)
            (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h3) (by omega)) (by omega))
          (Expr.eval_const (by omega)) ?_
        refine runs_store_le
          (Expr.eval_add (Expr.eval_reg_of_eq h1)
            (Expr.eval_add (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq h3) (by omega))
              (Expr.eval_const (by omega)) (by omega)) (by omega))
          (Expr.eval_add (Expr.eval_reg_of_eq h3) (Expr.eval_const (by omega)) (by omega)) ?_ ?_
        · dsimp only
          refine ⟨⟨h0, h1, h2, by simp, ?_, ?_⟩, h3⟩
          · rw [List.range_succ, List.map_append, List.map_singleton]
            have h1' := listAt_pairs_snoc (u := 0) (v := i + 1) hlist
            simpa [List.length_map, List.length_range, Nat.add_assoc] using h1'
          · intro a ha
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hframe a ha
        · wram_cost)
    wram_step
    have hloop' := hloop.conseq
      (fun st (h : st.regs 0 = n ∧ st.regs 1 = outPairs ∧ st.regs 2 = n - 1 ∧ st.mem = mem) => h)
      (fun _ _ h => h) (fun _ _ => le_refl _)
    refine runs_seq_triple_le hloop'
      (by simp [startState]) ?_
    · intro st₁ ⟨_, _, h2, _, hlist, hframe⟩
      refine runs_ret_le (by eval_expr) ⟨n, outPairs, rfl, rfl, hlist, hframe⟩ ?_
      simp only [starPairsContract, starPairsCost, List.getD_cons_zero, Expr.size_bin,
        Expr.size_const, Expr.size_reg, Nat.sub_zero]
      omega
  · have hn_le1 : n ≤ 1 := by omega
    refine runs_ret_le (by eval_expr) ⟨n, outPairs, rfl, by simp [Outcome.value]; omega, ?_, fun _ _ => rfl⟩ ?_
    · have : n - 1 = 0 := by omega
      rw [this]; simp
    · simp only [starPairsContract, starPairsCost, List.getD_cons_zero, Expr.size_bin,
        Expr.size_const, Expr.size_reg]
      omega

/-! ### `buildVertIdx` contract and verification -/

def buildVertIdxCost (n : ℕ) : ℕ := n * 25 + 15

def buildVertIdxContract (n : ℕ) (V_list : List ℕ) (w : ℕ) : Contract where
  pre args mem := ∃ vListPtr vIdxPtr,
    args = [V_list.length, vListPtr, vIdxPtr] ∧ 16 ≤ 2 ^ w ∧
    V_list.Nodup ∧ (∀ x ∈ V_list, x < n) ∧
    vListPtr + V_list.length ≤ vIdxPtr ∧ vIdxPtr + n < 2 ^ w ∧
    ListAt mem vListPtr V_list
  post args mem _ mem' := ∃ vListPtr vIdxPtr,
    args = [V_list.length, vListPtr, vIdxPtr] ∧
    (∀ k (hk : k < V_list.length), mem' (vIdxPtr + V_list[k]) = k) ∧
    (∀ u ∈ V_list, mem' (vIdxPtr + u) = V_list.idxOf u) ∧
    (∀ a, a < vIdxPtr ∨ vIdxPtr + n ≤ a → mem' a = mem a)
  cost _ _ := buildVertIdxCost n

theorem buildVertIdx_meetsContract {n : ℕ} {V_list : List ℕ} {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b csrAuxModule) :
    MeetsContract w p (b + idxBuildVertIdx) (buildVertIdxContract n V_list w) := by
  have hproc : p.procs[b + idxBuildVertIdx]? = some buildVertIdx := hp 2 (by simp [csrAuxModule])
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨vListPtr, vIdxPtr, rfl, hw16, hnd, hbnd, hdisj, hv_w, hvm⟩
  have hlen_w : V_list.length < 2 ^ w := hwords V_list.length (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  let stepInv : ℕ → State → Prop := fun k st =>
    st.regs 0 = V_list.length ∧ st.regs 1 = vListPtr ∧ st.regs 2 = vIdxPtr ∧ st.regs 3 = k ∧
    (∀ j, j < k → ∀ hjn : j < V_list.length, st.mem (vIdxPtr + V_list[j]'hjn) = j) ∧
    (∀ a, a < vIdxPtr ∨ vIdxPtr + n ≤ a → st.mem a = mem a)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 3) (lo := .const 0) (hi := .reg 0)
    (body := .store (.bin .add (.reg 2) (.load (.bin .add (.reg 1) (.reg 3)))) (.reg 3))
    (P := fun st => st = startState [V_list.length, vListPtr, vIdxPtr] mem pos)
    (Inv := stepInv)
    15 0 V_list.length (Nat.zero_le _) hw1 (fun _ => hlen_w)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ?_, ?_, ?_, by simp, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ _ => rfl⟩ <;> simp [startState])
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by have h0 := hi.1; eval_expr)
    (fun k _ hk => by
      intro st _ ⟨h0, h1, h2, h3, hset, hfr⟩
      have hvk_mem : st.mem (vListPtr + k) = V_list[k]'hk := by
        rw [hfr _ (by omega)]; exact hvm k hk
      have hvk_lt : V_list[k]'hk < n := hbnd _ (List.getElem_mem hk)
      refine runs_start_le ?_
      refine runs_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq h2)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h1) (Expr.eval_reg_of_eq h3) (by omega)) hvk_mem)
          (by omega))
        (Expr.eval_reg_of_eq h3) ?_ ?_
      · refine ⟨⟨h0, h1, h2, by simp, ?_, ?_⟩, h3⟩
        · intro j hj hjn
          by_cases hjk : j = k
          · subst hjk; simp [Function.update_self]
          · simp only [Function.update_apply]
            rw [ite_eq_right (by
              intro heq
              exact hjk ((List.Nodup.getElem_inj_iff hnd).mp (by omega : V_list[j]'hjn = V_list[k]'hk)))]
            exact hset j (by omega) hjn
        · intro a ha
          simp only [Function.update_apply]
          rw [ite_eq_right (by omega)]
          exact hfr a ha
      · wram_cost)
  refine runs_start_le ?_
  dsimp only [buildVertIdx]
  refine runs_seq_triple_le hloop rfl ?_
  · intro st₁ ⟨_, _, _, _, hset, hfr⟩
    have hset' : ∀ k (hk : k < V_list.length), st₁.mem (vIdxPtr + V_list[k]) = k := fun k hk =>
      hset k hk hk
    have hidx : ∀ u ∈ V_list, st₁.mem (vIdxPtr + u) = V_list.idxOf u := by
      intro u hu
      have hk := List.idxOf_lt_length_of_mem hu
      have hget := List.getElem_idxOf hk
      have h1 := hset' (V_list.idxOf u) hk
      rwa [hget] at h1
    refine runs_ret_le (by eval_expr) ⟨vListPtr, vIdxPtr, rfl, hset', hidx, hfr⟩ ?_
    simp only [buildVertIdxContract, buildVertIdxCost, Expr.size_const, Expr.size_reg, Nat.sub_zero]
    have : V_list.length ≤ n := by
      calc V_list.length = V_list.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
        _ ≤ (Finset.range n).card := Finset.card_le_card fun x hx =>
            Finset.mem_range.mpr (hbnd x (List.mem_toFinset.mp hx))
        _ = n := Finset.card_range n
    omega

end MinCostFlow.WideWord
