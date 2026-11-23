module

public import MinCostFlow.LinkCut.PathProg.OpCost
public import MinCostFlow.LinkCut.PathProg.Notes
public import MinCostFlow.LinkCut.PathTree.FindCorrect

/-!
# The cost of find-ready against the model's counts

Find-ready pops the stack entries that fail the test, at a constant cost each, and then descends
from the first valid entry to a ready edge `y` and exposes `y`. The descent visits at most one
node more than the depth of `y`, and the expose of `y` counts at least half that depth. After
the descent, the expose of `y` costs exactly what it costs at the start (`exposeCost_descend`),
since the descent only pushes the nodes that the splay of `y` pushes anyway.

So find-ready costs at most a constant per popped entry, plus `findRate` per unit that
`lctExposeCost` counts for `y` (`findCost_le`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree SplayState

variable {α σ τ : Type*}

theorem splayDepth_congr {s s' : SplayState α σ τ} (h : ∀ z, (s'.nodes z).par = (s.nodes z).par) :
    ∀ k y, splayDepth s' k y = splayDepth s k y
  | 0, _ => rfl
  | k + 1, y => by
    simp only [splayDepth, h y]
    rw [splayDepth_congr h k]

section Generic

variable {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
  {ok : PayloadOk α σ τ}

/-- After the pushes of the splay path of `y`, the expose of `y` costs what it costs before. -/
theorem exposeCost_descend (S : PayloadSteps w p P Lay ok) (st : LctState α σ τ)
    {D : SplayState α σ τ} {y : ℕ}
    (hD : D = pushPath P st.splay (2 * st.n + 1) y)
    (hfix : pushPath P D (2 * st.n + 1) y = D)
    (hsp : splay P D (2 * st.n + 1) y = splay P st.splay (2 * st.n + 1) y) :
    exposeCost S { st with splay := D } y = exposeCost S st y := by
  have hpar : ∀ z, (D.nodes z).par = (st.splay.nodes z).par := fun z => by
    rw [hD, pushPath_eq_pushSeq, par_pushSeq]
  have hstart : exposeStart P { st with splay := D } y = exposeStart P st y := by
    unfold exposeStart; simp only; rw [hsp]
  have hsc : splayCost S D (2 * st.n + 1) y = splayCost S st.splay (2 * st.n + 1) y := by
    unfold splayCost
    rw [splayDepth_congr hpar, hfix, ← hD]
  unfold exposeCost
  simp only
  rw [hsc, hstart]

end Generic

/-- The cost of one counted unit of find-ready. -/
def findRate {w : ℕ} {p : Program} {Lay : NodeLayout (Option PathEdgeValue) PathSummary PathTag}
    {ok : PayloadOk (Option PathEdgeValue) PathSummary PathTag}
    (S : PayloadSteps w p pathPayload Lay ok) (T : ReadyTests w p Lay pathRs pathRv) : ℕ :=
  exposeRate S + 3 * (pushDownCost S + 2 * T.cost + 120) + 3 * T.cost + 1000

/-- Find-ready costs at most `T.cost + 300` per entry it pops, plus `findRate` per unit that the
expose of its answer counts. The bound charges `T.cost + 300` for each entry of the new stack, so
the entries the expose pushes are paid too. When the answer is `0`, the last term only adds
slack. -/
theorem findCost_le {w : ℕ} {p : Program}
    {Lay : NodeLayout (Option PathEdgeValue) PathSummary PathTag}
    {ok : PayloadOk (Option PathEdgeValue) PathSummary PathTag}
    (S : PayloadSteps w p pathPayload Lay ok) (T : ReadyTests w p Lay pathRs pathRv)
    {s : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees free depth) (hF : FreeShape s free) :
    ∀ R : List ℕ, findCost S T s R +
      (T.cost + 300) * (findLoop pathPayload pathRs pathRv s R).2.1.length ≤
      (T.cost + 300) * R.length +
      findRate S T * ((lctExposeCost pathPayload s (findLoop pathPayload pathRs pathRv s R).2.2).2.1 +
        (lctExposeCost pathPayload s (findLoop pathPayload pathRs pathRv s R).2.2).2.2 + 1)
  | [] => by
    have : 50 ≤ findRate S T := by unfold findRate; omega
    simp only [findCost, findLoop, List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact le_trans this (Nat.le_mul_of_pos_right _ (by omega))
  | x :: R => by
    by_cases hv : ValidG pathRs s.n s.splay x
    · have hv' : ValidRoot s x := hv
      obtain ⟨t, ht, rfl⟩ := validRoot_root W hF hv'
      have htinv := W.treesInv t ht
      have hne := W.treesNonEmpty t ht
      have hcnt := tree_count_le W ht
      set D := (descend pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId).1 with hDdef
      set y := (descend pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId).2 with hydef
      have hd : descend pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId = (D, y) := rfl
      obtain ⟨hyt, -, -, hD, hsp, hfix, hsteps⟩ :=
        descend_root pathPayload_laws pathReadyLaw htinv hne hv'.2.2.2.1 (by omega) hd
      have hloop : findLoop pathPayload pathRs pathRv s (t.rootId :: R) =
          (lctExpose pathPayload (descState pathPayload pathRs pathRv s t.rootId) y,
            exposeNotes pathPayload (descState pathPayload pathRs pathRv s t.rootId) y
              (t.rootId :: R).reverse, y) := by
        simp [findLoop, hv, descNode, hydef]
      have hcost : findCost S T s (t.rootId :: R) =
          (descendSteps pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId + 1) *
            (pushDownCost S + 2 * T.cost + 120) +
          exposeCost S { s with splay := D } y + T.cost + 300 := by
        simp only [findCost, ite_eq_left hv]
        rfl
      have hnotes := exposeNotes_length_le pathPayload s y (t.rootId :: R).reverse
      rw [hloop, hcost, exposeCost_descend S s hD hfix hsp]
      dsimp only
      rw [show descState pathPayload pathRs pathRv s t.rootId = { s with splay := D } from rfl,
        exposeNotes_of_splay_eq s hsp]
      rw [List.length_reverse] at hnotes
      generalize (exposeNotes pathPayload s y (t.rootId :: R).reverse).length = m at hnotes ⊢
      have hya : y ∈ trees.flatMap AuxTree.toList := List.mem_flatMap.mpr ⟨t, ht, hyt⟩
      have he := exposeCost_le pathPayload_laws S W hya
      have hh : splayDepth s.splay (2 * s.n + 1) y / 2 ≤ (lctExposeCost pathPayload s y).2.1 := by
        show _ ≤ _ / 2 + _ + _
        omega
      generalize (lctExposeCost pathPayload s y).2.1 = a at he hh ⊢
      generalize (lctExposeCost pathPayload s y).2.2 = b at he hnotes ⊢
      generalize exposeCost S s y = e at he ⊢
      generalize descendSteps pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId = k
        at hsteps ⊢
      generalize splayDepth s.splay (2 * s.n + 1) y = d at hsteps hh
      unfold findRate
      generalize exposeRate S = r at he ⊢
      generalize pushDownCost S + 2 * T.cost + 120 = q
      have hk : k + 1 ≤ 3 * (a + b + 1) := by omega
      have h1 := Nat.mul_le_mul_right q hk
      generalize T.cost = tc at hnotes ⊢
      generalize (t.rootId :: R).length = l at hnotes ⊢
      have h2 : (tc + 300) * m ≤ (tc + 300) * l + (tc + 300) * (2 * b) := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hnotes
      nlinarith
    · have hloop : findLoop pathPayload pathRs pathRv s (x :: R) =
          findLoop pathPayload pathRs pathRv s R := by
        simp [findLoop, hv]
      have hcost : findCost S T s (x :: R) = T.cost + 300 + findCost S T s R := by
        simp only [findCost, ite_eq_right hv]
      rw [hloop, hcost, List.length_cons]
      have ih := findCost_le S T W hF R
      rw [Nat.mul_add, Nat.mul_one]
      omega

end MinCostFlow.LinkCut.PathProg
