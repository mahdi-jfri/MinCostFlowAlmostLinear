module

public import MinCostFlow.LinkCut.PathProg.FindNum
public import MinCostFlow.LinkCut.PathTree.FindCorrect
public import MinCostFlow.MinRatio.PathSplayNumericBounds
public import MinCostFlow.LinkCut.SplayQuery
public import MinCostFlow.LinkCut.PathProg.OpCost
public import MinCostFlow.LinkCut.PathProg.FindCost

/-!
# Paying for an operation

The contract charges each operation `pathTreeBudget C L n` word operations, amortized against
the potential `pathPhi`. This file has the pieces that the final proof uses to pay.

* The potentials of the model depend only on the shape of the state: its pointers, its flip
  bits and its free list (`potentials_shape`). A point write changes only a value and a sum, so
  it has the potentials of the expose before it (`write_potentials`).
* Two witnesses of the invariant have the same active nodes (`active_mem`), because the free
  list is fixed by the state. So a node that is active for the contract is active in the
  witness that the representation keeps (`active_of`).
* When find-ready finds nothing, it pays only for the entries it pops (`findCost_zero`).
* An operation whose cost and stack growth are paid at some rate per counted unit, with the
  model's potential bounds, meets its budget (`pay`).
* The constant `pathC` and the allocation `pathAlloc`, with the bound of the rates by
  `pathC * (L + 1) ^ 2` (`unit_le`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.Path

section Shape

variable {α σ τ : Type*}

/-- Two states with the same shape: the same size, free head, pointers and flip bits. -/
structure SameShape (s s' : LctState α σ τ) : Prop where
  n : s'.n = s.n
  fh : s'.freeHead = s.freeHead
  left : ∀ z, (s'.splay.nodes z).left = (s.splay.nodes z).left
  right : ∀ z, (s'.splay.nodes z).right = (s.splay.nodes z).right
  par : ∀ z, (s'.splay.nodes z).par = (s.splay.nodes z).par
  ppar : ∀ z, (s'.splay.nodes z).ppar = (s.splay.nodes z).ppar
  rev : ∀ z, (s'.splay.nodes z).rev = (s.splay.nodes z).rev

theorem treeIds_shape (P : LctPayload α σ τ) {s s' : SplayState α σ τ}
    (hrev : ∀ z, (s'.nodes z).rev = (s.nodes z).rev) (t : AuxTree) :
    treeIds P s' t = treeIds P s t := by
  simp only [treeIds, SplayState.evalPairs_map_fst, hrev]

theorem inducedSubPar_shape (P : LctPayload α σ τ) {s s' : SplayState α σ τ}
    (hrev : ∀ z, (s'.nodes z).rev = (s.nodes z).rev)
    (hppar : ∀ z, (s'.nodes z).ppar = (s.nodes z).ppar) :
    ∀ (ts : List AuxTree) (x : ℕ), inducedSubPar P s' ts x = inducedSubPar P s ts x
  | [], _ => rfl
  | t :: ts, x => by
    simp only [inducedSubPar, treeIds_shape P hrev, hppar, inducedSubPar_shape P hrev hppar ts x]

theorem canonFreeList_shape {s s' : SplayState α σ τ}
    (hpar : ∀ z, (s'.nodes z).par = (s.nodes z).par) :
    ∀ k h, canonFreeList s' k h = canonFreeList s k h
  | 0, _ => rfl
  | k + 1, h => by simp only [canonFreeList, hpar, canonFreeList_shape hpar k]

theorem buildAuxTree_shape {s s' : SplayState α σ τ}
    (hl : ∀ z, (s'.nodes z).left = (s.nodes z).left)
    (hr : ∀ z, (s'.nodes z).right = (s.nodes z).right) :
    ∀ k x, buildAuxTree s' k x = buildAuxTree s k x
  | 0, _ => rfl
  | k + 1, x => by simp only [buildAuxTree, hl, hr, buildAuxTree_shape hl hr k]

theorem canonActive_shape {s s' : LctState α σ τ} (hS : SameShape s s') :
    canonActive s' = canonActive s := by
  unfold canonActive
  rw [hS.n, hS.fh, canonFreeList_shape hS.par]

theorem canonTrees_shape {s s' : LctState α σ τ} (hS : SameShape s s') :
    canonTrees s' = canonTrees s := by
  unfold canonTrees canonRoots
  rw [canonActive_shape hS, hS.n]
  simp only [hS.par]
  congr 1
  funext x
  exact buildAuxTree_shape hS.left hS.right _ x

/-- The potentials of the model depend only on the shape of the state. -/
theorem potentials_shape (P : LctPayload α σ τ) {s s' : LctState α σ τ} (hS : SameShape s s') :
    sumTreePhi P s' = sumTreePhi P s ∧ heavyCount P s' = heavyCount P s := by
  have hpar : inducedSubPar P s'.splay (canonTrees s) = inducedSubPar P s.splay (canonTrees s) :=
    funext (inducedSubPar_shape P hS.rev hS.ppar _)
  unfold sumTreePhi heavyCount vSize heavyCountList isHeavyEdge
  simp only [canonActive_shape hS, canonTrees_shape hS, hpar, hS.ppar, treeIds_shape P hS.rev]
  exact ⟨trivial, trivial⟩

end Shape

/-- A point write has the shape of the expose before it. -/
theorem write_shape (s : PathTreeState) (x : ℕ) (v : Option PathEdgeValue) :
    SameShape (lctExpose pathPayload s x) (pathTreeWrite s x v) := by
  refine ⟨rfl, rfl, fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_⟩ <;>
  · simp only [pathTreeWrite, SplayState.pull_left_eq, SplayState.pull_right_eq,
      SplayState.pull_par_eq, SplayState.pull_ppar_eq, SplayState.pull_rev_eq,
      SplayState.updateNode]
    split_ifs with hz
    · subst hz; rfl
    · rfl

/-- A point write has the potentials of the expose before it. -/
theorem write_potentials (s : PathTreeState) (x : ℕ) (v : Option PathEdgeValue) :
    sumTreePhi pathPayload (pathTreeWrite s x v) = sumTreePhi pathPayload (lctExpose pathPayload s x) ∧
      heavyCount pathPayload (pathTreeWrite s x v) =
        heavyCount pathPayload (lctExpose pathPayload s x) :=
  potentials_shape pathPayload (write_shape s x v)

/-- Two witnesses of the invariant have the same active nodes. The free list is fixed by the
state, since both witnesses follow it from the free head. -/
theorem active_mem {s : PathTreeState} {trees trees' : List AuxTree} {fl fl' : List ℕ}
    {d d' : ℕ → ℕ} (W : LctInvWith pathPayload s trees fl d)
    (W' : LctInvWith pathPayload s trees' fl' d') {x : ℕ}
    (hx : x ∈ trees'.flatMap AuxTree.toList) : x ∈ trees.flatMap AuxTree.toList := by
  have h1 := canonFreeList_eq_of_FreeListInv W.freeListInv (k := fl.length + fl'.length)
    (by omega)
  have h2 := canonFreeList_eq_of_FreeListInv W'.freeListInv (k := fl.length + fl'.length)
    (by omega)
  have hfl : fl' = fl := h2.symm.trans h1
  subst hfl
  exact lct_active_mem_of_same_freeList W W' rfl hx

/-- A node that is active for the contract is active in every witness. -/
theorem active_of {s : PathTreeState} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees fl d) {x : ℕ} (hx : pathTreeActive s x) :
    x ∈ trees.flatMap AuxTree.toList := by
  obtain ⟨_, _, _, W', h⟩ := hx
  exact active_mem W W' h

/-- When find-ready returns `0`, it pays only for the entries it pops. -/
theorem findCost_zero {w : ℕ} {p : Program}
    {Lay : NodeLayout (Option PathEdgeValue) PathSummary PathTag}
    {ok : PayloadOk (Option PathEdgeValue) PathSummary PathTag}
    (S : PayloadSteps w p pathPayload Lay ok) (T : ReadyTests w p Lay pathRs pathRv)
    {s : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees free depth) (hE : ValsOnEdges s) (hF : FreeShape s free) :
    ∀ R : List ℕ, ReadyIdx s trees R.reverse →
      (findLoop pathPayload pathRs pathRv s R).2.2 = 0 →
      findCost S T s R ≤ (T.cost + 300) * R.length + 50
  | [], _, _ => by simp [findCost]
  | x :: R, hI, h0 => by
    rw [List.reverse_cons] at hI
    by_cases hv : ValidG pathRs s.n s.splay x
    · exfalso
      have hv' : ValidRoot s x := hv
      obtain ⟨t, ht, rfl⟩ := validRoot_root W hF hv'
      have hd : descend pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId =
          ((descend pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId).1,
            (descend pathPayload pathRs pathRv s.splay (2 * s.n + 1) t.rootId).2) := rfl
      obtain ⟨hready, -, -⟩ := descend_ready W hE ht hv'.2.2.2.1 hd
      have hloop : (findLoop pathPayload pathRs pathRv s (t.rootId :: R)).2.2 =
          descNode pathPayload pathRs pathRv s t.rootId := by
        simp [findLoop, hv]
      rw [hloop] at h0
      exact (pathTreeReady_bounds hready).1 h0
    · have hloop : findLoop pathPayload pathRs pathRv s (x :: R) =
          findLoop pathPayload pathRs pathRv s R := by
        simp [findLoop, hv]
      have hcost : findCost S T s (x :: R) = T.cost + 300 + findCost S T s R := by
        simp only [findCost, ite_eq_right hv]
      rw [hloop] at h0
      rw [hcost, List.length_cons]
      have ih := findCost_zero S T W hE hF R (readyIdx_pop W hE hI hv) h0
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- An operation that costs at most `A` per counted unit, where the stack entries it adds are
counted at `340` each, meets its budget when `A ≤ C (L + 1) ^ 2` and the units obey the
potential bounds of the model. -/
theorem pay {C L c A rot spl : ℕ} {s s' : PathTreeState} {S S' : List ℕ}
    (hA : A ≤ C * (L + 1) ^ 2)
    (hc : c + 340 * S'.length ≤ A * (rot + spl + 1) + 340 * S.length)
    (hr : rot + sumTreePhi pathPayload s' ≤
      sumTreePhi pathPayload s + 18 * Nat.log 2 (2 * s.n + 1))
    (hs : spl + heavyCount pathPayload s' ≤
      heavyCount pathPayload s + 6 * Nat.log 2 (2 * s.n + 1) + 10) :
    c + pathPhi C L s' S' ≤ pathTreeBudget C L s.n + pathPhi C L s S := by
  have hk := Nat.mul_le_mul_right (rot + spl + 1) hA
  have h := pathTreeCost_amortized (constant := C) (limbs := L) (n := s.n)
    (cost := c + 340 * S'.length - 340 * S.length) (by omega) hr hs
  unfold pathPhi
  omega

/-- A rate `R + X` with `2000 ≤ X` pays for `R` per unit, `X` once, and `2000` per splice. -/
theorem absorb {R X a b : ℕ} (hX : 2000 ≤ X) :
    R * (a + b + 1) + X + 2000 * b ≤ (R + X) * (a + b + 1) := by
  have e1 : (R + X) * (a + b + 1) = R * (a + b + 1) + (X * a + X * b + X) := by ring
  have : 2000 * b ≤ X * b := Nat.mul_le_mul_right b hX
  omega

/-- The constant of the contract. -/
def pathC : ℕ := 10000000

/-- The allocation of the contract: the arena for the initialization, and the scratch space of
the tree procedures with the output blocks for the operations. -/
def pathAlloc (L i n : ℕ) (_ : List ℕ) : ℕ :=
  if i = 7 then arenaEnd 0 n L else 20 * treeLimbs L + 100

theorem stepsAt_cost {w h b0 K : ℕ} {p : Program} (hh : 0 < h) (hw : 2 * h + 2 ≤ w)
    (hp : p.HasAt b0 (pathTreeBodies h b0)) : (stepsAt K hh hw hp).cost = 2000 * K + 2000 := rfl

theorem testsAt_cost {w h b0 K : ℕ} {p : Program} (hh : 0 < h) (hw : 2 * h + 2 ≤ w)
    (hp : p.HasAt b0 (pathTreeBodies h b0)) (hK : 0 < K) : (testsAt K hh hw hp hK).cost = 40 :=
  rfl

/-- The rates of the tree procedures fit the constant. -/
theorem unit_le {w h b0 : ℕ} {p : Program} (L : ℕ) (hh : 0 < h) (hw : 2 * h + 2 ≤ w)
    (hp : p.HasAt b0 (pathTreeBodies h b0)) :
    opRate (stepsAt (treeLimbs L) hh hw hp) +
      findRate (stepsAt (treeLimbs L) hh hw hp) (testsAt (treeLimbs L) hh hw hp (treeLimbs_pos L)) +
      (stepsAt (treeLimbs L) hh hw hp).cost + 400 * treeLimbs L + 2000 ≤ pathC * (L + 1) ^ 2 := by
  have hsq : L + 1 ≤ (L + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  simp only [opRate, findRate, testsAt_cost, exposeRate, splayRate, singleCost, pushDownCost,
    splayStepCost, rotateCost, stepsAt_cost, pathLayout]
  simp only [treeLimbs, pathC]
  omega

end MinCostFlow.LinkCut.PathProg
