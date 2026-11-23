module

public import MinCostFlow.SparseCore.Program.TourSplayProg
public import MinCostFlow.SparseCore.Program.TourCycle
import Mathlib.Tactic

/-!
# Higher-level WordRAM splay sequence operations for tour maintenance

Builds and verifies the amortized `O(log (cap + 2))` sequence operations on top of
`TourSplayProg`:
- `tourJoinBody`: concatenate two (possibly empty) splay trees;
- `tourRotateFrontBody`: cyclically rotate a tree so `x` becomes first (`rotateToList x`);
- `tourDeleteNodeBody`: remove `x` from its tree, leaving `AuxTree.node x .leaf .leaf` as a
  zero-potential singleton in the forest;
- `tourInsertBeforeBody`: splice singleton `AuxTree.node x .leaf .leaf` immediately before `y`
  in `y`'s tree.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Helpers for optional trees, permutations, and `sumOk` -/

/-- Lift an optional nonempty `AuxTree` to a 0-or-1 element forest list. -/
def optTrees (t? : Option AuxTree) : List AuxTree := t?.toList

/-- Root id of an optional tree (`0` when `none`). -/
def optRoot (t? : Option AuxTree) : ℕ := t?.elim 0 AuxTree.rootId

/-- In-order node list of an optional tree (`[]` when `none`). -/
def optList (t? : Option AuxTree) : List ℕ := t?.elim [] AuxTree.toList

/-- Cyclically rotate a `List ℕ` so that `x` comes first (if `x ∈ xs`). -/
def rotateNatList (x : ℕ) (xs : List ℕ) : List ℕ :=
  if x ∈ xs then xs.drop (xs.idxOf x) ++ xs.take (xs.idxOf x) else xs

theorem rotateNatList_map {f : ℕ → Bundle.End} (hinj : Function.Injective f)
    {x : ℕ} {xs : List ℕ} :
    (rotateNatList x xs).map f = rotateToList (f x) (xs.map f) := by
  unfold rotateNatList rotateToList
  by_cases hx : x ∈ xs
  · have hfx : f x ∈ xs.map f := List.mem_map.mpr ⟨x, hx, rfl⟩
    have hidx : (xs.map f).idxOf (f x) = xs.idxOf x := by
      clear * - hinj
      induction xs with
      | nil => simp
      | cons a as ih =>
        by_cases h : a = x
        · subst h; simp
        · have hne : f a ≠ f x := fun heq => h (hinj heq)
          simp [h, hne, ih]
    simp [hx, hfx, hidx, List.map_append, List.map_drop, List.map_take]
  · have hfx : f x ∉ xs.map f := fun hm => by
      rcases List.mem_map.mp hm with ⟨y, hy, hyx⟩
      exact hx (hinj hyx ▸ hy)
    simp [hx, hfx]

theorem forestPhi_perm {ts₁ ts₂ : List AuxTree} (hp : ts₁.Perm ts₂) :
    forestPhi ts₁ = forestPhi ts₂ :=
  List.Perm.sum_eq (hp.map fun t => t.treePhi tourVSize)

theorem tourDetachLeft_sumOk {w cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    {pre post : List AuxTree} {L R : AuxTree}
    (hf : TourForestInv cap st (pre ++ AuxTree.node x L R :: post)) (hvals : TourValsOk w cap st) :
    x ≠ 0 → (st.nodes x).left ≠ 0 →
    (tourOk w).sumOk (pullSum tourPayload ((st.setPar (st.nodes x).left 0).setLeft x 0) x) := by
  intro hx0 hl0
  obtain ⟨hp, _, hval, _⟩ := tourDetachLeft_preserves hf
  have hvals' : TourValsOk w cap (tourDetachLeft st x) :=
    ⟨hvals.1, fun u hu => by rw [hval u hu]; exact hvals.2 u hu⟩
  have hmem : AuxTree.node x .leaf R ∈ pre ++ ((if L = .leaf then [] else [L]) ++ [AuxTree.node x .leaf R]) ++ post := by simp
  have hsb := hp.sum_bounds hvals' hmem x (by simp [AuxTree.toList])
  have hcnt := hp.countNodes_le hmem
  have heq : ((tourDetachLeft st x).nodes x).sum =
      pullSum tourPayload ((st.setPar (st.nodes x).left 0).setLeft x 0) x := by
    simp only [tourDetachLeft, hx0, hl0, ↓reduceIte, pull, updateNode]; rfl
  rw [← heq]
  exact ⟨by have := hvals.1; omega, by have := hvals.1; omega, by have := hvals.1; omega, hsb.2.2.2⟩

theorem tourDetachRight_sumOk {w cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    {pre post : List AuxTree} {L R : AuxTree}
    (hf : TourForestInv cap st (pre ++ AuxTree.node x L R :: post)) (hvals : TourValsOk w cap st) :
    x ≠ 0 → (st.nodes x).right ≠ 0 →
    (tourOk w).sumOk (pullSum tourPayload ((st.setPar (st.nodes x).right 0).setRight x 0) x) := by
  intro hx0 hr0
  obtain ⟨hp, _, hval, _⟩ := tourDetachRight_preserves hf
  have hvals' : TourValsOk w cap (tourDetachRight st x) :=
    ⟨hvals.1, fun u hu => by rw [hval u hu]; exact hvals.2 u hu⟩
  have hmem : AuxTree.node x L .leaf ∈ pre ++ (AuxTree.node x L .leaf :: (if R = .leaf then [] else [R])) ++ post := by simp
  have hsb := hp.sum_bounds hvals' hmem x (by simp [AuxTree.toList])
  have hcnt := hp.countNodes_le hmem
  have heq : ((tourDetachRight st x).nodes x).sum =
      pullSum tourPayload ((st.setPar (st.nodes x).right 0).setRight x 0) x := by
    simp only [tourDetachRight, hx0, hr0, ↓reduceIte, pull, updateNode]; rfl
  rw [← heq]
  exact ⟨by have := hvals.1; omega, by have := hvals.1; omega, by have := hvals.1; omega, hsb.2.2.2⟩

theorem tourAttachLeft_sumOk {w cap y : ℕ} {st : SplayState TourVal TourSum Unit}
    {rest : List AuxTree} {tL R : AuxTree}
    (hf : TourForestInv cap st (tL :: AuxTree.node y .leaf R :: rest)) (hvals : TourValsOk w cap st) :
    y ≠ 0 →
    (tourOk w).sumOk (pullSum tourPayload
      (if tL.rootId = 0 then st.setLeft y tL.rootId
       else ((st.setLeft y tL.rootId).setPar tL.rootId y).setPpar tL.rootId 0) y) := by
  intro hy0
  obtain ⟨hp, _, hval, _⟩ := tourAttachLeft_preserves hf
  have hvals' : TourValsOk w cap (tourAttachLeft st y tL.rootId) :=
    ⟨hvals.1, fun u hu => by rw [hval u hu]; exact hvals.2 u hu⟩
  have hsb := hp.sum_bounds hvals' (by simp : AuxTree.node y tL R ∈ _) y (by simp [AuxTree.toList])
  have hcnt := hp.countNodes_le (by simp : AuxTree.node y tL R ∈ _)
  have heq : ((tourAttachLeft st y tL.rootId).nodes y).sum =
      pullSum tourPayload (if tL.rootId = 0 then st.setLeft y tL.rootId
        else ((st.setLeft y tL.rootId).setPar tL.rootId y).setPpar tL.rootId 0) y := by
    unfold tourAttachLeft pull updateNode; simp only [hy0, ↓reduceIte]; rfl
  rw [← heq]
  exact ⟨by have := hvals.1; omega, by have := hvals.1; omega, by have := hvals.1; omega, hsb.2.2.2⟩

theorem tourSetVal_sumOk {w cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    {pre post : List AuxTree} {L R : AuxTree} {v : TourVal}
    (hf : TourForestInv cap st (pre ++ AuxTree.node x L R :: post)) (hvals : TourValsOk w cap st)
    (hv : v.rootTag < 2 ^ w) :
    x ≠ 0 →
    (tourOk w).sumOk (pullSum tourPayload (st.updateNode x fun nd => { nd with val := v }) x) := by
  intro hx0
  obtain ⟨hp, hvx, hout⟩ := tourSetVal_preserves v hf
  have hvals' : TourValsOk w cap (tourSetVal st x v) := ⟨hvals.1, fun u hu => by
    by_cases hux : u = x
    · subst hux; rw [hvx]; exact hv
    · rw [hout u hux]; exact hvals.2 u hu⟩
  have hmem : AuxTree.node x L R ∈ pre ++ AuxTree.node x L R :: post := by simp
  have hsb := hp.sum_bounds hvals' hmem x (by simp [AuxTree.toList])
  have hcnt := hp.countNodes_le hmem
  have heq : ((tourSetVal st x v).nodes x).sum =
      pullSum tourPayload (st.updateNode x fun nd => { nd with val := v }) x := by
    unfold tourSetVal pull pullSum updateNode; simp only [hx0, ↓reduceIte]
  rw [← heq]
  exact ⟨by have := hvals.1; omega, by have := hvals.1; omega, by have := hvals.1; omega, hsb.2.2.2⟩

/-! ## Amortized constants and procedure bundle -/

/-- Amortized per-`log` cost constant for `tourJoinBody`. -/
def TOUR_JOIN_AMORT : ℕ := 110000

/-- Amortized per-`log` cost constant for `tourRotateFrontBody`, `tourDeleteNodeBody`,
and `tourInsertBeforeBody`. -/
def TOUR_SEQ_AMORT : ℕ := 220000

/-! ## WordRAM bodies -/

/-- `tourJoin [nb, r1, r2, fuel, heap]`: concatenate trees `r1` and `r2`, returning the new root. -/
def tourJoinBody (walkProc splayProc attachLeftProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 2))
    (.cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 1))
      (.call 5 walkProc [.reg 0, .reg 2, .reg 3, .reg 4] ;;
       .call 6 splayProc [.reg 0, .reg 5, .reg 3, .reg 4] ;;
       .call 6 attachLeftProc [.reg 0, .reg 5, .reg 1, .reg 4] ;;
       .ret (.reg 5)))

/-- `tourRotateFront [nb, x, fuel, heap]`: rotate `x`'s tree so `x` becomes first. -/
def tourRotateFrontBody (splayProc detachLeftProc joinProc : ℕ) : Stmt :=
  .call 4 splayProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .call 4 detachLeftProc [.reg 0, .reg 1, .reg 3] ;;
  .call 5 joinProc [.reg 0, .reg 1, .reg 4, .reg 2, .reg 3] ;;
  .ret (.reg 5)

/-- `tourDeleteNode [nb, x, fuel, heap]`: remove `x` from its tree, returning the new root (`0` if empty). -/
def tourDeleteNodeBody (splayProc detachLeftProc detachRightProc joinProc : ℕ) : Stmt :=
  .call 4 splayProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .call 4 detachLeftProc [.reg 0, .reg 1, .reg 3] ;;
  .call 5 detachRightProc [.reg 0, .reg 1, .reg 3] ;;
  .call 6 joinProc [.reg 0, .reg 4, .reg 5, .reg 2, .reg 3] ;;
  .ret (.reg 6)

/-- `tourInsertBefore [nb, x, y, fuel, heap]`: insert detached singleton `x` immediately before `y`, returning `y`. -/
def tourInsertBeforeBody (splayProc detachLeftProc attachLeftProc : ℕ) : Stmt :=
  .call 5 splayProc [.reg 0, .reg 2, .reg 3, .reg 4] ;;
  .call 5 detachLeftProc [.reg 0, .reg 2, .reg 4] ;;
  .call 6 attachLeftProc [.reg 0, .reg 1, .reg 5, .reg 4] ;;
  .call 6 attachLeftProc [.reg 0, .reg 2, .reg 1, .reg 4] ;;
  .ret (.reg 2)

theorem tourSplayOps_bodies_noRand (wP sP dL dR aL jP : ℕ) :
    (tourJoinBody wP sP aL).NoRand ∧
    (tourRotateFrontBody sP dL jP).NoRand ∧
    (tourDeleteNodeBody sP dL dR jP).NoRand ∧
    (tourInsertBeforeBody sP dL aL).NoRand := by
  simp [tourJoinBody, tourRotateFrontBody, tourDeleteNodeBody, tourInsertBeforeBody, Stmt.NoRand]

/-- Core + sequence splay procedures installed in `p`. -/
structure TourSplayOpsProcs (w : ℕ) (p : Program) extends TourSplayCoreProcs w p where
  detachLeft : ℕ
  detachLeft_body : p.procs[detachLeft]? = some (tourDetachLeftBody splay.pull)
  detachRight : ℕ
  detachRight_body : p.procs[detachRight]? = some (tourDetachRightBody splay.pull)
  attachLeft : ℕ
  attachLeft_body : p.procs[attachLeft]? = some (tourAttachLeftBody splay.pull)
  setVal : ℕ
  setVal_body : p.procs[setVal]? = some (tourSetValBody splay.pull)
  initNode : ℕ
  initNode_body : p.procs[initNode]? = some tourInitNodeBody
  join : ℕ
  join_body : p.procs[join]? = some (tourJoinBody walkProc splay.splay attachLeft)
  rotateFront : ℕ
  rotateFront_body : p.procs[rotateFront]? = some (tourRotateFrontBody splay.splay detachLeft join)
  deleteNode : ℕ
  deleteNode_body : p.procs[deleteNode]? = some (tourDeleteNodeBody splay.splay detachLeft detachRight join)
  insertBefore : ℕ
  insertBefore_body : p.procs[insertBefore]? = some (tourInsertBeforeBody splay.splay detachLeft attachLeft)

/-! ## Amortized run theorems -/

private theorem heapOk_of_frame {nb cap heap sp : ℕ} {w : ℕ} {mem M : ℕ → ℕ}
    (hheap : HeapOk tourLayout w nb cap heap sp mem)
    (hfr : TreeFrame tourLayout nb cap heap mem M) :
    HeapOk tourLayout w nb cap heap sp M :=
  ⟨hheap.rec_le, hheap.room, hfr.1, hheap.wide⟩

private theorem heapOk_zero {nb cap heap sp : ℕ} {w : ℕ} {mem : ℕ → ℕ}
    (hheap : HeapOk tourLayout w nb cap heap sp mem) :
    HeapOk tourLayout w nb cap heap 0 mem :=
  ⟨hheap.rec_le, by have := hheap.room; omega, hheap.zero, hheap.wide⟩

theorem tour_runs_seq_normal {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {c₁ c₂ : ℕ}
    (h1 : Runs w p ω s st .normal st₁ c₁) (h2 : Runs w p ω t st₁ o st₂ c₂) :
    Runs w p ω (s ;; t) st o st₂ (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h1, h2, rfl⟩)

theorem runs_seq_ret {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st' : State} {v c₁ : ℕ}
    (h1 : Runs w p ω s st (.returned v) st' c₁) :
    Runs w p ω (s ;; t) st (.returned v) st' (c₁ + 1) :=
  runs_seq_iff.mpr (Or.inl ⟨v, c₁, h1, rfl, rfl⟩)

theorem tour_runs_call_of {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {st st₁ : State} {vs : List ℕ} {body : Stmt} {o₁ : Outcome} {c₁ : ℕ}
    (hget : p.procs[f]? = some body) (hev : evalArgs w st args = some vs)
    (hrun : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁) :
    Runs w p ω (.call r f args) st .normal
      { st₁ with regs := Function.update st.regs r o₁.value }
      (argsSize args + c₁ + 1) :=
  runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hev, hget, hrun, rfl, rfl, rfl⟩

theorem runs_call_regs3 {w : ℕ} {p : Program} {ω : ℕ → Bool} (r : ℕ) {f : ℕ} (r0 r1 r2 : ℕ)
    {st st₁ : State} {v0 v1 v2 : ℕ} {body : Stmt} {o₁ : Outcome} {c₁ : ℕ}
    (hget : p.procs[f]? = some body)
    (h0 : st.regs r0 = v0) (h1 : st.regs r1 = v1) (h2 : st.regs r2 = v2)
    (hrun : Runs w p ω body (startState [v0, v1, v2] st.mem st.pos) o₁ st₁ c₁) :
    Runs w p ω (.call r f [.reg r0, .reg r1, .reg r2]) st .normal
      { st₁ with regs := Function.update st.regs r o₁.value } (4 + c₁) := by
  have h := tour_runs_call_of (r := r) (args := [.reg r0, .reg r1, .reg r2]) hget
    (by simp [evalArgs, Expr.eval, h0, h1, h2]) hrun
  convert h using 1; simp [argsSize, Expr.size]; omega

theorem runs_call_regs4 {w : ℕ} {p : Program} {ω : ℕ → Bool} (r : ℕ) {f : ℕ} (r0 r1 r2 r3 : ℕ)
    {st st₁ : State} {v0 v1 v2 v3 : ℕ} {body : Stmt} {o₁ : Outcome} {c₁ : ℕ}
    (hget : p.procs[f]? = some body)
    (h0 : st.regs r0 = v0) (h1 : st.regs r1 = v1) (h2 : st.regs r2 = v2) (h3 : st.regs r3 = v3)
    (hrun : Runs w p ω body (startState [v0, v1, v2, v3] st.mem st.pos) o₁ st₁ c₁) :
    Runs w p ω (.call r f [.reg r0, .reg r1, .reg r2, .reg r3]) st .normal
      { st₁ with regs := Function.update st.regs r o₁.value } (5 + c₁) := by
  have h := tour_runs_call_of (r := r) (args := [.reg r0, .reg r1, .reg r2, .reg r3]) hget
    (by simp [evalArgs, Expr.eval, h0, h1, h2, h3]) hrun
  convert h using 1; simp [argsSize, Expr.size]; omega

theorem runs_call_regs5 {w : ℕ} {p : Program} {ω : ℕ → Bool} (r : ℕ) {f : ℕ} (r0 r1 r2 r3 r4 : ℕ)
    {st st₁ : State} {v0 v1 v2 v3 v4 : ℕ} {body : Stmt} {o₁ : Outcome} {c₁ : ℕ}
    (hget : p.procs[f]? = some body)
    (h0 : st.regs r0 = v0) (h1 : st.regs r1 = v1) (h2 : st.regs r2 = v2)
    (h3 : st.regs r3 = v3) (h4 : st.regs r4 = v4)
    (hrun : Runs w p ω body (startState [v0, v1, v2, v3, v4] st.mem st.pos) o₁ st₁ c₁) :
    Runs w p ω (.call r f [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4]) st .normal
      { st₁ with regs := Function.update st.regs r o₁.value } (6 + c₁) := by
  have h := tour_runs_call_of (r := r) (args := [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4]) hget
    (by simp [evalArgs, Expr.eval, h0, h1, h2, h3, h4]) hrun
  convert h using 1; simp [argsSize, Expr.size]; omega

theorem runs_call_regs6 {w : ℕ} {p : Program} {ω : ℕ → Bool} (r : ℕ) {f : ℕ} (r0 r1 r2 r3 r4 r5 : ℕ)
    {st st₁ : State} {v0 v1 v2 v3 v4 v5 : ℕ} {body : Stmt} {o₁ : Outcome} {c₁ : ℕ}
    (hget : p.procs[f]? = some body)
    (h0 : st.regs r0 = v0) (h1 : st.regs r1 = v1) (h2 : st.regs r2 = v2)
    (h3 : st.regs r3 = v3) (h4 : st.regs r4 = v4) (h5 : st.regs r5 = v5)
    (hrun : Runs w p ω body (startState [v0, v1, v2, v3, v4, v5] st.mem st.pos) o₁ st₁ c₁) :
    Runs w p ω (.call r f [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4, .reg r5]) st .normal
      { st₁ with regs := Function.update st.regs r o₁.value } (7 + c₁) := by
  have h := tour_runs_call_of (r := r) (args := [.reg r0, .reg r1, .reg r2, .reg r3, .reg r4, .reg r5]) hget
    (by simp [evalArgs, Expr.eval, h0, h1, h2, h3, h4, h5]) hrun
  convert h using 1; simp [argsSize, Expr.size]; omega

theorem runs_ret_reg {w : ℕ} {p : Program} {ω : ℕ → Bool} {r v : ℕ} {st : State}
    (h : st.regs r = v) :
    Runs w p ω (.ret (.reg r)) st (.returned v) st 2 :=
  runs_ret_iff.mpr ⟨v, by simp [Expr.eval, h], rfl, rfl, rfl⟩

theorem runs_ret_const {w : ℕ} {p : Program} {ω : ℕ → Bool} {v : ℕ} {st : State}
    (hv : v < 2 ^ w) :
    Runs w p ω (.ret (.const v)) st (.returned v) st 2 :=
  runs_ret_iff.mpr ⟨v, by simp [Expr.eval, hv], rfl, rfl, rfl⟩

theorem tour_runs_cond_true {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st st' : State} {o : Outcome} {v c₁ : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0) (hr : Runs w p ω s₁ st o st' c₁) :
    Runs w p ω (.cond e s₁ s₂) st o st' (e.size + c₁ + 1) :=
  runs_cond_iff.mpr ⟨v, c₁, he, by simpa [hv] using hr, rfl⟩

theorem tour_runs_cond_false {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st st' : State} {o : Outcome} {c₁ : ℕ}
    (he : e.eval w st = some 0) (hr : Runs w p ω s₂ st o st' c₁) :
    Runs w p ω (.cond e s₁ s₂) st o st' (e.size + c₁ + 1) :=
  runs_cond_iff.mpr ⟨0, c₁, he, by simpa using hr, rfl⟩

private theorem eval_eq_zero_of_ne {w r v : ℕ} {st : State} (hr : st.regs r = v)
    (hne : v ≠ 0) (hw : 1 < 2 ^ w) :
    (Expr.bin .eq (.reg r) (.const 0)).eval w st = some 0 := by
  simp [Expr.eval, hr, BinOp.eval, hne, Nat.pos_of_ne_zero (by omega : 2 ^ w ≠ 0)]

private theorem eval_eq_zero_of_eq {w r : ℕ} {st : State} (hr : st.regs r = 0)
    (hw : 1 < 2 ^ w) :
    (Expr.bin .eq (.reg r) (.const 0)).eval w st = some 1 := by
  simp [Expr.eval, hr, BinOp.eval, Nat.pos_of_ne_zero (by omega : 2 ^ w ≠ 0), hw]

/-- Amortized run theorem for `tourJoinBody` on two optional trees `t₁?, t₂?`. -/
theorem tourJoinBody_runs {w nb cap heap fuel pos : ℕ} {p : Program}
    (C : TourSplayOpsProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t₁? t₂? : Option AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (optTrees t₁? ++ optTrees t₂? ++ rest))
    (hvals : TourValsOk w cap st)
    (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ t'? s' o st' c,
      Runs w p ω (tourJoinBody C.walkProc C.splay.splay C.attachLeft)
        (startState [nb, optRoot t₁?, optRoot t₂?, fuel, heap] mem pos) o st' c ∧
      o.value = optRoot t'? ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (optTrees t'? ++ rest) ∧
      TourValsOk w cap s' ∧
      optList t'? = optList t₁? ++ optList t₂? ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ optList t₁? ++ optList t₂?, s'.nodes u = st.nodes u) ∧
      c + TOUR_PHI_MULT * forestPhi (optTrees t'? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (optTrees t₁? ++ optTrees t₂? ++ rest) +
          TOUR_JOIN_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hwide := hheap.wide
  unfold tourJoinBody; rw [startState]
  cases t₁? with
  | none =>
    set st0 : State := ⟨mem, fun i => [nb, optRoot none, optRoot t₂?, fuel, heap].getD i 0, pos⟩
    have hc0 := eval_eq_zero_of_eq (w := w) (r := 1) (st := st0) (by simp [st0, optRoot]) (by omega)
    have hret : Runs w p ω (.ret (.reg 2)) st0 (.returned (optRoot t₂?)) st0 _ :=
      runs_ret_iff.mpr ⟨_, by simp only [st0]; eval_expr, rfl, rfl, rfl⟩
    refine ⟨t₂?, st, .returned (optRoot t₂?), st0, _,
      tour_runs_cond_true hc0 (by omega) hret, rfl, hnodes,
      TreeFrame.refl hheap.zero, by simpa [optTrees] using hf, hvals, by simp [optList],
      fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    simp only [optTrees, Option.toList, List.nil_append, Expr.size, TOUR_JOIN_AMORT]; omega
  | some t₁ =>
    have ht₁_mem : t₁ ∈ optTrees (some t₁) ++ optTrees t₂? ++ rest := by simp [optTrees]
    have ht₁_ne : t₁ ≠ .leaf := hf.nonEmpty t₁ ht₁_mem
    have hr₁_nz : t₁.rootId ≠ 0 := by
      cases t₁ with
      | leaf => exact absurd rfl ht₁_ne
      | node _ _ _ => exact (hf.treesInv _ ht₁_mem).sub.1
    cases t₂? with
    | none =>
      set st0 : State := ⟨mem, fun i => [nb, optRoot (some t₁), optRoot none, fuel, heap].getD i 0, pos⟩
      have hc0 := eval_eq_zero_of_ne (w := w) (r := 1) (v := t₁.rootId) (st := st0)
        (by simp [st0, optRoot]) hr₁_nz (by omega)
      have hc1 := eval_eq_zero_of_eq (w := w) (r := 2) (st := st0) (by simp [st0, optRoot]) (by omega)
      have hret : Runs w p ω (.ret (.reg 1)) st0 (.returned t₁.rootId) st0 _ :=
        runs_ret_iff.mpr ⟨_, by simp only [st0, optRoot, Option.elim]; eval_expr, rfl, rfl, rfl⟩
      refine ⟨some t₁, st, .returned t₁.rootId, st0, _,
        tour_runs_cond_false hc0 (tour_runs_cond_true hc1 (by omega) hret),
        rfl, hnodes, TreeFrame.refl hheap.zero, by simpa [optTrees] using hf, hvals,
        by simp [optList], fun _ _ => rfl, fun _ _ => rfl, ?_⟩
      simp only [optTrees, Option.toList, List.append_nil, List.cons_append, List.nil_append,
        Expr.size, TOUR_JOIN_AMORT]; omega
    | some t₂ =>
      have ht₂_mem : t₂ ∈ optTrees (some t₁) ++ optTrees (some t₂) ++ rest := by simp [optTrees]
      have ht₂_ne : t₂ ≠ .leaf := hf.nonEmpty t₂ ht₂_mem
      have hr₂_nz : t₂.rootId ≠ 0 := by
        cases t₂ with
        | leaf => exact absurd rfl ht₂_ne
        | node _ _ _ => exact (hf.treesInv _ ht₂_mem).sub.1
      have hcnt₂ : t₂.countNodes < fuel := lt_of_le_of_lt (hf.countNodes_le ht₂_mem) hfuel
      have hf' : TourForestInv cap st ([t₁] ++ t₂ :: rest) := by simpa [optTrees] using hf
      obtain ⟨m, t₂', o₁, st₁, c₁, o₂, st₂, c₂, hrun₁, hv₁, hrun₂, hn₂, hfr₂, hinv₂, hvals₂,
        hne₂', hroot₂', hm_left0, hlist₂', hm_head, hout₂, hcost₂⟩ :=
        tourFindLeftmost_cost_le (pos := pos) C.toTourSplayCoreProcs ω hnodes hf' hvals hcnt₂ hfuelW hheap
      have hm_mem : m ∈ t₂.toList := List.mem_of_head? hm_head
      set s₁ := SplayState.splay tourPayload st fuel m
      cases ht₂c : t₂' with
      | leaf => exact absurd ht₂c hne₂'
      | node mid l₂ R₂ =>
        have hmid : mid = m := by simpa [ht₂c, AuxTree.rootId] using hroot₂'
        rcases hmid with rfl
        rw [ht₂c] at hinv₂ hlist₂' hcost₂
        have hl₂_leaf : l₂ = .leaf := by
          have hsub_m := (hinv₂.treesInv (AuxTree.node mid l₂ R₂) (by simp)).sub
          have hml := hsub_m.2.1
          rw [hm_left0] at hml
          cases l₂ with
          | leaf => rfl
          | node lid _ _ =>
            have hnz : lid ≠ 0 := hsub_m.2.2.2.2.2.2.2.1.1
            simp [AuxTree.rootId] at hml; exact absurd hml.symm hnz
        subst hl₂_leaf
        have hinv₂' : TourForestInv cap s₁ (t₁ :: AuxTree.node mid .leaf R₂ :: rest) := by
          simpa using hinv₂
        have hm_cap : mid ≤ cap := (hinv₂'.mem_inCap (t := AuxTree.node mid .leaf R₂) (by simp) (by simp [AuxTree.toList])).2
        have hr₁_cap : t₁.rootId ≤ cap := (hinv₂'.mem_inCap (t := t₁) (by simp) (AuxTree.rootId_mem ht₁_ne)).2
        obtain ⟨o₃, st₃, c₃, hrun₃, ⟨hn₃, hfr₃⟩, hc₃⟩ := tourAttachLeftBody_runs (pos := st₂.pos)
          C.toTourSplayCoreProcs ω hn₂ hinv₂'.ptrOk hm_cap hr₁_cap
          (heapOk_zero (heapOk_of_frame hheap hfr₂)) (tourAttachLeft_sumOk hinv₂' hvals₂)
        obtain ⟨hinv₃, hout₃, hval₃, hphi₃⟩ := tourAttachLeft_preserves hinv₂'
        have hdep_m : t₂.depthOf mid < fuel := lt_trans (auxTree_depthOf_lt_countNodes hm_mem) hcnt₂
        obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf' hm_mem hdep_m
        have hval_all : ∀ u ≤ cap, ((tourAttachLeft s₁ mid t₁.rootId).nodes u).val = (st.nodes u).val := by
          intro u hu; rw [hval₃ u hu]; exact hval_sp u hu
        have hvals₃ : TourValsOk w cap (tourAttachLeft s₁ mid t₁.rootId) :=
          ⟨hvals.1, fun u hu => by rw [hval_all u hu]; exact hvals.2 u hu⟩
        have hret_run : ∃ st_fin c_fin, st_fin.mem = st₃.mem ∧ c_fin ≤ c₁ + c₂ + c₃ + 30 ∧ Runs w p ω
            (.call 5 C.walkProc [.reg 0, .reg 2, .reg 3, .reg 4] ;;
             .call 6 C.splay.splay [.reg 0, .reg 5, .reg 3, .reg 4] ;;
             .call 6 C.attachLeft [.reg 0, .reg 5, .reg 1, .reg 4] ;;
             .ret (.reg 5))
            ⟨mem, fun i => [nb, t₁.rootId, t₂.rootId, fuel, heap].getD i 0, pos⟩
            (.returned mid) st_fin c_fin := by
          set s0 : State := ⟨mem, fun i => [nb, t₁.rootId, t₂.rootId, fuel, heap].getD i 0, pos⟩
          set s1_st : State := { st₁ with regs := Function.update s0.regs 5 o₁.value }
          set s2_st : State := { st₂ with regs := Function.update s1_st.regs 6 o₂.value }
          set s3_st : State := { st₃ with regs := Function.update s2_st.regs 6 o₃.value }
          have hc_step1 := runs_call_regs4 5 0 2 3 4 (st := s0) C.walk_body (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) hrun₁
          have hc_step2 := runs_call_regs4 6 0 5 3 4 (st := s1_st) C.splay.splay_body (by simp [s1_st, s0]) (by simp [s1_st, hv₁]) (by simp [s1_st, s0]) (by simp [s1_st, s0]) hrun₂
          have hc_step3 := runs_call_regs4 6 0 5 1 4 (st := s2_st) C.attachLeft_body (by simp [s2_st, s1_st, s0]) (by simp [s2_st, s1_st, hv₁]) (by simp [s2_st, s1_st, s0]) (by simp [s2_st, s1_st, s0]) hrun₃
          have hret4 := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s3_st) (r := 5) (v := mid) (by simp [s3_st, s2_st, s1_st, hv₁])
          exact ⟨s3_st, _, rfl, by omega, tour_runs_seq_normal hc_step1 (tour_runs_seq_normal hc_step2 (tour_runs_seq_normal hc_step3 hret4))⟩
        obtain ⟨st_fin, c_fin, hmem_fin, hcfin, hret_run⟩ := hret_run
        have hc0 := eval_eq_zero_of_ne (w := w) (r := 1) (v := t₁.rootId)
          (st := ⟨mem, fun i => [nb, optRoot (some t₁), optRoot (some t₂), fuel, heap].getD i 0, pos⟩)
          (by simp [optRoot]) hr₁_nz (by omega)
        have hc1 := eval_eq_zero_of_ne (w := w) (r := 2) (v := t₂.rootId)
          (st := ⟨mem, fun i => [nb, optRoot (some t₁), optRoot (some t₂), fuel, heap].getD i 0, pos⟩)
          (by simp [optRoot]) hr₂_nz (by omega)
        refine ⟨some (AuxTree.node mid t₁ R₂), tourAttachLeft s₁ mid t₁.rootId, .returned mid, st_fin, _,
          tour_runs_cond_false hc0 (tour_runs_cond_false hc1 hret_run), rfl, hmem_fin ▸ hn₃, hmem_fin ▸ (hfr₂.trans hfr₃), by simpa [optTrees] using hinv₃, hvals₃, ?_, hval_all, ?_, ?_⟩
        · simp only [optList, Option.elim, AuxTree.toList]
          rw [← hlist₂']; simp [AuxTree.toList, List.append_assoc]
        · intro u hu
          simp only [optList, Option.elim, List.mem_append, not_or] at hu
          have hun : u ∉ (AuxTree.node mid t₁ R₂).toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton, not_or]
            have hu₂ : u ∉ (AuxTree.node mid .leaf R₂).toList := by rw [hlist₂']; exact hu.2
            simp only [AuxTree.toList, List.nil_append, List.mem_append, List.mem_singleton, not_or] at hu₂
            exact ⟨⟨hu.1, hu₂.1⟩, hu₂.2⟩
          exact (hout₃ u hun).trans (hout₂ u hu.2)
        · have hphi3' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₃
          simp only [optTrees, Option.toList, List.cons_append, List.nil_append,
            TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_JOIN_AMORT, Expr.size] at hcost₂ hphi3' hc₃ hcfin ⊢
          nlinarith

/-- Amortized run theorem for `tourRotateFrontBody`: rotates `t` so `x` is first (`rotateToList x t.toList`). -/
theorem tourRotateFrontBody_runs {w nb cap heap fuel x pos : ℕ} {p : Program}
    (C : TourSplayOpsProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t : AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (t :: rest)) (hvals : TourValsOk w cap st)
    (hx : x ∈ t.toList) (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ t' s' o st' c,
      Runs w p ω (tourRotateFrontBody C.splay.splay C.detachLeft C.join)
        (startState [nb, x, fuel, heap] mem pos) o st' c ∧
      o.value = t'.rootId ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (t' :: rest) ∧
      TourValsOk w cap s' ∧
      t' ≠ .leaf ∧
      t'.toList = rotateNatList x t.toList ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ t.toList, s'.nodes u = st.nodes u) ∧
      c + TOUR_PHI_MULT * forestPhi (t' :: rest) ≤
        TOUR_PHI_MULT * forestPhi (t :: rest) + TOUR_SEQ_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hdep : t.depthOf x < fuel :=
    lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hx) (le_of_lt (lt_of_le_of_lt (hf.countNodes_le (by simp)) hfuel))
  have hf0 : TourForestInv cap st ([] ++ t :: rest) := hf
  obtain ⟨t₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, hout₁, hcost₁⟩ :=
    tourSplay_runs_amort (pos := pos) C.toTourSplayCoreProcs ω hnodes hf0 hvals hx hdep hfuelW hheap
  set s₁ := SplayState.splay tourPayload st fuel x
  cases ht₁c : t₁ with
  | leaf => exact absurd ht₁c hne₁
  | node xid L R =>
    have hxid : xid = x := by simpa [ht₁c, AuxTree.rootId] using hroot₁
    rcases hxid with rfl
    rw [ht₁c] at hinv₁ hlist₁ hcost₁
    have hx_cap : xid ≤ cap := (hinv₁.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList])).2
    obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hv₂, hn₂, hfr₂⟩, hc₂⟩ := tourDetachLeftBody_runs (pos := st₁.pos)
      C.toTourSplayCoreProcs ω hn₁ hinv₁.ptrOk hx_cap (heapOk_zero (heapOk_of_frame hheap hfr₁))
      (tourDetachLeft_sumOk hinv₁ hvals₁)
    obtain ⟨hinv₂, hout₂, hval₂, hphi₂⟩ := tourDetachLeft_preserves hinv₁
    set s₂ := tourDetachLeft s₁ xid
    have hvals₂ : TourValsOk w cap s₂ := ⟨hvals₁.1, fun u hu => by rw [hval₂ u hu]; exact hvals₁.2 u hu⟩
    let L? : Option AuxTree := if L = .leaf then none else some L
    have hL_root : o₂.value = optRoot L? := by
      have hsub := (hinv₁.treesInv (AuxTree.node xid L R) (by simp)).sub
      simp only [hv₂, hsub.1, ↓reduceIte, hsub.2.1]; cases L <;> simp [L?, optRoot, AuxTree.rootId]
    have hinv₂_perm : TourForestInv cap s₂ (optTrees (some (AuxTree.node xid .leaf R)) ++ optTrees L? ++ rest) := by
      refine (hinv₂.perm ?_).1
      cases L <;> simp only [L?, optTrees, Option.toList, reduceCtorEq, ↓reduceIte, List.nil_append, List.cons_append]
      · exact List.Perm.refl _
      · exact List.Perm.swap _ _ rest
    have hphi₂_eq : forestPhi (optTrees (some (AuxTree.node xid .leaf R)) ++ optTrees L? ++ rest) =
        forestPhi ([] ++ ((if L = .leaf then [] else [L]) ++ [AuxTree.node xid .leaf R]) ++ rest) := by
      refine forestPhi_perm ?_
      cases L <;> simp only [L?, optTrees, Option.toList, reduceCtorEq, ↓reduceIte, List.nil_append, List.cons_append]
      · exact List.Perm.refl _
      · exact List.Perm.swap _ _ rest
    obtain ⟨t'?, s₃, o₃, st₃, c₃, hrun₃, hv₃, hn₃, hfr₃, hinv₃, hvals₃, hlist₃, hval₃, hout₃, hcost₃⟩ :=
      tourJoinBody_runs (pos := st₂.pos) C ω hn₂ hinv₂_perm hvals₂ hfuel hfuelW
        (heapOk_of_frame hheap (hfr₁.trans hfr₂))
    cases t'? with
    | none => simp [optList, AuxTree.toList] at hlist₃
    | some t' =>
      have hne' : t' ≠ .leaf := hinv₃.nonEmpty t' (by simp [optTrees])
      have hrot_eq : t'.toList = rotateNatList xid t.toList := by
        have h1 : t'.toList = (xid :: R.toList) ++ L.toList := by
          have hLopt : optList L? = L.toList := by cases L <;> simp [L?, optList, AuxTree.toList]
          rw [hLopt] at hlist₃
          simpa [optList, AuxTree.toList] using hlist₃
        have h2 : t.toList = L.toList ++ xid :: R.toList := by rw [← hlist₁]; simp [AuxTree.toList]
        rw [h1, h2]
        have hx_nL : xid ∉ L.toList := (AuxTree.nodup_node_unfold (hinv₁.treesInv (AuxTree.node xid L R) (by simp)).nodup).2.1
        unfold rotateNatList
        have hidx : (L.toList ++ xid :: R.toList).idxOf xid = L.toList.length := by
          generalize hLs : L.toList = ls at hx_nL ⊢
          clear * - hx_nL
          induction ls with
          | nil => simp
          | cons a as ih =>
            have hax : a ≠ xid := fun h => hx_nL (by simp [h])
            simp [hax, ih (fun hm => hx_nL (by simp [hm]))]
        simp [hidx]
      obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf0 hx hdep
      have hval_all : ∀ u ≤ cap, (s₃.nodes u).val = (st.nodes u).val := by
        intro u hu; rw [hval₃ u hu, hval₂ u hu]; exact hval_sp u hu
      have hout_all : ∀ u ∉ t.toList, s₃.nodes u = st.nodes u := by
        intro u hu
        have hu1 : u ∉ (AuxTree.node xid L R).toList := by rwa [hlist₁]
        have hu3 : u ∉ optList (some (AuxTree.node xid .leaf R)) ++ optList L? := by
          intro hm; apply hu1
          have hLopt : optList L? = L.toList := by cases L <;> simp [L?, optList, AuxTree.toList]
          rw [hLopt] at hm
          simp only [optList, Option.elim, AuxTree.toList, List.nil_append, List.mem_append,
            List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
          tauto
        exact (hout₃ u hu3).trans ((hout₂ u hu1).trans (hout₁ u hu))
      have hbody_run : ∃ st_fin c_fin, st_fin.mem = st₃.mem ∧ c_fin ≤ c₁ + c₂ + c₃ + 30 ∧
          Runs w p ω (tourRotateFrontBody C.splay.splay C.detachLeft C.join)
            (startState [nb, xid, fuel, heap] mem pos) (.returned t'.rootId) st_fin c_fin := by
        unfold tourRotateFrontBody; rw [startState]
        set s0 : State := ⟨mem, fun i => [nb, xid, fuel, heap].getD i 0, pos⟩
        set s1_st : State := { st₁ with regs := Function.update s0.regs 4 o₁.value }
        set s2_st : State := { st₂ with regs := Function.update s1_st.regs 4 o₂.value }
        set s3_st : State := { st₃ with regs := Function.update s2_st.regs 5 o₃.value }
        have hc1 := runs_call_regs4 4 0 1 2 3 (st := s0) C.splay.splay_body (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) hrun₁
        have hc2 := runs_call_regs3 4 0 1 3 (st := s1_st) C.detachLeft_body (by simp [s1_st, s0]) (by simp [s1_st, s0]) (by simp [s1_st, s0]) hrun₂
        have hc3 := runs_call_regs5 5 0 1 4 2 3 (st := s2_st) C.join_body (by simp [s2_st, s1_st, s0]) (by simp [s2_st, s1_st, s0, optRoot, AuxTree.rootId]) (by simp [s2_st, hL_root]) (by simp [s2_st, s1_st, s0]) (by simp [s2_st, s1_st, s0]) hrun₃
        have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s3_st) (r := 5) (v := t'.rootId) (by simp [s3_st, hv₃, optRoot])
        exact ⟨s3_st, _, rfl, by omega, tour_runs_seq_normal hc1 (tour_runs_seq_normal hc2 (tour_runs_seq_normal hc3 hret))⟩
      obtain ⟨st_fin, c_fin, hmem_fin, hcfin, hbody_run⟩ := hbody_run
      refine ⟨t', s₃, .returned t'.rootId, st_fin, c_fin, hbody_run, rfl, hmem_fin ▸ hn₃, hmem_fin ▸ (hfr₁.trans (hfr₂.trans hfr₃)),
        by simpa [optTrees] using hinv₃, hvals₃, hne', hrot_eq, hval_all, hout_all, ?_⟩
      have hphi2' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₂
      rw [hphi₂_eq] at hcost₃
      simp only [optTrees, Option.toList, List.nil_append, List.cons_append,
        TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_JOIN_AMORT, TOUR_SEQ_AMORT] at hcost₁ hcost₃ hphi2' hc₂ hcfin ⊢
      nlinarith

/-- Amortized run theorem for `tourDeleteNodeBody`: removes `x` from `t` and leaves
`AuxTree.node x .leaf .leaf` as a zero-potential singleton in the forest. -/
theorem tourDeleteNodeBody_runs {w nb cap heap fuel x pos : ℕ} {p : Program}
    (C : TourSplayOpsProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t : AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (t :: rest)) (hvals : TourValsOk w cap st)
    (hx : x ∈ t.toList) (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ t'? s' o st' c,
      Runs w p ω (tourDeleteNodeBody C.splay.splay C.detachLeft C.detachRight C.join)
        (startState [nb, x, fuel, heap] mem pos) o st' c ∧
      o.value = optRoot t'? ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (AuxTree.node x .leaf .leaf :: optTrees t'? ++ rest) ∧
      TourValsOk w cap s' ∧
      optList t'? = t.toList.erase x ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ t.toList, s'.nodes u = st.nodes u) ∧
      c + TOUR_PHI_MULT * forestPhi (AuxTree.node x .leaf .leaf :: optTrees t'? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (t :: rest) + TOUR_SEQ_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hdep : t.depthOf x < fuel :=
    lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hx) (le_of_lt (lt_of_le_of_lt (hf.countNodes_le (by simp)) hfuel))
  have hf0 : TourForestInv cap st ([] ++ t :: rest) := hf
  obtain ⟨t₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, hout₁, hcost₁⟩ :=
    tourSplay_runs_amort (pos := pos) C.toTourSplayCoreProcs ω hnodes hf0 hvals hx hdep hfuelW hheap
  set s₁ := SplayState.splay tourPayload st fuel x
  cases ht₁c : t₁ with
  | leaf => exact absurd ht₁c hne₁
  | node xid L R =>
    have hxid : xid = x := by simpa [ht₁c, AuxTree.rootId] using hroot₁
    rcases hxid with rfl
    rw [ht₁c] at hinv₁ hlist₁ hcost₁
    have hx_cap : xid ≤ cap := (hinv₁.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList])).2
    have hsub₁ := (hinv₁.treesInv (AuxTree.node xid L R) (by simp)).sub
    obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hv₂, hn₂, hfr₂⟩, hc₂⟩ := tourDetachLeftBody_runs (pos := st₁.pos)
      C.toTourSplayCoreProcs ω hn₁ hinv₁.ptrOk hx_cap (heapOk_zero (heapOk_of_frame hheap hfr₁))
      (tourDetachLeft_sumOk hinv₁ hvals₁)
    obtain ⟨hinv₂, hout₂, hval₂, hphi₂⟩ := tourDetachLeft_preserves hinv₁
    set s₂ := tourDetachLeft s₁ xid
    have hvals₂ : TourValsOk w cap s₂ := ⟨hvals₁.1, fun u hu => by rw [hval₂ u hu]; exact hvals₁.2 u hu⟩
    let L? : Option AuxTree := if L = .leaf then none else some L
    let R? : Option AuxTree := if R = .leaf then none else some R
    have hL_root : o₂.value = optRoot L? := by
      simp only [hv₂, hsub₁.1, ↓reduceIte, hsub₁.2.1]; cases L <;> simp [L?, optRoot, AuxTree.rootId]
    have hinv₂' : TourForestInv cap s₂ (optTrees L? ++ AuxTree.node xid .leaf R :: rest) := by
      cases L <;> simpa [L?, optTrees] using hinv₂
    have hsub₂ := (hinv₂'.treesInv (AuxTree.node xid .leaf R) (by simp)).sub
    obtain ⟨o₃, st₃, c₃, hrun₃, ⟨hv₃, hn₃, hfr₃⟩, hc₃⟩ := tourDetachRightBody_runs (pos := st₂.pos)
      C.toTourSplayCoreProcs ω hn₂ hinv₂'.ptrOk hx_cap
      (heapOk_zero (heapOk_of_frame hheap (hfr₁.trans hfr₂))) (tourDetachRight_sumOk hinv₂' hvals₂)
    obtain ⟨hinv₃, hout₃, hval₃, hphi₃⟩ := tourDetachRight_preserves hinv₂'
    set s₃ := tourDetachRight s₂ xid
    have hvals₃ : TourValsOk w cap s₃ := ⟨hvals₂.1, fun u hu => by rw [hval₃ u hu]; exact hvals₂.2 u hu⟩
    have hR_root : o₃.value = optRoot R? := by
      simp only [hv₃, hsub₁.1, ↓reduceIte, hsub₂.2.2.1]; cases R <;> simp [R?, optRoot, AuxTree.rootId]
    have hperm₃ : (optTrees L? ++ ([AuxTree.node xid .leaf .leaf] ++ (if R = .leaf then [] else [R])) ++ rest).Perm
        (optTrees L? ++ optTrees R? ++ (AuxTree.node xid .leaf .leaf :: rest)) := by
      cases R <;> simp only [R?, optTrees, Option.toList, List.append_nil, List.nil_append, List.cons_append,
        List.append_assoc, reduceCtorEq, ↓reduceIte]
      · exact List.Perm.refl _
      · exact List.Perm.append_left _ (List.Perm.swap _ _ rest)
    have hinv₃' : TourForestInv cap s₃ (optTrees L? ++ optTrees R? ++ (AuxTree.node xid .leaf .leaf :: rest)) :=
      (hinv₃.perm hperm₃).1
    obtain ⟨t'?, s₄, o₄, st₄, c₄, hrun₄, hv₄, hn₄, hfr₄, hinv₄, hvals₄, hlist₄, hval₄, hout₄, hcost₄⟩ :=
      tourJoinBody_runs (pos := st₃.pos) C ω hn₃ hinv₃' hvals₃ hfuel hfuelW
        (heapOk_of_frame hheap (hfr₁.trans (hfr₂.trans hfr₃)))
    have hperm₄ : (optTrees t'? ++ (AuxTree.node xid .leaf .leaf :: rest)).Perm
        (AuxTree.node xid .leaf .leaf :: optTrees t'? ++ rest) := by
      cases t'? <;> simp [optTrees]
      exact List.Perm.swap _ _ rest
    have herase : optList t'? = t.toList.erase xid := by
      have h1 : optList t'? = L.toList ++ R.toList := by
        have hL : optList L? = L.toList := by cases L <;> simp [L?, optList, AuxTree.toList]
        have hR : optList R? = R.toList := by cases R <;> simp [R?, optList, AuxTree.toList]
        rw [hlist₄, hL, hR]
      have h2 : t.toList = L.toList ++ xid :: R.toList := by rw [← hlist₁]; simp [AuxTree.toList]
      have hx_nL : xid ∉ L.toList := (AuxTree.nodup_node_unfold (hinv₁.treesInv (AuxTree.node xid L R) (by simp)).nodup).2.1
      rw [h1, h2]
      generalize hLs : L.toList = ls at hx_nL ⊢
      clear * - hx_nL
      induction ls with
      | nil => simp
      | cons a as ih =>
        have hax : a ≠ xid := fun h => hx_nL (by simp [h])
        simp [hax, ih (fun hm => hx_nL (by simp [hm]))]
    obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf0 hx hdep
    have hval_all : ∀ u ≤ cap, (s₄.nodes u).val = (st.nodes u).val := by
      intro u hu; rw [hval₄ u hu, hval₃ u hu, hval₂ u hu]; exact hval_sp u hu
    have hout_all : ∀ u ∉ t.toList, s₄.nodes u = st.nodes u := by
      intro u hu
      have hu1 : u ∉ (AuxTree.node xid L R).toList := by rwa [hlist₁]
      have hu2 : u ∉ (AuxTree.node xid .leaf R).toList := fun hm => hu1 (by
        simp only [AuxTree.toList, List.nil_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hm ⊢
        tauto)
      have hu4 : u ∉ optList L? ++ optList R? := fun hm => hu1 (by
        have hL : optList L? = L.toList := by cases L <;> simp [L?, optList, AuxTree.toList]
        have hR : optList R? = R.toList := by cases R <;> simp [R?, optList, AuxTree.toList]
        rw [hL, hR] at hm
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hm ⊢
        rcases hm with h1 | h2; exact Or.inl (Or.inl h1); exact Or.inr h2)
      exact (hout₄ u hu4).trans ((hout₃ u hu2).trans ((hout₂ u hu1).trans (hout₁ u hu)))
    have hbody_run : ∃ st_fin c_fin, st_fin.mem = st₄.mem ∧ c_fin ≤ c₁ + c₂ + c₃ + c₄ + 35 ∧
        Runs w p ω (tourDeleteNodeBody C.splay.splay C.detachLeft C.detachRight C.join)
          (startState [nb, xid, fuel, heap] mem pos) (.returned (optRoot t'?)) st_fin c_fin := by
      unfold tourDeleteNodeBody; rw [startState]
      set s0 : State := ⟨mem, fun i => [nb, xid, fuel, heap].getD i 0, pos⟩
      set s1_st : State := { st₁ with regs := Function.update s0.regs 4 o₁.value }
      set s2_st : State := { st₂ with regs := Function.update s1_st.regs 4 o₂.value }
      set s3_st : State := { st₃ with regs := Function.update s2_st.regs 5 o₃.value }
      set s4_st : State := { st₄ with regs := Function.update s3_st.regs 6 o₄.value }
      have hc1 := runs_call_regs4 4 0 1 2 3 (st := s0) C.splay.splay_body (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) hrun₁
      have hc2 := runs_call_regs3 4 0 1 3 (st := s1_st) C.detachLeft_body (by simp [s1_st, s0]) (by simp [s1_st, s0]) (by simp [s1_st, s0]) hrun₂
      have hc3 := runs_call_regs3 5 0 1 3 (st := s2_st) C.detachRight_body (by simp [s2_st, s1_st, s0]) (by simp [s2_st, s1_st, s0]) (by simp [s2_st, s1_st, s0]) hrun₃
      have hc4 := runs_call_regs5 6 0 4 5 2 3 (st := s3_st) C.join_body (by simp [s3_st, s2_st, s1_st, s0]) (by simp [s3_st, s2_st, hL_root]) (by simp [s3_st, hR_root]) (by simp [s3_st, s2_st, s1_st, s0]) (by simp [s3_st, s2_st, s1_st, s0]) hrun₄
      have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s4_st) (r := 6) (v := optRoot t'?) (by simp [s4_st, hv₄])
      exact ⟨s4_st, _, rfl, by omega, tour_runs_seq_normal hc1 (tour_runs_seq_normal hc2 (tour_runs_seq_normal hc3 (tour_runs_seq_normal hc4 hret)))⟩
    obtain ⟨st_fin, c_fin, hmem_fin, hcfin, hbody_run⟩ := hbody_run
    refine ⟨t'?, s₄, .returned (optRoot t'?), st_fin, c_fin, hbody_run, rfl, hmem_fin ▸ hn₄,
      hmem_fin ▸ (hfr₁.trans (hfr₂.trans (hfr₃.trans hfr₄))), (hinv₄.perm hperm₄).1, hvals₄, herase, hval_all, hout_all, ?_⟩
    have hphi2' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₂
    have hphi3' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₃
    have hpeq3 := forestPhi_perm hperm₃
    have hpeq4 := forestPhi_perm hperm₄
    have hphi2_bridge : forestPhi (optTrees L? ++ AuxTree.node xid .leaf R :: rest) =
        forestPhi ([] ++ ((if L = .leaf then [] else [L]) ++ [AuxTree.node xid .leaf R]) ++ rest) := by
      cases L <;> simp [L?, optTrees]
    rw [← hpeq4]
    rw [← hpeq3] at hcost₄
    rw [hphi2_bridge] at hphi3'
    simp only [List.nil_append, TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_JOIN_AMORT, TOUR_SEQ_AMORT] at hcost₁ hcost₄ hphi2' hphi3' hc₂ hc₃ hcfin ⊢
    nlinarith

end MinCostFlow.SparseCore.Program
