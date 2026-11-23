module

public import MinCostFlow.LowStretch.ProgClusterSet12
public import MinCostFlow.LowStretch.ProgClusterLoop
public import MinCostFlow.LowStretch.ProgClusterSet6

/-!
# The setup of a cluster: the first state of the petals

Before any petal, every node `v < s` is allowed and the dummy node `s` is not. Then the parent of
every node is allowed (`PW.Cone.init`), the remaining vertices are all of `X`
(`PW.Y_init`, which is `Z` with no petal), and the allowed nodes are `0, …, s - 1`
(`PW.Nodes_init`). These are the fields `cone`, `Y`, `room` and `kle` of the first `LInv`.
The tree `PW.Tree` comes from the tree of parents after `hwFix` and its copy `NXT`
(`PW.PTree.tree`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PW

variable {W : PW} {A : TA} {mem : ℕ → ℕ}

/-- At the start the cone holds: every node is allowed. -/
theorem Cone.init (hT : W.Tree A mem) (hok : ∀ v < W.s, mem (W.L.OK + v) = W.L.os) :
    W.Cone mem :=
  fun v hv _ hr => hok _ (hT.edge v hv hr).1

/-- At the start the remaining vertices are all of `X`. -/
theorem Y_init {w : ℕ} (h : W.Ok w mem) (hok : ∀ v < W.s, mem (W.L.OK + v) = W.L.os) (sp : Bool) :
    W.Y mem = W.c.Z W.G ⟨sp, []⟩ 0 := by
  show W.c.X.filter _ = W.c.X
  exact Finset.filter_true_of_mem fun a ha => hok _ (h.sv_lt ha)

/-- At the start the allowed nodes are the nodes `0, …, s - 1`. -/
theorem Nodes_init {w : ℕ} (h : W.Ok w mem) (hok : ∀ v < W.s, mem (W.L.OK + v) = W.L.os) :
    W.Nodes mem = Finset.range W.s := by
  unfold Nodes
  rw [h.hNN]
  ext v
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hv, he⟩
    by_contra hge
    have : v = W.s := by omega
    subst this
    exact h.sS he
  · intro hv
    exact ⟨by omega, hok v hv⟩

/-- At the start there are `s` allowed nodes. -/
theorem card_init {w : ℕ} (h : W.Ok w mem) (hok : ∀ v < W.s, mem (W.L.OK + v) = W.L.os) :
    (W.Nodes mem).card = W.s := by
  rw [Nodes_init h hok, Finset.card_range]

/-- **The tree of the petal searches**, from the tree of parents at `PAR` (`PTree`), its copy at
`NXT`, the slot costs, and the distances at `FD`. -/
theorem PTree.tree {PAR SC : ℕ}
    (hP : PTree W.T W.G W.c W.R W.s W.root PAR A.PP A.PF A.PA A.PB SC mem)
    (hcp : ∀ v < W.s, mem (W.NXT + v) = mem (PAR + v))
    (hsc : ∀ v < W.s, v ≠ W.root → mem (W.L.CS + W.slotA mem v) = mem (SC + v))
    (hfd : ∀ a ∈ W.c.X, mem (A.FD + W.sv a) = W.c.d W.G W.c.x0 a) (hr : W.root < W.s) :
    W.Tree A mem where
  root := by rw [hcp _ hr]; exact hP.root
  edge v hv hvr := by
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hP.edge v hv hvr
    rw [hcp v hv, hsc v hv hvr]
    exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩
  fd := hfd

end PW

end MinCostFlow.LowStretch
