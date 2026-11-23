module

public import MinCostFlow.LowStretch.ProgClusterNext
public import MinCostFlow.LowStretch.ProgChildSpec

/-!
# The tree of the first run, and the highway of a regular petal

After the first run of Dijkstra (and `hwFix`) every node `v` other than the node of the center has
a parent `NXT[v]`, the pair `PP[v]` of its parent arc, the end `PA[v]` of this pair in `v` and the
end `PB[v]` in the parent (`PW.Tree`). Along each parent arc the distance to the center drops by the
positive length of the pair. So the path of parents from any node reaches the node of the center
(`Tree.reach`), and the steps along it (`stp`) split a highway (`Tree.hwDec`). This is the highway
of a regular petal.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ}

/-- The addresses of the arrays of the tree: pair, flag, near end and far end of the parent arc
of each node, and the distance to the center of each node. -/
structure TA where
  PP : ℕ
  PF : ℕ
  PA : ℕ
  PB : ℕ
  FD : ℕ

/-- The node of the center. -/
noncomputable def root (W : PW) : ℕ := W.sv W.c.x0

/-- The node reached from `v` after `i` steps of `NXT`. -/
def pe (W : PW) (mem : ℕ → ℕ) (v i : ℕ) : ℕ := parEnd mem W.NXT v i

theorem pe_zero (v : ℕ) : W.pe mem v 0 = v := rfl

theorem pe_succ (v i : ℕ) : W.pe mem v (i + 1) = W.pe mem (mem (W.NXT + v)) i := by
  unfold pe parEnd; rw [Function.iterate_succ_apply]

theorem pe_succ' (v i : ℕ) : W.pe mem v (i + 1) = mem (W.NXT + W.pe mem v i) := by
  unfold pe parEnd; rw [Function.iterate_succ_apply']

/-- **The tree of the first run**, in memory. -/
structure Tree (W : PW) (A : TA) (mem : ℕ → ℕ) : Prop where
  root : mem (W.NXT + W.root) = W.s
  edge : ∀ v < W.s, v ≠ W.root →
    mem (W.NXT + v) < W.s ∧ mem (A.PA + v) ∈ W.c.X ∧ W.sv (mem (A.PA + v)) = v ∧
    mem (A.PB + v) ∈ W.c.X ∧ W.sv (mem (A.PB + v)) = mem (W.NXT + v) ∧
    W.G.Joins (mem (A.PP + v)) (mem (A.PA + v)) (mem (A.PB + v)) ∧
    W.c.d W.G W.c.x0 (mem (A.PA + v)) =
      W.c.d W.G W.c.x0 (mem (A.PB + v)) + W.c.len W.G (mem (A.PP + v)) ∧
    0 < W.c.len W.G (mem (A.PP + v)) ∧
    mem (W.L.CS + W.slotA mem v) = W.c.len W.G (mem (A.PP + v)) ∧
    mem (A.PF + v) = if mem (A.PP + v) ∈ W.c.half then 1 else 0
  fd : ∀ a ∈ W.c.X, mem (A.FD + W.sv a) = W.c.d W.G W.c.x0 a

/-- The tree depends only on its arrays, `NXT`, the ranges and the costs. -/
theorem Tree.congr {A : TA} (hT : W.Tree A mem) {mem' : ℕ → ℕ}
    (h1 : ∀ v < W.s, mem' (W.NXT + v) = mem (W.NXT + v) ∧ mem' (W.L.HI + v) = mem (W.L.HI + v) ∧
      mem' (A.PP + v) = mem (A.PP + v) ∧ mem' (A.PF + v) = mem (A.PF + v) ∧
      mem' (A.PA + v) = mem (A.PA + v) ∧ mem' (A.PB + v) = mem (A.PB + v) ∧
      mem' (A.FD + v) = mem (A.FD + v))
    (h2 : ∀ v < W.s, mem' (W.L.CS + W.slotA mem v) = mem (W.L.CS + W.slotA mem v))
    (hroot : W.root < W.s) (hsv : ∀ a ∈ W.c.X, W.sv a < W.s) : W.Tree A mem' where
  root := by rw [(h1 _ hroot).1]; exact hT.root
  edge v hv hr := by
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hT.edge v hv hr
    obtain ⟨f1, f2, f3, f4, f5, f6, -⟩ := h1 v hv
    have hs : W.slotA mem' v = W.slotA mem v := by unfold slotA; rw [f2]
    rw [f1, f3, f4, f5, f6, hs, h2 v hv]
    exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩
  fd a ha := by rw [(h1 _ (hsv a ha)).2.2.2.2.2.2]; exact hT.fd a ha

/-! ### Nodes and vertices -/

/-- Every node holds a vertex of the cluster. -/
theorem Ok.sv_surj (h : W.Ok w mem) {u : ℕ} (hu : u < W.s) : ∃ a ∈ W.c.X, W.sv a = u := by
  have hr := h.hrec
  have hk : W.R.nodes[u] ∈ W.R.nodes := List.getElem_mem hu
  obtain ⟨v, hv, hvk⟩ := KT.exists_leaf hr.tree _ (hr.node_lt _ hk)
  have htop := hr.node_top _ hk v hv hvk
  refine ⟨v, (hr.X_iff v).mpr ⟨hv, by rw [htop]; exact hk⟩, ?_⟩
  show W.R.nodes.idxOf (W.T.top W.c.θ v) = u
  rw [htop]; exact List.Nodup.idxOf_getElem hr.nodup u hu

theorem Ok.root_lt (h : W.Ok w mem) : W.root < W.s := h.sv_lt h.conn.1

variable {A : TA}

theorem Tree.fdA (hT : W.Tree A mem) {v : ℕ} (hv : v < W.s) (hr : v ≠ W.root) :
    mem (A.FD + v) = W.c.d W.G W.c.x0 (mem (A.PA + v)) := by
  obtain ⟨-, e2, e3, -⟩ := hT.edge v hv hr
  have := hT.fd _ e2
  rwa [e3] at this

theorem Tree.fdB (hT : W.Tree A mem) {v : ℕ} (hv : v < W.s) (hr : v ≠ W.root) :
    mem (A.FD + mem (W.NXT + v)) = W.c.d W.G W.c.x0 (mem (A.PB + v)) := by
  obtain ⟨-, -, -, e4, e5, -⟩ := hT.edge v hv hr
  have := hT.fd _ e4
  rwa [e5] at this

/-- Along a parent arc the distance of the node drops. -/
theorem Tree.fd_lt (hT : W.Tree A mem) {v : ℕ} (hv : v < W.s) (hr : v ≠ W.root) :
    mem (A.FD + mem (W.NXT + v)) < mem (A.FD + v) := by
  obtain ⟨-, -, -, -, -, -, e7, e8, -⟩ := hT.edge v hv hr
  rw [hT.fdA hv hr, hT.fdB hv hr]; omega

/-- **The path of parents reaches the node of the center.** -/
theorem Tree.reach (hT : W.Tree A mem) {v : ℕ} (hv : v < W.s) :
    ∃ n, W.pe mem v n = W.root ∧ ∀ i < n, W.pe mem v i ≠ W.root ∧ W.pe mem v i < W.s := by
  suffices ∀ D, ∀ v < W.s, mem (A.FD + v) ≤ D →
      ∃ n, W.pe mem v n = W.root ∧ ∀ i < n, W.pe mem v i ≠ W.root ∧ W.pe mem v i < W.s from
    this _ v hv le_rfl
  intro D
  induction D with
  | zero =>
    intro v hv hD
    by_cases hr : v = W.root
    · exact ⟨0, hr, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · have := hT.fd_lt hv hr; omega
  | succ D ih =>
    intro v hv hD
    by_cases hr : v = W.root
    · exact ⟨0, hr, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · have hlt := hT.fd_lt hv hr
      obtain ⟨n, h1, h2⟩ := ih _ (hT.edge v hv hr).1 (by omega)
      refine ⟨n + 1, by rw [pe_succ]; exact h1, fun i hi => ?_⟩
      cases i with
      | zero => exact ⟨hr, hv⟩
      | succ i => rw [pe_succ]; exact h2 i (by omega)

/-- The path facts of a node: `n` steps lead to the node of the center, through other nodes. -/
def Path (W : PW) (mem : ℕ → ℕ) (v n : ℕ) : Prop :=
  W.pe mem v n = W.root ∧ ∀ i < n, W.pe mem v i ≠ W.root ∧ W.pe mem v i < W.s

theorem Path.succ {v n : ℕ} (h : W.Path mem v (n + 1)) : W.Path mem (mem (W.NXT + v)) n :=
  ⟨by rw [← pe_succ]; exact h.1, fun i hi => by rw [← pe_succ]; exact h.2 (i + 1) (by omega)⟩

theorem Path.lt (hr : W.root < W.s) {v n : ℕ} (h : W.Path mem v n) {i : ℕ} (hi : i ≤ n) :
    W.pe mem v i < W.s := by
  rcases Nat.lt_or_ge i n with h1 | h1
  · exact (h.2 i h1).2
  · rw [show i = n by omega, h.1]; exact hr

/-! ### The steps of the path -/

/-- The steps of the path of parents from `v`: `n` parent arcs, as (pair, near end, far end). -/
def stp (W : PW) (A : TA) (mem : ℕ → ℕ) (v n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).map fun i =>
    (mem (A.PP + W.pe mem v i), mem (A.PA + W.pe mem v i), mem (A.PB + W.pe mem v i))

theorem stp_length (v n : ℕ) : (W.stp A mem v n).length = n := by simp [stp]

theorem stp_succ (v n : ℕ) : W.stp A mem v (n + 1) =
    (mem (A.PP + v), mem (A.PA + v), mem (A.PB + v)) :: W.stp A mem (mem (W.NXT + v)) n := by
  unfold stp
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1

theorem stp_getElem {v n i : ℕ} (hi : i < (W.stp A mem v n).length) :
    (W.stp A mem v n)[i] =
      (mem (A.PP + W.pe mem v i), mem (A.PA + W.pe mem v i), mem (A.PB + W.pe mem v i)) := by
  simp [stp]

/-- **The steps split a highway** from any vertex `e` of the node `v`. -/
theorem Tree.hwDec (h : W.Ok w mem) (hT : W.Tree A mem) :
    ∀ n v e, W.Path mem v n → e ∈ W.c.X → W.sv e = v → ∃ hw, W.c.HwDec W.G e (W.stp A mem v n) hw := by
  intro n
  induction n with
  | zero =>
    intro v e hp he hsv
    have hl : W.c.LConn W.G e W.c.x0 := (h.sv_iff he h.conn.1).mp (by rw [hsv]; exact hp.1)
    obtain ⟨l, hl⟩ := hl
    exact ⟨l, Cl.HwDec.nil hl⟩
  | succ n ih =>
    intro v e hp he hsv
    have hr : v ≠ W.root := (hp.2 0 (by omega)).1
    have hv : v < W.s := (hp.2 0 (by omega)).2
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, -⟩ := hT.edge v hv hr
    obtain ⟨hw, hd⟩ := ih _ _ hp.succ e4 e5
    have hl : W.c.LConn W.G e (mem (A.PA + v)) := (h.sv_iff he e2).mp (by rw [hsv, e3])
    obtain ⟨l, hl⟩ := hl
    rw [stp_succ]
    exact ⟨l ++ mem (A.PP + v) :: hw, Cl.HwDec.cons hl e6 e4 e7 hd⟩

/-- The highway nodes of the steps are the nodes of the path. -/
theorem Tree.Hl_eq (hT : W.Tree A mem) {e v n : ℕ} (hp : W.Path mem v n) (hsv : W.sv e = v) :
    W.Hl e (W.stp A mem v n) = (List.range (n + 1)).map (W.pe mem v) := by
  unfold Hl
  rw [List.range_succ_eq_map, List.map_cons, hsv, pe_zero]
  congr 1
  unfold stp
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  obtain ⟨-, -, -, -, e5, -⟩ := hT.edge _ (hp.2 i hi').2 (hp.2 i hi').1
  simp only [Function.comp_apply]
  rw [e5, pe_succ']

/-- The entries of the steps lie in the nodes of the path. -/
theorem Tree.ent (hT : W.Tree A mem) {e v n : ℕ} (hp : W.Path mem v n) (he : e ∈ W.c.X)
    (hsv : W.sv e = v) {i : ℕ} (hi : i ≤ n) :
    Cl.stEnt e (W.stp A mem v n) i ∈ W.c.X ∧ W.sv (Cl.stEnt e (W.stp A mem v n) i) = W.pe mem v i := by
  cases i with
  | zero => exact ⟨he, hsv⟩
  | succ i =>
    have hi' : i < n := by omega
    obtain ⟨-, -, -, e4, e5, -⟩ := hT.edge _ (hp.2 i hi').2 (hp.2 i hi').1
    have : Cl.stEnt e (W.stp A mem v n) (i + 1) = mem (A.PB + W.pe mem v i) := by
      unfold Cl.stEnt
      rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp [stp_length]; omega)]
      simp [stp]
    rw [this, pe_succ']
    exact ⟨e4, e5⟩

/-- The nodes of the path are distinct: their distances drop. -/
theorem Tree.path_nodup (hT : W.Tree A mem) {v n : ℕ} (hp : W.Path mem v n) :
    ((List.range (n + 1)).map (W.pe mem v)).Nodup := by
  have hlt : ∀ i j, i < j → j ≤ n → mem (A.FD + W.pe mem v j) < mem (A.FD + W.pe mem v i) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hj' : j < n := by omega
      have := hT.fd_lt (hp.2 j hj').2 (hp.2 j hj').1
      rw [← pe_succ' (W := W) (mem := mem) v j] at this
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h1 | h1
      · exact lt_trans this (ih h1 (by omega))
      · subst h1; exact this
  rw [List.nodup_iff_injective_get]
  intro a b hab
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range] at hab
  have ha := a.isLt; have hb := b.isLt
  simp only [List.length_map, List.length_range] at ha hb
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · have := hlt _ _ h1 (by omega); rw [hab] at this; omega
  · have := hlt _ _ h1 (by omega); rw [hab] at this; omega

end PW

end MinCostFlow.LowStretch
