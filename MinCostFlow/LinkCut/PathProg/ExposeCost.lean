module

public import MinCostFlow.LinkCut.PathProg.SplayCost
public import MinCostFlow.LinkCut.Gen.Expose
public import MinCostFlow.LinkCut.ForestExposeSpec
public import MinCostFlow.LinkCut.ForestModelLink

/-!
# The cost of an expose against the model's counts

The model `lctExposeCost` counts the half rotations of its splays and the splices of its loop.
The program `exposeBody` costs at most `exposeRate S` per counted unit, plus one more
(`exposeCost_le`). The proof walks the expose loop as `lctExposeLoop_spec` does: at each splice
the path parent lies in a valid tree, so its splay costs at most `splayRate S` per half rotation
(`splayCost_le`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen SplayState

variable {α σ τ : Type*}

/-- The cost of one counted unit of an expose. -/
def exposeRate {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) : ℕ :=
  splayRate S + 2 * S.cost + 1000

theorem tree_count_le {P : LctPayload α σ τ} {st : LctState α σ τ} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d) {t : AuxTree} (ht : t ∈ trees) :
    t.countNodes ≤ 2 * st.n := by
  have h1 := tree_length_le_active ht
  have h2 := active_length_le_two_mul W.activeNodup W.activeValid
  rw [AuxTree.length_toList] at h1
  omega

/-- A splay of an active node costs at most `splayRate S` per half rotation, plus one. -/
theorem splayCost_active {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (hL : P.Laws) (S : PayloadSteps w p P Lay ok)
    {st : LctState α σ τ} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith P st trees fl d) {t : AuxTree} {x : ℕ} (ht : t ∈ trees) (hx : x ∈ t.toList) :
    splayCost S st.splay (2 * st.n + 1) x ≤
      (splayDepth st.splay (2 * st.n + 1) x / 2 + 1) * splayRate S := by
  have := depthOf_lt_countNodes hx
  have := tree_count_le W ht
  exact splayCost_le hL S (W.treesInv t ht) hx (by omega)

private theorem listLast0_mem : ∀ {l : List ℕ}, l ≠ [] → listLast0 l ∈ l
  | [], h => absurd rfl h
  | [x], _ => by simp [listLast0]
  | x :: y :: l, _ => by
    have := listLast0_mem (l := y :: l) (by simp)
    simp only [listLast0] at this ⊢
    exact List.mem_cons_of_mem _ this

/-- The splices of an expose: each costs at most `splayRate S` per half rotation, plus
`exposeRate S`. -/
theorem exposeLoopCost_le {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (hL : P.Laws) (S : PayloadSteps w p P Lay ok) :
    ∀ (fuel : ℕ) {st : LctState α σ τ} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
      {t_last : AuxTree}, LctInvWith P st trees fl d → t_last ∈ trees →
      exposeLoopCost S st fuel t_last.rootId ≤
        splayRate S * (lctExposeLoop P st fuel t_last.rootId).2.2.1 +
          exposeRate S * (lctExposeLoop P st fuel t_last.rootId).2.2.2
  | 0, _, _, _, _, _, _, _ => by simp [exposeLoopCost]
  | fuel + 1, st, trees, fl, d, t_last, W, ht => by
    by_cases hp : (st.splay.nodes t_last.rootId).ppar = 0
    · simp [exposeLoopCost, hp]
    have hp_act := W.pparActive t_last ht hp
    obtain ⟨tp, htp, hp_tp⟩ := List.mem_flatMap.mp hp_act
    have hsc := splayCost_active hL S W htp hp_tp
    have hv_mem : listLast0 (treeIds P st.splay t_last) ∈ t_last.toList :=
      (treeIds_perm st.splay t_last).mem_iff.mp (listLast0_mem (treeIds_ne_nil
        (W.treesNonEmpty t_last ht)))
    obtain ⟨trees', L_next, ht_next, -, W', -⟩ := lctExposeStep_spec hL W ht rfl hv_mem rfl hp
      (inducedSubPar P st.splay trees) (fun _ => rfl) _ (List.Perm.refl _)
    have ih := exposeLoopCost_le hL S fuel W' ht_next
    have hrt : (AuxTree.node (lctExposeStep P st t_last.rootId).2.1 L_next t_last).rootId =
        (lctExposeStep P st t_last.rootId).2.1 := rfl
    rw [hrt] at ih
    generalize t_last.rootId = last at *
    have hloop : lctExposeLoop P st (fuel + 1) last =
        let r1 := lctExposeStep P st last
        let r2 := lctExposeLoop P r1.1 fuel r1.2.1
        (r2.1, r2.2.1, r1.2.2 + r2.2.2.1, 1 + r2.2.2.2) := by
      rw [lctExposeLoop]; simp [hp]
    rw [hloop]
    simp only [exposeLoopCost, hp, ite_false]
    have hstep2 : (lctExposeStep P st last).2.2 =
        splayDepth st.splay (2 * st.n + 1) (st.splay.nodes last).ppar / 2 := rfl
    have hstep1 : (lctExposeStep P st last).2.1 = (st.splay.nodes last).ppar :=
      rfl
    rw [hstep2, hstep1]
    rw [hstep1] at ih
    unfold exposeRate at ih ⊢
    nlinarith

/-- An expose of an active node costs at most `exposeRate S` per counted unit, plus one. -/
theorem exposeCost_le {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (hL : P.Laws) (S : PayloadSteps w p P Lay ok)
    {st : LctState α σ τ} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
    (W : LctInvWith P st trees fl d) {v : ℕ} (hv : v ∈ trees.flatMap AuxTree.toList) :
    exposeCost S st v ≤
      exposeRate S * ((lctExposeCost P st v).2.1 + (lctExposeCost P st v).2.2 + 1) := by
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp hv
  have h1 := splayCost_active hL S W htv hvt
  obtain ⟨trees1, L1, ht1_mem, hv1, hW1, -, -, -, hlast1, -⟩ := lctExposeInit_spec hL W htv hvt
  have h2 := exposeLoopCost_le hL S (2 * st.n + 1) hW1 ht1_mem
  obtain ⟨trees2, t_loop, ht2_mem, -, hv2, -, -, hW2, -⟩ :=
    lctExposeLoop_spec hL (2 * st.n + 1) hW1 ht1_mem (last := v) rfl hv1 hlast1
      (par0 := inducedSubPar P (SplayState.detachRight P
        (SplayState.splay P st.splay (2 * st.n + 1) v) v) trees1) (fun _ => rfl)
      (List.Perm.refl _) (Nat.lt_succ_of_le (Nat.sub_le _ _))
  have h3 := splayCost_active hL S hW2 ht2_mem hv2
  rw [lctExposeLoop_n] at h3
  change splayCost S (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).1.splay
      (2 * st.n + 1) v ≤ (splayDepth (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).1.splay
      (2 * st.n + 1) v / 2 + 1) * splayRate S at h3
  change exposeLoopCost S (exposeStart P st v) (2 * st.n + 1) v ≤
    splayRate S * (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).2.2.1 +
      exposeRate S * (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).2.2.2 at h2
  show splayCost S st.splay (2 * st.n + 1) v + S.cost +
      exposeLoopCost S (exposeStart P st v) (2 * st.n + 1) v +
      splayCost S (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).1.splay
        (2 * st.n + 1) v + 600 ≤
    exposeRate S * ((splayDepth st.splay (2 * st.n + 1) v / 2 +
      (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).2.2.1 +
      splayDepth (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).1.splay
        (2 * st.n + 1) v / 2) +
      (1 + (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).2.2.2) + 1)
  generalize lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v = r at h2 h3 ⊢
  generalize splayCost S st.splay (2 * st.n + 1) v = a at h1 ⊢
  generalize splayCost S r.1.splay (2 * st.n + 1) v = f at h3 ⊢
  generalize exposeLoopCost S (exposeStart P st v) (2 * st.n + 1) v = e at h2 ⊢
  generalize splayDepth st.splay (2 * st.n + 1) v / 2 = d0 at h1 ⊢
  generalize splayDepth r.1.splay (2 * st.n + 1) v / 2 = df at h3 ⊢
  generalize r.2.2.1 = hl at h2 ⊢
  generalize r.2.2.2 = il at h2 ⊢
  unfold exposeRate at h2 ⊢
  generalize splayRate S = sr at h1 h2 h3 ⊢
  generalize S.cost = c at h2 ⊢
  nlinarith

end MinCostFlow.LinkCut.PathProg
