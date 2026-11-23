module

public import MinCostFlow.LinkCut.Prog.LctForestWrap
public import MinCostFlow.LinkCut.Prog.LctForestModel
public import MinCostFlow.IPM.Machine.ForestContract

/-!
# The query wrappers

This file builds the three wrappers that the solver's forest contract needs for `pathMin`,
`pathSum` and `pathAdd`. Each wrapper first tests `u = v`. If so, it returns at once, since the
path is empty. Otherwise it runs `lctWrapTail` from `LctForestWrap.lean`: find the root of `u`,
run the query, copy the answer to the heap pointer, and reroot back.

The `pathAdd` wrapper first copies the delta block to the heap pointer. The contract allows this
block to lie inside the cells of the link-cut tree, which `findRoot` may change, so the wrapper
must save it before it does anything else.

The results used later are `lctPathMinWrap_runs`, `lctPathSumWrap_runs` and
`lctPathAddWrap_runs`. Each one says that the wrapper keeps the represented roots, gives the
answer the contract asks for, and stays within a space and cost bound of the same shape as the
procedures it calls.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding MinCostFlow.IPM.Machine

section ForestFacts

/-- Both ends of an edge of a valid forest are vertices. -/
theorem rawEdges_lt {F : MathForest} (hV : F.Valid) {re : RawEdge} (hre : re ∈ F.rawEdges) :
    re.u < F.n ∧ re.v < F.n := by
  simp only [MathForest.rawEdges, List.mem_map] at hre
  obtain ⟨e, he, rfl⟩ := hre
  exact ⟨(hV.1 e he).1, (hV.1 e he).2.1⟩

/-- Two different vertices in one tree of a valid forest are vertices: each one is the end of
the first edge of a walk that leaves it. -/
theorem sameComp_lt_of_ne {F : MathForest} (hV : F.Valid) {u v : ℕ} (h : F.SameComp u v)
    (hne : u ≠ v) : u < F.n ∧ v < F.n := by
  have hfirst : ∀ {a c : ℕ}, F.SameComp a c → a ≠ c → a < F.n := by
    intro a c hac hne'
    obtain ⟨es, hw⟩ := hac
    cases hw with
    | nil _ => exact absurd rfl hne'
    | cons hre hcon _ =>
        have := rawEdges_lt hV hre
        rcases hcon with ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega
  exact ⟨hfirst h hne, hfirst h.symm (Ne.symm hne)⟩

theorem pathMin_self (F : MathForest) (u : ℕ) : F.pathMin u u = none := by
  simp [MathForest.pathMin, MathForest.findSteps_self, stepsMinHit]

theorem pathSum_self (F : MathForest) (u : ℕ) : F.pathSum u u = 0 := by
  simp [MathForest.pathSum, MathForest.findSteps_self, stepsCost]

theorem pathAdd_self (F : MathForest) (u : ℕ) (δ : ℚ) : F.pathAdd u u δ = F := by
  have hid : MathForest.applyStepsDelta [] δ = id := by
    funext e; simp [MathForest.applyStepsDelta]
  simp [MathForest.pathAdd, MathForest.findSteps_self, hid]

theorem pathAdd_n (F : MathForest) (u v : ℕ) (δ : ℚ) : (F.pathAdd u v δ).n = F.n := by
  unfold MathForest.pathAdd
  split <;> rfl

end ForestFacts

section Answers

/-- The answer that the link-cut `pathMin` writes is the answer the contract asks for. -/
theorem pathHitAt_of_lctPathMinAt {h L P a : ℕ} {mem : ℕ → ℕ} {r : Option PathHit}
    (hr : LctPathMinAt h L P r mem a) : PathHitAt mem a h L P r := by
  cases r with
  | none => exact hr
  | some hit =>
      obtain ⟨h0, h1, h2, h3, hv1, hv2, hq1, hq2⟩ := hr
      refine ⟨?_, ⟨hv1, hq1⟩, ⟨hv2, hq2⟩⟩
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i
      · simpa using h0
      · simpa using h1
      · simpa using h2
      · simpa using h3

/-- A `pathMin` answer depends only on its `2 * L + 4` words. -/
theorem pathHitAt_shift {h L P a a' : ℕ} {m m' : ℕ → ℕ} {r : Option PathHit}
    (hr : PathHitAt m a h L P r) (hag : ∀ i < 2 * L + 4, m' (a' + i) = m (a + i)) :
    PathHitAt m' a' h L P r := by
  cases r with
  | none =>
      have h0 := hag 0 (by omega)
      simp only [PathHitAt, Nat.add_zero] at hr h0 ⊢
      rw [h0]; exact hr
  | some hit =>
      obtain ⟨hl, ⟨hv1, hq1⟩, ⟨hv2, hq2⟩⟩ := hr
      have hb1 : ∀ i < L, m' (a' + 4 + i) = m (a + 4 + i) := fun i hi => by
        rw [show a' + 4 + i = a' + (4 + i) by omega, show a + 4 + i = a + (4 + i) by omega]
        exact hag _ (by omega)
      have hb2 : ∀ i < L, m' (a' + 4 + L + i) = m (a + 4 + L + i) := fun i hi => by
        rw [show a' + 4 + L + i = a' + (4 + L + i) by omega,
          show a + 4 + L + i = a + (4 + L + i) by omega]
        exact hag _ (by omega)
      refine ⟨fun i hi => ?_, ⟨fun i hi => ?_, ?_⟩, ⟨fun i hi => ?_, ?_⟩⟩
      · simp only [List.length_cons, List.length_nil] at hi
        rw [hag i (by omega)]; exact hl i hi
      · rw [hb1 i hi]; exact hv1 i hi
      · rw [← hq1]; unfold readRat; rw [intVal_congr hb1]
      · rw [hb2 i hi]; exact hv2 i hi
      · rw [← hq2]; unfold readRat; rw [intVal_congr hb2]

/-- A `pathSum` answer depends only on its `L` words. -/
theorem sumAt_shift {h L a a' : ℕ} {m m' : ℕ → ℕ} {z : ℤ}
    (hr : Valid m a h L ∧ intVal m a h L = z) (hag : ∀ i < L, m' (a' + i) = m (a + i)) :
    Valid m' a' h L ∧ intVal m' a' h L = z := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hag i hi]; exact hr.1 i hi
  · rw [← hr.2]; exact intVal_congr hag

end Answers

section WrapBody

/-- The run of `lctWrapBody`. If `u = v` the wrapper returns at once, so the forest must stay
the same (`hF1self`) and the answer must already hold in zero memory (`hself`). Otherwise it runs
`lctWrapTail`; the query `q` must then meet the run statement `hq`. -/
theorem lctWrapBody_runs {w h L P b u v hp A Cq Eq pos rh : ℕ}
    {F F1 : MathForest} {x₀ : LctConc} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (regs : ℕ → ℕ) (q : Stmt) (Ans : (ℕ → ℕ) → ℕ → Prop) (ω : ℕ → Bool)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hfr_eq : p.procs[lp.findRoot]? = some (lctFindRootBody lp))
    (hcut_eq : p.procs[lp.cut]? = some (lctCutBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀) (hV : F.Valid) (hsc : F.SameComp u v)
    (hF1n : F1.n = F.n) (hF1v : F1.Valid) (hF1self : u = v → F1 = F)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp) (hz₀ : ZeroFrom mem₀ hp)
    (hr0 : regs 0 = b) (hr1 : regs 1 = u) (hr2 : regs 2 = v) (hrh : regs rh = hp)
    (hrh20 : rh < 20)
    (hAns : ∀ m m' a a', Ans m a → (∀ i < A, m' (a' + i) = m (a + i)) → Ans m' a')
    (hself : u = v → Ans mem₀ hp)
    (hq : u ≠ v → ∀ mem1 x1 hp1 pos1 regs1,
      LctMemRep w h L P b F x1 mem1 → (∀ a, lctFoot b x1 a → a < hp1) → ZeroFrom mem1 hp1 →
      hp + A ≤ hp1 →
      hp1 + lctPhi L mem1 b F.n + Cq * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) +
        Eq < 2 ^ w →
      (∀ i < 20, regs1 i = regs i) → regs1 21 = hp1 →
      (∀ i < A, mem1 (hp + i) = mem₀ (hp + i)) →
      ∃ (hp2 : ℕ) (st2 : State) (c2 : ℕ) (x2 : LctConc),
        Runs w p ω q { mem := mem1, regs := regs1, pos := pos1 } .normal
          { mem := st2.mem, regs := Function.update regs1 23 hp2, pos := st2.pos } c2 ∧
        LctMemRep w h L P b F1 x2 st2.mem ∧
        (lctDSRep w h L P).Respects (lctFoot b x1) hp1
          (lctPhi L mem1 b F.n + Cq * (Nat.log 2 (F.n + 2) + 1) + Eq) mem1 hp2 b x2 st2.mem ∧
        c2 + (hp2 - hp1) + lctPhi L st2.mem b F.n ≤
          lctPhi L mem1 b F.n + Cq * (Nat.log 2 (F.n + 2) + 1) + 20 ∧
        Ans st2.mem hp1 ∧ RerootRoots mem1 st2.mem b F u)
    (hroom : hp + lctPhi L mem₀ b F.n +
      (C_FINDROOT_OP L + Cq + C_CUT_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 18 * A + Eq + 200 < 2 ^ w) :
    ∃ hp' st' c x',
      Runs w p ω (lctWrapBody lp rh A q) { mem := mem₀, regs := regs, pos := pos }
        (.returned hp') st' c ∧
      LctMemRep w h L P b F1 x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp
        (lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + Cq + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * A + 200) mem₀ hp' b x' st'.mem ∧
      c + (hp' - hp) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + Cq + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * A + 204 ∧
      Ans st'.mem hp ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
  let st : State := { mem := mem₀, regs := regs, pos := pos }
  have hw1 : 1 < 2 ^ w := by omega
  have hcond_eq : Expr.eval w st (.bin .eq (.reg 1) (.reg 2)) = some (if u = v then 1 else 0) := by
    have hw' : (if u = v then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    simpa [BinOp.eval] using Expr.eval_bin (op := .eq)
      (Expr.eval_reg_of_eq (w := w) (st := st) hr1) (Expr.eval_reg_of_eq (w := w) (st := st) hr2)
      (by simpa [BinOp.eval] using hw')
  by_cases huv : u = v
  · rw [hF1self huv]
    have hret : Runs w p ω (.ret (.reg rh)) st (.returned hp) st 2 :=
      runs_ret_iff.mpr ⟨hp, Expr.eval_reg_of_eq (w := w) (st := st) hrh, rfl, rfl, rfl⟩
    have hcond : Runs w p ω (lctWrapBody lp rh A q) st (.returned hp) st (3 + 2 + 1) := by
      rw [lctWrapBody, runs_cond_iff]
      refine ⟨1, 2, by simpa [huv] using hcond_eq, ?_, by decide⟩
      simp only [Nat.one_ne_zero, ↓reduceIte]
      exact hret
    refine ⟨hp, st, 3 + 2 + 1, x₀, hcond, hrep₀,
      ⟨le_rfl, Nat.le_add_right _ _, hz₀, fun _ _ _ => rfl, fun _ ha => Or.inl ha⟩, ?_,
      hself huv, fun _ _ => rfl⟩
    show 3 + 2 + 1 + (hp - hp) + lctPhi L mem₀ b F.n ≤ _
    omega
  · have hu := (sameComp_lt_of_ne hV hsc huv).1
    obtain ⟨hp', st', c, x', hrun, hrep', hresp', hc, hans, hroots⟩ :=
      lctWrapTail_runs (pos := pos) p lp mem₀ regs q Ans ω hp_base hp_sp hexpose_eq hreroot_eq
        hfr_eq hcut_eq hrep₀ hu hF1n hF1v hfoot (fun a ha => hz₀ a (by omega)) hr0 hr1 hrh hrh20
        hAns (hq huv) hroom
    refine ⟨hp', st', 3 + c + 1, x', ?_, hrep', hresp', by omega, hans, hroots⟩
    rw [lctWrapBody, runs_cond_iff]
    refine ⟨0, c, by simpa [huv] using hcond_eq, by simpa using hrun, rfl⟩

end WrapBody

section QueryWraps

/-- The `pathMin` wrapper. The answer has `2 * L + 4` words. -/
def lctPathMinWrap (lp : LctProcs) (L : ℕ) : Stmt :=
  lctWrapBody lp 3 (2 * L + 4) (.call 23 lp.pathMin [.reg 0, .reg 1, .reg 2, .reg 21])

/-- The `pathSum` wrapper. The answer has `L` words. -/
def lctPathSumWrap (lp : LctProcs) (L : ℕ) : Stmt :=
  lctWrapBody lp 3 L (.call 23 lp.pathSum [.reg 0, .reg 1, .reg 2, .reg 21])

/-- The `pathAdd` wrapper, for `args = [b, u, v, a, heap]`. It copies the delta block at `a` to
the heap pointer first, and then passes that copy to `pathAdd`. -/
def lctPathAddWrap (lp : LctProcs) (L : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.reg 2)) (.ret (.reg 4))
    (.call 26 lp.copyWords [.reg 3, .reg 4, .const L] ;;
      lctWrapTail lp 4 L
        (.call 23 lp.pathAdd [.reg 0, .reg 1, .reg 2, .reg 4, .const 0, .reg 21]))

theorem lctPathMinWrap_noRand (lp : LctProcs) (L : ℕ) : (lctPathMinWrap lp L).NoRand :=
  lctWrapBody_noRand _ _ _ (by simp [Stmt.NoRand])

theorem lctPathSumWrap_noRand (lp : LctProcs) (L : ℕ) : (lctPathSumWrap lp L).NoRand :=
  lctWrapBody_noRand _ _ _ (by simp [Stmt.NoRand])

theorem lctPathAddWrap_noRand (lp : LctProcs) (L : ℕ) : (lctPathAddWrap lp L).NoRand := by
  simp [lctPathAddWrap, lctWrapTail, Stmt.NoRand]

end QueryWraps

section QueryRuns

/-- The run of the `pathMin` wrapper on `args = [b, u, v, hp]`. -/
theorem lctPathMinWrap_runs {w h L P b u v hp pos : ℕ} {F : MathForest} {x₀ : LctConc}
    (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ) (ω : ℕ → Bool)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hfr_eq : p.procs[lp.findRoot]? = some (lctFindRootBody lp))
    (hcut_eq : p.procs[lp.cut]? = some (lctCutBody lp))
    (hq_eq : p.procs[lp.pathMin]? = some (lctPathMinBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀) (hV : F.Valid) (hsc : F.SameComp u v)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp) (hz₀ : ZeroFrom mem₀ hp)
    (hroom : hp + lctPhi L mem₀ b F.n +
      (C_FINDROOT_OP L + C_PATHMIN_OP L + C_CUT_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 18 * (2 * L + 4) + (2 * L + 5) + 200 < 2 ^ w) :
    ∃ hp' st' c x',
      Runs w p ω (lctPathMinWrap lp L) (startState [b, u, v, hp] mem₀ pos)
        (.returned hp') st' c ∧
      LctMemRep w h L P b F x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp
        (lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHMIN_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * (2 * L + 4) + 200) mem₀ hp' b x' st'.mem ∧
      c + (hp' - hp) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHMIN_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * (2 * L + 4) + 204 ∧
      PathHitAt st'.mem hp h L P (F.pathMin u v) ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
  refine lctWrapBody_runs (Cq := C_PATHMIN_OP L) (Eq := 2 * L + 5) (rh := 3) p lp mem₀ _ _
    (fun m a => PathHitAt m a h L P (F.pathMin u v)) ω hp_base hp_sp hexpose_eq hreroot_eq hfr_eq
    hcut_eq hrep₀ hV hsc rfl hV (fun _ => rfl) hfoot hz₀ rfl rfl rfl rfl (by decide)
    (fun _ _ _ _ hm hag => pathHitAt_shift hm hag)
    (fun huv => by subst huv; rw [pathMin_self]; exact hz₀ hp le_rfl) ?_ hroom
  intro huv mem1 x1 hp1 pos1 regs1 hrep1 hfoot1 hz1 _ hroom1 hregs1 hr21 _
  have hv := sameComp_lt_of_ne hV hsc huv
  obtain ⟨hp2, st2, c2, x2, hrun2, hrep2, hresp2, hans2, hc2, hroots2⟩ :=
    lctPathMinBody_runs (pos := pos1)
      (space := lctPhi L mem1 b F.n + C_PATHMIN_OP L * (Nat.log 2 (F.n + 2) + 1) + (2 * L + 5))
      p lp mem1 hp_base hp_sp hexpose_eq hreroot_eq hrep1 hv.1 hv.2 hsc hfoot1 hz1
      (by omega) (by omega) ω
  refine ⟨hp2, st2, 4 + c2 + 1, x2, ?_, hrep2, hresp2, by omega,
    pathHitAt_of_lctPathMinAt (r := F.pathMin u v) hans2, hroots2 huv⟩
  refine runs_call_iff.mpr ⟨[b, u, v, hp1], lctPathMinBody lp, .returned hp2, st2, c2, ?_, hq_eq,
    hrun2, rfl, by cases st2; rfl, rfl⟩
  have h0 : regs1 0 = b := hregs1 0 (by decide)
  have h1 : regs1 1 = u := hregs1 1 (by decide)
  have h2 : regs1 2 = v := hregs1 2 (by decide)
  simp [evalArgs, Expr.eval, h0, h1, h2, hr21]

/-- The run of the `pathSum` wrapper on `args = [b, u, v, hp]`. -/
theorem lctPathSumWrap_runs {w h L P b u v hp pos : ℕ} {F : MathForest} {x₀ : LctConc}
    (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ) (ω : ℕ → Bool)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hfr_eq : p.procs[lp.findRoot]? = some (lctFindRootBody lp))
    (hcut_eq : p.procs[lp.cut]? = some (lctCutBody lp))
    (hq_eq : p.procs[lp.pathSum]? = some (lctPathSumBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀) (hV : F.Valid) (hsc : F.SameComp u v)
    (hfits : Fits h L (F.pathSum u v))
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp) (hz₀ : ZeroFrom mem₀ hp)
    (hroom : hp + lctPhi L mem₀ b F.n +
      (C_FINDROOT_OP L + C_PATHSUM_OP L + C_CUT_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 18 * L + (L + 1) + 200 < 2 ^ w) :
    ∃ hp' st' c x',
      Runs w p ω (lctPathSumWrap lp L) (startState [b, u, v, hp] mem₀ pos)
        (.returned hp') st' c ∧
      LctMemRep w h L P b F x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp
        (lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHSUM_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * L + 200) mem₀ hp' b x' st'.mem ∧
      c + (hp' - hp) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHSUM_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * L + 204 ∧
      (Valid st'.mem hp h L ∧ intVal st'.mem hp h L = F.pathSum u v) ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
  refine lctWrapBody_runs (Cq := C_PATHSUM_OP L) (Eq := L + 1) (rh := 3) p lp mem₀ _ _
    (fun m a => Valid m a h L ∧ intVal m a h L = F.pathSum u v) ω hp_base hp_sp hexpose_eq
    hreroot_eq hfr_eq hcut_eq hrep₀ hV hsc rfl hV (fun _ => rfl) hfoot hz₀ rfl rfl rfl rfl
    (by decide) (fun _ _ _ _ hm hag => sumAt_shift hm hag)
    (fun huv => by
      subst huv
      rw [pathSum_self]
      exact ⟨zeroFrom_valid hz₀ le_rfl, intVal_zeroFrom hz₀ le_rfl⟩) ?_ hroom
  intro huv mem1 x1 hp1 pos1 regs1 hrep1 hfoot1 hz1 _ hroom1 hregs1 hr21 _
  have hv := sameComp_lt_of_ne hV hsc huv
  obtain ⟨hp2, st2, c2, x2, hrun2, hrep2, hresp2, hvalid2, hval2, hc2, hroots2⟩ :=
    lctPathSumBody_runs (pos := pos1)
      (space := lctPhi L mem1 b F.n + C_PATHSUM_OP L * (Nat.log 2 (F.n + 2) + 1) + (L + 1))
      p lp mem1 hp_base hp_sp hexpose_eq hreroot_eq hrep1 hv.1 hv.2 hsc hfoot1 hz1
      (by omega) (by omega) ω
  refine ⟨hp2, st2, 4 + c2 + 1, x2, ?_, hrep2, hresp2, by omega,
    ⟨hvalid2, hval2.trans (wrap_of_fits hfits)⟩, hroots2⟩
  refine runs_call_iff.mpr ⟨[b, u, v, hp1], lctPathSumBody lp, .returned hp2, st2, c2, ?_, hq_eq,
    hrun2, rfl, by cases st2; rfl, rfl⟩
  have h0 : regs1 0 = b := hregs1 0 (by decide)
  have h1 : regs1 1 = u := hregs1 1 (by decide)
  have h2 : regs1 2 = v := hregs1 2 (by decide)
  simp [evalArgs, Expr.eval, h0, h1, h2, hr21]

/-- The run of the `pathAdd` wrapper on `args = [b, u, v, a, hp]`, where the block at `a`
holds the delta. The copy of the delta at the start costs at most `17 * L + 10` steps, which
is why the cost bound has the extra term `17 * L`. -/
theorem lctPathAddWrap_runs {w h L P b u v a hp pos : ℕ} {F : MathForest} {x₀ : LctConc}
    (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ) (ω : ℕ → Bool)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hfr_eq : p.procs[lp.findRoot]? = some (lctFindRootBody lp))
    (hcut_eq : p.procs[lp.cut]? = some (lctCutBody lp))
    (hq_eq : p.procs[lp.pathAdd]? = some (lctPathAddBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀) (hV : F.Valid) (hsc : F.SameComp u v)
    (ha : a + L ≤ hp) (hva : Valid mem₀ a h L)
    (hfit : ∀ e ∈ (F.pathAdd u v (readRat mem₀ a h L P)).edges, EdgeFits h L P e)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp) (hz₀ : ZeroFrom mem₀ hp)
    (hroom : hp + lctPhi L mem₀ b F.n +
      (C_FINDROOT_OP L + C_PATHADD_OP L + C_CUT_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 18 * L + (L + 1) + 200 < 2 ^ w) :
    ∃ hp' st' c x',
      Runs w p ω (lctPathAddWrap lp L) (startState [b, u, v, a, hp] mem₀ pos)
        (.returned hp') st' c ∧
      LctMemRep w h L P b (F.pathAdd u v (readRat mem₀ a h L P)) x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) hp
        (lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHADD_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * L + 200) mem₀ hp' b x' st'.mem ∧
      c + (hp' - hp) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_FINDROOT_OP L + C_PATHADD_OP L + C_CUT_OP L) *
          (Nat.log 2 (F.n + 2) + 1) + 18 * L + (17 * L + 230) ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
  let st : State := startState [b, u, v, a, hp] mem₀ pos
  have hw1 : 1 < 2 ^ w := by omega
  have hhp_w : hp < 2 ^ w := by omega
  have hL_w : L < 2 ^ w := hp_base.hL
  have hcond_eq : Expr.eval w st (.bin .eq (.reg 1) (.reg 2)) = some (if u = v then 1 else 0) := by
    have hw' : (if u = v then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    simpa [BinOp.eval] using Expr.eval_bin (op := .eq)
      (Expr.eval_reg_of_eq (w := w) (st := st) (v := u) rfl)
      (Expr.eval_reg_of_eq (w := w) (st := st) (v := v) rfl) (by simpa [BinOp.eval] using hw')
  by_cases huv : u = v
  · subst huv
    rw [pathAdd_self]
    have hret : Runs w p ω (.ret (.reg 4)) st (.returned hp) st 2 :=
      runs_ret_iff.mpr ⟨hp, Expr.eval_reg_of_eq (w := w) (st := st) rfl, rfl, rfl, rfl⟩
    have hcond : Runs w p ω (lctPathAddWrap lp L) st (.returned hp) st (3 + 2 + 1) := by
      rw [lctPathAddWrap, runs_cond_iff]
      refine ⟨1, 2, by simpa using hcond_eq, ?_, by decide⟩
      simp only [Nat.one_ne_zero, ↓reduceIte]
      exact hret
    refine ⟨hp, st, 3 + 2 + 1, x₀, hcond, hrep₀,
      ⟨le_rfl, Nat.le_add_right _ _, hz₀, fun _ _ _ => rfl, fun _ ha => Or.inl ha⟩, ?_,
      fun _ _ => rfl⟩
    show 3 + 2 + 1 + (hp - hp) + lctPhi L mem₀ b F.n ≤ _
    omega
  have hu := (sameComp_lt_of_ne hV hsc huv).1
  have hv := (sameComp_lt_of_ne hV hsc huv).2
  rcases arenaHi_bounds hrep₀ hfoot hhp_w with ⟨harena_le, -⟩
  -- Step 1: copy the delta block to `hp`.
  have hcp_args : ∀ x ∈ [a, hp, L], x < 2 ^ w := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  have hpre_cp : (copyWordsContract w).pre [a, hp, L] mem₀ :=
    ⟨a, hp, L, rfl, hw1, by omega, by omega, Or.inr ha⟩
  obtain ⟨body_cp, hcp_eq, o_cp, st_cp, c_cp, hrun_cp, hpost_cp, hc_cp⟩ :=
    hp_base.copyWords_ok [a, hp, L] mem₀ pos ω hcp_args hpre_cp
  obtain ⟨_, _, _, hcp_arg, _, hcp_vals, hcp_out⟩ := hpost_cp
  cases hcp_arg
  have hc_cp' : c_cp ≤ 17 * L + 10 := hc_cp
  let regs' := Function.update st.regs 26 o_cp.value
  have hcall_cp : Runs w p ω (.call 26 lp.copyWords [.reg 3, .reg 4, .const L]) st .normal
      { mem := st_cp.mem, regs := regs', pos := st_cp.pos } (3 + c_cp + 1) := by
    refine runs_call_iff.mpr ⟨[a, hp, L], body_cp, o_cp, st_cp, c_cp, ?_, hcp_eq, hrun_cp,
      rfl, by cases st_cp; rfl, rfl⟩
    simp [evalArgs, Expr.eval, st, startState, hL_w]
  have hkeep : ∀ x, x < hp → st_cp.mem x = mem₀ x := fun x hx => hcp_out x (Or.inl hx)
  have hloc := lctDSRep_local w h L P b F x₀ mem₀ st_cp.mem (fun x hx => (hkeep x (hfoot x hx)).symm)
  have hrep_cp : LctMemRep w h L P b F x₀ st_cp.mem := hloc.1 hrep₀
  have hphi_cp : lctPhi L st_cp.mem b F.n = lctPhi L mem₀ b F.n := by
    have h2 := hloc.2
    simp only [lctDSRep, hrep₀.2.2.2.2.1] at h2
    exact h2.symm
  have hz_cp : ZeroFrom st_cp.mem (hp + L) := fun x hx =>
    (hcp_out x (Or.inr hx)).trans (hz₀ x (by omega))
  have hcanon_cp : ∀ z, lctCanonRoot st_cp.mem b F.n z = lctCanonRoot mem₀ b F.n z := by
    intro z
    unfold lctCanonRoot
    rw [show lctAuxParent st_cp.mem (lctNodesBase b) (lctCap F.n) =
        lctAuxParent mem₀ (lctNodesBase b) (lctCap F.n) from funext fun z =>
      lctAuxParent_agree (fun i _ hi => (hkeep i
        (lt_of_lt_of_le (by simpa [lctArenaHi] using hi) harena_le)).symm) z]
  have hr0' : regs' 0 = b := by simp [regs', st, startState]
  have hr1' : regs' 1 = u := by simp [regs', st, startState]
  have hr2' : regs' 2 = v := by simp [regs', st, startState]
  have hr4' : regs' 4 = hp := by simp [regs', st, startState]
  -- Step 2: the tail, with `pathAdd` as the query.
  have hroom' : hp + lctPhi L st_cp.mem b F.n +
      (C_FINDROOT_OP L + C_PATHADD_OP L + C_CUT_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 18 * L + (L + 1) + 200 < 2 ^ w := by
    rw [hphi_cp]; exact hroom
  obtain ⟨hp', st', c, x', hrun, hrep', hresp', hc, -, hroots⟩ :=
    lctWrapTail_runs (A := L) (Cq := C_PATHADD_OP L) (Eq := L + 1) (rh := 4)
      (F1 := F.pathAdd u v (readRat mem₀ a h L P)) (pos := st_cp.pos) p lp st_cp.mem regs'
      (.call 23 lp.pathAdd [.reg 0, .reg 1, .reg 2, .reg 4, .const 0, .reg 21])
      (fun _ _ => True) ω hp_base hp_sp hexpose_eq hreroot_eq hfr_eq hcut_eq hrep_cp hu
      (pathAdd_n _ _ _ _) (MathForest.pathAdd_valid hV _ _ _) hfoot hz_cp hr0' hr1' hr4'
      (by decide) (fun _ _ _ _ _ _ => trivial)
      (by
          intro mem1 x1 hp1 pos1 regs1 hrep1 hfoot1 hz1 hle hroom1 hregs1 hr21 hag
          have hag' : ∀ i < L, mem1 (hp + i) = mem₀ (a + i) := fun i hi =>
            (hag i hi).trans (hcp_vals i hi)
          have hvalid1 : Valid mem1 hp h L := fun i hi => by rw [hag' i hi]; exact hva i hi
          have hδ : ((if (0 : ℕ) = 0 then intVal mem1 hp h L else -intVal mem1 hp h L : ℤ) : ℚ) /
              (2 : ℚ) ^ P = readRat mem₀ a h L P := by
            simp only [↓reduceIte]
            unfold readRat
            rw [intVal_congr hag']
          obtain ⟨hp2, st2, c2, x2, hrun2, hrep2, hresp2, hc2, hroots2⟩ :=
            lctPathAddBody_runs (dPtr := hp) (dNeg := 0) (pos := pos1)
              (space := lctPhi L mem1 b F.n + C_PATHADD_OP L * (Nat.log 2 (F.n + 2) + 1) + (L + 1))
              p lp mem1 hp_base hp_sp hexpose_eq hreroot_eq hrep1 hu hv hsc (by decide) hvalid1
              (by omega) hδ hfit hfoot1 hz1 (by omega) (by omega) ω
          rw [pathAdd_n] at hc2
          refine ⟨hp2, st2, 6 + c2 + 1, x2, ?_, hrep2, hresp2, by omega, trivial, hroots2 huv⟩
          refine runs_call_iff.mpr ⟨[b, u, v, hp, 0, hp1], lctPathAddBody lp, .returned hp2, st2, c2,
            ?_, hq_eq, hrun2, rfl, by cases st2; rfl, rfl⟩
          have h0 : regs1 0 = b := (hregs1 0 (by decide)).trans hr0'
          have h1 : regs1 1 = u := (hregs1 1 (by decide)).trans hr1'
          have h2 : regs1 2 = v := (hregs1 2 (by decide)).trans hr2'
          have h4 : regs1 4 = hp := (hregs1 4 (by decide)).trans hr4'
          have h0w : 0 < 2 ^ w := by omega
          simp [evalArgs, Expr.eval, h0, h1, h2, h4, hr21, h0w]) hroom'
  refine ⟨hp', st', 3 + ((3 + c_cp + 1) + c + 1) + 1, x', ?_, hrep', ?_, ?_, ?_⟩
  · rw [lctPathAddWrap, runs_cond_iff]
    refine ⟨0, _, by simpa [huv] using hcond_eq, ?_, rfl⟩
    simp only [↓reduceIte]
    exact runs_seq_normal hcall_cp hrun
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hresp'
    refine ⟨h1, by rw [← hphi_cp]; exact h2, h3, fun x hx hnf => ?_, h5⟩
    rw [h4 x hx hnf, hkeep x hx]
  · rw [hphi_cp] at hc
    omega
  · intro z hz
    rw [hroots z hz, hcanon_cp]
end QueryRuns

end MinCostFlow.LinkCut.Prog
