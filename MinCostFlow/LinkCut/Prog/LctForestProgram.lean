module

public import MinCostFlow.LinkCut.Prog.LctForestOps
public import MinCostFlow.LinkCut.Prog.LctImplements

/-!
# The link-cut program for the solver's forest contract

This file puts together what `LctForestImplements.lean` needs to show that the link-cut tree
meets `forestMachineContract lctForestModel`:

* the wrappers for `init` and `link`, which turn the contract's arguments into the ones the
  link-cut procedures take, with their run theorems `lctInitWrap_runs` and `lctLinkWrap_runs`;
* the whole program `lctForestBodies` (five wrappers, then the link-cut procedures) and the map
  `lctForestOp` from operation numbers to procedure numbers;
* the rate `lctForestRate`, the space bound `lctForestAlloc`, and the representation
  `lctForestRep`, with its locality `lctForestRep_local`;
* how the represented roots match the model's roots after `link` and `cut`
  (`linkRoots_eq`, `cutRoots_eq`).

**Why the number of vertices is bounded.** The contract's space bound of an operation sees only
the arguments of the call, not the state. But the space our operations use grows with the
potential, which grows with the number of vertices `n`. So the representation also asks
`n ≤ N` for a fixed `N`, and the space bound of an operation is the bound for `N` vertices.
Initialization with `n > N` must then be impossible, so its space bound is `2 ^ w` in that case;
no call can meet the room condition `heap + 2 ^ w < 2 ^ w`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding MinCostFlow.IPM.Machine

section Wrappers

/-- The `init` wrapper, for `args = [n, L, P, heap]`: initialize `n` vertices at `heap`. -/
def lctInitWrap (lp : LctProcs) : Stmt :=
  .call 4 lp.init [.reg 0, .reg 3] ;; .ret (.reg 4)

/-- The `link` wrapper, for `args = [b, a, heap]`. The edge record at `a` is `[eid, u, v]`
followed by four blocks of `L` words. -/
def lctLinkWrap (lp : LctProcs) (L : ℕ) : Stmt :=
  .call 3 lp.link [.reg 0, .load (.bin .add (.reg 1) (.const 1)),
    .load (.bin .add (.reg 1) (.const 2)), .load (.reg 1), .bin .add (.reg 1) (.const 3),
    .bin .add (.reg 1) (.const (3 + L)), .bin .add (.reg 1) (.const (3 + 2 * L)),
    .bin .add (.reg 1) (.const (3 + 3 * L)), .reg 2] ;;
  .ret (.reg 3)

theorem lctInitWrap_noRand (lp : LctProcs) : (lctInitWrap lp).NoRand := by
  simp [lctInitWrap, Stmt.NoRand]

theorem lctLinkWrap_noRand (lp : LctProcs) (L : ℕ) : (lctLinkWrap lp L).NoRand := by
  simp [lctLinkWrap, Stmt.NoRand]

/-- The run of the `init` wrapper. -/
theorem lctInitWrap_runs {w h L P n heap pos : ℕ} (p : Program) (lp : LctProcs)
    (mem₀ : ℕ → ℕ) (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hL : L < 2 ^ w) (hP : P < 2 ^ w)
    (hinit_eq : p.procs[lp.init]? = some (lctInitBody L P))
    (hz₀ : ZeroFrom mem₀ heap) (hb_w : heap + lctArenaWords n < 2 ^ w) (ω : ℕ → Bool) :
    ∃ hp' st' c x,
      Runs w p ω (lctInitWrap lp) (startState [n, L, P, heap] mem₀ pos) (.returned hp') st' c ∧
      LctMemRep w h L P heap (MathForest.empty n) x st'.mem ∧
      (lctDSRep w h L P).Respects (fun _ => False) heap (lctArenaWords n) mem₀ hp' heap x
        st'.mem ∧
      c + lctPhi L st'.mem heap n ≤ C_LCT_INIT * (n + 1) + 6 := by
  obtain ⟨o, st₁, c, x, hrun, -, hrep, hresp, hc⟩ :=
    lctInit_runs (n := n) (b := heap) p mem₀ pos hh hw hL hP hz₀ hb_w ω
  let st : State := startState [n, L, P, heap] mem₀ pos
  let st₂ : State := { st₁ with regs := Function.update st.regs 4 o.value }
  have hcall : Runs w p ω (.call 4 lp.init [.reg 0, .reg 3]) st .normal st₂ (2 + c + 1) :=
    runs_call_iff.mpr ⟨[n, heap], lctInitBody L P, o, st₁, c, by simp [evalArgs, Expr.eval, st,
      startState], hinit_eq, hrun, rfl, rfl, rfl⟩
  have hret : Runs w p ω (.ret (.reg 4)) st₂ (.returned o.value) st₂ 2 :=
    runs_ret_iff.mpr ⟨o.value, Expr.eval_reg_of_eq (by simp [st₂]), rfl, rfl, rfl⟩
  exact ⟨o.value, st₂, 2 + c + 1 + 2 + 1, x, runs_seq_normal hcall hret, hrep, hresp,
    by simp only [st₂]; omega⟩

/-- The run of the `link` wrapper: it reads `eid`, `u` and `v` from the record at `a` and passes
pointers to the four blocks to `link`. -/
theorem lctLinkWrap_runs {w h L P b a heap space pos : ℕ} {F : MathForest} {x₀ : LctConc}
    {e : ForestEdge} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ) (ω : ℕ → Bool)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hreroot_eq : p.procs[lp.reroot]? = some (lctRerootBody lp))
    (hlink_eq : p.procs[lp.link]? = some (lctLinkBody lp))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hu : e.u < F.n) (hv : e.v < F.n) (hdisc : ¬ F.SameComp e.u e.v)
    (hfresh : ∀ e' ∈ F.edges, e'.eid ≠ e.eid) (heid : e.eid < 2 ^ w)
    (hfe : EdgeFits h L P e) (hedge : ForestEdgeAt mem₀ a h L P e) (ha : a + 3 + 4 * L ≤ heap)
    (hfoot : ∀ a, lctFoot b x₀ a → a < heap) (hz₀ : ZeroFrom mem₀ heap)
    (hroom : heap + lctPhi L mem₀ b F.n + C_LINK_OP L * (Nat.log 2 (F.n + 2) + 1) +
        7000 * (L + 1) * (F.n + 2) + 7 * L + 1 < 2 ^ w)
    (hspace : lctPhi L mem₀ b F.n + C_LINK_OP L * (Nat.log 2 (F.n + 2) + 1) + 7 * L + 1 ≤
      space) :
    ∃ hp' st' c x',
      Runs w p ω (lctLinkWrap lp L) (startState [b, a, heap] mem₀ pos) (.returned hp') st' c ∧
      LctMemRep w h L P b (F.link e) x' st'.mem ∧
      (lctDSRep w h L P).Respects (lctFoot b x₀) heap space mem₀ hp' b x' st'.mem ∧
      c + (hp' - heap) + lctPhi L st'.mem b F.n ≤
        lctPhi L mem₀ b F.n + C_LINK_OP L * (Nat.log 2 (F.n + 2) + 1) + 30 ∧
      ∀ z < F.n, lctCanonRoot st'.mem b F.n z =
        if lctCanonRoot mem₀ b F.n z = lctCanonRoot mem₀ b F.n e.u then lctCanonRoot mem₀ b F.n e.v
        else lctCanonRoot mem₀ b F.n z := by
  obtain ⟨hlist, hcv, hcval, ⟨hfv, hfval⟩, ⟨hafv, hafval⟩, ⟨habv, habval⟩⟩ := hedge
  have hw_heap : heap < 2 ^ w := by omega
  -- The four block addresses, written as the wrapper computes them.
  have e1 : a + (3 + L) = a + 3 + L := by omega
  have e2 : a + (3 + 2 * L) = a + 3 + 2 * L := by omega
  have e3 : a + (3 + 3 * L) = a + 3 + 3 * L := by omega
  obtain ⟨hpf, st₁, c, x', hrun, hrep', hresp, hc, hroots⟩ :=
    lctLinkBody_runs (cPtr := a + 3) (fPtr := a + (3 + L)) (afPtr := a + (3 + 2 * L))
      (abPtr := a + (3 + 3 * L)) (pos := pos) p lp mem₀ hp_base hp_sp hexpose_eq hreroot_eq
      hrep₀ hu hv hdisc hfresh heid hfe hcv (by omega) hcval (e1 ▸ hfv) (by omega)
      (e1 ▸ hfval) (e2 ▸ hafv) (by omega) (e2 ▸ hafval) (e3 ▸ habv) (by omega) (e3 ▸ habval)
      hfoot hz₀ hroom hspace ω
  let st : State := startState [b, a, heap] mem₀ pos
  have hev : ∀ k, a + k < 2 ^ w →
      Expr.eval w st (.bin .add (.reg 1) (.const k)) = some (a + k) := fun k hk =>
    Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) hk
  have hl0 : Expr.eval w st (.load (.reg 1)) = some e.eid :=
    Expr.eval_load_of_eq (Expr.eval_reg_of_eq rfl) (by simpa [st, startState] using hlist 0 (by simp))
  have hl1 : Expr.eval w st (.load (.bin .add (.reg 1) (.const 1))) = some e.u :=
    Expr.eval_load_of_eq (hev 1 (by omega)) (by simpa [st, startState] using hlist 1 (by simp))
  have hl2 : Expr.eval w st (.load (.bin .add (.reg 1) (.const 2))) = some e.v :=
    Expr.eval_load_of_eq (hev 2 (by omega)) (by simpa [st, startState] using hlist 2 (by simp))
  have hr0 : Expr.eval w st (.reg 0) = some b := Expr.eval_reg_of_eq rfl
  have hr2 : Expr.eval w st (.reg 2) = some heap := Expr.eval_reg_of_eq rfl
  let st₂ : State := { st₁ with regs := Function.update st.regs 3 hpf }
  have hcall : Runs w p ω (.call 3 lp.link [.reg 0, .load (.bin .add (.reg 1) (.const 1)),
      .load (.bin .add (.reg 1) (.const 2)), .load (.reg 1), .bin .add (.reg 1) (.const 3),
      .bin .add (.reg 1) (.const (3 + L)), .bin .add (.reg 1) (.const (3 + 2 * L)),
      .bin .add (.reg 1) (.const (3 + 3 * L)), .reg 2]) st .normal st₂ (24 + c + 1) := by
    refine runs_call_iff.mpr ⟨_, lctLinkBody lp, .returned hpf, st₁, c, ?_, hlink_eq, hrun, rfl,
      rfl, rfl⟩
    simp only [evalArgs, hr0, hl0, hl1, hl2, hr2, hev 3 (by omega), hev (3 + L) (by omega),
      hev (3 + 2 * L) (by omega), hev (3 + 3 * L) (by omega)]
  have hret : Runs w p ω (.ret (.reg 3)) st₂ (.returned hpf) st₂ 2 :=
    runs_ret_iff.mpr ⟨hpf, Expr.eval_reg_of_eq (by simp [st₂]), rfl, rfl, rfl⟩
  refine ⟨hpf, st₂, 24 + c + 1 + 2 + 1, x', runs_seq_normal hcall hret, hrep', hresp, ?_, hroots⟩
  simp only [st₂]
  have : lctPhi L st₁.mem b (F.link e).n = lctPhi L st₁.mem b F.n := rfl
  omega

end Wrappers

section Layout

/-- The procedures: the wrappers for `init`, `link`, `pathAdd`, `pathMin` and `pathSum`, then
the link-cut procedures from index `b0 + 5` on. -/
def lctForestBodies (h L P b0 : ℕ) : List Stmt :=
  [lctInitWrap (LctProcs.atBase (b0 + 5)), lctLinkWrap (LctProcs.atBase (b0 + 5)) L,
    lctPathAddWrap (LctProcs.atBase (b0 + 5)) L, lctPathMinWrap (LctProcs.atBase (b0 + 5)) L,
    lctPathSumWrap (LctProcs.atBase (b0 + 5)) L] ++ lctBodies h L P (b0 + 5)

/-- The procedure of operation `i`: `findRoot` and `cut` are the link-cut procedures, the
others are wrappers. -/
def lctForestOp (b0 : ℕ) : ℕ → ℕ
  | 0 => (LctProcs.atBase (b0 + 5)).findRoot
  | 1 => b0 + 1
  | 2 => (LctProcs.atBase (b0 + 5)).cut
  | 3 => b0 + 2
  | 4 => b0 + 3
  | 5 => b0 + 4
  | _ => b0

/-- No procedure of the program uses random bits. -/
theorem lctForestBodies_noRand (h L P b0 : ℕ) : ∀ s ∈ lctForestBodies h L P b0, s.NoRand := by
  intro s hs
  simp only [lctForestBodies, List.cons_append, List.mem_cons, List.nil_append] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | hs
  · exact lctInitWrap_noRand _
  · exact lctLinkWrap_noRand _ _
  · exact lctPathAddWrap_noRand _ _
  · exact lctPathMinWrap_noRand _ _
  · exact lctPathSumWrap_noRand _ _
  · exact lctBodies_noRand h L P (b0 + 5) s hs

/-- The five wrappers at their indices. -/
theorem lctForestBodies_procs {p : Program} {h L P b0 : ℕ}
    (hp : p.HasAt b0 (lctForestBodies h L P b0)) :
    p.procs[b0]? = some (lctInitWrap (LctProcs.atBase (b0 + 5))) ∧
    p.procs[b0 + 1]? = some (lctLinkWrap (LctProcs.atBase (b0 + 5)) L) ∧
    p.procs[b0 + 2]? = some (lctPathAddWrap (LctProcs.atBase (b0 + 5)) L) ∧
    p.procs[b0 + 3]? = some (lctPathMinWrap (LctProcs.atBase (b0 + 5)) L) ∧
    p.procs[b0 + 4]? = some (lctPathSumWrap (LctProcs.atBase (b0 + 5)) L) ∧
    p.HasAt (b0 + 5) (lctBodies h L P (b0 + 5)) := by
  have hf := hasAt_append_left hp
  have g : ∀ i (hi : i < 5), _ := fun i hi => hf i (by simpa using hi)
  exact ⟨by simpa using g 0 (by decide), g 1 (by decide), g 2 (by decide), g 3 (by decide),
    g 4 (by decide), by simpa using hasAt_append_right hp⟩

end Layout

section Bounds

/-- The amortized cost of every operation on `n` vertices. -/
def lctForestRate (L n : ℕ) : ℕ := 1000000 * (L + 1) * (Nat.log 2 (n + 2) + 1)

/-- The bound on the potential with `n` vertices (`LctMemRep.lctPhi_le_bound`). -/
def lctPhiBound (L n : ℕ) : ℕ := 2 * (K_SPLAY_STEP L + C_HEAVY L) * n * (Nat.log 2 (n + 2) + 1)

/-- The space bound of an operation with at most `N` vertices. -/
def lctForestOpSpace (L N : ℕ) : ℕ :=
  lctPhiBound L N + 1000000 * (L + 1) * (Nat.log 2 (N + 2) + 1) + 7000 * (L + 1) * (N + 2) +
    100 * L + 1000

/-- The space bounds: index `6` is initialization (`args = [n, L, P, heap]`), the others are
operations. -/
def lctForestAlloc (w L N : ℕ) (i : ℕ) (args : List ℕ) : ℕ :=
  if i = 6 then (if args.getD 0 0 ≤ N then lctArenaWords (args.getD 0 0) + 10 else 2 ^ w)
  else lctForestOpSpace L N

theorem lctPhiBound_mono (L : ℕ) {n N : ℕ} (hn : n ≤ N) : lctPhiBound L n ≤ lctPhiBound L N :=
  Nat.mul_le_mul (Nat.mul_le_mul_left _ hn) (Nat.succ_le_succ (Nat.log_mono_right (by omega)))

end Bounds

section Rep

/-- The representation of the model state `(F, r)`: the link-cut tree holds `F`, `F` has at
most `N` vertices, and `r` is the root map that the memory represents. -/
def lctForestRep (w h L P N : ℕ) : DSRep (MathForest × (ℕ → ℕ)) where
  τ := LctConc
  rep b s x mem := LctMemRep w h L P b s.1 x mem ∧ s.1.n ≤ N ∧
    s.2 = rootsOn s.1.n (lctCanonRoot mem b s.1.n)
  phi b x mem := lctPhi L mem b x.n
  foot b x a := lctFoot b x a

/-- The represented roots depend only on the cells of the arena. -/
theorem lctCanonRoot_of_foot {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem mem' : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) (hag : ∀ a, lctFoot b x a → mem a = mem' a) (z : ℕ) :
    lctCanonRoot mem' b F.n z = lctCanonRoot mem b F.n z := by
  have hxn : x.n = F.n := hrep.2.2.2.2.1
  unfold lctCanonRoot
  rw [show lctAuxParent mem' (lctNodesBase b) (lctCap F.n) =
      lctAuxParent mem (lctNodesBase b) (lctCap F.n) from funext fun q =>
    lctAuxParent_agree (fun i hi1 hi2 => hag i (lctFoot_arena
      (by unfold lctNodesBase at hi1; omega) (by rw [hxn]; simpa [lctArenaHi] using hi2))) q]

theorem lctForestRep_local (w h L P N : ℕ) : (lctForestRep w h L P N).Local := by
  intro b s x mem mem' hag
  have hl := lctDSRep_local w h L P b s.1 x mem mem' hag
  refine ⟨fun hr => ?_, hl.2⟩
  obtain ⟨hrep, hn, hroots⟩ := hr
  refine ⟨hl.1 hrep, hn, ?_⟩
  rw [hroots]
  congr 1
  funext z
  exact (lctCanonRoot_of_foot hrep hag z).symm

/-- After `link e`, the represented roots are the model's roots. -/
theorem linkRoots_eq {F : MathForest} {e : ForestEdge} {c₀ c' : ℕ → ℕ} (hu : e.u < F.n) (hv : e.v < F.n)
    (hl : ∀ z < F.n, c' z = if c₀ z = c₀ e.u then c₀ e.v else c₀ z) :
    lctLinkRoots F (rootsOn F.n c₀) e = rootsOn F.n c' := by
  funext z
  by_cases hz : z < F.n
  · simp only [lctLinkRoots, rootsOn, hz, hu, hv, ↓reduceIte, hl z hz]
  · simp [lctLinkRoots, rootsOn, hz]

/-- After `cut x y`, the represented roots are the model's roots. -/
theorem cutRoots_eq {mem₀ mem' : ℕ → ℕ} {b x y : ℕ} {F : MathForest}
    (hcr : CutRoots mem₀ mem' b F x y) :
    lctCutRoots F (rootsOn F.n (lctCanonRoot mem₀ b F.n)) x y =
      rootsOn F.n (lctCanonRoot mem' b F.n) := by
  funext z
  by_cases hz : z < F.n
  · obtain ⟨hbad, hsame, hsplit⟩ := hcr z hz
    by_cases hxy : x < F.n ∧ y < F.n
    · by_cases hcut : F.cut x y = F
      · simp only [lctCutRoots, rootsOn, hz, hxy, and_self, hcut, ↓reduceIte,
          hsame hxy.1 hxy.2 hcut]
      · obtain ⟨hy, hx, hrest⟩ := hsplit hxy.1 hxy.2 hcut
        by_cases hzy : (F.cut x y).SameComp z y
        · simp only [lctCutRoots, rootsOn, hz, hxy, and_self, hcut, hzy, ↓reduceIte, hy hzy]
        · by_cases hzx : (F.cut x y).SameComp z x
          · simp only [lctCutRoots, rootsOn, hz, hxy, and_self, hcut, hzy, hzx, ↓reduceIte,
              hx hzy hzx]
          · simp only [lctCutRoots, rootsOn, hz, hxy, and_self, hcut, hzy, hzx, ↓reduceIte,
              hrest hzy hzx]
    · simp only [lctCutRoots, rootsOn, hz, hxy, ↓reduceIte, hbad hxy]
  · simp [lctCutRoots, rootsOn, hz]

end Rep

end MinCostFlow.LinkCut.Prog
