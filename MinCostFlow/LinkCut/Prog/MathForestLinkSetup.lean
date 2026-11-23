module

public import MinCostFlow.LinkCut.Prog.MathForestLinkPhi

/-!
# Word-RAM `link` Helpers, Setup, Splice, and Arithmetic Bounds

Provides:
- `storeNodeOffsExprStmt` and `storeNodeOffsExprStmt_runs` (reused by `cut`).
- `C_LINK_OP`, `lctLinkSetupRegsBody`, `lctLinkPreallocBody`, `lctLinkOffPairsExpr`,
  `lctLinkSpliceBody`, `lctLinkBody`, and their `.NoRand` proofs.
- Execution lemmas `lctExposeInvs_perm_trees`, `link_prealloc_runs`, and `link_splice_runs`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section StoreNodeOffsStmt

/-- Reusable deterministic sequence storing each `(off, valExpr)` pair at
`nodeAddrExpr + off`. Shared by `link` and `cut`. -/
def storeNodeOffsExprStmt (nodeAddrExpr : Expr) : List (ℕ × Expr) → Stmt
  | [] => .nop
  | (off, valExpr) :: rest =>
      .store (.bin .add nodeAddrExpr (.const off)) valExpr ;;
      storeNodeOffsExprStmt nodeAddrExpr rest

theorem storeNodeOffsExprStmt_noRand (nodeAddrExpr : Expr) (pairs : List (ℕ × Expr)) :
    (storeNodeOffsExprStmt nodeAddrExpr pairs).NoRand := by
  induction pairs with
  | nil => simp [storeNodeOffsExprStmt, Stmt.NoRand]
  | cons p rest ih => simp [storeNodeOffsExprStmt, Stmt.NoRand, ih]

/-- Correctness and exact cost bound for `storeNodeOffsExprStmt` matching `writeNodeOffs`. -/
theorem storeNodeOffsExprStmt_runs {w nb x pos : ℕ} {p : Program} {ω : ℕ → Bool}
    {addrExpr : Expr} {regs : ℕ → ℕ}
    (haddr : ∀ mem, Expr.eval w { mem := mem, regs := regs, pos := pos } addrExpr =
      some (nb + NODE_STRIDE * x))
    (pairs : List (ℕ × (Expr × ℕ)))
    (hpairs : ∀ q ∈ pairs,
      q.1 < 2 ^ w ∧ nb + NODE_STRIDE * x + q.1 < 2 ^ w ∧
      ∀ mem, Expr.eval w { mem := mem, regs := regs, pos := pos } q.2.1 = some q.2.2) :
    ∀ mem, ∃ c,
      Runs w p ω (storeNodeOffsExprStmt addrExpr (pairs.map fun q => (q.1, q.2.1)))
        { mem := mem, regs := regs, pos := pos } .normal
        { mem := writeNodeOffs mem nb x (pairs.map fun q => (q.1, q.2.2)),
          regs := regs, pos := pos } c ∧
      c ≤ 5 * pairs.length + 1 + (pairs.map fun q => addrExpr.size + q.2.1.size).sum := by
  induction pairs with
  | nil =>
      intro mem
      simp only [List.map_nil, storeNodeOffsExprStmt, writeNodeOffs, List.length_nil,
        List.sum_nil]
      exact ⟨1, runs_nop_iff.2 ⟨rfl, rfl, rfl⟩, by omega⟩
  | cons q rest ih =>
      intro mem
      have hq := hpairs q List.mem_cons_self
      have hrest : ∀ q' ∈ rest,
          q'.1 < 2 ^ w ∧ nb + NODE_STRIDE * x + q'.1 < 2 ^ w ∧
          ∀ mem', Expr.eval w { mem := mem', regs := regs, pos := pos } q'.2.1 = some q'.2.2 :=
        fun q' hq' => hpairs q' (List.mem_cons_of_mem _ hq')
      have hev_addr :
          Expr.eval w { mem := mem, regs := regs, pos := pos }
            (.bin .add addrExpr (.const q.1)) = some (nb + NODE_STRIDE * x + q.1) :=
        Expr.eval_add (haddr mem) (Expr.eval_const hq.1) hq.2.1
      have hst_store :
          Runs w p ω (.store (.bin .add addrExpr (.const q.1)) q.2.1)
            { mem := mem, regs := regs, pos := pos } .normal
            { mem := Function.update mem (nb + NODE_STRIDE * x + q.1) q.2.2,
              regs := regs, pos := pos } ((addrExpr.size + 1 + 1) + q.2.1.size + 1) :=
        runs_store_iff.2 ⟨nb + NODE_STRIDE * x + q.1, q.2.2, hev_addr, hq.2.2 mem, rfl, rfl, rfl⟩
      rcases ih hrest (Function.update mem (nb + NODE_STRIDE * x + q.1) q.2.2) with
        ⟨c₂, hrun₂, hc₂⟩
      refine ⟨((addrExpr.size + 1 + 1) + q.2.1.size + 1) + c₂ + 1,
        runs_seq_iff.2 (Or.inr ⟨_, _, c₂, hst_store, hrun₂, rfl⟩), ?_⟩
      simp only [List.map_cons, List.length_cons, List.sum_cons] at hc₂ ⊢
      omega

end StoreNodeOffsStmt

section LinkProgramDefs

/-- Amortized constant coefficient for `link` (`reroot + expose + splay + splice + pull + alloc`). -/
def C_LINK_OP (L : ℕ) : ℕ := 450000 * (L + 1)

/-- Register initialization prelude for `lctLinkBody` on
`args = [b, u, v, eid, cPtr, fPtr, afPtr, abPtr, hp_caller]`. Sets registers `9..20`. -/
def lctLinkSetupRegsBody : Stmt :=
  .assign 9 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))) ;;
  .assign 10 (.bin .add (.reg 0) (.const LCT_HDR_SIZE)) ;;
  .assign 11 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 12 (.bin .add (.reg 2) (.const 1)) ;;
  .assign 13 (.reg 8) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 9)) ;;
  .assign 15 (.bin .add (.reg 14) (.reg 9)) ;;
  .assign 16 (.bin .add (.reg 15) (.reg 9)) ;;
  .assign 17 (.bin .add (.reg 16) (.reg 9)) ;;
  .assign 18 (.bin .add (.reg 17) (.reg 9)) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 9)) ;;
  .assign 20 (.bin .add (.reg 19) (.reg 9))

/-- Copy the four input number blocks (`cPtr, fPtr, afPtr, abPtr`) into scratch slots `0..3`. -/
def lctLinkCopy4Body (lp : LctProcs) : Stmt :=
  .call 25 lp.copyWords [.reg 4, .reg 13, .reg 9] ;;
  .call 25 lp.copyWords [.reg 5, .reg 14, .reg 9] ;;
  .call 25 lp.copyWords [.reg 6, .reg 15, .reg 9] ;;
  .call 25 lp.copyWords [.reg 7, .reg 16, .reg 9]

/-- Compute zero and `p_cb = wrap(-cost)` in scratch slots `4..6` and store `hp_eff`. -/
def lctLinkZeroSubBody (lp : LctProcs) : Stmt :=
  .call 25 lp.splay.numZero [.reg 9, .reg 17] ;;
  .call 25 lp.splay.numSub [.reg 17, .reg 13, .reg 9, .reg 18] ;;
  .store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 20)

/-- Pre-allocation phase for `lctLinkBody`: sets up registers `9..20`, copies `cPtr, fPtr, afPtr, abPtr`
into `[hp_caller, hp_caller + 4 * L)`, computes `0` and `p_cb = wrap(-cost)` in
`[hp_caller + 4 * L, hp_caller + 7 * L)`, and stores `hp_eff = hp_caller + 7 * L` at `LCT_HDR_HP`. -/
def lctLinkPreallocBody (lp : LctProcs) : Stmt :=
  lctLinkSetupRegsBody ;;
  lctLinkCopy4Body lp ;;
  lctLinkZeroSubBody lp

/-- Offset-expression list matching `lctLinkOffPairs` for storing edge node `ed`'s non-aggregate fields. -/
def lctLinkOffPairsExpr (r_u r_u1 r_v r_v1 r_eid r_cf r_cb r_fl r_af r_ab : ℕ) : List (ℕ × Expr) :=
  [(OFF_LEFT, .const 0),
   (OFF_RIGHT, .reg r_u1),
   (OFF_PARENT, .const 0),
   (OFF_PPAR, .reg r_v1),
   (OFF_REV, .const 0),
   (OFF_ISV, .const 0),
   (OFF_HASE, .const 1),
   (OFF_DIR, .const 0),
   (OFF_HAS_TAG, .const 0),
   (OFF_TAG_PTR, .const 0),
   (OFF_TAG_NEG, .const 0),
   (OFF_EID, .reg r_eid),
   (OFF_EU, .reg r_u),
   (OFF_EV, .reg r_v),
   (OFF_COST_FWD, .reg r_cb),
   (OFF_COST_BWD, .reg r_cf),
   (OFF_FLOW_PTR, .reg r_fl),
   (OFF_AF_PTR, .reg r_ab),
   (OFF_AB_PTR, .reg r_af)]

/-- Free-list pop and pointer/payload splicing phase of `lctLinkBody` after `splay (u + 1)`. -/
def lctLinkSpliceBody : Stmt :=
  .assign 21 (.load (.bin .add (.reg 0) (.const LCT_HDR_FREE))) ;;
  .assign 22 (.bin .add (.reg 10) (.bin .mul (.const NODE_STRIDE) (.reg 21))) ;;
  .assign 23 (.load (.bin .add (.reg 22) (.const OFF_EU))) ;;
  .store (.bin .add (.reg 0) (.const LCT_HDR_FREE)) (.reg 23) ;;
  storeNodeOffsExprStmt (.reg 22) (lctLinkOffPairsExpr 1 11 2 12 3 13 19 14 15 16) ;;
  .assign 24 (.bin .add (.reg 10) (.bin .mul (.const NODE_STRIDE) (.reg 11))) ;;
  .store (.bin .add (.reg 24) (.const OFF_PARENT)) (.reg 21)

/-- Deterministic Word-RAM `link` procedure body taking
`args = [b, u, v, eid, cPtr, fPtr, afPtr, abPtr, hp_caller]`. -/
def lctLinkBody (lp : LctProcs) : Stmt :=
  lctLinkPreallocBody lp ;;
  .call 25 lp.reroot [.reg 10, .reg 11] ;;
  .call 25 lp.expose [.reg 10, .reg 12] ;;
  .call 25 lp.splay.splay [.reg 10, .reg 11] ;;
  lctLinkSpliceBody ;;
  .call 25 lp.splay.pull [.reg 10, .reg 21] ;;
  .assign 26 (.load (.bin .add (.reg 0) (.const LCT_HDR_HP))) ;;
  .ret (.bin .add (.reg 26) (.const 1))

theorem lctLinkSetupRegsBody_noRand : lctLinkSetupRegsBody.NoRand := by
  simp [lctLinkSetupRegsBody, Stmt.NoRand]

theorem lctLinkCopy4Body_noRand (lp : LctProcs) : (lctLinkCopy4Body lp).NoRand := by
  simp [lctLinkCopy4Body, Stmt.NoRand]

theorem lctLinkZeroSubBody_noRand (lp : LctProcs) : (lctLinkZeroSubBody lp).NoRand := by
  simp [lctLinkZeroSubBody, Stmt.NoRand]

theorem lctLinkPreallocBody_noRand (lp : LctProcs) : (lctLinkPreallocBody lp).NoRand := by
  simp [lctLinkPreallocBody, lctLinkSetupRegsBody_noRand, lctLinkCopy4Body_noRand,
    lctLinkZeroSubBody_noRand, Stmt.NoRand]

theorem lctLinkSpliceBody_noRand : lctLinkSpliceBody.NoRand := by
  simp [lctLinkSpliceBody, storeNodeOffsExprStmt_noRand, Stmt.NoRand]

theorem lctLinkBody_noRand (lp : LctProcs) : (lctLinkBody lp).NoRand := by
  simp [lctLinkBody, lctLinkPreallocBody_noRand, lctLinkSpliceBody_noRand, Stmt.NoRand]

end LinkProgramDefs

section LinkExecutionHelpers

theorem link_runs_seq_normal {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt}
    {st st₁ st' : State} {o : Outcome} {c₁ c₂ : ℕ}
    (h₁ : Runs w p ω s₁ st .normal st₁ c₁)
    (h₂ : Runs w p ω s₂ st₁ o st' c₂) :
    Runs w p ω (s₁ ;; s₂) st o st' (c₁ + c₂ + 1) :=
  runs_seq_iff.2 (Or.inr ⟨st₁, c₁, c₂, h₁, h₂, rfl⟩)

theorem link_runs_seq_call_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {r f : ℕ} {args : List Expr} {s : Stmt} {st st₁ : State} {vs : List ℕ}
    {body : Stmt} {o₁ : Outcome} {c₁ : ℕ} {o : Outcome} {st' : State} {c₂ : ℕ}
    (heval : evalArgs w st args = some vs)
    (hproc : p.procs[f]? = some body)
    (hbody : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hcont : Runs w p ω s
      { mem := st₁.mem, regs := Function.update st.regs r o₁.value, pos := st₁.pos } o st' c₂) :
    Runs w p ω (.call r f args ;; s) st o st' (argsSize args + c₁ + 1 + c₂ + 1) :=
  link_runs_seq_normal
    (runs_call_iff.2 ⟨vs, body, o₁, st₁, c₁, heval, hproc, hbody, rfl, rfl, rfl⟩) hcont

private lemma link_perm_flatMap {α β : Type*} (f : α → List β) {l₁ l₂ : List α}
    (hp : l₁.Perm l₂) : (l₁.flatMap f).Perm (l₂.flatMap f) := by
  induction hp with
  | nil => rfl
  | cons x _ ih => simp only [List.flatMap_cons]; exact ih.append_left (f x)
  | swap x y l =>
      simp only [List.flatMap_cons, ← List.append_assoc]
      exact List.Perm.append_right _ List.perm_append_comm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem lctExposeInvs_perm_trees {w h L P b n : ℕ} {freeEdges : List ℕ}
    {edgeMap : List (ℕ × ForestEdge)} {trees trees' : List AuxTree} {mem : ℕ → ℕ}
    (hi : LctExposeInvs w h L P b n freeEdges edgeMap trees mem)
    (hp : trees.Perm trees') :
    LctExposeInvs w h L P b n freeEdges edgeMap trees' mem := by
  have hs_perm : (trees'.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) :=
    link_perm_flatMap AuxTree.toList hp.symm
  refine ⟨hi.hdrN, hi.hdrCap, hi.hdrL, hi.hdrP,
    ⟨hi.sf.1, hi.sf.2.1, hi.sf.2.2.1, hi.sf.2.2.2.1, hi.sf.2.2.2.2.1, hi.sf.2.2.2.2.2.1,
     hi.sf.2.2.2.2.2.2.1, hi.sf.2.2.2.2.2.2.2.1, hs_perm.trans hi.sf.perm,
     fun s hs => hi.sf.trees_ok s (hp.mem_iff.2 hs)⟩,
    hi.freeChain, ?_, hi.vertexOk, ?_, ?_, hi.subdivOk⟩
  · intro ed hed
    rcases hi.freeNodeOk ed hed with ⟨h1, h2, htr, h4⟩
    exact ⟨h1, h2, hp.mem_iff.1 htr, h4⟩
  · intro q hq
    rcases hi.edgeOk q hq with ⟨h1, h2, h3, h4, h5, h6, h7, s, hs, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, s, hp.mem_iff.1 hs, h8⟩
  · intro s hs
    exact hi.auxPathOk s (hp.mem_iff.2 hs)

private lemma link_copyWords_step {w h L hp_caller pos r_src r_dst f_cp : ℕ}
    {p : Program} {ω : ℕ → Bool} {regs : ℕ → ℕ} {mem₀ mem : ℕ → ℕ} {src dst : ℕ}
    (hcw : MeetsContract w p f_cp (copyWordsContract w))
    (h2w1 : 1 < 2 ^ w)
    (hsrc_reg : regs r_src = src) (hdst_reg : regs r_dst = dst) (hL_reg : regs 9 = L)
    (hsrc_lt : src + L ≤ hp_caller) (hdst_lo : hp_caller ≤ dst)
    (hdst_hi : dst + L < 2 ^ w) (hL_w : L < 2 ^ w)
    (hsrc_valid : Valid mem src h L)
    (hbelow_in : ∀ a < hp_caller, mem a = mem₀ a) :
    ∃ st' c,
      Runs w p ω (.call 25 f_cp [.reg r_src, .reg r_dst, .reg 9])
        { mem := mem, regs := regs, pos := pos } .normal st' c ∧
      c ≤ 17 * L + 14 ∧
      (∀ i < L, st'.mem (dst + i) = mem (src + i)) ∧
      (∀ a, a < dst ∨ dst + L ≤ a → st'.mem a = mem a) ∧
      (∀ a < hp_caller, st'.mem a = mem₀ a) ∧
      Valid st'.mem dst h L ∧
      intVal st'.mem dst h L = intVal mem src h L ∧
      (∀ r' ≠ 25, st'.regs r' = regs r') := by
  have heval : evalArgs w { mem := mem, regs := regs, pos := pos }
      [.reg r_src, .reg r_dst, .reg 9] = some [src, dst, L] := by
    simp [evalArgs, Expr.eval_reg, hsrc_reg, hdst_reg, hL_reg]
  have hargs_w : ∀ a ∈ ([src, dst, L] : List ℕ), a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  have hpre : (copyWordsContract w).pre [src, dst, L] mem :=
    ⟨src, dst, L, rfl, h2w1, by omega, by omega, Or.inr (le_trans hsrc_lt hdst_lo)⟩
  rcases runs_call_of_meetsContract hcw heval hargs_w hpre ω with
    ⟨st', c, _, hrun, ⟨s0, d0, l0, heq, _, hcp, hout⟩, _, hreg_eq, hc_le⟩
  injection heq with hs hrest
  injection hrest with hd hrest2
  injection hrest2 with hl _
  subst s0 d0 l0
  have hbelow_out : ∀ a < hp_caller, st'.mem a = mem₀ a := fun a ha =>
    (hout a (Or.inl (lt_of_lt_of_le ha hdst_lo))).trans (hbelow_in a ha)
  have hval : Valid st'.mem dst h L := fun i hi => by rw [hcp i hi]; exact hsrc_valid i hi
  have hint : intVal st'.mem dst h L = intVal mem src h L := intVal_congr hcp
  have hc' : c ≤ 17 * L + 14 := by
    simp only [copyWordsContract, argsSize, Expr.size_reg] at hc_le
    omega
  exact ⟨st', c, hrun, hc', hcp, hout, hbelow_out, hval, hint, hreg_eq⟩

private lemma link_setupRegs_runs {w b u v eid cPtr fPtr afPtr abPtr hp_caller L cap pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {regs0 : ℕ → ℕ}
    (hr0 : regs0 0 = b) (hr1 : regs0 1 = u) (hr2 : regs0 2 = v) (hr3 : regs0 3 = eid)
    (hr4 : regs0 4 = cPtr) (hr5 : regs0 5 = fPtr) (hr6 : regs0 6 = afPtr) (hr7 : regs0 7 = abPtr)
    (hr8 : regs0 8 = hp_caller)
    (hL_mem : mem (b + LCT_HDR_L) = L)
    (harena : lctArenaHi b cap ≤ hp_caller) (hucap : u + 1 ≤ cap) (hvcap : v + 1 ≤ cap)
    (heff_w : hp_caller + 7 * L < 2 ^ w) (h14000 : 14000 < 2 ^ w) :
    ∃ regs1 c,
      Runs w p ω lctLinkSetupRegsBody { mem := mem, regs := regs0, pos := pos } .normal
        { mem := mem, regs := regs1, pos := pos } c ∧
      c ≤ 80 ∧
      regs1 0 = b ∧ regs1 1 = u ∧ regs1 2 = v ∧ regs1 3 = eid ∧
      regs1 4 = cPtr ∧ regs1 5 = fPtr ∧ regs1 6 = afPtr ∧ regs1 7 = abPtr ∧
      regs1 8 = hp_caller ∧ regs1 9 = L ∧ regs1 10 = lctNodesBase b ∧
      regs1 11 = u + 1 ∧ regs1 12 = v + 1 ∧
      regs1 13 = hp_caller ∧ regs1 14 = hp_caller + L ∧
      regs1 15 = hp_caller + 2 * L ∧ regs1 16 = hp_caller + 3 * L ∧
      regs1 17 = hp_caller + 4 * L ∧ regs1 18 = hp_caller + 5 * L ∧
      regs1 19 = hp_caller + 6 * L ∧ regs1 20 = hp_caller + 7 * L := by
  have hL_lt : LCT_HDR_L < 2 ^ w := by unfold LCT_HDR_L; omega
  have harena' := harena
  unfold lctArenaHi lctNodesBase NODE_STRIDE at harena'
  have hnb_add : b + LCT_HDR_L < 2 ^ w := by unfold LCT_HDR_SIZE LCT_HDR_L at *; omega
  have hsz_lt : LCT_HDR_SIZE < 2 ^ w := by unfold LCT_HDR_SIZE; omega
  have hnb_w : b + LCT_HDR_SIZE < 2 ^ w := by unfold LCT_HDR_SIZE at *; omega
  have h1_w : 1 < 2 ^ w := by omega
  have hu_w : u + 1 < 2 ^ w := by unfold LCT_HDR_SIZE at *; omega
  have hv_w : v + 1 < 2 ^ w := by unfold LCT_HDR_SIZE at *; omega
  dsimp only [lctLinkSetupRegsBody]
  have step9 :
      Runs w p ω (.assign 9 (.load (.bin .add (.reg 0) (.const LCT_HDR_L))))
        { mem := mem, regs := regs0, pos := pos } .normal
        { mem := mem, regs := Function.update regs0 9 L, pos := pos } 5 := by
    refine runs_assign_iff.2 ⟨L, Expr.eval_load_mem (Expr.eval_add (by simp [Expr.eval_reg, hr0])
      (Expr.eval_const hL_lt) hnb_add) (by simpa using hL_mem), rfl, rfl, by simp [Expr.size]⟩
  have step10 :
      Runs w p ω (.assign 10 (.bin .add (.reg 0) (.const LCT_HDR_SIZE)))
        { mem := mem, regs := Function.update regs0 9 L, pos := pos } .normal
        { mem := mem, regs := Function.update (Function.update regs0 9 L) 10 (lctNodesBase b), pos := pos } 4 := by
    refine runs_assign_iff.2 ⟨lctNodesBase b,
      Expr.eval_add (by simp [Expr.eval_reg, hr0]) (Expr.eval_const hsz_lt) hnb_w, rfl, rfl,
      by simp [Expr.size]⟩
  set r10 := Function.update (Function.update regs0 9 L) 10 (lctNodesBase b)
  have step11 :
      Runs w p ω (.assign 11 (.bin .add (.reg 1) (.const 1)))
        { mem := mem, regs := r10, pos := pos } .normal
        { mem := mem, regs := Function.update r10 11 (u + 1), pos := pos } 4 := by
    refine runs_assign_iff.2 ⟨u + 1,
      Expr.eval_add (by simp [r10, Expr.eval_reg, hr1]) (Expr.eval_const h1_w) hu_w, rfl, rfl,
      by simp [Expr.size]⟩
  set r11 := Function.update r10 11 (u + 1)
  have step12 :
      Runs w p ω (.assign 12 (.bin .add (.reg 2) (.const 1)))
        { mem := mem, regs := r11, pos := pos } .normal
        { mem := mem, regs := Function.update r11 12 (v + 1), pos := pos } 4 := by
    refine runs_assign_iff.2 ⟨v + 1,
      Expr.eval_add (by simp [r11, r10, Expr.eval_reg, hr2]) (Expr.eval_const h1_w) hv_w, rfl, rfl,
      by simp [Expr.size]⟩
  set r12 := Function.update r11 12 (v + 1)
  have step13 :
      Runs w p ω (.assign 13 (.reg 8)) { mem := mem, regs := r12, pos := pos } .normal
        { mem := mem, regs := Function.update r12 13 hp_caller, pos := pos } 2 := by
    refine runs_assign_iff.2 ⟨hp_caller, by simp [r12, r11, r10, Expr.eval_reg, hr8],
      rfl, rfl, by simp [Expr.size]⟩
  set r13 := Function.update r12 13 hp_caller
  have hmk_add : ∀ {r_cur r_dst cur next : ℕ} {regs : ℕ → ℕ},
      regs r_cur = cur → regs 9 = L → cur + L < 2 ^ w →
      cur + L = next →
      Runs w p ω (.assign r_dst (.bin .add (.reg r_cur) (.reg 9)))
        { mem := mem, regs := regs, pos := pos } .normal
        { mem := mem, regs := Function.update regs r_dst next, pos := pos } 4 := by
    intro r_cur r_dst cur next regs hc hl hlt hsum
    subst hsum
    refine runs_assign_iff.2 ⟨cur + L, Expr.eval_add (by simp [Expr.eval_reg, hc])
      (by simp [Expr.eval_reg, hl]) hlt, rfl, rfl, by simp [Expr.size]⟩
  have step14 := hmk_add (r_cur := 13) (r_dst := 14) (cur := hp_caller) (next := hp_caller + L)
    (regs := r13) (by simp [r13]) (by simp [r13, r12, r11, r10]) (by omega) rfl
  set r14 := Function.update r13 14 (hp_caller + L)
  have step15 := hmk_add (r_cur := 14) (r_dst := 15) (cur := hp_caller + L)
    (next := hp_caller + 2 * L) (regs := r14) (by simp [r14])
    (by simp [r14, r13, r12, r11, r10]) (by omega) (by omega)
  set r15 := Function.update r14 15 (hp_caller + 2 * L)
  have step16 := hmk_add (r_cur := 15) (r_dst := 16) (cur := hp_caller + 2 * L)
    (next := hp_caller + 3 * L) (regs := r15) (by simp [r15])
    (by simp [r15, r14, r13, r12, r11, r10]) (by omega) (by omega)
  set r16 := Function.update r15 16 (hp_caller + 3 * L)
  have step17 := hmk_add (r_cur := 16) (r_dst := 17) (cur := hp_caller + 3 * L)
    (next := hp_caller + 4 * L) (regs := r16) (by simp [r16])
    (by simp [r16, r15, r14, r13, r12, r11, r10]) (by omega) (by omega)
  set r17 := Function.update r16 17 (hp_caller + 4 * L)
  have step18 := hmk_add (r_cur := 17) (r_dst := 18) (cur := hp_caller + 4 * L)
    (next := hp_caller + 5 * L) (regs := r17) (by simp [r17])
    (by simp [r17, r16, r15, r14, r13, r12, r11, r10]) (by omega) (by omega)
  set r18 := Function.update r17 18 (hp_caller + 5 * L)
  have step19 := hmk_add (r_cur := 18) (r_dst := 19) (cur := hp_caller + 5 * L)
    (next := hp_caller + 6 * L) (regs := r18) (by simp [r18])
    (by simp [r18, r17, r16, r15, r14, r13, r12, r11, r10]) (by omega) (by omega)
  set r19 := Function.update r18 19 (hp_caller + 6 * L)
  have step20 := hmk_add (r_cur := 19) (r_dst := 20) (cur := hp_caller + 6 * L)
    (next := hp_caller + 7 * L) (regs := r19) (by simp [r19])
    (by simp [r19, r18, r17, r16, r15, r14, r13, r12, r11, r10]) (by omega) (by omega)
  set r20 := Function.update r19 20 (hp_caller + 7 * L)
  have hrun := link_runs_seq_normal step9 (link_runs_seq_normal step10 (link_runs_seq_normal step11
    (link_runs_seq_normal step12 (link_runs_seq_normal step13 (link_runs_seq_normal step14
      (link_runs_seq_normal step15 (link_runs_seq_normal step16 (link_runs_seq_normal step17
        (link_runs_seq_normal step18 (link_runs_seq_normal step19 step20))))))))))
  refine ⟨r20, _, hrun, by omega, ?_⟩
  simp [r20, r19, r18, r17, r16, r15, r14, r13, r12, r11, r10, hr0, hr1, hr2, hr3, hr4, hr5, hr6,
    hr7, hr8]

private lemma link_pa_off_le {hp L k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : hp + k₁ * L ≤ hp + k₂ * L :=
  Nat.add_le_add_left (Nat.mul_le_mul_right L h) hp

private lemma link_pa_copy_cost {c1 c2 c3 c4 L : ℕ}
    (h1 : c1 ≤ 17 * L + 14) (h2 : c2 ≤ 17 * L + 14)
    (h3 : c3 ≤ 17 * L + 14) (h4 : c4 ≤ 17 * L + 14) :
    c1 + (c2 + (c3 + c4 + 1) + 1) + 1 ≤ 68 * L + 60 := by omega

private lemma link_pa_zs_cost {cz csub L : ℕ} (hz : cz ≤ 7) (hs : csub ≤ 74 * L + 47) :
    cz + (csub + 5 + 1) + 1 ≤ 74 * L + 65 := by omega

private lemma link_pa_total_cost {c_sr c_cp c_zs L : ℕ}
    (hsr : c_sr ≤ 80) (hcp : c_cp ≤ 68 * L + 60) (hzs : c_zs ≤ 74 * L + 65) :
    c_sr + (c_cp + c_zs + 1) + 1 ≤ 150 * L + 210 := by omega

private lemma link_prealloc_copy4
    {w h L cPtr fPtr afPtr abPtr hp_caller pos : ℕ}
    {p : Program} {lp : LctProcs} {ω : ℕ → Bool} {mem₀ : ℕ → ℕ} {regs : ℕ → ℕ}
    (hcw : MeetsContract w p lp.copyWords (copyWordsContract w))
    (h2w1 : 1 < 2 ^ w) (hL_w : L < 2 ^ w) (heff_w : hp_caller + 7 * L < 2 ^ w)
    (hc_valid : Valid mem₀ cPtr h L) (hc_bd : cPtr + L ≤ hp_caller)
    (hf_valid : Valid mem₀ fPtr h L) (hf_bd : fPtr + L ≤ hp_caller)
    (haf_valid : Valid mem₀ afPtr h L) (haf_bd : afPtr + L ≤ hp_caller)
    (hab_valid : Valid mem₀ abPtr h L) (hab_bd : abPtr + L ≤ hp_caller)
    (hr4 : regs 4 = cPtr) (hr5 : regs 5 = fPtr) (hr6 : regs 6 = afPtr) (hr7 : regs 7 = abPtr)
    (hr9 : regs 9 = L) (hr13 : regs 13 = hp_caller) (hr14 : regs 14 = hp_caller + L)
    (hr15 : regs 15 = hp_caller + 2 * L) (hr16 : regs 16 = hp_caller + 3 * L) :
    ∃ st4 c_cp,
      Runs w p ω (lctLinkCopy4Body lp) { mem := mem₀, regs := regs, pos := pos } .normal st4 c_cp ∧
      c_cp ≤ 68 * L + 60 ∧
      (∀ a < hp_caller, st4.mem a = mem₀ a) ∧
      (∀ a, hp_caller + 4 * L ≤ a → st4.mem a = mem₀ a) ∧
      Valid st4.mem hp_caller h L ∧ intVal st4.mem hp_caller h L = intVal mem₀ cPtr h L ∧
      Valid st4.mem (hp_caller + L) h L ∧ intVal st4.mem (hp_caller + L) h L = intVal mem₀ fPtr h L ∧
      Valid st4.mem (hp_caller + 2 * L) h L ∧ intVal st4.mem (hp_caller + 2 * L) h L = intVal mem₀ afPtr h L ∧
      Valid st4.mem (hp_caller + 3 * L) h L ∧ intVal st4.mem (hp_caller + 3 * L) h L = intVal mem₀ abPtr h L ∧
      (∀ r' ≠ 25, st4.regs r' = regs r') := by
  have hw1 : hp_caller + L < 2 ^ w := by omega
  have hw2 : (hp_caller + L) + L < 2 ^ w := by omega
  have hw3 : (hp_caller + 2 * L) + L < 2 ^ w := by omega
  have hw4 : (hp_caller + 3 * L) + L < 2 ^ w := by omega
  rcases link_copyWords_step hcw h2w1 hr4 hr13 hr9
      hc_bd le_rfl hw1 hL_w hc_valid (fun _ _ => rfl) with
    ⟨st1, c1, hrun1, hc1, _, hout1, hbelow1, hval1, hint1, hreg1⟩
  have hr5_1 : st1.regs 5 = fPtr := (hreg1 5 (by decide)).trans hr5
  have hr6_1 : st1.regs 6 = afPtr := (hreg1 6 (by decide)).trans hr6
  have hr7_1 : st1.regs 7 = abPtr := (hreg1 7 (by decide)).trans hr7
  have hr9_1 : st1.regs 9 = L := (hreg1 9 (by decide)).trans hr9
  have hr14_1 : st1.regs 14 = hp_caller + L := (hreg1 14 (by decide)).trans hr14
  have hf_val1 : Valid st1.mem fPtr h L := fun i hi => by
    rw [hbelow1 (fPtr + i) (lt_of_lt_of_le (Nat.add_lt_add_left hi fPtr) hf_bd)]; exact hf_valid i hi
  have hf_int1 : intVal st1.mem fPtr h L = intVal mem₀ fPtr h L :=
    intVal_agree_block fun i hi => hbelow1 (fPtr + i) (lt_of_lt_of_le (Nat.add_lt_add_left hi fPtr) hf_bd)
  rcases link_copyWords_step hcw h2w1 hr5_1 hr14_1 hr9_1
      hf_bd (Nat.le_add_right hp_caller L) hw2 hL_w hf_val1 hbelow1 with
    ⟨st2, c2, hrun2, hc2, _, hout2, hbelow2, hval2, hint2, hreg2⟩
  have hr6_2 : st2.regs 6 = afPtr := (hreg2 6 (by decide)).trans hr6_1
  have hr7_2 : st2.regs 7 = abPtr := (hreg2 7 (by decide)).trans hr7_1
  have hr9_2 : st2.regs 9 = L := (hreg2 9 (by decide)).trans hr9_1
  have hr15_2 : st2.regs 15 = hp_caller + 2 * L :=
    (hreg2 15 (by decide)).trans ((hreg1 15 (by decide)).trans hr15)
  have haf_val2 : Valid st2.mem afPtr h L := fun i hi => by
    rw [hbelow2 (afPtr + i) (lt_of_lt_of_le (Nat.add_lt_add_left hi afPtr) haf_bd)]; exact haf_valid i hi
  have haf_int2 : intVal st2.mem afPtr h L = intVal mem₀ afPtr h L :=
    intVal_agree_block fun i hi => hbelow2 (afPtr + i) (lt_of_lt_of_le (Nat.add_lt_add_left hi afPtr) haf_bd)
  rcases link_copyWords_step hcw h2w1 hr6_2 hr15_2 hr9_2
      haf_bd (Nat.le_add_right hp_caller (2 * L)) hw3 hL_w haf_val2 hbelow2 with
    ⟨st3, c3, hrun3, hc3, _, hout3, hbelow3, hval3, hint3, hreg3⟩
  have hr7_3 : st3.regs 7 = abPtr := (hreg3 7 (by decide)).trans hr7_2
  have hr9_3 : st3.regs 9 = L := (hreg3 9 (by decide)).trans hr9_2
  have hr16_3 : st3.regs 16 = hp_caller + 3 * L :=
    (hreg3 16 (by decide)).trans ((hreg2 16 (by decide)).trans ((hreg1 16 (by decide)).trans hr16))
  have hab_val3 : Valid st3.mem abPtr h L := fun i hi => by
    rw [hbelow3 (abPtr + i) (lt_of_lt_of_le (Nat.add_lt_add_left hi abPtr) hab_bd)]; exact hab_valid i hi
  have hab_int3 : intVal st3.mem abPtr h L = intVal mem₀ abPtr h L :=
    intVal_agree_block fun i hi => hbelow3 (abPtr + i) (lt_of_lt_of_le (Nat.add_lt_add_left hi abPtr) hab_bd)
  rcases link_copyWords_step hcw h2w1 hr7_3 hr16_3 hr9_3
      hab_bd (Nat.le_add_right hp_caller (3 * L)) hw4 hL_w hab_val3 hbelow3 with
    ⟨st4, c4, hrun4, hc4, _, hout4, hbelow4, hval4, hint4, hreg4⟩
  have hrun_all : Runs w p ω (lctLinkCopy4Body lp) { mem := mem₀, regs := regs, pos := pos } .normal st4
      (c1 + (c2 + (c3 + c4 + 1) + 1) + 1) := by
    dsimp only [lctLinkCopy4Body]
    exact link_runs_seq_normal hrun1 (link_runs_seq_normal hrun2 (link_runs_seq_normal hrun3 hrun4))
  have hkeep4 : ∀ r' ≠ 25, st4.regs r' = regs r' := fun r' hr' =>
    (hreg4 r' hr').trans ((hreg3 r' hr').trans ((hreg2 r' hr').trans (hreg1 r' hr')))
  have hhi : ∀ a, hp_caller + 4 * L ≤ a → st4.mem a = mem₀ a := fun a ha => by
    rw [hout4 a (Or.inr (le_trans (by omega) ha)), hout3 a (Or.inr (le_trans (by omega) ha)),
      hout2 a (Or.inr (le_trans (by omega) ha)), hout1 a (Or.inr (le_trans (by omega) ha))]
  have hcf_blk : ∀ i < L, st4.mem (hp_caller + i) = st1.mem (hp_caller + i) := fun i hi => by
    have h1 : hp_caller + i < hp_caller + L := Nat.add_lt_add_left hi hp_caller
    have h13 : hp_caller + L ≤ hp_caller + 3 * L :=
      Nat.add_le_add_left (Nat.le_mul_of_pos_left L (by decide)) hp_caller
    have h12 : hp_caller + L ≤ hp_caller + 2 * L :=
      Nat.add_le_add_left (Nat.le_mul_of_pos_left L (by decide)) hp_caller
    rw [hout4 _ (Or.inl (lt_of_lt_of_le h1 h13)),
      hout3 _ (Or.inl (lt_of_lt_of_le h1 h12)),
      hout2 _ (Or.inl h1)]
  have hfl_blk : ∀ i < L, st4.mem (hp_caller + L + i) = st2.mem (hp_caller + L + i) := fun i hi => by
    have h2 : hp_caller + L + i < hp_caller + 2 * L := by
      have : hp_caller + L + i < hp_caller + L + L := Nat.add_lt_add_left hi _
      omega
    rw [hout4 _ (Or.inl (lt_of_lt_of_le h2 (link_pa_off_le (by decide : 2 ≤ 3)))),
      hout3 _ (Or.inl h2)]
  have haf_blk : ∀ i < L, st4.mem (hp_caller + 2 * L + i) = st3.mem (hp_caller + 2 * L + i) :=
    fun i hi => hout4 _ (Or.inl (by have := Nat.add_lt_add_left hi (hp_caller + 2 * L); omega))
  refine ⟨st4, _, hrun_all, link_pa_copy_cost hc1 hc2 hc3 hc4, hbelow4, hhi,
    fun i hi => by rw [hcf_blk i hi]; exact hval1 i hi,
    (intVal_agree_block hcf_blk).trans hint1,
    fun i hi => by rw [hfl_blk i hi]; exact hval2 i hi,
    (intVal_agree_block hfl_blk).trans (hint2.trans hf_int1),
    fun i hi => by rw [haf_blk i hi]; exact hval3 i hi,
    (intVal_agree_block haf_blk).trans (hint3.trans haf_int2),
    hval4, hint4.trans hab_int3, hkeep4⟩

private lemma link_prealloc_zeroSub
    {w h L b hp_caller pos : ℕ} {cost0 : ℤ}
    {p : Program} {lp : LctProcs} {ω : ℕ → Bool} {mem4 : ℕ → ℕ} {regs : ℕ → ℕ}
    (hz_ok : MeetsContract w p lp.splay.numZero (zeroContract w h))
    (hsub_ok : MeetsContract w p lp.splay.numSub (subtractContract w h))
    (hL_w : L < 2 ^ w) (heff_w : hp_caller + 7 * L < 2 ^ w) (h14000 : 14000 < 2 ^ w)
    (hbh_lt : b + LCT_HDR_HP < 2 ^ w) (hbh_eq : b + LCT_HDR_HP = lctNodesBase b - 1)
    (hr0 : regs 0 = b) (hr9 : regs 9 = L) (hr13 : regs 13 = hp_caller)
    (hr17 : regs 17 = hp_caller + 4 * L) (hr18 : regs 18 = hp_caller + 5 * L)
    (hr20 : regs 20 = hp_caller + 7 * L)
    (hz4 : ZeroFrom mem4 (hp_caller + 4 * L))
    (hval_cf : Valid mem4 hp_caller h L) (hint_cf : intVal mem4 hp_caller h L = cost0) :
    ∃ mem_pre regs_zs pos_zs c_zs,
      Runs w p ω (lctLinkZeroSubBody lp) { mem := mem4, regs := regs, pos := pos } .normal
        { mem := Function.update mem_pre (lctNodesBase b - 1) (hp_caller + 7 * L),
          regs := regs_zs, pos := pos_zs } c_zs ∧
      c_zs ≤ 74 * L + 65 ∧
      ZeroFrom mem_pre (hp_caller + 7 * L) ∧
      (∀ a < hp_caller + 4 * L, mem_pre a = mem4 a) ∧
      Valid mem_pre (hp_caller + 6 * L) h L ∧
      intVal mem_pre (hp_caller + 6 * L) h L = wrap h L (-cost0) ∧
      (∀ r' ≠ 25, regs_zs r' = regs r') := by
  have hlt4 : hp_caller + 4 * L < 2 ^ w := by omega
  have hlt5 : hp_caller + 5 * L < 2 ^ w := by omega
  have heval_z : evalArgs w { mem := mem4, regs := regs, pos := pos } [.reg 9, .reg 17] =
      some [L, hp_caller + 4 * L] := by
    simp [evalArgs, Expr.eval_reg, hr9, hr17]
  have hz_args_w : ∀ a ∈ ([L, hp_caller + 4 * L] : List ℕ), a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> [exact hL_w; exact hlt4]
  have hha_z : heapArg [L, hp_caller + 4 * L] = hp_caller + 4 * L := rfl
  have hpre_z : (zeroContract w h).pre [L, hp_caller + 4 * L] mem4 := by
    refine ⟨⟨L, hp_caller + 4 * L, rfl⟩, ?_, ?_⟩
    · rw [hha_z]; exact hz4
    · rw [hha_z]; change hp_caller + 4 * L + L < 2 ^ w; omega
  rcases runs_call_of_meetsContract (r := 25) hz_ok heval_z hz_args_w hpre_z ω with
    ⟨stz, cz, w_z, hrun_z, ⟨hwz_eq, _, _, hz_below, hz_from, hval_z, hint_z⟩, _, hreg_z, hc_z⟩
  have hwz_val : w_z = hp_caller + 5 * L := by
    rw [hwz_eq, hha_z]; change hp_caller + 4 * L + L = hp_caller + 5 * L; omega
  rw [hwz_val] at hz_from
  change Valid stz.mem (heapArg [L, hp_caller + 4 * L]) h L at hval_z
  change intVal stz.mem (heapArg [L, hp_caller + 4 * L]) h L = 0 at hint_z
  rw [hha_z] at hval_z hint_z
  have hcf_z_blk : ∀ i < L, stz.mem (hp_caller + i) = mem4 (hp_caller + i) := fun i hi =>
    hz_below (hp_caller + i) (by rw [hha_z]; exact lt_of_lt_of_le (Nat.add_lt_add_left hi _) (by omega))
  have hval_cf_z : Valid stz.mem hp_caller h L := fun i hi => by
    rw [hcf_z_blk i hi]; exact hval_cf i hi
  have hint_cf_z : intVal stz.mem hp_caller h L = cost0 :=
    (intVal_agree_block hcf_z_blk).trans hint_cf
  have heval_sub : evalArgs w stz [.reg 17, .reg 13, .reg 9, .reg 18] =
      some [hp_caller + 4 * L, hp_caller, L, hp_caller + 5 * L] := by
    simp [evalArgs, Expr.eval_reg, hreg_z 17 (by decide), hr17, hreg_z 13 (by decide), hr13,
      hreg_z 9 (by decide), hr9, hreg_z 18 (by decide), hr18]
  have hsub_args_w : ∀ a ∈ ([hp_caller + 4 * L, hp_caller, L, hp_caller + 5 * L] : List ℕ),
      a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> [exact hlt4; omega; exact hL_w; exact hlt5]
  have hha_sub : heapArg [hp_caller + 4 * L, hp_caller, L, hp_caller + 5 * L] = hp_caller + 5 * L := rfl
  have hpre_sub : (subtractContract w h).pre
      [hp_caller + 4 * L, hp_caller, L, hp_caller + 5 * L] stz.mem := by
    refine ⟨⟨hp_caller + 4 * L, hp_caller, L, hp_caller + 5 * L, rfl, by omega, by omega,
      hval_z, hval_cf_z⟩, ?_, ?_⟩
    · rw [hha_sub]; exact hz_from
    · rw [hha_sub]; change (hp_caller + 5 * L) + 2 * L < 2 ^ w; omega
  rcases runs_call_of_meetsContract (r := 25) hsub_ok heval_sub hsub_args_w hpre_sub ω with
    ⟨stsub, csub, w_sub, hrun_sub, ⟨hwsub_eq, _, _, hsub_below, hsub_from, hval_cb, hint_cb⟩, _,
      hreg_sub, hc_sub⟩
  have hwsub_val : w_sub = hp_caller + 7 * L := by
    rw [hwsub_eq, hha_sub]; change (hp_caller + 5 * L) + 2 * L = hp_caller + 7 * L; omega
  rw [hwsub_val] at hsub_from
  have hkeep_sub : ∀ r' ≠ 25, stsub.regs r' = regs r' := fun r' hr' =>
    (hreg_sub r' hr').trans (hreg_z r' hr')
  have hp_lt : LCT_HDR_HP < 2 ^ w := by unfold LCT_HDR_HP; omega
  have hstore_hp :
      Runs w p ω (.store (.bin .add (.reg 0) (.const LCT_HDR_HP)) (.reg 20)) stsub .normal
        { mem := Function.update stsub.mem (lctNodesBase b - 1) (hp_caller + 7 * L),
          regs := stsub.regs, pos := stsub.pos } 5 := by
    refine runs_store_iff.2 ⟨lctNodesBase b - 1, hp_caller + 7 * L, ?_,
      by simp [Expr.eval_reg, hkeep_sub 20 (by decide), hr20],
      rfl, rfl, by simp [Expr.size]⟩
    rw [← hbh_eq]
    exact Expr.eval_add (by simp [Expr.eval_reg, hkeep_sub 0 (by decide), hr0])
      (Expr.eval_const hp_lt) hbh_lt
  have hrun_zs : Runs w p ω (lctLinkZeroSubBody lp) { mem := mem4, regs := regs, pos := pos } .normal
      { mem := Function.update stsub.mem (lctNodesBase b - 1) (hp_caller + 7 * L),
        regs := stsub.regs, pos := stsub.pos } (cz + (csub + 5 + 1) + 1) := by
    dsimp only [lctLinkZeroSubBody]
    exact link_runs_seq_normal hrun_z (link_runs_seq_normal hrun_sub hstore_hp)
  have hpre_below : ∀ a < hp_caller + 4 * L, stsub.mem a = mem4 a := fun a ha => by
    have ha5 : a < heapArg [hp_caller + 4 * L, hp_caller, L, hp_caller + 5 * L] := by
      rw [hha_sub]; omega
    have ha4 : a < heapArg [L, hp_caller + 4 * L] := by rw [hha_z]; exact ha
    exact (hsub_below a ha5).trans (hz_below a ha4)
  have h6L : heapArg [hp_caller + 4 * L, hp_caller, L, hp_caller + 5 * L] +
      ([hp_caller + 4 * L, hp_caller, L, hp_caller + 5 * L] : List ℕ).getD 2 0 =
      hp_caller + 6 * L := by
    rw [hha_sub]; change (hp_caller + 5 * L) + L = hp_caller + 6 * L; omega
  have hval_cb_sub : Valid stsub.mem (hp_caller + 6 * L) h L := by rw [← h6L]; exact hval_cb
  have hint_cb_sub : intVal stsub.mem (hp_caller + 6 * L) h L = wrap h L (-cost0) := by
    have hcb0 : intVal stsub.mem (hp_caller + 6 * L) h L =
        wrap h L (intVal stz.mem (hp_caller + 4 * L) h L - intVal stz.mem hp_caller h L) := by
      rw [← h6L]; exact hint_cb
    rw [hcb0, hint_z, zero_sub, hint_cf_z]
  have hcz_le : cz ≤ 7 := by
    have hsz : argsSize [.reg 9, .reg 17] = 2 := by decide
    have hcost : (zeroContract w h).cost [L, hp_caller + 4 * L] mem4 = 4 := rfl
    rw [hsz, hcost] at hc_z; exact hc_z
  have hcsub_le : csub ≤ 74 * L + 47 := by
    have hsz : argsSize [.reg 17, .reg 13, .reg 9, .reg 18] = 4 := by decide
    have hcost : (subtractContract w h).cost [hp_caller + 4 * L, hp_caller, L, hp_caller + 5 * L]
        stz.mem = 74 * L + 42 := rfl
    rw [hsz, hcost] at hc_sub; omega
  exact ⟨stsub.mem, stsub.regs, stsub.pos, _, hrun_zs, link_pa_zs_cost hcz_le hcsub_le,
    hsub_from, hpre_below, hval_cb_sub, hint_cb_sub, hkeep_sub⟩

theorem link_prealloc_runs {w h L P b u v eid cPtr fPtr afPtr abPtr hp_caller pos : ℕ}
    {p : Program} {lp : LctProcs} {ω : ℕ → Bool} {F : MathForest} {x₀ : LctConc}
    {e : ForestEdge} {mem₀ : ℕ → ℕ}
    (hp_base : LctBaseOk w h L P p lp)
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hu : u < F.n) (hv : v < F.n)
    (hc_valid : Valid mem₀ cPtr h L) (hc_bd : cPtr + L ≤ hp_caller) (hc_val : intVal mem₀ cPtr h L = e.cost)
    (hf_valid : Valid mem₀ fPtr h L) (hf_bd : fPtr + L ≤ hp_caller)
    (hf_val : ((intVal mem₀ fPtr h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.flow)
    (haf_valid : Valid mem₀ afPtr h L) (haf_bd : afPtr + L ≤ hp_caller)
    (haf_val : ((intVal mem₀ afPtr h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.availFwd)
    (hab_valid : Valid mem₀ abPtr h L) (hab_bd : abPtr + L ≤ hp_caller)
    (hab_val : ((intVal mem₀ abPtr h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.availBwd)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hz₀ : ZeroFrom mem₀ hp_caller)
    (heff_w : hp_caller + 7 * L < 2 ^ w) (h14000 : 14000 < 2 ^ w) :
    let nb := lctNodesBase b
    let hp_eff := hp_caller + 7 * L
    ∃ mem_pre regs_pa pos_pa c_pa,
      Runs w p ω (lctLinkPreallocBody lp)
        (startState [b, u, v, eid, cPtr, fPtr, afPtr, abPtr, hp_caller] mem₀ pos) .normal
        { mem := Function.update mem_pre (nb - 1) hp_eff, regs := regs_pa, pos := pos_pa } c_pa ∧
      c_pa ≤ 150 * L + 210 ∧
      ZeroFrom mem_pre hp_eff ∧
      (∀ a, a < hp_caller ∨ hp_eff ≤ a → mem_pre a = mem₀ a) ∧
      LctMemRep w h L P b F x₀ mem_pre ∧
      lctPhi L mem_pre b F.n = lctPhi L mem₀ b F.n ∧
      Valid mem_pre hp_caller h L ∧ intVal mem_pre hp_caller h L = e.cost ∧
      Valid mem_pre (hp_caller + 6 * L) h L ∧
      intVal mem_pre (hp_caller + 6 * L) h L = wrap h L (-e.cost) ∧
      Valid mem_pre (hp_caller + L) h L ∧
      ((intVal mem_pre (hp_caller + L) h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.flow ∧
      Valid mem_pre (hp_caller + 2 * L) h L ∧
      ((intVal mem_pre (hp_caller + 2 * L) h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.availFwd ∧
      Valid mem_pre (hp_caller + 3 * L) h L ∧
      ((intVal mem_pre (hp_caller + 3 * L) h L : ℤ) : ℚ) / (2 : ℚ) ^ P = e.availBwd ∧
      regs_pa 0 = b ∧ regs_pa 1 = u ∧ regs_pa 2 = v ∧ regs_pa 3 = eid ∧
      regs_pa 9 = L ∧ regs_pa 10 = nb ∧ regs_pa 11 = u + 1 ∧ regs_pa 12 = v + 1 ∧
      regs_pa 13 = hp_caller ∧ regs_pa 14 = hp_caller + L ∧
      regs_pa 15 = hp_caller + 2 * L ∧ regs_pa 16 = hp_caller + 3 * L ∧
      regs_pa 19 = hp_caller + 6 * L ∧ regs_pa 20 = hp_eff := by
  intro nb hp_eff
  have harena : lctArenaHi b (lctCap F.n) ≤ hp_caller := by
    have hlt := b_lt_lctArenaHi b (lctCap F.n)
    have hpos : 0 < lctArenaHi b (lctCap F.n) := lt_of_le_of_lt (Nat.zero_le b) hlt
    have hx0n : x₀.n = F.n := hrep₀.2.2.2.2.1
    have hf := hfoot (lctArenaHi b (lctCap F.n) - 1)
      (lctFoot_arena (x := x₀) (by omega) (by rw [hx0n]; exact Nat.sub_lt hpos (by decide)))
    omega
  have hucap : u + 1 ≤ lctCap F.n := by unfold lctCap; omega
  have hvcap : v + 1 ≤ lctCap F.n := by unfold lctCap; omega
  have hbh_lt : b + LCT_HDR_HP < 2 ^ w := by
    unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE at harena
    unfold LCT_HDR_HP; omega
  have hbh_eq : b + LCT_HDR_HP = nb - 1 := by
    dsimp only [nb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_HP; omega
  rcases link_setupRegs_runs (mem := mem₀) (regs0 := fun i =>
      ([b, u, v, eid, cPtr, fPtr, afPtr, abPtr, hp_caller] : List ℕ).getD i 0)
      (p := p) (ω := ω) (pos := pos)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl hrep₀.2.2.2.2.2.2.2.2.2.2.2.1
      harena hucap hvcap heff_w h14000 with
    ⟨r1, c_sr, hrun_sr, hc_sr, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hr7, _, hr9, hr10, hr11, hr12,
      hr13, hr14, hr15, hr16, hr17, hr18, hr19, hr20⟩
  rcases link_prealloc_copy4 hp_base.copyWords_ok (by omega : 1 < 2 ^ w) hp_base.hL heff_w
      hc_valid hc_bd hf_valid hf_bd haf_valid haf_bd hab_valid hab_bd
      hr4 hr5 hr6 hr7 hr9 hr13 hr14 hr15 hr16 with
    ⟨st4, c_cp, hrun_cp, hc_cp, hbelow4, hhi4, hval_cf4, hint_cf4, hval_fl4, hint_fl4,
      hval_af4, hint_af4, hval_ab4, hint_ab4, hkeep4⟩
  have hz4 : ZeroFrom st4.mem (hp_caller + 4 * L) := fun a ha =>
    (hhi4 a ha).trans (hz₀ a (le_trans (Nat.le_add_right hp_caller (4 * L)) ha))
  rcases link_prealloc_zeroSub hp_base.splay_ok.zero_ok hp_base.splay_ok.sub_ok hp_base.hL heff_w
      h14000 hbh_lt hbh_eq ((hkeep4 0 (by decide)).trans hr0) ((hkeep4 9 (by decide)).trans hr9)
      ((hkeep4 13 (by decide)).trans hr13) ((hkeep4 17 (by decide)).trans hr17)
      ((hkeep4 18 (by decide)).trans hr18) ((hkeep4 20 (by decide)).trans hr20)
      hz4 hval_cf4 (hint_cf4.trans hc_val) with
    ⟨mem_pre, regs_pa, pos_pa, c_zs, hrun_zs, hc_zs, hz_eff, hpre_below, hval_cb_sub, hint_cb_sub,
      hkeep_zs⟩
  have hkeep_all : ∀ r' ≠ 25, regs_pa r' = r1 r' := fun r' hr' =>
    (hkeep_zs r' hr').trans (hkeep4 r' hr')
  have hfull_run : Runs w p ω (lctLinkPreallocBody lp)
      (startState [b, u, v, eid, cPtr, fPtr, afPtr, abPtr, hp_caller] mem₀ pos) .normal
      { mem := Function.update mem_pre (nb - 1) hp_eff, regs := regs_pa, pos := pos_pa }
      (c_sr + (c_cp + c_zs + 1) + 1) := by
    dsimp only [lctLinkPreallocBody]
    exact link_runs_seq_normal hrun_sr (link_runs_seq_normal hrun_cp hrun_zs)
  have hpre_lt : ∀ a < hp_caller, mem_pre a = mem₀ a := fun a ha =>
    (hpre_below a (lt_of_lt_of_le ha (Nat.le_add_right hp_caller (4 * L)))).trans (hbelow4 a ha)
  have hagree : ∀ a, a < hp_caller ∨ hp_eff ≤ a → mem_pre a = mem₀ a := by
    rintro a (ha | ha)
    · exact hpre_lt a ha
    · exact (hz_eff a ha).trans (hz₀ a (le_trans (Nat.le_add_right hp_caller (7 * L)) ha)).symm
  have hloc := lctDSRep_local w h L P b F x₀ mem₀ mem_pre
    (fun a ha => (hpre_lt a (hfoot a ha)).symm)
  have hphi_eq : lctPhi L mem_pre b F.n = lctPhi L mem₀ b F.n := by
    have h2 := hloc.2.symm
    dsimp only [lctDSRep] at h2
    rwa [hrep₀.2.2.2.2.1] at h2
  have hblk_lt4 : ∀ k ≤ 3, ∀ i < L, hp_caller + k * L + i < hp_caller + 4 * L := by
    intro k hk i hi
    have h1 : hp_caller + k * L + i < hp_caller + (k + 1) * L := by
      have : (k + 1) * L = k * L + L := Nat.succ_mul k L
      rw [this, ← Nat.add_assoc]
      exact Nat.add_lt_add_left hi _
    exact lt_of_lt_of_le h1 (link_pa_off_le (Nat.succ_le_of_lt (Nat.lt_succ_of_le hk)))
  have hcf_blk : ∀ i < L, mem_pre (hp_caller + i) = st4.mem (hp_caller + i) := fun i hi =>
    hpre_below _ (by simpa using hblk_lt4 0 (by decide) i hi)
  have hfl_blk : ∀ i < L, mem_pre (hp_caller + L + i) = st4.mem (hp_caller + L + i) := fun i hi =>
    hpre_below _ (by simpa using hblk_lt4 1 (by decide) i hi)
  have haf_blk : ∀ i < L, mem_pre (hp_caller + 2 * L + i) = st4.mem (hp_caller + 2 * L + i) :=
    fun i hi => hpre_below _ (hblk_lt4 2 (by decide) i hi)
  have hab_blk : ∀ i < L, mem_pre (hp_caller + 3 * L + i) = st4.mem (hp_caller + 3 * L + i) :=
    fun i hi => hpre_below _ (hblk_lt4 3 (by decide) i hi)
  refine ⟨mem_pre, regs_pa, pos_pa, _, hfull_run, link_pa_total_cost hc_sr hc_cp hc_zs,
    hz_eff, hagree, hloc.1 hrep₀, hphi_eq,
    fun i hi => by rw [hcf_blk i hi]; exact hval_cf4 i hi,
    (intVal_agree_block hcf_blk).trans (hint_cf4.trans hc_val),
    hval_cb_sub, hint_cb_sub,
    fun i hi => by rw [hfl_blk i hi]; exact hval_fl4 i hi,
    by rw [intVal_agree_block hfl_blk, hint_fl4, hf_val],
    fun i hi => by rw [haf_blk i hi]; exact hval_af4 i hi,
    by rw [intVal_agree_block haf_blk, hint_af4, haf_val],
    fun i hi => by rw [hab_blk i hi]; exact hval_ab4 i hi,
    by rw [intVal_agree_block hab_blk, hint_ab4, hab_val],
    (hkeep_all 0 (by decide)).trans hr0, (hkeep_all 1 (by decide)).trans hr1,
    (hkeep_all 2 (by decide)).trans hr2, (hkeep_all 3 (by decide)).trans hr3,
    (hkeep_all 9 (by decide)).trans hr9, (hkeep_all 10 (by decide)).trans hr10,
    (hkeep_all 11 (by decide)).trans hr11, (hkeep_all 12 (by decide)).trans hr12,
    (hkeep_all 13 (by decide)).trans hr13, (hkeep_all 14 (by decide)).trans hr14,
    (hkeep_all 15 (by decide)).trans hr15, (hkeep_all 16 (by decide)).trans hr16,
    (hkeep_all 19 (by decide)).trans hr19, (hkeep_all 20 (by decide)).trans hr20⟩

theorem link_splice_runs {w b nb cap u v eid p_cf p_cb p_fl p_af p_ab ed nextFree pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {regs : ℕ → ℕ} {mem₃ : ℕ → ℕ}
    (hr0 : regs 0 = b) (hr1 : regs 1 = u) (hr2 : regs 2 = v) (hr3 : regs 3 = eid)
    (hr10 : regs 10 = nb) (hr11 : regs 11 = u + 1) (hr12 : regs 12 = v + 1)
    (hr13 : regs 13 = p_cf) (hr14 : regs 14 = p_fl) (hr15 : regs 15 = p_af)
    (hr16 : regs 16 = p_ab) (hr19 : regs 19 = p_cb)
    (hnb : nb = lctNodesBase b)
    (hfree_hdr : mem₃ (b + LCT_HDR_FREE) = ed)
    (hnext_free : nodeField mem₃ nb ed OFF_EU = nextFree)
    (harena : nb + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hed_bd : 1 ≤ ed ∧ ed ≤ cap) (hu_bd : u + 1 ≤ cap)
    (h14000 : 14000 < 2 ^ w) :
    ∃ regs_sp c_sp,
      Runs w p ω lctLinkSpliceBody { mem := mem₃, regs := regs, pos := pos } .normal
        { mem := lctLinkWriteMem mem₃ nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed,
          regs := regs_sp, pos := pos } c_sp ∧
      c_sp ≤ 200 ∧
      regs_sp 0 = b ∧ regs_sp 10 = nb ∧ regs_sp 21 = ed := by
  have hns_w : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE; omega
  have hfree_lt : LCT_HDR_FREE < 2 ^ w := by unfold LCT_HDR_FREE; omega
  have hfree_add : b + LCT_HDR_FREE < 2 ^ w := by
    have : b + LCT_HDR_FREE < nb := by rw [hnb]; unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_FREE; omega
    have : nb ≤ nb + NODE_STRIDE * (cap + 1) := Nat.le_add_right _ _
    omega
  have hed_mul_w : NODE_STRIDE * ed < 2 ^ w := by
    have h1 : NODE_STRIDE * ed ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hed_base_w : nb + NODE_STRIDE * ed < 2 ^ w := by
    have h1 : NODE_STRIDE * ed ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have heu_w : OFF_EU < 2 ^ w := by unfold OFF_EU; omega
  have hed_eu_w : nb + NODE_STRIDE * ed + OFF_EU < 2 ^ w := by
    have h1 : OFF_EU < NODE_STRIDE := by unfold OFF_EU NODE_STRIDE; omega
    have h2 : NODE_STRIDE * ed + OFF_EU < NODE_STRIDE * (cap + 1) := by
      have hm := Nat.mul_le_mul_left NODE_STRIDE (by omega : ed + 1 ≤ cap + 1)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
    omega
  have hu_mul_w : NODE_STRIDE * (u + 1) < 2 ^ w := by
    have h1 : NODE_STRIDE * (u + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hu_base_w : nb + NODE_STRIDE * (u + 1) < 2 ^ w := by
    have h1 : NODE_STRIDE * (u + 1) ≤ NODE_STRIDE * (cap + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hpar_w : OFF_PARENT < 2 ^ w := by unfold OFF_PARENT; omega
  have hu_par_w : nb + NODE_STRIDE * (u + 1) + OFF_PARENT < 2 ^ w := by
    have h1 : OFF_PARENT < NODE_STRIDE := by unfold OFF_PARENT NODE_STRIDE; omega
    have h2 : NODE_STRIDE * (u + 1) + OFF_PARENT < NODE_STRIDE * (cap + 1) := by
      have hm := Nat.mul_le_mul_left NODE_STRIDE (by omega : (u + 1) + 1 ≤ cap + 1)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
    omega
  have step21 :
      Runs w p ω (.assign 21 (.load (.bin .add (.reg 0) (.const LCT_HDR_FREE))))
        { mem := mem₃, regs := regs, pos := pos } .normal
        { mem := mem₃, regs := Function.update regs 21 ed, pos := pos } 5 :=
    runs_assign_iff.2 ⟨ed, Expr.eval_load_mem (Expr.eval_add (by simp [Expr.eval_reg, hr0])
      (Expr.eval_const hfree_lt) hfree_add) (by simpa using hfree_hdr), rfl, rfl,
      by simp [Expr.size]⟩
  set r21 := Function.update regs 21 ed
  have step22 :
      Runs w p ω (.assign 22 (.bin .add (.reg 10) (.bin .mul (.const NODE_STRIDE) (.reg 21))))
        { mem := mem₃, regs := r21, pos := pos } .normal
        { mem := mem₃, regs := Function.update r21 22 (nb + NODE_STRIDE * ed), pos := pos } 6 :=
    runs_assign_iff.2 ⟨nb + NODE_STRIDE * ed,
      Expr.eval_add (by simp [r21, Expr.eval_reg, hr10])
        (Expr.eval_mul (Expr.eval_const hns_w) (by simp [r21, Expr.eval_reg]) hed_mul_w)
        hed_base_w,
      rfl, rfl, by simp [Expr.size]⟩
  set r22 := Function.update r21 22 (nb + NODE_STRIDE * ed)
  have step23 :
      Runs w p ω (.assign 23 (.load (.bin .add (.reg 22) (.const OFF_EU))))
        { mem := mem₃, regs := r22, pos := pos } .normal
        { mem := mem₃, regs := Function.update r22 23 nextFree, pos := pos } 5 :=
    runs_assign_iff.2 ⟨nextFree, Expr.eval_load_mem (Expr.eval_add (by simp [r22, Expr.eval_reg])
      (Expr.eval_const heu_w) hed_eu_w) (by simpa [nodeField] using hnext_free), rfl, rfl,
      by simp [Expr.size]⟩
  set r23 := Function.update r22 23 nextFree
  have step_free :
      Runs w p ω (.store (.bin .add (.reg 0) (.const LCT_HDR_FREE)) (.reg 23))
        { mem := mem₃, regs := r23, pos := pos } .normal
        { mem := Function.update mem₃ (b + LCT_HDR_FREE) nextFree, regs := r23, pos := pos } 5 :=
    runs_store_iff.2 ⟨b + LCT_HDR_FREE, nextFree,
      Expr.eval_add (by simp [r23, r22, r21, Expr.eval_reg, hr0])
        (Expr.eval_const hfree_lt) hfree_add,
      by simp [r23, Expr.eval_reg], rfl, rfl, by simp [Expr.size]⟩
  set mem_free := Function.update mem₃ (b + LCT_HDR_FREE) nextFree
  let offPairs : List (ℕ × (Expr × ℕ)) :=
    [(OFF_LEFT, (.const 0, 0)),
     (OFF_RIGHT, (.reg 11, u + 1)),
     (OFF_PARENT, (.const 0, 0)),
     (OFF_PPAR, (.reg 12, v + 1)),
     (OFF_REV, (.const 0, 0)),
     (OFF_ISV, (.const 0, 0)),
     (OFF_HASE, (.const 1, 1)),
     (OFF_DIR, (.const 0, 0)),
     (OFF_HAS_TAG, (.const 0, 0)),
     (OFF_TAG_PTR, (.const 0, 0)),
     (OFF_TAG_NEG, (.const 0, 0)),
     (OFF_EID, (.reg 3, eid)),
     (OFF_EU, (.reg 1, u)),
     (OFF_EV, (.reg 2, v)),
     (OFF_COST_FWD, (.reg 19, p_cb)),
     (OFF_COST_BWD, (.reg 13, p_cf)),
     (OFF_FLOW_PTR, (.reg 14, p_fl)),
     (OFF_AF_PTR, (.reg 16, p_ab)),
     (OFF_AB_PTR, (.reg 15, p_af))]
  have hoff_check : ∀ q ∈ offPairs,
      q.1 < 2 ^ w ∧ nb + NODE_STRIDE * ed + q.1 < 2 ^ w ∧
      ∀ mem, Expr.eval w { mem := mem, regs := r23, pos := pos } q.2.1 = some q.2.2 := by
    have h0w : 0 < 2 ^ w := by omega
    have h1w : 1 < 2 ^ w := by omega
    have hbd_off : ∀ off, off < NODE_STRIDE →
        off < 2 ^ w ∧ nb + NODE_STRIDE * ed + off < 2 ^ w := fun off hoff => by
      have hm := Nat.mul_le_mul_left NODE_STRIDE (by omega : ed + 1 ≤ cap + 1)
      rw [Nat.mul_add, Nat.mul_one] at hm
      exact ⟨by omega, by omega⟩
    intro q hq
    simp only [offPairs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(hbd_off OFF_LEFT (by unfold OFF_LEFT NODE_STRIDE; omega)).1,
        (hbd_off OFF_LEFT (by unfold OFF_LEFT NODE_STRIDE; omega)).2, fun _ => Expr.eval_const h0w⟩
    · exact ⟨(hbd_off OFF_RIGHT (by unfold OFF_RIGHT NODE_STRIDE; omega)).1,
        (hbd_off OFF_RIGHT (by unfold OFF_RIGHT NODE_STRIDE; omega)).2,
        fun _ => by simp [r23, r22, r21, Expr.eval_reg, hr11]⟩
    · exact ⟨(hbd_off OFF_PARENT (by unfold OFF_PARENT NODE_STRIDE; omega)).1,
        (hbd_off OFF_PARENT (by unfold OFF_PARENT NODE_STRIDE; omega)).2, fun _ => Expr.eval_const h0w⟩
    · exact ⟨(hbd_off OFF_PPAR (by unfold OFF_PPAR NODE_STRIDE; omega)).1,
        (hbd_off OFF_PPAR (by unfold OFF_PPAR NODE_STRIDE; omega)).2,
        fun _ => by simp [r23, r22, r21, Expr.eval_reg, hr12]⟩
    · exact ⟨(hbd_off OFF_REV (by unfold OFF_REV NODE_STRIDE; omega)).1,
        (hbd_off OFF_REV (by unfold OFF_REV NODE_STRIDE; omega)).2, fun _ => Expr.eval_const h0w⟩
    · exact ⟨(hbd_off OFF_ISV (by unfold OFF_ISV NODE_STRIDE; omega)).1,
        (hbd_off OFF_ISV (by unfold OFF_ISV NODE_STRIDE; omega)).2, fun _ => Expr.eval_const h0w⟩
    · exact ⟨(hbd_off OFF_HASE (by unfold OFF_HASE NODE_STRIDE; omega)).1,
        (hbd_off OFF_HASE (by unfold OFF_HASE NODE_STRIDE; omega)).2, fun _ => Expr.eval_const h1w⟩
    · exact ⟨(hbd_off OFF_DIR (by unfold OFF_DIR NODE_STRIDE; omega)).1,
        (hbd_off OFF_DIR (by unfold OFF_DIR NODE_STRIDE; omega)).2, fun _ => Expr.eval_const h0w⟩
    · exact ⟨(hbd_off OFF_HAS_TAG (by unfold OFF_HAS_TAG NODE_STRIDE; omega)).1,
        (hbd_off OFF_HAS_TAG (by unfold OFF_HAS_TAG NODE_STRIDE; omega)).2, fun _ => Expr.eval_const h0w⟩
    · exact ⟨(hbd_off OFF_TAG_PTR (by unfold OFF_TAG_PTR NODE_STRIDE; omega)).1,
        (hbd_off OFF_TAG_PTR (by unfold OFF_TAG_PTR NODE_STRIDE; omega)).2, fun _ => Expr.eval_const h0w⟩
    · exact ⟨(hbd_off OFF_TAG_NEG (by unfold OFF_TAG_NEG NODE_STRIDE; omega)).1,
        (hbd_off OFF_TAG_NEG (by unfold OFF_TAG_NEG NODE_STRIDE; omega)).2, fun _ => Expr.eval_const h0w⟩
    · exact ⟨(hbd_off OFF_EID (by unfold OFF_EID NODE_STRIDE; omega)).1,
        (hbd_off OFF_EID (by unfold OFF_EID NODE_STRIDE; omega)).2,
        fun _ => by simp [r23, r22, r21, Expr.eval_reg, hr3]⟩
    · exact ⟨(hbd_off OFF_EU (by unfold OFF_EU NODE_STRIDE; omega)).1,
        (hbd_off OFF_EU (by unfold OFF_EU NODE_STRIDE; omega)).2,
        fun _ => by simp [r23, r22, r21, Expr.eval_reg, hr1]⟩
    · exact ⟨(hbd_off OFF_EV (by unfold OFF_EV NODE_STRIDE; omega)).1,
        (hbd_off OFF_EV (by unfold OFF_EV NODE_STRIDE; omega)).2,
        fun _ => by simp [r23, r22, r21, Expr.eval_reg, hr2]⟩
    · exact ⟨(hbd_off OFF_COST_FWD (by unfold OFF_COST_FWD NODE_STRIDE; omega)).1,
        (hbd_off OFF_COST_FWD (by unfold OFF_COST_FWD NODE_STRIDE; omega)).2,
        fun _ => by simp [r23, r22, r21, Expr.eval_reg, hr19]⟩
    · exact ⟨(hbd_off OFF_COST_BWD (by unfold OFF_COST_BWD NODE_STRIDE; omega)).1,
        (hbd_off OFF_COST_BWD (by unfold OFF_COST_BWD NODE_STRIDE; omega)).2,
        fun _ => by simp [r23, r22, r21, Expr.eval_reg, hr13]⟩
    · exact ⟨(hbd_off OFF_FLOW_PTR (by unfold OFF_FLOW_PTR NODE_STRIDE; omega)).1,
        (hbd_off OFF_FLOW_PTR (by unfold OFF_FLOW_PTR NODE_STRIDE; omega)).2,
        fun _ => by simp [r23, r22, r21, Expr.eval_reg, hr14]⟩
    · exact ⟨(hbd_off OFF_AF_PTR (by unfold OFF_AF_PTR NODE_STRIDE; omega)).1,
        (hbd_off OFF_AF_PTR (by unfold OFF_AF_PTR NODE_STRIDE; omega)).2,
        fun _ => by simp [r23, r22, r21, Expr.eval_reg, hr16]⟩
    · exact ⟨(hbd_off OFF_AB_PTR (by unfold OFF_AB_PTR NODE_STRIDE; omega)).1,
        (hbd_off OFF_AB_PTR (by unfold OFF_AB_PTR NODE_STRIDE; omega)).2,
        fun _ => by simp [r23, r22, r21, Expr.eval_reg, hr15]⟩
  rcases storeNodeOffsExprStmt_runs (p := p) (ω := ω) (addrExpr := .reg 22) (regs := r23)
      (pos := pos) (fun _ => by simp [r23, r22, Expr.eval_reg]) offPairs hoff_check mem_free with
    ⟨c_offs, hrun_offs, hc_offs⟩
  have he_map : offPairs.map (fun q => (q.1, q.2.1)) =
      lctLinkOffPairsExpr 1 11 2 12 3 13 19 14 15 16 := rfl
  have hv_map : offPairs.map (fun q => (q.1, q.2.2)) =
      lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab := rfl
  rw [he_map] at hrun_offs
  rw [hv_map] at hrun_offs
  set mem_ed := writeNodeOffs mem_free nb ed (lctLinkOffPairs u v eid p_cf p_cb p_fl p_af p_ab)
  have step24 :
      Runs w p ω (.assign 24 (.bin .add (.reg 10) (.bin .mul (.const NODE_STRIDE) (.reg 11))))
        { mem := mem_ed, regs := r23, pos := pos } .normal
        { mem := mem_ed, regs := Function.update r23 24 (nb + NODE_STRIDE * (u + 1)), pos := pos } 6 :=
    runs_assign_iff.2 ⟨nb + NODE_STRIDE * (u + 1),
      Expr.eval_add (by simp [r23, r22, r21, Expr.eval_reg, hr10])
        (Expr.eval_mul (Expr.eval_const hns_w) (by simp [r23, r22, r21, Expr.eval_reg, hr11]) hu_mul_w)
        hu_base_w,
      rfl, rfl, by simp [Expr.size]⟩
  set r24 := Function.update r23 24 (nb + NODE_STRIDE * (u + 1))
  have step_par :
      Runs w p ω (.store (.bin .add (.reg 24) (.const OFF_PARENT)) (.reg 21))
        { mem := mem_ed, regs := r24, pos := pos } .normal
        { mem := Function.update mem_ed (nb + NODE_STRIDE * (u + 1) + OFF_PARENT) ed,
          regs := r24, pos := pos } 5 :=
    runs_store_iff.2 ⟨nb + NODE_STRIDE * (u + 1) + OFF_PARENT, ed,
      Expr.eval_add (by simp [r24, Expr.eval_reg]) (Expr.eval_const hpar_w) hu_par_w,
      by simp [r24, r23, r22, r21, Expr.eval_reg], rfl, rfl, by simp [Expr.size]⟩
  have hmem_fin :
      Function.update mem_ed (nb + NODE_STRIDE * (u + 1) + OFF_PARENT) ed =
      lctLinkWriteMem mem₃ nb b u v eid p_cf p_cb p_fl p_af p_ab nextFree ed := rfl
  have hrun_full := link_runs_seq_normal step21 (link_runs_seq_normal step22 (link_runs_seq_normal step23
    (link_runs_seq_normal step_free (link_runs_seq_normal hrun_offs (link_runs_seq_normal step24 step_par)))))
  rw [hmem_fin] at hrun_full
  have hc_offs' : c_offs ≤ 134 := by
    simp only [offPairs, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Expr.size] at hc_offs
    omega
  refine ⟨r24, _, hrun_full, by omega, ?_, ?_, ?_⟩ <;>
    simp [r24, r23, r22, r21, hr0, hr10]

end LinkExecutionHelpers

end MinCostFlow.LinkCut.Prog
