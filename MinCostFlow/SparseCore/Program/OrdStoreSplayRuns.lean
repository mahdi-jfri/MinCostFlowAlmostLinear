module

public import MinCostFlow.SparseCore.Program.OrdStoreSplay
import Mathlib.Tactic

/-!
# Run theorems for `ordSplayStepBody`, `ordSplayBody`, and `ordSplayRootBody`

This file proves the Word-RAM run theorems for `ordSplayStepBody`, `ordSplayBody`, and
`ordSplayRootBody`, showing that splaying a live node `x` of vertex `v` preserves `OrdInv`,
`OrdArenaAt`, and `OrdFrame`, updates `vRoot[v] := x`, and satisfies the Sleator–Tarjan amortized
cost bound `c + C_phi * sumTreePhi S' ≤ C_phi * sumTreePhi S + (3 * C_phi + 700) * ordStoreLog S.eCap`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.LinkCut SplayState

/-! ### Splay step, loop, and root-updating procedures -/

/-- `ordSplayStep` on `[nb, x]`: one zig, zig-zig, or zig-zag splay step. -/
def ordSplayStepBody (rotProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 2 (.load (.bin .add (ordRec 1) (.const 2))) ;;
     .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.const 0))
       (.assign 3 (ordRec 2) ;;
        .assign 4 (.load (.bin .add (.reg 3) (.const 2))) ;;
        .cond (.bin .eq (.reg 4) (.const 0))
          (.call 5 rotProc [.reg 0, .reg 1] ;; .ret (.const 0))
          (.assign 6 (.bin .eq (.reg 1) (.load (.reg 3))) ;;
           .assign 7 (.bin .eq (.reg 2) (.load (ordRec 4))) ;;
           .cond (.bin .eq (.reg 6) (.reg 7))
             (.call 5 rotProc [.reg 0, .reg 2])
             (.call 5 rotProc [.reg 0, .reg 1]) ;;
           .call 5 rotProc [.reg 0, .reg 1] ;;
           .ret (.const 0))))

theorem ordSplayStepBody_noRand (rotProc : ℕ) : (ordSplayStepBody rotProc).NoRand := by
  simp [ordSplayStepBody, ordRec, Stmt.NoRand]

/-- `ordSplay` on `[nb, x]`: splay `x` to the root of its auxiliary tree. -/
def ordSplayBody (stepProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.loop (.load (.bin .add (ordRec 1) (.const 2)))
      (.call 2 stepProc [.reg 0, .reg 1]) ;;
     .ret (.const 0))

theorem ordSplayBody_noRand (stepProc : ℕ) : (ordSplayBody stepProc).NoRand := by
  simp [ordSplayBody, ordRec, Stmt.NoRand]

/-- `ordSplayRoot` on `[b, x]`: splay live node `x` to the root of its vertex's tree, update
`vRoot[owner] := x`, and return `x.ppar` (`owner + 1`). -/
def ordSplayRootBody (splayProc : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 4))) ;;
  .call 3 splayProc [.reg 2, .reg 1] ;;
  .assign 4 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 8) (.reg 1))) (.const 3))) ;;
  .cond (.reg 4)
    (.assign 5 (.load (.bin .add (.reg 0) (.const 2))) ;;
     .store (.bin .add (.reg 5) (.bin .sub (.reg 4) (.const 1))) (.reg 1))
    .nop ;;
  .ret (.reg 4)

theorem ordSplayRootBody_noRand (splayProc : ℕ) : (ordSplayRootBody splayProc).NoRand := by
  simp [ordSplayRootBody, Stmt.NoRand]

def ORD_SPLAY_STEP_COST : ℕ := 600
def ORD_SPLAY_RATE : ℕ := 650

/-! ### Local `Runs` helpers -/

private theorem spr_runs_seq_normal {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {c₁ c₂ : ℕ}
    (h₁ : Runs w p ω s st .normal st₁ c₁) (h₂ : Runs w p ω t st₁ o st₂ c₂) :
    Runs w p ω (.seq s t) st o st₂ (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, h₂, rfl⟩)

private theorem spr_runs_seq_run_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st st₁ : State} {c₁ k T : ℕ} {Q : Outcome → State → Prop}
    (h₁ : Runs w p ω s st .normal st₁ c₁)
    (hrest : ∃ o st' c, Runs w p ω t st₁ o st' c ∧ Q o st' ∧ (k + c₁ + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s t) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c, h₂, hq, hc⟩ := hrest
  exact ⟨o, st', c₁ + c + 1, spr_runs_seq_normal h₁ h₂, hq, by omega⟩

private theorem spr_runs_loop_false {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st : State} (he : e.eval w st = some 0) :
    Runs w p ω (.loop e body) st .normal st (e.size + 1) :=
  runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩)

private theorem spr_runs_loop_true {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st st₁ st₂ : State} {o : Outcome} {v c₁ c₂ : ℕ}
    (he : e.eval w st = some v) (hv : v ≠ 0)
    (h₁ : Runs w p ω body st .normal st₁ c₁) (h₂ : Runs w p ω (.loop e body) st₁ o st₂ c₂) :
    Runs w p ω (.loop e body) st o st₂ (e.size + c₁ + c₂ + 1) :=
  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st₁, c₁, c₂, he, hv, h₁, h₂, rfl⟩))

private theorem spr_parentIn_rootId {t : AuxTree} (p₀ : ℕ) : t.parentIn t.rootId p₀ = p₀ := by
  cases t <;> simp [AuxTree.rootId, AuxTree.parentIn]

/-! ### `ordSplayStepBody_runs` -/

theorem ordSplayStepBody_runs {w nb cap x pos rotProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {st : SplayState ℕ Unit Unit} {nf : ℕ → ℕ} {t : AuxTree}
    (hnodes : OrdNodesAt mem nb cap st nf) (hok : OrdTreeOk cap st t)
    (hx : x ∈ t.toList) (hw : nb + 8 * (cap + 1) < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordSplayStepBody rotProc) (startState [nb, x] mem pos) o st' c ∧
      (OrdNodesAt st'.mem nb cap (SplayState.splayStep ordPayload st x) nf ∧
        ∀ a, ¬ InOrdNodes nb cap a → st'.mem a = mem a) ∧
      0 + c ≤ ORD_SPLAY_STEP_COST := by
  have hx0 : x ≠ 0 := SplayState.SubtreeInv_nonZero hok.inv.sub hx
  obtain ⟨hxc, -, -, hpc, -⟩ := hok.ptrs_le hx
  set pa := (st.nodes x).par with hpa
  have hm_x2 : mem (nb + 8 * x + 2) = pa := (hnodes x hxc).2.2.1
  unfold ordSplayStepBody
  rw [startState]
  wram_step
  wram_step; try dsimp only
  rw [hm_x2]
  wram_step
  · have hp0 : pa = 0 := hcond
    wram_step
    · refine ⟨?_, fun _ _ => rfl⟩
      simpa [SplayState.splayStep, hx0, ← hpa, hp0] using hnodes
    · unfold ORD_SPLAY_STEP_COST; wram_cost
  have hp0 : pa ≠ 0 := hcond
  have hp_mem : pa ∈ t.toList := hok.par_mem hx hp0
  obtain ⟨-, -, -, hgc, -⟩ := hok.ptrs_le hp_mem
  set g := (st.nodes pa).par with hg
  have hm_p0 : mem (nb + 8 * pa) = (st.nodes pa).left := (hnodes pa hpc).1
  have hm_p2 : mem (nb + 8 * pa + 2) = g := (hnodes pa hpc).2.2.1
  have hm_g0 : mem (nb + 8 * g) = (st.nodes g).left := (hnodes g hgc).1
  wram_step; try dsimp only
  wram_step; try dsimp only
  rw [hm_p2]
  wram_step
  · -- zig
    have hg0 : g = 0 := hcond
    obtain ⟨o₁, st₁, c₁, hrun₁, ⟨hn₁, hfr₁⟩, hc₁⟩ :=
      ordRotateBody_runs ω hnodes hok hx hw hwide (p := p) (pos := pos)
    refine spr_runs_seq_run_le
      (runs_call_iff.mpr ⟨[nb, x], ordRotateBody, o₁, st₁, c₁, by eval_expr, hrot, hrun₁,
        rfl, rfl, rfl⟩) ?_
    wram_step
    · refine ⟨?_, hfr₁⟩
      have heq : SplayState.splayStep ordPayload st x = SplayState.rotate ordPayload st x := by
        simp [SplayState.splayStep, hx0, ← hpa, hp0, ← hg, hg0]
      rw [heq]; exact hn₁
    · unfold ORD_SPLAY_STEP_COST; unfold ORD_ROTATE_COST at hc₁
      simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
        argsSize_cons, argsSize_nil] at *
      omega
  have hg0 : g ≠ 0 := hcond
  wram_step; try dsimp only
  rw [hm_p0]
  wram_step; try dsimp only
  rw [hm_g0]
  have hiff : ((if x = (st.nodes pa).left then 1 else 0) = (if pa = (st.nodes g).left then 1 else 0)) ↔
      ((x == (st.nodes pa).left) == (pa == (st.nodes g).left)) = true := by
    by_cases h1 : x = (st.nodes pa).left <;> by_cases h2 : pa = (st.nodes g).left <;> simp [h1, h2]
  refine runs_seq_cond_le (by eval_expr) (fun hc => ?_) (fun hc => ?_)
  · -- zig-zig
    have hc' : ((x == (st.nodes pa).left) == (pa == (st.nodes g).left)) = true := by
      rw [← hiff]; by_contra h; simp [h] at hc
    obtain ⟨o₁, st₁, c₁, hrun₁, ⟨hn₁, hfr₁⟩, hc₁⟩ :=
      ordRotateBody_runs ω hnodes hok hp_mem hw hwide (p := p) (pos := pos)
    have hok₁ : OrdTreeOk cap (SplayState.rotate ordPayload st pa) (t.rotateAt pa) := hok.rotate hp_mem
    have hx₁ : x ∈ (t.rotateAt pa).toList := (AuxTree.rotateAt_toList_perm pa t).mem_iff.mpr hx
    obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hn₂, hfr₂⟩, hc₂⟩ :=
      ordRotateBody_runs ω hn₁ hok₁ hx₁ hw hwide (p := p) (pos := st₁.pos)
    refine spr_runs_seq_run_le
      (runs_call_iff.mpr ⟨[nb, pa], ordRotateBody, o₁, st₁, c₁, by eval_expr, hrot, hrun₁,
        rfl, rfl, rfl⟩) ?_
    refine spr_runs_seq_run_le
      (runs_call_iff.mpr ⟨[nb, x], ordRotateBody, o₂, st₂, c₂, by eval_expr, hrot, hrun₂,
        rfl, rfl, rfl⟩) ?_
    wram_step
    · refine ⟨?_, fun a ha => (hfr₂ a ha).trans (hfr₁ a ha)⟩
      have heq : SplayState.splayStep ordPayload st x =
          SplayState.rotate ordPayload (SplayState.rotate ordPayload st pa) x := by
        simp only [SplayState.splayStep, hx0, ← hpa, hp0, ← hg, hg0, hc', ite_false, ite_true]
      rw [heq]; exact hn₂
    · unfold ORD_SPLAY_STEP_COST; unfold ORD_ROTATE_COST at hc₁ hc₂
      simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
        argsSize_cons, argsSize_nil] at *
      omega
  · -- zig-zag
    have hc' : ((x == (st.nodes pa).left) == (pa == (st.nodes g).left)) = false := by
      by_contra h; simp only [Bool.not_eq_false] at h; rw [← hiff] at h; simp [h] at hc
    obtain ⟨o₁, st₁, c₁, hrun₁, ⟨hn₁, hfr₁⟩, hc₁⟩ :=
      ordRotateBody_runs ω hnodes hok hx hw hwide (p := p) (pos := pos)
    have hok₁ : OrdTreeOk cap (SplayState.rotate ordPayload st x) (t.rotateAt x) := hok.rotate hx
    have hx₁ : x ∈ (t.rotateAt x).toList := (AuxTree.rotateAt_toList_perm x t).mem_iff.mpr hx
    obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hn₂, hfr₂⟩, hc₂⟩ :=
      ordRotateBody_runs ω hn₁ hok₁ hx₁ hw hwide (p := p) (pos := st₁.pos)
    refine spr_runs_seq_run_le
      (runs_call_iff.mpr ⟨[nb, x], ordRotateBody, o₁, st₁, c₁, by eval_expr, hrot, hrun₁,
        rfl, rfl, rfl⟩) ?_
    refine spr_runs_seq_run_le
      (runs_call_iff.mpr ⟨[nb, x], ordRotateBody, o₂, st₂, c₂, by eval_expr, hrot, hrun₂,
        rfl, rfl, rfl⟩) ?_
    wram_step
    · refine ⟨?_, fun a ha => (hfr₂ a ha).trans (hfr₁ a ha)⟩
      have heq : SplayState.splayStep ordPayload st x =
          SplayState.rotate ordPayload (SplayState.rotate ordPayload st x) x := by
        simp only [SplayState.splayStep, hx0, ← hpa, hp0, ← hg, hg0, hc', ite_false]; rfl
      rw [heq]; exact hn₂
    · unfold ORD_SPLAY_STEP_COST; unfold ORD_ROTATE_COST at hc₁ hc₂
      simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
        argsSize_cons, argsSize_nil] at *
      omega

/-! ### `ordSplayBody_runs` -/

theorem ordSplayBody_runs {w nb cap x pos rotProc stepProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc)) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {st : SplayState ℕ Unit Unit} {nf : ℕ → ℕ} {t : AuxTree}
    (hnodes : OrdNodesAt mem nb cap st nf) (hok : OrdTreeOk cap st t)
    (hx : x ∈ t.toList) (hw : nb + 8 * (cap + 1) < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordSplayBody stepProc) (startState [nb, x] mem pos) o st' c ∧
      (OrdNodesAt st'.mem nb cap (SplayState.splayLoop ordPayload st t.countNodes x) nf ∧
        ∀ a, ¬ InOrdNodes nb cap a → st'.mem a = mem a) ∧
      0 + c ≤ (t.depthOf x / 2 + 1) * ORD_SPLAY_RATE + 40 := by
  have hx0 : x ≠ 0 := SplayState.SubtreeInv_nonZero hok.inv.sub hx
  -- Loop induction on fuel k ≥ t.depthOf x / 2 + t.depthOf x % 2
  have hloop : ∀ (k : ℕ) (fuel : ℕ) (stM : State) (s : SplayState ℕ Unit Unit) (t' : AuxTree),
      OrdNodesAt stM.mem nb cap s nf → OrdTreeOk cap s t' → x ∈ t'.toList →
      t'.depthOf x / 2 + t'.depthOf x % 2 ≤ k →
      t'.depthOf x / 2 + t'.depthOf x % 2 ≤ fuel →
      stM.regs 0 = nb → stM.regs 1 = x →
      ∃ stE cE, Runs w p ω
          (.loop (.load (.bin .add (ordRec 1) (.const 2)))
            (.call 2 stepProc [.reg 0, .reg 1])) stM .normal stE cE ∧
        OrdNodesAt stE.mem nb cap (SplayState.splayLoop ordPayload s fuel x) nf ∧
        (∀ a, ¬ InOrdNodes nb cap a → stE.mem a = stM.mem a) ∧
        cE ≤ (t'.depthOf x / 2 + t'.depthOf x % 2) * (ORD_SPLAY_STEP_COST + 30) + 15 := by
    intro k
    induction k with
    | zero =>
      intro fuel stM s t' hn ho hx' hk hfuel r0 r1
      have hd0 : t'.depthOf x = 0 := by omega
      have hxr : x = t'.rootId := (AuxTree.depthOf_zero_iff_root hx').mp hd0
      have hp0 : (s.nodes x).par = 0 := by
        rw [SplayState.SubtreeInv_par_eq_parentIn ho.inv.nodup ho.inv.sub hx', hxr, spr_parentIn_rootId]
      have hxc := (ho.ptrs_le hx').1
      have hm_x2 : stM.mem (nb + 8 * x + 2) = 0 := by rw [← hp0]; exact (hn x hxc).2.2.1
      have hcond : (Expr.load (.bin .add (ordRec 1) (.const 2))).eval w stM = some 0 := by
        refine Expr.eval_load_of_eq ?_ hm_x2; eval_expr
      have hsl : SplayState.splayLoop ordPayload s fuel x = s := by
        cases fuel with
        | zero => rfl
        | succ f => simp [SplayState.splayLoop, hx0, hp0]
      refine ⟨stM, _, spr_runs_loop_false hcond, hsl.symm ▸ hn, fun _ _ => rfl, ?_⟩
      simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
    | succ k ih =>
      intro fuel stM s t' hn ho hx' hk hfuel r0 r1
      have hxc := (ho.ptrs_le hx').1
      by_cases hxr : x = t'.rootId
      · have hp0 : (s.nodes x).par = 0 := by
          rw [SplayState.SubtreeInv_par_eq_parentIn ho.inv.nodup ho.inv.sub hx', hxr, spr_parentIn_rootId]
        have hm_x2 : stM.mem (nb + 8 * x + 2) = 0 := by rw [← hp0]; exact (hn x hxc).2.2.1
        have hcond : (Expr.load (.bin .add (ordRec 1) (.const 2))).eval w stM = some 0 := by
          refine Expr.eval_load_of_eq ?_ hm_x2; eval_expr
        have hsl : SplayState.splayLoop ordPayload s fuel x = s := by
          cases fuel with
          | zero => rfl
          | succ f => simp [SplayState.splayLoop, hx0, hp0]
        refine ⟨stM, _, spr_runs_loop_false hcond, hsl.symm ▸ hn, fun _ _ => rfl, ?_⟩
        simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const]; omega
      · have hpar := SplayState.SubtreeInv_par_eq_parentIn ho.inv.nodup ho.inv.sub hx'
        have hpm := AuxTree.parentIn_mem_and_depth (p₀ := 0) ho.inv.nodup hx' hxr
        have hp0 : (s.nodes x).par ≠ 0 := hpar ▸ SplayState.SubtreeInv_nonZero ho.inv.sub hpm.1
        have hdep_pos : 0 < t'.depthOf x := by
          by_contra h0; exact hxr ((AuxTree.depthOf_zero_iff_root hx').mp (by omega))
        have hfuel_pos : 0 < fuel := by omega
        obtain ⟨fuel', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
        have hclean_path : ∀ u ∈ t'.pathTo x, (s.nodes u).rev = false ∧ (s.nodes u).tag = () :=
          fun u _ => ⟨ho.clean u, rfl⟩
        obtain ⟨t₁, ht₁, hperm₁, -, -, hout₁, -, -, hzig₁, hdbl₁⟩ :=
          SplayState.splayStep_preserves ordPayload_laws ho.inv hx' hxr hclean_path
        have h0_nmem : 0 ∉ t'.toList := fun h0 => SplayState.SubtreeInv_nonZero ho.inv.sub h0 rfl
        have ho₁ : OrdTreeOk cap (SplayState.splayStep ordPayload s x) t₁ :=
          { null_node := (hout₁ 0 h0_nmem).trans ho.null_node
            clean := splayStep_preserves_clean ho.clean x
            inv := ht₁
            mem_le := fun u hu => ho.mem_le u (hperm₁.mem_iff.mp hu)
            count_le := by
              rw [← AuxTree.length_toList, hperm₁.length_eq, AuxTree.length_toList]; exact ho.count_le }
        have hx₁ : x ∈ t₁.toList := hperm₁.mem_iff.mpr hx'
        have hdep_drop : t₁.depthOf x / 2 + t₁.depthOf x % 2 + 1 =
            t'.depthOf x / 2 + t'.depthOf x % 2 := by
          by_cases hd1 : t'.depthOf x = 1
          · have h1 := (hzig₁ hd1).2.1; rw [hd1, h1]
          · have h2 := (hdbl₁ (by omega)).1; rw [h2]; omega
        obtain ⟨o₁, st₁, c₁, hrun₁, ⟨hn₁, hfr₁⟩, hc₁⟩ :=
          ordSplayStepBody_runs hrot ω hn ho hx' hw hwide (pos := stM.pos)
        have hm_x2 : stM.mem (nb + 8 * x + 2) = (s.nodes x).par := (hn x hxc).2.2.1
        have hcond : (Expr.load (.bin .add (ordRec 1) (.const 2))).eval w stM =
            some (s.nodes x).par := by
          refine Expr.eval_load_of_eq ?_ hm_x2; eval_expr
        have hcall : Runs w p ω (.call 2 stepProc [.reg 0, .reg 1]) stM .normal
            { st₁ with regs := Function.update stM.regs 2 o₁.value }
            (argsSize [.reg 0, .reg 1] + c₁ + 1) :=
          runs_call_iff.mpr ⟨[nb, x], ordSplayStepBody rotProc, o₁, st₁, c₁, by eval_expr, hstep,
            hrun₁, rfl, rfl, rfl⟩
        obtain ⟨stE, cE, hrest, hnE, hfrE, hcE⟩ :=
          ih fuel' { st₁ with regs := Function.update stM.regs 2 o₁.value }
            (SplayState.splayStep ordPayload s x) t₁ hn₁ ho₁ hx₁ (by omega) (by omega)
            (by simp [r0]) (by simp [r1])
        have hsl : SplayState.splayLoop ordPayload s (fuel' + 1) x =
            SplayState.splayLoop ordPayload (SplayState.splayStep ordPayload s x) fuel' x := by
          simp [SplayState.splayLoop, hx0, hp0]
        refine ⟨stE, _, spr_runs_loop_true hcond hp0 hcall hrest, hsl ▸ hnE,
          fun a ha => (hfrE a ha).trans (hfr₁ a ha), ?_⟩
        rw [← hdep_drop]
        simp only [Expr.size_load, Expr.size_bin, Expr.size_reg, Expr.size_const,
          argsSize_cons, argsSize_nil] at *
        have hmul : (t₁.depthOf x / 2 + t₁.depthOf x % 2 + 1) * (ORD_SPLAY_STEP_COST + 30) =
            (t₁.depthOf x / 2 + t₁.depthOf x % 2) * (ORD_SPLAY_STEP_COST + 30) +
              (ORD_SPLAY_STEP_COST + 30) := by ring
        omega
  unfold ordSplayBody
  rw [startState]
  wram_step
  have hdep_lt : t.depthOf x < t.countNodes := depthOf_lt_countNodes hx
  obtain ⟨stE, cE, hrunL, hnE, hfrE, hcE⟩ :=
    hloop (t.depthOf x / 2 + t.depthOf x % 2) t.countNodes
      (startState [nb, x] mem pos) st t hnodes hok hx
      (le_refl _) (by omega) (by simp [startState]) (by simp [startState])
  refine spr_runs_seq_run_le hrunL ?_
  wram_step
  · exact ⟨hnE, hfrE⟩
  · have hbound : (t.depthOf x / 2 + t.depthOf x % 2) * (ORD_SPLAY_STEP_COST + 30) + 15 ≤
        (t.depthOf x / 2 + 1) * ORD_SPLAY_RATE := by
      unfold ORD_SPLAY_STEP_COST ORD_SPLAY_RATE
      have h1 : (t.depthOf x / 2 + t.depthOf x % 2) * (600 + 30) ≤ (t.depthOf x / 2 + 1) * 630 :=
        Nat.mul_le_mul_right 630 (by have := Nat.mod_lt (t.depthOf x) (by decide : 0 < 2); omega)
      have h2 : (t.depthOf x / 2 + 1) * 630 + 15 ≤ (t.depthOf x / 2 + 1) * 650 := by
        have h3 : (t.depthOf x / 2 + 1) * 630 + (t.depthOf x / 2 + 1) * 20 =
            (t.depthOf x / 2 + 1) * 650 := by ring
        have h4 : 15 ≤ (t.depthOf x / 2 + 1) * 20 :=
          Nat.le_trans (by decide) (Nat.mul_le_mul_right 20 (Nat.succ_pos _))
        have h5 := Nat.add_le_add_left h4 ((t.depthOf x / 2 + 1) * 630)
        rwa [h3] at h5
      exact Nat.le_trans (Nat.add_le_add_right h1 15) h2
    simp only [Expr.size_bin, Expr.size_reg, Expr.size_const] at *
    omega

/-! ### `ordSplayRootBody_runs` -/

theorem ordSplayRootBody_runs {w b x pos rotProc stepProc splayProc : ℕ} {p : Program}
    (hrot : p.procs[rotProc]? = some ordRotateBody)
    (hstep : p.procs[stepProc]? = some (ordSplayStepBody rotProc))
    (hsplay : p.procs[splayProc]? = some (ordSplayBody stepProc)) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {ord : ℕ → List End} {S : OrdStoreState} {v heap : ℕ}
    (hinv : OrdInv ord S) (harena : OrdArenaAt b S mem) (hv : v < S.vCap)
    (hx : x ∈ (S.trees v).toList) (hfoot : b + ordArenaSize S.vCap S.eCap ≤ heap)
    (hz : ZeroFrom mem heap) (hw : heap < 2 ^ w) (hwide : 16 ≤ 2 ^ w) :
    ∃ o st' c, Runs w p ω (ordSplayRootBody splayProc) (startState [b, x] mem pos) o st' c ∧
      (∃ S' : OrdStoreState,
        o.value = v + 1 ∧
        OrdInv ord S' ∧ OrdArenaAt b S' st'.mem ∧
        OrdFrame b S.vCap S.eCap heap mem st'.mem ∧
        S'.vCap = S.vCap ∧ S'.eCap = S.eCap ∧
        (S'.trees v).rootId = x ∧ (S'.trees v).toList = (S.trees v).toList ∧
        (∀ u, (S'.trees u).toList = (S.trees u).toList) ∧
        sumCountNodes S' = sumCountNodes S ∧
        sumTreePhi S' + (S.trees v).depthOf x / 2 ≤ sumTreePhi S + 3 * ordStoreLog S.eCap) ∧
      0 + c ≤ ((S.trees v).depthOf x / 2 + 1) * ORD_SPLAY_RATE + 100 := by
  set nb := ordNodesBase b S.vCap S.eCap with hnb
  have hfoot' : b + (16 + S.vCap + 18 * S.eCap) ≤ heap := hfoot
  have hnb_end : nb + 8 * (S.nextNode + 1) ≤ b + ordArenaSize S.vCap S.eCap := by
    have h1 := ordNodesBase_end b S.vCap S.eCap
    have h2 := hinv.next_le
    rw [hnb]; omega
  have hnb_w : nb + 8 * (S.nextNode + 1) < 2 ^ w := by omega
  have hxc : x ≤ S.nextNode := (hinv.live_le_nextNode hv hx).2
  obtain ⟨t', hinv', ht'_ne, ht'_root, ht'_list, -, hcnt', hphi'⟩ := ordInv_splay hinv hv hx
  set sp' := SplayState.splayLoop ordPayload S.splay (S.trees v).countNodes x
  set S' : OrdStoreState :=
    { S with splay := sp', vRoot := Function.update S.vRoot v x, trees := Function.update S.trees v t' }
  have hok := hinv.ordTreeOk hv
  obtain ⟨o₁, st₁, c₁, hrun₁, ⟨hn₁, hfr₁⟩, hc₁⟩ :=
    ordSplayBody_runs hrot hstep ω harena.nodes_at hok hx hnb_w hwide (pos := pos)
  have hfr₁_arena : ∀ a, ¬ ordFoot b S.vCap S.eCap a → st₁.mem a = mem a := fun a ha =>
    hfr₁ a fun hin => ha ⟨by unfold InOrdNodes ordNodesBase at hin; omega, by unfold InOrdNodes at hin; omega⟩
  have hpp' : (sp'.nodes x).ppar = v + 1 := by
    have := hinv'.root_ppar v hv (by simp [S', ht'_ne])
    simpa [S', ht'_root] using this
  have hm1_pp : st₁.mem (nb + 8 * x + 3) = v + 1 := by
    rw [← hpp']; exact (hn₁ x hxc).2.2.2.1
  have hm1_vr : st₁.mem (b + 2) = ordVRootBase b := by
    rw [hfr₁ (b + 2) (fun hin => by unfold InOrdNodes ordNodesBase at hin; omega)]
    exact harena.hdr_vRoot
  have hv_w : ordVRootBase b + v < 2 ^ w := by
    have := ordFoot_vRoot (b := b) (eCap := S.eCap) hv
    unfold ordFoot at this; omega
  have hmem_b4 : mem (b + 4) = nb := harena.hdr_nodes
  unfold ordSplayRootBody
  refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := b) (by simp [startState]))
    (Expr.eval_const (by omega)) (by omega)) hmem_b4) ?_
  refine spr_runs_seq_run_le
    (runs_call_iff.mpr ⟨[nb, x], ordSplayBody stepProc, o₁, st₁, c₁, by eval_expr, hsplay, hrun₁,
      rfl, rfl, rfl⟩) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add
    (Expr.eval_reg_of_eq (v := nb) (by simp))
    (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (v := x) (by simp [startState])) (by omega))
    (by omega)) (Expr.eval_const (by omega)) (by omega)) hm1_pp) ?_
  refine runs_seq_cond_le (Expr.eval_reg_of_eq (v := v + 1) (by simp)) (fun _ => ?_) (fun h => absurd h (Nat.succ_ne_zero v))
  refine runs_seq_assoc_le ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := b) (by simp [startState]))
    (Expr.eval_const (by omega)) (by omega)) hm1_vr) ?_
  refine runs_seq_store_le
    (Expr.eval_add (Expr.eval_reg_of_eq (v := ordVRootBase b) (by simp))
      (Expr.eval_sub (Expr.eval_reg_of_eq (v := v + 1) (by simp)) (Expr.eval_const (by omega)) (by omega))
      (by simp only [Nat.add_sub_cancel]; omega))
    (Expr.eval_reg_of_eq (v := x) (by simp [startState])) ?_
  wram_step
  · refine ⟨S', by simp [Outcome.value], hinv', ?_, ?_, rfl, rfl,
      by simp [S', ht'_root], by simp [S', ht'_list],
      fun u => by by_cases h : u = v <;> simp [S', h, ht'_list],
      hcnt', hphi'⟩
    · have hmid : OrdArenaAt b { S with splay := sp', trees := Function.update S.trees v t' } st₁.mem :=
        { hdr_vCap := (hfr₁ (b + 0) (fun hin => by unfold InOrdNodes ordNodesBase at hin; omega)).trans harena.hdr_vCap
          hdr_eCap := (hfr₁ (b + 1) (fun hin => by unfold InOrdNodes ordNodesBase at hin; omega)).trans harena.hdr_eCap
          hdr_vRoot := hm1_vr
          hdr_eNode := (hfr₁ (b + 3) (fun hin => by unfold InOrdNodes ordNodesBase at hin; omega)).trans harena.hdr_eNode
          hdr_nodes := (hfr₁ (b + 4) (fun hin => by unfold InOrdNodes ordNodesBase at hin; omega)).trans harena.hdr_nodes
          hdr_next := (hfr₁ (b + 5) (fun hin => by unfold InOrdNodes ordNodesBase at hin; omega)).trans harena.hdr_next
          hdr_free := (hfr₁ (b + 6) (fun hin => by unfold InOrdNodes ordNodesBase at hin; omega)).trans harena.hdr_free
          vRoot_at := fun u hu =>
            (hfr₁ (ordVRootBase b + u) (fun hin => by
              dsimp only at hu; unfold InOrdNodes ordVRootBase ordNodesBase at hin; omega)).trans
              (harena.vRoot_at u hu)
          eNode_at := fun k hk =>
            (hfr₁ (ordENodeBase b S.vCap + k) (fun hin => by
              dsimp only at hk; unfold InOrdNodes ordENodeBase ordNodesBase at hin; omega)).trans
              (harena.eNode_at k hk)
          nodes_at := hn₁ }
      have hupd := hmid.setVRoot (v := v) (r := x) hv
      simpa only [Nat.add_sub_cancel] using hupd
    · -- OrdFrame
      have hfr1_f : OrdFrame b S.vCap S.eCap heap mem st₁.mem :=
        ⟨fun a ha => (hfr₁_arena a (fun hf => by unfold ordFoot at hf; omega)).trans (hz a ha),
         fun a _ hnf => hfr₁_arena a hnf⟩
      have hfr2_f : OrdFrame b S.vCap S.eCap heap st₁.mem
          (Function.update st₁.mem (ordVRootBase b + (v + 1 - 1)) x) :=
        OrdFrame.of_store_in_foot hfr1_f.1 (by simpa [Nat.add_sub_cancel] using ordFoot_vRoot hv) hfoot
      exact hfr1_f.trans hfr2_f
  · simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
      argsSize_cons, argsSize_nil] at *
    omega

end MinCostFlow.SparseCore.Program
