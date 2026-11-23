module

public import MinCostFlow.LinkCut.Gen.RevNode
public import WordRAM.Tactic

/-!
# `pull` as a program

`pullBody` is the machine version of `SplayState.pull`: for node `x ≠ 0` it writes the size
`1 + szL + szR` (capped at `4`, see `NodeLayout.NodeAt`) and calls the payload's `pull` step,
which writes the summary. The arguments are `[nb, x, heap]`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

/-- Register `rd` := the record address of the node in register `rs`, and register `rz` := its
capped size, or `0` and `0` if that node is `0`. -/
def childInfo (rs rd rz : ℕ) : Stmt :=
  .assign rd (.const 0) ;; .assign rz (.const 0) ;;
  .cond (.reg rs) (.assign rd (recAddr rs) ;;
    .assign rz (.load (.bin .add (.reg rd) (.const 4)))) .nop

/-- `pull` on `[nb, x, heap]`. -/
def pullBody (pullProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 3 (recAddr 1) ;;
     .assign 4 (.load (.reg 3)) ;;
     .assign 5 (.load (.bin .add (.reg 3) (.const 1))) ;;
     childInfo 4 6 7 ;;
     childInfo 5 8 9 ;;
     .assign 7 (.bin .add (.bin .add (.const 1) (.reg 7)) (.reg 9)) ;;
     .cond (.bin .lt (.const 4) (.reg 7)) (.assign 7 (.const 4)) .nop ;;
     .store (.bin .add (.reg 3) (.const 4)) (.reg 7) ;;
     .call 10 pullProc [.reg 1, .reg 3, .reg 6, .reg 8, .reg 2] ;;
     .ret (.const 0))

theorem pullBody_noRand (pullProc : ℕ) :
    (pullBody pullProc).NoRand := by
  simp [pullBody, childInfo, recAddr, Stmt.NoRand]

/-- The summary that `SplayState.pull` writes into node `x`. -/
def pullSum (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) : σ :=
  P.combine (if (st.nodes x).left = 0 then P.empty else (st.nodes (st.nodes x).left).sum)
    (P.combine (P.single x (st.nodes x).val)
      (if (st.nodes x).right = 0 then P.empty else (st.nodes (st.nodes x).right).sum))

/-- The size that `SplayState.pull` writes into node `x`. -/
def pullSz (st : SplayState α σ τ) (x : ℕ) : ℕ :=
  1 + (if (st.nodes x).left = 0 then 0 else (st.nodes (st.nodes x).left).sz) +
    (if (st.nodes x).right = 0 then 0 else (st.nodes (st.nodes x).right).sz)

theorem pull_nodes_self {P : LctPayload α σ τ} {st : SplayState α σ τ} {x : ℕ} (hx : x ≠ 0) :
    (SplayState.pull P st x).nodes x =
      { st.nodes x with sz := pullSz st x, sum := pullSum P st x } := by
  simp [SplayState.pull, hx, pullSz, pullSum]

theorem pull_nodes_ne {P : LctPayload α σ τ} {st : SplayState α σ τ} {x y : ℕ} (hy : y ≠ x) :
    (SplayState.pull P st x).nodes y = st.nodes y := by
  unfold SplayState.pull
  split_ifs <;> simp [hy]

theorem pull_zero {P : LctPayload α σ τ} {st : SplayState α σ τ} :
    SplayState.pull P st 0 = st := by
  simp [SplayState.pull]

/-- The run of `childInfo`. -/
theorem childInfo_runs {w nb c z rs rd rz : ℕ} {Lay : NodeLayout α σ τ} {p : Program}
    {ω : ℕ → Bool} {st : State} (h0 : st.regs 0 = nb) (hc : st.regs rs = c)
    (hrd : rd ≠ rs) (hrz : rz ≠ rs) (hrdz : rd ≠ rz) (hrd0 : rd ≠ 0) (hrz0 : rz ≠ 0)
    (hrd20 : rd ≠ 20) (hrz20 : rz ≠ 20) (hS : st.regs 20 = Lay.nodeStride)
    (hA : c ≠ 0 → nb + Lay.nodeStride * c + 4 < 2 ^ w)
    (hz : c ≠ 0 → st.mem (nb + Lay.nodeStride * c + 4) = z) :
    ∃ cc ≤ 20, Runs w p ω (childInfo rs rd rz) st .normal
      { st with regs := Function.update (Function.update st.regs rd
        (if c = 0 then 0 else nb + Lay.nodeStride * c)) rz (if c = 0 then 0 else z) } cc := by
  have hw : 0 < 2 ^ w := Nat.two_pow_pos w
  unfold childInfo
  set st₁ : State := { st with regs := Function.update st.regs rd 0 }
  set st₂ : State := { st₁ with regs := Function.update st₁.regs rz 0 }
  have r₁ : Runs w p ω (.assign rd (.const 0)) st .normal st₁ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const hw, rfl, rfl, rfl⟩
  have r₂ : Runs w p ω (.assign rz (.const 0)) st₁ .normal st₂ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const hw, rfl, rfl, rfl⟩
  have hc2 : st₂.regs rs = c := by
    simp [st₂, st₁, Function.update_of_ne (Ne.symm hrz), Function.update_of_ne (Ne.symm hrd), hc]
  have h02 : st₂.regs 0 = nb := by
    simp [st₂, st₁, Function.update_of_ne (Ne.symm hrz0), Function.update_of_ne (Ne.symm hrd0), h0]
  have hS2 : st₂.regs 20 = Lay.nodeStride := by
    simp [st₂, st₁, Function.update_of_ne (Ne.symm hrz20), Function.update_of_ne (Ne.symm hrd20),
      hS]
  by_cases hc0 : c = 0
  · subst hc0
    have rn : Runs w p ω .nop st₂ .normal st₂ 1 := runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
    have r₃ : Runs w p ω (.cond (.reg rs) (.assign rd (recAddr rs) ;;
        .assign rz (.load (.bin .add (.reg rd) (.const 4)))) .nop) st₂ .normal st₂ 3 :=
      runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq hc2, by simpa using rn, rfl⟩
    refine ⟨2 + (2 + 3 + 1) + 1, by omega, ?_⟩
    simpa [st₂, st₁] using runs_seq_normal r₁ (runs_seq_normal r₂ r₃)
  · have hA' := hA hc0
    set A := nb + Lay.nodeStride * c
    set st₃ : State := { st₂ with regs := Function.update st₂.regs rd A }
    set st₄ : State := { st₃ with regs := Function.update st₃.regs rz z }
    have hAw : Lay.nodeAddr nb c < 2 ^ w := by unfold nodeAddr; omega
    have r₄ : Runs w p ω (.assign rd (recAddr rs)) st₂ .normal st₃ 6 :=
      runs_assign_iff.mpr ⟨A, eval_recAddr h02 hc2 hS2 hAw, rfl, rfl, rfl⟩
    have hrd3 : st₃.regs rd = A := by simp [st₃]
    have r₅ : Runs w p ω (.assign rz (.load (.bin .add (.reg rd) (.const 4)))) st₃ .normal st₄ 5 :=
      runs_assign_iff.mpr ⟨z, Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hrd3)
        (Expr.eval_const (by omega)) (by omega)) (hz hc0), rfl, rfl, rfl⟩
    have r₄₅ := runs_seq_normal r₄ r₅
    have r₃ : Runs w p ω (.cond (.reg rs) (.assign rd (recAddr rs) ;;
        .assign rz (.load (.bin .add (.reg rd) (.const 4)))) .nop) st₂ .normal st₄ 14 :=
      runs_cond_iff.mpr ⟨c, 12, Expr.eval_reg_of_eq hc2, by simpa [hc0] using r₄₅, rfl⟩
    refine ⟨2 + (2 + 14 + 1) + 1, by omega, ?_⟩
    have hfin : st₄ = { st with regs := Function.update (Function.update st.regs rd A) rz z } := by
      simp only [st₄, st₃, st₂, st₁, State.mk.injEq, true_and, and_true]
      funext i
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    simpa [hc0, hfin] using runs_seq_normal r₁ (runs_seq_normal r₂ r₃)

/-- `childInfo` followed by `t`. -/
theorem runs_seq_childInfo_le {w nb c z rs rd rz k T : ℕ} {Lay : NodeLayout α σ τ} {p : Program}
    {ω : ℕ → Bool} {st : State} {t : Stmt} {Q : Outcome → State → Prop}
    (h0 : st.regs 0 = nb) (hc : st.regs rs = c)
    (hrd : rd ≠ rs) (hrz : rz ≠ rs) (hrdz : rd ≠ rz) (hrd0 : rd ≠ 0) (hrz0 : rz ≠ 0)
    (hrd20 : rd ≠ 20) (hrz20 : rz ≠ 20) (hS : st.regs 20 = Lay.nodeStride)
    (hA : c ≠ 0 → nb + Lay.nodeStride * c + 4 < 2 ^ w)
    (hz : c ≠ 0 → st.mem (nb + Lay.nodeStride * c + 4) = z)
    (hrest : ∃ o st' cc, Runs w p ω t { st with regs := Function.update (Function.update st.regs rd
        (if c = 0 then 0 else nb + Lay.nodeStride * c)) rz (if c = 0 then 0 else z) } o st' cc ∧
      Q o st' ∧ (k + 21) + cc ≤ T) :
    ∃ o st' cc, Runs w p ω (.seq (childInfo rs rd rz) t) st o st' cc ∧ Q o st' ∧ k + cc ≤ T := by
  obtain ⟨c₁, hc₁, hr⟩ := childInfo_runs (p := p) (ω := ω) h0 hc hrd hrz hrdz hrd0 hrz0 hrd20
    hrz20 hS hA hz
  obtain ⟨o, st', cc, hr', hq, hcc⟩ := hrest
  exact runs_seq_run_le hr ⟨o, st', cc, hr', hq, by omega⟩

/-- Capping register `7` at `4`, followed by `t`. -/
theorem runs_seq_cap_le {w v k T : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} {t : Stmt}
    {Q : Outcome → State → Prop} (h7 : st.regs 7 = v) (hw : 4 < 2 ^ w)
    (hrest : ∃ o st' cc, Runs w p ω t { st with regs := Function.update st.regs 7 (min v 4) } o st'
      cc ∧ Q o st' ∧ (k + 7) + cc ≤ T) :
    ∃ o st' cc, Runs w p ω (.seq (.cond (.bin .lt (.const 4) (.reg 7)) (.assign 7 (.const 4)) .nop)
      t) st o st' cc ∧ Q o st' ∧ k + cc ≤ T := by
  obtain ⟨o, st', cc, hr', hq, hcc⟩ := hrest
  have he : (Expr.bin .lt (.const 4) (.reg 7)).eval w st = some (if 4 < v then 1 else 0) :=
    Expr.eval_bin (Expr.eval_const hw) (Expr.eval_reg_of_eq h7) (by simp; split_ifs <;> omega)
  by_cases hv : 4 < v
  · have r₁ : Runs w p ω (.assign 7 (.const 4)) st .normal
        { st with regs := Function.update st.regs 7 4 } 2 :=
      runs_assign_iff.mpr ⟨4, Expr.eval_const hw, rfl, rfl, rfl⟩
    have r₂ : Runs w p ω (.cond (.bin .lt (.const 4) (.reg 7)) (.assign 7 (.const 4)) .nop) st
        .normal { st with regs := Function.update st.regs 7 4 } 6 :=
      runs_cond_iff.mpr ⟨1, 2, by simpa [hv] using he, by simpa using r₁, rfl⟩
    have hmin : min v 4 = 4 := by omega
    rw [hmin] at hr'
    exact runs_seq_run_le r₂ ⟨o, st', cc, hr', hq, by omega⟩
  · have rn : Runs w p ω .nop st .normal st 1 := runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
    have r₂ : Runs w p ω (.cond (.bin .lt (.const 4) (.reg 7)) (.assign 7 (.const 4)) .nop) st
        .normal st 5 :=
      runs_cond_iff.mpr ⟨0, 1, by simpa [hv] using he, by simpa using rn, rfl⟩
    have hmin : min v 4 = v := by omega
    have hst : { st with regs := Function.update st.regs 7 (min v 4) } = st := by
      rw [hmin, ← h7]; simp
    rw [hst] at hr'
    exact runs_seq_run_le r₂ ⟨o, st', cc, hr', hq, by omega⟩

/-- The run of `pullBody`. -/
theorem pullBody_runs {w nb cap x heap pos : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    (S : PayloadSteps w p P Lay ok) (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk Lay w nb cap heap S.space mem)
    (hok : x ≠ 0 → ok.sumOk (pullSum P st x)) :
    ∃ o st' c, Runs w p ω (pullBody S.pull) (startState [nb, x, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.pull P st x) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧ 0 + c ≤ S.cost + 150 := by
  have hroom := hheap.room
  have hwide := hheap.wide
  have hS6 := Lay.stride_pos
  have hstr := hnodes.stride
  have hnb6 := hheap.nb6
  have hA := hheap.addr_lt hx
  obtain ⟨hpl, hpr, -, -⟩ := hptr x hx
  set l := (st.nodes x).left with hl_def
  set r := (st.nodes x).right with hr_def
  have hAl := hheap.addr_lt hpl
  have hAr := hheap.addr_lt hpr
  obtain ⟨h0, h1, -, -, -, -, hv, -, -⟩ := hnodes x hx
  have hm0 : mem (nb + Lay.nodeStride * x) = l := h0
  have hm1 : mem (nb + Lay.nodeStride * x + 1) = r := h1
  have hszl : mem (nb + Lay.nodeStride * l + 4) = min (st.nodes l).sz 4 := (hnodes l hpl).2.2.2.2.1
  have hszr : mem (nb + Lay.nodeStride * r + 4) = min (st.nodes r).sz 4 := (hnodes r hpr).2.2.2.2.1
  unfold NodeLayout.nodeAddr at hA hAl hAr
  unfold pullBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hstr hnb6 ?_
  wram_step
  · -- `x = 0`
    subst hcond
    wram_step
    · exact ⟨by simpa [pull_zero] using hnodes, TreeFrame.refl hheap.zero⟩
    · wram_cost
  · wram_step; try dsimp only
    wram_step; try dsimp only; rw [hm0]
    wram_step; try dsimp only; rw [hm1]
    have hzl : (if l = 0 then 0 else min (st.nodes l).sz 4) ≤ 4 := by split_ifs <;> omega
    have hzr : (if r = 0 then 0 else min (st.nodes r).sz 4) ≤ 4 := by split_ifs <;> omega
    refine runs_seq_childInfo_le (by simp) (by simp) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by simp) (fun _ => by omega) (fun _ => hszl) ?_
    refine runs_seq_childInfo_le (by simp) (by simp) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by simp) (fun _ => by omega) (fun _ => hszr) ?_
    wram_step; try dsimp only
    refine runs_seq_cap_le (by simp; rfl) (by omega) ?_
    have hm : min ((1 + if l = 0 then 0 else min (st.nodes l).sz 4) +
        (if r = 0 then 0 else min (st.nodes r).sz 4)) 4 = min (pullSz st x) 4 := by
      simp only [pullSz, ← hl_def, ← hr_def]; split_ifs <;> simp only [min_def] <;> split_ifs <;> omega
    simp only [hm]
    wram_step; try dsimp only
    have hpull := S.pull_ok
    -- the records after the size write
    set st₁ := st.updateNode x fun nd => { nd with sz := pullSz st x } with hst₁
    have hn₁ : Lay.NodesAt (Function.update mem (nb + Lay.nodeStride * x + 4) (min (pullSz st x) 4))
        nb cap st₁ := hnodes.setSz Lay hx
    have hsum₁ : ∀ y, (st₁.nodes y).sum = (st.nodes y).sum := fun y => by
      by_cases hy : y = x
      · subst hy; simp [st₁]
      · simp [st₁, hy]
    have hval₁ : (st₁.nodes x).val = (st.nodes x).val := by simp [st₁]
    have hchild : ∀ c ≤ cap, ChildSumAt P Lay
        (Function.update mem (nb + Lay.nodeStride * x + 4) (min (pullSz st x) 4))
        (if c = 0 then 0 else nb + Lay.nodeStride * c)
        (if c = 0 then P.empty else (st.nodes c).sum) := fun c hc => by
      by_cases hc0 : c = 0
      · left; simp [hc0]
      · right
        simp only [hc0, if_false]
        refine ⟨by have := Lay.stride_pos; positivity, ?_⟩
        have := (hn₁ c hc).2.2.2.2.2.2.2.1
        rwa [hsum₁] at this
    have hzero₁ : ZeroFrom (Function.update mem (nb + Lay.nodeStride * x + 4)
        (min (pullSz st x) 4)) heap := fun a ha => by
      rw [Function.update_of_ne (by omega)]; exact hheap.zero a ha
    wram_step
    · have hxS : x ≤ Lay.nodeStride * x := Nat.le_mul_of_pos_left x (by omega)
      intro v hv; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with h | h | h | h | h <;> rw [h] <;> (try split_ifs) <;> omega
    · refine ⟨⟨x, nb + Lay.nodeStride * x, _, _, heap, rfl, hA, ?_, ?_, (st.nodes x).val, _, _,
        ?_, hchild l hpl, hchild r hpr, ?_⟩, hzero₁, by simpa [heapArg] using hroom⟩
      · split_ifs <;> omega
      · split_ifs <;> omega
      · have := (hn₁ x hx).2.2.2.2.2.2.1
        rwa [hval₁] at this
      · simpa [pullSum, ← hl_def, ← hr_def] using hok hcond
    · rintro v mem' pos' ⟨hz', hframe, hres⟩
      wram_step
      · obtain ⟨hv', hs', ht'⟩ := hres _ _ _ ((hn₁ x hx).2.2.2.2.2.2.1) (hchild l hpl)
          (hchild r hpr)
        have hfin := NodesAt.payload hn₁ hx hzero₁ hz' hframe hv' hs'
          (ht' _ (hn₁ x hx).2.2.2.2.2.2.2.2)
        refine ⟨?_, ?_⟩
        · convert hfin using 1
          refine splayState_ext fun y => ?_
          by_cases hy : y = x
          · subst hy
            rw [pull_nodes_self hcond]
            simp [st₁, pullSum, ← hl_def, ← hr_def]
          · rw [pull_nodes_ne hy]
            simp [st₁, hy]
        · exact (TreeFrame.of_ctrl (Lay := Lay) (off := OFF_SZ) hx (by decide) hA
            hheap.zero).trans (TreeFrame.of_payload hx hz' hframe)
      · simp only [pullContract, payloadContract]; wram_cost

end MinCostFlow.LinkCut.Gen
