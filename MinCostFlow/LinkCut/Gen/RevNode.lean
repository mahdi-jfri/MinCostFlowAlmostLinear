module

public import MinCostFlow.LinkCut.Gen.Call

/-!
# `revNode` as a program

`revNodeBody` is the machine version of `SplayState.revNode`: for node `x ≠ 0` it swaps the two
child pointers of `x`, flips its reversal bit, and calls the payload's `rev` step on the record of
`x`. The run theorem `revNodeBody_runs` says that the records then hold `revNode P st x`, and that
the call keeps the tree frame (`TreeFrame`).

The arguments are `[nb, x, heap]`, where `nb` is the address of the record of node `0`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

/-- `revNode` on `[nb, x, heap]`. -/
def revNodeBody (revProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.reg 2))
    (.assign 3 (recAddr 1) ;;
     .assign 4 (.load (.reg 3)) ;;
     .assign 5 (.load (.bin .add (.reg 3) (.const 1))) ;;
     .store (.reg 3) (.reg 5) ;;
     .store (.bin .add (.reg 3) (.const 1)) (.reg 4) ;;
     .store (.bin .add (.reg 3) (.const 5))
       (.bin .sub (.const 1) (.load (.bin .add (.reg 3) (.const 5)))) ;;
     .call 6 revProc [.reg 3, .reg 2] ;;
     .ret (.reg 6))

theorem revNodeBody_noRand (revProc : ℕ) :
    (revNodeBody revProc).NoRand := by
  simp [revNodeBody, recAddr, Stmt.NoRand]

/-- The run of `revNodeBody`. -/
theorem revNodeBody_runs {w nb cap x heap pos : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    (S : PayloadSteps w p P Lay ok) (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) (hheap : HeapOk Lay w nb cap heap S.space mem)
    (hok : x ≠ 0 → ok.valOk (P.revVal (st.nodes x).val) ∧ ok.sumOk (P.revSum (st.nodes x).sum) ∧
      ok.tagOk (P.revTag (st.nodes x).tag)) :
    ∃ v st' c, Runs w p ω (revNodeBody S.rev) (startState [nb, x, heap] mem pos)
        (.returned v) st' c ∧
      Lay.NodesAt st'.mem nb cap (SplayState.revNode P st x) ∧
      TreeFrame Lay nb cap heap mem st'.mem ∧ c ≤ S.cost + 70 := by
  have hroom := hheap.room
  have hA := hheap.addr_lt hx
  have hS6 := Lay.stride_pos
  set A := Lay.nodeAddr nb x with hA_def
  have hstr := hnodes.stride
  set st00 := startState [nb, x, heap] mem pos with hst00
  set st0 : State := { st00 with regs := Function.update st00.regs 20 Lay.nodeStride } with hst0
  have hload : Runs w p ω strideLoad st00 .normal st0 5 := by
    refine runs_assign_iff.mpr ⟨Lay.nodeStride, ?_, rfl, rfl, rfl⟩
    have hnb : nb + 6 < 2 ^ w := by
      have := hheap.addr_lt (Nat.zero_le cap); unfold nodeAddr at this; omega
    have h6 : 6 < 2 ^ w := by omega
    exact Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st00, startState]))
      (Expr.eval_const h6) hnb) hstr
  have hw1 : 1 < 2 ^ w := by
    have : 6 ≤ heap := le_trans (by omega) hA
    have : 2 ≤ heap + S.space := by omega
    omega
  have hcond : Expr.eval w st0 (.bin .eq (.reg 1) (.const 0)) = some (if x = 0 then 1 else 0) := by
    have h0w : 0 < 2 ^ w := by omega
    have hx' : (if x = 0 then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    simp [Expr.eval, BinOp.eval, st0, st00, startState, h0w, hx']
  by_cases hx0 : x = 0
  · -- nothing to do
    subst hx0
    have hret : Runs w p ω (.ret (.reg 2)) st0 (.returned heap) st0 2 :=
      runs_ret_iff.mpr ⟨heap, Expr.eval_reg_of_eq rfl, rfl, rfl, rfl⟩
    refine ⟨heap, st0, 5 + (3 + 2 + 1) + 1, ?_, ?_, TreeFrame.refl hheap.zero, by omega⟩
    · rw [revNodeBody]
      refine runs_seq_normal hload (runs_cond_iff.mpr ?_)
      exact ⟨1, 2, by simpa using hcond, by simpa using hret, rfl⟩
    · simpa [SplayState.revNode, st0, st00, startState] using hnodes
  -- the record of `x` and the values read from it
  obtain ⟨h0, h1, h2, h3, h4, h5, hv, hs, ht⟩ := hnodes x hx
  set nd := st.nodes x with hnd
  have hA_w : A + Lay.nodeStride < 2 ^ w := by omega
  -- step 1: register 3 := A
  have hSw : Lay.nodeStride < 2 ^ w := by omega
  have hSx : Lay.nodeStride * x ≤ A := by rw [hA_def]; unfold nodeAddr; omega
  let regs1 := Function.update st0.regs 3 A
  have hs1 : Runs w p ω (.assign 3 (recAddr 1)) st0 .normal { st0 with regs := regs1 } 6 := by
    refine runs_assign_iff.mpr ⟨A, ?_, rfl, rfl, rfl⟩
    have hmul : Lay.nodeStride * x < 2 ^ w := by omega
    have hadd : nb + Lay.nodeStride * x < 2 ^ w := by rw [hA_def] at hA_w; unfold nodeAddr at hA_w; omega
    simp [recAddr, Expr.eval, BinOp.eval, st0, st00, startState, hSw, hmul, hadd, hA_def, nodeAddr]
  -- step 2: register 4 := left, register 5 := right
  let st1 : State := { st0 with regs := regs1 }
  have hr3 : st1.regs 3 = A := by simp [st1, regs1]
  have hm0 : st1.mem A = nd.left := h0
  have hm1 : st1.mem (A + 1) = nd.right := h1
  have hm5 : st1.mem (A + 5) = (if nd.rev then 1 else 0) := h5
  let st2 : State := { st1 with regs := Function.update st1.regs 4 nd.left }
  have hs2 : Runs w p ω (.assign 4 (.load (.reg 3))) st1 .normal st2 3 :=
    runs_assign_iff.mpr ⟨nd.left, Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr3) hm0, rfl, rfl, rfl⟩
  let st3 : State := { st2 with regs := Function.update st2.regs 5 nd.right }
  have hs3 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 3) (.const 1)))) st2 .normal st3 5 := by
    refine runs_assign_iff.mpr ⟨nd.right, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [st2, hr3])) (Expr.eval_const hw1) (by omega))
      hm1, rfl, rfl, rfl⟩
  have hr3' : st3.regs 3 = A := by simp [st3, st2, hr3]
  -- step 3: the three stores
  let m1 := Function.update st1.mem A nd.right
  let m2 := Function.update m1 (A + 1) nd.left
  let rb := if nd.rev then 1 else 0
  let m3 := Function.update m2 (A + 5) (1 - rb)
  have hs4 : Runs w p ω (.store (.reg 3) (.reg 5)) st3 .normal { st3 with mem := m1 } 3 :=
    runs_store_iff.mpr ⟨A, nd.right, Expr.eval_reg_of_eq hr3', Expr.eval_reg_of_eq (by simp [st3]),
      rfl, rfl, rfl⟩
  have hs5 : Runs w p ω (.store (.bin .add (.reg 3) (.const 1)) (.reg 4)) { st3 with mem := m1 }
      .normal { st3 with mem := m2 } 5 :=
    runs_store_iff.mpr ⟨A + 1, nd.left, Expr.eval_add (Expr.eval_reg_of_eq hr3')
      (Expr.eval_const hw1) (by omega), Expr.eval_reg_of_eq (by simp [st3, st2]), rfl, rfl, rfl⟩
  have hm2_5 : m2 (A + 5) = rb := by
    simp only [m2, m1, Function.update_apply]
    rw [if_neg (by omega), if_neg (by omega)]; exact hm5
  have hrb : rb ≤ 1 := by simp only [rb]; split_ifs <;> omega
  have hs6 : Runs w p ω (.store (.bin .add (.reg 3) (.const 5))
      (.bin .sub (.const 1) (.load (.bin .add (.reg 3) (.const 5))))) { st3 with mem := m2 }
      .normal { st3 with mem := m3 } 10 := by
    have h5w : 5 < 2 ^ w := by omega
    have hadd5 : Expr.eval w { st3 with mem := m2 } (.bin .add (.reg 3) (.const 5)) =
        some (A + 5) := Expr.eval_add (Expr.eval_reg_of_eq hr3') (Expr.eval_const h5w) (by omega)
    refine runs_store_iff.mpr ⟨A + 5, 1 - rb, hadd5, ?_, rfl, rfl, rfl⟩
    exact Expr.eval_sub (Expr.eval_const hw1) (Expr.eval_load_of_eq hadd5 hm2_5) hw1
  -- the memory after the stores
  have hm3 : ∀ k, m3 (A + k) =
      if k = 0 then nd.right else if k = 1 then nd.left else if k = 5 then 1 - rb
      else st1.mem (A + k) := by
    intro k
    simp only [m3, m2, m1, Function.update_apply]
    by_cases k0 : k = 0
    · subst k0; simp
    by_cases k1 : k = 1
    · subst k1; simp
    by_cases k5 : k = 5
    · subst k5; simp
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp [k0, k1, k5]
  have hm3_other : ∀ y, (∀ i < Lay.nodeStride, y ≠ A + i) → m3 y = mem y := by
    intro y hy
    simp only [m3, m2, m1, Function.update_apply]
    rw [if_neg (hy 5 (by omega)), if_neg (hy 1 (by omega)), if_neg (by simpa using hy 0 (by omega))]
    rfl
  have hm3_lo : ZeroFrom m3 heap := by
    intro z hz
    rw [hm3_other z fun i hi heq => by omega]
    exact hheap.zero z hz
  have hpay : ∀ k, 6 ≤ k → k < Lay.nodeStride → m3 (A + k) = mem (A + k) := fun k hk _ => by
    rw [hm3]; simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 5 by omega, st1, st0, st00,
      startState]
  obtain ⟨hv3, hs3', ht3⟩ := Lay.payload_keep (mem := mem) (mem' := m3) hpay hv hs ht
  -- step 4: the payload call
  obtain ⟨okv, oks, okt⟩ := hok hx0
  have hargs : ∀ a ∈ [A, heap], a < 2 ^ w := by
    intro a ha; simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  obtain ⟨body, hbody, o, stc, cc, hrunc, hpost, hcc⟩ :=
    S.rev_ok [A, heap] m3 pos ω hargs
      ⟨⟨A, heap, rfl, hA, nd.val, nd.sum, nd.tag, hv3, hs3', ht3, okv, oks, okt⟩,
        hm3_lo, hroom⟩
  obtain ⟨hz', hframe, hres⟩ := hpost
  obtain ⟨hv', hs', ht'⟩ := hres nd.val nd.sum nd.tag hv3 hs3' ht3
  let st4 : State := { stc with regs := Function.update st3.regs 6 o.value }
  have hs7 : Runs w p ω (.call 6 S.rev [.reg 3, .reg 2]) { st3 with mem := m3 } .normal st4
      (2 + cc + 1) := by
    refine runs_call_iff.mpr ⟨[A, heap], body, o, stc, cc, ?_, hbody, hrunc, rfl, rfl, rfl⟩
    have h2 : st3.regs 2 = heap := by simp [st3, st2, st1, regs1, st0, st00, startState]
    simp [evalArgs, Expr.eval, hr3', h2]
  have hs8 : Runs w p ω (.ret (.reg 6)) st4 (.returned o.value) st4 2 :=
    runs_ret_iff.mpr ⟨o.value, Expr.eval_reg_of_eq (by simp [st4]), rfl, rfl, rfl⟩
  have hrun := runs_seq_normal hs1 (runs_seq_normal hs2 (runs_seq_normal hs3
    (runs_seq_normal hs4 (runs_seq_normal hs5 (runs_seq_normal hs6 (runs_seq_normal hs7 hs8))))))
  -- the final memory
  have hfin_lo : ∀ y < heap, ¬ Lay.PayCell A y → stc.mem y = m3 y := hframe
  have hctrl : ∀ k < 6, stc.mem (A + k) = m3 (A + k) := fun k hk =>
    hfin_lo _ (by omega) fun hc => by unfold PayCell OFF_VAL at hc; omega
  refine ⟨o.value, st4, 5 + (
    3 + (6 + (3 + (5 + (3 + (5 + (10 + ((2 + cc + 1) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1, ?_, ?_, ⟨hz', fun y hy hnr => ?_⟩, ?_⟩
  · rw [revNodeBody]
    refine runs_seq_normal hload (runs_cond_iff.mpr ?_)
    exact ⟨0, _, by simpa [hx0] using hcond, by simpa [hx0] using hrun, rfl⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx
      have hnode : (SplayState.revNode P st y).nodes y =
          { nd with
            left := nd.right
            right := nd.left
            rev := !nd.rev
            val := P.revVal nd.val
            sum := P.revSum nd.sum
            tag := P.revTag nd.tag } := by
        simp [SplayState.revNode, hx0, nd]
      rw [hnode]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hv', hs', ht'⟩ <;>
        simp only [st4, NodeLayout.OFF_LEFT, NodeLayout.OFF_RIGHT, NodeLayout.OFF_PAR, NodeLayout.OFF_PPAR, NodeLayout.OFF_SZ, NodeLayout.OFF_REV] <;>
        rw [hctrl _ (by decide), hm3] <;> simp [st1, st0, st00, startState]
      · simpa [NodeLayout.OFF_PAR] using h2
      · simpa [NodeLayout.OFF_PPAR] using h3
      · simpa [NodeLayout.OFF_SZ] using h4
      · simp only [rb]; cases nd.rev <;> rfl
    · have hrec : (SplayState.revNode P st x).nodes y = st.nodes y := by
        simp [SplayState.revNode, hx0, hyx]
      rw [hrec]
      refine (hnodes y hy).congr Lay fun i hi => ?_
      have hy_lt := (hheap.addr_lt hy)
      have hnot : ∀ j < Lay.nodeStride, Lay.nodeAddr nb y + i ≠ A + j := fun j hj heq =>
        hyx (Lay.addr_disjoint hi hj heq).1
      show stc.mem _ = mem _
      have hlt : Lay.nodeAddr nb y + i < heap := by omega
      have hnp : ¬ Lay.PayCell A (Lay.nodeAddr nb y + i) := fun hc => by
        unfold PayCell at hc
        exact hnot (Lay.nodeAddr nb y + i - A) (by omega) (by omega)
      rw [hfin_lo _ hlt hnp, hm3_other _ hnot]
  · show stc.mem y = mem y
    have hnot : ∀ j < Lay.nodeStride, y ≠ A + j := fun j hj heq =>
      hnr (heq ▸ inRecords_of_rec hx hj)
    have hnp : ¬ Lay.PayCell A y := fun hc => by
      unfold PayCell at hc
      exact hnot (y - A) (by omega) (by omega)
    rw [hfin_lo y hy hnp, hm3_other y hnot]
  · have : cc ≤ S.cost := hcc
    omega

end MinCostFlow.LinkCut.Gen
