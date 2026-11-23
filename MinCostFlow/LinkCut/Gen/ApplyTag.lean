module

public import MinCostFlow.LinkCut.Gen.Pull

/-!
# `applyTagNode` as a program

`applyTagBody` is the machine version of `SplayState.applyTagNode`: for node `x ≠ 0` it calls
the payload's `act` step on the record of `x`, with a tag kept in a block at `b` outside all
records. The arguments are `[nb, x, b, heap]`.

`ActOk ok P t nd` says that applying the tag `t` to the node `nd` gives representable payload
values; it is the condition the `act` step needs.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

/-- `applyTagNode` on `[nb, x, b, heap]`. -/
def applyTagBody (actProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.call 4 actProc [.reg 2, recAddr 1, .reg 3] ;; .ret (.const 0))

theorem applyTagBody_noRand (actProc : ℕ) :
    (applyTagBody actProc).NoRand := by
  simp [applyTagBody, recAddr, Stmt.NoRand]

/-- Applying `t` to `nd` gives representable payload values. -/
def ActOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (t : τ) (nd : SplayNode α σ τ) : Prop :=
  ok.valOk (P.actVal t nd.val) ∧ ok.sumOk (P.actSum t nd.sum) ∧ ok.tagOk (P.compTag t nd.tag)

theorem applyTagNode_zero {P : LctPayload α σ τ} {st : SplayState α σ τ} {t : τ} :
    SplayState.applyTagNode P st 0 t = st := by
  simp [SplayState.applyTagNode]

/-- The run of `applyTagBody`. -/
theorem applyTagBody_runs {w nb cap x b heap pos : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    (S : PayloadSteps w p P Lay ok) (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ} {t : τ}
    (hnodes : Lay.NodesAt mem nb cap st) (hx : x ≤ cap)
    (hheap : HeapOk Lay w nb cap heap S.space mem)
    (hb : Lay.nodeAddr nb (cap + 1) ≤ b) (hbh : b + Lay.tagW ≤ heap) (ht : Lay.TagAt mem b t)
    (hok : x ≠ 0 → ActOk ok P t (st.nodes x)) :
    ∃ o st' c, Runs w p ω (applyTagBody S.act) (startState [nb, x, b, heap] mem pos) o st'
        c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.applyTagNode P st x t) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧ 0 + c ≤ S.cost + 30 := by
  have hroom := hheap.room
  have hwide := hheap.wide
  have hS := hheap.stride_lt
  have hS6 := Lay.stride_pos
  have hA := hheap.addr_lt hx
  have hrec := hheap.rec_le
  have hxS : x ≤ Lay.nodeStride * x := Nat.le_mul_of_pos_left x (by omega)
  have hxrec : Lay.nodeAddr nb x + Lay.nodeStride ≤ Lay.nodeAddr nb (cap + 1) :=
by
    unfold nodeAddr
    have : Lay.nodeStride * x + Lay.nodeStride ≤ Lay.nodeStride * (cap + 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨-, -, -, -, -, -, hv, hs, htg⟩ := hnodes x hx
  unfold nodeAddr at hA hxrec hb
  unfold applyTagBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  have hact := S.act_ok
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simpa [applyTagNode_zero] using hnodes, TreeFrame.refl hheap.zero⟩
    · wram_cost
  · wram_step
    · obtain ⟨ok1, ok2, ok3⟩ := hok hcond
      exact ⟨⟨b, nb + Lay.nodeStride * x, heap, rfl, hA, hbh, Or.inr (by omega), t, _, _, _, ht,
        hv, hs, htg, ok1, ok2, ok3⟩, hheap.zero, by simpa [heapArg] using hroom⟩
    · rintro v mem' pos' ⟨hz', hframe, hres⟩
      wram_step
      · obtain ⟨hv', hs', ht'⟩ := hres _ _ _ _ ht hv hs htg
        have hfin := NodesAt.payload hnodes hx hheap.zero hz' hframe hv' hs' ht'
        refine ⟨?_, TreeFrame.of_payload hx hz' hframe⟩
        convert hfin using 1
        refine splayState_ext fun y => ?_
        by_cases hy : y = x
        · subst hy; simp [SplayState.applyTagNode, hcond]
        · simp [SplayState.applyTagNode, hcond, hy]
      · simp only [actContract, payloadContract]; wram_cost

end MinCostFlow.LinkCut.Gen
