module

public import MinCostFlow.LinkCut.Gen.PushDownRev
public import WordRAM.CopyWords

/-!
# `pushDownTag` as a program

`pushDownTagBody` is the machine version of `SplayState.pushDownTag`. For node `x ≠ 0` whose tag
is not the identity (payload step `isId`), it copies the tag of `x` to the heap pointer, writes
the identity tag into `x` (`setId`), applies the copy to the left and then to the right child
(`applyTagNode`, procedure `atProc`), and clears the copy again. Copying first makes the program
follow the model even when a child is `x` itself. The arguments are `[nb, x, heap]`. Procedure
`copyProc` is `copyWords`; the copy is cleared by copying the zero block just above it.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

/-- `pushDownTag` on `[nb, x, heap]`. -/
def pushDownTagBody (isIdProc setIdProc copyProc atProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 3 (recAddr 1) ;;
     .call 4 isIdProc [.reg 3, .reg 2] ;;
     .cond (.reg 4) (.ret (.const 0))
       (.assign 5 (.load (.reg 3)) ;;
        .assign 6 (.load (.bin .add (.reg 3) (.const 1))) ;;
        .assign 21 (.load (.bin .add (.reg 0) (.const 8))) ;;
        .call 7 copyProc [.bin .add (.reg 3) (.bin .sub (.reg 20) (.reg 21)), .reg 2, .reg 21] ;;
        .call 7 setIdProc [.reg 3, .bin .add (.reg 2) (.reg 21)] ;;
        .call 7 atProc [.reg 0, .reg 5, .reg 2, .bin .add (.reg 2) (.reg 21)] ;;
        .call 7 atProc [.reg 0, .reg 6, .reg 2, .bin .add (.reg 2) (.reg 21)] ;;
        .call 7 copyProc [.bin .add (.reg 2) (.reg 21), .reg 2, .reg 21] ;;
        .ret (.const 0)))

theorem pushDownTagBody_noRand (isIdProc setIdProc copyProc atProc : ℕ) :
    (pushDownTagBody isIdProc setIdProc copyProc atProc).NoRand := by
  simp [pushDownTagBody, recAddr, Stmt.NoRand]

/-- The payload values that `pushDownTag P st x` computes are representable. -/
def PushDownTagOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : SplayState α σ τ)
    (x : ℕ) : Prop :=
  x ≠ 0 → P.isIdTag (st.nodes x).tag = false →
    let st₀ := st.updateNode x fun cur => { cur with tag := P.idTag }
    ((st.nodes x).left ≠ 0 → ActOk ok P (st.nodes x).tag (st₀.nodes (st.nodes x).left)) ∧
    ((st.nodes x).right ≠ 0 → ActOk ok P (st.nodes x).tag
      ((SplayState.applyTagNode P st₀ (st.nodes x).left (st.nodes x).tag).nodes
        (st.nodes x).right))

/-- The run of `pushDownTagBody`. -/
theorem pushDownTagBody_runs {w nb cap x heap pos copyProc atProc : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    (S : PayloadSteps w p P Lay ok) (hcopy : MeetsContract w p copyProc (copyWordsContract w))
    (hat : p.procs[atProc]? = some (applyTagBody S.act))
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem)
    (hok : PushDownTagOk ok P st x) :
    ∃ o st' c, Runs w p ω (pushDownTagBody S.isId S.setId copyProc atProc)
        (startState [nb, x, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.pushDownTag P st x) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧ 0 + c ≤ 5 * S.cost + 40 * Lay.tagW + 300 := by
  have hroom := hheap.room
  have hwide := hheap.wide
  have hS := hheap.stride_lt
  have hS6 := Lay.stride_pos
  have hA := hheap.addr_lt hx
  have hrec := hheap.rec_le
  have hxS : x ≤ Lay.nodeStride * x := Nat.le_mul_of_pos_left x (by omega)
  have hoff : Lay.offTag + Lay.tagW = Lay.nodeStride := by unfold offTag nodeStride; omega
  have hoff' : Lay.nodeStride - Lay.tagW = Lay.offTag := by omega
  have htw := hnodes.tagW
  have hnb9 := hheap.nb9
  obtain ⟨hpl, hpr, -, -⟩ := hptr x hx
  obtain ⟨h0, h1, -, -, -, -, hv, hs, htg⟩ := hnodes x hx
  have hm0 : mem (nb + Lay.nodeStride * x) = (st.nodes x).left := h0
  have hm1 : mem (nb + Lay.nodeStride * x + 1) = (st.nodes x).right := h1
  have hAx := hA
  unfold nodeAddr at hA
  unfold pushDownTagBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simpa [SplayState.pushDownTag] using hnodes, TreeFrame.refl hheap.zero⟩
    · wram_cost
  · wram_step; try dsimp only
    have hisid := S.isId_ok
    wram_step
    · exact ⟨⟨_, heap, rfl, hA, ⟨_, hv⟩, _, htg⟩, hheap.zero, by simpa [heapArg] using (by omega :
        heap + S.space < 2 ^ w)⟩
    rintro v mem' pos' ⟨hz', hfr, hres⟩
    have hmem' : mem = mem' := by
      funext a
      by_cases ha : a < heap
      · exact (hfr a ha (by simp)).symm
      · simp only [heapArg] at hz'
        rw [hz' a (by simpa using ha), hheap.zero a (by omega)]
    subst hmem'
    have hv' : v = if P.isIdTag (st.nodes x).tag then 1 else 0 := hres _ htg
    subst hv'
    refine runs_cond_le (Expr.eval_reg_of_eq (by simp; rfl)) ?_ ?_
    · intro hid
      have hid' : P.isIdTag (st.nodes x).tag = true := by by_contra h; simp [h] at hid
      wram_step
      · exact ⟨by simpa [SplayState.pushDownTag, hcond, hid'] using hnodes,
          TreeFrame.refl hheap.zero⟩
      · simp only [isIdContract, payloadContract]; wram_cost
    · intro hid
      have hid' : P.isIdTag (st.nodes x).tag = false := by by_contra h; simp_all
      obtain ⟨okl, okr⟩ := hok hcond hid'
      set t := (st.nodes x).tag with ht_def
      set l := (st.nodes x).left with hl_def
      set r := (st.nodes x).right with hr_def
      set st₀ := st.updateNode x fun cur => { cur with tag := P.idTag } with hst₀
      have hbase : ∀ i < Lay.tagW, ¬ Lay.InRecords nb cap (heap + i) := fun i _ hi => by
        have := hi.2; omega
      wram_step; try dsimp only; rw [hm0]
      wram_step; try dsimp only; rw [hm1]
      refine runs_seq_load0_le (by simp) htw (by omega) ?_
      -- copy the tag of `x` to `heap`
      wram_step
      · exact ⟨_, _, _, rfl, by omega, by omega, by omega, Or.inr (by omega)⟩
      rintro - m₁ - ⟨src, dst, len, heq, -, hcp, hout⟩
      simp only [List.cons.injEq, and_true] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      rw [hoff'] at hcp
      have hlow₁ : ∀ a < heap, m₁ a = mem a := fun a ha => hout a (Or.inl ha)
      have hn₁ : Lay.NodesAt m₁ nb cap st :=
        hnodes.congr Lay fun a ha => hlow₁ a (lt_of_lt_of_le ha.2 hrec)
      have ht₁ : Lay.TagAt m₁ heap t := Lay.tag_move _ _ _ _ _ htg fun i hi => hcp i hi
      have hz₁ : ZeroFrom m₁ (heap + Lay.tagW) := fun a ha => by
        rw [hout a (Or.inr ha)]; exact hheap.zero a (by omega)
      -- write the identity tag into `x`
      have hsetid := S.setId_ok
      wram_step
      · exact ⟨⟨_, _, rfl, by omega, _, (hn₁ x hx).2.2.2.2.2.2.1⟩, by simpa [heapArg] using hz₁,
          by simp [heapArg]; omega⟩
      rintro - m₂ - ⟨hz₂, hfr₂, hval₂, hsum₂, htag₂⟩
      simp only [heapArg, List.getD_cons_zero] at hz₂ hfr₂ hval₂ hsum₂ htag₂
      obtain ⟨-, -, -, -, -, -, hv₁, hs₁, -⟩ := hn₁ x hx
      have hn₂' := NodesAt.payload hn₁ hx hz₁ hz₂ hfr₂ (hval₂ _ hv₁) (hsum₂ _ hs₁) htag₂
      have hst₀' : st₀ = st.updateNode x fun nd =>
          { nd with val := (st.nodes x).val, sum := (st.nodes x).sum, tag := P.idTag } := by
        refine splayState_ext fun y => ?_
        by_cases hy : y = x
        · subst hy; simp [st₀]
        · simp [st₀, hy]
      have hn₂ : Lay.NodesAt m₂ nb cap st₀ := by rw [hst₀']; exact hn₂'
      have hxrec : nb + Lay.nodeStride * x + Lay.nodeStride ≤ nb + Lay.nodeStride * (cap + 1) := by
        have : Lay.nodeStride * x + Lay.nodeStride ≤ Lay.nodeStride * (cap + 1) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
        omega
      have hlow₂ : ∀ a < heap + Lay.tagW, ¬ Lay.InRecords nb cap a → m₂ a = m₁ a := fun a ha hr =>
        hfr₂ a ha fun hc => hr (by
          unfold PayCell at hc
          refine ⟨by omega, ?_⟩
          unfold nodeAddr; omega)
      have ht₂ : Lay.TagAt m₂ heap t :=
        Lay.tag_congr _ _ _ _ ht₁ fun i hi => hlow₂ _ (by omega) (hbase i hi)
      have hh₂ : HeapOk Lay w nb cap (heap + Lay.tagW) S.space m₂ :=
        ⟨by omega, by omega, hz₂, hwide⟩
      -- apply the copy to the left child
      refine runs_seq_callBody_le hat (by eval_expr)
        (R := fun _ st₃ c₃ => Lay.NodesAt st₃.mem nb cap (SplayState.applyTagNode P st₀ l t) ∧
          TreeFrame Lay nb cap (heap + Lay.tagW) m₂ st₃.mem ∧ c₃ ≤ S.cost + 30) ?_ ?_
      · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := applyTagBody_runs S ω hn₂ hpl hh₂ hrec (by omega)
          ht₂ okl
        exact ⟨o, st', c, hr, hn, hf, by omega⟩
      rintro - st₃ c₃ ⟨hn₃, hf₃, hc₃⟩
      have ht₃ : Lay.TagAt st₃.mem heap t :=
        Lay.tag_congr _ _ _ _ ht₂ fun i hi => hf₃.2 _ (by omega) (hbase i hi)
      have hh₃ : HeapOk Lay w nb cap (heap + Lay.tagW) S.space st₃.mem :=
        ⟨by omega, by omega, hf₃.1, hwide⟩
      -- apply the copy to the right child
      refine runs_seq_callBody_le hat (by eval_expr)
        (R := fun _ st₄ c₄ => Lay.NodesAt st₄.mem nb cap (SplayState.applyTagNode P
          (SplayState.applyTagNode P st₀ l t) r t) ∧
          TreeFrame Lay nb cap (heap + Lay.tagW) st₃.mem st₄.mem ∧ c₄ ≤ S.cost + 30) ?_ ?_
      · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := applyTagBody_runs S ω hn₃ hpr hh₃ hrec (by omega)
          ht₃ okr
        exact ⟨o, st', c, hr, hn, hf, by omega⟩
      rintro - st₄ c₄ ⟨hn₄, hf₄, hc₄⟩
      -- clear the copy
      wram_step
      · exact ⟨_, _, _, rfl, by omega, by omega, by omega, Or.inl le_rfl⟩
      rintro - m₅ - ⟨src, dst, len, heq, -, hcp₅, hout₅⟩
      simp only [List.cons.injEq, and_true] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      wram_step
      · refine ⟨?_, ?_, ?_⟩
        · have hfin : SplayState.pushDownTag P st x =
              SplayState.applyTagNode P (SplayState.applyTagNode P st₀ l t) r t := by
            simp [SplayState.pushDownTag, hcond, hid', st₀, t, l, r]
          rw [hfin]
          exact hn₄.congr Lay fun a ha => hout₅ a (Or.inl (lt_of_lt_of_le ha.2 hrec))
        · intro a ha
          dsimp only
          by_cases ha' : a < heap + Lay.tagW
          · have := hcp₅ (a - heap) (by omega)
            rw [show heap + (a - heap) = a by omega] at this
            rw [this]; exact hf₄.1 _ (by omega)
          · rw [hout₅ a (Or.inr (by omega))]; exact hf₄.1 a (by omega)
        · intro a ha hr
          dsimp only
          rw [hout₅ a (Or.inl ha), hf₄.2 a (by omega) hr, hf₃.2 a (by omega) hr,
            hlow₂ a (by omega) hr, hlow₁ a ha]
      · simp only [copyWordsContract, isIdContract, setIdContract, payloadContract]; wram_cost

end MinCostFlow.LinkCut.Gen
