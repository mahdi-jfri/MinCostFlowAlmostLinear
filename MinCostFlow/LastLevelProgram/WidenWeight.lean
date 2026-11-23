module

public import MinCostFlow.LastLevelProgram.WeightUpdateFit
public import MinCostFlow.Num.SignExtend
import WordRAM.Tactic

/-!
# Widening the inputs to the weight update

For Lemma 5.5 (page 18), the stored operands can be narrower than
the intermediate product. Sign-extend the three operands into fresh
working blocks before invoking the verified update.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- Extend the three source blocks to `2 * L + 1` limbs, then update.
Arguments are `[weight, stretch, scaled denominator, L, heap]`. -/
def widenWeightBody (extend update : ℕ) : Stmt :=
  .assign 5 (.bin .add (.bin .mul (.const 2) (.reg 3)) (.const 1)) ;;
  .call 6 extend [.reg 0, .reg 3, .reg 5, .reg 4] ;;
  .call 7 extend [.reg 1, .reg 3, .reg 5, .reg 6] ;;
  .call 8 extend [.reg 2, .reg 3, .reg 5, .reg 7] ;;
  .call 9 update [.reg 4, .reg 6, .reg 7, .reg 5, .reg 8] ;;
  .ret (.reg 9)

/-- Space for the widened operands and the update working allocation. -/
def widenWeightSpace (L : ℕ) : ℕ :=
  let W := 2 * L + 1
  3 * W + weightUpdateSpace W

/-- Cost of the full widened update, including the extension calls. -/
def widenWeightCost (L : ℕ) : ℕ :=
  let W := 2 * L + 1
  weightUpdateCost W + 90 * W + 200

private theorem preservedBlock {mem out : ℕ → ℕ} {a L h heap : ℕ}
    (ha : a + L ≤ heap) (hf : ∀ x < heap, out x = mem x) :
    (Valid mem a h L → Valid out a h L) ∧ intVal out a h L = intVal mem a h L := by
  have hc (i : ℕ) (hi : i < L) := hf (a + i) (by omega)
  exact ⟨fun hv i hi => (hc i hi).trans_lt (hv i hi), intVal_congr hc⟩

/-- The widened update needs valid source blocks and a positive
denominator. The fit of the intermediate arithmetic follows from
the working-width bound. -/
theorem widenWeight_runs {w h extend update : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w)
    (he : p.HasAt extend (signExtendModule extend h))
    (hu : MeetsContract w p update (weightUpdateContract w h))
    (a b d L heap pos : ℕ) (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (ha : a + L ≤ heap) (hb : b + L ≤ heap) (hd : d + L ≤ heap)
    (hva : Valid mem a h L) (hvb : Valid mem b h L) (hvd : Valid mem d h L)
    (hpos : 0 < intVal mem d h L) (hz : ZeroFrom mem heap)
    (hroom : heap + widenWeightSpace L < 2 ^ w) :
    let W := 2 * L + 1
    ∃ o st c, Runs w p ω (widenWeightBody extend update)
      (startState [a,b,d,L,heap] mem pos) o st c ∧
      (o.value = heap + widenWeightSpace L ∧
        Valid st.mem (o.value - W) h W ∧
        intVal st.mem (o.value - W) h W =
          intVal mem a h L + intVal mem a h L * intVal mem b h L / intVal mem d h L ∧
        (∀ x < heap, st.mem x = mem x) ∧ ZeroFrom st.mem o.value) ∧ c ≤ widenWeightCost L := by
  intro W
  have hW : W = 2 * L + 1 := rfl
  have hspace : heap + (3 * W + weightUpdateSpace W) < 2 ^ w := hroom
  have htwo : 2 < 2 ^ w := (by decide : 2 < 2 ^ 3) |>.trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hbase : base h < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  have hmc := signExtend_meetsContract hh (lt_trans (by decide : 1 < 2) htwo) hbase he
  have ⟨_, _, _, hprod, hquot, hsum⟩ := weightUpdate_workingFit hh
    (intVal_fits hva) (intVal_fits hvb) (intVal_fits hvd) hpos
  apply runs_start_le
  unfold widenWeightBody
  refine runs_seq_assign_le (v := W) (by eval_expr) ?_
  refine runs_seq_call_le hmc (vs := [a,L,W,heap]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨a,L,W,heap,rfl,by omega,ha,hva⟩,hz,by change heap + W < 2^w; omega⟩
  · intro r₁ m₁ pos₁ hpost
    obtain ⟨hr₁, _, _, hf₁, hz₁, hva₁, hval₁⟩ := hpost
    change r₁ = heap + W at hr₁
    change ZeroFrom m₁ r₁ at hz₁
    change ∀ x < heap, m₁ x = mem x at hf₁
    change Valid m₁ heap h W at hva₁
    change intVal m₁ heap h W = intVal mem a h L at hval₁
    have hb₁ := preservedBlock (h := h) hb hf₁
    have hd₁ := preservedBlock (h := h) hd hf₁
    refine runs_seq_call_le hmc (vs := [b,L,W,r₁]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨⟨b,L,W,r₁,rfl,by omega,by omega,hb₁.1 hvb⟩,hz₁,by
        change r₁ + W < 2^w; omega⟩
    · intro r₂ m₂ pos₂ hpost
      obtain ⟨hr₂, _, _, hf₂, hz₂, hvb₂, hval₂⟩ := hpost
      change r₂ = r₁ + W at hr₂
      change ZeroFrom m₂ r₂ at hz₂
      change ∀ x < r₁, m₂ x = m₁ x at hf₂
      change Valid m₂ r₁ h W at hvb₂
      change intVal m₂ r₁ h W = intVal m₁ b h L at hval₂
      have ha₂ := preservedBlock (h := h) hr₁.ge hf₂
      have hd₂ := preservedBlock (h := h) (show d + L ≤ r₁ by omega) hf₂
      refine runs_seq_call_le hmc (vs := [d,L,W,r₂]) (by eval_expr) ?_ ?_ ?_
      · wram_words
      · exact ⟨⟨d,L,W,r₂,rfl,by omega,by omega,hd₂.1 (hd₁.1 hvd)⟩,hz₂,by
          change r₂ + W < 2^w; omega⟩
      · intro r₃ m₃ pos₃ hpost
        obtain ⟨hr₃, _, _, hf₃, hz₃, hvd₃, hval₃⟩ := hpost
        change r₃ = r₂ + W at hr₃
        change ZeroFrom m₃ r₃ at hz₃
        change ∀ x < r₂, m₃ x = m₂ x at hf₃
        change Valid m₃ r₂ h W at hvd₃
        change intVal m₃ r₂ h W = intVal m₂ d h L at hval₃
        have ha₃ := preservedBlock (h := h) (show heap + W ≤ r₂ by omega) hf₃
        have hb₃ := preservedBlock (h := h) hr₂.ge hf₃
        have hA := ha₃.2.trans (ha₂.2.trans hval₁)
        have hB := hb₃.2.trans (hval₂.trans hb₁.2)
        have hD := hval₃.trans (hd₂.2.trans hd₁.2)
        refine runs_seq_call_le hu (vs := [heap,r₁,r₂,W,r₃]) (by eval_expr) ?_ ?_ ?_
        · wram_words
        · refine ⟨⟨heap,r₁,r₂,W,r₃,rfl,by omega,by omega,by omega,
            ha₃.1 (ha₂.1 hva₁),hb₃.1 hvb₂,hvd₃,?_,?_,?_,?_⟩,hz₃,?_⟩
          · rwa [hD]
          · rwa [hA, hB]
          · rwa [hA, hB, hD]
          · rwa [hA, hB, hD]
          · change r₃ + weightUpdateSpace W < 2^w
            omega
        · intro r₄ m₄ pos₄ hpost
          obtain ⟨hr₄, _, _, hf₄, hz₄, hv, hval⟩ := hpost
          change r₄ = r₃ + weightUpdateSpace W at hr₄
          change ZeroFrom m₄ r₄ at hz₄
          change ∀ x < r₃, m₄ x = m₃ x at hf₄
          change Valid m₄ (r₃ + (11 * W + 1) + integerDivideSpace W) h W at hv
          change intVal m₄ (r₃ + (11 * W + 1) + integerDivideSpace W) h W =
            intVal m₃ heap h W + intVal m₃ heap h W * intVal m₃ r₁ h W / intVal m₃ r₂ h W at hval
          rw [hA,hB,hD] at hval
          have hresult : r₄ - W = r₃ + (11 * W + 1) + integerDivideSpace W := by
            unfold weightUpdateSpace at hr₄
            omega
          have hrw : r₄ < 2^w := by omega
          refine runs_ret_le (v := r₄) (by eval_expr) ?_ ?_
          · refine ⟨by change r₄ = heap + (3 * W + weightUpdateSpace W); omega,
              by simpa only [Outcome.value,hresult] using hv,
              by simpa only [Outcome.value,hresult] using hval, ?_, hz₄⟩
            intro x hx
            exact (hf₄ x (by omega)).trans ((hf₃ x (by omega)).trans
              ((hf₂ x (by omega)).trans (hf₁ x hx)))
          · simp [widenWeightCost, signExtendContract, weightUpdateContract, heapContract,
              argsSize, Expr.size]
            rw [hW]
            omega

/-- Heap interface for the widened update. Its output starts one working
block before the returned heap pointer. -/
def widenWeightContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a b d L heap, args = [a,b,d,L,heap] ∧
      a + L ≤ heap ∧ b + L ≤ heap ∧ d + L ≤ heap ∧
      Valid mem a h L ∧ Valid mem b h L ∧ Valid mem d h L ∧ 0 < intVal mem d h L)
    (fun _ _ _ => True)
    (fun args _ => widenWeightCost (args.getD 3 0))
    (fun args _ => widenWeightSpace (args.getD 3 0))
  { C with post := fun args mem ret out =>
      let L := args.getD 3 0
      let W := 2 * L + 1
      let a := intVal mem (args.getD 0 0) h L
      let b := intVal mem (args.getD 1 0) h L
      let d := intVal mem (args.getD 2 0) h L
      ret = heapArg args + widenWeightSpace L ∧ C.post args mem ret out ∧
        Valid out (ret - W) h W ∧ intVal out (ret - W) h W = a + a * b / d }

/-- Install the widened update as a call from the edge-wise iteration. -/
theorem widenWeight_meetsContract {w h entry extend update : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w)
    (hb : p.procs[entry]? = some (widenWeightBody extend update))
    (he : p.HasAt extend (signExtendModule extend h))
    (hu : MeetsContract w p update (weightUpdateContract w h)) :
    MeetsContract w p entry (widenWeightContract w h) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω _ hpre
  obtain ⟨⟨a,b,d,L,heap,rfl,ha,hb',hd,hva,hvb,hvd,hpos⟩,hz,hroom⟩ := hpre
  obtain ⟨o, st, cost, hrun, ⟨hret, hv, hval, hframe, hzero⟩, hcost⟩ :=
    widenWeight_runs hh hw he hu a b d L heap pos mem ω ha hb' hd hva hvb hvd hpos hz hroom
  have hle : heap ≤ o.value := hret ▸ Nat.le_add_right _ _
  exact ⟨o, st, cost, hrun, ⟨hret, ⟨hle, hret.le, hframe, hzero, trivial⟩, hv, hval⟩, hcost⟩

end MinCostFlow.LastLevelProgram
