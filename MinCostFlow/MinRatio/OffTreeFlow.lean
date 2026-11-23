module

public import MinCostFlow.MinRatio.PathPayloadLayout
public import MinCostFlow.Num.Add
public import WordRAM.CopyWords
import MinCostFlow.MinRatio.PathIntAdd
import WordRAM.Tactic

/-!
# Applying a normalized increment to an explicit edge

Theorem 5.1 (page 15) represents the direction by tree paths and
explicit off-tree edges. For an explicit edge, Algorithm 2 (page 29)
adds the signed flow and its detector increment directly to the two
blocks of its record. This procedure updates those blocks while
preserving the direction, gradient, and length.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- Arguments are the edge record, tag, limb count, and heap. -/
def offTreeFlowBody (add copy : ℕ) : Stmt :=
  .assign 4 (.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 2))) ;;
  .call 5 add [.reg 4, .reg 1, .reg 2, .reg 3] ;;
  .call 6 add [.bin .add (.reg 4) (.reg 2), .bin .add (.reg 1) (.reg 2), .reg 2, .reg 5] ;;
  .call 7 copy [.reg 3, .reg 4, .bin .mul (.const 2) (.reg 2)] ;;
  .ret (.reg 6)

/-- Update the two account blocks of an explicit edge in place. The
written tag is already in the stored direction of the edge. -/
def offTreeFlowContract (w h : ℕ) (value : PathEdgeValue) (tag : PathTag) : Contract where
  pre args mem := ∃ edge change L heap, args = [edge, change, L, heap] ∧
    2 < 2 ^ w ∧ edge + 2 + 4 * L ≤ heap ∧ change + 2 * L ≤ heap ∧
    PathEdgeAt mem edge h L (some value) ∧ PathTagAt mem change h L tag ∧
    Num.Fits h L (value.flow + tag.flow) ∧ Num.Fits h L (value.detector + tag.detector) ∧
    ZeroFrom mem heap ∧ heap + 2 * L < 2 ^ w
  post args mem ret mem' := ∃ edge change L heap, args = [edge, change, L, heap] ∧
    ret = heap + 2 * L ∧ PathEdgeAt mem' edge h L (some (value.shift tag)) ∧
    (∀ x < heap, x < edge + 2 + 2 * L ∨ edge + 2 + 4 * L ≤ x → mem' x = mem x) ∧
    ZeroFrom mem' ret
  cost args _ := 110 * args.getD 2 0 + 96

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM

/-- The explicit edge update allocates two scratch blocks and uses
at most `110 * L + 96` steps. -/
theorem offTreeFlow_meetsContract {w h entry add copy : ℕ} {p : Program}
    (value : PathEdgeValue) (tag : PathTag) (hp : p.HasAt entry [offTreeFlowBody add copy])
    (ha : MeetsContract w p add (Num.addContract w h))
    (hc : MeetsContract w p copy (copyWordsContract w)) :
    MeetsContract w p entry (offTreeFlowContract w h value tag) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨edge, change, L, heap, rfl, hw, hrecord, htagEnd, hv, ht, hfitF, hfitD, hz, hroom⟩ := hpre
  obtain ⟨hkind, hdir, hg, hl, hf, hd⟩ := hv
  let flow := edge + 2 + 2 * L
  have hflow : flow = edge + 2 + 2 * L := rfl
  have hdet : flow + L = edge + 2 + 3 * L := by omega
  have hfloww : flow < 2 ^ w := by omega
  have hdetw : flow + L < 2 ^ w := by omega
  have htagw : change + L < 2 ^ w := by omega
  have h2L : 2 * L < 2 ^ w := by omega
  have hew := hwords edge (by simp)
  have hcw := hwords change (by simp)
  have hLw := hwords L (by simp)
  have hhw := hwords heap (by simp)
  apply runs_start_le
  unfold offTreeFlowBody
  refine runs_seq_assign_le (v := flow) (by eval_expr) ?_
  refine runs_seq_call_le ha (vs := [flow, change, L, heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact addPathInt_pre hf ht.1 (by omega) (by omega) hz (by omega)
  · intro top mem₁ pos₁ hp₁
    obtain ⟨htop, hframe₁, hz₁, hf₁⟩ := addPathInt_post hf ht.1 hfitF hp₁
    have htopw : top < 2 ^ w := by omega
    have hd₁ := hd.congr (mem' := mem₁) (fun i hi => hframe₁ _ (by omega))
    have ht₁ := ht.2.congr (mem' := mem₁) (fun i hi => hframe₁ _ (by omega))
    have hd₁' : PathIntAt mem₁ (flow + L) h L value.detector := hdet.symm ▸ hd₁
    have ht₁' : PathIntAt mem₁ (change + L) h L tag.detector := ht₁
    refine runs_seq_call_le ha (vs := [flow + L, change + L, L, top]) (by eval_expr) (by wram_words) ?_ ?_
    · exact addPathInt_pre hd₁' ht₁' (by omega) (by omega) hz₁ (by omega)
    · intro ret mem₂ pos₂ hp₂
      obtain ⟨hret, hframe₂, hz₂, hd₂⟩ := addPathInt_post hd₁' ht₁' hfitD hp₂
      have hretw : ret < 2 ^ w := by omega
      have hf₂ := hf₁.congr (mem' := mem₂) (fun i hi => hframe₂ _ (by omega))
      refine runs_seq_call_le hc (vs := [heap, flow, 2 * L]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨heap, flow, 2 * L, rfl, by omega, by omega, by omega, Or.inl (by omega)⟩
      · intro ignored mem₃ pos₃ hp₃
        obtain ⟨src, dst, count, hargs, _, hcopy, hframe₃⟩ := hp₃
        simp only [List.cons.injEq, and_true] at hargs
        obtain ⟨rfl, rfl, rfl⟩ := hargs
        have hframe : ∀ x < heap, x < flow ∨ flow + 2 * L ≤ x → mem₃ x = mem x :=
          fun x hx hout => (hframe₃ x hout).trans ((hframe₂ x (by omega)).trans (hframe₁ x hx))
        have hnewFlow : PathIntAt mem₃ flow h L (value.flow + tag.flow) :=
          hf₂.congr fun i hi => hcopy i (by omega)
        have hnewDetector : PathIntAt mem₃ (flow + L) h L (value.detector + tag.detector) :=
          hd₂.congr fun i hi => by
            rw [htop]
            simpa only [Nat.add_assoc] using hcopy (L + i) (by omega)
        have hnew : PathEdgeAt mem₃ edge h L (some (value.shift tag)) := by
          refine ⟨(hframe _ (by omega) (Or.inl (by omega))).trans hkind,
            (hframe _ (by omega) (Or.inl (by omega))).trans hdir, ?_, ?_, hnewFlow, hdet ▸ hnewDetector⟩
          · exact hg.congr fun i hi => hframe _ (by omega) (Or.inl (by omega))
          · exact hl.congr fun i hi => hframe _ (by omega) (Or.inl (by omega))
        refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
        · refine ⟨edge, change, L, heap, rfl, by change ret = heap + 2 * L; omega,
            hnew, ?_, ?_⟩
          · intro x hx hout
            exact hframe x hx (by omega)
          · intro x hx
            change ret ≤ x at hx
            exact (hframe₃ x (Or.inr (by omega))).trans (hz₂ x hx)
        · simp only [offTreeFlowContract, Num.addContract, copyWordsContract,
            List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, Expr.size_bin, Expr.size_const,
            argsSize_cons, argsSize_nil]
          omega

end MinCostFlow.MinRatio
