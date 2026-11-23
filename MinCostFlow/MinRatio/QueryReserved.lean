module

public import MinCostFlow.MinRatio.QueryResolved
public import WordRAM.CopyWords
import WordRAM.Tactic

/-!
# Returning a Query result below tree workspace

Definition 4.5 (page 14) queries one flow coordinate. The IPM expects
that scalar at the heap address supplied when Query starts. A tree
point read can allocate above that address. The final writer computes
the signed value at the current heap and copies it to the reserved
answer block.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Arguments are the resolved value, limb count, answer address, and heap. -/
def queryReservedBody (write copy : ℕ) : Stmt :=
  .call 4 write [.reg 0, .reg 1, .reg 3] ;;
  .call 5 copy [.reg 3, .reg 2, .reg 1] ;;
  .ret (.reg 4)

/-- Write the resolved coordinate into the answer block reserved below the heap. -/
noncomputable def queryReservedContract (w h P : ℕ) (v : PathEdgeValue) : Contract where
  pre args mem := ∃ a L answer heap, args = [a, L, answer, heap] ∧
    2 < 2 ^ w ∧ a + 2 + 4 * L ≤ heap ∧ answer + L ≤ heap ∧
    PathEdgeAt mem a h L (some v) ∧ Num.Fits h L v.originalFlow ∧
    ZeroFrom mem heap ∧ heap + L < 2 ^ w
  post args mem ret mem' := ∃ a L answer heap, args = [a, L, answer, heap] ∧
    ret = heap + L ∧ ScalarAt mem' answer h L P ((v.originalFlow : ℝ) / (2 : ℝ) ^ P) ∧
    (∀ x < heap, x < answer ∨ answer + L ≤ x → mem' x = mem x) ∧ ZeroFrom mem' ret
  cost args _ := 53 * args.getD 1 0 + 71

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain IPM.Machine

/-- The writer preserves all earlier cells outside the answer block.
It costs at most `53 * L + 71` steps. -/
theorem queryReserved_meetsContract {w h P entry write copy : ℕ} {p : Program}
    (v : PathEdgeValue) (hp : p.HasAt entry [queryReservedBody write copy])
    (hw : MeetsContract w p write (queryResolvedContract w h P v))
    (hc : MeetsContract w p copy (copyWordsContract w)) :
    MeetsContract w p entry (queryReservedContract w h P v) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨a, L, answer, heap, rfl, hword, hrecord, hanswer, hedge, hfit, hz, hroom⟩ := hpre
  have haw := hwords a (by simp)
  have hLw := hwords L (by simp)
  have hansw := hwords answer (by simp)
  have hheapw := hwords heap (by simp)
  apply runs_start_le
  unfold queryReservedBody
  refine runs_seq_call_le hw (vs := [a, L, heap]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨a, L, heap, rfl, hword, hrecord, hedge, hfit, hz, hroom⟩
  · intro ret mem₁ pos₁ hpost
    obtain ⟨hret, hscalar, hf, hz₁⟩ := hpost
    change ret = heap + L at hret
    change (∀ x < heap, mem₁ x = mem x) at hf
    have hretw : ret < 2 ^ w := by omega
    refine runs_seq_call_le hc (vs := [heap, answer, L]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨heap, answer, L, rfl, by omega, by omega, by omega, Or.inl hanswer⟩
    · intro ignored mem₂ pos₂ hpost₂
      obtain ⟨src, dst, count, hargs, _, hcopy, hframe⟩ := hpost₂
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl, rfl⟩ := hargs
      have hscalar₂ : ScalarAt mem₂ answer h L P ((v.originalFlow : ℝ) / (2 : ℝ) ^ P) := by
        change ScalarAt mem₁ heap h L P ((v.originalFlow : ℝ) / (2 : ℝ) ^ P) at hscalar
        obtain ⟨hvalid, hvalue⟩ := hscalar
        refine ⟨fun i hi => (hcopy i hi).symm ▸ hvalid i hi, ?_⟩
        unfold Num.fixVal at hvalue ⊢
        rw [Num.intVal_congr hcopy, hvalue]
      refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
      · exact ⟨a, L, answer, heap, rfl, hret, hscalar₂,
          fun x hx hout => (hframe x hout).trans (hf x hx),
          fun x hx => (hframe x (Or.inr (by change ret ≤ x at hx; omega))).trans (hz₁ x hx)⟩
      · simp only [queryReservedContract, queryResolvedContract, copyWordsContract,
          List.getD_cons_zero, List.getD_cons_succ, Expr.size_reg, argsSize_cons, argsSize_nil]
        omega

/-- The Query precondition supplies the signed output range, even when
the tree orientation is opposite to the original edge direction. -/
theorem queryReserved_pre_of_stateFits {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    {G : MGraph} {edge address answer heap : ℕ} {s : (algorithm2_dsWithFailure cfg).State}
    {mem : ℕ → ℕ} {v : PathEdgeValue}
    (hstate : MinRatioStateFits (algorithm2_dsWithFailure cfg) G F.fmt.limbBits F.limbs
      F.fmt.precision s)
    (he : edge ∈ G.E)
    (hflow : (v.originalFlow : ℝ) / (2 : ℝ) ^ F.fmt.precision = algorithm2_query cfg s edge)
    (hrecord : PathEdgeAt mem address F.fmt.limbBits F.limbs (some v))
    (hword : 2 < 2 ^ w) (hs : address + 2 + 4 * F.limbs ≤ heap)
    (hanswer : answer + F.limbs ≤ heap) (hz : ZeroFrom mem heap)
    (hroom : heap + F.limbs < 2 ^ w) :
    (queryReservedContract w F.fmt.limbBits F.fmt.precision v).pre
      [address, F.limbs, answer, heap] mem := by
  obtain ⟨z, hfit, hzval⟩ := hstate edge he
  change algorithm2_query cfg s edge = _ at hzval
  have hscale : (2 : ℝ) ^ F.fmt.precision ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have heq : (v.originalFlow : ℝ) = (z : ℝ) :=
    (div_left_inj' hscale).mp (hflow.trans hzval)
  have hzint : v.originalFlow = z := Int.cast_inj.mp heq
  exact ⟨address, F.limbs, answer, heap, rfl, hword, hs, hanswer, hrecord, hzint ▸ hfit, hz, hroom⟩

/-- For a resolved value matching the model, the reserved answer is
the IPM Query output at the original heap. -/
theorem queryReserved_minRatio_post {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    {G : MGraph} {m handle heap answer edge address ret : ℕ} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ}
    {s : (algorithm2_dsWithFailure cfg).State} {mem mem' : ℕ → ℕ} {v : PathEdgeValue}
    (hflow : (v.originalFlow : ℝ) / (2 : ℝ) ^ F.fmt.precision = algorithm2_query cfg s edge)
    (hout : (queryReservedContract w F.fmt.limbBits F.fmt.precision v).post
      [address, F.limbs, answer, heap] mem ret mem') :
    (minRatioMachineContract F (algorithm2_dsWithFailure cfg) G m κ α rate allocation).post
      1 s [handle, edge, answer] mem s mem' := by
  obtain ⟨a, L, dst, top, hargs, _, hvalue, _, _⟩ := hout
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hargs
  rw [hflow] at hvalue
  exact ⟨rfl, hvalue⟩

end MinCostFlow.MinRatio
