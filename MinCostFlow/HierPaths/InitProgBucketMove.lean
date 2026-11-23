module

public import MinCostFlow.HierPaths.InitProgBucket
public import MinCostFlow.HierPaths.InitProgFillWord
public import MinCostFlow.HierPaths.InitProgMove

/-!
# Finishing a bucketed section

The record producer puts keys and payloads in scratch. The bucket procedure
sorts them above that scratch, clears its counters and order array, then
moves the compressed result down and clears the record buffers.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments are the key and payload addresses, record count, key count,
temporary result address and final destination. -/
def initBucketMove (bucket clear move : ℕ) : Stmt :=
  .call 6 bucket [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
  .call 7 clear [.reg 6, .bin .add (.reg 3) (.reg 2), .const 0] ;;
  .call 8 move [.reg 5, .reg 4, .reg 6] ;;
  .ret (.reg 8)

theorem initBucketMove_noRand (bucket clear move : ℕ) :
    (initBucketMove bucket clear move).NoRand := by simp [initBucketMove, Stmt.NoRand]

/-- The interval above the section is returned to zero. The cost charges
every word in the scratch interval that is cleared. -/
def initBucketMoveContract (w k : ℕ) (rs : List (ℕ × ℕ)) : Contract where
  pre args mem := ∃ keys vals tmp dst, args = [keys, vals, rs.length, k, tmp, dst] ∧
    (initBucketContract w k rs).pre [keys, vals, rs.length, k, tmp] mem ∧
    dst ≤ tmp ∧ ZeroFrom mem (tmp + (k + 1) + rs.length + k + rs.length)
  post args mem r mem' := ∃ keys vals tmp dst, args = [keys, vals, rs.length, k, tmp, dst] ∧
    r = dst + (k + 1) + rs.length ∧ ListAt mem' dst (csrList k (buckets rs)) ∧
    ZeroFrom mem' r ∧ ∀ y < dst, mem' y = mem y
  cost args _ := 300 * (rs.length + k + 1) + 17 * (args.getD 4 0 - args.getD 5 0)

theorem initBucketMove_meetsContract {w f bucket clear move k : ℕ}
    {rs : List (ℕ × ℕ)} {p : Program}
    (hp : p.procs[f]? = some (initBucketMove bucket clear move))
    (hB : MeetsContract w p bucket (initBucketContract w k rs))
    (hC : MeetsContract w p clear (initFillWordContract w))
    (hM : MeetsContract w p move (moveDownContract w)) :
    MeetsContract w p f (initBucketMoveContract w k rs) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨keys, vals, tmp, dst, rfl, hpre, hsep, hzero⟩ := hpre
  have hpre' := hpre
  obtain ⟨_, _, tmp', hargs, _, _, _, _, hk, hroom⟩ := hpre'
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨_, _, _, _, ht⟩ := hargs
  subst tmp'
  let n := rs.length
  let r := tmp + (k + 1) + n
  let endScratch := r + k + n
  have hd : (csrList k (buckets rs)).length = (k + 1) + n := by
    rw [csrList, List.length_append, length_csrOffsets, initBucket_data_length rs k hk]
  have hR : r < 2 ^ w := by dsimp [r, n]; omega
  have hE : endScratch < 2 ^ w := by dsimp [endScratch, r, n]; omega
  have hkn : k + n < 2 ^ w := by dsimp [endScratch] at hE; omega
  have h1 : 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold initBucketMove
  refine runs_seq_call_le hB (vs := [keys, vals, n, k, tmp]) rfl ?_ hpre ?_
  · intro v hv
    exact hw v (by simp [n] at hv ⊢; tauto)
  intro q mem₁ pos₁ hp₁
  obtain ⟨_, _, tmp', ha, hq, hdata, hf₁⟩ := hp₁
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨_, _, _, _, ht⟩ := ha
  subst tmp' q
  change ∀ y, y < tmp ∨ endScratch ≤ y → mem₁ y = mem y at hf₁
  refine runs_seq_call_le hC (vs := [r, k + n, 0])
    (by simp [evalArgs, Expr.eval, startState, BinOp.eval, n, r, hkn]) ?_
    ⟨r, k + n, 0, rfl, by simpa [endScratch, Nat.add_assoc] using hE, h1⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hR
    · exact hkn
    · exact Nat.two_pow_pos _
  intro q mem₂ pos₂ hp₂
  obtain ⟨r', n', v', ha, _, hrep, hf₂⟩ := hp₂
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨hr', hn', hv'⟩ := ha
  subst r' n' v'
  have hData₂ : ListAt mem₂ tmp (csrList k (buckets rs)) :=
    listAt_congr (fun i hi => by
      rw [hd] at hi
      exact (hf₂ _ (.inl (by dsimp [r]; omega))).symm) hdata
  have hz₂ : ZeroFrom mem₂ r := by
    intro y hy
    by_cases h : y < endScratch
    · have hy' : y - r < k + n := by dsimp [endScratch] at h; omega
      have hrep' := hrep (y - r) (by simpa using hy')
      rw [show r + (y - r) = y by omega] at hrep'
      exact hrep'.trans (List.getElem_replicate _)
    · exact (hf₂ _ (.inr (by dsimp [endScratch] at h ⊢; omega))).trans
        ((hf₁ _ (.inr (by omega))).trans (hzero _ (by dsimp [endScratch, r, n] at h ⊢; omega)))
  refine runs_seq_call_le hM (vs := [dst, tmp, r]) rfl ?_
    ⟨dst, tmp, r, rfl, hsep, by dsimp [r]; omega, hR, h1⟩ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hw _ (by simp)
    · exact hw _ (by simp)
    · exact hR
  intro out mem₃ pos₃ hp₃
  obtain ⟨dst', tmp', r', ha, hout, hres, hbelow, hz₃, hf₃⟩ := hp₃
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨hd', ht', hr'⟩ := ha
  subst dst' tmp' r'
  have hlen : r - tmp = (k + 1) + n := by dsimp [r]; omega
  rw [hlen] at hout hres hz₃
  refine runs_ret_le (v := out) (Expr.eval_reg_of_eq rfl)
    ⟨keys, vals, tmp, dst, rfl, by simpa [Outcome.value, n, Nat.add_assoc] using hout, ?_, ?_, ?_⟩ ?_
  · intro i hi
    exact (hres i (hd ▸ hi)).trans (hData₂ i hi)
  · intro y hy
    change out ≤ y at hy
    rcases Nat.lt_or_ge y r with h | h
    · exact hz₃ _ (hout ▸ hy) h
    · exact (hf₃ _ h).trans (hz₂ _ h)
  · intro y hy
    exact (hbelow _ hy).trans ((hf₂ _ (.inl (by dsimp [r]; omega))).trans
      (hf₁ _ (.inl (hy.trans_le hsep))))
  · have hspan : r - dst = tmp - dst + (k + 1) + n := by dsimp [r]; omega
    simp [initBucketContract, initFillWordContract, moveDownContract, initBucketMoveContract,
      Expr.size, argsSize, hspan, n]
    omega

end MinCostFlow.HierPaths

end
