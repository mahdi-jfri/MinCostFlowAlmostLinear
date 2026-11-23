module

public import MinCostFlow.Num.DivisionLoop
public import MinCostFlow.Num.EffectiveLength
public import MinCostFlow.Num.ExtendCopy
import MinCostFlow.Num.ModulePlacement
import MinCostFlow.Num.DivisionBlockFacts
import MinCostFlow.Num.ExtendFacts
import MinCostFlow.Num.WordBounds
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Unsigned long division

The divisor is extended by one zero limb. Fresh memory supplies the initial zero
quotient and remainder. The quotient loop then processes all numerator limbs. The
result consists of an exact quotient of `K` limbs and remainder of `K+1` limbs.
-/

@[expose] public section
namespace MinCostFlow.Num
open WordRAM

/-- Fresh cells for the extended divisor, quotient, initial remainder, and digit steps. -/
def unsignedDivideSpace (K : ℕ) : ℕ := 3 * K + 2 + 5 * K * (K + 1)

/-- Arguments `[a,d,K,heap]`. -/
def unsignedDivideBody (length extend loop : ℕ) : Stmt :=
  .call 4 length [.reg 1, .reg 2] ;;
  .call 5 extend [.reg 1, .reg 2, .bin .add (.reg 2) (.const 1), .const 0, .reg 3] ;;
  .assign 6 (.bin .add (.reg 5) (.reg 2)) ;;
  .assign 7 (.bin .add (.reg 6) (.bin .add (.reg 2) (.const 1))) ;;
  .call 8 loop [.reg 0, .reg 3, .reg 4, .reg 2, .reg 2, .reg 5, .reg 6, .reg 7] ;;
  .ret (.reg 8)

/-- Unsigned division linked to its scan, copy, digit loop, and step modules. -/
def unsignedDivideModule (b h : ℕ) : List Stmt :=
  [unsignedDivideBody (b + 1) (b + 2) (b + 3)] ++
  (effectiveLengthModule (b + 1) ++ (extendCopyModule (b + 2) ++
    (divisionLoopModule (b + 3) (b + 4) ++ divisionStepModule (b + 4) h)))

/-- The quotient starts after the extended divisor. The final remainder ends at the
returned heap. Division by zero is excluded. -/
def unsignedDivideContract (w h : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d K heap, args = [a,d,K,heap] ∧ a + K ≤ heap ∧ d + K ≤ heap ∧
      Valid mem a h K ∧ Valid mem d h K ∧ 0 < unsignedVal mem d h K)
    (fun args mem mem' =>
      Valid mem' (heapArg args + args.getD 2 0 + 1) h (args.getD 2 0) ∧
      unsignedVal mem' (heapArg args + args.getD 2 0 + 1) h (args.getD 2 0) =
        unsignedVal mem (args.getD 0 0) h (args.getD 2 0) /
          unsignedVal mem (args.getD 1 0) h (args.getD 2 0) ∧
      Valid mem' (heapArg args + unsignedDivideSpace (args.getD 2 0) - (args.getD 2 0 + 1)) h (args.getD 2 0 + 1) ∧
      unsignedVal mem' (heapArg args + unsignedDivideSpace (args.getD 2 0) - (args.getD 2 0 + 1)) h (args.getD 2 0 + 1) =
        unsignedVal mem (args.getD 0 0) h (args.getD 2 0) %
          unsignedVal mem (args.getD 1 0) h (args.getD 2 0))
    (fun args _ => args.getD 2 0 * (300 * args.getD 2 0 + 644) + 51 * args.getD 2 0 + 85)
    (fun args _ => unsignedDivideSpace (args.getD 2 0))
  { C with post := fun args mem v mem' => v = heapArg args + unsignedDivideSpace (args.getD 2 0) ∧ C.post args mem v mem' }

/-- Unsigned division and its linked procedures are deterministic. -/
theorem unsignedDivideModule_noRand (b h : ℕ) : ∀ s ∈ unsignedDivideModule b h, s.NoRand := by
  intro s hs
  simp only [unsignedDivideModule, List.mem_append, List.mem_singleton] at hs
  rcases hs with rfl | hl | he | hloop | hstep
  · simp [unsignedDivideBody, Stmt.NoRand]
  · have he : s = effectiveLengthBody (b + 1) := by simpa [effectiveLengthModule] using hl
    subst s; exact effectiveLengthBody_noRand _
  · have he : s = extendCopyBody (b + 2) := by simpa [extendCopyModule] using he
    subst s; exact extendCopyBody_noRand _
  · have he : s = divisionLoopBody (b + 3) (b + 4) := by simpa [divisionLoopModule] using hloop
    subst s; exact divisionLoopBody_noRand _ _
  · exact divisionStepModule_noRand _ _ _ hstep

/-- Unsigned division has exact quotient and remainder and quadratic cost. -/
theorem unsignedDivide_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 3 * h + 2 ≤ w)
    (hp : p.HasAt b (unsignedDivideModule b h)) :
    MeetsContract w p b (unsignedDivideContract w h) := by
  have htail := hasAt_append_right hp
  change p.HasAt (b + 1) _ at htail
  have hl := hasAt_append_left htail
  have htail₂ := hasAt_append_right htail
  change p.HasAt (b + 2) _ at htail₂
  have he := hasAt_append_left htail₂
  have htail₃ := hasAt_append_right htail₂
  change p.HasAt (b + 3) _ at htail₃
  have hloop := hasAt_append_left htail₃
  have hstep := hasAt_append_right htail₃
  change p.HasAt (b + 4) _ at hstep
  have hb := base_lt_word (show 2 * h + 2 ≤ w by omega)
  have hw1 : 1 < 2 ^ w := lt_trans (Nat.one_lt_pow (Nat.ne_of_gt hh) (by decide)) hb
  have hlength := effectiveLength_meetsContract (h := h) hw1 hl
  have hextend := extendCopy_meetsContract (h := h) hw1 he
  have hs := divisionStep_meetsContract hh hw hstep
  have hloopC := divisionLoop_meetsContract hw1 hb hloop hs
  have hentry : p.procs[b]? = some (unsignedDivideBody (b + 1) (b + 2) (b + 3)) := hp.head
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨a,d,K,heap,rfl,ha,hd,hva,hvd,hV⟩,hz,hbound⟩
  change ZeroFrom mem heap at hz
  change heap + unsignedDivideSpace K < 2 ^ w at hbound
  have hbound' : heap + 3 * K + 2 + 5 * K * (K + 1) < 2 ^ w := by
    simpa only [unsignedDivideSpace, Nat.add_assoc] using hbound
  have haw : a < 2 ^ w := hwords a (by simp)
  have hdw : d < 2 ^ w := hwords d (by simp)
  have hKw : K < 2 ^ w := hwords K (by simp)
  have hheapw : heap < 2 ^ w := hwords heap (by simp)
  have hMw : K + 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold unsignedDivideBody
  refine runs_seq_call_le hlength (vs := [d,K]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨d,K,rfl,by omega,hvd⟩
  · intro n mem₀ pos₀ hpost₀
    rcases hpost₀ with ⟨hmem,hnK,hzeros,htop,hvalue⟩
    subst mem₀
    change n ≤ K at hnK
    change (0 < n → 0 < mem (d + (n - 1))) at htop
    change unsignedVal mem d h n = unsignedVal mem d h K at hvalue
    have hn : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := by omega
      rw [hn0, unsignedVal] at hvalue
      omega
    have hnw : n < 2 ^ w := by omega
    have hprefix : Valid mem d h n := fun i hi => hvd i (lt_of_lt_of_le hi hnK)
    have hVhi : unsignedVal mem d h K < capacity h n := by rw [← hvalue]; exact unsignedVal_lt hprefix
    have hVlo : capacity h (n - 1) ≤ unsignedVal mem d h K := by
      rw [← hvalue]; exact capacity_le_unsignedVal_of_top_pos hn (htop hn)
    refine runs_seq_call_le hextend (vs := [d,K,K+1,0,heap]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨⟨d,K,K+1,0,heap,rfl,by omega,hd,base_pos h,hvd⟩,hz,by change heap + (K+1) < 2^w; omega⟩
    · intro q mem₁ pos₁ hpost₁
      rcases hpost₁ with ⟨hq,hlo,hhi,hframe,hzero,hlist⟩
      change q = heap + (K + 1) at hq
      change (∀ z < heap, mem₁ z = mem z) at hframe
      change ListAt mem₁ heap (extendedLimbs mem d 0 K (K+1)) at hlist
      have hvdiv := valid_listAt hlist (extendedLimbs_lt hvd (base_pos h))
      rw [extendedLimbs_length] at hvdiv
      have hdiv : unsignedVal mem₁ heap h (K+1) = unsignedVal mem d h K := by
        have hx := unsignedVal_listAt (h := h) hlist
        rw [extendedLimbs_length, listVal_extended_zero (by omega)] at hx
        exact hx
      have hvnum : Valid mem₁ a h K := by intro i hi; rw [hframe _ (by omega)]; exact hva i hi
      have hnum : unsignedVal mem₁ a h K = unsignedVal mem a h K :=
        unsignedVal_congr (fun i hi => hframe _ (by omega))
      have htop₁ : 0 < mem₁ (heap + (n-1)) := top_pos_of_capacity_le_unsignedVal hvdiv hn
        (by omega) (by rw [hdiv]; exact hVlo) (by rw [hdiv]; exact hVhi)
      have hzeros₁ := unsignedVal_high_zero_of_lt hvdiv (show n ≤ K+1 by omega)
        (show unsignedVal mem₁ heap h (K+1) < capacity h n by rw [hdiv]; exact hVhi)
      have hqw : q < 2^w := by omega
      have hrw : q + K < 2^w := by omega
      have hworkw : q + K + (K+1) < 2^w := by omega
      refine runs_seq_assign_le (v := q + K) (by eval_expr) ?_
      refine runs_seq_assign_le (v := q + K + (K+1)) (by eval_expr) ?_
      refine runs_seq_call_le hloopC (vs := [a,heap,n,K,K,q,q+K,q+K+(K+1)])
        (by eval_expr) (by wram_words) ?_ ?_
      · refine ⟨a,heap,n,K,K,q,q+K,q+K+(K+1),rfl,le_rfl,hn,hnK,by omega,by omega,
          le_rfl,rfl,hvnum,hvdiv,zeroFrom_valid hzero le_rfl,
          zeroFrom_valid hzero (by omega),htop₁,hzeros₁,?_,?_,?_⟩
        · have hzR : unsignedVal mem₁ (q+K) h (K+1) = 0 :=
            unsignedVal_zero (fun i hi => hzero _ (by omega))
          rw [hzR,hdiv]; exact hV
        · intro z hz; exact hzero z (by omega)
        · omega
      · intro v mem₂ pos₂ hpost₂
        rcases hpost₂ with ⟨hv,hz₂,hframe₂,hvq,hqvalue,hvr,hrvalue⟩
        change v = q+K+(K+1)+5*K*(K+1) at hv
        change (∀ z < q+K+(K+1), z < q ∨ q+K ≤ z → mem₂ z = mem₁ z) at hframe₂
        change Valid mem₂ q h K at hvq
        change unsignedVal mem₂ q h K = loopNumerator mem₁ a (q+K) h K K / unsignedVal mem₁ heap h (K+1) at hqvalue
        change Valid mem₂ (v-(K+1)) h (K+1) at hvr
        change unsignedVal mem₂ (v-(K+1)) h (K+1) = loopNumerator mem₁ a (q+K) h K K % unsignedVal mem₁ heap h (K+1) at hrvalue
        have hzR : unsignedVal mem₁ (q+K) h (K+1) = 0 :=
          unsignedVal_zero (fun i hi => hzero _ (by omega))
        have hX : loopNumerator mem₁ a (q+K) h K K = unsignedVal mem a h K := by
          rw [loopNumerator,hzR,zero_mul,zero_add,hnum]
        rw [hX,hdiv] at hqvalue hrvalue
        have hvw : v < 2^w := by omega
        refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
        · change v = heap + unsignedDivideSpace K ∧ heap ≤ v ∧ v ≤ heap + unsignedDivideSpace K ∧
            (∀ z < heap, mem₂ z = mem z) ∧ ZeroFrom mem₂ v ∧
            Valid mem₂ (heap+K+1) h K ∧
            unsignedVal mem₂ (heap+K+1) h K = unsignedVal mem a h K / unsignedVal mem d h K ∧
            Valid mem₂ (heap+unsignedDivideSpace K-(K+1)) h (K+1) ∧
            unsignedVal mem₂ (heap+unsignedDivideSpace K-(K+1)) h (K+1) = unsignedVal mem a h K % unsignedVal mem d h K
          have hvexact : v = heap + unsignedDivideSpace K := by unfold unsignedDivideSpace; omega
          refine ⟨hvexact,by omega,by omega,?_,hz₂,?_,?_,?_,?_⟩
          · intro z hz; exact (hframe₂ z (by omega) (Or.inl (by omega))).trans (hframe z hz)
          · simpa only [hq, Nat.add_assoc] using hvq
          · simpa only [hq, Nat.add_assoc] using hqvalue
          · simpa only [hvexact] using hvr
          · simpa only [hvexact] using hrvalue
        · simp only [unsignedDivideContract,effectiveLengthContract,extendCopyContract,divisionLoopContract,
            heapContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_reg,Expr.size_bin,
            Expr.size_const,argsSize_cons,argsSize_nil]
          omega

end MinCostFlow.Num
