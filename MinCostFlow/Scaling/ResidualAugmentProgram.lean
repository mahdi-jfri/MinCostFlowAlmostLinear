module

public import MinCostFlow.Scaling.RoutingAugmentLayout
import MinCostFlow.Scaling.ModulePlacement
import WordRAM.Tactic

/-!
# Integer residual flow augmentation from its two stored halves

The residual solver stores forward corrections before reverse corrections.
Pass those two addresses and the starting flow to the augmentation scan.
Its unsigned result represents exactly the integer model update whenever
the update is nonnegative. All hypotheses here concern the stored numbers.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[start,residual,count,heap]`. -/
def residualAugmentBody (scan : ℕ) : Stmt :=
  .call 4 scan [.reg 0,.reg 1,.bin .add (.reg 1) (.reg 2),.reg 2,.reg 3] ;;
  .ret (.reg 4)

/-- The address adapter and unsigned augmentation scan. -/
def residualAugmentModule (b : ℕ) : List Stmt := residualAugmentBody (b+1) :: routingAugmentModule (b+1)

/-- The exact integer update is stored in its nonnegative unsigned layout. -/
def residualAugmentContract (w : ℕ) {m : ℕ} (start : Fin m → ℤ) (delta : Fin (m+m) → ℤ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ a d heap, args = [a,d,m,heap] ∧
      ListAt mem a (List.ofFn (fun e => (start e).toNat)) ∧
      ListAt mem d (List.ofFn (fun e => (delta e).toNat)) ∧ a+m ≤ heap ∧ d+(m+m) ≤ heap ∧
      (∀ e,0 ≤ start e) ∧ (∀ e,0 ≤ delta e) ∧
      (∀ e,0 ≤ start e+delta (Fin.castAdd m e)-delta (Fin.natAdd m e)) ∧
      (∀ e,(start e).toNat+(delta (Fin.castAdd m e)).toNat < 2^w ∧
        (delta (Fin.natAdd m e)).toNat < 2^w) ∧ 1 < 2^w)
    (fun args _ mem' => ListAt mem' (heapArg args) (List.ofFn
      (fun e => (start e+delta (Fin.castAdd m e)-delta (Fin.natAdd m e)).toNat)))
    (fun _ _ => 100*m+100) (fun _ _ => m)
  { C with post := fun args mem ret mem' => C.post args mem ret mem' ∧ ret = heapArg args+m }

/-- All augmentation procedures use no random instruction. -/
theorem residualAugmentModule_noRand (b : ℕ) : ∀ body ∈ residualAugmentModule b, body.NoRand := by
  intro body hb
  rcases List.mem_cons.mp hb with rfl | hb
  · simp only [residualAugmentBody,Stmt.NoRand,and_self]
  · have he : body = routingAugmentBody (b+1) := by simpa only [routingAugmentModule,List.mem_singleton] using hb
    subst body
    exact routingAugmentBody_noRand _

/-- The adapter and scan compute exactly the integer residual update with
linear cost, exact allocation, and preserved source arrays. -/
theorem residualAugment_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b (residualAugmentModule b)) {m : ℕ}
    (start : Fin m → ℤ) (delta : Fin (m+m) → ℤ) :
    MeetsContract w p b (residualAugmentContract w start delta) := by
  have hk := routingAugment_meetsContract (w := w) (hasAt_tail hp) (routingAugmentTriples start delta)
  have hlen : (routingAugmentTriples start delta).length = m := by
    simp only [routingAugmentTriples,List.length_ofFn]
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a,d,heap,rfl,ha,hd,haend,hdend,hstart,hdelta,hupdate,hvalues,hw⟩,hz,hs⟩ := hpre
  change ZeroFrom mem heap at hz
  change heap+m < 2^w at hs
  have hh : heap < 2^w := by omega
  have hm : m < 2^w := by omega
  have hdr : d+m < 2^w := by omega
  obtain ⟨hsa,hda,hra⟩ := routingAugment_sources start delta ha hd
  have hout := routingAugment_words start delta hstart hdelta hupdate
  apply runs_start_le
  unfold residualAugmentBody
  refine runs_seq_call_le hk (vs := [a,d,d+m,m,heap]) (by eval_expr) ?_ ?_ ?_
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hwords _ List.mem_cons_self
    · exact hwords _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact hdr
    · exact hm
    · exact hh
  · refine ⟨⟨a,d,d+m,heap,by rw [hlen],hsa,hda,hra,by rw [hlen]; omega,
      by rw [hlen]; omega,by rw [hlen]; omega,?_,hw⟩,hz,?_⟩
    · intro x hx
      obtain ⟨e,he⟩ := List.mem_ofFn.mp hx
      rw [← he]
      exact hvalues e
    · change heap+(routingAugmentTriples start delta).length < 2^w
      rw [hlen]
      exact hs
  · intro ret memR posR hpost
    obtain ⟨⟨hlo,hhi,hframe,hzR,hatR⟩,hret⟩ := hpost
    change ret = heap+(routingAugmentTriples start delta).length at hret
    rw [hlen] at hret
    change (∀ x < heap,memR x = mem x) at hframe
    change ZeroFrom memR ret at hzR
    change ListAt memR heap ((routingAugmentTriples start delta).map (fun x => x.1+x.2.1-x.2.2)) at hatR
    rw [hout] at hatR
    have hr : ret < 2^w := by omega
    refine runs_ret_le (v := ret) (by eval_expr) ?_ ?_
    · change (heap ≤ ret ∧ ret ≤ heap+m ∧ (∀ x < heap,memR x = mem x) ∧
        ZeroFrom memR ret ∧ ListAt memR heap _) ∧ ret = heap+m
      exact ⟨⟨by omega,by omega,hframe,hzR,hatR⟩,hret⟩
    · simp only [residualAugmentContract,routingAugmentContract,heapContract,hlen,
        argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_reg]
      omega

end MinCostFlow.Scaling.Machine
