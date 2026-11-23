module

public import MinCostFlow.Num.Copy
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Writing a computed block into an array

Cycle updates and vector evaluation write computed values into a reserved
array. A forward copy between disjoint blocks preserves every cell outside
the destination. In particular it leaves the fresh heap untouched when
both blocks end below the heap pointer.
-/

@[expose] public section
namespace MinCostFlow.Num.IPM
open WordRAM

/-- Arguments `[source,L,destination]`. -/
def writeBlockModule (b : ℕ) := copyModule b

/-- Copy disjoint blocks without allocating memory. The returned value is
the end of the destination block; all other memory cells are preserved. -/
def writeBlockContract (w h : ℕ) : Contract where
  pre args mem := ∃ src L dst,args=[src,L,dst] ∧ src+L<2^w ∧ dst+L<2^w ∧
    (src+L≤dst ∨ dst+L≤src) ∧ Valid mem src h L
  post args mem v mem' := v=args.getD 2 0+args.getD 1 0 ∧
    (∀z,z<args.getD 2 0 ∨ args.getD 2 0+args.getD 1 0≤z → mem' z=mem z) ∧
    (∀i<args.getD 1 0,mem' (args.getD 2 0+i)=mem (args.getD 0 0+i)) ∧
    Valid mem' (args.getD 2 0) h (args.getD 1 0) ∧
    intVal mem' (args.getD 2 0) h (args.getD 1 0)=intVal mem (args.getD 0 0) h (args.getD 1 0)
  cost args _ := 17*args.getD 1 0+12

/-- Array writes are deterministic. -/
theorem writeBlockModule_noRand (b : ℕ) : ∀ s∈writeBlockModule b,s.NoRand := by
  intro s hs
  simp only [writeBlockModule,copyModule,List.mem_singleton] at hs
  subst s
  exact copyBody_noRand

private theorem writeLoop {w src L dst : ℕ} (p : Program) (mem : ℕ→ℕ) (pos : ℕ)
    (hw : 1<2^w) (hs : src+L<2^w) (hd : dst+L<2^w)
    (hdis : src+L≤dst ∨ dst+L≤src) :
    Triple w p (fun st => st=startState [src,L,dst] mem pos)
      (forRange 3 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 2) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))))
      (normalPost fun st => st.regs 1=L ∧ st.regs 2=dst ∧
        (∀i<L,st.mem (dst+i)=mem (src+i)) ∧
        (∀z,z<dst ∨ dst+L≤z → st.mem z=mem z))
      (fun _ => 17*L+7) := by
  have hl := Triple.forRange_const (p:=p) (r:=3) (lo:=.const 0) (hi:=.reg 1)
    (body:=.store (.bin .add (.reg 2) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3))))
    (P:=fun st => st=startState [src,L,dst] mem pos)
    (Inv:=fun i st => st.regs 0=src ∧ st.regs 1=L ∧ st.regs 2=dst ∧ st.regs 3=i ∧
      (∀j < i,st.mem (dst+j)=mem (src+j)) ∧ (∀z,z<dst ∨ dst+i≤z → st.mem z=mem z))
    8 0 L (Nat.zero_le L) hw (fun _ => by omega)
    (fun st he => by
      subst st
      refine ⟨by eval_expr,?_⟩
      simp [startState])
    (fun _ _ _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by
      have h1 := hi.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω hst
      rcases hst with ⟨h0,h1,h2,h3,hcopy,hframe⟩
      have hread : st.mem (src+i)=mem (src+i) := hframe _ (by rcases hdis with hh | hh <;> omega)
      apply runs_start_le
      refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
      · change (_ ∧ _) ∧ _
        refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,h3⟩
        · simpa using h0
        · simpa using h1
        · simpa using h2
        · simp
        · intro j hj
          dsimp only
          by_cases he : j=i
          · subst j
            simp [hread]
          · rw [Function.update_of_ne (by omega)]
            exact hcopy j (by omega)
        · intro z hz
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe z (by omega)
      · wram_cost)
  refine hl.conseq (fun _ he => he) ?_ ?_
  · intro o st ho
    cases o with
    | returned v => exact False.elim ho
    | normal => exact ⟨ho.2.1,ho.2.2.1,ho.2.2.2.2⟩
  · intro _ _
    simp only [Nat.sub_zero,Expr.size_const,Expr.size_reg]
    omega

/-- Copying into an array changes only the designated destination block. -/
theorem writeBlock_meetsContract {w h b : ℕ} {p : Program}
    (hw : 1<2^w) (hp : p.HasAt b (writeBlockModule b)) :
    MeetsContract w p b (writeBlockContract w h) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨src,L,dst,rfl,hs,hd,hdis,hv⟩
  apply runs_start_le
  unfold copyBody
  refine runs_seq_triple_le (writeLoop p mem pos hw hs hd hdis) rfl ?_
  intro st ⟨h1,h2,hcopy,hframe⟩
  refine runs_ret_le (by eval_expr) ?_ ?_
  · change dst+L=dst+L ∧ (∀z,z<dst ∨ dst+L≤z → st.mem z=mem z) ∧
      (∀i<L,st.mem (dst+i)=mem (src+i)) ∧ Valid st.mem dst h L ∧
      intVal st.mem dst h L=intVal mem src h L
    exact ⟨rfl,hframe,hcopy,fun i hi => hcopy i hi ▸ hv i hi,intVal_congr hcopy⟩
  · simp only [writeBlockContract,List.getD_cons_zero,List.getD_cons_succ,Expr.size_bin,Expr.size_reg]
    omega

/-- Writing below the heap leaves its zero suffix available for later calls. -/
theorem zeroFrom_writeBlock {mem mem' : ℕ→ℕ} {dst L heap : ℕ}
    (hframe : ∀z,z<dst ∨ dst+L≤z → mem' z=mem z) (hd : dst+L≤heap)
    (hz : ZeroFrom mem heap) : ZeroFrom mem' heap := by
  intro z hz'
  rw [hframe z (Or.inr (by omega))]
  exact hz z hz'

end MinCostFlow.Num.IPM
