module

public import MinCostFlow.IPM.Machine.RecoverWord
import WordRAM.Tactic

/-!
# Writing the recovered circulation table

The recovery scan reads the kept edge prefix in order. Each
coordinate becomes one nonnegative output word and the input
and output regions are disjoint.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- On [source,L,P,dest,count,heap], recover the first count coordinates. -/
def recoverScanBody (entry wordEntry : ℕ) : Stmt :=
  .cond (.reg 4)
    (.call 6 wordEntry [.reg 0,.reg 1,.reg 2,.reg 5] ;;
     .store (.reg 3) (.reg 6) ;;
     .call 7 entry [.bin .add (.reg 0) (.reg 1),.reg 1,.reg 2,.bin .add (.reg 3) (.const 1),
       .bin .sub (.reg 4) (.const 1),
       .bin .add (.reg 5) (.bin .add (.bin .mul (.const 2) (.reg 1)) (.const 1))] ;;
     .ret (.reg 7))
    (.ret (.reg 5))

/-- Recovery uses linear workspace in the number of input limbs. -/
def recoverScanSpace (L m : ℕ) : ℕ := m*(2*L+1)

/-- A linear-cost output scan preserves the rest of the allocated prefix. -/
def recoverScanContract (w h : ℕ) : Contract where
  pre args mem := ∃ a L P d m heap,args=[a,L,P,d,m,heap] ∧ d+m≤a ∧
    a+m*L≤heap ∧ 2<2^w ∧ ZeroFrom mem heap ∧ heap+recoverScanSpace L m<2^w ∧
    ∀ i<m,∃ q : ℕ,q<2^w ∧ RatAt mem (a+i*L) h L P (q:ℚ)
  post args mem v final :=
    let a := args.getD 0 0
    let L := args.getD 1 0
    let P := args.getD 2 0
    let d := args.getD 3 0
    let m := args.getD 4 0
    let heap := heapArg args
    v=heap+recoverScanSpace L m ∧ ZeroFrom final v ∧
      (∀ z<heap,z<d ∨ d+m≤z → final z=mem z) ∧
      ∀ i<m,RatAt mem (a+i*L) h L P (final (d+i):ℚ)
  cost args _ := args.getD 4 0*(100*args.getD 1 0+240)+8

/-- The recovery scan uses no randomness. -/
theorem recoverScan_noRand (entry wordEntry : ℕ) : (recoverScanBody entry wordEntry).NoRand := by
  simp [recoverScanBody,Stmt.NoRand]

set_option maxHeartbeats 500000 in
set_option maxRecDepth 4096 in
/-- Recovery writes the exact integral prefix, one word per edge,
with a deterministic loop and explicit linear cost. -/
theorem recoverScan_meetsContract {w h entry wordEntry : ℕ} {p : Program}
    (hBody : p.procs[entry]?=some (recoverScanBody entry wordEntry))
    (hWord : ∀ q,MeetsContract w p wordEntry (recoverWordContract w h q)) :
    MeetsContract w p entry (recoverScanContract w h) := by
  apply meetsContract_of_rec (fun args _ => args.getD 4 0) hBody
  intro fuel ih args mem pos ω hw hpre hFuel
  obtain ⟨a,L,P,d,m,heap,rfl,hd,ha,hTwo,hz,hspace,hVals⟩ := hpre
  change m=fuel at hFuel
  subst fuel
  have hOne : 1<2^w := by omega
  have hA : a<2^w := hw _ (by simp)
  have hL : L<2^w := hw _ (by simp)
  have hP : P<2^w := hw _ (by simp)
  have hD : d<2^w := hw _ (by simp)
  have hH : heap<2^w := hw _ (by simp)
  apply runs_start_le
  unfold recoverScanBody
  cases m with
  | zero =>
    refine runs_cond_le (v:=0) rfl (fun hn => (hn rfl).elim) ?_
    intro _
    refine runs_ret_le (v:=heap) rfl ?_ ?_
    · change heap=heap+recoverScanSpace L 0 ∧ ZeroFrom mem heap ∧
        (∀ z<heap,z<d ∨ d+0≤z → mem z=mem z) ∧ ∀ i<0,RatAt mem (a+i*L) h L P (mem (d+i):ℚ)
      exact ⟨by simp [recoverScanSpace],hz,fun _ _ _ => rfl,fun _ h => by omega⟩
    · simp only [recoverScanContract,List.getD_cons_succ,List.getD_cons_zero,Nat.zero_mul,Nat.zero_add,Expr.size_reg]
      decide
  | succ m =>
    have hm : 0<m+1 := by omega
    have hSpace' : recoverScanSpace L (m+1)=recoverScanSpace L m+(2*L+1) := by
      simp [recoverScanSpace,Nat.add_mul]
    have hAEnd : a+m*L+L≤heap := by rw [Nat.succ_mul] at ha; omega
    have hScratch : heap+2*L+1<2^w := by omega
    have hAL : a+L<2^w := by omega
    obtain ⟨q,hQ,hVal⟩ := hVals 0 hm
    have hVal₀ : RatAt mem a h L P (q:ℚ) := by simpa using hVal
    refine runs_cond_le (v:=m+1) rfl ?_ (fun he => by omega)
    intro _
    refine runs_seq_call_le (hWord q) (vs:=[a,L,P,heap]) rfl (by wram_words)
      ⟨a,L,P,heap,rfl,by omega,hQ,hVal₀,hz,hScratch⟩ ?_
    intro value mid pos₁ hout
    obtain ⟨hValue,hFrame,hZero⟩ := hout
    have hV : value=q := hValue
    have hValW : value<2^w := hV.symm ▸ hQ
    have hFrame₁ : ∀ z<heap,mid z=mem z := hFrame
    let next := heap+(2*L+1)
    have hZero₁ : ZeroFrom mid next := by change ZeroFrom mid (heap+2*L+1) at hZero; simpa [next,Nat.add_assoc] using hZero
    have hNext : next<2^w := by dsimp [next]; omega
    have hNextW : heap+(2*L+1)<2^w := hNext
    have hD1 : d+1<2^w := by omega
    have hmW₀ : m+1<2^w := hw (m+1) (by simp)
    have hmW : m<2^w := by omega
    have hBig : 2*L+1<2^w := by omega
    have hBig' : 2*L<2^w := by omega
    let stored := Function.update mid d value
    have hMemStore : ∀ z<heap,z≠d → stored z=mem z := by
      intro z hz hd'
      exact (Function.update_of_ne hd' _ _).trans (hFrame₁ z hz)
    have hStoreZ : ZeroFrom stored next := by
      intro z hz'
      have hNe : z≠d := by dsimp [next] at hz'; omega
      exact (Function.update_of_ne hNe _ _).trans (hZero₁ z hz')
    refine runs_seq_store_le (x:=d) (v:=value) rfl rfl ?_
    let recArgs := [a+L,L,P,d+1,m,next]
    have hPre : (recoverScanContract w h).pre recArgs stored := by
      refine ⟨a+L,L,P,d+1,m,next,rfl,by omega,by dsimp [next]; omega,hTwo,hStoreZ,by dsimp [next]; omega,?_⟩
      intro i hi
      obtain ⟨z,hz',hval⟩ := hVals (i+1) (by omega)
      rw [Nat.succ_mul] at hval
      have hAddr : a+L+i*L=a+(i*L+L) := by omega
      refine ⟨z,hz',?_⟩
      rw [hAddr]
      apply hval.agree
      intro k hk
      have hlim := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hlim
      exact hMemStore _ (by omega) (by omega)
    refine runs_seq_call_le ih (vs:=recArgs) (by
      dsimp only [recArgs,next]
      eval_expr
      rw [Expr.eval_sub (show (Expr.reg 4).eval w _=some (m+1) from rfl)
        (show (Expr.const 1).eval w _=some 1 from by eval_expr) hmW₀]
      simp)
      (by dsimp [recArgs]; wram_words) ⟨hPre,by change m<m+1; omega⟩ ?_
    intro out final pos₂ hRes
    obtain ⟨he,hZ,hFr,hOut⟩ := hRes
    change out=next+recoverScanSpace L m at he
    change ∀ z<next,z<d+1 ∨ (d+1)+m≤z → final z=stored z at hFr
    change ∀ i<m,RatAt stored (a+L+i*L) h L P (final (d+1+i):ℚ) at hOut
    refine runs_ret_le (v:=out) rfl ?_ ?_
    · change out=heap+recoverScanSpace L (m+1) ∧ ZeroFrom final out ∧
        (∀ z<heap,z<d ∨ d+(m+1)≤z → final z=mem z) ∧
        ∀ i<m+1,RatAt mem (a+i*L) h L P (final (d+i):ℚ)
      refine ⟨by dsimp [next] at he; omega,hZ,?_,?_⟩
      · intro z hz' hs
        have hh : z<next := by dsimp [next]; omega
        have hs' : z<d+1 ∨ (d+1)+m≤z := by omega
        exact (hFr z hh hs').trans (hMemStore z hz' (by omega))
      · intro i hi
        cases i with
        | zero =>
          have heq : final d=q := (hFr d (by dsimp [next]; omega) (Or.inl (by omega))).trans
            (by simp [stored,hV])
          simpa [heq] using hVal₀
        | succ i =>
          have hi' : i<m := by omega
          rw [Nat.succ_mul,show d+(i+1)=d+1+i by omega,show a+(i*L+L)=a+L+i*L by omega]
          apply (hOut i hi').agree
          intro k hk
          have hlim := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hi')
          rw [Nat.succ_mul] at hlim
          exact (hMemStore _ (by omega) (by omega)).symm
    · change (2+4+(100*L+150)+2+4+18+(m*(100*L+240)+8)+2)+2≤(m+1)*(100*L+240)+8
      rw [show (m+1)*(100*L+240)=m*(100*L+240)+(100*L+240) from Nat.succ_mul _ _]
      omega

end MinCostFlow.IPM.Machine
