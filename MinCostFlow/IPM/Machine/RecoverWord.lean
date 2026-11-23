module

public import MinCostFlow.IPM.Machine.RoundRatFacts
public import MinCostFlow.Num.PackWord
import MinCostFlow.Num.DivisionStepFacts
import WordRAM.Tactic

/-!
# Recovering an exact bounded-program output word

The rounding table contains integers in signed fixed-point form.
Take the exact integer floor and pack its nonnegative magnitude
into the solver's one-word output format.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- On [source,L,P,heap], return the integral coordinate as a word. -/
def recoverWordBody (floor pack : ℕ) : Stmt :=
  .call 4 floor [.reg 0,.reg 1,.reg 2,.reg 3] ;;
  .call 5 pack [.bin .sub (.reg 4) (.reg 1),.reg 1] ;;
  .ret (.reg 5)

/-- The decoded output word and scratch frame of recovery. -/
def recoverWordContract (w h : ℕ) (q : ℕ) : Contract where
  pre args mem := ∃ a L P heap,args=[a,L,P,heap] ∧ a+L≤heap ∧
    q<2^w ∧ RatAt mem a h L P (q:ℚ) ∧
    ZeroFrom mem heap ∧ heap+2*L+1<2^w
  post args mem value final :=
    value=q ∧ (∀ z<heapArg args,final z=mem z) ∧ ZeroFrom final (heapArg args+2*args.getD 1 0+1)
  cost args _ := 100*args.getD 1 0+150

/-- The output conversion contains no random instruction. -/
theorem recoverWord_noRand (floor pack : ℕ) : (recoverWordBody floor pack).NoRand := by
  simp [recoverWordBody,Stmt.NoRand]

/-- For an integral nonnegative coordinate, unscaling and packing
return the same exact number. -/
theorem recoverWord_meetsContract {w h entry floor pack : ℕ} {p : Program}
    (hAt : p.procs[entry]?=some (recoverWordBody floor pack))
    (hFloor : MeetsContract w p floor (Num.floorContract w h))
    (hPack : MeetsContract w p pack (Num.packWordContract w h))
    (q : ℕ) :
    MeetsContract w p entry (recoverWordContract w h q) := by
  apply meetsContract_of_runs hAt
  intro args mem pos ω hw hpre
  obtain ⟨a,L,P,heap,rfl,hEnd,hQ,hValue,hz,hSpace⟩ := hpre
  have hArg : (Num.floorContract w h).pre [a,L,P,heap] mem :=
    ⟨⟨a,L,P,heap,rfl,hEnd,hValue.1⟩,hz,by change heap+(2*L+1)<2^w; omega⟩
  apply runs_start_le
  unfold recoverWordBody
  refine runs_seq_call_le hFloor (vs:=[a,L,P,heap]) rfl hw hArg ?_
  intro out mid pos' hout
  obtain ⟨he,hFrame,hZero,hValid,hn⟩ := round_floor_output hValue hout
  have hs : out-L=heap+L+1 := by omega
  have hUnsigned : Num.unsignedVal mid (out-L) h L=q := by
    rw [hs]
    apply Num.unsignedVal_of_intVal_nonneg hValid
    simpa using hn
  have hV' : Num.Valid mid (out-L) h L := hs ▸ hValid
  have ho : out<2^w := by omega
  have hoL : out-L<2^w := by omega
  have hLW : L<2^w := hw _ (by simp)
  refine runs_seq_call_le hPack (vs:=[out-L,L]) (by eval_expr) (by wram_words)
    ⟨out-L,L,rfl,by omega,hV',hUnsigned.symm ▸ hQ⟩ ?_
  intro r final pos'' hp
  obtain ⟨hm,hr⟩ := hp
  have hmem : final=mid := hm
  subst final
  have hR : r=q := hr.trans hUnsigned
  refine runs_ret_le (v:=r) rfl ?_ ?_
  · change r=q ∧ (∀ z<heap,mid z=mem z) ∧ ZeroFrom mid (heap+2*L+1)
    exact ⟨hR,hFrame,he ▸ hZero⟩
  · change 0+4+(66*L+106)+2+4+(25*L+6)+2+2≤100*L+150
    omega

end MinCostFlow.IPM.Machine
