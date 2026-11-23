module

public import MinCostFlow.IPM.Machine.RoundMachine
public import MinCostFlow.IPM.Machine.RecoverScan
public import MinCostFlow.IPM.Machine.RecoverPrefix
public import MinCostFlow.IPM.Machine.EpochFlowCopy
import WordRAM.Tactic

/-!
# Rounding and extracting a solver result

Copy the selected search flow to fresh working storage. This keeps
the graph and numerical tables before the mutable flow even when
the successful test returned the initial half-slack table. Round
the copy and extract the original-edge prefix to the solver output.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling Rounding

/-- On [n,M,graph,cost,source,L,P,one,heap,dest,m], round and recover. -/
def roundExtractBody (copy roundEntry extract : ℕ) : Stmt :=
  .call 11 copy [.reg 4,.reg 1,.reg 5,.reg 8] ;;
  .call 12 roundEntry [.reg 0,.reg 1,.reg 2,.reg 3,.reg 8,.reg 5,.reg 6,.reg 7,.reg 11] ;;
  .call 13 extract [.reg 8,.reg 5,.reg 6,.reg 9,.reg 10,.reg 12] ;;
  .ret (.reg 13)

/-- The copy, round, and recovery composition is deterministic. -/
theorem roundExtract_noRand (copy roundEntry extract : ℕ) :
    (roundExtractBody copy roundEntry extract).NoRand := by
  simp [roundExtractBody,Stmt.NoRand]

/-- Exact copied coordinates agree with the input flow. -/
theorem roundFlowAt_of_copy {w h L P : ℕ} (I : Instance)
    {source heap out : ℕ} {mem final : ℕ → ℕ} {f : Fin I.m → ℚ}
    (hf : RoundFlowAt I mem source h L P f)
    (hc : (epochFlowCopyContract w).post [source,I.m,L,heap] mem out final) :
    RoundFlowAt I final heap h L P f := by
  intro e
  have hlim := Nat.mul_le_mul_right L (Nat.succ_le_of_lt e.isLt)
  rw [Nat.succ_mul] at hlim
  have hEq (i : ℕ) (hi : i<L) : final (heap+e.val*L+i)=mem (source+e.val*L+i) := by
    have he : e.val*L+i<I.m*L := by omega
    have h := hc.1.2.2.2.2 (e.val*L+i) he
    change final (heap+(e.val*L+i))=mem (source+(e.val*L+i)) at h
    simpa only [Nat.add_assoc] using h
  have hAt := hf e
  constructor
  · intro i hi
    rw [hEq i hi]
    exact hAt.1 i hi
  · unfold readRat
    rw [Num.intVal_congr hEq]
    exact hAt.2

set_option maxHeartbeats 500000 in
/-- Copy the target flow, round it, and read an original prefix whose
rounded values are certified optimal. -/
theorem roundExtract_prefix_runs {w h L P copy roundEntry extract init loop A : ℕ}
    (D : DynForest) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {p : Program} (hCopy : MeetsContract w p copy (epochFlowCopyContract w))
    (hRound : p.procs[roundEntry]?=some (roundMachineBody init loop))
    (hExtract : MeetsContract w p extract (recoverScanContract w h))
    (J : Circulation) (I : Instance) (hm : J.m ≤ I.m)
    (f : Fin I.m → ℚ)
    (q : Fin J.m → ℕ) (hq : ∀ e,(roundFlow D I f).flowArr
      ⟨e.val,e.isLt.trans_le hm⟩=(q e:ℚ))
    (hOpt : J.Optimal (fun e => (q e:ℝ))) (hQW : ∀ e,q e<2^w)
    (graph cost source one heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hWords : ∀ z∈[I.n,I.m,graph,cost,source,L,P,one,heap,dest,J.m],z<2^w)
    (hTwo : 2<2^w) (hZero : ZeroFrom mem heap)
    (hEnd : source+I.m*L≤heap) (hDest : dest+J.m≤heap)
    (hFlow : RoundFlowAt I mem source h L P f)
    (hSpace :
      let b := heap+I.m*L
      let r := roundMachineSpace (allocation 6 [I.n,L,P,b]) A L I.m
      b+r+recoverScanSpace L J.m<2^w)
    (hRunner :
      let b := heap+I.m*L
      ∀ mid pos₁, (∀ z<heap,mid z=mem z) → ZeroFrom mid b →
        RoundFlowAt I mid heap h L P f →
        ∃ out final c,
          Runs w p ω (roundMachineBody init loop)
            (startState [I.n,I.m,graph,cost,heap,L,P,one,b] mid pos₁) (.returned out) final c ∧
          RoundFlowAt I final.mem heap h L P (roundFlow D I f).flowArr ∧ b≤out ∧
          out≤b+roundMachineSpace (allocation 6 [I.n,L,P,b]) A L I.m ∧ ZeroFrom final.mem out ∧
          (∀ z<heap,final.mem z=mid z) ∧ c≤roundMachineCost (rate I.n) L I.n I.m) :
    let b := heap+I.m*L
    ∃ out final c,
      Runs w p ω (roundExtractBody copy roundEntry extract)
        (startState [I.n,I.m,graph,cost,source,L,P,one,heap,dest,J.m] mem pos)
        (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤b+roundMachineSpace (allocation 6 [I.n,L,P,b]) A L I.m+recoverScanSpace L J.m ∧
      ZeroFrom final.mem out ∧ (∀ z<dest,final.mem z=mem z) ∧
      c≤roundMachineCost (rate I.n) L I.n I.m+17*(I.m*L)+J.m*(100*L+240)+100 := by
  dsimp only at hWords hSpace hRunner ⊢
  let b := heap+I.m*L
  let args := [I.n,I.m,graph,cost,source,L,P,one,heap,dest,J.m]
  let parent := startState args mem pos
  let R := roundMachineSpace (allocation 6 [I.n,L,P,b]) A L I.m
  have hB : b<2^w := by change b+R+recoverScanSpace L J.m<2^w at hSpace; omega
  have hW (i : Fin 11) : args[i.val]'i.isLt<2^w := hWords _ (List.getElem_mem (l:=args) i.isLt)
  have hw₁ : ∀ z∈[source,I.m,L,heap],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hW 4
    · exact hW 1
    · exact hW 5
    · exact hW 8
  have hArg₁ : evalArgs w parent [.reg 4,.reg 1,.reg 5,.reg 8]=some [source,I.m,L,heap] := rfl
  have hPre₁ : (epochFlowCopyContract w).pre [source,I.m,L,heap] mem :=
    ⟨⟨source,I.m,L,heap,rfl,hEnd,by omega⟩,hZero,hB⟩
  obtain ⟨s₁,c₁,b₁,hCall₁,hOut₁,hHeap₁,hReg₁,hC₁⟩ :=
    runs_call_of_meetsContract (r:=11) hCopy hArg₁ hw₁ hPre₁ ω
  have hb₁ : b₁=b := hOut₁.2
  have hFlow₁ := roundFlowAt_of_copy I hFlow hOut₁
  have hFrame₁ : ∀ z<heap,s₁.mem z=mem z := hOut₁.1.2.2.1
  have hZero₁ : ZeroFrom s₁.mem b₁ := hOut₁.1.2.2.2.1
  have hZb : ZeroFrom s₁.mem b := by rwa [← hb₁]
  obtain ⟨midHeap,raw₂,c₂,hRun₂,hRound₂,hLo₂,hHi₂,hZero₂,hFrame₂,hC₂⟩ :=
    hRunner s₁.mem s₁.pos hFrame₁ hZb hFlow₁
  have hr₁ (i : ℕ) (hi : i<11) : s₁.regs i=parent.regs i := hReg₁ i (by omega)
  have hArg₂ : evalArgs w s₁ [.reg 0,.reg 1,.reg 2,.reg 3,.reg 8,.reg 5,.reg 6,.reg 7,.reg 11]=
      some [I.n,I.m,graph,cost,heap,L,P,one,b] := by
    have r₀ : s₁.regs 0=I.n := hr₁ 0 (by decide)
    have r₁ : s₁.regs 1=I.m := hr₁ 1 (by decide)
    have r₂ : s₁.regs 2=graph := hr₁ 2 (by decide)
    have r₃ : s₁.regs 3=cost := hr₁ 3 (by decide)
    have r₅ : s₁.regs 5=L := hr₁ 5 (by decide)
    have r₆ : s₁.regs 6=P := hr₁ 6 (by decide)
    have r₇ : s₁.regs 7=one := hr₁ 7 (by decide)
    have r₈ : s₁.regs 8=heap := hr₁ 8 (by decide)
    simp [evalArgs,Expr.eval,r₀,r₁,r₂,r₃,r₅,r₆,r₇,r₈,hHeap₁,hb₁]
  have hCall₂ := round_returning_call (dst:=12) hRound hArg₂ hRun₂
  let mid : State := ⟨raw₂.mem,Function.update s₁.regs 12 midHeap,raw₂.pos⟩
  have hLen : heap+J.m*L≤midHeap := by
    have hh := Nat.mul_le_mul_right L hm
    exact (Nat.add_le_add_left hh heap).trans hLo₂
  have hRoom : midHeap+recoverScanSpace L J.m<2^w := by
    change b+R+recoverScanSpace L J.m<2^w at hSpace
    change midHeap≤b+R at hHi₂
    omega
  have hPre₃ : (recoverScanContract w h).pre [heap,L,P,dest,J.m,midHeap] mid.mem := by
    refine ⟨heap,L,P,dest,J.m,midHeap,rfl,hDest,hLen,hTwo,hZero₂,hRoom,?_⟩
    intro e he
    let j : Fin J.m := ⟨e,he⟩
    have hAt := hRound₂ ⟨j.val,j.isLt.trans_le hm⟩
    rw [hq j] at hAt
    exact ⟨q j,hQW j,hAt⟩
  have hArg₃ : evalArgs w mid [.reg 8,.reg 5,.reg 6,.reg 9,.reg 10,.reg 12]=some [heap,L,P,dest,J.m,midHeap] := by
    have r₅ : s₁.regs 5=L := hr₁ 5 (by decide)
    have r₆ : s₁.regs 6=P := hr₁ 6 (by decide)
    have r₈ : s₁.regs 8=heap := hr₁ 8 (by decide)
    have r₉ : s₁.regs 9=dest := hr₁ 9 (by decide)
    have r₁₀ : s₁.regs 10=J.m := hr₁ 10 (by decide)
    simp [evalArgs,Expr.eval,mid,r₅,r₆,r₈,r₉,r₁₀]
  have hW₃ : ∀ z∈[heap,L,P,dest,J.m,midHeap],z<2^w := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hW 8
    · exact hW 5
    · exact hW 6
    · exact hW 9
    · exact hW 10
    · omega
  obtain ⟨final,c₃,out,hCall₃,hOut₃,hRet₃,hRegs₃,hC₃⟩ :=
    runs_call_of_meetsContract (r:=13) hExtract hArg₃ hW₃ hPre₃ ω
  obtain ⟨hEnd₃,hZero₃,hFr₃,hVals⟩ := hOut₃
  change out=midHeap+recoverScanSpace L J.m at hEnd₃
  change ∀ z<midHeap,z<dest ∨ dest+J.m≤z → final.mem z=mid.mem z at hFr₃
  have hEq : (fun e => (J.readSolverFlow final.mem dest e:ℝ))=(fun e => (q e:ℝ)) := by
    funext e
    have ha := hVals e.val e.isLt
    have hb := hRound₂ ⟨e.val,e.isLt.trans_le hm⟩
    rw [hq e] at hb
    have he : (final.mem (dest+e.val):ℚ)=(q e:ℚ) := ha.2.symm.trans hb.2
    have hf : final.mem (dest+e.val)=q e := by exact_mod_cast he
    change (final.mem (dest+e.val):ℤ)=(q e:ℝ)
    rw [hf]
    simp
  have hRet : Runs w p ω (.ret (.reg 13)) final (.returned out) final 2 :=
    runs_ret_iff.mpr ⟨out,congrArg some hRet₃,rfl,rfl,rfl⟩
  let c := c₁+(9+c₂+1+(c₃+2+1)+1)+1
  refine ⟨out,final,c,?_,hEq.symm ▸ hOpt,?_,?_,hZero₃,?_,?_⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s₁,_,_,hCall₁,runs_seq_iff.mpr (Or.inr
      ⟨mid,_,_,hCall₂,runs_seq_iff.mpr (Or.inr ⟨final,_,_,hCall₃,hRet,rfl⟩),rfl⟩),rfl⟩)
  · have hb' : heap≤b := by dsimp [b]; omega
    exact hb'.trans (hLo₂.trans (by omega))
  · change midHeap≤b+R at hHi₂
    change out≤b+R+recoverScanSpace L J.m
    omega
  · intro z hz
    exact (hFr₃ z (by have hh : heap≤midHeap := (Nat.le_add_right _ _).trans hLo₂; omega) (Or.inl hz)).trans
      ((hFrame₂ z (by omega)).trans (hFrame₁ z (by omega)))
  · change c₁≤4+(17*(I.m*L)+40)+1 at hC₁
    change c₃≤6+(J.m*(100*L+240)+8)+1 at hC₃
    change c₂≤roundMachineCost (rate I.n) L I.n I.m at hC₂
    dsimp only [c]
    omega


/-- Compose the actual rounder with the output scan on the original
Lemma 4.12 augmentation. -/
theorem roundExtract_runs {w h L P copy roundEntry extract init loop A : ℕ}
    (D : DynForest) (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {p : Program} (hCopy : MeetsContract w p copy (epochFlowCopyContract w))
    (hRound : p.procs[roundEntry]?=some (roundMachineBody init loop))
    (hExtract : MeetsContract w p extract (recoverScanContract w h))
    (J : Circulation) (K : ℤ) (hp : ∀ e,1≤J.capacity e)
    (f : Fin (initialInstance J.toInstance K).m → ℚ)
    (q : Fin J.m → ℕ) (hq : ∀ e,(roundFlow D (initialInstance J.toInstance K) f).flowArr
      (augmentedOriginalIndex J K hp e)=(q e:ℚ))
    (hOpt : J.Optimal (fun e => (q e:ℝ))) (hQW : ∀ e,q e<2^w)
    (graph cost source one heap dest : ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (hWords : let I := initialInstance J.toInstance K
      ∀ z∈[I.n,I.m,graph,cost,source,L,P,one,heap,dest,J.m],z<2^w)
    (hTwo : 2<2^w) (hZero : ZeroFrom mem heap)
    (hEnd : source+(initialInstance J.toInstance K).m*L≤heap) (hDest : dest+J.m≤heap)
    (hFlow : RoundFlowAt (initialInstance J.toInstance K) mem source h L P f)
    (hSpace : let I := initialInstance J.toInstance K
      let b := heap+I.m*L
      let r := roundMachineSpace (allocation 6 [I.n,L,P,b]) A L I.m
      b+r+recoverScanSpace L J.m<2^w)
    (hRunner : let I := initialInstance J.toInstance K
      let b := heap+I.m*L
      ∀ mid pos₁, (∀ z<heap,mid z=mem z) → ZeroFrom mid b →
        RoundFlowAt I mid heap h L P f →
        ∃ out final c,
          Runs w p ω (roundMachineBody init loop)
            (startState [I.n,I.m,graph,cost,heap,L,P,one,b] mid pos₁) (.returned out) final c ∧
          RoundFlowAt I final.mem heap h L P (roundFlow D I f).flowArr ∧ b≤out ∧
          out≤b+roundMachineSpace (allocation 6 [I.n,L,P,b]) A L I.m ∧ ZeroFrom final.mem out ∧
          (∀ z<heap,final.mem z=mid z) ∧ c≤roundMachineCost (rate I.n) L I.n I.m) :
    let I := initialInstance J.toInstance K
    let b := heap+I.m*L
    ∃ out final c,
      Runs w p ω (roundExtractBody copy roundEntry extract)
        (startState [I.n,I.m,graph,cost,source,L,P,one,heap,dest,J.m] mem pos)
        (.returned out) final c ∧
      J.Optimal (fun e => (J.readSolverFlow final.mem dest e:ℝ)) ∧
      heap≤out ∧ out≤b+roundMachineSpace (allocation 6 [I.n,L,P,b]) A L I.m+recoverScanSpace L J.m ∧
      ZeroFrom final.mem out ∧ (∀ z<dest,final.mem z=mem z) ∧
      c≤roundMachineCost (rate I.n) L I.n I.m+17*(I.m*L)+J.m*(100*L+240)+100 :=
  roundExtract_prefix_runs D rate allocation hCopy hRound hExtract J _
    (circulation_augmented_m_ge J K hp) f q hq hOpt hQW graph cost source one heap dest
    mem pos ω hWords hTwo hZero hEnd hDest hFlow hSpace hRunner

end MinCostFlow.IPM.Machine
