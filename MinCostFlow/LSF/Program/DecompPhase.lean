module

public import MinCostFlow.LSF.Program.CallSeq
public import MinCostFlow.LSF.Program.DecompWTProc
public import MinCostFlow.LSF.Program.WstrWidth
public import MinCostFlow.LSF.Program.WstrStage
public import MinCostFlow.LSF.Program.FlagMerge
public import MinCostFlow.LSF.Program.RootsStage
public import MinCostFlow.LSF.Program.DecompPhaseMath
public import MinCostFlow.LSF.Program.WstrCopy

/-!
# The decomposition phase of the initialization

After the order phase, the tree `T₀` is rooted, `π` is in the `T` block, and the parents and
depths of `T_H` are in memory. The decomposition phase runs six calls followed by two active-edge
copy loops:
1. `decompWTProc`: the decomposition `W_T` (Lemma B.7) in a zero scratch area of `12 n` words;
   array `11` holds the flags of its boundary;
2. `wstrLBProc`: the block width `LB` of the stretch pass, returned in a register;
3. `wstrStageProc`: the stretch bounds `wstr` in scratch arrays, and the flags of the edges
   whose bound reaches the threshold; it returns the place of these flags;
4. `memCopyStmt`: copy these flags to a fixed place, below the outputs of the next two calls;
5. `flagMergeProc`: the flags of the first root set (representatives, boundary, ends of the
   flagged edges);
6. `rootsStageProc`: the closure of the root set in `T_H` and the forest `F` arrays
   (`mp`, `own`, `rt`);
7. and 8. `wstrCopyEdgesStmt`: copy only the `m₀` active edge entries of the two stretch arrays
   to their static place (`O(m₀ · L_w)`).

The stretch pass needs every array it reads below its numerator array (`WstrPre`). The endpoint
arrays and the depths of `T_H` lie in scratch above the static blocks, so the stretch arrays are
first built in scratch and then their active edges are copied (`WstrAt.of_copy_edges`).

`DecompLayout` names the places and `DecompLayout.args` lists the `40` arguments of the phase.
The results of calls `2` and `3` land in registers `41` and `42`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Call sequences with a custom tail statement -/

/-- Run a sequence of calls and then execute `tail`. Call `j` writes register `R + i + j`. -/
def callSeqThen (R : ℕ) (tail : Stmt) : ℕ → List CallItem → Stmt
  | _, [] => tail
  | i, it :: rest => .call (R + i) it.f (it.rs.map Expr.reg) ;; callSeqThen R tail (i + 1) rest

lemma callSeqThen_noRand (R : ℕ) {tail : Stmt} (ht : tail.NoRand) :
    ∀ (i : ℕ) (items : List CallItem), (callSeqThen R tail i items).NoRand
  | _, [] => ht
  | i, _ :: rest => ⟨trivial, callSeqThen_noRand R ht (i + 1) rest⟩

/-- Precondition of `callSeqThen`, ending with a continuation predicate `cont` on the registers,
memory, and remaining budget after the calls. -/
def SeqPreCont (w R : ℕ) (cont : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop) :
    ℕ → List CallItem → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop
  | _, [], regs, mem, B => cont regs mem B
  | i, it :: rest, regs, mem, B =>
    (∀ x ∈ it.rs.map regs, x < 2 ^ w) ∧ it.C.pre (it.rs.map regs) mem ∧
    it.C.cost (it.rs.map regs) mem + it.rs.length + 2 ≤ B ∧
    ∀ v mem', it.C.post (it.rs.map regs) mem v mem' →
      SeqPreCont w R cont (i + 1) rest (Function.update regs (R + i) v) mem'
        (B - (it.C.cost (it.rs.map regs) mem + it.rs.length + 2))

/-- Postcondition of `callSeqThen`, ending with a continuation predicate `cont` on the registers
after the calls, the memory after the calls, the return value, and the final memory. -/
def SeqPostCont (R : ℕ) (cont : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop) :
    ℕ → List CallItem → (ℕ → ℕ) → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop
  | _, [], regs, mem, ret, mem' => cont regs mem ret mem'
  | i, it :: rest, regs, mem, ret, mem' => ∃ v mem₁, it.C.post (it.rs.map regs) mem v mem₁ ∧
    SeqPostCont R cont (i + 1) rest (Function.update regs (R + i) v) mem₁ ret mem'

lemma SeqPreCont.mono {w R : ℕ} {cont : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hmono : ∀ regs mem B B', cont regs mem B → B ≤ B' → cont regs mem B') :
    ∀ {items : List CallItem} {i : ℕ} {regs mem : ℕ → ℕ} {B B' : ℕ},
      SeqPreCont w R cont i items regs mem B → B ≤ B' → SeqPreCont w R cont i items regs mem B'
  | [], _, _, _, _, _, h, hB => hmono _ _ _ _ h hB
  | _ :: _, _, _, _, _, _, ⟨hw, hC, hc, hn⟩, hB =>
    ⟨hw, hC, by omega, fun v mem' hp => SeqPreCont.mono hmono (hn v mem' hp) (by omega)⟩

lemma SeqPreCont.cons {w R i : ℕ} {cont : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    (hmono : ∀ regs mem B B', cont regs mem B → B ≤ B' → cont regs mem B')
    {it : CallItem} {rest : List CallItem} {regs mem : ℕ → ℕ} {B : ℕ}
    (args : List ℕ) (c : ℕ) (hargs : it.rs.map regs = args) (hw : ∀ x ∈ it.rs.map regs, x < 2 ^ w)
    (hpre : it.C.pre args mem) (hc : it.C.cost args mem + it.rs.length + 2 ≤ c) (hcB : c ≤ B)
    (hnext : ∀ v mem', it.C.post args mem v mem' →
      SeqPreCont w R cont (i + 1) rest (Function.update regs (R + i) v) mem' (B - c)) :
    SeqPreCont w R cont i (it :: rest) regs mem B := by
  subst hargs
  exact ⟨hw, hpre, by omega, fun v mem' hp => SeqPreCont.mono hmono (hnext v mem' hp) (by omega)⟩

theorem runs_callSeqThen {w R : ℕ} {p : Program} {ω : ℕ → Bool} {tail : Stmt}
    {contPre : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → Prop}
    {contPost : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop}
    (htail : ∀ st B, contPre st.regs st.mem B →
      ∃ o st' c, Runs w p ω tail st o st' c ∧ contPost st.regs st.mem o.value st'.mem ∧ c ≤ B) :
    ∀ (items : List CallItem) (i : ℕ) (st : State) (B k : ℕ), AllMeet w p items →
      SeqPreCont w R contPre i items st.regs st.mem B →
      ∃ o st' c, Runs w p ω (callSeqThen R tail i items) st o st' c ∧
        SeqPostCont R contPost i items st.regs st.mem o.value st'.mem ∧ k + c ≤ k + B := by
  intro items
  induction items with
  | nil =>
    intro i st B k _ hB
    obtain ⟨o, st', c, hr, hpost, hc⟩ := htail st B hB
    exact ⟨o, st', c, hr, hpost, by omega⟩
  | cons it rest ih =>
    intro i st B k hall hpre
    obtain ⟨hw, hC, hcost, hnext⟩ := hpre
    have hf : MeetsContract w p it.f it.C := hall it (List.mem_cons_self ..)
    have hrest : AllMeet w p rest := fun it' h' => hall it' (List.mem_cons_of_mem _ h')
    refine runs_seq_call_le (vs := it.rs.map st.regs) hf (evalArgs_map_reg_seq _) hw hC ?_
    intro v mem' pos' hpost
    obtain ⟨o, st', c, hr, hseq, hc⟩ := ih (i + 1)
      { mem := mem', regs := Function.update st.regs (R + i) v, pos := pos' }
      (B - (it.C.cost (it.rs.map st.regs) st.mem + it.rs.length + 2))
      (k + argsSize (it.rs.map Expr.reg) + it.C.cost (it.rs.map st.regs) st.mem + 2) hrest
      (hnext v mem' hpost)
    refine ⟨o, st', c, hr, ⟨v, mem', hpost, hseq⟩, ?_⟩
    rw [argsSize_map_reg_seq] at hc ⊢
    omega

/-! ## Layout, tail copy loops, and contract of the decomposition phase -/

/-- The places and numbers of the decomposition phase. The root is index `0`. -/
structure DecompLayout where
  n : ℕ
  m0 : ℕ
  eu : ℕ
  ev : ℕ
  qOrd : ℕ
  auxPar : ℕ
  θ : ℕ
  dBase : ℕ
  D : ℕ
  Lw : ℕ
  tM : ℕ
  k : ℕ
  Lin : ℕ
  nOrig : ℕ
  logCap : ℕ
  lenArr : ℕ
  tPtr : ℕ
  vCap : ℕ
  eCap : ℕ
  gPtr : ℕ
  thBase : ℕ
  thDst : ℕ
  numS : ℕ
  idPtr : ℕ
  hiCopy : ℕ
  cnt : ℕ
  repPtr : ℕ
  vIdx : ℕ
  inR : ℕ
  numSt : ℕ
  denSt : ℕ

namespace DecompLayout

variable (X : DecompLayout)

/-- The scratch denominator array of the stretch pass. -/
def denS : ℕ := X.numS + X.eCap * X.Lw

/-- The `40` arguments of the phase. -/
def args : List ℕ :=
  [X.n, X.m0, X.eu, X.ev, X.qOrd, X.auxPar, 0, X.θ, X.dBase,
    X.D, X.Lw, X.tM, X.k, X.Lin, X.nOrig, X.logCap, X.lenArr, tOrigIdBase X.tPtr X.vCap X.tM,
    X.auxPar + X.n, tPiBase X.tPtr X.vCap X.tM, X.thBase + 7 * X.n, X.auxPar + 3 * X.n,
    X.auxPar + X.n + X.n, dgEListBase X.gPtr X.vCap X.eCap, X.numS, X.denS, X.idPtr,
    X.hiCopy, X.cnt, X.dBase + 11 * X.n, X.repPtr, X.vIdx, X.inR,
    X.thDst, X.inR + X.n, X.inR + X.n + X.n, X.inR + X.n + X.n + X.tM,
    X.numSt, X.denSt, X.eCap * X.Lw]

end DecompLayout

/-- The six calls of the decomposition phase before the two active-edge stretch copy loops. -/
def decompPhaseItems (w h C : ℕ) (bWT bLB bW bCopy bFlag bRoots : ℕ) : List CallItem :=
  [⟨bWT, [0, 1, 2, 3, 4, 5, 6, 7, 8], decompWTContract w⟩,
   ⟨bLB, [0, 9, 10], wstrLBContract w⟩,
   ⟨bW, [0, 11, 1, 12, 41, 10, 13, 14, 6, 15, 16, 17, 4, 5, 18, 19, 20, 2, 3, 21, 22, 23, 24, 25,
      26], wstrStageContract w h C⟩,
   ⟨bCopy, [27, 42, 1], memCopyContract w⟩,
   ⟨bFlag, [0, 28, 1, 29, 30, 31, 27, 2, 3, 32], flagMergeContract w⟩,
   ⟨bRoots, [0, 11, 6, 4, 5, 18, 19, 33, 20, 9, 32, 34, 35, 36], rootsStageContract w⟩]

/-- Tail of `decompPhaseProc`: copy the `m₀` active edge entries of `numS` and `denS` to
`numSt` and `denSt`, then return register `6`. -/
def decompCopyTail (bCopy : ℕ) : Stmt :=
  wstrCopyEdgesStmt bCopy 37 24 23 1 10 ;;
  wstrCopyEdgesStmt bCopy 38 25 23 1 10 ;;
  .ret (.reg 6)

lemma decompCopyTail_noRand (bCopy : ℕ) : (decompCopyTail bCopy).NoRand := by
  simp [decompCopyTail, wstrCopyEdgesStmt_noRand, Stmt.NoRand]

/-- Precondition of `decompCopyTail` after the six calls. -/
def decompCopyPre (w : ℕ) (regs mem : ℕ → ℕ) (B : ℕ) : Prop :=
  wstrCopyEdgesPre w (regs 37) (regs 24) (regs 23) (regs 1) (regs 10) (regs 39) mem ∧
  wstrCopyEdgesPre w (regs 38) (regs 25) (regs 23) (regs 1) (regs 10) (regs 39) mem ∧
  regs 37 + regs 39 ≤ regs 38 ∧
  regs 38 + regs 39 ≤ regs 24 ∧
  regs 24 + regs 39 ≤ regs 25 ∧
  2 * wstrCopyEdgesCost (regs 1) (regs 10) + 4 ≤ B

lemma decompCopyPre_mono (w : ℕ) :
    ∀ regs mem B B', decompCopyPre w regs mem B → B ≤ B' → decompCopyPre w regs mem B' := by
  intro regs mem B B' ⟨h1, h2, h3, h4, h5, h6⟩ hle
  exact ⟨h1, h2, h3, h4, h5, le_trans h6 hle⟩

/-- Postcondition of `decompCopyTail`. -/
def decompCopyPost (regs m₆ : ℕ → ℕ) (ret : ℕ) (mem₈ : ℕ → ℕ) : Prop :=
  ∃ m₇,
    wstrCopyEdgesPost (regs 37) (regs 24) (regs 23) (regs 1) (regs 10) (regs 39) m₆ m₇ ∧
    wstrCopyEdgesPost (regs 38) (regs 25) (regs 23) (regs 1) (regs 10) (regs 39) m₇ mem₈ ∧
    ret = regs 6

lemma decompCopyTail_runs {w bCopy : ℕ} {p : Program} {ω : ℕ → Bool}
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (st : State) (B : ℕ) (hpre : decompCopyPre w st.regs st.mem B) :
    ∃ o st' c, Runs w p ω (decompCopyTail bCopy) st o st' c ∧
      decompCopyPost st.regs st.mem o.value st'.mem ∧ c ≤ B := by
  obtain ⟨hp1, hp2, h3738, h3824, h2425, hB⟩ := hpre
  obtain ⟨st₁, c₁, hr₁, hreg₁, hpost₁, hc₁⟩ :=
    wstrCopyEdges_runs hCopy (by decide) (by decide) (by decide) (by decide) (by decide)
      rfl rfl rfl rfl rfl hp1
  have hp2₁ : wstrCopyEdgesPre w (st.regs 38) (st.regs 25) (st.regs 23) (st.regs 1) (st.regs 10)
      (st.regs 39) st₁.mem := by
    obtain ⟨hw16, hLw1, hLwW, hEL, hDS, hSW, hEt⟩ := hp2
    refine ⟨hw16, hLw1, hLwW, hEL, hDS, hSW, fun t ht => ?_⟩
    have hEL1 := hp1.2.2.2.1
    rw [hpost₁.2 _ (Or.inl (by omega))]
    exact hEt t ht
  obtain ⟨st₂, c₂, hr₂, hreg₂, hpost₂, hc₂⟩ :=
    wstrCopyEdges_runs hCopy (by decide) (by decide) (by decide) (by decide) (by decide)
      (hreg₁ 38 (by decide)) (hreg₁ 25 (by decide)) (hreg₁ 23 (by decide))
      (hreg₁ 1 (by decide)) (hreg₁ 10 (by decide)) hp2₁
  have hret6 : st₂.regs 6 = st.regs 6 := (hreg₂ 6 (by decide)).trans (hreg₁ 6 (by decide))
  have hr_ret : Runs w p ω (.ret (.reg 6)) st₂ (.returned (st.regs 6)) st₂ 2 :=
    runs_ret_iff.mpr ⟨st.regs 6, by simp [Expr.eval, hret6], rfl, rfl, by simp [Expr.size]⟩
  have hr₂₃ : Runs w p ω (wstrCopyEdgesStmt bCopy 38 25 23 1 10 ;; .ret (.reg 6))
      st₁ (.returned (st.regs 6)) st₂ (c₂ + 2 + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st₂, c₂, 2, hr₂, hr_ret, rfl⟩)
  have hr₁₂₃ : Runs w p ω (decompCopyTail bCopy) st (.returned (st.regs 6)) st₂
      (c₁ + (c₂ + 2 + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂ + 2 + 1, hr₁, hr₂₃, rfl⟩)
  exact ⟨.returned (st.regs 6), st₂, c₁ + (c₂ + 2 + 1) + 1, hr₁₂₃,
    ⟨st₁.mem, hpost₁, hpost₂, rfl⟩, by omega⟩

/-- The contract of the decomposition phase, with cost bound `K`. -/
def decompPhaseContract (w h C : ℕ) (bWT bLB bW bCopy bFlag bRoots : ℕ)
    (K : List ℕ → (ℕ → ℕ) → ℕ) : Contract where
  pre args mem :=
    SeqPreCont w 40 (decompCopyPre w) 0 (decompPhaseItems w h C bWT bLB bW bCopy bFlag bRoots)
      (fun j => args.getD j 0) mem (K args mem)
  post args mem ret mem' :=
    SeqPostCont 40 decompCopyPost 0 (decompPhaseItems w h C bWT bLB bW bCopy bFlag bRoots)
      (fun j => args.getD j 0) mem ret mem'
  cost := K

/-- The body of the decomposition phase. -/
def decompPhaseProc (w h C : ℕ) (bWT bLB bW bCopy bFlag bRoots : ℕ) : Stmt :=
  callSeqThen 40 (decompCopyTail bCopy) 0 (decompPhaseItems w h C bWT bLB bW bCopy bFlag bRoots)

lemma decompPhaseProc_noRand (w h C bWT bLB bW bCopy bFlag bRoots : ℕ) :
    (decompPhaseProc w h C bWT bLB bW bCopy bFlag bRoots).NoRand :=
  callSeqThen_noRand 40 (decompCopyTail_noRand bCopy) 0 _

theorem decompPhase_meetsContract {w h C : ℕ} {p : Program} {b bWT bLB bW bCopy bFlag bRoots : ℕ}
    {K : List ℕ → (ℕ → ℕ) → ℕ}
    (hp : p.procs[b]? = some (decompPhaseProc w h C bWT bLB bW bCopy bFlag bRoots))
    (hWT : MeetsContract w p bWT (decompWTContract w))
    (hLB : MeetsContract w p bLB (wstrLBContract w))
    (hW : MeetsContract w p bW (wstrStageContract w h C))
    (hCopy : MeetsContract w p bCopy (memCopyContract w))
    (hFlag : MeetsContract w p bFlag (flagMergeContract w))
    (hRoots : MeetsContract w p bRoots (rootsStageContract w)) :
    MeetsContract w p b (decompPhaseContract w h C bWT bLB bW bCopy bFlag bRoots K) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  have hall : AllMeet w p (decompPhaseItems w h C bWT bLB bW bCopy bFlag bRoots) := by
    intro it hit
    simp only [decompPhaseItems, List.mem_cons, List.not_mem_nil, or_false] at hit
    rcases hit with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hWT, hLB, hW, hCopy, hFlag, hRoots]
  obtain ⟨o, st', c, hr, hseq, hc⟩ :=
    runs_callSeqThen (decompCopyTail_runs hCopy)
      (decompPhaseItems w h C bWT bLB bW bCopy bFlag bRoots) 0 (startState args mem pos)
      (K args mem) 0 hall hpre
  exact ⟨o, st', c, hr, hseq, by simpa [decompPhaseContract] using hc⟩

end

end MinCostFlow.LSF.Program
