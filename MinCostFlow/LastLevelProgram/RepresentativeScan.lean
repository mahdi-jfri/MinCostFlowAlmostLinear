module

public import MinCostFlow.LastLevelProgram.RepresentativeKeys
import Mathlib.Tactic
import WordRAM.Tactic

/-!
# Scanning sorted representative keys

The Definition 5.8 rebuild (pages 19–20) scans each parallel class and keeps its shortest edge.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num DynSpanner.Program SparseCore

/-- Compare the candidate's unsigned length with the incumbent's.
Registers 11 and 12 hold the names, 13 holds the length table base,
and 14 holds the caller's limb count. -/
def representativeLengthLess (entry : ℕ) : Stmt :=
  let addr := fun r => .bin .add (.reg 13) (.bin .mul (.reg r) (.reg 14))
  .call 15 entry [addr 11,addr 12,.reg 14]

/-- A strict comparison leaves the first edge in place on a tie.
The length table and the other scan registers are preserved. -/
theorem representativeLengthLess_runs {w entry : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (candidate incumbent lengths L : ℕ)
    (hc : MeetsContract w p entry (unsignedLessContract w 4))
    (h11 : st.regs 11 = candidate) (h12 : st.regs 12 = incumbent)
    (h13 : st.regs 13 = lengths) (h14 : st.regs 14 = L)
    (ha : lengths+candidate*L+L < 2^w) (hb : lengths+incumbent*L+L < 2^w)
    (hva : Valid st.mem (lengths+candidate*L) 4 L)
    (hvb : Valid st.mem (lengths+incumbent*L) 4 L) :
    ∃ out cost, Runs w p ω (representativeLengthLess entry) st .normal out cost ∧
      out.mem = st.mem ∧
      out.regs 15 = (if unsignedVal st.mem (lengths+candidate*L) 4 L <
        unsignedVal st.mem (lengths+incumbent*L) 4 L then 1 else 0) ∧
      (∀ r, r ≠ 15 → out.regs r = st.regs r) ∧ cost ≤ 41*L+18 := by
  let a := lengths+candidate*L
  let b := lengths+incumbent*L
  have hra : candidate*L < 2^w := by omega
  have hrb : incumbent*L < 2^w := by omega
  have haa : lengths+candidate*L < 2^w := by omega
  have hbb : lengths+incumbent*L < 2^w := by omega
  have hargs : evalArgs w st [(.bin .add (.reg 13) (.bin .mul (.reg 11) (.reg 14))),
      (.bin .add (.reg 13) (.bin .mul (.reg 12) (.reg 14))),.reg 14] = some [a,b,L] := by
    simp [evalArgs,Expr.eval,BinOp.eval,h11,h12,h13,h14,hra,hrb,haa,hbb,a,b]
  have hwords : ∀ x ∈ [a,b,L], x < 2^w := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact haa
    · exact hbb
    · omega
  obtain ⟨out,c,ret,hr,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 15) hc hargs hwords
      ⟨a,b,L,rfl,ha,hb,hva,hvb⟩ ω
  obtain ⟨hm,hval⟩ := hpost
  change c ≤ 11 + (41*L+6) + 1 at hcost
  exact ⟨out,c,hr,hm,hret.trans hval,hregs,by omega⟩

/-- Keep the shorter edge in the current class. Keys are visited in
increasing edge-name order within each class. -/
def representativeChoose (entry : ℕ) : Stmt :=
  .seq (representativeLengthLess entry) (.cond (.reg 15) (.assign 12 (.reg 11)) .nop)

/-- The incumbent changes exactly when the candidate has a shorter length. -/
theorem representativeChoose_runs {w entry : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (candidate incumbent lengths L : ℕ)
    (hc : MeetsContract w p entry (unsignedLessContract w 4))
    (h11 : st.regs 11 = candidate) (h12 : st.regs 12 = incumbent)
    (h13 : st.regs 13 = lengths) (h14 : st.regs 14 = L)
    (ha : lengths+candidate*L+L < 2^w) (hb : lengths+incumbent*L+L < 2^w)
    (hva : Valid st.mem (lengths+candidate*L) 4 L)
    (hvb : Valid st.mem (lengths+incumbent*L) 4 L) :
    ∃ out cost, Runs w p ω (representativeChoose entry) st .normal out cost ∧
      out.mem = st.mem ∧
      out.regs 12 = (if unsignedVal st.mem (lengths+candidate*L) 4 L <
        unsignedVal st.mem (lengths+incumbent*L) 4 L then candidate else incumbent) ∧
      (∀ r, r ≠ 12 → r ≠ 15 → out.regs r = st.regs r) ∧ cost ≤ 41*L+23 := by
  obtain ⟨mid,c,hr,hm,htest,hregs,hcost⟩ :=
    representativeLengthLess_runs st candidate incumbent lengths L hc h11 h12 h13 h14 ha hb hva hvb
  have hread : (.reg 11 : Expr).eval w mid = some candidate := by
    simp [Expr.eval,(hregs 11 (by decide)).trans h11]
  by_cases h : unsignedVal st.mem (lengths+candidate*L) 4 L <
      unsignedVal st.mem (lengths+incumbent*L) 4 L
  · let out := {mid with regs := Function.update mid.regs 12 candidate}
    have hs : Runs w p ω (.assign 12 (.reg 11)) mid .normal out 2 :=
      runs_assign_iff.mpr ⟨candidate,hread,rfl,rfl,rfl⟩
    have ht : Runs w p ω (.cond (.reg 15) (.assign 12 (.reg 11)) .nop) mid .normal out 4 :=
      runs_cond_iff.mpr ⟨1,2,by simp [Expr.eval,htest,h],by simpa using hs,rfl⟩
    refine ⟨out,c+5,runs_seq_iff.mpr (Or.inr ⟨mid,c,4,hr,ht,rfl⟩),hm,
      by simp [out,h],fun r h12' h15' => ?_,by omega⟩
    exact (Function.update_of_ne h12' ..).trans (hregs r h15')
  · have ht : Runs w p ω (.cond (.reg 15) (.assign 12 (.reg 11)) .nop) mid .normal mid 3 :=
      runs_cond_iff.mpr ⟨0,1,by simp [Expr.eval,htest,h],by simp [runs_nop_iff],rfl⟩
    refine ⟨mid,c+4,runs_seq_iff.mpr (Or.inr ⟨mid,c,3,hr,ht,rfl⟩),hm,?_,
      fun r _ h15' => hregs r h15',by omega⟩
    simpa only [ite_eq_right h] using (hregs 12 (by decide)).trans h12

/-- Append the winner of a non-loop class. Register 16 is the
destination base and register 17 is the number of winners written. -/
def representativeAppend : Stmt :=
  .seq (.store (.bin .add (.reg 16) (.reg 17)) (.reg 12))
    (.assign 17 (.bin .add (.reg 17) (.const 1)))

/-- Appending writes exactly one cell and advances the output count. -/
theorem representativeAppend_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (dst count winner : ℕ)
    (h12 : st.regs 12 = winner) (h16 : st.regs 16 = dst) (h17 : st.regs 17 = count)
    (hd : dst+count < 2^w) (hc : count+1 < 2^w) :
    ∃ out, Runs w p ω representativeAppend st .normal out 10 ∧
      out.mem = Function.update st.mem (dst+count) winner ∧
      out.regs 17 = count+1 ∧ ∀ r, r ≠ 17 → out.regs r = st.regs r := by
  let mid := {st with mem := Function.update st.mem (dst+count) winner}
  let out := {mid with regs := Function.update mid.regs 17 (count+1)}
  have hstore : Runs w p ω (.store (.bin .add (.reg 16) (.reg 17)) (.reg 12))
      st .normal mid 5 :=
    runs_store_iff.mpr ⟨dst+count,winner,by simp [Expr.eval,BinOp.eval,h16,h17,hd],
      congrArg some h12,rfl,rfl,rfl⟩
  have hone : 1 < 2^w := by omega
  have hinc : Runs w p ω (.assign 17 (.bin .add (.reg 17) (.const 1)))
      mid .normal out 4 :=
    runs_assign_iff.mpr ⟨count+1,by simp [mid,Expr.eval,BinOp.eval,h17,hc,hone],
      rfl,rfl,rfl⟩
  exact ⟨out,runs_seq_iff.mpr (Or.inr ⟨mid,5,4,hstore,hinc,rfl⟩),rfl,
    by simp [out],fun r hr => Function.update_of_ne hr ..⟩

/-- Finish the current class. Register 18 holds any key from that class.
Equal endpoints identify a self-loop, which produces no output. -/
def representativeFlush : Stmt :=
  let ends := representativeClassEnds (.reg 18)
  .cond (.bin .eq ends.1 ends.2) .nop representativeAppend

/-- Finishing a class appends its winner exactly when its endpoints differ. -/
theorem representativeFlush_runs {w vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (e dst count winner : ℕ)
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap)
    (h12 : st.regs 12 = winner) (h16 : st.regs 16 = dst) (h17 : st.regs 17 = count)
    (h18 : st.regs 18 = representativeSortKey G vCap eCap e)
    (he : e < eCap) (hv : (edgePairKey G e).2 < vCap)
    (hk : representativeSortKey G vCap eCap e < 2^w)
    (hd : dst+count < 2^w) (hc : count+1 < 2^w) :
    let isLoop := (edgePairKey G e).1 = (edgePairKey G e).2
    ∃ out cost, Runs w p ω representativeFlush st .normal out cost ∧
      out.mem = (if isLoop then st.mem else Function.update st.mem (dst+count) winner) ∧
      out.regs 17 = (if isLoop then count else count+1) ∧
      (∀ r, r ≠ 17 → out.regs r = st.regs r) ∧ cost ≤ 23 := by
  let ends := representativeClassEnds (.reg 18)
  have hread : (.reg 18 : Expr).eval w st = some (representativeSortKey G vCap eCap e) :=
    congrArg some h18
  obtain ⟨_,_,hlo,hhi⟩ := representativeKey_eval G e h4 h5 hread he hv hk
  have hw : 1 < 2^w := by omega
  have hz : 0 < 2^w := by omega
  by_cases h : (edgePairKey G e).1 = (edgePairKey G e).2
  · have ht : (.bin .eq ends.1 ends.2 : Expr).eval w st = some 1 := by
      simp [ends,Expr.eval,BinOp.eval,hlo,hhi,h,hw]
    have hr : Runs w p ω representativeFlush st .normal st 13 :=
      runs_cond_iff.mpr ⟨1,1,ht,by simp [runs_nop_iff],rfl⟩
    exact ⟨st,13,hr,by simp [h],by simpa [h] using h17,fun _ _ => rfl,by decide⟩
  · have ht : (.bin .eq ends.1 ends.2 : Expr).eval w st = some 0 := by
      simp [ends,Expr.eval,BinOp.eval,hlo,hhi,h,hz]
    obtain ⟨out,hr,hm,hn,hregs⟩ := representativeAppend_runs st dst count winner h12 h16 h17 hd hc
    have hf : Runs w p ω representativeFlush st .normal out 22 :=
      runs_cond_iff.mpr ⟨0,10,ht,by simpa using hr,rfl⟩
    exact ⟨out,22,hf,by simpa [h] using hm,by simpa [h] using hn,hregs,by decide⟩

/-- Start a class with the current candidate and its key in register 19. -/
def representativeBeginClass : Stmt :=
  .seq (.assign 18 (.reg 19)) (.assign 12 (.reg 11))

/-- Starting a class sets the class key and incumbent without touching memory. -/
theorem representativeBeginClass_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (key candidate : ℕ) (h19 : st.regs 19 = key) (h11 : st.regs 11 = candidate) :
    ∃ out, Runs w p ω representativeBeginClass st .normal out 5 ∧ out.mem = st.mem ∧
      out.regs 18 = key ∧ out.regs 12 = candidate ∧
      ∀ r, r ≠ 18 → r ≠ 12 → out.regs r = st.regs r := by
  let mid := {st with regs := Function.update st.regs 18 key}
  let out := {mid with regs := Function.update mid.regs 12 candidate}
  have hfirst : Runs w p ω (.assign 18 (.reg 19)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨key,congrArg some h19,rfl,rfl,rfl⟩
  have hnext : Runs w p ω (.assign 12 (.reg 11)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨candidate,by simp [Expr.eval,mid,h11,Function.update_of_ne],rfl,rfl,rfl⟩
  refine ⟨out,runs_seq_iff.mpr (Or.inr ⟨mid,2,2,hfirst,hnext,rfl⟩),rfl,?_,?_,?_⟩
  · simp [out,mid,Function.update_of_ne]
  · simp [out]
  · intro r h18 h12
    simp [out,mid,Function.update_of_ne,h18,h12]

/-- Load the sorted key at the current index and decode its edge name. -/
def representativeReadCandidate : Stmt :=
  .seq (.assign 19 (.load (.bin .add (.reg 6) (.reg 8))))
    (.assign 11 (representativeNameExpr (.reg 19)))

/-- Reading a candidate leaves the sorted array and the class state intact. -/
theorem representativeReadCandidate_runs {w vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (src i e : ℕ)
    (h5 : st.regs 5 = eCap) (h6 : st.regs 6 = src) (h8 : st.regs 8 = i)
    (hm : st.mem (src+i) = representativeSortKey G vCap eCap e)
    (hs : src+i < 2^w) (he : e < eCap)
    (hv : (edgePairKey G e).2 < vCap)
    (hk : representativeSortKey G vCap eCap e < 2^w) :
    ∃ out, Runs w p ω representativeReadCandidate st .normal out 10 ∧
      out.mem = st.mem ∧ out.regs 19 = representativeSortKey G vCap eCap e ∧
      out.regs 11 = e ∧ ∀ r, r ≠ 19 → r ≠ 11 → out.regs r = st.regs r := by
  let key := representativeSortKey G vCap eCap e
  let mid := {st with regs := Function.update st.regs 19 key}
  let out := {mid with regs := Function.update mid.regs 11 e}
  have hload : Runs w p ω (.assign 19 (.load (.bin .add (.reg 6) (.reg 8))))
      st .normal mid 5 :=
    runs_assign_iff.mpr ⟨key,by simp [Expr.eval,BinOp.eval,h6,h8,hs,hm,key],rfl,rfl,rfl⟩
  have hname := (representativeSortKey_decode G vCap eCap e he hv).1
  have hb : key % eCap < 2^w := (Nat.mod_le _ _).trans_lt hk
  have hdecode : Runs w p ω (.assign 11 (representativeNameExpr (.reg 19))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨e,by
      simp only [representativeNameExpr,Expr.eval,mid,Function.update_self,
        Function.update_of_ne (show (5 : ℕ) ≠ 19 by decide),h5,BinOp.eval,hb,ite_true]
      exact congrArg some hname,rfl,rfl,rfl⟩
  refine ⟨out,runs_seq_iff.mpr (Or.inr ⟨mid,5,4,hload,hdecode,rfl⟩),rfl,?_,?_,?_⟩
  · simp [out,mid,key,Function.update_of_ne]
  · simp [out]
  · intro r h19 h11
    simp [out,mid,Function.update_of_ne,h19,h11]

/-- Update the current class or emit its winner and start the next class. -/
def representativeClassStep (entry : ℕ) : Stmt :=
  .cond (representativeSameClass (.reg 18) (.reg 19)) (representativeChoose entry)
    (.seq representativeFlush representativeBeginClass)

/-- A class boundary emits the previous winner and installs the new candidate. -/
theorem representativeClassBoundary_runs {w entry vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph)
    (e f dst count winner : ℕ)
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap)
    (h11 : st.regs 11 = f) (h12 : st.regs 12 = winner)
    (h16 : st.regs 16 = dst) (h17 : st.regs 17 = count)
    (h18 : st.regs 18 = representativeSortKey G vCap eCap e)
    (h19 : st.regs 19 = representativeSortKey G vCap eCap f)
    (he : e < eCap) (hf : f < eCap)
    (hev : (edgePairKey G e).2 < vCap) (hfv : (edgePairKey G f).2 < vCap)
    (heb : representativeSortKey G vCap eCap e < 2^w)
    (hfb : representativeSortKey G vCap eCap f < 2^w)
    (hne : edgePairKey G e ≠ edgePairKey G f)
    (hd : dst+count < 2^w) (hc : count+1 < 2^w) :
    let isLoop := (edgePairKey G e).1 = (edgePairKey G e).2
    ∃ out cost, Runs w p ω (representativeClassStep entry) st .normal out cost ∧
      out.mem = (if isLoop then st.mem else Function.update st.mem (dst+count) winner) ∧
      out.regs 17 = (if isLoop then count else count+1) ∧
      out.regs 18 = representativeSortKey G vCap eCap f ∧ out.regs 12 = f ∧
      (∀ r, r ≠ 12 → r ≠ 17 → r ≠ 18 → out.regs r = st.regs r) ∧ cost ≤ 37 := by
  have hw : 1 < 2^w := by omega
  have ht : (representativeSameClass (.reg 18) (.reg 19)).eval w st = some 0 := by
    simpa only [ite_eq_right hne] using
      representativeSameClass_eval G h4 h5 (congrArg some h18) (congrArg some h19)
        he hf hev hfv heb hfb hw (left := .reg 18) (right := .reg 19)
  obtain ⟨mid,c,hr,hm,hn,hregs,hcost⟩ :=
    representativeFlush_runs st G e dst count winner h4 h5 h12 h16 h17 h18 he hev heb hd hc
  obtain ⟨out,hbegin,hmem,hkey,hname,hout⟩ :=
    representativeBeginClass_runs mid _ f ((hregs 19 (by decide)).trans h19)
      ((hregs 11 (by decide)).trans h11)
  have hseq : Runs w p ω (.seq representativeFlush representativeBeginClass) st .normal out (c+6) :=
    runs_seq_iff.mpr (Or.inr ⟨mid,c,5,hr,hbegin,by omega⟩)
  have hrun : Runs w p ω (representativeClassStep entry) st .normal out (c+14) :=
    runs_cond_iff.mpr ⟨0,c+6,ht,by simpa using hseq,by
      change c+14 = 7+(c+6)+1
      omega⟩
  exact ⟨out,c+14,hrun,hmem.trans hm,(hout 17 (by decide) (by decide)).trans hn,hkey,hname,
    fun r h12' h17' h18' => (hout r h18' h12').trans (hregs r h17'),by omega⟩

/-- A candidate in the current class updates the incumbent without emitting an edge. -/
theorem representativeClassContinue_runs {w entry vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph)
    (e f winner lengths L : ℕ)
    (hcmp : MeetsContract w p entry (unsignedLessContract w 4))
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap)
    (h11 : st.regs 11 = f) (h12 : st.regs 12 = winner)
    (h13 : st.regs 13 = lengths) (h14 : st.regs 14 = L)
    (h18 : st.regs 18 = representativeSortKey G vCap eCap e)
    (h19 : st.regs 19 = representativeSortKey G vCap eCap f)
    (he : e < eCap) (hf : f < eCap)
    (hev : (edgePairKey G e).2 < vCap) (hfv : (edgePairKey G f).2 < vCap)
    (heb : representativeSortKey G vCap eCap e < 2^w)
    (hfb : representativeSortKey G vCap eCap f < 2^w)
    (hsame : edgePairKey G e = edgePairKey G f) (hw : 1 < 2^w)
    (ha : lengths+f*L+L < 2^w) (hb : lengths+winner*L+L < 2^w)
    (hva : Valid st.mem (lengths+f*L) 4 L)
    (hvb : Valid st.mem (lengths+winner*L) 4 L) :
    ∃ out cost, Runs w p ω (representativeClassStep entry) st .normal out cost ∧
      out.mem = st.mem ∧
      out.regs 12 = (if unsignedVal st.mem (lengths+f*L) 4 L <
        unsignedVal st.mem (lengths+winner*L) 4 L then f else winner) ∧
      (∀ r, r ≠ 12 → r ≠ 15 → out.regs r = st.regs r) ∧ cost ≤ 41*L+31 := by
  have ht : (representativeSameClass (.reg 18) (.reg 19)).eval w st = some 1 := by
    simpa only [ite_eq_left hsame] using
      representativeSameClass_eval G h4 h5 (congrArg some h18) (congrArg some h19)
        he hf hev hfv heb hfb hw (left := .reg 18) (right := .reg 19)
  obtain ⟨out,c,hr,hm,hn,hregs,hcost⟩ :=
    representativeChoose_runs st f winner lengths L hcmp h11 h12 h13 h14 ha hb hva hvb
  have hrun : Runs w p ω (representativeClassStep entry) st .normal out (c+8) :=
    runs_cond_iff.mpr ⟨1,c,ht,by simpa using hr,by change c+8 = 7+c+1; omega⟩
  exact ⟨out,c+8,hrun,hm,hn,hregs,by omega⟩

/-- Read a sorted candidate and advance the representative scan by one edge. -/
def representativeGroupStep (entry : ℕ) : Stmt :=
  .seq representativeReadCandidate (representativeClassStep entry)

/-- Each group step either improves the current winner or starts the next class.
A boundary writes one winner only when the class has distinct endpoints. -/
theorem representativeGroupStep_runs {w entry vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph)
    (e f src i dst count winner lengths L : ℕ)
    (hcmp : MeetsContract w p entry (unsignedLessContract w 4))
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap)
    (h6 : st.regs 6 = src) (h8 : st.regs 8 = i)
    (h12 : st.regs 12 = winner) (h13 : st.regs 13 = lengths) (h14 : st.regs 14 = L)
    (h16 : st.regs 16 = dst) (h17 : st.regs 17 = count)
    (h18 : st.regs 18 = representativeSortKey G vCap eCap e)
    (hread : st.mem (src+i) = representativeSortKey G vCap eCap f)
    (he : e < eCap) (hf : f < eCap)
    (hev : (edgePairKey G e).2 < vCap) (hfv : (edgePairKey G f).2 < vCap)
    (heb : representativeSortKey G vCap eCap e < 2^w)
    (hfb : representativeSortKey G vCap eCap f < 2^w)
    (hs : src+i < 2^w) (hd : dst+count < 2^w) (hc : count+1 < 2^w)
    (ha : lengths+f*L+L < 2^w) (hb : lengths+winner*L+L < 2^w)
    (hva : Valid st.mem (lengths+f*L) 4 L)
    (hvb : Valid st.mem (lengths+winner*L) 4 L) :
    let same := edgePairKey G e = edgePairKey G f
    let emit := ¬same ∧ (edgePairKey G e).1 ≠ (edgePairKey G e).2
    ∃ out cost, Runs w p ω (representativeGroupStep entry) st .normal out cost ∧
      out.mem = (if emit then Function.update st.mem (dst+count) winner else st.mem) ∧
      out.regs 17 = (if emit then count+1 else count) ∧
      out.regs 18 = representativeSortKey G vCap eCap (if same then e else f) ∧
      out.regs 12 = (if same then
        if unsignedVal st.mem (lengths+f*L) 4 L < unsignedVal st.mem (lengths+winner*L) 4 L
        then f else winner else f) ∧
      (∀ r, r ≠ 11 → r ≠ 12 → r ≠ 15 → r ≠ 17 → r ≠ 18 → r ≠ 19 →
        out.regs r = st.regs r) ∧ cost ≤ 41*L+48 := by
  obtain ⟨mid,hr,hm,hkey,hname,hregs⟩ :=
    representativeReadCandidate_runs st G src i f h5 h6 h8 hread hs hf hfv hfb
  have keep r (hn : r ≠ 19) (hm' : r ≠ 11) := hregs r hn hm'
  by_cases same : edgePairKey G e = edgePairKey G f
  · obtain ⟨out,c,hstep,hmem,hwin,hout,hcost⟩ :=
      representativeClassContinue_runs mid G e f winner lengths L hcmp
        ((keep 4 (by decide) (by decide)).trans h4) ((keep 5 (by decide) (by decide)).trans h5)
        hname ((keep 12 (by decide) (by decide)).trans h12)
        ((keep 13 (by decide) (by decide)).trans h13) ((keep 14 (by decide) (by decide)).trans h14)
        ((keep 18 (by decide) (by decide)).trans h18) hkey he hf hev hfv heb hfb same
        (by omega) ha hb (by simpa only [hm]) (by simpa only [hm])
    refine ⟨out,10+c+1,runs_seq_iff.mpr (Or.inr ⟨mid,10,c,hr,hstep,rfl⟩),?_,?_,?_,?_,?_,by omega⟩
    · simpa [same] using hmem.trans hm
    · simpa [same] using (hout 17 (by decide) (by decide)).trans
        ((keep 17 (by decide) (by decide)).trans h17)
    · simpa [same] using (hout 18 (by decide) (by decide)).trans
        ((keep 18 (by decide) (by decide)).trans h18)
    · simpa [same,hm] using hwin
    · exact fun r h11 h12' h15 _ _ h19 => (hout r h12' h15).trans (keep r h19 h11)
  · obtain ⟨out,c,hstep,hmem,hn,hnew,hwin,hout,hcost⟩ :=
      representativeClassBoundary_runs (entry := entry) mid G e f dst count winner
        ((keep 4 (by decide) (by decide)).trans h4) ((keep 5 (by decide) (by decide)).trans h5)
        hname ((keep 12 (by decide) (by decide)).trans h12)
        ((keep 16 (by decide) (by decide)).trans h16) ((keep 17 (by decide) (by decide)).trans h17)
        ((keep 18 (by decide) (by decide)).trans h18) hkey he hf hev hfv heb hfb same hd hc
    refine ⟨out,10+c+1,runs_seq_iff.mpr (Or.inr ⟨mid,10,c,hr,hstep,rfl⟩),?_,?_,?_,?_,?_,by omega⟩
    · by_cases h : (edgePairKey G e).1 = (edgePairKey G e).2 <;> simpa [same,h,hm] using hmem
    · by_cases h : (edgePairKey G e).1 = (edgePairKey G e).2 <;> simpa [same,h] using hn
    · simpa [same] using hnew
    · simpa [same] using hwin
    · exact fun r h11 h12' _ h17' h18' h19 => (hout r h12' h17' h18').trans (keep r h19 h11)

/-- Initialize the output count and seed the first class at sorted index zero. -/
def representativeGroupInit : Stmt :=
  .seq (.assign 8 (.const 0)) (.seq (.assign 17 (.const 0))
    (.seq representativeReadCandidate representativeBeginClass))

/-- The first edge supplies both the class key and its initial winner. -/
theorem representativeGroupInit_runs {w vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (src e : ℕ)
    (h5 : st.regs 5 = eCap) (h6 : st.regs 6 = src)
    (hm : st.mem src = representativeSortKey G vCap eCap e)
    (hs : src < 2^w) (he : e < eCap) (hv : (edgePairKey G e).2 < vCap)
    (hk : representativeSortKey G vCap eCap e < 2^w) :
    ∃ out, Runs w p ω representativeGroupInit st .normal out 22 ∧
      out.mem = st.mem ∧ out.regs 17 = 0 ∧
      out.regs 18 = representativeSortKey G vCap eCap e ∧ out.regs 12 = e ∧
      ∀ r, r ≠ 8 → r ≠ 11 → r ≠ 12 → r ≠ 17 → r ≠ 18 → r ≠ 19 →
        out.regs r = st.regs r := by
  let first := {st with regs := Function.update st.regs 8 0}
  let next := {first with regs := Function.update first.regs 17 0}
  have hz : 0 < 2^w := by omega
  have hfirst : Runs w p ω (.assign 8 (.const 0)) st .normal first 2 :=
    runs_assign_iff.mpr ⟨0,by simp [Expr.eval,hz],rfl,rfl,rfl⟩
  have hnext : Runs w p ω (.assign 17 (.const 0)) first .normal next 2 :=
    runs_assign_iff.mpr ⟨0,by simp [Expr.eval,hz],rfl,rfl,rfl⟩
  obtain ⟨mid,hread,hmem,hkey,hname,hkeep⟩ :=
    representativeReadCandidate_runs next G src 0 e (by simpa [next,first] using h5)
      (by simpa [next,first] using h6) (by simp [next,first])
      (by simpa [next,first] using hm) (by simpa using hs) he hv hk
  obtain ⟨out,hbegin,hout,hclass,hwinner,hregs⟩ :=
    representativeBeginClass_runs mid _ e hkey hname
  have hseed : Runs w p ω (.seq representativeReadCandidate representativeBeginClass)
      next .normal out 16 :=
    runs_seq_iff.mpr (Or.inr ⟨mid,10,5,hread,hbegin,rfl⟩)
  have hcount : Runs w p ω (.seq (.assign 17 (.const 0))
      (.seq representativeReadCandidate representativeBeginClass)) first .normal out 19 :=
    runs_seq_iff.mpr (Or.inr ⟨next,2,16,hnext,hseed,rfl⟩)
  refine ⟨out,runs_seq_iff.mpr (Or.inr ⟨first,2,19,hfirst,hcount,rfl⟩),
    hout.trans hmem,?_,hclass,hwinner,?_⟩
  · rw [hregs 17 (by decide) (by decide),hkeep 17 (by decide) (by decide)]
    simp [next]
  · intro r h8 h11 h12 h17 h18 h19
    rw [hregs r h18 h12,hkeep r h19 h11]
    simp [next,first,h8,h17]

/-- Scan the nonempty sorted array and finish its last class.
An empty input initializes the count without reading any key. -/
def representativeGroupScan (entry : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 7) (.const 0)) (.assign 17 (.const 0))
    (.seq representativeGroupInit
      (.seq (forRange 8 (.const 1) (.reg 7) (representativeGroupStep entry)) representativeFlush))

/-- An empty array produces zero winners and leaves memory untouched. -/
theorem representativeGroupScan_empty_runs {w entry : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (hn : st.regs 7 = 0) (hw : 1 < 2^w) :
    ∃ out, Runs w p ω (representativeGroupScan entry) st .normal out 6 ∧
      out.mem = st.mem ∧ out.regs 17 = 0 ∧ ∀ r, r ≠ 17 → out.regs r = st.regs r := by
  let out := {st with regs := Function.update st.regs 17 0}
  have hz : 0 < 2^w := by omega
  have htest : (.bin .eq (.reg 7) (.const 0) : Expr).eval w st = some 1 := by
    simp [Expr.eval,BinOp.eval,hn,hw,hz]
  have hzero : Runs w p ω (.assign 17 (.const 0)) st .normal out 2 :=
    runs_assign_iff.mpr ⟨0,by simp [Expr.eval,hz],rfl,rfl,rfl⟩
  refine ⟨out,runs_cond_iff.mpr ⟨1,2,htest,by simpa using hzero,rfl⟩,rfl,?_,?_⟩
  · simp [out]
  · exact fun r hr => Function.update_of_ne hr ..

/-- For one sorted edge the scan seeds and finishes the same class. -/
theorem representativeGroupScan_single_runs {w entry vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (src dst e : ℕ)
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap) (h6 : st.regs 6 = src)
    (h7 : st.regs 7 = 1) (h16 : st.regs 16 = dst)
    (hm : st.mem src = representativeSortKey G vCap eCap e)
    (hs : src < 2^w) (hd : dst < 2^w) (hw : 1 < 2^w)
    (he : e < eCap) (hv : (edgePairKey G e).2 < vCap)
    (hk : representativeSortKey G vCap eCap e < 2^w) :
    let isLoop := (edgePairKey G e).1 = (edgePairKey G e).2
    ∃ out cost, Runs w p ω (representativeGroupScan entry) st .normal out cost ∧
      out.mem = (if isLoop then st.mem else Function.update st.mem dst e) ∧
      out.regs 17 = (if isLoop then 0 else 1) ∧ cost ≤ 58 := by
  obtain ⟨seed,hseed,hmem,hcount,hclass,hwinner,hkeep⟩ :=
    representativeGroupInit_runs st G src e h5 h6 hm hs he hv hk
  let mid := {seed with regs := Function.update seed.regs 8 1}
  have hkeep' r (h8' : r ≠ 8) : mid.regs r = seed.regs r :=
    Function.update_of_ne h8' ..
  have hz : 0 < 2^w := by omega
  have hset : Runs w p ω (.assign 8 (.const 1)) seed .normal mid 2 :=
    runs_assign_iff.mpr ⟨1,by simp [Expr.eval,hw],rfl,rfl,rfl⟩
  have hhi : mid.regs 7 = 1 := (hkeep' 7 (by decide)).trans
    ((hkeep 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h7)
  have hstop : Runs w p ω (forUp 8 (.reg 7) (representativeGroupStep entry)) mid .normal mid 4 :=
    runs_loop_iff.mpr (Or.inl ⟨by
      have h8 : mid.regs 8 = 1 := by simp [mid]
      simp [Expr.eval,BinOp.eval,h8,hhi,hz],rfl,rfl,rfl⟩)
  have hloop : Runs w p ω (forRange 8 (.const 1) (.reg 7) (representativeGroupStep entry))
      seed .normal mid 7 :=
    runs_seq_iff.mpr (Or.inr ⟨mid,2,4,hset,hstop,rfl⟩)
  obtain ⟨out,c,hflush,hout,hresult,_,hcost⟩ := representativeFlush_runs mid G e dst 0 e
    ((hkeep' 4 (by decide)).trans ((hkeep 4 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h4))
    ((hkeep' 5 (by decide)).trans ((hkeep 5 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h5))
    ((hkeep' 12 (by decide)).trans hwinner)
    ((hkeep' 16 (by decide)).trans ((hkeep 16 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h16))
    ((hkeep' 17 (by decide)).trans hcount) ((hkeep' 18 (by decide)).trans hclass)
    he hv hk (by simpa using hd) (by simpa using hw)
  have htail : Runs w p ω (.seq (forRange 8 (.const 1) (.reg 7)
      (representativeGroupStep entry)) representativeFlush) seed .normal out (c+8) :=
    runs_seq_iff.mpr (Or.inr ⟨mid,7,c,hloop,hflush,by omega⟩)
  have hbody : Runs w p ω (.seq representativeGroupInit
      (.seq (forRange 8 (.const 1) (.reg 7) (representativeGroupStep entry)) representativeFlush))
      st .normal out (c+31) :=
    runs_seq_iff.mpr (Or.inr ⟨seed,22,c+8,hseed,htail,by omega⟩)
  have hrun : Runs w p ω (representativeGroupScan entry) st .normal out (c+35) :=
    runs_cond_iff.mpr ⟨0,c+31,by simp [Expr.eval,BinOp.eval,h7,hz],
      by simpa using hbody,by change c+35 = 3+(c+31)+1; omega⟩
  exact ⟨out,c+35,hrun,by simpa [mid,hmem] using hout,hresult,by omega⟩

end MinCostFlow.LastLevelProgram
