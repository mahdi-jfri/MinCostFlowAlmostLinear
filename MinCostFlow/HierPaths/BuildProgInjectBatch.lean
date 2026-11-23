module

public import MinCostFlow.HierPaths.BuildProgInjectLayout
public import MinCostFlow.HierPaths.BuildProgInjectSides
import MinCostFlow.HierPaths.BuildProgPlayerViews

/-!
# Batched final injection

Scan the saved pointers in original child order, reuse one mask, and
write the two offsets and terminal lists of each router request.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

/-- The finished game's saved pointers give the two sets of each pair. -/
def InjectInput (w : ℕ) (mem : ℕ → ℕ) (saved mask first s : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) : Prop :=
  ∀ i < pairs.length, ∃ S : Finset ℕ, S ⊆ Finset.range s ∧
    let rep := mem (saved+i)
    rep + 4 + S.card ≤ mask ∧ ListAt mem rep (coreResultWords (.expander S)) ∧
    pairs.getD i (∅,∅) =
      (shiftSet (first+i*s) (Finset.range s \ S),shiftSet (first+i*s) S) ∧
    first+i*s+s < 2^w

/-- Read one reply, pack its row at the fixed stride, then write the offsets. -/
def buildInjectionStep (fSides : ℕ) : Stmt :=
  .seq (.assign 8 (.bin .mul (.reg 7) (.reg 3)))
    (.seq (.assign 9 (.load (.bin .add (.reg 0) (.reg 7))))
      (.seq (.call 10 fSides [
        .bin .add (.reg 9) (.const 4),
        .bin .sub (.load (.bin .add (.reg 9) (.const 2))) (.const 1),
        .reg 3,.reg 1,.bin .add (.reg 6) (.reg 8),.bin .add (.reg 5) (.reg 8)])
        (.seq (.store (.bin .add (.reg 4) (.bin .add (.reg 7) (.reg 7))) (.reg 8))
          (.store (.bin .add (.bin .add (.reg 4) (.bin .add (.reg 7) (.reg 7))) (.const 1))
            (.bin .add (.reg 8) (.reg 10))))))

/-- Args are the saved pointers, mask, number of children, child size,
output base, and first terminal. -/
def buildInjectionProc (fSides : ℕ) : Stmt :=
  .seq (.assign 6 (.bin .add (.bin .add (.reg 4) (.bin .add (.reg 2) (.reg 2))) (.const 1)))
    (.seq (forRange 7 (.const 0) (.reg 2) (buildInjectionStep fSides))
      (.seq (.store (.bin .add (.reg 4) (.bin .add (.reg 2) (.reg 2)))
        (.bin .mul (.reg 2) (.reg 3)))
        (.ret (.bin .add (.reg 6) (.bin .mul (.reg 2) (.reg 3))))))

theorem buildInjectionProc_noRand (fSides : ℕ) : (buildInjectionProc fSides).NoRand := by
  simp [buildInjectionProc,buildInjectionStep,forRange,forUp,Stmt.NoRand]

/-- Build the router's request from the saved replies below the mask. -/
def buildInjectionContract (w s : ℕ) (pairs : List (Finset ℕ × Finset ℕ)) : Contract where
  pre args mem := ∃ saved mask first out, args = [saved,mask,pairs.length,s,out,first] ∧
    saved+pairs.length ≤ mask ∧ mask+s ≤ out ∧ buildBatchEnd out pairs.length s+s < 2^w ∧
    4 < 2^w ∧ InjectInput w mem saved mask first s pairs ∧
    ∀ i < pairs.length, (buildBatchRow pairs i).length = s
  post args mem v mem' := ∃ saved mask first out, args = [saved,mask,pairs.length,s,out,first] ∧
    v = buildBatchEnd out pairs.length s ∧ InjectWritten mem' out s pairs ∧
    ∀ j, (j < mask ∨ mask+s ≤ j) → (j < out ∨ v ≤ j) → mem' j = mem j
  cost _ _ := pairs.length*(120*s+260)+64

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.ExpanderDecomp

private def injectInv (mem : ℕ → ℕ) (saved mask first out s : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = saved ∧ st.regs 1 = mask ∧ st.regs 2 = pairs.length ∧
  st.regs 3 = s ∧ st.regs 4 = out ∧ st.regs 5 = first ∧
  st.regs 6 = out+2*pairs.length+1 ∧ st.regs 7 = i ∧
  (∀ j < i, st.mem (out+2*j) = j*s ∧
    st.mem (out+2*j+1) = j*s+(pairs.getD j (∅,∅)).1.card ∧
    ListAt st.mem (out+2*pairs.length+1+j*s) (buildBatchRow pairs j)) ∧
  ∀ j, (j < mask ∨ mask+s ≤ j) →
    (j < out ∨ (out+2*i ≤ j ∧ j < out+2*pairs.length+1) ∨
      out+2*pairs.length+1+i*s ≤ j) → st.mem j = mem j

private theorem buildInjection_step {w saved mask out first s i fSides fMask fPack : ℕ} {p : Program}
    {mem : ℕ → ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hProc : p.procs[fSides]? = some (buildInjectSidesProc fMask fPack))
    (hMask : p.procs[fMask]? = some buildCutMaskProc)
    (hPack : p.procs[fPack]? = some buildCutPackProc)
    (hi : i < pairs.length) (hSaved : saved + pairs.length ≤ mask) (hMaskEnd : mask + s ≤ out)
    (hRoom : buildBatchEnd out pairs.length s + s < 2^w) (hw : 4 < 2^w)
    (hSets : InjectInput w mem saved mask first s pairs)
    (hLen : ∀ j < pairs.length, (buildBatchRow pairs j).length = s) :
    Triple w p (injectInv mem saved mask first out s pairs i) (buildInjectionStep fSides)
      (normalPost fun st => injectInv mem saved mask first out s pairs (i+1)
        {st with regs := Function.update st.regs 7 (i+1)} ∧ st.regs 7 = i)
      (fun _ => 120*s+240) := by
  intro st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,hPrev,hFrame⟩
  let data := out+2*pairs.length+1
  let rep := mem (saved+i)
  let dest := data+i*s
  let off := first+i*s
  obtain ⟨S,hS,hRep,hBlock,hPair,hOff⟩ := hSets i hi
  change rep+4+S.card ≤ mask at hRep
  change ListAt mem rep (coreResultWords (.expander S)) at hBlock
  change pairs.getD i (∅,∅) = (shiftSet off (Finset.range s \ S),shiftSet off S) at hPair
  change off+s < 2^w at hOff
  obtain ⟨hSrc,hOffset⟩ := coreSet_view hBlock
  have hBase : out+2*pairs.length+1+pairs.length*s+s < 2^w := hRoom
  have hRead (a : ℕ) (ha : a < mask) : st.mem a = mem a :=
    hFrame a (Or.inl ha) (Or.inl (by omega))
  have hCell : st.mem (saved+i) = rep := hRead _ (by omega)
  have hCellW : saved+i < 2^w := by omega
  have hRepW : rep < 2^w := by omega
  have hRep2W : rep+2 < 2^w := by omega
  have hRep4W : rep+4 < 2^w := by omega
  have hOffsetW : 1+S.card < 2^w := by omega
  have hSW : s < 2^w := by omega
  have hMaskW : mask < 2^w := by omega
  have hTwo : 2 < 2^w := by omega
  have hCardW : S.card < 2^w := by omega
  have hiLast : (i+1)*s = i*s+s := Nat.succ_mul i s
  have hiProd : i*s+s ≤ pairs.length*s := by
    rw [← hiLast]
    exact Nat.mul_le_mul_right s hi
  have hProdW : i*s < 2^w := by omega
  have hDestW : dest+2*s < 2^w := by dsimp [dest,data]; omega
  have hDest : dest < 2^w := by omega
  have hOffW : off < 2^w := by omega
  have hi2W : i+i < 2^w := by omega
  have hHeaderW : out+(i+i) < 2^w := by omega
  have hHeader1W : out+(i+i)+1 < 2^w := by omega
  have hOne : 1 < 2^w := by omega
  let len := (injectSides s off S).1.length
  have hLenEq : len = (pairs.getD i (∅,∅)).1.card := by
    rw [hPair]
    simp [len,injectSides,finsetWords,card_shiftSet]
  have hRow : (injectSides s off S).1 ++ (injectSides s off S).2 = buildBatchRow pairs i := by
    simp only [buildBatchRow,hPair,injectSides]
  have hMidW : i*s+len < 2^w := by
    have hBoth := injectSides_length (off := off) hS
    change len+_ = s at hBoth
    omega
  refine runs_start_le ?_
  unfold buildInjectionStep
  refine runs_seq_assign_le (v := i*s) (Expr.eval_mul (Expr.eval_reg_of_eq h7)
    (Expr.eval_reg_of_eq h3) hProdW) ?_
  refine runs_seq_assign_le (v := rep) ?_ ?_
  · simp [Expr.eval,Function.update,h0,h7,hCellW,hCell]
  refine runs_seq_call_le (buildInjectSidesProc_meetsContract hProc hMask hPack)
    (vs := [rep+4,S.card,s,mask,dest,off]) ?_ ?_
    ⟨rep+4,mask,dest,off,rfl,?_,hS,hRep,by dsimp [dest,data]; omega,hDestW,hOff,hOne⟩ ?_
  · have hReadOffset := (hRead (rep+2) (by omega)).trans hOffset
    simp [evalArgs,Expr.eval,Function.update,h1,h3,h5,h6,hRep2W,hRep4W,hw,hTwo,hOne,hCardW,
      hReadOffset,hDest,dest,data,off,hOffW]
  · wram_words
  · exact WordRAM.ListAt.congr hSrc fun a _ ha => hRead a (by
      have hL : (finsetWords S).length = S.card := by simp [finsetWords]
      omega)
  intro a mem' pos' hPost
  obtain ⟨_,_,_,_,he,hLen',hCopy',hBelow⟩ := hPost
  simp only [List.cons.injEq,and_true,true_and] at he
  obtain ⟨rfl,rfl,rfl,rfl⟩ := he
  have ha : a = len := hLen'
  subst a
  rw [hRow] at hCopy'
  have hBelow' (a : ℕ) (ha : a < mask ∨ mask+s ≤ a) (hb : a < dest ∨ dest+s ≤ a) :
      mem' a = st.mem a := hBelow a ha hb
  refine runs_seq_store_le (x := out + 2 * i) (v := i * s) ?_ ?_ ?_
  · simp [Expr.eval, Function.update, h4, h7, hi2W, hHeaderW, Nat.two_mul]
  · simp [Expr.eval, Function.update]
  refine runs_store_le (x := out + 2 * i + 1) (v := i * s + len) ?_ ?_ ?_ ?_
  · simp [Expr.eval, Function.update, h4, h7, hi2W, hHeaderW, hHeader1W, hOne, Nat.two_mul]
  · exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_reg_of_eq (by simp only [Function.update_self]; exact ha)) hMidW
  · let next := Function.update (Function.update mem' (out + 2 * i) (i * s))
        (out + 2 * i + 1) (i * s + len)
    have hNoTouch {a : ℕ} (ha : a ≠ out + 2 * i) (hb : a ≠ out + 2 * i + 1) : next a = mem' a := by
      simp [next, Function.update_of_ne, ha, hb]
    refine ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
      by simpa using h4, by simpa using h5, by simpa using h6, by simp, ?_, ?_⟩, h7⟩
    · intro j hj
      change next (out + 2 * j) = j * s ∧ next (out + 2 * j + 1) = j * s + (pairs.getD j (∅,∅)).1.card ∧ _
      have hData : ∀ a, data ≤ a → next a = mem' a := fun a ha => hNoTouch (by omega) (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨hl, hr, hOld⟩ := hPrev j hj
        have hjmul : j * s + s ≤ i * s := by
          rw [← Nat.succ_mul]
          exact Nat.mul_le_mul_right s (by omega)
        refine ⟨?_, ?_, ?_⟩
        · rw [hNoTouch (by omega) (by omega), hBelow' _ (Or.inr (by omega)) (Or.inl (by dsimp [dest]; omega))]
          exact hl
        · rw [hNoTouch (by omega) (by omega), hBelow' _ (Or.inr (by omega)) (Or.inl (by dsimp [dest]; omega))]
          exact hr
        · exact WordRAM.ListAt.congr hOld fun a ha hb => (hData a (by omega)).trans
            (hBelow' a (Or.inr (by omega)) (Or.inl (by rw [hLen j (hj.trans hi)] at hb; dsimp [dest]; omega)))
      · refine ⟨?_, by simp [next,hLenEq], ?_⟩
        · simp [next]
        · exact WordRAM.ListAt.congr hCopy' fun a ha _ => hData a (by change data + j * s ≤ a at ha; omega)
    · intro j hm hj
      change next j = mem j
      have hNever : j ≠ out + 2 * i ∧ j ≠ out + 2 * i + 1 := by
        rw [hiLast] at hj
        omega
      rw [hNoTouch hNever.1 hNever.2]
      refine (hBelow' _ hm ?_).trans (hFrame _ hm ?_)
      · rw [hiLast] at hj
        dsimp [dest]
        omega
      · rw [hiLast] at hj
        omega
  · simp [buildInjectSidesContract, argsSize, Expr.size]
    omega

/-- The injection scan writes a contiguous batch and its two section offsets
per child, in time linear in the number of written words. -/
theorem buildInjectionProc_meetsContract {w s f fSides fMask fPack : ℕ} {p : Program}
    {pairs : List (Finset ℕ × Finset ℕ)}
    (hf : p.procs[f]? = some (buildInjectionProc fSides))
    (hc : p.procs[fSides]? = some (buildInjectSidesProc fMask fPack))
    (hm : p.procs[fMask]? = some buildCutMaskProc)
    (hp : p.procs[fPack]? = some buildCutPackProc) :
    MeetsContract w p f (buildInjectionContract w s pairs) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨saved,mask,first,out,rfl,hSaved,hMaskEnd,hEnd,hw,hRows,hLen⟩ := hPre
  let k := pairs.length
  let data := out + 2 * k + 1
  have hFit : out + 2 * k + 1 + k * s < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ s) hEnd
  have hData : data < 2 ^ w := by dsimp [data]; omega
  have hOne : 1 < 2 ^ w := by omega
  have hK2 : k + k < 2 ^ w := by omega
  have hOutK : out + (k + k) < 2 ^ w := by omega
  have hProd : k * s < 2 ^ w := by omega
  let st0 := startState [saved,mask,k,s,out,first] mem pos
  let st1 : State := {st0 with regs := Function.update st0.regs 6 data}
  have hLoop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 2)
    (body := buildInjectionStep fSides) (P := fun st => st = st1)
    (Inv := injectInv mem saved mask first out s pairs)
    (120*s+240) 0 k (Nat.zero_le _) hOne (fun _ => by omega)
    (fun st hEq => by
      subst st
      refine ⟨Expr.eval_const (Nat.two_pow_pos _), ?_⟩
      exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _ hj => False.elim (Nat.not_lt_zero _ hj),
        fun _ _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1)
    (fun _ _ hi => buildInjection_step hc hm hp hi hSaved hMaskEnd hEnd hw hRows hLen)
  refine runs_start_le ?_
  unfold buildInjectionProc
  refine runs_seq_assign_le (v := data) ?_ ?_
  · change pairs.length + pairs.length < 2 ^ w at hK2
    change out + (pairs.length + pairs.length) < 2 ^ w at hOutK
    have hData' : out + (pairs.length + pairs.length) + 1 < 2 ^ w := by omega
    simp [Expr.eval, startState, hK2, hOutK, hOne, hData', data, Nat.two_mul]; rfl
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_, _, h2, h3, h4, _, h6, _, hRowsOut, hFrame⟩
  have h2' : st.regs 2 = k := h2
  have h5' : st.regs 6 = data := h6
  refine runs_seq_store_le (x := out + 2 * k) (v := k * s) ?_ ?_ ?_
  · simp [Expr.eval, h2', h4, hK2, hOutK, Nat.two_mul]
  · exact Expr.eval_mul (Expr.eval_reg_of_eq h2') (Expr.eval_reg_of_eq h3) hProd
  refine runs_ret_le (v := buildBatchEnd out k s) ?_ ?_ ?_
  · exact Expr.eval_add (Expr.eval_reg_of_eq h5')
      (Expr.eval_mul (Expr.eval_reg_of_eq h2') (Expr.eval_reg_of_eq h3) hProd) hFit
  · let next := Function.update st.mem (out + 2 * k) (k * s)
    have hk : k = pairs.length := rfl
    refine ⟨saved,mask,first,out,rfl,rfl, ⟨by simp [hk], ?_⟩, ?_⟩
    · intro j hj
      have hj' : j < k := hj
      obtain ⟨hl, hr, hAt⟩ := hRowsOut j hj
      have hNoTouch : ∀ a ≠ out + 2 * k, next a = st.mem a :=
        fun _ ha => Function.update_of_ne ha _ _
      change next (out + 2 * j) = _ ∧ next (out + 2 * j + 1) = _ ∧ ListAt next _ _
      refine ⟨(hNoTouch _ (by omega)).trans hl, (hNoTouch _ (by omega)).trans hr, ?_⟩
      exact WordRAM.ListAt.congr hAt fun a ha _ => hNoTouch a (by omega)
    · intro j hm hj
      change next j = mem j
      change j < out ∨ out + 2 * k + 1 + k * s ≤ j at hj
      rw [show next j = st.mem j from Function.update_of_ne (by omega) _ _]
      exact hFrame j hm (by
        rcases hj with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h))
  · simp [buildInjectionContract, Expr.size, k, Nat.mul_add]
    omega

end MinCostFlow.HierPaths
