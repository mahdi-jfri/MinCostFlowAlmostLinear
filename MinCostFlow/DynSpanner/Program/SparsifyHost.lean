module

public import MinCostFlow.DynSpanner.Program.CanonicalSparsify
public import MinCostFlow.DynSpanner.Program.GraphTranslateDyn
public import MinCostFlow.DynSpanner.Program.GraphTranslateRevDyn
public import WordRAM.Tactic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Host Word-RAM `Sparsify` Wrapper (`SparsifyHost`)

Composes:
1. `gtForwardDynStmt` (`DynGraphAt H'`, `DynGraphAt J`, `MEmbAt embJH` → `canonSparsifyInput` at `guestBase`),
2. `computeWordSizeStmt` (`w' = wordSize impl.cw input`),
3. Relocated guest `Sparsify` call (`sparsifyGuestProcs impl bGuest` at `bGuest + 1`),
4. `gtReverseDynStmt` (`SparsifyOutRelocAt` → `DynGraphAt out.Jtilde`, `MEmbBounded out.emb`, `ZeroFrom`),

into a single host Word-RAM procedure `sparsifyDynStmt` satisfying `sparsifyDyn_meetsContract`,
matching `canonicalSparsify impl H' J emb` cleanly with monotonic heap discipline.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.Cited

@[expose] public section

def gtIdxSparsifyDyn : ℕ := 0

/-- Relocated guest `Sparsify` procedure table anchored at `bGuest` (`p.HasAt bGuest`). -/
def sparsifyGuestProcs (impl : SparsifyImpl) (_bGuest : ℕ) : List Stmt :=
  .nop :: impl.procs.map (relocStmt impl.program.regBound _bGuest)

/-- Guest call argument list preparing registers `0..R-1 = [0, r7, 0, ...]`,
`R = r6 (guestBase)`, `R + 1 = r9 (2 ^ w')`. -/
def sparsifyGuestCallArgs (R : ℕ) : List Expr :=
  (List.take R [Expr.const 0, .reg 7] ++ List.replicate (R - 2) (.const 0)) ++ [.reg 6, .reg 9]

/-- Pure register/memory setup preparing `[triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr]`
in registers `11..14` for `gtReverseDynStmt`. -/
def spHostSetupRevStmt : Stmt :=
  .assign 11 (.bin .add (.reg 6) (.reg 10)) ;;
  .assign 12 (.load (.bin .add (.reg 1) (.const dgMOff))) ;;
  .assign 12 (.bin .add (.reg 11) (.bin .mul (.const 3) (.reg 12))) ;;
  .assign 13 (.bin .add (.reg 12)
    (.bin .add (.const 4)
      (.bin .add (.bin .mul (.const 7) (.reg 3)) (.bin .mul (.const 9) (.reg 4))))) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 4))

/-- Host Word-RAM `Sparsify` driver:
`args = [hPtr, jPtr, mEmbPtr, vCapOut, eCapOut, scratchPtr, guestBase]`.
Writes `[jtildeDynPtr, mEmbOutPtr]` to `mem'[scratchPtr .. scratchPtr + 1]` and returns
`newHeap` with `DynGraphAt` for `out.Jtilde`, `MEmbBounded` for `out.emb`, and `ZeroFrom mem' newHeap`. -/
def sparsifyDynStmt (R cw bFwd bRevDyn bGuest : ℕ) : Stmt :=
  .call 7 (bFwd + gtIdxForwardDyn) [.reg 0, .reg 1, .reg 2, .reg 5, .reg 6] ;;
  computeWordSizeStmt cw 6 7 8 9 10 11 12 ;;
  .call 10 (bGuest + 1) (sparsifyGuestCallArgs R) ;;
  spHostSetupRevStmt ;;
  .call 15 (bRevDyn + gtIdxReverseDyn)
    [.reg 1, .reg 6, .reg 7, .reg 3, .reg 4, .reg 5, .reg 11, .reg 12, .reg 13, .reg 14] ;;
  .store (.reg 5) (.reg 12) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.reg 13) ;;
  .ret (.reg 15)

/-- Module containing `sparsifyDynStmt`. -/
def sparsifyDynProcs (R cw bFwd bRevDyn bGuest : ℕ) : List Stmt :=
  [sparsifyDynStmt R cw bFwd bRevDyn bGuest]

/-- Contract for `sparsifyDynStmt` with respect to `canonicalSparsify impl` at edge cap `mMax`. -/
noncomputable def sparsifyDynContract (impl : SparsifyImpl) (mMax : ℕ)
    (w vCapH eCapH vCapJ eCapJ vCapOut eCapOut : ℕ)
    (H' J : MGraph) (emb : MinCostFlow.Embedding) : Contract where
  pre args mem := ∃ hPtr jPtr mEmbPtr scratchPtr guestBase,
    let rawEsLen := (collectRawEsFun (vertsOf J.E) emb).length
    let sLen := max (gtFwdDynScratchLen J.n J.m rawEsLen) (gtRevDynScratchLen J.n J.m)
    let x := canonSparsifyInput H' J emb
    let w' := wordSize impl.cw x
    let walkBnd := J.m * (1 + 2 * Nat.ceil (impl.γ_ℓ mMax))
    args = [hPtr, jPtr, mEmbPtr, vCapOut, eCapOut, scratchPtr, guestBase] ∧
    16 ≤ 2 ^ w ∧
    1 ≤ J.n ∧
    vCapOut < 2 ^ w ∧ eCapOut < 2 ^ w ∧
    1 ≤ guestBase ∧
    w' ≤ w ∧
    guestBase + 2 ^ (w' + 1) + 2 + 3 * J.m + dynGraphSize vCapOut eCapOut + eCapOut + walkBnd < 2 ^ w ∧
    hPtr + dynGraphSize vCapH eCapH < guestBase ∧
    jPtr + dynGraphSize vCapJ eCapJ < guestBase ∧
    mEmbPtr + eCapH < guestBase ∧
    scratchPtr + sLen ≤ guestBase ∧
    (∀ i < dynGraphSize vCapH eCapH, hPtr + i < scratchPtr ∨ scratchPtr + sLen ≤ hPtr + i) ∧
    (∀ i < dynGraphSize vCapJ eCapJ, jPtr + i < scratchPtr ∨ scratchPtr + sLen ≤ jPtr + i) ∧
    (∀ e ∈ J.E, mEmbPtr + e < scratchPtr ∨ scratchPtr + sLen ≤ mEmbPtr + e) ∧
    (∀ e ∈ J.E, ∀ k < (mWalkEncode (emb e)).length,
      mem (mEmbPtr + e) + k < scratchPtr ∨ scratchPtr + sLen ≤ mem (mEmbPtr + e) + k) ∧
    ZeroFrom mem guestBase ∧
    DynGraphAt mem hPtr vCapH eCapH H' ∧
    DynGraphAt mem jPtr vCapJ eCapJ J ∧
    emb.IsEmbedding J H' ∧
    MEmbAt mem mEmbPtr J.E eCapH emb ∧
    J.m ≤ mMax ∧
    (J.E.Nonempty → 1 ≤ emb.length J) ∧
    (∀ v ∈ J.V, v < vCapOut) ∧ (∀ e ∈ J.E, e < eCapOut) ∧
    (∀ e ∈ J.E, mem (mEmbPtr + e) + (mWalkEncode (emb e)).length < guestBase)
  post args mem ret mem' := ∃ hPtr jPtr mEmbPtr scratchPtr guestBase,
    let rawEsLen := (collectRawEsFun (vertsOf J.E) emb).length
    let sLen := max (gtFwdDynScratchLen J.n J.m rawEsLen) (gtRevDynScratchLen J.n J.m)
    let out := canonicalSparsify impl H' J emb
    let jtildeDynPtr := mem' scratchPtr
    let mEmbOutPtr := mem' (scratchPtr + 1)
    args = [hPtr, jPtr, mEmbPtr, vCapOut, eCapOut, scratchPtr, guestBase] ∧
    guestBase ≤ jtildeDynPtr ∧
    jtildeDynPtr + dynGraphSize vCapOut eCapOut = mEmbOutPtr ∧
    mEmbOutPtr + eCapOut ≤ ret ∧
    ret < 2 ^ w ∧
    ret ≤ guestBase + 2 ^ (wordSize impl.cw (canonSparsifyInput H' J emb) + 1) + 2 +
      3 * J.m + dynGraphSize vCapOut eCapOut + eCapOut + J.m * (1 + 2 * Nat.ceil (impl.γ_ℓ mMax)) ∧
    DynGraphAt mem' jtildeDynPtr vCapOut eCapOut out.Jtilde ∧
    MEmbBounded mem' mEmbOutPtr J.E eCapOut out.emb mEmbOutPtr ret ∧
    (∀ e ∈ J.E, mEmbOutPtr + eCapOut ≤ mem' (mEmbOutPtr + e)) ∧
    ZeroFrom mem' ret ∧
    ∀ addr, (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) →
      addr < guestBase → mem' addr = mem addr
  cost _ _ :=
    let rawEsLen := (collectRawEsFun (vertsOf J.E) emb).length
    let lArg := J.n + 2 * rawEsLen + J.m + 2
    let x := canonSparsifyInput H' J emb
    let R := impl.program.regBound
    let cQ_bnd := ⌈impl.K_t * (impl.γ_t mMax) *
      (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (emb.length J : ℝ)) *
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t⌉₊
    1430 * (J.n + J.m + rawEsLen) * (Nat.log 2 lArg + 1) + 1250 * (J.n + J.m + rawEsLen) + 1500 +
    40 * (x.length + wordSize impl.cw x + 1) +
    (R + 6) * cQ_bnd + R +
    250 * J.n * (Nat.log 2 (J.n + 1) + 1) + 250 * J.m * (Nat.log 2 (J.m + 1) + 1) +
    430 * J.n + 1065 * J.m + 250 * (J.m * Nat.ceil (impl.γ_ℓ mMax)) + 1200

end

section PrivateHelpers

private lemma argsSize_append (xs ys : List Expr) :
    argsSize (xs ++ ys) = argsSize xs + argsSize ys := by
  induction xs with
  | nil => simp [argsSize]
  | cons x xs ih => simp [argsSize, ih, Nat.add_assoc]

private lemma argsSize_replicate_const0 :
    ∀ n : ℕ, argsSize (List.replicate n (Expr.const 0)) = n
  | 0 => rfl
  | n + 1 => by
    simp only [List.replicate_succ, argsSize, Expr.size, argsSize_replicate_const0 n]
    omega

private lemma argsSize_sparsifyGuestCallArgs (R : ℕ) :
    argsSize (sparsifyGuestCallArgs R) = R + 2 := by
  unfold sparsifyGuestCallArgs
  rw [argsSize_append, argsSize_append, argsSize_replicate_const0]
  rcases R with _ | _ | R
  · simp [argsSize, Expr.size]
  · simp [argsSize, Expr.size]
  · simp [argsSize, Expr.size]; omega

private lemma evalArgs_sparsifyGuestCallArgs {w R inLen guestBase W : ℕ} {st : State}
    (_hw2 : 1 < 2 ^ w) (hr6 : st.regs 6 = guestBase) (hr7 : st.regs 7 = inLen) (hr9 : st.regs 9 = W)
    (_hgb : guestBase < 2 ^ w) (_hil : inLen < 2 ^ w) (_hW : W < 2 ^ w) :
    ∃ vs, evalArgs w st (sparsifyGuestCallArgs R) = some vs ∧
      vs.length = R + 2 ∧
      vs[R]? = some guestBase ∧
      vs[R + 1]? = some W ∧
      ∀ r < R, vs.getD r 0 = (if r = 0 then 0 else if r = 1 then inLen else 0) := by
  let hdr := [Expr.const 0, .reg 7]
  let l1 := hdr.take R
  let l2 := List.replicate (R - 2) (Expr.const 0)
  let l3 := [Expr.reg 6, Expr.reg 9]
  have heval1 : evalArgs w st l1 = some (List.take R [0, inLen]) := by
    rcases R with _ | _ | R <;> simp [l1, hdr, evalArgs, Expr.eval, hr7]
  have heval2 : ∀ n : ℕ, evalArgs w st (List.replicate n (.const 0)) = some (List.replicate n 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, evalArgs, Expr.eval, ih]
  have heval3 : evalArgs w st l3 = some [guestBase, W] := by
    simp [l3, evalArgs, Expr.eval, hr6, hr9]
  have heval_app : ∀ (as bs : List Expr) (vas vbs : List ℕ),
      evalArgs w st as = some vas → evalArgs w st bs = some vbs →
      evalArgs w st (as ++ bs) = some (vas ++ vbs) := by
    intro as
    induction as with
    | nil => intro bs vas vbs ha hb; simp [evalArgs] at ha; subst ha; simpa
    | cons a as ih =>
      intro bs vas vbs ha hb
      simp only [List.cons_append, evalArgs] at ha ⊢
      cases hae : Expr.eval w st a with
      | none => rw [hae] at ha; simp at ha
      | some va =>
        rw [hae] at ha
        cases has : evalArgs w st as with
        | none => rw [has] at ha; simp at ha
        | some vrest =>
          rw [has] at ha; simp at ha; subst ha
          rw [ih bs vrest vbs has hb]
          simp
  let vs := (List.take R [0, inLen] ++ List.replicate (R - 2) 0) ++ [guestBase, W]
  have hpref_len : (List.take R [0, inLen] ++ List.replicate (R - 2) 0).length = R := by
    simp; omega
  refine ⟨vs, ?_, ?_, ?_, ?_, ?_⟩
  · exact heval_app _ _ _ _ (heval_app _ _ _ _ heval1 (heval2 (R - 2))) heval3
  · simp [vs]; omega
  · rw [List.getElem?_append_right (by simp [hpref_len]), hpref_len, Nat.sub_self]
    rfl
  · rw [List.getElem?_append_right (by simp [hpref_len]), hpref_len]
    simp
  · intro r hr
    have hlt : r < (List.take R [0, inLen] ++ List.replicate (R - 2) 0).length := by
      rw [hpref_len]; exact hr
    rw [List.getD_eq_getElem vs 0 (by simp [vs]; omega)]
    change vs[r]'_ = _
    rw [List.getElem_append_left hlt]
    by_cases hr2 : r < (List.take R [0, inLen]).length
    · rw [List.getElem_append_left hr2, List.getElem_take]
      rcases r with _ | _ | r
      · rfl
      · rfl
      · simp at hr2
    · rw [List.getElem_append_right (Nat.le_of_not_lt hr2), List.getElem_replicate]
      rcases r with _ | _ | r
      · exfalso; simp at hr2; omega
      · exfalso; simp at hr2; omega
      · rfl

private lemma hasAt_sparsifyGuestProcs {impl : SparsifyImpl} {bGuest : ℕ} {p : Program}
    (hp : p.HasAt bGuest (sparsifyGuestProcs impl bGuest)) :
    ∀ (f : ℕ) (body : Stmt), impl.program.procs[f]? = some body →
      p.procs[bGuest + 1 + f]? = some (relocStmt impl.program.regBound bGuest body) := by
  intro f body hf
  have hlt : f < impl.procs.length := by
    simpa [SparsifyImpl.program] using (List.getElem?_eq_some_iff.mp hf).1
  have h1 : f + 1 < (sparsifyGuestProcs impl bGuest).length := by
    simp [sparsifyGuestProcs]; omega
  have hget := hp.get h1
  have hf_eq : impl.procs[f]'hlt = body := by
    simpa [SparsifyImpl.program] using (List.getElem?_eq_some_iff.mp hf).2
  have hidx : bGuest + (f + 1) = bGuest + 1 + f := by omega
  rw [hidx] at hget
  simpa [sparsifyGuestProcs, hf_eq] using hget

private lemma runs_seq_of_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt}
    {st st₁ st' : State} {o : Outcome} {c₁ c₂ : ℕ}
    (h₁ : Runs w p ω s₁ st .normal st₁ c₁)
    (h₂ : Runs w p ω s₂ st₁ o st' c₂) :
    Runs w p ω (s₁ ;; s₂) st o st' (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, h₂, rfl⟩)

private lemma nat_le_ceil_of_le_real {n : ℕ} {r : ℝ} (h : (n : ℝ) ≤ r) : n ≤ Nat.ceil r := by
  have h1 : (n : ℝ) ≤ ((Nat.ceil r : ℕ) : ℝ) := le_trans h (Nat.le_ceil r)
  exact Nat.cast_le.mp h1

private lemma spHostSetupRev_triple {w : ℕ} {p : Program} {mem : ℕ → ℕ}
    {jPtr vCapOut eCapOut scratchPtr guestBase inLen retHeap mJ : ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hmJ : mem (jPtr + dgMOff) = mJ)
    (hjp : jPtr + dgMOff < 2 ^ w)
    (htr : guestBase + retHeap < 2 ^ w)
    (hjt : guestBase + retHeap + 3 * mJ < 2 ^ w)
    (hme : guestBase + retHeap + 3 * mJ + dynGraphSize vCapOut eCapOut < 2 ^ w)
    (hwb : guestBase + retHeap + 3 * mJ + dynGraphSize vCapOut eCapOut + eCapOut < 2 ^ w) :
    Triple w p
      (fun st => st.mem = mem ∧
        st.regs 1 = jPtr ∧ st.regs 3 = vCapOut ∧ st.regs 4 = eCapOut ∧
        st.regs 5 = scratchPtr ∧ st.regs 6 = guestBase ∧ st.regs 7 = inLen ∧ st.regs 10 = retHeap)
      spHostSetupRevStmt
      (normalPost fun st =>
        st.mem = mem ∧
        st.regs 1 = jPtr ∧ st.regs 3 = vCapOut ∧ st.regs 4 = eCapOut ∧
        st.regs 5 = scratchPtr ∧ st.regs 6 = guestBase ∧ st.regs 7 = inLen ∧ st.regs 10 = retHeap ∧
        st.regs 11 = guestBase + retHeap ∧
        st.regs 12 = guestBase + retHeap + 3 * mJ ∧
        st.regs 13 = guestBase + retHeap + 3 * mJ + dynGraphSize vCapOut eCapOut ∧
        st.regs 14 = guestBase + retHeap + 3 * mJ + dynGraphSize vCapOut eCapOut + eCapOut)
      (fun _ => 50) := by
  intro st ω hpre
  rcases hpre with ⟨rfl, r1, r3, r4, r5, r6, r7, r10⟩
  have hm_lt : mJ < 2 ^ w := by
    have : 3 * mJ ≤ guestBase + retHeap + 3 * mJ := by omega
    omega
  have h7v_lt : 7 * vCapOut < 2 ^ w := by simp [dynGraphSize] at hme; omega
  have h9e_lt : 9 * eCapOut < 2 ^ w := by simp [dynGraphSize] at hme; omega
  have h79_lt : 7 * vCapOut + 9 * eCapOut < 2 ^ w := by simp [dynGraphSize] at hme; omega
  have hdgs_lt : 4 + (7 * vCapOut + 9 * eCapOut) < 2 ^ w := by simp [dynGraphSize] at hme; omega
  have hw2 : 1 < 2 ^ w := by omega
  have hmJ' : st.mem (st.regs 1 + dgMOff) = mJ := by rwa [r1]
  let v11 := guestBase + retHeap
  let v12 := v11 + 3 * mJ
  let v13 := v12 + dynGraphSize vCapOut eCapOut
  let v14 := v13 + eCapOut
  let st1 := { st with regs := Function.update st.regs 11 v11 }
  have hs1 : Runs w p ω (.assign 11 (.bin .add (.reg 6) (.reg 10))) st .normal st1
      ((Expr.bin .add (.reg 6) (.reg 10)).size + 1) := by
    rw [runs_assign_iff]
    refine ⟨v11, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, r6, r10, htr, v11]
  have hs1_r1 : st1.regs 1 = jPtr := by simp [st1, Function.update_of_ne, r1]
  have hs1_r11 : st1.regs 11 = v11 := by simp [st1, Function.update_self]
  let st2 := { st1 with regs := Function.update st1.regs 12 mJ }
  have hs2 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 1) (.const dgMOff)))) st1 .normal st2
      ((Expr.load (.bin .add (.reg 1) (.const dgMOff))).size + 1) := by
    rw [runs_assign_iff]
    have hdglt : dgMOff < 2 ^ w := by simp [dgMOff]; omega
    have hmem1 : st1.mem (jPtr + dgMOff) = mJ := hmJ
    exact ⟨mJ, Expr.eval_load_of_eq (v := mJ)
      (by simp [Expr.eval, hs1_r1, hdglt, hjp]) hmem1, rfl, rfl, rfl⟩
  have hs2_r11 : st2.regs 11 = v11 := by simp [st2, Function.update_of_ne, hs1_r11]
  have hs2_r12 : st2.regs 12 = mJ := by simp [st2, Function.update_self]
  let st3 := { st2 with regs := Function.update st2.regs 12 v12 }
  have hs3 : Runs w p ω (.assign 12 (.bin .add (.reg 11) (.bin .mul (.const 3) (.reg 12)))) st2 .normal st3
      ((Expr.bin .add (.reg 11) (.bin .mul (.const 3) (.reg 12))).size + 1) := by
    rw [runs_assign_iff]
    have h3lt : 3 < 2 ^ w := by omega
    have h3m_lt : 3 * mJ < 2 ^ w := by omega
    have hv12_lt : v11 + 3 * mJ < 2 ^ w := hjt
    refine ⟨v12, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, hs2_r11, hs2_r12, h3lt, h3m_lt, hv12_lt, v12]
  have hs3_r3 : st3.regs 3 = vCapOut := by simp [st3, st2, st1, Function.update_of_ne, r3]
  have hs3_r4 : st3.regs 4 = eCapOut := by simp [st3, st2, st1, Function.update_of_ne, r4]
  have hs3_r12 : st3.regs 12 = v12 := by simp [st3, Function.update_self]
  let st4 := { st3 with regs := Function.update st3.regs 13 v13 }
  let e13 := Expr.bin .add (.reg 12)
    (.bin .add (.const 4)
      (.bin .add (.bin .mul (.const 7) (.reg 3)) (.bin .mul (.const 9) (.reg 4))))
  have hs4 : Runs w p ω (.assign 13 e13) st3 .normal st4 (e13.size + 1) := by
    rw [runs_assign_iff]
    have h4lt : 4 < 2 ^ w := by omega
    have h7lt : 7 < 2 ^ w := by omega
    have h9lt : 9 < 2 ^ w := by omega
    have hv13_lt : v12 + (4 + (7 * vCapOut + 9 * eCapOut)) < 2 ^ w := by
      dsimp only [v12, v11, dynGraphSize] at *; omega
    have he13_val : v12 + (4 + (7 * vCapOut + 9 * eCapOut)) = v13 := by
      dsimp only [v13, dynGraphSize]; ring
    refine ⟨v13, ?_, rfl, rfl, rfl⟩
    rw [← he13_val]
    simp [e13, Expr.eval, hs3_r12, hs3_r3, hs3_r4, h4lt, h7lt, h9lt, h7v_lt, h9e_lt, h79_lt, hdgs_lt, hv13_lt]
  have hs4_r4 : st4.regs 4 = eCapOut := by simp [st4, Function.update_of_ne, hs3_r4]
  have hs4_r13 : st4.regs 13 = v13 := by simp [st4, Function.update_self]
  let st5 := { st4 with regs := Function.update st4.regs 14 v14 }
  have hs5 : Runs w p ω (.assign 14 (.bin .add (.reg 13) (.reg 4))) st4 .normal st5
      ((Expr.bin .add (.reg 13) (.reg 4)).size + 1) := by
    rw [runs_assign_iff]
    have hv14_lt : v13 + eCapOut < 2 ^ w := by
      dsimp only [v13, v12, v11, dynGraphSize] at *; omega
    refine ⟨v14, ?_, rfl, rfl, rfl⟩
    simp [Expr.eval, hs4_r13, hs4_r4, hv14_lt, v14]
  refine ⟨.normal, st5, _,
    runs_seq_of_runs hs1 (runs_seq_of_runs hs2 (runs_seq_of_runs hs3 (runs_seq_of_runs hs4 hs5))),
    ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [st5, st4, st3, st2, st1, Function.update_of_ne, r1]
    · simp [st5, st4, st3, st2, st1, Function.update_of_ne, r3]
    · simp [st5, st4, st3, st2, st1, Function.update_of_ne, r4]
    · simp [st5, st4, st3, st2, st1, Function.update_of_ne, r5]
    · simp [st5, st4, st3, st2, st1, Function.update_of_ne, r6]
    · simp [st5, st4, st3, st2, st1, Function.update_of_ne, r7]
    · simp [st5, st4, st3, st2, st1, Function.update_of_ne, r10]
    · simp [st5, st4, st3, st2, st1, Function.update_of_ne, v11]
    · simp [st5, st4, hs3_r12, Function.update_of_ne, v12, v11]
    · simp [st5, hs4_r13, Function.update_of_ne, v13, v12, v11]
    · simp [st5, Function.update_self, v14, v13, v12, v11]
  · simp [e13, Expr.size]

private lemma mEmbBounded_update_outside {mem : ℕ → ℕ} {E : Finset ℕ} {emb : MinCostFlow.Embedding}
    {a eCap lo hi x v : ℕ}
    (hB : MEmbBounded mem a E eCap emb lo hi)
    (hx_lt : x < lo) :
    MEmbBounded (Function.update mem x v) a E eCap emb lo hi := by
  rcases hB with ⟨hla, hhi, hE⟩
  refine ⟨hla, hhi, fun e he => ?_⟩
  rcases hE e he with ⟨hec, hlo, hwhi, hW⟩
  have hne1 : a + e ≠ x := by omega
  rw [Function.update_of_ne hne1]
  refine ⟨hec, hlo, hwhi, ?_⟩
  intro i hi_lt
  have hne2 : mem (a + e) + i ≠ x := by omega
  rw [Function.update_of_ne hne2]
  exact hW i hi_lt

private lemma collectRawEsFun_length_le_mul {J : MGraph} {emb : MinCostFlow.Embedding} :
    (collectRawEsFun (vertsOf J.E) emb).length ≤ J.m * emb.length J := by
  unfold collectRawEsFun
  have hlen : ((vertsOf J.E).flatMap fun e => (emb e).map Prod.fst).length =
      ((vertsOf J.E).map fun e => (emb e).length).sum := by
    induction vertsOf J.E with
    | nil => simp
    | cons x xs ih => simp [List.flatMap_cons, List.length_append, ih]
  rw [hlen]
  have hle : ∀ (l : List ℕ), (∀ e ∈ l, e ∈ J.E) →
      (l.map fun e => (emb e).length).sum ≤ l.length * emb.length J := by
    intro l hl
    induction l with
    | nil => simp
    | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have he_mem : e ∈ J.E := hl e List.mem_cons_self
      have he_le : (emb e).length ≤ emb.length J := by
        unfold MinCostFlow.Embedding.length
        exact Finset.le_sup (f := fun e => (emb e).length) he_mem
      have hes_le := ih fun x hx => hl x (List.mem_cons_of_mem _ hx)
      omega
  have h1 := hle (vertsOf J.E) fun e he => Spanner.mem_vertsOf.mp he
  simpa [Spanner.vertsOf_length, MGraph.m] using h1

end PrivateHelpers

public section

/-- Verification of `sparsifyDynStmt`: meets `sparsifyDynContract impl ...` for any deterministic
`impl : SparsifyImpl` wrapped via `sparsifyGuestProcs`. -/
theorem sparsifyDyn_meetsContract (impl : SparsifyImpl) (mMax : ℕ)
    {w vCapH eCapH vCapJ eCapJ vCapOut eCapOut : ℕ}
    {p : Program} {bSort bOps bEdge bSplit bBatch bFwd bRevPrim bGT bRevCore bRevDyn bEmit bGuest bSpDyn : ℕ}
    {H' J : MGraph} {emb : MinCostFlow.Embedding}
    (hpSpDyn : p.HasAt bSpDyn (sparsifyDynProcs impl.program.regBound impl.cw bFwd bRevDyn bGuest))
    (hpGuest : p.HasAt bGuest (sparsifyGuestProcs impl bGuest))
    (hpFwd : p.HasAt bFwd (gtForwardProcs bOps bGT bEmit bFwd))
    (hpEmit : p.HasAt bEmit (gtEmitProcs bSort bOps bGT))
    (hpRevDyn : p.HasAt bRevDyn (gtRevDynProcs bOps bGT bRevCore))
    (hpRevCore : p.HasAt bRevCore (gtRevCoreProcs bBatch bRevPrim))
    (hpRevPrim : p.HasAt bRevPrim gtRevPrimProcs)
    (hpBatch : p.HasAt bBatch (dgBatchProcs bOps bEdge bSplit bBatch))
    (hpEdge : p.HasAt bEdge (dgEdgeProcs bOps))
    (hpOps : p.HasAt bOps dgOpsProcs)
    (hpGT : p.HasAt bGT (gtProcs bSort bOps))
    (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (bSpDyn + gtIdxSparsifyDyn)
      (sparsifyDynContract impl mMax w vCapH eCapH vCapJ eCapJ vCapOut eCapOut H' J emb) := by
  refine meetsContract_of_runs
    (hpSpDyn.get (i := gtIdxSparsifyDyn) (by simp [sparsifyDynProcs, gtIdxSparsifyDyn]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨hPtr, jPtr, mEmbPtr, scratchPtr, guestBase,
    rfl, hw16, hJn1, hvCap_ltw, heCap_ltw, hgB1, hw'_le, hMemBnd,
    hH_ltgb, hJ_ltgb, hME_ltgb, hScr_le_gb,
    hdisjH, hdisjJ, hdisjME, hdisjW, hzMem, hDynH, hDynJ, hemb, hmEmb,
    hJm_le, hLen_pos, hvOut_cap, heOut_cap, hWalks_ltgb⟩
  let rawEsLen := (collectRawEsFun (Spanner.vertsOf J.E) emb).length
  let sLen := max (gtFwdDynScratchLen J.n J.m rawEsLen) (gtRevDynScratchLen J.n J.m)
  let x := canonSparsifyInput H' J emb
  let w' := wordSize impl.cw x
  let walkBnd := J.m * (1 + 2 * Nat.ceil (impl.γ_ℓ mMax))
  have hlt_hP : hPtr < 2 ^ w := hargs hPtr (by simp)
  have hlt_jP : jPtr < 2 ^ w := hargs jPtr (by simp)
  have hlt_mEP : mEmbPtr < 2 ^ w := hargs mEmbPtr (by simp)
  have hlt_scrP : scratchPtr < 2 ^ w := hargs scratchPtr (by simp)
  have hlt_gB : guestBase < 2 ^ w := hargs guestBase (by simp)
  have hH' : H'.IsValid := hDynH.1
  have hJ : J.IsValid := hDynJ.1
  have hV : CanonicalSparsifyValid impl H' J emb := ⟨hJn1, hH', hJ, hLen_pos, hemb⟩
  have hcw1 : 1 ≤ impl.cw := by have := impl.hcw; omega
  have hpow := pow_lt_two_pow_wordSize hcw1 x
  have hx_lt_w' : x.length < 2 ^ w' := by
    have h1 : x.length < x.length + x.foldr max 0 + 2 := by omega
    have h2 : x.length + x.foldr max 0 + 2 ≤ (x.length + x.foldr max 0 + 2) ^ impl.cw := by
      simpa using Nat.pow_le_pow_right (by omega) hcw1
    exact lt_trans (lt_of_lt_of_le h1 h2) hpow
  have h2pow : 2 ^ (w' + 1) = 2 * 2 ^ w' := by rw [pow_succ]; ring
  have hMemBnd' : guestBase + 2 * 2 ^ w' + 2 + 3 * J.m + dynGraphSize vCapOut eCapOut + eCapOut +
      walkBnd < 2 ^ w := by
    have h1 : 2 ^ (wordSize impl.cw (canonSparsifyInput H' J emb) + 1) = 2 * 2 ^ w' := h2pow
    dsimp only [walkBnd]; rw [← h1]; exact hMemBnd
  have hW'_le2 : 2 ^ w' ≤ 2 ^ (w' + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ _)
  have hx_ltw : x.length < 2 ^ w := lt_of_lt_of_le hx_lt_w' (Nat.pow_le_pow_right (by omega) hw'_le)
  have hW'_ltw : 2 ^ w' < 2 ^ w := by omega
  -- Step 1: Call `gtForwardDynStmt`
  have hFwd_mc : MeetsContract w p (bFwd + gtIdxForwardDyn)
      (gtForwardDynContract w vCapH eCapH vCapJ eCapJ H' J emb) :=
    gtForwardDyn_meetsContract hpFwd hpEmit hpOps hpGT hpSort
  let st0 := startState [hPtr, jPtr, mEmbPtr, vCapOut, eCapOut, scratchPtr, guestBase] mem pos
  have hargs1 : evalArgs w st0 [.reg 0, .reg 1, .reg 2, .reg 5, .reg 6] =
      some [hPtr, jPtr, mEmbPtr, scratchPtr, guestBase] := by
    simp [evalArgs, Expr.eval, st0, startState]
  have hvs1_lt : ∀ v ∈ [hPtr, jPtr, mEmbPtr, scratchPtr, guestBase], v < 2 ^ w := by
    intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hFwd_pre : (gtForwardDynContract w vCapH eCapH vCapJ eCapJ H' J emb).pre
      [hPtr, jPtr, mEmbPtr, scratchPtr, guestBase] mem := by
    refine ⟨hPtr, jPtr, mEmbPtr, scratchPtr, guestBase, rfl, hw16,
      by omega, by omega, by omega, by omega, ?_, Or.inl (by omega), ?_, ?_, ?_, ?_,
      hDynH, hDynJ, hemb, hmEmb, fun e he => ⟨?_, ?_⟩⟩
    · change guestBase + x.length < 2 ^ w; omega
    · intro i hi
      refine ⟨?_, Or.inl (by exact lt_of_lt_of_le (Nat.add_lt_add_left hi hPtr) (by omega))⟩
      rcases hdisjH i hi with h | h <;> [left; right] <;> omega
    · intro i hi
      refine ⟨?_, Or.inl (by exact lt_of_lt_of_le (Nat.add_lt_add_left hi jPtr) (by omega))⟩
      rcases hdisjJ i hi with h | h <;> [left; right] <;> omega
    · intro e he
      have he_c : e < eCapH := (hmEmb e he).1
      refine ⟨?_, Or.inl (by omega)⟩
      rcases hdisjME e he with h | h <;> [left; right] <;> omega
    · intro e he k hk
      refine ⟨?_, Or.inl (by exact lt_trans (Nat.add_lt_add_left hk _) (hWalks_ltgb e he))⟩
      rcases hdisjW e he k hk with h | h <;> [left; right] <;> omega
    · have hwlt := hWalks_ltgb e he
      have hmle := mWalkEncode_length (emb e)
      omega
    · exact lt_of_lt_of_le (hWalks_ltgb e he) (by omega)
  have ⟨body1, hbody1, o1, st1, c1, hRun1, hPost1, hCost1⟩ :=
    hFwd_mc [hPtr, jPtr, mEmbPtr, scratchPtr, guestBase] mem pos ω hvs1_lt hFwd_pre
  let stA := { st1 with regs := Function.update st0.regs 7 o1.value }
  have hCall1_runs : Runs w p ω
      (.call 7 (bFwd + gtIdxForwardDyn) [.reg 0, .reg 1, .reg 2, .reg 5, .reg 6])
      st0 .normal stA (argsSize [.reg 0, .reg 1, .reg 2, .reg 5, .reg 6] + c1 + 1) := by
    rw [runs_call_iff]
    exact ⟨_, body1, o1, st1, c1, hargs1, hbody1, hRun1, rfl, rfl, rfl⟩
  rcases hPost1 with ⟨_, _, _, _, _, hargs1_eq, hret1, hList1, hfr1⟩
  simp only [List.cons.injEq, and_true] at hargs1_eq
  rcases hargs1_eq with ⟨rfl, rfl, rfl, rfl, rfl⟩
  have ho1_eq : o1.value = x.length := hret1
  have hzA : ZeroFrom stA.mem (guestBase + x.length) := by
    intro addr haddr
    have h1 := hfr1 addr (Or.inr (by dsimp only [sLen, gtFwdDynScratchLen] at *; omega)) (Or.inr haddr)
    rw [h1]
    exact hzMem addr (by omega)
  -- Step 2: Run `computeWordSizeStmt`
  have hCws_nodup : [6, 7, 8, 9, 10, 11, 12].Nodup := by decide
  have hCws_hw : 2 ^ (wordSize impl.cw x + 1) + 2 ≤ 2 ^ w := by
    have : 2 ^ (wordSize impl.cw x + 1) = 2 * 2 ^ w' := h2pow
    omega
  have hCws_hal : guestBase + x.length < 2 ^ w := by omega
  obtain ⟨stB, c2, hRun2, hrB8, hrB9, hmB, _, hrB_other, hCost2⟩ :=
    Link.computeWordSize_runs (w := w) (p := p) (ω := ω) (c := impl.cw)
      (st := stA) hCws_nodup (a := guestBase) (x := x)
      (by simp [stA, st0, Function.update_of_ne, startState])
      (by simp [stA, Function.update_self, ho1_eq])
      hList1 hCws_hal hCws_hw
  -- Step 3: Run relocated guest `Sparsify` via `.call 10 (bGuest + 1) (sparsifyGuestCallArgs R)`
  let R := impl.program.regBound
  have hrB6 : stB.regs 6 = guestBase := by
    rw [hrB_other 6 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [stA, st0, Function.update_of_ne, startState]
  have hrB7 : stB.regs 7 = x.length := by
    rw [hrB_other 7 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [stA, Function.update_self, ho1_eq]
  obtain ⟨vs3, heval3, _, hvs3_R, hvs3_R1, hvs3_ltR⟩ :=
    evalArgs_sparsifyGuestCallArgs (R := R) (w := w) (inLen := x.length) (guestBase := guestBase)
      (W := 2 ^ w') (by omega) hrB6 hrB7 hrB9 hlt_gB hx_ltw hW'_ltw
  have hst3_arg : ∀ r < R, (startState vs3 stB.mem stB.pos).regs r =
      (startState [0, x.length] (initMem x) 0).regs r := by
    intro r hr
    simp only [startState]
    rw [hvs3_ltR r hr]
    rcases r with _ | _ | r <;> rfl
  obtain ⟨body3, o3, st3, c3, cJtilde, kept, embJJtilde, c_Q, hQ0, hp3, hRun3, hc3_le,
    hCostQ, hx_le, ho3_lt, hz3, hProp, hOut3, hJt_eq, hEmb_eq, _, hfr3, _⟩ :=
    canonical_sparsify_relocated_run impl mMax hV hJm_le (hasAt_sparsifyGuestProcs hpGuest) hw'_le hgB1
      (by dsimp only [w'] at *; omega) (by omega)
      (by dsimp only [startState]; change vs3[R]?.getD 0 = guestBase; rw [hvs3_R]; rfl)
      (by dsimp only [startState]; change vs3[R + 1]?.getD 0 = 2 ^ w'; rw [hvs3_R1]; rfl)
      hst3_arg
      (by rwa [hmB])
      (by rwa [hmB])
  let stC := { st3 with regs := Function.update stB.regs 10 o3.value }
  have hCall3_runs : Runs w p ω (.call 10 (bGuest + 1) (sparsifyGuestCallArgs R)) stB .normal stC
      (argsSize (sparsifyGuestCallArgs R) + c3 + 1) := by
    rw [runs_call_iff]
    exact ⟨vs3, relocStmt R bGuest body3, o3, st3, c3, heval3, hp3, hRun3, rfl, rfl, rfl⟩
  -- Step 4: Set up registers `11..14` and call `gtReverseDynStmt`
  have hrC_mem : ∀ addr < guestBase, stC.mem addr = stA.mem addr := fun addr haddr => by
    have := hfr3 addr (Or.inl haddr)
    simpa [stC, hmB, startState] using this
  have hfrCA : ∀ addr, (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) → addr < guestBase →
      stC.mem addr = mem addr := fun addr hscr hgb => by
    rw [hrC_mem addr hgb]
    refine hfr1 addr ?_ (Or.inl hgb)
    dsimp only [sLen, rawEsLen] at hscr
    rcases hscr with h | h <;> [left; right] <;> omega
  have hDynJ_C : DynGraphAt stC.mem jPtr vCapJ eCapJ J := by
    refine hDynJ.of_agree fun addr ha1 ha2 => ?_
    have hdj := hdisjJ (addr - jPtr) (Nat.sub_lt_left_of_lt_add ha1 ha2)
    rw [Nat.add_sub_cancel' ha1] at hdj
    have hdj' : addr < scratchPtr ∨ scratchPtr + sLen ≤ addr := by
      dsimp only [sLen, rawEsLen]; exact hdj
    exact hfrCA addr hdj' (lt_trans ha2 hJ_ltgb)
  have hrC1 : stC.regs 1 = jPtr := by
    simp only [stC, Function.update_of_ne (by decide : (1 : ℕ) ≠ 10)]
    rw [hrB_other 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [stA, Function.update_of_ne, st0, startState]
  have hrC3 : stC.regs 3 = vCapOut := by
    simp only [stC, Function.update_of_ne (by decide : (3 : ℕ) ≠ 10)]
    rw [hrB_other 3 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [stA, Function.update_of_ne, st0, startState]
  have hrC4 : stC.regs 4 = eCapOut := by
    simp only [stC, Function.update_of_ne (by decide : (4 : ℕ) ≠ 10)]
    rw [hrB_other 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [stA, Function.update_of_ne, st0, startState]
  have hrC5 : stC.regs 5 = scratchPtr := by
    simp only [stC, Function.update_of_ne (by decide : (5 : ℕ) ≠ 10)]
    rw [hrB_other 5 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [stA, Function.update_of_ne, st0, startState]
  have hrC6 : stC.regs 6 = guestBase := by
    simp [stC, Function.update_of_ne, hrB6]
  have hrC7 : stC.regs 7 = x.length := by
    simp [stC, Function.update_of_ne, hrB7]
  let triplesBufPtr := guestBase + o3.value
  let jtildeDynPtr := triplesBufPtr + 3 * J.m
  let mEmbOutPtr := jtildeDynPtr + dynGraphSize vCapOut eCapOut
  let walkBufPtr := mEmbOutPtr + eCapOut
  have htr_lt_gbW : triplesBufPtr < guestBase + 2 ^ w' := by
    dsimp only [triplesBufPtr, w', x]; omega
  have hwb_ltw : walkBufPtr < 2 ^ w := by
    dsimp only [walkBufPtr, mEmbOutPtr, jtildeDynPtr, triplesBufPtr]
    have : o3.value < 2 * 2 ^ w' := by
      have := lt_of_lt_of_le ho3_lt hW'_le2
      rwa [h2pow] at this
    omega
  have hmJ_mem : stC.mem (jPtr + dgMOff) = J.m := hDynJ_C.2.2.2.2.2.2.1
  have hjpdg : jPtr + dgMOff < 2 ^ w := by
    have : dgMOff < dynGraphSize vCapJ eCapJ := by simp [dgMOff, dynGraphSize]; omega
    have : jPtr + dgMOff < guestBase := lt_of_lt_of_le (Nat.add_lt_add_left this _) (le_of_lt hJ_ltgb)
    omega
  obtain ⟨o4_setup, stD, c4_setup, hRun4_setup, hstD_post, hCost4_setup⟩ :=
    spHostSetupRev_triple (p := p) (w := w)
      (jPtr := jPtr) (vCapOut := vCapOut) (eCapOut := eCapOut)
      (scratchPtr := scratchPtr) (guestBase := guestBase) (inLen := x.length)
      (retHeap := o3.value) (mJ := J.m)
      hw16 hmJ_mem hjpdg
      (by dsimp only [walkBufPtr, mEmbOutPtr, jtildeDynPtr, triplesBufPtr] at hwb_ltw; omega)
      (by dsimp only [walkBufPtr, mEmbOutPtr, jtildeDynPtr, triplesBufPtr] at hwb_ltw; omega)
      (by dsimp only [walkBufPtr, mEmbOutPtr, jtildeDynPtr, triplesBufPtr] at hwb_ltw; omega)
      hwb_ltw stC ω
      ⟨rfl, hrC1, hrC3, hrC4, hrC5, hrC6, hrC7, by simp [stC, Function.update_self]⟩
  have ho4s : o4_setup = .normal := by
    cases o4_setup with
    | normal => rfl
    | returned _ => exact False.elim hstD_post
  subst ho4s
  rcases hstD_post with ⟨hmD, hrD1, hrD3, hrD4, hrD5, hrD6, hrD7, _, hrD11, hrD12, hrD13, hrD14⟩
  -- Check `gtReverseDyn` precondition and call `gtReverseDynStmt`
  have hRev_mc := gtReverseDyn_meetsContract
    (w := w) (vCapJ := vCapJ) (eCapJ := eCapJ) (vCapOut := vCapOut) (eCapOut := eCapOut)
    (J := J) (retHeap := o3.value) (cJtilde := cJtilde) (kept := kept) (embJJtilde := embJJtilde)
    hpRevDyn hpRevCore hpRevPrim hpBatch hpEdge hpOps hpGT hpSort
  have htr_ltw : triplesBufPtr < 2 ^ w := by
    dsimp [walkBufPtr, mEmbOutPtr, jtildeDynPtr, triplesBufPtr] at hwb_ltw; omega
  have hjtd_ltw : jtildeDynPtr < 2 ^ w := by
    dsimp [walkBufPtr, mEmbOutPtr, jtildeDynPtr, triplesBufPtr] at hwb_ltw; omega
  have hmEP_ltw : mEmbOutPtr < 2 ^ w := by
    dsimp [walkBufPtr, mEmbOutPtr, jtildeDynPtr, triplesBufPtr] at hwb_ltw; omega
  let call4Args : List Expr :=
    [.reg 1, .reg 6, .reg 7, .reg 3, .reg 4, .reg 5, .reg 11, .reg 12, .reg 13, .reg 14]
  let args4 := [jPtr, guestBase, x.length, vCapOut, eCapOut, scratchPtr,
    triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr]
  have hargs4 : evalArgs w stD call4Args = some args4 := by
    simp [call4Args, args4, evalArgs, Expr.eval, hrD1, hrD6, hrD7, hrD3, hrD4, hrD5,
      hrD11, hrD12, hrD13, hrD14, triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr]
  have hargs4_lt : ∀ v ∈ args4, v < 2 ^ w := by
    intro v hv; simp only [args4, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hkept_nodup : kept.Nodup := hProp.1
  have hkept_lt : ∀ k ∈ kept, k < J.m := fun k hk => (toCitedJ_m J) ▸ hProp.2.1 k hk
  have hkept_len_le : kept.length ≤ J.m := by
    calc kept.length = kept.toFinset.card := (List.toFinset_card_of_nodup hkept_nodup).symm
      _ ≤ (Finset.range J.m).card := Finset.card_le_card fun k hk =>
        Finset.mem_range.mpr (hkept_lt k (List.mem_toFinset.mp hk))
      _ = J.m := Finset.card_range J.m
  let cJ := toCitedJ J
  have hcJn_eq : cJ.n = J.n := by dsimp [cJ, toCitedJ]; exact vertsOf_length J.V
  have hcJm_eq : cJ.m = J.m := toCitedJ_m J
  have hEachEmb_le : ∀ j < J.m, (embJJtilde j).edges.length ≤ Nat.ceil (impl.γ_ℓ mMax) := by
    intro j hj
    have hj_c : j < cJ.m := hcJm_eq.symm ▸ hj
    have hlen_nat : (embJJtilde j).edges.length ≤ Spanner.length cJ embJJtilde := by
      unfold Spanner.length
      exact (Finset.le_fold_max _).mpr (Or.inr ⟨j, Finset.mem_range.mpr hj_c, le_rfl⟩)
    have hlen_j : ((embJJtilde j).edges.length : ℝ) ≤ (Spanner.length cJ embJJtilde : ℝ) := by
      exact_mod_cast hlen_nat
    exact nat_le_ceil_of_le_real (le_trans hlen_j hProp.2.2.2.2.2.2.2.1)
  have hSumEmb_le : ((List.range J.m).map fun j => (embJJtilde j).edges.length).sum ≤
      J.m * Nat.ceil (impl.γ_ℓ mMax) := by
    have hgen : ∀ k ≤ J.m,
        ((List.range k).map fun j => (embJJtilde j).edges.length).sum ≤ k * Nat.ceil (impl.γ_ℓ mMax) := by
      intro k hk
      induction k with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
        have h1 := ih (Nat.le_of_succ_le hk)
        have h2 := hEachEmb_le m (Nat.lt_of_succ_le hk)
        rw [Nat.succ_mul]
        omega
    exact hgen J.m le_rfl
  let jEs := Spanner.vertsOf J.E
  have hjEs_len : jEs.length = J.m := Spanner.vertsOf_length J.E
  let totWalk := citedDecPrefLen jEs cJtilde kept embJJtilde jEs.length
  have hTotWalk_le : totWalk ≤ walkBnd := by
    have h1 := citedDecPrefLen_le_walkSum jEs cJtilde kept embJJtilde jEs.length
    have htot_eq : totWalk = citedDecPrefLen jEs cJtilde kept embJJtilde J.m := by
      dsimp only [totWalk]; rw [hjEs_len]
    rw [hjEs_len] at h1
    calc totWalk ≤ J.m + 2 * ((List.range J.m).map fun j => (embJJtilde j).edges.length).sum := htot_eq ▸ h1
      _ ≤ J.m + 2 * (J.m * Nat.ceil (impl.γ_ℓ mMax)) := by omega
      _ = walkBnd := by dsimp [walkBnd]; ring
  have hTot_ub : walkBufPtr + totWalk ≤ guestBase + 2 ^ (w' + 1) + 2 + 3 * J.m +
      dynGraphSize vCapOut eCapOut + eCapOut + walkBnd := by
    have ho3_2 : o3.value < 2 * 2 ^ w' := by
      have := lt_of_lt_of_le ho3_lt hW'_le2
      rwa [h2pow] at this
    dsimp only [walkBufPtr, mEmbOutPtr, jtildeDynPtr, triplesBufPtr]
    omega
  have hTot_ltw : walkBufPtr + totWalk < 2 ^ w := by
    have hMemBnd'' : guestBase + 2 ^ (w' + 1) + 2 + 3 * J.m + dynGraphSize vCapOut eCapOut +
        eCapOut + walkBnd < 2 ^ w := by
      rwa [h2pow]
    exact lt_of_le_of_lt hTot_ub hMemBnd''
  have hcJn_w' : cJ.n < 2 ^ w' := by
    have hx := listAt_initMem x
    have hxLen := canonSparsifyInput_length H' J emb
    let hcH := toCitedH H' J emb
    have hGJ := (canonSparsifyInput_decomp hx).2.2.2.2.1
    rw [zero_add] at hGJ
    have hpJ_lt : 3 + hcH.encode.length < x.length := by
      dsimp only [hcH]
      rw [hxLen, graph_encode_length (toCitedH H' J emb)]
      have hcH_m : (toCitedH H' J emb).m = (toCitedH H' J emb).edges.length := rfl
      omega
    have h1 := hGJ 0 (by simp [Cited.Graph.encode])
    have hxJ : initMem x (3 + hcH.encode.length) = x[3 + hcH.encode.length]'hpJ_lt :=
      List.getD_eq_getElem x 0 hpJ_lt
    have hcJn_mem : cJ.n ∈ x := by
      have : x[3 + hcH.encode.length]'hpJ_lt = cJ.n := by
        dsimp only [hcH, cJ] at hxJ h1 ⊢
        exact hxJ.symm.trans (by simpa [Cited.Graph.encode] using h1)
      rw [← this]; exact List.getElem_mem hpJ_lt
    have hle_max : ∀ {a : ℕ} {l : List ℕ}, a ∈ l → a ≤ l.foldr max 0 := by
      intro a l hl
      induction l with
      | nil => simp at hl
      | cons y ys ih =>
        rcases List.mem_cons.mp hl with rfl | hys
        · exact Nat.le_max_left _ _
        · exact le_trans (ih hys) (Nat.le_max_right _ _)
    have hle_m := hle_max hcJn_mem
    have hlt1 : cJ.n < x.length + x.foldr max 0 + 2 := by omega
    have hle2 : x.length + x.foldr max 0 + 2 ≤ (x.length + x.foldr max 0 + 2) ^ impl.cw := by
      simpa using Nat.pow_le_pow_right (by omega) hcw1
    exact lt_trans (lt_of_lt_of_le hlt1 hle2) hpow
  have hcJm_w' : cJ.m < 2 ^ w' := by
    rw [hcJm_eq]
    exact lt_of_le_of_lt (by rw [canonSparsifyInput_length]; omega) hx_lt_w'
  have hRev_bnds_w' := revDyn_bounds_of_citedSparsifyProp hProp (hmD ▸ hOut3)
    (toCitedJ_isValid hJ) hcJn_w' hcJm_w' ho3_lt
  have hPow_le : 2 ^ w' ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw'_le
  have hcJall_w : cJtilde.encode.all (· < 2 ^ w) = true := by
    rw [List.all_eq_true]
    have hall' := List.all_eq_true.mp hRev_bnds_w'.1
    intro z hz
    have h1 := decide_eq_true_eq.mp (hall' z hz)
    exact decide_eq_true_eq.mpr (lt_of_lt_of_le h1 hPow_le)
  have hcJw_w : ∀ i < cJtilde.m, (cJtilde.edges[i]!).1 < 2 ^ w ∧ (cJtilde.edges[i]!).2 < 2 ^ w :=
    fun i hi => ⟨lt_of_lt_of_le (hRev_bnds_w'.2.1 i hi).1 hPow_le,
      lt_of_lt_of_le (hRev_bnds_w'.2.1 i hi).2 hPow_le⟩
  have hembWalks_w : ∀ j < J.m,
      (embJJtilde j).verts.length < 2 ^ w ∧ (embJJtilde j).edges.length < 2 ^ w ∧
      (∀ c ∈ (embJJtilde j).edges, c < cJtilde.m ∧ c < kept.length) ∧
      (∀ u ∈ (embJJtilde j).verts, u < 2 ^ w) := by
    intro j hj
    have h := hRev_bnds_w'.2.2.2 j (hcJm_eq.symm ▸ hj)
    exact ⟨lt_of_lt_of_le h.1 hPow_le, lt_of_lt_of_le h.2.1 hPow_le, h.2.2.1,
      fun u hu => lt_of_lt_of_le (h.2.2.2 u hu) hPow_le⟩
  have hDynJ_D : DynGraphAt stD.mem jPtr vCapJ eCapJ J := by rwa [hmD]
  have hzD : ZeroFrom stD.mem triplesBufPtr := fun addr ha => by
    rw [hmD]; exact hz3 addr (by dsimp [triplesBufPtr] at ha; omega)
  have hOutD : SparsifyOutRelocAt stD.mem guestBase x.length o3.value J.m cJtilde kept embJJtilde := by
    rw [hmD]
    change SparsifyOutRelocAt st3.mem guestBase (canonSparsifyInput H' J emb).length o3.value J.m cJtilde kept embJJtilde
    simpa only [toCitedJ_m J] using hOut3
  have hScr_le_rev : scratchPtr + gtRevDynScratchLen J.n J.m ≤ guestBase :=
    le_trans (Nat.add_le_add_left (le_max_right _ _) scratchPtr) hScr_le_gb
  have hRev_pre : (gtReverseDynContract w vCapJ eCapJ vCapOut eCapOut J o3.value cJtilde kept embJJtilde).pre
      args4 stD.mem := by
    refine ⟨jPtr, guestBase, x.length, scratchPtr, triplesBufPtr, jtildeDynPtr, mEmbOutPtr, walkBufPtr,
      rfl, hw16, hvCap_ltw, heCap_ltw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hzD, hDynJ_D, hvOut_cap, heOut_cap, hkept_nodup, hkept_lt, hcJall_w, hcJw_w,
      hRev_bnds_w'.2.2.1, hembWalks_w, hOutD⟩
    · exact lt_of_lt_of_le hJ_ltgb (le_of_lt hlt_gB)
    · exact htr_ltw
    · dsimp only [triplesBufPtr]; omega
    · dsimp only [triplesBufPtr]; omega
    · dsimp only [jtildeDynPtr, triplesBufPtr]; omega
    · dsimp only [mEmbOutPtr]; exact le_rfl
    · dsimp only [walkBufPtr]; exact le_rfl
    · exact hTot_ltw
    · intro i hi
      rcases hdisjJ i hi with h | h <;> [left; right]
      · exact h
      · have hs_le : scratchPtr + gtRevDynScratchLen J.n J.m ≤ scratchPtr + sLen :=
          Nat.add_le_add_left (le_max_right _ _) scratchPtr
        dsimp only [sLen, rawEsLen] at hs_le
        exact le_trans hs_le h
    · intro i hi
      right; omega
  have ⟨body4, hbody4, o4, st4, c4, hRun4, hPost4, hCost4⟩ :=
    hRev_mc args4 stD.mem stD.pos ω hargs4_lt hRev_pre
  let stE := { st4 with regs := Function.update stD.regs 15 o4.value }
  have hCall4_runs : Runs w p ω (.call 15 (bRevDyn + gtIdxReverseDyn) call4Args) stD .normal stE
      (argsSize call4Args + c4 + 1) := by
    rw [runs_call_iff]
    exact ⟨args4, body4, o4, st4, c4, hargs4, hbody4, hRun4, rfl, rfl, rfl⟩
  rcases hPost4 with ⟨jPtr4, gb4, spOut4, scr4, tr4, jtd4, me4, wb4,
    hargs4_eq, hret4, hDynOut, hmEmbOut, hWalkBounds, hzE, hfr4⟩
  simp only [args4, List.cons.injEq] at hargs4_eq
  rcases hargs4_eq with ⟨rfl, rfl, rfl, _, _, rfl, rfl, rfl, rfl, rfl, _⟩
  have hrE5 : stE.regs 5 = scratchPtr := by simp [stE, Function.update_of_ne, hrD5]
  have hrE12 : stE.regs 12 = jtildeDynPtr := by
    simp [stE, Function.update_of_ne, hrD12, jtildeDynPtr, triplesBufPtr]
  have hrE13 : stE.regs 13 = mEmbOutPtr := by
    simp [stE, Function.update_of_ne, hrD13, mEmbOutPtr, jtildeDynPtr, triplesBufPtr]
  have hrE15 : stE.regs 15 = o4.value := by simp [stE, Function.update_self]
  have ho4_eq : o4.value = walkBufPtr + totWalk := hret4
  have hsLen_ge2 : scratchPtr + 1 < guestBase := by
    have : 2 ≤ gtRevDynScratchLen J.n J.m := by simp [gtRevDynScratchLen]; omega
    have : 2 ≤ sLen := le_trans this (le_max_right _ _)
    omega
  have hsc0_lt_gb : scratchPtr + 1 < guestBase := hsLen_ge2
  have hgb_le_tr : guestBase ≤ triplesBufPtr := by dsimp only [triplesBufPtr]; omega
  have htr_le_jtd : triplesBufPtr ≤ jtildeDynPtr := by dsimp only [jtildeDynPtr]; omega
  have hjtd_le_mep : jtildeDynPtr ≤ mEmbOutPtr := by dsimp only [mEmbOutPtr]; omega
  have hmep_le_wb : mEmbOutPtr ≤ walkBufPtr := by dsimp only [walkBufPtr]; omega
  have hscr_lt_mep : scratchPtr + 1 < mEmbOutPtr := by omega
  have hscr_lt_wb : scratchPtr + 1 < walkBufPtr := by omega
  have hmEmbB_E : MEmbBounded stE.mem mEmbOutPtr J.E eCapOut (citedEmbToMGraph J cJtilde kept embJJtilde)
      mEmbOutPtr (walkBufPtr + totWalk) := by
    refine ⟨le_rfl, by dsimp [walkBufPtr]; omega, fun e he => ?_⟩
    have hec := (hmEmbOut e he).1
    have hj_lt : jEs.idxOf e < jEs.length := List.idxOf_lt_length_iff.mpr (Spanner.mem_vertsOf.mpr he)
    have hwb := hWalkBounds (jEs.idxOf e) hj_lt
    have he_eq : jEs[jEs.idxOf e]'hj_lt = e := List.getElem_idxOf hj_lt
    rw [he_eq] at hwb
    have hwalk_eq : citedDecWalk jEs cJtilde kept embJJtilde (jEs.idxOf e) =
        citedEmbToMGraph J cJtilde kept embJJtilde e := by
      simp [citedEmbToMGraph, he, citedDecWalk, jEs]
    rw [hwalk_eq] at hwb
    exact ⟨hec, le_trans hmep_le_wb hwb.1, hwb.2, (hmEmbOut e he).2⟩
  -- Final stores & ret
  have hw2 : 1 < 2 ^ w := by omega
  let stF := { stE with mem := Function.update stE.mem scratchPtr jtildeDynPtr }
  have hStore1 : Runs w p ω (.store (.reg 5) (.reg 12)) stE .normal stF 3 := by
    rw [runs_store_iff]
    exact ⟨scratchPtr, jtildeDynPtr, by simp [Expr.eval, hrE5],
      by simp [Expr.eval, hrE12], rfl, rfl, by simp [Expr.size]⟩
  have hscr1_ltw : scratchPtr + 1 < 2 ^ w := by omega
  have hrF5 : stF.regs 5 = scratchPtr := hrE5
  have hrF13 : stF.regs 13 = mEmbOutPtr := hrE13
  have hrF15 : stF.regs 15 = o4.value := hrE15
  let stG := { stF with mem := Function.update stF.mem (scratchPtr + 1) mEmbOutPtr }
  have hStore2 : Runs w p ω (.store (.bin .add (.reg 5) (.const 1)) (.reg 13)) stF .normal stG 5 := by
    rw [runs_store_iff]
    exact ⟨scratchPtr + 1, mEmbOutPtr,
      by simp [Expr.eval, hrF5, hw2, hscr1_ltw],
      by simp [Expr.eval, hrF13], rfl, rfl, by simp [Expr.size]⟩
  have hRet : Runs w p ω (.ret (.reg 15)) stG (.returned o4.value) stG 2 := by
    rw [runs_ret_iff]
    exact ⟨o4.value, by simp [Expr.eval, stG, hrF15], rfl, rfl, by simp [Expr.size]⟩
  have hstG_jtd : stG.mem scratchPtr = jtildeDynPtr := by
    simp [stG, stF, Function.update_self]
  have hstG_mep : stG.mem (scratchPtr + 1) = mEmbOutPtr := by
    simp [stG, Function.update_self]
  have hDynOut_G : DynGraphAt stG.mem jtildeDynPtr vCapOut eCapOut (canonicalSparsify impl H' J emb).Jtilde := by
    rw [← hJt_eq]
    refine hDynOut.of_agree fun addr ha1 _ => ?_
    have hscr_lt_jtd : scratchPtr + 1 < jtildeDynPtr := lt_of_lt_of_le hsc0_lt_gb (le_trans hgb_le_tr htr_le_jtd)
    have hne1 : addr ≠ scratchPtr := Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_of_succ_lt hscr_lt_jtd) ha1)
    have hne2 : addr ≠ scratchPtr + 1 := Nat.ne_of_gt (lt_of_lt_of_le hscr_lt_jtd ha1)
    simp only [stG, stF, Function.update_of_ne hne2, Function.update_of_ne hne1]
    rfl
  have hmEmbB_G : MEmbBounded stG.mem mEmbOutPtr J.E eCapOut (canonicalSparsify impl H' J emb).emb
      mEmbOutPtr (walkBufPtr + totWalk) := by
    rw [← hEmb_eq]
    have hmEmbB_F : MEmbBounded stF.mem mEmbOutPtr J.E eCapOut (citedEmbToMGraph J cJtilde kept embJJtilde)
        mEmbOutPtr (walkBufPtr + totWalk) :=
      mEmbBounded_update_outside hmEmbB_E (Nat.lt_of_succ_lt hscr_lt_mep)
    exact mEmbBounded_update_outside hmEmbB_F hscr_lt_mep
  have hmEmbLo_G : ∀ e ∈ J.E, mEmbOutPtr + eCapOut ≤ stG.mem (mEmbOutPtr + e) := fun e he => by
    have hec := (hmEmbOut e he).1
    have hj_lt : jEs.idxOf e < jEs.length := List.idxOf_lt_length_iff.mpr (Spanner.mem_vertsOf.mpr he)
    have hwb := hWalkBounds (jEs.idxOf e) hj_lt
    have he_eq : jEs[jEs.idxOf e]'hj_lt = e := List.getElem_idxOf hj_lt
    rw [he_eq] at hwb
    have hne1 : mEmbOutPtr + e ≠ scratchPtr := by omega
    have hne2 : mEmbOutPtr + e ≠ scratchPtr + 1 := by omega
    simp only [stG, stF, Function.update_of_ne hne2, Function.update_of_ne hne1]
    change walkBufPtr ≤ stE.mem (mEmbOutPtr + e)
    exact hwb.1
  have hzG : ZeroFrom stG.mem (walkBufPtr + totWalk) := by
    intro addr haddr
    have hlt2 : scratchPtr + 1 < addr := lt_of_lt_of_le hscr_lt_wb (le_trans (Nat.le_add_right _ _) haddr)
    have hne1 : addr ≠ scratchPtr := Nat.ne_of_gt (Nat.lt_of_succ_lt hlt2)
    have hne2 : addr ≠ scratchPtr + 1 := Nat.ne_of_gt hlt2
    simp only [stG, stF, Function.update_of_ne hne2, Function.update_of_ne hne1]
    exact hzE addr haddr
  have hfrG : ∀ addr, (addr < scratchPtr ∨ scratchPtr + sLen ≤ addr) → addr < guestBase →
      stG.mem addr = mem addr := fun addr hscr hgb => by
    have hscr_rev : addr < scratchPtr ∨ scratchPtr + gtRevDynScratchLen J.n J.m ≤ addr := by
      rcases hscr with h | h <;> [left; right]
      · exact h
      · have hs : scratchPtr + gtRevDynScratchLen J.n J.m ≤ scratchPtr + sLen :=
          Nat.add_le_add_left (le_max_right _ _) scratchPtr
        exact le_trans hs h
    have hgt2 : 2 ≤ sLen := by
      have : 2 ≤ gtRevDynScratchLen J.n J.m := by simp [gtRevDynScratchLen]; omega
      exact le_trans this (le_max_right _ _)
    have hne1 : addr ≠ scratchPtr := by rcases hscr with h | h <;> omega
    have hne2 : addr ≠ scratchPtr + 1 := by rcases hscr with h | h <;> omega
    simp only [stG, stF, Function.update_of_ne hne2, Function.update_of_ne hne1]
    change st4.mem addr = mem addr
    have hlt_tr : addr < triplesBufPtr := lt_of_lt_of_le hgb hgb_le_tr
    rw [hfr4 addr hscr_rev hlt_tr, hmD, hfrCA addr hscr hgb]
  have hTotalRun : ∃ cTot,
      Runs w p ω (sparsifyDynStmt R impl.cw bFwd bRevDyn bGuest) st0 (.returned o4.value) stG cTot ∧
      cTot = c1 + c2 + c3 + c4_setup + c4 + R + 37 := by
    let h := runs_seq_of_runs hCall1_runs
      (runs_seq_of_runs hRun2
        (runs_seq_of_runs hCall3_runs
          (runs_seq_of_runs hRun4_setup
            (runs_seq_of_runs hCall4_runs
              (runs_seq_of_runs hStore1
                (runs_seq_of_runs hStore2 hRet))))))
    refine ⟨_, h, ?_⟩
    have hArgs1 : argsSize [.reg 0, .reg 1, .reg 2, .reg 5, .reg 6] = 5 := by simp [argsSize, Expr.size]
    have hArgs3 : argsSize (sparsifyGuestCallArgs R) = R + 2 := argsSize_sparsifyGuestCallArgs R
    have hArgs4 : argsSize call4Args = 10 := by simp [call4Args, argsSize, Expr.size]
    rw [hArgs1, hArgs3, hArgs4]
    omega
  rcases hTotalRun with ⟨cTot, hRunTotal, hcTot_eq⟩
  have ho4_ret : (Outcome.returned o4.value).value = walkBufPtr + totWalk := ho4_eq
  refine ⟨.returned o4.value, stG, cTot, hRunTotal, ?_, ?_⟩
  · refine ⟨hPtr, jPtr, mEmbPtr, scratchPtr, guestBase, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfrG⟩
    · rw [hstG_jtd]; exact le_trans hgb_le_tr htr_le_jtd
    · rw [hstG_jtd, hstG_mep]
    · rw [hstG_mep, ho4_ret]; dsimp only [walkBufPtr]; omega
    · rw [ho4_ret]; exact hTot_ltw
    · rw [ho4_ret]; exact hTot_ub
    · rwa [hstG_jtd]
    · rw [hstG_mep, ho4_ret]; exact hmEmbB_G
    · rw [hstG_mep]; exact hmEmbLo_G
    · rw [ho4_ret]; exact hzG
  · dsimp only [sparsifyDynContract]
    have hc1_bnd : c1 ≤
        1430 * (J.n + J.m + (collectRawEsFun (vertsOf J.E) emb).length) *
          (Nat.log 2 (J.n + 2 * (collectRawEsFun (vertsOf J.E) emb).length + J.m + 2) + 1) +
        1250 * (J.n + J.m + (collectRawEsFun (vertsOf J.E) emb).length) + 1500 := hCost1
    have hc2_bnd : c2 ≤
        40 * ((canonSparsifyInput H' J emb).length + wordSize impl.cw (canonSparsifyInput H' J emb) + 1) :=
      hCost2
    have hc3_bnd : c3 ≤ (impl.program.regBound + 6) *
        ⌈impl.K_t * (impl.γ_t mMax) *
          (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (emb.length J : ℝ)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t⌉₊ :=
      le_trans hc3_le (Nat.mul_le_mul_left (R + 6) hCostQ)
    have hc4s_bnd : c4_setup ≤ 50 := hCost4_setup
    have hrev_bnd : 250 * J.n * (Nat.log 2 (J.n + 1) + 1) + 250 * J.m * (Nat.log 2 (J.m + 1) + 1) +
        430 * J.n + 500 * J.m + 565 * kept.length +
        250 * ((List.range J.m).map fun j => (embJJtilde j).edges.length).sum + 1000 ≤
        250 * J.n * (Nat.log 2 (J.n + 1) + 1) + 250 * J.m * (Nat.log 2 (J.m + 1) + 1) +
        430 * J.n + 1065 * J.m + 250 * (J.m * Nat.ceil (impl.γ_ℓ mMax)) + 1000 := by
      omega
    have hc4_bnd : c4 ≤ 250 * J.n * (Nat.log 2 (J.n + 1) + 1) + 250 * J.m * (Nat.log 2 (J.m + 1) + 1) +
        430 * J.n + 1065 * J.m + 250 * (J.m * Nat.ceil (impl.γ_ℓ mMax)) + 1000 := le_trans hCost4 hrev_bnd
    have hR_eq : R = impl.program.regBound := rfl
    omega

/-- Useful summary of `collectRawEsFun` length bounded by `J.m * emb.length J`. -/
theorem collectRawEsFun_length_le {J : MGraph} {emb : MinCostFlow.Embedding} :
    (collectRawEsFun (vertsOf J.E) emb).length ≤ J.m * emb.length J :=
  collectRawEsFun_length_le_mul

end

end MinCostFlow.DynSpanner.Program
