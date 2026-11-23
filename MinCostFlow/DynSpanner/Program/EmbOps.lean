module

public import MinCostFlow.DynSpanner.Program.EmbLayouts
public import MinCostFlow.DynSpanner.Program.DynGraphOps
public import MinCostFlow.DynSpanner.Defs
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.List.TakeDrop

/-!
# Walk and embedding Word-RAM operations (`EmbOps`)

Implements and verifies basic `MWalkAt` / `MEmbAt` operations on the Word-RAM machine:
* `mWalkCopyStmt` (`[src, dst]`): copies a walk in `O(P.length + 1)` time.
* `mWalkRevStmt` (`[src, dst]`): reverses a walk `walkRev P` in `O(P.length + 1)` time.
* `mWalkConcatStmt` (`[srcP, srcQ, dst]`): concatenates two walks `P ++ Q` in
  `O(P.length + Q.length + 1)` time.
* `mWalkPrefixStmt` (`[gPtr, uStart, wPtr, SBitPtr, dstPtr]`): executes `prefixWalk H uStart W S`
  in `O(p₁.length + 1)` time using the `0/1` indicator array at `SBitPtr` and calls to
  `dgIdxGetTail` / `dgIdxGetHead`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

def embIdxWalkCopy : ℕ := 0
def embIdxWalkRev : ℕ := 1
def embIdxWalkConcat : ℕ := 2
def embIdxWalkPrefix : ℕ := 3

/-- Copy a walk (`[src, dst]`) to `dst`, returning `dst + 2 * len + 1`. -/
def mWalkCopyStmt : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .store (.reg 1) (.reg 2) ;;
  forRange 3 (.const 0) (.reg 2)
    (.assign 4 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 3))) ;;
     .assign 5 (.load (.bin .add (.reg 0) (.reg 4))) ;;
     .assign 6 (.load (.bin .add (.bin .add (.reg 0) (.reg 4)) (.const 1))) ;;
     .store (.bin .add (.reg 1) (.reg 4)) (.reg 5) ;;
     .store (.bin .add (.bin .add (.reg 1) (.reg 4)) (.const 1)) (.reg 6)) ;;
  .ret (.bin .add (.reg 1) (.bin .add (.bin .mul (.const 2) (.reg 2)) (.const 1)))

/-- Reverse a walk (`[src, dst]`) as `walkRev P`, returning `dst + 2 * len + 1`. -/
def mWalkRevStmt : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .store (.reg 1) (.reg 2) ;;
  forRange 3 (.const 0) (.reg 2)
    (.assign 4 (.bin .sub (.bin .sub (.reg 2) (.const 1)) (.reg 3)) ;;
     .assign 5 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 4))) ;;
     .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
     .assign 7 (.load (.bin .add (.bin .add (.reg 0) (.reg 5)) (.const 1))) ;;
     .assign 8 (.bin .sub (.const 1) (.reg 7)) ;;
     .assign 9 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 3))) ;;
     .store (.bin .add (.reg 1) (.reg 9)) (.reg 6) ;;
     .store (.bin .add (.bin .add (.reg 1) (.reg 9)) (.const 1)) (.reg 8)) ;;
  .ret (.bin .add (.reg 1) (.bin .add (.bin .mul (.const 2) (.reg 2)) (.const 1)))

/-- Concatenate walks at `srcP` and `srcQ` into `dst` (`[srcP, srcQ, dst]`),
returning `dst + 2 * (lenP + lenQ) + 1`. -/
def mWalkConcatStmt : Stmt :=
  .assign 3 (.load (.reg 0)) ;;
  .assign 4 (.load (.reg 1)) ;;
  .assign 5 (.bin .add (.reg 3) (.reg 4)) ;;
  .store (.reg 2) (.reg 5) ;;
  forRange 6 (.const 0) (.reg 3)
    (.assign 7 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 6))) ;;
     .assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
     .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.reg 7)) (.const 1))) ;;
     .store (.bin .add (.reg 2) (.reg 7)) (.reg 8) ;;
     .store (.bin .add (.bin .add (.reg 2) (.reg 7)) (.const 1)) (.reg 9)) ;;
  forRange 6 (.const 0) (.reg 4)
    (.assign 7 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 6))) ;;
     .assign 8 (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 3))) ;;
     .assign 9 (.load (.bin .add (.reg 1) (.reg 7))) ;;
     .assign 10 (.load (.bin .add (.bin .add (.reg 1) (.reg 7)) (.const 1))) ;;
     .store (.bin .add (.reg 2) (.reg 8)) (.reg 9) ;;
     .store (.bin .add (.bin .add (.reg 2) (.reg 8)) (.const 1)) (.reg 10)) ;;
  .ret (.bin .add (.reg 2) (.bin .add (.bin .mul (.const 2) (.reg 5)) (.const 1)))

/-- Compute `prefixWalk H uStart W S` (`[gPtr, uStart, wPtr, SBitPtr, dstPtr]`), writing
`(prefixWalk H uStart W S).2` in `MWalkAt` format at `dstPtr` and returning
`(prefixWalk H uStart W S).1`. -/
def mWalkPrefixStmt (bOps : ℕ) : Stmt :=
  .assign 5 (.load (.reg 2)) ;;
  .assign 6 (.reg 1) ;;
  .assign 7 (.const 0) ;;
  .assign 8 (.const 0) ;;
  .loop (.bin .eq (.reg 8) (.const 0))
    (.assign 9 (.load (.bin .add (.reg 3) (.reg 6))) ;;
     .cond (.bin .eq (.reg 9) (.const 0))
       (.cond (.bin .lt (.reg 7) (.reg 5))
         (.assign 10 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 7))) ;;
          .assign 11 (.load (.bin .add (.reg 2) (.reg 10))) ;;
          .assign 12 (.load (.bin .add (.bin .add (.reg 2) (.reg 10)) (.const 1))) ;;
          .store (.bin .add (.reg 4) (.reg 10)) (.reg 11) ;;
          .store (.bin .add (.bin .add (.reg 4) (.reg 10)) (.const 1)) (.reg 12) ;;
          .cond (.reg 12)
            (.call 6 (bOps + dgIdxGetHead) [.reg 0, .reg 11])
            (.call 6 (bOps + dgIdxGetTail) [.reg 0, .reg 11]) ;;
          .assign 7 (.bin .add (.reg 7) (.const 1)))
         (.assign 8 (.const 1)))
       (.assign 8 (.const 1))) ;;
  .store (.reg 4) (.reg 7) ;;
  .ret (.reg 6)

def embOpsProcs (bOps : ℕ) : List Stmt :=
  [mWalkCopyStmt, mWalkRevStmt, mWalkConcatStmt, mWalkPrefixStmt bOps]

lemma embOpsProcs_length (bOps : ℕ) : (embOpsProcs bOps).length = 4 := rfl

lemma embOpsProcs_noRand (bOps : ℕ) : ∀ s ∈ embOpsProcs bOps, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Contracts -/

def mWalkCopyContract (w : ℕ) (P : List (ℕ × Bool)) : Contract where
  pre args mem := ∃ src dst,
    args = [src, dst] ∧ 16 ≤ 2 ^ w ∧
    src + (2 * P.length + 1) < 2 ^ w ∧ dst + (2 * P.length + 1) < 2 ^ w ∧
    (src + (2 * P.length + 1) ≤ dst ∨ dst + (2 * P.length + 1) ≤ src) ∧
    (∀ x ∈ P, x.1 < 2 ^ w) ∧
    MWalkAt mem src P
  post args mem ret mem' := ∃ src dst,
    args = [src, dst] ∧ ret = dst + (2 * P.length + 1) ∧
    MWalkAt mem' dst P ∧
    ∀ addr, addr < dst ∨ dst + (2 * P.length + 1) ≤ addr → mem' addr = mem addr
  cost _ _ := 60 * P.length + 30

def mWalkRevContract (w : ℕ) (P : List (ℕ × Bool)) : Contract where
  pre args mem := ∃ src dst,
    args = [src, dst] ∧ 16 ≤ 2 ^ w ∧
    src + (2 * P.length + 1) < 2 ^ w ∧ dst + (2 * P.length + 1) < 2 ^ w ∧
    (src + (2 * P.length + 1) ≤ dst ∨ dst + (2 * P.length + 1) ≤ src) ∧
    (∀ x ∈ P, x.1 < 2 ^ w) ∧
    MWalkAt mem src P
  post args mem ret mem' := ∃ src dst,
    args = [src, dst] ∧ ret = dst + (2 * P.length + 1) ∧
    MWalkAt mem' dst (walkRev P) ∧
    ∀ addr, addr < dst ∨ dst + (2 * P.length + 1) ≤ addr → mem' addr = mem addr
  cost _ _ := 70 * P.length + 30

def mWalkConcatContract (w : ℕ) (P Q : List (ℕ × Bool)) : Contract where
  pre args mem := ∃ srcP srcQ dst,
    args = [srcP, srcQ, dst] ∧ 16 ≤ 2 ^ w ∧
    srcP + (2 * P.length + 1) < 2 ^ w ∧ srcQ + (2 * Q.length + 1) < 2 ^ w ∧
    dst + (2 * (P.length + Q.length) + 1) < 2 ^ w ∧
    (srcP + (2 * P.length + 1) ≤ dst ∨ dst + (2 * (P.length + Q.length) + 1) ≤ srcP) ∧
    (srcQ + (2 * Q.length + 1) ≤ dst ∨ dst + (2 * (P.length + Q.length) + 1) ≤ srcQ) ∧
    (∀ x ∈ P, x.1 < 2 ^ w) ∧ (∀ x ∈ Q, x.1 < 2 ^ w) ∧
    MWalkAt mem srcP P ∧ MWalkAt mem srcQ Q
  post args mem ret mem' := ∃ srcP srcQ dst,
    args = [srcP, srcQ, dst] ∧ ret = dst + (2 * (P.length + Q.length) + 1) ∧
    MWalkAt mem' dst (P ++ Q) ∧
    ∀ addr, addr < dst ∨ dst + (2 * (P.length + Q.length) + 1) ≤ addr → mem' addr = mem addr
  cost _ _ := 70 * (P.length + Q.length) + 50

def mWalkPrefixContract (w vCap eCap : ℕ) (H : MGraph) (uStart vEnd : ℕ)
    (W : List (ℕ × Bool)) (S : Finset ℕ) : Contract where
  pre args mem := ∃ gPtr wPtr SBitPtr dstPtr,
    args = [gPtr, uStart, wPtr, SBitPtr, dstPtr] ∧ 16 ≤ 2 ^ w ∧
    gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    wPtr + (2 * W.length + 1) < 2 ^ w ∧
    SBitPtr + vCap < 2 ^ w ∧
    dstPtr + (2 * (prefixWalk H uStart W S).2.length + 1) < 2 ^ w ∧
    (wPtr + (2 * W.length + 1) ≤ dstPtr ∨ dstPtr + (2 * (prefixWalk H uStart W S).2.length + 1) ≤ wPtr) ∧
    (∀ v < vCap, SBitPtr + v < dstPtr ∨ dstPtr + (2 * (prefixWalk H uStart W S).2.length + 1) ≤ SBitPtr + v) ∧
    (∀ i < dynGraphSize vCap eCap,
      gPtr + i < dstPtr ∨ dstPtr + (2 * (prefixWalk H uStart W S).2.length + 1) ≤ gPtr + i) ∧
    DynGraphAt mem gPtr vCap eCap H ∧
    H.IsValid ∧ (∀ v ∈ H.V, v < vCap) ∧ (∀ e ∈ H.E, e < eCap) ∧ uStart ∈ H.V ∧
    H.IsWalk uStart (prefixWalk H uStart W S).1 (prefixWalk H uStart W S).2 ∧
    MWalkAt mem wPtr W ∧
    (∀ v < vCap, mem (SBitPtr + v) = if v ∈ S then 1 else 0)
  post args mem ret mem' := ∃ gPtr wPtr SBitPtr dstPtr,
    args = [gPtr, uStart, wPtr, SBitPtr, dstPtr] ∧
    ret = (prefixWalk H uStart W S).1 ∧
    MWalkAt mem' dstPtr (prefixWalk H uStart W S).2 ∧
    ∀ addr, addr < dstPtr ∨ dstPtr + (2 * (prefixWalk H uStart W S).2.length + 1) ≤ addr →
      mem' addr = mem addr
  cost _ _ := 180 * (prefixWalk H uStart W S).2.length + 80

/-- Both prefix walks of `P` (forward from `a` and backward from `b` along `walkRev P`) stop
at `S` using only valid edges of `G`, and every edge ID in `P` lies below `eCap`. This holds
for `piLt_mid e` after deletions and splits even when edges in the middle of `P` were deleted. -/
def PrefixWalksValid (G : MGraph) (S : Finset ℕ) (eCap a b : ℕ) (P : List (ℕ × Bool)) : Prop :=
  G.IsWalk a (prefixWalk G a P S).1 (prefixWalk G a P S).2 ∧
  G.IsWalk b (prefixWalk G b (walkRev P) S).1 (prefixWalk G b (walkRev P) S).2 ∧
  ∀ x ∈ P, x.1 < eCap

lemma isWalk_end_mem_V {G : MGraph} (hV : G.IsValid) :
    ∀ {u v : ℕ} {P : List (ℕ × Bool)}, u ∈ G.V → G.IsWalk u v P → v ∈ G.V
  | _, _, [], hu, .nil _ => hu
  | _, _, x :: xs, _, .cons he _ hrest => by
    have hd : G.dst x ∈ G.V := by
      rcases x with ⟨e, d⟩
      cases d <;> [exact (hV e he).1; exact (hV e he).2]
    exact isWalk_end_mem_V hV hd hrest

end

/-! ## Helper walk lemmas -/

public section

lemma mWalkAt_of_prefix_mem {mem : ℕ → ℕ} {a : ℕ} {P : List (ℕ × Bool)}
    (hlen : mem a = P.length)
    (hsteps : ∀ i (hi : i < P.length),
      mem (a + (1 + 2 * i)) = P[i].1 ∧
      mem (a + (1 + 2 * i) + 1) = (if P[i].2 then 1 else 0)) :
    MWalkAt mem a P := by
  intro j hj
  simp only [mWalkEncode_length] at hj
  rcases j with _ | k
  · simp [mWalkEncode, hlen]
  · have hk : k < 2 * P.length := by omega
    let q := k / 2
    have hq : q < P.length := by omega
    rcases hsteps q hq with ⟨he, hd⟩
    rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
    · have hidx : k = 2 * q := by omega
      have hget : (mWalkEncode P)[k + 1]'(by rw [mWalkEncode_length]; omega) = P[q].1 := by
        simp only [mWalkEncode, List.getElem_cons_succ]
        have hev := flatMap_pair_getElem_even hq
        convert hev using 2
      have haddr : a + (k + 1) = a + (1 + 2 * q) := by omega
      rw [hget, haddr]; exact he
    · have hidx : k = 2 * q + 1 := by omega
      have hget : (mWalkEncode P)[k + 1]'(by rw [mWalkEncode_length]; omega) =
          if P[q].2 then 1 else 0 := by
        simp only [mWalkEncode, List.getElem_cons_succ]
        have hod := flatMap_pair_getElem_odd hq
        convert hod using 2
      have haddr : a + (k + 1) = a + (1 + 2 * q) + 1 := by omega
      rw [hget, haddr]; exact hd

lemma mWalkAt_len {mem : ℕ → ℕ} {a : ℕ} {P : List (ℕ × Bool)}
    (hP : MWalkAt mem a P) : mem a = P.length := MWalkAt_head hP

/-! ## Contract proofs -/

theorem mWalkCopy_meetsContract {w : ℕ} {p : Program} {b bOps : ℕ} {P : List (ℕ × Bool)}
    (hp : p.HasAt b (embOpsProcs bOps)) :
    MeetsContract w p (b + embIdxWalkCopy) (mWalkCopyContract w P) := by
  refine meetsContract_of_runs (hp.get (i := embIdxWalkCopy) (by simp [embOpsProcs, embIdxWalkCopy]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨src, dst, rfl, hw16, hsrcB, hdstB, hdisj, hxW, hPat⟩
  have hlt_src : src < 2 ^ w := hargs src (by simp)
  have hlt_dst : dst < 2 ^ w := hargs dst (by simp)
  have hlt_len : P.length < 2 ^ w := by omega
  have hlt_end : dst + (2 * P.length + 1) < 2 ^ w := hdstB
  have hw_ne0 : w ≠ 0 := by rintro rfl; omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [embOpsProcs, embIdxWalkCopy, List.getElem_cons_zero, mWalkCopyStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := P.length) (by eval_expr)
    (by simpa [startState] using mWalkAt_len hPat)) ?_
  refine runs_seq_store_le (v := P.length) (x := dst) (by eval_expr) (by eval_expr) ?_
  let mem0 : ℕ → ℕ := Function.update mem dst P.length
  let Inv : ℕ → State → Prop := fun k st =>
    k ≤ P.length ∧
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = P.length ∧ st.regs 3 = k ∧
    st.mem dst = P.length ∧
    (∀ i < k, st.mem (dst + (1 + 2 * i)) = P[i]!.1 ∧
              st.mem (dst + (1 + 2 * i) + 1) = (if P[i]!.2 then 1 else 0)) ∧
    ∀ addr, addr < dst ∨ dst + (2 * P.length + 1) ≤ addr → st.mem addr = mem addr
  let body : Stmt :=
    .assign 4 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 3))) ;;
    .assign 5 (.load (.bin .add (.reg 0) (.reg 4))) ;;
    .assign 6 (.load (.bin .add (.bin .add (.reg 0) (.reg 4)) (.const 1))) ;;
    .store (.bin .add (.reg 1) (.reg 4)) (.reg 5) ;;
    .store (.bin .add (.bin .add (.reg 1) (.reg 4)) (.const 1)) (.reg 6)
  let P0 : State → Prop := fun st =>
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = P.length ∧ st.mem dst = P.length ∧
    ∀ addr, addr < dst ∨ dst + (2 * P.length + 1) ≤ addr → st.mem addr = mem addr
  have hLoop : Triple w p P0 (forRange 3 (.const 0) (.reg 2) body) (normalPost (Inv P.length))
      (fun _ => (P.length - 0) * (40 + Expr.size (.reg 2) + 8) + (Expr.size (.const 0) + Expr.size (.reg 2) + 5)) := by
    refine Triple.forRange_const 40 0 P.length (Nat.zero_le _) h1_lt (fun _ => hlt_len)
      (fun st hst => by
        rcases hst with ⟨h0, h1, h2, hmd, hfr⟩
        refine ⟨by simp [Expr.eval, h0_lt],
          ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, hmd, fun _ hi => absurd hi (Nat.not_lt_zero _), hfr⟩⟩
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp)
      (fun k st _ _ hk => hk.2.2.2.2.1)
      (fun k st _ _ hk => by
        rcases hk with ⟨_, _, _, hr2, _, _, _, _⟩
        simp [Expr.eval, hr2])
      (fun k _ hk_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr1, hr2, hr3, hmd, hsteps, hfr⟩
        have hk_2k : 2 * k < 2 ^ w := by omega
        have hk_off : 1 + 2 * k < 2 ^ w := by omega
        have hsrc_off : src + (1 + 2 * k) < 2 ^ w := by omega
        have hsrc_off1 : src + (1 + 2 * k) + 1 < 2 ^ w := by omega
        have hdst_off : dst + (1 + 2 * k) < 2 ^ w := by omega
        have hdst_off1 : dst + (1 + 2 * k) + 1 < 2 ^ w := by omega
        have hdisj0 : src + (1 + 2 * k) < dst ∨ dst + (2 * P.length + 1) ≤ src + (1 + 2 * k) := by omega
        have hdisj1 : src + (1 + 2 * k) + 1 < dst ∨ dst + (2 * P.length + 1) ≤ src + (1 + 2 * k) + 1 := by omega
        have he_mem : st.mem (src + (1 + 2 * k)) = P[k].1 := by
          rw [hfr _ hdisj0]
          have := MWalkAt_step_edge hPat hk_lt
          rwa [show src + 1 + 2 * k = src + (1 + 2 * k) by omega] at this
        have hd_mem : st.mem (src + (1 + 2 * k) + 1) = (if P[k].2 then 1 else 0) := by
          rw [hfr _ hdisj1]
          have := MWalkAt_step_dir hPat hk_lt
          rwa [show src + 1 + 2 * k + 1 = src + (1 + 2 * k) + 1 by omega] at this
        have he_lt : P[k].1 < 2 ^ w := hxW P[k] (List.getElem_mem hk_lt)
        have hd_lt : (if P[k].2 then 1 else 0) < 2 ^ w := by split_ifs <;> omega
        suffices h : ∃ o st₁ c, Runs w p ω' body st o st₁ c ∧
            (normalPost fun st₁ =>
              Inv (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 3 (k + 1), pos := st₁.pos } ∧
                st₁.regs 3 = k) o st₁ ∧
            0 + c ≤ 40 by
          rcases h with ⟨o, st₁, c, hr, hq, hc⟩
          exact ⟨o, st₁, c, hr, hq, by simpa using hc⟩
        dsimp only [body]
        refine runs_seq_assign_le (v := 1 + 2 * k)
          (by simp [Expr.eval, BinOp.eval, h1_lt, h2_lt, hr3, hk_2k, hk_off]) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := P[k].1) (by simp [Expr.eval, BinOp.eval, hr0, hsrc_off]) he_mem) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := if P[k].2 then 1 else 0)
            (by simp [Expr.eval, BinOp.eval, h1_lt, hr0, hsrc_off, hsrc_off1]) hd_mem) ?_
        refine runs_seq_store_le (v := P[k].1) (x := dst + (1 + 2 * k))
          (by simp [Expr.eval, BinOp.eval, hr1, hdst_off]) (by eval_expr) ?_
        refine runs_store_le (v := if P[k].2 then 1 else 0) (x := dst + (1 + 2 * k) + 1)
          (by simp [Expr.eval, BinOp.eval, h1_lt, hr1, hdst_off, hdst_off1]) (by eval_expr)
          ?_ (by dsimp only [Expr.size]; omega)
        refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · dsimp only; simp [hr0]
        · dsimp only; simp [hr1]
        · dsimp only; simp [hr2]
        · simp
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hmd
        · intro i hi
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hik | heq
          · have ihs := hsteps i hik
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact ihs
          · simp only [heq, getElem!_pos P k hk_lt]
            constructor
            · simp only [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self (dst + (1 + 2 * k)))),
                Function.update_self]
            · simp only [Function.update_self]
        · intro addr hout
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr addr hout
        · dsimp only; simp [hr3])
  refine runs_seq_triple_le hLoop ⟨?_, ?_, ?_, ?_, ?_⟩ ?_
  · simp [startState]
  · simp [startState]
  · simp [startState]
  · simp
  · intro addr hout
    dsimp only [startState]
    rw [Function.update_of_ne (by omega)]
  intro st₁ ⟨_, _, hr1, hr2, _, hmd, hsteps, hfr⟩
  have hPat' : MWalkAt st₁.mem dst P := mWalkAt_of_prefix_mem hmd fun i hi => by
    simpa [getElem!_pos P i hi] using hsteps i hi
  have h2p_1 : 2 * P.length + 1 < 2 ^ w := by omega
  have hdst_2p_1 : dst + (2 * P.length + 1) < 2 ^ w := by omega
  refine runs_ret_le (by simp [Expr.eval, BinOp.eval, h1_lt, h2_lt, hr1, hr2, h2p_1, hdst_2p_1,
    show 2 * P.length < 2 ^ w by omega])
    ⟨src, dst, rfl, rfl, hPat', hfr⟩ ?_
  dsimp only [mWalkCopyContract, Expr.size]
  omega

theorem mWalkRev_meetsContract {w : ℕ} {p : Program} {b bOps : ℕ} {P : List (ℕ × Bool)}
    (hp : p.HasAt b (embOpsProcs bOps)) :
    MeetsContract w p (b + embIdxWalkRev) (mWalkRevContract w P) := by
  refine meetsContract_of_runs (hp.get (i := embIdxWalkRev) (by simp [embOpsProcs, embIdxWalkRev]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨src, dst, rfl, hw16, hsrcB, hdstB, hdisj, hxW, hPat⟩
  have hlt_src : src < 2 ^ w := hargs src (by simp)
  have hlt_dst : dst < 2 ^ w := hargs dst (by simp)
  have hlt_len : P.length < 2 ^ w := by omega
  have hlt_end : dst + (2 * P.length + 1) < 2 ^ w := hdstB
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [embOpsProcs, embIdxWalkRev, List.getElem_cons_succ, List.getElem_cons_zero, mWalkRevStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := P.length) (by eval_expr)
    (by simpa [startState] using mWalkAt_len hPat)) ?_
  refine runs_seq_store_le (v := P.length) (x := dst) (by eval_expr) (by eval_expr) ?_
  let R := walkRev P
  have hRlen : R.length = P.length := length_walkRev P
  let Inv : ℕ → State → Prop := fun k st =>
    k ≤ P.length ∧
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = P.length ∧ st.regs 3 = k ∧
    st.mem dst = P.length ∧
    (∀ i < k, st.mem (dst + (1 + 2 * i)) = R[i]!.1 ∧
              st.mem (dst + (1 + 2 * i) + 1) = (if R[i]!.2 then 1 else 0)) ∧
    ∀ addr, addr < dst ∨ dst + (2 * P.length + 1) ≤ addr → st.mem addr = mem addr
  let body : Stmt :=
    .assign 4 (.bin .sub (.bin .sub (.reg 2) (.const 1)) (.reg 3)) ;;
    .assign 5 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 4))) ;;
    .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
    .assign 7 (.load (.bin .add (.bin .add (.reg 0) (.reg 5)) (.const 1))) ;;
    .assign 8 (.bin .sub (.const 1) (.reg 7)) ;;
    .assign 9 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 3))) ;;
    .store (.bin .add (.reg 1) (.reg 9)) (.reg 6) ;;
    .store (.bin .add (.bin .add (.reg 1) (.reg 9)) (.const 1)) (.reg 8)
  let P0 : State → Prop := fun st =>
    st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = P.length ∧ st.mem dst = P.length ∧
    ∀ addr, addr < dst ∨ dst + (2 * P.length + 1) ≤ addr → st.mem addr = mem addr
  have hLoop : Triple w p P0 (forRange 3 (.const 0) (.reg 2) body) (normalPost (Inv P.length))
      (fun _ => (P.length - 0) * (60 + Expr.size (.reg 2) + 8) + (Expr.size (.const 0) + Expr.size (.reg 2) + 5)) := by
    refine Triple.forRange_const 60 0 P.length (Nat.zero_le _) h1_lt (fun _ => hlt_len)
      (fun st hst => by
        rcases hst with ⟨h0, h1, h2, hmd, hfr⟩
        refine ⟨by simp [Expr.eval, h0_lt],
          ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, hmd, fun _ hi => absurd hi (Nat.not_lt_zero _), hfr⟩⟩
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp)
      (fun k st _ _ hk => hk.2.2.2.2.1)
      (fun k st _ _ hk => by
        rcases hk with ⟨_, _, _, hr2, _, _, _, _⟩
        simp [Expr.eval, hr2])
      (fun k _ hk_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr1, hr2, hr3, hmd, hsteps, hfr⟩
        let revIdx := P.length - 1 - k
        have hrev_lt : revIdx < P.length := by omega
        have hlen_sub : P.length - 1 < 2 ^ w := by omega
        have h2rev : 2 * revIdx < 2 ^ w := by omega
        have hoff_rev : 1 + 2 * revIdx < 2 ^ w := by omega
        have hsrc_off : src + (1 + 2 * revIdx) < 2 ^ w := by omega
        have hsrc_off1 : src + (1 + 2 * revIdx) + 1 < 2 ^ w := by omega
        have hk_2k : 2 * k < 2 ^ w := by omega
        have hoff_k : 1 + 2 * k < 2 ^ w := by omega
        have hdst_off : dst + (1 + 2 * k) < 2 ^ w := by omega
        have hdst_off1 : dst + (1 + 2 * k) + 1 < 2 ^ w := by omega
        have hdisj0 : src + (1 + 2 * revIdx) < dst ∨ dst + (2 * P.length + 1) ≤ src + (1 + 2 * revIdx) := by omega
        have hdisj1 : src + (1 + 2 * revIdx) + 1 < dst ∨ dst + (2 * P.length + 1) ≤ src + (1 + 2 * revIdx) + 1 := by omega
        have hkR : k < R.length := hRlen.symm ▸ hk_lt
        have hRk : R[k] = (P[revIdx].1, !P[revIdx].2) := by
          simp only [R, walkRev, List.getElem_reverse, List.getElem_map, List.length_map]
          rfl
        have he_mem : st.mem (src + (1 + 2 * revIdx)) = R[k].1 := by
          rw [hfr _ hdisj0, hRk]
          have := MWalkAt_step_edge hPat hrev_lt
          rwa [show src + 1 + 2 * revIdx = src + (1 + 2 * revIdx) by omega] at this
        have hd_raw : st.mem (src + (1 + 2 * revIdx) + 1) = (if P[revIdx].2 then 1 else 0) := by
          rw [hfr _ hdisj1]
          have := MWalkAt_step_dir hPat hrev_lt
          rwa [show src + 1 + 2 * revIdx + 1 = src + (1 + 2 * revIdx) + 1 by omega] at this
        have hd_flip : 1 - (if P[revIdx].2 then 1 else 0) = if R[k].2 then 1 else 0 := by
          rw [hRk]
          cases P[revIdx].2 <;> rfl
        have he_lt : R[k].1 < 2 ^ w := by
          rw [hRk]; exact hxW P[revIdx] (List.getElem_mem hrev_lt)
        have hd_raw_lt : (if P[revIdx].2 then 1 else 0) < 2 ^ w := by split_ifs <;> omega
        have hd_lt : (if R[k].2 then 1 else 0) < 2 ^ w := by split_ifs <;> omega
        suffices h : ∃ o st₁ c, Runs w p ω' body st o st₁ c ∧
            (normalPost fun st₁ =>
              Inv (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 3 (k + 1), pos := st₁.pos } ∧
                st₁.regs 3 = k) o st₁ ∧
            0 + c ≤ 60 by
          rcases h with ⟨o, st₁, c, hr, hq, hc⟩
          exact ⟨o, st₁, c, hr, hq, by simpa using hc⟩
        dsimp only [body]
        refine runs_seq_assign_le (v := revIdx)
          (by simp [Expr.eval, BinOp.eval, h1_lt, hr2, hr3, hlen_sub,
            show P.length - 1 - k < 2 ^ w by omega]; rfl) ?_
        refine runs_seq_assign_le (v := 1 + 2 * revIdx)
          (by simp [Expr.eval, BinOp.eval, h1_lt, h2_lt, h2rev, hoff_rev]) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := R[k].1) (by simp [Expr.eval, BinOp.eval, hr0, hsrc_off]) he_mem) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := if P[revIdx].2 then 1 else 0)
            (by simp [Expr.eval, BinOp.eval, h1_lt, hr0, hsrc_off, hsrc_off1]) hd_raw) ?_
        refine runs_seq_assign_le (v := if R[k].2 then 1 else 0)
          (by simp [Expr.eval, BinOp.eval, h1_lt, hd_flip, hd_lt]) ?_
        refine runs_seq_assign_le (v := 1 + 2 * k)
          (by simp [Expr.eval, BinOp.eval, h1_lt, h2_lt, hr3, hk_2k, hoff_k]) ?_
        refine runs_seq_store_le (v := R[k].1) (x := dst + (1 + 2 * k))
          (by simp [Expr.eval, BinOp.eval, hr1, hdst_off]) (by eval_expr) ?_
        refine runs_store_le (v := if R[k].2 then 1 else 0) (x := dst + (1 + 2 * k) + 1)
          (by simp [Expr.eval, BinOp.eval, h1_lt, hr1, hdst_off, hdst_off1]) (by eval_expr)
          ?_ (by dsimp only [Expr.size]; omega)
        refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · dsimp only; simp [hr0]
        · dsimp only; simp [hr1]
        · dsimp only; simp [hr2]
        · simp
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hmd
        · intro i hi
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hik | heq
          · have ihs := hsteps i hik
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact ihs
          · simp only [heq, getElem!_pos R k hkR]
            constructor
            · simp only [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self (dst + (1 + 2 * k)))),
                Function.update_self]
            · simp only [Function.update_self]
        · intro addr hout
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr addr hout
        · dsimp only; simp [hr3])
  refine runs_seq_triple_le hLoop ⟨?_, ?_, ?_, ?_, ?_⟩ ?_
  · simp [startState]
  · simp [startState]
  · simp [startState]
  · simp
  · intro addr hout
    dsimp only [startState]
    rw [Function.update_of_ne (by omega)]
  intro st₁ ⟨_, _, hr1, hr2, _, hmd, hsteps, hfr⟩
  have hRat' : MWalkAt st₁.mem dst R := mWalkAt_of_prefix_mem (hRlen ▸ hmd) fun i hi => by
    simpa [getElem!_pos R i hi] using hsteps i (hRlen ▸ hi)
  have h2p_1 : 2 * P.length + 1 < 2 ^ w := by omega
  have hdst_2p_1 : dst + (2 * P.length + 1) < 2 ^ w := by omega
  refine runs_ret_le (by simp [Expr.eval, BinOp.eval, h1_lt, h2_lt, hr1, hr2, h2p_1, hdst_2p_1,
    show 2 * P.length < 2 ^ w by omega])
    ⟨src, dst, rfl, rfl, hRat', hfr⟩ ?_
  dsimp only [mWalkRevContract, Expr.size]
  omega

theorem mWalkConcat_meetsContract {w : ℕ} {p : Program} {b bOps : ℕ} {P Q : List (ℕ × Bool)}
    (hp : p.HasAt b (embOpsProcs bOps)) :
    MeetsContract w p (b + embIdxWalkConcat) (mWalkConcatContract w P Q) := by
  refine meetsContract_of_runs (hp.get (i := embIdxWalkConcat) (by simp [embOpsProcs, embIdxWalkConcat]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨srcP, srcQ, dst, rfl, hw16, hP_B, hQ_B, hdst_B, hdisjP, hdisjQ, hxP, hxQ, hPat, hQat⟩
  have hlt_sP : srcP < 2 ^ w := hargs srcP (by simp)
  have hlt_sQ : srcQ < 2 ^ w := hargs srcQ (by simp)
  have hlt_dst : dst < 2 ^ w := hargs dst (by simp)
  have hlt_Plen : P.length < 2 ^ w := by omega
  have hlt_Qlen : Q.length < 2 ^ w := by omega
  have hlt_PQ : P.length + Q.length < 2 ^ w := by omega
  have hlt_end : dst + (2 * (P.length + Q.length) + 1) < 2 ^ w := hdst_B
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [embOpsProcs, embIdxWalkConcat, List.getElem_cons_succ, List.getElem_cons_zero,
    mWalkConcatStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := P.length) (by eval_expr)
    (by simpa [startState] using mWalkAt_len hPat)) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := Q.length) (by eval_expr)
    (by simpa [startState] using mWalkAt_len hQat)) ?_
  refine runs_seq_assign_le (v := P.length + Q.length) (by eval_expr) ?_
  refine runs_seq_store_le (v := P.length + Q.length) (x := dst) (by eval_expr) (by eval_expr) ?_
  let InvP : ℕ → State → Prop := fun k st =>
    k ≤ P.length ∧
    st.regs 0 = srcP ∧ st.regs 1 = srcQ ∧ st.regs 2 = dst ∧ st.regs 3 = P.length ∧
    st.regs 4 = Q.length ∧ st.regs 5 = P.length + Q.length ∧ st.regs 6 = k ∧
    st.mem dst = P.length + Q.length ∧
    (∀ i < k, st.mem (dst + (1 + 2 * i)) = P[i]!.1 ∧
              st.mem (dst + (1 + 2 * i) + 1) = (if P[i]!.2 then 1 else 0)) ∧
    ∀ addr, addr < dst ∨ dst + (2 * (P.length + Q.length) + 1) ≤ addr → st.mem addr = mem addr
  let bodyP : Stmt :=
    .assign 7 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 6))) ;;
    .assign 8 (.load (.bin .add (.reg 0) (.reg 7))) ;;
    .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.reg 7)) (.const 1))) ;;
    .store (.bin .add (.reg 2) (.reg 7)) (.reg 8) ;;
    .store (.bin .add (.bin .add (.reg 2) (.reg 7)) (.const 1)) (.reg 9)
  let PP0 : State → Prop := fun st =>
    st.regs 0 = srcP ∧ st.regs 1 = srcQ ∧ st.regs 2 = dst ∧ st.regs 3 = P.length ∧
    st.regs 4 = Q.length ∧ st.regs 5 = P.length + Q.length ∧ st.mem dst = P.length + Q.length ∧
    ∀ addr, addr < dst ∨ dst + (2 * (P.length + Q.length) + 1) ≤ addr → st.mem addr = mem addr
  have hLoopP : Triple w p PP0 (forRange 6 (.const 0) (.reg 3) bodyP) (normalPost (InvP P.length))
      (fun _ => (P.length - 0) * (40 + Expr.size (.reg 3) + 8) + (Expr.size (.const 0) + Expr.size (.reg 3) + 5)) := by
    refine Triple.forRange_const 40 0 P.length (Nat.zero_le _) h1_lt (fun _ => hlt_Plen)
      (fun st hst => by
        rcases hst with ⟨h0, h1, h2, h3, h4, h5, hmd, hfr⟩
        refine ⟨by simp [Expr.eval, h0_lt],
          ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmd, fun _ hi => absurd hi (Nat.not_lt_zero _), hfr⟩⟩
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp [h3]
        · simp [h4]
        · simp [h5]
        · simp)
      (fun k st _ _ hk => hk.2.2.2.2.2.2.2.1)
      (fun k st _ _ hk => by
        rcases hk with ⟨_, _, _, _, hr3, _, _, _, _, _, _⟩
        simp [Expr.eval, hr3])
      (fun k _ hk_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hmd, hsteps, hfr⟩
        have hk_2k : 2 * k < 2 ^ w := by omega
        have hk_off : 1 + 2 * k < 2 ^ w := by omega
        have hsrc_off : srcP + (1 + 2 * k) < 2 ^ w := by omega
        have hsrc_off1 : srcP + (1 + 2 * k) + 1 < 2 ^ w := by omega
        have hdst_off : dst + (1 + 2 * k) < 2 ^ w := by omega
        have hdst_off1 : dst + (1 + 2 * k) + 1 < 2 ^ w := by omega
        have hdisj0 : srcP + (1 + 2 * k) < dst ∨ dst + (2 * (P.length + Q.length) + 1) ≤ srcP + (1 + 2 * k) := by omega
        have hdisj1 : srcP + (1 + 2 * k) + 1 < dst ∨ dst + (2 * (P.length + Q.length) + 1) ≤ srcP + (1 + 2 * k) + 1 := by omega
        have he_mem : st.mem (srcP + (1 + 2 * k)) = P[k].1 := by
          rw [hfr _ hdisj0]
          have := MWalkAt_step_edge hPat hk_lt
          rwa [show srcP + 1 + 2 * k = srcP + (1 + 2 * k) by omega] at this
        have hd_mem : st.mem (srcP + (1 + 2 * k) + 1) = (if P[k].2 then 1 else 0) := by
          rw [hfr _ hdisj1]
          have := MWalkAt_step_dir hPat hk_lt
          rwa [show srcP + 1 + 2 * k + 1 = srcP + (1 + 2 * k) + 1 by omega] at this
        have he_lt : P[k].1 < 2 ^ w := hxP P[k] (List.getElem_mem hk_lt)
        have hd_lt : (if P[k].2 then 1 else 0) < 2 ^ w := by split_ifs <;> omega
        suffices h : ∃ o st₁ c, Runs w p ω' bodyP st o st₁ c ∧
            (normalPost fun st₁ =>
              InvP (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 6 (k + 1), pos := st₁.pos } ∧
                st₁.regs 6 = k) o st₁ ∧
            0 + c ≤ 40 by
          rcases h with ⟨o, st₁, c, hr, hq, hc⟩
          exact ⟨o, st₁, c, hr, hq, by simpa using hc⟩
        dsimp only [bodyP]
        refine runs_seq_assign_le (v := 1 + 2 * k)
          (by simp [Expr.eval, BinOp.eval, h1_lt, h2_lt, hr6, hk_2k, hk_off]) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := P[k].1) (by simp [Expr.eval, BinOp.eval, hr0, hsrc_off]) he_mem) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := if P[k].2 then 1 else 0)
            (by simp [Expr.eval, BinOp.eval, h1_lt, hr0, hsrc_off, hsrc_off1]) hd_mem) ?_
        refine runs_seq_store_le (v := P[k].1) (x := dst + (1 + 2 * k))
          (by simp [Expr.eval, BinOp.eval, hr2, hdst_off]) (by eval_expr) ?_
        refine runs_store_le (v := if P[k].2 then 1 else 0) (x := dst + (1 + 2 * k) + 1)
          (by simp [Expr.eval, BinOp.eval, h1_lt, hr2, hdst_off, hdst_off1]) (by eval_expr)
          ?_ (by dsimp only [Expr.size]; omega)
        refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · dsimp only; simp [hr0]
        · dsimp only; simp [hr1]
        · dsimp only; simp [hr2]
        · dsimp only; simp [hr3]
        · dsimp only; simp [hr4]
        · dsimp only; simp [hr5]
        · simp
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hmd
        · intro i hi
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hik | heq
          · have ihs := hsteps i hik
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact ihs
          · simp only [heq, getElem!_pos P k hk_lt]
            constructor
            · simp only [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self (dst + (1 + 2 * k)))),
                Function.update_self]
            · simp only [Function.update_self]
        · intro addr hout
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr addr hout
        · dsimp only; simp [hr6])
  refine runs_seq_triple_le hLoopP ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · simp [startState]
  · simp [startState]
  · simp [startState]
  · simp [startState]
  · simp [startState]
  · simp [startState]
  · simp
  · intro addr hout
    dsimp only [startState]
    rw [Function.update_of_ne (by omega)]
  intro stP ⟨_, hr0P, hr1P, hr2P, hr3P, hr4P, hr5P, _, hmdP, hstepsP, hfrP⟩
  let PQ0 : State → Prop := fun st =>
    st.regs 0 = srcP ∧ st.regs 1 = srcQ ∧ st.regs 2 = dst ∧ st.regs 3 = P.length ∧
    st.regs 4 = Q.length ∧ st.regs 5 = P.length + Q.length ∧ st.mem dst = P.length + Q.length ∧
    (∀ i < P.length, st.mem (dst + (1 + 2 * i)) = P[i]!.1 ∧
                     st.mem (dst + (1 + 2 * i) + 1) = (if P[i]!.2 then 1 else 0)) ∧
    ∀ addr, addr < dst ∨ dst + (2 * (P.length + Q.length) + 1) ≤ addr → st.mem addr = mem addr
  let InvQ : ℕ → State → Prop := fun k st =>
    k ≤ Q.length ∧
    st.regs 0 = srcP ∧ st.regs 1 = srcQ ∧ st.regs 2 = dst ∧ st.regs 3 = P.length ∧
    st.regs 4 = Q.length ∧ st.regs 5 = P.length + Q.length ∧ st.regs 6 = k ∧
    st.mem dst = P.length + Q.length ∧
    (∀ i < P.length, st.mem (dst + (1 + 2 * i)) = P[i]!.1 ∧
                     st.mem (dst + (1 + 2 * i) + 1) = (if P[i]!.2 then 1 else 0)) ∧
    (∀ i < k, st.mem (dst + (1 + 2 * P.length + 2 * i)) = Q[i]!.1 ∧
              st.mem (dst + (1 + 2 * P.length + 2 * i) + 1) = (if Q[i]!.2 then 1 else 0)) ∧
    ∀ addr, addr < dst ∨ dst + (2 * (P.length + Q.length) + 1) ≤ addr → st.mem addr = mem addr
  let bodyQ : Stmt :=
    .assign 7 (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 6))) ;;
    .assign 8 (.bin .add (.reg 7) (.bin .mul (.const 2) (.reg 3))) ;;
    .assign 9 (.load (.bin .add (.reg 1) (.reg 7))) ;;
    .assign 10 (.load (.bin .add (.bin .add (.reg 1) (.reg 7)) (.const 1))) ;;
    .store (.bin .add (.reg 2) (.reg 8)) (.reg 9) ;;
    .store (.bin .add (.bin .add (.reg 2) (.reg 8)) (.const 1)) (.reg 10)
  have hLoopQ : Triple w p PQ0 (forRange 6 (.const 0) (.reg 4) bodyQ) (normalPost (InvQ Q.length))
      (fun _ => (Q.length - 0) * (50 + Expr.size (.reg 4) + 8) + (Expr.size (.const 0) + Expr.size (.reg 4) + 5)) := by
    refine Triple.forRange_const 50 0 Q.length (Nat.zero_le _) h1_lt (fun _ => hlt_Qlen)
      (fun st hst => by
        rcases hst with ⟨h0, h1, h2, h3, h4, h5, hmd, hsP, hfr⟩
        refine ⟨by simp [Expr.eval, h0_lt],
          ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmd, hsP, fun _ hi => absurd hi (Nat.not_lt_zero _), hfr⟩⟩
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp [h3]
        · simp [h4]
        · simp [h5]
        · simp)
      (fun k st _ _ hk => hk.2.2.2.2.2.2.2.1)
      (fun k st _ _ hk => by
        rcases hk with ⟨_, _, _, _, _, hr4, _, _, _, _, _, _⟩
        simp [Expr.eval, hr4])
      (fun k _ hk_lt st ω' hk => by
        rcases hk with ⟨_, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hmd, hsP, hsQ, hfr⟩
        have hk_2k : 2 * k < 2 ^ w := by omega
        have hk_off : 1 + 2 * k < 2 ^ w := by omega
        have hP_2 : 2 * P.length < 2 ^ w := by omega
        have hdst_off_rel : 1 + 2 * k + 2 * P.length < 2 ^ w := by omega
        have hsrc_off : srcQ + (1 + 2 * k) < 2 ^ w := by omega
        have hsrc_off1 : srcQ + (1 + 2 * k) + 1 < 2 ^ w := by omega
        have hdst_off : dst + (1 + 2 * P.length + 2 * k) < 2 ^ w := by omega
        have hdst_off1 : dst + (1 + 2 * P.length + 2 * k) + 1 < 2 ^ w := by omega
        have hdisj0 : srcQ + (1 + 2 * k) < dst ∨ dst + (2 * (P.length + Q.length) + 1) ≤ srcQ + (1 + 2 * k) := by omega
        have hdisj1 : srcQ + (1 + 2 * k) + 1 < dst ∨ dst + (2 * (P.length + Q.length) + 1) ≤ srcQ + (1 + 2 * k) + 1 := by omega
        have he_mem : st.mem (srcQ + (1 + 2 * k)) = Q[k].1 := by
          rw [hfr _ hdisj0]
          have := MWalkAt_step_edge hQat hk_lt
          rwa [show srcQ + 1 + 2 * k = srcQ + (1 + 2 * k) by omega] at this
        have hd_mem : st.mem (srcQ + (1 + 2 * k) + 1) = (if Q[k].2 then 1 else 0) := by
          rw [hfr _ hdisj1]
          have := MWalkAt_step_dir hQat hk_lt
          rwa [show srcQ + 1 + 2 * k + 1 = srcQ + (1 + 2 * k) + 1 by omega] at this
        have he_lt : Q[k].1 < 2 ^ w := hxQ Q[k] (List.getElem_mem hk_lt)
        have hd_lt : (if Q[k].2 then 1 else 0) < 2 ^ w := by split_ifs <;> omega
        suffices h : ∃ o st₁ c, Runs w p ω' bodyQ st o st₁ c ∧
            (normalPost fun st₁ =>
              InvQ (k + 1) { mem := st₁.mem, regs := Function.update st₁.regs 6 (k + 1), pos := st₁.pos } ∧
                st₁.regs 6 = k) o st₁ ∧
            0 + c ≤ 50 by
          rcases h with ⟨o, st₁, c, hr, hq, hc⟩
          exact ⟨o, st₁, c, hr, hq, by simpa using hc⟩
        dsimp only [bodyQ]
        refine runs_seq_assign_le (v := 1 + 2 * k)
          (by simp [Expr.eval, BinOp.eval, h1_lt, h2_lt, hr6, hk_2k, hk_off]) ?_
        refine runs_seq_assign_le (v := 1 + 2 * P.length + 2 * k)
          (by simp [Expr.eval, BinOp.eval, h2_lt, hr3, hP_2,
            show 1 + 2 * k + 2 * P.length = 1 + 2 * P.length + 2 * k by omega,
            show 1 + 2 * P.length + 2 * k < 2 ^ w by omega]) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := Q[k].1) (by simp [Expr.eval, BinOp.eval, hr1, hsrc_off]) he_mem) ?_
        refine runs_seq_assign_le
          (Expr.eval_load_of_eq (v := if Q[k].2 then 1 else 0)
            (by simp [Expr.eval, BinOp.eval, h1_lt, hr1, hsrc_off, hsrc_off1]) hd_mem) ?_
        refine runs_seq_store_le (v := Q[k].1) (x := dst + (1 + 2 * P.length + 2 * k))
          (by simp [Expr.eval, BinOp.eval, hr2, hdst_off]) (by eval_expr) ?_
        refine runs_store_le (v := if Q[k].2 then 1 else 0) (x := dst + (1 + 2 * P.length + 2 * k) + 1)
          (by simp [Expr.eval, BinOp.eval, h1_lt, hr2, hdst_off, hdst_off1]) (by eval_expr)
          ?_ (by dsimp only [Expr.size]; omega)
        refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · dsimp only; simp [hr0]
        · dsimp only; simp [hr1]
        · dsimp only; simp [hr2]
        · dsimp only; simp [hr3]
        · dsimp only; simp [hr4]
        · dsimp only; simp [hr5]
        · simp
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hmd
        · intro i hi
          have ihP := hsP i hi
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact ihP
        · intro i hi
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hik | heq
          · have ihs := hsQ i hik
            dsimp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact ihs
          · simp only [heq, getElem!_pos Q k hk_lt]
            constructor
            · simp only [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self (dst + (1 + 2 * P.length + 2 * k)))),
                Function.update_self]
            · simp only [Function.update_self]
        · intro addr hout
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr addr hout
        · dsimp only; simp [hr6])
  refine runs_seq_triple_le hLoopQ ⟨hr0P, hr1P, hr2P, hr3P, hr4P, hr5P, hmdP, hstepsP, hfrP⟩ ?_
  intro stQ ⟨_, _, _, hr2Q, _, _, hr5Q, _, hmdQ, hsP, hsQ, hfrQ⟩
  have hPQat : MWalkAt stQ.mem dst (P ++ Q) := by
    refine mWalkAt_of_prefix_mem (by simpa using hmdQ) fun i hi => ?_
    simp only [List.length_append] at hi
    by_cases hiP : i < P.length
    · rw [List.getElem_append_left hiP]
      simpa [getElem!_pos P i hiP] using hsP i hiP
    · have hiP_ge : P.length ≤ i := Nat.le_of_not_lt hiP
      have hiQ : i - P.length < Q.length := by omega
      rw [List.getElem_append_right hiP_ge]
      have hsub := hsQ (i - P.length) hiQ
      simp only [getElem!_pos Q (i - P.length) hiQ] at hsub
      simpa [Nat.add_assoc, show 1 + 2 * i = 1 + 2 * P.length + 2 * (i - P.length) by omega] using hsub
  have h2pql_1 : 2 * (P.length + Q.length) + 1 < 2 ^ w := by omega
  refine runs_ret_le
    (by simp [Expr.eval, BinOp.eval, h1_lt, h2_lt, hr2Q, hr5Q, hlt_end, h2pql_1,
      show 2 * (P.length + Q.length) < 2 ^ w by omega])
    ⟨srcP, srcQ, dst, rfl, rfl, hPQat, hfrQ⟩ ?_
  dsimp only [mWalkConcatContract, Expr.size]
  omega


end

end MinCostFlow.DynSpanner.Program
