module

public import MinCostFlow.HierPaths.BuildTopNumConn
public import MinCostFlow.HierPaths.BuildTopLabels
public import MinCostFlow.HierPaths.BuildTopSec3
public import MinCostFlow.HierPaths.BuildTopSec4
public import MinCostFlow.HierPaths.BuildTopSec5
public import MinCostFlow.HierPaths.BuildTopFinish
public import MinCostFlow.HierPaths.BuildTopRootModel

import Mathlib.Tactic.Ring

/-!
# Assembling and packing all six sections of `StaticOut`

After `buildTopDriver` has produced all certified level replies, `buildTopPackAll`
materializes sections 0, 2, 3, 4, and 5 in scratch memory above `tail0` (section 1
is already in place at `ownersAddr`), builds the 6-entry directory, and calls
`buildTopFinish` to pack the final `StaticOut` at `h` and clear scratch memory.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Store the six `(addr, len)` directory pairs at `reg 20 .. reg 20 + 11`. -/
def buildTopStoreDir6 : Stmt :=
  .store (.reg 20) (.bin .add (.reg 9) (.const 3)) ;;
  .store (.bin .add (.reg 20) (.const 1)) (.const 3) ;;
  .store (.bin .add (.reg 20) (.const 2)) (.reg 7) ;;
  .store (.bin .add (.reg 20) (.const 3)) (.reg 2) ;;
  .store (.bin .add (.reg 20) (.const 4)) (.bin .add (.reg 9) (.const 6)) ;;
  .store (.bin .add (.reg 20) (.const 5)) (.reg 12) ;;
  .store (.bin .add (.reg 20) (.const 6)) (.reg 15) ;;
  .store (.bin .add (.reg 20) (.const 7)) (.reg 16) ;;
  .store (.bin .add (.reg 20) (.const 8)) (.reg 18) ;;
  .store (.bin .add (.reg 20) (.const 9)) (.reg 19) ;;
  .store (.bin .add (.reg 20) (.const 10)) (.reg 21) ;;
  .store (.bin .add (.reg 20) (.const 11)) (.reg 22)

theorem buildTopStoreDir6_noRand : buildTopStoreDir6.NoRand := by
  simp [buildTopStoreDir6, Stmt.NoRand]

/-- Materialize section 0 (`[x, b, numConn]`) at `tail0 + 3..5` and section 2 (labels)
at `tail0 + 6..tail0 + 6 + rootM`, putting `rootM` in reg 12 and `dir3` in reg 13. -/
def buildTopPackSec02 (numConn labels : ℕ) : Stmt :=
  .call 11 numConn [.reg 4, .reg 5, .reg 1] ;;
  .store (.bin .add (.reg 9) (.const 3)) (.reg 4) ;;
  .store (.bin .add (.reg 9) (.const 4)) (.reg 5) ;;
  .store (.bin .add (.reg 9) (.const 5)) (.reg 11) ;;
  .assign 12 (.load (.bin .add (.reg 6) (.const 1))) ;;
  .call 13 labels [.reg 8, .reg 12, .bin .add (.reg 9) (.const 6)]

theorem buildTopPackSec02_noRand (numConn labels : ℕ) :
    (buildTopPackSec02 numConn labels).NoRand := by
  simp [buildTopPackSec02, Stmt.NoRand]

/-- Materialize sections 3, 4, and 5 above `dir3`, recording their `(addr, len)` spans in
registers 15..22 and leaving the scratch end `ctx` in register 20. -/
def buildTopPackSec345 (sec3 sec4 sec5 : ℕ) : Stmt :=
  .call 14 sec3 [.reg 0, .reg 1, .reg 2, .reg 6, .reg 9, .reg 13] ;;
  .assign 15 (.bin .add (.reg 13) (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 1) (.const 1)) (.reg 2)))) ;;
  .assign 16 (.bin .sub (.reg 14) (.reg 15)) ;;
  .call 17 sec4 [.reg 0, .reg 1, .reg 2, .bin .add (.reg 9) (.const 2), .reg 14] ;;
  .assign 18 (.bin .add (.reg 14) (.bin .mul (.const 2) (.bin .mul (.reg 1) (.reg 2)))) ;;
  .assign 19 (.bin .sub (.reg 17) (.reg 18)) ;;
  .call 20 sec5 [.reg 0, .reg 1, .reg 2, .reg 3, .bin .add (.reg 9) (.const 2), .reg 17] ;;
  .assign 21 (.bin .add (.reg 17) (.bin .mul (.const 2) (.bin .mul (.bin .mul (.reg 1) (.reg 2)) (.reg 3)))) ;;
  .assign 22 (.bin .sub (.reg 20) (.reg 21))

theorem buildTopPackSec345_noRand (sec3 sec4 sec5 : ℕ) :
    (buildTopPackSec345 sec3 sec4 sec5).NoRand := by
  simp [buildTopPackSec345, Stmt.NoRand]

/-- Arguments:
`[table, D, P, twoPowB, x, b, rootGraph, ownersAddr, origM, tail0, h]`. -/
def buildTopPackAll (numConn labels sec3 sec4 sec5 finish : ℕ) : Stmt :=
  buildTopPackSec02 numConn labels ;;
  buildTopPackSec345 sec3 sec4 sec5 ;;
  buildTopStoreDir6 ;;
  .call 23 finish [.reg 20, .bin .add (.reg 20) (.const 12), .reg 10] ;;
  .ret (.reg 23)

theorem buildTopPackAll_noRand (numConn labels sec3 sec4 sec5 finish : ℕ) :
    (buildTopPackAll numConn labels sec3 sec4 sec5 finish).NoRand := by
  simp [buildTopPackAll, buildTopPackSec02_noRand, buildTopPackSec345_noRand,
    buildTopStoreDir6_noRand, Stmt.NoRand]

/-! ### Constant-size-state chaining combinators (prevent `{ st with ... }` blowup) -/

private lemma runs_seq_assign_clean {w r v c₁ c₂ : ℕ} {e : Expr} {s₂ : Stmt} {p : Program}
    {ω : ℕ → Bool} {st : State} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (h₂ : ∀ st' : State, st'.mem = st.mem → st'.regs r = v →
      (∀ j, j ≠ r → st'.regs j = st.regs j) →
      ∃ o t c, Runs w p ω s₂ st' o t c ∧ Q o t ∧ c₁ + e.size + 2 + c ≤ c₂) :
    ∃ o t c, Runs w p ω (.seq (.assign r e) s₂) st o t c ∧ Q o t ∧ c₁ + c ≤ c₂ :=
  runs_seq_assign_le he (h₂ { st with regs := Function.update st.regs r v } rfl
    (Function.update_self r v st.regs) (fun _ hj => Function.update_of_ne hj v st.regs))

private lemma runs_seq_store_clean {w a v c₁ c₂ : ℕ} {ae ve : Expr} {s₂ : Stmt} {p : Program}
    {ω : ℕ → Bool} {st : State} {Q : Outcome → State → Prop}
    (ha : ae.eval w st = some a) (hv : ve.eval w st = some v)
    (h₂ : ∀ st' : State, st'.regs = st.regs → st'.mem a = v →
      (∀ y, y ≠ a → st'.mem y = st.mem y) →
      ∃ o t c, Runs w p ω s₂ st' o t c ∧ Q o t ∧ c₁ + ae.size + ve.size + 2 + c ≤ c₂) :
    ∃ o t c, Runs w p ω (.seq (.store ae ve) s₂) st o t c ∧ Q o t ∧ c₁ + c ≤ c₂ :=
  runs_seq_store_le ha hv (h₂ { st with mem := Function.update st.mem a v } rfl
    (Function.update_self a v st.mem) (fun _ hy => Function.update_of_ne hy v st.mem))

private lemma runs_seq_call_clean {w r f c₁ c₂ : ℕ} {es : List Expr} {vs : List ℕ}
    {s₂ : Stmt} {p : Program} {ω : ℕ → Bool} {st : State} {C : Contract}
    {Q : Outcome → State → Prop}
    (hc : MeetsContract w p f C) (he : evalArgs w st es = some vs)
    (hw : ∀ v ∈ vs, v < 2 ^ w) (hpre : C.pre vs st.mem)
    (h₂ : ∀ v (st' : State), C.post vs st.mem v st'.mem → st'.regs r = v →
      (∀ j, j ≠ r → st'.regs j = st.regs j) →
      ∃ o t c, Runs w p ω s₂ st' o t c ∧ Q o t ∧
        c₁ + argsSize es + C.cost vs st.mem + 2 + c ≤ c₂) :
    ∃ o t c, Runs w p ω (.seq (.call r f es) s₂) st o t c ∧ Q o t ∧ c₁ + c ≤ c₂ :=
  runs_seq_call_le hc he hw hpre fun v mem' pos' hpost =>
    h₂ v { st with mem := mem', regs := Function.update st.regs r v, pos := pos' }
      hpost (Function.update_self r v st.regs) (fun _ hj => Function.update_of_ne hj v st.regs)

private lemma packAll_sections_sum_le (S : StaticData) :
    (S.sections.getD 0 []).length + (S.sections.getD 1 []).length +
      (S.sections.getD 2 []).length + (S.sections.getD 3 []).length +
      (S.sections.getD 4 []).length + (S.sections.getD 5 []).length ≤ S.encode.length := by
  have hEnc : S.encode.length = 7 + (csrData 6 (buildTopSections S)).length := by
    rw [← buildTopSections_encode, csrList, List.length_append, length_csrOffsets]
  have hData : (csrData 6 (buildTopSections S)).length =
      (S.sections.getD 0 []).length + (S.sections.getD 1 []).length +
      (S.sections.getD 2 []).length + (S.sections.getD 3 []).length +
      (S.sections.getD 4 []).length + (S.sections.getD 5 []).length := by
    simp [csrData, buildTopSections, List.range_succ]
    omega
  omega

private lemma storeDir6_triple {w ctx tail0 ownersAddr P rootM s3 l3 s4 l4 s5 l5 h : ℕ}
    {p : Program} {st : State}
    (r2 : st.regs 2 = P) (r7 : st.regs 7 = ownersAddr) (r9 : st.regs 9 = tail0)
    (r10 : st.regs 10 = h)
    (r12 : st.regs 12 = rootM) (r15 : st.regs 15 = s3) (r16 : st.regs 16 = l3)
    (r18 : st.regs 18 = s4) (r19 : st.regs 19 = l4) (r20 : st.regs 20 = ctx)
    (r21 : st.regs 21 = s5) (r22 : st.regs 22 = l5)
    (hctx : ctx + 12 < 2 ^ w) (ht6 : tail0 + 6 < 2 ^ w) (h13 : 13 < 2 ^ w) :
    Triple w p (fun t => t = st) buildTopStoreDir6
      (normalPost fun t =>
        t.regs 10 = h ∧ t.regs 20 = ctx ∧
        t.mem ctx = tail0 + 3 ∧ t.mem (ctx + 1) = 3 ∧
        t.mem (ctx + 2) = ownersAddr ∧ t.mem (ctx + 3) = P ∧
        t.mem (ctx + 4) = tail0 + 6 ∧ t.mem (ctx + 5) = rootM ∧
        t.mem (ctx + 6) = s3 ∧ t.mem (ctx + 7) = l3 ∧
        t.mem (ctx + 8) = s4 ∧ t.mem (ctx + 9) = l4 ∧
        t.mem (ctx + 10) = s5 ∧ t.mem (ctx + 11) = l5 ∧
        ∀ y, y < ctx ∨ ctx + 12 ≤ y → t.mem y = st.mem y)
      (fun _ => 120) := by
  intro st' ω hst'
  subst st'
  have hc (k : ℕ) (hk : k < 12) : k < 2 ^ w := by omega
  have ha (k : ℕ) (hk : k < 12) : ctx + k < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold buildTopStoreDir6
  refine runs_seq_store_clean (Expr.eval_reg_of_eq r20)
    (Expr.eval_add (Expr.eval_reg_of_eq r9) (Expr.eval_const (hc 3 (by decide))) (by omega)) ?_
  intro s1 hr1 hm1_0 hfr1
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (hr1.symm ▸ r20)) (Expr.eval_const (hc 1 (by decide))) (ha 1 (by decide)))
    (Expr.eval_const (hc 3 (by decide))) ?_
  intro s2 hr2 hm2_1 hfr2
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq ((hr2.trans hr1).symm ▸ r20)) (Expr.eval_const (hc 2 (by decide))) (ha 2 (by decide)))
    (Expr.eval_reg_of_eq ((hr2.trans hr1).symm ▸ r7)) ?_
  intro s3s hr3 hm3_2 hfr3
  have hr3' : s3s.regs = st.regs := hr3.trans (hr2.trans hr1)
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (hr3'.symm ▸ r20)) (Expr.eval_const (hc 3 (by decide))) (ha 3 (by decide)))
    (Expr.eval_reg_of_eq (hr3'.symm ▸ r2)) ?_
  intro s4s hr4 hm4_3 hfr4
  have hr4' : s4s.regs = st.regs := hr4.trans hr3'
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (hr4'.symm ▸ r20)) (Expr.eval_const (hc 4 (by decide))) (ha 4 (by decide)))
    (Expr.eval_add (Expr.eval_reg_of_eq (hr4'.symm ▸ r9)) (Expr.eval_const (hc 6 (by decide))) ht6) ?_
  intro s5s hr5 hm5_4 hfr5
  have hr5' : s5s.regs = st.regs := hr5.trans hr4'
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (hr5'.symm ▸ r20)) (Expr.eval_const (hc 5 (by decide))) (ha 5 (by decide)))
    (Expr.eval_reg_of_eq (hr5'.symm ▸ r12)) ?_
  intro s6s hr6 hm6_5 hfr6
  have hr6' : s6s.regs = st.regs := hr6.trans hr5'
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (hr6'.symm ▸ r20)) (Expr.eval_const (hc 6 (by decide))) (ha 6 (by decide)))
    (Expr.eval_reg_of_eq (hr6'.symm ▸ r15)) ?_
  intro s7s hr7 hm7_6 hfr7
  have hr7' : s7s.regs = st.regs := hr7.trans hr6'
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (hr7'.symm ▸ r20)) (Expr.eval_const (hc 7 (by decide))) (ha 7 (by decide)))
    (Expr.eval_reg_of_eq (hr7'.symm ▸ r16)) ?_
  intro s8s hr8 hm8_7 hfr8
  have hr8' : s8s.regs = st.regs := hr8.trans hr7'
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (hr8'.symm ▸ r20)) (Expr.eval_const (hc 8 (by decide))) (ha 8 (by decide)))
    (Expr.eval_reg_of_eq (hr8'.symm ▸ r18)) ?_
  intro s9s hr9 hm9_8 hfr9
  have hr9' : s9s.regs = st.regs := hr9.trans hr8'
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (hr9'.symm ▸ r20)) (Expr.eval_const (hc 9 (by decide))) (ha 9 (by decide)))
    (Expr.eval_reg_of_eq (hr9'.symm ▸ r19)) ?_
  intro s10s hr10 hm10_9 hfr10
  have hr10' : s10s.regs = st.regs := hr10.trans hr9'
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (hr10'.symm ▸ r20)) (Expr.eval_const (hc 10 (by decide))) (ha 10 (by decide)))
    (Expr.eval_reg_of_eq (hr10'.symm ▸ r21)) ?_
  intro s11s hr11 hm11_10 hfr11
  have hr11' : s11s.regs = st.regs := hr11.trans hr10'
  refine runs_store_le
    (Expr.eval_add (Expr.eval_reg_of_eq (hr11'.symm ▸ r20)) (Expr.eval_const (hc 11 (by decide))) (ha 11 (by decide)))
    (Expr.eval_reg_of_eq (hr11'.symm ▸ r22)) ?_ ?_
  · have hmem (y : ℕ) (hy : y ≠ ctx + 11) : Function.update s11s.mem (ctx + 11) l5 y = s11s.mem y :=
      Function.update_of_ne hy _ _
    refine ⟨hr11'.symm ▸ r10, hr11'.symm ▸ r20, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      Function.update_self _ _ _, ?_⟩
    · dsimp only; rw [hmem _ (by omega), hfr11 _ (by omega), hfr10 _ (by omega), hfr9 _ (by omega),
        hfr8 _ (by omega), hfr7 _ (by omega), hfr6 _ (by omega), hfr5 _ (by omega),
        hfr4 _ (by omega), hfr3 _ (by omega), hfr2 _ (by omega), hm1_0]
    · dsimp only; rw [hmem _ (by omega), hfr11 _ (by omega), hfr10 _ (by omega), hfr9 _ (by omega),
        hfr8 _ (by omega), hfr7 _ (by omega), hfr6 _ (by omega), hfr5 _ (by omega),
        hfr4 _ (by omega), hfr3 _ (by omega), hm2_1]
    · dsimp only; rw [hmem _ (by omega), hfr11 _ (by omega), hfr10 _ (by omega), hfr9 _ (by omega),
        hfr8 _ (by omega), hfr7 _ (by omega), hfr6 _ (by omega), hfr5 _ (by omega),
        hfr4 _ (by omega), hm3_2]
    · dsimp only; rw [hmem _ (by omega), hfr11 _ (by omega), hfr10 _ (by omega), hfr9 _ (by omega),
        hfr8 _ (by omega), hfr7 _ (by omega), hfr6 _ (by omega), hfr5 _ (by omega), hm4_3]
    · dsimp only; rw [hmem _ (by omega), hfr11 _ (by omega), hfr10 _ (by omega), hfr9 _ (by omega),
        hfr8 _ (by omega), hfr7 _ (by omega), hfr6 _ (by omega), hm5_4]
    · dsimp only; rw [hmem _ (by omega), hfr11 _ (by omega), hfr10 _ (by omega), hfr9 _ (by omega),
        hfr8 _ (by omega), hfr7 _ (by omega), hm6_5]
    · dsimp only; rw [hmem _ (by omega), hfr11 _ (by omega), hfr10 _ (by omega), hfr9 _ (by omega),
        hfr8 _ (by omega), hm7_6]
    · dsimp only; rw [hmem _ (by omega), hfr11 _ (by omega), hfr10 _ (by omega), hfr9 _ (by omega), hm8_7]
    · dsimp only; rw [hmem _ (by omega), hfr11 _ (by omega), hfr10 _ (by omega), hm9_8]
    · dsimp only; rw [hmem _ (by omega), hfr11 _ (by omega), hm10_9]
    · dsimp only; rw [hmem _ (by omega), hm11_10]
    · intro y hy
      dsimp only
      rw [hmem _ (by omega), hfr11 _ (by omega), hfr10 _ (by omega), hfr9 _ (by omega),
        hfr8 _ (by omega), hfr7 _ (by omega), hfr6 _ (by omega), hfr5 _ (by omega),
        hfr4 _ (by omega), hfr3 _ (by omega), hfr2 _ (by omega), hfr1 _ (by omega)]
  · simp [Expr.size]

private lemma packSec02_triple
    {w numConn labels iota fill D x b rootGraph origM tail0 : ℕ}
    {root : Graph} {p : Program} {st : State}
    (hnc : p.procs[numConn]? = some buildTopNumConn)
    (hlab : p.procs[labels]? = some (buildTopLabels iota fill))
    (hiota : p.HasAt iota [LowStretch.iotaP])
    (hfill : p.procs[fill]? = some initFillWord)
    (r1 : st.regs 1 = D) (r4 : st.regs 4 = x) (r5 : st.regs 5 = b)
    (r6 : st.regs 6 = rootGraph) (r8 : st.regs 8 = origM) (r9 : st.regs 9 = tail0)
    (hxpos : 0 < x) (hbpos : 0 < b) (hbx : b ≤ x) (hDeq : D = leafDepth x b)
    (hRootM_ge : origM ≤ root.m)
    (hRootAt : GraphAt st.mem rootGraph root) (hRootEnd : rootGraph + root.encode.length ≤ tail0)
    (hZero : ZeroFrom st.mem tail0)
    (h2x : 2 ^ x < 2 ^ w) (hDPB : D * 2 ^ x * 2 ^ b < 2 ^ w)
    (hdir3_w : tail0 + 6 + root.m + 1 < 2 ^ w) (h13 : 13 < 2 ^ w) :
    Triple w p (fun t => t = st) (buildTopPackSec02 numConn labels)
      (normalPost fun t =>
        (∀ j < 11, t.regs j = st.regs j) ∧
        t.regs 12 = root.m ∧ t.regs 13 = tail0 + 6 + root.m ∧
        ListAt t.mem (tail0 + 3) [x, b, buildTopNumConnVal x b] ∧
        ListAt t.mem (tail0 + 6) (buildTopLabelWords origM root.m) ∧
        ListAt t.mem tail0 [0, 0] ∧
        ListAt t.mem (tail0 + 2) [0] ∧
        ZeroFrom t.mem (tail0 + 6 + root.m) ∧
        ∀ y < tail0 + 3, t.mem y = st.mem y)
      (fun _ => 70 * D + 40 * root.m + 180) := by
  intro st' ω hst'
  subst st'
  have h1 : 1 < 2 ^ w := by omega
  have h3 : 3 < 2 ^ w := by omega
  have h4 : 4 < 2 ^ w := by omega
  have h5 : 5 < 2 ^ w := by omega
  have h6 : 6 < 2 ^ w := by omega
  have hx_w : x < 2 ^ w := x.lt_two_pow_self.trans h2x
  have hb_w : b < 2 ^ w := hbx.trans_lt hx_w
  have hD_w : D < 2 ^ w := by
    have : D ≤ D * (2 ^ x * 2 ^ b) := Nat.le_mul_of_pos_right D (Nat.mul_pos (Nat.two_pow_pos x) (Nat.two_pow_pos b))
    have hmul : D * (2 ^ x * 2 ^ b) = D * 2 ^ x * 2 ^ b := by ring
    omega
  have hRootM_mem : st.mem (rootGraph + 1) = root.m := by
    have hLen := graph_encode_length root
    have h := hRootAt 1 (by omega)
    simpa [Graph.encode] using h
  refine runs_start_le ?_
  unfold buildTopPackSec02
  refine runs_seq_call_clean (buildTopNumConn_meetsContract (w := w) (x := x) (b := b) hnc)
    (vs := [x, b, D]) (by simp [evalArgs, Expr.eval, r1, r4, r5])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> assumption)
    ⟨by rw [hDeq], hxpos, hbpos, hbx, h2x, by rw [← hDeq]; exact hDPB⟩ ?_
  intro nc st1 ⟨hnc_eq, hmem1⟩ h1_r11 h1_reg
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (v := tail0) ((h1_reg 9 (by decide)).trans r9)) (Expr.eval_const h3) (by omega))
    (Expr.eval_reg_of_eq (v := x) ((h1_reg 4 (by decide)).trans r4)) ?_
  intro st2a hr2a hm2a_3 hfr2a
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (v := tail0) (by rw [hr2a]; exact (h1_reg 9 (by decide)).trans r9))
      (Expr.eval_const h4) (by omega))
    (Expr.eval_reg_of_eq (v := b) (by rw [hr2a]; exact (h1_reg 5 (by decide)).trans r5)) ?_
  intro st2b hr2b hm2b_4 hfr2b
  refine runs_seq_store_clean
    (Expr.eval_add (Expr.eval_reg_of_eq (v := tail0) (by rw [hr2b, hr2a]; exact (h1_reg 9 (by decide)).trans r9))
      (Expr.eval_const h5) (by omega))
    (Expr.eval_reg_of_eq (v := nc) (by rw [hr2b, hr2a]; exact h1_r11)) ?_
  intro st2 hr2 hm2_5 hfr2
  have hr2_all : st2.regs = st1.regs := hr2.trans (hr2b.trans hr2a)
  have hFr₂ : ∀ y, y < tail0 + 3 ∨ tail0 + 6 ≤ y → st2.mem y = st.mem y := fun y hy =>
    (hfr2 y (by omega)).trans ((hfr2b y (by omega)).trans ((hfr2a y (by omega)).trans (by rw [hmem1])))
  have hSec0_at₂ : ListAt st2.mem (tail0 + 3) [x, b, buildTopNumConnVal x b] := by
    rw [← hnc_eq]
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    match i with
    | 0 => exact (hfr2 _ (by omega)).trans ((hfr2b _ (by omega)).trans hm2a_3)
    | 1 => exact (hfr2 _ (by omega)).trans (by simpa [show tail0 + 3 + 1 = tail0 + 4 by omega] using hm2b_4)
    | 2 => simpa [show tail0 + 3 + 2 = tail0 + 5 by omega] using hm2_5
    | i + 3 => omega
  have hRootM_st2 : st2.mem (rootGraph + 1) = root.m := by
    have hLen := graph_encode_length root
    rw [hFr₂ (rootGraph + 1) (.inl (by omega)), hRootM_mem]
  refine runs_seq_assign_clean (v := root.m)
    (Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (v := rootGraph) (by rw [hr2_all]; exact (h1_reg 6 (by decide)).trans r6))
      (Expr.eval_const h1) (by omega)) hRootM_st2) ?_
  intro st2c hmem2c h2c_r12 h2c_reg
  refine runs_call_le (buildTopLabels_meetsContract (w := w) hlab hiota hfill)
    (vs := [origM, root.m, tail0 + 6])
    (by
      have hr8 : st2c.regs 8 = origM := (h2c_reg 8 (by decide)).trans (by rw [hr2_all]; exact (h1_reg 8 (by decide)).trans r8)
      have hr9 : st2c.regs 9 = tail0 := (h2c_reg 9 (by decide)).trans (by rw [hr2_all]; exact (h1_reg 9 (by decide)).trans r9)
      simp [evalArgs, Expr.eval, BinOp.eval, hr8, h2c_r12, hr9, h6, show tail0 + 6 < 2 ^ w by omega])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨origM, root.m, tail0 + 6, rfl, hRootM_ge, hdir3_w⟩ ?_
  intro v3 mem3 pos3 hPost3
  obtain ⟨m', rm', dst', ha3, hv3, hLabAt, hFr3⟩ := hPost3
  simp only [List.cons.injEq, and_true] at ha3
  obtain ⟨rfl, rfl, rfl⟩ := ha3
  have hFr3_below : ∀ y < tail0 + 6, mem3 y = st2.mem y := fun y hy =>
    (hFr3 y (.inl hy)).trans (by rw [hmem2c])
  have hFr3_orig : ∀ y < tail0 + 3, mem3 y = st.mem y := fun y hy =>
    (hFr3_below y (by omega)).trans (hFr₂ y (.inl hy))
  refine ⟨⟨?_, ?_, ?_, ?_, hLabAt, ?_, ?_, ?_, hFr3_orig⟩, ?_⟩
  · intro j hj
    dsimp only
    rw [Function.update_of_ne (by omega)]
    exact (h2c_reg j (by omega)).trans (by rw [hr2_all]; exact h1_reg j (by omega))
  · dsimp only; rw [Function.update_of_ne (by decide)]; exact h2c_r12
  · dsimp only; rw [Function.update_self]; exact hv3
  · intro i hi
    have hi3 : i < 3 := by simpa using hi
    exact (hFr3_below (tail0 + 3 + i) (by omega)).trans (hSec0_at₂ i hi)
  · intro i hi
    dsimp only
    have hi2 : i < 2 := by simpa using hi
    rw [hFr3_orig (tail0 + i) (by omega), hZero (tail0 + i) (by omega)]
    match i with | 0 => rfl | 1 => rfl | i + 2 => omega
  · intro i hi
    dsimp only
    have hi1 : i < 1 := by simpa using hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [hFr3_orig (tail0 + 2 + 0) (by omega), hZero (tail0 + 2 + 0) (by omega)]
    rfl
  · intro y hy
    dsimp only
    rw [hFr3 y (.inr (by omega)), hmem2c, hFr₂ y (.inr (by omega)), hZero y (by omega)]
  · simp only [buildTopNumConnContract, buildTopLabelsContract, Expr.size, argsSize,
      List.getD_cons_zero, List.getD_cons_succ, hDeq]
    omega

private lemma packSec345_triple
    {w sec3p dir3p sec4p dir4p sec5p dir5p gather row copy span read seek
      table D x b rootGraph tail0 dir3 : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ}
    {p : Program} {st : State}
    (hs3 : p.procs[sec3p]? = some (buildTopSec3 dir3p gather))
    (hd3 : p.procs[dir3p]? = some (buildTopSec3Dir span))
    (hs4 : p.procs[sec4p]? = some (buildTopSec4 dir4p gather))
    (hd4 : p.procs[dir4p]? = some (buildTopSec4Dir span))
    (hs5 : p.procs[sec5p]? = some (buildTopSec5 dir5p gather))
    (hd5 : p.procs[dir5p]? = some (buildTopSec5Dir span))
    (hgat : p.procs[gather]? = some (initCSRWrite row))
    (hrow : p.procs[row]? = some (buildTopRow copy))
    (hcopy : p.procs[copy]? = some buildCopyProc)
    (hspan : p.procs[span]? = some (buildTopReplySpan read))
    (hread : p.procs[read]? = some (buildTopReplyRead seek))
    (hseek : p.procs[seek]? = some initCSRSeek)
    (r0 : st.regs 0 = table) (r1 : st.regs 1 = D) (r2 : st.regs 2 = 2 ^ x)
    (r3 : st.regs 3 = 2 ^ b) (r6 : st.regs 6 = rootGraph) (r9 : st.regs 9 = tail0)
    (r13 : st.regs 13 = dir3)
    (hD1 : 1 ≤ D) (hbx : b ≤ x) (htail_le : tail0 + 6 ≤ dir3)
    (hRep : BuildTopRepliesInMem table D x b reply replyAddr dir3 st.mem)
    (hRootAt : GraphAt st.mem rootGraph root) (hRootEnd : rootGraph + root.encode.length ≤ dir3)
    (hEmpG : ListAt st.mem tail0 [0, 0]) (hEmpC : ListAt st.mem (tail0 + 2) [0])
    (hZero : ZeroFrom st.mem dir3)
    (htable_w : table < 2 ^ w)
    (h13 : 13 < 2 ^ w) (h2Pw : 2 * 2 ^ x < 2 ^ w)
    (hRoom :
      let sec3 := csrList ((D + 1) * 2 ^ x) (buildTopSec3Rows x b root reply)
      let sec4 := csrList (D * 2 ^ x) (buildTopSec4Rows x b root reply)
      let sec5 := csrList (D * 2 ^ x * 2 ^ b) (buildTopSec5Rows x b root reply)
      dir3 + 2 * ((D + 1) * 2 ^ x) + sec3.length + 2 * (D * 2 ^ x) + sec4.length +
        2 * (D * 2 ^ x * 2 ^ b) + sec5.length < 2 ^ w) :
    let P := 2 ^ x
    let twoPowB := 2 ^ b
    let sec3 := csrList ((D + 1) * P) (buildTopSec3Rows x b root reply)
    let sec4 := csrList (D * P) (buildTopSec4Rows x b root reply)
    let sec5 := csrList (D * P * twoPowB) (buildTopSec5Rows x b root reply)
    let s3Addr := dir3 + 2 * ((D + 1) * P)
    let dir4 := s3Addr + sec3.length
    let s4Addr := dir4 + 2 * (D * P)
    let dir5 := s4Addr + sec4.length
    let s5Addr := dir5 + 2 * (D * P * twoPowB)
    let ctx := s5Addr + sec5.length
    Triple w p (fun t => t = st) (buildTopPackSec345 sec3p sec4p sec5p)
      (normalPost fun t =>
        (∀ j < 13, t.regs j = st.regs j) ∧
        t.regs 15 = s3Addr ∧ t.regs 16 = sec3.length ∧
        t.regs 18 = s4Addr ∧ t.regs 19 = sec4.length ∧
        t.regs 20 = ctx ∧ t.regs 21 = s5Addr ∧ t.regs 22 = sec5.length ∧
        ListAt t.mem s3Addr sec3 ∧ ListAt t.mem s4Addr sec4 ∧ ListAt t.mem s5Addr sec5 ∧
        ZeroFrom t.mem ctx ∧
        ∀ y < dir3, t.mem y = st.mem y)
      (fun _ => 17 * (sec3.length + sec4.length + sec5.length) +
        640 * ((D + 1) * P) + 360 * (D * P * twoPowB) + 520) := by
  dsimp only
  intro st' ω hst'
  subst st'
  set P := 2 ^ x
  set twoPowB := 2 ^ b
  set sec3 := csrList ((D + 1) * P) (buildTopSec3Rows x b root reply)
  set sec4 := csrList (D * P) (buildTopSec4Rows x b root reply)
  set sec5 := csrList (D * P * twoPowB) (buildTopSec5Rows x b root reply)
  set s3Addr := dir3 + 2 * ((D + 1) * P)
  set dir4 := s3Addr + sec3.length
  set s4Addr := dir4 + 2 * (D * P)
  set dir5 := s4Addr + sec4.length
  set s5Addr := dir5 + 2 * (D * P * twoPowB)
  set ctx := s5Addr + sec5.length
  have hCtxW : ctx < 2 ^ w := hRoom
  have hPpos : 0 < P := Nat.two_pow_pos x
  have hD1_le : D + 1 ≤ (D + 1) * P := Nat.le_mul_of_pos_right (D + 1) hPpos
  have hDP_le : D * P ≤ (D + 1) * P := Nat.mul_le_mul_right P (Nat.le_succ D)
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hB_le : twoPowB ≤ P := Nat.pow_le_pow_right (by decide) hbx
  have hPw : P < 2 ^ w := by omega
  have h2Bw : twoPowB < 2 ^ w := lt_of_le_of_lt hB_le hPw
  -- Simple address ordering and word-bound facts (avoiding repeated heavy `omega` calls)
  have h_dir3_s3 : dir3 ≤ s3Addr := Nat.le_add_right _ _
  have h_s3_dir4 : s3Addr ≤ dir4 := Nat.le_add_right _ _
  have h_dir3_dir4 : dir3 ≤ dir4 := h_dir3_s3.trans h_s3_dir4
  have h_dir4_s4 : dir4 ≤ s4Addr := Nat.le_add_right _ _
  have h_s4_dir5 : s4Addr ≤ dir5 := Nat.le_add_right _ _
  have h_dir4_dir5 : dir4 ≤ dir5 := h_dir4_s4.trans h_s4_dir5
  have h_dir5_s5 : dir5 ≤ s5Addr := Nat.le_add_right _ _
  have h_s5_ctx : s5Addr ≤ ctx := Nat.le_add_right _ _
  have h_dir5_ctx : dir5 ≤ ctx := h_dir5_s5.trans h_s5_ctx
  have h_dir4_ctx : dir4 ≤ ctx := h_dir4_dir5.trans h_dir5_ctx
  have h_dir3_ctx : dir3 ≤ ctx := h_dir3_dir4.trans h_dir4_ctx
  have h_dir5_w : dir5 < 2 ^ w := lt_of_le_of_lt h_dir5_ctx hCtxW
  have h_s5_w : s5Addr < 2 ^ w := lt_of_le_of_lt h_s5_ctx hCtxW
  have h_dir4_w : dir4 < 2 ^ w := lt_of_le_of_lt h_dir4_ctx hCtxW
  have h_s4_w : s4Addr < 2 ^ w := lt_of_le_of_lt h_s4_dir5 h_dir5_w
  have h_dir3_w : dir3 < 2 ^ w := lt_of_le_of_lt h_dir3_ctx hCtxW
  have h_s3_w : s3Addr < 2 ^ w := lt_of_le_of_lt h_s3_dir4 h_dir4_w
  have h_tail0_w : tail0 < 2 ^ w := lt_of_le_of_lt (by omega : tail0 ≤ dir3) h_dir3_w
  have h_tail2_w : tail0 + 2 < 2 ^ w := lt_of_le_of_lt (by omega : tail0 + 2 ≤ dir3) h_dir3_w
  have h_rootG_w : rootGraph < 2 ^ w := lt_of_le_of_lt ((Nat.le_add_right _ _).trans hRootEnd) h_dir3_w
  have h_2D1P_w : 2 * ((D + 1) * P) < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ dir3) h_s3_w
  have h_D1P_w : (D + 1) * P < 2 ^ w := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by decide)) h_2D1P_w
  have h_D1_w : D + 1 < 2 ^ w := lt_of_le_of_lt hD1_le h_D1P_w
  have h_D_w : D < 2 ^ w := lt_of_le_of_lt (Nat.le_succ D) h_D1_w
  have h_2DP_w : 2 * (D * P) < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ dir4) h_s4_w
  have h_DP_w : D * P < 2 ^ w := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by decide)) h_2DP_w
  have h_2DPB_w : 2 * (D * P * twoPowB) < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ dir5) h_s5_w
  have h_DPB_w : D * P * twoPowB < 2 ^ w := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by decide)) h_2DPB_w
  refine runs_start_le ?_
  unfold buildTopPackSec345
  -- sec3
  refine runs_seq_call_clean
    (buildTopSec3_meetsContract (w := w) (table := table) (D := D) (x := x) (b := b)
      (rootGraph := rootGraph) (emptyGraph := tail0) (dir := dir3)
      (root := root) (reply := reply) (replyAddr := replyAddr)
      hs3 hd3 hgat hrow hcopy hspan hread hseek)
    (vs := [table, D, P, rootGraph, tail0, dir3])
    (by simp [evalArgs, Expr.eval, r0, r1, r2, r6, r9, r13, P])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · exact htable_w
      · exact h_D_w
      · exact hPw
      · exact h_rootG_w
      · exact h_tail0_w
      · exact h_dir3_w)
    ⟨rfl, hRep, hRootAt, hRootEnd, hEmpG, le_trans (by omega) htail_le, hZero, h_dir4_w, h13⟩ ?_
  intro v4 st4 ⟨_, hv4, hSec3At₄, hZero₄, hFr₄⟩ h4_r14 h4_reg
  have hv4_eq : v4 = dir4 := hv4
  subst hv4_eq
  have h4_low : ∀ j < 14, st4.regs j = st.regs j := fun j hj => h4_reg j (Nat.ne_of_lt hj)
  refine runs_seq_assign_clean (v := s3Addr)
    (Expr.eval_add (Expr.eval_reg_of_eq ((h4_low 13 (by decide)).trans r13))
      (Expr.eval_mul (Expr.eval_const h2)
        (Expr.eval_mul (Expr.eval_add (Expr.eval_reg_of_eq ((h4_low 1 (by decide)).trans r1))
          (Expr.eval_const h1) h_D1_w)
          (Expr.eval_reg_of_eq ((h4_low 2 (by decide)).trans r2)) h_D1P_w) h_2D1P_w) h_s3_w) ?_
  intro st4a hmem4a h4a_r15 h4a_reg
  refine runs_seq_assign_clean (v := sec3.length)
    (Expr.eval_eq_of_eq
      (Expr.eval_sub (Expr.eval_reg_of_eq ((h4a_reg 14 (by decide)).trans h4_r14))
        (Expr.eval_reg_of_eq h4a_r15) h_dir4_w)
      (Nat.add_sub_cancel_left s3Addr sec3.length)) ?_
  intro st4b hmem4b h4b_r16 h4b_reg
  have h4b_mem : st4b.mem = st4.mem := hmem4b.trans hmem4a
  have h4b_low : ∀ j < 14, st4b.regs j = st.regs j := fun j hj =>
    (h4b_reg j (Nat.ne_of_lt (lt_trans hj (by decide)))).trans
      ((h4a_reg j (Nat.ne_of_lt (lt_trans hj (by decide)))).trans (h4_low j hj))
  have h4b_r14 : st4b.regs 14 = dir4 := (h4b_reg 14 (by decide)).trans ((h4a_reg 14 (by decide)).trans h4_r14)
  have h4b_r15 : st4b.regs 15 = s3Addr := (h4b_reg 15 (by decide)).trans h4a_r15
  have hRep₄ : BuildTopRepliesInMem table D x b reply replyAddr dir4 st4b.mem := by
    rw [h4b_mem]; exact hRep.mono h_dir3_dir4 (fun y hy => hFr₄ y hy)
  have hEmpC₄ : ListAt st4b.mem (tail0 + 2) [0] := fun i hi => by
    rw [h4b_mem]; have hi1 : i < 1 := by simpa using hi
    exact (hFr₄ (tail0 + 2 + i) (by omega)).trans (hEmpC i hi)
  -- sec4
  refine runs_seq_call_clean
    (buildTopSec4_meetsContract (w := w) (table := table) (D := D) (x := x) (b := b)
      (emptyCSR := tail0 + 2) (dir := dir4) (root := root) (reply := reply) (replyAddr := replyAddr)
      hs4 hd4 hgat hrow hcopy hspan hread hseek)
    (vs := [table, D, P, tail0 + 2, dir4])
    (by
      have hr0 : st4b.regs 0 = table := (h4b_low 0 (by decide)).trans r0
      have hr1 : st4b.regs 1 = D := (h4b_low 1 (by decide)).trans r1
      have hr2 : st4b.regs 2 = P := (h4b_low 2 (by decide)).trans r2
      have hr9 : st4b.regs 9 = tail0 := (h4b_low 9 (by decide)).trans r9
      simp [evalArgs, Expr.eval, BinOp.eval, hr0, hr1, hr2, hr9, h4b_r14, h2, h_tail2_w])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact htable_w
      · exact h_D_w
      · exact hPw
      · exact h_tail2_w
      · exact h_dir4_w)
    ⟨rfl, hRep₄, hEmpC₄, le_trans (by omega) (htail_le.trans h_dir3_dir4), h4b_mem ▸ hZero₄,
      h_dir5_w, h13, hPw⟩ ?_
  intro v5 st5 ⟨_, hv5, hSec4At₅, hZero₅, hFr₅⟩ h5_r17 h5_reg
  have hv5_eq : v5 = dir5 := hv5
  subst hv5_eq
  have hFr₅' : ∀ y < dir4, st5.mem y = st4.mem y := fun y hy => (hFr₅ y hy).trans (by rw [h4b_mem])
  have h5_low : ∀ j < 14, st5.regs j = st.regs j := fun j hj =>
    (h5_reg j (Nat.ne_of_lt (lt_trans hj (by decide)))).trans (h4b_low j hj)
  have h5_r14 : st5.regs 14 = dir4 := (h5_reg 14 (by decide)).trans h4b_r14
  have h5_r15 : st5.regs 15 = s3Addr := (h5_reg 15 (by decide)).trans h4b_r15
  have h5_r16 : st5.regs 16 = sec3.length := (h5_reg 16 (by decide)).trans h4b_r16
  refine runs_seq_assign_clean (v := s4Addr)
    (Expr.eval_add (Expr.eval_reg_of_eq h5_r14)
      (Expr.eval_mul (Expr.eval_const h2)
        (Expr.eval_mul (Expr.eval_reg_of_eq ((h5_low 1 (by decide)).trans r1))
          (Expr.eval_reg_of_eq ((h5_low 2 (by decide)).trans r2)) h_DP_w) h_2DP_w) h_s4_w) ?_
  intro st5a hmem5a h5a_r18 h5a_reg
  refine runs_seq_assign_clean (v := sec4.length)
    (Expr.eval_eq_of_eq
      (Expr.eval_sub (Expr.eval_reg_of_eq ((h5a_reg 17 (by decide)).trans h5_r17))
        (Expr.eval_reg_of_eq h5a_r18) h_dir5_w)
      (Nat.add_sub_cancel_left s4Addr sec4.length)) ?_
  intro st5b hmem5b h5b_r19 h5b_reg
  have h5b_mem : st5b.mem = st5.mem := hmem5b.trans hmem5a
  have h5b_low : ∀ j < 14, st5b.regs j = st.regs j := fun j hj =>
    (h5b_reg j (Nat.ne_of_lt (lt_trans hj (by decide)))).trans
      ((h5a_reg j (Nat.ne_of_lt (lt_trans hj (by decide)))).trans (h5_low j hj))
  have h5b_r15 : st5b.regs 15 = s3Addr := (h5b_reg 15 (by decide)).trans ((h5a_reg 15 (by decide)).trans h5_r15)
  have h5b_r16 : st5b.regs 16 = sec3.length := (h5b_reg 16 (by decide)).trans ((h5a_reg 16 (by decide)).trans h5_r16)
  have h5b_r17 : st5b.regs 17 = dir5 := (h5b_reg 17 (by decide)).trans ((h5a_reg 17 (by decide)).trans h5_r17)
  have h5b_r18 : st5b.regs 18 = s4Addr := (h5b_reg 18 (by decide)).trans h5a_r18
  have hRep₅ : BuildTopRepliesInMem table D x b reply replyAddr dir5 st5b.mem := by
    rw [h5b_mem]; exact hRep₄.mono h_dir4_dir5 (fun y hy => hFr₅ y hy)
  have hEmpC₅ : ListAt st5b.mem (tail0 + 2) [0] := fun i hi => by
    rw [h5b_mem]; have hi1 : i < 1 := by simpa using hi
    exact (hFr₅ (tail0 + 2 + i) (lt_of_lt_of_le (by omega) h_dir3_dir4)).trans (hEmpC₄ i hi)
  -- sec5
  refine runs_seq_call_clean
    (buildTopSec5_meetsContract (w := w) (table := table) (D := D) (x := x) (b := b)
      (emptyCSR := tail0 + 2) (dir := dir5) (root := root) (reply := reply) (replyAddr := replyAddr)
      hs5 hd5 hgat hrow hcopy hspan hread hseek)
    (vs := [table, D, P, twoPowB, tail0 + 2, dir5])
    (by
      have hr0 : st5b.regs 0 = table := (h5b_low 0 (by decide)).trans r0
      have hr1 : st5b.regs 1 = D := (h5b_low 1 (by decide)).trans r1
      have hr2 : st5b.regs 2 = P := (h5b_low 2 (by decide)).trans r2
      have hr3 : st5b.regs 3 = twoPowB := (h5b_low 3 (by decide)).trans r3
      have hr9 : st5b.regs 9 = tail0 := (h5b_low 9 (by decide)).trans r9
      simp [evalArgs, Expr.eval, BinOp.eval, hr0, hr1, hr2, hr3, hr9, h5b_r17, h2, h_tail2_w])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · exact htable_w
      · exact h_D_w
      · exact hPw
      · exact h2Bw
      · exact h_tail2_w
      · exact h_dir5_w)
    ⟨rfl, hD1, hbx, hRep₅, hEmpC₅, le_trans (by omega) (htail_le.trans (h_dir3_dir4.trans h_dir4_dir5)),
      h5b_mem ▸ hZero₅, hCtxW, h13, h2Pw⟩ ?_
  intro v6 st6 ⟨_, hv6, hSec5At₆, hZero₆, hFr₆⟩ h6_r20 h6_reg
  have hv6_eq : v6 = ctx := hv6
  subst hv6_eq
  have hFr₆' : ∀ y < dir5, st6.mem y = st5.mem y := fun y hy => (hFr₆ y hy).trans (by rw [h5b_mem])
  have h6_low : ∀ j < 14, st6.regs j = st.regs j := fun j hj =>
    (h6_reg j (Nat.ne_of_lt (lt_trans hj (by decide)))).trans (h5b_low j hj)
  have h6_r15 : st6.regs 15 = s3Addr := (h6_reg 15 (by decide)).trans h5b_r15
  have h6_r16 : st6.regs 16 = sec3.length := (h6_reg 16 (by decide)).trans h5b_r16
  have h6_r17 : st6.regs 17 = dir5 := (h6_reg 17 (by decide)).trans h5b_r17
  have h6_r18 : st6.regs 18 = s4Addr := (h6_reg 18 (by decide)).trans h5b_r18
  have h6_r19 : st6.regs 19 = sec4.length := (h6_reg 19 (by decide)).trans h5b_r19
  refine runs_seq_assign_clean (v := s5Addr)
    (Expr.eval_add (Expr.eval_reg_of_eq h6_r17)
      (Expr.eval_mul (Expr.eval_const h2)
        (Expr.eval_mul
          (Expr.eval_mul (Expr.eval_reg_of_eq ((h6_low 1 (by decide)).trans r1))
            (Expr.eval_reg_of_eq ((h6_low 2 (by decide)).trans r2)) h_DP_w)
          (Expr.eval_reg_of_eq ((h6_low 3 (by decide)).trans r3)) h_DPB_w) h_2DPB_w) h_s5_w) ?_
  intro st6a hmem6a h6a_r21 h6a_reg
  refine runs_assign_le (v := sec5.length)
    (Expr.eval_eq_of_eq
      (Expr.eval_sub (Expr.eval_reg_of_eq ((h6a_reg 20 (by decide)).trans h6_r20))
        (Expr.eval_reg_of_eq h6a_r21) hCtxW)
      (Nat.add_sub_cancel_left s5Addr sec5.length)) ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      dsimp only
      rw [Function.update_of_ne (Nat.ne_of_lt (lt_trans hj (by decide)))]
      exact (h6a_reg j (Nat.ne_of_lt (lt_trans hj (by decide)))).trans (h6_low j (lt_trans hj (by decide)))
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact (h6a_reg 15 (by decide)).trans h6_r15
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact (h6a_reg 16 (by decide)).trans h6_r16
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact (h6a_reg 18 (by decide)).trans h6_r18
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact (h6a_reg 19 (by decide)).trans h6_r19
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact (h6a_reg 20 (by decide)).trans h6_r20
    · dsimp only; rw [Function.update_of_ne (by decide)]; exact h6a_r21
    · dsimp only; rw [Function.update_self]
    · intro u hu; dsimp only; rw [hmem6a]
      have hlt4 : s3Addr + u < dir4 := Nat.add_lt_add_left hu s3Addr
      exact (hFr₆' _ (lt_of_lt_of_le hlt4 h_dir4_dir5)).trans ((hFr₅' _ hlt4).trans (hSec3At₄ u hu))
    · intro u hu; dsimp only; rw [hmem6a]
      exact (hFr₆' _ (Nat.add_lt_add_left hu s4Addr)).trans (hSec4At₅ u hu)
    · intro u hu; dsimp only; rw [hmem6a]; exact hSec5At₆ u hu
    · intro y hy; dsimp only; rw [hmem6a]; exact hZero₆ y hy
    · intro y hy; dsimp only; rw [hmem6a]
      exact (hFr₆' y (lt_of_lt_of_le hy (h_dir3_dir4.trans h_dir4_dir5))).trans
        ((hFr₅' y (lt_of_lt_of_le hy h_dir3_dir4)).trans (hFr₄ y hy))
  · simp only [buildTopSec3Contract, buildTopSec4Contract, buildTopSec5Contract,
      Expr.size, argsSize]
    change 0 + _ + (17 * sec3.length + 320 * ((D + 1) * P) + 120) + _ + _ + _ + _ + _ + _ +
        (17 * sec4.length + 320 * (D * P) + 120) + _ + _ + _ + _ + _ + _ +
        (17 * sec5.length + 360 * (D * P * twoPowB) + 120) + _ + _ + _ + _ ≤
      17 * (sec3.length + sec4.length + sec5.length) +
        640 * ((D + 1) * P) + 360 * (D * P * twoPowB) + 520
    clear * - hDP_le
    omega

/-- Total space above `tail0` needed by `buildTopPackAll`. -/
def buildTopPackAllSpace (S : StaticData) (D P twoPowB : ℕ) : ℕ :=
  2 * S.encode.length + 4 * ((D + 1) * P) + 2 * (D * P * twoPowB) + 18

/-- Contract for `buildTopPackAll`. -/
def buildTopPackAllContract (w table D x b rootGraph ownersAddr tail0 h : ℕ) (G : Graph)
    (reply : ℕ → ℕ → BuildLevelData) (replyAddr : ℕ → ℕ → ℕ) : Contract where
  pre args mem :=
    let root := hostGraph cloud G
    let H := buildTopHierarchy x b root reply
    let S : StaticData := ⟨x, b, hostOwner G, hostLabel G, H⟩
    let P := 2 ^ x
    let twoPowB := 2 ^ b
    args = [table, D, P, twoPowB, x, b, rootGraph, ownersAddr, G.m, tail0, h] ∧
    G.IsValid ∧ 1 ≤ G.m ∧ 0 < x ∧ 0 < b ∧ b ≤ x ∧ D = leafDepth x b ∧ 1 ≤ D ∧
    P = hostSize G ∧ H.IsValid x b ∧ h ≤ tail0 ∧
    BuildTopRepliesInMem table D x b reply replyAddr tail0 mem ∧
    GraphAt mem rootGraph root ∧ rootGraph + root.encode.length ≤ tail0 ∧
    ListAt mem ownersAddr (tabList P (hostOwner G)) ∧ ownersAddr + P ≤ tail0 ∧
    ZeroFrom mem tail0 ∧
    tail0 + buildTopPackAllSpace S D P twoPowB < 2 ^ w ∧
    13 < 2 ^ w ∧ 2 * P < 2 ^ w
  post _ mem v mem' :=
    let root := hostGraph cloud G
    let H := buildTopHierarchy x b root reply
    let S : StaticData := ⟨x, b, hostOwner G, hostLabel G, H⟩
    let P := 2 ^ x
    let twoPowB := 2 ^ b
    h + S.encode.length ≤ v ∧
    v ≤ tail0 + buildTopPackAllSpace S D P twoPowB ∧
    StaticOut mem' h S ∧
    ZeroFrom mem' v ∧
    ∀ y < h, mem' y = mem y
  cost _ _ :=
    let root := hostGraph cloud G
    let H := buildTopHierarchy x b root reply
    let S : StaticData := ⟨x, b, hostOwner G, hostLabel G, H⟩
    let P := 2 ^ x
    let twoPowB := 2 ^ b
    120 * S.encode.length + 1000 * ((D + 1) * P + D * P * twoPowB) + 2000

theorem buildTopPackAll_meetsContract
    {w f numConn labels iota fill sec3 dir3 sec4 dir4 sec5 dir5 finish gather row copy span read
      seek move table D x b rootGraph ownersAddr tail0 h : ℕ}
    {G : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {p : Program}
    (hp : p.procs[f]? = some (buildTopPackAll numConn labels sec3 sec4 sec5 finish))
    (hnc : p.procs[numConn]? = some buildTopNumConn)
    (hlab : p.procs[labels]? = some (buildTopLabels iota fill))
    (hiota : p.HasAt iota [LowStretch.iotaP])
    (hfill : p.procs[fill]? = some initFillWord)
    (hs3 : p.procs[sec3]? = some (buildTopSec3 dir3 gather))
    (hd3 : p.procs[dir3]? = some (buildTopSec3Dir span))
    (hs4 : p.procs[sec4]? = some (buildTopSec4 dir4 gather))
    (hd4 : p.procs[dir4]? = some (buildTopSec4Dir span))
    (hs5 : p.procs[sec5]? = some (buildTopSec5 dir5 gather))
    (hd5 : p.procs[dir5]? = some (buildTopSec5Dir span))
    (hfin : p.procs[finish]? = some (buildTopFinish gather move))
    (hgat : p.procs[gather]? = some (initCSRWrite row))
    (hrow : p.procs[row]? = some (buildTopRow copy))
    (hcopy : p.procs[copy]? = some buildCopyProc)
    (hspan : p.procs[span]? = some (buildTopReplySpan read))
    (hread : p.procs[read]? = some (buildTopReplyRead seek))
    (hseek : p.procs[seek]? = some initCSRSeek)
    (hmove : p.procs[move]? = some copyDown) :
    MeetsContract w p f
      (buildTopPackAllContract w table D x b rootGraph ownersAddr tail0 h G reply replyAddr) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨rfl, hG, hm, hxpos, hbpos, hbx, hDeq, hD1, hPhs, hValidH, hht, hRep, hRootAt, hRootEnd,
    hOwnAt, hOwnEnd, hZero, hRoom, h13, h2Pw⟩ := hpre
  set root := hostGraph cloud G
  set H := buildTopHierarchy x b root reply
  set S : StaticData := ⟨x, b, hostOwner G, hostLabel G, H⟩
  set P := 2 ^ x
  set twoPowB := 2 ^ b
  set sec3 := csrList ((D + 1) * P) (buildTopSec3Rows x b root reply)
  set sec4 := csrList (D * P) (buildTopSec4Rows x b root reply)
  set sec5 := csrList (D * P * twoPowB) (buildTopSec5Rows x b root reply)
  have hSec0_eq : buildTopSections S 0 = [x, b, buildTopNumConnVal x b] := by
    simp only [buildTopSections, StaticData.sections, List.getD_cons_zero, StaticData.numConn, S]
    rw [length_connRecs_eq hxpos hbpos hValidH]
  have hSec1_eq : buildTopSections S 1 = tabList P (hostOwner G) := rfl
  have hSec2_eq : buildTopSections S 2 = buildTopLabelWords G.m root.m := by
    have hH0 : H.host 0 0 = root := rfl
    simp only [buildTopSections, StaticData.sections, List.getD_cons_succ, List.getD_cons_zero, S,
      hH0]
    exact (buildTopLabelWords_eq hG hm).symm
  have hSec3_eq : buildTopSections S 3 = sec3 := by
    change csrList ((leafDepth x b + 1) * 2 ^ x) (buildTopSec3Rows x b root reply) =
      csrList ((D + 1) * P) (buildTopSec3Rows x b root reply)
    rw [← hDeq]
  have hSec4_eq : buildTopSections S 4 = sec4 := by
    change csrList (leafDepth x b * 2 ^ x) (buildTopSec4Rows x b root reply) =
      csrList (D * P) (buildTopSec4Rows x b root reply)
    rw [← hDeq]
  have hSec5_eq : buildTopSections S 5 = sec5 := by
    change csrList (leafDepth x b * 2 ^ x * 2 ^ b) (buildTopSec5Rows x b root reply) =
      csrList (D * P * twoPowB) (buildTopSec5Rows x b root reply)
    rw [← hDeq]
  have hRootM_ge : G.m ≤ root.m := by
    unfold root hostGraph Graph.m portGraph
    simp [origPortEdges, inside_verts_length hG, Graph.m]
  have hSumLen : 3 + P + root.m + sec3.length + sec4.length + sec5.length ≤ S.encode.length := by
    have h := packAll_sections_sum_le S
    have h0 : (S.sections.getD 0 []).length = 3 := by
      change (buildTopSections S 0).length = 3; rw [hSec0_eq]; rfl
    have h1 : (S.sections.getD 1 []).length = P := by
      change (buildTopSections S 1).length = P; rw [hSec1_eq]; simp [tabList]
    have h2 : (S.sections.getD 2 []).length = root.m := by
      change (buildTopSections S 2).length = root.m
      rw [hSec2_eq]; simp [buildTopLabelWords, Nat.add_sub_of_le hRootM_ge]
    have h3 : (S.sections.getD 3 []).length = sec3.length := by
      change (buildTopSections S 3).length = _; rw [hSec3_eq]
    have h4 : (S.sections.getD 4 []).length = sec4.length := by
      change (buildTopSections S 4).length = _; rw [hSec4_eq]
    have h5 : (S.sections.getD 5 []).length = sec5.length := by
      change (buildTopSections S 5).length = _; rw [hSec5_eq]
    omega
  have hRoom' : tail0 + 2 * S.encode.length + 4 * ((D + 1) * P) + 2 * (D * P * twoPowB) + 18 <
      2 ^ w := by
    simpa [buildTopPackAllSpace, Nat.add_assoc] using hRoom
  have hDP_le : D * P ≤ (D + 1) * P := Nat.mul_le_mul_right P (Nat.le_succ D)
  have hPpos : 0 < P := Nat.two_pow_pos x
  have hD_le_DP : D ≤ D * P := Nat.le_mul_of_pos_right D hPpos
  have hD1_le : D + 1 ≤ (D + 1) * P := Nat.le_mul_of_pos_right (D + 1) hPpos
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have h3 : 3 < 2 ^ w := by omega
  have h4 : 4 < 2 ^ w := by omega
  have h5 : 5 < 2 ^ w := by omega
  have h6 : 6 < 2 ^ w := by omega
  have h12 : 12 < 2 ^ w := by omega
  set dir3 := tail0 + 6 + root.m
  set s3Addr := dir3 + 2 * ((D + 1) * P)
  set dir4 := s3Addr + sec3.length
  set s4Addr := dir4 + 2 * (D * P)
  set dir5 := s4Addr + sec4.length
  set s5Addr := dir5 + 2 * (D * P * twoPowB)
  set ctx := s5Addr + sec5.length
  have hCtxLe : ctx + 12 + S.encode.length ≤
      tail0 + 2 * S.encode.length + 4 * ((D + 1) * P) + 2 * (D * P * twoPowB) + 18 := by
    dsimp only [ctx, s5Addr, dir5, s4Addr, dir4, s3Addr, dir3]
    omega
  have hCtxRoom : ctx + 12 + S.encode.length < 2 ^ w := lt_of_le_of_lt hCtxLe hRoom'
  have hDPB_w : D * 2 ^ x * 2 ^ b < 2 ^ w := by
    have : D * P * twoPowB < 2 ^ w := by omega
    exact this
  have hNC_w : buildTopNumConnVal x b < 2 ^ w := by
    have h := buildTopNumConnVal_le x b
    rw [← hDeq] at h
    exact lt_of_le_of_lt h hDPB_w
  let initRegs : ℕ → ℕ :=
    (startState [table, D, P, twoPowB, x, b, rootGraph, ownersAddr, G.m, tail0, h] mem pos).regs
  -- Run the procedure step by step with clean state binders
  refine runs_start_le ?_
  unfold buildTopPackAll
  -- Steps 1..6: buildTopPackSec02 (numConn + sec0 + labels)
  refine runs_seq_triple_le
    (packSec02_triple (w := w) (p := p) (root := root) hnc hlab hiota hfill
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      hxpos hbpos hbx hDeq hRootM_ge hRootAt hRootEnd hZero
      (by omega) hDPB_w (by omega) h13) rfl ?_
  intro st3 ⟨h3_below, h3_r12, h3_r13, hSec0_at₃, hLabAt₃, hEmpG_at₃, hEmpC_at₃, hZero₃, hFr₃_orig⟩
  have hRep₃ : BuildTopRepliesInMem table D x b reply replyAddr dir3 st3.mem :=
    hRep.mono (by omega) (fun y hy => hFr₃_orig y (by omega))
  have hRootAt₃ : GraphAt st3.mem rootGraph root := fun i hi =>
    (hFr₃_orig (rootGraph + i) (by omega)).trans (hRootAt i hi)
  have h_t0_dir3 : tail0 ≤ dir3 := Nat.le_trans (Nat.le_add_right _ 6) (Nat.le_add_right _ _)
  have h_t6_dir3 : tail0 + 6 ≤ dir3 := Nat.le_add_right _ _
  have h_dir3_s3 : dir3 ≤ s3Addr := Nat.le_add_right _ _
  have h_s3_dir4 : s3Addr ≤ dir4 := Nat.le_add_right _ _
  have h_dir3_dir4 : dir3 ≤ dir4 := h_dir3_s3.trans h_s3_dir4
  have h_dir4_s4 : dir4 ≤ s4Addr := Nat.le_add_right _ _
  have h_s4_dir5 : s4Addr ≤ dir5 := Nat.le_add_right _ _
  have h_dir4_dir5 : dir4 ≤ dir5 := h_dir4_s4.trans h_s4_dir5
  have h_dir5_s5 : dir5 ≤ s5Addr := Nat.le_add_right _ _
  have h_s5_ctx : s5Addr ≤ ctx := Nat.le_add_right _ _
  have h_dir5_ctx : dir5 ≤ ctx := h_dir5_s5.trans h_s5_ctx
  have h_dir4_ctx : dir4 ≤ ctx := h_dir4_dir5.trans h_dir5_ctx
  have h_dir3_ctx : dir3 ≤ ctx := h_dir3_dir4.trans h_dir4_ctx
  have h_ctx_12_w : ctx + 12 < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hCtxRoom
  have h_ctx_w : ctx < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ 12) h_ctx_12_w
  have h_t6_w : tail0 + 6 < 2 ^ w := lt_of_le_of_lt (h_t6_dir3.trans h_dir3_ctx) h_ctx_w
  have h_h_w : h < 2 ^ w := lt_of_le_of_lt (hht.trans (h_t0_dir3.trans h_dir3_ctx)) h_ctx_w
  -- Steps 7..15: buildTopPackSec345 (sec3, sec4, sec5)
  refine runs_seq_triple_le
    (packSec345_triple (w := w) (p := p) (table := table) (D := D) (x := x) (b := b)
      (rootGraph := rootGraph) (tail0 := tail0) (dir3 := dir3)
      (root := root) (reply := reply) (replyAddr := replyAddr)
      hs3 hd3 hs4 hd4 hs5 hd5 hgat hrow hcopy hspan hread hseek
      (h3_below 0 (by decide)) (h3_below 1 (by decide)) (h3_below 2 (by decide))
      (h3_below 3 (by decide)) (h3_below 6 (by decide)) (h3_below 9 (by decide))
      h3_r13 hD1 hbx h_t6_dir3 hRep₃ hRootAt₃ (hRootEnd.trans h_t0_dir3) hEmpG_at₃ hEmpC_at₃ hZero₃
      (hw _ (by simp)) h13 h2Pw h_ctx_w) rfl ?_
  intro st6b ⟨h6b_low, h6b_r15, h6b_r16, h6b_r18, h6b_r19, h6b_r20, h6b_r21, h6b_r22,
    hSec3At₆, hSec4At₆, hSec5At₆, hZero₆, hFr₆_dir3⟩
  have h6b_below : ∀ j < 11, st6b.regs j = initRegs j := fun j hj =>
    (h6b_low j (lt_trans hj (by decide))).trans (h3_below j hj)
  -- Step 16: store the 6 (addr, len) pairs at ctx .. ctx + 11
  refine runs_seq_triple_le (storeDir6_triple (w := w) (p := p) (st := st6b)
    (ctx := ctx) (tail0 := tail0) (ownersAddr := ownersAddr) (P := P) (rootM := root.m)
    (s3 := s3Addr) (l3 := sec3.length) (s4 := s4Addr) (l4 := sec4.length)
    (s5 := s5Addr) (l5 := sec5.length) (h := h)
    (h6b_below 2 (by decide)) (h6b_below 7 (by decide)) (h6b_below 9 (by decide)) (h6b_below 10 (by decide))
    ((h6b_low 12 (by decide)).trans h3_r12)
    h6b_r15 h6b_r16 h6b_r18 h6b_r19 h6b_r20 h6b_r21 h6b_r22
    h_ctx_12_w h_t6_w h13) rfl ?_
  intro st₇ hSt₇
  obtain ⟨hr10_7, hr20_7, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hFr₇⟩ := hSt₇
  have hFr₇_below : ∀ y < ctx, st₇.mem y = st6b.mem y := fun y hy => hFr₇ y (.inl hy)
  have hFr₇_dir3 : ∀ y < dir3, st₇.mem y = st3.mem y := fun y hy =>
    (hFr₇_below y (lt_of_lt_of_le hy h_dir3_ctx)).trans (hFr₆_dir3 y hy)
  have hFr₆_to_orig : ∀ y < tail0, st₇.mem y = mem y := fun y hy =>
    (hFr₇_dir3 y (lt_of_lt_of_le hy h_t0_dir3)).trans (hFr₃_orig y (lt_of_lt_of_le hy (Nat.le_add_right _ 3)))
  let src6 : ℕ → ℕ := fun i =>
    match i with
    | 0 => tail0 + 3
    | 1 => ownersAddr
    | 2 => tail0 + 6
    | 3 => s3Addr
    | 4 => s4Addr
    | _ => s5Addr
  have hRowDir : buildTopRowDir ctx 6 (buildTopSections S) src6 (ctx + 12) st₇.mem := by
    refine ⟨le_rfl, ?_⟩
    intro i hi
    match i with
    | 0 =>
      have hlen : (buildTopSections S 0).length = 3 := by rw [hSec0_eq]; rfl
      refine ⟨by simpa [src6] using hc0, by simpa [hlen] using hc1, ?_,
        by change tail0 + 3 + (buildTopSections S 0).length ≤ ctx + 12; rw [hlen]; exact h_t6_dir3.trans (h_dir3_ctx.trans (Nat.le_add_right _ _))⟩
      change ListAt st₇.mem (tail0 + 3) (buildTopSections S 0)
      rw [hSec0_eq]
      intro u hu
      have hu3 : u < 3 := by simpa using hu
      exact (hFr₇_dir3 _ (lt_of_lt_of_le (Nat.add_lt_add_left hu3 (tail0 + 3)) h_t6_dir3)).trans
        (hSec0_at₃ u hu)
    | 1 =>
      have hlen : (buildTopSections S 1).length = P := by rw [hSec1_eq]; simp [tabList]
      refine ⟨by simpa [src6] using hc2, by simpa [hlen] using hc3, ?_,
        by change ownersAddr + (buildTopSections S 1).length ≤ ctx + 12; rw [hlen]; exact hOwnEnd.trans (h_t0_dir3.trans (h_dir3_ctx.trans (Nat.le_add_right _ _)))⟩
      change ListAt st₇.mem ownersAddr (buildTopSections S 1)
      rw [hSec1_eq]
      intro u hu
      have huP : u < P := by simpa [tabList] using hu
      exact (hFr₆_to_orig (ownersAddr + u) (lt_of_lt_of_le (Nat.add_lt_add_left huP ownersAddr) hOwnEnd)).trans
        (hOwnAt u hu)
    | 2 =>
      have hlen : (buildTopSections S 2).length = root.m := by
        rw [hSec2_eq]; simp [buildTopLabelWords, Nat.add_sub_of_le hRootM_ge]
      refine ⟨by simpa [src6] using hc4, by simpa [hlen] using hc5, ?_,
        by change tail0 + 6 + (buildTopSections S 2).length ≤ ctx + 12; rw [hlen]; exact h_dir3_ctx.trans (Nat.le_add_right _ _)⟩
      change ListAt st₇.mem (tail0 + 6) (buildTopSections S 2)
      rw [hSec2_eq]
      intro u hu
      have huM : u < root.m := by simpa [buildTopLabelWords, Nat.add_sub_of_le hRootM_ge] using hu
      exact (hFr₇_dir3 _ (Nat.add_lt_add_left huM (tail0 + 6))).trans (hLabAt₃ u hu)
    | 3 =>
      have hlen : (buildTopSections S 3).length = sec3.length := by rw [hSec3_eq]
      refine ⟨by simpa [src6] using hc6, by simpa [hlen] using hc7, ?_,
        by change s3Addr + (buildTopSections S 3).length ≤ ctx + 12; rw [hlen]; exact h_dir4_ctx.trans (Nat.le_add_right _ _)⟩
      change ListAt st₇.mem s3Addr (buildTopSections S 3)
      rw [hSec3_eq]
      intro u hu
      exact (hFr₇_below _ (lt_of_lt_of_le (Nat.add_lt_add_left hu s3Addr) h_dir4_ctx)).trans (hSec3At₆ u hu)
    | 4 =>
      have hlen : (buildTopSections S 4).length = sec4.length := by rw [hSec4_eq]
      refine ⟨by simpa [src6] using hc8, by simpa [hlen] using hc9, ?_,
        by change s4Addr + (buildTopSections S 4).length ≤ ctx + 12; rw [hlen]; exact h_dir5_ctx.trans (Nat.le_add_right _ _)⟩
      change ListAt st₇.mem s4Addr (buildTopSections S 4)
      rw [hSec4_eq]
      intro u hu
      exact (hFr₇_below _ (lt_of_lt_of_le (Nat.add_lt_add_left hu s4Addr) h_dir5_ctx)).trans (hSec4At₆ u hu)
    | 5 =>
      have hlen : (buildTopSections S 5).length = sec5.length := by rw [hSec5_eq]
      refine ⟨by simpa [src6] using hc10, by simpa [hlen] using hc11, ?_,
        by change s5Addr + (buildTopSections S 5).length ≤ ctx + 12; rw [hlen]; exact Nat.le_add_right _ _⟩
      change ListAt st₇.mem s5Addr (buildTopSections S 5)
      rw [hSec5_eq]
      intro u hu
      exact (hFr₇_below _ (Nat.add_lt_add_left hu s5Addr)).trans (hSec5At₆ u hu)
    | i + 6 => omega
  have hZero₇ : ZeroFrom st₇.mem (ctx + 12) := fun y hy =>
    (hFr₇ y (.inr hy)).trans (hZero₆ y (le_trans (Nat.le_add_right _ 12) hy))
  have h_h_le_ctx12 : h ≤ ctx + 12 := hht.trans (h_t0_dir3.trans (h_dir3_ctx.trans (Nat.le_add_right _ _)))
  -- Step 17: call finish [ctx, ctx + 12, h] -> reg 23
  refine runs_seq_call_clean
    (buildTopFinish_meetsContract (w := w) (S := S) (src := src6) hfin hgat hrow hcopy hmove)
    (vs := [ctx, ctx + 12, h])
    (by simp [evalArgs, Expr.eval, BinOp.eval, hr10_7, hr20_7, h12, h_ctx_12_w])
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact h_ctx_w
      · exact h_ctx_12_w
      · exact h_h_w)
    ⟨ctx, ctx + 12, h, rfl, h_h_le_ctx12, hRowDir, hZero₇, hCtxRoom, h6⟩ ?_
  intro vFin stFin hPostFin hFin_r23 _
  obtain ⟨ctx', tail', h', haF, hvFinLo, hvFinHi, hSO, hZeroFin, hFrFin⟩ := hPostFin
  simp only [List.cons.injEq, and_true] at haF
  obtain ⟨rfl, rfl, rfl⟩ := haF
  -- Step 18: ret reg 23
  refine runs_ret_le (v := vFin) (Expr.eval_reg_of_eq hFin_r23)
    ⟨hvFinLo, by change vFin ≤ tail0 + buildTopPackAllSpace S D P twoPowB
                 unfold buildTopPackAllSpace; clear * - hvFinHi hCtxLe; omega,
      hSO, hZeroFin, fun y hy => (hFrFin y hy).trans (hFr₆_to_orig y (lt_of_lt_of_le hy hht))⟩ ?_
  have hFinCost := buildTopFinish_cost_le w ctx (ctx + 12) h S src6 st₇.mem
  simp only [buildTopPackAllContract, Expr.size, argsSize]
  change 0 + (70 * D + 40 * root.m + 180) + _ +
      (17 * (sec3.length + sec4.length + sec5.length) +
        640 * ((D + 1) * P) + 360 * (D * P * twoPowB) + 520) + _ + 120 + _ + _ +
      (buildTopFinishContract w S src6).cost [ctx, ctx + 12, h] st₇.mem + _ + _ ≤
    120 * S.encode.length + 1000 * ((D + 1) * P + D * P * twoPowB) + 2000
  have h1' : 40 * root.m + 17 * (sec3.length + sec4.length + sec5.length) ≤
      40 * S.encode.length := by
    have h2x : 0 ≤ 2 ^ x := Nat.zero_le _
    clear * - hSumLen h2x; omega
  have h2' : 70 * D + 640 * ((D + 1) * P) ≤ 1000 * ((D + 1) * P) := by
    clear * - hD_le_DP hD1_le; omega
  clear * - hFinCost h1' h2'
  omega

end MinCostFlow.HierPaths

end
