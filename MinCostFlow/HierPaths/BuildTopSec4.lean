module

public import MinCostFlow.HierPaths.BuildTopSec3

/-!
# Assembling section 4 of `StaticData` (child edge embeddings)

Reads all child edge embeddings from section 1 of the completed level replies,
populates a `D * 2^x`-entry `(src, len)` directory, and invokes `buildTopGather`
(`initCSRWrite (buildTopRow buildCopyProc)`) to materialize section 4 of `StaticData`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Section 4 rows of `StaticData`. -/
def buildTopSec4Rows (x b : ℕ) (root : Graph) (reply : ℕ → ℕ → BuildLevelData) (k : ℕ) : List ℕ :=
  let P := 2 ^ x
  let H := buildTopHierarchy x b root reply
  csrList (H.host (k / P + 1) (k % P)).m (H.emb (k / P) (k % P))

/-- Source address for row `k` of section 4. -/
def buildTopSec4Src (x b emptyCSR : ℕ) (reply : ℕ → ℕ → BuildLevelData)
    (replyAddr : ℕ → ℕ → ℕ) (k : ℕ) : ℕ :=
  let P := 2 ^ x
  let j := k / P
  let c := k % P
  if c < numGroups x b (j + 1) then
    let B := branching x b j
    let p := parentGroup x b j c
    let D := reply j p
    buildTopReplyRowAddr (replyAddr j p) 1 B (c % B)
      (fun u => csrList (D.host u).m (D.emb u)) (buildTopReplySections D B)
  else emptyCSR

/-- Directory loop body for section 4.
Regs: `0=table, 1=D, 2=P, 3=emptyCSR, 4=dir, 5=total, 6=k`. -/
def buildTopSec4DirBody (span : ℕ) : Stmt :=
  .assign 7 (.bin .div (.reg 6) (.reg 2)) ;;
  .assign 8 (.bin .mod (.reg 6) (.reg 2)) ;;
  .assign 9 (.bin .add (.reg 4) (.bin .add (.reg 6) (.reg 6))) ;;
  .assign 10 (.bin .add (.reg 0) (.bin .mul (.const 13) (.reg 7))) ;;
  .assign 11 (.load (.bin .add (.reg 10) (.const 4))) ;;
  .assign 12 (.bin .mul (.load (.bin .add (.reg 10) (.const 5))) (.reg 11)) ;;
  .cond (.bin .lt (.reg 8) (.reg 12))
    (.assign 13 (.load (.bin .add (.load (.bin .add (.reg 10) (.const 1)))
        (.bin .div (.reg 8) (.reg 11)))) ;;
      .call 14 span [.reg 13, .const 1, .reg 11, .bin .mod (.reg 8) (.reg 11), .reg 9])
    (.store (.reg 9) (.reg 3) ;;
      .store (.bin .add (.reg 9) (.const 1)) (.const 1))

/-- Populate the `D * P` `(src, len)` directory for section 4.
Args: `[table, D, P, emptyCSR, dir]`. -/
def buildTopSec4Dir (span : ℕ) : Stmt :=
  .assign 5 (.bin .mul (.reg 1) (.reg 2)) ;;
  forRange 6 (.const 0) (.reg 5) (buildTopSec4DirBody span) ;;
  .ret (.const 0)

/-- Build section 4 at `dir + 2 * (D * P)` and return its end address.
Args: `[table, D, P, emptyCSR, dir]`. -/
def buildTopSec4 (dir4 gather : ℕ) : Stmt :=
  .assign 5 (.bin .mul (.reg 1) (.reg 2)) ;;
  .assign 6 (.bin .add (.reg 4) (.bin .add (.reg 5) (.reg 5))) ;;
  .call 7 dir4 [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4] ;;
  .call 7 gather [.reg 4, .reg 5, .reg 6] ;;
  .ret (.reg 7)

theorem buildTopSec4Dir_noRand (span : ℕ) : (buildTopSec4Dir span).NoRand := by
  simp [buildTopSec4Dir, buildTopSec4DirBody, forRange, forUp, Stmt.NoRand]

theorem buildTopSec4_noRand (dir4 gather : ℕ) : (buildTopSec4 dir4 gather).NoRand := by
  simp [buildTopSec4, Stmt.NoRand]

/-- Contract for `buildTopSec4Dir`. -/
def buildTopSec4DirContract (w table D x b emptyCSR dir : ℕ) (root : Graph)
    (reply : ℕ → ℕ → BuildLevelData) (replyAddr : ℕ → ℕ → ℕ) : Contract where
  pre args mem :=
    let P := 2 ^ x
    let total := D * P
    args = [table, D, P, emptyCSR, dir] ∧
    BuildTopRepliesInMem table D x b reply replyAddr dir mem ∧
    ListAt mem emptyCSR [0] ∧ emptyCSR + 1 ≤ dir ∧
    ZeroFrom mem dir ∧ dir + 2 * total < 2 ^ w ∧ 13 < 2 ^ w ∧ P < 2 ^ w
  post args mem _ mem' :=
    let P := 2 ^ x
    let total := D * P
    args = [table, D, P, emptyCSR, dir] ∧
    buildTopRowDir dir total (buildTopSec4Rows x b root reply)
      (buildTopSec4Src x b emptyCSR reply replyAddr) (dir + 2 * total) mem' ∧
    ZeroFrom mem' (dir + 2 * total) ∧
    ∀ y < dir, mem' y = mem y
  cost _ _ := 220 * (D * 2 ^ x) + 40

private lemma emptyCSR_eq (f : ℕ → List ℕ) : csrList 0 f = [0] := by
  simp [csrList, csrOffsets, csrData]

private lemma sec4Src_end_le_dir {table D x b emptyCSR dir i : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {mem0 : ℕ → ℕ}
    (hRep : BuildTopRepliesInMem table D x b reply replyAddr dir mem0)
    (hEmpEnd : emptyCSR + 1 ≤ dir)
    (hi : i < D * 2 ^ x) :
    buildTopSec4Src x b emptyCSR reply replyAddr i +
      (buildTopSec4Rows x b root reply i).length ≤ dir := by
  dsimp only [buildTopSec4Src, buildTopSec4Rows]
  have hjlt : i / 2 ^ x < D := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos x)).mpr hi
  by_cases hc : i % 2 ^ x < numGroups x b (i / 2 ^ x + 1)
  · simp only [hc, ↓reduceIte, buildTopHierarchy]
    have hp : parentGroup x b (i / 2 ^ x) (i % 2 ^ x) < numGroups x b (i / 2 ^ x) := by
      unfold parentGroup
      rw [Nat.div_lt_iff_lt_mul branching_pos, ← numGroups_succ]; exact hc
    have hlc : (i % 2 ^ x) % branching x b (i / 2 ^ x) < branching x b (i / 2 ^ x) :=
      Nat.mod_lt _ branching_pos
    obtain ⟨_, hAtP, hEndP⟩ := hRep.reply_entry (i / 2 ^ x) hjlt _ hp
    have hF := (buildTopReplyRowAddr_facts (sec := 1) (k := branching x b (i / 2 ^ x))
      (i := (i % 2 ^ x) % branching x b (i / 2 ^ x))
      (rows := fun u =>
        csrList ((reply (i / 2 ^ x) (parentGroup x b (i / 2 ^ x) (i % 2 ^ x))).host u).m
          ((reply (i / 2 ^ x) (parentGroup x b (i / 2 ^ x) (i % 2 ^ x))).emb u))
      (sections := buildTopReplySections
        (reply (i / 2 ^ x) (parentGroup x b (i / 2 ^ x) (i % 2 ^ x))) (branching x b (i / 2 ^ x)))
      rfl (by decide) hlc rfl hAtP).2
    exact hF.trans hEndP
  · simp only [hc, ↓reduceIte, buildTopHierarchy, Graph.m, List.length_nil, emptyCSR_eq,
      List.length_singleton]
    exact hEmpEnd

private theorem buildTopSec4DirBody_triple
    {w span read seek table D x b emptyCSR dir k : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ}
    {mem0 : ℕ → ℕ} {p : Program}
    (hspan : p.procs[span]? = some (buildTopReplySpan read))
    (hread : p.procs[read]? = some (buildTopReplyRead seek))
    (hseek : p.procs[seek]? = some initCSRSeek)
    (hRep : BuildTopRepliesInMem table D x b reply replyAddr dir mem0)
    (hEmpAt : ListAt mem0 emptyCSR [0]) (hEmpEnd : emptyCSR + 1 ≤ dir)
    (hRoom : dir + 2 * (D * 2 ^ x) < 2 ^ w) (h13 : 13 < 2 ^ w) (hPw : 2 ^ x < 2 ^ w)
    (hk : k < D * 2 ^ x) :
    let P := 2 ^ x
    let total := D * P
    let rows := buildTopSec4Rows x b root reply
    let src := buildTopSec4Src x b emptyCSR reply replyAddr
    Triple w p
      (fun st =>
        st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = P ∧
        st.regs 3 = emptyCSR ∧ st.regs 4 = dir ∧ st.regs 5 = total ∧ st.regs 6 = k ∧
        (∀ y < dir, st.mem y = mem0 y) ∧ ZeroFrom st.mem (dir + 2 * k) ∧
        ∀ i < k, st.mem (dir + 2 * i) = src i ∧ st.mem (dir + 2 * i + 1) = (rows i).length ∧
          ListAt st.mem (src i) (rows i) ∧ src i + (rows i).length ≤ dir + 2 * total)
      (buildTopSec4DirBody span)
      (normalPost fun st =>
        st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = P ∧
        st.regs 3 = emptyCSR ∧ st.regs 4 = dir ∧ st.regs 5 = total ∧ st.regs 6 = k ∧
        (∀ y < dir, st.mem y = mem0 y) ∧ ZeroFrom st.mem (dir + 2 * (k + 1)) ∧
        ∀ i < k + 1, st.mem (dir + 2 * i) = src i ∧ st.mem (dir + 2 * i + 1) = (rows i).length ∧
          ListAt st.mem (src i) (rows i) ∧ src i + (rows i).length ≤ dir + 2 * total)
      (fun _ => 200) := by
  dsimp only
  set P := 2 ^ x
  set total := D * P
  set rows := buildTopSec4Rows x b root reply
  set src := buildTopSec4Src x b emptyCSR reply replyAddr
  intro st ω hPre
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, hFr, hZ, hPrev⟩ := hPre
  have hPpos : 0 < P := Nat.two_pow_pos x
  have h1 : 1 < 2 ^ w := by omega
  have h4 : 4 < 2 ^ w := by omega
  have h5 : 5 < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  have hg_w : k % P < 2 ^ w := (Nat.mod_lt k hPpos).trans hPw
  have h2k_w : k + k < 2 ^ w := by omega
  have hdst_w : dir + (k + k) < 2 ^ w := by omega
  have hdst1_w : dir + 2 * k + 1 < 2 ^ w := by omega
  have hdst_eq : dir + (k + k) = dir + 2 * k := by omega
  have hRepSt := hRep.mono le_rfl hFr
  have hEmpAtSt : ListAt st.mem emptyCSR [0] := fun u hu => by
    have hu1 : u < 1 := by simpa using hu
    exact (hFr _ (by omega)).trans (hEmpAt u hu)
  have hjlt : k / P < D := (Nat.div_lt_iff_lt_mul hPpos).mpr hk
  set j := k / P
  have hTbl := hRepSt.table_end
  have hrow_w : table + 13 * j < 2 ^ w := by omega
  have h13j_w : 13 * j < 2 ^ w := by omega
  have hrow4_w : table + 13 * j + 4 < 2 ^ w := by omega
  have hrow5_w : table + 13 * j + 5 < 2 ^ w := by omega
  have hrow1_w : table + 13 * j + 1 < 2 ^ w := by omega
  have hB_eq := hRepSt.row_branch j hjlt
  have hCnt_eq := hRepSt.row_count j hjlt
  have hRD_eq := hRepSt.row_replyDir j hjlt
  have hng_succ : numGroups x b j * branching x b j = numGroups x b (j + 1) :=
    (numGroups_succ x b j).symm
  have hng_le_P : numGroups x b (j + 1) ≤ P :=
    (Nat.le_mul_of_pos_right _ groupSize_pos).trans (le_of_eq numGroups_mul_groupSize)
  have hng_w : numGroups x b (j + 1) < 2 ^ w := hng_le_P.trans_lt hPw
  have hB_pos : 0 < branching x b j := branching_pos
  have hB_w : branching x b j < 2 ^ w := by
    have h1' : branching x b j ≤ groupSize x b j :=
      (Nat.le_mul_of_pos_right _ groupSize_pos).trans (le_of_eq (groupSize_eq_mul_branching.symm))
    have h2' : groupSize x b j ≤ P := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    exact (h1'.trans h2').trans_lt hPw
  have hFinish : ∀ (mem' : ℕ → ℕ) (regs' : ℕ → ℕ) (pos' : ℕ),
      (∀ r ≤ 6, regs' r = st.regs r) →
      (∀ y, y ≠ dir + 2 * k → y ≠ dir + 2 * k + 1 → mem' y = st.mem y) →
      mem' (dir + 2 * k) = src k →
      mem' (dir + 2 * k + 1) = (rows k).length →
      ListAt st.mem (src k) (rows k) →
      src k + (rows k).length ≤ dir →
      let st' : State := ⟨mem', regs', pos'⟩
      st'.regs 0 = table ∧ st'.regs 1 = D ∧ st'.regs 2 = P ∧
      st'.regs 3 = emptyCSR ∧ st'.regs 4 = dir ∧ st'.regs 5 = total ∧ st'.regs 6 = k ∧
      (∀ y < dir, st'.mem y = mem0 y) ∧ ZeroFrom st'.mem (dir + 2 * (k + 1)) ∧
      ∀ i < k + 1, st'.mem (dir + 2 * i) = src i ∧ st'.mem (dir + 2 * i + 1) = (rows i).length ∧
        ListAt st'.mem (src i) (rows i) ∧ src i + (rows i).length ≤ dir + 2 * total := by
    intro mem' regs' pos' hRegs hMemFr hS0 hS1 hListK hEndK
    have hFr' : ∀ y < dir, mem' y = mem0 y := fun y hy =>
      (hMemFr y (by omega) (by omega)).trans (hFr y hy)
    have hZ' : ZeroFrom mem' (dir + 2 * (k + 1)) := fun y hy =>
      (hMemFr y (by omega) (by omega)).trans (hZ y (by omega))
    refine ⟨(hRegs 0 (by decide)).trans r0, (hRegs 1 (by decide)).trans r1,
      (hRegs 2 (by decide)).trans r2, (hRegs 3 (by decide)).trans r3,
      (hRegs 4 (by decide)).trans r4, (hRegs 5 (by decide)).trans r5,
      (hRegs 6 (by decide)).trans r6, hFr', hZ', ?_⟩
    intro i hi
    by_cases hik : i = k
    · subst i
      refine ⟨hS0, hS1, fun u hu => (hMemFr _ (by omega) (by omega)).trans (hListK u hu), by omega⟩
    · have hilt : i < k := by omega
      obtain ⟨ha, hb, hc, hd⟩ := hPrev i hilt
      have hlt_dir : src i + (rows i).length ≤ dir :=
        sec4Src_end_le_dir hRep hEmpEnd (hilt.trans hk)
      refine ⟨(hMemFr _ (by omega) (by omega)).trans ha,
        (hMemFr _ (by omega) (by omega)).trans hb,
        fun u hu => (hMemFr _ (by omega) (by omega)).trans (hc u hu), hd⟩
  refine runs_start_le ?_
  unfold buildTopSec4DirBody
  refine runs_seq_assign_le (v := j)
    (Expr.eval_div (Expr.eval_reg_of_eq r6) (Expr.eval_reg_of_eq r2) hk_w) ?_
  refine runs_seq_assign_le (v := k % P)
    (Expr.eval_mod
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact r6))
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact r2)) hk_w) ?_
  refine runs_seq_assign_le (v := dir + 2 * k)
    (Expr.eval_eq_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r4]))
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r6]))
        (Expr.eval_reg_of_eq (by simp [r6])) h2k_w) hdst_w) hdst_eq) ?_
  refine runs_seq_assign_le (v := table + 13 * j)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0]))
      (Expr.eval_mul (Expr.eval_const h13) (Expr.eval_reg_of_eq (by simp)) h13j_w) hrow_w) ?_
  refine runs_seq_assign_le (v := branching x b j)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const h4) hrow4_w) hB_eq) ?_
  refine runs_seq_assign_le (v := numGroups x b (j + 1))
    (Expr.eval_eq_of_eq (Expr.eval_mul
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_const h5) hrow5_w) hCnt_eq)
      (Expr.eval_reg_of_eq (by simp)) (hng_succ.symm ▸ hng_w)) hng_succ) ?_
  by_cases hlt : k % P < numGroups x b (j + 1)
  · have hp : parentGroup x b j (k % P) < numGroups x b j := by
      unfold parentGroup
      rw [Nat.div_lt_iff_lt_mul hB_pos, ← numGroups_succ]; exact hlt
    have hlc : (k % P) % branching x b j < branching x b j := Nat.mod_lt _ hB_pos
    obtain ⟨hrAddr_eq, hAtP, hEndP⟩ := hRepSt.reply_entry j hjlt _ hp
    have hrd_end := hRepSt.replyDir_end j hjlt
    have hrd_p_w : buildTopScheduleReplies table D x j + parentGroup x b j (k % P) < 2 ^ w := by
      omega
    refine runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hlt, h1]) (fun _ => ?_)
      (fun h => absurd h one_ne_zero)
    refine runs_seq_assign_le (v := replyAddr j (parentGroup x b j (k % P)))
      (Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := table + 13 * j) (by simp))
          (Expr.eval_const h1) hrow1_w) hRD_eq)
        (Expr.eval_div (Expr.eval_reg_of_eq (v := k % P) (by simp))
          (Expr.eval_reg_of_eq (v := branching x b j) (by simp)) hg_w)
        hrd_p_w) hrAddr_eq) ?_
    let Dp := reply j (parentGroup x b j (k % P))
    let B := branching x b j
    let secs := buildTopReplySections Dp B
    let rws := fun u => csrList (Dp.host u).m (Dp.emb u)
    have hSpanC := buildTopReplySpan_meetsContract (w := w) (sec := 1) (k := B)
      (i := (k % P) % B) (rows := rws) (sections := secs) hspan hread hseek
    have hlc_w : (k % P) % B < 2 ^ w := hlc.trans hB_w
    refine runs_call_le hSpanC
      (vs := [replyAddr j (parentGroup x b j (k % P)), 1, B, (k % P) % B, dir + 2 * k])
      ?_ ?_ ⟨replyAddr j (parentGroup x b j (k % P)), dir + 2 * k, rfl, rfl, by decide, hlc, rfl,
        hAtP, lt_of_le_of_lt hEndP (by omega), hdst1_w, h1⟩ ?_
    · simp [evalArgs, Expr.eval, BinOp.eval, h1, hlc_w, B]
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · omega
      · exact h1
      · exact hB_w
      · exact hlc_w
      · omega
    · intro v mem' pos' hPost
      obtain ⟨rA', d', heq, hS0, hS1, hFrSpan⟩ := hPost
      simp only [List.cons.injEq, and_true, true_and] at heq
      obtain ⟨hE1, hE2⟩ := heq
      subst rA' d'
      have hFacts := buildTopReplyRowAddr_facts (sec := 1) (k := B) (i := (k % P) % B)
        (rows := rws) (sections := secs) rfl (by decide) hlc rfl hAtP
      refine ⟨hFinish mem' _ pos'
        (fun r hr => by dsimp only; simp [show r ≠ 14 by omega, show r ≠ 13 by omega,
          show r ≠ 12 by omega, show r ≠ 11 by omega, show r ≠ 10 by omega,
          show r ≠ 9 by omega, show r ≠ 8 by omega, show r ≠ 7 by omega])
        hFrSpan ?_ ?_ ?_ ?_, ?_⟩
      · simpa [src, buildTopSec4Src, P, j, hlt, B, Dp, secs, rws] using hS0
      · simpa [rows, buildTopSec4Rows, P, j, hlt, buildTopHierarchy, B, Dp, rws] using hS1
      · simpa [src, rows, buildTopSec4Src, buildTopSec4Rows, P, j, hlt, buildTopHierarchy,
          B, Dp, secs, rws] using hFacts.1
      · have hEnd := hFacts.2.trans hEndP
        simpa [src, rows, buildTopSec4Src, buildTopSec4Rows, P, j, hlt, buildTopHierarchy,
          B, Dp, secs, rws] using hEnd
      · simp [buildTopReplySpanContract, Expr.size, argsSize]
  · refine runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hlt])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine runs_seq_store_le
      (Expr.eval_reg_of_eq (v := dir + 2 * k) (by simp))
      (Expr.eval_reg_of_eq (v := emptyCSR) (by simp [r3])) ?_
    refine runs_store_le
      (Expr.eval_add (Expr.eval_reg_of_eq (v := dir + 2 * k) (by simp)) (Expr.eval_const h1) hdst1_w)
      (Expr.eval_const h1) ?_ ?_
    · refine hFinish _ _ _
        (fun r hr => by dsimp only; simp [show r ≠ 12 by omega, show r ≠ 11 by omega,
          show r ≠ 10 by omega, show r ≠ 9 by omega, show r ≠ 8 by omega, show r ≠ 7 by omega])
        (fun y hy0 hy1 => by dsimp only; rw [Function.update_of_ne hy1, Function.update_of_ne hy0])
        ?_ ?_ ?_ ?_
      · dsimp only
        rw [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self _)), Function.update_self]
        simp [src, buildTopSec4Src, P, j, hlt]
      · dsimp only
        rw [Function.update_self]
        simp [rows, buildTopSec4Rows, P, j, hlt, buildTopHierarchy, Graph.m, emptyCSR_eq]
      · simp only [src, rows, buildTopSec4Src, buildTopSec4Rows, P, j, hlt, ↓reduceIte,
          buildTopHierarchy, Graph.m, List.length_nil, emptyCSR_eq]
        exact hEmpAtSt
      · simp only [src, rows, buildTopSec4Src, buildTopSec4Rows, P, j, hlt, ↓reduceIte,
          buildTopHierarchy, Graph.m, List.length_nil, emptyCSR_eq, List.length_singleton]
        exact hEmpEnd
    · simp [Expr.size]

theorem buildTopSec4Dir_meetsContract
    {w f span read seek table D x b emptyCSR dir : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {p : Program}
    (hp : p.procs[f]? = some (buildTopSec4Dir span))
    (hspan : p.procs[span]? = some (buildTopReplySpan read))
    (hread : p.procs[read]? = some (buildTopReplyRead seek))
    (hseek : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p f
      (buildTopSec4DirContract w table D x b emptyCSR dir root reply replyAddr) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨rfl, hRep, hEmpAt, hEmpEnd, hZero, hRoom, h13, hPw⟩ := hpre
  have h1 : 1 < 2 ^ w := by omega
  have htot_w : D * 2 ^ x < 2 ^ w := by omega
  let rows := buildTopSec4Rows x b root reply
  let src := buildTopSec4Src x b emptyCSR reply replyAddr
  let Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = 2 ^ x ∧
    st.regs 3 = emptyCSR ∧ st.regs 4 = dir ∧ st.regs 5 = D * 2 ^ x ∧ st.regs 6 = k ∧
    (∀ y < dir, st.mem y = mem y) ∧ ZeroFrom st.mem (dir + 2 * k) ∧
    ∀ i < k, st.mem (dir + 2 * i) = src i ∧ st.mem (dir + 2 * i + 1) = (rows i).length ∧
      ListAt st.mem (src i) (rows i) ∧ src i + (rows i).length ≤ dir + 2 * (D * 2 ^ x)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 6) (lo := .const 0) (hi := .reg 5)
    (body := buildTopSec4DirBody span)
    (P := fun st =>
      st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = 2 ^ x ∧
      st.regs 3 = emptyCSR ∧ st.regs 4 = dir ∧ st.regs 5 = D * 2 ^ x ∧ st.mem = mem)
    (Inv := Inv) 200 0 (D * 2 ^ x) (Nat.zero_le _) h1 (fun _ => htot_w)
    (fun st ⟨r0, r1, r2, r3, r4, r5, hm⟩ => ⟨Expr.eval_const (Nat.two_pow_pos _), by
      refine ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp [r5],
        by simp, fun _ _ => by simp [hm], by simpa [hm] using hZero,
        fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.2.1)
    (fun k _ hk => by
      have hb := buildTopSec4DirBody_triple (root := root) hspan hread hseek hRep hEmpAt hEmpEnd
        hRoom h13 hPw hk
      exact Triple.conseq hb (fun _ hI => hI) (fun o st h => by
        cases o with
        | returned _ => exact h.elim
        | normal =>
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
          exact ⟨⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5],
            by simp [h6], by simp, h8, h9, h10⟩, h7⟩) (fun _ _ => le_rfl))
  refine runs_start_le ?_
  unfold buildTopSec4Dir
  refine runs_seq_assign_le (v := D * 2 ^ x)
    (Expr.eval_mul (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) htot_w) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro st' hEnd
    obtain ⟨_, _, _, _, _, _, _, hFr', hZ', hRows'⟩ := hEnd
    refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _))
      ⟨rfl, ⟨le_rfl, hRows'⟩, hZ', hFr'⟩ ?_
    simp [buildTopSec4DirContract, Expr.size]; omega

/-- Contract for `buildTopSec4`: materializes section 4 at `dir + 2 * (D * P)`
and returns its end address. -/
def buildTopSec4Contract (w table D x b emptyCSR dir : ℕ) (root : Graph)
    (reply : ℕ → ℕ → BuildLevelData) (replyAddr : ℕ → ℕ → ℕ) : Contract where
  pre args mem :=
    let P := 2 ^ x
    let total := D * P
    let sec4 := csrList total (buildTopSec4Rows x b root reply)
    args = [table, D, P, emptyCSR, dir] ∧
    BuildTopRepliesInMem table D x b reply replyAddr dir mem ∧
    ListAt mem emptyCSR [0] ∧ emptyCSR + 1 ≤ dir ∧
    ZeroFrom mem dir ∧ dir + 2 * total + sec4.length < 2 ^ w ∧ 13 < 2 ^ w ∧ P < 2 ^ w
  post args mem v mem' :=
    let P := 2 ^ x
    let total := D * P
    let sec4 := csrList total (buildTopSec4Rows x b root reply)
    args = [table, D, P, emptyCSR, dir] ∧
    v = dir + 2 * total + sec4.length ∧
    ListAt mem' (dir + 2 * total) sec4 ∧
    ZeroFrom mem' v ∧
    ∀ y < dir, mem' y = mem y
  cost _ _ :=
    let total := D * 2 ^ x
    let sec4 := csrList total (buildTopSec4Rows x b root reply)
    17 * sec4.length + 320 * total + 120

theorem buildTopSec4_meetsContract
    {w f dir4 gather row copy span read seek table D x b emptyCSR dir : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {p : Program}
    (hp : p.procs[f]? = some (buildTopSec4 dir4 gather))
    (hd : p.procs[dir4]? = some (buildTopSec4Dir span))
    (hg : p.procs[gather]? = some (initCSRWrite row))
    (hrow : p.procs[row]? = some (buildTopRow copy))
    (hcopy : p.procs[copy]? = some buildCopyProc)
    (hspan : p.procs[span]? = some (buildTopReplySpan read))
    (hread : p.procs[read]? = some (buildTopReplyRead seek))
    (hseek : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p f
      (buildTopSec4Contract w table D x b emptyCSR dir root reply replyAddr) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨rfl, hRep, hEmpAt, hEmpEnd, hZero, hRoom, h13, hPw⟩ := hpre
  have h1 : 1 < 2 ^ w := by omega
  have htot_w : D * 2 ^ x < 2 ^ w := by omega
  have h2tot_w : D * 2 ^ x + D * 2 ^ x < 2 ^ w := by omega
  have hdst_w : dir + (D * 2 ^ x + D * 2 ^ x) < 2 ^ w := by omega
  have hdst_eq : dir + (D * 2 ^ x + D * 2 ^ x) = dir + 2 * (D * 2 ^ x) := by omega
  refine runs_start_le ?_
  unfold buildTopSec4
  refine runs_seq_assign_le (v := D * 2 ^ x)
    (Expr.eval_mul (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) htot_w) ?_
  refine runs_seq_assign_le (v := dir + 2 * (D * 2 ^ x))
    (Expr.eval_eq_of_eq (Expr.eval_add (Expr.eval_reg_of_eq rfl)
      (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) h2tot_w) hdst_w) hdst_eq) ?_
  refine runs_seq_call_le
    (buildTopSec4Dir_meetsContract (w := w) (table := table) (D := D) (x := x) (b := b)
      (emptyCSR := emptyCSR) (dir := dir)
      (root := root) (reply := reply) (replyAddr := replyAddr) hd hspan hread hseek)
    (vs := [table, D, 2 ^ x, emptyCSR, dir]) rfl hw
    ⟨rfl, hRep, hEmpAt, hEmpEnd, hZero, by omega, h13, hPw⟩ ?_
  intro _ mem1 pos1 hPost1
  obtain ⟨_, hDir1, hZ1, hFr1⟩ := hPost1
  refine runs_seq_call_le
    (buildTopGather_meetsContract (w := w) (ctx := dir) (k := D * 2 ^ x)
      (rows := buildTopSec4Rows x b root reply)
      (src := buildTopSec4Src x b emptyCSR reply replyAddr) hg hrow hcopy)
    (vs := [dir, D * 2 ^ x, dir + 2 * (D * 2 ^ x)]) rfl
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨dir + 2 * (D * 2 ^ x), rfl, hDir1, hZ1, by simpa only [Nat.add_zero] using hRoom, h1⟩ ?_
  intro v2 mem2 pos2 hPost2
  obtain ⟨dst', ha, hv2, hAt2, hZ2, hFr2⟩ := hPost2
  simp only [List.cons.injEq, and_true, true_and] at ha
  subst dst'
  refine runs_ret_le (v := v2) (Expr.eval_reg_of_eq rfl)
    ⟨rfl, hv2, hAt2, hZ2, fun y hy => (hFr2 y (by omega)).trans (hFr1 y hy)⟩ ?_
  have hGC := buildTopGather_cost_le (D * 2 ^ x) (buildTopSec4Rows x b root reply)
  simp only [buildTopSec4Contract, buildTopSec4DirContract, initCSRWriteContract,
    Expr.size, argsSize]
  omega

end MinCostFlow.HierPaths

end
