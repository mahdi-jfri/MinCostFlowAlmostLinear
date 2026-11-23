module

public import MinCostFlow.HierPaths.BuildTopSecHelper
public import MinCostFlow.HierPaths.BuildTopScheduleLayout
public import MinCostFlow.HierPaths.BuildTopScheduleGeometry

/-!
# Assembling section 3 of `StaticData` (all host graphs)

Reads the root host graph and all child host graphs from the completed level replies,
populates a `(D + 1) * 2^x`-entry `(src, len)` directory, and invokes `buildTopGather`
(`initCSRWrite (buildTopRow buildCopyProc)`) to materialize section 3 of `StaticData`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Shared read-only memory invariant for sections 3, 4, and 5: the schedule table rows
and all completed parent replies sit below `bound`. -/
structure BuildTopRepliesInMem (table D x b : ℕ) (reply : ℕ → ℕ → BuildLevelData)
    (replyAddr : ℕ → ℕ → ℕ) (bound : ℕ) (mem : ℕ → ℕ) : Prop where
  table_end : table + 13 * D ≤ bound
  row_replyDir : ∀ j < D, mem (table + 13 * j + 1) = buildTopScheduleReplies table D x j
  row_branch : ∀ j < D, mem (table + 13 * j + 4) = branching x b j
  row_count : ∀ j < D, mem (table + 13 * j + 5) = numGroups x b j
  replyDir_end : ∀ j < D, buildTopScheduleReplies table D x j + numGroups x b j ≤ bound
  reply_entry : ∀ j < D, ∀ p < numGroups x b j,
    mem (buildTopScheduleReplies table D x j + p) = replyAddr j p ∧
    ListAt mem (replyAddr j p) ((reply j p).encode (branching x b j)) ∧
    replyAddr j p + ((reply j p).encode (branching x b j)).length ≤ bound

theorem BuildTopRepliesInMem.mono {table D x b bound bound' : ℕ}
    {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {mem mem' : ℕ → ℕ}
    (h : BuildTopRepliesInMem table D x b reply replyAddr bound mem)
    (hle : bound ≤ bound') (hf : ∀ y < bound, mem' y = mem y) :
    BuildTopRepliesInMem table D x b reply replyAddr bound' mem' where
  table_end := h.table_end.trans hle
  row_replyDir j hj := (hf _ (by have := h.table_end; omega)).trans (h.row_replyDir j hj)
  row_branch j hj := (hf _ (by have := h.table_end; omega)).trans (h.row_branch j hj)
  row_count j hj := (hf _ (by have := h.table_end; omega)).trans (h.row_count j hj)
  replyDir_end j hj := (h.replyDir_end j hj).trans hle
  reply_entry j hj p hp := by
    obtain ⟨he, hAt, hEnd⟩ := h.reply_entry j hj p hp
    have hrd := h.replyDir_end j hj
    refine ⟨(hf _ (by omega)).trans he, fun u hu => (hf _ (by omega)).trans (hAt u hu),
      hEnd.trans hle⟩

/-- Section 3 rows of `StaticData`: `(H.host (k / P) (k % P)).encode`. -/
def buildTopSec3Rows (x b : ℕ) (root : Graph) (reply : ℕ → ℕ → BuildLevelData) (k : ℕ) : List ℕ :=
  let P := 2 ^ x
  ((buildTopHierarchy x b root reply).host (k / P) (k % P)).encode

/-- Source address for row `k` of section 3. -/
def buildTopSec3Src (x b rootGraph emptyGraph : ℕ) (reply : ℕ → ℕ → BuildLevelData)
    (replyAddr : ℕ → ℕ → ℕ) (k : ℕ) : ℕ :=
  let P := 2 ^ x
  match k / P with
  | 0 => if k % P = 0 then rootGraph else emptyGraph
  | j + 1 =>
    if k % P < numGroups x b (j + 1) then
      let B := branching x b j
      let p := parentGroup x b j (k % P)
      let D := reply j p
      buildTopReplyRowAddr (replyAddr j p) 0 B ((k % P) % B)
        (fun c => (D.host c).encode) (buildTopReplySections D B)
    else emptyGraph

/-- Directory loop body for section 3.
Regs: `0=table, 1=D, 2=P, 3=rootGraph, 4=emptyGraph, 5=dir, 6=total, 7=k`. -/
def buildTopSec3DirBody (span : ℕ) : Stmt :=
  .assign 8 (.bin .div (.reg 7) (.reg 2)) ;;
  .assign 9 (.bin .mod (.reg 7) (.reg 2)) ;;
  .assign 10 (.bin .add (.reg 5) (.bin .add (.reg 7) (.reg 7))) ;;
  .cond (.bin .eq (.reg 8) (.const 0))
    (.cond (.bin .eq (.reg 9) (.const 0))
      (.store (.reg 10) (.reg 3) ;;
        .store (.bin .add (.reg 10) (.const 1))
          (.bin .add (.const 2) (.bin .mul (.const 2) (.load (.bin .add (.reg 3) (.const 1))))))
      (.store (.reg 10) (.reg 4) ;;
        .store (.bin .add (.reg 10) (.const 1)) (.const 2)))
    (.assign 11 (.bin .add (.reg 0) (.bin .mul (.const 13) (.bin .sub (.reg 8) (.const 1)))) ;;
      .assign 12 (.load (.bin .add (.reg 11) (.const 4))) ;;
      .assign 13 (.bin .mul (.load (.bin .add (.reg 11) (.const 5))) (.reg 12)) ;;
      .cond (.bin .lt (.reg 9) (.reg 13))
        (.assign 14 (.load (.bin .add (.load (.bin .add (.reg 11) (.const 1)))
            (.bin .div (.reg 9) (.reg 12)))) ;;
          .call 15 span [.reg 14, .const 0, .reg 12, .bin .mod (.reg 9) (.reg 12), .reg 10])
        (.store (.reg 10) (.reg 4) ;;
          .store (.bin .add (.reg 10) (.const 1)) (.const 2)))

/-- Populate the `(D + 1) * P` `(src, len)` directory for section 3.
Args: `[table, D, P, rootGraph, emptyGraph, dir]`. -/
def buildTopSec3Dir (span : ℕ) : Stmt :=
  .assign 6 (.bin .mul (.bin .add (.reg 1) (.const 1)) (.reg 2)) ;;
  forRange 7 (.const 0) (.reg 6) (buildTopSec3DirBody span) ;;
  .ret (.const 0)

/-- Build section 3 at `dir + 2 * (D + 1) * P` and return its end address.
Args: `[table, D, P, rootGraph, emptyGraph, dir]`. -/
def buildTopSec3 (dir3 gather : ℕ) : Stmt :=
  .assign 6 (.bin .mul (.bin .add (.reg 1) (.const 1)) (.reg 2)) ;;
  .assign 7 (.bin .add (.reg 5) (.bin .add (.reg 6) (.reg 6))) ;;
  .call 8 dir3 [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5] ;;
  .call 8 gather [.reg 5, .reg 6, .reg 7] ;;
  .ret (.reg 8)

theorem buildTopSec3Dir_noRand (span : ℕ) : (buildTopSec3Dir span).NoRand := by
  simp [buildTopSec3Dir, buildTopSec3DirBody, forRange, forUp, Stmt.NoRand]

theorem buildTopSec3_noRand (dir3 gather : ℕ) : (buildTopSec3 dir3 gather).NoRand := by
  simp [buildTopSec3, Stmt.NoRand]

/-- Contract for `buildTopSec3Dir`. -/
def buildTopSec3DirContract (w table D x b rootGraph emptyGraph dir : ℕ) (root : Graph)
    (reply : ℕ → ℕ → BuildLevelData) (replyAddr : ℕ → ℕ → ℕ) : Contract where
  pre args mem :=
    let P := 2 ^ x
    let total := (D + 1) * P
    args = [table, D, P, rootGraph, emptyGraph, dir] ∧
    BuildTopRepliesInMem table D x b reply replyAddr dir mem ∧
    GraphAt mem rootGraph root ∧ rootGraph + root.encode.length ≤ dir ∧
    ListAt mem emptyGraph [0, 0] ∧ emptyGraph + 2 ≤ dir ∧
    ZeroFrom mem dir ∧ dir + 2 * total < 2 ^ w ∧ 13 < 2 ^ w
  post args mem _ mem' :=
    let P := 2 ^ x
    let total := (D + 1) * P
    args = [table, D, P, rootGraph, emptyGraph, dir] ∧
    buildTopRowDir dir total (buildTopSec3Rows x b root reply)
      (buildTopSec3Src x b rootGraph emptyGraph reply replyAddr) (dir + 2 * total) mem' ∧
    ZeroFrom mem' (dir + 2 * total) ∧
    ∀ y < dir, mem' y = mem y
  cost _ _ := 220 * ((D + 1) * 2 ^ x) + 40

private lemma emptyGraph_encode : (⟨0, []⟩ : Graph).encode = [0, 0] := by
  simp [Graph.encode, Graph.m]

private lemma sec3Src_end_le_dir {table D x b rootGraph emptyGraph dir i : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {mem0 : ℕ → ℕ}
    (hRep : BuildTopRepliesInMem table D x b reply replyAddr dir mem0)
    (hRootEnd : rootGraph + root.encode.length ≤ dir)
    (hEmpEnd : emptyGraph + 2 ≤ dir)
    (hi : i < (D + 1) * 2 ^ x) :
    buildTopSec3Src x b rootGraph emptyGraph reply replyAddr i +
      (buildTopSec3Rows x b root reply i).length ≤ dir := by
  dsimp only [buildTopSec3Src, buildTopSec3Rows]
  cases ht : i / 2 ^ x with
  | zero =>
    by_cases hm : i % 2 ^ x = 0
    · simp only [hm, ↓reduceIte, buildTopHierarchy]; exact hRootEnd
    · simp only [hm, ↓reduceIte, buildTopHierarchy, emptyGraph_encode]; exact hEmpEnd
  | succ j =>
    have hjlt : j < D := by
      have h1 : (j + 1) * 2 ^ x ≤ i := by rw [← ht, Nat.mul_comm]; exact Nat.mul_div_le i (2 ^ x)
      exact Nat.lt_of_succ_lt_succ (Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h1 hi))
    by_cases hc' : i % 2 ^ x < numGroups x b (j + 1)
    · simp only [hc', ↓reduceIte, buildTopHierarchy]
      have hp : parentGroup x b j (i % 2 ^ x) < numGroups x b j := by
        unfold parentGroup
        rw [Nat.div_lt_iff_lt_mul branching_pos, ← numGroups_succ]; exact hc'
      have hlc : (i % 2 ^ x) % branching x b j < branching x b j := Nat.mod_lt _ branching_pos
      obtain ⟨_, hAtP, hEndP⟩ := hRep.reply_entry j hjlt _ hp
      have hF := (buildTopReplyRowAddr_facts (sec := 0) (k := branching x b j)
        (i := (i % 2 ^ x) % branching x b j)
        (rows := fun c => ((reply j (parentGroup x b j (i % 2 ^ x))).host c).encode)
        (sections := buildTopReplySections (reply j (parentGroup x b j (i % 2 ^ x))) (branching x b j))
        rfl (by decide) hlc rfl hAtP).2
      exact hF.trans hEndP
    · simp only [hc', ↓reduceIte, buildTopHierarchy, emptyGraph_encode]; exact hEmpEnd

private theorem buildTopSec3DirBody_triple
    {w span read seek table D x b rootGraph emptyGraph dir k : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ}
    {mem0 : ℕ → ℕ} {p : Program}
    (hspan : p.procs[span]? = some (buildTopReplySpan read))
    (hread : p.procs[read]? = some (buildTopReplyRead seek))
    (hseek : p.procs[seek]? = some initCSRSeek)
    (hRep : BuildTopRepliesInMem table D x b reply replyAddr dir mem0)
    (hRootAt : GraphAt mem0 rootGraph root) (hRootEnd : rootGraph + root.encode.length ≤ dir)
    (hEmpAt : ListAt mem0 emptyGraph [0, 0]) (hEmpEnd : emptyGraph + 2 ≤ dir)
    (hRoom : dir + 2 * ((D + 1) * 2 ^ x) < 2 ^ w) (h13 : 13 < 2 ^ w)
    (hk : k < (D + 1) * 2 ^ x) :
    let P := 2 ^ x
    let total := (D + 1) * P
    let rows := buildTopSec3Rows x b root reply
    let src := buildTopSec3Src x b rootGraph emptyGraph reply replyAddr
    Triple w p
      (fun st =>
        st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = P ∧
        st.regs 3 = rootGraph ∧ st.regs 4 = emptyGraph ∧ st.regs 5 = dir ∧
        st.regs 6 = total ∧ st.regs 7 = k ∧
        (∀ y < dir, st.mem y = mem0 y) ∧ ZeroFrom st.mem (dir + 2 * k) ∧
        ∀ i < k, st.mem (dir + 2 * i) = src i ∧ st.mem (dir + 2 * i + 1) = (rows i).length ∧
          ListAt st.mem (src i) (rows i) ∧ src i + (rows i).length ≤ dir + 2 * total)
      (buildTopSec3DirBody span)
      (normalPost fun st =>
        st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = P ∧
        st.regs 3 = rootGraph ∧ st.regs 4 = emptyGraph ∧ st.regs 5 = dir ∧
        st.regs 6 = total ∧ st.regs 7 = k ∧
        (∀ y < dir, st.mem y = mem0 y) ∧ ZeroFrom st.mem (dir + 2 * (k + 1)) ∧
        ∀ i < k + 1, st.mem (dir + 2 * i) = src i ∧ st.mem (dir + 2 * i + 1) = (rows i).length ∧
          ListAt st.mem (src i) (rows i) ∧ src i + (rows i).length ≤ dir + 2 * total)
      (fun _ => 200) := by
  dsimp only
  set P := 2 ^ x
  set total := (D + 1) * P
  set rows := buildTopSec3Rows x b root reply
  set src := buildTopSec3Src x b rootGraph emptyGraph reply replyAddr
  intro st ω hPre
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, hFr, hZ, hPrev⟩ := hPre
  have hPpos : 0 < P := Nat.two_pow_pos x
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have h4 : 4 < 2 ^ w := by omega
  have h5 : 5 < 2 ^ w := by omega
  have hP_w : P < 2 ^ w := by
    have : P ≤ total := Nat.le_mul_of_pos_left _ (Nat.succ_pos D)
    omega
  have hk_w : k < 2 ^ w := by omega
  have ht_w : k / P < 2 ^ w := (Nat.div_le_self k P).trans_lt hk_w
  have hg_w : k % P < 2 ^ w := (Nat.mod_lt k hPpos).trans hP_w
  have h2k_w : k + k < 2 ^ w := by omega
  have hdst_w : dir + (k + k) < 2 ^ w := by omega
  have hdst1_w : dir + 2 * k + 1 < 2 ^ w := by omega
  have hdst_eq : dir + (k + k) = dir + 2 * k := by omega
  have hRepSt := hRep.mono le_rfl hFr
  have hRootAtSt : GraphAt st.mem rootGraph root := fun u hu => (hFr _ (by omega)).trans (hRootAt u hu)
  have hEmpAtSt : ListAt st.mem emptyGraph [0, 0] := fun u hu => by
    have hu2 : u < 2 := by simpa using hu
    exact (hFr _ (by omega)).trans (hEmpAt u hu)
  have hFinish : ∀ (mem' : ℕ → ℕ) (regs' : ℕ → ℕ) (pos' : ℕ),
      (∀ j ≤ 7, regs' j = st.regs j) →
      (∀ y, y ≠ dir + 2 * k → y ≠ dir + 2 * k + 1 → mem' y = st.mem y) →
      mem' (dir + 2 * k) = src k →
      mem' (dir + 2 * k + 1) = (rows k).length →
      ListAt st.mem (src k) (rows k) →
      src k + (rows k).length ≤ dir →
      let st' : State := ⟨mem', regs', pos'⟩
      st'.regs 0 = table ∧ st'.regs 1 = D ∧ st'.regs 2 = P ∧
      st'.regs 3 = rootGraph ∧ st'.regs 4 = emptyGraph ∧ st'.regs 5 = dir ∧
      st'.regs 6 = total ∧ st'.regs 7 = k ∧
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
      (hRegs 6 (by decide)).trans r6, (hRegs 7 (by decide)).trans r7,
      hFr', hZ', ?_⟩
    intro i hi
    by_cases hik : i = k
    · subst i
      refine ⟨hS0, hS1, fun u hu => (hMemFr _ (by omega) (by omega)).trans (hListK u hu), by omega⟩
    · have hilt : i < k := by omega
      obtain ⟨ha, hb, hc, hd⟩ := hPrev i hilt
      have hlt_dir : src i + (rows i).length ≤ dir :=
        sec3Src_end_le_dir hRep hRootEnd hEmpEnd (hilt.trans hk)
      refine ⟨(hMemFr _ (by omega) (by omega)).trans ha,
        (hMemFr _ (by omega) (by omega)).trans hb,
        fun u hu => (hMemFr _ (by omega) (by omega)).trans (hc u hu), hd⟩
  refine runs_start_le ?_
  unfold buildTopSec3DirBody
  refine runs_seq_assign_le (v := k / P)
    (Expr.eval_div (Expr.eval_reg_of_eq r7) (Expr.eval_reg_of_eq r2) hk_w) ?_
  refine runs_seq_assign_le (v := k % P)
    (Expr.eval_mod
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact r7))
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact r2)) hk_w) ?_
  refine runs_seq_assign_le (v := dir + 2 * k)
    (Expr.eval_eq_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r5]))
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r7]))
        (Expr.eval_reg_of_eq (by simp [r7])) h2k_w) hdst_w) hdst_eq) ?_
  cases ht : k / P with
  | zero =>
    refine runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, h1]) (fun _ => ?_)
      (fun h => absurd h one_ne_zero)
    by_cases hg0 : k % P = 0
    · refine runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hg0, h1]) (fun _ => ?_)
        (fun h => absurd h one_ne_zero)
      have hm_eq : st.mem (rootGraph + 1) = root.m := by
        have h := hRootAtSt 1 (by rw [graph_encode_length]; omega)
        simpa [Graph.encode] using h
      have hLen : root.encode.length = 2 + 2 * root.m := graph_encode_length root
      have hroot1_w : rootGraph + 1 < 2 ^ w := by omega
      have h2m_w : 2 * root.m < 2 ^ w := by omega
      have h2p2m_w : 2 + 2 * root.m < 2 ^ w := by omega
      refine runs_seq_store_le
        (Expr.eval_reg_of_eq (v := dir + 2 * k) (by simp))
        (Expr.eval_reg_of_eq (v := rootGraph) (by simp [r3])) ?_
      refine runs_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq (v := dir + 2 * k) (by simp)) (Expr.eval_const h1) hdst1_w)
        (Expr.eval_add (Expr.eval_const h2)
          (Expr.eval_mul (Expr.eval_const h2)
            (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := rootGraph) (by simp [r3]))
              (Expr.eval_const h1) hroot1_w) (by
                dsimp only; rw [Function.update_of_ne (by omega)]; exact hm_eq))
            h2m_w) h2p2m_w) ?_ ?_
      · refine hFinish _ _ _
          (fun j hj => by dsimp only; simp [show j ≠ 10 by omega, show j ≠ 9 by omega, show j ≠ 8 by omega])
          (fun y hy0 hy1 => by dsimp only; rw [Function.update_of_ne hy1, Function.update_of_ne hy0])
          ?_ ?_ ?_ ?_
        · dsimp only
          rw [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self _)), Function.update_self]
          simp [src, buildTopSec3Src, P, ht, hg0]
        · dsimp only
          rw [Function.update_self]
          simp [rows, buildTopSec3Rows, P, ht, hg0, buildTopHierarchy, hLen]
        · simp only [src, rows, buildTopSec3Src, buildTopSec3Rows, P, ht, hg0, ↓reduceIte,
            buildTopHierarchy]
          exact hRootAtSt
        · simp only [src, rows, buildTopSec3Src, buildTopSec3Rows, P, ht, hg0, ↓reduceIte,
            buildTopHierarchy]
          exact hRootEnd
      · simp [Expr.size]
    · refine runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hg0])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine runs_seq_store_le
        (Expr.eval_reg_of_eq (v := dir + 2 * k) (by simp))
        (Expr.eval_reg_of_eq (v := emptyGraph) (by simp [r4])) ?_
      refine runs_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq (v := dir + 2 * k) (by simp)) (Expr.eval_const h1) hdst1_w)
        (Expr.eval_const h2) ?_ ?_
      · refine hFinish _ _ _
          (fun j hj => by dsimp only; simp [show j ≠ 10 by omega, show j ≠ 9 by omega, show j ≠ 8 by omega])
          (fun y hy0 hy1 => by dsimp only; rw [Function.update_of_ne hy1, Function.update_of_ne hy0])
          ?_ ?_ ?_ ?_
        · dsimp only
          rw [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self _)), Function.update_self]
          simp [src, buildTopSec3Src, P, ht, hg0]
        · dsimp only
          rw [Function.update_self]
          simp [rows, buildTopSec3Rows, P, ht, hg0, buildTopHierarchy, emptyGraph_encode]
        · simp only [src, rows, buildTopSec3Src, buildTopSec3Rows, P, ht, hg0, ↓reduceIte,
            buildTopHierarchy, emptyGraph_encode]
          exact hEmpAtSt
        · simp only [src, rows, buildTopSec3Src, buildTopSec3Rows, P, ht, hg0, ↓reduceIte,
            buildTopHierarchy, emptyGraph_encode]
          exact hEmpEnd
      · simp [Expr.size]
  | succ j =>
    have hjlt : j < D := by
      have h1' : (j + 1) * P ≤ k := by rw [← ht, Nat.mul_comm]; exact Nat.mul_div_le k P
      exact Nat.lt_of_succ_lt_succ (Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h1' hk))
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
    have hng_w : numGroups x b (j + 1) < 2 ^ w := hng_le_P.trans_lt hP_w
    have hB_pos : 0 < branching x b j := branching_pos
    have hB_w : branching x b j < 2 ^ w := by
      have h1' : branching x b j ≤ groupSize x b j :=
        (Nat.le_mul_of_pos_right _ groupSize_pos).trans (le_of_eq (groupSize_eq_mul_branching.symm))
      have h2' : groupSize x b j ≤ P := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
      exact (h1'.trans h2').trans_lt hP_w
    refine runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine runs_seq_assign_le (v := table + 13 * j)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0]))
        (Expr.eval_mul (Expr.eval_const h13)
          (Expr.eval_eq_of_eq (Expr.eval_sub (Expr.eval_reg_of_eq (by simp))
            (Expr.eval_const h1) (ht ▸ ht_w)) (Nat.add_sub_cancel j 1)) h13j_w) hrow_w) ?_
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
      let rws := fun c => (Dp.host c).encode
      have hSpanC := buildTopReplySpan_meetsContract (w := w) (sec := 0) (k := B)
        (i := (k % P) % B) (rows := rws) (sections := secs) hspan hread hseek
      have hlc_w : (k % P) % B < 2 ^ w := hlc.trans hB_w
      refine runs_call_le hSpanC
        (vs := [replyAddr j (parentGroup x b j (k % P)), 0, B, (k % P) % B, dir + 2 * k])
        ?_ ?_ ⟨replyAddr j (parentGroup x b j (k % P)), dir + 2 * k, rfl, rfl, by decide, hlc, rfl,
          hAtP, lt_of_le_of_lt hEndP (by omega), hdst1_w, h1⟩ ?_
      · simp [evalArgs, Expr.eval, BinOp.eval, hlc_w, B]
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl
        · omega
        · exact Nat.two_pow_pos _
        · exact hB_w
        · exact hlc_w
        · omega
      · intro v mem' pos' hPost
        obtain ⟨rA', d', heq, hS0, hS1, hFrSpan⟩ := hPost
        simp only [List.cons.injEq, and_true, true_and] at heq
        obtain ⟨hE1, hE2⟩ := heq
        subst rA' d'
        have hFacts := buildTopReplyRowAddr_facts (sec := 0) (k := B) (i := (k % P) % B)
          (rows := rws) (sections := secs) rfl (by decide) hlc rfl hAtP
        refine ⟨hFinish mem' _ pos'
          (fun r hr => by dsimp only; simp [show r ≠ 15 by omega, show r ≠ 14 by omega,
            show r ≠ 13 by omega, show r ≠ 12 by omega, show r ≠ 11 by omega, show r ≠ 10 by omega,
            show r ≠ 9 by omega, show r ≠ 8 by omega])
          hFrSpan ?_ ?_ ?_ ?_, ?_⟩
        · simpa [src, buildTopSec3Src, P, ht, hlt, B, Dp, secs, rws] using hS0
        · simpa [rows, buildTopSec3Rows, P, ht, hlt, buildTopHierarchy, B, Dp, rws] using hS1
        · simpa [src, rows, buildTopSec3Src, buildTopSec3Rows, P, ht, hlt, buildTopHierarchy,
            B, Dp, secs, rws] using hFacts.1
        · have hEnd := hFacts.2.trans hEndP
          simpa [src, rows, buildTopSec3Src, buildTopSec3Rows, P, ht, hlt, buildTopHierarchy,
            B, Dp, secs, rws] using hEnd
        · simp [buildTopReplySpanContract, Expr.size, argsSize]
    · refine runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, hlt])
        (fun h => absurd rfl h) (fun _ => ?_)
      refine runs_seq_store_le
        (Expr.eval_reg_of_eq (v := dir + 2 * k) (by simp))
        (Expr.eval_reg_of_eq (v := emptyGraph) (by simp [r4])) ?_
      refine runs_store_le
        (Expr.eval_add (Expr.eval_reg_of_eq (v := dir + 2 * k) (by simp)) (Expr.eval_const h1) hdst1_w)
        (Expr.eval_const h2) ?_ ?_
      · refine hFinish _ _ _
          (fun r hr => by dsimp only; simp [show r ≠ 13 by omega, show r ≠ 12 by omega,
            show r ≠ 11 by omega, show r ≠ 10 by omega, show r ≠ 9 by omega, show r ≠ 8 by omega])
          (fun y hy0 hy1 => by dsimp only; rw [Function.update_of_ne hy1, Function.update_of_ne hy0])
          ?_ ?_ ?_ ?_
        · dsimp only
          rw [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self _)), Function.update_self]
          simp [src, buildTopSec3Src, P, ht, hlt]
        · dsimp only
          rw [Function.update_self]
          simp [rows, buildTopSec3Rows, P, ht, hlt, buildTopHierarchy, emptyGraph_encode]
        · simp only [src, rows, buildTopSec3Src, buildTopSec3Rows, P, ht, hlt, ↓reduceIte,
            buildTopHierarchy, emptyGraph_encode]
          exact hEmpAtSt
        · simp only [src, rows, buildTopSec3Src, buildTopSec3Rows, P, ht, hlt, ↓reduceIte,
            buildTopHierarchy, emptyGraph_encode]
          exact hEmpEnd
      · simp [Expr.size]

theorem buildTopSec3Dir_meetsContract
    {w f span read seek table D x b rootGraph emptyGraph dir : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {p : Program}
    (hp : p.procs[f]? = some (buildTopSec3Dir span))
    (hspan : p.procs[span]? = some (buildTopReplySpan read))
    (hread : p.procs[read]? = some (buildTopReplyRead seek))
    (hseek : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p f
      (buildTopSec3DirContract w table D x b rootGraph emptyGraph dir root reply replyAddr) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨rfl, hRep, hRootAt, hRootEnd, hEmpAt, hEmpEnd, hZero, hRoom, h13⟩ := hpre
  have h1 : 1 < 2 ^ w := by omega
  have hD1_w : D + 1 < 2 ^ w := by
    have : D + 1 ≤ (D + 1) * 2 ^ x := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos x)
    omega
  have htot_w : (D + 1) * 2 ^ x < 2 ^ w := by omega
  let rows := buildTopSec3Rows x b root reply
  let src := buildTopSec3Src x b rootGraph emptyGraph reply replyAddr
  let Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = 2 ^ x ∧
    st.regs 3 = rootGraph ∧ st.regs 4 = emptyGraph ∧ st.regs 5 = dir ∧
    st.regs 6 = (D + 1) * 2 ^ x ∧ st.regs 7 = k ∧
    (∀ y < dir, st.mem y = mem y) ∧ ZeroFrom st.mem (dir + 2 * k) ∧
    ∀ i < k, st.mem (dir + 2 * i) = src i ∧ st.mem (dir + 2 * i + 1) = (rows i).length ∧
      ListAt st.mem (src i) (rows i) ∧ src i + (rows i).length ≤ dir + 2 * ((D + 1) * 2 ^ x)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 7) (lo := .const 0) (hi := .reg 6)
    (body := buildTopSec3DirBody span)
    (P := fun st =>
      st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = 2 ^ x ∧
      st.regs 3 = rootGraph ∧ st.regs 4 = emptyGraph ∧ st.regs 5 = dir ∧
      st.regs 6 = (D + 1) * 2 ^ x ∧ st.mem = mem)
    (Inv := Inv) 200 0 ((D + 1) * 2 ^ x) (Nat.zero_le _) h1 (fun _ => htot_w)
    (fun st ⟨r0, r1, r2, r3, r4, r5, r6, hm⟩ => ⟨Expr.eval_const (Nat.two_pow_pos _), by
      refine ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp [r5],
        by simp [r6], by simp, fun _ _ => by simp [hm], by simpa [hm] using hZero,
        fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.2.2.1)
    (fun k _ hk => by
      have hb := buildTopSec3DirBody_triple hspan hread hseek hRep hRootAt hRootEnd
        hEmpAt hEmpEnd hRoom h13 hk
      exact Triple.conseq hb (fun _ hI => hI) (fun o st h => by
        cases o with
        | returned _ => exact h.elim
        | normal =>
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
          exact ⟨⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5],
            by simp [h6], by simp [h7], by simp, h9, h10, h11⟩, h8⟩) (fun _ _ => le_rfl))
  refine runs_start_le ?_
  unfold buildTopSec3Dir
  refine runs_seq_assign_le (v := (D + 1) * 2 ^ x)
    (Expr.eval_mul (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) hD1_w)
      (Expr.eval_reg_of_eq rfl) htot_w) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro st' hEnd
    obtain ⟨_, _, _, _, _, _, _, _, hFr', hZ', hRows'⟩ := hEnd
    refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _))
      ⟨rfl, ⟨le_rfl, hRows'⟩, hZ', hFr'⟩ ?_
    simp [buildTopSec3DirContract, Expr.size]; omega

/-- Contract for `buildTopSec3`: materializes section 3 at `dir + 2 * (D + 1) * P`
and returns its end address. -/
def buildTopSec3Contract (w table D x b rootGraph emptyGraph dir : ℕ) (root : Graph)
    (reply : ℕ → ℕ → BuildLevelData) (replyAddr : ℕ → ℕ → ℕ) : Contract where
  pre args mem :=
    let P := 2 ^ x
    let total := (D + 1) * P
    let sec3 := csrList total (buildTopSec3Rows x b root reply)
    args = [table, D, P, rootGraph, emptyGraph, dir] ∧
    BuildTopRepliesInMem table D x b reply replyAddr dir mem ∧
    GraphAt mem rootGraph root ∧ rootGraph + root.encode.length ≤ dir ∧
    ListAt mem emptyGraph [0, 0] ∧ emptyGraph + 2 ≤ dir ∧
    ZeroFrom mem dir ∧ dir + 2 * total + sec3.length < 2 ^ w ∧ 13 < 2 ^ w
  post args mem v mem' :=
    let P := 2 ^ x
    let total := (D + 1) * P
    let sec3 := csrList total (buildTopSec3Rows x b root reply)
    args = [table, D, P, rootGraph, emptyGraph, dir] ∧
    v = dir + 2 * total + sec3.length ∧
    ListAt mem' (dir + 2 * total) sec3 ∧
    ZeroFrom mem' v ∧
    ∀ y < dir, mem' y = mem y
  cost _ _ :=
    let total := (D + 1) * 2 ^ x
    let sec3 := csrList total (buildTopSec3Rows x b root reply)
    17 * sec3.length + 320 * total + 120

theorem buildTopSec3_meetsContract
    {w f dir3 gather row copy span read seek table D x b rootGraph emptyGraph dir : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {p : Program}
    (hp : p.procs[f]? = some (buildTopSec3 dir3 gather))
    (hd : p.procs[dir3]? = some (buildTopSec3Dir span))
    (hg : p.procs[gather]? = some (initCSRWrite row))
    (hrow : p.procs[row]? = some (buildTopRow copy))
    (hcopy : p.procs[copy]? = some buildCopyProc)
    (hspan : p.procs[span]? = some (buildTopReplySpan read))
    (hread : p.procs[read]? = some (buildTopReplyRead seek))
    (hseek : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p f
      (buildTopSec3Contract w table D x b rootGraph emptyGraph dir root reply replyAddr) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨rfl, hRep, hRootAt, hRootEnd, hEmpAt, hEmpEnd, hZero, hRoom, h13⟩ := hpre
  have h1 : 1 < 2 ^ w := by omega
  have hD1_w : D + 1 < 2 ^ w := by
    have : D + 1 ≤ (D + 1) * 2 ^ x := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos x)
    omega
  have htot_w : (D + 1) * 2 ^ x < 2 ^ w := by omega
  have h2tot_w : (D + 1) * 2 ^ x + (D + 1) * 2 ^ x < 2 ^ w := by omega
  have hdst_w : dir + ((D + 1) * 2 ^ x + (D + 1) * 2 ^ x) < 2 ^ w := by omega
  have hdst_eq : dir + ((D + 1) * 2 ^ x + (D + 1) * 2 ^ x) = dir + 2 * ((D + 1) * 2 ^ x) := by omega
  refine runs_start_le ?_
  unfold buildTopSec3
  refine runs_seq_assign_le (v := (D + 1) * 2 ^ x)
    (Expr.eval_mul (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const h1) hD1_w)
      (Expr.eval_reg_of_eq rfl) htot_w) ?_
  refine runs_seq_assign_le (v := dir + 2 * ((D + 1) * 2 ^ x))
    (Expr.eval_eq_of_eq (Expr.eval_add (Expr.eval_reg_of_eq rfl)
      (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) h2tot_w) hdst_w) hdst_eq) ?_
  refine runs_seq_call_le
    (buildTopSec3Dir_meetsContract (w := w) (table := table) (D := D) (x := x) (b := b)
      (rootGraph := rootGraph) (emptyGraph := emptyGraph) (dir := dir)
      (root := root) (reply := reply) (replyAddr := replyAddr) hd hspan hread hseek)
    (vs := [table, D, 2 ^ x, rootGraph, emptyGraph, dir]) rfl hw
    ⟨rfl, hRep, hRootAt, hRootEnd, hEmpAt, hEmpEnd, hZero, by omega, h13⟩ ?_
  intro _ mem1 pos1 hPost1
  obtain ⟨_, hDir1, hZ1, hFr1⟩ := hPost1
  refine runs_seq_call_le
    (buildTopGather_meetsContract (w := w) (ctx := dir) (k := (D + 1) * 2 ^ x)
      (rows := buildTopSec3Rows x b root reply)
      (src := buildTopSec3Src x b rootGraph emptyGraph reply replyAddr) hg hrow hcopy)
    (vs := [dir, (D + 1) * 2 ^ x, dir + 2 * ((D + 1) * 2 ^ x)]) rfl
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨dir + 2 * ((D + 1) * 2 ^ x), rfl, hDir1, hZ1, by simpa only [Nat.add_zero] using hRoom, h1⟩ ?_
  intro v2 mem2 pos2 hPost2
  obtain ⟨dst', ha, hv2, hAt2, hZ2, hFr2⟩ := hPost2
  simp only [List.cons.injEq, and_true, true_and] at ha
  subst dst'
  refine runs_ret_le (v := v2) (Expr.eval_reg_of_eq rfl)
    ⟨rfl, hv2, hAt2, hZ2, fun y hy => (hFr2 y (by omega)).trans (hFr1 y hy)⟩ ?_
  have hGC := buildTopGather_cost_le ((D + 1) * 2 ^ x) (buildTopSec3Rows x b root reply)
  simp only [buildTopSec3Contract, buildTopSec3DirContract, initCSRWriteContract,
    Expr.size, argsSize]
  omega

end MinCostFlow.HierPaths

end
