module

public import MinCostFlow.HierPaths.BuildTopSec4

/-!
# Assembling section 5 of `StaticData` (sibling connectors)

Reads all sibling connector tables from section 2 of the completed level replies,
populates a `D * 2^x * 2^b`-entry `(src, len)` directory indexed via `pairOfIdx`,
and invokes `buildTopGather` (`initCSRWrite (buildTopRow buildCopyProc)`) to
materialize section 5 of `StaticData`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Section 5 rows of `StaticData`. -/
def buildTopSec5Rows (x b : ℕ) (root : Graph) (reply : ℕ → ℕ → BuildLevelData) (k : ℕ) : List ℕ :=
  let H := buildTopHierarchy x b root reply
  let l := H.conn (pairOfIdx x b k).1 (pairOfIdx x b k).2.1 (pairOfIdx x b k).2.2
  csrList l.length fun i => connWords (l.getD i (0, 0, []))

/-- Source address for row `k` of section 5. -/
def buildTopSec5Src (x b emptyCSR : ℕ) (reply : ℕ → ℕ → BuildLevelData)
    (replyAddr : ℕ → ℕ → ℕ) (k : ℕ) : ℕ :=
  let j := (pairOfIdx x b k).1
  let c := (pairOfIdx x b k).2.1
  let c' := (pairOfIdx x b k).2.2
  if c < c' ∧ c' < numGroups x b (j + 1) ∧ parentGroup x b j c = parentGroup x b j c' then
    let B := branching x b j
    let p := parentGroup x b j c
    let D := reply j p
    let idx := (c % B) * B + (c' % B)
    buildTopReplyRowAddr (replyAddr j p) 2 (B * B) idx
      (fun u =>
        let pair := D.conn (u / B) (u % B)
        csrList pair.length fun i => connWords (pair.getD i (0, 0, [])))
      (buildTopReplySections D B)
  else emptyCSR

/-- Directory loop body for section 5.
Regs: `0=table, 1=D, 2=P, 3=twoPowB, 4=emptyCSR, 5=dir, 6=total, 7=k`. -/
def buildTopSec5DirBody (span : ℕ) : Stmt :=
  .assign 8 (.bin .div (.reg 7) (.reg 3)) ;;
  .assign 9 (.bin .mod (.reg 7) (.reg 3)) ;;
  .assign 10 (.bin .div (.reg 8) (.reg 2)) ;;
  .assign 11 (.bin .mod (.reg 8) (.reg 2)) ;;
  .assign 12 (.bin .add (.reg 5) (.bin .add (.reg 7) (.reg 7))) ;;
  .assign 13 (.bin .add (.reg 0) (.bin .mul (.const 13) (.reg 10))) ;;
  .assign 14 (.load (.bin .add (.reg 13) (.const 4))) ;;
  .assign 15 (.bin .mul (.load (.bin .add (.reg 13) (.const 5))) (.reg 14)) ;;
  .assign 16 (.bin .div (.reg 11) (.reg 14)) ;;
  .assign 17 (.bin .mul (.reg 16) (.reg 14)) ;;
  .assign 18 (.bin .add (.reg 17)
    (.bin .mod (.bin .sub (.bin .add (.reg 9) (.reg 3)) (.bin .mod (.reg 17) (.reg 3))) (.reg 3))) ;;
  .assign 19 (.bin .mul
    (.bin .mul (.bin .lt (.reg 11) (.reg 18)) (.bin .lt (.reg 18) (.reg 15)))
    (.bin .eq (.bin .div (.reg 18) (.reg 14)) (.reg 16))) ;;
  .cond (.reg 19)
    (.assign 20 (.load (.bin .add (.load (.bin .add (.reg 13) (.const 1))) (.reg 16))) ;;
      .assign 21 (.bin .add (.bin .mul (.bin .mod (.reg 11) (.reg 14)) (.reg 14))
        (.bin .mod (.reg 18) (.reg 14))) ;;
      .call 22 span [.reg 20, .const 2, .bin .mul (.reg 14) (.reg 14), .reg 21, .reg 12])
    (.store (.reg 12) (.reg 4) ;;
      .store (.bin .add (.reg 12) (.const 1)) (.const 1))

/-- Populate the `D * P * 2^b` `(src, len)` directory for section 5.
Args: `[table, D, P, twoPowB, emptyCSR, dir]`. -/
def buildTopSec5Dir (span : ℕ) : Stmt :=
  .assign 6 (.bin .mul (.bin .mul (.reg 1) (.reg 2)) (.reg 3)) ;;
  forRange 7 (.const 0) (.reg 6) (buildTopSec5DirBody span) ;;
  .ret (.const 0)

/-- Build section 5 at `dir + 2 * (D * P * 2^b)` and return its end address.
Args: `[table, D, P, twoPowB, emptyCSR, dir]`. -/
def buildTopSec5 (dir5 gather : ℕ) : Stmt :=
  .assign 6 (.bin .mul (.bin .mul (.reg 1) (.reg 2)) (.reg 3)) ;;
  .assign 7 (.bin .add (.reg 5) (.bin .add (.reg 6) (.reg 6))) ;;
  .call 8 dir5 [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5] ;;
  .call 8 gather [.reg 5, .reg 6, .reg 7] ;;
  .ret (.reg 8)

theorem buildTopSec5Dir_noRand (span : ℕ) : (buildTopSec5Dir span).NoRand := by
  simp [buildTopSec5Dir, buildTopSec5DirBody, forRange, forUp, Stmt.NoRand]

theorem buildTopSec5_noRand (dir5 gather : ℕ) : (buildTopSec5 dir5 gather).NoRand := by
  simp [buildTopSec5, Stmt.NoRand]

/-- Contract for `buildTopSec5Dir`. -/
def buildTopSec5DirContract (w table D x b emptyCSR dir : ℕ) (root : Graph)
    (reply : ℕ → ℕ → BuildLevelData) (replyAddr : ℕ → ℕ → ℕ) : Contract where
  pre args mem :=
    let P := 2 ^ x
    let twoPowB := 2 ^ b
    let total := D * P * twoPowB
    args = [table, D, P, twoPowB, emptyCSR, dir] ∧
    1 ≤ D ∧ b ≤ x ∧
    BuildTopRepliesInMem table D x b reply replyAddr dir mem ∧
    ListAt mem emptyCSR [0] ∧ emptyCSR + 1 ≤ dir ∧
    ZeroFrom mem dir ∧ dir + 2 * total < 2 ^ w ∧ 13 < 2 ^ w ∧ 2 * P < 2 ^ w
  post args mem _ mem' :=
    let P := 2 ^ x
    let twoPowB := 2 ^ b
    let total := D * P * twoPowB
    args = [table, D, P, twoPowB, emptyCSR, dir] ∧
    buildTopRowDir dir total (buildTopSec5Rows x b root reply)
      (buildTopSec5Src x b emptyCSR reply replyAddr) (dir + 2 * total) mem' ∧
    ZeroFrom mem' (dir + 2 * total) ∧
    ∀ y < dir, mem' y = mem y
  cost _ _ := 260 * (D * 2 ^ x * 2 ^ b) + 40

private lemma emptyCSR5_eq (f : ℕ → List ℕ) : csrList 0 f = [0] := by
  simp [csrList, csrOffsets, csrData]

private lemma idx_div_mod {B a b : ℕ} (hb : b < B) :
    (a * B + b) / B = a ∧ (a * B + b) % B = b := by
  have hB : 0 < B := Nat.pos_of_ne_zero (by omega)
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm a B, Nat.mul_add_div hB, Nat.div_eq_of_lt hb, Nat.add_zero]
  · rw [Nat.mul_comm a B, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

private lemma idx_lt_sq {B a b : ℕ} (ha : a < B) (hb : b < B) : a * B + b < B * B := by
  have h1 : (a + 1) * B ≤ B * B := Nat.mul_le_mul_right B (Nat.succ_le_of_lt ha)
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

private lemma sec5Src_end_le_dir {table D x b emptyCSR dir i : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {mem0 : ℕ → ℕ}
    (hRep : BuildTopRepliesInMem table D x b reply replyAddr dir mem0)
    (hEmpEnd : emptyCSR + 1 ≤ dir)
    (hi : i < D * 2 ^ x * 2 ^ b) :
    buildTopSec5Src x b emptyCSR reply replyAddr i +
      (buildTopSec5Rows x b root reply i).length ≤ dir := by
  dsimp only [buildTopSec5Src, buildTopSec5Rows]
  set j := (pairOfIdx x b i).1
  set c := (pairOfIdx x b i).2.1
  set c' := (pairOfIdx x b i).2.2
  have hjlt : j < D := by
    have hq : i / 2 ^ b < D * 2 ^ x := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b)).mpr hi
    exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos x)).mpr hq
  by_cases hact : c < c' ∧ c' < numGroups x b (j + 1) ∧ parentGroup x b j c = parentGroup x b j c'
  · obtain ⟨hlt, hc'ng, hpar⟩ := hact
    have hcng : c < numGroups x b (j + 1) := hlt.trans hc'ng
    have hBpos : 0 < branching x b j := branching_pos
    have hp : parentGroup x b j c < numGroups x b j := by
      unfold parentGroup
      rw [Nat.div_lt_iff_lt_mul hBpos, ← numGroups_succ]; exact hcng
    have hlc : c % branching x b j < branching x b j := Nat.mod_lt _ hBpos
    have hlc' : c' % branching x b j < branching x b j := Nat.mod_lt _ hBpos
    have hidx : (c % branching x b j) * branching x b j + c' % branching x b j <
        branching x b j * branching x b j := idx_lt_sq hlc hlc'
    have hdm := idx_div_mod hlc' (a := c % branching x b j)
    obtain ⟨_, hAtP, hEndP⟩ := hRep.reply_entry j hjlt _ hp
    set B := branching x b j
    set Dp := reply j (parentGroup x b j c)
    have hF := (buildTopReplyRowAddr_facts (sec := 2) (k := B * B)
      (i := (c % B) * B + c' % B)
      (rows := fun u =>
        let pair := Dp.conn (u / B) (u % B)
        csrList pair.length fun m => connWords (pair.getD m (0, 0, [])))
      (sections := buildTopReplySections Dp B) rfl (by decide) hidx rfl hAtP).2
    have hconn : (buildTopHierarchy x b root reply).conn j c c' = Dp.conn (c % B) (c' % B) := by
      simp [buildTopHierarchy, hlt, hc'ng, hpar, Dp, B]
    have hEnd := hF.trans hEndP
    simp only [hdm.1, hdm.2] at hEnd
    simpa only [hlt, hc'ng, hpar, and_self, ↓reduceIte, hconn] using hEnd
  · have hconn : (buildTopHierarchy x b root reply).conn j c c' = [] := by
      simp [buildTopHierarchy, hact]
    simp only [hact, ↓reduceIte, hconn, List.length_nil, emptyCSR5_eq, List.length_singleton]
    exact hEmpEnd

private theorem buildTopSec5DirBody_triple
    {w span read seek table D x b emptyCSR dir k : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ}
    {mem0 : ℕ → ℕ} {p : Program}
    (hspan : p.procs[span]? = some (buildTopReplySpan read))
    (hread : p.procs[read]? = some (buildTopReplyRead seek))
    (hseek : p.procs[seek]? = some initCSRSeek)
    (hD1 : 1 ≤ D) (hbx : b ≤ x)
    (hRep : BuildTopRepliesInMem table D x b reply replyAddr dir mem0)
    (hEmpAt : ListAt mem0 emptyCSR [0]) (hEmpEnd : emptyCSR + 1 ≤ dir)
    (hRoom : dir + 2 * (D * 2 ^ x * 2 ^ b) < 2 ^ w) (h13 : 13 < 2 ^ w) (h2Pw : 2 * 2 ^ x < 2 ^ w)
    (hk : k < D * 2 ^ x * 2 ^ b) :
    let P := 2 ^ x
    let twoPowB := 2 ^ b
    let total := D * P * twoPowB
    let rows := buildTopSec5Rows x b root reply
    let src := buildTopSec5Src x b emptyCSR reply replyAddr
    Triple w p
      (fun st =>
        st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = P ∧ st.regs 3 = twoPowB ∧
        st.regs 4 = emptyCSR ∧ st.regs 5 = dir ∧ st.regs 6 = total ∧ st.regs 7 = k ∧
        (∀ y < dir, st.mem y = mem0 y) ∧ ZeroFrom st.mem (dir + 2 * k) ∧
        ∀ i < k, st.mem (dir + 2 * i) = src i ∧ st.mem (dir + 2 * i + 1) = (rows i).length ∧
          ListAt st.mem (src i) (rows i) ∧ src i + (rows i).length ≤ dir + 2 * total)
      (buildTopSec5DirBody span)
      (normalPost fun st =>
        st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = P ∧ st.regs 3 = twoPowB ∧
        st.regs 4 = emptyCSR ∧ st.regs 5 = dir ∧ st.regs 6 = total ∧ st.regs 7 = k ∧
        (∀ y < dir, st.mem y = mem0 y) ∧ ZeroFrom st.mem (dir + 2 * (k + 1)) ∧
        ∀ i < k + 1, st.mem (dir + 2 * i) = src i ∧ st.mem (dir + 2 * i + 1) = (rows i).length ∧
          ListAt st.mem (src i) (rows i) ∧ src i + (rows i).length ≤ dir + 2 * total)
      (fun _ => 240) := by
  dsimp only
  set P := 2 ^ x
  set twoPowB := 2 ^ b
  set total := D * P * twoPowB
  set rows := buildTopSec5Rows x b root reply
  set src := buildTopSec5Src x b emptyCSR reply replyAddr
  intro st ω hPre
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, hFr, hZ, hPrev⟩ := hPre
  have hPpos : 0 < P := Nat.two_pow_pos x
  have h2Bpos : 0 < twoPowB := Nat.two_pow_pos b
  have h2BleP : twoPowB ≤ P := Nat.pow_le_pow_right (by decide) hbx
  have hPw : P < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have h4 : 4 < 2 ^ w := by omega
  have h5 : 5 < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  set q := k / twoPowB
  set rem := k % twoPowB
  set j := q / P
  set c := q % P
  have hq_lt : q < D * P := (Nat.div_lt_iff_lt_mul h2Bpos).mpr hk
  have hjlt : j < D := (Nat.div_lt_iff_lt_mul hPpos).mpr hq_lt
  have hq_w : q < 2 ^ w := (Nat.div_le_self k twoPowB).trans_lt hk_w
  have hc_lt : c < P := Nat.mod_lt q hPpos
  have hc_w : c < 2 ^ w := hc_lt.trans hPw
  have hrem_lt : rem < twoPowB := Nat.mod_lt k h2Bpos
  have h2k_w : k + k < 2 ^ w := by omega
  have hdst_w : dir + (k + k) < 2 ^ w := by omega
  have hdst1_w : dir + 2 * k + 1 < 2 ^ w := by omega
  have hdst_eq : dir + (k + k) = dir + 2 * k := by omega
  have hRepSt := hRep.mono le_rfl hFr
  have hEmpAtSt : ListAt st.mem emptyCSR [0] := fun u hu => by
    have hu1 : u < 1 := by simpa using hu
    exact (hFr _ (by omega)).trans (hEmpAt u hu)
  have hTbl := hRepSt.table_end
  have hrow_w : table + 13 * j < 2 ^ w := by omega
  have h13j_w : 13 * j < 2 ^ w := by omega
  have hrow4_w : table + 13 * j + 4 < 2 ^ w := by omega
  have hrow5_w : table + 13 * j + 5 < 2 ^ w := by omega
  have hrow1_w : table + 13 * j + 1 < 2 ^ w := by omega
  have hB_eq := hRepSt.row_branch j hjlt
  have hCnt_eq := hRepSt.row_count j hjlt
  have hRD_eq := hRepSt.row_replyDir j hjlt
  set B := branching x b j
  have hng_succ : numGroups x b j * B = numGroups x b (j + 1) := (numGroups_succ x b j).symm
  have hng_le_P : numGroups x b (j + 1) ≤ P :=
    (Nat.le_mul_of_pos_right _ groupSize_pos).trans (le_of_eq numGroups_mul_groupSize)
  have hng_w : numGroups x b (j + 1) < 2 ^ w := hng_le_P.trans_lt hPw
  have hB_pos : 0 < B := branching_pos
  have hB_le_2B : B ≤ twoPowB := branching_le_pow j
  have hB_le_P : B ≤ P := hB_le_2B.trans h2BleP
  have hB_w : B < 2 ^ w := hB_le_P.trans_lt hPw
  have hBB_le_tot : B * B ≤ total := by
    calc B * B ≤ P * twoPowB := Nat.mul_le_mul hB_le_P hB_le_2B
      _ ≤ D * (P * twoPowB) := Nat.le_mul_of_pos_left _ hD1
      _ = D * P * twoPowB := by ring
  have hBB_w : B * B < 2 ^ w := lt_of_le_of_lt hBB_le_tot (by omega)
  set pGrp := c / B
  set L := pGrp * B
  have hL_le_c : L ≤ c := by
    change c / B * B ≤ c
    rw [Nat.mul_comm]; exact Nat.mul_div_le c B
  have hL_w : L < 2 ^ w := lt_of_le_of_lt hL_le_c hc_w
  have hRemAdd_w : rem + twoPowB < 2 ^ w := by omega
  have hSub_w : rem + twoPowB - L % twoPowB < 2 ^ w := by omega
  set c' := L + (rem + twoPowB - L % twoPowB) % twoPowB
  have hc'_lt_2P : c' < 2 * P := by
    have hmod_lt : (rem + twoPowB - L % twoPowB) % twoPowB < twoPowB := Nat.mod_lt _ h2Bpos
    omega
  have hc'_w : c' < 2 ^ w := hc'_lt_2P.trans h2Pw
  have hPair : pairOfIdx x b k = (j, c, c') := rfl
  have hFinish : ∀ (mem' : ℕ → ℕ) (regs' : ℕ → ℕ) (pos' : ℕ),
      (∀ r ≤ 7, regs' r = st.regs r) →
      (∀ y, y ≠ dir + 2 * k → y ≠ dir + 2 * k + 1 → mem' y = st.mem y) →
      mem' (dir + 2 * k) = src k →
      mem' (dir + 2 * k + 1) = (rows k).length →
      ListAt st.mem (src k) (rows k) →
      src k + (rows k).length ≤ dir →
      let st' : State := ⟨mem', regs', pos'⟩
      st'.regs 0 = table ∧ st'.regs 1 = D ∧ st'.regs 2 = P ∧ st'.regs 3 = twoPowB ∧
      st'.regs 4 = emptyCSR ∧ st'.regs 5 = dir ∧ st'.regs 6 = total ∧ st'.regs 7 = k ∧
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
      (hRegs 6 (by decide)).trans r6, (hRegs 7 (by decide)).trans r7, hFr', hZ', ?_⟩
    intro i hi
    by_cases hik : i = k
    · subst i
      refine ⟨hS0, hS1, fun u hu => (hMemFr _ (by omega) (by omega)).trans (hListK u hu), by omega⟩
    · have hilt : i < k := by omega
      obtain ⟨ha, hb, hc, hd⟩ := hPrev i hilt
      have hlt_dir : src i + (rows i).length ≤ dir :=
        sec5Src_end_le_dir hRep hEmpEnd (hilt.trans hk)
      refine ⟨(hMemFr _ (by omega) (by omega)).trans ha,
        (hMemFr _ (by omega) (by omega)).trans hb,
        fun u hu => (hMemFr _ (by omega) (by omega)).trans (hc u hu), hd⟩
  refine runs_start_le ?_
  unfold buildTopSec5DirBody
  refine runs_seq_assign_le (v := q)
    (Expr.eval_div (Expr.eval_reg_of_eq r7) (Expr.eval_reg_of_eq r3) hk_w) ?_
  refine runs_seq_assign_le (v := rem)
    (Expr.eval_mod
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact r7))
      (Expr.eval_reg_of_eq (by dsimp only; rw [Function.update_of_ne (by decide)]; exact r3)) hk_w) ?_
  refine runs_seq_assign_le (v := j)
    (Expr.eval_div (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [r2])) hq_w) ?_
  refine runs_seq_assign_le (v := c)
    (Expr.eval_mod (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [r2])) hq_w) ?_
  refine runs_seq_assign_le (v := dir + 2 * k)
    (Expr.eval_eq_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (by simp [r5]))
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r7]))
        (Expr.eval_reg_of_eq (by simp [r7])) h2k_w) hdst_w) hdst_eq) ?_
  refine runs_seq_assign_le (v := table + 13 * j)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r0]))
      (Expr.eval_mul (Expr.eval_const h13) (Expr.eval_reg_of_eq (by simp)) h13j_w) hrow_w) ?_
  refine runs_seq_assign_le (v := B)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_const h4) hrow4_w) hB_eq) ?_
  refine runs_seq_assign_le (v := numGroups x b (j + 1))
    (Expr.eval_eq_of_eq (Expr.eval_mul
      (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_const h5) hrow5_w) hCnt_eq)
      (Expr.eval_reg_of_eq (by simp)) (hng_succ.symm ▸ hng_w)) hng_succ) ?_
  refine runs_seq_assign_le (v := pGrp)
    (Expr.eval_div (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) hc_w) ?_
  refine runs_seq_assign_le (v := L)
    (Expr.eval_mul (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) hL_w) ?_
  refine runs_seq_assign_le (v := c')
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_mod
        (Expr.eval_sub
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [r3])) hRemAdd_w)
          (Expr.eval_mod (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp [r3])) hL_w)
          hRemAdd_w)
        (Expr.eval_reg_of_eq (by simp [r3])) hSub_w) hc'_w) ?_
  let flag : ℕ :=
    (if c < c' then 1 else 0) * (if c' < numGroups x b (j + 1) then 1 else 0) *
      (if c' / B = pGrp then 1 else 0)
  refine runs_seq_assign_le (v := flag) ?_ ?_
  · refine Expr.eval_mul (Expr.eval_mul ?_ ?_ ?_) ?_ ?_
    · show Expr.eval w _ (.bin .lt (.reg 11) (.reg 18)) = some (if c < c' then 1 else 0)
      split_ifs <;> simp [Expr.eval, BinOp.eval, *]
    · show Expr.eval w _ (.bin .lt (.reg 18) (.reg 15)) =
        some (if c' < numGroups x b (j + 1) then 1 else 0)
      split_ifs <;> simp [Expr.eval, BinOp.eval, *]
    · split_ifs <;> omega
    · show Expr.eval w _ (.bin .eq (.bin .div (.reg 18) (.reg 14)) (.reg 16)) =
        some (if c' / B = pGrp then 1 else 0)
      have hdiv_w : c' / B < 2 ^ w := (Nat.div_le_self _ _).trans_lt hc'_w
      have hpGrp_w : pGrp < 2 ^ w := (Nat.div_le_self _ _).trans_lt hc_w
      split_ifs <;> simp [Expr.eval, BinOp.eval, *]
    · split_ifs <;> omega
  by_cases hact : c < c' ∧ c' < numGroups x b (j + 1) ∧ parentGroup x b j c = parentGroup x b j c'
  · obtain ⟨hlt, hc'ng, hpar⟩ := hact
    have hFlag1 : flag = 1 := by
      have hp' : c' / B = pGrp := hpar.symm
      simp [flag, hlt, hc'ng, hp']
    have hcng : c < numGroups x b (j + 1) := hlt.trans hc'ng
    have hp : pGrp < numGroups x b j := by
      change c / B < numGroups x b j
      rw [Nat.div_lt_iff_lt_mul hB_pos, ← numGroups_succ]; exact hcng
    have hlc : c % B < B := Nat.mod_lt _ hB_pos
    have hlc' : c' % B < B := Nat.mod_lt _ hB_pos
    have hidx_lt : (c % B) * B + c' % B < B * B := idx_lt_sq hlc hlc'
    have hidx_w : (c % B) * B + c' % B < 2 ^ w := hidx_lt.trans hBB_w
    have hmul_w : (c % B) * B < 2 ^ w := by omega
    have hdm := idx_div_mod hlc' (a := c % B)
    obtain ⟨hrAddr_eq, hAtP, hEndP⟩ := hRepSt.reply_entry j hjlt pGrp hp
    have hrd_end := hRepSt.replyDir_end j hjlt
    have hrd_p_w : buildTopScheduleReplies table D x j + pGrp < 2 ^ w := by omega
    refine runs_cond_le (v := 1) (by simp [Expr.eval, hFlag1]) (fun _ => ?_)
      (fun h => absurd h one_ne_zero)
    refine runs_seq_assign_le (v := replyAddr j pGrp)
      (Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (v := table + 13 * j) (by simp))
          (Expr.eval_const h1) hrow1_w) hRD_eq)
        (Expr.eval_reg_of_eq (v := pGrp) (by simp)) hrd_p_w) hrAddr_eq) ?_
    refine runs_seq_assign_le (v := (c % B) * B + c' % B)
      (Expr.eval_add
        (Expr.eval_mul
          (Expr.eval_mod (Expr.eval_reg_of_eq (v := c) (by simp))
            (Expr.eval_reg_of_eq (v := B) (by simp)) hc_w)
          (Expr.eval_reg_of_eq (v := B) (by simp)) hmul_w)
        (Expr.eval_mod (Expr.eval_reg_of_eq (v := c') (by simp))
          (Expr.eval_reg_of_eq (v := B) (by simp)) hc'_w) hidx_w) ?_
    let Dp := reply j pGrp
    let secs := buildTopReplySections Dp B
    let rws : ℕ → List ℕ := fun u =>
      let pair := Dp.conn (u / B) (u % B)
      csrList pair.length fun m => connWords (pair.getD m (0, 0, []))
    have hSpanC := buildTopReplySpan_meetsContract (w := w) (sec := 2) (k := B * B)
      (i := (c % B) * B + c' % B) (rows := rws) (sections := secs) hspan hread hseek
    refine runs_call_le hSpanC
      (vs := [replyAddr j pGrp, 2, B * B, (c % B) * B + c' % B, dir + 2 * k])
      ?_ ?_ ⟨replyAddr j pGrp, dir + 2 * k, rfl, rfl, by decide, hidx_lt, rfl,
        hAtP, lt_of_le_of_lt hEndP (by omega), hdst1_w, h1⟩ ?_
    · simp [evalArgs, Expr.eval, BinOp.eval, h2, hBB_w]
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · omega
      · exact h2
      · exact hBB_w
      · exact hidx_w
      · omega
    · intro v mem' pos' hPost
      obtain ⟨rA', d', heq, hS0, hS1, hFrSpan⟩ := hPost
      simp only [List.cons.injEq, and_true, true_and] at heq
      obtain ⟨hE1, hE2⟩ := heq
      subst rA' d'
      have hFacts := buildTopReplyRowAddr_facts (sec := 2) (k := B * B)
        (i := (c % B) * B + c' % B) (rows := rws) (sections := secs) rfl (by decide) hidx_lt rfl hAtP
      have hconn : (buildTopHierarchy x b root reply).conn j c c' = Dp.conn (c % B) (c' % B) := by
        dsimp only [buildTopHierarchy]
        rw [ite_eq_left ⟨hlt, hc'ng, hpar⟩]
        rfl
      have hRowEq : rws ((c % B) * B + c' % B) = rows k := by
        dsimp only [rws, rows, buildTopSec5Rows]
        rw [hPair, hdm.1, hdm.2, hconn]
      have hSrcEq : buildTopReplyRowAddr (replyAddr j pGrp) 2 (B * B) ((c % B) * B + c' % B)
          rws secs = src k := by
        dsimp only [src, buildTopSec5Src]
        rw [hPair, ite_eq_left ⟨hlt, hc'ng, hpar⟩]
        rfl
      refine ⟨hFinish mem' _ pos'
        (fun r hr => by dsimp only; simp [show r ≠ 22 by omega, show r ≠ 21 by omega,
          show r ≠ 20 by omega, show r ≠ 19 by omega, show r ≠ 18 by omega, show r ≠ 17 by omega,
          show r ≠ 16 by omega, show r ≠ 15 by omega, show r ≠ 14 by omega, show r ≠ 13 by omega,
          show r ≠ 12 by omega, show r ≠ 11 by omega, show r ≠ 10 by omega, show r ≠ 9 by omega,
          show r ≠ 8 by omega])
        hFrSpan (hS0.trans hSrcEq) (hS1.trans (congrArg List.length hRowEq))
        (by rw [← hSrcEq, ← hRowEq]; exact hFacts.1)
        (by rw [← hSrcEq, ← hRowEq]; exact hFacts.2.trans hEndP), ?_⟩
      simp [buildTopReplySpanContract, Expr.size, argsSize]
  · have hFlag0 : flag = 0 := by
      dsimp only [flag]
      by_cases h1' : c < c'
      · by_cases h2' : c' < numGroups x b (j + 1)
        · have h3' : c' / B ≠ pGrp := fun heq => hact ⟨h1', h2', heq.symm⟩
          simp [h1', h2', h3']
        · simp [h1', h2']
      · simp [h1']
    refine runs_cond_le (v := 0) (by simp [Expr.eval, hFlag0])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine runs_seq_store_le
      (Expr.eval_reg_of_eq (v := dir + 2 * k) (by simp))
      (Expr.eval_reg_of_eq (v := emptyCSR) (by simp [r4])) ?_
    refine runs_store_le
      (Expr.eval_add (Expr.eval_reg_of_eq (v := dir + 2 * k) (by simp)) (Expr.eval_const h1) hdst1_w)
      (Expr.eval_const h1) ?_ ?_
    · have hconn : (buildTopHierarchy x b root reply).conn j c c' = [] := by
        simp [buildTopHierarchy, hact]
      have hSrcEq : emptyCSR = src k := by
        dsimp only [src, buildTopSec5Src]
        rw [hPair]; simp [hact]
      have hRowEq : rows k = [0] := by
        dsimp only [rows, buildTopSec5Rows]
        rw [hPair, hconn]; exact emptyCSR5_eq _
      refine hFinish _ _ _
        (fun r hr => by dsimp only; simp [show r ≠ 19 by omega, show r ≠ 18 by omega,
          show r ≠ 17 by omega, show r ≠ 16 by omega, show r ≠ 15 by omega, show r ≠ 14 by omega,
          show r ≠ 13 by omega, show r ≠ 12 by omega, show r ≠ 11 by omega, show r ≠ 10 by omega,
          show r ≠ 9 by omega, show r ≠ 8 by omega])
        (fun y hy0 hy1 => by dsimp only; rw [Function.update_of_ne hy1, Function.update_of_ne hy0])
        ?_ ?_ ?_ ?_
      · dsimp only
        rw [Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self _)), Function.update_self]
        exact hSrcEq
      · dsimp only
        rw [Function.update_self, hRowEq]; rfl
      · rw [← hSrcEq, hRowEq]; exact hEmpAtSt
      · rw [← hSrcEq, hRowEq]; exact hEmpEnd
    · simp [Expr.size]

theorem buildTopSec5Dir_meetsContract
    {w f span read seek table D x b emptyCSR dir : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {p : Program}
    (hp : p.procs[f]? = some (buildTopSec5Dir span))
    (hspan : p.procs[span]? = some (buildTopReplySpan read))
    (hread : p.procs[read]? = some (buildTopReplyRead seek))
    (hseek : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p f
      (buildTopSec5DirContract w table D x b emptyCSR dir root reply replyAddr) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨rfl, hD1, hbx, hRep, hEmpAt, hEmpEnd, hZero, hRoom, h13, h2Pw⟩ := hpre
  have h1 : 1 < 2 ^ w := by omega
  have hDP_w : D * 2 ^ x < 2 ^ w := by
    have : D * 2 ^ x ≤ D * 2 ^ x * 2 ^ b := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos b)
    omega
  have htot_w : D * 2 ^ x * 2 ^ b < 2 ^ w := by omega
  let rows := buildTopSec5Rows x b root reply
  let src := buildTopSec5Src x b emptyCSR reply replyAddr
  let Inv : ℕ → State → Prop := fun k st =>
    st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = 2 ^ x ∧ st.regs 3 = 2 ^ b ∧
    st.regs 4 = emptyCSR ∧ st.regs 5 = dir ∧ st.regs 6 = D * 2 ^ x * 2 ^ b ∧ st.regs 7 = k ∧
    (∀ y < dir, st.mem y = mem y) ∧ ZeroFrom st.mem (dir + 2 * k) ∧
    ∀ i < k, st.mem (dir + 2 * i) = src i ∧ st.mem (dir + 2 * i + 1) = (rows i).length ∧
      ListAt st.mem (src i) (rows i) ∧ src i + (rows i).length ≤ dir + 2 * (D * 2 ^ x * 2 ^ b)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 7) (lo := .const 0) (hi := .reg 6)
    (body := buildTopSec5DirBody span)
    (P := fun st =>
      st.regs 0 = table ∧ st.regs 1 = D ∧ st.regs 2 = 2 ^ x ∧ st.regs 3 = 2 ^ b ∧
      st.regs 4 = emptyCSR ∧ st.regs 5 = dir ∧ st.regs 6 = D * 2 ^ x * 2 ^ b ∧ st.mem = mem)
    (Inv := Inv) 240 0 (D * 2 ^ x * 2 ^ b) (Nat.zero_le _) h1 (fun _ => htot_w)
    (fun st ⟨r0, r1, r2, r3, r4, r5, r6, hm⟩ => ⟨Expr.eval_const (Nat.two_pow_pos _), by
      refine ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp [r5],
        by simp [r6], by simp, fun _ _ => by simp [hm], by simpa [hm] using hZero,
        fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.2.2.1)
    (fun k _ hk => by
      have hb := buildTopSec5DirBody_triple (root := root) hspan hread hseek hD1 hbx
        hRep hEmpAt hEmpEnd hRoom h13 h2Pw hk
      exact Triple.conseq hb (fun _ hI => hI) (fun o st h => by
        cases o with
        | returned _ => exact h.elim
        | normal =>
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
          exact ⟨⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5],
            by simp [h6], by simp [h7], by simp, h9, h10, h11⟩, h8⟩) (fun _ _ => le_rfl))
  refine runs_start_le ?_
  unfold buildTopSec5Dir
  refine runs_seq_assign_le (v := D * 2 ^ x * 2 ^ b)
    (Expr.eval_mul (Expr.eval_mul (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hDP_w)
      (Expr.eval_reg_of_eq rfl) htot_w) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro st' hEnd
    obtain ⟨_, _, _, _, _, _, _, _, hFr', hZ', hRows'⟩ := hEnd
    refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _))
      ⟨rfl, ⟨le_rfl, hRows'⟩, hZ', hFr'⟩ ?_
    simp [buildTopSec5DirContract, Expr.size]; omega

/-- Contract for `buildTopSec5`: materializes section 5 at `dir + 2 * (D * P * 2^b)`
and returns its end address. -/
def buildTopSec5Contract (w table D x b emptyCSR dir : ℕ) (root : Graph)
    (reply : ℕ → ℕ → BuildLevelData) (replyAddr : ℕ → ℕ → ℕ) : Contract where
  pre args mem :=
    let P := 2 ^ x
    let twoPowB := 2 ^ b
    let total := D * P * twoPowB
    let sec5 := csrList total (buildTopSec5Rows x b root reply)
    args = [table, D, P, twoPowB, emptyCSR, dir] ∧
    1 ≤ D ∧ b ≤ x ∧
    BuildTopRepliesInMem table D x b reply replyAddr dir mem ∧
    ListAt mem emptyCSR [0] ∧ emptyCSR + 1 ≤ dir ∧
    ZeroFrom mem dir ∧ dir + 2 * total + sec5.length < 2 ^ w ∧ 13 < 2 ^ w ∧ 2 * P < 2 ^ w
  post args mem v mem' :=
    let P := 2 ^ x
    let twoPowB := 2 ^ b
    let total := D * P * twoPowB
    let sec5 := csrList total (buildTopSec5Rows x b root reply)
    args = [table, D, P, twoPowB, emptyCSR, dir] ∧
    v = dir + 2 * total + sec5.length ∧
    ListAt mem' (dir + 2 * total) sec5 ∧
    ZeroFrom mem' v ∧
    ∀ y < dir, mem' y = mem y
  cost _ _ :=
    let total := D * 2 ^ x * 2 ^ b
    let sec5 := csrList total (buildTopSec5Rows x b root reply)
    17 * sec5.length + 360 * total + 120

theorem buildTopSec5_meetsContract
    {w f dir5 gather row copy span read seek table D x b emptyCSR dir : ℕ}
    {root : Graph} {reply : ℕ → ℕ → BuildLevelData} {replyAddr : ℕ → ℕ → ℕ} {p : Program}
    (hp : p.procs[f]? = some (buildTopSec5 dir5 gather))
    (hd : p.procs[dir5]? = some (buildTopSec5Dir span))
    (hg : p.procs[gather]? = some (initCSRWrite row))
    (hrow : p.procs[row]? = some (buildTopRow copy))
    (hcopy : p.procs[copy]? = some buildCopyProc)
    (hspan : p.procs[span]? = some (buildTopReplySpan read))
    (hread : p.procs[read]? = some (buildTopReplyRead seek))
    (hseek : p.procs[seek]? = some initCSRSeek) :
    MeetsContract w p f
      (buildTopSec5Contract w table D x b emptyCSR dir root reply replyAddr) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨rfl, hD1, hbx, hRep, hEmpAt, hEmpEnd, hZero, hRoom, h13, h2Pw⟩ := hpre
  have h1 : 1 < 2 ^ w := by omega
  have hDP_w : D * 2 ^ x < 2 ^ w := by
    have : D * 2 ^ x ≤ D * 2 ^ x * 2 ^ b := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos b)
    omega
  have htot_w : D * 2 ^ x * 2 ^ b < 2 ^ w := by omega
  have h2tot_w : D * 2 ^ x * 2 ^ b + D * 2 ^ x * 2 ^ b < 2 ^ w := by omega
  have hdst_w : dir + (D * 2 ^ x * 2 ^ b + D * 2 ^ x * 2 ^ b) < 2 ^ w := by omega
  have hdst_eq : dir + (D * 2 ^ x * 2 ^ b + D * 2 ^ x * 2 ^ b) =
      dir + 2 * (D * 2 ^ x * 2 ^ b) := by omega
  refine runs_start_le ?_
  unfold buildTopSec5
  refine runs_seq_assign_le (v := D * 2 ^ x * 2 ^ b)
    (Expr.eval_mul (Expr.eval_mul (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) hDP_w)
      (Expr.eval_reg_of_eq rfl) htot_w) ?_
  refine runs_seq_assign_le (v := dir + 2 * (D * 2 ^ x * 2 ^ b))
    (Expr.eval_eq_of_eq (Expr.eval_add (Expr.eval_reg_of_eq rfl)
      (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_reg_of_eq rfl) h2tot_w) hdst_w) hdst_eq) ?_
  refine runs_seq_call_le
    (buildTopSec5Dir_meetsContract (w := w) (table := table) (D := D) (x := x) (b := b)
      (emptyCSR := emptyCSR) (dir := dir)
      (root := root) (reply := reply) (replyAddr := replyAddr) hd hspan hread hseek)
    (vs := [table, D, 2 ^ x, 2 ^ b, emptyCSR, dir]) rfl hw
    ⟨rfl, hD1, hbx, hRep, hEmpAt, hEmpEnd, hZero, by omega, h13, h2Pw⟩ ?_
  intro _ mem1 pos1 hPost1
  obtain ⟨_, hDir1, hZ1, hFr1⟩ := hPost1
  refine runs_seq_call_le
    (buildTopGather_meetsContract (w := w) (ctx := dir) (k := D * 2 ^ x * 2 ^ b)
      (rows := buildTopSec5Rows x b root reply)
      (src := buildTopSec5Src x b emptyCSR reply replyAddr) hg hrow hcopy)
    (vs := [dir, D * 2 ^ x * 2 ^ b, dir + 2 * (D * 2 ^ x * 2 ^ b)]) rfl
    (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> omega)
    ⟨dir + 2 * (D * 2 ^ x * 2 ^ b), rfl, hDir1, hZ1, by simpa only [Nat.add_zero] using hRoom, h1⟩ ?_
  intro v2 mem2 pos2 hPost2
  obtain ⟨dst', ha, hv2, hAt2, hZ2, hFr2⟩ := hPost2
  simp only [List.cons.injEq, and_true, true_and] at ha
  subst dst'
  refine runs_ret_le (v := v2) (Expr.eval_reg_of_eq rfl)
    ⟨rfl, hv2, hAt2, hZ2, fun y hy => (hFr2 y (by omega)).trans (hFr1 y hy)⟩ ?_
  have hGC := buildTopGather_cost_le (D * 2 ^ x * 2 ^ b) (buildTopSec5Rows x b root reply)
  simp only [buildTopSec5Contract, buildTopSec5DirContract, initCSRWriteContract,
    Expr.size, argsSize]
  omega

end MinCostFlow.HierPaths

end
