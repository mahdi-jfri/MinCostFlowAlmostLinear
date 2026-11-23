module

public import MinCostFlow.HierPaths.DelProgTouched

/-!
# Testing a vertex for output

After the cursor passes, a touched vertex is ready to report when its support cursor is at
the end and its pruned bit is still clear. The flag is computed from the layout.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The report flag for a vertex after the support passes. -/
def HierConcrete.delReport (x : HierConcrete) (v : ℕ) : Prop :=
  x.ms.st.supCur v = (x.H.A.C.supportArray v).length ∧ v ∉ x.ms.abs.Vhat

instance (x : HierConcrete) (v : ℕ) : Decidable (x.delReport v) := by
  unfold HierConcrete.delReport
  infer_instance

/-- Set register 57 to one when the touched vertex in register 39 must be reported. -/
def delReportTest : Stmt :=
  .seq (delCursorSetup 9 20 3 (readHdr 0))
    (.assign 57 (.bin .mul (.bin .eq (.reg 42) (.reg 43))
      (.bin .sub (.const 1) (readSec numSec 0 17 (.reg 39)))))

theorem delReportTest_noRand : delReportTest.NoRand := by
  simp [delReportTest, delCursorSetup_noRand, Stmt.NoRand]

/-- The test reads the new support cursor and the old pruned bit without changing memory. -/
theorem delReportTest_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b v : ℕ} {R : ℕ → ℕ} {M : (ℕ → ℕ) → Prop}
    (h0 : R 0 = b) (h39 : R 39 = v) (hv : v < x.n)
    (hb : b + x.encode.length < 2 ^ w)
    (hM : ∀ mem, M mem → ListAt mem b x.encode) :
    Triple w p (fun s => s.regs = R ∧ M s.mem) delReportTest
      (normalPost fun s => s.regs 0 = b ∧ s.regs 39 = v ∧
        s.regs 57 = (if x.delReport v then 1 else 0) ∧ M s.mem)
      (fun _ => 130) := by
  let f := fun u => (x.H.A.C.supportArray u).flatMap entryWords
  let old := x.ms.st.supCur v
  let N := (x.H.A.C.supportArray v).length
  let R' := Function.update (Function.update
    (Function.update (Function.update R 40 (delCsrStart x.n f v)) 41
      (delCsrStart x.n f (v + 1))) 42 ((f v).length / 3)) 43 old
  have hs20 : x.sections.getD 20 [] = tabList x.n x.ms.st.supCur := rfl
  have hi20 : v < (x.sections.getD 20 []).length := by rw [hs20]; simpa using hv
  have hv20 : (x.sections.getD 20 [])[v] = old := by
    rw [← List.getD_eq_getElem _ 0 hi20, hs20]
    simp [tabList, List.getD_eq_getElem?_getD, hv, old]
  have h3 : 3 < 2 ^ w := by have := x.le_length_encode; omega
  have hsetup := delCursorSetup_triple (w := w) (p := p) x
    (lists := 9) (curs := 20) (width := 3) (count := readHdr 0) (f := f)
    (by decide) (by decide) rfl hv h0 h39 hi20 hv20 h3 hM hb
    (fun s hm hr => by
      simpa [HierConcrete.header, HierConcrete.n] using
        x.eval_readHdr hb hr (hM _ hm) (k := 0) (by decide))
  have htest : Triple w p (fun s => s.regs = R' ∧ M s.mem)
      (.assign 57 (.bin .mul (.bin .eq (.reg 42) (.reg 43))
        (.bin .sub (.const 1) (readSec numSec 0 17 (.reg 39)))))
      (normalPost fun s => s.regs = Function.update R' 57 (if x.delReport v then 1 else 0) ∧ M s.mem)
      (fun _ => 25) := by
    refine (triple_assign_exact ?_).mono_cost (fun _ _ => by decide)
    intro s hr hm
    have hN : s.regs 42 = N := by simp [hr, R', f, N, List.length_flatMap, length_entryWords]
    have hold : s.regs 43 = old := by simp [hr, R']
    have hb0 : s.regs 0 = b := by rw [hr]; simpa [R'] using h0
    have hb39 : s.regs 39 = v := by rw [hr]; simpa [R'] using h39
    have hs17 : x.sections.getD 17 [] = bitsList x.n (fun u => decide (u ∈ x.ms.abs.Vhat)) := rfl
    have hv17 : v < (x.sections.getD 17 []).length := by rw [hs17]; simpa using hv
    have hbit := eval_readSec (w := w) (show ListAt s.mem b (layoutList x.sections) from hM _ hm)
      hb hb0 (i := 17) (by rw [x.length_sections']; decide) (Expr.eval_reg_of_eq hb39) hv17
    rw [x.length_sections', ← List.getD_eq_getElem _ 0 hv17, hs17,
      List.getD_eq_getElem _ 0 (by simpa using hv)] at hbit
    simp only [bitsList, List.getElem_map, List.getElem_range] at hbit
    have heq := Expr.eval_eq_op (w := w) (Expr.eval_reg_of_eq hN) (Expr.eval_reg_of_eq hold) (by omega)
    by_cases he : N = old <;> by_cases hs : v ∈ x.ms.abs.Vhat
    all_goals
      simp [he] at heq
      simp [hs] at hbit
      have hsub := Expr.eval_sub (Expr.eval_const (by omega : 1 < 2 ^ w)) hbit (by omega)
      simp at hsub
      have h := Expr.eval_mul heq hsub (by omega)
      simpa [he, hs, HierConcrete.delReport, N, old, eq_comm] using h
  unfold delReportTest
  refine ((Triple.seq_normal_const hsetup htest).strengthen_post ?_).mono_cost ?_
  · intro o s hs
    cases o <;> try contradiction
    obtain ⟨hr, hm⟩ := hs
    refine ⟨?_, ?_, by simp [hr], hm⟩
    · simpa [hr, R'] using h0
    · simpa [hr, R'] using h39
  · intro s hs
    decide

/-- Set the pruned bit for the vertex in register 39. -/
def delVhatSet : Stmt :=
  .store (secAddr numSec 0 17 (.reg 39)) (.const 1)

theorem delVhatSet_noRand : delVhatSet.NoRand := by
  simp [delVhatSet, Stmt.NoRand]

/-- Set one pruned bit and keep all other memory outside the block. -/
theorem delVhatSet_triple {w : ℕ} {p : Program} (x : HierConcrete) {b v : ℕ}
    {F : State → Prop} (hv : v < x.n) (hb : b + x.encode.length < 2 ^ w)
    (hF : ∀ s, F s → s.regs 0 = b ∧ s.regs 39 = v ∧ ListAt s.mem b x.encode) :
    Triple w p F delVhatSet (normalPost fun s =>
      ∃ s₀, F s₀ ∧ s.regs = s₀.regs ∧
        ListAt s.mem b (x.withVhat (insert v x.ms.abs.Vhat)).encode ∧
        ∀ i, (i < b ∨ b + x.encode.length ≤ i) → s.mem i = s₀.mem i)
      (fun _ => 14) := by
  have hs17 : x.sections.getD 17 [] = bitsList x.n (fun u => decide (u ∈ x.ms.abs.Vhat)) := rfl
  have hv17 : v < (x.sections.getD 17 []).length := by rw [hs17]; simpa using hv
  have H := triple_writeSec' (w := w) (p := p) (P := F) (bs := x.sections) (r := 0)
    (i := 17) (by rw [x.length_sections']; decide) (ke := .reg 39) (ve := .const 1)
    (k := fun _ => v) (v := fun _ => 1) (fun s hs => by
      obtain ⟨h0, h39, hmem⟩ := hF s hs
      exact ⟨hmem, h0, Expr.eval_reg_of_eq h39, hv17,
        Expr.eval_const (by have := x.le_length_encode; omega)⟩) hb
  rw [x.length_sections'] at H
  unfold delVhatSet
  refine (H.strengthen_post fun o s h => ?_).mono_cost (fun _ _ => by decide)
  cases o <;> try contradiction
  obtain ⟨s₀, hs₀, hregs, _, hmem, hf⟩ := h
  refine ⟨s₀, hs₀, hregs, ?_, hf⟩
  change ListAt s.mem b (layoutList (x.withVhat (insert v x.ms.abs.Vhat)).sections)
  rwa [x.sections_setVhat]

theorem HierConcrete.length_encode_withVhat (x : HierConcrete) (V : Finset ℕ) :
    (x.withVhat V).encode.length = x.encode.length := by
  have hs : (x.withVhat V).sections =
      x.sections.set 17 (bitsList x.n fun v => decide (v ∈ V)) := rfl
  show (layoutList (x.withVhat V).sections).length = (layoutList x.sections).length
  rw [hs]
  exact length_layoutList_set _ (by simp [sections])

/-- Append the vertex in register `39`, with base and length in `58` and `59`. -/
def delVertexPush : Stmt :=
  .seq (.store (.bin .add (.reg 58) (.reg 59)) (.reg 39))
    (.assign 59 (.bin .add (.reg 59) (.const 1)))

/-- Append one vertex and advance the work-list length in constant time. -/
theorem delVertexPush_triple {w : ℕ} {p : Program} {b base c : ℕ} {block L : List ℕ}
    {R mem0 : ℕ → ℕ} (hbase : R 58 = base) (hcount : R 59 = L.length)
    (hc : R 39 = c) (hdisj : b + block.length ≤ base) (hw : base + L.length + 1 < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b block ∧ ListAt s.mem base L ∧ s.mem = mem0)
      delVertexPush
      (normalPost fun s => s.regs = Function.update R 59 (L.length + 1) ∧
        ListAt s.mem b block ∧ ListAt s.mem base (L ++ [c]) ∧
        s.mem = Function.update mem0 (base + L.length) c)
      (fun _ => 12) := by
  let M := fun mem => ListAt mem b block ∧ ListAt mem base (L ++ [c]) ∧
    mem = Function.update mem0 (base + L.length) c
  have hstore : Triple w p
      (fun s => s.regs = R ∧ ListAt s.mem b block ∧ ListAt s.mem base L ∧ s.mem = mem0)
      (.store (.bin .add (.reg 58) (.reg 59)) (.reg 39))
      (normalPost fun s => s.regs = R ∧ M s.mem)
      (fun _ => (Expr.bin .add (.reg 58) (.reg 59)).size + (Expr.reg 39).size + 1) := by
    refine Triple.store (addr := fun _ => base + L.length) (val := fun _ => c)
      (fun s hs => Expr.eval_add (Expr.eval_reg_of_eq (by rw [hs.1, hbase]))
        (Expr.eval_reg_of_eq (by rw [hs.1, hcount])) (by omega))
      (fun s hs => Expr.eval_reg_of_eq (by rw [hs.1, hc])) (fun s hs => ?_)
    obtain ⟨hr, hblk, hL, hmem⟩ := hs
    refine ⟨hr, ?_, listAt_append_one hL c, by rw [hmem]⟩
    refine listAt_congr (fun k hk => ?_) hblk
    exact (Function.update_of_ne (by omega) _ _).symm
  unfold delVertexPush
  refine (Triple.seq_normal_const hstore (triple_assign_exact (M := M) ?_)).mono_cost ?_
  · intro s hs _
    exact Expr.eval_add (Expr.eval_reg_of_eq (by rw [hs, hcount]))
      (Expr.eval_const (by omega)) (by omega)
  · intro s hs
    decide

theorem delVertexPush_noRand : delVertexPush.NoRand := by
  simp [delVertexPush, Stmt.NoRand]

/-- Test a touched vertex, then set its bit and append it if this is its first report. -/
def delReportVertex : Stmt :=
  .seq delReportTest (.cond (.reg 57) (.seq delVhatSet delVertexPush) .nop)

theorem delReportVertex_noRand : delReportVertex.NoRand := by
  simp [delReportVertex, Stmt.NoRand, delReportTest_noRand, delVhatSet_noRand,
    delVertexPush_noRand]

/-- Report one touched vertex and preserve every other output slot. -/
theorem delReportVertex_triple {w : ℕ} {p : Program} (x : HierConcrete) {b base v : ℕ}
    {R mem0 : ℕ → ℕ} {L : List ℕ} (h0 : R 0 = b) (h39 : R 39 = v)
    (h58 : R 58 = base) (h59 : R 59 = L.length)
    (hv : v < x.n) (hblk : b + x.encode.length ≤ base)
    (hw : base + L.length + 1 < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base L ∧ s.mem = mem0) delReportVertex
      (normalPost fun s =>
        let out := if x.delReport v then L ++ [v] else L
        let y := if x.delReport v then x.withVhat (insert v x.ms.abs.Vhat) else x
        s.regs 0 = b ∧ s.regs 58 = base ∧ s.regs 59 = out.length ∧
        ListAt s.mem b y.encode ∧ ListAt s.mem base out ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j)
      (fun _ => 165) := by
  let M := fun mem => ListAt mem b x.encode ∧ ListAt mem base L ∧ mem = mem0
  let out := if x.delReport v then L ++ [v] else L
  let y := if x.delReport v then x.withVhat (insert v x.ms.abs.Vhat) else x
  let Q := fun s : State => s.regs 0 = b ∧ s.regs 58 = base ∧ s.regs 59 = out.length ∧
    ListAt s.mem b y.encode ∧ ListAt s.mem base out ∧
    ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
      (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j
  let P := fun s : State => s.regs 0 = b ∧ s.regs 39 = v ∧
    s.regs 57 = (if x.delReport v then 1 else 0) ∧ M s.mem ∧
    s.regs 58 = base ∧ s.regs 59 = L.length
  have hb : b + x.encode.length < 2 ^ w := by omega
  have htest := Triple.regs_frame (n := 58)
    (show Stmt.WritesBelow 58 delReportTest by
      simp [delReportTest, delCursorSetup, delCsrSetup, Stmt.WritesBelow])
    (delReportTest_triple (w := w) (p := p) (M := M) x h0 h39 hv hb (fun _ h => h.1)) R
  have htest' := (htest.weaken_pre (P' := fun s => s.regs = R ∧ M s.mem)
    (fun s hs => ⟨hs, fun r _ => congrFun hs.1 r⟩)).strengthen_post
      (Q' := normalPost P) (fun o s h => by
        cases o <;> try exact False.elim h.1
        obtain ⟨⟨hr0, hr39, hf, hm⟩, hr⟩ := h
        exact ⟨hr0, hr39, hf, hm, (hr 58 (by decide)).trans h58, (hr 59 (by decide)).trans h59⟩)
  have hcond : Triple w p P (.cond (.reg 57) (.seq delVhatSet delVertexPush) .nop)
      (normalPost Q) (fun _ => 33) := by
    refine (Triple.cond (val := fun s => s.regs 57) (fun _ _ => Expr.eval_reg_of_eq rfl)
      (T_t := fun _ => 27) (T_f := fun _ => 1) ?_ (Triple.nop ?_)).mono_cost ?_
    · intro s ω ⟨hs, hne⟩
      have hyes : x.delReport v := by
        by_contra hn
        exact hne (by simp [hs.2.2.1, hn])
      have hy : y = x.withVhat (insert v x.ms.abs.Vhat) := by simp [y, hyes]
      have hout : out = L ++ [v] := by simp [out, hyes]
      have hylen : y.encode.length = x.encode.length := by rw [hy, x.length_encode_withVhat]
      let Mid := fun t : State => t.regs = s.regs ∧ ListAt t.mem b y.encode ∧
        ListAt t.mem base L ∧ ∀ j, (j < b ∨ b + x.encode.length ≤ j) → t.mem j = mem0 j
      have H := delVhatSet_triple (w := w) (p := p) x (F := fun t => t = s) hv hb
        (fun t ht => by subst t; exact ⟨hs.1, hs.2.1, hs.2.2.2.1.1⟩)
      have H' := H.strengthen_post (Q' := normalPost Mid) (fun o t h => by
        cases o <;> try contradiction
        obtain ⟨s₀, ht, hr, hb', hf⟩ := h
        subst s₀
        refine ⟨hr, hy.symm ▸ hb', ?_, fun j hj => (hf j hj).trans
          (congrFun hs.2.2.2.1.2.2 j)⟩
        exact listAt_congr (fun j _ => (hf _ (Or.inr (by omega))).symm) hs.2.2.2.1.2.1)
      have hpush : Triple w p Mid delVertexPush (normalPost Q) (fun _ => 12) := by
        intro t ω' ht
        obtain ⟨hr, hb', hL, hf⟩ := ht
        have hsep : b + y.encode.length ≤ base := (congrArg (b + ·) hylen).le.trans hblk
        have HH := delVertexPush_triple (w := w) (p := p) (b := b) (R := s.regs)
          (mem0 := t.mem) (base := base) (L := L) (c := v) (block := y.encode) hs.2.2.2.2.1 hs.2.2.2.2.2 hs.2.1 hsep hw
        obtain ⟨o, t', k, hrun, h, hcost⟩ := HH t ω' ⟨hr, hb', hL, rfl⟩
        cases o <;> try contradiction
        obtain ⟨hr', hb'', hL', hm⟩ := h
        refine ⟨_, t', k, hrun, ?_, hcost⟩
        refine ⟨by simpa [hr'] using hs.1, by simpa [hr'] using hs.2.2.2.2.1,
          by simp [hr', hout], hb'', hout.symm ▸ hL', ?_⟩
        intro j hj hj'
        have hne : j ≠ base + L.length := by
          rw [hout, List.length_append, List.length_singleton] at hj'
          omega
        rw [hm, Function.update_of_ne hne]
        exact hf j hj
      exact Triple.seq_normal_const H' hpush s ω rfl
    · intro s ⟨hs, hz⟩
      have hn : ¬ x.delReport v := by intro h; simp [hs.2.2.1, h] at hz
      have hx : y = x := by simp [y, hn]
      have ho : out = L := by simp [out, hn]
      refine ⟨hs.1, hs.2.2.2.2.1, ho.symm ▸ hs.2.2.2.2.2,
        hx.symm ▸ hs.2.2.2.1.1, ho.symm ▸ hs.2.2.2.1.2.1,
        fun j _ _ => congrFun hs.2.2.2.1.2.2 j⟩
    · intro s hs
      split <;> decide
  exact (Triple.seq_normal_const htest' hcond).mono_cost (fun _ _ => by decide)

/-- The first reports from a pass over a list of touched vertices. -/
def HierConcrete.delReports (x : HierConcrete) (vs : List ℕ) : List ℕ :=
  delCollect x.ms.abs.Vhat (vs.filter fun v =>
    x.ms.st.supCur v = (x.H.A.C.supportArray v).length)

/-- The output contains exactly the previously unpruned vertices whose cursor is at the end. -/
theorem HierConcrete.mem_delReports (x : HierConcrete) (vs : List ℕ) (v : ℕ) :
    v ∈ x.delReports vs ↔ v ∈ vs ∧ x.delReport v := by
  simp [delReports, mem_delCollect, delReport, and_assoc]

theorem HierConcrete.delReports_nodup (x : HierConcrete) (vs : List ℕ) :
    (x.delReports vs).Nodup :=
  nodup_delCollect ..

/-- Inserting the vertices found in a prefix gives the bit set for scanning the suffix. -/
theorem HierConcrete.delReports_append (x : HierConcrete) (vs ws : List ℕ) :
    x.delReports (vs ++ ws) = x.delReports vs ++
      (x.withVhat (x.ms.abs.Vhat ∪ (x.delReports vs).toFinset)).delReports ws := by
  simp only [delReports, List.filter_append, delCollect_append]
  have he : x.ms.abs.Vhat ∪ (x.delReports vs).toFinset =
      x.ms.abs.Vhat ∪ (vs.filter fun v =>
        x.ms.st.supCur v = (x.H.A.C.supportArray v).length).toFinset := by
    ext v
    simp only [Finset.mem_union, List.mem_toFinset, x.mem_delReports, HierConcrete.delReport,
      List.mem_filter, decide_eq_true_eq]
    tauto
  change _ = x.delReports vs ++ delCollect (x.ms.abs.Vhat ∪ (x.delReports vs).toFinset)
    (ws.filter fun v => x.ms.st.supCur v = (x.H.A.C.supportArray v).length)
  rw [he]
  rfl

/-- The report pass produces the set difference required by operation 0. -/
theorem HierConcrete.delReports_spec (x : HierConcrete) {st : DelState} {e ξ κ : ℕ}
    (hA : x.H.A.Spec x.ms.abs.G ξ κ) (hG : x.ms.abs.G.IsValid)
    (hinv : x.H.A.DelInv x.ms.abs.G st)
    (hcur : x.ms.st.supCur = (x.H.A.deleteState st e).supCur)
    (hV : x.ms.abs.Vhat = x.H.A.C.prunedSet x.ms.abs.G (x.H.A.surv st)) :
    let A := x.H.A
    let out := x.delReports (A.delSupportVisits st e)
    out.Nodup ∧ out.toFinset = A.C.prunedSet x.ms.abs.G (A.newSurv st e) \ x.ms.abs.Vhat := by
  dsimp only
  refine ⟨x.delReports_nodup _, ?_⟩
  have hn := (x.H.A.deleteState_inv hA hinv e).1
  have hdel := (x.H.A.delete_spec hA hG hinv e).2.2.2
  rw [StaticArrays.surv_deleteState] at hdel
  rw [hV, ← hdel]
  ext v
  simp only [List.mem_toFinset, x.mem_delReports, StaticArrays.mem_delSupportVisits,
    HierConcrete.delReport, hcur, hV, StaticArrays.deleteOut, List.mem_filter, decide_eq_true_eq]
  by_cases hv : v ∈ x.H.A.touchedVerts st e
  · have hvn := x.H.A.lt_of_mem_touchedVerts hA hG hinv e hv
    have hold := (x.H.A.supCur_eq_len_iff hinv hvn).not
    have hle := (hinv.supCur v hvn).1
    have hlt : v ∉ x.H.A.C.prunedSet x.ms.abs.G (x.H.A.surv st) ↔
        st.supCur v < (x.H.A.C.supportArray v).length := by
      rw [← hold]
      omega
    simp only [hv, true_and, hlt]
    tauto
  · simp [hv]

/-- The state after reporting a prefix of the touched vertices. -/
def HierConcrete.afterReports (x : HierConcrete) (vs : List ℕ) : HierConcrete :=
  x.withVhat (x.ms.abs.Vhat ∪ (x.delReports vs).toFinset)

theorem HierConcrete.delReports_singleton (x : HierConcrete) (v : ℕ) :
    x.delReports [v] = if x.delReport v then [v] else [] := by
  by_cases h : x.ms.st.supCur v = (x.H.A.C.supportArray v).length <;>
    by_cases hv : v ∈ x.ms.abs.Vhat <;> simp [delReports, delCollect, delReport, h, hv]

theorem HierConcrete.afterReports_nil (x : HierConcrete) : x.afterReports [] = x := by
  simp [afterReports, delReports, delCollect, withVhat]

theorem HierConcrete.afterReports_append_one (x : HierConcrete) (vs : List ℕ) (v : ℕ) :
    x.afterReports (vs ++ [v]) =
      if (x.afterReports vs).delReport v then
        (x.afterReports vs).withVhat (insert v (x.afterReports vs).ms.abs.Vhat)
      else x.afterReports vs := by
  rw [afterReports, x.delReports_append]
  change x.withVhat (x.ms.abs.Vhat ∪
    (x.delReports vs ++ (x.afterReports vs).delReports [v]).toFinset) = _
  rw [HierConcrete.delReports_singleton]
  by_cases h : (x.afterReports vs).delReport v
  · simp only [ite_eq_left h, List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
    have he : x.ms.abs.Vhat ∪ ((x.delReports vs).toFinset ∪ insert v ∅) =
        insert v (x.ms.abs.Vhat ∪ (x.delReports vs).toFinset) := by
      ext k
      simp only [Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
      tauto
    rw [he]
    rfl
  · simp only [ite_eq_right h, List.append_nil]
    rfl

theorem HierConcrete.delReports_length_le (x : HierConcrete) {vs : List ℕ}
    (hv : ∀ v ∈ vs, v < x.n) : (x.delReports vs).length ≤ x.n := by
  have hsub : (x.delReports vs).toFinset ⊆ Finset.range x.n := by
    intro v h
    exact Finset.mem_range.mpr (hv v ((x.mem_delReports vs v).mp (List.mem_toFinset.mp h)).1)
  have hc := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup (x.delReports_nodup vs), Finset.card_range] at hc

/-- Read a touched vertex from an index expression and conditionally report it. -/
def delReportRead (vertex : Expr) : Stmt :=
  .seq (.assign 39 vertex) delReportVertex

theorem delReportRead_noRand (vertex : Expr) : (delReportRead vertex).NoRand := by
  simp [delReportRead, Stmt.NoRand, delReportVertex_noRand]

theorem delReportRead_writesBelow (vertex : Expr) :
    Stmt.WritesBelow 60 (delReportRead vertex) := by
  simp [delReportRead, delReportVertex, delReportTest, delCursorSetup, delCsrSetup,
    delVhatSet, delVertexPush, Stmt.WritesBelow]

/-- Report a vertex supplied by a read in the current register and memory state. -/
theorem delReportRead_triple {w : ℕ} {p : Program} (x : HierConcrete) {b base v : ℕ}
    {R mem0 : ℕ → ℕ} {L : List ℕ} {vertex : Expr}
    (h0 : R 0 = b) (h58 : R 58 = base) (h59 : R 59 = L.length)
    (hv : v < x.n) (hblk : b + x.encode.length ≤ base)
    (hw : base + L.length + 1 < 2 ^ w)
    (hread : ∀ s : State, s.regs = R → s.mem = mem0 → vertex.eval w s = some v) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base L ∧ s.mem = mem0) (delReportRead vertex)
      (normalPost fun s =>
        let out := L ++ x.delReports [v]
        s.regs 0 = b ∧ s.regs 58 = base ∧ s.regs 59 = out.length ∧
        ListAt s.mem b (x.afterReports [v]).encode ∧ ListAt s.mem base out ∧
        ∀ j, (j < b ∨ b + x.encode.length ≤ j) →
          (j < base + L.length ∨ base + out.length ≤ j) → s.mem j = mem0 j)
      (fun _ => vertex.size + 167) := by
  let M := fun mem => ListAt mem b x.encode ∧ ListAt mem base L ∧ mem = mem0
  have H := triple_assign_exact (w := w) (p := p) (M := M) (r := 39)
    (e := vertex) (v := v) (fun s hr hm => hread s hr hm.2.2)
  have H' := delReportVertex_triple (w := w) (p := p) (R := Function.update R 39 v)
    (base := base) (L := L) (mem0 := mem0) x (by simpa using h0) (by simp)
    (by simpa using h58) (by simpa using h59) hv hblk hw
  have hstate : x.afterReports [v] =
      if x.delReport v then x.withVhat (insert v x.ms.abs.Vhat) else x := by
    simpa only [List.nil_append, HierConcrete.afterReports_nil] using
      x.afterReports_append_one [] v
  have hout : L ++ x.delReports [v] = if x.delReport v then L ++ [v] else L := by
    rw [x.delReports_singleton]
    split <;> simp
  unfold delReportRead
  refine ((Triple.seq_normal_const H H').strengthen_post ?_).mono_cost (fun _ _ => by omega)
  intro o s hp
  cases o <;> try contradiction
  simpa only [hstate, hout] using hp

theorem HierConcrete.afterReports_append (x : HierConcrete) (vs ws : List ℕ) :
    x.afterReports (vs ++ ws) = (x.afterReports vs).afterReports ws := by
  rw [afterReports, x.delReports_append, List.toFinset_append]
  change x.withVhat (x.ms.abs.Vhat ∪
    ((x.delReports vs).toFinset ∪ ((x.afterReports vs).delReports ws).toFinset)) =
    x.withVhat ((x.ms.abs.Vhat ∪ (x.delReports vs).toFinset) ∪
      ((x.afterReports vs).delReports ws).toFinset)
  rw [Finset.union_assoc]

end MinCostFlow.HierPaths

end
