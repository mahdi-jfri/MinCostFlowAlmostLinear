module

public import MinCostFlow.LinkCut.Prog.SplayStepPullBlocks
public import MinCostFlow.LinkCut.Prog.SplayStepPushDownBlocks

namespace MinCostFlow.LinkCut.Prog

/-!
`WordRAM` execution proofs for `pullBody`:
- `pullPtrs_exec`, `pullVcntHdr_exec`, `pullCsumPair_exec`, `pullMinNumStmt_runs`,
- `pullBody_runs` upgrading `PullPre` to `TreeMemMatch w h L st'.mem nodesBase cap (.node x l r) parId pp`
  plus `LctFrame` and amortized step+heap bound `K_PULL L`.
-/

open WordRAM MinCostFlow.Num

@[expose] public section

/-! ### Small combinator and pure arithmetic helpers -/

theorem runs_seq3_normal {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ s₃ rest : Stmt} {st₀ st₃ st₄ : State} {o : Outcome} {c₁₃ c₄ : ℕ}
    (h13 : Runs w p ω (s₁ ;; s₂ ;; s₃) st₀ .normal st₃ c₁₃)
    (h4 : Runs w p ω rest st₃ o st₄ c₄) :
    Runs w p ω (s₁ ;; s₂ ;; s₃ ;; rest) st₀ o st₄ (c₁₃ + c₄ + 1) := by
  rcases runs_seq_iff.mp h13 with ⟨_, _, _, hret, _⟩ | ⟨st₁, c₁, c₂₃, h1, h23, hceq⟩
  · cases hret
  · have h234 := runs_seq2_normal h23 h4
    have hseq := runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂₃ + c₄ + 1, h1, h234, rfl⟩)
    simpa [hceq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hseq

theorem runs_seq4_normal {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ s₃ s₄ rest : Stmt} {st₀ st₄ st₅ : State} {o : Outcome} {c₁₄ c₅ : ℕ}
    (h14 : Runs w p ω (s₁ ;; s₂ ;; s₃ ;; s₄) st₀ .normal st₄ c₁₄)
    (h5 : Runs w p ω rest st₄ o st₅ c₅) :
    Runs w p ω (s₁ ;; s₂ ;; s₃ ;; s₄ ;; rest) st₀ o st₅ (c₁₄ + c₅ + 1) := by
  rcases runs_seq_iff.mp h14 with ⟨_, _, _, hret, _⟩ | ⟨st₁, c₁, c₂₄, h1, h24, hceq⟩
  · cases hret
  · have h245 := runs_seq3_normal h24 h5
    have hseq := runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂₄ + c₅ + 1, h1, h245, rfl⟩)
    simpa [hceq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hseq

theorem runs_seq6_normal {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ s₃ s₄ s₅ s₆ rest : Stmt} {st₀ st₆ st₇ : State} {o : Outcome} {c₁₆ c₇ : ℕ}
    (h16 : Runs w p ω (s₁ ;; s₂ ;; s₃ ;; s₄ ;; s₅ ;; s₆) st₀ .normal st₆ c₁₆)
    (h7 : Runs w p ω rest st₆ o st₇ c₇) :
    Runs w p ω (s₁ ;; s₂ ;; s₃ ;; s₄ ;; s₅ ;; s₆ ;; rest) st₀ o st₇ (c₁₆ + c₇ + 1) := by
  rcases runs_seq_iff.mp h16 with ⟨_, _, _, hret, _⟩ | ⟨st₁, c₁, c₂₆, h1, h26, hceq⟩
  · cases hret
  · have h267 := runs_seq5_normal h26 h7
    have hseq := runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂₆ + c₇ + 1, h1, h267, rfl⟩)
    simpa [hceq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hseq

theorem runs_seq8_normal {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ rest : Stmt} {st₀ st₈ st₉ : State} {o : Outcome} {c₁₈ c₉ : ℕ}
    (h18 : Runs w p ω (s₁ ;; s₂ ;; s₃ ;; s₄ ;; s₅ ;; s₆ ;; s₇ ;; s₈) st₀ .normal st₈ c₁₈)
    (h9 : Runs w p ω rest st₈ o st₉ c₉) :
    Runs w p ω (s₁ ;; s₂ ;; s₃ ;; s₄ ;; s₅ ;; s₆ ;; s₇ ;; s₈ ;; rest) st₀ o st₉ (c₁₈ + c₉ + 1) := by
  rcases runs_seq_iff.mp h18 with ⟨_, _, _, hret, _⟩ | ⟨st₁, c₁, c₂₈, h1, h28, hceq1⟩
  · cases hret
  · rcases runs_seq_iff.mp h28 with ⟨_, _, _, hret, _⟩ | ⟨st₂, c₂, c₃₈, h2, h38, hceq2⟩
    · cases hret
    · have h389 := runs_seq6_normal h38 h9
      have hseq := runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂ + (c₃₈ + c₉ + 1) + 1, h1,
        runs_seq_iff.mpr (Or.inr ⟨st₂, c₂, c₃₈ + c₉ + 1, h2, h389, rfl⟩), rfl⟩)
      simpa [hceq1, hceq2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hseq

theorem combineIntMinAgg_endpoints_lt {W : ℕ} {A B : IntMinAgg}
    (hW : 0 < W)
    (hA : A.first < W ∧ A.last < W) (hB : B.first < W ∧ B.last < W) :
    (combineIntMinAgg A B).first < W ∧ (combineIntMinAgg A B).last < W := by
  simp only [combineIntMinAgg]
  split_ifs <;> simp [hW, hA.1, hA.2, hB.1, hB.2]

theorem listIntMinAgg_endpoints_lt {W : ℕ} (hW : 0 < W)
    {xs : List (ℕ × ℤ)} (hxs : ∀ p ∈ xs, p.1 < W) :
    (listIntMinAgg xs).first < W ∧ (listIntMinAgg xs).last < W := by
  induction xs with
  | nil => simp [listIntMinAgg, hW]
  | cons p xs ih =>
      rcases p with ⟨id, v⟩
      exact combineIntMinAgg_endpoints_lt hW
        ⟨hxs (id, v) (by simp), hxs (id, v) (by simp)⟩
        (ih fun q hq => hxs q (by simp [hq]))

theorem evalMemSteps_nodeId_lt {w h L : ℕ} {mem : ℕ → ℕ} {nb cap : ℕ}
    (hbase : nb + NODE_STRIDE * (cap + 1) < 2 ^ w)
    {t : AuxTree} {par pp : ℕ} (ht : TreeMemMatch w h L mem nb cap t par pp)
    (f : Bool) (δ : ℤ) :
    ∀ s ∈ evalMemSteps mem nb h L t f δ, s.nodeId < 2 ^ w := by
  revert par pp ht f δ
  induction t with
  | leaf =>
      intro _ _ _ _ _ _ hs
      simp [evalMemSteps] at hs
  | node y l r ihl ihr =>
      intro par pp ht f δ s hs
      rcases ht with ⟨_, hy2, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
      have hy_lt : y < 2 ^ w := by
        have hptr := nodePtr_lt_pow hbase hy2
        have hst : 1 ≤ NODE_STRIDE := by unfold NODE_STRIDE; omega
        have hmul : y ≤ NODE_STRIDE * y := Nat.le_mul_of_pos_left y hst
        omega
      have hown : ∀ (f' : Bool) (s' : RawStep), s' ∈ ((nodeOwnRawStep mem nb h L y).map
          (fun a => (if f' = true then a.flip else a).addDeltaMod h L δ)).toList → s'.nodeId < 2 ^ w := by
        intro f' s' hs'
        by_cases hhe : nodeField mem nb y OFF_HASE = 0
        · simp [nodeOwnRawStep, hhe] at hs'
        · simp only [nodeOwnRawStep, hhe, ↓reduceIte, Option.map_some, Option.toList_some,
            List.mem_singleton] at hs'
          have hnid : ∀ (u : RawStep), (u.addDeltaMod h L δ).nodeId = u.nodeId := fun u => by
            cases h : u.fwd <;> simp [RawStep.addDeltaMod, h]
          rw [hs', hnid]
          cases f' <;> simp [RawStep.flip, hy_lt]
      simp only [evalMemSteps] at hs
      split_ifs at hs <;> simp only [List.mem_append] at hs <;>
        rcases hs with (hs | hs) | hs
      · exact ihr hr _ _ s hs
      · exact hown true s hs
      · exact ihl hl _ _ s hs
      · exact ihl hl _ _ s hs
      · exact hown false s hs
      · exact ihr hr _ _ s hs

theorem listIntMinAgg_append_map {α : Type*} (f : α → ℕ × ℤ) (xs ys : List α) :
    listIntMinAgg ((xs ++ ys).map f) =
      combineIntMinAgg (listIntMinAgg (xs.map f)) (listIntMinAgg (ys.map f)) := by
  rw [List.map_append, listIntMinAgg_append]

private theorem wrap_add_left (h L : ℕ) (x y : ℤ) :
    wrap h L (wrap h L x + y) = wrap h L (x + y) := by
  rw [add_comm (wrap h L x) y, wrap_add_wrap, add_comm]

theorem wrap_add3 (h L : ℕ) (a b c : ℤ) :
    wrap h L (wrap h L (wrap h L a + wrap h L b) + wrap h L c) =
      wrap h L (a + b + c) := by
  rw [wrap_add_wrap, wrap_add_left, add_assoc (wrap h L a), wrap_add_left,
    add_comm a (wrap h L b + c), add_assoc (wrap h L b), wrap_add_left]
  ring_nf

theorem wrap_neg3 (h L : ℕ) (a b c : ℤ) :
    wrap h L (wrap h L (wrap h L (-a) + wrap h L (-b)) + wrap h L (-c)) =
      wrap h L (-(a + b + c)) := by
  rw [wrap_add_wrap, wrap_add_left, add_assoc (wrap h L (-a)), wrap_add_left,
    add_comm (-a) (wrap h L (-b) + -c), add_assoc (wrap h L (-b)), wrap_add_left]
  ring_nf

theorem pull_total_cost_le {L c1 hp1 c2 hp2 c3 c4 : ℕ}
    (hc1 : c1 + hp1 ≤ 78 * L + 90)
    (hc2 : c2 + hp2 ≤ 78 * L + 90)
    (hc3 : c3 ≤ 128 * L + 255)
    (hc4 : c4 ≤ 128 * L + 255) :
    (1 + (32 + (33 + (c1 + (c2 + (c3 + (c4 + (5 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
      (hp1 + hp2) ≤ K_PULL L := by
  have hk : K_PULL L = 800 * L + 800 := by simp [K_PULL]; ring
  omega

theorem treeMemMatch_rootOptCsumOk {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap parId pp : ℕ}
    (h0 : SlotZeroOk mem nodesBase) {s : AuxTree}
    (hs : TreeMemMatch w h L mem nodesBase cap s parId pp) :
    OptNumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
      (nodeField mem nodesBase s.rootId OFF_CSUM_FWD) ∧
    OptNumPtrOk mem (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) h L
      (nodeField mem nodesBase s.rootId OFF_CSUM_BWD) := by
  cases s with
  | leaf =>
      simp only [AuxTree.rootId, nodeField, Nat.mul_zero, Nat.add_zero]
      rw [h0 OFF_CSUM_FWD (by decide), h0 OFF_CSUM_BWD (by decide)]
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  | node rid rl rr =>
      rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, hcf, hcb, _, _, _, _, _, _, _, _, _⟩
      exact ⟨hcf, hcb⟩

theorem combineIntMinAgg_own_zero_eq {x : ℕ} {v : ℤ} {a : IntMinAgg}
    (ha : a.has = false → a = ⟨false, 0, 0, 0⟩) :
    combineIntMinAgg a ⟨false, v, x, x⟩ = combineIntMinAgg a ⟨false, 0, 0, 0⟩ := by
  cases h : a.has
  · simp [combineIntMinAgg, ha h]
  · simp [combineIntMinAgg, h]

/-! ### Modular block executors inside `pullBody` -/

theorem pullPtrs_exec {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem₀ : ℕ → ℕ} {nodesBase cap x lId rId : ℕ}
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    (hx2 : x ≤ cap) (hl_le : lId ≤ cap) (hr_le : rId ≤ cap)
    (hL : nodeField mem₀ nodesBase x OFF_LEFT = lId)
    (hR : nodeField mem₀ nodesBase x OFF_RIGHT = rId)
    (st₀ : State) (hmem : st₀.mem = mem₀)
    (hr0 : st₀.regs 0 = nodesBase) (hr1 : st₀.regs 1 = x) :
    ∃ st1,
      Runs w p ω
        (Stmt.assign 2 (nodePtrExpr 0 1) ;;
         Stmt.assign 3 (fieldLoadExpr 2 OFF_LEFT) ;;
         Stmt.assign 4 (nodePtrExpr 0 3) ;;
         Stmt.assign 5 (fieldLoadExpr 2 OFF_RIGHT) ;;
         Stmt.assign 6 (nodePtrExpr 0 5))
        st₀ .normal st1 32 ∧
      st1.mem = mem₀ ∧
      st1.regs 0 = nodesBase ∧
      st1.regs 1 = x ∧
      st1.regs 2 = nodesBase + NODE_STRIDE * x ∧
      st1.regs 4 = nodesBase + NODE_STRIDE * lId ∧
      st1.regs 6 = nodesBase + NODE_STRIDE * rId := by
  subst hmem
  let ptr := nodesBase + NODE_STRIDE * x
  let lPtr := nodesBase + NODE_STRIDE * lId
  let rPtr := nodesBase + NODE_STRIDE * rId
  have hstride : NODE_STRIDE < 2 ^ w := by unfold NODE_STRIDE at *; omega
  have hptr_lt : ptr < 2 ^ w := nodePtr_lt_pow hbase hx2
  have hl_lt : lPtr < 2 ^ w := nodePtr_lt_pow hbase hl_le
  have hr_lt : rPtr < 2 ^ w := nodePtr_lt_pow hbase hr_le
  have ha_L : ptr + OFF_LEFT < 2 ^ w := nodeAddr_lt_pow hbase hx2 (by decide)
  have ha_R : ptr + OFF_RIGHT < 2 ^ w := nodeAddr_lt_pow hbase hx2 (by decide)
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs 2 ptr, pos := st₀.pos }
  let st2 : State := { mem := st₀.mem, regs := Function.update st1.regs 3 lId, pos := st₀.pos }
  let st3 : State := { mem := st₀.mem, regs := Function.update st2.regs 4 lPtr, pos := st₀.pos }
  let st4 : State := { mem := st₀.mem, regs := Function.update st3.regs 5 rId, pos := st₀.pos }
  let st5 : State := { mem := st₀.mem, regs := Function.update st4.regs 6 rPtr, pos := st₀.pos }
  have h1_0 : st1.regs 0 = nodesBase := by dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr0
  have h1_2 : st1.regs 2 = ptr := by dsimp [st1]; exact Function.update_self _ _ _
  have h2_0 : st2.regs 0 = nodesBase := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact h1_0
  have h2_2 : st2.regs 2 = ptr := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact h1_2
  have h2_3 : st2.regs 3 = lId := by dsimp [st2]; exact Function.update_self _ _ _
  have h3_0 : st3.regs 0 = nodesBase := by dsimp [st3]; rw [Function.update_of_ne (by decide)]; exact h2_0
  have h3_2 : st3.regs 2 = ptr := by dsimp [st3]; rw [Function.update_of_ne (by decide)]; exact h2_2
  have h4_0 : st4.regs 0 = nodesBase := by dsimp [st4]; rw [Function.update_of_ne (by decide)]; exact h3_0
  have h4_5 : st4.regs 5 = rId := by dsimp [st4]; exact Function.update_self _ _ _
  have hrun : Runs w p ω
      (Stmt.assign 2 (nodePtrExpr 0 1) ;;
       Stmt.assign 3 (fieldLoadExpr 2 OFF_LEFT) ;;
       Stmt.assign 4 (nodePtrExpr 0 3) ;;
       Stmt.assign 5 (fieldLoadExpr 2 OFF_RIGHT) ;;
       Stmt.assign 6 (nodePtrExpr 0 5))
      st₀ .normal st5 32 :=
    runs_seq_iff.mpr (Or.inr ⟨st1, 6, 25,
      runs_assign_iff.mpr ⟨ptr, eval_nodePtrExpr hstride hr0 hr1 hptr_lt, rfl, rfl, rfl⟩,
      runs_seq_iff.mpr (Or.inr ⟨st2, 5, 19,
        runs_assign_iff.mpr ⟨lId, (eval_fieldLoadExpr h1_2 ha_L).trans (congrArg some (by simpa [ptr, nodeField] using hL)), rfl, rfl, rfl⟩,
        runs_seq_iff.mpr (Or.inr ⟨st3, 6, 12,
          runs_assign_iff.mpr ⟨lPtr, eval_nodePtrExpr hstride h2_0 h2_3 hl_lt, rfl, rfl, rfl⟩,
          runs_seq_iff.mpr (Or.inr ⟨st4, 5, 6,
            runs_assign_iff.mpr ⟨rId, (eval_fieldLoadExpr h3_2 ha_R).trans (congrArg some (by simpa [ptr, nodeField] using hR)), rfl, rfl, rfl⟩,
            runs_assign_iff.mpr ⟨rPtr, eval_nodePtrExpr hstride h4_0 h4_5 hr_lt, rfl, rfl, rfl⟩,
            rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  refine ⟨st5, hrun, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [st5]; rw [Function.update_of_ne (by decide)]; exact h4_0
  · dsimp [st5, st4, st3, st2, st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact hr1
  · dsimp [st5, st4, st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact h2_2
  · dsimp [st5, st4, st3]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact Function.update_self _ _ _
  · dsimp [st5]; exact Function.update_self _ _ _

theorem pullVcntHdr_exec {w L hp₀ newVcnt x : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem₀ : ℕ → ℕ} {nodesBase ptr lPtr rPtr : ℕ}
    (hnb : 3 ≤ nodesBase)
    (hnb_ptr : nodesBase ≤ ptr)
    (hL_hdr : mem₀ (nodesBase - 3) = L)
    (hhp_hdr : mem₀ (nodesBase - 1) = hp₀)
    (_hL_lt : L < 2 ^ w) (_hhp_lt : hp₀ < 2 ^ w)
    (hal_l_vc : lPtr + OFF_VCNT < 2 ^ w)
    (hal_x_isv : ptr + OFF_ISV < 2 ^ w)
    (hal_r_vc : rPtr + OFF_VCNT < 2 ^ w)
    (hal_x_vc : ptr + OFF_VCNT < 2 ^ w)
    (hvc1_lt : mem₀ (lPtr + OFF_VCNT) + mem₀ (ptr + OFF_ISV) < 2 ^ w)
    (hvc_eq : mem₀ (lPtr + OFF_VCNT) + mem₀ (ptr + OFF_ISV) + mem₀ (rPtr + OFF_VCNT) = newVcnt)
    (hvc2_lt : newVcnt < 2 ^ w)
    (st1 : State) (hmem1 : st1.mem = mem₀)
    (hr0 : st1.regs 0 = nodesBase) (hr1 : st1.regs 1 = x)
    (hr2 : st1.regs 2 = ptr) (hr4 : st1.regs 4 = lPtr) (hr6 : st1.regs 6 = rPtr) :
    ∃ st2,
      Runs w p ω
        (Stmt.assign 7 (.bin .add
           (.bin .add (fieldLoadExpr 4 OFF_VCNT) (fieldLoadExpr 2 OFF_ISV))
           (fieldLoadExpr 6 OFF_VCNT)) ;;
         Stmt.store (fieldAddrExpr 2 OFF_VCNT) (.reg 7) ;;
         Stmt.assign 15 (.load (.bin .sub (.reg 0) (.const 3))) ;;
         Stmt.assign 16 (.load (.bin .sub (.reg 0) (.const 1))))
        st1 .normal st2 33 ∧
      st2.mem = Function.update mem₀ (ptr + OFF_VCNT) newVcnt ∧
      st2.regs 0 = nodesBase ∧
      st2.regs 1 = x ∧
      st2.regs 2 = ptr ∧
      st2.regs 4 = lPtr ∧
      st2.regs 6 = rPtr ∧
      st2.regs 15 = L ∧
      st2.regs 16 = hp₀ := by
  subst hmem1
  have hw3 : (3 : ℕ) < 2 ^ w := by omega
  have hw1 : (1 : ℕ) < 2 ^ w := by omega
  have ha1 := eval_fieldLoadExpr hr4 hal_l_vc
  have ha2 := eval_fieldLoadExpr hr2 hal_x_isv
  have ha3 := eval_fieldLoadExpr hr6 hal_r_vc
  have hsum := Expr.eval_add (Expr.eval_add ha1 ha2 hvc1_lt) ha3 (by rw [hvc_eq]; exact hvc2_lt)
  rw [hvc_eq] at hsum
  let st_a : State := { mem := st1.mem, regs := Function.update st1.regs 7 newVcnt, pos := st1.pos }
  let mem_b := Function.update st1.mem (ptr + OFF_VCNT) newVcnt
  let st_b : State := { mem := mem_b, regs := st_a.regs, pos := st1.pos }
  let st_c : State := { mem := mem_b, regs := Function.update st_b.regs 15 L, pos := st1.pos }
  let st_d : State := { mem := mem_b, regs := Function.update st_c.regs 16 hp₀, pos := st1.pos }
  have ha_0 : st_a.regs 0 = nodesBase := by dsimp [st_a]; rw [Function.update_of_ne (by decide)]; exact hr0
  have ha_2 : st_a.regs 2 = ptr := by dsimp [st_a]; rw [Function.update_of_ne (by decide)]; exact hr2
  have ha_7 : st_a.regs 7 = newVcnt := by dsimp [st_a]; exact Function.update_self _ _ _
  have haddr_vc : (fieldAddrExpr 2 OFF_VCNT).eval w st_a = some (ptr + OFF_VCNT) :=
    eval_fieldAddrExpr ha_2 hal_x_vc
  have hne3 : nodesBase - 3 ≠ ptr + OFF_VCNT := by omega
  have hne1 : nodesBase - 1 ≠ ptr + OFF_VCNT := by omega
  have hb_0 : st_b.regs 0 = nodesBase := ha_0
  have hc_0 : st_c.regs 0 = nodesBase := by dsimp [st_c, st_b]; rw [Function.update_of_ne (by decide)]; exact ha_0
  have hev_L : (Expr.load (.bin .sub (.reg 0) (.const 3))).eval w st_b = some L := by
    have hsub := Expr.eval_sub (Expr.eval_reg_of_eq hb_0) (Expr.eval_const hw3) (by omega)
    have hld := Expr.eval_load hsub
    simpa [st_b, mem_b, Function.update_of_ne hne3, hL_hdr] using hld
  have hev_hp : (Expr.load (.bin .sub (.reg 0) (.const 1))).eval w st_c = some hp₀ := by
    have hsub := Expr.eval_sub (Expr.eval_reg_of_eq hc_0) (Expr.eval_const hw1) (by omega)
    have hld := Expr.eval_load hsub
    simpa [st_c, mem_b, Function.update_of_ne hne1, hhp_hdr] using hld
  have hrun : Runs w p ω
      (Stmt.assign 7 (.bin .add
         (.bin .add (fieldLoadExpr 4 OFF_VCNT) (fieldLoadExpr 2 OFF_ISV))
         (fieldLoadExpr 6 OFF_VCNT)) ;;
       Stmt.store (fieldAddrExpr 2 OFF_VCNT) (.reg 7) ;;
       Stmt.assign 15 (.load (.bin .sub (.reg 0) (.const 3))) ;;
       Stmt.assign 16 (.load (.bin .sub (.reg 0) (.const 1))))
      st1 .normal st_d 33 :=
    runs_seq_iff.mpr (Or.inr ⟨st_a, 15, 17,
      runs_assign_iff.mpr ⟨newVcnt, hsum, rfl, rfl, rfl⟩,
      runs_seq_iff.mpr (Or.inr ⟨st_b, 5, 11,
        runs_store_iff.mpr ⟨ptr + OFF_VCNT, newVcnt, haddr_vc, Expr.eval_reg_of_eq ha_7, rfl, rfl, rfl⟩,
        runs_seq_iff.mpr (Or.inr ⟨st_c, 5, 5,
          runs_assign_iff.mpr ⟨L, hev_L, rfl, rfl, rfl⟩,
          runs_assign_iff.mpr ⟨hp₀, hev_hp, rfl, rfl, rfl⟩, rfl⟩), rfl⟩), rfl⟩)
  refine ⟨st_d, hrun, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [st_d]; rw [Function.update_of_ne (by decide)]; exact hc_0
  · dsimp [st_d, st_c, st_b, st_a]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact hr1
  · dsimp [st_d, st_c, st_b]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact ha_2
  · dsimp [st_d, st_c, st_b, st_a]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact hr4
  · dsimp [st_d, st_c, st_b, st_a]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact hr6
  · dsimp [st_d, st_c]; rw [Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  · dsimp [st_d]; exact Function.update_self _ _ _

theorem pullCsumPair_exec {w h L arenaHi hp nodesBase x ptr lPtr rPtr fCsum fCost : ℕ}
    {sp : SplayProcs} {p : Program} {ω : ℕ → Bool}
    (hp_ok : SplayProgramOk w h p sp)
    (harena_pos : 1 ≤ arenaHi) (harena_hp : arenaHi ≤ hp)
    (hhp_lt : hp + 2 * L < 2 ^ w)
    (hfCsum : fCsum < NODE_STRIDE) (hfCost : fCost < NODE_STRIDE)
    (hl_arena : lPtr + NODE_STRIDE ≤ arenaHi)
    (hx_arena : ptr + NODE_STRIDE ≤ arenaHi)
    (hr_arena : rPtr + NODE_STRIDE ≤ arenaHi)
    (st₀ : State)
    (hz : ZeroFrom st₀.mem hp)
    (hr0 : st₀.regs 0 = nodesBase) (hr1 : st₀.regs 1 = x)
    (hr2 : st₀.regs 2 = ptr) (hr4 : st₀.regs 4 = lPtr) (hr6 : st₀.regs 6 = rPtr)
    (hr15 : st₀.regs 15 = L) (hr16 : st₀.regs 16 = hp)
    (hl_ok : OptNumPtrOk st₀.mem arenaHi hp h L (st₀.mem (lPtr + fCsum)))
    (hx_ok : OptNumPtrOk st₀.mem arenaHi hp h L (st₀.mem (ptr + fCost)))
    (hr_ok : OptNumPtrOk st₀.mem arenaHi hp h L (st₀.mem (rPtr + fCsum))) :
    ∃ st' c hp',
      Runs w p ω
        (Stmt.assign 7 (fieldLoadExpr 4 fCsum) ;;
         Stmt.assign 8 (fieldLoadExpr 2 fCost) ;;
         addOptPtrStmt sp 7 8 15 16 18 ;;
         Stmt.assign 7 (fieldLoadExpr 6 fCsum) ;;
         addOptPtrStmt sp 18 7 15 16 8 ;;
         Stmt.store (fieldAddrExpr 2 fCsum) (.reg 8))
        st₀ .normal st' c ∧
      st'.regs 0 = nodesBase ∧ st'.regs 1 = x ∧ st'.regs 2 = ptr ∧
      st'.regs 4 = lPtr ∧ st'.regs 6 = rPtr ∧ st'.regs 15 = L ∧ st'.regs 16 = hp' ∧
      hp ≤ hp' ∧ hp' ≤ hp + 2 * L ∧
      c + (hp' - hp) ≤ 78 * L + 90 ∧
      (∀ a < hp, a ≠ ptr + fCsum → st'.mem a = st₀.mem a) ∧
      ZeroFrom st'.mem hp' ∧
      OptNumPtrOk st'.mem arenaHi hp' h L (st'.mem (ptr + fCsum)) ∧
      optIntVal st'.mem h L (st'.mem (ptr + fCsum)) =
        wrap h L
          (wrap h L
            (optIntVal st₀.mem h L (st₀.mem (lPtr + fCsum)) +
             optIntVal st₀.mem h L (st₀.mem (ptr + fCost))) +
           optIntVal st₀.mem h L (st₀.mem (rPtr + fCsum))) := by
  have hx_addr_lt : ptr + fCsum < 2 ^ w := by omega
  have hcost_addr_lt : ptr + fCost < 2 ^ w := by omega
  have hl_addr_lt : lPtr + fCsum < 2 ^ w := by omega
  have hr_addr_lt : rPtr + fCsum < 2 ^ w := by omega
  let pL := st₀.mem (lPtr + fCsum)
  let pX := st₀.mem (ptr + fCost)
  let pR := st₀.mem (rPtr + fCsum)
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs 7 pL, pos := st₀.pos }
  let st2 : State := { mem := st₀.mem, regs := Function.update st1.regs 8 pX, pos := st₀.pos }
  have h12 : Runs w p ω (Stmt.assign 7 (fieldLoadExpr 4 fCsum) ;; Stmt.assign 8 (fieldLoadExpr 2 fCost))
      st₀ .normal st2 11 := by
    have hr1_2 : st1.regs 2 = ptr := by dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr2
    exact runs_seq_iff.mpr (Or.inr ⟨st1, 5, 5,
      runs_assign_iff.mpr ⟨pL, by simpa [pL] using eval_fieldLoadExpr hr4 hl_addr_lt, rfl, rfl, rfl⟩,
      runs_assign_iff.mpr ⟨pX, by simpa [st1, pX] using eval_fieldLoadExpr hr1_2 hcost_addr_lt, rfl, rfl, rfl⟩, rfl⟩)
  have h2_7 : st2.regs 7 = pL := by
    dsimp [st2, st1]; rw [Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  have h2_8 : st2.regs 8 = pX := by dsimp [st2]; exact Function.update_self _ _ _
  have h2_15 : st2.regs 15 = L := by
    dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr15
  have h2_16 : st2.regs 16 = hp := by
    dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr16
  rcases addOptPtrStmt_runs hp_ok (by decide : [7, 8, 15, 16, 18].Nodup) st2
      h2_7 h2_8 h2_15 h2_16 harena_pos harena_hp hl_ok hx_ok hz (by omega) ω with
    ⟨st3, ca1, hp1, out1, hra1, hr3_16, hr3_18, hr3_other, hle1, hhi1, hc1, hpres1, hz1, hout1_ok, hout1_val⟩
  have h3_0 : st3.regs 0 = nodesBase :=
    (hr3_other 0 (by decide) (by decide)).trans (by dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr0)
  have h3_1 : st3.regs 1 = x :=
    (hr3_other 1 (by decide) (by decide)).trans (by dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr1)
  have h3_2 : st3.regs 2 = ptr :=
    (hr3_other 2 (by decide) (by decide)).trans (by dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr2)
  have h3_4 : st3.regs 4 = lPtr :=
    (hr3_other 4 (by decide) (by decide)).trans (by dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr4)
  have h3_6 : st3.regs 6 = rPtr :=
    (hr3_other 6 (by decide) (by decide)).trans (by dsimp [st2, st1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr6)
  have h3_15 : st3.regs 15 = L := (hr3_other 15 (by decide) (by decide)).trans h2_15
  have hm3_pR : st3.mem (rPtr + fCsum) = pR := hpres1 (rPtr + fCsum) (by omega)
  let st4 : State := { mem := st3.mem, regs := Function.update st3.regs 7 pR, pos := st3.pos }
  have ha_pR : Runs w p ω (Stmt.assign 7 (fieldLoadExpr 6 fCsum)) st3 .normal st4 5 :=
    runs_assign_iff.mpr ⟨pR, by simpa [hm3_pR] using eval_fieldLoadExpr h3_6 hr_addr_lt, rfl, rfl, rfl⟩
  have h4_18 : st4.regs 18 = out1 := by dsimp [st4]; rw [Function.update_of_ne (by decide)]; exact hr3_18
  have h4_7 : st4.regs 7 = pR := by dsimp [st4]; exact Function.update_self _ _ _
  have h4_15 : st4.regs 15 = L := by dsimp [st4]; rw [Function.update_of_ne (by decide)]; exact h3_15
  have h4_16 : st4.regs 16 = hp1 := by dsimp [st4]; rw [Function.update_of_ne (by decide)]; exact hr3_16
  have hr_ok4 : OptNumPtrOk st4.mem arenaHi hp1 h L pR :=
    optNumPtrOk_congr hle1 (fun a _ ha => hpres1 a ha) hr_ok
  rcases addOptPtrStmt_runs hp_ok (by decide : [18, 7, 15, 16, 8].Nodup) st4
      h4_18 h4_7 h4_15 h4_16 harena_pos (le_trans harena_hp hle1) hout1_ok hr_ok4 hz1 (by omega) ω with
    ⟨st5, ca2, hp2, out2, hra2, hr5_16, hr5_8, hr5_other, hle2, hhi2, hc2, hpres2, hz2, hout2_ok, hout2_val⟩
  have h5_2 : st5.regs 2 = ptr :=
    (hr5_other 2 (by decide) (by decide)).trans (by dsimp [st4]; rw [Function.update_of_ne (by decide)]; exact h3_2)
  let mem' := Function.update st5.mem (ptr + fCsum) out2
  let st' : State := { mem := mem', regs := st5.regs, pos := st5.pos }
  have hstore : Runs w p ω (Stmt.store (fieldAddrExpr 2 fCsum) (.reg 8)) st5 .normal st' 5 :=
    runs_store_iff.mpr ⟨ptr + fCsum, out2, eval_fieldAddrExpr h5_2 hx_addr_lt,
      Expr.eval_reg_of_eq hr5_8, rfl, rfl, rfl⟩
  have htail : Runs w p ω
      (Stmt.assign 7 (fieldLoadExpr 6 fCsum) ;; addOptPtrStmt sp 18 7 15 16 8 ;; Stmt.store (fieldAddrExpr 2 fCsum) (.reg 8))
      st3 .normal st' (5 + (ca2 + 5 + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st4, 5, ca2 + 5 + 1, ha_pR,
      runs_seq_iff.mpr (Or.inr ⟨st5, ca2, 5, hra2, hstore, rfl⟩), rfl⟩)
  have hfull : Runs w p ω
      (Stmt.assign 7 (fieldLoadExpr 4 fCsum) ;; Stmt.assign 8 (fieldLoadExpr 2 fCost) ;;
       addOptPtrStmt sp 7 8 15 16 18 ;;
       Stmt.assign 7 (fieldLoadExpr 6 fCsum) ;; addOptPtrStmt sp 18 7 15 16 8 ;;
       Stmt.store (fieldAddrExpr 2 fCsum) (.reg 8))
      st₀ .normal st' (11 + (ca1 + (5 + (ca2 + 5 + 1) + 1) + 1) + 1) :=
    runs_seq2_normal h12 (runs_seq_iff.mpr (Or.inr ⟨st3, ca1, 5 + (ca2 + 5 + 1) + 1, hra1, htail, rfl⟩))
  have hag5' : ∀ a, arenaHi ≤ a → a < hp2 → st'.mem a = st5.mem a := fun a ha _ =>
    Function.update_of_ne (by omega) _ _
  have hr_eq : ∀ r, r ≠ 16 → r ≠ 8 → r ≠ 7 → r ≠ 18 → st'.regs r = st₀.regs r := fun r h16 h8 h7 h18 => by
    dsimp [st']
    rw [hr5_other r h16 h8, show st4.regs r = st3.regs r by dsimp [st4]; rw [Function.update_of_ne h7],
      hr3_other r h16 h18]
    dsimp [st2, st1]
    rw [Function.update_of_ne h8, Function.update_of_ne h7]
  refine ⟨st', _, hp2, hfull,
    (hr_eq 0 (by decide) (by decide) (by decide) (by decide)).trans hr0,
    (hr_eq 1 (by decide) (by decide) (by decide) (by decide)).trans hr1,
    (hr_eq 2 (by decide) (by decide) (by decide) (by decide)).trans hr2,
    (hr_eq 4 (by decide) (by decide) (by decide) (by decide)).trans hr4,
    (hr_eq 6 (by decide) (by decide) (by decide) (by decide)).trans hr6,
    (hr_eq 15 (by decide) (by decide) (by decide) (by decide)).trans hr15,
    hr5_16, le_trans hle1 hle2, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro a ha hne
    dsimp [st', mem']
    rw [Function.update_of_ne hne, hpres2 a (lt_of_lt_of_le ha hle1), hpres1 a ha]
  · intro a ha
    dsimp [st', mem']
    rw [Function.update_of_ne (by omega)]
    exact hz2 a ha
  · have hm : st'.mem (ptr + fCsum) = out2 := Function.update_self _ _ _
    rw [hm]
    exact optNumPtrOk_congr le_rfl (fun a ha1 ha2 => hag5' a ha1 ha2) hout2_ok
  · have hm : st'.mem (ptr + fCsum) = out2 := Function.update_self _ _ _
    rw [hm, optIntVal_agree_heap (fun a ha1 ha2 => hag5' a ha1 ha2) hout2_ok, hout2_val]
    have hpR_eq : optIntVal st4.mem h L pR = optIntVal st₀.mem h L pR :=
      optIntVal_agree_heap (fun a _ ha => hpres1 a ha) hr_ok
    have hout1_eq : optIntVal st4.mem h L out1 = optIntVal st3.mem h L out1 := rfl
    rw [hpR_eq, hout1_eq, hout1_val]

/-! ### `pullMinNumStmt` execution helper -/

theorem pullMinLoadLeft_exec {w x ptr lPtr fSelfVal fMinHas fMinVal fMinFirst fMinLast : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hx_lt : ∀ off < NODE_STRIDE, ptr + off < 2 ^ w)
    (hl_lt : ∀ off < NODE_STRIDE, lPtr + off < 2 ^ w)
    (hfH : fMinHas < NODE_STRIDE) (hfV : fMinVal < NODE_STRIDE)
    (hfF : fMinFirst < NODE_STRIDE) (hfL : fMinLast < NODE_STRIDE)
    (hfS : fSelfVal < NODE_STRIDE)
    (st₀ : State)
    (hr1 : st₀.regs 1 = x) (hr2 : st₀.regs 2 = ptr) (hr4 : st₀.regs 4 = lPtr) :
    ∃ st1,
      Runs w p ω
        (Stmt.assign 7 (fieldLoadExpr 4 fMinHas) ;;
         Stmt.assign 8 (fieldLoadExpr 4 fMinVal) ;;
         Stmt.assign 9 (fieldLoadExpr 4 fMinFirst) ;;
         Stmt.assign 10 (fieldLoadExpr 4 fMinLast) ;;
         Stmt.assign 11 (fieldLoadExpr 2 OFF_HASE) ;;
         Stmt.assign 12 (fieldLoadExpr 2 fSelfVal) ;;
         Stmt.assign 13 (.reg 1) ;;
         Stmt.assign 14 (.reg 1))
        st₀ .normal st1 41 ∧
      st1.mem = st₀.mem ∧
      (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 →
        st1.regs r = st₀.regs r) ∧
      st1.regs 7 = st₀.mem (lPtr + fMinHas) ∧
      st1.regs 8 = st₀.mem (lPtr + fMinVal) ∧
      st1.regs 9 = st₀.mem (lPtr + fMinFirst) ∧
      st1.regs 10 = st₀.mem (lPtr + fMinLast) ∧
      st1.regs 11 = st₀.mem (ptr + OFF_HASE) ∧
      st1.regs 12 = st₀.mem (ptr + fSelfVal) ∧
      st1.regs 13 = x ∧
      st1.regs 14 = x := by
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs 7 (st₀.mem (lPtr + fMinHas)), pos := st₀.pos }
  let st2 : State := { mem := st₀.mem, regs := Function.update st1.regs 8 (st₀.mem (lPtr + fMinVal)), pos := st₀.pos }
  let st3 : State := { mem := st₀.mem, regs := Function.update st2.regs 9 (st₀.mem (lPtr + fMinFirst)), pos := st₀.pos }
  let st4 : State := { mem := st₀.mem, regs := Function.update st3.regs 10 (st₀.mem (lPtr + fMinLast)), pos := st₀.pos }
  let st5 : State := { mem := st₀.mem, regs := Function.update st4.regs 11 (st₀.mem (ptr + OFF_HASE)), pos := st₀.pos }
  let st6 : State := { mem := st₀.mem, regs := Function.update st5.regs 12 (st₀.mem (ptr + fSelfVal)), pos := st₀.pos }
  let st7 : State := { mem := st₀.mem, regs := Function.update st6.regs 13 x, pos := st₀.pos }
  let st8 : State := { mem := st₀.mem, regs := Function.update st7.regs 14 x, pos := st₀.pos }
  have hr4_1 : st1.regs 4 = lPtr := by dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr4
  have hr4_2 : st2.regs 4 = lPtr := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr4_1
  have hr4_3 : st3.regs 4 = lPtr := by dsimp [st3]; rw [Function.update_of_ne (by decide)]; exact hr4_2
  have hr2_4 : st4.regs 2 = ptr := by
    dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr2
  have hr2_5 : st5.regs 2 = ptr := by dsimp [st5]; rw [Function.update_of_ne (by decide)]; exact hr2_4
  have hr1_6 : st6.regs 1 = x := by
    dsimp [st6, st5, st4, st3, st2, st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr1
  have hr1_7 : st7.regs 1 = x := by dsimp [st7]; rw [Function.update_of_ne (by decide)]; exact hr1_6
  have h5 : Runs w p ω
      (Stmt.assign 7 (fieldLoadExpr 4 fMinHas) ;;
       Stmt.assign 8 (fieldLoadExpr 4 fMinVal) ;;
       Stmt.assign 9 (fieldLoadExpr 4 fMinFirst) ;;
       Stmt.assign 10 (fieldLoadExpr 4 fMinLast) ;;
       Stmt.assign 11 (fieldLoadExpr 2 OFF_HASE))
      st₀ .normal st5 29 :=
    runs_seq_iff.mpr (Or.inr ⟨st1, 5, 23,
      runs_assign_iff.mpr ⟨_, eval_fieldLoadExpr hr4 (hl_lt _ hfH), rfl, rfl, rfl⟩,
      runs_seq_iff.mpr (Or.inr ⟨st2, 5, 17,
        runs_assign_iff.mpr ⟨_, by simpa [st1] using eval_fieldLoadExpr hr4_1 (hl_lt _ hfV), rfl, rfl, rfl⟩,
        runs_seq_iff.mpr (Or.inr ⟨st3, 5, 11,
          runs_assign_iff.mpr ⟨_, by simpa [st2, st1] using eval_fieldLoadExpr hr4_2 (hl_lt _ hfF), rfl, rfl, rfl⟩,
          runs_seq_iff.mpr (Or.inr ⟨st4, 5, 5,
            runs_assign_iff.mpr ⟨_, by simpa [st3, st2, st1] using eval_fieldLoadExpr hr4_3 (hl_lt _ hfL), rfl, rfl, rfl⟩,
            runs_assign_iff.mpr ⟨_, by simpa [st4, st3, st2, st1] using eval_fieldLoadExpr hr2_4 (hx_lt OFF_HASE (by decide)), rfl, rfl, rfl⟩, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have h3 : Runs w p ω
      (Stmt.assign 12 (fieldLoadExpr 2 fSelfVal) ;;
       Stmt.assign 13 (.reg 1) ;;
       Stmt.assign 14 (.reg 1))
      st5 .normal st8 11 :=
    runs_seq_iff.mpr (Or.inr ⟨st6, 5, 5,
      runs_assign_iff.mpr ⟨_, by simpa [st5, st4, st3, st2, st1] using eval_fieldLoadExpr hr2_5 (hx_lt _ hfS), rfl, rfl, rfl⟩,
      runs_seq_iff.mpr (Or.inr ⟨st7, 2, 2,
        runs_assign_iff.mpr ⟨x, Expr.eval_reg_of_eq hr1_6, rfl, rfl, rfl⟩,
        runs_assign_iff.mpr ⟨x, Expr.eval_reg_of_eq hr1_7, rfl, rfl, rfl⟩, rfl⟩), rfl⟩)
  refine ⟨st8, runs_seq5_normal h5 h3, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h7 h8 h9 h10 h11 h12 h13 h14
    dsimp [st8, st7, st6, st5, st4, st3, st2, st1]
    rw [Function.update_of_ne h14, Function.update_of_ne h13, Function.update_of_ne h12,
      Function.update_of_ne h11, Function.update_of_ne h10, Function.update_of_ne h9,
      Function.update_of_ne h8, Function.update_of_ne h7]
  · dsimp [st8, st7, st6, st5, st4, st3, st2, st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  · dsimp [st8, st7, st6, st5, st4, st3, st2]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  · dsimp [st8, st7, st6, st5, st4, st3]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  · dsimp [st8, st7, st6, st5, st4]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  · dsimp [st8, st7, st6, st5]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  · dsimp [st8, st7, st6]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  · dsimp [st8, st7]; rw [Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  · dsimp [st8]; exact Function.update_self _ _ _

theorem pullMinLoadRight_exec {w rPtr fMinHas fMinVal fMinFirst fMinLast : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hr_lt : ∀ off < NODE_STRIDE, rPtr + off < 2 ^ w)
    (hfH : fMinHas < NODE_STRIDE) (hfV : fMinVal < NODE_STRIDE)
    (hfF : fMinFirst < NODE_STRIDE) (hfL : fMinLast < NODE_STRIDE)
    (st₀ : State) (hr6 : st₀.regs 6 = rPtr) :
    ∃ st1,
      Runs w p ω
        (Stmt.assign 11 (fieldLoadExpr 6 fMinHas) ;;
         Stmt.assign 12 (fieldLoadExpr 6 fMinVal) ;;
         Stmt.assign 13 (fieldLoadExpr 6 fMinFirst) ;;
         Stmt.assign 14 (fieldLoadExpr 6 fMinLast))
        st₀ .normal st1 23 ∧
      st1.mem = st₀.mem ∧
      (∀ r, r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → st1.regs r = st₀.regs r) ∧
      st1.regs 11 = st₀.mem (rPtr + fMinHas) ∧
      st1.regs 12 = st₀.mem (rPtr + fMinVal) ∧
      st1.regs 13 = st₀.mem (rPtr + fMinFirst) ∧
      st1.regs 14 = st₀.mem (rPtr + fMinLast) := by
  let st1 : State := { mem := st₀.mem, regs := Function.update st₀.regs 11 (st₀.mem (rPtr + fMinHas)), pos := st₀.pos }
  let st2 : State := { mem := st₀.mem, regs := Function.update st1.regs 12 (st₀.mem (rPtr + fMinVal)), pos := st₀.pos }
  let st3 : State := { mem := st₀.mem, regs := Function.update st2.regs 13 (st₀.mem (rPtr + fMinFirst)), pos := st₀.pos }
  let st4 : State := { mem := st₀.mem, regs := Function.update st3.regs 14 (st₀.mem (rPtr + fMinLast)), pos := st₀.pos }
  have hr6_1 : st1.regs 6 = rPtr := by dsimp [st1]; rw [Function.update_of_ne (by decide)]; exact hr6
  have hr6_2 : st2.regs 6 = rPtr := by dsimp [st2]; rw [Function.update_of_ne (by decide)]; exact hr6_1
  have hr6_3 : st3.regs 6 = rPtr := by dsimp [st3]; rw [Function.update_of_ne (by decide)]; exact hr6_2
  have hrun : Runs w p ω
      (Stmt.assign 11 (fieldLoadExpr 6 fMinHas) ;;
       Stmt.assign 12 (fieldLoadExpr 6 fMinVal) ;;
       Stmt.assign 13 (fieldLoadExpr 6 fMinFirst) ;;
       Stmt.assign 14 (fieldLoadExpr 6 fMinLast))
      st₀ .normal st4 23 :=
    runs_seq_iff.mpr (Or.inr ⟨st1, 5, 17,
      runs_assign_iff.mpr ⟨_, eval_fieldLoadExpr hr6 (hr_lt _ hfH), rfl, rfl, rfl⟩,
      runs_seq_iff.mpr (Or.inr ⟨st2, 5, 11,
        runs_assign_iff.mpr ⟨_, by simpa [st1] using eval_fieldLoadExpr hr6_1 (hr_lt _ hfV), rfl, rfl, rfl⟩,
        runs_seq_iff.mpr (Or.inr ⟨st3, 5, 5,
          runs_assign_iff.mpr ⟨_, by simpa [st2, st1] using eval_fieldLoadExpr hr6_2 (hr_lt _ hfF), rfl, rfl, rfl⟩,
          runs_assign_iff.mpr ⟨_, by simpa [st3, st2, st1] using eval_fieldLoadExpr hr6_3 (hr_lt _ hfL), rfl, rfl, rfl⟩, rfl⟩), rfl⟩), rfl⟩)
  refine ⟨st4, hrun, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h11 h12 h13 h14
    dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne h14, Function.update_of_ne h13, Function.update_of_ne h12, Function.update_of_ne h11]
  · dsimp [st4, st3, st2, st1]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  · dsimp [st4, st3, st2]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  · dsimp [st4, st3]; rw [Function.update_of_ne (by decide)]; exact Function.update_self _ _ _
  · dsimp [st4]; exact Function.update_self _ _ _

theorem pullMinStore_exec {w ptr fMinHas fMinVal fMinFirst fMinLast : ℕ}
    {p : Program} {ω : ℕ → Bool}
    (hx_lt : ∀ off < NODE_STRIDE, ptr + off < 2 ^ w)
    (hfH : fMinHas < NODE_STRIDE) (hfV : fMinVal < NODE_STRIDE)
    (hfF : fMinFirst < NODE_STRIDE) (hfL : fMinLast < NODE_STRIDE)
    (hnd : [fMinHas, fMinVal, fMinFirst, fMinLast].Nodup)
    (st₀ : State) (hr2 : st₀.regs 2 = ptr) :
    ∃ st1,
      Runs w p ω
        (Stmt.store (fieldAddrExpr 2 fMinHas) (.reg 7) ;;
         Stmt.store (fieldAddrExpr 2 fMinVal) (.reg 8) ;;
         Stmt.store (fieldAddrExpr 2 fMinFirst) (.reg 9) ;;
         Stmt.store (fieldAddrExpr 2 fMinLast) (.reg 10))
        st₀ .normal st1 23 ∧
      st1.regs = st₀.regs ∧
      (∀ a, a ≠ ptr + fMinHas → a ≠ ptr + fMinVal → a ≠ ptr + fMinFirst → a ≠ ptr + fMinLast →
        st1.mem a = st₀.mem a) ∧
      st1.mem (ptr + fMinHas) = st₀.regs 7 ∧
      st1.mem (ptr + fMinVal) = st₀.regs 8 ∧
      st1.mem (ptr + fMinFirst) = st₀.regs 9 ∧
      st1.mem (ptr + fMinLast) = st₀.regs 10 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  rcases hnd with ⟨⟨hHV, hHF, hHL⟩, ⟨hVF, hVL⟩, hFL, _⟩
  let mem1 := Function.update st₀.mem (ptr + fMinHas) (st₀.regs 7)
  let mem2 := Function.update mem1 (ptr + fMinVal) (st₀.regs 8)
  let mem3 := Function.update mem2 (ptr + fMinFirst) (st₀.regs 9)
  let mem4 := Function.update mem3 (ptr + fMinLast) (st₀.regs 10)
  let st1 : State := { st₀ with mem := mem1 }
  let st2 : State := { st₀ with mem := mem2 }
  let st3 : State := { st₀ with mem := mem3 }
  let st4 : State := { st₀ with mem := mem4 }
  have hrun : Runs w p ω
      (Stmt.store (fieldAddrExpr 2 fMinHas) (.reg 7) ;;
       Stmt.store (fieldAddrExpr 2 fMinVal) (.reg 8) ;;
       Stmt.store (fieldAddrExpr 2 fMinFirst) (.reg 9) ;;
       Stmt.store (fieldAddrExpr 2 fMinLast) (.reg 10))
      st₀ .normal st4 23 :=
    runs_seq_iff.mpr (Or.inr ⟨st1, 5, 17,
      runs_store_iff.mpr ⟨ptr + fMinHas, st₀.regs 7, eval_fieldAddrExpr hr2 (hx_lt _ hfH),
        Expr.eval_reg w 7 st₀, rfl, rfl, rfl⟩,
      runs_seq_iff.mpr (Or.inr ⟨st2, 5, 11,
        runs_store_iff.mpr ⟨ptr + fMinVal, st₀.regs 8,
          eval_fieldAddrExpr (by simpa [st1] using hr2) (hx_lt _ hfV),
          Expr.eval_reg w 8 st1, rfl, rfl, rfl⟩,
        runs_seq_iff.mpr (Or.inr ⟨st3, 5, 5,
          runs_store_iff.mpr ⟨ptr + fMinFirst, st₀.regs 9,
            eval_fieldAddrExpr (by simpa [st2, st1] using hr2) (hx_lt _ hfF),
            Expr.eval_reg w 9 st2, rfl, rfl, rfl⟩,
          runs_store_iff.mpr ⟨ptr + fMinLast, st₀.regs 10,
            eval_fieldAddrExpr (by simpa [st3, st2, st1] using hr2) (hx_lt _ hfL),
            Expr.eval_reg w 10 st3, rfl, rfl, rfl⟩, rfl⟩), rfl⟩), rfl⟩)
  refine ⟨st4, hrun, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro a hH hV hF hL
    dsimp [st4, mem4, mem3, mem2, mem1]
    rw [Function.update_of_ne hL, Function.update_of_ne hF,
      Function.update_of_ne hV, Function.update_of_ne hH]
  · dsimp [st4, mem4, mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
  · dsimp [st4, mem4, mem3, mem2]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
  · dsimp [st4, mem4, mem3]
    rw [Function.update_of_ne (by omega)]; exact Function.update_self _ _ _
  · dsimp [st4, mem4]; exact Function.update_self _ _ _

theorem pullMinNumStmt_runs {w h L arenaHi hp nodesBase x ptr lPtr rPtr
    fSelfVal fMinHas fMinVal fMinFirst fMinLast : ℕ}
    {sp : SplayProcs} {p : Program} {ω : ℕ → Bool}
    (hp_ok : SplayProgramOk w h p sp)
    (hhp_lt : hp < 2 ^ w)
    (hx_arena : ptr + NODE_STRIDE ≤ arenaHi)
    (hx_lt : ∀ off < NODE_STRIDE, ptr + off < 2 ^ w)
    (hl_lt : ∀ off < NODE_STRIDE, lPtr + off < 2 ^ w)
    (hr_lt : ∀ off < NODE_STRIDE, rPtr + off < 2 ^ w)
    (hfH : fMinHas < NODE_STRIDE) (hfV : fMinVal < NODE_STRIDE)
    (hfF : fMinFirst < NODE_STRIDE) (hfL : fMinLast < NODE_STRIDE)
    (hfS : fSelfVal < NODE_STRIDE)
    (hnd_off : [fMinHas, fMinVal, fMinFirst, fMinLast].Nodup)
    (st₀ : State)
    (hr0 : st₀.regs 0 = nodesBase) (hr1 : st₀.regs 1 = x) (hr2 : st₀.regs 2 = ptr)
    (hr4 : st₀.regs 4 = lPtr) (hr6 : st₀.regs 6 = rPtr)
    (hr15 : st₀.regs 15 = L) (hr16 : st₀.regs 16 = hp)
    (hl_ca : CanonicalNumAgg st₀.mem arenaHi hp h L
      (st₀.mem (lPtr + fMinHas)) (st₀.mem (lPtr + fMinVal))
      (st₀.mem (lPtr + fMinFirst)) (st₀.mem (lPtr + fMinLast)))
    (hx_ok : st₀.mem (ptr + OFF_HASE) ≠ 0 →
      st₀.mem (ptr + OFF_HASE) = 1 ∧ NumPtrOk st₀.mem arenaHi hp h L (st₀.mem (ptr + fSelfVal)))
    (hr_ok : st₀.mem (rPtr + fMinHas) ≠ 0 →
      st₀.mem (rPtr + fMinHas) = 1 ∧ NumPtrOk st₀.mem arenaHi hp h L (st₀.mem (rPtr + fMinVal))) :
    let agg := combineIntMinAgg
      (combineIntMinAgg
        (decodeNumAgg st₀.mem h L (st₀.mem (lPtr + fMinHas)) (st₀.mem (lPtr + fMinVal))
          (st₀.mem (lPtr + fMinFirst)) (st₀.mem (lPtr + fMinLast)))
        (decodeNumAgg st₀.mem h L (st₀.mem (ptr + OFF_HASE)) (st₀.mem (ptr + fSelfVal)) x x))
      (decodeNumAgg st₀.mem h L (st₀.mem (rPtr + fMinHas)) (st₀.mem (rPtr + fMinVal))
        (st₀.mem (rPtr + fMinFirst)) (st₀.mem (rPtr + fMinLast)))
    ∃ st' c,
      Runs w p ω (pullMinNumStmt sp 1 2 4 6 fSelfVal fMinHas fMinVal fMinFirst fMinLast)
        st₀ .normal st' c ∧
      c ≤ 128 * L + 255 ∧
      st'.regs 0 = nodesBase ∧ st'.regs 1 = x ∧ st'.regs 2 = ptr ∧
      st'.regs 4 = lPtr ∧ st'.regs 6 = rPtr ∧ st'.regs 15 = L ∧ st'.regs 16 = hp ∧
      (∀ a, a ≠ ptr + fMinHas → a ≠ ptr + fMinVal → a ≠ ptr + fMinFirst → a ≠ ptr + fMinLast →
        st'.mem a = st₀.mem a) ∧
      st'.mem (ptr + fMinHas) = (if agg.has then 1 else 0) ∧
      (st'.mem (ptr + fMinHas) = 0 →
        st'.mem (ptr + fMinVal) = 0 ∧ st'.mem (ptr + fMinFirst) = 0 ∧ st'.mem (ptr + fMinLast) = 0) ∧
      (st'.mem (ptr + fMinHas) = 1 →
        NumPtrOk st'.mem arenaHi hp h L (st'.mem (ptr + fMinVal)) ∧
        intVal st'.mem (st'.mem (ptr + fMinVal)) h L = agg.val) ∧
      st'.mem (ptr + fMinFirst) = agg.first ∧
      st'.mem (ptr + fMinLast) = agg.last := by
  intro agg
  rcases pullMinLoadLeft_exec hx_lt hl_lt hfH hfV hfF hfL hfS st₀ hr1 hr2 hr4 with
    ⟨st1, hr_1, hm1, hr1_other, h1_7, h1_8, h1_9, h1_10, h1_11, h1_12, h1_13, h1_14⟩
  have h1_pres : ∀ r, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 6 ∨ r = 15 ∨ r = 16 →
      st1.regs r = st₀.regs r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hr1_other _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
  have h1_15 : st1.regs 15 = L := (h1_pres 15 (by simp)).trans hr15
  have h1_ca : CanonicalNumAgg st1.mem arenaHi hp h L
      (st1.regs 7) (st1.regs 8) (st1.regs 9) (st1.regs 10) := by
    rw [hm1, h1_7, h1_8, h1_9, h1_10]; exact hl_ca
  have h1_xok : st1.regs 11 ≠ 0 → st1.regs 11 = 1 ∧ NumPtrOk st1.mem arenaHi hp h L (st1.regs 12) := by
    rw [hm1, h1_11, h1_12]; exact hx_ok
  rcases combineNumAggStmt_runs hp_ok hhp_lt (by decide : [7, 8, 9, 10, 11, 12, 13, 14, 15, 17].Nodup)
      st1 h1_15 h1_ca h1_xok ω with
    ⟨st2, c_cb1, hr_cb1, hm2, hr2_other, h2_ca, h2_dec, hc_cb1⟩
  have h2_pres : ∀ r, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 6 ∨ r = 15 ∨ r = 16 →
      st2.regs r = st₀.regs r := by
    intro r hr
    refine (hr2_other r ?_ ?_ ?_ ?_ ?_).trans (h1_pres r hr) <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr2_6 : st2.regs 6 = rPtr := (h2_pres 6 (by simp)).trans hr6
  rcases pullMinLoadRight_exec hr_lt hfH hfV hfF hfL st2 hr2_6 with
    ⟨st3, hr_3, hm3, hr3_other, h3_11, h3_12, h3_13, h3_14⟩
  have hm30 : st3.mem = st₀.mem := hm3.trans (hm2.trans hm1)
  have h3_pres : ∀ r, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 6 ∨ r = 15 ∨ r = 16 →
      st3.regs r = st₀.regs r := by
    intro r hr
    refine (hr3_other r ?_ ?_ ?_ ?_).trans (h2_pres r hr) <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h3_7 : st3.regs 7 = st2.regs 7 := hr3_other 7 (by decide) (by decide) (by decide) (by decide)
  have h3_8 : st3.regs 8 = st2.regs 8 := hr3_other 8 (by decide) (by decide) (by decide) (by decide)
  have h3_9 : st3.regs 9 = st2.regs 9 := hr3_other 9 (by decide) (by decide) (by decide) (by decide)
  have h3_10 : st3.regs 10 = st2.regs 10 := hr3_other 10 (by decide) (by decide) (by decide) (by decide)
  have h3_15 : st3.regs 15 = L := (h3_pres 15 (by simp)).trans hr15
  have h3_ca : CanonicalNumAgg st3.mem arenaHi hp h L
      (st3.regs 7) (st3.regs 8) (st3.regs 9) (st3.regs 10) := by
    rw [hm3, h3_7, h3_8, h3_9, h3_10]; exact h2_ca
  have h3_rok : st3.regs 11 ≠ 0 → st3.regs 11 = 1 ∧ NumPtrOk st3.mem arenaHi hp h L (st3.regs 12) := by
    rw [hm30, h3_11, h3_12, hm2, hm1]; exact hr_ok
  rcases combineNumAggStmt_runs hp_ok hhp_lt (by decide : [7, 8, 9, 10, 11, 12, 13, 14, 15, 17].Nodup)
      st3 h3_15 h3_ca h3_rok ω with
    ⟨st4, c_cb2, hr_cb2, hm4, hr4_other, h4_ca, h4_dec, hc_cb2⟩
  have h4_pres : ∀ r, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 6 ∨ r = 15 ∨ r = 16 →
      st4.regs r = st₀.regs r := by
    intro r hr
    refine (hr4_other r ?_ ?_ ?_ ?_ ?_).trans (h3_pres r hr) <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hr4_2 : st4.regs 2 = ptr := (h4_pres 2 (by simp)).trans hr2
  rcases pullMinStore_exec hx_lt hfH hfV hfF hfL hnd_off st4 hr4_2 with
    ⟨st5, hr_5, hr5_eq, hm5_other, hm5_H, hm5_V, hm5_F, hm5_L⟩
  have hfull : Runs w p ω (pullMinNumStmt sp 1 2 4 6 fSelfVal fMinHas fMinVal fMinFirst fMinLast)
      st₀ .normal st5 (41 + (c_cb1 + (23 + (c_cb2 + 23 + 1) + 1) + 1) + 1) := by
    dsimp only [pullMinNumStmt]
    exact runs_seq8_normal hr_1 (runs_seq_iff.mpr (Or.inr ⟨st2, c_cb1, 23 + (c_cb2 + 23 + 1) + 1, hr_cb1,
      runs_seq4_normal hr_3 (runs_seq_iff.mpr (Or.inr ⟨st4, c_cb2, 23, hr_cb2, hr_5, rfl⟩)), rfl⟩))
  have hm40 : st4.mem = st₀.mem := hm4.trans hm30
  have h4_agg : decodeNumAgg st4.mem h L (st4.regs 7) (st4.regs 8) (st4.regs 9) (st4.regs 10) = agg := by
    rw [h4_dec, hm3, h3_7, h3_8, h3_9, h3_10, h2_dec, hm1, hm2, h1_7, h1_8, h1_9, h1_10,
      h1_11, h1_12, h1_13, h1_14, h3_11, h3_12, h3_13, h3_14, hm2, hm1]
  have hhas_eq : decide (st4.regs 7 ≠ 0) = agg.has := by
    simpa [decodeNumAgg] using congrArg IntMinAgg.has h4_agg
  have hval_eq : optIntVal st4.mem h L (st4.regs 8) = agg.val := by
    simpa [decodeNumAgg] using congrArg IntMinAgg.val h4_agg
  have hf_eq : st4.regs 9 = agg.first := by
    simpa [decodeNumAgg] using congrArg IntMinAgg.first h4_agg
  have hl_eq : st4.regs 10 = agg.last := by
    simpa [decodeNumAgg] using congrArg IntMinAgg.last h4_agg
  have hag54 : ∀ a, arenaHi ≤ a → a < hp → st5.mem a = st4.mem a := fun a ha _ =>
    hm5_other a (by omega) (by omega) (by omega) (by omega)
  have hr5_has : st5.mem (ptr + fMinHas) = if agg.has then 1 else 0 := by
    rw [hm5_H]
    by_cases hh : agg.has = true
    · simp only [hh, ↓reduceIte]
      have hne : st4.regs 7 ≠ 0 := by
        intro hz
        have : decide (st4.regs 7 ≠ 0) = false := by simp [hz]
        rw [hhas_eq, hh] at this; cases this
      exact (h4_ca.2 hne).1
    · have hf : agg.has = false := Bool.eq_false_iff.mpr hh
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
      by_contra hne
      have : decide (st4.regs 7 ≠ 0) = true := by simp [hne]
      rw [hhas_eq, hf] at this; cases this
  have hr5_z : st5.mem (ptr + fMinHas) = 0 →
      st5.mem (ptr + fMinVal) = 0 ∧ st5.mem (ptr + fMinFirst) = 0 ∧ st5.mem (ptr + fMinLast) = 0 := by
    intro hz
    rw [hm5_H] at hz
    obtain ⟨h8, h9, h10⟩ := h4_ca.1 hz
    rw [hm5_V, hm5_F, hm5_L]
    exact ⟨h8, h9, h10⟩
  have hr5_nz : st5.mem (ptr + fMinHas) = 1 →
      NumPtrOk st5.mem arenaHi hp h L (st5.mem (ptr + fMinVal)) ∧
      intVal st5.mem (st5.mem (ptr + fMinVal)) h L = agg.val := by
    intro h1
    rw [hm5_H] at h1
    have hne : st4.regs 7 ≠ 0 := by omega
    have hok4 := (h4_ca.2 hne).2
    have hok5 : NumPtrOk st5.mem arenaHi hp h L (st5.mem (ptr + fMinVal)) := by
      rw [hm5_V]
      exact numPtrOk_congr le_rfl (fun a ha1 ha2 => hag54 a ha1 ha2) hok4
    refine ⟨hok5, ?_⟩
    rw [hm5_V]
    rw [intVal_agree_heap (fun a ha1 ha2 => hag54 a ha1 ha2) hok4.2.1 hok4.2.2.1]
    have hnz8 : st4.regs 8 ≠ 0 := hok4.1
    simpa [optIntVal, hnz8] using hval_eq
  refine ⟨st5, _, hfull, by omega,
    (by rw [hr5_eq]; exact (h4_pres 0 (by simp)).trans hr0),
    (by rw [hr5_eq]; exact (h4_pres 1 (by simp)).trans hr1),
    (by rw [hr5_eq]; exact (h4_pres 2 (by simp)).trans hr2),
    (by rw [hr5_eq]; exact (h4_pres 4 (by simp)).trans hr4),
    (by rw [hr5_eq]; exact (h4_pres 6 (by simp)).trans hr6),
    (by rw [hr5_eq]; exact (h4_pres 15 (by simp)).trans hr15),
    (by rw [hr5_eq]; exact (h4_pres 16 (by simp)).trans hr16),
    (fun a ha1 ha2 ha3 ha4 => (hm5_other a ha1 ha2 ha3 ha4).trans (by rw [hm40])),
    hr5_has, hr5_z, hr5_nz, by rw [hm5_F, hf_eq], by rw [hm5_L, hl_eq]⟩


end

end MinCostFlow.LinkCut.Prog
