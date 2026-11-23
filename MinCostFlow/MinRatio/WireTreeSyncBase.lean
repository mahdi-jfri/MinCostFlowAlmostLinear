module

public import MinCostFlow.MinRatio.WireSpecBase
public import MinCostFlow.MinRatio.SolverRep
public import MinCostFlow.MinRatio.TreeEditAccountDirection
public import MinCostFlow.MinRatio.PathNumericHistory
public import MinCostFlow.Num.Negate
public import WordRAM.CopyWords
import MinCostFlow.MinRatio.TreeEditPayloadSave
import WordRAM.Tactic

/-!
# Canonical payload copy and account bridges for tree synchronization (`WireTreeSyncBase`)

Provides the building blocks shared by terminal shift (`ShiftTermChainSyncSpecW`), deep shift
(`ShiftDeepChainSyncSpecW`), and chain update core (`OrdChainUpdateCoreSpecW`):
1. `wireCanonCopyBody`: copies a `PathEdgeAt` record from `src` into persistent off-tree storage
   `dst`, normalizing `forward = false` records via `PathEdgeValue.reverse` (negating gradient and
   flow) so that `SolverEdgeOrientInv` (`forward = true`) holds on every off-tree record.
2. `canonPathEdgeValue`: canonical (`forward = true`) representative of a `PathEdgeValue`.
3. `liveAccounts_of_solverStateRep`: extracts canonical `TreeEditLiveAccounts` and per-edge
   accounts/bounds from `solverStateRep`, `PathTreeNumericInv`, `OffTreeRecInv`, `OffTreeRecBound`.
4. `solverEdgeAccounts_of_treeSync`: reconstructs `SolverEdgeAccountsAt`, `SolverEdgeOrientInv`,
   `OffTreeRecInv`, and `OffTreeRecBound` after applying tree edits.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain SparseCore.Program

/-! ### Canonical `PathEdgeValue` -/

/-- Canonical (`forward = true`) representative of a `PathEdgeValue`. -/
@[expose] def canonPathEdgeValue (v : PathEdgeValue) : PathEdgeValue :=
  if v.forward then v else v.reverse

theorem canonPathEdgeValue_forward (v : PathEdgeValue) : (canonPathEdgeValue v).forward = true := by
  unfold canonPathEdgeValue
  cases h : v.forward <;> simp [PathEdgeValue.reverse, h]

theorem canonPathEdgeValue_originalFlow (v : PathEdgeValue) :
    (canonPathEdgeValue v).originalFlow = v.originalFlow := by
  unfold canonPathEdgeValue
  cases h : v.forward <;> simp [PathEdgeValue.originalFlow_reverse]

theorem canonPathEdgeValue_originalGradient (v : PathEdgeValue) :
    (canonPathEdgeValue v).originalGradient = v.originalGradient := by
  unfold canonPathEdgeValue
  cases h : v.forward <;> simp [PathEdgeValue.originalGradient_reverse]

theorem canonPathEdgeValue_length (v : PathEdgeValue) :
    (canonPathEdgeValue v).length = v.length := by
  unfold canonPathEdgeValue
  cases h : v.forward <;> simp [PathEdgeValue.reverse, h]

theorem canonPathEdgeValue_detector (v : PathEdgeValue) :
    (canonPathEdgeValue v).detector = v.detector := by
  unfold canonPathEdgeValue
  cases h : v.forward <;> simp [PathEdgeValue.reverse, h]

theorem canonPathEdgeValue_bounds {v : PathEdgeValue} {B : ℤ}
    (hg : |v.gradient| ≤ B) (hl : |v.length| ≤ B) (hf : |v.flow| ≤ B) (hd : |v.detector| ≤ B) :
    |(canonPathEdgeValue v).gradient| ≤ B ∧ |(canonPathEdgeValue v).length| ≤ B ∧
    |(canonPathEdgeValue v).flow| ≤ B ∧ |(canonPathEdgeValue v).detector| ≤ B := by
  unfold canonPathEdgeValue
  cases h : v.forward <;> simp [PathEdgeValue.reverse, h, hg, hl, hf, hd]

theorem canonPathEdgeValue_eq_self_of_forward {v : PathEdgeValue} (hf : v.forward = true) :
    canonPathEdgeValue v = v := by
  simp [canonPathEdgeValue, hf]

theorem canonPathEdgeValue_reverse (v : PathEdgeValue) :
    canonPathEdgeValue v.reverse = canonPathEdgeValue v := by
  cases v with
  | mk fwd g l f d =>
    cases fwd <;> simp [canonPathEdgeValue, PathEdgeValue.reverse]

/-! ### Canonical copy procedure (`wireCanonCopyBody`) -/

/-- Procedure `[src, dst, L, heap]` (`reg 0..3`) copying `PathEdgeAt` at `src` into `dst`
in canonical (`forward = true`) form. Uses at most `2 * L` scratch words at `heap` and returns
`nextHeap ≤ heap + 2 * L`. -/
@[expose] def wireCanonCopyBody (copy negate : ℕ) : Stmt :=
  .cond (.load (.bin .add (.reg 0) (.const 1)))
    (.call 4 copy [.reg 0, .reg 1, .bin .add (.const 2) (.bin .mul (.const 4) (.reg 2))] ;;
     .ret (.reg 3))
    (.store (.reg 1) (.const 1) ;;
     .store (.bin .add (.reg 1) (.const 1)) (.const 1) ;;
     .call 5 negate [.bin .add (.reg 0) (.const 2), .reg 2, .reg 3] ;;
     .call 4 copy [.reg 3, .bin .add (.reg 1) (.const 2), .reg 2] ;;
     .call 4 copy [.bin .add (.bin .add (.reg 0) (.const 2)) (.reg 2),
       .bin .add (.bin .add (.reg 1) (.const 2)) (.reg 2), .reg 2] ;;
     .call 6 negate [.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 2) (.reg 2)),
       .reg 2, .reg 5] ;;
     .call 4 copy [.reg 5,
       .bin .add (.bin .add (.reg 1) (.const 2)) (.bin .mul (.const 2) (.reg 2)), .reg 2] ;;
     .call 4 copy [.bin .add (.bin .add (.reg 0) (.const 2)) (.bin .mul (.const 3) (.reg 2)),
       .bin .add (.bin .add (.reg 1) (.const 2)) (.bin .mul (.const 3) (.reg 2)), .reg 2] ;;
     .ret (.reg 6))

theorem wireCanonCopyBody_noRand (copy negate : ℕ) : (wireCanonCopyBody copy negate).NoRand := by
  simp [wireCanonCopyBody, Stmt.NoRand]

/-- Contract for `wireCanonCopyBody`: writes `canonPathEdgeValue edge` at `dst`, using at most
`2 * L` scratch words at `heap` and at most `160 * L + 280` steps. -/
@[expose] def wireCanonCopyContract (w : ℕ) (edge : PathEdgeValue) : Contract where
  pre args mem := ∃ src dst L heap, args = [src, dst, L, heap] ∧
    4 < 2 ^ w ∧
    (dst + (2 + 4 * L) ≤ src ∨ src + (2 + 4 * L) ≤ dst) ∧
    src + (2 + 4 * L) ≤ heap ∧ dst + (2 + 4 * L) ≤ heap ∧ heap + 2 * L < 2 ^ w ∧
    PathEdgeAt mem src 4 L (some edge) ∧
    Num.Fits 4 L (-edge.gradient) ∧ Num.Fits 4 L (-edge.flow) ∧
    ZeroFrom mem heap
  post args mem ret mem' := ∃ src dst L heap, args = [src, dst, L, heap] ∧
    heap ≤ ret ∧ ret ≤ heap + 2 * L ∧
    PathEdgeAt mem' dst 4 L (some (canonPathEdgeValue edge)) ∧
    ZeroFrom mem' ret ∧
    ∀ a < heap, (a < dst ∨ dst + (2 + 4 * L) ≤ a) → mem' a = mem a
  cost args _ := 160 * args.getD 2 0 + 280

/-- `wireCanonCopyBody` meets `wireCanonCopyContract`. -/
theorem wireCanonCopy_meetsContract {w entry copy negate : ℕ} {p : Program}
    (edge : PathEdgeValue)
    (hp : p.procs[entry]? = some (wireCanonCopyBody copy negate))
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hn : MeetsContract w p negate (Num.negateContract w 4)) :
    MeetsContract w p entry (wireCanonCopyContract w edge) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨src, dst, L, heap, rfl, hw4, hds, hsh, hdh, hroom, hedge, hfitG, hfitF, hz⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hL4 : 2 + 4 * L < 2 ^ w := by omega
  have hdstW : dst < 2 ^ w := by omega
  have hsrcW : src < 2 ^ w := by omega
  have hLW : L < 2 ^ w := by omega
  have hheapW : heap < 2 ^ w := by omega
  obtain ⟨htag, hfwd, hgrad, hlen, hflow, hdet⟩ := hedge
  cases hf : edge.forward with
  | true =>
    have hbit : mem (src + 1) = 1 := by simpa [hf] using hfwd
    apply runs_start_le
    unfold wireCanonCopyBody
    refine runs_cond_le (v := 1) (by eval_expr)
      (fun _ => ?_) (fun h => by cases h)
    refine runs_seq_call_le hc (vs := [src, dst, 2 + 4 * L])
      (by eval_expr)
      (by simp [hsrcW, hdstW, hL4])
      ⟨src, dst, 2 + 4 * L, rfl, hw1, by omega, by omega, hds⟩ ?_
    intro _ mem1 _ hp1
    obtain ⟨s', d', n', harg1, _, hcp1, hfr1⟩ := hp1
    simp only [List.cons.injEq, and_true] at harg1
    obtain ⟨rfl, rfl, rfl⟩ := harg1
    refine runs_ret_le (v := heap) (by eval_expr) ?_ ?_
    · dsimp only [Outcome.value]
      refine ⟨src, dst, L, heap, rfl, le_rfl, by omega, ?_,
        fun a ha => (hfr1 a (Or.inr (by omega))).trans (hz a ha),
        fun a _ hsep => hfr1 a hsep⟩
      rw [canonPathEdgeValue_eq_self_of_forward hf]
      exact PathEdgeAt.copy ⟨htag, hfwd, hgrad, hlen, hflow, hdet⟩ hcp1
    · simp only [wireCanonCopyContract, copyWordsContract, Expr.size, argsSize,
        List.getD_cons_zero, List.getD_cons_succ]
      omega
  | false =>
    have hbit : mem (src + 1) = 0 := by simpa [hf] using hfwd
    apply runs_start_le
    unfold wireCanonCopyBody
    refine runs_cond_le (v := 0) (by eval_expr)
      (fun h => (h rfl).elim) (fun _ => ?_)
    -- Store `dst[0] := 1`, `dst[1] := 1`
    refine runs_seq_store_le (x := dst) (v := 1) (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (x := dst + 1) (v := 1) (by eval_expr) (by eval_expr) ?_
    let m0 := Function.update (Function.update mem dst 1) (dst + 1) 1
    have hm0_ge (a : ℕ) (ha : dst + 2 ≤ a) : m0 a = mem a := by
      dsimp only [m0]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hm0_lt (a : ℕ) (ha : a < dst) : m0 a = mem a := by
      dsimp only [m0]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    have hm0_src (a : ℕ) (hlo : src ≤ a) (hhi : a < src + (2 + 4 * L)) : m0 a = mem a := by
      rcases hds with h | h
      · exact hm0_ge a (by omega)
      · exact hm0_lt a (by omega)
    have hz0 : ZeroFrom m0 heap := fun a ha => (hm0_ge a (by omega)).trans (hz a ha)
    have hgrad0 : PathIntAt m0 (src + 2) 4 L edge.gradient :=
      hgrad.congr fun i hi => hm0_src _ (by omega) (by omega)
    -- Negate gradient at `heap` -> `h1 = heap + L`
    refine runs_seq_call_le hn (vs := [src + 2, L, heap])
      (by eval_expr)
      (by simp [show src + 2 < 2 ^ w by omega, hLW, hheapW])
      ⟨src + 2, L, heap, rfl, ⟨⟨src + 2, L, 1, heap, rfl, by omega, le_rfl, hgrad0.1⟩,
        hz0, by change heap + L < 2 ^ w; omega⟩⟩ ?_
    intro h1 m1 _ hpN1
    obtain ⟨hh1, _, _, hfrN1, hz1, hdigN1⟩ := hpN1
    change h1 = heap + L at hh1
    change ∀ x < heap, m1 x = m0 x at hfrN1
    change ZeroFrom m1 h1 at hz1
    have hnegG : PathIntAt m1 heap 4 L (-edge.gradient) := by
      obtain ⟨hv, hval⟩ := Num.negateCarry_value_one hgrad0.1 hdigN1
      rw [hgrad0.2, Num.wrap_of_fits hfitG] at hval
      exact ⟨hv, hval⟩
    -- Copy negated gradient `[heap, heap + L)` to `dst + 2`
    refine runs_seq_call_le hc (vs := [heap, dst + 2, L])
      (by eval_expr)
      (by simp [hheapW, show dst + 2 < 2 ^ w by omega, hLW])
      ⟨heap, dst + 2, L, rfl, hw1, by omega, by omega, Or.inl (by omega)⟩ ?_
    intro _ m2 _ hpC1
    obtain ⟨_, _, _, haC1, _, hcpC1, hfrC1⟩ := hpC1
    simp only [List.cons.injEq, and_true] at haC1; obtain ⟨rfl, rfl, rfl⟩ := haC1
    -- Copy length `[src + 2 + L, src + 2 + 2*L)` to `dst + 2 + L`
    refine runs_seq_call_le hc (vs := [src + 2 + L, dst + 2 + L, L])
      (by eval_expr)
      (by simp [show src + 2 + L < 2 ^ w by omega, show dst + 2 + L < 2 ^ w by omega, hLW])
      ⟨src + 2 + L, dst + 2 + L, L, rfl, hw1, by omega, by omega,
        by rcases hds with h | h; exact Or.inl (by omega); exact Or.inr (by omega)⟩ ?_
    intro _ m3 _ hpC2
    obtain ⟨_, _, _, haC2, _, hcpC2, hfrC2⟩ := hpC2
    simp only [List.cons.injEq, and_true] at haC2; obtain ⟨rfl, rfl, rfl⟩ := haC2
    -- Negate flow `[src + 2 + 2*L, ...)` at `h1 = heap + L` -> `h2 = heap + 2 * L`
    have hz3 : ZeroFrom m3 h1 := fun a ha =>
      (hfrC2 a (Or.inr (by omega))).trans ((hfrC1 a (Or.inr (by omega))).trans (hz1 a ha))
    have hflow3 : PathIntAt m3 (src + 2 + 2 * L) 4 L edge.flow :=
      hflow.congr fun i hi =>
        (hfrC2 _ (by rcases hds with h | h; exact Or.inr (by omega); exact Or.inl (by omega))).trans
          ((hfrC1 _ (by rcases hds with h | h; exact Or.inr (by omega); exact Or.inl (by omega))).trans
            ((hfrN1 _ (by omega)).trans (hm0_src _ (by omega) (by omega))))
    refine runs_seq_call_le hn (vs := [src + 2 + 2 * L, L, h1])
      (by eval_expr)
      (by simp [show src + 2 + 2 * L < 2 ^ w by omega, hLW, show h1 < 2 ^ w by omega])
      ⟨src + 2 + 2 * L, L, h1, rfl, ⟨⟨src + 2 + 2 * L, L, 1, h1, rfl, by omega, le_rfl, hflow3.1⟩,
        hz3, by change h1 + L < 2 ^ w; omega⟩⟩ ?_
    intro h2 m4 _ hpN2
    obtain ⟨hh2, _, _, hfrN2, hz4, hdigN2⟩ := hpN2
    change h2 = h1 + L at hh2
    change ∀ x < h1, m4 x = m3 x at hfrN2
    change ZeroFrom m4 h2 at hz4
    have hnegF : PathIntAt m4 h1 4 L (-edge.flow) := by
      obtain ⟨hv, hval⟩ := Num.negateCarry_value_one hflow3.1 hdigN2
      rw [hflow3.2, Num.wrap_of_fits hfitF] at hval
      exact ⟨hv, hval⟩
    -- Copy negated flow `[h1, h1 + L)` to `dst + 2 + 2 * L`
    refine runs_seq_call_le hc (vs := [h1, dst + 2 + 2 * L, L])
      (by eval_expr)
      (by simp [show h1 < 2 ^ w by omega, show dst + 2 + 2 * L < 2 ^ w by omega, hLW])
      ⟨h1, dst + 2 + 2 * L, L, rfl, hw1, by omega, by omega, Or.inl (by omega)⟩ ?_
    intro _ m5 _ hpC3
    obtain ⟨_, _, _, haC3, _, hcpC3, hfrC3⟩ := hpC3
    simp only [List.cons.injEq, and_true] at haC3; obtain ⟨rfl, rfl, rfl⟩ := haC3
    -- Copy detector `[src + 2 + 3 * L, ...)` to `dst + 2 + 3 * L`
    refine runs_seq_call_le hc (vs := [src + 2 + 3 * L, dst + 2 + 3 * L, L])
      (by eval_expr)
      (by simp [show src + 2 + 3 * L < 2 ^ w by omega, show dst + 2 + 3 * L < 2 ^ w by omega, hLW])
      ⟨src + 2 + 3 * L, dst + 2 + 3 * L, L, rfl, hw1, by omega, by omega,
        by rcases hds with h | h; exact Or.inl (by omega); exact Or.inr (by omega)⟩ ?_
    intro _ m6 _ hpC4
    obtain ⟨_, _, _, haC4, _, hcpC4, hfrC4⟩ := hpC4
    simp only [List.cons.injEq, and_true] at haC4; obtain ⟨rfl, rfl, rfl⟩ := haC4
    refine runs_ret_le (v := h2) (by eval_expr) ?_ ?_
    · dsimp only [Outcome.value]
      refine ⟨src, dst, L, heap, rfl, by omega, by omega, ?_, ?_, ?_⟩
      · -- `PathEdgeAt m6 dst 4 L (some (canonPathEdgeValue edge))`
        have hce : canonPathEdgeValue edge = edge.reverse := by simp [canonPathEdgeValue, hf]
        rw [hce]
        have hm6_d0 : m6 dst = 1 :=
          (hfrC4 _ (Or.inl (by omega))).trans ((hfrC3 _ (Or.inl (by omega))).trans
            ((hfrN2 _ (by omega)).trans ((hfrC2 _ (Or.inl (by omega))).trans
              ((hfrC1 _ (Or.inl (by omega))).trans ((hfrN1 _ (by omega)).trans
                (by simp [m0, Function.update_of_ne]))))))
        have hm6_d1 : m6 (dst + 1) = 1 :=
          (hfrC4 _ (Or.inl (by omega))).trans ((hfrC3 _ (Or.inl (by omega))).trans
            ((hfrN2 _ (by omega)).trans ((hfrC2 _ (Or.inl (by omega))).trans
              ((hfrC1 _ (Or.inl (by omega))).trans ((hfrN1 _ (by omega)).trans
                (by simp [m0]))))))
        refine ⟨hm6_d0, by simp [PathEdgeValue.reverse, hf, hm6_d1], ?_, ?_, ?_, ?_⟩
        · exact hnegG.congr fun i hi =>
            (hfrC4 _ (Or.inl (by omega))).trans ((hfrC3 _ (Or.inl (by omega))).trans
              ((hfrN2 _ (by omega)).trans ((hfrC2 _ (Or.inl (by omega))).trans (hcpC1 i hi))))
        · exact hlen.congr fun i hi =>
            (hfrC4 _ (Or.inl (by omega))).trans ((hfrC3 _ (Or.inl (by omega))).trans
              ((hfrN2 _ (by omega)).trans ((hcpC2 i hi).trans
                ((hfrC1 _ (by rcases hds with h | h; exact Or.inr (by omega); exact Or.inl (by omega))).trans
                  ((hfrN1 _ (by omega)).trans (hm0_src _ (by omega) (by omega)))))))
        · exact hnegF.congr fun i hi =>
            (hfrC4 _ (Or.inl (by omega))).trans (hcpC3 i hi)
        · exact hdet.congr fun i hi =>
            (hcpC4 i hi).trans ((hfrC3 _ (by rcases hds with h | h; exact Or.inr (by omega); exact Or.inl (by omega))).trans
              ((hfrN2 _ (by omega)).trans ((hfrC2 _ (by rcases hds with h | h; exact Or.inr (by omega); exact Or.inl (by omega))).trans
                ((hfrC1 _ (by rcases hds with h | h; exact Or.inr (by omega); exact Or.inl (by omega))).trans
                  ((hfrN1 _ (by omega)).trans (hm0_src _ (by omega) (by omega)))))))
      · intro a ha
        exact (hfrC4 a (Or.inr (by omega))).trans ((hfrC3 a (Or.inr (by omega))).trans (hz4 a ha))
      · intro a ha hsep
        have h1' : m6 a = m5 a := hfrC4 a (by rcases hsep with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
        have h2' : m5 a = m4 a := hfrC3 a (by rcases hsep with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
        have h3' : m4 a = m3 a := hfrN2 a (by omega)
        have h4' : m3 a = m2 a := hfrC2 a (by rcases hsep with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
        have h5' : m2 a = m1 a := hfrC1 a (by rcases hsep with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
        have h6' : m1 a = m0 a := hfrN1 a ha
        have h7' : m0 a = mem a := by rcases hsep with h | h; exact hm0_lt a h; exact hm0_ge a (by omega)
        exact h1'.trans (h2'.trans (h3'.trans (h4'.trans (h5'.trans (h6'.trans h7')))))
    · simp only [wireCanonCopyContract, copyWordsContract, Num.negateContract,
        Expr.size, argsSize, List.getD_cons_zero, List.getD_cons_succ]
      omega

/-! ### Bridges between `solverStateRep` and `TreeEditLiveAccounts` -/

/-- Extract canonical per-internal-edge accounts (`forward = true`) from `solverStateRep`,
`PathTreeNumericInv`, `OffTreeRecInv`, and `OffTreeRecBound`, giving `TreeEditLiveAccounts`
on `F = model.chain.toTreeChain.chainTree` and `PathEdgeAt` on off-tree edges. -/
theorem liveAccounts_of_solverStateRep {cfg : Alg2Config} {L P m V psi k epsExp drainUnit : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {root : ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {mem : ℕ → ℕ} {B R : ℤ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hoff : OffTreeRecInv model L mem tok.edgeRecords B)
    (hBd : OffTreeRecBound model L mem tok.edgeRecords B)
    (hFsub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E) :
    let F := model.chain.toTreeChain.chainTree
    ∃ canonVal : ℕ → PathEdgeValue,
      TreeEditLiveAccounts tok.tree tok.trees F (fun ei => mem (tok.slots + ei)) canonVal ∧
      (∀ e ∈ model.extG.E,
        let ei := model.extToInt e
        let v := canonVal ei
        v.forward = true ∧
        |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e ∧
        (∃ account : ℤ,
          (account : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
          v.detector = account - detectorThreshold P cfg.ε (model.extℓ e)) ∧
        (ei ∉ F.E → PathEdgeAt mem (mem (tok.edgeRecords + ei)) 4 L (some v))) := by
  intro F
  obtain ⟨_, _, _, _, hfresh, _, _, _, _, _, _, hlct, _, hedgeAcc, _, _, _, _, hwire, _⟩ := hrep
  have hEx : ∀ ei : ℕ, ei ∈ (model.chain.G 0).E →
      ∃ v : PathEdgeValue,
        v.forward = true ∧
        |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
        (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow (model.intToExt ei) ∧
        (v.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg (model.intToExt ei) ∧
        (v.length : ℝ) / (2 : ℝ) ^ P = model.extℓ (model.intToExt ei) ∧
        (∃ account : ℤ,
          (account : ℝ) / (2 : ℝ) ^ P = model.detectAccum (model.intToExt ei) ∧
          v.detector = account - detectorThreshold P cfg.ε (model.extℓ (model.intToExt ei))) ∧
        (ei ∈ F.E → TreeEditDirectedAccount tok.tree tok.trees (mem (tok.slots + ei))
          (vid (F.tail ei)) (vid (F.head ei)) v) ∧
        (ei ∉ F.E → PathEdgeAt mem (mem (tok.edgeRecords + ei)) 4 L (some v)) := by
    intro ei heiG
    obtain ⟨he2i, heExt⟩ := hfresh.hRight ei heiG
    have hbr := (hedgeAcc.1 (model.intToExt ei) heExt).2.2
    have hgl := hwire.2.2.2.2 (model.intToExt ei) heExt
    dsimp only at hbr hgl
    rw [he2i] at hbr hgl
    by_cases hin : ei ∈ F.E
    · rw [ite_eq_left hin] at hbr hgl
      obtain ⟨_, _, _, _, val, acc, hp, hfl, hac, hdet⟩ := hbr
      obtain ⟨hgr, hln, hft, hff⟩ := hgl val hp
      obtain ⟨hgB, hlB, hfB, hdB⟩ := hnum.2.2.2.1 _ val hp
      refine ⟨canonPathEdgeValue val, canonPathEdgeValue_forward val,
        (canonPathEdgeValue_bounds hgB hlB hfB hdB).1,
        (canonPathEdgeValue_bounds hgB hlB hfB hdB).2.1,
        (canonPathEdgeValue_bounds hgB hlB hfB hdB).2.2.1,
        (canonPathEdgeValue_bounds hgB hlB hfB hdB).2.2.2,
        by rw [canonPathEdgeValue_originalFlow]; exact hfl,
        by rw [canonPathEdgeValue_originalGradient]; exact hgr,
        by rw [canonPathEdgeValue_length]; exact hln,
        ⟨acc, hac, by rw [canonPathEdgeValue_detector]; exact hdet⟩,
        fun _ => ?_, fun hnot => (hnot hin).elim⟩
      unfold TreeEditDirectedAccount canonPathEdgeValue
      cases hv : val.forward
      · simp only [Bool.false_eq_true, ↓reduceIte, PathEdgeValue.reverse_reverse]
        exact Or.inr ⟨(hff hv).1, (hff hv).2, hp⟩
      · simp only [↓reduceIte]
        exact Or.inl ⟨(hft hv).1, (hft hv).2, hp⟩
    · rw [ite_eq_right hin] at hbr hgl
      obtain ⟨_, val, acc, hrec, hfl, hac, hdet, _⟩ := hbr
      obtain ⟨hfwd, hgr, hln⟩ := hgl val hrec
      have hrec' : PathEdgeAt mem (mem (tok.edgeRecords + model.extToInt (model.intToExt ei))) 4 L (some val) :=
        he2i.symm ▸ hrec
      have hdetB := hoff.1 (model.intToExt ei) heExt (he2i.symm ▸ hin) val hrec'
      obtain ⟨hgB, hlB, hfB⟩ := hBd (model.intToExt ei) heExt (he2i.symm ▸ hin) val hrec'
      exact ⟨val, hfwd, hgB, hlB, hfB, hdetB, hfl, hgr, hln, ⟨acc, hac, hdet⟩,
        fun h => (hin h).elim, fun _ => hrec⟩
  let canonVal : ℕ → PathEdgeValue := fun ei =>
    if h : ei ∈ (model.chain.G 0).E then (hEx ei h).choose else
      { forward := true, gradient := 0, length := 0, flow := 0, detector := 0 }
  refine ⟨canonVal, fun ei heiF => ?_, fun e heE => ?_⟩
  · have heiG : ei ∈ (model.chain.G 0).E := hFsub heiF
    have hsp := (hEx ei heiG).choose_spec
    dsimp only [canonVal]
    rw [dite_eq_left_of_eq_true (eq_true heiG)]
    exact hsp.2.2.2.2.2.2.2.2.2.1 heiF
  · have heiG : model.extToInt e ∈ (model.chain.G 0).E :=
      hfresh.hE ▸ Finset.mem_image_of_mem _ heE
    have hinv : model.intToExt (model.extToInt e) = e := hfresh.hLeft e heE
    dsimp only [canonVal]
    rw [dite_eq_left_of_eq_true (eq_true heiG)]
    generalize hv : (hEx (model.extToInt e) heiG).choose = v
    have hsp := (hEx (model.extToInt e) heiG).choose_spec
    rw [hv] at hsp
    obtain ⟨hfwd, hgB, hlB, hfB, hdB, hfl, hgr, hln, hacc, _, hoffRec⟩ := hsp
    rw [hinv] at hfl hgr hln hacc
    exact ⟨hfwd, hgB, hlB, hfB, hdB, hfl, hgr, hln, hacc, hoffRec⟩

/-- Reconstruct `SolverEdgeAccountsAt`, `SolverEdgeOrientInv`, `OffTreeRecInv`, and
`OffTreeRecBound` after applying tree edits that move edges between `tree` and `edgeRecords`
while keeping canonical per-edge accounts `canonVal`. -/
theorem solverEdgeAccounts_of_treeSync {cfg : Alg2Config} {L P : ℕ}
    {model : Alg2State cfg} {mem : ℕ → ℕ}
    {slots names slotThresholds edgeThresholds edgeRecords inOffReady intCap : ℕ}
    {tree : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    {canonVal : ℕ → PathEdgeValue} {B : ℤ}
    (hfresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hlct : LctInvWith pathPayload tree trees free depth)
    (hns : TreeEditNamedSlots tree trees model.chain.toTreeChain.chainTree
      (fun ei => mem (slots + ei)) (fun sl => mem (names + sl)))
    (hlive : TreeEditLiveAccounts tree trees model.chain.toTreeChain.chainTree
      (fun ei => mem (slots + ei)) canonVal)
    (hFsub : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E)
    (hcapE : ∀ ei ∈ (model.chain.G 0).E, ei < intCap)
    (hThr : ∀ e ∈ model.extG.E,
      PathIntAt mem (mem (edgeThresholds + model.extToInt e)) 4 L
        (detectorThreshold P cfg.ε (model.extℓ e)))
    (hCanon : ∀ e ∈ model.extG.E,
      let ei := model.extToInt e
      let v := canonVal ei
      v.forward = true ∧
      |v.gradient| ≤ B ∧ |v.length| ≤ B ∧ |v.flow| ≤ B ∧ |v.detector| ≤ B ∧
      (v.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
      (v.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
      (v.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e ∧
      ∃ account : ℤ,
        (account : ℝ) / (2 : ℝ) ^ P = model.detectAccum e ∧
        v.detector = account - detectorThreshold P cfg.ε (model.extℓ e))
    (hTreeSlotThr : ∀ ei ∈ model.chain.toTreeChain.chainTree.E,
      mem (slotThresholds + mem (slots + ei)) = mem (edgeThresholds + ei))
    (hOffSlot0 : ∀ e ∈ model.extG.E, model.extToInt e ∉ model.chain.toTreeChain.chainTree.E →
      mem (slots + model.extToInt e) = 0)
    (hOffRec : ∀ e ∈ model.extG.E, model.extToInt e ∉ model.chain.toTreeChain.chainTree.E →
      PathEdgeAt mem (mem (edgeRecords + model.extToInt e)) 4 L (some (canonVal (model.extToInt e))))
    (hOffPush : ∀ e ∈ model.extG.E, model.extToInt e ∉ model.chain.toTreeChain.chainTree.E →
      0 ≤ (canonVal (model.extToInt e)).detector → mem (inOffReady + model.extToInt e) = 1)
    (hOffDisj : ∀ e₁ ∈ model.extG.E, ∀ e₂ ∈ model.extG.E, e₁ ≠ e₂ →
      model.extToInt e₁ ∉ model.chain.toTreeChain.chainTree.E →
      model.extToInt e₂ ∉ model.chain.toTreeChain.chainTree.E →
      mem (edgeRecords + model.extToInt e₁) + (2 + 4 * L) ≤ mem (edgeRecords + model.extToInt e₂) ∨
      mem (edgeRecords + model.extToInt e₂) + (2 + 4 * L) ≤ mem (edgeRecords + model.extToInt e₁)) :
    SolverEdgeAccountsAt model L P mem slots names slotThresholds edgeThresholds
      edgeRecords inOffReady intCap tree trees ∧
    SolverEdgeOrientInv L P model mem slots edgeRecords tree trees ∧
    OffTreeRecInv model L mem edgeRecords B ∧
    OffTreeRecBound model L mem edgeRecords B := by
  let F := model.chain.toTreeChain.chainTree
  have hfp_uniq : ∀ sl v₁ v₂, (sl, some v₁) ∈ forestPairs pathPayload tree.splay trees →
      (sl, some v₂) ∈ forestPairs pathPayload tree.splay trees → v₁ = v₂ := by
    intro sl v₁ v₂ h1 h2
    have hnd : ((forestPairs pathPayload tree.splay trees).map Prod.fst).Nodup := by
      have hp : ((forestPairs pathPayload tree.splay trees).map Prod.fst).Perm
          (trees.flatMap AuxTree.toList) := by
        clear h1 h2 hlct hns hlive
        induction trees with
        | nil => simp [forestPairs]
        | cons t rest ih =>
          simp only [forestPairs, List.flatMap_cons, List.map_append]
          exact ((SplayState.evalPairs_map_fst pathPayload tree.splay t false pathPayload.idTag) ▸
            t.evalInorder_perm _ _).append ih
      exact hp.nodup_iff.mpr hlct.activeNodup
    have haux : ∀ (xs : List (ℕ × Option PathEdgeValue)), (xs.map Prod.fst).Nodup →
        (sl, some v₁) ∈ xs → (sl, some v₂) ∈ xs → v₁ = v₂ := by
      intro xs hxs h1' h2'
      induction xs with
      | nil => cases h1'
      | cons hd tl ih =>
        rw [List.map_cons, List.nodup_cons] at hxs
        rcases List.mem_cons.mp h1' with h1e | h1t <;> rcases List.mem_cons.mp h2' with h2e | h2t
        · exact Option.some.inj (congrArg Prod.snd (h1e.trans h2e.symm))
        · exact (hxs.1 (h1e ▸ List.mem_map.mpr ⟨(sl, some v₂), h2t, rfl⟩)).elim
        · exact (hxs.1 (h2e ▸ List.mem_map.mpr ⟨(sl, some v₁), h1t, rfl⟩)).elim
        · exact ih hxs.2 h1t h2t
    exact haux _ hnd h1 h2
  have hfp_mem_active : ∀ sl val, (sl, some val) ∈ forestPairs pathPayload tree.splay trees →
      sl ∈ trees.flatMap AuxTree.toList := by
    intro sl val hp
    obtain ⟨t, ht, hp'⟩ := List.mem_flatMap.mp hp
    refine List.mem_flatMap.mpr ⟨t, ht, ?_⟩
    have hm : sl ∈ (SplayState.evalPairs pathPayload tree.splay t false pathPayload.idTag).map Prod.fst :=
      List.mem_map.mpr ⟨(sl, some val), hp', rfl⟩
    rw [SplayState.evalPairs_map_fst] at hm
    exact (t.evalInorder_perm _ _).mem_iff.mp hm
  have hpa_uniq : ∀ addr v₁ v₂, PathEdgeAt mem addr 4 L (some v₁) →
      PathEdgeAt mem addr 4 L (some v₂) → v₁ = v₂ := by
    intro addr v₁ v₂ h1 h2
    cases v₁ with | mk f1 g1 l1 fl1 d1 =>
    cases v₂ with | mk f2 g2 l2 fl2 d2 =>
    obtain ⟨_, hf1, hg1, hl1, hfl1, hd1⟩ := h1
    obtain ⟨_, hf2, hg2, hl2, hfl2, hd2⟩ := h2
    have hfeq : f1 = f2 := by
      cases f1 <;> cases f2
      · rfl
      · simp only [Bool.false_eq_true, ↓reduceIte] at hf1; simp only [↓reduceIte] at hf2; omega
      · simp only [↓reduceIte] at hf1; simp only [Bool.false_eq_true, ↓reduceIte] at hf2; omega
      · rfl
    simp only [PathEdgeValue.mk.injEq]
    exact ⟨hfeq, hg1.2.symm.trans hg2.2, hl1.2.symm.trans hl2.2,
      hfl1.2.symm.trans hfl2.2, hd1.2.symm.trans hd2.2⟩
  refine ⟨⟨fun e heE => ?_, fun sl val hsl hp => ?_⟩, fun e heE => ?_,
    ⟨fun e heE hnot val hpa => ?_, hOffDisj⟩, fun e heE hnot val hpa => ?_⟩
  · have heiG : model.extToInt e ∈ (model.chain.G 0).E :=
      hfresh.hE ▸ Finset.mem_image_of_mem _ heE
    have heiCap : model.extToInt e < intCap := hcapE _ heiG
    obtain ⟨hfwd, _, _, _, _, hfl, _, _, ⟨acc, hac, hdet⟩⟩ := hCanon e heE
    refine ⟨heiCap, hThr e heE, ?_⟩
    split_ifs with hin
    · obtain ⟨_, his, hnm⟩ := hns.forward _ hin
      have hsnz : mem (slots + model.extToInt e) ≠ 0 := by unfold isEdgeSlot at his; omega
      refine ⟨hsnz, his, hnm, hTreeSlotThr _ hin, ?_⟩
      rcases hlive _ hin with ⟨_, _, hpair⟩ | ⟨_, _, hpair⟩
      · exact ⟨canonVal (model.extToInt e), acc, hpair, hfl, hac, hdet⟩
      · exact ⟨(canonVal (model.extToInt e)).reverse, acc, hpair,
          by rw [PathEdgeValue.originalFlow_reverse]; exact hfl, hac,
          by simpa [PathEdgeValue.reverse] using hdet⟩
    · exact ⟨hOffSlot0 e heE hin, canonVal (model.extToInt e), acc, hOffRec e heE hin,
        hfl, hac, hdet, hOffPush e heE hin⟩
  · have hact := hfp_mem_active sl val hp
    obtain ⟨heF, hse⟩ := hns.inverse sl hact hsl
    have heG : mem (names + sl) ∈ (model.chain.G 0).E := hFsub heF
    obtain ⟨he2i, heExt⟩ := hfresh.hRight _ heG
    exact ⟨hcapE _ heG, heF, hse, heExt, he2i⟩
  · dsimp only
    obtain ⟨hfwd, _, _, _, _, _, hgr, hln, _⟩ := hCanon e heE
    split_ifs with hin
    · intro val hp
      rcases hlive _ hin with ⟨hp1, hp2, hp0⟩ | ⟨hp1, hp2, hp0⟩
      · have heq := hfp_uniq _ val _ hp hp0
        subst heq
        exact ⟨hgr, hln, fun _ => ⟨hp1, hp2⟩, fun hf => by rw [hfwd] at hf; cases hf⟩
      · have heq := hfp_uniq _ val _ hp hp0
        subst heq
        have hrf : (canonVal (model.extToInt e)).reverse.forward = false := by
          simp [PathEdgeValue.reverse, hfwd]
        exact ⟨by rw [PathEdgeValue.originalGradient_reverse]; exact hgr,
          by simpa [PathEdgeValue.reverse] using hln,
          (fun ht => by rw [hrf] at ht; cases ht), fun _ => ⟨hp1, hp2⟩⟩
    · intro val hpa
      have heq := hpa_uniq _ val _ hpa (hOffRec e heE hin)
      subst heq
      exact ⟨hfwd, hgr, hln⟩
  · have heq := hpa_uniq _ val _ hpa (hOffRec e heE hnot)
    subst heq
    exact (hCanon e heE).2.2.2.2.1
  · have heq := hpa_uniq _ val _ hpa (hOffRec e heE hnot)
    subst heq
    obtain ⟨_, hgB, hlB, hfB, _⟩ := hCanon e heE
    exact ⟨hgB, hlB, hfB⟩

end MinCostFlow.MinRatio
