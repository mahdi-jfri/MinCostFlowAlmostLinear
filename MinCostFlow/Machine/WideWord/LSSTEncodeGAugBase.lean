module

public import MinCostFlow.Machine.WideWord.LSSTEncodeSub
public import MinCostFlow.Machine.WideWord.LSSTWeightsBase
import WordRAM.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cost, contract, and initial phase lemmas for `encodeGAugProc`

This module defines `encodeGAugCost` and `encodeGAugContract`, provides helper lemmas for
`rangeCost` and `origOfCopy` prefixes, and proves the initial summation (`encodeGAug_sum_runs`)
and header (`encodeGAug_hdr_runs`) phases of `encodeGAugProc`.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Helper lemmas for range sums and `origOfCopy` prefixes -/

lemma rangeCost_add_const (f : ℕ → ℕ) (c n : ℕ) :
    rangeCost (fun j => f j + c) 0 n = rangeCost f 0 n + n * c := by
  induction n with
  | zero => simp [rangeCost]
  | succ n ih =>
    simp only [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton, Nat.succ_mul] at ih ⊢
    omega

lemma rangeCost_scale (g : ℕ → ℕ) (M n : ℕ) :
    rangeCost (fun j => g j * M) 0 n = rangeCost g 0 n * M := by
  simp only [rangeCost_zero_eq_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      List.map_append, List.map_singleton, List.sum_append, List.sum_singleton, ih, Nat.add_mul]

lemma rangeCost_map_take_sum (xs : List ℕ) (mult : ℕ → ℕ) :
    ∀ k ≤ xs.length,
      rangeCost (fun j => if h : j < xs.length then mult (xs[j]'h) else 0) 0 k =
        ((xs.take k).map mult).sum := by
  intro k hk
  induction k with
  | zero => simp [rangeCost]
  | succ k ih =>
    have hlt : k < xs.length := hk
    rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton]
    have ih' : ((List.range k).map fun j => if h : j < xs.length then mult (xs[j]'h) else 0).sum =
        ((xs.take k).map mult).sum := by
      simpa [rangeCost_zero_eq_range] using ih (Nat.le_of_lt hlt)
    rw [ih', dite_eq_left hlt, List.take_succ_eq_append_getElem hlt, List.map_append,
      List.map_singleton, List.sum_append, List.sum_singleton]

lemma take_map_sum_succ_le (xs : List ℕ) (mult : ℕ → ℕ) {k : ℕ} (hk : k < xs.length) :
    ((xs.take k).map mult).sum + mult (xs[k]'hk) = ((xs.take (k + 1)).map mult).sum ∧
      ((xs.take (k + 1)).map mult).sum ≤ (xs.map mult).sum := by
  have heq : ((xs.take k).map mult).sum + mult (xs[k]'hk) = ((xs.take (k + 1)).map mult).sum := by
    rw [List.take_succ_eq_append_getElem hk, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton]
  have hle : ((xs.take (k + 1)).map mult).sum ≤ (xs.map mult).sum := by
    have hsp : xs = xs.take (k + 1) ++ xs.drop (k + 1) := (List.take_append_drop (k + 1) xs).symm
    conv_rhs => rw [hsp, List.map_append, List.sum_append]
    omega
  exact ⟨heq, hle⟩

lemma take_map_sum_mono (xs : List ℕ) (mult : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b) :
    ((xs.take a).map mult).sum ≤ ((xs.take b).map mult).sum := by
  have h : xs.take a = (xs.take b).take a := by simp [List.take_take, Nat.min_eq_left hab]
  conv_lhs => rw [h]
  have hsp := (List.take_append_drop a (xs.take b)).symm
  conv_rhs => rw [hsp, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

lemma listAt_orig_prefix {xs : List ℕ} {mult : ℕ → ℕ} {origPtr : ℕ} :
    ∀ k ≤ xs.length, ∀ mem : ℕ → ℕ,
      (∀ (j : ℕ) (hj : j < xs.length), j < k →
        ∀ c < mult (xs[j]'hj), mem (origPtr + ((xs.take j).map mult).sum + c) = xs[j]'hj) →
      ListAt mem origPtr ((xs.take k).flatMap fun e => List.replicate (mult e) e) := by
  intro k hk mem hmem
  induction k generalizing mem with
  | zero => simp [listAt_nil]
  | succ k ih =>
    have hlt : k < xs.length := hk
    rw [List.take_succ_eq_append_getElem hlt, List.flatMap_append, List.flatMap_singleton]
    have hlen : ((xs.take k).flatMap fun e => List.replicate (mult e) e).length =
        ((xs.take k).map mult).sum := by
      simp [List.length_flatMap]
    refine listAt_append.mpr ⟨ih (Nat.le_of_lt hlt) mem fun j hj hjk c hc =>
      hmem j hj (Nat.lt_trans hjk (Nat.lt_succ_self k)) c hc, ?_⟩
    rw [hlen]
    exact listAt_replicate.mpr fun c hc => by
      simpa [Nat.add_assoc] using hmem k hlt (Nat.lt_succ_self k) c hc

/-! ### Cost and contract of `encodeGAugProc` -/

def encodeGAugCost (args : List ℕ) (mem : ℕ → ℕ) : ℕ :=
  let nlCnt := args.getD 0 0
  let multArr := args.getD 5 0
  let B_len := args.getD 9 0
  let L_sim := args.getD 11 0
  let m₁ := ((List.range nlCnt).map fun j => mem (multArr + j)).sum
  110 * nlCnt + (m₁ + B_len) * (70 * L_sim + 110) + 50 * L_sim + 120

def encodeGAugContract (w h : ℕ) : Contract where
  pre args mem :=
    ∃ (G : IndexedGraph) (V_list B : List ℕ) (mult w_orig : ℕ → ℕ)
      (nlArr tailArr headArr vIdxPtr multArr wArr K bArr L_sim origPtr outArr : ℕ),
      let nl := nonloopEdges G
      let m₁ := (nl.map mult).sum
      let encLen := 2 + 3 * (m₁ + B.length)
      args = [nl.length, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K,
        V_list.length, B.length, bArr, L_sim, 2 ^ h, origPtr, outArr] ∧
      G.Valid ∧ V_list.Nodup ∧
      (∀ u ∈ V_list, u < G.n) ∧
      (∀ e ∈ nl, G.tail e ∈ V_list ∧ G.head e ∈ V_list) ∧
      (∀ b ∈ B, b ∈ V_list) ∧
      1 ≤ h ∧ 2 * h + 2 ≤ w ∧ 1 ≤ K ∧ K ≤ L_sim ∧
      V_list.length < 2 ^ (L_sim * h) ∧ m₁ + B.length < 2 ^ (L_sim * h) ∧
      m₁ + B.length < 2 ^ w ∧
      nlArr + nl.length < 2 ^ w ∧ tailArr + G.m < 2 ^ w ∧ headArr + G.m < 2 ^ w ∧
      vIdxPtr + G.n < 2 ^ w ∧ multArr + nl.length < 2 ^ w ∧ wArr + nl.length * K < 2 ^ w ∧
      bArr + B.length < 2 ^ w ∧ origPtr + m₁ < 2 ^ w ∧ outArr + encLen * L_sim < 2 ^ w ∧
      DisjointRanges outArr (encLen * L_sim) nlArr nl.length ∧
      DisjointRanges outArr (encLen * L_sim) tailArr G.m ∧
      DisjointRanges outArr (encLen * L_sim) headArr G.m ∧
      DisjointRanges outArr (encLen * L_sim) vIdxPtr G.n ∧
      DisjointRanges outArr (encLen * L_sim) multArr nl.length ∧
      DisjointRanges outArr (encLen * L_sim) wArr (nl.length * K) ∧
      DisjointRanges outArr (encLen * L_sim) bArr B.length ∧
      DisjointRanges origPtr m₁ outArr (encLen * L_sim) ∧
      DisjointRanges origPtr m₁ nlArr nl.length ∧
      DisjointRanges origPtr m₁ tailArr G.m ∧
      DisjointRanges origPtr m₁ headArr G.m ∧
      DisjointRanges origPtr m₁ vIdxPtr G.n ∧
      DisjointRanges origPtr m₁ multArr nl.length ∧
      DisjointRanges origPtr m₁ wArr (nl.length * K) ∧
      DisjointRanges origPtr m₁ bArr B.length ∧
      ListAt mem nlArr nl ∧
      ListAt mem tailArr (List.ofFn fun i : Fin G.m => G.tail i) ∧
      ListAt mem headArr (List.ofFn fun i : Fin G.m => G.head i) ∧
      (∀ u ∈ V_list, mem (vIdxPtr + u) = V_list.idxOf u) ∧
      (∀ j (hj : j < nl.length), mem (multArr + j) = mult (nl[j]'hj)) ∧
      (∀ j (hj : j < nl.length), LimbsAt mem (wArr + j * K) K h (w_orig (nl[j]'hj))) ∧
      ListAt mem bArr B
  post args mem ret mem' :=
    ∃ (G : IndexedGraph) (V_list B : List ℕ) (mult w_orig : ℕ → ℕ)
      (nlArr tailArr headArr vIdxPtr multArr wArr K bArr L_sim origPtr outArr : ℕ),
      let nl := nonloopEdges G
      let m₁ := (nl.map mult).sum
      let encLen := 2 + 3 * (m₁ + B.length)
      args = [nl.length, nlArr, tailArr, headArr, vIdxPtr, multArr, wArr, K,
        V_list.length, B.length, bArr, L_sim, 2 ^ h, origPtr, outArr] ∧
      ret = m₁ ∧
      ListAt mem' origPtr (origOfCopy G mult) ∧
      (∀ i (hi : i < (buildGAug G V_list B mult w_orig).encode.length),
        LimbsAt mem' (outArr + i * L_sim) L_sim h
          ((buildGAug G V_list B mult w_orig).encode[i]'hi)) ∧
      (∀ a, (a < outArr ∨ outArr + encLen * L_sim ≤ a) →
        (a < origPtr ∨ origPtr + m₁ ≤ a) → mem' a = mem a)
  cost := encodeGAugCost

/-! ### Phase lemmas for summation and header encoding -/

structure EGAugRegs (s : State) (nlCnt nlArr tailArr headArr vIdxPtr multArr wArr K
    Vcnt B_len bArr L_sim B2h origPtr outArr : ℕ) : Prop where
  r0 : s.regs 0 = nlCnt
  r1 : s.regs 1 = nlArr
  r2 : s.regs 2 = tailArr
  r3 : s.regs 3 = headArr
  r4 : s.regs 4 = vIdxPtr
  r5 : s.regs 5 = multArr
  r6 : s.regs 6 = wArr
  r7 : s.regs 7 = K
  r8 : s.regs 8 = Vcnt
  r9 : s.regs 9 = B_len
  r10 : s.regs 10 = bArr
  r11 : s.regs 11 = L_sim
  r12 : s.regs 12 = B2h
  r13 : s.regs 13 = origPtr
  r14 : s.regs 14 = outArr

lemma egAugRegs_upd {s st' : State} {nlCnt nlArr tailArr headArr vIdxPtr multArr wArr K
    Vcnt B_len bArr L_sim B2h origPtr outArr r v : ℕ}
    (h : EGAugRegs s nlCnt nlArr tailArr headArr vIdxPtr multArr wArr K Vcnt B_len bArr L_sim B2h origPtr outArr)
    (hreg : st'.regs = Function.update s.regs r v) (hr : 15 ≤ r) :
    EGAugRegs st' nlCnt nlArr tailArr headArr vIdxPtr multArr wArr K Vcnt B_len bArr L_sim B2h origPtr outArr :=
  ⟨by rw [hreg, Function.update_of_ne (by omega)]; exact h.r0,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r1,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r2,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r3,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r4,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r5,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r6,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r7,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r8,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r9,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r10,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r11,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r12,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r13,
   by rw [hreg, Function.update_of_ne (by omega)]; exact h.r14⟩

lemma encodeGAug_sum_runs {w arithBase encodeBase : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {st₀ : State} {nl : List ℕ} {mult : ℕ → ℕ}
    {nlArr tailArr headArr vIdxPtr multArr wArr K Vcnt B_len bArr L_sim B2h origPtr outArr : ℕ}
    {k_cost T : ℕ} {Q : Outcome → State → Prop}
    (hw1 : 1 < 2 ^ w) (hnl_w : nl.length < 2 ^ w) (hmul_w : multArr + nl.length < 2 ^ w)
    (hm_aug_w : (nl.map mult).sum + B_len < 2 ^ w)
    (hmult_mem : ∀ j (hj : j < nl.length), mem (multArr + j) = mult (nl[j]'hj))
    (hregs0 : EGAugRegs st₀ nl.length nlArr tailArr headArr vIdxPtr multArr wArr K Vcnt B_len bArr L_sim B2h origPtr outArr)
    (hmem0 : st₀.mem = mem)
    (hrest : ∀ st₁ : State,
      EGAugRegs st₁ nl.length nlArr tailArr headArr vIdxPtr multArr wArr K Vcnt B_len bArr L_sim B2h origPtr outArr →
      st₁.regs 15 = (nl.map mult).sum →
      st₁.regs 16 = (nl.map mult).sum + B_len →
      st₁.mem = mem →
      ∃ o st' c,
        Runs w p ω
          (.call 17 (arithBase + idxFromHost) [.reg 8, .reg 14, .reg 11, .reg 12] ;;
           .call 17 (arithBase + idxFromHost) [.reg 16, .bin .add (.reg 14) (.reg 11), .reg 11, .reg 12] ;;
           .assign 17 (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 11))) ;;
           .assign 18 (.const 0) ;;
           forRange 19 (.const 0) (.reg 0)
             (.assign 20 (.load (.bin .add (.reg 1) (.reg 19))) ;;
              .assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
              .assign 21 (.load (.bin .add (.reg 4) (.reg 21))) ;;
              .assign 22 (.load (.bin .add (.reg 3) (.reg 20))) ;;
              .assign 22 (.load (.bin .add (.reg 4) (.reg 22))) ;;
              .assign 23 (.bin .add (.reg 6) (.bin .mul (.reg 19) (.reg 7))) ;;
              .assign 24 (.load (.bin .add (.reg 5) (.reg 19))) ;;
              .call 17 (encodeBase + idxEncodeEdgeCopies)
                [.reg 21, .reg 22, .reg 23, .reg 7, .reg 24, .reg 11, .reg 12, .reg 17, .reg 13, .reg 18, .reg 20] ;;
              .assign 18 (.bin .add (.reg 18) (.reg 24))) ;;
           .call 17 (encodeBase + idxEncodeBridges) [.reg 9, .reg 10, .reg 4, .reg 11, .reg 12, .reg 17] ;;
           .ret (.reg 15))
          st₁ o st' c ∧ Q o st' ∧ (k_cost + (16 * nl.length + 18)) + c ≤ T) :
    ∃ o st' c, Runs w p ω (encodeGAugProc arithBase encodeBase) st₀ o st' c ∧ Q o st' ∧ k_cost + c ≤ T := by
  dsimp only [encodeGAugProc]
  refine runs_seq_assign_step (Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1)) rfl fun st1 hm1 _ hr1 => ?_
  have hregs1 := egAugRegs_upd hregs0 hr1 (by decide)
  have hst1_15 : st1.regs 15 = 0 := by rw [hr1, Function.update_self]
  have hst1_mem : st1.mem = mem := hm1.trans hmem0
  let sumInv : ℕ → State → Prop := fun j st =>
    EGAugRegs st nl.length nlArr tailArr headArr vIdxPtr multArr wArr K Vcnt B_len bArr L_sim B2h origPtr outArr ∧
    st.regs 15 = ((nl.take j).map mult).sum ∧
    st.regs 16 = j ∧
    st.mem = mem
  have hsumLoop := Triple.forRange_const (w := w) (p := p) (r := 16) (lo := .const 0) (hi := .reg 0)
    (body := .assign 15 (.bin .add (.reg 15) (.load (.bin .add (.reg 5) (.reg 16)))))
    (P := fun st => st = st1) (Inv := sumInv) 7 0 nl.length (Nat.zero_le _) hw1 (fun _ => hnl_w)
    (fun st hst => by
      rw [hst]
      refine ⟨Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1), ?_⟩
      dsimp only [sumInv]
      exact ⟨egAugRegs_upd hregs1 rfl (by decide),
        by rw [Function.update_of_ne (by decide), hst1_15]; simp,
        by rw [Function.update_self], hst1_mem⟩)
    (fun _ st _ _ hi => hi.2.2.1)
    (fun _ st _ _ hi => Expr.eval_reg_of_eq hi.1.r0)
    (fun j _ hj => by
      intro st ω hInv
      have hregs := hInv.1
      have hr15 := hInv.2.1
      have hr16 := hInv.2.2.1
      have hst_m := hInv.2.2.2
      have hj1 := take_map_sum_succ_le nl mult hj
      have hm_lt : ((nl.take j).map mult).sum + mult (nl[j]'hj) < 2 ^ w :=
        lt_of_le_of_lt (le_trans (by omega) (Nat.le_add_right _ B_len)) hm_aug_w
      have hj_addr_w : multArr + j < 2 ^ w := by linarith only [hj, hmul_w]
      have hj_val : st.mem (multArr + j) = mult (nl[j]'hj) := by rw [hst_m, hmult_mem j hj]
      refine runs_start_le ?_
      refine runs_assign_le
        (Expr.eval_add (Expr.eval_reg_of_eq hr15)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hregs.r5) (Expr.eval_reg_of_eq hr16) hj_addr_w) hj_val)
          hm_lt) ?_ ?_
      · refine ⟨⟨egAugRegs_upd (egAugRegs_upd hregs rfl (by decide)) rfl (by decide), ?_, by dsimp only; rw [Function.update_self], hst_m⟩, ?_⟩
        · dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]; exact hj1.1
        · dsimp only; rw [Function.update_of_ne (by decide), hr16]
      · dsimp only [Expr.size]; omega)
  refine runs_seq_triple_le (hsumLoop.conseq (fun _ h => h) (fun o st hq => by
    cases o with | returned _ => exact False.elim hq | normal => exact hq) (fun _ _ => le_rfl)) rfl ?_
  intro st2 hInv2
  have hregs2 := hInv2.1
  have hr15_2 := hInv2.2.1
  have hm2 := hInv2.2.2.2
  have hr15_eq : st2.regs 15 = (nl.map mult).sum := by simpa using hr15_2
  refine runs_seq_assign_step (Expr.eval_add (Expr.eval_reg_of_eq hr15_eq) (Expr.eval_reg_of_eq hregs2.r9) hm_aug_w)
    rfl fun st3 hm3 _ hr3 => ?_
  have hregs3 := egAugRegs_upd hregs2 hr3 (by decide)
  have hr15_3 : st3.regs 15 = (nl.map mult).sum := by
    rw [hr3, Function.update_of_ne (by decide), hr15_eq]
  have hr16_3 : st3.regs 16 = (nl.map mult).sum + B_len := by rw [hr3, Function.update_self]
  obtain ⟨o, st', c, hrun, hq, hc⟩ := hrest st3 hregs3 hr15_3 hr16_3 (hm3.trans hm2)
  refine ⟨o, st', c, hrun, hq, ?_⟩
  dsimp only [argsSize, Expr.size]
  simp only [Nat.sub_zero]
  linarith only [hc]

lemma encodeGAug_hdr_runs {w arithBase encodeBase h : ℕ} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {st₃ : State} {nl : List ℕ}
    {nlArr tailArr headArr vIdxPtr multArr wArr K Vcnt B_len bArr L_sim origPtr outArr m₁ : ℕ}
    {k_cost T : ℕ} {Q : Outcome → State → Prop}
    (hfh_mc : MeetsContract w p (arithBase + idxFromHost) (mwFromHostContract w))
    (hh : 1 ≤ h) (hw2 : 2 * h + 2 ≤ w) (hw1 : 1 < 2 ^ w) (h2_w : 2 < 2 ^ w)
    (hV_lt : Vcnt < 2 ^ (L_sim * h)) (hm_lt : m₁ + B_len < 2 ^ (L_sim * h))
    (hV_w : Vcnt < 2 ^ w) (hm_w : m₁ + B_len < 2 ^ w) (hL_w : L_sim < 2 ^ w) (hB2h_w : 2 ^ h < 2 ^ w)
    (hout_2L_w : outArr + 2 * L_sim < 2 ^ w)
    (hregs3 : EGAugRegs st₃ nl.length nlArr tailArr headArr vIdxPtr multArr wArr K Vcnt B_len bArr L_sim (2 ^ h) origPtr outArr)
    (hr15_3 : st₃.regs 15 = m₁) (hr16_3 : st₃.regs 16 = m₁ + B_len) (hm3 : st₃.mem = mem)
    (hrest : ∀ st₆ : State,
      EGAugRegs st₆ nl.length nlArr tailArr headArr vIdxPtr multArr wArr K Vcnt B_len bArr L_sim (2 ^ h) origPtr outArr →
      st₆.regs 15 = m₁ →
      st₆.regs 17 = outArr + 2 * L_sim →
      st₆.regs 18 = 0 →
      LimbsAt st₆.mem outArr L_sim h Vcnt →
      LimbsAt st₆.mem (outArr + L_sim) L_sim h (m₁ + B_len) →
      (∀ a, a < outArr ∨ outArr + 2 * L_sim ≤ a → st₆.mem a = mem a) →
      ∃ o st' c,
        Runs w p ω
          (forRange 19 (.const 0) (.reg 0)
            (.assign 20 (.load (.bin .add (.reg 1) (.reg 19))) ;;
             .assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
             .assign 21 (.load (.bin .add (.reg 4) (.reg 21))) ;;
             .assign 22 (.load (.bin .add (.reg 3) (.reg 20))) ;;
             .assign 22 (.load (.bin .add (.reg 4) (.reg 22))) ;;
             .assign 23 (.bin .add (.reg 6) (.bin .mul (.reg 19) (.reg 7))) ;;
             .assign 24 (.load (.bin .add (.reg 5) (.reg 19))) ;;
             .call 17 (encodeBase + idxEncodeEdgeCopies)
               [.reg 21, .reg 22, .reg 23, .reg 7, .reg 24, .reg 11, .reg 12, .reg 17, .reg 13, .reg 18, .reg 20] ;;
             .assign 18 (.bin .add (.reg 18) (.reg 24))) ;;
           .call 17 (encodeBase + idxEncodeBridges) [.reg 9, .reg 10, .reg 4, .reg 11, .reg 12, .reg 17] ;;
           .ret (.reg 15))
          st₆ o st' c ∧ Q o st' ∧ (k_cost + (50 * L_sim + 55)) + c ≤ T) :
    ∃ o st' c,
      Runs w p ω
        (.call 17 (arithBase + idxFromHost) [.reg 8, .reg 14, .reg 11, .reg 12] ;;
         .call 17 (arithBase + idxFromHost) [.reg 16, .bin .add (.reg 14) (.reg 11), .reg 11, .reg 12] ;;
         .assign 17 (.bin .add (.reg 14) (.bin .mul (.const 2) (.reg 11))) ;;
         .assign 18 (.const 0) ;;
         forRange 19 (.const 0) (.reg 0)
           (.assign 20 (.load (.bin .add (.reg 1) (.reg 19))) ;;
            .assign 21 (.load (.bin .add (.reg 2) (.reg 20))) ;;
            .assign 21 (.load (.bin .add (.reg 4) (.reg 21))) ;;
            .assign 22 (.load (.bin .add (.reg 3) (.reg 20))) ;;
            .assign 22 (.load (.bin .add (.reg 4) (.reg 22))) ;;
            .assign 23 (.bin .add (.reg 6) (.bin .mul (.reg 19) (.reg 7))) ;;
            .assign 24 (.load (.bin .add (.reg 5) (.reg 19))) ;;
            .call 17 (encodeBase + idxEncodeEdgeCopies)
              [.reg 21, .reg 22, .reg 23, .reg 7, .reg 24, .reg 11, .reg 12, .reg 17, .reg 13, .reg 18, .reg 20] ;;
            .assign 18 (.bin .add (.reg 18) (.reg 24))) ;;
         .call 17 (encodeBase + idxEncodeBridges) [.reg 9, .reg 10, .reg 4, .reg 11, .reg 12, .reg 17] ;;
         .ret (.reg 15))
        st₃ o st' c ∧ Q o st' ∧ k_cost + c ≤ T := by
  have hout_L_w : outArr + L_sim < 2 ^ w := by omega
  have hout_w : outArr < 2 ^ w := by omega
  have h2L_w : 2 * L_sim < 2 ^ w := by omega
  refine runs_seq_call_step hfh_mc (vs := [Vcnt, outArr, L_sim, 2 ^ h])
    (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r8)
      (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r14)
        (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r11)
          (evalArgs_cons (Expr.eval_reg_of_eq hregs3.r12) (evalArgs_nil _ _)))))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx | hx <;> rw [hx] <;> assumption)
    ⟨Vcnt, outArr, L_sim, h, rfl, hh, hw2, hout_L_w⟩
    rfl (rfl : _ = 25 * L_sim + 15) fun _ mem4 st4 hp4 hm4 hr4 => ?_
  rw [hm3] at hp4
  obtain ⟨_, _, _, _, heq4, _, hd4, hf4⟩ := hp4
  simp only [List.cons.injEq, and_true] at heq4
  rcases heq4 with ⟨h1_4, h2_4, h3_4, h4_4⟩
  rw [← h1_4, ← h2_4, ← h3_4, ← Nat.pow_right_injective (by norm_num) h4_4] at hd4
  rw [← h2_4, ← h3_4] at hf4
  have hregs4 := egAugRegs_upd hregs3 hr4 (by decide)
  have hr15_4 : st4.regs 15 = m₁ := by rw [hr4, Function.update_of_ne (by decide), hr15_3]
  have hr16_4 : st4.regs 16 = m₁ + B_len := by rw [hr4, Function.update_of_ne (by decide), hr16_3]
  refine runs_seq_call_step hfh_mc (vs := [m₁ + B_len, outArr + L_sim, L_sim, 2 ^ h])
    (evalArgs_cons (Expr.eval_reg_of_eq hr16_4)
      (evalArgs_cons (Expr.eval_add (Expr.eval_reg_of_eq hregs4.r14) (Expr.eval_reg_of_eq hregs4.r11) hout_L_w)
        (evalArgs_cons (Expr.eval_reg_of_eq hregs4.r11)
          (evalArgs_cons (Expr.eval_reg_of_eq hregs4.r12) (evalArgs_nil _ _)))))
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx | hx <;> rw [hx] <;> assumption)
    ⟨m₁ + B_len, outArr + L_sim, L_sim, h, rfl, hh, hw2, (by linarith only [hout_2L_w])⟩
    rfl (rfl : _ = 25 * L_sim + 15) fun _ mem5 st5 hp5 hm5 hr5 => ?_
  rw [hm4] at hp5
  obtain ⟨_, _, _, _, heq5, _, hd5, hf5⟩ := hp5
  simp only [List.cons.injEq, and_true] at heq5
  rcases heq5 with ⟨h1_5, h2_5, h3_5, h4_5⟩
  rw [← h1_5, ← h2_5, ← h3_5, ← Nat.pow_right_injective (by norm_num) h4_5] at hd5
  rw [← h2_5, ← h3_5] at hf5
  have hregs5 := egAugRegs_upd hregs4 hr5 (by decide)
  have hr15_5 : st5.regs 15 = m₁ := by rw [hr5, Function.update_of_ne (by decide), hr15_4]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hregs5.r14)
      (Expr.eval_mul (Expr.eval_const h2_w) (Expr.eval_reg_of_eq hregs5.r11) h2L_w) hout_2L_w)
    rfl fun st5b hm5b _ hr5b => ?_
  have hregs5b := egAugRegs_upd hregs5 hr5b (by decide)
  have hr15_5b : st5b.regs 15 = m₁ := by rw [hr5b, Function.update_of_ne (by decide), hr15_5]
  have hr17_5b : st5b.regs 17 = outArr + 2 * L_sim := by rw [hr5b, Function.update_self]
  refine runs_seq_assign_step (Expr.eval_const (Nat.lt_trans Nat.zero_lt_one hw1)) rfl fun st6 hm6 _ hr6 => ?_
  have hregs6 := egAugRegs_upd hregs5b hr6 (by decide)
  have hr15_6 : st6.regs 15 = m₁ := by rw [hr6, Function.update_of_ne (by decide), hr15_5b]
  have hr17_6 : st6.regs 17 = outArr + 2 * L_sim := by
    rw [hr6, Function.update_of_ne (by decide), hr17_5b]
  have hr18_6 : st6.regs 18 = 0 := by rw [hr6, Function.update_self]
  have hmem6 : st6.mem = mem5 := hm6.trans (hm5b.trans hm5)
  have hl_V : LimbsAt st6.mem outArr L_sim h Vcnt := by
    rw [hmem6]
    exact (limbsAt_of_fromHost hV_lt hd4).congr fun q hq1 hq2 => by rw [hf5 q (Or.inl (by omega))]
  have hl_m : LimbsAt st6.mem (outArr + L_sim) L_sim h (m₁ + B_len) := by
    rw [hmem6]; exact limbsAt_of_fromHost hm_lt hd5
  have hfr6 : ∀ a, a < outArr ∨ outArr + 2 * L_sim ≤ a → st6.mem a = mem a := fun a ha => by
    rw [hmem6, hf5 a (by rcases ha with h1 | h1 <;> [left; right] <;> omega),
      hf4 a (by rcases ha with h1 | h1 <;> [left; right] <;> omega)]
  obtain ⟨o, st', c, hrun, hq, hc⟩ := hrest st6 hregs6 hr15_6 hr17_6 hr18_6 hl_V hl_m hfr6
  refine ⟨o, st', c, hrun, hq, ?_⟩
  dsimp only [argsSize, Expr.size]
  linarith only [hc]

end MinCostFlow.WideWord
