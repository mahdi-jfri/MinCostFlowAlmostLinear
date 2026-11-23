module

public import MinCostFlow.DynSpanner.Program.EmbOps
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.List.TakeDrop

/-!
# Verification of `mWalkPrefix` (`EmbPrefix`)

Proves `mWalkPrefix_meetsContract` for `embOpsProcs bOps` at index `embIdxWalkPrefix = 3`:
executing `prefixWalk H uStart W S` on Word-RAM in `O((prefixWalk H uStart W S).2.length + 1)`
time using an `O(1)` indicator table for `S` and calls to `dgIdxGetTail` / `dgIdxGetHead`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

private lemma prefixWalk_take_prefix (H : MGraph) (S : Finset ℕ) :
    ∀ (W : List (ℕ × Bool)) (u : ℕ), (prefixWalk H u W S).2 <+: W
  | [], _ => by unfold prefixWalk; split_ifs <;> simp
  | x :: xs, u => by
    unfold prefixWalk
    split_ifs with h
    · exact List.nil_prefix
    · exact List.cons_prefix_cons.mpr ⟨rfl, prefixWalk_take_prefix H S xs (H.dst x)⟩

private def walkCur (H : MGraph) (u : ℕ) (P : List (ℕ × Bool)) : ℕ :=
  match P with
  | [] => u
  | x :: xs => walkCur H (H.dst x) xs

private lemma walkCur_snoc (H : MGraph) (u : ℕ) :
    ∀ (P : List (ℕ × Bool)) (x : ℕ × Bool),
      walkCur H u (P ++ [x]) = H.dst x
  | [], _ => rfl
  | _ :: xs, x => walkCur_snoc H _ xs x

private lemma isWalk_take_mem_V {H : MGraph} (hVal : H.IsValid) :
    ∀ {u v : ℕ} {W : List (ℕ × Bool)}, u ∈ H.V → H.IsWalk u v W → ∀ (k : ℕ), k ≤ W.length →
      walkCur H u (W.take k) ∈ H.V ∧
      ∀ (hk_lt : k < W.length), (W[k]'hk_lt).1 ∈ H.E ∧ H.src (W[k]'hk_lt) = walkCur H u (W.take k)
  | u, _, [], huV, .nil _, k, hk => by
    simp only [List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨huV, fun h => absurd h (Nat.not_lt_zero _)⟩
  | u, v, x :: xs, huV, .cons he hsrc hW, 0, _ =>
    ⟨huV, fun _ => ⟨he, hsrc⟩⟩
  | u, v, x :: xs, _, .cons he hsrc hW, k + 1, hk => by
    have hdstV : H.dst x ∈ H.V := by
      rcases x with ⟨e, b⟩
      cases b <;> [exact (hVal e he).1; exact (hVal e he).2]
    simpa [walkCur, List.take_succ_cons] using isWalk_take_mem_V hVal hdstV hW k (by simpa using hk)

private lemma prefixWalk_char (H : MGraph) (S : Finset ℕ) :
    ∀ (W : List (ℕ × Bool)) (u : ℕ),
      let res := prefixWalk H u W S
      res.1 = walkCur H u res.2 ∧
      (∀ k < res.2.length, walkCur H u (W.take k) ∉ S) ∧
      (res.2.length < W.length → walkCur H u res.2 ∈ S) ∧
      (res.2.length = W.length → True)
  | [], u => by
    unfold prefixWalk
    split_ifs <;> simp [walkCur]
  | x :: xs, u => by
    by_cases hu : u ∈ S
    · unfold prefixWalk
      simp only [hu, ↓reduceIte, List.length_nil, List.length_cons]
      exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _), fun _ => hu, fun _ => trivial⟩
    · have ih := prefixWalk_char H S xs (H.dst x)
      unfold prefixWalk
      simp only [hu, ↓reduceIte]
      rcases ih with ⟨h1, h2, h3, _⟩
      have hpre : (prefixWalk H (H.dst x) xs S).2 <+: xs :=
        prefixWalk_take_prefix H S xs (H.dst x)
      refine ⟨?_, ?_, ?_, fun _ => trivial⟩
      · simpa [walkCur] using h1
      · intro k hk
        cases k with
        | zero => simpa [walkCur] using hu
        | succ m =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
          simpa [walkCur, List.take_succ_cons] using h2 m hk
      · intro hlt
        simp only [List.length_cons, Nat.succ_lt_succ_iff] at hlt
        simpa [walkCur] using h3 hlt

private theorem runs_cond_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (hT : v ≠ 0 → ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T)
    (hF : v = 0 → ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  by_cases hv : v = 0
  · rcases hF hv with ⟨o, st', c₁, hr₁, hq, hc⟩
    exact ⟨o, st', e.size + c₁ + 1,
      runs_cond_iff.mpr ⟨0, c₁, hv ▸ he, by simpa using hr₁, rfl⟩, hq, by omega⟩
  · rcases hT hv with ⟨o, st', c₁, hr₁, hq, hc⟩
    exact ⟨o, st', e.size + c₁ + 1,
      runs_cond_iff.mpr ⟨v, c₁, he, by simpa [hv] using hr₁, rfl⟩, hq, by omega⟩

public section

theorem mWalkPrefix_meetsContract {w vCap eCap : ℕ} {p : Program} {b bOps : ℕ}
    {H : MGraph} {uStart vEnd : ℕ} {W : List (ℕ × Bool)} {S : Finset ℕ}
    (hp : p.HasAt b (embOpsProcs bOps)) (hpOps : p.HasAt bOps dgOpsProcs) :
    MeetsContract w p (b + embIdxWalkPrefix)
      (mWalkPrefixContract w vCap eCap H uStart vEnd W S) := by
  refine meetsContract_of_runs (hp.get (i := embIdxWalkPrefix) (by simp [embOpsProcs, embIdxWalkPrefix]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨gPtr, wPtr, SBitPtr, dstPtr, rfl, hw16, hgB, hwB, hSB, hdstB,
    hdisjW, hdisjS, hdisjG, hH, hH_val, hvCap, heCap, huV, hW, hWat, hS⟩
  have hlt_gp : gPtr < 2 ^ w := hargs gPtr (by simp)
  have hlt_u : uStart < 2 ^ w := hargs uStart (by simp)
  have hlt_wp : wPtr < 2 ^ w := hargs wPtr (by simp)
  have hlt_Sp : SBitPtr < 2 ^ w := hargs SBitPtr (by simp)
  have hlt_dp : dstPtr < 2 ^ w := hargs dstPtr (by simp)
  have hlt_dp_end : dstPtr + (2 * (prefixWalk H uStart W S).2.length + 1) < 2 ^ w := hdstB
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have hw_ne0 : w ≠ 0 := by rintro rfl; omega
  have hlt_Wlen : W.length < 2 ^ w := by omega
  let res := prefixWalk H uStart W S
  let p₁ := res.2
  have hp₁_sub : p₁ <+: W := prefixWalk_take_prefix H S W uStart
  have hp₁_take : W.take p₁.length = p₁ := by
    rcases hp₁_sub with ⟨t, ht⟩
    rw [← ht, List.take_left]
  have hp₁_len : p₁.length ≤ W.length := hp₁_sub.length_le
  have hlt_p1len : p₁.length < 2 ^ w := by omega
  have hchar := prefixWalk_char H S W uStart
  dsimp only at hchar
  rcases hchar with ⟨hres1, hnotS, hhitS, _⟩
  refine runs_start_le ?_
  dsimp only [embOpsProcs, embIdxWalkPrefix, List.getElem_cons_succ, List.getElem_cons_zero,
    mWalkPrefixStmt]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (v := W.length) (by eval_expr)
    (by simpa [startState] using mWalkAt_len hWat)) ?_
  refine runs_seq_assign_le (v := uStart) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  let Inv : State → Prop := fun st =>
    ∃ (idx done : ℕ),
      idx ≤ p₁.length ∧ (done = 0 ∨ done = 1) ∧
      (done = 1 → idx = p₁.length) ∧
      st.regs 0 = gPtr ∧ st.regs 2 = wPtr ∧ st.regs 3 = SBitPtr ∧ st.regs 4 = dstPtr ∧
      st.regs 5 = W.length ∧ st.regs 6 = walkCur H uStart (W.take idx) ∧
      st.regs 7 = idx ∧ st.regs 8 = done ∧
      (∀ i < idx, st.mem (dstPtr + (1 + 2 * i)) = p₁[i]!.1 ∧
                  st.mem (dstPtr + (1 + 2 * i) + 1) = (if p₁[i]!.2 then 1 else 0)) ∧
      ∀ addr, addr < dstPtr ∨ dstPtr + (2 * p₁.length + 1) ≤ addr → st.mem addr = mem addr
  let condExpr : Expr := .bin .eq (.reg 8) (.const 0)
  let bodyStmt : Stmt :=
    .assign 9 (.load (.bin .add (.reg 3) (.reg 6))) ;;
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
      (.assign 8 (.const 1))
  let mFn : State → ℕ := fun st => 2 * (p₁.length - st.regs 7) + (1 - st.regs 8)
  let remFn : State → ℕ := fun st => 170 * (p₁.length - st.regs 7) + 40 * (1 - st.regs 8) + 10
  let condFn : State → ℕ := fun st => if st.regs 8 = 0 then 1 else 0
  have hloop : Triple w p Inv (.loop condExpr bodyStmt) (normalPost fun st =>
      st.regs 4 = dstPtr ∧ st.regs 6 = res.1 ∧ st.regs 7 = p₁.length ∧
      (∀ i < p₁.length, st.mem (dstPtr + (1 + 2 * i)) = p₁[i]!.1 ∧
                        st.mem (dstPtr + (1 + 2 * i) + 1) = (if p₁[i]!.2 then 1 else 0)) ∧
      ∀ addr, addr < dstPtr ∨ dstPtr + (2 * p₁.length + 1) ≤ addr → st.mem addr = mem addr) remFn := by
    refine Triple.loop_measure (condVal := condFn) (m := mFn) (rem := remFn)
      (fun st hInv => by
        rcases hInv with ⟨_, done, _, hd, _, _, _, _, _, _, _, _, hr8, _, _⟩
        dsimp only [condExpr, condFn]
        rcases hd with rfl | rfl <;> simp [Expr.eval, BinOp.eval, hr8, h0_lt, h1_lt])
      (fun st hInv hv => by
        rcases hInv with ⟨idx, done, _, hd, hdone_idx, _, _, _, hr4, _, hr6, hr7, hr8, hsteps, hfr⟩
        dsimp only [condFn] at hv
        have hd1 : done = 1 := by
          rcases hd with rfl | rfl
          · rw [hr8] at hv; simp at hv
          · rfl
        have hidx_eq : idx = p₁.length := hdone_idx hd1
        subst hidx_eq
        have hcur_eq : walkCur H uStart (W.take p₁.length) = res.1 := by
          rw [hp₁_take, hres1]
        refine ⟨⟨hr4, hr6.trans hcur_eq, hr7, hsteps, hfr⟩,
          by dsimp only [condExpr, Expr.size, remFn]; rw [hr7, hr8, hd1]; omega⟩)
      (fun st hInv hv => by
        rcases hInv with ⟨idx, done, hidx, hd, _, hr0, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hsteps, hfr⟩
        dsimp only [condFn] at hv
        have hd0 : done = 0 := by
          rcases hd with rfl | rfl
          · rfl
          · rw [hr8] at hv; simp at hv
        have hidx_W : idx ≤ W.length := le_trans hidx hp₁_len
        have htake_eq : W.take idx = p₁.take idx := by
          rcases hp₁_sub with ⟨t, ht⟩
          rw [← ht, List.take_append_of_le_length hidx]
        have hcur_V : walkCur H uStart (W.take idx) ∈ H.V := by
          rw [htake_eq]
          exact (isWalk_take_mem_V hH_val huV hW idx hidx).1
        have hcur_cap : walkCur H uStart (W.take idx) < vCap := hvCap _ hcur_V
        have hcur_ltw : walkCur H uStart (W.take idx) < 2 ^ w := by omega
        have hSp_cur : SBitPtr + walkCur H uStart (W.take idx) < 2 ^ w := by omega
        have hSbit_eq : st.mem (SBitPtr + walkCur H uStart (W.take idx)) =
            if walkCur H uStart (W.take idx) ∈ S then 1 else 0 := by
          rw [hfr _ (hdisjS _ hcur_cap)]
          exact hS _ hcur_cap
        by_cases h_lt : idx < p₁.length
        · have hidx_lt_W : idx < W.length := lt_of_lt_of_le h_lt hp₁_len
          have hnot_cur : walkCur H uStart (W.take idx) ∉ S := hnotS idx h_lt
          have hS0 : st.mem (SBitPtr + walkCur H uStart (W.take idx)) = 0 := by
            simp [hSbit_eq, hnot_cur]
          have hp₁_idx : p₁[idx] = W[idx] := by
            rcases hp₁_sub with ⟨t, ht⟩
            have : (p₁ ++ t)[idx]'(by rw [ht]; exact hidx_lt_W) = W[idx] := by simp [ht]
            rwa [List.getElem_append_left h_lt] at this
          have hedge_info : (W[idx]'hidx_lt_W).1 ∈ H.E ∧
              H.src (W[idx]'hidx_lt_W) = walkCur H uStart (W.take idx) := by
            have h0 := (isWalk_take_mem_V hH_val huV hW idx hidx).2 h_lt
            rwa [hp₁_idx, ← htake_eq] at h0
          have he_G : W[idx].1 ∈ H.E := hedge_info.1
          have he_cap : W[idx].1 < eCap := heCap _ he_G
          have he_ltw : W[idx].1 < 2 ^ w := by
            have he_dyn : eCap ≤ dynGraphSize vCap eCap := by dsimp [dynGraphSize]; omega
            omega
          have hdstB_p1 : dstPtr + (2 * p₁.length + 1) < 2 ^ w := hdstB
          have hdisjW_p1 : wPtr + (2 * W.length + 1) ≤ dstPtr ∨ dstPtr + (2 * p₁.length + 1) ≤ wPtr := hdisjW
          have h2idx : 2 * idx < 2 ^ w := by omega
          have hoff : 1 + 2 * idx < 2 ^ w := by omega
          have hwp_off : wPtr + (1 + 2 * idx) < 2 ^ w := by omega
          have hwp_off1 : wPtr + (1 + 2 * idx) + 1 < 2 ^ w := by omega
          have hdp_off : dstPtr + (1 + 2 * idx) < 2 ^ w := by omega
          have hdp_off1 : dstPtr + (1 + 2 * idx) + 1 < 2 ^ w := by omega
          have hw_e : st.mem (wPtr + (1 + 2 * idx)) = W[idx].1 := by
            rw [hfr _ (by rcases hdisjW_p1 with hdW | hdW <;> [left; right] <;> omega)]
            have := MWalkAt_step_edge hWat hidx_lt_W
            rwa [show wPtr + 1 + 2 * idx = wPtr + (1 + 2 * idx) by omega] at this
          have hw_d : st.mem (wPtr + (1 + 2 * idx) + 1) = (if W[idx].2 then 1 else 0) := by
            rw [hfr _ (by rcases hdisjW_p1 with hdW | hdW <;> [left; right] <;> omega)]
            have := MWalkAt_step_dir hWat hidx_lt_W
            rwa [show wPtr + 1 + 2 * idx + 1 = wPtr + (1 + 2 * idx) + 1 by omega] at this
          have hnext_cur : walkCur H uStart (W.take (idx + 1)) = H.dst W[idx] := by
            rw [List.take_succ_eq_append_getElem hidx_lt_W]
            exact walkCur_snoc H uStart (W.take idx) W[idx]
          refine ⟨160, ?_⟩
          intro s ω' hs_eq
          subst s
          suffices h : ∃ o s' c, Runs w p ω' bodyStmt st o s' c ∧
              (match o with
                | .returned u => normalPost (fun st =>
                    st.regs 4 = dstPtr ∧ st.regs 6 = res.1 ∧ st.regs 7 = p₁.length ∧
                    (∀ i < p₁.length, st.mem (dstPtr + (1 + 2 * i)) = p₁[i]!.1 ∧
                                      st.mem (dstPtr + (1 + 2 * i) + 1) = (if p₁[i]!.2 then 1 else 0)) ∧
                    ∀ addr, addr < dstPtr ∨ dstPtr + (2 * p₁.length + 1) ≤ addr → st.mem addr = mem addr)
                    (.returned u) s' ∧ condExpr.size + 160 + 1 ≤ remFn st
                | .normal => Inv s' ∧ mFn s' < mFn st ∧ condExpr.size + 160 + remFn s' + 1 ≤ remFn st) ∧
              0 + c ≤ 160 by
            rcases h with ⟨o, s', c, hr, hq, hc⟩
            exact ⟨o, s', c, hr, hq, by simpa using hc⟩
          dsimp only [bodyStmt]
          refine runs_seq_assign_le
            (Expr.eval_load_of_eq (v := 0) (by simp [Expr.eval, BinOp.eval, hr3, hr6, hSp_cur]) hS0) ?_
          refine runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, h0_lt, h1_lt]) ?_ ?_
          · intro _
            refine runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, hr5, hr7, hidx_lt_W, h1_lt]) ?_ ?_
            · intro _
              refine runs_seq_assign_le (v := 1 + 2 * idx)
                (by simp [Expr.eval, BinOp.eval, h1_lt, h2_lt, hr7, h2idx, hoff]) ?_
              refine runs_seq_assign_le
                (Expr.eval_load_of_eq (v := W[idx].1) (by simp [Expr.eval, BinOp.eval, hr2, hwp_off]) hw_e) ?_
              have hdt_lt : (if W[idx].2 then 1 else 0) < 2 ^ w := by split_ifs <;> omega
              refine runs_seq_assign_le
                (Expr.eval_load_of_eq (v := if W[idx].2 then 1 else 0)
                  (by simp [Expr.eval, BinOp.eval, h1_lt, hr2, hwp_off, hwp_off1]) hw_d) ?_
              refine runs_seq_store_le (v := W[idx].1) (x := dstPtr + (1 + 2 * idx))
                (by simp [Expr.eval, BinOp.eval, hr4, hdp_off]) (by eval_expr) ?_
              refine runs_seq_store_le (v := if W[idx].2 then 1 else 0) (x := dstPtr + (1 + 2 * idx) + 1)
                (by simp [Expr.eval, BinOp.eval, h1_lt, hr4, hdp_off, hdp_off1]) (by eval_expr) ?_
              let mem1 : ℕ → ℕ := Function.update
                (Function.update st.mem (dstPtr + (1 + 2 * idx)) W[idx].1)
                (dstPtr + (1 + 2 * idx) + 1) (if W[idx].2 then 1 else 0)
              have hfr1 : ∀ addr, addr < dstPtr ∨ dstPtr + (2 * p₁.length + 1) ≤ addr → mem1 addr = mem addr := by
                intro addr hout
                dsimp only [mem1]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact hfr addr hout
              have hH_1 : DynGraphAt mem1 gPtr vCap eCap H :=
                hH.of_agree fun addr hlo hhi => by
                  have hdg := hdisjG (addr - gPtr) (by omega)
                  have hadd : gPtr + (addr - gPtr) = addr := by omega
                  rw [hadd] at hdg
                  have hdg' : addr < dstPtr ∨ dstPtr + (2 * p₁.length + 1) ≤ addr := hdg
                  dsimp only [mem1]
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                  exact hfr addr hdg'
              let regs1 : ℕ → ℕ :=
                Function.update (Function.update (Function.update (Function.update st.regs 9 0)
                  10 (1 + 2 * idx)) 11 W[idx].1) 12 (if W[idx].2 then 1 else 0)
              have hr0_1 : regs1 0 = gPtr := by simp [regs1, hr0]
              have hr11_1 : regs1 11 = W[idx].1 := by simp [regs1]
              have hr12_1 : regs1 12 = if W[idx].2 then 1 else 0 := by simp [regs1]
              have hcont_after_call : ∀ (stC : State),
                  stC.mem = mem1 →
                  stC.regs 6 = H.dst W[idx] →
                  (∀ r' ≠ 6, stC.regs r' = regs1 r') →
                  ∃ s' c, Runs w p ω' (.assign 7 (.bin .add (.reg 7) (.const 1))) stC .normal s' c ∧
                    (Inv s' ∧ mFn s' < mFn st ∧ condExpr.size + 160 + remFn s' + 1 ≤ remFn st) ∧
                    c ≤ 10 := by
                intro stC hmc hr6c hrc
                have hidx1_lt : idx + 1 < 2 ^ w := by omega
                have hr7c : stC.regs 7 = idx := (hrc 7 (by decide)).trans (by simp [regs1, hr7])
                refine ⟨{ mem := stC.mem, regs := Function.update stC.regs 7 (idx + 1), pos := stC.pos },
                  (Expr.bin .add (.reg 7) (.const 1)).size + 1,
                  runs_assign_iff.mpr ⟨idx + 1, by simp [Expr.eval, BinOp.eval, h1_lt, hr7c, hidx1_lt],
                    rfl, rfl, rfl⟩,
                  ⟨⟨idx + 1, 0, by omega, Or.inl rfl, fun h => absurd h (by decide),
                    (by dsimp only; rw [Function.update_of_ne (by decide), hrc 0 (by decide)]; exact hr0_1),
                    (by dsimp only; rw [Function.update_of_ne (by decide), hrc 2 (by decide)]; simp [regs1, hr2]),
                    (by dsimp only; rw [Function.update_of_ne (by decide), hrc 3 (by decide)]; simp [regs1, hr3]),
                    (by dsimp only; rw [Function.update_of_ne (by decide), hrc 4 (by decide)]; simp [regs1, hr4]),
                    (by dsimp only; rw [Function.update_of_ne (by decide), hrc 5 (by decide)]; simp [regs1, hr5]),
                    (by dsimp only; rw [Function.update_of_ne (by decide), hr6c, hnext_cur]),
                    (by simp),
                    (by dsimp only; rw [Function.update_of_ne (by decide), hrc 8 (by decide)]; simp [regs1, hr8, hd0]),
                    (fun i hi => by
                      dsimp only; rw [hmc]
                      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hik | heq
                      · have ihs := hsteps i hik
                        dsimp only [mem1]
                        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                        exact ihs
                      · simp only [heq, getElem!_pos p₁ idx h_lt, hp₁_idx]
                        constructor
                        · simp only [mem1, Function.update_of_ne (Nat.ne_of_lt (Nat.lt_succ_self (dstPtr + (1 + 2 * idx)))),
                            Function.update_self]
                        · simp only [mem1, Function.update_self]),
                    (by rw [hmc]; exact hfr1)⟩,
                    (by dsimp only [mFn]; simp only [Function.update_self, Function.update_of_ne (by decide : (8 : ℕ) ≠ 7)];
                        rw [hrc 8 (by decide), hr7, hr8, hd0]; simp [regs1]; omega),
                    (by dsimp only [condExpr, Expr.size, remFn];
                        simp only [Function.update_self, Function.update_of_ne (by decide : (8 : ℕ) ≠ 7)];
                        rw [hrc 8 (by decide), hr7, hr8, hd0]; simp [regs1]; omega)⟩,
                  by dsimp only [Expr.size]; omega⟩
              rcases Bool.dichotomy W[idx].2 with hb | hb
              · have hdest : H.tail W[idx].1 = H.dst W[idx] := by
                  simp [MGraph.dst, hb]
                refine runs_seq_cond_le (v := 0) (by simp [Expr.eval, hb]) ?_ ?_
                · intro hc; exact absurd rfl hc
                · intro _
                  have hpre_t : (dgGetTailContract w vCap eCap H).pre [gPtr, W[idx].1] mem1 :=
                    ⟨gPtr, W[idx].1, rfl, hw16, hgB, he_G, hH_1⟩
                  have hev_t : evalArgs w ⟨mem1, regs1, st.pos⟩ [.reg 0, .reg 11] = some [gPtr, W[idx].1] := by
                    simp [evalArgs, Expr.eval, hr0_1, hr11_1]
                  rcases runs_call_of_meetsContract (r := 6) (dgGetTail_meetsContract hpOps)
                    hev_t (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl) <;> assumption)
                    hpre_t ω' with ⟨stC, cC, ret, hrC, hpC, hr6C, hregsC, hcostC⟩
                  rcases hpC with ⟨_, _, hEqt, hmc, hret_eq⟩
                  simp only [List.cons.injEq, and_true] at hEqt
                  rcases hEqt with ⟨rfl, rfl⟩
                  rcases hcont_after_call stC hmc (hr6C.trans (hret_eq.trans hdest)) hregsC with
                    ⟨s', cA, hrA, hinvA, hcA⟩
                  refine ⟨.normal, s', cC + cA + 1, runs_seq_iff.mpr (Or.inr ⟨stC, cC, cA, hrC, hrA, rfl⟩), hinvA, ?_⟩
                  dsimp only [dgGetTailContract, argsSize, Expr.size] at hcostC ⊢
                  omega
              · have hdest : H.head W[idx].1 = H.dst W[idx] := by
                  simp [MGraph.dst, hb]
                refine runs_seq_cond_le (v := 1) (by simp [Expr.eval, hb]) ?_ ?_
                · intro _
                  have hpre_h : (dgGetHeadContract w vCap eCap H).pre [gPtr, W[idx].1] mem1 :=
                    ⟨gPtr, W[idx].1, rfl, hw16, hgB, he_G, hH_1⟩
                  have hev_h : evalArgs w ⟨mem1, regs1, st.pos⟩ [.reg 0, .reg 11] = some [gPtr, W[idx].1] := by
                    simp [evalArgs, Expr.eval, hr0_1, hr11_1]
                  rcases runs_call_of_meetsContract (r := 6) (dgGetHead_meetsContract hpOps)
                    hev_h (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro z (rfl|rfl) <;> assumption)
                    hpre_h ω' with ⟨stC, cC, ret, hrC, hpC, hr6C, hregsC, hcostC⟩
                  rcases hpC with ⟨_, _, hEqh, hmc, hret_eq⟩
                  simp only [List.cons.injEq, and_true] at hEqh
                  rcases hEqh with ⟨rfl, rfl⟩
                  rcases hcont_after_call stC hmc (hr6C.trans (hret_eq.trans hdest)) hregsC with
                    ⟨s', cA, hrA, hinvA, hcA⟩
                  refine ⟨.normal, s', cC + cA + 1, runs_seq_iff.mpr (Or.inr ⟨stC, cC, cA, hrC, hrA, rfl⟩), hinvA, ?_⟩
                  dsimp only [dgGetHeadContract, argsSize, Expr.size] at hcostC ⊢
                  omega
                · intro hc; cases hc
            · intro hc; cases hc
          · intro hc; cases hc
        · have hidx_eq : idx = p₁.length := by omega
          subst hidx_eq
          refine ⟨30, ?_⟩
          intro s ω' hs_eq
          subst s
          suffices h : ∃ o s' c, Runs w p ω' bodyStmt st o s' c ∧
              (match o with
                | .returned u => normalPost (fun st =>
                    st.regs 4 = dstPtr ∧ st.regs 6 = res.1 ∧ st.regs 7 = p₁.length ∧
                    (∀ i < p₁.length, st.mem (dstPtr + (1 + 2 * i)) = p₁[i]!.1 ∧
                                      st.mem (dstPtr + (1 + 2 * i) + 1) = (if p₁[i]!.2 then 1 else 0)) ∧
                    ∀ addr, addr < dstPtr ∨ dstPtr + (2 * p₁.length + 1) ≤ addr → st.mem addr = mem addr)
                    (.returned u) s' ∧ condExpr.size + 30 + 1 ≤ remFn st
                | .normal => Inv s' ∧ mFn s' < mFn st ∧ condExpr.size + 30 + remFn s' + 1 ≤ remFn st) ∧
              0 + c ≤ 30 by
            rcases h with ⟨o, s', c, hr, hq, hc⟩
            exact ⟨o, s', c, hr, hq, by simpa using hc⟩
          dsimp only [bodyStmt]
          let bS : ℕ := if walkCur H uStart (W.take p₁.length) ∈ S then 1 else 0
          have hbS_lt : bS < 2 ^ w := by dsimp only [bS]; split_ifs <;> omega
          refine runs_seq_assign_le
            (Expr.eval_load_of_eq (v := bS) (by simp [Expr.eval, BinOp.eval, hr3, hr6, hSp_cur]) hSbit_eq) ?_
          by_cases hmemS : walkCur H uStart (W.take p₁.length) ∈ S
          · have hb1 : bS = 1 := by simp [bS, hmemS]
            refine runs_cond_le (v := 0) (by simp [Expr.eval, BinOp.eval, h0_lt, hb1]) ?_ ?_
            · intro hc; exact absurd rfl hc
            · intro _
              refine runs_assign_le (v := 1) (by eval_expr) ?_ (by dsimp only [Expr.size]; omega)
              refine ⟨⟨p₁.length, 1, le_refl _, Or.inr rfl, fun _ => rfl,
                ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsteps, hfr⟩, ?_, ?_⟩
              · simp [hr0]
              · simp [hr2]
              · simp [hr3]
              · simp [hr4]
              · simp [hr5]
              · simp [hr6]
              · simp [hr7]
              · simp
              · dsimp only [mFn]; simp [hr7, hr8, hd0]
              · dsimp only [condExpr, Expr.size, remFn]; simp [hr7, hr8, hd0]
          · have hp_not_lt : ¬ p₁.length < W.length := fun h => hmemS (by simpa [hp₁_take] using hhitS h)
            have hp_eq_W : p₁.length = W.length := by omega
            have hb0 : bS = 0 := by simp [bS, hmemS]
            refine runs_cond_le (v := 1) (by simp [Expr.eval, BinOp.eval, h0_lt, h1_lt, hb0]) ?_ ?_
            · intro _
              refine runs_cond_le (v := 0)
                (by simp [Expr.eval, BinOp.eval, hr5, hr7, hp_eq_W, h0_lt]) ?_ ?_
              · intro hc; exact absurd rfl hc
              · intro _
                refine runs_assign_le (v := 1) (by eval_expr) ?_ (by dsimp only [Expr.size]; omega)
                refine ⟨⟨p₁.length, 1, le_refl _, Or.inr rfl, fun _ => rfl,
                  ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsteps, hfr⟩, ?_, ?_⟩
                · simp [hr0]
                · simp [hr2]
                · simp [hr3]
                · simp [hr4]
                · simp [hr5]
                · simp [hr6]
                · simp [hr7]
                · simp
                · dsimp only [mFn]; simp [hr7, hr8, hd0]
                · dsimp only [condExpr, Expr.size, remFn]; simp [hr7, hr8, hd0]
            · intro hc; cases hc)
  refine runs_seq_triple_le hloop
    ⟨0, 0, Nat.zero_le _, Or.inl rfl, fun h => absurd h (by decide),
      (by simp [startState]), (by simp [startState]), (by simp [startState]),
      (by simp [startState]), (by simp [startState]), (by simp [startState, walkCur]),
      (by simp [startState]), (by simp [startState]), (fun _ hi => absurd hi (Nat.not_lt_zero _)), fun _ _ => rfl⟩ ?_
  intro stL ⟨hr4L, hr6L, hr7L, hstepsL, hfrL⟩
  dsimp only [p₁, res] at hr6L hr7L hstepsL hfrL
  have hcur_lt : (prefixWalk H uStart W S).1 < 2 ^ w := by
    have hcurV : (prefixWalk H uStart W S).1 ∈ H.V := by
      rw [show (prefixWalk H uStart W S).1 = walkCur H uStart (p₁.take p₁.length) by
        rw [List.take_length]; exact hres1]
      exact (isWalk_take_mem_V hH_val huV hW p₁.length (le_refl _)).1
    exact lt_trans (hvCap _ hcurV) (by have : vCap ≤ SBitPtr + vCap := Nat.le_add_left _ _; omega)
  refine runs_seq_store_le (x := dstPtr) (v := (prefixWalk H uStart W S).2.length)
    (by simp [Expr.eval, hr4L]) (by simp [Expr.eval, hr7L]) ?_
  refine runs_ret_le (by simp [Expr.eval, hr6L])
    ⟨gPtr, wPtr, SBitPtr, dstPtr, rfl, rfl, ?_, ?_⟩ ?_
  · refine mWalkAt_of_prefix_mem (by simp) fun i hi => ?_
    have hsi := hstepsL i hi
    dsimp only
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    simpa [getElem!_pos (prefixWalk H uStart W S).2 i hi] using hsi
  · intro addr hout
    dsimp only
    rw [Function.update_of_ne (by omega)]
    exact hfrL addr hout
  · dsimp only [mWalkPrefixContract, remFn, Expr.size, p₁, res]
    simp only [startState, Function.update_self, Function.update_of_ne (by decide : (7 : ℕ) ≠ 8), Nat.sub_zero]
    omega

end

end MinCostFlow.DynSpanner.Program
