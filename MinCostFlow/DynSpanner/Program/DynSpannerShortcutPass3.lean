module

public import MinCostFlow.DynSpanner.Program.DynSpannerShortcutPasses

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Walk-Shortcutting Pass 3 Verification (`DynSpannerShortcutPass3`)

Proves `shortcut_pass3_triple` for Pass 3 of `dsShortcutEdgeStmt`: traverses the linked stack
`StackListIn` containing `Q₀ = shortcutWalk G (G.tail e) (emb e)`, clears vertex stamps (including
`vEnd`), writes the compact `MWalkAt` encoding at `[outWalkPtr .. outWalkPtr + 1 + 2 * Q₀.length)`,
updates `mEmbPtr[e] := outWalkPtr`, and advances `r5 := outWalkPtr + 1 + 2 * Q₀.length`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

section

private lemma drop_eq_getElem_cons_of_eq {α : Type*} {xs ys : List α} {idx : ℕ} {x : α}
    (hidx : idx < xs.length) (hdrop : xs.drop idx = x :: ys) :
    xs[idx]'hidx = x ∧ xs.drop (idx + 1) = ys := by
  have h1 : xs.drop idx = xs[idx]'hidx :: xs.drop (idx + 1) :=
    List.drop_eq_getElem_cons hidx
  rw [h1] at hdrop
  cases hdrop
  exact ⟨rfl, rfl⟩

/-- Loop invariant for Pass 3 over the remaining stack suffix `xs = Q₀.drop idx`. -/
private def Pass3LoopInv (vCap vStampPtr stampVal gen0 nodeBase outWalkPtr : ℕ)
    (G : MGraph) (vEnd : ℕ) (Q₀ : List (ℕ × Bool))
    (memPre : ℕ → ℕ) (regsPre : ℕ → ℕ) (xs : List (ℕ × Bool)) (st : State) : Prop :=
  ∃ idx cur : ℕ,
    idx + xs.length = Q₀.length ∧
    xs = Q₀.drop idx ∧
    cur ∈ G.V ∧
    G.IsWalk cur vEnd xs ∧
    (G.walkVertices cur xs).Nodup ∧
    StackListIn G nodeBase outWalkPtr st.mem (st.regs 18) cur xs ∧
    VStampInv st.mem vStampPtr vCap stampVal gen0 (G.walkVertices cur xs) ∧
    st.regs 21 = outWalkPtr + 1 + 2 * idx ∧
    st.regs 22 = outWalkPtr ∧
    st.regs 23 = idx ∧
    (∀ r, (r ≤ 11 ∨ r = 16 ∨ r = 19) → st.regs r = regsPre r) ∧
    (∀ j < idx, ∃ hj : j < Q₀.length,
      st.mem (outWalkPtr + 1 + 2 * j) = (Q₀[j]'hj).1 ∧
      st.mem (outWalkPtr + 1 + 2 * j + 1) = if (Q₀[j]'hj).2 then 1 else 0) ∧
    ∀ addr, (∀ v < vCap, addr ≠ vStampPtr + v) →
      (addr < outWalkPtr + 1 ∨ outWalkPtr + 1 + 2 * idx ≤ addr) →
      st.mem addr = memPre addr

private theorem shortcut_pass3_loop_triple {w vCap vStampPtr stampVal gen0 nodeBase
    outWalkPtr vEnd u0 : ℕ} {G : MGraph} {Q₀ : List (ℕ × Bool)} {p : Program}
    {memPre regsPre : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hnode1 : 1 ≤ nodeBase)
    (hvst_disj : ∀ v < vCap, vStampPtr + v < nodeBase)
    (hvst_w : vStampPtr + vCap < 2 ^ w)
    (_hnode_le : nodeBase ≤ outWalkPtr)
    (hout_w : outWalkPtr + 1 + 2 * Q₀.length < 2 ^ w)
    (hG_val : G.IsValid)
    (hvG : ∀ v ∈ G.V, v < vCap)
    (hu0 : u0 ∈ G.V)
    (hWalk : G.IsWalk u0 vEnd Q₀)
    (hNd : (G.walkVertices u0 Q₀).Nodup)
    (hregs4 : regsPre 4 = regsPre 4)
    (hr6 : regsPre 6 = vStampPtr)
    : Triple w p
        (Pass3LoopInv vCap vStampPtr stampVal gen0 nodeBase outWalkPtr G vEnd Q₀
          memPre regsPre Q₀)
        (.loop (.reg 18)
          (.assign 15 (.load (.reg 18)) ;;
           .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
           .assign 14 (.load (.bin .add (.reg 18) (.const 1))) ;;
           .store (.reg 21) (.reg 14) ;;
           .assign 14 (.load (.bin .add (.reg 18) (.const 2))) ;;
           .store (.bin .add (.reg 21) (.const 1)) (.reg 14) ;;
           .assign 21 (.bin .add (.reg 21) (.const 2)) ;;
           .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
           .assign 18 (.load (.bin .add (.reg 18) (.const 3)))))
        (normalPost (Pass3LoopInv vCap vStampPtr stampVal gen0 nodeBase outWalkPtr
          G vEnd Q₀ memPre regsPre []))
        (fun _ => 49 * Q₀.length + 2) := by
  let _ := hu0
  let _ := hWalk
  let _ := hNd
  let _ := hregs4
  let Inv := Pass3LoopInv vCap vStampPtr stampVal gen0 nodeBase outWalkPtr G vEnd Q₀ memPre regsPre
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hloop : Triple w p (Inv Q₀)
      (.loop (.reg 18)
        (.assign 15 (.load (.reg 18)) ;;
         .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
         .assign 14 (.load (.bin .add (.reg 18) (.const 1))) ;;
         .store (.reg 21) (.reg 14) ;;
         .assign 14 (.load (.bin .add (.reg 18) (.const 2))) ;;
         .store (.bin .add (.reg 21) (.const 1)) (.reg 14) ;;
         .assign 21 (.bin .add (.reg 21) (.const 2)) ;;
         .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
         .assign 18 (.load (.bin .add (.reg 18) (.const 3)))))
      (normalPost (Inv []))
      (fun _ => (Q₀.map (fun _ => 47)).sum + Q₀.length * ((Expr.reg 18).size + 1) +
        (Expr.reg 18).size + 1) := by
    refine Triple.loop_list (Inv := Inv)
      (Q := normalPost (Inv []))
      (fun _ => 47) ?_ ?_ Q₀
    · intro st hInv
      rcases hInv with ⟨idx, cur, hlen, hdrop, hcurV, hWk, hNd', hSt, hV, hr21, hr22, hr23,
        hregs, hentries, hfr⟩
      have hhead0 : st.regs 18 = 0 := hSt
      refine ⟨by simp [Expr.eval, hhead0], ?_⟩
      exact ⟨idx, cur, hlen, hdrop, hcurV, hWk, hNd', hSt, hV, hr21, hr22, hr23,
        hregs, hentries, hfr⟩
    · intro x xs st hInv
      rcases hInv with ⟨idx, cur, hlen, hdrop, hcurV, hWk, hNd', hSt, hV, hr21, hr22, hr23,
        hregs, hentries, hfr⟩
      dsimp only [StackListIn] at hSt
      rcases hSt with ⟨hlo, hhi, hm0, hm1, hm2, hSt_rest⟩
      set head := st.regs 18
      have hhead_ne0 : head ≠ 0 := by omega
      have hhead_w : head < 2 ^ w := by omega
      have hhead3_w : head + 3 < 2 ^ w := by omega
      have hidx_lt : idx < Q₀.length := by simp at hlen; omega
      have ⟨hx_eq, hdrop_next⟩ := drop_eq_getElem_cons_of_eq hidx_lt hdrop.symm
      have hcur_lt : cur < vCap := hvG cur hcurV
      have hvst_cur_w : vStampPtr + cur < 2 ^ w := by omega
      have hr6_st : st.regs 6 = vStampPtr := hregs 6 (Or.inl (by omega)) |>.trans hr6
      have hcur_notin : cur ∉ G.walkVertices (G.dst x) xs := by
        change (cur :: G.walkVertices (G.dst x) xs).Nodup at hNd'
        exact (List.nodup_cons.mp hNd').1
      have hNd_next : (G.walkVertices (G.dst x) xs).Nodup := by
        change (cur :: G.walkVertices (G.dst x) xs).Nodup at hNd'
        exact (List.nodup_cons.mp hNd').2
      cases hWk with
      | cons he _ hWk_next =>
        have hdst_V : G.dst x ∈ G.V := isWalk_mem_dst_V hG_val he
        refine ⟨head, Expr.eval_reg_of_eq rfl, hhead_ne0, fun s ω hs => ?_⟩
        subst hs
        refine runs_start_le ?_
        refine runs_seq_assign_le (v := cur)
          (Expr.eval_load_of_eq (x := head) (Expr.eval_reg_of_eq rfl) hm0) ?_
        have hw0 : 0 < 2 ^ w := by omega
        refine runs_seq_store_le (x := vStampPtr + cur) (v := 0)
          (by simp [Expr.eval, BinOp.eval, hr6_st, hvst_cur_w])
          (Expr.eval_const hw0) ?_
        have hvst_cur_lt : vStampPtr + cur < nodeBase := hvst_disj cur hcur_lt
        refine runs_seq_assign_le (v := x.1)
          (Expr.eval_load_of_eq (x := head + 1)
            (by simp [Expr.eval, BinOp.eval, head, hw1, show head + 1 < 2 ^ w by omega])
            (by dsimp only; rw [Function.update_of_ne (by omega)]; exact hm1)) ?_
        have hw_pair_w : outWalkPtr + 1 + 2 * idx + 1 < 2 ^ w := by omega
        refine runs_seq_store_le (x := outWalkPtr + 1 + 2 * idx) (v := x.1)
          (by simp [Expr.eval, hr21]) (Expr.eval_reg_of_eq (by simp)) ?_
        refine runs_seq_assign_le (v := if x.2 then 1 else 0)
          (Expr.eval_load_of_eq (x := head + 2)
            (by simp [Expr.eval, BinOp.eval, head, hw2, show head + 2 < 2 ^ w by omega])
            (by dsimp only
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact hm2)) ?_
        refine runs_seq_store_le (x := outWalkPtr + 1 + 2 * idx + 1)
          (v := if x.2 then 1 else 0)
          (by simp [Expr.eval, BinOp.eval, hr21, hw1, hw_pair_w])
          (Expr.eval_reg_of_eq (by simp)) ?_
        refine runs_seq_assign_le (v := outWalkPtr + 1 + 2 * (idx + 1))
          (by simp [Expr.eval, BinOp.eval, hr21, hw2,
            show outWalkPtr + 1 + 2 * idx + 2 < 2 ^ w by omega,
            show outWalkPtr + 1 + 2 * (idx + 1) = outWalkPtr + 1 + 2 * idx + 2 by omega]) ?_
        refine runs_seq_assign_le (v := idx + 1)
          (by simp [Expr.eval, BinOp.eval, hr23, hw1, show idx + 1 < 2 ^ w by omega]) ?_
        set mem1 := Function.update
          (Function.update (Function.update s.mem (vStampPtr + cur) 0)
            (outWalkPtr + 1 + 2 * idx) x.1)
          (outWalkPtr + 1 + 2 * idx + 1) (if x.2 then 1 else 0)
        have hmem1_next : mem1 (head + 3) = s.mem (head + 3) := by
          dsimp only [mem1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega)]
        refine runs_assign_le
          (Expr.eval_load_of_eq (x := head + 3)
            (by simp [Expr.eval, BinOp.eval, head, hw3, hhead3_w]) hmem1_next) ?_ ?_
        · refine ⟨idx + 1, G.dst x, by simp at hlen ⊢; omega, hdrop_next.symm, hdst_V,
            hWk_next, hNd_next, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact hSt_rest.of_agree fun a ha1 ha2 => by
              dsimp only [mem1]
              have hvac : a ≠ vStampPtr + cur := by have := hvst_disj cur hcur_lt; omega
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne hvac]
          · intro v hv
            have hnv1 : vStampPtr + v ≠ outWalkPtr + 1 + 2 * idx := by
              have := hvst_disj v hv; omega
            have hnv2 : vStampPtr + v ≠ outWalkPtr + 1 + 2 * idx + 1 := by
              have := hvst_disj v hv; omega
            dsimp only [mem1]
            rw [Function.update_of_ne hnv2, Function.update_of_ne hnv1]
            constructor
            · intro hmemv
              have hv_ne_cur : v ≠ cur := fun heq => hcur_notin (heq ▸ hmemv)
              rw [Function.update_of_ne (by omega)]
              have hmemv' : v ∈ G.walkVertices cur (x :: xs) := by
                change v ∈ cur :: G.walkVertices (G.dst x) xs
                exact List.mem_cons_of_mem cur hmemv
              exact (hV v hv).1 hmemv'
            · intro hnotv
              by_cases hvc : v = cur
              · subst hvc; rw [Function.update_self]; exact Nat.zero_le _
              · rw [Function.update_of_ne (by omega)]
                have hnotv' : v ∉ G.walkVertices cur (x :: xs) := by
                  change v ∉ cur :: G.walkVertices (G.dst x) xs
                  simp [hvc, hnotv]
                exact (hV v hv).2 hnotv'
          · simp
          · simp [hr22]
          · simp
          · intro r hrr
            have hrn18 : r ≠ 18 := by rcases hrr with h | rfl | rfl <;> omega
            have hrn23 : r ≠ 23 := by rcases hrr with h | rfl | rfl <;> omega
            have hrn21 : r ≠ 21 := by rcases hrr with h | rfl | rfl <;> omega
            have hrn14 : r ≠ 14 := by rcases hrr with h | rfl | rfl <;> omega
            have hrn15 : r ≠ 15 := by rcases hrr with h | rfl | rfl <;> omega
            simp [hrn18, hrn23, hrn21, hrn14, hrn15]
            exact hregs r hrr
          · intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt | rfl
            · obtain ⟨hjQ, hm_e, hm_d⟩ := hentries j hj_lt
              refine ⟨hjQ, ?_, ?_⟩
              · dsimp only [mem1]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
                exact hm_e
              · dsimp only [mem1]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
                exact hm_d
            · refine ⟨hidx_lt, ?_, ?_⟩
              · dsimp only [mem1]
                rw [Function.update_of_ne (by omega), Function.update_self, hx_eq]
              · dsimp only [mem1]
                rw [Function.update_self, hx_eq]
          · intro addr ha_vst ha_rng
            dsimp only [mem1]
            have ha_cur : addr ≠ vStampPtr + cur := ha_vst cur hcur_lt
            have ha_e : addr ≠ outWalkPtr + 1 + 2 * idx := by
              rcases ha_rng with h | h <;> omega
            have ha_d : addr ≠ outWalkPtr + 1 + 2 * idx + 1 := by
              rcases ha_rng with h | h <;> omega
            rw [Function.update_of_ne ha_d, Function.update_of_ne ha_e,
              Function.update_of_ne ha_cur]
            exact hfr addr ha_vst (by rcases ha_rng with h | h <;> [left; right] <;> omega)
        · dsimp only [Expr.size]
          omega
  refine hloop.conseq (fun _ h => h) (fun o st h => by cases o <;> exact h) ?_
  intro st _
  have hsum : (Q₀.map (fun _ : ℕ × Bool => 47)).sum = 47 * Q₀.length := by
    suffices ∀ L : List (ℕ × Bool), (L.map (fun _ => 47)).sum = 47 * L.length from this Q₀
    intro L
    induction L with
    | nil => simp
    | cons _ _ ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
  rw [hsum]
  dsimp only [Expr.size]
  omega

/-- Complete Pass 3 post-Pass 2 verification: copies stack `Q₀` to compact `MWalkAt` format at
`outWalkPtr = st.regs 17`, clears all vertex stamps (including `vEnd`), writes `mEmbPtr[e] :=
outWalkPtr`, and advances `r5 := outWalkPtr + 1 + 2 * Q₀.length`. -/
public theorem shortcut_pass3_triple {w vCap vStampPtr stampVal gen0 nodeBase outWalkPtr
    mEmbPtr eCapEmb e vEnd u0 : ℕ} {G : MGraph} {Q₀ : List (ℕ × Bool)} {p : Program}
    {mem0 regs0 : ℕ → ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (hnode1 : 1 ≤ nodeBase)
    (hvst_disj : ∀ v < vCap, vStampPtr + v < nodeBase)
    (hvst_w : vStampPtr + vCap < 2 ^ w)
    (_hnode_le : nodeBase ≤ outWalkPtr)
    (hout_w : outWalkPtr + 1 + 2 * Q₀.length < 2 ^ w)
    (hm_w : mEmbPtr + eCapEmb < 2 ^ w)
    (he_lt : e < eCapEmb)
    (hm_vst : ∀ v < vCap, mEmbPtr + e ≠ vStampPtr + v)
    (hm_out : mEmbPtr + e < outWalkPtr ∨ outWalkPtr + 1 + 2 * Q₀.length ≤ mEmbPtr + e)
    (hG_val : G.IsValid)
    (hvG : ∀ v ∈ G.V, v < vCap)
    (hu0 : u0 ∈ G.V)
    (hvEnd : vEnd ∈ G.V)
    (hWalk : G.IsWalk u0 vEnd Q₀)
    (hNd : (G.walkVertices u0 Q₀).Nodup)
    (hSt : StackListIn G nodeBase outWalkPtr mem0 (regs0 18) u0 Q₀)
    (hV : VStampInv mem0 vStampPtr vCap stampVal gen0 (G.walkVertices u0 Q₀))
    (hr4 : regs0 4 = mEmbPtr) (hr6 : regs0 6 = vStampPtr)
    (hr9 : regs0 9 = e) (hr17 : regs0 17 = outWalkPtr) (hr19 : regs0 19 = vEnd) :
    Triple w p
      (fun st => st.mem = mem0 ∧ st.regs = regs0)
      (.assign 22 (.reg 17) ;;
       .assign 21 (.bin .add (.reg 17) (.const 1)) ;;
       .assign 23 (.const 0) ;;
       .loop (.reg 18)
         (.assign 15 (.load (.reg 18)) ;;
          .store (.bin .add (.reg 6) (.reg 15)) (.const 0) ;;
          .assign 14 (.load (.bin .add (.reg 18) (.const 1))) ;;
          .store (.reg 21) (.reg 14) ;;
          .assign 14 (.load (.bin .add (.reg 18) (.const 2))) ;;
          .store (.bin .add (.reg 21) (.const 1)) (.reg 14) ;;
          .assign 21 (.bin .add (.reg 21) (.const 2)) ;;
          .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
          .assign 18 (.load (.bin .add (.reg 18) (.const 3)))) ;;
       .store (.bin .add (.reg 6) (.reg 19)) (.const 0) ;;
       .store (.reg 22) (.reg 23) ;;
       .store (.bin .add (.reg 4) (.reg 9)) (.reg 22) ;;
       .assign 5 (.reg 21))
      (normalPost fun st' =>
        st'.regs 5 = outWalkPtr + 1 + 2 * Q₀.length ∧
        (∀ r, (r ≤ 4 ∨ (6 ≤ r ∧ r ≤ 8) ∨ r = 16) → st'.regs r = regs0 r) ∧
        st'.mem (mEmbPtr + e) = outWalkPtr ∧
        MWalkAt st'.mem outWalkPtr Q₀ ∧
        (∀ v < vCap, st'.mem (vStampPtr + v) ≤ gen0) ∧
        ∀ addr, (∀ v < vCap, addr ≠ vStampPtr + v) → addr ≠ mEmbPtr + e →
          (addr < outWalkPtr ∨ outWalkPtr + 1 + 2 * Q₀.length ≤ addr) →
          st'.mem addr = mem0 addr)
      (fun _ => 50 * Q₀.length + 35) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  intro st ω ⟨hm0, hreg0⟩
  subst hm0
  subst hreg0
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := outWalkPtr) (Expr.eval_reg_of_eq hr17) ?_
  refine runs_seq_assign_le (v := outWalkPtr + 1)
    (by simp [Expr.eval, BinOp.eval, hr17, hw1, show outWalkPtr + 1 < 2 ^ w by omega]) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const hw0) ?_
  let r0 := Function.update
    (Function.update (Function.update st.regs 22 outWalkPtr) 21 (outWalkPtr + 1)) 23 0
  let st0 : State := { st with regs := r0 }
  have hInv0 : Pass3LoopInv vCap vStampPtr stampVal gen0 nodeBase outWalkPtr G vEnd Q₀
      st.mem st.regs Q₀ st0 := by
    refine ⟨0, u0, by simp, rfl, hu0, hWalk, hNd, ?_, hV, by simp [st0, r0], ?_, by simp [st0, r0],
      ?_, fun j hj => by omega, fun addr _ _ => rfl⟩
    · simp only [st0, r0, Function.update_of_ne (by omega : (18 : ℕ) ≠ 23),
        Function.update_of_ne (by omega : (18 : ℕ) ≠ 21),
        Function.update_of_ne (by omega : (18 : ℕ) ≠ 22)]
      exact hSt
    · simp [st0, r0]
    · intro r hrr
      have hr23 : r ≠ 23 := by rcases hrr with h | rfl | rfl <;> omega
      have hr21 : r ≠ 21 := by rcases hrr with h | rfl | rfl <;> omega
      have hr22 : r ≠ 22 := by rcases hrr with h | rfl | rfl <;> omega
      simp [st0, r0, hr23, hr21, hr22]
  refine runs_seq_triple_le (Q₁ := Pass3LoopInv vCap vStampPtr stampVal gen0 nodeBase outWalkPtr
      G vEnd Q₀ st.mem st.regs [])
    (shortcut_pass3_loop_triple (p := p) (stampVal := stampVal) (gen0 := gen0) (memPre := st.mem)
      hw16 hnode1 hvst_disj hvst_w _hnode_le hout_w hG_val hvG hu0 hWalk hNd rfl hr6)
    hInv0 fun stL hqL => ?_
  rcases hqL with ⟨idx, cur, hlen, hdrop, hcurV, hWk, _, hStL, hVL, hr21L, hr22L, hr23L,
    hregsL, hentriesL, hfrL⟩
  have hidx_eq : idx = Q₀.length := by simp at hlen; exact hlen
  subst hidx_eq
  have hcur_eq : cur = vEnd := by
    cases hWk with
    | nil => rfl
  subst hcur_eq
  have hvEnd_lt : cur < vCap := hvG cur hvEnd
  have hvst_e_w : vStampPtr + cur < 2 ^ w := by omega
  have hr6L : stL.regs 6 = vStampPtr := hregsL 6 (Or.inl (by omega)) |>.trans hr6
  have hr19L : stL.regs 19 = cur := hregsL 19 (Or.inr (Or.inr rfl)) |>.trans hr19
  refine runs_seq_store_le (x := vStampPtr + cur) (v := 0)
    (by simp [Expr.eval, BinOp.eval, hr6L, hr19L, hvst_e_w])
    (Expr.eval_const hw0) ?_
  have hout_lt_w : outWalkPtr < 2 ^ w := by omega
  have hQ0_w : Q₀.length < 2 ^ w := by omega
  refine runs_seq_store_le (x := outWalkPtr) (v := Q₀.length)
    (by simp [Expr.eval, hr22L]) (Expr.eval_reg_of_eq hr23L) ?_
  have hm_e_w : mEmbPtr + e < 2 ^ w := by omega
  have hr4L : stL.regs 4 = mEmbPtr := hregsL 4 (Or.inl (by omega)) |>.trans hr4
  have hr9L : stL.regs 9 = e := hregsL 9 (Or.inl (by omega)) |>.trans hr9
  refine runs_seq_store_le (x := mEmbPtr + e) (v := outWalkPtr)
    (by simp [Expr.eval, BinOp.eval, hr4L, hr9L, hm_e_w])
    (Expr.eval_reg_of_eq hr22L) ?_
  set memF := Function.update
    (Function.update (Function.update stL.mem (vStampPtr + cur) 0) outWalkPtr Q₀.length)
    (mEmbPtr + e) outWalkPtr
  refine runs_assign_le (Expr.eval_reg_of_eq hr21L) ?_ ?_
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro r hrr
      have hrn5 : r ≠ 5 := by rcases hrr with h | h | rfl <;> omega
      simp [hrn5]
      have hrr' : r ≤ 11 ∨ r = 16 ∨ r = 19 := by
        rcases hrr with h | h | rfl
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl rfl)
      exact hregsL r hrr'
    · dsimp only [memF]; rw [Function.update_self]
    · refine mWalkAt_of_entries ?_ ?_ ?_
      · dsimp only [memF]
        have hne_m : outWalkPtr ≠ mEmbPtr + e := by
          rcases hm_out with h | h <;> omega
        rw [Function.update_of_ne hne_m, Function.update_self]
      · intro j hj
        obtain ⟨_, hm_e, _⟩ := hentriesL j hj
        dsimp only [memF]
        have h1e : outWalkPtr + 1 + 2 * j ≠ mEmbPtr + e := by rcases hm_out with h | h <;> omega
        have h2e : outWalkPtr + 1 + 2 * j ≠ vStampPtr + cur := by
          have := hvst_disj cur hvEnd_lt; omega
        rw [Function.update_of_ne h1e, Function.update_of_ne (by omega),
          Function.update_of_ne h2e, hm_e]
      · intro j hj
        obtain ⟨_, _, hm_d⟩ := hentriesL j hj
        dsimp only [memF]
        have h1d : outWalkPtr + 1 + 2 * j + 1 ≠ mEmbPtr + e := by rcases hm_out with h | h <;> omega
        have h2d : outWalkPtr + 1 + 2 * j + 1 ≠ vStampPtr + cur := by
          have := hvst_disj cur hvEnd_lt; omega
        rw [Function.update_of_ne h1d, Function.update_of_ne (by omega),
          Function.update_of_ne h2d, hm_d]
    · intro v hv
      dsimp only [memF]
      have hnv_m : vStampPtr + v ≠ mEmbPtr + e := (hm_vst v hv).symm
      have hnv_out : vStampPtr + v ≠ outWalkPtr := by
        have := hvst_disj v hv; omega
      rw [Function.update_of_ne hnv_m, Function.update_of_ne hnv_out]
      by_cases hvc : v = cur
      · subst hvc; rw [Function.update_self]; exact Nat.zero_le _
      · rw [Function.update_of_ne (by omega)]
        have hnotv : v ∉ G.walkVertices cur [] := by
          simpa [MGraph.walkVertices] using hvc
        exact (hVL v hv).2 hnotv
    · intro addr ha_vst ha_m ha_rng
      dsimp only [memF]
      have ha_cur : addr ≠ vStampPtr + cur := ha_vst cur hvEnd_lt
      have ha_out : addr ≠ outWalkPtr := by rcases ha_rng with h | h <;> omega
      rw [Function.update_of_ne ha_m, Function.update_of_ne ha_out, Function.update_of_ne ha_cur]
      exact hfrL addr ha_vst (by rcases ha_rng with h | h <;> [left; right] <;> omega)
  · dsimp only [Expr.size]
    omega

end

end MinCostFlow.DynSpanner.Program
