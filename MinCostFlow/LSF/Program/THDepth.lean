module

public import MinCostFlow.LSF.Program.THBstLoop

/-!
# The parent and depth pass

`thDepthProc` first stores `thPar r = r` and `dTH r = 0` for the root `r = Q[0]`. Then it walks
the top-down order `Q` over the positions `1, …, n - 1`. At `x = Q[j]` with top `t` and
`pos = dep x - dep t` it runs the search loop `thBst_loop` on the segment
`[off t + 1, off t + cnt t)` of the chain array for position `pos - 1`, and then stores, with no
branch,

* `thPar x = par x` and `dTH x = dTH (par x) + 1` when `pos = 0`,
* `thPar x = R.1` and `dTH x = dTH t + 1 + R.2` otherwise, where `R` is the search result.

The parent, and the top when `pos > 0`, come before `x` in `Q`, so their depths are already
stored. The cost is `O(n log n)`.

The contract asks for a function `D` that follows the same rule and is bounded by `B`. It is used
only to bound the stored numbers during the run. The driver takes the depths in `T_H` for `D`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

/-- The search result at `x`. -/
def thR (top dep cnt off arr : ℕ → ℕ) (x : ℕ) : ℕ × ℕ :=
  bstIdx (top x) arr (off (top x) + 1) (cnt (top x) - 1) (dep x - dep (top x) - 1)

/-- The depth rule at `x`. -/
def DepthRule (par top dep cnt off arr D : ℕ → ℕ) (x : ℕ) : Prop :=
  D x = if dep x - dep (top x) = 0 then D (par x) + 1 else D (top x) + 1 + (thR top dep cnt off arr x).2

/-- The parent rule at `x`. -/
def ParRule (par top dep cnt off arr thPar : ℕ → ℕ) (x : ℕ) : Prop :=
  thPar x = if dep x - dep (top x) = 0 then par x else (thR top dep cnt off arr x).1

/-- The facts the pass needs about its input arrays. -/
structure THDepthIn (n r : ℕ) (Q : List ℕ) (par top dep cnt off arr : ℕ → ℕ) (B : ℕ)
    (D : ℕ → ℕ) : Prop where
  top_lt : ∀ x < n, top x < n
  dep_lt : ∀ x < n, dep x < n
  pos_lt : ∀ x < n, dep x - dep (top x) < cnt (top x)
  blk : ∀ x < n, off (top x) + cnt (top x) ≤ n
  arr_lt : ∀ s < n, arr s < n
  order : ∀ x < n, x ≠ r → dep x - dep (top x) ≠ 0 → top x ∈ Q.take (Q.idxOf x)
  D_r : D r = 0
  D_le : ∀ x < n, D x ≤ B
  D_rule : ∀ x < n, x ≠ r → DepthRule par top dep cnt off arr D x

/-- The search only reads the segment. -/
lemma bstIdx_congr {A A' : ℕ → ℕ} :
    ∀ len above lo j, (∀ k < len, A (lo + k) = A' (lo + k)) →
      bstIdx above A lo len j = bstIdx above A' lo len j := by
  intro len
  induction len using Nat.strong_induction_on with
  | h len ih =>
    intro above lo j hA
    rw [bstIdx.eq_def above A lo len j, bstIdx.eq_def above A' lo len j]
    by_cases h0 : len = 0
    · simp [h0]
    · have hm : len / 2 < len := Nat.div_lt_self (by omega) (by decide)
      have hmid : A (lo + len / 2) = A' (lo + len / 2) := hA _ hm
      simp only [h0, dite_false]
      split_ifs with h1 h2
      · rfl
      · rw [hmid, ih (len / 2) hm (A' (lo + len / 2)) lo j (fun k hk => hA k (by omega))]
      · rw [hmid, ih (len - len / 2 - 1) (by omega) (A' (lo + len / 2)) (lo + len / 2 + 1)
          (j - len / 2 - 1) (fun k hk => by
            have := hA (len / 2 + 1 + k) (by omega)
            rwa [show lo + (len / 2 + 1 + k) = lo + len / 2 + 1 + k by omega] at this)]

/-- One step (register `10` is `j`). Registers: `11 = x`, `12 = t`, `13 = pos`, `14`–`19`, `22`,
`23` for the search, `20 = [pos = 0]`, `21 = par x`. -/
def thDepthBody : Stmt :=
  .assign 11 (.load (.bin .add (.reg 1) (.reg 10))) ;;
  .assign 12 (.load (.bin .add (.reg 3) (.reg 11))) ;;
  .assign 13 (.bin .sub (.load (.bin .add (.reg 4) (.reg 11))) (.load (.bin .add (.reg 4) (.reg 12)))) ;;
  .assign 14 (.reg 12) ;;
  .assign 15 (.bin .add (.load (.bin .add (.reg 6) (.reg 12))) (.const 1)) ;;
  .assign 16 (.bin .sub (.load (.bin .add (.reg 5) (.reg 12))) (.const 1)) ;;
  .assign 17 (.bin .sub (.reg 13) (.const 1)) ;;
  .assign 18 (.const 0) ;;
  .assign 19 (.bin .sub (.const 1) (.bin .eq (.reg 17) (.bin .div (.reg 16) (.const 2)))) ;;
  .loop (.reg 19) thBstBody ;;
  .assign 20 (.bin .eq (.reg 13) (.const 0)) ;;
  .assign 21 (.load (.bin .add (.reg 2) (.reg 11))) ;;
  .store (.bin .add (.reg 8) (.reg 11))
    (.bin .add (.bin .mul (.reg 20) (.reg 21)) (.bin .mul (.bin .sub (.const 1) (.reg 20)) (.reg 14))) ;;
  .store (.bin .add (.reg 9) (.reg 11))
    (.bin .add (.bin .mul (.reg 20) (.bin .add (.load (.bin .add (.reg 9) (.reg 21))) (.const 1)))
      (.bin .mul (.bin .sub (.const 1) (.reg 20))
        (.bin .add (.bin .add (.load (.bin .add (.reg 9) (.reg 12))) (.const 1)) (.reg 18))))

/-- Args: `[n, qPtr, parPtr, topPtr, depPtr, cntPtr, offPtr, arrPtr, thParPtr, dthPtr]`. -/
def thDepthProc : Stmt :=
  .assign 11 (.load (.reg 1)) ;;
  .store (.bin .add (.reg 8) (.reg 11)) (.reg 11) ;;
  .store (.bin .add (.reg 9) (.reg 11)) (.const 0) ;;
  forRange 10 (.const 1) (.reg 0) thDepthBody ;;
  .ret (.const 0)

lemma thDepthProc_noRand : thDepthProc.NoRand := by
  simp [thDepthProc, thDepthBody, thBstBody, forRange, forUp, Stmt.NoRand]

/-- The contract of `thDepthProc`. -/
def thDepthContract (w : ℕ) : Contract where
  pre args mem := ∃ (n qPtr parPtr topPtr depPtr cntPtr offPtr arrPtr thParPtr dthPtr r B : ℕ)
      (Q : List ℕ) (D : ℕ → ℕ),
    args = [n, qPtr, parPtr, topPtr, depPtr, cntPtr, offPtr, arrPtr, thParPtr, dthPtr] ∧ 0 < n ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    qPtr + n ≤ thParPtr ∧ parPtr + n ≤ thParPtr ∧ topPtr + n ≤ thParPtr ∧
    depPtr + n ≤ thParPtr ∧ cntPtr + n ≤ thParPtr ∧ offPtr + n ≤ thParPtr ∧
    arrPtr + n ≤ thParPtr ∧ thParPtr + n ≤ dthPtr ∧ dthPtr + n < 2 ^ w ∧ B + 2 * n + 8 < 2 ^ w ∧
    (∀ y < n, mem (dthPtr + y) ≤ B) ∧
    THDepthIn n r Q (fun x => mem (parPtr + x)) (fun x => mem (topPtr + x))
      (fun x => mem (depPtr + x)) (fun x => mem (cntPtr + x)) (fun x => mem (offPtr + x))
      (fun x => mem (arrPtr + x)) B D
  post args mem ret mem' := ∃ (n qPtr parPtr topPtr depPtr cntPtr offPtr arrPtr thParPtr dthPtr : ℕ),
    args = [n, qPtr, parPtr, topPtr, depPtr, cntPtr, offPtr, arrPtr, thParPtr, dthPtr] ∧ ret = 0 ∧
    (∀ a, a < thParPtr ∨ dthPtr + n ≤ a → mem' a = mem a) ∧
    ∀ Q r, TopDownOrder n r (fun x => mem (parPtr + x)) Q → ListAt mem qPtr Q →
      mem' (thParPtr + r) = r ∧ mem' (dthPtr + r) = 0 ∧
      ∀ x < n, x ≠ r →
        ParRule (fun x => mem (parPtr + x)) (fun x => mem (topPtr + x))
          (fun x => mem (depPtr + x)) (fun x => mem (cntPtr + x)) (fun x => mem (offPtr + x))
          (fun x => mem (arrPtr + x)) (fun x => mem' (thParPtr + x)) x ∧
        DepthRule (fun x => mem (parPtr + x)) (fun x => mem (topPtr + x))
          (fun x => mem (depPtr + x)) (fun x => mem (cntPtr + x)) (fun x => mem (offPtr + x))
          (fun x => mem (arrPtr + x)) (fun x => mem' (dthPtr + x)) x
  cost args _ := args.getD 0 0 * (bstLoopCost (args.getD 0 0) + 200) + 60

private lemma sel3 {c a a' : ℕ} (P : Prop) [Decidable P] (hc : c = if P then 1 else 0) :
    c * a + (1 - c) * a' = if P then a else a' := by
  subst hc; split_ifs <;> simp

private lemma bstLoopCost_mono {a b : ℕ} (h : a ≤ b) : bstLoopCost a ≤ bstLoopCost b := by
  unfold bstLoopCost
  have := Nat.log_mono_right (b := 2) (show 2 * a ≤ 2 * b by omega)
  omega

theorem thDepth_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some thDepthProc) :
    MeetsContract w p b (thDepthContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qPtr, parPtr, topPtr, depPtr, cntPtr, offPtr, arrPtr, thParPtr, dthPtr, r, B, Q, D,
    rfl, hn, hQ, hQat, hqa, hpa, hta, hda, hca, hoa, haa, htp, hdt, hB, hdth0, hIn⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  set args := [n, qPtr, parPtr, topPtr, depPtr, cntPtr, offPtr, arrPtr, thParPtr, dthPtr]
    with hargs
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set top : ℕ → ℕ := fun x => mem (topPtr + x) with htop
  set dep : ℕ → ℕ := fun x => mem (depPtr + x) with hdep
  set cnt : ℕ → ℕ := fun x => mem (cntPtr + x) with hcnt
  set off : ℕ → ℕ := fun x => mem (offPtr + x) with hoff
  set arr : ℕ → ℕ := fun x => mem (arrPtr + x) with harr
  have hnw : n < 2 ^ w := by omega
  have hlenQ : Q.length = n := hQ.len
  have hlen0 : 0 < Q.length := by omega
  have hrQ : r = Q[0] := (hQ.head_eq hn).symm
  have hrn : r < n := hQ.lt r (by rw [hrQ]; exact List.getElem_mem _)
  let Inv : ℕ → State → Prop := fun j st =>
    (∀ i < 10, st.regs i = args.getD i 0) ∧ st.regs 10 = j ∧
    (∀ a, a < thParPtr ∨ dthPtr + n ≤ a → st.mem a = mem a) ∧
    (∀ y < n, st.mem (dthPtr + y) ≤ B) ∧ st.mem (thParPtr + r) = r ∧ st.mem (dthPtr + r) = 0 ∧
    ∀ y ∈ Q.take j, y ≠ r → st.mem (dthPtr + y) = D y ∧
      ParRule par top dep cnt off arr (fun x => st.mem (thParPtr + x)) y
  have hloop : ∀ st₀ : State, Inv 1 {st₀ with regs := Function.update st₀.regs 10 1} →
      Triple w p (fun st => st = st₀)
      (forRange 10 (.const 1) (.reg 0) thDepthBody) (normalPost (Inv n))
      (fun _ => (n - 1) * ((bstLoopCost n + 180) + (Expr.reg 0).size + 8) +
        ((Expr.const 1).size + (Expr.reg 0).size + 5)) := by
    intro st₀ hI1
    refine Triple.forRange_const (bstLoopCost n + 180) 1 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl; exact ⟨by eval_expr, hI1⟩
    · intro i st _ _ hI; exact hI.2.1
    · intro i st _ _ hI
      have r0 : st.regs 0 = n := hI.1 0 (by omega)
      eval_expr
    · intro j hj1 hjn st ω' hI
      obtain ⟨hR, h10, hfr, hdle, hpr, hdr, hdone⟩ := hI
      have r1 : st.regs 1 = qPtr := hR 1 (by omega)
      have r2 : st.regs 2 = parPtr := hR 2 (by omega)
      have r3 : st.regs 3 = topPtr := hR 3 (by omega)
      have r4 : st.regs 4 = depPtr := hR 4 (by omega)
      have r5 : st.regs 5 = cntPtr := hR 5 (by omega)
      have r6 : st.regs 6 = offPtr := hR 6 (by omega)
      have r7 : st.regs 7 = arrPtr := hR 7 (by omega)
      have r8 : st.regs 8 = thParPtr := hR 8 (by omega)
      have r9 : st.regs 9 = dthPtr := hR 9 (by omega)
      have hjQ : j < Q.length := by omega
      set x := Q[j] with hx
      have hxn : x < n := hQ.lt x (List.getElem_mem _)
      have hxr : x ≠ r := by
        intro h
        rw [hrQ, hx] at h
        have := (hQ.nodup.getElem_inj_iff).mp h
        omega
      have hidx : Q.idxOf x = j := hQ.nodup.idxOf_getElem j hjQ
      have hxt : x ∉ Q.take j := hQ.not_mem_take hjQ
      have hpQ := hQ.after j hjQ hxr
      have hpn : par x < n := hQ.lt _ (List.mem_of_mem_take hpQ)
      set t := top x with ht
      have htn : t < n := hIn.top_lt x hxn
      have hdxn : dep x < n := hIn.dep_lt x hxn
      have hdtn : dep t < n := hIn.dep_lt t htn
      have hposlt : dep x - dep t < cnt t := hIn.pos_lt x hxn
      have hblk : off t + cnt t ≤ n := hIn.blk x hxn
      set ps := dep x - dep t with hps
      have hmx : st.mem (qPtr + j) = x := by
        rw [hfr _ (Or.inl (by omega))]; exact hQat _ hjQ
      have hmt : st.mem (topPtr + x) = t := hfr _ (Or.inl (by omega))
      have hmdx : st.mem (depPtr + x) = dep x := hfr _ (Or.inl (by omega))
      have hmdt : st.mem (depPtr + t) = dep t := by
        have : depPtr + t < thParPtr := by omega
        exact hfr _ (Or.inl this)
      have hmo : st.mem (offPtr + t) = off t := by
        have : offPtr + t < thParPtr := by omega
        exact hfr _ (Or.inl this)
      have hmc : st.mem (cntPtr + t) = cnt t := by
        have : cntPtr + t < thParPtr := by omega
        exact hfr _ (Or.inl this)
      have hmp : st.mem (parPtr + x) = par x := hfr _ (Or.inl (by omega))
      -- the search
      set lo0 := off t + 1 with hlo0
      set len0 := cnt t - 1 with hlen0'
      set jj0 := ps - 1 with hjj0
      have hRdef : thR top dep cnt off arr x = bstIdx t arr lo0 len0 jj0 := rfl
      set Rx := thR top dep cnt off arr x with hRx
      have hjl0 : jj0 < len0 ∨ (len0 = 0 ∧ jj0 = 0) := by omega
      refine runs_start_le ?_
      unfold thDepthBody
      refine runs_seq_assign_le (v := x) (by rw [← hmx]; eval_expr) ?_
      refine runs_seq_assign_le (v := t) (by rw [← hmt]; eval_expr) ?_
      refine runs_seq_assign_le (v := ps) (by
        rw [hps, ← hmdx, ← hmdt]
        have : st.mem (depPtr + x) < 2 ^ w := by rw [hmdx]; omega
        have : st.mem (depPtr + t) < 2 ^ w := by rw [hmdt]; omega
        eval_expr) ?_
      refine runs_seq_assign_le (v := t) (by eval_expr) ?_
      refine runs_seq_assign_le (v := lo0) (by
        rw [hlo0, ← hmo]
        have : st.mem (offPtr + t) + 1 < 2 ^ w := by rw [hmo]; omega
        eval_expr) ?_
      refine runs_seq_assign_le (v := len0) (by
        rw [hlen0', ← hmc]
        have : st.mem (cntPtr + t) < 2 ^ w := by rw [hmc]; omega
        eval_expr) ?_
      refine runs_seq_assign_le (v := jj0) (by eval_expr) ?_
      refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
      refine runs_seq_assign_le (v := 1 - (if jj0 = len0 / 2 then 1 else 0)) (by eval_expr) ?_
      set rg : ℕ → ℕ := Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update st.regs 11 x) 12 t) 13 ps) 14 t) 15 lo0) 16 len0) 17 jj0) 18 0) 19 (1 - (if jj0 = len0 / 2 then 1 else 0)) with hrg
      set st1 : State := { st with regs := rg } with hst1
      have hM : ∀ s < n, st.mem (arrPtr + s) < n := by
        intro s hs
        have : arrPtr + s < thParPtr := by omega
        rw [hfr _ (Or.inl this)]; exact hIn.arr_lt s hs
      have hRcongr : bstIdx t (fun s => st.mem (arrPtr + s)) lo0 len0 jj0 = Rx := by
        rw [hRdef]
        refine bstIdx_congr len0 t lo0 jj0 (fun k hk => ?_)
        have : arrPtr + (lo0 + k) < thParPtr := by omega
        exact hfr _ (Or.inl this)
      have hInv0 : BstInv n arrPtr st.mem st1.regs Rx (t, lo0, len0, jj0, 0) st1 := by
        refine ⟨rfl, fun i _ => rfl, by simp [hst1, hrg], by simp [hst1, hrg], by simp [hst1, hrg], by simp [hst1, hrg],
          by simp [hst1, hrg], ?_, by rw [hRcongr], by dsimp only; rw [hRcongr]; omega, hjl0,
          by dsimp only; omega, htn, by dsimp only; omega⟩
        simp only [hst1, hrg, Function.update_self]
        split_ifs <;> rfl
      refine runs_seq_triple_le (thBst_loop (R := Rx) (show st1.regs 7 = arrPtr by
        simp [hst1, hrg, r7]) hM (by omega) (t, lo0, len0, jj0, 0)) hInv0 ?_
      rintro st2 ⟨hm2, hfr2, h14, h18, hR1n, hR2n⟩
      have s2r : ∀ i, ¬ BstReg i → st2.regs i = st1.regs i := hfr2
      have q1 : st2.regs 1 = qPtr := by rw [s2r 1 (by simp [BstReg])]; simp [hst1, hrg, r1]
      have q2 : st2.regs 2 = parPtr := by rw [s2r 2 (by simp [BstReg])]; simp [hst1, hrg, r2]
      have q8 : st2.regs 8 = thParPtr := by rw [s2r 8 (by simp [BstReg])]; simp [hst1, hrg, r8]
      have q9 : st2.regs 9 = dthPtr := by rw [s2r 9 (by simp [BstReg])]; simp [hst1, hrg, r9]
      have q11 : st2.regs 11 = x := by rw [s2r 11 (by simp [BstReg])]; simp [hst1, hrg]
      have q12 : st2.regs 12 = t := by rw [s2r 12 (by simp [BstReg])]; simp [hst1, hrg]
      have q13 : st2.regs 13 = ps := by rw [s2r 13 (by simp [BstReg])]; simp [hst1, hrg]
      have hm2p : st2.mem (parPtr + x) = par x := by rw [hm2, hmp]
      have hDof : ∀ y ∈ Q.take j, st.mem (dthPtr + y) = D y := by
        intro y hy
        by_cases hyr : y = r
        · rw [hyr, hdr, hIn.D_r]
        · exact (hdone y hy hyr).1
      set ee := (if ps = 0 then 1 else 0) with hee
      have hee1 : ee ≤ 1 := by rw [hee]; split_ifs <;> omega
      set dp := st.mem (dthPtr + par x) with hdp
      set dt := st.mem (dthPtr + t) with hdt'
      have hdpB : dp ≤ B := hdle _ hpn
      have hdtB : dt ≤ B := hdle _ htn
      set pv := (if ps = 0 then par x else Rx.1) with hpv
      set dv := (if ps = 0 then dp + 1 else dt + 1 + Rx.2) with hdv
      have hpvsel : ee * par x + (1 - ee) * Rx.1 = pv := sel3 _ hee
      have hdvsel : ee * (dp + 1) + (1 - ee) * (dt + 1 + Rx.2) = dv := sel3 _ hee
      have hpvn : pv < n := by rw [hpv]; split_ifs <;> omega
      have hdvD : dv = D x := by
        have hrule := hIn.D_rule x hxn hxr
        unfold DepthRule at hrule
        rw [hdv, hrule]
        change _ = if ps = 0 then D (par x) + 1 else D t + 1 + Rx.2
        split_ifs with hps0
        · rw [hdp, hDof _ hpQ]
        · have htQ := hIn.order x hxn hxr hps0
          rw [hidx] at htQ
          rw [hdt', hDof _ htQ]
      have hdvB : dv ≤ B := by rw [hdvD]; exact hIn.D_le x hxn
      refine runs_seq_assign_le (v := ee) (by eval_expr) ?_
      refine runs_seq_assign_le (v := par x) (by rw [← hm2p]; eval_expr) ?_
      refine runs_seq_store_le (x := thParPtr + x) (v := pv) (by eval_expr) (by
        rw [← hpvsel]
        have : ee * par x + (1 - ee) * Rx.1 < 2 ^ w := by rw [hpvsel]; omega
        eval_expr) ?_
      have hm3p : Function.update st2.mem (thParPtr + x) pv (dthPtr + par x) = dp := by
        rw [Function.update_of_ne (by omega), hm2]
      have hm3t : Function.update st2.mem (thParPtr + x) pv (dthPtr + t) = dt := by
        rw [Function.update_of_ne (by omega), hm2]
      refine runs_store_le (x := dthPtr + x) (v := dv) (by eval_expr) (by
        rw [← hdvsel, ← hm3p, ← hm3t]
        have : Function.update st2.mem (thParPtr + x) pv (dthPtr + par x) + 1 < 2 ^ w := by
          rw [hm3p]; omega
        have : Function.update st2.mem (thParPtr + x) pv (dthPtr + t) + 1 + Rx.2 < 2 ^ w := by
          rw [hm3t]; omega
        have : ee * (Function.update st2.mem (thParPtr + x) pv (dthPtr + par x) + 1) +
            (1 - ee) * (Function.update st2.mem (thParPtr + x) pv (dthPtr + t) + 1 + Rx.2) <
              2 ^ w := by
          rw [hm3p, hm3t, hdvsel]; omega
        eval_expr) ⟨⟨fun i hi => ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ ?_
      · simp only [Function.update_of_ne (show i ≠ 10 by omega),
          Function.update_of_ne (show i ≠ 20 by omega), Function.update_of_ne (show i ≠ 21 by omega)]
        rw [s2r i (by simp only [BstReg]; omega)]
        simp only [hst1, hrg, Function.update_of_ne (show i ≠ 11 by omega),
          Function.update_of_ne (show i ≠ 12 by omega), Function.update_of_ne (show i ≠ 13 by omega),
          Function.update_of_ne (show i ≠ 14 by omega), Function.update_of_ne (show i ≠ 15 by omega),
          Function.update_of_ne (show i ≠ 16 by omega), Function.update_of_ne (show i ≠ 17 by omega),
          Function.update_of_ne (show i ≠ 18 by omega), Function.update_of_ne (show i ≠ 19 by omega)]
        exact hR i hi
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm2]
        exact hfr a ha
      · intro y hy
        dsimp only
        by_cases hyx : y = x
        · rw [hyx, Function.update_self]; exact hdvB
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm2]
          exact hdle y hy
      · dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm2]; exact hpr
      · dsimp only
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm2]; exact hdr
      · intro y hy hyr
        rw [List.take_add_one, List.getElem?_eq_getElem hjQ, Option.toList_some, List.mem_append,
          List.mem_singleton] at hy
        dsimp only
        rcases hy with hy | hy
        · have hyx : y ≠ x := fun h => hxt (h ▸ hy)
          have hyn : y < n := hQ.lt y (List.mem_of_mem_take hy)
          obtain ⟨h1, h2⟩ := hdone y hy hyr
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm2]; exact h1
          · unfold ParRule at h2 ⊢
            dsimp only at h2 ⊢
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm2]; exact h2
        · rw [← hx] at hy
          subst hy
          refine ⟨by rw [Function.update_self, hdvD], ?_⟩
          unfold ParRule
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_self]
      · simp only [Function.update_of_ne (show (10:ℕ) ≠ 21 by omega),
          Function.update_of_ne (show (10:ℕ) ≠ 20 by omega)]
        rw [s2r 10 (by simp [BstReg])]
        simp [hst1, hrg, h10]
      · have := bstLoopCost_mono (show len0 ≤ n by omega)
        simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
        omega
  -- the root step, then the loop
  have hR0 : ∀ i < 10, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hmr : mem qPtr = r := by rw [hrQ]; simpa using hQat 0 hlen0
  refine runs_start_le ?_
  unfold thDepthProc
  refine runs_seq_assign_le (v := r) (by
    have := hR0 1 (by omega); rw [← hmr]; eval_expr) ?_
  refine runs_seq_store_le (x := thParPtr + r) (v := r) (by
    have := hR0 8 (by omega); eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := dthPtr + r) (v := 0) (by
    have := hR0 9 (by omega); eval_expr) (by eval_expr) ?_
  set m1 := Function.update (Function.update mem (thParPtr + r) r) (dthPtr + r) 0 with hm1
  refine runs_seq_triple_le (hloop _ ⟨fun i hi => ?_, by simp, fun a ha => ?_, fun y hy => ?_, ?_,
    ?_, fun y hy hyr => ?_⟩) rfl ?_
  · simp only [Function.update_of_ne (show i ≠ 10 by omega),
      Function.update_of_ne (show i ≠ 11 by omega)]
    exact hR0 i hi
  · show m1 a = mem a
    rw [hm1, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · show m1 (dthPtr + y) ≤ B
    rw [hm1]
    by_cases hyr : y = r
    · rw [hyr, Function.update_self]; omega
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hdth0 y hy
  · show m1 (thParPtr + r) = r
    rw [hm1, Function.update_of_ne (by omega), Function.update_self]
  · show m1 (dthPtr + r) = 0
    rw [hm1, Function.update_self]
  · rw [hQ.take_one hn, List.mem_singleton] at hy
    exact absurd hy hyr
  rintro st ⟨-, -, hfr, -, hpr, hdr, hdone⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qPtr, parPtr, topPtr, depPtr, cntPtr, offPtr,
    arrPtr, thParPtr, dthPtr, rfl, rfl, hfr, fun Q' r' hQ' hQat' => ?_⟩ ?_
  · have hQQ := topDownOrder_eq_of_listAt hQ hQ' hQat hQat'
    subst Q'
    have hr' : r' = r := by rw [← hQ'.head_eq hn, hQ.head_eq hn]
    subst hr'
    have htakeQ : Q.take n = Q := List.take_of_length_le (by rw [hQ.len])
    rw [htakeQ] at hdone
    have hDall : ∀ y < n, st.mem (dthPtr + y) = D y := by
      intro y hy
      by_cases hyr : y = r'
      · rw [hyr, hdr, hIn.D_r]
      · exact (hdone y (hQ.cover y hy) hyr).1
    refine ⟨hpr, hdr, fun x hx hxr => ⟨(hdone x (hQ.cover x hx) hxr).2, ?_⟩⟩
    unfold DepthRule
    dsimp only
    have hpn : par x < n := by
      have hxQ := hQ.cover x hx
      have hi := List.idxOf_lt_length_of_mem hxQ
      have hget : Q[Q.idxOf x] = x := List.getElem_idxOf hi
      have := hQ.after _ hi (by rw [hget]; exact hxr)
      rw [hget] at this
      exact hQ.lt _ (List.mem_of_mem_take this)
    rw [hDall x hx, hDall _ hpn, hDall _ (hIn.top_lt x hx)]
    exact hIn.D_rule x hx hxr
  · simp only [thDepthContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg,
      Expr.size_bin, Expr.size_load]
    have := bstLoopCost_mono (show n ≤ n from le_rfl)
    rcases n with _ | n
    · omega
    · simp only [Nat.add_sub_cancel]
      nlinarith

end

end MinCostFlow.LSF.Program
