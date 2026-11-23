module

public import MinCostFlow.HierPaths.BuildProgConnAllCost
public import MinCostFlow.HierPaths.BuildProgCopy
import MinCostFlow.HierPaths.InitBlockLen

/-!
# Packing all sibling connector rows in one CSR section (bump-heap 2-pass)

Under the bump router contract, each sibling pair routing call may advance the heap by up to
`connPairSpace`. Rather than zeroing router bump scratch between pairs, `buildConnAllProc` runs
two linear bump passes:
1. For every `i = c * k + c' < k * k`, route and build the connector row for `(c, c')` (or `[0]`
   when `c' ≤ c`) at the current bump cursor `cur`, recording `(rowAddr[i], rowLen[i])` in the
   `2 * k * k` directory at `[dst, dst + 2 * k * k)`.
2. Gather all `k * k` rows into a contiguous `csrList (k * k)` starting at `csrStart = cur`, then
   copy that contiguous CSR down to `dst` using `buildCopyProc` (`buildCopyDownContract`) and
   return the final bump cursor `vFinal = csrStart + sec2.length`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Args are `[gAddr, xAddr, start, s, k, Δ, L, d, dst]`. Writes `sec2` at `dst` and returns
a bumped heap cursor `v` with `dst + sec2.length ≤ v ≤ dst + connAllSpace sR G s k d` and
`ZeroFrom after v`. -/
def buildConnAllProc (fPair fCopy : ℕ) : Stmt :=
  .assign 9 (.bin .mul (.reg 4) (.reg 4)) ;;
  .assign 10 (.bin .mul (.reg 3) (.reg 4)) ;;
  .assign 11 (.bin .add (.reg 8) (.bin .add (.reg 9) (.reg 9))) ;;
  forRange 12 (.const 0) (.reg 9)
    (.assign 13 (.bin .div (.reg 12) (.reg 4)) ;;
     .assign 14 (.bin .mod (.reg 12) (.reg 4)) ;;
     .cond (.bin .lt (.reg 13) (.reg 14))
       (.call 15 fPair [.reg 0, .reg 1,
          .bin .add (.reg 2) (.bin .mul (.reg 13) (.reg 3)),
          .bin .add (.reg 2) (.bin .mul (.reg 14) (.reg 3)),
          .reg 3, .reg 5, .reg 6, .reg 11, .reg 7, .reg 10] ;;
        .assign 16 (.load (.reg 11)) ;;
        .store (.bin .add (.reg 8) (.reg 12)) (.reg 16) ;;
        .store (.bin .add (.bin .add (.reg 8) (.reg 9)) (.reg 12))
          (.bin .sub (.reg 15) (.reg 16)) ;;
        .assign 11 (.reg 15))
       (.store (.reg 11) (.const 0) ;;
        .store (.bin .add (.reg 8) (.reg 12)) (.reg 11) ;;
        .store (.bin .add (.bin .add (.reg 8) (.reg 9)) (.reg 12)) (.const 1) ;;
        .assign 11 (.bin .add (.reg 11) (.const 1)))) ;;
  .assign 13 (.reg 11) ;;
  .assign 14 (.bin .add (.bin .add (.reg 13) (.reg 9)) (.const 1)) ;;
  .assign 15 (.reg 14) ;;
  forRange 12 (.const 0) (.reg 9)
    (.store (.bin .add (.reg 13) (.reg 12)) (.bin .sub (.reg 15) (.reg 14)) ;;
     .assign 16 (.load (.bin .add (.reg 8) (.reg 12))) ;;
     .assign 17 (.load (.bin .add (.bin .add (.reg 8) (.reg 9)) (.reg 12))) ;;
     .call 18 fCopy [.reg 16, .reg 17, .reg 15] ;;
     .assign 15 (.bin .add (.reg 15) (.reg 17))) ;;
  .store (.bin .add (.reg 13) (.reg 9)) (.bin .sub (.reg 15) (.reg 14)) ;;
  .call 18 fCopy [.reg 13, .bin .sub (.reg 15) (.reg 13), .reg 8] ;;
  .ret (.reg 15)

theorem buildConnAllProc_noRand (fPair fCopy : ℕ) : (buildConnAllProc fPair fCopy).NoRand := by
  simp [buildConnAllProc, forRange, forUp, Stmt.NoRand]

/-- Contract for writing section 2 (`csrList (k * k) (levelConnRow ...)`) at `dst`, returning a
bumped heap cursor `v` with `ZeroFrom after v`. -/
def buildConnAllContract (w K C : ℕ) (route : RouterFn) (sR : ℕ → ℕ → ℕ → ℕ → ℕ)
    (G : Graph) (start s k Δ L bh : ℕ) : Contract :=
  let X := buildLevelVerts start s k
  let d := routePathLen Δ bh L
  let sec := csrList (k * k) (levelConnRow route G start s k Δ L)
  { pre := fun args mem => ∃ g x dst, args = [g, x, start, s, k, Δ, L, d, dst] ∧
      GraphAt mem g G ∧ ListAt mem x (finsetWords X) ∧
      g + G.encode.length ≤ dst ∧ x + (finsetWords X).length ≤ dst ∧
      ZeroFrom mem dst ∧ G.IsValid ∧ HostPre G X Δ L ∧ 1 ≤ s ∧ 1 ≤ k ∧
      start + k * s < 2 ^ w ∧ 4 < 2 ^ w ∧ G.n < 2 ^ w ∧
      dst + connAllSpace sR G s k Δ L d < 2 ^ w ∧
      ∃ β : ℝ, 0 < β ∧ G.IsExpansionExpanderOn X β ∧ max 2 (2 / β) ≤ (bh : ℝ)
    post := fun args mem v after => ∃ g x dst, args = [g, x, start, s, k, Δ, L, d, dst] ∧
      dst + sec.length ≤ v ∧ v ≤ dst + connAllSpace sR G s k Δ L d ∧
      ListAt after dst sec ∧
      (∀ j < dst, after j = mem j) ∧ ZeroFrom after v
    cost := fun _ _ => connAllCostBound K C G s k Δ L bh }

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

private theorem connAll_pass2_triple {w fCopy total csrStart dataStart dst : ℕ}
    {rows : ℕ → List ℕ} {p : Program} {mem₁ : ℕ → ℕ} {maxRow : ℕ}
    (hfCopy : p.procs[fCopy]? = some buildCopyProc)
    (hDstCsr : dst + 2 * total ≤ csrStart)
    (hDataEq : dataStart = csrStart + total + 1)
    (hRowLe : ∀ i < total, (rows i).length ≤ maxRow)
    (hDir : ∀ j < total,
      mem₁ (dst + j) + (rows j).length ≤ csrStart ∧
      mem₁ (dst + total + j) = (rows j).length ∧
      ListAt mem₁ (mem₁ (dst + j)) (rows j))
    (hZero₁ : ZeroFrom mem₁ csrStart)
    (hEndW : dataStart + initCSRPrefix rows total < 2 ^ w)
    (hw1 : 1 < 2 ^ w) :
    let pref := initCSRPrefix rows
    Triple w p
      (fun st =>
        st.regs 8 = dst ∧ st.regs 9 = total ∧ st.regs 13 = csrStart ∧
        st.regs 14 = dataStart ∧ st.regs 15 = dataStart ∧ st.mem = mem₁)
      (forRange 12 (.const 0) (.reg 9)
        (.store (.bin .add (.reg 13) (.reg 12)) (.bin .sub (.reg 15) (.reg 14)) ;;
         .assign 16 (.load (.bin .add (.reg 8) (.reg 12))) ;;
         .assign 17 (.load (.bin .add (.bin .add (.reg 8) (.reg 9)) (.reg 12))) ;;
         .call 18 fCopy [.reg 16, .reg 17, .reg 15] ;;
         .assign 15 (.bin .add (.reg 15) (.reg 17))))
      (normalPost fun st =>
        st.regs 8 = dst ∧ st.regs 9 = total ∧ st.regs 13 = csrStart ∧
        st.regs 14 = dataStart ∧ st.regs 15 = dataStart + pref total ∧
        (∀ j < total, st.mem (csrStart + j) = pref j) ∧
        ListAt st.mem dataStart (csrData total rows) ∧
        ZeroFrom st.mem (dataStart + pref total) ∧
        ∀ y < csrStart, st.mem y = mem₁ y)
      (fun _ => (total - 0) * ((17 * maxRow + 65) + ((Expr.reg 9).size + 8)) +
        ((Expr.const 0).size + (Expr.reg 9).size + 5)) := by
  intro pref
  have hPrefMono (i : ℕ) (hi : i ≤ total) : pref i ≤ pref total := by
    simpa only [pref, initAppendPrefix, List.length_flatMap, initCSRPrefix] using
      initAppendPrefix_length_mono rows hi
  have hTotW : total < 2 ^ w := by omega
  have hCopySpec := buildCopyProc_meetsContract (w := w) hfCopy
  refine (Triple.forRange_const (p := p) (r := 12) (lo := .const 0) (hi := .reg 9)
    (Inv := fun i st =>
      st.regs 8 = dst ∧ st.regs 9 = total ∧ st.regs 12 = i ∧ st.regs 13 = csrStart ∧
      st.regs 14 = dataStart ∧ st.regs 15 = dataStart + pref i ∧
      (∀ j < i, st.mem (csrStart + j) = pref j) ∧
      ListAt st.mem dataStart (csrData i rows) ∧
      ZeroFrom st.mem (dataStart + pref i) ∧
      ∀ y < csrStart, st.mem y = mem₁ y)
    (17 * maxRow + 65) 0 total (Nat.zero_le _) hw1 (fun _ => hTotW)
    (fun st ⟨r8, r9, r13, r14, r15, hm⟩ => by
      have hp0 : pref 0 = 0 := rfl
      refine ⟨Expr.eval_const (Nat.two_pow_pos w), by simp [r8], by simp [r9], by simp,
        by simp [r13], by simp [r14], by simpa [hp0] using r15,
        fun _ h => (Nat.not_lt_zero _ h).elim, by simp [csrData, ListAt],
        by rw [hp0, Nat.add_zero, hm]; exact fun y hy => hZero₁ y (by omega),
        fun _ _ => congrFun hm _⟩)
    (fun _ _ _ _ h => h.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.1)
    (fun i _ hi st ω' ⟨r8, r9, r12, r13, r14, r15, hOff, hData, hZero, hFrame⟩ => by
      let cur := dataStart + pref i
      have hSucc : pref (i + 1) = pref i + (rows i).length := initCSRPrefix_succ rows i
      have hCurNext : cur + (rows i).length ≤ dataStart + pref total := by
        have := hPrefMono (i + 1) hi; rw [hSucc] at this; dsimp [cur]; omega
      have hEndW' : dataStart + pref total < 2 ^ w := hEndW
      have hCurW : cur < 2 ^ w := by omega
      have hNextW : cur + (rows i).length < 2 ^ w := by omega
      have hCsrI : csrStart + i < 2 ^ w := by omega
      have hDstI : dst + i < 2 ^ w := by omega
      have hDstTot : dst + total < 2 ^ w := by omega
      have hDstTotI : dst + total + i < 2 ^ w := by omega
      obtain ⟨hAddrEnd, hLenAt, hRowAt⟩ := hDir i hi
      set addr := mem₁ (dst + i)
      set rlen := (rows i).length
      have hAddrW : addr < 2 ^ w := by omega
      have hLenW : rlen < 2 ^ w := by omega
      let m₁ := Function.update st.mem (csrStart + i) (pref i)
      have hM1Lt (y : ℕ) (hy : y < csrStart) : m₁ y = mem₁ y :=
        (Function.update_of_ne (by omega) _ _).trans (hFrame y hy)
      have hAddrM1 : m₁ (dst + i) = addr := hM1Lt _ (by omega)
      have hLenM1 : m₁ (dst + total + i) = rlen := (hM1Lt _ (by omega)).trans hLenAt
      refine runs_start_le ?_
      refine runs_seq_store_le (x := csrStart + i) (v := pref i)
        (Expr.eval_add (Expr.eval_reg_of_eq r13) (Expr.eval_reg_of_eq r12) hCsrI)
        (by have hsub : cur - dataStart = pref i := by dsimp [cur]; omega
            rw [← hsub]; exact Expr.eval_sub (Expr.eval_reg_of_eq r15) (Expr.eval_reg_of_eq r14) hCurW) ?_
      refine runs_seq_assign_le (v := addr)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r8)
          (Expr.eval_reg_of_eq r12) hDstI) hAddrM1) ?_
      refine runs_seq_assign_le (v := rlen)
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r8))
          (Expr.eval_reg_of_eq (by simpa using r9)) hDstTot)
          (Expr.eval_reg_of_eq (by simpa using r12)) hDstTotI) hLenM1) ?_
      refine runs_seq_call_le hCopySpec (vs := [addr, rlen, cur])
        (by simp [evalArgs, Expr.eval, r15, cur])
        (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl | rfl <;> assumption)
        ⟨addr, rlen, cur, rfl, by dsimp [cur]; omega, hNextW, hw1⟩ ?_
      intro _ m₂ _ hPostC
      obtain ⟨_, _, _, hEqC, hCopied, hFrC⟩ := hPostC
      simp only [List.cons.injEq, and_true] at hEqC
      obtain ⟨rfl, rfl, rfl⟩ := hEqC
      refine runs_assign_le (v := cur + rlen)
        (Expr.eval_add (Expr.eval_reg_of_eq (by simpa using r15))
          (Expr.eval_reg_of_eq (by simp)) hNextW) ?_ ?_
      · refine ⟨⟨by simp [r8], by simp [r9], by simp, by simp [r13], by simp [r14],
          by change cur + rlen = dataStart + pref (i + 1); rw [hSucc]; dsimp [cur, rlen]; omega,
          ?_, ?_, ?_, ?_⟩, by simp [r12]⟩
        · intro j hj
          have hneC : csrStart + j < cur := by dsimp [cur]; omega
          change m₂ (csrStart + j) = pref j
          rw [hFrC _ (Or.inl hneC)]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · exact (Function.update_of_ne (by omega) _ _).trans (hOff j hlt)
          · simp [m₁]
        · rw [csrData_succ, listAt_append, length_csrData_eq]
          refine ⟨WordRAM.ListAt.congr hData fun j _ hj2 => ?_, ?_⟩
          · rw [length_csrData_eq] at hj2
            change j < cur at hj2
            exact (hFrC j (Or.inl hj2)).trans (Function.update_of_ne (by dsimp [cur] at hj2; omega) _ _)
          · intro j hj
            exact (hCopied j hj).trans ((hM1Lt _ (by omega)).trans (hRowAt j hj))
        · intro y hy
          rw [hSucc] at hy
          exact (hFrC y (Or.inr (by dsimp [cur, rlen]; omega))).trans
            ((Function.update_of_ne (by omega) _ _).trans (hZero y (by omega)))
        · intro y hy
          exact (hFrC y (Or.inl (by dsimp [cur]; omega))).trans (hM1Lt y hy)
      · have hRL := hRowLe i hi
        simp only [buildCopyContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
        dsimp only [rlen]; omega)).conseq (fun _ h => h)
    (fun o st h => match o with
      | .returned _ => False.elim h
      | .normal => ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
          h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩)
    (fun _ _ => le_rfl)

/-- **`buildConnAllProc` writes the entire connector CSR section** at `dst` in two bump passes
within `connAllCostBound` and `connAllSpace`, without zeroing router scratch. -/
theorem buildConnAllProc_meetsContract {w K C f fPair fCopy : ℕ} {p : Program}
    {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {start s k Δ L bh : ℕ}
    (hf : p.procs[f]? = some (buildConnAllProc fPair fCopy))
    (hfCopy : p.procs[fCopy]? = some buildCopyProc)
    (hPlayer : IsMatchingPlayer route routeCost)
    (hC : ∀ pairs b', RouterPre G (buildLevelVerts start s k) pairs Δ L → 2 ≤ b' →
      routeCost G (buildLevelVerts start s k) pairs Δ L b' 0 ≤
        routeBound C G (buildLevelVerts start s k) pairs Δ L b')
    (hPair : ∀ a b M emb,
      (lemma1Route route G (buildLevelVerts start s k) (connRequestPairs a b s) Δ L).1 =
        .matched [M] emb →
      M.length = s →
      MeetsContract w p fPair (buildConnOneContract w K route routeCost sR G
        (buildLevelVerts start s k) a b Δ L (routePathLen Δ bh L) M emb)) :
    MeetsContract w p f (buildConnAllContract w K C route sR G start s k Δ L bh) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨g, x, dst, rfl, hG, hX, hGE, hXE, hZ, hValid, hHost, hs, hk, hTermW, hw4, hGnW,
    hRoom, β, hPos, hExp, hBh⟩ := hPre
  let X := buildLevelVerts start s k
  let d := routePathLen Δ bh L
  let R := routeCong Δ bh L
  let rows := levelConnRow route G start s k Δ L
  let total := k * k
  let xLen := s * k
  let sec := csrList total rows
  let pairSp := connPairSpace sR G s k Δ L d
  have hXcard : X.card = xLen := by simp [X, buildLevelVerts, xLen, Nat.mul_comm]
  have hSecLenLe : sec.length ≤ total + 1 + total * (8 + 3 * s + s * d) :=
    levelConnSec_length_le hPlayer hPos hExp hHost hs hk hBh
  have hSecLen : sec.length = total + 1 + initCSRPrefix rows total := by
    rw [show sec = csrList total rows from rfl, csrList, List.length_append, length_csrOffsets,
      length_csrData_eq]
    rfl
  have hSpaceUnfold : connAllSpace sR G s k Δ L d =
      2 * total + total * pairSp + (total + 1 + total * (8 + 3 * s + s * d)) + 10 := rfl
  change dst + connAllSpace sR G s k Δ L d < 2 ^ w at hRoom
  have hw1 : 1 < 2 ^ w := by omega
  have hTotW : total < 2 ^ w := by dsimp [total] at hSpaceUnfold ⊢; omega
  have hXLenW : xLen < 2 ^ w := by
    have : xLen = k * s := Nat.mul_comm s k
    omega
  have h2TotW : total + total < 2 ^ w := by omega
  have hCur0W : dst + (total + total) < 2 ^ w := by omega
  -- Pass 1 invariant and loop
  let step1Bound := (2 * (K * (C + 10) + 280) + 1500) * (s * k + G.m + 1) * (d + 1) * (R + 1) + 160
  let RFixed (st : State) : Prop :=
    st.regs 0 = g ∧ st.regs 1 = x ∧ st.regs 2 = start ∧ st.regs 3 = s ∧
    st.regs 4 = k ∧ st.regs 5 = Δ ∧ st.regs 6 = L ∧ st.regs 7 = d ∧
    st.regs 8 = dst ∧ st.regs 9 = total ∧ st.regs 10 = xLen
  let Inv1 (i : ℕ) (st : State) : Prop :=
    RFixed st ∧ st.regs 12 = i ∧
    dst + 2 * total ≤ st.regs 11 ∧ st.regs 11 ≤ dst + 2 * total + i * pairSp ∧
    (∀ j < i, dst + 2 * total ≤ st.mem (dst + j) ∧
      st.mem (dst + j) + (rows j).length ≤ st.regs 11 ∧
      st.mem (dst + total + j) = (rows j).length ∧
      ListAt st.mem (st.mem (dst + j)) (rows j) ∧
      (rows j).length ≤ 8 + 3 * s + s * d) ∧
    ZeroFrom st.mem (st.regs 11) ∧
    ∀ y < dst, st.mem y = mem y
  have hLoop1 := Triple.forRange_const (p := p) (r := 12) (lo := .const 0) (hi := .reg 9)
    (body :=
      .assign 13 (.bin .div (.reg 12) (.reg 4)) ;;
      .assign 14 (.bin .mod (.reg 12) (.reg 4)) ;;
      .cond (.bin .lt (.reg 13) (.reg 14))
        (.call 15 fPair [.reg 0, .reg 1,
           .bin .add (.reg 2) (.bin .mul (.reg 13) (.reg 3)),
           .bin .add (.reg 2) (.bin .mul (.reg 14) (.reg 3)),
           .reg 3, .reg 5, .reg 6, .reg 11, .reg 7, .reg 10] ;;
         .assign 16 (.load (.reg 11)) ;;
         .store (.bin .add (.reg 8) (.reg 12)) (.reg 16) ;;
         .store (.bin .add (.bin .add (.reg 8) (.reg 9)) (.reg 12))
           (.bin .sub (.reg 15) (.reg 16)) ;;
         .assign 11 (.reg 15))
        (.store (.reg 11) (.const 0) ;;
         .store (.bin .add (.reg 8) (.reg 12)) (.reg 11) ;;
         .store (.bin .add (.bin .add (.reg 8) (.reg 9)) (.reg 12)) (.const 1) ;;
         .assign 11 (.bin .add (.reg 11) (.const 1))))
    (P := fun st => RFixed st ∧ st.regs 11 = dst + (total + total) ∧ st.mem = mem)
    (Inv := Inv1) step1Bound 0 total (Nat.zero_le _) hw1 (fun _ => hTotW)
    (fun st ⟨hR, h11, hm⟩ => by
      refine ⟨Expr.eval_const (Nat.two_pow_pos w), by simpa [RFixed] using hR, by simp,
        by simp [h11]; omega, by simp [h11]; omega,
        fun _ h => (Nat.not_lt_zero _ h).elim,
        by simp [h11, hm]; exact fun y hy => hZ y (by omega),
        fun _ _ => congrFun hm _⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.1.2.2.2.2.2.2.2.2.2.1)
    (fun i _ hi st ω' ⟨hR, h12, hCurLo, hCurHi, hDir, hZero, hFrame⟩ => by
      obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := hR
      set cur := st.regs 11
      have hMulLe : (i + 1) * pairSp ≤ total * pairSp := Nat.mul_le_mul_right pairSp hi
      rw [Nat.succ_mul] at hMulLe
      have hCurRoom : cur + pairSp < 2 ^ w := by omega
      have hCurW : cur < 2 ^ w := by omega
      have hIw : i < 2 ^ w := hi.trans hTotW
      have hDstI : dst + i < 2 ^ w := by omega
      have hDstTot : dst + total < 2 ^ w := by omega
      have hDstTotI : dst + total + i < 2 ^ w := by omega
      let c := i / k
      let c' := i % k
      have hc : c < k := Nat.div_lt_of_lt_mul hi
      have hc' : c' < k := Nat.mod_lt i (by omega)
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := c)
        (Expr.eval_div (Expr.eval_reg_of_eq h12) (Expr.eval_reg_of_eq r4) hIw) ?_
      refine runs_seq_assign_le (v := c')
        (Expr.eval_mod (Expr.eval_reg_of_eq (by simp [h12])) (Expr.eval_reg_of_eq (by simp [r4])) hIw) ?_
      refine runs_cond_le (v := if c < c' then 1 else 0)
        (Expr.eval_lt_op (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) hw1) ?_ ?_
      · intro hne
        have hlt : c < c' := by split_ifs at hne with h; exact h; omega
        let a := start + c * s
        let b := start + c' * s
        have hcs : c * s + s ≤ k * s := by
          have : (c + 1) * s ≤ k * s := Nat.mul_le_mul_right s hc
          rw [Nat.add_mul, Nat.one_mul] at this; exact this
        have hc's : c' * s + s ≤ k * s := by
          have : (c' + 1) * s ≤ k * s := Nat.mul_le_mul_right s hc'
          rw [Nat.add_mul, Nat.one_mul] at this; exact this
        have hcsW : c * s < 2 ^ w := by omega
        have hc'sW : c' * s < 2 ^ w := by omega
        have haW : a < 2 ^ w := by dsimp [a]; omega
        have hbW : b < 2 ^ w := by dsimp [b]; omega
        have hasW : a + s < 2 ^ w := by dsimp [a]; omega
        have hbsW : b + s < 2 ^ w := by dsimp [b]; omega
        have hch := buildLevel_isChildren (start := start) (k := k) hs
        have hRPre : RouterPre G X (connRequestPairs a b s) Δ L := by
          simpa [connRequestPairs, buildLevelChild, a, b] using
            routerPre_pair hHost hch hc hc' (by omega)
        obtain ⟨_, hex⟩ := exists_lemma_1 hPlayer
        obtain ⟨⟨Ms, emb, hRes, hMatch, hFull⟩, _, hLast, _, _⟩ :=
          hex G X (connRequestPairs a b s) Δ L hRPre (by simp [connRequestPairs]) β hPos hExp
        have hLen1 : Ms.length = 1 := by simpa [connRequestPairs] using hMatch.1
        rcases List.length_eq_one_iff.mp hLen1 with ⟨M, rfl⟩
        have hMlen : M.length = s := by
          have hf := hFull 0 (by simp [connRequestPairs])
          simpa [connRequestPairs, card_shiftSet] using hf
        have hLastNat : (lemma1Route route G X (connRequestPairs a b s) Δ L).2 ≤ bh := by
          exact_mod_cast hLast.trans hBh
        have hWalk : ∀ j < M.length, IsEdgeWalk G.edges (edgeAt M j).1 (edgeAt M j).2 (emb j) := by
          intro j hj
          have hj' : j < ([M] : List (List (ℕ × ℕ))).flatten.length := by simpa using hj
          have hmem : edgeAt M j ∈ M := by
            unfold edgeAt; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
          have hends := (hMatch.2.1 0 (by simp [connRequestPairs])).1 (edgeAt M j) (by simpa using hmem)
          have hins : insideB X (edgeAt ([M] : List (List (ℕ × ℕ))).flatten j) = true := by
            simp only [List.flatten_cons, List.flatten_nil, List.append_nil, insideB,
              Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨(hch.2.1 _ hc).1 hends.1, (hch.2.1 _ hc').1 hends.2⟩
          simpa [Graph.m, edgeAt] using (hMatch.2.2.2.1 j hj' hins).1
        have hEmbLen : ∀ j < M.length, (emb j).length ≤ d := by
          intro j hj
          have hj' : j < ([M] : List (List (ℕ × ℕ))).flatten.length := by simpa using hj
          have h1 := hMatch.2.2.2.2.1 j hj'
          have h2 : routePathLen Δ (lemma1Route route G X (connRequestPairs a b s) Δ L).2 L ≤ d := by
            dsimp [d]; unfold routePathLen; gcongr
          exact h1.trans h2
        have hRowEq : rows i = csrList M.length (connectorRows G M emb) :=
          levelConnRow_eq_connectorRows hlt hRes
        have hPairsLen : (pairsWords (connRequestPairs a b s)).length = 3 + 2 * s := by
          rw [connRequestPairs_words]; simp [length_tabList]; omega
        have hRawLe : ((List.range s).map fun j => (emb j).length).sum ≤ s * d :=
          sum_map_le_mul_conn fun j hj => hEmbLen j (hMlen.symm ▸ hj)
        have hRowLenLe : (csrList M.length (connectorRows G M emb)).length ≤ 8 + 3 * s + s * d := by
          have h1 : (csrList M.length (connectorRows G M emb)).length ≤
              8 + 3 * M.length + ((List.range M.length).map fun j => (emb j).length).sum :=
            (connectorRows_length_le hWalk).trans (le_of_eq (connectorReplyLength M emb))
          rw [hMlen] at h1 ⊢; omega
        have hPairPre : (buildConnOneContract w K route routeCost sR G X a b Δ L d M emb).pre
            [g, x, a, b, s, Δ, L, cur, d, xLen] st.mem := by
          refine ⟨g, x, cur, by rw [hMlen, hXcard], ?_, hw4, hGnW, ?_⟩
          · refine ⟨g, x, cur, by rw [hMlen, hXcard], ?_, hValid, ?_, hGE.trans (by omega), hXE.trans (by omega),
              by rw [hMlen]; exact hasW, by rw [hMlen]; exact hbsW, hw4, hZero, ?_, ?_⟩
            · exact WordRAM.ListAt.congr hG fun j _ hj => hFrame j (hj.trans_le hGE)
            · exact WordRAM.ListAt.congr hX fun j _ hj => hFrame j (hj.trans_le hXE)
            · rw [hMlen, hPairsLen, hXcard]
              dsimp [pairSp, connPairSpace, xLen] at hCurRoom ⊢; omega
            · rw [hMlen]; exact hRPre
          · intro rep top _ hTopHi
            change top ≤ cur + 3 + 2 * M.length +
              (X.card + 1) * routerSpaceUpTo sR G.n G.encode.length
                (pairsWords (connRequestPairs a b M.length)).length (Δ + L + max 2 X.card) at hTopHi
            rw [hMlen, hPairsLen, hXcard] at hTopHi
            have hCurSz := connectorWalkRow_cursor_size M emb (top + 2 + M.length + d + 1 + G.n) M.length
            rw [hCurSz, hMlen]
            have hRL : (csrList s (connectorRows G M emb)).length ≤ 8 + 3 * s + s * d := hMlen ▸ hRowLenLe
            dsimp [pairSp, connPairSpace, xLen] at hCurRoom hTopHi ⊢; omega
        have hCall := hPair a b M emb hRes hMlen
        refine runs_seq_call_le hCall (vs := [g, x, a, b, s, Δ, L, cur, d, xLen])
          (by simp [evalArgs, Expr.eval, Function.update, r0, r1, r2, r3, r5, r6, r7, r10,
              hcsW, hc'sW, haW, hbW, a, b, cur])
          (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
              all_goals first | exact haW | exact hbW | exact hCurW | exact hXLenW | exact hWords _ (by simp [d]))
          hPairPre ?_
        intro vEnd after₁ pos₁ hPost
        obtain ⟨_, _, _, top, out, eq, _, hTopHi, hOutEq, hCurLtOut, hOutPtr, hRowAt, hvEndEq, hF, hZero₁⟩ := hPost
        simp only [List.cons.injEq, and_true, true_and] at eq
        obtain ⟨rfl, rfl, _, rfl, _⟩ := eq
        rw [← hRowEq] at hRowAt hvEndEq
        have hvEndLe : vEnd ≤ cur + pairSp := by
          rw [hMlen, hPairsLen, hXcard] at hTopHi
          have hCurSz := connectorWalkRow_cursor_size M emb (top + 2 + M.length + d + 1 + G.n) M.length
          rw [hCurSz, hMlen] at hOutEq
          have hRL : (rows i).length ≤ 8 + 3 * s + s * d := hRowEq ▸ hRowLenLe
          dsimp [pairSp, connPairSpace, xLen] at hTopHi ⊢; omega
        have hvEndW : vEnd < 2 ^ w := by omega
        have hOutW : out < 2 ^ w := by omega
        have hRowLenW : (rows i).length < 2 ^ w := by omega
        have hSubLen : vEnd - out = (rows i).length := by omega
        refine runs_seq_assign_le (v := out)
          (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by simp [cur])) hOutPtr) ?_
        refine runs_seq_store_le (x := dst + i) (v := out)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r8])) (Expr.eval_reg_of_eq (by simp [h12])) hDstI)
          (Expr.eval_reg_of_eq (by simp)) ?_
        refine runs_seq_store_le (x := dst + total + i) (v := (rows i).length)
          (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r8]))
            (Expr.eval_reg_of_eq (by simp [r9])) hDstTot)
            (Expr.eval_reg_of_eq (by simp [h12])) hDstTotI)
          (by rw [← hSubLen]; exact Expr.eval_sub (Expr.eval_reg_of_eq (by simp))
                (Expr.eval_reg_of_eq (by simp)) hvEndW) ?_
        refine runs_assign_le (v := vEnd) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
        · let mFin := Function.update (Function.update after₁ (dst + i) out)
              (dst + total + i) (rows i).length
          have hMFinAbove (y : ℕ) (hy : dst + 2 * total ≤ y) : mFin y = after₁ y := by
            dsimp [mFin]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          have hMFinBelow (y : ℕ) (hy : y < dst) : mFin y = mem y := by
            dsimp [mFin]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact (hF y (by omega)).trans (hFrame y hy)
          let rFin := Function.update (Function.update (Function.update (Function.update
              (Function.update (Function.update st.regs 13 c) 14 c') 15 vEnd) 16 out) 11 vEnd)
              12 (i + 1)
          have hReg11 : rFin 11 = vEnd := by
            dsimp [rFin]; rw [Function.update_of_ne (by decide), Function.update_self]
          refine ⟨⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
            by simp [r5], by simp [r6], by simp [r7], by simp [r8], by simp [r9], by simp [r10]⟩,
            by simp, by change dst + 2 * total ≤ rFin 11; rw [hReg11]; omega,
            by change rFin 11 ≤ dst + 2 * total + (i + 1) * pairSp
               rw [hReg11, Nat.add_mul, Nat.one_mul]; omega,
            ?_, ?_, ?_⟩, by simp [h12]⟩
          · intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hltj | rfl
            · obtain ⟨hJLo, hJE, hJL, hJAt, hJMax⟩ := hDir j hltj
              have hAddrJ : mFin (dst + j) = st.mem (dst + j) := by
                dsimp [mFin]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact hF _ (by omega)
              have hLenJ : mFin (dst + total + j) = (rows j).length := by
                dsimp [mFin]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact (hF _ (by omega)).trans hJL
              refine ⟨by change dst + 2 * total ≤ mFin (dst + j); rw [hAddrJ]; exact hJLo,
                by change mFin (dst + j) + (rows j).length ≤ rFin 11; rw [hAddrJ, hReg11]; omega,
                hLenJ, ?_, hJMax⟩
              change ListAt mFin (mFin (dst + j)) (rows j)
              rw [hAddrJ]
              exact WordRAM.ListAt.congr hJAt fun y hy1 hy2 =>
                (hMFinAbove y (hJLo.trans hy1)).trans (hF y (hy2.trans_le hJE))
            · have hA : mFin (dst + j) = out := by
                dsimp [mFin]; rw [Function.update_of_ne (by omega), Function.update_self]
              refine ⟨by change dst + 2 * total ≤ mFin (dst + j); rw [hA]; omega,
                by change mFin (dst + j) + (rows j).length ≤ rFin 11; rw [hA, hReg11]; omega,
                by simp, ?_, hRowEq ▸ hRowLenLe⟩
              change ListAt mFin (mFin (dst + j)) (rows j)
              rw [hA]
              exact WordRAM.ListAt.congr hRowAt fun y hy _ => hMFinAbove y (by omega)
          · intro y hy; change rFin 11 ≤ y at hy; rw [hReg11] at hy
            exact (hMFinAbove y (by omega)).trans (hZero₁ y hy)
          · exact hMFinBelow
        · have hCost := pair_one_cost_le (w := w) (K := K) (C := C) (sR := sR)
            (args := [g, x, a, b, s, Δ, L, cur, d, xLen]) (mem := st.mem)
            hPlayer hC hRPre hRes hLastNat hMlen hWalk hEmbLen hs hk
          have hCost' : (buildConnOneContract w K route routeCost sR G (buildLevelVerts start s k)
              a b Δ L (routePathLen Δ bh L) M emb).cost
              [g, x, a, b, s, Δ, L, cur, d, xLen] st.mem ≤
            (2 * (K * (C + 10) + 280) + 1500) * (s * k + G.m + 1) * (d + 1) * (R + 1) := hCost
          simp only [Expr.size, argsSize, step1Bound]
          clear * - hCost'
          omega
      · intro hzero
        have hge : c' ≤ c := by split_ifs at hzero with h; omega
        have hRowEq : rows i = [0] := levelConnRow_of_ge hge
        have hCur1W : cur + 1 < 2 ^ w := by dsimp [pairSp, connPairSpace] at hCurRoom; omega
        refine runs_seq_store_le (x := cur) (v := 0)
          (Expr.eval_reg_of_eq (by simp [cur])) (Expr.eval_const (Nat.two_pow_pos w)) ?_
        refine runs_seq_store_le (x := dst + i) (v := cur)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r8])) (Expr.eval_reg_of_eq (by simp [h12])) hDstI)
          (Expr.eval_reg_of_eq (by simp [cur])) ?_
        refine runs_seq_store_le (x := dst + total + i) (v := 1)
          (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r8]))
            (Expr.eval_reg_of_eq (by simp [r9])) hDstTot)
            (Expr.eval_reg_of_eq (by simp [h12])) hDstTotI)
          (Expr.eval_const hw1) ?_
        refine runs_assign_le (v := cur + 1)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [cur])) (Expr.eval_const hw1) hCur1W) ?_ ?_
        · let mFin := Function.update (Function.update (Function.update st.mem cur 0)
              (dst + i) cur) (dst + total + i) 1
          let rFin := Function.update (Function.update (Function.update (Function.update
              st.regs 13 c) 14 c') 11 (cur + 1)) 12 (i + 1)
          have hReg11 : rFin 11 = cur + 1 := by
            dsimp [rFin]; rw [Function.update_of_ne (by decide), Function.update_self]
          refine ⟨⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
            by simp [r5], by simp [r6], by simp [r7], by simp [r8], by simp [r9], by simp [r10]⟩,
            by simp, by change dst + 2 * total ≤ rFin 11; rw [hReg11]; omega,
            by change rFin 11 ≤ dst + 2 * total + (i + 1) * pairSp
               have hPairPos : 1 ≤ pairSp := by dsimp [pairSp, connPairSpace]; omega
               rw [hReg11, Nat.add_mul, Nat.one_mul]; omega,
            ?_, ?_, ?_⟩, by simp [h12]⟩
          · intro j hj
            rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hltj | rfl
            · obtain ⟨hJLo, hJE, hJL, hJAt, hJMax⟩ := hDir j hltj
              have hAddrJ : mFin (dst + j) = st.mem (dst + j) := by
                dsimp [mFin]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
              have hLenJ : mFin (dst + total + j) = (rows j).length := by
                dsimp [mFin]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
                exact hJL
              refine ⟨by change dst + 2 * total ≤ mFin (dst + j); rw [hAddrJ]; exact hJLo,
                by change mFin (dst + j) + (rows j).length ≤ rFin 11; rw [hAddrJ, hReg11]; omega,
                hLenJ, ?_, hJMax⟩
              change ListAt mFin (mFin (dst + j)) (rows j)
              rw [hAddrJ]
              exact WordRAM.ListAt.congr hJAt fun y hy1 hy2 => by
                dsimp [mFin]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega)]
            · have hA : mFin (dst + j) = cur := by
                dsimp [mFin]; rw [Function.update_of_ne (by omega), Function.update_self]
              refine ⟨by change dst + 2 * total ≤ mFin (dst + j); rw [hA]; exact hCurLo,
                by change mFin (dst + j) + (rows j).length ≤ rFin 11; rw [hA, hReg11, hRowEq]; simp,
                by simp [hRowEq], ?_, by simp [hRowEq]; omega⟩
              change ListAt mFin (mFin (dst + j)) (rows j)
              rw [hA, hRowEq]
              intro idx hidx
              have h0 : idx = 0 := by simp at hidx; omega
              subst h0
              change mFin (cur + 0) = 0
              dsimp [mFin]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              simp [Function.update]
          · intro y hy; change rFin 11 ≤ y at hy; rw [hReg11] at hy
            dsimp [mFin]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hZero y (by omega)
          · intro y hy
            dsimp [mFin]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
            exact hFrame y hy
        · simp only [Expr.size, step1Bound]; omega)
  -- Chain Pass 1, Pass 2, final copy down, and return
  refine runs_start_le ?_
  unfold buildConnAllProc
  refine runs_seq_assign_le (v := total)
    (Expr.eval_mul (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_reg_of_eq (by simp [startState])) hTotW) ?_
  refine runs_seq_assign_le (v := xLen)
    (Expr.eval_mul (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_reg_of_eq (by simp [startState])) hXLenW) ?_
  refine runs_seq_assign_le (v := dst + (total + total))
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_reg_of_eq (by simp)) h2TotW) hCur0W) ?_
  refine runs_seq_triple_le hLoop1
    ⟨⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp [startState], by simp [startState], by simp [startState, d],
      by simp [startState], by simp, by simp⟩, by simp, rfl⟩ ?_
  intro st₁ ⟨⟨_, _, _, _, _, _, _, _, r8, r9, _⟩, _, hCsrLo, hCsrHi, hDir₁, hZero₁, hFrame₁⟩
  set csrStart := st₁.regs 11
  set dataStart := csrStart + total + 1
  set writeEnd := dataStart + initCSRPrefix rows total
  have hWriteEq : writeEnd = csrStart + sec.length := by rw [hSecLen]; dsimp [writeEnd, dataStart]; omega
  have hWriteLe : writeEnd ≤ dst + connAllSpace sR G s k Δ L d := by omega
  have hWriteW : writeEnd < 2 ^ w := hWriteLe.trans_lt hRoom
  have hCsrTotW : csrStart + total < 2 ^ w := by dsimp [writeEnd, dataStart] at hWriteW; omega
  have hDataW : dataStart < 2 ^ w := by dsimp [writeEnd, dataStart] at hWriteW; omega
  have hCsrW : csrStart < 2 ^ w := by dsimp [writeEnd, dataStart] at hWriteW; omega
  refine runs_seq_assign_le (v := csrStart) (Expr.eval_reg_of_eq rfl) ?_
  refine runs_seq_assign_le (v := dataStart)
    (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
      (Expr.eval_reg_of_eq (by simp [r9])) hCsrTotW) (Expr.eval_const hw1) hDataW) ?_
  refine runs_seq_assign_le (v := dataStart) (Expr.eval_reg_of_eq (by simp)) ?_
  have hLoop2 := connAll_pass2_triple (w := w) (fCopy := fCopy) (total := total)
    (csrStart := csrStart) (dataStart := dataStart) (dst := dst) (rows := rows)
    (mem₁ := st₁.mem) (maxRow := 8 + 3 * s + s * d) hfCopy hCsrLo rfl
    (fun i hi => (hDir₁ i hi).2.2.2.2)
    (fun j hj => ⟨(hDir₁ j hj).2.1, (hDir₁ j hj).2.2.1, (hDir₁ j hj).2.2.2.1⟩)
    hZero₁ hWriteW hw1
  refine runs_seq_triple_le hLoop2
    ⟨by simp [r8], by simp [r9], by simp, by simp, by simp, rfl⟩ ?_
  intro st₂ ⟨q8, q9, q13, q14, q15, hOff₂, hData₂, hZero₂, hFrame₂⟩
  have hSubPref : writeEnd - dataStart = initCSRPrefix rows total := by dsimp [writeEnd]; omega
  refine runs_seq_store_le (x := csrStart + total) (v := initCSRPrefix rows total)
    (Expr.eval_add (Expr.eval_reg_of_eq q13) (Expr.eval_reg_of_eq q9) hCsrTotW)
    (by rw [← hSubPref]; exact Expr.eval_sub (Expr.eval_reg_of_eq q15) (Expr.eval_reg_of_eq q14) hWriteW) ?_
  let m₃ := Function.update st₂.mem (csrStart + total) (initCSRPrefix rows total)
  have hSecAt₃ : ListAt m₃ csrStart sec := by
    change ListAt m₃ csrStart (csrList total rows)
    rw [csrList, listAt_append, length_csrOffsets]
    refine ⟨listAt_csrOffsets_of fun j hj => ?_, ?_⟩
    · rcases Nat.lt_or_eq_of_le hj with hlt | rfl
      · exact (Function.update_of_ne (by omega) _ _).trans (hOff₂ j hlt)
      · simp [m₃, initCSRPrefix]
    · exact WordRAM.ListAt.congr hData₂ fun j hj _ => Function.update_of_ne (by omega) _ _
  have hZero₃ : ZeroFrom m₃ writeEnd := fun y hy =>
    (Function.update_of_ne (by dsimp [writeEnd, dataStart] at hy; omega) _ _).trans (hZero₂ y hy)
  have hFrame₃ : ∀ y < dst, m₃ y = mem y := fun y hy =>
    (Function.update_of_ne (by omega) _ _).trans ((hFrame₂ y (by omega)).trans (hFrame₁ y hy))
  have hSubSec : writeEnd - csrStart = sec.length := by omega
  have hSecW : sec.length < 2 ^ w := by omega
  have hCopyDown := buildCopyProc_meetsDownContract (w := w) hfCopy
  refine runs_seq_call_le hCopyDown (vs := [csrStart, sec.length, dst])
    (by unfold evalArgs
        rw [Expr.eval_reg_of_eq (by simpa using q13)]
        unfold evalArgs
        have hSubE : (Expr.bin .sub (.reg 15) (.reg 13)).eval w { st₂ with mem := m₃ } = some sec.length := by
          rw [← hSubSec]; exact Expr.eval_sub (Expr.eval_reg_of_eq (by simpa using q15))
            (Expr.eval_reg_of_eq (by simpa using q13)) hWriteW
        rw [hSubE]
        unfold evalArgs
        rw [Expr.eval_reg_of_eq (by simpa using q8)]
        rfl)
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl <;> first | exact hCsrW | exact hSecW | exact hWords _ (by simp))
    ⟨csrStart, sec.length, dst, rfl, by omega, hWriteEq ▸ hWriteW, hw1⟩ ?_
  intro _ m₄ _ hPostCopy
  obtain ⟨_, _, _, hEqC, hCopied, hFrC⟩ := hPostCopy
  simp only [List.cons.injEq, and_true] at hEqC
  obtain ⟨rfl, rfl, rfl⟩ := hEqC
  refine runs_ret_le (v := writeEnd) (Expr.eval_reg_of_eq (by simpa using q15)) ?_ ?_
  · refine ⟨g, x, dst, rfl, by change dst + sec.length ≤ writeEnd; omega,
      by dsimp only [Outcome.value]; exact hWriteLe, ?_, ?_, ?_⟩
    · exact fun j hj => (hCopied j hj).trans (hSecAt₃ j hj)
    · exact fun j hj => (hFrC j (Or.inl hj)).trans (hFrame₃ j hj)
    · exact fun y hy => (hFrC y (Or.inr (by dsimp only [Outcome.value] at hy; omega))).trans (hZero₃ y hy)
  · simp only [buildConnAllContract, connAllCostBound, buildCopyDownContract, buildCopyContract,
      List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize, Nat.sub_zero, step1Bound]
    set P := (s * k + G.m + 1) * (d + 1) * (R + 1)
    have hRowP : 8 + 3 * s + s * d ≤ 12 * P := by
      have hS : s ≤ s * k := Nat.le_mul_of_pos_right s (by omega)
      have hsd : s * d ≤ P :=
        (Nat.mul_le_mul (by omega) (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega))
      have hs1 : s ≤ P :=
        ((show s ≤ s * k + G.m + 1 by omega).trans (Nat.le_mul_of_pos_right _ (by omega))).trans
          (Nat.le_mul_of_pos_right _ (by omega))
      have h1P : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr (by dsimp [P]; positivity)
      omega
    have hTotRow : total * (8 + 3 * s + s * d) ≤ 12 * (total * P) := by
      calc total * (8 + 3 * s + s * d) ≤ total * (12 * P) := Nat.mul_le_mul_left _ hRowP
        _ = 12 * (total * P) := by ring
    have hDist2 : total * (17 * (8 + 3 * s + s * d) + 65 + (1 + 8)) =
        17 * (total * (8 + 3 * s + s * d)) + 74 * total := by ring
    have hRHS : (2 * (K * (C + 10) + 280) + 3000) * total * (s * k + G.m + 1) * (d + 1) * (R + 1) =
        (2 * (K * (C + 10) + 280) + 3000) * (total * P) := by dsimp [P]; ring
    have hSplit : (2 * (K * (C + 10) + 280) + 3000) * (total * P) =
        (2 * (K * (C + 10) + 280) + 1500) * (total * P) + 1500 * (total * P) := by ring
    have hSec17 : 17 * sec.length ≤ 17 * total + 17 + 17 * (total * (8 + 3 * s + s * d)) := by
      omega
    have h1 : total * ((2 * (K * (C + 10) + 280) + 1500) * (s * k + G.m + 1) * (d + 1) * (R + 1) + 160 + (1 + 8)) =
        (2 * (K * (C + 10) + 280) + 1500) * (total * P) + 169 * total := by
      dsimp [P]; ring
    change _ ≤ (2 * (K * (C + 10) + 280) + 3000) * total * (s * k + G.m + 1) * (d + 1) * (R + 1) +
      250 * total + 200
    have h1P : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr (by dsimp [P]; positivity)
    have hTotP : total ≤ total * P := Nat.le_mul_of_pos_right total h1P
    rw [h1, hDist2, hRHS, hSplit]
    clear * - hTotRow hSec17 hTotP
    omega

end MinCostFlow.HierPaths
