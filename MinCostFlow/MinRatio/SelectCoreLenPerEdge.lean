module

public import MinCostFlow.MinRatio.SelectCoreLenFill
import WordRAM.Tactic

/-!
# Per-edge execution lemma for `selCoreLenFillBody` (`SelectCoreLenPerEdge`)

Runs `selCoreLenFillBody edgeProc` under per-edge bounds on `(prevBase, numBase, denBase)` rather
than full `eCap * Lw` bounds, matching `LastLevelProgram.BranchWithin` (which bounds
`numBase + e * L + L ≤ limit` and `denBase + e * L + L ≤ limit` for each `e ∈ E`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

private theorem ent_disj_pe {e e' L t : ℕ} (hne : e ≠ e') (ht : t < L) :
    e * L + t < e' * L ∨ e' * L + L ≤ e * L + t := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this; omega
  · right
    have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this; omega

theorem ent_end_pe {e c L : ℕ} (h : e < c) : e * L + L ≤ c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at this; exact this

private theorem selCoreLenEntryOk_congr_pe {P shift L Lw : ℕ} {mem mem' : ℕ → ℕ}
    {prevBase numBase denBase e : ℕ}
    (hok : SelCoreLenEntryOk P shift L Lw mem prevBase numBase denBase e)
    (hp : ∀ t < L, mem' (prevBase + e * L + t) = mem (prevBase + e * L + t))
    (hn : ∀ t < Lw, mem' (numBase + e * Lw + t) = mem (numBase + e * Lw + t))
    (hd : ∀ t < Lw, mem' (denBase + e * Lw + t) = mem (denBase + e * Lw + t)) :
    SelCoreLenEntryOk P shift L Lw mem' prevBase numBase denBase e ∧
      selCoreLenVal mem' P prevBase numBase denBase L Lw e =
        selCoreLenVal mem P prevBase numBase denBase L Lw e := by
  have hfix : ∀ a l p, (∀ t < l, mem' (a + t) = mem (a + t)) →
      (Num.Valid mem' a 4 l ↔ Num.Valid mem a 4 l) ∧
        Num.fixVal mem' a 4 l p = Num.fixVal mem a 4 l p := fun a l p heq =>
    ⟨⟨fun hv t ht => heq t ht ▸ hv t ht, fun hv t ht => (heq t ht).symm ▸ hv t ht⟩, by
      unfold Num.fixVal; rw [Num.intVal_congr heq]⟩
  have cp := hfix (prevBase + e * L) L P hp
  have cn := hfix (numBase + e * Lw) Lw P hn
  have cd := hfix (denBase + e * Lw) Lw P hd
  have hval : selCoreLenVal mem' P prevBase numBase denBase L Lw e =
      selCoreLenVal mem P prevBase numBase denBase L Lw e := by
    unfold selCoreLenVal; rw [cp.2, cn.2, cd.2]
  obtain ⟨v1, v2, v3, hdPos, hshFit, q, hqFit, hqVal⟩ := hok
  refine ⟨⟨cp.1.2 v1, cn.1.2 v2, cd.1.2 v3, cd.2 ▸ hdPos, ?_, q, hqFit, hqVal.trans hval.symm⟩, hval⟩
  rw [Num.intVal_congr hp]; exact hshFit

set_option maxHeartbeats 800000 in
/-- Run `selCoreLenFillBody edgeProc` using per-edge source bounds (instead of full `eCap * Lw`
bounds on `numBase`/`denBase`), returning `heap + L_list.length * selCoreLenEdgeSpace L Lw`. -/
theorem selCoreLenFill_runs_perEdge {w P eCap edgeProc prevBase numBase denBase dst listPtr L Lw
    shift heap pos : ℕ} {L_list : List ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hedge : MeetsContract w p edgeProc (selCoreLenEdgeContract w P))
    (hw16 : 16 < 2 ^ w) (hL_W : L < 2 ^ w) (hLw_W : Lw < 2 ^ w) (hsh_W : shift < 2 ^ w)
    (heCapW : eCap ≤ 2 ^ w)
    (hdstLe : dst + eCap * L ≤ heap) (hlistLe : listPtr + L_list.length ≤ heap)
    (hlistDisj : listPtr + L_list.length ≤ dst ∨ dst + eCap * L ≤ listPtr)
    (hlist : ListAt mem listPtr L_list)
    (hcap : ∀ e ∈ L_list, e < eCap)
    (hprevLe : ∀ e ∈ L_list, prevBase + e * L + L ≤ heap ∧
      (prevBase + e * L + L ≤ dst ∨ dst + eCap * L ≤ prevBase + e * L))
    (hnumLe : ∀ e ∈ L_list, numBase + e * Lw + Lw ≤ heap ∧
      (numBase + e * Lw + Lw ≤ dst ∨ dst + eCap * L ≤ numBase + e * Lw))
    (hdenLe : ∀ e ∈ L_list, denBase + e * Lw + Lw ≤ heap ∧
      (denBase + e * Lw + Lw ≤ dst ∨ dst + eCap * L ≤ denBase + e * Lw))
    (hok : ∀ e ∈ L_list, SelCoreLenEntryOk P shift L Lw mem prevBase numBase denBase e)
    (hz : ZeroFrom mem heap)
    (hroom : heap + L_list.length * selCoreLenEdgeSpace L Lw < 2 ^ w) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω (selCoreLenFillBody edgeProc)
        (startState [prevBase, numBase, denBase, dst, listPtr, L_list.length, L, Lw, shift, heap]
          mem pos)
        (.returned (heap + L_list.length * selCoreLenEdgeSpace L Lw)) out cost ∧
      cost ≤ L_list.length * (selCoreLenEdgeCost L Lw + 40) + 20 ∧
      (∀ e ∈ L_list, Num.Valid out.mem (dst + e * L) 4 L ∧
        Num.fixVal out.mem (dst + e * L) 4 L (P + shift) =
          selCoreLenVal mem P prevBase numBase denBase L Lw e) ∧
      ZeroFrom out.mem (heap + L_list.length * selCoreLenEdgeSpace L Lw) ∧
      (∀ a < heap, (a < dst ∨ dst + eCap * L ≤ a) → out.mem a = mem a) ∧
      (∀ e < eCap, e ∉ L_list → ∀ t < L, out.mem (dst + e * L + t) = mem (dst + e * L + t)) := by
  have hw1 : 1 < 2 ^ w := by omega
  set sp := selCoreLenEdgeSpace L Lw
  have hloop := Triple.forRange_const (p := p) (r := 10) (lo := .const 0) (hi := .reg 5)
    (body := .assign 11 (.load (.bin .add (.reg 4) (.reg 10))) ;;
      .call 9 edgeProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 11, .reg 6, .reg 7, .reg 8, .reg 9])
    (P := fun st =>
      st = startState [prevBase, numBase, denBase, dst, listPtr, L_list.length, L, Lw, shift, heap]
        mem pos)
    (Inv := fun i st =>
      st.regs 0 = prevBase ∧ st.regs 1 = numBase ∧ st.regs 2 = denBase ∧ st.regs 3 = dst ∧
      st.regs 4 = listPtr ∧ st.regs 5 = L_list.length ∧ st.regs 6 = L ∧ st.regs 7 = Lw ∧
      st.regs 8 = shift ∧ st.regs 9 = heap + i * sp ∧ st.regs 10 = i ∧
      ZeroFrom st.mem (heap + i * sp) ∧
      (∀ k < i, ∀ (hk : k < L_list.length),
        Num.Valid st.mem (dst + L_list[k] * L) 4 L ∧
        Num.fixVal st.mem (dst + L_list[k] * L) 4 L (P + shift) =
          selCoreLenVal mem P prevBase numBase denBase L Lw L_list[k]) ∧
      (∀ a < heap, (a < dst ∨ dst + eCap * L ≤ a) → st.mem a = mem a) ∧
      (∀ e < eCap, (∀ k < i, ∀ (hk : k < L_list.length), L_list[k] ≠ e) →
        ∀ t < L, st.mem (dst + e * L + t) = mem (dst + e * L + t)))
    (selCoreLenEdgeCost L Lw + 30) 0 L_list.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simp [startState],
        by simp, by simpa [startState] using hz, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h5 := hi.2.2.2.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hzI, hdone, hfr, hkeep⟩
      have heL : L_list[i] ∈ L_list := List.getElem_mem hi
      have heCap := hcap _ heL
      have heEnd := ent_end_pe (L := L) heCap
      have hspStep : (i + 1) * sp ≤ L_list.length * sp :=
        Nat.mul_le_mul_right sp (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hspStep
      have hread : st.mem (listPtr + i) = L_list[i] := by
        rw [hfr _ (by omega) (by rcases hlistDisj with h | h <;> omega)]; exact hlist i hi
      have hprevK : ∀ t < L, st.mem (prevBase + L_list[i] * L + t) =
          mem (prevBase + L_list[i] * L + t) := fun t ht => by
        obtain ⟨h1', h2'⟩ := hprevLe _ heL
        exact hfr _ (by omega) (by rcases h2' with h | h <;> omega)
      have hnumK : ∀ t < Lw, st.mem (numBase + L_list[i] * Lw + t) =
          mem (numBase + L_list[i] * Lw + t) := fun t ht => by
        obtain ⟨h1', h2'⟩ := hnumLe _ heL
        exact hfr _ (by omega) (by rcases h2' with h | h <;> omega)
      have hdenK : ∀ t < Lw, st.mem (denBase + L_list[i] * Lw + t) =
          mem (denBase + L_list[i] * Lw + t) := fun t ht => by
        obtain ⟨h1', h2'⟩ := hdenLe _ heL
        exact hfr _ (by omega) (by rcases h2' with h | h <;> omega)
      obtain ⟨hokI, hvalI⟩ := selCoreLenEntryOk_congr_pe (hok _ heL) hprevK hnumK hdenK
      have heW : L_list[i] < 2 ^ w := lt_of_lt_of_le heCap heCapW
      have hprevB := (hprevLe _ heL).1
      have hnumB := (hnumLe _ heL).1
      have hdenB := (hdenLe _ heL).1
      apply runs_start_le
      refine runs_seq_assign_le (v := L_list[i]) (by eval_expr) ?_
      refine runs_call_le hedge
        (vs := [prevBase, numBase, denBase, dst, L_list[i], L, Lw, shift, heap + i * sp])
        (by eval_expr) (by wram_words)
        ⟨prevBase, numBase, denBase, dst, L_list[i], L, Lw, shift, heap + i * sp, rfl, hw16,
          by omega, by omega, by omega, by omega, hokI, hzI, by omega⟩ ?_
      intro ret1 mem1 pos1 hp1
      dsimp only [selCoreLenEdgeContract] at hp1
      obtain ⟨hret1, hv1, hf1, hz1, hfr1⟩ := hp1
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hret1 hv1 hf1 hfr1
      have hretEq : ret1 = heap + (i + 1) * sp := by
        rw [hret1, Nat.succ_mul]; change heap + i * sp + sp = heap + (i * sp + sp); omega
      refine ⟨⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4, by simpa using h5, by simpa using h6, by simpa using h7,
        by simpa using h8, by simpa using hretEq, by simp, hretEq ▸ hz1,
        fun k hk hkL => ?_, fun a ha hout => ?_, fun e heC hne t ht => ?_⟩, by simp [h10]⟩, ?_⟩
      · dsimp only
        by_cases hki : L_list[k] = L_list[i]
        · rw [hki]; exact ⟨hv1, hf1.trans hvalI⟩
        · have hkLt : k < i := by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
            · exact hlt
            · exact (hki rfl).elim
          have hekEnd := ent_end_pe (L := L) (hcap _ (List.getElem_mem hkL))
          have hstay : ∀ t < L, mem1 (dst + L_list[k] * L + t) = st.mem (dst + L_list[k] * L + t) :=
            fun t ht => hfr1 _ (by omega) (by rcases ent_disj_pe hki ht with h | h <;> omega)
          obtain ⟨hvk, hfk⟩ := hdone k hkLt hkL
          refine ⟨fun t ht => (hstay t ht) ▸ hvk t ht, ?_⟩
          unfold Num.fixVal; rw [Num.intVal_congr hstay]; exact hfk
      · dsimp only
        exact (hfr1 a (by omega) (by omega)).trans (hfr a ha hout)
      · dsimp only
        have hneI : e ≠ L_list[i] := Ne.symm (hne i (Nat.lt_succ_self i) hi)
        have heEnd' := ent_end_pe (L := L) heC
        rw [hfr1 _ (by omega) (by rcases ent_disj_pe hneI ht with h | h <;> omega)]
        exact hkeep e heC (fun k hk hkL => hne k (Nat.lt_succ_of_lt hk) hkL) t ht
      · simp only [selCoreLenEdgeContract, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_reg, Expr.size_bin, Expr.size_load, argsSize_cons, argsSize_nil]
        omega)
  have hRun : ∃ o out cost,
      Runs w p ω (selCoreLenFillBody edgeProc)
        (startState [prevBase, numBase, denBase, dst, listPtr, L_list.length, L, Lw, shift, heap]
          mem pos) o out cost ∧
      (o = .returned (heap + L_list.length * sp) ∧
        (∀ e ∈ L_list, Num.Valid out.mem (dst + e * L) 4 L ∧
          Num.fixVal out.mem (dst + e * L) 4 L (P + shift) =
            selCoreLenVal mem P prevBase numBase denBase L Lw e) ∧
        ZeroFrom out.mem (heap + L_list.length * sp) ∧
        (∀ a < heap, (a < dst ∨ dst + eCap * L ≤ a) → out.mem a = mem a) ∧
        (∀ e < eCap, e ∉ L_list → ∀ t < L, out.mem (dst + e * L + t) = mem (dst + e * L + t))) ∧
      cost ≤ L_list.length * (selCoreLenEdgeCost L Lw + 40) + 20 := by
    apply runs_start_le
    unfold selCoreLenFillBody
    refine runs_seq_triple_le hloop rfl ?_
    intro st1 ⟨_, _, _, _, _, _, _, _, _, h9, _, hz1, hdone, hfr, hkeep⟩
    refine WordRAM.runs_ret_le (v := heap + L_list.length * sp) (by eval_expr) ?_ ?_
    · refine ⟨rfl, fun e he => ?_, hz1, hfr, fun e heC hnot => hkeep e heC fun k _ hk heq =>
        hnot (heq ▸ List.getElem_mem hk)⟩
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
      exact hdone k hk hk
    · simp only [Expr.size, Nat.sub_zero]; nlinarith
  obtain ⟨_, out, cost, hr, ⟨rfl, hd, hz', hfr', hk'⟩, hc⟩ := hRun
  exact ⟨out, cost, hr, hc, hd, hz', hfr', hk'⟩

end MinCostFlow.MinRatio
