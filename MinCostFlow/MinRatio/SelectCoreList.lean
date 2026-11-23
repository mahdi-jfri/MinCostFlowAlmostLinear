module

public import MinCostFlow.MinRatio.SelectBlocksParts
import WordRAM.Tactic

/-!
# The edge list of the active core (`SelectCoreList`)

At a rebuild or a shift of level `j < d`, the embedding slots of level `j` are filled for every
edge of the active core (`SelectEmbCopy.lean`). The copy takes the edges as a list. The edges of
the active core are the edges of `G_j` that are not in the forest `F_j`
(`coreGraph`, `(C.activeCore j).E = (C.G j).E \ F_j.E`). The readouts give no such list, but the
graph `G_j` has a live edge list, and the block of `F_j` has a presence bit for every edge name
(`DynGraphAt`). This file keeps the listed edges whose presence bit is `0`, in `O(m_j)` steps.

* `selFilterAbsentBody` (`[listPtr, len, presBase, outPtr]`): writes the listed edges `e` with
  `mem (presBase + e) = 0` to `outPtr`, in order, and returns how many there are.
* `selFilterAbsent_meetsContract`: the words at `outPtr` hold `selAbsent mem presBase L`, and
  every other word is kept. Cost `40 len + 20`.
* `mem_selAbsent_iff`: with the presence bits of a `DynGraphAt` block of `F`, and a list of the
  edges of `G` below the cap, the kept edges are the edges of `G` not in `F`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program

/-- Keep the listed edges whose presence bit is `0` (`[listPtr, len, presBase, outPtr]`). -/
def selFilterAbsentBody : Stmt :=
  .assign 4 (.const 0) ;;
  forRange 5 (.const 0) (.reg 1)
    (.assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
     .cond (.load (.bin .add (.reg 2) (.reg 6))) .nop
       (.store (.bin .add (.reg 3) (.reg 4)) (.reg 6) ;;
        .assign 4 (.bin .add (.reg 4) (.const 1)))) ;;
  .ret (.reg 4)

theorem selFilterAbsentBody_noRand : selFilterAbsentBody.NoRand := by
  simp [selFilterAbsentBody, forRange, forUp, Stmt.NoRand]

/-- The listed edges whose presence bit at `presBase` is `0`. -/
def selAbsent (mem : ℕ → ℕ) (presBase : ℕ) (L : List ℕ) : List ℕ :=
  L.filter fun e => mem (presBase + e) = 0

/-- Contract of `selFilterAbsentBody` for the list `L`. The output lies off the list and off the
presence bits of the listed edges. -/
def selFilterAbsentContract (w : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ listPtr presBase outPtr, args = [listPtr, L.length, presBase, outPtr] ∧
    16 < 2 ^ w ∧ listPtr + L.length < 2 ^ w ∧ outPtr + L.length < 2 ^ w ∧
    (listPtr + L.length ≤ outPtr ∨ outPtr + L.length ≤ listPtr) ∧
    ListAt mem listPtr L ∧
    (∀ e ∈ L, e < 2 ^ w ∧ presBase + e < 2 ^ w ∧ mem (presBase + e) < 2 ^ w ∧
      (presBase + e < outPtr ∨ outPtr + L.length ≤ presBase + e))
  post args mem ret mem' := ∃ listPtr presBase outPtr,
    args = [listPtr, L.length, presBase, outPtr] ∧
    ret = (selAbsent mem presBase L).length ∧ ListAt mem' outPtr (selAbsent mem presBase L) ∧
    ∀ a, (a < outPtr ∨ outPtr + L.length ≤ a) → mem' a = mem a
  cost _ _ := 40 * L.length + 20

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM DynSpanner.Program

theorem selAbsent_take_succ (mem : ℕ → ℕ) (presBase : ℕ) (L : List ℕ) {i : ℕ}
    (hi : i < L.length) :
    selAbsent mem presBase (L.take (i + 1)) =
      selAbsent mem presBase (L.take i) ++ (if mem (presBase + L[i]) = 0 then [L[i]] else []) := by
  unfold selAbsent
  rw [List.take_succ_eq_append_getElem hi, List.filter_append]
  congr 1
  by_cases h : mem (presBase + L[i]) = 0 <;> simp [h]

theorem selAbsent_length_le (mem : ℕ → ℕ) (presBase : ℕ) (L : List ℕ) :
    (selAbsent mem presBase L).length ≤ L.length :=
  List.length_filter_le _ _

set_option maxHeartbeats 400000 in
/-- `selFilterAbsentBody` meets `selFilterAbsentContract`. -/
theorem selFilterAbsent_meetsContract {w proc : ℕ} {L : List ℕ} {p : Program}
    (hp : p.procs[proc]? = some selFilterAbsentBody) :
    MeetsContract w p proc (selFilterAbsentContract w L) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨listPtr, presBase, outPtr, rfl, hw16, hlistW, houtW, hldisj, hlist, hent⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hloop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 1)
    (body := .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
      .cond (.load (.bin .add (.reg 2) (.reg 6))) .nop
        (.store (.bin .add (.reg 3) (.reg 4)) (.reg 6) ;;
          .assign 4 (.bin .add (.reg 4) (.const 1))))
    (P := fun st => st = { startState [listPtr, L.length, presBase, outPtr] mem pos with
      regs := Function.update (startState [listPtr, L.length, presBase, outPtr] mem pos).regs 4 0 })
    (Inv := fun i st => st.regs 0 = listPtr ∧ st.regs 1 = L.length ∧ st.regs 2 = presBase ∧
      st.regs 3 = outPtr ∧ st.regs 5 = i ∧
      st.regs 4 = (selAbsent mem presBase (L.take i)).length ∧
      ListAt st.mem outPtr (selAbsent mem presBase (L.take i)) ∧
      (∀ a, (a < outPtr ∨ outPtr + L.length ≤ a) → st.mem a = mem a))
    30 0 L.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr, ⟨rfl, rfl, rfl, rfl, by simp, by simp [selAbsent], ?_,
        fun _ _ => rfl⟩⟩
      intro t ht; simp [selAbsent] at ht)
    (fun _ _ _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by have h1 := hi.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, h5, h4, hdone, hout⟩
      have heL : L[i] ∈ L := List.getElem_mem hi
      obtain ⟨heW, hpW, hbW, hpd⟩ := hent _ heL
      have hcnt : (selAbsent mem presBase (L.take i)).length ≤ i := by
        have := selAbsent_length_le mem presBase (L.take i)
        simp only [List.length_take] at this; omega
      have hread : st.mem (listPtr + i) = L[i] := by
        rw [hout _ (by rcases hldisj with h | h <;> omega)]
        exact hlist i hi
      have hbit : st.mem (presBase + L[i]) = mem (presBase + L[i]) := hout _ hpd
      have hstep := selAbsent_take_succ mem presBase L hi
      apply runs_start_le
      refine runs_seq_assign_le (v := L[i]) (by eval_expr) ?_
      have hbW' : st.mem (presBase + L[i]) < 2 ^ w := hbit ▸ hbW
      refine WordRAM.runs_cond_le (v := mem (presBase + L[i])) (by rw [← hbit]; eval_expr) ?_ ?_
      · -- Present in `F`: nothing is written.
        intro hne
        refine runs_nop_le ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2,
          by simpa using h3, by simp, ?_, ?_, hout⟩, by simpa using h5⟩ ?_
        · simp only [Function.update_of_ne (show (4 : ℕ) ≠ 5 by decide),
            Function.update_of_ne (show (4 : ℕ) ≠ 6 by decide), h4, hstep, ite_eq_right hne,
            List.append_nil]
        · rw [hstep, ite_eq_right hne, List.append_nil]; exact hdone
        · simp only [Expr.size_reg, Expr.size_bin, Expr.size_load]; omega
      · -- Absent from `F`: write `e` at the end of the output.
        intro hz
        have hk : outPtr + (selAbsent mem presBase (L.take i)).length < 2 ^ w := by omega
        refine runs_seq_store_le (x := outPtr + (selAbsent mem presBase (L.take i)).length)
          (v := L[i]) (by eval_expr) (by eval_expr) ?_
        refine runs_assign_le (v := (selAbsent mem presBase (L.take i)).length + 1)
          (by eval_expr) ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2,
            by simpa using h3, by simp, ?_, ?_, fun a ha => ?_⟩, by simpa using h5⟩ ?_
        · simp [hstep, hz]
        · rw [hstep, ite_eq_left hz]
          intro t ht
          simp only [List.length_append, List.length_singleton] at ht
          dsimp only
          rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | rfl
          · rw [Function.update_of_ne (by omega), hdone t hlt, List.getElem_append_left hlt]
          · rw [Function.update_self, List.getElem_append_right (le_refl _)]
            simp
        · dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hout a ha
        · simp only [Expr.size_reg, Expr.size_bin, Expr.size_load, Expr.size_const]; omega)
  apply runs_start_le
  unfold selFilterAbsentBody
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  refine runs_seq_triple_le hloop rfl ?_
  intro st1 ⟨_, _, _, _, _, h4, hdone, hout⟩
  rw [List.take_length] at h4 hdone
  refine WordRAM.runs_ret_le (v := (selAbsent mem presBase L).length) (by eval_expr) ?_ ?_
  · exact ⟨listPtr, presBase, outPtr, rfl, rfl, hdone, hout⟩
  · simp only [selFilterAbsentContract, Expr.size, Nat.sub_zero]
    omega

/-- **The kept edges are the edges of `G` not in `F`.** Let `L` list the edges of `G`, below the
cap `eCap`, and let `presBase` be the presence bits of a `DynGraphAt` block of `F` with the same
cap. Then an edge is kept exactly when it is in `G` and not in `F`. -/
theorem mem_selAbsent_iff {mem : ℕ → ℕ} {fBase vCap eCap : ℕ} {F G : MGraph} {L : List ℕ}
    (hF : DynGraphAt mem fBase vCap eCap F) (hL : ∀ e, e ∈ L ↔ e ∈ G.E)
    (hcap : ∀ e ∈ G.E, e < eCap) (e : ℕ) :
    e ∈ selAbsent mem (dgEPresBase fBase vCap) L ↔ e ∈ G.E \ F.E := by
  unfold selAbsent
  rw [List.mem_filter, Finset.mem_sdiff, hL]
  constructor
  · rintro ⟨he, hz⟩
    have hbit := hF.2.2.2.2.2.2.2.2.2.2.2.1 e (hcap e he)
    refine ⟨he, fun hf => ?_⟩
    rw [ite_eq_left hf] at hbit
    simp [hbit] at hz
  · rintro ⟨he, hf⟩
    have hbit := hF.2.2.2.2.2.2.2.2.2.2.2.1 e (hcap e he)
    rw [ite_eq_right hf] at hbit
    exact ⟨he, by simp [hbit]⟩

end MinCostFlow.MinRatio
