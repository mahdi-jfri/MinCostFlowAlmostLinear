module


public import MinCostFlow.DynSpanner.Program.StateLayout
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import MinCostFlow.DynSpanner.Program.DynGraphDelete
import MinCostFlow.DynSpanner.Program.DynGraphInsert

/-!
# Part 1 of `DynSpannerPhase`

The first part of the proofs of `DynSpannerPhase.lean`, split off to keep files short. See `DynSpannerPhase.lean`
for the overview.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Procedure indices -/

def phaseIdxChooseLevel : ℕ := 0
def phaseIdxClearAux : ℕ := 1
def phaseIdxBuildActive : ℕ := 2
def phaseIdxHBucketCons : ℕ := 3
def phaseIdxHBucketRemove : ℕ := 4

/-! ## Pure helper arithmetic for `chooseLevel` -/

lemma chooseLevel_zero (L q : ℕ) : chooseLevel L q 0 = 0 := by
  unfold chooseLevel
  rw [List.range_succ_eq_map]
  simp

private lemma chooseLevel_loop_inv {L q t j B : ℕ} (hq : 1 ≤ q) (ht : 0 < t)
    (hjL : j ≤ L) (hB : B = q ^ (L - j))
    (hnext : B ≤ t / q → ¬ (B * q ∣ t)) :
    ∀ k : ℕ, k < j → ¬ (phasePeriod q L k ∣ t) := by
  intro k hk hkd
  have h1 : B * q ∣ phasePeriod q L k := by
    unfold phasePeriod
    rw [hB]
    have hexp : L - j + 1 ≤ L - k := by omega
    rw [← pow_succ q (L - j)]
    exact Nat.pow_dvd_pow q hexp
  have hdvd_next : B * q ∣ t := dvd_trans h1 hkd
  by_cases hBq : B ≤ t / q
  · exact hnext hBq hdvd_next
  · have hdiv_lt : t / q < B := Nat.lt_of_not_ge hBq
    have hdiv_mod := Nat.div_add_mod t q
    have hmod_lt : t % q < q := Nat.mod_lt t (by omega)
    have hsucc : q * (t / q + 1) = q * (t / q) + q := Nat.mul_succ q (t / q)
    have hmul : q * (t / q + 1) ≤ q * B := Nat.mul_le_mul_left q (by omega)
    have hle := Nat.le_of_dvd ht hdvd_next
    have hcomm : B * q = q * B := Nat.mul_comm B q
    omega

lemma chooseLevel_eq_of_dvd_not_pred {L q t j : ℕ} (hq : 1 ≤ q) (hjL : j ≤ L)
    (hdvd : phasePeriod q L j ∣ t)
    (hno : ∀ k : ℕ, k < j → ¬ (phasePeriod q L k ∣ t)) :
    chooseLevel L q t = j := by
  apply le_antisymm
  · exact (chooseLevel_le_iff_dvd hq hjL).mpr hdvd
  · by_contra hlt
    have hk := Nat.lt_of_not_ge hlt
    exact hno _ hk (chooseLevel_dvd L q t)

/-! ## Word-RAM statement bodies -/

/-- `args = [L, q, t]`: returns `chooseLevel L q t`. Assumes `1 ≤ q` and `L, q, t < 2 ^ w`. -/
def chooseLevelStmt : Stmt :=
  .cond (.bin .eq (.reg 2) (.const 0))
    (.ret (.const 0))
    (.assign 3 (.reg 0) ;;
     .assign 4 (.const 1) ;;
     .assign 5 (.bin .div (.reg 2) (.reg 1)) ;;
     .assign 6 (.const 1) ;;
     .loop (.reg 6)
       (.cond (.bin .lt (.const 0) (.reg 3))
         (.cond (.bin .lt (.reg 5) (.reg 4))
           (.assign 6 (.const 0))
           (.assign 7 (.bin .mul (.reg 4) (.reg 1)) ;;
            .cond (.bin .eq (.bin .mod (.reg 2) (.reg 7)) (.const 0))
              (.assign 4 (.reg 7) ;;
               .assign 3 (.bin .sub (.reg 3) (.const 1)))
              (.assign 6 (.const 0))))
         (.assign 6 (.const 0))) ;;
     .ret (.reg 3))

/-- `args = [auxPtr]`: clears `DynGraphAt mem auxPtr vCap eCap A` back to `emptyMGraph`
in `O(A.m + A.n + 1)` time without scanning `vCap` or `eCap`. -/
def clearAuxGraphStmt (bEdge : ℕ) : Stmt :=
  .assign 1 (.load (.reg 0)) ;;
  .assign 2 (.load (.bin .add (.reg 0) (.const dgECapOff))) ;;
  .assign 3 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 1))) ;;
  .assign 4 (.bin .add (.reg 3) (.reg 2)) ;;
  .loop (.bin .lt (.const 0) (.load (.bin .add (.reg 0) (.const dgMOff))))
    (.assign 5 (.load (.reg 4)) ;;
     .call 6 (bEdge + dgIdxDeleteEdge) [.reg 0, .reg 5]) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dgNOff))) ;;
  .assign 6 (.bin .add (.reg 0) (.const 4)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 1)) ;;
  forRange 8 (.const 0) (.reg 5)
    (.assign 9 (.load (.bin .add (.reg 7) (.reg 8))) ;;
     .store (.bin .add (.reg 6) (.reg 9)) (.const 0)) ;;
  .store (.bin .add (.reg 0) (.const dgNOff)) (.const 0) ;;
  .ret (.const 0)

/-- `args = [gPtr, auxPtr]`: builds `activeSubgraph G` at `auxPtr` from `DynGraphAt mem gPtr`
and empty `DynGraphAt mem auxPtr` in `O(G.m + 1)` time. -/
def buildActiveOnAuxStmt (bOps bEdge : ℕ) : Stmt :=
  .assign 2 (.load (.reg 0)) ;;
  .assign 3 (.load (.bin .add (.reg 0) (.const dgECapOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const dgMOff))) ;;
  .assign 5 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 7) (.reg 2))) (.reg 3)) ;;
  forRange 6 (.const 0) (.reg 4)
    (.assign 7 (.load (.bin .add (.reg 5) (.reg 6))) ;;
     .call 8 (bOps + dgIdxGetTail) [.reg 0, .reg 7] ;;
     .call 9 (bOps + dgIdxGetHead) [.reg 0, .reg 7] ;;
     .call 10 (bOps + dgIdxAddVertex) [.reg 1, .reg 8] ;;
     .call 10 (bOps + dgIdxAddVertex) [.reg 1, .reg 9] ;;
     .call 10 (bEdge + dgIdxInsertEdge) [.reg 1, .reg 7, .reg 8, .reg 9]) ;;
  .ret (.const 0)

/-- `args = [b, i, e]`: pushes `e` onto `hBuckets[i]` and sets `minH[e] := i + 1`. -/
def hBucketConsStmt (bOps : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 6 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize))
    (.bin .mul (.const 3)
      (.bin .add (.const 4)
        (.bin .add (.bin .mul (.const 7) (.reg 3)) (.bin .mul (.const 9) (.reg 4)))))) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 4)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 4)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 4)) ;;
  .assign 10 (.bin .add (.reg 9) (.bin .add (.reg 5) (.const 1))) ;;
  .store (.bin .add (.reg 6) (.reg 2)) (.bin .add (.reg 1) (.const 1)) ;;
  .call 11 (bOps + dgIdxDllCons)
    [.reg 8, .reg 7, .bin .add (.reg 9) (.reg 1), .bin .add (.reg 10) (.reg 1), .reg 2] ;;
  .ret (.const 0)

/-- `args = [b, i, e]`: removes `e` from `hBuckets[i]` and clears `minH[e] := 0`. -/
def hBucketRemoveStmt (bOps : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
  .assign 6 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize))
    (.bin .mul (.const 3)
      (.bin .add (.const 4)
        (.bin .add (.bin .mul (.const 7) (.reg 3)) (.bin .mul (.const 9) (.reg 4)))))) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 4)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 4)) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 4)) ;;
  .assign 10 (.bin .add (.reg 9) (.bin .add (.reg 5) (.const 1))) ;;
  .store (.bin .add (.reg 6) (.reg 2)) (.const 0) ;;
  .call 11 (bOps + dgIdxDllRemove)
    [.reg 8, .reg 7, .bin .add (.reg 9) (.reg 1), .bin .add (.reg 10) (.reg 1), .reg 2] ;;
  .ret (.const 0)

/-- Phase helper module (`5` deterministic procedures). -/
def phaseProcs (bOps bEdge : ℕ) : List Stmt :=
  [ chooseLevelStmt
  , clearAuxGraphStmt bEdge
  , buildActiveOnAuxStmt bOps bEdge
  , hBucketConsStmt bOps
  , hBucketRemoveStmt bOps ]

lemma phaseProcs_length (bOps bEdge : ℕ) : (phaseProcs bOps bEdge).length = 5 := rfl

lemma phaseProcs_noRand (bOps bEdge : ℕ) : ∀ s ∈ phaseProcs bOps bEdge, s.NoRand := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  rcases List.mem_cons.mp hs with rfl | hs; · trivial
  cases hs

/-! ## Contracts -/

/-- Contract for `chooseLevelStmt` (`[L, q, t]`). -/
def chooseLevelContract (w : ℕ) (L q t : ℕ) : Contract where
  pre args _mem := args = [L, q, t] ∧ 16 ≤ 2 ^ w ∧ 1 ≤ q ∧ L < 2 ^ w ∧ q < 2 ^ w ∧ t < 2 ^ w
  post args mem ret mem' := args = [L, q, t] ∧ mem' = mem ∧ ret = chooseLevel L q t
  cost _ _ := 35 * L + 60

/-- Contract for `clearAuxGraphStmt` (`[auxPtr]`). -/
def clearAuxGraphContract (w vCap eCap : ℕ) (A : MGraph) : Contract where
  pre args mem := ∃ auxPtr,
    args = [auxPtr] ∧ 16 ≤ 2 ^ w ∧ auxPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    DynGraphAt mem auxPtr vCap eCap A
  post args mem ret mem' := ∃ auxPtr,
    args = [auxPtr] ∧ ret = 0 ∧
    DynGraphAt mem' auxPtr vCap eCap emptyMGraph ∧
    ∀ addr, addr < auxPtr ∨ auxPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost _ _ := 500 * A.m + 30 * A.n + 80

/-- Contract for `buildActiveOnAuxStmt` (`[gPtr, auxPtr]`). -/
def buildActiveOnAuxContract (w vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ gPtr auxPtr,
    args = [gPtr, auxPtr] ∧ 16 ≤ 2 ^ w ∧
    gPtr + dynGraphSize vCap eCap < 2 ^ w ∧ auxPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    (gPtr + dynGraphSize vCap eCap ≤ auxPtr ∨ auxPtr + dynGraphSize vCap eCap ≤ gPtr) ∧
    DynGraphAt mem gPtr vCap eCap G ∧
    DynGraphAt mem auxPtr vCap eCap emptyMGraph
  post args mem ret mem' := ∃ gPtr auxPtr,
    args = [gPtr, auxPtr] ∧ ret = 0 ∧
    DynGraphAt mem' auxPtr vCap eCap (activeSubgraph G) ∧
    ∀ addr, addr < auxPtr ∨ auxPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost _ _ := 900 * G.m + 60

/-- Contract for `hBucketConsStmt` (`[b, i, e]`). -/
def hBucketConsContract (w L vCap eCap b : ℕ) (L_buck : List ℕ) (i e : ℕ) : Contract where
  pre args mem :=
    args = [b, i, e] ∧ 16 ≤ 2 ^ w ∧ b + dsFixedSize L vCap eCap < 2 ^ w ∧
    i ≤ L ∧ e < eCap ∧ e ∉ L_buck ∧
    mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
    IsDoublyLinkedList mem (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap + i) eCap L_buck ∧
    mem (dsHDegDummyBase b L vCap eCap + i) = L_buck.length
  post args mem ret mem' :=
    args = [b, i, e] ∧ ret = 0 ∧
    mem' (dsMinHBase b vCap eCap + e) = i + 1 ∧
    IsDoublyLinkedList mem' (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap + i) eCap (e :: L_buck) ∧
    mem' (dsHDegDummyBase b L vCap eCap + i) = L_buck.length + 1 ∧
    ∀ addr,
      addr ≠ dsMinHBase b vCap eCap + e →
      addr ≠ dsHHeadBase b vCap eCap + i →
      addr ≠ dsHDegDummyBase b L vCap eCap + i →
      (∀ x, addr = dsHPrevBase b vCap eCap + x → x ∉ e :: L_buck) →
      (∀ x, addr = dsHNextBase b vCap eCap + x → x ∉ e :: L_buck) →
      mem' addr = mem addr
  cost _ _ := 180

/-- Contract for `hBucketRemoveStmt` (`[b, i, e]`). -/
def hBucketRemoveContract (w L vCap eCap b : ℕ) (L_buck : List ℕ) (i e : ℕ) : Contract where
  pre args mem :=
    args = [b, i, e] ∧ 16 ≤ 2 ^ w ∧ b + dsFixedSize L vCap eCap < 2 ^ w ∧
    i ≤ L ∧ e < eCap ∧ e ∈ L_buck ∧
    mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
    IsDoublyLinkedList mem (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap + i) eCap L_buck ∧
    mem (dsHDegDummyBase b L vCap eCap + i) = L_buck.length
  post args mem ret mem' :=
    args = [b, i, e] ∧ ret = 0 ∧
    mem' (dsMinHBase b vCap eCap + e) = 0 ∧
    IsDoublyLinkedList mem' (dsHPrevBase b vCap eCap) (dsHNextBase b vCap eCap)
      (dsHHeadBase b vCap eCap + i) eCap (L_buck.erase e) ∧
    mem' (dsHDegDummyBase b L vCap eCap + i) = L_buck.length - 1 ∧
    ∀ addr,
      addr ≠ dsMinHBase b vCap eCap + e →
      addr ≠ dsHHeadBase b vCap eCap + i →
      addr ≠ dsHDegDummyBase b L vCap eCap + i →
      (∀ x, addr = dsHPrevBase b vCap eCap + x → x ∉ L_buck) →
      (∀ x, addr = dsHNextBase b vCap eCap + x → x ∉ L_buck) →
      mem' addr = mem addr
  cost _ _ := 185

/-! ## Shared graph & doubly-linked list helpers -/

lemma dynGraphAt_congr {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G₁ G₂ : MGraph}
    (hV : G₁.V = G₂.V) (hE : G₁.E = G₂.E)
    (hEnds : ∀ e ∈ G₁.E, G₁.tail e = G₂.tail e ∧ G₁.head e = G₂.head e)
    (hG : DynGraphAt mem a vCap eCap G₁) :
    DynGraphAt mem a vCap eCap G₂ := by
  rcases hG with ⟨hval, hvC, heC, h0, h1, h2, h3, hvp, hvL, heti, hite, hep, heL, hets, hinc⟩
  have hn : G₁.n = G₂.n := by simp [MGraph.n, hV]
  have hm : G₁.m = G₂.m := by simp [MGraph.m, hE]
  refine ⟨?_, ?_, ?_, h0, h1, hn ▸ h2, hm ▸ h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    have he1 : e ∈ G₁.E := hE ▸ he
    obtain ⟨ht, hh⟩ := hEnds e he1
    rw [← ht, ← hh, ← hV]
    exact hval e he1
  · intro v hv; exact hvC v (hV ▸ hv)
  · intro e he; exact heC e (hE ▸ he)
  · intro v hv; simpa [hV] using hvp v hv
  · rcases hvL with ⟨vL, hlen, hnd, hmem, hat, hpos⟩
    exact ⟨vL, hn ▸ hlen, hnd, fun v => (hmem v).trans (by simp [hV]), hat, hpos⟩
  · intro v hv; simpa [hV] using heti v (hV ▸ hv)
  · intro s hs; simpa [hV] using hite s (hV ▸ hs)
  · intro e he; simpa [hE] using hep e he
  · rcases heL with ⟨eL, hlen, hnd, hmem, hat, hpos⟩
    exact ⟨eL, hm ▸ hlen, hnd, fun e => (hmem e).trans (by simp [hE]), hat, hpos⟩
  · intro e he
    have he1 : e ∈ G₁.E := hE ▸ he
    obtain ⟨ht, hh⟩ := hEnds e he1
    rw [← ht, ← hh]
    exact hets e he1
  · rcases hinc with ⟨incL, hincL⟩
    exact ⟨incL, fun s hs => by simpa [hE] using hincL s hs⟩

lemma dll_length_le_cap {mem : ℕ → ℕ} {prev next head cap : ℕ} {L : List ℕ}
    (h : IsDoublyLinkedList mem prev next head cap L) : L.length ≤ cap := by
  have h1 : L.length = L.toFinset.card := (List.toFinset_card_of_nodup h.1).symm
  have h2 : L.toFinset ⊆ Finset.range cap := fun x hx =>
    Finset.mem_range.mpr (h.2.1 x (List.mem_toFinset.mp hx))
  have hc := Finset.card_le_card h2
  have hlen : L.length ≤ (Finset.range cap).card := by simpa [h1] using hc
  simpa using hlen

lemma dll_length_succ_le_cap {mem : ℕ → ℕ} {prev next head cap e : ℕ} {L : List ℕ}
    (h : IsDoublyLinkedList mem prev next head cap L) (he : e < cap) (hne : e ∉ L) :
    L.length + 1 ≤ cap := by
  have hnd : (e :: L).Nodup := List.nodup_cons.mpr ⟨hne, h.1⟩
  have h1 : (e :: L).length = (e :: L).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
  have h2 : (e :: L).toFinset ⊆ Finset.range cap := fun x hx => by
    rcases List.mem_cons.mp (List.mem_toFinset.mp hx) with rfl | hxL
    · exact Finset.mem_range.mpr he
    · exact Finset.mem_range.mpr (h.2.1 x hxL)
  have hc := Finset.card_le_card h2
  have hlen : (e :: L).length ≤ (Finset.range cap).card := by simpa [h1] using hc
  simpa using hlen

/-! ## Verification proofs -/

theorem chooseLevel_meetsContract {w L q t : ℕ} {p : Program} {bPhase bOps bEdge : ℕ}
    (hp : p.HasAt bPhase (phaseProcs bOps bEdge)) :
    MeetsContract w p (bPhase + phaseIdxChooseLevel) (chooseLevelContract w L q t) := by
  refine meetsContract_of_runs
    (hp.get (i := phaseIdxChooseLevel) (by simp [phaseProcs, phaseIdxChooseLevel]))
    fun args mem pos _ _ hpre => ?_
  rcases hpre with ⟨rfl, hw16, hq1, hLw, hqw, htw⟩
  have h0w : (0 : ℕ) < 2 ^ w := by omega
  have h1w : (1 : ℕ) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [phaseProcs, phaseIdxChooseLevel, List.getElem_cons_zero, chooseLevelStmt]
  by_cases ht0 : t = 0
  · subst ht0
    refine runs_cond_le (v := 1) ?_
      (fun _ => runs_ret_le (by eval_expr) ⟨rfl, rfl, (chooseLevel_zero L q).symm⟩
        (by dsimp only [chooseLevelContract, Expr.size]; omega))
      (fun h => False.elim (by omega))
    simp [Expr.eval, BinOp.eval, startState, h0w, h1w]
  · have ht_pos : 0 < t := Nat.pos_of_ne_zero ht0
    have hdiv_lt : t / q < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self t q) htw
    refine runs_cond_le (v := 0) ?_ (fun h => False.elim (by omega)) (fun _ => ?_)
    · simp [Expr.eval, BinOp.eval, startState, h0w, ht0]
    refine runs_seq_assign_le (v := L) (by eval_expr) ?_
    refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
    refine runs_seq_assign_le (v := t / q) ?_ ?_
    · simp [Expr.eval, BinOp.eval, startState, hdiv_lt]
    refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
    let InvC : State → Prop := fun st =>
      ∃ j B flag,
        j ≤ L ∧ B = q ^ (L - j) ∧ phasePeriod q L j ∣ t ∧
        B ≤ t ∧ (flag = 0 ∨ flag = 1) ∧
        (flag = 0 → ∀ k < j, ¬ phasePeriod q L k ∣ t) ∧
        st.mem = mem ∧ st.regs 0 = L ∧ st.regs 1 = q ∧ st.regs 2 = t ∧
        st.regs 3 = j ∧ st.regs 4 = B ∧ st.regs 5 = t / q ∧ st.regs 6 = flag
    have hLoop : Triple w p InvC
        (.loop (.reg 6)
          (.cond (.bin .lt (.const 0) (.reg 3))
            (.cond (.bin .lt (.reg 5) (.reg 4))
              (.assign 6 (.const 0))
              (.assign 7 (.bin .mul (.reg 4) (.reg 1)) ;;
               .cond (.bin .eq (.bin .mod (.reg 2) (.reg 7)) (.const 0))
                 (.assign 4 (.reg 7) ;;
                  .assign 3 (.bin .sub (.reg 3) (.const 1)))
                 (.assign 6 (.const 0))))
            (.assign 6 (.const 0))))
        (normalPost fun st =>
          ∃ j, j ≤ L ∧ phasePeriod q L j ∣ t ∧ (∀ k < j, ¬ phasePeriod q L k ∣ t) ∧
            st.mem = mem ∧ st.regs 3 = j)
        (fun st => ((.reg 6 : Expr).size + 28 + 1) * (st.regs 3 + st.regs 6) +
          (.reg 6 : Expr).size + 1) := by
      refine Triple.loop_const_normal
        (m := fun st => st.regs 3 + st.regs 6) (condVal := fun st => st.regs 6) (bodyBound := 28)
        (fun _ ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr6⟩ => by simp [Expr.eval, hr6])
        (fun st ⟨j, _, _, hjL, _, hdvd, _, _, hno, hm, _, _, _, hr3, _, _, hr6⟩ hv =>
          ⟨j, hjL, hdvd, hno (hr6 ▸ hv), hm, hr3⟩)
        (fun st ⟨j, B, flag, hjL, hB, hdvd, hBt, hfl, hno, hm, hr0, hr1, hr2, hr3, hr4, hr5, hr6⟩ hv => by
          intro s ω hs
          rw [hs]
          refine runs_start_le ?_
          have hfl1 : flag = 1 := by rcases hfl with rfl | rfl <;> [exact absurd hr6 hv; rfl]
          subst hfl1
          have hBw : B < 2 ^ w := lt_of_le_of_lt hBt htw
          by_cases hj0 : 0 < j
          · refine runs_cond_le (v := 1) ?_ ?_ (fun h => False.elim (by omega))
            · simp [Expr.eval, BinOp.eval, h0w, h1w, hr3, hj0]
            intro _
            by_cases hdivB : t / q < B
            · have hno_next := chooseLevel_loop_inv hq1 ht_pos hjL hB
                (fun hle => absurd hle (Nat.not_le_of_gt hdivB))
              refine runs_cond_le (v := 1) ?_ ?_ (fun h => False.elim (by omega))
              · simp [Expr.eval, BinOp.eval, h1w, hr4, hr5, hdivB]
              intro _
              refine runs_assign_le (v := 0) (by eval_expr) ?_
                (by dsimp only [Expr.size]; omega)
              refine ⟨⟨j, B, 0, hjL, hB, hdvd, hBt, Or.inl rfl, fun _ => hno_next,
                hm, hr0, hr1, hr2, hr3, hr4, hr5, by simp⟩, by simp [hr3, hr6]⟩
            · have hle_div : B ≤ t / q := Nat.le_of_not_gt hdivB
              have hBq_le : B * q ≤ t := by
                calc B * q ≤ (t / q) * q := Nat.mul_le_mul_right _ hle_div
                  _ ≤ t := Nat.div_mul_le_self t q
              have hBq_ltw : B * q < 2 ^ w := lt_of_le_of_lt hBq_le htw
              refine runs_cond_le (v := 0) ?_ (fun h => False.elim (by omega)) ?_
              · simp [Expr.eval, BinOp.eval, h0w, hr4, hr5, hdivB]
              intro _
              refine runs_seq_assign_le (v := B * q)
                (by simp [Expr.eval, BinOp.eval, hr4, hr1, hBq_ltw]) ?_
              by_cases hmod0 : t % (B * q) = 0
              · refine runs_cond_le (v := 1) ?_ ?_ (fun h => False.elim (by omega))
                · simp [Expr.eval, BinOp.eval, h0w, h1w, hr2, hmod0]
                intro _
                refine runs_seq_assign_le (v := B * q) (by simp [Expr.eval]) ?_
                refine runs_assign_le (v := j - 1) ?_ ?_ (by dsimp only [Expr.size]; omega)
                · simp [Expr.eval, BinOp.eval, h1w, hr3, show j - 1 < 2 ^ w by omega]
                · have hj1L : j - 1 ≤ L := by omega
                  have hB1 : B * q = q ^ (L - (j - 1)) := by
                    rw [hB, show L - (j - 1) = L - j + 1 by omega, pow_succ]
                  have hd1 : phasePeriod q L (j - 1) ∣ t := by
                    unfold phasePeriod; rw [← hB1]; exact Nat.dvd_of_mod_eq_zero hmod0
                  refine ⟨⟨j - 1, B * q, 1, hj1L, hB1, hd1, hBq_le, Or.inr rfl, (fun hc => by cases hc),
                    hm, hr0, hr1, hr2, by simp, by simp [Function.update_of_ne],
                    by simp [Function.update_of_ne, hr5],
                    by simp [Function.update_of_ne, hr6]⟩, by simp [hr3, hr6]; omega⟩
              · have hmod_lt : t % (B * q) < 2 ^ w :=
                  lt_of_le_of_lt (Nat.mod_le _ _) htw
                have hno_next := chooseLevel_loop_inv hq1 ht_pos hjL hB
                  (fun _ hd => hmod0 (Nat.mod_eq_zero_of_dvd hd))
                refine runs_cond_le (v := 0) ?_ (fun h => False.elim (by omega)) ?_
                · simp [Expr.eval, BinOp.eval, h0w, hr2, hmod_lt, hmod0]
                intro _
                refine runs_assign_le (v := 0) (by eval_expr) ?_
                  (by dsimp only [Expr.size]; omega)
                refine ⟨⟨j, B, 0, hjL, hB, hdvd, hBt, Or.inl rfl, fun _ => hno_next,
                  hm, hr0, hr1, hr2, hr3, hr4, hr5, by simp⟩, by simp [hr3, hr6]⟩
          · refine runs_cond_le (v := 0) ?_ (fun h => False.elim (by omega)) ?_
            · simp [Expr.eval, BinOp.eval, h0w, hr3, hj0]
            intro _
            refine runs_assign_le (v := 0) (by eval_expr) ?_ (by dsimp only [Expr.size]; omega)
            refine ⟨⟨j, B, 0, hjL, hB, hdvd, hBt, Or.inl rfl, fun _ k hk => by omega,
              hm, hr0, hr1, hr2, hr3, hr4, hr5, by simp⟩, by simp [hr3, hr6]⟩)
    refine runs_seq_triple_le hLoop
      ⟨L, 1, 1, le_rfl, by simp, by simp [phasePeriod], Nat.succ_le_of_lt ht_pos, Or.inr rfl,
        (fun hc => False.elim (by omega)), rfl, by simp [startState], by simp [startState], by simp [startState],
        by simp, by simp, by simp, by simp⟩ ?_
    intro stF ⟨j, hjL, hdvd, hno, hm, hr3⟩
    refine runs_ret_le (by eval_expr) ⟨rfl, hm, ?_⟩ ?_
    · rw [chooseLevel_eq_of_dvd_not_pred hq1 hjL hdvd hno]; rfl
    · dsimp only [chooseLevelContract, Expr.size]
      simp [startState]
      omega

end

end MinCostFlow.DynSpanner.Program

