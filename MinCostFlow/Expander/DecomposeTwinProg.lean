module

public import MinCostFlow.Expander.DecomposeLevelBase
import all MinCostFlow.Expander.BfsCompProg

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Twin-Graph Construction & Decomposition Subroutines for `levelProc`

1. `buildTwin_triple`: builds `(twinGraph D curG).encode ++ [1, 200, rOf m_twin]` at `twAddr`;
2. `twinDecompStmt` & `twinDecomp_triple`: runs `runner (stripRandProg P_cited)` when
   `thr ≤ m_twin`, or `buildCsr` + `bfsLabels` when `m_twin < thr`, writing labels to `lblAddr`
   and preserving `ZeroFrom` at the updated cursor `mem[statePtr + 1]`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. `buildTwin_triple` -/

private lemma flatMap_pair_length (es : List (ℕ × ℕ)) :
    (es.flatMap fun (e : ℕ × ℕ) => [e.1, e.2]).length = 2 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

private lemma runs_seqStmts_append_list {w : ℕ} {p : Program} {ω : ℕ → Bool} :
    ∀ {s : Stmt} {ss ts : List Stmt} {st₀ st₁ st₂ : State} {c₁ c₂ : ℕ},
      ts ≠ [] →
      Runs w p ω (seqStmts (s :: ss)) st₀ .normal st₁ c₁ →
      Runs w p ω (seqStmts ts) st₁ .normal st₂ c₂ →
      Runs w p ω (seqStmts ((s :: ss) ++ ts)) st₀ .normal st₂ (c₁ + c₂ + 1)
  | s, [], ts, st₀, st₁, st₂, c₁, c₂, hne, h1, h2 => by
    cases ts with
    | nil => exact absurd rfl hne
    | cons t ts' => exact runs_seq h1 h2
  | s, s' :: ss, ts, st₀, st₁, st₂, c₁, c₂, hne, h1, h2 => by
    rcases runs_seq_iff.mp h1 with ⟨_, _, _, hret, _⟩ | ⟨st_m, c_s, c_r, hs, hr, rfl⟩
    · exact absurd hret (by simp)
    · have ih := runs_seqStmts_append_list (ss := ss) hne hr h2
      simpa only [List.cons_append, seqStmts, Nat.add_assoc] using
        runs_seq_iff.mpr (Or.inr ⟨st_m, c_s, c_r + c₂ + 1, hs, ih, by omega⟩)

private lemma triple_seqStmts_append {w : ℕ} {p : Program} {P Q R : State → Prop}
    {T₁ T₂ T : State → ℕ} {s : Stmt} {ss ts : List Stmt} (hne : ts ≠ [])
    (ht₁ : Triple w p P (seqStmts (s :: ss)) (normalPost Q) T₁)
    (ht₂ : Triple w p Q (seqStmts ts) (normalPost R) T₂)
    (hcost : ∀ st st', P st → Q st' → T₁ st + T₂ st' + 1 ≤ T st) :
    Triple w p P (seqStmts ((s :: ss) ++ ts)) (normalPost R) T := by
  intro st ω hP
  obtain ⟨o₁, st₁, c₁, hr₁, hQ, hc₁⟩ := ht₁ st ω hP
  cases o₁ with
  | returned _ => exact False.elim hQ
  | normal =>
    obtain ⟨o₂, st₂, c₂, hr₂, hR, hc₂⟩ := ht₂ st₁ ω hQ
    cases o₂ with
    | returned _ => exact False.elim hR
    | normal =>
      refine ⟨.normal, st₂, c₁ + c₂ + 1, runs_seqStmts_append_list hne hr₁ hr₂, hR, ?_⟩
      exact le_trans (by omega) (hcost st st₁ hP hQ)

lemma buildTwin_triple {w : ℕ} (p : Program) (mem : ℕ → ℕ) (curG : Cited.Graph)
    (curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr keptVertAddr
      statePtr lvl D D_phi mCap csrAddr qAddr lblAddr : ℕ)
    (hV : curG.IsValid) (hD : 1 ≤ D) (hga : GraphAt mem curGAddr curG)
    (hcur_tw : curGAddr + 2 + 2 * curG.m ≤ twAddr)
    (hm_twin_w : curG.m + D * curG.n < 2 ^ w)
    (hlog_w : Nat.log 2 (curG.m + D * curG.n) + 1 < 2 ^ w)
    (hcb_w : (rOf (curG.m + D * curG.n) + 1) ^ 3 < 2 ^ w)
    (h2n_w : 2 * curG.n < 2 ^ w)
    (htw_w : twAddr + 5 + 2 * (curG.m + D * curG.n) < 2 ^ w)
    (h200_w : 201 ≤ 2 ^ w) (_hw16 : 16 ≤ 2 ^ w) :
    Triple w p
      (fun st =>
        LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
        st.mem = mem)
      buildTwinStmt
      (normalPost fun st =>
        LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
        st.regs 19 = (twinGraph D curG).m ∧
        st.regs 20 = 5 + 2 * (twinGraph D curG).m ∧
        st.regs 21 = rOf (twinGraph D curG).m ∧
        ListAt st.mem twAddr ((twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m]) ∧
        GraphAt st.mem twAddr (twinGraph D curG) ∧
        MemFrame mem st.mem twAddr (twAddr + 5 + 2 * (twinGraph D curG).m))
      (fun _ => 120 * (curG.m + D * curG.n + 1) + 45 * (Nat.log 2 (curG.m + D * curG.n + 1) + 2)) := by
  have hw2 : 1 < 2 ^ w := by omega
  have hw4 : 4 ≤ 2 ^ w := by omega
  let m_twin := curG.m + D * curG.n
  have hm_twin_eq : (twinGraph D curG).m = m_twin := twinGraph_m D curG
  -- Stage 1: header
  let S1 : State → Prop := fun st =>
    LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
    st.regs 19 = m_twin ∧ st.regs 20 = 2 * curG.n ∧
    st.mem twAddr = 2 * curG.n ∧ st.mem (twAddr + 1) = m_twin ∧
    MemFrame mem st.mem twAddr (twAddr + 2)
  have h1 : Triple w p
      (fun st =>
        LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
        st.mem = mem)
      (seqStmts
        [ .assign 19 (.bin .add (.reg 15) (.bin .mul (.reg 11) (.reg 14)))
        , .assign 20 (.bin .mul (.const 2) (.reg 14))
        , .store (.reg 5) (.reg 20)
        , .store (.bin .add (.reg 5) (.const 1)) (.reg 19) ])
      (normalPost S1) (fun _ => 30) := by
    intro st ω ⟨hlvl, hm⟩
    rcases hlvl with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
    refine runs_start_le ?_
    wram_run
    · refine ⟨lvlRegs_of_eq (fun r hr => by
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
          ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩,
        by simp [r14, m_twin], by simp [r14],
        by simp [r5, r14],
        by simp [r5, r14, m_twin], fun a ha => ?_⟩
      rcases ha with ha | ha <;> simp [r5, Function.update_of_ne (by omega : a ≠ twAddr + 1),
        Function.update_of_ne (by omega : a ≠ twAddr), hm]
    · wram_cost
  -- Stage 2: copy scaled edges
  let CopyInv : ℕ → State → Prop := fun j st =>
    LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
    st.regs 19 = m_twin ∧ st.regs 22 = j ∧
    st.mem twAddr = 2 * curG.n ∧ st.mem (twAddr + 1) = m_twin ∧
    (∀ t, t < j → ∀ ht : t < curG.edges.length,
      st.mem (twAddr + 2 + 2 * t) = 2 * curG.edges[t].1 ∧
      st.mem (twAddr + 3 + 2 * t) = 2 * curG.edges[t].2) ∧
    MemFrame mem st.mem twAddr (twAddr + 2 + 2 * curG.m)
  let S2 : State → Prop := fun st =>
    LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
    st.regs 19 = m_twin ∧ st.regs 25 = twAddr + 2 + 2 * curG.m ∧
    st.mem twAddr = 2 * curG.n ∧ st.mem (twAddr + 1) = m_twin ∧
    (∀ t, ∀ ht : t < curG.edges.length,
      st.mem (twAddr + 2 + 2 * t) = 2 * curG.edges[t].1 ∧
      st.mem (twAddr + 3 + 2 * t) = 2 * curG.edges[t].2) ∧
    MemFrame mem st.mem twAddr (twAddr + 2 + 2 * curG.m)
  have h2 : Triple w p S1
      (seqStmts
        [ forRange 22 (.const 0) (.reg 15)
            (seqStmts
              [ .assign 23 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 22)))))
              , .assign 24 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 22)))))
              , .store (.bin .add (.reg 5) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 22))))
                  (.bin .mul (.const 2) (.reg 23))
              , .store (.bin .add (.reg 5) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 22))))
                  (.bin .mul (.const 2) (.reg 24)) ])
        , .assign 25 (.bin .add (.reg 5) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 15)))) ])
      (normalPost S2) (fun _ => 55 * curG.m + 25) := by
    have hloop := Triple.forRange_const (p := p) (r := 22) (lo := .const 0) (hi := .reg 15)
      (body := seqStmts
        [ .assign 23 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 22)))))
        , .assign 24 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 22)))))
        , .store (.bin .add (.reg 5) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 22))))
            (.bin .mul (.const 2) (.reg 23))
        , .store (.bin .add (.reg 5) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 22))))
            (.bin .mul (.const 2) (.reg 24)) ])
      (P := S1) (Inv := CopyInv) 43 0 curG.m (Nat.zero_le _) hw2 (fun _ => by omega)
      (fun st ⟨hlvl, r19, _, htw0, htw1, hfr⟩ =>
        ⟨by eval_expr,
          lvlRegs_of_eq (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]) hlvl,
          r19, by simp, htw0, htw1, fun _ h => by omega,
          fun a ha => hfr a (by rcases ha with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])⟩)
      (fun _ st _ _ hI => hI.2.2.1)
      (fun _ st _ _ hI => by have := hI.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
      (fun j _ hjlt st ω hI => by
        rcases hI with ⟨hlvl, r19, r22, htw0, htw1, he_prev, hfr⟩
        rcases hV _ (List.getElem_mem hjlt) with ⟨hu_n, hv_n⟩
        have hu_mem : st.mem (curGAddr + 2 + 2 * j) = curG.edges[j].1 := by
          rw [hfr _ (Or.inl (by omega))]; exact graphAt_edge_fst hga hjlt
        have hv_mem : st.mem (curGAddr + 3 + 2 * j) = curG.edges[j].2 := by
          rw [hfr _ (Or.inl (by omega))]; exact graphAt_edge_snd hga hjlt
        rcases hlvl with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
        let st_a : State := { st with regs := Function.update st.regs 23 curG.edges[j].1 }
        let st_b : State := { st_a with regs := Function.update st_a.regs 24 curG.edges[j].2 }
        let st_c : State := { st_b with mem := Function.update st_b.mem (twAddr + 2 + 2 * j) (2 * curG.edges[j].1) }
        let st_d : State := { st_c with mem := Function.update st_c.mem (twAddr + 3 + 2 * j) (2 * curG.edges[j].2) }
        have ha23 : Runs w p ω (.assign 23 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 22))))))
            st .normal st_a 9 :=
          runs_assign_iff.mpr ⟨curG.edges[j].1, by
            simp [Expr.eval, BinOp.eval, show (2 : ℕ) < 2 ^ w by omega, r0, r22,
              show 2 * j < 2 ^ w by omega, show 2 + 2 * j < 2 ^ w by omega,
              show curGAddr + (2 + 2 * j) = curGAddr + 2 + 2 * j by omega, hu_mem,
              show curGAddr + 2 + 2 * j < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have ha24 : Runs w p ω (.assign 24 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 22))))))
            st_a .normal st_b 9 :=
          runs_assign_iff.mpr ⟨curG.edges[j].2, by
            simp [st_a, Expr.eval, BinOp.eval, show (2 : ℕ) < 2 ^ w by omega, show (3 : ℕ) < 2 ^ w by omega,
              r0, r22, show 2 * j < 2 ^ w by omega, show 3 + 2 * j < 2 ^ w by omega,
              show curGAddr + (3 + 2 * j) = curGAddr + 3 + 2 * j by omega, hv_mem,
              show curGAddr + 3 + 2 * j < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have hs1 : Runs w p ω (.store (.bin .add (.reg 5) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 22))))
            (.bin .mul (.const 2) (.reg 23))) st_b .normal st_c 11 :=
          runs_store_iff.mpr ⟨twAddr + 2 + 2 * j, 2 * curG.edges[j].1,
            by simp [st_b, st_a, Expr.eval, BinOp.eval, show (2 : ℕ) < 2 ^ w by omega, r5, r22,
              show 2 * j < 2 ^ w by omega, show 2 + 2 * j < 2 ^ w by omega,
              show twAddr + (2 + 2 * j) = twAddr + 2 + 2 * j by omega,
              show twAddr + 2 + 2 * j < 2 ^ w by omega],
            by simp [st_b, st_a, Expr.eval, BinOp.eval, show (2 : ℕ) < 2 ^ w by omega,
              show 2 * curG.edges[j].1 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have hs2 : Runs w p ω (.store (.bin .add (.reg 5) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 22))))
            (.bin .mul (.const 2) (.reg 24))) st_c .normal st_d 11 :=
          runs_store_iff.mpr ⟨twAddr + 3 + 2 * j, 2 * curG.edges[j].2,
            by simp [st_c, st_b, st_a, Expr.eval, BinOp.eval, show (2 : ℕ) < 2 ^ w by omega,
              show (3 : ℕ) < 2 ^ w by omega, r5, r22,
              show 2 * j < 2 ^ w by omega, show 3 + 2 * j < 2 ^ w by omega,
              show twAddr + (3 + 2 * j) = twAddr + 3 + 2 * j by omega,
              show twAddr + 3 + 2 * j < 2 ^ w by omega],
            by simp [st_c, st_b, Expr.eval, BinOp.eval, show (2 : ℕ) < 2 ^ w by omega,
              show 2 * curG.edges[j].2 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have hrun_j : Runs w p ω (seqStmts
            [ .assign 23 (.load (.bin .add (.reg 0) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 22)))))
            , .assign 24 (.load (.bin .add (.reg 0) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 22)))))
            , .store (.bin .add (.reg 5) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 22)))) (.bin .mul (.const 2) (.reg 23))
            , .store (.bin .add (.reg 5) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 22)))) (.bin .mul (.const 2) (.reg 24)) ])
            st .normal st_d 43 :=
          runs_seq_iff.mpr (Or.inr ⟨st_a, 9, _, ha23,
            runs_seq_iff.mpr (Or.inr ⟨st_b, 9, _, ha24,
              runs_seq_iff.mpr (Or.inr ⟨st_c, 11, 11, hs1, hs2, rfl⟩), rfl⟩), rfl⟩)
        refine ⟨.normal, st_d, 43, hrun_j, ⟨⟨lvlRegs_of_eq (fun r hr => by
            dsimp [st_d, st_c, st_b, st_a]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
            ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩,
          by simp [st_d, st_c, st_b, st_a, r19], by simp, ?_, ?_, fun t htj ht => ?_, fun a ha => ?_⟩,
          by simp [st_d, st_c, st_b, st_a, r22]⟩, by dsimp only; omega⟩
        · simp [st_d, st_c, st_b, st_a, Function.update_of_ne (by omega : twAddr ≠ twAddr + 3 + 2 * j),
            Function.update_of_ne (by omega : twAddr ≠ twAddr + 2 + 2 * j), htw0]
        · simp [st_d, st_c, st_b, st_a, Function.update_of_ne (by omega : twAddr + 1 ≠ twAddr + 3 + 2 * j),
            Function.update_of_ne (by omega : twAddr + 1 ≠ twAddr + 2 + 2 * j), htw1]
        · rcases Nat.lt_succ_iff_lt_or_eq.mp htj with hlt | rfl
          · simp only [st_d, st_c, st_b, st_a]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact he_prev t hlt ht
          · simp only [st_d, st_c, st_b, st_a]
            rw [Function.update_of_ne (by omega : twAddr + 2 + 2 * t ≠ twAddr + 3 + 2 * t),
              Function.update_self, Function.update_self]
            exact ⟨rfl, rfl⟩
        · simp only [st_d, st_c, st_b, st_a]
          rw [Function.update_of_ne (by rcases ha with h | h <;> omega),
            Function.update_of_ne (by rcases ha with h | h <;> omega)]
          exact hfr a (by rcases ha with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]))
    have ha25 : Triple w p
        (fun st => LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
          st.regs 19 = m_twin ∧ st.mem twAddr = 2 * curG.n ∧ st.mem (twAddr + 1) = m_twin ∧
          (∀ t, ∀ ht : t < curG.edges.length,
            st.mem (twAddr + 2 + 2 * t) = 2 * curG.edges[t].1 ∧
            st.mem (twAddr + 3 + 2 * t) = 2 * curG.edges[t].2) ∧
          MemFrame mem st.mem twAddr (twAddr + 2 + 2 * curG.m))
        (.assign 25 (.bin .add (.reg 5) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 15)))))
        (normalPost S2) (fun _ => 10) := by
      intro st ω ⟨hlvl, r19, htw0, htw1, he, hfr⟩
      rcases hlvl with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
      refine runs_start_le ?_
      wram_run
      · exact ⟨lvlRegs_of_eq (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)])
          ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩,
          by simp [r19], by simp; omega, htw0, htw1, he, hfr⟩
      · wram_cost
    exact (Triple.seq_normal (hloop.conseq (fun _ h => h) (fun o st h => by
        cases o with | returned _ => exact False.elim h | normal =>
          exact ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, fun t ht => h.2.2.2.2.2.1 t ht ht, h.2.2.2.2.2.2⟩)
        (fun _ _ => le_rfl)) ha25 (T := fun _ => 55 * curG.m + 25)
      (fun _ _ _ _ => by simp only [Expr.size, Nat.sub_zero]; omega))
  -- Stage 3: twin edges nested loop
  let TwinOuterInv : ℕ → State → Prop := fun u st =>
    LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
    st.regs 19 = m_twin ∧ st.regs 22 = u ∧
    st.regs 25 = twAddr + 2 + 2 * curG.m + 2 * (u * D) ∧
    st.mem twAddr = 2 * curG.n ∧ st.mem (twAddr + 1) = m_twin ∧
    (∀ t, ∀ ht : t < curG.edges.length,
      st.mem (twAddr + 2 + 2 * t) = 2 * curG.edges[t].1 ∧
      st.mem (twAddr + 3 + 2 * t) = 2 * curG.edges[t].2) ∧
    (∀ u' < u, ∀ d < D,
      st.mem (twAddr + 2 + 2 * curG.m + 2 * (u' * D + d)) = 2 * u' ∧
      st.mem (twAddr + 2 + 2 * curG.m + 2 * (u' * D + d) + 1) = 2 * u' + 1) ∧
    MemFrame mem st.mem twAddr (twAddr + 2 + 2 * m_twin)
  let S3 : State → Prop := fun st =>
    LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
      keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
    st.regs 19 = m_twin ∧ st.regs 25 = twAddr + 2 + 2 * m_twin ∧
    st.mem twAddr = 2 * curG.n ∧ st.mem (twAddr + 1) = m_twin ∧
    (∀ t, ∀ ht : t < curG.edges.length,
      st.mem (twAddr + 2 + 2 * t) = 2 * curG.edges[t].1 ∧
      st.mem (twAddr + 3 + 2 * t) = 2 * curG.edges[t].2) ∧
    (∀ u' < curG.n, ∀ d < D,
      st.mem (twAddr + 2 + 2 * curG.m + 2 * (u' * D + d)) = 2 * u' ∧
      st.mem (twAddr + 2 + 2 * curG.m + 2 * (u' * D + d) + 1) = 2 * u' + 1) ∧
    MemFrame mem st.mem twAddr (twAddr + 2 + 2 * m_twin)
  have h3 : Triple w p S2
      (forRange 22 (.const 0) (.reg 14)
        (seqStmts
          [ .assign 23 (.bin .mul (.const 2) (.reg 22))
          , .assign 24 (.bin .add (.reg 23) (.const 1))
          , forRange 26 (.const 0) (.reg 11)
              (seqStmts
                [ .store (.reg 25) (.reg 23)
                , .store (.bin .add (.reg 25) (.const 1)) (.reg 24)
                , .assign 25 (.bin .add (.reg 25) (.const 2)) ]) ]))
      (normalPost S3) (fun _ => 60 * m_twin + 30) := by
    have houter := Triple.forRange_const (p := p) (r := 22) (lo := .const 0) (hi := .reg 14)
      (body := seqStmts
        [ .assign 23 (.bin .mul (.const 2) (.reg 22))
        , .assign 24 (.bin .add (.reg 23) (.const 1))
        , forRange 26 (.const 0) (.reg 11)
            (seqStmts
              [ .store (.reg 25) (.reg 23)
              , .store (.bin .add (.reg 25) (.const 1)) (.reg 24)
              , .assign 25 (.bin .add (.reg 25) (.const 2)) ]) ])
      (P := S2) (Inv := TwinOuterInv) (25 * D + 20) 0 curG.n (Nat.zero_le _) hw2
      (fun _ => by have := curG.n; omega)
      (fun st ⟨hlvl, r19, r25, htw0, htw1, he, hfr⟩ =>
        ⟨by eval_expr, lvlRegs_of_eq (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]) hlvl, r19, by simp,
          by simpa using r25, htw0, htw1, he, fun _ h => by omega,
          fun a ha => hfr a (by rcases ha with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])⟩)
      (fun _ st _ _ hI => hI.2.2.1)
      (fun _ st _ _ hI => by have := hI.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
      (fun u _ hult st ω hI => by
        rcases hI with ⟨hlvl, r19, r22, r25, htw0, htw1, he, htw_prev, hfr⟩
        let st_a : State := { st with regs := Function.update st.regs 23 (2 * u) }
        let st_b : State := { st_a with regs := Function.update st_a.regs 24 (2 * u + 1) }
        have ha23 : Runs w p ω (.assign 23 (.bin .mul (.const 2) (.reg 22))) st .normal st_a 4 :=
          runs_assign_iff.mpr ⟨2 * u, by simp [Expr.eval, BinOp.eval, show (2 : ℕ) < 2 ^ w by omega, r22, show 2 * u < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        have ha24 : Runs w p ω (.assign 24 (.bin .add (.reg 23) (.const 1))) st_a .normal st_b 4 :=
          runs_assign_iff.mpr ⟨2 * u + 1, by
            simp [st_a, Expr.eval, BinOp.eval, hw2, show 2 * u + 1 < 2 ^ w by omega],
            rfl, rfl, rfl⟩
        let InnerInv : ℕ → State → Prop := fun d st_in =>
          LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
            keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st_in ∧
          st_in.regs 19 = m_twin ∧ st_in.regs 22 = u ∧ st_in.regs 23 = 2 * u ∧
          st_in.regs 24 = 2 * u + 1 ∧ st_in.regs 26 = d ∧
          st_in.regs 25 = twAddr + 2 + 2 * curG.m + 2 * (u * D + d) ∧
          st_in.mem twAddr = 2 * curG.n ∧ st_in.mem (twAddr + 1) = m_twin ∧
          (∀ t, ∀ ht : t < curG.edges.length,
            st_in.mem (twAddr + 2 + 2 * t) = 2 * curG.edges[t].1 ∧
            st_in.mem (twAddr + 3 + 2 * t) = 2 * curG.edges[t].2) ∧
          (∀ u' < u, ∀ d' < D,
            st_in.mem (twAddr + 2 + 2 * curG.m + 2 * (u' * D + d')) = 2 * u' ∧
            st_in.mem (twAddr + 2 + 2 * curG.m + 2 * (u' * D + d') + 1) = 2 * u' + 1) ∧
          (∀ d' < d,
            st_in.mem (twAddr + 2 + 2 * curG.m + 2 * (u * D + d')) = 2 * u ∧
            st_in.mem (twAddr + 2 + 2 * curG.m + 2 * (u * D + d') + 1) = 2 * u + 1) ∧
          MemFrame st.mem st_in.mem (twAddr + 2 + 2 * curG.m + 2 * (u * D))
            (twAddr + 2 + 2 * curG.m + 2 * ((u + 1) * D))
        have hD_lt : D < 2 ^ w := by
          have : D ≤ D * curG.n := Nat.le_mul_of_pos_right D (by omega)
          omega
        have hinner := Triple.forRange_const (p := p) (r := 26) (lo := .const 0) (hi := .reg 11)
          (body := seqStmts
            [ .store (.reg 25) (.reg 23)
            , .store (.bin .add (.reg 25) (.const 1)) (.reg 24)
            , .assign 25 (.bin .add (.reg 25) (.const 2)) ])
          (P := fun s => s = st_b) (Inv := InnerInv) 14 0 D (Nat.zero_le _) hw2 (fun _ => hD_lt)
          (fun s hs => by
            subst hs
            have hl_b : LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
                keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st_b :=
              lvlRegs_of_eq (fun r hr => by
                dsimp [st_b, st_a]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]) hlvl
            have r25b : st_b.regs 25 = twAddr + 2 + 2 * curG.m + 2 * (u * D + 0) := by
              simpa [st_b, st_a] using r25
            refine ⟨by eval_expr,
              lvlRegs_of_eq (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]) hl_b,
              by simp [st_b, st_a, r19], by simp [st_b, st_a, r22], by simp [st_b, st_a],
              by simp [st_b], by simp, by simp [r25b],
              htw0, htw1, he, htw_prev, fun _ h => by omega, memFrame_refl _ _ _⟩)
          (fun _ st_in _ _ hI => hI.2.2.2.2.2.1)
          (fun _ st_in _ _ hI => by have := hI.1.2.2.2.2.2.2.2.2.2.2.2.1; eval_expr)
          (fun d _ hdlt st_in ω' hI => by
            rcases hI with ⟨hl_in, i19, i22, i23, i24, i26, i25, itw0, itw1, ihe, itw_u, itw_d, ifr⟩
            have hbound_addr : twAddr + 2 + 2 * curG.m + 2 * (u * D + d) + 2 ≤
                twAddr + 2 + 2 * m_twin := by
              have h1 : u * D + d + 1 ≤ (u + 1) * D := by rw [Nat.succ_mul]; omega
              have h2 : (u + 1) * D ≤ curG.n * D := Nat.mul_le_mul_right D hult
              dsimp only [m_twin]; rw [Nat.mul_comm D curG.n]; omega
            rcases hl_in with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
            set base := twAddr + 2 + 2 * curG.m + 2 * (u * D + d)
            have hbase_le : base + 2 ≤ twAddr + 2 + 2 * m_twin := hbound_addr
            have hbase_eq : base = twAddr + 2 + 2 * curG.m + 2 * (u * D + d) := rfl
            have hbase2_w : twAddr + 2 + 2 * curG.m + 2 * (u * D + d) + 2 < 2 ^ w := by
              rw [← hbase_eq]
              exact lt_of_le_of_lt hbase_le (by have hm_tw : m_twin = curG.m + D * curG.n := rfl; omega)
            have hbase1_w : twAddr + 2 + 2 * curG.m + 2 * (u * D + d) + 1 < 2 ^ w := by omega
            let s1 : State := { st_in with mem := Function.update st_in.mem base (2 * u) }
            let s2 : State := { s1 with mem := Function.update s1.mem (base + 1) (2 * u + 1) }
            let s3 : State := { s2 with regs := Function.update s2.regs 25 (base + 2) }
            have hs1 : Runs w p ω' (.store (.reg 25) (.reg 23)) st_in .normal s1 3 :=
              runs_store_iff.mpr ⟨base, 2 * u,
                by simp [Expr.eval, i25, hbase_eq],
                by simp [Expr.eval, i23], rfl, rfl, rfl⟩
            have hs2 : Runs w p ω' (.store (.bin .add (.reg 25) (.const 1)) (.reg 24)) s1 .normal s2 5 :=
              runs_store_iff.mpr ⟨base + 1, 2 * u + 1,
                by simp [s1, Expr.eval, BinOp.eval, i25, hw2, hbase_eq, hbase1_w],
                by simp [s1, Expr.eval, i24], rfl, rfl, rfl⟩
            have ha25' : Runs w p ω' (.assign 25 (.bin .add (.reg 25) (.const 2))) s2 .normal s3 4 :=
              runs_assign_iff.mpr ⟨base + 2,
                by simp [s2, s1, Expr.eval, BinOp.eval, i25, show (2 : ℕ) < 2 ^ w by omega, hbase_eq, hbase2_w],
                rfl, rfl, rfl⟩
            have hrun_d : Runs w p ω' (seqStmts
                [ .store (.reg 25) (.reg 23)
                , .store (.bin .add (.reg 25) (.const 1)) (.reg 24)
                , .assign 25 (.bin .add (.reg 25) (.const 2)) ]) st_in .normal s3 14 :=
              runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, hs1, runs_seq_iff.mpr (Or.inr ⟨s2, 5, 4, hs2, ha25', rfl⟩), rfl⟩)
            refine ⟨.normal, s3, 14, hrun_d, ⟨⟨lvlRegs_of_eq (fun r hr => by
                dsimp [s3, s2, s1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
                ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩,
              by simp [s3, s2, s1, i19], by simp [s3, s2, s1, i22], by simp [s3, s2, s1, i23],
              by simp [s3, s2, s1, i24], by simp [s3, s2, s1],
              by dsimp only [s3, base]; rw [Function.update_of_ne (by decide), Function.update_self]; ring,
              ?_, ?_, fun t ht => ?_, fun u' hu' d' hd' => ?_,
              fun d' hd' => ?_, fun a ha => ?_⟩, by simp [s3, s2, s1, i26]⟩, by dsimp only; omega⟩
            · simp only [s3, s2, s1, hbase_eq]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), itw0]
            · simp only [s3, s2, s1, hbase_eq]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), itw1]
            · have htm : t < curG.m := ht
              simp only [s3, s2, s1, hbase_eq]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact ihe t ht
            · have hu'd : u' * D + d' + 1 ≤ u * D :=
                le_trans (by rw [Nat.succ_mul]; omega) (Nat.mul_le_mul_right D hu')
              simp only [s3, s2, s1, hbase_eq]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact itw_u u' hu' d' hd'
            · rcases Nat.lt_succ_iff_lt_or_eq.mp hd' with hlt | rfl
              · simp only [s3, s2, s1, hbase_eq]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact itw_d d' hlt
              · simp only [s3, s2, s1, hbase_eq]
                rw [Function.update_of_ne (by omega : twAddr + 2 + 2 * curG.m + 2 * (u * D + d') ≠
                    twAddr + 2 + 2 * curG.m + 2 * (u * D + d') + 1),
                  Function.update_self, Function.update_self]
                exact ⟨rfl, rfl⟩
            · have h_succ : (u + 1) * D = u * D + D := Nat.succ_mul u D
              simp only [s3, s2, s1, hbase_eq] at ha ⊢
              rw [Function.update_of_ne (by rcases ha with h | h <;> omega),
                Function.update_of_ne (by rcases ha with h | h <;> omega)]
              exact ifr a (by rcases ha with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]))
        rcases hinner st_b ω rfl with ⟨o_in, st_in, c_in, hr_in, ho_in, hc_in⟩
        cases o_in with
        | returned _ => exact False.elim ho_in
        | normal =>
          rcases ho_in with ⟨hl_in, i19, i22, _, _, _, i25, itw0, itw1, ihe, itw_u, itw_d, ifr⟩
          have hseq_b : Runs w p ω (seqStmts
              [ .assign 23 (.bin .mul (.const 2) (.reg 22))
              , .assign 24 (.bin .add (.reg 23) (.const 1))
              , forRange 26 (.const 0) (.reg 11)
                  (seqStmts
                    [ .store (.reg 25) (.reg 23)
                    , .store (.bin .add (.reg 25) (.const 1)) (.reg 24)
                    , .assign 25 (.bin .add (.reg 25) (.const 2)) ]) ]) st .normal st_in
              (4 + (4 + c_in + 1) + 1) :=
            runs_seq_iff.mpr (Or.inr ⟨st_a, 4, _, ha23,
              runs_seq_iff.mpr (Or.inr ⟨st_b, 4, c_in, ha24, hr_in, rfl⟩), rfl⟩)
          refine ⟨.normal, st_in, _, hseq_b, ?_, by simp only [Expr.size] at hc_in ⊢; omega⟩
          refine ⟨⟨lvlRegs_of_eq (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]) hl_in,
              by simp [i19], by simp, by simp only; rw [Function.update_of_ne (by decide), i25]; ring,
              itw0, itw1, ihe, fun u' hu' d' hd' => ?_, fun a ha => ?_⟩, i22⟩
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hu' with hlt | rfl
            · exact itw_u u' hlt d' hd'
            · exact itw_d d' hd'
          · rw [ifr a (by
              have h1 : (u + 1) * D ≤ curG.n * D := Nat.mul_le_mul_right D hult
              have hm_tw : m_twin = curG.m + curG.n * D := congrArg (curG.m + ·) (Nat.mul_comm D curG.n)
              rcases ha with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
            exact hfr a ha)
    refine houter.conseq (fun _ h => h) (fun o st h => ?_) (fun _ _ => ?_)
    · cases o with
      | returned _ => exact False.elim h
      | normal =>
        rcases h with ⟨hl, r19, _, r25, htw0, htw1, he, htw, hfr⟩
        exact ⟨hl, r19, by rw [r25]; dsimp only [m_twin]; ring, htw0, htw1, he, htw, hfr⟩
    · have h2 : curG.n ≤ D * curG.n := Nat.le_mul_of_pos_left _ hD
      have hm_tw : m_twin = curG.m + D * curG.n := rfl
      have hcalc : curG.n * (25 * D + 20 + 1 + 8) + (1 + 1 + 5) ≤ 60 * m_twin + 30 := by
        calc curG.n * (25 * D + 20 + 1 + 8) + (1 + 1 + 5)
            = 25 * (curG.n * D) + 29 * curG.n + 7 := by ring
          _ ≤ 25 * (D * curG.n) + 29 * (D * curG.n) + 7 := by rw [Nat.mul_comm curG.n D]; omega
          _ ≤ 60 * (curG.m + D * curG.n) + 30 := by omega
      simp only [Expr.size]
      exact hcalc
  -- Stage 4: compute `rOf m_twin` + write `[1, 200, r_twin]` + `r20 := 5 + 2 * m_twin`
  have h4 : Triple w p S3
      (seqStmts
        [ rOfStmt 19 21 22 23
        , .store (.reg 25) (.const 1)
        , .store (.bin .add (.reg 25) (.const 1)) (.const 200)
        , .store (.bin .add (.reg 25) (.const 2)) (.reg 21)
        , .assign 20 (.bin .add (.bin .mul (.const 2) (.reg 19)) (.const 5)) ])
      (normalPost fun st =>
        LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
        st.regs 19 = (twinGraph D curG).m ∧
        st.regs 20 = 5 + 2 * (twinGraph D curG).m ∧
        st.regs 21 = rOf (twinGraph D curG).m ∧
        ListAt st.mem twAddr ((twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m]) ∧
        GraphAt st.mem twAddr (twinGraph D curG) ∧
        MemFrame mem st.mem twAddr (twAddr + 5 + 2 * (twinGraph D curG).m))
      (fun _ => 40 * (Nat.log 2 (m_twin + 1) + 2) + 25) := by
    intro st ω ⟨hlvl, r19, r25, htw0, htw1, he, htw, hfr⟩
    obtain ⟨st4, c4, hr4, hr4_out, hm4, hp4, hreg4, hc4⟩ :=
      rOfStmt_runs 19 21 22 23 (by decide) m_twin hm_twin_w hlog_w hcb_w hw4 st r19
    have h4_19 : st4.regs 19 = m_twin := by rw [hreg4 19 (by decide) (by decide) (by decide), r19]
    have h4_25 : st4.regs 25 = twAddr + 2 + 2 * m_twin := by rw [hreg4 25 (by decide) (by decide) (by decide), r25]
    have h4_lvl : LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
        keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st4 :=
      lvlRegs_of_eq (fun r hr => hreg4 r (by omega) (by omega) (by omega)) hlvl
    let m1 : ℕ → ℕ := Function.update st4.mem (twAddr + 2 + 2 * m_twin) 1
    let m2 : ℕ → ℕ := Function.update m1 (twAddr + 3 + 2 * m_twin) 200
    let st5 : State :=
      { mem := Function.update m2 (twAddr + 4 + 2 * m_twin) (rOf m_twin)
      , regs := Function.update st4.regs 20 (5 + 2 * m_twin)
      , pos := st4.pos }
    have htail : ∃ c5, Runs w p ω
        (seqStmts
          [ .store (.reg 25) (.const 1)
          , .store (.bin .add (.reg 25) (.const 1)) (.const 200)
          , .store (.bin .add (.reg 25) (.const 2)) (.reg 21)
          , .assign 20 (.bin .add (.bin .mul (.const 2) (.reg 19)) (.const 5)) ])
        st4 .normal st5 c5 ∧ c5 ≤ 22 := by
      refine ⟨22, ?_, by omega⟩
      dsimp only [seqStmts]
      have hs1 : Runs w p ω (.store (.reg 25) (.const 1)) st4 .normal { st4 with mem := m1 } 3 :=
        runs_store_iff.mpr ⟨_, 1, by simp [Expr.eval, h4_25], by simp [Expr.eval, hw2], rfl, rfl, rfl⟩
      have hs2 : Runs w p ω (.store (.bin .add (.reg 25) (.const 1)) (.const 200))
          { st4 with mem := m1 } .normal { st4 with mem := m2 } 5 :=
        runs_store_iff.mpr ⟨_, 200, by simp [Expr.eval, BinOp.eval, h4_25, hw2, show twAddr + 2 + 2 * m_twin + 1 = twAddr + 3 + 2 * m_twin by omega, show twAddr + 3 + 2 * m_twin < 2 ^ w by omega],
          by simp [Expr.eval, show (200 : ℕ) < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hs3 : Runs w p ω (.store (.bin .add (.reg 25) (.const 2)) (.reg 21))
          { st4 with mem := m2 } .normal { st4 with mem := st5.mem } 5 :=
        runs_store_iff.mpr ⟨_, rOf m_twin, by simp [Expr.eval, BinOp.eval, h4_25, show (2 : ℕ) < 2 ^ w by omega, show twAddr + 2 + 2 * m_twin + 2 = twAddr + 4 + 2 * m_twin by omega, show twAddr + 4 + 2 * m_twin < 2 ^ w by omega],
          by simp [Expr.eval, hr4_out], rfl, rfl, rfl⟩
      have ha20 : Runs w p ω (.assign 20 (.bin .add (.bin .mul (.const 2) (.reg 19)) (.const 5)))
          { st4 with mem := st5.mem } .normal st5 6 :=
        runs_assign_iff.mpr ⟨5 + 2 * m_twin, by
          simp [Expr.eval, BinOp.eval, h4_19, show (2 : ℕ) < 2 ^ w by omega, show (5 : ℕ) < 2 ^ w by omega,
            show 2 * m_twin < 2 ^ w by omega, show 2 * m_twin + 5 = 5 + 2 * m_twin by omega,
            show 5 + 2 * m_twin < 2 ^ w by omega],
          rfl, rfl, rfl⟩
      exact runs_seq_iff.mpr (Or.inr ⟨_, 3, _, hs1,
        runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hs2,
          runs_seq_iff.mpr (Or.inr ⟨_, 5, 6, hs3, ha20, rfl⟩), rfl⟩), rfl⟩)
    rcases htail with ⟨c5, hr5, hc5⟩
    have hrun := runs_seq_iff.mpr (Or.inr ⟨st4, c4, c5, hr4, hr5, rfl⟩)
    refine ⟨.normal, st5, c4 + c5 + 1, hrun, ?_, by dsimp only; omega⟩
    have hfr5 : MemFrame mem st5.mem twAddr (twAddr + 5 + 2 * m_twin) := fun a ha => by
      dsimp only [st5, m2, m1]
      rw [Function.update_of_ne (by rcases ha with h | h <;> omega),
        Function.update_of_ne (by rcases ha with h | h <;> omega),
        Function.update_of_ne (by rcases ha with h | h <;> omega), hm4]
      exact hfr a (by rcases ha with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
    have he5 : ∀ t (ht : t < curG.edges.length),
        st5.mem (twAddr + 2 + 2 * t) = 2 * curG.edges[t].1 ∧
        st5.mem (twAddr + 3 + 2 * t) = 2 * curG.edges[t].2 := fun t ht => by
      dsimp only [st5, m2, m1]
      have htm : t < curG.m := ht
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm4]
      exact he t ht
    have htw5 : ∀ u' < curG.n, ∀ d' < D,
        st5.mem (twAddr + 2 + 2 * curG.m + 2 * (u' * D + d')) = 2 * u' ∧
        st5.mem (twAddr + 2 + 2 * curG.m + 2 * (u' * D + d') + 1) = 2 * u' + 1 := fun u' hu' d' hd' => by
      have hud : u' * D + d' < D * curG.n := by
        have h1 : u' * D + d' + 1 ≤ (u' + 1) * D := by rw [Nat.succ_mul]; omega
        have h2 : (u' + 1) * D ≤ curG.n * D := Nat.mul_le_mul_right D hu'
        rw [Nat.mul_comm D curG.n]; omega
      have hcomm_u : D * u' = u' * D := Nat.mul_comm D u'
      have hcomm_n : curG.n * D = D * curG.n := Nat.mul_comm curG.n D
      have hm_tw : m_twin = curG.m + D * curG.n := rfl
      dsimp only [st5, m2, m1]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega), hm4]
      exact htw u' hu' d' hd'
    have htw_h0 : st5.mem twAddr = 2 * curG.n := by
      dsimp only [st5, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hm4, htw0]
    have htw_h1 : st5.mem (twAddr + 1) = m_twin := by
      dsimp only [st5, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), hm4, htw1]
    have hlist_tw : ListAt st5.mem twAddr ((twinGraph D curG).encode ++ [1, 200, rOf m_twin]) := by
      rw [Cited.Graph.encode, hm_twin_eq]
      dsimp only [twinGraph]
      simp only [List.cons_append]
      rw [List.flatMap_append, List.append_assoc]
      refine listAt_cons.mpr ⟨htw_h0, listAt_cons.mpr ⟨htw_h1, ?_⟩⟩
      refine listAt_append.mpr ⟨?_, listAt_append.mpr ⟨?_, ?_⟩⟩
      · exact listAt_scaledEdges st5.mem (twAddr + 2) curG.edges fun j hj =>
          ⟨(he5 j hj).1, by rw [show twAddr + 2 + 2 * j + 1 = twAddr + 3 + 2 * j by omega]; exact (he5 j hj).2⟩
      · rw [flatMap_pair_length,
          show twAddr + 1 + 1 + 2 * (curG.edges.map fun (e : ℕ × ℕ) => (2 * e.1, 2 * e.2)).length =
              twAddr + 2 + 2 * curG.m by simp [Cited.Graph.m]]
        exact listAt_twinEdges_block st5.mem (twAddr + 2 + 2 * curG.m) curG.n D htw5
      · have hlen_tw : ((twinGraph D curG).edges.flatMap fun (e : ℕ × ℕ) => [e.1, e.2]).length = 2 * m_twin := by
          rw [flatMap_pair_length]; exact congrArg (2 * ·) hm_twin_eq
        have hl1 : (((curG.edges.map fun (e : ℕ × ℕ) => (2 * e.1, 2 * e.2)).flatMap fun (e : ℕ × ℕ) => [e.1, e.2]).length +
            (((List.range curG.n).flatMap fun u => List.replicate D (2 * u, 2 * u + 1)).flatMap fun (e : ℕ × ℕ) => [e.1, e.2]).length) =
            2 * m_twin := by
          rw [← List.length_append, ← List.flatMap_append]; exact hlen_tw
        have heq_base : twAddr + 2 +
            ((curG.edges.map fun (e : ℕ × ℕ) => (2 * e.1, 2 * e.2)).flatMap fun (e : ℕ × ℕ) => [e.1, e.2]).length +
            (((List.range curG.n).flatMap fun u => List.replicate D (2 * u, 2 * u + 1)).flatMap fun (e : ℕ × ℕ) => [e.1, e.2]).length =
            twAddr + 2 + 2 * m_twin := by omega
        rw [heq_base]
        refine listAt_cons.mpr ⟨by dsimp [st5, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self],
          listAt_cons.mpr ⟨by
              dsimp [st5, m2, m1]
              rw [show twAddr + 2 + 2 * m_twin + 1 = twAddr + 3 + 2 * m_twin by omega,
                Function.update_of_ne (by omega), Function.update_self],
            listAt_cons.mpr ⟨by
                dsimp [st5, m2, m1]
                rw [show twAddr + 2 + 2 * m_twin + 1 + 1 = twAddr + 4 + 2 * m_twin by omega,
                  Function.update_self],
              fun _ h => by simp at h⟩⟩⟩
    have hga_tw : GraphAt st5.mem twAddr (twinGraph D curG) := fun i hi => by
      have hlt : i < ((twinGraph D curG).encode ++ [1, 200, rOf m_twin]).length := by simp at hi ⊢; omega
      simpa [List.getElem_append_left hi] using hlist_tw i hlt
    refine ⟨lvlRegs_of_eq (fun r hr => by
        dsimp only [st5]; rw [Function.update_of_ne (by omega)]) h4_lvl,
      by dsimp [st5]; rw [Function.update_of_ne (by decide), h4_19, hm_twin_eq],
      by dsimp [st5]; rw [Function.update_self, hm_twin_eq, Nat.add_comm 5 _],
      by dsimp [st5]; rw [Function.update_of_ne (by decide), hr4_out, hm_twin_eq],
      by simpa [hm_twin_eq] using hlist_tw, hga_tw, by simpa [hm_twin_eq] using hfr5⟩
  have h3' : Triple w p S2 (seqStmts [forRange 22 (.const 0) (.reg 14) (seqStmts
        [ .assign 23 (.bin .mul (.const 2) (.reg 22))
        , .assign 24 (.bin .add (.reg 23) (.const 1))
        , forRange 26 (.const 0) (.reg 11) (seqStmts
            [ .store (.reg 25) (.reg 23)
            , .store (.bin .add (.reg 25) (.const 1)) (.reg 24)
            , .assign 25 (.bin .add (.reg 25) (.const 2)) ]) ])])
      (normalPost S3) (fun _ => 60 * m_twin + 30) := h3
  have h34 := triple_seqStmts_append (by simp) h3' h4
    (T := fun _ => 60 * m_twin + 30 + (40 * (Nat.log 2 (m_twin + 1) + 2) + 25) + 1)
    (fun _ _ _ _ => le_rfl)
  have h234 := triple_seqStmts_append (by simp) h2 h34
    (T := fun _ => (55 * curG.m + 25) + (60 * m_twin + 30 + (40 * (Nat.log 2 (m_twin + 1) + 2) + 25) + 1) + 1)
    (fun _ _ _ _ => le_rfl)
  exact triple_seqStmts_append (by simp) h1 h234
    (T := fun _ => 120 * (curG.m + D * curG.n + 1) + 45 * (Nat.log 2 (curG.m + D * curG.n + 1) + 2))
    (fun _ _ _ _ => by
      have hm_tw : m_twin = curG.m + D * curG.n := rfl
      have hlog_eq : Nat.log 2 (m_twin + 1) = Nat.log 2 (curG.m + D * curG.n + 1) := rfl
      omega)

/-! ## 2. `twinDecompStmt` (`runner` vs CSR + BFS Fallback) -/

/-- Decomposes `G_twin` stored at `twAddr` (`reg 5`) and writes its `2 * curN` labels to `lblAddr`
(`reg 18`), calling `b_csr` + `b_bfs` if `m_twin < thr` and `b_run` otherwise. -/
def twinDecompStmt (b_run b_csr b_bfs thr : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 19) (.const thr))
    (seqStmts
      [ .assign 21 (.bin .mul (.const 2) (.reg 14))
      , .call 22 b_csr [.reg 5, .reg 16]
      , .call 22 b_bfs [.reg 21, .reg 19, .reg 16, .reg 17, .reg 18] ])
    (seqStmts
      [ .assign 21 (.load (.bin .add (.reg 9) (.const 1)))
      , .call 22 b_run [.reg 5, .reg 20, .reg 21]
      , .store (.bin .add (.reg 9) (.const 1)) (.reg 22)
      , .assign 23 (.bin .add (.reg 21) (.const 1))
      , .assign 24 (.bin .mul (.const 2) (.reg 14))
      , forRange 25 (.const 0) (.reg 24)
          (.store (.bin .add (.reg 18) (.reg 25))
            (.load (.bin .add (.reg 23) (.reg 25)))) ])

lemma twinDecompStmt_noRand (b_run b_csr b_bfs thr : ℕ) :
    (twinDecompStmt b_run b_csr b_bfs thr).NoRand := by
  simp [twinDecompStmt, forRange, WordRAM.forUp, seqStmts, Stmt.NoRand]

lemma twinDecomp_triple {w : ℕ} {p : Program} {b_run b_csr b_bfs thr : ℕ}
    {P_cited : Program} {c_cited : ℕ} {φ_cited : ℝ}
    (mem : ℕ → ℕ) (curG : Cited.Graph)
    (curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr keptVertAddr
      statePtr lvl D D_phi mCap csrAddr qAddr lblAddr zeroCursor c_cited_ub : ℕ)
    (hV : curG.IsValid) (hga_tw : GraphAt mem twAddr (twinGraph D curG))
    (hlist_tw : ListAt mem twAddr ((twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m]))
    (hz_eq : mem (statePtr + 1) = zeroCursor) (hzero : ZeroFrom mem zeroCursor)
    (hp_csr : MeetsContract w p b_csr (buildCsrContract w))
    (hp_bfs : MeetsContract w p b_bfs (bfsLabelsContract w))
    (hp_run : p.HasAt b_run (runner (stripRandProg P_cited) c_cited b_run))
    (hcited_run : thr ≤ (twinGraph D curG).m → ∃ out cost_c,
      RunsTo (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m]))
        P_cited ((twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m]) (fun _ => false) out cost_c ∧
      IsExpanderDecomposition (twinGraph D curG) (1 / 200) φ_cited out ∧
      (1 : ℝ) / (D_phi : ℝ) ≤ φ_cited ∧
      cost_c ≤ c_cited_ub)
    (hthr_phi : thr + 1 ≤ D_phi) (hthr_w : thr < 2 ^ w)
    (hstate_tw : statePtr + 3 ≤ twAddr)
    (htw_csr : twAddr + 5 + 2 * (twinGraph D curG).m ≤ csrAddr)
    (hcsr_q : csrAddr + 4 * curG.n + 1 + 4 * (twinGraph D curG).m ≤ qAddr)
    (hq_lbl : qAddr + 2 * curG.n ≤ lblAddr)
    (hlbl_z : lblAddr + 2 * curG.n ≤ zeroCursor)
    (hz_w : zeroCursor < 2 ^ w)
    (hrun_w : thr ≤ (twinGraph D curG).m →
      zeroCursor + 2 * curG.n + 2 ^ (wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m]) + 1) + 2 ≤ 2 ^ w)
    (hx_lt : ∀ v ∈ (twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m], v < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) :
    Triple w p
      (fun st =>
        LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st ∧
        st.regs 19 = (twinGraph D curG).m ∧
        st.regs 20 = 5 + 2 * (twinGraph D curG).m ∧
        st.mem = mem)
      (twinDecompStmt b_run b_csr b_bfs thr)
      (fun o st' => o = .normal ∧
        LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
          keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st' ∧
        ∃ (label : List ℕ) (φ_B1 : ℝ),
          label.length = 2 * curG.n ∧
          ListAt st'.mem lblAddr label ∧
          (∀ i < 2 * curG.n, st'.mem (lblAddr + i) < 2 ^ w) ∧
          (1 : ℝ) / (D_phi : ℝ) ≤ φ_B1 ∧
          IsExpanderDecomposition (twinGraph D curG) (1 / 200) φ_B1 label ∧
          ZeroFrom st'.mem (st'.mem (statePtr + 1)) ∧
          zeroCursor ≤ st'.mem (statePtr + 1) ∧
          (st'.mem (statePtr + 1) ≤ if thr ≤ (twinGraph D curG).m then
            zeroCursor + 1 + 2 ^ wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m])
          else zeroCursor) ∧
          (∀ a, a < zeroCursor → a ≠ statePtr + 1 → (a < csrAddr ∨ lblAddr + 2 * curG.n ≤ a) →
            st'.mem a = mem a))
      (fun _ =>
        400 * (2 * curG.n + (twinGraph D curG).m + 2) +
        runnerScale P_cited * (2 * c_cited_ub + (5 + 2 * (twinGraph D curG).m) +
          wordSize c_cited ((twinGraph D curG).encode ++ [1, 200, rOf (twinGraph D curG).m]) + 1) +
        30) := by
  intro st₀ ω ⟨hlvl, hr19, hr20, hmem0⟩
  subst hmem0
  set G_twin := twinGraph D curG
  set m_twin := G_twin.m
  set x := G_twin.encode ++ [1, 200, rOf m_twin]
  have hGtw_V : G_twin.IsValid := twinGraph_isValid hV
  have hGtw_n : G_twin.n = 2 * curG.n := rfl
  have hw2 : 1 < 2 ^ w := by omega
  have hw2_lt : 2 < 2 ^ w := by omega
  have hw4 : 4 ≤ 2 ^ w := by omega
  have hm_tw_len : G_twin.edges.length = m_twin := rfl
  have henc_len : G_twin.encode.length = 2 + 2 * m_twin := by
    simp [Cited.Graph.encode, hm_tw_len]; ring
  have hx_len : x.length = 5 + 2 * m_twin := by
    simp only [x, List.length_append, List.length_cons, List.length_nil]
    rw [henc_len]; omega
  by_cases hm_lt : m_twin < thr
  · have hcond : (Expr.bin .lt (.reg 19) (.const thr)).eval w st₀ = some 1 := by
      simp [Expr.eval, BinOp.eval, hr19, hthr_w, hm_lt, hw2]
    rcases hlvl with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
    let st1a : State := { st₀ with regs := Function.update st₀.regs 21 (2 * curG.n) }
    have ha21 : Runs w p ω (.assign 21 (.bin .mul (.const 2) (.reg 14))) st₀ .normal st1a 4 :=
      runs_assign_iff.mpr ⟨2 * curG.n, by
        simp [Expr.eval, BinOp.eval, hw2_lt, r14, show 2 * curG.n < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    have hwords1 : ∀ v ∈ [twAddr, csrAddr], v < 2 ^ w := fun v hv => by
      simp at hv; rcases hv with rfl | rfl <;> omega
    have hpre1 : (buildCsrContract w).pre [twAddr, csrAddr] st1a.mem :=
      ⟨twAddr, csrAddr, G_twin, rfl, hga_tw, hGtw_V, by omega, by omega, hw4⟩
    rcases runs_call_of_meetsContract (r := 22) (args := [.reg 5, .reg 16]) (vs := [twAddr, csrAddr])
        hp_csr (by simp [st1a, evalArgs, Expr.eval, r5, r16]) hwords1 hpre1 ω with
      ⟨st1b, c1b, _, hr1b, hcpost1, _, h1b_oth, hc1b⟩
    simp only [buildCsrContract, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, show Cited.readGraph st1a.mem twAddr = G_twin from graphAt_iff_readGraph.mp hga_tw] at hcpost1 hc1b
    rcases hcpost1 with ⟨_, hcsr1, hfr1⟩
    have hwords2 : ∀ v ∈ [2 * curG.n, m_twin, csrAddr, qAddr, lblAddr], v < 2 ^ w := fun v hv => by
      simp at hv; rcases hv with rfl | rfl | rfl | rfl | rfl <;> omega
    have hpre2 : (bfsLabelsContract w).pre [2 * curG.n, m_twin, csrAddr, qAddr, lblAddr] st1b.mem := by
      dsimp only [bfsLabelsContract]
      refine ⟨2 * curG.n, m_twin, csrAddr, qAddr, lblAddr, G_twin, rfl, rfl, rfl, hGtw_V, hcsr1, ?_, ?_, ?_,
        by omega, by omega, by omega, hw4⟩
      · left; omega
      · left; omega
      · left; omega
    have hr1b_21 : st1b.regs 21 = 2 * curG.n := by rw [h1b_oth 21 (by decide)]; simp [st1a]
    have hr1b_19 : st1b.regs 19 = m_twin := by rw [h1b_oth 19 (by decide)]; simp [st1a, hr19]
    have hr1b_16 : st1b.regs 16 = csrAddr := by rw [h1b_oth 16 (by decide)]; simp [st1a, r16]
    have hr1b_17 : st1b.regs 17 = qAddr := by rw [h1b_oth 17 (by decide)]; simp [st1a, r17]
    have hr1b_18 : st1b.regs 18 = lblAddr := by rw [h1b_oth 18 (by decide)]; simp [st1a, r18]
    rcases runs_call_of_meetsContract (r := 22) (args := [.reg 21, .reg 19, .reg 16, .reg 17, .reg 18])
        (vs := [2 * curG.n, m_twin, csrAddr, qAddr, lblAddr]) hp_bfs
        (by simp [evalArgs, Expr.eval, hr1b_21, hr1b_19, hr1b_16, hr1b_17, hr1b_18]) hwords2 hpre2 ω with
      ⟨st2, c2, _, hr2, hcpost2, _, h2_oth, hc2⟩
    simp only [bfsLabelsContract, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some] at hcpost2 hc2
    rcases hcpost2 with ⟨hfr2, hbfs_post⟩
    rcases hbfs_post G_twin rfl rfl hGtw_V hcsr1 with ⟨hlen_lbl, hmem_lbl_lt, hparts_eq⟩
    set label := (List.range (2 * curG.n)).map fun i => st2.mem (lblAddr + i)
    have hlist_lbl : ListAt st2.mem lblAddr label := fun i hi => by
      simp [label] at hi ⊢
    have hdec_fb : IsExpanderDecomposition G_twin (1 / 200) (1 / (D_phi : ℝ)) label :=
      isExpanderDecomposition_of_partsEq hGtw_V hm_lt hthr_phi hlen_lbl hparts_eq
    have hfr_sub : ∀ a, a < zeroCursor → (a < csrAddr ∨ lblAddr + 2 * curG.n ≤ a) → st2.mem a = st₀.mem a := by
      intro a ha_z ha_out
      have h2 := hfr2 a (by rcases ha_out with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
        (by rcases ha_out with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
      have h1 := hfr1 a (by rcases ha_out with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
      exact h2.trans h1
    have hst2_z : st2.mem (statePtr + 1) = zeroCursor := by
      rw [hfr_sub (statePtr + 1) (by omega) (Or.inl (by omega)), hz_eq]
    have hzero2 : ZeroFrom st2.mem (st2.mem (statePtr + 1)) := by
      rw [hst2_z]
      intro a ha
      have h2 := hfr2 a (Or.inr (by omega)) (Or.inr (by omega))
      have h1 := hfr1 a (Or.inr (by omega))
      rw [h2, h1]; exact hzero a ha
    have hlvl2 : LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
        keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st2 := by
      refine lvlRegs_of_eq (fun r hr => ?_)
        ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
      rw [h2_oth r (by omega), h1b_oth r (by omega)]
      simp [st1a, Function.update_of_ne (by omega : r ≠ 21)]
    have hseq_t : Runs w p ω (seqStmts
        [ .assign 21 (.bin .mul (.const 2) (.reg 14))
        , .call 22 b_csr [.reg 5, .reg 16]
        , .call 22 b_bfs [.reg 21, .reg 19, .reg 16, .reg 17, .reg 18] ])
        st₀ .normal st2 (4 + (c1b + c2 + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨st1a, 4, _, ha21,
        runs_seq_iff.mpr (Or.inr ⟨st1b, c1b, c2, hr1b, hr2, rfl⟩), rfl⟩)
    have hrun : Runs w p ω (twinDecompStmt b_run b_csr b_bfs thr) st₀ .normal st2 _ :=
      runs_cond_iff.mpr ⟨1, _, hcond, by simpa using hseq_t, rfl⟩
    refine ⟨.normal, st2, _, hrun, ⟨rfl, hlvl2, label, 1 / (D_phi : ℝ), hlen_lbl, hlist_lbl,
      fun i hi => lt_of_lt_of_le (hmem_lbl_lt i hi) (by omega), le_rfl, hdec_fb, hzero2,
      by simp [hst2_z], by simp [hst2_z, Nat.not_le.mpr hm_lt],
      fun a ha _ ha2 => hfr_sub a ha ha2⟩, ?_⟩
    simp only [argsSize, Expr.size] at hc1b hc2 ⊢
    omega
  · have hge_thr : thr ≤ m_twin := Nat.le_of_not_lt hm_lt
    have hcond : (Expr.bin .lt (.reg 19) (.const thr)).eval w st₀ = some 0 := by
      simp [Expr.eval, BinOp.eval, hr19, hthr_w, hm_lt]
    rcases hlvl with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
    obtain ⟨out, cost_c, hrun_c, hdec_c, hφ_c, hcost_c⟩ := hcited_run hge_thr
    let st1a : State := { st₀ with regs := Function.update st₀.regs 21 zeroCursor }
    have ha21 : Runs w p ω (.assign 21 (.load (.bin .add (.reg 9) (.const 1)))) st₀ .normal st1a 5 :=
      runs_assign_iff.mpr ⟨zeroCursor, by
        simp [Expr.eval, BinOp.eval, hw2, r9, show statePtr + 1 < 2 ^ w by omega, hz_eq],
        rfl, rfl, rfl⟩
    have hrun_w' := hrun_w hge_thr
    have hw_sub : wordSize c_cited x < w := by
      have h1 : 2 ^ wordSize c_cited x < 2 ^ w := by
        have : 2 ^ wordSize c_cited x ≤ 2 ^ (wordSize c_cited x + 1) := by rw [pow_succ']; omega
        omega
      by_contra hle
      have : 2 ^ w ≤ 2 ^ wordSize c_cited x := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hle)
      omega
    have hout_lt := runsTo_mem_lt_of_input_lt hw_sub.le hx_lt hrun_c
    have hargs_r : evalArgs w st1a [.reg 5, .reg 20, .reg 21] = some [twAddr, 5 + 2 * m_twin, zeroCursor] := by
      simp [st1a, evalArgs, Expr.eval, r5, hr20]
    obtain ⟨st1b, c1b, hr1b, hregs1b, _, hout1b, hfr1b, hzero1b, hc1b⟩ :=
      runs_call_runner_stripRand (ω := ω) (r := 22) (b_run := b_run) (c := c_cited)
        hp_run hargs_r (by omega) hx_len.symm (by simpa [st1a] using hlist_tw)
        (by simpa [st1a] using hzero) (by omega) hrun_c
    let zeroCursor' := zeroCursor + 1 + 2 ^ wordSize c_cited x
    have hzc'_eq : zeroCursor' = zeroCursor + 1 + 2 ^ wordSize c_cited x := rfl
    have hzc'_ge : zeroCursor + 1 ≤ zeroCursor' := by
      have := Nat.one_le_two_pow (n := wordSize c_cited x); omega
    have hzc'_lt : zeroCursor' < 2 ^ w := by
      have := Nat.one_le_two_pow (n := wordSize c_cited x)
      have h2p : 2 ^ wordSize c_cited x ≤ 2 ^ (wordSize c_cited x + 1) := by rw [pow_succ']; omega
      omega
    have hr1b_22 : st1b.regs 22 = zeroCursor' := by rw [hregs1b]; simp [zeroCursor']
    have hr1b_21 : st1b.regs 21 = zeroCursor := by
      rw [hregs1b, Function.update_of_ne (by decide)]; simp [st1a]
    have hr1b_9 : st1b.regs 9 = statePtr := by
      rw [hregs1b, Function.update_of_ne (by decide)]; simp [st1a, r9]
    have hr1b_14 : st1b.regs 14 = curG.n := by
      rw [hregs1b, Function.update_of_ne (by decide)]; simp [st1a, r14]
    have hr1b_18 : st1b.regs 18 = lblAddr := by
      rw [hregs1b, Function.update_of_ne (by decide)]; simp [st1a, r18]
    let st1c : State := { st1b with mem := Function.update st1b.mem (statePtr + 1) zeroCursor' }
    have hs_zc : Runs w p ω (.store (.bin .add (.reg 9) (.const 1)) (.reg 22)) st1b .normal st1c 5 :=
      runs_store_iff.mpr ⟨statePtr + 1, zeroCursor',
        by simp [Expr.eval, BinOp.eval, hw2, hr1b_9, show statePtr + 1 < 2 ^ w by omega],
        by simp [Expr.eval, hr1b_22], rfl, rfl, rfl⟩
    let st1d : State := { st1c with regs := Function.update st1c.regs 23 (zeroCursor + 1) }
    let st1e : State := { st1d with regs := Function.update st1d.regs 24 (2 * curG.n) }
    have hzc1_lt : zeroCursor + 1 < 2 ^ w := by omega
    have ha23 : Runs w p ω (.assign 23 (.bin .add (.reg 21) (.const 1))) st1c .normal st1d 4 :=
      runs_assign_iff.mpr ⟨zeroCursor + 1,
        by simp [st1c, Expr.eval, BinOp.eval, hw2, hr1b_21, hzc1_lt],
        rfl, rfl, rfl⟩
    have ha24 : Runs w p ω (.assign 24 (.bin .mul (.const 2) (.reg 14))) st1d .normal st1e 4 :=
      runs_assign_iff.mpr ⟨2 * curG.n,
        by simp [st1d, st1c, Expr.eval, BinOp.eval, hw2_lt, hr1b_14, show 2 * curG.n < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    have hlvl1e : LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
        keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr st1e := by
      refine lvlRegs_of_eq (fun r hr => ?_)
        ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩
      dsimp [st1e, st1d, st1c]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hregs1b,
        Function.update_of_ne (by omega)]
      dsimp [st1a]
      rw [Function.update_of_ne (by omega)]
    have hout_len : out.length = 2 * curG.n := hdec_c.1
    let CopyLblInv : ℕ → State → Prop := fun t s =>
      LvlRegs curGAddr curIdxAddr nextGAddr nextIdxAddr lvlArrAddr twAddr bufAddr workAddr
        keptVertAddr statePtr lvl D D_phi mCap curG.n curG.m csrAddr qAddr lblAddr s ∧
      s.regs 23 = zeroCursor + 1 ∧ s.regs 24 = 2 * curG.n ∧ s.regs 25 = t ∧
      (∀ i < t, ∀ hi : i < out.length, s.mem (lblAddr + i) = out[i]) ∧
      MemFrame st1e.mem s.mem lblAddr (lblAddr + 2 * curG.n)
    have hcopy_lbl := Triple.forRange_const (p := p) (r := 25) (lo := .const 0) (hi := .reg 24)
      (body := .store (.bin .add (.reg 18) (.reg 25)) (.load (.bin .add (.reg 23) (.reg 25))))
      (P := fun s => s = st1e) (Inv := CopyLblInv) 16 0 (2 * curG.n) (Nat.zero_le _) hw2
      (fun _ => by omega)
      (fun s hs => by
        subst hs
        refine ⟨by eval_expr,
          lvlRegs_of_eq (fun r hr => by dsimp only; rw [Function.update_of_ne (by omega)]) hlvl1e,
          by simp [st1e, st1d], by simp [st1e], by simp, fun _ h => by omega, memFrame_refl _ _ _⟩)
      (fun _ s _ _ hI => hI.2.2.2.1)
      (fun _ s _ _ hI => by have := hI.2.2.1; eval_expr)
      (fun t _ htlt s ω' hI => by
        rcases hI with ⟨hl_s, r23s, r24s, r25s, hprev, hfr_s⟩
        have hto : t < out.length := hout_len ▸ htlt
        have hsrc : s.mem (zeroCursor + 1 + t) = out[t] := by
          rw [hfr_s _ (Or.inr (by omega))]
          dsimp [st1e, st1d, st1c]
          rw [Function.update_of_ne (by omega)]
          exact hout1b.getElem hto
        rcases hl_s with ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩
        let s1' : State := { s with mem := Function.update s.mem (lblAddr + t) out[t] }
        refine ⟨.normal, s1', _, runs_store_iff.mpr ⟨lblAddr + t, out[t],
            by simp [Expr.eval, BinOp.eval, s18, r25s, show lblAddr + t < 2 ^ w by omega],
            by simp [Expr.eval, BinOp.eval, r23s, r25s, show zeroCursor + 1 + t < 2 ^ w by omega, hsrc],
            rfl, rfl, rfl⟩,
          ⟨⟨lvlRegs_of_eq (fun r hr => by dsimp only [s1']; rw [Function.update_of_ne (by omega)])
            ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18⟩,
          by simp [s1', r23s], by simp [s1', r24s], by simp [s1'], fun i hit hi => ?_, fun a ha => ?_⟩,
          r25s⟩, by simp [Expr.size]⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hit with hlt | rfl
          · simp only [s1']; rw [Function.update_of_ne (by omega)]; exact hprev i hlt hi
          · simp only [s1']; rw [Function.update_self]
        · simp only [s1']; rw [Function.update_of_ne (by rcases ha with h | h <;> omega)]; exact hfr_s a ha)
    rcases hcopy_lbl st1e ω rfl with ⟨oc, st2, cc, hrc, hoc, hcc⟩
    cases oc with
    | returned _ => exact False.elim hoc
    | normal =>
      rcases hoc with ⟨hlvl2, _, _, _, hlbl2, hfr2⟩
      have hlist_lbl : ListAt st2.mem lblAddr out := fun i hi => by
        exact hlbl2 i (hout_len ▸ hi) hi
      have hmem_lbl_lt : ∀ i < 2 * curG.n, st2.mem (lblAddr + i) < 2 ^ w := fun i hi => by
        have hio : i < out.length := hout_len ▸ hi
        rw [hlist_lbl.getElem hio]
        exact hout_lt _ (List.getElem_mem hio)
      have hst2_z : st2.mem (statePtr + 1) = zeroCursor' := by
        rw [hfr2 _ (Or.inl (by omega))]
        simp [st1e, st1d, st1c]
      have hzero2 : ZeroFrom st2.mem (st2.mem (statePtr + 1)) := by
        rw [hst2_z]
        intro a ha
        rw [hfr2 a (Or.inr (by omega))]
        dsimp [st1e, st1d, st1c]
        rw [Function.update_of_ne (by omega)]
        exact hzero1b a ha
      have hfr_sub : ∀ a, a < zeroCursor → a ≠ statePtr + 1 → (a < csrAddr ∨ lblAddr + 2 * curG.n ≤ a) →
          st2.mem a = st₀.mem a := by
        intro a ha hne ha_out
        have h2 : st2.mem a = st1e.mem a :=
          hfr2 a (by rcases ha_out with h | h <;> [exact Or.inl (by omega); exact Or.inr h])
        rw [h2]
        dsimp [st1e, st1d, st1c]
        rw [Function.update_of_ne hne]
        exact hfr1b a ha
      have hseq_f : Runs w p ω (seqStmts
          [ .assign 21 (.load (.bin .add (.reg 9) (.const 1)))
          , .call 22 b_run [.reg 5, .reg 20, .reg 21]
          , .store (.bin .add (.reg 9) (.const 1)) (.reg 22)
          , .assign 23 (.bin .add (.reg 21) (.const 1))
          , .assign 24 (.bin .mul (.const 2) (.reg 14))
          , forRange 25 (.const 0) (.reg 24)
              (.store (.bin .add (.reg 18) (.reg 25))
                (.load (.bin .add (.reg 23) (.reg 25)))) ])
          st₀ .normal st2 (5 + (c1b + (5 + (4 + (4 + cc + 1) + 1) + 1) + 1) + 1) :=
        runs_seq_iff.mpr (Or.inr ⟨st1a, 5, _, ha21,
          runs_seq_iff.mpr (Or.inr ⟨st1b, c1b, _, hr1b,
            runs_seq_iff.mpr (Or.inr ⟨st1c, 5, _, hs_zc,
              runs_seq_iff.mpr (Or.inr ⟨st1d, 4, _, ha23,
                runs_seq_iff.mpr (Or.inr ⟨st1e, 4, cc, ha24, hrc, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      have hrun : Runs w p ω (twinDecompStmt b_run b_csr b_bfs thr) st₀ .normal st2 _ :=
        runs_cond_iff.mpr ⟨0, _, hcond, by simpa using hseq_f, rfl⟩
      have hrc_ub : runnerScale P_cited * (2 * cost_c + (5 + 2 * m_twin) + wordSize c_cited x + 1) ≤
          runnerScale P_cited * (2 * c_cited_ub + (5 + 2 * m_twin) + wordSize c_cited x + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      refine ⟨.normal, st2, _, hrun, ⟨rfl, hlvl2, out, φ_cited, hout_len, hlist_lbl, hmem_lbl_lt,
        hφ_c, hdec_c, hzero2, by rw [hst2_z]; omega,
        by simp [hst2_z, hge_thr, hzc'_eq], hfr_sub⟩, ?_⟩
      simp only [Expr.size] at hc1b hcc ⊢
      omega

end MinCostFlow.Expander
