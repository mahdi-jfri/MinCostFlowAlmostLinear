module

public import MinCostFlow.SparseCore.Program.LSFWindowCanon
public import WordRAM.Link
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Relocated Deterministic Guest Execution (`LSFWindowReloc`)

Proves:
* `runs_relocStmt_noRand`: deterministic specialization of `WordRAM.Link.runs_relocStmt` for any
  `Q.IsDeterministic` and `s.NoRand`, allowing an arbitrary value (in particular `0`) in register
  `Q.regBound + 1` so the host never needs to compute the noncomputable `2 ^ w'` at runtime.
* `canonicalLSF_relocated_run`: calling relocated `lemma55Module` at `guestBase` on
  `canonGuestMem` executes `chosenGuestRun hV` in `[guestBase, guestBase + 2 ^ w')`, producing
  `(LSFRep h).rep (r.hs j) (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k j) (r.x₀ j)`
  on shifted memory `fun a => st_H'.mem (guestBase + a)` for every `j < k` at cost at most
  `((lemma55Module Q_AN c_AN K_AN h).regBound + 6) * lemma55Cost ...`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM WordRAM.Link MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program
  MinCostFlow.DynSpanner.Program MinCostFlow.WideWord MinCostFlow.Num

/-! ## Deterministic relocation helpers (independent of register `R + 1`) -/

private lemma relocExpr_size_le_local (R : ℕ) : ∀ e : Expr, (relocExpr R e).size ≤ 3 * e.size
  | .const _ => by simp [relocExpr, Expr.size]
  | .reg _ => by simp [relocExpr, Expr.size]
  | .load a => by
    have ih := relocExpr_size_le_local R a
    simp only [relocExpr, Expr.size]; omega
  | .bin _ a b => by
    have iha := relocExpr_size_le_local R a
    have ihb := relocExpr_size_le_local R b
    simp only [relocExpr, Expr.size]; omega

private lemma argsSize_reloc_le_local (R : ℕ) :
    ∀ args : List Expr, argsSize (args.map (relocExpr R)) ≤ 3 * argsSize args
  | [] => by simp [argsSize]
  | e :: es => by
    have he := relocExpr_size_le_local R e
    have hes := argsSize_reloc_le_local R es
    simp only [List.map_cons, argsSize]; omega

private lemma argsSize_append_local :
    ∀ xs ys : List Expr, argsSize (xs ++ ys) = argsSize xs + argsSize ys
  | [], ys => by simp [argsSize]
  | x :: xs, ys => by simp [argsSize, argsSize_append_local xs ys, Nat.add_assoc]

private lemma argsSize_replicate_const_zero (n : ℕ) :
    argsSize (List.replicate n (.const 0)) = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]; omega

private lemma eval_relocExpr_local {w w' R h : ℕ} {e : Expr} {st_Q st_H : State} {v : ℕ}
    (hw_le : w' ≤ w) (hh : h + 1 + 2 ^ w' ≤ 2 ^ w)
    (he_rb : e.regBound ≤ R)
    (hregs : ∀ r < R, st_H.regs r = st_Q.regs r)
    (hbase : st_H.regs R = h + 1)
    (hq_regs : ∀ r, st_Q.regs r < 2 ^ w')
    (hq_mem : ∀ a, st_Q.mem a < 2 ^ w')
    (hmem : ∀ a < 2 ^ w', st_H.mem (h + 1 + a) = st_Q.mem a)
    (he : e.eval w' st_Q = some v) :
    (relocExpr R e).eval w st_H = some v ∧ v < 2 ^ w' := by
  have hpow_le : 2 ^ w' ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw_le
  induction e generalizing v with
  | const k =>
    simp only [Expr.eval, Option.ite_none_right_eq_some, Option.some.injEq] at he
    rcases he with ⟨hk, rfl⟩
    exact ⟨by simp [relocExpr, Expr.eval, lt_of_lt_of_le hk hpow_le], hk⟩
  | reg r =>
    simp only [Expr.eval, Option.some.injEq] at he
    subst he
    have hr : r < R := by simpa [Expr.regBound] using he_rb
    exact ⟨by simp [relocExpr, Expr.eval, hregs r hr], hq_regs r⟩
  | load a ih =>
    simp only [Expr.eval] at he
    cases ha : a.eval w' st_Q with
    | none => simp [ha] at he
    | some addr =>
      simp only [ha, Option.map_some, Option.some.injEq] at he
      subst he
      obtain ⟨ha_H, haddr_lt⟩ := ih (by simpa [Expr.regBound] using he_rb) ha
      have hsum_lt : h + 1 + addr < 2 ^ w := by omega
      refine ⟨?_, hq_mem addr⟩
      simp [relocExpr, Expr.eval, BinOp.eval, hbase, ha_H, hsum_lt, hmem addr haddr_lt]
  | bin op a b iha ihb =>
    simp only [Expr.eval] at he
    cases ha : a.eval w' st_Q with
    | none => simp [ha] at he
    | some va =>
      cases hb : b.eval w' st_Q with
      | none => simp [ha, hb] at he
      | some vb =>
        simp only [ha, hb] at he
        simp only [Expr.regBound, max_le_iff] at he_rb
        obtain ⟨ha_H, hva_lt⟩ := iha he_rb.1 ha
        obtain ⟨hb_H, hvb_lt⟩ := ihb he_rb.2 hb
        split_ifs at he with hlt
        injection he with hv; subst hv
        exact ⟨by simp [relocExpr, Expr.eval, ha_H, hb_H, lt_of_lt_of_le hlt hpow_le], hlt⟩

private lemma evalArgs_reloc_local {w w' R h : ℕ} {args : List Expr} {st_Q st_H : State}
    {vs : List ℕ}
    (hw_le : w' ≤ w) (hh : h + 1 + 2 ^ w' ≤ 2 ^ w)
    (hargs_rb : argsRegBound args ≤ R)
    (hregs : ∀ r < R, st_H.regs r = st_Q.regs r)
    (hbase : st_H.regs R = h + 1)
    (hq_regs : ∀ r, st_Q.regs r < 2 ^ w')
    (hq_mem : ∀ a, st_Q.mem a < 2 ^ w')
    (hmem : ∀ a < 2 ^ w', st_H.mem (h + 1 + a) = st_Q.mem a)
    (hargs : evalArgs w' st_Q args = some vs) :
    evalArgs w st_H (args.map (relocExpr R)) = some vs ∧
      vs.length = args.length ∧ ∀ v ∈ vs, v < 2 ^ w' := by
  induction args generalizing vs with
  | nil =>
    simp only [evalArgs, Option.some.injEq] at hargs
    subst hargs; simp
  | cons e es ih =>
    simp only [evalArgs] at hargs
    cases he : e.eval w' st_Q with
    | none => simp [he] at hargs
    | some v =>
      cases hes : evalArgs w' st_Q es with
      | none => simp [he, hes] at hargs
      | some vs' =>
        simp only [he, hes, Option.some.injEq] at hargs
        subst hargs
        simp only [argsRegBound, max_le_iff] at hargs_rb
        obtain ⟨he_H, hv_lt⟩ := eval_relocExpr_local hw_le hh hargs_rb.1 hregs hbase hq_regs hq_mem hmem he
        obtain ⟨hes_H, hlen, hvs'⟩ := ih hargs_rb.2 hes
        refine ⟨by simp [evalArgs, he_H, hes_H], by simp [hlen], fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hv_lt
        · exact hvs' x hx'

/-- Deterministic specialization of `WordRAM.Link.runs_relocStmt`: when `Q` is deterministic and
`s.NoRand`, register `Q.regBound + 1` is never read for `.rand` masking and may hold any value
`v_R1` (in particular `0`). -/
theorem runs_relocStmt_noRand {w w' h b v_R1 : ℕ} {Q p : Program} {ω_Q ω : ℕ → Bool}
    (hdet : Q.IsDeterministic)
    (hp : ∀ f body, Q.procs[f]? = some body →
      p.procs[b + 1 + f]? = some (relocStmt Q.regBound b body))
    (hw_le : w' ≤ w) (hh : h + 1 + 2 ^ w' ≤ 2 ^ w) :
    ∀ fuel s st_Q st_H o st_Q' c_Q,
      s.NoRand →
      s.regBound ≤ Q.regBound →
      st_H.regs Q.regBound = h + 1 →
      st_H.regs (Q.regBound + 1) = v_R1 →
      (∀ r < Q.regBound, st_H.regs r = st_Q.regs r) →
      (∀ r, st_Q.regs r < 2 ^ w') →
      (∀ a, st_Q.mem a < 2 ^ w') →
      (∀ a < 2 ^ w', st_H.mem (h + 1 + a) = st_Q.mem a) →
      exec w' Q ω_Q fuel s st_Q = some (o, st_Q', c_Q) →
      ∃ st_H' c_H,
        Runs w p ω (relocStmt Q.regBound b s) st_H o st_H' c_H ∧
        c_H ≤ (Q.regBound + 6) * c_Q ∧
        o.value < 2 ^ w' ∧
        st_H'.regs Q.regBound = h + 1 ∧
        st_H'.regs (Q.regBound + 1) = v_R1 ∧
        (∀ r < Q.regBound, st_H'.regs r = st_Q'.regs r) ∧
        (∀ r, st_Q'.regs r < 2 ^ w') ∧
        (∀ a, st_Q'.mem a < 2 ^ w') ∧
        (∀ a < 2 ^ w', st_H'.mem (h + 1 + a) = st_Q'.mem a) ∧
        (∀ addr, addr < h + 1 ∨ h + 1 + 2 ^ w' ≤ addr → st_H'.mem addr = st_H.mem addr) := by
  set R := Q.regBound
  have h1R : 1 ≤ R := one_le_regBound Q
  have hw'_pos : 0 < 2 ^ w' := Nat.two_pow_pos w'
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ hex; simp [exec] at hex
  | succ fuel ih =>
    intro s st_Q st_H o st_Q' c_Q hnr hs_reg hbase hW hregs hq_regs hq_mem hmem hex
    cases s with
    | nop =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hex
      rcases hex with ⟨rfl, rfl, rfl⟩
      exact ⟨st_H, 1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by omega, hw'_pos,
        hbase, hW, hregs, hq_regs, hq_mem, hmem, fun _ _ => rfl⟩
    | assign r e =>
      simp only [exec] at hex
      cases he : e.eval w' st_Q with
      | none => simp [he] at hex
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at hex
        rcases hex with ⟨rfl, rfl, rfl⟩
        simp only [Stmt.regBound, max_le_iff] at hs_reg
        obtain ⟨he_H, hv_lt⟩ := eval_relocExpr_local hw_le hh hs_reg.2 hregs hbase hq_regs hq_mem hmem he
        set st_H' : State := { st_H with regs := Function.update st_H.regs r v }
        have hr_R : r < R := by omega
        have hc_eq : (relocExpr R e).size + 1 ≤ (R + 6) * (e.size + 1) := by
          have h1 := relocExpr_size_le_local R e
          have h2 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
          have hmul : (R + 6) * (e.size + 1) = (R + 6) * e.size + (R + 6) := by ring
          omega
        refine ⟨st_H', (relocExpr R e).size + 1, runs_assign_iff.mpr ⟨v, he_H, rfl, rfl, rfl⟩,
          hc_eq, hw'_pos, ?_, ?_, ?_, ?_, hq_mem, hmem, fun _ _ => rfl⟩
        · simp [st_H', hbase, show R ≠ r by omega]
        · simp [st_H', hW, show R + 1 ≠ r by omega]
        · intro r' hr'
          by_cases hrr' : r' = r
          · subst hrr'; simp [st_H']
          · simp [st_H', hrr', hregs r' hr']
        · intro r'
          by_cases hrr' : r' = r
          · subst hrr'; simpa using hv_lt
          · simp [Function.update, hrr', hq_regs r']
    | store a e =>
      simp only [exec] at hex
      cases ha : a.eval w' st_Q with
      | none => simp [ha] at hex
      | some addr_v =>
        cases he : e.eval w' st_Q with
        | none => simp [ha, he] at hex
        | some val_v =>
          simp only [ha, he, Option.some.injEq, Prod.mk.injEq] at hex
          rcases hex with ⟨rfl, rfl, rfl⟩
          simp only [Stmt.regBound, max_le_iff] at hs_reg
          obtain ⟨ha_H, haddr_lt⟩ := eval_relocExpr_local hw_le hh hs_reg.1 hregs hbase hq_regs hq_mem hmem ha
          obtain ⟨he_H, hval_lt⟩ := eval_relocExpr_local hw_le hh hs_reg.2 hregs hbase hq_regs hq_mem hmem he
          have hsum_lt : h + 1 + addr_v < 2 ^ w := by omega
          have haddr_H : (Expr.bin .add (.reg R) (relocExpr R a)).eval w st_H = some (h + 1 + addr_v) := by
            simp [Expr.eval, BinOp.eval, hbase, ha_H, hsum_lt]
          set st_H' : State := { st_H with mem := Function.update st_H.mem (h + 1 + addr_v) val_v }
          have hc_eq : (Expr.bin .add (.reg R) (relocExpr R a)).size + (relocExpr R e).size + 1 ≤
              (R + 6) * (a.size + e.size + 1) := by
            have h1 := relocExpr_size_le_local R a
            have h2 := relocExpr_size_le_local R e
            have h3 : 3 * a.size ≤ (R + 6) * a.size := Nat.mul_le_mul_right a.size (by omega)
            have h4 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
            have hmul : (R + 6) * (a.size + e.size + 1) = (R + 6) * a.size + (R + 6) * e.size + (R + 6) := by ring
            simp only [Expr.size]; omega
          refine ⟨st_H', (Expr.bin .add (.reg R) (relocExpr R a)).size + (relocExpr R e).size + 1,
            runs_store_iff.mpr ⟨h + 1 + addr_v, val_v, haddr_H, he_H, rfl, rfl, rfl⟩,
            hc_eq, hw'_pos, hbase, hW, hregs, hq_regs, ?_, ?_, ?_⟩
          · intro addr'
            by_cases ha' : addr' = addr_v
            · subst ha'; simpa using hval_lt
            · simp [Function.update, ha', hq_mem addr']
          · intro addr' haddr'
            by_cases ha' : addr' = addr_v
            · subst ha'; simp [st_H']
            · have hne : h + 1 + addr' ≠ h + 1 + addr_v := by omega
              simp [st_H', Function.update, ha', hmem addr' haddr']
          · intro addr' houts
            have hne : addr' ≠ h + 1 + addr_v := by omega
            simp [st_H', hne]
    | rand _ => cases hnr
    | seq s₁ s₂ =>
      simp only [exec] at hex
      simp only [Stmt.regBound, max_le_iff] at hs_reg
      simp only [Stmt.NoRand] at hnr
      cases hs₁ : exec w' Q ω_Q fuel s₁ st_Q with
      | none => simp [hs₁] at hex
      | some res₁ =>
        rcases res₁ with ⟨o₁, st₁, c₁⟩
        cases o₁ with
        | returned v =>
          simp only [hs₁, Option.some.injEq, Prod.mk.injEq] at hex
          rcases hex with ⟨rfl, rfl, rfl⟩
          obtain ⟨st_H', c_H1, hr1, hc1, hv_lt, hb', hW', hregs', hqr', hqm', hmm', houts'⟩ :=
            ih s₁ st_Q st_H (.returned v) st₁ c₁ hnr.1 hs_reg.1 hbase hW hregs hq_regs hq_mem hmem hs₁
          refine ⟨st_H', c_H1 + 1, runs_seq_iff.mpr (Or.inl ⟨v, c_H1, hr1, rfl, rfl⟩),
            ?_, hv_lt, hb', hW', hregs', hqr', hqm', hmm', houts'⟩
          have : (R + 6) * (c₁ + 1) = (R + 6) * c₁ + (R + 6) := by ring
          omega
        | normal =>
          simp only [hs₁] at hex
          cases hs₂ : exec w' Q ω_Q fuel s₂ st₁ with
          | none => simp [hs₂] at hex
          | some res₂ =>
            rcases res₂ with ⟨o₂, st₂, c₂⟩
            simp only [hs₂, Option.some.injEq, Prod.mk.injEq] at hex
            rcases hex with ⟨rfl, rfl, rfl⟩
            obtain ⟨st_H1, c_H1, hr1, hc1, _, hb1, hW1, hregs1, hqr1, hqm1, hmm1, houts1⟩ :=
              ih s₁ st_Q st_H .normal st₁ c₁ hnr.1 hs_reg.1 hbase hW hregs hq_regs hq_mem hmem hs₁
            obtain ⟨st_H', c_H2, hr2, hc2, ho', hb', hW', hregs', hqr', hqm', hmm', houts'⟩ :=
              ih s₂ st₁ st_H1 o₂ st₂ c₂ hnr.2 hs_reg.2 hb1 hW1 hregs1 hqr1 hqm1 hmm1 hs₂
            refine ⟨st_H', c_H1 + c_H2 + 1,
              runs_seq_iff.mpr (Or.inr ⟨st_H1, c_H1, c_H2, hr1, hr2, rfl⟩),
              ?_, ho', hb', hW', hregs', hqr', hqm', hmm', ?_⟩
            · have : (R + 6) * (c₁ + c₂ + 1) = (R + 6) * c₁ + (R + 6) * c₂ + (R + 6) := by ring
              omega
            · intro addr haddr; rw [houts' addr haddr, houts1 addr haddr]
    | cond e s₁ s₂ =>
      simp only [exec] at hex
      cases he : e.eval w' st_Q with
      | none => simp [he] at hex
      | some v =>
        simp only [he] at hex
        cases hbr : exec w' Q ω_Q fuel (if v = 0 then s₂ else s₁) st_Q with
        | none => simp [hbr] at hex
        | some res =>
          rcases res with ⟨o₁, st₁, c₁⟩
          simp only [hbr, Option.some.injEq, Prod.mk.injEq] at hex
          rcases hex with ⟨rfl, rfl, rfl⟩
          simp only [Stmt.regBound, max_le_iff] at hs_reg
          simp only [Stmt.NoRand] at hnr
          obtain ⟨he_H, _⟩ := eval_relocExpr_local hw_le hh hs_reg.1 hregs hbase hq_regs hq_mem hmem he
          have hbr_nr : (if v = 0 then s₂ else s₁).NoRand := by split_ifs <;> [exact hnr.2; exact hnr.1]
          have hbr_reg : (if v = 0 then s₂ else s₁).regBound ≤ R := by
            split_ifs <;> [exact hs_reg.2.2; exact hs_reg.2.1]
          have hbr_reloc : relocStmt R b (if v = 0 then s₂ else s₁) =
              if v = 0 then relocStmt R b s₂ else relocStmt R b s₁ := by split_ifs <;> rfl
          obtain ⟨st_H', c_H1, hr_br, hc1, ho', hb', hW', hregs', hqr', hqm', hmm', houts'⟩ :=
            ih (if v = 0 then s₂ else s₁) st_Q st_H o₁ st₁ c₁ hbr_nr hbr_reg hbase hW hregs
              hq_regs hq_mem hmem hbr
          rw [hbr_reloc] at hr_br
          have hc_eq : (relocExpr R e).size + c_H1 + 1 ≤ (R + 6) * (e.size + c₁ + 1) := by
            have h1 := relocExpr_size_le_local R e
            have h2 : (R + 6) * (e.size + c₁ + 1) = (R + 6) * e.size + (R + 6) * c₁ + (R + 6) := by ring
            have h3 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
            omega
          exact ⟨st_H', (relocExpr R e).size + c_H1 + 1,
            runs_cond_iff.mpr ⟨v, c_H1, he_H, hr_br, rfl⟩,
            hc_eq, ho', hb', hW', hregs', hqr', hqm', hmm', houts'⟩
    | loop e body =>
      simp only [exec] at hex
      cases he : e.eval w' st_Q with
      | none => simp [he] at hex
      | some v =>
        simp only [he] at hex
        have hs_reg' := hs_reg
        have hnr' := hnr
        simp only [Stmt.regBound, max_le_iff] at hs_reg
        simp only [Stmt.NoRand] at hnr
        obtain ⟨he_H, _⟩ := eval_relocExpr_local hw_le hh hs_reg.1 hregs hbase hq_regs hq_mem hmem he
        by_cases hv : v = 0
        · subst hv
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hex
          rcases hex with ⟨rfl, rfl, rfl⟩
          have hc_eq : (relocExpr R e).size + 1 ≤ (R + 6) * (e.size + 1) := by
            have h1 := relocExpr_size_le_local R e
            have h2 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
            have hmul : (R + 6) * (e.size + 1) = (R + 6) * e.size + (R + 6) := by ring
            omega
          exact ⟨st_H, (relocExpr R e).size + 1, runs_loop_iff.mpr (Or.inl ⟨he_H, rfl, rfl, rfl⟩),
            hc_eq, hw'_pos, hbase, hW, hregs, hq_regs, hq_mem, hmem, fun _ _ => rfl⟩
        · simp only [hv, ↓reduceIte] at hex
          cases hbody : exec w' Q ω_Q fuel body st_Q with
          | none => simp [hbody] at hex
          | some res₁ =>
            rcases res₁ with ⟨o₁, st₁, c₁⟩
            cases o₁ with
            | returned u =>
              simp only [hbody, Option.some.injEq, Prod.mk.injEq] at hex
              rcases hex with ⟨rfl, rfl, rfl⟩
              obtain ⟨st_H', c_H1, hr1, hc1, hu_lt, hb', hW', hregs', hqr', hqm', hmm', houts'⟩ :=
                ih body st_Q st_H (.returned u) st₁ c₁ hnr hs_reg.2 hbase hW hregs hq_regs hq_mem hmem hbody
              have hc_eq : (relocExpr R e).size + c_H1 + 1 ≤ (R + 6) * (e.size + c₁ + 1) := by
                have h1 := relocExpr_size_le_local R e
                have h2 : (R + 6) * (e.size + c₁ + 1) = (R + 6) * e.size + (R + 6) * c₁ + (R + 6) := by ring
                have h3 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
                omega
              exact ⟨st_H', (relocExpr R e).size + c_H1 + 1,
                runs_loop_iff.mpr (Or.inr (Or.inl ⟨v, u, c_H1, he_H, hv, hr1, rfl, rfl⟩)),
                hc_eq, hu_lt, hb', hW', hregs', hqr', hqm', hmm', houts'⟩
            | normal =>
              simp only [hbody] at hex
              cases hloop : exec w' Q ω_Q fuel (.loop e body) st₁ with
              | none => simp [hloop] at hex
              | some res₂ =>
                rcases res₂ with ⟨o₂, st₂, c₂⟩
                simp only [hloop, Option.some.injEq, Prod.mk.injEq] at hex
                rcases hex with ⟨rfl, rfl, rfl⟩
                obtain ⟨st_H1, c_H1, hr1, hc1, _, hb1, hW1, hregs1, hqr1, hqm1, hmm1, houts1⟩ :=
                  ih body st_Q st_H .normal st₁ c₁ hnr hs_reg.2 hbase hW hregs hq_regs hq_mem hmem hbody
                obtain ⟨st_H', c_H2, hr2, hc2, ho', hb', hW', hregs', hqr', hqm', hmm', houts'⟩ :=
                  ih (.loop e body) st₁ st_H1 o₂ st₂ c₂ hnr' hs_reg' hb1 hW1 hregs1 hqr1 hqm1 hmm1 hloop
                have hc_eq : (relocExpr R e).size + c_H1 + c_H2 + 1 ≤
                    (R + 6) * (e.size + c₁ + c₂ + 1) := by
                  have h1 := relocExpr_size_le_local R e
                  have h2 : (R + 6) * (e.size + c₁ + c₂ + 1) =
                      (R + 6) * e.size + (R + 6) * c₁ + (R + 6) * c₂ + (R + 6) := by ring
                  have h3 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
                  omega
                refine ⟨st_H', (relocExpr R e).size + c_H1 + c_H2 + 1,
                  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st_H1, c_H1, c_H2, he_H, hv, hr1, hr2, rfl⟩)),
                  hc_eq, ho', hb', hW', hregs', hqr', hqm', hmm', ?_⟩
                intro addr haddr; rw [houts' addr haddr, houts1 addr haddr]
    | call r f args =>
      simp only [exec] at hex
      cases hargs : evalArgs w' st_Q args with
      | none => simp [hargs] at hex
      | some vs =>
        cases hproc : Q.procs[f]? with
        | none => simp [hargs, hproc] at hex
        | some body =>
          simp only [hargs, hproc] at hex
          cases hbody : exec w' Q ω_Q fuel body { st_Q with regs := fun i => vs.getD i 0 } with
          | none => simp only [hbody] at hex; cases hex
          | some res =>
            rcases res with ⟨o₁, st₁, c₁⟩
            simp only [hbody, Option.some.injEq, Prod.mk.injEq] at hex
            rcases hex with ⟨rfl, rfl, rfl⟩
            simp only [Stmt.regBound, max_le_iff] at hs_reg
            rcases hs_reg with ⟨hr_R, hargs_len, hargs_rb⟩
            obtain ⟨hargs_H, hvs_len, hvs_lt⟩ :=
              evalArgs_reloc_local hw_le hh hargs_rb hregs hbase hq_regs hq_mem hmem hargs
            have hbody_mem : body ∈ Q.procs := List.mem_of_getElem? hproc
            have hbody_nr : body.NoRand := hdet body hbody_mem
            have hbody_rb : body.regBound ≤ R := regBound_le_of_mem hbody_mem
            have hproc_H : p.procs[b + 1 + f]? = some (relocStmt R b body) := hp f body hproc
            let pad : List Expr := List.replicate (R - args.length) (.const 0)
            let extra : List Expr := [.reg R, .reg (R + 1)]
            let fullArgs : List Expr := args.map (relocExpr R) ++ pad ++ extra
            have hpad_eval : evalArgs w st_H pad = some (List.replicate (R - args.length) 0) :=
              evalArgs_replicate_zero (w := w)
            have hextra_eval : evalArgs w st_H extra = some [h + 1, v_R1] := by
              simp [extra, evalArgs, Expr.eval, hbase, hW]
            have hfull_eval : evalArgs w st_H fullArgs =
                some (vs ++ List.replicate (R - args.length) 0 ++ [h + 1, v_R1]) :=
              evalArgs_append (evalArgs_append hargs_H hpad_eval) hextra_eval
            set vs_H := vs ++ List.replicate (R - args.length) 0 ++ [h + 1, v_R1]
            set st_Q_call : State := { st_Q with regs := fun i => vs.getD i 0 }
            set st_H_call : State := startState vs_H st_H.mem st_H.pos
            have hlen1 : (vs ++ List.replicate (R - args.length) 0).length = R := by
              simp [hvs_len]; omega
            have hbase_call : st_H_call.regs R = h + 1 := by
              simp only [st_H_call, startState, vs_H, List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_right (le_of_eq hlen1), hlen1, Nat.sub_self]; simp
            have hW_call : st_H_call.regs (R + 1) = v_R1 := by
              simp only [st_H_call, startState, vs_H, List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_right (by rw [hlen1]; omega), hlen1,
                show R + 1 - R = 1 by omega]; simp
            have hregs_call : ∀ i < R, st_H_call.regs i = st_Q_call.regs i := by
              intro i hi
              simp only [st_H_call, startState, st_Q_call, vs_H, List.getD_eq_getElem?_getD]
              by_cases hivs : i < vs.length
              · rw [List.getElem?_append_left (by omega), List.getElem?_append_left hivs]
              · rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega)]
                rw [List.getElem?_replicate, ite_eq_left (by omega),
                  List.getElem?_eq_none (by omega)]; rfl
            have hq_regs_call : ∀ i, st_Q_call.regs i < 2 ^ w' := by
              intro i
              simp only [st_Q_call]
              by_cases hivs : i < vs.length
              · rw [List.getD_eq_getElem _ _ hivs]; exact hvs_lt _ (List.getElem_mem hivs)
              · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hivs)]; exact hw'_pos
            obtain ⟨st_H1, c_H1, hr1, hc1, ho1_lt, _, _, _, _, hqm1, hmm1, houts1⟩ :=
              ih body st_Q_call st_H_call o₁ st₁ c₁ hbody_nr hbody_rb hbase_call hW_call
                hregs_call hq_regs_call hq_mem hmem hbody
            set st_H' : State :=
              { mem := st_H1.mem, regs := Function.update st_H.regs r o₁.value, pos := st_H1.pos }
            have hc_eq : argsSize fullArgs + c_H1 + 1 ≤ (R + 6) * (argsSize args + c₁ + 1) := by
              have hsz : argsSize fullArgs = argsSize (args.map (relocExpr R)) + (R - args.length) + 2 := by
                dsimp only [fullArgs, pad, extra]
                rw [argsSize_append_local, argsSize_append_local, argsSize_replicate_const_zero]
                simp [argsSize, Expr.size]
              have h1 := argsSize_reloc_le_local R args
              have h2 : (R + 6) * (argsSize args + c₁ + 1) =
                  (R + 6) * argsSize args + (R + 6) * c₁ + (R + 6) := by ring
              have h3 : 3 * argsSize args ≤ (R + 6) * argsSize args :=
                Nat.mul_le_mul_right (argsSize args) (by omega)
              omega
            refine ⟨st_H', argsSize fullArgs + c_H1 + 1,
              runs_call_iff.mpr ⟨vs_H, relocStmt R b body, o₁, st_H1, c_H1, hfull_eval, hproc_H,
                hr1, rfl, rfl, rfl⟩,
              hc_eq, hw'_pos, ?_, ?_, ?_, ?_, hqm1, hmm1, houts1⟩
            · simp [st_H', hbase, show R ≠ r by omega]
            · simp [st_H', hW, show R + 1 ≠ r by omega]
            · intro r' hr'
              by_cases hrr' : r' = r
              · subst hrr'; cases o₁ <;> simp [st_H', Outcome.value]
              · simp [st_H', hrr', hregs r' hr']
            · intro r'
              by_cases hrr' : r' = r
              · subst hrr'; dsimp only; rw [Function.update_self]; cases o₁ <;> exact ho1_lt
              · simp [Function.update, hrr', hq_regs r']
    | ret e =>
      simp only [exec] at hex
      cases he : e.eval w' st_Q with
      | none => simp [he] at hex
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at hex
        rcases hex with ⟨rfl, rfl, rfl⟩
        obtain ⟨he_H, hv_lt⟩ := eval_relocExpr_local hw_le hh hs_reg hregs hbase hq_regs hq_mem hmem he
        have hc_eq : (relocExpr R e).size + 1 ≤ (R + 6) * (e.size + 1) := by
          have h1 := relocExpr_size_le_local R e
          have h2 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
          have hmul : (R + 6) * (e.size + 1) = (R + 6) * e.size + (R + 6) := by ring
          omega
        exact ⟨st_H, (relocExpr R e).size + 1, runs_ret_iff.mpr ⟨v, he_H, rfl, rfl, rfl⟩,
          hc_eq, hv_lt, hbase, hW, hregs, hq_regs, hq_mem, hmem, fun _ _ => rfl⟩

/-! ## Relocated guest run of `lemma55Module` at `guestBase` -/

/-- Relocated procedure list of `lemma55Module Q_AN c_AN K_AN h`, intended to be placed at index
`bReloc + 1` in a host program (so entry `lemma55IdxInit = 0` sits at `bReloc + 1`). -/
noncomputable def lemma55RelocProcs (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (bReloc h : ℕ) :
    List Stmt :=
  let Q := lemma55Module Q_AN c_AN K_AN h
  Q.procs.map (relocStmt Q.regBound bReloc)

private lemma map_reloc_length (Q : Program) (bReloc : ℕ) :
    (Q.procs.map (relocStmt Q.regBound bReloc)).length = Q.procs.length :=
  List.length_map _

private lemma map_reloc_getElem (Q : Program) (bReloc i : ℕ) (hi : i < Q.procs.length) :
    (Q.procs.map (relocStmt Q.regBound bReloc))[i]'(by rw [map_reloc_length]; exact hi) =
      relocStmt Q.regBound bReloc Q.procs[i] :=
  List.getElem_map _

lemma lemma55RelocProcs_length (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (bReloc h : ℕ) :
    (lemma55RelocProcs Q_AN c_AN K_AN bReloc h).length =
      (lemma55Module Q_AN c_AN K_AN h).procs.length :=
  map_reloc_length (lemma55Module Q_AN c_AN K_AN h) bReloc

lemma lemma55RelocProcs_getElem (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (bReloc h i : ℕ)
    (hi : i < (lemma55Module Q_AN c_AN K_AN h).procs.length) :
    (lemma55RelocProcs Q_AN c_AN K_AN bReloc h)[i]'(by rw [lemma55RelocProcs_length]; exact hi) =
      relocStmt (lemma55Module Q_AN c_AN K_AN h).regBound bReloc
        (lemma55Module Q_AN c_AN K_AN h).procs[i] :=
  map_reloc_getElem (lemma55Module Q_AN c_AN K_AN h) bReloc i hi

private lemma relocStmt_noRand {R b : ℕ} {s : Stmt} (hs : s.NoRand) :
    (relocStmt R b s).NoRand := by
  induction s with
  | nop => trivial
  | assign _ _ => trivial
  | store _ _ => trivial
  | rand _ => exact False.elim hs
  | seq _ _ ih1 ih2 => exact ⟨ih1 hs.1, ih2 hs.2⟩
  | cond _ _ _ ih1 ih2 => exact ⟨ih1 hs.1, ih2 hs.2⟩
  | loop _ _ ih => exact ih hs
  | call _ _ _ => trivial
  | ret _ => trivial

lemma lemma55RelocProcs_noRand (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (bReloc h : ℕ) :
    ∀ s ∈ lemma55RelocProcs Q_AN c_AN K_AN bReloc h, s.NoRand := by
  intro s hs
  dsimp only [lemma55RelocProcs] at hs
  rw [List.mem_map] at hs
  rcases hs with ⟨s₀, hs₀, rfl⟩
  exact relocStmt_noRand (lemma55Module_isDeterministic Q_AN c_AN K_AN h s₀ hs₀)

/-- Relocated execution of `lemma55Module` at `guestBase` on a canonical memory image of
`(G₀, ℓ₀, k)` produces the exact states `canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k j`
represented in shifted memory `fun a => st_H'.mem (guestBase + a)` for all `j < k`. -/
theorem canonicalLSF_relocated_run {w h c_AN bReloc guestBase L_in P_fp k : ℕ}
    {p Q_AN : Program} {K_AN : ℝ} {G₀ : MGraph} {ℓ₀ : ℕ → ℝ} {mem : ℕ → ℕ}
    (pos : ℕ) (ω : ℕ → Bool)
    (hV : CanonicalLSFValid Q_AN c_AN K_AN h L_in P_fp G₀ (safeLen G₀ ℓ₀) k)
    (hp : p.HasAt (bReloc + 1) (lemma55RelocProcs Q_AN c_AN K_AN bReloc h))
    (hgb1 : 1 ≤ guestBase)
    (hw_le : canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k ≤ w)
    (hgb_sp : guestBase + 2 ^ canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k ≤ 2 ^ w)
    (hmem_eq : ∀ a < 2 ^ canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k,
      mem (guestBase + a) = canonGuestMem G₀ ℓ₀ h L_in P_fp a)
    (hz_above : ZeroFrom mem (guestBase + 2 ^ canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k)) :
    let Q := lemma55Module Q_AN c_AN K_AN h
    let R := Q.regBound
    let r := chosenGuestRun hV
    let w' := canonWordBits Q_AN c_AN K_AN h L_in P_fp G₀ k
    let callArgs := canonGuestArgs K_AN L_in P_fp G₀ k ++ List.replicate (R - 10) 0 ++ [guestBase, 0]
    ∃ body st_H' c_H,
      p.procs[bReloc + 1]? = some body ∧
      Runs w p ω body (startState callArgs mem pos) (.returned r.endHeap) st_H' c_H ∧
      c_H ≤ (R + 6) * lemma55Cost Q_AN c_AN K_AN h L_in (canonLw K_AN L_in G₀.n k) P_fp k G₀.n G₀.m ∧
      canonHeap G₀ L_in k ≤ r.endHeap ∧
      r.endHeap ≤ canonHeap G₀ L_in k +
        lemma55Space Q_AN K_AN c_AN h L_in (canonLw K_AN L_in G₀.n k) P_fp k
          (canonVCap G₀) (canonECap G₀) G₀.n G₀.m ∧
      ZeroFrom st_H'.mem (guestBase + r.endHeap) ∧
      (∀ addr, addr < guestBase ∨ guestBase + 2 ^ w' ≤ addr → st_H'.mem addr = mem addr) ∧
      (∀ a < 2 ^ w', st_H'.mem (guestBase + a) = r.st'.mem a) ∧
      (∀ a < 2 ^ w', st_H'.mem (guestBase + a) < 2 ^ w') ∧
      (∀ j < k, st_H'.mem (guestBase + canonHandlesOut G₀ L_in + j) = r.hs j ∧
        (LSFRep h).rep (r.hs j)
          (canonicalLSFInitWithH h Q_AN c_AN K_AN L_in P_fp G₀ ℓ₀ k j)
          (r.x₀ j) (fun a => st_H'.mem (guestBase + a)) ∧
        (r.x₀ j).vCap = canonVCap G₀ ∧ (r.x₀ j).eCap = canonECap G₀ ∧
        (r.x₀ j).L_w = canonLw K_AN L_in G₀.n k ∧
        (r.x₀ j).n0 = G₀.n ∧ (r.x₀ j).m0 = G₀.E.card ∧
        ∀ a, (LSFRep h).foot (r.hs j) (r.x₀ j) a → canonHeap G₀ L_in k ≤ a ∧ a < r.endHeap) ∧
      (∀ j₁ < k, ∀ j₂ < k, j₁ ≠ j₂ →
        ∀ a, (LSFRep h).foot (r.hs j₁) (r.x₀ j₁) a → ¬ (LSFRep h).foot (r.hs j₂) (r.x₀ j₂) a) := by
  intro Q R r w' callArgs
  have hℓ_eq : ∀ e ∈ G₀.E, safeLen G₀ ℓ₀ e = ℓ₀ e := fun _ he => safeLen_eq_of_mem ℓ₀ he
  have hcmem_eq : canonGuestMem G₀ (safeLen G₀ ℓ₀) h L_in P_fp = canonGuestMem G₀ ℓ₀ h L_in P_fp :=
    canonGuestMem_eq_of_eq_on_E hℓ_eq
  have hG₀ : G₀.IsValid := hV.2.2.2.2.2.2.2.2.1
  have hLin1 : 1 ≤ L_in := hV.2.2.1
  have hk : 1 ≤ k := hV.2.2.2.2.2.1
  set s0 := lemma55InitProc 3 (lemma55BaseLsf 0 + lsfIdxInit) 1 h
  have hs0_get : Q.procs[0]? = some s0 := by
    have hp0 : Q.HasAt 0 (lemma55ModuleProcs Q_AN c_AN K_AN 0 h) := fun i hi => by
      simp only [Q, lemma55Module, Nat.zero_add, List.getElem?_eq_getElem hi]
    exact (lemma55HasAt_split hp0).1
  have hs0_mem : s0 ∈ Q.procs := List.mem_of_getElem? hs0_get
  have hdet : Q.IsDeterministic := lemma55Module_isDeterministic Q_AN c_AN K_AN h
  have hs0_nr : s0.NoRand := hdet s0 hs0_mem
  have hs0_rb : s0.regBound ≤ R := regBound_le_of_mem hs0_mem
  have hR_ge10 : 10 ≤ R := by
    have h10 : 10 ≤ s0.regBound := by
      dsimp only [s0, lemma55InitProc, Stmt.regBound, Expr.regBound]; omega
    exact le_trans h10 hs0_rb
  have hp_rel : ∀ f body, Q.procs[f]? = some body →
      p.procs[bReloc + 1 + f]? = some (relocStmt R bReloc body) := by
    intro f body hget
    have hf_lt : f < Q.procs.length := (List.getElem?_eq_some_iff.mp hget).1
    have hget_m := hp.get (i := f) (by rw [lemma55RelocProcs_length]; exact hf_lt)
    rw [lemma55RelocProcs_getElem Q_AN c_AN K_AN bReloc h f hf_lt] at hget_m
    have hb_eq : (lemma55Module Q_AN c_AN K_AN h).procs[f]'hf_lt = body :=
      Option.some.inj ((List.getElem?_eq_getElem hf_lt).symm.trans hget)
    rw [hb_eq] at hget_m
    exact hget_m
  have hp0 : p.procs[bReloc + 1]? = some (relocStmt R bReloc s0) := by
    simpa using hp_rel 0 s0 hs0_get
  -- Unpack guest run `r.hrun`
  obtain ⟨fuel, hfuel⟩ := r.hrun (fun _ => false)
  set st_Q := startState (canonGuestArgs K_AN L_in P_fp G₀ k) (canonGuestMem G₀ (safeLen G₀ ℓ₀) h L_in P_fp) 0
  set st_H := startState callArgs mem pos
  have hargs_len : (canonGuestArgs K_AN L_in P_fp G₀ k).length = 10 := rfl
  have hlen_prefix : (canonGuestArgs K_AN L_in P_fp G₀ k ++ List.replicate (R - 10) 0).length = R := by
    simp [hargs_len]; omega
  have hbase_H : st_H.regs R = (guestBase - 1) + 1 := by
    have hgb_eq : (guestBase - 1) + 1 = guestBase := by omega
    rw [hgb_eq]
    simp only [st_H, startState, callArgs, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_of_eq hlen_prefix), hlen_prefix, Nat.sub_self]; simp
  have hW_H : st_H.regs (R + 1) = 0 := by
    simp only [st_H, startState, callArgs, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by rw [hlen_prefix]; omega), hlen_prefix,
      show R + 1 - R = 1 by omega]; simp
  have hregs_H : ∀ i < R, st_H.regs i = st_Q.regs i := by
    intro i hi
    simp only [st_H, st_Q, startState, callArgs, List.getD_eq_getElem?_getD]
    by_cases hi10 : i < 10
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by rw [hargs_len]; exact hi10)]
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by rw [hargs_len]; omega)]
      rw [List.getElem?_replicate, ite_eq_left (by rw [hargs_len]; omega),
        List.getElem?_eq_none (by rw [hargs_len]; omega)]; rfl
  obtain ⟨hw_h, hB_lt, _⟩ := canonWordBits_bounds Q_AN c_AN K_AN h L_in P_fp G₀ k
  have hq_regs : ∀ i, st_Q.regs i < 2 ^ w' := by
    intro i
    simp only [st_Q, startState]
    have hsp_lt : canonHeap G₀ L_in k +
        lemma55Space Q_AN K_AN c_AN h L_in (canonLw K_AN L_in G₀.n k) P_fp k
          (canonVCap G₀) (canonECap G₀) G₀.n G₀.m < 2 ^ w' :=
      lt_trans (Nat.lt_succ_of_le (le_max_left _ _)) hB_lt
    have hP_lt : P_fp < 2 ^ w' := by
      have : 2 * P_fp + 9 < 2 ^ w' :=
        lt_trans (Nat.lt_succ_of_le (le_trans (le_max_left _ _) (le_max_right _ _))) hB_lt
      omega
    have hLw_lt : canonLw K_AN L_in G₀.n k < 2 ^ w' := by
      have h1 : canonLw K_AN L_in G₀.n k ≤
          lemma55Space Q_AN K_AN c_AN h L_in (canonLw K_AN L_in G₀.n k) P_fp k
            (canonVCap G₀) (canonECap G₀) G₀.n G₀.m := by
        unfold lemma55Space; dsimp only
        have ha : canonLw K_AN L_in G₀.n k ≤ 2 * canonLw K_AN L_in G₀.n k := by omega
        exact Nat.le_trans ha (Nat.le_trans (Nat.le_add_left _ _)
          (Nat.le_trans (Nat.le_add_right _ _)
            (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))
      omega
    have hLin_lt : L_in < 2 ^ w' := lt_of_le_of_lt (canonLw_ge_Lin K_AN L_in G₀.n k) hLw_lt
    have hvCap_lt : canonVCap G₀ < 2 ^ w' := by
      unfold canonHeap canonHandlesOut canonLenArr dynGraphSize at hsp_lt; omega
    have heCap_lt : canonECap G₀ < 2 ^ w' := by
      unfold canonHeap canonHandlesOut canonLenArr dynGraphSize at hsp_lt; omega
    have hlen_lt : canonLenArr G₀ < 2 ^ w' := by unfold canonHeap canonHandlesOut at hsp_lt; omega
    have hhnd_lt : canonHandlesOut G₀ L_in < 2 ^ w' := by unfold canonHeap at hsp_lt; omega
    have hheap_lt : canonHeap G₀ L_in k < 2 ^ w' := by omega
    have hk_lt : k < 2 ^ w' := by unfold canonHeap at hsp_lt; omega
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      simp [canonGuestArgs, hlen_lt, hLin_lt, hP_lt, hk_lt, hLw_lt,
        hvCap_lt, heCap_lt, hhnd_lt, hheap_lt]
  have hq_mem : ∀ a, st_Q.mem a < 2 ^ w' := canonGuestMem_lt_two_pow hG₀
  have hmem_shift : ∀ a < 2 ^ w', st_H.mem ((guestBase - 1) + 1 + a) = st_Q.mem a := fun a ha => by
    dsimp only [st_H, st_Q, startState]
    rw [show (guestBase - 1) + 1 = guestBase by omega, hmem_eq a ha, hcmem_eq]
  obtain ⟨st_H', c_H, hrun_H, hc_H, _, _, _, _, _, hqm', hmem_H', houts_H'⟩ :=
    runs_relocStmt_noRand (h := guestBase - 1) (b := bReloc) (v_R1 := 0) (ω := ω)
      hdet hp_rel hw_le (by omega) fuel s0 st_Q st_H (.returned r.endHeap) r.st' r.c
      hs0_nr hs0_rb hbase_H hW_H hregs_H hq_regs hq_mem hmem_shift hfuel
  have hgb_id : (guestBase - 1) + 1 = guestBase := by omega
  rw [hgb_id] at hmem_H' houts_H'
  have hend_lt_w' : r.endHeap < 2 ^ w' :=
    lt_of_le_of_lt r.hheap_le (lt_trans (Nat.lt_succ_of_le (le_max_left _ _)) hB_lt)
  refine ⟨relocStmt R bReloc s0, st_H', c_H, hp0, hrun_H,
    le_trans hc_H (Nat.mul_le_mul_left (R + 6) r.hcost),
    r.hheap_ge, r.hheap_le, ?_, houts_H', hmem_H',
    fun a ha => (hmem_H' a ha).symm ▸ hqm' a, ?_, r.hdisj⟩
  · -- ZeroFrom st_H'.mem (guestBase + r.endHeap)
    intro z hz
    by_cases hlt : z < guestBase + 2 ^ w'
    · have hsub : z - guestBase < 2 ^ w' := by omega
      have h1 := hmem_H' (z - guestBase) hsub
      rw [show guestBase + (z - guestBase) = z by omega] at h1
      rw [h1]
      exact r.hz' (z - guestBase) (by omega)
    · rw [houts_H' z (Or.inr (by dsimp only [w'] at hlt ⊢; omega))]
      exact hz_above z (by dsimp only [w'] at hlt ⊢; omega)
  · intro j hj
    obtain ⟨hhnd_j, hrep_j, hv_j, he_j, hlw_j, hn_j, hm_j, hfoot_j⟩ := r.hrep j hj
    have hhnd_lt : canonHandlesOut G₀ L_in + j < 2 ^ w' := by
      have : canonHandlesOut G₀ L_in + j < canonHeap G₀ L_in k := by unfold canonHeap; omega
      exact lt_of_lt_of_le this (le_trans r.hheap_ge hend_lt_w'.le)
    refine ⟨?_, ?_, hv_j, he_j, hlw_j, hn_j, hm_j, hfoot_j⟩
    · rw [show guestBase + canonHandlesOut G₀ L_in + j = guestBase + (canonHandlesOut G₀ L_in + j) by omega,
          hmem_H' _ hhnd_lt, hhnd_j]
    · rw [canonicalLSFInitWithH_eq_chosen hV]
      exact (lsfRep_local h (r.hs j) (r.S₀ j) (r.x₀ j) r.st'.mem (fun a => st_H'.mem (guestBase + a))
        fun a ha => (hmem_H' a (lt_trans (hfoot_j a ha).2 hend_lt_w')).symm).1 hrep_j

end MinCostFlow.SparseCore.Program
