module

public import WordRAM.Logic

import MinCostFlow.SparseCore.Program.AssemblyFirstRotProg
import WordRAM.Tactic

/-!
# Linear two-pass deduplication for Phase 4 rotation (`AssemblyFirstStepP4RotDedup`)

Deduplicates a raw candidate vertex list `rawL[0..m)` (`∀ v ∈ rawL, v < vCap`) in `O(m)` time
before `asmFirstBuildRotStmt` merge-sorts it:
1. Pass 1 computes `flagCap := rotFlagCap rawL = max_{v ∈ rawL} (v + 1) ≤ vCap` without writing
   memory;
2. Pass 2 scans `rawL[0..m)` using the zeroed flag array `[hE, hE + flagCap)` and writes the
   distinct vertices `uniqL := rotDedup rawL` of length `u ≤ min m vCap` into
   `[hE + flagCap, hE + flagCap + u)`.

Because `flagCap ≤ vCap` is computed directly from `rawL`, `p4RotDedupStmt` needs no `vCap`
register argument and fits inline inside `asmFirstP4RotStmt`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM

/-! ## The procedure -/

@[expose] public section

/-- Linear two-pass deduplication of the raw list `rawL[0..m)` (`reg 6 = rawPtr`, `reg 5 = h`
holding `m`, `reg 10 = hE` zeroed): computes `flagCap = max_{v ∈ rawL} (v + 1)` in `reg 13`,
deduplicates into `uniqPtr = hE + flagCap` (`reg 14`) of length `u` (`reg 15`) using zeroed flags
at `[hE, hE + flagCap)`, and sets `reg 16 := uniqPtr + u`. -/
def p4RotDedupStmt : Stmt :=
  .assign 12 (.load (.reg 5)) ;;
  .assign 13 (.const 0) ;;
  forRange 14 (.const 0) (.reg 12)
    (.assign 15 (.load (.bin .add (.reg 6) (.reg 14))) ;;
     .cond (.bin .lt (.reg 13) (.bin .add (.reg 15) (.const 1)))
       (.assign 13 (.bin .add (.reg 15) (.const 1)))
       .nop) ;;
  .assign 14 (.bin .add (.reg 10) (.reg 13)) ;;
  .assign 15 (.const 0) ;;
  forRange 16 (.const 0) (.reg 12)
    (.assign 17 (.load (.bin .add (.reg 6) (.reg 16))) ;;
     .cond (.bin .eq (.load (.bin .add (.reg 10) (.reg 17))) (.const 0))
       (.store (.bin .add (.reg 10) (.reg 17)) (.const 1) ;;
        .store (.bin .add (.reg 14) (.reg 15)) (.reg 17) ;;
        .assign 15 (.bin .add (.reg 15) (.const 1)))
       .nop) ;;
  .assign 16 (.bin .add (.reg 14) (.reg 15))

/-- Tight upper bound `max_{v ∈ L} (v + 1)` (and `0` on `[]`). -/
def rotFlagCap (L : List ℕ) : ℕ :=
  L.foldl (fun acc v => max acc (v + 1)) 0

/-- First-occurrence deduplication of `L`. -/
def rotDedup (L : List ℕ) : List ℕ :=
  L.foldl (fun acc v => if v ∈ acc then acc else acc ++ [v]) []

end

/-! ## Pure model lemmas -/

private lemma rotFlagCap_append (L : List ℕ) (v : ℕ) :
    rotFlagCap (L ++ [v]) = max (rotFlagCap L) (v + 1) := by
  simp [rotFlagCap]

private lemma rotFlagCap_gt_aux :
    ∀ (L : List ℕ) (init v : ℕ), v ∈ L → v < L.foldl (fun acc x => max acc (x + 1)) init := by
  intro L
  induction L with
  | nil => intro _ _ h; cases h
  | cons a rest ih =>
    intro init v hv
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hv with rfl | hrest
    · have hmono : ∀ (xs : List ℕ) (acc : ℕ),
          acc ≤ xs.foldl (fun acc x => max acc (x + 1)) acc := by
        intro xs
        induction xs with
        | nil => intro acc; exact le_rfl
        | cons b bs ihb =>
          intro acc
          simp only [List.foldl_cons]
          exact le_trans (le_max_left _ _) (ihb _)
      exact lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self v) (le_max_right init (v + 1)))
        (hmono rest _)
    · exact ih _ v hrest

private lemma rotFlagCap_le_aux :
    ∀ (L : List ℕ) (init cap : ℕ), init ≤ cap → (∀ v ∈ L, v < cap) →
      L.foldl (fun acc x => max acc (x + 1)) init ≤ cap := by
  intro L
  induction L with
  | nil => intro init cap h _; exact h
  | cons a rest ih =>
    intro init cap h hall
    simp only [List.foldl_cons]
    exact ih (max init (a + 1)) cap (max_le h (Nat.succ_le_of_lt (hall a List.mem_cons_self)))
      (fun v hv => hall v (List.mem_cons_of_mem a hv))

private lemma rotDedup_append (L : List ℕ) (v : ℕ) :
    rotDedup (L ++ [v]) = if v ∈ rotDedup L then rotDedup L else rotDedup L ++ [v] := by
  simp only [rotDedup, List.foldl_append, List.foldl_cons, List.foldl_nil]
  by_cases h : v ∈ List.foldl (fun acc v => if v ∈ acc then acc else acc ++ [v]) [] L <;> simp [h]

private lemma rotDedup_nodup_aux :
    ∀ (L acc : List ℕ), acc.Nodup →
      (L.foldl (fun a v => if v ∈ a then a else a ++ [v]) acc).Nodup := by
  intro L
  induction L with
  | nil => intro acc h; exact h
  | cons x rest ih =>
    intro acc h
    simp only [List.foldl_cons]
    split_ifs with hx
    · exact ih acc h
    · exact ih (acc ++ [x]) (List.nodup_append.mpr ⟨h, List.nodup_singleton x,
        fun a ha b hb hab => hx (by rw [← List.mem_singleton.mp hb, ← hab]; exact ha)⟩)

private lemma mem_rotDedup_aux :
    ∀ (L acc : List ℕ) (v : ℕ),
      v ∈ L.foldl (fun a x => if x ∈ a then a else a ++ [x]) acc ↔ v ∈ acc ∨ v ∈ L := by
  intro L
  induction L with
  | nil => intro acc v; simp
  | cons x rest ih =>
    intro acc v
    simp only [List.foldl_cons, List.mem_cons]
    split_ifs with hx
    · rw [ih]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hx
        · exact Or.inr h
    · rw [ih]
      simp only [List.mem_append, List.mem_singleton]
      tauto

private lemma rotDedup_length_le_length_aux :
    ∀ (L acc : List ℕ),
      (L.foldl (fun a x => if x ∈ a then a else a ++ [x]) acc).length ≤ acc.length + L.length := by
  intro L
  induction L with
  | nil => intro acc; simp
  | cons x rest ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    split_ifs
    · have := ih acc; omega
    · have := ih (acc ++ [x]); simp only [List.length_append, List.length_singleton] at this; omega

public section

theorem p4RotDedupStmt_noRand : p4RotDedupStmt.NoRand := by
  simp [p4RotDedupStmt, forRange, forUp, Stmt.NoRand]

theorem rotFlagCap_gt {L : List ℕ} {v : ℕ} (hv : v ∈ L) : v < rotFlagCap L :=
  rotFlagCap_gt_aux L 0 v hv

theorem rotFlagCap_le {L : List ℕ} {cap : ℕ} (h : ∀ v ∈ L, v < cap) :
    rotFlagCap L ≤ cap :=
  rotFlagCap_le_aux L 0 cap (Nat.zero_le _) h

theorem rotDedup_nodup (L : List ℕ) : (rotDedup L).Nodup :=
  rotDedup_nodup_aux L [] List.nodup_nil

theorem mem_rotDedup (L : List ℕ) (v : ℕ) : v ∈ rotDedup L ↔ v ∈ L := by
  simpa [rotDedup] using mem_rotDedup_aux L [] v

theorem rotDedup_toFinset (L : List ℕ) : (rotDedup L).toFinset = L.toFinset := by
  ext v
  simp [mem_rotDedup]

theorem rotDedup_length_le_length (L : List ℕ) : (rotDedup L).length ≤ L.length := by
  simpa [rotDedup] using rotDedup_length_le_length_aux L []

theorem rotDedup_length_le_cap {L : List ℕ} {cap : ℕ} (h : ∀ v ∈ L, v < cap) :
    (rotDedup L).length ≤ cap := by
  classical
  rw [← List.toFinset_card_of_nodup (rotDedup_nodup L)]
  calc (rotDedup L).toFinset.card ≤ (Finset.range cap).card :=
        Finset.card_le_card fun v hv =>
          Finset.mem_range.mpr (h v ((mem_rotDedup L v).mp (List.mem_toFinset.mp hv)))
    _ = cap := Finset.card_range cap

theorem rotDedup_length_le_min {L : List ℕ} {cap : ℕ} (h : ∀ v ∈ L, v < cap) :
    (rotDedup L).length ≤ min L.length cap :=
  le_min (rotDedup_length_le_length L) (rotDedup_length_le_cap h)

/-! ## Verification of `p4RotDedupStmt` -/

/-- **Run of `p4RotDedupStmt`**: computes `flagCap = rotFlagCap rawL ≤ vCap` and writes
`uniqL = rotDedup rawL` of length `u ≤ min rawL.length vCap` at `uniqPtr = hE + flagCap`,
preserving memory below `hE`, keeping `ZeroFrom` from `hBuild = uniqPtr + u`, and costing at most
`100 * rawL.length + 70`. -/
theorem p4RotDedup_runs {w h rawPtr hE vCap : ℕ} {p : Program}
    {rawL : List ℕ} {st₀ : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hr5 : st₀.regs 5 = h) (hr6 : st₀.regs 6 = rawPtr) (hr10 : st₀.regs 10 = hE)
    (hmh : st₀.mem h = rawL.length)
    (hraw : ListAt st₀.mem rawPtr rawL) (hraw_le : rawPtr + rawL.length ≤ hE)
    (hraw_cap : ∀ v ∈ rawL, v < vCap) (hvCap_w : vCap < 2 ^ w)
    (hz : ZeroFrom st₀.mem hE)
    (hsp : hE + vCap + rawL.length < 2 ^ w) :
    let flagCap := rotFlagCap rawL
    let uniqL := rotDedup rawL
    let uniqPtr := hE + flagCap
    let hBuild := uniqPtr + uniqL.length
    ∃ st' c,
      Runs w p ω p4RotDedupStmt st₀ .normal st' c ∧
      st'.regs 5 = h ∧
      st'.regs 14 = uniqPtr ∧
      st'.regs 15 = uniqL.length ∧
      st'.regs 16 = hBuild ∧
      ListAt st'.mem uniqPtr uniqL ∧
      ZeroFrom st'.mem hBuild ∧
      (∀ a < hE, st'.mem a = st₀.mem a) ∧
      c ≤ 100 * rawL.length + 70 := by
  intro flagCap uniqL uniqPtr hBuild
  set m := rawL.length
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have hfc_le : flagCap ≤ vCap := rotFlagCap_le hraw_cap
  have hu_le_m : uniqL.length ≤ m := rotDedup_length_le_length rawL
  -- Step A: `reg 12 := mem[h]`, `reg 13 := 0`
  set rA1 := Function.update st₀.regs 12 m
  set rA2 := Function.update rA1 13 0
  have ha12 : Runs w p ω (.assign 12 (.load (.reg 5))) st₀ .normal ⟨st₀.mem, rA1, st₀.pos⟩ 3 :=
    runs_assign_iff.mpr ⟨m, Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr5) hmh, rfl, rfl, rfl⟩
  have ha13 : Runs w p ω (.assign 13 (.const 0)) ⟨st₀.mem, rA1, st₀.pos⟩ .normal
      ⟨st₀.mem, rA2, st₀.pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  -- Step B: Loop 1 (max-scan computing `flagCap`)
  let inv1 : ℕ → State → Prop := fun i st =>
    st.mem = st₀.mem ∧
    st.regs 5 = h ∧ st.regs 6 = rawPtr ∧ st.regs 10 = hE ∧ st.regs 12 = m ∧
    st.regs 13 = rotFlagCap (rawL.take i) ∧ st.regs 14 = i
  have hloop1 := Triple.forRange_le (w := w) (p := p) (r := 14) (lo := .const 0) (hi := .reg 12)
    (body := .assign 15 (.load (.bin .add (.reg 6) (.reg 14))) ;;
      .cond (.bin .lt (.reg 13) (.bin .add (.reg 15) (.const 1)))
        (.assign 13 (.bin .add (.reg 15) (.const 1))) .nop)
    (P := fun st => inv1 0 { st with regs := Function.update st.regs 14 0 })
    (Inv := inv1) (fun _ => 20) 0 m (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.1)
    (fun i _ hi st ω' ⟨hmem, r5, r6, r10, r12, r13, r14⟩ => by
      set v := rawL[i]'hi
      have hv_cap : v < vCap := hraw_cap v (List.getElem_mem hi)
      have hfc_i : rotFlagCap (rawL.take i) ≤ vCap :=
        rotFlagCap_le fun x hx => hraw_cap x (List.mem_of_mem_take hx)
      have hmv : st.mem (rawPtr + i) = v := by rw [hmem]; exact hraw i hi
      set r1 := Function.update st.regs 15 v
      have hs1 : Runs w p ω' (.assign 15 (.load (.bin .add (.reg 6) (.reg 14)))) st .normal
          ⟨st.mem, r1, st.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq r6) (Expr.eval_reg_of_eq r14) (by omega)) hmv,
          rfl, rfl, rfl⟩
      have htk : rotFlagCap (rawL.take (i + 1)) = max (rotFlagCap (rawL.take i)) (v + 1) := by
        rw [List.take_succ_eq_append_getElem hi, rotFlagCap_append]
      have he13 : (Expr.reg 13).eval w ⟨st.mem, r1, st.pos⟩ = some (rotFlagCap (rawL.take i)) :=
        Expr.eval_reg_of_eq (by simp [r1, r13])
      have heV1 : (Expr.bin .add (.reg 15) (.const 1)).eval w ⟨st.mem, r1, st.pos⟩ = some (v + 1) :=
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1])) (Expr.eval_const h1w) (by omega)
      by_cases hlt : rotFlagCap (rawL.take i) < v + 1
      · have heC : (Expr.bin .lt (.reg 13) (.bin .add (.reg 15) (.const 1))).eval w
            ⟨st.mem, r1, st.pos⟩ = some 1 := by
          unfold Expr.eval; rw [he13, heV1]; simp [BinOp.eval, hlt, h1w]
        set r2 := Function.update r1 13 (v + 1)
        have hs2 : Runs w p ω' (.assign 13 (.bin .add (.reg 15) (.const 1)))
            ⟨st.mem, r1, st.pos⟩ .normal ⟨st.mem, r2, st.pos⟩ 4 :=
          runs_assign_iff.mpr ⟨v + 1, heV1, rfl, rfl, rfl⟩
        refine ⟨.normal, ⟨st.mem, r2, st.pos⟩, 5 + (5 + 4 + 1) + 1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
            runs_cond_iff.mpr ⟨1, 4, heC, by simpa using hs2, by simp [Expr.size]⟩, rfl⟩),
          ⟨⟨hmem, by simp [r2, r1, r5], by simp [r2, r1, r6], by simp [r2, r1, r10],
            by simp [r2, r1, r12], by rw [htk, Nat.max_eq_right (by omega)]; simp [r2],
            by simp⟩, by simp [r2, r1, r14]⟩, by dsimp only; omega⟩
      · have heC : (Expr.bin .lt (.reg 13) (.bin .add (.reg 15) (.const 1))).eval w
            ⟨st.mem, r1, st.pos⟩ = some 0 := by
          unfold Expr.eval; rw [he13, heV1]; simp [BinOp.eval, hlt, h0w]
        refine ⟨.normal, ⟨st.mem, r1, st.pos⟩, 5 + (5 + 1 + 1) + 1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
            runs_cond_iff.mpr ⟨0, 1, heC, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
              by simp [Expr.size]⟩, rfl⟩),
          ⟨⟨hmem, by simp [r1, r5], by simp [r1, r6], by simp [r1, r10], by simp [r1, r12],
            by rw [htk, Nat.max_eq_left (by omega)]; simp [r1, r13], by simp⟩,
            by simp [r1, r14]⟩, by dsimp only; omega⟩)
  obtain ⟨oL1, st1, cL1, hrL1, hpost1, hcL1⟩ := hloop1 ⟨st₀.mem, rA2, st₀.pos⟩ ω
    ⟨rfl, by simp [rA2, rA1, hr5], by simp [rA2, rA1, hr6], by simp [rA2, rA1, hr10],
      by simp [rA2, rA1], by simp [rA2, rotFlagCap], by simp⟩
  cases oL1 with
  | returned _ => cases hpost1
  | normal =>
  obtain ⟨hmem1, h1r5, h1r6, h1r10, h1r12, h1r13, -⟩ := hpost1
  rw [show rawL.take m = rawL from List.take_length] at h1r13
  -- Step C: `reg 14 := hE + flagCap`, `reg 15 := 0`
  set rB1 := Function.update st1.regs 14 uniqPtr
  set rB2 := Function.update rB1 15 0
  have ha14 : Runs w p ω (.assign 14 (.bin .add (.reg 10) (.reg 13))) st1 .normal
      ⟨st1.mem, rB1, st1.pos⟩ 4 :=
    runs_assign_iff.mpr ⟨uniqPtr, Expr.eval_add (Expr.eval_reg_of_eq h1r10)
      (Expr.eval_reg_of_eq h1r13) (by omega), rfl, rfl, rfl⟩
  have ha15 : Runs w p ω (.assign 15 (.const 0)) ⟨st1.mem, rB1, st1.pos⟩ .normal
      ⟨st1.mem, rB2, st1.pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  -- Step D: Loop 2 (zeroed flag-array deduplication)
  let inv2 : ℕ → State → Prop := fun i st =>
    let U := rotDedup (rawL.take i)
    st.regs 5 = h ∧ st.regs 6 = rawPtr ∧ st.regs 10 = hE ∧ st.regs 12 = m ∧
    st.regs 14 = uniqPtr ∧ st.regs 15 = U.length ∧ st.regs 16 = i ∧
    ListAt st.mem uniqPtr U ∧
    (∀ x < flagCap, st.mem (hE + x) = if x ∈ U then 1 else 0) ∧
    (∀ a, a < hE ∨ uniqPtr + U.length ≤ a → st.mem a = st₀.mem a)
  have hloop2 := Triple.forRange_le (w := w) (p := p) (r := 16) (lo := .const 0) (hi := .reg 12)
    (body := .assign 17 (.load (.bin .add (.reg 6) (.reg 16))) ;;
      .cond (.bin .eq (.load (.bin .add (.reg 10) (.reg 17))) (.const 0))
        (.store (.bin .add (.reg 10) (.reg 17)) (.const 1) ;;
         .store (.bin .add (.reg 14) (.reg 15)) (.reg 17) ;;
         .assign 15 (.bin .add (.reg 15) (.const 1)))
        .nop)
    (P := fun st => inv2 0 { st with regs := Function.update st.regs 16 0 })
    (Inv := inv2) (fun _ => 35) 0 m (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.1)
    (fun i _ hi st ω' ⟨r5, r6, r10, r12, r14, r15, r16, hLA, hfl, hfr⟩ => by
      set U := rotDedup (rawL.take i)
      set v := rawL[i]'hi
      have hv_fc : v < flagCap := rotFlagCap_gt (List.getElem_mem hi)
      have hv_cap : v < vCap := hraw_cap v (List.getElem_mem hi)
      have hU_le : U.length ≤ i := (rotDedup_length_le_length _).trans (by simp)
      have hmv : st.mem (rawPtr + i) = v := by
        rw [hfr (rawPtr + i) (Or.inl (by omega))]; exact hraw i hi
      set r1 := Function.update st.regs 17 v
      have hs1 : Runs w p ω' (.assign 17 (.load (.bin .add (.reg 6) (.reg 16)))) st .normal
          ⟨st.mem, r1, st.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq r6) (Expr.eval_reg_of_eq r16) (by omega)) hmv,
          rfl, rfl, rfl⟩
      have htk : rotDedup (rawL.take (i + 1)) = if v ∈ U then U else U ++ [v] := by
        rw [List.take_succ_eq_append_getElem hi, rotDedup_append]
      have hfl_v : st.mem (hE + v) = if v ∈ U then 1 else 0 := hfl v hv_fc
      have heAddr : (Expr.bin .add (.reg 10) (.reg 17)).eval w ⟨st.mem, r1, st.pos⟩ =
          some (hE + v) :=
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, r10]))
          (Expr.eval_reg_of_eq (by simp [r1])) (by omega)
      by_cases hvU : v ∈ U
      · have hfl1 : st.mem (hE + v) = 1 := by simpa [hvU] using hfl_v
        have heC : (Expr.bin .eq (.load (.bin .add (.reg 10) (.reg 17))) (.const 0)).eval w
            ⟨st.mem, r1, st.pos⟩ = some 0 := by
          have hl := Expr.eval_load_of_eq heAddr hfl1
          have hc := Expr.eval_const (w := w) (st := ⟨st.mem, r1, st.pos⟩) h0w
          unfold Expr.eval; rw [hl, hc]; simp [BinOp.eval, h0w]
        refine ⟨.normal, ⟨st.mem, r1, st.pos⟩, 5 + (6 + 1 + 1) + 1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
            runs_cond_iff.mpr ⟨0, 1, heC, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
              by simp [Expr.size]⟩, rfl⟩),
          ⟨⟨by simp [r1, r5], by simp [r1, r6], by simp [r1, r10], by simp [r1, r12],
            by simp [r1, r14], by simp only [htk, hvU, ↓reduceIte]; simp [r1, r15],
            by simp,
            by simp only [htk, hvU, ↓reduceIte]; exact hLA,
            by simp only [htk, hvU, ↓reduceIte]; exact hfl,
            by simp only [htk, hvU, ↓reduceIte]; exact hfr⟩, by simp [r1, r16]⟩, by dsimp only; omega⟩
      · have hfl0 : st.mem (hE + v) = 0 := by simpa [hvU] using hfl_v
        have heC : (Expr.bin .eq (.load (.bin .add (.reg 10) (.reg 17))) (.const 0)).eval w
            ⟨st.mem, r1, st.pos⟩ = some 1 := by
          have hl := Expr.eval_load_of_eq heAddr hfl0
          have hc := Expr.eval_const (w := w) (st := ⟨st.mem, r1, st.pos⟩) h0w
          unfold Expr.eval; rw [hl, hc]; simp [BinOp.eval, h1w]
        set m1 := Function.update st.mem (hE + v) 1
        set m2 := Function.update m1 (uniqPtr + U.length) v
        set r2 := Function.update r1 15 (U.length + 1)
        have hst1 : Runs w p ω' (.store (.bin .add (.reg 10) (.reg 17)) (.const 1))
            ⟨st.mem, r1, st.pos⟩ .normal ⟨m1, r1, st.pos⟩ 5 :=
          runs_store_iff.mpr ⟨hE + v, 1, heAddr, Expr.eval_const h1w, rfl, rfl, rfl⟩
        have hst2 : Runs w p ω' (.store (.bin .add (.reg 14) (.reg 15)) (.reg 17))
            ⟨m1, r1, st.pos⟩ .normal ⟨m2, r1, st.pos⟩ 5 :=
          runs_store_iff.mpr ⟨uniqPtr + U.length, v,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, r14]))
              (Expr.eval_reg_of_eq (by simp [r1, r15])) (by omega),
            Expr.eval_reg_of_eq (by simp [r1]), rfl, rfl, rfl⟩
        have hinc : Runs w p ω' (.assign 15 (.bin .add (.reg 15) (.const 1)))
            ⟨m2, r1, st.pos⟩ .normal ⟨m2, r2, st.pos⟩ 4 :=
          runs_assign_iff.mpr ⟨U.length + 1,
            Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, r15])) (Expr.eval_const h1w)
              (by omega), rfl, rfl, rfl⟩
        have hbody : Runs w p ω'
            (.store (.bin .add (.reg 10) (.reg 17)) (.const 1) ;;
             .store (.bin .add (.reg 14) (.reg 15)) (.reg 17) ;;
             .assign 15 (.bin .add (.reg 15) (.const 1)))
            ⟨st.mem, r1, st.pos⟩ .normal ⟨m2, r2, st.pos⟩ (5 + (5 + 4 + 1) + 1) :=
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst1,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst2, hinc, rfl⟩), rfl⟩)
        refine ⟨.normal, ⟨m2, r2, st.pos⟩, 5 + (6 + (5 + (5 + 4 + 1) + 1) + 1) + 1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
            runs_cond_iff.mpr ⟨1, 5 + (5 + 4 + 1) + 1, heC, by simpa using hbody,
              by simp [Expr.size]⟩, rfl⟩),
          ⟨⟨by simp [r2, r1, r5], by simp [r2, r1, r6], by simp [r2, r1, r10], by simp [r2, r1, r12],
            by simp [r2, r1, r14], by simp only [htk, hvU, ↓reduceIte]; simp [r2],
            by simp, ?_, ?_, ?_⟩, by simp [r2, r1, r16]⟩, by dsimp only; omega⟩
        · simp only [htk, hvU, ↓reduceIte]
          intro j hj
          simp only [List.length_append, List.length_singleton] at hj
          by_cases hju : j < U.length
          · rw [List.getElem_append_left hju]
            dsimp only [m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hLA j hju
          · have hjeq : j = U.length := by omega
            subst hjeq
            rw [List.getElem_append_right le_rfl]
            simp [m2]
        · simp only [htk, hvU, ↓reduceIte]
          intro x hx
          dsimp only [m2, m1]
          rw [Function.update_of_ne (by omega)]
          simp only [List.mem_append, List.mem_singleton]
          by_cases hxv : x = v
          · subst hxv; simp
          · rw [Function.update_of_ne (by omega)]
            simp only [hxv, or_false]
            exact hfl x hx
        · simp only [htk, hvU, ↓reduceIte]
          intro a ha
          simp only [List.length_append, List.length_singleton] at ha
          dsimp only [m2, m1]
          rw [Function.update_of_ne (by rcases ha with h1 | h2 <;> omega),
            Function.update_of_ne (by rcases ha with h1 | h2 <;> omega)]
          exact hfr a (by rcases ha with h1 | h2 <;> [exact Or.inl h1; exact Or.inr (by omega)])
    )
  obtain ⟨oL2, st2, cL2, hrL2, hpost2, hcL2⟩ := hloop2 ⟨st1.mem, rB2, st1.pos⟩ ω
    ⟨by simp [rB2, rB1, h1r5], by simp [rB2, rB1, h1r6], by simp [rB2, rB1, h1r10],
      by simp [rB2, rB1, h1r12], by simp [rB2, rB1], by simp [rB2, rotDedup], by simp,
      by intro j hj; simp [rotDedup] at hj,
      by intro x hx; rw [hmem1]; simpa [rotDedup] using hz (hE + x) (by omega),
      by intro a _; exact hmem1 ▸ rfl⟩
  cases oL2 with
  | returned _ => cases hpost2
  | normal =>
  obtain ⟨h2r5, -, -, -, h2r14, h2r15, -, hLA2, -, hfr2⟩ := hpost2
  rw [show rawL.take m = rawL from List.take_length] at h2r15 hLA2 hfr2
  -- Step E: `reg 16 := uniqPtr + u`
  set rF := Function.update st2.regs 16 hBuild
  have ha16 : Runs w p ω (.assign 16 (.bin .add (.reg 14) (.reg 15))) st2 .normal
      ⟨st2.mem, rF, st2.pos⟩ 4 :=
    runs_assign_iff.mpr ⟨hBuild, Expr.eval_add (Expr.eval_reg_of_eq h2r14)
      (Expr.eval_reg_of_eq h2r15) (by omega), rfl, rfl, rfl⟩
  have hrAll : Runs w p ω p4RotDedupStmt st₀ .normal ⟨st2.mem, rF, st2.pos⟩
      (3 + (2 + (cL1 + (4 + (2 + (cL2 + 4 + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha12,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha13,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrL1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha14,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha15,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, hrL2, ha16, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
        rfl⟩), rfl⟩)
  have hrc1 : rangeCost (fun _ => 20) 0 m = 20 * m := by simp [rangeCost, Nat.mul_comm]
  have hrc2 : rangeCost (fun _ => 35) 0 m = 35 * m := by simp [rangeCost, Nat.mul_comm]
  dsimp only at hcL1 hcL2
  simp only [hrc1, hrc2, Nat.sub_zero, Expr.size] at hcL1 hcL2
  refine ⟨⟨st2.mem, rF, st2.pos⟩, _, hrAll, by simp [rF, h2r5], by simp [rF, h2r14],
    by simp [rF, h2r15, uniqL], by simp [rF], hLA2,
    fun x hx => (hfr2 x (Or.inr hx)).trans (hz x (by omega)),
    fun a ha => hfr2 a (Or.inl ha), by omega⟩

end

end MinCostFlow.SparseCore.Program
