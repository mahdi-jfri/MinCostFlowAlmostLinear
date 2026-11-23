module

public import WordRAM.Logic
public import WordRAM.Tactic

/-!
# Copying groups of items

`grpCopyP`, called with `[L, nsp, GOFF, GPR, OUT, c0]`, reads the keys `u_i = L[3 i]` for
`i < nsp`, and for each key copies the items `GPR[GOFF[u_i]], …, GPR[GOFF[u_i + 1] - 1]` to the
output, two words per item: the item and the flag `0`, from entry `c0` of `OUT` on
(`grpCopyP_spec`). It returns the number of entries written so far. After a reset, the split walk
uses it to append the pairs grouped at the split nodes to the stored pairs of the child; the
keys are then the split column of the walk (stride `3`). The cost is linear in the number of keys
and of items.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The numbers of `grpCopyP`. -/
structure GCE where
  L : ℕ
  nsp : ℕ
  GOFF : ℕ
  GPR : ℕ
  OUT : ℕ
  c0 : ℕ
  mem0 : ℕ → ℕ

namespace GCE

variable (E : GCE)

/-- The key `i`. -/
def key (i : ℕ) : ℕ := E.mem0 (E.L + 3 * i)

/-- The start of the items of key `i`. -/
def lo (i : ℕ) : ℕ := E.mem0 (E.GOFF + E.key i)

/-- The end of the items of key `i`. -/
def hi (i : ℕ) : ℕ := E.mem0 (E.GOFF + E.key i + 1)

/-- The items of key `i`. -/
def blk (i : ℕ) : List ℕ := (List.range' (E.lo i) (E.hi i - E.lo i)).map fun j => E.mem0 (E.GPR + j)

/-- The items before position `j` of key `i`. -/
def pre (i j : ℕ) : List ℕ :=
  (List.range i).flatMap E.blk ++ (List.range' (E.lo i) (j - E.lo i)).map fun j => E.mem0 (E.GPR + j)

/-- All the items. -/
def seq : List ℕ := (List.range E.nsp).flatMap E.blk

/-- The precondition: the ranges are ordered, the reads lie below the first cell written, and
the output fits in a word. -/
structure Ok (w : ℕ) : Prop where
  w1 : 1 < 2 ^ w
  mono : ∀ i < E.nsp, E.lo i ≤ E.hi i
  rL : E.L + 3 * E.nsp ≤ E.OUT + 2 * E.c0
  rG : ∀ i < E.nsp, E.GOFF + E.key i + 1 < E.OUT + 2 * E.c0
  rP : ∀ i < E.nsp, E.GPR + E.hi i ≤ E.OUT + 2 * E.c0
  room : E.OUT + 2 * (E.c0 + E.seq.length) + 2 < 2 ^ w

/-- The memory `M` holds the list `W` as output, and the other cells keep their first value. -/
def Done (M : ℕ → ℕ) (W : List ℕ) : Prop :=
  (∀ t < W.length, M (E.OUT + 2 * (E.c0 + t)) = W.getD t 0 ∧ M (E.OUT + 2 * (E.c0 + t) + 1) = 0) ∧
    ∀ a, (a < E.OUT + 2 * E.c0 ∨ E.OUT + 2 * (E.c0 + W.length) ≤ a) → M a = E.mem0 a

theorem pre_lo (i : ℕ) : E.pre i (E.lo i) = (List.range i).flatMap E.blk := by simp [pre]

theorem pre_hi (i : ℕ) : E.pre i (E.hi i) = (List.range (i + 1)).flatMap E.blk := by
  simp [pre, blk, List.range_succ, List.flatMap_append]

theorem pre_succ {i j : ℕ} (hj : E.lo i ≤ j) :
    E.pre i (j + 1) = E.pre i j ++ [E.mem0 (E.GPR + j)] := by
  unfold pre
  rw [show j + 1 - E.lo i = (j - E.lo i) + 1 by omega, List.range'_concat, List.map_append,
    ← List.append_assoc]
  simp [show E.lo i + (j - E.lo i) = j by omega]

theorem flat_le {i : ℕ} (hi : i ≤ E.nsp) :
    ((List.range i).flatMap E.blk).length ≤ E.seq.length := by
  unfold seq
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi
  rw [hk, List.range_add, List.flatMap_append, List.length_append]
  omega

theorem pre_le {w : ℕ} (h : E.Ok w) {i j : ℕ} (hi : i < E.nsp) (hj : j ≤ E.hi i) :
    (E.pre i j).length ≤ E.seq.length := by
  have h1 := E.flat_le (show i + 1 ≤ E.nsp by omega)
  rw [← pre_hi] at h1
  have h2 := h.mono i hi
  simp only [pre, List.length_append, List.length_map, List.length_range'] at h1 ⊢
  omega

/-- One item written. -/
theorem Done.step {M : ℕ → ℕ} {W : List ℕ} (hd : E.Done M W) (v : ℕ) :
    E.Done (Function.update (Function.update M (E.OUT + 2 * (E.c0 + W.length)) v)
      (E.OUT + 2 * (E.c0 + W.length) + 1) 0) (W ++ [v]) := by
  refine ⟨fun t ht => ?_, fun a ha => ?_⟩
  · simp only [List.length_append, List.length_singleton] at ht
    rcases Nat.lt_or_ge t W.length with htl | htl
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        List.getD_append _ _ _ _ htl]
      exact hd.1 t htl
    · have e : t = W.length := by omega
      subst e
      rw [Function.update_of_ne (by omega), Function.update_self, Function.update_self]
      simp
  · simp only [List.length_append, List.length_singleton] at ha
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hd.2 a (by omega)

end GCE

/-- The inner body: `OUT[2c] := GPR[j]`, `OUT[2c + 1] := 0`, `c := c + 1`, with `c` in register
`5` and `j` in register `8`. -/
def grpIn : Stmt :=
  .seq (.store (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 5)))
    (.load (.bin .add (.reg 3) (.reg 8))))
  (.seq (.store (.bin .add (.bin .add (.reg 4) (.bin .mul (.const 2) (.reg 5))) (.const 1))
    (.const 0))
  (.assign 5 (.bin .add (.reg 5) (.const 1))))

/-- The start of the items of the key in register `7`. -/
def grpLo : Expr := .load (.bin .add (.reg 2) (.reg 7))

/-- The end of the items of the key in register `7`. -/
def grpHi : Expr := .load (.bin .add (.bin .add (.reg 2) (.reg 7)) (.const 1))

/-- The outer body, for key `i` in register `6`. -/
def grpOut : Stmt :=
  .seq (.assign 7 (.load (.bin .add (.reg 0) (.bin .mul (.const 3) (.reg 6)))))
    (forRange 8 grpLo grpHi grpIn)

/-- `grpCopyP` with `args = [L, nsp, GOFF, GPR, OUT, c0]`. -/
def grpCopyP : Stmt :=
  .seq (forRange 6 (.const 0) (.reg 1) grpOut) (.ret (.reg 5))

theorem grpCopyP_noRand : grpCopyP.NoRand := by
  simp [grpCopyP, grpOut, grpIn, grpLo, grpHi, forRange, forUp, Stmt.NoRand]

/-- The contract of `grpCopyP`. -/
def grpCopyC (w : ℕ) : Contract where
  pre args mem := ∃ E : GCE, args = [E.L, E.nsp, E.GOFF, E.GPR, E.OUT, E.c0] ∧ E.mem0 = mem ∧
    E.Ok w
  post args mem v mem' := ∀ E : GCE, args = [E.L, E.nsp, E.GOFF, E.GPR, E.OUT, E.c0] →
    E.mem0 = mem → v = E.c0 + E.seq.length ∧ E.Done mem' E.seq
  cost args mem := 60 * (((List.range (args.getD 1 0)).map fun i =>
      mem (args.getD 2 0 + mem (args.getD 0 0 + 3 * i) + 1) -
        mem (args.getD 2 0 + mem (args.getD 0 0 + 3 * i))).sum + args.getD 1 0) + 20

namespace GCE

/-- The registers that never change. -/
def R (E : GCE) (st : State) : Prop :=
  st.regs 0 = E.L ∧ st.regs 1 = E.nsp ∧ st.regs 2 = E.GOFF ∧ st.regs 3 = E.GPR ∧ st.regs 4 = E.OUT

theorem R.upd {E : GCE} {st : State} (h : E.R st) {r : ℕ} (hr : 5 ≤ r) (v : ℕ) :
    E.R { st with regs := Function.update st.regs r v } := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Function.update_apply] <;> rwa [ite_eq_right (by omega)]

end GCE

/-- The contract of `grpCopyP` holds. -/
theorem grpCopyP_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [grpCopyP]) :
    MeetsContract w p b (grpCopyC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨E, rfl, hm, h⟩ := hpre
  subst hm
  have hproc : p.procs[b]? = some grpCopyP := hp 0 (by simp)
  clear hp
  have hw1 := h.w1
  have room := h.room
  -- the inner loop, for key `i`
  have hinner : ∀ i < E.nsp, Triple w p
      (fun st => E.R st ∧ st.regs 6 = i ∧ st.regs 7 = E.key i ∧
        st.regs 5 = E.c0 + (E.pre i (E.lo i)).length ∧ E.Done st.mem (E.pre i (E.lo i)))
      (forRange 8 grpLo grpHi grpIn)
      (normalPost fun st => E.R st ∧ st.regs 6 = i ∧
        st.regs 5 = E.c0 + (E.pre i (E.hi i)).length ∧ E.Done st.mem (E.pre i (E.hi i)))
      (fun _ => (E.hi i - E.lo i) * (30 + grpHi.size + 8) + (grpLo.size + grpHi.size + 5)) := by
    intro i hi
    have hmo := h.mono i hi
    have hrG := h.rG i hi
    have hrP := h.rP i hi
    have := Triple.forRange_const (w := w) (p := p) (r := 8) (lo := grpLo) (hi := grpHi)
      (body := grpIn)
      (P := fun st => E.R st ∧ st.regs 6 = i ∧ st.regs 7 = E.key i ∧
        st.regs 5 = E.c0 + (E.pre i (E.lo i)).length ∧ E.Done st.mem (E.pre i (E.lo i)))
      (Inv := fun j st => E.R st ∧ st.regs 6 = i ∧ st.regs 7 = E.key i ∧ st.regs 8 = j ∧
        st.regs 5 = E.c0 + (E.pre i j).length ∧ E.Done st.mem (E.pre i j))
      30 (E.lo i) (E.hi i) hmo hw1 (fun _ => by omega)
      (fun st hP => by
        obtain ⟨hr, h6, h7, h5, hd⟩ := hP
        have hr' := hr
        obtain ⟨a0, a1, a2, a3, a4⟩ := hr
        have e : st.mem (E.GOFF + E.key i) = E.lo i := hd.2 _ (Or.inl (by omega))
        have b : st.regs 2 + st.regs 7 < 2 ^ w := by rw [a2, h7]; omega
        refine ⟨?_, hr'.upd (by omega) _, by simp [h6], by simp [h7], by simp, by simp [h5], hd⟩
        simp only [grpLo]
        eval_expr)
      (fun _ st _ _ hI => hI.2.2.2.1)
      (fun j st _ _ hI => by
        obtain ⟨⟨a0, a1, a2, a3, a4⟩, h6, h7, -, -, hd⟩ := hI
        have e : st.mem (E.GOFF + E.key i + 1) = E.hi i := hd.2 _ (Or.inl (by omega))
        have b : st.regs 2 + st.regs 7 + 1 < 2 ^ w := by rw [a2, h7]; omega
        simp only [grpHi]
        eval_expr)
      (fun j hj1 hj2 st ω hI => by
        obtain ⟨hr, h6, h7, h8, h5, hd⟩ := hI
        have hr' := hr
        obtain ⟨a0, a1, a2, a3, a4⟩ := hr
        have hle := E.pre_le h hi (show j + 1 ≤ E.hi i by omega)
        rw [E.pre_succ hj1, List.length_append, List.length_singleton] at hle
        have eG : st.mem (E.GPR + j) = E.mem0 (E.GPR + j) := hd.2 _ (Or.inl (by omega))
        have b1 : st.regs 3 + st.regs 8 < 2 ^ w := by rw [a3, h8]; omega
        have b2 : st.regs 4 + 2 * st.regs 5 + 1 < 2 ^ w := by rw [a4, h5]; omega
        have b3 : st.regs 5 + 1 < 2 ^ w := by rw [h5]; omega
        refine runs_start_le ?_
        dsimp only [grpIn]
        wram_run
        · dsimp only [normalPost]
          refine ⟨⟨by simp [GCE.R, a0, a1, a2, a3, a4], by simp [h6], by simp [h7], by simp,
            by simp [E.pre_succ hj1, Nat.add_assoc], ?_⟩, by simp [h8]⟩
          rw [E.pre_succ hj1, ← eG]
          exact GCE.Done.step E hd _
        · wram_cost)
    refine this.strengthen_post ?_
    intro o st hq
    cases o with
    | returned v => exact hq.elim
    | normal => exact ⟨hq.1, hq.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2⟩
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 6) (lo := .const 0) (hi := .reg 1)
    (body := grpOut)
    (P := fun st => st = startState [E.L, E.nsp, E.GOFF, E.GPR, E.OUT, E.c0] E.mem0 pos)
    (Inv := fun i st => E.R st ∧ st.regs 6 = i ∧
      st.regs 5 = E.c0 + ((List.range i).flatMap E.blk).length ∧
      E.Done st.mem ((List.range i).flatMap E.blk))
    (fun i => (E.hi i - E.lo i) * (30 + grpHi.size + 8) + (grpLo.size + grpHi.size + 5) + 9)
    0 E.nsp (Nat.zero_le _) hw1 (fun _ => by have := h.rL; omega)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, GCE.R.upd ⟨rfl, rfl, rfl, rfl, rfl⟩ (by omega) _, by simp,
        by simp [startState],
        fun t ht => by simp at ht, fun a _ => rfl⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun i _ hi st ω hI => by
      obtain ⟨hr, h6, h5, hd⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4⟩ := hr
      have hrL := h.rL
      have e : st.mem (E.L + 3 * i) = E.key i := hd.2 _ (Or.inl (by omega))
      have b : st.regs 0 + 3 * st.regs 6 < 2 ^ w := by rw [a0, h6]; omega
      have b' : 3 * st.regs 6 < 2 ^ w := by rw [h6]; omega
      refine runs_start_le ?_
      dsimp only [grpOut]
      refine runs_seq_assign_le (by eval_expr) ?_
      refine runs_triple_le (hinner i hi) ⟨hr'.upd (by omega) _, by simp [h6], ?_, ?_, ?_⟩
        (fun o st' hq => ?_) ?_
      · simp only [Function.update_apply]; simp [e]
      · simp [h5, E.pre_lo]
      · rw [E.pre_lo]; exact hd
      · cases o with
        | returned v => exact hq.elim
        | normal =>
          obtain ⟨hr2, h62, h52, hd2⟩ := hq
          rw [E.pre_hi] at h52 hd2
          exact ⟨⟨hr2.upd (by omega) _, by simp, by simp [h52], hd2⟩, h62⟩
      · simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin]
        omega)
  refine ⟨grpCopyP, hproc, ?_⟩
  dsimp only [grpCopyP]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop rfl (fun st hI => ?_)
  obtain ⟨-, -, h5, hd⟩ := hI
  refine runs_ret_le (by eval_expr) ?_ ?_
  · intro E' he hm'
    have e : E' = E := by
      cases E; cases E'; simp only [List.cons.injEq] at he; simp_all
    subst e
    exact ⟨rfl, hd⟩
  · have hsum : ∀ n, rangeCost (fun i => (E.hi i - E.lo i) * (30 + grpHi.size + 8) +
        (grpLo.size + grpHi.size + 5) + 9) 0 n ≤
        60 * ((List.range n).map fun i => E.hi i - E.lo i).sum + 40 * n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [rangeCost_zero_eq_range] at ih ⊢
        simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, grpHi, grpLo, Expr.size_const,
          Expr.size_reg, Expr.size_load, Expr.size_bin] at ih ⊢
        nlinarith
    have := hsum E.nsp
    simp only [grpCopyC, List.getD_cons_zero, List.getD_cons_succ, Expr.size_const,
      Expr.size_reg]
    change _ ≤ 60 * ((List.range E.nsp).map fun i => E.mem0 (E.GOFF + E.mem0 (E.L + 3 * i) + 1) -
      E.mem0 (E.GOFF + E.mem0 (E.L + 3 * i))).sum + 40 * E.nsp at this
    omega

end MinCostFlow.LowStretch
