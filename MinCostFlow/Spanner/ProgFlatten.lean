module

public import MinCostFlow.Spanner.ProgSetup
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.LSF.Program.Utils

@[expose] public section

/-!
# Listing the Edges of an Embedding

The first step of the output part of `Sparsify` is the list of kept edges. In the model it is
`((List.range W.m).flatMap fun eW => (embWJ eW).edges).dedup`. This file gives the program for
the list before `dedup`: it walks over the `m` walks of an embedding stored by `EmbAt`, and copies
the edge list of each walk to the end of an output buffer with `memCopy`. It returns the length
of the output. The result is `flatEdges_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited LSF.Program

/-- The edges of the first `k` walks of `emb`, one walk after the other. -/
def flatEdges (emb : ℕ → Walk) (k : ℕ) : List ℕ :=
  (List.range k).flatMap fun e => (emb e).edges

lemma flatEdges_succ (emb : ℕ → Walk) (k : ℕ) :
    flatEdges emb (k + 1) = flatEdges emb k ++ (emb k).edges := by
  simp [flatEdges, List.range_succ, List.flatMap_append]

lemma flatEdges_congr {e₁ e₂ : ℕ → Walk} :
    ∀ {k : ℕ}, (∀ j < k, e₁ j = e₂ j) → flatEdges e₁ k = flatEdges e₂ k
  | 0, _ => rfl
  | k + 1, h => by
    rw [flatEdges_succ, flatEdges_succ, flatEdges_congr (fun j hj => h j (by omega)),
      h k (by omega)]

lemma flatEdges_length_le {emb : ℕ → Walk} {L : ℕ} (hL : ∀ e, (emb e).edges.length ≤ L) :
    ∀ k, (flatEdges emb k).length ≤ k * L
  | 0 => by simp [flatEdges]
  | k + 1 => by
    rw [flatEdges_succ, List.length_append, Nat.succ_mul]
    have := flatEdges_length_le hL k
    have := hL k
    omega

/-- Procedure body, at `args = [E, m, dst, L]`; `fc` is the address of `memCopyStmt`. The
argument `L` is a bound on the edge counts of the walks; the body does not read it. -/
def flatEdgesBody (fc : ℕ) : Stmt :=
  .assign 9 (.const 0) ;;
  forRange 4 (.const 0) (.reg 1) (
    .assign 5 (.load (.bin .add (.reg 0) (.reg 4))) ;;
    .assign 6 (.load (.reg 5)) ;;
    .assign 7 (.load (.bin .add (.bin .add (.reg 5) (.const 1)) (.reg 6))) ;;
    .call 8 fc [.bin .add (.reg 2) (.reg 9), .bin .add (.bin .add (.reg 5) (.const 2)) (.reg 6),
      .reg 7] ;;
    .assign 9 (.bin .add (.reg 9) (.reg 7))) ;;
  .ret (.reg 9)

/-- The walks of `emb` are stored by `EmbAt` at `E`, all below `dst`, each with at most `L`
edges, and `dst + m L` fits in a word. -/
def FlatEdgesPre (mem : ℕ → ℕ) (E m dst L : ℕ) (emb : ℕ → Walk) (w : ℕ) : Prop :=
  EmbAt mem E m emb ∧ EmbBounded mem E m emb dst ∧ (∀ e, (emb e).edges.length ≤ L) ∧
    dst + m * L < 2 ^ w ∧ 1 < 2 ^ w

/-- Contract of `flatEdgesBody`. -/
def flatEdgesContract (w : ℕ) : Contract where
  pre args mem := ∃ E m dst L emb, args = [E, m, dst, L] ∧ FlatEdgesPre mem E m dst L emb w
  post args mem v mem' := ∀ E m dst L emb, args = [E, m, dst, L] →
    FlatEdgesPre mem E m dst L emb w →
    v = (flatEdges emb m).length ∧ ListAt mem' dst (flatEdges emb m) ∧
      ∀ x, x < dst ∨ dst + (flatEdges emb m).length ≤ x → mem' x = mem x
  cost args _ := args.getD 1 0 * (20 * args.getD 3 0 + 120) + 30

/-- Loop invariant: after `k` walks, the output holds their edges, and the memory outside the
output is unchanged. -/
def FlatInv (mem : ℕ → ℕ) (E m dst : ℕ) (emb : ℕ → Walk) (k : ℕ) (st : State) : Prop :=
  st.regs 0 = E ∧ st.regs 1 = m ∧ st.regs 2 = dst ∧ st.regs 4 = k ∧
    st.regs 9 = (flatEdges emb k).length ∧ k ≤ m ∧ ListAt st.mem dst (flatEdges emb k) ∧
    ∀ x, x < dst ∨ dst + (flatEdges emb k).length ≤ x → st.mem x = mem x

lemma flatEdges_step {w : ℕ} {p : Program} {fc : ℕ} (hfc : MeetsContract w p fc (memCopyContract w))
    {mem : ℕ → ℕ} {E m dst L : ℕ} {emb : ℕ → Walk} (hpre : FlatEdgesPre mem E m dst L emb w)
    (k : ℕ) (hk : k < m) :
    Triple w p (FlatInv mem E m dst emb k)
      (.assign 5 (.load (.bin .add (.reg 0) (.reg 4))) ;;
        .assign 6 (.load (.reg 5)) ;;
        .assign 7 (.load (.bin .add (.bin .add (.reg 5) (.const 1)) (.reg 6))) ;;
        .call 8 fc [.bin .add (.reg 2) (.reg 9),
          .bin .add (.bin .add (.reg 5) (.const 2)) (.reg 6), .reg 7] ;;
        .assign 9 (.bin .add (.reg 9) (.reg 7)))
      (normalPost fun st₁ =>
        FlatInv mem E m dst emb (k + 1) { st₁ with regs := Function.update st₁.regs 4 (k + 1) } ∧
          st₁.regs 4 = k)
      (fun _ => 20 * L + 100) := by
  obtain ⟨hEmb, hBnd, hL, hdw, hw1⟩ := hpre
  intro st ω hI
  obtain ⟨r0, r1, r2, r4, r9, hkm, hlist, hout⟩ := hI
  have hflat := flatEdges_length_le hL k
  have hkL : k * L + L ≤ m * L := by
    have := Nat.mul_le_mul_right L (show k + 1 ≤ m by omega); rw [Nat.succ_mul] at this; exact this
  set cnt := (flatEdges emb k).length with hcnt
  -- The walk of edge `k`.
  have hEk : E + k < dst := by have := hBnd.1; omega
  set P := mem (E + k) with hP
  have hW := walkAt_iff.mp (hEmb k hk)
  obtain ⟨hnv, -, hne, hedges⟩ := hW
  have hPb := hBnd.2 k hk
  rw [walk_encode_length] at hPb
  set nv := (emb k).verts.length with hnvdef
  set ne := (emb k).edges.length with hnedef
  have hneL : ne ≤ L := hL k
  have hst : ∀ x, x < dst → st.mem x = mem x := fun x hx => hout x (Or.inl hx)
  have hwd : dst < 2 ^ w := by omega
  -- Evaluations.
  have e5 : (Expr.load (.bin .add (.reg 0) (.reg 4))).eval w st = some P :=
    ev_load (ev_add (ev_reg r0 (by omega)) (ev_reg r4 (by omega)) (by omega)) (hst _ hEk) (by omega)
  let s1 : State := { st with regs := Function.update st.regs 5 P }
  have e6 : (Expr.load (.reg 5)).eval w s1 = some nv :=
    ev_load (ev_reg (v := P) (by simp [s1]) (by omega)) (by simp only [s1]; rw [hst P (by omega)]; exact hnv)
      (by omega)
  let s2 : State := { s1 with regs := Function.update s1.regs 6 nv }
  have e7 : (Expr.load (.bin .add (.bin .add (.reg 5) (.const 1)) (.reg 6))).eval w s2 = some ne :=
    ev_load (ev_add (ev_add (ev_reg (v := P) (by simp [s2, s1]) (by omega)) (ev_const hw1) (by omega))
      (ev_reg (v := nv) (by simp [s2]) (by omega)) (by omega))
      (by simp only [s2, s1]; rw [hst (P + 1 + nv) (by omega)]; exact hne) (by omega)
  let s3 : State := { s2 with regs := Function.update s2.regs 7 ne }
  have hargs : evalArgs w s3 [.bin .add (.reg 2) (.reg 9),
      .bin .add (.bin .add (.reg 5) (.const 2)) (.reg 6), .reg 7] =
      some [dst + cnt, P + 2 + nv, ne] := by
    have a1 : (Expr.bin .add (.reg 2) (.reg 9)).eval w s3 = some (dst + cnt) :=
      ev_add (ev_reg (v := dst) (by simp [s3, s2, s1, r2]) hwd)
        (ev_reg (v := cnt) (by simp [s3, s2, s1, r9]) (by omega))
        (by omega)
    have a2 : (Expr.bin .add (.bin .add (.reg 5) (.const 2)) (.reg 6)).eval w s3 =
        some (P + 2 + nv) :=
      ev_add (ev_add (ev_reg (v := P) (by simp [s3, s2, s1]) (by omega)) (ev_const (c := 2) (by omega))
        (by omega)) (ev_reg (v := nv) (by simp [s3, s2]) (by omega)) (by omega)
    have a3 : (Expr.reg 7).eval w s3 = some ne := ev_reg (v := ne) (by simp [s3]) (by omega)
    simp [evalArgs, a1, a2, a3]
  refine runs_start_le ?_
  refine runs_seq_assign_le e5 ?_
  refine runs_seq_assign_le e6 ?_
  refine runs_seq_assign_le e7 ?_
  refine runs_seq_call_le hfc hargs ?_ ⟨dst + cnt, P + 2 + nv, ne, rfl, by omega, by omega,
    Or.inr (by omega)⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  intro v mem' pos' hpost
  obtain ⟨d', s', l', hargs', -, hcopy, hother⟩ := hpost
  simp only [List.cons.injEq, and_true] at hargs'
  obtain ⟨hd', hs', hl'⟩ := hargs'
  subst hd' hs' hl'
  have e9 : (Expr.bin .add (.reg 9) (.reg 7)).eval w
      { mem := mem', regs := Function.update s3.regs 8 v, pos := pos' } = some (cnt + ne) :=
    ev_add (ev_reg (v := cnt) (by simp [s3, s2, s1, r9]) (by omega))
      (ev_reg (v := ne) (by simp [s3]) (by omega))
      (by omega)
  refine runs_assign_le e9 ⟨⟨?_, ?_, ?_, by simp, ?_, by omega, ?_, ?_⟩, by simp [s3, s2, s1, r4]⟩
    (by simp only [Expr.size, argsSize, memCopyContract, List.getD_cons_succ,
      List.getD_cons_zero]; omega)
  · simp [s3, s2, s1, r0]
  · simp [s3, s2, s1, r1]
  · simp [s3, s2, s1, r2]
  · simp [flatEdges_succ, cnt, ne]
  · -- The output now holds the edges of walk `k` after the earlier ones.
    dsimp only
    rw [flatEdges_succ, listAt_append]
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [hother _ (Or.inl (by omega))]; exact hlist i hi
    · rw [← hcnt, hcopy i hi, hst (P + 2 + nv + i) (by omega)]
      exact hedges i hi
  · intro x hx
    dsimp only
    rw [flatEdges_succ, List.length_append] at hx
    rw [hother x (by omega)]
    exact hout x (by omega)

/-- `flatEdgesBody fc` at `f` meets `flatEdgesContract`, given that `fc` holds `memCopyStmt`.
The cost is `m (20 L + 120) + 30`. -/
theorem flatEdges_meetsContract {w : ℕ} {p : Program} {f fc : ℕ}
    (hproc : p.procs[f]? = some (flatEdgesBody fc))
    (hfc : MeetsContract w p fc (memCopyContract w)) :
    MeetsContract w p f (flatEdgesContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨E, m, dst, L, emb, rfl, hP⟩ := hpre
  have hP' := hP
  obtain ⟨hEmb, hBnd, hL, hdw, hw1⟩ := hP'
  have hmw : m < 2 ^ w := hwords m (by simp)
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 4) (lo := .const 0) (hi := .reg 1)
    (P := fun st => st.regs 0 = E ∧ st.regs 1 = m ∧ st.regs 2 = dst ∧ st.regs 9 = 0 ∧ st.mem = mem)
    (Inv := FlatInv mem E m dst emb) (20 * L + 100) 0 m (Nat.zero_le _) hw1 (fun _ => hmw)
    (fun st ⟨r0, r1, r2, r9, hm⟩ => ⟨ev_const (by omega),
      ⟨by simp [r0], by simp [r1], by simp [r2], by simp, by simp [r9, flatEdges],
        Nat.zero_le _, by simp [flatEdges, listAt_nil], fun x _ => by simp [hm]⟩⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ _ _ _ h => ev_reg h.2.1 hmw)
    (fun k _ hk => flatEdges_step hfc hP k hk)
  refine runs_start_le ?_
  refine runs_seq_assign_le (ev_const (c := 0) (by omega)) ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState],
    by simp [startState], by simp, rfl⟩ ?_
  intro st₁ hI
  obtain ⟨-, -, -, -, r9, -, hlist, hout⟩ := hI
  refine runs_ret_le (v := (flatEdges emb m).length) (ev_reg r9 (by
    have := flatEdges_length_le hL m; omega)) (fun E' m' dst' L' emb' h1 h2 => ?_) ?_
  · simp only [List.cons.injEq, and_true] at h1
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h1
    have hE : flatEdges emb m = flatEdges emb' m :=
      flatEdges_congr fun j hj => walkAt_unique (hEmb j hj) (h2.1 j hj)
    rw [← hE]
    exact ⟨rfl, hlist, hout⟩
  · simp only [Expr.size, flatEdgesContract, List.getD_cons_succ, List.getD_cons_zero,
      Nat.sub_zero]
    nlinarith [Nat.mul_le_mul_left m (show 20 * L + 100 + 1 + 8 ≤ 20 * L + 120 by omega)]

end MinCostFlow.Spanner
