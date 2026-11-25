module

public import WordRAM.Module
public import WordRAM.CopyWords
public import MinCostFlow.Scaling.SolverContract
public import MinCostFlow.Scaling.CompressionProgram
public import MinCostFlow.Final.ScratchSolve
public import MinCostFlow.Final.ForestConcretePrograms
import WordRAM.Tactic
import WordRAM.Entry
import Mathlib.Tactic.Ring

/-!
# Host-width bounded circulation solver adapter (`narrowSolverAdapter`)

Bridges `DyadicWithVConcretePrograms` (`MinCostFlow/Final/ForestConcretePrograms.lean`), whose
proved solver `P.solver` meets `compressedSolverContract` at a call-dependent guest word width
`wordSize (scratchWordMultiplier 1 P.scratchDegree) J.solverWords`, to the host-width
`solverContract w (narrowSolverTime P) (narrowSolverSpace P.scratchDegree)` expected by the
narrow-word programs (`bitScale` and `stage1Circ`).

On arguments `[a, h]`, `narrowSolverAdapterBody`:
1. compresses isolated vertices via `compressionModule` (`Scaling/CompressionProgram.lean`),
   writing `J.compress.solverWords` at `h` and obtaining `h1 = h + J.solverWords.length + 2 + J.n`;
2. runs `scratchSolveModule P.solver 0 _ 1 P.scratchDegree` (`Final/ScratchSolve.lean`) on `[h, h1]`,
   which handles both `J.m = 0` and `J.m > 0` at `guestWidth = wordSize mult J.compress.solverWords`
   and writes an optimal flow of `J.compress` (hence of `J`) at `h1`;
3. copies the `J.m` flow words from `h1` back to `h` via `copyWords` (`WordRAM/CopyWords.lean`,
   reusing the copy already inside `compressionModule`) and returns `h2 = h1 + 1 + 2 ^ guestWidth`.
-/

@[expose] public section

open WordRAM MinCostFlow.Scaling MinCostFlow.Scaling.Machine MinCostFlow.Final
  MinCostFlow.IPM.Machine

namespace MinCostFlow.NarrowTop

/-! ### Polynomial space and monotone time bounds -/

/-- Host-width workspace budget for the compressed-relocated solver adapter: covers vertex
compression (`J.n + 5 * J.m + 4`), the guest-block upper bound `2 ^ (guestWidth + 1) + 2`,
and alignment slack. Polynomial in `n + m + 2`. -/
def narrowSolverSpace (d n m : ℕ) : ℕ :=
  n + 5 * m + 10 + 2 * (m + 2) ^ (42 * scratchWordMultiplier 1 d)

/-- Host-width time bound for the compressed-relocated solver adapter, in the form
`A * linkedForestSolverTime P.runtimeResources (2 * m) m + B * (m + 1)`. -/
noncomputable def narrowSolverTime (P : DyadicWithVConcretePrograms) (_n m : ℕ) : ℕ :=
  (P.solver.regBound + 6) * linkedForestSolverTime P.runtimeResources (2 * m) m +
    (3400 * scratchWordMultiplier 1 P.scratchDegree + P.solver.regBound + 6000) * (m + 1)

theorem narrowSolverSpace_mono (d : ℕ) {n n' m m' : ℕ} (hn : n ≤ n') (hm : m ≤ m') :
    narrowSolverSpace d n m ≤ narrowSolverSpace d n' m' := by
  unfold narrowSolverSpace
  have hpow : (m + 2) ^ (42 * scratchWordMultiplier 1 d) ≤
      (m' + 2) ^ (42 * scratchWordMultiplier 1 d) :=
    Nat.pow_le_pow_left (by omega) _
  omega

theorem narrowSolverSpace_poly (d n m : ℕ) :
    narrowSolverSpace d n m ≤ 8 * (n + m + 2) ^ (42 * scratchWordMultiplier 1 d) := by
  unfold narrowSolverSpace
  set e := 42 * scratchWordMultiplier 1 d
  have hmult : 3 ≤ scratchWordMultiplier 1 d := by
    unfold scratchWordMultiplier
    have h2 : 2 ≤ max 2 (Nat.clog 2 1 + d) := le_max_left _ _
    omega
  have he : 4 ≤ e := by dsimp only [e]; omega
  set B := n + m + 2
  have hB2 : 2 ≤ B := by dsimp only [B]; omega
  have hB1 : 1 ≤ B := by omega
  have hpow_ge : B ^ 4 ≤ B ^ e := Nat.pow_le_pow_right hB1 he
  have hB4 : n + 5 * m + 10 ≤ 6 * B ^ e := by
    have hlin : n + 5 * m + 10 ≤ 5 * B := by dsimp only [B]; omega
    have hB_le : B ≤ B ^ 4 := by
      have : B ^ 1 ≤ B ^ 4 := Nat.pow_le_pow_right hB1 (by decide)
      simpa only [pow_one] using this
    have hBe : B ≤ B ^ e := hB_le.trans hpow_ge
    omega
  have hm_pow : (m + 2) ^ e ≤ B ^ e := Nat.pow_le_pow_left (by dsimp only [B]; omega) e
  omega

theorem narrowSolverTime_mono (P : DyadicWithVConcretePrograms) :
    SolverTimeMonotone (narrowSolverTime P) := by
  intro n n' m m' _ hm
  unfold narrowSolverTime
  have h1 := linkedForestSolverTime_mono P.runtimeResources (2 * m) (2 * m') m m' (by omega) hm
  have h2 := Nat.mul_le_mul_left (P.solver.regBound + 6) h1
  have h3 := Nat.mul_le_mul_left
    (3400 * scratchWordMultiplier 1 P.scratchDegree + P.solver.regBound + 6000)
    (show m + 1 ≤ m' + 1 by omega)
  exact Nat.add_le_add h2 h3

/-! ### Adapter procedure and module -/

/-- Host-width solver adapter entry: compresses `[reg 0, reg 1]` via `comp`, solves the
compressed circulation via `solve`, copies the `m` flow words back to `reg 1` via `copy`,
and returns the updated heap pointer. -/
def narrowSolverAdapterBody (comp solve copy : ℕ) : Stmt :=
  .assign 2 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .call 3 comp [.reg 0, .reg 1] ;;
  .call 4 solve [.reg 1, .reg 3] ;;
  .call 5 copy [.reg 3, .reg 1, .reg 2] ;;
  .ret (.reg 4)

/-- Contiguous procedure block for the host-width solver adapter placed at index `b`:
- `b`: `narrowSolverAdapterBody (b + 1) (b + 7) (b + 5)`
- `b + 1 .. b + 6`: `compressionModule (b + 1)` (with `copyWords` at `b + 5`)
- `b + 7 ..`: `scratchSolveModule Q f (b + 7) 1 d` -/
def narrowSolverAdapterModule (Q : Program) (f b d : ℕ) : List Stmt :=
  narrowSolverAdapterBody (b + 1) (b + 7) (b + 5) ::
    (compressionModule (b + 1) ++ scratchSolveModule Q f (b + 7) 1 d)

theorem narrowSolverAdapterModule_noRand (Q : Program) (f b d : ℕ) (hdet : Q.IsDeterministic) :
    ∀ body ∈ narrowSolverAdapterModule Q f b d, body.NoRand := by
  intro body hbody
  rcases List.mem_cons.mp hbody with rfl | hbody
  · simp only [narrowSolverAdapterBody, Stmt.NoRand, and_self]
  · rcases List.mem_append.mp hbody with hbody | hbody
    · exact compressionModule_noRand _ body hbody
    · exact scratchSolveModule_noRand Q f _ 1 d hdet body hbody

/-- Polymorphic `WordRAM.Module` wrapper for `narrowSolverAdapterModule Q f b d`, assigning names
`mkName 0, mkName 1, …` so `mkName 0` is the adapter entry at index `b`. -/
def narrowSolverAdapterMod {ι : Type} (mkName : ℕ → ι) (Q : Program) (f b d : ℕ) : Module ι :=
  ⟨(narrowSolverAdapterModule Q f b d).zipIdx.map fun p => (mkName p.2, fun _ => p.1)⟩

theorem narrowSolverAdapterMod_bodies {ι : Type} (mkName : ℕ → ι) (Q : Program) (f b d : ℕ)
    (idx : ι → ℕ) :
    (narrowSolverAdapterMod mkName Q f b d).bodies idx = narrowSolverAdapterModule Q f b d := by
  unfold narrowSolverAdapterMod Module.bodies
  rw [List.map_map]
  simp only [Function.comp_def]
  have h : ∀ (l : List Stmt) (k : ℕ), (l.zipIdx k).map Prod.fst = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons x xs ih => intro k; simp [List.zipIdx_cons, ih]
  exact h _ 0

theorem narrowSolverAdapterMod_names {ι : Type} (mkName : ℕ → ι) (Q : Program) (f b d : ℕ) :
    (narrowSolverAdapterMod mkName Q f b d).names =
      (List.range (narrowSolverAdapterModule Q f b d).length).map mkName := by
  unfold narrowSolverAdapterMod Module.names
  rw [List.map_map]
  simp only [Function.comp_def]
  have h : ∀ (l : List Stmt) (k : ℕ),
      (l.zipIdx k).map (fun p => mkName p.2) = (List.range' k l.length).map mkName := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons x xs ih => intro k; simp [List.zipIdx_cons, List.range'_succ, ih]
  rw [h _ 0, List.range_eq_range']

theorem narrowSolverAdapterMod_noRand {ι : Type} (mkName : ℕ → ι) (Q : Program) (f b d : ℕ)
    (hdet : Q.IsDeterministic) :
    (narrowSolverAdapterMod mkName Q f b d).NoRand := by
  intro q hq idx
  unfold narrowSolverAdapterMod at hq
  obtain ⟨⟨body, i⟩, hmem, rfl⟩ := List.mem_map.mp hq
  have hmem' : body ∈ narrowSolverAdapterModule Q f b d := by
    have ⟨_, _, hget⟩ := List.mem_zipIdx hmem
    exact List.mem_of_getElem hget.symm
  exact narrowSolverAdapterModule_noRand Q f b d hdet body hmem'

/-! ### Circulation injectivity from `solverWords` -/

private theorem flatMap_solverEdgeWords_getElem? (J : Circulation) (es : List (Fin J.m))
    (i r : ℕ) (hr : r < 5) :
    (es.flatMap J.solverEdgeWords)[5 * i + r]? =
      (es[i]?).bind fun e => (J.solverEdgeWords e)[r]? := by
  induction es generalizing i with
  | nil => simp
  | cons a es ih =>
    simp only [List.flatMap_cons]
    have hlen : (J.solverEdgeWords a).length = 5 := rfl
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, List.getElem?_cons_zero, Option.bind_some]
      rw [List.getElem?_append_left (by omega)]
    | succ i =>
      rw [List.getElem?_append_right (by omega)]
      simp only [List.getElem?_cons_succ]
      rw [show 5 * (i + 1) + r - (J.solverEdgeWords a).length = 5 * i + r by omega]
      exact ih i

private theorem solverWords_edge_getElem? (J : Circulation) (e : Fin J.m) (r : ℕ) (hr : r < 5) :
    J.solverWords[2 + 5 * e.val + r]? = (J.solverEdgeWords e)[r]? := by
  unfold Circulation.solverWords
  have h1 : 2 + 5 * e.val + r = (5 * e.val + r) + 2 := by omega
  rw [h1]
  simp only [List.getElem?_cons_succ]
  rw [flatMap_solverEdgeWords_getElem? J (List.finRange J.m) e.val r hr]
  have hfr : (List.finRange J.m)[e.val]? = some e := by
    rw [List.getElem?_eq_getElem (by simp [e.isLt])]
    simp
  rw [hfr, Option.bind_some]

private theorem circulation_eq_of_solverWords_eq {J K : Circulation}
    (h : J.solverWords = K.solverWords) : J = K := by
  have hn : J.n = K.n := by
    have h0 := congrArg (fun l : List ℕ => l[0]?) h
    simpa only [Circulation.solverWords, List.getElem?_cons_zero, Option.some.injEq] using h0
  have hm : J.m = K.m := by
    have h1 := congrArg (fun l : List ℕ => l[1]?) h
    simpa only [Circulation.solverWords, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] using h1
  rcases J with ⟨n1, m1, t1, h1, cap1, cost1⟩
  rcases K with ⟨n2, m2, t2, h2, cap2, cost2⟩
  dsimp only at hn hm
  subst hn; subst hm
  let J1 : Circulation := ⟨n1, m1, t1, h1, cap1, cost1⟩
  let J2 : Circulation := ⟨n1, m1, t2, h2, cap2, cost2⟩
  have hcell : ∀ (e : Fin m1) (r : ℕ) (hr : r < 5),
      (J1.solverEdgeWords e)[r]? = (J2.solverEdgeWords e)[r]? := by
    intro e r hr
    rw [← solverWords_edge_getElem? J1 e r hr, ← solverWords_edge_getElem? J2 e r hr]
    exact congrArg (fun l : List ℕ => l[2 + 5 * e.val + r]?) h
  have ht : t1 = t2 := by
    funext e
    have h0 := hcell e 0 (by decide)
    simp only [Circulation.solverEdgeWords, J1, J2, List.getElem?_cons_zero,
      Option.some.injEq] at h0
    exact Fin.ext h0
  have hh : h1 = h2 := by
    funext e
    have h0 := hcell e 1 (by decide)
    simp only [Circulation.solverEdgeWords, J1, J2, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] at h0
    exact Fin.ext h0
  have hcap : cap1 = cap2 := by
    funext e
    have h0 := hcell e 2 (by decide)
    simp only [Circulation.solverEdgeWords, J1, J2, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] at h0
    exact h0
  have hcost : cost1 = cost2 := by
    funext e
    have h3 := hcell e 3 (by decide)
    have h4 := hcell e 4 (by decide)
    simp only [Circulation.solverEdgeWords, J1, J2, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] at h3 h4
    by_cases hc1 : cost1 e < 0 <;> by_cases hc2 : cost2 e < 0 <;>
      simp only [hc1, hc2, ↓reduceIte] at h3 <;> omega
  subst ht; subst hh; subst hcap; subst hcost
  rfl

/-! ### Guest-width polynomial bounds for compressed circulations -/

private theorem foldr_max_le_of_forall {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) :
    l.foldr max 0 ≤ M := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons]
    exact max_le (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem x hy))

private theorem compressed_solverWords_foldr_le (J : Circulation)
    (hn : J.n ≤ 2 * J.m) (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) :
    J.solverWords.foldr max 0 ≤ (J.m + 2) ^ 40 := by
  apply foldr_max_le_of_forall
  intro x hx
  have hm_ge2 : 2 ≤ J.m + 2 := by omega
  have h2m_le : 2 * J.m ≤ (J.m + 2) ^ 40 := by
    have hsq : 2 * J.m ≤ (J.m + 2) ^ 2 := by nlinarith
    exact hsq.trans (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 40))
  have hm10 : J.m ^ 10 ≤ (J.m + 2) ^ 40 := by
    calc J.m ^ 10 ≤ (J.m + 2) ^ 10 := Nat.pow_le_pow_left (by omega) 10
      _ ≤ (J.m + 2) ^ 40 := Nat.pow_le_pow_right (by omega) (by decide : 10 ≤ 40)
  have hm40 : J.m ^ 40 ≤ (J.m + 2) ^ 40 := Nat.pow_le_pow_left (by omega) 40
  have h1 : 1 ≤ (J.m + 2) ^ 40 := Nat.one_le_pow _ _ (by omega)
  unfold Circulation.solverWords at hx
  simp only [List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and] at hx
  rcases hx with rfl | rfl | ⟨e, he⟩
  · omega
  · omega
  · unfold Circulation.solverEdgeWords at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · have := (J.tail e).isLt; omega
    · have := (J.head e).isLt; omega
    · exact (hu e).2.trans hm40
    · split_ifs <;> omega
    · exact (hc e).trans hm10

private theorem compressed_guestWidth_bounds (J : Circulation) (mult : ℕ)
    (hn : J.n ≤ 2 * J.m) (hc : J.CostsBounded (J.m ^ 10))
    (hu : ∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ J.m ^ 40) :
    2 ^ wordSize mult J.solverWords ≤ (J.m + 2) ^ (42 * mult) ∧
    wordSize mult J.solverWords ≤ 84 * mult * (J.m + 1) := by
  set B := J.solverWords.length + J.solverWords.foldr max 0 + 2
  have hlen : J.solverWords.length = 2 + 5 * J.m := J.solverWords_length
  have hmax := compressed_solverWords_foldr_le J hn hc hu
  have hlen_le : 5 * J.m + 4 ≤ (J.m + 2) ^ 40 := by
    have hcube : (J.m + 2) ^ 3 = J.m ^ 3 + 6 * J.m ^ 2 + 12 * J.m + 8 := by ring
    have hsq : 5 * J.m + 4 ≤ (J.m + 2) ^ 3 := by omega
    exact hsq.trans (Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 40))
  have hB_le : B ≤ 2 * (J.m + 2) ^ 40 := by dsimp only [B]; omega
  have hB_pos : 0 < B := by dsimp only [B]; omega
  have hpow1 : 2 ^ (Nat.log 2 B + 1) ≤ (J.m + 2) ^ 42 := by
    have hlog : 2 ^ Nat.log 2 B ≤ B := Nat.pow_log_le_self 2 (by omega)
    have h2 : 2 ^ (Nat.log 2 B + 1) = 2 * 2 ^ Nat.log 2 B := by rw [Nat.pow_succ, mul_comm]
    have h4 : 4 ≤ (J.m + 2) ^ 2 := by nlinarith
    calc 2 ^ (Nat.log 2 B + 1) = 2 * 2 ^ Nat.log 2 B := h2
      _ ≤ 2 * B := Nat.mul_le_mul_left 2 hlog
      _ ≤ 4 * (J.m + 2) ^ 40 := by omega
      _ ≤ (J.m + 2) ^ 2 * (J.m + 2) ^ 40 := Nat.mul_le_mul_right _ h4
      _ = (J.m + 2) ^ 42 := by rw [← pow_add]
  have hpow_mult : 2 ^ wordSize mult J.solverWords ≤ (J.m + 2) ^ (42 * mult) := by
    unfold wordSize
    change 2 ^ (mult * (Nat.log 2 B + 1)) ≤ (J.m + 2) ^ (42 * mult)
    rw [Nat.mul_comm mult, pow_mul, pow_mul]
    exact Nat.pow_le_pow_left hpow1 mult
  have hlin : wordSize mult J.solverWords ≤ 84 * mult * (J.m + 1) := by
    unfold wordSize
    change mult * (Nat.log 2 B + 1) ≤ 84 * mult * (J.m + 1)
    have hlog_le : Nat.log 2 B + 1 ≤ 84 * (J.m + 1) := by
      have hm2_le : J.m + 2 ≤ 2 ^ (2 * (J.m + 1)) := by
        have h1 : J.m + 2 ≤ 2 * (J.m + 1) := by omega
        exact h1.trans (Nat.lt_two_pow_self.le)
      have hpow42 : (J.m + 2) ^ 42 ≤ 2 ^ (84 * (J.m + 1)) := by
        calc (J.m + 2) ^ 42 ≤ (2 ^ (2 * (J.m + 1))) ^ 42 := Nat.pow_le_pow_left hm2_le 42
          _ = 2 ^ (2 * (J.m + 1) * 42) := (pow_mul 2 _ 42).symm
          _ = 2 ^ (84 * (J.m + 1)) := by ring_nf
      have h2le : 2 ^ (Nat.log 2 B + 1) ≤ 2 ^ (84 * (J.m + 1)) := hpow1.trans hpow42
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h2le
    calc mult * (Nat.log 2 B + 1) ≤ mult * (84 * (J.m + 1)) := Nat.mul_le_mul_left mult hlog_le
      _ = 84 * mult * (J.m + 1) := by ring
  exact ⟨hpow_mult, hlin⟩

/-! ### Contract verification for the host-width solver adapter -/

private theorem adapter_hasAt_parts {Q P : Program} {f b d : ℕ}
    (hp : P.HasAt b (narrowSolverAdapterModule Q f b d)) :
    P.procs[b]? = some (narrowSolverAdapterBody (b + 1) (b + 7) (b + 5)) ∧
    P.HasAt (b + 1) (compressionModule (b + 1)) ∧
    P.HasAt (b + 5) [copyWords] ∧
    P.HasAt (b + 7) (scratchSolveModule Q f (b + 7) 1 d) := by
  have hcomp_len : (compressionModule (b + 1)).length = 6 := rfl
  refine ⟨hp.head, ?_, ?_, ?_⟩
  · intro i hi
    have h := hp (i + 1) (by
      simp only [narrowSolverAdapterModule, List.length_cons, List.length_append]
      omega)
    have hidx : b + (i + 1) = (b + 1) + i := by omega
    rw [hidx] at h
    simpa only [narrowSolverAdapterModule, List.getElem_cons_succ,
      List.getElem_append_left hi] using h
  · intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst i
    have h := hp 5 (by
      simp only [narrowSolverAdapterModule, List.length_cons, List.length_append, hcomp_len]
      omega)
    have hget : (narrowSolverAdapterModule Q f b d)[5]'(by
        simp only [narrowSolverAdapterModule, List.length_cons, List.length_append, hcomp_len]
        omega) = copyWords := by
      simp only [narrowSolverAdapterModule, List.getElem_cons_succ,
        List.getElem_append_left (show 4 < (compressionModule (b + 1)).length by rw [hcomp_len]; omega)]
      rfl
    simpa only [Nat.add_zero, List.getElem_cons_zero, hget] using h
  · intro i hi
    have h := hp (i + 7) (by
      simp only [narrowSolverAdapterModule, List.length_cons, List.length_append, hcomp_len]
      omega)
    have hidx : b + (i + 7) = (b + 7) + i := by omega
    rw [hidx] at h
    simp only [narrowSolverAdapterModule, List.getElem_cons_succ] at h
    rw [List.getElem_append_right (by rw [hcomp_len]; omega)] at h
    simpa only [hcomp_len, show i + 6 - 6 = i by omega] using h

private theorem adapter_cost_bound (regBound mult m T1 T2 guestW : ℕ)
    (hT : T1 ≤ T2) (hguest : guestW ≤ 84 * mult * (m + 1)) :
    0 + (1 + 1 + 1 + 1) + 2 + (1 + 1) + (500 * m + 500) + 2 + (1 + 1) +
        ((regBound + 6) * T1 + 80 * (2 + 5 * m) + 40 * guestW + regBound + 300) +
        2 + (1 + (1 + 1)) + (17 * m + 10) + 2 + (1 + 1) ≤
    (regBound + 6) * T2 + (3400 * mult + regBound + 6000) * (m + 1) := by
  have hT_mul := Nat.mul_le_mul_left (regBound + 6) hT
  have h40 : 40 * guestW ≤ 3360 * mult * (m + 1) := by
    calc 40 * guestW ≤ 40 * (84 * mult * (m + 1)) := Nat.mul_le_mul_left 40 hguest
      _ = 3360 * mult * (m + 1) := by ring
  have hmul : (3400 * mult + regBound + 6000) * (m + 1) =
      3400 * mult * (m + 1) + regBound * (m + 1) + 6000 * (m + 1) := by ring
  have h3360 : 3360 * mult * (m + 1) ≤ 3400 * mult * (m + 1) :=
    Nat.mul_le_mul_right (m + 1) (Nat.mul_le_mul_right mult (by decide))
  have hreg : regBound ≤ regBound * (m + 1) := Nat.le_mul_of_pos_right regBound (by omega)
  omega

/-- **Host-width solver contract.** When `narrowSolverAdapterModule P.solver 0 b P.scratchDegree`
is placed at index `b` in host program `p`, procedure `b` meets the unrestricted host-width
`solverContract w (narrowSolverTime P) (narrowSolverSpace P.scratchDegree)` at every host word
width `w`. -/
theorem narrowSolverAdapter_meetsContract (P : DyadicWithVConcretePrograms) {w b : ℕ} {p : Program}
    (hp : p.HasAt b (narrowSolverAdapterModule P.solver 0 b P.scratchDegree)) :
    MeetsContract w p b (solverContract w (narrowSolverTime P) (narrowSolverSpace P.scratchDegree)) := by
  obtain ⟨hentry, hcompAt, hcopyAt, hsolveAt⟩ := adapter_hasAt_parts hp
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨⟨a, heap, rfl, J, hat, hend, hJwords, hJcost, hJspace, hJcap⟩, hzero, _⟩ := hpre
  change ZeroFrom mem heap at hzero
  set d := P.scratchDegree
  set mult := scratchWordMultiplier 1 d
  set J' := J.compress
  set guestWidth := wordSize mult J'.solverWords
  have hJlen : J.solverWords.length = 2 + 5 * J.m := J.solverWords_length
  have hJ'len : J'.solverWords.length = 2 + 5 * J.m := J'.solverWords_length
  have hJ'n_le : J'.n ≤ 2 * J.m := J.endpointLabels_count_le
  have hJ'n_comp : J'.n ≤ 2 * J'.m + 1 := by change J'.n ≤ 2 * J.m + 1; omega
  have hJ'cost : J'.CostsBounded (J'.m ^ 10) := hJcost
  have hJ'cap : ∀ e, 1 ≤ J'.capacity e ∧ J'.capacity e ≤ J'.m ^ 40 := hJcap
  obtain ⟨hguestPow0, hguestLin0⟩ := compressed_guestWidth_bounds J' mult hJ'n_le hJ'cost hJ'cap
  have hguestPow : 2 ^ guestWidth ≤ (J.m + 2) ^ (42 * mult) := hguestPow0
  have hguestLin : guestWidth ≤ 84 * mult * (J.m + 1) := hguestLin0
  have hspace_unfold : heap + J.m + (J.n + 5 * J.m + 10 + 2 * (J.m + 2) ^ (42 * mult)) < 2 ^ w :=
    hJspace
  have hw8 : 8 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hcomp_space : heap + (J.solverWords.length + J.n + 2) < 2 ^ w := by omega
  have hdoubled : 2 ^ (guestWidth + 1) + 2 ≤ 2 ^ w := by
    rw [Nat.pow_succ]
    omega
  have h1_val_lt : heap + J.solverWords.length + 2 + J.n < 2 ^ w := by omega
  have hsolve_space : (heap + J.solverWords.length + 2 + J.n) + (1 + 2 ^ guestWidth) < 2 ^ w := by
    omega
  have h2_val_lt : (heap + J.solverWords.length + 2 + J.n) + 1 + 2 ^ guestWidth < 2 ^ w := by
    omega
  have ha_lt : a < 2 ^ w := hwords a (by simp)
  have hh_lt : heap < 2 ^ w := hwords heap (by simp)
  have ha1_lt : a + 1 < 2 ^ w := by omega
  have hm_lt : J.m < 2 ^ w := by omega
  have hmcell : mem (a + 1) = J.m := by
    have h1 := hat 1 (by omega)
    simpa only [Circulation.solverWords, List.getElem_cons_succ, List.getElem_cons_zero] using h1
  have hkComp := compression_meetsContract (w := w) hw8 hcompAt J
  have hkSolve := compressedSolveModule_meetsContract (w := w) (b := b + 7)
    (Q := P.solver) (P := p) (f := 0)
    (T := forestConnectedSolverRuntimeTime P.runtimeResources)
    (S := forestConnectedSolverRuntimeWorkspace P.runtimeResources)
    (c := 1) (d := d)
    P.solver_meetsContract P.solver_deterministic J' hJ'n_comp
    (by simpa only [Nat.one_mul] using P.workspace_le J'.n J'.m)
    hJ'cost hJ'cap hsolveAt
  have hkCopy := copyWords_meetsContract (w := w) hcopyAt
  apply runs_start_le
  unfold narrowSolverAdapterBody
  refine runs_seq_assign_le (v := J.m) (by
    simp only [Expr.eval, startState, List.getD_cons_zero, hw1, ↓reduceIte, BinOp.eval,
      ha1_lt, Option.map_some, hmcell]) ?_
  refine runs_seq_call_le hkComp (vs := [a, heap]) (by
    simp [evalArgs, Expr.eval, startState]) ?_ ?_ ?_
  · wram_words
  · exact ⟨⟨a, heap, rfl, hat, hend, hJwords⟩, hzero, hcomp_space⟩
  · intro h1 mem1 pos1 hpost1
    obtain ⟨⟨_, _, hframe1, hzero1, hat1⟩, hh1⟩ := hpost1
    change h1 = heap + J.solverWords.length + 2 + J.n at hh1
    change ∀ x < heap, mem1 x = mem x at hframe1
    change ZeroFrom mem1 h1 at hzero1
    change ListAt mem1 heap J'.solverWords at hat1
    have hh1_lt : h1 < 2 ^ w := by omega
    refine runs_seq_call_le hkSolve (vs := [heap, h1]) (by
      simp [evalArgs, Expr.eval, startState]) ?_ ?_ ?_
    · wram_words
    · refine ⟨⟨heap, h1, rfl, hat1, by omega, hdoubled⟩, hzero1, ?_⟩
      change h1 + (1 + 2 ^ guestWidth) < 2 ^ w
      omega
    · intro h2 mem2 pos2 hpost2
      obtain ⟨⟨_, _, hframe2, hzero2, hflow2⟩, hh2⟩ := hpost2
      change h2 = h1 + 1 + 2 ^ guestWidth at hh2
      change ∀ x < h1, mem2 x = mem1 x at hframe2
      change ZeroFrom mem2 h2 at hzero2
      change J'.readSolverFlow mem2 h1 =
        compressedCanonicalSolverAt guestWidth P.solver 0 _ _ (P.solver_meetsContract J') J' at hflow2
      have hh2_lt : h2 < 2 ^ w := by omega
      have hm_le_guest : J.m ≤ 1 + 2 ^ guestWidth := by
        have hmult1 : 1 ≤ mult := by unfold mult scratchWordMultiplier; omega
        have hlt := length_lt_two_pow_wordSize hmult1 J'.solverWords
        change J'.solverWords.length < 2 ^ guestWidth at hlt
        omega
      refine runs_seq_call_le hkCopy (vs := [h1, heap, J.m]) (by
        simp [evalArgs, Expr.eval, startState]) ?_ ?_ ?_
      · wram_words
      · exact ⟨h1, heap, J.m, rfl, hw1, by omega, by omega, Or.inl (by omega)⟩
      · intro _ mem3 pos3 hpost3
        obtain ⟨src, dst, len, hargs, _, hcopied, hframe3⟩ := hpost3
        have hsrc : src = h1 := by
          have := congrArg (fun l : List ℕ => l.getD 0 0) hargs; simpa using this.symm
        have hdst : dst = heap := by
          have := congrArg (fun l : List ℕ => l.getD 1 0) hargs; simpa using this.symm
        have hlen : len = J.m := by
          have := congrArg (fun l : List ℕ => l.getD 2 0) hargs; simpa using this.symm
        subst src; subst dst; subst len
        refine runs_ret_le (v := h2) (by
          simp [Expr.eval, startState]) ?_ ?_
        · have hdim : solverDimensions [a, heap] mem = (J.n, J.m) :=
            solverDimensions_of_at J mem a heap hat
          change heap ≤ h2 ∧
            h2 ≤ heap + ((solverDimensions [a, heap] mem).2 +
              narrowSolverSpace d (solverDimensions [a, heap] mem).1 (solverDimensions [a, heap] mem).2) ∧
            (∀ x < heap, mem3 x = mem x) ∧ ZeroFrom mem3 h2 ∧
            ∀ K : Circulation, ListAt mem a K.solverWords →
              K.Optimal (fun e => (K.readSolverFlow mem3 heap e : ℝ))
          rw [hdim]
          refine ⟨by omega, ?_, ?_, ?_, ?_⟩
          · dsimp only [narrowSolverSpace, mult] at hguestPow ⊢
            omega
          · intro x hx
            exact (hframe3 x (Or.inl hx)).trans
              ((hframe2 x (by omega)).trans (hframe1 x hx))
          · intro x hx
            exact (hframe3 x (Or.inr (by omega))).trans
              (hzero2 x hx)
          · intro K hKat
            have hKdim := solverDimensions_of_at K mem a heap hKat
            have hKm : K.m = J.m := congrArg Prod.snd (hKdim.symm.trans hdim)
            have hlenEq : J.solverWords.length = K.solverWords.length := by
              rw [J.solverWords_length, K.solverWords_length, hKm]
            have hJK : J = K := circulation_eq_of_solverWords_eq (hat.ext hKat hlenEq)
            subst hJK
            have hoptJ' : J'.Optimal (fun e => (J'.readSolverFlow mem2 h1 e : ℝ)) := by
              rw [hflow2]
              exact compressedCanonicalSolverAt_optimal guestWidth P.solver 0 _ _
                (P.solver_meetsContract J') J'
            have hoptJ : J.Optimal (fun e => (J'.readSolverFlow mem2 h1 e : ℝ)) :=
              (J.compress_optimal_iff _).mp hoptJ'
            have hflowEq : (fun e : Fin J.m => (J.readSolverFlow mem3 heap e : ℝ)) =
                (fun e : Fin J.m => (J'.readSolverFlow mem2 h1 e : ℝ)) := by
              funext e
              change ((mem3 (heap + e.val) : ℤ) : ℝ) = ((mem2 (h1 + e.val) : ℤ) : ℝ)
              rw [hcopied e.val e.isLt]
            rwa [hflowEq]
        · have hdim : solverDimensions [a, heap] mem = (J.n, J.m) :=
            solverDimensions_of_at J mem a heap hat
          change _ ≤ narrowSolverTime P (solverDimensions [a, heap] mem).1
            (solverDimensions [a, heap] mem).2
          rw [hdim]
          dsimp only [narrowSolverTime]
          have hT_le : forestConnectedSolverRuntimeTime P.runtimeResources J'.n J'.m ≤
              linkedForestSolverTime P.runtimeResources (2 * J.m) J.m :=
            (forestConnectedSolverRuntimeTime_le_linkedForestSolverTime P.runtimeResources J'.n J'.m).trans
              (linkedForestSolverTime_mono P.runtimeResources J'.n (2 * J.m) J'.m J.m hJ'n_le le_rfl)
          simp only [compressionContract, compressedSolveContract, copyWordsContract,
            heapContract, argsSize_cons, argsSize_nil, Expr.size_load, Expr.size_bin,
            Expr.size_reg, Expr.size_const, Nat.add_zero]
          dsimp only [J', mult, d, guestWidth] at hT_le hguestLin hJ'len ⊢
          rw [hJ'len]
          exact adapter_cost_bound P.solver.regBound (scratchWordMultiplier 1 P.scratchDegree) J.m
            (forestConnectedSolverRuntimeTime P.runtimeResources J.compress.n J.compress.m)
            (linkedForestSolverTime P.runtimeResources (2 * J.m) J.m)
            (wordSize (scratchWordMultiplier 1 P.scratchDegree) J.compress.solverWords)
            hT_le hguestLin

end MinCostFlow.NarrowTop
