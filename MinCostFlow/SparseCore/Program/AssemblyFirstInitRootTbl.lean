module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitComp
public import MinCostFlow.SparseCore.Program.ReadRestartInitSetup
public import MinCostFlow.SparseCore.Program.ReadSpec
public import MinCostFlow.SparseCore.Program.RestartLoopDefs
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The roots of the forest as a table (`AssemblyFirstInitRootTbl`)

The build of a branch at its init makes the output graph `S₀` with P10's rebuild
(`AssemblyFirstInitS0.lean`). The rebuild asks the root of the ends of each edge through a root
query (`RootQueryAt`). P4's root query may write into P4's cells, which lie below the heap pointer
of the build, and the build must keep all those cells. So the build answers the root
queries from a table of its own, which it writes first.

**The table.** Each tree of the forest `F` has exactly one root. So it is enough to label the trees
and to store, for each label, the root with that label. The procedure `rootTblBody` does this:
1. it writes the memory form of `F` from P4's export of `F` (`initGraphFromExportStmt`);
2. it labels the components of `F` with the component map (`compMap_runs`): the word
   `cmpF + v` holds the index of the component of `v`;
3. for each root `r`, it stores `r` at `rootOf + (index of the component of r)`.
A two-word record at the heap pointer holds `cmpF` and `rootOf`.

**The query** (`rootTblQueryBody`) reads `rootOf + cmpF[u]` and writes it at its heap pointer. It
writes nothing else, so the table and all other memory stay as they are. `rootTblQuery` packs it
as a `RootQueryAt` on the representation `rootTblRep` of the table.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LSF MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Read MinCostFlow.SparseCore.Program.Restart

/-! ## The table and its query -/

/-- **The table of the roots** for the vertex set `V`. The record at `b` holds the addresses
`x.1` of the labels and `x.2` of the roots of the labels. For each `u ∈ V`, the label of `u` is
below `vCap`, and the root at that label is `s u`. -/
def rootTblRep (vCap : ℕ) (V : Finset ℕ) : DSRep (ℕ → ℕ) where
  τ := ℕ × ℕ
  rep b s x mem := mem b = x.1 ∧ mem (b + 1) = x.2 ∧
    ∀ u ∈ V, u < vCap ∧ mem (x.1 + u) < vCap ∧ mem (x.2 + mem (x.1 + u)) = s u
  phi _ _ _ := 0
  foot b x a := (b ≤ a ∧ a < b + 2) ∨ (x.1 ≤ a ∧ a < x.1 + vCap) ∨ (x.2 ≤ a ∧ a < x.2 + vCap)

theorem rootTblRep_local (vCap : ℕ) (V : Finset ℕ) : (rootTblRep vCap V).Local := by
  intro b s x mem mem' hag
  refine ⟨fun ⟨h0, h1, hu⟩ => ⟨?_, ?_, fun u hu' => ?_⟩, rfl⟩
  · rw [← hag b (Or.inl ⟨le_rfl, by omega⟩)]; exact h0
  · rw [← hag (b + 1) (Or.inl ⟨by omega, by omega⟩)]; exact h1
  · obtain ⟨hlt, hc, hr⟩ := hu u hu'
    have e1 : mem' (x.1 + u) = mem (x.1 + u) := (hag _ (Or.inr (Or.inl ⟨by omega, by omega⟩))).symm
    have e2 : mem' (x.2 + mem (x.1 + u)) = mem (x.2 + mem (x.1 + u)) :=
      (hag _ (Or.inr (Or.inr ⟨by omega, by omega⟩))).symm
    exact ⟨hlt, e1 ▸ hc, by rw [e1, e2]; exact hr⟩

/-- **The root query on the table**, `[b, j, u, h]`: store the root at the label of `u` at `h`,
and return `h + 1`. -/
def rootTblQueryBody : Stmt :=
  .store (.reg 3) (.load (.bin .add (.load (.bin .add (.reg 0) (.const 1)))
    (.load (.bin .add (.load (.reg 0)) (.reg 2))))) ;;
  .ret (.bin .add (.reg 3) (.const 1))

theorem rootTblQueryBody_noRand : rootTblQueryBody.NoRand := by
  simp [rootTblQueryBody, Stmt.NoRand]

/-- **The root query of the table** as a `RootQueryAt`: the state is the root function, a vertex
is good when it lies in `V`, and a query costs at most `20`. -/
def rootTblQuery (w : ℕ) (p : Program) (fQ vCap : ℕ) (V : Finset ℕ)
    (hf : p.procs[fQ]? = some rootTblQueryBody) : RootQueryAt w p fQ where
  σ := ℕ → ℕ
  R := rootTblRep vCap V
  root s _ u := s u
  ok _ _ u := u ∈ V
  cost := 20
  R_local := rootTblRep_local vCap V
  runs b j u h s x mem pos ω hb _ hu hh hok hrep hfoot hz hsp := by
    obtain ⟨h0, h1, hU⟩ := hrep
    obtain ⟨hult, hclt, hval⟩ := hU u hok
    have f1 : x.1 + u < h := hfoot _ (Or.inr (Or.inl ⟨by omega, by omega⟩))
    have f2 : x.2 + mem (x.1 + u) < h := hfoot _ (Or.inr (Or.inr ⟨by omega, by omega⟩))
    have fb : b + 1 < h := hfoot _ (Or.inl ⟨by omega, by omega⟩)
    set st0 := startState [b, j, u, h] mem pos with hst0
    have r0 : st0.regs 0 = b := rfl
    have r2 : st0.regs 2 = u := rfl
    have r3 : st0.regs 3 = h := rfl
    have hm0 : st0.mem b = x.1 := h0
    have hm1 : st0.mem (b + 1) = x.2 := h1
    have e1 : (Expr.bin .add (.reg 0) (.const 1)).eval w st0 = some (b + 1) :=
      Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_const (by omega)) (by omega)
    have e2 : (Expr.load (.bin .add (.reg 0) (.const 1))).eval w st0 = some x.2 :=
      Expr.eval_load_of_eq e1 hm1
    have e3 : (Expr.bin .add (.load (.reg 0)) (.reg 2)).eval w st0 = some (x.1 + u) :=
      Expr.eval_add (Expr.eval_load_of_eq (Expr.eval_reg_of_eq r0) hm0) (Expr.eval_reg_of_eq r2)
        (by omega)
    have e4 : (Expr.load (.bin .add (.load (.reg 0)) (.reg 2))).eval w st0 =
        some (mem (x.1 + u)) := Expr.eval_load e3
    have e5 : (Expr.bin .add (.load (.bin .add (.reg 0) (.const 1)))
        (.load (.bin .add (.load (.reg 0)) (.reg 2)))).eval w st0 =
        some (x.2 + mem (x.1 + u)) := Expr.eval_add e2 e4 (by omega)
    have eA : (Expr.load (.bin .add (.load (.bin .add (.reg 0) (.const 1)))
        (.load (.bin .add (.load (.reg 0)) (.reg 2))))).eval w st0 = some (s u) :=
      Expr.eval_load_of_eq e5 hval
    set st1 : State := { st0 with mem := Function.update mem h (s u) } with hst1
    have q1 : Runs w p ω (.store (.reg 3) (.load (.bin .add (.load (.bin .add (.reg 0) (.const 1)))
        (.load (.bin .add (.load (.reg 0)) (.reg 2)))))) st0 .normal st1 _ :=
      runs_store_iff.mpr ⟨h, s u, Expr.eval_reg_of_eq r3, eA, rfl, rfl, rfl⟩
    have q2 : Runs w p ω (.ret (.bin .add (.reg 3) (.const 1))) st1 (.returned (h + 1)) st1 4 :=
      runs_ret_iff.mpr ⟨h + 1, Expr.eval_add (Expr.eval_reg_of_eq r3)
        (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
    have hagr : ∀ a, (rootTblRep vCap V).foot b x a → mem a = st1.mem a := by
      intro a ha
      have := hfoot a ha
      show mem a = Function.update mem h (s u) a
      rw [Function.update_of_ne (by omega)]
    refine ⟨_, hf, .returned (h + 1), st1, _, x,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, q1, q2, rfl⟩), ?_,
      ((rootTblRep_local vCap V) b s x mem st1.mem hagr).1 ⟨h0, h1, hU⟩, Nat.le_succ h,
      le_rfl, fun a ha => ?_, fun a ha hn => ?_, fun a ha => Or.inl ha, ?_⟩
    · show Function.update mem h (s u) h = s u
      exact Function.update_self _ _ _
    · show Function.update mem h (s u) a = 0
      rw [Function.update_of_ne (by simp only [Outcome.value] at ha; omega)]
      exact hz a (by simp only [Outcome.value] at ha; omega)
    · show Function.update mem h (s u) a = mem a
      rw [Function.update_of_ne (by omega)]
    · show _ + 0 ≤ 20 + 0
      simp only [Expr.size, Nat.add_zero]
      omega

/-! ## The procedure that writes the table -/

/-- **The table of the roots**, `[fD, vCap, eCap, rootsPtr, nR, heap]`, where `fD` is P4's export
of the forest and the `nR` roots lie at `rootsPtr`. With `g = heap + 2`, `cmpF` after the memory
form of the forest at `g`, and `rootOf = cmpF + vCap`:
1. store `cmpF` and `rootOf` at `heap` and `heap + 1`;
2. write the forest at `g` (`fGraph`), and its labels at `cmpF` (`fComp`, scratch from
   `rootOf + vCap`);
3. for each root `r`, store `r` at `rootOf + cmpF[r]`;
4. return the end `rootOf + vCap + 5 vCap + 6 eCap + 3` of the scratch. -/
def rootTblBody (fGraph fComp : ℕ) : Stmt :=
  .assign 6 (.bin .add (.reg 5) (.const 2)) ;;
  .assign 7 (.bin .add (.reg 6) (.bin .add (.bin .add (.const 4) (.bin .mul (.const 7) (.reg 1)))
    (.bin .mul (.const 9) (.reg 2)))) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 1)) ;;
  .store (.reg 5) (.reg 7) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.reg 8) ;;
  .call 9 fGraph [.reg 6, .reg 1, .reg 2, .reg 0] ;;
  .call 9 fComp [.reg 6, .reg 7, .bin .add (.reg 8) (.reg 1)] ;;
  forRange 10 (.const 0) (.reg 4)
    (.store (.bin .add (.reg 8) (.load (.bin .add (.reg 7) (.load (.bin .add (.reg 3) (.reg 10))))))
      (.load (.bin .add (.reg 3) (.reg 10)))) ;;
  .ret (.bin .add (.bin .add (.reg 8) (.reg 1))
    (.bin .add (.bin .add (.bin .mul (.const 5) (.reg 1)) (.bin .mul (.const 6) (.reg 2)))
      (.const 3)))

theorem rootTblBody_noRand (fGraph fComp : ℕ) : (rootTblBody fGraph fComp).NoRand := by
  simp [rootTblBody, forRange, forUp, Stmt.NoRand]

/-- The words of the table, from the heap pointer: the record, the forest, the labels, the roots
of the labels, and the scratch of the labels. -/
def rootTblSpace (vCap eCap : ℕ) : ℕ :=
  2 + dynGraphSize vCap eCap + 2 * vCap + (5 * vCap + 6 * eCap + 3)

/-- The cost of `rootTblBody` on a forest with `n` vertices, `m` edges and `nR` roots. -/
def rootTblCost (n m nR : ℕ) : ℕ := 130 * n + 490 * m + compMapCost n m + 40 * nR + 400

/-! ## The loop over the roots -/

/-- **The loop over the roots.** Registers `3 = rootsPtr`, `4 = nR`, `7 = cmpF`, `8 = rootOf`. Let
the labels `lab r = mem (cmpF + r)` of the roots be below `vCap`, and let two roots with the same
label be equal. Then the loop stores each root at `rootOf` plus its label, and changes nothing
outside `[rootOf, rootOf + vCap)` and register `10`. -/
theorem rootTbl_loop {w : ℕ} {p : Program} {mem : ℕ → ℕ} {rootsPtr cmpF rootOf vCap : ℕ}
    {roots : List ℕ} (R : ℕ → ℕ) (hR3 : R 3 = rootsPtr) (hR4 : R 4 = roots.length)
    (hR7 : R 7 = cmpF) (hR8 : R 8 = rootOf)
    (hroots : ListAt mem rootsPtr roots)
    (hlab : ∀ t (ht : t < roots.length), mem (cmpF + roots[t]) < vCap)
    (hsame : ∀ t₁ (h₁ : t₁ < roots.length) t₂ (h₂ : t₂ < roots.length),
      mem (cmpF + roots[t₁]) = mem (cmpF + roots[t₂]) → roots[t₁] = roots[t₂])
    (hrw : rootsPtr + roots.length < 2 ^ w) (hcw : ∀ r ∈ roots, cmpF + r < 2 ^ w)
    (hlay : ∀ t, t < roots.length → rootsPtr + t < rootOf ∨ rootOf + vCap ≤ rootsPtr + t)
    (hlay2 : ∀ r ∈ roots, cmpF + r < rootOf ∨ rootOf + vCap ≤ cmpF + r)
    (hw : rootOf + vCap < 2 ^ w) (hw16 : 16 ≤ 2 ^ w) :
    Triple w p (fun st => st.mem = mem ∧ ∀ r, r ≠ 10 → st.regs r = R r)
      (forRange 10 (.const 0) (.reg 4)
        (.store (.bin .add (.reg 8) (.load (.bin .add (.reg 7)
          (.load (.bin .add (.reg 3) (.reg 10)))))) (.load (.bin .add (.reg 3) (.reg 10)))))
      (normalPost fun st => (∀ r, r ≠ 10 → st.regs r = R r) ∧
        (∀ a, (a < rootOf ∨ rootOf + vCap ≤ a) → st.mem a = mem a) ∧
        ∀ t (ht : t < roots.length), st.mem (rootOf + mem (cmpF + roots[t])) = roots[t])
      (fun _ => roots.length * 40 + 7) := by
  have hw1 : 1 < 2 ^ w := by omega
  let Inv : ℕ → State → Prop := fun i st =>
    (∀ r, r ≠ 10 → st.regs r = R r) ∧ st.regs 10 = i ∧
    (∀ a, (a < rootOf ∨ rootOf + vCap ≤ a) → st.mem a = mem a) ∧
    ∀ t (ht : t < roots.length), t < i → st.mem (rootOf + mem (cmpF + roots[t])) = roots[t]
  have hstep : ∀ i, 0 ≤ i → i < roots.length →
      Triple w p (Inv i)
        (.store (.bin .add (.reg 8) (.load (.bin .add (.reg 7)
          (.load (.bin .add (.reg 3) (.reg 10)))))) (.load (.bin .add (.reg 3) (.reg 10))))
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 10 (i + 1) } ∧
            st₁.regs 10 = i)
        (fun _ => 30) := by
    intro i _ hi st ω' hI
    obtain ⟨hR, r10, hfr, hcp⟩ := hI
    have r3 : st.regs 3 = rootsPtr := (hR 3 (by omega)).trans hR3
    have r7 : st.regs 7 = cmpF := (hR 7 (by omega)).trans hR7
    have r8 : st.regs 8 = rootOf := (hR 8 (by omega)).trans hR8
    have hri : roots[i] ∈ roots := List.getElem_mem hi
    have m1 : st.mem (rootsPtr + i) = roots[i] := by
      rw [hfr _ (hlay i hi)]; exact hroots i hi
    have m2 : st.mem (cmpF + roots[i]) = mem (cmpF + roots[i]) := hfr _ (hlay2 _ hri)
    have hl := hlab i hi
    have eI : (Expr.load (.bin .add (.reg 3) (.reg 10))).eval w st = some roots[i] :=
      Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_reg_of_eq r10)
        (by omega)) m1
    have eA : (Expr.bin .add (.reg 8) (.load (.bin .add (.reg 7)
        (.load (.bin .add (.reg 3) (.reg 10)))))).eval w st =
        some (rootOf + mem (cmpF + roots[i])) :=
      Expr.eval_add (Expr.eval_reg_of_eq r8) (Expr.eval_load_of_eq (Expr.eval_add
        (Expr.eval_reg_of_eq r7) eI (hcw _ hri)) m2) (by omega)
    refine runs_start_le ?_
    refine runs_store_le eA eI ?_ ?_
    · refine ⟨⟨fun r hr => ?_, by simp, fun a ha => ?_, fun t ht hti => ?_⟩, r10⟩
      · simp [hr, hR r hr]
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hfr a ha
      · dsimp only
        by_cases hti' : t = i
        · subst hti'
          rw [Function.update_self]
        · by_cases hlt : mem (cmpF + roots[t]) = mem (cmpF + roots[i])
          · rw [hlt, Function.update_self]
            exact (hsame t ht i hi hlt).symm
          · rw [Function.update_of_ne (by omega)]
            exact hcp t ht (by omega)
    · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin]
      omega
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 10) (lo := .const 0)
    (hi := .reg 4)
    (P := fun st => st.mem = mem ∧ ∀ r, r ≠ 10 → st.regs r = R r)
    (Inv := Inv) 30 0 roots.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hP => ⟨Expr.eval_const (by omega), fun r hr => by simp [hr, hP.2 r hr], by simp,
      fun a _ => by simp [hP.1], fun t _ ht => absurd ht (Nat.not_lt_zero _)⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq ((hI.1 4 (by omega)).trans hR4)) hstep
  refine hloop.conseq (fun st h => h) ?_ ?_
  · intro o st' hQ
    cases o with
    | returned _ => exact hQ
    | normal =>
      obtain ⟨hR, -, hfr, hcp⟩ := hQ
      exact ⟨hR, hfr, fun t ht => hcp t ht ht⟩
  · intro st _
    simp only [Expr.size_reg, Expr.size_const]
    omega

/-! ## The run of the procedure -/

/-- A call whose body has a run with a postcondition on the returned value and the memory,
followed by a statement, in the forward form with a fixed total cost. -/
theorem runs_seq_call_post_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {body s : Stmt} {st : State} {vs : List ℕ} {B k T : ℕ}
    {Q_call : ℕ → (ℕ → ℕ) → Prop} {Q : Outcome → State → Prop}
    (hproc : p.procs[f]? = some body) (hargs : evalArgs w st args = some vs)
    (hbody : ∃ o st₁ c₁, Runs w p ω body (startState vs st.mem st.pos) o st₁ c₁ ∧
      Q_call o.value st₁.mem ∧ c₁ ≤ B)
    (hrest : ∀ v mem' pos', Q_call v mem' →
      ∃ o st' c₂, Runs w p ω s { mem := mem', regs := Function.update st.regs r v, pos := pos' }
        o st' c₂ ∧ Q o st' ∧ (k + argsSize args + B + 2) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩ := hbody
  obtain ⟨o₂, st', c₂, hr₂, hq₂, hc₂⟩ := hrest o₁.value st₁.mem st₁.pos hq₁
  have hcall : Runs w p ω (.call r f args) st .normal
      { mem := st₁.mem, regs := Function.update st.regs r o₁.value, pos := st₁.pos }
      (argsSize args + c₁ + 1) :=
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hproc, hr₁, rfl, rfl, rfl⟩
  exact ⟨o₂, st', (argsSize args + c₁ + 1) + c₂ + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall, hr₂, rfl⟩), hq₂, by omega⟩

/-- Each vertex has, in the map of the components, the index of its component. -/
theorem compMapPost_idx {w : ℕ} {G : MGraph} {vCap cmpH heap : ℕ} {mem mem' : ℕ → ℕ}
    {comps : List (Finset ℕ)} (hP : CompMapPost w G vCap cmpH heap mem mem' comps)
    {v : ℕ} (hv : v ∈ G.V) :
    ∃ c, ∃ hc : c < comps.length, comps[c] = compOf G v ∧ mem' (cmpH + v) = c := by
  obtain ⟨-, hmem, hidx, -⟩ := hP
  obtain ⟨c, hc, hcv⟩ := List.mem_iff_getElem.mp ((hmem _).mpr (compOf_mem_components hv))
  exact ⟨c, hc, hcv, hidx c hc v (hcv ▸ self_mem_compOf hv)⟩

/-- Two vertices with the same index in the map of the components are connected. -/
theorem compMapPost_connected {w : ℕ} {G : MGraph} {vCap cmpH heap : ℕ} {mem mem' : ℕ → ℕ}
    {comps : List (Finset ℕ)} (hP : CompMapPost w G vCap cmpH heap mem mem' comps)
    {u v : ℕ} (hu : u ∈ G.V) (hv : v ∈ G.V) (h : mem' (cmpH + u) = mem' (cmpH + v)) :
    G.Connected u v := by
  obtain ⟨c, hc, hcu, hu'⟩ := compMapPost_idx hP hu
  obtain ⟨d, hd, hdv, hv'⟩ := compMapPost_idx hP hv
  have hcd : c = d := by omega
  subst hcd
  exact (compOf_eq_iff hv).mp (hcu.symm.trans hdv)

/-- Connected vertices have the same index in the map of the components. -/
theorem compMapPost_eq_of_connected {w : ℕ} {G : MGraph} {vCap cmpH heap : ℕ}
    {mem mem' : ℕ → ℕ} {comps : List (Finset ℕ)}
    (hP : CompMapPost w G vCap cmpH heap mem mem' comps)
    {u v : ℕ} (hu : u ∈ G.V) (hv : v ∈ G.V) (h : G.Connected u v) :
    mem' (cmpH + u) = mem' (cmpH + v) := by
  obtain ⟨c, hc, hcu, hu'⟩ := compMapPost_idx hP hu
  obtain ⟨d, hd, hdv, hv'⟩ := compMapPost_idx hP hv
  rw [hu', hv']
  have hcd : comps[c] = comps[d] := by rw [hcu, hdv]; exact compOf_eq_of_connected h
  exact (List.Nodup.getElem_inj_iff hP.1).mp hcd

/-- There are at most `vCap` components when the vertices lie below `vCap`. -/
theorem compMapPost_length_le {w : ℕ} {G : MGraph} {vCap cmpH heap : ℕ} {mem mem' : ℕ → ℕ}
    {comps : List (Finset ℕ)} (hP : CompMapPost w G vCap cmpH heap mem mem' comps)
    (hV : ∀ v ∈ G.V, v < vCap) : comps.length ≤ vCap := by
  obtain ⟨hnd, hmem, -⟩ := hP
  calc comps.length = comps.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ (components G).card :=
        Finset.card_le_card fun C hC => (hmem C).mp (List.mem_toFinset.mp hC)
    _ ≤ G.V.card := Finset.card_image_le
    _ ≤ (Finset.range vCap).card :=
        Finset.card_le_card fun v hv => Finset.mem_range.mpr (hV v hv)
    _ = vCap := Finset.card_range _

/-- A finite set below `cap` has at most `cap` members. -/
theorem card_le_of_lt_cap {S : Finset ℕ} {cap : ℕ} (h : ∀ x ∈ S, x < cap) : S.card ≤ cap :=
  (Finset.card_le_card fun x hx => Finset.mem_range.mpr (h x hx)).trans (Finset.card_range cap).le

/-- **The run of the table of the roots.** Let `fD` hold P4's export of the forest `F` and the
roots `roots` lie at `rootsPtr`, below the heap pointer, with fresh memory from `heap`. Let `rt u`
be a root connected to `u`, and let two connected roots be equal. Then the procedure returns
`heap + rootTblSpace vCap eCap`, and the table at `heap` gives `rt u` for each vertex `u` of `F`.
The memory below `heap` does not change. -/
theorem rootTbl_runs {w bC fGraph vCap eCap fD hEnd rootsPtr heap pos : ℕ} {p : Program}
    (ω : ℕ → Bool) {F : MGraph} {roots : List ℕ} {rt : ℕ → ℕ} {mem : ℕ → ℕ}
    (hpG : MeetsContract w p fGraph (initGraphFromExportContract w vCap eCap F))
    (hpC : p.HasAt bC (compMapModule bC))
    (hF : F.IsValid) (hFV : ∀ v ∈ F.V, v < vCap) (hFE : ∀ e ∈ F.E, e < eCap)
    (hExp : ExportAt mem fD hEnd F) (hEndLe : hEnd ≤ heap)
    (hroots : ListAt mem rootsPtr roots) (hrootsLe : rootsPtr + roots.length ≤ heap)
    (hrV : ∀ r ∈ roots, r ∈ F.V)
    (hrt : ∀ u ∈ F.V, rt u ∈ roots ∧ F.Connected u (rt u))
    (huniq : ∀ r₁ ∈ roots, ∀ r₂ ∈ roots, F.Connected r₁ r₂ → r₁ = r₂)
    (hz : ZeroFrom mem heap) (hsp : heap + rootTblSpace vCap eCap < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) (hfDw : fD < 2 ^ w) :
    ∃ st' c, Runs w p ω (rootTblBody fGraph bC)
        (startState [fD, vCap, eCap, rootsPtr, roots.length, heap] mem pos)
        (.returned (heap + rootTblSpace vCap eCap)) st' c ∧
      (rootTblRep vCap F.V).rep heap rt
        (heap + 2 + dynGraphSize vCap eCap, heap + 2 + dynGraphSize vCap eCap + vCap) st'.mem ∧
      (∀ a < heap, st'.mem a = mem a) ∧
      ZeroFrom st'.mem (heap + rootTblSpace vCap eCap) ∧
      c ≤ rootTblCost F.n F.m roots.length := by
  have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hsp' : heap + (2 + (4 + 7 * vCap + 9 * eCap) + 2 * vCap + (5 * vCap + 6 * eCap + 3)) <
      2 ^ w := hsp
  have hn : F.n ≤ vCap := card_le_of_lt_cap hFV
  have hm : F.m ≤ eCap := card_le_of_lt_cap hFE
  set nR := roots.length with hnR
  set cmpF := heap + 2 + (4 + 7 * vCap + 9 * eCap) with hcmpF
  set rootOf := cmpF + vCap with hrootOf
  have hrw : ∀ r ∈ roots, r < vCap := fun r hr => hFV r (hrV r hr)
  have h5 := Nat.mul_le_mul_left 5 hn
  have h6 := Nat.mul_le_mul_left 6 hm
  suffices H : ∃ o st' c, Runs w p ω (rootTblBody fGraph bC)
      (startState [fD, vCap, eCap, rootsPtr, nR, heap] mem pos) o st' c ∧
      (o = .returned (heap + rootTblSpace vCap eCap) ∧
        (rootTblRep vCap F.V).rep heap rt (cmpF, rootOf) st'.mem ∧
        (∀ a < heap, st'.mem a = mem a) ∧ ZeroFrom st'.mem (heap + rootTblSpace vCap eCap)) ∧
      0 + c ≤ rootTblCost F.n F.m nR by
    obtain ⟨o, st', c, hr, ⟨rfl, h1, h2, h3⟩, hc⟩ := H
    exact ⟨st', c, hr, h1, h2, h3, by omega⟩
  unfold rootTblBody
  refine runs_seq_assign_le (v := heap + 2) (by eval_expr) ?_
  refine runs_seq_assign_le (v := cmpF) (by eval_expr) ?_
  refine runs_seq_assign_le (v := rootOf) (by eval_expr) ?_
  refine runs_seq_store_le (x := heap) (v := cmpF) (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (x := heap + 1) (v := rootOf) (by eval_expr) (by eval_expr) ?_
  set mem1 := Function.update (Function.update mem heap cmpF) (heap + 1) rootOf with hmem1
  have hm1lo : ∀ a, a < heap → mem1 a = mem a := fun a ha => by
    rw [hmem1, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hm1hi : ∀ a, heap + 2 ≤ a → mem1 a = mem a := fun a ha => by
    rw [hmem1, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  refine runs_seq_call_le hpG (vs := [heap + 2, vCap, eCap, fD]) (by eval_expr)
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv; omega)
    ⟨heap + 2, fD, hEnd, rfl, hw16, by omega, by omega,
      fun a ha => (hm1hi a (by omega)).trans (hz a (by omega)), hF, hFV, hFE,
      exportAt_congr (fun a _ ha => hm1lo a (by omega)) hExp⟩ (fun v mem2 pos2 hpost => ?_)
  obtain ⟨gP, d, hargs, -, hG2, hfr2, hz2⟩ := hpost
  simp only [List.cons.injEq, and_true, true_and] at hargs
  obtain ⟨rfl, rfl⟩ := hargs
  have hm2lo : ∀ a, a < heap + 2 → mem2 a = mem1 a := fun a ha => hfr2 a (Or.inl ha)
  obtain ⟨o3, st3, c3, hr3, ⟨comps, ho3, hpost3⟩, hc3⟩ :=
    compMap_runs (w := w) (ω := ω) (pos := pos2) (cmpH := cmpF) (heap := rootOf + vCap) hpC hG2
      (by rw [hdg]) (by omega)
      (fun a ha => hz2 a (by rw [hdg]; omega))
      (by unfold compMapSpace; omega) (by omega)
  have hbody0 : p.procs[bC]? = some (compMapBody (bC + 1) (bC + 2)) := by
    simpa [compMapModule] using hpC 0 (by simp [compMapModule])
  refine runs_seq_call_post_le (B := compMapCost F.n F.m) (vs := [heap + 2, cmpF, rootOf + vCap])
    (Q_call := fun v mem' => ∃ comps : List (Finset ℕ), v = comps.length ∧
      CompMapPost w F vCap cmpF (rootOf + vCap) mem2 mem' comps) hbody0
    (by eval_expr) ⟨o3, st3, c3, hr3, ⟨comps, by rw [ho3]; rfl, hpost3⟩, hc3⟩
    (fun v mem3 pos3 hpost => ?_)
  obtain ⟨comps', -, hP⟩ := hpost
  obtain ⟨-, -, -, -, hlow3, -, hz3⟩ := id hP
  -- the labels of the roots
  have hlen := compMapPost_length_le hP hFV
  have hlab : ∀ r ∈ F.V, mem3 (cmpF + r) < vCap := fun r hr => by
    obtain ⟨c, hc, -, hrc⟩ := compMapPost_idx hP hr
    omega
  have hroots3 : ListAt mem3 rootsPtr roots := fun t ht => by
    rw [hlow3 _ (by omega), hm2lo _ (by omega), hm1lo _ (by omega)]; exact hroots t ht
  have hrootOf3 : ∀ a, rootOf + vCap + (5 * vCap + 6 * eCap + 3) ≤ a → mem3 a = 0 :=
    fun a ha => hz3 a (by unfold compMapSpace; omega)
  have hsame : ∀ t₁ (h₁ : t₁ < roots.length) t₂ (h₂ : t₂ < roots.length),
      mem3 (cmpF + roots[t₁]) = mem3 (cmpF + roots[t₂]) → roots[t₁] = roots[t₂] :=
    fun t₁ h₁ t₂ h₂ heq => huniq _ (List.getElem_mem h₁) _ (List.getElem_mem h₂)
      (compMapPost_connected hP (hrV _ (List.getElem_mem h₁)) (hrV _ (List.getElem_mem h₂)) heq)
  -- the loop over the roots
  refine runs_seq_triple_le (rootTbl_loop (mem := mem3) (rootsPtr := rootsPtr) (cmpF := cmpF)
    (rootOf := rootOf) (vCap := vCap) (roots := roots) _ ?h3 ?h4 ?h7 ?h8 hroots3
    (fun t ht => hlab _ (hrV _ (List.getElem_mem ht))) hsame (by omega)
    (fun r hr => by have := hrw r hr; omega) (fun t ht => Or.inl (by omega))
    (fun r hr => Or.inl (by have := hrw r hr; omega)) (by omega) hw16)
    ⟨rfl, fun r _ => rfl⟩ (fun st₁ h₁ => ?_)
  case h3 => rfl
  case h4 => rfl
  case h7 => rfl
  case h8 => rfl
  obtain ⟨hR₁, hfr₁, htbl₁⟩ := h₁
  have r1 : st₁.regs 1 = vCap := hR₁ 1 (by omega)
  have r2 : st₁.regs 2 = eCap := hR₁ 2 (by omega)
  have r8 : st₁.regs 8 = rootOf := hR₁ 8 (by omega)
  have hlo : ∀ a < heap + 2, st₁.mem a = mem1 a := fun a ha => by
    rw [hfr₁ a (Or.inl (by omega)), hlow3 a (by omega), hm2lo a ha]
  refine runs_ret_le (v := heap + rootTblSpace vCap eCap)
    (Expr.eval_eq_of_eq (by eval_expr) (by rw [rootTblSpace, hdg]; omega))
    ⟨rfl, ⟨?_, ?_, fun u hu => ?_⟩, fun a ha => ?_, fun a ha => ?_⟩ ?_
  · rw [hlo heap (by omega), hmem1, Function.update_of_ne (by omega), Function.update_self]
  · rw [hlo (heap + 1) (by omega), hmem1, Function.update_self]
  · have hu1 : st₁.mem (cmpF + u) = mem3 (cmpF + u) :=
      hfr₁ _ (Or.inl (by have := hFV u hu; omega))
    obtain ⟨hrtm, hcon⟩ := hrt u hu
    obtain ⟨t, ht, hrt'⟩ := List.mem_iff_getElem.mp hrtm
    have hlab' : mem3 (cmpF + u) = mem3 (cmpF + roots[t]) := by
      rw [hrt']; exact compMapPost_eq_of_connected hP hu (hrV _ hrtm) hcon
    refine ⟨hFV u hu, ?_, ?_⟩
    · rw [hu1]; exact hlab u hu
    · rw [hu1, hlab', htbl₁ t ht, hrt']
  · rw [hlo a (by omega)]; exact hm1lo a ha
  · rw [hfr₁ a (Or.inr (by unfold rootTblSpace at ha; rw [hdg] at ha; omega))]
    exact hrootOf3 a (by unfold rootTblSpace at ha; rw [hdg] at ha; omega)
  · simp only [initGraphFromExportContract, argsSize_cons, argsSize_nil, Expr.size_reg,
      Expr.size_const, Expr.size_bin, rootTblCost]
    omega

end MinCostFlow.SparseCore.Program
