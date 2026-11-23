module

public import MinCostFlow.HierPaths.Chain
public import MinCostFlow.HierPaths.BoundsProg
public import MinCostFlow.HierPaths.Layout

/-!
# The implementation from its three procedures

`DSRep.Implements` has three parts: `Local`, the clause of the initialization, and one clause for
each operation. Here each clause is a `Prop` of its own (`InitClause`, `OpClause`), so that the
three procedures of the path data structure (`Init`, `Delete`, `GetPath`) can be proved apart.

A procedure (`HierProc`) is an entry body `entry k` and a list of helper bodies `helpers k`, both
given the index `k` where the helpers start, so that the entry can call them. `HierProc.At p j k`
says that the entry is at index `j` of the program `p` and the helpers at `k, k + 1, …`.

The constants of `hierParams` are bundled as `HierConsts a`. The three specifications
`InitProcSpec`, `DelProcSpec` and `QueryProcSpec` say that the procedure is deterministic and
that it meets its clause for `hierRep a` and `pathDSDataStructure c.params w`, for all
`c : HierConsts a` whose constant and space function of this operation are the given ones and
whose word constant `cw` is at least the given `cw₀`. The other fields of `c` do not enter the
clause of the operation. The space function must have the polynomial form that `hierParams`
asks for (`SpaceForm`).

`hierPathDSExists_of_procs` puts the three procedures at the start of the program
(`hierProcs`), with `boundsProcs := gammaBoundsProcs a`, and proves `HierPathDSExists`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner

/-! ### The clauses of `DSRep.Implements` -/

/-- The clause of the initialization in `DSRep.Implements`, for the body at index `j`. -/
def InitClause {σ : Type} (R : DSRep σ) (w : ℕ) (p : Program) (j : ℕ)
    (D : DataStructure σ) : Prop :=
  ∀ args mem pos ω, (∀ a ∈ args, a < 2 ^ w) → D.initPre args mem →
    ZeroFrom mem (heapArg args) → heapArg args + D.initSpace args mem < 2 ^ w →
    ∃ body, p.procs[j]? = some body ∧ ∃ o st' c,
      Runs w p ω body (startState args mem pos) o st' c ∧ ∃ s' x',
        R.rep (heapArg args) s' x' st'.mem ∧ D.initPost args mem s' st'.mem ∧
        R.Respects (fun _ => False) (heapArg args) (D.initSpace args mem) mem o.value
          (heapArg args) x' st'.mem ∧
        c + R.phi (heapArg args) x' st'.mem ≤ D.initCost args mem

/-- The clause of operation `i` in `DSRep.Implements`, for the body at index `j`. -/
def OpClause {σ : Type} (R : DSRep σ) (w : ℕ) (p : Program) (i j : ℕ)
    (D : DataStructure σ) : Prop :=
  ∀ b s x args mem pos ω, (∀ a ∈ args, a < 2 ^ w) → args.head? = some b →
    R.rep b s x mem → D.pre i s args mem → (∀ a, R.foot b x a → a < heapArg args) →
    ZeroFrom mem (heapArg args) → heapArg args + D.space i s args mem < 2 ^ w →
    ∃ body, p.procs[j]? = some body ∧ ∃ o st' c,
      Runs w p ω body (startState args mem pos) o st' c ∧ ∃ s' x',
        R.rep b s' x' st'.mem ∧ D.post i s args mem s' st'.mem ∧
        R.Respects (R.foot b x) (heapArg args) (D.space i s args mem) mem o.value b x'
          st'.mem ∧
        c + R.phi b x' st'.mem ≤ D.cost i s args mem + R.phi b x mem

/-- `DSRep.Implements` is `Local` together with the clauses. -/
theorem implements_of_clauses {σ : Type} {R : DSRep σ} {w : ℕ} {p : Program} {init : ℕ}
    {op : ℕ → ℕ} {D : DataStructure σ} (hloc : R.Local) (hinit : InitClause R w p init D)
    (hop : ∀ i, OpClause R w p i (op i) D) : R.Implements w p init op D :=
  ⟨hloc, hinit, fun i => hop i⟩

/-! ### The constants of `hierParams` -/

/-- The polynomial form of a space function that `hierParams` asks for. -/
def SpaceForm (a : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (C c : ℕ) : Prop :=
  ∀ phiNum phiDen n m M, 1 ≤ phiNum → phiNum ≤ phiDen →
    f phiNum phiDen n m M ≤
      C * (phiDen + n + m + M + gammaHP a ((phiDen + phiNum - 1) / phiNum) M + 2) ^ c

/-- A larger constant and a larger exponent keep the form. -/
theorem SpaceForm.mono {a : ℕ} {f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {C c C' c' : ℕ}
    (h : SpaceForm a f C c) (hC : C ≤ C') (hc : c ≤ c') : SpaceForm a f C' c' := by
  intro phiNum phiDen n m M h1 h2
  refine le_trans (h phiNum phiDen n m M h1 h2) (Nat.mul_le_mul hC ?_)
  exact Nat.pow_le_pow_right (by omega) hc

/-- The arguments of `hierParams` other than `a`. -/
structure HierConsts (a : ℕ) where
  K_init : ℝ
  K_del : ℝ
  K_query : ℝ
  hK_init : 0 ≤ K_init
  hK_del : 0 ≤ K_del
  hK_query : 0 ≤ K_query
  K_bounds : ℕ
  cw : ℕ
  hcw_pos : 1 ≤ cw
  boundsSpace : ℕ → ℕ → ℕ
  initSpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  delSpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  querySpace : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  C_space : ℕ
  c_space : ℕ
  hC_space : 1 ≤ C_space
  hb : ∀ d M, boundsSpace d M ≤ C_space * (d + M + 2) ^ c_space
  hi : SpaceForm a initSpace C_space c_space
  hd : SpaceForm a delSpace C_space c_space
  hq : SpaceForm a querySpace C_space c_space

/-- The parameters `hierParams a …` with the constants `c`. -/
def HierConsts.params {a : ℕ} (c : HierConsts a) : PathDSParams :=
  hierParams a c.K_init c.K_del c.K_query c.hK_init c.hK_del c.hK_query c.K_bounds c.cw
    c.hcw_pos c.boundsSpace c.initSpace c.delSpace c.querySpace c.C_space c.c_space c.hC_space
    c.hb c.hi c.hd c.hq

/-! ### Procedures and their specifications -/

/-- A procedure: an entry body and helper bodies, given the index where the helpers start. -/
structure HierProc where
  entry : ℕ → Stmt
  helpers : ℕ → List Stmt

/-- The entry of `P` is at index `j` of `p`, and its helpers are at `k, k + 1, …`. -/
def HierProc.At (P : HierProc) (p : Program) (j k : ℕ) : Prop :=
  p.procs[j]? = some (P.entry k) ∧ p.HasAt k (P.helpers k)

/-- All bodies of `P` are deterministic. -/
def HierProc.NoRand (P : HierProc) : Prop :=
  ∀ k, (P.entry k).NoRand ∧ ∀ s ∈ P.helpers k, s.NoRand

/-- The specification of the `Init` procedure: deterministic, and the clause of the
initialization for every `c` with `K_init = K`, `initSpace = space` and `cw₀ ≤ cw`. -/
def InitProcSpec (a : ℕ) (P : HierProc) (K : ℝ) (space : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (C c cw₀ : ℕ) : Prop :=
  P.NoRand ∧ 0 ≤ K ∧ SpaceForm a space C c ∧
    ∀ hc : HierConsts a, hc.K_init = K → hc.initSpace = space → cw₀ ≤ hc.cw →
      ∀ w p j k, P.At p j k → InitClause (hierRep a) w p j (pathDSDataStructure hc.params w)

/-- The specification of the `Delete` procedure (operation `0`): deterministic, and its clause
for every `c` with `K_del = K`, `delSpace = space` and `cw₀ ≤ cw`. -/
def DelProcSpec (a : ℕ) (P : HierProc) (K : ℝ) (space : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (C c cw₀ : ℕ) : Prop :=
  P.NoRand ∧ 0 ≤ K ∧ SpaceForm a space C c ∧
    ∀ hc : HierConsts a, hc.K_del = K → hc.delSpace = space → cw₀ ≤ hc.cw →
      ∀ w p j k, P.At p j k → OpClause (hierRep a) w p 0 j (pathDSDataStructure hc.params w)

/-- The specification of the `GetPath` procedure (operation `1`): deterministic, and its clause
for every `c` with `K_query = K`, `querySpace = space` and `cw₀ ≤ cw`. -/
def QueryProcSpec (a : ℕ) (P : HierProc) (K : ℝ) (space : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (C c cw₀ : ℕ) : Prop :=
  P.NoRand ∧ 0 ≤ K ∧ SpaceForm a space C c ∧
    ∀ hc : HierConsts a, hc.K_query = K → hc.querySpace = space → cw₀ ≤ hc.cw →
      ∀ w p j k, P.At p j k → OpClause (hierRep a) w p 1 j (pathDSDataStructure hc.params w)

/-! ### The assembly -/

/-- The bodies of the implementation at base `b`: the three entries at `b`, `b + 1`, `b + 2`,
then the helpers of `PI`, `PD` and `PQ`, in this order. -/
def hierProcs (PI PD PQ : HierProc) (b : ℕ) : List Stmt :=
  let kI := b + 3
  let kD := kI + (PI.helpers kI).length
  let kQ := kD + (PD.helpers kD).length
  [PI.entry kI, PD.entry kD, PQ.entry kQ] ++ PI.helpers kI ++ PD.helpers kD ++ PQ.helpers kQ

/-- A program that has `l₁ ++ l₂` at `b` has `l₂` at `b + l₁.length`. -/
theorem hasAt_append_right {p : Program} {b : ℕ} {l₁ l₂ : List Stmt}
    (h : p.HasAt b (l₁ ++ l₂)) : p.HasAt (b + l₁.length) l₂ := by
  intro i hi
  have := h (l₁.length + i) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.add_assoc] using this

/-- A program that has `l₁ ++ l₂` at `b` has `l₁` at `b`. -/
theorem hasAt_append_left {p : Program} {b : ℕ} {l₁ l₂ : List Stmt}
    (h : p.HasAt b (l₁ ++ l₂)) : p.HasAt b l₁ := by
  intro i hi
  have := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at this

/-- Where the three procedures sit in a program that has `hierProcs PI PD PQ b` at `b`. -/
theorem hierProcs_at {PI PD PQ : HierProc} {p : Program} {b : ℕ}
    (hp : p.HasAt b (hierProcs PI PD PQ b)) :
    PI.At p b (b + 3) ∧
    PD.At p (b + 1) (b + 3 + (PI.helpers (b + 3)).length) ∧
    PQ.At p (b + 2) (b + 3 + (PI.helpers (b + 3)).length +
      (PD.helpers (b + 3 + (PI.helpers (b + 3)).length)).length) := by
  unfold hierProcs at hp
  have h3 := hasAt_append_left (hasAt_append_left (hasAt_append_left hp))
  have hI := hasAt_append_right (hasAt_append_left (hasAt_append_left hp))
  have hD := hasAt_append_right (hasAt_append_left hp)
  have hQ := hasAt_append_right hp
  simp only [List.length_append, List.length_cons, List.length_nil] at hI hD hQ
  refine ⟨⟨by simpa using h3 0 (by simp), by simpa [Nat.add_comm] using hI⟩,
    ⟨by simpa using h3 1 (by simp), ?_⟩, ⟨by simpa using h3 2 (by simp), ?_⟩⟩
  · convert hD using 1; omega
  · convert hQ using 1; omega

/-- The constants of the assembly, from those of the three procedures: `cw` is the largest
`cw₀` (and at least `3`), `K_bounds = 1000`, `boundsSpace = 3`, and the space form takes the
largest constant (and at least `3`) and the largest exponent. -/
def assembleConsts (a : ℕ) (KI KD KQ : ℝ) (hKI : 0 ≤ KI) (hKD : 0 ≤ KD) (hKQ : 0 ≤ KQ)
    (sI sD sQ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (CI cI CD cD CQ cQ cwI cwD cwQ : ℕ)
    (hI : SpaceForm a sI CI cI) (hD : SpaceForm a sD CD cD) (hQ : SpaceForm a sQ CQ cQ) :
    HierConsts a where
  K_init := KI
  K_del := KD
  K_query := KQ
  hK_init := hKI
  hK_del := hKD
  hK_query := hKQ
  K_bounds := 1000
  cw := max 3 (max cwI (max cwD cwQ))
  hcw_pos := le_trans (by norm_num) (le_max_left _ _)
  boundsSpace _ _ := 3
  initSpace := sI
  delSpace := sD
  querySpace := sQ
  C_space := max 3 (max CI (max CD CQ))
  c_space := max cI (max cD cQ)
  hC_space := le_trans (by norm_num) (le_max_left _ _)
  hb d M := by
    have h1 : 1 ≤ (d + M + 2) ^ max cI (max cD cQ) := Nat.one_le_pow _ _ (by omega)
    calc 3 ≤ max 3 (max CI (max CD CQ)) * 1 := by simp
      _ ≤ _ := Nat.mul_le_mul_left _ h1
  hi := hI.mono (by omega) (by omega)
  hd := hD.mono (by omega) (by omega)
  hq := hQ.mono (by omega) (by omega)

/-- **The implementation from its three procedures.** For every `a ≥ 1`, procedures meeting
`InitProcSpec`, `DelProcSpec` and `QueryProcSpec` give `HierPathDSExists`. The representation
is `hierRep a`, local by `hierRep_local`, and the parameter evaluator is `gammaBoundsProcs a`. -/
theorem hierPathDSExists_of_procs
    (h : ∀ a : ℕ, 1 ≤ a → ∃ (PI PD PQ : HierProc) (KI KD KQ : ℝ)
      (sI sD sQ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (CI cI CD cD CQ cQ cwI cwD cwQ : ℕ),
      InitProcSpec a PI KI sI CI cI cwI ∧ DelProcSpec a PD KD sD CD cD cwD ∧
        QueryProcSpec a PQ KQ sQ CQ cQ cwQ) :
    HierPathDSExists := by
  intro a ha
  obtain ⟨PI, PD, PQ, KI, KD, KQ, sI, sD, sQ, CI, cI, CD, cD, CQ, cQ, cwI, cwD, cwQ,
    ⟨hnrI, hKI, hfI, hspecI⟩, ⟨hnrD, hKD, hfD, hspecD⟩, ⟨hnrQ, hKQ, hfQ, hspecQ⟩⟩ := h a ha
  let hc := assembleConsts a KI KD KQ hKI hKD hKQ sI sD sQ CI cI CD cD CQ cQ cwI cwD cwQ hfI hfD hfQ
  have hcwI : cwI ≤ hc.cw := by simp only [hc, assembleConsts]; omega
  have hcwD : cwD ≤ hc.cw := by simp only [hc, assembleConsts]; omega
  have hcwQ : cwQ ≤ hc.cw := by simp only [hc, assembleConsts]; omega
  have hcw3 : 3 ≤ hc.cw := by simp only [hc, assembleConsts]; omega
  let impl : PathDSImpl :=
    { params := hc.params
      R := hierRep a
      procs := hierProcs PI PD PQ
      hprocs_len := fun b => by simp [hierProcs]
      spec := fun w p b hp => by
        obtain ⟨hI, hD, hQ⟩ := hierProcs_at hp
        refine implements_of_clauses (hierRep_local a)
          (hspecI hc rfl rfl hcwI w p b _ hI) (fun i => ?_)
        match i with
        | 0 => exact hspecD hc rfl rfl hcwD w p (b + 1) _ hD
        | 1 => exact hspecQ hc rfl rfl hcwQ w p (b + 2) _ hQ
        | i + 2 =>
          intro _ _ _ _ _ _ _ _ _ _ hpre
          exact hpre.elim
      boundsProcs := fun _ => gammaBoundsProcs a
      hbounds_nonempty := fun _ => gammaBoundsProcs_nonempty a
      hbounds_noRand := fun _ => gammaBoundsProcs_noRand a
      boundsSpec := fun w p bB hp =>
        hierParams_boundsSpec a hcw3 (le_refl 1000) (fun _ _ => le_refl 3) w p bB hp }
  refine ⟨hc.K_init, hc.K_del, hc.K_query, hc.hK_init, hc.hK_del, hc.hK_query, hc.K_bounds,
    hc.cw, hc.hcw_pos, hc.boundsSpace, hc.initSpace, hc.delSpace, hc.querySpace, hc.C_space,
    hc.c_space, hc.hC_space, hc.hb, hc.hi, hc.hd, hc.hq, impl, rfl, fun b s hs => ?_⟩
  simp only [impl, hierProcs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with (((rfl | rfl | rfl) | hs) | hs) | hs
  · exact (hnrI _).1
  · exact (hnrD _).1
  · exact (hnrQ _).1
  · exact (hnrI _).2 s hs
  · exact (hnrD _).2 s hs
  · exact (hnrQ _).2 s hs

end MinCostFlow.HierPaths
