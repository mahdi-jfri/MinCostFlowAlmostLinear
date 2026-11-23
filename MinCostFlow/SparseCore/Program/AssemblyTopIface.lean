module

public import MinCostFlow.SparseCore.Program.AssemblyModel
public import MinCostFlow.SparseCore.Program.AssemblyInputInv
public import MinCostFlow.SparseCore.Program.AssemblyReemb
public import MinCostFlow.SparseCore.Program.AssemblyCompactOrd
public import MinCostFlow.SparseCore.Program.AssemblyEmpty
public import MinCostFlow.SparseCore.Program.OrdStoreImplements
public import MinCostFlow.SparseCore.Program.ReadSpec
public import MinCostFlow.SparseCore.Program.OrdEditsBlocks
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitLengths
public import MinCostFlow.SparseCore.Program.CompSplitListModel
public import MinCostFlow.Expander.Section8Asymptotics

/-!
# Top-layer interfaces and representation for the sparse-core program (`AssemblyTopIface`)

The sparse-core program (`SparseCoreOrdProgramUniform`, Lemma 5.17, page 23, with the bundle
repair described in the README) is assembled in two layers:
* **Top layer** (`AssemblyTop*.lean`): owns the
  20-word header (including a 4-word `emptyGraph` block), the order store **P1** (using the
  `ordStore_implements_cap` theorem), the linear-time order compactor
  (`AssemblyCompactOrd.lean`), the empty-graph fast path (`AssemblyEmpty.lean`), the component-LSF
  family **P4** (`AsmCompFamilyAt`), and a `k`-entry table of independent branch modules
  (`AsmBranchAt`).
* **Branch layer** (`AssemblyBranch*.lean`): builds `AsmBranchAt` from P2, P5, P6 (real
  `bucketSpannerDS_implements`), P7, P8 (real `restartBranch_runs`), and P10.

This file defines:
* `PolyBound`: input-independent polynomial space bounds `coeff * (x + 2) ^ deg` with monotonicity
  and composition lemmas.
* `AsmCompFamilyAt`: interface of P4 (`compLSFDS` + per-branch forest-change output of `op 0`).
* `AsmBranchAt`: interface of one branch `j < k` (`init`, `step`, `restart`, readouts `2`–`5`).
* Header offsets (`ASM_HDR_*`), the top-layer concrete state `AsmTopMeta`, the representation
  `asmTopRep`, and its locality theorem `asmTopRep_local`.

Note that `asmTopRep` depends only on the tool `T` (and the CF/BR representations), never on
`G, k, M, N, vCap, eCap`. When the LSF initializer ignores the limb count `L`, `asmTopRep` is also
independent of `L`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.LSF

/-! ## Polynomial space bounds and top-layer header offsets -/

/-- An input-independent polynomial upper bound `coeff * (x + 2) ^ deg`. -/
structure PolyBound where
  coeff : ℕ
  deg : ℕ

/-- Evaluate a polynomial bound at `x`. -/
def PolyBound.eval (pb : PolyBound) (x : ℕ) : ℕ := pb.coeff * (x + 2) ^ pb.deg

theorem PolyBound.eval_mono (pb : PolyBound) {a b : ℕ} (h : a ≤ b) :
    pb.eval a ≤ pb.eval b := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) pb.deg)

def ASM_HDR_NE : ℕ := 0
def ASM_HDR_K : ℕ := 1
def ASM_HDR_M : ℕ := 2
def ASM_HDR_N : ℕ := 3
def ASM_HDR_VCAP : ℕ := 4
def ASM_HDR_ECAP : ℕ := 5
def ASM_HDR_L : ℕ := 6
def ASM_HDR_PFP : ℕ := 7
def ASM_HDR_ORDH : ℕ := 8
def ASM_HDR_CFH : ℕ := 9
def ASM_HDR_TBL : ℕ := 10
def ASM_HDR_EMPTYG : ℕ := 16
def ASM_HDR_SIZE : ℕ := 20

/-! ## Component-LSF family interface (P4) -/

/-- Abstract state of a component-LSF family for `k` branches (the `cs` fields of the branches). -/
abbrev CompFamilyAbs := ℕ → CompLSFState

/-- Input-independent cost and space parameters of the component-LSF family (P4).
`wordExp` depends ONLY on `capExp` (never on `limbMul`); `mul` may depend on both. -/
structure AsmCompFamilySpec where
  /-- Cost multiplier (may depend on `capExp` and `limbMul`, free of the input). -/
  mul : ℕ → ℕ → ℕ
  /-- Constant cost of one forest-root query (`op 3`, may depend on `capExp`). -/
  rootCost : ℕ → ℕ
  /-- Minimum word-size exponent required by P4 (depends ONLY on `capExp`, never on `limbMul`). -/
  wordExp : ℕ → ℕ
  /-- Space bound of `init` as a polynomial in `vCap + eCap + L + k`. -/
  initSpace : ℕ → PolyBound
  /-- Space bound of `batch` as a polynomial in `vCap + eCap + L + k + words`. -/
  batchSpace : ℕ → PolyBound
  /-- Space bound of single-branch `export` as a polynomial in `M + N + k + vCap + eCap + L`. -/
  exportSpace : ℕ → PolyBound

/-- Concrete memory layout of P4's per-branch forest-change records (piece P4, `CompContract.lean`,
and piece P10, `ReadSpec.lean`):
* `[fChgPtr, fChgPtr + k)` is a table of `k` pointers `chgPtr_j = mem (fChgPtr + j)`;
* for each `j < k`, `chgPtr_j` holds `Read.LSFChangeAt mem chgPtr_j (chg j)` with
  `(chg j).Exact (cfs j).lsf (compLSFBatch (cfs j) U).lsf`;
* the pointer table and every change record lie inside `[fChgPtr, fChgEnd)` and every word in
  `[fChgPtr, fChgEnd)` is `< 2 ^ w`. -/
def CompFamilyChgAt (w k : ℕ) (mem : ℕ → ℕ) (fChgPtr fChgEnd : ℕ)
    (cfs : CompFamilyAbs) (U : List Update) : Prop :=
  fChgPtr + k ≤ fChgEnd ∧
  (∀ a, fChgPtr ≤ a → a < fChgEnd → mem a < 2 ^ w) ∧
  ∃ chg : ℕ → Read.LSFChange, ∀ j < k,
    let chgPtr := mem (fChgPtr + j)
    Read.LSFChangeAt mem chgPtr (chg j) ∧
    (chg j).Exact (cfs j).lsf (compLSFBatch (cfs j) U).lsf ∧
    fChgPtr + k ≤ chgPtr ∧
    chgPtr + (chg j).words ≤ fChgEnd

/-- `CompFamilyChgAt` depends only on memory inside `[fChgPtr, fChgEnd)`. -/
theorem compFamilyChgAt_congr {w k : ℕ} {mem₁ mem₂ : ℕ → ℕ} {fChgPtr fChgEnd : ℕ}
    {cfs : CompFamilyAbs} {U : List Update}
    (hag : ∀ a, fChgPtr ≤ a → a < fChgEnd → mem₁ a = mem₂ a)
    (h : CompFamilyChgAt w k mem₁ fChgPtr fChgEnd cfs U) :
    CompFamilyChgAt w k mem₂ fChgPtr fChgEnd cfs U := by
  rcases h with ⟨hlo, hlt, chg, hchg⟩
  refine ⟨hlo, fun a ha1 ha2 => by rw [← hag a ha1 ha2]; exact hlt a ha1 ha2, chg, fun j hj => ?_⟩
  obtain ⟨hAt, hEx, hptrLo, hptrHi⟩ := hchg j hj
  have hptr_eq : mem₂ (fChgPtr + j) = mem₁ (fChgPtr + j) := (hag (fChgPtr + j) (by omega) (by omega)).symm
  dsimp only
  rw [hptr_eq]
  set p := mem₁ (fChgPtr + j)
  rcases hAt with ⟨hr0, hrL, hf0, hfL⟩
  have hw_def : (chg j).words = 2 + ((chg j).roots.length + (chg j).fDel.length) := rfl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hEx, hptrLo, hptrHi⟩
  · exact (hag p (by omega) (by omega)).symm.trans hr0
  · exact listAt_of_agree hrL fun x hx1 hx2 => (hag x (by omega) (by omega)).symm
  · exact (hag (p + 1 + (chg j).roots.length) (by omega) (by omega)).symm.trans hf0
  · exact listAt_of_agree hfL fun x hx1 hx2 => (hag x (by omega) (by omega)).symm

private theorem readTriples_of_agree {mem₁ mem₂ : ℕ → ℕ} {a n : ℕ}
    (h : ∀ x, a ≤ x → x < a + 3 * n → mem₂ x = mem₁ x) :
    readTriples mem₂ a n = readTriples mem₁ a n :=
  List.map_congr_left fun i hi => by
    have hilt := List.mem_range.mp hi
    rw [h (a + 3 * i) (by omega) (by omega), h (a + 3 * i + 1) (by omega) (by omega),
      h (a + 3 * i + 2) (by omega) (by omega)]

private theorem exportAt_congr {mem₁ mem₂ : ℕ → ℕ} {d hEnd : ℕ} {G : MGraph}
    (hag : ∀ a, d ≤ a → a < hEnd → mem₁ a = mem₂ a)
    (h : Restart.ExportAt mem₁ d hEnd G) :
    Restart.ExportAt mem₂ d hEnd G := by
  rcases h with ⟨h0, h2, hndV, hV, hndE, hE1, hE2, hd4, hvLo, heLo, hvHi, heHi⟩
  have hm0 : mem₂ d = mem₁ d := (hag d le_rfl (by omega)).symm
  have hm1 : mem₂ (d + 1) = mem₁ (d + 1) := (hag (d + 1) (by omega) (by omega)).symm
  have hm2 : mem₂ (d + 2) = mem₁ (d + 2) := (hag (d + 2) (by omega) (by omega)).symm
  have hm3 : mem₂ (d + 3) = mem₁ (d + 3) := (hag (d + 3) (by omega) (by omega)).symm
  have hvL : readList mem₂ (mem₂ (d + 1)) (mem₂ d) = readList mem₁ (mem₁ (d + 1)) (mem₁ d) := by
    rw [hm1, hm0]
    exact readList_of_agree fun x hx1 hx2 => (hag x (by omega) (by omega)).symm
  have heT : readTriples mem₂ (mem₂ (d + 3)) (mem₂ (d + 2)) =
      readTriples mem₁ (mem₁ (d + 3)) (mem₁ (d + 2)) := by
    rw [hm3, hm2]
    exact readTriples_of_agree fun x hx1 hx2 => (hag x (by omega) (by omega)).symm
  refine ⟨hm0.trans h0, hm2.trans h2, hvL ▸ hndV, ?_, heT ▸ hndE, ?_, ?_, hd4,
    by omega, by omega, by omega, by omega⟩
  · intro v; rw [hvL]; exact hV v
  · intro t ht; rw [heT] at ht; exact hE1 t ht
  · intro e he; rw [heT]; exact hE2 e he

/-- Concrete memory layout of P4's single-branch export (`CF.export_runs`) in the `ExportAt` /
`ReadInitAt` form consumed by P10's initialization (`ReadSpec.lean`):
* `[expPtr, expPtr + 8)` is an 8-word header `[tD, fD, rootsPtr, nR, numPtr, denPtr, L_w, tCap]`;
* all exported payloads lie inside `[expPtr + 8, expEnd)` and every word in `[expPtr, expEnd)` is
  `< 2 ^ w`;
* `tD` and `fD` hold `ExportAt` of `cs.lsf.T` and `cs.lsf.F.F`;
* `rootsPtr` holds a duplicate-free list of length `nR` enumerating `cs.lsf.F.R`;
* `L_w` satisfies `1 ≤ L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)`;
* `tCap` satisfies `eCap ≤ tCap ≤ 2 * (vCap + eCap + 2) ^ 2` and bounds every edge ID of `cs.lsf.T`;
* `numPtr` and `denPtr` hold valid `4`-bit, `L_w`-limb signed-integer tables at stride `L_w` for
  every `e ∈ cs.G.E` with `0 < den e` and `(num e : ℝ) / (den e : ℝ) = cs.lsf.wstr e`. -/
def CompBranchExportAt (w : ℕ) (mem : ℕ → ℕ) (expPtr expEnd L capExp M N vCap eCap : ℕ)
    (cs : CompLSFState) : Prop :=
  let tD := mem expPtr
  let fD := mem (expPtr + 1)
  let rootsPtr := mem (expPtr + 2)
  let nR := mem (expPtr + 3)
  let numPtr := mem (expPtr + 4)
  let denPtr := mem (expPtr + 5)
  let L_w := mem (expPtr + 6)
  let tCap := mem (expPtr + 7)
  expPtr + 8 ≤ expEnd ∧
  (∀ a, expPtr ≤ a → a < expEnd → mem a < 2 ^ w) ∧
  expPtr + 8 ≤ tD ∧ Restart.ExportAt mem tD expEnd cs.lsf.T ∧
  expPtr + 8 ≤ fD ∧ Restart.ExportAt mem fD expEnd cs.lsf.F.F ∧
  (∃ roots : List ℕ, roots.length = nR ∧ roots.Nodup ∧ roots.toFinset = cs.lsf.F.R ∧
    ListAt mem rootsPtr roots ∧ expPtr + 8 ≤ rootsPtr ∧ rootsPtr + nR ≤ expEnd) ∧
  1 ≤ L_w ∧ L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
  eCap ≤ tCap ∧ tCap ≤ 2 * (vCap + eCap + 2) ^ 2 ∧ (∀ e ∈ cs.lsf.T.E, e < tCap) ∧
  ∃ num den : ℕ → ℤ, ∀ e ∈ cs.G.E,
    expPtr + 8 ≤ numPtr + e * L_w ∧ numPtr + (e + 1) * L_w ≤ expEnd ∧
    expPtr + 8 ≤ denPtr + e * L_w ∧ denPtr + (e + 1) * L_w ≤ expEnd ∧
    Num.Valid mem (numPtr + e * L_w) 4 L_w ∧ Num.Valid mem (denPtr + e * L_w) 4 L_w ∧
    Num.intVal mem (numPtr + e * L_w) 4 L_w = num e ∧
    Num.intVal mem (denPtr + e * L_w) 4 L_w = den e ∧
    0 < den e ∧ (num e : ℝ) / (den e : ℝ) = cs.lsf.wstr e

/-- `CompBranchExportAt` depends only on memory inside `[expPtr, expEnd)`. -/
theorem compBranchExportAt_congr {w : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    {expPtr expEnd L capExp M N vCap eCap : ℕ} {cs : CompLSFState}
    (hag : ∀ a, expPtr ≤ a → a < expEnd → mem₁ a = mem₂ a)
    (h : CompBranchExportAt w mem₁ expPtr expEnd L capExp M N vCap eCap cs) :
    CompBranchExportAt w mem₂ expPtr expEnd L capExp M N vCap eCap cs := by
  rcases h with ⟨h8, hlt, htLo, htEx, hfLo, hfEx, ⟨roots, hrLen, hrNd, hrFs, hrLA, hrLo, hrHi⟩,
    hLw1, hLwHi, htCapLo, htCapHi, htE, num, den, hnd⟩
  have hhdr : ∀ i < 8, mem₂ (expPtr + i) = mem₁ (expPtr + i) := fun i hi =>
    (hag (expPtr + i) (by omega) (by omega)).symm
  have h0 : mem₂ expPtr = mem₁ expPtr := by simpa using hhdr 0 (by omega)
  dsimp only [CompBranchExportAt]
  rw [h0, hhdr 1 (by omega), hhdr 2 (by omega), hhdr 3 (by omega),
    hhdr 4 (by omega), hhdr 5 (by omega), hhdr 6 (by omega), hhdr 7 (by omega)]
  refine ⟨h8, fun a ha1 ha2 => by rw [← hag a ha1 ha2]; exact hlt a ha1 ha2,
    htLo, exportAt_congr (fun a ha1 ha2 => hag a (by omega) ha2) htEx,
    hfLo, exportAt_congr (fun a ha1 ha2 => hag a (by omega) ha2) hfEx,
    ⟨roots, hrLen, hrNd, hrFs,
      listAt_of_agree hrLA fun a ha1 ha2 => (hag a (by omega) (by omega)).symm, hrLo, hrHi⟩,
    hLw1, hLwHi, htCapLo, htCapHi, htE, num, den, fun e he => ?_⟩
  obtain ⟨hnLo, hnHi, hdLo, hdHi, hnV, hdV, hnEq, hdEq, hdPos, hrat⟩ := hnd e he
  have hmul : (e + 1) * mem₁ (expPtr + 6) = e * mem₁ (expPtr + 6) + mem₁ (expPtr + 6) :=
    Nat.add_one_mul e _
  have hnum_ag : ∀ i < mem₁ (expPtr + 6),
      mem₂ (mem₁ (expPtr + 4) + e * mem₁ (expPtr + 6) + i) =
      mem₁ (mem₁ (expPtr + 4) + e * mem₁ (expPtr + 6) + i) := fun i hi =>
    (hag _ (by omega) (by omega)).symm
  have hden_ag : ∀ i < mem₁ (expPtr + 6),
      mem₂ (mem₁ (expPtr + 5) + e * mem₁ (expPtr + 6) + i) =
      mem₁ (mem₁ (expPtr + 5) + e * mem₁ (expPtr + 6) + i) := fun i hi =>
    (hag _ (by omega) (by omega)).symm
  exact ⟨hnLo, hnHi, hdLo, hdHi, fun i hi => by rw [hnum_ag i hi]; exact hnV i hi,
    fun i hi => by rw [hden_ag i hi]; exact hdV i hi,
    by rw [Num.intVal_congr hnum_ag]; exact hnEq,
    by rw [Num.intVal_congr hden_ag]; exact hdEq, hdPos, hrat⟩

/-- **Interface of P4 (`CompContract.lean` + forest changes + root query + branch export).**
Provides `init` (`[graph, lengths, L, P_fp, k, vCap, eCap, h]`), `batch`
(`[cfH, batch, words, h]`, writing at `h` the pointer `fChgPtr` to the concrete `k`-pointer
forest-change table `CompFamilyChgAt`), `fRoot` (operation `3` of `compLSFDS`, exporting
`Read.RootQueryAt` on `rep`), and `fExport` (single-branch export `[cfH, j, h]` in the
`CompBranchExportAt` / `ExportAt` / `ReadInitAt` layout). -/
structure AsmCompFamilyAt (S : AsmCompFamilySpec) (lsfInit : LSFInit) (w : ℕ)
    (fmt : Num.Format w) (L capExp limbMul : ℕ) (p : Program) (fInit fBatch : ℕ) where
  rep : DSRep CompFamilyAbs
  rep_local : rep.Local
  /-- Vertex and edge capacities pinned by the concrete state at `init`. -/
  vCapOf : rep.τ → ℕ
  eCapOf : rep.τ → ℕ
  /-- Procedure index of P4's forest-root query (operation `3` of `compLSFDS`). -/
  fRoot : ℕ
  /-- Procedure index of P4's single-branch export (`[cfH, j, h]`) for P10's initialization. -/
  fExport : ℕ
  /-- `init` creates `fun j => initCompLSFWith lsfInit G ℓ₀ k j` at handle `h`. -/
  init_runs : ∀ (graph lengths k M N vCap eCap h : ℕ) (G : MGraph) (mem : ℕ → ℕ)
      (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → 0 < k → G.IsValid → G.V.Nonempty → G.m ≤ M → G.n ≤ N →
      CompInitFormatHyp L fmt.precision k G.m → k ≤ (M + N + 2) ^ capExp →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      (M + N + 2) ^ S.wordExp capExp * (L + 1) < 2 ^ w →
      DynGraphAt mem graph vCap eCap G →
      graph + dynGraphSize vCap eCap ≤ h → lengths + eCap * L ≤ h →
      (∀ e ∈ G.E, e < eCap ∧ Num.Valid mem (lengths + e * L) 4 L ∧
        0 < readEdgeValues mem lengths 4 L fmt.precision G.E e) →
      (∀ a ∈ [graph, lengths, L, fmt.precision, k, vCap, eCap, h], a < 2 ^ w) →
      ZeroFrom mem h →
      h + (S.initSpace capExp).eval (vCap + eCap + L + k) < 2 ^ w →
      let ℓ₀ := readEdgeValues mem lengths 4 L fmt.precision G.E
      let cfs₀ : CompFamilyAbs := fun j => initCompLSFWith lsfInit G ℓ₀ k j
      ∃ body, p.procs[fInit]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [graph, lengths, L, fmt.precision, k, vCap, eCap, h] mem pos)
          o st' c ∧
        rep.rep h cfs₀ x' st'.mem ∧ vCapOf x' = vCap ∧ eCapOf x' = eCap ∧
        rep.Respects (fun _ => False) h ((S.initSpace capExp).eval (vCap + eCap + L + k))
          mem o.value h x' st'.mem ∧
        c + rep.phi h x' st'.mem ≤
          S.mul capExp limbMul * (G.n + G.m + 1 + k * lsfInitSize G * bundleLogFactor M N ^ 3)
  /-- `batch` advances every branch `j < k` by `compLSFBatch` and writes the forest-change table
  pointer at `h` (`st'.mem h = fChgPtr` with `h ≤ fChgPtr ≤ o.value`, concrete records satisfying
  `CompFamilyChgAt w k st'.mem fChgPtr o.value cfs U`). -/
  batch_runs : ∀ (cfH batch words k M N vCap eCap h : ℕ) (cfs : CompFamilyAbs) (x : rep.τ)
      (U : List Update) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → 0 < k → k = (cfs 0).k → k ≤ (M + N + 2) ^ capExp → (cfs 0).G₀.n ≤ N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      (M + N + 2) ^ S.wordExp capExp * (L + 1) < 2 ^ w →
      rep.rep cfH cfs x mem → vCapOf x = vCap → eCapOf x = eCap →
      (∀ j < k, (cfs j).G = (cfs 0).G) →
      SmallBatchAt mem batch (cfs 0).G U words →
      (cfs 0).G.BatchIsValid U → BatchWithinCaps vCap eCap U →
      (∀ i < words, mem (batch + i) < 2 ^ w) → batch + words ≤ h →
      (∀ a ∈ [cfH, batch, words, h], a < 2 ^ w) →
      (∀ a, rep.foot cfH x a → a < h) →
      ZeroFrom mem h →
      h + (S.batchSpace capExp).eval (vCap + eCap + L + k + words) < 2 ^ w →
      let cfs' : CompFamilyAbs := fun j => compLSFBatch (cfs j) U
      ∃ body, p.procs[fBatch]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [cfH, batch, words, h] mem pos) o st' c ∧
        rep.rep cfH cfs' x' st'.mem ∧ vCapOf x' = vCap ∧ eCapOf x' = eCap ∧
        h + 1 ≤ o.value ∧
        h ≤ st'.mem h ∧ st'.mem h ≤ o.value ∧
        CompFamilyChgAt w k st'.mem (st'.mem h) o.value cfs U ∧
        CompSplitListAt w k st'.mem (st'.mem h + k) o.value cfs U ∧
        rep.Respects (rep.foot cfH x) h
          ((S.batchSpace capExp).eval (vCap + eCap + L + k + words)) mem o.value cfH x' st'.mem ∧
        c + rep.phi cfH x' st'.mem ≤
          S.mul capExp limbMul * ((Finset.range k).sum (fun j => lsfBatchSize (cfs j) U) +
            (k + 1) * (words + 1)) * bundleLogFactor M N + rep.phi cfH x mem
  /-- Operation `3` of P4 (`[cfH, j, u, h]`): writes `(cfs j).RF.root u` at `h`, keeping `cfs`
  and costing at most `S.rootCost capExp`. -/
  root_runs : ∀ (cfH j u h k : ℕ) (cfs : CompFamilyAbs) (x : rep.τ)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      cfH < 2 ^ w → j < 2 ^ w → u < 2 ^ w → h < 2 ^ w →
      16 ≤ 2 ^ w → j < k → k = (cfs 0).k → u ∈ (cfs j).G.V →
      rep.rep cfH cfs x mem → (∀ a, rep.foot cfH x a → a < h) → ZeroFrom mem h → h + 1 < 2 ^ w →
      ∃ body, p.procs[fRoot]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [cfH, j, u, h] mem pos) o st' c ∧
        st'.mem h = (cfs j).RF.root u ∧ rep.rep cfH cfs x' st'.mem ∧
        vCapOf x' = vCapOf x ∧ eCapOf x' = eCapOf x ∧
        h ≤ o.value ∧ o.value ≤ h + 1 ∧ ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ rep.foot cfH x a → st'.mem a = mem a) ∧
        (∀ a, rep.foot cfH x' a → rep.foot cfH x a ∨ (h ≤ a ∧ a < o.value)) ∧
        c + rep.phi cfH x' st'.mem ≤ S.rootCost capExp + rep.phi cfH x mem
  /-- Single-branch export (`[cfH, j, h]`): writes the 8-word `CompBranchExportAt` header at `h`
  and all payloads (`T`, `F`, `roots`, `num`, `den`) inside `[h + 8, o.value)`, keeping `cfs`,
  allocating at most `(S.exportSpace capExp).eval (M + N + k + vCap + eCap + L)` words, and
  costing at most `S.mul capExp limbMul * (((cfs j).G.n + (cfs j).G.m + 1) * bundleLogFactor M N)`
  amortized against `rep.phi`. -/
  export_runs : ∀ (cfH j k M N vCap eCap h : ℕ) (cfs : CompFamilyAbs) (x : rep.τ)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → 0 < k → j < k → k = (cfs 0).k → k ≤ (M + N + 2) ^ capExp →
      (cfs j).G.m ≤ M → (cfs j).G.n ≤ N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      (M + N + 2) ^ S.wordExp capExp * (L + 1) < 2 ^ w →
      rep.rep cfH cfs x mem → vCapOf x = vCap → eCapOf x = eCap →
      (∀ a, rep.foot cfH x a → a < h) →
      (∀ a ∈ [cfH, j, h], a < 2 ^ w) →
      ZeroFrom mem h →
      h + (S.exportSpace capExp).eval (M + N + k + vCap + eCap + L) < 2 ^ w →
      ∃ body, p.procs[fExport]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [cfH, j, h] mem pos) o st' c ∧
        rep.rep cfH cfs x' st'.mem ∧ vCapOf x' = vCap ∧ eCapOf x' = eCap ∧
        CompBranchExportAt w st'.mem h o.value L capExp M N vCap eCap (cfs j) ∧
        rep.Respects (rep.foot cfH x) h
          ((S.exportSpace capExp).eval (M + N + k + vCap + eCap + L)) mem o.value cfH x' st'.mem ∧
        c + rep.phi cfH x' st'.mem ≤
          S.mul capExp limbMul * (((cfs j).G.n + (cfs j).G.m + 1) * bundleLogFactor M N) +
            rep.phi cfH x mem

/-- Package P4's root query (`CF.root_runs`, operation `3`) as a `Read.RootQueryAt w p CF.fRoot`
on `CF.rep`, for direct use by P10's restart (`ReadBranchAt.restart`). -/
noncomputable def AsmCompFamilyAt.toRootQueryAt {S : AsmCompFamilySpec} {lsfInit : LSFInit} {w : ℕ}
    {fmt : Num.Format w} {L capExp limbMul : ℕ} {p : Program} {fInit fBatch : ℕ}
    (CF : AsmCompFamilyAt S lsfInit w fmt L capExp limbMul p fInit fBatch) (k : ℕ) :
    Read.RootQueryAt w p CF.fRoot where
  σ := CompFamilyAbs
  R := CF.rep
  root cfs j u := (cfs j).RF.root u
  ok cfs j u := 16 ≤ 2 ^ w ∧ j < k ∧ k = (cfs 0).k ∧ u ∈ (cfs j).G.V
  cost := S.rootCost capExp
  R_local := CF.rep_local
  runs b j u h s x mem pos ω hb hj hu hh hok hrep hft hz hsp := by
    obtain ⟨body, hbody, o, st', c, x', h1, h2, h3, -, -, h4, h5, h6, h7, h8, h9⟩ :=
      CF.root_runs b j u h k s x mem pos ω hb hj hu hh hok.1 hok.2.1 hok.2.2.1 hok.2.2.2 hrep hft hz hsp
    exact ⟨body, hbody, o, st', c, x', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Restriction of `CF.rep` pinning `CF.vCapOf x = vCap` and `CF.eCapOf x = eCap` for P10's restart. -/
noncomputable def AsmCompFamilyAt.toRootQueryAtCaps {S : AsmCompFamilySpec} {lsfInit : LSFInit} {w : ℕ}
    {fmt : Num.Format w} {L capExp limbMul : ℕ} {p : Program} {fInit fBatch : ℕ}
    (CF : AsmCompFamilyAt S lsfInit w fmt L capExp limbMul p fInit fBatch) (k vCap eCap : ℕ) :
    Read.RootQueryAt w p CF.fRoot where
  σ := CompFamilyAbs
  R := ⟨CF.rep.τ, fun b s x mem => CF.rep.rep b s x mem ∧ CF.vCapOf x = vCap ∧ CF.eCapOf x = eCap,
    CF.rep.phi, CF.rep.foot⟩
  root cfs j u := (cfs j).RF.root u
  ok cfs j u := 16 ≤ 2 ^ w ∧ j < k ∧ k = (cfs 0).k ∧ u ∈ (cfs j).G.V
  cost := S.rootCost capExp
  R_local := fun b s x m1 m2 hag =>
    ⟨fun ⟨h1, h2, h3⟩ => ⟨(CF.rep_local b s x m1 m2 hag).1 h1, h2, h3⟩, (CF.rep_local b s x m1 m2 hag).2⟩
  runs b j u h s x mem pos ω hb hj hu hh hok hrep hft hz hsp := by
    obtain ⟨body, hbody, o, st', c, x', h1, h2, h3, hv', he', h4, h5, h6, h7, h8, h9⟩ :=
      CF.root_runs b j u h k s x mem pos ω hb hj hu hh hok.1 hok.2.1 hok.2.2.1 hok.2.2.2 hrep.1 hft hz hsp
    exact ⟨body, hbody, o, st', c, x', h1, h2, ⟨h3, hv'.trans hrep.2.1, he'.trans hrep.2.2⟩,
      h4, h5, h6, h7, h8, h9⟩

/-! ## Branch module interface (implemented in Layer 3 from P2, P5, P6, P7, P8, P10) -/

/-- Abstract state of a single branch `j < k` on a nonempty state: its `BundleTreeState depth`,
the current input order `ord`, and the vertex/edge capacity bounds `(vCap, eCap)` of the instance. -/
structure AsmBranchAbs (depth : ℕ) where
  tr : BundleTreeState depth
  ord : ℕ → List End
  vCap : ℕ
  eCap : ℕ

/-- Procedure indices for the 7 operations of a branch module. -/
structure AsmBranchProcs where
  fInit : ℕ
  fStep : ℕ
  fRestart : ℕ
  fReadLSF : ℕ
  fReadS : ℕ
  fReadEmb : ℕ
  fReadOrd : ℕ

/-- Input-independent cost and space parameters of the branch module.
`wordExp` depends ONLY on `capExp` (never on `limbMul`); `mul` may depend on both. -/
structure AsmBranchSpec where
  mul : ℕ → ℕ → ℕ
  readout : ℕ → ℕ
  wordExp : ℕ → ℕ
  initSpace : ℕ → PolyBound
  stepSpace : ℕ → PolyBound
  restartSpace : ℕ → PolyBound

/-- **Interface of one branch module `BR`** (built in Layer 3 from P2, P5, P6, P7, P8, P10).
The representation `rep : DSRep (AsmBranchAbs depth)` is uniform over `G, k, M, N, vCap, eCap`.
Parameter `wordExp` depends on `capExp` alone; the word condition `(M + N + 2) ^ S.wordExp capExp *
(L + 1) < 2 ^ w` covers the `(L + 1)` space factor without introducing `limbMul` into the exponent. -/
structure AsmBranchAt (S : AsmBranchSpec) (CFS : AsmCompFamilySpec)
    (lsfInit : LSFInit) (C_lsst : ℝ) (depth w : ℕ) (fmt : Num.Format w) (L capExp limbMul : ℕ)
    (impl : SparsifyImpl)
    (brReemb : BundleTreeState depth → List Update → (ℕ → List End) → (ℕ → List End) → List ℕ)
    (p : Program) (fCFInit fCFBatch : ℕ)
    (CF : AsmCompFamilyAt CFS lsfInit w fmt L capExp limbMul p fCFInit fCFBatch)
    (bp : AsmBranchProcs) where
  rep : DSRep (AsmBranchAbs depth)
  rep_local : rep.Local
  /-- `init [cfH, j, graph, compactOrdPtr, expPtr, k, M, N, L, P_fp, vCap, eCap, depth, lengths,
  h]`: builds branch `j` at handle `h` from `CF`, `G` with its lengths at `lengths`, the compacted
  order, and P4's single-branch export at `expPtr` (`CompBranchExportAt`). Leaves `CF` unchanged. -/
  init_runs : ∀ (cfH j graph lengths cOrdPtr expPtr expEnd k M N vCap eCap h cWords : ℕ)
      (G : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (cfs : CompFamilyAbs) (xcf : CF.rep.τ)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → fmt.precision ≤ 4 * L → 0 < k → j < k → G.IsValid → G.V.Nonempty → G.m ≤ M → G.n ≤ N →
      G.n ≤ G.m + 1 → SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      (M + N + 2) ^ S.wordExp capExp * (L + 1) < 2 ^ w →
      CF.rep.rep cfH cfs xcf mem → cfs j = initCompLSFWith lsfInit G ℓ₀ k j →
      BranchLengthsAt mem lengths eCap L fmt.precision h G ℓ₀ →
      DynGraphAt mem graph vCap eCap G → graph + dynGraphSize vCap eCap ≤ h →
      OrdListAt mem cOrdPtr ord cWords → cOrdPtr + cWords ≤ h →
      cWords ≤ 1 + 6 * G.m → IsRotationOrder G ord →
      CompBranchExportAt w mem expPtr expEnd L capExp M N vCap eCap (cfs j) →
      expEnd ≤ h → (∀ a, CF.rep.foot cfH xcf a → a < h) →
      (∀ a ∈ [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, fmt.precision, vCap, eCap, depth,
        lengths, h], a < 2 ^ w) →
      ZeroFrom mem h →
      h + (S.initSpace capExp).eval (M + N + k + vCap + eCap + L + depth) < 2 ^ w →
      let tr₀ := initBundleTreeWithParams lsfInit depth (fun _ => canonicalSparsify impl)
        (canonicalSparsifyParams impl) (dsAmortConst impl) k M N G ℓ₀ ord j
      AsmBrModelFacts impl vCap eCap tr₀ ord → BranchUpdatesBelow impl tr₀ 0 →
      ∃ body, p.procs[bp.fInit]? = some body ∧ ∃ o st' c x', Runs w p ω body
          (startState [cfH, j, graph, cOrdPtr, expPtr, k, M, N, L, fmt.precision, vCap, eCap, depth,
            lengths, h] mem pos) o st' c ∧
        rep.rep h ⟨tr₀, ord, vCap, eCap⟩ x' st'.mem ∧
        rep.Respects (fun _ => False) h
          ((S.initSpace capExp).eval (M + N + k + vCap + eCap + L + depth)) mem o.value h x' st'.mem ∧
        c + rep.phi h x' st'.mem ≤ S.mul capExp limbMul * tr₀.machCost
  /-- `step [brH, cfH, j, batch, words, edits, editWords, fChgPtr, outSlotPtr, reembSlotPtr, h]`:
  steps branch `j` via `stepBundleTree`, writes the 4 output words of `BranchOutAt` at
  `outSlotPtr .. outSlotPtr + 3` and the 2 `reembList` words `[reembPtr, reembLen]` at
  `reembSlotPtr, reembSlotPtr + 1` (all output payloads allocated inside `[h, o.value)`), and
  leaves `CF` unchanged. -/
  step_runs : ∀ (brH cfH j batch words edits editWords fChgPtr fChgEnd
      outSlotPtr reembSlotPtr h : ℕ)
      (k M N vCap eCap n : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : rep.τ) (cfsOld cfsNew : CompFamilyAbs) (xcf : CF.rep.τ)
      (U : List Update) (ed : List OrdEdit) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → 0 < k → j < k → tr.m₀ = M → tr.n₀ = N →
      1 ≤ depth → depth ≤ bundleLogFactor M N → depth ≤ Expander.chosenL ((M + N) ^ 2) →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      (M + N + 2) ^ S.wordExp capExp * (L + 1) < 2 ^ w →
      rep.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      CF.rep.rep cfH cfsNew xcf mem →
      cfsOld j = tr.cs → cfsNew j = compLSFBatch tr.cs U →
      CompFamilyChgAt w k mem fChgPtr fChgEnd cfsOld U →
      CompSplitListAt w k mem (fChgPtr + k) fChgEnd cfsOld U → fChgEnd ≤ h →
      SmallBatchAt mem batch tr.cs.G U words → tr.cs.G.BatchIsValid U →
      BatchWithinCaps vCap eCap U →
      OrdEditsAt mem edits ed editWords →
      OrderedBatch tr.cs.G U ord (applyOrdEdits ord ed) →
      OrdEditsValidFor vCap eCap ord ed →
      OrdEditsForBatch tr.cs.G U ed →
      (∀ i < words, mem (batch + i) < 2 ^ w) → (∀ i < editWords, mem (edits + i) < 2 ^ w) →
      batch + words ≤ h → edits + editWords ≤ h →
      outSlotPtr + 4 ≤ h → reembSlotPtr + 2 ≤ h →
      (∀ a, outSlotPtr ≤ a → a < outSlotPtr + 4 → ¬ (reembSlotPtr ≤ a ∧ a < reembSlotPtr + 2)) →
      (∀ a, rep.foot brH x a → a < h) → (∀ a, CF.rep.foot cfH xcf a → a < h) →
      (∀ a, rep.foot brH x a → ¬ CF.rep.foot cfH xcf a) →
      (∀ a, outSlotPtr ≤ a → a < outSlotPtr + 4 → ¬ rep.foot brH x a ∧ ¬ CF.rep.foot cfH xcf a) →
      (∀ a, reembSlotPtr ≤ a → a < reembSlotPtr + 2 → ¬ rep.foot brH x a ∧ ¬ CF.rep.foot cfH xcf a) →
      (∀ a, batch ≤ a → a < batch + words → ¬ rep.foot brH x a) →
      (∀ a, edits ≤ a → a < edits + editWords → ¬ rep.foot brH x a) →
      (∀ a, fChgPtr ≤ a → a < fChgEnd → ¬ rep.foot brH x a) →
      fChgPtr + j < 2 ^ w → mem (fChgPtr + j) < 2 ^ w →
      (∀ a ∈ [brH, cfH, j, batch, words, edits, editWords, fChgPtr, outSlotPtr, reembSlotPtr, h],
        a < 2 ^ w) →
      ZeroFrom mem h →
      h + (S.stepSpace capExp).eval (M + N + k + vCap + eCap + L + depth + words + editWords) < 2 ^ w →
      let ord' := applyOrdEdits ord ed
      let info := stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord'
      ((n + U.length : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N →
      BranchUpdatesBelow impl tr n →
      BranchUpdatesBelow impl info.state (n + U.length) →
      AsmBrModelFacts impl vCap eCap tr ord →
      AsmBrModelFacts impl vCap eCap info.state ord' →
      ∃ body, p.procs[bp.fStep]? = some body ∧ ∃ o st' c x',
        Runs w p ω body
          (startState [brH, cfH, j, batch, words, edits, editWords, fChgPtr, outSlotPtr,
            reembSlotPtr, h, fChgPtr + k] mem pos) o st' c ∧
        rep.rep brH ⟨info.state, ord', vCap, eCap⟩ x' st'.mem ∧
        SmallBatchAt st'.mem (st'.mem outSlotPtr) tr.S_cur info.U_S (st'.mem (outSlotPtr + 1)) ∧
        h ≤ st'.mem outSlotPtr ∧ st'.mem outSlotPtr + st'.mem (outSlotPtr + 1) ≤ o.value ∧
        (∃ outEd : List OrdEdit,
          OrdEditsAt st'.mem (st'.mem (outSlotPtr + 2)) outEd (st'.mem (outSlotPtr + 3)) ∧
          applyOrdEdits (tr.outOrder ord) outEd = info.state.outOrder ord' ∧
          OrdEditsValidFor vCap eCap (tr.outOrder ord) outEd ∧
          OrdEditsForBatch tr.S_cur info.U_S outEd) ∧
        h ≤ st'.mem (outSlotPtr + 2) ∧ st'.mem (outSlotPtr + 2) + st'.mem (outSlotPtr + 3) ≤ o.value ∧
        readList st'.mem (st'.mem reembSlotPtr) (st'.mem (reembSlotPtr + 1)) =
          brReemb tr U ord ord' ∧
        h ≤ st'.mem reembSlotPtr ∧ st'.mem reembSlotPtr + st'.mem (reembSlotPtr + 1) ≤ o.value ∧
        h ≤ o.value ∧
        o.value ≤ h + (S.stepSpace capExp).eval (M + N + k + vCap + eCap + L + depth + words + editWords) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ rep.foot brH x a → ¬ (outSlotPtr ≤ a ∧ a < outSlotPtr + 4) →
          ¬ (reembSlotPtr ≤ a ∧ a < reembSlotPtr + 2) → st'.mem a = mem a) ∧
        (∀ a, rep.foot brH x' a → rep.foot brH x a ∨ (h ≤ a ∧ a < o.value)) ∧
        c + rep.phi brH x' st'.mem ≤
          S.mul capExp limbMul * (branchStepCharge (fun _ => canonicalSparsify impl) tr U ord ord' +
            (words + editWords + 1) * bundleLogFactor M N) + rep.phi brH x mem
  /-- `restart [brH, cfH, j, h]`: restarts branch `j` via `restartBundleTree`, querying P4's
  root oracle (`CF.toRootQueryAt k`) and returning updated witnesses `(x', xcf')` with disjoint
  footprints. -/
  restart_runs : ∀ (brH cfH j k M N vCap eCap h : ℕ) (tr : BundleTreeState depth)
      (ord : ℕ → List End) (x : rep.τ) (cfs : CompFamilyAbs) (xcf : CF.rep.τ)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → 0 < k → j < k → tr.m₀ = M → tr.n₀ = N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      16 ≤ 2 ^ w → (M + N + 2) ^ S.wordExp capExp * (L + 1) < 2 ^ w →
      rep.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      CF.rep.rep cfH cfs xcf mem → CF.vCapOf xcf = vCap → CF.eCapOf xcf = eCap → cfs j = tr.cs → k = (cfs 0).k →
      (∀ a, rep.foot brH x a → a < h) → (∀ a, CF.rep.foot cfH xcf a → a < h) →
      (∀ a, rep.foot brH x a → ¬ CF.rep.foot cfH xcf a) →
      (∀ a ∈ [brH, cfH, j, h], a < 2 ^ w) →
      ZeroFrom mem h →
      h + (S.restartSpace capExp).eval (M + N + k + vCap + eCap + L + depth) < 2 ^ w →
      let tr' := restartBundleTree depth (fun _ => canonicalSparsify impl) tr ord
      AsmBrModelFacts impl vCap eCap tr ord →
      AsmBrModelFacts impl vCap eCap tr' ord →
      ∃ body, p.procs[bp.fRestart]? = some body ∧ ∃ o st' c x' xcf',
        Runs w p ω body (startState [brH, cfH, j, h] mem pos) o st' c ∧
        rep.rep brH ⟨tr', ord, vCap, eCap⟩ x' st'.mem ∧
        CF.rep.rep cfH cfs xcf' st'.mem ∧ CF.vCapOf xcf' = vCap ∧ CF.eCapOf xcf' = eCap ∧
        h ≤ o.value ∧
        o.value ≤ h + (S.restartSpace capExp).eval (M + N + k + vCap + eCap + L + depth) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, ¬ rep.foot brH x a → ¬ CF.rep.foot cfH xcf a → st'.mem a = mem a) ∧
        (∀ a, rep.foot brH x' a → rep.foot brH x a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, CF.rep.foot cfH xcf' a → CF.rep.foot cfH xcf a ∨ (h ≤ a ∧ a < o.value)) ∧
        (∀ a, rep.foot brH x' a → ¬ CF.rep.foot cfH xcf' a) ∧
        c + rep.phi brH x' st'.mem + CF.rep.phi cfH xcf' st'.mem ≤
          S.mul capExp limbMul * (singleBundleRestartMachCost depth (fun _ => canonicalSparsify impl) tr ord + 1) +
            rep.phi brH x mem + CF.rep.phi cfH xcf mem
  /-- Readout `2` (`[brH, h]`): writes the 5 words of `LSFAt` with
  `L_w ≤ L + (capExp + sparseCoreReadout2LimbConst) * (log + 1)`. -/
  readLSF_runs : ∀ (brH h M N vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      fmt.limbBits = 4 → tr.m₀ = M → tr.n₀ = N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      rep.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, rep.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 5 < 2 ^ w →
      ∃ body, p.procs[bp.fReadLSF]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        rep.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ forestVCap forestECap,
          st'.mem (h + 4) ≤
            L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) ∧
          LSFAt st'.mem h forestVCap forestECap fmt.limbBits (st'.mem (h + 4)) fmt.precision
            tr.cs.G.E tr.cs.lsf) ∧
        rep.Respects (rep.foot brH x) h 5 mem o.value brH x' st'.mem ∧
        c + rep.phi brH x' st'.mem ≤ S.readout capExp + rep.phi brH x mem
  /-- Readout `3` (`[brH, h]`): writes a pointer to `DynGraphAt` of `tr.S_cur` at `h`. -/
  readS_runs : ∀ (brH h vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      rep.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, rep.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 1 < 2 ^ w →
      ∃ body, p.procs[bp.fReadS]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        rep.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ graphVCap graphECap, DynGraphAt st'.mem (st'.mem h) graphVCap graphECap tr.S_cur) ∧
        rep.Respects (rep.foot brH x) h 1 mem o.value brH x' st'.mem ∧
        c + rep.phi brH x' st'.mem ≤ S.readout capExp + rep.phi brH x mem
  /-- Readout `4` (`[brH, h]`): writes `[embPtr, embECap]` at `h, h + 1` (embedding table, built
  by P10). -/
  readEmb_runs : ∀ (brH h vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      rep.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, rep.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h → h + 2 < 2 ^ w →
      ∃ body, p.procs[bp.fReadEmb]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        rep.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        EmbeddingReadoutAt st'.mem h (st'.mem (h + 1)) tr.cs.G tr.cs.lsf tr.emb ∧
        rep.Respects (rep.foot brH x) h 2 mem o.value brH x' st'.mem ∧
        c + rep.phi brH x' st'.mem ≤ S.readout capExp + rep.phi brH x mem
  /-- Readout `5` (`[brH, h]`): writes `OrdListAt` of `tr.outOrder ord` at `st'.mem h` in at most
  `ordWordsOn tr.S_cur.V (tr.outOrder ord)` words, using space at most `1 + ordWordsOn ...`. -/
  readOrd_runs : ∀ (brH h M N vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : rep.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      tr.m₀ = M → tr.n₀ = N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      rep.rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, rep.foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h →
      h + (1 + ordWordsOn tr.S_cur.V (tr.outOrder ord)) < 2 ^ w →
      ∃ body, p.procs[bp.fReadOrd]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        rep.rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ words, OrdListAt st'.mem (st'.mem h) (tr.outOrder ord) words ∧
          words ≤ ordWordsOn tr.S_cur.V (tr.outOrder ord)) ∧
        rep.Respects (rep.foot brH x) h (1 + ordWordsOn tr.S_cur.V (tr.outOrder ord))
          mem o.value brH x' st'.mem ∧
        c + rep.phi brH x' st'.mem ≤
          S.mul capExp limbMul * (ordWordsOn tr.S_cur.V (tr.outOrder ord) + 1) * bundleLogFactor M N +
            rep.phi brH x mem

/-! ## Top-layer concrete state and `DSRep` -/

/-- Concrete sub-structure handles and witnesses present when the graph is nonempty. -/
structure AsmTopNE (τCF τBR : Type) where
  ordH : ℕ
  xOrd : OrdStoreState
  cfH : ℕ
  xCF : τCF
  tbl : ℕ
  brH : ℕ → ℕ
  xBR : ℕ → τBR

/-- Concrete state of the top-layer sparse-core program. Stores the level dimensions, an optional
nonempty payload (`AsmTopNE`), and a reserved footprint range `[resLo, resHi)` guaranteeing
`M + N + k + vCap + eCap + L + 20 ≤ heap` on every subsequent call. -/
structure AsmTopMeta (τCF τBR : Type) where
  k : ℕ
  M : ℕ
  N : ℕ
  vCap : ℕ
  eCap : ℕ
  L : ℕ
  P_fp : ℕ
  ne : Option (AsmTopNE τCF τBR)
  resLo : ℕ
  resHi : ℕ

/-- Footprint of the top-layer concrete state: header `[b, b + 20)` and reserved block
`[resLo, resHi)`, plus (when nonempty) the P1 arena, P4 footprint, branch table `[tbl, tbl + k)`,
and all `k` branch footprints. -/
def asmTopFoot {depth : ℕ} {τCF τBR : Type} (R_CF : DSRep CompFamilyAbs) (R_BR : DSRep (AsmBranchAbs depth))
    (hCF : R_CF.τ = τCF) (hBR : R_BR.τ = τBR)
    (b : ℕ) (x : AsmTopMeta τCF τBR) (a : ℕ) : Prop :=
  (b ≤ a ∧ a < b + ASM_HDR_SIZE) ∨
  (x.resLo ≤ a ∧ a < x.resHi) ∨
  match x.ne with
  | none => False
  | some ne =>
    ordFoot ne.ordH x.vCap x.eCap a ∨
    R_CF.foot ne.cfH (hCF ▸ ne.xCF) a ∨
    (ne.tbl ≤ a ∧ a < ne.tbl + x.k) ∨
    ∃ j < x.k, R_BR.foot (ne.brH j) (hBR ▸ ne.xBR j) a

/-- Representation predicate for the top-layer sparse-core program on `SparseCoreOrdAbs T`. -/
def AsmTopRepAt {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    (R_CF : DSRep CompFamilyAbs) (R_BR : DSRep (AsmBranchAbs depth))
    (b : ℕ) (a : SparseCoreOrdAbs (sparseCoreProgTool lsfInit C_lsst depth impl))
    (x : AsmTopMeta R_CF.τ R_BR.τ) (mem : ℕ → ℕ) : Prop :=
  x.ne.isSome = a.st.isNonempty ∧
  x.k = a.st.k ∧
  x.resLo + (x.M + x.N + x.k + x.vCap + x.eCap + x.L + ASM_HDR_SIZE) ≤ x.resHi ∧
  -- Header words and 4-word zero `emptyGraph`
  mem (b + ASM_HDR_NE) = (if x.ne.isSome then 1 else 0) ∧
  mem (b + ASM_HDR_K) = x.k ∧
  mem (b + ASM_HDR_M) = x.M ∧
  mem (b + ASM_HDR_N) = x.N ∧
  mem (b + ASM_HDR_VCAP) = x.vCap ∧
  mem (b + ASM_HDR_ECAP) = x.eCap ∧
  mem (b + ASM_HDR_L) = x.L ∧
  mem (b + ASM_HDR_PFP) = x.P_fp ∧
  mem (b + ASM_HDR_EMPTYG) = 0 ∧
  mem (b + ASM_HDR_EMPTYG + 1) = 0 ∧
  mem (b + ASM_HDR_EMPTYG + 2) = 0 ∧
  mem (b + ASM_HDR_EMPTYG + 3) = 0 ∧
  -- Nonempty sub-structures and pairwise disjointness
  (∀ ne, x.ne = some ne →
    mem (b + ASM_HDR_ORDH) = ne.ordH ∧
    mem (b + ASM_HDR_CFH) = ne.cfH ∧
    mem (b + ASM_HDR_TBL) = ne.tbl ∧
    ne.cfH < x.resHi ∧ ne.tbl + x.k ≤ x.resHi ∧ (∀ j < x.k, ne.brH j < x.resHi) ∧
    (∀ v ∈ a.G.V, v < x.vCap) ∧ (∀ e ∈ a.G.E, e < x.eCap) ∧
    (∀ j < x.k, (a.st.trees j).cs.G = a.G ∧ (a.st.trees j).m₀ = x.M ∧ (a.st.trees j).n₀ = x.N) ∧
    (ordStoreRep x.vCap x.eCap).rep ne.ordH a.st.ord ne.xOrd mem ∧
    R_CF.rep ne.cfH (fun j => (a.st.trees j).cs) ne.xCF mem ∧
    (∀ j < x.k, mem (ne.tbl + j) = ne.brH j) ∧
    (∀ j < x.k, R_BR.rep (ne.brH j) ⟨a.st.trees j, a.st.ord, x.vCap, x.eCap⟩ (ne.xBR j) mem) ∧
    -- Pairwise footprint disjointness between header, P1, P4, table, and the `k` branches
    (∀ addr, b ≤ addr ∧ addr < b + ASM_HDR_SIZE →
      ¬ ordFoot ne.ordH x.vCap x.eCap addr ∧ ¬ R_CF.foot ne.cfH ne.xCF addr ∧
      ¬ (ne.tbl ≤ addr ∧ addr < ne.tbl + x.k) ∧
      ∀ j < x.k, ¬ R_BR.foot (ne.brH j) (ne.xBR j) addr) ∧
    (∀ addr, ordFoot ne.ordH x.vCap x.eCap addr →
      ¬ R_CF.foot ne.cfH ne.xCF addr ∧ ¬ (ne.tbl ≤ addr ∧ addr < ne.tbl + x.k) ∧
      ∀ j < x.k, ¬ R_BR.foot (ne.brH j) (ne.xBR j) addr) ∧
    (∀ addr, R_CF.foot ne.cfH ne.xCF addr →
      ¬ (ne.tbl ≤ addr ∧ addr < ne.tbl + x.k) ∧
      ∀ j < x.k, ¬ R_BR.foot (ne.brH j) (ne.xBR j) addr) ∧
    (∀ addr, ne.tbl ≤ addr ∧ addr < ne.tbl + x.k →
      ∀ j < x.k, ¬ R_BR.foot (ne.brH j) (ne.xBR j) addr) ∧
    (∀ j₁ < x.k, ∀ j₂ < x.k, j₁ ≠ j₂ → ∀ addr,
      R_BR.foot (ne.brH j₁) (ne.xBR j₁) addr → ¬ R_BR.foot (ne.brH j₂) (ne.xBR j₂) addr))

/-- Potential of the top-layer concrete state: `0` when empty, otherwise the sum of P1's potential,
P4's potential, and the `k` branch potentials. -/
noncomputable def asmTopPhi {depth : ℕ} (R_CF : DSRep CompFamilyAbs)
    (R_BR : DSRep (AsmBranchAbs depth))
    (x : AsmTopMeta R_CF.τ R_BR.τ) (mem : ℕ → ℕ) : ℕ :=
  match x.ne with
  | none => 0
  | some ne =>
    (ordStoreRep x.vCap x.eCap).phi ne.ordH ne.xOrd mem +
    R_CF.phi ne.cfH ne.xCF mem +
    (Finset.range x.k).sum fun j => R_BR.phi (ne.brH j) (ne.xBR j) mem

/-- Top-layer `DSRep` for `SparseCoreOrdAbs (sparseCoreProgTool lsfInit C_lsst depth impl)` at
level capacities `(L, vCap, eCap)` and word-size parameters `(wordExp, capExp, w, P_fp)`.
Its concrete state type `τ`, potential `phi`, and footprint `foot` depend ONLY on `R_CF` and
`R_BR` (completely uniform over `L, G, k, M, N, vCap, eCap`); only `rep` pins the immutable level
constants `(L, P_fp, vCap, eCap)` and the word-size / cap invariants established at `init`. -/
noncomputable def asmTopRep {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    (R_CF : DSRep CompFamilyAbs) (R_BR : DSRep (AsmBranchAbs depth))
    (wordExp capExp limbMul w L P_fp vCap eCap : ℕ) :
    DSRep (SparseCoreOrdAbs (sparseCoreProgTool lsfInit C_lsst depth impl)) where
  τ := AsmTopMeta R_CF.τ R_BR.τ
  rep b a x mem :=
    AsmTopRepAt R_CF R_BR b a x mem ∧
    x.L = L ∧ x.P_fp = P_fp ∧ x.vCap = vCap ∧ x.eCap = eCap ∧
    (x.M + x.N + 2) ^ wordExp * (x.L + 1) < 2 ^ w ∧
    SparseCoreCapHyp capExp limbMul x.L x.M x.N x.vCap x.eCap ∧
    0 < x.k
  phi _ x mem := asmTopPhi R_CF R_BR x mem
  foot b x a := asmTopFoot R_CF R_BR rfl rfl b x a

/-- `asmTopRep` is local whenever `R_CF` and `R_BR` are local. -/
theorem asmTopRep_local {lsfInit : LSFInit} {C_lsst : ℝ} {depth : ℕ} {impl : SparsifyImpl}
    {R_CF : DSRep CompFamilyAbs} {R_BR : DSRep (AsmBranchAbs depth)}
    {wordExp capExp limbMul w L P_fp vCap eCap : ℕ}
    (hCF : R_CF.Local) (hBR : R_BR.Local) :
    (asmTopRep (lsfInit := lsfInit) (C_lsst := C_lsst) (impl := impl) R_CF R_BR
      wordExp capExp limbMul w L P_fp vCap eCap).Local := by
  intro b a x mem mem' hagree
  have hhdr : ∀ i < ASM_HDR_SIZE, mem (b + i) = mem' (b + i) := fun i hi =>
    hagree (b + i) (Or.inl ⟨by omega, by omega⟩)
  refine ⟨?_, ?_⟩
  · intro ⟨hrep, hrest⟩
    rcases hrep with ⟨hne, hk, hres, h0, h1, h2, h3, h4, h5, h6, h7,
      he0, he1, he2, he3, hnonempty⟩
    refine ⟨⟨hne, hk, hres,
      (hhdr ASM_HDR_NE (by decide)).symm.trans h0, (hhdr ASM_HDR_K (by decide)).symm.trans h1,
      (hhdr ASM_HDR_M (by decide)).symm.trans h2, (hhdr ASM_HDR_N (by decide)).symm.trans h3,
      (hhdr ASM_HDR_VCAP (by decide)).symm.trans h4, (hhdr ASM_HDR_ECAP (by decide)).symm.trans h5,
      (hhdr ASM_HDR_L (by decide)).symm.trans h6, (hhdr ASM_HDR_PFP (by decide)).symm.trans h7,
      (hhdr ASM_HDR_EMPTYG (by decide)).symm.trans he0, (hhdr (ASM_HDR_EMPTYG + 1) (by decide)).symm.trans he1,
      (hhdr (ASM_HDR_EMPTYG + 2) (by decide)).symm.trans he2, (hhdr (ASM_HDR_EMPTYG + 3) (by decide)).symm.trans he3,
      fun ne hneEq => ?_⟩, hrest⟩
    obtain ⟨h8, h9, h10, hcfLt, htblLt, hbrLt, hvG, heG, hG, hOrd, hCFrep, hTbl, hBRrep, hd1, hd2, hd3, hd4, hd5⟩ :=
      hnonempty ne hneEq
    refine ⟨(hhdr ASM_HDR_ORDH (by decide)).symm.trans h8, (hhdr ASM_HDR_CFH (by decide)).symm.trans h9,
      (hhdr ASM_HDR_TBL (by decide)).symm.trans h10, hcfLt, htblLt, hbrLt, hvG, heG, hG,
      (ordStoreRep_local x.vCap x.eCap ne.ordH a.st.ord ne.xOrd mem mem'
        (fun addr ha => hagree addr (Or.inr (Or.inr (by simp [hneEq]; exact Or.inl ha))))).1 hOrd,
      (hCF ne.cfH (fun j => (a.st.trees j).cs) ne.xCF mem mem'
        (fun addr ha => hagree addr (Or.inr (Or.inr (by simp [hneEq]; exact Or.inr (Or.inl ha)))))).1 hCFrep,
      fun j hj => (hagree (ne.tbl + j) (Or.inr (Or.inr (by simp [hneEq]; right; right; left; omega)))).symm.trans (hTbl j hj),
      fun j hj => (hBR (ne.brH j) ⟨a.st.trees j, a.st.ord, x.vCap, x.eCap⟩ (ne.xBR j) mem mem'
        (fun addr ha => hagree addr (Or.inr (Or.inr (by simp [hneEq]; right; right; right; exact ⟨j, hj, ha⟩))))).1 (hBRrep j hj),
      hd1, hd2, hd3, hd4, hd5⟩
  · show asmTopPhi R_CF R_BR x mem = asmTopPhi R_CF R_BR x mem'
    rcases x with ⟨xk, xM, xN, xvCap, xeCap, xL, xPfp, none | ne, xresLo, xresHi⟩
    · rfl
    · unfold asmTopPhi; dsimp only
      rw [(hCF ne.cfH (fun j => (a.st.trees j).cs) ne.xCF mem mem'
            (fun addr ha => hagree addr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))).2,
          Finset.sum_congr rfl fun j hj => (hBR (ne.brH j) ⟨a.st.trees j, a.st.ord, xvCap, xeCap⟩
            (ne.xBR j) mem mem' (fun addr ha => hagree addr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr ⟨j, Finset.mem_range.mp hj, ha⟩))))))).2]
      rfl

end MinCostFlow.SparseCore.Program
