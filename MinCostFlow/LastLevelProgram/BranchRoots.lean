module

public import MinCostFlow.LastLevelProgram.Choices
public import MinCostFlow.LastLevelProgram.IndexGraph
public import MinCostFlow.MinRatio.Layouts
import WordRAM.Tactic

/-!
# Root bits for a connected last-level branch

The root of Definition 5.8 (pages 19–20) is the smallest vertex name in
its component. A connected input has just one such name, so writing
its root table in fresh memory takes one store.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM MinRatio LSF

/-- For a connected nonempty input, the least live vertex is the only root. -/
theorem componentRoots_eq_singleton {G : MGraph} (hv : G.V.Nonempty)
    (hc : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b) :
    componentRoots G = {firstVertex G.V} := by
  have hcomp (u : ℕ) (hu : u ∈ G.V) : compOf G u = G.V := by
    ext v
    exact ⟨fun h => (mem_compOf_iff.mp h).1,
      fun h => mem_compOf_iff.mpr ⟨h, hc u hu v h⟩⟩
  ext r
  constructor
  · intro hr
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hr
    rw [hcomp u hu]
    exact Finset.mem_singleton_self _
  · intro hr
    obtain rfl := Finset.mem_singleton.mp hr
    obtain ⟨u,hu⟩ := hv
    exact Finset.mem_image.mpr ⟨u,hu,congrArg firstVertex (hcomp u hu)⟩

/-- The least vertex name is at index zero in the compact order. -/
theorem firstVertex_eq_vertexName_zero {G : MGraph} (hv : G.V.Nonempty) :
    firstVertex G.V = vertexName G 0 := by
  have hzero : 0 < G.n := Finset.card_pos.mpr hv
  let iso : Fin G.n ≃o G.V := G.V.orderIsoOfFin rfl
  have hname : vertexName G 0 = (iso ⟨0, hzero⟩ : ℕ) := by
    rw [vertexName, dite_eq_left hzero]
    rfl
  apply le_antisymm
  · simpa [firstVertex, hv] using G.V.min'_le _ (vertexName_mem hzero)
  · rw [hname]
    let r : G.V := ⟨firstVertex G.V, firstVertex_mem hv⟩
    have hle : (⟨0, hzero⟩ : Fin G.n) ≤ iso.symm r := Nat.zero_le _
    have h := iso.monotone hle
    rwa [iso.apply_symm_apply] at h

/-- Write the one live root bit in a zeroed array. -/
def writeRootBitBody : Stmt :=
  .seq (.store (.bin .add (.reg 0) (.reg 1)) (.const 1)) (.ret (.const 0))

/-- The single-root bit write returns the shared root layout. -/
theorem writeRootBit_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos base cap root : ℕ)
    (_hw : 1 < 2^w) (hc : root < cap) (_hroom : base + cap < 2^w)
    (hz : ∀ v < cap, mem (base+v) = 0) :
    ∃ o out cost, Runs w p ω writeRootBitBody (startState [base,root] mem pos) o out cost ∧
      (o.value = 0 ∧ RootsAt out.mem base cap {root} ∧
        (∀ a, a < base ∨ base+cap ≤ a → out.mem a = mem a)) ∧ cost ≤ 10 := by
  apply runs_start_le
  unfold writeRootBitBody
  wram_run
  · dsimp only [startState]
    have hframe (a : ℕ) (ha : a < base ∨ base+cap ≤ a) :
        Function.update mem (base+root) 1 a = mem a := Function.update_of_ne (by omega) ..
    refine ⟨rfl,⟨?_,?_⟩,hframe⟩
    · intro r hr
      obtain rfl := Finset.mem_singleton.mp hr
      exact hc
    · intro v hv
      by_cases he : v = root
      · subst v
        exact Or.inl ⟨Finset.mem_singleton_self _,Function.update_self ..⟩
      · exact Or.inr ⟨fun h => he (Finset.mem_singleton.mp h),
          (Function.update_of_ne (by omega) ..).trans (hz v hv)⟩
  · wram_cost

/-- Contract for writing the root table of a connected nonempty branch.
The caller passes the original vertex name and the table's reserved capacity. -/
def branchRootsContract (w cap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ base,
    args = [base, firstVertex G.V] ∧ 1 < 2^w ∧ firstVertex G.V < cap ∧
      base+cap < 2^w ∧ (∀ v < cap, mem (base+v) = 0)
  post args mem ret out := ∃ base,
    args = [base, firstVertex G.V] ∧ ret = 0 ∧
      RootsAt out base cap (componentRoots G) ∧
      (∀ a, a < base ∨ base+cap ≤ a → out a = mem a)
  cost _ _ := 10

/-- The installed root writer returns the named root layout for Definition 5.8
(pages 19–20). The name can be read from slot zero of the compact vertex array. -/
theorem branchRoots_meetsContract {w entry cap : ℕ} {p : Program} {G : MGraph}
    (hp : p.procs[entry]? = some writeRootBitBody) (hv : G.V.Nonempty)
    (hc : ∀ a ∈ G.V, ∀ b ∈ G.V, G.Connected a b) :
    MeetsContract w p entry (branchRootsContract w cap G) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨base,rfl,hw,hr,hroom,hzero⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ :=
    writeRootBit_runs (p := p) (ω := ω) mem pos base cap (firstVertex G.V)
      hw hr hroom hzero
  refine ⟨o,out,cost,hrun,⟨base,rfl,?_⟩,hcost⟩
  rw [componentRoots_eq_singleton hv hc]
  exact hpost

open DynSpanner.Program in
/-- In the loop-only branch all vertices are roots, so the forest's
existing vertex presence table serves as the root table. -/
theorem loopOnlyRoots_at {mem : ℕ → ℕ} {g vCap eCap : ℕ} {F : MGraph}
    (hF : DynGraphAt mem g vCap eCap F) :
    RootsAt mem (dgVPresBase g) vCap F.V := by
  obtain ⟨_,hfit,_,_,_,_,_,hbits,_⟩ := hF
  refine ⟨hfit,fun v hv => ?_⟩
  rw [hbits v hv]
  by_cases h : v ∈ F.V
  · exact Or.inl ⟨h,ite_eq_left h⟩
  · exact Or.inr ⟨h,ite_eq_right h⟩

end MinCostFlow.LastLevelProgram
