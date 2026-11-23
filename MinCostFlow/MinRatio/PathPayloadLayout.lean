module

public import MinCostFlow.MinRatio.PathPayload
public import MinCostFlow.Num.Encoding

/-!
# Fixed-point storage for path values and tags

The computational model (page 7) stores numbers in several machine words.
The Section 6 path payload uses integer numerators at the chosen fixed-point
scale. Every numeric field below uses the shared two's-complement format.
A node header distinguishes vertices from edges. Edge nodes store a direction
bit followed by gradient, length, flow, and detector blocks. A summary stores
gradient and length blocks, then a detector-presence bit and its block.
Lazy tags store signed flow and detector changes separately.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

/-- One integer numerator in the numeric library's fixed-point format. -/
def PathIntAt (mem : ℕ → ℕ) (a h L : ℕ) (z : ℤ) : Prop :=
  Num.Valid mem a h L ∧ Num.intVal mem a h L = z

/-- A vertex header, or an edge header and its four fixed-point blocks.
An edge uses `2 + 4 * L` words. A vertex needs only the zero header. -/
def PathEdgeAt (mem : ℕ → ℕ) (a h L : ℕ) : Option PathEdgeValue → Prop
  | none => mem a = 0
  | some v => mem a = 1 ∧ mem (a + 1) = (if v.forward then 1 else 0) ∧
      PathIntAt mem (a + 2) h L v.gradient ∧
      PathIntAt mem (a + 2 + L) h L v.length ∧
      PathIntAt mem (a + 2 + 2 * L) h L v.flow ∧
      PathIntAt mem (a + 2 + 3 * L) h L v.detector

/-- A lazy tag occupies two blocks, or `2 * L` words. -/
def PathTagAt (mem : ℕ → ℕ) (a h L : ℕ) (t : PathTag) : Prop :=
  PathIntAt mem a h L t.flow ∧ PathIntAt mem (a + L) h L t.detector

/-- A summary occupies `3 * L + 1` words. The absent detector has tag zero.
Its reserved numeric block is ignored. -/
def PathSummaryAt (mem : ℕ → ℕ) (a h L : ℕ) (s : PathSummary) : Prop :=
  PathIntAt mem a h L s.gradient ∧ PathIntAt mem (a + L) h L s.length ∧
  match s.detector with
  | none => mem (a + 2 * L) = 0
  | some z => mem (a + 2 * L) = 1 ∧ PathIntAt mem (a + 2 * L + 1) h L z

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

/-- Reading a stored numerator gives an integer in the signed range. -/
theorem PathIntAt.fits {mem : ℕ → ℕ} {a h L : ℕ} {z : ℤ}
    (hz : PathIntAt mem a h L z) : Num.Fits h L z := by
  rw [← hz.2]
  exact Num.intVal_fits hz.1

/-- Stored numerators are unique. -/
theorem PathIntAt.unique {mem : ℕ → ℕ} {a h L : ℕ} {x y : ℤ}
    (hx : PathIntAt mem a h L x) (hy : PathIntAt mem a h L y) : x = y :=
  hx.2.symm.trans hy.2

/-- Moving an unchanged block preserves its payload numerator. -/
theorem PathIntAt.congr {mem mem' : ℕ → ℕ} {a a' h L : ℕ} {z : ℤ}
    (hz : PathIntAt mem a h L z)
    (heq : ∀ i < L, mem' (a' + i) = mem (a + i)) : PathIntAt mem' a' h L z := by
  refine ⟨fun i hi => (heq i hi) ▸ hz.1 i hi, ?_⟩
  exact (Num.intVal_congr heq).trans hz.2

/-- Agreement on an edge record preserves its direction and all four numerators. -/
theorem PathEdgeAt.congr {mem mem' : ℕ → ℕ} {a h L : ℕ} {value : PathEdgeValue}
    (hv : PathEdgeAt mem a h L (some value))
    (hframe : ∀ x, a ≤ x → x < a + 2 + 4 * L → mem' x = mem x) :
    PathEdgeAt mem' a h L (some value) := by
  obtain ⟨hk, hd, hg, hl, hf, hr⟩ := hv
  exact ⟨(hframe _ (by omega) (by omega)).trans hk,
    (hframe _ (by omega) (by omega)).trans hd,
    hg.congr (fun i hi => hframe _ (by omega) (by omega)),
    hl.congr (fun i hi => hframe _ (by omega) (by omega)),
    hf.congr (fun i hi => hframe _ (by omega) (by omega)),
    hr.congr (fun i hi => hframe _ (by omega) (by omega))⟩

/-- A numeric-library encoding supplies exactly the required payload block. -/
theorem PathIntAt.of_encoding {mem : ℕ → ℕ} {a h L : ℕ} {z : ℤ}
    (he : WordRAM.ListAt mem a (Num.encodeLimbs h L z)) (hz : Num.Fits h L z) :
    PathIntAt mem a h L z := ⟨Num.valid_encodeLimbs he, Num.intVal_encodeLimbs he hz⟩

/-- Fresh zero memory supplies a zero numerator block. -/
theorem pathIntAt_zero {mem : ℕ → ℕ} {heap a h L : ℕ}
    (hz : WordRAM.ZeroFrom mem heap) (ha : heap ≤ a) : PathIntAt mem a h L 0 :=
  ⟨Num.zeroFrom_valid hz ha, Num.intVal_zeroFrom hz ha⟩

/-- The identity tag has a fitting layout in fresh zero memory. -/
theorem pathTagAt_zero {mem : ℕ → ℕ} {heap a h L : ℕ}
    (hz : WordRAM.ZeroFrom mem heap) (ha : heap ≤ a) : PathTagAt mem a h L PathTag.zero :=
  ⟨pathIntAt_zero hz ha, pathIntAt_zero hz (ha.trans (Nat.le_add_right _ _))⟩

/-- The empty summary has a fitting layout in fresh zero memory. -/
theorem pathSummaryAt_empty {mem : ℕ → ℕ} {heap a h L : ℕ}
    (hz : WordRAM.ZeroFrom mem heap) (ha : heap ≤ a) :
    PathSummaryAt mem a h L PathSummary.empty := by
  refine ⟨pathIntAt_zero hz ha, pathIntAt_zero hz (ha.trans (Nat.le_add_right _ _)), ?_⟩
  exact hz _ (ha.trans (Nat.le_add_right _ _))

end MinCostFlow.MinRatio
