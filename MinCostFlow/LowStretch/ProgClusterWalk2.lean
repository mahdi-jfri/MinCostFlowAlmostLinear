module

public import MinCostFlow.LowStretch.ProgClusterWalk
public import MinCostFlow.LowStretch.ProgClusterLoop5

/-!
# The walk of a raw child along the tree

The child step needs, for each raw child, that the path of the parent array from its target
gives the stored form of its highway (`PetL.Ok.walk`). For a petal carved along the tree, the
highway splits into the steps of the path of parents (`HwDec`), and the part before the portal
is made of the first `m` steps, where `m` is the step of the portal. Then the stored form is the
list of the parent arcs of the first `m` nodes of the path (`Cl.HwDec.hwE_take`). This file
proves this (`PW.walk_of_dec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

theorem parWalk_eq (mem : ℕ → ℕ) (PAR : ℕ) :
    ∀ u ℓ, parWalk mem PAR u ℓ = (List.range ℓ).map (parEnd mem PAR u) := by
  intro u ℓ
  induction ℓ generalizing u with
  | zero => rfl
  | succ ℓ ih =>
    rw [parWalk, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {A : TA}

/-- **The walk of a raw child along the tree.** A highway `hw` from `e` that splits into the
steps of the path of parents of `e`, with its portal at position `i` given by step `m`, gives
the facts of `PetL.Ok.walk` for the part of `hw` before the portal, at every petal block `X`
whose tree arrays are those of `A`. -/
theorem walk_of_dec (h : W.Ok w mem) (hT : W.Tree A mem) {e n m i : ℕ} {hw : List ℕ}
    (hp : W.Path mem (W.sv e) n) (hd : W.c.HwDec W.G e (W.stp A mem (W.sv e) n) hw)
    (hmn : m < n) (hi : i < hw.length)
    (e0 : hw.getD i 0 = mem (A.PP + W.pe mem (W.sv e) m))
    (e1 : hv W.G e hw i = mem (A.PA + W.pe mem (W.sv e) m))
    (X : PetL) (hX : X.PAR = W.NXT ∧ X.PP = A.PP ∧ X.PF = A.PF ∧ X.PA = A.PA ∧ X.PB = A.PB) :
    (parWalk mem X.PAR (W.sv e) (Cl.hwE W.G e (hw.take i) W.c.θ W.c.half).length).map
        (X.ent mem) = Cl.hwE W.G e (hw.take i) W.c.θ W.c.half ∧
      (∀ u ∈ parWalk mem X.PAR (W.sv e) (Cl.hwE W.G e (hw.take i) W.c.θ W.c.half).length,
        u = W.sv (mem (X.PA + u))) ∧
      parEnd mem X.PAR (W.sv e) (Cl.hwE W.G e (hw.take i) W.c.θ W.c.half).length =
        W.sv (hv W.G e hw i) ∧
      W.sv (hv W.G e hw i) ∉
        parWalk mem X.PAR (W.sv e) (Cl.hwE W.G e (hw.take i) W.c.θ W.c.half).length ∧
      (parWalk mem X.PAR (W.sv e) (Cl.hwE W.G e (hw.take i) W.c.θ W.c.half).length).Nodup := by
  obtain ⟨x1, x2, x3, x4, x5⟩ := hX
  have hr := h.root_lt
  have hlen := stp_length (W := W) (A := A) (mem := mem) (W.sv e) n
  have hedge : ∀ k < n, W.pe mem (W.sv e) k < W.s ∧ W.pe mem (W.sv e) k ≠ W.root :=
    fun k hk => ⟨(hp.2 k hk).2, (hp.2 k hk).1⟩
  have hpos : ∀ s ∈ W.stp A mem (W.sv e) n, 0 < W.c.len W.G s.1 := by
    intro s hs
    unfold stp at hs
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs
    have hk' := List.mem_range.mp hk
    exact (hT.edge _ (hedge k hk').1 (hedge k hk').2).2.2.2.2.2.2.2.1
  have hm' : m < (W.stp A mem (W.sv e) n).length := by rw [hlen]; exact hmn
  have hH := hd.hwE_take h.conn hpos W.c.half hi hm' (by rw [stp_getElem]; exact e0)
    (by rw [stp_getElem]; exact e1)
  have hL : (Cl.hwE W.G e (hw.take i) W.c.θ W.c.half).length = m := by
    rw [hH]; simp [hlen]; omega
  rw [hL, hH, parWalk_eq, x1]
  have hpe : ∀ k, parEnd mem W.NXT (W.sv e) k = W.pe mem (W.sv e) k := fun _ => rfl
  simp only [hpe]
  have hnd := hT.path_nodup hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply List.ext_getElem (by simp [hlen]; omega)
    intro k h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, stp_getElem, PetL.ent,
      Cl.stE, x2, x3, x4, x5, hpe]
    have := (hT.edge _ (hedge k (by omega)).1 (hedge k (by omega)).2).2.2.2.2.2.2.2.2.2
    rw [this]
  · intro u hu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu
    have hk' := List.mem_range.mp hk
    simp only [hpe]
    rw [x4, (hT.edge _ (hedge k (by omega)).1 (hedge k (by omega)).2).2.2.1]
  · rw [e1, (hT.edge _ (hedge m hmn).1 (hedge m hmn).2).2.2.1]
  · rw [e1, (hT.edge _ (hedge m hmn).1 (hedge m hmn).2).2.2.1]
    intro hmem
    obtain ⟨k, hk, hk2⟩ := List.mem_map.mp hmem
    simp only [hpe] at hk2
    have hk' := List.mem_range.mp hk
    have := List.inj_on_of_nodup_map hnd (List.mem_range.mpr (show k < n + 1 by omega))
      (List.mem_range.mpr (show m < n + 1 by omega)) hk2
    omega
  · have : List.Sublist ((List.range m).map (W.pe mem (W.sv e)))
        ((List.range (n + 1)).map (W.pe mem (W.sv e))) := by
      apply List.Sublist.map
      exact (List.range_sublist).mpr (by omega)
    exact this.nodup hnd

end PW

end MinCostFlow.LowStretch
