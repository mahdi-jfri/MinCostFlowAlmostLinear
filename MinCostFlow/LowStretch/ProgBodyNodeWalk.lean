module

public import MinCostFlow.LowStretch.ProgBodyNodeCongr
public import MinCostFlow.LowStretch.ProgClusterWalk3

/-!
# The walk of child `0`

Child `0` (the stem) has as highway the highway `c.hw` of the cluster (no special petal) or its
part after the special portal. Its walk in the tree of the first run is a tail of the path of
parents from the node of `c.t`, which the setup gives (`SetupOut`). `PW.walk_stem` is the case
without a special petal: the whole path. `PW.walk_stem_sp` is the case with one: the tail after
the parent arc that is the special portal.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {A : TA}

/-- The steps of a path of parents have positive length. -/
theorem stp_pos (hT : W.Tree A mem) {v n : ℕ} (hp : W.Path mem v n) :
    ∀ s ∈ W.stp A mem v n, 0 < W.c.len W.G s.1 := by
  intro s hs
  unfold stp at hs
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hs
  have hk' := List.mem_range.mp hk
  exact (hT.edge _ (hp.2 k hk').2 (hp.2 k hk').1).2.2.2.2.2.2.2.1

/-- The nodes of a tail of a path of parents are nodes of the cluster. -/
theorem Path.walk_lt (hr : W.root < W.s) {v n j0 : ℕ} (hp : W.Path mem v n) (hj : j0 ≤ n) :
    ∀ u ∈ parWalk mem W.NXT (W.pe mem v j0) (n - j0), u < W.s := by
  intro u hu
  rw [parWalk_eq] at hu
  obtain ⟨j, hj', rfl⟩ := List.mem_map.mp hu
  have e : parEnd mem W.NXT (W.pe mem v j0) j = W.pe mem v (j + j0) := by
    unfold pe parEnd; rw [Function.iterate_add_apply]
  rw [e]
  exact hp.lt hr (by simp at hj'; omega)

/-- **The walk of the stem without a special petal**: the path of parents from the node of
`c.t`, as `PetL.Ok.walk` states it for a highway `hw` that splits along the path. -/
theorem walk_stem (h : W.Ok w mem) (hT : W.Tree A mem) {e n : ℕ} {hw : List ℕ}
    (hp : W.Path mem (W.sv e) n) (hd : W.c.HwDec W.G e (W.stp A mem (W.sv e) n) hw)
    (X : PetL) (hX : X.PAR = W.NXT ∧ X.PP = A.PP ∧ X.PF = A.PF ∧ X.PA = A.PA ∧ X.PB = A.PB) :
    (parWalk mem X.PAR (W.sv e) (Cl.hwE W.G e hw W.c.θ W.c.half).length).map (X.ent mem) =
        Cl.hwE W.G e hw W.c.θ W.c.half ∧
      (∀ u ∈ parWalk mem X.PAR (W.sv e) (Cl.hwE W.G e hw W.c.θ W.c.half).length,
        u = W.sv (mem (X.PA + u))) ∧
      parEnd mem X.PAR (W.sv e) (Cl.hwE W.G e hw W.c.θ W.c.half).length = W.root ∧
      W.root ∉ parWalk mem X.PAR (W.sv e) (Cl.hwE W.G e hw W.c.θ W.c.half).length ∧
      (parWalk mem X.PAR (W.sv e) (Cl.hwE W.G e hw W.c.θ W.c.half).length).Nodup ∧
      ∀ u ∈ parWalk mem X.PAR (W.sv e) (Cl.hwE W.G e hw W.c.θ W.c.half).length, u < W.s := by
  have hE := hd.hwE_eq (stp_pos hT hp) W.c.half
  have hlen : (Cl.hwE W.G e hw W.c.θ W.c.half).length = n := by
    rw [hE, List.length_map, stp_length]
  have ht := walk_tail h hT hp (Nat.zero_le n) X hX
  simp only [Nat.sub_zero, List.drop_zero] at ht
  have hpe0 : W.pe mem (W.sv e) 0 = W.sv e := rfl
  rw [hpe0] at ht
  rw [hlen]
  refine ⟨ht.1.trans hE.symm, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2, ?_⟩
  rw [hX.1]
  simpa [hpe0] using Path.walk_lt h.root_lt hp (Nat.zero_le n)

/-- **The walk of the stem with a special petal**: the tail of the path of parents from the
node of the other end `hv e hw (i + 1)` of the special portal, which is the parent arc of node
`m` of the path. -/
theorem walk_stem_sp (h : W.Ok w mem) (hT : W.Tree A mem) {e n m i : ℕ} {hw : List ℕ}
    (hp : W.Path mem (W.sv e) n) (hd : W.c.HwDec W.G e (W.stp A mem (W.sv e) n) hw)
    (hmn : m < n) (hi : i < hw.length)
    (e0 : hw.getD i 0 = mem (A.PP + W.pe mem (W.sv e) m))
    (e1 : hv W.G e hw i = mem (A.PA + W.pe mem (W.sv e) m))
    (e2 : hv W.G e hw (i + 1) = mem (A.PB + W.pe mem (W.sv e) m))
    (X : PetL) (hX : X.PAR = W.NXT ∧ X.PP = A.PP ∧ X.PF = A.PF ∧ X.PA = A.PA ∧ X.PB = A.PB) :
    (parWalk mem X.PAR (W.sv (hv W.G e hw (i + 1)))
        (Cl.hwE W.G (hv W.G e hw (i + 1)) (hw.drop (i + 1)) W.c.θ W.c.half).length).map
        (X.ent mem) = Cl.hwE W.G (hv W.G e hw (i + 1)) (hw.drop (i + 1)) W.c.θ W.c.half ∧
      (∀ u ∈ parWalk mem X.PAR (W.sv (hv W.G e hw (i + 1)))
          (Cl.hwE W.G (hv W.G e hw (i + 1)) (hw.drop (i + 1)) W.c.θ W.c.half).length,
        u = W.sv (mem (X.PA + u))) ∧
      parEnd mem X.PAR (W.sv (hv W.G e hw (i + 1)))
          (Cl.hwE W.G (hv W.G e hw (i + 1)) (hw.drop (i + 1)) W.c.θ W.c.half).length =
        W.root ∧
      W.root ∉ parWalk mem X.PAR (W.sv (hv W.G e hw (i + 1)))
          (Cl.hwE W.G (hv W.G e hw (i + 1)) (hw.drop (i + 1)) W.c.θ W.c.half).length ∧
      (parWalk mem X.PAR (W.sv (hv W.G e hw (i + 1)))
          (Cl.hwE W.G (hv W.G e hw (i + 1)) (hw.drop (i + 1)) W.c.θ W.c.half).length).Nodup ∧
      ∀ u ∈ parWalk mem X.PAR (W.sv (hv W.G e hw (i + 1)))
          (Cl.hwE W.G (hv W.G e hw (i + 1)) (hw.drop (i + 1)) W.c.θ W.c.half).length, u < W.s := by
  have hlen := stp_length (W := W) (A := A) (mem := mem) (W.sv e) n
  have hm' : m < (W.stp A mem (W.sv e) n).length := by rw [hlen]; exact hmn
  have hE := hd.hwE_drop h.conn (stp_pos hT hp) W.c.half hi hm'
    (by rw [stp_getElem]; exact e0) (by rw [stp_getElem]; exact e1)
  have hL : (Cl.hwE W.G (hv W.G e hw (i + 1)) (hw.drop (i + 1)) W.c.θ W.c.half).length =
      n - (m + 1) := by
    rw [hE, List.length_map, List.length_drop, hlen]
  have hedge := hT.edge _ (hp.2 m hmn).2 (hp.2 m hmn).1
  have hsv : W.sv (hv W.G e hw (i + 1)) = W.pe mem (W.sv e) (m + 1) := by
    rw [e2, hedge.2.2.2.2.1, pe_succ']
  have ht := walk_tail h hT hp (show m + 1 ≤ n by omega) X hX
  rw [hsv, hL]
  refine ⟨ht.1.trans hE.symm, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2, ?_⟩
  rw [hX.1]
  exact Path.walk_lt h.root_lt hp (by omega)

end PW

end MinCostFlow.LowStretch
