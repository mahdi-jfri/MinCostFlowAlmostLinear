module

public import MinCostFlow.LowStretch.ProgBodyNode
public import MinCostFlow.LowStretch.ProgClusterPetL

/-!
# Small facts for the proof of the node part

* `PW.LInv.congr`: the invariant of the petal loop reads only the registers below `43` and the
  memory. So it holds at the start of the call of the loop, whose registers are the arguments.
* `parWalk_congrW`, `parEnd_congrW`: a path of the parent array reads only the parents of its
  nodes.
* `Rec.sv_le`: a local index is at most the number of super-vertices.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace PW

variable {W : PW} {w : ℕ} {A : TA} {Q : LA}

/-- **The invariant of the loop reads only the registers below `43` and the memory.** -/
theorem LInv.congr {sp : Bool} {k0 : ℕ} {M0 : ℕ → ℕ} {a : LG} {st st' : State}
    (h : W.LInv A Q sp k0 M0 w a st) (hm : st'.mem = st.mem)
    (hr : ∀ i < 43, st'.regs i = st.regs i) : W.LInv A Q sp k0 M0 w a st' := by
  rcases st with ⟨m, r, p⟩
  rcases st' with ⟨m', r', p'⟩
  obtain rfl : m' = m := hm
  exact { h with
    regs := fun i hi a b c => (hr i hi).trans (h.regs i hi a b c)
    r13 := (hr 13 (by omega)).trans h.r13
    r32 := (hr 32 (by omega)).trans h.r32
    r41 := (hr 41 (by omega)).trans h.r41 }

end PW

/-- A path of the parent array reads only the parents of its nodes. -/
theorem parWalk_congrW {M M' : ℕ → ℕ} {PAR : ℕ} :
    ∀ (l u : ℕ), (∀ v ∈ parWalk M PAR u l, M' (PAR + v) = M (PAR + v)) →
      parWalk M' PAR u l = parWalk M PAR u l
  | 0, _, _ => rfl
  | l + 1, u, h => by
    simp only [parWalk] at h ⊢
    rw [h u List.mem_cons_self,
      parWalk_congrW l _ (fun v hv => h v (List.mem_cons_of_mem _ hv))]

/-- The end of a path of the parent array reads only the parents of its nodes. -/
theorem parEnd_congrW {M M' : ℕ → ℕ} {PAR : ℕ} :
    ∀ (l u : ℕ), (∀ v ∈ parWalk M PAR u l, M' (PAR + v) = M (PAR + v)) →
      parEnd M' PAR u l = parEnd M PAR u l
  | 0, _, _ => rfl
  | l + 1, u, h => by
    simp only [parWalk] at h
    unfold parEnd
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h u List.mem_cons_self]
    exact parEnd_congrW l _ (fun v hv => h v (List.mem_cons_of_mem _ hv))

/-- A local index is at most the number of super-vertices. -/
theorem Rec.sv_le (T : KT) (R : Rec) (c : Cl) (v : ℕ) : R.sv T c v ≤ R.nodes.length :=
  List.idxOf_le_length

end MinCostFlow.LowStretch

namespace MinCostFlow.LowStretch

/-- The next vertex of a highway is the other end of its pair, seen from the vertex before. This
is how the node part finds the target of child `0` past the special portal. -/
theorem hv_succ (G : PG) : ∀ (t : ℕ) (hw : List ℕ) (i : ℕ), i < hw.length →
    hv G t hw (i + 1) = G.other (hw.getD i 0) (hv G t hw i)
  | _, [], _, h => by simp at h
  | t, p :: hw, 0, _ => by
    simp only [hv, PG.vtx, List.getD_cons_succ, List.getD_cons_zero]
    exact PG.vtx_getD_zero _ _
  | t, p :: hw, i + 1, h => by
    have := hv_succ G (G.other p t) hw i (by simpa using h)
    simpa [hv, PG.vtx] using this

end MinCostFlow.LowStretch
