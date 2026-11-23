module

public import MinCostFlow.LowStretch.ProgChildMid2

/-!
# One child that keeps its threshold: the invariant after it

`CInv.step_raw`: when child `k` is not reset and the memory meets `MidOk` (with more cells
changed only from `OUTK + 2` on), the loop invariant holds for `k + 1`. The records of the earlier
children are not touched (`RecAt.congr_blk`): child `k` writes only its own cells (`CS.WrJ k`), its
record block and the heap from `H` on.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The nodes of the tree path of child `j` are local indices. -/
theorem walk_lt (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) {j : ℕ}
    (hj : j < S.nch) {u : ℕ} (hu : u ∈ S.walk j) : u < S.s := by
  obtain ⟨ha, -, -, he⟩ := hpre.ok.walk_mem hpre.two hpre.dec hpre.pet hj hu
  rw [(pre_of hpre).s, he]
  exact hpre.ok.sv_lt (Cl.raw_X_subset j ha)

/-- The cells of `WrJ j` lie below `h` or among the highway marks. -/
theorem wrJ_cases (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) {j a : ℕ}
    (hj : j < S.nch) (ha : S.WrJ j a) : a < S.h ∨ (S.HM ≤ a ∧ a < S.H0) := by
  have h1 : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have h2 : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  rcases ha with ⟨v, hv, rfl⟩ | ⟨v, hv, u, hu, -, rfl⟩ | ⟨u, hu, rfl⟩
  · have := hpre.ok.n_of_mem (Cl.raw_X_subset j hv); omega
  · have hvn := hpre.ok.n_of_mem (Cl.raw_X_subset j hv)
    have hN := hpre.ok.tree.n_lt
    have huN : u < S.T.N := hu.lt_N hpre.ok.tree (by omega)
    have := (hd_under hpre.ok.tree u huN).lt_N hpre.ok.tree huN
    omega
  · have := walk_lt hpre hj hu
    have := S.HM_le_H0
    omega

/-- The threshold of a child is at least `1` and at most `θ`, and it keeps the vertices. -/
theorem next_θ {r c' : Cl} (hn : Next S.G S.P r c') (hr : 1 ≤ r.θ) :
    1 ≤ c'.θ ∧ c'.θ ≤ r.θ ∧ c'.X = r.X := by
  rcases hn with ⟨rfl, -⟩ | ⟨-, hX, -, -, -, -, h4, h1, -⟩
  · exact ⟨hr, le_rfl, rfl⟩
  · exact ⟨h1, by omega, hX⟩

/-- Child `k` does not write the label of a vertex of another piece. -/
theorem not_wrJ_lab (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {j k v : ℕ} (hj : j < S.nch) (hk : k < S.nch) (hjk : j ≠ k) (hv : v ∈ (S.raw j).X) :
    ¬ S.WrJ k (S.E.LAB + v) := by
  have h1 : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hl : RegDisj (S.E.LAB, S.G.n) (S.E.LOC, S.T.N) := hpre.lab_loc
  unfold RegDisj at hl; dsimp only at hl
  have hvn := hpre.ok.n_of_mem (Cl.raw_X_subset j hv)
  have hb := S.h_le_HM
  rintro (⟨v', hv', he⟩ | ⟨v', hv', u, hu, -, he⟩ | ⟨u, -, he⟩)
  · have : v = v' := by omega
    subst this
    exact hjk (Cl.raw_unique hj hk hv hv')
  · have hvn' := hpre.ok.n_of_mem (Cl.raw_X_subset k hv')
    have hN := hpre.ok.tree.n_lt
    have huN : u < S.T.N := hu.lt_N hpre.ok.tree (by omega)
    have := (hd_under hpre.ok.tree u huN).lt_N hpre.ok.tree huN
    omega
  · omega

/-- Child `k` does not write the local index of a vertex of another piece, at its `x`-node for
any `x` between `1` and `θ`. -/
theorem not_wrJ_loc (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    {j k v x : ℕ} (hj : j < S.nch) (hk : k < S.nch) (hjk : j ≠ k) (hv : v ∈ (S.raw j).X)
    (hx1 : 1 ≤ x) (hxθ : x ≤ S.c.θ) :
    ¬ S.WrJ k (S.E.LOC + S.T.hd S.G (S.T.top x v)) := by
  have h2 : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
  have hl : RegDisj (S.E.LAB, S.G.n) (S.E.LOC, S.T.N) := hpre.lab_loc
  unfold RegDisj at hl; dsimp only at hl
  have hvn := hpre.ok.n_of_mem (Cl.raw_X_subset j hv)
  have hN := hpre.ok.tree.n_lt
  have htN := top_lt_N hpre.ok.tree hvn hx1
  have hhd := (hd_under hpre.ok.tree _ htN).lt_N hpre.ok.tree htN
  have hb := S.h_le_HM
  rintro (⟨v', hv', he⟩ | ⟨v', hv', u, hu, hut, he⟩ | ⟨u, -, he⟩)
  · have := hpre.ok.n_of_mem (Cl.raw_X_subset k hv'); omega
  · have ht := isTop_top hpre.ok.tree hvn hx1
    have hθ := isTop_top hpre.ok.tree hvn hpre.ok.inv.one_le
    have hne := hpre.ok.hd_ne hj hk hjk hv hv' ht.1
      (IsTop.under_of_le hpre.ok.tree (by omega) hxθ ht hθ) hu hut
    exact hne (by omega)
  · omega

/-- The records of the earlier children stay in memory when child `k` writes only its own cells,
its block and the heap from `H` on. -/
theorem recs_keep (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) {H' : ℕ} {M' : ℕ → ℕ}
    (hkeep : ∀ a, ¬ (H ≤ a ∧ a < H') → ¬ (S.h + 9 * k ≤ a ∧ a < S.h + 9 * k + 9) →
      ¬ S.WrJ k a → M' a = M a) {j : ℕ} (hj : j < k) :
    RecAt S.T S.G (S.csOf j) (Rs j) S.E (RecL.read M' (S.h + 9 * j)) M' ∧
      ∀ r ∈ (RecL.read M' (S.h + 9 * j)).regs, S.H0 ≤ r.1 ∧ r.1 + r.2 ≤ H := by
  obtain ⟨hn, -, hat, hreg⟩ := hI.recs j hj
  have hjn : j < S.nch := by omega
  have hb := S.h_le_HM
  have hb2 := S.HM_le_H0
  have hH := hI.hle
  have hkn : 9 * k + 9 ≤ 9 * S.nch := by omega
  have hθj := next_θ hn (by rw [show (S.raw j).θ = S.c.θ from Cl.raw_θ j]; exact hpre.ok.inv.one_le)
  rw [show (S.raw j).θ = S.c.θ from Cl.raw_θ j] at hθj
  obtain ⟨hx1, hxθ, hXj⟩ := hθj
  have hnot : ∀ a, (a < S.h ∨ (S.HM ≤ a ∧ a < S.H0)) → ¬ S.WrJ k a →
      (a < S.h + 9 * k ∨ S.h + 9 * k + 9 ≤ a) → M' a = M a := fun a h1 h2 h3 =>
    hkeep a (by omega) (by omega) h2
  have hbk : ∀ i < 9, M' (S.h + 9 * j + i) = M (S.h + 9 * j + i) := fun i hi =>
    hkeep _ (by omega) (by omega) (fun hw => by
      rcases wrJ_cases hpre hk hw with h1 | h1 <;> omega)
  have hrd := RecL.read_congr_blk hbk
  refine ⟨RecAt.congr_blk hat hbk (fun r hr a h1 h2 => ?_) (fun p hp => ⟨?_, ?_⟩) (fun p hp => ?_)
    (fun p hp => ?_) (fun v hv => ?_) (fun v hv => ?_), fun r hr => hreg r (by rw [hrd] at hr; exact hr)⟩
  · have := hreg r hr
    exact hkeep a (by omega) (by omega) (fun hw => by
      rcases wrJ_cases hpre hk hw with h1 | h1 <;> omega)
  all_goals first
    | (have hr : (S.E.IN, 3 * S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
          simp [readRegs]
       have hm : S.E.m = S.G.m := hpre.glob.m
       first
       | have ha := safe_of_read hpre hr (a := S.E.IN + 3 * p) (by dsimp only; omega)
           (by dsimp only; omega)
         exact hkeep _ (by have := ha.1; omega) (by have := ha.1; omega) (ha.not_wrJ hpre k)
       | have ha := safe_of_read hpre hr (a := S.E.IN + 3 * p + 1) (by dsimp only; omega)
           (by dsimp only; omega)
         exact hkeep _ (by have := ha.1; omega) (by have := ha.1; omega) (ha.not_wrJ hpre k))
    | skip
  · have hr : (S.E.PW, S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
    have hm : S.E.m = S.G.m := hpre.glob.m
    have ha := safe_of_read hpre hr (a := S.E.PW + p) (by dsimp only; omega) (by dsimp only; omega)
    exact hkeep _ (by have := ha.1; omega) (by have := ha.1; omega) (ha.not_wrJ hpre k)
  · have hr : (S.E.EXP, S.E.m) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by simp [readRegs]
    have hm : S.E.m = S.G.m := hpre.glob.m
    have ha := safe_of_read hpre hr (a := S.E.EXP + p) (by dsimp only; omega) (by dsimp only; omega)
    exact hkeep _ (by have := ha.1; omega) (by have := ha.1; omega) (ha.not_wrJ hpre k)
  · rw [hXj] at hv
    have h1 : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
    have := hpre.ok.n_of_mem (Cl.raw_X_subset j hv)
    exact hnot _ (by omega) (not_wrJ_lab hpre hjn hk (by omega) hv) (by omega)
  · have hv' := hv
    rw [hXj] at hv'
    rw [hat.lab v hv]
    have h2 : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
    have hvn := hpre.ok.n_of_mem (Cl.raw_X_subset j hv')
    have hN := hpre.ok.tree.n_lt
    have htN := top_lt_N hpre.ok.tree hvn hx1
    have hhd := (hd_under hpre.ok.tree _ htN).lt_N hpre.ok.tree htN
    exact hnot _ (by omega) (not_wrJ_loc hpre hjn hk (by omega) hv' hx1 hxθ) (by omega)

end CS

end MinCostFlow.LowStretch
