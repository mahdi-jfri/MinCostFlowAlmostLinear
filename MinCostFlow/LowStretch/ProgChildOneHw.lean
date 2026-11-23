module

public import MinCostFlow.LowStretch.ProgChildOneC

/-!
# One child: the highway

The first call of `oneP` writes the stored highway of child `k` from the tree arrays of the petal
loop (`hwWalkP`). This file proves its precondition at the start of child `k` (`CS.hwOk`) and
reads the highway and the marks off its result (`CS.hw_of_done`, `CS.hm_of_done`). The tree
arrays are safe cells, so they still hold what the petal loop left; `PetL.Ok.walk` then says
that the path of the tree from the target is the stored highway.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem parEnd_congr {M M' : ℕ → ℕ} {PAR u : ℕ} :
    ∀ i, (∀ j < i, M (PAR + parEnd M' PAR u j) = M' (PAR + parEnd M' PAR u j)) →
      parEnd M PAR u i = parEnd M' PAR u i
  | 0, _ => rfl
  | i + 1, h => by
      rw [parEnd_succ, parEnd_succ, parEnd_congr i (fun j hj => h j (by omega)), h i (by omega)]

namespace CS

variable {S : CS} {w : ℕ} {M1 M : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The tree arrays of the petal loop still hold their values. -/
theorem keepM_tree (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) {u : ℕ} (hu : u < S.s) :
    M (S.X.PAR + u) = S.mem (S.X.PAR + u) ∧ M (S.X.PP + u) = S.mem (S.X.PP + u) ∧
      M (S.X.PF + u) = S.mem (S.X.PF + u) ∧ M (S.X.PA + u) = S.mem (S.X.PA + u) ∧
      M (S.X.PB + u) = S.mem (S.X.PB + u) := by
  have hs : S.s = S.L.s := rfl
  refine ⟨keepM_safe hT hpre hI (safe_reg hpre (r := (S.X.PAR, S.L.s)) (by simp [readRegs,
    PetL.regs]) (by omega)), keepM_safe hT hpre hI (safe_reg hpre (r := (S.X.PP, S.L.s))
    (by simp [readRegs, PetL.regs]) (by omega)), keepM_safe hT hpre hI (safe_reg hpre
    (r := (S.X.PF, S.L.s)) (by simp [readRegs, PetL.regs]) (by omega)), keepM_safe hT hpre hI
    (safe_reg hpre (r := (S.X.PA, S.L.s)) (by simp [readRegs, PetL.regs]) (by omega)),
    keepM_safe hT hpre hI (safe_reg hpre (r := (S.X.PB, S.L.s)) (by simp [readRegs, PetL.regs])
    (by omega))⟩

/-- The nodes of the path in `M` are the nodes of the tree path of child `k`. -/
theorem nd_eq (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) {i : ℕ} (hi : i ≤ S.ℓK k) :
    ((S.oneV M1 k H).hwE M).nd i =
      parEnd S.mem S.X.PAR (S.R.sv S.T S.c (S.mem (S.X.CT + k))) i := by
  refine parEnd_congr i fun j hj => (keepM_tree hpre hT hI ?_).1
  have hm : parEnd S.mem S.X.PAR (S.R.sv S.T S.c (S.mem (S.X.CT + k))) j ∈ S.walk k :=
    mem_parWalk.mpr ⟨j, lt_of_lt_of_le hj hi, rfl⟩
  exact walk_lt hpre hk hm

/-- The nodes of the tree path of child `k` are in node group `k`. -/
theorem walk_sub (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) {u : ℕ} (hu : u ∈ S.walk k) :
    u ∈ grp (S.chxF M1) S.s k := by
  have h := pre_of hpre
  obtain ⟨ha, -, -, he⟩ := hpre.ok.walk_mem hpre.two hpre.dec hpre.pet hk hu
  have hc := (hpre.ok.chx_iff hpre.pet (chxF_one hT h.nd_lt) (chxF_zero (M := M1) hT)
    (Cl.raw_X_subset k ha) hk).mp ha
  simp only [grp, List.mem_filter, List.mem_range, decide_eq_true_eq]
  refine ⟨walk_lt hpre hk hu, ?_⟩
  rw [he]; exact hc

theorem ℓK_le (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) : S.ℓK k ≤ S.sNK M1 k := by
  have hnd : (S.walk k).Nodup := (hpre.pet.walk k hk).2.2.2.2
  have hl : (S.walk k).length = S.ℓK k := length_parWalk _ _ _ _
  rw [← hl]
  exact (List.subperm_of_subset hnd fun u hu => walk_sub hpre hT hk hu).length_le

theorem hwE_flag_le {G : PG} {t : ℕ} {hw : List ℕ} {θ : ℕ} {half : Finset ℕ}
    {e : ℕ × ℕ × ℕ × ℕ} (he : e ∈ Cl.hwE G t hw θ half) : e.2.1 ≤ 1 := by
  unfold Cl.hwE at he
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp he
  dsimp only; split_ifs <;> omega

/-- **The precondition of `hwWalkP`** at the start of child `k`. -/
theorem hwOk (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hroom : H + 4 * S.ℓK k + 4 < 2 ^ w) :
    ((S.oneV M1 k H).hwE M).Ok w S.s (S.ℓK k) := by
  obtain ⟨hmap, -, hend, hnot, -⟩ := hpre.pet.walk k hk
  have hs : S.s = S.L.s := rfl
  have hreg : ∀ a, (a, S.L.s) ∈ PetL.regs S.X S.mem S.L.s → a + S.s ≤ S.h := fun a ha =>
    hpre.below (a, S.L.s) (by simp only [readRegs, List.mem_append]; exact Or.inr ha)
  have b1 := hreg S.X.PAR (by simp [PetL.regs])
  have b2 := hreg S.X.PP (by simp [PetL.regs])
  have b3 := hreg S.X.PF (by simp [PetL.regs])
  have b4 := hreg S.X.PA (by simp [PetL.regs])
  have b5 := hreg S.X.PB (by simp [PetL.regs])
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hH0 := S.HM_le_H0
  have hle := hI.hle
  have hwk : ∀ i < S.ℓK k, parEnd S.mem S.X.PAR (S.R.sv S.T S.c (S.mem (S.X.CT + k))) i ∈
      S.walk k := fun i hi => mem_parWalk.mpr ⟨i, hi, rfl⟩
  refine ⟨?_, fun i hi => ?_, fun i hi => ?_,
    ⟨show S.X.PAR + S.s ≤ S.HM by omega, show S.X.PP + S.s ≤ S.HM by omega,
      show S.X.PF + S.s ≤ S.HM by omega, show S.X.PA + S.s ≤ S.HM by omega,
      show S.X.PB + S.s ≤ S.HM by omega⟩, show S.HM + S.s ≤ H by unfold H0 at hle; omega,
    hroom, by show S.rgK k ≤ 1; unfold rgK; split_ifs <;> omega,
    fun i hi => ?_⟩
  · rw [nd_eq hpre hT hI hk le_rfl]; exact hend
  · rw [nd_eq hpre hT hI hk hi.le]
    intro he
    have := hwk i hi
    rw [he] at this
    exact hnot this
  · rw [nd_eq hpre hT hI hk hi.le]; exact walk_lt hpre hk (hwk i hi)
  · rw [nd_eq hpre hT hI hk hi.le]
    have hu := hwk i hi
    show M (S.X.PF + _) < 2 ^ w
    rw [(keepM_tree hpre hT hI (walk_lt hpre hk hu)).2.2.1]
    have hm : S.X.ent S.mem (parEnd S.mem S.X.PAR (S.R.sv S.T S.c (S.mem (S.X.CT + k))) i) ∈
        Cl.hwE S.G (S.raw k).t (S.raw k).hw S.c.θ S.c.half := by
      have hmap' : (S.walk k).map (S.X.ent S.mem) =
          Cl.hwE S.G (S.raw k).t (S.raw k).hw S.c.θ S.c.half := hmap
      rw [← hmap']; exact List.mem_map_of_mem hu
    have := hwE_flag_le hm
    have hw2 : 2 ≤ 2 ^ w := by omega
    exact lt_of_le_of_lt this (by omega)

theorem getD_mem_of_lt {α : Type} {l : List α} {i : ℕ} (h : i < l.length) (d : α) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

theorem hwE_mem_facts {G : PG} {t : ℕ} {hw : List ℕ} {θ : ℕ} {half : Finset ℕ}
    {e : ℕ × ℕ × ℕ × ℕ} (he : e ∈ Cl.hwE G t hw θ half) :
    e.2.1 = (if e.1 ∈ half then 1 else 0) ∧ θ ≤ G.pω e.1 := by
  unfold Cl.hwE at he
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
  exact ⟨rfl, by simpa using (List.mem_filter.mp hm).2⟩

/-- The entry `i` of the path in `M` is the entry `i` of the stored highway of `c`. -/
theorem ent_eq (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) {i : ℕ} (hi : i < S.ℓK k) :
    S.X.ent S.mem (((S.oneV M1 k H).hwE M).nd i) =
      (Cl.hwE S.G (S.raw k).t (S.raw k).hw S.c.θ S.c.half).getD i (0, 0, 0, 0) := by
  obtain ⟨hmap, -⟩ := hpre.pet.walk k hk
  have hmap' : (S.walk k).map (S.X.ent S.mem) =
      Cl.hwE S.G (S.raw k).t (S.raw k).hw S.c.θ S.c.half := hmap
  have hl : (S.walk k).length = S.ℓK k := length_parWalk _ _ _ _
  rw [nd_eq hpre hT hI hk hi.le, ← hmap',
    List.getD_eq_getElem _ _ (by rw [List.length_map, hl]; exact hi),
    List.getElem_map, ← parWalk_getD (mem := S.mem) hi,
    List.getD_eq_getElem _ _ (by rw [length_parWalk]; exact hi)]
  rfl

/-- **The stored highway after `hwWalkP`.** -/
theorem hw_of_done (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) {M2 : ℕ → ℕ}
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2) :
    ∀ j < S.ℓK k, M2 (H + 4 * j) = (S.hwK k j).1 ∧ M2 (H + 4 * j + 1) = (S.hwK k j).2.1 ∧
      M2 (H + 4 * j + 2) = (S.hwK k j).2.2.1 ∧ M2 (H + 4 * j + 3) = (S.hwK k j).2.2.2 := by
  intro j hj
  obtain ⟨a1, a2, a3, a4⟩ := hd.1 j hj
  have hu := (nd_eq hpre hT hI hk hj.le).trans (parWalk_getD (mem := S.mem) hj).symm
  have hu' : ((S.oneV M1 k H).hwE M).nd j ∈ S.walk k := by
    rw [hu]; exact getD_mem_of_lt (show j < (S.walk k).length by
      rw [show (S.walk k).length = S.ℓK k from length_parWalk _ _ _ _]; exact hj) _
  obtain ⟨k1, k2, k3, k4, k5⟩ := keepM_tree hpre hT hI (walk_lt hpre hk hu')
  have he := ent_eq hpre hT hI hk hj
  have hlen : j < (Cl.hwE S.G (S.raw k).t (S.raw k).hw S.c.θ S.c.half).length := hj
  have hmem := getD_mem_of_lt hlen ((0 : ℕ), (0 : ℕ), (0 : ℕ), (0 : ℕ))
  rw [← he] at hmem
  obtain ⟨hfl, hθ⟩ := hwE_mem_facts hmem
  have hK : S.hwK k j = ((S.X.ent S.mem (((S.oneV M1 k H).hwE M).nd j)).1,
      if (S.X.ent S.mem (((S.oneV M1 k H).hwE M).nd j)).1 ∈ (S.raw k).half then 1 else 0,
      (S.X.ent S.mem (((S.oneV M1 k H).hwE M).nd j)).2.2) := by
    unfold hwK
    rw [show (S.raw k).θ = S.c.θ from Cl.raw_θ k, Cl.hwE_half (half := S.c.half),
      List.getD_eq_getElem _ _ (by simpa using hlen),
      List.getElem_map, ← List.getD_eq_getElem _ (0, 0, 0, 0) hlen, ← he]
  rw [hK]
  refine ⟨a1.trans k2, a2.trans ?_, a3.trans k4, a4.trans k5⟩
  show S.rgK k ||| M (S.X.PF + _) = _
  rw [k3]
  have hmh := Cl.mem_raw_half (G := S.G) (D := S.D) (k := k) hθ
  have hp : (S.X.ent S.mem (((S.oneV M1 k H).hwE M).nd j)).1 ∈
      (S.raw k).hw.filter (fun q => S.c.θ ≤ S.G.pω q) := by
    rw [← Cl.hwE_fst S.G (S.raw k).t (S.raw k).hw S.c.θ S.c.half]
    exact List.mem_map_of_mem hmem
  change S.rgK k ||| (S.X.ent S.mem (((S.oneV M1 k H).hwE M).nd j)).2.1 = _
  rw [hfl]
  have hmh' : (S.X.ent S.mem (((S.oneV M1 k H).hwE M).nd j)).1 ∈ (S.raw k).half ↔
      (S.X.ent S.mem (((S.oneV M1 k H).hwE M).nd j)).1 ∈ S.c.half ∨ S.D.Reg k := by
    rw [show (S.raw k).half = (S.c.raw S.G S.D k).half from rfl, hmh]
    exact or_congr Iff.rfl ⟨fun h => h.1, fun h => ⟨h, hp⟩⟩
  generalize (S.X.ent S.mem (((S.oneV M1 k H).hwE M).nd j)).1 = q at hmh' ⊢
  unfold rgK
  by_cases h1 : S.D.Reg k <;> by_cases h2 : q ∈ S.c.half <;> simp [h1, h2, hmh']

/-- **The marks after `hwWalkP`.** -/
theorem hm_of_done (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) {M2 : ℕ → ℕ}
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2) : ∀ u ∈ S.walk k, M2 (S.HM + u) = S.rgK k := by
  intro u hu
  obtain ⟨i, hi, rfl⟩ := mem_parWalk.mp hu
  rw [← nd_eq hpre hT hI hk hi.le]
  exact hd.2.1 i hi

end CS

end MinCostFlow.LowStretch
