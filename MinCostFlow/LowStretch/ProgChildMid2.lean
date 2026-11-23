module

public import MinCostFlow.LowStretch.ProgChildMid

/-!
# One raw child: from the memory to the invariant

`CS.rawRecAt`: when the memory meets `MidOk`, the record of raw child `k` is in memory.
`CInv.step_raw`: if child `k` is not reset, the loop invariant holds after it.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace CS

variable {S : CS} {w : ℕ} {M1 M M6 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

theorem pre_of (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem) : S.Pre :=
  ⟨hpre.two, hpre.ok, hpre.dec, hpre.pet, hpre.recAt.arcs.s⟩

/-- The nodes of raw child `k` are `θ`-nodes of its vertices. -/
theorem nodesK_getD (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) {i : ℕ} (hi : i < S.sNK M1 k) :
    ∃ a ∈ (S.raw k).X, S.T.top S.c.θ a = (S.nodesK M1 k).getD i 0 := by
  have hi' : i < (S.nodesK M1 k).length := by rw [length_nodesK]; exact hi
  rw [List.getD_eq_getElem _ _ hi']
  exact ((pre_of hpre).nodesK_mem hT hk _).mp (List.getElem_mem hi')

/-- A cell of child `k`'s own writes below the heap is one of `WrJ k`. -/
theorem wrJ_of_loc (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) {i : ℕ} (hi : i < S.sNK M1 k) :
    S.WrJ k (S.E.LOC + S.T.hd S.G ((S.nodesK M1 k).getD i 0)) := by
  obtain ⟨a, ha, he⟩ := nodesK_getD hpre hT hk hi
  have han := hpre.ok.n_of_mem (Cl.raw_X_subset k ha)
  refine Or.inr (Or.inl ⟨a, ha, _, (isTop_top hpre.ok.tree han hpre.ok.inv.one_le).1,
    Under.refl _, by rw [he]⟩)

/-- The labels do not change while the record of a raw child is written. -/
theorem keep_lab6 (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6)
    {v : ℕ} (hv : v < S.G.n) : M6 (S.E.LAB + v) = M (S.E.LAB + v) := by
  have h1 : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hl : RegDisj (S.E.LAB, S.G.n) (S.E.LOC, S.T.N) := hpre.lab_loc
  unfold RegDisj at hl
  have hH := hI.hle
  have hb := S.h_le_HM
  have hb2 := S.HM_le_H0
  refine hmid.frame _ (by omega) (by omega) (fun u _ => by omega) (fun i hi => ?_)
  obtain ⟨a, ha, he⟩ := nodesK_getD hpre hT hk hi
  have hN := hpre.ok.tree.n_lt
  have han := hpre.ok.n_of_mem (Cl.raw_X_subset k ha)
  have htN := top_lt_N hpre.ok.tree han hpre.ok.inv.one_le
  rw [← he]
  have := (hd_under hpre.ok.tree _ htN).lt_N hpre.ok.tree htN
  dsimp only at hl
  omega

/-- The label of a vertex of child `k` is still the head of its `θ`-node. -/
theorem lab_raw (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    {v : ℕ} (hv : v ∈ (S.raw k).X) : M (S.E.LAB + v) = S.T.hd S.G (S.T.top S.c.θ v) := by
  have hvX := Cl.raw_X_subset k hv
  have hvn := hpre.ok.n_of_mem hvX
  have h1 : S.E.LAB + S.G.n ≤ S.h := hpre.lab_below
  have hl : RegDisj (S.E.LAB, S.G.n) (S.E.LOC, S.T.N) := hpre.lab_loc
  unfold RegDisj at hl
  dsimp only at hl
  have hb := S.h_le_HM
  have hb2 := S.HM_le_H0
  have hH := hI.hle
  rw [hI.frame _ ?_, hT.low (S.E.LAB + v) (by omega)]
  · exact hpre.recAt.lab v hvX
  rintro (⟨h2, -⟩ | ⟨h2, -⟩ | ⟨j, hj, hw⟩)
  · omega
  · omega
  · rcases hw with ⟨v', hv', he⟩ | ⟨v', hv', u, hu, hut, he⟩ | ⟨u, -, he⟩
    · have : v = v' := by omega
      subst this
      have hk' : k < S.D.nch := hk
      exact absurd (Cl.raw_unique (by omega) hk hv' hv) (by omega)
    · have hvn' := hpre.ok.n_of_mem (Cl.raw_X_subset j hv')
      have hN := hpre.ok.tree.n_lt
      have huN : u < S.T.N := hu.lt_N hpre.ok.tree (by omega)
      have := (hd_under hpre.ok.tree u huN).lt_N hpre.ok.tree huN
      omega
    · omega

/-- The local index of a vertex of child `k` in the new record. -/
theorem loc_raw6 (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6) {v : ℕ}
    (hv : v ∈ (S.raw k).X) :
    M6 (S.E.LOC + S.T.hd S.G (S.T.top S.c.θ v)) = (S.rawRec M1 k).sv S.T (S.raw k) v := by
  have hm : S.T.top S.c.θ v ∈ S.nodesK M1 k := ((pre_of hpre).nodesK_mem hT hk _).mpr ⟨v, hv, rfl⟩
  have hi := List.idxOf_lt_length_of_mem hm
  have he : (S.nodesK M1 k).getD ((S.nodesK M1 k).idxOf (S.T.top S.c.θ v)) 0 =
      S.T.top S.c.θ v := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_idxOf hi
  rw [length_nodesK] at hi
  have := hmid.loc _ hi
  rw [he] at this
  rw [this]
  unfold Rec.sv
  rw [show (S.raw k).θ = S.c.θ from Cl.raw_θ k]
  rfl

/-- **The record of raw child `k` is in memory.** -/
theorem rawRecAt (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch) (hmid : MidOk S M1 k H M M6) :
    RecAt S.T S.G (S.raw k) (S.rawRec M1 k) S.E (RecL.read M6 (S.h + 9 * k)) M6 := by
  rw [hmid.blk]
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hm : S.E.m = S.G.m := hG.m
  have hsafe : ∀ r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem, ∀ a, r.1 ≤ a → a < r.1 + r.2 →
      M6 a = S.mem a := fun r hr a h1 h2 =>
    keep_safe hpre hT hI hk hmid (safe_of_read hpre hr h1 h2)
  have hIN : ∀ p < S.G.m, M6 (S.E.IN + 3 * p) = S.mem (S.E.IN + 3 * p) ∧
      M6 (S.E.IN + 3 * p + 1) = S.mem (S.E.IN + 3 * p + 1) := fun p hp =>
    ⟨hsafe (S.E.IN, 3 * S.E.m) (by simp [readRegs]) _ (by dsimp only; omega)
      (by dsimp only; omega),
     hsafe (S.E.IN, 3 * S.E.m) (by simp [readRegs]) _ (by dsimp only; omega)
      (by dsimp only; omega)⟩
  have hθ : (S.raw k).θ = S.c.θ := Cl.raw_θ k
  have hhw := Cl.hwE_half (G := S.G) (S.raw k).t (S.raw k).hw S.c.θ S.c.half (S.raw k).half
  refine ⟨⟨(length_SK k).symm, (length_nodesK k).symm, fun j hj => (hmid.pr j ?_).1,
    fun j hj => (hmid.pr j ?_).2, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_,
    fun v hv => ?_, ?_⟩, fun i hi => hmid.na i ?_, (hpre.pet.cc k hk), (hpre.pet.ct k hk), ?_,
    fun j hj => ?_, fun v hv => ?_⟩
  · show j < S.cntK M1 k; rw [← length_SK]; exact hj
  · show j < S.cntK M1 k; rw [← length_SK]; exact hj
  · show M6 (S.E.IN + 3 * p) = _ ∧ M6 (S.E.IN + 3 * p + 1) = _
    rw [(hIN p hp).1, (hIN p hp).2]; exact hG.ends p hp
  · show M6 (S.E.PW + p) = _
    rw [hsafe (S.E.PW, S.E.m) (by simp [readRegs]) _ (by dsimp only; omega)
      (by dsimp only; omega)]
    exact hG.pw p hp
  · show _ = 2 ^ M6 (S.E.EXP + p)
    rw [hsafe (S.E.EXP, S.E.m) (by simp [readRegs]) _ (by dsimp only; omega)
      (by dsimp only; omega)]
    exact hG.ex p hp
  · show M6 (S.E.LOC + M6 (S.E.LAB + v)) = _
    have hvn := hpre.ok.n_of_mem (Cl.raw_X_subset k hv)
    rw [keep_lab6 hpre hT hI hk hmid hvn, lab_raw hpre hT hI hk hv]
    exact loc_raw6 hpre hT hk hmid hv
  · show (S.raw k).θ = 2 ^ S.L.lθ
    rw [hθ]; exact hpre.recAt.arcs.th
  · show i < S.sNK M1 k; rw [← length_nodesK]; exact hi
  · show S.ℓK k = _
    unfold ℓK; rw [hθ, hhw, List.length_map]
  · exact hmid.hw j hj
  · have hvn := hpre.ok.n_of_mem (Cl.raw_X_subset k hv)
    rw [keep_lab6 hpre hT hI hk hmid hvn, lab_raw hpre hT hI hk hv, hθ]

end CS

end MinCostFlow.LowStretch
