module

public import MinCostFlow.LowStretch.ProgRecFrame

/-!
# The precondition of the call on a child

After the body, the recursion calls the cluster procedure on the children `0, 1, …` in order.
Before the call on child `k`, the memory `Mk` differs from the memory `Mb` after the body only
at the cells of `ChildWr` of the earlier children, at the output, and from the end of the heap of
the body on. `kidPre` shows that the precondition `RecPre` of child `k` holds then, with the heap
pointer `HEk` (the end of the heap used so far) and its part `OUTk` of the output.

The global block and the global arrays lie below `h`, apart from the labels, the local indices
and the output, so no call changes them. The record block of child `k` and its arrays lie in the
heap of the body, which the earlier children do not touch. The labels of the vertices of child
`k` and the local indices of their heads are not cells of `ChildWr` of an earlier child
(`childWr_disj`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {T : KT} {G : PG} {P : Par}

theorem RegDisj.sub_right {r : ℕ × ℕ} {a l a' l' : ℕ} (h : RegDisj r (a, l)) (h1 : a ≤ a')
    (h2 : a' + l' ≤ a + l) : RegDisj r (a', l') := by
  unfold RegDisj at h ⊢; simp only at h ⊢; omega

theorem RegDisj.sub_left {s : ℕ × ℕ} {a l a' l' : ℕ} (h : RegDisj (a, l) s) (h1 : a ≤ a')
    (h2 : a' + l' ≤ a + l) : RegDisj (a', l') s := by
  unfold RegDisj at h ⊢; simp only at h ⊢; omega

/-- The facts that the children give: each is in `c`, has threshold at most `θ` and at least
`1`, is a union of its nodes and lies in `[0, n)`. -/
theorem kid_facts (_hT : T.Ok G) {c : Cl} {D : Cl.Dec} {cs : ℕ → Cl} {Rs : ℕ → Rec}
    {E : GlobL} {h : ℕ} {M : ℕ → ℕ}
    (hkids : BodyKids T G P c D cs Rs E h M) {j : ℕ} (hj : j < D.nch) :
    (cs j).X ⊆ c.X ∧ (cs j).θ ≤ c.θ ∧ 1 ≤ (cs j).θ ∧ T.Sat G (cs j).θ (cs j).X ∧
      (cs j).X ⊆ Finset.range G.n := by
  obtain ⟨hn, -, hokj, -⟩ := hkids.2.1 j hj
  refine ⟨?_, ?_, hokj.inv.one_le, hokj.sat, hokj.sub⟩
  · rw [hn.X_eq]; exact Cl.raw_X_subset j
  · have := hn.θ_le; rw [Cl.raw_θ] at this; exact this

/-- **The precondition of the call on child `k`.** -/
theorem kidPre {w A : ℕ} {c : Cl} {R : Rec} {D : Cl.Dec} {cs : ℕ → Cl} {Rs : ℕ → Rec}
    {GB RB OUT h : ℕ} {mem Mb Mk : ℕ → ℕ} {k HEk OUTk : ℕ}
    (hpre : RecPre w A T G P c R GB RB OUT h mem)
    (hfrb : ∀ a < h, ¬ ChildWr T G c (GlobL.read mem GB) a → Mb a = mem a)
    (hkids : BodyKids T G P c D cs Rs (GlobL.read mem GB) h Mb) (hk : k < D.nch)
    (hfr : ∀ a < h, (∀ j < k, ¬ ChildWr T G (cs j) (GlobL.read mem GB) a) →
      ¬ (OUT ≤ a ∧ a < OUT + c.X.card) → Mk a = Mb a)
    (hheap : ∀ a, h ≤ a → a < Mb (h + 2) → Mk a = Mb a)
    (hlab : ∀ u < G.n, Mk ((GlobL.read mem GB).LAB + u) < T.N)
    (hloc : ∀ x < T.N, Mk ((GlobL.read mem GB).LOC + x) < 2 ^ w)
    (hz : ZeroFrom Mk HEk) (hHE : Mb (h + 2) ≤ HEk)
    (hroom : HEk + ((GlobL.read mem GB).J + 2) * recCost w A T G P (cs k) (Rs k) ≤
      h + ((GlobL.read mem GB).J + 2) * recCost w A T G P c R)
    (hout1 : OUT ≤ OUTk) (hout2 : OUTk + (cs k).X.card ≤ OUT + c.X.card) :
    RecPre w A T G P (cs k) (Rs k) GB (Mb (h + 1) + 9 * k) OUTk HEk Mk := by
  have hpar := hpre.toClPre
  have hT := hpar.glob.tree
  have hcsub := hpar.ok.sub
  have hcθ := hpar.ok.inv.one_le
  have hEn := hpar.glob.n
  have hEN := hpar.glob.N
  have hll : (GlobL.read mem GB).LAB + G.n ≤ (GlobL.read mem GB).LOC ∨ (GlobL.read mem GB).LOC + T.N ≤ (GlobL.read mem GB).LAB := by
    have := hpar.lab_loc; unfold RegDisj at this; simpa [hEn] using this
  have hfacts := fun j (hj : j < D.nch) => kid_facts (P := P) hT hkids hj
  obtain ⟨hnk, hsatk, hokk, hrecat, hb1, hb2, hregs⟩ := hkids.2.1 k hk
  set L := RecL.read Mb (Mb (h + 1) + 9 * k) with hLdef
  -- the memory after the body keeps the regions read by `c`
  have keepB : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB), ∀ i < r.2,
      Mb (r.1 + i) = mem (r.1 + i) := fun r hr i hi => by
    have := hpar.below r hr
    exact hfrb _ (by omega) (not_childWr (r := r) hT hcsub hcθ
      (hpar.lab_disj r hr) (hpar.loc_disj r hr)
      (by omega) (by omega))
  have keep : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB), ∀ i < r.2,
      Mk (r.1 + i) = mem (r.1 + i) := fun r hr i hi => by
    have hb := hpar.below r hr
    have hnc := not_childWr (r := r) (a := r.1 + i) hT hcsub hcθ
      (hpar.lab_disj r hr) (hpar.loc_disj r hr)
      (by omega) (by omega)
    have ho := hpre.out_disj r hr
    unfold RegDisj at ho
    rw [hfr _ (by omega) (fun j hj hw => hnc (childWr_mono hT (hfacts j (by omega)).1 hcsub
      (hfacts j (by omega)).2.1 (hfacts j (by omega)).2.2.1 hw)) (by omega)]
    exact keepB r hr i hi
  have hEk : GlobL.read Mk GB = (GlobL.read mem GB) :=
    GlobL.read_congr (fun i hi => keep (GB, 21) (by simp [recRegs]) i hi)
  have hEb : GlobL.read Mb GB = (GlobL.read mem GB) :=
    GlobL.read_congr (fun i hi => keepB (GB, 21) (by simp [recRegs]) i hi)
  have hglob : ∀ r ∈ globArrs (GlobL.read mem GB), r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB) := fun r hr =>
    mem_recRegs.mpr (Or.inr (Or.inr (Or.inl hr)))
  have hEokb : (GlobL.read mem GB).Ok T G P Mb := hpar.glob.congr (fun r hr i hi => keepB r (hglob r hr) i hi)
  have hEokk : (GlobL.read mem GB).Ok T G P Mk := hpar.glob.congr (fun r hr i hi => keep r (hglob r hr) i hi)
  have hh2 : h ≤ Mb (h + 2) := by omega
  -- the cells that child `k` reads among the labels and the local indices
  have hlabk : ∀ v ∈ (cs k).X, Mk ((GlobL.read mem GB).LAB + v) = Mb ((GlobL.read mem GB).LAB + v) := fun v hv => by
    have hvn := Finset.mem_range.mp ((hfacts k hk).2.2.2.2 hv)
    have hol := hpre.out_lab
    unfold RegDisj at hol; simp only at hol
    have := hpar.lab_below
    refine hfr _ (by omega) (fun j hj => ?_) (by rw [← hEn] at hol; omega)
    have hj' : j < D.nch := by omega
    exact (childWr_disj hT (hfacts j hj').2.2.2.1 (hfacts k hk).2.2.2.1
      (hfacts j hj').2.2.2.2 (hfacts k hk).2.2.2.2 (hfacts j hj').2.2.1 (hfacts k hk).2.2.1
      (fun z hz hz' => by
        obtain ⟨hnj, -⟩ := hkids.2.1 j hj'
        rw [hnj.X_eq] at hz; rw [hnk.X_eq] at hz'
        exact Cl.raw_disj hk hj hz hz') hll hv).1
  have hlock : ∀ v ∈ (cs k).X, Mk ((GlobL.read mem GB).LOC + T.hd G (T.top (cs k).θ v)) =
      Mb ((GlobL.read mem GB).LOC + T.hd G (T.top (cs k).θ v)) := fun v hv => by
    have hvn := Finset.mem_range.mp ((hfacts k hk).2.2.2.2 hv)
    have htop := KT.top_lt_N hT hvn (hfacts k hk).2.2.1
    have hhd := (KT.hd_under hT _ htop).lt_N hT htop
    have hol := hpre.out_loc
    unfold RegDisj at hol; simp only at hol
    have := hpar.loc_below
    refine hfr _ (by omega) (fun j hj => ?_) (by rw [← hEN] at hol; omega)
    have hj' : j < D.nch := by omega
    exact (childWr_disj hT (hfacts j hj').2.2.2.1 (hfacts k hk).2.2.2.1
      (hfacts j hj').2.2.2.2 (hfacts k hk).2.2.2.2 (hfacts j hj').2.2.1 (hfacts k hk).2.2.1
      (fun z hz hz' => by
        obtain ⟨hnj, -⟩ := hkids.2.1 j hj'
        rw [hnj.X_eq] at hz; rw [hnk.X_eq] at hz'
        exact Cl.raw_disj hk hj hz hz') hll hv).2
  -- the record block of child `k`
  have hLk : RecL.read Mk (Mb (h + 1) + 9 * k) = L :=
    RecL.read_congr (fun i hi => hheap _ (by omega) (by omega))
  have hsame : SameOn (recRegs GB (Mb (h + 1) + 9 * k) (GlobL.read mem GB) L) Mb Mk := by
    intro r hr i hi
    rcases mem_recRegs.mp hr with rfl | rfl | hr' | hr'
    · rw [keep (GB, 21) (by simp [recRegs]) i hi, keepB (GB, 21) (by simp [recRegs]) i hi]
    · exact hheap _ (by omega) (by simp only at hi; omega)
    · rw [keep r (hglob r hr') i hi, keepB r (hglob r hr') i hi]
    · have := hregs r hr'
      exact hheap _ (by omega) (by omega)
  have hrecat' : RecAt T G (cs k) (Rs k) (GlobL.read mem GB) L Mk := RecAt.congr hEokb hrecat hsame hlabk hlock
  -- the regions of child `k`
  have hkregs : ∀ r ∈ recRegs GB (Mb (h + 1) + 9 * k) (GlobL.read mem GB) L,
      r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB) ∨ (h + 4 ≤ r.1 ∧ r.1 + r.2 ≤ Mb (h + 2)) := by
    intro r hr
    rcases mem_recRegs.mp hr with rfl | rfl | hr' | hr'
    · exact Or.inl (by simp [recRegs])
    · exact Or.inr ⟨hb1, by simp only; omega⟩
    · exact Or.inl (hglob r hr')
    · exact Or.inr (hregs r hr')
  obtain ⟨Mw, hMw1, hMw2, hMw3⟩ := hpar.room
  have hXk : (cs k).X.card ≤ c.X.card := Finset.card_le_card (hfacts k hk).1
  have hout := hpre.out_le
  refine ⟨⟨hokk, ?_, ?_, ?_, ?_, hz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hpar.L_eq, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    try simp only [hEk, hLk]
  · exact hEokk
  · exact hrecat'
  · exact hlab
  · exact hpar.J_eq
  · intro r hr
    rcases hkregs r hr with h1 | h1
    · have := hpar.below r h1; omega
    · omega
  · have := hpar.lab_below; omega
  · have := hpar.loc_below; omega
  · exact hpar.lab_loc
  · intro r hr
    rcases hkregs r hr with h1 | h1
    · exact hpar.lab_disj r h1
    · have := hpar.lab_below
      unfold RegDisj; omega
  · intro r hr
    rcases hkregs r hr with h1 | h1
    · exact hpar.loc_disj r h1
    · have := hpar.loc_below
      unfold RegDisj; omega
  · exact ⟨Mw, hMw1, hMw2, by omega⟩
  · exact hloc
  · omega
  · intro r hr
    rcases hkregs r hr with h1 | h1
    · exact (hpre.out_disj r h1).sub_right hout1 hout2
    · unfold RegDisj; simp only; omega
  · exact hpre.out_lab.sub_left hout1 hout2
  · exact hpre.out_loc.sub_left hout1 hout2

end MinCostFlow.LowStretch
