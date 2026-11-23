module

public import MinCostFlow.LowStretch.ProgChildOneNc

/-!
# One child: the two sums

The fourth call of `oneP` (`smP`) adds the leaf counts `KSZ` of the nodes of child `k` and takes
the largest weight `KMW` among them. This file proves its precondition (`CS.smOk`) and that the
two results are the number of vertices of the raw child and the largest weight of a `θ`-node of
its vertices (`CS.sm_sum`, `CS.sm_mx`).

The sum is the vertex count because the raw child is a union of `θ`-nodes (`Cl.sat_raw`): its
vertices split by their `θ`-node, and the vertices with a given `θ`-node `j` are exactly the leaves
below `j` (`KT.card_eq_sum_sz`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM KT

namespace KT

variable {T : KT} {G : PG}

/-- **A union of `x`-nodes has as many vertices as the leaves of its `x`-nodes.** -/
theorem card_eq_sum_sz (h : T.Ok G) {x : ℕ} {X : Finset ℕ} (hs : T.Sat G x X)
    (hXn : X ⊆ Finset.range G.n) (hx : 1 ≤ x) :
    X.card = ∑ j ∈ X.image (T.top x), T.sz G j := by
  rw [Finset.card_eq_sum_card_image (T.top x) X]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
  unfold sz
  congr 1
  ext v
  simp only [Finset.mem_filter, mem_lv]
  have han : a < G.n := Finset.mem_range.mp (hXn ha)
  have hN := h.n_lt
  constructor
  · rintro ⟨hv, he⟩
    have hvn := Finset.mem_range.mp (hXn hv)
    refine ⟨hvn, ?_⟩
    rw [← he]
    exact (isTop_top h hvn hx).1
  · rintro ⟨hvn, hu⟩
    refine ⟨hs a ha v hvn hu, ?_⟩
    have ta := isTop_top h han hx
    exact ((IsTop.of_common h (by omega) ta ta.1 hu ta.2.1).eq_top h hvn hx).symm

end KT

/-- The entries of a list, read by index. -/
theorem image_getD_range (l : List ℕ) :
    (Finset.range l.length).image (fun i => l.getD i 0) = l.toFinset := by
  ext j
  simp only [Finset.mem_image, Finset.mem_range, List.mem_toFinset]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · intro hj
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hj
    exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩

theorem sum_getD_range {l : List ℕ} (hl : l.Nodup) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range l.length, f (l.getD i 0) = ∑ j ∈ l.toFinset, f j := by
  rw [← image_getD_range, Finset.sum_image]
  intro i hi j hj he
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  simp only at he
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at he
  exact hl.getElem_inj_iff.mp he

theorem sup_getD_range (l : List ℕ) (f : ℕ → ℕ) :
    (Finset.range l.length).sup (fun i => f (l.getD i 0)) = l.toFinset.sup f := by
  rw [← image_getD_range, Finset.sup_image]
  rfl

namespace CS

variable {S : CS} {w : ℕ} {M1 M M2 M3 M4 : ℕ → ℕ} {k H : ℕ} {Rs : ℕ → Rec}

/-- The nodes of child `k` as a set: the `θ`-nodes of its vertices. -/
theorem nodesK_toFinset (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hk : k < S.nch) :
    (S.nodesK M1 k).toFinset = (S.raw k).X.image (S.T.top S.c.θ) := by
  ext j
  rw [List.mem_toFinset, (pre_of hpre).nodesK_mem hT hk j, Finset.mem_image]

/-- **What `smP` reads.** The node cells hold the nodes of child `k`, and the cells of `KSZ` and
`KMW` still hold the leaf counts and the weights. -/
theorem sm_cells (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2)
    (hd2 : ((S.oneV M1 k H).pcE (S.ℓK k) M2).Done (S.cntK M1 k) M3)
    (hd3 : ((S.oneV M1 k H).ncE (S.ℓK k) M3).Done (S.sNK M1 k) M4) :
    (∀ i < S.sNK M1 k,
      (S.oneV M1 k H).putBlk (S.ℓK k) M4 (S.NAK M1 H k + i) = (S.nodesK M1 k).getD i 0) ∧
    (∀ j < S.T.N, (S.oneV M1 k H).putBlk (S.ℓK k) M4 (S.E.KSZ + j) = S.T.sz S.G j ∧
      (S.oneV M1 k H).putBlk (S.ℓK k) M4 (S.E.KMW + j) = S.T.mw j) := by
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hEN : S.E.N = S.T.N := hG.N
  have hBK : (S.oneV M1 k H).BK = S.h + 9 * k := rfl
  have hNAO : ((S.oneV M1 k H).ncE (S.ℓK k) M3).NAO = S.NAK M1 H k := rfl
  have hNAK : S.NAK M1 H k = H + 4 * S.ℓK k + 2 * S.cntK M1 k := rfl
  have pb : ∀ a, a < S.h → (S.oneV M1 k H).putBlk (S.ℓK k) M4 a = M4 a := fun a ha => by
    simp only [OneV.putBlk, hBK]
    split_ifs <;> omega
  have pb2 : ∀ a, H ≤ a → (S.oneV M1 k H).putBlk (S.ℓK k) M4 a = M4 a := fun a ha => by
    simp only [OneV.putBlk, hBK]
    split_ifs <;> omega
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · rw [pb2 _ (by omega), ← hNAO, hd3.1 i hi]
    exact (nc_reads hpre hT hI hk hd hd2 hi).2.1
  · have k3 : ∀ {a}, a < S.HM → M3 a = M a := fun {a} ha => by
      rw [hd2.2 a (Or.inl (by show a < H + 4 * S.ℓK k; omega))]; exact keepM2 hd hle ha
    have hloc : S.E.LOC + S.T.N ≤ S.h := hpre.loc_below
    have cell : ∀ r ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem, r.2 = S.E.N →
        (S.oneV M1 k H).putBlk (S.ℓK k) M4 (r.1 + j) = S.mem (r.1 + j) := by
      intro r hr hr2
      have bR : r.1 + r.2 ≤ S.h := hpre.below _ hr
      have dR : RegDisj r (S.E.LOC, S.T.N) := hpre.loc_disj _ hr
      unfold RegDisj at dR
      dsimp only at dR
      rw [pb _ (by omega), hd3.2.2 _ ?_]
      · show M3 (r.1 + j) = _
        rw [k3 (by omega)]
        exact keepM_safe hT hpre hI (safe_reg hpre hr (by omega))
      rintro (⟨h1, -⟩ | ⟨i, hi, he⟩)
      · rw [hNAO] at h1; omega
      · obtain ⟨-, -, hhd⟩ := nc_reads hpre hT hI hk hd hd2 hi
        rw [hhd] at he
        obtain ⟨a, ha, ea⟩ := nodesK_getD hpre hT hk hi
        have hxN : (S.nodesK M1 k).getD i 0 < S.T.N := by
          rw [← ea]
          exact KT.top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha))
            hpre.ok.inv.one_le
        have := (KT.hd_under hpre.ok.tree _ hxN).lt_N hpre.ok.tree hxN
        have e : ((S.oneV M1 k H).ncE (S.ℓK k) M3).LOC = S.E.LOC := rfl
        rw [e] at he
        omega
    have hS : (S.E.KSZ, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
      simp [readRegs]
    have hW : (S.E.KMW, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
      simp [readRegs]
    exact ⟨(cell _ hS rfl).trans (hG.sz j hj), (cell _ hW rfl).trans (hG.mw j hj)⟩

/-- **The first result of `smP`: the number of vertices of raw child `k`.** -/
theorem sm_sum (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2)
    (hd2 : ((S.oneV M1 k H).pcE (S.ℓK k) M2).Done (S.cntK M1 k) M3)
    (hd3 : ((S.oneV M1 k H).ncE (S.ℓK k) M3).Done (S.sNK M1 k) M4) :
    ((S.oneV M1 k H).smE (S.ℓK k) ((S.oneV M1 k H).putBlk (S.ℓK k) M4)).sum (S.sNK M1 k) =
      (S.raw k).X.card := by
  obtain ⟨c1, c2⟩ := sm_cells hpre hT hI hk hd hd2 hd3
  have hnd : ∀ i < S.sNK M1 k, (S.nodesK M1 k).getD i 0 < S.T.N := fun i hi => by
    obtain ⟨a, ha, ea⟩ := nodesK_getD hpre hT hk hi
    rw [← ea]
    exact KT.top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha)) hpre.ok.inv.one_le
  have e1 : ((S.oneV M1 k H).smE (S.ℓK k) ((S.oneV M1 k H).putBlk (S.ℓK k) M4)).sum
      (S.sNK M1 k) = ∑ i ∈ Finset.range (S.nodesK M1 k).length,
        S.T.sz S.G ((S.nodesK M1 k).getD i 0) := by
    rw [length_nodesK]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi : i < S.sNK M1 k := Finset.mem_range.mp hi
    show (S.oneV M1 k H).putBlk (S.ℓK k) M4
      (S.E.KSZ + (S.oneV M1 k H).putBlk (S.ℓK k) M4 (S.NAK M1 H k + i)) = _
    rw [c1 i hi]
    exact (c2 _ (hnd i hi)).1
  rw [e1, sum_getD_range ((pre_of hpre).nodesK_nodup k), nodesK_toFinset hpre hT hk]
  have hs : S.T.Sat S.G S.c.θ (S.raw k).X := Cl.sat_raw hpre.ok k
  exact (KT.card_eq_sum_sz hpre.ok.tree hs ((Cl.raw_X_subset k).trans hpre.ok.inv.sub)
    hpre.ok.inv.one_le).symm

/-- **The second result of `smP`: the largest weight of a `θ`-node of raw child `k`.** -/
theorem sm_mx (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2)
    (hd2 : ((S.oneV M1 k H).pcE (S.ℓK k) M2).Done (S.cntK M1 k) M3)
    (hd3 : ((S.oneV M1 k H).ncE (S.ℓK k) M3).Done (S.sNK M1 k) M4) :
    ((S.oneV M1 k H).smE (S.ℓK k) ((S.oneV M1 k H).putBlk (S.ℓK k) M4)).mx (S.sNK M1 k) =
      (S.raw k).X.sup (fun a => S.T.mw (S.T.top S.c.θ a)) := by
  obtain ⟨c1, c2⟩ := sm_cells hpre hT hI hk hd hd2 hd3
  have hnd : ∀ i < S.sNK M1 k, (S.nodesK M1 k).getD i 0 < S.T.N := fun i hi => by
    obtain ⟨a, ha, ea⟩ := nodesK_getD hpre hT hk hi
    rw [← ea]
    exact KT.top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha)) hpre.ok.inv.one_le
  have e1 : ((S.oneV M1 k H).smE (S.ℓK k) ((S.oneV M1 k H).putBlk (S.ℓK k) M4)).mx
      (S.sNK M1 k) = (Finset.range (S.nodesK M1 k).length).sup
        (fun i => S.T.mw ((S.nodesK M1 k).getD i 0)) := by
    rw [length_nodesK]
    refine Finset.sup_congr rfl fun i hi => ?_
    have hi : i < S.sNK M1 k := Finset.mem_range.mp hi
    show (S.oneV M1 k H).putBlk (S.ℓK k) M4
      (S.E.KMW + (S.oneV M1 k H).putBlk (S.ℓK k) M4 (S.NAK M1 H k + i)) = _
    rw [c1 i hi]
    exact (c2 _ (hnd i hi)).2
  rw [e1, sup_getD_range, nodesK_toFinset hpre hT hk, Finset.sup_image]
  rfl

/-- **The precondition of `smP`** at child `k`, after `hwWalkP`, `pcP`, `ncP` and the record
block. -/
theorem smOk (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) (hI : CInv w S M1 k H Rs M) (hk : k < S.nch)
    (hd : ((S.oneV M1 k H).hwE M).Done (S.ℓK k) M2)
    (hd2 : ((S.oneV M1 k H).pcE (S.ℓK k) M2).Done (S.cntK M1 k) M3)
    (hd3 : ((S.oneV M1 k H).ncE (S.ℓK k) M3).Done (S.sNK M1 k) M4)
    (hroom : S.OUTK M1 H k + S.sNK M1 k + 2 < 2 ^ w) :
    ((S.oneV M1 k H).smE (S.ℓK k) ((S.oneV M1 k H).putBlk (S.ℓK k) M4)).Ok w := by
  obtain ⟨c1, -⟩ := sm_cells hpre hT hI hk hd hd2 hd3
  have hle := hI.hle
  have hHM := S.HM_le_H0
  have hh : S.h + 9 * S.nch ≤ S.HM := S.h_le_HM
  have hG : S.E.Ok S.T S.G S.P S.mem := hpre.glob
  have hEN : S.E.N = S.T.N := hG.N
  have hS : (S.E.KSZ, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have hW : (S.E.KMW, S.E.N) ∈ readRegs S.GB S.RB S.XB S.E S.L S.X S.mem := by
    simp [readRegs]
  have bS : S.E.KSZ + S.E.N ≤ S.h := hpre.below _ hS
  have bW : S.E.KMW + S.E.N ≤ S.h := hpre.below _ hW
  have hOUT : S.OUTK M1 H k = H + 4 * S.ℓK k + 2 * S.cntK M1 k + S.sNK M1 k := rfl
  have hcard : (S.raw k).X.card ≤ S.G.n := by
    have hsub : (S.raw k).X ⊆ Finset.range S.G.n := (Cl.raw_X_subset k).trans hpre.ok.inv.sub
    have := Finset.card_le_card hsub
    simpa using this
  have hN := hpre.ok.tree.n_lt
  refine ⟨fun i hi => ?_, ?_, hroom⟩
  · have hi : i < S.sNK M1 k := hi
    obtain ⟨a, ha, ea⟩ := nodesK_getD hpre hT hk hi
    have hxN : (S.nodesK M1 k).getD i 0 < S.T.N := by
      rw [← ea]
      exact KT.top_lt_N hpre.ok.tree (hpre.ok.n_of_mem (Cl.raw_X_subset k ha))
        hpre.ok.inv.one_le
    change S.NAK M1 H k + i < S.OUTK M1 H k ∧
      S.E.KSZ + (S.oneV M1 k H).putBlk (S.ℓK k) M4 (S.NAK M1 H k + i) < S.OUTK M1 H k ∧
      S.E.KMW + (S.oneV M1 k H).putBlk (S.ℓK k) M4 (S.NAK M1 H k + i) < S.OUTK M1 H k
    rw [c1 i hi]
    exact ⟨by rw [hOUT]; unfold NAK SAK; omega, by omega, by omega⟩
  · show ((S.oneV M1 k H).smE (S.ℓK k) ((S.oneV M1 k H).putBlk (S.ℓK k) M4)).sum
      (S.sNK M1 k) < 2 ^ w
    rw [sm_sum hpre hT hI hk hd hd2 hd3]
    omega

end CS

end MinCostFlow.LowStretch
