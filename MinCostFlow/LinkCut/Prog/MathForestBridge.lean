module

public import MinCostFlow.LinkCut.Prog.MathForestTreeSize

/-!
# Bridge from `LctMemRep` to `MathForest` connectivity and capacity

Connects the represented parent map (`lctAuxParent`), free-slot pool, and `truncMem`
extraction under `LctMemRep` directly to `MathForest`:
- `LctMemRep` clean field projections (`edgeMap_snd_perm`, `slots_perm`, `treeMemMatch`, etc.);
- `rootAbove`: root-finding along `lctAuxParent` and exact equivalence with `MathForest.SameComp`;
- `LctMemRep.freeEdges_ne_nil_of_lt`: counting injection showing at least one free slot exists
  whenever `F.n > 0`;
- `LctMemRep.splayForestOk_trunc`, `treeRank_le_log`, `lctPhi_le_bound`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section RootAndConnectivity

/-- Climb `par` up to `k` steps, stopping as soon as `par u = 0`. -/
def rootAbove (par : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, u => u
  | k + 1, u => if par u = 0 then u else rootAbove par k (par u)

theorem rootAbove_zero_par {par : ℕ → ℕ} {cap u : ℕ}
    (hacyc : iterParent par cap u = 0) (hu0 : u ≠ 0) :
    par (rootAbove par cap u) = 0 := by
  have go : ∀ k u, iterParent par k u = 0 → u ≠ 0 → par (rootAbove par k u) = 0 := by
    intro k
    induction k with
    | zero => intro u h hu; simp [iterParent] at h; exact absurd h hu
    | succ k ih =>
        intro u h _
        by_cases hp : par u = 0
        · simp [rootAbove, hp]
        · simp only [rootAbove, hp, ↓reduceIte]
          exact ih (par u) (by simpa [iterParent] using h) hp
  exact go cap u hacyc hu0

theorem rootAbove_bounds {par : ℕ → ℕ} {cap : ℕ}
    (hle : ∀ x, 1 ≤ x → x ≤ cap → par x ≤ cap) :
    ∀ k u, 1 ≤ u → u ≤ cap → iterParent par k u = 0 →
      1 ≤ rootAbove par k u ∧ rootAbove par k u ≤ cap := by
  intro k
  induction k with
  | zero => intro u _ _ h0; simp [iterParent] at h0; omega
  | succ k ih =>
      intro u hu1 hu2 h0
      by_cases hp : par u = 0
      · simp [rootAbove, hp]; exact ⟨hu1, hu2⟩
      · simp only [rootAbove, hp, ↓reduceIte]
        exact ih (par u) (Nat.pos_of_ne_zero hp) (hle u hu1 hu2) (by simpa [iterParent] using h0)

theorem rootAbove_reachesIn {par : ℕ → ℕ} {cap : ℕ}
    (hle : ∀ x, 1 ≤ x → x ≤ cap → par x ≤ cap)
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent par cap u = 0) :
    ∀ {u : ℕ}, 1 ≤ u → u ≤ cap → reachesIn par cap u (rootAbove par cap u) = true := by
  have go : ∀ k u, 1 ≤ u → u ≤ cap → iterParent par k u = 0 → k ≤ cap →
      ∃ j < cap, iterParent par j u = rootAbove par k u := by
    intro k
    induction k with
    | zero => intro u _ _ h0 _; simp [iterParent] at h0; omega
    | succ k ih =>
        intro u hu1 hu2 h0 hle_cap
        by_cases hp : par u = 0
        · simp only [rootAbove, hp, ↓reduceIte]
          exact ⟨0, by omega, rfl⟩
        · simp only [rootAbove, hp, ↓reduceIte]
          rcases ih (par u) (Nat.pos_of_ne_zero hp) (hle u hu1 hu2)
            (by simpa [iterParent] using h0) (by omega) with ⟨j, _, hjeq⟩
          refine ⟨j + 1, ?_, ?_⟩
          · by_contra hge
            have hjc : j + 1 = cap := by omega
            have hrb := rootAbove_bounds hle k (par u) (Nat.pos_of_ne_zero hp)
              (hle u hu1 hu2) (by simpa [iterParent] using h0)
            have hc := hacyc u hu1 hu2
            rw [← hjc] at hc
            change iterParent par (j + 1) u = 0 at hc
            rw [iterParent, hjeq] at hc
            omega
          · simpa [iterParent] using hjeq
  intro u hu1 hu2
  rcases go cap u hu1 hu2 (hacyc u hu1 hu2) le_rfl with ⟨j, hj, hj_eq⟩
  simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
  exact ⟨⟨hu1, hu2⟩, j, hj, hj_eq⟩

theorem rootAbove_eq_of_reaches {par : ℕ → ℕ} {cap : ℕ}
    (hp0 : par 0 = 0) (hle : ∀ x, 1 ≤ x → x ≤ cap → par x ≤ cap)
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent par cap u = 0)
    {u r : ℕ} (hu1 : 1 ≤ u) (hu2 : u ≤ cap) (hr1 : 1 ≤ r) (hrp : par r = 0)
    (hreach : reachesIn par cap u r = true) :
    r = rootAbove par cap u := by
  have h1 := rootAbove_reachesIn hle hacyc hu1 hu2
  have hpr := rootAbove_zero_par (hacyc u hu1 hu2) (by omega)
  simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
    at hreach h1
  rcases hreach with ⟨_, k₁, _, hk₁⟩
  rcases h1 with ⟨_, k₂, _, hk₂⟩
  have hzero_ge : ∀ m z, par z = 0 → iterParent par (m + 1) z = 0 := by
    intro m z hz
    simp only [iterParent, hz, iterParent_zero_fixed hp0]
  rcases Nat.le_total k₁ k₂ with hle12 | hle21
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle12
    cases d with
    | zero => rw [Nat.add_zero] at hk₂; exact hk₁.symm.trans hk₂
    | succ d' =>
        rw [iterParent_add, hk₁, hzero_ge d' r hrp] at hk₂
        have hrb := rootAbove_bounds hle cap u hu1 hu2 (hacyc u hu1 hu2)
        omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle21
    cases d with
    | zero => rw [Nat.add_zero] at hk₁; exact hk₁.symm.trans hk₂
    | succ d' =>
        rw [iterParent_add, hk₂, hzero_ge d' _ hpr] at hk₁
        omega

theorem rootAbove_step {par : ℕ → ℕ} {cap : ℕ}
    (hp0 : par 0 = 0) (hle : ∀ x, 1 ≤ x → x ≤ cap → par x ≤ cap)
    (hacyc : ∀ u, 1 ≤ u → u ≤ cap → iterParent par cap u = 0)
    {u : ℕ} (hu1 : 1 ≤ u) (hu2 : u ≤ cap) (hpu : par u ≠ 0) :
    rootAbove par cap (par u) = rootAbove par cap u := by
  have hpu1 : 1 ≤ par u := Nat.pos_of_ne_zero hpu
  have hpu2 : par u ≤ cap := hle u hu1 hu2
  have hreach_pu := rootAbove_reachesIn hle hacyc hpu1 hpu2
  have hpr_pu := rootAbove_zero_par (hacyc (par u) hpu1 hpu2) (by omega)
  have hrb_pu := rootAbove_bounds hle cap (par u) hpu1 hpu2 (hacyc (par u) hpu1 hpu2)
  simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
    at hreach_pu
  rcases hreach_pu with ⟨_, k, _, hk_eq⟩
  have hreach_u : reachesIn par cap u (rootAbove par cap (par u)) = true := by
    simp only [reachesIn, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]
    refine ⟨⟨hu1, hu2⟩, k + 1, ?_, ?_⟩
    · by_contra hge
      have hkc : k + 1 = cap := by omega
      have hc := hacyc u hu1 hu2
      rw [← hkc] at hc
      change iterParent par (k + 1) u = 0 at hc
      rw [iterParent, hk_eq] at hc
      omega
    · simpa [iterParent] using hk_eq
  exact rootAbove_eq_of_reaches hp0 hle hacyc hu1 hu2 hrb_pu.1 hpr_pu hreach_u

end RootAndConnectivity

section MemRepSplayExtraction

theorem LctMemRep.valid {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) : F.Valid :=
  hrep.2.2.1

theorem LctMemRep.edgeFits {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) : ∀ e ∈ F.edges, EdgeFits h L P e :=
  hrep.2.2.2.1

theorem LctMemRep.edgeMap_snd_perm {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) : (x.edgeMap.map Prod.snd).Perm F.edges := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h17, _⟩
  exact h17

theorem LctMemRep.slots_perm {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) :
    ((x.edgeMap.map Prod.fst) ++ x.freeEdges).Perm ((List.range F.n).map (F.n + 1 + ·)) := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h18, _⟩
  exact h18

theorem LctMemRep.edgeMap_fst_nodup {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) : (x.edgeMap.map Prod.fst).Nodup := by
  have hnd : ((List.range F.n).map (F.n + 1 + ·)).Nodup :=
    List.nodup_range.map (fun _ _ h => by omega)
  exact (hrep.slots_perm.nodup_iff.2 hnd).of_append_left

theorem LctMemRep.free_ok {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) :
    ∀ ed ∈ x.freeEdges,
      F.n + 1 ≤ ed ∧ ed ≤ lctCap F.n ∧
      AuxTree.node ed .leaf .leaf ∈ x.trees ∧
      nodeField mem (lctNodesBase b) ed OFF_PPAR = 0 ∧
      nodeField mem (lctNodesBase b) ed OFF_ISV = 0 ∧
      nodeField mem (lctNodesBase b) ed OFF_HASE = 0 := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h20, _⟩
  exact h20

theorem LctMemRep.trees_perm {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) :
    (x.trees.flatMap AuxTree.toList).Perm ((List.range (lctCap F.n)).map (· + 1)) := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h22, _⟩
  exact h22

theorem LctMemRep.treeMemMatch {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) {t : AuxTree} (ht : t ∈ x.trees) :
    t ≠ .leaf ∧
      TreeMemMatch w h L mem (lctNodesBase b) (lctCap F.n) t 0
        (nodeField mem (lctNodesBase b) t.rootId OFF_PPAR) := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h23, _⟩
  exact ⟨(h23 t ht).1, (h23 t ht).2.2⟩

theorem LctMemRep.vertexOk {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) :
    VertexNodeOk mem (lctNodesBase b) F.n := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h24, _⟩
  exact h24

theorem LctMemRep.activeEdgeOk {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) :
    ActiveEdgeNodeOk mem (lctNodesBase b) h L P F.n x.trees x.edgeMap := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h25, _⟩
  exact h25

theorem LctMemRep.auxPathOk {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) :
    LctAuxPathOk mem (lctNodesBase b) F.n x.freeEdges x.trees := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h26, _⟩
  exact h26

theorem LctMemRep.subdivOk {w h L P b : ℕ} {F : MathForest} {x : LctConc} {mem : ℕ → ℕ}
    (hrep : LctMemRep w h L P b F x mem) :
    LctSubdivOk mem (lctNodesBase b) F.n x.freeEdges x.edgeMap := by
  rcases hrep with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h27, _⟩
  exact h27

/-- Truncated copy of `mem` below `mem (lctNodesBase b - 1)` establishing `ZeroFrom`. -/
def truncMem (mem : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  fun a => if a < mem (lctNodesBase b - 1) then mem a else 0

theorem LctMemRep.splayForestOk_trunc {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) :
    let memZ := truncMem mem b
    SplayForestOk w h L memZ (lctNodesBase b) (lctCap F.n) x.trees ∧
    MemAgreeOn b (lctArenaHi b (lctCap F.n)) mem memZ ∧
    (∀ a, a < mem (lctNodesBase b - 1) → memZ a = mem a) := by
  rcases hrep with ⟨hh_pos, hwh, _, _, _, _, _, _, _, _, _, hL, _, hhp_lo, _, hhp_w,
    _, _, _, _, hslot0, hperm, htok, _⟩
  have hnb : 3 ≤ lctNodesBase b := lctNodesBase_ge3 b
  have hhp_eq : lctNodesBase b - 1 = b + LCT_HDR_HP := by
    unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_HP; omega
  have hhp_arena : lctArenaHi b (lctCap F.n) ≤ mem (lctNodesBase b - 1) := by
    rw [hhp_eq]; exact hhp_lo
  have hmem_agree : ∀ a, a < mem (lctNodesBase b - 1) → truncMem mem b a = mem a := fun a ha => by
    simp [truncMem, ha]
  have hag_arena : MemAgreeOn b (lctArenaHi b (lctCap F.n)) mem (truncMem mem b) :=
    fun a _ ha => (hmem_agree a (lt_of_lt_of_le ha hhp_arena)).symm
  have hlt_hp : lctNodesBase b - 1 < mem (lctNodesBase b - 1) := by
    have : lctNodesBase b - 1 < lctArenaHi b (lctCap F.n) := by
      unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE; omega
    exact lt_of_lt_of_le this hhp_arena
  have hhp_trunc : truncMem mem b (lctNodesBase b - 1) = mem (lctNodesBase b - 1) :=
    hmem_agree _ hlt_hp
  have hz : ZeroFrom (truncMem mem b) (truncMem mem b (lctNodesBase b - 1)) := by
    rw [hhp_trunc]
    intro a ha
    simp [truncMem, show ¬ a < mem (lctNodesBase b - 1) by omega]
  have hlt_hdr : lctNodesBase b - 3 < mem (lctNodesBase b - 1) := by
    have : lctNodesBase b - 3 < lctArenaHi b (lctCap F.n) := by
      unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE; omega
    exact lt_of_lt_of_le this hhp_arena
  have hL_trunc : truncMem mem b (lctNodesBase b - 3) = L := by
    rw [hmem_agree _ hlt_hdr]
    have : lctNodesBase b - 3 = b + LCT_HDR_L := by
      unfold lctNodesBase LCT_HDR_SIZE LCT_HDR_L; omega
    rw [this]; exact hL
  have hheap_eq : ∀ a, lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1) ≤ a →
      a < mem (lctNodesBase b - 1) → truncMem mem b a = mem a :=
    fun a _ ha => hmem_agree a ha
  refine ⟨⟨hh_pos, hwh, hnb, ?_, hL_trunc, ?_, hz, ?_, hperm, ?_⟩, hag_arena, hmem_agree⟩
  · rw [hhp_trunc]; simpa [lctArenaHi] using hhp_arena
  · rw [hhp_trunc, hhp_eq]; exact hhp_w
  · intro off hoff
    rw [← hslot0 off hoff]
    apply hmem_agree
    have hmul : NODE_STRIDE ≤ NODE_STRIDE * (lctCap F.n + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have hlt_a : lctNodesBase b + off < lctArenaHi b (lctCap F.n) := by
      unfold lctArenaHi; omega
    exact lt_of_lt_of_le hlt_a hhp_arena
  · intro t ht
    rcases htok t ht with ⟨hne, hppw, htm⟩
    have hrt_le : t.rootId ≤ lctCap F.n := by
      have hm := hperm.mem_iff.1 (List.mem_flatMap.2 ⟨t, ht, AuxTree.rootId_mem_toList hne⟩)
      rcases List.mem_map.1 hm with ⟨y, hy, hyr⟩
      rw [List.mem_range] at hy; omega
    have hfield_rt : ∀ off < NODE_STRIDE,
        nodeField (truncMem mem b) (lctNodesBase b) t.rootId off =
        nodeField mem (lctNodesBase b) t.rootId off := fun off hoff =>
      nodeField_agree_of_memAgree rfl hag_arena hrt_le hoff
    refine ⟨hne, by rw [hfield_rt OFF_PPAR (by decide)]; exact hppw, ?_⟩
    rw [hfield_rt OFF_PPAR (by decide)]
    exact memAgree_treeMemMatch
      (fun a ha1 ha2 => hag_arena a (by unfold lctNodesBase LCT_HDR_SIZE at ha1; omega)
        (by simpa [lctArenaHi] using ha2))
      (le_of_eq hhp_trunc.symm) hheap_eq htm

theorem LctMemRep.lctTreeSeq_eq {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) {t : AuxTree} (ht : t ∈ x.trees) :
    lctTreeSeq mem (lctNodesBase b) (lctCap F.n) t.rootId =
      t.evalInorder (revFlag mem (lctNodesBase b)) false := by
  rcases hrep.splayForestOk_trunc with ⟨hsf, hag, _⟩
  have hag_nb : MemAgreeOn (lctNodesBase b) (lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1))
      mem (truncMem mem b) :=
    fun a h1 h2 => hag a (by unfold lctNodesBase LCT_HDR_SIZE at h1; omega) (by simpa [lctArenaHi] using h2)
  rw [← lctTreeSeq_agree hag_nb, hsf.lctTreeSeq_eq ht]
  apply AuxTree.evalInorder_agree
  intro u hu
  have hu_le : u ≤ lctCap F.n := by
    have hm := hsf.perm.mem_iff.1 (List.mem_flatMap.2 ⟨t, ht, hu⟩)
    rcases List.mem_map.1 hm with ⟨y, hy, hyr⟩; rw [List.mem_range] at hy; omega
  have hf := nodeField_agree_of_memAgree rfl hag hu_le (by decide : OFF_REV < NODE_STRIDE)
  simp [revFlag, hf]

theorem LctMemRep.auxParent_of_tree {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) {t : AuxTree} (ht : t ∈ x.trees) :
    let seq := lctTreeSeq mem (lctNodesBase b) (lctCap F.n) t.rootId
    ∀ i (hi : i < seq.length),
      lctAuxParent mem (lctNodesBase b) (lctCap F.n) seq[i] =
        if i = 0 then nodeField mem (lctNodesBase b) t.rootId OFF_PPAR else seq[i - 1]! := by
  rcases hrep.splayForestOk_trunc with ⟨hsf, hag, _⟩
  have haux_ok := hrep.auxPathOk
  have hag_nb : MemAgreeOn (lctNodesBase b) (lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1))
      mem (truncMem mem b) :=
    fun a h1 h2 => hag a (by unfold lctNodesBase LCT_HDR_SIZE at h1; omega) (by simpa [lctArenaHi] using h2)
  have hpp_le : ∀ s ∈ x.trees, nodeField (truncMem mem b) (lctNodesBase b) s.rootId OFF_PPAR ≤ lctCap F.n := by
    intro s hs
    have hne := (hsf.trees_ok s hs).1
    have hrt_le : s.rootId ≤ lctCap F.n := by
      have hm := hsf.perm.mem_iff.1 (List.mem_flatMap.2 ⟨s, hs, AuxTree.rootId_mem_toList hne⟩)
      rcases List.mem_map.1 hm with ⟨y, hy, hyr⟩; rw [List.mem_range] at hy; omega
    rw [nodeField_agree_of_memAgree rfl hag hrt_le (by decide : OFF_PPAR < NODE_STRIDE)]
    rcases (haux_ok s hs).2.1 with h0 | ⟨_, hle, _⟩ <;> omega
  have hseq_eq : lctTreeSeq (truncMem mem b) (lctNodesBase b) (lctCap F.n) t.rootId =
      lctTreeSeq mem (lctNodesBase b) (lctCap F.n) t.rootId := lctTreeSeq_agree hag_nb
  intro seq i hi
  have hi' : i < (lctTreeSeq (truncMem mem b) (lctNodesBase b) (lctCap F.n) t.rootId).length := by
    rw [hseq_eq]; exact hi
  have hpar := lctAuxParent_of_tree hsf hpp_le ht i hi'
  have hpar_eq : lctAuxParent (truncMem mem b) (lctNodesBase b) (lctCap F.n) seq[i] =
      lctAuxParent mem (lctNodesBase b) (lctCap F.n) seq[i] := lctAuxParent_agree hag_nb _
  have hrt_le : t.rootId ≤ lctCap F.n := by
    have hne := (hsf.trees_ok t ht).1
    have hm := hsf.perm.mem_iff.1 (List.mem_flatMap.2 ⟨t, ht, AuxTree.rootId_mem_toList hne⟩)
    rcases List.mem_map.1 hm with ⟨y, hy, hyr⟩; rw [List.mem_range] at hy; omega
  have hpp_eq := nodeField_agree_of_memAgree rfl hag hrt_le (by decide : OFF_PPAR < NODE_STRIDE)
  simpa only [seq, hseq_eq, hpar_eq, hpp_eq] using hpar

private theorem LctMemRep.trunc_invs {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) :
    (∀ u, 1 ≤ u → u ≤ lctCap F.n →
      iterParent (lctAuxParent (truncMem mem b) (lctNodesBase b) (lctCap F.n)) (lctCap F.n) u = 0) ∧
    LctAuxPathOk (truncMem mem b) (lctNodesBase b) F.n x.freeEdges x.trees := by
  rcases hrep.splayForestOk_trunc with ⟨hsf, hag, _⟩
  have haux := hrep.auxPathOk
  have hsub := hrep.subdivOk
  have hag_nb : MemAgreeOn (lctNodesBase b) (lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1))
      mem (truncMem mem b) :=
    fun a h1 h2 => hag a (by unfold lctNodesBase LCT_HDR_SIZE at h1; omega) (by simpa [lctArenaHi] using h2)
  refine ⟨?_, ?_⟩
  · intro u hu1 hu2
    have hpar_eq := lctAuxParent_agree hag_nb
    have hiter : ∀ k z, iterParent (lctAuxParent (truncMem mem b) (lctNodesBase b) (lctCap F.n)) k z =
        iterParent (lctAuxParent mem (lctNodesBase b) (lctCap F.n)) k z := by
      intro k; induction k with
      | zero => intro z; rfl
      | succ k ih => intro z; simp only [iterParent, hpar_eq, ih]
    rw [hiter]; exact hsub.1 u hu1 hu2
  · intro s hs
    have hne := (hsf.trees_ok s hs).1
    have hrt_le : s.rootId ≤ lctCap F.n := by
      have hm := hsf.perm.mem_iff.1 (List.mem_flatMap.2 ⟨s, hs, AuxTree.rootId_mem_toList hne⟩)
      rcases List.mem_map.1 hm with ⟨y, hy, hyr⟩; rw [List.mem_range] at hy; omega
    have hrev : s.evalInorder (revFlag (truncMem mem b) (lctNodesBase b)) false =
        s.evalInorder (revFlag mem (lctNodesBase b)) false := by
      apply AuxTree.evalInorder_agree
      intro u hu
      have hu_le : u ≤ lctCap F.n := by
        have hm := hsf.perm.mem_iff.1 (List.mem_flatMap.2 ⟨s, hs, hu⟩)
        rcases List.mem_map.1 hm with ⟨y, hy, hyr⟩; rw [List.mem_range] at hy; omega
      simp [revFlag, nodeField_agree_of_memAgree rfl hag hu_le (by decide : OFF_REV < NODE_STRIDE)]
    rw [hrev, nodeField_agree_of_memAgree rfl hag hrt_le (by decide : OFF_PPAR < NODE_STRIDE)]
    exact haux s hs

theorem LctMemRep.treeRank_le_log {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) {t : AuxTree} (ht : t ∈ x.trees) :
    t.rank (lctVSize mem (lctNodesBase b) (lctCap F.n)) ≤ Nat.log 2 (F.n + 2) + 1 := by
  rcases hrep.splayForestOk_trunc with ⟨hsf, hag, _⟩
  rcases hrep.trunc_invs with ⟨hacyc_z, haux_z⟩
  have hag_nb : MemAgreeOn (lctNodesBase b) (lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1))
      mem (truncMem mem b) :=
    fun a h1 h2 => hag a (by unfold lctNodesBase LCT_HDR_SIZE at h1; omega) (by simpa [lctArenaHi] using h2)
  have hrk := treeRank_le_log_of_invs hsf hacyc_z haux_z ht
  have hv_eq := lctVSize_agree hag_nb
  have hts : ∀ s : AuxTree, s.treeSize (lctVSize mem (lctNodesBase b) (lctCap F.n)) =
      s.treeSize (lctVSize (truncMem mem b) (lctNodesBase b) (lctCap F.n)) := by
    intro s; induction s with
    | leaf => rfl
    | node id l r ihl ihr => simp [AuxTree.treeSize, hv_eq id, ihl, ihr]
  simpa [AuxTree.rank, hts t] using hrk

theorem LctMemRep.lctPhi_le_bound {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) :
    lctPhi L mem b F.n ≤ 2 * (K_SPLAY_STEP L + C_HEAVY L) * F.n * (Nat.log 2 (F.n + 2) + 1) := by
  rcases hrep.splayForestOk_trunc with ⟨hsf, hag, _⟩
  rcases hrep.trunc_invs with ⟨hacyc_z, haux_z⟩
  have hag_nb : MemAgreeOn (lctNodesBase b) (lctNodesBase b + NODE_STRIDE * (lctCap F.n + 1))
      mem (truncMem mem b) :=
    fun a h1 h2 => hag a (by unfold lctNodesBase LCT_HDR_SIZE at h1; omega) (by simpa [lctArenaHi] using h2)
  have hbd := lctPhi_le_bound_of_invs hsf hacyc_z haux_z
  have hphi_eq : lctPhi L (truncMem mem b) b F.n = lctPhi L mem b F.n :=
    lctPhi_agree (by simpa [lctArenaHi] using hag_nb)
  rwa [← hphi_eq]

end MemRepSplayExtraction

section ForestCompAndFreePool

theorem LctMemRep.sameComp_of_rootAbove {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) :
    ∀ {v : ℕ}, v < F.n →
      let par := lctAuxParent mem (lctNodesBase b) (lctCap F.n)
      let r := rootAbove par (lctCap F.n) (v + 1)
      1 ≤ r ∧ r ≤ F.n ∧ par r = 0 ∧ F.SameComp v (r - 1) := by
  let par := lctAuxParent mem (lctNodesBase b) (lctCap F.n)
  let cap := lctCap F.n
  have hp0 : par 0 = 0 := lctAuxParent_zero mem (lctNodesBase b) cap
  have hle : ∀ z, 1 ≤ z → z ≤ cap → par z ≤ cap := fun z _ _ =>
    lctAuxParent_le_cap mem (lctNodesBase b) cap z
  have hsub := hrep.subdivOk
  have hacyc := hsub.1
  have hv_par := hsub.2.2.1
  have he_par := hsub.2.2.2
  have hval := hrep.valid
  have hedge_snd := hrep.edgeMap_snd_perm
  have hf_lt : ∀ p ∈ x.edgeMap, p.2.u < F.n ∧ p.2.v < F.n ∧ p.2.u ≠ p.2.v := fun p hp =>
    hval.1 p.2 (hedge_snd.mem_iff.1 (List.mem_map.2 ⟨p, hp, rfl⟩))
  have hslot_bd : ∀ p ∈ x.edgeMap, F.n + 1 ≤ p.1 ∧ p.1 ≤ cap := fun p hp => by
    have hm := hrep.slots_perm.mem_iff.1
      (List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩))
    rcases List.mem_map.1 hm with ⟨i, hi, hei⟩
    rw [List.mem_range] at hi
    dsimp only [cap, lctCap]; omega
  have hm_step : ∀ m v, v < F.n → iterParent par m (v + 1) = 0 →
      1 ≤ rootAbove par cap (v + 1) ∧ rootAbove par cap (v + 1) ≤ F.n ∧
      par (rootAbove par cap (v + 1)) = 0 ∧ F.SameComp v (rootAbove par cap (v + 1) - 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro v hv hm0
        by_cases hpz : par (v + 1) = 0
        · have hrb : rootAbove par cap (v + 1) = v + 1 := by
            have hcap_pos : 1 ≤ cap := by dsimp only [cap, lctCap]; omega
            cases hc : cap with
            | zero => omega
            | succ k => simp [rootAbove, hpz]
          rw [hrb]
          exact ⟨by omega, by omega, hpz, MathForest.SameComp.refl F v⟩
        · rcases hv_par v hv with h0 | ⟨p, hp_in, hinc, hpv⟩
          · exact absurd h0 hpz
          · have hlt := hf_lt p hp_in
            have hp_bd := hslot_bd p hp_in
            have he_raw : p.2.toRaw ∈ F.rawEdges :=
              List.mem_map.2 ⟨p.2, hedge_snd.mem_iff.1 (List.mem_map.2 ⟨p, hp_in, rfl⟩), rfl⟩
            change lctAuxParent mem (lctNodesBase b) (lctCap F.n) (v + 1) = p.1 at hpv
            change par (v + 1) = p.1 at hpv
            rcases he_par p hp_in with ⟨hpe, hpc⟩ | ⟨hpe, hpc⟩
            · change par p.1 = p.2.u + 1 at hpe
              have hv_eq : v = p.2.v := by
                rcases hinc with rfl | rfl
                · exfalso
                  have hcyc := iterParent_no_cycle (y := p.2.u + 1) (d := 2) hp0 hacyc (by omega)
                    (by dsimp only [cap, lctCap]; omega) (by omega)
                  apply hcyc
                  change par (par (p.2.u + 1)) = p.2.u + 1
                  rw [hpv, hpe]
                · rfl
              subst hv_eq
              have hstep1 : rootAbove par cap (p.2.v + 1) = rootAbove par cap (p.2.u + 1) := by
                have hs1 := rootAbove_step hp0 hle hacyc (u := p.2.v + 1) (by omega)
                  (by dsimp only [cap, lctCap]; omega) hpz
                have hs2 := rootAbove_step hp0 hle hacyc (u := p.1) (by omega) hp_bd.2
                  (by rw [hpe]; omega)
                rw [← hs1, hpv, ← hs2, hpe]
              have hm_sub : m ≥ 2 := by
                cases m with
                | zero => simp [iterParent] at hm0
                | succ m1 =>
                    cases m1 with
                    | zero =>
                        change iterParent par 1 (p.2.v + 1) = 0 at hm0
                        simp only [iterParent, hpv] at hm0
                        omega
                    | succ _ => omega
              have hm2 : iterParent par (m - 2) (p.2.u + 1) = 0 := by
                have heqm : m = 2 + (m - 2) := by omega
                rw [heqm, iterParent_add] at hm0
                simpa [iterParent, hpv, hpe] using hm0
              rcases ih (m - 2) (by omega) p.2.u hlt.1 hm2 with ⟨h1, h2, h3, hsc⟩
              rw [hstep1]
              refine ⟨h1, h2, h3, MathForest.SameComp.trans
                ⟨[p.2.toRaw], .cons he_raw (Or.inr ⟨rfl, rfl⟩) (.nil _)⟩ hsc⟩
            · change par p.1 = p.2.v + 1 at hpe
              have hv_eq : v = p.2.u := by
                rcases hinc with rfl | rfl
                · rfl
                · exfalso
                  have hcyc := iterParent_no_cycle (y := p.2.v + 1) (d := 2) hp0 hacyc (by omega)
                    (by dsimp only [cap, lctCap]; omega) (by omega)
                  apply hcyc
                  change par (par (p.2.v + 1)) = p.2.v + 1
                  rw [hpv, hpe]
              subst hv_eq
              have hstep1 : rootAbove par cap (p.2.u + 1) = rootAbove par cap (p.2.v + 1) := by
                have hs1 := rootAbove_step hp0 hle hacyc (u := p.2.u + 1) (by omega)
                  (by dsimp only [cap, lctCap]; omega) hpz
                have hs2 := rootAbove_step hp0 hle hacyc (u := p.1) (by omega) hp_bd.2
                  (by rw [hpe]; omega)
                rw [← hs1, hpv, ← hs2, hpe]
              have hm_sub : m ≥ 2 := by
                cases m with
                | zero => simp [iterParent] at hm0
                | succ m1 =>
                    cases m1 with
                    | zero =>
                        change iterParent par 1 (p.2.u + 1) = 0 at hm0
                        simp only [iterParent, hpv] at hm0
                        omega
                    | succ _ => omega
              have hm2 : iterParent par (m - 2) (p.2.v + 1) = 0 := by
                have heqm : m = 2 + (m - 2) := by omega
                rw [heqm, iterParent_add] at hm0
                simpa [iterParent, hpv, hpe] using hm0
              rcases ih (m - 2) (by omega) p.2.v hlt.2.1 hm2 with ⟨h1, h2, h3, hsc⟩
              rw [hstep1]
              refine ⟨h1, h2, h3, MathForest.SameComp.trans
                ⟨[p.2.toRaw], .cons he_raw (Or.inl ⟨rfl, rfl⟩) (.nil _)⟩ hsc⟩
  intro v hv
  exact hm_step cap v hv (hacyc (v + 1) (by omega) (by dsimp only [cap, lctCap]; omega))

theorem LctMemRep.sameComp_iff_rootAbove {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) {u v : ℕ} (hu : u < F.n) (hv : v < F.n) :
    F.SameComp u v ↔
      rootAbove (lctAuxParent mem (lctNodesBase b) (lctCap F.n)) (lctCap F.n) (u + 1) =
      rootAbove (lctAuxParent mem (lctNodesBase b) (lctCap F.n)) (lctCap F.n) (v + 1) := by
  let par := lctAuxParent mem (lctNodesBase b) (lctCap F.n)
  let cap := lctCap F.n
  have hp0 : par 0 = 0 := lctAuxParent_zero mem (lctNodesBase b) cap
  have hle : ∀ z, 1 ≤ z → z ≤ cap → par z ≤ cap := fun z _ _ =>
    lctAuxParent_le_cap mem (lctNodesBase b) cap z
  have hsub := hrep.subdivOk
  have hacyc := hsub.1
  have he_par := hsub.2.2.2
  have hval := hrep.valid
  have hedge_snd := hrep.edgeMap_snd_perm
  constructor
  · rintro ⟨es, hw⟩
    clear hu hv
    induction hw with
    | nil _ => rfl
    | @cons a b' c e es he_raw hcon hw_rest ih =>
        rcases List.mem_map.1 he_raw with ⟨fe, hfe, rfl⟩
        rcases List.mem_map.1 (hedge_snd.symm.mem_iff.1 hfe) with ⟨p, hp_in, hpe_eq⟩
        subst hpe_eq
        have hlt := hval.1 p.2 hfe
        rw [← ih]
        have hp_bd : 1 ≤ p.1 ∧ p.1 ≤ cap := by
          have hm := hrep.slots_perm.mem_iff.1
            (List.mem_append_left _ (List.mem_map.2 ⟨p, hp_in, rfl⟩))
          rcases List.mem_map.1 hm with ⟨i, hi, hei⟩
          rw [List.mem_range] at hi
          dsimp only [cap, lctCap]; omega
        have hconn_uv : rootAbove par cap (p.2.u + 1) = rootAbove par cap (p.2.v + 1) := by
          rcases he_par p hp_in with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · change par p.1 = p.2.u + 1 at h1; change par (p.2.v + 1) = p.1 at h2
            have hs1 := rootAbove_step hp0 hle hacyc (u := p.2.v + 1) (by omega)
              (by dsimp only [cap, lctCap]; omega) (by rw [h2]; omega)
            have hs2 := rootAbove_step hp0 hle hacyc hp_bd.1 hp_bd.2
              (by rw [h1]; omega)
            rw [← hs1, h2, ← hs2, h1]
          · change par p.1 = p.2.v + 1 at h1; change par (p.2.u + 1) = p.1 at h2
            have hs1 := rootAbove_step hp0 hle hacyc (u := p.2.u + 1) (by omega)
              (by dsimp only [cap, lctCap]; omega) (by rw [h2]; omega)
            have hs2 := rootAbove_step hp0 hle hacyc hp_bd.1 hp_bd.2
              (by rw [h1]; omega)
            rw [← hs1, h2, ← hs2, h1]
        rcases hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hconn_uv
        · exact hconn_uv.symm
  · intro heq
    rcases hrep.sameComp_of_rootAbove hu with ⟨_, _, _, hsc_u⟩
    rcases hrep.sameComp_of_rootAbove hv with ⟨_, _, _, hsc_v⟩
    rw [show rootAbove par cap (u + 1) = rootAbove par cap (v + 1) from heq] at hsc_u
    exact hsc_u.trans hsc_v.symm

theorem LctMemRep.findRoot_empty_edges {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) (hempty : F.edges = [])
    {v : ℕ} (hv : v < F.n) :
    rootAbove (lctAuxParent mem (lctNodesBase b) (lctCap F.n)) (lctCap F.n) (v + 1) = v + 1 := by
  have hemap : x.edgeMap = [] := by
    have hp := hrep.edgeMap_snd_perm
    rw [hempty, List.perm_nil] at hp
    exact List.eq_nil_of_map_eq_nil hp
  have hpar0 : lctAuxParent mem (lctNodesBase b) (lctCap F.n) (v + 1) = 0 := by
    rcases hrep.subdivOk.2.2.1 v hv with h0 | ⟨p, hp, _⟩
    · exact h0
    · simp [hemap] at hp
  have hcap_pos : 1 ≤ lctCap F.n := by unfold lctCap; omega
  cases hc : lctCap F.n with
  | zero => omega
  | succ k =>
      have hpar0' : lctAuxParent mem (lctNodesBase b) (k + 1) (v + 1) = 0 := by
        simpa [hc] using hpar0
      simp [rootAbove, hpar0']

theorem LctMemRep.freeEdges_ne_nil_of_lt {w h L P b : ℕ} {F : MathForest} {x : LctConc}
    {mem : ℕ → ℕ} (hrep : LctMemRep w h L P b F x mem) (hn : 0 < F.n) :
    x.freeEdges ≠ [] := by
  let par := lctAuxParent mem (lctNodesBase b) (lctCap F.n)
  let childOfEdge : ℕ × ForestEdge → ℕ := fun p =>
    if par (p.2.u + 1) = p.1 then p.2.u + 1 else p.2.v + 1
  have hsub := hrep.subdivOk
  have hval := hrep.valid
  have hedge_snd := hrep.edgeMap_snd_perm
  have hc_par : ∀ p ∈ x.edgeMap, par (childOfEdge p) = p.1 := by
    intro p hp
    dsimp only [childOfEdge]
    split_ifs with h1
    · exact h1
    · rcases hsub.2.2.2 p hp with ⟨_, hu2⟩ | ⟨_, hu2⟩
      · change par (p.2.v + 1) = p.1 at hu2; exact hu2
      · change par (p.2.u + 1) = p.1 at hu2; exact absurd hu2 h1
  have hc_in : ∀ z ∈ x.edgeMap.map childOfEdge, z ∈ (List.range F.n).map (· + 1) := by
    intro z hz
    rcases List.mem_map.1 hz with ⟨p, hp, rfl⟩
    have hlt := hval.1 p.2 (hedge_snd.mem_iff.1 (List.mem_map.2 ⟨p, hp, rfl⟩))
    dsimp only [childOfEdge]
    split_ifs
    · exact List.mem_map.2 ⟨p.2.u, List.mem_range.2 hlt.1, rfl⟩
    · exact List.mem_map.2 ⟨p.2.v, List.mem_range.2 hlt.2.1, rfl⟩
  have hfst_nd := hrep.edgeMap_fst_nodup
  have hmap_nd : x.edgeMap.Nodup := hfst_nd.of_map
  have hc_nd : (x.edgeMap.map childOfEdge).Nodup := by
    rw [List.nodup_map_iff_inj_on hmap_nd]
    intro p₁ hp₁ p₂ hp₂ heqc
    have hpe : p₁.1 = p₂.1 := by rw [← hc_par p₁ hp₁, heqc, hc_par p₂ hp₂]
    exact (List.nodup_map_iff_inj_on hmap_nd).1 hfst_nd p₁ hp₁ p₂ hp₂ hpe
  have hroot_all := hrep.sameComp_of_rootAbove hn
  dsimp only at hroot_all
  rcases hroot_all with ⟨hr1, hr2, hrp, _⟩
  let r := rootAbove (lctAuxParent mem (lctNodesBase b) (lctCap F.n)) (lctCap F.n) (0 + 1)
  have hr_in_all : r ∈ (List.range F.n).map (· + 1) :=
    List.mem_map.2 ⟨r - 1, List.mem_range.2 (by omega), by omega⟩
  have hr_notin : r ∉ x.edgeMap.map childOfEdge := by
    intro hmem
    rcases List.mem_map.1 hmem with ⟨p, hp, hpr⟩
    have hpe : p.1 ≥ F.n + 1 := by
      have hm := hrep.slots_perm.mem_iff.1
        (List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩))
      rcases List.mem_map.1 hm with ⟨i, _, hi⟩; omega
    have hcp := hc_par p hp
    change lctAuxParent mem (lctNodesBase b) (lctCap F.n) (childOfEdge p) = p.1 at hcp
    rw [hpr, hrp] at hcp
    omega
  have hsub_len : (x.edgeMap.map childOfEdge).length + 1 ≤ ((List.range F.n).map (· + 1)).length := by
    have hnd_r : (r :: x.edgeMap.map childOfEdge).Nodup := List.nodup_cons.2 ⟨hr_notin, hc_nd⟩
    have hsub_l : ∀ z ∈ r :: x.edgeMap.map childOfEdge, z ∈ (List.range F.n).map (· + 1) := by
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hzt
      · exact hr_in_all
      · exact hc_in z hzt
    simpa [List.length_cons] using List.Nodup.length_le_of_subset hnd_r hsub_l
  have hslot_len := hrep.slots_perm.length_eq
  simp only [List.length_append, List.length_map, List.length_range] at hslot_len hsub_len
  intro heq
  rw [heq, List.length_nil] at hslot_len
  omega

end ForestCompAndFreePool

end MinCostFlow.LinkCut.Prog
