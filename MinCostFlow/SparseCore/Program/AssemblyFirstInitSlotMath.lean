module

public import MinCostFlow.SparseCore.Program.AssemblyBranchSide
import Mathlib.Tactic

/-!
# The slots of the active pairs at the init: the arithmetic (`AssemblyFirstInitSlotMath`)

The bundle side of a branch gives each active pair `(C, b)` of a component and a bucket its own
slot, one to one (`SlotMapOK`), and keeps for each component the list of the pairs
`(bucket, slot)` of its active pairs (`AsmSdMapsAt`). This file gives the arithmetic of how the
init finds them.

**The keys.** Let `comps` list the components of `G₀`, each once, and let `B` be larger than the
word `bucketCode b` of every bucket that occurs. The *key* of a pair `(C, b)` is
`c · B + bucketCode b`, where `c` is the index of `C` in `comps` (`pairKey`). Two keys of pairs
with words below `B` are equal only for equal pairs (`pairKey_inj`). The program writes, for each
core edge `e` whose component is active, the key of the pair of `e` (`slotKeys`): the component
of its tail and its bucket. At the init the pairs of these edges are the active pairs
(`mem_activePairs_init`), so the keys are the keys of the active pairs (`mem_slotKeys_iff`).

**The slots.** The program sorts the keys and removes repeats. Call the result `D`: a strictly
increasing list with the same members. The slot of a pair is the index of its key in `D`
(`slotOfD`). Then `slotOfD` maps the active pairs one to one onto `0, …, |D| - 1`
(`slotMapOK_slotOfD`).

**The lists of the components.** Since `D` is sorted, the entries of `D` with the same component
`c = D[j] / B` are consecutive (`slotSeg_iff`): they are the indices `j` from `slotSegStart D B c`,
the number of entries with a smaller component, on. So the list of component `c` is one segment of
the list of the pairs `(D[j] mod B, j)` (`cslList`, `mem_cslList_iff`, `cslList_getElem`).

The model fact behind `mem_activePairs_init`: the core graph puts each edge at the root of its
tail, and this root lies in the component of the tail (`root_mem_comp_iff`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.Bundle
open MinCostFlow.DynSpanner MinCostFlow.SparseCore.Program.Restart

/-! ## Words of buckets back to buckets -/

/-- The bucket of a word: the inverse of `bucketCode`. -/
def bucketDecode (n : ℕ) : ℤ := if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -(((n + 1) / 2 : ℕ) : ℤ)

theorem bucketCode_bucketDecode (n : ℕ) : bucketCode (bucketDecode n) = n := by
  unfold bucketDecode bucketCode
  by_cases hn : n % 2 = 0
  · simp only [hn, ↓reduceIte]
    have : (0 : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := Int.natCast_nonneg _
    simp only [this, ↓reduceIte, Int.toNat_natCast]
    omega
  · simp only [hn, ↓reduceIte]
    have hpos : 0 < (n + 1) / 2 := by omega
    have : ¬ (0 : ℤ) ≤ -(((n + 1) / 2 : ℕ) : ℤ) := by omega
    simp only [this, ↓reduceIte, neg_neg, Int.toNat_natCast]
    omega

theorem bucketCode_injective : Function.Injective bucketCode := by
  intro a b h
  unfold bucketCode at h
  split_ifs at h with ha hb hb <;> omega

theorem bucketDecode_bucketCode (b : ℤ) : bucketDecode (bucketCode b) = b :=
  bucketCode_injective (bucketCode_bucketDecode _)

/-! ## Keys of pairs -/

/-- The key of the pair `(C, b)`: the index of `C` in `comps` times `B`, plus the word of `b`. -/
noncomputable def pairKey (comps : List (Finset ℕ)) (B : ℕ) (p : Finset ℕ × ℤ) : ℕ :=
  comps.idxOf p.1 * B + bucketCode p.2

/-- Keys with remainders below `B` are equal only when their quotients and remainders are. -/
theorem key_inj {B c c' x x' : ℕ} (hx : x < B) (hx' : x' < B) (h : c * B + x = c' * B + x') :
    c = c' ∧ x = x' := by
  have hB : 0 < B := by omega
  have h1 : (c * B + x) / B = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hx, Nat.zero_add]
  have h2 : (c' * B + x') / B = c' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hx', Nat.zero_add]
  have hc : c = c' := by rw [← h1, ← h2, h]
  subst hc
  exact ⟨rfl, by omega⟩

theorem key_div {B c x : ℕ} (hx : x < B) : (c * B + x) / B = c := by
  have hB : 0 < B := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hx, Nat.zero_add]

theorem key_mod {B c x : ℕ} (hx : x < B) : (c * B + x) % B = x := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

/-- **Keys of pairs are one to one**, on pairs of members of `comps` with words below `B`. -/
theorem pairKey_inj {comps : List (Finset ℕ)} {B : ℕ} {p q : Finset ℕ × ℤ}
    (hp : p.1 ∈ comps) (hq : q.1 ∈ comps) (hbp : bucketCode p.2 < B) (hbq : bucketCode q.2 < B)
    (h : pairKey comps B p = pairKey comps B q) : p = q := by
  obtain ⟨h1, h2⟩ := key_inj hbp hbq h
  have e1 : p.1 = q.1 := by
    have := congrArg (fun i => comps[i]?) h1
    simp only [List.getElem?_idxOf hp, List.getElem?_idxOf hq, Option.some.injEq] at this
    exact this
  exact Prod.ext e1 (bucketCode_injective h2)

/-! ## The model fact: roots stay in their component -/

/-- In a rooted spanning forest of `G`, the root of a vertex lies in the component of the vertex
in `G`: the forest connects the vertex to its root, and the forest is a subgraph of `G`. -/
theorem root_mem_compOf {RF : RootedForest} {G : MGraph} (hRF : RF.IsRootedSpanningForestOf G)
    {v : ℕ} (hv : v ∈ G.V) : RF.root v ∈ compOf G v := by
  obtain ⟨hR, hconn⟩ := rootedForest_root_spec hRF hv
  exact mem_compOf_iff.mpr ⟨hRF.2.2.1 hR, connected_of_subgraph hRF.2.2.2.2 hconn⟩

/-- **The root of a vertex is in a component exactly when the vertex is.** -/
theorem root_mem_comp_iff {RF : RootedForest} {G : MGraph} (hRF : RF.IsRootedSpanningForestOf G)
    {v : ℕ} (hv : v ∈ G.V) {C : Finset ℕ} (hC : C ∈ components G) :
    RF.root v ∈ C ↔ v ∈ C := by
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hC
  have hr := mem_compOf_iff.mp (root_mem_compOf hRF hv)
  constructor
  · intro h
    obtain ⟨-, hur⟩ := mem_compOf_iff.mp h
    exact mem_compOf_iff.mpr ⟨hv, connected_trans hur (connected_symm hr.2)⟩
  · intro h
    obtain ⟨-, huv⟩ := mem_compOf_iff.mp h
    exact mem_compOf_iff.mpr ⟨hr.1, connected_trans huv hr.2⟩

/-- A component that holds a vertex is the component of that vertex. -/
theorem comp_eq_compOf {G : MGraph} {C : Finset ℕ} (hC : C ∈ components G) {v : ℕ} (hv : v ∈ C) :
    C = compOf G v := by
  obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hC
  exact compOf_eq_of_connected (mem_compOf_iff.mp hv).2

/-- **The active pairs at the init.** At the bundle state of the init, a pair `(C, b)` is active
exactly when `C` is a large component and some edge `e` of `G` outside the forest of the LSF has
its tail in `C` and the bucket `b`. The core graph puts `e` at the root of its tail, and the root is
in `C` exactly when the tail is (`root_mem_comp_iff`). -/
theorem mem_activePairs_init (lsfInit : LSFInit) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ)
    (hRF : (initCompLSFWith lsfInit G ℓ₀ k j).RF.IsRootedSpanningForestOf G)
    (hG : G.IsValid) (p : Finset ℕ × ℤ) :
    let tr := initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j
    p ∈ activePairs tr ↔ p.1 ∈ largeComps k G ∧
      ∃ e ∈ G.E, e ∉ tr.cs.lsf.F.F.E ∧ G.tail e ∈ p.1 ∧ tr.origBucket e = p.2 := by
  intro tr
  rw [mem_activePairs]
  have hC : tr.activeComps = largeComps k G := rfl
  rw [hC]
  constructor
  · rintro ⟨hl, hb⟩
    refine ⟨hl, ?_⟩
    have hb' : p.2 ∈ ((coreGraph G tr.cs.lsf).E.filter
        fun e => (coreGraph G tr.cs.lsf).tail e ∈ p.1).image tr.origBucket := hb
    obtain ⟨e, he, hbe⟩ := Finset.mem_image.mp hb'
    obtain ⟨heC, htail⟩ := Finset.mem_filter.mp he
    obtain ⟨heG, heF⟩ := Finset.mem_sdiff.mp heC
    have hpc : p.1 ∈ components G := (Finset.mem_filter.mp hl).1
    have htl : tr.cs.lsf.F.root (G.tail e) ∈ p.1 := htail
    exact ⟨e, heG, heF, (root_mem_comp_iff hRF (hG e heG).1 hpc).mp htl, hbe⟩
  · rintro ⟨hl, e, heG, heF, htl, hbe⟩
    refine ⟨hl, ?_⟩
    have hpc : p.1 ∈ components G := (Finset.mem_filter.mp hl).1
    show p.2 ∈ ((coreGraph G tr.cs.lsf).E.filter
        fun e => (coreGraph G tr.cs.lsf).tail e ∈ p.1).image tr.origBucket
    refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨heG, heF⟩, ?_⟩,
      hbe⟩
    exact (root_mem_comp_iff hRF (hG e heG).1 hpc).mpr htl

/-! ## The keys of the core edges -/

/-- The index of the component of the tail of `e` in `comps`. -/
noncomputable def tailComp (comps : List (Finset ℕ)) (G : MGraph) (e : ℕ) : ℕ :=
  comps.idxOf (compOf G (G.tail e))

/-- An edge whose key the program writes: an edge outside the forest edges `Fe` whose tail lies in
a large component. -/
def SlotCoreAct (G : MGraph) (Fe : Finset ℕ) (k e : ℕ) : Prop :=
  e ∉ Fe ∧ compOf G (G.tail e) ∈ largeComps k G

/-- **The keys of the core edges** of the active components, in the order of the edge list `eL`:
for such an edge `e`, the key of the pair of the component of its tail and its bucket. -/
noncomputable def slotKeys (comps : List (Finset ℕ)) (G : MGraph) (Fe : Finset ℕ) (k B : ℕ)
    (orig : ℕ → ℤ) (eL : List ℕ) : List ℕ :=
  open Classical in
  (eL.filter fun e => decide (SlotCoreAct G Fe k e)).map fun e =>
    tailComp comps G e * B + bucketCode (orig e)

/-- The hypotheses on the inputs of the keys: `comps` lists the components of `G` once each, `eL`
lists the edges of `G`, the words of the buckets of the edges are below `B`, and the pairs of the
model are those of `mem_activePairs_init`. -/
structure SlotKeyHyps {depth : ℕ} (tr : BundleTreeState depth) (comps : List (Finset ℕ))
    (G : MGraph) (Fe : Finset ℕ) (k B : ℕ) (eL : List ℕ) : Prop where
  valid : G.IsValid
  nodup : comps.Nodup
  comps_iff : ∀ C, C ∈ comps ↔ C ∈ components G
  eL_iff : ∀ e, e ∈ eL ↔ e ∈ G.E
  code_lt : ∀ e ∈ G.E, bucketCode (tr.origBucket e) < B
  act_iff : ∀ p, p ∈ activePairs tr ↔ p.1 ∈ largeComps k G ∧
    ∃ e ∈ G.E, e ∉ Fe ∧ G.tail e ∈ p.1 ∧ tr.origBucket e = p.2

section Keys

variable {depth : ℕ} {tr : BundleTreeState depth} {comps : List (Finset ℕ)} {G : MGraph}
  {Fe : Finset ℕ} {k B : ℕ} {eL : List ℕ}

theorem SlotKeyHyps.tail_comp (H : SlotKeyHyps tr comps G Fe k B eL) {e : ℕ} (he : e ∈ G.E) :
    compOf G (G.tail e) ∈ comps :=
  (H.comps_iff _).mpr (compOf_mem_components (H.valid e he).1)

/-- An active pair has a member of `comps` and a word below `B`. -/
theorem SlotKeyHyps.of_active (H : SlotKeyHyps tr comps G Fe k B eL) {p : Finset ℕ × ℤ}
    (hp : p ∈ activePairs tr) : p.1 ∈ comps ∧ bucketCode p.2 < B := by
  obtain ⟨hl, e, heG, -, -, hbe⟩ := (H.act_iff p).mp hp
  exact ⟨(H.comps_iff _).mpr (Finset.mem_filter.mp hl).1, hbe ▸ H.code_lt e heG⟩

/-- **The keys are the keys of the active pairs.** -/
theorem mem_slotKeys_iff (H : SlotKeyHyps tr comps G Fe k B eL) (x : ℕ) :
    x ∈ slotKeys comps G Fe k B tr.origBucket eL ↔
      ∃ p ∈ activePairs tr, pairKey comps B p = x := by
  classical
  unfold slotKeys
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e, ⟨heL, hF, hl⟩, rfl⟩
    have heG := (H.eL_iff e).mp heL
    refine ⟨(compOf G (G.tail e), tr.origBucket e), (H.act_iff _).mpr ⟨hl, e, heG, hF,
      self_mem_compOf (H.valid e heG).1, rfl⟩, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hl, e, heG, hF, htl, hbe⟩ := (H.act_iff p).mp hp
    have hpc : p.1 ∈ components G := (Finset.mem_filter.mp hl).1
    have hpe : p.1 = compOf G (G.tail e) := comp_eq_compOf hpc htl
    refine ⟨e, ⟨(H.eL_iff e).mpr heG, hF, hpe ▸ hl⟩, ?_⟩
    simp only [pairKey, tailComp, ← hpe, hbe]

theorem slotKeys_length_le (comps : List (Finset ℕ)) (G : MGraph) (Fe : Finset ℕ) (k B : ℕ)
    (orig : ℕ → ℤ) (eL : List ℕ) : (slotKeys comps G Fe k B orig eL).length ≤ eL.length := by
  unfold slotKeys
  rw [List.length_map]
  exact List.length_filter_le _ _

/-! ## The slots -/

/-- The slot of a pair: the index of its key in the sorted list `D` of the keys without repeats. -/
noncomputable def slotOfD (comps : List (Finset ℕ)) (B : ℕ) (D : List ℕ) (p : Finset ℕ × ℤ) : ℕ :=
  D.idxOf (pairKey comps B p)

/-- **The slots of the active pairs.** If `D` has no repeats and the same members as the keys,
then the slot map sends the active pairs one to one onto the slots `0, …, |D| - 1`. -/
theorem slotMapOK_slotOfD (H : SlotKeyHyps tr comps G Fe k B eL) {D : List ℕ} (hnd : D.Nodup)
    (hD : ∀ x, x ∈ D ↔ x ∈ slotKeys comps G Fe k B tr.origBucket eL) {slotCap cap : ℕ}
    (hcap : D.length ≤ slotCap) (hcap' : D.length ≤ cap) :
    SlotMapOK tr slotCap cap (List.range D.length) (slotOfD comps B D) := by
  have hmem : ∀ p ∈ activePairs tr, pairKey comps B p ∈ D := fun p hp =>
    (hD _).mpr ((mem_slotKeys_iff H _).mpr ⟨p, hp, rfl⟩)
  refine ⟨List.nodup_range, fun p hp => ?_, fun s hs => ?_, fun p hp q hq hpq => ?_,
    fun s hs => ?_⟩
  · exact List.mem_range.mpr (List.idxOf_lt_length_of_mem (hmem p hp))
  · have hs' := List.mem_range.mp hs
    obtain ⟨p, hp, hpk⟩ := (mem_slotKeys_iff H _).mp ((hD _).mp (List.getElem_mem hs'))
    refine ⟨p, hp, ?_⟩
    unfold slotOfD
    rw [hpk]
    exact List.Nodup.idxOf_getElem hnd s hs'
  · have h1 := hmem p hp
    have h2 := hmem q hq
    unfold slotOfD at hpq
    have hk : pairKey comps B p = pairKey comps B q := by
      have e1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem h1)
      have e2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem h2)
      simp only [hpq] at e1
      exact e1.symm.trans e2
    obtain ⟨hp1, hp2⟩ := H.of_active hp
    obtain ⟨hq1, hq2⟩ := H.of_active hq
    exact pairKey_inj hp1 hq1 hp2 hq2 hk
  · have := List.mem_range.mp hs
    exact ⟨by omega, by omega⟩

/-! ## The lists of the components -/

/-- The list of the pairs `(bucket, slot)` of component `c`: the entries `j` of `D` whose key has
the component `c`, with the bucket of the key. -/
def cslList (D : List ℕ) (B c : ℕ) : List (ℤ × ℕ) :=
  ((List.range D.length).filter fun j => D.getD j 0 / B = c).map fun j =>
    (bucketDecode (D.getD j 0 % B), j)

theorem cslList_nodup (D : List ℕ) (B c : ℕ) : (cslList D B c).Nodup := by
  unfold cslList
  refine List.Nodup.map_on ?_ (List.nodup_range.filter _)
  intro a _ b _ h
  exact (Prod.mk.inj h).2

/-- **The list of component `c` holds its active pairs**, each with its slot. -/
theorem mem_cslList_iff (H : SlotKeyHyps tr comps G Fe k B eL) {D : List ℕ} (hnd : D.Nodup)
    (hD : ∀ x, x ∈ D ↔ x ∈ slotKeys comps G Fe k B tr.origBucket eL) {c : ℕ}
    (hc : c < comps.length) (b : ℤ) (t : ℕ) :
    (b, t) ∈ cslList D B c ↔
      (comps[c], b) ∈ activePairs tr ∧ t = slotOfD comps B D (comps[c], b) := by
  have hidx : comps.idxOf comps[c] = c := List.Nodup.idxOf_getElem H.nodup c hc
  unfold cslList
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨j, ⟨hj, hjc⟩, hb, rfl⟩
    have hgj : D.getD j 0 = D[j] := by simp [List.getElem?_eq_getElem hj]
    rw [hgj] at hjc hb
    obtain ⟨p, hp, hpk⟩ := (mem_slotKeys_iff H _).mp ((hD _).mp (List.getElem_mem hj))
    obtain ⟨hp1, hp2⟩ := H.of_active hp
    have hdiv : D[j] / B = comps.idxOf p.1 := by rw [← hpk]; exact key_div hp2
    have hmod : D[j] % B = bucketCode p.2 := by rw [← hpk]; exact key_mod hp2
    have hpc : p.1 = comps[c] := by
      have h1 : comps.idxOf p.1 = c := by rw [← hdiv, hjc]
      have := List.getElem_idxOf (List.idxOf_lt_length_of_mem hp1)
      simp only [h1] at this
      exact this.symm
    have hpb : p.2 = b := by rw [← hb, hmod, bucketDecode_bucketCode]
    have hpeq : p = (comps[c], b) := Prod.ext hpc hpb
    subst hpeq
    refine ⟨hp, ?_⟩
    unfold slotOfD
    rw [hpk]
    exact (List.Nodup.idxOf_getElem hnd j hj).symm
  · rintro ⟨hp, rfl⟩
    have hk : pairKey comps B (comps[c], b) ∈ D :=
      (hD _).mpr ((mem_slotKeys_iff H _).mpr ⟨_, hp, rfl⟩)
    have hj := List.idxOf_lt_length_of_mem hk
    have hgj : D.getD (D.idxOf (pairKey comps B (comps[c], b))) 0 = pairKey comps B (comps[c], b) := by
      simp [List.getElem?_eq_getElem hj, List.getElem_idxOf hj]
    obtain ⟨-, hb2⟩ := H.of_active hp
    refine ⟨D.idxOf (pairKey comps B (comps[c], b)), ⟨hj, ?_⟩, ?_, rfl⟩
    · rw [hgj]
      unfold pairKey
      rw [key_div hb2, hidx]
    · rw [hgj]
      unfold pairKey
      rw [key_mod hb2, bucketDecode_bucketCode]

/-! ## The segments of a sorted list -/

/-- On a prefix-closed property below `n`, the members below `n` are those below their count. -/
theorem lt_count_iff_of_prefix (P : ℕ → Prop) [DecidablePred P] (n : ℕ)
    (hP : ∀ i j, i ≤ j → j < n → P j → P i) (j : ℕ) (hj : j < n) :
    P j ↔ j < ((List.range n).filter fun i => decide (P i)).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append]
    have hP' : ∀ i j, i ≤ j → j < n → P j → P i := fun i j hij hjn => hP i j hij (by omega)
    by_cases hPn : P n
    · have hall : ∀ i < n, P i := fun i hi => hP i n (by omega) (by omega) hPn
      have hfil : (List.range n).filter (fun i => decide (P i)) = List.range n :=
        List.filter_eq_self.mpr fun i hi => by simpa using hall i (List.mem_range.mp hi)
      rw [hfil, List.length_range]
      simp only [List.filter_cons, hPn, decide_true, ↓reduceIte, List.filter_nil,
        List.length_singleton]
      constructor
      · intro _; omega
      · intro _
        rcases Nat.lt_or_ge j n with h | h
        · exact hall j h
        · have : j = n := by omega
          subst this; exact hPn
    · simp only [List.filter_cons, hPn, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.filter_nil, List.length_nil, Nat.add_zero]
      rcases Nat.lt_or_ge j n with h | h
      · exact ih hP' h
      · have : j = n := by omega
        subst this
        have hle := List.length_filter_le (fun i => decide (P i)) (List.range j)
        rw [List.length_range] at hle
        exact ⟨fun h' => absurd h' hPn, fun h' => by omega⟩

/-- The entries with value at most `c` split into those below `c` and those equal to `c`. -/
theorem filter_le_split (g : ℕ → ℕ) (c : ℕ) (l : List ℕ) :
    (l.filter fun i => decide (g i ≤ c)).length =
      (l.filter fun i => decide (g i < c)).length + (l.filter fun i => decide (g i = c)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h1 : g a < c
    · have h2 : g a ≠ c := by omega
      have h3 : g a ≤ c := by omega
      simp only [List.filter_cons, h1, h2, h3, decide_true, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.length_cons, ih]
      omega
    · by_cases h2 : g a = c
      · have h3 : g a ≤ c := by omega
        simp only [List.filter_cons, h2, decide_true, decide_false, Bool.false_eq_true,
          ↓reduceIte, List.length_cons, ih, lt_irrefl, le_refl]
        omega
      · have h3 : ¬ g a ≤ c := by omega
        simp only [List.filter_cons, h1, h2, h3, decide_false, Bool.false_eq_true, ↓reduceIte, ih]

/-- The start of the segment of component `c` in the sorted list `D`: the number of entries whose
component is smaller. -/
def slotSegStart (D : List ℕ) (B c : ℕ) : ℕ :=
  ((List.range D.length).filter fun j => decide (D.getD j 0 / B < c)).length

/-- The length of the segment of component `c`: the number of entries with component `c`. -/
def slotSegLen (D : List ℕ) (B c : ℕ) : ℕ :=
  ((List.range D.length).filter fun j => decide (D.getD j 0 / B = c)).length

theorem div_mono_of_sorted {D : List ℕ} (hs : D.Pairwise (· < ·)) (B : ℕ) {i j : ℕ} (hij : i ≤ j)
    (hj : j < D.length) : D.getD i 0 / B ≤ D.getD j 0 / B := by
  have hi : i < D.length := by omega
  have hgi : D.getD i 0 = D[i] := by simp [List.getElem?_eq_getElem hi]
  have hgj : D.getD j 0 = D[j] := by simp [List.getElem?_eq_getElem hj]
  rw [hgi, hgj]
  rcases Nat.eq_or_lt_of_le hij with h | h
  · subst h; exact le_refl _
  · exact Nat.div_le_div_right (le_of_lt (List.pairwise_iff_getElem.mp hs i j hi hj h))

/-- **The segment of a component.** In a strictly increasing list `D`, the entries with component
`c` are those with index from `slotSegStart D B c` to `slotSegStart D B c + slotSegLen D B c`. -/
theorem slotSeg_iff {D : List ℕ} (hs : D.Pairwise (· < ·)) (B c : ℕ) {j : ℕ}
    (hj : j < D.length) :
    D.getD j 0 / B = c ↔ slotSegStart D B c ≤ j ∧ j < slotSegStart D B c + slotSegLen D B c := by
  have hlt := lt_count_iff_of_prefix (fun j => D.getD j 0 / B < c) D.length
    (fun i j hij hj h => lt_of_le_of_lt (div_mono_of_sorted hs B hij hj) h) j hj
  have hle := lt_count_iff_of_prefix (fun j => D.getD j 0 / B ≤ c) D.length
    (fun i j hij hj h => le_trans (div_mono_of_sorted hs B hij hj) h) j hj
  have hsplit : ((List.range D.length).filter fun i => decide (D.getD i 0 / B ≤ c)).length =
      slotSegStart D B c + slotSegLen D B c := by
    unfold slotSegStart slotSegLen
    exact filter_le_split _ _ _
  rw [hsplit] at hle
  change D.getD j 0 / B < c ↔ j < slotSegStart D B c at hlt
  constructor
  · intro h
    exact ⟨Nat.le_of_not_lt fun h' => by have := hlt.mpr h'; omega, hle.mp (le_of_eq h)⟩
  · rintro ⟨h1, h2⟩
    have a := hle.mpr h2
    have b : ¬ D.getD j 0 / B < c := fun h' => by have := hlt.mp h'; omega
    omega

/-- The segment of component `c` lies inside `D`. -/
theorem slotSeg_le (D : List ℕ) (B c : ℕ) :
    slotSegStart D B c + slotSegLen D B c ≤ D.length := by
  unfold slotSegStart slotSegLen
  rw [← filter_le_split]
  have h := List.length_filter_le (fun j => decide (D.getD j 0 / B ≤ c)) (List.range D.length)
  rwa [List.length_range] at h

/-- The list of component `c` has the length of its segment. -/
theorem cslList_length (D : List ℕ) (B c : ℕ) : (cslList D B c).length = slotSegLen D B c := by
  unfold cslList slotSegLen
  rw [List.length_map]

/-- **The entries of the list of component `c`**: the `i`-th is the entry `slotSegStart + i` of
`D`. -/
theorem cslList_getElem {D : List ℕ} (hs : D.Pairwise (· < ·)) (B c : ℕ) (i : ℕ)
    (hi : i < (cslList D B c).length) :
    (cslList D B c)[i] = (bucketDecode (D.getD (slotSegStart D B c + i) 0 % B),
      slotSegStart D B c + i) := by
  have hfil : (List.range D.length).filter (fun j => decide (D.getD j 0 / B = c)) =
      List.range' (slotSegStart D B c) (slotSegLen D B c) := by
    have hle := slotSeg_le D B c
    refine List.SortedLT.eq_of_mem_iff ?_ ?_ fun j => ?_
    · exact List.sortedLT_iff_pairwise.mpr
        ((List.pairwise_lt_range (n := D.length)).filter _)
    · exact List.sortedLT_iff_pairwise.mpr List.pairwise_lt_range'
    · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, List.mem_range'_1]
      constructor
      · rintro ⟨hj, h⟩
        exact (slotSeg_iff hs B c hj).mp h
      · rintro ⟨h1, h2⟩
        have hj : j < D.length := by omega
        exact ⟨hj, (slotSeg_iff hs B c hj).mpr ⟨h1, h2⟩⟩
  have heq : cslList D B c = (List.range' (slotSegStart D B c) (slotSegLen D B c)).map fun j =>
      (bucketDecode (D.getD j 0 % B), j) := by
    unfold cslList
    rw [hfil]
  have hi' : i < ((List.range' (slotSegStart D B c) (slotSegLen D B c)).map fun j =>
      (bucketDecode (D.getD j 0 % B), j)).length := by rw [← heq]; exact hi
  have h1 : (cslList D B c)[i] = (((List.range' (slotSegStart D B c) (slotSegLen D B c)).map
      fun j => (bucketDecode (D.getD j 0 % B), j))[i]'hi') := by
    simp only [heq]
  rw [h1, List.getElem_map, List.getElem_range']
  simp only [Nat.one_mul]

end Keys

end MinCostFlow.SparseCore.Program
