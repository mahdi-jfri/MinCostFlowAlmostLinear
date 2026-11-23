module

public import MinCostFlow.LowStretch.ProgChildSpec

/-!
# The splits of a reset, in mathematics

When a child `r` of a cluster resets its threshold from `θ` to a smaller `x`, its super-vertices
change from the `θ`-nodes of its vertices to their `x`-nodes. The program finds the new nodes by
walking down the merge tree from the old ones. It keeps a stack of nodes still to look at, a list
of finished nodes and a list of split nodes. It takes a node `u` from the stack:
* if `u` was made by a merge of weight at least `x`, it splits `u`: it pushes the two children of
  `u` and records `u` as split;
* otherwise `u` is an `x`-node, and it is finished.

This file gives the invariant of this walk (`KT.SplitInv`) and what it gives at the end: the
finished nodes are the `x`-nodes of `r` (`KT.SplitInv.no_iff`), and the split nodes are the nodes
of `KT.splitSet`, each once (`KT.SplitInv.sp_toFinset`). When a node `u` is split, the program
relabels the vertices below its light child. The labels then name the head of the heavy path of
the node above each vertex (`KT.LabInv`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace KT

variable {T : KT} {G : PG}

/-- `a` and `b` have no vertex below both. -/
def Apart (T : KT) (G : PG) (a b : ℕ) : Prop := ∀ v < G.n, ¬ (T.Under v a ∧ T.Under v b)

theorem Apart.symm {a b : ℕ} (h : T.Apart G a b) : T.Apart G b a :=
  fun v hv h2 => h v hv ⟨h2.2, h2.1⟩

theorem Apart.ne (h : T.Ok G) {a b : ℕ} (ha : a < T.N) (hab : T.Apart G a b) : a ≠ b := by
  rintro rfl
  obtain ⟨v, hv, hu⟩ := exists_leaf h a ha
  exact hab v hv ⟨hu, hu⟩

/-- A node strictly above `v` has a child above `v`. -/
theorem under_child (h : T.Ok G) {v u : ℕ} (hv : v < T.N) (hu : T.Under v u) (hne : v ≠ u) :
    T.Under v (T.ch1 u) ∨ T.Under v (T.ch2 u) := by
  obtain ⟨c, hvc, hpc, hcu⟩ := child_on_path hu hne
  have hcN : c < T.N := hvc.lt_N h hv
  have hc1 : c + 1 < T.N := by
    by_contra hc
    have e : c = T.N - 1 := by omega
    rw [e, h.root] at hpc
    exact hcu (e.trans hpc)
  rcases h.par_ch c hc1 with e | e <;> rw [hpc] at e
  · exact Or.inl (e ▸ hvc)
  · exact Or.inr (e ▸ hvc)

/-- The node `u` is split at threshold `x`: it was made by a merge of weight at least `x`. -/
def SplitsAt (G : PG) (T : KT) (x u : ℕ) : Prop := G.n ≤ u ∧ x ≤ T.mw u

instance (x u : ℕ) : Decidable (T.SplitsAt G x u) := inferInstanceAs (Decidable (_ ∧ _))

/-- **The invariant of the split walk** for the child `r` and the new threshold `x`, with stack
`st`, finished nodes `no` and split nodes `sp`. -/
structure SplitInv (T : KT) (G : PG) (r : Cl) (x : ℕ) (st no sp : List ℕ) : Prop where
  st_ok : ∀ k ∈ st, k < T.N ∧ (∃ v ∈ r.X, T.Under v k ∧ T.Under k (T.top r.θ v)) ∧
    (k + 1 < T.N → x ≤ T.mw (T.par k))
  no_ok : ∀ k ∈ no, ∃ v ∈ r.X, T.IsTop x v k
  cover : ∀ v ∈ r.X, ∃ k ∈ st ++ no, T.Under v k
  apart : (st ++ no).Pairwise (T.Apart G)
  sp_mem : ∀ u ∈ sp, u ∈ T.splitSet G r x
  sp_out : ∀ u ∈ sp, ∀ k ∈ st ++ no, ¬ T.Under u k
  sp_nodup : sp.Nodup
  compl : ∀ u ∈ T.splitSet G r x, u ∈ sp ∨ ∃ k ∈ st, T.Under u k

/-- The labels `lab` name the head of the heavy path of the node above each vertex of `r`. -/
def LabInv (T : KT) (G : PG) (r : Cl) (lab : ℕ → ℕ) (fr : List ℕ) : Prop :=
  ∀ v ∈ r.X, ∀ k ∈ fr, T.Under v k → lab v = T.hd G k

open Classical in
/-- The labels after splitting `u`: the vertices below the light child of `u` get its head. -/
noncomputable def relab (T : KT) (G : PG) (u : ℕ) (lab : ℕ → ℕ) : ℕ → ℕ :=
  fun v => if T.Under v (T.light G u) then T.hd G (T.light G u) else lab v

theorem relab_of {u v : ℕ} {lab : ℕ → ℕ} (hv : T.Under v (T.light G u)) :
    T.relab G u lab v = T.hd G (T.light G u) := by
  classical
  simp only [relab]; exact ite_eq_left hv

theorem relab_of_not {u v : ℕ} {lab : ℕ → ℕ} (hv : ¬ T.Under v (T.light G u)) :
    T.relab G u lab v = lab v := by
  classical
  simp only [relab]; exact ite_eq_right hv

/-- The hypotheses on the child: a set of vertices that is a union of `θ`-nodes, and a new
threshold `1 ≤ x ≤ θ`. -/
structure SplitHyp (T : KT) (G : PG) (r : Cl) (x : ℕ) : Prop where
  ok : T.Ok G
  vx : ∀ v ∈ r.X, v < G.n
  sat : T.Sat G r.θ r.X
  x1 : 1 ≤ x
  xθ : x ≤ r.θ

variable {r : Cl} {x : ℕ}

theorem SplitHyp.isTop (H : T.SplitHyp G r x) {v : ℕ} (hv : v ∈ r.X) :
    T.IsTop r.θ v (T.top r.θ v) :=
  isTop_top H.ok (H.vx v hv) (le_trans H.x1 H.xθ)

/-- A vertex below a `θ`-node of `r` is in `r` and has that `θ`-node. -/
theorem SplitHyp.top_eq (H : T.SplitHyp G r x) {v w : ℕ} (hv : v ∈ r.X) (hw : w < G.n)
    (hu : T.Under w (T.top r.θ v)) : w ∈ r.X ∧ T.top r.θ v = T.top r.θ w := by
  have hwX : w ∈ r.X := H.sat v hv w hw hu
  have hN := H.ok.n_lt
  have ht := H.isTop hv
  exact ⟨hwX, (ht.of_common H.ok (by have := H.vx v hv; omega) ht.1 hu ht.2.1).eq_top H.ok hw
    (le_trans H.x1 H.xθ)⟩

/-- **The start of the walk**: the stack holds the `θ`-nodes of `r`, each once. -/
theorem SplitInv.init (H : T.SplitHyp G r x) {L : List ℕ} (hL : ∀ k ∈ L, ∃ v ∈ r.X, k = T.top r.θ v)
    (hL' : ∀ v ∈ r.X, T.top r.θ v ∈ L) (hnd : L.Nodup) : T.SplitInv G r x L [] [] := by
  have hN := H.ok.n_lt
  refine ⟨fun k hk => ?_, by simp, fun v hv => ⟨_, by simpa using hL' v hv, (H.isTop hv).1⟩, ?_,
    by simp, by simp, List.nodup_nil, fun u hu => ?_⟩
  · obtain ⟨v, hv, rfl⟩ := hL k hk
    have ht := H.isTop hv
    exact ⟨ht.1.lt_N H.ok (by have := H.vx v hv; omega), ⟨v, hv, ht.1, Under.refl _⟩,
      fun h1 => le_trans H.xθ (ht.2.2 h1)⟩
  · rw [List.append_nil]
    refine hnd.pairwise_of_forall_ne fun a ha b hb hab w hw ⟨h1, h2⟩ => hab ?_
    obtain ⟨va, hva, rfl⟩ := hL a ha
    obtain ⟨vb, hvb, rfl⟩ := hL b hb
    rw [(H.top_eq hva hw h1).2, (H.top_eq hvb hw h2).2]
  · right
    simp only [splitSet, Finset.mem_filter, Finset.mem_range] at hu
    obtain ⟨-, -, -, v, hv, -, hut⟩ := hu
    exact ⟨_, hL' v hv, hut⟩

/-- **A split step.** -/
theorem SplitInv.split (H : T.SplitHyp G r x) {u : ℕ} {st no sp : List ℕ}
    (I : T.SplitInv G r x (u :: st) no sp) (hs : T.SplitsAt G x u) :
    T.SplitInv G r x (T.ch1 u :: T.ch2 u :: st) no (u :: sp) := by
  have h := H.ok
  have hN := h.n_lt
  obtain ⟨huN, ⟨v0, hv0, hv0u, hut⟩, -⟩ := I.st_ok u (by simp)
  obtain ⟨hp1, hp2, hne, hlt1, hlt2⟩ := h.ch u hs.1 huN
  have hc1 : T.Under (T.ch1 u) u := under_ch1 h hs.1 huN
  have hc2 : T.Under (T.ch2 u) u := under_ch2 h hs.1 huN
  have hap := I.apart
  simp only [List.cons_append, List.pairwise_cons] at hap
  obtain ⟨hapu, haprest⟩ := hap
  -- a child of `u` is a good stack node
  have chok : ∀ c, c < u → T.Under c u → T.par c = u → c < T.N ∧
      (∃ v ∈ r.X, T.Under v c ∧ T.Under c (T.top r.θ v)) ∧ (c + 1 < T.N → x ≤ T.mw (T.par c)) := by
    intro c hcu hcU hpc
    obtain ⟨w, hw, hwc⟩ := exists_leaf h c (by omega)
    obtain ⟨hwX, he⟩ := H.top_eq hv0 hw ((hwc.trans hcU).trans hut)
    exact ⟨by omega, ⟨w, hwX, hwc, he ▸ hcU.trans hut⟩, fun _ => hpc ▸ hs.2⟩
  -- the frontier below `u` is apart from the rest
  have below : ∀ c, T.Under c u → ∀ k ∈ st ++ no, T.Apart G c k := fun c hc k hk w hw hb =>
    hapu k hk w hw ⟨hb.1.trans hc, hb.2⟩
  refine ⟨fun k hk => ?_, I.no_ok, fun v hv => ?_, ?_, fun w hw => ?_, fun w hw k hk => ?_, ?_,
    fun w hw => ?_⟩
  · simp only [List.mem_cons] at hk
    rcases hk with rfl | rfl | hk
    · exact chok _ hlt1 hc1 hp1
    · exact chok _ hlt2 hc2 hp2
    · exact I.st_ok k (by simp [hk])
  · obtain ⟨k, hk, hvk⟩ := I.cover v hv
    simp only [List.cons_append, List.mem_cons] at hk
    rcases hk with rfl | hk
    · have hvn := H.vx v hv
      rcases under_child h (by omega) hvk (by have := hs.1; omega) with h1 | h1
      · exact ⟨_, by simp, h1⟩
      · exact ⟨_, by simp, h1⟩
    · exact ⟨k, by simp [hk], hvk⟩
  · simp only [List.cons_append, List.pairwise_cons, List.mem_cons]
    refine ⟨fun k hk => ?_, fun k hk => below _ hc2 k hk, haprest⟩
    rcases hk with rfl | hk
    · exact fun w hw hb => not_under_both h hs.1 huN hb.1 hb.2
    · exact below _ hc1 k hk
  · simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp only [splitSet, Finset.mem_filter, Finset.mem_range]
      exact ⟨huN, hs.1, hs.2, v0, hv0, hv0u, hut⟩
    · exact I.sp_mem w hw
  · simp only [List.mem_cons] at hw
    simp only [List.cons_append, List.mem_cons] at hk
    rcases hw with rfl | hw
    · rcases hk with rfl | rfl | hk
      · exact fun hu => by have := hu.le h huN; omega
      · exact fun hu => by have := hu.le h huN; omega
      · intro hu
        obtain ⟨v, hv, hvw⟩ := exists_leaf h w huN
        exact hapu k hk v hv ⟨hvw, hvw.trans hu⟩
    · have hout := I.sp_out w hw
      rcases hk with rfl | rfl | hk
      · exact fun hu => hout u (by simp) (hu.trans hc1)
      · exact fun hu => hout u (by simp) (hu.trans hc2)
      · exact hout k (by simp at hk ⊢; tauto)
  · refine List.nodup_cons.mpr ⟨fun hu => I.sp_out u hu u (by simp) (Under.refl u), I.sp_nodup⟩
  · rcases I.compl w hw with h1 | ⟨k, hk, hwk⟩
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · by_cases e : w = k
      · exact Or.inl (by simp [e])
      have hwN : w < T.N := by
        simp only [splitSet, Finset.mem_filter, Finset.mem_range] at hw; exact hw.1
      rcases under_child h hwN hwk e with h1 | h1
      · exact Or.inr ⟨_, by simp, h1⟩
      · exact Or.inr ⟨_, by simp, h1⟩
    · exact Or.inr ⟨k, by simp [hk], hwk⟩

/-- **A finishing step.** -/
theorem SplitInv.keep (H : T.SplitHyp G r x) {u : ℕ} {st no sp : List ℕ}
    (I : T.SplitInv G r x (u :: st) no sp) (hs : ¬ T.SplitsAt G x u) :
    T.SplitInv G r x st (u :: no) sp := by
  have h := H.ok
  obtain ⟨huN, ⟨v0, hv0, hv0u, -⟩, hpar⟩ := I.st_ok u (by simp)
  have hmem : ∀ k, k ∈ st ++ u :: no ↔ k ∈ (u :: st) ++ no := fun k => by simp; tauto
  refine ⟨fun k hk => I.st_ok k (by simp [hk]), fun k hk => ?_, fun v hv => ?_, ?_,
    I.sp_mem, fun w hw k hk => I.sp_out w hw k ((hmem k).mp hk), I.sp_nodup, fun w hw => ?_⟩
  · simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · refine ⟨v0, hv0, hv0u, ?_, hpar⟩
      by_cases hn : G.n ≤ k
      · exact not_le.mp fun hx => hs ⟨hn, hx⟩
      · rw [h.leaf_mw k (by omega)]; exact H.x1
    · exact I.no_ok k hk
  · obtain ⟨k, hk, hvk⟩ := I.cover v hv
    exact ⟨k, (hmem k).mpr hk, hvk⟩
  · have e : (u :: st) ++ no = u :: (st ++ no) := rfl
    have hp := I.apart
    rw [e] at hp
    exact (List.perm_middle.pairwise_iff fun {a b} hab => Apart.symm hab).mpr hp
  · rcases I.compl w hw with h1 | ⟨k, hk, hwk⟩
    · exact Or.inl h1
    simp only [List.mem_cons] at hk
    rcases hk with rfl | hk
    · exfalso
      simp only [splitSet, Finset.mem_filter, Finset.mem_range] at hw
      obtain ⟨hwN, hwn, hwx, -⟩ := hw
      have := hwk.mw_le h hwN
      have := hwk.le h hwN
      exact hs ⟨by omega, by omega⟩
    · exact Or.inr ⟨k, hk, hwk⟩

/-- At the end, the finished nodes are the `x`-nodes of `r`. -/
theorem SplitInv.no_iff (H : T.SplitHyp G r x) {no sp : List ℕ} (I : T.SplitInv G r x [] no sp)
    (k : ℕ) : k ∈ no ↔ ∃ v ∈ r.X, k = T.top x v := by
  have h := H.ok
  have hN := h.n_lt
  constructor
  · intro hk
    obtain ⟨v, hv, ht⟩ := I.no_ok k hk
    exact ⟨v, hv, ht.eq_top h (H.vx v hv) H.x1⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, hk, hvk⟩ := I.cover v hv
    rw [List.nil_append] at hk
    obtain ⟨v', hv', ht⟩ := I.no_ok k hk
    have hv'n := H.vx v' hv'
    have := (ht.of_common h (by omega) ht.1 hvk ht.2.1).eq_top h (H.vx v hv) H.x1
    rwa [← this]

/-- At the end, each `x`-node of `r` is finished once. -/
theorem SplitInv.no_nodup (H : T.SplitHyp G r x) {no sp : List ℕ}
    (I : T.SplitInv G r x [] no sp) : no.Nodup := by
  have hp := I.apart
  rw [List.nil_append] at hp
  refine hp.imp_of_mem fun {a b} ha _ hab => ?_
  obtain ⟨v, hv, ht⟩ := I.no_ok a ha
  have hvn := H.vx v hv
  have hN := H.ok.n_lt
  exact hab.ne H.ok (ht.1.lt_N H.ok (by omega))

/-- At the end, the split nodes are the nodes of `KT.splitSet`. -/
theorem SplitInv.sp_toFinset {no sp : List ℕ} (I : T.SplitInv G r x [] no sp) :
    sp.toFinset = T.splitSet G r x := by
  ext u
  rw [List.mem_toFinset]
  constructor
  · exact I.sp_mem u
  · intro hu
    rcases I.compl u hu with h1 | ⟨k, hk, -⟩
    · exact h1
    · simp at hk

/-- **The labels at the start**: each vertex has the head of its `θ`-node. -/
theorem LabInv.init (H : T.SplitHyp G r x) {L : List ℕ} (hL : ∀ k ∈ L, ∃ v ∈ r.X, k = T.top r.θ v)
    {lab : ℕ → ℕ} (hlab : ∀ v ∈ r.X, lab v = T.hd G (T.top r.θ v)) :
    T.LabInv G r lab (L ++ []) := by
  intro v hv k hk hvk
  rw [List.append_nil] at hk
  obtain ⟨w, hw, rfl⟩ := hL k hk
  rw [hlab v hv, (H.top_eq hw (H.vx v hv) hvk).2]

/-- **The labels after a split step.** -/
theorem LabInv.split (H : T.SplitHyp G r x) {u : ℕ} {st no sp : List ℕ} {lab : ℕ → ℕ}
    (I : T.SplitInv G r x (u :: st) no sp) (hs : T.SplitsAt G x u)
    (hl : T.LabInv G r lab ((u :: st) ++ no)) :
    T.LabInv G r (T.relab G u lab) ((T.ch1 u :: T.ch2 u :: st) ++ no) := by
  have h := H.ok
  obtain ⟨huN, -, -⟩ := I.st_ok u (by simp)
  have hap := I.apart
  simp only [List.cons_append, List.pairwise_cons] at hap
  have hlu : T.Under (T.light G u) u := by
    rcases heavy_light h hs.1 huN with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    · exact under_ch2 h hs.1 huN
    · exact under_ch1 h hs.1 huN
  intro v hv k hk hvk
  have hvn := H.vx v hv
  simp only [List.cons_append, List.mem_cons] at hk
  -- the heavy child keeps the label of `u`
  have heavy_case : ∀ c, (T.heavy G u = c ∧ T.light G u ≠ c) → T.Under v c →
      T.relab G u lab v = T.hd G c := by
    rintro c ⟨e1, e2⟩ hvc
    have hcu : T.Under c u := by
      rcases heavy_light h hs.1 huN with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [← e1, a]
      · exact under_ch1 h hs.1 huN
      · exact under_ch2 h hs.1 huN
    have hnl : ¬ T.Under v (T.light G u) := by
      intro hvl
      rcases heavy_light h hs.1 huN with ⟨a, b⟩ | ⟨a, b⟩
      · rw [← e1, a] at hvc; rw [b] at hvl; exact not_under_both h hs.1 huN hvc hvl
      · rw [← e1, a] at hvc; rw [b] at hvl; exact not_under_both h hs.1 huN hvl hvc
    rw [relab_of_not hnl, hl v hv u (by simp) (hvc.trans hcu), ← e1, heavy_ch1 h hs.1 huN]
  have child_case : ∀ c, (c = T.ch1 u ∨ c = T.ch2 u) → T.Under v c →
      T.relab G u lab v = T.hd G c := by
    intro c hc hvc
    by_cases e : T.light G u = c
    · rw [relab_of (e ▸ hvc), e]
    · refine heavy_case c ⟨?_, e⟩ hvc
      rcases heavy_light h hs.1 huN with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hc with rfl | rfl
      · exact a
      · exact absurd b e
      · exact absurd b e
      · exact a
  rcases hk with rfl | rfl | hk
  · exact child_case _ (Or.inl rfl) hvk
  · exact child_case _ (Or.inr rfl) hvk
  · have hnl : ¬ T.Under v (T.light G u) := fun hvl =>
      hap.1 k (by simpa using hk) v hvn ⟨hvl.trans hlu, hvk⟩
    rw [relab_of_not hnl]
    exact hl v hv k (by simp at hk ⊢; tauto) hvk

/-- **The labels after a finishing step** stay right. -/
theorem LabInv.keep {u : ℕ} {st no : List ℕ} {lab : ℕ → ℕ}
    (hl : T.LabInv G r lab ((u :: st) ++ no)) : T.LabInv G r lab (st ++ u :: no) :=
  fun v hv k hk hvk => hl v hv k (by simp at hk ⊢; tauto) hvk

/-- **The labels at the end**: each vertex has the head of its `x`-node. -/
theorem LabInv.done (H : T.SplitHyp G r x) {no sp : List ℕ} {lab : ℕ → ℕ}
    (I : T.SplitInv G r x [] no sp) (hl : T.LabInv G r lab ([] ++ no)) :
    ∀ v ∈ r.X, lab v = T.hd G (T.top x v) :=
  fun v hv => hl v hv _ (by rw [List.nil_append]; exact (I.no_iff H _).mpr ⟨v, hv, rfl⟩)
    (isTop_top H.ok (H.vx v hv) H.x1).1

/-- The size of the stack: it drops by at least one at each step. -/
noncomputable def stM (T : KT) (G : PG) (st : List ℕ) : ℕ := (st.map fun k => 2 * T.sz G k - 1).sum

theorem stM_split (H : T.SplitHyp G r x) {u : ℕ} {st no sp : List ℕ}
    (I : T.SplitInv G r x (u :: st) no sp) (hs : T.SplitsAt G x u) :
    T.stM G (T.ch1 u :: T.ch2 u :: st) < T.stM G (u :: st) := by
  have h := H.ok
  obtain ⟨huN, -, -⟩ := I.st_ok u (by simp)
  obtain ⟨-, -, -, hlt1, hlt2⟩ := h.ch u hs.1 huN
  have e := sz_inner h hs.1 huN
  have := sz_pos h (show T.ch1 u < T.N by omega)
  have := sz_pos h (show T.ch2 u < T.N by omega)
  simp only [stM, List.map_cons, List.sum_cons]
  omega

theorem stM_keep (H : T.SplitHyp G r x) {u : ℕ} {st no sp : List ℕ}
    (I : T.SplitInv G r x (u :: st) no sp) : T.stM G st < T.stM G (u :: st) := by
  obtain ⟨huN, -, -⟩ := I.st_ok u (by simp)
  have := sz_pos H.ok huN
  simp only [stM, List.map_cons, List.sum_cons]
  omega

end KT

end MinCostFlow.LowStretch
