module

public import MinCostFlow.LowStretch.ProgSplitMath
public import MinCostFlow.LowStretch.ProgSplitLab

/-!
# The split walk in memory

The program `splitP` (`ProgSplit`) runs the split walk of `ProgSplitMath` in memory. This file
fixes its arguments (`SplitL`), its precondition (`SplitPre`) and the memory part of the loop
invariant (`SplitMem`), and shows that one step of the walk keeps the invariant
(`SplitMem.keep`, `SplitMem.split`).

The three lists of the walk share one array from `A` with stride `3`: entry `i` of the stack is at
`A + 3 i`, entry `i` of the finished nodes at `A + 3 i + 1`, and entry `i` of the split nodes at
`A + 3 i + 2`. The array needs no bound fixed in advance: the stack and the finished nodes have at
most `len0 + |sp|` entries together, where `len0` is the number of `θ`-nodes and `sp` the split
nodes so far.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open KT

/-- The arguments of `splitP`: the children, weights, leaf counts and interval starts of the merge
tree, the leaf order, the labels, the number `n` of vertices, the work array `A`, the `θ`-nodes
(`len0` of them at `NA`), and the new threshold `x`. -/
structure SplitL where
  CH1 : ℕ
  CH2 : ℕ
  MW : ℕ
  SZ : ℕ
  LO : ℕ
  ORDL : ℕ
  LAB : ℕ
  n : ℕ
  A : ℕ
  NA : ℕ
  len0 : ℕ
  x : ℕ

namespace SplitL

variable (E : SplitL)

/-- The argument list. -/
def args : List ℕ := [E.CH1, E.CH2, E.MW, E.SZ, E.LO, E.ORDL, E.LAB, E.n, E.A, E.NA, E.len0, E.x]

/-- The `θ`-nodes given to `splitP`. -/
def nodes (mem : ℕ → ℕ) : List ℕ := (List.range E.len0).map fun i => mem (E.NA + i)

/-- An array of the merge tree lies below `A` and away from the labels. -/
def Lay (T : KT) (G : PG) (Z : ℕ) : Prop :=
  Z + T.N ≤ E.A ∧ (Z + T.N ≤ E.LAB ∨ E.LAB + G.n ≤ Z)

end SplitL

/-- Column `r` of the work array: entries `0, …, k - 1`. -/
def rdS (M : ℕ → ℕ) (A r k : ℕ) : List ℕ := (List.range k).map fun i => M (A + 3 * i + r)

theorem rdS_length (M : ℕ → ℕ) (A r k : ℕ) : (rdS M A r k).length = k := by simp [rdS]

theorem rdS_succ (M : ℕ → ℕ) (A r k : ℕ) : rdS M A r (k + 1) = rdS M A r k ++ [M (A + 3 * k + r)] := by
  simp [rdS, List.range_succ]

theorem rdS_congr {M M' : ℕ → ℕ} {A r k : ℕ} (h : ∀ i < k, M (A + 3 * i + r) = M' (A + 3 * i + r)) :
    rdS M A r k = rdS M' A r k :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- **The precondition of `splitP`** for the child `r` and the new threshold `x`. -/
structure SplitPre (w : ℕ) (T : KT) (G : PG) (r : Cl) (x : ℕ) (E : SplitL) (mem : ℕ → ℕ) : Prop where
  H : T.SplitHyp G r x
  ex : E.x = x
  n : E.n = G.n
  ch : ∀ k, G.n ≤ k → k < T.N → mem (E.CH1 + k) = T.ch1 k ∧ mem (E.CH2 + k) = T.ch2 k
  mw : ∀ k < T.N, mem (E.MW + k) = T.mw k
  sz : ∀ k < T.N, mem (E.SZ + k) = T.sz G k
  lo : ∀ k < T.N, mem (E.LO + k) = T.lo G k
  ordl : ∀ v < G.n, mem (E.ORDL + T.lo G v) = v
  nd : (E.nodes mem).Nodup
  nd_top : ∀ k ∈ E.nodes mem, ∃ v ∈ r.X, k = T.top r.θ v
  top_nd : ∀ v ∈ r.X, T.top r.θ v ∈ E.nodes mem
  lab : ∀ v ∈ r.X, mem (E.LAB + v) = T.hd G (T.top r.θ v)
  lay1 : E.Lay T G E.CH1
  lay2 : E.Lay T G E.CH2
  lay3 : E.Lay T G E.MW
  lay4 : E.Lay T G E.SZ
  lay5 : E.Lay T G E.LO
  lay_o : E.ORDL + G.n ≤ E.A ∧ (E.ORDL + G.n ≤ E.LAB ∨ E.LAB + G.n ≤ E.ORDL)
  lay_na : E.NA + E.len0 ≤ E.A
  lay_lab : E.LAB + G.n ≤ E.A
  room : E.A + 3 * (E.len0 + T.N + 1) < 2 ^ w
  xw : x < 2 ^ w

/-- **The memory part of the loop invariant**, for the walk state `(st, no, sp)` and the memory
`M`, started from the memory `mem0`. -/
structure SplitMem (T : KT) (G : PG) (r : Cl) (x : ℕ) (E : SplitL) (mem0 : ℕ → ℕ)
    (st no sp : List ℕ) (M : ℕ → ℕ) : Prop where
  rst : st = (rdS M E.A 0 st.length).reverse
  rno : no = (rdS M E.A 1 no.length).reverse
  rsp : sp = (rdS M E.A 2 sp.length).reverse
  inv : T.SplitInv G r x st no sp
  lab : T.LabInv G r (fun v => M (E.LAB + v)) (st ++ no)
  count : st.length + no.length = E.len0 + sp.length
  low : ∀ a < E.A, (∀ v ∈ r.X, a ≠ E.LAB + v) → M a = mem0 a
  high : ∀ a, E.A + 3 * (E.len0 + sp.length) ≤ a → M a = mem0 a

variable {T : KT} {G : PG} {r : Cl} {x : ℕ} {E : SplitL} {mem0 : ℕ → ℕ} {w : ℕ}

/-- The cells below `A` away from the labels keep their first value. -/
theorem SplitMem.low' {st no sp : List ℕ} {M : ℕ → ℕ} (S : SplitMem T G r x E mem0 st no sp M)
    (H : T.SplitHyp G r x) {a : ℕ} (ha : a < E.A) (hl : a < E.LAB ∨ E.LAB + G.n ≤ a) :
    M a = mem0 a :=
  S.low a ha fun v hv => by have := H.vx v hv; omega

/-- The split nodes are distinct nodes of `KT.splitSet`, so there are at most `T.N` of them. -/
theorem KT.SplitInv.sp_le {st no sp : List ℕ} (I : T.SplitInv G r x st no sp) : sp.length ≤ T.N := by
  classical
  rw [← List.toFinset_card_of_nodup I.sp_nodup]
  calc sp.toFinset.card ≤ (T.splitSet G r x).card :=
        Finset.card_le_card fun u hu => I.sp_mem u (List.mem_toFinset.mp hu)
    _ ≤ (Finset.range T.N).card := Finset.card_filter_le _ _
    _ = T.N := Finset.card_range _

/-- The labels matter only on `X`. -/
theorem KT.LabInv.congr {lab lab' : ℕ → ℕ} {fr : List ℕ} (h : T.LabInv G r lab fr)
    (he : ∀ v ∈ r.X, lab' v = lab v) : T.LabInv G r lab' fr :=
  fun v hv k hk hvk => (he v hv).trans (h v hv k hk hvk)

/-- **A finishing step in memory**: the node `u` is written to the finished column. -/
theorem SplitMem.keep (H : T.SplitHyp G r x) {u : ℕ} {st no sp : List ℕ} {M : ℕ → ℕ}
    (S : SplitMem T G r x E mem0 (u :: st) no sp M) (hs : ¬ T.SplitsAt G x u)
    (hlab : E.LAB + G.n ≤ E.A) :
    SplitMem T G r x E mem0 st (u :: no) sp
      (Function.update M (E.A + 3 * no.length + 1) u) := by
  have hc := S.count
  simp only [List.length_cons] at hc
  have hst : rdS (Function.update M (E.A + 3 * no.length + 1) u) E.A 0 st.length =
      rdS M E.A 0 st.length :=
    rdS_congr fun i _ => Function.update_of_ne (by omega) _ _
  have hst' : u :: st = (rdS M E.A 0 st.length ++ [M (E.A + 3 * st.length + 0)]).reverse := by
    have := S.rst; rwa [List.length_cons, rdS_succ] at this
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.cons.injEq] at hst'
  refine ⟨?_, ?_, ?_, S.inv.keep H hs, ?_, by simp; omega, fun a ha hl => ?_, fun a ha => ?_⟩
  · rw [hst]; exact hst'.2
  · rw [List.length_cons, rdS_succ, Function.update_self, rdS_congr (M' := M)
      fun i hi => Function.update_of_ne (by omega) _ _, List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append]
    rw [← S.rno]
  · rw [rdS_congr (M' := M) fun i _ => Function.update_of_ne (by omega) _ _]
    exact S.rsp
  · refine (LabInv.keep S.lab).congr fun v hv => ?_
    have := H.vx v hv
    exact Function.update_of_ne (by omega) _ _
  · rw [Function.update_of_ne (by omega)]; exact S.low a ha hl
  · rw [Function.update_of_ne (by omega)]; exact S.high a ha

/-- The memory of a split step before the relabeling: the node `u` is written to the split column,
and its children replace it on the stack, the first child on top. -/
def splitMem (E : SplitL) (M : ℕ → ℕ) (st sp : List ℕ) (u c1 c2 : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update M (E.A + 3 * sp.length + 2) u)
    (E.A + 3 * st.length) c2) (E.A + 3 * st.length + 3) c1

theorem splitMem_low {M : ℕ → ℕ} {st sp : List ℕ} {u c1 c2 a : ℕ} (ha : a < E.A) :
    splitMem E M st sp u c1 c2 a = M a := by
  simp only [splitMem]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega)]

/-- The leaves in the interval of a node `k` are the leaves below `k`. -/
theorem SplitPre.ordl_mem (P : SplitPre w T G r x E mem0) {M : ℕ → ℕ}
    (hM : ∀ a < E.A, (a < E.LAB ∨ E.LAB + G.n ≤ a) → M a = mem0 a) {k j : ℕ} (hk : k < T.N)
    (hj1 : T.lo G k ≤ j) (hj2 : j < T.lo G k + T.sz G k) : M (E.ORDL + j) ∈ T.lv G k := by
  have h := P.H.ok
  have hN := h.n_lt
  have hroot := (show T.Under k (T.N - 1) from ⟨T.N, reach_root h hk⟩).lo h hk
  rw [lo_root, sz_root h] at hroot
  have lo := P.lay_o
  rw [hM _ (by omega) (by omega)]
  refine lo_fill (A := fun j => mem0 (E.ORDL + j)) h (fun v hv => P.ordl v hv) hk hj1 hj2

/-- The interval of a node lies inside the leaf order. -/
theorem SplitPre.lo_sz (P : SplitPre w T G r x E mem0) {k : ℕ} (hk : k < T.N) :
    T.lo G k + T.sz G k ≤ G.n := by
  have h := P.H.ok
  have hN := h.n_lt
  have hroot := (show T.Under k (T.N - 1) from ⟨T.N, reach_root h hk⟩).lo h hk
  rw [lo_root, sz_root h] at hroot
  omega

/-- **A split step in memory.** After the stores of `splitMem`, the relabeling writes the light
child `l` of `u` to the labels of the leaves in the interval of `l`, and leaves the other cells. -/
theorem SplitMem.split (P : SplitPre w T G r x E mem0) {u : ℕ} {st no sp : List ℕ}
    {M M3 : ℕ → ℕ} (S : SplitMem T G r x E mem0 (u :: st) no sp M) (hs : T.SplitsAt G x u)
    (hf1 : ∀ j, T.lo G (T.light G u) ≤ j → j < T.lo G (T.light G u) + T.sz G (T.light G u) →
      M3 (E.LAB + splitMem E M st sp u (T.ch1 u) (T.ch2 u) (E.ORDL + j)) = T.light G u)
    (hf2 : ∀ a, ¬ FillHit (splitMem E M st sp u (T.ch1 u) (T.ch2 u)) E.ORDL E.LAB
      (T.lo G (T.light G u)) (T.lo G (T.light G u) + T.sz G (T.light G u)) a → M3 a =
      splitMem E M st sp u (T.ch1 u) (T.ch2 u) a) :
    SplitMem T G r x E mem0 (T.ch1 u :: T.ch2 u :: st) no (u :: sp) M3 := by
  have H := P.H
  have h := H.ok
  have hN := h.n_lt
  set M2 := splitMem E M st sp u (T.ch1 u) (T.ch2 u) with hM2
  set L := T.light G u with hL
  obtain ⟨huN, ⟨v0, hv0, hv0u, hut⟩, -⟩ := S.inv.st_ok u (by simp)
  have hlu : T.Under L u := by
    rcases heavy_light h hs.1 huN with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [hL, e]
    · exact under_ch2 h hs.1 huN
    · exact under_ch1 h hs.1 huN
  have hLN : L < T.N := by
    obtain ⟨-, -, -, h1, h2⟩ := h.ch u hs.1 huN
    rcases heavy_light h hs.1 huN with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [hL, e] <;> omega
  have hlab := P.lay_lab
  have hlo := P.lay_o
  have hc := S.count
  simp only [List.length_cons] at hc
  have hLsz := P.lo_sz hLN
  -- reads below `A` see the first memory
  have hM2low : ∀ a < E.A, (a < E.LAB ∨ E.LAB + G.n ≤ a) → M2 a = mem0 a := fun a ha hl => by
    rw [hM2, splitMem_low ha]; exact S.low' H ha hl
  -- the cells written by the relabeling are the labels of leaves of `L`, all in `X`
  have hhit : ∀ a, FillHit M2 E.ORDL E.LAB (T.lo G L) (T.lo G L + T.sz G L) a →
      ∃ v ∈ T.lv G L, a = E.LAB + v := by
    rintro a ⟨j, hj1, hj2, rfl⟩
    exact ⟨_, P.ordl_mem hM2low hLN hj1 hj2, rfl⟩
  have hlvX : ∀ v ∈ T.lv G L, v ∈ r.X := fun v hv =>
    (H.top_eq hv0 (mem_lv.mp hv).1 (((mem_lv.mp hv).2.trans hlu).trans hut)).1
  have hM3 : ∀ a, E.A ≤ a → M3 a = M2 a := fun a ha => hf2 a fun hh => by
    obtain ⟨v, hv, rfl⟩ := hhit a hh
    have := (mem_lv.mp hv).1
    omega
  have hst' : u :: st = (rdS M E.A 0 st.length ++ [M (E.A + 3 * st.length + 0)]).reverse := by
    have := S.rst; rwa [List.length_cons, rdS_succ] at this
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.cons.injEq] at hst'
  have hsp := S.inv.sp_le
  refine ⟨?_, ?_, ?_, S.inv.split H hs, ?_, by simp; omega, fun a ha hl => ?_, fun a ha => ?_⟩
  · simp only [List.length_cons]
    rw [rdS_congr (M' := M2) fun i _ => hM3 _ (by omega), rdS_succ, rdS_succ,
      rdS_congr (M' := M) fun i hi => by
        simp only [hM2, splitMem]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega)]]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    rw [← hst'.2]
    simp only [hM2, splitMem, Nat.add_zero]
    rw [show E.A + 3 * (st.length + 1) = E.A + 3 * st.length + 3 by ring, Function.update_self,
      Function.update_of_ne (show E.A + 3 * st.length ≠ E.A + 3 * st.length + 3 by omega),
      Function.update_self]
  · rw [rdS_congr (M' := M) fun i hi => by
      rw [hM3 _ (by omega)]
      simp only [hM2, splitMem]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]]
    exact S.rno
  · simp only [List.length_cons]
    rw [rdS_succ, rdS_congr (M' := M) fun i hi => by
      rw [hM3 _ (by omega)]
      simp only [hM2, splitMem]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]]
    rw [hM3 _ (by omega)]
    simp only [hM2, splitMem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self,
      List.reverse_append, List.reverse_singleton, List.singleton_append, ← S.rsp]
  · refine (LabInv.split H S.inv hs S.lab).congr fun v hv => ?_
    have hvn := H.vx v hv
    by_cases hvl : T.Under v L
    · rw [relab_of hvl, hd_lightc h hs.1 huN]
      have hvlo := hvl.lo h (by omega)
      rw [sz_leaf h hvn] at hvlo
      have e : M2 (E.ORDL + T.lo G v) = v := by
        rw [hM2low _ (by have := lo_lt h hvn; omega) (by have := lo_lt h hvn; omega)]
        exact P.ordl v hvn
      have := hf1 (T.lo G v) hvlo.1 (by omega)
      rwa [e] at this
    · rw [relab_of_not hvl]
      have hnh : ¬ FillHit M2 E.ORDL E.LAB (T.lo G L) (T.lo G L + T.sz G L) (E.LAB + v) := by
        intro hh
        obtain ⟨v', hv', e⟩ := hhit _ hh
        have : v = v' := by omega
        exact hvl (this ▸ (mem_lv.mp hv').2)
      rw [hf2 _ hnh, hM2, splitMem_low (by omega)]
  · have hnh : ¬ FillHit M2 E.ORDL E.LAB (T.lo G L) (T.lo G L + T.sz G L) a := by
      intro hh
      obtain ⟨v', hv', e⟩ := hhit _ hh
      exact hl v' (hlvX v' hv') e
    rw [hf2 _ hnh, hM2, splitMem_low ha]
    exact S.low a ha hl
  · simp only [List.length_cons] at ha
    rw [hM3 _ (by omega)]
    simp only [hM2, splitMem]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact S.high a (by omega)

end MinCostFlow.LowStretch
