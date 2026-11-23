module

public import MinCostFlow.LowStretch.UFMath
public import MinCostFlow.LowStretch.KPure

/-!
# The Kruskal state in memory

The program of `ProgKruskal` keeps the state `s : KS` of `kstep` in memory: a union-find
structure whose labels are the tops `s.top` (`UFRep`), and the arrays of the tree nodes `KPAR`,
`KMW` (all nodes) and `KCH1`, `KCH2`, `KMP` (inner nodes). `KRep` says this. `KRep.step` shows that
the writes of one merge give the representation of `kstep G s q`.

`KT.Ok.congr` shows that a merge tree is still one when only the values that the rules read are
kept. This lets a later step read the tree from memory.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Finset

section frame

variable {M M' : ℕ → ℕ} {UF SZ TN n : ℕ} {dep top : ℕ → ℕ}

theorem UFCons.iter_congr (hc : UFCons M UF n dep) (hM : ∀ y < n, M' (UF + y) = M (UF + y))
    {x : ℕ} (hx : x < n) (i : ℕ) :
    (fun y => M' (UF + y))^[i] x = (fun y => M (UF + y))^[i] x := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact hM _ (hc.iter_lt hx i)

theorem UFCons.congr (hc : UFCons M UF n dep) (hM : ∀ y < n, M' (UF + y) = M (UF + y)) :
    UFCons M' UF n dep := by
  intro x hx; rw [hM x hx]; exact hc x hx

theorem UFCons.rt_congr (hc : UFCons M UF n dep) (hM : ∀ y < n, M' (UF + y) = M (UF + y))
    {x : ℕ} (hx : x < n) : rt M' UF dep x = rt M UF dep x :=
  hc.iter_congr hM hx _

theorem ufRoots_congr (hM : ∀ y < n, M' (UF + y) = M (UF + y)) :
    ufRoots M' UF n = ufRoots M UF n := by
  unfold ufRoots
  exact filter_congr (fun r hr => by rw [hM r (mem_range.mp hr)])

/-- Writes outside the three arrays keep the representation. -/
theorem UFRep.frame (h : UFRep M UF SZ TN n dep top) (hU : ∀ y < n, M' (UF + y) = M (UF + y))
    (hS : ∀ y < n, M' (SZ + y) = M (SZ + y)) (hT : ∀ y < n, M' (TN + y) = M (TN + y)) :
    UFRep M' UF SZ TN n dep top := by
  have hc := h.cons
  refine ⟨hc.congr hU, fun x hx => ?_, fun x hx => ?_, fun x hx y hy => ?_, fun r hr hroot => ?_⟩
  · rw [hc.rt_congr hU hx, hT _ (hc.rt_lt hx)]; exact h.lab x hx
  · rw [hc.rt_congr hU hx, hS _ (hc.rt_lt hx)]; exact h.size x hx
  · rw [hc.rt_congr hU hx, hc.rt_congr hU hy]; exact h.same x hx y hy
  · rw [hU r hr] at hroot
    rw [hS r hr, h.card r hr hroot]
    unfold ufSet
    congr 1
    exact filter_congr (fun x hx => by rw [hc.rt_congr hU (mem_range.mp hx)])

/-- Only the labels of the elements matter. -/
theorem UFRep.congr_top {top' : ℕ → ℕ} (h : UFRep M UF SZ TN n dep top)
    (ht : ∀ x < n, top' x = top x) : UFRep M UF SZ TN n dep top' :=
  ⟨h.cons, fun x hx => by rw [ht x hx]; exact h.lab x hx, h.size,
    fun x hx y hy => by rw [ht x hx, ht y hy]; exact h.same x hx y hy, h.card⟩

theorem UFRep.mem_roots (h : UFRep M UF SZ TN n dep top) {x : ℕ} (hx : x < n) :
    rt M UF dep x ∈ ufRoots M UF n := by
  simp only [ufRoots, mem_filter, mem_range]
  exact ⟨h.cons.rt_lt hx, h.cons.rt_is_root hx⟩

end frame

namespace KT

/-- The rules of a merge tree read the parents everywhere, the merge weights below `N` and the
children and merge pairs of the inner nodes only. -/
theorem Ok.congr {T T' : KT} {G : PG} (h : T.Ok G) (hN : T'.N = T.N) (hpar : T'.par = T.par)
    (hmw : ∀ k < T.N, T'.mw k = T.mw k)
    (hch : ∀ k, G.n ≤ k → k < T.N → T'.ch1 k = T.ch1 k ∧ T'.ch2 k = T.ch2 k ∧ T'.mp k = T.mp k) :
    T'.Ok G := by
  have hU : ∀ j k, T'.Under j k ↔ T.Under j k := fun j k => by
    unfold KT.Under; rw [hpar]
  have hS : ∀ p k, G.n ≤ k → k < T.N → (T'.Splits G p k ↔ T.Splits G p k) := fun p k h1 h2 => by
    unfold KT.Splits
    rw [hU, hU, hU, hU, (hch k h1 h2).1, (hch k h1 h2).2.1]
  have hn := h.n_lt
  refine ⟨hN ▸ h.n_lt, fun k hk => ?_, ?_, fun v hv => ?_, fun k hk => ?_, fun k hk => ?_,
    fun k hk => ?_, fun k h1 h2 => ?_, fun k h1 h2 => ?_, fun p hp k h1 h2 hs => ?_, fun v hv => ?_⟩
  · rw [hpar, hN]; exact h.par_lt k (by omega)
  · rw [hpar, hN]; exact h.root
  · rw [hmw v (by omega)]; exact h.leaf_mw v hv
  · rw [hN] at hk
    rw [hpar, hmw k hk, hmw _ (par_lt_N h hk)]; exact h.mw_mono k hk
  · rw [hpar]; exact h.par_internal k (by omega)
  · rw [hN] at hk
    rw [hpar]
    have := h.par_lt k hk
    have := h.par_internal k hk
    rw [(hch _ (by omega) (by omega)).1, (hch _ (by omega) (by omega)).2.1]
    exact h.par_ch k hk
  · rw [hN] at h2
    rw [hpar, (hch k h1 h2).1, (hch k h1 h2).2.1]; exact h.ch k h1 h2
  · rw [hN] at h2
    rw [(hch k h1 h2).2.2, hmw k h2, hS _ k h1 h2]; exact h.merge k h1 h2
  · rw [hN] at h2
    rw [hS p k h1 h2] at hs
    rw [hmw k h2]; exact h.lca p hp k h1 h2 hs
  · rw [hU, hN]; exact h.all v hv

end KT

/-- Where the Kruskal procedure keeps its data. The node arrays have room for `2n` nodes. -/
structure KL where
  n : ℕ
  UF : ℕ
  SZ : ℕ
  TN : ℕ
  KPAR : ℕ
  KCH1 : ℕ
  KCH2 : ℕ
  KMW : ℕ
  KMP : ℕ

/-- The arrays do not overlap. -/
structure KL.Lay (E : KL) : Prop where
  l1 : E.UF + E.n ≤ E.SZ
  l2 : E.SZ + E.n ≤ E.TN
  l3 : E.TN + E.n ≤ E.KPAR
  l4 : E.KPAR + 2 * E.n ≤ E.KCH1
  l5 : E.KCH1 + 2 * E.n ≤ E.KCH2
  l6 : E.KCH2 + 2 * E.n ≤ E.KMW
  l7 : E.KMW + 2 * E.n ≤ E.KMP

/-- The memory `M` holds the state `s`. -/
structure KRep (M : ℕ → ℕ) (E : KL) (s : KS) (dep : ℕ → ℕ) : Prop where
  uf : UFRep M E.UF E.SZ E.TN E.n dep s.top
  cnt : (ufRoots M E.UF E.n).card + (s.T.N - E.n) = E.n
  par : ∀ k < s.T.N, M (E.KPAR + k) = s.T.par k
  mw : ∀ k < s.T.N, M (E.KMW + k) = s.T.mw k
  ch : ∀ k, E.n ≤ k → k < s.T.N →
    M (E.KCH1 + k) = s.T.ch1 k ∧ M (E.KCH2 + k) = s.T.ch2 k ∧ M (E.KMP + k) = s.T.mp k

/-- The memory after the writes of the new node `N`, with children `ta` and `tb`. -/
def kW (E : KL) (M : ℕ → ℕ) (N ta tb wq q : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update M (E.KCH1 + N) ta) (E.KCH2 + N) tb) (E.KPAR + ta) N)
    (E.KPAR + tb) N) (E.KPAR + N) N) (E.KMW + N) wq) (E.KMP + N) q

/-- The memory after hanging the root `ra` below the root `rb`, writing the size `sz` of the new
set and labelling it with `N`. -/
def kU (E : KL) (M : ℕ → ℕ) (ra rb N sz : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update M (E.UF + ra) rb) (E.SZ + rb) sz) (E.TN + rb) N

variable {M : ℕ → ℕ} {E : KL} {s : KS} {dep : ℕ → ℕ} {G : PG} {l r : List ℕ}

section kW

variable {N ta tb wq q k : ℕ} (hl : E.Lay) (hN : N < 2 * E.n) (hk : k < 2 * E.n)
  (ha : ta < 2 * E.n) (hb : tb < 2 * E.n)
include hl hN hk ha hb

theorem kW_par :
    kW E M N ta tb wq q (E.KPAR + k) =
      if k = N then N else if k = tb then N else if k = ta then N else M (E.KPAR + k) := by
  have l4 := hl.l4; have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7
  have e1 : E.KPAR + k ≠ E.KMP + N := by omega
  have e2 : E.KPAR + k ≠ E.KMW + N := by omega
  have e3 : E.KPAR + k ≠ E.KCH2 + N := by omega
  have e4 : E.KPAR + k ≠ E.KCH1 + N := by omega
  simp only [kW, Function.update_apply, e1, e2, e3, e4, if_false, add_right_inj]

theorem kW_mw : kW E M N ta tb wq q (E.KMW + k) = if k = N then wq else M (E.KMW + k) := by
  have l4 := hl.l4; have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7
  have e1 : E.KMW + k ≠ E.KMP + N := by omega
  have e3 : E.KMW + k ≠ E.KCH2 + N := by omega
  have e4 : E.KMW + k ≠ E.KCH1 + N := by omega
  have e5 : E.KMW + k ≠ E.KPAR + N := by omega
  have e6 : E.KMW + k ≠ E.KPAR + ta := by omega
  have e7 : E.KMW + k ≠ E.KPAR + tb := by omega
  simp only [kW, Function.update_apply, e1, e3, e4, e5, e6, e7, if_false, add_right_inj]

theorem kW_ch1 : kW E M N ta tb wq q (E.KCH1 + k) = if k = N then ta else M (E.KCH1 + k) := by
  have l4 := hl.l4; have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7
  have e1 : E.KCH1 + k ≠ E.KMP + N := by omega
  have e2 : E.KCH1 + k ≠ E.KMW + N := by omega
  have e3 : E.KCH1 + k ≠ E.KCH2 + N := by omega
  have e5 : E.KCH1 + k ≠ E.KPAR + N := by omega
  have e6 : E.KCH1 + k ≠ E.KPAR + ta := by omega
  have e7 : E.KCH1 + k ≠ E.KPAR + tb := by omega
  simp only [kW, Function.update_apply, e1, e2, e3, e5, e6, e7, if_false, add_right_inj]

theorem kW_ch2 : kW E M N ta tb wq q (E.KCH2 + k) = if k = N then tb else M (E.KCH2 + k) := by
  have l4 := hl.l4; have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7
  have e1 : E.KCH2 + k ≠ E.KMP + N := by omega
  have e2 : E.KCH2 + k ≠ E.KMW + N := by omega
  have e4 : E.KCH2 + k ≠ E.KCH1 + N := by omega
  have e5 : E.KCH2 + k ≠ E.KPAR + N := by omega
  have e6 : E.KCH2 + k ≠ E.KPAR + ta := by omega
  have e7 : E.KCH2 + k ≠ E.KPAR + tb := by omega
  simp only [kW, Function.update_apply, e1, e2, e4, e5, e6, e7, if_false, add_right_inj]

theorem kW_mp : kW E M N ta tb wq q (E.KMP + k) = if k = N then q else M (E.KMP + k) := by
  have l4 := hl.l4; have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7
  have e2 : E.KMP + k ≠ E.KMW + N := by omega
  have e3 : E.KMP + k ≠ E.KCH2 + N := by omega
  have e4 : E.KMP + k ≠ E.KCH1 + N := by omega
  have e5 : E.KMP + k ≠ E.KPAR + N := by omega
  have e6 : E.KMP + k ≠ E.KPAR + ta := by omega
  have e7 : E.KMP + k ≠ E.KPAR + tb := by omega
  simp only [kW, Function.update_apply, e2, e3, e4, e5, e6, e7, if_false, add_right_inj]

end kW

theorem kW_out {N ta tb wq q a : ℕ} (hl : E.Lay) (hN : N < 2 * E.n) (ha : ta < 2 * E.n)
    (hb : tb < 2 * E.n) (hx : a < E.KPAR ∨ E.KMP + 2 * E.n ≤ a) : kW E M N ta tb wq q a = M a := by
  have l4 := hl.l4; have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7
  simp only [kW, Function.update_apply]
  split_ifs <;> first | rfl | omega

theorem kU_out {ra rb N sz a : ℕ} (hl : E.Lay) (hra : ra < E.n) (hrb : rb < E.n)
    (hx : a < E.UF ∨ E.TN + E.n ≤ a) : kU E M ra rb N sz a = M a := by
  have l1 := hl.l1; have l2 := hl.l2
  simp only [kU, Function.update_apply]
  split_ifs <;> first | rfl | omega

theorem KRep.congr {M' : ℕ → ℕ} (h : KRep M E s dep) (hl : E.Lay)
    (hM : ∀ a, E.UF ≤ a → a < E.KMP + 2 * E.n → M' a = M a) : KRep M' E s dep := by
  have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4; have l5 := hl.l5
  have l6 := hl.l6; have l7 := hl.l7
  have hN := h.cnt
  have hU : ∀ y < E.n, M' (E.UF + y) = M (E.UF + y) := fun y hy => hM _ (by omega) (by omega)
  refine ⟨h.uf.frame hU (fun y hy => hM _ (by omega) (by omega))
    (fun y hy => hM _ (by omega) (by omega)), by rw [ufRoots_congr hU]; exact h.cnt,
    fun k hk => ?_, fun k hk => ?_, fun k h1 h2 => ?_⟩
  · rw [hM _ (by omega) (by omega)]; exact h.par k hk
  · rw [hM _ (by omega) (by omega)]; exact h.mw k hk
  · rw [hM _ (by omega) (by omega), hM _ (by omega) (by omega), hM _ (by omega) (by omega)]
    exact h.ch k h1 h2

/-- The writes of one merge give the next state. `ra` is hung below `rb`; the two roots are those
of the ends of `q`, in some order. -/
theorem KRep.step (h : KRep M E s dep) (hI : s.Inv G l r) (hl : E.Lay) (hn : E.n = G.n) {q : ℕ}
    (hq : G.pu q < G.n ∧ G.pv q < G.n) {ra rb : ℕ}
    (hr : (rt M E.UF dep (G.pu q) = ra ∧ rt M E.UF dep (G.pv q) = rb) ∨
      (rt M E.UF dep (G.pu q) = rb ∧ rt M E.UF dep (G.pv q) = ra)) (hne : ra ≠ rb)
    (hsz : M (E.SZ + ra) ≤ M (E.SZ + rb)) :
    s.T.N + 2 ≤ 2 * E.n ∧ ∃ dep', KRep (kU E (kW E M s.T.N (M (E.TN + rt M E.UF dep (G.pu q)))
      (M (E.TN + rt M E.UF dep (G.pv q))) (G.pω q) q) ra rb s.T.N
      (M (E.SZ + ra) + M (E.SZ + rb))) E (kstep G s q) dep' := by
  have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4; have l5 := hl.l5
  have l6 := hl.l6; have l7 := hl.l7
  have hu := h.uf
  have hc := hu.cons
  set N := s.T.N with hNdef
  set a := s.top (G.pu q) with ha_def
  set b := s.top (G.pv q) with hb_def
  have hqu : G.pu q < E.n := by omega
  have hqv : G.pv q < E.n := by omega
  have hta : M (E.TN + rt M E.UF dep (G.pu q)) = a := hu.lab _ hqu
  have htb : M (E.TN + rt M E.UF dep (G.pv q)) = b := hu.lab _ hqv
  rw [hta, htb]
  have hrne : rt M E.UF dep (G.pu q) ≠ rt M E.UF dep (G.pv q) := by
    rcases hr with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact hne
    · exact Ne.symm hne
  have hab : a ≠ b := fun e => hrne ((hu.same _ hqu _ hqv).mpr e)
  obtain ⟨haN, -, -⟩ := hI.top _ hq.1
  obtain ⟨hbN, -, -⟩ := hI.top _ hq.2
  rw [← ha_def] at haN
  rw [← hb_def] at hbN
  have hpN : s.T.par N = N := hI.par_big N le_rfl
  have hnN : E.n ≤ N := by rw [hn]; exact hI.n_le
  -- the two roots
  have hra : ra < E.n ∧ M (E.UF + ra) = ra := by
    rcases hr with ⟨e1, -⟩ | ⟨-, e1⟩ <;> rw [← e1] <;> exact ⟨hc.rt_lt (by omega), hc.rt_is_root (by omega)⟩
  have hrb : rb < E.n ∧ M (E.UF + rb) = rb := by
    rcases hr with ⟨-, e1⟩ | ⟨e1, -⟩ <;> rw [← e1] <;> exact ⟨hc.rt_lt (by omega), hc.rt_is_root (by omega)⟩
  have hmem : ∀ x, x < E.n → M (E.UF + x) = x → x ∈ ufRoots M E.UF E.n := fun x hx hxx => by
    simp only [ufRoots, mem_filter, mem_range]; exact ⟨hx, hxx⟩
  have hcard2 : 2 ≤ (ufRoots M E.UF E.n).card := by
    have : ({ra, rb} : Finset ℕ) ⊆ ufRoots M E.UF E.n := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hmem _ hra.1 hra.2
      · exact hmem _ hrb.1 hrb.2
    have := card_le_card this
    rw [card_pair hne] at this
    exact this
  have hcnt := h.cnt
  have hN2 : N + 2 ≤ 2 * E.n := by omega
  refine ⟨hN2, ?_⟩
  -- the memory after the node writes
  set M1 := kW E M N a b (G.pω q) q with hM1
  have fr1 : ∀ x, x < E.KPAR → M1 x = M x := fun x hx => by
    simp only [M1, kW, Function.update_apply]
    split_ifs <;> first | rfl | omega
  have hU1 : ∀ y < E.n, M1 (E.UF + y) = M (E.UF + y) := fun y hy => fr1 _ (by omega)
  have hu1 : UFRep M1 E.UF E.SZ E.TN E.n dep s.top :=
    hu.frame hU1 (fun y hy => fr1 _ (by omega)) (fun y hy => fr1 _ (by omega))
  have hrt1 : ∀ x < E.n, rt M1 E.UF dep x = rt M E.UF dep x := fun x hx => hc.rt_congr hU1 hx
  have hsz1 : M1 (E.SZ + ra) ≤ M1 (E.SZ + rb) := by
    rw [fr1 _ (by omega), fr1 _ (by omega)]; exact hsz
  have hN' : ∀ x < E.n, s.top x ≠ N := fun x hx => by
    have := (hI.top x (by omega)).1; omega
  obtain ⟨hu2, -, hroots⟩ := UFRep.union hu1 hra.1 hrb.1 (by rw [fr1 _ (by omega)]; exact hra.2)
    (by rw [fr1 _ (by omega)]; exact hrb.2) hne hsz1 l1 l2 hN'
  rw [fr1 (E.SZ + ra) (by omega), fr1 (E.SZ + rb) (by omega)] at hu2 hroots
  refine ⟨fun x => if rt M1 E.UF dep x = ra then dep x + 1 else dep x, ?_⟩
  have hfr2 : ∀ x, E.KPAR ≤ x → kU E M1 ra rb N (M (E.SZ + ra) + M (E.SZ + rb)) x = M1 x := fun x hx => by
    simp only [kU, Function.update_apply]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- the new state
  have hks : kstep G s q = ⟨⟨N + 1, fun k => if k = a ∨ k = b then N else s.T.par k,
      Function.update s.T.ch1 N a, Function.update s.T.ch2 N b, Function.update s.T.mw N (G.pω q),
      Function.update s.T.mp N q⟩, fun x => if s.top x = a ∨ s.top x = b then N else s.top x⟩ := by
    simp only [kstep]; rw [if_neg hab]
  rw [hks]
  have hsame : ∀ x < E.n, (s.top x = a ∨ s.top x = b) ↔
      (rt M1 E.UF dep x = ra ∨ rt M1 E.UF dep x = rb) := fun x hx => by
    rw [hrt1 x hx, ← hu.same x hx _ hqu, ← hu.same x hx _ hqv]
    rcases hr with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact or_comm
  refine ⟨hu2.congr_top (fun x hx' => ?_), ?_, fun k hk => ?_, fun k hk => ?_, fun k h1 h2 => ?_⟩
  · simp only
    by_cases hx : s.top x = a ∨ s.top x = b
    · rw [if_pos hx, if_pos ((hsame x hx').mp hx)]
    · rw [if_neg hx, if_neg (fun e => hx ((hsame x hx').mpr e))]
  · rw [show ufRoots (kU E M1 ra rb N (M (E.SZ + ra) + M (E.SZ + rb))) E.UF E.n = (ufRoots M1 E.UF E.n).erase ra from hroots,
      ufRoots_congr hU1, card_erase_of_mem (hmem _ hra.1 hra.2)]
    simp only
    omega
  · simp only at hk ⊢
    rw [hfr2 _ (by omega), hM1, kW_par hl (by omega) (by omega) (by omega) (by omega)]
    by_cases hkN : k < N
    · have := h.par k hkN
      split_ifs <;> omega
    · have hk' : k = N := by omega
      subst hk'
      split_ifs <;> omega
  · simp only at hk ⊢
    rw [hfr2 _ (by omega), hM1, kW_mw hl (by omega) (by omega) (by omega) (by omega), Function.update_apply]
    by_cases hkN : k < N
    · have := h.mw k hkN
      split_ifs <;> omega
    · have hk' : k = N := by omega
      subst hk'
      simp
  · simp only at h2 ⊢
    rw [hfr2 _ (by omega), hfr2 _ (by omega), hfr2 _ (by omega), hM1,
      kW_ch1 hl (by omega) (by omega) (by omega) (by omega), kW_ch2 hl (by omega) (by omega) (by omega) (by omega),
      kW_mp hl (by omega) (by omega) (by omega) (by omega), Function.update_apply, Function.update_apply,
      Function.update_apply]
    by_cases hkN : k < N
    · obtain ⟨c1, c2, c3⟩ := h.ch k h1 hkN
      refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
    · have hk' : k = N := by omega
      subst hk'
      simp

end MinCostFlow.LowStretch
