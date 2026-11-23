module

public import MinCostFlow.LinkCut.Prog.LctForestProgram

/-!
# The link-cut tree meets the solver's forest contract

The main result is `lctForest_implements`. If a program holds the procedures
`lctForestBodies h L P b0` from index `b0` on, then procedure `b0` and procedures
`lctForestOp b0 i` implement `forestMachineContract lctForestModel w h L P rate allocation` with
the representation `lctForestRep w h L P N`. Here

* `rate n = 1000000 * (L + 1) * (log (n + 2) + 1)` (`lctForestRate`), and
* `allocation = lctForestAlloc w L N`: an operation may use `lctForestOpSpace L N` new words,
  and initialization with `n` vertices may use `lctArenaWords n + 10` words if `n ≤ N`.

No procedure uses random bits (`lctForestBodies_noRand`). Each case of the proof applies one run
theorem and checks that the room, space and cost bounds of the contract cover the ones of that
run theorem. These checks are the private lemmas below.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding MinCostFlow.IPM.Machine

section Arith

/-- A larger space bound is still met. -/
theorem respects_mono {σ : Type} {R : DSRep σ} {old : ℕ → Prop} {hp s1 s2 hp' b : ℕ}
    {mem mem' : ℕ → ℕ} {x' : R.τ} (h : R.Respects old hp s1 mem hp' b x' mem')
    (hle : s1 ≤ s2) : R.Respects old hp s2 mem hp' b x' mem' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, by omega, h3, h4, h5⟩

private theorem xl_le {X L lg LG : ℕ} (hX : X ≤ 930000 * (L + 1)) (hlg : lg ≤ LG) :
    X * lg ≤ 1000000 * (L + 1) * LG :=
  Nat.mul_le_mul (le_trans hX (by omega)) hlg

/-! The cost factors of the operations, and the small extra terms, fit in the rate and in the
space bound. -/

private theorem cF (L : ℕ) : C_FINDROOT_OP L ≤ 930000 * (L + 1) := by
  unfold C_FINDROOT_OP; omega
private theorem cL (L : ℕ) : C_LINK_OP L ≤ 930000 * (L + 1) := by unfold C_LINK_OP; omega
private theorem cC (L : ℕ) : C_CUT_OP L ≤ 930000 * (L + 1) := by unfold C_CUT_OP; omega
private theorem cPA (L : ℕ) : C_FINDROOT_OP L + C_PATHADD_OP L + C_CUT_OP L ≤ 930000 * (L + 1) := by
  unfold C_FINDROOT_OP C_PATHADD_OP C_CUT_OP; omega
private theorem cPM (L : ℕ) : C_FINDROOT_OP L + C_PATHMIN_OP L + C_CUT_OP L ≤ 930000 * (L + 1) := by
  unfold C_FINDROOT_OP C_PATHMIN_OP C_CUT_OP; omega
private theorem cPS (L : ℕ) : C_FINDROOT_OP L + C_PATHSUM_OP L + C_CUT_OP L ≤ 930000 * (L + 1) := by
  unfold C_FINDROOT_OP C_PATHSUM_OP C_CUT_OP; omega
private theorem eS (L k : ℕ) (hk : k ≤ 1000) : k ≤ 100 * L + 1000 := by omega
private theorem eS2 (L : ℕ) : 7 * L + 1 ≤ 100 * L + 1000 := by omega
private theorem eS3 (L : ℕ) : 18 * L + (L + 1) + 200 ≤ 100 * L + 1000 := by omega
private theorem eS4 (L : ℕ) : 18 * (2 * L + 4) + (2 * L + 5) + 200 ≤ 100 * L + 1000 := by omega
private theorem eC1 (L : ℕ) : 30 ≤ 70000 * (L + 1) := by omega
private theorem eC2 (L : ℕ) : 18 * L + (17 * L + 230) ≤ 70000 * (L + 1) := by omega
private theorem eC3 (L : ℕ) : 18 * (2 * L + 4) + 204 ≤ 70000 * (L + 1) := by omega
private theorem eC4 (L : ℕ) : 18 * L + 204 ≤ 70000 * (L + 1) := by omega

private theorem fit1 {hp phi PhiN XL M MN e L A W : ℕ} (hphi : phi ≤ PhiN) (hXL : XL ≤ A)
    (hM : M ≤ MN) (he : e ≤ 100 * L + 1000)
    (hroom : hp + (PhiN + A + MN + 100 * L + 1000) < W) :
    hp + phi + XL + M + e < W ∧ phi + XL + e ≤ PhiN + A + MN + 100 * L + 1000 := by
  omega

private theorem fit2 {hp phi PhiN XL M MN e1 e2 L A W : ℕ} (hphi : phi ≤ PhiN) (hXL : XL ≤ A)
    (hM : M ≤ MN) (he : e1 + e2 ≤ 100 * L + 1000)
    (hroom : hp + (PhiN + A + MN + 100 * L + 1000) < W) :
    hp + phi + XL + M + e1 + e2 < W ∧ phi + XL + e1 + e2 ≤ PhiN + A + MN + 100 * L + 1000 := by
  omega

private theorem fit3 {hp phi PhiN XL M MN e1 e2 e3 L A W : ℕ} (hphi : phi ≤ PhiN)
    (hXL : XL ≤ A) (hM : M ≤ MN) (he : e1 + e2 + e3 ≤ 100 * L + 1000)
    (hroom : hp + (PhiN + A + MN + 100 * L + 1000) < W) :
    hp + phi + XL + M + e1 + e2 + e3 < W ∧
      phi + XL + e1 + e3 ≤ PhiN + A + MN + 100 * L + 1000 := by
  omega

private theorem rate_split {X e L lg : ℕ} (hlg : 1 ≤ lg) (hX : X ≤ 930000 * (L + 1))
    (he : e ≤ 70000 * (L + 1)) : X * lg + e ≤ 1000000 * (L + 1) * lg := by
  have h1 : X * lg ≤ 930000 * (L + 1) * lg := Nat.mul_le_mul_right _ hX
  have h2 : 70000 * (L + 1) ≤ 70000 * (L + 1) * lg := Nat.le_mul_of_pos_right _ hlg
  have h3 : 1000000 * (L + 1) * lg = 930000 * (L + 1) * lg + 70000 * (L + 1) * lg := by ring
  omega

private theorem cost0 {c d phi' phi X lg L : ℕ} (hc : c + d + phi' ≤ phi + X * lg)
    (hlg : 1 ≤ lg) (hX : X ≤ 930000 * (L + 1)) : c + phi' ≤ 1000000 * (L + 1) * lg + phi := by
  have := rate_split (e := 0) hlg hX (by omega)
  omega

private theorem cost1 {c d phi' phi X lg e L : ℕ} (hc : c + d + phi' ≤ phi + X * lg + e)
    (hlg : 1 ≤ lg) (hX : X ≤ 930000 * (L + 1)) (he : e ≤ 70000 * (L + 1)) :
    c + phi' ≤ 1000000 * (L + 1) * lg + phi := by
  have := rate_split hlg hX he
  omega

private theorem cost2 {c d phi' phi X lg e1 e2 L : ℕ}
    (hc : c + d + phi' ≤ phi + X * lg + e1 + e2)
    (hlg : 1 ≤ lg) (hX : X ≤ 930000 * (L + 1)) (he : e1 + e2 ≤ 70000 * (L + 1)) :
    c + phi' ≤ 1000000 * (L + 1) * lg + phi := by
  have := rate_split hlg hX he
  omega

private theorem init_cost_le {c phi n L : ℕ} (hc : c + phi ≤ C_LCT_INIT * (n + 1) + 6) :
    c + phi ≤ lctForestRate L n * (n + 1) := by
  have h1 : 1 ≤ (L + 1) * (Nat.log 2 (n + 2) + 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have h2 : 1000000 * (n + 1) ≤ lctForestRate L n * (n + 1) := by
    unfold lctForestRate
    rw [show 1000000 * (L + 1) * (Nat.log 2 (n + 2) + 1) =
      1000000 * ((L + 1) * (Nat.log 2 (n + 2) + 1)) by ring]
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h1)
  unfold C_LCT_INIT at hc
  omega

end Arith

/-- Roots that agree on the vertices give the same root map. -/
private theorem rootsOn_congr {n : ℕ} {c c' : ℕ → ℕ} (h : ∀ z < n, c' z = c z) :
    rootsOn n c = rootsOn n c' := by
  funext z
  simp only [rootsOn]
  split_ifs with hz
  · exact (h z hz).symm
  · rfl

/-- The link-cut tree implements the solver's forest contract. -/
theorem lctForest_implements {w h L P N b0 : ℕ} {p : Program} (hh : 0 < h)
    (hw : 2 * h + 2 ≤ w) (hL : L < 2 ^ w) (hP : P < 2 ^ w)
    (hp : p.HasAt b0 (lctForestBodies h L P b0)) :
    (lctForestRep w h L P N).Implements w p b0 (lctForestOp b0)
      (forestMachineContract lctForestModel w h L P (lctForestRate L) (lctForestAlloc w L N)) := by
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hp5⟩ := lctForestBodies_procs hp
  have hbase := lctBaseOk_of_hasAt hh hw hL hP hp5
  have hsp : ∃ spB, (LctProcs.atBase (b0 + 5)).splay = SplayProcs.atBase spB :=
    ⟨b0 + 5 + 11, rfl⟩
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, -, -, h9, h10⟩ := lctBodies_procs hp5
  refine ⟨lctForestRep_local w h L P N, ?_, ?_⟩
  · -- initialization
    intro args mem pos ω _ hpre hz hroom
    obtain ⟨n, heap, rfl⟩ := hpre
    have hroom' : heap + lctForestAlloc w L N 6 [n, L, P, heap] < 2 ^ w := hroom
    by_cases hnN : n ≤ N
    swap
    · simp [lctForestAlloc, hnN] at hroom'
    simp only [lctForestAlloc, ↓reduceIte, List.getD_cons_zero, hnN] at hroom'
    obtain ⟨hp', st', c, x, hrun, hrep, hresp, hc⟩ :=
      lctInitWrap_runs (n := n) (heap := heap) (pos := pos) p (LctProcs.atBase (b0 + 5)) mem hh hw hL hP h0 hz
        (by omega) ω
    have hxn : x.n = n := hrep.2.2.2.2.1
    refine ⟨_, hw0, .returned hp', st', c, hrun, (MathForest.empty n, rootsOn n id), x,
      ⟨hrep, hnN, ?_⟩, rfl, ?_, ?_⟩
    · funext z
      by_cases hzn : z < n
      · have hs := (hrep.lctCanonRoot_spec (v := z) hzn).2.2.1
        have hzn' : z < (MathForest.empty n).n := hzn
        simp only [rootsOn, hzn, hzn', ↓reduceIte, id]
        exact ForestComp.empty_sameComp hs
      · have hzn' : ¬ z < (MathForest.empty n).n := hzn
        simp [rootsOn, hzn, hzn']
    · obtain ⟨r1, r2, r3, r4, r5⟩ := hresp
      refine ⟨r1, ?_, r3, r4, r5⟩
      show hp' ≤ heap + lctForestAlloc w L N 6 [n, L, P, heap]
      simp only [lctForestAlloc, ↓reduceIte, List.getD_cons_zero, hnN]
      omega
    · show c + lctPhi L st'.mem heap x.n ≤ lctForestRate L n * (n + 1)
      rw [hxn]
      exact init_cost_le hc
  · -- operations
    intro i b s x args mem pos ω _ hhead hrep hpre hfoot hz hroom
    obtain ⟨F, r⟩ := s
    obtain ⟨hrepL, hnN', hroots⟩ := hrep
    have hnN : F.n ≤ N := hnN'
    obtain ⟨hinv, -, hpre⟩ := hpre
    have hroots' : r = rootsOn F.n (lctCanonRoot mem b F.n) := hroots
    subst hroots'
    have hV : F.Valid := hinv.1
    have hxn : x.n = F.n := hrepL.2.2.2.2.1
    have hphi : lctPhi L mem b F.n ≤ lctPhiBound L N :=
      le_trans hrepL.lctPhi_le_bound (lctPhiBound_mono L hnN)
    have hlg : Nat.log 2 (F.n + 2) + 1 ≤ Nat.log 2 (N + 2) + 1 :=
      Nat.succ_le_succ (Nat.log_mono_right (by omega))
    have hM : 7000 * (L + 1) * (F.n + 2) ≤ 7000 * (L + 1) * (N + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have hlg1 : 1 ≤ Nat.log 2 (F.n + 2) + 1 := by omega
    rcases i with _ | _ | _ | _ | _ | _ | i
    · -- findRoot
      obtain ⟨b', v, heap, rfl, hv⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hv' : v < F.n := hv
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := fit1 (e := 2) hphi
        (xl_le (cF L) hlg) hM (eS L 2 (by decide)) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hans, -, hcanon, -, hc⟩ :=
        lctFindRootBody_runs (space := lctForestOpSpace L N) p (LctProcs.atBase (b0 + 5)) mem hbase hsp h9 hrepL hv'
          hfoot hz hr1 hs1 ω
      have hx'n : x'.n = F.n := hrep'.2.2.2.2.1
      refine ⟨_, h1, _, st', c, hrun, (F, rootsOn F.n (lctCanonRoot mem b F.n)), x',
        ⟨hrep', hnN, rootsOn_congr fun z _ => hcanon z⟩, ⟨rfl, ?_⟩, hresp, ?_⟩
      · show st'.mem heap = rootsOn F.n (lctCanonRoot mem b F.n) v
        simp only [rootsOn, hv', ↓reduceIte]
        exact hans
      · show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
        rw [hx'n, hxn]
        exact cost0 hc hlg1 (cF L)
    · -- link
      obtain ⟨b', a, heap, e, rfl, ha, hedge, heid, hu, hv, hdisc, hfresh, hfitL⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hu' : e.u < F.n := hu
      have hv' : e.v < F.n := hv
      have hfe : EdgeFits h L P e := hfitL e (by simp [lctForestModel, MathForest.link])
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := fit2 (e1 := 7 * L) (e2 := 1) hphi
        (xl_le (cL L) hlg) hM (eS2 L) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, hcanon⟩ :=
        lctLinkWrap_runs p (LctProcs.atBase (b0 + 5)) mem ω hbase hsp h9 h10 h2 hrepL hu' hv' hdisc hfresh heid hfe hedge
          ha hfoot hz hr1 hs1
      have hx'n : x'.n = F.n := hrep'.2.2.2.2.1
      refine ⟨_, hw1, _, st', c, hrun,
        (F.link e, lctLinkRoots F (rootsOn F.n (lctCanonRoot mem b F.n)) e), x',
        ⟨hrep', hnN, linkRoots_eq hu' hv' hcanon⟩, ⟨e, hedge, rfl⟩, hresp, ?_⟩
      show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
      rw [hx'n, hxn]
      exact cost1 hc hlg1 (cL L) (eC1 L)
    · -- cut
      obtain ⟨b', x1, y1, heap, rfl, -⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := fit1 (e := 1) hphi
        (xl_le (cC L) hlg) hM (eS L 1 (by decide)) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, hcr⟩ :=
        lctCutBody_runs (x := x1) (y := y1) (space := lctForestOpSpace L N) p (LctProcs.atBase (b0 + 5)) mem hbase hsp
          h9 h10 hrepL hfoot hz hr1 hs1 ω
      have hx'n : x'.n = F.n := hrep'.2.2.2.2.1
      have hc' : c + (hpf - heap) + lctPhi L st'.mem b F.n ≤
          lctPhi L mem b F.n + C_CUT_OP L * (Nat.log 2 (F.n + 2) + 1) := hc
      refine ⟨_, h3, _, st', c, hrun,
        (F.cut x1 y1, lctCutRoots F (rootsOn F.n (lctCanonRoot mem b F.n)) x1 y1), x',
        ⟨hrep', hnN, cutRoots_eq hcr⟩, rfl, hresp, ?_⟩
      show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
      rw [hx'n, hxn]
      exact cost0 hc' hlg1 (cC L)
    · -- pathAdd
      obtain ⟨b', u, v, a, heap, rfl, ha, hva, hsc, hfitA⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := fit3 (e1 := 18 * L) (e2 := L + 1) (e3 := 200) hphi
        (xl_le (cPA L) hlg) hM (eS3 L) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, hcanon⟩ :=
        lctPathAddWrap_runs p (LctProcs.atBase (b0 + 5)) mem ω hbase hsp h9 h10 h1 h3 h4 hrepL hV hsc ha hva
          (fun e he => hfitA e he) hfoot hz hr1
      have hx'n : x'.n = F.n := by rw [hrep'.2.2.2.2.1, pathAdd_n]
      refine ⟨_, hw2, _, st', c, hrun,
        (F.pathAdd u v (readRat mem a h L P), rootsOn F.n (lctCanonRoot mem b F.n)), x',
        ⟨hrep', by show (F.pathAdd u v _).n ≤ N; rw [pathAdd_n]; exact hnN, ?_⟩, rfl,
        respects_mono hresp hs1, ?_⟩
      · show rootsOn F.n (lctCanonRoot mem b F.n) = rootsOn (F.pathAdd u v _).n
          (lctCanonRoot st'.mem b (F.pathAdd u v _).n)
        rw [pathAdd_n]
        exact rootsOn_congr hcanon
      · show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
        rw [hx'n, hxn]
        exact cost2 hc hlg1 (cPA L) (eC2 L)
    · -- pathMin
      obtain ⟨b', u, v, heap, rfl, hsc⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := fit3 (e1 := 18 * (2 * L + 4)) (e2 := 2 * L + 5) (e3 := 200) hphi
        (xl_le (cPM L) hlg) hM (eS4 L) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, hans, hcanon⟩ :=
        lctPathMinWrap_runs p (LctProcs.atBase (b0 + 5)) mem ω hbase hsp h9 h10 h1 h3 h5 hrepL hV hsc hfoot hz hr1
      have hx'n : x'.n = F.n := hrep'.2.2.2.2.1
      refine ⟨_, hw3, _, st', c, hrun, (F, rootsOn F.n (lctCanonRoot mem b F.n)), x',
        ⟨hrep', hnN, rootsOn_congr hcanon⟩, ⟨rfl, hans⟩, respects_mono hresp hs1, ?_⟩
      show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
      rw [hx'n, hxn]
      exact cost2 hc hlg1 (cPM L) (eC3 L)
    · -- pathSum
      obtain ⟨b', u, v, heap, rfl, hsc, hfits⟩ := hpre
      obtain rfl : b = b' := (Option.some.inj hhead).symm
      have hroom' : heap + lctForestOpSpace L N < 2 ^ w := hroom
      obtain ⟨hr1, hs1⟩ := fit3 (e1 := 18 * L) (e2 := L + 1) (e3 := 200) hphi
        (xl_le (cPS L) hlg) hM (eS3 L) hroom'
      obtain ⟨hpf, st', c, x', hrun, hrep', hresp, hc, hans, hcanon⟩ :=
        lctPathSumWrap_runs p (LctProcs.atBase (b0 + 5)) mem ω hbase hsp h9 h10 h1 h3 h6 hrepL hV hsc hfits hfoot hz hr1
      have hx'n : x'.n = F.n := hrep'.2.2.2.2.1
      refine ⟨_, hw4, _, st', c, hrun, (F, rootsOn F.n (lctCanonRoot mem b F.n)), x',
        ⟨hrep', hnN, rootsOn_congr hcanon⟩, ⟨rfl, hans⟩, respects_mono hresp hs1, ?_⟩
      show c + lctPhi L st'.mem b x'.n ≤ lctForestRate L F.n + lctPhi L mem b x.n
      rw [hx'n, hxn]
      exact cost2 hc hlg1 (cPS L) (eC4 L)
    · exact hpre.elim

end MinCostFlow.LinkCut.Prog
