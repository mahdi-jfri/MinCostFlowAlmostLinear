module

public import MinCostFlow.LSF.Program.InitWords
public import MinCostFlow.LSF.Program.InitFrame
public import MinCostFlow.LSF.Program.InitPhi
public import MinCostFlow.LSF.Program.InitRep
public import MinCostFlow.LSF.Program.InitCostSum
import MinCostFlow.LSF.Program.WstrThresh

/-!
# The program of `Initialize`, main path

`lsfInit_main_runs` is what the data-structure contract (`DSRep.Implements`) asks of
`Initialize`, for inputs with `2 ≤ n₀`: the body `mainBody` runs, and its final
memory represents a state that meets `lsfInitPost`, respects memory, and costs at most
`lsfInitCost` together with its potential.

The proof runs `main_wp` through `runs_dseqStmt`. The places are those of `InitVals` at the
numbers of the input (`initValsOf`). The lengths and weights are the real numbers read from the
input arrays (`memArrayReal`), which is what `lsfInitPost` speaks of. Every word bound comes
from `initWordBounds`, the cost from `initCost_total_le` and `lsfPhi_rep_le`, the space from
`initUseEnd_le`, the frame from `init_frame`, and the state from `init_lsfRep` and
`lsfInitPost_of_rep`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program MinCostFlow.WideWord
  MinCostFlow.Num InitDriver

@[expose] public section

/-- The places of the driver at the numbers of the input. -/
def initValsOf (G₀ : MGraph) (L_in L_w vCap eCap b : ℕ) : InitVals where
  b := b
  vCap := vCap
  eCap := eCap
  n0 := G₀.n
  m0 := G₀.E.card
  L_in := L_in
  L_w := L_w
  K_w := kWidthOf G₀.E.card L_in
  K := widthK G₀.E.card L_in
  H := 0
  LB := wstrLB G₀.n (hldDepthBound G₀.n) L_w

/-- A graph in the layout of `DynGraphLayout.lean` has at most `vCap` vertices and at most
`eCap` edges, since its vertex and edge names lie below these capacities. -/
lemma dynGraph_card_le {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hdg : DynGraphAt mem a vCap eCap G) : G.n ≤ vCap ∧ G.E.card ≤ eCap := by
  have hV : G.V ⊆ Finset.range vCap := fun u hu => Finset.mem_range.mpr (hdg.2.1 u hu)
  have hE : G.E ⊆ Finset.range eCap := fun e he => Finset.mem_range.mpr (hdg.2.2.1 e he)
  have h1 := Finset.card_le_card hV
  have h2 := Finset.card_le_card hE
  rw [Finset.card_range] at h1 h2
  exact ⟨h1, h2⟩

/-- The input facts of the tree phase, from the precondition and the word bounds. -/
lemma segBIn_of_pre {w h : ℕ} {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {mem : ℕ → ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr L_in P_fp kk L_w vCap eCap b : ℕ}
    (hc : 1 ≤ c_AN) (hh : 1 ≤ h) (hhw : 3 * h + 2 ≤ w)
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    (hlenB : lenArr + eCap0 * L_in ≤ b) (hwtB : wtArr + eCap0 * L_in ≤ b)
    (hLin : 1 ≤ L_in) (h2L : 2 ≤ h * L_in) (hPd : h ∣ P_fp) (hk : 1 ≤ kk)
    (hlv : ∀ e ∈ G₀.E, Num.Valid mem (lenArr + e * L_in) h L_in ∧ 0 < Num.fixVal mem (lenArr + e * L_in) h L_in P_fp)
    (hwv : ∀ e ∈ G₀.E, Num.Valid mem (wtArr + e * L_in) h L_in ∧ 0 < Num.fixVal mem (wtArr + e * L_in) h L_in P_fp)
    (WB : InitWordBounds w h Q_AN c_AN K_AN (initValsOf G₀ L_in L_w vCap eCap b) kk P_fp)
    (hlenw : lenArr < 2 ^ w) (hwtw : wtArr < 2 ^ w) :
    SegBIn w h Q_AN c_AN K_AN G₀ (memArrayReal mem wtArr G₀ h L_in P_fp)
      (memArrayReal mem lenArr G₀ h L_in P_fp) P_fp (initValsOf G₀ L_in L_w vCap eCap b)
      lenArr wtArr kk mem := by
  have hB : ∀ {arr : ℕ}, arr + eCap0 * L_in ≤ b → ∀ e ∈ G₀.E, arr + e * L_in + L_in ≤ b := by
    intro arr harr e he
    have he' : e + 1 ≤ eCap0 := hdg0.2.2.1 e he
    have := Nat.mul_le_mul_right L_in he'
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  exact
    { hh := hh
      hhw := hhw
      hLin := hLin
      h2L := h2L
      hPd := hPd
      hlenB := hB hlenB
      hwtB := hB hwtB
      hlv := fun e he => ⟨(hlv e he).1, (memArrayReal_eq he).symm, by
        rw [memArrayReal_eq he]; exact (hlv e he).2⟩
      hwv := fun e he => ⟨(hwv e he).1, (memArrayReal_eq he).symm, by
        rw [memArrayReal_eq he]; exact (hwv e he).2⟩
      hsp := WB.hsp
      hec := WB.hec
      hc := hc
      hl1 := WB.hl1
      hl3 := WB.hl3
      hl4 := WB.hl4
      hl5 := WB.hl5
      hl6 := WB.hl6
      hl7 := WB.hl7
      hspL := WB.hspL
      hk := hk
      hkw := WB.hkw3
      hwK := WB.hwK
      hlenw := hlenw
      hwtw := hwtw }

/-- The space bound of the specification, in the numbers of `initValsOf`. -/
lemma lsfInitSpace_eq {Q_AN : Program} {K_AN : ℝ} {c_AN h : ℕ} {G₀ : MGraph} {mem : ℕ → ℕ}
    {g0Ptr vCap0 eCap0 lenArr wtArr L_in P_fp kk L_w vCap eCap b : ℕ}
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀) :
    lsfInitSpace Q_AN K_AN c_AN h [g0Ptr, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap, eCap, b] mem =
      initSpaceV Q_AN K_AN c_AN h (initValsOf G₀ L_in L_w vCap eCap b) := by
  have hn : mem (g0Ptr + dgNOff) = G₀.n := hdg0.2.2.2.2.2.1
  have hm : mem (g0Ptr + dgMOff) = G₀.m := hdg0.2.2.2.2.2.2.1
  simp only [lsfInitSpace, initSpaceV, initValsOf, List.getD_cons_zero, List.getD_cons_succ]
  rw [hn, hm]
  rfl

/-- The cost bound of the specification, in the numbers of `initValsOf`. -/
lemma lsfInitCost_eq {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {h : ℕ} {G₀ : MGraph}
    {mem : ℕ → ℕ} {g0Ptr vCap0 eCap0 lenArr wtArr L_in P_fp kk L_w vCap eCap b : ℕ}
    (hdg0 : DynGraphAt mem g0Ptr vCap0 eCap0 G₀) :
    lsfInitCost Q_AN c_AN K_AN h [g0Ptr, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap, eCap, b] mem =
      lsfInitCostFactor * Nat.ceil (((G₀.E.card + G₀.n + 1 : ℕ) : ℝ) *
        lsfOverhead Q_AN c_AN K_AN G₀.n G₀.E.card L_in L_w h) := by
  have hn : mem (g0Ptr + dgNOff) = G₀.n := hdg0.2.2.2.2.2.1
  have hm : mem (g0Ptr + dgMOff) = G₀.m := hdg0.2.2.2.2.2.2.1
  simp only [lsfInitCost, List.getD_cons_zero, List.getD_cons_succ]
  rw [hn, hm]
  rfl

/-- `lsfInitPre` specialized to a fixed initial graph `G₀`. -/
def lsfInitPreFor (c_AN : ℕ) (K_AN : ℝ) (w h : ℕ) (G₀ : MGraph) (args : List ℕ)
    (mem : ℕ → ℕ) : Prop :=
  ∃ (v ℓ₀ : ℕ → ℝ)
    (g0Ptr vCap0 eCap0 lenArr wtArr L_in P_fp k_nat L_w vCap eCap b : ℕ),
    args = [g0Ptr, lenArr, wtArr, L_in, P_fp, k_nat, L_w, vCap, eCap, b] ∧
    1 ≤ c_AN ∧ 1 ≤ h ∧ 3 * h + 2 ≤ w ∧
    G₀.IsValid ∧ G₀.V.Nonempty ∧
    DynGraphAt mem g0Ptr vCap0 eCap0 G₀ ∧
    g0Ptr + dynGraphSize vCap0 eCap0 ≤ b ∧
    vCap0 ≤ vCap ∧ eCap0 ≤ eCap ∧ 1 ≤ eCap ∧
    lenArr + eCap0 * L_in ≤ b ∧ wtArr + eCap0 * L_in ≤ b ∧
    1 ≤ L_in ∧ 2 ≤ h * L_in ∧ h ∣ P_fp ∧ 1 ≤ k_nat ∧
    3 * (4 * k_nat * (hldDepthBound G₀.n + 1)) < 2 ^ w ∧
    L_in ≤ L_w ∧ 2 ≤ h * L_w ∧
    defaultThreshNat K_AN G₀.n k_nat < 2 ^ (h * (L_w - L_in)) ∧
    (∀ e ∈ G₀.E, Num.Valid mem (lenArr + e * L_in) h L_in ∧
      Num.fixVal mem (lenArr + e * L_in) h L_in P_fp = ℓ₀ e ∧ 0 < ℓ₀ e) ∧
    (∀ e ∈ G₀.E, Num.Valid mem (wtArr + e * L_in) h L_in ∧
      Num.fixVal mem (wtArr + e * L_in) h L_in P_fp = v e ∧ 0 < v e)

set_option maxHeartbeats 4000000 in
/-- The main path of `Initialize` (`2 ≤ n₀`) for a fixed initial graph `G₀`, also witnessing
`s'.G₀ = G₀`, with `+ 20` cost slack for the top-level branch on `n₀ = 1`. -/
theorem lsfInit_main_runs_slack_for {w h : ℕ} {p : Program} {I : InitIdx}
    {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ} {G₀ : MGraph}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots bG bA bWF : ℕ}
    (hlog : MeetsContract w p I.log2 log2Contract)
    (hprep : ∀ G₀, MeetsContract w p I.prep (prepStageContract w G₀))
    (hwid : MeetsContract w p I.widths (widthsContract w))
    (htree : ∀ G₀ v ℓ₀ P_fp vList eList, MeetsContract w p I.tree
      (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList))
    (hord : ∀ G₀ T₀ vList eList, MeetsContract w p I.order
      (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH))
    (hlb : MeetsContract w p I.lb (wstrLBContract w))
    (hdec : MeetsContract w p I.decomp
      (decompPhaseContract w h (defaultC_ceil K_AN) bWT bLB bW bCopy bFlag bRoots
        decompPhaseCost))
    (hf : MeetsContract w p I.forest (fPhaseContract w h bG bA bWF))
    (hs20 : MeetsContract w p I.store20 (storeArgsContract w 20))
    (hs24 : MeetsContract w p I.store24 (storeArgsContract w 24))
    {args : List ℕ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w) (hpre : lsfInitPreFor c_AN K_AN w h G₀ args mem)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + lsfInitSpace Q_AN K_AN c_AN h args mem < 2 ^ w)
    (hn2 : 2 ≤ mem (args.getD 0 0 + dgNOff)) :
    ∃ o st' c, Runs w p ω (mainBody I h) (startState args mem pos) o st' c ∧
      ∃ s' x', s'.G₀ = G₀ ∧ (LSFRep h).rep (heapArg args) s' x' st'.mem ∧
        lsfInitPost K_AN h args mem s' st'.mem ∧
        (LSFRep h).Respects (fun _ => False) (heapArg args)
          (lsfInitSpace Q_AN K_AN c_AN h args mem) mem o.value (heapArg args) x' st'.mem ∧
        c + (LSFRep h).phi (heapArg args) x' st'.mem + 20 ≤
          lsfInitCost Q_AN c_AN K_AN h args mem := by
  classical
  obtain ⟨v₀, ℓ₀, g0Ptr, vCap0, eCap0, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap, eCap, b,
    rfl, hc, hh, hhw, hG₀, -, hdg0, hg0, hvc, hec, hec1, hlenB, hwtB, hLin, h2L, hPd, hk, hk3, hLinw,
    -, hθ, hlv, hwv⟩ := hpre
  have hb : heapArg [g0Ptr, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap, eCap, b] = b := rfl
  rw [hb] at hz hsp ⊢
  have hn : mem (g0Ptr + dgNOff) = G₀.n := hdg0.2.2.2.2.2.1
  have hm : mem (g0Ptr + dgMOff) = G₀.E.card := hdg0.2.2.2.2.2.2.1
  simp only [List.getD_cons_zero] at hn2
  rw [hn] at hn2
  set V := initValsOf G₀ L_in L_w vCap eCap b with hV
  set v := memArrayReal mem wtArr G₀ h L_in P_fp with hvdef
  set ℓ := memArrayReal mem lenArr G₀ h L_in P_fp with hℓdef
  have hspV := hsp
  rw [lsfInitSpace_eq hdg0] at hspV
  have hLw : L_w < 2 ^ w := hwords L_w (by simp)
  have hPw : P_fp < 2 ^ w := hwords P_fp (by simp)
  have WB := initWordBounds Q_AN K_AN V hc hhw (show 1 ≤ G₀.n by omega) hLin rfl rfl rfl hspV
    hk3 hLw hPw
  have hlv' : ∀ e ∈ G₀.E, Num.Valid mem (lenArr + e * L_in) h L_in ∧
      0 < Num.fixVal mem (lenArr + e * L_in) h L_in P_fp :=
    fun e he => ⟨(hlv e he).1, (hlv e he).2.1 ▸ (hlv e he).2.2⟩
  have hwv' : ∀ e ∈ G₀.E, Num.Valid mem (wtArr + e * L_in) h L_in ∧
      0 < Num.fixVal mem (wtArr + e * L_in) h L_in P_fp :=
    fun e he => ⟨(hwv e he).1, (hwv e he).2.1 ▸ (hwv e he).2.2⟩
  have S := segBIn_of_pre (Q_AN := Q_AN) (K_AN := K_AN) (L_w := L_w) (vCap := vCap)
    (eCap := eCap) hc hh hhw hdg0 hlenB hwtB hLin h2L hPd hk hlv' hwv' WB
    (hwords lenArr (by simp)) (hwords wtArr (by simp))
  have hv0 : ∀ e ∈ G₀.E, 0 < v e := fun e he => (S.hwv e he).2.2
  obtain ⟨hn0', hm0'⟩ := dynGraph_card_le hdg0
  have hn0 : V.n0 ≤ V.vCap := le_trans hn0' hvc
  have hm0 : V.m0 ≤ V.eCap := le_trans hm0' hec
  have hC : defaultC_ceil K_AN < 2 ^ (h * V.L_w) := defaultC_lt hk hθ
  have hCθ : threshProd (defaultC_ceil K_AN) V.n0 kk = defaultThreshNat K_AN G₀.n kk :=
    threshProd_eq K_AN hk
  have hθ' : threshProd (defaultC_ceil K_AN) V.n0 kk < 2 ^ (h * (V.L_w - V.L_in)) := by
    rw [hCθ]; exact hθ
  have hVlt : ∀ u ∈ G₀.V, u < V.vCap := fun u hu => lt_of_lt_of_le (hdg0.2.1 u hu) hvc
  have hElt : ∀ e ∈ G₀.E, e < V.eCap := fun e he => lt_of_lt_of_le (hdg0.2.2.1 e he) hec
  -- the budget
  set Bsum := segACost V.n0 + segBCost V.n0 V.m0 (treeBound Q_AN c_AN K_AN h V) + segCCost V +
    segDCost V V.n0 + segECost V + segFCost with hBsum
  set space := lsfInitSpace Q_AN K_AN c_AN h [g0Ptr, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap,
    eCap, b] mem with hspace
  set L := Nat.log 2 (G₀.n + 2) + 1 with hL
  -- the final condition
  let Q : ℕ → (ℕ → ℕ) → Prop := fun o mem' =>
    ∃ s' x', s'.G₀ = G₀ ∧ (LSFRep h).rep b s' x' mem' ∧
      lsfInitPost K_AN h [g0Ptr, lenArr, wtArr, L_in, P_fp, kk, L_w, vCap, eCap, b] mem s' mem' ∧
      (LSFRep h).Respects (fun _ => False) b space mem o b x' mem' ∧
      (LSFRep h).phi b x' mem' ≤ 3000 * (G₀.n + 1) * L
  have hwp : SeqWP w p 10 rRet Q 0 (mainSteps I h) (startState [g0Ptr, lenArr, wtArr, L_in,
      P_fp, kk, L_w, vCap, eCap, b] mem pos).regs mem (Bsum + 2) := by
    refine main_wp (upClosed_wp rRet Q) V hlog (hprep G₀) hwid (htree G₀ v ℓ P_fp) (hord G₀) hlb
      hdec hf hs20 hs24 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl S hdg0 hg0 hvc hec hz rfl rfl rfl
      rfl rfl hn2 hn0 hm0 hec1 (show lenArr ≤ b by omega) hLinw hC WB.hw WB.hU WB.hl20 WB.hDw WB.hm0w WB.hLBw
      WB.hkw WB.hLw WB.hPw
      (fun vList eList hl hnd hmem => treeCostOf_le hh hv0 rfl hl hnd hmem) (Nat.le_add_right _ 2) ?_
    intro regs' cnt mem₁ mem₂ vList eList H mem₃ T_raw v₄ mem₄ v₅ mem₅ v₆ mem₆ v₇ mem₇ v₈ mem₈
      h₁ h₂ hvLen hvL heLen heNd heE heL h₃ hT IO h₄ ID h₅ IF h₆ h₇ h₈ hret
    refine ⟨?_, by omega⟩
    obtain ⟨C_reps, W_T, hp, x, hxv, hxe, hxn, hxt, hxL, hrep⟩ := init_lsfRep V S rfl rfl hn0
      hm0 hG₀ hVlt hElt hLinw hCθ hθ' h₁ h₂ hvLen hvL heLen heNd heE h₃ hT IO h₄ ID h₅ IF h₆ h₇ h₈
    obtain ⟨hlow, hzero⟩ := init_frame V hh hLin rfl rfl h₁ h₂ h₃ IO h₄ ID h₅ h₆ h₇ h₈
    obtain ⟨hH1, hH2, -⟩ := tree_ret V hh hLin h₃
    have hUe := initUseEnd_le Q_AN K_AN V hc rfl rfl rfl hH2
    have hWH : (V.withH H).lsstHeap ≤ (V.withH H).H := hH1
    have g9 := ((V.withH H).frame_places hWH rfl).2.2.2.2.2.2.2.2.2
    have u4 := (V.withH H).useEnd_ge.2.2.2
    have hend : (V.withH H).endA = V.endA := rfl
    have hlh : (V.withH H).lsstHeap = V.lsstHeap := rfl
    have hHH : (V.withH H).H = H := rfl
    have hsV : space = initSpaceV Q_AN K_AN c_AN h V := lsfInitSpace_eq hdg0
    have hbe : b ≤ V.endA := by
      show b ≤ lsfEndAddr b vCap eCap G₀.n (G₀.n - 1) L_w
      unfold lsfEndAddr; omega
    refine ⟨_, x, rfl, hrep, lsfInitPost_of_rep rfl hdg0 hp hrep hxv hxe hxL, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hret]; omega
    · rw [hret, hsV]
      unfold initSpaceV
      exact hUe
    · rw [hret]; exact hzero
    · intro a ha _; exact hlow a ha
    · intro a ha
      right
      obtain ⟨ha1, ha2⟩ := ha
      refine ⟨ha1, ?_⟩
      rw [hret]
      have hx : x.endAddr b = V.endA := by
        show lsfEndAddr b x.vCap x.eCap x.n0 x.tM x.L_w = V.endA
        rw [hxv, hxe, hxn, hxt, hxL]
        rfl
      change a < x.endAddr b at ha2
      omega
    · have hcard : (initLSFWith G₀ ℓ v (kk : ℝ) T_raw (vList.getD 0 0) C_reps
          (orderPi (OrderLayout.ofVals (V.withH H) (mem₃ V.outHdr)) mem₃ mem₄) W_T
          (defaultThreshNat K_AN G₀.n kk : ℝ)).T_cur.V.card ≤ x.n0 := by
        obtain ⟨-, -, -, -, -, -, hInv, hn0x, -⟩ := hrep
        rw [hInv.hT_cur_V]
        exact le_of_eq hn0x
      have := lsfPhi_rep_le hrep hcard
      rw [hxn] at this
      exact this
  obtain ⟨o, st', c, hr, ⟨s', x', hsG0, hrep, hpost, hresp, hphi⟩, hc'⟩ :=
    runs_dseqStmt (ω := ω) (mainSteps I h) 0 (startState [g0Ptr, lenArr, wtArr, L_in, P_fp, kk,
      L_w, vCap, eCap, b] mem pos) (Bsum + 2) 0 hwp
  refine ⟨o, st', c, hr, s', x', hsG0, hrep, hpost, hresp, ?_⟩
  have htot := initCost_total_le_slack Q_AN K_AN V hc hh (show 1 ≤ G₀.n by omega) rfl rfl
  rw [← hBsum] at htot
  have hphi' : (LSFRep h).phi b x' st'.mem ≤ 3000 * (V.n0 + 1) * initLg V.n0 := hphi
  have h1 : c + (LSFRep h).phi b x' st'.mem + 20 ≤
      Bsum + 3000 * (V.n0 + 1) * initLg V.n0 + 2 + 20 := by omega
  rw [lsfInitCost_eq hdg0]
  exact h1.trans htot

/-- The main path of `Initialize` (`2 ≤ n₀`) meets what `DSRep.Implements` asks of an
initialization, with `+ 20` cost slack for the top-level branch on `n₀ = 1`. -/
theorem lsfInit_main_runs_slack {w h : ℕ} {p : Program} {I : InitIdx}
    {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots bG bA bWF : ℕ}
    (hlog : MeetsContract w p I.log2 log2Contract)
    (hprep : ∀ G₀, MeetsContract w p I.prep (prepStageContract w G₀))
    (hwid : MeetsContract w p I.widths (widthsContract w))
    (htree : ∀ G₀ v ℓ₀ P_fp vList eList, MeetsContract w p I.tree
      (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList))
    (hord : ∀ G₀ T₀ vList eList, MeetsContract w p I.order
      (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH))
    (hlb : MeetsContract w p I.lb (wstrLBContract w))
    (hdec : MeetsContract w p I.decomp
      (decompPhaseContract w h (defaultC_ceil K_AN) bWT bLB bW bCopy bFlag bRoots
        decompPhaseCost))
    (hf : MeetsContract w p I.forest (fPhaseContract w h bG bA bWF))
    (hs20 : MeetsContract w p I.store20 (storeArgsContract w 20))
    (hs24 : MeetsContract w p I.store24 (storeArgsContract w 24))
    {args : List ℕ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w) (hpre : lsfInitPre c_AN K_AN w h args mem)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + lsfInitSpace Q_AN K_AN c_AN h args mem < 2 ^ w)
    (hn2 : 2 ≤ mem (args.getD 0 0 + dgNOff)) :
    ∃ o st' c, Runs w p ω (mainBody I h) (startState args mem pos) o st' c ∧
      ∃ s' x', (LSFRep h).rep (heapArg args) s' x' st'.mem ∧
        lsfInitPost K_AN h args mem s' st'.mem ∧
        (LSFRep h).Respects (fun _ => False) (heapArg args)
          (lsfInitSpace Q_AN K_AN c_AN h args mem) mem o.value (heapArg args) x' st'.mem ∧
        c + (LSFRep h).phi (heapArg args) x' st'.mem + 20 ≤
          lsfInitCost Q_AN c_AN K_AN h args mem := by
  obtain ⟨G₀, hpre'⟩ := hpre
  obtain ⟨o, st', c, hr, s', x', -, hrep, hpost, hresp, hc⟩ :=
    lsfInit_main_runs_slack_for hlog hprep hwid htree hord hlb hdec hf hs20 hs24 pos ω hwords hpre'
      hz hsp hn2
  exact ⟨o, st', c, hr, s', x', hrep, hpost, hresp, hc⟩

/-- The main path of `Initialize` (`2 ≤ n₀`) meets what `DSRep.Implements` asks of an
initialization: it runs, and its final memory represents a state that meets `lsfInitPost`,
respects memory with the space bound `lsfInitSpace`, and costs at most `lsfInitCost` together
with its potential. -/
theorem lsfInit_main_runs {w h : ℕ} {p : Program} {I : InitIdx}
    {Q_AN : Program} {c_AN : ℕ} {K_AN : ℝ}
    {bRoot bStore bOrder bT bTH bWT bLB bW bCopy bFlag bRoots bG bA bWF : ℕ}
    (hlog : MeetsContract w p I.log2 log2Contract)
    (hprep : ∀ G₀, MeetsContract w p I.prep (prepStageContract w G₀))
    (hwid : MeetsContract w p I.widths (widthsContract w))
    (htree : ∀ G₀ v ℓ₀ P_fp vList eList, MeetsContract w p I.tree
      (treePhaseContract Q_AN c_AN K_AN w h G₀ v ℓ₀ P_fp vList eList))
    (hord : ∀ G₀ T₀ vList eList, MeetsContract w p I.order
      (orderPhaseContract w h G₀ T₀ vList eList bRoot bStore bOrder bT bTH))
    (hlb : MeetsContract w p I.lb (wstrLBContract w))
    (hdec : MeetsContract w p I.decomp
      (decompPhaseContract w h (defaultC_ceil K_AN) bWT bLB bW bCopy bFlag bRoots
        decompPhaseCost))
    (hf : MeetsContract w p I.forest (fPhaseContract w h bG bA bWF))
    (hs20 : MeetsContract w p I.store20 (storeArgsContract w 20))
    (hs24 : MeetsContract w p I.store24 (storeArgsContract w 24))
    {args : List ℕ} {mem : ℕ → ℕ} (pos : ℕ) (ω : ℕ → Bool)
    (hwords : ∀ a ∈ args, a < 2 ^ w) (hpre : lsfInitPre c_AN K_AN w h args mem)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + lsfInitSpace Q_AN K_AN c_AN h args mem < 2 ^ w)
    (hn2 : 2 ≤ mem (args.getD 0 0 + dgNOff)) :
    ∃ o st' c, Runs w p ω (mainBody I h) (startState args mem pos) o st' c ∧
      ∃ s' x', (LSFRep h).rep (heapArg args) s' x' st'.mem ∧
        lsfInitPost K_AN h args mem s' st'.mem ∧
        (LSFRep h).Respects (fun _ => False) (heapArg args)
          (lsfInitSpace Q_AN K_AN c_AN h args mem) mem o.value (heapArg args) x' st'.mem ∧
        c + (LSFRep h).phi (heapArg args) x' st'.mem ≤ lsfInitCost Q_AN c_AN K_AN h args mem := by
  obtain ⟨o, st', c, hr, s', x', hrep, hpost, hresp, hc⟩ :=
    lsfInit_main_runs_slack hlog hprep hwid htree hord hlb hdec hf hs20 hs24 pos ω hwords hpre hz
      hsp hn2
  exact ⟨o, st', c, hr, s', x', hrep, hpost, hresp, le_trans (Nat.le_add_right _ 20) hc⟩

end

end MinCostFlow.LSF.Program
