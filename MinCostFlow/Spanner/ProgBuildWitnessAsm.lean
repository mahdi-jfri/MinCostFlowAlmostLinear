module

public import MinCostFlow.Spanner.ProgBuildWitnessAsmHelpers

/-!
# Word-RAM Verification of Component Loops and Assembly for `buildWitnessCore` (`ProgBuildWitnessAsm`)

Verifies `buildCompWEdgesBody`, `buildCompJOrigBody`, `buildCompAsmBody`, and `buildAssembleStmt`,
transforming `CeLoopPost` into `AsmPost` with concrete `GraphAt`, `WSourcesAt`, and `JSourcesAt`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited WitnessCoreInput

/-! ## 1. Pure integer update helpers and loop invariants -/

private lemma wEdge_updates_agree {m m' : ℕ → ℕ} (wAddr Wm wIdx : ℕ)
    (hm_out : ∀ x,
      x ≠ wAddr + (2 + 2 * wIdx) → x ≠ wAddr + (3 + 2 * wIdx) →
      x ≠ wAddr + (2 + 2 * Wm) + wIdx →
      x ≠ wAddr + (2 + 2 * Wm) + Wm + 3 * wIdx →
      x ≠ wAddr + (2 + 2 * Wm) + Wm + (3 * wIdx + 1) →
      x ≠ wAddr + (2 + 2 * Wm) + Wm + (3 * wIdx + 2) → m' x = m x)
    (hwIdx : wIdx < Wm) :
    (∀ x < wAddr + 2, m' x = m x) ∧
    (∀ x, wAddr + (2 + 2 * Wm) + Wm + 3 * Wm ≤ x → m' x = m x) ∧
    (∀ idx < wIdx,
      m' (wAddr + 2 + 2 * idx) = m (wAddr + 2 + 2 * idx) ∧
      m' (wAddr + 3 + 2 * idx) = m (wAddr + 3 + 2 * idx) ∧
      m' (wAddr + (2 + 2 * Wm) + idx) = m (wAddr + (2 + 2 * Wm) + idx) ∧
      m' (wAddr + (2 + 2 * Wm) + Wm + 3 * idx) = m (wAddr + (2 + 2 * Wm) + Wm + 3 * idx) ∧
      m' (wAddr + (2 + 2 * Wm) + Wm + 3 * idx + 1) = m (wAddr + (2 + 2 * Wm) + Wm + 3 * idx + 1) ∧
      m' (wAddr + (2 + 2 * Wm) + Wm + 3 * idx + 2) = m (wAddr + (2 + 2 * Wm) + Wm + 3 * idx + 2)) ∧
    (∀ k, wIdx + 1 ≤ k → k < Wm →
      m' (wAddr + 2 + 2 * k) = m (wAddr + 2 + 2 * k) ∧
      m' (wAddr + 3 + 2 * k) = m (wAddr + 3 + 2 * k) ∧
      m' (wAddr + (2 + 2 * Wm) + k) = m (wAddr + (2 + 2 * Wm) + k) ∧
      ∀ t < 3, m' (wAddr + (2 + 2 * Wm) + Wm + 3 * k + t) =
        m (wAddr + (2 + 2 * Wm) + Wm + 3 * k + t)) := by
  refine ⟨fun x hx => hm_out x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    fun x hx => hm_out x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    fun idx hidx =>
      ⟨hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
       hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
       hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
       hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
       hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
       hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩,
    fun k hk hkw =>
      ⟨hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
       hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
       hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
       fun t ht => hm_out _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩⟩

private lemma wEdge_writes_cell (m : ℕ → ℕ) (wAddr Wm wIdx u v phi_lvl ci eL : ℕ)
    (hwIdx : wIdx < Wm) :
    let wWNumAddr := wAddr + (2 + 2 * Wm)
    let wSrcAddr := wWNumAddr + Wm
    let m_prev := Function.update (Function.update (Function.update (Function.update
      (Function.update m (wAddr + (2 + 2 * wIdx)) u)
        (wAddr + (3 + 2 * wIdx)) v)
        (wWNumAddr + wIdx) phi_lvl)
        (wSrcAddr + 3 * wIdx) 1)
        (wSrcAddr + (3 * wIdx + 1)) ci
    let m1 := Function.update m_prev (wSrcAddr + (3 * wIdx + 2)) eL
    m1 (wAddr + 2 + 2 * wIdx) = u ∧ m1 (wAddr + 3 + 2 * wIdx) = v ∧
    m1 (wWNumAddr + wIdx) = phi_lvl ∧ m1 (wSrcAddr + 3 * wIdx) = 1 ∧
    m1 (wSrcAddr + 3 * wIdx + 1) = ci ∧ m1 (wSrcAddr + 3 * wIdx + 2) = eL := by
  intro wWNumAddr wSrcAddr m_prev m1
  dsimp only [m1, m_prev]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),
      show wAddr + 2 + 2 * wIdx = wAddr + (2 + 2 * wIdx) by omega, Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      show wAddr + 3 + 2 * wIdx = wAddr + (3 + 2 * wIdx) by omega, Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_self]
  · rw [Function.update_of_ne (by omega),
      show wSrcAddr + 3 * wIdx + 1 = wSrcAddr + (3 * wIdx + 1) by omega, Function.update_self]
  · rw [show wSrcAddr + 3 * wIdx + 2 = wSrcAddr + (3 * wIdx + 2) by omega, Function.update_self]

private lemma jOrig_updates_agree {m m' : ℕ → ℕ} (jSrcAddr eJ : ℕ)
    (hm_out : ∀ x, x ≠ jSrcAddr + 3 * eJ → x ≠ jSrcAddr + (3 * eJ + 1) →
      x ≠ jSrcAddr + (3 * eJ + 2) → m' x = m x) :
    (∀ x < jSrcAddr, m' x = m x) ∧
    (∀ eJ', eJ' ≠ eJ → ∀ t < 3, m' (jSrcAddr + 3 * eJ' + t) = m (jSrcAddr + 3 * eJ' + t)) ∧
    (∀ Jm x, jSrcAddr + 3 * Jm ≤ x → eJ < Jm → m' x = m x) :=
  ⟨fun x hx => hm_out x (by omega) (by omega) (by omega),
   fun eJ' hne t ht => hm_out _ (by omega) (by omega) (by omega),
   fun Jm x hx hej => hm_out x (by omega) (by omega) (by omega)⟩

private lemma jOrig_writes_cell (m : ℕ → ℕ) (jSrcAddr eJ ci jL : ℕ) :
    let m1 := Function.update (Function.update (Function.update m (jSrcAddr + 3 * eJ) 2)
      (jSrcAddr + (3 * eJ + 1)) ci) (jSrcAddr + (3 * eJ + 2)) jL
    m1 (jSrcAddr + 3 * eJ) = 2 ∧ m1 (jSrcAddr + 3 * eJ + 1) = ci ∧ m1 (jSrcAddr + 3 * eJ + 2) = jL := by
  intro m1
  dsimp only [m1]
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · rw [Function.update_of_ne (by omega),
      show jSrcAddr + 3 * eJ + 1 = jSrcAddr + (3 * eJ + 1) by omega, Function.update_self]
  · rw [show jSrcAddr + 3 * eJ + 2 = jSrcAddr + (3 * eJ + 2) by omega, Function.update_self]

/-- Inner invariant inside component `ci` while writing `W_sub` edges `0 .. eLDone - 1`. -/
def CompWEdgesInv (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (mem₀ : ℕ → ℕ) (WSubs : List Graph) (aCompExt wAddr ci eLDone : ℕ) (st : State) : Prop :=
  let wd := inp.mkWitnessData ce pds WSubs
  let Wm := wd.W.m
  let wWNumAddr := wAddr + (2 + 2 * Wm)
  let wSrcAddr := wWNumAddr + Wm
  let jSrcAddr := wSrcAddr + 3 * Wm
  let hEnd := jSrcAddr + 3 * inp.prep.J.m
  let comp := wd.comps.getD ci defaultCompInfo
  eLDone ≤ comp.W_sub.m ∧
  CeBaseInv inp ce pds mem₀ st ∧
  st.regs 18 = aCompExt ∧ st.regs 23 = Wm ∧ st.regs 24 = wAddr ∧
  st.regs 25 = wWNumAddr ∧ st.regs 26 = wSrcAddr ∧ st.regs 27 = jSrcAddr ∧
  st.regs 28 = hEnd ∧ st.regs 29 = ci ∧
  st.regs 30 = inp.prep.cVertsPtr ci ∧
  st.regs 31 = inp.prep.cJOrigPtr ci ∧
  st.regs 32 = comp.J_sub.m ∧
  st.regs 33 = comp.wStart ∧
  st.regs 34 = st.mem (aCompExt + 6 * ci + 1) ∧
  st.regs 35 = inp.prep.phiNum_dec * 2 ^ comp.level ∧
  st.regs 36 = comp.W_sub.m ∧
  st.regs 37 = eLDone ∧
  inp.ValidWSubs ce WSubs ∧
  aCompExt + 6 * inp.prep.rawComps.length ≤ wAddr ∧
  hEnd ≤ inp.maxHeapEnd ce pds ∧
  CompExtAt st.mem aCompExt inp.prep.phiNum_dec wAddr wd.comps ∧
  (∀ x < inp.h, st.mem x = mem₀ x) ∧
  WitnessHdr0 st.mem inp ce pds ∧
  st.mem (inp.h + 12) = aCompExt ∧ st.mem (inp.h + 13) = wAddr ∧
  st.mem (inp.h + 14) = wWNumAddr ∧ st.mem (inp.h + 15) = wSrcAddr ∧
  st.mem (inp.h + 16) = jSrcAddr ∧
  st.mem wAddr = inp.prep.J.n ∧ st.mem (wAddr + 1) = Wm ∧
  (∀ k < inp.prep.j0Edges.length,
    let eJ := inp.prep.j0Edges[k]!
    let edge := inp.prep.J.edges[eJ]!
    st.mem (wAddr + 2 + 2 * k) = edge.1 ∧ st.mem (wAddr + 3 + 2 * k) = edge.2 ∧
    st.mem (wWNumAddr + k) = inp.prep.phiNum_dec ∧
    st.mem (wSrcAddr + 3 * k) = 0 ∧ st.mem (wSrcAddr + 3 * k + 1) = eJ ∧
    st.mem (wSrcAddr + 3 * k + 2) = 0 ∧
    st.mem (jSrcAddr + 3 * eJ) = 1 ∧ st.mem (jSrcAddr + 3 * eJ + 1) = k ∧
    st.mem (jSrcAddr + 3 * eJ + 2) = 0) ∧
  (∀ j (_hj : j < ci) eL' (_heL' : eL' < (wd.comps.getD j defaultCompInfo).W_sub.m),
    let cj := wd.comps.getD j defaultCompInfo
    let wIdx := cj.wStart + eL'
    let eW := cj.W_sub.edges[eL']!
    st.mem (wAddr + 2 + 2 * wIdx) = cj.verts[eW.1]! ∧
    st.mem (wAddr + 3 + 2 * wIdx) = cj.verts[eW.2]! ∧
    st.mem (wWNumAddr + wIdx) = inp.prep.phiNum_dec * 2 ^ cj.level ∧
    st.mem (wSrcAddr + 3 * wIdx) = 1 ∧
    st.mem (wSrcAddr + 3 * wIdx + 1) = j ∧
    st.mem (wSrcAddr + 3 * wIdx + 2) = eL') ∧
  (∀ j (_hj : j < ci) jL (_hjL : jL < (wd.comps.getD j defaultCompInfo).J_sub.m),
    let cj := wd.comps.getD j defaultCompInfo
    let eJ := cj.jSubOrigEdges[jL]!
    st.mem (jSrcAddr + 3 * eJ) = 2 ∧ st.mem (jSrcAddr + 3 * eJ + 1) = j ∧
    st.mem (jSrcAddr + 3 * eJ + 2) = jL) ∧
  (∀ eL' < eLDone,
    let wIdx := comp.wStart + eL'
    let eW := comp.W_sub.edges[eL']!
    st.mem (wAddr + 2 + 2 * wIdx) = comp.verts[eW.1]! ∧
    st.mem (wAddr + 3 + 2 * wIdx) = comp.verts[eW.2]! ∧
    st.mem (wWNumAddr + wIdx) = inp.prep.phiNum_dec * 2 ^ comp.level ∧
    st.mem (wSrcAddr + 3 * wIdx) = 1 ∧
    st.mem (wSrcAddr + 3 * wIdx + 1) = ci ∧
    st.mem (wSrcAddr + 3 * wIdx + 2) = eL') ∧
  (∀ k, comp.wStart + eLDone ≤ k → k < Wm →
    st.mem (wAddr + 2 + 2 * k) = 0 ∧ st.mem (wAddr + 3 + 2 * k) = 0 ∧
    st.mem (wWNumAddr + k) = 0 ∧ (∀ t < 3, st.mem (wSrcAddr + 3 * k + t) = 0)) ∧
  (∀ eJ < inp.prep.J.m, eJ ∉ inp.prep.j0Edges →
    (∀ j < ci, eJ ∉ (wd.comps.getD j defaultCompInfo).jSubOrigEdges) →
    ∀ t < 3, st.mem (jSrcAddr + 3 * eJ + t) = 0) ∧
  ZeroFrom st.mem hEnd

/-- Inner invariant inside component `ci` while recording `jSubOrigEdges[0 .. jLDone - 1]`. -/
def CompJOrigInv (inp : WitnessCoreInput) (ce : ConstructExpanderImpl) (pds : PathDSParams)
    (mem₀ : ℕ → ℕ) (WSubs : List Graph) (aCompExt wAddr ci jLDone : ℕ) (st : State) : Prop :=
  let wd := inp.mkWitnessData ce pds WSubs
  let Wm := wd.W.m
  let wWNumAddr := wAddr + (2 + 2 * Wm)
  let wSrcAddr := wWNumAddr + Wm
  let jSrcAddr := wSrcAddr + 3 * Wm
  let hEnd := jSrcAddr + 3 * inp.prep.J.m
  let comp := wd.comps.getD ci defaultCompInfo
  jLDone ≤ comp.J_sub.m ∧
  CeBaseInv inp ce pds mem₀ st ∧
  st.regs 18 = aCompExt ∧ st.regs 23 = Wm ∧ st.regs 24 = wAddr ∧
  st.regs 25 = wWNumAddr ∧ st.regs 26 = wSrcAddr ∧ st.regs 27 = jSrcAddr ∧
  st.regs 28 = hEnd ∧ st.regs 29 = ci ∧
  st.regs 31 = inp.prep.cJOrigPtr ci ∧
  st.regs 32 = comp.J_sub.m ∧
  st.regs 37 = jLDone ∧
  inp.ValidWSubs ce WSubs ∧
  aCompExt + 6 * inp.prep.rawComps.length ≤ wAddr ∧
  hEnd ≤ inp.maxHeapEnd ce pds ∧
  CompExtAt st.mem aCompExt inp.prep.phiNum_dec wAddr wd.comps ∧
  (∀ x < inp.h, st.mem x = mem₀ x) ∧
  WitnessHdr0 st.mem inp ce pds ∧
  st.mem (inp.h + 12) = aCompExt ∧ st.mem (inp.h + 13) = wAddr ∧
  st.mem (inp.h + 14) = wWNumAddr ∧ st.mem (inp.h + 15) = wSrcAddr ∧
  st.mem (inp.h + 16) = jSrcAddr ∧
  st.mem wAddr = inp.prep.J.n ∧ st.mem (wAddr + 1) = Wm ∧
  (∀ k < inp.prep.j0Edges.length,
    let eJ := inp.prep.j0Edges[k]!
    let edge := inp.prep.J.edges[eJ]!
    st.mem (wAddr + 2 + 2 * k) = edge.1 ∧ st.mem (wAddr + 3 + 2 * k) = edge.2 ∧
    st.mem (wWNumAddr + k) = inp.prep.phiNum_dec ∧
    st.mem (wSrcAddr + 3 * k) = 0 ∧ st.mem (wSrcAddr + 3 * k + 1) = eJ ∧
    st.mem (wSrcAddr + 3 * k + 2) = 0 ∧
    st.mem (jSrcAddr + 3 * eJ) = 1 ∧ st.mem (jSrcAddr + 3 * eJ + 1) = k ∧
    st.mem (jSrcAddr + 3 * eJ + 2) = 0) ∧
  (∀ j (_hj : j < ci + 1) eL' (_heL' : eL' < (wd.comps.getD j defaultCompInfo).W_sub.m),
    let cj := wd.comps.getD j defaultCompInfo
    let wIdx := cj.wStart + eL'
    let eW := cj.W_sub.edges[eL']!
    st.mem (wAddr + 2 + 2 * wIdx) = cj.verts[eW.1]! ∧
    st.mem (wAddr + 3 + 2 * wIdx) = cj.verts[eW.2]! ∧
    st.mem (wWNumAddr + wIdx) = inp.prep.phiNum_dec * 2 ^ cj.level ∧
    st.mem (wSrcAddr + 3 * wIdx) = 1 ∧
    st.mem (wSrcAddr + 3 * wIdx + 1) = j ∧
    st.mem (wSrcAddr + 3 * wIdx + 2) = eL') ∧
  (∀ j (_hj : j < ci) jL (_hjL : jL < (wd.comps.getD j defaultCompInfo).J_sub.m),
    let cj := wd.comps.getD j defaultCompInfo
    let eJ := cj.jSubOrigEdges[jL]!
    st.mem (jSrcAddr + 3 * eJ) = 2 ∧ st.mem (jSrcAddr + 3 * eJ + 1) = j ∧
    st.mem (jSrcAddr + 3 * eJ + 2) = jL) ∧
  (∀ jL' < jLDone,
    let eJ := comp.jSubOrigEdges[jL']!
    st.mem (jSrcAddr + 3 * eJ) = 2 ∧ st.mem (jSrcAddr + 3 * eJ + 1) = ci ∧
    st.mem (jSrcAddr + 3 * eJ + 2) = jL') ∧
  (∀ k, comp.wStart + comp.W_sub.m ≤ k → k < Wm →
    st.mem (wAddr + 2 + 2 * k) = 0 ∧ st.mem (wAddr + 3 + 2 * k) = 0 ∧
    st.mem (wWNumAddr + k) = 0 ∧ (∀ t < 3, st.mem (wSrcAddr + 3 * k + t) = 0)) ∧
  (∀ eJ < inp.prep.J.m, eJ ∉ inp.prep.j0Edges →
    (∀ j < ci, eJ ∉ (wd.comps.getD j defaultCompInfo).jSubOrigEdges) →
    eJ ∉ comp.jSubOrigEdges.take jLDone →
    ∀ t < 3, st.mem (jSrcAddr + 3 * eJ + t) = 0) ∧
  ZeroFrom st.mem hEnd

/-! ## 2. Verification of `buildCompWEdgesBody` -/

private lemma buildCompWEdgesBody_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {m regs : ℕ → ℕ} {pos : ℕ}
    {wAddr wWNumAddr wSrcAddr wSubPtr cvPtr wStart phiLvl ci eL uL vL u v : ℕ}
    (hr24 : regs 24 = wAddr) (hr25 : regs 25 = wWNumAddr) (hr26 : regs 26 = wSrcAddr)
    (hr29 : regs 29 = ci) (hr30 : regs 30 = cvPtr) (hr33 : regs 33 = wStart)
    (hr34 : regs 34 = wSubPtr) (hr35 : regs 35 = phiLvl) (hr37 : regs 37 = eL)
    (hm_uL : m (wSubPtr + (2 + 2 * eL)) = uL)
    (hm_vL : m (wSubPtr + (3 + 2 * eL)) = vL)
    (hm_u : m (cvPtr + uL) = u) (hm_v : m (cvPtr + vL) = v)
    (h1_w : 1 < 2 ^ w) (h2_w : 2 < 2 ^ w) (h3_w : 3 < 2 ^ w)
    (hci_w : ci < 2 ^ w) (heL_w : eL < 2 ^ w) (hu_w : u < 2 ^ w) (hv_w : v < 2 ^ w)
    (hwSubPtr_w : wSubPtr < 2 ^ w) (hcvPtr_w : cvPtr < 2 ^ w)
    (hwA_w : wAddr < 2 ^ w) (hwwn_base_w : wWNumAddr < 2 ^ w) (hwSrc_base_w : wSrcAddr < 2 ^ w)
    (h2eL_w : 2 * eL < 2 ^ w) (h2p2eL_w : 2 + 2 * eL < 2 ^ w) (h3p2eL_w : 3 + 2 * eL < 2 ^ w)
    (hws2_w : wSubPtr + (2 + 2 * eL) < 2 ^ w) (hws3_w : wSubPtr + (3 + 2 * eL) < 2 ^ w)
    (huL_lt_w : uL < 2 ^ w) (hvL_lt_w : vL < 2 ^ w)
    (hcvu_w : cvPtr + uL < 2 ^ w) (hcvv_w : cvPtr + vL < 2 ^ w)
    (hwStart_w : wStart < 2 ^ w)
    (hwIdx_w : wStart + eL < 2 ^ w) (h2wIdx_w : 2 * (wStart + eL) < 2 ^ w)
    (h2p2wIdx_w : 2 + 2 * (wStart + eL) < 2 ^ w) (h3p2wIdx_w : 3 + 2 * (wStart + eL) < 2 ^ w)
    (hwA2_w : wAddr + (2 + 2 * (wStart + eL)) < 2 ^ w)
    (hwA3_w : wAddr + (3 + 2 * (wStart + eL)) < 2 ^ w)
    (hwwn_w : wWNumAddr + (wStart + eL) < 2 ^ w)
    (h3wIdx_w : 3 * (wStart + eL) < 2 ^ w) (hwS0_w : wSrcAddr + 3 * (wStart + eL) < 2 ^ w)
    (h3wIdx1_w : 3 * (wStart + eL) + 1 < 2 ^ w) (hwS1_w : wSrcAddr + (3 * (wStart + eL) + 1) < 2 ^ w)
    (h3wIdx2_w : 3 * (wStart + eL) + 2 < 2 ^ w) (hwS2_w : wSrcAddr + (3 * (wStart + eL) + 2) < 2 ^ w)
    (hphi_w : phiLvl < 2 ^ w) :
    let wIdx := wStart + eL
    let m_prev := Function.update (Function.update (Function.update (Function.update
      (Function.update m (wAddr + (2 + 2 * wIdx)) u)
        (wAddr + (3 + 2 * wIdx)) v)
        (wWNumAddr + wIdx) phiLvl)
        (wSrcAddr + 3 * wIdx) 1)
        (wSrcAddr + (3 * wIdx + 1)) ci
    let m' := Function.update m_prev (wSrcAddr + (3 * wIdx + 2)) eL
    let regs' := Function.update (Function.update (Function.update
      (Function.update (Function.update regs 38 uL) 39 vL) 38 u) 39 v) 40 wIdx
    ∃ o st' c, Runs w p ω buildCompWEdgesBody ⟨m, regs, pos⟩ o st' c ∧
      (o = .normal ∧ st' = ⟨m', regs', pos⟩) ∧ c ≤ asmWEdgeCost := by
  intro wIdx m_prev m' regs'
  dsimp only [buildCompWEdgesBody]
  refine runs_start_le ?_
  refine runs_seq_assign_flat (v := uL)
    (e := .load (.bin .add (.reg 34) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 37)))))
    (ev_load (ev_add (ev_reg hr34 hwSubPtr_w)
      (ev_add (ev_const h2_w) (ev_mul (ev_const h2_w) (ev_reg hr37 heL_w) h2eL_w) h2p2eL_w) hws2_w)
      hm_uL huL_lt_w) ?_
  refine runs_seq_assign_flat (v := vL)
    (e := .load (.bin .add (.reg 34) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 37)))))
    (ev_load (ev_add
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide)]; exact hr34) hwSubPtr_w)
      (ev_add (ev_const h3_w) (ev_mul (ev_const h2_w)
        (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide)]; exact hr37) heL_w) h2eL_w) h3p2eL_w)
      hws3_w) hm_vL hvL_lt_w) ?_
  refine runs_seq_assign_flat (v := u) (e := .load (.bin .add (.reg 30) (.reg 38)))
    (ev_load (ev_add
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr30) hcvPtr_w)
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]) huL_lt_w) hcvu_w)
      hm_u hu_w) ?_
  refine runs_seq_assign_flat (v := v) (e := .load (.bin .add (.reg 30) (.reg 39)))
    (ev_load (ev_add
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hr30) hcvPtr_w)
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]) hvL_lt_w) hcvv_w)
      hm_v hv_w) ?_
  refine runs_seq_assign_flat (v := wIdx) (e := .bin .add (.reg 33) (.reg 37))
    (ev_add
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr33) hwStart_w)
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr37) heL_w)
      hwIdx_w) ?_
  refine runs_seq_store_flat (x := wAddr + (2 + 2 * wIdx)) (v := u)
    (ea := .bin .add (.reg 24) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 40))))
    (ev := .reg 38)
    (ev_add
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hr24) hwA_w)
      (ev_add (ev_const h2_w) (ev_mul (ev_const h2_w)
        (ev_reg (by dsimp only; rw [Function.update_self]) hwIdx_w) h2wIdx_w) h2p2wIdx_w) hwA2_w)
    (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self]) hu_w) ?_
  refine runs_seq_store_flat (x := wAddr + (3 + 2 * wIdx)) (v := v)
    (ea := .bin .add (.reg 24) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 40))))
    (ev := .reg 39)
    (ev_add
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hr24) hwA_w)
      (ev_add (ev_const h3_w) (ev_mul (ev_const h2_w)
        (ev_reg (by dsimp only; rw [Function.update_self]) hwIdx_w) h2wIdx_w) h3p2wIdx_w) hwA3_w)
    (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]) hv_w) ?_
  refine runs_seq_store_flat (x := wWNumAddr + wIdx) (v := phiLvl)
    (ea := .bin .add (.reg 25) (.reg 40)) (ev := .reg 35)
    (ev_add
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hr25) hwwn_base_w)
      (ev_reg (by dsimp only; rw [Function.update_self]) hwIdx_w) hwwn_w)
    (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact hr35) hphi_w) ?_
  refine runs_seq_store_flat (x := wSrcAddr + 3 * wIdx) (v := 1)
    (ea := .bin .add (.reg 26) (.bin .mul (.const 3) (.reg 40))) (ev := .const 1)
    (ev_add
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hr26) hwSrc_base_w)
      (ev_mul (ev_const h3_w) (ev_reg (by dsimp only; rw [Function.update_self]) hwIdx_w) h3wIdx_w) hwS0_w)
    (ev_const h1_w) ?_
  refine runs_seq_store_flat (x := wSrcAddr + (3 * wIdx + 1)) (v := ci)
    (ea := .bin .add (.reg 26) (.bin .add (.bin .mul (.const 3) (.reg 40)) (.const 1)))
    (ev := .reg 29)
    (ev_add
      (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide)]; exact hr26) hwSrc_base_w)
      (ev_add (ev_mul (ev_const h3_w) (ev_reg (by dsimp only; rw [Function.update_self]) hwIdx_w) h3wIdx_w)
        (ev_const h1_w) h3wIdx1_w) hwS1_w)
    (ev_reg (by dsimp only; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide)]; exact hr29) hci_w) ?_
  refine ⟨.normal, ⟨m', regs', pos⟩, _,
    runs_store_iff.mpr ⟨wSrcAddr + (3 * wIdx + 2), eL,
      ev_add
        (ev_reg (by dsimp only [regs']; rw [Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr26) hwSrc_base_w)
        (ev_add (ev_mul (ev_const h3_w)
          (ev_reg (by dsimp only [regs']; rw [Function.update_self]) hwIdx_w)
          h3wIdx_w) (ev_const h2_w) h3wIdx2_w) hwS2_w,
      ev_reg (by dsimp only [regs']; rw [Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide),
        Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hr37) heL_w,
      rfl, rfl, rfl⟩,
    ⟨rfl, rfl⟩, by norm_num [asmWEdgeCost, Expr.size]⟩

private theorem buildCompWEdgesBody_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ : ℕ → ℕ} {WSubs : List Graph} {aCompExt wAddr ci eL : ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) (hci : ci < inp.prep.rawComps.length) :
    let wd := inp.mkWitnessData ce pds WSubs
    let comp := wd.comps.getD ci defaultCompInfo
    Triple w p
      (fun st => CompWEdgesInv inp ce pds mem₀ WSubs aCompExt wAddr ci eL st ∧ eL < comp.W_sub.m)
      buildCompWEdgesBody
      (normalPost fun st =>
        CompWEdgesInv inp ce pds mem₀ WSubs aCompExt wAddr ci (eL + 1)
          { st with regs := Function.update st.regs 37 (eL + 1) } ∧ st.regs 37 = eL)
      (fun _ => asmWEdgeCost) := by
  intro wd comp st ω ⟨hP, heL⟩
  cases st with | mk m regs pos =>
  rcases hP with ⟨_, hbase, hr18, hr23, hr24, hr25, hr26, hr27, hr28, hr29,
    hr30, hr31, hr32, hr33, hr34, hr35, hr36, hr37,
    hws, ha_ext, hmax_le, hcomp_ext, hbelow, hhdr0, hm12, hm13, hm14, hm15, hm16,
    hm_n, hm_m, hprev_j0, hprev_w, hprev_j, hcur_w, hzero_w, hzero_j, hzf⟩
  dsimp only at hr18 hr23 hr24 hr25 hr26 hr27 hr28 hr29 hr30 hr31 hr32 hr33 hr34 hr35 hr36 hr37
  dsimp only at hcomp_ext hbelow hhdr0 hm12 hm13 hm14 hm15 hm16 hm_n hm_m hprev_j0 hprev_w hprev_j hcur_w hzero_w hzero_j hzf
  set Wm := wd.W.m
  set wWNumAddr := wAddr + (2 + 2 * Wm)
  set wSrcAddr := wWNumAddr + Wm
  set jSrcAddr := wSrcAddr + 3 * Wm
  set hEnd := jSrcAddr + 3 * inp.prep.J.m
  rcases ce_word_bounds hvalid with ⟨h1w, hheap_w, hm_w⟩
  rcases hvalid.2.2.1 with ⟨_, _, _, _, _, _, _, _, hpn, hpnd, _, _, _, _, _, _, _, _, _, hwb⟩
  have h_in_lt := inp.input_reads_lt_h hvalid
  have hEnd_lt_w : hEnd < 2 ^ w := lt_of_le_of_lt hmax_le hheap_w
  have ha_lo : inp.h + 20 ≤ aCompExt := by
    rw [← hr18]; exact hbase.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcomps_len : wd.comps.length = inp.prep.rawComps.length :=
    buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
  have hci_wd : ci < wd.comps.length := by rw [hcomps_len]; exact hci
  have hce_ci := hcomp_ext ci hci_wd
  dsimp only at hce_ci
  have hcomp_eq : wd.comps[ci] = comp := by simp [comp, List.getD_eq_getElem?_getD, hci_wd]
  rw [hcomp_eq] at hce_ci
  rcases hce_ci with ⟨hws_ci, h2l_ci, hpn_ci, hv_len_ci, hwm_ci, hg_wsub, hwsub_lo, hwsub_hi⟩
  set wSubPtr := m (aCompExt + 6 * ci + 1)
  set wIdx := comp.wStart + eL
  have hwm_sum := mkWitnessData_W_m_eq_sum inp ce pds hws.1
  have hw_ci := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 ci hci
  have hwStart_eq_ci : comp.wStart = inp.prep.j0Edges.length + ((WSubs.take ci).map Graph.m).sum := by
    rw [← hcomp_eq]; exact hw_ci.1
  have hWsub_eq_ci : comp.W_sub = WSubs[ci]'(by rw [hws.1]; exact hci) := by
    rw [← hcomp_eq]; exact hw_ci.2.1
  have hwIdx_lt_Wm : wIdx < Wm := by
    change wd.W.m = _ at hwm_sum
    have htake_succ : ((WSubs.take (ci + 1)).map Graph.m).sum =
        ((WSubs.take ci).map Graph.m).sum + comp.W_sub.m := by
      rw [List.take_succ_eq_append_getElem (by rw [hws.1]; exact hci), List.map_append, List.sum_append]
      simp [hWsub_eq_ci]
    have hle := hw_ci.2.2.2.2.2.2.2
    omega
  have hwStart_ge_j0 : inp.prep.j0Edges.length ≤ comp.wStart := by rw [hwStart_eq_ci]; omega
  have hj_end_le_wStart : ∀ j < ci,
      (wd.comps.getD j defaultCompInfo).wStart + (wd.comps.getD j defaultCompInfo).W_sub.m ≤
        comp.wStart := by
    intro j hj
    have hj_lt_rc : j < inp.prep.rawComps.length := lt_trans hj hci
    have hj_wd : j < wd.comps.length := lt_trans hj hci_wd
    have hw_j := buildCompsFrom_getElem inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1 j hj_lt_rc
    have hj_eq : wd.comps[j] = wd.comps.getD j defaultCompInfo := by
      simp [List.getD_eq_getElem?_getD, hj_wd]
    have hws_j : (wd.comps.getD j defaultCompInfo).wStart =
        inp.prep.j0Edges.length + ((WSubs.take j).map Graph.m).sum := by
      rw [← hj_eq]; exact hw_j.1
    have hWsub_j : (wd.comps.getD j defaultCompInfo).W_sub = WSubs[j]'(by rw [hws.1]; exact hj_lt_rc) := by
      rw [← hj_eq]; exact hw_j.2.1
    rw [hwStart_eq_ci, hws_j]
    have htake_succ : ((WSubs.take (j + 1)).map Graph.m).sum =
        ((WSubs.take j).map Graph.m).sum + (wd.comps.getD j defaultCompInfo).W_sub.m := by
      rw [List.take_succ_eq_append_getElem (by rw [hws.1]; exact hj_lt_rc), List.map_append, List.sum_append]
      rw [← hWsub_j]; simp
    linarith [htake_succ, take_map_sum_mono (j + 1) ci WSubs hj]
  have hWsub_prop : (WSubs[ci]'(by rw [hws.1]; exact hci)).n = inp.prep.rawComps[ci].2.length ∧
      (WSubs[ci]'(by rw [hws.1]; exact hci)).IsValid := by
    have hp := hws.2 ci hci
    have hget : WSubs.getD ci ⟨0, []⟩ = WSubs[ci]'(by rw [hws.1]; exact hci) := by
      simp [List.getD_eq_getElem?_getD, hws.1, hci]
    rw [hget] at hp
    exact ⟨hp.1, hp.2.1⟩
  have hWsub_valid : comp.W_sub.IsValid := by rw [hWsub_eq_ci]; exact hWsub_prop.2
  have hWsub_n : comp.W_sub.n = inp.prep.rawComps[ci].2.length := by rw [hWsub_eq_ci]; exact hWsub_prop.1
  have heW_u_lt : comp.W_sub.edges[eL].1 < comp.W_sub.n :=
    (hWsub_valid _ (List.getElem_mem heL)).1
  have heW_v_lt : comp.W_sub.edges[eL].2 < comp.W_sub.n :=
    (hWsub_valid _ (List.getElem_mem heL)).2
  have hcprops := comp_props_at hvalid.2.2.1.toValid_zeroTail hci
  have hrc_bang : inp.prep.rawComps[ci]! = inp.prep.rawComps[ci] := by simp [hci]
  have hverts_eq : comp.verts = inp.prep.rawComps[ci].2 := by
    have hpw_c : inp.prep.rawComps[ci].2.Pairwise (· < ·) := by
      rw [← hrc_bang]; exact hcprops.2.2.1
    have hverts_wd : wd.comps[ci].verts = vertsOf inp.prep.rawComps[ci].2.toFinset := by
      dsimp only [wd, mkWitnessData]; exact hw_ci.2.2.2.2.1
    rw [← hcomp_eq, hverts_wd]
    exact vertsOf_toFinset_of_pairwise_lt hpw_c
  have huL_lt_verts : comp.W_sub.edges[eL].1 < comp.verts.length := by rw [hverts_eq, ← hWsub_n]; exact heW_u_lt
  have hvL_lt_verts : comp.W_sub.edges[eL].2 < comp.verts.length := by rw [hverts_eq, ← hWsub_n]; exact heW_v_lt
  have hverts_at : ListAt m (inp.prep.cVertsPtr ci) inp.prep.rawComps[ci].2 :=
    (rawComps_recordAt hvalid.2.2.1.toValid_zeroTail
      (fun x hx => by simp [hx]; exact hbelow x (lt_of_lt_of_le hx (by have := h_in_lt.2.2.2.1; omega))) hci).2.2
  have hc_lt_h := h_in_lt.2.2.2.2.2.2.2 ci hci
  set uL := comp.W_sub.edges[eL].1
  set vL := comp.W_sub.edges[eL].2
  set u := comp.verts[uL]
  set v := comp.verts[vL]
  have hm_uL : m (wSubPtr + (2 + 2 * eL)) = uL := by
    simpa [Nat.add_assoc] using graphAt_edge_fst hg_wsub heL
  have hm_vL : m (wSubPtr + (3 + 2 * eL)) = vL := by
    have hs := graphAt_edge_snd hg_wsub heL
    simpa [show wSubPtr + 3 + 2 * eL = wSubPtr + (3 + 2 * eL) by omega] using hs
  have hm_u : m (inp.prep.cVertsPtr ci + uL) = u := by
    have h1 := hverts_at uL (by rw [← hverts_eq]; exact huL_lt_verts)
    simpa [u, hverts_eq] using h1
  have hm_v : m (inp.prep.cVertsPtr ci + vL) = v := by
    have h1 := hverts_at vL (by rw [← hverts_eq]; exact hvL_lt_verts)
    simpa [v, hverts_eq] using h1
  have hu_lt_Jn : u < inp.prep.J.n := by
    have hmem : u ∈ inp.prep.rawComps[ci]!.2 := by
      rw [hrc_bang, ← hverts_eq]; exact List.getElem_mem huL_lt_verts
    exact hcprops.2.2.2.2.2.1 u hmem
  have hv_lt_Jn : v < inp.prep.J.n := by
    have hmem : v ∈ inp.prep.rawComps[ci]!.2 := by
      rw [hrc_bang, ← hverts_eq]; exact List.getElem_mem hvL_lt_verts
    exact hcprops.2.2.2.2.2.1 v hmem
  have hJn_lt_w : inp.prep.J.n < 2 ^ w := by omega
  have hphi_lvl_lt_w : inp.prep.phiNum_dec * 2 ^ comp.level < 2 ^ w := by
    have hcb := comp_weight_bounds hvalid.2.2.1 hci
    have hcmp_lvl : comp.level = inp.prep.rawComps[ci].1 := by rw [← hcomp_eq]; exact hw_ci.2.2.1
    rw [hcmp_lvl]
    have hm1 : inp.prep.phiNum_dec * 2 ^ inp.prep.rawComps[ci].1 ≤
        4 * (inp.prep.J0_strip.m + 1) * inp.prep.phiDen_dec := by
      have h1 := hcb.1
      nlinarith only [h1, hpn, hpnd]
    omega
  have hwEnd_lt_w : wAddr + (2 + 2 * Wm) + Wm + 3 * Wm + 3 * inp.prep.J.m < 2 ^ w := hEnd_lt_w
  have hjs_def : wAddr + (2 + 2 * Wm) + Wm + 3 * Wm = jSrcAddr := rfl
  have hww_def : wAddr + (2 + 2 * Wm) = wWNumAddr := rfl
  have hws_def : wWNumAddr + Wm = wSrcAddr := rfl
  have h1_w : 1 < 2 ^ w := h1w
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have hci_w : ci < 2 ^ w := by
    have : inp.prep.rawComps.length ≤ inp.h := by
      have := h_in_lt.2.2.2.2.2.1; omega
    have : inp.h ≤ inp.maxHeapEnd ce pds := by simp [maxHeapEnd]; omega
    omega
  have heL_w : eL < 2 ^ w := by omega
  have hu_w : u < 2 ^ w := by omega
  have hv_w : v < 2 ^ w := by omega
  have hwSubPtr_w : wSubPtr < 2 ^ w := by omega
  have hcvPtr_w : inp.prep.cVertsPtr ci < 2 ^ w := by
    have : inp.h ≤ inp.maxHeapEnd ce pds := by simp [maxHeapEnd]; omega
    omega
  have hwA_w : wAddr < 2 ^ w := by omega
  have hwwn_base_w : wWNumAddr < 2 ^ w := by dsimp only [wWNumAddr]; omega
  have hwSrc_base_w : wSrcAddr < 2 ^ w := by dsimp only [wSrcAddr, wWNumAddr]; omega
  have h2eL_w : 2 * eL < 2 ^ w := by omega
  have h2p2eL_w : 2 + 2 * eL < 2 ^ w := by omega
  have h3p2eL_w : 3 + 2 * eL < 2 ^ w := by omega
  have hws2_w : wSubPtr + (2 + 2 * eL) < 2 ^ w := by omega
  have hws3_w : wSubPtr + (3 + 2 * eL) < 2 ^ w := by omega
  have huL_lt_raw : uL < inp.prep.rawComps[ci].2.length := by rw [← hverts_eq]; exact huL_lt_verts
  have hvL_lt_raw : vL < inp.prep.rawComps[ci].2.length := by rw [← hverts_eq]; exact hvL_lt_verts
  have huL_lt_w : uL < 2 ^ w := lt_trans huL_lt_verts (by rw [hverts_eq, ← hWsub_n]; omega)
  have hvL_lt_w : vL < 2 ^ w := lt_trans hvL_lt_verts (by rw [hverts_eq, ← hWsub_n]; omega)
  have hcvu_w : inp.prep.cVertsPtr ci + uL < 2 ^ w := by
    have : inp.h ≤ inp.maxHeapEnd ce pds := by simp [maxHeapEnd]; omega
    omega
  have hcvv_w : inp.prep.cVertsPtr ci + vL < 2 ^ w := by
    have : inp.h ≤ inp.maxHeapEnd ce pds := by simp [maxHeapEnd]; omega
    omega
  have hwIdx_w : wIdx < 2 ^ w := by omega
  have h2wIdx_w : 2 * wIdx < 2 ^ w := by omega
  have h2p2wIdx_w : 2 + 2 * wIdx < 2 ^ w := by omega
  have h3p2wIdx_w : 3 + 2 * wIdx < 2 ^ w := by omega
  have hwA2_w : wAddr + (2 + 2 * wIdx) < 2 ^ w := by omega
  have hwA3_w : wAddr + (3 + 2 * wIdx) < 2 ^ w := by omega
  have hwwn_w : wWNumAddr + wIdx < 2 ^ w := by dsimp only [wWNumAddr]; omega
  have h3wIdx_w : 3 * wIdx < 2 ^ w := by omega
  have hwS0_w : wSrcAddr + 3 * wIdx < 2 ^ w := by dsimp only [wSrcAddr, wWNumAddr]; omega
  have h3wIdx1_w : 3 * wIdx + 1 < 2 ^ w := by omega
  have hwS1_w : wSrcAddr + (3 * wIdx + 1) < 2 ^ w := by dsimp only [wSrcAddr, wWNumAddr]; omega
  have h3wIdx2_w : 3 * wIdx + 2 < 2 ^ w := by omega
  have hwS2_w : wSrcAddr + (3 * wIdx + 2) < 2 ^ w := by dsimp only [wSrcAddr, wWNumAddr]; omega
  have hr33' : regs 33 = comp.wStart := hr33
  have hr35' : regs 35 = inp.prep.phiNum_dec * 2 ^ comp.level := hr35
  rcases buildCompWEdgesBody_runs (ω := ω) (p := p)
      hr24 hr25 hr26 hr29 hr30 hr33' hr34 hr35' hr37 hm_uL hm_vL hm_u hm_v
      h1_w h2_w h3_w hci_w heL_w hu_w hv_w hwSubPtr_w hcvPtr_w hwA_w hwwn_base_w hwSrc_base_w
      h2eL_w h2p2eL_w h3p2eL_w hws2_w hws3_w huL_lt_w hvL_lt_w hcvu_w hcvv_w (by omega)
      hwIdx_w h2wIdx_w h2p2wIdx_w h3p2wIdx_w hwA2_w hwA3_w hwwn_w h3wIdx_w hwS0_w h3wIdx1_w hwS1_w
      h3wIdx2_w hwS2_w hphi_lvl_lt_w with
    ⟨o, st_out, c_run, hruns, ⟨rfl, rfl⟩, hcost_run⟩
  set m_prev := Function.update (Function.update (Function.update (Function.update
    (Function.update m (wAddr + (2 + 2 * wIdx)) u)
      (wAddr + (3 + 2 * wIdx)) v)
      (wWNumAddr + wIdx) (inp.prep.phiNum_dec * 2 ^ comp.level))
      (wSrcAddr + 3 * wIdx) 1)
      (wSrcAddr + (3 * wIdx + 1)) ci
  set m' := Function.update m_prev (wSrcAddr + (3 * wIdx + 2)) eL
  set regs' := Function.update (Function.update (Function.update
    (Function.update (Function.update regs 38 uL) 39 vL) 38 u) 39 v) 40 wIdx
  refine ⟨.normal, ⟨m', regs', pos⟩, c_run, hruns, ?_, hcost_run⟩
  have hm_out : ∀ x,
      x ≠ wAddr + (2 + 2 * wIdx) → x ≠ wAddr + (3 + 2 * wIdx) → x ≠ wWNumAddr + wIdx →
      x ≠ wSrcAddr + 3 * wIdx → x ≠ wSrcAddr + (3 * wIdx + 1) → x ≠ wSrcAddr + (3 * wIdx + 2) →
      m' x = m x := by
    intro x h1 h2 h3 h4 h5 h6
    dsimp only [m', m_prev]
    rw [Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4,
      Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  rcases wEdge_updates_agree wAddr Wm wIdx hm_out hwIdx_lt_Wm with
    ⟨hm_below_w, hm_jSrc, hslot_lt, hslot_gt⟩
  have hm_below_w0 : ∀ x < wAddr, m' x = m x :=
    fun x hx => hm_below_w x (Nat.lt_trans hx (Nat.lt_succ_of_lt (Nat.lt_succ_self wAddr)))
  have ha_subptr : aCompExt + 6 * ci + 1 < wAddr := by
    have hci6 : 6 * (ci + 1) ≤ 6 * inp.prep.rawComps.length := Nat.mul_le_mul_left 6 hci
    omega
  have hst_stat := asm_preserves_static hhdr0 hm12 hm13 hm14 hm15 hm16 hbelow ha_lo ha_ext hm_below_w0
  have hr_36 : ∀ r ≤ 36, Function.update regs' 37 (eL + 1) r = regs r := by
    intro r hr; dsimp only [regs']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hjSrc_ge_arr : ∀ eJ, wAddr + (2 + 2 * Wm) + Wm + 3 * Wm ≤ jSrcAddr + 3 * eJ := fun eJ => by
    rw [hjs_def]; exact Nat.le_add_right _ _
  have hjSrc_ge_arr1 : ∀ eJ, wAddr + (2 + 2 * Wm) + Wm + 3 * Wm ≤ jSrcAddr + 3 * eJ + 1 := fun eJ => by
    rw [hjs_def]; exact le_trans (Nat.le_add_right _ _) (Nat.le_succ _)
  have hjSrc_ge_arr2 : ∀ eJ, wAddr + (2 + 2 * Wm) + Wm + 3 * Wm ≤ jSrcAddr + 3 * eJ + 2 := fun eJ => by
    rw [hjs_def]; exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ 2)
  refine ⟨?_, ?_⟩
  · unfold CompWEdgesInv
    dsimp only
    refine ⟨heL, @ceBaseInv_of_agree inp ce pds mem₀ m' aCompExt wAddr ⟨m, regs, pos⟩
        hbase hr18 ha_ext hm_below_w0 (Function.update regs' 37 (eL + 1))
        (fun r hr => hr_36 r (Nat.le_trans hr (by decide))),
      (hr_36 18 (by decide)).trans hr18, (hr_36 23 (by decide)).trans hr23,
      (hr_36 24 (by decide)).trans hr24, (hr_36 25 (by decide)).trans hr25,
      (hr_36 26 (by decide)).trans hr26, (hr_36 27 (by decide)).trans hr27,
      (hr_36 28 (by decide)).trans hr28, (hr_36 29 (by decide)).trans hr29,
      (hr_36 30 (by decide)).trans hr30, (hr_36 31 (by decide)).trans hr31,
      (hr_36 32 (by decide)).trans hr32, (hr_36 33 (by decide)).trans hr33,
      by rw [hr_36 34 (by decide), hm_below_w0 _ ha_subptr]; exact hr34,
      (hr_36 35 (by decide)).trans hr35, (hr_36 36 (by decide)).trans hr36,
      by rw [Function.update_self],
      hws, ha_ext, hmax_le, compExtAt_of_agree_below hcomp_ext hm_below_w0,
      hst_stat.1, hst_stat.2.1, hst_stat.2.2.1, hst_stat.2.2.2.1, hst_stat.2.2.2.2.1,
      hst_stat.2.2.2.2.2.1, hst_stat.2.2.2.2.2.2,
      (hm_below_w wAddr (Nat.lt_succ_of_lt (Nat.lt_succ_self wAddr))).trans hm_n,
      (hm_below_w (wAddr + 1) (Nat.lt_succ_self (wAddr + 1))).trans hm_m,
      ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => (hm_jSrc x (le_trans (hjSrc_ge_arr inp.prep.J.m) hx)).trans (hzf x hx)⟩
    · intro k hk
      have hp := hprev_j0 k hk
      have hs := hslot_lt k (lt_of_lt_of_le hk (le_trans hwStart_ge_j0 (Nat.le_add_right _ _)))
      set eJk := inp.prep.j0Edges[k]!
      exact ⟨hs.1.trans hp.1, hs.2.1.trans hp.2.1, hs.2.2.1.trans hp.2.2.1,
        hs.2.2.2.1.trans hp.2.2.2.1, hs.2.2.2.2.1.trans hp.2.2.2.2.1, hs.2.2.2.2.2.trans hp.2.2.2.2.2.1,
        (hm_jSrc _ (hjSrc_ge_arr eJk)).trans hp.2.2.2.2.2.2.1,
        (hm_jSrc _ (hjSrc_ge_arr1 eJk)).trans hp.2.2.2.2.2.2.2.1,
        (hm_jSrc _ (hjSrc_ge_arr2 eJk)).trans hp.2.2.2.2.2.2.2.2⟩
    · intro j hj eL' heL'
      have hp := hprev_w j hj eL' heL'
      have hs := hslot_lt _ (lt_of_lt_of_le (Nat.add_lt_add_left heL' _)
        ((hj_end_le_wStart j hj).trans (Nat.le_add_right _ _)))
      exact ⟨hs.1.trans hp.1, hs.2.1.trans hp.2.1, hs.2.2.1.trans hp.2.2.1,
        hs.2.2.2.1.trans hp.2.2.2.1, hs.2.2.2.2.1.trans hp.2.2.2.2.1, hs.2.2.2.2.2.trans hp.2.2.2.2.2⟩
    · intro j hj jL hjL
      have hp := hprev_j j hj jL hjL
      set eJj := (wd.comps.getD j defaultCompInfo).jSubOrigEdges[jL]!
      exact ⟨(hm_jSrc _ (hjSrc_ge_arr eJj)).trans hp.1,
        (hm_jSrc _ (hjSrc_ge_arr1 eJj)).trans hp.2.1,
        (hm_jSrc _ (hjSrc_ge_arr2 eJj)).trans hp.2.2⟩
    · intro eL' heL'
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp heL') with he_lt | hel_eq
      · have hp := hcur_w eL' he_lt
        have hs := hslot_lt (comp.wStart + eL') (Nat.add_lt_add_left he_lt _)
        exact ⟨hs.1.trans hp.1, hs.2.1.trans hp.2.1, hs.2.2.1.trans hp.2.2.1,
          hs.2.2.2.1.trans hp.2.2.2.1, hs.2.2.2.2.1.trans hp.2.2.2.2.1, hs.2.2.2.2.2.trans hp.2.2.2.2.2⟩
      · subst hel_eq
        have heW_len : eL' < comp.W_sub.edges.length := heL
        have heW_eq : comp.W_sub.edges[eL']! = comp.W_sub.edges[eL'] := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem heW_len]; rfl
        have hu_eq : comp.verts[uL]! = u := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem huL_lt_verts]; rfl
        have hv_eq : comp.verts[vL]! = v := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hvL_lt_verts]; rfl
        have hc := wEdge_writes_cell m wAddr Wm wIdx u v (inp.prep.phiNum_dec * 2 ^ comp.level) ci eL' hwIdx_lt_Wm
        dsimp only at hc ⊢
        rw [heW_eq]
        change m' (wAddr + 2 + 2 * wIdx) = comp.verts[uL]! ∧ m' (wAddr + 3 + 2 * wIdx) = comp.verts[vL]! ∧
          m' (wWNumAddr + wIdx) = inp.prep.phiNum_dec * 2 ^ comp.level ∧
          m' (wSrcAddr + 3 * wIdx) = 1 ∧ m' (wSrcAddr + 3 * wIdx + 1) = ci ∧ m' (wSrcAddr + 3 * wIdx + 2) = eL'
        rw [hu_eq, hv_eq]
        exact hc
    · intro k hk hk_wm
      have hz := hzero_w k (by omega) hk_wm
      have hs := hslot_gt k (by omega) hk_wm
      exact ⟨hs.1.trans hz.1, hs.2.1.trans hz.2.1, hs.2.2.1.trans hz.2.2.1,
        fun t ht => (hs.2.2.2 t ht).trans (hz.2.2.2 t ht)⟩
    · intro eJ heJ h1 h2 t ht
      exact (hm_jSrc _ (le_trans (hjSrc_ge_arr eJ) (Nat.le_add_right _ t))).trans
        (hzero_j eJ heJ h1 h2 t ht)
  · dsimp only [regs']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hr37

theorem buildCompWEdgesLoop_triple {w : ℕ} {p : Program}
    {inp : WitnessCoreInput} {ce : ConstructExpanderImpl} {pds : PathDSParams}
    {mem₀ : ℕ → ℕ} {WSubs : List Graph} {aCompExt wAddr ci : ℕ}
    (hvalid : inp.Valid ce pds mem₀ w) (hci : ci < inp.prep.rawComps.length)
    (hws : inp.ValidWSubs ce WSubs) :
    let wd := inp.mkWitnessData ce pds WSubs
    let comp := wd.comps.getD ci defaultCompInfo
    Triple w p
      (fun st => CompWEdgesInv inp ce pds mem₀ WSubs aCompExt wAddr ci 0
        { st with regs := Function.update st.regs 37 0 })
      (forRange 37 (.const 0) (.reg 36) buildCompWEdgesBody)
      (normalPost fun st => CompJOrigInv inp ce pds mem₀ WSubs aCompExt wAddr ci 0
        { st with regs := Function.update st.regs 37 0 })
      (fun _ => asmWEdgeCost * comp.W_sub.m + 9 * comp.W_sub.m + 7) := by
  intro wd comp
  have h1w : 1 < 2 ^ w := (ce_word_bounds hvalid).1
  have h0w : 0 < 2 ^ w := lt_trans Nat.zero_lt_one h1w
  have hwm_lt : comp.W_sub.m < 2 ^ w := by
    have hclen : wd.comps.length = inp.prep.rawComps.length :=
      buildCompsFrom_length inp inp.prep.j0Edges.length inp.prep.rawComps WSubs hws.1
    have hceq : wd.comps[ci]'(by rw [hclen]; exact hci) = comp := by
      simp [comp, List.getD_eq_getElem?_getD, hclen, hci]
    have hcb := (mkWitnessData_W_m_upper (pds := pds) hvalid.2.2.1 hws).2 ci (by rw [hclen]; exact hci)
    rw [hceq] at hcb
    have hmw_le : inp.mwInt ce ≤
        2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + inp.prep.phiNum_dec := by
      unfold mwInt
      have h1 : (2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec +
          inp.prep.phiNum_dec - 1) / inp.prep.phiNum_dec ≤
          2 * ce.c_deg_int * inp.prep.J0_strip.m * inp.prep.phiDen_dec + inp.prep.phiNum_dec - 1 :=
        Nat.div_le_self _ _
      have hpn := hvalid.2.2.1.2.2.2.2.2.2.2.2.1
      omega
    have hpn := hvalid.2.2.1.2.2.2.2.2.2.2.2.1
    have hpnd := hvalid.2.2.1.2.2.2.2.2.2.2.2.2.1
    have hm_w := (ce_word_bounds hvalid).2.2
    nlinarith only [hcb, hmw_le, hpn, hpnd, hm_w]
  refine (Triple.seq_normal_const
    (R := CompWEdgesInv inp ce pds mem₀ WSubs aCompExt wAddr ci 0)
    (c₁ := (Expr.const 0).size + 1)
    (c₂ := (comp.W_sub.m - 0) * (asmWEdgeCost + (Expr.reg 36).size + 8) + ((Expr.reg 36).size + 3))
    ?_ ?_).mono_cost (fun _ _ => by dsimp only [asmWEdgeCost]; simp [Expr.size]; omega)
  · exact Triple.assign (val := fun _ => 0) (fun _ _ => ev_const h0w) fun _ hP => hP
  · refine (Triple.forUp_const asmWEdgeCost 0 comp.W_sub.m
      (Nat.zero_le _) h1w (fun _ => hwm_lt)
      (fun _ _ _ _ hP => hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ _ _ _ hP => by
        have hm := hP.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simp only [Expr.eval, hm]; rfl)
      (fun k _ hk => Triple.weaken_pre (buildCompWEdgesBody_triple hvalid hci (eL := k))
        fun _ hinv => ⟨hinv, hk⟩)).strengthen_post ?_
    intro o st hpost
    cases o with
    | normal =>
      rcases hpost with ⟨_, hbase, hr18, hr23, hr24, hr25, hr26, hr27, hr28, hr29,
        _, hr31, hr32, _, _, _, _, _,
        hws, ha_ext, hmax_le, hcomp_ext, hbelow, hhdr0, hm12, hm13, hm14, hm15, hm16,
        hm_n, hm_m, hprev_j0, hprev_w, hprev_j, hcur_w, hzero_w, hzero_j, hzf⟩
      unfold CompJOrigInv
      dsimp only
      refine ⟨Nat.zero_le _, @ceBaseInv_of_agree inp ce pds mem₀ st.mem aCompExt wAddr st
          hbase hr18 ha_ext (fun _ _ => rfl) (Function.update st.regs 37 0)
          (fun r hr => by rw [Function.update_of_ne (by omega)]),
        by rw [Function.update_of_ne (by omega)]; exact hr18,
        by rw [Function.update_of_ne (by omega)]; exact hr23,
        by rw [Function.update_of_ne (by omega)]; exact hr24,
        by rw [Function.update_of_ne (by omega)]; exact hr25,
        by rw [Function.update_of_ne (by omega)]; exact hr26,
        by rw [Function.update_of_ne (by omega)]; exact hr27,
        by rw [Function.update_of_ne (by omega)]; exact hr28,
        by rw [Function.update_of_ne (by omega)]; exact hr29,
        by rw [Function.update_of_ne (by omega)]; exact hr31,
        by rw [Function.update_of_ne (by omega)]; exact hr32,
        by rw [Function.update_self],
        hws, ha_ext, hmax_le, hcomp_ext, hbelow, hhdr0, hm12, hm13, hm14, hm15, hm16, hm_n, hm_m,
        hprev_j0, ?_, hprev_j, fun _ hjL => (Nat.not_lt_zero _ hjL).elim, hzero_w,
        fun eJ heJ h1 h2 _ => hzero_j eJ heJ h1 h2, hzf⟩
      intro j hj eL' heL'
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj_lt | rfl
      · exact hprev_w j hj_lt eL' heL'
      · exact hcur_w eL' heL'
    | returned _ => exact False.elim hpost

end MinCostFlow.Spanner