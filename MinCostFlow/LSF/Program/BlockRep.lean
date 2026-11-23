module

public import MinCostFlow.LSF.Program.Layout
public import MinCostFlow.Num.Representation

/-!
# Sub-Block Memory Representations and Frame Lemmas for LSF

Defines `TBlockAt`, `FAncAt`, `WBlockAt`, `WstrAt`, and `AuxAt`, together with locality /
memory-agreement frame lemmas (`.of_agree`) showing each predicate depends solely on the
memory cells inside its allocated sub-block interval.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

/-- `T` block at `tPtr` representing `S.T_cur` with dense edge IDs `0..tM-1` in `tOrigList`,
stored edge order `π`, endpoint-match self-loop trackers `2 * i + p` inside `dgTPtr`, and
frozen endpoints when trackers are absent. -/
def TBlockAt (mem : ℕ → ℕ) (tPtr vCap eCap tM : ℕ) (G T_cur T₀ : MGraph)
    (π : ℕ → ℕ) (tOrigList : List ℕ) : Prop :=
  mem (tPtr + tOffM) = tM ∧
  mem (tPtr + tOffDgTPtr) = tDgTPtr tPtr ∧
  mem (tPtr + tOffOrigIdPtr) = tOrigIdBase tPtr vCap tM ∧
  mem (tPtr + tOffPiPtr) = tPiBase tPtr vCap tM ∧
  mem (tPtr + tOffFrozenTailPtr) = tFrozenTailBase tPtr vCap tM ∧
  mem (tPtr + tOffFrozenHeadPtr) = tFrozenHeadBase tPtr vCap tM ∧
  mem (tPtr + tOffIdxOfEdgePtr) = tIdxOfEdgeBase tPtr vCap tM ∧
  mem (tPtr + tOffSplitScratchPtr) = tSplitScratchBase tPtr vCap eCap tM ∧
  tOrigList.length = tM ∧ tOrigList.Nodup ∧ (∀ f, f ∈ tOrigList ↔ f ∈ T₀.E) ∧
  ListAt mem (tOrigIdBase tPtr vCap tM) tOrigList ∧
  ListAt mem (tPiBase tPtr vCap tM) (tOrigList.map π) ∧
  (∀ i (hi : i < tOrigList.length), tOrigList[i] < eCap →
    mem (tIdxOfEdgeBase tPtr vCap tM + tOrigList[i]) = i + 1) ∧
  (∀ e < eCap, mem (tIdxOfEdgeBase tPtr vCap tM + e) ≠ 0 →
    ∃ i, ∃ (hi : i < tOrigList.length),
      tOrigList[i] = e ∧ mem (tIdxOfEdgeBase tPtr vCap tM + e) = i + 1) ∧
  ∃ dgT : MGraph,
    DynGraphAt mem (tDgTPtr tPtr) vCap (2 * tM + 1) dgT ∧
    dgT.V = G.V ∧
    (∀ e ∈ dgT.E, e < 2 * tM) ∧
    ∀ i (hi : i < tOrigList.length),
      let f := tOrigList[i]
      (2 * i ∈ dgT.E ↔ f ∈ G.E ∧ G.tail f = T_cur.tail f) ∧
      (2 * i ∈ dgT.E → dgT.tail (2 * i) = T_cur.tail f ∧ dgT.head (2 * i) = T_cur.tail f) ∧
      (2 * i ∉ dgT.E → mem (tFrozenTailBase tPtr vCap tM + i) = T_cur.tail f) ∧
      (2 * i + 1 ∈ dgT.E ↔ f ∈ G.E ∧ G.head f = T_cur.head f) ∧
      (2 * i + 1 ∈ dgT.E →
        dgT.tail (2 * i + 1) = T_cur.head f ∧ dgT.head (2 * i + 1) = T_cur.head f) ∧
      (2 * i + 1 ∉ dgT.E → mem (tFrozenHeadBase tPtr vCap tM + i) = T_cur.head f)

lemma TBlockAt.of_agree {mem mem' : ℕ → ℕ} {tPtr vCap eCap tM : ℕ}
    {G T_cur T₀ : MGraph} {π : ℕ → ℕ} {tOrigList : List ℕ}
    (h : TBlockAt mem tPtr vCap eCap tM G T_cur T₀ π tOrigList)
    (hagree : ∀ a, tPtr ≤ a → a < tPtr + tBlockSize vCap eCap tM → mem' a = mem a) :
    TBlockAt mem' tPtr vCap eCap tM G T_cur T₀ π tOrigList := by
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hlen, hnd, hmemL, hLO, hLPi, hidx1, hidx2,
    dgT, hdgT, hdgTV, hdgTE, htrack⟩
  have hhd : ∀ off, off < tHdrSize → mem' (tPtr + off) = mem (tPtr + off) :=
    fun off hoff => hagree (tPtr + off) (Nat.le_add_right _ _) (by dsimp [tBlockSize]; omega)
  refine ⟨(hhd _ (by decide)).trans h0, (hhd _ (by decide)).trans h1,
    (hhd _ (by decide)).trans h2, (hhd _ (by decide)).trans h3,
    (hhd _ (by decide)).trans h4, (hhd _ (by decide)).trans h5,
    (hhd _ (by decide)).trans h6, (hhd _ (by decide)).trans h7,
    hlen, hnd, hmemL, ?_, ?_, ?_, ?_, dgT, ?_, hdgTV, hdgTE, ?_⟩
  · intro i hi
    have hi' : i < tM := by omega
    have := hagree (tOrigIdBase tPtr vCap tM + i)
      (by dsimp [tOrigIdBase, tDgTPtr]; omega)
      (by dsimp [tOrigIdBase, tDgTPtr, tBlockSize]; omega)
    exact this.trans (hLO i hi)
  · intro i hi
    have hi' : i < tM := by simp only [List.length_map] at hi; omega
    have := hagree (tPiBase tPtr vCap tM + i)
      (by dsimp [tPiBase, tOrigIdBase, tDgTPtr]; omega)
      (by dsimp [tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega)
    exact this.trans (hLPi i hi)
  · intro i hi hlt
    have hi' : i < tM := by omega
    have := hagree (tIdxOfEdgeBase tPtr vCap tM + tOrigList[i])
      (by dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr]; omega)
      (by dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr,
          tBlockSize]; omega)
    exact this.trans (hidx1 i hi hlt)
  · intro e he hne
    have hme : mem' (tIdxOfEdgeBase tPtr vCap tM + e) = mem (tIdxOfEdgeBase tPtr vCap tM + e) :=
      hagree (tIdxOfEdgeBase tPtr vCap tM + e)
        (by dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr]; omega)
        (by dsimp [tIdxOfEdgeBase, tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr,
            tBlockSize]; omega)
    rw [hme] at hne ⊢
    exact hidx2 e he hne
  · refine hdgT.of_agree fun a ha1 ha2 => hagree a ?_ ?_
    · dsimp [tDgTPtr] at ha1; omega
    · dsimp [tDgTPtr, tBlockSize] at ha2 ⊢; omega
  · intro i hi
    have hi' : i < tM := by omega
    have ⟨a, b, c, d, e, f⟩ := htrack i hi
    have hft : mem' (tFrozenTailBase tPtr vCap tM + i) = mem (tFrozenTailBase tPtr vCap tM + i) :=
      hagree _
        (by dsimp [tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr]; omega)
        (by dsimp [tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega)
    have hfh : mem' (tFrozenHeadBase tPtr vCap tM + i) = mem (tFrozenHeadBase tPtr vCap tM + i) :=
      hagree _
        (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr]; omega)
        (by dsimp [tFrozenHeadBase, tFrozenTailBase, tPiBase, tOrigIdBase, tDgTPtr, tBlockSize]; omega)
    exact ⟨a, b, fun h2 => hft.trans (c h2), d, e, fun h2 => hfh.trans (f h2)⟩

/-- `F` ancestor and component metadata block at `fAncPtr`. -/
def FAncAt (mem : ℕ → ℕ) (fAncPtr vCap : ℕ) (RF : RootedForest)
    (rList : List ℕ) (compId compRoot compSize : ℕ → ℕ) (activeCids : Finset ℕ) : Prop :=
  open Classical in
  mem (fAncPtr + fOffRCount) = RF.R.card ∧
  mem (fAncPtr + fOffIsRootPtr) = fIsRootBase fAncPtr ∧
  mem (fAncPtr + fOffRListPtr) = fRListBase fAncPtr vCap ∧
  mem (fAncPtr + fOffCompIdPtr) = fCompIdBase fAncPtr vCap ∧
  mem (fAncPtr + fOffCompRootPtr) = fCompRootBase fAncPtr vCap ∧
  mem (fAncPtr + fOffCompSizePtr) = fCompSizeBase fAncPtr vCap ∧
  (∀ v ∈ RF.F.V, v < vCap) ∧
  rList.length = RF.R.card ∧ rList.Nodup ∧ (∀ r, r ∈ rList ↔ r ∈ RF.R) ∧
  rList.length ≤ vCap ∧
  ListAt mem (fRListBase fAncPtr vCap) rList ∧
  (∀ v < vCap, mem (fIsRootBase fAncPtr + v) = if v ∈ RF.R then 1 else 0) ∧
  activeCids ⊆ RF.R ∧
  (∀ c ∈ activeCids, c < vCap ∧
    mem (fCompRootBase fAncPtr vCap + c) = compRoot c ∧
    compRoot c ∈ RF.R ∧
    compId (compRoot c) = c ∧
    mem (fCompSizeBase fAncPtr vCap + c) = compSize c ∧
    1 ≤ compSize c ∧
    compSize c = (RF.F.V.filter (fun u => RF.F.Connected u (compRoot c))).card) ∧
  (∀ v ∈ RF.F.V,
    let c := mem (fCompIdBase fAncPtr vCap + v)
    c = compId v ∧ c ∈ activeCids ∧ RF.F.Connected v (compRoot c))

lemma FAncAt.of_agree {mem mem' : ℕ → ℕ} {fAncPtr vCap : ℕ} {RF : RootedForest}
    {rList : List ℕ} {compId compRoot compSize : ℕ → ℕ} {activeCids : Finset ℕ}
    (h : FAncAt mem fAncPtr vCap RF rList compId compRoot compSize activeCids)
    (hagree : ∀ a, fAncPtr ≤ a → a < fAncPtr + fAncSize vCap → mem' a = mem a) :
    FAncAt mem' fAncPtr vCap RF rList compId compRoot compSize activeCids := by
  classical
  dsimp only [FAncAt] at h ⊢
  rcases h with ⟨h0, h1, h2, h3, h4, h5, hvlt, hrlen, hrnd, hrmem, hrle, hrL, hroot, hact, hcid, hvF⟩
  have hhd : ∀ off, off < fAncHdrSize → mem' (fAncPtr + off) = mem (fAncPtr + off) :=
    fun off hoff => hagree (fAncPtr + off) (Nat.le_add_right _ _) (by dsimp [fAncSize]; omega)
  refine ⟨(hhd _ (by decide)).trans h0, (hhd _ (by decide)).trans h1,
    (hhd _ (by decide)).trans h2, (hhd _ (by decide)).trans h3,
    (hhd _ (by decide)).trans h4, (hhd _ (by decide)).trans h5,
    hvlt, hrlen, hrnd, hrmem, hrle, ?_, ?_, hact, ?_, ?_⟩
  · intro i hi
    have := hagree (fRListBase fAncPtr vCap + i)
      (by dsimp [fRListBase, fIsRootBase]; omega)
      (by dsimp [fRListBase, fIsRootBase, fAncSize]; omega)
    exact this.trans (hrL i hi)
  · intro v hv
    have := hagree (fIsRootBase fAncPtr + v)
      (by dsimp [fIsRootBase]; omega)
      (by dsimp [fIsRootBase, fAncSize]; omega)
    exact this.trans (hroot v hv)
  · intro c hc
    obtain ⟨hlt, hcr, hcrR, hcid_eq, hcs, hcs1, hcard⟩ := hcid c hc
    have hm1 : mem' (fCompRootBase fAncPtr vCap + c) = mem (fCompRootBase fAncPtr vCap + c) :=
      hagree _
        (by dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)
        (by dsimp [fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncSize]; omega)
    have hm2 : mem' (fCompSizeBase fAncPtr vCap + c) = mem (fCompSizeBase fAncPtr vCap + c) :=
      hagree _
        (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase]; omega)
        (by dsimp [fCompSizeBase, fCompRootBase, fCompIdBase, fRListBase, fIsRootBase, fAncSize]; omega)
    exact ⟨hlt, hm1.trans hcr, hcrR, hcid_eq, hm2.trans hcs, hcs1, hcard⟩
  · intro v hv
    have hmv : mem' (fCompIdBase fAncPtr vCap + v) = mem (fCompIdBase fAncPtr vCap + v) :=
      hagree _
        (by dsimp [fCompIdBase, fRListBase, fIsRootBase]; omega)
        (by dsimp [fCompIdBase, fRListBase, fIsRootBase, fAncSize]; have := hvlt v hv; omega)
    simpa only [hmv] using hvF v hv

/-- `W` decomposition CSR block at `wPtr`. -/
def WBlockAt (mem : ℕ → ℕ) (wPtr n0 : ℕ) (W_init : Finset (Finset ℕ)) (F₀ : MGraph) : Prop :=
  let np := mem (wPtr + wOffNumPieces)
  let tv := mem (wPtr + wOffTotalVerts)
  let te := mem (wPtr + wOffTotalEdges)
  mem (wPtr + wOffVertOffPtr) = wVertOffBase wPtr ∧
  mem (wPtr + wOffVertsPtr) = wVertsBase wPtr n0 ∧
  mem (wPtr + wOffEdgeOffPtr) = wEdgeOffBase wPtr n0 ∧
  mem (wPtr + wOffEdgesPtr) = wEdgesBase wPtr n0 ∧
  np ≤ n0 ∧ tv ≤ 2 * n0 ∧ te ≤ n0 ∧
  mem (wVertOffBase wPtr + 0) = 0 ∧ mem (wVertOffBase wPtr + np) = tv ∧
  mem (wEdgeOffBase wPtr n0 + 0) = 0 ∧ mem (wEdgeOffBase wPtr n0 + np) = te ∧
  ∃ wList : List (Finset ℕ), wList.length = np ∧ wList.Nodup ∧ (∀ W, W ∈ wList ↔ W ∈ W_init) ∧
    ∀ i (hi : i < wList.length),
      let vs := mem (wVertOffBase wPtr + i)
      let ve := mem (wVertOffBase wPtr + (i + 1))
      let es := mem (wEdgeOffBase wPtr n0 + i)
      let ee := mem (wEdgeOffBase wPtr n0 + (i + 1))
      vs ≤ ve ∧ ve ≤ tv ∧ es ≤ ee ∧ ee ≤ te ∧
      ∃ vL : List ℕ, vL.length = ve - vs ∧ vL.Nodup ∧ (∀ x, x ∈ vL ↔ x ∈ wList[i]) ∧
        ListAt mem (wVertsBase wPtr n0 + vs) vL ∧
      ∃ eL : List ℕ, eL.length = ee - es ∧ eL.Nodup ∧
        (∀ e, e ∈ eL ↔ e ∈ inducedEdges F₀ wList[i]) ∧
        ListAt mem (wEdgesBase wPtr n0 + es) eL

lemma WBlockAt.of_agree {mem mem' : ℕ → ℕ} {wPtr n0 : ℕ}
    {W_init : Finset (Finset ℕ)} {F₀ : MGraph}
    (h : WBlockAt mem wPtr n0 W_init F₀)
    (hagree : ∀ a, wPtr ≤ a → a < wPtr + wBlockSize n0 → mem' a = mem a) :
    WBlockAt mem' wPtr n0 W_init F₀ := by
  have hhd : ∀ off, off < wHdrSize → mem' (wPtr + off) = mem (wPtr + off) :=
    fun off hoff => hagree (wPtr + off) (Nat.le_add_right _ _) (by dsimp [wBlockSize]; omega)
  have hnp : mem' (wPtr + wOffNumPieces) = mem (wPtr + wOffNumPieces) :=
    hhd wOffNumPieces (by decide)
  have htv : mem' (wPtr + wOffTotalVerts) = mem (wPtr + wOffTotalVerts) :=
    hhd wOffTotalVerts (by decide)
  have hte : mem' (wPtr + wOffTotalEdges) = mem (wPtr + wOffTotalEdges) :=
    hhd wOffTotalEdges (by decide)
  dsimp only [WBlockAt] at h ⊢
  rw [hnp, htv, hte]
  rcases h with ⟨h1, h2, h3, h4, hnp_le, htv_le, hte_le, hvo0, hvoN, heo0, heoN,
    wList, hwlen, hwnd, hwmem, hpieces⟩
  have hvo : ∀ j ≤ mem (wPtr + wOffNumPieces),
      mem' (wVertOffBase wPtr + j) = mem (wVertOffBase wPtr + j) := fun j hj =>
    hagree _ (by dsimp [wVertOffBase]; omega) (by dsimp [wVertOffBase, wBlockSize]; omega)
  have heo : ∀ j ≤ mem (wPtr + wOffNumPieces),
      mem' (wEdgeOffBase wPtr n0 + j) = mem (wEdgeOffBase wPtr n0 + j) := fun j hj =>
    hagree _ (by dsimp [wEdgeOffBase, wVertsBase, wVertOffBase]; omega)
      (by dsimp [wEdgeOffBase, wVertsBase, wVertOffBase, wBlockSize]; omega)
  refine ⟨(hhd _ (by decide)).trans h1, (hhd _ (by decide)).trans h2,
      (hhd _ (by decide)).trans h3, (hhd _ (by decide)).trans h4,
      hnp_le, htv_le, hte_le,
      (hvo 0 (Nat.zero_le _)).trans hvo0, (hvo _ le_rfl).trans hvoN,
      (heo 0 (Nat.zero_le _)).trans heo0, (heo _ le_rfl).trans heoN,
      wList, hwlen, hwnd, hwmem, ?_⟩
  intro i hi
  have hi_np : i < mem (wPtr + wOffNumPieces) := hwlen ▸ hi
  rw [hvo i (by omega), hvo (i + 1) (by omega), heo i (by omega), heo (i + 1) (by omega)]
  rcases hpieces i hi with ⟨h1', h2', h3', h4', vL, hvlen, hvnd, hvmem, hvLA,
    eL, helen, hend, hemem, heLA⟩
  refine ⟨h1', h2', h3', h4', vL, hvlen, hvnd, hvmem, ?_, eL, helen, hend, hemem, ?_⟩
  · intro j hj
    have hj_lt : mem (wVertOffBase wPtr + i) + j < 2 * n0 := by
      have : j < mem (wVertOffBase wPtr + (i + 1)) - mem (wVertOffBase wPtr + i) := hvlen ▸ hj
      omega
    have hl1 : wPtr ≤ wVertsBase wPtr n0 := by dsimp [wVertsBase, wVertOffBase]; omega
    have hl2 : wVertsBase wPtr n0 + 2 * n0 ≤ wPtr + wBlockSize n0 := by
      dsimp [wVertsBase, wVertOffBase, wBlockSize]; omega
    have := hagree (wVertsBase wPtr n0 + mem (wVertOffBase wPtr + i) + j)
      (by omega) (by omega)
    simpa only [Nat.add_assoc] using this.trans (hvLA j hj)
  · intro j hj
    have hj_lt : mem (wEdgeOffBase wPtr n0 + i) + j < n0 := by
      have : j < mem (wEdgeOffBase wPtr n0 + (i + 1)) - mem (wEdgeOffBase wPtr n0 + i) := helen ▸ hj
      omega
    have hl1 : wPtr ≤ wEdgesBase wPtr n0 := by
      dsimp [wEdgesBase, wEdgeOffBase, wVertsBase, wVertOffBase]; omega
    have hl2 : wEdgesBase wPtr n0 + n0 ≤ wPtr + wBlockSize n0 := by
      dsimp [wEdgesBase, wEdgeOffBase, wVertsBase, wVertOffBase, wBlockSize]; omega
    have := hagree (wEdgesBase wPtr n0 + mem (wEdgeOffBase wPtr n0 + i) + j)
      (by omega) (by omega)
    simpa only [Nat.add_assoc] using this.trans (heLA j hj)

/-- Exact rational stretch arrays `(wstrNum, wstrDen)` for `e ∈ G.E`. -/
def WstrAt (mem : ℕ → ℕ) (wstrNumPtr wstrDenPtr eCap h L_w : ℕ)
    (G : MGraph) (wstr : ℕ → ℝ) : Prop :=
  2 ≤ h * L_w ∧ 1 ≤ L_w ∧
  ∀ e ∈ G.E, e < eCap ∧
    Num.Valid mem (wstrNumPtr + e * L_w) h L_w ∧
    Num.Valid mem (wstrDenPtr + e * L_w) h L_w ∧
    1 ≤ Num.intVal mem (wstrNumPtr + e * L_w) h L_w ∧
    1 ≤ Num.intVal mem (wstrDenPtr + e * L_w) h L_w ∧
    (Num.intVal mem (wstrNumPtr + e * L_w) h L_w : ℝ) /
      (Num.intVal mem (wstrDenPtr + e * L_w) h L_w : ℝ) = wstr e

lemma WstrAt.of_agree {mem mem' : ℕ → ℕ} {wstrNumPtr wstrDenPtr eCap h L_w : ℕ}
    {G : MGraph} {wstr : ℕ → ℝ}
    (hw : WstrAt mem wstrNumPtr wstrDenPtr eCap h L_w G wstr)
    (hN : ∀ a, wstrNumPtr ≤ a → a < wstrNumPtr + eCap * L_w → mem' a = mem a)
    (hD : ∀ a, wstrDenPtr ≤ a → a < wstrDenPtr + eCap * L_w → mem' a = mem a) :
    WstrAt mem' wstrNumPtr wstrDenPtr eCap h L_w G wstr := by
  rcases hw with ⟨hhL, hL, hE⟩
  refine ⟨hhL, hL, fun e he => ?_⟩
  rcases hE e he with ⟨hlt, hVN, hVD, hIN, hID, hval⟩
  have heN : ∀ i < L_w, mem' (wstrNumPtr + e * L_w + i) = mem (wstrNumPtr + e * L_w + i) :=
    fun i hi => hN _ (by omega) (by
      have : e * L_w + i < eCap * L_w := by
        calc e * L_w + i < (e + 1) * L_w := by nlinarith
          _ ≤ eCap * L_w := Nat.mul_le_mul_right _ hlt
      omega)
  have heD : ∀ i < L_w, mem' (wstrDenPtr + e * L_w + i) = mem (wstrDenPtr + e * L_w + i) :=
    fun i hi => hD _ (by omega) (by
      have : e * L_w + i < eCap * L_w := by
        calc e * L_w + i < (e + 1) * L_w := by nlinarith
          _ ≤ eCap * L_w := Nat.mul_le_mul_right _ hlt
      omega)
  have hVN' : Num.Valid mem' (wstrNumPtr + e * L_w) h L_w := fun i hi => by
    rw [heN i hi]; exact hVN i hi
  have hVD' : Num.Valid mem' (wstrDenPtr + e * L_w) h L_w := fun i hi => by
    rw [heD i hi]; exact hVD i hi
  have hiN : Num.intVal mem' (wstrNumPtr + e * L_w) h L_w =
      Num.intVal mem (wstrNumPtr + e * L_w) h L_w := Num.intVal_congr heN
  have hiD : Num.intVal mem' (wstrDenPtr + e * L_w) h L_w =
      Num.intVal mem (wstrDenPtr + e * L_w) h L_w := Num.intVal_congr heD
  rw [hiN, hiD]
  exact ⟨hlt, hVN', hVD', hIN, hID, hval⟩

/-- Specification of static `T₀` ancestor / binary lifting / HLD `T_H` metadata and scratch in
`auxPtr`. -/
def AuxAt (mem : ℕ → ℕ) (auxPtr vCap n0 tM : ℕ) (S : LSFState) (tOrigList vList : List ℕ)
    (t0Parent t0ParentTreeIdx t0Depth thParent : ℕ → ℕ)
    (upV upMinIdx : ℕ → ℕ → ℕ) : Prop :=
  let logCap := auxLogCap n0
  mem (auxPtr + auxOffVIdxPtr) = auxVIdxBase auxPtr ∧
  mem (auxPtr + auxOffVListPtr) = auxVListBase auxPtr vCap ∧
  mem (auxPtr + auxOffT0ParentPtr) = auxT0ParentBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffT0ParentTreeIdxPtr) = auxT0ParentTreeIdxBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffT0DepthPtr) = auxT0DepthBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffLogCap) = logCap ∧
  mem (auxPtr + auxOffUpVPtr) = auxUpVBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffUpMinIdxPtr) = auxUpMinIdxBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffThParentPtr) = auxThParentBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffOrigVertPtr) = auxOrigVertBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffIsOrigVertPtr) = auxIsOrigVertBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffQBufAPtr) = auxQBufABase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffQBufBPtr) = auxQBufBBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffVisAPtr) = auxVisABase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffVisBPtr) = auxVisBBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffThStackPtr) = auxThStackBase auxPtr vCap n0 ∧
  mem (auxPtr + auxOffFSplitScratchPtr) = auxFSplitScratchBase auxPtr vCap n0 ∧
  vList.length = n0 ∧ vList.Nodup ∧ (∀ v, v ∈ vList ↔ v ∈ S.T₀.V) ∧
  tOrigList.length = tM ∧
  ListAt mem (auxVListBase auxPtr vCap) vList ∧
  (∀ i (hi : i < vList.length), mem (auxVIdxBase auxPtr + vList[i]) = i + 1) ∧
  (∀ v < vCap, v ∉ S.T₀.V → mem (auxVIdxBase auxPtr + v) = 0) ∧
  mem (auxPtr + auxOffR0Idx) < n0 ∧ vList[mem (auxPtr + auxOffR0Idx)]? = some S.r₀ ∧
  (∀ i < n0, mem (auxT0ParentBase auxPtr vCap n0 + i) = t0Parent i ∧ t0Parent i < n0) ∧
  (∀ i < n0, mem (auxT0ParentTreeIdxBase auxPtr vCap n0 + i) = t0ParentTreeIdx i ∧
    (0 < tM → t0ParentTreeIdx i < tM)) ∧
  (∀ i < n0, mem (auxT0DepthBase auxPtr vCap n0 + i) = t0Depth i) ∧
  (∀ i < n0, ∀ j < logCap,
    mem (auxUpVBase auxPtr vCap n0 + (i * logCap + j)) = upV i j ∧ upV i j < n0 ∧
    mem (auxUpMinIdxBase auxPtr vCap n0 + (i * logCap + j)) = upMinIdx i j ∧
    (0 < tM → upMinIdx i j < tM)) ∧
  (∀ i < n0, mem (auxThParentBase auxPtr vCap n0 + i) = thParent i ∧ thParent i < n0) ∧
  thParent (mem (auxPtr + auxOffR0Idx)) = mem (auxPtr + auxOffR0Idx) ∧
  t0Depth (mem (auxPtr + auxOffR0Idx)) = 0 ∧
  (∀ i (hi : i < vList.length), i ≠ mem (auxPtr + auxOffR0Idx) →
    let u := vList[i]
    let p := vList[t0Parent i]!
    t0Depth i = t0Depth (t0Parent i) + 1 ∧
    t0ParentTreeIdx i < tOrigList.length ∧
    let f := tOrigList[t0ParentTreeIdx i]!
    f ∈ S.T₀.E ∧ ((S.T₀.tail f = u ∧ S.T₀.head f = p) ∨ (S.T₀.tail f = p ∧ S.T₀.head f = u))) ∧
  (∀ i < n0, ∀ j < logCap,
    (j = 0 → upV i 0 = t0Parent i ∧ upMinIdx i 0 = t0ParentTreeIdx i) ∧
    (j + 1 < logCap → upV i (j + 1) = upV (upV i j) j) ∧
    (let u := vList[i]!
     let w := vList[upV i j]!
     u ≠ w →
       upMinIdx i j < tOrigList.length ∧
       tOrigList[upMinIdx i j]! ∈ walkEdges (S.T₀.forestPath u w) ∧
       ∀ e ∈ walkEdges (S.T₀.forestPath u w), S.π (tOrigList[upMinIdx i j]!) ≤ S.π e)) ∧
  (∀ i (hi : i < vList.length), i ≠ mem (auxPtr + auxOffR0Idx) →
    let u := vList[i]
    let p := vList[thParent i]!
    (S.TH.forestPath u S.r₀).length = (S.TH.forestPath p S.r₀).length + 1 ∧
    ∃ e ∈ S.TH.E, (S.TH.tail e = u ∧ S.TH.head e = p) ∨ (S.TH.tail e = p ∧ S.TH.head e = u)) ∧
  (∀ v < vCap, mem (auxIsOrigVertBase auxPtr vCap n0 + v) = if v ∈ S.T₀.V then 1 else 0) ∧
  (∀ w ∈ S.G.V, w < vCap → mem (auxOrigVertBase auxPtr vCap n0 + w) = S.origVert w) ∧
  (∀ v < vCap, mem (auxVisABase auxPtr vCap n0 + v) = 0 ∧ mem (auxVisBBase auxPtr vCap n0 + v) = 0)

lemma AuxAt.of_agree {mem mem' : ℕ → ℕ} {auxPtr vCap n0 tM : ℕ} {S : LSFState}
    {tOrigList vList : List ℕ} {t0Parent t0ParentTreeIdx t0Depth thParent : ℕ → ℕ}
    {upV upMinIdx : ℕ → ℕ → ℕ}
    (h : AuxAt mem auxPtr vCap n0 tM S tOrigList vList
      t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx)
    (hagree : ∀ a, auxPtr ≤ a → a < auxPtr + auxSize vCap n0 → mem' a = mem a)
    (hvlt : ∀ v ∈ S.T₀.V, v < vCap) :
    AuxAt mem' auxPtr vCap n0 tM S tOrigList vList
      t0Parent t0ParentTreeIdx t0Depth thParent upV upMinIdx := by
  have hhd : ∀ off, off < auxHdrSize → mem' (auxPtr + off) = mem (auxPtr + off) :=
    fun off hoff => hagree (auxPtr + off) (Nat.le_add_right _ _)
      (by dsimp [auxSize]; omega)
  dsimp only [AuxAt] at h ⊢
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    hvlen, hvnd, hvmem, htlen, hvLA, hvIdx, hvIdx0, hr0lt, hr0v, hp, hpe, hd, hup, hth, hthR0,
    hdR0, ht0Edge, hUpProp, hThProp, hIsOrig, hOrig, hVis⟩
  have hr0eq : mem' (auxPtr + auxOffR0Idx) = mem (auxPtr + auxOffR0Idx) :=
    hhd auxOffR0Idx (by decide)
  rw [hr0eq]
  refine ⟨(hhd _ (by decide)).trans h0, (hhd _ (by decide)).trans h1, (hhd _ (by decide)).trans h2,
    (hhd _ (by decide)).trans h3, (hhd _ (by decide)).trans h4, (hhd _ (by decide)).trans h5,
    (hhd _ (by decide)).trans h6, (hhd _ (by decide)).trans h7, (hhd _ (by decide)).trans h8,
    (hhd _ (by decide)).trans h9, (hhd _ (by decide)).trans h10, (hhd _ (by decide)).trans h11,
    (hhd _ (by decide)).trans h12, (hhd _ (by decide)).trans h13, (hhd _ (by decide)).trans h14,
    (hhd _ (by decide)).trans h15, (hhd _ (by decide)).trans h16,
    hvlen, hvnd, hvmem, htlen, ?_, ?_, ?_, hr0lt, hr0v, ?_, ?_, ?_, ?_, ?_, hthR0,
    hdR0, ht0Edge, hUpProp, hThProp, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < n0 := by omega
    have := hagree (auxVListBase auxPtr vCap + i)
      (by dsimp [auxVListBase, auxVIdxBase]; omega)
      (by dsimp [auxVListBase, auxVIdxBase, auxSize]; omega)
    exact this.trans (hvLA i hi)
  · intro i hi
    have hi' : i < n0 := by omega
    have hvmemT : vList[i] ∈ S.T₀.V := (hvmem _).mp (List.getElem_mem _)
    have hlt := hvlt _ hvmemT
    have := hagree (auxVIdxBase auxPtr + vList[i])
      (by dsimp [auxVIdxBase]; omega)
      (by dsimp [auxVIdxBase, auxSize]; omega)
    exact this.trans (hvIdx i hi)
  · intro v hv hvnot
    have := hagree (auxVIdxBase auxPtr + v)
      (by dsimp [auxVIdxBase]; omega)
      (by dsimp [auxVIdxBase, auxSize]; omega)
    exact this.trans (hvIdx0 v hv hvnot)
  · intro i hi
    have := hagree (auxT0ParentBase auxPtr vCap n0 + i)
      (by dsimp [auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)
      (by dsimp [auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]; omega)
    rw [this]; exact hp i hi
  · intro i hi
    have := hagree (auxT0ParentTreeIdxBase auxPtr vCap n0 + i)
      (by dsimp [auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)
      (by dsimp [auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]; omega)
    rw [this]; exact hpe i hi
  · intro i hi
    have := hagree (auxT0DepthBase auxPtr vCap n0 + i)
      (by dsimp [auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega)
      (by dsimp [auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]; omega)
    exact this.trans (hd i hi)
  · intro i hi j hj
    have hlt_ij : i * auxLogCap n0 + j < n0 * auxLogCap n0 := by
      calc i * auxLogCap n0 + j < i * auxLogCap n0 + auxLogCap n0 := Nat.add_lt_add_left hj _
        _ = (i + 1) * auxLogCap n0 := by ring
        _ ≤ n0 * auxLogCap n0 := Nat.mul_le_mul_right _ hi
    have hb1 : auxPtr ≤ auxUpVBase auxPtr vCap n0 := by
      dsimp [auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
        auxVListBase, auxVIdxBase]; omega
    have he1 : auxUpVBase auxPtr vCap n0 + n0 * auxLogCap n0 ≤ auxPtr + auxSize vCap n0 := by
      dsimp [auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
        auxVListBase, auxVIdxBase, auxSize]; omega
    have hb2 : auxPtr ≤ auxUpMinIdxBase auxPtr vCap n0 := by
      dsimp [auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
        auxVListBase, auxVIdxBase]; omega
    have he2 : auxUpMinIdxBase auxPtr vCap n0 + n0 * auxLogCap n0 ≤ auxPtr + auxSize vCap n0 := by
      dsimp [auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
        auxVListBase, auxVIdxBase, auxSize]; omega
    have hm1 := hagree (auxUpVBase auxPtr vCap n0 + (i * auxLogCap n0 + j))
      (by omega) (by omega)
    have hm2 := hagree (auxUpMinIdxBase auxPtr vCap n0 + (i * auxLogCap n0 + j))
      (by omega) (by omega)
    rw [hm1, hm2]; exact hup i hi j hj
  · intro i hi
    have hb : auxPtr ≤ auxThParentBase auxPtr vCap n0 := by
      dsimp [auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
        auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega
    have he : auxThParentBase auxPtr vCap n0 + n0 ≤ auxPtr + auxSize vCap n0 := by
      dsimp [auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
        auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]; omega
    have := hagree (auxThParentBase auxPtr vCap n0 + i) (by omega) (by omega)
    rw [this]; exact hth i hi
  · intro v hv
    have hb : auxPtr ≤ auxIsOrigVertBase auxPtr vCap n0 := by
      dsimp [auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
        auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
        auxVListBase, auxVIdxBase]; omega
    have he : auxIsOrigVertBase auxPtr vCap n0 + vCap ≤ auxPtr + auxSize vCap n0 := by
      dsimp [auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase,
        auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase,
        auxVListBase, auxVIdxBase, auxSize]; omega
    have := hagree (auxIsOrigVertBase auxPtr vCap n0 + v) (by omega) (by omega)
    exact this.trans (hIsOrig v hv)
  · intro w hw hwl
    have hb : auxPtr ≤ auxOrigVertBase auxPtr vCap n0 := by
      dsimp [auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
        auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega
    have he : auxOrigVertBase auxPtr vCap n0 + vCap ≤ auxPtr + auxSize vCap n0 := by
      dsimp [auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
        auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]; omega
    have := hagree (auxOrigVertBase auxPtr vCap n0 + w) (by omega) (by omega)
    exact this.trans (hOrig w hw hwl)
  · intro v hv
    have hbA : auxPtr ≤ auxVisABase auxPtr vCap n0 := by
      dsimp [auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase, auxOrigVertBase,
        auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase,
        auxT0ParentBase, auxVListBase, auxVIdxBase]; omega
    have heA : auxVisABase auxPtr vCap n0 + vCap ≤ auxPtr + auxSize vCap n0 := by
      dsimp [auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase, auxOrigVertBase,
        auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase, auxT0ParentTreeIdxBase,
        auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]; omega
    have hbB : auxPtr ≤ auxVisBBase auxPtr vCap n0 := by
      dsimp [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
        auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
        auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]; omega
    have heB : auxVisBBase auxPtr vCap n0 + vCap ≤ auxPtr + auxSize vCap n0 := by
      dsimp [auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase, auxIsOrigVertBase,
        auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase, auxT0DepthBase,
        auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase, auxSize]; omega
    have hma := hagree (auxVisABase auxPtr vCap n0 + v) (by omega) (by omega)
    have hmb := hagree (auxVisBBase auxPtr vCap n0 + v) (by omega) (by omega)
    exact ⟨hma.trans (hVis v hv).1, hmb.trans (hVis v hv).2⟩

end MinCostFlow.LSF.Program
