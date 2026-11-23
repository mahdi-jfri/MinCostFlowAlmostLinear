module

public import MinCostFlow.LastLevelProgram.StagedController
public import MinCostFlow.LastLevelProgram.CanonicalModel
public import MinCostFlow.MinRatio.LastLevelContract
import MinCostFlow.LastLevelProgram.ConnectedLSST
import MinCostFlow.LastLevelProgram.OutputCapacity
import MinCostFlow.Num.WordBounds
import MinCostFlow.LSF.Components

/-!
# Inputs to the staged last-level round

The controller for Definition 5.8 (pages 19–20) copies the compact
graph, retains the current host weights, and invokes the guest selector.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num

/-- The staging copy and the controller invariant establish the guest
selector's precondition on the model weights. -/
theorem stagedController_selectorReady
    {w vCap eCap L P caller base count handle bound j src guestL sim Q stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged : State) (len : ℕ → ℤ)
    (hs : stagedRoundStateAtStride H vCap eCap 4 L P caller base count handle bound stride E branches ρ query mem j st)
    (hstrideGe : L ≤ stride)
    (hcopy : ∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = st.mem (src+i))
    (hframe : ∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a → staged.mem a = st.mem a)
    (ht : ∀ i < H.m, st.mem (src+i) = (indexedGraph H).tail i)
    (hh : ∀ i < H.m, st.mem (src+(H.m+i)) = (indexedGraph H).head i)
    (hlen : ∀ i < H.m, ListAt st.mem (src+queryLengths H+i*guestL)
      (encodeLimbs 1 guestL (len (edgeName H i))))
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hP : P+guestL < 2^w) (hQ : Q < 2^w)
    (hm : H.m < 2^w) (hroom : st.regs 0+queryOriginals H guestL < 2^w)
    (hpos : ∀ e ∈ H.E, 0 ≤ weights P ρ query j e)
    (hfit : ∀ e ∈ H.E, Fits 1 guestL (queryNumerator Q (weights P ρ query j e))) :
    let cursor := st.regs 0
    let source := st.mem (cursor-1)
    let input := stagedGuestArgs H guestL sim cursor source stride P Q ++ List.replicate 7 0 ++ [L]
    convertedSelectorReady w H guestL sim cursor source stride P Q L len
      (queryNumerator Q ∘ weights P ρ query j) input staged.mem := by
  obtain ⟨ht',hh',hlen',_,_⟩ :=
    stagedController_numericInput st staged len hs hcopy (fun a ha => hframe a (Or.inl ha)) ht hh hlen
  obtain ⟨hpack,hzero,hwt⟩ :=
    stagedController_selectorMemory st staged hs hstrideGe hframe hw hL hP hQ hm hroom hpos hfit
  refine ⟨rfl,hpack,ht',hh',hlen',fun i hi => (hwt i hi).symm,?_⟩
  intro a ha
  apply hzero a
  unfold queryOriginals at ha
  omega

/-- The selector call evaluates to the converted input words and all
of them fit the host machine. The cursor and weight pointer fit by
the collection invariant. -/
theorem stagedController_selectorWords
    {w vCap eCap L P caller base count handle bound j guestL sim Q stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged : State) (pos : ℕ)
    (hs : stagedRoundStateAtStride H vCap eCap 4 L P caller base count handle bound stride E branches ρ query mem j st)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hcursor : staged.regs 5 = st.regs 0)
    (hweight : staged.regs 8 = st.mem (st.regs 0-1))
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim)
    (hstride : st.regs 81 = stride) (hP : st.regs 82 = P) (hQ : st.regs 83 = Q)
    (hhost : st.regs 91 = L) (hbound : bound < 2^w)
    (hwords : ∀ r, st.regs r < 2^w) :
    let args := stagedGuestArgs H guestL sim (st.regs 0) (st.mem (st.regs 0-1))
      stride P Q ++ List.replicate 7 0 ++ [L]
    evalArgs w staged convertedGuestCallArgs = some args ∧ ∀ a ∈ args, a < 2^w := by
  intro args
  refine ⟨stagedController_selectorArgs st staged pos H guestL sim stride P Q L
    hkeep hcursor hweight hn hm hguest hsim hstride hP hQ hhost,?_⟩
  have hptr : st.mem (st.regs 0-1) < 2^w := by
    obtain ⟨_,_,_,_,hb,_,_,_,hend,_⟩ := hs
    exact (show st.mem (st.regs 0-1) ≤ bound by omega).trans_lt hbound
  intro a ha
  simp only [args,stagedGuestArgs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    List.mem_replicate] at ha
  rcases ha with (ha | ha) | ha
  · rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hn ▸ hwords 72
    · exact hm ▸ hwords 73
    · exact hguest ▸ hwords 74
    · exact hsim ▸ hwords 75
    · exact Nat.two_pow_pos _
    · exact hwords 0
    · exact Nat.two_pow_pos _
    · exact Nat.two_pow_pos _
    · exact hptr
    · exact hstride ▸ hwords 81
    · exact hP ▸ hwords 82
    · exact hQ ▸ hwords 83
  · exact ha.2.symm ▸ Nat.two_pow_pos _
  · exact ha.symm ▸ (hhost ▸ hwords 91)

/-- The prepared controller state gives the three selector-call
premises consumed by the numeric round. -/
theorem stagedController_selectorCall
    {w vCap eCap L P caller base count handle bound j src guestL sim Q stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged : State) (pos : ℕ) (len : ℕ → ℤ)
    (hs : stagedRoundStateAtStride H vCap eCap 4 L P caller base count handle bound stride E branches ρ query mem j st)
    (hstrideGe : L ≤ stride)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hcursor : staged.regs 5 = st.regs 0)
    (hweight : staged.regs 8 = st.mem (st.regs 0-1))
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim)
    (hstride : st.regs 81 = stride) (hP : st.regs 82 = P) (hQ : st.regs 83 = Q)
    (hhost : st.regs 91 = L) (hbound : bound < 2^w) (hwords : ∀ r, st.regs r < 2^w)
    (hcopy : ∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = st.mem (src+i))
    (hframe : ∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a → staged.mem a = st.mem a)
    (ht : ∀ i < H.m, st.mem (src+i) = (indexedGraph H).tail i)
    (hh : ∀ i < H.m, st.mem (src+(H.m+i)) = (indexedGraph H).head i)
    (hlen : ∀ i < H.m, ListAt st.mem (src+queryLengths H+i*guestL)
      (encodeLimbs 1 guestL (len (edgeName H i))))
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hprec : P+guestL < 2^w)
    (hroom : st.regs 0+queryOriginals H guestL < 2^w)
    (hpos : ∀ e ∈ H.E, 0 ≤ weights P ρ query j e)
    (hfit : ∀ e ∈ H.E, Fits 1 guestL (queryNumerator Q (weights P ρ query j e))) :
    let cursor := st.regs 0
    let source := st.mem (cursor-1)
    let input := stagedGuestArgs H guestL sim cursor source stride P Q ++ List.replicate 7 0 ++ [L]
    evalArgs w staged convertedGuestCallArgs = some input ∧ (∀ a ∈ input, a < 2^w) ∧
    convertedSelectorReady w H guestL sim cursor source stride P Q L len
      (queryNumerator Q ∘ weights P ρ query j) input staged.mem := by
  obtain ⟨heval,hfits⟩ := stagedController_selectorWords st staged pos hs hkeep hcursor hweight
    hn hm hguest hsim hstride hP hQ hhost hbound hwords
  exact ⟨heval,hfits,stagedController_selectorReady (sim := sim) st staged len hs hstrideGe hcopy hframe
    ht hh hlen hw hL hprec (hQ ▸ hwords 83) (hm ▸ hwords 73) hroom hpos hfit⟩

/-- A fitting canonical query supplies the guest weight fit checks for the
controller's selector call. -/
theorem stagedController_canonicalSelectorCall
    {w vCap eCap L P caller base count handle bound j src guestL sim Q stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged : State) (pos : ℕ) (len : ℕ → ℝ) (C : ℝ)
    (hready : GraphQueryReady C H len (weights P ρ query j))
    (hguestL : guestL = roundQueryLimbs C H len)
    (hguestQ : Q = roundQueryPrecision C H len)
    (hs : stagedRoundStateAtStride H vCap eCap 4 L P caller base count handle bound stride E branches ρ query mem j st)
    (hstrideGe : L ≤ stride)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hcursor : staged.regs 5 = st.regs 0)
    (hweight : staged.regs 8 = st.mem (st.regs 0-1))
    (hn : st.regs 72 = H.n) (hm : st.regs 73 = H.m)
    (hguest : st.regs 74 = guestL) (hsim : st.regs 75 = sim)
    (hstride : st.regs 81 = stride) (hP : st.regs 82 = P) (hQ : st.regs 83 = Q)
    (hhost : st.regs 91 = L) (hbound : bound < 2^w) (hwords : ∀ r, st.regs r < 2^w)
    (hcopy : ∀ i < queryWeights H guestL, staged.mem (st.regs 0+i) = st.mem (src+i))
    (hframe : ∀ a, a < st.regs 0 ∨ st.regs 0+queryWeights H guestL ≤ a → staged.mem a = st.mem a)
    (ht : ∀ i < H.m, st.mem (src+i) = (indexedGraph H).tail i)
    (hh : ∀ i < H.m, st.mem (src+(H.m+i)) = (indexedGraph H).head i)
    (hlen : ∀ i < H.m, ListAt st.mem (src+queryLengths H+i*guestL)
      (encodeLimbs 1 guestL (queryNumerator Q (len (edgeName H i)))))
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hprec : P+guestL < 2^w)
    (guest : Program) (D : ℕ)
    (hspace : st.regs 0+queryOriginals H guestL+1+
      2^paddedGuestWidth guest D H.n H.m sim (queryHeap H guestL) ≤ 2^w) :
    let cursor := st.regs 0
    let source := st.mem (cursor-1)
    let input := stagedGuestArgs H guestL sim cursor source stride P Q ++ List.replicate 7 0 ++ [L]
    evalArgs w staged convertedGuestCallArgs = some input ∧ (∀ a ∈ input, a < 2^w) ∧
    convertedSelectorReady w H guestL sim cursor source stride P Q L (queryNumerator Q ∘ len)
      (queryNumerator Q ∘ weights P ρ query j) input staged.mem := by
  have hfit (e : ℕ) (he : e ∈ H.E) :
      Fits 1 guestL (queryNumerator Q (weights P ρ query j e)) := by
    rw [hguestL, hguestQ]
    exact (hready.2.2.2.2.1 e he).2
  have hpos (e : ℕ) (he : e ∈ H.E) : 0 ≤ weights P ρ query j e := by
    obtain ⟨a, ha⟩ := hready.2.2.2.2.2.2 e
    have hnum := (hready.2.2.2.2.1 e he).1
    rw [ha, queryNumerator_grid] at hnum
    exact ha.symm ▸ div_nonneg (by exact_mod_cast hnum.le) (by positivity)
  have hroom : st.regs 0+queryOriginals H guestL < 2^w :=
    (Nat.lt_succ_self _).trans_le ((Nat.le_add_right _ _).trans hspace)
  exact stagedController_selectorCall st staged pos (queryNumerator Q ∘ len) hs hstrideGe hkeep
    hcursor hweight hn hm hguest hsim hstride hP hQ hhost hbound hwords hcopy hframe
    ht hh hlen hw hL hprec hroom hpos hfit

/-- The controller's binary-lifting depth covers every vertex and
leaves room for the row count in a host word. -/
theorem stagedController_levelBounds (st staged : State) (pos n w : ℕ)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r)
    (hlevel : st.regs 86 = Nat.clog 2 n) (hword : n+1 < 2^w) :
    staged.regs 14 = Nat.clog 2 n ∧ n ≤ 2^(staged.regs 14+1) ∧
      staged.regs 14+1 < 2^w := by
  have hr : staged.regs 14 = Nat.clog 2 n := by
    simpa [startState,roundControllerRegister,List.getD,hlevel] using
      hkeep 14 (by decide) (by decide) (by decide) (by decide)
  refine ⟨hr,?_,?_⟩
  · rw [hr]
    exact (Nat.le_pow_clog (by decide : 1 < 2) n).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  · rw [hr]
    have hlog : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_two_pow_self))
    exact (Nat.succ_le_succ hlog).trans_lt hword

/-- The numeric pass and the selector share the compact graph counts
and the guest format forwarded by the controller. -/
theorem stagedController_graphRegisters (st staged : State) (pos : ℕ)
    (hkeep : ∀ r, r ≠ 5 → r ≠ 8 → r ≠ 31 → r ≠ 70 →
      staged.regs r = (startState ((List.range 70).map (st.regs ∘ roundControllerRegister))
        st.mem pos).regs r) :
    staged.regs 0 = st.regs 72 ∧ staged.regs 1 = st.regs 73 ∧
    staged.regs 2 = st.regs 74 ∧ staged.regs 3 = st.regs 75 := by
  refine ⟨?_,?_,?_,?_⟩
  · simpa [startState,roundControllerRegister,List.getD] using
      hkeep 0 (by decide) (by decide) (by decide) (by decide)
  · simpa [startState,roundControllerRegister,List.getD] using
      hkeep 1 (by decide) (by decide) (by decide) (by decide)
  · simpa [startState,roundControllerRegister,List.getD] using
      hkeep 2 (by decide) (by decide) (by decide) (by decide)
  · simpa [startState,roundControllerRegister,List.getD] using
      hkeep 3 (by decide) (by decide) (by decide) (by decide)

/-- The numeric pass reads the original host length blocks by
representative edge name. Staging preserves those live blocks and the
compact name table. -/
theorem stagedController_numericLengths {G : MGraph} {h L src names cursor guestL : ℕ}
    {input staged : ℕ → ℕ} (ℓ : ℕ → ℝ) (len : ℕ → ℤ)
    (hG : G.IsValid) (hsrc : src ≤ cursor) (hframe : ∀ a < cursor, staged a = input a)
    (hlength : ∀ e ∈ G.E, src+e*L+L ≤ cursor ∧ Valid input (src+e*L) h L ∧
      intVal input (src+e*L) h L = len e) :
    let H := representativeGraph G ℓ
    names+H.m ≤ cursor →
    (∀ i < H.m, input (names+i) = edgeName H i) →
    let stop := cursor+queryWeights H guestL
    (src ≤ stop ∧ ∀ e ∈ H.E, src+e*L+L ≤ stop) ∧ names+H.m ≤ stop ∧
    (∀ i < H.m, staged (names+i) = edgeName H i) ∧
    ∀ e ∈ H.E, Valid staged (src+e*L) h L ∧ intVal staged (src+e*L) h L = len e := by
  intro H hnameEnd hnames stop
  have hstop : cursor ≤ stop := Nat.le_add_right _ _
  have hsub := (representativeGraph_subgraph hG ℓ).2.1
  refine ⟨⟨hsrc.trans hstop,fun e he => (hlength e (hsub he)).1.trans hstop⟩,
    hnameEnd.trans hstop,fun i hi => (hframe _ (by omega)).trans (hnames i hi),?_⟩
  intro e he
  obtain ⟨hend,hvalid,hval⟩ := hlength e ((representativeGraph_subgraph hG ℓ).2.1 he)
  have hkeep k (hk : k < L) : staged (src+e*L+k) = input (src+e*L+k) :=
    hframe _ (by omega)
  exact ⟨fun k hk => (hkeep k hk).trans_lt (hvalid k hk),(intVal_congr hkeep).trans hval⟩

/-- Branch append reads names below the staging cursor and endpoints
from the copied compact graph. -/
theorem stagedController_appendNames (H : MGraph) (input staged : ℕ → ℕ)
    (names vertices cursor guestL : ℕ)
    (hframe : ∀ a < cursor, staged a = input a)
    (hnames : names+H.m ≤ cursor) (hvertices : vertices+H.n ≤ cursor)
    (hname : ∀ i < H.m, input (names+i) = edgeName H i)
    (hvertex : ∀ i < H.n, input (vertices+i) = vertexName H i)
    (ht : ∀ i < H.m, staged (cursor+i) = (indexedGraph H).tail i)
    (hh : ∀ i < H.m, staged (cursor+(H.m+i)) = (indexedGraph H).head i) :
    names+H.m ≤ cursor+queryWeights H guestL ∧
    vertices+H.n ≤ cursor+queryWeights H guestL ∧
    (∀ i < H.m, staged (names+i) = edgeName H i ∧
      staged (cursor+i) = (indexedGraph H).tail i ∧
      staged (cursor+(H.m+i)) = (indexedGraph H).head i) ∧
    (∀ i < H.n, staged (vertices+i) = vertexName H i) := by
  have hle : cursor ≤ cursor+queryWeights H guestL := Nat.le_add_right _ _
  exact ⟨hnames.trans hle,hvertices.trans hle,
    fun i hi => ⟨(hframe _ (by omega)).trans (hname i hi),ht i hi,hh i hi⟩,
    fun i hi => (hframe _ (by omega)).trans (hvertex i hi)⟩

/-- Restrict the caller's fixed-point length blocks to the representatives.
Their integer payloads are the numerators of the safe lengths used by the
numeric tree pass. -/
theorem stagedController_callerLengthNumerators (G : MGraph) (mem : ℕ → ℕ)
    (src L Q : ℕ) (hG : G.IsValid)
    (hvalid : ∀ e ∈ G.E, Valid mem (src+e*L) 4 L)
    (hpos : ∀ e ∈ G.E, 0 < MinRatio.readEdgeValues mem src 4 L Q G.E e) :
    let ℓ := MinRatio.readEdgeValues mem src 4 L Q G.E
    let H := representativeGraph G ℓ
    let len := queryNumerator Q ∘ LSF.safeLen H ℓ
    (∀ e ∈ H.E, Valid mem (src+e*L) 4 L ∧
      intVal mem (src+e*L) 4 L = len e ∧ 0 < len e) ∧
    OnQueryGrid Q (LSF.safeLen H ℓ) := by
  intro ℓ H len
  have hsub := (representativeGraph_subgraph hG ℓ).2.1
  have hdecode (e : ℕ) (he : e ∈ H.E) :
      LSF.safeLen H ℓ e = (intVal mem (src+e*L) 4 L : ℝ)/(2 : ℝ)^Q := by
    rw [LSF.safeLen_eq_of_mem ℓ he]
    simp [ℓ,MinRatio.readEdgeValues,hsub he,fixVal]
  refine ⟨?_,?_⟩
  · intro e he
    have hnum : len e = intVal mem (src+e*L) 4 L := by
      change queryNumerator Q (LSF.safeLen H ℓ e) = _
      rw [hdecode e he,queryNumerator_grid]
    have hv := hpos e (hsub he)
    change 0 < ℓ e at hv
    rw [← LSF.safeLen_eq_of_mem ℓ he,hdecode e he] at hv
    have hn := (div_pos_iff_of_pos_right (show (0 : ℝ) < (2 : ℝ)^Q by positivity)).mp hv
    exact ⟨hvalid e (hsub he),hnum.symm,hnum.symm ▸ (by exact_mod_cast hn)⟩
  · intro e
    by_cases he : e ∈ H.E
    · exact ⟨_,hdecode e he⟩
    · refine ⟨0,?_⟩
      simp [LSF.safeLen,he]

/-- Encode the safe lengths on the caller grid so the numeric pass
computes the rounded stretches of the canonical model. -/
theorem stagedController_encodedStretches {H T : MGraph} {ℓ v : ℕ → ℝ} {γ : ℝ}
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (Q P : ℕ)
    (hH : H.IsValid)
    (htree : LSF.IsLSST (indexedGraph H).toMGraph (LSF.safeLen H ℓ ∘ edgeName H)
      (v ∘ edgeName H) γ T)
    (horacle : oracle H (LSF.safeLen H ℓ) v = restoreTreeNames H T)
    (hgrid : OnQueryGrid Q (LSF.safeLen H ℓ)) :
    ∀ i < H.m, roundStretch P (treeStretch (indexedGraph H).toMGraph T
        (fun e => (queryNumerator Q (LSF.safeLen H ℓ (edgeName H e)) : ℝ)/(2 : ℝ)^Q) i) =
      stretchQuery oracle H ℓ P v (edgeName H i) := by
  apply encodedRoundStretch_eq_query oracle Q P _ hH htree horacle
  intro i
  obtain ⟨a,ha⟩ := hgrid (edgeName H i)
  change (queryNumerator Q (LSF.safeLen H ℓ (edgeName H i)) : ℝ)/(2 : ℝ)^Q =
    LSF.safeLen H ℓ (edgeName H i)
  rw [ha,queryNumerator_grid]

/-- The host update consumes the same live weights as the selector,
with the scale interpreted as the integer read by the machine. -/
theorem stagedController_numericWeights
    {w vCap eCap h L P caller base count handle bound j guestL scale stride : ℕ}
    {H : MGraph} {E : Finset ℕ} {branches : ℕ → LSF} {ρ : ℝ} {query : (ℕ → ℝ) → ℕ → ℝ}
    {mem : ℕ → ℕ} (st staged : State)
    (hs : stagedRoundStateAtStride H vCap eCap h L P caller base count handle bound stride E branches ρ query mem j st)
    (hstrideGe : L ≤ stride)
    (hframe : ∀ a < st.regs 0, staged.mem a = st.mem a)
    (hscale : (scale : ℝ) = ρ) (hstride : st.regs 104 = stride)
    (hwords : ∀ r, st.regs r < 2^w) :
    let source := st.mem (st.regs 0-1)
    let stagingEnd := st.regs 0+queryWeights H guestL
    stride < 2^w ∧ L ≤ stride ∧ source+(H.m-1)*stride+L ≤ stagingEnd ∧
    (∀ i < H.m, source+i*stride+L ≤ stagingEnd ∧ Valid staged.mem (source+i*stride) h L) ∧
    ∀ i < H.m, fixVal staged.mem (source+i*stride) h L P =
      weights P ((scale : ℤ) : ℝ) query j (edgeName H i) := by
  intro source stagingEnd
  obtain ⟨hend,hweights⟩ := stagedController_stagedWeights st staged hs hframe
  have hscale' : ((scale : ℤ) : ℝ) = ρ := by exact_mod_cast hscale
  refine ⟨by simpa only [← hstride] using hwords 104,hstrideGe,
    hend.trans (Nat.le_add_right _ _),?_,?_⟩
  · intro i hi
    have hmul := Nat.mul_le_mul_right stride (show i ≤ H.m-1 by omega)
    exact ⟨(Nat.add_le_add_right (Nat.add_le_add_left hmul source) L).trans
      (hend.trans (Nat.le_add_right _ _)),(hweights i hi).1⟩
  · intro i hi
    rw [hscale']
    exact (hweights i hi).2

/-- One capacity bound on the scaled update denominator covers its
unscaled word and the shared unit block used by branch append. -/
theorem stagedController_scaleFits {h L P scale : ℕ}
    (hpos : 0 < scale) (hwidth : 2*(scale : ℝ)*(2 : ℝ)^P < capacity h L) :
    Fits h L (scale : ℤ) ∧ Fits h L ((scale : ℤ)*(2 : ℤ)^P) ∧
      2*(2 : ℝ)^P < capacity h L := by
  have hpos' : (0 : ℤ) < scale := by exact_mod_cast hpos
  have hpow : 1 ≤ (2 : ℝ)^P := one_le_pow₀ (by norm_num)
  have hscale : (1 : ℝ) ≤ scale := by exact_mod_cast hpos
  have hbase : 2*(scale : ℝ) ≤ 2*(scale : ℝ)*(2 : ℝ)^P := by
    exact le_mul_of_one_le_right (by positivity) hpow
  have hunit : 2*(2 : ℝ)^P ≤ 2*(scale : ℝ)*(2 : ℝ)^P := by
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hfit := scaledDenominator_fits (P := 0) hpos' (by
    simpa only [pow_zero,mul_one,Int.cast_natCast] using hbase.trans_lt hwidth)
  exact ⟨by simpa only [pow_zero,mul_one] using hfit,
    scaledDenominator_fits hpos' (by simpa only [Int.cast_natCast] using hwidth),
    hunit.trans_lt hwidth⟩

/-- The capacity check made for the representative graph also covers
the selected tree's distance and rounded stretch intermediates. -/
theorem stagedController_treeCapacity {h L P B : ℕ} {H T : MGraph}
    (hvertices : T.V.card ≤ H.n)
    (hwidth : 2*((2*(H.n : ℤ)*B+B)*(2 : ℤ)^P) < (capacity h L : ℤ)) :
    2*((2*(T.V.card : ℤ)*B+B)*(2 : ℤ)^P) < (capacity h L : ℤ) := by
  have hn : (T.V.card : ℤ) ≤ H.n := by exact_mod_cast hvertices
  have hB : (0 : ℤ) ≤ B := Int.natCast_nonneg _
  have hp : (0 : ℤ) ≤ (2 : ℤ)^P := by positivity
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by decide : (0 : ℤ) ≤ 2)) hB
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (add_le_add hb (le_refl (B : ℤ))) hp) (by decide : (0 : ℤ) ≤ 2)).trans_lt hwidth

/-- A connected input with a live non-loop edge gives a valid and
connected compact graph for the selector and numeric traversal. -/
theorem stagedController_compactGraph (G : MGraph) (ℓ : ℕ → ℝ)
    (hG : G.IsValid) (hne : (SparseCore.nonLoopEdges G).Nonempty)
    (hconn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    let H := representativeGraph G ℓ
    (indexedGraph H).Valid ∧ 0 < H.m ∧
    ∀ u ∈ (indexedGraph H).toMGraph.V, ∀ v ∈ (indexedGraph H).toMGraph.V,
      (indexedGraph H).toMGraph.Connected u v := by
  intro H
  obtain ⟨e,he⟩ := hne
  obtain ⟨hf,_,_⟩ := representativeGraph_shortest (ℓ := ℓ) he
  have hv := representativeGraph_valid G ℓ
  have hsub := (representativeGraph_subgraph hG ℓ).1
  refine ⟨indexedGraph_valid hv ⟨_,(hv _ hf).1⟩,Finset.card_pos.mpr ⟨_,hf⟩,?_⟩
  exact indexedGraph_connected fun u hu v hv' =>
    representativeGraph_connected ℓ (hconn u (hsub hu) v (hsub hv'))

/-- Tree selection preserves the endpoint arrays and the host blocks
read by the widened arithmetic preparation. -/
theorem selectedTree_numericSources
    {G T : MGraph} {st selected : State} {base dest count staging names src weights stride h L : ℕ}
    (htree : selectedTreeAt G T base dest count st.mem selected.mem)
    (hend : staging+2*G.m ≤ base) (hnEnd : names+G.m ≤ base)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hh : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i)
    (hn : ∀ i < G.m, st.mem (names+i) = edgeName G i)
    (hl : ∀ e ∈ G.E, src+e*L+L ≤ base ∧ Valid st.mem (src+e*L) h L)
    (hw : ∀ i < G.m, weights+i*stride+L ≤ base ∧ Valid st.mem (weights+i*stride) h L) :
    (∀ i < G.m, selected.mem (staging+i) = (indexedGraph G).tail i) ∧
    (∀ i < G.m, selected.mem (staging+(G.m+i)) = (indexedGraph G).head i) ∧
    (∀ i < G.m, selected.mem (names+i) = edgeName G i) ∧
    (∀ e ∈ G.E, Valid selected.mem (src+e*L) h L ∧
      intVal selected.mem (src+e*L) h L = intVal st.mem (src+e*L) h L) ∧
    (∀ i < G.m, Valid selected.mem (weights+i*stride) h L ∧
      intVal selected.mem (weights+i*stride) h L = intVal st.mem (weights+i*stride) h L) := by
  obtain ⟨_,_,_,_,_,_,hf,_⟩ := htree
  have preserve {addr : ℕ} (ha : addr+L ≤ base) (hv : Valid st.mem addr h L) :
      Valid selected.mem addr h L ∧ intVal selected.mem addr h L = intVal st.mem addr h L := by
    have agree (i : ℕ) (hi : i < L) := hf (addr+i) (by omega)
    exact ⟨fun i hi => (agree i hi).trans_lt (hv i hi),intVal_congr agree⟩
  exact ⟨fun i hi => (hf _ (by omega)).trans (ht i hi),
    fun i hi => (hf _ (by omega)).trans (hh i hi),
    fun i hi => (hf _ (by omega)).trans (hn i hi),
    fun e he => preserve (hl e he).1 (hl e he).2,
    fun i hi => preserve (hw i hi).1 (hw i hi).2⟩

/-- The guest prefix and the retained tree precede the arithmetic
scratch tables. Tree selection leaves those tables fresh. -/
theorem selectedTree_wideScratch
    {G T : MGraph} {st selected : State} {staging guestL width levels : ℕ}
    (htree : selectedTreeAt G T (staging+queryWeights G guestL)
      (staging+queryOriginals G guestL+1+2^width+G.m) (selected.regs 13) st.mem selected.mem)
    (hcursor : selected.regs 12 = staging+queryOriginals G guestL+2^width) :
    let dest := selected.regs 12+1+G.m
    let adj := dest+G.n+stagedTraversalReserve G.n levels
    let records := adj+G.n
    let tails := records+6*G.n
    staging+2*G.m ≤ staging+queryWeights G guestL ∧
    staging+queryWeights G guestL ≤ dest ∧
    selectedTreeAt G T (staging+queryWeights G guestL) dest (selected.regs 13)
      st.mem selected.mem ∧
    ZeroFrom selected.mem tails := by
  intro dest adj records tails
  have hweights : 2*G.m ≤ queryWeights G guestL := by
    unfold queryWeights queryLengths
    omega
  have horig : queryWeights G guestL ≤ queryOriginals G guestL := by
    unfold queryOriginals
    omega
  have hd : dest = staging+queryOriginals G guestL+1+2^width+G.m := by
    dsimp [dest]
    omega
  have htree' : selectedTreeAt G T (staging+queryWeights G guestL) dest (selected.regs 13)
      st.mem selected.mem := hd.symm ▸ htree
  have hcopy := htree'
  obtain ⟨_,_,_,_,_,_,_,hz⟩ := hcopy
  exact ⟨by omega,hd.symm ▸ ((Nat.add_le_add_left horig staging).trans ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))),htree',fun a ha => hz a (by
    dsimp [tails,records,adj] at ha
    omega)⟩

/-- Prepare widened arithmetic directly after tree selection. The packed
numerators agree with the staged sources and the original prefix survives. -/
theorem prepareWideStagedNumeric_of_selection
    {w h copy packLengths packWeights prepare extend store shift : ℕ}
    {p : Program} {ω : ℕ → Bool} (st selected : State) (G T : MGraph)
    (staging guestL width levels src names weights stride L P scale : ℕ)
    (htree : selectedTreeAt G T (staging+queryWeights G guestL)
      (staging+queryOriginals G guestL+1+2^width+G.m) (selected.regs 13) st.mem selected.mem)
    (hcursor : selected.regs 12 = staging+queryOriginals G guestL+2^width)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hl : p.procs[packLengths]? = some (packWideValuesBody extend))
    (hwg : p.procs[packWeights]? = some (packWideWeightsBody extend))
    (hd : p.procs[prepare]? = some (denominatorBody store shift))
    (hx : p.HasAt extend (Num.signExtendModule extend h))
    (hstore : p.procs[store]? = some (storeWordBody h))
    (hshift : p.HasAt shift (Num.shiftLeftModule shift h))
    (hbits : 2*h+2 ≤ w) (hh : 0 < h) (hw : 7 < 2^w) (hn : 0 < G.n)
    (h0 : selected.regs 0 = G.n) (h1 : selected.regs 1 = G.m) (h5 : selected.regs 5 = staging)
    (h14 : selected.regs 14 = levels) (h19 : selected.regs 19 = L)
    (h23 : selected.regs 23 = P) (h27 : selected.regs 27 = src) (h28 : selected.regs 28 = names)
    (h31 : selected.regs 31 = weights) (h32 : selected.regs 32 = stride) (h35 : selected.regs 35 = scale)
    (hwords : ∀ r, selected.regs r < 2^w) (hprec : P+levels+7 < 2^w)
    (ht : ∀ i < G.m, st.mem (staging+i) = (indexedGraph G).tail i)
    (hhead : ∀ i < G.m, st.mem (staging+(G.m+i)) = (indexedGraph G).head i) :
    let K := L+(P+levels+7)/4
    let base := staging+queryWeights G guestL
    let dest := selected.regs 12+1+G.m
    let adj := dest+G.n+stagedTraversalReserve G.n levels
    let records := adj+G.n
    let tails := records+6*G.n
    let lengths := tails+2*G.m
    let old := lengths+G.m*K
    let dst := old+G.m*K
    let dist := dst+2*K
    let heap := dist+G.n*K
    K < 2^w → heap < 2^w →
    names+G.m ≤ base → (∀ i < G.m, st.mem (names+i) = edgeName G i) →
    (∀ e ∈ G.E, src+e*L+L ≤ base ∧ Num.Valid st.mem (src+e*L) h L) →
    (∀ i < G.m, weights+i*stride+L ≤ base ∧ Num.Valid st.mem (weights+i*stride) h L) →
    Num.Fits h K (scale : ℤ) → Num.Fits h K ((scale : ℤ)*(2 : ℤ)^P) →
    ∃ out cost, Runs w p ω (prepareWideStagedNumericBody copy packLengths packWeights prepare)
      selected .normal out cost ∧
      (∀ i < G.m,
        (Num.Valid out.mem (lengths+i*K) h K ∧ Num.intVal out.mem (lengths+i*K) h K =
          Num.intVal st.mem (src+edgeName G i*L) h L) ∧
        (Num.Valid out.mem (old+i*K) h K ∧ Num.intVal out.mem (old+i*K) h K =
          Num.intVal st.mem (weights+i*stride) h L)) ∧
      Num.Valid out.mem (dst+K) h K ∧ Num.intVal out.mem (dst+K) h K = (scale : ℤ)*(2 : ℤ)^P ∧
      ZeroFrom out.mem dist ∧
      out.regs 21 = tails ∧ out.regs 22 = tails+G.m ∧ out.regs 18 = lengths ∧
      out.regs 26 = old ∧ out.regs 25 = dst+K ∧ out.regs 17 = dist ∧
      out.regs 20 = heap ∧ out.regs 24 = K ∧
      (∀ r, r ∉ ([64,21,22,18,26,25,17,20,24,29,30,33,34] : List ℕ) → out.regs r = selected.regs r) ∧
      ListAt out.mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) ∧
      ListAt out.mem (tails+G.m) (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) ∧
      retainedStagedTreeAt G T base dest (selected.regs 13) st.mem out.mem ∧
      (∀ a, dest+G.n ≤ a → a < records → out.mem a = 0) ∧
      (∀ a < tails, out.mem a = selected.mem a) ∧
      (∀ a < base, out.mem a = st.mem a) ∧
      cost ≤ stagedScratchWidthExpr.size+
        argsSize (stagedNumericLayoutArgs (.reg 0) (.reg 1) (.reg 14) (.reg 12) (.reg 64) ++
          [.reg 64])+37+34*G.m+(2*((30*K+90)*G.m+20)+56*K+72) := by
  intro K base dest adj records tails lengths old dst dist heap hkw hheap hnEnd hnames hlengths hweights hscale hdenom
  obtain ⟨hend,hbase,hselected,hz⟩ := selectedTree_wideScratch (levels := levels) htree hcursor
  have hroom : base ≤ tails := hbase.trans (by
    dsimp [tails,records,adj]
    omega)
  obtain ⟨ht',hh',hn',hl',hw'⟩ :=
    selectedTree_numericSources htree hend hnEnd ht hhead hnames hlengths hweights
  obtain ⟨out,cost,hr,hblocks,hdenv,hdene,hzero,h21,h22,h18,h26,h25,h17,h20,h24,hkeep,htail,hhead',hf,hcost⟩ :=
    prepareWideStagedNumeric_runs (ω := ω) selected G staging (selected.regs 12) levels
      src names weights stride L P scale hc hl hwg hd hx hstore hshift hbits hh hw hn
      h0 h1 h5 rfl h14 h19 h23 h27 h28 h31 h32 h35 hwords hprec ht' hh'
      hkw hheap (hend.trans hroom) hz (hnEnd.trans hroom) hn'
      (fun e he => ⟨(hlengths e he).1.trans hroom,(hl' e he).1⟩)
      (fun i hi => ⟨(hweights i hi).1.trans hroom,(hw' i hi).1⟩) hscale hdenom
  have hretain := retainedStagedTreeAt_of_frame hselected hroom
    (show dest+G.n ≤ tails by dsimp [tails,records,adj]; omega) hf
  obtain ⟨_,_,_,_,_,_,hframe,hfresh⟩ := hselected
  have hclear (a : ℕ) (ha : dest+G.n ≤ a) (hb : a < records) : out.mem a = 0 :=
    (hf a (hb.trans_le (Nat.le_add_right _ _))).trans (hfresh a ha)
  refine ⟨out,cost,hr,?_,hdenv,hdene,hzero,h21,h22,h18,h26,h25,h17,h20,h24,
    hkeep,htail,hhead',hretain,hclear,hf,fun a ha => (hf a (ha.trans_le hroom)).trans (hframe a ha),hcost⟩
  intro j hj
  obtain ⟨⟨hvl,hel⟩,⟨hvw,hew⟩⟩ := hblocks j hj
  exact ⟨⟨hvl,hel.trans (hl' _ (edgeName_mem hj)).2⟩,⟨hvw,hew.trans (hw' j hj).2⟩⟩

end MinCostFlow.LastLevelProgram
