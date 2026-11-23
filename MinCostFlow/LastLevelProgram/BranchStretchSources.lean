module

public import MinCostFlow.LastLevelProgram.RepresentativeGraph
public import MinCostFlow.LastLevelProgram.IndexGraph
public import MinCostFlow.MinRatio.Layouts
public import WordRAM.CopyWords
import WordRAM.Tactic

/-!
# Reading a round's stretches by original edge name

Definition 5.8 (pages 19–20) lifts the representative tree to the input
graph. Each parallel edge uses its representative's stretch. Loops
receive one, as in the fixed-point last-level model.
-/

public section

namespace MinCostFlow.LastLevelProgram

open SparseCore Num MinRatio WordRAM

/-- If the named table has the copied representative blocks and unit
loop blocks, it encodes the branch's stretch numerator table. -/
theorem branchStretch_edgeValuesAt
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (j h L P base : ℕ) (mem : ℕ → ℕ)
    (hnl : (nonLoopEdges G).Nonempty) :
    let H := representativeGraph G ℓ
    let prec := weightPrecision C H
    let query := stretchQuery oracle H ℓ prec
    let v := weights prec (roundedScale C H) query j
    (∀ e ∈ nonLoopEdges G, Valid mem (base + e * L) h L ∧
      fixVal mem (base + e * L) h L P = query v (shortestEdge G ℓ (edgePairKey G e))) →
    (∀ e ∈ G.E, e ∉ nonLoopEdges G → Valid mem (base + e * L) h L ∧
      fixVal mem (base + e * L) h L P = 1) →
    EdgeValuesAt mem base h L P G.E ((fixedPointLastLevelTool oracle C).build G ℓ |>.2 j).wstr := by
  intro H prec query v hRep hLoop e he
  by_cases hl : e ∈ nonLoopEdges G
  · simpa only [fixedPointLastLevelTool, hnl, hl, dite_eq_left, ite_eq_left] using hRep e hl
  · simpa only [fixedPointLastLevelTool, hnl, hl, dite_eq_left, ite_eq_right, ite_true, ite_false] using hLoop e he hl

/-- The source of a copied non-loop stretch is a live compact block. -/
theorem branchStretch_representativeIndex {G : MGraph} (ℓ : ℕ → ℝ) {e : ℕ}
    (he : e ∈ nonLoopEdges G) :
    let H := representativeGraph G ℓ
    let f := shortestEdge G ℓ (edgePairKey G e)
    edgeIndex H f < H.m ∧ edgeName H (edgeIndex H f) = f :=
  edgeIndex_live (representativeGraph_shortest (ℓ := ℓ) he).1

/-- Copy one strided compact stretch block to a slot indexed by the
original edge name. Arguments are source, stride, compact index,
destination base, original edge name, and limb count. -/
@[expose] def copyBranchStretchBody (copy : ℕ) : Stmt :=
  .seq (.call 6 copy
    [.bin .add (.reg 0) (.bin .mul (.reg 2) (.reg 1)),
     .bin .add (.reg 3) (.bin .mul (.reg 4) (.reg 5)), .reg 5])
    (.ret (.const 0))

/-- A block copy preserves the decoded stretch and frames all other slots. -/
theorem copyBranchStretch_runs {w h P copy : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp : p.HasAt copy [copyWords]) (mem : ℕ → ℕ)
    (pos src stride i dst e L : ℕ)
    (hwords : ∀ a ∈ [src,stride,i,dst,e,L], a < 2^w)
    (hw : 1 < 2^w) (hsrc : src+i*stride+L ≤ dst)
    (hroom : dst+e*L+L < 2^w) (hvalid : Valid mem (src+i*stride) h L) :
    ∃ o out cost, Runs w p ω (copyBranchStretchBody copy)
      (startState [src,stride,i,dst,e,L] mem pos) o out cost ∧
      (o.value = 0 ∧ Valid out.mem (dst+e*L) h L ∧
        fixVal out.mem (dst+e*L) h L P = fixVal mem (src+i*stride) h L P ∧
        ∀ a, a < dst+e*L ∨ dst+e*L+L ≤ a → out.mem a = mem a) ∧
      cost ≤ 17*L+25 := by
  have hi : i*stride < 2^w := by omega
  have he : e*L < 2^w := by omega
  have ha : src+i*stride < 2^w := by omega
  have hb : dst+e*L < 2^w := by omega
  have hl := hwords L (by simp)
  apply runs_start_le
  unfold copyBranchStretchBody
  refine runs_seq_call_le (copyWords_meetsContract hp)
    (vs := [src+i*stride,dst+e*L,L]) (by eval_expr) ?_ ?_ ?_
  · intro a ha'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha'
    rcases ha' with rfl | rfl | rfl <;> assumption
  · exact ⟨_,_,_,rfl,hw,by omega,by omega,Or.inr (by omega)⟩
  · intro ret out next hp'
    obtain ⟨s,d,k,heq,_,hcopy,hframe⟩ := hp'
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨rfl,rfl,rfl⟩ := heq
    have hv : Valid out (dst+e*L) h L := fun j hj => (hcopy j hj).trans_lt (hvalid j hj)
    have heq : fixVal out (dst+e*L) h L P = fixVal mem (src+i*stride) h L P := by
      unfold fixVal
      rw [intVal_congr hcopy]
      rfl
    refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl,hv,heq,hframe⟩ ?_
    simp [copyWordsContract, Expr.size, argsSize]
    omega

/-- The installed copy has no random instruction. -/
theorem copyBranchStretchBody_noRand (copy : ℕ) : (copyBranchStretchBody copy).NoRand := by
  simp [copyBranchStretchBody, Stmt.NoRand]

/-- The per-edge branch copy reads the representative index and writes
the block at the original edge name. -/
@[expose] def copyBranchStretchContract (w h P : ℕ) : Contract where
  pre args mem := ∃ src stride i dst e L, args = [src,stride,i,dst,e,L] ∧
    1 < 2^w ∧ src+i*stride+L ≤ dst ∧ dst+e*L+L < 2^w ∧ Valid mem (src+i*stride) h L
  post args mem ret out := ∃ src stride i dst e L, args = [src,stride,i,dst,e,L] ∧
    ret = 0 ∧ Valid out (dst+e*L) h L ∧
    fixVal out (dst+e*L) h L P = fixVal mem (src+i*stride) h L P ∧
    ∀ a, a < dst+e*L ∨ dst+e*L+L ≤ a → out a = mem a
  cost args _ := 17 * args.getD 5 0 + 25

/-- The installed copy meets the branch output contract for every tape. -/
theorem copyBranchStretch_meetsContract {w h P entry copy : ℕ} {p : Program}
    (hentry : p.procs[entry]? = some (copyBranchStretchBody copy))
    (hp : p.HasAt copy [copyWords]) :
    MeetsContract w p entry (copyBranchStretchContract w h P) := by
  apply meetsContract_of_runs hentry
  intro args mem pos ω hwords hpre
  obtain ⟨src,stride,i,dst,e,L,rfl,hw,hsrc,hroom,hvalid⟩ := hpre
  obtain ⟨o,out,cost,hr,hpost,hcost⟩ :=
    copyBranchStretch_runs (P := P) (ω := ω) hp mem pos src stride i dst e L
      hwords hw hsrc hroom hvalid
  exact ⟨o,out,cost,hr,⟨src,stride,i,dst,e,L,rfl,hpost⟩,hcost⟩

/-- Read the source and destination indices for a live edge and copy
its stretch. Loop edges can point to a unit block in the source table. -/
@[expose] def scatterBranchStretchArgs : List Expr :=
  [.reg 0, .reg 1, .load (.bin .add (.reg 3) (.reg 7)), .reg 4,
    .load (.bin .add (.reg 2) (.reg 7)), .reg 5]

/-- Iterate over the compact list of original edge names. -/
@[expose] def scatterBranchStretchLoop (entry : ℕ) : Stmt :=
  forRange 7 (.const 0) (.reg 6) (.call 8 entry scatterBranchStretchArgs)

/-- The scatter writes one block per live name. Its index table may
repeat source indices, while destination names are all distinct. -/
theorem scatterBranchStretch_triple {w h P entry : ℕ} {p : Program}
    (hp : MeetsContract w p entry (copyBranchStretchContract w h P))
    (mem : ℕ → ℕ) (pos src stride names indices dst L m cap : ℕ)
    (name index : ℕ → ℕ) (hw : 1 < 2^w) (hL : L < 2^w)
    (hstride : stride < 2^w) (hm : m < 2^w)
    (hn : names + m ≤ dst) (hi : indices + m ≤ dst) (hdst : dst+cap*L < 2^w)
    (hentries : ∀ i < m, mem (names+i) = name i ∧ mem (indices+i) = index i ∧
      name i < cap ∧ name i < 2^w ∧ index i < 2^w ∧ src+index i*stride+L ≤ dst ∧
      Valid mem (src+index i*stride) h L)
    (hdistinct : ∀ i < m, ∀ j < m, name i = name j → i = j) :
    Triple w p (fun st => st = startState [src,stride,names,indices,dst,L,m] mem pos)
      (scatterBranchStretchLoop entry)
      (normalPost fun st =>
        (∀ i < m, Valid st.mem (dst+name i*L) h L ∧
          fixVal st.mem (dst+name i*L) h L P = fixVal mem (src+index i*stride) h L P) ∧
        (∀ a, a < dst ∨ dst+cap*L ≤ a → st.mem a = mem a))
      (fun _ => (17*L+47)*m+7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = src ∧ st.regs 1 = stride ∧ st.regs 2 = names ∧ st.regs 3 = indices ∧
    st.regs 4 = dst ∧ st.regs 5 = L ∧ st.regs 6 = m ∧ st.regs 7 = i ∧
    (∀ j < i, Valid st.mem (dst+name j*L) h L ∧
      fixVal st.mem (dst+name j*L) h L P = fixVal mem (src+index j*stride) h L P) ∧
    (∀ a, a < dst ∨ dst+cap*L ≤ a → st.mem a = mem a)
  have loop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 6)
    (body := .call 8 entry scatterBranchStretchArgs) (Inv := Inv)
    (P := fun st => st = startState [src,stride,names,indices,dst,L,m] mem pos)
    (17*L+38) 0 m (Nat.zero_le _) hw (fun _ => hm)
    (fun st hs => by subst st; exact ⟨by eval_expr, by simp [Inv,startState]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.1)
    (fun _ st _ _ h => by
      have hreg := h.2.2.2.2.2.2.1
      eval_expr)
    (fun i _ hs st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,hdone,hframe⟩ => by
      obtain ⟨hname,hindex,hcap,hnameW,hindexW,hsrc,hvalid⟩ := hentries i hs
      have hni : names+i < dst := by omega
      have hii : indices+i < dst := by omega
      have hread : st.mem (names+i) = name i := (hframe _ (Or.inl hni)).trans hname
      have hread' : st.mem (indices+i) = index i := (hframe _ (Or.inl hii)).trans hindex
      have hroom : dst+name i*L+L < 2^w := by
        have hm' := Nat.mul_le_mul_right L hcap
        rw [Nat.succ_mul] at hm'
        omega
      have hsource (k : ℕ) (hk : k < L) : st.mem (src+index i*stride+k) =
          mem (src+index i*stride+k) := hframe _ (Or.inl (by omega))
      have hhvalid : Valid st.mem (src+index i*stride) h L :=
        fun k hk => (hsource k hk).trans_lt (hvalid k hk)
      have hvalues : ∀ a ∈ [src,stride,index i,dst,name i,L], a < 2^w := by
        intro a ha
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      have ha : evalArgs w st scatterBranchStretchArgs =
          some [src,stride,index i,dst,name i,L] := by
        unfold scatterBranchStretchArgs
        eval_expr
      obtain ⟨out,cost,ret,hr,hpost,_,hregs,hcost⟩ :=
        runs_call_of_meetsContract (r := 8) hp ha hvalues
          ⟨src,stride,index i,dst,name i,L,rfl,hw,hsrc,hroom,hhvalid⟩ ω
      obtain ⟨s,t,j,d,e,k,heq,_,hv,hval,hf⟩ := hpost
      simp only [List.cons.injEq,and_true] at heq
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
      have hDecoded : fixVal st.mem (src+index i*stride) h L P =
          fixVal mem (src+index i*stride) h L P := by
        unfold fixVal
        rw [intVal_congr hsource]
      refine ⟨.normal,out,cost,hr,⟨⟨(hregs 0 (by decide)).trans h0,
        (hregs 1 (by decide)).trans h1,(hregs 2 (by decide)).trans h2,
        (hregs 3 (by decide)).trans h3,(hregs 4 (by decide)).trans h4,
        (hregs 5 (by decide)).trans h5,(hregs 6 (by decide)).trans h6,by simp,?_,?_⟩,
        (hregs 7 (by decide)).trans h7⟩,?_⟩
      · intro j hj
        by_cases he : j = i
        · subst j
          exact ⟨hv,hval.trans hDecoded⟩
        · have hj' : j < i := by omega
          have hne : name j ≠ name i := fun he' => he (hdistinct j (hj'.trans hs) i hs he')
          have hblock (k : ℕ) (hk : k < L) :
              out.mem (dst+name j*L+k) = st.mem (dst+name j*L+k) := by
            apply hf
            rcases lt_or_gt_of_ne hne with hjn | hin
            · have hmul := Nat.mul_le_mul_right L hjn
              rw [Nat.succ_mul] at hmul
              exact Or.inl (by omega)
            · have hmul := Nat.mul_le_mul_right L hin
              rw [Nat.succ_mul] at hmul
              exact Or.inr (by omega)
          obtain ⟨hjv,hjval⟩ := hdone j hj'
          refine ⟨fun k hk => (hblock k hk).trans_lt (hjv k hk),?_⟩
          unfold fixVal
          rw [intVal_congr hblock]
          exact hjval
      · intro a ha
        have hlim := Nat.mul_le_mul_right L hcap
        rw [Nat.succ_mul] at hlim
        exact (hf a (ha.imp (by omega) (by omega))).trans (hframe a ha)
      · change cost ≤ 17*L+38
        simp [copyBranchStretchContract, scatterBranchStretchArgs, argsSize, Expr.size] at hcost
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st hp
    cases o with
    | returned => exact hp
    | normal => exact hp.2.2.2.2.2.2.2.2
  · intro _ _
    simp [Expr.size_const, Expr.size_reg, Nat.mul_comm]

/-- Compact source index for each original edge. The index after the
representative array is reserved for the unit stretch used on loops. -/
noncomputable def branchStretchIndex (G : MGraph) (ℓ : ℕ → ℝ) (e : ℕ) : ℕ :=
  open Classical in
  let H := representativeGraph G ℓ
  if e ∈ nonLoopEdges G then edgeIndex H (shortestEdge G ℓ (edgePairKey G e)) else H.m

/-- Every source index is within the representative array plus its unit slot. -/
theorem branchStretchIndex_le (G : MGraph) (ℓ : ℕ → ℝ) (e : ℕ) :
    branchStretchIndex G ℓ e ≤ (representativeGraph G ℓ).m := by
  classical
  by_cases he : e ∈ nonLoopEdges G
  · rw [branchStretchIndex, ite_eq_left he]
    exact (branchStretch_representativeIndex ℓ he).1.le
  · simp [branchStretchIndex, he]

/-- A scan can recover the compact stretch index by comparing endpoint
pairs. Loops use the sentinel and never match a representative. -/
theorem branchStretchIndex_eq_of_key {G : MGraph} (ℓ : ℕ → ℝ) {e i : ℕ}
    (he : e ∈ G.E) (hi : i < (representativeGraph G ℓ).m)
    (hkey : edgePairKey G (edgeName (representativeGraph G ℓ) i) = edgePairKey G e) :
    branchStretchIndex G ℓ e = i := by
  classical
  let H := representativeGraph G ℓ
  have hrep := representative_mem (edgeName_mem (G := H) hi)
  have hne : G.tail e ≠ G.head e := by
    intro heq
    have hdiag : (edgePairKey G e).1 = (edgePairKey G e).2 := by
      simp [edgePairKey, heq]
    have hn : G.tail (edgeName H i) ≠ G.head (edgeName H i) :=
      (Finset.mem_filter.mp hrep.1).2
    have hh := congrArg Prod.fst hkey
    have ht := congrArg Prod.snd hkey
    unfold edgePairKey at hh ht
    change min (G.tail (edgeName H i)) (G.head (edgeName H i)) = _ at hh
    change max (G.tail (edgeName H i)) (G.head (edgeName H i)) = _ at ht
    have hsame : min (G.tail (edgeName H i)) (G.head (edgeName H i)) =
        max (G.tail (edgeName H i)) (G.head (edgeName H i)) := hh.trans (hdiag.trans ht.symm)
    omega
  have hnl : e ∈ nonLoopEdges G := Finset.mem_filter.mpr ⟨he,hne⟩
  obtain ⟨hf,hfkey,_⟩ := representativeGraph_shortest (ℓ := ℓ) hnl
  have heq := representativeGraph_edge_eq_of_key (edgeName_mem (G := H) hi) hf
    (hkey.trans hfkey.symm)
  rw [branchStretchIndex, ite_eq_left hnl, ← heq, edgeIndex_name hi]

/-- The quotients of the sortable edge keys are the class identifiers
used by the stretch-source scan. A match occurs at exactly the model
index. On loops no compact index matches. -/
theorem branchStretchIndex_key_iff {G : MGraph} (ℓ : ℕ → ℝ)
    {vCap eCap e i : ℕ} (he : e ∈ G.E) (hi : i < (representativeGraph G ℓ).m)
    (hG : G.IsValid) (hvc : ∀ v ∈ G.V, v < vCap) (hec : ∀ e ∈ G.E, e < eCap) :
    let f := edgeName (representativeGraph G ℓ) i
    representativeSortKey G vCap eCap f / eCap =
      representativeSortKey G vCap eCap e / eCap ↔ branchStretchIndex G ℓ e = i := by
  intro f
  have hf := (representativeGraph_subgraph hG ℓ).2.1 (edgeName_mem hi)
  have hv (a : ℕ) (ha : a ∈ G.E) : (edgePairKey G a).2 < vCap := by
    obtain ⟨ht,hh⟩ := hG a ha
    exact max_lt (hvc _ ht) (hvc _ hh)
  constructor
  · intro h
    have hpair := congrArg (fun k : ℕ => (k / vCap,k % vCap)) h
    rw [(representativeSortKey_decode G vCap eCap f (hec f hf) (hv f hf)).2,
      (representativeSortKey_decode G vCap eCap e (hec e he) (hv e he)).2] at hpair
    exact branchStretchIndex_eq_of_key ℓ he hi hpair
  · intro h
    classical
    by_cases hn : e ∈ nonLoopEdges G
    · rw [branchStretchIndex,ite_eq_left hn] at h
      have hname := (branchStretch_representativeIndex ℓ hn).2
      rw [h] at hname
      change f = _ at hname
      have hpair := (representativeGraph_shortest (ℓ := ℓ) hn).2.1
      have hpair' : edgePairKey G f = edgePairKey G e := hname ▸ hpair
      simp only [representativeSortKey,hpair']
      have hp : 0 < eCap := Nat.zero_lt_of_lt (hec e he)
      rw [Nat.add_div hp,Nat.add_div hp]
      simp [Nat.mod_eq_of_lt (hec f hf),Nat.mod_eq_of_lt (hec e he),
        Nat.div_eq_of_lt (hec f hf),Nat.div_eq_of_lt (hec e he),
        (hec f hf).not_ge,(hec e he).not_ge]
    · simp only [branchStretchIndex,ite_eq_right hn] at h
      omega

/-- The scatter postcondition gives the branch's named stretch table
once the compact source contains the representative and unit blocks. -/
theorem branchStretch_edgeValuesAt_of_scatter
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ)
    (G : MGraph) (ℓ : ℕ → ℝ) (j h L P dst : ℕ) (source mem out : ℕ → ℕ)
    (hnl : (nonLoopEdges G).Nonempty) :
    let H := representativeGraph G ℓ
    let prec := weightPrecision C H
    let query := stretchQuery oracle H ℓ prec
    let v := weights prec (roundedScale C H) query j
    (∀ i < H.m, fixVal mem (source i) h L P = query v (edgeName H i)) →
    fixVal mem (source H.m) h L P = 1 →
    (∀ i < G.m, Valid out (dst+edgeName G i*L) h L ∧
      fixVal out (dst+edgeName G i*L) h L P =
        fixVal mem (source (branchStretchIndex G ℓ (edgeName G i))) h L P) →
    EdgeValuesAt out dst h L P G.E ((fixedPointLastLevelTool oracle C).build G ℓ |>.2 j).wstr := by
  intro H prec query v hrep hunit hscatter
  have hNamed (e : ℕ) (he : e ∈ G.E) :
      Valid out (dst+e*L) h L ∧ fixVal out (dst+e*L) h L P =
        fixVal mem (source (branchStretchIndex G ℓ e)) h L P := by
    obtain ⟨hi,hname⟩ := edgeIndex_live he
    simpa only [hname] using hscatter (edgeIndex G e) hi
  apply branchStretch_edgeValuesAt oracle C G ℓ j h L P dst out hnl
  · intro e he
    obtain ⟨hv,hval⟩ := hNamed e (Finset.mem_filter.mp he).1
    obtain ⟨hi,hname⟩ := branchStretch_representativeIndex ℓ he
    refine ⟨hv, hval.trans ?_⟩
    rw [branchStretchIndex, ite_eq_left he]
    rw [hrep _ hi, hname]
  · intro e he hn
    obtain ⟨hv,hval⟩ := hNamed e he
    exact ⟨hv, hval.trans (by simpa only [branchStretchIndex, ite_eq_right hn] using hunit)⟩

/-- The same scatter can use absolute source addresses, with source
base zero and stride one. Loop entries can then read a separate unit
block without taking space in the compact numeric output. -/
theorem scatterBranchStretch_addresses {w h P entry : ℕ} {p : Program}
    (hp : MeetsContract w p entry (copyBranchStretchContract w h P))
    (mem : ℕ → ℕ) (pos names addresses dst L m cap : ℕ)
    (name source : ℕ → ℕ) (hw : 1 < 2^w) (hL : L < 2^w) (hm : m < 2^w)
    (hn : names + m ≤ dst) (ha : addresses + m ≤ dst) (hdst : dst+cap*L < 2^w)
    (hentries : ∀ i < m, mem (names+i) = name i ∧ mem (addresses+i) = source i ∧
      name i < cap ∧ name i < 2^w ∧ source i + L ≤ dst ∧ Valid mem (source i) h L)
    (hdistinct : ∀ i < m, ∀ j < m, name i = name j → i = j) :
    Triple w p (fun st => st = startState [0,1,names,addresses,dst,L,m] mem pos)
      (scatterBranchStretchLoop entry)
      (normalPost fun st =>
        (∀ i < m, Valid st.mem (dst+name i*L) h L ∧
          fixVal st.mem (dst+name i*L) h L P = fixVal mem (source i) h L P) ∧
        (∀ a, a < dst ∨ dst+cap*L ≤ a → st.mem a = mem a))
      (fun _ => (17*L+47)*m+7) := by
  have hslots (i : ℕ) (hi : i < m) :
      mem (names+i) = name i ∧ mem (addresses+i) = source i ∧
        name i < cap ∧ name i < 2^w ∧ source i < 2^w ∧
        0 + source i * 1 + L ≤ dst ∧ Valid mem (0 + source i * 1) h L := by
    obtain ⟨hn, ha, hc, hword, hb, hv⟩ := hentries i hi
    exact ⟨hn, ha, hc, hword, by omega, by simpa using hb, by simpa using hv⟩
  simpa only [Nat.zero_add, Nat.mul_one] using
    scatterBranchStretch_triple hp mem pos 0 1 names addresses dst L m cap
      name source hw hL hw hm hn ha hdst hslots hdistinct

/-- Translate an index to a source address. The sentinel index points
to the separate unit block. The result is written to the address table. -/
@[expose] def writeStretchSourceBody : Stmt :=
  .seq (.cond (.bin .eq (.reg 0) (.reg 1))
    (.store (.reg 5) (.reg 4))
    (.store (.reg 5) (.bin .add (.reg 2) (.bin .mul (.reg 0) (.reg 3)))))
    (.ret (.const 0))

/-- One address-table cell holds the chosen source, with no other writes. -/
theorem writeStretchSource_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos index sentinel src stride unit dst : ℕ)
    (_hword : ∀ a ∈ [index,sentinel,src,stride,unit,dst], a < 2^w)
    (_hw : 1 < 2^w) (_haddr : src+index*stride < 2^w ∨ index = sentinel) :
    ∃ o out cost, Runs w p ω writeStretchSourceBody
      (startState [index,sentinel,src,stride,unit,dst] mem pos) o out cost ∧
      (o.value = 0 ∧ out.mem = Function.update mem dst
        (if index = sentinel then unit else src+index*stride)) ∧ cost ≤ 24 := by
  apply runs_start_le
  unfold writeStretchSourceBody
  by_cases he : index = sentinel
  · subst sentinel
    wram_run
    · simp
      exact ⟨rfl,rfl⟩
    · wram_cost
  · have hh := _haddr.resolve_right he
    have hm : index*stride < 2^w := by omega
    wram_run
    · simp [he]
      exact ⟨rfl,rfl⟩
    · wram_cost

/-- The source translation writes only its destination cell. -/
@[expose] def writeStretchSourceContract (w : ℕ) : Contract where
  pre args _ := ∃ index sentinel src stride unit dst,
    args = [index,sentinel,src,stride,unit,dst] ∧
    1 < 2^w ∧ (src+index*stride < 2^w ∨ index = sentinel)
  post args mem ret out := ∃ index sentinel src stride unit dst,
    args = [index,sentinel,src,stride,unit,dst] ∧ ret = 0 ∧
    out = Function.update mem dst (if index = sentinel then unit else src+index*stride)
  cost _ _ := 24

/-- Install the source translation as a deterministic procedure. -/
theorem writeStretchSource_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.procs[entry]? = some writeStretchSourceBody) :
    MeetsContract w p entry (writeStretchSourceContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω words pre
  obtain ⟨index,sentinel,src,stride,unit,dst,rfl,hw,ha⟩ := pre
  obtain ⟨o,out,cost,hr,hpost,hcost⟩ :=
    writeStretchSource_runs (ω := ω) mem pos index sentinel src stride unit dst words hw ha
  exact ⟨o,out,cost,hr,⟨index,sentinel,src,stride,unit,dst,rfl,hpost⟩,hcost⟩

/-- Registers zero through six hold the index table, sentinel, compact
source base, stride, unit block, destination table, and live edge count. -/
@[expose] def stretchSourceArgs : List Expr :=
  [.load (.bin .add (.reg 0) (.reg 7)), .reg 1, .reg 2, .reg 3, .reg 4,
    .bin .add (.reg 5) (.reg 7)]

/-- Translate every live edge's source index in linear time. -/
@[expose] def stretchSourceLoop (entry : ℕ) : Stmt :=
  forRange 7 (.const 0) (.reg 6) (.call 8 entry stretchSourceArgs)

/-- Translate all the source indices and preserve memory outside the
address table. The cost is constant per live edge. -/
theorem stretchSourceLoop_triple {w entry : ℕ} {p : Program}
    (hp : MeetsContract w p entry (writeStretchSourceContract w))
    (mem : ℕ → ℕ) (pos indices sentinel src stride unit dst m : ℕ)
    (index : ℕ → ℕ) (hw : 1 < 2^w)
    (hwords : ∀ a ∈ [indices,sentinel,src,stride,unit,dst,m], a < 2^w)
    (hsrc : indices+m ≤ dst) (hroom : dst+m < 2^w)
    (hinput : ∀ i < m, mem (indices+i) = index i ∧ index i < 2^w ∧
      (src+index i*stride < 2^w ∨ index i = sentinel)) :
    Triple w p (fun st => st = startState [indices,sentinel,src,stride,unit,dst,m] mem pos)
      (stretchSourceLoop entry)
      (normalPost fun st =>
        (∀ i < m, st.mem (dst+i) = if index i = sentinel then unit else src+index i*stride) ∧
        (∀ a, a < dst ∨ dst+m ≤ a → st.mem a = mem a))
      (fun _ => 45*m+7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = indices ∧ st.regs 1 = sentinel ∧ st.regs 2 = src ∧ st.regs 3 = stride ∧
    st.regs 4 = unit ∧ st.regs 5 = dst ∧ st.regs 6 = m ∧ st.regs 7 = i ∧
    (∀ j < i, st.mem (dst+j) = if index j = sentinel then unit else src+index j*stride) ∧
    ∀ a, a < dst ∨ dst+i ≤ a → st.mem a = mem a
  have hm := hwords m (by simp)
  have loop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 6)
    (body := .call 8 entry stretchSourceArgs) (Inv := Inv)
    (P := fun st => st = startState [indices,sentinel,src,stride,unit,dst,m] mem pos)
    36 0 m (Nat.zero_le _) hw (fun _ => hm)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [Inv,startState]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.1)
    (fun i st _ _ h => by
      have hreg := h.2.2.2.2.2.2.1
      eval_expr)
    (fun i _ hi st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,hdone,hframe⟩ => by
      obtain ⟨hindex,hidx,ha⟩ := hinput i hi
      have hread : st.mem (indices+i) = index i := (hframe _ (Or.inl (by omega))).trans hindex
      have hsrcW : indices+i < 2^w := by omega
      have hdstW : dst+i < 2^w := by omega
      have heval : evalArgs w st stretchSourceArgs = some [index i,sentinel,src,stride,unit,dst+i] := by
        unfold stretchSourceArgs
        eval_expr
      have hw' : ∀ a ∈ [index i,sentinel,src,stride,unit,dst+i], a < 2^w := by
        intro a hh
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
        rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | exact hwords _ (by simp)
      obtain ⟨out,cost,ret,hr,hpost,_,hregs,hcost⟩ :=
        runs_call_of_meetsContract (r := 8) hp heval hw'
          ⟨index i,sentinel,src,stride,unit,dst+i,rfl,hw,ha⟩ ω
      obtain ⟨x,y,s,t,u,d,he,_,hmem⟩ := hpost
      simp only [List.cons.injEq,and_true] at he
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
      refine ⟨.normal,out,cost,hr,⟨⟨(hregs 0 (by decide)).trans h0,
        (hregs 1 (by decide)).trans h1,(hregs 2 (by decide)).trans h2,
        (hregs 3 (by decide)).trans h3,(hregs 4 (by decide)).trans h4,
        (hregs 5 (by decide)).trans h5,(hregs 6 (by decide)).trans h6,by simp,?_,?_⟩,
        (hregs 7 (by decide)).trans h7⟩,?_⟩
      · intro j hj
        change out.mem (dst+j) = _
        rw [hmem]
        by_cases he : j = i
        · subst j
          exact Function.update_self ..
        · rw [Function.update_of_ne (by omega)]
          exact hdone j (by omega)
      · intro a ha
        change out.mem a = mem a
        rw [hmem, Function.update_of_ne (by omega)]
        exact hframe a (ha.imp_right (by omega))
      · change cost ≤ 36
        simp [writeStretchSourceContract,stretchSourceArgs,argsSize,Expr.size] at hcost
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned => exact h
    | normal => exact h.2.2.2.2.2.2.2.2
  · intro _ _
    simp [Expr.size_const,Expr.size_reg,Nat.mul_comm]

end MinCostFlow.LastLevelProgram
