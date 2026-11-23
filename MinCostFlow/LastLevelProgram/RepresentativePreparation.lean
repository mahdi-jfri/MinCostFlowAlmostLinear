module

public import MinCostFlow.LastLevelProgram.RepresentativeGroups
public import MinCostFlow.DynSpanner.Program.GraphTranslate
public import MinCostFlow.LastLevelProgram.SortNames

/-!
# Representative edge preparation

Definition 5.8 (pages 19–20) uses a simple graph. Decode the sorted
live-edge keys and scan their parallel classes in the caller's format.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num DynSpanner.Program SparseCore Spanner

/-- The sorted key array and the caller's positive lengths determine a
duplicate-free enumeration of the representative graph. -/
theorem representativeSortedScan_runs {w entry g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} (st : State) (ℓ : ℕ → ℝ)
    (src dst lengths L P : ℕ) (edges sorted : List ℕ)
    (hcmp : MeetsContract w p entry (unsignedLessContract w 4))
    (hG : DynGraphAt st.mem g vCap eCap G)
    (hedges : ∀ e, e ∈ edges ↔ e ∈ G.E)
    (hperm : sorted.Perm (edges.map (representativeSortKey G vCap eCap)))
    (hsorted : sorted.Pairwise (· ≤ ·))
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap) (h6 : st.regs 6 = src)
    (h7 : st.regs 7 = sorted.length) (h13 : st.regs 13 = lengths)
    (h14 : st.regs 14 = L) (h16 : st.regs 16 = dst)
    (hkeys : ListAt st.mem src sorted)
    (hw : 1 < 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hs : src+sorted.length < 2^w) (hd : dst+sorted.length < 2^w)
    (hsg : src+sorted.length ≤ dst ∨ dst+sorted.length ≤ src)
    (hdg : g+dynGraphSize vCap eCap ≤ dst ∨ dst+sorted.length ≤ g)
    (hlen : ∀ f ∈ G.E, lengths+f*L+L < 2^w ∧ Valid st.mem (lengths+f*L) 4 L ∧
      (lengths+f*L+L ≤ dst ∨ dst+sorted.length ≤ lengths+f*L))
    (hval : ∀ e ∈ G.E, fixVal st.mem (lengths+e*L) 4 L P = ℓ e ∧ 0 < ℓ e) :
    ∃ out cost names, Runs w p ω (representativeGroupScan entry) st .normal out cost ∧
      ListAt out.mem dst names ∧ names.Nodup ∧
      (∀ e, e ∈ names ↔ e ∈ (representativeGraph G ℓ).E) ∧
      out.regs 17 = names.length ∧
      (∀ a, a < dst ∨ dst+sorted.length ≤ a → out.mem a = st.mem a) ∧
      (∀ r, representativeGroupPreserves r → out.regs r = st.regs r) ∧
      cost ≤ sorted.length*(41*L+57)+58 := by
  obtain ⟨input,hinput,hmap,hord⟩ := representativeSortedKeys_decode edges sorted hperm hsorted
    (fun e he => by
      obtain ⟨hname,hend,_⟩ := representativeLiveKey_bounds hG ((hedges e).mp he) hcap
      exact ⟨hname,hend⟩)
  have hsize : input.length = sorted.length := by
    rw [← hmap,List.length_map]
  have horder e (he : e ∈ G.E) f (hf : f ∈ G.E) :
      unsignedVal st.mem (lengths+e*L) 4 L ≤ unsignedVal st.mem (lengths+f*L) 4 L ↔ ℓ e ≤ ℓ f := by
    obtain ⟨heval,hepos⟩ := hval e he
    obtain ⟨hfval,hfpos⟩ := hval f hf
    simpa only [heval,hfval] using representativeLength_order (P := P)
      (hlen e he).2.1 (hlen f hf).2.1 (by rwa [heval]) (by rwa [hfval])
  simpa only [hsize] using representativeGroupScan_enumerates (ω := ω) st ℓ src dst lengths L
    input hcmp hG (fun e => hinput.mem_iff.trans (hedges e)) hord
    h4 h5 h6 (h7.trans hsize.symm) h13 h14 h16 (by rwa [hmap]) hw hcap
    (by rwa [hsize]) (by rwa [hsize]) (by rwa [hsize]) (by rwa [hsize])
    (by simpa only [hsize] using hlen) horder

/-- Sort the encoded keys and write the canonical representative names. -/
@[expose] def representativeSortAndScan (sort cmp : ℕ) : Stmt :=
  .seq (representativeKeySort sort) (representativeGroupScan cmp)

/-- The sorter and class scan preserve the graph and the caller's length
blocks. Their writes are confined to the three work arrays. -/
theorem representativeSortAndScan_runs {w sort cmp g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} (st : State) (ℓ : ℕ → ℝ)
    (src scratch dst lengths L P : ℕ) (edges : List ℕ)
    (hsort : MeetsContract w p sort (mergeSortContract w
      (edges.map (representativeSortKey G vCap eCap))))
    (hcmp : MeetsContract w p cmp (unsignedLessContract w 4))
    (hG : DynGraphAt st.mem g vCap eCap G)
    (hedges : ∀ e, e ∈ edges ↔ e ∈ G.E)
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap) (h6 : st.regs 6 = src)
    (h7 : st.regs 7 = edges.length) (h10 : st.regs 10 = scratch)
    (h13 : st.regs 13 = lengths) (h14 : st.regs 14 = L) (h16 : st.regs 16 = dst)
    (hkeys : ListAt st.mem src (edges.map (representativeSortKey G vCap eCap)))
    (hw : 16 ≤ 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hs : src+edges.length < 2^w) (ht : scratch+edges.length < 2^w)
    (hd : dst+edges.length < 2^w)
    (hst : src+edges.length ≤ scratch ∨ scratch+edges.length ≤ src)
    (hsd : src+edges.length ≤ dst ∨ dst+edges.length ≤ src)
    (hsg : g+dynGraphSize vCap eCap ≤ src ∨ src+edges.length ≤ g)
    (htg : g+dynGraphSize vCap eCap ≤ scratch ∨ scratch+edges.length ≤ g)
    (hdg : g+dynGraphSize vCap eCap ≤ dst ∨ dst+edges.length ≤ g)
    (hlen : ∀ f ∈ G.E, lengths+f*L+L < 2^w ∧ Valid st.mem (lengths+f*L) 4 L ∧
      (lengths+f*L+L ≤ src ∨ src+edges.length ≤ lengths+f*L) ∧
      (lengths+f*L+L ≤ scratch ∨ scratch+edges.length ≤ lengths+f*L) ∧
      (lengths+f*L+L ≤ dst ∨ dst+edges.length ≤ lengths+f*L))
    (hval : ∀ e ∈ G.E, fixVal st.mem (lengths+e*L) 4 L P = ℓ e ∧ 0 < ℓ e) :
    ∃ out cost names, Runs w p ω (representativeSortAndScan sort cmp) st .normal out cost ∧
      ListAt out.mem dst names ∧ names.Nodup ∧
      (∀ e, e ∈ names ↔ e ∈ (representativeGraph G ℓ).E) ∧ out.regs 17 = names.length ∧
      (∀ a, (a < src ∨ src+edges.length ≤ a) →
        (a < scratch ∨ scratch+edges.length ≤ a) →
        (a < dst ∨ dst+edges.length ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, representativeGroupPreserves r → out.regs r = st.regs r) ∧
      cost ≤ 200*edges.length*(Nat.log 2 (edges.length+1)+1)+
        edges.length*(41*L+57)+113 := by
  let keys := edges.map (representativeSortKey G vCap eCap)
  have hklen : keys.length = edges.length := List.length_map _
  have hbound k (hk : k ∈ keys) : k < 2^w := by
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hk
    exact (representativeLiveKey_bounds hG ((hedges e).mp he) hcap).2.2
  obtain ⟨mid,c,sorted,hr,hperm,hordered,hlist,hgraph,hframe,hregs,hcost⟩ :=
    representativeKeySort_runs (ω := ω) st G keys src scratch hsort hG h6
      (h7.trans hklen.symm) h10 hkeys hbound hw (by rwa [hklen]) (by rwa [hklen])
      (by rwa [hklen]) (by rwa [hklen]) (by rwa [hklen])
  have hsize : sorted.length = edges.length := hperm.length_eq.trans hklen
  have hcell f (hf : f ∈ G.E) i (hi : i < L) :
      mid.mem (lengths+f*L+i) = st.mem (lengths+f*L+i) := by
    obtain ⟨_,_,hsep₁,hsep₂,_⟩ := hlen f hf
    apply hframe <;> rw [hklen] <;> omega
  have hlen' f (hf : f ∈ G.E) :
      lengths+f*L+L < 2^w ∧ Valid mid.mem (lengths+f*L) 4 L ∧
        (lengths+f*L+L ≤ dst ∨ dst+sorted.length ≤ lengths+f*L) := by
    obtain ⟨hb,hv,_,_,hsep⟩ := hlen f hf
    exact ⟨hb,fun i hi => (hcell f hf i hi).trans_lt (hv i hi),by rwa [hsize]⟩
  have hval' f (hf : f ∈ G.E) : fixVal mid.mem (lengths+f*L) 4 L P = ℓ f ∧ 0 < ℓ f := by
    unfold fixVal
    rw [intVal_congr (hcell f hf)]
    exact hval f hf
  obtain ⟨out,d,names,hrun,hout,hn,henum,hcount,hframe',hkeep,hcost'⟩ :=
    representativeSortedScan_runs (ω := ω) mid ℓ src dst lengths L P edges sorted
      hcmp hgraph hedges hperm hordered
      ((hregs 4 (by decide)).trans h4) ((hregs 5 (by decide)).trans h5)
      ((hregs 6 (by decide)).trans h6) ((hregs 7 (by decide)).trans (h7.trans hsize.symm))
      ((hregs 13 (by decide)).trans h13) ((hregs 14 (by decide)).trans h14)
      ((hregs 16 (by decide)).trans h16) hlist (by omega) hcap
      (by rwa [hsize]) (by rwa [hsize]) (by rwa [hsize]) (by rwa [hsize]) hlen' hval'
  refine ⟨out,c+d+1,names,runs_seq_iff.mpr (Or.inr ⟨mid,c,d,hr,hrun,rfl⟩),
    hout,hn,henum,hcount,?_,?_,?_⟩
  · intro a hsrc hscratch hdst
    exact (hframe' a (by simpa only [hsize] using hdst)).trans
      (hframe a (by simpa only [hklen] using hsrc) (by simpa only [hklen] using hscratch))
  · intro r hr'
    exact (hkeep r hr').trans (hregs r (by unfold representativeGroupPreserves at hr'; omega))
  · rw [hklen] at hcost
    rw [hsize] at hcost'
    omega

/-- Generate and sort the live-edge keys before scanning their classes. -/
@[expose] def representativePrepareEdges (key sort cmp : ℕ) : Stmt :=
  .seq (representativeKeyScan key) (representativeSortAndScan (sort+sortIdxMergeSort) cmp)

/-- The preparation pass enumerates the representative graph edges from
the original graph and the caller's positive fixed-point lengths. -/
theorem representativePrepareEdges_runs {w key sort cmp g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} (st : State) (ℓ : ℕ → ℝ)
    (src scratch dst lengths L P : ℕ)
    (hkey : MeetsContract w p key (representativeKeyContract w g vCap eCap G))
    (hsort : p.HasAt sort (sortProcs sort))
    (hcmp : MeetsContract w p cmp (unsignedLessContract w 4))
    (hG : DynGraphAt st.mem g vCap eCap G)
    (h0 : st.regs 0 = dgIntToExtBase g vCap)
    (h1 : st.regs 1 = dgETailSlotBase g vCap eCap)
    (h2 : st.regs 2 = dgEHeadSlotBase g vCap eCap)
    (h3 : st.regs 3 = dgEListBase g vCap eCap)
    (hg : g+dynGraphSize vCap eCap < 2^w)
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap) (h6 : st.regs 6 = src)
    (h7 : st.regs 7 = G.m) (h10 : st.regs 10 = scratch)
    (h13 : st.regs 13 = lengths) (h14 : st.regs 14 = L) (h16 : st.regs 16 = dst)
    (hw : 16 ≤ 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hs : src+G.m < 2^w) (ht : scratch+G.m < 2^w)
    (hd : dst+G.m < 2^w)
    (hst : src+G.m ≤ scratch ∨ scratch+G.m ≤ src)
    (hsd : src+G.m ≤ dst ∨ dst+G.m ≤ src)
    (hsg : g+dynGraphSize vCap eCap ≤ src ∨ src+G.m ≤ g)
    (htg : g+dynGraphSize vCap eCap ≤ scratch ∨ scratch+G.m ≤ g)
    (hdg : g+dynGraphSize vCap eCap ≤ dst ∨ dst+G.m ≤ g)
    (hlen : ∀ f ∈ G.E, lengths+f*L+L < 2^w ∧ Valid st.mem (lengths+f*L) 4 L ∧
      (lengths+f*L+L ≤ src ∨ src+G.m ≤ lengths+f*L) ∧
      (lengths+f*L+L ≤ scratch ∨ scratch+G.m ≤ lengths+f*L) ∧
      (lengths+f*L+L ≤ dst ∨ dst+G.m ≤ lengths+f*L))
    (hval : ∀ e ∈ G.E, fixVal st.mem (lengths+e*L) 4 L P = ℓ e ∧ 0 < ℓ e) :
    ∃ out cost names, Runs w p ω (representativePrepareEdges key sort cmp) st .normal out cost ∧
      ListAt out.mem dst names ∧ names.Nodup ∧
      (∀ e, e ∈ names ↔ e ∈ (representativeGraph G ℓ).E) ∧ out.regs 17 = names.length ∧
      (∀ a, (a < src ∨ src+G.m ≤ a) →
        (a < scratch ∨ scratch+G.m ≤ a) →
        (a < dst ∨ dst+G.m ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, representativeGroupPreserves r → out.regs r = st.regs r) ∧
      cost ≤ 200*G.m*(Nat.log 2 (G.m+1)+1)+
        G.m*(41*L+114)+121 := by
  obtain ⟨o,mid,c,hr,hpost,hcost⟩ :=
    (representativeKeyScan_graph_triple st G src hkey hG h0 h1 h2 h3 h4 h5 h6 h7
      (by omega) hg hcap hs hsg).runs ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    obtain ⟨hgraph,⟨edges,hsize,_,hedges,hkeys⟩,hframe,hregs⟩ := hpost
    have hcell f (hf : f ∈ G.E) i (hi : i < L) :
        mid.mem (lengths+f*L+i) = st.mem (lengths+f*L+i) := by
      have hsep := (hlen f hf).2.2.1
      exact hframe _ (by omega)
    have hlen' f (hf : f ∈ G.E) :
        lengths+f*L+L < 2^w ∧ Valid mid.mem (lengths+f*L) 4 L ∧
        (lengths+f*L+L ≤ src ∨ src+edges.length ≤ lengths+f*L) ∧
        (lengths+f*L+L ≤ scratch ∨ scratch+edges.length ≤ lengths+f*L) ∧
        (lengths+f*L+L ≤ dst ∨ dst+edges.length ≤ lengths+f*L) := by
      obtain ⟨hb,hv,hsep⟩ := hlen f hf
      exact ⟨hb,fun i hi => (hcell f hf i hi).trans_lt (hv i hi),by rwa [hsize]⟩
    have hval' f (hf : f ∈ G.E) : fixVal mid.mem (lengths+f*L) 4 L P = ℓ f ∧ 0 < ℓ f := by
      unfold fixVal
      rw [intVal_congr (hcell f hf)]
      exact hval f hf
    obtain ⟨out,d,names,hrun,hout,hn,hmem,hcount,houtside,hkeep,hdcost⟩ :=
      representativeSortAndScan_runs (ω := ω) mid ℓ src scratch dst lengths L P edges
        (mergeSort_meetsContract hsort hsort) hcmp hgraph hedges
        ((hregs 4 (by decide) (by decide)).trans h4)
        ((hregs 5 (by decide) (by decide)).trans h5)
        ((hregs 6 (by decide) (by decide)).trans h6)
        ((hregs 7 (by decide) (by decide)).trans (h7.trans hsize.symm))
        ((hregs 10 (by decide) (by decide)).trans h10)
        ((hregs 13 (by decide) (by decide)).trans h13)
        ((hregs 14 (by decide) (by decide)).trans h14)
        ((hregs 16 (by decide) (by decide)).trans h16)
        hkeys hw hcap (by rwa [hsize]) (by rwa [hsize]) (by rwa [hsize])
        (by rwa [hsize]) (by rwa [hsize]) (by rwa [hsize]) (by rwa [hsize])
        (by rwa [hsize]) hlen' hval'
    refine ⟨out,c+d+1,names,runs_seq_iff.mpr (Or.inr ⟨mid,c,d,hr,hrun,rfl⟩),
      hout,hn,hmem,hcount,?_,?_,?_⟩
    · intro a hsrc hscratch hdst
      rw [hsize] at houtside
      exact (houtside a hsrc hscratch hdst).trans (hframe a hsrc)
    · intro r hr'
      have hp := hr'
      unfold representativeGroupPreserves at hp
      exact (hkeep r hr').trans (hregs r (by omega) (by omega))
    · rw [hsize] at hdcost
      have hm : G.m * (41*L+114) = G.m * (41*L+57) + 57*G.m := by
        rw [show 41*L+114 = (41*L+57)+57 by omega, Nat.mul_add, Nat.mul_comm G.m 57]
      rw [hm]
      omega

/-- List both endpoint names of each retained edge before sorting and deduplication. -/
@[expose] def representativeVertexCandidates (G : MGraph) (edges : List ℕ) : List ℕ :=
  edges.flatMap fun e => [G.tail e,G.head e]

/-- Every retained edge contributes two entries to the vertex work array. -/
theorem representativeVertexCandidates_length (G : MGraph) (edges : List ℕ) :
    (representativeVertexCandidates G edges).length = 2*edges.length := by
  induction edges with
  | nil => simp [representativeVertexCandidates]
  | cons e rest ih =>
    simp only [representativeVertexCandidates,List.flatMap_cons,List.length_append,
      List.length_cons,List.length_nil] at ih ⊢
    omega

/-- Deduplicating the endpoint names gives exactly the representative vertex set. -/
theorem representativeVertexCandidates_mem {G : MGraph} {ℓ : ℕ → ℝ} {edges : List ℕ}
    (h : ∀ e, e ∈ edges ↔ e ∈ (representativeGraph G ℓ).E) (v : ℕ) :
    v ∈ representativeVertexCandidates G edges ↔ v ∈ (representativeGraph G ℓ).V := by
  change v ∈ representativeVertexCandidates G edges ↔
    v ∈ (representativeGraph G ℓ).E.biUnion (fun e => {G.tail e,G.head e})
  simp only [representativeVertexCandidates,List.mem_flatMap,Finset.mem_biUnion,
    List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton,h]

/-- Write the endpoint names of the edge in register 3 to the pair at
index 8 in the vertex work array based at register 20. -/
@[expose] def representativeWriteVertexPair : Stmt :=
  let addr : Expr := .bin .add (.reg 20) (.bin .mul (.const 2) (.reg 8))
  .seq (.store addr (representativeEndpointExpr (.reg 1)))
    (.store (.bin .add addr (.const 1)) (representativeEndpointExpr (.reg 2)))

/-- Writing a pair only changes its two cells. Disjointness from the graph
block keeps the head lookup valid after the tail write. -/
theorem representativeWriteVertexPair_runs {w g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (e dst i : ℕ)
    (hG : DynGraphAt st.mem g vCap eCap G) (he : e ∈ G.E)
    (h0 : st.regs 0 = dgIntToExtBase g vCap) (h1 : st.regs 1 = dgETailSlotBase g vCap eCap)
    (h2 : st.regs 2 = dgEHeadSlotBase g vCap eCap) (h3 : st.regs 3 = e)
    (h8 : st.regs 8 = i) (h20 : st.regs 20 = dst)
    (hg : g+dynGraphSize vCap eCap < 2^w) (hw : 2 < 2^w) (hd : dst+2*i+1 < 2^w)
    (hsep : dst+2*i+1 < g ∨ g+dynGraphSize vCap eCap ≤ dst+2*i) :
    ∃ out, Runs w p ω representativeWriteVertexPair st .normal out 29 ∧
      out.mem = Function.update (Function.update st.mem (dst+2*i) (G.tail e))
        (dst+2*i+1) (G.head e) ∧ out.regs = st.regs := by
  let addr : Expr := .bin .add (.reg 20) (.bin .mul (.const 2) (.reg 8))
  let mid := {st with mem := Function.update st.mem (dst+2*i) (G.tail e)}
  let out := {mid with mem := Function.update mid.mem (dst+2*i+1) (G.head e)}
  have hm : 2*i < 2^w := by omega
  have ha : dst+2*i < 2^w := by omega
  have haddr : addr.eval w st = some (dst+2*i) := by
    simp [addr,Expr.eval,BinOp.eval,h8,h20,hw,hm,ha]
  have ht := (representativeEndpointExpr_eval st G g vCap eCap e hG he h0 h3 h1 h2 hg).1
  have hfirst : Runs w p ω (.store addr (representativeEndpointExpr (.reg 1))) st .normal mid 13 :=
    runs_store_iff.mpr ⟨dst+2*i,G.tail e,haddr,ht,rfl,rfl,rfl⟩
  have hgraph : DynGraphAt mid.mem g vCap eCap G :=
    representativeGraph_frame hG (fun a hlow hhigh => Function.update_of_ne (by omega) ..)
  have hh := (representativeEndpointExpr_eval mid G g vCap eCap e hgraph he h0 h3 h1 h2 hg).2
  have hadr' : (.bin .add addr (.const 1) : Expr).eval w mid = some (dst+2*i+1) := by
    have hone : 1 < 2^w := by omega
    simp [addr,mid,Expr.eval,BinOp.eval,h8,h20,hw,hm,ha,hd,hone]
  have hsecond : Runs w p ω (.store (.bin .add addr (.const 1))
      (representativeEndpointExpr (.reg 2))) mid .normal out 15 :=
    runs_store_iff.mpr ⟨dst+2*i+1,G.head e,hadr',hh,rfl,rfl,rfl⟩
  exact ⟨out,runs_seq_iff.mpr (Or.inr ⟨mid,13,15,hfirst,hsecond,rfl⟩),rfl,rfl⟩

/-- Load the retained edge at the current index and write its vertex pair. -/
@[expose] def representativeVertexStep : Stmt :=
  .seq (.assign 3 (.load (.bin .add (.reg 16) (.reg 8)))) representativeWriteVertexPair

/-- The vertex iteration reads one edge name and writes its two endpoints. -/
theorem representativeVertexStep_runs {w g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (e src dst i : ℕ)
    (hG : DynGraphAt st.mem g vCap eCap G) (he : e ∈ G.E)
    (h0 : st.regs 0 = dgIntToExtBase g vCap) (h1 : st.regs 1 = dgETailSlotBase g vCap eCap)
    (h2 : st.regs 2 = dgEHeadSlotBase g vCap eCap)
    (h8 : st.regs 8 = i) (h16 : st.regs 16 = src) (h20 : st.regs 20 = dst)
    (hread : st.mem (src+i) = e) (hs : src+i < 2^w)
    (hg : g+dynGraphSize vCap eCap < 2^w) (hw : 2 < 2^w) (hd : dst+2*i+1 < 2^w)
    (hsep : dst+2*i+1 < g ∨ g+dynGraphSize vCap eCap ≤ dst+2*i) :
    ∃ out, Runs w p ω representativeVertexStep st .normal out 35 ∧
      out.mem = Function.update (Function.update st.mem (dst+2*i) (G.tail e))
        (dst+2*i+1) (G.head e) ∧ ∀ r, r ≠ 3 → out.regs r = st.regs r := by
  let mid := {st with regs := Function.update st.regs 3 e}
  have hload : Runs w p ω (.assign 3 (.load (.bin .add (.reg 16) (.reg 8)))) st .normal mid 5 :=
    runs_assign_iff.mpr ⟨e,by simp [Expr.eval,BinOp.eval,h16,h8,hs,hread],rfl,rfl,rfl⟩
  obtain ⟨out,hwrites,hm,hregs⟩ := representativeWriteVertexPair_runs (ω := ω) mid G e dst i
    hG he (by simpa [mid] using h0) (by simpa [mid] using h1) (by simpa [mid] using h2)
    (by simp [mid]) (by simpa [mid] using h8) (by simpa [mid] using h20) hg hw hd hsep
  exact ⟨out,runs_seq_iff.mpr (Or.inr ⟨mid,5,29,hload,hwrites,rfl⟩),hm,
    fun r hne => (congrFun hregs r).trans (Function.update_of_ne hne ..)⟩

/-- List the endpoints of every retained edge in the vertex work array. -/
@[expose] def representativeVertexLoop : Stmt :=
  forRange 8 (.const 0) (.reg 17) representativeVertexStep

/-- Consecutive endpoint pairs form the list expected by the word sorter. -/
theorem representativeVertexCandidates_at (G : MGraph) (mem : ℕ → ℕ)
    (edges : List ℕ) (dst : ℕ)
    (hpairs : ∀ j (hj : j < edges.length), mem (dst+2*j) = G.tail edges[j] ∧
      mem (dst+2*j+1) = G.head edges[j]) :
    ListAt mem dst (representativeVertexCandidates G edges) := by
  induction edges generalizing dst with
  | nil =>
    intro j hj
    exact False.elim (Nat.not_lt_zero _ hj)
  | cons e rest ih =>
    rw [representativeVertexCandidates,List.flatMap_cons,listAt_append]
    constructor
    · rw [listAt_cons,listAt_singleton]
      exact hpairs 0 (by simp)
    · apply ih
      intro j hj
      have hout := hpairs (j+1) (by simpa using hj)
      simpa only [List.length_cons,List.length_nil,List.getElem_cons_succ,
        show dst+2*(j+1) = dst+(0+1+1)+2*j by omega] using hout

/-- The endpoint pass writes one pair per retained edge in linear time. -/
theorem representativeVertexLoop_triple {w g vCap eCap : ℕ}
    {p : Program} (initial : State) (G : MGraph) (edges : List ℕ) (src dst : ℕ)
    (hG : DynGraphAt initial.mem g vCap eCap G) (he : ∀ e ∈ edges, e ∈ G.E)
    (h0 : initial.regs 0 = dgIntToExtBase g vCap) (h1 : initial.regs 1 = dgETailSlotBase g vCap eCap)
    (h2 : initial.regs 2 = dgEHeadSlotBase g vCap eCap)
    (h16 : initial.regs 16 = src) (h17 : initial.regs 17 = edges.length)
    (h20 : initial.regs 20 = dst) (hlist : ListAt initial.mem src edges)
    (hg : g+dynGraphSize vCap eCap < 2^w) (hw : 2 < 2^w)
    (hs : src+edges.length < 2^w) (hd : dst+2*edges.length < 2^w)
    (hsrc : src+edges.length ≤ dst ∨ dst+2*edges.length ≤ src)
    (hsep : dst+2*edges.length ≤ g ∨ g+dynGraphSize vCap eCap ≤ dst) :
    Triple w p (fun st => st = initial) representativeVertexLoop
      (normalPost fun st =>
        ListAt st.mem dst (representativeVertexCandidates G edges) ∧
        (∀ a, a < dst ∨ dst+2*edges.length ≤ a → st.mem a = initial.mem a) ∧
        ∀ r, r ≠ 3 → r ≠ 8 → st.regs r = initial.regs r)
      (fun _ => 44*edges.length+7) := by
  let keep (st : State) := ∀ r, r ≠ 3 → r ≠ 8 → st.regs r = initial.regs r
  let frame (st : State) := ∀ a, a < dst ∨ dst+2*edges.length ≤ a → st.mem a = initial.mem a
  let pairs i (st : State) := ∀ j (hj : j < min i edges.length),
    st.mem (dst+2*j) = G.tail edges[j] ∧ st.mem (dst+2*j+1) = G.head edges[j]
  let Inv i (st : State) := st.regs 8 = i ∧ keep st ∧ frame st ∧ pairs i st
  have loop := Triple.forRange_const (p := p) (r := 8) (lo := .const 0) (hi := .reg 17)
    (body := representativeVertexStep) (P := fun st => st = initial) (Inv := Inv)
    35 0 edges.length (Nat.zero_le _) (show 1 < 2^w by omega) (fun _ => by omega)
    (fun st hst => by
      subst st
      refine ⟨by simp [Expr.eval,show 0 < 2^w by omega],by simp,
        fun r _ hr => Function.update_of_ne hr ..,fun _ _ => rfl,?_⟩
      intro j hj
      simp at hj)
    (fun _ _ _ _ h => h.1)
    (fun _ st _ _ h => by simp [Expr.eval,(h.2.1 17 (by decide) (by decide)).trans h17])
    (fun i _ hi => by
      intro st ω ⟨hindex,hkeep,hframe,hpairs⟩
      have hgraph := representativeGraph_frame hG (fun a ha hb => hframe a (by omega))
      obtain ⟨out,hrun,hm,hr⟩ := representativeVertexStep_runs (ω := ω)
        st G edges[i] src dst i hgraph (he _ (List.getElem_mem hi))
        ((hkeep 0 (by decide) (by decide)).trans h0)
        ((hkeep 1 (by decide) (by decide)).trans h1)
        ((hkeep 2 (by decide) (by decide)).trans h2) hindex
        ((hkeep 16 (by decide) (by decide)).trans h16)
        ((hkeep 20 (by decide) (by decide)).trans h20)
        ((hframe _ (by omega)).trans (hlist i hi)) (by omega) hg hw (by omega) (by omega)
      refine ⟨.normal,out,35,hrun,⟨⟨by simp,?_,?_,?_⟩,
        (hr 8 (by decide)).trans hindex⟩,le_rfl⟩
      · intro r hr3 hr8
        exact (Function.update_of_ne hr8 ..).trans ((hr r hr3).trans (hkeep r hr3 hr8))
      · intro a ha
        change out.mem a = initial.mem a
        rw [hm,Function.update_of_ne (show a ≠ dst+2*i+1 by omega),
          Function.update_of_ne (show a ≠ dst+2*i by omega)]
        exact hframe a ha
      · intro j hj
        change out.mem (dst+2*j) = _ ∧ out.mem (dst+2*j+1) = _
        rw [hm]
        by_cases h : j = i
        · subst j
          simp
        · rw [Function.update_of_ne (show dst+2*j ≠ dst+2*i+1 by omega),
            Function.update_of_ne (show dst+2*j ≠ dst+2*i by omega),
            Function.update_of_ne (show dst+2*j+1 ≠ dst+2*i+1 by omega),
            Function.update_of_ne (show dst+2*j+1 ≠ dst+2*i by omega)]
          exact hpairs j (by omega))
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | normal =>
      exact ⟨representativeVertexCandidates_at G st.mem edges dst
        (fun j hj => h.2.2.2 j (by simpa using hj)),h.2.2.1,h.2.1⟩
    | returned _ => exact h
  · intro _ _
    simp [Expr.size_const,Expr.size_reg,Nat.mul_comm]

/-- Sort and deduplicate the endpoint array into the canonical vertex names. -/
@[expose] def representativeSortVertices (entry : ℕ) : Stmt :=
  .call 72 entry [.reg 20,.bin .mul (.const 2) (.reg 17),.reg 21,.reg 22]

/-- The shared sorter yields the canonical vertex list and its count. -/
theorem representativeSortVertices_runs {w entry : ℕ} {p : Program} {ω : ℕ → Bool}
    {G : MGraph} (st : State) (ℓ : ℕ → ℝ) (edges : List ℕ) (src dst scratch : ℕ)
    (hc : MeetsContract w p entry
      (gtSortDedupContract w (representativeVertexCandidates G edges) (representativeGraph G ℓ).V))
    (henum : ∀ e, e ∈ edges ↔ e ∈ (representativeGraph G ℓ).E)
    (h17 : st.regs 17 = edges.length) (h20 : st.regs 20 = src)
    (h21 : st.regs 21 = dst) (h22 : st.regs 22 = scratch)
    (hlist : ListAt st.mem src (representativeVertexCandidates G edges))
    (hw : 16 ≤ 2^w) (hs : src+2*edges.length < 2^w) (hd : dst+2*edges.length < 2^w)
    (ht : scratch+2*edges.length < 2^w)
    (hst : src+2*edges.length ≤ scratch ∨ scratch+2*edges.length ≤ src)
    (hsd : src+2*edges.length ≤ dst ∨ dst+2*edges.length ≤ src)
    (hwords : ∀ v ∈ (representativeGraph G ℓ).V, v < 2^w) :
    ∃ out cost, Runs w p ω (representativeSortVertices entry) st .normal out cost ∧
      ListAt out.mem dst (representativeGraph G ℓ).V.sort ∧
      out.regs 72 = (representativeGraph G ℓ).n ∧
      (∀ a, (a < src ∨ src+2*edges.length ≤ a) →
        (a < scratch ∨ scratch+2*edges.length ≤ a) →
        (a < dst ∨ dst+(representativeGraph G ℓ).n ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 72 → out.regs r = st.regs r) ∧
      cost ≤ 250*(2*edges.length)*(Nat.log 2 (2*edges.length+1)+1)+127 := by
  let names := representativeVertexCandidates G edges
  have hn : names.length = 2*edges.length := representativeVertexCandidates_length G edges
  have ha : evalArgs w st [.reg 20,.bin .mul (.const 2) (.reg 17),.reg 21,.reg 22] =
      some [src,names.length,dst,scratch] := by
    have htwo : 2 < 2^w := by omega
    have hfit : 2*edges.length < 2^w := by omega
    simp [evalArgs,Expr.eval,BinOp.eval,h17,h20,h21,h22,htwo,hfit,hn]
  have harg : ∀ a ∈ [src,names.length,dst,scratch], a < 2^w := by
    intro a ha'
    simp only [List.mem_cons,List.not_mem_nil,or_false,hn] at ha'
    rcases ha' with rfl|rfl|rfl|rfl <;> omega
  obtain ⟨out,c,ret,hr,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 72) hc ha harg
      ⟨src,dst,scratch,rfl,hw,by rwa [hn],by rwa [hn],by rwa [hn],by rwa [hn],by rwa [hn],
        hlist,fun v hv => hwords v ((representativeVertexCandidates_mem henum v).mp hv),
        representativeVertexCandidates_mem henum⟩ ω
  obtain ⟨s,d,t,he,hnum,hout,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,_,rfl,rfl⟩ := he
  have hvlen : (vertsOf (representativeGraph G ℓ).V).length = (representativeGraph G ℓ).n := by
    simp [vertsOf,MGraph.n]
  change c ≤ 6 + (250*names.length*(Nat.log 2 (names.length+1)+1)+120) + 1 at hcost
  refine ⟨out,c,hr,hout,hret.trans (hnum.trans hvlen),?_,hregs,?_⟩
  · simpa only [representativeVertexCandidates_length,hvlen] using hframe
  · rw [hn] at hcost
    omega

/-- Build the canonical vertex name array from the retained edge names. -/
@[expose] def representativePrepareVertices (entry : ℕ) : Stmt :=
  .seq representativeVertexLoop (representativeSortVertices entry)

/-- The vertex preparation pass returns the compact name order used by Theorem 2.2. -/
theorem representativePrepareVertices_runs {w entry g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} (st : State) (ℓ : ℕ → ℝ)
    (edges : List ℕ) (edgesAt work names scratch : ℕ)
    (hc : MeetsContract w p entry
      (gtSortDedupContract w (representativeVertexCandidates G edges) (representativeGraph G ℓ).V))
    (hG : DynGraphAt st.mem g vCap eCap G)
    (henum : ∀ e, e ∈ edges ↔ e ∈ (representativeGraph G ℓ).E)
    (h0 : st.regs 0 = dgIntToExtBase g vCap) (h1 : st.regs 1 = dgETailSlotBase g vCap eCap)
    (h2 : st.regs 2 = dgEHeadSlotBase g vCap eCap)
    (h16 : st.regs 16 = edgesAt) (h17 : st.regs 17 = edges.length)
    (h20 : st.regs 20 = work) (h21 : st.regs 21 = names) (h22 : st.regs 22 = scratch)
    (hlist : ListAt st.mem edgesAt edges)
    (hg : g+dynGraphSize vCap eCap < 2^w) (hw : 16 ≤ 2^w)
    (he : edgesAt+edges.length < 2^w) (hs : work+2*edges.length < 2^w)
    (hd : names+2*edges.length < 2^w) (ht : scratch+2*edges.length < 2^w)
    (hes : edgesAt+edges.length ≤ work ∨ work+2*edges.length ≤ edgesAt)
    (hsg : work+2*edges.length ≤ g ∨ g+dynGraphSize vCap eCap ≤ work)
    (hst : work+2*edges.length ≤ scratch ∨ scratch+2*edges.length ≤ work)
    (hsd : work+2*edges.length ≤ names ∨ names+2*edges.length ≤ work) :
    ∃ out cost, Runs w p ω (representativePrepareVertices entry) st .normal out cost ∧
      ListAt out.mem names (representativeGraph G ℓ).V.sort ∧
      out.regs 72 = (representativeGraph G ℓ).n ∧
      (∀ a, (a < work ∨ work+2*edges.length ≤ a) →
        (a < scratch ∨ scratch+2*edges.length ≤ a) →
        (a < names ∨ names+(representativeGraph G ℓ).n ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 3 → r ≠ 8 → r ≠ 72 → out.regs r = st.regs r) ∧
      cost ≤ 250*(2*edges.length)*(Nat.log 2 (2*edges.length+1)+1)+44*edges.length+135 := by
  have hsub := representativeGraph_subgraph hG.1 ℓ
  obtain ⟨o,mid,c,hr,hpost,hcost⟩ := (representativeVertexLoop_triple st G edges edgesAt work hG
    (fun e he' => hsub.2.1 ((henum e).mp he')) h0 h1 h2 h16 h17 h20 hlist hg (by omega)
      he hs hes hsg).runs ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    obtain ⟨harray,hframe,hregs⟩ := hpost
    have hword v (hv : v ∈ (representativeGraph G ℓ).V) : v < 2^w := by
      have hv' := hG.2.1 v (hsub.1 hv)
      unfold dynGraphSize at hg
      omega
    obtain ⟨out,d,hrun,hout,hnum,hframe',hregs',hcost'⟩ :=
      representativeSortVertices_runs (ω := ω) mid ℓ edges work names scratch hc henum
        ((hregs 17 (by decide) (by decide)).trans h17)
        ((hregs 20 (by decide) (by decide)).trans h20)
        ((hregs 21 (by decide) (by decide)).trans h21)
        ((hregs 22 (by decide) (by decide)).trans h22) harray hw hs hd ht hst hsd hword
    exact ⟨out,c+d+1,runs_seq_iff.mpr (Or.inr ⟨mid,c,d,hr,hrun,rfl⟩),hout,hnum,
      fun a ha hb hc' => (hframe' a ha hb hc').trans (hframe a ha),
      fun r hr3 hr8 hr72 => (hregs' r hr72).trans (hregs r hr3 hr8),by omega⟩

/-- Resolve one sorted vertex name to its original graph slot.
Register 23 holds the external-to-internal table base. -/
@[expose] def representativeVertexSlotStep : Stmt :=
  .store (.bin .add (.reg 148) (.reg 8))
    (.load (.bin .add (.reg 23) (.load (.bin .add (.reg 21) (.reg 8)))))

/-- The slot lookup writes only its output cell and preserves registers. -/
theorem representativeVertexSlotStep_runs {w g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} (st : State)
    (src dst i v : ℕ) (hG : DynGraphAt st.mem g vCap eCap G) (hv : v ∈ G.V)
    (h8 : st.regs 8 = i) (h21 : st.regs 21 = src) (h148 : st.regs 148 = dst)
    (h23 : st.regs 23 = dgExtToIntBase g vCap) (hread : st.mem (src+i) = v)
    (hs : src+i < 2^w) (hd : dst+i < 2^w) (hg : g+dynGraphSize vCap eCap < 2^w) :
    ∃ out, Runs w p ω representativeVertexSlotStep st .normal out 11 ∧
      out.mem = Function.update st.mem (dst+i) (st.mem (dgExtToIntBase g vCap+v)) ∧
      out.regs = st.regs := by
  let out := {st with mem := Function.update st.mem (dst+i) (st.mem (dgExtToIntBase g vCap+v))}
  have hvCap := hG.2.1 v hv
  have hword : dgExtToIntBase g vCap+v < 2^w := by
    simp only [dgExtToIntBase,dynGraphSize] at hg ⊢
    omega
  refine ⟨out,runs_store_iff.mpr ⟨dst+i,st.mem (dgExtToIntBase g vCap+v),?_,?_,
    rfl,rfl,rfl⟩,rfl,rfl⟩
  · simp [Expr.eval,BinOp.eval,h148,h8,hd]
  · simp [Expr.eval,BinOp.eval,h23,h21,h8,hs,hread,hword]

/-- Build the original slot array in canonical representative vertex order. -/
@[expose] def representativeVertexSlots : Stmt :=
  forRange 8 (.const 0) (.reg 72) representativeVertexSlotStep

/-- The slot loop provides the source array used by the inverse index pass. -/
theorem representativeVertexSlots_triple {w g vCap eCap : ℕ} {p : Program}
    (initial : State) (G H : MGraph) (src dst : ℕ)
    (hG : DynGraphAt initial.mem g vCap eCap G) (hH : G.IsSubgraph H)
    (h21 : initial.regs 21 = src) (h23 : initial.regs 23 = dgExtToIntBase g vCap)
    (h72 : initial.regs 72 = H.n) (h148 : initial.regs 148 = dst)
    (hlist : ListAt initial.mem src H.V.sort)
    (hw : 1 < 2^w) (hg : g+dynGraphSize vCap eCap < 2^w)
    (hs : src+H.n < 2^w) (hd : dst+H.n < 2^w)
    (hsep : src+H.n ≤ dst ∨ dst+H.n ≤ src)
    (hdis : g+dynGraphSize vCap eCap ≤ dst ∨ dst+H.n ≤ g) :
    Triple w p (fun st => st = initial) representativeVertexSlots
      (normalPost fun st =>
        (∀ j < H.n, st.mem (dst+j) = initial.mem (dgExtToIntBase g vCap+vertexName H j)) ∧
        (∀ a, a < dst ∨ dst+H.n ≤ a → st.mem a = initial.mem a) ∧
        ∀ r, r ≠ 8 → st.regs r = initial.regs r)
      (fun _ => 20*H.n+7) := by
  let frame (st : State) := ∀ a, a < dst ∨ dst+H.n ≤ a → st.mem a = initial.mem a
  let Inv i (st : State) := st.regs 8 = i ∧ (∀ r, r ≠ 8 → st.regs r = initial.regs r) ∧
    frame st ∧ ∀ j < i, st.mem (dst+j) = initial.mem (dgExtToIntBase g vCap+vertexName H j)
  have loop := Triple.forRange_const (p := p) (r := 8) (lo := .const 0) (hi := .reg 72)
    (body := representativeVertexSlotStep) (P := fun st => st = initial) (Inv := Inv)
    11 0 H.n (Nat.zero_le _) hw (fun _ => by omega)
    (fun st h => by
      subst st
      refine ⟨by simp [Expr.eval,show 0 < 2^w by omega],by simp,
        fun _ hr => Function.update_of_ne hr ..,fun _ _ => rfl,
        fun j hj => False.elim (Nat.not_lt_zero j hj)⟩)
    (fun _ _ _ _ h => h.1)
    (fun _ st _ _ h => by simp [Expr.eval,(h.2.1 72 (by decide)).trans h72])
    (fun i _ hi => by
      intro st ω ⟨hindex,hregs,hframe,hwritten⟩
      let v := vertexName H i
      have hv := hH.1 (vertexName_mem hi)
      have hgraph := representativeGraph_frame hG (fun a ha hb => hframe a (by omega))
      have hread := (hframe (src+i) (by omega)).trans (sortedVertexNames_at hlist i hi)
      obtain ⟨out,hr,hm,hrg⟩ := representativeVertexSlotStep_runs (ω := ω)
        st src dst i v hgraph hv hindex ((hregs 21 (by decide)).trans h21)
        ((hregs 148 (by decide)).trans h148) ((hregs 23 (by decide)).trans h23)
        hread (by omega) (by omega) hg
      have hval : st.mem (dgExtToIntBase g vCap+v) = initial.mem (dgExtToIntBase g vCap+v) := by
        have hv' := hG.2.1 v hv
        simp only [dgExtToIntBase,dynGraphSize] at hdis ⊢
        exact hframe _ (by omega)
      refine ⟨.normal,out,11,hr,⟨⟨by simp,?_,?_,?_⟩,(congrFun hrg 8).trans hindex⟩,le_rfl⟩
      · intro r hr'
        exact (Function.update_of_ne hr' ..).trans ((congrFun hrg r).trans (hregs r hr'))
      · intro a ha
        change out.mem a = _
        rw [hm,Function.update_of_ne (show a ≠ dst+i by omega)]
        exact hframe a ha
      · intro j hj
        change out.mem (dst+j) = _
        rw [hm]
        by_cases h : j = i
        · subst j
          rw [Function.update_self]
          exact hval
        · rw [Function.update_of_ne (show dst+j ≠ dst+i by omega)]
          exact hwritten j (by omega))
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | normal => exact ⟨h.2.2.2,h.2.2.1,h.2.1⟩
    | returned _ => exact h
  · intro _ _
    simp [Expr.size_const,Expr.size_reg,Nat.mul_comm]

/-- Prepare canonical vertex names and their internal graph slots. -/
@[expose] def representativePrepareVertexSlots (entry : ℕ) : Stmt :=
  .seq (representativePrepareVertices entry) representativeVertexSlots

/-- The vertex preparation pass supplies the slot list consumed by the inverse index pass. -/
theorem representativePrepareVertexSlots_runs {w entry g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} (st : State) (ℓ : ℕ → ℝ)
    (edges : List ℕ) (edgesAt work names scratch slots : ℕ)
    (hc : MeetsContract w p entry
      (gtSortDedupContract w (representativeVertexCandidates G edges) (representativeGraph G ℓ).V))
    (hG : DynGraphAt st.mem g vCap eCap G)
    (henum : ∀ e, e ∈ edges ↔ e ∈ (representativeGraph G ℓ).E)
    (h0 : st.regs 0 = dgIntToExtBase g vCap) (h1 : st.regs 1 = dgETailSlotBase g vCap eCap)
    (h2 : st.regs 2 = dgEHeadSlotBase g vCap eCap)
    (h16 : st.regs 16 = edgesAt) (h17 : st.regs 17 = edges.length)
    (h20 : st.regs 20 = work) (h21 : st.regs 21 = names) (h22 : st.regs 22 = scratch)
    (h23 : st.regs 23 = dgExtToIntBase g vCap) (h148 : st.regs 148 = slots)
    (hlist : ListAt st.mem edgesAt edges)
    (hg : g+dynGraphSize vCap eCap < 2^w) (hw : 16 ≤ 2^w)
    (he : edgesAt+edges.length < 2^w) (hs : work+2*edges.length < 2^w)
    (hd : names+2*edges.length < 2^w) (ht : scratch+2*edges.length < 2^w)
    (hes : edgesAt+edges.length ≤ work ∨ work+2*edges.length ≤ edgesAt)
    (hsg : work+2*edges.length ≤ g ∨ g+dynGraphSize vCap eCap ≤ work)
    (hst : work+2*edges.length ≤ scratch ∨ scratch+2*edges.length ≤ work)
    (hsd : work+2*edges.length ≤ names ∨ names+2*edges.length ≤ work)
    (hng : names+2*edges.length ≤ g ∨ g+dynGraphSize vCap eCap ≤ names)
    (htg : scratch+2*edges.length ≤ g ∨ g+dynGraphSize vCap eCap ≤ scratch)
    (hslots : slots+(representativeGraph G ℓ).n < 2^w)
    (hnslots : names+(representativeGraph G ℓ).n ≤ slots ∨
      slots+(representativeGraph G ℓ).n ≤ names)
    (hslotg : g+dynGraphSize vCap eCap ≤ slots ∨ slots+(representativeGraph G ℓ).n ≤ g) :
    ∃ out cost, Runs w p ω (representativePrepareVertexSlots entry) st .normal out cost ∧
      ListAt out.mem names (representativeGraph G ℓ).V.sort ∧
      (∀ j < (representativeGraph G ℓ).n, out.mem (slots+j) =
        st.mem (dgExtToIntBase g vCap+vertexName (representativeGraph G ℓ) j)) ∧
      out.regs 72 = (representativeGraph G ℓ).n ∧
      (∀ a, (a < work ∨ work+2*edges.length ≤ a) →
        (a < scratch ∨ scratch+2*edges.length ≤ a) →
        (a < names ∨ names+(representativeGraph G ℓ).n ≤ a) →
        (a < slots ∨ slots+(representativeGraph G ℓ).n ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 3 → r ≠ 8 → r ≠ 72 → out.regs r = st.regs r) ∧
      cost ≤ 250*(2*edges.length)*(Nat.log 2 (2*edges.length+1)+1)+44*edges.length+20*(representativeGraph G ℓ).n+143 := by
  let H := representativeGraph G ℓ
  have hsub := representativeGraph_subgraph hG.1 ℓ
  have hm : edges.length ≥ H.E.card := by
    have heq : edges.toFinset = H.E := by
      ext e
      simpa only [List.mem_toFinset] using henum e
    rw [← heq]
    exact List.toFinset_card_le edges
  have hn : (representativeGraph G ℓ).n ≤ 2*edges.length :=
    (representativeGraph_n_le_twice_m G ℓ).trans (Nat.mul_le_mul_left _ hm)
  obtain ⟨mid,c,hr,hname,hnum,hframe,hregs,hcost⟩ :=
    representativePrepareVertices_runs (ω := ω) st ℓ edges edgesAt work names scratch hc hG henum
      h0 h1 h2 h16 h17 h20 h21 h22 hlist hg hw he hs hd ht hes hsg hst hsd
  have hgraph := representativeGraph_frame hG (fun a ha hb =>
    hframe a (by omega) (by omega) (by omega))
  obtain ⟨o,out,d,hslot,hpost,hdcost⟩ :=
    (representativeVertexSlots_triple mid G H names slots hgraph hsub
      ((hregs 21 (by decide) (by decide) (by decide)).trans h21)
      ((hregs 23 (by decide) (by decide) (by decide)).trans h23) hnum
      ((hregs 148 (by decide) (by decide) (by decide)).trans h148) hname
      (by omega) hg (show names+(representativeGraph G ℓ).n < 2^w by omega) hslots hnslots hslotg).runs ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    obtain ⟨hvalues,hout,hkeep⟩ := hpost
    dsimp only [H] at hn hdcost hvalues hout
    refine ⟨out,c+d+1,runs_seq_iff.mpr (Or.inr ⟨mid,c,d,hr,hslot,rfl⟩),?_,?_,
      (hkeep 72 (by decide)).trans hnum,?_,?_,by omega⟩
    · apply hname.congr
      intro a ha hb
      have hlen : (representativeGraph G ℓ).V.sort.length = (representativeGraph G ℓ).n := Finset.length_sort _
      exact hout a (by omega)
    · intro j hj
      rw [hvalues j hj]
      have hv := hG.2.1 _ (hsub.1 (vertexName_mem hj))
      apply hframe
      all_goals
        simp only [dgExtToIntBase,dynGraphSize] at hsg hng htg ⊢
        omega
    · intro a ha hb hc' hd'
      exact (hout a hd').trans (hframe a ha hb hc')
    · intro r hr3 hr8 hr72
      exact (hkeep r hr8).trans (hregs r hr3 hr8 hr72)

/-- Sort the retained edge names in place for the compact edge index. -/
@[expose] def representativeSortEdgeNames (entry : ℕ) : Stmt :=
  .call 9 entry [.reg 16,.reg 17,.reg 22]

/-- Sorting the duplicate-free representative list writes the canonical edge order. -/
theorem representativeSortEdgeNames_runs {w entry : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (H : MGraph) (edges : List ℕ) (src scratch : ℕ)
    (hc : MeetsContract w p entry (mergeSortContract w edges))
    (hn : edges.Nodup) (he : ∀ e, e ∈ edges ↔ e ∈ H.E)
    (h16 : st.regs 16 = src) (h17 : st.regs 17 = edges.length) (h22 : st.regs 22 = scratch)
    (hlist : ListAt st.mem src edges) (hwords : ∀ e ∈ edges, e < 2^w)
    (hw : 16 ≤ 2^w) (hs : src+edges.length < 2^w) (ht : scratch+edges.length < 2^w)
    (hsep : src+edges.length ≤ scratch ∨ scratch+edges.length ≤ src) :
    ∃ out cost, Runs w p ω (representativeSortEdgeNames entry) st .normal out cost ∧
      ListAt out.mem src H.E.sort ∧
      (∀ i < H.m, out.mem (src+i) = edgeName H i) ∧ out.regs 17 = H.m ∧
      (∀ a, (a < src ∨ src+edges.length ≤ a) →
        (a < scratch ∨ scratch+edges.length ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 9 → out.regs r = st.regs r) ∧
      cost ≤ 200*edges.length*(Nat.log 2 (edges.length+1)+1)+54 := by
  have ha : evalArgs w st [.reg 16,.reg 17,.reg 22] = some [src,edges.length,scratch] := by
    simp [evalArgs,Expr.eval,h16,h17,h22]
  have hargs : ∀ a ∈ [src,edges.length,scratch], a < 2^w := by
    intro a h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> omega
  obtain ⟨out,c,ret,hr,hpost,_,hregs,hcost⟩ := runs_call_of_meetsContract (r := 9)
    hc ha hargs ⟨src,scratch,rfl,hw,hs,ht,hsep,hlist,hwords⟩ ω
  obtain ⟨a,b,sorted,hab,_,hperm,hordered,hout,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at hab
  obtain ⟨rfl,_,rfl⟩ := hab
  have hset : sorted.toFinset = H.E := by
    ext e
    exact List.mem_toFinset.trans (hperm.mem_iff.trans (he e))
  have hsort := (List.toFinset_sort (r := (· ≤ ·)) (hperm.nodup_iff.mpr hn)).2 hordered
  rw [hset] at hsort
  rw [hsort]
  change c ≤ 3 + (200*edges.length*(Nat.log 2 (edges.length+1)+1)+50) + 1 at hcost
  have hlength : edges.length = H.m := by
    have hsorted : H.E.sort.length = H.m := Finset.length_sort _
    rw [hsort] at hsorted
    exact hperm.length_eq.symm.trans hsorted
  exact ⟨out,c,hr,hout,sortedEdgeNames_at (show ListAt out.mem src H.E.sort by rwa [hsort]),
    (hregs 17 (by decide)).trans (h17.trans hlength),hframe,hregs,by omega⟩

/-- Publish the prepared edge name pointer and edge count to the rebuild registers. -/
@[expose] def representativePublishEdgeIndex : Stmt :=
  .seq (.assign 100 (.reg 16)) (.assign 73 (.reg 17))

/-- Publishing the compact edge index preserves both the arrays and the vertex count. -/
theorem representativePublishEdgeIndex_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (names count : ℕ) (h16 : st.regs 16 = names) (h17 : st.regs 17 = count) :
    ∃ out, Runs w p ω representativePublishEdgeIndex st .normal out 5 ∧
      out.mem = st.mem ∧ out.regs 100 = names ∧ out.regs 73 = count ∧
      ∀ r, r ≠ 100 → r ≠ 73 → out.regs r = st.regs r := by
  let mid := {st with regs := Function.update st.regs 100 names}
  let out := {mid with regs := Function.update mid.regs 73 count}
  have hnames : Runs w p ω (.assign 100 (.reg 16)) st .normal mid 2 :=
    runs_assign_iff.mpr ⟨names,congrArg some h16,rfl,rfl,rfl⟩
  have hcount : Runs w p ω (.assign 73 (.reg 17)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨count,by simp [Expr.eval,mid,h17,Function.update_of_ne],rfl,rfl,rfl⟩
  refine ⟨out,runs_seq_iff.mpr (Or.inr ⟨mid,2,2,hnames,hcount,rfl⟩),rfl,?_,?_,?_⟩
  · simp [out,mid,Function.update_of_ne]
  · simp [out]
  · intro r h100 h73
    simp [out,mid,Function.update_of_ne,h100,h73]

/-- Sort the retained edges and publish the compact edge index. -/
@[expose] def representativePrepareEdgeIndex (sort : ℕ) : Stmt :=
  .seq (representativeSortEdgeNames (sort+sortIdxMergeSort)) representativePublishEdgeIndex

/-- The edge index pass supplies the exact compact order expected by endpoint packing. -/
theorem representativePrepareEdgeIndex_runs {w sort : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (H : MGraph) (edges : List ℕ) (src scratch : ℕ)
    (hc : p.HasAt sort (sortProcs sort))
    (hn : edges.Nodup) (he : ∀ e, e ∈ edges ↔ e ∈ H.E)
    (h16 : st.regs 16 = src) (h17 : st.regs 17 = edges.length) (h22 : st.regs 22 = scratch)
    (hlist : ListAt st.mem src edges) (hwords : ∀ e ∈ edges, e < 2^w)
    (hw : 16 ≤ 2^w) (hs : src+edges.length < 2^w) (ht : scratch+edges.length < 2^w)
    (hsep : src+edges.length ≤ scratch ∨ scratch+edges.length ≤ src) :
    ∃ out cost, Runs w p ω (representativePrepareEdgeIndex sort) st .normal out cost ∧
      (∀ i < H.m, out.mem (src+i) = edgeName H i) ∧
      out.regs 100 = src ∧ out.regs 73 = H.m ∧
      (∀ a, (a < src ∨ src+edges.length ≤ a) →
        (a < scratch ∨ scratch+edges.length ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 9 → r ≠ 100 → r ≠ 73 → out.regs r = st.regs r) ∧
      cost ≤ 200*edges.length*(Nat.log 2 (edges.length+1)+1)+60 := by
  obtain ⟨mid,c,hr,_,hindex,hcount,hframe,hregs,hcost⟩ :=
    representativeSortEdgeNames_runs (ω := ω) st H edges src scratch
      (mergeSort_meetsContract hc hc) hn he h16 h17 h22 hlist hwords hw hs ht hsep
  obtain ⟨out,hpub,hm,hptr,hnames,hkeep⟩ := representativePublishEdgeIndex_runs (ω := ω)
    mid src H.m ((hregs 16 (by decide)).trans h16) hcount
  refine ⟨out,c+6,runs_seq_iff.mpr (Or.inr ⟨mid,c,5,hr,hpub,by omega⟩),
    ?_,hptr,hnames,?_,?_,by omega⟩
  · simpa only [hm] using hindex
  · simpa only [hm] using hframe
  · exact fun r h9 h100 h73 => (hkeep r h100 h73).trans (hregs r h9)

/-- The retained edge list has exactly the compact edge count, bounded
by the original live edge count used to allocate its work arrays. -/
theorem representativeEnumeration_size {G : MGraph} {ℓ : ℕ → ℝ} {edges : List ℕ}
    (hG : G.IsValid) (hn : edges.Nodup)
    (he : ∀ e, e ∈ edges ↔ e ∈ (representativeGraph G ℓ).E) :
    edges.length = (representativeGraph G ℓ).m ∧ edges.length ≤ G.m := by
  have hset : edges.toFinset = (representativeGraph G ℓ).E := by
    ext e
    exact List.mem_toFinset.trans (he e)
  have hlen : edges.length = (representativeGraph G ℓ).m := by
    rw [← List.toFinset_card_of_nodup hn,hset]
    rfl
  exact ⟨hlen,hlen.le.trans (Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1)⟩

/-- Prepare the canonical edge and vertex lookup tables for endpoint packing. -/
@[expose] def representativePrepareIndices (vertices sort : ℕ) : Stmt :=
  .seq (representativePrepareVertexSlots vertices) (representativePrepareEdgeIndex sort)

/-- The combined preparation pass supplies the compact edge index and ordered vertex slots. -/
theorem representativePrepareIndices_runs {w entry sort g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} (st : State) (ℓ : ℕ → ℝ)
    (edges : List ℕ) (edgesAt work names scratch slots : ℕ)
    (hc : MeetsContract w p entry
      (gtSortDedupContract w (representativeVertexCandidates G edges) (representativeGraph G ℓ).V))
    (hsort : p.HasAt sort (sortProcs sort)) (hnodup : edges.Nodup)
    (hG : DynGraphAt st.mem g vCap eCap G)
    (henum : ∀ e, e ∈ edges ↔ e ∈ (representativeGraph G ℓ).E)
    (h0 : st.regs 0 = dgIntToExtBase g vCap) (h1 : st.regs 1 = dgETailSlotBase g vCap eCap)
    (h2 : st.regs 2 = dgEHeadSlotBase g vCap eCap)
    (h16 : st.regs 16 = edgesAt) (h17 : st.regs 17 = edges.length)
    (h20 : st.regs 20 = work) (h21 : st.regs 21 = names) (h22 : st.regs 22 = scratch)
    (h23 : st.regs 23 = dgExtToIntBase g vCap) (h148 : st.regs 148 = slots)
    (hlist : ListAt st.mem edgesAt edges)
    (hg : g+dynGraphSize vCap eCap < 2^w) (hw : 16 ≤ 2^w)
    (he : edgesAt+edges.length < 2^w) (hs : work+2*edges.length < 2^w)
    (hd : names+2*edges.length < 2^w) (ht : scratch+2*edges.length < 2^w)
    (hes : edgesAt+edges.length ≤ work ∨ work+2*edges.length ≤ edgesAt)
    (hsg : work+2*edges.length ≤ g ∨ g+dynGraphSize vCap eCap ≤ work)
    (hst : work+2*edges.length ≤ scratch ∨ scratch+2*edges.length ≤ work)
    (hsd : work+2*edges.length ≤ names ∨ names+2*edges.length ≤ work)
    (hng : names+2*edges.length ≤ g ∨ g+dynGraphSize vCap eCap ≤ names)
    (htg : scratch+2*edges.length ≤ g ∨ g+dynGraphSize vCap eCap ≤ scratch)
    (hslots : slots+(representativeGraph G ℓ).n < 2^w)
    (hnslots : names+(representativeGraph G ℓ).n ≤ slots ∨
      slots+(representativeGraph G ℓ).n ≤ names)
    (hslotg : g+dynGraphSize vCap eCap ≤ slots ∨ slots+(representativeGraph G ℓ).n ≤ g)
    (het : edgesAt+edges.length ≤ scratch ∨ scratch+2*edges.length ≤ edgesAt)
    (hen : edgesAt+edges.length ≤ names ∨ names+(representativeGraph G ℓ).n ≤ edgesAt)
    (hns : scratch+edges.length ≤ names ∨ names+(representativeGraph G ℓ).n ≤ scratch)
    (hel : edgesAt+edges.length ≤ slots ∨ slots+(representativeGraph G ℓ).n ≤ edgesAt)
    (htl : scratch+edges.length ≤ slots ∨ slots+(representativeGraph G ℓ).n ≤ scratch) :
    ∃ out cost, Runs w p ω (representativePrepareIndices entry sort) st .normal out cost ∧
      (∀ i < (representativeGraph G ℓ).m,
        out.mem (edgesAt+i) = edgeName (representativeGraph G ℓ) i) ∧
      ListAt out.mem names (representativeGraph G ℓ).V.sort ∧
      out.regs 100 = edgesAt ∧ out.regs 73 = (representativeGraph G ℓ).m ∧
      (∀ j < (representativeGraph G ℓ).n, out.mem (slots+j) =
        st.mem (dgExtToIntBase g vCap+vertexName (representativeGraph G ℓ) j)) ∧
      out.regs 72 = (representativeGraph G ℓ).n ∧
      (∀ a, (a < edgesAt ∨ edgesAt+edges.length ≤ a) →
        (a < work ∨ work+2*edges.length ≤ a) →
        (a < scratch ∨ scratch+2*edges.length ≤ a) →
        (a < names ∨ names+(representativeGraph G ℓ).n ≤ a) →
        (a < slots ∨ slots+(representativeGraph G ℓ).n ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 3 → r ≠ 8 → r ≠ 72 → r ≠ 9 → r ≠ 100 → r ≠ 73 → out.regs r = st.regs r) ∧
      cost ≤ 250*(2*edges.length)*(Nat.log 2 (2*edges.length+1)+1)+44*edges.length+20*(representativeGraph G ℓ).n+
        200*edges.length*(Nat.log 2 (edges.length+1)+1)+204 := by
  obtain ⟨mid,c,hr,hnamesAt,hslotsAt,hcount,hframe,hregs,hcost⟩ :=
    representativePrepareVertexSlots_runs (ω := ω) st ℓ edges edgesAt work names scratch slots
      hc hG henum h0 h1 h2 h16 h17 h20 h21 h22 h23 h148 hlist hg hw he hs hd ht
      hes hsg hst hsd hng htg hslots hnslots hslotg
  have hsub := representativeGraph_subgraph hG.1 ℓ
  have hwords e (he' : e ∈ edges) : e < 2^w := by
    have heb := hG.2.2.1 e (hsub.2.1 ((henum e).mp he'))
    unfold dynGraphSize at hg
    omega
  have hlist' := hlist.congr fun a ha hb =>
    hframe a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨out,d,hrun,hindex,hptr,hm,hframe',hregs',hcost'⟩ :=
    representativePrepareEdgeIndex_runs (ω := ω) mid (representativeGraph G ℓ) edges edgesAt scratch
      hsort hnodup henum ((hregs 16 (by decide) (by decide) (by decide)).trans h16)
      ((hregs 17 (by decide) (by decide) (by decide)).trans h17)
      ((hregs 22 (by decide) (by decide) (by decide)).trans h22)
      hlist' hwords hw he (by omega) (by omega)
  refine ⟨out,c+d+1,runs_seq_iff.mpr (Or.inr ⟨mid,c,d,hr,hrun,rfl⟩),
    hindex,?_,hptr,hm,?_,(hregs' 72 (by decide) (by decide) (by decide)).trans hcount,?_,?_,by omega⟩
  · apply hnamesAt.congr
    intro a ha hb
    rw [Finset.length_sort] at hb
    change a < names+(representativeGraph G ℓ).n at hb
    exact hframe' a (by omega) (by omega)
  · intro j hj
    exact (hframe' _ (by omega) (by omega)).trans (hslotsAt j hj)
  · intro a ha hb hc' hd' he'
    exact (hframe' a ha (by omega)).trans (hframe a hb hc' hd' he')
  · intro r h3 h8 h72 h9 h100 h73
    exact (hregs' r h9 h100 h73).trans (hregs r h3 h8 h72)

end MinCostFlow.LastLevelProgram
