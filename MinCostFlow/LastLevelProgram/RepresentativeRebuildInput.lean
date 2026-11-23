module

public import MinCostFlow.LastLevelProgram.RepresentativePreparation
import WordRAM.Tactic

/-!
# Preparing the compact input for the last-level rebuild

Definition 5.8 (pages 19–20) selects a simple representative graph.
The preparation pass builds the edge index and vertex slots from the
original graph in disjoint consecutive work regions.
-/

public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num DynSpanner.Program SparseCore

/-- Load the caller arguments and reserve the compact-input scratch arrays.
Register 112 keeps the graph pointer while selection uses register 0. -/
@[expose] def representativeRuntimeInput : Stmt :=
  let add := Expr.bin .add
  let mul := Expr.bin .mul
  let atOffset := fun k => Expr.load (add (.reg 0) (.const k))
  .assign 112 (.reg 0) ;;
  .assign 151 (.reg 4) ;;
  .assign 99 (.reg 1) ;;
  .assign 127 (.reg 2) ;;
  .assign 144 (.reg 2) ;;
  .assign 145 (.reg 3) ;;
  .assign 13 (.reg 1) ;;
  .assign 14 (.reg 2) ;;
  .assign 113 (.load (.reg 0)) ;;
  .assign 114 (atOffset 1) ;;
  .assign 115 (atOffset 2) ;;
  .assign 116 (add (add (.reg 0) (.const 4)) (.reg 113)) ;;
  .assign 7 (atOffset 3) ;;
  .assign 133 (.reg 7) ;;
  .assign 6 (.reg 4) ;;
  .assign 4 (.reg 113) ;;
  .assign 5 (.reg 114) ;;
  .assign 10 (add (.reg 6) (.reg 7)) ;;
  .assign 16 (add (.reg 10) (.reg 7)) ;;
  .assign 20 (add (.reg 16) (.reg 7)) ;;
  .assign 22 (add (.reg 20) (mul (.const 2) (.reg 7))) ;;
  .assign 21 (add (.reg 22) (mul (.const 2) (.reg 7))) ;;
  .assign 150 (.reg 21) ;;
  .assign 148 (add (.reg 21) (mul (.const 2) (.reg 7))) ;;
  .assign 146 (add (.reg 148) (mul (.const 2) (.reg 7))) ;;
  .assign 142 (add (.reg 146) (.reg 4)) ;;
  .assign 141 (add (.reg 142) (.const 1)) ;;
  .assign 23 (add (add (.reg 0) (.const 4)) (mul (.const 3) (.reg 4))) ;;
  .assign 3 (add (add (add (.reg 0) (.const 4)) (mul (.const 7) (.reg 4))) (.reg 5)) ;;
  .assign 1 (add (.reg 3) (mul (.const 2) (.reg 5))) ;;
  .assign 2 (add (.reg 1) (.reg 5)) ;;
  .assign 134 (.reg 6) ;;
  .assign 136 (.reg 10) ;;
  .assign 137 (.reg 3) ;;
  .assign 138 (.reg 20) ;;
  .assign 131 (add (.reg 20) (.reg 7)) ;;
  .assign 0 (add (.reg 23) (.reg 4))

/-- The runtime input setup leaves the caller's memory unchanged and
supplies the original graph tables and scratch bases for edge selection. -/
theorem representativeRuntimeInput_runs {w g vCap eCap : ℕ} {p : Program} {ω : ℕ → Bool}
    (G : MGraph) (mem : ℕ → ℕ) (lengths L P heap pos : ℕ)
    (hG : DynGraphAt mem g vCap eCap G) (hw : 16 ≤ 2^w)
    (hg : g+dynGraphSize vCap eCap ≤ heap) (hroom : heap+11*G.m+vCap+1 < 2^w) :
    ∃ o out cost, Runs w p ω representativeRuntimeInput
        (startState [g,lengths,L,P,heap] mem pos) o out cost ∧
      (o = .normal ∧ out.mem = mem ∧
      out.regs 0 = dgIntToExtBase g vCap ∧ out.regs 1 = dgETailSlotBase g vCap eCap ∧
      out.regs 2 = dgEHeadSlotBase g vCap eCap ∧ out.regs 3 = dgEListBase g vCap eCap ∧
      out.regs 4 = vCap ∧ out.regs 5 = eCap ∧ out.regs 6 = heap ∧ out.regs 7 = G.m ∧
      out.regs 10 = heap+G.m ∧ out.regs 13 = lengths ∧ out.regs 14 = L ∧
      out.regs 16 = heap+2*G.m ∧ out.regs 20 = heap+3*G.m ∧
      out.regs 21 = heap+7*G.m ∧ out.regs 22 = heap+5*G.m ∧
      out.regs 23 = dgExtToIntBase g vCap ∧ out.regs 148 = heap+9*G.m ∧
      out.regs 112 = g ∧ out.regs 113 = vCap ∧ out.regs 114 = eCap ∧
      out.regs 99 = lengths ∧ out.regs 127 = L ∧ out.regs 144 = L ∧ out.regs 145 = P ∧
      out.regs 146 = heap+11*G.m ∧ out.regs 142 = heap+11*G.m+vCap ∧
      out.regs 141 = heap+11*G.m+vCap+1 ∧ out.regs 151 = heap ∧ out.regs 150 = heap+7*G.m ∧
      out.regs 115 = G.n ∧ out.regs 116 = dgVListBase g vCap ∧ out.regs 133 = G.m ∧
      out.regs 134 = heap ∧ out.regs 136 = heap+G.m ∧ out.regs 137 = dgEListBase g vCap eCap ∧
      out.regs 138 = heap+3*G.m ∧ out.regs 131 = heap+4*G.m) ∧
      cost ≤ 208 := by
  have hv : mem g = vCap := hG.2.2.2.1
  have he : mem (g+1) = eCap := hG.2.2.2.2.1
  have hn : mem (g+2) = G.n := hG.2.2.2.2.2.1
  have hm : mem (g+3) = G.m := hG.2.2.2.2.2.2.1
  unfold dynGraphSize at hg
  apply runs_start_le
  unfold representativeRuntimeInput
  wram_run
  · simp [startState,dgIntToExtBase,dgETailSlotBase,dgEHeadSlotBase,dgEListBase,dgExtToIntBase,dgVListBase,hn]
    all_goals omega
  · wram_cost

/-- Select representative edges and build the two compact lookup tables. -/
@[expose] def representativeRebuildInput (key sort cmp vertices : ℕ) : Stmt :=
  .seq (representativePrepareEdges key sort cmp)
    (representativePrepareIndices vertices sort)

/-- Preparation starts from the caller's graph and lengths and leaves the
canonical edge lookup and original vertex slots ready for endpoint packing. -/
theorem representativeRebuildInput_runs {w key sort cmp vertices ops g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {G : MGraph} (st : State) (ℓ : ℕ → ℝ)
    (src scratch edgesAt work temp names slots lengths L P : ℕ)
    (hkey : MeetsContract w p key (representativeKeyContract w g vCap eCap G))
    (hsort : p.HasAt sort (sortProcs sort))
    (hcmp : MeetsContract w p cmp (unsignedLessContract w 4))
    (hvertices : p.HasAt vertices (gtProcs sort ops))
    (hG : DynGraphAt st.mem g vCap eCap G)
    (h0 : st.regs 0 = dgIntToExtBase g vCap) (h1 : st.regs 1 = dgETailSlotBase g vCap eCap)
    (h2 : st.regs 2 = dgEHeadSlotBase g vCap eCap) (h3 : st.regs 3 = dgEListBase g vCap eCap)
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap) (h6 : st.regs 6 = src)
    (h7 : st.regs 7 = G.m) (h10 : st.regs 10 = scratch)
    (h13 : st.regs 13 = lengths) (h14 : st.regs 14 = L) (h16 : st.regs 16 = edgesAt)
    (h20 : st.regs 20 = work) (h21 : st.regs 21 = names) (h22 : st.regs 22 = temp)
    (h23 : st.regs 23 = dgExtToIntBase g vCap) (h148 : st.regs 148 = slots)
    (hw : 16 ≤ 2^w) (hcap : vCap*vCap*eCap ≤ 2^w)
    (hg : g+dynGraphSize vCap eCap ≤ src)
    (hs : src+G.m ≤ scratch) (ht : scratch+G.m ≤ edgesAt)
    (he : edgesAt+G.m ≤ work) (hwk : work+2*G.m ≤ temp)
    (htmp : temp+2*G.m ≤ names) (hn : names+2*G.m ≤ slots)
    (hend : slots+2*G.m < 2^w)
    (hlen : ∀ e ∈ G.E, lengths+e*L+L ≤ src ∧ Valid st.mem (lengths+e*L) 4 L ∧
      fixVal st.mem (lengths+e*L) 4 L P = ℓ e ∧ 0 < ℓ e) :
    let H := representativeGraph G ℓ
    ∃ out cost, Runs w p ω (representativeRebuildInput key sort cmp (vertices+gtIdxSortDedup))
        st .normal out cost ∧
      DynGraphAt out.mem g vCap eCap G ∧
      (∀ i < H.m, out.mem (edgesAt+i) = edgeName H i) ∧
      ListAt out.mem names H.V.sort ∧
      (∀ i < H.n, out.mem (slots+i) = out.mem (dgExtToIntBase g vCap+vertexName H i)) ∧
      out.regs 100 = edgesAt ∧ out.regs 73 = H.m ∧ out.regs 72 = H.n ∧
      (∀ a, a < src ∨ slots+2*G.m ≤ a → out.mem a = st.mem a) ∧
      (∀ r, 20 ≤ r → r ≠ 72 → r ≠ 73 → r ≠ 100 → out.regs r = st.regs r) ∧
      cost ≤ 200*G.m*(Nat.log 2 (G.m+1)+1)+G.m*(41*L+114)+
        (250*(2*H.m)*(Nat.log 2 (2*H.m+1)+1)+44*H.m+20*H.n+
          200*H.m*(Nat.log 2 (H.m+1)+1))+326 := by
  have hgfit : g+dynGraphSize vCap eCap < 2^w := by omega
  obtain ⟨mid,c,edges,hr,hlist,hnd,henum,hcount,hframe,hkeep,hcost⟩ :=
    representativePrepareEdges_runs (ω := ω) st ℓ src scratch edgesAt lengths L P
      hkey hsort hcmp hG h0 h1 h2 h3 hgfit h4 h5 h6 h7 h10 h13 h14 h16 hw hcap
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
      (fun e he' => by
        obtain ⟨hb,hv,_,_⟩ := hlen e he'
        exact ⟨by omega,hv,by omega,by omega,by omega⟩)
      (fun e he' => (hlen e he').2.2)
  obtain ⟨hm,hbound⟩ := representativeEnumeration_size hG.1 hnd henum
  have hnb := (representativeGraph_n_le_twice_m G ℓ).trans (Nat.mul_le_mul_left 2 (hm ▸ hbound))
  have hmid : DynGraphAt mid.mem g vCap eCap G :=
    representativeGraph_frame hG (fun a ha hb => hframe a (by omega) (by omega) (by omega))
  have hk r (h : r < 8 ∨ r = 16 ∨ 20 ≤ r) : mid.regs r = st.regs r :=
    hkeep r (by unfold representativeGroupPreserves; omega)
  obtain ⟨out,d,hsortRun,hindex,hnames,hptr,hmedge,hslot,hnvert,hframe',hkeep',hcost'⟩ :=
    representativePrepareIndices_runs (ω := ω) mid ℓ edges edgesAt work names temp slots
      (gtSortDedup_meetsContract hvertices hsort) hsort hnd hmid henum
      ((hk 0 (by omega)).trans h0) ((hk 1 (by omega)).trans h1) ((hk 2 (by omega)).trans h2)
      ((hk 16 (by omega)).trans h16) hcount ((hk 20 (by omega)).trans h20)
      ((hk 21 (by omega)).trans h21) ((hk 22 (by omega)).trans h22)
      ((hk 23 (by omega)).trans h23) ((hk 148 (by omega)).trans h148) hlist hgfit hw
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  have hgraph := representativeGraph_frame hmid (fun a ha hb =>
    hframe' a (by omega) (by omega) (by omega) (by omega) (by omega))
  refine ⟨out,c+d+1,runs_seq_iff.mpr (Or.inr ⟨mid,c,d,hr,hsortRun,rfl⟩),
    hgraph,hindex,hnames,?_,hptr,hmedge,hnvert,?_,?_,?_⟩
  · intro i hi
    rw [hslot i hi]
    have hv := hG.2.1 _ ((representativeGraph_subgraph hG.1 ℓ).1 (vertexName_mem hi))
    symm
    apply hframe'
    all_goals
      simp only [dgExtToIntBase,dynGraphSize] at hg ⊢
      omega
  · intro a ha
    exact (hframe' a (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hframe a (by omega) (by omega) (by omega))
  · intro r hr' h72 h73 h100
    exact (hkeep' r (by omega) (by omega) h72 (by omega) h100 h73).trans (hk r (by omega))
  · rw [hm] at hcost'
    omega

/-- Prepare the representative graph from the runtime arguments, then
restore the original graph pointer for endpoint packing. -/
@[expose] def prepareRuntimeRepresentative (key sort cmp vertices : ℕ) : Stmt :=
  .seq representativeRuntimeInput
    (.seq (representativeRebuildInput key sort cmp vertices) (.assign 0 (.reg 112)))

/-- The compact representative graph and its two lookup tables are ready
after runtime preparation. The scratch writes are confined to the caller heap. -/
theorem prepareRuntimeRepresentative_runs {w key sort cmp vertices ops g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (G : MGraph) (mem : ℕ → ℕ) (ℓ : ℕ → ℝ)
    (lengths L P heap pos : ℕ)
    (hkey : MeetsContract w p key (representativeKeyContract w g vCap eCap G))
    (hsort : p.HasAt sort (sortProcs sort))
    (hcmp : MeetsContract w p cmp (unsignedLessContract w 4))
    (hvertices : p.HasAt vertices (gtProcs sort ops))
    (hG : DynGraphAt mem g vCap eCap G) (hw : 16 ≤ 2^w)
    (hcap : vCap*vCap*eCap ≤ 2^w) (hg : g+dynGraphSize vCap eCap ≤ heap)
    (hroom : heap+11*G.m+vCap+1 < 2^w)
    (hlen : ∀ e ∈ G.E, lengths+e*L+L ≤ heap ∧ Valid mem (lengths+e*L) 4 L ∧
      fixVal mem (lengths+e*L) 4 L P = ℓ e ∧ 0 < ℓ e) :
    let H := representativeGraph G ℓ
    ∃ out cost, Runs w p ω (prepareRuntimeRepresentative key sort cmp (vertices+gtIdxSortDedup))
        (startState [g,lengths,L,P,heap] mem pos) .normal out cost ∧
      DynGraphAt out.mem g vCap eCap G ∧
      (∀ i < H.m, out.mem (heap+2*G.m+i) = edgeName H i) ∧
      ListAt out.mem (heap+7*G.m) H.V.sort ∧
      (∀ i < H.n, out.mem (heap+9*G.m+i) = out.mem (dgExtToIntBase g vCap+vertexName H i)) ∧
      out.regs 0 = g ∧ out.regs 112 = g ∧ out.regs 113 = vCap ∧ out.regs 114 = eCap ∧
      out.regs 148 = heap+9*G.m ∧ out.regs 100 = heap+2*G.m ∧
      out.regs 73 = H.m ∧ out.regs 72 = H.n ∧
      out.regs 99 = lengths ∧ out.regs 127 = L ∧ out.regs 144 = L ∧ out.regs 145 = P ∧
      out.regs 146 = heap+11*G.m ∧ out.regs 142 = heap+11*G.m+vCap ∧
      out.regs 141 = heap+11*G.m+vCap+1 ∧ out.regs 151 = heap ∧ out.regs 150 = heap+7*G.m ∧
      out.regs 115 = G.n ∧ out.regs 116 = dgVListBase g vCap ∧ out.regs 133 = G.m ∧
      out.regs 134 = heap ∧ out.regs 136 = heap+G.m ∧ out.regs 137 = dgEListBase g vCap eCap ∧
      out.regs 138 = heap+3*G.m ∧ out.regs 131 = heap+4*G.m ∧
      (∀ a, a < heap ∨ heap+11*G.m ≤ a → out.mem a = mem a) ∧
      cost ≤ 200*G.m*(Nat.log 2 (G.m+1)+1)+G.m*(41*L+114)+
        (250*(2*H.m)*(Nat.log 2 (2*H.m+1)+1)+44*H.m+20*H.n+
          200*H.m*(Nat.log 2 (H.m+1)+1))+538 := by
  dsimp only
  obtain ⟨o,ready,c,hsetup,⟨rfl,hm,h0,h1,h2,h3,h4,h5,h6,h7,h10,h13,h14,h16,
    h20,h21,h22,h23,h148,h112,h113,h114,h99,h127,h144,h145,h146,h142,h141,h151,h150,h115,h116,h133,h134,h136,h137,h138,h131⟩,hc⟩ :=
    representativeRuntimeInput_runs (ω := ω) G mem lengths L P heap pos hG hw hg hroom
  obtain ⟨mid,d,hr,hgraph,hedges,hnames,hslots,h100,h73,h72,hframe,hkeep,hd⟩ :=
    representativeRebuildInput_runs (ω := ω) ready ℓ heap (heap+G.m) (heap+2*G.m)
      (heap+3*G.m) (heap+5*G.m) (heap+7*G.m) (heap+9*G.m) lengths L P
      hkey hsort hcmp hvertices (hm.symm ▸ hG) h0 h1 h2 h3 h4 h5 h6 h7 h10 h13 h14 h16
      h20 h21 h22 h23 h148 hw hcap hg le_rfl (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (hm.symm ▸ hlen)
  let out := {mid with regs := Function.update mid.regs 0 g}
  have hrestore : Runs w p ω (.assign 0 (.reg 112)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨g,congrArg some ((hkeep 112 (by decide) (by decide) (by decide)
      (by decide)).trans h112),rfl,rfl,rfl⟩
  have hseq := runs_seq_iff.mpr (Or.inr ⟨mid,d,2,hr,hrestore,rfl⟩)
  have preserve (r : ℕ) (hr20 : 20 ≤ r) (hr72 : r ≠ 72) (hr73 : r ≠ 73) (hr100 : r ≠ 100) :
      out.regs r = ready.regs r :=
    (Function.update_of_ne (show r ≠ 0 by omega) g mid.regs).trans
      (hkeep r hr20 hr72 hr73 hr100)
  refine ⟨out,c+(d+2+1)+1,runs_seq_iff.mpr (Or.inr ⟨ready,c,d+2+1,hsetup,hseq,rfl⟩),
    hgraph,hedges,hnames,hslots,by simp [out],
    (preserve 112 (by decide) (by decide) (by decide) (by decide)).trans h112,
    (preserve 113 (by decide) (by decide) (by decide) (by decide)).trans h113,
    (preserve 114 (by decide) (by decide) (by decide) (by decide)).trans h114,
    (preserve 148 (by decide) (by decide) (by decide) (by decide)).trans h148,
    (Function.update_of_ne (show (100 : ℕ) ≠ 0 by decide) g mid.regs).trans h100,
    (Function.update_of_ne (show (73 : ℕ) ≠ 0 by decide) g mid.regs).trans h73,
    (Function.update_of_ne (show (72 : ℕ) ≠ 0 by decide) g mid.regs).trans h72,
    (preserve 99 (by decide) (by decide) (by decide) (by decide)).trans h99,
    (preserve 127 (by decide) (by decide) (by decide) (by decide)).trans h127,
    (preserve 144 (by decide) (by decide) (by decide) (by decide)).trans h144,
    (preserve 145 (by decide) (by decide) (by decide) (by decide)).trans h145,
    (preserve 146 (by decide) (by decide) (by decide) (by decide)).trans h146,
    (preserve 142 (by decide) (by decide) (by decide) (by decide)).trans h142,
    (preserve 141 (by decide) (by decide) (by decide) (by decide)).trans h141,
    (preserve 151 (by decide) (by decide) (by decide) (by decide)).trans h151,
    (preserve 150 (by decide) (by decide) (by decide) (by decide)).trans h150,
    (preserve 115 (by decide) (by decide) (by decide) (by decide)).trans h115,
    (preserve 116 (by decide) (by decide) (by decide) (by decide)).trans h116,
    (preserve 133 (by decide) (by decide) (by decide) (by decide)).trans h133,
    (preserve 134 (by decide) (by decide) (by decide) (by decide)).trans h134,
    (preserve 136 (by decide) (by decide) (by decide) (by decide)).trans h136,
    (preserve 137 (by decide) (by decide) (by decide) (by decide)).trans h137,
    (preserve 138 (by decide) (by decide) (by decide) (by decide)).trans h138,
    (preserve 131 (by decide) (by decide) (by decide) (by decide)).trans h131,
    ?_,by omega⟩
  · intro a ha
    exact (hframe a (by omega)).trans (congrFun hm a)

/-- Cost factor for preparing the compact graph from the caller's edge table. -/
@[expose] def representativeInputMultiplier (L m : ℕ) : ℕ :=
  900*(Nat.log 2 (2*m+1)+1)+41*L+524

/-- The setup budget depends only on caller width and original edge count.
The representative graph has at most two vertices per retained edge. -/
theorem representativeInputCost_le (G : MGraph) (ℓ : ℕ → ℝ) (L : ℕ)
    (hG : G.IsValid) :
    let H := representativeGraph G ℓ
    200*G.m*(Nat.log 2 (G.m+1)+1)+G.m*(41*L+114)+
      (250*(2*H.m)*(Nat.log 2 (2*H.m+1)+1)+44*H.m+20*H.n+
        200*H.m*(Nat.log 2 (H.m+1)+1))+326 ≤
      representativeInputMultiplier L G.m * (G.m+1) := by
  intro H
  have hm : H.m ≤ G.m := Finset.card_le_card (representativeGraph_subgraph hG ℓ).2.1
  have hn : H.n ≤ 2*G.m :=
    (representativeGraph_n_le_twice_m G ℓ).trans (Nat.mul_le_mul_left 2 hm)
  let q := Nat.log 2 (2*G.m+1)+1
  have hq₁ : Nat.log 2 (G.m+1)+1 ≤ q :=
    Nat.succ_le_succ (Nat.log_mono_right (by omega))
  have hq₂ : Nat.log 2 (2*H.m+1)+1 ≤ q :=
    Nat.succ_le_succ (Nat.log_mono_right (by omega))
  have hq₃ : Nat.log 2 (H.m+1)+1 ≤ q :=
    Nat.succ_le_succ (Nat.log_mono_right (by omega))
  have h₁ := Nat.mul_le_mul_left (200*G.m) hq₁
  have h₂ := Nat.mul_le_mul (Nat.mul_le_mul_left 250 (Nat.mul_le_mul_left 2 hm)) hq₂
  have h₃ := Nat.mul_le_mul (Nat.mul_le_mul_left 200 hm) hq₃
  have h₄ := Nat.mul_le_mul_left 44 hm
  have h₅ := Nat.mul_le_mul_left 20 hn
  have hsum : 200*G.m*(Nat.log 2 (G.m+1)+1)+G.m*(41*L+114)+
      (250*(2*H.m)*(Nat.log 2 (2*H.m+1)+1)+44*H.m+20*H.n+
        200*H.m*(Nat.log 2 (H.m+1)+1))+326 ≤
      200*G.m*q+G.m*(41*L+114)+(250*(2*G.m)*q+44*G.m+20*(2*G.m)+200*G.m*q)+326 := by
    omega
  refine hsum.trans ?_
  change _ ≤ (900*q+41*L+524)*(G.m+1)
  calc
    _ = (900*q+41*L+198)*G.m+326 := by ring
    _ ≤ (900*q+41*L+524)*(G.m+1) := by
      rw [Nat.mul_add (900*q+41*L+524) G.m 1, Nat.mul_one]
      exact Nat.add_le_add (Nat.mul_le_mul_right G.m (by omega)) (by omega)

/-- Copy the original edge list into scratch and sort it by name for
the stretch scatter. The graph's own edge list keeps its slot order. -/
@[expose] def prepareOriginalEdgeNames (copy sort : ℕ) : Stmt :=
  .seq (.call 135 copy [.reg 137,.reg 134,.reg 133])
    (.call 135 (sort+sortIdxMergeSort) [.reg 134,.reg 133,.reg 136])

/-- The two calls leave the canonical original edge names in the
destination and preserve memory outside the two work arrays. -/
theorem prepareOriginalEdgeNames_runs {w copy sort : ℕ} {p : Program} {ω : ℕ → Bool}
    (st : State) (G : MGraph) (edges : List ℕ) (src dst scratch : ℕ)
    (hc : MeetsContract w p copy (copyWordsContract w))
    (hs : p.HasAt sort (sortProcs sort))
    (h137 : st.regs 137 = src) (h134 : st.regs 134 = dst)
    (h133 : st.regs 133 = G.m) (h136 : st.regs 136 = scratch)
    (hlen : edges.length = G.m) (hnd : edges.Nodup)
    (hset : ∀ e, e ∈ edges ↔ e ∈ G.E) (hlist : ListAt st.mem src edges)
    (hedges : ∀ e ∈ G.E, e < 2^w) (hw : 16 ≤ 2^w)
    (hsrc : src+G.m ≤ dst) (hdst : dst+G.m ≤ scratch) (hfit : scratch+G.m < 2^w) :
    ∃ out cost, Runs w p ω (prepareOriginalEdgeNames copy sort) st .normal out cost ∧
      (∀ i < G.m, out.mem (dst+i) = edgeName G i) ∧
      (∀ a, a < dst ∨ scratch+G.m ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 135 → out.regs r = st.regs r) ∧
      cost ≤ 200*G.m*(Nat.log 2 (G.m+1)+1)+17*G.m+69 := by
  have ha : evalArgs w st [.reg 137,.reg 134,.reg 133] = some [src,dst,G.m] := by
    simp [evalArgs,Expr.eval,h137,h134,h133]
  have hwords : ∀ x ∈ [src,dst,G.m], x < 2^w := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  obtain ⟨mid,c,ret,hr,hpost,_,hregs,hcCost⟩ :=
    runs_call_of_meetsContract (r := 135) hc ha hwords
      ⟨src,dst,G.m,rfl,by omega,by omega,by omega,Or.inr hsrc⟩ ω
  obtain ⟨s,d,m,he,_,hdata,hcopy⟩ := hpost
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,rfl,rfl⟩ := he
  have hb : evalArgs w mid [.reg 134,.reg 133,.reg 136] = some [dst,edges.length,scratch] := by
    simp [evalArgs,Expr.eval,(hregs 134 (by decide)).trans h134,
      (hregs 133 (by decide)).trans h133,(hregs 136 (by decide)).trans h136,hlen]
  have hwords' : ∀ x ∈ [dst,edges.length,scratch], x < 2^w := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false,hlen] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  obtain ⟨out,k,value,hsort,hpost',_,hkeep,hsCost⟩ :=
    runs_call_of_meetsContract (r := 135) (mergeSort_meetsContract hs hs)
      hb hwords' ⟨dst,scratch,rfl,hw,by omega,by omega,Or.inl (by omega),
        copyWords_listAt hlist hlen hdata,fun e he => hedges e ((hset e).mp he)⟩ ω
  obtain ⟨d,s,sorted,he,_,hperm,horder,hlist',hframe⟩ := hpost'
  simp only [List.cons.injEq,and_true] at he
  obtain ⟨rfl,_,rfl⟩ := he
  have hset' : sorted.toFinset = G.E := by
    ext e
    exact List.mem_toFinset.trans (hperm.mem_iff.trans (hset e))
  have hsorted := (List.toFinset_sort (r := (· ≤ ·)) (hperm.nodup_iff.mpr hnd)).2 horder
  rw [hset'] at hsorted
  change c ≤ 3+(17*G.m+10)+1 at hcCost
  change k ≤ 3+(200*edges.length*(Nat.log 2 (edges.length+1)+1)+50)+1 at hsCost
  rw [hlen] at hsCost
  refine ⟨out,c+k+1,runs_seq_iff.mpr (Or.inr ⟨mid,c,k,hr,hsort,rfl⟩),
    sortedEdgeNames_at (hsorted ▸ hlist'),?_,fun r hn => (hkeep r hn).trans (hregs r hn),by omega⟩
  intro a ha'
  exact (hframe a (by omega) (by omega)).trans (hcopy a (by omega))

end MinCostFlow.LastLevelProgram
