module

public import MinCostFlow.LastLevelProgram.EdgeStretchQuery
import WordRAM.Tactic

/-!
# Querying stretches for packed edges

Read each edge's endpoints from the compact arrays and allocate one
rounded stretch result per edge.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num LSF

/-- The loop keeps the table bases and format in registers zero through nine.
Register ten is the heap cursor and register twelve is the edge index. -/
def stretchRoundArgs : List Expr :=
  [.reg 0,.reg 1,.reg 2,
   .load (.bin .add (.reg 3) (.reg 12)),
   .load (.bin .add (.reg 4) (.reg 12)),
   .reg 5,.reg 6,.bin .add (.reg 7) (.bin .mul (.reg 12) (.reg 8)),
   .reg 8,.reg 9,.reg 10]

/-- Process the packed edges in increasing index order. Register eleven
holds the edge count. -/
def stretchRoundLoop (query : ℕ) : Stmt :=
  forRange 12 (.const 0) (.reg 11) (.call 10 query stretchRoundArgs)

/-- Load the endpoints and the length block address for a single iteration. -/
theorem stretchRoundArgs_eval {w : ℕ} {st : State}
    (base n rows tails heads db dist lengths L P heap i u v : ℕ)
    (h0 : st.regs 0 = base) (h1 : st.regs 1 = n) (h2 : st.regs 2 = rows)
    (h3 : st.regs 3 = tails) (h4 : st.regs 4 = heads) (h5 : st.regs 5 = db)
    (h6 : st.regs 6 = dist) (h7 : st.regs 7 = lengths) (h8 : st.regs 8 = L)
    (h9 : st.regs 9 = P) (h10 : st.regs 10 = heap) (h12 : st.regs 12 = i)
    (hu : st.mem (tails+i) = u) (hv : st.mem (heads+i) = v)
    (htu : tails+i < 2^w) (htv : heads+i < 2^w) (hlen : lengths+i*L < 2^w) :
    evalArgs w st stretchRoundArgs =
      some [base,n,rows,u,v,db,dist,lengths+i*L,L,P,heap] := by
  have hmul : i*L < 2^w := (Nat.le_add_left _ _).trans_lt hlen
  unfold stretchRoundArgs
  eval_expr

/-- Moving the heap cursor past earlier results preserves the next query's
precondition when the input tables and blocks lie below the initial cursor. -/
theorem edgeStretchQuery_pre_frame {w h base n rows u v db dist edge L P heap cur : ℕ}
    {T : MGraph} {r : ℕ} {mem out : ℕ → ℕ}
    (hpre : (edgeStretchQueryContract w h T r).pre
      [base,n,rows,u,v,db,dist,edge,L,P,heap] mem)
    (hat : base+rows*n ≤ heap) (hdt : db+n ≤ heap)
    (hcur : heap ≤ cur) (hroom : cur+edgeStretchSpace L < 2^w)
    (hzero : ZeroFrom out cur) (hf : ∀ a < heap, out a = mem a) :
    (edgeStretchQueryContract w h T r).pre
      [base,n,rows,u,v,db,dist,edge,L,P,cur] out := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,he,hV,hu,hv,hd,ha,hs,_⟩ := hpre
  cases he
  obtain ⟨_,_,_,_,_,_,he,hV',hw,hr,hu',hv',hdep,hdb,hdepth,hbase,htable⟩ := ha
  cases he
  obtain ⟨⟨_,_,_,_,_,_,_,he,huB,hvB,hzB,heB,huV,hvV,hzV,heV,
    hfitU,hfitV,hfitPath,hpos,hfit⟩,_,_⟩ := hs
  cases he
  have hblock (a : ℕ) (hb : a+L ≤ heap) :
      (Valid mem a h L → Valid out a h L) ∧ intVal out a h L = intVal mem a h L := by
    have hc (i : ℕ) (hi : i < L) := hf (a+i) (by omega)
    exact ⟨fun valid i hi => (hc i hi).trans_lt (valid i hi),intVal_congr hc⟩
  obtain ⟨hvu,heu⟩ := hblock _ huB
  obtain ⟨hvv,hev⟩ := hblock _ hvB
  obtain ⟨hvz,hez⟩ := hblock _ hzB
  obtain ⟨hve,hee⟩ := hblock _ heB
  refine ⟨base,n,rows,u,v,db,dist,edge,L,P,cur,rfl,hV,hu,hv,hd,?_,?_,hroom⟩
  · refine ⟨base,n,rows,u,v,db,rfl,hV',hw,hr,hu',hv',hdep,hdb,?_,hbase,?_⟩
    · intro x hx
      rw [hf _ (by omega)]
      exact hdepth x hx
    · intro i hi x hx
      have hmul := Nat.mul_le_mul_right n (show i+1 ≤ rows by omega)
      rw [Nat.succ_mul] at hmul
      rw [hf _ (by omega)]
      exact htable i hi x hx
  · refine ⟨⟨_,_,_,_,L,P,cur,rfl,huB.trans hcur,hvB.trans hcur,hzB.trans hcur,
      heB.trans hcur,hvu huV,hvv hvV,hvz hzV,hve heV,?_,?_,?_,?_,?_⟩,hzero,hroom⟩
    · rwa [heu,hez]
    · rwa [hev,hez]
    · rwa [heu,hev,hez]
    · rwa [hee]
    · rwa [heu,hev,hez,hee]

/-- Earlier outputs below the current heap cursor retain both their
representation and their fixed-point value after another query. -/
theorem edgeStretchQuery_preservesBlock {w h base n rows u v db dist edge L P cur ret a : ℕ}
    {T : MGraph} {r : ℕ} {mem out : ℕ → ℕ}
    (hpost : (edgeStretchQueryContract w h T r).post
      [base,n,rows,u,v,db,dist,edge,L,P,cur] mem ret out)
    (ha : a+L ≤ cur) (hv : Valid mem a h L) :
    Valid out a h L ∧ fixVal out a h L P = fixVal mem a h L P := by
  have hf : ∀ x < cur, out x = mem x := hpost.2.2.2.1
  have he (i : ℕ) (hi : i < L) : out (a+i) = mem (a+i) := hf _ (by omega)
  exact ⟨fun i hi => (he i hi).trans_lt (hv i hi),by rw [fixVal,fixVal,intVal_congr he]⟩

/-- The final block in the space reserved for edge `i`. -/
def roundStretchAddr (heap L i : ℕ) : ℕ :=
  heap+(i+1)*edgeStretchSpace L-L

/-- The numerically rounded stretch for the endpoints indexed by edge `i`. -/
noncomputable def roundStretchValue (mem : ℕ → ℕ) (T : MGraph) (r h L P dist lengths u v i : ℕ) : ℝ :=
  let a := intVal mem (dist+u*L) h L
  let b := intVal mem (dist+v*L) h L
  let z := intVal mem (dist+lca T r u v*L) h L
  roundStretch P (1 + ((a+b-2*z : ℤ) : ℝ) / (intVal mem (lengths+i*L) h L : ℝ))

/-- A pass over packed edges allocates one rounded output per edge,
preserves the input tables, and keeps the unallocated heap tail zero. -/
theorem stretchRoundLoop_triple {w h query : ℕ} {p : Program} {T : MGraph} {r : ℕ}
    (hq : MeetsContract w p query (edgeStretchQueryContract w h T r))
    (mem : ℕ → ℕ) (pos base n rows tails heads db dist lengths L P heap m : ℕ)
    (u v : ℕ → ℕ) (hw : 1 < 2^w)
    (hwords : ∀ a ∈ [base,n,rows,tails,heads,db,dist,lengths,L,P,heap,m], a < 2^w)
    (hat : base+rows*n ≤ heap) (hdt : db+n ≤ heap)
    (ht : tails+m ≤ heap) (hh : heads+m ≤ heap)
    (he : lengths+m*L ≤ heap)
    (hroom : heap+m*edgeStretchSpace L < 2^w) (hzero : ZeroFrom mem heap)
    (hu : ∀ i < m, mem (tails+i) = u i ∧ u i < 2^w)
    (hv : ∀ i < m, mem (heads+i) = v i ∧ v i < 2^w)
    (hpre : ∀ i < m, (edgeStretchQueryContract w h T r).pre
      [base,n,rows,u i,v i,db,dist,lengths+i*L,L,P,heap] mem) :
    Triple w p (fun st => st = startState [base,n,rows,tails,heads,db,dist,lengths,L,P,heap,m] mem pos)
      (stretchRoundLoop query)
      (normalPost fun st => st.regs 10 = heap+m*edgeStretchSpace L ∧
        ZeroFrom st.mem (st.regs 10) ∧ (∀ a < heap, st.mem a = mem a) ∧
        ∀ i < m, Valid st.mem (roundStretchAddr heap L i) h L ∧
          fixVal st.mem (roundStretchAddr heap L i) h L P =
            roundStretchValue mem T r h L P dist lengths (u i) (v i) i)
      (fun _ => (86*rows + edgeStretchCost L + 126)*m+7) := by
  let S := edgeStretchSpace L
  have hLS : L ≤ S := by
    unfold S edgeStretchSpace stretchFromLengthSpace
    omega
  have hm := hwords m (by simp)
  let Inv := fun i (st : State) =>
    st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 2 = rows ∧ st.regs 3 = tails ∧
    st.regs 4 = heads ∧ st.regs 5 = db ∧ st.regs 6 = dist ∧ st.regs 7 = lengths ∧
    st.regs 8 = L ∧ st.regs 9 = P ∧ st.regs 10 = heap+i*S ∧ st.regs 11 = m ∧
    st.regs 12 = i ∧ ZeroFrom st.mem (st.regs 10) ∧
    (∀ a < heap, st.mem a = mem a) ∧
    ∀ j < i, Valid st.mem (roundStretchAddr heap L j) h L ∧
      fixVal st.mem (roundStretchAddr heap L j) h L P =
        roundStretchValue mem T r h L P dist lengths (u j) (v j) j
  have loop := Triple.forRange_const (p := p) (r := 12) (lo := .const 0) (hi := .reg 11)
    (body := .call 10 query stretchRoundArgs) (Inv := Inv)
    (P := fun st => st = startState [base,n,rows,tails,heads,db,dist,lengths,L,P,heap,m] mem pos)
    (86*rows + edgeStretchCost L + 117) 0 m (Nat.zero_le _) hw (fun _ => hm)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [Inv,startState,hzero]⟩)
    (fun _ _ _ _ h => by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hi,_⟩ := h
      exact hi)
    (fun _ st _ _ h => by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hr,_⟩ := h
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,hz,hf,hdone⟩
      let cur := heap+i*S
      let edge := lengths+i*L
      have hcur : heap ≤ cur := Nat.le_add_right _ _
      have hspace : cur+S < 2^w := by
        have hmul := Nat.mul_le_mul_right S hi
        rw [Nat.succ_mul] at hmul
        change heap+m*S < 2^w at hroom
        dsimp [cur]
        omega
      have hlen : edge < 2^w := by
        have hmul := Nat.mul_le_mul_right L hi.le
        dsimp [edge,cur] at *
        omega
      have hcurw : cur < 2^w := by omega
      obtain ⟨htu,huw⟩ := hu i hi
      obtain ⟨hvh,hvw⟩ := hv i hi
      have hargs := stretchRoundArgs_eval base n rows tails heads db dist lengths L P cur i
        (u i) (v i) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h12
        ((hf _ (by omega)).trans htu) ((hf _ (by omega)).trans hvh)
        (by dsimp [cur] at hspace; omega) (by dsimp [cur] at hspace; omega) hlen
      have hargsW : ∀ a ∈ [base,n,rows,u i,v i,db,dist,edge,L,P,cur], a < 2^w := by
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals first | assumption | apply hwords; simp
      have hnext := edgeStretchQuery_pre_frame (hpre i hi) hat hdt hcur hspace (by change ZeroFrom st.mem (heap+i*S); rwa [h10] at hz) hf
      obtain ⟨out,c,ret,hrun,hpost,hreg,hregs,hcost⟩ :=
        runs_call_of_meetsContract (r := 10) hq hargs hargsW hnext ω
      have hnew : ret = heap+(i+1)*S := by
        have hret : ret = cur+S := hpost.1
        rw [Nat.succ_mul]
        simpa only [cur,Nat.add_assoc] using hret
      have hframe : ∀ a < cur, out.mem a = st.mem a := hpost.2.2.2.1
      have htail : ZeroFrom out.mem ret := hpost.2.2.2.2.1
      have hindex := (hregs 12 (by decide)).trans h12
      refine ⟨.normal,out,c,hrun,⟨?_,hindex⟩,?_⟩
      · refine ⟨(hregs 0 (by decide)).trans h0,(hregs 1 (by decide)).trans h1,
          (hregs 2 (by decide)).trans h2,(hregs 3 (by decide)).trans h3,
          (hregs 4 (by decide)).trans h4,(hregs 5 (by decide)).trans h5,
          (hregs 6 (by decide)).trans h6,(hregs 7 (by decide)).trans h7,
          (hregs 8 (by decide)).trans h8,(hregs 9 (by decide)).trans h9,hreg.trans hnew,
          (hregs 11 (by decide)).trans h11,by simp,?_,?_,?_⟩
        · change ZeroFrom out.mem (Function.update out.regs 12 (i+1) 10)
          simpa [Function.update_of_ne (by decide : (10 : ℕ) ≠ 12),hreg] using htail
        · exact fun a ha => (hframe a (ha.trans_le hcur)).trans (hf a ha)
        · intro j hj
          by_cases hij : j = i
          · subst j
            have hs := hpost.2.2.2.2.2
            change Valid out.mem (cur+S-L) h L ∧
              fixVal out.mem (cur+S-L) h L P =
                roundStretchValue st.mem T r h L P dist lengths (u i) (v i) i at hs
            have haEq : roundStretchAddr heap L i = cur+S-L := by
              unfold roundStretchAddr cur S
              rw [Nat.succ_mul]
              omega
            rw [haEq]
            refine ⟨hs.1,hs.2.trans ?_⟩
            obtain ⟨_,_,_,_,_,_,_,_,_,_,_,heq,_,_,_,_,_,hblock,_⟩ := hpre i hi
            cases heq
            obtain ⟨⟨_,_,_,_,_,_,_,heq,ha,hb,hz,he',_⟩,_,_⟩ := hblock
            cases heq
            have hval (a : ℕ) (hb : a+L ≤ heap) :
                intVal st.mem a h L = intVal mem a h L :=
              intVal_congr fun j hj => hf _ (by omega)
            unfold roundStretchValue
            rw [hval _ ha,hval _ hb,hval _ hz,hval _ he']
          · have hj' : j < i := by omega
            have hmul := Nat.mul_le_mul_right S (show j+1 ≤ i by omega)
            have hLj := hLS.trans (Nat.le_mul_of_pos_left S (by omega : 0 < j+1))
            have hbefore : roundStretchAddr heap L j + L ≤ cur := by
              unfold cur roundStretchAddr
              change heap+(j+1)*S-L+L ≤ _
              omega
            obtain ⟨hvalid,hval⟩ := hdone j hj'
            obtain ⟨hv',heq⟩ := edgeStretchQuery_preservesBlock hpost hbefore hvalid
            exact ⟨hv',heq.trans hval⟩
      · change c ≤ argsSize stretchRoundArgs + (86*rows + edgeStretchCost L+95) + 1 at hcost
        simp [stretchRoundArgs,argsSize,Expr.size] at hcost
        change c ≤ 86*rows + edgeStretchCost L + 117
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned => exact h
    | normal =>
      obtain ⟨_,_,_,_,_,_,_,_,_,_,hr,_,_,hz,hf,hdone⟩ := h
      exact ⟨hr,hz,hf,hdone⟩
  · intro _ _
    simp [Expr.size,Nat.mul_comm,Nat.add_assoc]

/-- When the table stores root distances, the stretch loop's numeric formula
is the upward-rounded tree stretch of the edge in Definition 5.8. -/
theorem roundStretchValue_eq_treeStretch {G T : MGraph} {r e : ℕ}
    (hT : IsRootedTree T r) (hu : G.tail e ∈ T.V) (hv : G.head e ∈ T.V)
    (ℓ : ℕ → ℝ) (mem : ℕ → ℕ) (h L P Q dist lengths i : ℕ)
    (hDist : ∀ x ∈ T.V, fixVal mem (dist+x*L) h L Q = walkLength ℓ (T.forestPath x r))
    (hEdge : fixVal mem (lengths+i*L) h L Q = ℓ e) :
    roundStretchValue mem T r h L P dist lengths (G.tail e) (G.head e) i =
      roundStretch P (treeStretch G T ℓ e) :=
  edgeStretch_eq_model hT hu hv ℓ (hDist _ hu) (hDist _ hv)
    (hDist _ (lca_mem hT hu hv)) hEdge

/-- Decode the whole stretch round against the tree-stretch formula, allowing
the packed edge order to differ from the graph's edge names. -/
theorem stretchRound_outputs_eq_treeStretch {G T : MGraph} {r : ℕ}
    (hT : IsRootedTree T r) (ℓ : ℕ → ℝ) (mem out : ℕ → ℕ)
    (h L P Q dist lengths heap m : ℕ) (edge : ℕ → ℕ)
    (hDist : ∀ x ∈ T.V, fixVal mem (dist+x*L) h L Q = walkLength ℓ (T.forestPath x r))
    (hEdge : ∀ i < m, fixVal mem (lengths+i*L) h L Q = ℓ (edge i))
    (hEnds : ∀ i < m, G.tail (edge i) ∈ T.V ∧ G.head (edge i) ∈ T.V)
    (hOutput : ∀ i < m, Valid out (roundStretchAddr heap L i) h L ∧
      fixVal out (roundStretchAddr heap L i) h L P =
        roundStretchValue mem T r h L P dist lengths (G.tail (edge i)) (G.head (edge i)) i) :
    ∀ i < m, Valid out (roundStretchAddr heap L i) h L ∧
      fixVal out (roundStretchAddr heap L i) h L P = roundStretch P (treeStretch G T ℓ (edge i)) := by
  intro i hi
  obtain ⟨hu,hv⟩ := hEnds i hi
  obtain ⟨hvalid,hval⟩ := hOutput i hi
  exact ⟨hvalid,hval.trans
    (roundStretchValue_eq_treeStretch hT hu hv ℓ mem h L P Q dist lengths i hDist (hEdge i hi))⟩

/-- Starting at the first stretch result and using the allocation
stride addresses every later result. -/
theorem roundStretchAddr_stride (heap L i : ℕ) :
    roundStretchAddr heap L 0 + i*edgeStretchSpace L = roundStretchAddr heap L i := by
  have hL : L ≤ edgeStretchSpace L := by unfold edgeStretchSpace stretchFromLengthSpace; omega
  simp only [roundStretchAddr,Nat.zero_add,Nat.succ_mul]
  omega

/-- Every stretch block ends at or before the heap pointer returned by
the round. -/
theorem roundStretchAddr_end_le (heap L m i : ℕ) (hi : i < m) :
    roundStretchAddr heap L i + L ≤ heap+m*edgeStretchSpace L := by
  have hL : L ≤ edgeStretchSpace L := by unfold edgeStretchSpace stretchFromLengthSpace; omega
  have hmul := Nat.mul_le_mul_right (edgeStretchSpace L) hi
  simp only [roundStretchAddr,Nat.succ_mul] at *
  omega

end MinCostFlow.LastLevelProgram
