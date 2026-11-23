module

public import MinCostFlow.LastLevelProgram.ConnectedLSST
public import MinCostFlow.LastLevelProgram.RelocatedTreeCall
import WordRAM.Tactic

/-!
# Selecting the tree for a rebuild round

Theorem 2.2 (page 7) supplies the tree for a round of Definition 5.8
(pages 19–20). The second call reads its output count and leaves the
distinct selected edge indices in the traversal input array.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord LSF

/-- Call the tree routine, read its count, and return the retained count. -/
def selectTreeBody (lsst dedup selectedReg marksReg destReg headerReg tmp count : ℕ)
    (args : List Expr) : Stmt :=
  .call tmp lsst args ;;
  .call count dedup [.reg selectedReg, .reg marksReg, .reg destReg, .load (.reg headerReg)] ;;
  .ret (.reg count)

/-- The selection wrapper contains only ordinary calls and a return. -/
theorem selectTreeBody_noRand (lsst dedup selectedReg marksReg destReg headerReg tmp count : ℕ)
    (args : List Expr) :
    (selectTreeBody lsst dedup selectedReg marksReg destReg headerReg tmp count args).NoRand := by
  simp [selectTreeBody, Stmt.NoRand]

/-- Sequence the installed procedures, returning the deduplicated count.
The caller supplies the layout transfer for the untouched endpoint arrays
and the fresh mark region. -/
theorem selectTree_runs {w lsst dedup selectedReg marksReg destReg headerReg tmp count : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    {C D : Contract} {args : List Expr} {vs : List ℕ}
    {selected marks dest header bound : ℕ}
    (hlsst : MeetsContract w p lsst C) (hdedup : MeetsContract w p dedup D)
    (hargs : evalArgs w st args = some vs) (hwords : ∀ a ∈ vs, a < 2^w)
    (hpre : C.pre vs st.mem)
    (hselected : st.regs selectedReg = selected) (hmarks : st.regs marksReg = marks)
    (hdest : st.regs destReg = dest) (hheader : st.regs headerReg = header)
    (hne : selectedReg ≠ tmp ∧ marksReg ≠ tmp ∧ destReg ≠ tmp ∧ headerReg ≠ tmp)
    (haddr : selected < 2^w ∧ marks < 2^w ∧ dest < 2^w ∧ header < 2^w)
    (hnext : ∀ v mem, C.post vs st.mem v mem →
      mem header < 2^w ∧ D.pre [selected, marks, dest, mem header] mem ∧
        D.cost [selected, marks, dest, mem header] mem ≤ bound)
    (hret : ∀ input v out, input header < 2^w → D.post [selected, marks, dest, input header] input v out →
      v < 2^w) :
    ∃ o out cost, Runs w p ω
      (selectTreeBody lsst dedup selectedReg marksReg destReg headerReg tmp count args)
      st o out cost ∧
      (∃ v input k, C.post vs st.mem v input ∧
        D.post [selected, marks, dest, input header] input k out.mem ∧ o = .returned k) ∧
      cost ≤ argsSize args + C.cost vs st.mem + bound + 12 := by
  unfold selectTreeBody
  apply runs_start_le
  refine runs_seq_call_le hlsst hargs hwords hpre ?_
  intro v mem pos hv
  obtain ⟨hh, hpre', hcost⟩ := hnext v mem hv
  obtain ⟨hselNe, hmarksNe, hdestNe, hheaderNe⟩ := hne
  obtain ⟨hs, hm, hd, hhdr⟩ := haddr
  refine runs_seq_call_le hdedup (vs := [selected, marks, dest, mem header]) ?_ ?_ hpre' ?_
  · simp only [evalArgs, Expr.eval, Function.update_of_ne hselNe,
      Function.update_of_ne hmarksNe, Function.update_of_ne hdestNe,
      Function.update_of_ne hheaderNe, hselected, hmarks, hdest, hheader]
    rfl
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  · intro k out _ hk
    have hkw := hret mem k out hh hk
    refine runs_ret_le (v := k) (by eval_expr) ⟨v, mem, k, hv, hk, rfl⟩ ?_
    simp only [argsSize, Expr.size]
    omega

/-- The relocated output and an allocation after the guest region
supply the precondition and cost bound for selected-edge deduplication. -/
theorem dedupSelectedTree_pre_of_relocated {w c₀ heap src guestCost L : ℕ}
    {Q : Program} {K : ℝ} {G T : MGraph} {len wt : ℕ → ℤ}
    {args : List ℕ} {mem out : ℕ → ℕ} {ret : ℕ}
    (marks dest tails heads : ℕ) {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v gamma T)
    (hpost : (relocatedTreeContract Q c₀ K G L len wt heap src guestCost T).post args mem ret out) :
    let base := heap + 1
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let guestWidth := max 5 (Nat.log 2 (queryHeap G L + lsstSpace Q K G.n G.m sim 1) + 1)
    let selected := base + queryOriginals G L
    let bridges := base + queryBridges G L
    let header := base + queryHeader G L
    let C := dedupSelectedTreeContract w G ℓ v gamma selected bridges header marks dest tails heads
    base + 2 ^ guestWidth ≤ marks → selected + G.n ≤ marks →
    marks + G.m ≤ dest → dest + G.n < 2 ^ w → G.n + 1 < 2 ^ w →
    tails + G.m ≤ base → heads + G.m ≤ base →
    ListAt mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) →
    ListAt mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) →
    out header < 2 ^ w ∧ C.pre [selected, marks, dest, out header] out ∧
      C.cost [selected, marks, dest, out header] out ≤ 40 * G.n + 14 := by
  intro base sim guestWidth selected bridges header C hmarks hsel hdest hroom hword
    htail hhead ht hh
  obtain ⟨_, hdecoded, hcount, _, hframe, hzero⟩ := hpost
  change out header ≤ G.n at hcount
  have hpreserve (ptr : ℕ) (values : List ℕ) (hb : ptr + values.length ≤ base)
      (hat : ListAt mem ptr values) : ListAt out ptr values := by
    intro i hi
    rw [hframe _ (by omega)]
    exact hat i hi
  refine ⟨by omega, ⟨rfl, hdecoded.symm ▸ htree, by omega, by omega, hdest,
    by omega, by omega, by omega, ?_, ?_, ?_⟩, ?_⟩
  · exact hpreserve tails _ (by simpa using htail) ht
  · exact hpreserve heads _ (by simpa using hhead) hh
  · intro e _
    exact hzero _ (hmarks.trans (Nat.le_add_right _ _))
  · change 40 * out header + 14 ≤ 40 * G.n + 14
    omega

/-- Execute tree selection on a packed connected graph. The retained list
represents the compact oracle tree, and memory preceding the guest remains intact. -/
theorem selectRelocatedTree_runs {w c₀ heap src guestCost L lsst dedup : ℕ}
    {Q p : Program} {K : ℝ} {G T : MGraph} {len wt : ℕ → ℤ}
    {ω : ℕ → Bool} {st : State} {args : List Expr} {vs : List ℕ}
    {selectedReg marksReg destReg headerReg tmp count : ℕ}
    (marks dest tails heads : ℕ) {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v gamma T) :
    let base := heap + 1
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let guestWidth := max 5 (Nat.log 2 (queryHeap G L + lsstSpace Q K G.n G.m sim 1) + 1)
    let selected := base + queryOriginals G L
    let bridges := base + queryBridges G L
    let header := base + queryHeader G L
    let C := relocatedTreeContract Q c₀ K G L len wt heap src guestCost T
    let D := dedupSelectedTreeContract w G ℓ v gamma selected bridges header marks dest tails heads
    MeetsContract w p lsst C → MeetsContract w p dedup D →
    evalArgs w st args = some vs → (∀ a ∈ vs, a < 2^w) → C.pre vs st.mem →
    st.regs selectedReg = selected → st.regs marksReg = marks →
    st.regs destReg = dest → st.regs headerReg = header →
    (selectedReg ≠ tmp ∧ marksReg ≠ tmp ∧ destReg ≠ tmp ∧ headerReg ≠ tmp) →
    base + 2 ^ guestWidth ≤ marks → selected + G.n ≤ marks → header ≤ marks →
    marks + G.m ≤ dest → dest + G.n < 2 ^ w → G.n + 1 < 2 ^ w →
    tails + G.m ≤ base → heads + G.m ≤ base →
    ListAt st.mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) →
    ListAt st.mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i) →
    ∃ out cost kept, Runs w p ω
        (selectTreeBody lsst dedup selectedReg marksReg destReg headerReg tmp count args)
        st (.returned kept.length) out cost ∧
      kept.length ≤ G.n ∧ kept.Nodup ∧ ListAt out.mem dest kept ∧
      decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T ∧
      (∀ a < base, out.mem a = st.mem a) ∧ ZeroFrom out.mem (dest + G.n) ∧
      cost ≤ argsSize args + C.cost vs st.mem + 40 * G.n + 26 := by
  intro base sim guestWidth selected bridges header C D
    hlsst hdedup hargs hwords hpre hselected hmarks hdest hheader hne
    halloc hsel hhdr hdestAlloc hroom hword htail hhead ht hh
  obtain ⟨o, out, cost, hr, ⟨ret, input, k, hpost, hdpost, ho⟩, hcost⟩ :=
    selectTree_runs (ω := ω) (count := count) (bound := 40 * G.n + 14)
      hlsst hdedup hargs hwords hpre hselected hmarks hdest hheader hne
      ⟨by omega, by omega, by omega, by omega⟩
      (fun _ _ hp => dedupSelectedTree_pre_of_relocated marks dest tails heads htree hp
        halloc hsel hdestAlloc hroom hword htail hhead ht hh)
      (by
        intro mem n result hwordIn hp
        obtain ⟨_, _, hn, _⟩ := hp
        exact hn.trans_lt hwordIn)
  obtain ⟨_, hdecoded, hcount, _, hf, hzero⟩ := hpost
  change input header ≤ G.n at hcount
  change ZeroFrom input (base + 2 ^ guestWidth) at hzero
  obtain ⟨kept, hk, hlen, hnodup, hlist, hsame, hframe⟩ := hdpost
  refine ⟨out, cost, kept, ?_, (hk ▸ hlen).trans hcount, hnodup, hlist, hsame.trans hdecoded, ?_, ?_, ?_⟩
  · rwa [ho, hk] at hr
  · intro a ha
    exact (hframe a (Or.inl (by omega))).trans (hf a ha)
  · intro a ha
    rw [hframe a (Or.inr (by omega))]
    exact hzero a (by omega)
  · omega

/-- The retained array and the untouched endpoint arrays meet the
adjacency precondition. All list heads start at zero in fresh memory. -/
theorem selectedAdjacency_pre_of_selection {w base dest tails heads adj records : ℕ}
    {G : MGraph} {mem out : ℕ → ℕ} {kept : List ℕ}
    (hcount : kept.length ≤ G.n) (hkept : ListAt out dest kept)
    (hframe : ∀ a < base, out a = mem a)
    (hzero : ZeroFrom out (dest + G.n))
    (halloc : dest + G.n ≤ adj) (hbase : base ≤ adj)
    (hrecords : adj + G.n ≤ records) (hroom : records + 6 * G.n < 2^w)
    (htail : tails + G.m ≤ base) (hhead : heads + G.m ≤ base)
    (ht : ListAt mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i))
    (hh : ListAt mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i)) :
    (selectedAdjacencyContract w (indexedGraph G) kept dest tails heads adj records).pre
      [dest, tails, heads, adj, records, kept.length] out ∧ ZeroFrom out adj := by
  have transfer (ptr : ℕ) (values : List ℕ) (hptr : ptr + values.length ≤ base)
      (hat : ListAt mem ptr values) : ListAt out ptr values := by
    intro i hi
    exact (hframe _ (by omega)).trans (hat i hi)
  have hroom' : records + 6 * kept.length < 2^w :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hcount) records).trans_lt hroom
  refine ⟨⟨rfl, by omega, htail.trans hbase, hhead.trans hbase, hrecords,
    hroom', hkept, ?_, ?_⟩, fun a ha => hzero a (halloc.trans ha)⟩
  · apply transfer tails _ _ ht
    simpa using htail
  · apply transfer heads _ _ hh
    simpa using hhead

/-- The selected tree array and the memory frame exposed to traversal. -/
def selectedTreeAt (G T : MGraph) (base dest count : ℕ)
    (mem out : ℕ → ℕ) : Prop :=
  ∃ kept : List ℕ, count = kept.length ∧ kept.length ≤ G.n ∧ kept.Nodup ∧
    ListAt out dest kept ∧
    decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T ∧
    (∀ a < base, out a = mem a) ∧ ZeroFrom out (dest + G.n)

/-- The selection return word is the adjacency procedure's edge count. -/
theorem adjacency_pre_of_selectedTreeAt {w base dest count tails heads adj records : ℕ}
    {G T : MGraph} {mem out : ℕ → ℕ}
    (hTree : selectedTreeAt G T base dest count mem out)
    (halloc : dest + G.n ≤ adj) (hbase : base ≤ adj)
    (hrecords : adj + G.n ≤ records) (hroom : records + 6 * G.n < 2^w)
    (htail : tails + G.m ≤ base) (hhead : heads + G.m ≤ base)
    (ht : ListAt mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i))
    (hh : ListAt mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i)) :
    ∃ kept : List ℕ, count = kept.length ∧ kept.Nodup ∧
      decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T ∧
      (selectedAdjacencyContract w (indexedGraph G) kept dest tails heads adj records).pre
        [dest, tails, heads, adj, records, count] out ∧ ZeroFrom out adj := by
  obtain ⟨kept, hcount, hsize, hn, hl, he, hf, hz⟩ := hTree
  obtain ⟨hp, hz'⟩ := selectedAdjacency_pre_of_selection hsize hl hf hz
    halloc hbase hrecords hroom htail hhead ht hh
  exact ⟨kept, hcount, hn, he, hcount.symm ▸ hp, hz'⟩

/-- Reuse the verified selection run through an ordinary procedure call.
The input predicate supplies the packed query and its register layout. -/
theorem selectTree_meetsContract_of_runs {w entry : ℕ} {p : Program} {body : Stmt}
    {G T : MGraph} {base dest : ℕ}
    (hp : p.procs[entry]? = some body) (ready : List ℕ → (ℕ → ℕ) → Prop)
    (budget : ℕ)
    (hrun : ∀ args mem pos ω, (∀ a ∈ args, a < 2^w) → ready args mem →
      ∃ out cost kept, Runs w p ω body (startState args mem pos) (.returned kept.length) out cost ∧
        kept.length ≤ G.n ∧ kept.Nodup ∧ ListAt out.mem dest kept ∧
        decodedTree G.n G.m (indexedGraph G).tail (indexedGraph G).head kept [] = T ∧
        (∀ a < base, out.mem a = mem a) ∧ ZeroFrom out.mem (dest + G.n) ∧ cost ≤ budget) :
    MeetsContract w p entry
      { pre := ready, post := fun _ mem count out => selectedTreeAt G T base dest count mem out,
        cost := fun _ _ => budget } := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨out, cost, kept, hr, hcount, hn, hl, he, hf, hz, hc⟩ :=
    hrun args mem pos ω hwords hpre
  exact ⟨.returned kept.length, out, cost, hr, ⟨kept,rfl,hcount,hn,hl,he,hf,hz⟩, hc⟩

/-- The selection entry stores its four local pointers first, followed
by the arguments of the relocated LSST. -/
def selectTreeEntry (lsst dedup arity : ℕ) : Stmt :=
  selectTreeBody lsst dedup 0 1 2 3 (arity + 4) (arity + 5)
    ((List.range' 4 arity).map Expr.reg)

theorem evalArgs_registerRange {w : ℕ} (st : State) (start : ℕ)
    (values : List ℕ) (h : ∀ i, i < values.length → st.regs (start + i) = values.getD i 0) :
    evalArgs w st ((List.range' start values.length).map Expr.reg) = some values := by
  induction values generalizing start with
  | nil => rfl
  | cons value tail ih =>
    rw [List.length_cons, List.range'_succ, List.map_cons]
    apply evalArgs_cons
    · have hhead := h 0 (Nat.succ_pos _)
      simpa [Expr.eval] using hhead
    · apply ih
      intro i hi
      have he := h (i + 1) (Nat.succ_lt_succ hi)
      simpa only [List.getD_cons_succ, show start + (i + 1) = start + 1 + i by omega] using he

/-- The selection entry forwards exactly the arguments behind its four
local pointers. -/
theorem selectTreeEntry_args (w pos selected marks dest header : ℕ)
    (values : List ℕ) (mem : ℕ → ℕ) :
    evalArgs w (startState ([selected, marks, dest, header] ++ values) mem pos)
      ((List.range' 4 values.length).map Expr.reg) = some values := by
  apply evalArgs_registerRange
  intro i _
  rw [Nat.add_comm 4 i]
  rfl

/-- The selection entry uses no random instructions. -/
theorem selectTreeEntry_noRand (lsst dedup arity : ℕ) :
    (selectTreeEntry lsst dedup arity).NoRand :=
  selectTreeBody_noRand _ _ _ _ _ _ _ _ _

/-- Call tree selection with the four local pointers and a packed
query whose endpoints also supply the adjacency input arrays. -/
theorem selectTreeEntry_meetsContract {w c₀ heap src guestCost L entry lsst dedup : ℕ}
    {Q p : Program} {K : ℝ} {G T : MGraph} {len wt : ℕ → ℤ}
    (values : List ℕ) (marks dest tails heads : ℕ) {ℓ v : ℕ → ℝ} {gamma : ℝ}
    (htree : IsLSST (indexedGraph G).toMGraph ℓ v gamma T)
    (hp : p.procs[entry]? = some (selectTreeEntry lsst dedup values.length)) :
    let base := heap + 1
    let sim := lsstLSimMin c₀ G.n G.m L 1
    let guestWidth := max 5 (Nat.log 2 (queryHeap G L + lsstSpace Q K G.n G.m sim 1) + 1)
    let selected := base + queryOriginals G L
    let bridges := base + queryBridges G L
    let header := base + queryHeader G L
    let C := relocatedTreeContract Q c₀ K G L len wt heap src guestCost T
    let D := dedupSelectedTreeContract w G ℓ v gamma selected bridges header marks dest tails heads
    MeetsContract w p lsst C → MeetsContract w p dedup D →
    base + 2 ^ guestWidth ≤ marks → selected + G.n ≤ marks → header ≤ marks →
    marks + G.m ≤ dest → dest + G.n < 2 ^ w → G.n + 1 < 2 ^ w →
    tails + G.m ≤ base → heads + G.m ≤ base →
    MeetsContract w p entry {
      pre := fun args mem => args = [selected, marks, dest, header] ++ values ∧ C.pre values mem ∧
        ListAt mem tails (List.ofFn fun i : Fin G.m => (indexedGraph G).tail i) ∧
        ListAt mem heads (List.ofFn fun i : Fin G.m => (indexedGraph G).head i)
      post := fun _ mem count out => selectedTreeAt G T base dest count mem out
      cost := fun _ mem => argsSize ((List.range' 4 values.length).map Expr.reg) +
        C.cost values mem + 40 * G.n + 26 } := by
  intro base sim guestWidth selected bridges header C D hlsst hdedup
    halloc hsel hhdr hd hroom hword htail hhead
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨he, hpre, ht, hh⟩ := hpre
  subst args
  have harg := selectTreeEntry_args w pos selected marks dest header values mem
  have hvalues (a : ℕ) (ha : a ∈ values) : a < 2^w :=
    hwords a (List.mem_append_right _ ha)
  have hne : 0 ≠ values.length + 4 ∧ 1 ≠ values.length + 4 ∧
      2 ≠ values.length + 4 ∧ 3 ≠ values.length + 4 :=
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨out, cost, kept, hr, hsize, hn, hl, hsame, hf, hz, hc⟩ :=
    selectRelocatedTree_runs (ω := ω) (count := values.length + 5)
      marks dest tails heads htree hlsst hdedup harg hvalues hpre
      rfl rfl rfl rfl hne halloc hsel hhdr hd hroom hword htail hhead ht hh
  exact ⟨.returned kept.length, out, cost, hr, ⟨kept,rfl,hsize,hn,hl,hsame,hf,hz⟩, hc⟩

end MinCostFlow.LastLevelProgram
