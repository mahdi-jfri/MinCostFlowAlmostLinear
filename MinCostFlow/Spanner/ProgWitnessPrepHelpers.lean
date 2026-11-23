module

public import MinCostFlow.Spanner.ProgWitnessPrep

/-!
# Shared Layout and Invariant Helpers for `witnessPrep`

Defines layout pointer helpers on `PrepInput` (`aLvlHead`, `aComps`, `cVertsPtr`, `cJSubPtr`,
`cJOrigPtr`, `cDegPtr`, `cEndPtr`), register invariants (`PrepBaseRegs`, `PrepFullRegs`),
`PrepStaticState`, component decoding lemma `rawComps_recordAt`, and flat sequential `Runs`
lemmas used across the phase-by-phase verification of `witnessPrepModule`.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM MinCostFlow.Cited

/-! ## 1. Deterministic Layout Addresses & Pre-Computed Offsets -/

namespace PrepInput

def aLvlHead (inp : PrepInput) : ℕ := inp.h + 8
def aEdgeNext (inp : PrepInput) : ℕ := inp.aLvlHead + inp.d_ℓ + 1
def aJ0Out (inp : PrepInput) : ℕ := inp.aEdgeNext + inp.J0_strip.m
def aComps (inp : PrepInput) : ℕ := inp.aJ0Out + inp.j0Edges.length
def aVComp (inp : PrepInput) : ℕ := inp.aComps + 7 * inp.rawComps.length
def aVLoc (inp : PrepInput) : ℕ := inp.aVComp + inp.J.n

def cVertsPtr (inp : PrepInput) (ci : ℕ) : ℕ :=
  inp.decAddr + 4 + inp.J0_strip.m +
    ((inp.rawComps.take ci).map fun p => 2 + p.2.length).sum + 2

def cJSubPtr (inp : PrepInput) (ci : ℕ) : ℕ :=
  inp.hBlocksStart +
    ((inp.rawComps.take ci).map fun p => 2 + 3 * (inp.cJSub p).m + p.2.length).sum

def cJOrigPtr (inp : PrepInput) (ci : ℕ) : ℕ :=
  inp.cJSubPtr ci + 2 + 2 * (inp.cJSub (inp.rawComps.getD ci (0, []))).m

def cDegPtr (inp : PrepInput) (ci : ℕ) : ℕ :=
  inp.cJOrigPtr ci + (inp.cJSub (inp.rawComps.getD ci (0, []))).m

def cEndPtr (inp : PrepInput) (ci : ℕ) : ℕ :=
  inp.cDegPtr ci + (inp.rawComps.getD ci (0, [])).2.length

theorem hBlocksStart_eq (inp : PrepInput) :
    inp.hBlocksStart = inp.aVLoc + inp.J.n := by
  simp only [hBlocksStart, aVLoc, aVComp, aComps, aJ0Out, aEdgeNext, aLvlHead]; omega

theorem cJSubPtr_zero (inp : PrepInput) : inp.cJSubPtr 0 = inp.hBlocksStart := by
  simp [cJSubPtr]

theorem cJSubPtr_succ {inp : PrepInput} {ci : ℕ} (hci : ci < inp.rawComps.length) :
    inp.cJSubPtr (ci + 1) = inp.cEndPtr ci := by
  set c := inp.rawComps[ci]
  have htake : inp.rawComps.take (ci + 1) = inp.rawComps.take ci ++ [c] :=
    List.take_succ_eq_append_getElem hci
  have hget : inp.rawComps.getD ci (0, []) = c := List.getD_eq_getElem _ _ hci
  simp only [cJSubPtr, cEndPtr, cDegPtr, cJOrigPtr, htake, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton, hget]
  omega

theorem cJSubPtr_length (inp : PrepInput) :
    inp.cJSubPtr inp.rawComps.length = inp.hEnd := by
  simp [cJSubPtr, hEnd, List.take_length]

theorem cJSubPtr_mono (inp : PrepInput) {a b : ℕ} (hab : a ≤ b) :
    inp.cJSubPtr a ≤ inp.cJSubPtr b := by
  have htake : inp.rawComps.take a = (inp.rawComps.take b).take a := by
    rw [List.take_take, min_eq_left hab]
  rw [cJSubPtr, cJSubPtr, htake]
  have hp := (List.take_prefix a (inp.rawComps.take b)).sublist
  have hs := List.Sublist.sum_le_sum (List.Sublist.map (fun p => 2 + 3 * (inp.cJSub p).m + p.2.length) hp)
    (fun _ _ => Nat.zero_le _)
  omega

theorem cJSubPtr_le_hEnd {inp : PrepInput} {ci : ℕ} (hci : ci ≤ inp.rawComps.length) :
    inp.cJSubPtr ci ≤ inp.hEnd := by
  rw [← inp.cJSubPtr_length]
  exact inp.cJSubPtr_mono hci

end PrepInput

/-- Fixed base register predicate valid throughout `witnessPrepModule`. -/
def PrepBaseRegs (inp : PrepInput) (st : State) : Prop :=
  st.regs 0 = inp.jAddr ∧
  st.regs 1 = inp.j0Addr ∧
  st.regs 2 = inp.nlAddr ∧
  st.regs 3 = inp.decAddr ∧
  st.regs 4 = inp.h ∧
  st.regs 5 = inp.J.n ∧
  st.regs 6 = inp.J0_strip.m ∧
  st.regs 7 = inp.d_ℓ ∧
  st.regs 8 = inp.rawComps.length ∧
  st.regs 9 = inp.aLvlHead ∧
  st.regs 10 = inp.aEdgeNext ∧
  st.regs 11 = inp.aJ0Out

/-- Full immutable register predicate valid after `prepHdrStoreStmt`. -/
def PrepFullRegs (inp : PrepInput) (st : State) : Prop :=
  PrepBaseRegs inp st ∧
  st.regs 12 = inp.j0Edges.length ∧
  st.regs 13 = inp.aComps ∧
  st.regs 14 = inp.aVComp ∧
  st.regs 15 = inp.aVLoc

theorem prepBaseRegs_update {inp : PrepInput} {st : State} {r v : ℕ}
    (hb : PrepBaseRegs inp st) (hr : 12 ≤ r) :
    PrepBaseRegs inp { st with regs := Function.update st.regs r v } := by
  rcases hb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Function.update_of_ne (by omega : (0 : ℕ) ≠ r)] using h0
  · simpa [Function.update_of_ne (by omega : (1 : ℕ) ≠ r)] using h1
  · simpa [Function.update_of_ne (by omega : (2 : ℕ) ≠ r)] using h2
  · simpa [Function.update_of_ne (by omega : (3 : ℕ) ≠ r)] using h3
  · simpa [Function.update_of_ne (by omega : (4 : ℕ) ≠ r)] using h4
  · simpa [Function.update_of_ne (by omega : (5 : ℕ) ≠ r)] using h5
  · simpa [Function.update_of_ne (by omega : (6 : ℕ) ≠ r)] using h6
  · simpa [Function.update_of_ne (by omega : (7 : ℕ) ≠ r)] using h7
  · simpa [Function.update_of_ne (by omega : (8 : ℕ) ≠ r)] using h8
  · simpa [Function.update_of_ne (by omega : (9 : ℕ) ≠ r)] using h9
  · simpa [Function.update_of_ne (by omega : (10 : ℕ) ≠ r)] using h10
  · simpa [Function.update_of_ne (by omega : (11 : ℕ) ≠ r)] using h11

theorem prepFullRegs_update {inp : PrepInput} {st : State} {r v : ℕ}
    (hf : PrepFullRegs inp st) (hr : 16 ≤ r) :
    PrepFullRegs inp { st with regs := Function.update st.regs r v } := by
  rcases hf with ⟨hb, h12, h13, h14, h15⟩
  refine ⟨prepBaseRegs_update hb (by omega), ?_, ?_, ?_, ?_⟩
  · simpa [Function.update_of_ne (by omega : (12 : ℕ) ≠ r)] using h12
  · simpa [Function.update_of_ne (by omega : (13 : ℕ) ≠ r)] using h13
  · simpa [Function.update_of_ne (by omega : (14 : ℕ) ≠ r)] using h14
  · simpa [Function.update_of_ne (by omega : (15 : ℕ) ≠ r)] using h15

theorem prepBaseRegs_congr {inp : PrepInput} {s1 s2 : State}
    (hb : PrepBaseRegs inp s1) (hregs : ∀ r < 12, s2.regs r = s1.regs r) :
    PrepBaseRegs inp s2 := by
  rcases hb with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hregs 0 (by omega), h0]
  · rw [hregs 1 (by omega), h1]
  · rw [hregs 2 (by omega), h2]
  · rw [hregs 3 (by omega), h3]
  · rw [hregs 4 (by omega), h4]
  · rw [hregs 5 (by omega), h5]
  · rw [hregs 6 (by omega), h6]
  · rw [hregs 7 (by omega), h7]
  · rw [hregs 8 (by omega), h8]
  · rw [hregs 9 (by omega), h9]
  · rw [hregs 10 (by omega), h10]
  · rw [hregs 11 (by omega), h11]

theorem prepFullRegs_congr {inp : PrepInput} {s1 s2 : State}
    (hf : PrepFullRegs inp s1) (hregs : ∀ r < 16, s2.regs r = s1.regs r) :
    PrepFullRegs inp s2 := by
  rcases hf with ⟨hb, h12, h13, h14, h15⟩
  refine ⟨prepBaseRegs_congr hb (fun r hr => hregs r (by omega)), ?_, ?_, ?_, ?_⟩
  · rw [hregs 12 (by omega), h12]
  · rw [hregs 13 (by omega), h13]
  · rw [hregs 14 (by omega), h14]
  · rw [hregs 15 (by omega), h15]

theorem listAt_sub_eq {mem : ℕ → ℕ} {a : ℕ} {xs : List ℕ}
    (hl : ListAt mem a xs) {k : ℕ} (hk : k < xs.length) :
    mem (a + k) = xs.getD k 0 := by
  rw [listAt_getElem hl hk, List.getD_eq_getElem _ _ hk]

theorem runs_seq_assign0 {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {s : Stmt} {st : State} {v T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (hrest : ∃ o st' c, Runs w p ω s { mem := st.mem, regs := Function.update st.regs r v, pos := st.pos }
      o st' c ∧ Q o st' ∧ (0 + e.size + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.assign r e) s) st o st' c ∧ Q o st' ∧ c ≤ T := by
  simpa using runs_seq_assign_le (k := 0) he hrest

theorem runs_seq_store0 {w : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr}
    {s : Stmt} {st : State} {addr v T : ℕ} {Q : Outcome → State → Prop}
    (ha : a.eval w st = some addr) (he : e.eval w st = some v)
    (hrest : ∃ o st' c, Runs w p ω s { mem := Function.update st.mem addr v, regs := st.regs, pos := st.pos }
      o st' c ∧ Q o st' ∧ (0 + a.size + e.size + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.store a e) s) st o st' c ∧ Q o st' ∧ c ≤ T := by
  simpa using runs_seq_store_le (k := 0) ha he hrest


/-! ## 3. Header Store, Parse, and Block Pure Helpers -/

def PrepStaticState (inp : PrepInput) (mem₀ mem : ℕ → ℕ) : Prop :=
  (∀ x < inp.h, mem x = mem₀ x) ∧
  mem inp.h = inp.j0Edges.length ∧
  mem (inp.h + 1) = inp.aJ0Out ∧
  mem (inp.h + 2) = inp.rawComps.length ∧
  mem (inp.h + 3) = inp.aComps ∧
  mem (inp.h + 4) = inp.aLvlHead ∧
  mem (inp.h + 5) = inp.aEdgeNext ∧
  mem (inp.h + 6) = inp.aVComp ∧
  mem (inp.h + 7) = inp.aVLoc ∧
  ListAt mem inp.aJ0Out inp.j0Edges ∧
  ∀ lvl ≤ inp.d_ℓ,
    ChainAt mem inp.aEdgeNext (mem (inp.aLvlHead + lvl))
      (DecomposeOutput.edgesAt inp.J0_strip inp.decomp lvl)

theorem prepStaticState_of_agree {inp : PrepInput} {mem₀ mem mem' : ℕ → ℕ}
    (hs : PrepStaticState inp mem₀ mem) (hag : ∀ x < inp.aComps, mem' x = mem x) :
    PrepStaticState inp mem₀ mem' := by
  rcases hs with ⟨hlt, h0, h1, h2, h3, h4, h5, h6, h7, hl, hch⟩
  have hlt_a : ∀ i < 8, inp.h + i < inp.aComps := by
    intro i hi
    simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
    omega
  refine ⟨fun x hx => (hag x (by
      simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
      omega)).trans (hlt x hx),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (hag inp.h (by simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]; omega)).trans h0
  · rw [hag _ (hlt_a 1 (by omega)), h1]
  · rw [hag _ (hlt_a 2 (by omega)), h2]
  · rw [hag _ (hlt_a 3 (by omega)), h3]
  · rw [hag _ (hlt_a 4 (by omega)), h4]
  · rw [hag _ (hlt_a 5 (by omega)), h5]
  · rw [hag _ (hlt_a 6 (by omega)), h6]
  · rw [hag _ (hlt_a 7 (by omega)), h7]
  · refine listAt_of_congr hl fun i hi => ?_
    exact hag (inp.aJ0Out + i) (by simp only [PrepInput.aComps]; omega)
  · intro lvl hlvl
    have hhd : inp.aLvlHead + lvl < inp.aComps := by
      simp only [PrepInput.aComps, PrepInput.aJ0Out, PrepInput.aEdgeNext, PrepInput.aLvlHead]
      omega
    rw [hag _ hhd]
    refine chainAt_of_agree (hch lvl hlvl) fun q hq => ?_
    simp only [DecomposeOutput.edgesAt, List.mem_filter, List.mem_range] at hq
    have hqm := hq.1
    exact hag (inp.aEdgeNext + q) (by simp only [PrepInput.aComps, PrepInput.aJ0Out]; omega)

theorem rawComps_recordAt {inp : PrepInput} {mem₀ mem : ℕ → ℕ} {w : ℕ}
    (hv : inp.Valid mem₀ w) (hlt : ∀ x < inp.h, mem x = mem₀ x)
    {ci : ℕ} (hci : ci < inp.rawComps.length) :
    mem (inp.cVertsPtr ci - 2) = inp.rawComps[ci].1 ∧
    mem (inp.cVertsPtr ci - 1) = inp.rawComps[ci].2.length ∧
    ListAt mem (inp.cVertsPtr ci) inp.rawComps[ci].2 := by
  rcases hv with ⟨_, _, _, _, _, _, hdec, hllen, _, _, _, _, _, _, _, _, hdecle, _, _, _⟩
  have hdecF := decomposeOutAt_fields hdec
  set xs := inp.rawComps
  have hsplit : xs = xs.take ci ++ xs[ci] :: xs.drop (ci + 1) := by
    rw [← List.drop_eq_getElem_cons hci, List.take_append_drop]
  have hfm : xs.flatMap compRecord =
      (xs.take ci).flatMap compRecord ++ (compRecord xs[ci] ++ (xs.drop (ci + 1)).flatMap compRecord) := by
    conv_lhs => rw [hsplit]
    simp only [List.flatMap_append, List.flatMap_cons]
  have hlAt : ListAt mem₀ (inp.decAddr + 4 + inp.J0_strip.m) (xs.flatMap compRecord) := by
    simpa [hllen] using hdecF.2.2.2.2.2
  rw [hfm, listAt_append, listAt_append] at hlAt
  have hmid := hlAt.2.1
  rw [compRecord, listAt_cons, listAt_cons] at hmid
  have hprefLen : ((xs.take ci).flatMap compRecord).length =
      ((xs.take ci).map fun p => 2 + p.2.length).sum := by
    induction (xs.take ci) with
    | nil => simp
    | cons p ps ih => simp [compRecord, ih]; omega
  rw [hprefLen] at hmid
  have h_sum_le : ((xs.take ci).map fun p => 2 + p.2.length).sum + (2 + xs[ci].2.length) ≤
      (xs.map fun p => 2 + p.2.length).sum := by
    have hsplit2 := congrArg (List.map fun p : ℕ × List ℕ => 2 + p.2.length) hsplit
    have hsplit3 := congrArg List.sum hsplit2
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hsplit3
    omega
  have hdeclen : (Decompose.encode inp.d_ℓ inp.phiNum_dec inp.phiDen_dec inp.level xs).length =
      4 + inp.J0_strip.m + (xs.map fun p => 2 + p.2.length).sum := by
    rw [decompose_encode_length, hllen]
  have hptr_eq : inp.cVertsPtr ci =
      inp.decAddr + 4 + inp.J0_strip.m + ((xs.take ci).map fun p => 2 + p.2.length).sum + 2 := rfl
  have hsub2 : inp.cVertsPtr ci - 2 < inp.h := by rw [hptr_eq]; omega
  have hsub1 : inp.cVertsPtr ci - 1 < inp.h := by rw [hptr_eq]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hlt _ hsub2]
    have hidx0 : inp.decAddr + 4 + inp.J0_strip.m + ((xs.take ci).map fun p => 2 + p.2.length).sum =
        inp.cVertsPtr ci - 2 := by rw [hptr_eq]; omega
    rw [← hidx0]
    exact hmid.1
  · rw [hlt _ hsub1]
    have hidx1 : inp.decAddr + 4 + inp.J0_strip.m + ((xs.take ci).map fun p => 2 + p.2.length).sum + 1 =
        inp.cVertsPtr ci - 1 := by rw [hptr_eq]; omega
    rw [← hidx1]
    exact hmid.2.1
  · have hlTail2' : ListAt mem₀ (inp.cVertsPtr ci) xs[ci].2 := by
      simpa [hptr_eq, add_assoc] using hmid.2.2
    refine listAt_of_congr hlTail2' fun i hi => ?_
    change i < xs[ci].2.length at hi
    have hi_h : inp.cVertsPtr ci + i < inp.h := by rw [hptr_eq]; omega
    exact hlt _ hi_h


theorem update_inc_inc (f : ℕ → ℕ) (a b z : ℕ) :
    Function.update (Function.update f a (f a + 1)) b
      ((Function.update f a (f a + 1)) b + 1) z =
    f z + (if z = a then 1 else 0) + (if z = b then 1 else 0) := by
  by_cases hzb : z = b <;> by_cases hza : z = a
  · subst hzb hza; rw [Function.update_self, Function.update_self]; simp
  · subst hzb; rw [Function.update_self, Function.update_of_ne hza]; simp [hza]
  · subst hza; rw [Function.update_of_ne hzb, Function.update_self]; simp [hzb]
  · rw [Function.update_of_ne hzb, Function.update_of_ne hza]; simp [hzb, hza]

theorem state_regs_mk (m r : ℕ → ℕ) (p : ℕ) : (State.mk m r p).regs = r := rfl
theorem state_mem_mk (m r : ℕ → ℕ) (p : ℕ) : (State.mk m r p).mem = m := rfl

theorem runs_seq_assign_flat {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {r : ℕ} {e : Expr} {s₂ : Stmt} {m₀ : ℕ → ℕ} {regs₀ : ℕ → ℕ} {pos₀ : ℕ}
    {Post : Outcome → State → Prop} {k c_bound v : ℕ}
    (he : e.eval w ⟨m₀, regs₀, pos₀⟩ = some v)
    (hrest : ∃ o st' c', Runs w p ω s₂ ⟨m₀, Function.update regs₀ r v, pos₀⟩ o st' c' ∧
      Post o st' ∧ k + e.size + 2 + c' ≤ c_bound) :
    ∃ o st' c', Runs w p ω ((Stmt.assign r e).seq s₂) ⟨m₀, regs₀, pos₀⟩ o st' c' ∧
      Post o st' ∧ k + c' ≤ c_bound := by
  rcases hrest with ⟨o, st', c', hr, hp, hc⟩
  exact ⟨o, st', e.size + 1 + c' + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, _,
    runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr, rfl⟩), hp, by omega⟩

theorem runs_seq_store_flat {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {ea ev : Expr} {s₂ : Stmt} {m₀ : ℕ → ℕ} {regs₀ : ℕ → ℕ} {pos₀ : ℕ}
    {Post : Outcome → State → Prop} {k c_bound x v : ℕ}
    (hxa : ea.eval w ⟨m₀, regs₀, pos₀⟩ = some x)
    (hxv : ev.eval w ⟨m₀, regs₀, pos₀⟩ = some v)
    (hrest : ∃ o st' c', Runs w p ω s₂ ⟨Function.update m₀ x v, regs₀, pos₀⟩ o st' c' ∧
      Post o st' ∧ k + ea.size + ev.size + 2 + c' ≤ c_bound) :
    ∃ o st' c', Runs w p ω ((Stmt.store ea ev).seq s₂) ⟨m₀, regs₀, pos₀⟩ o st' c' ∧
      Post o st' ∧ k + c' ≤ c_bound := by
  rcases hrest with ⟨o, st', c', hr, hp, hc⟩
  exact ⟨o, st', ea.size + ev.size + 1 + c' + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, _,
    runs_store_iff.mpr ⟨x, v, hxa, hxv, rfl, rfl, rfl⟩, hr, rfl⟩), hp, by omega⟩

end MinCostFlow.Spanner
