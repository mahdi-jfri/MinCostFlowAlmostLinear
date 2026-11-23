module

public import MinCostFlow.HierPaths.InitProgConnRows

/-!
# Copying one endpoint field from a row of connectors

Each connector record starts with two terminals. One scan of a row writes either endpoint
column in order. The destination follows the static input, so copying preserves the offset
table and all connector records.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The selected word is either an endpoint or the local record number. -/
def initEndpointValue (field : ℕ) (row : ℕ → List ℕ) (i : ℕ) : ℕ :=
  if field = 3 then i else (row i).getD field 0

/-- Registers 0 through 3 hold the source, record count, destination and field.
Register 4 holds the row-local connector number. -/
def initEndpointBody : Stmt :=
  .cond (.bin .eq (.reg 3) (.const 3))
    (.store (.bin .add (.reg 2) (.reg 4)) (.reg 4))
    (.store (.bin .add (.reg 2) (.reg 4))
      (.load (.bin .add
        (.bin .add (.bin .add (.reg 0) (.bin .add (.reg 1) (.const 1)))
          (.load (.bin .add (.reg 0) (.reg 4))))
        (.reg 3))))

/-- Copy a column and return the first address after it. -/
def initEndpointCopy : Stmt :=
  forRange 4 (.const 0) (.reg 1) initEndpointBody ;;
  .ret (.bin .add (.reg 2) (.reg 1))

theorem initEndpointCopy_noRand : initEndpointCopy.NoRand := by
  simp [initEndpointCopy, initEndpointBody, forRange, forUp, Stmt.NoRand]

/-- Copy the selected field of each compressed row. The source does not overlap the destination. -/
def initEndpointContract (w n : ℕ) (f : ℕ → List ℕ) : Contract where
  pre args mem := ∃ src dst field, args = [src, n, dst, field] ∧
    ListAt mem src (csrList n f) ∧ (field = 3 ∨ ∀ i < n, field < (f i).length) ∧
    src + (csrList n f).length ≤ dst ∧ dst + n < 2 ^ w ∧ 1 < 2 ^ w
  post args mem v mem' := ∃ src dst field, args = [src, n, dst, field] ∧ v = dst + n ∧
    ListAt mem' dst (tabList n (initEndpointValue field f)) ∧
    ∀ y, y < dst ∨ dst + n ≤ y → mem' y = mem y
  cost _ _ := 40 * n + 20

private theorem initEndpointBody_triple {w n src dst field i : ℕ} {p : Program}
    {f : ℕ → List ℕ} {mem : ℕ → ℕ} (hm : ListAt mem src (csrList n f))
    (hi : i < n) (hf : field = 3 ∨ field < (f i).length)
    (hsep : src + (csrList n f).length ≤ dst) (hd : dst + n < 2 ^ w) (h1w : 1 < 2 ^ w)
    (st : State) (hr0 : st.regs 0 = src) (hr1 : st.regs 1 = n)
    (hr2 : st.regs 2 = dst) (hr3 : st.regs 3 = field) (hr4 : st.regs 4 = i)
    (hframe : ∀ y < dst, st.mem y = mem y) :
    Triple w p (fun s => s = st) initEndpointBody
      (normalPost fun t => t =
        { st with mem := Function.update st.mem (dst + i) (initEndpointValue field f i) }) (fun _ => 26) := by
  have hlen : n + 1 ≤ (csrList n f).length := by rw [length_csrList]; omega
  have hthree : 3 < 2 ^ w := by omega
  intro s ω hs
  subst s
  refine runs_start_le ?_
  unfold initEndpointBody
  refine runs_cond_le (v := if field = 3 then 1 else 0)
    (Expr.eval_eq_op (Expr.eval_reg_of_eq hr3) (Expr.eval_const hthree) h1w) ?_ ?_
  · intro hn
    have he : field = 3 := by by_contra h; simp [h] at hn
    refine runs_store_le
      (Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_reg_of_eq hr4) (by omega))
      (Expr.eval_reg_of_eq hr4) ?_ ?_
    · simp [initEndpointValue, he]
    · simp [Expr.size]
  · intro hz
    have hne : field ≠ 3 := by intro h; simp [h] at hz
    have hf := hf.resolve_left hne
    have hnext := initCSRAddr_le_end (addr := src) (f := f) (i := i + 1) hi
    rw [initCSRAddr_succ] at hnext
    have hcell : initCSRAddr src n f i + field < dst := by omega
    have hrow := initCSRAddr_listAt hm hi
    have hvalue : st.mem (initCSRAddr src n f i + field) = (f i).getD field 0 := by
      rw [hframe _ hcell, List.getD_eq_getElem _ _ hf]
      exact hrow field hf
    have hoff : st.mem (src + i) = initCSRPrefix f i := by
      rw [hframe _ (by omega)]
      exact csrList_offset hm hi.le
    have hb : initCSRAddr src n f i < 2 ^ w := by omega
    have hsrcAddr : src + i < 2 ^ w := by omega
    have eo : (Expr.load (.bin .add (.reg 0) (.reg 4))).eval w st = some (initCSRPrefix f i) := Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq hr0) (Expr.eval_reg_of_eq hr4) hsrcAddr) hoff
    have ea : (Expr.bin .add (.bin .add (.reg 0) (.bin .add (.reg 1) (.const 1)))
        (.load (.bin .add (.reg 0) (.reg 4)))).eval w st = some (initCSRAddr src n f i) :=
      Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq hr0)
        (Expr.eval_add (Expr.eval_reg_of_eq hr1) (Expr.eval_const h1w) (by omega)) (by omega)) eo hb
    refine runs_store_le (Expr.eval_add (Expr.eval_reg_of_eq hr2) (Expr.eval_reg_of_eq hr4) (by omega))
      (Expr.eval_load_of_eq (Expr.eval_add ea (Expr.eval_reg_of_eq hr3) (by omega)) hvalue) ?_ ?_
    · simp [initEndpointValue, hne]
    · simp [Expr.size]

/-- The column scan returns the expected values and changes only its output words. -/
theorem initEndpointCopy_meetsContract {w n j : ℕ} {f : ℕ → List ℕ} {p : Program}
    (hp : p.procs[j]? = some initEndpointCopy) :
    MeetsContract w p j (initEndpointContract w n f) := by
  refine meetsContract_of_runs hp fun args mem pos ω _ hpre => ?_
  obtain ⟨src, dst, field, rfl, hm, hf, hsep, hd, h1w⟩ := hpre
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = dst ∧ st.regs 3 = field ∧ st.regs 4 = i ∧
      (∀ j < i, st.mem (dst + j) = initEndpointValue field f j) ∧
      (∀ y, y < dst ∨ dst + i ≤ y → st.mem y = mem y)
  let initial := startState [src, n, dst, field] mem pos
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 4) (lo := .const 0)
    (hi := .reg 1) (body := initEndpointBody) (P := fun st => st = initial) (Inv := Inv)
    26 0 n (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hst => by
      subst st
      exact ⟨Expr.eval_const (Nat.two_pow_pos w), rfl, rfl, rfl, rfl, by simp [initial, startState],
        fun _ hj => False.elim (Nat.not_lt_zero _ hj), fun _ _ => rfl⟩)
    (fun _ _ _ _ hInv => hInv.2.2.2.2.1)
    (fun _ _ _ _ hInv => Expr.eval_reg_of_eq hInv.2.1)
    (fun i _ hi => by
      intro st ω hInv
      obtain ⟨h0, h1, h2, h3, h4, hc, hfr⟩ := hInv
      obtain ⟨o, t, cost, hr, ht, hcost⟩ :=
        initEndpointBody_triple (p := p) hm hi (hf.imp_right fun h => h i hi) hsep hd h1w st h0 h1 h2 h3 h4
          (fun _ hy => hfr _ (Or.inl hy)) st ω rfl
      cases o with
      | returned => exact False.elim ht
      | normal =>
        change t = _ at ht
        subst t
        refine ⟨.normal, _, cost, hr, ⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
          by simp, ?_, ?_⟩, h4⟩, hcost⟩
        · intro j hj
          change Function.update st.mem (dst + i) (initEndpointValue field f i) (dst + j) = _
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | rfl
          · rw [Function.update_of_ne (by omega)]
            exact hc j hj'
          · rw [Function.update_self]
        · intro y hy
          change Function.update st.mem (dst + i) (initEndpointValue field f i) y = _
          rw [Function.update_of_ne (by omega)]
          exact hfr y (by omega))
  refine runs_start_le ?_
  unfold initEndpointCopy
  refine runs_seq_triple_le hloop rfl ?_
  intro st ⟨_, h1, h2, _, _, hcopied, hframe⟩
  refine runs_ret_le (v := dst + n) (Expr.eval_add (Expr.eval_reg_of_eq h2)
    (Expr.eval_reg_of_eq h1) hd) ⟨src, dst, field, rfl, rfl, ?_, hframe⟩ ?_
  · intro i hi
    have hi' : i < n := by simpa using hi
    simpa [tabList] using hcopied i hi'
  · simp only [initEndpointContract, Expr.size, Nat.sub_zero]
    omega

/-- The fields read from one connector row. -/
def initPairEndpointWords (S : StaticData) (field j c c' : ℕ) : List ℕ :=
  if c < c' then
    if field = 2 then List.replicate (S.H.conn j c c').length (pairIdxOf S.x S.b j c c')
    else if field = 3 then List.range (S.H.conn j c c').length
    else (S.H.conn j c c').map (fun q => (connWords q).getD field 0)
  else []

/-- Visit the connector rows in the same order as the concrete block. -/
def initEndpointWords (S : StaticData) (field : ℕ) : List ℕ :=
  (List.range (leafDepth S.x S.b)).flatMap fun j =>
    (List.range (numGroups S.x S.b j)).flatMap fun g =>
      (childList S.x S.b j g).flatMap fun c =>
        (childList S.x S.b j g).flatMap fun c' => initPairEndpointWords S field j c c'

theorem initEndpointWords_eq_map (S : StaticData) (field : ℕ) (hf : field < 2) :
    initEndpointWords S field =
      (connRecs S.H S.x S.b).map (fun r => if field = 0 then r.endA else r.endB) := by
  unfold initEndpointWords connRecs
  simp only [List.map_flatMap]
  congr 1; funext j; congr 1; funext g; congr 1; funext c; congr 1; funext c'
  unfold initPairEndpointWords pairRecs
  by_cases hlt : c < c'
  · have hfield : field = 0 ∨ field = 1 := by omega
    rcases hfield with rfl | rfl <;> simp [hlt, List.map_map, Function.comp_def, connWords]
  · simp [hlt]

/-- The pair-number column follows the connector numbering in `connRecs`. -/
theorem initEndpointWords_pairs_eq_map (S : StaticData) :
    initEndpointWords S 2 =
      (connRecs S.H S.x S.b).map (pairNum S.x S.b) := by
  unfold initEndpointWords connRecs
  simp only [List.map_flatMap]
  congr 1; funext j; congr 1; funext g; congr 1; funext c; congr 1; funext c'
  by_cases hlt : c < c'
  · simp [initPairEndpointWords, pairRecs, hlt, List.map_map, Function.comp_def,
      pairNum, pairIdxOf, min_eq_left hlt.le, max_eq_right hlt.le]
  · simp [initPairEndpointWords, pairRecs, hlt]

/-- Section 5 is the pair number of every connector, in connector order. -/
theorem initEndpointWords_section_pair (S : StaticData) (a : ℕ)
    (s : MinCostFlow.Spanner.PathDSAbsState) :
    (initConcrete S a s).sections.getD 5 [] = initEndpointWords S 2 := by
  rw [initEndpointWords_pairs_eq_map]
  change tabList (connRecs S.H S.x S.b).length (fun i =>
     pairNum S.x S.b ((connRecs S.H S.x S.b).getD i default)) = _
  apply List.ext_getElem (by simp)
  intro i hi _
  have hil : i < (connRecs S.H S.x S.b).length := by simpa using hi
  simp [tabList, List.getElem?_eq_getElem hil]

private theorem initEndpointWords_eq_tabList (S : StaticData) (field : ℕ) (hf : field < 2) :
    initEndpointWords S field = tabList S.numConn (fun i =>
      let r := (connRecs S.H S.x S.b).getD i default
      if field = 0 then r.endA else r.endB) := by
  rw [initEndpointWords_eq_map S field hf]
  apply List.ext_getElem
  · simp [StaticData.numConn]
  · intro i hiMap hiTab
    have hi : i < (connRecs S.H S.x S.b).length := by simpa using hiMap
    simp [tabList, List.getElem?_eq_getElem hi]

/-- The endpoint stream writes section 2 for first endpoints, section 3 for second endpoints,
and section 4 for designated endpoints, which are the first endpoints. -/
theorem initEndpointWords_sections (S : StaticData) (a : ℕ)
    (s : MinCostFlow.Spanner.PathDSAbsState) :
    (initConcrete S a s).sections.getD 2 [] = initEndpointWords S 0 ∧
    (initConcrete S a s).sections.getD 3 [] = initEndpointWords S 1 ∧
    (initConcrete S a s).sections.getD 4 [] = initEndpointWords S 0 := by
  rw [initEndpointWords_eq_tabList S 0 (by decide), initEndpointWords_eq_tabList S 1 (by decide)]
  have hdesig :
      (connSystem S.H S.x S.b S.owner S.label).desig =
        (connSystem S.H S.x S.b S.owner S.label).endA := rfl
  simp only [HierConcrete.sections, initConcrete, StaticData.model, staticArrays, List.getD_cons_succ,
    List.getD_cons_zero, hdesig, Nat.one_ne_zero, ↓reduceIte]
  exact ⟨rfl, rfl, rfl⟩

end MinCostFlow.HierPaths

end
