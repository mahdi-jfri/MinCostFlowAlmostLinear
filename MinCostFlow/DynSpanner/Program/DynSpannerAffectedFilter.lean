module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedCandA
public import MinCostFlow.DynSpanner.Program.DynGraphOps
public import MinCostFlow.DynSpanner.Program.StateLayout

import Mathlib.Tactic.Linarith

/-!
# Dynamic Spanner Edge Filtering Helpers (`DynSpannerAffectedFilter`)

Pure helpers (`findEmbLevel` fold equivalence, `walkVertices` equivalence),
`FilterCtx`, `FilterMemInv`, base-computation triple, level-lookup triple, and
walk-scanning loop triple for `dsFilterAffectedStmt`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## Pure helpers -/

lemma foldl_eq_reverse_find_getD (P : ℕ → Bool) (acc : ℕ) :
    ∀ k : ℕ, (List.range k).foldl (fun a i => if P i then i else a) acc =
      ((List.range k).reverse.find? P).getD acc := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.reverse_append, List.reverse_singleton, List.singleton_append, List.find?_cons]
    cases hPk : P k with
    | true => simp
    | false => simpa using ih

lemma findEmbLevel_eq_foldl {L j : ℕ} (inDom : Fin (L + 1) → Finset ℕ) (hj : j ≤ L) (e : ℕ) :
    findEmbLevel inDom j e =
      (List.range j).foldl
        (fun a i => if h : i < L + 1 then if e ∈ inDom ⟨i, h⟩ then i else a else a) 0 := by
  have hmin : min j (L + 1) = j := min_eq_left (by omega)
  dsimp only [findEmbLevel]
  rw [hmin, ← foldl_eq_reverse_find_getD]
  congr 1
  funext a i
  by_cases hi : i < L + 1 <;> simp [hi]

private lemma foldl_lt_bound (f : ℕ → Bool) (k : ℕ) :
    ∀ m ≤ k, ∀ acc < k,
      (List.range m).foldl (fun a i => if f i then i else a) acc < k := by
  intro m hm acc ha
  induction m generalizing acc with
  | zero => simpa using ha
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hprev := ih (by omega) acc ha
    split_ifs <;> omega

lemma findEmbLevel_lt {L j : ℕ} (inDom : Fin (L + 1) → Finset ℕ) (h1j : 1 ≤ j) (hj : j ≤ L)
    (e : ℕ) : findEmbLevel inDom j e < j ∧ findEmbLevel inDom j e < L + 1 := by
  have hlt := foldl_lt_bound
    (fun i => if h : i < L + 1 then decide (e ∈ inDom ⟨i, h⟩) else false) j j (le_refl _) 0 h1j
  have heq : (List.range j).foldl
      (fun a i => if (if h : i < L + 1 then decide (e ∈ inDom ⟨i, h⟩) else false) = true then i else a) 0 =
      findEmbLevel inDom j e := by
    rw [findEmbLevel_eq_foldl inDom hj e]
    congr 1; funext a i; split_ifs <;> simp_all
  rw [heq] at hlt
  exact ⟨hlt, by omega⟩

lemma findEmbLevel_mem {L j : ℕ} (inDom : Fin (L + 1) → Finset ℕ) (h1j : 1 ≤ j) (hj : j ≤ L)
    {e : ℕ} (he0 : e ∈ inDom ⟨0, Nat.zero_lt_succ L⟩) :
    e ∈ inDom ⟨findEmbLevel inDom j e, (findEmbLevel_lt inDom h1j hj e).2⟩ := by
  have hmin : min j (L + 1) = j := min_eq_left (by omega)
  set P : ℕ → Bool := fun i => if h : i < L + 1 then decide (e ∈ inDom ⟨i, h⟩) else false
  have h0_mem : 0 ∈ List.range j := List.mem_range.mpr h1j
  have hP0 : P 0 = true := by
    simp only [P, Nat.zero_lt_succ, dite_true, decide_eq_true_eq]
    exact he0
  have hne : ((List.range j).reverse.find? P).isSome = true := by
    rw [List.find?_isSome]
    exact ⟨0, List.mem_reverse.mpr h0_mem, hP0⟩
  rcases Option.isSome_iff_exists.mp hne with ⟨m, hm⟩
  have hfd : findEmbLevel inDom j e = m := by
    dsimp only [findEmbLevel]
    rw [hmin]
    change (((List.range j).reverse.find? P).getD 0) = m
    rw [hm]; rfl
  have hPm : P m = true := List.find?_some hm
  have hmL : m < L + 1 := (findEmbLevel_lt inDom h1j hj e).2 |> fun h => by rwa [hfd] at h
  simp only [P, dite_eq_left_of_eq_true (eq_true hmL), decide_eq_true_eq] at hPm
  simpa [hfd]

lemma walkVertices_congr_ends_of_sub {G' H_lt : MGraph}
    (hEnds : ∀ e ∈ H_lt.E, H_lt.tail e = G'.tail e ∧ H_lt.head e = G'.head e) :
    ∀ (u : ℕ) (P : List (ℕ × Bool)), (∀ x ∈ P, x.1 ∈ H_lt.E) →
      H_lt.walkVertices u P = G'.walkVertices u P := by
  intro u P hP
  simp only [MGraph.walkVertices, List.cons.injEq, true_and]
  refine List.map_congr_left fun x hx => ?_
  have hxE := hP x hx
  rcases hEnds x.1 hxE with ⟨ht, hh⟩
  cases x.2 <;> simp [MGraph.dst, ht, hh]

lemma mem_walkVertices_iff {G' : MGraph} {u : ℕ} {P : List (ℕ × Bool)} {S : Finset ℕ} :
    (∃ z ∈ G'.walkVertices u P, z ∈ S) ↔
      u ∈ S ∨ ∃ i : ℕ, ∃ hi : i < P.length, G'.dst P[i] ∈ S := by
  simp only [MGraph.walkVertices, List.mem_cons, List.mem_map]
  constructor
  · rintro ⟨z, rfl | ⟨x, hxP, rfl⟩, hzS⟩
    · exact Or.inl hzS
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxP
      exact Or.inr ⟨i, hi, hzS⟩
  · rintro (huS | ⟨i, hi, hdstS⟩)
    · exact ⟨u, Or.inl rfl, huS⟩
    · exact ⟨G'.dst P[i], Or.inr ⟨P[i], List.getElem_mem hi, rfl⟩, hdstS⟩

lemma take_succ_filter_decide {α : Type*} (xs : List α) {k : ℕ} (hk : k < xs.length)
    (P : α → Bool) :
    (xs.take (k + 1)).filter (fun x => P x) =
      (xs.take k).filter (fun x => P x) ++ if P xs[k] then [xs[k]] else [] := by
  rw [List.take_succ_eq_append_getElem hk, List.filter_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]

/-! ## Layout bounds from `b + dsFixedSize < 2 ^ w` -/

structure DsFilterLayout (b L vCap eCap w : ℕ) : Prop where
  dgs_eq : 4 + (7 * vCap + 9 * eCap) = dynGraphSize vCap eCap
  g_lt_w : dsGPtr b + dynGraphSize vCap eCap < 2 ^ w
  dom_eq : dsMinHBase b vCap eCap + (3 * eCap + 2 * (L + 1)) = dsDomGenBase b L vCap eCap
  ed_eq : dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap
  pi_eq : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap
  sb_eq : dsPiPtrBase b L vCap eCap +
    ((L + 1) * eCap + (3 * ((L + 1) * vCap) + 2 * (L + 1))) = dsSBitBase b L vCap eCap
  dom_lt_w : dsDomGenBase b L vCap eCap + (L + 1) < 2 ^ w
  ed_lt_w : dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap < 2 ^ w
  pi_lt_w : dsPiPtrBase b L vCap eCap + (L + 1) * eCap < 2 ^ w
  sb_lt_w : dsSBitBase b L vCap eCap + vCap < 2 ^ w
  dom_ge_b : b + dsHdrSize ≤ dsDomGenBase b L vCap eCap
  ed_ge_dom : dsDomGenBase b L vCap eCap ≤ dsEdgeDomGenBase b L vCap eCap
  pi_ge_ed : dsEdgeDomGenBase b L vCap eCap ≤ dsPiPtrBase b L vCap eCap
  sb_ge_pi : dsPiPtrBase b L vCap eCap ≤ dsSBitBase b L vCap eCap
  sb_le_fix : dsSBitBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap
  vCap_w : vCap < 2 ^ w
  eCap_w : eCap < 2 ^ w
  L1_w : L + 1 < 2 ^ w
  Le_w : (L + 1) * eCap < 2 ^ w
  Lv3_w : 3 * ((L + 1) * vCap) < 2 ^ w
  dgs_w : dynGraphSize vCap eCap < 2 ^ w

lemma dsFilterLayout_mk {b L vCap eCap w : ℕ}
    (hw : b + dsFixedSize L vCap eCap < 2 ^ w) :
    DsFilterLayout b L vCap eCap w := by
  have hfa := dsFixedSize_add b L vCap eCap
  have hgp : dsGPtr b = b + dsHdrSize := rfl
  have hhp : dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap := rfl
  have hap : dsAuxPtr b vCap eCap = dsHPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hmp : dsMinHBase b vCap eCap = dsAuxPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have h1 := dsDomGenBase_eq b L vCap eCap
  have hed : dsEdgeDomGenBase b L vCap eCap = dsDomGenBase b L vCap eCap + (L + 1) := rfl
  have hpi : dsPiPtrBase b L vCap eCap = dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap := rfl
  have hrg : dsRevGenBase b L vCap eCap = dsPiPtrBase b L vCap eCap + (L + 1) * eCap := rfl
  have hrh : dsRevHeadBase b L vCap eCap = dsRevGenBase b L vCap eCap + (L + 1) * vCap := rfl
  have hsg : dsSGenBase b L vCap eCap = dsRevHeadBase b L vCap eCap + (L + 1) * vCap := rfl
  have hvsg : dsVSGenBase b L vCap eCap = dsSGenBase b L vCap eCap + (L + 1) := rfl
  have hsh : dsSHeadBase b L vCap eCap = dsVSGenBase b L vCap eCap + (L + 1) * vCap := rfl
  have hsb : dsSBitBase b L vCap eCap = dsSHeadBase b L vCap eCap + (L + 1) := rfl
  have hvsb : dsVStampBase b L vCap eCap = dsSBitBase b L vCap eCap + vCap := rfl
  have h5 := dsVStampBase_eq b L vCap eCap
  have hes : dsEStampBase b L vCap eCap = dsVStampBase b L vCap eCap + vCap := rfl
  have hks : dsKeptStampBase b L vCap eCap = dsEStampBase b L vCap eCap + eCap := rfl
  have hmt : dsMEmbTempBase b L vCap eCap = dsKeptStampBase b L vCap eCap + eCap := rfl
  exact {
    dgs_eq := by dsimp only [dynGraphSize]; omega
    g_lt_w := by omega
    dom_eq := h1.symm
    ed_eq := hed.symm
    pi_eq := hpi.symm
    sb_eq := by omega
    dom_lt_w := by omega
    ed_lt_w := by omega
    pi_lt_w := by omega
    sb_lt_w := by omega
    dom_ge_b := by omega
    ed_ge_dom := by omega
    pi_ge_ed := by omega
    sb_ge_pi := by omega
    sb_le_fix := by omega
    vCap_w := by omega
    eCap_w := by omega
    L1_w := by omega
    Le_w := by omega
    Lv3_w := by omega
    dgs_w := by omega
  }

/-! ## Filter context and memory invariant -/

structure FilterCtx where
  w : ℕ
  L : ℕ
  vCap : ℕ
  eCap : ℕ
  b : ℕ
  j : ℕ
  candPtr : ℕ
  candLen : ℕ
  outArrPtr : ℕ
  G' : MGraph
  H_lt : MGraph
  inDom_mid : Fin (L + 1) → Finset ℕ
  Pi_level : Fin (L + 1) → Embedding
  piLt_mid : Embedding
  S_prev : Finset ℕ
  cand : List ℕ
  memInDom : Fin (L + 1) → Finset ℕ
  footPi : ℕ → Prop
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  h1j : 1 ≤ j
  hjL : j ≤ L
  hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w
  hcand_w : candPtr + candLen < 2 ^ w
  hout_w : outArrPtr + candLen < 2 ^ w
  hfix_out : b + dsFixedSize L vCap eCap ≤ outArrPtr
  hfoot_out : ∀ a, footPi a → a < outArrPtr ∨ outArrPtr + candLen ≤ a
  hcand_out : ∀ k < candLen, candPtr + k < outArrPtr ∨ outArrPtr + candLen ≤ candPtr + k
  hmL : mem0 (b + dsLOff) = L
  hmV : mem0 (b + dsVCapOff) = vCap
  hmE : mem0 (b + dsECapOff) = eCap
  hDG : DynGraphAt mem0 (dsGPtr b) vCap eCap G'
  hG_val : G'.IsValid
  hGV_cap : ∀ v ∈ G'.V, v < vCap
  hGE_cap : ∀ e ∈ G'.E, e < eCap
  hm_cand : ListAt mem0 candPtr cand
  hcand_len : cand.length = candLen
  hcand_nd : cand.Nodup
  hcand_sub : ∀ e ∈ cand, e ∈ G'.E ∧ e < eCap
  hH_sub : H_lt.E ⊆ G'.E
  hH_ends : H_lt.tail = G'.tail ∧ H_lt.head = G'.head
  hsBit : ∀ v < vCap, mem0 (dsSBitBase b L vCap eCap + v) = if v ∈ S_prev then 1 else 0
  hdom : ∀ i : Fin (L + 1), i.1 < j →
    ∀ e < eCap,
      (0 < mem0 (dsDomGenBase b L vCap eCap + i.1) ∧
        mem0 (dsEdgeDomGenBase b L vCap eCap + i.1 * eCap + e) =
          mem0 (dsDomGenBase b L vCap eCap + i.1)) ↔ e ∈ memInDom i
  hinDom_eq : ∀ i : Fin (L + 1), i.1 < j → inDom_mid i = memInDom i ∩ G'.E
  hinDom0 : ∀ e ∈ G'.E, e ∈ inDom_mid ⟨0, Nat.zero_lt_succ L⟩
  hpi_at : ∀ i : Fin (L + 1), i.1 < j → ∀ e ∈ inDom_mid i,
    let ptr := mem0 (dsPiPtrBase b L vCap eCap + i.1 * eCap + e)
    MWalkAt mem0 ptr (Pi_level i e) ∧
    (∀ addr, ptr ≤ addr → addr < ptr + (mWalkEncode (Pi_level i e)).length → footPi addr) ∧
    ptr + (mWalkEncode (Pi_level i e)).length < 2 ^ w
  hpi_walk : ∀ e ∈ cand, ∀ k (hk : k < (piLt_mid e).length),
    ¬ (G'.tail e ∈ S_prev ∨ ∃ i < k, ∃ hi : i < (piLt_mid e).length, G'.dst ((piLt_mid e)[i]'hi) ∈ S_prev) →
    ((piLt_mid e)[k]'hk).1 ∈ H_lt.E
  hpiLt_eq : piLt_mid = piLtFrom Pi_level inDom_mid j

theorem FilterCtx.lay (c : FilterCtx) : DsFilterLayout c.b c.L c.vCap c.eCap c.w :=
  dsFilterLayout_mk c.hfix_w

def FilterFixedRegs (c : FilterCtx) (st : State) : Prop :=
  st.regs 0 = c.b ∧ st.regs 1 = c.j ∧ st.regs 2 = c.candPtr ∧
  st.regs 3 = c.candLen ∧ st.regs 4 = c.outArrPtr ∧
  st.regs 5 = c.vCap ∧ st.regs 6 = c.eCap ∧ st.regs 7 = c.L ∧
  st.regs 8 = dsDomGenBase c.b c.L c.vCap c.eCap ∧
  st.regs 9 = dsEdgeDomGenBase c.b c.L c.vCap c.eCap ∧
  st.regs 10 = dsPiPtrBase c.b c.L c.vCap c.eCap ∧
  st.regs 11 = dsSBitBase c.b c.L c.vCap c.eCap ∧
  st.regs 13 = dsGPtr c.b

lemma FilterFixedRegs.agree {c : FilterCtx} {st st' : State} (h : FilterFixedRegs c st)
    (hr : ∀ r ≤ 13, r ≠ 12 → st'.regs r = st.regs r) : FilterFixedRegs c st' := by
  rcases h with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r13⟩
  exact ⟨(hr 0 (by omega) (by omega)).trans r0, (hr 1 (by omega) (by omega)).trans r1,
    (hr 2 (by omega) (by omega)).trans r2, (hr 3 (by omega) (by omega)).trans r3,
    (hr 4 (by omega) (by omega)).trans r4, (hr 5 (by omega) (by omega)).trans r5,
    (hr 6 (by omega) (by omega)).trans r6, (hr 7 (by omega) (by omega)).trans r7,
    (hr 8 (by omega) (by omega)).trans r8, (hr 9 (by omega) (by omega)).trans r9,
    (hr 10 (by omega) (by omega)).trans r10, (hr 11 (by omega) (by omega)).trans r11,
    (hr 13 (by omega) (by omega)).trans r13⟩

lemma FilterFixedRegs.r0 {c : FilterCtx} {st : State} (h : FilterFixedRegs c st) : st.regs 0 = c.b := h.1
lemma FilterFixedRegs.r1 {c : FilterCtx} {st : State} (h : FilterFixedRegs c st) : st.regs 1 = c.j := h.2.1
lemma FilterFixedRegs.r5 {c : FilterCtx} {st : State} (h : FilterFixedRegs c st) : st.regs 5 = c.vCap := h.2.2.2.2.2.1
lemma FilterFixedRegs.r6 {c : FilterCtx} {st : State} (h : FilterFixedRegs c st) : st.regs 6 = c.eCap := h.2.2.2.2.2.2.1
lemma FilterFixedRegs.r8 {c : FilterCtx} {st : State} (h : FilterFixedRegs c st) : st.regs 8 = dsDomGenBase c.b c.L c.vCap c.eCap := h.2.2.2.2.2.2.2.2.1
lemma FilterFixedRegs.r9 {c : FilterCtx} {st : State} (h : FilterFixedRegs c st) : st.regs 9 = dsEdgeDomGenBase c.b c.L c.vCap c.eCap := h.2.2.2.2.2.2.2.2.2.1
lemma FilterFixedRegs.r11 {c : FilterCtx} {st : State} (h : FilterFixedRegs c st) : st.regs 11 = dsSBitBase c.b c.L c.vCap c.eCap := h.2.2.2.2.2.2.2.2.2.2.2.1
lemma FilterFixedRegs.r13 {c : FilterCtx} {st : State} (h : FilterFixedRegs c st) : st.regs 13 = dsGPtr c.b := h.2.2.2.2.2.2.2.2.2.2.2.2

def FilterMemInv (c : FilterCtx) (idx : ℕ) (st : State) : Prop :=
  let eAff := (c.cand.take idx).filter fun e => decide (e ∈ affectedEdges c.G' c.H_lt c.piLt_mid c.S_prev)
  FilterFixedRegs c st ∧
  st.regs 14 = idx ∧
  st.regs 12 = eAff.length ∧
  eAff.length ≤ idx ∧
  ListAt st.mem c.outArrPtr eAff ∧
  ∀ addr, (addr < c.outArrPtr ∨ c.outArrPtr + c.candLen ≤ addr) → st.mem addr = c.mem0 addr

lemma FilterMemInv.read_fix {c : FilterCtx} {idx : ℕ} {st : State} (h : FilterMemInv c idx st)
    {addr : ℕ} (ha : addr < c.b + dsFixedSize c.L c.vCap c.eCap) : st.mem addr = c.mem0 addr :=
  h.2.2.2.2.2 addr (Or.inl (lt_of_lt_of_le ha c.hfix_out))

lemma FilterMemInv.read_cand {c : FilterCtx} {idx : ℕ} {st : State} (h : FilterMemInv c idx st)
    {k : ℕ} (hk : k < c.candLen) :
    st.mem (c.candPtr + k) = c.cand[k]'(by have := c.hcand_len; omega) := by
  rw [h.2.2.2.2.2 _ (c.hcand_out k hk)]
  simpa using c.hm_cand k (by have := c.hcand_len; omega)

lemma FilterMemInv.of_regs_agree {c : FilterCtx} {idx : ℕ} {st st' : State}
    (h : FilterMemInv c idx st) (hmem : st'.mem = st.mem)
    (hr : ∀ r ≤ 14, r ≠ 12 → st'.regs r = st.regs r) (hr12 : st'.regs 12 = st.regs 12) :
    FilterMemInv c idx st' := by
  rcases h with ⟨hf, h14, h12, hle, hlist, hfr⟩
  exact ⟨hf.agree (fun r hr' hn12 => hr r (by omega) hn12),
    (hr 14 (by omega) (by omega)).trans h14, hr12.trans h12, hle,
    by simpa [hmem] using hlist, fun addr ha => (congrFun hmem addr).trans (hfr addr ha)⟩

lemma FilterMemInv.dynGraphAt {c : FilterCtx} {idx : ℕ} {st : State} (h : FilterMemInv c idx st) :
    DynGraphAt st.mem (dsGPtr c.b) c.vCap c.eCap c.G' := by
  refine dynGraphAt_of_agree c.hDG fun addr _ hhi => ?_
  have hlt_fix : addr < c.b + dsFixedSize c.L c.vCap c.eCap := by
    have := dsFixedSize_ge_aux c.b c.L c.vCap c.eCap
    have : dsGPtr c.b + dynGraphSize c.vCap c.eCap ≤ dsAuxPtr c.b c.vCap c.eCap + dynGraphSize c.vCap c.eCap := by
      simp only [dsAuxPtr, dsHPtr]; omega
    omega
  exact h.read_fix hlt_fix

lemma FilterMemInv.read_sBit {c : FilterCtx} {idx : ℕ} {st : State} (h : FilterMemInv c idx st)
    {v : ℕ} (hv : v < c.vCap) :
    st.mem (dsSBitBase c.b c.L c.vCap c.eCap + v) = if v ∈ c.S_prev then 1 else 0 := by
  rw [h.read_fix (lt_of_lt_of_le (Nat.add_lt_add_left hv _) c.lay.sb_le_fix), c.hsBit v hv]

/-! ## Prefix bases triple -/

lemma dsFilterAffected_bases_triple (c : FilterCtx) {p : Program} :
    Triple c.w p
      (fun st => st.mem = c.mem0 ∧ st.regs 0 = c.b ∧ st.regs 1 = c.j ∧
        st.regs 2 = c.candPtr ∧ st.regs 3 = c.candLen ∧ st.regs 4 = c.outArrPtr)
      (.assign 5 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
       .assign 6 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
       .assign 7 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
       .assign 12 (.bin .add (.const 4)
         (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 9) (.reg 6)))) ;;
       .assign 8 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize)) (.bin .mul (.const 3) (.reg 12))) ;;
       .assign 8 (.bin .add (.reg 8)
         (.bin .add (.bin .mul (.const 3) (.reg 6)) (.bin .mul (.const 2) (.bin .add (.reg 7) (.const 1))))) ;;
       .assign 9 (.bin .add (.reg 8) (.bin .add (.reg 7) (.const 1))) ;;
       .assign 10 (.bin .add (.reg 9) (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 6))) ;;
       .assign 11 (.bin .add (.reg 10)
         (.bin .add (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 6))
           (.bin .add (.bin .mul (.const 3) (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 5)))
             (.bin .mul (.const 2) (.bin .add (.reg 7) (.const 1)))))) ;;
       .assign 12 (.const 0) ;;
       .assign 13 (.bin .add (.reg 0) (.const dsHdrSize)))
      (normalPost fun st =>
        st.mem = c.mem0 ∧ FilterFixedRegs c st ∧ st.regs 12 = 0)
      (fun _ => 115) := by
  have hlay := c.lay
  have hw16 := c.hw16
  have hb_w : c.b < 2 ^ c.w := by
    have := dsFixedSize_pos c.L c.vCap c.eCap; have := c.hfix_w; omega
  have hbv_w : c.b + dsVCapOff < 2 ^ c.w := by
    have : dsVCapOff < dsHdrSize := by decide
    have := hlay.g_lt_w; dsimp only [dsGPtr, dynGraphSize] at this; omega
  have hbe_w : c.b + dsECapOff < 2 ^ c.w := by
    have : dsECapOff < dsHdrSize := by decide
    have := hlay.g_lt_w; dsimp only [dsGPtr, dynGraphSize] at this; omega
  have hbl_w : c.b + dsLOff < 2 ^ c.w := by
    have : dsLOff < dsHdrSize := by decide
    have := hlay.g_lt_w; dsimp only [dsGPtr, dynGraphSize] at this; omega
  have hbh_w : c.b + dsHdrSize < 2 ^ c.w := by
    have := hlay.g_lt_w; dsimp only [dsGPtr, dynGraphSize] at this; omega
  have h7v_w : 7 * c.vCap < 2 ^ c.w := by have := hlay.dgs_w; dsimp only [dynGraphSize] at this; omega
  have h9e_w : 9 * c.eCap < 2 ^ c.w := by have := hlay.dgs_w; dsimp only [dynGraphSize] at this; omega
  have h7v9e_w : 7 * c.vCap + 9 * c.eCap < 2 ^ c.w := by
    have := hlay.dgs_w; dsimp only [dynGraphSize] at this; omega
  have h3dgs_w : 3 * dynGraphSize c.vCap c.eCap < 2 ^ c.w := by
    have := dsMinHBase_eq c.b c.vCap c.eCap; have := hlay.dom_eq; have := hlay.dom_lt_w; omega
  have hmin_w : dsMinHBase c.b c.vCap c.eCap < 2 ^ c.w := by
    have := hlay.dom_eq; have := hlay.dom_lt_w; omega
  have h3e_w : 3 * c.eCap < 2 ^ c.w := by
    have := hlay.dom_eq; have := hlay.dom_lt_w; omega
  have h2L_w : 2 * (c.L + 1) < 2 ^ c.w := by
    have := hlay.dom_eq; have := hlay.dom_lt_w; omega
  have h3e2L_w : 3 * c.eCap + 2 * (c.L + 1) < 2 ^ c.w := by
    have := hlay.dom_eq; have := hlay.dom_lt_w; omega
  have hsub_sb_w : (c.L + 1) * c.eCap + (3 * ((c.L + 1) * c.vCap) + 2 * (c.L + 1)) < 2 ^ c.w := by
    have := hlay.sb_eq; have := hlay.sb_lt_w; omega
  have hrhs_sb_w : 3 * ((c.L + 1) * c.vCap) + 2 * (c.L + 1) < 2 ^ c.w := by omega
  have hLv_w : (c.L + 1) * c.vCap < 2 ^ c.w := by have := hlay.Lv3_w; omega
  intro st ω ⟨hmem, r0, r1, r2, r3, r4⟩
  suffices hres : ∃ o st' c_1,
      Runs c.w p ω
        (.assign 5 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
         .assign 6 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
         .assign 7 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
         .assign 12 (.bin .add (.const 4)
           (.bin .add (.bin .mul (.const 7) (.reg 5)) (.bin .mul (.const 9) (.reg 6)))) ;;
         .assign 8 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize)) (.bin .mul (.const 3) (.reg 12))) ;;
         .assign 8 (.bin .add (.reg 8)
           (.bin .add (.bin .mul (.const 3) (.reg 6)) (.bin .mul (.const 2) (.bin .add (.reg 7) (.const 1))))) ;;
         .assign 9 (.bin .add (.reg 8) (.bin .add (.reg 7) (.const 1))) ;;
         .assign 10 (.bin .add (.reg 9) (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 6))) ;;
         .assign 11 (.bin .add (.reg 10)
           (.bin .add (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 6))
             (.bin .add (.bin .mul (.const 3) (.bin .mul (.bin .add (.reg 7) (.const 1)) (.reg 5)))
               (.bin .mul (.const 2) (.bin .add (.reg 7) (.const 1)))))) ;;
         .assign 12 (.const 0) ;;
         .assign 13 (.bin .add (.reg 0) (.const dsHdrSize)))
        st o st' c_1 ∧
        normalPost (fun st => st.mem = c.mem0 ∧ FilterFixedRegs c st ∧ st.regs 12 = 0) o st' ∧
        0 + c_1 ≤ 115 by
    rcases hres with ⟨o, st', c_1, hr, hq, hc⟩
    dsimp only; exact ⟨o, st', c_1, hr, hq, by omega⟩
  refine runs_seq_assign_le (v := c.vCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0)
      (Expr.eval_const (by omega)) hbv_w)
      (by rw [hmem, c.hmV])) ?_
  refine runs_seq_assign_le (v := c.eCap)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (r := 0) (v := c.b) (by simp [r0]))
      (Expr.eval_const (by omega)) hbe_w)
      (by simp [hmem, c.hmE])) ?_
  refine runs_seq_assign_le (v := c.L)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (r := 0) (v := c.b) (by simp [r0]))
      (Expr.eval_const (by omega)) hbl_w)
      (by simp [hmem, c.hmL])) ?_
  refine runs_seq_assign_le (v := dynGraphSize c.vCap c.eCap)
    (by
      have h4_eq : dynGraphSize c.vCap c.eCap = 4 + (7 * c.vCap + 9 * c.eCap) := by
        dsimp only [dynGraphSize]; ring
      rw [h4_eq]
      exact Expr.eval_add (Expr.eval_const (by omega))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (by simp)) h7v_w)
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_reg_of_eq (by simp)) h9e_w) h7v9e_w)
        (by have := hlay.dgs_w; dsimp only [dynGraphSize] at this; omega)) ?_
  refine runs_seq_assign_le (v := dsMinHBase c.b c.vCap c.eCap)
    (by
      rw [dsMinHBase_eq]
      exact Expr.eval_add
        (Expr.eval_add (Expr.eval_reg_of_eq (r := 0) (v := c.b) (by simp [r0]))
          (Expr.eval_const (by have : dsHdrSize = 6 := rfl; omega)) hbh_w)
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h3dgs_w)
        (by have := dsMinHBase_eq c.b c.vCap c.eCap; omega)) ?_
  refine runs_seq_assign_le (v := dsDomGenBase c.b c.L c.vCap c.eCap)
    (by
      rw [← hlay.dom_eq]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add
          (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp)) h3e_w)
          (Expr.eval_mul (Expr.eval_const (by omega))
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) hlay.L1_w) h2L_w)
          h3e2L_w) (by have := hlay.dom_eq; have := hlay.dom_lt_w; omega)) ?_
  refine runs_seq_assign_le (v := dsEdgeDomGenBase c.b c.L c.vCap c.eCap)
    (by
      rw [← hlay.ed_eq]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) hlay.L1_w)
        (by have := hlay.ed_eq; have := hlay.ed_lt_w; omega)) ?_
  refine runs_seq_assign_le (v := dsPiPtrBase c.b c.L c.vCap c.eCap)
    (by
      rw [← hlay.pi_eq]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_mul
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) hlay.L1_w)
          (Expr.eval_reg_of_eq (by simp)) hlay.Le_w)
        (by have := hlay.pi_eq; have := hlay.pi_lt_w; omega)) ?_
  refine runs_seq_assign_le (v := dsSBitBase c.b c.L c.vCap c.eCap)
    (by
      rw [← hlay.sb_eq]
      exact Expr.eval_add (Expr.eval_reg_of_eq (by simp))
        (Expr.eval_add
          (Expr.eval_mul
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) hlay.L1_w)
            (Expr.eval_reg_of_eq (by simp)) hlay.Le_w)
          (Expr.eval_add
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_mul
                (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) hlay.L1_w)
                (Expr.eval_reg_of_eq (by simp)) hLv_w) hlay.Lv3_w)
            (Expr.eval_mul (Expr.eval_const (by omega))
              (Expr.eval_add (Expr.eval_reg_of_eq (by simp)) (Expr.eval_const (by omega)) hlay.L1_w) h2L_w)
            hrhs_sb_w)
          hsub_sb_w)
        (by have := hlay.sb_eq; have := hlay.sb_lt_w; omega)) ?_
  refine runs_seq_assign_le (Expr.eval_const (by omega)) ?_
  refine runs_assign_le
    (Expr.eval_add (Expr.eval_reg_of_eq (r := 0) (v := c.b) (by simp [r0]))
      (Expr.eval_const (by have : dsHdrSize = 6 := rfl; omega)) hbh_w)
    ?_ (by dsimp only [Expr.size]; omega)
  · exact ⟨by simp [hmem], ⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp [dsGPtr]⟩,
      by simp⟩

/-! ## Level lookup inner `forRange` (`findEmbLevel`) -/

lemma dsFilterAffected_findLevel_triple (c : FilterCtx) {p : Program}
    {idx e : ℕ} (he_G : e ∈ c.G'.E) (he_cap : e < c.eCap)
    (rInit : ℕ → ℕ) :
    Triple c.w p
      (fun st => FilterMemInv c idx st ∧ st.regs 15 = e ∧ st.regs 16 = 0 ∧
        ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r)
      (forRange 17 (.const 0) (.reg 1)
        (.assign 18 (.load (.bin .add (.reg 8) (.reg 17))) ;;
         .cond (.reg 18)
           (.cond (.bin .eq (.load (.bin .add (.reg 9) (.bin .add (.bin .mul (.reg 17) (.reg 6)) (.reg 15)))) (.reg 18))
             (.assign 16 (.reg 17))
             .nop)
           .nop))
      (normalPost fun st => FilterMemInv c idx st ∧ st.regs 15 = e ∧
        st.regs 16 = findEmbLevel c.inDom_mid c.j e ∧
        ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r)
      (fun _ => 35 * c.j + 7) := by
  have hlay := c.lay
  have hw16 := c.hw16
  let stepFn : ℕ → ℕ → ℕ := fun acc i =>
    if hi : i < c.L + 1 then if e ∈ c.inDom_mid ⟨i, hi⟩ then i else acc else acc
  let InvL : ℕ → State → Prop := fun i st =>
    FilterMemInv c idx st ∧
    st.regs 15 = e ∧
    st.regs 16 = (List.range i).foldl stepFn 0 ∧
    st.regs 17 = i ∧
    ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r
  have ht := Triple.forRange_const (w := c.w) (p := p)
    (P := fun st => FilterMemInv c idx st ∧ st.regs 15 = e ∧ st.regs 16 = 0 ∧
      ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r)
    (r := 17) (lo := .const 0) (hi := .reg 1)
    (body :=
      .assign 18 (.load (.bin .add (.reg 8) (.reg 17))) ;;
      .cond (.reg 18)
        (.cond (.bin .eq (.load (.bin .add (.reg 9) (.bin .add (.bin .mul (.reg 17) (.reg 6)) (.reg 15)))) (.reg 18))
          (.assign 16 (.reg 17))
          .nop)
        .nop)
    (Inv := InvL) 26 0 c.j
    (Nat.zero_le _) (by omega)
    (fun _ => lt_of_le_of_lt c.hjL (Nat.lt_trans (Nat.lt_succ_self _) hlay.L1_w))
    (fun st ⟨hfm, r15, r16, hfr⟩ => by
      refine ⟨Expr.eval_const (by omega), ?_⟩
      exact ⟨FilterMemInv.of_regs_agree hfm rfl
        (fun r hr _ => by simp [show r ≠ 17 by omega]) (by simp),
        by simp [r15], by simp [r16], by simp,
        fun r hr h12 => by simp [show r ≠ 17 by omega, hfr r hr h12]⟩)
    (fun i st _ _ hL => hL.2.2.2.1)
    (fun i st _ _ hL => by simp [Expr.eval, hL.1.1.r1])
    (fun i _ hi => by
      intro st ω ⟨hfm, r15, r16, r17, hfr⟩
      have hiL1 : i < c.L + 1 := by have := c.hjL; omega
      have hdg_lt_fix : dsDomGenBase c.b c.L c.vCap c.eCap + i <
          c.b + dsFixedSize c.L c.vCap c.eCap := by
        have := hlay.ed_eq; have := hlay.pi_eq; have := hlay.sb_eq; have := hlay.sb_le_fix; omega
      have hdg_w : dsDomGenBase c.b c.L c.vCap c.eCap + i < 2 ^ c.w := by
        have := hlay.dom_lt_w; omega
      have hdg_mem : st.mem (dsDomGenBase c.b c.L c.vCap c.eCap + i) =
          c.mem0 (dsDomGenBase c.b c.L c.vCap c.eCap + i) := hfm.read_fix hdg_lt_fix
      have hie_lt : i * c.eCap + e < (c.L + 1) * c.eCap := by
        have h1 : i * c.eCap + e < i * c.eCap + c.eCap := by omega
        have h2 : (i + 1) * c.eCap ≤ (c.L + 1) * c.eCap := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.succ_mul] at h2; omega
      have hie_w : i * c.eCap + e < 2 ^ c.w := lt_trans hie_lt hlay.Le_w
      have hie_mul_w : i * c.eCap < 2 ^ c.w := by omega
      have hed_lt_fix : dsEdgeDomGenBase c.b c.L c.vCap c.eCap + (i * c.eCap + e) <
          c.b + dsFixedSize c.L c.vCap c.eCap := by
        have := hlay.pi_eq; have := hlay.sb_eq; have := hlay.sb_le_fix; omega
      have hed_w : dsEdgeDomGenBase c.b c.L c.vCap c.eCap + (i * c.eCap + e) < 2 ^ c.w := by
        have := hlay.ed_lt_w; omega
      have hed_mem : st.mem (dsEdgeDomGenBase c.b c.L c.vCap c.eCap + (i * c.eCap + e)) =
          c.mem0 (dsEdgeDomGenBase c.b c.L c.vCap c.eCap + i * c.eCap + e) := by
        rw [hfm.read_fix hed_lt_fix, ← Nat.add_assoc]
      set dg := c.mem0 (dsDomGenBase c.b c.L c.vCap c.eCap + i)
      set eg := c.mem0 (dsEdgeDomGenBase c.b c.L c.vCap c.eCap + i * c.eCap + e)
      suffices hres : ∃ o st' c_1,
          Runs c.w p ω
            (.assign 18 (.load (.bin .add (.reg 8) (.reg 17))) ;;
             .cond (.reg 18)
               (.cond (.bin .eq (.load (.bin .add (.reg 9) (.bin .add (.bin .mul (.reg 17) (.reg 6)) (.reg 15)))) (.reg 18))
                 (.assign 16 (.reg 17))
                 .nop)
               .nop) st o st' c_1 ∧
            normalPost (fun st' => InvL (i + 1) { st' with regs := Function.update st'.regs 17 (i + 1) } ∧ st'.regs 17 = i) o st' ∧
            0 + c_1 ≤ 26 by
        rcases hres with ⟨o, st', c_1, hr, hq, hc⟩
        dsimp only; exact ⟨o, st', c_1, hr, hq, by omega⟩
      refine runs_seq_assign_le
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hfm.1.r8)
          (Expr.eval_reg_of_eq r17) hdg_w) hdg_mem) ?_
      have hdom_iff : (0 < dg ∧ eg = dg) ↔ e ∈ c.inDom_mid ⟨i, hiL1⟩ := by
        have hdom0 := c.hdom ⟨i, hiL1⟩ hi e he_cap
        rw [c.hinDom_eq ⟨i, hiL1⟩ hi, Finset.mem_inter]
        exact ⟨fun h => ⟨hdom0.mp h, he_G⟩, fun h => hdom0.mpr h.1⟩
      refine runs_cond_le (v := dg) (Expr.eval_reg_of_eq (r := 18) (v := dg) (by simp)) ?_ ?_
      · intro hdg_nz
        have hdg_pos : 0 < dg := Nat.pos_of_ne_zero hdg_nz
        refine runs_cond_le (v := if eg = dg then 1 else 0)
          (Expr.eval_eq_op
            (Expr.eval_load_of_eq
              (Expr.eval_add
                (Expr.eval_reg_of_eq (by simp [hfm.1.r9]))
                (Expr.eval_add
                  (Expr.eval_mul (Expr.eval_reg_of_eq (by simp [r17]))
                    (Expr.eval_reg_of_eq (by simp [hfm.1.r6])) hie_mul_w)
                  (Expr.eval_reg_of_eq (by simp [r15])) hie_w)
                hed_w)
              (by simpa using hed_mem))
            (Expr.eval_reg_of_eq (r := 18) (v := dg) (by simp))
            (by omega)) ?_ ?_
        · intro heg_nz
          have he_in : e ∈ c.inDom_mid ⟨i, hiL1⟩ :=
            hdom_iff.mp ⟨hdg_pos, by by_contra hne; simp [hne] at heg_nz⟩
          refine runs_assign_le (Expr.eval_reg_of_eq (r := 17) (v := i) (by simp [r17])) ?_
            (by dsimp only [Expr.size]; omega)
          refine ⟨⟨FilterMemInv.of_regs_agree hfm rfl
            (fun r hr _ => by simp [show r ≠ 17 by omega, show r ≠ 16 by omega, show r ≠ 18 by omega])
            (by simp),
            by simp [r15], ?_, by simp,
            fun r hr h12 => by simp [show r ≠ 17 by omega, show r ≠ 16 by omega, show r ≠ 18 by omega, hfr r hr h12]⟩,
            by simp [r17]⟩
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          dsimp only [stepFn]
          simp only [Function.update_of_ne (by decide : (16 : ℕ) ≠ 17), Function.update_self]
          rw [dite_eq_left_of_eq_true (eq_true hiL1)]
          simp only [eq_true he_in, ↓reduceIte]
        · intro heg_z
          have he_nin : e ∉ c.inDom_mid ⟨i, hiL1⟩ :=
            fun hmem => by simp [(hdom_iff.mpr hmem).2] at heg_z
          refine runs_nop_le ?_ (by dsimp only [Expr.size]; omega)
          refine ⟨⟨FilterMemInv.of_regs_agree hfm rfl
            (fun r hr _ => by simp [show r ≠ 17 by omega, show r ≠ 18 by omega]) (by simp),
            by simp [r15], ?_, by simp,
            fun r hr h12 => by simp [show r ≠ 17 by omega, show r ≠ 18 by omega, hfr r hr h12]⟩,
            by simp [r17]⟩
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          dsimp only [stepFn]
          simp only [Function.update_of_ne (by decide : (16 : ℕ) ≠ 17),
            Function.update_of_ne (by decide : (16 : ℕ) ≠ 18), r16]
          rw [dite_eq_left_of_eq_true (eq_true hiL1)]
          simp only [eq_false he_nin, ↓reduceIte]
          rfl
      · intro hdg_z
        have he_nin : e ∉ c.inDom_mid ⟨i, hiL1⟩ := fun hmem => by
          have := (hdom_iff.mpr hmem).1; omega
        refine runs_nop_le ?_ (by dsimp only [Expr.size]; omega)
        refine ⟨⟨FilterMemInv.of_regs_agree hfm rfl
          (fun r hr _ => by simp [show r ≠ 17 by omega, show r ≠ 18 by omega]) (by simp),
          by simp [r15], ?_, by simp,
          fun r hr h12 => by simp [show r ≠ 17 by omega, show r ≠ 18 by omega, hfr r hr h12]⟩,
          by simp [r17]⟩
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        dsimp only [stepFn]
        simp only [Function.update_of_ne (by decide : (16 : ℕ) ≠ 17),
          Function.update_of_ne (by decide : (16 : ℕ) ≠ 18), r16]
        rw [dite_eq_left_of_eq_true (eq_true hiL1)]
        simp only [eq_false he_nin, ↓reduceIte]
        rfl)
  refine ht.conseq (fun st h => h) (fun o st' h => by
      cases o with
      | returned _ => exact h
      | normal =>
        refine ⟨h.1, h.2.1, ?_, h.2.2.2.2⟩
        rw [h.2.2.1, findEmbLevel_eq_foldl c.inDom_mid c.hjL e])
    fun st _ => by dsimp only [Expr.size]; omega

/-! ## Walk scanning loop (`loop ((r21 < r20) * (r19 == 0))`) -/

lemma dsFilterAffected_walkLoop_triple (c : FilterCtx) {p : Program} {bOps : ℕ}
    (hpOps : p.HasAt bOps dgOpsProcs)
    {idx e ptr : ℕ} (P : List (ℕ × Bool))
    (hP_walk : ∀ k (hk : k < P.length),
      ¬ (c.G'.tail e ∈ c.S_prev ∨ ∃ i < k, ∃ hi : i < P.length, c.G'.dst (P[i]'hi) ∈ c.S_prev) →
      (P[k]'hk).1 ∈ c.H_lt.E)
    (hptr_walk : MWalkAt c.mem0 ptr P)
    (hptr_foot : ∀ addr, ptr ≤ addr → addr < ptr + (mWalkEncode P).length → c.footPi addr)
    (hptr_w : ptr + (mWalkEncode P).length < 2 ^ c.w)
    (_he_G : e ∈ c.G'.E)
    (rInit : ℕ → ℕ) :
    Triple c.w p
      (fun st => FilterMemInv c idx st ∧ st.regs 15 = e ∧ st.regs 17 = ptr ∧
        st.regs 19 = (if c.G'.tail e ∈ c.S_prev then 1 else 0) ∧
        st.regs 20 = P.length ∧ st.regs 21 = 0 ∧
        ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r)
      (.loop (.bin .mul (.bin .lt (.reg 21) (.reg 20)) (.bin .eq (.reg 19) (.const 0)))
        (.assign 22 (.load (.bin .add (.reg 17) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 21))))) ;;
         .assign 23 (.load (.bin .add (.reg 17) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 21))))) ;;
         .cond (.reg 23)
           (.call 18 (bOps + dgIdxGetHead) [.reg 13, .reg 22])
           (.call 18 (bOps + dgIdxGetTail) [.reg 13, .reg 22]) ;;
         .cond (.load (.bin .add (.reg 11) (.reg 18))) (.assign 19 (.const 1)) .nop ;;
         .assign 21 (.bin .add (.reg 21) (.const 1))))
      (normalPost fun st => FilterMemInv c idx st ∧ st.regs 15 = e ∧
        st.regs 19 = (if ∃ z ∈ c.G'.walkVertices (c.G'.tail e) P, z ∈ c.S_prev then 1 else 0) ∧
        ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r)
      (fun _ => 96 * P.length + 10) := by
  have hlay := c.lay
  have hw16 := c.hw16
  have hPlen_w : P.length < 2 ^ c.w := by have := mWalkEncode_length P; omega
  let hitPrefix : ℕ → Prop := fun k =>
    c.G'.tail e ∈ c.S_prev ∨ ∃ i < k, ∃ hi : i < P.length, c.G'.dst (P[i]'hi) ∈ c.S_prev
  let InvW : State → Prop := fun st =>
    ∃ k ≤ P.length,
      FilterMemInv c idx st ∧
      st.regs 15 = e ∧ st.regs 17 = ptr ∧
      st.regs 19 = (if hitPrefix k then 1 else 0) ∧
      st.regs 20 = P.length ∧ st.regs 21 = k ∧
      ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r
  let mFn : State → ℕ := fun st => P.length - st.regs 21
  let remFn : State → ℕ := fun st => 96 * (P.length - st.regs 21) + 10
  have hmem_walk : ∀ st, FilterMemInv c idx st →
      MWalkAt st.mem ptr P := fun st hfm =>
    hptr_walk.of_agree fun addr ha1 ha2 => by
      refine hfm.2.2.2.2.2 addr (c.hfoot_out addr (hptr_foot addr ha1 ?_))
      have := mWalkEncode_length P; omega
  exact (Triple.loop_measure (w := c.w) (p := p)
    (Inv := InvW)
    (Q := normalPost fun st => FilterMemInv c idx st ∧ st.regs 15 = e ∧
      st.regs 19 = (if ∃ z ∈ c.G'.walkVertices (c.G'.tail e) P, z ∈ c.S_prev then 1 else 0) ∧
      ∀ r ≤ 15, r ≠ 12 → st.regs r = rInit r)
    (condVal := fun st =>
      (if st.regs 21 < P.length then 1 else 0) * (if st.regs 19 = 0 then 1 else 0))
    (m := mFn) (rem := remFn)
    (fun st ⟨k, hk, _, _, _, _, hr20, hr21, _⟩ => by
      refine Expr.eval_mul
        (Expr.eval_lt_op (Expr.eval_reg_of_eq (v := st.regs 21) rfl)
          (Expr.eval_reg_of_eq hr20) (by omega))
        (Expr.eval_eq_op (Expr.eval_reg_of_eq rfl) (Expr.eval_const (by omega)) (by omega))
        (by split_ifs <;> omega))
    (fun st ⟨k, hk, hfm, hr15, _, hr19, _, hr21, hfr⟩ hzero => by
      have hhit_iff : (∃ z ∈ c.G'.walkVertices (c.G'.tail e) P, z ∈ c.S_prev) ↔ hitPrefix k := by
        rw [mem_walkVertices_iff]
        dsimp only [hitPrefix]
        rcases eq_or_lt_of_le hk with rfl | hlt
        · exact or_congr_right ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, hi, h⟩, fun ⟨i, _, hi, h⟩ => ⟨i, hi, h⟩⟩
        · have hnot0 : st.regs 19 ≠ 0 := by
            intro hz
            rw [hz, hr21] at hzero
            simp [hlt] at hzero
          have hhp : hitPrefix k := by
            by_contra hnh; simp [hnh] at hr19; exact hnot0 hr19
          exact ⟨fun _ => hhp, by rintro (h | ⟨i, _, hi, hd⟩); exact Or.inl h; exact Or.inr ⟨i, hi, hd⟩⟩
      refine ⟨?_, by dsimp only [remFn, Expr.size]; omega⟩
      simp only [normalPost]
      refine ⟨hfm, hr15, ?_, hfr⟩
      have hite : (if ∃ z ∈ c.G'.walkVertices (c.G'.tail e) P, z ∈ c.S_prev then (1 : ℕ) else 0) =
          if hitPrefix k then 1 else 0 :=
        if_congr hhit_iff rfl rfl
      rw [hr19, hite])
    (fun st ⟨k, hk, hfm, hr15, hr17, hr19, hr20, hr21, hfr⟩ hnz => by
      have hk_lt : k < P.length := by
        by_contra hge
        have : ¬ (st.regs 21 < P.length) := by omega
        simp [this] at hnz
      have hr19_z : st.regs 19 = 0 := by
        by_contra hne
        simp [hne] at hnz
      have hnhit : ¬ hitPrefix k := by
        intro hh; simp [hh] at hr19; exact absurd hr19_z (by omega)
      set x := P[k]
      have hxH : x.1 ∈ c.H_lt.E := hP_walk k hk_lt hnhit
      have hxG : x.1 ∈ c.G'.E := c.hH_sub hxH
      have hm_P := hmem_walk st hfm
      have h2k_lt : 1 + 2 * k < 2 ^ c.w := by have := mWalkEncode_length P; omega
      have h2k2_lt : 2 + 2 * k < 2 ^ c.w := by have := mWalkEncode_length P; omega
      have ha1_lt : ptr + (1 + 2 * k) < 2 ^ c.w := by have := mWalkEncode_length P; omega
      have ha2_lt : ptr + (2 + 2 * k) < 2 ^ c.w := by have := mWalkEncode_length P; omega
      have hed_eq : st.mem (ptr + (1 + 2 * k)) = x.1 := by
        have := MWalkAt_step_edge hm_P hk_lt
        simpa [Nat.add_assoc] using this
      have hdir_eq : st.mem (ptr + (2 + 2 * k)) = if x.2 then 1 else 0 := by
        have := MWalkAt_step_dir hm_P hk_lt
        simpa [show ptr + 1 + 2 * k + 1 = ptr + (2 + 2 * k) by omega] using this
      have hev22 : (Expr.load (.bin .add (.reg 17) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 21))))).eval c.w st = some x.1 :=
        Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq hr17)
            (Expr.eval_add (Expr.eval_const (by omega))
              (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hr21) (by omega))
              h2k_lt) ha1_lt) hed_eq
      refine ⟨88, fun s ω hs => ?_⟩
      · subst s
        suffices hres : ∃ o st' c_1,
            Runs c.w p ω
              (.assign 22 (.load (.bin .add (.reg 17) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 21))))) ;;
               .assign 23 (.load (.bin .add (.reg 17) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 21))))) ;;
               .cond (.reg 23)
                 (.call 18 (bOps + dgIdxGetHead) [.reg 13, .reg 22])
                 (.call 18 (bOps + dgIdxGetTail) [.reg 13, .reg 22]) ;;
               .cond (.load (.bin .add (.reg 11) (.reg 18))) (.assign 19 (.const 1)) .nop ;;
               .assign 21 (.bin .add (.reg 21) (.const 1)))
              st o st' c_1 ∧
              (match o with
              | .returned u => normalPost (fun _ => False) (.returned u) st'
              | .normal => InvW st' ∧ mFn st' < mFn st ∧ 7 + 88 + remFn st' + 1 ≤ remFn st) ∧
              0 + c_1 ≤ 88 by
          rcases hres with ⟨o, st', c_1, hr, hq, hc⟩
          dsimp only [Expr.size]
          cases o with
          | returned u => exact absurd hq (by simp [normalPost])
          | normal => exact ⟨.normal, st', c_1, hr, hq, by omega⟩
        refine runs_seq_assign_le hev22 ?_
        have hev23 : (Expr.load (.bin .add (.reg 17) (.bin .add (.const 2) (.bin .mul (.const 2) (.reg 21))))).eval c.w
            { st with regs := Function.update st.regs 22 x.1 } = some (if x.2 then 1 else 0) :=
          Expr.eval_load_of_eq
            (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hr17]))
              (Expr.eval_add (Expr.eval_const (by omega))
                (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [hr21])) (by omega))
                h2k2_lt) ha2_lt) (by simp [hdir_eq])
        refine runs_seq_assign_le hev23 ?_
        let dst := c.G'.dst x
        have hdst_V : dst ∈ c.G'.V := by
          rcases c.hG_val x.1 hxG with ⟨hv1, hv2⟩
          cases hxb : x.2 <;> simp [dst, MGraph.dst, hxb, hv1, hv2]
        have hdst_cap : dst < c.vCap := c.hGV_cap dst hdst_V
        have hdst_w : dst < 2 ^ c.w := lt_trans hdst_cap hlay.vCap_w
        have hsb_dst_w : dsSBitBase c.b c.L c.vCap c.eCap + dst < 2 ^ c.w := by
          have := hlay.sb_lt_w; omega
        have hx1_w : x.1 < 2 ^ c.w := lt_trans (c.hGE_cap x.1 hxG) hlay.eCap_w
        have hg_w : dsGPtr c.b < 2 ^ c.w := by
          have := hlay.g_lt_w; dsimp only [dynGraphSize] at this; omega
        have hcont : ∀ (mem1 : ℕ → ℕ), mem1 = st.mem →
            ∀ (v18 : ℕ), v18 = dst →
            ∀ pos',
            let stC : State :=
              { mem := mem1
                regs := Function.update
                  (Function.update (Function.update st.regs 22 x.1) 23 (if x.2 then 1 else 0))
                  18 v18
                pos := pos' }
            ∃ o st' c_2,
              Runs c.w p ω
                (.cond (.load (.bin .add (.reg 11) (.reg 18))) (.assign 19 (.const 1)) .nop ;;
                 .assign 21 (.bin .add (.reg 21) (.const 1)))
                stC o st' c_2 ∧
              (match o with
              | .returned u => False
              | .normal => InvW st' ∧ mFn st' < mFn st ∧ 7 + 88 + remFn st' + 1 ≤ remFn st) ∧
              73 + c_2 ≤ 88 := by
          intro mem1 hmem1 v18 hv18 pos' stC
          have hsb_v : stC.mem (dsSBitBase c.b c.L c.vCap c.eCap + dst) =
              if dst ∈ c.S_prev then 1 else 0 := by
            dsimp only [stC]; rw [hmem1]; exact hfm.read_sBit hdst_cap
          have hev_sb : (Expr.load (.bin .add (.reg 11) (.reg 18))).eval c.w stC =
              some (if dst ∈ c.S_prev then 1 else 0) :=
            Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (by dsimp only [stC]; simp [hfm.1.r11]))
                (Expr.eval_reg_of_eq (r := 18) (v := dst) (by dsimp only [stC]; rw [Function.update_self, hv18]))
                hsb_dst_w)
              hsb_v
          refine runs_seq_cond_le hev_sb ?_ ?_
          · intro hhit_nz
            have hdst_S : dst ∈ c.S_prev := by by_contra hns; simp [hns] at hhit_nz
            refine runs_seq_assign_le (Expr.eval_const (by omega)) ?_
            refine runs_assign_le
              (Expr.eval_add (Expr.eval_reg_of_eq (r := 21) (v := k) (by dsimp only [stC]; simp [hr21]))
                (Expr.eval_const (by omega)) (by omega)) ?_ (by dsimp only [Expr.size]; omega)
            have hhit1 : hitPrefix (k + 1) :=
              Or.inr ⟨k, Nat.lt_succ_self k, hk_lt, hdst_S⟩
            refine ⟨⟨k + 1, Nat.succ_le_of_lt hk_lt,
              FilterMemInv.of_regs_agree hfm (by dsimp only [stC]; exact hmem1)
                (fun r hr _ => by dsimp only [stC]; simp [show r ≠ 21 by omega, show r ≠ 19 by omega, show r ≠ 18 by omega, show r ≠ 23 by omega, show r ≠ 22 by omega])
                (by dsimp only [stC]; simp [hfm.2.2.1]),
              by dsimp only [stC]; simp [hr15], by dsimp only [stC]; simp [hr17],
              by dsimp only [stC]; simp [hhit1], by dsimp only [stC]; simp [hr20],
              by dsimp only [stC]; simp,
              fun r hr h12 => by dsimp only [stC]; simp [show r ≠ 21 by omega, show r ≠ 19 by omega, show r ≠ 18 by omega, show r ≠ 23 by omega, show r ≠ 22 by omega, hfr r hr h12]⟩,
              by dsimp only [mFn, remFn, stC]; simp [hr21]; omega⟩
          · intro hhit_z
            have hdst_nS : dst ∉ c.S_prev := fun h => by simp [h] at hhit_z
            have hnhit1 : ¬ hitPrefix (k + 1) := by
              rintro (h | ⟨i, hi, hiP, hdi⟩)
              · exact hnhit (Or.inl h)
              · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt' | rfl
                · exact hnhit (Or.inr ⟨i, hlt', hiP, hdi⟩)
                · exact hdst_nS hdi
            refine runs_seq_nop_le ?_
            refine runs_assign_le
              (Expr.eval_add (Expr.eval_reg_of_eq (r := 21) (v := k) (by dsimp only [stC]; simp [hr21]))
                (Expr.eval_const (by omega)) (by omega)) ?_ (by dsimp only [Expr.size]; omega)
            refine ⟨⟨k + 1, Nat.succ_le_of_lt hk_lt,
              FilterMemInv.of_regs_agree hfm (by dsimp only [stC]; exact hmem1)
                (fun r hr _ => by dsimp only [stC]; simp [show r ≠ 21 by omega, show r ≠ 18 by omega, show r ≠ 23 by omega, show r ≠ 22 by omega])
                (by dsimp only [stC]; simp [hfm.2.2.1]),
              by dsimp only [stC]; simp [hr15], by dsimp only [stC]; simp [hr17],
              by dsimp only [stC]; simp [hr19_z, hnhit1], by dsimp only [stC]; simp [hr20],
              by dsimp only [stC]; simp,
              fun r hr h12 => by dsimp only [stC]; simp [show r ≠ 21 by omega, show r ≠ 18 by omega, show r ≠ 23 by omega, show r ≠ 22 by omega, hfr r hr h12]⟩,
              by dsimp only [mFn, remFn, stC]; simp [hr21]; omega⟩
        refine runs_seq_cond_le (v := if x.2 then 1 else 0)
          (Expr.eval_reg_of_eq (r := 23) (v := if x.2 then 1 else 0) (by simp)) ?_ ?_
        · intro hx2_nz
          have hx2 : x.2 = true := by by_contra hf; simp [hf] at hx2_nz
          refine runs_seq_call_le (dgGetHead_meetsContract (w := c.w) (vCap := c.vCap) (eCap := c.eCap) (G := c.G') hpOps)
            (by simp [evalArgs, Expr.eval, hfm.1.r13])
            (fun a ha => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
              rcases ha with rfl | rfl; exact hg_w; exact hx1_w)
            ⟨dsGPtr c.b, x.1, rfl, c.hw16, hlay.g_lt_w, hxG, hfm.dynGraphAt⟩ ?_
          intro v mem' pos' ⟨_, _, rfl, hmem', hv⟩
          have hdv : v = dst := by rw [hv]; simp [dst, MGraph.dst, hx2]
          rcases hcont mem' hmem' v hdv pos' with ⟨o, st', c_2, hr2, hq2, hc2⟩
          exact ⟨o, st', c_2, hr2, hq2, by dsimp only [argsSize, Expr.size, dgGetHeadContract] at hc2 ⊢; omega⟩
        · intro hx2_z
          have hx2 : x.2 = false := by by_contra ht; simp [ht] at hx2_z
          refine runs_seq_call_le (dgGetTail_meetsContract (w := c.w) (vCap := c.vCap) (eCap := c.eCap) (G := c.G') hpOps)
            (by simp [evalArgs, Expr.eval, hfm.1.r13])
            (fun a ha => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
              rcases ha with rfl | rfl; exact hg_w; exact hx1_w)
            ⟨dsGPtr c.b, x.1, rfl, c.hw16, hlay.g_lt_w, hxG, hfm.dynGraphAt⟩ ?_
          intro v mem' pos' ⟨_, _, rfl, hmem', hv⟩
          have hdv : v = dst := by rw [hv]; simp [dst, MGraph.dst, hx2]
          rcases hcont mem' hmem' v hdv pos' with ⟨o, st', c_2, hr2, hq2, hc2⟩
          exact ⟨o, st', c_2, hr2, hq2, by dsimp only [argsSize, Expr.size, dgGetTailContract] at hc2 ⊢; omega⟩)).conseq
    (fun st ⟨hfm, hr15, hr17, hr19, hr20, hr21, hfr⟩ =>
      ⟨0, Nat.zero_le _, hfm, hr15, hr17, by simpa [hitPrefix] using hr19, hr20, hr21, hfr⟩)
    (fun _ _ h => h)
    (fun st ⟨_, _, _, _, _, hr21, _⟩ => by dsimp only [remFn]; rw [hr21]; omega)

end

end MinCostFlow.DynSpanner.Program
