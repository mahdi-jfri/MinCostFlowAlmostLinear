module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedDefs
public import MinCostFlow.DynSpanner.Program.DynSpannerAffectedUpdateS

import Mathlib.Tactic.Linarith

/-!
# Dynamic Spanner Candidate Collection: Contract, Helpers & Phase A

Defines `dsCollectCandContract` and `dsCollectCandFrameCond`, proves reusable pure helpers
(`llPtr`, `listAt_*`, `filterCandFold`, `DsCandLayout`), and proves the Word-RAM Phase A triple
(`dsCollectCand_bases_triple` and `dsCollectCand_phaseA_triple`) extracting `S_prev = S_level (j - 1)`.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

@[expose] public section

/-! ## Contract specification -/

/-- Candidate rev-list length sum over levels `0 ≤ i < j` and vertices `v ∈ sPrev`. -/
def candRevSum (L j : ℕ) (revLists : Fin (L + 1) → ℕ → List ℕ) (sPrev : List ℕ) : ℕ :=
  (Finset.range j).sum fun i =>
    (sPrev.map fun v => if hi : i < L + 1 then (revLists ⟨i, hi⟩ v).length else 0).sum

/-- Frame addresses preserved outside `dsGenOff`, `sBit`, `eStamp`, and `[heapPtr, ret)`. -/
def dsCollectCandFrameCond (L vCap eCap b heapPtr ret addr : ℕ) : Prop :=
  addr ≠ b + dsGenOff ∧
  (∀ v < vCap, addr ≠ dsSBitBase b L vCap eCap + v) ∧
  (∀ e < eCap, addr ≠ dsEStampBase b L vCap eCap + e) ∧
  (addr < heapPtr ∨ ret ≤ addr)

/-- Contract for `dsCollectCandStmt`.
`args = [b, j, heapPtr]`. Returns `ret = heapPtr + 2 + sPrevList.length + cand.length`. -/
def dsCollectCandContract (w L vCap eCap b j : ℕ) (G' : MGraph)
    (S_prev : Finset ℕ) (sPrevList : List ℕ)
    (revLists : Fin (L + 1) → ℕ → List ℕ) (footS footRev : ℕ → Prop) : Contract where
  pre args mem := ∃ heapPtr,
    args = [b, j, heapPtr] ∧
    16 ≤ 2 ^ w ∧ 1 ≤ j ∧ j ≤ L ∧
    b + dsFixedSize L vCap eCap ≤ heapPtr ∧
    heapPtr + 2 + vCap + eCap < 2 ^ w ∧
    mem (b + dsLOff) = L ∧ mem (b + dsVCapOff) = vCap ∧ mem (b + dsECapOff) = eCap ∧
    1 ≤ mem (b + dsGenOff) ∧ mem (b + dsGenOff) + 1 < 2 ^ w ∧
    DynGraphAt mem (dsGPtr b) vCap eCap G' ∧ G'.IsValid ∧
    (∀ e ∈ G'.E, e < eCap) ∧
    (∀ a, footS a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr) ∧
    (∀ a, footRev a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr) ∧
    (∀ v ∈ S_prev, v < vCap) ∧
    sPrevList.Nodup ∧ (∀ v, v ∈ sPrevList ↔ v ∈ S_prev) ∧
    0 < mem (dsSGenBase b L vCap eCap + (j - 1)) ∧
    mem (dsSGenBase b L vCap eCap + (j - 1)) ≤ mem (b + dsGenOff) ∧
    LinkedListIn footS mem (mem (dsSHeadBase b L vCap eCap + (j - 1))) sPrevList ∧
    (∀ v < vCap, mem (dsSBitBase b L vCap eCap + v) = 0) ∧
    (∀ e < eCap, mem (dsEStampBase b L vCap eCap + e) ≤ mem (b + dsGenOff)) ∧
    (∀ i : Fin (L + 1), i.1 < j → mem (dsDomGenBase b L vCap eCap + i.1) ≤ mem (b + dsGenOff)) ∧
    (∀ i : Fin (L + 1), i.1 < j → ∀ v ∈ S_prev,
      mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem (b + dsGenOff) ∧
      (if 0 < mem (dsDomGenBase b L vCap eCap + i.1) ∧
          mem (dsRevGenBase b L vCap eCap + i.1 * vCap + v) = mem (dsDomGenBase b L vCap eCap + i.1)
       then LinkedListIn footRev mem (mem (dsRevHeadBase b L vCap eCap + i.1 * vCap + v)) (revLists i v)
       else revLists i v = []) ∧
      (∀ e ∈ revLists i v, e < eCap))
  post args mem ret mem' := ∃ heapPtr cand,
    args = [b, j, heapPtr] ∧
    cand.Nodup ∧
    ret = heapPtr + 2 + sPrevList.length + cand.length ∧
    ret ≤ heapPtr + 2 + vCap + eCap ∧
    mem' heapPtr = sPrevList.length ∧
    mem' (heapPtr + 1) = cand.length ∧
    ListAt mem' (heapPtr + 2) sPrevList ∧
    ListAt mem' (heapPtr + 2 + sPrevList.length) cand ∧
    (∀ v < vCap, mem' (dsSBitBase b L vCap eCap + v) = if v ∈ S_prev then 1 else 0) ∧
    (∀ e, e ∈ cand ↔ e ∈ G'.E ∧ ∃ i : Fin (L + 1), ∃ v ∈ S_prev, i.1 < j ∧ e ∈ revLists i v) ∧
    (∀ e ∈ cand, e < eCap) ∧
    mem' (b + dsGenOff) = mem (b + dsGenOff) + 1 ∧
    (∀ e < eCap, mem' (dsEStampBase b L vCap eCap + e) ≤ mem (b + dsGenOff) + 1) ∧
    ∀ addr, dsCollectCandFrameCond L vCap eCap b heapPtr ret addr → mem' addr = mem addr
  cost args _ :=
    let jArg := args[1]?.getD 0
    100 * candRevSum L jArg revLists sPrevList +
      100 * (jArg * sPrevList.length) + 100 * sPrevList.length + 100 * jArg + 450

/-! ## Pure list, `ListAt`, and `LinkedListIn` pointer helpers -/

lemma list_length_le_of_nodup_lt {xs : List ℕ} {cap : ℕ}
    (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x < cap) : xs.length ≤ cap := by
  have hsub : xs.toFinset ⊆ Finset.range cap := fun x hx =>
    Finset.mem_range.mpr (hlt x (List.mem_toFinset.mp hx))
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at hcard
  exact hcard

lemma listAt_of_agree {mem mem' : ℕ → ℕ} {a : ℕ} {xs : List ℕ}
    (h : ∀ k < xs.length, mem' (a + k) = mem (a + k))
    (ha : ListAt mem a xs) : ListAt mem' a xs :=
  fun k hk => (h k hk).trans (ha k hk)

lemma listAt_snoc {mem : ℕ → ℕ} {a : ℕ} {xs : List ℕ} {x : ℕ}
    (hxs : ListAt mem a xs) (hx : mem (a + xs.length) = x) :
    ListAt mem a (xs ++ [x]) := by
  intro k hk
  by_cases hlt : k < xs.length
  · rw [List.getElem_append_left hlt]; exact hxs k hlt
  · have hlen : (xs ++ [x]).length = xs.length + 1 := by simp
    have hkeq : k = xs.length := by omega
    subst hkeq; simp [hx]

lemma listAt_get {mem : ℕ → ℕ} {a : ℕ} {xs : List ℕ} {k : ℕ}
    (hk : k < xs.length) (h : ListAt mem a xs) : mem (a + k) = xs[k] :=
  h k hk

def llPtr (mem : ℕ → ℕ) (head : ℕ) : ℕ → ℕ
  | 0 => head
  | k + 1 => mem (llPtr mem head k + 1)

lemma llPtr_succ {mem : ℕ → ℕ} {head k : ℕ} :
    llPtr mem head (k + 1) = llPtr mem (mem (head + 1)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change mem (llPtr mem head (k + 1) + 1) = mem (llPtr mem (mem (head + 1)) k + 1)
    rw [ih]

lemma llPtr_zero {foot : ℕ → Prop} {mem : ℕ → ℕ} {head : ℕ} {xs : List ℕ} :
    LinkedListIn foot mem head xs → llPtr mem head xs.length = 0 := by
  induction xs generalizing head with
  | nil => intro h; exact h
  | cons _ _ ih =>
    intro ⟨_, _, _, _, hnext⟩
    simp only [List.length_cons]
    rw [llPtr_succ]
    exact ih hnext

lemma llPtr_step_spec {foot : ℕ → Prop} {mem : ℕ → ℕ} {head : ℕ} {xs : List ℕ}
    (hL : LinkedListIn foot mem head xs) :
    ∀ k (hk : k < xs.length),
      0 < llPtr mem head k ∧
      foot (llPtr mem head k) ∧
      foot (llPtr mem head k + 1) ∧
      mem (llPtr mem head k) = xs[k] ∧
      llPtr mem head (k + 1) = mem (llPtr mem head k + 1) := by
  induction xs generalizing head with
  | nil => intro k hk; simp at hk
  | cons _ _ ih =>
    intro k hk
    rcases hL with ⟨hpos, hf0, hf1, hx, hnext⟩
    cases k with
    | zero => exact ⟨hpos, hf0, hf1, hx, rfl⟩
    | succ k' =>
      simpa [llPtr_succ] using ih hnext k' (Nat.succ_lt_succ_iff.mp hk)

lemma llPtr_shift {mem : ℕ → ℕ} {head a b : ℕ} :
    llPtr mem head (a + b) = llPtr mem (llPtr mem head a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, llPtr, ih]; rfl

lemma llPtr_inj {foot : ℕ → Prop} {mem : ℕ → ℕ} {head : ℕ} {xs : List ℕ}
    (hL : LinkedListIn foot mem head xs) {a b : ℕ} (ha : a ≤ xs.length) (hb : b ≤ xs.length)
    (heq : llPtr mem head a = llPtr mem head b) : a = b := by
  wlog hab : a ≤ b generalizing a b
  · exact (this hb ha heq.symm (Nat.le_of_not_ge hab)).symm
  by_contra hne
  have hlt : a < b := lt_of_le_of_ne hab hne
  set d := xs.length - b
  have had : a + d < xs.length := by omega
  have h0 : llPtr mem head (a + d) = 0 := by
    rw [llPtr_shift, heq, ← llPtr_shift, show b + d = xs.length by omega]
    exact llPtr_zero hL
  have hpos := (llPtr_step_spec hL (a + d) had).1
  omega

lemma llPtr_lt_w {foot : ℕ → Prop} {mem : ℕ → ℕ} {head heapPtr w : ℕ} {xs : List ℕ}
    (hL : LinkedListIn foot mem head xs) (hfoot : ∀ a, foot a → a < heapPtr)
    (hh_lt : heapPtr < 2 ^ w) :
    ∀ k ≤ xs.length, llPtr mem head k < 2 ^ w := by
  intro k hk
  rcases eq_or_lt_of_le hk with rfl | hlt
  · rw [llPtr_zero hL]; omega
  · exact lt_trans (hfoot _ (llPtr_step_spec hL k hlt).2.1) hh_lt

def filterCandStep (G : MGraph) (cand : List ℕ) (e : ℕ) : List ℕ :=
  if e ∈ G.E ∧ e ∉ cand then cand ++ [e] else cand

def filterCandFold (G : MGraph) (cand : List ℕ) (es : List ℕ) : List ℕ :=
  es.foldl (filterCandStep G) cand

lemma filterCandStep_props {G : MGraph} {eCap e : ℕ} {cand : List ℕ}
    (hnd : cand.Nodup) (hsub : ∀ x ∈ cand, x ∈ G.E ∧ x < eCap) (he : e < eCap) :
    (filterCandStep G cand e).Nodup ∧
    (∀ x ∈ filterCandStep G cand e, x ∈ G.E ∧ x < eCap) ∧
    (∀ x, x ∈ filterCandStep G cand e ↔ x ∈ cand ∨ (x ∈ G.E ∧ x = e)) := by
  dsimp only [filterCandStep]
  split_ifs with h
  · refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton e, fun x hx y hy hxy => by
        subst hxy; rw [List.mem_singleton] at hy; subst hy; exact h.2 hx⟩,
      fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl; exact hsub x hx; exact ⟨h.1, he⟩,
      fun x => by
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (hx | rfl); exact Or.inl hx; exact Or.inr ⟨h.1, rfl⟩
        · rintro (hx | ⟨_, rfl⟩); exact Or.inl hx; exact Or.inr rfl⟩
  · exact ⟨hnd, hsub, fun x => by
      simp only [not_and, not_not] at h
      constructor
      · intro hx; exact Or.inl hx
      · rintro (hx | ⟨hxE, rfl⟩); exact hx; exact h hxE⟩

lemma filterCandFold_props {G : MGraph} {eCap : ℕ} :
    ∀ {es cand : List ℕ},
      cand.Nodup → (∀ x ∈ cand, x ∈ G.E ∧ x < eCap) → (∀ e ∈ es, e < eCap) →
      (filterCandFold G cand es).Nodup ∧
      (∀ x ∈ filterCandFold G cand es, x ∈ G.E ∧ x < eCap) ∧
      (∀ x, x ∈ filterCandFold G cand es ↔ x ∈ cand ∨ (x ∈ G.E ∧ x ∈ es))
  | [], cand, hnd, hsub, _ => ⟨hnd, hsub, fun x => by simp [filterCandFold]⟩
  | e :: es, cand, hnd, hsub, hes => by
    have h1 := filterCandStep_props hnd hsub (hes e List.mem_cons_self)
    have h2 := filterCandFold_props (es := es) (cand := filterCandStep G cand e)
      h1.1 h1.2.1 (fun x hx => hes x (List.mem_cons_of_mem e hx))
    refine ⟨h2.1, h2.2.1, fun x => ?_⟩
    rw [filterCandFold, List.foldl_cons]
    have hfold : es.foldl (filterCandStep G) (filterCandStep G cand e) =
        filterCandFold G (filterCandStep G cand e) es := rfl
    rw [hfold, h2.2.2 x, h1.2.2 x, List.mem_cons]
    tauto

/-! ## Layout and base computation -/

structure DsCandLayout (b L vCap eCap heapPtr w : ℕ) : Prop where
  dgs_eq : 4 + (7 * vCap + 9 * eCap) = dynGraphSize vCap eCap
  min_eq : b + dsHdrSize + 3 * dynGraphSize vCap eCap = dsMinHBase b vCap eCap
  dom_eq : dsMinHBase b vCap eCap + (3 * eCap + 2 * (L + 1)) = dsDomGenBase b L vCap eCap
  revg_eq : dsDomGenBase b L vCap eCap + ((L + 1) + 2 * ((L + 1) * eCap)) = dsRevGenBase b L vCap eCap
  revh_eq : dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap
  sg_eq : dsRevHeadBase b L vCap eCap + (L + 1) * vCap = dsSGenBase b L vCap eCap
  sh_eq : dsSGenBase b L vCap eCap + (L + 1) + (L + 1) * vCap = dsSHeadBase b L vCap eCap
  sb_eq : dsSHeadBase b L vCap eCap + (L + 1) = dsSBitBase b L vCap eCap
  es_eq : dsSBitBase b L vCap eCap + 2 * vCap = dsEStampBase b L vCap eCap
  epres_eq : b + (dsHdrSize + 4) + 7 * vCap = dgEPresBase (dsGPtr b) vCap
  es_lt_fix : dsEStampBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap
  ep_lt_fix : dgEPresBase (dsGPtr b) vCap + eCap ≤ b + dsFixedSize L vCap eCap
  b_lt_dom : b + dsGenOff < dsDomGenBase b L vCap eCap
  dom_lt_revg : dsDomGenBase b L vCap eCap + (L + 1) ≤ dsRevGenBase b L vCap eCap
  revg_lt_revh : dsRevGenBase b L vCap eCap + (L + 1) * vCap ≤ dsRevHeadBase b L vCap eCap
  revh_lt_sg : dsRevHeadBase b L vCap eCap + (L + 1) * vCap ≤ dsSGenBase b L vCap eCap
  sg_lt_sh : dsSGenBase b L vCap eCap + (L + 1) ≤ dsSHeadBase b L vCap eCap
  sh_lt_sb : dsSHeadBase b L vCap eCap + (L + 1) ≤ dsSBitBase b L vCap eCap
  sb_lt_es : dsSBitBase b L vCap eCap + vCap ≤ dsEStampBase b L vCap eCap
  hp_lt_w : heapPtr < 2 ^ w
  L1_w : L + 1 < 2 ^ w
  vCap_w : vCap < 2 ^ w
  eCap_w : eCap < 2 ^ w
  b_w : b < 2 ^ w
  dgs_w : dynGraphSize vCap eCap < 2 ^ w
  min_w : dsMinHBase b vCap eCap < 2 ^ w
  dom_w : dsDomGenBase b L vCap eCap < 2 ^ w
  revg_w : dsRevGenBase b L vCap eCap < 2 ^ w
  revh_w : dsRevHeadBase b L vCap eCap < 2 ^ w
  sg_w : dsSGenBase b L vCap eCap < 2 ^ w
  sh_w : dsSHeadBase b L vCap eCap < 2 ^ w
  sb_w : dsSBitBase b L vCap eCap < 2 ^ w
  es_w : dsEStampBase b L vCap eCap < 2 ^ w
  ep_w : dgEPresBase (dsGPtr b) vCap < 2 ^ w

lemma dsCandLayout_mk {b L vCap eCap heapPtr w : ℕ}
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hh_lt : heapPtr + 2 + vCap + eCap < 2 ^ w) :
    DsCandLayout b L vCap eCap heapPtr w := by
  have h1 := dsMinHBase_eq b vCap eCap
  have h2 := dsDomGenBase_eq b L vCap eCap
  have h3 := dsRevGenBase_eq b L vCap eCap
  have h4 := dsRevHeadBase_eq b L vCap eCap
  have hm := dsMEmbTempBase_eq_rev b L vCap eCap
  have hfa := dsFixedSize_add b L vCap eCap
  have hes_eq : dsSBitBase b L vCap eCap + 2 * vCap = dsEStampBase b L vCap eCap :=
    dsSBitBase_add_double_vCap b L vCap eCap
  have hsb : dsSBitBase b L vCap eCap = dsSHeadBase b L vCap eCap + (L + 1) := rfl
  have hsg1 : dsSGenBase b L vCap eCap = dsRevHeadBase b L vCap eCap + (L + 1) * vCap := rfl
  have hvsg1 : dsVSGenBase b L vCap eCap = dsSGenBase b L vCap eCap + (L + 1) := rfl
  have hsh1 : dsSHeadBase b L vCap eCap = dsVSGenBase b L vCap eCap + (L + 1) * vCap := rfl
  have hgp : dsGPtr b = b + dsHdrSize := rfl
  have hhp : dsHPtr b vCap eCap = dsGPtr b + dynGraphSize vCap eCap := rfl
  have hap : dsAuxPtr b vCap eCap = dsHPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have hmp : dsMinHBase b vCap eCap = dsAuxPtr b vCap eCap + dynGraphSize vCap eCap := rfl
  have dep : dgEPresBase (dsGPtr b) vCap = dsGPtr b + 4 + 7 * vCap := rfl
  have hdgs : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hdg : dsGenOff < dsHdrSize := by decide
  have hmin_eq : b + dsHdrSize + 3 * dynGraphSize vCap eCap = dsMinHBase b vCap eCap := by
    linarith only [hgp, hhp, hap, hmp]
  have hdom_eq : dsMinHBase b vCap eCap + (3 * eCap + 2 * (L + 1)) =
      dsDomGenBase b L vCap eCap := h2.symm
  have hrevg_eq : dsDomGenBase b L vCap eCap + ((L + 1) + 2 * ((L + 1) * eCap)) =
      dsRevGenBase b L vCap eCap := by linarith only [h2, h3]
  have hrevh_eq : dsRevGenBase b L vCap eCap + (L + 1) * vCap = dsRevHeadBase b L vCap eCap := h4.symm
  have hsg_eq : dsRevHeadBase b L vCap eCap + (L + 1) * vCap = dsSGenBase b L vCap eCap := hsg1.symm
  have hsh_eq : dsSGenBase b L vCap eCap + (L + 1) + (L + 1) * vCap =
      dsSHeadBase b L vCap eCap := by linarith only [hvsg1, hsh1]
  have hsb_eq : dsSHeadBase b L vCap eCap + (L + 1) = dsSBitBase b L vCap eCap := hsb.symm
  have hep_eq : b + (dsHdrSize + 4) + 7 * vCap = dgEPresBase (dsGPtr b) vCap := by
    linarith only [hgp, dep]
  have hm_rev : dsMEmbTempBase b L vCap eCap =
      dsEStampBase b L vCap eCap + 2 * eCap := by
    linarith only [hm, h4, hsg1, hvsg1, hsh1, hsb, hes_eq]
  have hes_fix : dsEStampBase b L vCap eCap + eCap ≤ b + dsFixedSize L vCap eCap := by
    omega
  have hep_min : dgEPresBase (dsGPtr b) vCap + eCap ≤ dsMinHBase b vCap eCap := by
    rw [← hmin_eq, ← hep_eq, hdgs]; omega
  have hmin_dom : dsMinHBase b vCap eCap ≤ dsDomGenBase b L vCap eCap :=
    hdom_eq ▸ Nat.le_add_right _ _
  have hdom_revg : dsDomGenBase b L vCap eCap ≤ dsRevGenBase b L vCap eCap :=
    hrevg_eq ▸ Nat.le_add_right _ _
  have hrevg_revh : dsRevGenBase b L vCap eCap ≤ dsRevHeadBase b L vCap eCap :=
    hrevh_eq ▸ Nat.le_add_right _ _
  have hrevh_sg : dsRevHeadBase b L vCap eCap ≤ dsSGenBase b L vCap eCap :=
    hsg_eq ▸ Nat.le_add_right _ _
  have hsg_sh : dsSGenBase b L vCap eCap ≤ dsSHeadBase b L vCap eCap :=
    hsh_eq ▸ Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hsh_sb : dsSHeadBase b L vCap eCap ≤ dsSBitBase b L vCap eCap :=
    hsb_eq ▸ Nat.le_add_right _ _
  have hsb_es : dsSBitBase b L vCap eCap ≤ dsEStampBase b L vCap eCap :=
    hes_eq ▸ Nat.le_add_right _ _
  have hmin_es : dsMinHBase b vCap eCap ≤ dsEStampBase b L vCap eCap := by omega
  have hep_fix : dgEPresBase (dsGPtr b) vCap + eCap ≤ b + dsFixedSize L vCap eCap := by
    omega
  have hes_w : dsEStampBase b L vCap eCap < 2 ^ w := by omega
  have hsb_w : dsSBitBase b L vCap eCap < 2 ^ w := by omega
  have hsh_w : dsSHeadBase b L vCap eCap < 2 ^ w := by omega
  have hsg_w : dsSGenBase b L vCap eCap < 2 ^ w := by omega
  have hrevh_w : dsRevHeadBase b L vCap eCap < 2 ^ w := by omega
  have hrevg_w : dsRevGenBase b L vCap eCap < 2 ^ w := by omega
  have hdom_w : dsDomGenBase b L vCap eCap < 2 ^ w := by omega
  have hmin_w : dsMinHBase b vCap eCap < 2 ^ w := by omega
  exact {
    dgs_eq := by omega
    min_eq := hmin_eq
    dom_eq := hdom_eq
    revg_eq := hrevg_eq
    revh_eq := hrevh_eq
    sg_eq := hsg_eq
    sh_eq := hsh_eq
    sb_eq := hsb_eq
    es_eq := hes_eq
    epres_eq := hep_eq
    es_lt_fix := hes_fix
    ep_lt_fix := hep_fix
    b_lt_dom := by linarith only [hmin_eq, hdom_eq, hdg, hdgs]
    dom_lt_revg := by omega
    revg_lt_revh := by omega
    revh_lt_sg := by omega
    sg_lt_sh := by omega
    sh_lt_sb := by omega
    sb_lt_es := by omega
    hp_lt_w := by omega
    L1_w := by omega
    vCap_w := by omega
    eCap_w := by omega
    b_w := by linarith only [hmin_eq, hmin_w]
    dgs_w := by linarith only [hmin_eq, hmin_w]
    min_w := hmin_w
    dom_w := hdom_w
    revg_w := hrevg_w
    revh_w := hrevh_w
    sg_w := hsg_w
    sh_w := hsh_w
    sb_w := hsb_w
    es_w := hes_w
    ep_w := by omega
  }

lemma dsCollectCand_bases_triple {w L vCap eCap b j heapPtr : ℕ}
    {p : Program} (mem0 : ℕ → ℕ)
    (hw16 : 16 ≤ 2 ^ w) (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hh_lt : heapPtr + 2 + vCap + eCap < 2 ^ w)
    (hmL : mem0 (b + dsLOff) = L) (hmV : mem0 (b + dsVCapOff) = vCap)
    (hmE : mem0 (b + dsECapOff) = eCap) (hgen_lt : mem0 (b + dsGenOff) < 2 ^ w) :
    Triple w p
      (fun st => st.mem = mem0 ∧ st.regs 0 = b ∧ st.regs 1 = j ∧ st.regs 2 = heapPtr)
      (.assign 3 (.load (.bin .add (.reg 0) (.const dsVCapOff))) ;;
       .assign 4 (.load (.bin .add (.reg 0) (.const dsECapOff))) ;;
       .assign 5 (.load (.bin .add (.reg 0) (.const dsLOff))) ;;
       .assign 6 (.load (.bin .add (.reg 0) (.const dsGenOff))) ;;
       .assign 14 (.bin .add (.const 4)
         (.bin .add (.bin .mul (.const 7) (.reg 3)) (.bin .mul (.const 9) (.reg 4)))) ;;
       .assign 7 (.bin .add (.bin .add (.reg 0) (.const dsHdrSize)) (.bin .mul (.const 3) (.reg 14))) ;;
       .assign 7 (.bin .add (.reg 7)
         (.bin .add (.bin .mul (.const 3) (.reg 4)) (.bin .mul (.const 2) (.bin .add (.reg 5) (.const 1))))) ;;
       .assign 8 (.bin .add (.reg 7)
         (.bin .add (.bin .add (.reg 5) (.const 1))
           (.bin .mul (.const 2) (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 4))))) ;;
       .assign 9 (.bin .add (.reg 8) (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 3))) ;;
       .assign 10 (.bin .add (.reg 9) (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 3))) ;;
       .assign 11 (.bin .add (.bin .add (.reg 10) (.bin .add (.reg 5) (.const 1)))
         (.bin .mul (.bin .add (.reg 5) (.const 1)) (.reg 3))) ;;
       .assign 12 (.bin .add (.reg 11) (.bin .add (.reg 5) (.const 1))) ;;
       .assign 13 (.bin .add (.reg 12) (.bin .mul (.const 2) (.reg 3))))
      (normalPost fun st =>
        st.mem = mem0 ∧ st.regs 0 = b ∧ st.regs 1 = j ∧ st.regs 2 = heapPtr ∧
        st.regs 3 = vCap ∧ st.regs 4 = eCap ∧ st.regs 5 = L ∧
        st.regs 6 = mem0 (b + dsGenOff) ∧
        st.regs 7 = dsDomGenBase b L vCap eCap ∧ st.regs 8 = dsRevGenBase b L vCap eCap ∧
        st.regs 9 = dsRevHeadBase b L vCap eCap ∧ st.regs 10 = dsSGenBase b L vCap eCap ∧
        st.regs 11 = dsSHeadBase b L vCap eCap ∧ st.regs 12 = dsSBitBase b L vCap eCap ∧
        st.regs 13 = dsEStampBase b L vCap eCap)
      (fun _ => 220) := by
  have lay := dsCandLayout_mk hfix hh_lt
  have hb_lt := lay.b_w
  have hv_lt := lay.vCap_w
  have he_lt := lay.eCap_w
  have hL1_lt := lay.L1_w
  have hdgs_lt := lay.dgs_w
  have hmin_lt := lay.min_w
  have hdom_lt := lay.dom_w
  have hrevg_lt := lay.revg_w
  have hrevh_lt := lay.revh_w
  have hsg_lt := lay.sg_w
  have hsh_lt := lay.sh_w
  have hsb_lt := lay.sb_w
  have hes_lt := lay.es_w
  have hdsh_lt : dsHdrSize < 2 ^ w := by simp [dsHdrSize]; omega
  have hdg_lt : dsGenOff < 2 ^ w := by simp [dsGenOff]; omega
  have hdv_lt : dsVCapOff < 2 ^ w := by simp [dsVCapOff]; omega
  have hde_lt : dsECapOff < 2 ^ w := by simp [dsECapOff]; omega
  have hdl_lt : dsLOff < 2 ^ w := by simp [dsLOff]; omega
  have h7v : 7 * vCap < 2 ^ w := by have := lay.dgs_eq; omega
  have h9e : 9 * eCap < 2 ^ w := by have := lay.dgs_eq; omega
  have h3e : 3 * eCap < 2 ^ w := by omega
  have h2L : 2 * (L + 1) < 2 ^ w := by have := lay.dom_eq; omega
  have h3dgs : 3 * (4 + (7 * vCap + 9 * eCap)) < 2 ^ w := by
    rw [lay.dgs_eq]; have := lay.min_eq; omega
  have h2Le : 2 * ((L + 1) * eCap) < 2 ^ w := by have := lay.revg_eq; omega
  have hLv : (L + 1) * vCap < 2 ^ w := by have := lay.revh_eq; omega
  have h3e2L : 3 * eCap + 2 * (L + 1) < 2 ^ w := by have := lay.dom_eq; omega
  have hL2Le : (L + 1) + 2 * ((L + 1) * eCap) < 2 ^ w := by have := lay.revg_eq; omega
  have hsgL1 : dsSGenBase b L vCap eCap + (L + 1) < 2 ^ w := by have := lay.sh_eq; omega
  have h2v : 2 * vCap < 2 ^ w := by have := lay.es_eq; omega
  have hm0 := lay.dgs_eq
  have hm1 : b + dsHdrSize + 3 * (4 + (7 * vCap + 9 * eCap)) = dsMinHBase b vCap eCap := by
    rw [hm0]; exact lay.min_eq
  have hm2 := lay.dom_eq
  have hm3 := lay.revg_eq
  have hm4 := lay.revh_eq
  have hm5 := lay.sg_eq
  have hm6 := lay.sh_eq
  have hm7 := lay.sb_eq
  have hm8 := lay.es_eq
  have hb_gen : b + dsGenOff < 2 ^ w := by have := lay.b_lt_dom; omega
  have hvc_lt : dsVCapOff < dsGenOff := by decide
  have hec_lt : dsECapOff < dsGenOff := by decide
  have hl_lt : dsLOff < dsGenOff := by decide
  have hb_vc : b + dsVCapOff < 2 ^ w := by omega
  have hb_ec : b + dsECapOff < 2 ^ w := by omega
  have hb_l : b + dsLOff < 2 ^ w := by omega
  clear hfix hh_lt lay hvc_lt hec_lt hl_lt
  wram_enter
  rcases hpre with ⟨hmem, r0, r1, r2⟩
  have hrv : st.regs 0 + dsVCapOff < 2 ^ w := by rw [r0]; exact hb_vc
  have hre : st.regs 0 + dsECapOff < 2 ^ w := by rw [r0]; exact hb_ec
  have hrl : st.regs 0 + dsLOff < 2 ^ w := by rw [r0]; exact hb_l
  have hrg : st.regs 0 + dsGenOff < 2 ^ w := by rw [r0]; exact hb_gen
  have hmv_w : st.mem (st.regs 0 + dsVCapOff) < 2 ^ w := by rw [hmem, r0, hmV]; exact hv_lt
  have hme_w : st.mem (st.regs 0 + dsECapOff) < 2 ^ w := by rw [hmem, r0, hmE]; exact he_lt
  have hml_w : st.mem (st.regs 0 + dsLOff) < 2 ^ w := by rw [hmem, r0, hmL]; omega
  have hmg_w : st.mem (st.regs 0 + dsGenOff) < 2 ^ w := by rw [hmem, r0]; exact hgen_lt
  wram_step; wram_step; wram_step; wram_step
  simp only [r0, hmem, hmV, hmE, hmL]
  wram_run
  · dsimp only
    refine ⟨rfl, by simp [Function.update, r0], by simp [Function.update, r1],
      by simp [Function.update, r2], by simp [Function.update], by simp [Function.update],
      by simp [Function.update], by simp [Function.update],
      by simp [Function.update]; omega, by simp [Function.update]; omega,
      by simp [Function.update]; omega, by simp [Function.update]; omega,
      by simp [Function.update]; omega, by simp [Function.update]; omega,
      by simp [Function.update]; omega⟩
  · wram_cost

/-! ## Phase A: S_prev extraction -/

lemma dsCollectCand_phaseA_triple {w L vCap eCap b j heapPtr : ℕ}
    {p : Program} (mem0 : ℕ → ℕ)
    (S_prev : Finset ℕ) (sPrevList : List ℕ) (footS : ℕ → Prop)
    (hw16 : 16 ≤ 2 ^ w) (h1j : 1 ≤ j) (hjL : j ≤ L)
    (hfix : b + dsFixedSize L vCap eCap ≤ heapPtr)
    (hh_lt : heapPtr + 2 + vCap + eCap < 2 ^ w)
    (hfootS : ∀ a, footS a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr)
    (hS_cap : ∀ v ∈ S_prev, v < vCap)
    (hs_nd : sPrevList.Nodup) (hs_mem : ∀ v, v ∈ sPrevList ↔ v ∈ S_prev)
    (hsg_pos : 0 < mem0 (dsSGenBase b L vCap eCap + (j - 1)))
    (hsg_lt : mem0 (dsSGenBase b L vCap eCap + (j - 1)) < 2 ^ w)
    (hll : LinkedListIn footS mem0 (mem0 (dsSHeadBase b L vCap eCap + (j - 1))) sPrevList)
    (hsBit0 : ∀ v < vCap, mem0 (dsSBitBase b L vCap eCap + v) = 0) :
    Triple w p
      (fun st => st.mem = mem0 ∧ st.regs 0 = b ∧ st.regs 1 = j ∧ st.regs 2 = heapPtr ∧
        st.regs 3 = vCap ∧ st.regs 4 = eCap ∧ st.regs 5 = L ∧
        st.regs 6 = mem0 (b + dsGenOff) ∧
        st.regs 7 = dsDomGenBase b L vCap eCap ∧ st.regs 8 = dsRevGenBase b L vCap eCap ∧
        st.regs 9 = dsRevHeadBase b L vCap eCap ∧ st.regs 10 = dsSGenBase b L vCap eCap ∧
        st.regs 11 = dsSHeadBase b L vCap eCap ∧ st.regs 12 = dsSBitBase b L vCap eCap ∧
        st.regs 13 = dsEStampBase b L vCap eCap)
      (.assign 14 (.bin .add (.reg 2) (.const 2)) ;;
       .assign 15 (.bin .sub (.reg 1) (.const 1)) ;;
       .cond (.load (.bin .add (.reg 10) (.reg 15)))
         (.assign 15 (.load (.bin .add (.reg 11) (.reg 15))) ;;
          .loop (.reg 15)
            (.assign 16 (.load (.reg 15)) ;;
             .store (.reg 14) (.reg 16) ;;
             .assign 14 (.bin .add (.reg 14) (.const 1)) ;;
             .store (.bin .add (.reg 12) (.reg 16)) (.const 1) ;;
             .assign 15 (.load (.bin .add (.reg 15) (.const 1)))))
         .nop ;;
       .assign 15 (.bin .sub (.reg 14) (.bin .add (.reg 2) (.const 2))) ;;
       .store (.reg 2) (.reg 15))
      (normalPost fun st =>
        st.regs 0 = b ∧ st.regs 1 = j ∧ st.regs 2 = heapPtr ∧
        st.regs 3 = vCap ∧ st.regs 4 = eCap ∧ st.regs 5 = L ∧
        st.regs 6 = mem0 (b + dsGenOff) ∧
        st.regs 7 = dsDomGenBase b L vCap eCap ∧ st.regs 8 = dsRevGenBase b L vCap eCap ∧
        st.regs 9 = dsRevHeadBase b L vCap eCap ∧ st.regs 10 = dsSGenBase b L vCap eCap ∧
        st.regs 11 = dsSHeadBase b L vCap eCap ∧ st.regs 12 = dsSBitBase b L vCap eCap ∧
        st.regs 13 = dsEStampBase b L vCap eCap ∧
        st.regs 14 = heapPtr + 2 + sPrevList.length ∧
        st.regs 15 = sPrevList.length ∧
        st.mem heapPtr = sPrevList.length ∧
        ListAt st.mem (heapPtr + 2) sPrevList ∧
        (∀ v < vCap, st.mem (dsSBitBase b L vCap eCap + v) = if v ∈ S_prev then 1 else 0) ∧
        ∀ addr, (∀ v < vCap, addr ≠ dsSBitBase b L vCap eCap + v) →
          (addr < heapPtr ∨ heapPtr + 2 + sPrevList.length ≤ addr) → st.mem addr = mem0 addr)
      (fun _ => 55 * sPrevList.length + 70) := by
  have lay := dsCandLayout_mk hfix hh_lt
  have hs_len_le : sPrevList.length ≤ vCap :=
    list_length_le_of_nodup_lt hs_nd fun v hv => hS_cap v ((hs_mem v).mp hv)
  set head0 := mem0 (dsSHeadBase b L vCap eCap + (j - 1))
  have hh0_lt : head0 < 2 ^ w := llPtr_lt_w hll (fun a ha => (hfootS a ha).2) lay.hp_lt_w 0 (Nat.zero_le _)
  have hsg_addr_lt : dsSGenBase b L vCap eCap + (j - 1) < 2 ^ w := by
    have := lay.sg_lt_sh; have := lay.sh_w; omega
  have hsh_addr_lt : dsSHeadBase b L vCap eCap + (j - 1) < 2 ^ w := by
    have := lay.sh_lt_sb; have := lay.sb_w; omega
  have hj_lt : j < 2 ^ w := by have := lay.L1_w; omega
  have hsbit_w : ∀ v < vCap, dsSBitBase b L vCap eCap + v < 2 ^ w := fun v hv => by
    have := lay.sb_lt_es; have := lay.es_w; omega
  let bodyS :=
    Stmt.assign 16 (.load (.reg 15)) ;;
    Stmt.store (.reg 14) (.reg 16) ;;
    Stmt.assign 14 (.bin .add (.reg 14) (.const 1)) ;;
    Stmt.store (.bin .add (.reg 12) (.reg 16)) (.const 1) ;;
    Stmt.assign 15 (.load (.bin .add (.reg 15) (.const 1)))
  let InvL : State → Prop := fun st =>
    ∃ k ≤ sPrevList.length,
      st.regs 0 = b ∧ st.regs 1 = j ∧ st.regs 2 = heapPtr ∧
      st.regs 3 = vCap ∧ st.regs 4 = eCap ∧ st.regs 5 = L ∧
      st.regs 6 = mem0 (b + dsGenOff) ∧
      st.regs 7 = dsDomGenBase b L vCap eCap ∧ st.regs 8 = dsRevGenBase b L vCap eCap ∧
      st.regs 9 = dsRevHeadBase b L vCap eCap ∧ st.regs 10 = dsSGenBase b L vCap eCap ∧
      st.regs 11 = dsSHeadBase b L vCap eCap ∧ st.regs 12 = dsSBitBase b L vCap eCap ∧
      st.regs 13 = dsEStampBase b L vCap eCap ∧
      st.regs 14 = heapPtr + 2 + k ∧
      st.regs 15 = llPtr mem0 head0 k ∧
      ListAt st.mem (heapPtr + 2) (sPrevList.take k) ∧
      (∀ v < vCap, st.mem (dsSBitBase b L vCap eCap + v) =
        if v ∈ sPrevList.take k then 1 else 0) ∧
      ∀ addr, (∀ v < vCap, addr ≠ dsSBitBase b L vCap eCap + v) →
        (addr < heapPtr + 2 ∨ heapPtr + 2 + k ≤ addr) → st.mem addr = mem0 addr
  let mFn : State → ℕ := fun st =>
    if h : ∃ k ≤ sPrevList.length, st.regs 15 = llPtr mem0 head0 k then
      sPrevList.length - Nat.find h
    else 0
  let remFn : State → ℕ := fun st => 55 * mFn st + 10
  have hm_eq : ∀ {st} {k} (hk : k ≤ sPrevList.length),
      st.regs 15 = llPtr mem0 head0 k → mFn st = sPrevList.length - k := by
    intro st k hk hr15
    have hex : ∃ k' ≤ sPrevList.length, st.regs 15 = llPtr mem0 head0 k' := ⟨k, hk, hr15⟩
    have hm1 : mFn st = sPrevList.length - Nat.find hex := by
      dsimp only [mFn]; split_ifs; rfl
    have hsp := Nat.find_spec hex
    rw [hm1, llPtr_inj hll hsp.1 hk (hsp.2.symm.trans hr15)]
  have hLoop : Triple w p InvL (.loop (.reg 15) bodyS)
      (normalPost fun st =>
        st.regs 0 = b ∧ st.regs 1 = j ∧ st.regs 2 = heapPtr ∧
        st.regs 3 = vCap ∧ st.regs 4 = eCap ∧ st.regs 5 = L ∧
        st.regs 6 = mem0 (b + dsGenOff) ∧
        st.regs 7 = dsDomGenBase b L vCap eCap ∧ st.regs 8 = dsRevGenBase b L vCap eCap ∧
        st.regs 9 = dsRevHeadBase b L vCap eCap ∧ st.regs 10 = dsSGenBase b L vCap eCap ∧
        st.regs 11 = dsSHeadBase b L vCap eCap ∧ st.regs 12 = dsSBitBase b L vCap eCap ∧
        st.regs 13 = dsEStampBase b L vCap eCap ∧
        st.regs 14 = heapPtr + 2 + sPrevList.length ∧
        ListAt st.mem (heapPtr + 2) sPrevList ∧
        (∀ v < vCap, st.mem (dsSBitBase b L vCap eCap + v) = if v ∈ S_prev then 1 else 0) ∧
        ∀ addr, (∀ v < vCap, addr ≠ dsSBitBase b L vCap eCap + v) →
          (addr < heapPtr + 2 ∨ heapPtr + 2 + sPrevList.length ≤ addr) → st.mem addr = mem0 addr)
      remFn := by
    refine Triple.loop_measure (condVal := fun st => st.regs 15) (m := mFn) (rem := remFn)
      (fun st hInv => by
        rcases hInv with ⟨k, hk, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr15, _⟩
        have hlt := llPtr_lt_w hll (fun a ha => (hfootS a ha).2) lay.hp_lt_w k hk
        simp [Expr.eval, hr15])
      (fun st hInv hzero => by
        rcases hInv with ⟨k, hk, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, hr15, hAt, hsB, hFr⟩
        have hkeq : k = sPrevList.length := by
          by_contra hne
          have hlt := lt_of_le_of_ne hk hne
          have hpos := (llPtr_step_spec hll k hlt).1
          rw [hr15] at hzero; omega
        subst hkeq
        rw [List.take_length] at hAt hsB
        refine ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, hAt,
          fun v hv => by simpa [hs_mem v] using hsB v hv, hFr⟩, ?_⟩
        dsimp only [remFn, Expr.size]; omega)
      (fun st hInv hnz => by
        rcases hInv with ⟨k, hk, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, hr15, hAt, hsB, hFr⟩
        have hlt : k < sPrevList.length := by
          by_contra hge
          have hkeq : k = sPrevList.length := by omega
          apply hnz; rw [hr15, hkeq, llPtr_zero hll]
        have hsp := llPtr_step_spec hll k hlt
        set pNode := llPtr mem0 head0 k
        set v := sPrevList[k]
        have hv_cap : v < vCap := hS_cap v ((hs_mem v).mp (List.getElem_mem hlt))
        have hv_lt : v < 2 ^ w := lt_trans hv_cap lay.vCap_w
        have hp_lt_hp : pNode < heapPtr := (hfootS pNode hsp.2.1).2
        have hp_lt_w : pNode < 2 ^ w := lt_trans hp_lt_hp lay.hp_lt_w
        have hp1_lt_w : pNode + 1 < 2 ^ w := lt_trans (hfootS _ hsp.2.2.1).2 lay.hp_lt_w
        have hm_node : st.mem pNode = v := by
          have hne_sb : ∀ z < vCap, pNode ≠ dsSBitBase b L vCap eCap + z := fun z hz => by
            have := (hfootS pNode hsp.2.1).1; have := lay.es_lt_fix; have := lay.sb_lt_es; omega
          rw [hFr pNode hne_sb (Or.inl (by omega)), hsp.2.2.2.1]
        have hm_next : st.mem (pNode + 1) = llPtr mem0 head0 (k + 1) := by
          have hne_sb : ∀ z < vCap, pNode + 1 ≠ dsSBitBase b L vCap eCap + z := fun z hz => by
            have := (hfootS _ hsp.2.2.1).1; have := lay.es_lt_fix; have := lay.sb_lt_es; omega
          rw [hFr (pNode + 1) hne_sb (Or.inl (by omega)), hsp.2.2.2.2]
        have hnext_w : llPtr mem0 head0 (k + 1) < 2 ^ w :=
          llPtr_lt_w hll (fun a ha => (hfootS a ha).2) lay.hp_lt_w (k + 1) (Nat.succ_le_of_lt hlt)
        have h14_lt : st.regs 14 + 1 < 2 ^ w := by have := lay.hp_lt_w; omega
        have hs12v_lt : st.regs 12 + v < 2 ^ w := by rw [r12]; exact hsbit_w v hv_cap
        have h1_lt : (1 : ℕ) < 2 ^ w := by omega
        have hs_lt : st.regs 15 < 2 ^ w := by rw [hr15]; exact hp_lt_w
        have hs1_lt : st.regs 15 + 1 < 2 ^ w := by rw [hr15]; exact hp1_lt_w
        have hmem16 : st.mem (st.regs 15) = v := by rw [hr15, hm_node]
        refine ⟨52, ?_⟩
        wram_enter
        subst hpre
        dsimp only [bodyS]
        wram_run
        · dsimp only
          have hnext' : Function.update (Function.update st.mem (st.regs 14) v)
              (st.regs 12 + v) 1 (st.regs 15 + 1) = llPtr mem0 head0 (k + 1) := by
            rw [r12, r14, hr15]
            have hne1 : pNode + 1 ≠ heapPtr + 2 + k := by omega
            have hne2 : pNode + 1 ≠ dsSBitBase b L vCap eCap + v := by
              have := (hfootS _ hsp.2.2.1).1; have := lay.es_lt_fix; have := lay.sb_lt_es; omega
            rw [Function.update_of_ne hne2, Function.update_of_ne hne1]
            exact hm_next
          have hmem_at : ListAt (Function.update (Function.update st.mem (st.regs 14) v)
              (st.regs 12 + v) 1) (heapPtr + 2) (sPrevList.take (k + 1)) := by
            rw [List.take_succ_eq_append_getElem hlt]
            refine listAt_snoc (listAt_of_agree (fun t ht => ?_) hAt) ?_
            · rw [List.length_take_of_le (Nat.le_of_lt hlt)] at ht
              rw [r12, r14]
              have hne2 : heapPtr + 2 + t ≠ dsSBitBase b L vCap eCap + v := by
                have := lay.es_lt_fix; have := lay.sb_lt_es; omega
              rw [Function.update_of_ne hne2, Function.update_of_ne (by omega)]
            · rw [List.length_take_of_le (Nat.le_of_lt hlt), r12, r14]
              have hne2 : heapPtr + 2 + k ≠ dsSBitBase b L vCap eCap + v := by
                have := lay.es_lt_fix; have := lay.sb_lt_es; omega
              rw [Function.update_of_ne hne2, Function.update_self]
          have hsb' : ∀ z < vCap, Function.update (Function.update st.mem (st.regs 14) v)
              (st.regs 12 + v) 1 (dsSBitBase b L vCap eCap + z) =
              if z ∈ sPrevList.take (k + 1) then 1 else 0 := by
            intro z hz
            rw [List.take_succ_eq_append_getElem hlt, r12, r14]
            simp only [List.mem_append, List.mem_singleton]
            by_cases hzv : z = v
            · subst hzv; rw [Function.update_self]; simp [v]
            · have hne1 : dsSBitBase b L vCap eCap + z ≠ heapPtr + 2 + k := by
                have := lay.es_lt_fix; have := lay.sb_lt_es; omega
              rw [Function.update_of_ne (by omega), Function.update_of_ne hne1, hsB z hz]
              simp [v, hzv]
          have hfr' : ∀ addr, (∀ z < vCap, addr ≠ dsSBitBase b L vCap eCap + z) →
              (addr < heapPtr + 2 ∨ heapPtr + 2 + (k + 1) ≤ addr) →
              Function.update (Function.update st.mem (st.regs 14) v)
                (st.regs 12 + v) 1 addr = mem0 addr := by
            intro addr hns hrange
            rw [r12, r14, Function.update_of_ne (hns v hv_cap), Function.update_of_ne (by omega)]
            exact hFr addr hns (by omega)
          have hr15_next : (Function.update (Function.update (Function.update st.regs 16 (st.mem pNode))
                14 (st.regs 14 + 1)) 15 (Function.update (Function.update st.mem (st.regs 14) (st.mem pNode))
                (st.regs 12 + st.mem pNode) 1 (st.regs 15 + 1))) 15 = llPtr mem0 head0 (k + 1) := by
            rw [Function.update_self, hm_node]; exact hnext'
          have hm_st : ∀ st₁ : State, st₁.regs 15 = llPtr mem0 head0 (k + 1) →
              mFn st₁ < mFn st ∧ (Expr.reg 15 : Expr).size + 52 + remFn st₁ + 1 ≤ remFn st := by
            intro st₁ hr1_next
            have h1 := hm_eq (Nat.succ_le_of_lt hlt) hr1_next
            have h2 := hm_eq hk hr15
            dsimp only [remFn, Expr.size]
            exact ⟨by omega, by omega⟩
          refine ⟨⟨k + 1, Nat.succ_le_of_lt hlt,
            by dsimp only; simp only [Function.update_of_ne (by decide : (0 : ℕ) ≠ 15), Function.update_of_ne (by decide : (0 : ℕ) ≠ 14), Function.update_of_ne (by decide : (0 : ℕ) ≠ 16), r0],
            by dsimp only; simp only [Function.update_of_ne (by decide : (1 : ℕ) ≠ 15), Function.update_of_ne (by decide : (1 : ℕ) ≠ 14), Function.update_of_ne (by decide : (1 : ℕ) ≠ 16), r1],
            by dsimp only; simp only [Function.update_of_ne (by decide : (2 : ℕ) ≠ 15), Function.update_of_ne (by decide : (2 : ℕ) ≠ 14), Function.update_of_ne (by decide : (2 : ℕ) ≠ 16), r2],
            by dsimp only; simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 15), Function.update_of_ne (by decide : (3 : ℕ) ≠ 14), Function.update_of_ne (by decide : (3 : ℕ) ≠ 16), r3],
            by dsimp only; simp only [Function.update_of_ne (by decide : (4 : ℕ) ≠ 15), Function.update_of_ne (by decide : (4 : ℕ) ≠ 14), Function.update_of_ne (by decide : (4 : ℕ) ≠ 16), r4],
            by dsimp only; simp only [Function.update_of_ne (by decide : (5 : ℕ) ≠ 15), Function.update_of_ne (by decide : (5 : ℕ) ≠ 14), Function.update_of_ne (by decide : (5 : ℕ) ≠ 16), r5],
            by dsimp only; simp only [Function.update_of_ne (by decide : (6 : ℕ) ≠ 15), Function.update_of_ne (by decide : (6 : ℕ) ≠ 14), Function.update_of_ne (by decide : (6 : ℕ) ≠ 16), r6],
            by dsimp only; simp only [Function.update_of_ne (by decide : (7 : ℕ) ≠ 15), Function.update_of_ne (by decide : (7 : ℕ) ≠ 14), Function.update_of_ne (by decide : (7 : ℕ) ≠ 16), r7],
            by dsimp only; simp only [Function.update_of_ne (by decide : (8 : ℕ) ≠ 15), Function.update_of_ne (by decide : (8 : ℕ) ≠ 14), Function.update_of_ne (by decide : (8 : ℕ) ≠ 16), r8],
            by dsimp only; simp only [Function.update_of_ne (by decide : (9 : ℕ) ≠ 15), Function.update_of_ne (by decide : (9 : ℕ) ≠ 14), Function.update_of_ne (by decide : (9 : ℕ) ≠ 16), r9],
            by dsimp only; simp only [Function.update_of_ne (by decide : (10 : ℕ) ≠ 15), Function.update_of_ne (by decide : (10 : ℕ) ≠ 14), Function.update_of_ne (by decide : (10 : ℕ) ≠ 16), r10],
            by dsimp only; simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 15), Function.update_of_ne (by decide : (11 : ℕ) ≠ 14), Function.update_of_ne (by decide : (11 : ℕ) ≠ 16), r11],
            by dsimp only; simp only [Function.update_of_ne (by decide : (12 : ℕ) ≠ 15), Function.update_of_ne (by decide : (12 : ℕ) ≠ 14), Function.update_of_ne (by decide : (12 : ℕ) ≠ 16), r12],
            by dsimp only; simp only [Function.update_of_ne (by decide : (13 : ℕ) ≠ 15), Function.update_of_ne (by decide : (13 : ℕ) ≠ 14), Function.update_of_ne (by decide : (13 : ℕ) ≠ 16), r13],
            by dsimp only; simp only [Function.update_of_ne (by decide : (14 : ℕ) ≠ 15), Function.update_self, r14]; omega,
            by dsimp only; exact hr15_next,
            by dsimp only; rw [hm_node]; exact hmem_at,
            by dsimp only; rw [hm_node]; exact hsb',
            by dsimp only; rw [hm_node]; exact hfr'⟩,
            (hm_st _ (by dsimp only; exact hr15_next)).1,
            (hm_st _ (by dsimp only; exact hr15_next)).2⟩
        · wram_cost)
  have hrem_head : ∀ st₁, st₁.regs 15 = head0 → remFn st₁ = 55 * sPrevList.length + 10 := by
    intro st₁ hr
    dsimp only [remFn]
    rw [hm_eq (Nat.zero_le _) hr, Nat.sub_zero]
  wram_enter
  rcases hpre with ⟨hmem, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13⟩
  have hr2_lt : heapPtr + 2 < 2 ^ w := by have := lay.hp_lt_w; omega
  have hr15_sub : j - 1 < 2 ^ w := by omega
  have hr1_lt : st.regs 1 < 2 ^ w := by rw [r1]; exact hj_lt
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have h10_15 : st.regs 10 + (j - 1) < 2 ^ w := by rw [r10]; exact hsg_addr_lt
  have h11_15 : st.regs 11 + (j - 1) < 2 ^ w := by rw [r11]; exact hsh_addr_lt
  have hmg_lt : st.mem (dsSGenBase b L vCap eCap + (j - 1)) < 2 ^ w := by rw [hmem]; exact hsg_lt
  have hmh_lt : st.mem (dsSHeadBase b L vCap eCap + (j - 1)) < 2 ^ w := by rw [hmem]; exact hh0_lt
  wram_step; wram_step
  refine runs_seq_cond_le (v := mem0 (dsSGenBase b L vCap eCap + (j - 1))) ?_ ?_ ?_
  · refine Expr.eval_load_of_eq
      (Expr.eval_add (x := dsSGenBase b L vCap eCap) (y := j - 1)
        (Expr.eval_reg_of_eq ?_) (Expr.eval_reg_of_eq ?_) hsg_addr_lt) ?_
    · dsimp only
      simp only [Function.update_of_ne (by decide : (10 : ℕ) ≠ 15),
        Function.update_of_ne (by decide : (10 : ℕ) ≠ 14), r10]
    · dsimp only; simp only [Function.update_self, r1]
    · dsimp only; rw [hmem]
  · intro _
    refine runs_seq_assoc_le ?_
    refine runs_seq_assign_le (v := head0) ?_ ?_
    · refine Expr.eval_load_of_eq
        (Expr.eval_add (x := dsSHeadBase b L vCap eCap) (y := j - 1)
          (Expr.eval_reg_of_eq ?_) (Expr.eval_reg_of_eq ?_) hsh_addr_lt) ?_
      · dsimp only
        simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 15),
          Function.update_of_ne (by decide : (11 : ℕ) ≠ 14), r11]
      · dsimp only; simp only [Function.update_self, r1]
      · dsimp only; rw [hmem]
    refine runs_seq_triple_le hLoop ?_ ?_
    · dsimp only
      refine ⟨0, Nat.zero_le _,
        by simp only [Function.update_of_ne (by decide : (0 : ℕ) ≠ 15), Function.update_of_ne (by decide : (0 : ℕ) ≠ 14), r0],
        by simp only [Function.update_of_ne (by decide : (1 : ℕ) ≠ 15), Function.update_of_ne (by decide : (1 : ℕ) ≠ 14), r1],
        by simp only [Function.update_of_ne (by decide : (2 : ℕ) ≠ 15), Function.update_of_ne (by decide : (2 : ℕ) ≠ 14), r2],
        by simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 15), Function.update_of_ne (by decide : (3 : ℕ) ≠ 14), r3],
        by simp only [Function.update_of_ne (by decide : (4 : ℕ) ≠ 15), Function.update_of_ne (by decide : (4 : ℕ) ≠ 14), r4],
        by simp only [Function.update_of_ne (by decide : (5 : ℕ) ≠ 15), Function.update_of_ne (by decide : (5 : ℕ) ≠ 14), r5],
        by simp only [Function.update_of_ne (by decide : (6 : ℕ) ≠ 15), Function.update_of_ne (by decide : (6 : ℕ) ≠ 14), r6],
        by simp only [Function.update_of_ne (by decide : (7 : ℕ) ≠ 15), Function.update_of_ne (by decide : (7 : ℕ) ≠ 14), r7],
        by simp only [Function.update_of_ne (by decide : (8 : ℕ) ≠ 15), Function.update_of_ne (by decide : (8 : ℕ) ≠ 14), r8],
        by simp only [Function.update_of_ne (by decide : (9 : ℕ) ≠ 15), Function.update_of_ne (by decide : (9 : ℕ) ≠ 14), r9],
        by simp only [Function.update_of_ne (by decide : (10 : ℕ) ≠ 15), Function.update_of_ne (by decide : (10 : ℕ) ≠ 14), r10],
        by simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 15), Function.update_of_ne (by decide : (11 : ℕ) ≠ 14), r11],
        by simp only [Function.update_of_ne (by decide : (12 : ℕ) ≠ 15), Function.update_of_ne (by decide : (12 : ℕ) ≠ 14), r12],
        by simp only [Function.update_of_ne (by decide : (13 : ℕ) ≠ 15), Function.update_of_ne (by decide : (13 : ℕ) ≠ 14), r13],
        by simp only [Function.update_of_ne (by decide : (14 : ℕ) ≠ 15), Function.update_self],
        by simp only [Function.update_self]; rfl,
        fun _ hk => by simp at hk, fun v hv => by rw [hmem]; exact hsBit0 v hv,
        fun _ _ _ => hmem ▸ rfl⟩
    · intro stA ⟨ar0, ar1, ar2, ar3, ar4, ar5, ar6, ar7, ar8, ar9, ar10, ar11, ar12, ar13, ar14,
        hAtA, hsbA, hfrA⟩
      have har14 : stA.regs 14 < 2 ^ w := by rw [ar14]; have := lay.hp_lt_w; omega
      have har22 : stA.regs 2 + 2 < 2 ^ w := by rw [ar2]; exact hr2_lt
      have har2_lt : stA.regs 2 < 2 ^ w := by rw [ar2]; have := lay.hp_lt_w; omega
      have hdiff_lt : sPrevList.length < 2 ^ w := by omega
      wram_run
      · dsimp only
        refine ⟨
          by simp only [Function.update_of_ne (by decide : (0 : ℕ) ≠ 15), ar0],
          by simp only [Function.update_of_ne (by decide : (1 : ℕ) ≠ 15), ar1],
          by simp only [Function.update_of_ne (by decide : (2 : ℕ) ≠ 15), ar2],
          by simp only [Function.update_of_ne (by decide : (3 : ℕ) ≠ 15), ar3],
          by simp only [Function.update_of_ne (by decide : (4 : ℕ) ≠ 15), ar4],
          by simp only [Function.update_of_ne (by decide : (5 : ℕ) ≠ 15), ar5],
          by simp only [Function.update_of_ne (by decide : (6 : ℕ) ≠ 15), ar6],
          by simp only [Function.update_of_ne (by decide : (7 : ℕ) ≠ 15), ar7],
          by simp only [Function.update_of_ne (by decide : (8 : ℕ) ≠ 15), ar8],
          by simp only [Function.update_of_ne (by decide : (9 : ℕ) ≠ 15), ar9],
          by simp only [Function.update_of_ne (by decide : (10 : ℕ) ≠ 15), ar10],
          by simp only [Function.update_of_ne (by decide : (11 : ℕ) ≠ 15), ar11],
          by simp only [Function.update_of_ne (by decide : (12 : ℕ) ≠ 15), ar12],
          by simp only [Function.update_of_ne (by decide : (13 : ℕ) ≠ 15), ar13],
          by simp only [Function.update_of_ne (by decide : (14 : ℕ) ≠ 15), ar14],
          by simp only [Function.update_self]; omega,
          by dsimp only; rw [ar2, Function.update_self]; omega,
          ?_, ?_, ?_⟩
        · dsimp only
          exact listAt_of_agree (fun k hk => by
            rw [ar2, Function.update_of_ne (by omega)]) hAtA
        · dsimp only
          intro v hv
          have hne : dsSBitBase b L vCap eCap + v ≠ stA.regs 2 := by
            rw [ar2]; have := lay.es_lt_fix; have := lay.sb_lt_es; omega
          rw [Function.update_of_ne hne]; exact hsbA v hv
        · dsimp only
          intro addr hns hrange
          rw [Function.update_of_ne (by rw [ar2]; omega)]
          exact hfrA addr hns (by omega)
      · rw [hrem_head _ (by dsimp only; simp only [Function.update_self])]
        wram_cost
  · intro hzero
    exfalso; exact (Nat.ne_of_gt hsg_pos) hzero

end

end MinCostFlow.DynSpanner.Program
