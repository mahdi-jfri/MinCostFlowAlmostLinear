module

public import MinCostFlow.DynSpanner.Program.DynSpannerAffected
public import MinCostFlow.DynSpanner.Program.DynSpannerProjStage
import Mathlib.Tactic.Ring

/-!
# The affected stage: data and the context of the projection

The affected stage (Algorithm 6, lines 70–77) first collects the candidate edges with
`dsCollectCandStmt` and at the end runs the projection stage `dsProjStageStmt`. In between,
`dsFilterAffectedStmt` keeps the affected candidates. The contexts of the filter and of the
projection, `FilterCtx`, are about the memory before each call and the list of edges that the
call reads. This file gives the data of the whole stage (`AffCtx`,
about the memory before the first call), the facts that hold before the filter and before the
projection (`AffMid`), and the context built from them (`AffCtx.toFilter`).
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.DynSpanner

@[expose] public section

/-- The data of the affected stage, with the facts on the memory `mem0` before it. -/
structure AffCtx where
  w : ℕ
  L : ℕ
  vCap : ℕ
  eCap : ℕ
  b : ℕ
  j : ℕ
  heapPtr : ℕ
  G' : MGraph
  H_lt : MGraph
  inDom_mid : Fin (L + 1) → Finset ℕ
  Pi_level : Fin (L + 1) → Embedding
  piLt_mid : Embedding
  S_prev : Finset ℕ
  sPrevList : List ℕ
  revLists : Fin (L + 1) → ℕ → List ℕ
  memInDom : Fin (L + 1) → Finset ℕ
  footPi : ℕ → Prop
  footS : ℕ → Prop
  footRev : ℕ → Prop
  mem0 : ℕ → ℕ
  hw16 : 16 ≤ 2 ^ w
  h1j : 1 ≤ j
  hjL : j ≤ L
  hfix_w : b + dsFixedSize L vCap eCap < 2 ^ w
  hfixH : b + dsFixedSize L vCap eCap ≤ heapPtr
  hmL : mem0 (b + dsLOff) = L
  hmV : mem0 (b + dsVCapOff) = vCap
  hmE : mem0 (b + dsECapOff) = eCap
  hgen1 : 1 ≤ mem0 (b + dsGenOff)
  hgenB : mem0 (b + dsGenOff) + 1 < 2 ^ w
  hDG : DynGraphAt mem0 (dsGPtr b) vCap eCap G'
  hG_val : G'.IsValid
  hGV_cap : ∀ v ∈ G'.V, v < vCap
  hGE_cap : ∀ e ∈ G'.E, e < eCap
  hH_sub : H_lt.E ⊆ G'.E
  hH_ends : H_lt.tail = G'.tail ∧ H_lt.head = G'.head
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
  hpi_walk : ∀ e ∈ G'.E, ∀ k (hk : k < (piLt_mid e).length),
    ¬ (G'.tail e ∈ S_prev ∨ ∃ i < k, ∃ hi : i < (piLt_mid e).length, G'.dst ((piLt_mid e)[i]'hi) ∈ S_prev) →
    ((piLt_mid e)[k]'hk).1 ∈ H_lt.E
  hpiLt_eq : piLt_mid = piLtFrom Pi_level inDom_mid j
  hfootPi : ∀ a, footPi a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr
  hfootS : ∀ a, footS a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr
  hfootRev : ∀ a, footRev a → b + dsFixedSize L vCap eCap ≤ a ∧ a < heapPtr
  hS_cap : ∀ v ∈ S_prev, v < vCap
  hs_nd : sPrevList.Nodup
  hs_iff : ∀ v, v ∈ sPrevList ↔ v ∈ S_prev
  hsg0 : 0 < mem0 (dsSGenBase b L vCap eCap + (j - 1))
  hsgle : mem0 (dsSGenBase b L vCap eCap + (j - 1)) ≤ mem0 (b + dsGenOff)
  hsll : LinkedListIn footS mem0 (mem0 (dsSHeadBase b L vCap eCap + (j - 1))) sPrevList
  hsbit0 : ∀ v < vCap, mem0 (dsSBitBase b L vCap eCap + v) = 0
  hestamp : ∀ e < eCap, mem0 (dsEStampBase b L vCap eCap + e) ≤ mem0 (b + dsGenOff)
  hdomle : ∀ i : Fin (L + 1), i.1 < j →
    mem0 (dsDomGenBase b L vCap eCap + i.1) ≤ mem0 (b + dsGenOff)
  hrev : ∀ i : Fin (L + 1), i.1 < j → ∀ v ∈ S_prev,
    mem0 (dsRevGenBase b L vCap eCap + i.1 * vCap + v) ≤ mem0 (b + dsGenOff) ∧
    (if 0 < mem0 (dsDomGenBase b L vCap eCap + i.1) ∧
        mem0 (dsRevGenBase b L vCap eCap + i.1 * vCap + v) = mem0 (dsDomGenBase b L vCap eCap + i.1)
     then LinkedListIn footRev mem0 (mem0 (dsRevHeadBase b L vCap eCap + i.1 * vCap + v))
       (revLists i v)
     else revLists i v = []) ∧
    (∀ e ∈ revLists i v, e < eCap)
  aux0 : DynGraphAt mem0 (dsAuxPtr b vCap eCap) vCap eCap emptyMGraph
  walks : ∀ e ∈ G'.E, PrefixWalksValid G' S_prev eCap (G'.tail e) (G'.head e) (piLt_mid e)

/-- The edges of `G'` on a reverse list `revLists i v` of a vertex `v ∈ S_prev` at a level
`i < j`. -/
noncomputable def revCandSet (L j : ℕ) (revLists : Fin (L + 1) → ℕ → List ℕ) (S_prev : Finset ℕ)
    (G' : MGraph) : Finset ℕ :=
  @Finset.filter _ (fun e => ∃ i : Fin (L + 1), ∃ v ∈ S_prev, i.1 < j ∧ e ∈ revLists i v)
    (Classical.decPred _) G'.E

/-- The set of candidate edges (Algorithm 6, line 71): edges of `G'` on a reverse list of a vertex
of `S_{j-1}` at a level below `j`. -/
noncomputable def AffCtx.candSet (a : AffCtx) : Finset ℕ :=
  @Finset.filter _ (fun e => ∃ i : Fin (a.L + 1), ∃ v ∈ a.S_prev, i.1 < a.j ∧ e ∈ a.revLists i v)
    (Classical.decPred _) a.G'.E

lemma AffCtx.candSet_eq_revCandSet (a : AffCtx) :
    a.candSet = revCandSet a.L a.j a.revLists a.S_prev a.G' := rfl

/-- The affected edges among the candidates (Algorithm 6, line 71). -/
noncomputable def AffCtx.affSet (a : AffCtx) : Finset ℕ :=
  a.candSet.filter fun e => e ∈ affectedEdges a.G' a.H_lt a.piLt_mid a.S_prev

/-- A bound on the heap words of the projection: the words it would need for all candidates. -/
noncomputable def AffCtx.heapNeed (a : AffCtx) : ℕ :=
  ∑ e ∈ a.candSet, (14 * (a.piLt_mid e).length + 15)

/-- The start of the list of candidates written by `dsCollectCandStmt`. -/
def AffCtx.candPtr (a : AffCtx) : ℕ := a.heapPtr + 2 + a.sPrevList.length

/-- The facts after the first calls of the stage: a list `l` of edges of `G'` without repeats is
at `ptr` in the heap, the array `sBit` marks `S_{j-1}`, and the words that the projection reads
are unchanged. -/
structure AffMid (a : AffCtx) (ptr : ℕ) (l : List ℕ) (mem : ℕ → ℕ) : Prop where
  nd : l.Nodup
  sub : ∀ e ∈ l, e ∈ a.G'.E
  lt : ∀ e ∈ l, e < a.eCap
  at_ : ListAt mem ptr l
  sBit : ∀ v < a.vCap, mem (dsSBitBase a.b a.L a.vCap a.eCap + v) = if v ∈ a.S_prev then 1 else 0
  agree : ∀ addr, ((addr < dsSBitBase a.b a.L a.vCap a.eCap ∧ addr ≠ a.b + dsGenOff) ∨
    (a.b + dsFixedSize a.L a.vCap a.eCap ≤ addr ∧ addr < a.heapPtr)) → mem addr = a.mem0 addr
  hp : a.heapPtr ≤ ptr
  hB : ptr + l.length + l.length + projHeapNeed a.piLt_mid l < 2 ^ a.w

end

public section

/-- An index `i · m + e` with `i < n` and `e < m` is below `n · m`. -/
lemma idx_lt_mul {i n e m : ℕ} (hi : i < n) (he : e < m) : i * m + e < n * m := by
  calc i * m + e < i * m + m := by omega
    _ = (i + 1) * m := by ring
    _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)

lemma sBit_ge_layout (b L vCap eCap : ℕ) :
    dsPiPtrBase b L vCap eCap + (L + 1) * eCap ≤ dsSBitBase b L vCap eCap ∧
    dsEdgeDomGenBase b L vCap eCap + (L + 1) * eCap = dsPiPtrBase b L vCap eCap ∧
    dsDomGenBase b L vCap eCap + (L + 1) = dsEdgeDomGenBase b L vCap eCap ∧
    dsAuxPtr b vCap eCap + dynGraphSize vCap eCap ≤ dsDomGenBase b L vCap eCap ∧
    dsGPtr b + dynGraphSize vCap eCap ≤ dsAuxPtr b vCap eCap ∧
    b + dsGenOff < dsGPtr b ∧ b + dsLOff < dsGPtr b ∧ b + dsVCapOff < dsGPtr b ∧
    b + dsECapOff < dsGPtr b ∧
    dsSBitBase b L vCap eCap + vCap ≤ b + dsFixedSize L vCap eCap := by
  have hfa := dsFixedSize_add b L vCap eCap
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [dsAuxPtr, dsHPtr, dsSBitBase, dsSHeadBase, dsVSGenBase, dsSGenBase, dsRevHeadBase,
    dsRevGenBase, dsPiPtrBase, dsEdgeDomGenBase, dsDomGenBase, dsHDegDummyBase, dsHHeadBase,
    dsHPrevBase, dsHNextBase, dsMinHBase, dsMEmbTempBase, dsKeptStampBase, dsEStampBase,
    dsVStampBase, dsGPtr, dsHdrSize, dsGenOff, dsLOff, dsVCapOff, dsECapOff] at hfa ⊢ <;>
  omega

/-- The context `FilterCtx` of a call of the filter or of the projection on the list `cand` at
`ptr`, with the memory `mem` before the call. -/
@[expose] def AffCtx.toFilter (a : AffCtx) (ptr : ℕ) (cand : List ℕ) (mem : ℕ → ℕ)
    (h : AffMid a ptr cand mem) : FilterCtx :=
  have hl := sBit_ge_layout a.b a.L a.vCap a.eCap
  have hag : ∀ addr, addr < dsSBitBase a.b a.L a.vCap a.eCap → addr ≠ a.b + dsGenOff →
      mem addr = a.mem0 addr := fun addr h1 h2 => h.agree addr (Or.inl ⟨h1, h2⟩)
  { w := a.w, L := a.L, vCap := a.vCap, eCap := a.eCap, b := a.b, j := a.j
    candPtr := ptr, candLen := cand.length, outArrPtr := ptr + cand.length
    G' := a.G', H_lt := a.H_lt, inDom_mid := a.inDom_mid, Pi_level := a.Pi_level
    piLt_mid := a.piLt_mid, S_prev := a.S_prev, cand := cand, memInDom := a.memInDom
    footPi := a.footPi, mem0 := mem
    hw16 := a.hw16, h1j := a.h1j, hjL := a.hjL, hfix_w := a.hfix_w
    hcand_w := by have := h.hB; omega
    hout_w := by have := h.hB; omega
    hfix_out := by have := a.hfixH; have := h.hp; omega
    hfoot_out := fun x hx => by
      have := (a.hfootPi x hx).2; have := h.hp; left; omega
    hcand_out := fun k hk => by left; omega
    hmL := by rw [hag _ (by omega) (by simp [dsLOff, dsGenOff])]; exact a.hmL
    hmV := by rw [hag _ (by omega) (by simp [dsVCapOff, dsGenOff])]; exact a.hmV
    hmE := by rw [hag _ (by omega) (by simp [dsECapOff, dsGenOff])]; exact a.hmE
    hDG := dynGraphAt_of_agree a.hDG fun addr h1 h2 => hag addr (by omega) (by omega)
    hG_val := a.hG_val, hGV_cap := a.hGV_cap, hGE_cap := a.hGE_cap
    hm_cand := h.at_, hcand_len := rfl, hcand_nd := h.nd
    hcand_sub := fun e he => ⟨h.sub e he, h.lt e he⟩
    hH_sub := a.hH_sub, hH_ends := a.hH_ends
    hsBit := h.sBit
    hdom := fun i hi e he => by
      have h1 := idx_lt_mul i.2 he
      rw [hag (dsDomGenBase a.b a.L a.vCap a.eCap + i.1) (by omega) (by omega),
        hag (dsEdgeDomGenBase a.b a.L a.vCap a.eCap + i.1 * a.eCap + e) (by omega) (by omega)]
      exact a.hdom i hi e he
    hinDom_eq := a.hinDom_eq, hinDom0 := a.hinDom0
    hpi_at := fun i hi e he => by
      have heC : e < a.eCap := by
        have := a.hinDom_eq i hi
        rw [this] at he
        exact a.hGE_cap e (Finset.mem_inter.mp he).2
      have h1 := idx_lt_mul i.2 heC
      have hp : mem (dsPiPtrBase a.b a.L a.vCap a.eCap + i.1 * a.eCap + e) =
          a.mem0 (dsPiPtrBase a.b a.L a.vCap a.eCap + i.1 * a.eCap + e) :=
        hag _ (by omega) (by omega)
      obtain ⟨hw, hf, hb⟩ := a.hpi_at i hi e he
      simp only at hw hf hb ⊢
      rw [hp]
      refine ⟨hw.of_agree fun addr h1 h2 => ?_, hf, hb⟩
      have := a.hfootPi addr (hf addr h1 (by rw [mWalkEncode_length]; omega))
      exact h.agree addr (Or.inr this)
    hpi_walk := fun e he => a.hpi_walk e (h.sub e he), hpiLt_eq := a.hpiLt_eq }

end

end MinCostFlow.DynSpanner.Program
