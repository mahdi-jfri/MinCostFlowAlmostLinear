module

public import MinCostFlow.LastLevelProgram.StagedBranchAppend
public import MinCostFlow.DynSpanner.Program.MergeSort
public import MinCostFlow.Num.UnsignedLess
import Mathlib.Tactic
import WordRAM.Tactic

/-!
# Preparing representative edges

Definition 5.8 (pages 19–20) rebuilds the last level on a simple subgraph.
The program sorts keys by endpoints and edge name, then scans each parallel
class once to choose a shortest edge.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Num DynSpanner.Program SparseCore

/-- Decode the external endpoint names of a live input edge. -/
def representativeEndpointExpr (slotBase : Expr) : Expr :=
  .load (.bin .add (.reg 0) (.load (.bin .add slotBase (.reg 3))))

/-- The original graph's slot tables recover the two endpoint names
used by the representative key. -/
theorem representativeEndpointExpr_eval {w : ℕ} (st : State)
    (G : MGraph) (g vCap eCap e : ℕ)
    (hG : DynGraphAt st.mem g vCap eCap G) (he : e ∈ G.E)
    (hmap : st.regs 0 = dgIntToExtBase g vCap) (hname : st.regs 3 = e)
    (ht : st.regs 1 = dgETailSlotBase g vCap eCap)
    (hh : st.regs 2 = dgEHeadSlotBase g vCap eCap)
    (hfit : g+dynGraphSize vCap eCap < 2^w) :
    (representativeEndpointExpr (.reg 1)).eval w st = some (G.tail e) ∧
    (representativeEndpointExpr (.reg 2)).eval w st = some (G.head e) := by
  obtain ⟨hvalid,hvc,hec,_,_,_,_,_,_,hExt,_,_,_,hends,_⟩ := hG
  obtain ⟨htv,hhv⟩ := hvalid e he
  obtain ⟨htt,hhh⟩ := hends e he
  have htail := (hExt _ htv).2
  have hhead := (hExt _ hhv).2
  have hsTail := hvc _ (hExt _ htv).1
  have hsHead := hvc _ (hExt _ hhv).1
  have hEdge := hec e he
  unfold dynGraphSize at hfit
  have htFit : dgETailSlotBase g vCap eCap+e < 2^w := by unfold dgETailSlotBase; omega
  have hhFit : dgEHeadSlotBase g vCap eCap+e < 2^w := by unfold dgEHeadSlotBase; omega
  have htailFit : dgIntToExtBase g vCap+st.mem (dgExtToIntBase g vCap+G.tail e) < 2^w := by
    unfold dgIntToExtBase
    omega
  have hheadFit : dgIntToExtBase g vCap+st.mem (dgExtToIntBase g vCap+G.head e) < 2^w := by
    unfold dgIntToExtBase
    omega
  simp only [representativeEndpointExpr,Expr.eval,BinOp.eval,hmap,hname,ht,hh,htFit,hhFit,
    ite_eq_left,Option.map_some,htt,hhh,htailFit,hheadFit,htail,hhead,and_self]

/-- Compute the sortable key from the two external endpoint names.
The capacities are runtime inputs in registers four and five. -/
def representativeKeyExpr (lo hi : ℕ) : Expr :=
  .bin .add
    (.bin .mul (.bin .add (.bin .mul (.reg 4) (.reg lo)) (.reg hi)) (.reg 5)) (.reg 3)

/-- Decode the endpoints and return the encoded unordered pair and edge name. -/
def representativeKeyBody : Stmt :=
  .seq (.assign 6 (representativeEndpointExpr (.reg 1)))
    (.seq (.assign 7 (representativeEndpointExpr (.reg 2)))
      (.cond (.bin .lt (.reg 6) (.reg 7))
        (.ret (representativeKeyExpr 6 7)) (.ret (representativeKeyExpr 7 6))))

/-- The key expression fits whenever its final value fits and both
endpoint names and the edge name fit their respective capacities. -/
theorem representativeKeyExpr_eval {w : ℕ} (st : State) (lo hi a b vCap eCap e : ℕ)
    (ha : st.regs lo = a) (hb : st.regs hi = b)
    (hv : st.regs 4 = vCap) (hc : st.regs 5 = eCap) (he : st.regs 3 = e)
    (hcap : 0 < eCap) (hfit : (vCap*a+b)*eCap+e < 2^w) :
    (representativeKeyExpr lo hi).eval w st = some ((vCap*a+b)*eCap+e) := by
  have hprod : (vCap*a+b)*eCap < 2^w := (Nat.le_add_right _ _).trans_lt hfit
  have hpair : vCap*a+b < 2^w := (Nat.le_mul_of_pos_right _ hcap).trans_lt hprod
  have hfirst : vCap*a < 2^w := (Nat.le_add_right _ _).trans_lt hpair
  simp only [representativeKeyExpr,Expr.eval,BinOp.eval,ha,hb,hv,hc,he,
    hfirst,hpair,hprod,hfit,ite_eq_left]

/-- The key procedure returns the same value for either orientation
of the endpoint pair. It makes no writes to memory. -/
theorem representativeKey_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos : ℕ) (G : MGraph) (g vCap eCap e : ℕ)
    (hG : DynGraphAt mem g vCap eCap G) (he : e ∈ G.E)
    (hw : 1 < 2^w) (hg : g+dynGraphSize vCap eCap < 2^w)
    (hcap : vCap*vCap*eCap ≤ 2^w) :
    let args := [dgIntToExtBase g vCap,dgETailSlotBase g vCap eCap,
      dgEHeadSlotBase g vCap eCap,e,vCap,eCap]
    ∃ out cost, Runs w p ω representativeKeyBody (startState args mem pos)
      (.returned (representativeSortKey G vCap eCap e)) out cost ∧
      out.mem = mem ∧ cost ≤ 32 := by
  intro args
  let st := startState args mem pos
  let mid := {st with regs := Function.update st.regs 6 (G.tail e)}
  let out := {mid with regs := Function.update mid.regs 7 (G.head e)}
  obtain ⟨ht,hh⟩ := representativeEndpointExpr_eval (w := w) st G g vCap eCap e
    hG he rfl rfl rfl rfl hg
  have hah : (representativeEndpointExpr (.reg 2)).eval w mid = some (G.head e) := by
    simpa only [representativeEndpointExpr,Expr.eval,mid,Function.update_of_ne
      (by decide : (0 : ℕ) ≠ 6),Function.update_of_ne (by decide : (2 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (3 : ℕ) ≠ 6)] using hh
  have h₁ : Runs w p ω (.assign 6 (representativeEndpointExpr (.reg 1))) st .normal mid 8 :=
    runs_assign_iff.mpr ⟨_,ht,rfl,rfl,rfl⟩
  have h₂ : Runs w p ω (.assign 7 (representativeEndpointExpr (.reg 2))) mid .normal out 8 :=
    runs_assign_iff.mpr ⟨_,hah,rfl,rfl,rfl⟩
  obtain ⟨htv,hhv⟩ := hG.1 e he
  have hf := (representativeSortKey_lt G vCap eCap e (hG.2.1 _ htv) (hG.2.1 _ hhv)
    (hG.2.2.1 e he)).trans_le hcap
  have hePos := Nat.zero_lt_of_lt (hG.2.2.1 e he)
  have h6 : out.regs 6 = G.tail e := by simp [out,mid,Function.update]
  have h7 : out.regs 7 = G.head e := by simp [out]
  have h4 : out.regs 4 = vCap := rfl
  have h5 : out.regs 5 = eCap := rfl
  have h3 : out.regs 3 = e := rfl
  have hbranch : Runs w p ω (.cond (.bin .lt (.reg 6) (.reg 7))
        (.ret (representativeKeyExpr 6 7)) (.ret (representativeKeyExpr 7 6))) out
      (.returned (representativeSortKey G vCap eCap e)) out 14 := by
    by_cases h : G.tail e < G.head e
    · have hk : representativeSortKey G vCap eCap e =
          (vCap*G.tail e+G.head e)*eCap+e := by
        simp [representativeSortKey,edgePairKey,min_eq_left h.le,max_eq_right h.le]
      refine runs_cond_iff.mpr ⟨1,10,?_,?_,rfl⟩
      · simp [Expr.eval,BinOp.eval,h6,h7,h,hw]
      · simp only [one_ne_zero,ite_false]
        exact runs_ret_iff.mpr ⟨_,hk.symm ▸ representativeKeyExpr_eval out 6 7 _ _ _ _ _
          h6 h7 h4 h5 h3 hePos (hk ▸ hf),rfl,rfl,rfl⟩
    · have hk : representativeSortKey G vCap eCap e =
          (vCap*G.head e+G.tail e)*eCap+e := by
        simp [representativeSortKey,edgePairKey,min_eq_right (Nat.le_of_not_gt h),
          max_eq_left (Nat.le_of_not_gt h)]
      refine runs_cond_iff.mpr ⟨0,10,?_,?_,rfl⟩
      · simp [Expr.eval,BinOp.eval,h6,h7,h]
      · simp only [ite_true]
        exact runs_ret_iff.mpr ⟨_,hk.symm ▸ representativeKeyExpr_eval out 7 6 _ _ _ _ _
          h7 h6 h4 h5 h3 hePos (hk ▸ hf),rfl,rfl,rfl⟩
  have htail := runs_seq_iff.mpr (Or.inr ⟨out,8,14,h₂,hbranch,rfl⟩)
  exact ⟨out,32,runs_seq_iff.mpr (Or.inr ⟨mid,8,23,h₁,htail,rfl⟩),rfl,le_rfl⟩

/-- The scan can call the key procedure for any live edge. Its
source table pointers and capacity words are ordinary call arguments. -/
def representativeKeyContract (w g vCap eCap : ℕ) (G : MGraph) : Contract where
  pre args mem := ∃ e ∈ G.E,
    args = [dgIntToExtBase g vCap,dgETailSlotBase g vCap eCap,
      dgEHeadSlotBase g vCap eCap,e,vCap,eCap] ∧
    DynGraphAt mem g vCap eCap G ∧ 1 < 2^w ∧
    g+dynGraphSize vCap eCap < 2^w ∧ vCap*vCap*eCap ≤ 2^w
  post args mem ret out := ∃ e,
    args[3]? = some e ∧ ret = representativeSortKey G vCap eCap e ∧ out = mem
  cost _ _ := 32

/-- Install the canonical key procedure for the live-edge scan. -/
theorem representativeKey_meetsContract {w entry g vCap eCap : ℕ} {p : Program}
    (G : MGraph) (he : p.procs[entry]? = some representativeKeyBody) :
    MeetsContract w p entry (representativeKeyContract w g vCap eCap G) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨e,he',rfl,hG,hw,hg,hcap⟩ := hpre
  obtain ⟨out,cost,hrun,hmem,hcost⟩ :=
    representativeKey_runs (p := p) (ω := ω) mem pos G g vCap eCap e hG he' hw hg hcap
  exact ⟨.returned (representativeSortKey G vCap eCap e),out,cost,hrun,
    ⟨e,rfl,rfl,hmem⟩,hcost⟩

/-- Read the next live edge, then store its sortable representative key.
Registers zero through five hold the endpoint-map base, slot table
bases, live-edge list, vertex capacity and edge capacity. -/
def representativeKeyScanStep (entry : ℕ) : Stmt :=
  .seq (.call 9 entry [.reg 0,.reg 1,.reg 2,.load (.bin .add (.reg 3) (.reg 8)),.reg 4,.reg 5])
    (.store (.bin .add (.reg 6) (.reg 8)) (.reg 9))

/-- Each scan iteration writes one key and preserves the live-edge list
and every other cell. -/
theorem representativeKeyScanStep_runs {w entry g vCap eCap : ℕ}
    {p : Program} {ω : ℕ → Bool} (st : State) (G : MGraph) (e src dst i : ℕ)
    (hc : MeetsContract w p entry (representativeKeyContract w g vCap eCap G))
    (hG : DynGraphAt st.mem g vCap eCap G) (he : e ∈ G.E)
    (h0 : st.regs 0 = dgIntToExtBase g vCap) (h1 : st.regs 1 = dgETailSlotBase g vCap eCap)
    (h2 : st.regs 2 = dgEHeadSlotBase g vCap eCap) (h3 : st.regs 3 = src)
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap) (h6 : st.regs 6 = dst)
    (h8 : st.regs 8 = i) (hread : st.mem (src+i) = e)
    (hw : 1 < 2^w) (hg : g+dynGraphSize vCap eCap < 2^w)
    (hcap : vCap*vCap*eCap ≤ 2^w) (hs : src+i < 2^w) (hd : dst+i < 2^w)
    (hwords : ∀ a ∈ [dgIntToExtBase g vCap,dgETailSlotBase g vCap eCap,
      dgEHeadSlotBase g vCap eCap,e,vCap,eCap], a < 2^w) :
    ∃ out cost, Runs w p ω (representativeKeyScanStep entry) st .normal out cost ∧
      out.mem = Function.update st.mem (dst+i) (representativeSortKey G vCap eCap e) ∧
      (∀ r, r ≠ 9 → out.regs r = st.regs r) ∧ cost ≤ 48 := by
  have ha : evalArgs w st
      [.reg 0,.reg 1,.reg 2,.load (.bin .add (.reg 3) (.reg 8)),.reg 4,.reg 5] =
      some [dgIntToExtBase g vCap,dgETailSlotBase g vCap eCap,
        dgEHeadSlotBase g vCap eCap,e,vCap,eCap] := by
    simp only [evalArgs,Expr.eval,BinOp.eval,h0,h1,h2,h3,h4,h5,h8,hread,hs,ite_eq_left,Option.map_some]
  obtain ⟨mid,c,ret,hr,hpost,hret,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 9) hc ha hwords ⟨e,he,rfl,hG,hw,hg,hcap⟩ ω
  obtain ⟨e',heq,hkey,hmem⟩ := hpost
  have he' : e = e' := Option.some.inj heq
  subst e'
  let out := {mid with mem := Function.update mid.mem (dst+i) (representativeSortKey G vCap eCap e)}
  have hstore : Runs w p ω (.store (.bin .add (.reg 6) (.reg 8)) (.reg 9)) mid .normal out 5 :=
    runs_store_iff.mpr ⟨dst+i,representativeSortKey G vCap eCap e,
      by simp [Expr.eval,BinOp.eval,(hregs _ (by decide)).trans h6,(hregs _ (by decide)).trans h8,hd],
      congrArg some (hret.trans hkey),rfl,rfl,rfl⟩
  change c ≤ 9+32+1 at hcost
  exact ⟨out,c+6,runs_seq_iff.mpr (Or.inr ⟨mid,c,5,hr,hstore,rfl⟩),
    by simp [out,hmem],hregs,by omega⟩

/-- The dynamic graph encoding depends only on the cells in its allocated block. -/
theorem representativeGraph_frame {mem out : ℕ → ℕ} {g vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem g vCap eCap G)
    (agree : ∀ a, g ≤ a → a < g + dynGraphSize vCap eCap → out a = mem a) :
    DynGraphAt out g vCap eCap G := by
  obtain ⟨valid,hv,he,hvc,hec,hn,hm,hvp,⟨vs,hvs,hvn,hvm,hvl,hvi⟩,
    hforward,hback,hep,⟨es,hes,hen,hem,hel,hei⟩,hends,⟨inc,hinc⟩⟩ := hG
  simp only [dynGraphSize] at agree
  refine ⟨valid,hv,he,?_,?_,?_,?_,?_,⟨vs,hvs,hvn,hvm,?_,?_⟩,
    ?_,?_,?_,⟨es,hes,hen,hem,?_,?_⟩,?_,⟨inc,?_⟩⟩
  all_goals
    simp only [dgVCapOff,dgECapOff,dgNOff,dgMOff,dgVPresBase,dgVListBase,dgVPosBase,
      dgExtToIntBase,dgIntToExtBase,dgEPresBase,dgEListBase,dgEPosBase,dgETailSlotBase,
      dgEHeadSlotBase,dgHePrevBase,dgHeNextBase,dgIncHeadBase,dgSlotDegBase] at *
  · rwa [agree _ (by omega) (by omega)]
  · rwa [agree _ (by omega) (by omega)]
  · rwa [agree _ (by omega) (by omega)]
  · rwa [agree _ (by omega) (by omega)]
  · intro v hv'
    rw [agree _ (by omega) (by omega)]
    exact hvp v hv'
  · intro j hj
    have hj' := hv _ ((hvm _).mp (List.getElem_mem hj))
    have hlen : vs.length ≤ vCap := by
      simpa only [List.length_range] using List.Nodup.length_le_of_subset hvn (l₂ := List.range vCap)
        (fun x hx => List.mem_range.mpr (hv x ((hvm x).mp hx)))
    rw [agree _ (by omega) (by omega)]
    exact hvl j hj
  · intro j hj
    have hj' := hv _ ((hvm _).mp (List.getElem_mem hj))
    rw [agree _ (by omega) (by omega)]
    exact hvi j hj
  · intro v hv'
    have hvb := hv v hv'
    obtain ⟨hs,hmap⟩ := hforward v hv'
    have hsb := hv _ hs
    rw [agree _ (by omega) (by omega),agree _ (by omega) (by omega)]
    exact ⟨hs,hmap⟩
  · intro v hv'
    have hvb := hv v hv'
    obtain ⟨hs,hmap⟩ := hback v hv'
    have hsb := hv _ hs
    rw [agree _ (by omega) (by omega),agree _ (by omega) (by omega)]
    exact ⟨hs,hmap⟩
  · intro e he'
    rw [agree _ (by omega) (by omega)]
    exact hep e he'
  · intro j hj
    have hj' := he _ ((hem _).mp (List.getElem_mem hj))
    have hlen : es.length ≤ eCap := by
      simpa only [List.length_range] using List.Nodup.length_le_of_subset hen (l₂ := List.range eCap)
        (fun x hx => List.mem_range.mpr (he x ((hem x).mp hx)))
    rw [agree _ (by omega) (by omega)]
    exact hel j hj
  · intro j hj
    have hj' := he _ ((hem _).mp (List.getElem_mem hj))
    rw [agree _ (by omega) (by omega)]
    exact hei j hj
  · intro e he'
    have heb := he e he'
    have ht := hv _ ((valid e he').1)
    have hh := hv _ ((valid e he').2)
    obtain ⟨hTail,hHead⟩ := hends e he'
    constructor
    · rwa [agree _ (by omega) (by omega),agree _ (by omega) (by omega)]
    · rwa [agree _ (by omega) (by omega),agree _ (by omega) (by omega)]
  · intro v hv'
    obtain ⟨⟨nodup,range,first,links⟩,deg,incidence⟩ := hinc v hv'
    refine ⟨⟨nodup,range,?_,?_⟩,?_,?_⟩
    · rwa [agree _ (by omega) (by omega)]
    · intro j hj
      have hj' := range _ (List.getElem_mem hj)
      rw [agree _ (by omega) (by omega),agree _ (by omega) (by omega)]
      exact links j hj
    · rwa [agree _ (by omega) (by omega)]
    · intro h
      by_cases hb : h < 2*eCap
      · have he' : h/2 < eCap := by omega
        rw [agree (g+4+7*vCap+3*eCap+h/2) (by omega) (by omega),
          agree (g+4+7*vCap+4*eCap+h/2) (by omega) (by omega)]
        exact incidence h
      · simpa [hb] using incidence h

/-- Scan the live edge list once and write keys in list order. -/
def representativeKeyScan (entry : ℕ) : Stmt :=
  forRange 8 (.const 0) (.reg 7) (representativeKeyScanStep entry)

/-- The key scan fills the destination array and preserves all other cells.
The graph view must be supported outside the destination array. -/
theorem representativeKeyScan_triple {w entry g vCap eCap : ℕ}
    {p : Program} (initial : State) (G : MGraph) (edges : List ℕ) (src dst : ℕ)
    (hc : MeetsContract w p entry (representativeKeyContract w g vCap eCap G))
    (hgraph : ∀ mem, (∀ a, a < dst ∨ dst + edges.length ≤ a → mem a = initial.mem a) →
      DynGraphAt mem g vCap eCap G)
    (h0 : initial.regs 0 = dgIntToExtBase g vCap)
    (h1 : initial.regs 1 = dgETailSlotBase g vCap eCap)
    (h2 : initial.regs 2 = dgEHeadSlotBase g vCap eCap)
    (h3 : initial.regs 3 = src) (h4 : initial.regs 4 = vCap)
    (h5 : initial.regs 5 = eCap) (h6 : initial.regs 6 = dst)
    (h7 : initial.regs 7 = edges.length)
    (hedges : ∀ i (hi : i < edges.length), edges[i] ∈ G.E ∧ initial.mem (src+i) = edges[i])
    (hw : 1 < 2^w) (hg : g+dynGraphSize vCap eCap < 2^w)
    (hcap : vCap*vCap*eCap ≤ 2^w)
    (hs : src+edges.length < 2^w) (hd : dst+edges.length < 2^w)
    (hsep : src+edges.length ≤ dst ∨ dst+edges.length ≤ src)
    (hwords : ∀ e ∈ G.E, ∀ a ∈ [dgIntToExtBase g vCap,dgETailSlotBase g vCap eCap,
      dgEHeadSlotBase g vCap eCap,e,vCap,eCap], a < 2^w) :
    Triple w p (fun st => st = initial) (representativeKeyScan entry)
      (normalPost fun st =>
        (∀ j (hj : j < edges.length), st.mem (dst+j) =
          representativeSortKey G vCap eCap edges[j]) ∧
        (∀ a, a < dst ∨ dst+edges.length ≤ a → st.mem a = initial.mem a) ∧
        ∀ r, r ≠ 8 → r ≠ 9 → st.regs r = initial.regs r)
      (fun _ => 57 * edges.length + 7) := by
  let frame := fun (st : State) =>
    ∀ a, a < dst ∨ dst+edges.length ≤ a → st.mem a = initial.mem a
  let keysWritten := fun i (st : State) =>
    ∀ j (hj : j < min i edges.length), st.mem (dst+j) =
      representativeSortKey G vCap eCap edges[j]
  let Inv := fun i (st : State) =>
    (∀ r, r ≠ 8 → r ≠ 9 → st.regs r = initial.regs r) ∧ st.regs 8 = i ∧ keysWritten i st ∧ frame st
  have loop := Triple.forRange_const (p := p) (r := 8) (lo := .const 0) (hi := .reg 7)
    (body := representativeKeyScanStep entry) (P := fun st => st = initial)
    (Inv := Inv) 48 0 edges.length (Nat.zero_le _) hw (fun _ => by omega)
    (fun st hst => by
      subst st
      refine ⟨by simp [Expr.eval,show 0 < 2^w by omega], ?_⟩
      refine ⟨fun _ hr _ => Function.update_of_ne hr .., (by simp), ?_,
        fun _ _ => rfl⟩
      intro j hj
      simp at hj)
    (fun _ _ _ _ h => h.2.1)
    (fun _ st _ _ h => by simp [Expr.eval,(h.1 7 (by decide) (by decide)).trans h7])
    (fun i _ hi => by
      intro st ω ⟨hreg, hindex, hprefix, hframe⟩
      obtain ⟨he, hread⟩ := hedges i hi
      have hsource := (hframe (src+i) (by omega)).trans hread
      obtain ⟨out,c,hrun,hm,hregs,hcost⟩ :=
        representativeKeyScanStep_runs st G edges[i] src dst i hc (hgraph _ hframe) he
          ((hreg 0 (by decide) (by decide)).trans h0) ((hreg 1 (by decide) (by decide)).trans h1)
          ((hreg 2 (by decide) (by decide)).trans h2) ((hreg 3 (by decide) (by decide)).trans h3)
          ((hreg 4 (by decide) (by decide)).trans h4) ((hreg 5 (by decide) (by decide)).trans h5)
          ((hreg 6 (by decide) (by decide)).trans h6) hindex hsource hw hg hcap
          (by omega) (by omega) (hwords _ he)
      refine ⟨.normal,out,c,hrun,⟨⟨?_,(by simp),?_,?_⟩,
        (hregs 8 (by decide)).trans hindex⟩,hcost⟩
      · intro r hr8 hr9
        exact (Function.update_of_ne hr8 ..).trans ((hregs r hr9).trans (hreg r hr8 hr9))
      · intro j hj
        change out.mem (dst+j) = _
        by_cases heq : j = i
        · subst j
          rw [hm,Function.update_self]
        · rw [hm, Function.update_of_ne (show dst+j ≠ dst+i by omega)]
          exact hprefix j (by omega)
      · intro a ha
        change out.mem a = initial.mem a
        rw [hm,Function.update_of_ne (show a ≠ dst+i by omega)]
        exact hframe a ha)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | normal => exact ⟨fun j hj => h.2.2.1 j (by simpa using hj),h.2.2.2,h.1⟩
    | returned _ => exact False.elim h
  · intro _ _
    simp [Expr.size_reg,Expr.size_const,Nat.mul_comm]

/-- Read the edge enumeration directly from the dynamic graph layout.
The key array is disjoint from the input graph block. -/
theorem representativeKeyScan_graph_triple {w entry g vCap eCap : ℕ}
    {p : Program} (initial : State) (G : MGraph) (dst : ℕ)
    (hc : MeetsContract w p entry (representativeKeyContract w g vCap eCap G))
    (hG : DynGraphAt initial.mem g vCap eCap G)
    (h0 : initial.regs 0 = dgIntToExtBase g vCap)
    (h1 : initial.regs 1 = dgETailSlotBase g vCap eCap)
    (h2 : initial.regs 2 = dgEHeadSlotBase g vCap eCap)
    (h3 : initial.regs 3 = dgEListBase g vCap eCap)
    (h4 : initial.regs 4 = vCap) (h5 : initial.regs 5 = eCap)
    (h6 : initial.regs 6 = dst) (h7 : initial.regs 7 = G.m)
    (hw : 1 < 2^w) (hg : g+dynGraphSize vCap eCap < 2^w)
    (hcap : vCap*vCap*eCap ≤ 2^w) (hd : dst+G.m < 2^w)
    (hsep : g+dynGraphSize vCap eCap ≤ dst ∨ dst+G.m ≤ g) :
    Triple w p (fun st => st = initial) (representativeKeyScan entry)
      (normalPost fun st =>
        DynGraphAt st.mem g vCap eCap G ∧
        (∃ edges : List ℕ, edges.length = G.m ∧ edges.Nodup ∧
          (∀ e, e ∈ edges ↔ e ∈ G.E) ∧
          ListAt st.mem dst (edges.map (representativeSortKey G vCap eCap))) ∧
        (∀ a, a < dst ∨ dst+G.m ≤ a → st.mem a = initial.mem a) ∧
        ∀ r, r ≠ 8 → r ≠ 9 → st.regs r = initial.regs r)
      (fun _ => 57 * G.m + 7) := by
  have heCap := hG.2.2.1
  obtain ⟨edges,hlen,hnodup,hmem,hlist,_⟩ := hG.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmCap : G.m ≤ eCap := by
    rw [← hlen]
    simpa only [List.length_range] using
      hnodup.length_le_of_subset (l₂ := List.range eCap)
        (fun e he => List.mem_range.mpr (heCap e ((hmem e).mp he)))
  have hframe (mem : ℕ → ℕ)
      (h : ∀ a, a < dst ∨ dst+edges.length ≤ a → mem a = initial.mem a) :
      DynGraphAt mem g vCap eCap G := by
    refine representativeGraph_frame hG fun a ha hb => h a ?_
    rw [hlen]
    omega
  have hs : dgEListBase g vCap eCap + edges.length < 2^w := by
    simp only [dgEListBase,dynGraphSize,hlen] at hg ⊢
    omega
  have hdisjoint : dgEListBase g vCap eCap + edges.length ≤ dst ∨
      dst+edges.length ≤ dgEListBase g vCap eCap := by
    simp only [dgEListBase,dynGraphSize,hlen] at hsep ⊢
    omega
  have hwords e (he : e ∈ G.E) :
      ∀ a ∈ [dgIntToExtBase g vCap,dgETailSlotBase g vCap eCap,
        dgEHeadSlotBase g vCap eCap,e,vCap,eCap], a < 2^w := by
    have heb := heCap e he
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    simp only [dynGraphSize] at hg
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;>
      try simp only [dgIntToExtBase,dgETailSlotBase,dgEHeadSlotBase]
    all_goals omega
  have run := representativeKeyScan_triple initial G edges _ dst hc hframe
    h0 h1 h2 h3 h4 h5 h6 (h7.trans hlen.symm)
    (fun i hi => ⟨(hmem _).mp (List.getElem_mem hi), hlist i hi⟩)
    hw hg hcap hs (by rwa [hlen]) hdisjoint hwords
  refine run.conseq (fun _ h => h) ?_ (fun _ _ => by rw [hlen])
  intro o st h
  cases o with
  | returned _ => exact h
  | normal =>
    refine ⟨hframe _ h.2.1,⟨edges,hlen,hnodup,hmem,?_⟩,?_,h.2.2⟩
    · intro i hi
      simpa only [List.getElem_map] using h.1 i (by simpa only [List.length_map] using hi)
    · simpa only [hlen] using h.2.1

/-- Sort the edge keys in place, using a separate scratch block. -/
def representativeKeySort (entry : ℕ) : Stmt :=
  .call 9 entry [.reg 6,.reg 7,.reg 10]

/-- Sorting preserves the key multiset and the graph block. -/
theorem representativeKeySort_runs {w entry g vCap eCap : ℕ} {p : Program}
    {ω : ℕ → Bool} (st : State) (G : MGraph) (keys : List ℕ) (dst scratch : ℕ)
    (hc : MeetsContract w p entry (mergeSortContract w keys))
    (hG : DynGraphAt st.mem g vCap eCap G)
    (h6 : st.regs 6 = dst) (h7 : st.regs 7 = keys.length) (h10 : st.regs 10 = scratch)
    (hkeys : ListAt st.mem dst keys) (hbound : ∀ k ∈ keys, k < 2^w)
    (hw : 16 ≤ 2^w) (hd : dst+keys.length < 2^w) (hs : scratch+keys.length < 2^w)
    (hsep : dst+keys.length ≤ scratch ∨ scratch+keys.length ≤ dst)
    (hdg : g+dynGraphSize vCap eCap ≤ dst ∨ dst+keys.length ≤ g)
    (hsg : g+dynGraphSize vCap eCap ≤ scratch ∨ scratch+keys.length ≤ g) :
    ∃ out cost sorted, Runs w p ω (representativeKeySort entry) st .normal out cost ∧
      sorted.Perm keys ∧ sorted.Pairwise (· ≤ ·) ∧ ListAt out.mem dst sorted ∧
      DynGraphAt out.mem g vCap eCap G ∧
      (∀ a, (a < dst ∨ dst+keys.length ≤ a) →
        (a < scratch ∨ scratch+keys.length ≤ a) → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 9 → out.regs r = st.regs r) ∧
      cost ≤ 200*keys.length*(Nat.log 2 (keys.length+1)+1)+54 := by
  have ha : evalArgs w st [.reg 6,.reg 7,.reg 10] = some [dst,keys.length,scratch] := by
    simp [evalArgs,Expr.eval,h6,h7,h10]
  have hwords : ∀ a ∈ [dst,keys.length,scratch], a < 2^w := by
    intro a ha'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha'
    rcases ha' with rfl|rfl|rfl <;> omega
  obtain ⟨out,c,ret,hr,hpost,_,hregs,hcost⟩ :=
    runs_call_of_meetsContract (r := 9) hc ha hwords
      ⟨dst,scratch,rfl,hw,hd,hs,hsep,hkeys,hbound⟩ ω
  obtain ⟨d,s,sorted,heq,_,hperm,hsorted,hout,hframe⟩ := hpost
  simp only [List.cons.injEq,true_and,and_true] at heq
  obtain ⟨rfl,rfl⟩ := heq
  refine ⟨out,c,sorted,hr,hperm,hsorted,hout,?_,hframe,hregs,?_⟩
  · exact representativeGraph_frame hG fun a ha hb => hframe a (by omega) (by omega)
  · change c ≤ 3 + (200*keys.length*(Nat.log 2 (keys.length+1)+1)+50) + 1 at hcost
    omega

/-- The high digits are the parallel-class identifier. -/
def representativeClassExpr (key : Expr) : Expr := .bin .div key (.reg 5)

/-- The low digit is the original edge name. -/
def representativeNameExpr (key : Expr) : Expr := .bin .mod key (.reg 5)

/-- The two digits of a class identifier are its ordered endpoint names. -/
def representativeClassEnds (key : Expr) : Expr × Expr :=
  let cls := representativeClassExpr key
  (.bin .div cls (.reg 4), .bin .mod cls (.reg 4))

/-- Decoding a key gives the original name and the ordered endpoints.
The class identifier is computed with a single division. -/
theorem representativeKey_eval {w vCap eCap : ℕ} {st : State} {key : Expr}
    (G : MGraph) (e : ℕ) (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap)
    (hkey : key.eval w st = some (representativeSortKey G vCap eCap e))
    (he : e < eCap) (hv : (edgePairKey G e).2 < vCap)
    (hb : representativeSortKey G vCap eCap e < 2^w) :
    (representativeNameExpr key).eval w st = some e ∧
    (representativeClassExpr key).eval w st =
      some (representativeSortKey G vCap eCap e / eCap) ∧
    (representativeClassEnds key).1.eval w st = some (edgePairKey G e).1 ∧
    (representativeClassEnds key).2.eval w st = some (edgePairKey G e).2 := by
  obtain ⟨hname,hends⟩ := representativeSortKey_decode G vCap eCap e he hv
  have hlo : representativeSortKey G vCap eCap e / eCap / vCap = (edgePairKey G e).1 :=
    congrArg Prod.fst hends
  have hhi : representativeSortKey G vCap eCap e / eCap % vCap = (edgePairKey G e).2 :=
    congrArg Prod.snd hends
  have hclass := (Nat.div_le_self _ eCap).trans_lt hb
  have hlob := (Nat.div_le_self _ vCap).trans_lt hclass
  have hhib := (Nat.mod_le _ vCap).trans_lt hclass
  have hnb := (Nat.mod_le _ eCap).trans_lt hb
  simp only [representativeNameExpr,representativeClassExpr,representativeClassEnds,
    Expr.eval,BinOp.eval,hkey,h4,h5,hclass,hlob,hhib,hnb,ite_true,Option.some.injEq]
  exact ⟨hname,True.intro,hlo,hhi⟩

/-- Compare the high digits of two keys to detect a parallel class. -/
def representativeSameClass (left right : Expr) : Expr :=
  .bin .eq (representativeClassExpr left) (representativeClassExpr right)

/-- Equality of the class digits is exactly equality of the ordered endpoints. -/
theorem representativeClass_eq_iff {G : MGraph} {vCap eCap e f : ℕ}
    (he : e < eCap) (hf : f < eCap)
    (hev : (edgePairKey G e).2 < vCap) (hfv : (edgePairKey G f).2 < vCap) :
    representativeSortKey G vCap eCap e / eCap =
      representativeSortKey G vCap eCap f / eCap ↔ edgePairKey G e = edgePairKey G f := by
  constructor
  · intro h
    rw [← (representativeSortKey_decode G vCap eCap e he hev).2,
      ← (representativeSortKey_decode G vCap eCap f hf hfv).2,h]
  · intro h
    have digit (a : ℕ) (ha : a < eCap) :
        representativeSortKey G vCap eCap a / eCap =
          vCap*(edgePairKey G a).1+(edgePairKey G a).2 := by
      rw [representativeSortKey,Nat.mul_comm _ eCap,Nat.mul_add_div (by omega),
        Nat.div_eq_of_lt ha,Nat.add_zero]
    rw [digit e he,digit f hf,h]

/-- The scan can branch on a single word comparison to detect a class boundary. -/
theorem representativeSameClass_eval {w vCap eCap e f : ℕ} {st : State}
    {left right : Expr} (G : MGraph)
    (h4 : st.regs 4 = vCap) (h5 : st.regs 5 = eCap)
    (hl : left.eval w st = some (representativeSortKey G vCap eCap e))
    (hr : right.eval w st = some (representativeSortKey G vCap eCap f))
    (he : e < eCap) (hf : f < eCap)
    (hev : (edgePairKey G e).2 < vCap) (hfv : (edgePairKey G f).2 < vCap)
    (heb : representativeSortKey G vCap eCap e < 2^w)
    (hfb : representativeSortKey G vCap eCap f < 2^w)
    (hw : 1 < 2^w) :
    (representativeSameClass left right).eval w st =
      some (if edgePairKey G e = edgePairKey G f then 1 else 0) := by
  have hleft := (representativeKey_eval G e h4 h5 hl he hev heb).2.1
  have hright := (representativeKey_eval G f h4 h5 hr hf hfv hfb).2.1
  have hclass := representativeClass_eq_iff (G := G) he hf hev hfv
  by_cases h : edgePairKey G e = edgePairKey G f
  · simp [representativeSameClass,Expr.eval,hleft,hright,BinOp.eval,hclass.mpr h,h,hw]
  · have hne := mt hclass.mp h
    simp [representativeSameClass,Expr.eval,hleft,hright,BinOp.eval,hne,h,show 0 < 2^w by omega]

end MinCostFlow.LastLevelProgram
