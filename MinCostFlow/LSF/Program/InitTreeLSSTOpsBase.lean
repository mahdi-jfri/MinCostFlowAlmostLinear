module

public import MinCostFlow.LSF.Program.SharedProcs
public import MinCostFlow.LSF.Program.Utils
public import MinCostFlow.Machine.WideWord.LSSTProgram
public import MinCostFlow.DynSpanner.Program.DynGraphOps
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import MinCostFlow.DynSpanner.Program.DynGraphInsert
import MinCostFlow.LSF.Model
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# InitTreeLSSTOps, first part

The first part of `InitTreeLSSTOps.lean`, split off to keep files short. It contains:
- Local empty dynamic graph initialization
- Contract wrapper for `lsstFrontierProc`
- Copy `G₀` to `dgGPtr` with capacity `(vCap, eCap)`
-/

namespace MinCostFlow.LSF.Program

open WordRAM
open MinCostFlow.DynSpanner.Program
open MinCostFlow.WideWord
open MinCostFlow.LSF

@[expose] public section

/-! ## Local empty dynamic graph initialization -/

/-- Contract for `dgInitEmptyStmt` requiring only local zeros on `[gPtr, gPtr + dynGraphSize vCap eCap)`. -/
def dgInitEmptyLocalContract (w : ℕ) : Contract where
  pre args mem := ∃ gPtr vCap eCap, args = [gPtr, vCap, eCap] ∧
    16 ≤ 2 ^ w ∧ gPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    ∀ i < dynGraphSize vCap eCap, mem (gPtr + i) = 0
  post args mem ret mem' := ∃ gPtr vCap eCap, args = [gPtr, vCap, eCap] ∧ ret = gPtr ∧
    DynGraphAt mem' gPtr vCap eCap
      { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 } ∧
    (∀ addr, addr < gPtr ∨ gPtr + 4 ≤ addr → mem' addr = mem addr)
  cost _ _ := 40

/-- `dgInitEmptyStmt` works on any locally zeroed dynamic-graph buffer. -/
theorem dgInitEmptyLocal_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b dgOpsProcs) :
    MeetsContract w p (b + dgIdxInitEmpty) (dgInitEmptyLocalContract w) := by
  have hp0 : p.procs[b + dgIdxInitEmpty]? = some dgInitEmptyStmt :=
    hp.get (i := dgIdxInitEmpty) (by simp [dgOpsProcs, dgIdxInitEmpty])
  refine meetsContract_of_runs hp0 fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨gPtr, vCap, eCap, rfl, h16, hbd, hzero⟩
  have hgPtr : gPtr < 2 ^ w := hwords gPtr (by simp)
  have hvCap : vCap < 2 ^ w := hwords vCap (by simp)
  have heCap : eCap < 2 ^ w := hwords eCap (by simp)
  have hlt1 : gPtr + 1 < 2 ^ w := by dsimp [dynGraphSize] at hbd; omega
  have hlt2 : gPtr + 2 < 2 ^ w := by dsimp [dynGraphSize] at hbd; omega
  have hlt3 : gPtr + 3 < 2 ^ w := by dsimp [dynGraphSize] at hbd; omega
  have hw1 : 1 < 2 ^ w := by omega
  let memZ : ℕ → ℕ := fun a => if a < gPtr then mem a else 0
  have hzeroZ : ZeroFrom memZ gPtr := fun a ha => by
    dsimp only [memZ]; exact ite_eq_right (by omega)
  have hmZ := dgInitEmpty_meetsContract (w := w) hp
  have hpreZ : (dgInitEmptyContract w).pre [gPtr, vCap, eCap] memZ :=
    ⟨gPtr, vCap, eCap, rfl, h16, hbd, hzeroZ⟩
  rcases hmZ [gPtr, vCap, eCap] memZ pos ω hwords hpreZ with
    ⟨_, _, oZ, stZ, _, _, hpostZ, _⟩
  rcases hpostZ with ⟨gZ, vZ, eZ, hargsZ, _, hdgZ, hframeZ, _⟩
  simp only [List.cons.injEq, and_true] at hargsZ
  rcases hargsZ with ⟨rfl, rfl, rfl⟩
  let mem1 := Function.update mem gPtr vCap
  let mem2 := Function.update mem1 (gPtr + 1) eCap
  let mem3 := Function.update mem2 (gPtr + 2) 0
  let mem4 := Function.update mem3 (gPtr + 3) 0
  have hfr4 : ∀ addr, addr < gPtr ∨ gPtr + 4 ≤ addr → mem4 addr = mem addr := by
    intro addr haddr
    dsimp only [mem4, mem3, mem2, mem1]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hagree : ∀ addr, gPtr ≤ addr → addr < gPtr + dynGraphSize vCap eCap →
      mem4 addr = stZ.mem addr := by
    intro addr ha1 ha2
    by_cases ha4 : addr < gPtr + 4
    · have h0' : stZ.mem (gPtr + dgVCapOff) = vCap := hdgZ.2.2.2.1
      have h1' : stZ.mem (gPtr + dgECapOff) = eCap := hdgZ.2.2.2.2.1
      have h2' : stZ.mem (gPtr + dgNOff) = 0 := hdgZ.2.2.2.2.2.1
      have h3' : stZ.mem (gPtr + dgMOff) = 0 := hdgZ.2.2.2.2.2.2.1
      dsimp only [dgVCapOff, dgECapOff, dgNOff, dgMOff] at h0' h1' h2' h3'
      have hcases : addr = gPtr ∨ addr = gPtr + 1 ∨ addr = gPtr + 2 ∨ addr = gPtr + 3 := by omega
      rcases hcases with rfl | rfl | rfl | rfl
      · simpa [mem4, mem3, mem2, mem1] using h0'.symm
      · simp [mem4, mem3, mem2, mem1, h1'.symm]
      · simp [mem4, mem3, mem2, mem1, h2'.symm]
      · simp [mem4, mem3, mem2, mem1, h3'.symm]
    · have hge4 : gPtr + 4 ≤ addr := by omega
      have hzm : stZ.mem addr = memZ addr := hframeZ addr (Or.inr hge4)
      have hz0 : memZ addr = 0 := by dsimp only [memZ]; exact ite_eq_right (by omega)
      have hm4 : mem4 addr = mem addr := hfr4 addr (Or.inr hge4)
      have hm0 : mem addr = 0 := by
        have hsub : addr - gPtr < dynGraphSize vCap eCap := by omega
        simpa [Nat.add_sub_cancel' ha1] using hzero (addr - gPtr) hsub
      rw [hm4, hm0, hzm, hz0]
  have hdg4 : DynGraphAt mem4 gPtr vCap eCap
      { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 } :=
    DynGraphAt.of_agree hdgZ hagree
  refine runs_start_le ?_
  dsimp only [dgInitEmptyStmt]
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_ret_le (by eval_expr) ?_ (by simp [dgInitEmptyLocalContract, Expr.size])
  exact ⟨gPtr, vCap, eCap, rfl, rfl, hdg4, hfr4⟩

/-! ## Contract wrapper for `lsstFrontierProc` -/

/-- `Contract` wrapper around `lsst_frontier_runs` for `lsstFrontierProc`. -/
noncomputable def lsstFrontierContract (Q_AN : Program) (c_AN : ℕ) (K_AN : ℝ) (w h : ℕ)
    (G : IndexedGraph) (v ℓ : ℕ → ℝ) (P_fp : ℕ) : Contract where
  pre args mem := ∃ n0 M_copies copyTailPtr copyHeadPtr copyLenPtr copyWtPtr L_in L_sim
      outOrigPtr outBridgePtr outHdrPtr lsstHeap,
    args = [n0, M_copies, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr,
      L_in, L_sim, outOrigPtr, outBridgePtr, outHdrPtr, lsstHeap] ∧
    n0 = G.n ∧ M_copies = G.m ∧ 1 ≤ c_AN ∧ G.Valid ∧ 1 ≤ h ∧ 3 * h + 2 ≤ w ∧ 1 ≤ L_in ∧
    lsstLSimMin c_AN G.n G.m L_in h ≤ L_sim ∧
    copyTailPtr + G.m ≤ lsstHeap ∧ copyHeadPtr + G.m ≤ lsstHeap ∧
    copyLenPtr + G.m * L_in ≤ lsstHeap ∧ copyWtPtr + G.m * L_in ≤ lsstHeap ∧
    outOrigPtr + G.n ≤ lsstHeap ∧ outBridgePtr + 2 * G.n ≤ lsstHeap ∧ outHdrPtr + 2 ≤ lsstHeap ∧
    DisjointRanges outOrigPtr G.n outBridgePtr (2 * G.n) ∧
    DisjointRanges outOrigPtr G.n outHdrPtr 2 ∧
    DisjointRanges outBridgePtr (2 * G.n) outHdrPtr 2 ∧
    ListAt mem copyTailPtr (List.ofFn fun i : Fin G.m => G.tail i.1) ∧
    ListAt mem copyHeadPtr (List.ofFn fun i : Fin G.m => G.head i.1) ∧
    (∀ e < G.m, Num.Valid mem (copyLenPtr + e * L_in) h L_in ∧
      Num.fixVal mem (copyLenPtr + e * L_in) h L_in P_fp = ℓ e ∧ 0 < ℓ e) ∧
    (∀ e < G.m, Num.Valid mem (copyWtPtr + e * L_in) h L_in ∧
      Num.fixVal mem (copyWtPtr + e * L_in) h L_in P_fp = v e ∧ 0 < v e) ∧
    ZeroFrom mem lsstHeap ∧
    lsstHeap + lsstSpace Q_AN K_AN G.n G.m L_sim h < 2 ^ w
  post args mem ret mem' := ∃ n0 M_copies copyTailPtr copyHeadPtr copyLenPtr copyWtPtr L_in L_sim
      outOrigPtr outBridgePtr outHdrPtr lsstHeap,
    args = [n0, M_copies, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr,
      L_in, L_sim, outOrigPtr, outBridgePtr, outHdrPtr, lsstHeap] ∧
    lsstHeap ≤ ret ∧
    ret ≤ lsstHeap + lsstSpace Q_AN K_AN G.n G.m L_sim h ∧
    LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr lsstHeap mem (.returned 0) mem' ∧
    ZeroFrom mem' ret
  cost args _ :=
    let L_in := args.getD 6 0
    let L_sim := args.getD 7 0
    lsstCost Q_AN K_AN c_AN G.n G.m L_in L_sim h + 10

lemma lsstFrontierProc_noRand (b h : ℕ) : (lsstFrontierProc b h).NoRand := by
  simp [lsstFrontierProc, Stmt.NoRand]

/-- Verified contract for `lsstFrontierProc` given `lsstModule` and oracle hypothesis `hQ`. -/
theorem lsstFrontier_meetsContract {w h bLsst bSelf c_AN : ℕ} {p Q_AN : Program} {K_AN : ℝ}
    {G : IndexedGraph} {v ℓ : ℕ → ℝ} {P_fp : ℕ}
    (hpSelf : p.procs[bSelf]? = some (lsstFrontierProc bLsst h))
    (hpLsst : p.HasAt bLsst (lsstModule Q_AN bLsst h))
    (hQ : ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
      (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
      ∃ out cost,
        RunsTo (wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
          G_a.IsSpanningTree out ∧
          G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
          (cost : ℝ) ≤ K_AN * (G_a.m + 1) *
            (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight)) :
    MeetsContract w p bSelf (lsstFrontierContract Q_AN c_AN K_AN w h G v ℓ P_fp) := by
  refine meetsContract_of_runs hpSelf fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨n0, M_copies, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, L_in, L_sim,
    outOrigPtr, outBridgePtr, outHdrPtr, lsstHeap, rfl, rfl, rfl,
    hc, hGval, hh, hw, hLin, hLsim, ht1, ht2, ht3, ht4, ho1, ho2, ho3,
    hd1, hd2, hd3, hLa, hHb, hLen, hWt, hzf, hsp⟩
  have hres := lsst_frontier_runs (ω := ω) hpLsst hQ G v ℓ P_fp
    copyTailPtr copyHeadPtr copyLenPtr copyWtPtr L_in L_sim outOrigPtr outBridgePtr outHdrPtr
    lsstHeap mem pos hwords hc hGval hh hw hLin hLsim ht1 ht2 ht3 ht4 ho1 ho2 ho3
    hd1 hd2 hd3 hLa hHb hLen hWt hzf hsp
  rcases hres with ⟨hp_end, st', c, hruns, hge, hle, hpost, hzf', hcost⟩
  refine ⟨.returned hp_end, st', c, hruns,
    ⟨G.n, G.m, copyTailPtr, copyHeadPtr, copyLenPtr, copyWtPtr, L_in, L_sim,
      outOrigPtr, outBridgePtr, outHdrPtr, lsstHeap, rfl, hge, hle, hpost, hzf'⟩, ?_⟩
  simpa [lsstFrontierContract] using hcost

/-! ## Copy `G₀` to `dgGPtr` with capacity `(vCap, eCap)` -/

/-- Copy `G₀` from `(g0Ptr, eListPtr, vListPtr)` into `dgGPtr` with caps `(vCap, eCap)`.
Args: `[g0Ptr, dgGPtr, eListPtr, vListPtr, vCap, eCap, n0, m0]`. -/
def initCopyGStmt (bDg : ℕ) : Stmt :=
  .call 8 (bDg + dgIdxInitEmpty) [.reg 1, .reg 4, .reg 5] ;;
  forRange 8 (.const 0) (.reg 6)
    (.assign 9 (.load (.bin .add (.reg 3) (.reg 8))) ;;
     .call 10 (bDg + dgIdxAddVertex) [.reg 1, .reg 9]) ;;
  forRange 8 (.const 0) (.reg 7)
    (.assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ;;
     .call 10 (bDg + dgIdxGetTail) [.reg 0, .reg 9] ;;
     .call 11 (bDg + dgIdxGetHead) [.reg 0, .reg 9] ;;
     .call 12 (bDg + 7 + dgIdxInsertEdge) [.reg 1, .reg 9, .reg 10, .reg 11]) ;;
  .ret (.const 0)

lemma initCopyGStmt_noRand (bDg : ℕ) : (initCopyGStmt bDg).NoRand := by
  simp [initCopyGStmt, forRange, forUp, Stmt.NoRand]

def initCopyGContract (w vCap0 eCap0 vCap eCap : ℕ) (G₀ : MGraph)
    (eList vList : List ℕ) : Contract where
  pre args mem := ∃ g0Ptr dgGPtr eListPtr vListPtr n0 m0,
    args = [g0Ptr, dgGPtr, eListPtr, vListPtr, vCap, eCap, n0, m0] ∧
    16 ≤ 2 ^ w ∧ G₀.IsValid ∧ G₀.n = n0 ∧ G₀.E.card = m0 ∧
    (∀ v ∈ G₀.V, v < vCap) ∧ (∀ e ∈ G₀.E, e < eCap) ∧
    DynGraphAt mem g0Ptr vCap0 eCap0 G₀ ∧
    g0Ptr + dynGraphSize vCap0 eCap0 < 2 ^ w ∧
    (g0Ptr + dynGraphSize vCap0 eCap0 ≤ dgGPtr ∨ dgGPtr + dynGraphSize vCap eCap ≤ g0Ptr) ∧
    eList.length = m0 ∧ eList.Nodup ∧ (∀ e, e ∈ eList ↔ e ∈ G₀.E) ∧
    ListAt mem eListPtr eList ∧
    eListPtr + m0 < 2 ^ w ∧
    (eListPtr + m0 ≤ dgGPtr ∨ dgGPtr + dynGraphSize vCap eCap ≤ eListPtr) ∧
    vList.length = n0 ∧ vList.Nodup ∧ (∀ v, v ∈ vList ↔ v ∈ G₀.V) ∧
    ListAt mem vListPtr vList ∧
    vListPtr + n0 < 2 ^ w ∧
    (vListPtr + n0 ≤ dgGPtr ∨ dgGPtr + dynGraphSize vCap eCap ≤ vListPtr) ∧
    dgGPtr + dynGraphSize vCap eCap < 2 ^ w ∧
    ∀ i < dynGraphSize vCap eCap, mem (dgGPtr + i) = 0
  post args mem ret mem' := ∃ g0Ptr dgGPtr eListPtr vListPtr n0 m0,
    args = [g0Ptr, dgGPtr, eListPtr, vListPtr, vCap, eCap, n0, m0] ∧ ret = 0 ∧
    DynGraphAt mem' dgGPtr vCap eCap G₀ ∧
    ∀ addr, addr < dgGPtr ∨ dgGPtr + dynGraphSize vCap eCap ≤ addr → mem' addr = mem addr
  cost args _ := 140 * args.getD 6 0 + 600 * args.getD 7 0 + 100

private def addVGraph (vList : List ℕ) (i : ℕ) : MGraph :=
  { V := (vList.take i).toFinset, E := ∅, tail := fun _ => 0, head := fun _ => 0 }

private lemma addVGraph_zero (vList : List ℕ) :
    addVGraph vList 0 = { V := ∅, E := ∅, tail := fun _ => 0, head := fun _ => 0 } := by
  simp [addVGraph]

private lemma addVGraph_succ {vList : List ℕ} {i : ℕ} (hi : i < vList.length) :
    ({ V := insert vList[i] (addVGraph vList i).V, E := (addVGraph vList i).E,
       tail := (addVGraph vList i).tail, head := (addVGraph vList i).head } : MGraph) =
      addVGraph vList (i + 1) := by
  dsimp [addVGraph]
  congr 1
  rw [List.take_succ_eq_append_getElem hi, List.toFinset_append, List.toFinset_cons,
    List.toFinset_nil, insert_empty_eq, Finset.union_comm]
  rfl

private def addEGraph (G₀ : MGraph) (eList : List ℕ) (j : ℕ) : MGraph :=
  { V := G₀.V
    E := (eList.take j).toFinset
    tail := fun e => if e ∈ (eList.take j).toFinset then G₀.tail e else 0
    head := fun e => if e ∈ (eList.take j).toFinset then G₀.head e else 0 }

private lemma addEGraph_succ {G₀ : MGraph} {eList : List ℕ} {j : ℕ} (hj : j < eList.length)
    (heNd : eList.Nodup) :
    let e := eList[j]
    e ∉ (addEGraph G₀ eList j).E ∧
    (addEGraph G₀ eList j).applyUpdate (.insert e (G₀.tail e) (G₀.head e)) =
      addEGraph G₀ eList (j + 1) := by
  intro e
  have hnot : e ∉ (eList.take j).toFinset := by
    rw [List.mem_toFinset]
    intro hmem
    obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_getElem.mp hmem
    have hkj : k < j := by
      have := List.length_take_le j eList
      omega
    have hk_get : (eList.take j)[k] = eList[k] := List.getElem_take
    rw [hk_get] at hk_eq
    have hinj := heNd.getElem_inj_iff.mp hk_eq
    omega
  refine ⟨hnot, ?_⟩
  dsimp only [MGraph.applyUpdate, addEGraph]
  have hEeq : insert e (eList.take j).toFinset = (eList.take (j + 1)).toFinset := by
    rw [List.take_succ_eq_append_getElem hj, List.toFinset_append, List.toFinset_cons,
      List.toFinset_nil, insert_empty_eq, Finset.union_comm]
    rfl
  have hmem1 : e ∈ (eList.take (j + 1)).toFinset := by
    rw [List.mem_toFinset, List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton]
    exact Or.inr rfl
  have hmem2 : ∀ x ≠ e, (x ∈ (eList.take (j + 1)).toFinset ↔ x ∈ (eList.take j).toFinset) := by
    intro x hx
    rw [List.mem_toFinset, List.mem_toFinset, List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton]
    exact ⟨fun h => h.elim id (fun h => absurd h hx), Or.inl⟩
  have htEq : Function.update (fun x => if x ∈ (eList.take j).toFinset then G₀.tail x else 0)
      e (G₀.tail e) =
      (fun x => if x ∈ (eList.take (j + 1)).toFinset then G₀.tail x else 0) := by
    funext x
    by_cases hxe : x = e
    · subst x; rw [Function.update_self, ite_eq_left hmem1]
    · rw [Function.update_of_ne hxe]; simp only [hmem2 x hxe]
  have hhEq : Function.update (fun x => if x ∈ (eList.take j).toFinset then G₀.head x else 0)
      e (G₀.head e) =
      (fun x => if x ∈ (eList.take (j + 1)).toFinset then G₀.head x else 0) := by
    funext x
    by_cases hxe : x = e
    · subst x; rw [Function.update_self, ite_eq_left hmem1]
    · rw [Function.update_of_ne hxe]; simp only [hmem2 x hxe]
  rw [hEeq, htEq, hhEq]

/-- Verified contract for `initCopyGStmt`. -/
theorem initCopyG_meetsContract {w bSelf bDg vCap0 eCap0 vCap eCap : ℕ}
    {G₀ : MGraph} {eList vList : List ℕ} {p : Program}
    (hpSelf : p.procs[bSelf]? = some (initCopyGStmt bDg))
    (hpDg : p.HasAt bDg (dgRelocProcs bDg)) :
    MeetsContract w p bSelf (initCopyGContract w vCap0 eCap0 vCap eCap G₀ eList vList) := by
  have hpOps : p.HasAt bDg dgOpsProcs := dgReloc_hasAt_ops hpDg
  have hpEdge : p.HasAt (bDg + 7) (dgEdgeProcs bDg) := dgReloc_hasAt_edge hpDg
  refine meetsContract_of_runs hpSelf fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨g0Ptr, dgGPtr, eListPtr, vListPtr, n0, m0, rfl, h16, hGval, rfl, rfl,
    hvCap, heCap, hdgG0, hg0Bd, hg0Disj, heLen, heNd, heMem, heAt, heLw_bd, heDisj,
    hvLen, hvNd, hvMem, hvAt, hvLw_bd, hvDisj, hdgBd, hzero⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hg0w : g0Ptr < 2 ^ w := hwords g0Ptr (by simp)
  have hdgw : dgGPtr < 2 ^ w := hwords dgGPtr (by simp)
  have heLw : eListPtr < 2 ^ w := hwords eListPtr (by simp)
  have hvLw : vListPtr < 2 ^ w := hwords vListPtr (by simp)
  have hvCw : vCap < 2 ^ w := hwords vCap (by simp)
  have heCw : eCap < 2 ^ w := hwords eCap (by simp)
  have hn0w : G₀.n < 2 ^ w := hwords G₀.n (by simp)
  have hm0w : G₀.E.card < 2 ^ w := hwords G₀.E.card (by simp)
  let dgSize := dynGraphSize vCap eCap
  have hstep1 : Triple w p (fun st => st = startState
        [g0Ptr, dgGPtr, eListPtr, vListPtr, vCap, eCap, G₀.n, G₀.E.card] mem pos)
      (.call 8 (bDg + dgIdxInitEmpty) [.reg 1, .reg 4, .reg 5])
      (normalPost fun st => st.regs 0 = g0Ptr ∧ st.regs 1 = dgGPtr ∧ st.regs 2 = eListPtr ∧
        st.regs 3 = vListPtr ∧ st.regs 4 = vCap ∧ st.regs 5 = eCap ∧
        st.regs 6 = G₀.n ∧ st.regs 7 = G₀.E.card ∧
        DynGraphAt st.mem dgGPtr vCap eCap (addVGraph vList 0) ∧
        (∀ addr, addr < dgGPtr ∨ dgGPtr + dgSize ≤ addr → st.mem addr = mem addr))
      (fun _ => 50) := by
    intro st ω' hst
    subst hst
    have hpre_e : (dgInitEmptyLocalContract w).pre [dgGPtr, vCap, eCap] mem :=
      ⟨dgGPtr, vCap, eCap, rfl, h16, hdgBd, hzero⟩
    have heval1 : evalArgs w (startState [g0Ptr, dgGPtr, eListPtr, vListPtr, vCap, eCap, G₀.n, G₀.E.card] mem pos)
        [.reg 1, .reg 4, .reg 5] = some [dgGPtr, vCap, eCap] :=
      evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))
    rcases runs_call_of_meetsContract (r := 8) (dgInitEmptyLocal_meetsContract hpOps) heval1
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl <;> first | exact hdgw | exact hvCw | exact heCw)
        hpre_e ω' with ⟨st1, c1, _, hruns1, hpost1, _, hregs1, hcost1⟩
    rcases hpost1 with ⟨g1, v1, e1, hargs1, _, hdg1, hfr1⟩
    simp only [List.cons.injEq, and_true] at hargs1
    rcases hargs1 with ⟨hg1, hv1, he1⟩
    rw [← hg1, ← hv1, ← he1] at hdg1
    rw [← hg1] at hfr1
    rw [addVGraph_zero]
    refine ⟨.normal, st1, c1, hruns1, ?_, ?_⟩
    · refine ⟨by rw [hregs1 0 (by omega)]; rfl, by rw [hregs1 1 (by omega)]; rfl,
        by rw [hregs1 2 (by omega)]; rfl, by rw [hregs1 3 (by omega)]; rfl,
        by rw [hregs1 4 (by omega)]; rfl, by rw [hregs1 5 (by omega)]; rfl,
        by rw [hregs1 6 (by omega)]; rfl, by rw [hregs1 7 (by omega)]; rfl,
        hdg1, fun addr haddr => hfr1 addr (by
          rcases haddr with hlt | hge
          · exact Or.inl hlt
          · exact Or.inr (by dsimp [dgSize, dynGraphSize] at hge; omega))⟩
    · dsimp only [dgInitEmptyLocalContract, argsSize, Expr.size] at hcost1 ⊢
      omega
  let InvV : ℕ → State → Prop := fun i st =>
    st.regs 0 = g0Ptr ∧ st.regs 1 = dgGPtr ∧ st.regs 2 = eListPtr ∧ st.regs 3 = vListPtr ∧
    st.regs 4 = vCap ∧ st.regs 5 = eCap ∧ st.regs 6 = G₀.n ∧ st.regs 7 = G₀.E.card ∧
    st.regs 8 = i ∧
    DynGraphAt st.mem dgGPtr vCap eCap (addVGraph vList i) ∧
    (∀ addr, addr < dgGPtr ∨ dgGPtr + dgSize ≤ addr → st.mem addr = mem addr)
  have hv_init : ∀ st,
      (st.regs 0 = g0Ptr ∧ st.regs 1 = dgGPtr ∧ st.regs 2 = eListPtr ∧ st.regs 3 = vListPtr ∧
        st.regs 4 = vCap ∧ st.regs 5 = eCap ∧ st.regs 6 = G₀.n ∧ st.regs 7 = G₀.E.card ∧
        DynGraphAt st.mem dgGPtr vCap eCap (addVGraph vList 0) ∧
        (∀ addr, addr < dgGPtr ∨ dgGPtr + dgSize ≤ addr → st.mem addr = mem addr)) →
      Expr.eval w st (.const 0) = some 0 ∧
        InvV 0 { mem := st.mem, regs := Function.update st.regs 8 0, pos := st.pos } := by
    intro st ⟨h0, h1, h2, h3, h4, h5, h6, h7, hdg, hfr⟩
    exact ⟨by eval_expr, by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
      by simp [h5], by simp [h6], by simp [h7], by simp, hdg, hfr⟩
  have hv_body : ∀ i, 0 ≤ i → i < G₀.n →
      Triple w p (InvV i)
        (.assign 9 (.load (.bin .add (.reg 3) (.reg 8))) ;;
         .call 10 (bDg + dgIdxAddVertex) [.reg 1, .reg 9])
        (normalPost fun st₁ =>
          InvV (i + 1) { mem := st₁.mem, regs := Function.update st₁.regs 8 (i + 1), pos := st₁.pos } ∧
          st₁.regs 8 = i) (fun _ => 130) := by
    intro i _ hi st ω' hinv
    rcases hinv with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hdg, hfr⟩
    have hi_len : i < vList.length := by omega
    have hvi_bd : vListPtr + i < 2 ^ w := by
      rcases hvDisj with hle | hge <;> omega
    have hmem_vi : st.mem (vListPtr + i) = vList[i] := by
      rw [hfr (vListPtr + i) (by rcases hvDisj with hle | hge <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
      exact hvAt i hi_len
    have hv_in : vList[i] ∈ G₀.V := (hvMem _).mp (List.getElem_mem hi_len)
    have hv_lt : vList[i] < vCap := hvCap _ hv_in
    have hvi_w : vList[i] < 2 ^ w := Nat.lt_trans hv_lt hvCw
    refine runs_start_le ?_
    refine runs_seq_assign_le (by eval_expr) ?_
    have hpre_av : (dgAddVertexContract w vCap eCap (addVGraph vList i)).pre [dgGPtr, vList[i]] st.mem :=
      ⟨dgGPtr, vList[i], rfl, h16, hdgBd, hv_lt, hdg⟩
    have heval_av : evalArgs w { mem := st.mem, regs := Function.update st.regs 9 (st.mem (vListPtr + i)), pos := st.pos }
        [.reg 1, .reg 9] = some [dgGPtr, vList[i]] :=
      evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
    rcases runs_call_of_meetsContract (r := 10) (dgAddVertex_meetsContract (G := addVGraph vList i) hpOps)
        heval_av (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl <;> assumption) hpre_av ω' with
      ⟨stB, cB, _, hrunsB, hpostB, _, hregsB, hcostB⟩
    rcases hpostB with ⟨gB, vB, hargsB, _, hdgB, hfrB⟩
    simp only [List.cons.injEq, and_true] at hargsB
    rcases hargsB with ⟨hgB, hvB⟩
    have hdgB' : DynGraphAt stB.mem dgGPtr vCap eCap (addVGraph vList (i + 1)) := by
      rw [← hgB, ← hvB] at hdgB
      rw [← addVGraph_succ hi_len]
      exact hdgB
    refine ⟨.normal, stB, cB, hrunsB, ⟨⟨by simp [hregsB 0 (by omega), h0],
      by simp [hregsB 1 (by omega), h1], by simp [hregsB 2 (by omega), h2],
      by simp [hregsB 3 (by omega), h3], by simp [hregsB 4 (by omega), h4],
      by simp [hregsB 5 (by omega), h5], by simp [hregsB 6 (by omega), h6],
      by simp [hregsB 7 (by omega), h7], by simp, hdgB', fun addr ha => ?_⟩,
      by simp [hregsB 8 (by omega), h8]⟩, ?_⟩
    · rw [← hgB] at hfrB
      dsimp only [dgSize] at ha
      rw [hfrB addr ha, hfr addr ha]
    · dsimp only [dgAddVertexContract, argsSize, Expr.size] at hcostB ⊢
      omega
  have hstep2 : Triple w p
      (fun st => st.regs 0 = g0Ptr ∧ st.regs 1 = dgGPtr ∧ st.regs 2 = eListPtr ∧
        st.regs 3 = vListPtr ∧ st.regs 4 = vCap ∧ st.regs 5 = eCap ∧
        st.regs 6 = G₀.n ∧ st.regs 7 = G₀.E.card ∧
        DynGraphAt st.mem dgGPtr vCap eCap (addVGraph vList 0) ∧
        (∀ addr, addr < dgGPtr ∨ dgGPtr + dgSize ≤ addr → st.mem addr = mem addr))
      (forRange 8 (.const 0) (.reg 6)
        (.assign 9 (.load (.bin .add (.reg 3) (.reg 8))) ;;
         .call 10 (bDg + dgIdxAddVertex) [.reg 1, .reg 9]))
      (normalPost (InvV G₀.n)) (fun _ => 140 * G₀.n + 10) := by
    have hloop := Triple.forRange_const 130 0 G₀.n (Nat.zero_le G₀.n) hw1 (fun _ => hn0w)
      hv_init (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h := hi.2.2.2.2.2.2.1; eval_expr) hv_body
    exact hloop.mono_cost (fun _ _ => by dsimp only [Expr.size]; omega)
  have haddV_end : addVGraph vList G₀.n = { V := G₀.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 } := by
    dsimp only [addVGraph]
    rw [List.take_of_length_le hvLen.le]
    congr 1; ext x; simp [hvMem]
  let InvE : ℕ → State → Prop := fun j st =>
    st.regs 0 = g0Ptr ∧ st.regs 1 = dgGPtr ∧ st.regs 2 = eListPtr ∧ st.regs 3 = vListPtr ∧
    st.regs 4 = vCap ∧ st.regs 5 = eCap ∧ st.regs 6 = G₀.n ∧ st.regs 7 = G₀.E.card ∧
    st.regs 8 = j ∧
    DynGraphAt st.mem dgGPtr vCap eCap (addEGraph G₀ eList j) ∧
    (∀ addr, addr < dgGPtr ∨ dgGPtr + dgSize ≤ addr → st.mem addr = mem addr)
  have he_init : ∀ st, InvV G₀.n st →
      Expr.eval w st (.const 0) = some 0 ∧
        InvE 0 { mem := st.mem, regs := Function.update st.regs 8 0, pos := st.pos } := by
    intro st ⟨h0, h1, h2, h3, h4, h5, h6, h7, _, hdg, hfr⟩
    have h0eq : addEGraph G₀ eList 0 = { V := G₀.V, E := ∅, tail := fun _ => 0, head := fun _ => 0 } := by
      dsimp only [addEGraph]; simp
    rw [haddV_end, ← h0eq] at hdg
    exact ⟨by eval_expr, by simp [h0], by simp [h1], by simp [h2], by simp [h3], by simp [h4],
      by simp [h5], by simp [h6], by simp [h7], by simp, hdg, hfr⟩
  have he_body : ∀ j, 0 ≤ j → j < G₀.E.card →
      Triple w p (InvE j)
        (.assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ;;
         .call 10 (bDg + dgIdxGetTail) [.reg 0, .reg 9] ;;
         .call 11 (bDg + dgIdxGetHead) [.reg 0, .reg 9] ;;
         .call 12 (bDg + 7 + dgIdxInsertEdge) [.reg 1, .reg 9, .reg 10, .reg 11])
        (normalPost fun st₁ =>
          InvE (j + 1) { mem := st₁.mem, regs := Function.update st₁.regs 8 (j + 1), pos := st₁.pos } ∧
          st₁.regs 8 = j) (fun _ => 570) := by
    intro j _ hj st ω' hinv
    rcases hinv with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hdg, hfr⟩
    have hj_len : j < eList.length := by omega
    have hej_bd : eListPtr + j < 2 ^ w := by
      rcases heDisj with hle | hge <;> omega
    have hmem_ej : st.mem (eListPtr + j) = eList[j] := by
      rw [hfr (eListPtr + j) (by rcases heDisj with hle | hge <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
      exact heAt j hj_len
    let ej := eList[j]
    have hej_in : ej ∈ G₀.E := (heMem _).mp (List.getElem_mem hj_len)
    have hej_lt : ej < eCap := heCap _ hej_in
    have hej_w : ej < 2 ^ w := Nat.lt_trans hej_lt heCw
    have hdg0_st : DynGraphAt st.mem g0Ptr vCap0 eCap0 G₀ :=
      DynGraphAt.of_agree hdgG0 fun addr ha1 ha2 =>
        hfr addr (by rcases hg0Disj with hle | hge <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
    have hu_in : G₀.tail ej ∈ (addEGraph G₀ eList j).V := (hGval ej hej_in).1
    have hv_in : G₀.head ej ∈ (addEGraph G₀ eList j).V := (hGval ej hej_in).2
    have huw : G₀.tail ej < 2 ^ w := Nat.lt_trans (hvCap _ hu_in) hvCw
    have hvw : G₀.head ej < 2 ^ w := Nat.lt_trans (hvCap _ hv_in) hvCw
    refine runs_start_le ?_
    refine runs_seq_assign_le (by eval_expr) ?_
    have hevalT : evalArgs w { mem := st.mem, regs := Function.update st.regs 9 (st.mem (eListPtr + j)), pos := st.pos }
        [.reg 0, .reg 9] = some [g0Ptr, ej] :=
      evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
    refine runs_seq_call_le (dgGetTail_meetsContract hpOps)
        hevalT
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl <;> assumption)
        ⟨g0Ptr, ej, rfl, h16, hg0Bd, hej_in, hdg0_st⟩
        fun retB memB posB hpostB => ?_
    rcases hpostB with ⟨gB, eB, hargsB, hmemB, hretB⟩
    simp only [List.cons.injEq, and_true] at hargsB
    rcases hargsB with ⟨hgB, heB⟩
    rw [← heB] at hretB
    subst hretB
    have hevalH : evalArgs w { mem := memB, regs := Function.update (Function.update st.regs 9 (st.mem (eListPtr + j))) 10 (G₀.tail ej), pos := posB }
        [.reg 0, .reg 9] = some [g0Ptr, ej] :=
      evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))
    refine runs_seq_call_le (dgGetHead_meetsContract hpOps)
        hevalH
        (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl <;> assumption)
        (by rw [hmemB]; exact ⟨g0Ptr, ej, rfl, h16, hg0Bd, hej_in, hdg0_st⟩)
        fun retC memC posC hpostC => ?_
    rcases hpostC with ⟨gC, eC, hargsC, hmemC, hretC⟩
    simp only [List.cons.injEq, and_true] at hargsC
    rcases hargsC with ⟨hgC, heC⟩
    rw [← heC] at hretC
    subst hretC
    have hdgC : DynGraphAt memC dgGPtr vCap eCap (addEGraph G₀ eList j) := by
      rw [hmemC, hmemB]; exact hdg
    let stC : State := { mem := memC, regs := Function.update (Function.update (Function.update st.regs 9 (st.mem (eListPtr + j))) 10 (G₀.tail ej)) 11 (G₀.head ej), pos := posC }
    have hevalC : evalArgs w stC [.reg 1, .reg 9, .reg 10, .reg 11] =
        some [dgGPtr, ej, G₀.tail ej, G₀.head ej] :=
      evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
        (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))
    have hins_pre : (dgInsertEdgeContract w vCap eCap (addEGraph G₀ eList j)).pre
        [dgGPtr, ej, G₀.tail ej, G₀.head ej] memC :=
      ⟨dgGPtr, ej, G₀.tail ej, G₀.head ej, rfl, h16, hdgBd, hu_in, hv_in, hdgC⟩
    rcases runs_call_of_meetsContract (r := 12) (dgInsertEdge_meetsContract hpEdge hpOps)
        hevalC (fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl <;> assumption)
        hins_pre ω' with ⟨stD, cD, _, hrunsD, hpostD, _, hregsD, hcostD⟩
    rcases hpostD with ⟨gD, eD, uD, vD, hargsD, _, hdgD, hfrD⟩
    simp only [List.cons.injEq, and_true] at hargsD
    rcases hargsD with ⟨hgD, heD, huD, hvD⟩
    obtain ⟨hnot_in, happ⟩ := addEGraph_succ hj_len heNd
    have hdgD' : DynGraphAt stD.mem dgGPtr vCap eCap (addEGraph G₀ eList (j + 1)) := by
      rw [← hgD, ← heD, ← huD, ← hvD, ite_eq_left ⟨hej_lt, hnot_in⟩, happ] at hdgD
      exact hdgD
    refine ⟨.normal, stD, cD, hrunsD, ?_, ?_⟩
    · refine ⟨⟨by simp [hregsD 0 (by omega), stC, h0], by simp [hregsD 1 (by omega), stC, h1],
        by simp [hregsD 2 (by omega), stC, h2], by simp [hregsD 3 (by omega), stC, h3],
        by simp [hregsD 4 (by omega), stC, h4], by simp [hregsD 5 (by omega), stC, h5],
        by simp [hregsD 6 (by omega), stC, h6], by simp [hregsD 7 (by omega), stC, h7],
        by simp, hdgD', fun addr ha => ?_⟩,
        by simp [hregsD 8 (by omega), stC, h8]⟩
      rw [← hgD] at hfrD
      dsimp only [dgSize] at ha
      rw [hfrD addr ha]
      dsimp only [stC]
      rw [hmemC, hmemB, hfr addr ha]
    · dsimp only [dgGetTailContract, dgGetHeadContract, dgInsertEdgeContract, argsSize, Expr.size]
        at hcostD ⊢
      omega
  have hstep3 : Triple w p (InvV G₀.n)
      (forRange 8 (.const 0) (.reg 7)
        (.assign 9 (.load (.bin .add (.reg 2) (.reg 8))) ;;
         .call 10 (bDg + dgIdxGetTail) [.reg 0, .reg 9] ;;
         .call 11 (bDg + dgIdxGetHead) [.reg 0, .reg 9] ;;
         .call 12 (bDg + 7 + dgIdxInsertEdge) [.reg 1, .reg 9, .reg 10, .reg 11]))
      (normalPost (InvE G₀.E.card)) (fun _ => 580 * G₀.E.card + 10) := by
    have hloop := Triple.forRange_const 570 0 G₀.E.card (Nat.zero_le G₀.E.card) hw1 (fun _ => hm0w)
      he_init (fun _ _ _ _ hi => hi.2.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h := hi.2.2.2.2.2.2.2.1; eval_expr) he_body
    exact hloop.mono_cost (fun _ _ => by dsimp only [Expr.size]; omega)
  refine runs_start_le ?_
  dsimp only [initCopyGStmt]
  refine runs_seq_triple_le hstep1 rfl fun st1 h1 => ?_
  refine runs_seq_triple_le hstep2 h1 fun st2 h2 => ?_
  refine runs_seq_triple_le hstep3 h2 fun stF hinvF => ?_
  rcases hinvF with ⟨_, _, _, _, _, _, _, _, _, hdgF, hfrF⟩
  have haddE_end : DynGraphAt stF.mem dgGPtr vCap eCap G₀ := by
    refine DynGraphAt.congr_ends (G₁ := addEGraph G₀ eList G₀.E.card) rfl ?_ ?_ hdgF
    · ext x
      simp only [addEGraph, List.take_of_length_le heLen.le, List.mem_toFinset, heMem]
    · intro e he
      simp only [addEGraph, List.mem_toFinset] at he ⊢
      simp [he]
  refine runs_ret_le (by eval_expr)
    ⟨g0Ptr, dgGPtr, eListPtr, vListPtr, G₀.n, G₀.E.card, rfl, rfl, haddE_end, hfrF⟩ ?_
  dsimp only [initCopyGContract, Expr.size, List.getD]
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  omega

