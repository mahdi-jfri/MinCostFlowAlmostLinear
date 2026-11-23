module

public import WordRAM.Contract
public import WordRAM.Logic
public import WordRAM.Tactic
public import MinCostFlow.ExpanderDecomp.PortRounding
public import MinCostFlow.ExpanderDecomp.OuterProgContracts
public import MinCostFlow.ExpanderDecomp.OuterProgSubgraphOps
import Mathlib.Tactic.Linarith

/-!
# Port-Cut Rounding and Edge Contraction Word-RAM Procedures (`OuterProgPortOps`)

Implements and verifies the two port-to-original translation procedures on the
Word-RAM without ever scanning `range n`:

1. `outerContractEdgesProc`: given `ownerAddr` holding `portOwnersList edges` and a port edge list `F`
   of length `mF`, maps each port edge `(p, q)` to `(owner[p], owner[q])` and drops loops
   `owner[p] = owner[q]`, computing `contractEdges G X F` exactly in `O(mF + 1)` steps.
2. `outerRoundPortCutProc`: given a compact vertex list `verts` (`|verts| = k`), port owners of `2e`
   ports at `ownerAddr`, a nodup port cut list `uList` (`|uList| = kU`), reusable zeroed `locAddr`,
   and zero-heap cursor `h`, rounds each cloud to its majority side and splits `verts` into
   `S_list` (`S_list.toFinset = roundPortCut G X U`) and `T_list`
   (`T_list.toFinset = X \ roundPortCut G X U`) in `O(k + e + kU + 1)` steps, restoring `locAddr`
   to all zeros and advancing the zero-heap cursor by `2 * k + 2 * e`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited

/-! ## 1. `outerContractEdgesProc` -/

/-- Contract port edges `F` along `ownerAddr` and drop self-loops, writing the contracted edge list
at `outF'Addr` and returning its length. Args: `[ownerAddr, mF, fAddr, outF'Addr]`. -/
def outerContractEdgesProc : Stmt :=
  .assign 5 (.const 0) ;;
  forRange 4 (.const 0) (.reg 1)
    (.assign 6 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4)))) ;;
     .assign 7 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4))) (.const 1))) ;;
     .assign 8 (.load (.bin .add (.reg 0) (.reg 6))) ;;
     .assign 9 (.load (.bin .add (.reg 0) (.reg 7))) ;;
     .cond (.bin .eq (.reg 8) (.reg 9))
       .nop
       (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 5))) (.reg 8) ;;
        .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 5))) (.const 1)) (.reg 9) ;;
        .assign 5 (.bin .add (.reg 5) (.const 1)))) ;;
  .ret (.reg 5)

/-- Explicit step bound for `outerContractEdgesProc`: `O(mF + 1)`. -/
def outerContractEdgesCost (mF : ℕ) : ℕ :=
  80 * mF + 40

/-- Contract for `outerContractEdgesProc`: writes
`(F.map fun ed => (owners.getD ed.1 0, owners.getD ed.2 0)).filter fun ed => decide (ed.1 ≠ ed.2)`
at `outF'Addr` and returns its length, preserving all memory outside
`[outF'Addr, outF'Addr + 2 * mF)`. -/
def outerContractEdgesContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (ownerAddr mF fAddr outF'Addr numPorts : ℕ) (owners : List ℕ) (F : List (ℕ × ℕ)),
      args = [ownerAddr, mF, fAddr, outF'Addr] ∧
      owners.length = numPorts ∧
      F.length = mF ∧
      (∀ ed ∈ F, ed.1 < numPorts ∧ ed.2 < numPorts) ∧
      ListAt mem ownerAddr owners ∧
      EdgesAt mem fAddr F ∧
      ownerAddr + numPorts < 2 ^ w ∧
      fAddr + 2 * mF < 2 ^ w ∧
      outF'Addr + 2 * mF < 2 ^ w ∧
      16 < 2 ^ w ∧
      DisjointRange outF'Addr (2 * mF) ownerAddr numPorts ∧
      DisjointRange outF'Addr (2 * mF) fAddr (2 * mF)
  post args mem v mem' :=
    let ownerAddr := args.getD 0 0
    let mF := args.getD 1 0
    let fAddr := args.getD 2 0
    let outF'Addr := args.getD 3 0
    let F := readEdges mem fAddr mF
    let contracted := (F.map fun ed => (mem (ownerAddr + ed.1), mem (ownerAddr + ed.2))).filter
      fun ed => decide (ed.1 ≠ ed.2)
    v = contracted.length ∧
    EdgesAt mem' outF'Addr contracted ∧
    (∀ a, a < outF'Addr ∨ outF'Addr + 2 * mF ≤ a → mem' a = mem a)
  cost args _mem :=
    outerContractEdgesCost (args.getD 1 0)

/-! ## 2. `outerRoundPortCutProc` -/

/-- Fill `locAddr[verts[i]] := i + 1` for `i < k`. Uses `r0=k, r1=vertsAddr, r6=locAddr`,
scratch `r11, r12`. -/
def rpcFillLocStmt : Stmt :=
  forRange 11 (.const 0) (.reg 0)
    (.assign 12 (.load (.bin .add (.reg 1) (.reg 11))) ;;
     .store (.bin .add (.reg 6) (.reg 12)) (.bin .add (.reg 11) (.const 1)))

/-- Mark `portInU[u] := 1` for `u` in `uAddr[0 .. kU - 1]`, where `portInU` is at `r15`.
Uses `r4=kU, r5=uAddr, r15=portInUAddr`, scratch `r11, r12`. -/
def rpcMarkUStmt : Stmt :=
  forRange 11 (.const 0) (.reg 4)
    (.assign 12 (.load (.bin .add (.reg 5) (.reg 11))) ;;
     .store (.bin .add (.reg 15) (.reg 12)) (.const 1))

/-- Accumulate cloud sizes `deg[idx]` (at `r13`) and `inU[idx]` (at `r14`) across all `2 * e`
ports using `ownerAddr` (`r3`), `locAddr` (`r6`), and `portInU` (`r15`). -/
def rpcCountPortsStmt : Stmt :=
  .assign 16 (.bin .mul (.const 2) (.reg 2)) ;;
  forRange 11 (.const 0) (.reg 16)
    (.assign 12 (.load (.bin .add (.reg 3) (.reg 11))) ;;
     .assign 17 (.bin .sub (.load (.bin .add (.reg 6) (.reg 12))) (.const 1)) ;;
     .assign 18 (.load (.bin .add (.reg 13) (.reg 17))) ;;
     .store (.bin .add (.reg 13) (.reg 17)) (.bin .add (.reg 18) (.const 1)) ;;
     .assign 19 (.load (.bin .add (.reg 15) (.reg 11))) ;;
     .cond (.bin .lt (.const 0) (.reg 19))
       (.assign 18 (.load (.bin .add (.reg 14) (.reg 17))) ;;
        .store (.bin .add (.reg 14) (.reg 17)) (.bin .add (.reg 18) (.const 1)))
       .nop)

/-- Split `verts` (`r0, r1`) into `outSAddr` (`r7`, count in `r17`) and `outTAddr` (`r8`, count in
`r18`) according to `deg[i] ≤ 2 * inU[i]` (majority in `U`). -/
def rpcSplitVertsStmt : Stmt :=
  .assign 17 (.const 0) ;;
  .assign 18 (.const 0) ;;
  forRange 11 (.const 0) (.reg 0)
    (.assign 12 (.load (.bin .add (.reg 1) (.reg 11))) ;;
     .assign 19 (.load (.bin .add (.reg 13) (.reg 11))) ;;
     .assign 20 (.bin .mul (.const 2) (.load (.bin .add (.reg 14) (.reg 11)))) ;;
     .cond (.bin .lt (.reg 20) (.reg 19))
       (.store (.bin .add (.reg 8) (.reg 18)) (.reg 12) ;;
        .assign 18 (.bin .add (.reg 18) (.const 1)))
       (.store (.bin .add (.reg 7) (.reg 17)) (.reg 12) ;;
        .assign 17 (.bin .add (.reg 17) (.const 1))))

/-- Round a port cut `U` to whole clouds (`roundPortCut`) and split `verts` into `S_list` and
`T_list`. Args: `[k, vertsAddr, e, ownerAddr, kU, uAddr, locAddr, outSAddr, outTAddr, outLenAddr, h]`.
Stores `[|S_list|, |T_list|]` at `outLenAddr`, restores `locAddr` to zeros, and returns the new
zero-heap cursor `h + 2 * k + 2 * e`. -/
def outerRoundPortCutProc : Stmt :=
  .assign 13 (.reg 10) ;;
  .assign 14 (.bin .add (.reg 10) (.reg 0)) ;;
  .assign 15 (.bin .add (.reg 14) (.reg 0)) ;;
  rpcFillLocStmt ;;
  rpcMarkUStmt ;;
  rpcCountPortsStmt ;;
  rpcSplitVertsStmt ;;
  markVertsStmt 0 1 6 11 12 0 ;;
  .store (.reg 9) (.reg 17) ;;
  .store (.bin .add (.reg 9) (.const 1)) (.reg 18) ;;
  .ret (.bin .add (.reg 15) (.bin .mul (.const 2) (.reg 2)))

/-- Heap space used by `outerRoundPortCutProc`: `2 * k + 2 * e` words. -/
def roundPortCutSpace (k e : ℕ) : ℕ :=
  2 * k + 2 * e

/-- Step bound for `outerRoundPortCutProc`: `O(k + e + kU + 1)`. -/
def outerRoundPortCutCost (k e kU : ℕ) : ℕ :=
  140 * k + 200 * e + 40 * kU + 180

/-- Word-size bound for `outerRoundPortCutProc`. -/
def OuterRoundPortCutWordBound (w n k e kU vertsAddr ownerAddr uAddr locAddr outSAddr outTAddr
    outLenAddr h : ℕ) : Prop :=
  vertsAddr + k ≤ h ∧
  ownerAddr + 2 * e ≤ h ∧
  uAddr + kU ≤ h ∧
  locAddr + n ≤ h ∧
  outSAddr + k ≤ h ∧
  outTAddr + k ≤ h ∧
  outLenAddr + 2 ≤ h ∧
  h + roundPortCutSpace k e < 2 ^ w ∧
  4 * e + 16 < 2 ^ w ∧
  k + 16 < 2 ^ w

/-- Disjointness of mutable buffers below `h` for `outerRoundPortCutProc`. -/
def OuterRoundPortCutDisjoint (n k e kU vertsAddr ownerAddr uAddr locAddr outSAddr outTAddr
    outLenAddr : ℕ) : Prop :=
  DisjointRange locAddr n vertsAddr k ∧
  DisjointRange locAddr n ownerAddr (2 * e) ∧
  DisjointRange locAddr n uAddr kU ∧
  DisjointRange locAddr n outSAddr k ∧
  DisjointRange locAddr n outTAddr k ∧
  DisjointRange locAddr n outLenAddr 2 ∧
  DisjointRange outSAddr k vertsAddr k ∧
  DisjointRange outSAddr k ownerAddr (2 * e) ∧
  DisjointRange outSAddr k uAddr kU ∧
  DisjointRange outSAddr k outTAddr k ∧
  DisjointRange outSAddr k outLenAddr 2 ∧
  DisjointRange outTAddr k vertsAddr k ∧
  DisjointRange outTAddr k ownerAddr (2 * e) ∧
  DisjointRange outTAddr k uAddr kU ∧
  DisjointRange outTAddr k outLenAddr 2 ∧
  DisjointRange outLenAddr 2 vertsAddr k ∧
  DisjointRange outLenAddr 2 ownerAddr (2 * e) ∧
  DisjointRange outLenAddr 2 uAddr kU

/-- Count of ports in `[0, m)` owned by `v` (helper matching `cloudOf`). -/
def portCountPrefix (owners : List ℕ) (m v : ℕ) : ℕ :=
  ((Finset.range m).filter fun p => owners.getD p 0 = v).card

/-- Count of ports in `[0, m) ∩ U` owned by `v` (helper matching `U ∩ cloudOf`). -/
def portInUCountPrefix (owners : List ℕ) (U : Finset ℕ) (m v : ℕ) : ℕ :=
  ((Finset.range m).filter fun p => owners.getD p 0 = v ∧ p ∈ U).card

/-- Contract for `outerRoundPortCutProc`: partitions `verts` into `S_list` and `T_list` according to
whether at least half of each vertex's ports belong to `U = uList.toFinset`, writes `[|S|, |T|]` at
`outLenAddr`, restores `locAddr` to zeros, returns `h' = h + 2 * k + 2 * e` with `ZeroFrom mem' h'`,
and preserves all memory below `h` outside `outSAddr`, `outTAddr`, and `outLenAddr`. -/
def outerRoundPortCutContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ (n k vertsAddr e ownerAddr kU uAddr locAddr outSAddr outTAddr outLenAddr h : ℕ)
      (verts owners uList : List ℕ),
      args = [k, vertsAddr, e, ownerAddr, kU, uAddr, locAddr, outSAddr, outTAddr, outLenAddr, h] ∧
      verts.length = k ∧ verts.Nodup ∧ (∀ v ∈ verts, v < n) ∧
      owners.length = 2 * e ∧ (∀ v ∈ owners, v ∈ verts.toFinset) ∧
      uList.length = kU ∧ uList.Nodup ∧ (∀ p ∈ uList, p < 2 * e) ∧
      ListAt mem vertsAddr verts ∧
      ListAt mem ownerAddr owners ∧
      ListAt mem uAddr uList ∧
      (∀ u < n, mem (locAddr + u) = 0) ∧
      ZeroFrom mem h ∧
      OuterRoundPortCutWordBound w n k e kU vertsAddr ownerAddr uAddr locAddr outSAddr outTAddr
        outLenAddr h ∧
      OuterRoundPortCutDisjoint n k e kU vertsAddr ownerAddr uAddr locAddr outSAddr outTAddr outLenAddr
  post args mem v mem' :=
    let k := args.getD 0 0
    let vertsAddr := args.getD 1 0
    let e := args.getD 2 0
    let ownerAddr := args.getD 3 0
    let kU := args.getD 4 0
    let uAddr := args.getD 5 0
    let outSAddr := args.getD 7 0
    let outTAddr := args.getD 8 0
    let outLenAddr := args.getD 9 0
    let h := args.getD 10 0
    let verts := readList mem vertsAddr k
    let owners := readList mem ownerAddr (2 * e)
    let U := (readList mem uAddr kU).toFinset
    let inS : ℕ → Bool := fun x =>
      decide (portCountPrefix owners (2 * e) x ≤ 2 * portInUCountPrefix owners U (2 * e) x)
    let sList := verts.filter inS
    let tList := verts.filter fun x => !inS x
    v = h + roundPortCutSpace k e ∧
    ZeroFrom mem' v ∧
    ListAt mem' outSAddr sList ∧
    ListAt mem' outTAddr tList ∧
    mem' outLenAddr = sList.length ∧
    mem' (outLenAddr + 1) = tList.length ∧
    (∀ a < h,
      (a < outSAddr ∨ outSAddr + k ≤ a) →
      (a < outTAddr ∨ outTAddr + k ≤ a) →
      (a < outLenAddr ∨ outLenAddr + 2 ≤ a) →
      mem' a = mem a)
  cost args _mem :=
    outerRoundPortCutCost (args.getD 0 0) (args.getD 2 0) (args.getD 4 0)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited

lemma outerContractEdgesProc_noRand : outerContractEdgesProc.NoRand := by
  simp [outerContractEdgesProc, forRange, forUp, Stmt.NoRand]

lemma outerRoundPortCutProc_noRand : outerRoundPortCutProc.NoRand := by
  simp [outerRoundPortCutProc, rpcFillLocStmt, rpcMarkUStmt, rpcCountPortsStmt, rpcSplitVertsStmt,
    markVertsStmt_noRand, forRange, forUp, Stmt.NoRand]

/-! ## 3. Bridge Lemmas to `contractEdges` and `roundPortCut` -/

/-- When `ownerAddr` holds `portOwnersList (G.inside X)` and all port endpoints of `F` are below
`2 * (G.inside X).length`, the output of `outerContractEdgesProc` equals `contractEdges G X F`. -/
lemma contractEdges_eq_of_owners {mem : ℕ → ℕ} {ownerAddr : ℕ} {G : Graph} {X : Finset ℕ}
    {edges F : List (ℕ × ℕ)} (hin : G.inside X = edges)
    (hown : ListAt mem ownerAddr (portOwnersList edges))
    (hF : ∀ ed ∈ F, ed.1 < 2 * edges.length ∧ ed.2 < 2 * edges.length) :
    (F.map fun ed => (mem (ownerAddr + ed.1), mem (ownerAddr + ed.2))).filter
      (fun ed => decide (ed.1 ≠ ed.2)) = contractEdges G X F := by
  unfold contractEdges
  congr 1
  apply List.map_congr_left
  intro ed hed
  have h1 := (hF ed hed).1
  have h2 := (hF ed hed).2
  have hlen : (portOwnersList edges).length = 2 * edges.length := portOwnersList_length edges
  have hm1 : mem (ownerAddr + ed.1) = portOwner G X ed.1 := by
    rw [hown ed.1 (by omega), ← portOwnersList_getD_eq_portOwner hin h1]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : ed.1 < (portOwnersList edges).length)]
  have hm2 : mem (ownerAddr + ed.2) = portOwner G X ed.2 := by
    rw [hown ed.2 (by omega), ← portOwnersList_getD_eq_portOwner hin h2]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : ed.2 < (portOwnersList edges).length)]
  rw [hm1, hm2]

/-- The majority predicate of `outerRoundPortCutProc` coincides with membership in `roundPortCut G X U`
whenever `owners = portOwnersList (G.inside X)`. -/
lemma portCountPrefix_iff_mem_roundPortCut {G : Graph} {X U : Finset ℕ} {edges : List (ℕ × ℕ)}
    (hin : G.inside X = edges) {x : ℕ} (hx : x ∈ X) :
    (portCountPrefix (portOwnersList edges) (2 * edges.length) x ≤
        2 * portInUCountPrefix (portOwnersList edges) U (2 * edges.length) x) ↔
      x ∈ roundPortCut G X U := by
  have hcl : (Finset.range (2 * edges.length)).filter
      (fun p => (portOwnersList edges).getD p 0 = x) = cloudOf G X x := by
    ext p
    simp only [cloudOf, Finset.mem_filter, Finset.mem_range, hin]
    constructor
    · rintro ⟨hp, heq⟩; exact ⟨hp, by rwa [← portOwnersList_getD_eq_portOwner hin hp]⟩
    · rintro ⟨hp, heq⟩; exact ⟨hp, by rwa [portOwnersList_getD_eq_portOwner hin hp]⟩
  have hinU : (Finset.range (2 * edges.length)).filter
      (fun p => (portOwnersList edges).getD p 0 = x ∧ p ∈ U) = U ∩ cloudOf G X x := by
    ext p
    simp only [cloudOf, Finset.mem_inter, Finset.mem_filter, Finset.mem_range, hin]
    constructor
    · rintro ⟨hp, heq, hpU⟩; exact ⟨hpU, hp, by rwa [← portOwnersList_getD_eq_portOwner hin hp]⟩
    · rintro ⟨hpU, hp, heq⟩; exact ⟨hp, by rwa [portOwnersList_getD_eq_portOwner hin hp], hpU⟩
  have hsum : (cloudOf G X x \ U).card + (U ∩ cloudOf G X x).card = (cloudOf G X x).card := by
    rw [Finset.inter_comm]
    exact Finset.card_sdiff_add_card_inter (cloudOf G X x) U
  unfold portCountPrefix portInUCountPrefix roundPortCut
  rw [hcl, hinU, Finset.mem_filter]
  simp only [hx, true_and]
  omega

/-! ## 4. Verification of `outerContractEdgesProc` -/

private lemma disjointRange_ne' {a la b lb x y : ℕ} (hd : DisjointRange a la b lb)
    (hx1 : a ≤ x) (hx2 : x < a + la) (hy1 : b ≤ y) (hy2 : y < b + lb) : x ≠ y := by
  rcases hd with h | h <;> omega

/-- Specification of `outerContractEdgesProc`. -/
theorem outerContractEdgesProc_spec {w : ℕ} {pProg : Program} {b : ℕ}
    (hp : pProg.HasAt b [outerContractEdgesProc]) :
    MeetsContract w pProg b (outerContractEdgesContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨ownerAddr, mF, fAddr, outF'Addr, numPorts, owners, F, rfl, hlenO, hlenF, hFlt,
    hlistO, hedgesF, hwO, hwF, hwOut, hw16, hdOutO, hdOutF⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  set mapF : List (ℕ × ℕ) → List (ℕ × ℕ) := fun xs =>
    (xs.map fun ed => (mem (ownerAddr + ed.1), mem (ownerAddr + ed.2))).filter
      fun ed => decide (ed.1 ≠ ed.2)
  refine runs_start_le ?_
  dsimp only [outerContractEdgesProc]
  refine runs_seq_assign_le (v := 0) (by simp [Expr.eval, (by omega : 0 < 2 ^ w)]) ?_
  let st1 : State := { startState [ownerAddr, mF, fAddr, outF'Addr] mem pos with
    regs := Function.update (startState [ownerAddr, mF, fAddr, outF'Addr] mem pos).regs 5 0 }
  have hloop := Triple.forRange_const (p := pProg) (r := 4) (lo := .const 0) (hi := .reg 1)
    (body :=
      .assign 6 (.load (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4)))) ;;
      .assign 7 (.load (.bin .add (.bin .add (.reg 2) (.bin .mul (.const 2) (.reg 4))) (.const 1))) ;;
      .assign 8 (.load (.bin .add (.reg 0) (.reg 6))) ;;
      .assign 9 (.load (.bin .add (.reg 0) (.reg 7))) ;;
      .cond (.bin .eq (.reg 8) (.reg 9))
        .nop
        (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 5))) (.reg 8) ;;
         .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 5))) (.const 1)) (.reg 9) ;;
         .assign 5 (.bin .add (.reg 5) (.const 1))))
    (P := fun s => s = st1)
    (Inv := fun i s =>
      let res := mapF (F.take i)
      s.regs 4 = i ∧
      s.regs 0 = ownerAddr ∧ s.regs 1 = mF ∧ s.regs 2 = fAddr ∧ s.regs 3 = outF'Addr ∧
      s.regs 5 = res.length ∧
      EdgesAt s.mem outF'Addr res ∧
      (∀ a, a < outF'Addr ∨ outF'Addr + 2 * res.length ≤ a → s.mem a = mem a))
    65 0 mF (Nat.zero_le mF) hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, (by omega : 0 < 2 ^ w)], by simp,
        by simp [st1, startState], by simp [st1, startState], by simp [st1, startState],
        by simp [st1, startState], by simp [st1, mapF], fun j hj => by simp [mapF] at hj,
        fun _ _ => rfl⟩)
    (fun _ s _ _ hi => hi.1)
    (fun _ s _ _ hi => by simp [Expr.eval, hi.2.2.1])
    (fun i _ hilt => by
      intro s ω ⟨hiReg, hr0, hr1, hr2, hr3, hr5, hedOut, hfr⟩
      have hiLen : i < F.length := by omega
      set ed := F[i]'hiLen
      have hedP := hFlt ed (List.getElem_mem hiLen)
      have hres_le : (mapF (F.take i)).length ≤ i := by
        have h1 : (mapF (F.take i)).length ≤ ((F.take i).map fun x => (mem (ownerAddr + x.1), mem (ownerAddr + x.2))).length :=
          List.length_filter_le _ _
        rw [List.length_map, List.length_take, Nat.min_eq_left (by omega)] at h1; exact h1
      have hmem_e1 : s.mem (fAddr + 2 * i) = ed.1 := by
        rw [hfr (fAddr + 2 * i) (Or.elim hdOutF (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact (hedgesF i hiLen).1
      have hmem_e2 : s.mem (fAddr + 2 * i + 1) = ed.2 := by
        rw [hfr (fAddr + 2 * i + 1) (Or.elim hdOutF (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))]
        exact (hedgesF i hiLen).2
      have hmem_o1 : s.mem (ownerAddr + ed.1) = mem (ownerAddr + ed.1) :=
        hfr (ownerAddr + ed.1) (Or.elim hdOutO (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
      have hmem_o2 : s.mem (ownerAddr + ed.2) = mem (ownerAddr + ed.2) :=
        hfr (ownerAddr + ed.2) (Or.elim hdOutO (fun h => Or.inr (by omega)) (fun h => Or.inl (by omega)))
      set u := mem (ownerAddr + ed.1)
      set v := mem (ownerAddr + ed.2)
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := ed.1)
        (by simp [Expr.eval, BinOp.eval, hr2, hiReg, hw2, (by omega : 2 * i < 2 ^ w),
              (by omega : fAddr + 2 * i < 2 ^ w), hmem_e1]) ?_
      refine runs_seq_assign_le (v := ed.2)
        (by simp [Expr.eval, BinOp.eval, hr2, hiReg, hw1, hw2, (by omega : 2 * i < 2 ^ w),
              (by omega : fAddr + 2 * i < 2 ^ w), (by omega : fAddr + 2 * i + 1 < 2 ^ w), hmem_e2]) ?_
      refine runs_seq_assign_le (v := u)
        (by simp [Expr.eval, BinOp.eval, hr0, (by omega : ownerAddr + ed.1 < 2 ^ w), hmem_o1, u]) ?_
      refine runs_seq_assign_le (v := v)
        (by simp [Expr.eval, BinOp.eval, hr0, (by omega : ownerAddr + ed.2 < 2 ^ w), hmem_o2, v]) ?_
      let stA : State := { s with regs :=
        (Function.update (Function.update (Function.update (Function.update s.regs 6 ed.1) 7 ed.2) 8 u) 9 v) }
      have hA_r : ∀ r ≤ 5, stA.regs r = s.regs r := fun r hr => by
        simp [stA, Function.update_of_ne (by omega : r ≠ 9), Function.update_of_ne (by omega : r ≠ 8),
          Function.update_of_ne (by omega : r ≠ 7), Function.update_of_ne (by omega : r ≠ 6)]
      have hA_8 : stA.regs 8 = u := by simp [stA]
      have hA_9 : stA.regs 9 = v := by simp [stA]
      by_cases huv : u = v
      · have htake_eq : mapF (F.take (i + 1)) = mapF (F.take i) := by
          unfold mapF
          rw [List.take_succ_eq_append_getElem hiLen, List.map_append, List.filter_append]
          simp [ed, u, v, huv]
        refine ⟨.normal, stA, 5, runs_cond_iff.mpr ⟨1, 1,
            by simp [Expr.eval, BinOp.eval, hA_8, hA_9, huv, hw1],
            by simp only [one_ne_zero, ↓reduceIte]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, by simp [hA_r 0 (by omega), hr0], by simp [hA_r 1 (by omega), hr1],
          by simp [hA_r 2 (by omega), hr2], by simp [hA_r 3 (by omega), hr3],
          by rw [htake_eq]; simp [hA_r 5 (by omega), hr5],
          by rw [htake_eq]; exact hedOut, by rw [htake_eq]; exact hfr⟩,
          by rw [hA_r 4 (by omega), hiReg]⟩
      · let cnt := (mapF (F.take i)).length
        have htake_eq : mapF (F.take (i + 1)) = mapF (F.take i) ++ [(u, v)] := by
          unfold mapF
          rw [List.take_succ_eq_append_getElem hiLen, List.map_append, List.filter_append]
          simp [ed, u, v, huv]
        let mem1 := Function.update s.mem (outF'Addr + 2 * cnt) u
        let mem2 := Function.update mem1 (outF'Addr + 2 * cnt + 1) v
        let stB1 : State := { stA with mem := mem1 }
        let stB2 : State := { stB1 with mem := mem2 }
        let stC : State := { stB2 with regs := Function.update stB2.regs 5 (cnt + 1) }
        have hs1 : Runs w pProg ω (.store (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 5))) (.reg 8))
            stA .normal stB1 7 := by
          rw [runs_store_iff]
          exact ⟨outF'Addr + 2 * cnt, u,
            by simp [Expr.eval, BinOp.eval, hA_r 3 (by omega), hr3, hA_r 5 (by omega), hr5, hw2, cnt,
                 (by omega : 2 * cnt < 2 ^ w), (by omega : outF'Addr + 2 * cnt < 2 ^ w)],
            by simp [Expr.eval, hA_8], rfl, rfl, by simp [Expr.size]⟩
        have hs2 : Runs w pProg ω (.store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 2) (.reg 5))) (.const 1)) (.reg 9))
            stB1 .normal stB2 9 := by
          rw [runs_store_iff]
          exact ⟨outF'Addr + 2 * cnt + 1, v,
            by simp [Expr.eval, BinOp.eval, stB1, hA_r 3 (by omega), hr3, hA_r 5 (by omega), hr5,
                 hw1, hw2, cnt, (by omega : 2 * cnt < 2 ^ w), (by omega : outF'Addr + 2 * cnt < 2 ^ w),
                 (by omega : outF'Addr + 2 * cnt + 1 < 2 ^ w)],
            by simp [Expr.eval, stB1, hA_9], rfl, rfl, by simp [Expr.size]⟩
        have hs3 : Runs w pProg ω (.assign 5 (.bin .add (.reg 5) (.const 1))) stB2 .normal stC 4 := by
          rw [runs_assign_iff]
          exact ⟨cnt + 1,
            by simp [Expr.eval, BinOp.eval, stB2, stB1, hA_r 5 (by omega), hr5, hw1, cnt,
                 (by omega : cnt + 1 < 2 ^ w)],
            rfl, rfl, by simp [Expr.size]⟩
        refine ⟨.normal, stC, 26, runs_cond_iff.mpr ⟨0, 22,
            by simp [Expr.eval, BinOp.eval, hA_8, hA_9, huv],
            by simp only [↓reduceIte]
               exact runs_seq_iff.mpr (Or.inr ⟨stB1, 7, 14, hs1, runs_seq_iff.mpr (Or.inr ⟨stB2, 9, 4, hs2, hs3, rfl⟩), rfl⟩),
            by simp [Expr.size]⟩, ?_, by simp [Expr.size]⟩
        refine ⟨⟨by simp, by simp [stC, stB2, stB1, hA_r 0 (by omega), hr0],
          by simp [stC, stB2, stB1, hA_r 1 (by omega), hr1],
          by simp [stC, stB2, stB1, hA_r 2 (by omega), hr2],
          by simp [stC, stB2, stB1, hA_r 3 (by omega), hr3],
          by simp [stC, htake_eq, cnt], ?_, ?_⟩,
          by simp [stC, stB2, stB1, hA_r 4 (by omega), hiReg]⟩
        · rw [htake_eq]
          intro j hj
          rw [List.length_append, List.length_singleton] at hj
          dsimp only [stC, stB2, stB1, mem2, mem1]
          by_cases hlt : j < cnt
          · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            simpa [List.getElem_append_left hlt] using hedOut j hlt
          · have hjeq : j = cnt := by omega
            subst hjeq
            refine ⟨?_, ?_⟩
            · rw [Function.update_of_ne (by omega : outF'Addr + 2 * cnt ≠ outF'Addr + 2 * cnt + 1),
                Function.update_self]
              simp [List.getElem_append_right (le_refl cnt), cnt]
            · rw [Function.update_self]
              simp [List.getElem_append_right (le_refl cnt), cnt]
        · intro a ha
          rw [htake_eq, List.length_append, List.length_singleton] at ha
          dsimp only [stC, stB2, stB1, mem2, mem1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr a (by omega))
  refine runs_seq_triple_le hloop rfl ?_
  intro st2 ⟨_, _, _, _, _, h2_5, h2_edOut, h2_fr⟩
  have htakeF : F.take mF = F := by rw [← hlenF, List.take_length]
  rw [htakeF] at h2_5 h2_edOut h2_fr
  refine runs_ret_le (v := (mapF F).length) (by simp [Expr.eval, h2_5]) ?_ ?_
  · dsimp only [outerContractEdgesContract, Outcome.value, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    have hreadF : readEdges mem fAddr mF = F := by rw [← hlenF]; exact readEdges_eq_of_edgesAt hedgesF
    rw [hreadF]
    have hle : (mapF F).length ≤ mF := by
      have h1 : (mapF F).length ≤ (F.map fun x => (mem (ownerAddr + x.1), mem (ownerAddr + x.2))).length :=
        List.length_filter_le _ _
      rw [List.length_map, hlenF] at h1; exact h1
    exact ⟨rfl, h2_edOut, fun a ha => h2_fr a (by omega)⟩
  · simp only [outerContractEdgesContract, outerContractEdgesCost, Expr.size, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    omega


end MinCostFlow.ExpanderDecomp
