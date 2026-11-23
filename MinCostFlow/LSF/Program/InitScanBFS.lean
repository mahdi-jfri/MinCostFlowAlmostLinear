module

public import MinCostFlow.LSF.Program.SharedProcs
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Connected-Component BFS Core (`InitScanBFS`) for LSF Initialization

Implements `initScanStmt` (copying `G₀`'s vertex list, populating `vIdx`/`origVert`/`isOrigVert`,
and running BFS over `DynGraphAt G₀` to record component representatives `C_reps` starting with
`r₀`) and proves the inner half-edge traversal (`walkInc_runs`) and single-component BFS
(`bfsComp_runs`) lemmas needed by `MinCostFlow.LSF.Program.InitScan`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Procedure Definition and Contract -/

/-- Step for one endpoint `uEndExpr` inside BFS edge traversal (`initScanStmt`). -/
def initScanCheckNbrStmt (uEndExpr : Expr) : Stmt :=
  .assign 32 uEndExpr ;;
  .cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 32))) (.const 0))
    (.store (.bin .add (.reg 14) (.reg 32)) (.const 1) ;;
     .store (.bin .add (.reg 12) (.reg 26)) (.reg 32) ;;
     .assign 26 (.bin .add (.reg 26) (.const 1)))
    .nop

def initScanWalkIncBodyStmt : Stmt :=
  .assign 30 (.bin .sub (.reg 29) (.const 1)) ;;
  .assign 31 (.bin .div (.reg 30) (.const 2)) ;;
  .assign 29 (.load (.bin .add (.reg 21) (.reg 30))) ;;
  initScanCheckNbrStmt
    (.load (.bin .add (.reg 17) (.load (.bin .add (.reg 19) (.reg 31))))) ;;
  initScanCheckNbrStmt
    (.load (.bin .add (.reg 17) (.load (.bin .add (.reg 20) (.reg 31)))))

/-- Inner BFS loop exploring one connected component from pushed vertex in `qBufA[0]`. -/
def initScanBfsCompStmt : Stmt :=
  .loop (.bin .lt (.reg 25) (.reg 26))
    (.assign 27 (.load (.bin .add (.reg 12) (.reg 25))) ;;
     .assign 25 (.bin .add (.reg 25) (.const 1)) ;;
     .assign 28 (.load (.bin .add (.reg 16) (.reg 27))) ;;
     .assign 29 (.load (.bin .add (.reg 18) (.reg 28))) ;;
     .loop (.reg 29) initScanWalkIncBodyStmt)

/-- Extract `vList`, `vIdx`, `origVert`, `isOrigVert`, and BFS component reps `C_reps`.
Args: `[g0Ptr, vCap, auxPtr, logCap]`. -/
def initScanStmt : Stmt :=
  .assign 4 (.load (.reg 0)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const dgECapOff))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const dgNOff))) ;;
  .assign 7 (.bin .add (.reg 2) (.const auxHdrSize)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 1)) ;;
  .assign 9 (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 4) (.reg 6)))
    (.bin .mul (.const 2) (.bin .mul (.reg 6) (.reg 3)))) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 6)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 1)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 1)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 1)) ;;
  .assign 14 (.bin .add (.reg 13) (.bin .mul (.const 2) (.reg 1))) ;;
  .assign 15 (.bin .add (.bin .add (.reg 0) (.const 4)) (.reg 4)) ;;
  .assign 16 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 3) (.reg 4))) ;;
  .assign 17 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 4) (.reg 4))) ;;
  .assign 18 (.bin .add (.bin .add (.reg 0) (.const 4)) (.bin .mul (.const 6) (.reg 4))) ;;
  .assign 19 (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .add (.bin .mul (.const 7) (.reg 4)) (.bin .mul (.const 3) (.reg 5)))) ;;
  .assign 20 (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .add (.bin .mul (.const 7) (.reg 4)) (.bin .mul (.const 4) (.reg 5)))) ;;
  .assign 21 (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .add (.bin .mul (.const 7) (.reg 4)) (.bin .mul (.const 7) (.reg 5)))) ;;
  forRange 22 (.const 0) (.reg 6)
    (.assign 24 (.load (.bin .add (.reg 15) (.reg 22))) ;;
     .store (.bin .add (.reg 8) (.reg 22)) (.reg 24) ;;
     .store (.bin .add (.reg 7) (.reg 24)) (.bin .add (.reg 22) (.const 1)) ;;
     .store (.bin .add (.reg 10) (.reg 24)) (.reg 24) ;;
     .store (.bin .add (.reg 11) (.reg 24)) (.const 1)) ;;
  .assign 23 (.const 0) ;;
  forRange 22 (.const 0) (.reg 6)
    (.assign 24 (.load (.bin .add (.reg 8) (.reg 22))) ;;
     .cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 24))) (.const 0))
       (.store (.bin .add (.reg 13) (.reg 23)) (.reg 24) ;;
        .assign 23 (.bin .add (.reg 23) (.const 1)) ;;
        .store (.bin .add (.reg 14) (.reg 24)) (.const 1) ;;
        .store (.reg 12) (.reg 24) ;;
        .assign 25 (.const 0) ;;
        .assign 26 (.const 1) ;;
        initScanBfsCompStmt)
       .nop) ;;
  forRange 22 (.const 0) (.reg 6)
    (.assign 24 (.load (.bin .add (.reg 8) (.reg 22))) ;;
     .store (.bin .add (.reg 14) (.reg 24)) (.const 0)) ;;
  .ret (.reg 23)

lemma initScanStmt_noRand : initScanStmt.NoRand := by
  simp [initScanStmt, initScanBfsCompStmt, initScanWalkIncBodyStmt, initScanCheckNbrStmt,
    forRange, forUp, Stmt.NoRand]

def initScanContract (w : ℕ) (G₀ : MGraph) : Contract where
  pre args mem := ∃ (g0Ptr vCap auxPtr logCap vCap0 eCap0 : ℕ),
    args = [g0Ptr, vCap, auxPtr, logCap] ∧
    16 ≤ 2 ^ w ∧
    1 ≤ G₀.n ∧ G₀.V.Nonempty ∧
    vCap0 ≤ vCap ∧ logCap = auxLogCap G₀.n ∧
    g0Ptr + dynGraphSize vCap0 eCap0 ≤ auxPtr ∧
    auxPtr + auxSize vCap G₀.n < 2 ^ w ∧
    DynGraphAt mem g0Ptr vCap0 eCap0 G₀ ∧
    (∀ v < vCap, mem (auxVIdxBase auxPtr + v) = 0) ∧
    (∀ v < vCap, mem (auxIsOrigVertBase auxPtr vCap G₀.n + v) = 0) ∧
    (∀ v < vCap, mem (auxVisABase auxPtr vCap G₀.n + v) = 0 ∧
      mem (auxVisBBase auxPtr vCap G₀.n + v) = 0)
  post args mem ret mem' := ∃ (g0Ptr vCap auxPtr logCap vCap0 eCap0 : ℕ)
    (vList repList : List ℕ),
    args = [g0Ptr, vCap, auxPtr, logCap] ∧
    DynGraphAt mem g0Ptr vCap0 eCap0 G₀ ∧
    vList.length = G₀.n ∧ vList.Nodup ∧ (∀ v, v ∈ vList ↔ v ∈ G₀.V) ∧
    ListAt mem' (auxVListBase auxPtr vCap) vList ∧
    (∀ i (hi : i < vList.length), mem' (auxVIdxBase auxPtr + vList[i]) = i + 1) ∧
    (∀ v < vCap, v ∉ G₀.V → mem' (auxVIdxBase auxPtr + v) = 0) ∧
    (∀ v < vCap, mem' (auxIsOrigVertBase auxPtr vCap G₀.n + v) = if v ∈ G₀.V then 1 else 0) ∧
    (∀ w' ∈ G₀.V, w' < vCap → mem' (auxOrigVertBase auxPtr vCap G₀.n + w') = w') ∧
    (∀ v < vCap, mem' (auxVisABase auxPtr vCap G₀.n + v) = 0 ∧
      mem' (auxVisBBase auxPtr vCap G₀.n + v) = 0) ∧
    1 ≤ ret ∧ ret ≤ G₀.n ∧ repList.length = ret ∧ repList.Nodup ∧
    repList.getD 0 0 = vList.getD 0 0 ∧
    ListAt mem' (auxQBufBBase auxPtr vCap G₀.n) repList ∧
    IsCompReps G₀ (vList.getD 0 0) repList.toFinset ∧
    (∀ a, a < auxPtr ∨ auxPtr + auxSize vCap G₀.n ≤ a → mem' a = mem a)
  cost args mem :=
    let g0Ptr := args.getD 0 0
    500 * mem (g0Ptr + dgNOff) + 320 * mem (g0Ptr + dgMOff) + 250

/-! ## Graph & Memory Helpers -/

lemma sum_incL_le_two_mul_m {mem : ℕ → ℕ} {g0Ptr vCap0 eCap0 : ℕ} {G₀ : MGraph}
    (hdg : DynGraphAt mem g0Ptr vCap0 eCap0 G₀)
    {incL : ℕ → List ℕ}
    (hinc : ∀ s < vCap0,
      IsDoublyLinkedList mem (dgHePrevBase g0Ptr vCap0 eCap0)
        (dgHeNextBase g0Ptr vCap0 eCap0) (dgIncHeadBase g0Ptr vCap0 + s) (2 * eCap0) (incL s) ∧
      mem (dgSlotDegBase g0Ptr vCap0 + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCap0 ∧ h / 2 ∈ G₀.E ∧
        (if h % 2 = 0 then mem (dgETailSlotBase g0Ptr vCap0 eCap0 + h / 2)
         else mem (dgEHeadSlotBase g0Ptr vCap0 eCap0 + h / 2)) = s) :
    ∑ x ∈ G₀.V, (incL (mem (dgExtToIntBase g0Ptr vCap0 + x))).length ≤ 2 * G₀.m := by
  rcases hdg with ⟨hG₀, hvlt, _, _, _, _, _, _, _, hext, _, _, _, _, _⟩
  let slotOf := fun x => mem (dgExtToIntBase g0Ptr vCap0 + x)
  have hslot_inj : ∀ x ∈ G₀.V, ∀ y ∈ G₀.V, slotOf x = slotOf y → x = y := fun x hx y hy heq => by
    have h1 := (hext x hx).2
    have h2 := (hext y hy).2
    dsimp only [slotOf] at heq
    rw [heq] at h1
    rw [← h1, h2]
  have hdisj : (G₀.V : Set ℕ).PairwiseDisjoint (fun x => (incL (slotOf x)).toFinset) := by
    intro x hx y hy hxy
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro h hhx hhy
    have hxs : slotOf x < vCap0 := hvlt _ (hext x hx).1
    have hys : slotOf y < vCap0 := hvlt _ (hext y hy).1
    have hxEq := ((hinc _ hxs).2.2 h).mp (List.mem_toFinset.mp hhx)
    have hyEq := ((hinc _ hys).2.2 h).mp (List.mem_toFinset.mp hhy)
    exact hxy (hslot_inj x hx y hy (hxEq.2.2.symm.trans hyEq.2.2))
  have hcard_eq : ∀ x ∈ G₀.V, (incL (slotOf x)).length = (incL (slotOf x)).toFinset.card :=
    fun x hx => (List.toFinset_card_of_nodup (hinc _ (hvlt _ (hext x hx).1)).1.1).symm
  have hbi := Finset.card_biUnion hdisj
  rw [Finset.sum_congr rfl hcard_eq, ← hbi]
  let allHE := G₀.E.image (fun e => 2 * e) ∪ G₀.E.image (fun e => 2 * e + 1)
  have hsub : G₀.V.biUnion (fun x => (incL (slotOf x)).toFinset) ⊆ allHE := by
    intro h hh
    rw [Finset.mem_biUnion] at hh
    rcases hh with ⟨x, hx, hhx⟩
    have hxs : slotOf x < vCap0 := hvlt _ (hext x hx).1
    have hmemE := ((hinc _ hxs).2.2 h).mp (List.mem_toFinset.mp hhx) |>.2.1
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases Nat.even_or_odd h with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · left; refine ⟨k, ?_, by omega⟩
      simpa [show (k + k) / 2 = k by omega] using hmemE
    · right; refine ⟨k, ?_, by omega⟩
      simpa [show (2 * k + 1) / 2 = k by omega] using hmemE
  have hall_le : allHE.card ≤ 2 * G₀.m := by
    calc allHE.card
        ≤ (G₀.E.image (fun e => 2 * e)).card + (G₀.E.image (fun e => 2 * e + 1)).card :=
          Finset.card_union_le _ _
      _ ≤ G₀.E.card + G₀.E.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * G₀.m := by simp [MGraph.m, two_mul]
  exact (Finset.card_le_card hsub).trans hall_le

def mgAdj (G : MGraph) (u v : ℕ) : Prop :=
  ∃ e ∈ G.E, (G.tail e = u ∧ G.head e = v) ∨ (G.tail e = v ∧ G.head e = u)

lemma nodup_idxOf_getElem : ∀ {L : List ℕ}, L.Nodup → ∀ k (hk : k < L.length),
    L.idxOf (L[k]'hk) = k
  | [], _, _, hk => by simp at hk
  | a :: t, hnd, 0, _ => by simp
  | a :: t, hnd, k + 1, hk => by
    rw [List.nodup_cons] at hnd
    have hmem : t[k]'(by simp at hk; omega) ∈ t := List.getElem_mem _
    have hne : a ≠ t[k]'(by simp at hk; omega) := fun heq => hnd.1 (heq ▸ hmem)
    simpa [List.idxOf_cons_ne _ hne] using nodup_idxOf_getElem hnd.2 k (by simp at hk; omega)

lemma mgraph_adj_of_edge {G : MGraph} {x y e : ℕ} (_hG : G.IsValid) (he : e ∈ G.E)
    (hx : G.tail e = x ∨ G.head e = x) (hy : y = G.tail e ∨ y = G.head e) :
    G.Connected x y := by
  by_cases hxy : x = y
  · subst hxy
    rcases hx with rfl | rfl
    · exact connected_refl G _
    · exact connected_refl G _
  · exact connected_of_edge he |> fun hconn => by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hconn
      · exact connected_symm hconn
      · exact absurd rfl hxy

private lemma memSlice_update_push {mem : ℕ → ℕ} {qBase qTail v : ℕ} :
    memSlice (Function.update mem (qBase + qTail) v) qBase (qTail + 1) =
      memSlice mem qBase qTail ++ [v] := by
  refine List.ext_getElem (by simp [memSlice_length]) fun i hi _ => ?_
  simp only [memSlice_length] at hi
  by_cases hil : i < qTail
  · rw [List.getElem_append_left (by simpa [memSlice_length] using hil),
      memSlice_getElem, memSlice_getElem, Function.update_of_ne (by omega)]
  · have hie : i = qTail := by omega
    subst hie
    rw [List.getElem_append_right (by simp [memSlice_length]), memSlice_getElem]
    simp

private lemma nodup_card_lt_of_not_mem {L : List ℕ} {V : Finset ℕ} {x : ℕ}
    (hnd : L.Nodup) (hsub : ∀ z ∈ L, z ∈ V) (hxV : x ∈ V) (hxL : x ∉ L) :
    L.length < V.card := by
  have hs : insert x L.toFinset ⊆ V := by
    intro z hz
    rw [Finset.mem_insert, List.mem_toFinset] at hz
    rcases hz with rfl | hz
    · exact hxV
    · exact hsub z hz
  have hc := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem (by simp [hxL]), List.toFinset_card_of_nodup hnd] at hc
  omega

lemma reachable_in_closed_set {G : MGraph} {S : Finset ℕ} {a b : ℕ}
    (hclosed : ∀ u ∈ S, ∀ v, mgAdj G u v → v ∈ S) (ha : a ∈ S) (hc : G.Connected a b) :
    b ∈ S := by
  obtain ⟨P, hW⟩ := hc
  induction P generalizing a with
  | nil => cases hW; exact ha
  | cons x Q ih =>
    cases hW with
    | cons hx hsrc hrest =>
      have hdst : G.dst x ∈ S := by
        refine hclosed a ha (G.dst x) ⟨x.1, hx, ?_⟩
        rcases x with ⟨e, _ | _⟩ <;> simp only [MGraph.src, MGraph.dst] at hsrc ⊢
        · exact Or.inr ⟨rfl, hsrc⟩
        · exact Or.inl ⟨hsrc, rfl⟩
      exact ih hdst hrest

/-! ## Static Base Addresses and Register Frame -/

structure ScanBases where
  vCap0 : ℕ
  eCap0 : ℕ
  n0 : ℕ
  vIdxBase : ℕ
  vListBase : ℕ
  thParentBase : ℕ
  origVertBase : ℕ
  isOrigBase : ℕ
  qBufABase : ℕ
  cRepsBase : ℕ
  visBBase : ℕ
  gVListBase : ℕ
  gExtToIntBase : ℕ
  gIntToExtBase : ℕ
  gIncHeadBase : ℕ
  gETailBase : ℕ
  gEHeadBase : ℕ
  gHeNextBase : ℕ

def mkScanBases (g0Ptr vCap auxPtr logCap vCap0 eCap0 n0 : ℕ) : ScanBases where
  vCap0 := vCap0
  eCap0 := eCap0
  n0 := n0
  vIdxBase := auxVIdxBase auxPtr
  vListBase := auxVListBase auxPtr vCap
  thParentBase := auxVListBase auxPtr vCap + 4 * n0 + 2 * (n0 * logCap)
  origVertBase := auxVListBase auxPtr vCap + 4 * n0 + 2 * (n0 * logCap) + n0
  isOrigBase := auxVListBase auxPtr vCap + 4 * n0 + 2 * (n0 * logCap) + n0 + vCap
  qBufABase := auxVListBase auxPtr vCap + 4 * n0 + 2 * (n0 * logCap) + n0 + 2 * vCap
  cRepsBase := auxVListBase auxPtr vCap + 4 * n0 + 2 * (n0 * logCap) + n0 + 3 * vCap
  visBBase := auxVListBase auxPtr vCap + 4 * n0 + 2 * (n0 * logCap) + n0 + 5 * vCap
  gVListBase := dgVListBase g0Ptr vCap0
  gExtToIntBase := dgExtToIntBase g0Ptr vCap0
  gIntToExtBase := dgIntToExtBase g0Ptr vCap0
  gIncHeadBase := dgIncHeadBase g0Ptr vCap0
  gETailBase := dgETailSlotBase g0Ptr vCap0 eCap0
  gEHeadBase := dgEHeadSlotBase g0Ptr vCap0 eCap0
  gHeNextBase := dgHeNextBase g0Ptr vCap0 eCap0

lemma scanBases_eq (g0Ptr vCap auxPtr vCap0 eCap0 n0 : ℕ) :
    let sb := mkScanBases g0Ptr vCap auxPtr (auxLogCap n0) vCap0 eCap0 n0
    sb.vIdxBase = auxVIdxBase auxPtr ∧
    sb.vListBase = auxVListBase auxPtr vCap ∧
    sb.origVertBase = auxOrigVertBase auxPtr vCap n0 ∧
    sb.isOrigBase = auxIsOrigVertBase auxPtr vCap n0 ∧
    sb.qBufABase = auxQBufABase auxPtr vCap n0 ∧
    sb.cRepsBase = auxQBufBBase auxPtr vCap n0 ∧
    sb.visBBase = auxVisBBase auxPtr vCap n0 := by
  dsimp [mkScanBases, auxVisBBase, auxVisABase, auxQBufBBase, auxQBufABase,
    auxIsOrigVertBase, auxOrigVertBase, auxThParentBase, auxUpMinIdxBase, auxUpVBase,
    auxT0DepthBase, auxT0ParentTreeIdxBase, auxT0ParentBase, auxVListBase, auxVIdxBase]
  exact ⟨rfl, rfl, by ring, by ring, by ring, by ring, by ring⟩

lemma scanBases_bounds {g0Ptr vCap auxPtr vCap0 eCap0 n0 : ℕ}
    (hle : g0Ptr + dynGraphSize vCap0 eCap0 ≤ auxPtr) (hnv0 : n0 ≤ vCap0) (_hnv : n0 ≤ vCap) :
    let sb := mkScanBases g0Ptr vCap auxPtr (auxLogCap n0) vCap0 eCap0 n0
    sb.gVListBase + n0 ≤ auxPtr ∧
    sb.gExtToIntBase + vCap0 ≤ auxPtr ∧
    sb.gIntToExtBase + vCap0 ≤ auxPtr ∧
    sb.gIncHeadBase + vCap0 ≤ auxPtr ∧
    sb.gETailBase + eCap0 ≤ auxPtr ∧
    sb.gEHeadBase + eCap0 ≤ auxPtr ∧
    sb.gHeNextBase + 2 * eCap0 ≤ auxPtr ∧
    auxPtr + auxHdrSize ≤ sb.vIdxBase ∧
    sb.vIdxBase + vCap = sb.vListBase ∧
    sb.vListBase + n0 ≤ sb.origVertBase ∧
    sb.origVertBase + vCap = sb.isOrigBase ∧
    sb.isOrigBase + vCap = sb.qBufABase ∧
    sb.qBufABase + vCap = sb.cRepsBase ∧
    sb.cRepsBase + 2 * vCap = sb.visBBase ∧
    sb.visBBase + vCap ≤ auxPtr + auxSize vCap n0 := by
  dsimp [mkScanBases, dgVListBase, dgExtToIntBase, dgIntToExtBase, dgIncHeadBase,
    dgETailSlotBase, dgEHeadSlotBase, dgHeNextBase, dynGraphSize,
    auxVListBase, auxVIdxBase, auxSize] at *
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  omega

structure ScanBaseRegs (s : State) (g0Ptr vCap auxPtr logCap : ℕ) (sb : ScanBases) : Prop where
  r0 : s.regs 0 = g0Ptr
  r1 : s.regs 1 = vCap
  r2 : s.regs 2 = auxPtr
  r3 : s.regs 3 = logCap
  r4 : s.regs 4 = sb.vCap0
  r5 : s.regs 5 = sb.eCap0
  r6 : s.regs 6 = sb.n0
  r7 : s.regs 7 = sb.vIdxBase
  r8 : s.regs 8 = sb.vListBase
  r9 : s.regs 9 = sb.thParentBase
  r10 : s.regs 10 = sb.origVertBase
  r11 : s.regs 11 = sb.isOrigBase
  r12 : s.regs 12 = sb.qBufABase
  r13 : s.regs 13 = sb.cRepsBase
  r14 : s.regs 14 = sb.visBBase
  r15 : s.regs 15 = sb.gVListBase
  r16 : s.regs 16 = sb.gExtToIntBase
  r17 : s.regs 17 = sb.gIntToExtBase
  r18 : s.regs 18 = sb.gIncHeadBase
  r19 : s.regs 19 = sb.gETailBase
  r20 : s.regs 20 = sb.gEHeadBase
  r21 : s.regs 21 = sb.gHeNextBase

lemma scanBaseRegs_upd {s : State} {g0Ptr vCap auxPtr logCap : ℕ} {sb : ScanBases}
    (hb : ScanBaseRegs s g0Ptr vCap auxPtr logCap sb) (r v : ℕ) (hr : 22 ≤ r) :
    ScanBaseRegs { s with regs := Function.update s.regs r v } g0Ptr vCap auxPtr logCap sb :=
  ⟨by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r0,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r1,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r2,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r3,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r4,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r5,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r6,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r7,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r8,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r9,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r10,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r11,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r12,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r13,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r14,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r15,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r16,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r17,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r18,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r19,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r20,
   by dsimp only; rw [Function.update_of_ne (by omega)]; exact hb.r21⟩

lemma scanBaseRegs_updMem {s : State} {g0Ptr vCap auxPtr logCap : ℕ} {sb : ScanBases}
    (hb : ScanBaseRegs s g0Ptr vCap auxPtr logCap sb) (m' : ℕ → ℕ) :
    ScanBaseRegs { s with mem := m' } g0Ptr vCap auxPtr logCap sb :=
  ⟨hb.r0, hb.r1, hb.r2, hb.r3, hb.r4, hb.r5, hb.r6, hb.r7, hb.r8, hb.r9, hb.r10,
   hb.r11, hb.r12, hb.r13, hb.r14, hb.r15, hb.r16, hb.r17, hb.r18, hb.r19, hb.r20, hb.r21⟩

/-! ## Inner Neighbor Check, Edge Walk, and Component BFS -/

private lemma checkNbr_bfs {w nbrVal startV qHead : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {uEndExpr : Expr} {sb : ScanBases}
    {g0Ptr vCap auxPtr logCap auxEnd : ℕ} {G₀ : MGraph}
    {preVis : Finset ℕ} {allQ : List ℕ} {memBase : ℕ → ℕ}
    (hw1 : 1 < 2 ^ w) (hauxW : auxEnd < 2 ^ w)
    (hb : ScanBaseRegs st g0Ptr vCap auxPtr logCap sb)
    (heval : uEndExpr.eval w st = some nbrVal)
    (hnbrV : nbrVal ∈ G₀.V) (hnbr_cap : nbrVal < vCap) (_hnv : G₀.n ≤ vCap)
    (_hpre_closed : ∀ a ∈ preVis, ∀ b, mgAdj G₀ a b → b ∈ preVis)
    (_hstart_npre : startV ∉ preVis)
    (hconn_nbr : G₀.Connected startV nbrVal)
    (hvis_bound : sb.visBBase + vCap ≤ auxEnd)
    (hq_bound : sb.qBufABase + vCap ≤ auxEnd)
    (hdisj_qv : sb.qBufABase + vCap ≤ sb.visBBase)
    (hinv : st.regs 25 = qHead ∧ st.regs 26 = allQ.length ∧
      memSlice st.mem sb.qBufABase allQ.length = allQ ∧
      allQ.length ≤ G₀.n ∧ allQ.Nodup ∧ (∀ z ∈ allQ, z ∈ G₀.V) ∧
      (0 < allQ.length ∧ allQ[0]? = some startV) ∧ (∀ z ∈ allQ, G₀.Connected startV z) ∧
      (∀ z ∈ G₀.V, st.mem (sb.visBBase + z) = if z ∈ preVis ∨ z ∈ allQ then 1 else 0) ∧
      (∀ z < vCap, z ∉ G₀.V → st.mem (sb.visBBase + z) = 0) ∧
      ∀ a, a < sb.qBufABase ∨ (sb.qBufABase + vCap ≤ a ∧ a < sb.visBBase) ∨
        sb.visBBase + vCap ≤ a → st.mem a = memBase a) :
    ∃ st' c, Runs w p ω (initScanCheckNbrStmt uEndExpr) st .normal st' c ∧
      (∃ allQ',
        ScanBaseRegs st' g0Ptr vCap auxPtr logCap sb ∧
        (∀ r, r ≠ 26 → r ≠ 32 → st'.regs r = st.regs r) ∧
        (nbrVal ∈ preVis ∨ nbrVal ∈ allQ') ∧
        (∀ z ∈ allQ, z ∈ allQ') ∧
        st'.regs 25 = qHead ∧ st'.regs 26 = allQ'.length ∧
        memSlice st'.mem sb.qBufABase allQ'.length = allQ' ∧
        allQ'.length ≤ G₀.n ∧ allQ'.Nodup ∧ (∀ z ∈ allQ', z ∈ G₀.V) ∧
        (0 < allQ'.length ∧ allQ'[0]? = some startV) ∧ (∀ z ∈ allQ', G₀.Connected startV z) ∧
        (∀ z ∈ G₀.V, st'.mem (sb.visBBase + z) = if z ∈ preVis ∨ z ∈ allQ' then 1 else 0) ∧
        (∀ z < vCap, z ∉ G₀.V → st'.mem (sb.visBBase + z) = 0) ∧
        allQ.length ≤ allQ'.length ∧
        (∀ i < allQ.length, st'.mem (sb.qBufABase + i) = st.mem (sb.qBufABase + i)) ∧
        (∀ a, a < sb.qBufABase ∨ (sb.qBufABase + vCap ≤ a ∧ a < sb.visBBase) ∨
          sb.visBBase + vCap ≤ a → st'.mem a = memBase a)) ∧
      c ≤ uEndExpr.size + 30 := by
  suffices h : ∃ o st' c, Runs w p ω (initScanCheckNbrStmt uEndExpr) st o st' c ∧
      (o = .normal ∧ ∃ allQ',
        ScanBaseRegs st' g0Ptr vCap auxPtr logCap sb ∧
        (∀ r, r ≠ 26 → r ≠ 32 → st'.regs r = st.regs r) ∧
        (nbrVal ∈ preVis ∨ nbrVal ∈ allQ') ∧
        (∀ z ∈ allQ, z ∈ allQ') ∧
        st'.regs 25 = qHead ∧ st'.regs 26 = allQ'.length ∧
        memSlice st'.mem sb.qBufABase allQ'.length = allQ' ∧
        allQ'.length ≤ G₀.n ∧ allQ'.Nodup ∧ (∀ z ∈ allQ', z ∈ G₀.V) ∧
        (0 < allQ'.length ∧ allQ'[0]? = some startV) ∧ (∀ z ∈ allQ', G₀.Connected startV z) ∧
        (∀ z ∈ G₀.V, st'.mem (sb.visBBase + z) = if z ∈ preVis ∨ z ∈ allQ' then 1 else 0) ∧
        (∀ z < vCap, z ∉ G₀.V → st'.mem (sb.visBBase + z) = 0) ∧
        allQ.length ≤ allQ'.length ∧
        (∀ i < allQ.length, st'.mem (sb.qBufABase + i) = st.mem (sb.qBufABase + i)) ∧
        (∀ a, a < sb.qBufABase ∨ (sb.qBufABase + vCap ≤ a ∧ a < sb.visBBase) ∨
          sb.visBBase + vCap ≤ a → st'.mem a = memBase a)) ∧
      c ≤ uEndExpr.size + 30 by
    rcases h with ⟨_, st', c, hr, ⟨rfl, hex⟩, hc⟩
    exact ⟨st', c, hr, hex, hc⟩
  rcases hinv with ⟨hr25, hr26, hmemQ, hqLen, hqNd, hqV, hq0, hqConn, hvis1, hvisOut, hfr⟩
  have hnbrW : nbrVal < 2 ^ w := by omega
  have hvis_addrW : sb.visBBase + nbrVal < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold initScanCheckNbrStmt
  refine runs_seq_assign_le (v := nbrVal) heval ?_
  set st1 : State := { st with regs := Function.update st.regs 32 nbrVal }
  have hb1 := scanBaseRegs_upd hb 32 nbrVal (by decide)
  have hcond_eval : Expr.eval w st1 (.bin .eq (.load (.bin .add (.reg 14) (.reg 32))) (.const 0)) =
      some (if st.mem (sb.visBBase + nbrVal) = 0 then 1 else 0) := by
    have hr14_1 := hb1.r14
    have hr32_1 : st1.regs 32 = nbrVal := by simp [st1]
    eval_expr
  refine WordRAM.runs_cond_le hcond_eval ?_ ?_
  · intro hne0
    have hnot_pre_Q : nbrVal ∉ preVis ∧ nbrVal ∉ allQ := by
      rw [hvis1 nbrVal hnbrV] at hne0
      by_cases hmem : nbrVal ∈ preVis ∨ nbrVal ∈ allQ
      · simp [hmem] at hne0
      · exact not_or.mp hmem
    have hvis_eq0 : st.mem (sb.visBBase + nbrVal) = 0 := by
      rw [hvis1 nbrVal hnbrV]
      simp [hnot_pre_Q]
    have hq_lt_n : allQ.length < G₀.n := nodup_card_lt_of_not_mem hqNd hqV hnbrV hnot_pre_Q.2
    have hq_addrW : sb.qBufABase + allQ.length < 2 ^ w := by omega
    have hq1_w : allQ.length + 1 < 2 ^ w := by omega
    have hr14_1 := hb1.r14
    have hr12_1 := hb1.r12
    have hr26_1 : st1.regs 26 = allQ.length := by simp [st1, hr26]
    have hr32_1 : st1.regs 32 = nbrVal := by simp [st1]
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
    refine runs_assign_le (v := allQ.length + 1) (by eval_expr) ?_ ?_
    · have hb_post : ScanBaseRegs
          { mem := Function.update (Function.update st1.mem (sb.visBBase + nbrVal) 1)
              (sb.qBufABase + allQ.length) nbrVal,
            regs := Function.update st1.regs 26 (allQ.length + 1),
            pos := st1.pos } g0Ptr vCap auxPtr logCap sb :=
        scanBaseRegs_upd (scanBaseRegs_updMem hb1 _) 26 (allQ.length + 1) (by decide)
      refine ⟨rfl, allQ ++ [nbrVal], hb_post,
        fun r hr26n hr32n => by
          dsimp only
          simp [st1, Function.update_of_ne hr26n, Function.update_of_ne hr32n],
        Or.inr (by simp), fun z hz => List.mem_append_left _ hz,
        by dsimp only; simp [st1, hr25], by dsimp only; simp, ?_, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_,
        by simp, fun i hi => by
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)], ?_⟩
      · dsimp only
        rw [List.length_append, List.length_singleton]
        have hms1 : memSlice (Function.update (Function.update st1.mem (sb.visBBase + nbrVal) 1)
            (sb.qBufABase + allQ.length) nbrVal) sb.qBufABase (allQ.length + 1) =
            memSlice (Function.update st1.mem (sb.visBBase + nbrVal) 1) sb.qBufABase allQ.length ++
              [nbrVal] := memSlice_update_push
        have hagree : memSlice (Function.update st1.mem (sb.visBBase + nbrVal) 1) sb.qBufABase allQ.length =
            memSlice st.mem sb.qBufABase allQ.length :=
          memSlice_eq_of_agree (base := sb.qBufABase) (len := allQ.length) fun i hi => by
            dsimp [st1]
            rw [Function.update_of_ne (by omega : sb.qBufABase + i ≠ sb.visBBase + nbrVal)]
        rw [hms1, hagree, hmemQ]
      · exact List.nodup_append.mpr ⟨hqNd, List.nodup_singleton _, fun a ha b hb => by
          simp only [List.mem_singleton] at hb; subst hb; intro heq; subst heq; exact hnot_pre_Q.2 ha⟩
      · intro z hz
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl <;> [exact hqV z hz; exact hnbrV]
      · refine ⟨by simp, ?_⟩
        rcases List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hq0.1) with ⟨a, as, has⟩
        have h0' := hq0.2
        rw [has] at h0' ⊢
        simpa using h0'
      · intro z hz
        simp only [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl <;> [exact hqConn z hz; exact hconn_nbr]
      · intro z hzV
        dsimp only
        by_cases hzn : z = nbrVal
        · subst z
          simp [Function.update_of_ne (by omega : sb.visBBase + nbrVal ≠ sb.qBufABase + allQ.length)]
        · have hne1 : sb.visBBase + z ≠ sb.qBufABase + allQ.length := by omega
          have hne2 : sb.visBBase + z ≠ sb.visBBase + nbrVal := by omega
          rw [Function.update_of_ne hne1, Function.update_of_ne hne2, hvis1 z hzV]
          simp [List.mem_append, hzn]
      · intro z hz hznot
        dsimp only
        have hzn : z ≠ nbrVal := fun h => hznot (h ▸ hnbrV)
        have hne1 : sb.visBBase + z ≠ sb.qBufABase + allQ.length := by omega
        have hne2 : sb.visBBase + z ≠ sb.visBBase + nbrVal := by omega
        rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
        exact hvisOut z hz hznot
      · intro a ha
        dsimp only
        have hne1 : a ≠ sb.qBufABase + allQ.length := by
          rcases ha with h | ⟨h1, h2⟩ | h <;> omega
        have hne2 : a ≠ sb.visBBase + nbrVal := by
          rcases ha with h | ⟨h1, h2⟩ | h <;> omega
        rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
        exact hfr a ha
    · dsimp [Expr.size]; omega
  · intro heq0
    have hmem_preQ : nbrVal ∈ preVis ∨ nbrVal ∈ allQ := by
      rw [hvis1 nbrVal hnbrV] at heq0
      by_cases hmem : nbrVal ∈ preVis ∨ nbrVal ∈ allQ
      · exact hmem
      · simp [hmem] at heq0
    exact runs_nop_le ⟨rfl, allQ, scanBaseRegs_upd hb 32 nbrVal (by decide),
      fun r hr26n hr32n => by simp [st1, Function.update_of_ne hr32n],
      hmem_preQ, fun z hz => hz, by simp [st1, hr25], by simp [st1, hr26], hmemQ, hqLen, hqNd,
      hqV, hq0, hqConn, hvis1, hvisOut, le_rfl, fun _ _ => rfl, hfr⟩ (by dsimp [Expr.size]; omega)

lemma walkInc_runs {w x s startV qHead : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {sb : ScanBases}
    {g0Ptr vCap auxPtr logCap auxEnd vCap0 eCap0 : ℕ} {G₀ : MGraph}
    {preVis : Finset ℕ} {allQ0 : List ℕ} {mem₀ : ℕ → ℕ} {L_s : List ℕ}
    (hw1 : 1 < 2 ^ w) (hauxW : auxEnd < 2 ^ w)
    (hdg : DynGraphAt mem₀ g0Ptr vCap0 eCap0 G₀)
    (hvs : G₀.n ≤ vCap) (hvs0 : vCap0 ≤ vCap) (haux_lo : g0Ptr + dynGraphSize vCap0 eCap0 ≤ auxPtr)
    (hvis_bound : sb.visBBase + vCap ≤ auxEnd)
    (hq_bound : sb.qBufABase + vCap ≤ auxEnd)
    (hdisj_qv : sb.qBufABase + vCap ≤ sb.visBBase)
    (hle_aux : auxPtr + auxHdrSize ≤ sb.qBufABase)
    (hsb_eq : sb.gExtToIntBase = dgExtToIntBase g0Ptr vCap0 ∧
      sb.gIntToExtBase = dgIntToExtBase g0Ptr vCap0 ∧
      sb.gIncHeadBase = dgIncHeadBase g0Ptr vCap0 ∧
      sb.gETailBase = dgETailSlotBase g0Ptr vCap0 eCap0 ∧
      sb.gEHeadBase = dgEHeadSlotBase g0Ptr vCap0 eCap0 ∧
      sb.gHeNextBase = dgHeNextBase g0Ptr vCap0 eCap0)
    (hxV : x ∈ G₀.V) (hs_eq : s = mem₀ (dgExtToIntBase g0Ptr vCap0 + x))
    (hLs_dll : IsDoublyLinkedList mem₀ (dgHePrevBase g0Ptr vCap0 eCap0)
      (dgHeNextBase g0Ptr vCap0 eCap0) (dgIncHeadBase g0Ptr vCap0 + s) (2 * eCap0) L_s)
    (hLs_mem : ∀ h, h ∈ L_s ↔ h < 2 * eCap0 ∧ h / 2 ∈ G₀.E ∧
      (if h % 2 = 0 then mem₀ (dgETailSlotBase g0Ptr vCap0 eCap0 + h / 2)
       else mem₀ (dgEHeadSlotBase g0Ptr vCap0 eCap0 + h / 2)) = s)
    (hpre_closed : ∀ a ∈ preVis, ∀ b, mgAdj G₀ a b → b ∈ preVis)
    (hstart_npre : startV ∉ preVis) (hx_npre : x ∉ preVis) (hx_conn : G₀.Connected startV x)
    (hb : ScanBaseRegs st g0Ptr vCap auxPtr logCap sb)
    (hr29 : st.regs 29 = match L_s with | [] => 0 | h :: _ => h + 1)
    (hinv0 : st.regs 25 = qHead ∧ st.regs 26 = allQ0.length ∧
      memSlice st.mem sb.qBufABase allQ0.length = allQ0 ∧
      allQ0.length ≤ G₀.n ∧ allQ0.Nodup ∧ (∀ z ∈ allQ0, z ∈ G₀.V) ∧
      (0 < allQ0.length ∧ allQ0[0]? = some startV) ∧ (∀ z ∈ allQ0, G₀.Connected startV z) ∧
      (∀ z ∈ G₀.V, st.mem (sb.visBBase + z) = if z ∈ preVis ∨ z ∈ allQ0 then 1 else 0) ∧
      (∀ z < vCap, z ∉ G₀.V → st.mem (sb.visBBase + z) = 0) ∧
      ∀ a, a < sb.qBufABase ∨ (sb.qBufABase + vCap ≤ a ∧ a < sb.visBBase) ∨
        sb.visBBase + vCap ≤ a → st.mem a = mem₀ a) :
    ∃ st' c, Runs w p ω
      (.loop (.reg 29)
        (.assign 30 (.bin .sub (.reg 29) (.const 1)) ;;
         .assign 31 (.bin .div (.reg 30) (.const 2)) ;;
         .assign 29 (.load (.bin .add (.reg 21) (.reg 30))) ;;
         initScanCheckNbrStmt
           (.load (.bin .add (.reg 17) (.load (.bin .add (.reg 19) (.reg 31))))) ;;
         initScanCheckNbrStmt
           (.load (.bin .add (.reg 17) (.load (.bin .add (.reg 20) (.reg 31))))))) st .normal st' c ∧
      (∃ allQ',
        ScanBaseRegs st' g0Ptr vCap auxPtr logCap sb ∧
        (∀ r ∈ ([22, 23, 25] : List ℕ), st'.regs r = st.regs r) ∧
        (∀ z ∈ allQ0, z ∈ allQ') ∧
        (∀ y, mgAdj G₀ x y → y ∈ allQ') ∧
        st'.regs 25 = qHead ∧ st'.regs 26 = allQ'.length ∧
        memSlice st'.mem sb.qBufABase allQ'.length = allQ' ∧
        allQ'.length ≤ G₀.n ∧ allQ'.Nodup ∧ (∀ z ∈ allQ', z ∈ G₀.V) ∧
        (0 < allQ'.length ∧ allQ'[0]? = some startV) ∧ (∀ z ∈ allQ', G₀.Connected startV z) ∧
        (∀ z ∈ G₀.V, st'.mem (sb.visBBase + z) = if z ∈ preVis ∨ z ∈ allQ' then 1 else 0) ∧
        (∀ z < vCap, z ∉ G₀.V → st'.mem (sb.visBBase + z) = 0) ∧
        allQ0.length ≤ allQ'.length ∧
        (∀ i < allQ0.length, st'.mem (sb.qBufABase + i) = st.mem (sb.qBufABase + i)) ∧
        (∀ a, a < sb.qBufABase ∨ (sb.qBufABase + vCap ≤ a ∧ a < sb.visBBase) ∨
          sb.visBBase + vCap ≤ a → st'.mem a = mem₀ a)) ∧
      c ≤ 140 * L_s.length + 10 := by
  rcases hdg with ⟨hG₀, hvlt0, helt0, _, _, _, _, _, _, hext, _, _, _, heEnds, _⟩
  let Inv : State → Prop := fun st_k => ∃ k allQ,
    k ≤ L_s.length ∧
    ScanBaseRegs st_k g0Ptr vCap auxPtr logCap sb ∧
    st_k.regs 22 = st.regs 22 ∧ st_k.regs 23 = st.regs 23 ∧
    st_k.regs 29 = (if hk : k < L_s.length then L_s[k] + 1 else 0) ∧
    (∀ z ∈ allQ0, z ∈ allQ) ∧
    (∀ i, i < k →
      let e := L_s.getD i 0 / 2
      G₀.tail e ∈ allQ ∧ G₀.head e ∈ allQ) ∧
    st_k.regs 25 = qHead ∧ st_k.regs 26 = allQ.length ∧
    memSlice st_k.mem sb.qBufABase allQ.length = allQ ∧
    allQ.length ≤ G₀.n ∧ allQ.Nodup ∧ (∀ z ∈ allQ, z ∈ G₀.V) ∧
    (0 < allQ.length ∧ allQ[0]? = some startV) ∧ (∀ z ∈ allQ, G₀.Connected startV z) ∧
    (∀ z ∈ G₀.V, st_k.mem (sb.visBBase + z) = if z ∈ preVis ∨ z ∈ allQ then 1 else 0) ∧
    (∀ z < vCap, z ∉ G₀.V → st_k.mem (sb.visBBase + z) = 0) ∧
    allQ0.length ≤ allQ.length ∧
    (∀ i < allQ0.length, st_k.mem (sb.qBufABase + i) = st.mem (sb.qBufABase + i)) ∧
    ∀ a, a < sb.qBufABase ∨ (sb.qBufABase + vCap ≤ a ∧ a < sb.visBBase) ∨
      sb.visBBase + vCap ≤ a → st_k.mem a = mem₀ a
  have hloop := Triple.loop_measure (w := w) (p := p) (e := .reg 29)
    (body := initScanWalkIncBodyStmt)
    (Inv := Inv) (Q := normalPost (fun st_k => Inv st_k ∧ st_k.regs 29 = 0))
    (m := fun st_k =>
      if h0 : st_k.regs 29 = 0 then 0
      else L_s.length - L_s.idxOf (st_k.regs 29 - 1))
    (rem := fun st_k =>
      (if h0 : st_k.regs 29 = 0 then 0
       else 140 * (L_s.length - L_s.idxOf (st_k.regs 29 - 1))) + 10)
    (condVal := fun st_k => st_k.regs 29)
    (fun st_k _ => by eval_expr)
    (fun st_k hInv hv0 => ⟨⟨hInv, hv0⟩, by simp [hv0, Expr.size]⟩)
    (fun st_k hInv hv_ne => by
      rcases hInv with ⟨k, allQ, hk_le, hb_k, hr22, hr23, hr29_k, hqSub, hEdges,
        hr25_k, hr26_k, hmemQ_k, hqLen_k, hqNd_k, hqV_k, hq0_k, hqConn_k, hvis1_k, hvisOut_k,
        hLenLe_k, hPref_k, hfr_k⟩
      have hk_lt : k < L_s.length := by
        by_contra hge
        simp [hge] at hr29_k
        exact hv_ne hr29_k
      have hr29_eq : st_k.regs 29 = L_s[k] + 1 := by simp [hk_lt] at hr29_k; exact hr29_k
      have h_memL : L_s[k] ∈ L_s := List.getElem_mem hk_lt
      have hh_lt2e : L_s[k] < 2 * eCap0 := hLs_dll.2.1 _ h_memL
      have hh_info := (hLs_mem _).mp h_memL
      have he_E : L_s[k] / 2 ∈ G₀.E := hh_info.2.1
      have he_cap : L_s[k] / 2 < eCap0 := helt0 _ he_E
      have hIdxOf : L_s.idxOf (L_s[k]) = k := nodup_idxOf_getElem hLs_dll.1 k hk_lt
      have hm_val : (if h0 : st_k.regs 29 = 0 then 0
          else L_s.length - L_s.idxOf (st_k.regs 29 - 1)) = L_s.length - k := by
        simp [hr29_eq, hIdxOf]
      have hrem_val : (if h0 : st_k.regs 29 = 0 then 0
          else 140 * (L_s.length - L_s.idxOf (st_k.regs 29 - 1))) + 10 =
          140 * (L_s.length - k) + 10 := by
        simp [hr29_eq, hIdxOf]
      have heEnds_k := heEnds _ he_E
      have haux_w : auxPtr < 2 ^ w := by
        have : auxPtr + auxHdrSize ≤ auxEnd := by omega
        omega
      have heT_mem : st_k.mem (sb.gETailBase + L_s[k] / 2) =
          mem₀ (dgExtToIntBase g0Ptr vCap0 + G₀.tail (L_s[k] / 2)) := by
        rw [hfr_k _ (Or.inl (by rw [hsb_eq.2.2.2.1]; dsimp [dgETailSlotBase, dynGraphSize] at *; omega)),
          hsb_eq.2.2.2.1, heEnds_k.1]
      have heH_mem : st_k.mem (sb.gEHeadBase + L_s[k] / 2) =
          mem₀ (dgExtToIntBase g0Ptr vCap0 + G₀.head (L_s[k] / 2)) := by
        rw [hfr_k _ (Or.inl (by rw [hsb_eq.2.2.2.2.1]; dsimp [dgEHeadSlotBase, dynGraphSize] at *; omega)),
          hsb_eq.2.2.2.2.1, heEnds_k.2]
      have ht_int_ext : st_k.mem (sb.gIntToExtBase + st_k.mem (sb.gETailBase + L_s[k] / 2)) =
          G₀.tail (L_s[k] / 2) := by
        rw [heT_mem]
        have htV := (hG₀ _ he_E).1
        have hlt_slot : mem₀ (dgExtToIntBase g0Ptr vCap0 + G₀.tail (L_s[k] / 2)) < vCap0 :=
          hvlt0 _ (hext _ htV).1
        rw [hfr_k _ (Or.inl (by rw [hsb_eq.2.1]; dsimp [dgIntToExtBase, dynGraphSize] at *; omega)),
          hsb_eq.2.1]
        exact (hext _ htV).2
      have hNext_eq : st_k.mem (sb.gHeNextBase + L_s[k]) =
          if k + 1 = L_s.length then 0 else L_s.getD (k + 1) 0 + 1 := by
        rw [hfr_k _ (Or.inl (by rw [hsb_eq.2.2.2.2.2]; dsimp [dgHeNextBase, dynGraphSize] at *; omega)),
          hsb_eq.2.2.2.2.2]
        exact (hLs_dll.2.2.2 k hk_lt).2
      have hNext_eq' : st_k.mem (sb.gHeNextBase + L_s[k]) =
          if hk1 : k + 1 < L_s.length then L_s[k + 1] + 1 else 0 := by
        rw [hNext_eq]
        by_cases hk1 : k + 1 < L_s.length
        · have hne_l : k + 1 ≠ L_s.length := by omega
          simp [hk1, hne_l]
        · have heq_l : k + 1 = L_s.length := by omega
          simp [heq_l]
      have h_words : L_s[k] < 2 ^ w ∧ L_s[k] / 2 < 2 ^ w ∧
          sb.gHeNextBase + L_s[k] < 2 ^ w ∧
          st_k.mem (sb.gHeNextBase + L_s[k]) < 2 ^ w := by
        have h2e_aux : 2 * eCap0 ≤ auxPtr := by dsimp [dynGraphSize] at haux_lo; omega
        have haux_end : auxPtr ≤ auxEnd := by omega
        refine ⟨by omega, by omega,
          by rw [hsb_eq.2.2.2.2.2]; dsimp [dgHeNextBase, dynGraphSize] at *; omega, ?_⟩
        rw [hNext_eq']
        split_ifs with hk1
        · have hmem1 : L_s[k + 1] ∈ L_s := List.getElem_mem hk1
          have hlt2e : L_s[k + 1] < 2 * eCap0 := hLs_dll.2.1 _ hmem1
          omega
        · omega
      have hx_end : G₀.tail (L_s[k] / 2) = x ∨ G₀.head (L_s[k] / 2) = x := by
        rcases Nat.mod_two_eq_zero_or_one L_s[k] with hm0 | hm1
        · have hslot := hh_info.2.2
          simp only [hm0, ↓reduceIte] at hslot
          rw [heEnds_k.1] at hslot
          left
          have htV := (hG₀ _ he_E).1
          have := congrArg (fun slot => mem₀ (dgIntToExtBase g0Ptr vCap0 + slot)) hslot
          simpa [hs_eq, (hext _ htV).2, (hext x hxV).2] using this
        · have hslot := hh_info.2.2
          simp only [hm1, show (1 : ℕ) ≠ 0 by decide, ↓reduceIte] at hslot
          rw [heEnds_k.2] at hslot
          right
          have hhV := (hG₀ _ he_E).2
          have := congrArg (fun slot => mem₀ (dgIntToExtBase g0Ptr vCap0 + slot)) hslot
          simpa [hs_eq, (hext _ hhV).2, (hext x hxV).2] using this
      refine ⟨100, fun s_0 ω' hs0 => ?_⟩
      subst s_0
      unfold initScanWalkIncBodyStmt
      have hr29_sub : Expr.eval w st_k (.bin .sub (.reg 29) (.const 1)) = some L_s[k] := by
        have h2e_aux : 2 * eCap0 ≤ auxPtr := by dsimp [dynGraphSize] at haux_lo; omega
        have hlt29 : L_s[k] + 1 < 2 ^ w := by omega
        have hsub := Expr.eval_sub
          (by show Expr.eval w st_k (.reg 29) = some (L_s[k] + 1)
              simp [Expr.eval, hr29_eq])
          (Expr.eval_const hw1) hlt29
        rwa [Nat.add_sub_cancel] at hsub
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := L_s[k]) hr29_sub ?_
      refine runs_seq_assign_le (v := L_s[k] / 2) (by eval_expr) ?_
      refine runs_seq_assign_le (v := st_k.mem (sb.gHeNextBase + L_s[k]))
        (by have := hb_k.r21; eval_expr) ?_
      set stA := { st_k with
        regs := Function.update
          (Function.update (Function.update st_k.regs 30 L_s[k]) 31 (L_s[k] / 2))
          29 (st_k.mem (sb.gHeNextBase + L_s[k])) }
      have hbA : ScanBaseRegs stA g0Ptr vCap auxPtr logCap sb :=
        scanBaseRegs_upd (scanBaseRegs_upd (scanBaseRegs_upd hb_k 30 _ (by decide)) 31 _ (by decide)) 29 _ (by decide)
      have heval_tail : Expr.eval w stA
          (.load (.bin .add (.reg 17) (.load (.bin .add (.reg 19) (.reg 31))))) =
          some (G₀.tail (L_s[k] / 2)) := by
        have h17 := hbA.r17
        have h19 := hbA.r19
        have h31 : stA.regs 31 = L_s[k] / 2 := by simp [stA]
        have hlt1 : sb.gETailBase + L_s[k] / 2 < 2 ^ w := by
          rw [hsb_eq.2.2.2.1]; dsimp [dgETailSlotBase, dynGraphSize] at *; omega
        have hlt2 : sb.gIntToExtBase + st_k.mem (sb.gETailBase + L_s[k] / 2) < 2 ^ w := by
          rw [heT_mem]
          have := hvlt0 _ (hext _ (hG₀ _ he_E).1).1
          rw [hsb_eq.2.1]; dsimp [dgIntToExtBase, dynGraphSize] at *; omega
        have htV_W : G₀.tail (L_s[k] / 2) < 2 ^ w := by
          have := hvlt0 _ (hG₀ _ he_E).1; omega
        eval_expr
      have ht_conn : G₀.Connected startV (G₀.tail (L_s[k] / 2)) :=
        connected_trans hx_conn (mgraph_adj_of_edge hG₀ he_E hx_end (Or.inl rfl))
      have hh_conn : G₀.Connected startV (G₀.head (L_s[k] / 2)) :=
        connected_trans hx_conn (mgraph_adj_of_edge hG₀ he_E hx_end (Or.inr rfl))
      obtain ⟨stB, c1, hr1, ⟨allQ1, hbB, hrpres1, ht_mem1, hsub1, hr25_B, hr26_B, hmemQ_B,
          hqLen_B, hqNd_B, hqV_B, hq0_B, hqConn_B, hvis1_B, hvisOut_B, hLenLe_B, hPref_B, hfr_B⟩, hc1⟩ :=
        checkNbr_bfs (qHead := qHead) (ω := ω') hw1 hauxW hbA heval_tail (hG₀ _ he_E).1
          (by have := hvlt0 _ (hG₀ _ he_E).1; omega) hvs hpre_closed hstart_npre ht_conn
          hvis_bound hq_bound hdisj_qv
          ⟨by simp [stA, hr25_k], by simp [stA, hr26_k], hmemQ_k, hqLen_k, hqNd_k, hqV_k,
            hq0_k, hqConn_k, hvis1_k, hvisOut_k, hfr_k⟩
      have heval_head : Expr.eval w stB
          (.load (.bin .add (.reg 17) (.load (.bin .add (.reg 20) (.reg 31))))) =
          some (G₀.head (L_s[k] / 2)) := by
        have h17 := hbB.r17
        have h20 := hbB.r20
        have h31 : stB.regs 31 = L_s[k] / 2 := by rw [hrpres1 31 (by decide) (by decide)]; simp [stA]
        have haddr1 : sb.gEHeadBase + L_s[k] / 2 < 2 ^ w := by
          rw [hsb_eq.2.2.2.2.1]; dsimp [dgEHeadSlotBase, dynGraphSize] at *; omega
        have hmE : stB.mem (sb.gEHeadBase + L_s[k] / 2) =
            mem₀ (dgExtToIntBase g0Ptr vCap0 + G₀.head (L_s[k] / 2)) := by
          rw [hfr_B _ (Or.inl (by rw [hsb_eq.2.2.2.2.1]; dsimp [dgEHeadSlotBase, dynGraphSize] at *; omega)),
            hsb_eq.2.2.2.2.1, heEnds_k.2]
        have hlt_slot : mem₀ (dgExtToIntBase g0Ptr vCap0 + G₀.head (L_s[k] / 2)) < vCap0 :=
          hvlt0 _ (hext _ (hG₀ _ he_E).2).1
        have haddr2 : sb.gIntToExtBase + stB.mem (sb.gEHeadBase + L_s[k] / 2) < 2 ^ w := by
          rw [hmE]
          rw [hsb_eq.2.1]; dsimp [dgIntToExtBase, dynGraphSize] at *; omega
        have hhV_W : G₀.head (L_s[k] / 2) < 2 ^ w := by
          have := hvlt0 _ (hG₀ _ he_E).2; omega
        have hh_eq' : stB.mem (sb.gIntToExtBase + stB.mem (sb.gEHeadBase + L_s[k] / 2)) =
            G₀.head (L_s[k] / 2) := by
          rw [hmE, hfr_B _ (Or.inl (by rw [hsb_eq.2.1]; dsimp [dgIntToExtBase, dynGraphSize] at *; omega)),
            hsb_eq.2.1]
          exact (hext _ (hG₀ _ he_E).2).2
        eval_expr
        try simp [hh_eq']
      obtain ⟨stC, c2, hr2, ⟨allQ2, hbC, hrpres2, hh_mem2, hsub2, hr25_C, hr26_C, hmemQ_C,
          hqLen_C, hqNd_C, hqV_C, hq0_C, hqConn_C, hvis1_C, hvisOut_C, hLenLe_C, hPref_C, hfr_C⟩, hc2⟩ :=
        checkNbr_bfs (qHead := qHead) (ω := ω') hw1 hauxW hbB heval_head (hG₀ _ he_E).2
          (by have := hvlt0 _ (hG₀ _ he_E).2; omega) hvs hpre_closed hstart_npre hh_conn
          hvis_bound hq_bound hdisj_qv
          ⟨hr25_B, hr26_B, hmemQ_B, hqLen_B, hqNd_B, hqV_B, hq0_B, hqConn_B, hvis1_B, hvisOut_B, hfr_B⟩
      refine ⟨.normal, stC, c1 + c2 + 1, WordRAM.runs_seq_iff.mpr (Or.inr ⟨stB, c1, c2, hr1, hr2, rfl⟩),
        ?_, ?_⟩
      have ht_allQ2 : G₀.tail (L_s[k] / 2) ∈ allQ2 := by
        rcases ht_mem1 with ht_pre | ht_q
        · exfalso
          exact hx_npre (by
            rcases hx_end with hx_eq | hx_eq
            · exact hx_eq ▸ ht_pre
            · exact hpre_closed _ ht_pre x ⟨L_s[k] / 2, he_E, Or.inl ⟨rfl, hx_eq⟩⟩)
        · exact hsub2 _ ht_q
      have hh_allQ2 : G₀.head (L_s[k] / 2) ∈ allQ2 := by
        rcases hh_mem2 with hh_pre | hh_q
        · exfalso
          exact hx_npre (by
            rcases hx_end with hx_eq | hx_eq
            · exact hpre_closed _ hh_pre x ⟨L_s[k] / 2, he_E, Or.inr ⟨hx_eq, rfl⟩⟩
            · exact hx_eq ▸ hh_pre)
        · exact hh_q
      have hr29_C : stC.regs 29 = if hk1 : k + 1 < L_s.length then L_s[k + 1] + 1 else 0 := by
        rw [hrpres2 29 (by decide) (by decide), hrpres1 29 (by decide) (by decide)]
        simpa [stA] using hNext_eq'
      refine ⟨⟨k + 1, allQ2, by omega, hbC,
          by rw [hrpres2 22 (by decide) (by decide), hrpres1 22 (by decide) (by decide)]; simp [stA, hr22],
          by rw [hrpres2 23 (by decide) (by decide), hrpres1 23 (by decide) (by decide)]; simp [stA, hr23],
          hr29_C, fun z hz => hsub2 z (hsub1 z (hqSub z hz)), fun i hi => ?_,
          hr25_C, hr26_C, hmemQ_C, hqLen_C, hqNd_C, hqV_C, hq0_C, hqConn_C, hvis1_C, hvisOut_C,
          le_trans hLenLe_k (le_trans hLenLe_B hLenLe_C),
          fun i hi => by
            rw [hPref_C i (lt_of_lt_of_le hi (le_trans hLenLe_k hLenLe_B)),
              hPref_B i (lt_of_lt_of_le hi hLenLe_k), hPref_k i hi],
          hfr_C⟩,
        ?_, ?_⟩
      · by_cases hik : i = k
        · subst i
          simpa [hk_lt] using ⟨ht_allQ2, hh_allQ2⟩
        · have ⟨h1, h2⟩ := hEdges i (by omega)
          exact ⟨hsub2 _ (hsub1 _ h1), hsub2 _ (hsub1 _ h2)⟩
      · rw [hm_val]
        by_cases hk1 : k + 1 < L_s.length
        · have hidx1 : L_s.idxOf (L_s[k + 1]) = k + 1 := nodup_idxOf_getElem hLs_dll.1 (k + 1) hk1
          simp [hk1, hr29_C, hidx1]; omega
        · simp [hk1, hr29_C]; omega
      · rw [hrem_val]
        by_cases hk1 : k + 1 < L_s.length
        · have hidx1 : L_s.idxOf (L_s[k + 1]) = k + 1 := nodup_idxOf_getElem hLs_dll.1 (k + 1) hk1
          simp only [hr29_C, hk1, ↓reduceDIte, Nat.add_eq_zero_iff, one_ne_zero, and_false,
            Nat.add_sub_cancel, hidx1, Expr.size]
          omega
        · simp only [hr29_C, hk1, ↓reduceDIte, Expr.size]; omega
      · simp only [Expr.size] at hc1 hc2 ⊢
        omega)
  have hInv0 : Inv st := by
    refine ⟨0, allQ0, Nat.zero_le _, hb, rfl, rfl, ?_, fun _ h => h, fun _ h => by omega,
      hinv0.1, hinv0.2.1, hinv0.2.2.1, hinv0.2.2.2.1, hinv0.2.2.2.2.1, hinv0.2.2.2.2.2.1,
      hinv0.2.2.2.2.2.2.1, hinv0.2.2.2.2.2.2.2.1, hinv0.2.2.2.2.2.2.2.2.1,
      hinv0.2.2.2.2.2.2.2.2.2.1, le_rfl, fun _ _ => rfl, hinv0.2.2.2.2.2.2.2.2.2.2⟩
    rw [hr29]
    cases L_s with
    | nil => simp
    | cons a t => simp
  obtain ⟨o, st', c, hr, hpost, hc⟩ := hloop st ω hInv0
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨⟨k, allQ', hk_le, hb', hr22', hr23', hr29', hsub0, hEdges',
      hr25', hr26', hmemQ', hqLen', hqNd', hqV', hq0', hqConn', hvis1', hvisOut',
      hLenLe', hPref', hfr'⟩, hr29_zero⟩
    have hk_eq : k = L_s.length := by
      by_contra hne
      have hk_lt : k < L_s.length := by omega
      simp [hk_lt] at hr29'
      omega
    subst hk_eq
    have hadj : ∀ y, mgAdj G₀ x y → y ∈ allQ' := by
      intro y ⟨e, heE, heEnds_xy⟩
      have h_in_Ls : (if G₀.tail e = x then 2 * e else 2 * e + 1) ∈ L_s := by
        rcases heEnds_xy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [↓reduceIte, hLs_mem]
          refine ⟨by have := helt0 e heE; omega, by simpa [show 2 * e / 2 = e by omega] using heE, ?_⟩
          simp [Nat.mul_mod_right, show 2 * e / 2 = e by omega, (heEnds e heE).1, hs_eq]
        · by_cases hloop_e : G₀.tail e = G₀.head e
          · simp only [hloop_e, ↓reduceIte, hLs_mem]
            refine ⟨by have := helt0 e heE; omega, by simpa [show 2 * e / 2 = e by omega] using heE, ?_⟩
            simp [Nat.mul_mod_right, show 2 * e / 2 = e by omega, (heEnds e heE).1, hloop_e, hs_eq]
          · simp only [hloop_e, ↓reduceIte, hLs_mem]
            refine ⟨by have := helt0 e heE; omega,
              by simpa [show (2 * e + 1) / 2 = e by omega] using heE, ?_⟩
            simp [show (2 * e + 1) % 2 = 1 by omega,
              show (2 * e + 1) / 2 = e by omega, (heEnds e heE).2, hs_eq]
      obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_getElem.mp h_in_Ls
      have hpair := hEdges' i hi_lt
      have he_div : L_s[i] / 2 = e := by rw [hi_eq]; split_ifs <;> omega
      rw [List.getD_eq_getElem _ _ hi_lt, he_div] at hpair
      rcases heEnds_xy with ⟨_, rfl⟩ | ⟨rfl, _⟩
      · exact hpair.2
      · exact hpair.1
    refine ⟨st', c, hr, ⟨allQ', hb', fun r hr => ?_, hsub0, hadj,
      hr25', hr26', hmemQ', hqLen', hqNd', hqV', hq0', hqConn', hvis1', hvisOut',
      hLenLe', hPref', hfr'⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> [exact hr22'; exact hr23'; exact hr25'.trans hinv0.1.symm]
    · have hbd : (if h0 : st.regs 29 = 0 then 0
          else 140 * (L_s.length - L_s.idxOf (st.regs 29 - 1))) + 10 ≤ 140 * L_s.length + 10 := by
        split_ifs <;> omega
      exact le_trans hc hbd

end

end MinCostFlow.LSF.Program

