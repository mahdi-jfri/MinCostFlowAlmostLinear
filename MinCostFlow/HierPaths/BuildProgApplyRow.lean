module

public import MinCostFlow.HierPaths.BuildProgMatchRead
public import MinCostFlow.HierPaths.BuildProgGameAppend
import MinCostFlow.HierPaths.QueryProgRoute

/-!
# Applying one routed matching to its child

Read the matching coordinates once. Then append the matching endpoints to the
local graph and store the shortcut walks in the order of the appended edges.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Read a word of the matching coordinates packet in register 4. -/
def matchCoordExpr (j : ℕ) : Expr := .load (.bin .add (.reg 4) (.const j))

/-- Args are `[matchTable, walkTable, rows, row, tmp, graph, off, ends, verts, positions,
directory, heap]`. Return the next free word of the walk arena. -/
def buildApplyRowProc (fRead fAppend fWalks : ℕ) : Stmt :=
  .seq (.call 12 fRead [.reg 0, .reg 2, .reg 3, .reg 4])
    (.seq (.call 12 fAppend [.reg 5, matchCoordExpr 0, matchCoordExpr 1, .reg 6])
      (.seq (.call 12 fWalks [.reg 1, matchCoordExpr 3, matchCoordExpr 2, matchCoordExpr 0,
        .reg 7, .reg 8, .reg 9, .reg 10, .reg 11, matchCoordExpr 1]) (.ret (.reg 12))))

theorem buildApplyRowProc_noRand (fRead fAppend fWalks : ℕ) :
    (buildApplyRowProc fRead fAppend fWalks).NoRand := by
  simp [buildApplyRowProc, Stmt.NoRand]

/-- The address at which the matching row's endpoint words begin. -/
def matchingRowBase (Ms : List (List (ℕ × ℕ))) (mt i : ℕ) : ℕ :=
  mt + (Ms.length + 1) + 2 * flatIndex Ms i 0

/-- The local graph may grow up to the matching and raw-walk tables. The parent graph
lies below the local graph. The packet and the directory are separate from these inputs. -/
structure ApplyRowFit (w : ℕ) (G W : Graph) (Ms : List (List (ℕ × ℕ))) (emb : ℕ → List ℕ)
    (i mt tb tmp g ends vs P dir out : ℕ) : Prop where
  row : i < Ms.length
  parent : ends + 2 * G.m ≤ g
  graphMatch : g + 2 + 2 * (W.m + (Ms.getD i []).length) ≤ mt
  graphWalk : g + 2 + 2 * (W.m + (Ms.getD i []).length) ≤ tb
  matchPacket : mt + (csrList Ms.length (matchingRowWords Ms)).length ≤ tmp
  walkPacket : tb + (csrList Ms.flatten.length emb).length ≤ tmp
  packet : tmp + 4 ≤ dir
  scratch : vs ≤ P
  walks : WalkRowFit w (matchingWalkRow Ms emb i) G tb (matchingRowBase Ms mt i) ends vs P dir out

/-- Unchanged cells lie outside the graph append, coordinates packet and walk write. -/
def ApplyRowKept (oldEnd cap tmp cnt vs P dir out g a : ℕ) : Prop :=
  a ≠ g + 1 ∧ (a < oldEnd ∨ cap ≤ a) ∧ (a < tmp ∨ tmp + 4 ≤ a) ∧
    WalkRowKept cnt vs P dir out a

/-- The result agrees with the two model updates for this matching row. -/
def buildApplyRowContract (w i : ℕ) (G W : Graph) (Ms : List (List (ℕ × ℕ)))
    (emb : ℕ → List ℕ) : Contract :=
  let R := matchingWalkRow Ms emb i
  let es := Ms.getD i []
  { pre := fun args mem => ∃ mt tb tmp g off ends vs P dir out,
      args = [mt, tb, Ms.length, i, tmp, g, off, ends, vs, P, dir, out] ∧
      ApplyRowFit w G W Ms emb i mt tb tmp g ends vs P dir out ∧
      GraphAt mem g W ∧ G.IsValid ∧
      ListAt mem mt (csrList Ms.length (matchingRowWords Ms)) ∧
      ListAt mem tb (csrList Ms.flatten.length emb) ∧
      ListAt mem ends (G.edges.flatMap fun e => [e.1, e.2]) ∧
      (∀ e ∈ es, off ≤ e.1 ∧ off ≤ e.2 ∧ e.1 < 2 ^ w ∧ e.2 < 2 ^ w) ∧
      (∀ j < R.count, R.u j < G.n ∧ IsEdgeWalk G.edges (R.u j) (R.v j) (R.raw j)) ∧
      ZeroFrom mem out ∧ (∀ a < G.n, mem (P + a) = 0)
    post := fun args mem v mem' => ∃ mt tb tmp g off ends vs P dir out,
      args = [mt, tb, Ms.length, i, tmp, g, off, ends, vs, P, dir, out] ∧
      GraphAt mem' g (appendGameMatching W off es) ∧
      v = R.cursor out R.count ∧ ZeroFrom mem' v ∧
      (∀ a, ApplyRowKept (g + 2 + 2 * W.m) (g + 2 + 2 * (W.m + es.length))
        tmp R.count vs P dir out g a → mem' a = mem a) ∧ (∀ a < G.n, mem' (P + a) = 0) ∧
      ∀ j < R.count, mem' (dir + j) = R.cursor out j ∧
        SeqAt mem' (R.cursor out j) (erase G.edges (R.u j) (R.raw j))
    cost := fun _ _ => rangeCost (fun j => 136 * (R.raw j).length + 330) 0 R.count +
      47 * R.count + 250 }

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The two writes consume the same router row. Walks and new graph edges therefore
have the same order. -/
theorem buildApplyRowProc_meetsContract {w i f fRead fAppend fEnds fWalks fWalk : ℕ}
    {G W : Graph} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ} {p : Program}
    (hf : p.procs[f]? = some (buildApplyRowProc fRead fAppend fWalks))
    (hRead : p.procs[fRead]? = some buildMatchReadProc)
    (hAppend : p.procs[fAppend]? = some (buildGameAppendProc fEnds))
    (hEnds : p.procs[fEnds]? = some buildLocalEndsProc)
    (hWalks : p.procs[fWalks]? = some (buildWalkRowProc fWalk))
    (hWalk : ∀ j < (matchingWalkRow Ms emb i).count,
      MeetsContract w p fWalk (buildStoreWalkContract w G.edges
        ((matchingWalkRow Ms emb i).u j) emb Ms.flatten.length (flatIndex Ms i 0 + j))) :
    MeetsContract w p f (buildApplyRowContract w i G W Ms emb) := by
  refine meetsContract_of_runs hf fun args mem pos ω hArgs hPre => ?_
  obtain ⟨mt, tb, tmp, g, off, ends, vs, P, dir, out, rfl, hFit, hW, hG, hMt, hTb, hE, hOff,
    hR, hZ, hP⟩ := hPre
  let R := matchingWalkRow Ms emb i
  let es := Ms.getD i []
  let src := matchingRowBase Ms mt i
  let cap := g + 2 + 2 * (W.m + es.length)
  have hCapM : cap ≤ mt := hFit.graphMatch
  have hCapT : cap ≤ tb := hFit.graphWalk
  have hCapTmp : cap ≤ tmp := hCapM.trans
    (Nat.le_add_right .. |>.trans hFit.matchPacket)
  have hParent := hFit.parent
  have hPacket := hFit.packet
  have hWF := hFit.walks
  have hDir := hWF.directory
  change dir + R.count ≤ vs at hDir
  have hPos := hWF.positions
  have hScratch := hFit.scratch
  have hOut : tmp + 4 ≤ out := by omega
  have hOutW := hArgs out (by simp)
  have hTmpW : tmp + 4 < 2 ^ w := by omega
  have hSrcLen : src + 2 * es.length ≤ dir := hWF.source
  have hCnt : R.count = es.length := rfl
  have hDirW : dir < 2 ^ w := hArgs _ (by simp)
  have hSrcW : src < 2 ^ w := by omega
  have hRaw : ListAt mem src (es.flatMap fun e => [e.1, e.2]) :=
    (matchingRow_view hFit.row hMt).2.2.2
  have hSrcBelow : src + 2 * es.length ≤ tmp := by
    have hs := csr_end_le Ms.length (matchingRowWords Ms) hFit.row
    have hm := hFit.matchPacket
    have he := (matchingRow_view hFit.row hMt).1
    have hSum := csrList_offset hMt (Nat.le_of_lt hFit.row)
    change mem (mt + i) = 2 * R.first at he
    have hil : (matchingRowWords Ms i).length = 2 * es.length := length_matchingRowWords _ _
    rw [hil, ← hSum, he] at hs
    have hsrc : src = mt + (Ms.length + 1) + 2 * R.first := rfl
    omega
  have hSrcCap : cap ≤ src := by dsimp [src, matchingRowBase]; omega
  have hw0 : 0 < 2 ^ w := Nat.two_pow_pos _
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hTmp₀ : tmp < 2 ^ w := by omega
  have hTmp₁ : tmp + 1 < 2 ^ w := by omega
  have hTmp₂ : tmp + 2 < 2 ^ w := by omega
  have hTmp₃ : tmp + 3 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold buildApplyRowProc
  refine runs_seq_call_le (buildMatchReadProc_meetsContract hRead)
    (vs := [mt, Ms.length, i, tmp]) (by rfl) ?_
    ⟨mt, tmp, rfl, hFit.row, hMt, hFit.matchPacket, hTmpW⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> exact hArgs _ (by simp)
  intro _ mem₁ pos₁ hPost
  obtain ⟨_, _, hEq, hCoords, hF₁⟩ := hPost
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨rfl, rfl⟩ := hEq
  have hC₀ : mem₁ tmp = src := hCoords 0 (by simp [matchReadWords])
  have hC₁ : mem₁ (tmp + 1) = es.length := hCoords 1 (by simp [matchReadWords])
  have hC₂ : mem₁ (tmp + 2) = R.first := hCoords 2 (by simp [matchReadWords])
  have hC₃ : mem₁ (tmp + 3) = R.total := hCoords 3 (by simp [matchReadWords])
  have hW₁ : GraphAt mem₁ g W := WordRAM.ListAt.congr hW fun a _ ha => hF₁ _ (Or.inl (by
    have he : W.encode.length = 2 + 2 * W.m := by
      simp [Graph.encode, Graph.m, List.length_flatMap, Nat.mul_comm]; omega
    rw [he] at ha
    dsimp [cap] at hCapTmp
    omega))
  have hRaw₁ : ListAt mem₁ src (es.flatMap fun e => [e.1, e.2]) :=
    WordRAM.ListAt.congr hRaw fun a _ ha => hF₁ _ (Or.inl (by
      rw [show (es.flatMap fun e => [e.1, e.2]).length = 2 * es.length by
        simp [List.length_flatMap, Nat.mul_comm]] at ha
      omega))
  refine runs_seq_call_le (buildGameAppendProc_meetsContract hAppend hEnds)
    (vs := [g, src, es.length, off]) ?_ ?_
    ⟨g, src, off, rfl, hW₁, hRaw₁, hSrcCap, by omega, hOff⟩ ?_
  · simp [evalArgs, Expr.eval, startState, Function.update, matchCoordExpr, hw0, hw1,
      hTmp₀, hTmp₁, hC₀, hC₁]
  · have hg := hArgs g (by simp)
    have hoff := hArgs off (by simp)
    wram_words
  intro _ mem₂ pos₂ hPost
  obtain ⟨_, _, _, hEq, hW₂, _, hF₂⟩ := hPost
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨rfl, rfl, rfl⟩ := hEq
  have hFrameAbove : ∀ a ≥ cap, mem₂ a = mem₁ a := fun a ha =>
    hF₂ a (by dsimp [cap] at ha; omega) (Or.inr ha)
  have hFrameBelow : ∀ a < g, mem₂ a = mem₁ a := fun a ha => hF₂ a (by omega) (Or.inl (by omega))
  have hTb₂ : ListAt mem₂ tb (csrList R.total R.emb) := WordRAM.ListAt.congr hTb fun a ha hu =>
    (hFrameAbove _ (hCapT.trans ha)).trans (hF₁ _ (Or.inl (hu.trans_le hFit.walkPacket)))
  have hE₂ : ListAt mem₂ ends (G.edges.flatMap fun e => [e.1, e.2]) :=
    WordRAM.ListAt.congr hE fun a _ ha => by
      have hn : (G.edges.flatMap fun e => [e.1, e.2]).length = 2 * G.m := by
        simp [Graph.m, List.length_flatMap, Nat.mul_comm]
      rw [hn] at ha
      exact (hFrameBelow _ (ha.trans_le hParent)).trans (hF₁ _ (Or.inl (by dsimp [cap] at hCapTmp; omega)))
  have hRaw₂ : ListAt mem₂ src (matchingRowWords Ms i) :=
    WordRAM.ListAt.congr hRaw₁ fun a ha _ => hFrameAbove a (hSrcCap.trans ha)
  have hP₂ : ∀ a < G.n, mem₂ (P + a) = 0 := fun a ha => by
    have hA : tmp + 4 ≤ P + a := by omega
    exact (hFrameAbove _ (by omega)).trans ((hF₁ _ (Or.inr hA)).trans (hP a ha))
  have hZ₂ : ZeroFrom mem₂ out := fun a ha =>
    (hFrameAbove _ (by omega)).trans ((hF₁ _ (Or.inr (by omega))).trans (hZ a ha))
  have h0₂ : mem₂ tmp = src := (hFrameAbove _ (by omega)).trans hC₀
  have h1₂ : mem₂ (tmp + 1) = R.count := (hFrameAbove _ (by omega)).trans hC₁
  have h2₂ : mem₂ (tmp + 2) = R.first := (hFrameAbove _ (by omega)).trans hC₂
  have h3₂ : mem₂ (tmp + 3) = R.total := (hFrameAbove _ (by omega)).trans hC₃
  refine runs_seq_call_le (buildWalkRowProc_meetsContract hWalks hWalk)
    (vs := [tb, R.total, R.first, src, ends, vs, P, dir, out, R.count]) ?_ ?_
    ⟨tb, src, ends, vs, P, dir, out, rfl, hWF, hG, hTb₂, hE₂,
      fun j hj => ⟨matchingRow_source hRaw₂ hj, hR j hj⟩, hZ₂, hP₂⟩ ?_
  · simp [evalArgs, Expr.eval, startState, Function.update, matchCoordExpr,
      hw0, hw1, hw2, hw3, hTmp₀, hTmp₁, hTmp₂, hTmp₃, h0₂, h1₂, h2₂, h3₂]
  · have htb := hArgs tb (by simp)
    have hv := hArgs vs (by simp)
    have hP' := hArgs P (by simp)
    have hEnds := hArgs ends (by simp)
    have hIdx : R.first + R.count ≤ R.total := hWF.index
    have hTable : tb + (csrList R.total R.emb).length ≤ dir := hWF.table
    have hTot : R.total < 2 ^ w := by
      have hLen : R.total + 1 ≤ (csrList R.total R.emb).length := by simp [csrList]
      omega
    wram_words
  intro v mem₃ pos₃ hPost
  obtain ⟨_, _, _, _, _, _, _, hEq, hv, hz, hBefore, hp, hD⟩ := hPost
  dsimp only [R] at hEq
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hEq
  refine runs_ret_le (v := v) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
  · refine ⟨mt, tb, tmp, g, off, ends, vs, P, dir, out, rfl, ?_, hv, hz, ?_, hp, hD⟩
    · apply WordRAM.ListAt.congr hW₂
      intro a _ ha
      have hLen (J : Graph) : J.encode.length = 2 + 2 * J.m := by
        simp [Graph.encode, Graph.m, List.length_flatMap, Nat.mul_comm]; omega
      have he : (appendGameMatching W off es).encode.length = 2 + 2 * (W.m + es.length) := by
        rw [hLen]
        simp only [appendGameMatching, Graph.m, List.length_append, List.length_map]
      rw [he] at ha
      exact hBefore a (Or.inl (ha.trans_le (by omega)))
    · intro a ⟨hNe, hGraph, hTmp, hWalkFrame⟩
      exact (hBefore a hWalkFrame).trans ((hF₂ a hNe hGraph).trans (hF₁ a hTmp))
  · simp [buildApplyRowContract, buildMatchReadContract, buildGameAppendContract, buildWalkRowContract,
      Expr.size, argsSize, matchCoordExpr, R, es, matchingWalkRow]
    omega

end MinCostFlow.HierPaths
