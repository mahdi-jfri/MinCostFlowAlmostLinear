module

public import MinCostFlow.SparseCore.Program.AssemblyBranchStepReadModel
public import MinCostFlow.SparseCore.Program.AssemblyBranchStepModel
public import MinCostFlow.SparseCore.Program.AssemblyBranchReadSame
public import MinCostFlow.SparseCore.Program.ReadSpec
import MinCostFlow.SparseCore.Program.OutEditsValid
import MinCostFlow.SparseCore.CompLSFBridge
import MinCostFlow.SparseCore.LSFInsertNonTree

/-!
# The third call of the step of a branch: P10's update (`AssemblyBranchStepRead`)

The step program of a branch (`asmBrStepStmt`, `AssemblyBranchStepIface.lean`) calls the update of
the readout data (piece P10, `ReadBranchAt.step`) third. It passes the input batch `U`, the change
record `c` of P4 for the branch, and the output batch `U_S` that P7's step wrote. This file shows
that the call runs and leaves the readout data holding the view of the model after the step
(`asmBr_readStep_runs`):
* the preconditions of P10 on the model come from the facts of the old and the new state: `U_S` is
  valid and fits the caps (`AssemblyBranchStepReadModel.lean`), no inserted edge is a tree edge
  when it is inserted (`bundleTree_insert_not_mem_T_at`), and the data after the update meet
  `ReadView.Inv` (`readView_step_inv`);
* P10 leaves the view `v.step U c U_S`, whose LSF is the LSF of the model up to `SameLSF`
  (`lsfViewStep_sameLSF`), so the data hold the view of the model with the same cells and the same
  potential (`readRep_of_sameLSF`).

P10 reads the words of `U_S`, so it asks that they are words. P7's step does not say so. Every word
of an encoded batch is a tag, a name of a vertex or an edge, or a count of edges, so the words are
below `2 ^ w` when the names fit the caps (`asmBr_batchAt_words_lt`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Read

/-! ## The words of an encoded batch -/

/-- A list of numbers below `B` written at `a` gives words below `B` at its cells. -/
private theorem listAt_lt {mem : ℕ → ℕ} {a B : ℕ} {l : List ℕ} (hl : ListAt mem a l)
    (hB : ∀ x ∈ l, x < B) : ∀ i < l.length, mem (a + i) < B := fun i hi => by
  rw [hl i hi]; exact hB _ (List.getElem_mem hi)

/-- A list without repeats of edges of a graph whose edges are below `eCap` has length at most
`eCap`. -/
private theorem nodup_length_le {l : List ℕ} {E : Finset ℕ} {eCap : ℕ} (hnd : l.Nodup)
    (hsub : ∀ e ∈ l, e ∈ E) (hE : ∀ e ∈ E, e < eCap) : l.length ≤ eCap := by
  rw [← List.toFinset_card_of_nodup hnd]
  calc l.toFinset.card ≤ (Finset.range eCap).card :=
        Finset.card_le_card fun e he =>
          Finset.mem_range.mpr (hE e (hsub e (List.mem_toFinset.mp he)))
    _ = eCap := Finset.card_range eCap

/-- **The words of an encoded batch body are below `B`**, when the vertices of the graph after the
batch are below `B`, the edges of the graph and the inserted edges are below `eCap < B`, and
`4 ≤ B`. Each word is a tag below `4`, a vertex of some graph of the batch (these grow, so they
are vertices of the last graph), an edge of some graph of the batch, or the number of moved ends of
a split, which is at most the number of edges. -/
theorem asmBr_batchBodyAt_words_lt {mem : ℕ → ℕ} {B eCap : ℕ} (heB : eCap < B) (h4 : 4 ≤ B) :
    ∀ (U : List Update) (G : MGraph) (a n : ℕ), BatchBodyAt mem a G U n → G.BatchIsValid U →
      (∀ x ∈ (G.applyBatch U).V, x < B) → (∀ e ∈ G.E, e < eCap) →
      (∀ e x y, Update.insert e x y ∈ U → e < eCap) → ∀ i < n, mem (a + i) < B
  | [], _, _, n, hB, _, _, _, _ => by
    intro i hi
    have : n = 0 := hB
    omega
  | u :: U, G, a, n, hB, hval, hV, hE, hins => by
    obtain ⟨len, hlen, hu, hrest⟩ := hB
    have hVu : ∀ x ∈ (G.applyUpdate u).V, x < B := fun x hx =>
      hV x (V_subset_applyBatch _ U hx)
    have hVG : ∀ x ∈ G.V, x < B := fun x hx => by
      apply hVu
      cases u <;> simp only [MGraph.applyUpdate] <;>
        first | exact hx | exact Finset.mem_insert_of_mem hx
    have hEu : ∀ e ∈ (G.applyUpdate u).E, e < eCap := by
      intro e he
      cases u with
      | insert e₀ x y =>
        rcases Finset.mem_insert.mp he with rfl | he
        · exact hins _ x y List.mem_cons_self
        · exact hE e he
      | delete e₀ => exact hE e (Finset.mem_erase.mp he).2
      | split v v' St Sh => exact hE e he
    have hhead : ∀ i < len, mem (a + i) < B := by
      cases u with
      | insert e x y =>
        obtain ⟨rfl, hl⟩ := hu
        obtain ⟨-, hx, hy⟩ := hval.1
        refine listAt_lt hl ?_
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · omega
        · exact lt_trans (hins _ x y List.mem_cons_self) heB
        · exact hVG _ hx
        · exact hVG _ hy
      | delete e =>
        obtain ⟨rfl, hl⟩ := hu
        refine listAt_lt hl ?_
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · omega
        · exact lt_trans (hE _ hval.1) heB
      | split v v' St Sh =>
        have hv : v < B := hVG v hval.1.1
        have hv' : v' < B := hVu v' (Finset.mem_insert_self _ _)
        have hcnt : ∀ (L : List ℕ), L.Nodup → (∀ e ∈ L, e ∈ G.E) → L.length < B ∧ ∀ e ∈ L, e < B :=
          fun L hnd hsub => ⟨lt_of_le_of_lt (nodup_length_le hnd hsub hE) heB,
            fun e he => lt_trans (hE e (hsub e he)) heB⟩
        rcases hu with ⟨Lt, Lh, hnt, hnh, hmt, hmh, rfl, hl⟩ | ⟨Lt, Lh, hnt, hnh, hmt, hmh, rfl, hl⟩
        · obtain ⟨ht1, ht2⟩ := hcnt Lt hnt fun e he => ((hmt e).mp he).1
          obtain ⟨hh1, hh2⟩ := hcnt Lh hnh fun e he => ((hmh e).mp he).1
          have hL5 : ([2, v, v', Lt.length, Lh.length] ++ Lt ++ Lh).length =
              5 + Lt.length + Lh.length := by
            simp only [List.length_append, List.length_cons, List.length_nil]
          have hall : ∀ z ∈ [2, v, v', Lt.length, Lh.length] ++ Lt ++ Lh, z < B := by
            intro z hz
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with (((rfl | rfl | rfl | rfl | rfl) | hz) | hz)
            · omega
            · exact hv
            · exact hv'
            · exact ht1
            · exact hh1
            · exact ht2 z hz
            · exact hh2 z hz
          exact fun i hi => listAt_lt hl hall i (by omega)
        · obtain ⟨ht1, ht2⟩ := hcnt Lt hnt fun e he => ((hmt e).mp he).1
          obtain ⟨hh1, hh2⟩ := hcnt Lh hnh fun e he => ((hmh e).mp he).1
          have hL5 : ([3, v, v', Lt.length, Lh.length] ++ Lt ++ Lh).length =
              5 + Lt.length + Lh.length := by
            simp only [List.length_append, List.length_cons, List.length_nil]
          have hall : ∀ z ∈ [3, v, v', Lt.length, Lh.length] ++ Lt ++ Lh, z < B := by
            intro z hz
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
            rcases hz with (((rfl | rfl | rfl | rfl | rfl) | hz) | hz)
            · omega
            · exact hv
            · exact hv'
            · exact ht1
            · exact hh1
            · exact ht2 z hz
            · exact hh2 z hz
          exact fun i hi => listAt_lt hl hall i (by omega)
    have htail := asmBr_batchBodyAt_words_lt heB h4 U (G.applyUpdate u) (a + len) (n - len) hrest
      hval.2 hV hEu (fun e x y h => hins e x y (List.mem_cons_of_mem _ h))
    intro i hi
    by_cases hil : i < len
    · exact hhead i hil
    · have := htail (i - len) (by omega)
      rwa [show a + len + (i - len) = a + i by omega] at this

/-- An encoded batch body has at least one word per update. -/
theorem asmBr_batchBodyAt_length_le {mem : ℕ → ℕ} :
    ∀ (U : List Update) (G : MGraph) (a n : ℕ), BatchBodyAt mem a G U n → U.length ≤ n
  | [], _, _, _, _ => Nat.zero_le _
  | u :: U, G, a, n, ⟨len, hlen, hu, hrest⟩ => by
    have h1 := asmBr_batchBodyAt_length_le U _ _ _ hrest
    have h2 : 1 ≤ len := by
      cases u with
      | insert => have := hu.1; omega
      | delete => have := hu.1; omega
      | split => rcases hu with ⟨_, _, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, _, rfl, _⟩ <;> omega
    simp only [List.length_cons]
    omega

/-- **The words of an encoded batch are below `B`**: the header is the number of updates, which
is below the number of words, and the body is `asmBr_batchBodyAt_words_lt`. -/
theorem asmBr_batchAt_words_lt {mem : ℕ → ℕ} {B eCap a n : ℕ} {G : MGraph} {U : List Update}
    (hB : BatchAt mem a G U n) (hval : G.BatchIsValid U) (heB : eCap < B) (h4 : 4 ≤ B)
    (hnB : n ≤ B) (hV : ∀ x ∈ (G.applyBatch U).V, x < B) (hE : ∀ e ∈ G.E, e < eCap)
    (hins : ∀ e x y, Update.insert e x y ∈ U → e < eCap) : ∀ i < n, mem (a + i) < B := by
  obtain ⟨h1, h0, hbody⟩ := hB
  have hlen := asmBr_batchBodyAt_length_le U G _ _ hbody
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [Nat.add_zero, h0]; omega
  · have := asmBr_batchBodyAt_words_lt heB h4 U G (a + 1) (n - 1) hbody hval hV hE hins (i - 1)
      (by omega)
    rwa [show a + 1 + (i - 1) = a + i by omega] at this

/-! ## The call -/

/-- **P10's update runs as the third call of the step.** Let the readout data at `r` hold the view
`y.view` of the branch before the step: the graph `tr.cs.G`, the LSF `tr.cs.lsf` and the output
graph `tr.S_cur`, with `ReadView.Inv`. Let the input batch `U`, the change record `c` of P4 and the
output batch `U_S` of the step lie at `batch`, `chg` and `us`, outside the cells of the data and
below `h`. Then the update of P10 runs and leaves the data holding the view of the model after the
step: the graph and the LSF of `compLSFBatch tr.cs U`, the new output graph, and the pairs of the
update. The view meets `ReadView.Inv`. The cost is the cost of P10's clause against the potential of
the data. -/
theorem asmBr_readStep_runs {w vCap eCap tCap L_w P : ℕ} {SP : DSParams} {cap : ℕ} {p : Program}
    {bR : ℕ} {readIdx : ℕ → ℕ} {fRoot : ℕ} {Q : RootQueryAt w p fRoot} {mul : ℕ}
    (hB : ReadBranchAt (readRep vCap eCap tCap L_w P) w vCap eCap tCap L_w P SP cap p bR readIdx
      fRoot Q mul)
    {depth : ℕ} (impl : SparsifyImpl) {vC eC : ℕ} (r batch words chg us usWords h : ℕ)
    (tr : BundleTreeState depth) (ord : ℕ → List End) (U : List Update) (ed : List OrdEdit)
    (c : LSFChange) (y : ReadConc) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) :
    let ord' := applyOrdEdits ord ed
    let sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify impl
    let info := stepBundleTree sparsify tr U ord ord'
    let v' : ReadView := ⟨info.state.cs.G, info.state.cs.lsf, info.state.S_cur,
      U.foldl pairViewUpdate y.view.num, U.foldl pairViewUpdate y.view.den⟩
    (∀ a ∈ [r, batch, words, chg, us, h], a < 2 ^ w) →
    y.view.G = tr.cs.G → y.view.lsf = tr.cs.lsf → y.view.S = tr.S_cur →
    y.view.Inv vCap eCap tCap →
    (readRep vCap eCap tCap L_w P).rep r y.view y mem →
    (∀ a, readFoot vCap eCap tCap L_w r y a → a < h) → ZeroFrom mem h →
    AsmBrModelFacts impl vC eC tr ord → AsmBrModelFacts impl vCap eCap info.state ord' →
    tr.cs.G.BatchIsValid U → OrderedBatch tr.cs.G U ord ord' →
    BatchAt mem batch tr.cs.G U words → BatchWithinCaps vCap eCap U →
    InputAt w mem (readFoot vCap eCap tCap L_w r y) batch words h →
    LSFChangeAt mem chg c → c.Exact tr.cs.lsf (compLSFBatch tr.cs U).lsf →
    InputAt w mem (readFoot vCap eCap tCap L_w r y) chg c.words h →
    BatchAt mem us tr.S_cur info.U_S usWords →
    us + usWords ≤ h → (∀ i < usWords, ¬ readFoot vCap eCap tCap L_w r y (us + i)) →
    usWords ≤ 2 ^ w → 4 ≤ 2 ^ w → vCap ≤ 2 ^ w → eCap < 2 ^ w →
    h + readSpace mul vCap tCap L_w (words + c.words + usWords) < 2 ^ w →
    ∃ body, p.procs[bR + readIdx 2]? = some body ∧ ∃ o st' cst y',
      Runs w p ω body (startState [r, batch, words, chg, us, usWords, h] mem pos) o st' cst ∧
      (readRep vCap eCap tCap L_w P).rep r v' y' st'.mem ∧ y'.view = v' ∧
      v'.Inv vCap eCap tCap ∧
      h ≤ o.value ∧ o.value ≤ h + readSpace mul vCap tCap L_w (words + c.words + usWords) ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ readFoot vCap eCap tCap L_w r y a → st'.mem a = mem a) ∧
      (∀ a, readFoot vCap eCap tCap L_w r y' a →
        readFoot vCap eCap tCap L_w r y a ∨ (h ≤ a ∧ a < o.value)) ∧
      cst + (readRep vCap eCap tCap L_w P).phi r y' st'.mem ≤
        mul * ((words + usWords + 1) * (L_w + 1) + c.size) +
          (readRep vCap eCap tCap L_w P).phi r y mem := by
  intro ord' sparsify info v' hargs hG hL hS hInv hrep hfoot hz hold hnew hBU hord hBat hcaps hBin
    hC hc hCin hBS hus husF hu2 h4 hvw hew hroom
  -- the model facts of P10's precondition
  have hready := asmBr_outStepReady sparsify hold hnew hBU hord
  have hUSv := stepBundleTree_U_S_valid sparsify hready
  have hSV' : ∀ x ∈ info.state.S_cur.V, x < vCap := by
    rw [hnew.2.2.1.2.1]; exact asmBr_newRoots_lt sparsify hnew
  have hSE' : ∀ e ∈ info.state.S_cur.E, e < eCap := asmBr_newOut_lt sparsify hnew
  have hUScap := stepBundleTree_U_S_withinCaps sparsify hSV' hSE'
  obtain ⟨-, ⟨C_lsst, ℓ₀, hI, -⟩, -⟩ := hold
  obtain ⟨-, ⟨-, -, hI', -⟩, -, -, hSval', -, -, hGV', hGE', -⟩ := hnew
  have hv : y.view = ⟨tr.cs.G, tr.cs.lsf, tr.S_cur, y.view.num, y.view.den⟩ := by
    rw [← hG, ← hL, ← hS]
  have hpairs : ∀ e ∈ tr.cs.G.E, 0 < y.view.den e ∧
      (y.view.num e : ℝ) / y.view.den e = tr.cs.lsf.wstr e := by
    rw [← hG, ← hL]; exact hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hInv' : (y.view.step U c info.U_S).Inv vCap eCap tCap := by
    rw [hv]
    exact readView_step_inv hI hBU hc hpairs hGV' hGE' hInv.2.2.2.1 hSval' hSV' hSE'
  have hins : ∀ k (hk : k < U.length), ∀ e x z, U[k] = Update.insert e x z →
      e ∉ ((U.take k).foldl tViewUpdate y.view.lsf.T).E := by
    rw [hL]; exact bundleTree_insert_not_mem_T_at tr hBU
  -- the words of the output batch
  have hSE : ∀ e ∈ tr.S_cur.E, e < eCap := fun e he => by
    rw [← hS] at he; exact hInv.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
  have hUSw : ∀ i < usWords, mem (us + i) < 2 ^ w :=
    asmBr_batchAt_words_lt hBS hUSv hew h4 hu2 (fun x hx => lt_of_lt_of_le (hSV' x hx) hvw) hSE
      (fun e x z hm => hUScap _ hm)
  have hargs' : ∀ a ∈ [r, batch, words, chg, us, usWords, h], a < 2 ^ w := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · exact hargs _ (by simp)
    · have : a ≤ h := by omega
      exact lt_of_le_of_lt this (hargs h (by simp))
    · exact hargs _ (by simp)
  have hBSin : InputAt w mem ((readRep vCap eCap tCap L_w P).foot r y) us usWords h :=
    ⟨hus, fun i hi => ⟨hUSw i hi, husF i hi⟩⟩
  obtain ⟨body, hbody, o, st', cst, y', hrun, hrep', -, hlo, hhi, hz', hfr, hgrow, hcost⟩ :=
    hB.step r batch words chg us usWords h y.view y U info.U_S c mem pos ω hargs' hrep hfoot hz
      (hG ▸ hBat) (hG ▸ hBU) hcaps hBin hC hCin (hS ▸ hBS) (hS ▸ hUSv) hUScap hBSin hins hInv'
      hroom
  -- the data hold the view of the model
  have hsame : SameLSF (y.view.step U c info.U_S).lsf info.state.cs.lsf := by
    show SameLSF (lsfViewStep y.view.lsf U c) (compLSFBatch tr.cs U).lsf
    rw [hL]; exact lsfViewStep_sameLSF hI hBU hc
  obtain ⟨hrep'', hphi, hft⟩ := readRep_of_sameLSF hrep' hsame
  have hveq : ({ y.view.step U c info.U_S with lsf := info.state.cs.lsf } : ReadView) = v' := by
    rw [hv]
    simp only [ReadView.step, v', info]
    rw [← compLSFBatch_G]
    rfl
  rw [hveq] at hrep'' hphi hft
  have hInvV : v'.Inv vCap eCap tCap := by
    rw [← hveq]
    exact ReadView.Inv.of_sameLSF hInv' hsame
  refine ⟨body, hbody, o, st', cst, { y' with view := v' }, hrun, hrep'', rfl, hInvV, hlo, hhi, hz',
    hfr, fun a ha => hgrow a ((hft a).mp ha), ?_⟩
  rw [hphi]
  exact hcost

end MinCostFlow.SparseCore.Program
