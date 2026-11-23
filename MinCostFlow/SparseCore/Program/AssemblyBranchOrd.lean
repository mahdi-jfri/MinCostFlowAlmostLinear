module

public import MinCostFlow.SparseCore.Program.AssemblyBranchOrdLoop

/-!
# Readout `5` of a branch (`AssemblyBranchOrd`)

Readout `5` of a branch writes the output order `tr.outOrder ord` (`OrdListAt`). The program
`asmBrReadOrdStmt` writes a pointer to the order at `h`, the number of vertices of `S_cur` at
`h + 1`, and then one record `[v, len, keys…]` for each vertex `v` of the vertex list of the output
graph. The loop is proved in `AssemblyBranchOrdLoop.lean`. This file adds the steps before and
after the loop, and shows that the records are the order.

* The records name each vertex of `S_cur` once, and the list at `v` is `tr.outOrder ord v`
  (`asmBr_markedList_eq`). A vertex outside `S_cur` is not a root, so its output list is empty
  (`outOrder_eq_nil_of_not_mem`). So the records give the order (`ordOfRecords_map_pair`).
* The records take exactly `ordWordsOn S_cur.V (outOrder ord) - 1` words, so with the pointer
  the readout uses exactly the space that the contract gives it.
* Only the tour changes its cells, and it does not grow them (`AsmBrRepAt.frame_tour`).

The main result is `asmBr_readOrd_runs`, the clause `readOrd_runs` of `AsmBranchAt` for
`asmBrRep`, with cost multiplier `asmBrOrdMul mulT capExp`. It assumes the listing interface
`AsmBrTourListAt` on P7's view of the tour (`asmTourView`), for every order, forest and core
lists (`AsmBrTourListProj`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio MinCostFlow.SparseCore.Program.Read

/-! ## A call on the tour -/

/-- Changing the concrete state of the tour leaves every other part. -/
theorem asmBrPart_setTour {TR : ℕ → ℕ → DSRep AsmTourAbs} {σX : Type} {X : DSRep σX}
    {b : ℕ} {x : AsmBrConc TR X.τ} {tx' : (TR x.vCap x.eCap).τ} :
    ∀ i, i ≠ 4 → asmBrPart X b { x with xTour := tx' } i = asmBrPart X b x i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, h => absurd rfl h
  | 5, _ => rfl
  | _ + 6, _ => rfl

/-- **Calls on the tour keep the branch.** Let the tour hold the same abstract state in `mem'`
with a new concrete state `tx'` whose cells are old cells of the tour, and let `mem'` agree with
`mem` below `h` outside the old cells of the tour. Then `mem'` holds the branch with `tx'`, its
cells do not grow, and its potential changes by the change of the potential of the tour. -/
theorem AsmBrRepAt.frame_tour {depth : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {X : DSRep (AsmBranchAbs depth)} (hX : X.Local)
    {P L capExp b h : ℕ} {a : AsmBranchAbs depth} {x : AsmBrConc TR X.τ}
    {mem mem' : ℕ → ℕ} {tx' : (TR x.vCap x.eCap).τ}
    (hrep : AsmBrRepAt TR X P L capExp b a x mem)
    (hfoot : ∀ c, asmBrFoot X b x c → c < h)
    (hT' : (asmBrTourView TR a x.vCap x.eCap).rep x.tourH x.sTour tx' mem')
    (hfr : ∀ c < h, ¬ (TR x.vCap x.eCap).foot x.tourH x.xTour c → mem' c = mem c)
    (hnew : ∀ c, (TR x.vCap x.eCap).foot x.tourH tx' c →
      (TR x.vCap x.eCap).foot x.tourH x.xTour c) :
    AsmBrRepAt TR X P L capExp b a { x with xTour := tx' } mem' ∧
      (∀ c, asmBrFoot X b { x with xTour := tx' } c → asmBrFoot X b x c) ∧
      asmBrPhi X { x with xTour := tx' } mem' + (TR x.vCap x.eCap).phi x.tourH x.xTour mem =
        asmBrPhi X x mem + (TR x.vCap x.eCap).phi x.tourH tx' mem' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hG, hlsf, hS, hinv, hR, hE, hdom, hemb, hO, -,
    hmarks, hXr, hV, hcap, hLw, hdisj⟩ := hrep
  have hkeep : ∀ i < 6, i ≠ 4 → ∀ c, asmBrPart X b x i c → mem c = mem' c := fun i hi hi4 c hc =>
    (hfr c (hfoot c ⟨i, hi, hc⟩) (hdisj i hi 4 (by decide) hi4 c hc)).symm
  have hrec : ∀ k < ASM_BR_SIZE, mem' (b + k) = mem (b + k) := fun k hk =>
    (hkeep 0 (by decide) (by decide) _ ⟨by omega, by omega⟩).symm
  have hR' := (readRep_local x.vCap x.eCap x.tCap x.L_w P x.readH x.yRead.view x.yRead mem mem'
    (hkeep 1 (by decide) (by decide))).1 hR
  have hE' := (embRep_local x.eCap x.embH x.yEmb.view x.yEmb mem mem'
    (hkeep 2 (by decide) (by decide))).1 hE
  have hO' := (outGraphRep_local x.vCap x.eCap x.outH a.tr.S_cur x.gOut mem mem'
    (hkeep 3 (by decide) (by decide))).1 hO
  have hX' := hX x.restH a x.xRest mem mem' (hkeep 5 (by decide) (by decide))
  obtain ⟨hdisj', hfoot'⟩ := asmBr_disjoint_of_part (k := 4) (hEnd := h)
    (x' := { x with xTour := tx' }) hdisj hfoot asmBrPart_setTour
    (fun c hc => Or.inl (hnew c hc))
  refine ⟨⟨(hrec _ (by decide)).trans h0, (hrec _ (by decide)).trans h1,
    (hrec _ (by decide)).trans h2, (hrec _ (by decide)).trans h3, (hrec _ (by decide)).trans h4,
    (hrec _ (by decide)).trans h5, (hrec _ (by decide)).trans h6, (hrec _ (by decide)).trans h7,
    (hrec _ (by decide)).trans h8, hG, hlsf, hS, hinv, hR', hE', hdom, hemb, hO', hT', hmarks,
    hX'.1 hXr, hV, hcap, hLw, hdisj'⟩, fun c hc => ?_, ?_⟩
  · rcases hfoot' c hc with hc' | hc'
    · exact hc'
    · omega
  · show readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T +
        (TR x.vCap x.eCap).phi x.tourH tx' mem' + X.phi x.restH x.xRest mem' +
        (TR x.vCap x.eCap).phi x.tourH x.xTour mem =
      readPotMul * treePot x.yRead.view.G x.yRead.view.lsf.T +
        (TR x.vCap x.eCap).phi x.tourH x.xTour mem + X.phi x.restH x.xRest mem +
        (TR x.vCap x.eCap).phi x.tourH tx' mem'
    rw [← hX'.2]
    omega

/-! ## Records of a list of vertices -/

/-- The order read from one record `(u, f u)` for each `u` of `l` is `f` on `l` and empty
elsewhere. -/
theorem ordOfRecords_map_pair (f : ℕ → List End) (v : ℕ) :
    ∀ l : List ℕ, ordOfRecords (l.map fun u => (u, f u)) v = if v ∈ l then f v else []
  | [] => by simp [ordOfRecords]
  | u :: l => by
    have ih := ordOfRecords_map_pair f v l
    unfold ordOfRecords at ih ⊢
    by_cases huv : u = v
    · subst huv
      simp
    · have hvu : v ≠ u := Ne.symm huv
      rw [List.map_cons, List.find?_cons_of_neg (by simpa using huv), ih]
      simp [hvu]

/-- **The tour conversion for the listing**: for every order, forest and core lists, procedure `f`
of `p` lists the marked ends on P7's view (`asmTourView`) of P2's tour family `TR`. -/
def AsmBrTourListProj (TR : ℕ → ℕ → DSRep AsmTourAbs) (w : ℕ) (p : Program) (f mul : ℕ) : Prop :=
  ∀ (ord : ℕ → List End) (rf : RootedForest) (cord : ℕ → List End),
    AsmBrTourListAt (fun vCap eCap => asmTourView (TR vCap eCap) ord rf cord) w p f mul

/-- The cost multiplier of readout `5`, for a listing with multiplier `mulT`. -/
def asmBrOrdMul (mulT capExp : ℕ) : ℕ := 100 + mulT * capExp

/-! ## Readout `5` -/

section Readout

variable {depth w : ℕ} {P L capExp limbMul : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
  {X : DSRep (AsmBranchAbs depth)}

/-- **Readout `5` of a branch** (the clause `readOrd_runs` of `AsmBranchAt`). The readout writes
the output order `tr.outOrder ord` in exactly `ordWordsOn S_cur.V (outOrder ord)` words after a
pointer, and costs at most `asmBrOrdMul mulT capExp · (words + 1) · bundleLogFactor M N`. -/
theorem asmBr_readOrd_runs (hTR : ∀ vCap eCap, (TR vCap eCap).Local) (hX : X.Local)
    {p : Program} {f fList mulT : ℕ} (hp : p.procs[f]? = some (asmBrReadOrdStmt fList))
    (hL : AsmBrTourListProj TR w p fList mulT) :
    ∀ (brH h M N vCap eCap : ℕ) (tr : BundleTreeState depth) (ord : ℕ → List End)
      (x : (asmBrRep TR X P L capExp).τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      tr.m₀ = M → tr.n₀ = N →
      SparseCoreCapHyp capExp limbMul L M N vCap eCap →
      (asmBrRep TR X P L capExp).rep brH ⟨tr, ord, vCap, eCap⟩ x mem →
      (∀ a, (asmBrRep TR X P L capExp).foot brH x a → a < h) →
      brH < 2 ^ w → h < 2 ^ w → ZeroFrom mem h →
      h + (1 + ordWordsOn tr.S_cur.V (tr.outOrder ord)) < 2 ^ w →
      ∃ body, p.procs[f]? = some body ∧ ∃ o st' c x',
        Runs w p ω body (startState [brH, h] mem pos) o st' c ∧
        x'.vCap = x.vCap ∧ x'.eCap = x.eCap ∧ x'.tCap = x.tCap ∧ x'.L_w = x.L_w ∧
        x'.xRest = x.xRest ∧
        (asmBrRep TR X P L capExp).rep brH ⟨tr, ord, vCap, eCap⟩ x' st'.mem ∧
        (∃ words, OrdListAt st'.mem (st'.mem h) (tr.outOrder ord) words ∧
          words ≤ ordWordsOn tr.S_cur.V (tr.outOrder ord)) ∧
        (asmBrRep TR X P L capExp).Respects ((asmBrRep TR X P L capExp).foot brH x) h
          (1 + ordWordsOn tr.S_cur.V (tr.outOrder ord)) mem o.value brH x' st'.mem ∧
        c + (asmBrRep TR X P L capExp).phi brH x' st'.mem ≤
          asmBrOrdMul mulT capExp * (ordWordsOn tr.S_cur.V (tr.outOrder ord) + 1) *
            bundleLogFactor M N + (asmBrRep TR X P L capExp).phi brH x mem := by
  intro brH h M N vCap eCap tr ord x mem pos ω hM hN _ hrep hfoot _ hh hz hroom
  have hrepA : AsmBrRepAt TR X P L capExp brH ⟨tr, ord, vCap, eCap⟩ x mem := hrep
  have hfootA : ∀ c, asmBrFoot X brH x c → c < h := hfoot
  have hrec := asmBr_record_lt hfootA
  obtain ⟨-, -, h2, h3, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, hT, hmarks, -, hV, hcap, -,
    hdisj⟩ := id hrepA
  obtain ⟨hOh, -, hdyn⟩ := hO
  obtain ⟨-, hVlt, -, hvc, -, hn, -, -, ⟨vL, hvLlen, hvLnd, hvLmem, hvLat, -⟩, -⟩ := hdyn
  have hvLmem' : ∀ v, v ∈ vL ↔ v ∈ tr.S_cur.V := hvLmem
  have hV' : tr.S_cur.V = tr.cs.RF.R := hV
  have hw : 1 < 2 ^ w := by simp only [ASM_BR_SIZE] at hrec; omega
  -- The words of the records.
  set out := tr.outOrder ord with hout
  set W := ordRecordsWords (vL.map fun v => (v, out v)) with hW
  have hVeq : tr.S_cur.V = vL.toFinset := by
    ext v
    rw [List.mem_toFinset, hvLmem']
  have hwords : ordWordsOn tr.S_cur.V out = 1 + W := by
    unfold ordWordsOn
    rw [hVeq, List.sum_toFinset _ hvLnd, hW]
    simp [ordRecordsWords, Function.comp_def]
  rw [hwords] at hroom ⊢
  -- The cells of the output graph lie below `h` and outside the tour.
  have hvLle : vL.length ≤ x.vCap := by
    rw [← List.toFinset_card_of_nodup hvLnd]
    calc vL.toFinset.card ≤ (Finset.range x.vCap).card :=
          Finset.card_le_card fun v hv => Finset.mem_range.mpr
            (hVlt v ((hvLmem' v).mp (List.mem_toFinset.mp hv)))
      _ = x.vCap := Finset.card_range _
  have hgpart : ∀ k < dynGraphSize x.vCap x.eCap, asmBrPart X brH x 3 (x.gOut + k) :=
    fun k hk => Or.inr ⟨by omega, by omega⟩
  have hgcell : ∀ k < dynGraphSize x.vCap x.eCap, x.gOut + k < h := fun k hk =>
    hfootA _ ⟨3, by decide, hgpart k hk⟩
  have hgtour : ∀ k < dynGraphSize x.vCap x.eCap,
      ¬ (TR x.vCap x.eCap).foot x.tourH x.xTour (x.gOut + k) := fun k hk hf =>
    hdisj 3 (by decide) 4 (by decide) (by decide) _ (hgpart k hk) hf
  have hL' := hL ord tr.cs.lsf.F (outCoreOrder tr ord)
  have htourLt : x.tourH < h := hfootA _ ⟨4, by decide, hL'.handle_foot _ _ _ _⟩
  have H : AsmBrOrdHyp (asmBrTourView TR ⟨tr, ord, vCap, eCap⟩ x.vCap x.eCap) w h x.gOut x.vCap
      x.tourH vL out x.sTour mem x.xTour :=
    { vl := fun j hj => hvLat j hj
      vlCell := fun j hj => by
        have hk : 4 + x.vCap + j < dynGraphSize x.vCap x.eCap := by
          unfold dynGraphSize; omega
        refine ⟨?_, ?_⟩
        · have := hgcell _ hk; omega
        · have := hgtour _ hk
          rwa [show x.gOut + (4 + x.vCap + j) = x.gOut + 4 + x.vCap + j by omega] at this
      vlt := fun v hv => hVlt v ((hvLmem' v).mp hv)
      marked := asmBr_markedList_eq (tr := tr) (ord := ord) hmarks
      footLt := fun a ha => hfootA a ⟨4, by decide, ha⟩
      tourLt := by omega
      room := by omega }
  -- The steps before the loop.
  have hg2 : x.gOut + 2 < h := hgcell 2 (by unfold dynGraphSize; omega)
  have hmn : mem (x.gOut + 2) = vL.length := by rw [hvLlen]; exact hn
  set st0 := startState [brH, h] mem pos with hst0
  have r1 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 0) (.const ASM_BR_OUT)))) st0 .normal
      { st0 with regs := Function.update st0.regs 2 x.outH } 5 :=
    runs_assign_iff.mpr ⟨x.outH, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (v := brH) (by simp [hst0, startState])) (Expr.eval_const (by
        simp only [ASM_BR_OUT, ASM_BR_SIZE] at hrec ⊢; omega)) (by
        simp only [ASM_BR_OUT, ASM_BR_SIZE] at hrec ⊢; omega)) (by simpa [hst0, startState]
        using h2), rfl, rfl, rfl⟩
  set st1 := { st0 with regs := Function.update st0.regs 2 x.outH } with hst1
  have r2 : Runs w p ω (.assign 3 (.load (.reg 2))) st1 .normal
      { st1 with regs := Function.update st1.regs 3 x.gOut } 3 :=
    runs_assign_iff.mpr ⟨x.gOut, Expr.eval_load_of_eq
      (Expr.eval_reg_of_eq (v := x.outH) (by simp [hst1]))
      (by simpa [hst1, hst0, startState] using hOh), rfl, rfl, rfl⟩
  set st2 := { st1 with regs := Function.update st1.regs 3 x.gOut } with hst2
  have r3 : Runs w p ω (.assign 4 (.load (.reg 3))) st2 .normal
      { st2 with regs := Function.update st2.regs 4 x.vCap } 3 :=
    runs_assign_iff.mpr ⟨x.vCap, Expr.eval_load_of_eq
      (Expr.eval_reg_of_eq (v := x.gOut) (by simp [hst2]))
      (by simpa [hst2, hst1, hst0, startState, dgVCapOff] using hvc), rfl, rfl, rfl⟩
  set st3 := { st2 with regs := Function.update st2.regs 4 x.vCap } with hst3
  have r4 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 3) (.const 2)))) st3 .normal
      { st3 with regs := Function.update st3.regs 5 vL.length } 5 :=
    runs_assign_iff.mpr ⟨vL.length, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (v := x.gOut) (by simp [hst3, hst2])) (Expr.eval_const (by omega))
      (by omega))
      (by simpa [hst3, hst2, hst1, hst0, startState] using hmn), rfl, rfl, rfl⟩
  set st4 := { st3 with regs := Function.update st3.regs 5 vL.length } with hst4
  have r5 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const ASM_BR_TOUR)))) st4 .normal
      { st4 with regs := Function.update st4.regs 6 x.tourH } 5 :=
    runs_assign_iff.mpr ⟨x.tourH, Expr.eval_load_of_eq (Expr.eval_add
      (Expr.eval_reg_of_eq (v := brH) (by simp [hst4, hst3, hst2, hst1, hst0, startState]))
      (Expr.eval_const (by simp only [ASM_BR_TOUR, ASM_BR_SIZE] at hrec ⊢; omega))
      (by simp only [ASM_BR_TOUR, ASM_BR_SIZE] at hrec ⊢; omega))
      (by simpa [hst4, hst3, hst2, hst1, hst0, startState] using h3), rfl, rfl, rfl⟩
  set st5 := { st4 with regs := Function.update st4.regs 6 x.tourH } with hst5
  have h1₅ : st5.regs 1 = h := by simp [hst5, hst4, hst3, hst2, hst1, hst0, startState]
  have r6 : Runs w p ω (.store (.reg 1) (.bin .add (.reg 1) (.const 1))) st5 .normal
      { st5 with mem := Function.update st5.mem h (h + 1) } 5 :=
    runs_store_iff.mpr ⟨h, h + 1, Expr.eval_reg_of_eq h1₅, Expr.eval_add
      (Expr.eval_reg_of_eq h1₅) (Expr.eval_const hw) (by omega), rfl, rfl, rfl⟩
  set st6 := { st5 with mem := Function.update st5.mem h (h + 1) } with hst6
  have h1₆ : st6.regs 1 = h := h1₅
  have h5₆ : st6.regs 5 = vL.length := by simp [hst6, hst5, hst4]
  have r7 : Runs w p ω (.store (.bin .add (.reg 1) (.const 1)) (.reg 5)) st6 .normal
      { st6 with mem := Function.update st6.mem (h + 1) vL.length } 5 :=
    runs_store_iff.mpr ⟨h + 1, vL.length, Expr.eval_add (Expr.eval_reg_of_eq h1₆)
      (Expr.eval_const hw) (by omega), Expr.eval_reg_of_eq h5₆, rfl, rfl, rfl⟩
  set st7 := { st6 with mem := Function.update st6.mem (h + 1) vL.length } with hst7
  have r8 : Runs w p ω (.assign 7 (.bin .add (.reg 1) (.const 2))) st7 .normal
      { st7 with regs := Function.update st7.regs 7 (h + 2) } 4 :=
    runs_assign_iff.mpr ⟨h + 2, Expr.eval_add (Expr.eval_reg_of_eq h1₆)
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  set st8 := { st7 with regs := Function.update st7.regs 7 (h + 2) } with hst8
  have r9 : Runs w p ω (.assign 8 (.const 0)) st8 .normal
      { st8 with regs := Function.update st8.regs 8 0 } 2 :=
    runs_assign_iff.mpr ⟨0, Expr.eval_const (by omega), rfl, rfl, rfl⟩
  set st9 := { st8 with regs := Function.update st8.regs 8 0 } with hst9
  -- The state before the loop.
  have hmem9 : st9.mem = Function.update (Function.update mem h (h + 1)) (h + 1) vL.length := rfl
  have hmem9' : ∀ a < h, st9.mem a = mem a := fun a ha => by
    rw [hmem9, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hT9 := asmBrTourView_keep hTR ⟨tr, ord, vCap, eCap⟩ (s := x.sTour) fun a ha =>
    (hmem9' a (hfootA a ⟨4, by decide, ha⟩)).symm
  have hinv0 : AsmBrOrdInv (asmBrTourView TR ⟨tr, ord, vCap, eCap⟩ x.vCap x.eCap) h x.gOut x.vCap
      x.tourH vL out x.sTour mem x.xTour 0 x.xTour st9 := by
    refine ⟨Nat.zero_le _, by simp [hst9, hst8, hst7, hst6, hst5, hst4, hst3, hst2],
      by simp [hst9, hst8, hst7, hst6, hst5, hst4, hst3],
      by simp [hst9, hst8, hst7, hst6, hst5, hst4], by simp [hst9, hst8, hst7, hst6, hst5],
      by simp [hst9, hst8, ordRecordsWords],
      by simp [hst9], hT9.1 hT, fun a ha => ha, fun a ha _ => hmem9' a ha, ?_, ?_, ?_, ?_⟩
    · intro a ha
      have h7₉ : st9.regs 7 = h + 2 := by simp [hst9, hst8]
      rw [h7₉] at ha
      rw [hmem9, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hz a (by omega)
    · rw [hmem9, Function.update_of_ne (by omega), Function.update_self]
    · rw [hmem9, Function.update_self]
    · simp [AsmBrRecsAt]
  -- The loop and the return.
  obtain ⟨st10, cL, tx', hloop, hinvN, hcostL⟩ :=
    asmBrOrd_loop_runs hL' (asmTourView_local (hTR x.vCap x.eCap) _ _ _) (ω := ω) hw H hinv0
  obtain ⟨-, -, -, -, -, h7N, -, hTN, hsubN, hfrN, hzN, hmhN, hmh1N, hrecsN⟩ := hinvN
  rw [List.take_length] at h7N hrecsN
  rw [← hW] at h7N
  rw [h7N] at hzN
  have r11 : Runs w p ω (.ret (.reg 7)) st10 (.returned (h + 2 + W)) st10 2 :=
    runs_ret_iff.mpr ⟨h + 2 + W, Expr.eval_reg_of_eq h7N, rfl, rfl, rfl⟩
  obtain ⟨c, hrunAll, hc⟩ : ∃ c, Runs w p ω (asmBrReadOrdStmt fList) st0
      (.returned (h + 2 + W)) st10 c ∧ c ≤ cL + 60 :=
    ⟨_, runs_seq_iff.mpr (Or.inr ⟨st1, _, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨st2, _, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨st3, _, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨st4, _, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨st5, _, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨st6, _, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨st7, _, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨st8, _, _, r8,
      runs_seq_iff.mpr (Or.inr ⟨st9, _, _, r9,
      runs_seq_iff.mpr (Or.inr ⟨st10, _, _, hloop, r11, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩
  -- The branch after the readout.
  obtain ⟨hrep', hfoot', hphi'⟩ := AsmBrRepAt.frame_tour (h := h) hX hrepA hfootA hTN
    (fun c hc hn => hfrN c hc hn) hsubN
  -- The records are the order.
  have hread : readOrdRecordsAt st10.mem (st10.mem h) = vL.map fun v => (v, out v) := by
    rw [hmhN]
    unfold readOrdRecordsAt
    rw [hmh1N, show h + 1 + 1 = h + 2 by omega]
    have := hrecsN.readOrdRecords_eq
    rwa [List.length_map] at this
  refine ⟨_, hp, .returned (h + 2 + W), st10, c, { x with xTour := tx' }, hrunAll, rfl, rfl,
    rfl, rfl, rfl, hrep',
    ⟨1 + W, ⟨?_, ?_, ?_⟩, le_rfl⟩,
    ⟨by simp only [Outcome.value]; omega, by simp only [Outcome.value]; omega,
      by simpa [Outcome.value] using hzN, fun a ha hn => hfrN a ha fun hf => hn ⟨4, by decide, hf⟩,
      fun a ha => Or.inl (hfoot' a ha)⟩, ?_⟩
  · rw [hread, List.map_map]
    simpa [Function.comp_def] using hvLnd
  · funext v
    unfold readOrd
    rw [hread, ordOfRecords_map_pair]
    split_ifs with hv
    · rfl
    · exact (outOrder_eq_nil_of_not_mem tr ord fun hR => hv ((hvLmem' v).mpr (hV' ▸ hR))).symm
  · rw [hread]
  · -- The cost.
    show c + asmBrPhi X { x with xTour := tx' } st10.mem ≤ _ + asmBrPhi X x mem
    have hphi9 : (asmTourView (TR x.vCap x.eCap) ord tr.cs.lsf.F (outCoreOrder tr ord)).phi
        x.tourH x.xTour st9.mem = (TR x.vCap x.eCap).phi x.tourH x.xTour mem := hT9.2.symm
    rw [hphi9] at hcostL
    change cL + (TR x.vCap x.eCap).phi x.tourH tx' st10.mem ≤ _ at hcostL
    have hsum := asmBrOrd_sum_le mulT x.eCap out vL
    rw [← hW] at hsum
    have hcap' : x.eCap + 2 ≤ (M + N + 2) ^ capExp := by
      have : x.vCap + x.eCap + 2 ≤ (tr.m₀ + tr.n₀ + 2) ^ capExp := hcap
      rw [hM, hN] at this
      omega
    have hlg : ordStoreLog x.eCap ≤ capExp * bundleLogFactor M N :=
      le_trans (ordStoreLog_le_of_cap hcap')
        (Nat.mul_le_mul_left _ (logStep_le_bundleLogFactor M N))
    have hb : 1 ≤ bundleLogFactor M N :=
      le_trans (by omega) (logStep_le_bundleLogFactor M N)
    have e1 : (29 + mulT * ordStoreLog x.eCap) * W ≤
        (29 + mulT * (capExp * bundleLogFactor M N)) * W :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlg) _)
    have e2 : (29 + mulT * (capExp * bundleLogFactor M N)) * W + 64 ≤
        asmBrOrdMul mulT capExp * (1 + W + 1) * bundleLogFactor M N := by
      unfold asmBrOrdMul
      have hWb : W ≤ W * bundleLogFactor M N := Nat.le_mul_of_pos_right W hb
      have q1 : (29 + mulT * (capExp * bundleLogFactor M N)) * W =
          29 * W + mulT * capExp * (W * bundleLogFactor M N) := by ring
      have q2 : (100 + mulT * capExp) * (1 + W + 1) * bundleLogFactor M N =
          100 * (W * bundleLogFactor M N) + 200 * bundleLogFactor M N +
            mulT * capExp * (W * bundleLogFactor M N) +
            2 * (mulT * capExp * bundleLogFactor M N) := by ring
      rw [q1, q2]
      omega
    omega

end Readout

end MinCostFlow.SparseCore.Program
