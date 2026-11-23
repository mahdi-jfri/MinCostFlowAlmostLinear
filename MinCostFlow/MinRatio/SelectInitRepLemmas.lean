module

public import MinCostFlow.MinRatio.SolverRep
public import MinCostFlow.MinRatio.SolverLevelCapsInv
import Mathlib.Tactic

/-!
# Representation frame lemmas for select-region initialization (`SelectInitRepLemmas`)

Two helper lemmas for `solverStateRep` used during select-region initialization:
1. `solverStateRep_update_coreTok`: updates a single sparse-core level `j < d` (`coreTok j := y`)
   whose new footprint lies in `[scratch, sc1)` above the existing footprint, preserving
   `solverStateRep.rep` and telescoping `solverStateRep.phi`.
2. `solverStateRep_write_hbCells`: preserves `solverStateRep.rep` and `solverStateRep.phi` when
   writing the two dedicated select-pointer cells `hbCell`, `hbCell + 1` whose tags do not collide
   with any `SolverTagsAt` tag (`1 .. 20 + d`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program

private lemma listAt_agree_init {mem₁ mem₂ : ℕ → ℕ} {base : ℕ} {xs : List ℕ}
    (h : ListAt mem₁ base xs) (hag : ∀ i < xs.length, mem₂ (base + i) = mem₁ (base + i)) :
    ListAt mem₂ base xs := fun i hi => (hag i hi).trans (h i hi)

/-- Core helper: if `mem₂` agrees with `mem₁` on every address with `tok.tag a ∈ [1, 20 + d]`
except possibly a single skipped tag `skipTag ∉ [1, 20]`, and `tok'` preserves all non-`skipTag`
tags and supplies the new `Rcore.rep` whenever `21 + i = skipTag`, then `solverStateRep.rep`
holds on `(tok', mem₂)`. -/
private theorem solverStateRep_of_tag_agree
    {cfg : Alg2Config} {L P m V psi k epsExp drainUnit skipTag : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {root : ℕ} {model : Alg2State cfg} {tok tok' : SolverToken cfg L Rcore}
    {mem₁ mem₂ : ℕ → ℕ}
    (hskip : skipTag = 0 ∨ 21 ≤ skipTag)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem₁)
    (hSameFields :
      tok'.handle = tok.handle ∧ tok'.table = tok.table ∧ tok'.levelsEnd = tok.levelsEnd ∧
      tok'.forward = tok.forward ∧ tok'.inverse = tok.inverse ∧
      tok'.freshCounter = tok.freshCounter ∧ tok'.slots = tok.slots ∧ tok'.names = tok.names ∧
      tok'.slotThresholds = tok.slotThresholds ∧ tok'.edgeThresholds = tok.edgeThresholds ∧
      tok'.edgeRecords = tok.edgeRecords ∧ tok'.offReadyCount = tok.offReadyCount ∧
      tok'.offReadyList = tok.offReadyList ∧ tok'.inOffReady = tok.inOffReady ∧
      tok'.rootGraph = tok.rootGraph ∧ tok'.rootECap = tok.rootECap ∧
      tok'.intCap = tok.intCap ∧ tok'.treeHeap = tok.treeHeap ∧
      tok'.searchSpace = tok.searchSpace ∧ tok'.readSpace = tok.readSpace ∧
      tok'.alphaPtr = tok.alphaPtr ∧ tok'.tree = tok.tree ∧ tok'.trees = tok.trees ∧
      tok'.free = tok.free ∧ tok'.depth = tok.depth ∧ tok'.treeTok = tok.treeTok ∧
      tok'.coreHandle = tok.coreHandle ∧ tok'.termHandle = tok.termHandle ∧
      tok'.vcLast = tok.vcLast ∧ tok'.ecLast = tok.ecLast ∧ tok'.termTok = tok.termTok)
    (hagT : ∀ a v, tok.tag a = v → 1 ≤ v → v ≤ 20 + cfg.P.d → v ≠ skipTag → mem₂ a = mem₁ a)
    (htagKeep : ∀ a v, tok.tag a = v → 1 ≤ v → v ≤ 20 + cfg.P.d → tok'.tag a = v)
    (hOwn' : ∀ a, tok'.tag a ≠ 0 → tok'.owned a)
    (hCore' : ∀ i (_hi : i < cfg.P.d),
      (21 + i = skipTag → Rcore.rep (tok.coreHandle i) (chainLevelOrdAbs model.chain i) (tok'.coreTok i) mem₂ ∧
        ∀ a, Rcore.foot (tok.coreHandle i) (tok'.coreTok i) a → tok'.tag a = 21 + i) ∧
      (21 + i ≠ skipTag → tok'.coreTok i = tok.coreTok i)) :
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok' mem₂ := by
  have htreeLocal := LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC
  have htermLocal := LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast
    4 L P (model.chain.G cfg.P.d).E
  obtain ⟨hrootDir, hdetect, hnum, hchainP, hfreshInv, hfreshTab, hextM, hintCapE,
    hsched, hoffReady, htn, hlctInv, htreeRep, hedgeAcc, hcores, htermH, htermBr,
    htermRep, hwire, htags⟩ := hrep
  obtain ⟨_, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
    t16, t1718, t19, t20, t21⟩ := htags
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31⟩ := hSameFields
  have hAgLow {a v : ℕ} (ht : tok.tag a = v) (hlo : 1 ≤ v) (hhi : v ≤ 20) : mem₂ a = mem₁ a :=
    hagT a v ht hlo (by omega) (by rcases hskip with h | h <;> omega)
  have hmem_et (e : ℕ) (he : e ∈ model.extG.E) :
      mem₂ (tok.edgeThresholds + model.extToInt e) = mem₁ (tok.edgeThresholds + model.extToInt e) :=
    hAgLow (t12 _ (hedgeAcc.1 e he).1) (by omega) (by omega)
  have hmem_er (e : ℕ) (he : e ∈ model.extG.E) :
      mem₂ (tok.edgeRecords + model.extToInt e) = mem₁ (tok.edgeRecords + model.extToInt e) :=
    hAgLow (t13 _ (hedgeAcc.1 e he).1) (by omega) (by omega)
  have htreeRep₂ : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).rep
      tok.treeHeap tok.tree tok.treeTok mem₂ :=
    (htreeLocal tok.treeHeap tok.tree tok.treeTok mem₁ mem₂
      (fun a ha => (hAgLow (t16 a ha) (by omega) (by omega)).symm)).1 htreeRep
  have htermRep₂ : (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
      (model.chain.G cfg.P.d).E).rep tok.termHandle (model.chain.lastK, model.chain.lastLSFs)
      tok.termTok mem₂ :=
    (htermLocal tok.termHandle _ tok.termTok mem₁ mem₂
      (fun a ha => (hAgLow (t19 a ((lastLevelRepresentation_foot_indep_P _ _ _ _ P 0 _ _ _ _).mp ha))
        (by omega) (by omega)).symm)).1 htermRep
  have htermRep₂' : (LastLevelProgram.lastLevelRepresentation tok'.vcLast tok'.ecLast 4 L P
      (model.chain.G cfg.P.d).E).rep tok'.termHandle (model.chain.lastK, model.chain.lastLSFs)
      tok'.termTok mem₂ := by
    rw [f28, f29, f30, f31]; exact htermRep₂
  have ht19' : ∀ a, (LastLevelProgram.lastLevelRepresentation tok'.vcLast tok'.ecLast 4 L 0
      (model.chain.G cfg.P.d).E).foot tok'.termHandle tok'.termTok a → tok'.tag a = 19 := by
    intro a ha; rw [f28, f29, f30, f31] at ha
    exact htagKeep _ 19 (t19 a ha) (by omega) (by omega)
  dsimp only [solverStateRep]
  rw [f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f17, f18,
    f19, f20, f21, f22, f23, f24, f25, f26, f27]
  refine ⟨listAt_agree_init hrootDir (fun j hj => hAgLow (t1 j (by simpa [List.length] using hj)) (by omega) (by omega)),
    listAt_agree_init hdetect (fun j hj => hAgLow (t2 j (by simp [List.length] at hj; omega)) (by omega) (by omega)),
    listAt_agree_init hnum (fun j hj => by
      have h1 : tok.handle + 5 + j = tok.handle + (5 + j) := by omega
      rw [h1]; exact hAgLow (t2 (5 + j) (by simp [List.length] at hj; omega)) (by omega) (by omega)),
    listAt_agree_init hchainP (fun j hj => by
      have h1 : tok.handle + 9 + j = tok.handle + (9 + j) := by omega
      rw [h1]; exact hAgLow (t2 (9 + j) (by simp [List.length] at hj; omega)) (by omega) (by omega)),
    hfreshInv,
    ⟨(hAgLow t6 (by omega) (by omega)).trans hfreshTab.1,
      fun e he => (hAgLow (t7 e he) (by omega) (by omega)).trans (hfreshTab.2.1 e he),
      fun e he => (hAgLow (t8 e he) (by omega) (by omega)).trans (hfreshTab.2.2 e he)⟩,
    hextM, hintCapE,
    ⟨fun i => (hAgLow (t5 i.val (by omega)) (by omega) (by omega)).trans (hsched.1 i),
      fun i hi => by
        have h1 : tok.levelsEnd + (cfg.P.d + 1) + i = tok.levelsEnd + (cfg.P.d + 1 + i) := by omega
        rw [h1]; exact (hAgLow (t5 _ (by omega)) (by omega) (by omega)).trans (by rw [← h1]; exact hsched.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 2 * (cfg.P.d + 1) + i = tok.levelsEnd + (2 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hAgLow (t5 _ (by omega)) (by omega) (by omega)).trans (by rw [← h1]; exact hsched.2.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 3 * (cfg.P.d + 1) + i = tok.levelsEnd + (3 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hAgLow (t5 _ (by omega)) (by omega) (by omega)).trans (by rw [← h1]; exact hsched.2.2.2.1 i hi),
      (hAgLow (t5 (4 * (cfg.P.d + 1)) (by omega)) (by omega) (by omega)).trans hsched.2.2.2.2⟩,
    ?_, htn, hlctInv, htreeRep₂, ?_, ?_,
    by rw [f28]; exact (hAgLow (t4 cfg.P.d (by omega)) (by omega) (by omega)).trans htermH,
    by
      have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by omega
      rw [h1] at htermBr ⊢; exact (hAgLow (t4 _ (by omega)) (by omega) (by omega)).trans htermBr,
    htermRep₂', ?_, ?_⟩
  · obtain ⟨hcnt, hmemL, hdist, hbits, hrev⟩ := hoffReady
    refine ⟨hcnt, fun j hj => ?_, fun j₁ hj₁ j₂ hj₂ hne => ?_, fun e he => ?_, fun e he h1 => ?_⟩
    · rw [hAgLow (t14 j (lt_of_lt_of_le hj hcnt)) (by omega) (by omega)]
      exact ⟨(hmemL j hj).1, (hAgLow (t15 _ (hmemL j hj).1) (by omega) (by omega)).trans (hmemL j hj).2⟩
    · rw [hAgLow (t14 j₁ (lt_of_lt_of_le hj₁ hcnt)) (by omega) (by omega),
          hAgLow (t14 j₂ (lt_of_lt_of_le hj₂ hcnt)) (by omega) (by omega)]
      exact hdist j₁ hj₁ j₂ hj₂ hne
    · rw [hAgLow (t15 e he) (by omega) (by omega)]; exact hbits e he
    · rw [hAgLow (t15 e he) (by omega) (by omega)] at h1
      obtain ⟨j, hj, hje⟩ := hrev e he h1
      exact ⟨j, hj, (hAgLow (t14 j (lt_of_lt_of_le hj hcnt)) (by omega) (by omega)).trans hje⟩
  · refine ⟨fun e he => ?_, fun slot val hslot hpair => ?_⟩
    · obtain ⟨heiCap, hthr, hbranch⟩ := hedgeAcc.1 e he
      refine ⟨heiCap, ?_, ?_⟩
      · rw [hmem_et e he]
        exact hthr.congr (fun j hj => hAgLow ((t1718 e he).1 j hj) (by omega) (by omega))
      · split_ifs at hbranch ⊢ with hin
        · obtain ⟨hsnz, his, hnm, hst, hval⟩ := hbranch
          have hslotLt : mem₁ (tok.slots + model.extToInt e) < 2 * tok.tree.n := by
            unfold isEdgeSlot at his; omega
          rw [hAgLow (t9 _ heiCap) (by omega) (by omega), hmem_et e he]
          exact ⟨hsnz, his,
            (hAgLow (t10 _ hslotLt) (by omega) (by omega)).trans hnm,
            (hAgLow (t11 _ hslotLt) (by omega) (by omega)).trans hst, hval⟩
        · obtain ⟨hs0, val, acc, hrec, hfl, hac, hdet, hpush⟩ := hbranch
          rw [hmem_er e he]
          refine ⟨(hAgLow (t9 _ heiCap) (by omega) (by omega)).trans hs0, val, acc,
            hrec.congr (fun x hxlo hxhi => by
              have hx : x = mem₁ (tok.edgeRecords + model.extToInt e) +
                  (x - mem₁ (tok.edgeRecords + model.extToInt e)) := by omega
              rw [hx]; exact hAgLow ((t1718 e he).2 hin _ (by omega)) (by omega) (by omega)),
            hfl, hac, hdet, fun hnn => (hAgLow (t15 _ heiCap) (by omega) (by omega)).trans (hpush hnn)⟩
    · have hslotLt : slot < 2 * tok.tree.n := by unfold isEdgeSlot at hslot; omega
      obtain ⟨heiCap, hin, hsl, heE, he2i⟩ := hedgeAcc.2 slot val hslot hpair
      rw [hAgLow (t10 slot hslotLt) (by omega) (by omega)]
      exact ⟨heiCap, hin, (hAgLow (t9 _ heiCap) (by omega) (by omega)).trans hsl, heE, he2i⟩
  · intro i hi
    obtain ⟨hh, hbr, hcr⟩ := hcores i hi
    refine ⟨(hAgLow (t4 i (by omega)) (by omega) (by omega)).trans hh,
      by
        have h1 : tok.handle + 18 + (cfg.P.d + 1) + i = tok.handle + 18 + (cfg.P.d + 1 + i) := by omega
        rw [h1] at hbr ⊢; exact (hAgLow (t4 _ (by omega)) (by omega) (by omega)).trans hbr, ?_⟩
    by_cases hEq : 21 + i = skipTag
    · exact ((hCore' i hi).1 hEq).1
    · rw [(hCore' i hi).2 hEq]
      exact (hlocalCore (tok.coreHandle i) _ (tok.coreTok i) mem₁ mem₂
        (fun a ha => (hagT a (21 + i) (t21 i hi a ha) (by omega) (by omega) hEq).symm)).1 hcr
  · obtain ⟨htabW, hrgW, hsubCap, hnsW, hglW⟩ := hwire
    dsimp only [SolverWireInv]
    rw [f2, f7, f8, f11, f15, f16, f17, f22, f23]
    refine ⟨fun j hj => (hAgLow (t3 j hj) (by omega) (by omega)).trans (htabW j hj),
      hrgW.of_agree (fun a h1 h2 => hAgLow (t20 a h1 h2) (by omega) (by omega)), hsubCap,
      ⟨fun ei hei => by
          rw [hAgLow (t9 ei (hsubCap.2 ei hei).1) (by omega) (by omega)]
          have hfwd := hnsW.forward ei hei
          have hslotLt : mem₁ (tok.slots + ei) < 2 * tok.tree.n := by unfold isEdgeSlot at hfwd; omega
          exact ⟨hfwd.1, hfwd.2.1, (hAgLow (t10 _ hslotLt) (by omega) (by omega)).trans hfwd.2.2⟩,
        fun k hk hks => by
          have hkLt : k < 2 * tok.tree.n := by unfold isEdgeSlot at hks; omega
          rw [hAgLow (t10 k hkLt) (by omega) (by omega)]
          obtain ⟨hmem, hslot⟩ := hnsW.inverse k hk hks
          exact ⟨hmem, (hAgLow (t9 _ (hsubCap.2 _ hmem).1) (by omega) (by omega)).trans hslot⟩,
        fun ei hei => by
          rw [hAgLow (t9 ei (hsubCap.2 ei hei).1) (by omega) (by omega)]; exact hnsW.endpoints ei hei⟩,
      fun e he => by
        dsimp only; have hgl := hglW e he; dsimp only at hgl
        have heiCap := (hedgeAcc.1 e he).1
        split_ifs at hgl ⊢ with hin
        · rw [hAgLow (t9 _ heiCap) (by omega) (by omega)]; exact hgl
        · intro val hpa; rw [hmem_er e he] at hpa
          exact hgl val (hpa.congr fun x hlo hhi => by
            have hx : x = mem₁ (tok.edgeRecords + model.extToInt e) +
                (x - mem₁ (tok.edgeRecords + model.extToInt e)) := by omega
            rw [hx]; exact (hAgLow ((t1718 e he).2 hin _ (by omega)) (by omega) (by omega)).symm)⟩
  · dsimp only [SolverTagsAt]
    refine ⟨hOwn',
      fun j hj => htagKeep _ 1 (t1 j hj) (by omega) (by omega),
      fun j hj => by rw [f1]; exact htagKeep _ 2 (t2 j hj) (by omega) (by omega),
      fun j hj => by rw [f2]; exact htagKeep _ 3 (t3 j hj) (by omega) (by omega),
      fun j hj => by rw [f1]; exact htagKeep _ 4 (t4 j hj) (by omega) (by omega),
      fun j hj => by rw [f3]; exact htagKeep _ 5 (t5 j hj) (by omega) (by omega),
      by rw [f6]; exact htagKeep _ 6 t6 (by omega) (by omega),
      fun j hj => by rw [f4]; exact htagKeep _ 7 (t7 j hj) (by omega) (by omega),
      fun j hj => by rw [f5]; rw [f17] at hj; exact htagKeep _ 8 (t8 j hj) (by omega) (by omega),
      fun j hj => by rw [f7]; rw [f17] at hj; exact htagKeep _ 9 (t9 j hj) (by omega) (by omega),
      fun j hj => by rw [f8]; rw [f22] at hj; exact htagKeep _ 10 (t10 j hj) (by omega) (by omega),
      fun j hj => by rw [f9]; rw [f22] at hj; exact htagKeep _ 11 (t11 j hj) (by omega) (by omega),
      fun j hj => by rw [f10]; rw [f17] at hj; exact htagKeep _ 12 (t12 j hj) (by omega) (by omega),
      fun j hj => by rw [f11]; rw [f17] at hj; exact htagKeep _ 13 (t13 j hj) (by omega) (by omega),
      fun j hj => by rw [f13]; rw [f17] at hj; exact htagKeep _ 14 (t14 j hj) (by omega) (by omega),
      fun j hj => by rw [f14]; rw [f17] at hj; exact htagKeep _ 15 (t15 j hj) (by omega) (by omega),
      fun a ha => by rw [f18, f26] at ha; exact htagKeep _ 16 (t16 a ha) (by omega) (by omega),
      fun e he => by
        rw [f10, f11, hmem_et e he, hmem_er e he]
        exact ⟨fun j hj => htagKeep _ 17 ((t1718 e he).1 j hj) (by omega) (by omega),
          fun hin j hj => htagKeep _ 18 ((t1718 e he).2 hin j hj) (by omega) (by omega)⟩,
      ht19',
      fun a h1 h2 => by rw [f15] at h1; rw [f15, f16] at h2; exact htagKeep _ 20 (t20 a h1 h2) (by omega) (by omega),
      fun i hi a ha => by
        rw [f27] at ha
        by_cases hEq : 21 + i = skipTag
        · exact ((hCore' i hi).1 hEq).2 a ha
        · rw [(hCore' i hi).2 hEq] at ha
          exact htagKeep _ (21 + i) (t21 i hi a ha) (by omega) (by omega)⟩

/-- Updating sparse-core level `j < d` (`coreTok j := y`) in place with new footprint inside
`[scratch, sc1)` preserves `solverStateRep.rep` and telescopes `solverStateRep.phi`. -/
theorem solverStateRep_update_coreTok
    {cfg : Alg2Config} {L P m V psi k epsExp drainUnit j scratch sc1 : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {root : ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {y : Rcore.τ} {mem mem' : ℕ → ℕ}
    (hj : j < cfg.P.d)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < scratch)
    (hfr : ∀ a < scratch, ¬ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a → mem' a = mem a)
    (hrepY : Rcore.rep (tok.coreHandle j) (chainLevelOrdAbs model.chain j) y mem')
    (hftY : ∀ a, Rcore.foot (tok.coreHandle j) y a →
      Rcore.foot (tok.coreHandle j) (tok.coreTok j) a ∨ (scratch ≤ a ∧ a < sc1)) :
    let tok' : SolverToken cfg L Rcore :=
      { tok with
        coreTok := Function.update tok.coreTok j y
        owned := fun a => tok.owned a ∨ (scratch ≤ a ∧ a < sc1)
        tag := fun a => if scratch ≤ a ∧ a < sc1 then 21 + j else tok.tag a }
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok' mem' ∧
    (∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a →
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨
        (scratch ≤ a ∧ a < sc1)) ∧
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok' mem' +
        Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem =
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem +
        Rcore.phi (tok.coreHandle j) y mem' := by
  intro tok'
  have htags := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hOwn := htags.1
  have t16 := htags.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have t21 := htags.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hltOwn : ∀ a, tok.owned a → a < scratch := fun a ha => hbelow a (Or.inl ha)
  have hrepOut := solverStateRep_of_tag_agree (skipTag := 21 + j) (tok' := tok') hlocalCore (Or.inr (by omega)) hrep
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun a v ht h1 _ hne => hfr a (hltOwn a (hOwn a (by omega)))
      (fun hc => hne (ht.symm.trans (t21 j hj a hc))))
    (fun a v ht h1 _ => by dsimp only [tok']; rw [ite_eq_right (by have := hltOwn a (hOwn a (by omega)); omega), ht])
    (fun a ha => by
      dsimp only [tok'] at ha ⊢
      by_cases hsc : scratch ≤ a ∧ a < sc1
      · exact Or.inr hsc
      · rw [ite_eq_right hsc] at ha; exact Or.inl (hOwn a ha))
    (fun i hi => ⟨fun hEq => by
        have hij : i = j := by omega
        subst hij
        refine ⟨by simpa [tok'] using hrepY, fun a ha => ?_⟩
        dsimp only [tok'] at ha ⊢; rw [Function.update_self] at ha
        rcases hftY a ha with hold | hnew
        · rw [ite_eq_right (by have := hbelow a (Or.inr (Or.inr ⟨i, hi, hold⟩)); omega)]
          exact t21 i hi a hold
        · rw [ite_eq_left hnew],
      fun hne => by dsimp only [tok']; exact Function.update_of_ne (by omega) _ _⟩)
  have hfootOut : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok' a →
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a ∨
        (scratch ≤ a ∧ a < sc1) := by
    intro a ha
    rcases ha with (ho | hnew) | htr | ⟨i, hi, hc⟩
    · exact Or.inl (Or.inl ho)
    · exact Or.inr hnew
    · exact Or.inl (Or.inr (Or.inl htr))
    · dsimp only [tok'] at hc
      by_cases hij : i = j
      · subst hij; rw [Function.update_self] at hc
        rcases hftY a hc with hold | hnew
        · exact Or.inl (Or.inr (Or.inr ⟨i, hi, hold⟩))
        · exact Or.inr hnew
      · rw [Function.update_of_ne hij] at hc; exact Or.inl (Or.inr (Or.inr ⟨i, hi, hc⟩))
  have hphiOut : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok' mem' +
      Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem =
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem +
      Rcore.phi (tok.coreHandle j) y mem' := by
    have htreeLocal := LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC
    dsimp only [solverStateRep, tok']
    have htrPhi : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap tok.treeTok mem' =
        (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).phi tok.treeHeap tok.treeTok mem :=
      ((htreeLocal tok.treeHeap tok.tree tok.treeTok mem mem' fun a ha =>
        (hfr a (hltOwn a (hOwn a (by rw [t16 a ha]; decide)))
          (fun hc => by have := t16 a ha; have := t21 j hj a hc; omega)).symm).2).symm
    have hsumSplit : ∀ (f : Fin cfg.P.d → ℕ),
        (∑ i : Fin cfg.P.d, f i) = f ⟨j, hj⟩ + ∑ i ∈ Finset.univ.erase ⟨j, hj⟩, f i :=
      fun f => (Finset.add_sum_erase Finset.univ f (Finset.mem_univ ⟨j, hj⟩)).symm
    have hrestEq : (∑ i ∈ Finset.univ.erase (⟨j, hj⟩ : Fin cfg.P.d),
          Rcore.phi (tok.coreHandle i.val) (Function.update tok.coreTok j y i.val) mem') =
        ∑ i ∈ Finset.univ.erase (⟨j, hj⟩ : Fin cfg.P.d), Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hne : i.val ≠ j := fun h => (Finset.mem_erase.mp hi).1 (Fin.ext h)
      rw [Function.update_of_ne hne]
      exact ((hlocalCore (tok.coreHandle i.val) (chainLevelOrdAbs model.chain i.val) (tok.coreTok i.val)
        mem mem' fun a ha =>
        (hfr a (hltOwn a (hOwn a (by rw [t21 i.val i.isLt a ha]; omega)))
          (fun hc => by have := t21 i.val i.isLt a ha; have := t21 j hj a hc; omega)).symm).2).symm
    rw [htrPhi, hsumSplit (fun i => Rcore.phi (tok.coreHandle i.val) (Function.update tok.coreTok j y i.val) mem'),
      hsumSplit (fun i => Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem),
      Function.update_self, hrestEq]
    dsimp only; omega
  exact ⟨hrepOut, hfootOut, hphiOut⟩

/-- Preserving `solverStateRep` when writing two dedicated select-pointer cells `hbCell`,
`hbCell + 1` whose tags do not collide with any `SolverTagsAt` tag (`1 .. 20 + d`). -/
theorem solverStateRep_write_hbCells
    {cfg : Alg2Config} {L P m V psi k epsExp drainUnit hbCell : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} (hlocalCore : Rcore.Local)
    {root : ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem mem' : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hTagOff : ∀ a, a = hbCell ∨ a = hbCell + 1 →
      ∀ v, 1 ≤ v → v ≤ 20 + cfg.P.d → tok.tag a ≠ v)
    (hfr : ∀ a, tok.owned a → a ≠ hbCell → a ≠ hbCell + 1 → mem' a = mem a) :
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem' ∧
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem' =
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem := by
  have htags := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hOwn := htags.1
  have t16 := htags.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have t21 := htags.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hagT : ∀ a v, tok.tag a = v → 1 ≤ v → v ≤ 20 + cfg.P.d → mem' a = mem a :=
    fun a v ht h1 h2 => hfr a (hOwn a (by omega))
      (fun h => hTagOff a (Or.inl h) v h1 h2 ht)
      (fun h => hTagOff a (Or.inr h) v h1 h2 ht)
  refine ⟨solverStateRep_of_tag_agree (skipTag := 0) hlocalCore (Or.inl rfl) hrep
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun a v ht h1 h2 _ => hagT a v ht h1 h2) (fun _ _ ht _ _ => ht) hOwn
    (fun _ _ => ⟨fun h => by omega, fun _ => rfl⟩), ?_⟩
  have htreeLocal := LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC
  dsimp only [solverStateRep]
  have h1 := ((htreeLocal tok.treeHeap tok.tree tok.treeTok mem mem' fun a ha => (hagT a 16 (t16 a ha) (by omega) (by omega)).symm).2).symm
  have h2 : (∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem') =
      ∑ i : Fin cfg.P.d, Rcore.phi (tok.coreHandle i.val) (tok.coreTok i.val) mem :=
    Finset.sum_congr rfl fun i _ =>
      ((hlocalCore (tok.coreHandle i.val) (chainLevelOrdAbs model.chain i.val) (tok.coreTok i.val)
        mem mem' fun a ha => (hagT a (21 + i.val) (t21 i.val i.isLt a ha) (by omega) (by omega)).symm).2).symm
  rw [h1, h2]

/-- Preserving `SolverLevelCapsInv` when writing two dedicated select-pointer cells `hbCell`,
`hbCell + 1` that lie outside `[solverN0Addr table d, solverLevelMetaAddr table d + 2 * d)` and
outside all addresses tagged `20`, `22 + d`, or `23 + d`. This fits the layout
where `hbCell = solverSelectHeapAddr table d` (`tag = 21 + d`). -/
theorem solverLevelCapsInv_write_hbCells
    {cfg : Alg2Config} {L P V vCap eCap hbCell : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem mem' : ℕ → ℕ}
    (hcaps : SolverLevelCapsInv P V vCap eCap model tok mem)
    (hOwn : ∀ a, tok.tag a ≠ 0 → tok.owned a)
    (hhbDisj : hbCell + 1 < solverN0Addr tok.table cfg.P.d ∨
      solverLevelMetaAddr tok.table cfg.P.d + 2 * cfg.P.d ≤ hbCell)
    (hhbTagOff : ∀ a, a = hbCell ∨ a = hbCell + 1 →
      tok.tag a ≠ 20 ∧ tok.tag a ≠ 22 + cfg.P.d ∧ tok.tag a ≠ 23 + cfg.P.d)
    (hfr : ∀ a, tok.owned a → a ≠ hbCell → a ≠ hbCell + 1 → mem' a = mem a) :
    SolverLevelCapsInv P V vCap eCap model tok mem' := by
  have hMC := solverLevelCapsInv_iff_metaCaps.mp hcaps
  rw [solverLevelCapsInv_iff_metaCaps]
  obtain ⟨⟨hN0Val, hTagN0, hTagSH, hTagSB⟩, hCoreOwn, hMTab, hTagM, hTagMeta, hLvls⟩ := hMC
  have hNeHb : ∀ a, solverN0Addr tok.table cfg.P.d ≤ a →
      a < solverLevelMetaAddr tok.table cfg.P.d + 2 * cfg.P.d →
      a ≠ hbCell ∧ a ≠ hbCell + 1 := fun a h1 h2 => by rcases hhbDisj with h | h <;> omega
  have hAgMeta : ∀ a, tok.tag a = 21 + cfg.P.d →
      solverN0Addr tok.table cfg.P.d ≤ a →
      a < solverLevelMetaAddr tok.table cfg.P.d + 2 * cfg.P.d →
      mem' a = mem a := fun a ht h1 h2 =>
    hfr a (hOwn a (by omega)) (hNeHb a h1 h2).1 (hNeHb a h1 h2).2
  have hAgOther : ∀ a, tok.tag a = 20 ∨ tok.tag a = 22 + cfg.P.d ∨ tok.tag a = 23 + cfg.P.d →
      mem' a = mem a := fun a ht =>
    hfr a (hOwn a (by rcases ht with h | h | h <;> omega))
      (fun h => by have := hhbTagOff a (Or.inl h); rcases ht with ht | ht | ht <;> omega)
      (fun h => by have := hhbTagOff a (Or.inr h); rcases ht with ht | ht | ht <;> omega)
  refine ⟨⟨?_, hTagN0, hTagSH, hTagSB⟩, hCoreOwn, ?_, hTagM, hTagMeta, ?_⟩
  · exact (hAgMeta _ hTagN0 le_rfl (by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega)).trans hN0Val
  · intro j hj
    exact (hAgMeta _ (hTagM j hj) (by unfold solverLvlMAddr solverN0Addr; omega)
      (by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega)).trans (hMTab j hj)
  · intro j hj
    obtain ⟨hDG, hEV, hLenOwn, hTagL, hTagG⟩ := hLvls j hj
    have hMemL : mem' (solverLevelMetaAddr tok.table cfg.P.d + j) =
        mem (solverLevelMetaAddr tok.table cfg.P.d + j) :=
      hAgOther _ (Or.inr (Or.inl (hTagMeta j (by omega))))
    have hMemG : mem' (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) =
        mem (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + j) := by
      have htag := hTagMeta (cfg.P.d + j) (by omega)
      rw [← Nat.add_assoc] at htag
      exact hAgOther _ (Or.inr (Or.inl htag))
    rw [hMemL, hMemG]
    refine ⟨hDG.of_agree fun a h1 h2 => hAgOther a (by
        have htg := hTagG a h1 h2; split_ifs at htg
        · exact Or.inl htg
        · exact Or.inr (Or.inr htg)),
      fun e he => ?_, hLenOwn, hTagL, hTagG⟩
    have hev := hEV e he
    have hcap := hDG.2.2.1 e he
    have hAgE : ∀ k < L, mem' (mem (solverLevelMetaAddr tok.table cfg.P.d + j) + e * L + k) =
        mem (mem (solverLevelMetaAddr tok.table cfg.P.d + j) + e * L + k) := fun k hk => by
      have hmul : e * L + L ≤ eCap * L := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L (Nat.succ_le_of_lt hcap)
      exact hAgOther _ (Or.inr (Or.inr (hTagL _ (by omega) (by omega))))
    exact ⟨fun k hk => by rw [hAgE k hk]; exact hev.1 k hk, by
      unfold Num.fixVal; rw [Num.intVal_congr hAgE]; exact hev.2⟩

/-- Sequencing helper for `.assign` statements in `selectInitRegion_runs`. -/
theorem runs_seq_assign_ex2 {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {r : ℕ} {e : Expr} {s2 : Stmt} {st : State} {v : ℕ} {P : Outcome → State → ℕ → Prop}
    (hv : e.eval w st = some v)
    (h2 : ∃ o out c, Runs w p ω s2 ⟨st.mem, Function.update st.regs r v, st.pos⟩ o out c ∧
      P o out ((e.size + 1) + c + 1)) :
    ∃ o out c, Runs w p ω (.assign r e ;; s2) st o out c ∧ P o out c := by
  obtain ⟨o, out, c, hr2, hp⟩ := h2
  exact ⟨o, out, _, runs_seq_iff.mpr (Or.inr ⟨_, _, _,
    runs_assign_iff.mpr ⟨v, hv, rfl, rfl, rfl⟩, hr2, rfl⟩), hp⟩

/-- Sequencing helper for `.call` statements in `selectInitRegion_runs`. -/
theorem runs_seq_call_ex2 {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {r f : ℕ} {args : List Expr} {s2 : Stmt} {st st1 : State} {vs : List ℕ}
    {body : Stmt} {o1 : Outcome} {c1 : ℕ} {P : Outcome → State → ℕ → Prop}
    (hvs : evalArgs w st args = some vs) (hbody : p.procs[f]? = some body)
    (hr1 : Runs w p ω body (startState vs st.mem st.pos) o1 st1 c1)
    (h2 : ∃ o out c, Runs w p ω s2 ⟨st1.mem, Function.update st.regs r o1.value, st1.pos⟩ o out c ∧
      P o out ((argsSize args + c1 + 1) + c + 1)) :
    ∃ o out c, Runs w p ω (.call r f args ;; s2) st o out c ∧ P o out c := by
  obtain ⟨o, out, c, hr2, hp⟩ := h2
  exact ⟨o, out, _, runs_seq_iff.mpr (Or.inr ⟨_, _, _,
    runs_call_iff.mpr ⟨vs, body, o1, st1, c1, hvs, hbody, hr1, rfl, rfl, rfl⟩, hr2, rfl⟩), hp⟩

/-- Sequencing helper for `.cond` with two `.assign` branches in `selectInitRegion_runs`. -/
theorem runs_seq_cond_assign_ex2 {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {ec eT eF : Expr} {r : ℕ} {s2 : Stmt} {st : State} {vc v : ℕ}
    {P : Outcome → State → ℕ → Prop}
    (hvc : ec.eval w st = some vc)
    (hbr : (if vc ≠ 0 then eT else eF).eval w st = some v)
    (h2 : ∃ o out c, Runs w p ω s2 ⟨st.mem, Function.update st.regs r v, st.pos⟩ o out c ∧
      P o out ((ec.size + ((if vc ≠ 0 then eT else eF).size + 1) + 1) + c + 1)) :
    ∃ o out c, Runs w p ω (.cond ec (.assign r eT) (.assign r eF) ;; s2) st o out c ∧ P o out c := by
  obtain ⟨o, out, c, hr2, hp⟩ := h2
  refine ⟨o, out, _, runs_seq_iff.mpr (Or.inr ⟨_, _, _,
    runs_cond_iff.mpr ⟨vc, (if vc ≠ 0 then eT else eF).size + 1, hvc, ?_, rfl⟩, hr2, rfl⟩), hp⟩
  by_cases h0 : vc = 0
  · simp only [h0, ↓reduceIte, ne_eq, not_true_eq_false] at hbr ⊢
    exact runs_assign_iff.mpr ⟨v, hbr, rfl, rfl, rfl⟩
  · simp only [h0, ↓reduceIte, ne_eq, not_false_eq_true] at hbr ⊢
    exact runs_assign_iff.mpr ⟨v, hbr, rfl, rfl, rfl⟩

end MinCostFlow.MinRatio
