module

public import MinCostFlow.SparseCore.Program.TourSplayQuery
import Mathlib.Tactic

/-!
# Cyclic next-ready WordRAM splay procedure for tour maintenance

Verifies `tourNextReadyBody` (used for `nextOpen`, `adjacent`, and `nextMarked`), proving that it
finds the first ready node in `(rotateNatList x t.toList).tail ++ [x]` (or `0` if none), restores
the exact tree sequence `t'.toList = t.toList`, and runs in `O(log (cap + 2))` amortized time.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

private theorem heapOk_of_frameN {nb cap heap sp : ℕ} {w : ℕ} {mem M : ℕ → ℕ}
    (hheap : HeapOk tourLayout w nb cap heap sp mem)
    (hfr : TreeFrame tourLayout nb cap heap mem M) :
    HeapOk tourLayout w nb cap heap sp M :=
  ⟨hheap.rec_le, hheap.room, hfr.1, hheap.wide⟩

private theorem heapOk_zeroN {nb cap heap sp : ℕ} {w : ℕ} {mem : ℕ → ℕ}
    (hheap : HeapOk tourLayout w nb cap heap sp mem) :
    HeapOk tourLayout w nb cap heap 0 mem :=
  ⟨hheap.rec_le, by have := hheap.room; omega, hheap.zero, hheap.wide⟩

private theorem child_rs_iff {cap x : ℕ} {st : SplayState TourVal TourSum Unit}
    {L R : AuxTree} {rest : List AuxTree} {rs : TourSum → Bool} {rv : TourVal → Bool}
    (hR : ReadyLaw tourPayload rs rv)
    (hf : TourForestInv cap st (AuxTree.node x L R :: rest)) :
    (L ≠ .leaf → (rs (st.nodes L.rootId).sum = true ↔ ∃ u ∈ L.toList, rv (st.nodes u).val = true)) ∧
    (R ≠ .leaf → (rs (st.nodes R.rootId).sum = true ↔ ∃ u ∈ R.toList, rv (st.nodes u).val = true)) := by
  have hsub := (hf.treesInv (AuxTree.node x L R) (by simp)).sub
  have hfold : ∀ (c : AuxTree), c ≠ .leaf → SubtreeInv tourPayload st x c →
      (∀ u ∈ c.toList, (st.nodes u).rev = false) →
      (rs (st.nodes c.rootId).sum = true ↔ ∃ u ∈ c.toList, rv (st.nodes u).val = true) := by
    intro c hcne hcsub hcrev
    cases c with
    | leaf => exact absurd rfl hcne
    | node cid cL cR =>
      have hsum : (st.nodes cid).sum =
          tourPayload.listSummary ((AuxTree.node cid cL cR).toList.map fun u => (u, (st.nodes u).val)) := by
        rw [hcsub.2.2.2.2.2.2.1, tourEvalPairs_eq_map hcrev]
      rw [AuxTree.rootId, hsum, hR]
      simp only [List.mem_map, exists_exists_and_eq_and]
  refine ⟨fun hne => hfold L hne hsub.2.2.2.2.2.2.2.1
      (fun u hu => hf.noRev u (hf.mem_inCap (t := AuxTree.node x L R) (by simp) (by simp [AuxTree.toList, hu])).2),
    fun hne => hfold R hne hsub.2.2.2.2.2.2.2.2
      (fun u hu => hf.noRev u (hf.mem_inCap (t := AuxTree.node x L R) (by simp) (by simp [AuxTree.toList, hu])).2)⟩

/-- Running `tourNextReadyBody` on `x ∈ t.toList` returns the first ready node in
`(rotateNatList x t.toList).tail ++ [x]` (or `0` if none), keeping `t'.toList = t.toList`
in `O(log (cap + 2))` amortized time. -/
theorem tourNextReadyBody_runs {w nb cap heap fuel x pos dp fp : ℕ} {p : Program}
    {rs : TourSum → Bool} {rv : TourVal → Bool}
    (C : TourSplayQueryProcs w p) (T : ReadyTests w p tourLayout rs rv) (hTc : T.cost = TOUR_TEST_COST)
    (hR : ReadyLaw tourPayload rs rv)
    (hdp : p.procs[dp]? = some (descendBody dp C.lazy.pushDown T.sumTest T.valTest))
    (hfp : p.procs[fp]? = some (tourFindFirstBody dp T.sumTest C.splay.splay))
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t : AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (t :: rest)) (hvals : TourValsOk w cap st)
    (hx : x ∈ t.toList) (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ y t' s' o st' c,
      Runs w p ω (tourNextReadyBody C.splay.splay C.detachLeft C.detachRight C.join fp T.sumTest T.valTest)
        (startState [nb, x, fuel, heap] mem pos) o st' c ∧
      o.value = y ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (t' :: rest) ∧
      TourValsOk w cap s' ∧
      t' ≠ .leaf ∧ t'.toList = t.toList ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ t.toList, s'.nodes u = st.nodes u) ∧
      (((rotateNatList x t.toList).tail ++ [x]).find? (fun u => rv (st.nodes u).val)).getD 0 = y ∧
      c + TOUR_PHI_MULT * forestPhi (t' :: rest) ≤
        TOUR_PHI_MULT * forestPhi (t :: rest) + TOUR_NEXT_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hwide := hheap.wide; have hroom := hheap.room
  have hdep : t.depthOf x < fuel :=
    lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hx) (le_of_lt (lt_of_le_of_lt (hf.countNodes_le (by simp)) hfuel))
  have hf0 : TourForestInv cap st ([] ++ t :: rest) := hf
  obtain ⟨t₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, hout₁, hcost₁⟩ :=
    tourSplay_runs_amort (pos := pos) C.toTourSplayCoreProcs ω hnodes hf0 hvals hx hdep hfuelW hheap
  set s₁ := SplayState.splay tourPayload st fuel x
  obtain ⟨_, _, _, _, _, _, hval_sp, _⟩ := tourSplay_preserves hf0 hx hdep
  cases ht₁c : t₁ with
  | leaf => exact absurd ht₁c hne₁
  | node xid L R =>
    have hxid : xid = x := by simpa [ht₁c, AuxTree.rootId] using hroot₁
    rcases hxid with rfl
    rw [ht₁c] at hinv₁ hlist₁ hcost₁
    have hinv₁' : TourForestInv cap s₁ (AuxTree.node xid L R :: rest) := hinv₁
    have hx_cap : xid ≤ cap := (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList])).2
    have hAx : nb + 17 * xid + 17 ≤ heap := by simpa [nodeAddr, tourLayout_stride] using hheap.addr_lt hx_cap
    have hsub₁ := (hinv₁'.treesInv (AuxTree.node xid L R) (by simp)).sub
    have hnd₁ := (hinv₁'.treesInv (AuxTree.node xid L R) (by simp)).nodup
    have hcyc_eq : (rotateNatList xid t.toList).tail ++ [xid] = R.toList ++ L.toList ++ [xid] := by
      have ht_eq : t.toList = L.toList ++ xid :: R.toList := by rw [← hlist₁]; simp [AuxTree.toList]
      have hx_nL : xid ∉ L.toList := (AuxTree.nodup_node_unfold hnd₁).2.1
      have hidx : (L.toList ++ xid :: R.toList).idxOf xid = L.toList.length := by
        generalize hLs : L.toList = ls at hx_nL ⊢
        clear * - hx_nL
        induction ls with
        | nil => simp
        | cons a as ih =>
          have hax : a ≠ xid := fun h => hx_nL (by simp [h])
          simp [hax, ih (fun hm => hx_nL (by simp [hm]))]
      have hrot : rotateNatList xid t.toList = xid :: (R.toList ++ L.toList) := by
        rw [ht_eq]; unfold rotateNatList
        have hx' : xid ∈ L.toList ++ xid :: R.toList := by simp
        simp [hx', hidx]
      rw [hrot]; simp
    have hm1_r : st₁.mem (nb + 17 * xid + 1) = R.rootId := by
      simpa [nodeAddr, OFF_RIGHT, tourLayout_stride, hsub₁.2.2.1] using (hn₁ xid hx_cap).2.1
    have hm1_l : st₁.mem (nb + 17 * xid) = L.rootId := by
      simpa [nodeAddr, OFF_LEFT, tourLayout_stride, hsub₁.2.1] using (hn₁ xid hx_cap).1
    have hheap₁ : HeapOk tourLayout w nb cap heap 2 st₁.mem := ⟨hheap.rec_le, hroom, hfr₁.1, hwide⟩
    have hchild_rs := child_rs_iff hR hinv₁'
    set r0 := fun i => [nb, xid, fuel, heap].getD i 0
    set r1 := Function.update r0 4 o₁.value
    set r2 := Function.update r1 4 (nb + 17 * xid)
    set r3 := Function.update r2 5 R.rootId
    have hc1_call : Runs w p ω (.call 4 C.splay.splay [.reg 0, .reg 1, .reg 2, .reg 3])
        (startState [nb, xid, fuel, heap] mem pos) .normal ⟨st₁.mem, r1, st₁.pos⟩ (5 + c₁) :=
      runs_call_regs4 4 0 1 2 3 (st := startState [nb, xid, fuel, heap] mem pos) C.splay.splay_body
        (by simp [startState]) (by simp [startState]) (by simp [startState]) (by simp [startState]) hrun₁
    have h17x_lt : 17 * xid < 2 ^ w := by omega
    have hnb17x_lt : nb + 17 * xid < 2 ^ w := by omega
    have hnb17x1_lt : nb + 17 * xid + 1 < 2 ^ w := by omega
    have hass4 : Runs w p ω (.assign 4 (.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 1))))
        ⟨st₁.mem, r1, st₁.pos⟩ .normal ⟨st₁.mem, r2, st₁.pos⟩ _ :=
      runs_assign_iff.mpr ⟨nb + 17 * xid, by simp [Expr.eval, r1, r0, BinOp.eval, h17x_lt, hnb17x_lt, (by omega : 17 < 2 ^ w)], rfl, rfl, rfl⟩
    have hass5r : Runs w p ω (.assign 5 (.load (.bin .add (.reg 4) (.const 1))))
        ⟨st₁.mem, r2, st₁.pos⟩ .normal ⟨st₁.mem, r3, st₁.pos⟩ _ :=
      runs_assign_iff.mpr ⟨R.rootId, by simp [Expr.eval, r2, BinOp.eval, hnb17x1_lt, hm1_r, (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
    by_cases hR_ready : ∃ u ∈ R.toList, rv (st.nodes u).val = true
    · have hR_ne : R ≠ .leaf := by
        rcases hR_ready with ⟨u, hu, _⟩; intro h; subst h; simp [AuxTree.toList] at hu
      have hR_nz : R.rootId ≠ 0 := by
        cases hRc : R with | leaf => exact absurd hRc hR_ne | node _ _ _ => rw [hRc] at hsub₁; exact hsub₁.2.2.2.2.2.2.2.2.1
      have hR_cap : R.rootId ≤ cap :=
        (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, AuxTree.rootId_mem hR_ne])).2
      have hAr : nb + 17 * R.rootId + 17 ≤ heap := by simpa [nodeAddr, tourLayout_stride] using hheap.addr_lt hR_cap
      have hR_s1_rs : rs (s₁.nodes R.rootId).sum = true := (hchild_rs.2 hR_ne).mpr <| by
        rcases hR_ready with ⟨u, hu, hru⟩
        exact ⟨u, hu, by rw [hval_sp u (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, hu])).2]; exact hru⟩
      have hstR_pre : (sumTestContract tourLayout rs w T.cost).pre [nb + 17 * R.rootId] st₁.mem :=
        ⟨nb + 17 * R.rootId, (s₁.nodes R.rootId).val, (s₁.nodes R.rootId).sum, rfl,
          by rw [tourLayout_stride]; omega, (hn₁ R.rootId hR_cap).2.2.2.2.2.2.1,
          (hn₁ R.rootId hR_cap).2.2.2.2.2.2.2.1⟩
      obtain ⟨b_sr, hb_sr, o_sr, st_sr, c_sr, hrun_sr, ⟨hmem_sr, hval_sr⟩, hc_sr⟩ :=
        T.sum_ok [nb + 17 * R.rootId] st₁.mem st₁.pos ω (by simp; omega) hstR_pre
      have hsr_one : o_sr.value = 1 := by
        simpa [hR_s1_rs] using hval_sr (s₁.nodes R.rootId).sum (hn₁ R.rootId hR_cap).2.2.2.2.2.2.2.1
      obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hv₂, hn₂, hfr₂⟩, hc₂⟩ := tourDetachRightBody_runs (pos := st_sr.pos)
        C.toTourSplayCoreProcs ω (hmem_sr ▸ hn₁) hinv₁'.ptrOk hx_cap
        (heapOk_zeroN (hmem_sr ▸ hheap₁)) (tourDetachRight_sumOk hinv₁ hvals₁)
      obtain ⟨hinv₂, hout₂, hval₂, hphi₂⟩ := tourDetachRight_preserves hinv₁
      set s₂ := tourDetachRight s₁ xid
      have hvals₂ : TourValsOk w cap s₂ := ⟨hvals₁.1, fun u hu => by rw [hval₂ u hu]; exact hvals₁.2 u hu⟩
      have hv₂_eq : o₂.value = R.rootId := by simp only [hv₂, hsub₁.1, ↓reduceIte, hsub₁.2.2.1]
      have hperm₂ : ([AuxTree.node xid L .leaf, R] ++ rest).Perm (optTrees (some R) ++ (AuxTree.node xid L .leaf :: rest)) := by
        simp only [optTrees, Option.toList, List.cons_append, List.nil_append]; exact List.Perm.swap _ _ rest
      have hinv₂' : TourForestInv cap s₂ (optTrees (some R) ++ (AuxTree.node xid L .leaf :: rest)) :=
        ((by simpa [hR_ne] using hinv₂ : TourForestInv cap s₂ ([AuxTree.node xid L .leaf, R] ++ rest)).perm hperm₂).1
      obtain ⟨y, R'?, s₃, o₃, st₃, c₃, hrun₃, hv₃, hn₃, hfr₃, hinv₃, hvals₃, hlist₃, hval₃, hout₃, hspec₃, hcost₃⟩ :=
        tourFindFirstBody_runs (pos := st₂.pos) C T hTc hR hdp ω hn₂ hinv₂' hvals₂ hfuel hfuelW
          (heapOk_of_frameN hheap (hfr₁.trans (hmem_sr ▸ hfr₂)))
      have hR_find_eq : R.toList.find? (fun u => rv (s₂.nodes u).val) = R.toList.find? (fun u => rv (st.nodes u).val) :=
        list_find?_congr fun u hu => by
          rw [hval₂ u (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, hu])).2,
              hval_sp u (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, hu])).2]
      obtain ⟨y₀, hy₀⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hR_ready)
      simp only [optList, Option.elim, hR_find_eq, hy₀] at hspec₃
      rcases hspec₃ with ⟨rfl, R', L_y, R_y, rfl, rfl, _, _⟩
      have hperm₃ : (optTrees (some (AuxTree.node y L_y R_y)) ++ (AuxTree.node xid L .leaf :: rest)).Perm
          (optTrees (some (AuxTree.node xid L .leaf)) ++ optTrees (some (AuxTree.node y L_y R_y)) ++ rest) := by
        simp only [optTrees, Option.toList, List.cons_append, List.nil_append]; exact List.Perm.swap _ _ rest
      obtain ⟨t'?, s₄, o₄, st₄, c₄, hrun₄, hv₄, hn₄, hfr₄, hinv₄, hvals₄, hlist₄, hval₄, hout₄, hcost₄⟩ :=
        tourJoinBody_runs (pos := st₃.pos) C.toTourSplayOpsProcs ω hn₃ (hinv₃.perm hperm₃).1 hvals₃ hfuel hfuelW
          (heapOk_of_frameN hheap (hfr₁.trans ((hmem_sr ▸ hfr₂).trans hfr₃)))
      cases t'? with
      | none => simp [optList, AuxTree.toList] at hlist₄
      | some t' =>
        have hne' : t' ≠ .leaf := hinv₄.nonEmpty t' (by simp [optTrees])
        have ht'_list : t'.toList = t.toList := by
          have hR' : (AuxTree.node y L_y R_y).toList = R.toList := by simpa [optList] using hlist₃
          simp only [optList, Option.elim] at hlist₄
          rw [hR'] at hlist₄
          rw [← hlist₁, hlist₄]; simp [AuxTree.toList]
        have hval_all : ∀ u ≤ cap, (s₄.nodes u).val = (st.nodes u).val := fun u hu => by
          exact (hval₄ u hu).trans ((hval₃ u hu).trans ((hval₂ u hu).trans (hval_sp u hu)))
        have hout_all : ∀ u ∉ t.toList, s₄.nodes u = st.nodes u := fun u hu => by
          have hu1 : u ∉ (AuxTree.node xid L R).toList := by rwa [hlist₁]
          have huR : u ∉ R.toList := fun h => hu1 (by simp [AuxTree.toList, h])
          have hR' : (AuxTree.node y L_y R_y).toList = R.toList := by simpa [optList] using hlist₃
          have hu4 : u ∉ optList (some (AuxTree.node xid L .leaf)) ++ optList (some (AuxTree.node y L_y R_y)) := by
            intro hm; apply hu1
            simp only [optList, Option.elim, List.mem_append] at hm
            rw [hR'] at hm
            rcases hm with h1 | h2
            · simp only [AuxTree.toList, List.append_nil, List.mem_append, List.mem_singleton] at h1
              rcases h1 with hL | rfl
              · simp [AuxTree.toList, hL]
              · simp [AuxTree.toList]
            · simp [AuxTree.toList, h2]
          exact (hout₄ u hu4).trans ((hout₃ u (by simpa [optList] using huR)).trans ((hout₂ u hu1).trans (hout₁ u hu)))
        have h17R_lt : 17 * R.rootId < 2 ^ w := by omega
        have hnb17R_lt : nb + 17 * R.rootId < 2 ^ w := by omega
        set s_sr : State := { st_sr with regs := Function.update r3 6 o_sr.value }
        set s_dr : State := { st₂ with regs := Function.update s_sr.regs 7 o₂.value }
        set s_ff : State := { st₃ with regs := Function.update s_dr.regs 8 o₃.value }
        set s_jn : State := { st₄ with regs := Function.update s_ff.regs 9 o₄.value }
        have hcall_sr := tour_runs_call_of (r := 6) (args := [.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 5))])
          (st := ⟨st₁.mem, r3, st₁.pos⟩) hb_sr
          (by simp [evalArgs, Expr.eval, r3, r2, r1, r0, BinOp.eval, h17R_lt, hnb17R_lt, (by omega : 17 < 2 ^ w)]) hrun_sr
        have hcall_dr := runs_call_regs3 7 0 1 3 (st := s_sr) C.detachRight_body (by simp [s_sr, r3, r2, r1, r0]) (by simp [s_sr, r3, r2, r1, r0]) (by simp [s_sr, r3, r2, r1, r0]) hrun₂
        have hcall_ff := runs_call_regs4 8 0 7 2 3 (st := s_dr) hfp (by simp [s_dr, s_sr, r3, r2, r1, r0]) (by simp [s_dr, hv₂_eq, optRoot]) (by simp [s_dr, s_sr, r3, r2, r1, r0]) (by simp [s_dr, s_sr, r3, r2, r1, r0]) hrun₃
        have hcall_jn := runs_call_regs5 9 0 1 8 2 3 (st := s_ff) C.join_body (by simp [s_ff, s_dr, s_sr, r3, r2, r1, r0]) (by simp [s_ff, s_dr, s_sr, r3, r2, r1, r0, optRoot, AuxTree.rootId]) (by simp [s_ff, hv₃, optRoot, AuxTree.rootId]) (by simp [s_ff, s_dr, s_sr, r3, r2, r1, r0]) (by simp [s_ff, s_dr, s_sr, r3, r2, r1, r0]) hrun₄
        have hret_y := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s_jn) (r := 8) (v := y) (by simp [s_jn, s_ff, hv₃])
        have hinner := tour_runs_seq_normal hcall_dr (tour_runs_seq_normal hcall_ff (tour_runs_seq_normal hcall_jn hret_y))
        have hcond6 := tour_runs_cond_true (e := .reg 6) (v := 1) (s₂ := .nop) (by simp [Expr.eval, s_sr, hsr_one]) (by omega) hinner
        have hcond5 := tour_runs_cond_true (e := .reg 5) (v := R.rootId) (s₂ := .nop) (by simp [Expr.eval, r3]) hR_nz (tour_runs_seq_normal hcall_sr hcond6)
        have hfull : ∃ c_fin, c_fin ≤ c₁ + c_sr + c₂ + c₃ + c₄ + 120 ∧
            Runs w p ω (tourNextReadyBody C.splay.splay C.detachLeft C.detachRight C.join fp T.sumTest T.valTest)
              (startState [nb, xid, fuel, heap] mem pos) (.returned y) s_jn c_fin := by
          unfold tourNextReadyBody
          exact ⟨_, by simp only [argsSize, Expr.size]; omega,
            tour_runs_seq_normal hc1_call (tour_runs_seq_normal hass4 (tour_runs_seq_normal hass5r (runs_seq_ret hcond5)))⟩
        obtain ⟨c_fin, hcfin, hfull⟩ := hfull
        refine ⟨y, t', s₄, .returned y, s_jn, c_fin, hfull, rfl, hn₄,
          hfr₁.trans ((hmem_sr ▸ hfr₂).trans (hfr₃.trans hfr₄)), by simpa [optTrees] using hinv₄,
          hvals₄, hne', ht'_list, hval_all, hout_all, ?_, ?_⟩
        · rw [hcyc_eq, List.append_assoc, List.find?_append, hy₀]; rfl
        · have hphi2' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₂
          have hpeq2 := forestPhi_perm hperm₂; have hpeq3 := forestPhi_perm hperm₃
          simp only [hR_ne, ↓reduceIte, List.nil_append] at hphi2'
          rw [← hpeq2] at hcost₃; rw [← hpeq3] at hcost₄
          simp only [sumTestContract, hTc, TOUR_TEST_COST] at hc_sr
          simp only [optTrees, Option.toList, List.nil_append, List.cons_append,
            TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_FIND_AMORT, TOUR_JOIN_AMORT, TOUR_NEXT_AMORT] at hcost₁ hcost₃ hcost₄ hphi2' hc₂ hc_sr hcfin ⊢
          omega
    · have hR_find_none : R.toList.find? (fun u => rv (st.nodes u).val) = none :=
        List.find?_eq_none.mpr fun u hu hru => hR_ready ⟨u, hu, hru⟩
      have hbranch1 : ∃ r3' c_b1 pos_b1,
          Runs w p ω (.cond (.reg 5)
            (.call 6 T.sumTest [.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 5))] ;;
             .cond (.reg 6)
               (.call 7 C.detachRight [.reg 0, .reg 1, .reg 3] ;;
                .call 8 fp [.reg 0, .reg 7, .reg 2, .reg 3] ;;
                .call 9 C.join [.reg 0, .reg 1, .reg 8, .reg 2, .reg 3] ;;
                .ret (.reg 8))
               .nop)
            .nop)
            ⟨st₁.mem, r3, st₁.pos⟩ .normal ⟨st₁.mem, r3', pos_b1⟩ c_b1 ∧
          (∀ i < 5, r3' i = r3 i) ∧ c_b1 ≤ TOUR_TEST_COST + 30 := by
        cases hRc : R with
        | leaf =>
          exact ⟨r3, _, st₁.pos, tour_runs_cond_false (by simp [Expr.eval, r3, hRc, AuxTree.rootId])
            (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), fun _ _ => rfl, by simp [Expr.size, TOUR_TEST_COST]⟩
        | node rid rL rR =>
          have hR_ne : R ≠ .leaf := by simp [hRc]
          have hR_nz : R.rootId ≠ 0 := by
            have h := hsub₁.2.2.2.2.2.2.2.2; rw [hRc] at h ⊢; exact h.1
          have hR_cap : R.rootId ≤ cap :=
            (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, AuxTree.rootId_mem hR_ne])).2
          have hAr : nb + 17 * R.rootId + 17 ≤ heap := by simpa [nodeAddr, tourLayout_stride] using hheap.addr_lt hR_cap
          have hR_rs0 : rs (s₁.nodes R.rootId).sum = false := by
            cases hrs : rs (s₁.nodes R.rootId).sum
            · rfl
            · exfalso; rcases (hchild_rs.2 hR_ne).mp hrs with ⟨u, hu, hru⟩
              rw [hval_sp u (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, hu])).2] at hru
              exact hR_ready ⟨u, hu, hru⟩
          have hstR_pre : (sumTestContract tourLayout rs w T.cost).pre [nb + 17 * R.rootId] st₁.mem :=
            ⟨nb + 17 * R.rootId, (s₁.nodes R.rootId).val, (s₁.nodes R.rootId).sum, rfl,
              by rw [tourLayout_stride]; omega, (hn₁ R.rootId hR_cap).2.2.2.2.2.2.1,
              (hn₁ R.rootId hR_cap).2.2.2.2.2.2.2.1⟩
          obtain ⟨b_sr, hb_sr, o_sr, st_sr, c_sr, hrun_sr, ⟨hmem_sr, hval_sr⟩, hc_sr⟩ :=
            T.sum_ok [nb + 17 * R.rootId] st₁.mem st₁.pos ω (by simp; omega) hstR_pre
          have hsr_zero : o_sr.value = 0 := by
            simpa [hR_rs0] using hval_sr (s₁.nodes R.rootId).sum (hn₁ R.rootId hR_cap).2.2.2.2.2.2.2.1
          have h17R_lt : 17 * R.rootId < 2 ^ w := by omega
          have hnb17R_lt : nb + 17 * R.rootId < 2 ^ w := by omega
          have hcall_sr := tour_runs_call_of (r := 6) (args := [.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 5))])
            (st := ⟨st₁.mem, r3, st₁.pos⟩) hb_sr
            (by simp [evalArgs, Expr.eval, r3, r2, r1, r0, BinOp.eval, h17R_lt, hnb17R_lt, (by omega : 17 < 2 ^ w)]) hrun_sr
          have hcond6 := tour_runs_cond_false (w := w) (p := p) (ω := ω)
            (st := ⟨st_sr.mem, Function.update r3 6 o_sr.value, st_sr.pos⟩)
            (e := .reg 6) (s₁ := .call 7 C.detachRight [.reg 0, .reg 1, .reg 3] ;;
               .call 8 fp [.reg 0, .reg 7, .reg 2, .reg 3] ;;
               .call 9 C.join [.reg 0, .reg 1, .reg 8, .reg 2, .reg 3] ;;
               .ret (.reg 8))
            (by simp [Expr.eval, Function.update_self, hsr_zero])
            (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)
          have hcond5 := tour_runs_cond_true (e := .reg 5) (v := R.rootId) (s₂ := .nop) (by simp [Expr.eval, r3]) hR_nz (tour_runs_seq_normal hcall_sr hcond6)
          refine ⟨Function.update r3 6 o_sr.value, _, st_sr.pos, by simpa [hmem_sr] using hcond5,
            fun i hi => by simp [show i ≠ 6 by omega], ?_⟩
          simp only [sumTestContract, hTc, TOUR_TEST_COST] at hc_sr
          simp only [TOUR_TEST_COST] at hc_sr ⊢; omega
      obtain ⟨r3', c_b1, pos_b1, hrun_b1, hr3'_eq, hc_b1⟩ := hbranch1
      set r4 := Function.update r3' 5 L.rootId
      have hr4_0 : r4 0 = nb := by simp [r4, hr3'_eq 0 (by omega), r3, r2, r1, r0]
      have hr4_1 : r4 1 = xid := by simp [r4, hr3'_eq 1 (by omega), r3, r2, r1, r0]
      have hr4_2 : r4 2 = fuel := by simp [r4, hr3'_eq 2 (by omega), r3, r2, r1, r0]
      have hr4_3 : r4 3 = heap := by simp [r4, hr3'_eq 3 (by omega), r3, r2, r1, r0]
      have hr4_4 : r4 4 = nb + 17 * xid := by simp [r4, hr3'_eq 4 (by omega), r3, r2]
      have hass5l : Runs w p ω (.assign 5 (.load (.reg 4)))
          ⟨st₁.mem, r3', pos_b1⟩ .normal ⟨st₁.mem, r4, pos_b1⟩ 3 := by
        have hr3'_4 : r3' 4 = nb + 17 * xid := by simp [hr3'_eq 4 (by omega), r3, r2]
        exact runs_assign_iff.mpr ⟨L.rootId, by simp [Expr.eval, hr3'_4, hm1_l], rfl, rfl, rfl⟩
      by_cases hL_ready : ∃ u ∈ L.toList, rv (st.nodes u).val = true
      · have hL_ne : L ≠ .leaf := by
          rcases hL_ready with ⟨u, hu, _⟩; intro h; subst h; simp [AuxTree.toList] at hu
        have hL_nz : L.rootId ≠ 0 := by
          cases hLc : L with | leaf => exact absurd hLc hL_ne | node _ _ _ => rw [hLc] at hsub₁; exact hsub₁.2.2.2.2.2.2.2.1.1
        have hL_cap : L.rootId ≤ cap :=
          (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, AuxTree.rootId_mem hL_ne])).2
        have hAl : nb + 17 * L.rootId + 17 ≤ heap := by simpa [nodeAddr, tourLayout_stride] using hheap.addr_lt hL_cap
        have hL_s1_rs : rs (s₁.nodes L.rootId).sum = true := (hchild_rs.1 hL_ne).mpr <| by
          rcases hL_ready with ⟨u, hu, hru⟩
          exact ⟨u, hu, by rw [hval_sp u (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, hu])).2]; exact hru⟩
        have hstL_pre : (sumTestContract tourLayout rs w T.cost).pre [nb + 17 * L.rootId] st₁.mem :=
          ⟨nb + 17 * L.rootId, (s₁.nodes L.rootId).val, (s₁.nodes L.rootId).sum, rfl,
            by rw [tourLayout_stride]; omega, (hn₁ L.rootId hL_cap).2.2.2.2.2.2.1,
            (hn₁ L.rootId hL_cap).2.2.2.2.2.2.2.1⟩
        obtain ⟨b_sl, hb_sl, o_sl, st_sl, c_sl, hrun_sl, ⟨hmem_sl, hval_sl⟩, hc_sl⟩ :=
          T.sum_ok [nb + 17 * L.rootId] st₁.mem pos_b1 ω (by simp; omega) hstL_pre
        have hsl_one : o_sl.value = 1 := by
          simpa [hL_s1_rs] using hval_sl (s₁.nodes L.rootId).sum (hn₁ L.rootId hL_cap).2.2.2.2.2.2.2.1
        obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hv₂, hn₂, hfr₂⟩, hc₂⟩ := tourDetachLeftBody_runs (pos := st_sl.pos)
          C.toTourSplayCoreProcs ω (hmem_sl ▸ hn₁) hinv₁'.ptrOk hx_cap
          (heapOk_zeroN (hmem_sl ▸ hheap₁)) (tourDetachLeft_sumOk hinv₁ hvals₁)
        obtain ⟨hinv₂, hout₂, hval₂, hphi₂⟩ := tourDetachLeft_preserves hinv₁
        set s₂ := tourDetachLeft s₁ xid
        have hvals₂ : TourValsOk w cap s₂ := ⟨hvals₁.1, fun u hu => by rw [hval₂ u hu]; exact hvals₁.2 u hu⟩
        have hv₂_eq : o₂.value = L.rootId := by simp only [hv₂, hsub₁.1, ↓reduceIte, hsub₁.2.1]
        have hinv₂' : TourForestInv cap s₂ (optTrees (some L) ++ (AuxTree.node xid .leaf R :: rest)) := by
          simpa [hL_ne, optTrees] using hinv₂
        obtain ⟨y, L'?, s₃, o₃, st₃, c₃, hrun₃, hv₃, hn₃, hfr₃, hinv₃, hvals₃, hlist₃, hval₃, hout₃, hspec₃, hcost₃⟩ :=
          tourFindFirstBody_runs (pos := st₂.pos) C T hTc hR hdp ω hn₂ hinv₂' hvals₂ hfuel hfuelW
            (heapOk_of_frameN hheap (hfr₁.trans (hmem_sl ▸ hfr₂)))
        have hL_find_eq : L.toList.find? (fun u => rv (s₂.nodes u).val) = L.toList.find? (fun u => rv (st.nodes u).val) :=
          list_find?_congr fun u hu => by
            rw [hval₂ u (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, hu])).2,
                hval_sp u (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, hu])).2]
        obtain ⟨y₀, hy₀⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hL_ready)
        simp only [optList, Option.elim, hL_find_eq, hy₀] at hspec₃
        rcases hspec₃ with ⟨rfl, L', L_y, R_y, rfl, rfl, _, _⟩
        have hinv₃' : TourForestInv cap s₃
            (optTrees (some (AuxTree.node y L_y R_y)) ++ optTrees (some (AuxTree.node xid .leaf R)) ++ rest) := by
          simpa [optTrees] using hinv₃
        obtain ⟨t'?, s₄, o₄, st₄, c₄, hrun₄, hv₄, hn₄, hfr₄, hinv₄, hvals₄, hlist₄, hval₄, hout₄, hcost₄⟩ :=
          tourJoinBody_runs (pos := st₃.pos) C.toTourSplayOpsProcs ω hn₃ hinv₃' hvals₃ hfuel hfuelW
            (heapOk_of_frameN hheap (hfr₁.trans ((hmem_sl ▸ hfr₂).trans hfr₃)))
        cases t'? with
        | none => simp [optList, AuxTree.toList] at hlist₄
        | some t' =>
          have hne' : t' ≠ .leaf := hinv₄.nonEmpty t' (by simp [optTrees])
          have ht'_list : t'.toList = t.toList := by
            have hL' : (AuxTree.node y L_y R_y).toList = L.toList := by simpa [optList] using hlist₃
            simp only [optList, Option.elim] at hlist₄
            rw [hL'] at hlist₄
            rw [← hlist₁, hlist₄]; simp [AuxTree.toList, List.append_assoc]
          have hval_all : ∀ u ≤ cap, (s₄.nodes u).val = (st.nodes u).val := fun u hu => by
            exact (hval₄ u hu).trans ((hval₃ u hu).trans ((hval₂ u hu).trans (hval_sp u hu)))
          have hout_all : ∀ u ∉ t.toList, s₄.nodes u = st.nodes u := fun u hu => by
            have hu1 : u ∉ (AuxTree.node xid L R).toList := by rwa [hlist₁]
            have huL : u ∉ L.toList := fun h => hu1 (by simp [AuxTree.toList, h])
            have hL' : (AuxTree.node y L_y R_y).toList = L.toList := by simpa [optList] using hlist₃
            have hu4 : u ∉ optList (some (AuxTree.node y L_y R_y)) ++ optList (some (AuxTree.node xid .leaf R)) := by
              intro hm; apply hu1
              simp only [optList, Option.elim, List.mem_append] at hm
              rw [hL'] at hm
              rcases hm with h1 | h2
              · simp [AuxTree.toList, h1]
              · simp only [AuxTree.toList, List.nil_append, List.mem_append, List.mem_singleton] at h2
                rcases h2 with rfl | hR
                · simp [AuxTree.toList]
                · simp [AuxTree.toList, hR]
            exact (hout₄ u hu4).trans ((hout₃ u (by simpa [optList] using huL)).trans ((hout₂ u hu1).trans (hout₁ u hu)))
          have h17L_lt : 17 * L.rootId < 2 ^ w := by omega
          have hnb17L_lt : nb + 17 * L.rootId < 2 ^ w := by omega
          set s_sl : State := { st_sl with regs := Function.update r4 6 o_sl.value }
          set s_dl : State := { st₂ with regs := Function.update s_sl.regs 7 o₂.value }
          set s_ff : State := { st₃ with regs := Function.update s_dl.regs 8 o₃.value }
          set s_jn : State := { st₄ with regs := Function.update s_ff.regs 9 o₄.value }
          have hr4_5 : r4 5 = L.rootId := by simp [r4]
          have hcall_sl := tour_runs_call_of (r := 6) (args := [.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 5))])
            (st := ⟨st₁.mem, r4, pos_b1⟩) hb_sl
            (by simp only [evalArgs, Expr.eval, hr4_0, hr4_5, BinOp.eval, h17L_lt, hnb17L_lt,
              (by omega : 17 < 2 ^ w), ↓reduceIte]) hrun_sl
          have hcall_dl := runs_call_regs3 7 0 1 3 (st := s_sl) C.detachLeft_body (by simp [s_sl, hr4_0]) (by simp [s_sl, hr4_1]) (by simp [s_sl, hr4_3]) hrun₂
          have hcall_ff := runs_call_regs4 8 0 7 2 3 (st := s_dl) hfp (by simp [s_dl, s_sl, hr4_0]) (by simp [s_dl, hv₂_eq, optRoot]) (by simp [s_dl, s_sl, hr4_2]) (by simp [s_dl, s_sl, hr4_3]) hrun₃
          have hcall_jn := runs_call_regs5 9 0 8 1 2 3 (st := s_ff) C.join_body (by simp [s_ff, s_dl, s_sl, hr4_0]) (by simp [s_ff, hv₃, optRoot, AuxTree.rootId]) (by simp [s_ff, s_dl, s_sl, hr4_1, optRoot, AuxTree.rootId]) (by simp [s_ff, s_dl, s_sl, hr4_2]) (by simp [s_ff, s_dl, s_sl, hr4_3]) hrun₄
          have hret_y := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s_jn) (r := 8) (v := y) (by simp [s_jn, s_ff, hv₃])
          have hinner := tour_runs_seq_normal hcall_dl (tour_runs_seq_normal hcall_ff (tour_runs_seq_normal hcall_jn hret_y))
          have hcond6 := tour_runs_cond_true (e := .reg 6) (v := 1) (s₂ := .nop) (by simp [Expr.eval, s_sl, hsl_one]) (by omega) hinner
          have hcond5 := tour_runs_cond_true (e := .reg 5) (v := L.rootId) (s₂ := .nop) (by simp [Expr.eval, r4]) hL_nz (tour_runs_seq_normal hcall_sl hcond6)
          have hfull : ∃ c_fin, c_fin ≤ c₁ + c_b1 + c_sl + c₂ + c₃ + c₄ + 120 ∧
              Runs w p ω (tourNextReadyBody C.splay.splay C.detachLeft C.detachRight C.join fp T.sumTest T.valTest)
                (startState [nb, xid, fuel, heap] mem pos) (.returned y) s_jn c_fin := by
            unfold tourNextReadyBody
            exact ⟨_, by simp only [argsSize, Expr.size]; omega,
              tour_runs_seq_normal hc1_call (tour_runs_seq_normal hass4 (tour_runs_seq_normal hass5r
                (tour_runs_seq_normal hrun_b1 (tour_runs_seq_normal hass5l (runs_seq_ret hcond5)))))⟩
          obtain ⟨c_fin, hcfin, hfull⟩ := hfull
          refine ⟨y, t', s₄, .returned y, s_jn, c_fin, hfull, rfl, hn₄,
            hfr₁.trans ((hmem_sl ▸ hfr₂).trans (hfr₃.trans hfr₄)), by simpa [optTrees] using hinv₄,
            hvals₄, hne', ht'_list, hval_all, hout_all, ?_, ?_⟩
          · rw [hcyc_eq, List.append_assoc, List.find?_append, hR_find_none, List.find?_append, hy₀]; rfl
          · have hphi2' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₂
            simp only [hL_ne, ↓reduceIte, List.nil_append, List.cons_append] at hphi2'
            simp only [sumTestContract, hTc, TOUR_TEST_COST] at hc_sl
            simp only [optTrees, Option.toList, List.nil_append, List.cons_append,
              TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_FIND_AMORT, TOUR_JOIN_AMORT, TOUR_NEXT_AMORT, TOUR_TEST_COST] at hcost₁ hcost₃ hcost₄ hphi2' hc₂ hc_sl hc_b1 hcfin ⊢
            omega
      · have hL_find_none : L.toList.find? (fun u => rv (st.nodes u).val) = none :=
          List.find?_eq_none.mpr fun u hu hru => hL_ready ⟨u, hu, hru⟩
        have hbranch2 : ∃ r4' c_b2 pos_b2,
            Runs w p ω (.cond (.reg 5)
              (.call 6 T.sumTest [.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 5))] ;;
               .cond (.reg 6)
                 (.call 7 C.detachLeft [.reg 0, .reg 1, .reg 3] ;;
                  .call 8 fp [.reg 0, .reg 7, .reg 2, .reg 3] ;;
                  .call 9 C.join [.reg 0, .reg 8, .reg 1, .reg 2, .reg 3] ;;
                  .ret (.reg 8))
                 .nop)
              .nop)
              ⟨st₁.mem, r4, pos_b1⟩ .normal ⟨st₁.mem, r4', pos_b2⟩ c_b2 ∧
            (∀ i < 5, r4' i = r4 i) ∧ c_b2 ≤ TOUR_TEST_COST + 30 := by
          cases hLc : L with
          | leaf =>
            exact ⟨r4, _, pos_b1, tour_runs_cond_false (by simp [Expr.eval, r4, hLc, AuxTree.rootId])
              (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩), fun _ _ => rfl, by simp [Expr.size, TOUR_TEST_COST]⟩
          | node lid lL lR =>
            have hL_ne : L ≠ .leaf := by simp [hLc]
            have hL_nz : L.rootId ≠ 0 := by
              have h := hsub₁.2.2.2.2.2.2.2.1; rw [hLc] at h ⊢; exact h.1
            have hL_cap : L.rootId ≤ cap :=
              (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, AuxTree.rootId_mem hL_ne])).2
            have hAl : nb + 17 * L.rootId + 17 ≤ heap := by simpa [nodeAddr, tourLayout_stride] using hheap.addr_lt hL_cap
            have hL_rs0 : rs (s₁.nodes L.rootId).sum = false := by
              cases hrs : rs (s₁.nodes L.rootId).sum
              · rfl
              · exfalso; rcases (hchild_rs.1 hL_ne).mp hrs with ⟨u, hu, hru⟩
                rw [hval_sp u (hinv₁'.mem_inCap (t := AuxTree.node xid L R) (by simp) (by simp [AuxTree.toList, hu])).2] at hru
                exact hL_ready ⟨u, hu, hru⟩
            have hstL_pre : (sumTestContract tourLayout rs w T.cost).pre [nb + 17 * L.rootId] st₁.mem :=
              ⟨nb + 17 * L.rootId, (s₁.nodes L.rootId).val, (s₁.nodes L.rootId).sum, rfl,
                by rw [tourLayout_stride]; omega, (hn₁ L.rootId hL_cap).2.2.2.2.2.2.1,
                (hn₁ L.rootId hL_cap).2.2.2.2.2.2.2.1⟩
            obtain ⟨b_sl, hb_sl, o_sl, st_sl, c_sl, hrun_sl, ⟨hmem_sl, hval_sl⟩, hc_sl⟩ :=
              T.sum_ok [nb + 17 * L.rootId] st₁.mem pos_b1 ω (by simp; omega) hstL_pre
            have hsl_zero : o_sl.value = 0 := by
              simpa [hL_rs0] using hval_sl (s₁.nodes L.rootId).sum (hn₁ L.rootId hL_cap).2.2.2.2.2.2.2.1
            have h17L_lt : 17 * L.rootId < 2 ^ w := by omega
            have hnb17L_lt : nb + 17 * L.rootId < 2 ^ w := by omega
            have hr4_5 : r4 5 = L.rootId := by simp [r4]
            have hcall_sl := tour_runs_call_of (r := 6) (args := [.bin .add (.reg 0) (.bin .mul (.const 17) (.reg 5))])
              (st := ⟨st₁.mem, r4, pos_b1⟩) hb_sl
              (by simp only [evalArgs, Expr.eval, hr4_0, hr4_5, BinOp.eval, h17L_lt, hnb17L_lt,
                (by omega : 17 < 2 ^ w), ↓reduceIte]) hrun_sl
            have hcond6 := tour_runs_cond_false (w := w) (p := p) (ω := ω)
              (st := ⟨st_sl.mem, Function.update r4 6 o_sl.value, st_sl.pos⟩)
              (e := .reg 6) (s₁ := .call 7 C.detachLeft [.reg 0, .reg 1, .reg 3] ;;
                 .call 8 fp [.reg 0, .reg 7, .reg 2, .reg 3] ;;
                 .call 9 C.join [.reg 0, .reg 8, .reg 1, .reg 2, .reg 3] ;;
                 .ret (.reg 8))
              (by simp [Expr.eval, Function.update_self, hsl_zero]) (runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩)
            have hcond5 := tour_runs_cond_true (e := .reg 5) (v := L.rootId) (s₂ := .nop) (by simp [Expr.eval, r4]) hL_nz (tour_runs_seq_normal hcall_sl hcond6)
            refine ⟨Function.update r4 6 o_sl.value, _, st_sl.pos, by simpa [hmem_sl] using hcond5,
              fun i hi => by simp [show i ≠ 6 by omega], ?_⟩
            simp only [sumTestContract, hTc, TOUR_TEST_COST] at hc_sl
            simp only [TOUR_TEST_COST] at hc_sl ⊢; omega
        obtain ⟨r4', c_b2, pos_b2, hrun_b2, hr4'_eq, hc_b2⟩ := hbranch2
        have hval_pre : (valTestContract tourLayout rv w T.cost).pre [nb + 17 * xid + 6] st₁.mem :=
          ⟨nb + 17 * xid + 6, (s₁.nodes xid).val, rfl, by simp [tourLayout]; omega,
            by simpa [nodeAddr, OFF_VAL, tourLayout_stride] using (hn₁ xid hx_cap).2.2.2.2.2.2.1⟩
        obtain ⟨b_vx, hb_vx, o_vx, st_vx, c_vx, hrun_vx, ⟨hmem_vx, hval_vx⟩, hc_vx⟩ :=
          T.val_ok [nb + 17 * xid + 6] st₁.mem pos_b2 ω (by simp; omega) hval_pre
        have hvx_eq : o_vx.value = if rv (st.nodes xid).val then 1 else 0 := by
          have := hval_vx (s₁.nodes xid).val
            (by simpa [nodeAddr, OFF_VAL, tourLayout_stride] using (hn₁ xid hx_cap).2.2.2.2.2.2.1)
          rw [hval_sp xid hx_cap] at this; exact this
        have hnb17x6_lt : nb + 17 * xid + 6 < 2 ^ w := by omega
        have hcall_vx := tour_runs_call_of (r := 6) (args := [.bin .add (.reg 4) (.const 6)])
          (st := ⟨st₁.mem, r4', pos_b2⟩) hb_vx
          (by simp [evalArgs, Expr.eval, hr4'_eq 4 (by omega), hr4_4, BinOp.eval, hnb17x6_lt, (by omega : 6 < 2 ^ w)]) hrun_vx
        set s_vx : State := { st_vx with regs := Function.update r4' 6 o_vx.value }
        cases hrvx : rv (st.nodes xid).val with
        | true =>
          have hv1 : o_vx.value = 1 := by simp [hvx_eq, hrvx]
          have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := s_vx) (r := 1) (v := xid) (by simp [s_vx, hr4'_eq 1 (by omega), hr4_1])
          have hcond6 := tour_runs_cond_true (e := .reg 6) (v := 1) (s₂ := .ret (.const 0)) (by simp [Expr.eval, s_vx, hv1]) (by omega) hret
          have hfull : ∃ c_fin, c_fin ≤ c₁ + c_b1 + c_b2 + c_vx + 80 ∧
              Runs w p ω (tourNextReadyBody C.splay.splay C.detachLeft C.detachRight C.join fp T.sumTest T.valTest)
                (startState [nb, xid, fuel, heap] mem pos) (.returned xid) s_vx c_fin := by
            unfold tourNextReadyBody
            exact ⟨_, by simp only [argsSize, Expr.size]; omega,
              tour_runs_seq_normal hc1_call (tour_runs_seq_normal hass4 (tour_runs_seq_normal hass5r
                (tour_runs_seq_normal hrun_b1 (tour_runs_seq_normal hass5l
                  (tour_runs_seq_normal hrun_b2 (tour_runs_seq_normal hcall_vx hcond6))))))⟩
          obtain ⟨c_fin, hcfin, hfull⟩ := hfull
          refine ⟨xid, AuxTree.node xid L R, s₁, .returned xid, s_vx, c_fin, hfull, rfl,
            hmem_vx ▸ hn₁, hmem_vx ▸ hfr₁, hinv₁', hvals₁, by simp, hlist₁, hval_sp, hout₁, ?_, ?_⟩
          · rw [hcyc_eq, List.append_assoc, List.find?_append, hR_find_none, List.find?_append, hL_find_none]
            simp [hrvx]
          · simp only [valTestContract, hTc, TOUR_TEST_COST] at hc_vx
            simp only [List.nil_append, TOUR_PHI_MULT, TOUR_SPLAY_AMORT, TOUR_NEXT_AMORT, TOUR_TEST_COST] at hcost₁ hc_b1 hc_b2 hc_vx hcfin ⊢
            omega
        | false =>
          have hv0 : o_vx.value = 0 := by simp [hvx_eq, hrvx]
          have hret := runs_ret_const (w := w) (p := p) (ω := ω) (st := s_vx) (v := 0) (by omega)
          have hcond6 := tour_runs_cond_false (e := .reg 6) (s₁ := .ret (.reg 1)) (by simp [Expr.eval, s_vx, hv0]) hret
          have hfull : ∃ c_fin, c_fin ≤ c₁ + c_b1 + c_b2 + c_vx + 80 ∧
              Runs w p ω (tourNextReadyBody C.splay.splay C.detachLeft C.detachRight C.join fp T.sumTest T.valTest)
                (startState [nb, xid, fuel, heap] mem pos) (.returned 0) s_vx c_fin := by
            unfold tourNextReadyBody
            exact ⟨_, by simp only [argsSize, Expr.size]; omega,
              tour_runs_seq_normal hc1_call (tour_runs_seq_normal hass4 (tour_runs_seq_normal hass5r
                (tour_runs_seq_normal hrun_b1 (tour_runs_seq_normal hass5l
                  (tour_runs_seq_normal hrun_b2 (tour_runs_seq_normal hcall_vx hcond6))))))⟩
          obtain ⟨c_fin, hcfin, hfull⟩ := hfull
          refine ⟨0, AuxTree.node xid L R, s₁, .returned 0, s_vx, c_fin, hfull, rfl,
            hmem_vx ▸ hn₁, hmem_vx ▸ hfr₁, hinv₁', hvals₁, by simp, hlist₁, hval_sp, hout₁, ?_, ?_⟩
          · rw [hcyc_eq, List.append_assoc, List.find?_append, hR_find_none, List.find?_append, hL_find_none]
            simp [hrvx]
          · simp only [valTestContract, hTc, TOUR_TEST_COST] at hc_vx
            simp only [List.nil_append, TOUR_PHI_MULT, TOUR_SPLAY_AMORT, TOUR_NEXT_AMORT, TOUR_TEST_COST] at hcost₁ hc_b1 hc_b2 hc_vx hcfin ⊢
            omega

end MinCostFlow.SparseCore.Program
