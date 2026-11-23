module

public import MinCostFlow.SparseCore.Program.TourSplayZero
import Mathlib.Tactic

/-!
# Zero-scratch marked-node listing (`tourListMark0Body_runs`)

Verifies `tourListReadyBody` with `tourFindFirstMark0Body_runs` and `tourJoin0Body_runs` under
`HeapOk tourLayout w nb cap splayHeap 0 mem` (zero splay scratch above `splayHeap`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-- Zero-scratch `tourListReadyBody` for marked nodes under `HeapOk ... splayHeap 0 mem`. -/
theorem tourListMark0Body_runs {w nb cap splayHeap fuel keyBase outPtr pos walk0 dp0 j0 fp0 : ℕ}
    {p : Program} (C : TourSplayQueryProcs w p)
    (hw0 : p.procs[walk0]? = some tourWalk0Body)
    (hdp0 : p.procs[dp0]? = some tourDescMark0Body)
    (hj0 : p.procs[j0]? = some (tourJoinBody walk0 C.splay.loop C.attachLeft))
    (hfp0 : p.procs[fp0]? = some (tourFindFirstBody dp0 C.markTests.sumTest C.splay.loop))
    (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t? : Option AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (optTrees t? ++ rest)) (hvals : TourValsOk w cap st)
    (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap splayHeap 0 mem)
    (hkey_disj : ∀ u ≤ cap, keyBase + u < splayHeap ∧ ¬tourLayout.InRecords nb cap (keyBase + u))
    (hout_rec : ∀ i ≤ ((optList t?).filter fun u => (st.nodes u).val.isMarked).length,
      ¬tourLayout.InRecords nb cap (outPtr + i))
    (hout_key : ∀ u ≤ cap, ∀ i ≤ ((optList t?).filter fun u => (st.nodes u).val.isMarked).length,
      outPtr + i ≠ keyBase + u)
    (hout_heap : outPtr + 1 + ((optList t?).filter fun u => (st.nodes u).val.isMarked).length ≤ splayHeap) :
    ∃ t'? s' o st' c,
      let ready := (optList t?).filter fun u => (st.nodes u).val.isMarked
      Runs w p ω (tourListReadyBody fp0 C.detachRight j0)
        (startState [nb, optRoot t?, fuel, keyBase, outPtr, splayHeap] mem pos) o st' c ∧
      o.value = optRoot t'? ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TourForestInv cap s' (optTrees t'? ++ rest) ∧
      TourValsOk w cap s' ∧
      optList t'? = optList t? ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      (∀ u ∉ optList t?, s'.nodes u = st.nodes u) ∧
      st'.mem outPtr = ready.length ∧
      (∀ i < ready.length, st'.mem (outPtr + 1 + i) = mem (keyBase + ready.getD i 0)) ∧
      (∀ a ≥ splayHeap, st'.mem a = 0) ∧
      (∀ a < splayHeap, ¬tourLayout.InRecords nb cap a →
        (∀ i ≤ ready.length, a ≠ outPtr + i) → st'.mem a = mem a) ∧
      c + TOUR_PHI_MULT * forestPhi (optTrees t'? ++ rest) ≤
        TOUR_PHI_MULT * forestPhi (optTrees t? ++ rest) +
          (ready.length + 1) * TOUR_LIST_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  have hwide := hheap.wide; have hroom := hheap.room
  set ready := (optList t?).filter fun u => (st.nodes u).val.isMarked
  set lbody : Stmt :=
    .store (.bin .add (.bin .add (.reg 4) (.const 1)) (.reg 6))
        (.load (.bin .add (.reg 3) (.reg 9))) ;;
     .assign 6 (.bin .add (.reg 6) (.const 1)) ;;
     .call 10 C.detachRight [.reg 0, .reg 9, .reg 5] ;;
     .call 7 j0 [.reg 0, .reg 7, .reg 9, .reg 2, .reg 5] ;;
     .assign 8 (.reg 10) ;;
     .call 9 fp0 [.reg 0, .reg 8, .reg 2, .reg 5]
  have hloop : ∀ (k : ℕ) (done? cur? : Option AuxTree) (s : SplayState TourVal TourSum Unit)
      (M : ℕ → ℕ) (regs : ℕ → ℕ) (lpos cnt y : ℕ),
      ((optList cur?).filter fun u => (st.nodes u).val.isMarked).length = k →
      ready = (ready.take cnt) ++ ((optList cur?).filter fun u => (st.nodes u).val.isMarked) →
      cnt + k = ready.length →
      optList done? ++ optList cur? = optList t? →
      regs 0 = nb → regs 2 = fuel → regs 3 = keyBase → regs 4 = outPtr →
      regs 5 = splayHeap → regs 6 = cnt → regs 7 = optRoot done? → (y = 0 → regs 8 = optRoot cur?) → regs 9 = y →
      tourLayout.NodesAt M nb cap s →
      TourForestInv cap s (optTrees done? ++ optTrees cur? ++ rest) →
      TourValsOk w cap s →
      HeapOk tourLayout w nb cap splayHeap 0 M →
      (∀ u ≤ cap, (s.nodes u).val = (st.nodes u).val) →
      (∀ u ∉ optList t?, s.nodes u = st.nodes u) →
      (∀ i < cnt, M (outPtr + 1 + i) = mem (keyBase + ready.getD i 0)) →
      (∀ a < splayHeap, ¬tourLayout.InRecords nb cap a → (∀ i < cnt, a ≠ outPtr + 1 + i) → M a = mem a) →
      (match (optList cur?).find? (fun u => (st.nodes u).val.isMarked) with
        | none => y = 0
        | some y₀ => y = y₀ ∧ ∃ L R, cur? = some (AuxTree.node y L R) ∧
            (∀ u ∈ L.toList, (st.nodes u).val.isMarked = false) ∧ (st.nodes y).val.isMarked = true) →
      ∃ done₁? cur₁? s₁ st₁ c₁,
        Runs w p ω (.loop (.reg 9) lbody) ⟨M, regs, lpos⟩ .normal st₁ c₁ ∧
        st₁.regs 0 = nb ∧ st₁.regs 2 = fuel ∧ st₁.regs 4 = outPtr ∧ st₁.regs 5 = splayHeap ∧
        st₁.regs 6 = ready.length ∧ st₁.regs 7 = optRoot done₁? ∧ st₁.regs 8 = optRoot cur₁? ∧
        optList done₁? ++ optList cur₁? = optList t? ∧
        tourLayout.NodesAt st₁.mem nb cap s₁ ∧
        TourForestInv cap s₁ (optTrees done₁? ++ optTrees cur₁? ++ rest) ∧
        TourValsOk w cap s₁ ∧
        HeapOk tourLayout w nb cap splayHeap 0 st₁.mem ∧
        (∀ u ≤ cap, (s₁.nodes u).val = (st.nodes u).val) ∧
        (∀ u ∉ optList t?, s₁.nodes u = st.nodes u) ∧
        (∀ i < ready.length, st₁.mem (outPtr + 1 + i) = mem (keyBase + ready.getD i 0)) ∧
        (∀ a < splayHeap, ¬tourLayout.InRecords nb cap a → (∀ i < ready.length, a ≠ outPtr + 1 + i) → st₁.mem a = mem a) ∧
        c₁ + TOUR_PHI_MULT * forestPhi (optTrees done₁? ++ optTrees cur₁? ++ rest) ≤
          TOUR_PHI_MULT * forestPhi (optTrees done? ++ optTrees cur? ++ rest) +
            k * TOUR_LIST_AMORT * (Nat.log 2 (cap + 2) + 1) + 5 := by
    intro k
    induction k with
    | zero =>
      intro done? cur? s M regs lpos cnt y hk _ hcnt hlist hr0 hr2 _ hr4 hr5 hr6 hr7 hr8 hr9
        hNM hF hV hH hval hout hpre hframe hy_spec
      have hfil0 : (optList cur?).filter (fun u => (st.nodes u).val.isMarked) = [] := List.eq_nil_of_length_eq_zero hk
      have hfind0 : (optList cur?).find? (fun u => (st.nodes u).val.isMarked) = none :=
        List.find?_eq_none.mpr fun u hu hru => (List.filter_eq_nil_iff.mp hfil0 u hu) hru
      rw [hfind0] at hy_spec
      have hcnt_eq : cnt = ready.length := by omega
      refine ⟨done?, cur?, s, ⟨M, regs, lpos⟩, 2,
        runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, hr9, hy_spec], rfl, rfl, rfl⟩),
        hr0, hr2, hr4, hr5, by dsimp only; rw [hr6, hcnt_eq], hr7, hr8 hy_spec, hlist, hNM, hF, hV, hH, hval, hout,
        hcnt_eq ▸ hpre, hcnt_eq ▸ hframe, by omega⟩
    | succ k' ih =>
      intro done? cur? s M regs lpos cnt y hk hsplit hcnt hlist hr0 hr2 hr3 hr4 hr5 hr6 hr7 hr8 hr9
        hNM hF hV hH hval hout hpre hframe hy_spec
      have hne_fil : (optList cur?).filter (fun u => (st.nodes u).val.isMarked) ≠ [] := by
        intro hnil; rw [hnil] at hk; simp at hk
      have hex_ready : ∃ u ∈ optList cur?, (st.nodes u).val.isMarked = true := by
        obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hne_fil
        have := List.mem_filter.mp hu; exact ⟨u, this.1, this.2⟩
      obtain ⟨y₀, hy₀⟩ := Option.isSome_iff_exists.mp (List.find?_isSome.mpr hex_ready)
      rw [hy₀] at hy_spec
      rcases hy_spec with ⟨rfl, L, R, rfl, hL_false, hy_true⟩
      have hcur_mem : AuxTree.node y L R ∈ optTrees done? ++ optTrees (some (AuxTree.node y L R)) ++ rest := by
        simp [optTrees]
      have hy_cap : y ≤ cap := (hF.mem_inCap (t := AuxTree.node y L R) hcur_mem (by simp [AuxTree.toList])).2
      have hsub_y := (hF.treesInv (AuxTree.node y L R) hcur_mem).sub
      have hy_nz : y ≠ 0 := hsub_y.1
      have hfil_cur : (optList (some (AuxTree.node y L R))).filter (fun u => (st.nodes u).val.isMarked) =
          y :: R.toList.filter (fun u => (st.nodes u).val.isMarked) := by
        have hLf : L.toList.filter (fun u => (st.nodes u).val.isMarked) = [] :=
          List.filter_eq_nil_iff.mpr fun u hu hpu => by rw [hL_false u hu] at hpu; exact Bool.false_ne_true hpu
        simp [optList, Option.elim, AuxTree.toList, List.append_assoc, List.filter_append, hLf, hy_true]
      have hk'_eq : (R.toList.filter fun u => (st.nodes u).val.isMarked).length = k' := by
        rw [hfil_cur, List.length_cons] at hk; omega
      have hready_cnt : ready.getD cnt 0 = y := by
        have hlt_cnt : cnt < ready.length := by omega
        have hlen_take : (ready.take cnt).length = cnt := List.length_take_of_le (by omega)
        have h2 : ready = ready.take cnt ++ y :: R.toList.filter (fun u => (st.nodes u).val.isMarked) := by
          rw [← hfil_cur]; exact hsplit
        have hq : ready[cnt]? = some y := by
          conv_lhs => rw [h2]
          rw [List.getElem?_append_right (by omega), hlen_take, Nat.sub_self]; rfl
        simp [List.getD_eq_getElem?_getD, hq]
      have hkey_y : M (keyBase + y) = mem (keyBase + y) :=
        hframe (keyBase + y) (hkey_disj y hy_cap).1 (hkey_disj y hy_cap).2
          fun i hi => by rw [Nat.add_assoc]; exact Ne.symm (hout_key y hy_cap (1 + i) (by omega))
      have hkey_lt : keyBase + y < 2 ^ w := by have := (hkey_disj y hy_cap).1; omega
      set M₁ := Function.update M (outPtr + 1 + cnt) (mem (keyBase + y))
      have hstore_run : Runs w p ω
          (.store (.bin .add (.bin .add (.reg 4) (.const 1)) (.reg 6))
            (.load (.bin .add (.reg 3) (.reg 9))))
          ⟨M, regs, lpos⟩ .normal ⟨M₁, regs, lpos⟩ 10 := by
        refine runs_store_iff.mpr ⟨outPtr + 1 + cnt, mem (keyBase + y), ?_, ?_, rfl, rfl, rfl⟩
        · simp [Expr.eval, hr4, hr6, BinOp.eval, (by omega : outPtr + 1 < 2 ^ w),
            (by omega : outPtr + 1 + cnt < 2 ^ w), (by omega : 1 < 2 ^ w)]
        · rw [← hkey_y]; simp [Expr.eval, hr3, hr9, BinOp.eval, hkey_lt]
      have hNM₁ : tourLayout.NodesAt M₁ nb cap s :=
        NodesAt.congr tourLayout hNM fun a ha => by
          dsimp only [M₁]; rw [Function.update_of_ne]
          intro heq; exact hout_rec (1 + cnt) (by omega) (by rw [← Nat.add_assoc, ← heq]; exact ha)
      have hH₁ : HeapOk tourLayout w nb cap splayHeap 0 M₁ :=
        ⟨hH.rec_le, hH.room, fun a ha => by dsimp only [M₁]; rw [Function.update_of_ne (by omega)]; exact hH.zero a ha, hH.wide⟩
      set regs₁ := Function.update regs 6 (cnt + 1)
      have hass6_run : Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 1)))
          ⟨M₁, regs, lpos⟩ .normal ⟨M₁, regs₁, lpos⟩ 4 :=
        runs_assign_iff.mpr ⟨cnt + 1, by simp [Expr.eval, hr6, BinOp.eval, (by omega : cnt + 1 < 2 ^ w), (by omega : 1 < 2 ^ w)], rfl, rfl, rfl⟩
      have hF_dr : TourForestInv cap s (optTrees done? ++ AuxTree.node y L R :: rest) := by
        simpa [optTrees] using hF
      obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hv₂, hn₂, hfr₂⟩, hc₂⟩ := tourDetachRightBody_runs (pos := lpos)
        C.toTourSplayCoreProcs ω hNM₁ hF_dr.ptrOk hy_cap hH₁ (tourDetachRight_sumOk hF_dr hV)
      obtain ⟨hF₂, hout₂, hval₂, hphi₂⟩ := tourDetachRight_preserves hF_dr
      set s₂ := tourDetachRight s y
      have hV₂ : TourValsOk w cap s₂ := ⟨hV.1, fun u hu => by rw [hval₂ u hu]; exact hV.2 u hu⟩
      let R? : Option AuxTree := if R = .leaf then none else some R
      have hR_root : o₂.value = optRoot R? := by
        simp only [hv₂, hy_nz, ↓reduceIte, hsub_y.2.2.1]; cases R <;> simp [R?, optRoot, AuxTree.rootId]
      have hR_list : optList R? = R.toList := by cases R <;> simp [R?, optList, AuxTree.toList]
      have hF₂' : TourForestInv cap s₂ (optTrees done? ++ optTrees (some (AuxTree.node y L .leaf)) ++ (optTrees R? ++ rest)) := by
        cases R <;> simpa [R?, optTrees, List.append_assoc] using hF₂
      obtain ⟨done'?, s₃, o₃, st₃, c₃, hrun₃, hv₃, hn₃, hfr₃, hF₃, hV₃, hlist₃, hval₃, hout₃, hcost₃⟩ :=
        tourJoin0Body_runs (pos := st₂.pos) C.toTourSplayOpsProcs hw0 ω hn₂ hF₂' hV₂ hfuel hfuelW
          (heapOk0_of_frame hH₁ hfr₂)
      have hperm₃ : (optTrees done'? ++ (optTrees R? ++ rest)).Perm (optTrees R? ++ (optTrees done'? ++ rest)) := by
        rw [← List.append_assoc, ← List.append_assoc]; exact List.Perm.append_right rest List.perm_append_comm
      obtain ⟨y', R'?, s₄, o₄, st₄, c₄, hrun₄, hv₄, hn₄, hfr₄, hF₄, hV₄, hlist₄, hval₄, hout₄, hspec₄, hcost₄⟩ :=
        tourFindFirstMark0Body_runs (pos := st₃.pos) C hdp0 ω hn₃ (hF₃.perm hperm₃).1 hV₃ hfuel hfuelW
          (heapOk0_of_frame hH₁ (hfr₂.trans hfr₃))
      have hperm₄ : (optTrees R'? ++ (optTrees done'? ++ rest)).Perm (optTrees done'? ++ optTrees R'? ++ rest) := by
        rw [← List.append_assoc]; exact List.Perm.append_right rest List.perm_append_comm
      have hval_all : ∀ u ≤ cap, (s₄.nodes u).val = (st.nodes u).val := fun u hu => by
        rw [hval₄ u hu, hval₃ u hu, hval₂ u hu, hval u hu]
      have hfr_all : TreeFrame tourLayout nb cap splayHeap M₁ st₄.mem := hfr₂.trans (hfr₃.trans hfr₄)
      have hpre_next : ∀ i < cnt + 1, st₄.mem (outPtr + 1 + i) = mem (keyBase + ready.getD i 0) := by
        intro i hi
        have hnotrec : ¬tourLayout.InRecords nb cap (outPtr + 1 + i) := by
          rw [Nat.add_assoc]; exact hout_rec (1 + i) (by omega)
        rw [hfr_all.2 _ (by omega) hnotrec]
        by_cases hic : i = cnt
        · subst hic; rw [hready_cnt]; simp [M₁]
        · rw [show M₁ (outPtr + 1 + i) = M (outPtr + 1 + i) from by dsimp only [M₁]; exact Function.update_of_ne (by omega) _ _]
          exact hpre i (by omega)
      have hframe_next : ∀ a < splayHeap, ¬tourLayout.InRecords nb cap a →
          (∀ i < cnt + 1, a ≠ outPtr + 1 + i) → st₄.mem a = mem a := by
        intro a ha hnr hne
        rw [hfr_all.2 a ha hnr, show M₁ a = M a from by dsimp only [M₁]; exact Function.update_of_ne (hne cnt (by omega)) _ _]
        exact hframe a ha hnr fun i hi => hne i (by omega)
      have hlist_next : optList done'? ++ optList R'? = optList t? := by
        rw [hlist₄, hlist₃, hR_list, List.append_assoc]
        simpa [optList, AuxTree.toList, List.append_assoc] using hlist
      have hsplit_next : ready = ready.take (cnt + 1) ++ ((optList R'?).filter fun u => (st.nodes u).val.isMarked) := by
        have hlt_cnt : cnt < ready.length := by omega
        have htake : ready.take (cnt + 1) = ready.take cnt ++ [y] := by
          rw [List.take_succ_eq_append_getElem hlt_cnt]
          have : ready[cnt]'hlt_cnt = y := by simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_cnt] using hready_cnt
          rw [this]
        rw [htake, List.append_assoc, List.singleton_append, hlist₄, hR_list]
        simpa [hfil_cur] using hsplit
      have hout_next : ∀ u ∉ optList t?, s₄.nodes u = st.nodes u := by
        intro u hu
        have hu_y : u ∉ (AuxTree.node y L R).toList := fun hm => hu (by rw [← hlist]; simp [optList, hm])
        have hu_d : u ∉ optList done? := fun hm => hu (by rw [← hlist]; simp [hm])
        have hu_R : u ∉ optList R? := fun hm => hu_y (by rw [hR_list] at hm; simp [AuxTree.toList, hm])
        have hu_jn : u ∉ optList done? ++ optList (some (AuxTree.node y L .leaf)) := by
          intro hm; rcases List.mem_append.mp hm with h1 | h2
          · exact hu_d h1
          · apply hu_y; simp only [optList, Option.elim, AuxTree.toList, List.append_nil, List.mem_append, List.mem_singleton] at h2 ⊢
            rcases h2 with hL | rfl; exact Or.inl (Or.inl hL); exact Or.inl (Or.inr rfl)
        exact (hout₄ u hu_R).trans ((hout₃ u hu_jn).trans ((hout₂ u hu_y).trans (hout u hu)))
      have hy'_spec : match (optList R'?).find? (fun u => (st.nodes u).val.isMarked) with
          | none => y' = 0
          | some y₀ => y' = y₀ ∧ ∃ L' R', R'? = some (AuxTree.node y' L' R') ∧
              (∀ u ∈ L'.toList, (st.nodes u).val.isMarked = false) ∧ (st.nodes y').val.isMarked = true := by
        have hfeq : (optList R?).find? (fun u => (s₃.nodes u).val.isMarked) =
            (optList R'?).find? (fun u => (st.nodes u).val.isMarked) := by
          rw [hlist₄]
          refine list_find?_congr fun u hu => ?_
          have hu_cap : u ≤ cap := by
            rw [hR_list] at hu
            exact (hF.mem_inCap (t := AuxTree.node y L R) hcur_mem (by simp [AuxTree.toList, hu])).2
          rw [hval₃ u hu_cap, hval₂ u hu_cap, hval u hu_cap]
        rw [hfeq] at hspec₄
        cases hf_r : (optList R'?).find? (fun u => (st.nodes u).val.isMarked) with
        | none => rw [hf_r] at hspec₄; exact hspec₄.1
        | some y₀ =>
          rw [hf_r] at hspec₄
          rcases hspec₄ with ⟨rfl, t', L', R', ht'eq, rfl, hL'f, hy't⟩
          refine ⟨rfl, L', R', ht'eq, fun u hu => ?_, ?_⟩
          · have hu_cap : u ≤ cap := (hF₄.mem_inCap (t := AuxTree.node y' L' R') (by simp [optTrees, ht'eq]) (by simp [AuxTree.toList, hu])).2
            rw [← hL'f u hu, hval₃ u hu_cap, hval₂ u hu_cap, hval u hu_cap]
          · have hy'_cap : y' ≤ cap := (hF₄.mem_inCap (t := AuxTree.node y' L' R') (by simp [optTrees, ht'eq]) (by simp [AuxTree.toList])).2
            rw [← hy't, hval₃ y' hy'_cap, hval₂ y' hy'_cap, hval y' hy'_cap]
      set regs₂ := Function.update regs₁ 10 o₂.value
      set regs₃ := Function.update regs₂ 7 o₃.value
      set regs₄ := Function.update regs₃ 8 o₂.value
      set regs₅ := Function.update regs₄ 9 o₄.value
      obtain ⟨done₁?, cur₁?, s₁, st₁, c_rem, hrun_rem, hr10, hr12, hr14, hr15, hr16, hr17, hr18,
        hlist_fin, hn_fin, hF_fin, hV_fin, hH_fin, hval_fin, hout_fin, hpre_fin, hfr_fin, hcost_rem⟩ :=
        ih done'? R'? s₄ st₄.mem regs₅ st₄.pos (cnt + 1) y'
          (by rw [hlist₄, hR_list]; exact hk'_eq) hsplit_next (by omega) hlist_next
          (by simp [regs₅, regs₄, regs₃, regs₂, regs₁, hr0])
          (by simp [regs₅, regs₄, regs₃, regs₂, regs₁, hr2])
          (by simp [regs₅, regs₄, regs₃, regs₂, regs₁, hr3])
          (by simp [regs₅, regs₄, regs₃, regs₂, regs₁, hr4])
          (by simp [regs₅, regs₄, regs₃, regs₂, regs₁, hr5])
          (by simp [regs₅, regs₄, regs₃, regs₂, regs₁])
          (by simp [regs₅, regs₄, regs₃, hv₃])
          (fun hy'0 => by
            have hR'_eq : R'? = R? := by
              cases hfr : (optList R?).find? (fun u => (s₃.nodes u).val.isMarked) with
              | none => rw [hfr] at hspec₄; exact hspec₄.2.1
              | some y₀ =>
                rw [hfr] at hspec₄
                rcases hspec₄ with ⟨rfl, t', L', R', ht'eq, rfl, _, _⟩
                have hnz := (hF₄.treesInv (AuxTree.node y' L' R') (by simp [optTrees, ht'eq])).sub.1
                exact absurd hy'0 hnz
            simp [regs₅, regs₄, hR_root, hR'_eq])
          (by simp [regs₅, hv₄])
          hn₄ (hF₄.perm hperm₄).1 hV₄ (heapOk0_of_frame hH₁ hfr_all) hval_all hout_next
          hpre_next hframe_next hy'_spec
      have hcall2 := runs_call_regs3 10 0 9 5 (st := ⟨M₁, regs₁, lpos⟩) C.detachRight_body
        (by simp [regs₁, hr0]) (by simp [regs₁, hr9]) (by simp [regs₁, hr5]) hrun₂
      have hcall3 := runs_call_regs5 7 0 7 9 2 5 (st := ⟨st₂.mem, regs₂, st₂.pos⟩) hj0
        (by simp [regs₂, regs₁, hr0]) (by simp [regs₂, regs₁, hr7]) (by simp [regs₂, regs₁, hr9, optRoot, AuxTree.rootId])
        (by simp [regs₂, regs₁, hr2]) (by simp [regs₂, regs₁, hr5]) hrun₃
      have hass8 : Runs w p ω (.assign 8 (.reg 10)) ⟨st₃.mem, regs₃, st₃.pos⟩ .normal ⟨st₃.mem, regs₄, st₃.pos⟩ 2 :=
        runs_assign_iff.mpr ⟨o₂.value, by simp [Expr.eval, regs₃, regs₂], rfl, rfl, rfl⟩
      have hcall4 := runs_call_regs4 9 0 8 2 5 (st := ⟨st₃.mem, regs₄, st₃.pos⟩) hfp0
        (by simp [regs₄, regs₃, regs₂, regs₁, hr0]) (by simp [regs₄, hR_root])
        (by simp [regs₄, regs₃, regs₂, regs₁, hr2]) (by simp [regs₄, regs₃, regs₂, regs₁, hr5]) hrun₄
      have hiter := tour_runs_seq_normal hstore_run (tour_runs_seq_normal hass6_run (tour_runs_seq_normal hcall2
        (tour_runs_seq_normal hcall3 (tour_runs_seq_normal hass8 hcall4))))
      have hloop_run := runs_loop_iff.mpr (Or.inr (Or.inr ⟨y, ⟨st₄.mem, regs₅, st₄.pos⟩, _, c_rem,
        by simp [Expr.eval, hr9], hy_nz, hiter, hrun_rem, rfl⟩))
      refine ⟨done₁?, cur₁?, s₁, st₁, _, hloop_run, hr10, hr12, hr14, hr15, hr16, hr17, hr18,
        hlist_fin, hn_fin, hF_fin, hV_fin, hH_fin, hval_fin, hout_fin, hpre_fin, hfr_fin, ?_⟩
      have hphi2' := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₂
      have hpeq3 := forestPhi_perm hperm₃; have hpeq4 := forestPhi_perm hperm₄
      have hphi2_eq : forestPhi (optTrees done? ++ optTrees (some (AuxTree.node y L .leaf)) ++ (optTrees R? ++ rest)) =
          forestPhi (optTrees done? ++ (AuxTree.node y L .leaf :: if R = .leaf then [] else [R]) ++ rest) := by
        cases R <;> simp [R?, optTrees, List.append_assoc]
      rw [← hpeq4] at hcost_rem; rw [← hpeq3] at hcost₄; rw [hphi2_eq] at hcost₃
      have hmul : (k' + 1) * TOUR_LIST_AMORT * (Nat.log 2 (cap + 2) + 1) =
          k' * TOUR_LIST_AMORT * (Nat.log 2 (cap + 2) + 1) + TOUR_LIST_AMORT * (Nat.log 2 (cap + 2) + 1) := by ring
      rw [hmul]
      simp only [optTrees, Option.toList, List.append_assoc, List.nil_append, List.cons_append, Expr.size,
        TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_JOIN_AMORT, TOUR_FIND_AMORT, TOUR_LIST_AMORT] at hcost_rem hcost₄ hcost₃ hphi2' hc₂ ⊢
      omega
  unfold tourListReadyBody; rw [startState]
  set r0 := fun i => [nb, optRoot t?, fuel, keyBase, outPtr, splayHeap].getD i 0
  set r1 := Function.update r0 6 0
  set r2 := Function.update r1 7 0
  set r3 := Function.update r2 8 (optRoot t?)
  have ha6 : Runs w p ω (.assign 6 (.const 0)) ⟨mem, r0, pos⟩ .normal ⟨mem, r1, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
  have ha7 : Runs w p ω (.assign 7 (.const 0)) ⟨mem, r1, pos⟩ .normal ⟨mem, r2, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, (by omega : 0 < 2 ^ w)], rfl, rfl, rfl⟩
  have ha8 : Runs w p ω (.assign 8 (.reg 1)) ⟨mem, r2, pos⟩ .normal ⟨mem, r3, pos⟩ 2 :=
    runs_assign_iff.mpr ⟨optRoot t?, by simp [Expr.eval, r2, r1, r0], rfl, rfl, rfl⟩
  obtain ⟨y0, t0?, s0, o0, st0, c0, hrun0, hv0, hn0, hfr0, hF0, hV0, hlist0, hval0, hout0, hspec0, hcost0⟩ :=
    tourFindFirstMark0Body_runs (pos := pos) C hdp0 ω hnodes hf hvals hfuel hfuelW hheap
  have hcall0 := runs_call_regs4 9 0 8 2 5 (st := ⟨mem, r3, pos⟩) hfp0
    (by simp [r3, r2, r1, r0]) (by simp [r3]) (by simp [r3, r2, r1, r0]) (by simp [r3, r2, r1, r0]) hrun0
  have hy0_spec : match (optList t0?).find? (fun u => (st.nodes u).val.isMarked) with
      | none => y0 = 0
      | some y' => y0 = y' ∧ ∃ L R, t0? = some (AuxTree.node y0 L R) ∧
          (∀ u ∈ L.toList, (st.nodes u).val.isMarked = false) ∧ (st.nodes y0).val.isMarked = true := by
    rw [hlist0]
    cases hf0 : (optList t?).find? (fun u => (st.nodes u).val.isMarked) with
    | none => rw [hf0] at hspec0; exact hspec0.1
    | some y' =>
      rw [hf0] at hspec0; rcases hspec0 with ⟨rfl, t', L, R, ht'eq, rfl, hLf, hyt⟩
      exact ⟨rfl, L, R, ht'eq, hLf, hyt⟩
  obtain ⟨done₁?, cur₁?, s₁, st₁, c_lp, hrun_lp, hr10, hr12, hr14, hr15, hr16, hr17, hr18,
    hlist_lp, hn_lp, hF_lp, hV_lp, hH_lp, hval_lp, hout_lp, hpre_lp, hfr_lp, hcost_lp⟩ :=
    hloop ready.length none t0? s0 st0.mem (Function.update r3 9 o0.value) st0.pos 0 y0
      (by simp only [ready, hlist0]) (by simp only [ready, hlist0, List.take_zero, List.nil_append]) (by omega)
      (by rw [show optList none = [] from rfl, List.nil_append]; exact hlist0)
      (by simp [r3, r2, r1, r0]) (by simp [r3, r2, r1, r0]) (by simp [r3, r2, r1, r0])
      (by simp [r3, r2, r1, r0]) (by simp [r3, r2, r1, r0]) (by simp [r3, r2, r1])
      (by simp [r3, r2, optRoot])
      (fun hy00 => by
        have ht0_eq : t0? = t? := by
          cases hf0 : (optList t?).find? (fun u => (st.nodes u).val.isMarked) with
          | none => rw [hf0] at hspec0; exact hspec0.2.1
          | some y' =>
            rw [hf0] at hspec0
            rcases hspec0 with ⟨rfl, t', L, R, ht'eq, rfl, _, _⟩
            have hnz := (hF0.treesInv (AuxTree.node y0 L R) (by simp [optTrees, ht'eq])).sub.1
            exact absurd hy00 hnz
        simp [r3, r2, r1, r0, ht0_eq])
      (by simp [hv0])
      hn0 (by simpa [optTrees] using hF0) hV0 (heapOk0_of_frame hheap hfr0) hval0 hout0
      (fun _ hi => by omega) (fun a ha hnr _ => hfr0.2 a ha hnr) hy0_spec
  obtain ⟨t'?, s₂, o₂, st₂, c₂, hrun₂, hv₂, hn₂, hfr₂, hF₂, hV₂, hlist₂, hval₂, hout₂, hcost₂⟩ :=
    tourJoin0Body_runs (pos := st₁.pos) C.toTourSplayOpsProcs hw0 ω hn_lp hF_lp hV_lp hfuel hfuelW hH_lp
  have hcall_fin := runs_call_regs5 10 0 7 8 2 5 (st := st₁) hj0 hr10 hr17 hr18 hr12 hr15 hrun₂
  set st_fin0 : State := { st₂ with regs := Function.update st₁.regs 10 o₂.value }
  set M_fin := Function.update st₂.mem outPtr ready.length
  have hst_out : Runs w p ω (.store (.reg 4) (.reg 6)) st_fin0 .normal { st_fin0 with mem := M_fin } 3 :=
    runs_store_iff.mpr ⟨outPtr, ready.length,
      by simp [Expr.eval, st_fin0, hr14], by simp [Expr.eval, st_fin0, hr16], rfl, rfl, rfl⟩
  have hret_fin : Runs w p ω (.ret (.reg 10)) { st_fin0 with mem := M_fin } (.returned (optRoot t'?)) { st_fin0 with mem := M_fin } 2 :=
    runs_ret_iff.mpr ⟨optRoot t'?, by simp [Expr.eval, st_fin0, hv₂], rfl, rfl, rfl⟩
  have hfull := tour_runs_seq_normal ha6 (tour_runs_seq_normal ha7 (tour_runs_seq_normal ha8
    (tour_runs_seq_normal hcall0 (tour_runs_seq_normal hrun_lp (tour_runs_seq_normal hcall_fin
      (tour_runs_seq_normal hst_out hret_fin))))))
  have hn_fin : tourLayout.NodesAt M_fin nb cap s₂ :=
    NodesAt.congr tourLayout hn₂ fun a ha => by
      dsimp only [M_fin]; rw [Function.update_of_ne]
      intro heq; exact hout_rec 0 (Nat.zero_le _) (by simpa [← heq] using ha)
  refine ⟨t'?, s₂, .returned (optRoot t'?), _, _, hfull, rfl, hn_fin, hF₂, hV₂,
    hlist₂.trans hlist_lp, fun u hu => (hval₂ u hu).trans (hval_lp u hu),
    fun u hu => (hout₂ u (by rwa [hlist_lp])).trans (hout_lp u hu),
    by simp [M_fin], fun i hi => ?_, fun a ha => ?_, fun a ha hnr hne => ?_, ?_⟩
  · dsimp only
    rw [show M_fin (outPtr + 1 + i) = st₂.mem (outPtr + 1 + i) from by dsimp only [M_fin]; exact Function.update_of_ne (by omega) _ _]
    rw [hfr₂.2 _ (by omega) (by rw [Nat.add_assoc]; exact hout_rec (1 + i) (by omega))]
    exact hpre_lp i hi
  · dsimp only
    rw [show M_fin a = st₂.mem a from by dsimp only [M_fin]; exact Function.update_of_ne (by omega) _ _]
    exact hfr₂.1 a ha
  · dsimp only
    rw [show M_fin a = st₂.mem a from by dsimp only [M_fin]; exact Function.update_of_ne (by simpa using hne 0 (Nat.zero_le _)) _ _]
    rw [hfr₂.2 a ha hnr]
    exact hfr_lp a ha hnr fun i hi => by rw [Nat.add_assoc]; exact hne (1 + i) (by omega)
  · have hmul : (ready.length + 1) * TOUR_LIST_AMORT * (Nat.log 2 (cap + 2) + 1) =
        ready.length * TOUR_LIST_AMORT * (Nat.log 2 (cap + 2) + 1) +
        TOUR_LIST_AMORT * (Nat.log 2 (cap + 2) + 1) := by ring
    rw [hmul]
    simp only [optTrees, Option.toList, List.nil_append,
      TOUR_PHI_MULT, TOUR_FIND_AMORT, TOUR_JOIN_AMORT, TOUR_LIST_AMORT] at hcost0 hcost_lp hcost₂ ⊢
    omega

end MinCostFlow.SparseCore.Program
