module

public import MinCostFlow.SparseCore.Program.TourSplayOps
import Mathlib.Tactic

/-!
# Splay-level cut-split and link-splice subroutines

Builds and verifies the two pure splay-forest structural subroutines shared by Op `1` (`cut`),
Op `2` (`link`), and `TourInit`:
- `tourCutSplitBody`: splits a tree `t` containing distinct `nx, ny` into `t1` (`nx :: Q`) and
  `t2` (`A ++ [ny]`) where `rotateNatList nx t.toList = nx :: A ++ ny :: Q`.
- `tourLinkSpliceBody`: splices two distinct trees `tx` (`Px ++ nx :: Qx`) and `ty`
  (`Py ++ ny :: Qy`) into one tree `t'` (`Px ++ nx :: Qy ++ Py ++ ny :: Qx`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.PathProg NodeLayout SplayState

/-! ## Amortized constants and WordRAM bodies -/

/-- Amortized per-`log` cost constant for `tourCutSplitBody`. -/
def TOUR_CUTSPLIT_AMORT : ℕ := 700000

/-- Amortized per-`log` cost constant for `tourLinkSpliceBody`. -/
def TOUR_LINKSPLICE_AMORT : ℕ := 800000

/-- `tourCutSplit [nb, nx, ny, fuel, heap]`: splits `nx, ny`'s tree into `nx :: Q` and `A ++ [ny]`. -/
def tourCutSplitBody (splayProc detachLeftProc detachRightProc joinProc rotateFrontProc : ℕ) : Stmt :=
  .call 5 rotateFrontProc [.reg 0, .reg 1, .reg 3, .reg 4] ;;
  .call 5 splayProc [.reg 0, .reg 2, .reg 3, .reg 4] ;;
  .call 5 detachLeftProc [.reg 0, .reg 2, .reg 4] ;;
  .call 6 detachRightProc [.reg 0, .reg 2, .reg 4] ;;
  .call 7 splayProc [.reg 0, .reg 1, .reg 3, .reg 4] ;;
  .call 7 detachRightProc [.reg 0, .reg 1, .reg 4] ;;
  .call 8 joinProc [.reg 0, .reg 1, .reg 6, .reg 3, .reg 4] ;;
  .call 9 joinProc [.reg 0, .reg 7, .reg 2, .reg 3, .reg 4] ;;
  .ret (.const 0)

/-- `tourLinkSplice [nb, nx, ny, fuel, heap]`: splices `tx` (`Px ++ nx :: Qx`) and `ty`
(`Py ++ ny :: Qy`) into `Px ++ nx :: Qy ++ Py ++ ny :: Qx`, returning the new root. -/
def tourLinkSpliceBody (splayProc detachLeftProc detachRightProc joinProc : ℕ) : Stmt :=
  .call 5 splayProc [.reg 0, .reg 1, .reg 3, .reg 4] ;;
  .call 5 detachLeftProc [.reg 0, .reg 1, .reg 4] ;;
  .call 6 detachRightProc [.reg 0, .reg 1, .reg 4] ;;
  .call 7 splayProc [.reg 0, .reg 2, .reg 3, .reg 4] ;;
  .call 7 detachLeftProc [.reg 0, .reg 2, .reg 4] ;;
  .call 8 detachRightProc [.reg 0, .reg 2, .reg 4] ;;
  .call 9 joinProc [.reg 0, .reg 5, .reg 1, .reg 3, .reg 4] ;;
  .call 9 joinProc [.reg 0, .reg 9, .reg 8, .reg 3, .reg 4] ;;
  .call 9 joinProc [.reg 0, .reg 9, .reg 7, .reg 3, .reg 4] ;;
  .call 9 joinProc [.reg 0, .reg 9, .reg 2, .reg 3, .reg 4] ;;
  .call 9 joinProc [.reg 0, .reg 9, .reg 6, .reg 3, .reg 4] ;;
  .ret (.reg 9)

theorem tourSplayCutLink_bodies_noRand (sP dL dR jP rfP : ℕ) :
    (tourCutSplitBody sP dL dR jP rfP).NoRand ∧
    (tourLinkSpliceBody sP dL dR jP).NoRand := by
  simp [tourCutSplitBody, tourLinkSpliceBody, Stmt.NoRand]

/-! ## Private helpers -/

private theorem heapOk_frame {nb cap heap sp w : ℕ} {mem M : ℕ → ℕ}
    (hheap : HeapOk tourLayout w nb cap heap sp mem)
    (hfr : TreeFrame tourLayout nb cap heap mem M) :
    HeapOk tourLayout w nb cap heap sp M :=
  ⟨hheap.rec_le, hheap.room, hfr.1, hheap.wide⟩

private theorem heapOk_zero' {nb cap heap sp w : ℕ} {mem : ℕ → ℕ}
    (hheap : HeapOk tourLayout w nb cap heap sp mem) :
    HeapOk tourLayout w nb cap heap 0 mem :=
  ⟨hheap.rec_le, by have := hheap.room; omega, hheap.zero, hheap.wide⟩

private theorem optList_of_ite (t : AuxTree) :
    optList (if t = .leaf then none else some t) = t.toList := by
  cases t <;> simp [optList, AuxTree.toList]

private theorem optTrees_of_ite (t : AuxTree) :
    optTrees (if t = .leaf then none else some t) = if t = .leaf then [] else [t] := by
  cases t <;> simp [optTrees]

private theorem optRoot_of_ite (t : AuxTree) :
    optRoot (if t = .leaf then none else some t) = t.rootId := by
  cases t <;> simp [optRoot, AuxTree.rootId]

private theorem rotateNatList_head_eq {x : ℕ} {L : List ℕ} (hx : x ∈ L) :
    (rotateNatList x L).head? = some x := by
  unfold rotateNatList
  simp only [hx, ↓reduceIte]
  have hlt : L.idxOf x < L.length := List.idxOf_lt_length_of_mem hx
  have hne : L.drop (L.idxOf x) ≠ [] := by
    intro h0; have := congrArg List.length h0; simp at this; omega
  rw [List.head?_append_of_ne_nil _ hne, List.head?_drop, List.getElem?_eq_getElem hlt,
    List.getElem_idxOf hlt]

theorem rotateNatList_perm {x : ℕ} {L : List ℕ} (hx : x ∈ L) :
    (rotateNatList x L).Perm L := by
  unfold rotateNatList; simp only [hx, ↓reduceIte]
  exact List.perm_append_comm.trans (by rw [List.take_append_drop])

private theorem rotateNatList_isRotated {x : ℕ} {L : List ℕ} (hx : x ∈ L) :
    (rotateNatList x L).IsRotated L := by
  unfold rotateNatList; simp only [hx, ↓reduceIte]
  exact List.isRotated_append.symm.trans (by rw [List.take_append_drop])

/-! ## Amortized run theorem for `tourCutSplitBody` -/

/-- Running `tourCutSplitBody` on a tree `t` containing distinct `nx, ny` splits `t` into
`t1` (`nx :: Q`) and `t2` (`A ++ [ny]`) where `rotateNatList nx t.toList = nx :: A ++ ny :: Q`. -/
theorem tourCutSplitBody_runs {w nb cap heap fuel nx ny pos : ℕ} {p : Program}
    (C : TourSplayOpsProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {t : AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (t :: rest)) (hvals : TourValsOk w cap st)
    (hnx : nx ∈ t.toList) (hny : ny ∈ t.toList) (hne : nx ≠ ny)
    (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ t1 t2 A Q s' o st' c,
      Runs w p ω (tourCutSplitBody C.splay.splay C.detachLeft C.detachRight C.join C.rotateFront)
        (startState [nb, nx, ny, fuel, heap] mem pos) o st' c ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (t1 :: t2 :: rest) ∧
      TourValsOk w cap s' ∧
      t1 ≠ .leaf ∧ t2 ≠ .leaf ∧
      rotateNatList nx t.toList = nx :: A ++ ny :: Q ∧
      t1.toList = nx :: Q ∧
      t2.toList = A ++ [ny] ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      c + TOUR_PHI_MULT * forestPhi (t1 :: t2 :: rest) ≤
        TOUR_PHI_MULT * forestPhi (t :: rest) + TOUR_CUTSPLIT_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  -- Step 1: rotateFront(nx)
  obtain ⟨t₁, s₁, o₁, st₁, c₁, hrun₁, _, hn₁, hfr₁, hinv₁, hvals₁, _, hrot₁, hval₁, _, hcost₁⟩ :=
    tourRotateFrontBody_runs (pos := pos) C ω hnodes hf hvals hnx hfuel hfuelW hheap
  have hny_t1 : ny ∈ t₁.toList := by rw [hrot₁]; exact (rotateNatList_perm hnx).mem_iff.mpr hny
  have hhead_t1 : t₁.toList.head? = some nx := by rw [hrot₁]; exact rotateNatList_head_eq hnx
  -- Step 2: splay(ny)
  have hdep_y : t₁.depthOf ny < fuel :=
    lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hny_t1)
      (le_of_lt (lt_of_le_of_lt (hinv₁.countNodes_le (by simp)) hfuel))
  have hinv₁0 : TourForestInv cap s₁ ([] ++ t₁ :: rest) := hinv₁
  obtain ⟨t₂, o₂, st₂, c₂, hrun₂, hn₂, hfr₂, hinv₂, hvals₂, hne₂, hroot₂, hlist₂, _, hcost₂⟩ :=
    tourSplay_runs_amort (pos := st₁.pos) C.toTourSplayCoreProcs ω hn₁ hinv₁0 hvals₁ hny_t1 hdep_y hfuelW
      (heapOk_frame hheap hfr₁)
  set s₂ := SplayState.splay tourPayload s₁ fuel ny
  obtain ⟨_, _, _, _, _, _, hval_sp2, _⟩ := tourSplay_preserves hinv₁0 hny_t1 hdep_y
  cases ht₂c : t₂ with
  | leaf => exact absurd ht₂c hne₂
  | node yid L R =>
    have hyid : yid = ny := by simpa [ht₂c, AuxTree.rootId] using hroot₂
    rcases hyid with rfl
    rw [ht₂c] at hinv₂ hlist₂ hcost₂
    -- Deduce L.toList = nx :: A (so L ≠ .leaf) and R.toList = Q
    have hL_head : L.toList.head? = some nx := by
      have h1 : (L.toList ++ yid :: R.toList).head? = some nx := by
        have : L.toList ++ yid :: R.toList = t₁.toList := by simpa [AuxTree.toList] using hlist₂
        rw [this]; exact hhead_t1
      cases hL : L.toList with
      | nil =>
        rw [hL, List.nil_append] at h1
        exact absurd (Option.some.inj h1).symm hne
      | cons a as => simpa [hL] using h1
    cases hL_list : L.toList with
    | nil => rw [hL_list] at hL_head; simp at hL_head
    | cons a0 A =>
      have ha0 : a0 = nx := Option.some.inj (by simpa [hL_list] using hL_head)
      subst a0
      have hL_ne : L ≠ .leaf := by intro h0; rw [h0] at hL_list; simp [AuxTree.toList] at hL_list
      have hrot_eq : rotateNatList nx t.toList = nx :: A ++ yid :: R.toList := by
        rw [← hrot₁, ← hlist₂]; simp [AuxTree.toList, hL_list]
      -- Step 3: detachLeft(ny)
      have hy_cap : yid ≤ cap := (hinv₂.mem_inCap (t := AuxTree.node yid L R) (by simp) (by simp [AuxTree.toList])).2
      have hsub₂ := (hinv₂.treesInv (AuxTree.node yid L R) (by simp)).sub
      obtain ⟨o₃, st₃, c₃, hrun₃, ⟨_, hn₃, hfr₃⟩, hc₃⟩ := tourDetachLeftBody_runs (pos := st₂.pos)
        C.toTourSplayCoreProcs ω hn₂ hinv₂.ptrOk hy_cap
        (heapOk_zero' (heapOk_frame hheap (hfr₁.trans hfr₂))) (tourDetachLeft_sumOk hinv₂ hvals₂)
      obtain ⟨hinv₃, _, hval₃, hphi₃⟩ := tourDetachLeft_preserves hinv₂
      set s₃ := tourDetachLeft s₂ yid
      have hvals₃ : TourValsOk w cap s₃ := ⟨hvals₂.1, fun u hu => by rw [hval₃ u hu]; exact hvals₂.2 u hu⟩
      have hinv₃' : TourForestInv cap s₃ ([L] ++ AuxTree.node yid .leaf R :: rest) := by
        simpa [hL_ne] using hinv₃
      -- Step 4: detachRight(ny)
      obtain ⟨o₄, st₄, c₄, hrun₄, ⟨hv₄, hn₄, hfr₄⟩, hc₄⟩ := tourDetachRightBody_runs (pos := st₃.pos)
        C.toTourSplayCoreProcs ω hn₃ hinv₃'.ptrOk hy_cap
        (heapOk_zero' (heapOk_frame hheap (hfr₁.trans (hfr₂.trans hfr₃))))
        (tourDetachRight_sumOk hinv₃' hvals₃)
      obtain ⟨hinv₄, _, hval₄, hphi₄⟩ := tourDetachRight_preserves hinv₃'
      set s₄ := tourDetachRight s₃ yid
      have hvals₄ : TourValsOk w cap s₄ := ⟨hvals₃.1, fun u hu => by rw [hval₄ u hu]; exact hvals₃.2 u hu⟩
      let R? : Option AuxTree := if R = .leaf then none else some R
      have hR_root : o₄.value = optRoot R? := by
        have hsub₃ := (hinv₃'.treesInv (AuxTree.node yid .leaf R) (by simp)).sub
        rw [hv₄]; simp only [hsub₃.1, ↓reduceIte, hsub₃.2.2.1, R?, optRoot_of_ite]
      have hinv₄' : TourForestInv cap s₄ ([] ++ L :: (AuxTree.node yid .leaf .leaf :: optTrees R? ++ rest)) := by
        simpa [R?, optTrees_of_ite] using hinv₄
      -- Step 5: splay(nx) on L
      have hnx_L : nx ∈ L.toList := by rw [hL_list]; simp
      have hdep_x : L.depthOf nx < fuel :=
        lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hnx_L)
          (le_of_lt (lt_of_le_of_lt (hinv₄'.countNodes_le (by simp)) hfuel))
      obtain ⟨t₅, o₅, st₅, c₅, hrun₅, hn₅, hfr₅, hinv₅, hvals₅, hne₅, hroot₅, hlist₅, _, hcost₅⟩ :=
        tourSplay_runs_amort (pos := st₄.pos) C.toTourSplayCoreProcs ω hn₄ hinv₄' hvals₄ hnx_L hdep_x hfuelW
          (heapOk_frame hheap (hfr₁.trans (hfr₂.trans (hfr₃.trans hfr₄))))
      set s₅ := SplayState.splay tourPayload s₄ fuel nx
      obtain ⟨_, _, _, _, _, _, hval_sp5, _⟩ := tourSplay_preserves hinv₄' hnx_L hdep_x
      cases ht₅c : t₅ with
      | leaf => exact absurd ht₅c hne₅
      | node xid Lx Ax =>
        have hxid : xid = nx := by simpa [ht₅c, AuxTree.rootId] using hroot₅
        rcases hxid with rfl
        rw [ht₅c] at hinv₅ hlist₅ hcost₅
        have hLx_leaf : Lx = .leaf := by
          have h1 : Lx.toList ++ xid :: Ax.toList = xid :: A := by
            rw [← hL_list, ← hlist₅]; simp [AuxTree.toList]
          have hnd := (AuxTree.nodup_node_unfold (hinv₅.treesInv (AuxTree.node xid Lx Ax) (by simp)).nodup).2.1
          cases hLx : Lx with
          | leaf => rfl
          | node lid _ _ =>
            have hne_l : Lx.toList ≠ [] := by rw [hLx]; simp [AuxTree.toList]
            cases hll : Lx.toList with
            | nil => exact absurd hll hne_l
            | cons z zs =>
              rw [hll] at h1
              have hzx : z = xid := (List.cons.inj h1).1
              exact absurd (by rw [hll, hzx]; simp) hnd
        subst hLx_leaf
        have hAx_list : Ax.toList = A := by
          have h1 : xid :: Ax.toList = xid :: A := by
            rw [← hL_list, ← hlist₅]; simp [AuxTree.toList]
          exact (List.cons.inj h1).2
        -- Step 6: detachRight(nx)
        have hx_cap : xid ≤ cap := (hinv₅.mem_inCap (t := AuxTree.node xid .leaf Ax) (by simp) (by simp [AuxTree.toList])).2
        obtain ⟨o₆, st₆, c₆, hrun₆, ⟨hv₆, hn₆, hfr₆⟩, hc₆⟩ := tourDetachRightBody_runs (pos := st₅.pos)
          C.toTourSplayCoreProcs ω hn₅ hinv₅.ptrOk hx_cap
          (heapOk_zero' (heapOk_frame hheap (hfr₁.trans (hfr₂.trans (hfr₃.trans (hfr₄.trans hfr₅))))))
          (tourDetachRight_sumOk hinv₅ hvals₅)
        obtain ⟨hinv₆, _, hval₆, hphi₆⟩ := tourDetachRight_preserves hinv₅
        set s₆ := tourDetachRight s₅ xid
        have hvals₆ : TourValsOk w cap s₆ := ⟨hvals₅.1, fun u hu => by rw [hval₆ u hu]; exact hvals₅.2 u hu⟩
        let Ax? : Option AuxTree := if Ax = .leaf then none else some Ax
        have hAx_root : o₆.value = optRoot Ax? := by
          have hsub₅ := (hinv₅.treesInv (AuxTree.node xid .leaf Ax) (by simp)).sub
          rw [hv₆]; simp only [hsub₅.1, ↓reduceIte, hsub₅.2.2.1, Ax?, optRoot_of_ite]
        -- Permute forest for join(nx, R?)
        have hperm₆ : ([] ++ ([AuxTree.node xid .leaf .leaf] ++ (if Ax = AuxTree.leaf then [] else [Ax])) ++
            (AuxTree.node yid .leaf .leaf :: optTrees R? ++ rest)).Perm
            (optTrees (some (AuxTree.node xid .leaf .leaf)) ++ optTrees R? ++
              (optTrees Ax? ++ AuxTree.node yid .leaf .leaf :: rest)) := by
          rw [← optTrees_of_ite Ax]
          change (AuxTree.node xid .leaf .leaf :: (optTrees Ax? ++ AuxTree.node yid .leaf .leaf :: (optTrees R? ++ rest))).Perm
            (AuxTree.node xid .leaf .leaf :: (optTrees R? ++ (optTrees Ax? ++ AuxTree.node yid .leaf .leaf :: rest)))
          refine List.Perm.cons _ ?_
          have h1 := List.Perm.append_right rest
            (List.perm_append_comm (l₁ := optTrees Ax? ++ [AuxTree.node yid .leaf .leaf]) (l₂ := optTrees R?))
          simpa [List.append_assoc] using h1
        have hinv₆' := (hinv₆.perm hperm₆).1
        -- Step 7: join(nx, R?) -> t1
        obtain ⟨t1?, s₇, o₇, st₇, c₇, hrun₇, _, hn₇, hfr₇, hinv₇, hvals₇, hlist₇, hval₇, _, hcost₇⟩ :=
          tourJoinBody_runs (pos := st₆.pos) C ω hn₆ hinv₆' hvals₆ hfuel hfuelW
            (heapOk_frame hheap (hfr₁.trans (hfr₂.trans (hfr₃.trans (hfr₄.trans (hfr₅.trans hfr₆))))))
        cases t1? with
        | none => simp [optList, AuxTree.toList] at hlist₇
        | some t1 =>
          have ht1_ne : t1 ≠ .leaf := hinv₇.nonEmpty t1 (by simp [optTrees])
          have ht1_list : t1.toList = xid :: R.toList := by
            rw [show optList R? = R.toList from optList_of_ite R] at hlist₇
            simpa [optList, AuxTree.toList] using hlist₇
          -- Permute forest for join(Ax?, ny)
          have hperm₇ : (optTrees (some t1) ++ (optTrees Ax? ++ AuxTree.node yid .leaf .leaf :: rest)).Perm
              (optTrees Ax? ++ optTrees (some (AuxTree.node yid .leaf .leaf)) ++ (t1 :: rest)) := by
            have hmid := List.perm_middle (a := t1) (l₁ := optTrees Ax? ++ [AuxTree.node yid .leaf .leaf]) (l₂ := rest)
            simpa [optTrees, List.append_assoc] using hmid.symm
          have hinv₇' := (hinv₇.perm hperm₇).1
          -- Step 8: join(Ax?, ny) -> t2
          obtain ⟨t2?, s₈, o₈, st₈, c₈, hrun₈, _, hn₈, hfr₈, hinv₈, hvals₈, hlist₈, hval₈, _, hcost₈⟩ :=
            tourJoinBody_runs (pos := st₇.pos) C ω hn₇ hinv₇' hvals₇ hfuel hfuelW
              (heapOk_frame hheap (hfr₁.trans (hfr₂.trans (hfr₃.trans (hfr₄.trans (hfr₅.trans (hfr₆.trans hfr₇)))))))
          cases t2? with
          | none => simp [optList, AuxTree.toList] at hlist₈
          | some t2 =>
            have ht2_ne : t2 ≠ .leaf := hinv₈.nonEmpty t2 (by simp [optTrees])
            have ht2_list : t2.toList = A ++ [yid] := by
              rw [show optList Ax? = Ax.toList from optList_of_ite Ax] at hlist₈
              simpa [optList, AuxTree.toList, hAx_list] using hlist₈
            have hperm₈ : (optTrees (some t2) ++ (t1 :: rest)).Perm (t1 :: t2 :: rest) := by
              simp only [optTrees, Option.toList, List.cons_append, List.nil_append]
              exact List.Perm.swap _ _ rest
            have hinv₈' := (hinv₈.perm hperm₈).1
            have hval_all : ∀ u ≤ cap, (s₈.nodes u).val = (st.nodes u).val := fun u hu => by
              rw [hval₈ u hu, hval₇ u hu, hval₆ u hu, hval_sp5 u hu, hval₄ u hu, hval₃ u hu,
                hval_sp2 u hu, hval₁ u hu]
            -- Assemble WordRAM execution
            have hwide := hheap.wide
            have hbody : ∃ st_fin c_fin, st_fin.mem = st₈.mem ∧
                c_fin ≤ c₁ + c₂ + c₃ + c₄ + c₅ + c₆ + c₇ + c₈ + 60 ∧
                Runs w p ω (tourCutSplitBody C.splay.splay C.detachLeft C.detachRight C.join C.rotateFront)
                  (startState [nb, xid, yid, fuel, heap] mem pos) (.returned 0) st_fin c_fin := by
              unfold tourCutSplitBody; rw [startState]
              set st0 : State := ⟨mem, fun i => [nb, xid, yid, fuel, heap].getD i 0, pos⟩
              set q1 : State := { st₁ with regs := Function.update st0.regs 5 o₁.value }
              set q2 : State := { st₂ with regs := Function.update q1.regs 5 o₂.value }
              set q3 : State := { st₃ with regs := Function.update q2.regs 5 o₃.value }
              set q4 : State := { st₄ with regs := Function.update q3.regs 6 o₄.value }
              set q5 : State := { st₅ with regs := Function.update q4.regs 7 o₅.value }
              set q6 : State := { st₆ with regs := Function.update q5.regs 7 o₆.value }
              set q7 : State := { st₇ with regs := Function.update q6.regs 8 o₇.value }
              set q8 : State := { st₈ with regs := Function.update q7.regs 9 o₈.value }
              have hc1 := runs_call_regs4 5 0 1 3 4 (st := st0) C.rotateFront_body (by simp [st0]) (by simp [st0]) (by simp [st0]) (by simp [st0]) hrun₁
              have hc2 := runs_call_regs4 5 0 2 3 4 (st := q1) C.splay.splay_body (by simp [q1, st0]) (by simp [q1, st0]) (by simp [q1, st0]) (by simp [q1, st0]) hrun₂
              have hc3 := runs_call_regs3 5 0 2 4 (st := q2) C.detachLeft_body (by simp [q2, q1, st0]) (by simp [q2, q1, st0]) (by simp [q2, q1, st0]) hrun₃
              have hc4 := runs_call_regs3 6 0 2 4 (st := q3) C.detachRight_body (by simp [q3, q2, q1, st0]) (by simp [q3, q2, q1, st0]) (by simp [q3, q2, q1, st0]) hrun₄
              have hc5 := runs_call_regs4 7 0 1 3 4 (st := q4) C.splay.splay_body (by simp [q4, q3, q2, q1, st0]) (by simp [q4, q3, q2, q1, st0]) (by simp [q4, q3, q2, q1, st0]) (by simp [q4, q3, q2, q1, st0]) hrun₅
              have hc6 := runs_call_regs3 7 0 1 4 (st := q5) C.detachRight_body (by simp [q5, q4, q3, q2, q1, st0]) (by simp [q5, q4, q3, q2, q1, st0]) (by simp [q5, q4, q3, q2, q1, st0]) hrun₆
              have hc7 := runs_call_regs5 8 0 1 6 3 4 (st := q6) C.join_body
                (by simp [q6, q5, q4, q3, q2, q1, st0]) (by simp [q6, q5, q4, q3, q2, q1, st0, optRoot, AuxTree.rootId])
                (by simp [q6, q5, q4, hR_root]) (by simp [q6, q5, q4, q3, q2, q1, st0]) (by simp [q6, q5, q4, q3, q2, q1, st0]) hrun₇
              have hc8 := runs_call_regs5 9 0 7 2 3 4 (st := q7) C.join_body
                (by simp [q7, q6, q5, q4, q3, q2, q1, st0]) (by simp [q7, q6, hAx_root])
                (by simp [q7, q6, q5, q4, q3, q2, q1, st0, optRoot, AuxTree.rootId]) (by simp [q7, q6, q5, q4, q3, q2, q1, st0])
                (by simp [q7, q6, q5, q4, q3, q2, q1, st0]) hrun₈
              have hret := runs_ret_const (w := w) (p := p) (ω := ω) (st := q8) (v := 0) (by omega)
              exact ⟨q8, _, rfl, by omega,
                tour_runs_seq_normal hc1 (tour_runs_seq_normal hc2 (tour_runs_seq_normal hc3 (tour_runs_seq_normal hc4
                  (tour_runs_seq_normal hc5 (tour_runs_seq_normal hc6 (tour_runs_seq_normal hc7 (tour_runs_seq_normal hc8 hret)))))))⟩
            obtain ⟨st_fin, c_fin, hmem_fin, hcfin, hbody⟩ := hbody
            refine ⟨t1, t2, A, R.toList, s₈, .returned 0, st_fin, c_fin, hbody,
              hmem_fin ▸ hn₈, hmem_fin ▸ (hfr₁.trans (hfr₂.trans (hfr₃.trans (hfr₄.trans (hfr₅.trans (hfr₆.trans (hfr₇.trans hfr₈))))))),
              hinv₈', hvals₈, ht1_ne, ht2_ne, hrot_eq, ht1_list, ht2_list, hval_all, ?_⟩
            -- Potential + cost telescoping
            have hp3 := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₃
            have hp4 := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₄
            have hp6 := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₆
            have hpeq3 : forestPhi ([] ++ ((if L = .leaf then [] else [L]) ++ [AuxTree.node yid .leaf R]) ++ rest) =
                forestPhi ([L] ++ AuxTree.node yid .leaf R :: rest) := by simp [hL_ne]
            have hpeq4 : forestPhi ([L] ++ ([AuxTree.node yid .leaf .leaf] ++ (if R = .leaf then [] else [R])) ++ rest) =
                forestPhi ([] ++ L :: (AuxTree.node yid .leaf .leaf :: optTrees R? ++ rest)) := by
              simp [R?, optTrees_of_ite]
            have hpeq6 := forestPhi_perm hperm₆
            have hpeq7 := forestPhi_perm hperm₇
            have hpeq8 := forestPhi_perm hperm₈
            rw [hpeq3] at hp3; rw [hpeq4] at hp4; rw [hpeq6] at hp6; rw [← hpeq7] at hcost₈; rw [hpeq8] at hcost₈
            simp only [List.nil_append, TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT,
              TOUR_JOIN_AMORT, TOUR_SEQ_AMORT, TOUR_CUTSPLIT_AMORT] at hcost₁ hcost₂ hc₃ hp3 hc₄ hp4 hcost₅ hc₆ hp6 hcost₇ hcost₈ hcfin ⊢
            omega

/-! ## Amortized run theorem for `tourLinkSpliceBody` -/

/-- Running `tourLinkSpliceBody` on two distinct trees `tx` (containing `nx`) and `ty`
(containing `ny`) splices them into `t'` with `t'.toList = Px ++ nx :: Qy ++ Py ++ ny :: Qx`. -/
theorem tourLinkSpliceBody_runs {w nb cap heap fuel nx ny pos : ℕ} {p : Program}
    (C : TourSplayOpsProcs w p) (ω : ℕ → Bool) {mem : ℕ → ℕ}
    {st : SplayState TourVal TourSum Unit} {tx ty : AuxTree} {rest : List AuxTree}
    (hnodes : tourLayout.NodesAt mem nb cap st)
    (hf : TourForestInv cap st (tx :: ty :: rest)) (hvals : TourValsOk w cap st)
    (hnx : nx ∈ tx.toList) (hny : ny ∈ ty.toList)
    (hfuel : cap < fuel) (hfuelW : fuel < 2 ^ w)
    (hheap : HeapOk tourLayout w nb cap heap 2 mem) :
    ∃ t' Px Qx Py Qy s' o st' c,
      Runs w p ω (tourLinkSpliceBody C.splay.splay C.detachLeft C.detachRight C.join)
        (startState [nb, nx, ny, fuel, heap] mem pos) o st' c ∧
      o.value = t'.rootId ∧
      tourLayout.NodesAt st'.mem nb cap s' ∧
      TreeFrame tourLayout nb cap heap mem st'.mem ∧
      TourForestInv cap s' (t' :: rest) ∧
      TourValsOk w cap s' ∧
      t' ≠ .leaf ∧
      tx.toList = Px ++ nx :: Qx ∧
      ty.toList = Py ++ ny :: Qy ∧
      t'.toList = Px ++ nx :: Qy ++ Py ++ ny :: Qx ∧
      (∀ u ≤ cap, (s'.nodes u).val = (st.nodes u).val) ∧
      c + TOUR_PHI_MULT * forestPhi (t' :: rest) ≤
        TOUR_PHI_MULT * forestPhi (tx :: ty :: rest) + TOUR_LINKSPLICE_AMORT * (Nat.log 2 (cap + 2) + 1) := by
  -- Step 1: splay(nx) on tx
  have hdep_x : tx.depthOf nx < fuel :=
    lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hnx)
      (le_of_lt (lt_of_le_of_lt (hf.countNodes_le (by simp)) hfuel))
  have hf0 : TourForestInv cap st ([] ++ tx :: (ty :: rest)) := hf
  obtain ⟨t₁, o₁, st₁, c₁, hrun₁, hn₁, hfr₁, hinv₁, hvals₁, hne₁, hroot₁, hlist₁, _, hcost₁⟩ :=
    tourSplay_runs_amort (pos := pos) C.toTourSplayCoreProcs ω hnodes hf0 hvals hnx hdep_x hfuelW hheap
  set s₁ := SplayState.splay tourPayload st fuel nx
  obtain ⟨_, _, _, _, _, _, hval_sp1, _⟩ := tourSplay_preserves hf0 hnx hdep_x
  cases ht₁c : t₁ with
  | leaf => exact absurd ht₁c hne₁
  | node xid Px Qx =>
    have hxid : xid = nx := by simpa [ht₁c, AuxTree.rootId] using hroot₁
    rcases hxid with rfl
    rw [ht₁c] at hinv₁ hlist₁ hcost₁
    have htx_eq : tx.toList = Px.toList ++ xid :: Qx.toList := by rw [← hlist₁]; simp [AuxTree.toList]
    have hx_cap : xid ≤ cap := (hinv₁.mem_inCap (t := AuxTree.node xid Px Qx) (by simp) (by simp [AuxTree.toList])).2
    -- Step 2: detachLeft(nx)
    obtain ⟨o₂, st₂, c₂, hrun₂, ⟨hv₂, hn₂, hfr₂⟩, hc₂⟩ := tourDetachLeftBody_runs (pos := st₁.pos)
      C.toTourSplayCoreProcs ω hn₁ hinv₁.ptrOk hx_cap
      (heapOk_zero' (heapOk_frame hheap hfr₁)) (tourDetachLeft_sumOk hinv₁ hvals₁)
    obtain ⟨hinv₂, _, hval₂, hphi₂⟩ := tourDetachLeft_preserves hinv₁
    set s₂ := tourDetachLeft s₁ xid
    have hvals₂ : TourValsOk w cap s₂ := ⟨hvals₁.1, fun u hu => by rw [hval₂ u hu]; exact hvals₁.2 u hu⟩
    let Px? : Option AuxTree := if Px = .leaf then none else some Px
    have hPx_root : o₂.value = optRoot Px? := by
      have hsub₁ := (hinv₁.treesInv (AuxTree.node xid Px Qx) (by simp)).sub
      rw [hv₂]; simp only [hsub₁.1, ↓reduceIte, hsub₁.2.1, Px?, optRoot_of_ite]
    have hinv₂' : TourForestInv cap s₂ (optTrees Px? ++ AuxTree.node xid .leaf Qx :: (ty :: rest)) := by
      simpa [Px?, optTrees_of_ite] using hinv₂
    -- Step 3: detachRight(nx)
    obtain ⟨o₃, st₃, c₃, hrun₃, ⟨hv₃, hn₃, hfr₃⟩, hc₃⟩ := tourDetachRightBody_runs (pos := st₂.pos)
      C.toTourSplayCoreProcs ω hn₂ hinv₂'.ptrOk hx_cap
      (heapOk_zero' (heapOk_frame hheap (hfr₁.trans hfr₂))) (tourDetachRight_sumOk hinv₂' hvals₂)
    obtain ⟨hinv₃, _, hval₃, hphi₃⟩ := tourDetachRight_preserves hinv₂'
    set s₃ := tourDetachRight s₂ xid
    have hvals₃ : TourValsOk w cap s₃ := ⟨hvals₂.1, fun u hu => by rw [hval₃ u hu]; exact hvals₂.2 u hu⟩
    let Qx? : Option AuxTree := if Qx = .leaf then none else some Qx
    have hQx_root : o₃.value = optRoot Qx? := by
      have hsub₂ := (hinv₂'.treesInv (AuxTree.node xid .leaf Qx) (by simp)).sub
      rw [hv₃]; simp only [hsub₂.1, ↓reduceIte, hsub₂.2.2.1, Qx?, optRoot_of_ite]
    have hperm₃ : (optTrees Px? ++ ([AuxTree.node xid .leaf .leaf] ++ (if Qx = .leaf then [] else [Qx])) ++ (ty :: rest)).Perm
        ([] ++ ty :: (optTrees Px? ++ AuxTree.node xid .leaf .leaf :: optTrees Qx? ++ rest)) := by
      rw [← optTrees_of_ite Qx]
      simpa [List.append_assoc] using
        (List.perm_middle (a := ty) (l₁ := optTrees Px? ++ AuxTree.node xid .leaf .leaf :: optTrees Qx?) (l₂ := rest))
    have hinv₃' := (hinv₃.perm hperm₃).1
    -- Step 4: splay(ny) on ty
    have hdep_y : ty.depthOf ny < fuel :=
      lt_of_lt_of_le (auxTree_depthOf_lt_countNodes hny)
        (le_of_lt (lt_of_le_of_lt (hinv₃'.countNodes_le (by simp)) hfuel))
    obtain ⟨t₄, o₄, st₄, c₄, hrun₄, hn₄, hfr₄, hinv₄, hvals₄, hne₄, hroot₄, hlist₄, _, hcost₄⟩ :=
      tourSplay_runs_amort (pos := st₃.pos) C.toTourSplayCoreProcs ω hn₃ hinv₃' hvals₃ hny hdep_y hfuelW
        (heapOk_frame hheap (hfr₁.trans (hfr₂.trans hfr₃)))
    set s₄ := SplayState.splay tourPayload s₃ fuel ny
    obtain ⟨_, _, _, _, _, _, hval_sp4, _⟩ := tourSplay_preserves hinv₃' hny hdep_y
    cases ht₄c : t₄ with
    | leaf => exact absurd ht₄c hne₄
    | node yid Py Qy =>
      have hyid : yid = ny := by simpa [ht₄c, AuxTree.rootId] using hroot₄
      rcases hyid with rfl
      rw [ht₄c] at hinv₄ hlist₄ hcost₄
      have hty_eq : ty.toList = Py.toList ++ yid :: Qy.toList := by rw [← hlist₄]; simp [AuxTree.toList]
      have hy_cap : yid ≤ cap := (hinv₄.mem_inCap (t := AuxTree.node yid Py Qy) (by simp) (by simp [AuxTree.toList])).2
      -- Step 5: detachLeft(ny)
      obtain ⟨o₅, st₅, c₅, hrun₅, ⟨hv₅, hn₅, hfr₅⟩, hc₅⟩ := tourDetachLeftBody_runs (pos := st₄.pos)
        C.toTourSplayCoreProcs ω hn₄ hinv₄.ptrOk hy_cap
        (heapOk_zero' (heapOk_frame hheap (hfr₁.trans (hfr₂.trans (hfr₃.trans hfr₄)))))
        (tourDetachLeft_sumOk hinv₄ hvals₄)
      obtain ⟨hinv₅, _, hval₅, hphi₅⟩ := tourDetachLeft_preserves hinv₄
      set s₅ := tourDetachLeft s₄ yid
      have hvals₅ : TourValsOk w cap s₅ := ⟨hvals₄.1, fun u hu => by rw [hval₅ u hu]; exact hvals₄.2 u hu⟩
      let Py? : Option AuxTree := if Py = .leaf then none else some Py
      have hPy_root : o₅.value = optRoot Py? := by
        have hsub₄ := (hinv₄.treesInv (AuxTree.node yid Py Qy) (by simp)).sub
        rw [hv₅]; simp only [hsub₄.1, ↓reduceIte, hsub₄.2.1, Py?, optRoot_of_ite]
      have hinv₅' : TourForestInv cap s₅ (optTrees Py? ++ AuxTree.node yid .leaf Qy ::
          (optTrees Px? ++ AuxTree.node xid .leaf .leaf :: optTrees Qx? ++ rest)) := by
        simpa [Py?, optTrees_of_ite] using hinv₅
      -- Step 6: detachRight(ny)
      obtain ⟨o₆, st₆, c₆, hrun₆, ⟨hv₆, hn₆, hfr₆⟩, hc₆⟩ := tourDetachRightBody_runs (pos := st₅.pos)
        C.toTourSplayCoreProcs ω hn₅ hinv₅'.ptrOk hy_cap
        (heapOk_zero' (heapOk_frame hheap (hfr₁.trans (hfr₂.trans (hfr₃.trans (hfr₄.trans hfr₅))))))
        (tourDetachRight_sumOk hinv₅' hvals₅)
      obtain ⟨hinv₆, _, hval₆, hphi₆⟩ := tourDetachRight_preserves hinv₅'
      set s₆ := tourDetachRight s₅ yid
      have hvals₆ : TourValsOk w cap s₆ := ⟨hvals₅.1, fun u hu => by rw [hval₆ u hu]; exact hvals₅.2 u hu⟩
      let Qy? : Option AuxTree := if Qy = .leaf then none else some Qy
      have hQy_root : o₆.value = optRoot Qy? := by
        have hsub₅ := (hinv₅'.treesInv (AuxTree.node yid .leaf Qy) (by simp)).sub
        rw [hv₆]; simp only [hsub₅.1, ↓reduceIte, hsub₅.2.2.1, Qy?, optRoot_of_ite]
      -- Permute all 6 pieces into join order: Px?, [nx], Qy?, Py?, [ny], Qx?, rest
      have hperm₆ : (optTrees Py? ++ ([AuxTree.node yid .leaf .leaf] ++ (if Qy = .leaf then [] else [Qy])) ++
          (optTrees Px? ++ AuxTree.node xid .leaf .leaf :: optTrees Qx? ++ rest)).Perm
          (optTrees Px? ++ optTrees (some (AuxTree.node xid .leaf .leaf)) ++
            (optTrees Qy? ++ optTrees Py? ++ optTrees (some (AuxTree.node yid .leaf .leaf)) ++ optTrees Qx? ++ rest)) := by
        rw [← optTrees_of_ite Qy]
        simp only [optTrees, Option.toList, List.cons_append, List.nil_append, List.append_assoc]
        -- Both sides are permutations of [Py?, ny, Qy?, Px?, nx, Qx?, rest]
        have hA : (optTrees Py? ++ (AuxTree.node yid .leaf .leaf :: (optTrees Qy? ++
            (optTrees Px? ++ (AuxTree.node xid .leaf .leaf :: (optTrees Qx? ++ rest)))))).Perm
            ((optTrees Py? ++ [AuxTree.node yid .leaf .leaf] ++ optTrees Qy?) ++
              (optTrees Px? ++ [AuxTree.node xid .leaf .leaf]) ++ (optTrees Qx? ++ rest)) := by
          simp [List.append_assoc]
        have hB : ((optTrees Py? ++ [AuxTree.node yid .leaf .leaf] ++ optTrees Qy?) ++
            (optTrees Px? ++ [AuxTree.node xid .leaf .leaf]) ++ (optTrees Qx? ++ rest)).Perm
            ((optTrees Px? ++ [AuxTree.node xid .leaf .leaf]) ++
              (optTrees Qy? ++ optTrees Py? ++ [AuxTree.node yid .leaf .leaf]) ++ (optTrees Qx? ++ rest)) := by
          refine List.Perm.append_right (optTrees Qx? ++ rest) ?_
          refine List.perm_append_comm.trans (List.Perm.append_left _ ?_)
          simpa [List.append_assoc] using List.perm_append_comm (l₁ := optTrees Py? ++ [AuxTree.node yid .leaf .leaf]) (l₂ := optTrees Qy?)
        exact hA.trans (hB.trans (by simp only [List.append_assoc, List.cons_append, List.nil_append]; exact List.Perm.refl _))
      have hinv₆' := (hinv₆.perm hperm₆).1
      -- Step 7..11: five sequential joins
      have hheap6 := heapOk_frame hheap (hfr₁.trans (hfr₂.trans (hfr₃.trans (hfr₄.trans (hfr₅.trans hfr₆)))))
      obtain ⟨j1?, s₇, o₇, st₇, c₇, hrun₇, hv₇, hn₇, hfr₇, hinv₇, hvals₇, hlist₇, hval₇, _, hcost₇⟩ :=
        tourJoinBody_runs (pos := st₆.pos) C ω hn₆ hinv₆' hvals₆ hfuel hfuelW hheap6
      have hinv₇' : TourForestInv cap s₇ (optTrees j1? ++ optTrees Qy? ++
          (optTrees Py? ++ optTrees (some (AuxTree.node yid .leaf .leaf)) ++ optTrees Qx? ++ rest)) := by
        simpa [List.append_assoc] using hinv₇
      obtain ⟨j2?, s₈, o₈, st₈, c₈, hrun₈, hv₈, hn₈, hfr₈, hinv₈, hvals₈, hlist₈, hval₈, _, hcost₈⟩ :=
        tourJoinBody_runs (pos := st₇.pos) C ω hn₇ hinv₇' hvals₇ hfuel hfuelW (heapOk_frame hheap6 hfr₇)
      have hinv₈' : TourForestInv cap s₈ (optTrees j2? ++ optTrees Py? ++
          (optTrees (some (AuxTree.node yid .leaf .leaf)) ++ optTrees Qx? ++ rest)) := by
        simpa [List.append_assoc] using hinv₈
      obtain ⟨j3?, s₉, o₉, st₉, c₉, hrun₉, hv₉, hn₉, hfr₉, hinv₉, hvals₉, hlist₉, hval₉, _, hcost₉⟩ :=
        tourJoinBody_runs (pos := st₈.pos) C ω hn₈ hinv₈' hvals₈ hfuel hfuelW
          (heapOk_frame hheap6 (hfr₇.trans hfr₈))
      have hinv₉' : TourForestInv cap s₉ (optTrees j3? ++ optTrees (some (AuxTree.node yid .leaf .leaf)) ++
          (optTrees Qx? ++ rest)) := by
        simpa [List.append_assoc] using hinv₉
      obtain ⟨j4?, s₁₀, o₁₀, st₁₀, c₁₀, hrun₁₀, hv₁₀, hn₁₀, hfr₁₀, hinv₁₀, hvals₁₀, hlist₁₀, hval₁₀, _, hcost₁₀⟩ :=
        tourJoinBody_runs (pos := st₉.pos) C ω hn₉ hinv₉' hvals₉ hfuel hfuelW
          (heapOk_frame hheap6 (hfr₇.trans (hfr₈.trans hfr₉)))
      have hinv₁₀' : TourForestInv cap s₁₀ (optTrees j4? ++ optTrees Qx? ++ rest) := by
        simpa [List.append_assoc] using hinv₁₀
      obtain ⟨t'?, s₁₁, o₁₁, st₁₁, c₁₁, hrun₁₁, hv₁₁, hn₁₁, hfr₁₁, hinv₁₁, hvals₁₁, hlist₁₁, hval₁₁, _, hcost₁₁⟩ :=
        tourJoinBody_runs (pos := st₁₀.pos) C ω hn₁₀ hinv₁₀' hvals₁₀ hfuel hfuelW
          (heapOk_frame hheap6 (hfr₇.trans (hfr₈.trans (hfr₉.trans hfr₁₀))))
      have hlist_full : optList t'? = Px.toList ++ xid :: Qy.toList ++ Py.toList ++ yid :: Qx.toList := by
        rw [hlist₁₁, hlist₁₀, hlist₉, hlist₈, hlist₇]
        simp only [Px?, Qx?, Py?, Qy?, optList_of_ite]
        simp [optList, AuxTree.toList]
      cases t'? with
      | none => simp [optList] at hlist_full
      | some t' =>
        have ht'_ne : t' ≠ .leaf := hinv₁₁.nonEmpty t' (by simp [optTrees])
        have ht'_list : t'.toList = Px.toList ++ xid :: Qy.toList ++ Py.toList ++ yid :: Qx.toList := by
          simpa [optList] using hlist_full
        have hval_all : ∀ u ≤ cap, (s₁₁.nodes u).val = (st.nodes u).val := fun u hu => by
          rw [hval₁₁ u hu, hval₁₀ u hu, hval₉ u hu, hval₈ u hu, hval₇ u hu, hval₆ u hu, hval₅ u hu,
            hval_sp4 u hu, hval₃ u hu, hval₂ u hu, hval_sp1 u hu]
        have hbody : ∃ st_fin c_fin, st_fin.mem = st₁₁.mem ∧
            c_fin ≤ c₁ + c₂ + c₃ + c₄ + c₅ + c₆ + c₇ + c₈ + c₉ + c₁₀ + c₁₁ + 80 ∧
            Runs w p ω (tourLinkSpliceBody C.splay.splay C.detachLeft C.detachRight C.join)
              (startState [nb, xid, yid, fuel, heap] mem pos) (.returned t'.rootId) st_fin c_fin := by
          unfold tourLinkSpliceBody; rw [startState]
          set st0 : State := ⟨mem, fun i => [nb, xid, yid, fuel, heap].getD i 0, pos⟩
          set q1 : State := { st₁ with regs := Function.update st0.regs 5 o₁.value }
          set q2 : State := { st₂ with regs := Function.update q1.regs 5 o₂.value }
          set q3 : State := { st₃ with regs := Function.update q2.regs 6 o₃.value }
          set q4 : State := { st₄ with regs := Function.update q3.regs 7 o₄.value }
          set q5 : State := { st₅ with regs := Function.update q4.regs 7 o₅.value }
          set q6 : State := { st₆ with regs := Function.update q5.regs 8 o₆.value }
          set q7 : State := { st₇ with regs := Function.update q6.regs 9 o₇.value }
          set q8 : State := { st₈ with regs := Function.update q7.regs 9 o₈.value }
          set q9 : State := { st₉ with regs := Function.update q8.regs 9 o₉.value }
          set q10 : State := { st₁₀ with regs := Function.update q9.regs 9 o₁₀.value }
          set q11 : State := { st₁₁ with regs := Function.update q10.regs 9 o₁₁.value }
          have hc1 := runs_call_regs4 5 0 1 3 4 (st := st0) C.splay.splay_body (by simp [st0]) (by simp [st0]) (by simp [st0]) (by simp [st0]) hrun₁
          have hc2 := runs_call_regs3 5 0 1 4 (st := q1) C.detachLeft_body (by simp [q1, st0]) (by simp [q1, st0]) (by simp [q1, st0]) hrun₂
          have hc3 := runs_call_regs3 6 0 1 4 (st := q2) C.detachRight_body (by simp [q2, q1, st0]) (by simp [q2, q1, st0]) (by simp [q2, q1, st0]) hrun₃
          have hc4 := runs_call_regs4 7 0 2 3 4 (st := q3) C.splay.splay_body (by simp [q3, q2, q1, st0]) (by simp [q3, q2, q1, st0]) (by simp [q3, q2, q1, st0]) (by simp [q3, q2, q1, st0]) hrun₄
          have hc5 := runs_call_regs3 7 0 2 4 (st := q4) C.detachLeft_body (by simp [q4, q3, q2, q1, st0]) (by simp [q4, q3, q2, q1, st0]) (by simp [q4, q3, q2, q1, st0]) hrun₅
          have hc6 := runs_call_regs3 8 0 2 4 (st := q5) C.detachRight_body (by simp [q5, q4, q3, q2, q1, st0]) (by simp [q5, q4, q3, q2, q1, st0]) (by simp [q5, q4, q3, q2, q1, st0]) hrun₆
          have hc7 := runs_call_regs5 9 0 5 1 3 4 (st := q6) C.join_body
            (by simp [q6, q5, q4, q3, q2, q1, st0]) (by simp [q6, q5, q4, q3, q2, hPx_root])
            (by simp [q6, q5, q4, q3, q2, q1, st0, optRoot, AuxTree.rootId])
            (by simp [q6, q5, q4, q3, q2, q1, st0]) (by simp [q6, q5, q4, q3, q2, q1, st0]) hrun₇
          have hc8 := runs_call_regs5 9 0 9 8 3 4 (st := q7) C.join_body
            (by simp [q7, q6, q5, q4, q3, q2, q1, st0]) (by simp [q7, hv₇]) (by simp [q7, q6, hQy_root])
            (by simp [q7, q6, q5, q4, q3, q2, q1, st0]) (by simp [q7, q6, q5, q4, q3, q2, q1, st0]) hrun₈
          have hc9 := runs_call_regs5 9 0 9 7 3 4 (st := q8) C.join_body
            (by simp [q8, q7, q6, q5, q4, q3, q2, q1, st0]) (by simp [q8, hv₈]) (by simp [q8, q7, q6, q5, hPy_root])
            (by simp [q8, q7, q6, q5, q4, q3, q2, q1, st0]) (by simp [q8, q7, q6, q5, q4, q3, q2, q1, st0]) hrun₉
          have hc10 := runs_call_regs5 9 0 9 2 3 4 (st := q9) C.join_body
            (by simp [q9, q8, q7, q6, q5, q4, q3, q2, q1, st0]) (by simp [q9, hv₉])
            (by simp [q9, q8, q7, q6, q5, q4, q3, q2, q1, st0, optRoot, AuxTree.rootId])
            (by simp [q9, q8, q7, q6, q5, q4, q3, q2, q1, st0]) (by simp [q9, q8, q7, q6, q5, q4, q3, q2, q1, st0]) hrun₁₀
          have hc11 := runs_call_regs5 9 0 9 6 3 4 (st := q10) C.join_body
            (by simp [q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, st0]) (by simp [q10, hv₁₀])
            (by simp [q10, q9, q8, q7, q6, q5, q4, q3, hQx_root])
            (by simp [q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, st0]) (by simp [q10, q9, q8, q7, q6, q5, q4, q3, q2, q1, st0]) hrun₁₁
          have hret := runs_ret_reg (w := w) (p := p) (ω := ω) (st := q11) (r := 9) (v := t'.rootId)
            (by simp [q11, hv₁₁, optRoot])
          exact ⟨q11, _, rfl, by omega,
            tour_runs_seq_normal hc1 (tour_runs_seq_normal hc2 (tour_runs_seq_normal hc3 (tour_runs_seq_normal hc4
              (tour_runs_seq_normal hc5 (tour_runs_seq_normal hc6 (tour_runs_seq_normal hc7 (tour_runs_seq_normal hc8
                (tour_runs_seq_normal hc9 (tour_runs_seq_normal hc10 (tour_runs_seq_normal hc11 hret))))))))))⟩
        obtain ⟨st_fin, c_fin, hmem_fin, hcfin, hbody⟩ := hbody
        refine ⟨t', Px.toList, Qx.toList, Py.toList, Qy.toList, s₁₁, .returned t'.rootId, st_fin, c_fin,
          hbody, rfl, hmem_fin ▸ hn₁₁,
          hmem_fin ▸ (hfr₁.trans (hfr₂.trans (hfr₃.trans (hfr₄.trans (hfr₅.trans (hfr₆.trans (hfr₇.trans (hfr₈.trans (hfr₉.trans (hfr₁₀.trans hfr₁₁)))))))))),
          by simpa [optTrees] using hinv₁₁, hvals₁₁, ht'_ne, htx_eq, hty_eq, ht'_list, hval_all, ?_⟩
        have hp2 := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₂
        have hp3 := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₃
        have hp5 := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₅
        have hp6 := Nat.mul_le_mul_left TOUR_PHI_MULT hphi₆
        have hpeq2 : forestPhi ([] ++ ((if Px = .leaf then [] else [Px]) ++ [AuxTree.node xid .leaf Qx]) ++ (ty :: rest)) =
            forestPhi (optTrees Px? ++ AuxTree.node xid .leaf Qx :: (ty :: rest)) := by simp [Px?, optTrees_of_ite]
        have hpeq3 := forestPhi_perm hperm₃
        have hpeq5 : forestPhi ([] ++ ((if Py = .leaf then [] else [Py]) ++ [AuxTree.node yid .leaf Qy]) ++
            (optTrees Px? ++ AuxTree.node xid .leaf .leaf :: optTrees Qx? ++ rest)) =
            forestPhi (optTrees Py? ++ AuxTree.node yid .leaf Qy ::
              (optTrees Px? ++ AuxTree.node xid .leaf .leaf :: optTrees Qx? ++ rest)) := by simp [Py?, optTrees_of_ite]
        have hpeq6 := forestPhi_perm hperm₆
        rw [hpeq2] at hp2; rw [hpeq3] at hp3; rw [hpeq5] at hp5; rw [hpeq6] at hp6
        simp only [List.nil_append, List.append_assoc, optTrees, Option.toList, List.cons_append]
          at hcost₁ hc₂ hp2 hc₃ hp3 hcost₄ hc₅ hp5 hc₆ hp6 hcost₇ hcost₈ hcost₉ hcost₁₀ hcost₁₁ ⊢
        simp only [TOUR_PHI_MULT, TOUR_SPLICE_COST, TOUR_SPLAY_AMORT, TOUR_JOIN_AMORT,
          TOUR_LINKSPLICE_AMORT] at hcost₁ hc₂ hp2 hc₃ hp3 hcost₄ hc₅ hp5 hc₆ hp6 hcost₇ hcost₈ hcost₉ hcost₁₀ hcost₁₁ hcfin ⊢
        omega

end MinCostFlow.SparseCore.Program
