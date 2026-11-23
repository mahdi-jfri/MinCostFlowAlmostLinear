module

public import MinCostFlow.LSF.Program.InitScanBFS
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Single-Component BFS Proof for `initScanStmt` (`InitScanComp`)

Establishes `bfsComp_runs` (`O(|compOf G₀ startV| + ∑_{u ∈ compOf G₀ startV} deg(u))`)
and `dynGraphAt_and_inc_of_agree` as building blocks for `InitScanOuter`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Component BFS and Finset Helpers -/

lemma getElem_not_mem_take {L : List ℕ} (hnd : L.Nodup) {i : ℕ} (hi : i < L.length) :
    L[i]'hi ∉ L.take i := by
  intro hmem
  obtain ⟨j, hj_lt, hj_eq⟩ := List.mem_iff_getElem.mp hmem
  have hj_len : j < i := by simp only [List.length_take] at hj_lt; omega
  have hj_orig : j < L.length := lt_trans hj_len hi
  have heq : L[j]'hj_orig = L[i]'hi := by simpa [List.getElem_take] using hj_eq
  have hij := hnd.getElem_inj_iff.mp heq
  omega

lemma memSlice_take_eq {mem : ℕ → ℕ} {base m n : ℕ} {L : List ℕ}
    (hL : memSlice mem base n = L) (hle : m ≤ n) :
    memSlice mem base m = L.take m := by
  have hlen : m ≤ L.length := by rw [← hL, memSlice_length]; exact hle
  refine List.ext_getElem (by simp [memSlice_length, hlen]) fun i hi _ => ?_
  simp only [memSlice_length] at hi
  rw [memSlice_getElem, List.getElem_take]
  subst hL
  rw [memSlice_getElem]

lemma memSlice_one (mem : ℕ → ℕ) (a : ℕ) : memSlice mem a 1 = [mem a] := by
  refine List.ext_getElem (by simp [memSlice_length]) fun i hi _ => ?_
  simp only [memSlice_length] at hi
  have hi0 : i = 0 := by omega
  subst hi0
  rw [memSlice_getElem]
  simp

lemma preVis_union_compOf_closed {G₀ : MGraph} (hG₀ : G₀.IsValid)
    {preVis : Finset ℕ} {startV : ℕ}
    (hclosed : ∀ u ∈ preVis, ∀ v, mgAdj G₀ u v → v ∈ preVis) :
    ∀ u ∈ preVis ∪ compOf G₀ startV, ∀ v, mgAdj G₀ u v → v ∈ preVis ∪ compOf G₀ startV := by
  intro u hu v huv
  rw [Finset.mem_union] at hu ⊢
  rcases hu with hu_pre | hu_comp
  · exact Or.inl (hclosed u hu_pre v huv)
  · right
    rw [mem_compOf_iff] at hu_comp ⊢
    rcases huv with ⟨e, heE, hEnds⟩
    have hvV : v ∈ G₀.V := by
      rcases hEnds with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> [exact (hG₀ e heE).2; exact (hG₀ e heE).1]
    have huv_conn : G₀.Connected u v := by
      rcases hEnds with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact mgraph_adj_of_edge hG₀ heE (Or.inl h1) (Or.inr h2.symm)
      · exact mgraph_adj_of_edge hG₀ heE (Or.inr h2) (Or.inl h1.symm)
    exact ⟨hvV, connected_trans hu_comp.2 huv_conn⟩

lemma bfsComp_runs {w startV : ℕ} {p : Program} {ω : ℕ → Bool}
    {st : State} {sb : ScanBases}
    {g0Ptr vCap auxPtr logCap auxEnd vCap0 eCap0 : ℕ} {G₀ : MGraph}
    {preVis : Finset ℕ} {mem₀ : ℕ → ℕ} {incL : ℕ → List ℕ}
    (hw1 : 1 < 2 ^ w) (hauxW : auxEnd < 2 ^ w)
    (hdg : DynGraphAt mem₀ g0Ptr vCap0 eCap0 G₀)
    (hinc : ∀ s < vCap0,
      IsDoublyLinkedList mem₀ (dgHePrevBase g0Ptr vCap0 eCap0)
        (dgHeNextBase g0Ptr vCap0 eCap0) (dgIncHeadBase g0Ptr vCap0 + s) (2 * eCap0) (incL s) ∧
      mem₀ (dgSlotDegBase g0Ptr vCap0 + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCap0 ∧ h / 2 ∈ G₀.E ∧
        (if h % 2 = 0 then mem₀ (dgETailSlotBase g0Ptr vCap0 eCap0 + h / 2)
         else mem₀ (dgEHeadSlotBase g0Ptr vCap0 eCap0 + h / 2)) = s)
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
    (hstartV : startV ∈ G₀.V) (_hpre_sub : preVis ⊆ G₀.V)
    (hpre_closed : ∀ a ∈ preVis, ∀ b, mgAdj G₀ a b → b ∈ preVis)
    (hstart_npre : startV ∉ preVis)
    (hb : ScanBaseRegs st g0Ptr vCap auxPtr logCap sb)
    (hinv0 : st.regs 25 = 0 ∧ st.regs 26 = 1 ∧
      memSlice st.mem sb.qBufABase 1 = [startV] ∧
      (∀ z ∈ G₀.V, st.mem (sb.visBBase + z) = if z ∈ preVis ∨ z = startV then 1 else 0) ∧
      (∀ z < vCap, z ∉ G₀.V → st.mem (sb.visBBase + z) = 0) ∧
      ∀ a, a < sb.qBufABase ∨ (sb.qBufABase + vCap ≤ a ∧ a < sb.visBBase) ∨
        sb.visBBase + vCap ≤ a → st.mem a = mem₀ a) :
    ∃ st' c, Runs w p ω initScanBfsCompStmt st .normal st' c ∧
      ScanBaseRegs st' g0Ptr vCap auxPtr logCap sb ∧
      st'.regs 22 = st.regs 22 ∧ st'.regs 23 = st.regs 23 ∧
      (∀ z ∈ G₀.V, st'.mem (sb.visBBase + z) =
        if z ∈ preVis ∪ compOf G₀ startV then 1 else 0) ∧
      (∀ z < vCap, z ∉ G₀.V → st'.mem (sb.visBBase + z) = 0) ∧
      (∀ z ∈ compOf G₀ startV, z ∉ preVis) ∧
      (∀ a, a < sb.qBufABase ∨ (sb.qBufABase + vCap ≤ a ∧ a < sb.visBBase) ∨
        sb.visBBase + vCap ≤ a → st'.mem a = mem₀ a) ∧
      c ≤ (∑ u ∈ compOf G₀ startV,
        (140 * (incL (mem₀ (dgExtToIntBase g0Ptr vCap0 + u))).length + 50)) + 15 := by
  have hdg_copy := hdg
  rcases hdg with ⟨hG₀, hvlt0, _, _, _, _, _, _, _, hext, _, _, _, _, _⟩
  let degCost : ℕ → ℕ := fun u => 140 * (incL (mem₀ (dgExtToIntBase g0Ptr vCap0 + u))).length + 50
  let Inv : State → Prop := fun st_k => ∃ qHead allQ,
    st_k.regs 25 = qHead ∧ qHead ≤ allQ.length ∧ st_k.regs 26 = allQ.length ∧
    ScanBaseRegs st_k g0Ptr vCap auxPtr logCap sb ∧
    st_k.regs 22 = st.regs 22 ∧ st_k.regs 23 = st.regs 23 ∧
    memSlice st_k.mem sb.qBufABase allQ.length = allQ ∧
    allQ.length ≤ G₀.n ∧ allQ.Nodup ∧ (∀ z ∈ allQ, z ∈ G₀.V) ∧
    (0 < allQ.length ∧ allQ[0]? = some startV) ∧ (∀ z ∈ allQ, G₀.Connected startV z) ∧
    (∀ j, j < qHead → ∀ y, mgAdj G₀ (allQ.getD j 0) y → y ∈ allQ) ∧
    (∀ z ∈ G₀.V, st_k.mem (sb.visBBase + z) = if z ∈ preVis ∨ z ∈ allQ then 1 else 0) ∧
    (∀ z < vCap, z ∉ G₀.V → st_k.mem (sb.visBBase + z) = 0) ∧
    ∀ a, a < sb.qBufABase ∨ (sb.qBufABase + vCap ≤ a ∧ a < sb.visBBase) ∨
      sb.visBBase + vCap ≤ a → st_k.mem a = mem₀ a
  have hloop := Triple.loop_measure (w := w) (p := p) (e := .bin .lt (.reg 25) (.reg 26))
    (body :=
      .assign 27 (.load (.bin .add (.reg 12) (.reg 25))) ;;
      .assign 25 (.bin .add (.reg 25) (.const 1)) ;;
      .assign 28 (.load (.bin .add (.reg 16) (.reg 27))) ;;
      .assign 29 (.load (.bin .add (.reg 18) (.reg 28))) ;;
      .loop (.reg 29) initScanWalkIncBodyStmt)
    (Inv := Inv) (Q := normalPost (fun st_k => Inv st_k ∧ st_k.regs 25 = st_k.regs 26))
    (m := fun st_k => G₀.n - st_k.regs 25)
    (rem := fun st_k =>
      (∑ u ∈ compOf G₀ startV \ (memSlice st_k.mem sb.qBufABase (st_k.regs 25)).toFinset,
        degCost u) + 15)
    (condVal := fun st_k => if st_k.regs 25 < st_k.regs 26 then 1 else 0)
    (fun st_k hInv => by
      rcases hInv with ⟨qHead, allQ, hr25, hle, hr26, _, _, _, _, hqLen, _, _, _, _, _, _, _, _⟩
      have h25w : st_k.regs 25 < 2 ^ w := by omega
      have h26w : st_k.regs 26 < 2 ^ w := by omega
      eval_expr)
    (fun st_k hInv hv0 => by
      rcases hInv with ⟨qHead, allQ, hr25, hle, hr26, _⟩
      have hge : st_k.regs 26 ≤ st_k.regs 25 := by
        by_contra hlt
        simp [show st_k.regs 25 < st_k.regs 26 by omega] at hv0
      exact ⟨⟨⟨qHead, allQ, hr25, hle, hr26, ‹_›⟩, by omega⟩, by dsimp [Expr.size]; omega⟩)
    (fun st_k hInv hv_ne => by
      rcases hInv with ⟨qHead, allQ, hr25, hle, hr26, hb_k, hr22_k, hr23_k, hmemQ_k, hqLen_k,
        hqNd_k, hqV_k, hq0_k, hqConn_k, hPop_k, hvis1_k, hvisOut_k, hfr_k⟩
      have hlt_q : qHead < allQ.length := by
        by_contra hge
        have : ¬ st_k.regs 25 < st_k.regs 26 := by omega
        simp [this] at hv_ne
      set x := allQ[qHead]'hlt_q
      have hx_memQ : x ∈ allQ := List.getElem_mem hlt_q
      have hxV : x ∈ G₀.V := hqV_k x hx_memQ
      have hx_conn : G₀.Connected startV x := hqConn_k x hx_memQ
      have hx_npre : x ∉ preVis := fun hx_p =>
        hstart_npre (reachable_in_closed_set hpre_closed hx_p (connected_symm hx_conn))
      set s := mem₀ (dgExtToIntBase g0Ptr vCap0 + x)
      have hs_lt : s < vCap0 := hvlt0 _ (hext x hxV).1
      obtain ⟨hLs_dll, _, hLs_mem⟩ := hinc s hs_lt
      have hx_comp : x ∈ compOf G₀ startV := mem_compOf_iff.mpr ⟨hxV, hx_conn⟩
      have hms_take : memSlice st_k.mem sb.qBufABase qHead = allQ.take qHead :=
        memSlice_take_eq hmemQ_k (by omega)
      have hx_nmem_pop : x ∉ (memSlice st_k.mem sb.qBufABase qHead).toFinset := by
        rw [hms_take, List.mem_toFinset]
        exact getElem_not_mem_take hqNd_k hlt_q
      have hx_rem : x ∈ compOf G₀ startV \ (memSlice st_k.mem sb.qBufABase (st_k.regs 25)).toFinset := by
        rw [hr25, Finset.mem_sdiff]
        exact ⟨hx_comp, hx_nmem_pop⟩
      have hdeg_split := Finset.add_sum_erase
        (compOf G₀ startV \ (memSlice st_k.mem sb.qBufABase (st_k.regs 25)).toFinset)
        degCost hx_rem
      refine ⟨140 * (incL s).length + 40, fun s0 ω' hs0 => ?_⟩
      subst s0
      have hr12_k := hb_k.r12
      have hr16_k := hb_k.r16
      have hr18_k := hb_k.r18
      have haux_end : auxPtr ≤ auxEnd := by omega
      have hx_lt0 : x < vCap0 := hvlt0 x hxV
      have haux_lo' : g0Ptr + (4 + 7 * vCap0 + 9 * eCap0) ≤ auxPtr := haux_lo
      have hq_addrW : sb.qBufABase + qHead < 2 ^ w := by omega
      have hx_val_mem : st_k.mem (sb.qBufABase + qHead) = x := by
        have hget := memSlice_getElem st_k.mem sb.qBufABase allQ.length qHead
          (by rw [memSlice_length]; exact hlt_q)
        simp only [hmemQ_k] at hget
        exact hget.symm
      have hxW : x < 2 ^ w := by omega
      have hq1W : qHead + 1 < 2 ^ w := by omega
      have hext_addrW : sb.gExtToIntBase + x < 2 ^ w := by
        rw [hsb_eq.1]; dsimp [dgExtToIntBase] at *; omega
      have hs_mem_eq : st_k.mem (sb.gExtToIntBase + x) = s := by
        have hlt_aux : sb.gExtToIntBase + x < sb.qBufABase := by
          rw [hsb_eq.1]; dsimp [dgExtToIntBase] at *; omega
        rw [hfr_k _ (Or.inl hlt_aux), hsb_eq.1]
      have hsW : s < 2 ^ w := by omega
      have hinc_addrW : sb.gIncHeadBase + s < 2 ^ w := by
        rw [hsb_eq.2.2.1]; dsimp [dgIncHeadBase] at *; omega
      have hcur_eq : st_k.mem (sb.gIncHeadBase + s) =
          match incL s with | [] => 0 | h :: _ => h + 1 := by
        have hlt_aux : sb.gIncHeadBase + s < sb.qBufABase := by
          rw [hsb_eq.2.2.1]; dsimp [dgIncHeadBase] at *; omega
        rw [hfr_k _ (Or.inl hlt_aux), hsb_eq.2.2.1]
        exact hLs_dll.2.2.1
      have hcurW : st_k.mem (sb.gIncHeadBase + s) < 2 ^ w := by
        rw [hcur_eq]
        cases hL : incL s with
        | nil => simp
        | cons h hd =>
          have hh2e := hLs_dll.2.1 h (hL ▸ List.mem_cons_self)
          simp only
          omega
      refine runs_start_le ?_
      refine runs_seq_assign_le (v := x) (by eval_expr; try simp [hx_val_mem]) ?_
      refine runs_seq_assign_le (v := qHead + 1) (by eval_expr) ?_
      refine runs_seq_assign_le (v := s) (by eval_expr) ?_
      refine runs_seq_assign_le (v := st_k.mem (sb.gIncHeadBase + s)) (by eval_expr) ?_
      let st1 : State := { st_k with
        regs := Function.update (Function.update (Function.update (Function.update st_k.regs 27 x)
          25 (qHead + 1)) 28 s) 29 (st_k.mem (sb.gIncHeadBase + s)) }
      have hb1 : ScanBaseRegs st1 g0Ptr vCap auxPtr logCap sb :=
        scanBaseRegs_upd (scanBaseRegs_upd (scanBaseRegs_upd (scanBaseRegs_upd hb_k 27 x (by decide))
          25 (qHead + 1) (by decide)) 28 s (by decide)) 29 _ (by decide)
      obtain ⟨st', c_w, hr_w, ⟨allQ', hb', hrpres', hsubQ', hadj', hr25', hr26', hmemQ',
          hqLen', hqNd', hqV', hq0', hqConn', hvis1', hvisOut', hLenLe', hPref', hfr'⟩, hc_w⟩ :=
        walkInc_runs (w := w) (qHead := qHead + 1) (ω := ω') (p := p) (st := st1) (L_s := incL s)
          hw1 hauxW hdg_copy hvs hvs0 haux_lo hvis_bound hq_bound hdisj_qv hle_aux hsb_eq
          hxV rfl hLs_dll hLs_mem hpre_closed hstart_npre hx_npre hx_conn hb1 hcur_eq
          ⟨by simp [st1], by simp [st1, hr26], hmemQ_k, hqLen_k, hqNd_k, hqV_k,
            hq0_k, hqConn_k, hvis1_k, hvisOut_k, hfr_k⟩
      refine ⟨.normal, st', c_w, hr_w, ?_, ?_⟩
      · have hr22' : st'.regs 22 = st.regs 22 := by
          rw [hrpres' 22 (by simp)]; simp [st1, hr22_k]
        have hr23' : st'.regs 23 = st.regs 23 := by
          rw [hrpres' 23 (by simp)]; simp [st1, hr23_k]
        have hr25_eq' : st'.regs 25 = qHead + 1 := by rw [hrpres' 25 (by simp)]; simp [st1]
        have hpop' : ∀ j, j < qHead + 1 → ∀ y, mgAdj G₀ (allQ'.getD j 0) y → y ∈ allQ' := by
          intro j hj y hy
          have hj_eq : allQ'.getD j 0 = allQ.getD j 0 := by
            have hj1 : j < allQ.length := by omega
            have hj2 : j < allQ'.length := lt_of_lt_of_le hj1 hLenLe'
            have hget' := memSlice_getElem st'.mem sb.qBufABase allQ'.length j
              (by rw [memSlice_length]; exact hj2)
            simp only [hmemQ'] at hget'
            have hget := memSlice_getElem st_k.mem sb.qBufABase allQ.length j
              (by rw [memSlice_length]; exact hj1)
            simp only [hmemQ_k] at hget
            rw [List.getD_eq_getElem _ _ hj2, List.getD_eq_getElem _ _ hj1, hget', hPref' j hj1, hget]
          rw [hj_eq] at hy
          by_cases hjk : j = qHead
          · subst j
            rw [List.getD_eq_getElem _ _ hlt_q] at hy
            exact hadj' y hy
          · exact hsubQ' _ (hPop_k j (by omega) y hy)
        have hms_q1 : memSlice st'.mem sb.qBufABase (qHead + 1) =
            memSlice st_k.mem sb.qBufABase qHead ++ [x] := by
          have hagree : memSlice st'.mem sb.qBufABase (qHead + 1) =
              memSlice st_k.mem sb.qBufABase (qHead + 1) :=
            memSlice_eq_of_agree fun i hi => hPref' i (by omega)
          rw [hagree, memSlice_take_eq hmemQ_k (by omega), hms_take,
            List.take_add_one (i := qHead), List.getElem?_eq_getElem hlt_q]
          rfl
        have hset_eq : compOf G₀ startV \ (memSlice st'.mem sb.qBufABase (st'.regs 25)).toFinset =
            (compOf G₀ startV \ (memSlice st_k.mem sb.qBufABase (st_k.regs 25)).toFinset).erase x := by
          rw [hr25_eq', hr25, hms_q1]
          simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil]
          ext z
          simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union,
            Finset.mem_insert, Finset.notMem_empty, or_false]
          tauto
        refine ⟨⟨qHead + 1, allQ', hr25_eq', by omega, hr26', hb', hr22', hr23', hmemQ', hqLen',
            hqNd', hqV', hq0', hqConn', hpop', hvis1', hvisOut', hfr'⟩,
          by omega, ?_⟩
        rw [hset_eq]
        dsimp only [Expr.size] at *
        rw [← hdeg_split]
        dsimp only [degCost, s] at *
        omega
      · simp only [Expr.size] at hc_w ⊢
        omega)
  have hInv0 : Inv st := by
    refine ⟨0, [startV], hinv0.1, by simp, hinv0.2.1, hb, rfl, rfl, hinv0.2.2.1,
      by simp [MGraph.n]; exact ⟨startV, hstartV⟩, List.nodup_singleton _,
      fun z hz => by simp at hz; subst hz; exact hstartV, ⟨by simp, by simp⟩,
      fun z hz => by simp at hz; subst z; exact connected_refl G₀ startV,
      fun _ hj => by omega, ?_, hinv0.2.2.2.2.1, hinv0.2.2.2.2.2⟩
    intro z hz
    simpa [List.mem_singleton] using hinv0.2.2.2.1 z hz
  obtain ⟨o, st', c, hr, hpost, hc⟩ := hloop st ω hInv0
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    rcases hpost with ⟨⟨qHead, allQ, hr25, hle, hr26, hb', hr22', hr23', hmemQ', hqLen',
        hqNd', hqV', hq0', hqConn', hPop', hvis1', hvisOut', hfr'⟩, h25_26⟩
    have hqHead_eq : qHead = allQ.length := by omega
    have hallQ_closed : ∀ u ∈ allQ.toFinset, ∀ v, mgAdj G₀ u v → v ∈ allQ.toFinset := by
      intro u hu v huv
      rw [List.mem_toFinset] at hu ⊢
      obtain ⟨j, hj_lt, hj_eq⟩ := List.mem_iff_getElem.mp hu
      have hpop := hPop' j (hqHead_eq ▸ hj_lt) v
      rw [List.getD_eq_getElem _ _ hj_lt, hj_eq] at hpop
      exact hpop huv
    have hallQ_iff : ∀ z, z ∈ allQ ↔ z ∈ compOf G₀ startV := by
      intro z
      constructor
      · intro hz
        exact mem_compOf_iff.mpr ⟨hqV' z hz, hqConn' z hz⟩
      · intro hz
        have hconn := (mem_compOf_iff.mp hz).2
        have hs_mem : startV ∈ allQ.toFinset := by
          rw [List.mem_toFinset]
          rcases List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hq0'.1) with ⟨a, as, has⟩
          have h0e := hq0'.2
          rw [has] at h0e
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h0e
          rw [has, h0e]; exact List.mem_cons_self
        exact List.mem_toFinset.mp (reachable_in_closed_set hallQ_closed hs_mem hconn)
    have hvis_final : ∀ z ∈ G₀.V,
        st'.mem (sb.visBBase + z) = if z ∈ preVis ∪ compOf G₀ startV then 1 else 0 := by
      intro z hz
      simp [hvis1' z hz, Finset.mem_union, hallQ_iff z]
    have hcomp_npre : ∀ z ∈ compOf G₀ startV, z ∉ preVis := fun z hz hpz =>
      hstart_npre (reachable_in_closed_set hpre_closed hpz (connected_symm (mem_compOf_iff.mp hz).2))
    refine ⟨st', c, hr, hb', hr22', hr23', hvis_final, hvisOut', hcomp_npre, hfr', ?_⟩
    refine le_trans hc ?_
    have hms0 : memSlice st.mem sb.qBufABase (st.regs 25) = [] := by
      rw [hinv0.1]; rfl
    dsimp only
    rw [hms0]
    simp [degCost]

lemma dynGraphAt_and_inc_of_agree {mem mem' : ℕ → ℕ} {gPtr vCap eCap : ℕ}
    {G : MGraph} {incL : ℕ → List ℕ}
    (hdg : DynGraphAt mem gPtr vCap eCap G)
    (hinc : ∀ s < vCap,
      IsDoublyLinkedList mem (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
        (dgIncHeadBase gPtr vCap + s) (2 * eCap) (incL s) ∧
      mem (dgSlotDegBase gPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCap ∧ h / 2 ∈ G.E ∧
        (if h % 2 = 0 then mem (dgETailSlotBase gPtr vCap eCap + h / 2)
         else mem (dgEHeadSlotBase gPtr vCap eCap + h / 2)) = s)
    (hagree : ∀ a < gPtr + dynGraphSize vCap eCap, mem' a = mem a) :
    DynGraphAt mem' gPtr vCap eCap G ∧
    ∀ s < vCap,
      IsDoublyLinkedList mem' (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
        (dgIncHeadBase gPtr vCap + s) (2 * eCap) (incL s) ∧
      mem' (dgSlotDegBase gPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCap ∧ h / 2 ∈ G.E ∧
        (if h % 2 = 0 then mem' (dgETailSlotBase gPtr vCap eCap + h / 2)
         else mem' (dgEHeadSlotBase gPtr vCap eCap + h / 2)) = s := by
  rcases hdg with ⟨hG, hvlt, helt, hvcap, hecap, hn, hm, hvp, ⟨vL, hvL_len, hvL_nd, hvL_mem,
    hvL_LA, hvL_pos⟩, hext, hint, hep, ⟨eL, heL_len, heL_nd, heL_mem, heL_LA, heL_pos⟩,
    heEnds, _⟩
  have hag : ∀ (d : ℕ) (hd : d < dynGraphSize vCap eCap), mem' (gPtr + d) = mem (gPtr + d) :=
    fun d hd => hagree (gPtr + d) (by omega)
  have hdll' : ∀ s < vCap,
      IsDoublyLinkedList mem' (dgHePrevBase gPtr vCap eCap) (dgHeNextBase gPtr vCap eCap)
        (dgIncHeadBase gPtr vCap + s) (2 * eCap) (incL s) ∧
      mem' (dgSlotDegBase gPtr vCap + s) = (incL s).length ∧
      ∀ h, h ∈ incL s ↔ h < 2 * eCap ∧ h / 2 ∈ G.E ∧
        (if h % 2 = 0 then mem' (dgETailSlotBase gPtr vCap eCap + h / 2)
         else mem' (dgEHeadSlotBase gPtr vCap eCap + h / 2)) = s := by
    intro s hs
    obtain ⟨⟨hnd, hlt, hhd, hbody⟩, hdeg, hmem⟩ := hinc s hs
    have hhead_eq : mem' (dgIncHeadBase gPtr vCap + s) = mem (dgIncHeadBase gPtr vCap + s) :=
      hagree _ (by dsimp [dgIncHeadBase, dynGraphSize]; omega)
    have hdeg_eq : mem' (dgSlotDegBase gPtr vCap + s) = mem (dgSlotDegBase gPtr vCap + s) :=
      hagree _ (by dsimp [dgSlotDegBase, dynGraphSize]; omega)
    refine ⟨⟨hnd, hlt, hhead_eq.trans hhd, fun i hi => ?_⟩, hdeg_eq.trans hdeg, fun h => ?_⟩
    · have hh_lt := hlt _ (List.getElem_mem hi)
      have hb := hbody i hi
      have hp_eq : mem' (dgHePrevBase gPtr vCap eCap + (incL s)[i]) =
          mem (dgHePrevBase gPtr vCap eCap + (incL s)[i]) :=
        hagree _ (by dsimp [dgHePrevBase, dynGraphSize]; omega)
      have hn_eq : mem' (dgHeNextBase gPtr vCap eCap + (incL s)[i]) =
          mem (dgHeNextBase gPtr vCap eCap + (incL s)[i]) :=
        hagree _ (by dsimp [dgHeNextBase, dynGraphSize]; omega)
      exact ⟨hp_eq.trans hb.1, hn_eq.trans hb.2⟩
    · rw [hmem h]
      refine and_congr_right fun hh2e => and_congr_right fun heE => ?_
      have he_lt := helt _ heE
      split_ifs
      · rw [hagree _ (by dsimp [dgETailSlotBase, dynGraphSize]; omega)]
      · rw [hagree _ (by dsimp [dgEHeadSlotBase, dynGraphSize]; omega)]
  have hn_vcap : G.n ≤ vCap := by
    simpa [MGraph.n] using Finset.card_le_card (fun v hv => Finset.mem_range.mpr (hvlt v hv))
  refine ⟨⟨hG, hvlt, helt,
    (hag dgVCapOff (by dsimp [dgVCapOff, dynGraphSize]; omega)).trans hvcap,
    (hag dgECapOff (by dsimp [dgECapOff, dynGraphSize]; omega)).trans hecap,
    (hag dgNOff (by dsimp [dgNOff, dynGraphSize]; omega)).trans hn,
    (hag dgMOff (by dsimp [dgMOff, dynGraphSize]; omega)).trans hm,
    fun v hv => by rw [hagree _ (by dsimp [dgVPresBase, dynGraphSize]; omega)]; exact hvp v hv,
    ⟨vL, hvL_len, hvL_nd, hvL_mem,
      fun i hi => by
        rw [hagree _ (by dsimp [dgVListBase, dynGraphSize]; omega)]
        exact hvL_LA i hi,
      fun i hi => by
        rw [hagree _ (by dsimp [dgVPosBase, dynGraphSize]; have := hvlt _ ((hvL_mem _).mp (List.getElem_mem hi)); omega)]
        exact hvL_pos i hi⟩,
    fun v hv => by
      have hvt := hvlt v hv
      have h1 : mem' (dgExtToIntBase gPtr vCap + v) = mem (dgExtToIntBase gPtr vCap + v) :=
        hagree _ (by dsimp [dgExtToIntBase, dynGraphSize]; omega)
      have hst := hvlt _ (hext v hv).1
      rw [h1, hagree _ (by dsimp [dgIntToExtBase, dynGraphSize]; omega)]
      exact hext v hv,
    fun s hs => by
      have hst := hvlt s hs
      have h1 : mem' (dgIntToExtBase gPtr vCap + s) = mem (dgIntToExtBase gPtr vCap + s) :=
        hagree _ (by dsimp [dgIntToExtBase, dynGraphSize]; omega)
      have hvt := hvlt _ (hint s hs).1
      rw [h1, hagree _ (by dsimp [dgExtToIntBase, dynGraphSize]; omega)]
      exact hint s hs,
    fun e he => by rw [hagree _ (by dsimp [dgEPresBase, dynGraphSize]; omega)]; exact hep e he,
    ⟨eL, heL_len, heL_nd, heL_mem,
      fun i hi => by
        rw [hagree _ (by
          dsimp [dgEListBase, dynGraphSize]
          have : G.m ≤ eCap := by simpa [MGraph.m] using Finset.card_le_card (fun e he => Finset.mem_range.mpr (helt e he))
          omega)]
        exact heL_LA i hi,
      fun i hi => by
        rw [hagree _ (by dsimp [dgEPosBase, dynGraphSize]; have := helt _ ((heL_mem _).mp (List.getElem_mem hi)); omega)]
        exact heL_pos i hi⟩,
    fun e he => by
      have he_lt := helt e he
      have htV := hvlt _ (hG e he).1
      have hhV := hvlt _ (hG e he).2
      rw [hagree (dgETailSlotBase gPtr vCap eCap + e) (by dsimp [dgETailSlotBase, dynGraphSize]; omega),
        hagree (dgEHeadSlotBase gPtr vCap eCap + e) (by dsimp [dgEHeadSlotBase, dynGraphSize]; omega),
        hagree (dgExtToIntBase gPtr vCap + G.tail e) (by dsimp [dgExtToIntBase, dynGraphSize]; omega),
        hagree (dgExtToIntBase gPtr vCap + G.head e) (by dsimp [dgExtToIntBase, dynGraphSize]; omega)]
      exact heEnds e he,
    ⟨incL, hdll'⟩⟩, hdll'⟩

end

end MinCostFlow.LSF.Program
